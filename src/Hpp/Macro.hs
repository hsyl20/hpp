{-# LANGUAGE CPP, OverloadedStrings, ViewPatterns #-}
module Hpp.Macro (parseDefinition, MacroStyle(..)) where
import Data.Char (isSpace)
#if __GLASGOW_HASKELL__ < 804
import Data.Semigroup ((<>))
#endif
import Hpp.StringSig
import Hpp.Tokens (trimUnimportant, importants, Token(..), isImportant)
import Hpp.Types (Macro(..), String, TOKEN, Scan(..), Variadic(..))
import Prelude hiding (String)
import qualified Data.List as List

-- * TOKEN Splices

-- | Deal with the two-character '##' token pasting/splicing
-- operator. We do so eliminating spaces around the @##@
-- operator.
prepTOKENSplices :: [TOKEN] -> [TOKEN]
prepTOKENSplices = map (fmap copy) . dropSpaces [] . mergeTOKENs []
  where -- Merges ## tokens, and reverses the input list
        mergeTOKENs acc [] = acc
        mergeTOKENs acc (Important "#" : Important "#" : ts) =
          mergeTOKENs (Important "##" : acc) (dropWhile (not . isImportant) ts)
        mergeTOKENs acc (t:ts) = mergeTOKENs (t : acc) ts
        -- Drop trailing spaces and re-reverse the list
        dropSpaces acc [] = acc
        dropSpaces acc (t@(Important "##") : ts) =
          dropSpaces (t : acc) (dropWhile (not . isImportant) ts)
        dropSpaces acc (t:ts) = dropSpaces (t : acc) ts

-- | Whether @#@ and @##@ are operators in the body of a function-like macro.
--
-- See Note [# is a letter in Haskell] in "Hpp.Config".
data MacroStyle
  = StandardMacros
    -- ^ @#x@ stringifies, @a ## b@ pastes. What C says.
  | TraditionalMacros
    -- ^ Neither: a @#@ is an ordinary character. What @-traditional-cpp@ does,
    -- and what a Haskell source needs.
  deriving (Eq, Show)

-- | Parse the definition of an object-like or function macro.
parseDefinition :: MacroStyle -> [TOKEN] -> Maybe (String, Macro)
parseDefinition style toks =
  case dropWhile (not . isImportant) toks of
    (Important name:Important "(":rst) ->
      let params0 = takeWhile (/= ")") $ filter (/= ",") (importants rst)
          arity0  = length params0
          (params, arity, variadic) = case splitAt (arity0 - 3) params0 of
            (as, [".",".","."]) -> (as, arity0 - 3, Variadic)
            _                   -> (params0, arity0, NotVariadic)
          body = trimUnimportant . drop 1 $ dropWhile (/= Important ")") toks
          macro = Function variadic arity
                    (functionMacro style variadic arity params body)
      in Just (name, macro)
    (Important name:_) ->
      let rhs = case dropWhile (/= Important name) toks of
                  [] -> [Important ""]
                  str@(_:t)
                    | all (not . isImportant) str -> [Important ""]
                    | otherwise -> trimUnimportant t
      in Just (copy name, Object (map (fmap copy) rhs))
    _ -> Nothing

-- * Function-like macros as Haskell functions

-- | Drop spaces following @'#'@ characters.
prepStringify :: [TOKEN] -> [TOKEN]
prepStringify [] = []
prepStringify (Important "#" : ts) =
  case dropWhile (not . isImportant) ts of
    (Important t : ts') -> Important (cons '#' t) : prepStringify ts'
    _ -> Important "#" : ts
prepStringify (t:ts) = t : prepStringify ts

-- | Concatenate tokens separated by @'##'@.
--
-- Under 'TraditionalMacros' there is no @##@ token to find: 'prepTOKENSplices'
-- never merged the two @#@s, so this walks the list unchanged.
paste :: [Scan] -> [Scan]
paste [] = []
paste (Rescan (Important s) : Rescan (Important "##") : Rescan (Important t) : ts) =
  paste (Rescan (Important (trimSpaces s <> sdropWhile isSpace t)) : ts)
paste (t:ts) = t : paste ts

-- | @functionMacro parameters body arguments@ substitutes @arguments@
-- for @parameters@ in @body@ and performs stringification for uses of
-- the @#@ operator and token concatenation for the @##@ operator.
--
-- Under 'TraditionalMacros' it does neither, and a @#@ in the body is
-- substituted through like any other character. See Note [# is a letter in
-- Haskell] in "Hpp.Config".
functionMacro :: MacroStyle -> Variadic -> Int -> [String] -> [TOKEN]
              -> [([Scan],String)] -> [Scan]
functionMacro style variadic arity params body args
  = paste . subst body' {- . M.fromList -} . zip params' $ args'
  where (args',var_args) = case variadic of
          NotVariadic -> (args,[])
          Variadic    -> List.splitAt arity args
        params' = map copy params
        subst toks gamma = go toks
          where go [] = []
                -- handle __VA_ARGS__ first
                go ((Important ","):(Important "##"):(Important "__VA_ARGS__"):ts)
                  | Variadic <- variadic
                  , [] <- var_args
                  = go ts -- GCC extension: we drop the leading comma if __VA_ARGS__ is empty
                go ((Important "__VA_ARGS__"):ts)
                  | Variadic <- variadic
                  = let vas = map (Rescan . Important . snd) var_args
                    in List.intersperse (Rescan (Important ",")) vas ++ go ts

                -- TODO: handle __VA_OPT__ here

                go (p@(Important "##"):t@(Important s):ts) =
                  case lookup s gamma of
                    Nothing -> Rescan p : Rescan t : go ts
                    Just (_,arg) ->
                      Rescan p : Rescan (Important arg) : go ts
                go (t@(Important s):p@(Important "##"):ts) =
                  case lookup s gamma of
                    Nothing -> Rescan t : go (p:ts)
                    Just (_,arg) -> Rescan (Important arg) : go (p:ts)
                go (t@(Important "##"):ts) = Rescan t : go ts
                go (t@(Important (uncons -> Just ('#',s))) : ts) =
                  case lookup s gamma of
                    Nothing -> Rescan t : go ts
                    Just (_,arg) ->
                      Rescan (Important (stringify arg)) : go ts
                go (t@(Important s) : ts) =
                  case lookup s gamma of
                    Nothing -> Rescan t : go ts
                    Just (arg,_) -> arg ++ go ts
                go (t:ts) = Rescan t : go ts
        -- The '##'-merging half of 'prepTOKENSplices' is what makes an
        -- @Important "##"@ exist at all, and 'prepStringify' is what makes a
        -- token start with a '#'. Skipping both leaves every branch of 'go'
        -- that looks for one unreachable, and a '#' reaches the output as
        -- itself.
        body' = case style of
          StandardMacros    -> prepStringify (prepTOKENSplices body0)
          TraditionalMacros -> map (fmap copy) body0
        body0 = dropWhile (not . isImportant) body
