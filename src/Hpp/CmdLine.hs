{-# LANGUAGE OverloadedStrings, RankNTypes, TupleSections #-}
-- | A front-end to run Hpp with textual arguments as from a command
-- line invocation.
module Hpp.CmdLine (runWithArgs) where
import Control.Monad (unless)
import Control.Monad.Trans.Except (runExceptT)
import Data.ByteString.Char8 (ByteString)
import Data.String (fromString)
import Hpp
import Hpp.Config
import Hpp.Env (deleteKey, emptyEnv, insertPair)
import Hpp.StringSig (readLines, putStringy)
import Hpp.Types (Env, Error(..), setL, lineNum)
import System.Directory (doesFileExist, makeAbsolute)
import System.IO (openFile, IOMode(..), hClose, stdout)

-- | Break a string on an equals sign. For example, the string @x=y@
-- is broken into @[x,"=",y]@.
breakEqs :: String -> [String]
breakEqs = aux . break (== '=')
  where aux (h,[]) = [h]
        aux (h,'=':t) = [h,"=",t]
        aux _ = error "breakEqs broke"

-- | If no space is included between a switch and its argument, break
-- it into two tokens to simplify parsing.
splitSwitches :: String -> [String]
splitSwitches ('-':'I':t@(_:_)) = ["-I",t]
splitSwitches ('-':'D':t@(_:_)) = ["-D",t]
splitSwitches ('-':'U':t@(_:_)) = ["-U",t]
splitSwitches ('-':'o':t@(_:_)) = ["-o",t]
splitSwitches ('-':'i':'n':'c':'l':'u':'d':'e':t@(_:_)) = ["-include",t]
splitSwitches x = [x]

-- | A @-D@ or @-U@ from the command line, kept until the configuration is
-- known. See Note [Definitions wait for the configuration].
data EnvOp = Define ByteString ByteString | Undef ByteString

-- Note [Definitions wait for the configuration]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- Reading a @-D@ into a macro is not independent of the configuration:
-- @--ftraditional-macros@ decides whether a @#@ in the body is an operator.
-- Applying each @-D@ where it is parsed would make the result depend on where
-- the switch sits on the command line, so the ops are collected in order and
-- replayed once 'realizeConfig' has produced the configuration they are read
-- under.

-- FIXME: Defining function macros probably doesn't work here.
parseArgs :: ConfigF Maybe -> [String]
          -> IO (Either Error (Env, [String], Config, Maybe FilePath))
parseArgs cfg0 = go id id cfg0 Nothing . concatMap breakEqs
  where go ops acc cfg out [] =
          case realizeConfig cfg of
            Just cfg' -> return ((, acc [], cfg', out) <$> replay cfg' (ops []))
            Nothing -> return (Left NoInputFile)
        go ops acc cfg out ("-D":name:"=":body:rst) =
          go (ops . (Define (fromString name) (fromString body):)) acc cfg out rst
        go ops acc cfg out ("-D":name:rst) =
          go (ops . (Define (fromString name) "1":)) acc cfg out rst
        go ops acc cfg out ("-U":name:rst) =
          go (ops . (Undef (fromString name):)) acc cfg out rst
        go ops acc cfg out ("-I":dir:rst) =
          let cfg' = cfg { includePathsF = fmap (++[dir]) (includePathsF cfg) }
          in go ops acc cfg' out rst
        go ops acc cfg out ("-include":file:rst) =
          let ln = "#include \"" ++ file ++ "\""
          in go ops (acc . (ln:)) cfg out rst
        go ops acc cfg out ("-P":rst) =
          let cfg' = cfg { inhibitLinemarkersF = Just True }
          in go ops acc cfg' out rst
        go ops acc cfg out ("--cpp":rst) =
          let cfg' = cfg { spliceLongLinesF = Just True
                         , eraseCCommentsF = Just True
                         , inhibitLinemarkersF = Just False
                         , replaceTrigraphsF = Just True }
              defs = concatMap ("-D":)
                       [ ["__STDC__"]
                         -- __STDC_VERSION__ is only defined in C94 and later
                       , ["__STDC_VERSION__","=","199409L"] ]
                       -- , ["_POSIX_C_SOURCE","=","200112L"] ]
          in go ops acc cfg' out (defs ++ rst)
        -- See Note [GHC syntax for line markers] in "Hpp.Config".
        go ops acc cfg out ("--fhaskell-line-markers":rst) =
          go ops acc (cfg { lineMarkerStyleF = Just HaskellLineMarkers
                          , inhibitLinemarkersF = Just False }) out rst
        go ops acc cfg out ("--fline-splice":rst) =
          go ops acc (cfg { spliceLongLinesF = Just True }) out rst
        go ops acc cfg out ("--ferase-comments":rst) =
          go ops acc (cfg { eraseCCommentsF = Just True }) out rst
        -- '//' is an operator in some languages -- Haskell has one -- so
        -- erasing to the end of the line there destroys code. Block comments
        -- are erased either way. See 'eraseCLineCommentsF'.
        go ops acc cfg out ("--fno-line-comments":rst) =
          go ops acc (cfg { eraseCLineCommentsF = Just False }) out rst
        -- See 'ignoreHaskellCommentsF'.
        go ops acc cfg out ("--fhaskell-comments":rst) =
          go ops acc (cfg { ignoreHaskellCommentsF = Just True }) out rst
        -- See Note [# is a letter in Haskell] in "Hpp.Config".
        go ops acc cfg out ("--ftraditional-macros":rst) =
          go ops acc (cfg { traditionalMacrosF = Just True }) out rst
        go ops acc cfg out ("--freplace-trigraphs":rst) =
          go ops acc (cfg { replaceTrigraphsF = Just True }) out rst
        go ops acc cfg out ("--only-macros":rst) =
          go ops acc (cfg { replaceTrigraphsF = Just False
                          , spliceLongLinesF = Just False
                          , eraseCCommentsF = Just False }) out rst
        go ops acc cfg _ ("-o":file:rst) =
          go ops acc cfg (Just file) rst
        go ops acc cfg out ("-x":_lang:rst) =
          go ops acc cfg out rst -- We ignore source language specification
        go ops acc cfg out ("-traditional":rst) =
          go ops acc cfg out rst -- Ignore the "-traditional" flag
        go ops acc cfg out ("-Werror":rst) =
          go ops acc cfg out rst -- Ignore the "-Werror" flag
        go ops acc cfg Nothing (file:rst) =
          case curFileNameF cfg of
            Nothing -> go ops acc (cfg { curFileNameF = Just file }) Nothing rst
            Just _ -> go ops acc cfg (Just file) rst
        go _ _ _ (Just _) _ =
          return . Left $ BadCommandLine "Multiple output files given"

        -- Apply the collected -D and -U in the order they were given, now that
        -- the configuration they are read under is known.
        replay cfg = foldl step (Right emptyEnv)
          where style = macroStyle cfg
                step (Left e) _ = Left e
                step (Right env) (Undef name) = Right (deleteKey name env)
                step (Right env) (Define name body) =
                  case parseDefinition style name body of
                    Nothing  -> Left (BadMacroDefinition 0)
                    Just def -> Right (insertPair def env)

-- | Run Hpp with the given commandline arguments.
runWithArgs :: [String] -> IO (Maybe Error)
runWithArgs args =
  do cfgNow <- defaultConfigFNow
     let args' = concatMap splitSwitches args
     (env,lns,cfg,outPath) <- fmap (either (error . show) id)
                                   (parseArgs cfgNow args')
     exists <- doesFileExist (curFileName cfg)
     unless exists . error $
       "Couldn't open input file: "++curFileName cfg
     let fileName = curFileName cfg
         cfg' = cfg { curFileNameF = pure fileName }
     (snk, closeSnk) <- case outPath of
                          Nothing -> return ( mapM_ (putStringy stdout)
                                            , return () )
                          Just f ->
                            do h <- makeAbsolute f >>=
                                    flip openFile WriteMode
                               return ( \os -> mapM_ (putStringy h) os
                                      , hClose h )
     -- See Note [Resetting __LINE__ after the CLI prelude]
     srcLines <- readLines fileName
     result <- runExceptT $ do
                 let st0 = initHppState cfg' env
                 (_, st1) <- streamHpp st0 snk
                                 (preprocess (map fromString lns))
                 let st2 = setL lineNum 1 st1
                 streamHpp st2 snk (preprocess srcLines)
     closeSnk
     case result of
       Left err -> return $ Just err
       _ -> return Nothing

-- Note [Resetting __LINE__ after the CLI prelude]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- The command-line driver builds up a small prelude from -D, -U and
-- -include options and would otherwise prepend it verbatim to the
-- user's source. For example,
--
--     hpp -D FOO=1 -include foo.h main.c
--
-- yields a synthetic prelude:
--
--     #define FOO 1
--     #include "foo.h"
--
-- Naïvely concatenating the prelude with main.c and feeding the lot
-- through 'preprocess' breaks line counting in two reinforcing ways:
--
--   1. The preprocessor's lineNum advances one per source line as it
--      is consumed, including the prelude. The user's first line ends
--      up at lineNum N+1 for an N-line prelude.
--
--   2. The C-comment-removal pass ('cCommentRemoval') sits in front of
--      directive dispatch and emits @#line K@ markers based on the
--      position of multi-line @/\*…\*\/@ blocks in the /combined/ input
--      stream. Those markers are off by N from the user's source line
--      numbers — and the offset is then baked into every subsequent
--      __LINE__ expansion.
--
-- The user-visible symptom is __LINE__ off by some N >= 1 for any
-- file that uses -include, with the off-by growing if a leading
-- block comment shifts cCommentRemoval's idea of "where the user's
-- code starts". MCPP test n_28.c fires assert(__LINE__ == 19) on its
-- own line 19 and trips the moment -include is added.
--
-- The fix is to drive the prelude and the user's source through two
-- separate streamHpp invocations. The prelude pass establishes the
-- macro environment and any included files; we then reset
-- @lineNum@ to 1 in the captured state and run the user's source on
-- its own. cCommentRemoval restarts at curLine=1 for the source pass
-- (see 'preprocess' in pkg:Hpp.RunHpp), and __LINE__ matches the
-- physical source line the user can see in their editor.
