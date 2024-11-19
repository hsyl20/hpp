{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE CPP #-}
import Control.Monad.Trans.Except
import Data.ByteString.Char8 (ByteString)
import Data.Maybe (fromMaybe)
import Hpp
import qualified Hpp.Config as C
import qualified Hpp.Types as T

#if __GLASGOW_HASKELL__ <= 802
import Data.Monoid ((<>))
#endif

import System.Exit

sourceIfdef :: [ByteString]
sourceIfdef = [ "#ifdef FOO"
              , "x = 42"
              , "#else"
              , "x = 99"
              , "#endif" ]

sourceArith1 :: ByteString -> [ByteString]
sourceArith1 s = [ "#define x 3"
                 , "#if 5 + x > " <> s
                 , "yay"
                 , "#else"
                 , "boo"
                 , "#endif" ]

hppHelper :: HppState -> [ByteString] -> [ByteString] -> IO Bool
hppHelper st src expected =
  case runExcept (expand st (preprocess src)) of
    Left e -> putStrLn ("Error running hpp: " ++ show e) >> return False
    Right (res, _) -> if hppOutput res == expected
                      then return True
                      else do putStr ("Expected "++show expected++", got")
                              print (hppOutput res)
                              return False

hppHelper' :: HppState -> [ByteString] -> [ByteString] -> IO Bool
hppHelper' = hppHelper . T.over T.config (T.setL C.inhibitLinemarkersL True)

testElse :: IO Bool
testElse = hppHelper' emptyHppState sourceIfdef ["x = 99\n","\n"]

testIf :: IO Bool
testIf = hppHelper' (fromMaybe (error "Preprocessor definition did not parse")
                      (addDefinition "FOO" "1" emptyHppState))
                    sourceIfdef
                    ["x = 42\n","\n"]

testArith1 :: IO Bool
testArith1 = (&&) <$> hppHelper' emptyHppState (sourceArith1 "7") ["yay\n","\n"]
                  <*> hppHelper' emptyHppState (sourceArith1 "8") ["boo\n","\n"]

sourceCommentsAndSplice :: [ByteString]
sourceCommentsAndSplice =
  [ "#ifdef FOO"
  , "Some /* neat */ text"
  , "#else"
  , "I am /* an else branch"
  , "whose importance must not"
  , "be */ underestimated "
  , "#endif"
  , "Do you\\"
  , "understand?"]

-- | A configuration to not splice lines, leave C-style comments,
-- ignore trigraphs, but emit line markers.
hppConfig :: HppState -> HppState
hppConfig st = T.over T.config opts $ st
  where opts = T.setL C.spliceLongLinesL False
             . T.setL C.eraseCCommentsL False
             . T.setL C.replaceTrigraphsL False
             . T.setL C.inhibitLinemarkersL False

remove_comments :: HppState -> HppState
remove_comments = T.over T.config (T.setL C.eraseCCommentsL True)

testCommentsAndSplice1 :: IO Bool
testCommentsAndSplice1 =
  hppHelper (hppConfig
              (fromMaybe (error "Preprocessor definition did not parse")
               (addDefinition "FOO" "1" emptyHppState)))
            sourceCommentsAndSplice
            [ "Some /* neat */ text\n"
            , "#line 8\n"
            , "Do you\\\n"
            , "understand?\n" ]

testCommentsAndSplice2 :: IO Bool
testCommentsAndSplice2 =
  hppHelper (hppConfig emptyHppState)
            sourceCommentsAndSplice
            [ "#line 4\n"
            , "I am /* an else branch\n"
            , "whose importance must not\n"
            , "be */ underestimated \n"
            , "Do you\\\n"
            , "understand?\n" ]

testMacroNoArgs :: IO Bool
testMacroNoArgs =
  hppHelper (hppConfig emptyHppState)
            [ "#define FOO() foo"
            , "bar"
            , "FOO()"
            , "baz"
            ]
            [ "bar\n"
            , "foo\n"
            , "baz\n"
            ]

testMacroInComments :: IO Bool
testMacroInComments = do
  hppHelper (remove_comments $ hppConfig emptyHppState)
            [ "#define FOO(a) a+a"
            , "// Blah FOO() blah"
            , "/* Blah FOO() blah */"
            ]
            [ "\n"
            , "\n"
            ]

testCommentInBlock :: IO Bool
testCommentInBlock = do
  hppHelper (remove_comments $ hppConfig emptyHppState)
            [ "foo"
            , "/* blah"
            , "   https://foo.bar */"
            , "bar"
            ]
            [ "foo\n"
            , "bar\n"
            ]

testLitBeforeCommentBlock :: IO Bool
testLitBeforeCommentBlock = do
  hppHelper (remove_comments $ hppConfig emptyHppState)
            [ "foo"
            , "\"something\"/* blah"
            , "   */"
            , "bar"
            ]
            [ "foo\n"
            , "\"something\"\n"
            , "bar\n"
            ]

testQuoteInCommentBlock :: IO Bool
testQuoteInCommentBlock = do
  hppHelper (remove_comments $ hppConfig emptyHppState)
            [ "foo"
            , "/* blah"
            , "  \" */"
            , "bar"
            ]
            [ "foo\n"
            , "bar\n"
            ]

main :: IO ()
main = do results <- sequenceA [ testElse, testIf, testArith1
                               , testCommentsAndSplice1
                               , testCommentsAndSplice2
                               , testMacroNoArgs
                               , testMacroInComments
                               , testCommentInBlock
                               , testLitBeforeCommentBlock
                               , testQuoteInCommentBlock
                               ]
          if and results
            then do putStrLn (show (length results) ++ " tests passed")
                    exitWith ExitSuccess
            else do putStrLn (show (length (filter id results)) ++
                              " of " ++ show (length results) ++
                              " tests passed")
                    exitWith (ExitFailure 1)
