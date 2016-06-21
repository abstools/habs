{-# LANGUAGE ScopedTypeVariables, ImplicitParams #-}
module Main where

import Test.Tasty
import Test.Tasty.Program (testProgram)
import Test.Tasty.Golden (goldenVsFile, writeBinaryFile)
import Test.Tasty.HUnit
import Test.Tasty.ExpectedFailure (expectFail)
import Test.Tasty.Runners.Html
import System.Process -- for running ABS programs and capturing stdout
import System.Exit (ExitCode (..))

import qualified ABS.AST as ABS
import qualified ABS.Parser as ABS
import ABS.Compiler.Codegen.Mod (tModul)
import ABS.Compiler.Utils (showQU)
import ABS.Compiler.Firstpass.SymbolTable (globalSTs)
import qualified Language.Haskell.Exts.Pretty as HS (prettyPrintWithMode, defaultMode, linePragmas)

import System.Environment (getArgs, withArgs)
import System.Directory (getDirectoryContents, doesDirectoryExist, createDirectoryIfMissing)
import System.FilePath ((</>), (<.>), dropExtension)
import Data.List (isSuffixOf,isInfixOf)

import Control.Exception (catch, SomeException)  --  hack for not_compile tests

hsOutputDir = "dist"</>"test"</>"gen"</>"haskell"

main :: IO ()
main = do
    args <- getArgs -- append to stdin args


    createDirectoryIfMissing True hsOutputDir

    to_pass <- map dropExtension . filter (".abs" `isSuffixOf`) <$> getDirectoryContents ("habs-samples"</>"to_pass")
    to_fail <- map dropExtension . filter (".abs" `isSuffixOf`) <$> getDirectoryContents ("habs-samples"</>"to_fail")
    to_timeout <- map dropExtension . filter (".abs" `isSuffixOf`) <$> getDirectoryContents ("habs-samples"</>"to_timeout")
    not_compile <- map dropExtension . filter (".abs" `isSuffixOf`) <$> getDirectoryContents ("habs-samples"</>"not_compile")

    isSandboxed <- doesDirectoryExist ".cabal-sandbox"
    let (ghc,ghcExtraArgs) = if isSandboxed then ("cabal",["exec","ghc","--"]) else ("ghc",[])
    let ghcArgs sample = ghcExtraArgs ++ [ "--make"
                                         , "-O0"
                                         , "-fforce-recomp"
                                         , "-main-is", sample
                                         , hsOutputDir </> sample <.> "hs"]

    withArgs ("-j1":"--catch-stderr":args) $ -- don't run tests in parallel because it messes output
       defaultMainWithIngredients (htmlRunner:defaultIngredients) $
        localOption (mkTimeout 10000000) $ -- timeouts any individual test **case** at 10s
         testGroup "habs" [
           testGroup "to_pass" [ testGroup "transpile" $ map (\ sample -> testCase sample $ transpile ("habs-samples"</>"to_pass") sample) to_pass
                               , testGroup "compile" $ map (\ sample -> testProgram sample ghc (ghcArgs sample) Nothing) to_pass
                               , testGroup "execute" $ map (\ sample -> goldenVsFile sample
                                                                            ("habs-samples"</>"to_pass"</>sample<.>"out")
                                                                            (hsOutputDir</>sample<.>"out")
                                                                            (exec_stdout sample)
                                                             ) to_pass]
         , testGroup "to_fail" [ testGroup "transpile" $ map (\ sample -> testCase sample $ transpile ("habs-samples"</>"to_fail") sample) to_fail
                               , testGroup "compile" $ map (\ sample -> testProgram sample ghc (ghcArgs sample) Nothing) to_fail
                               , testGroup "execute" $ map (\ sample -> testCase sample $ exec_stderr sample
                                                             ) to_fail]
  
         , testGroup "to_timeout" [ testGroup "transpile" $ map (\ sample -> testCase sample $ transpile ("habs-samples"</>"to_timeout") sample) to_timeout
                                  , testGroup "compile" $ map (\ sample -> testProgram sample ghc (ghcArgs sample) Nothing) to_timeout
                                  , testGroup "execute" $ map (\ sample -> expectFail $ testCase sample $ exec_stdout sample) to_timeout
                                  ]
         , testGroup "not_compile" $ map (\ sample -> expectFail $ 
                                     withResource (transpile ("habs-samples"</>"not_compile") sample `catch` (\ (_ :: SomeException) -> return ())) 
                                                      (const $ print sample)
                                                      (const $ testProgram sample ghc (ghcArgs sample) Nothing)
                                         ) not_compile                         
                          ]


transpile parentDir sample = do
  print sample
  res <- ABS.parseFile (parentDir </> sample <.> "abs")
  case res of
    (fp, ABS.Ok (ABS.Program ms)) -> let symbolTables = globalSTs ms
                                      in mapM_ (\ m@(ABS.Module mname _ _ _ _) -> do
                                        let hsContents = HS.prettyPrintWithMode (HS.defaultMode {HS.linePragmas = True}) $ 
                                                            let ?absFileName = fp in tModul m symbolTables
                                            -- clean-up empty LINE pragmas
                                            hsContentsClean = unlines . filter (not . isSuffixOf "{-# LINE 1 \"<unknown>.hs\" #-}") $ 
                                                                  lines hsContents    
      
                                        writeFile (hsOutputDir </> showQU mname <.> "hs") $ hsContentsClean 
                                               ) ms
    _ -> assertFailure "ABS parse error"


exec_stdout sample = do
  print sample
  (exitCode, outStr, _errStr) <- readCreateProcessWithExitCode ((proc (hsOutputDir</>sample) []) { cwd = Just hsOutputDir }) "" -- empty stdin
  case exitCode of
    ExitSuccess -> writeBinaryFile (hsOutputDir</>sample<.>"out") outStr
    _ -> fail "Failed to execute ABS program"

exec_stderr sample = do
  print sample
  (_exitCode, _outStr, errStr) <- readCreateProcessWithExitCode ((proc (hsOutputDir</>sample) ["-t"]) { cwd = Just hsOutputDir }) "" -- empty stdin
  writeBinaryFile (hsOutputDir</>sample<.>"err") errStr
  assertBool "Unexpected pass" ("Uncaught-Exception" `isInfixOf` errStr || "Assertion failed" `isInfixOf` errStr)