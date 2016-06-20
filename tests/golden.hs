{-# LANGUAGE ScopedTypeVariables, ImplicitParams #-}
module Main where

import Test.Tasty
import Test.Tasty.Program (testProgram)
import Test.Tasty.Golden (goldenVsFile)
import Test.Tasty.HUnit
import Test.Tasty.ExpectedFailure (expectFail)
import Test.Tasty.Runners.Html

import qualified ABS.AST as ABS
import qualified ABS.Parser as ABS
import ABS.Compiler.Codegen.Mod (tModul)
import ABS.Compiler.Utils (showQU)
import ABS.Compiler.Firstpass.SymbolTable (globalSTs)
import qualified Language.Haskell.Exts.Pretty as HS (prettyPrintWithMode, defaultMode, linePragmas)

import System.Environment (getArgs, withArgs)
import System.Directory (getDirectoryContents, doesDirectoryExist, createDirectoryIfMissing)
import System.FilePath ((</>), (<.>), dropExtension)
import Data.List (isSuffixOf)

import Control.Exception (catch, SomeException)  --  hack for not_compile tests

hsOutputDir = "dist"</>"test"</>"gen"</>"haskell"

main :: IO ()
main = do
    args <- getArgs -- append to stdin args


    createDirectoryIfMissing True hsOutputDir

    must <- map dropExtension . filter (".abs" `isSuffixOf`) <$> getDirectoryContents ("habs-samples"</>"must_pass")
    not_compile <- map dropExtension . filter (".abs" `isSuffixOf`) <$> getDirectoryContents ("habs-samples"</>"not_compile")
    deadlocked <- map dropExtension . filter (".abs" `isSuffixOf`) <$> getDirectoryContents ("habs-samples"</>"deadlocked")

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
           testGroup "must_pass" [ testGroup "transpile" $ map (\ sample -> testCase sample $ transpile ("habs-samples"</>"must_pass") sample) must
                                 , testGroup "compile" $ map (\ sample -> testProgram sample ghc (ghcArgs sample) Nothing) must]
         , testGroup "not_compile" $ map (\ sample -> expectFail $ 
                                     withResource (transpile ("habs-samples"</>"not_compile") sample `catch` (\ (_ :: SomeException) -> return ())) 
                                                      (const $ return ())
                                                      (const $ testProgram sample ghc (ghcArgs sample) Nothing)
                                 ) not_compile
         , testGroup "deadlocked" [ testGroup "transpile" $ map (\ sample -> testCase sample $ transpile ("habs-samples"</>"deadlocked") sample) deadlocked
                                     , testGroup "compile" $ map (\ sample -> testProgram sample ghc (ghcArgs sample) Nothing) deadlocked
                                     , testGroup "execute" $ map (\ sample -> expectFail $ testProgram sample "env" [hsOutputDir </> sample] Nothing) deadlocked
                                     ]
                       ]


transpile parentDir sample = do
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
    -- (_, ABS.Ok _) -> fail "no multiple modules supported in the test"
    _ -> fail "ABS parse error"
