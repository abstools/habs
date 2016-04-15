{-# LANGUAGE CPP #-}
module Main where

import Test.Tasty
import Test.Tasty.Program (testProgram, CatchStderr(..))
import Test.Tasty.Golden (goldenVsFile)
import Test.Tasty.HUnit
import Test.Tasty.ExpectedFailure (expectFail)
import Test.Tasty.Runners.Html

import qualified ABS.AST as ABS
import qualified ABS.Parser as ABS
import ABS.Compiler.Codegen.Mod (tModul)
import ABS.Compiler.Utils (showQType)
import ABS.Compiler.Firstpass.SymbolTable (globalSTs)
import qualified Language.Haskell.Exts.Pretty as HS (prettyPrint)

import System.Environment (getArgs, withArgs)
import System.Directory (getDirectoryContents, doesDirectoryExist, createDirectoryIfMissing)
import System.FilePath ((</>), (<.>), dropExtension)
import Data.List (isSuffixOf)

#if __GLASGOW_HASKELL__ < 710
import Control.Applicative
#endif

hsOutputDir = "./dist/test/gen/haskell"

main :: IO ()
main = do
    args <- getArgs -- append to stdin args
    must <- map dropExtension . filter (".abs" `isSuffixOf`) <$> getDirectoryContents "./habs-samples/must"
    createDirectoryIfMissing True hsOutputDir
    isSandboxed <- doesDirectoryExist "./.cabal-sandbox/"
    let (ghc,ghcExtraArgs) = if isSandboxed then ("cabal",["exec","ghc","--"]) else ("ghc",[])
    let ghcArgs sample = ghcExtraArgs ++ [ "--make"
                                         , "-O0"
                                         , "-fforce-recomp"
                                         , "-main-is", sample
                                         , hsOutputDir </> sample <.> "hs"]
    withArgs ("-j1":args) $ -- don't run tests in parallel because it messes output
       defaultMainWithIngredients (htmlRunner:defaultIngredients)(
         testGroup "habs" [
           testGroup "must" [ testGroup "transpile" $ map (\ sample -> testCase sample $ transpile "./habs-samples/must" sample) must
                            , testGroup "compile" $ map (\ sample -> testProgram sample ghc (ghcArgs sample) Nothing) must]
         , testGroup "could" []
         , testGroup "neg" []
         ]
                                                                 )


transpile parentDir sample = do
  res <- ABS.parseFile (parentDir </> sample <.> "abs")
  case res of
    (_, ABS.Ok (ABS.Prog ms)) -> let symbolTables = globalSTs ms
                                in mapM_ (\ m@(ABS.Modul mname _ _ _ _) ->
                                             writeFile (hsOutputDir </> showQType mname <.> "hs") $ 
                                             HS.prettyPrint $ tModul m symbolTables) ms
    -- (_, ABS.Ok _) -> fail "no multiple modules supported in the test"
    _ -> fail "ABS parse error"
