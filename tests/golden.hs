module Main where

import Test.Tasty
import Test.Tasty.Program (testProgram, CatchStderr(..))
import Test.Tasty.Golden (goldenVsFile)
import Test.Tasty.ExpectedFailure (expectFail)
import Test.Tasty.Runners.Html
import System.Environment (getArgs, withArgs)

main :: IO ()
main = do
    args <- getArgs -- append to stdin args
    withArgs ("-j1":args) $ -- don't run tests in parallel because it messes output
       defaultMainWithIngredients (htmlRunner:defaultIngredients)(
         testGroup "coop-scheduling" 
                       [ 
                        -- run habs and then testProgram runghc
                        testProgram "case_f" "echo" ["mplo"] Nothing
                        -- expectFail $ testProgram "case_f" "exe-name" [exe-args] mpwd
                       ])

case_todo :: IO ()
case_todo = return ()
