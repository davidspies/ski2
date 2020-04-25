module Main where

import           Control.Concurrent
import           Control.Monad
import           Data.Void
import           Lib
import           System.Environment

main :: IO ()
main = do
    args <- getArgs
    let delay :: Int
        delay = case args of
            []        -> 500000
            [     t ] -> read t
            _ : _ : _ -> error "Too many args"
    t <- readLn :: IO (Term Void)
    forM_ (steps t) $ \t' -> do
        print t'
        threadDelay delay
