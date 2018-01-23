{-# OPTIONS_GHC -Wall -fno-warn-unused-imports -fno-warn-name-shadowing -fno-warn-type-defaults #-}
{-# LANGUAGE TemplateHaskell,FlexibleContexts, FlexibleInstances #-}

module Runner  where

import Data.List (foldl',intercalate)
import Data.List.Split (endBy)
import Data.Maybe (mapMaybe,fromMaybe)
import Data.Char (isSpace)

import System.Environment (getArgs) 
import System.FilePath (takeFileName)
import System.Console.ArgParser
import System.Timeout
import System.TimeIt           -- for benchmarking

import Control.DeepSeq

import Syntax
import Tableau
import Pretty

import qualified MinimalSyntax 
import qualified MinimalTableau
import qualified MinimalPretty


-- TODO: create an LTL-LIKE type-class and a Prop-like typeclass
--       This should get rid of the dual Syntax/MinimalSyntax nonsense.


------------------------------------------------------------------------
-- Runner
------------------------------------------------------------------------


data Options = Options {
  out :: FilePath,
  inp :: FilePath,
  expression :: FilePath,
  timing :: String,
  slow :: Bool,
  pdf :: Bool,
  tabl :: Bool,
  graph :: Bool
  } deriving (Show, Read)
               


andAll :: [Bool] -> Bool
andAll = foldr (\b bs -> b && bs) True

mapString :: (String -> a) -> String -> String -> [a]
mapString f sep str = foldl' (\acc x -> acc ++ [f x] ) [] (endBy sep str)


parser :: ParserSpec Options
parser = Options
         `parsedBy` optFlag "" "outfile" `Descr` "The output file pattern for .sat (judgement) .pdf (graph) and .tex (labels) -- if none is given, no graph or tableau is calculated. Prints judgement to std out."
         `andBy` optFlag "" "infile" `Descr` "The input file for LTLf formulae, if empty read from stdin"
         `andBy` optFlag "" "expression" `Descr` "LTLf input formulae"
         `andBy` optFlag "" "timing" `Descr` "using the benchmarking execution pattern"
         `andBy` boolFlag "minimal" `Descr` "use minimal syntax?"
         `andBy` boolFlag "pdf" `Descr` "output tableau/graph construction to PDF"
         `andBy` boolFlag "tableau" `Descr` "construct a tableau"
         `andBy` boolFlag "graph" `Descr` "Construct a proof graph"


runner :: IO ()
runner = withParseResult parser doOpt

-- BREAKS ON NEWLINE TERMINATED FILES> THIS IS BAD
doOpt :: Options -> IO ()
doOpt opts =
  if not $ null $ timing opts
  then
    do
      formText <- (if null $ inp opts
                  then if null $ expression opts
                       then getContents
                       else return $ expression opts
                  else (++) <$> (readFile $ inp opts)
                            <*> return ( if null $ expression opts
                                         then "\n" ++ expression opts
                                         else ""))
      let stringltls = filter (not . null) $ lines formText
      let ltls = take 500 $ map (\s -> (parse' s, MinimalSyntax.parse' s)) stringltls
      csvlines <- sequence $ timer (read $ timing opts) (stringify $ inp opts) sat MinimalTableau.sat ltls
      sequence_ $ map putStrLn csvlines
  else
    do
      formText <- if null $ inp opts
                  then getContents
                  else readFile $ inp opts
      if null $ out opts
        then if slow opts
             then putSatRes MinimalTableau.satString MinimalSyntax.parse' formText
             else putSatRes satString                parse'               formText
        else if slow opts
             then if graph opts
                  then makeGraphs MinimalPretty.prettyGraph   MinimalSyntax.parse' formText
                  else makeGraphs MinimalPretty.prettyTableau MinimalSyntax.parse' formText
             else if graph opts
                  then makeGraphs prettyGraph                 parse'               formText
                  else makeGraphs prettyTableau               parse'               formText
  where
    sep = "\n"
    putSatRes  s p t = putStrLn $ concatMap (\f -> s f ++ "\n") $ formulae p t
    makeGraphs g p t = sequence_ $ makeGraphAndTex g (out opts) $ formulae p t
    formulae  = flip mapString sep
  

timeItTPure :: NFData t => (a -> t) -> a -> IO (Double, a)
timeItTPure f x = timeItT $ f x `deepseq` return x


-- timeout input is in seconds
timeoutDefault :: Int -> a -> IO a -> IO a
timeoutDefault to deflt actn = fromMaybe deflt <$> timeout to actn


-- input to timer is timeout in seconds
timer :: Int -> (Int -> (Double, a) -> (Double, b) ->  String) -> (a -> Bool) -> (b -> Bool) -> [(a, b)] -> [IO String] 
timer to format opt slow obs =
  let to_mu = to * 1000000 in -- timeout in microseconds
  snd $ foldr (\(phiO,phiS) (n,rst) ->
           (n+1, (format n  <$>
                  (timeoutDefault to_mu (fromIntegral to,phiO) $ timeItTPure opt phiO) <*>
                  (timeoutDefault to_mu (fromIntegral to,phiS) $ timeItTPure slow phiS)
                 ) : rst)
           ) (0,[]) obs


stringify :: String -> Int -> (Double, LTL a) -> (Double, b) -> String
stringify name n (optTime, phi) (slowTime, _) =
  let optTimeMs  = tomillis optTime :: Int in
  let slowTimeMs = tomillis slowTime :: Int in
  let speedup = slowTimeMs - optTimeMs :: Int in
  let percentSpeedup = if slowTimeMs == 0 then "" else show $ 100 * speedup `div` slowTimeMs in
  intercalate "," [ show n,
                    mknm (takeFileName name) n,
                    show $ Syntax.formSize phi,
                    show optTimeMs,
                    show slowTimeMs,
                    show speedup,
                    percentSpeedup]
  where
    mknm name 0 = name
    mknm name n = name ++ show n
    tomillis :: (Integral b, RealFrac a) => a -> b
    tomillis n = round (n * 1000)


makeGraphAndTex :: (a -> FilePath -> FilePath -> IO ()) -> FilePath -> [a] -> [IO ()]
makeGraphAndTex maker o fs =
  snd 
    $ foldr
        (\f (n,rst) -> (n+1, maker f (fn o n ".pdf") (fn o n ".tex") : rst))
        (0, []) fs
  where
    fn o n ext | n == 0    = o ++ ".pdf"
               | otherwise = o ++ show n ++ ext
