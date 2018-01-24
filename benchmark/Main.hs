-- You can benchmark your code quickly and effectively with Criterion. See its
-- website for help: <http://www.serpentine.com/criterion/>.
import Criterion.Main
import System.FilePath.Posix
import Data.List.Split

import Tableau
import Syntax

fileEnv :: FilePath -> IO (String, [String])
fileEnv fileName = do
  formulae <- readFile fileName
  return (takeBaseName fileName, filter (not . null) $ splitOn "\n" formulae)

getBenchFile :: Show a => [Char] -> [Char] -> a -> [Char] -> [Char]
getBenchFile file name num ext =
  "./benchmark/automatark/LTL/" ++ file ++ "/" ++ name ++ show num ++ ext

automatark :: Show a => [Char] -> [Char] -> a -> [Char] -> Benchmark
automatark file name num ext =
  env (fileEnv (getBenchFile file name num ext)) $
  \ ~(nm, phis) -> bgroup nm [bench "sat" $ nf (map (sat . parse')) phis]
  

main :: IO ()
main =
  defaultMain [
  -- bgroup "COUNTER" $ foldr (\num marks ->
  --                             automatark "counter" "counter_" num ".ltl"
  --                             : marks ) [] ([2..16] :: [Int]),
  -- bgroup "COUNTER_L" $ foldr (\num marks ->
  --                             automatark "counter" "counter_l_" num ".ltl"
  --                             : marks ) [] ([2..16] :: [Int]),
  -- bgroup "LIFT" $ foldr (\num marks ->
  --                        automatark "lift" "lift_" num ".ltl"
  --                        : marks ) [] ([2..9] :: [Int]),
  -- bgroup "LIFT_B" $ foldr (\num marks ->
  --                            automatark "lift" "lift_b" num ".ltl"
  --                            : marks) [] ([2..9] :: [Int])
     bgroup "RANDOM" $ foldr (\num marks ->
                                automatark "random" "P0.5N2L" num ".ltl"
                                : automatark "random" "P0.5N4L" num ".ltl"
                                : marks
                             ) [] [i | i <- [10..100], mod i (10 :: Int) == 0]
  ]
