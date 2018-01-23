{-# OPTIONS_GHC -Wall -fno-warn-unused-imports -fno-warn-name-shadowing #-}
{-# LANGUAGE TemplateHaskell,FlexibleContexts, FlexibleInstances #-}

module Test where

import Prelude hiding (negate, or, and, until)

import Syntax
import Tableau 

import Test.QuickCheck

------------------------------------------------------------------------
-- Tests
------------------------------------------------------------------------

-- a,b,c :: LTL NamedProp
-- a = P $ NamedProp "a"
-- b = P $ NamedProp "b"
-- c = P $ NamedProp "c"

-- -- prop_parseRoundTrip :: LTL NamedProp -> Property
-- -- prop_parseRoundTrip a = a === parse' (show a)

-- TODO: Big test suite > 20 non-trivial properties
--     A bunch that are satisfiable and a bunch that are unsat
--     push on infinitude stuff -- use COUNTER_L?

satisfiable :: [String]
satisfiable = ["top",
               "a",
               "a or b",
               "(G a) -> (a W b)",
               "( !( ( !(( !( ( !((! (b)))) U (!((! (a))))) ))) U (!((a) U ((X (a)))))) )",
               "(! (((a) || (a)) U ((X ((b) || ((! (b))))))))",
               "( !( ( !((X (b)))) U (!((! (((b) || (a)) U ((X (a)))))))) )",
               "( !( ( !(b)) U (!((( !( ( !((X ((X (b)))))) U (!((X (a))))) )) || (a)))) )",
               "( !( ( !(((! (b))) || (( !( ( !(a)) U (!(a))) )))) U (!((a) U (a)))) )",
               "(X (((X (a))) U (((! (( !( ( !(b)) U (!(a))) )))) U (b))))",
               "(( !( ( !(b)) U (!(a))) )) || ((( !( ( !((X (a)))) U (!(a))) )) && (a))",
               "(( !( ( !((X ((X ((X (b)))))))) U (!((a) U (a)))) )) && (b)",
               "(! ((! (((X (( !( ( !(b)) U (!(b))) )))) && (( !( ( !(b)) U (!(a))) ))))))",
               "(b) U ((! (( !( ( !(((a) || (a)) U (a))) U (!(b))) ))))",
               "(X (( !( ( !((( !( ( !((X (b)))) U (!(b))) )) U (b))) U (!((X (b))))) )))",
               "((X (( !( ( !(a)) U (!(b))) )))) U ((( !( ( !(b)) U (!(a))) )) || (a))",
               "((a) U (b)) U ((X ((( !( ( !(a)) U (!(a))) )) U (a))))",
               "(! (((! (( !( ( !(a)) U (!(a))) )))) || (( !( ( !((X (b)))) U (!(b))) ))))",
               "(! ((b) U (((X ((! ((a) U (a)))))) && (b))))",
               "((a) && (a)) U ((b) U (((! (a))) U (b)))",
               "(a) && (( !( ( !(((! (b))) U ((X (b))))) U (!((! (b))))) ))",
               "( !( ( !(b)) U (!((b) || ((! ((( !( ( !(b)) U (!(a))) )) || (a))))))) )",
               "(X ((X (((b) && (b)) && (((! (b))) U (a))))))",
               "( !( ( !((! (( !( ( !(a)) U (!(a))) ))))) U (!((b) U ((b) || (b))))) )",
               "( !( ( !((a) U (( !( ( !(((X (a))) U (a))) U (!(b))) )))) U (!(b))) )",
               "( !( ( !(a)) U (!((a) U (((b) U ((X (b)))) || (b))))) )",
               "( !( ( !(( !( ( !(b)) U (!(( !( ( !((X (a)))) U (!((X (b))))) )))) ))) U (!((X (b))))) )",
               "(b) && (( !( ( !(b)) U (!((b) U ((b) U ((! (a))))))) ))",
               "((X ((X (a))))) U ((X (((! (b))) U ((! (b))))))",
               "(( !( ( !(b)) U (!((! (a))))) )) || (( !( ( !(b)) U (!((b) && (b)))) ))",
               "((a) U ((X (a)))) || (((X (a))) && ((! (a))))",
               "( !( ( !(( !( ( !((X (b)))) U (!(a))) ))) U (!((X (( !( ( !((! (a)))) U (!(b))) )))))) )",
               "((X ((! (((X (a))) U ((! (a)))))))) && ((X (b)))",
               "(! (((X (b))) && (( !( ( !((! (a)))) U (!(( !( ( !(b)) U (!(b))) )))) ))))",
               "((X ((b) U ((b) || (a))))) U ((X ((! (a)))))",
               "(X ((X (( !( ( !((! (b)))) U (!((X ((b) || ((X (a)))))))) )))))",
               "( !( ( !((( !( ( !(b)) U (!(b))) )) U (a))) U (!(( !( ( !(a)) U (!((! (a))))) )))) )",
               "(( !( ( !(( !( ( !((a) && (b))) U (!(b))) ))) U (!(b))) )) U ((! (a)))",
               "((! (( !( ( !(a)) U (!((X ((! ((! (b))))))))) )))) U ((X (a)))",
               "((X (b))) && ((( !( ( !(a)) U (!((! (b))))) )) U ((! (a))))",
               "(((! (b))) && (( !( ( !(a)) U (!(a))) ))) && ((a) && (a))",
               "((! ((b) U ((! (b)))))) && (((X (a))) && (a))",
               "(X ((((! (b))) || (a)) U ((b) U ((X (a))))))",
               "(X ((( !( ( !((! (b)))) U (!(a))) )) && (( !( ( !((X (a)))) U (!(a))) ))))",
               "(a) U ((! ((b) || ((b) U (( !( ( !(b)) U (!(a))) ))))))",
               "((a) && ((X (b)))) && (((! (b))) && ((! (b))))",
               "( !( ( !(( !( ( !(b)) U (!((X (b))))) ))) U (!(( !( ( !((X (b)))) U (!((X (b))))) )))) )",
               "( !( ( !((X (((! (a))) U ((! (b))))))) U (!((X ((X (b))))))) )",
               "(! (( !( ( !((! ((! ((a) U (b))))))) U (!(( !( ( !(a)) U (!(b))) )))) )))",
               "(( !( ( !(a)) U (!((! (a))))) )) U (( !( ( !(a)) U (!((b) U (a)))) ))",
               "(( !( ( !((a) && ((! (a))))) U (!(a))) )) || ((! ((! (a)))))",
               "(((X ((b) U (b)))) || ((b) || (b))) U (a)",
               "((! (b))) U (((a) || (b)) || ((! ((X (a))))))"
               ]

varditest :: String
varditest = "(E a) and  ((G (a -> E b)) and (( G (b -> E a)) and (G (!a || !b))))"

unsatisfiable :: [String]
unsatisfiable = [varditest]


prop_satTerminates :: Property
prop_satTerminates = forAll (resize 3 arbitrary :: Gen (Syntax.LTL Syntax.NamedProp)) $ \a ->
  let res = Tableau.sat a in label (if res then "sat" else "unsat") True

prop_minSatTerminates :: Property
prop_minSatTerminates = forAll (resize 3 arbitrary :: Gen (LTL NamedProp)) $ \a ->
  let res = sat a in label (if res then "sat" else "unsat") True
  

failures :: Foldable t => (a -> Bool) -> t a -> [a]
failures f = foldr (\x rst -> if f x then rst else x : rst) []


return []
qcTests :: IO Bool
qcTests = $quickCheckAll

run_tests :: IO Bool
run_tests =
  let satFail = failures sat $ map parse' satisfiable in
  let unsatFail = failures unsat $ map parse' unsatisfiable in
  do
    putStrLn $ "Satisfiability: " ++ if null satFail  then "OK" else "failed"
    putStrLn $ "Unsatisfiability: " ++ if null unsatFail then "OK" else "failed"
    putStrLn "Randomized tests:"
    eqSat  <- qcTests 
    return (eqSat && null satFail  && null unsatFail)
