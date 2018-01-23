-- Tasty makes it easy to test your code. It is a test framework that can
-- combine many different types of tests into one suite. See its website for
-- help: <http://documentup.com/feuerbach/tasty>.
import qualified Test.Tasty
-- Hspec is one of the providers for Tasty. It provides a nice syntax for
-- writing tests. Its website has more info: <https://hspec.github.io>.
import Test.Tasty.Hspec
import Test.QuickCheck

import Tableau
import Syntax

main :: IO ()
main = do
    test <- testSpec "ltlf-decide" spec
    Test.Tasty.defaultMain test

spec :: Spec
spec = parallel $ do
    describe "Decision procedure" $ do
      it "terminates on arbitrary inputs" $ do
        forAll (resize 6 arbitrary :: Gen (LTL NamedProp)) $ \a ->
          let res = sat a in
            label (if res then "sat" else "unsat") True

      it "rejects infinite traces " $ do
        let a = P $ NamedProp "a"
        let b = P $ NamedProp "b"
        False `shouldBe` (sat $ ever a `Syntax.and` always (a `Imp` ever b) `Syntax.and` always (b `Imp` ever a) `Syntax.and` always (Syntax.negate a `Syntax.or` Syntax.negate b))

      it "correctly parses & accepts sat formulae" $ do
        foldr (\f b -> sat ( parse' f ) && b) True satisfiable
        
      it "correctly parses & rejects unsat formulae" $ do
        foldr (\f b -> (&&) b $ not $ sat $ parse' f ) True unsatisfiable 




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


unsatisfiable :: [String]
unsatisfiable = ["false"]
