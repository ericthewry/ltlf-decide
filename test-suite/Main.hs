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
  describe "Parser & Pretty-Printer " $ do
    it "are inverses" $ do
      forAll (resize 100 arbitrary :: Gen (LTL NamedProp)) $ \f ->
        parse' (show f) `shouldBe` f
  
  describe "Decision procedure" $ do
    it "terminates on arbitrary inputs" $ do
      forAll (resize 8 arbitrary :: Gen (LTL NamedProp)) $ \a ->
        let res = sat a in
          label (if res then "sat" else "unsat") True

    it "rejects infinite traces (De Giacomo & Vardi)" $ do
      let a = P $ NamedProp "a"
      let b = P $ NamedProp "b"
      False `shouldBe` (sat $ ever a `Syntax.and` always (a `Imp` ever b) `Syntax.and` always (b `Imp` ever a) `Syntax.and` always (Syntax.negate a `Syntax.or` Syntax.negate b))

    it "correctly parses & accepts sat formulae" $ do
      foldr (\f b -> sat ( parse' f ) && b) True satisfiables
        
    it "correctly parses & accepts valid formulae" $ do
      foldr (\f b -> (&&) b $ valid $ parse' f) True valids




satisfiables :: [String]
satisfiables = ["top",
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


valids :: [String]
valids = ["true",
         "a || !a",
           -- axioms
         "(WX(a -> b)) <-> ((WX a) -> (WX b))",          -- WkNextDistr
         "end -> !X a",                                  -- EndNextContra
         "E end",                                        -- Finite
         "(a W b) <-> (b || (a && WX (a W b)))",         -- WkUntilUnroll
         "(G a) -> G(WX a)",                             -- WkNextStep (ish)
         "(G(a -> b)) && G (a -> WX a) -> G( a -> G b)", -- Induction (ish)
           -- consequences
         "!(X true && X false)",
         "(!X a) <-> (end || X !a)",
         "(WX a) <-> X a || end",
         "(!end && WX !a -> !WX a)",
         "(WX(a && b)) <-> (WX a && WX b)",
         "(!WX a) -> WX !a",
         "(G a) <-> (a && WX (G a))",
           -- arbitrary
         "(((!(G y) W ((((X true) || r) W ((X true) || false))&&(E ((X true) || false))))&&(E ((((X true) || r) W ((X true) || false)) &&(E ((X true) || false))))) || ((!((end || false) W (X false)) || ((G !(X false)) || false)) || false))",        
         "((((X true) || false) || (WX l)) || false)",
         "(((X ((!j || true) || (!m &&(false -> m)))) W (WX (WX end)))&&(E (WX (WX end))))",
         "(WX (WX (true W ((k W a)&&(E a)))))",
         "((X (WX true)) || (((((X k) -> !v)&&(v || (X k))) W ((true || !s) || false))&&(E ((true || !s) || false))))",
         "(WX ((X ((false W true)&&(E true))) W (end || false)))",
         "((WX true) || false)",
         "(((WX (false -> p)) || (!p W (X false))) || (WX (((X z) -> !l)&&(l || (X z)))))",
         "(((WX true) || (((false || false) || !e) || false)) || !(!s W (WX end)))",
         "((X (((l W true)&&(E true)) || false)) || (WX (X (true&&l))))",
         "((((X (X false)) W (((X !v) || (!v && (false -> v)))&&(((v || false) || !(false -> v)) || (WX v))))&&(E (((X !v) || (!v&&(false -> v)))&&(((v || false) || !(false -> v)) || (WX v))))) || (((!(end W l) || ((G !l) || false)) || (WX true)) || (((false || false) || !r) || false)))"
         ]
