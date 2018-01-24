{-# OPTIONS_GHC -Wall -fno-warn-unused-imports -fno-warn-name-shadowing #-}
{-# LANGUAGE TemplateHaskell,FlexibleContexts, FlexibleInstances #-}

module Syntax where

import Prelude hiding (negate, or, and, until)

import Text.Parsec hiding (label)

import Test.QuickCheck

------------------------------------------------------------------------
-- LTL syntax, pretty printing, and parsing
------------------------------------------------------------------------

data LTL a =
    F
  | P a
  | Imp (LTL a) (LTL a)
  | X (LTL a)
  | W (LTL a) (LTL a)
    deriving (Eq, Ord)

instance (Eq a, Show a) => Show (LTL a) where
  show a = simpleShow a


simpleShow :: Show a => LTL a -> String
simpleShow F = "false"
simpleShow (P a) = show a
simpleShow (X a) = group ("X " ++ simpleShow a)
simpleShow (W a F) = group ("G " ++ simpleShow a)
simpleShow (W a b) = group (simpleShow a ++ " W " ++ simpleShow b)
simpleShow (Imp F F) = "true"
simpleShow (Imp (X (Imp F F)) F) = "end"
simpleShow (Imp (X (Imp a F)) F) = group ("WX " ++ simpleShow a)
simpleShow (Imp (W (Imp a F) F) F) = group ("E " ++ simpleShow a)
simpleShow (Imp (Imp (Imp (Imp a F) F) (Imp b F)) F) = group (simpleShow a ++ "&&" ++ simpleShow b )
simpleShow (Imp (Imp a F) b) = group (simpleShow a ++ " || " ++ simpleShow b)
simpleShow (Imp a F) = group ("!" ++ simpleShow a)
simpleShow (Imp a b) = group (simpleShow a ++ " -> " ++ simpleShow b)

group :: [Char] -> String
group s = "(" ++ s ++ ")"



showPrec :: (Eq a, Show a) => Int -> LTL a -> String
showPrec 0 (W a F) = "\\always " ++ showPrec 2 a
showPrec 0 (W a b) = showPrec 1 a ++ " \\upto " ++ showPrec 0 b
showPrec 0 a = showPrec 1 a
showPrec 1 (Imp F F) = "\\top"
showPrec 1 (Imp (X (Imp F F)) F) = "\\symend"
showPrec 1 (Imp (X (Imp a F)) F) = "\\wnext " ++ showPrec 2 a
showPrec 1 (Imp (W (Imp a F) F) F) = "\\ever " ++ showPrec 2 a
showPrec 1 (Imp (Imp (Imp (Imp a F) F) (Imp b F)) F) = showPrec 2 a ++ " \\wedge " ++ showPrec 2 b
showPrec 1 (Imp (Imp a F) b) = showPrec 2 a ++ " \\vee " ++ showPrec 2 b
showPrec 1 (Imp a F) = "\\neg" ++ showPrec 2 a
showPrec 1 (Imp a b) = showPrec 2 a ++ " \\to " ++ showPrec 1 b
showPrec 1 a = showPrec 2 a
showPrec 2 (Imp F F) = "\\top"
showPrec 2 (Imp (X (Imp F F)) F) = "\\symend"
showPrec 2 (Imp (X (Imp a F)) F) = "\\wnext " ++ showPrec 2 a
showPrec 2 (Imp (W (Imp a F) F) F) = "\\ever " ++ showPrec 2 a
showPrec 2 (Imp a F) = "\\neg" ++ showPrec 2 a
showPrec 2 (W a F) = "\\always " ++ showPrec 2 a
showPrec 2 F = "\\bot"
showPrec 2 (P a) = show a
showPrec 2 (X a) = "\\next " ++ showPrec 2 a
showPrec _ a = "(" ++ showPrec 0 a ++ ")"


formSize :: LTL a -> Int
formSize F = 1
formSize (P _) = 1
formSize (Imp a b) = 1 + formSize a + formSize b
formSize (X a) = 1 + formSize a
formSize (W a b) = 1 + formSize a + formSize b

keywords :: [String]
keywords = ["o","X","next","WX","weaknext","ever","always","G","U","W","end",
            "and","or","not","implies","false","F","true","T"]
isKeyword :: String -> Bool
isKeyword x = x `elem` keywords

-- precedence order:
--   U, W
--   implication, iff
--   or
--   and
--   X, ever, always, not
--   primitives

newtype NamedProp = NamedProp { propName :: String } deriving (Eq, Ord)

instance Show NamedProp where
  show (NamedProp s) = s

instance Arbitrary NamedProp where
  arbitrary = elements $ map NamedProp $ filter (not . isKeyword) $ map (\c -> [c]) ['A'..'Z']

instance Arbitrary (LTL NamedProp) where
  arbitrary = sized formula
    where formula 0 = oneof [elements [end,F,top], P <$> arbitrary]
          formula n = do
            let sub = formula (n `div` 2)
            unop <- elements [negate,X,wkX]
            binop <- elements [and,or,W,until,Imp,iff]
            oneof [unop <$> sub, binop <$> sub <*> sub]

parse' :: String -> LTL NamedProp
parse' s =
  case parse expr "<test input>" s of
    Left err -> error $ show err
    Right a -> a

expr, impl, adds, muls, unos, atom :: Stream s m Char => ParsecT s () m (LTL NamedProp)
expr = impl `chainr1` (op kwU until <|> op kwW W) <?> "top-level expression"
impl = adds `chainr1` (op kwImplies Imp <|> op kwIff iff) <?> "implication expression"
adds = muls `chainr1` op kwOr or <?> "disjunction expression"
muls = unos `chainr1` op kwAnd and <?> "conjunction expression"
unos = try ((op kwX X <|> op kwWkX wkX <|> op kwEver ever <|> op kwAlways always <|> op kwNot negate) <*> unos) <|>
       atom <?> "unary expression"
atom = op kwFalse F <|> op kwTrue top <|> op kwEnd end <|> try prop <|> parens expr <?> "atomic expression"

prop :: Stream s m Char => ParsecT s () m (LTL NamedProp)
prop = P . NamedProp <$> identifier <?> "proposition"

op :: ParsecT s () m () -> a -> ParsecT s () m a
op sym op = try (sym *> pure op)

kwX, kwWkX, kwEver, kwAlways, kwU, kwW, kwEnd, kwAnd, kwOr, kwNot, kwImplies, kwIff, kwFalse, kwTrue :: Stream s m Char => ParsecT s () m ()
kwX = (try (kw "o") <|> try (kw "X") <|> kw "next") <?> "next operator"
kwWkX = (try (kw "WX") <|> try (kw "weaknext")) <?> "weak next operator"
kwEver = (try (symbol "<>") <|> try (kw "E") <|> kw "ever") <?> "ever operator"
kwAlways = (try (symbol "[]") <|> try (kw "G") <|> kw "always") <?> "always operator"
kwU = kw "U" <?> "strong until operator"
kwW = kw "W" <?> "weak until operator"
kwEnd = kw "end" <?> "end proposition"
kwAnd = (try (symbol "&&") <|> try (symbol "/\\") <|>
         try (symbol "*") <|> try (symbol ";") <|> kw "and") <?> "and operator"
kwOr = (try (symbol "||") <|> try (symbol "\\/") <|>
        try (symbol "+") <|> kw "or") <?> "or operator"
kwNot = (try (symbol "~") <|> try (symbol "!") <|> kw "not") <?> "negation operator"
kwImplies = (try (symbol "->") <|> try (symbol "=>") <|> kw "implies") <?> "implies operator"
kwIff = (try (symbol "<->") <|> try (symbol "<=>") <|> kw "iff") <?> "iff operator"
kwFalse = (try (kw "false") <|> kw "F") <?> "false proposition"
kwTrue = (try (kw "true") <|> kw "T") <?> "true proposition"

kw :: Stream s m Char => String -> ParsecT s () m ()
kw s = symbol s *> notFollowedBy alphaNum

symbol :: Stream s m Char => String -> ParsecT s () m ()
symbol s = ws *> string s *> pure ()

parens :: Stream s m Char => ParsecT s () m a -> ParsecT s () m a
parens = between (symbol "(") (symbol ")")

identifier :: Stream s m Char => ParsecT s () m String
identifier = do
  ws
  x <- (:) <$> letter <*> many (alphaNum <|> char '\'')
  if isKeyword x
  then unexpected $ "keyword in place of variable (" ++ x ++ ")"
  else pure x

ws, comment :: Stream s m Char => ParsecT s () m ()
ws = many (try comment <|> space *> pure ()) *> pure ()
comment = string "--" *> manyTill anyChar eol *> pure ()
  where eol = (try endOfLine *> pure ()) <|> eof

------------------------------------------------------------------------
-- LTL encodings
------------------------------------------------------------------------

top :: LTL a
top = F `Imp` F

negate :: LTL a -> LTL a
negate a = a `Imp` F

or :: LTL a -> LTL a -> LTL a
or a b = (negate a) `Imp` b

and :: LTL a -> LTL a -> LTL a
and a b = negate (negate a `or` negate b)

iff :: LTL a -> LTL a -> LTL a
iff a b = and (Imp a b) (Imp b a)

wkX :: LTL a -> LTL a
wkX = negate . X . negate

always :: LTL a -> LTL a
always a = a `W` F

ever :: LTL a -> LTL a
ever a = negate $ always $ negate a

until :: LTL a -> LTL a -> LTL a
until a b = (a `W` b) `and` ever b

end :: LTL a
end = negate $ X top

------------------------------------------------------------------------
-- LTL encodings
------------------------------------------------------------------------

isProp :: LTL a -> Bool
isProp (P _) = True
isProp _ = False

isPrim :: LTL a -> Bool
isPrim (P _) = True
isPrim F = True
isPrim _ = False

isImp :: LTL a -> Bool
isImp (Imp _ _) = True
isImp _ = False

isW :: LTL a -> Bool
isW (W _ _) = True
isW _ = False

isX :: LTL a -> Bool
isX (X _) = True
isX _ = False
