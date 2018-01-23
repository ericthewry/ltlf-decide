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
  | T
  | P a
  | Imp (LTL a) (LTL a)
  | And (LTL a) (LTL a)
  | Or  (LTL a) (LTL a)
  | Not (LTL a)
--  | End               -- EndOfTime
  | WX (LTL a)        -- WeakNext
  | X  (LTL a)        -- Next
  | E (LTL a)         -- Ever
  | G (LTL a)         -- Globally
  | W (LTL a) (LTL a) -- WeakUntil
  | U (LTL a) (LTL a) -- Until
    deriving (Eq, Ord)

instance (Eq a, Show a) => Show (LTL a) where
  show a = showPrec 0 a
    where
      showPrec :: (Eq a, Show a) => Int -> LTL a -> String
      showPrec 0 (U a b) = showPrec 1 a ++ " \\until " ++ showPrec 1 b
      showPrec 0 (W a b) = showPrec 1 a ++ " \\upto " ++ showPrec 0 b
      showPrec 0 a = showPrec 1 a
      showPrec 1 T = "\\top"
      showPrec 1 (Not (X T)) = "\\symend"
      showPrec 1 (WX a) = "\\wnext " ++ showPrec 2 a
      showPrec 1 (E a) = "\\ever " ++ showPrec 2 a
-- not quite working for some reason---breaks round-tripping. probably a problem w/equality
--      showPrec 1 (Imp (Imp (Imp (Imp (W a b) F) F) (Imp (Imp (W (Imp b' F) F) F) F)) F)
--        | b == b' = showPrec 1 a ++ " U " ++ showPrec 0 b
      showPrec 1 (And a b) = showPrec 2 a ++ " \\wedge " ++ showPrec 2 b
      showPrec 1 (Or a b) = showPrec 2 a ++ " \\vee " ++ showPrec 2 b
      showPrec 1 (Not a) = "\\neg" ++ showPrec 2 a
      showPrec 1 (Imp a b) = showPrec 2 a ++ " \\to " ++ showPrec 1 b
      showPrec 1 a = showPrec 2 a
      showPrec 2 T = "\\top"
      showPrec 2 (Not (X T)) = "\\symend"
      showPrec 2 (WX a) = "\\wnext " ++ showPrec 2 a
      showPrec 2 (E a) = "\\ever " ++ showPrec 2 a
      showPrec 2 (Not a) = "\\neg" ++ showPrec 2 a
      showPrec 2 (G a) = "\\always " ++ showPrec 2 a
      showPrec 2 F = "\\bot"
      showPrec 2 (P a) = show a
      showPrec 2 (X a) = "\\next " ++ showPrec 2 a
      showPrec _ a = "(" ++ showPrec 0 a ++ ")"

formSize :: LTL a -> Int
formSize T = 1
formSize F = 1
formSize (P _) = 1
formSize (Imp a b) = 1 + formSize a + formSize b
formSize (And a b) = 1 + formSize a + formSize b
formSize (Or a b) = 1 + formSize a + formSize b
formSize (Not a) = 1 + formSize a
formSize (WX a) = 1 + formSize a
formSize (X a) = 1 + formSize a
formSize (E a) = 1 + formSize a
formSize (G a) = 1 + formSize a
formSize (U a b) = 1 + formSize a + formSize b
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
    where formula 0 = oneof [elements [end,F,T], P <$> arbitrary]
          formula n = do
            let sub = formula (n `div` 2)
            unop <- elements [Not,X,WX]
            binop <- elements [And,Or,W,U,Imp,iff]
            oneof [unop <$> sub, binop <$> sub <*> sub]

parse' :: String -> LTL NamedProp
parse' s =
  case parse expr "<test input>" s of
    Left err -> error $ show err
    Right a -> a

expr, impl, adds, muls, unos, atom :: Stream s m Char => ParsecT s () m (LTL NamedProp)
expr = impl `chainr1` (op kwU U <|> op kwW W) <?> "top-level expression"
impl = adds `chainr1` (op kwImplies Imp <|> op kwIff iff) <?> "implication expression"
adds = muls `chainr1` op kwOr Or <?> "disjunction expression"
muls = unos `chainr1` op kwAnd And <?> "conjunction expression"
unos = try ((op kwX X <|> op kwWkX WX <|> op kwEver E <|> op kwAlways G <|> op kwNot Not) <*> unos) <|>
       atom <?> "unary expression"
atom = op kwFalse F <|> op kwTrue T <|> op kwEnd end <|> try prop <|> parens expr <?> "atomic expression"

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

iff :: LTL a -> LTL a -> LTL a
iff a b = And (Imp a b) (Imp b a)

end,top :: LTL a
end = Not $ X T
top = T

and, or :: LTL a -> LTL a -> LTL a
and = And
or = Or

negate,always, ever :: LTL a -> LTL a
negate = Not
always = G
ever = E

------------------------------------------------------------------------
-- LTL encodings
------------------------------------------------------------------------

isProp :: LTL a -> Bool
isProp (P _) = True
isProp _ = False

isPrim :: LTL a -> Bool
isPrim (P _) = True
isPrim F = True
isPrim T = True
isPrim _ = False

isImp :: LTL a -> Bool
isImp (Imp _ _) = True
isImp _ = False

isAnd :: LTL a -> Bool
isAnd (And _ _ ) = True
isAnd _ = False

isOr :: LTL a -> Bool
isOr (Or _ _ ) = True
isOr _ = False

isNot :: LTL a -> Bool
isNot (Not _) = True
isNot _ = False

-- isEnd :: LTL a -> Bool
-- isEnd End = True
-- isEnd _ = False

isClass :: LTL a -> Bool
isClass F = True
isClass T = True
isClass (Imp _ _) = True
isClass (And _ _) = True
isClass (Or _ _) = True
isClass (Not _) = True
isClass _ = False

isTemporal :: LTL a -> Bool
isTemporal (WX _ ) = True
isTemporal (X _ ) = True
isTemporal (E _ ) = True
isTemporal (G _) = True
isTemporal (W _ _) = True
isTemporal (U _ _ ) = True
isTemporal _ = False


isW :: LTL a -> Bool
isW (W _ _) = True
isW _ = False

isX :: LTL a -> Bool
isX (X _) = True
isX _ = False

isG :: LTL a -> Bool
isG (G _ ) = True
isG _ = False

isE :: LTL a -> Bool
isE (E _ ) = True
isE _ = False

isU :: LTL a -> Bool
isU (U _ _ ) = True
isU _ = False

isWX :: LTL a -> Bool
isWX (WX _) = True
isWX _ = False


