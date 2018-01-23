{-# OPTIONS_GHC -Wall -fno-warn-unused-imports -fno-warn-name-shadowing #-}
{-# LANGUAGE TemplateHaskell,FlexibleContexts, FlexibleInstances #-}

module Tableau where

import Prelude hiding (negate, or, and, until)

import Data.List hiding (or, and)
import Data.List.Split (endBy)
import Data.Maybe (mapMaybe, isNothing, isJust, fromMaybe)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Syntax

------------------------------------------------------------------------
-- Positive-negative pairs (PNPs) and tableaus
------------------------------------------------------------------------

data PNPType
  = Norm | Temp | Term
    deriving (Show, Eq, Ord)


data PNP a
  = PNP {typ :: PNPType, pos :: Set (LTL a), neg :: Set (LTL a) }
  deriving (Eq, Ord)

instance (Eq a, Show a) => Show (PNP a) where
  show (PNP _ p n) =
    "\\left(" ++ showSet p ++ ", " ++ showSet n ++ "\\right)"                       


showSet :: Show a => Set a -> String
showSet s  | Set.null s = "\\emptyset"
           | otherwise = "\\{" ++ (intercalate "," (map show $ Set.toAscList s)) ++ "\\}"

-- simplPNP :: Ord a => PNP a -> PNP a
-- simplPNP pnp =
--     let pos' = pos pnp `Set.difference` Set.singleton top in
--     let neg' = neg pnp `Set.difference` Set.fromList [F, always $ negate end] in
--      pnp {pos = pos' `Set.difference` endForms,
--           neg = neg' `Set.difference` endForms}

--   where endForms = Set.fromList [negate end, X top]
         



newtype Tableau a = Tableau (Map (PNP a) [PNP a])

instance (Eq a, Show a) => Show (Tableau a) where
  show (Tableau t) =
    intercalate "\n" $ map showEdges (Map.toList t)
    where
      showEdges (p,succs) =
        "STATE : " ++ show p ++ "\n  "
           ++ intercalate "\n  " (map show succs)

emptyTableau :: Tableau a
emptyTableau = Tableau Map.empty

unseen :: Ord a => Tableau a -> PNP a -> Bool
unseen (Tableau t) n = Map.notMember n t

addEdges :: Ord a => PNP a -> [PNP a] -> Tableau a -> Tableau a
addEdges p succs (Tableau t) = Tableau (Map.insert p succs t)

successors :: Ord a => PNP a -> Tableau a -> [PNP a]
successors p (Tableau t) = Map.findWithDefault [] p t

------------------------------------------------------------------------
-- Tableau construction
------------------------------------------------------------------------

buildRoot :: Ord a => LTL a -> PNP a
buildRoot a = PNP Norm (Set.fromList [a, E end]) Set.empty

satisfying :: Ord a => (a -> Bool) -> Set a -> Maybe (a, Set a)
satisfying pred s = do
  let (sat, unsat) = Set.partition pred s
  (v,sat') <- Set.maxView sat
  return (v, sat' `Set.union` unsat)


tunion :: Ord a => Tableau a -> Tableau a -> Tableau a
tunion (Tableau t) (Tableau t') = Tableau $ t `Map.union` t'

getXs :: Ord a => Set (LTL a) -> Set (LTL a)
getXs s = Set.map (\(X f) -> f) $ Set.filter isX s


sigma_one :: Ord a => PNP a -> Set (LTL a)  
sigma_one  p = getXs $ pos p

sigma_two :: Ord a => PNP a -> Set (LTL a)
sigma_two  p = Set.filter
               (\f -> case f of
                      (W _ b) -> b `Set.member` neg p
                      _      -> False )
               (pos p)

sigma_three :: Ord a => PNP a -> Set (LTL a)               
sigma_three p = Set.filter
              (\f -> case f of
                      (W a _) -> (X T) `Set.member` neg p
                                 && a `Set.member` pos p
                      _      -> False)
              (pos p)

sigma_four :: Ord a => PNP a -> Set (LTL a)
sigma_four p = getXs $ neg p

sigma_five :: Ord a => PNP a -> Set (LTL a)
sigma_five  p= Set.filter
             (\f -> case f of
                     (W a b) -> a `Set.member` pos p
                                || b `Set.member` neg p
                     _      -> False)
             (neg p)

sigma :: Ord a => PNP a -> PNP a
sigma p = p {
  pos = sigma_one p `Set.union` sigma_two p `Set.union` sigma_three p,
  neg = sigma_four p `Set.union` sigma_five p
  }


desugar :: LTL a -> LTL a
desugar F = F
desugar T = F `Imp` F
desugar (P a) = P a
desugar (Imp a b) = (desugar a) `Imp` (desugar b)
desugar (And a b) = Not $ (desugar a) `Imp` Not (desugar b)  -- a&b == ~(~a+~b) == ~(a -> ~b)
desugar (Or a b) = Not (desugar a) `Imp` (desugar b)
desugar (Not a) = (desugar a) `Imp` F
desugar (WX a) = (X (desugar a `Imp` F)) `Imp` F
desugar (X a) = X $ desugar a
desugar (G a) = (desugar a) `W` F
desugar (E a) = ((desugar a `Imp` F) `W` F) `Imp` F
desugar (W a b) = desugar a `W` desugar b
desugar (U a b) = (desugar a `W` desugar b)

-- TODO End??
makeSucc :: Ord a => PNP a -> [PNP a]
makeSucc q =
  let simplPos = Set.map desugar $ pos q in
  let simplNeg = Set.map desugar $ neg q in
  if F `Set.member` pos q    -- Bot
     || T `Set.member` neg q
     || (not $ Set.null $  simplPos `Set.intersection` simplNeg)
  then []
  else case satisfying isImp (pos q) of -- (->+)
    Just (Imp a b, posq') ->
      [ constr q (Set.insert b posq') (neg q), -- need to use constr q here?????
        constr q posq' (Set.insert a $ neg q)]
    Just _ -> error "Expected Imp in posImp Case"
    Nothing ->
      case satisfying isImp (neg q) of -- ( -> -)
        Just (Imp a b, negq') ->
          [constr q (Set.insert a $ pos q) (Set.insert b negq')]
        Just _ -> error "Expected Imp in negImp case"
        Nothing ->
          case satisfying isAnd (pos q) of -- (&+)
            Just (And a b, posq') ->
              [constr q (Set.insert a $ Set.insert b posq') (neg q)]
            Just _ -> error "expected And in pos& case"
            Nothing -> 
              case satisfying isAnd (neg q) of -- (&-)
                Just (And a b, negq') ->
                  [ constr q (pos q) (Set.insert a negq'),
                    constr q (pos q) (Set.insert b negq')]
                Just _ -> error "expected And in neg& case"
                Nothing ->
                  case satisfying isOr (pos q) of -- (||+)
                    Just (Or a b, posq') ->
                      -- [q {pos = Set.insert (Not a `Imp` b) posq'}]
                      [ constr q (Set.insert a posq') (neg q),
                        constr q (Set.insert b posq') (neg q)]
                    Just _ -> error "expected Or in pos|| case"
                    Nothing ->
                      case satisfying isOr (neg q) of -- (||-) ~(a + b) == ~a*~b
                        Just (Or a b, negq') ->
                          -- [q {neg = Set.insert (Not a `Imp` b) negq'}]
                          [constr q (pos q) (Set.insert a $ Set.insert b $ negq') ]
                        Just _ -> error "expected Or in neg|| case"
                        Nothing ->
                          case satisfying isNot (pos q) of -- (~+)
                            -- Just (Not a, posq') -> [q {pos = Set.insert (a `Imp` F) posq'}]
                            Just (Not a, posq') -> [constr q posq' (Set.insert a (neg q))]
                            Just _ -> error "expected Not in neg+ case"
                            Nothing ->
                              case satisfying isNot (neg q) of -- (~-)
                                -- Just (Not b, negq') -> [q {neg = Set.insert (b `Imp` F) negq'}]
                                Just (Not b, negq') -> [constr q (Set.insert b (pos q)) negq']
                                Just _              -> error "expected Not in neg~ case"
                                Nothing ->
                                  case satisfying isG (pos q) of -- (G+)
                                    Just (G a, posq') ->
                                      -- [q {pos = Set.insert (a `W` F) posq'}]
                                      [constr q (Set.insert a $ Set.insert (WX $ G a) posq') (neg q)]
                                    Just _ -> error "expected G in G+ case"
                                    Nothing ->
                                      case satisfying isG (neg q) of -- (G-) 
                                        Just (G a, negq') ->
                                          -- [q {neg = Set.insert (a `W` F) negq'}]
                                          [ constr q (pos q) (Set.insert a negq'), 
                                            constr q (Set.insert (X $ Not $ G a) (pos q)) negq']
                                          -- ~(G a) === ~a + ~ WX G a)
                                        Just _ -> error "Expecting G in negG case"
                                        Nothing ->
                                          case satisfying isE (pos q) of -- (E+)
                                            Just (E a, posq') ->
                                              [q {pos = Set.insert a posq'},
                                               q {pos = Set.insert (X $ E a) posq'}
                                              ]
                                              -- [ q {pos = Set.insert a posq'},
                                              --   q {pos = Set.insert (X $ E a) posq'}
                                              -- ]
                                            Just _ -> error "expecting E in posE case"
                                            Nothing ->
                                              case satisfying isE (neg q) of -- (E-)
                                                Just (E a, negq') ->
                                                  [q {neg = Set.insert a $ Set.insert (X $ E a) negq'}]
                                                  -- [ q {neg = Set.insert a $ Set.insert (G $ Not a) negq'}]
                                                Just _ -> error "expecting E in negE case"
                                                Nothing ->
                                                  case satisfying isW (pos q) of -- (W+)
                                                    Just (W a b, posq') ->
                                                      [constr q (Set.insert b posq') (neg q),
                                                       constr q (posq' `Set.union` (Set.fromList [a, WX (a `W` b)])) (neg q)
                                                      ]
                                                    Just _ -> error "expected W in posW case"
                                                    Nothing ->
                                                      case satisfying isW (neg q) of -- (W-)
                                                        Just (W a b, negq') ->
                                                          [ constr q (pos q) (negq' `Set.union` Set.fromList [a,b]),
                                                            constr q
                                                              (Set.insert (X (Not (a `W` b))) (pos q))
                                                           (Set.insert b negq')]
                                                        Just _ -> error "expected W in negW case"
                                                        Nothing ->
                                                          case satisfying isU (pos q) of -- (U+)
                                                            Just (U a b, posq') ->
                                                              -- [q {pos = Set.insert ((a `W` b) `And` E b) posq'}]
                                                              [ constr q (Set.insert b posq') (neg q),
                                                                constr q (posq' `Set.union` (Set.fromList [a, X (a `U` b)])) (neg q)
                                                              ]
                                                            Just _ -> error "expected U in posU case"
                                                            Nothing ->
                                                              case satisfying isU (neg q) of -- (U-)
                                                                Just (U a b, negq') ->
                                                                  -- [q {neg = Set.insert ((a `W` b) `And` E b) negq'}]
                                                                  [ constr q (pos q) (negq' `Set.union` Set.fromList [a,b]),
                                                                    constr q (pos q) (negq' `Set.union` Set.fromList [b, X (a `U` b)])
                                                                  ] -- ~(a U b) == ~b;~a + ~b;~X(a U b))
                                                                Just _ -> error "expected U in negU case"
                                                                Nothing ->
                                                                  case satisfying isWX (pos q) of -- (WX+)
                                                                    Just (WX a, posq') -> -- WX a == ~X T + X a
                                                                      -- [constr q (Set.insert (Not $ X $ Not a) posq') (neg q)]
                                                                      [ constr q posq' (Set.insert (X T) (neg q)),
                                                                        constr q (Set.insert (X a) posq') (neg q)
                                                                      ]
                                                                    Just _ -> error "Expecting WX in posWX case"
                                                                    Nothing ->
                                                                      case satisfying isWX (neg q) of -- (WX-)
                                                                        Just (WX a, negq') ->
                                                                          -- ~(WX a) == ~(end + X a) == X T & ~ X a
                                                                          [ constr q
                                                                              (pos q `Set.union` Set.fromList [X T, Not $ X a])
                                                                              negq'
                                                                          ]
                                                                          -- [q {neg = Set.insert (X $ Not a) negq'}]
                                                                        Just _ -> error "Expecting WX in negWX case"
                                                                        Nothing ->
                                                                          let posq' = sigma_one q in
                                                                            if ((X T `Set.member` neg q)) && null posq'
                                                                            then [terminalPNP q]                -- (end)
                                                                            else [PNP Temp posq' (sigma_four q)] -- (o)
  where
    constr :: PNP a -> (Set (LTL a) -> Set (LTL a) -> PNP a)
    constr (PNP Term _ _) = PNP Term
    constr (PNP _ _ _)    = PNP Norm

    
dropTemporal :: LTL a -> LTL a
dropTemporal F = F
dropTemporal T = T
-- dropTemporal End = T
dropTemporal (X _ ) = F
dropTemporal (WX _) = T
dropTemporal (P a) = P a
dropTemporal (W a b) = dropTemporal a `Or` dropTemporal b
dropTemporal (Imp a b) = Imp (dropTemporal a) (dropTemporal b)
dropTemporal (And a b) = And (dropTemporal a) (dropTemporal b)
dropTemporal (Or  a b) = Or (dropTemporal a) (dropTemporal b)
dropTemporal (Not a) = Not (dropTemporal a)
dropTemporal (E a) = (dropTemporal a)
dropTemporal (G a) = (dropTemporal a)
dropTemporal (U _ b) = (dropTemporal b)


terminalPNP :: Ord a => PNP a -> PNP a
terminalPNP q = PNP Term (Set.map dropTemporal $ pos q) (Set.insert (X T) $ Set.map dropTemporal $ neg q)

buildTableau :: Ord a => (PNP a -> [PNP a]) -> [PNP a] -> Tableau a -> Tableau a
buildTableau _ [] t = t
buildTableau succRule (p:worklist)  t =
  let succs    = succRule p in
  let t'       = addEdges p succs t in
  let newNodes = filter (unseen t) succs in
  buildTableau succRule (worklist ++ newNodes) t'


tableau :: Ord a => LTL a -> Tableau a
tableau f = buildTableau makeSucc [buildRoot f] emptyTableau

------------------------------------------------------------------------
-- Path finding
------------------------------------------------------------------------

closed :: Ord a => PNP a -> Bool 
closed p = F `Set.member` pos p || T `Set.member` neg p
  || not (Set.null (pos p `Set.intersection` neg p))

-- isTerminal :: Ord a => PNP a -> Bool
-- isTerminal p =
--   X top `Set.member` neg p
--   && all isPrim (pos p)
--   && all isPrim (Set.delete (X top) (neg p))

isTerminal' :: PNP a -> Bool
isTerminal' p = typ p == Term

terminalPath :: Ord a => Tableau a -> Set (PNP a) -> PNP a -> Maybe [PNP a]
terminalPath _ _    p | closed p            = Nothing
terminalPath _ seen p | p `Set.member` seen = Nothing
terminalPath _ _    p | isTerminal' p        = Just [p]
terminalPath t seen p =
  let succs = successors p t in
  let paths = mapMaybe (terminalPath t (Set.insert p seen)) succs in
  case paths of
    []       -> Nothing
    (path:_) -> Just (p:path)

path :: Ord a => LTL a -> Maybe [PNP a]
path f = terminalPath (tableau f) Set.empty (buildRoot f)


------------------------------------------------------------------------
-- Satisfiability and validity checking
------------------------------------------------------------------------

valid :: Ord a => LTL a -> Bool
valid = isNothing . path . Not

sat, unsat :: Ord a => LTL a -> Bool
sat   = isJust . path
unsat = not . sat

satString :: Ord a => LTL a -> String
satString f = if sat f then "sat" else "unsat"

check :: Ord a => LTL a -> String
check f =
  if valid f
  then "valid"
  else if sat f
       then "sat" else "unsat"

doCheck :: String -> String
doCheck = check . parse'

doSatCheck :: String -> String
doSatCheck s =
  if sat $ parse' s
  then "sat"
  else "unsat"
