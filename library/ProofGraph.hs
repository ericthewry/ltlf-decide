{-# OPTIONS_GHC -Wall -fno-warn-unused-imports -fno-warn-name-shadowing #-}
{-# LANGUAGE TemplateHaskell,FlexibleContexts, FlexibleInstances #-}
module ProofGraph where

import Prelude hiding (negate, or, and, until)

import Data.List hiding (or, and)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map

import Syntax
import Tableau


------------------------------------------------------------------------
-- Making the Proof Graph
------------------------------------------------------------------------

closure :: Ord a => LTL a -> Set (LTL a)
closure (P v)     = Set.singleton $ P v
closure F         = Set.singleton $ F
closure (Imp a b) = Set.singleton (a `Imp` b)
                    `Set.union` closure a
                    `Set.union` closure b
closure (X a)     = Set.singleton (X a)
closure (W a b)   = Set.singleton (a `W` b)
                    `Set.union` closure a
                    `Set.union` closure b

unionMap :: Ord a => (a -> Set a) -> Set a -> Set a
unionMap f = foldr (\x acc -> f x `Set.union` acc) Set.empty

compsF :: Ord a => Set (LTL a) -> Set (PNP a)
compsF fs = makePNPs $ Set.toList $ unionMap closure fs

makePNPs :: Ord a => [LTL a] -> Set (PNP a)
makePNPs = foldr insertAll (Set.singleton (PNP Norm Set.empty Set.empty)) 

insertAll :: Ord a => LTL a -> Set (PNP a) -> Set (PNP a)
insertAll f pnps = foldr (posNegInsert f) Set.empty pnps
  where
    posNegInsert f p rst =
      Set.fromList [
        p {pos = pos p `Set.union` Set.singleton f},
        p {neg = neg p `Set.union` Set.singleton f}]
      `Set.union` rst
    
extends :: Ord a => PNP a -> PNP a -> Bool
extends q p =
  pos p `Set.isSubsetOf` pos q
  && neg p `Set.isSubsetOf` neg q
  

consistentComps :: Ord a => PNP a -> Set (PNP a)
consistentComps p =
  Set.filter (\q -> q `extends` p && consistent q) 
  $ compsF $ pos p `Set.union` neg p
  


formula :: Ord a => PNP a -> LTL a
formula p =
  Set.foldr and top (pos p)
  `and` Set.foldr (\l f -> negate l `and` f) top (neg p)

consistent :: Ord a => PNP a -> Bool
consistent = sat . formula   


sigmaGraph :: Ord a => PNP a -> Tableau a
sigmaGraph p = buildTableau succs [p] emptyTableau
  where succs p = [sigma p]

sigma_one :: Ord a => PNP a -> Set (LTL a)  
sigma_one  p = step $ pos p

sigma_four :: Ord a => PNP a -> Set (LTL a)
sigma_four p = step $ neg p

sigma_two :: Ord a => PNP a -> Set (LTL a)
sigma_two  p = Set.filter
               (\f -> case f of
                      (W _ b) -> b `Set.member` neg p
                      _      -> False
               ) (pos p)

sigma_three :: Ord a => PNP a -> Set (LTL a)               
sigma_three p = Set.filter
              (\f -> case f of
                      (W a _) -> (X top) `Set.member` neg p
                                 && a `Set.member` pos p
                      _      -> False
              ) (pos p)

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

getPrimitives :: PNP a -> PNP a
getPrimitives p = p { pos = Set.filter isProp (pos p),
                      neg = Set.filter isProp (neg p)}


--- PRE:: PNP  is complete.
proofGraph :: Ord a => PNP a -> Tableau a
proofGraph pstar = buildTableau succs [pstar] emptyTableau
  where
    succs p = map (\q -> if isTerm q
                         then q {typ = Term}
                         else q)
              $ Set.toList $ consistentComps (sigma p)
    isTerm p = end `Set.member` pos p || X top `Set.member` neg p
  

pgraphs :: Ord a => LTL a -> Tableau a
pgraphs f =
  (Tableau $ Map.insert rt roots Map.empty)
  `tunion`
  foldr (\r t -> t `tunion` proofGraph r ) (Tableau Map.empty) roots
  where
    rt = buildRoot f
    roots = Set.toList $ consistentComps rt

pgraph :: Ord a => LTL a -> Tableau a
pgraph f =
  let (rt:_) = Set.toList $ consistentComps $ buildRoot f in
  proofGraph rt

sigGraph :: Ord a => LTL a -> Tableau a
sigGraph f = sigmaGraph $ PNP Norm (Set.singleton f) Set.empty
