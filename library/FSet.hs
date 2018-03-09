module FSet
  (FSet()
  ,empty,null,member,insert,fromList,intersection
  ,pickImp,pickW,unfoldX,dropTemporal,terminate)
where

import Prelude hiding (or, null)

import qualified Data.Set as Set
import Data.Set (Set)

import Data.List (intercalate)

import Syntax

data FSet a = FSet { fsetF   :: Bool
                   , fsetP   :: Set a
                   , fsetImp :: Set (LTL a, LTL a)
                   , fsetX   :: Set (LTL a) -- ??? would making this an FSet improve things?
                   , fsetW   :: Set (LTL a, LTL a)
                   }
              deriving (Eq,Ord)

instance (Eq a, Show a) => Show (FSet a) where
  show s = "{ " ++ intercalate "," elts ++ " }"
    where elts = eltsFalse ++ eltsP ++ eltsImp ++ eltsX ++ eltsW
          eltsFalse = if fsetF s then ["F"] else []
          eltsP = map show $ Set.toAscList $ fsetP s
          eltsImp = map (show . uncurry Imp) $ Set.toAscList $ fsetImp s
          eltsX = map (show . X) $ Set.toAscList $ fsetX s
          eltsW = map (show . uncurry W) $ Set.toAscList $ fsetW s

empty :: FSet a
empty = FSet { fsetF   = False
             , fsetP   = Set.empty
             , fsetImp = Set.empty
             , fsetX   = Set.empty
             , fsetW   = Set.empty
             }

null :: FSet a -> Bool
null s =
  not      (fsetF s) &&
  Set.null (fsetP s) &&
  Set.null (fsetImp s) &&
  Set.null (fsetX s) &&
  Set.null (fsetW s)

member :: Ord a => LTL a -> FSet a -> Bool
member F         s = fsetF s
member (P a)     s = a     `Set.member` fsetP s
member (Imp a b) s = (a,b) `Set.member` fsetImp s
member (X a)     s = a     `Set.member` fsetX s
member (W a b)   s = (a,b) `Set.member` fsetW s

insert :: Ord a => LTL a -> FSet a -> FSet a
insert F         s = s { fsetF = True }
insert (P a)     s = s { fsetP = Set.insert a $ fsetP s }
insert (Imp a b) s = s { fsetImp = Set.insert (a,b) $ fsetImp s }
insert (X a)     s = s { fsetX = Set.insert a $ fsetX s }
insert (W a b)   s = s { fsetW = Set.insert (a,b) $ fsetW s }

fromList :: Ord a => [LTL a] -> FSet a
fromList = foldr insert empty

intersection :: Ord a => FSet a -> FSet a -> FSet a
intersection s1 s2 =
  FSet { fsetF   = fsetF s1 && fsetF s2
       , fsetP   = fsetP s1 `Set.intersection` fsetP s2
       , fsetImp = fsetImp s1 `Set.intersection` fsetImp s2
       , fsetX   = fsetX s1 `Set.intersection` fsetX s2
       , fsetW   = fsetW s1 `Set.intersection` fsetW s2
       }

pickImp :: FSet a -> Maybe ((LTL a, LTL a), FSet a)
pickImp s = (\(imp,rest) -> (imp,s { fsetImp = rest })) <$> Set.maxView (fsetImp s)

pickW :: FSet a -> Maybe ((LTL a, LTL a), FSet a)
pickW s = (\(w,rest) -> (w,s { fsetW = rest })) <$> Set.maxView (fsetW s)

unfoldX :: Ord a => FSet a -> FSet a
unfoldX = foldr insert empty . fsetX

dropTemporal :: LTL a -> LTL a
dropTemporal F = F
dropTemporal (X _) = F
dropTemporal (P a) = P a
dropTemporal (W a b) = dropTemporal a `or` dropTemporal b
dropTemporal (Imp a b) = Imp (dropTemporal a) (dropTemporal b)

terminate :: Ord a => FSet a -> FSet a
terminate s = contraX
  where dropped =
          -- first, drop all temporal bits
          s { fsetX = Set.empty
            , fsetImp = Set.map (\(a,b) -> (dropTemporal a, dropTemporal b)) $ fsetImp s
            , fsetW = Set.empty }
        collapsed =
          -- next, account for weak until
          Set.foldr (\(a,b) s' -> 
                        insert (dropTemporal a)
                        (insert (dropTemporal b) s'))
          dropped
          (fsetW s)
        contraX =
          -- finally, if there are any X's, make sure F shows up
          if Set.null $ fsetX s
          then collapsed
          else insert F collapsed
