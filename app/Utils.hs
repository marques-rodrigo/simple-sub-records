{-# LANGUAGE FlexibleContexts, LambdaCase #-}
module Utils where

import Control.Monad
import qualified Data.Map as Map
import Data.Set
import Control.Monad.State

--ghc.utils.monad
mapSndM :: Monad m => (b -> m c) -> [(a,b)] -> m [(a,c)]
mapSndM f xs = go xs
  where
    go []         = return []
    go ((a,b):xs) = do { c <- f b; rs <- go xs; return ((a,c):rs) }

mapFstM :: Monad m => (a -> m c) -> [(a,b)] -> m [(c,b)]
mapFstM f xs = go xs
  where
    go []         = return []
    go ((a,b):xs) = do { c <- f a; rs <- go xs; return ((c,b):rs) }

fmapMaybeM :: (Monad m) => (a -> m b) -> Maybe a -> m (Maybe b)
fmapMaybeM _ Nothing  = return Nothing
fmapMaybeM f (Just x) = f x >>= (return . Just)

when' :: (Monad m, Monoid a) => Bool -> m a -> m a
when' b ma = if b then ma else return mempty

varNames :: [String]
varNames = [1..] >>= flip replicateM ['a'..'z']

addToCache k v = modify (Map.insert k v)

cacheLookup k = gets (Map.lookup k)

cacheLookupOrElse k f = do
  gets (Map.lookup k) >>= \case
    Just v -> return v
    Nothing -> f

mergeMaybe :: (a -> a -> a) -> Maybe a -> Maybe a -> Maybe a
mergeMaybe f lhs rhs =
  case (lhs, rhs) of
    (Just lhs', Just rhs') -> Just (f lhs' rhs')
    (Just _, _) -> lhs
    (_, Just _) -> rhs
    (Nothing, Nothing) -> Nothing

closeOver :: Ord a => Set a -> (a -> Set a) -> Set a
closeOver = closeOverCached empty

closeOverCached :: Ord a => Set a -> Set a -> (a -> Set a) -> Set a
closeOverCached done todo f
  | todo == empty = done
  | otherwise = closeOverCached newDone (flatten (Data.Set.map f todo) \\ newDone) f
    where newDone = done `union` todo

flatten :: Ord a => Set (Set a) -> Set a
flatten = Data.Set.foldr union empty

getOrElseUpdate :: Ord k => k -> v -> Map.Map k v -> (v, Map.Map k v)
getOrElseUpdate k v m =
  case Map.lookup k m of
    Nothing -> (v, Map.insert k v m)
    Just val -> (val, m)

sepBy :: String -> String -> String -> String
sepBy _ "" b = b
sepBy _ a "" = a
sepBy c a b = a ++ c ++ b

insertM :: (Monad m, Ord k) => k -> m a -> Map.Map k a -> m (Map.Map k a)
insertM k v c = v >>= \u -> return $ Map.insert k u c

atIntersection f fs0 fs1 = do
  forM_ fs1 $ \(k1, v1) ->
    case lookup k1 fs0 of
      Just v0 -> f v0 v1
      Nothing -> return () 