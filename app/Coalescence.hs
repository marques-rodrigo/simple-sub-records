{-# LANGUAGE LambdaCase, NamedFieldPuns #-}

module Coalescence where

import Types
import Typer
import Utils
import Simplify

import Control.Monad
import Control.Monad.State
import Control.Monad.Extra
import Data.List
import Data.Tuple.Extra
import Data.Bifunctor (bimap)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe (fromJust, fromMaybe)
import Debug.Trace

type Coalesce a = StateT CoalesceState Infer a

type CoalesceState = Map.Map PolarVariable UniqueId

-- runCoalesce :: Coalesce a -> Infer a
-- runCoalesce m = runStateT m Map.empty

coalesceSimpleType :: SimpleType -> Infer Type
coalesceSimpleType t = evalStateT (coalesce True Set.empty t) Map.empty

coalesce :: Bool -> Set.Set PolarVariable -> SimpleType -> Coalesce Type
coalesce polarity inProcess t = case t of
  (Primitive p) -> return $ PrimitiveType p

  (Function l r) -> do
    l' <- coalesce (not polarity) inProcess l
    r' <- coalesce polarity inProcess r
    return $ FunctionType l' r'

  (Record fs p) -> RecordType <$> mapSndM (coalesce polarity inProcess) fs

  (Variable _ uid) -> do
    let polarVar = (t, polarity)
    if polarVar `Set.member` inProcess
      then findOrUpdate polarVar
      else do
        varState <- lift $ getVarState uid
        let bounds     = if polarity then lowerBounds varState else upperBounds varState
            cons       = if polarity then Union else Inter
            inProcess' = Set.insert polarVar inProcess
        boundTypes <- mapM (coalesce polarity inProcess') bounds
        let res = foldl cons (TypeVariable uid) boundTypes
        maybeRec <- gets (Map.lookup polarVar)
        return $ maybe res (`RecursiveType` res) maybeRec
  
  -- Abs -> return Absent
  (Pre t) -> coalesce polarity inProcess t

findOrUpdate :: PolarVariable -> Coalesce Type
findOrUpdate polarVar = do
  maybeRec <- gets (Map.lookup polarVar)
  TypeVariable <$> 
    case maybeRec of
      Just uid -> return uid
      Nothing -> do
        t <- lift $ freshVar 0
        modify (Map.insert polarVar (varId t))
        return (varId t)