{-# LANGUAGE DisambiguateRecordFields, NamedFieldPuns, ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}

module Simplify where

import Control.Monad.Extra
import Control.Monad.State
import Control.Monad.Except
import qualified Data.Set as Set
import qualified Data.Map.Lazy as Map
import Data.Maybe
import Debug.Trace

import Typer
import Types
import Utils

data CompactType = CompactType
  { vars     :: Set.Set SimpleType --UniqueId
  , prims    :: Set.Set SimpleType --Identifier
  , record   :: Maybe (Map.Map Label CompactType)
  , function :: Maybe (CompactType, CompactType) }
  deriving (Ord, Eq)

data CompactTypeScheme =
  CompactTypeScheme CompactType (Map.Map UniqueId CompactType)

type PolarType = (CompactType, Bool)

isEmpty :: CompactType -> Bool
isEmpty CompactType {vars, prims, record, function}
  = Set.null vars && Set.null prims && isNothing record && isNothing function

ct :: CompactType
ct = CompactType
  { vars     = Set.empty
  , prims    = Set.empty
  , record   = Nothing
  , function = Nothing}

emptyCt = ct

merge :: Polarity -> CompactType -> CompactType -> CompactType
merge pol lhs rhs = CompactType
  { vars     = vars lhs `Set.union` vars rhs
  , prims    = prims lhs `Set.union` prims rhs
  , record   = mergeMaybe (mergeRec pol) (record lhs) (record rhs)
  , function = mergeMaybe (mergeFun pol) (function lhs) (function rhs) }

mergeRec False = Map.unionWith (merge False)
mergeRec True  = Map.intersectionWith (merge True)

mergeFun pol (l0,r0) (l1,r1) = (merge (not pol) l0 l1, merge pol r0 r1)

data CompactState = CompactState
  { recursive :: Map.Map PolarType UniqueId
  , recVars   :: Map.Map UniqueId CompactType }

initialCompactState = CompactState
  { recursive = Map.empty
  , recVars   = Map.empty }

type Compact = StateT CompactState Infer

-- compact :: SimpleType -> Infer CompactTypeScheme
-- compact ty = do
--   (t, s) <- runStateT (go ty True Set.empty Set.empty) initialCompactState
--   return $ CompactTypeScheme t (recVars s)

-- go :: SimpleType -> Polarity -> Set.Set UniqueId -> Set.Set PolarVariable -> Compact CompactType
-- go ty pol parents inProcess =
--   case ty of
--     Primitive p ->
--       return ct { prims = Set.singleton p }
--     Function l r -> do
--       l' <- go l (not pol) Set.empty inProcess
--       r' <- go r pol Set.empty inProcess
--       return ct { function = Just (l', r') }
--     Record fs -> do
--       fs' <- mapSndM (\t -> go t pol Set.empty inProcess) fs
--       return ct { record = Just (Map.fromList fs') }
--     tv@(Variable lvl uid) -> do
--       let tv_pol  = (tv, pol)
--       if tv_pol `Set.member` inProcess
--         then if uid `Set.member` parents
--           then return ct
--           else do
--             recursive <- gets recursive
--             case Map.lookup tv_pol recursive of
--               Just id -> return ct { vars = Set.singleton id }
--               Nothing -> do
--                 b <- lift $ freshVar 0
--                 modify (\s -> s { recursive = Map.insert tv_pol (varId b) recursive })
--                 return ct { vars = Set.singleton (varId b) }
--           else do
--             recursive <- gets recursive
--             varState <- lift $ getVarState uid
--             let inProcess' = Set.insert tv_pol inProcess
--                 parents'   = Set.insert uid parents
--                 bounds = (if pol then lowerBounds else upperBounds) varState
--             compactBounds <- mapM (\t -> go t pol parents' inProcess') bounds
--             let bound = foldl (merge pol) (ct { vars = Set.singleton uid }) compactBounds
--             case Map.lookup tv_pol recursive of
--               Just id -> do
--                 recVars <- gets recVars
--                 modify (\s -> s { recVars = Map.insert id bound recVars })
--                 return $ ct { vars = Set.singleton id }
--               Nothing -> return bound

canonicalize :: SimpleType -> Infer CompactTypeScheme
canonicalize ty = do
  (t, s) <- runStateT (canonicalize' ty) initialCompactState
  return $ CompactTypeScheme t (recVars s)

canonicalize' ty = do
  ct <- compactOutermost ty True
  mergeBounds ct True Set.empty

compactOutermost :: SimpleType -> Polarity -> Compact CompactType
compactOutermost ty pol =
  case ty of
    p@(Primitive _) ->
      return ct { prims = Set.singleton p }
    Function l r -> do
      l' <- compactOutermost l (not pol)
      r' <- compactOutermost r pol
      return ct { function = Just (l', r') }
    Record fs _ -> do --todo: should ignore row?
      fs' <- mapSndM (`compactOutermost` pol) fs
      return ct { record = Just (Map.fromList fs') }
    tv@(Variable lvl uid) -> do
      InferState{varStates} <- lift get
      let tvs = closeOver (Set.singleton tv) (\case
            Variable _ id ->
              let bounds = if pol then lowerBounds else upperBounds
              in Set.fromList $ filter isVariable (bounds (varStates Map.! id))
            _ -> Set.empty)
      return ct { vars = tvs }

mergeBounds :: CompactType -> Polarity -> Set.Set PolarType -> Compact CompactType
mergeBounds ty pol inProcess
  | isEmpty ty = return ty
  | otherwise = do
    let pty = (ty, pol)
    if pty `Set.member` inProcess
      then do
        b <- findOrMakeFresh pty
        return ct { vars = Set.singleton b }
      else do
        compactBounds <- concatMapM (compactVarBounds pol) (Set.toList $ vars ty)
        let bound = foldr (merge pol) emptyCt compactBounds
            res = merge pol ty bound
            inProcess' = Set.insert pty inProcess
        fs' <- fmapMaybeM (mergeBoundsRecord pol inProcess') (record res)
        fn' <- fmapMaybeM (mergeBoundsFunction pol inProcess') (function res)
        let adapted = CompactType { vars = vars res, prims = prims res, record = fs', function = fn' }
        gets (Map.lookup pty . recursive) >>= \case
          Nothing -> return adapted
          Just uid -> do
            modify (\s -> s { recVars = Map.insert uid adapted (recVars s)})
            return ct { vars = Set.singleton (Variable 0 uid) }

compactVarBounds :: Polarity -> SimpleType -> Compact [CompactType]
compactVarBounds pol (Variable _ uid) = do
  bounds <- lift $ getVarBoundsPolar pol uid
  mapM (compactIgnoreVars pol) bounds

compactIgnoreVars :: Polarity -> SimpleType -> Compact CompactType
compactIgnoreVars pol (Variable _ _) = return emptyCt
compactIgnoreVars pol t = compactOutermost t pol

mergeBoundsFunction :: Polarity -> Set.Set PolarType -> (CompactType, CompactType) -> Compact (CompactType, CompactType)
mergeBoundsFunction pol inProcess (l, r) = do
  l' <- mergeBounds l (not pol) inProcess
  r' <- mergeBounds r pol inProcess
  return (l', r')

mergeBoundsRecord :: Polarity -> Set.Set PolarType -> Map.Map Label CompactType -> Compact (Map.Map Label CompactType)
mergeBoundsRecord pol inProcess = mapM (\x -> mergeBounds x pol inProcess)

findOrMakeFresh :: PolarType -> Compact SimpleType
findOrMakeFresh k = do
  s <- get
  m <- gets recursive
  case Map.lookup k m of
    Just uid -> return (Variable 0 uid)
    Nothing -> do
      b <- lift $ freshVar 0
      put s { recursive = Map.insert k (varId b) (recursive s) }
      return b

data SimplifyState = SimplifyState
  { allVars       :: Set.Set UniqueId
  , recursiveVars :: Map.Map UniqueId CompactType
  , coOccurences  :: Map.Map (UniqueId, Bool) (Set.Set SimpleType)
  , varSubst      :: Map.Map SimpleType (Maybe SimpleType) }
  deriving (Show)

emptySimplifyState = SimplifyState
  { allVars       = Set.empty
  , recursiveVars = Map.empty
  , coOccurences  = Map.empty
  , varSubst      = Map.empty }

type Simplify = StateT SimplifyState Infer

simplify :: CompactTypeScheme -> Infer (CompactTypeScheme, SimplifyState)
simplify cty@(CompactTypeScheme _ rVars) = do
  (st, s) <- runStateT (simplifyType cty) emptySimplifyState { allVars = Map.keysSet rVars }
  return (st, s)

simplifyType :: CompactTypeScheme -> Simplify CompactTypeScheme
simplifyType cty@(CompactTypeScheme ct rVars) = do
  gone <- analyze True ct rVars
  coOccs <- gets coOccurences
  recs <- gets recursiveVars
  traceM $ "[occ] " ++ show coOccs
  traceM $ "[rec] " ++ show recs
  removePolarVars
  unifyEquivalent
  subs <- gets varSubst
  traceM $ "[sub] " ++ show subs
  return $ CompactTypeScheme gone recs

analyze :: Polarity -> CompactType -> Map.Map UniqueId CompactType -> Simplify CompactType
analyze pol ty rVars = do
  forM_ (vars ty) $
    \(Variable _ tv) -> do
      modify (\s -> s { allVars = Set.insert tv (allVars s) })
      occs <- gets (Map.lookup (tv, pol) . coOccurences) >>= \case
        Just os -> return $ Set.intersection os (vars ty `Set.union` prims ty)
        Nothing -> return $ vars ty `Set.union` prims ty
      modify (\s -> s { coOccurences = Map.insert (tv,pol) occs (coOccurences s)})
      whenJust (Map.lookup tv rVars) $ \b -> do
        whenM (gets (not . Map.member tv . recursiveVars)) $ do
          modify (\s -> s { recursiveVars = Map.insert tv emptyCt (recursiveVars s) })
          t <- analyze pol b rVars
          modify (\s -> s { recursiveVars = Map.insert tv t (recursiveVars s) })
  rec' <- fmapMaybeM (mapM (\t -> analyze pol t rVars)) (record ty)
  fun' <- fmapMaybeM (analyzeFunction pol rVars) (function ty)
  substs <- gets varSubst
  let newVars = concatMap (\tv ->
        case Map.lookup tv substs of
          Just (Just tv2) -> [tv2]
          Just Nothing -> []
          Nothing -> [tv]
        ) (vars ty)
  return ct { vars = Set.fromList newVars, prims = prims ty, record = rec', function = fun' }

analyzeFunction pol rVars (l,r) = do
  l' <- analyze (not pol) l rVars
  r' <- analyze pol r rVars
  return (l', r')

removePolarVars :: Simplify ()
removePolarVars = do
  s <- get
  forM_ (allVars s) $ \v -> do
    unless (Map.member v (recursiveVars s)) $
      case (Map.lookup (v, True)  (coOccurences s),
            Map.lookup (v, False) (coOccurences s)) of
        (Just _, Nothing) -> eliminate v
        (Nothing, Just _) -> eliminate v
        (Nothing, Nothing) -> throwError (MissingCoOccs v)
        _ -> return ()

eliminate :: UniqueId -> Simplify ()
eliminate uid = do
  traceM $ "[!] " ++ showVar uid
  modify (\s -> s { varSubst = Map.insert (Variable 0 uid) Nothing (varSubst s)})

replace :: Polarity -> SimpleType -> SimpleType -> Simplify ()
replace pol w v = do
  coOccs <- gets coOccurences
  recVars <- gets recursiveVars
  traceM $ "[U] " ++ showVar (varId w) ++ " := " ++ showVar (varId v)
  modify (\s -> s { varSubst = Map.insert w (Just v) (varSubst s) })
  case Map.lookup (varId w) recVars of
    Just b_w | Map.member (varId w, not pol) coOccs -> do
      modify (\s -> s { recursiveVars = Map.delete (varId w) recVars })
      let b_v = fromJust $ Map.lookup (varId v) recVars
      modify (\s -> s { recursiveVars = Map.insert (varId v) (merge pol b_v b_w) (recursiveVars s)})
    Nothing ->
      gets (Map.lookup (varId w, not pol) . coOccurences) >>= \case
        Nothing -> undefined
        Just uCoOccs -> gets (Map.lookup (varId v, not pol) . coOccurences) >>= \case
          Nothing -> undefined
          Just vCoOccs -> modify (\s -> s { 
            coOccurences = Map.insert (varId v, not pol) 
                                      (Set.filter (\t -> t == v || Set.member t uCoOccs) vCoOccs) 
                                      (coOccurences s) })

unifyEquivalent :: Simplify ()
unifyEquivalent = do
  coOccs  <- gets coOccurences
  recVars <- gets recursiveVars
  allVars <- gets allVars
  forM_ (reverse $ Set.toList allVars) $ \vid -> do
    traceM $ "[v] " ++ showVar vid
                    ++ " +" ++ show (Map.lookup (vid, True) coOccs) ++ " "
                    ++ " -" ++ show (Map.lookup (vid, False) coOccs)
    forM_ [True, False] $ \pol -> do
      s <- get
      let v = Variable 0 vid
      unless (Map.member v (varSubst s)) $ do
        let maybeOccs = Map.lookup (vid, pol) coOccs
        whenJust maybeOccs $ \occs -> forM_ occs $ \w -> do
          case w of
            (Variable 0 wid) | wid /= vid && not (Map.member w (varSubst s)) && Map.member vid recVars == Map.member wid recVars
              -> replace pol w v
            p@(Primitive _) | maybe False (Set.member p) (Map.lookup (vid, not pol) coOccs)
              -> modify (\s -> s { varSubst = Map.insert v Nothing (varSubst s) })
            _ -> return ()


instance Show CompactType where
  show ct = show' ct True
    where
      show' CompactType {vars, prims, record, function} pol
        = "<" ++ v `sep` p `sep` r `sep` f ++ ">"
          where c = if pol then " ∨ " else " ∧ "
                sep = sepBy c

                v = showVars (Set.toList vars)
                p = showPrims (Set.toList prims)
                r = maybe "" ((\fs -> "{ " ++ showFields fs ++ " }"). Map.toList) record
                f = maybe "" (\(t1,t2) -> show' t1 (not pol) ++ " -> " ++ show' t2 pol) function

                showVars [] = ""
                showVars [x] = showVar (varId x)
                showVars (x : xs) = showVar (varId x) `sep` showVars xs

                showPrims [] = ""
                showPrims [p] = show p
                showPrims (p : ps) = show p `sep` showPrims ps

                showField (x,t) = x ++ " : " ++ show' t pol
                showFields [x] = showField x
                showFields (x:xs) = showField x ++ ", " ++ showFields xs


instance Show CompactTypeScheme where
  show (CompactTypeScheme ct m) = show ct ++ "\n\twhere: " ++ show m