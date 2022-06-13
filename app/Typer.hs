{-# LANGUAGE LambdaCase, FlexibleContexts, NamedFieldPuns #-}

module Typer where

import Control.Monad
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Extra
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Tuple.Extra (second, secondM)
import Debug.Trace

import Types
import Utils

type Infer = ExceptT TypeError (State InferState)

data InferState = InferState
  { count     :: Int
  , varStates :: Map.Map UniqueId VarState
  , expansions :: Map.Map UniqueId Expansion }

initialInferenceState = InferState
  { count     = 0
  , varStates = Map.empty
  , expansions = Map.empty }

runInfer :: Infer a -> InferState -> (Either TypeError a, InferState)
runInfer m = runState (runExceptT m)

evalInfer m = evalState (runExceptT m)

typeInt = Primitive "Int"
typeBool = Primitive "Bool"
typeString = Primitive "String"

builtins :: Context
builtins = Map.map asTypeScheme $ Map.fromList
  [ ("true", typeBool)
  , ("false", typeBool)
  , ("not", Function typeBool typeBool)
  , ("succ", Function typeInt typeInt)
  , ("add", Function typeInt (Function typeInt typeInt)) ]

addBuiltinIf :: Context -> Infer Context
addBuiltinIf ctx = do
  -- traceM "builtin if"
  v <- freshVar 1
  return $ ctx `extend` ("if", PolymorphicType 0 (Function typeBool (Function v (Function v v))))

addChoice ctx = do
  a <- freshVar 1
  return $ ctx `extend` ("choose", PolymorphicType 0 (Function a (Function a a)))

inferType :: Term -> Infer SimpleType
inferType t = do
  ctx <- addBuiltinIf builtins
  ctx <- addChoice ctx
  typeTerm 0 ctx t
  -- typeTerm 0 builtins t

inferTypes :: Program -> Context -> Infer [PolymorphicType]
inferTypes [] _ = return []
inferTypes ((isRec, name, expr) : defs) ctx = do
  t <- typeLetExpr isRec ctx 0 name expr
  ts <- inferTypes defs (ctx `extend` (name, t))
  return $ t : ts

typeTerm :: Level -> Context -> Term -> Infer SimpleType
typeTerm lvl ctx term =
  case term of

    Var name -> do
      tyScheme <- envLookup ctx name
      res <- instantiate lvl tyScheme
      traceM $ "var lookup " ++ name ++ " : " ++ show res
      return res

    Lam name body -> do
      -- traceM "lambda"
      t1 <- freshVar lvl
      t2 <- typeTerm lvl (ctx `extend` (name, t1)) body
      traceM $ "lambda result " ++ show (Function t1 t2)
      return $ Function t1 t2

    App e1 e2 -> do
      -- traceM "application"
      t1 <- typeTerm lvl ctx e1
      t2 <- typeTerm lvl ctx e2
      b <- freshVar lvl
      constrain t1 (Function t2 b)
      traceM $ "app result " ++ show b
      return b

    Lit 1 -> return typeInt
    Lit 2 -> return typeBool
    Lit 3 -> return typeString

    Sel expr name -> do
      -- traceM "selection"
      t <- typeTerm lvl ctx expr
      b <- freshVar lvl
      p <- freshVar lvl
      constrain t (Record [(name, Pre b)] p)
      traceM $ "sel result " ++ show b
      return b

    Ext expr name value -> do
      -- traceM "extension"
      t1 <- typeTerm lvl ctx expr
      t2 <- typeTerm lvl ctx value
      b <- freshVar lvl
      p <- freshVar lvl
      constrain t1 (Record [(name, b)] p)  
      traceM $ "ext result " ++ show (Record [(name, Pre t2)] p)
      tryExpand (Record [(name, Pre t2)] p)

    Rcd fields -> do
      -- traceM "record"
      fs <- mapSndM (typeTerm lvl ctx) fields
      let fs' = map (\(l,t) -> (l, Pre t)) fs
      traceM $ "rcd result " ++ show (Record fs' Abs)
      return $ Record fs' Abs

    Let isRec name expr body -> do
      t <- typeLetExpr isRec ctx lvl name expr
      traceM $ "recType: " ++ show t
      typeTerm lvl (ctx `extend` (name, t)) body

typeLetExpr :: Bool -> Context -> Level -> Identifier -> Term -> Infer PolymorphicType
typeLetExpr isRec ctx lvl name expr = do
  s <- get
  res <-
    if isRec
      then do
        -- traceM "letrec"
        b <- freshVar (lvl + 1)
        t <- typeTerm (lvl + 1) (ctx `extend` (name, b)) expr
        -- traceM "letrec constrain"
        constrain t b
        return b
      else typeTerm (lvl + 1) ctx expr
  -- traceM $ "typeLetExpr: " ++ show res
  return $ PolymorphicType lvl res

envLookup :: Context -> Identifier -> Infer TypeScheme
envLookup ctx name =
  case Map.lookup name ctx of
    Nothing -> throwError $ UndefinedVariable name
    Just tyScheme -> return tyScheme

tryExpand t@(Record _ Abs) = return t
tryExpand rcd@(Record _ p) = do
  res <- 
    gets (Map.lookup (varId p) . expansions) >>= \case
      Nothing -> return rcd
      Just exp -> do
        res <- expand exp rcd
        -- traceM $ "expanded " ++ show rcd ++ " to " ++ show res
        return res
  if res == rcd then return res else tryExpand res 
tryExpand t = return t

freshVar :: MonadState InferState m => Level -> m SimpleType
freshVar lvl = do
  s <- get
  let uid = count s
  put s { count = count s + 1
        , varStates = Map.insert uid emptyVarState (varStates s) }
  -- traceM $ "fresh " ++ show (Variable lvl uid)
  return $ Variable lvl uid
class Instantiatable a where
  instantiate :: Level -> a -> Infer SimpleType

instance Instantiatable TypeScheme where
  instantiate _ (SimpleType t) = return t
  instantiate lvl (QuantifiedType t) = instantiate lvl t

instance Instantiatable PolymorphicType where
  instantiate lvl (PolymorphicType level body) = freshenAbove lvl level body 

type FreshenState = Map.Map Int SimpleType
type Freshen = StateT FreshenState Infer

freshenAbove :: Level -> Level -> SimpleType -> Infer SimpleType
freshenAbove lvl lim ty = do
  -- traceM $ "freshenAbove " ++ show ty ++ " " ++ show lvl ++ " " ++ show lim
  evalStateT (freshenAbove' lim lvl ty) Map.empty

freshenAbove' :: Level -> Level -> SimpleType -> Freshen SimpleType
freshenAbove' lvl lim t
  | level t <= lim = return t
  | otherwise = case t of
      Variable _ uid -> do
        cacheLookup uid >>= \case
          Just ty -> return ty
          Nothing -> do
            -- traceM "freshen cache miss"
            v <- lift (freshVar lvl)
            addToCache uid v
            varState <- lift (getVarState uid)
            lbs' <- reverse <$> mapM freshen (reverse $ lowerBounds varState)
            lift (updateLowerBounds (varId v) lbs')
            ubs' <- reverse <$> mapM freshen (reverse $ upperBounds varState)
            lift (updateUpperBounds (varId v) ubs')
            -- traceM $ "freshen  " ++ show (varId v) ++ " " ++ show (lbs', ubs')
            return v
      Primitive _ -> return t
      Record fs row -> do
        fs' <- mapSndM freshen fs
        row' <- freshen row -- todo: uncertain
        return $ Record fs' row'
      Function l r -> Function <$> freshen l <*> freshen r
      _ -> return t
  where freshen = freshenAbove' lvl lim

getVarState :: MonadState InferState m => Int -> m VarState
getVarState uid = do
  s <- get
  return $ varStates s Map.! uid

getVarBounds :: MonadState InferState m => Int -> m ([SimpleType], [SimpleType])
getVarBounds uid = do
  s <- getVarState uid
  return (lowerBounds s, upperBounds s)

getVarBoundsPolar :: MonadState InferState m => Polarity -> Int -> m [SimpleType]
getVarBoundsPolar pol uid = do
  s <- getVarState uid
  if pol
    then return $ lowerBounds s
    else return $ upperBounds s

updateVarState :: MonadState InferState m => Int -> ([SimpleType], [SimpleType]) -> m ()
updateVarState uid (lbs, ubs) = do
  s <- get
  let bounds = (VarState { lowerBounds = lbs, upperBounds = ubs })
  put s { varStates = Map.insert uid bounds (varStates s) }

updateUpperBounds :: MonadState InferState m => Int -> [SimpleType] -> m ()
updateUpperBounds uid bounds = do
  s <- get
  varState <- getVarState uid
  let bounds' = (VarState { lowerBounds = lowerBounds varState, upperBounds = bounds })
  put s { varStates = Map.insert uid bounds' (varStates s) }

addUpperBound uid bound = do
  (_, ubs) <- getVarBounds uid
  updateUpperBounds uid (bound : ubs)

updateLowerBounds :: MonadState InferState m => Int -> [SimpleType] -> m ()
updateLowerBounds uid bounds = do
  s <- get
  varState <- getVarState uid
  let bounds' = (VarState { lowerBounds = bounds, upperBounds = upperBounds varState })
  put s { varStates = Map.insert uid bounds' (varStates s) }

addLowerBound uid bound = do
  (lbs, _) <- getVarBounds uid
  updateLowerBounds uid (bound : lbs)

type ConstrainState = Set.Set (SimpleType, SimpleType)
type Constrain = StateT ConstrainState Infer

constrain :: SimpleType -> SimpleType -> Infer ()
constrain t0 t1 = do
  t0 <- tryExpand t0
  t1 <- tryExpand t1
  traceM $ "constraining " ++ show t0 ++  " < " ++ show t1
  evalStateT (constrain' t0 t1) Set.empty

constrain' :: SimpleType -> SimpleType -> Constrain ()
constrain' t0 t1 | t0 == t1 = return ()
constrain' t0 t1 = do
  t0 <- lift $ tryExpand t0
  t1 <- lift $ tryExpand t1
  -- traceM $ "constraining " ++ show t0 ++  " < " ++ show t1
  let pair = (t0, t1)
  isCached <- cacheLookup pair
  if isCached
    then return () -- traceM "cached"
    else do
      case pair of
        (_, Variable _ _) -> addToCache pair
        (Variable _ _, _) -> addToCache pair
        _ -> return ()

      case pair of
        (Function l0 r0, Function l1 r1) -> do
          -- traceM "function contravariant"
          constrain' l1 l0
          -- traceM "function covariant"
          constrain' r0 r1

        (Pre _, Abs) -> return () --traceM $ "constrain Pre < Abs"

        (Pre f0, Pre f1) -> do
          -- traceM "constrain Pre"
          constrain' f0 f1

        -- for each field in fs0 missing from fs1
        -- create an analogue with a fresh type variable to insert in fs1
        (Record fs0 p0, Record fs1 p1) -> do
          missing <- concatMapM (\(label, _) ->
            case lookup label fs1 of
              Just _ -> return []
              Nothing -> do
                -- traceM $ "missing field " ++ label
                b <- lift $ freshVar (level t1) -- todo: uncertain about level
                return [(label, b)]) fs0

          if null missing
            then do 
              -- traceM $ "rhs had no missing fields"
              forM_ fs1 (\(label, ty1) -> do
                -- traceM $ "record fields"
                case lookup label fs0 of
                  Nothing -> constrain' Abs ty1
                  Just ty0 -> constrain' ty0 ty1)
              -- traceM $ "record rows"
              constrain' p0 p1
            else do
              -- traceM "rhs had missing fields"
              -- traceM "new row"
              p' <- lift $ freshVar (level t1)
              let exp = (p1, Record missing p')
              lift $ addExpansion exp
              t1 <- lift $ expand exp t1
              -- traceM $ "redo records"
              constrain' t0 t1

        (Variable _ uid, t1) | level t1 <= level t0 -> do
          lift $ addUpperBound uid t1
          (lbs, ubs) <- lift $ getVarBounds uid
          -- traceM $ "constraining lowerbounds " ++ show lbs ++ " < " ++ show t1
          mapM_ (`constrain'` t1) lbs

        (_, Variable _ uid) | level t0 <= level t1 -> do
          lift $ addLowerBound uid t0
          (lbs, ubs) <- lift $ getVarBounds uid
          -- traceM $ "constraining upperbounds " ++ show t0 ++ " < " ++ show ubs
          mapM_ (t0 `constrain'`) ubs

        (Variable _ _, rhs0) -> do
          rhs <- extrude rhs0 False (level t0)
          -- traceM "extrude rhs"
          constrain' t0 rhs

        (lhs0, Variable _ _) -> do
          lhs <- extrude lhs0 True (level t1)
          -- traceM "extrude lhs"
          constrain' lhs t1

        _ -> throwError $ ConstrainError t0 t1
  where
    addToCache x = modify (Set.insert x)
    cacheLookup x = gets (Set.member x)

addExpansion :: Expansion -> Infer ()
addExpansion exp@(row, rcd) = do 
  -- traceM $ "expansion " ++ show exp
  modify (\s -> s { expansions = Map.insert (varId row) exp (expansions s) })
  expandVarStates exp

-- Expansion
type Expansion = (SimpleType, SimpleType)

class Expandable a where
  expand :: Expansion -> a -> Infer a

instance Expandable SimpleType where
  expand sub@(row, t'@(Record fs' p')) t = case t of
    (Function l r) -> do
      l' <- expand sub l
      r' <- expand sub r
      return $ Function l' r'
    (Pre t) -> Pre <$> expand sub t
    (Record fs p) | p == row -> return $ Record (fs ++ fs') p'
    (Record fs p) -> do
      fs' <- mapSndM (expand sub) fs
      return $ Record fs' p
    (Variable _ uid) | uid == varId row -> return t'
    t -> return t

instance Expandable VarState where
  expand sub (VarState {lowerBounds, upperBounds}) = do
    lbs <- expand sub lowerBounds
    ubs <- expand sub upperBounds
    return $ VarState { lowerBounds = lbs, upperBounds = ubs}

instance Expandable a => Expandable [a] where
  expand sub = mapM (expand sub)

expandVarStates :: Expansion -> Infer ()
expandVarStates sub = do
  states <- gets varStates
  states' <- mapM (expand sub) states
  modify (\s -> s {varStates = states'})

type ExtrudeState = Map.Map PolarVariable SimpleType
type Extrude a = StateT ExtrudeState Constrain a

extrude :: SimpleType -> Polarity -> Level -> Constrain SimpleType
extrude t pol lvl = evalStateT (extrude' t pol lvl) Map.empty

extrude' :: SimpleType -> Polarity -> Level -> Extrude SimpleType
extrude' t pol lvl
  | level t <= lvl = return t
  | otherwise = case t of
    Function l r ->
      Function
        <$> extrude' l (not pol) lvl
         *> extrude' r pol lvl

    Pre t -> extrude' t pol lvl

    Record fs row -> do
      fs' <- mapSndM (\t-> extrude' t pol lvl) fs
      row' <- extrude' row pol lvl -- todo: uncertain
      return $ Record fs' row'

    Variable _ uid -> do
      cacheLookupOrElse (t, pol) (do
        nvs <- lift2 $ freshVar lvl
        addToCache (t,pol) nvs
        (lbs, ubs) <- lift2 $ getVarBounds uid
        if pol
          then do
            lift2 $ updateUpperBounds uid (nvs : ubs)
            lbs' <- mapM (\t -> extrude' t pol lvl) lbs
            lift2 $ updateLowerBounds (varId nvs) lbs'
          else do
            lift2 $ updateLowerBounds uid (nvs : lbs)
            ubs' <- mapM (\t -> extrude' t pol lvl) ubs
            lift2 $ updateUpperBounds (varId nvs) ubs'
        return nvs)

    Primitive _ -> return t

lift2 :: Infer a -> Extrude a
lift2 = lift . lift