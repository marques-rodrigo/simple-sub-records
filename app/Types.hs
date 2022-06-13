{-#LANGUAGE NamedFieldPuns #-}

module Types where

import Utils
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Tuple.Extra

type Level = Int
type UniqueId = Int
type Identifier = String
type Label = String
type Definition = (Bool, Identifier, Term)
type Program = [Definition]
type Polarity = Bool

-- Syntax terms - result from parsing, output to inference

data Term
  = Lit Integer                       -- 1
  | Var Identifier                    -- x
  | Lam Identifier Term               -- \x.M
  | App Term Term                     -- M N
  | Rcd [(Label, Term)]               -- { label : M }
  | Sel Term Label                    -- M.label
  | Let Bool Identifier Term Term     -- let [rec] x = M in N
  | Ext Term Label Term               -- M with { label = N }
  deriving (Show, Eq)

freeVars :: Term -> Set.Set Identifier
freeVars (Var x) = Set.singleton x
freeVars (App e1 e2) = freeVars e1 `Set.union` freeVars e2
freeVars (Lam x e) = x `Set.delete` freeVars e
freeVars (Let _ x e1 e2) = Set.delete x (freeVars e1 `Set.union` freeVars e2)
freeVars _ = Set.empty

-- Types - Final output of simple-sub

data Type
  = Top
  | Bot
  | Union Type Type
  | Inter Type Type
  | FunctionType Type Type
  | RecordType [(Label, Type)]
  | RecursiveType UniqueId Type
  | PrimitiveType String
  | TypeVariable UniqueId
  -- | Absent
  deriving (Eq, Ord)

-- SimpleType - result from initial inference step

type PolarVariable = (SimpleType, Bool)

data SimpleType
  = Function SimpleType SimpleType
  | Record [(Label, SimpleType)] SimpleType
  | Primitive String
  | Variable Level UniqueId
  | Abs
  | Pre SimpleType
  deriving (Eq, Ord)

class HasLevel a where
  level :: a -> Level
instance HasLevel SimpleType where
  level (Function t1 t2) = max (level t1) (level t2)
  level (Record [] row) = level row
  level (Record fs p) = max (maximum (map (level . snd) fs)) (level p)
  level (Primitive _) = 0
  level (Variable lvl _) = lvl
  level Abs = 0
  level (Pre t) = level t

varId :: SimpleType -> UniqueId
varId (Variable _ uid) = uid
varId (Pre t) = varId t
varId (Record _ p) = varId p
varId _ = undefined

isVariable :: SimpleType -> Bool
isVariable (Variable _ _) = True
isVariable _ = False

data VarState = VarState { lowerBounds :: [SimpleType], upperBounds :: [SimpleType]}
  deriving (Eq, Ord)

emptyVarState = VarState { lowerBounds = [], upperBounds = [] }

reverseState :: VarState -> VarState
reverseState VarState {lowerBounds, upperBounds}
  = VarState { lowerBounds = reverse lowerBounds, upperBounds = reverse upperBounds }

data PolymorphicType = PolymorphicType Level SimpleType

data TypeScheme
  = QuantifiedType PolymorphicType
  | SimpleType SimpleType

class TypeSchemeLike a where
  asTypeScheme :: a -> TypeScheme

instance TypeSchemeLike TypeScheme where
  asTypeScheme = id

instance TypeSchemeLike SimpleType where
  asTypeScheme = SimpleType

instance TypeSchemeLike PolymorphicType where
  asTypeScheme = QuantifiedType

-- Context 

type Context = Map.Map Identifier TypeScheme

emptyContext = Map.empty

extend :: TypeSchemeLike a => Context -> (Identifier, a) -> Context
extend ctx (x, t) = Map.insert x (asTypeScheme t) ctx

-- Errors 

data TypeError
  = UndefinedVariable Identifier
  | UndefinedLabel Identifier
  | ConstrainError SimpleType SimpleType
  | RecordScope SimpleType SimpleType
  | MissingCoOccs UniqueId

-- Pretty printing

-- instance Show Term where
--   show e =
--     case e of
--       Lit l -> show l
--       Var x -> x
--       Lam x e1 -> "λ" ++ x ++ "->" ++ show e1
--       App e1 e2 -> "(" ++ show e1 ++ " " ++ show e2 ++ ")"
--       Let False x e1 e2 -> "let " ++ show x ++ " = " ++ show e1 ++ " in " ++ show e2
--       Let True x e1 e2 -> "letrec " ++ show x ++ " = " ++ show e1 ++ " in " ++ show e2
--       Rcd members -> "{" ++ showRec members ++ "}"
--       Sel e l -> show e ++ "." ++ l
instance Show SimpleType where
  show t =
    case t of
      Function l r -> "(" ++ show l ++ " -> " ++ show r ++ ")"
      -- Function l r -> case l of
      --   Function _ _ -> "(" ++ show l ++ ") -> " ++ show r
      --   _ -> show l ++ " -> " ++ show r
      Record fs row -> "{" ++ showRec fs ++ "; " ++ show row ++ "}"
      Primitive p -> p
      Variable lvl uid -> showVar uid ++ replicate lvl '\''
      Abs -> "Abs"
      Pre t -> "Pre " ++ show t

showRec [] = ""
showRec [(n,v)] = n ++ " : " ++ show v
showRec ((n,v):xs) = n ++ " : " ++ show v ++ ", " ++ showRec xs

instance Show VarState where
  show (VarState{lowerBounds=[], upperBounds=[]}) = "emptyVarState"
  show (VarState{lowerBounds=[], upperBounds=up}) = "upperbounds = " ++ show up
  show (VarState{lowerBounds=lo, upperBounds=[]}) = "lowerbounds = " ++ show lo
  show (VarState{lowerBounds=lo, upperBounds=up})
    = "lowerbounds = " ++ show lo ++ ", upperbounds = " ++ show up

instance Show TypeScheme where
  show (QuantifiedType t) = show t
  show (SimpleType t) = show t

instance Show PolymorphicType where
  show (PolymorphicType lvl t) = show lvl ++ ": " ++ show t

instance Show TypeError where
  show e =
    case e of
      (UndefinedVariable name) -> "Variable not defined: " ++ name
      (UndefinedLabel name)    -> "Label not defined: "    ++ name
      (ConstrainError t1 t2)   -> "Cannot constrain: "     ++ show t1 ++ " < " ++ show t2
      (RecordScope t1 t2)      -> "Cannot constrain, records have different scope: "     ++ show t1 ++ " < " ++ show t2
      (MissingCoOccs uid)      -> "No coOccs for: "        ++ showVar uid

instance Show Type where
  show Top = "⊤"
  show Bot = "⊥"
  show (TypeVariable uid) = showVar uid
  show (PrimitiveType p) = p
  -- show (FunctionType l r) = case l of
  --   FunctionType _ _ -> "(" ++ show l ++ ") -> " ++ show r
  --   _ -> show l ++ " -> " ++ show r
  show (FunctionType t1 t2) = "(" ++ show t1 ++ " -> " ++ show t2 ++ ")"
  show (RecursiveType uid t) = "Rec " ++ showVar uid ++ " in (" ++ show t ++ ")"
  show (Union t1 t2) = "(" ++ show t1 ++ " ∨ " ++ show t2 ++ ")"
  show (Inter t1 t2) = "(" ++ show t1 ++ " ∧ " ++ show t2 ++ ")"
  show (RecordType fs) = "{" ++ showRec fs ++ "}"

showVar = show
-- showVar x = varNames !! x