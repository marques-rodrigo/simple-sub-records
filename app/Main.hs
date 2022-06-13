{-# LANGUAGE DisambiguateRecordFields, NamedFieldPuns #-}

import Control.Monad
import Control.Monad.Trans
import System.Console.Haskeline

import Data.List
import qualified Data.Map as Map
import qualified Data.Set as Set

import Types (Term (..), Type (..), SimpleType(..), PolymorphicType, emptyVarState)
import Parser
import Typer
import Coalescence
import Simplify
import Utils

data InferResult = InferResult
  { polyType    :: PolymorphicType
  , simpleType  :: SimpleType
  , canonType   :: CompactTypeScheme
  , simType     :: CompactTypeScheme
  , coalType    :: Type }

printState :: InferState -> IO ()
printState (InferState {varStates}) = mapM_ printBounds (Map.toList varStates)
  where 
    printBounds (x, bs) | bs /= emptyVarState
      = putStrLn $ "  " ++ show x ++ ": " ++ show bs
    printBounds (x, _)
      = putStrLn $ "  " ++ show x ++ ": no bounds"

main :: IO ()
main = runInputT defaultSettings loop
  where
    loop = do
      minput <- getInputLine "λ> "
      case minput of
        Nothing -> return ()
        Just "quit" -> return ()
        Just "" -> loop
        Just input -> liftIO (processExpr input) >> loop

processExpr :: String -> IO ()
processExpr input = do
  case parseExpr input of
    Left err -> putStr "Parse error: " >> print err
    Right term -> processTerm term

processTerm :: Term -> IO ()
processTerm term = do
  case runInfer (inferType term) initialInferenceState of
    (Left err, _) -> 
      putStr "Type error: " >> print err
    (Right inferResult, inferState) -> do
      putStr "SimpleType: " >> print inferResult
      putStrLn "InferState: " >> printState inferState
      putStrLn "Expansions: " >> printExpansions inferState
      case runInfer (coalesceSimpleType inferResult) inferState of
        (Left err, _) -> 
          putStr "Type error: " >> print err
        (Right coalResult, _) -> do
          putStr "Coalesced: " >> print coalResult

printExpansions :: InferState -> IO ()
printExpansions (InferState {expansions}) = mapM_ f (Map.toList expansions)
  where f (k,v) = putStrLn ("  " ++ show k ++ ": " ++ show v)

-- {x = 1}
rcdX = Rcd [("x", Lit 1)]

-- r with {y = 2}
withY r = (Ext r "y" (Lit 2))

-- r with {z = 3}
withZ r = (Ext r "z" (Lit 3))

-- \r -> r with {y = 2}
withYLambda = Lam "r" (Ext (Var "r") "y" (Lit 2))

-- \r -> r with {z = 3}
withZLambda = Lam "r" (Ext (Var "r") "z" (Lit 3))

-- {x = 1} with {y = 2}
extend = withY rcdX

-- ({x  = 1} with {y = 2}) with {z = 3}
extend2 = withZ $ withY rcdX

-- ({x = 1} with {y = 2}).x
extendSelOld = Sel extend "x"

-- ({x = 1} with {y = 2}).y
extendSelNew = Sel extend "y"

-- (\r -> r with {y = 2}) {x = 1}
extendLambda = App withYLambda rcdX

-- ((\r -> r with {y = 2}) {x = 1}).x
extendLambdaSelOld = Sel extendLambda "x"

-- ((\r -> r with {y = 2}) {x = 1}).y
extendLambdaSelNew = Sel extendLambda "y"

choice   = (App (App (Var "choose") (withY rcdX)) rcdX)
choiceX  = Sel choice "x"

-- fails

-- ({x = 1} with {y = 2}).z
extendSelMissing = Sel extend "z"

choiceY  = Sel choice "y"