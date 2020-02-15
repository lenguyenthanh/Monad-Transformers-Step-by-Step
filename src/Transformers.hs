{-# LANGUAGE BlockArguments #-}

module Transformers where

-- Resource
-- https://github.com/mgrabmueller/TransformersStepByStep

import qualified Data.Map as M
import Data.Maybe

import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.IO.Class
import Control.Monad.Reader
import Control.Monad.RWS
import Control.Monad.State
import Control.Monad.Writer

-- Example Program
type Name = String -- variable names

data Exp = Lit Integer -- Literal expressions
          | Var Name -- variable
          | Plus Exp Exp -- addition
          | Abs Name Exp -- lambda expressions (Abstraction)
          | App Exp Exp -- function application
          deriving (Show)

data Value = IntVal Integer
            | FunVal Env Name Exp
            deriving (Show)

type Env = M.Map Name Value -- mapping from names to values

eval0 :: Env -> Exp -> Value
eval0 _ (Lit i) = IntVal i
eval0 env (Var name) = fromJust $ M.lookup name env
eval0 env (Plus e1 e2) = let IntVal i1 = eval0 env e1
                             IntVal i2 = eval0 env e2
                         in IntVal $ i1 + i2
eval0 env (Abs n e) = FunVal env n e
eval0 env (App e1 e2) = let v1 = eval0 env e1
                            v2 = eval0 env e2
                         in case v1 of
                              FunVal env' n body -> eval0 (M.insert n v2 env') body

-- 12+((λx → x)(4+2))
exampleExp = (Lit 12) `Plus` (App (Abs "x" (Var "x")) ((Lit 4) `Plus` (Lit 2)))
--  eval0 M.empty exampleExp

-- Converting to Monadic Style
type Eval1 a = Identity a

runEval1 :: Eval1 a -> a
runEval1 = runIdentity -- runIdentityT

-- A generalized version: eval1 :: Monad m => Env -> Exp -> m Value
eval1 :: Env -> Exp -> Eval1 Value
eval1 _ (Lit i) = pure $ IntVal i
eval1 env (Var n) = pure . fromJust $ M.lookup n env
eval1 env (Plus e1 e2) = do
                          ~(IntVal i1) <- eval1 env e1
                          ~(IntVal i2) <- eval1 env e2
                          pure $ IntVal (i1 + i2)
eval1 env (Abs n e) = pure $ FunVal env n e
eval1 env (App e1 e2) = do
                        v1 <- eval1 env e1
                        v2 <- eval1 env e2
                        case v1 of
                          FunVal env' n body -> eval1 (M.insert n v2 env') body

-- eval1 Map.empty exampleExp

-- Adding Error
type Eval2 a = ExceptT String Identity a

runEval2 :: Eval2 a -> Either String a
runEval2 = runIdentity . runExceptT


eval2a :: Env -> Exp -> Eval2 Value
eval2a _ (Lit i) = pure $ IntVal i
eval2a env (Var n) = pure . fromJust $ M.lookup n env
eval2a env (Plus e1 e2) = do
                          ~(IntVal i1) <- eval2a env e1
                          ~(IntVal i2) <- eval2a env e2
                          pure $ IntVal (i1 + i2)
eval2a env (Abs n e) = pure $ FunVal env n e
eval2a env (App e1 e2) = do
                        v1 <- eval2a env e1
                        v2 <- eval2a env e2
                        case v1 of
                          FunVal env' n body -> eval2a (M.insert n v2 env') body

-- runEval2 (eval2a M.empty exampleExp) ⇒ Right (IntVal 18)

eval2b :: Env -> Exp -> Eval2 Value
eval2b _ (Lit i) = pure $ IntVal i
eval2b env (Var n) = maybe (fail ("undefined variable: " <> n)) pure $ M.lookup n env
eval2b env (Plus e1 e2) = do
                          e1' <- eval2b env e1
                          e2' <- eval2b env e2
                          case (e1', e2') of
                            (IntVal i1, IntVal i2) ->
                              pure $ IntVal (i1 + i2)
                            _ -> throwError "type error" -- for ExceptT
eval2b env (Abs n e) = pure $ FunVal env n e
eval2b env (App e1 e2) = do
                        v1 <- eval2b env e1
                        v2 <- eval2b env e2
                        case v1 of
                          FunVal env' n body -> eval2b (M.insert n v2 env') body
                          _ -> throwError "type error"

invalid1 = Plus (Lit 1) (Abs "x" (Var "x"))
onlyVar = Var "x"
-- runEval2 (eval2b M.empty invalid1)


eval2 :: Env -> Exp -> Eval2 Value
eval2 _ (Lit i) = pure $ IntVal i
eval2 env (Var n) = case M.lookup n env of
                      (Just a) -> pure a
                      Nothing  -> throwError("unbound variable: " ++ n)
eval2 env (Plus e1 e2) = do
                          e1' <- eval2 env e1
                          e2' <- eval2 env e2
                          case (e1', e2') of
                            (IntVal i1, IntVal i2) ->
                              pure $ IntVal (i1 + i2)
                            _ -> throwError "type error in addition"
eval2 env (Abs n e) = pure $ FunVal env n e
eval2 env (App e1 e2) = do
                        v1 <- eval2 env e1
                        v2 <- eval2 env e2
                        case v1 of
                          FunVal env' n body -> eval2 (M.insert n v2 env') body
                          _ -> throwError "type error in application"

-- Hiding the Environment

type Eval3 a = ReaderT Env (ExceptT String Identity) a

runEval3 :: Env -> Eval3 a -> Either String a
runEval3 env eval3 = runIdentity . runExceptT . (runReaderT eval3) $ env

eval3a :: Exp -> Eval3 Value
eval3a (Var n) = ReaderT $ \env -> case M.lookup n env of
                                     (Just a) -> pure a
                                     Nothing -> throwError ("unbound variable: " <> n)
eval3a (Plus e1 e2) = do e1' <- eval3a e1
                         e2' <- eval3a e2
                         case (e1', e2') of
                           (IntVal i1, IntVal i2) ->
                             pure . IntVal $ i1 + i2
                           _ -> throwError "type error in addition"
eval3a (Abs n e) = ReaderT $ \env -> pure $ FunVal env n e
eval3a (App e1 e2) = do v1 <- eval3a e1
                        v2 <- eval3a e2
                        case v1 of
                          (FunVal env n body) -> local (const (M.insert n v2 env)) (eval3 body)

eval3 :: Exp -> Eval3 Value
eval3 (Lit i) = pure $ IntVal i
eval3 (Var n) = do
                r <- ask
                case M.lookup n r of
                    (Just a) -> pure a
                    Nothing  -> throwError("unbound variable: " ++ n)
eval3 (Plus e1 e2) = do
                    e1' <- eval3 e1
                    e2' <- eval3 e2
                    case (e1', e2') of
                        (IntVal i1, IntVal i2) ->
                          pure $ IntVal (i1 + i2)
                        _ -> throwError "type error in addition"
eval3 (Abs n e) = do r <- ask
                     pure $ FunVal r n e
eval3 (App e1 e2) = do
                      v1 <- eval3 e1
                      v2 <- eval3 e2
                      case v1 of
                          FunVal env n body ->  local (const (M.insert n v2 env)) (eval3 body)
                          _ -> throwError "type error in application"

-- Adding State

type Eval4 a = ReaderT Env (ExceptT String (StateT Integer Identity)) a

runEval4 :: Env -> Integer -> Eval4 a -> (Either String a, Integer)
runEval4 env n eval = runIdentity ((runStateT . runExceptT) (runReaderT eval env) $ n)

tick :: (Num s, MonadState s m) => m ()
tick = do  st <- get
           put (st + 1)

eval4 :: Exp -> Eval4 Value
eval4 (Lit i) = do  tick
                    pure $ IntVal i
eval4 (Var n) = do tick
                   r <- ask
                   case M.lookup n r of
                     (Just a) -> pure a
                     Nothing  -> throwError("unbound variable: " ++ n)
eval4 (Plus e1 e2) = do tick
                        e1' <- eval4 e1
                        e2' <- eval4 e2
                        case (e1', e2') of
                            (IntVal i1, IntVal i2) ->
                              pure $ IntVal (i1 + i2)
                            _ -> throwError "type error in addition"
eval4 (Abs n e) = do tick
                     r <- ask
                     pure $ FunVal r n e
eval4 (App e1 e2) = do  tick
                        v1 <- eval4 e1
                        v2 <- eval4 e2
                        case v1 of
                            FunVal env n body ->  local (const (M.insert n v2 env)) (eval4 body)
                            _ -> throwError "type error in application"

type Eval4' a = ReaderT Env (StateT Integer (ExceptT String Identity)) a
runEval4' :: Env -> Integer -> Eval4' a -> (Either String (a, Integer ))
runEval4' env st ev = runIdentity (runExceptT (runStateT (runReaderT ev env) st))

-- Adding Logging

type Eval5 a = ReaderT Env(ExceptT String
                          (WriterT [String] (StateT Integer Identity))) a

runEval5 :: Env -> Integer -> Eval5 a -> ((Either String a, [String]), Integer )
runEval5 env st ev =
    runIdentity (runStateT (runWriterT (runExceptT (runReaderT ev env))) st)

eval5 :: Exp -> Eval5 Value
eval5 (Lit i) = do  tick
                    pure $ IntVal i
eval5 (Var n) = do tick
                   tell [n]
                   r <- ask
                   case M.lookup n r of
                     (Just a) -> pure a
                     Nothing  -> throwError("unbound variable: " ++ n)
eval5 (Plus e1 e2) = do tick
                        e1' <- eval5 e1
                        e2' <- eval5 e2
                        case (e1', e2') of
                            (IntVal i1, IntVal i2) ->
                              pure $ IntVal (i1 + i2)
                            _ -> throwError "type error in addition"
eval5 (Abs n e) = do tick
                     r <- ask
                     pure $ FunVal r n e
eval5 (App e1 e2) = do  tick
                        v1 <- eval5 e1
                        v2 <- eval5 e2
                        case v1 of
                            FunVal env n body ->  local (const (M.insert n v2 env)) (eval5 body)
                            _ -> throwError "type error in application"
-- IO
type Eval6 a = ReaderT Env(ExceptT String
                          (WriterT [String] (StateT Integer IO))) a

runEval6 :: Env -> Integer -> Eval6 a -> IO ((Either String a, [String]), Integer )
runEval6 env st ev =
    runStateT (runWriterT (runExceptT (runReaderT ev env))) st

eval6 :: Exp -> Eval6 Value
eval6 (Lit i) = do  tick
                    liftIO $ putStrLn $ show i
                    pure $ IntVal i
eval6 (Var n) = do tick
                   tell [n]
                   r <- ask
                   case M.lookup n r of
                     (Just a) -> pure a
                     Nothing  -> throwError("unbound variable: " ++ n)
eval6 (Plus e1 e2) = do tick
                        e1' <- eval6 e1
                        e2' <- eval6 e2
                        case (e1', e2') of
                            (IntVal i1, IntVal i2) ->
                              pure $ IntVal (i1 + i2)
                            _ -> throwError "type error in addition"
eval6 (Abs n e) = do tick
                     r <- ask
                     pure $ FunVal r n e
eval6 (App e1 e2) = do  tick
                        v1 <- eval6 e1
                        v2 <- eval6 e2
                        case v1 of
                            FunVal env n body ->  local (const (M.insert n v2 env)) (eval6 body)
                            _ -> throwError "type error in application"

-- RWS

type Eval7 a = RWST Env [String] Integer (ExceptT String IO) a

runEval7 :: Env -> Integer -> Eval7 a -> IO (Either String (a, Integer, [String]))
runEval7 env n eval = runExceptT ((runRWST eval) env n)

eval7 :: Exp -> Eval7 Value
eval7 (Lit i) = do  tick
                    liftIO $ putStrLn $ show i
                    pure $ IntVal i
eval7 (Var n) = do tick
                   tell [n]
                   r <- ask
                   case M.lookup n r of
                     (Just a) -> pure a
                     Nothing  -> throwError("unbound variable: " ++ n)
eval7 (Plus e1 e2) = do tick
                        e1' <- eval7 e1
                        e2' <- eval7 e2
                        case (e1', e2') of
                            (IntVal i1, IntVal i2) ->
                              pure $ IntVal (i1 + i2)
                            _ -> throwError "type error in addition"
eval7 (Abs n e) = do tick
                     r <- ask
                     pure $ FunVal r n e
eval7 (App e1 e2) = do  tick
                        v1 <- eval7 e1
                        v2 <- eval7 e2
                        case v1 of
                            FunVal env n body ->  local (const (M.insert n v2 env)) (eval7 body)
                            _ -> throwError "type error in application"
