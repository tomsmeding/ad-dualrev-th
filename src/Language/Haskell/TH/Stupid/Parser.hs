{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
module Language.Haskell.TH.Stupid.Parser where

import Control.Applicative
import Control.Monad (ap)
import Data.Char
import Data.List (foldl1')


data Result a = TryNext String
              | Fatal String
              | Ok a String
  deriving (Show, Functor)

newtype Parser m a = Parser { runParser :: String -> m (Result a) }
  deriving (Functor)

-- TODO: This could have an 'Applicative' constraint
instance Monad m => Applicative (Parser m) where
  pure x = Parser (\s -> pure (Ok x s))
  (<*>) = ap

instance Monad m => Monad (Parser m) where
  Parser g >>= f = Parser (\s -> g s >>= \case
                                   Ok x s' -> runParser (f x) s'
                                   TryNext err -> return (TryNext err)
                                   Fatal err -> return (Fatal err))

instance Monad m => Alternative (Parser m) where
  empty = Parser (\_ -> return (TryNext "empty"))
  Parser f <|> Parser g =
    Parser (\s -> f s >>= \case
                    Ok x s' -> return (Ok x s')
                    TryNext err -> g s >>= \case
                                     Ok x s' -> return (Ok x s')
                                     TryNext err' -> return (TryNext (err ++ " | " ++ err'))
                                     Fatal err' -> return (Fatal err')
                    Fatal err -> return (Fatal err))

instance Monad m => MonadFail (Parser m) where
  fail err = Parser (\_ -> return (TryNext err))

runParser' :: Monad m => Parser m a -> String -> m (Either String (a, String))
runParser' (Parser g) s = g s >>= \case Ok x s' -> return (Right (x, s'))
                                        TryNext err -> return (Left err)
                                        Fatal err -> return (Left err)

liftParser :: Functor m => m a -> Parser m a
liftParser act = Parser (\s -> (\x -> Ok x s) <$> act)

psatisfy :: Monad m => (Char -> Bool) -> Parser m Char
psatisfy pr = Parser $ \s -> case s of
  [] -> return (TryNext "psatisfy on empty input")
  x:xs | pr x -> return (Ok x xs)
       | otherwise -> return (TryNext "psatisfy failed")

pchar :: Monad m => Char -> Parser m ()
pchar c = Parser $ \s -> case s of
  [] -> return (TryNext "pchar on empty input")
  x:xs | x == c -> return (Ok () xs)
       | otherwise -> return (TryNext $ "pchar " ++ show c ++ " but input has " ++ show x)

label :: Monad m => String -> Parser m a -> Parser m a
label name (Parser g) = Parser (\s ->
  g s >>= \case Ok x s' -> return (Ok x s')
                TryNext _ -> return (TryNext ("Expected " ++ name))
                Fatal err -> return (Fatal err))

fatal :: Monad m => String -> Parser m a
fatal err = Parser (\_ -> return (Fatal err))

pspaces :: Monad m => Parser m ()
pspaces = many (psatisfy isSpace) >> return ()

choice :: Monad m => [Parser m a] -> Parser m a
choice [] = empty
choice ps = foldl1' (<|>) ps

psepBy :: Monad m => Parser m a -> Parser m sep -> Parser m [a]
psepBy p psep = (do (:) <$> p <*> many (psep >> p)) <|> return []
