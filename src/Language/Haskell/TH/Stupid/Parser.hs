{-# LANGUAGE LambdaCase #-}
module Language.Haskell.TH.Stupid.Parser where

import Control.Applicative
import Control.Monad (ap)
import Data.Bifunctor (first)
import Data.Char
import Data.List (foldl1')


newtype Parser m a = Parser { runParser :: String -> m (Either String (a, String)) }

instance Functor m => Functor (Parser m) where
  fmap f (Parser g) = Parser (fmap (fmap (first f)) . g)

-- TODO: This could have an 'Applicative' constraint
instance Monad m => Applicative (Parser m) where
  pure x = Parser (\s -> pure (Right (x, s)))
  (<*>) = ap

instance Monad m => Monad (Parser m) where
  Parser g >>= f = Parser (\s -> g s >>= \case
                                   Right (x, s') -> runParser (f x) s'
                                   Left err -> return (Left err))

instance Monad m => Alternative (Parser m) where
  empty = Parser (\_ -> return (Left "empty"))
  Parser f <|> Parser g =
    Parser (\s -> f s >>= \case
                    Right (x, s') -> return (Right (x, s'))
                    Left err -> g s >>= \case
                                  Right res -> return (Right res)
                                  Left err' -> return (Left (err ++ " | " ++ err')))

instance Monad m => MonadFail (Parser m) where
  fail err = Parser (\_ -> return (Left err))

liftParser :: Functor m => m a -> Parser m a
liftParser act = Parser (\s -> (\x -> Right (x, s)) <$> act)

psatisfy :: Monad m => (Char -> Bool) -> Parser m Char
psatisfy pr = Parser (\s -> case s of [] -> return (Left "satisfy failed")
                                      x:xs | pr x -> return (Right (x, xs))
                                           | otherwise -> return (Left "satisfy on empty input"))

pspaces :: Monad m => Parser m ()
pspaces = many (psatisfy isSpace) >> return ()

pchar :: Monad m => Char -> Parser m ()
pchar c = psatisfy (== c) >> return ()

choice :: Monad m => [Parser m a] -> Parser m a
choice [] = empty
choice ps = foldl1' (<|>) ps

psepBy :: Monad m => Parser m a -> Parser m sep -> Parser m [a]
psepBy p psep = (do (:) <$> p <*> many (psep >> p)) <|> return []
