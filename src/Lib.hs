{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Lib where

import           Control.Applicative
import           Data.Bifunctor
import           Data.Char                      ( isLower )
import           Data.Maybe
import           Data.Void

data Term v = S | K | I | B | T | V | L | M | C | (:>) (Term v) (Term v) | X v
    deriving Functor
infixl 9 :>

instance Show (Term Char) where
    showsPrec = showsPrecWith (showString . (: []))

instance Show (Term Int) where
    showsPrec = showsPrecWith (showParen True . shows)

instance Show (Term Void) where
    showsPrec = showsPrecWith absurd

showsPrecWith :: forall v . (v -> ShowS) -> Int -> Term v -> ShowS
showsPrecWith showVar = go
  where
    go :: Int -> Term v -> ShowS
    go d = \case
        S        -> showString "S"
        K        -> showString "K"
        I        -> showString "I"
        B        -> showString "B"
        T        -> showString "T"
        V        -> showString "V"
        L        -> showString "L"
        M        -> showString "M"
        C        -> showString "C"
        (:>) l r -> showParen (d > 11) $ go 11 l . go 12 r
        X v      -> showVar v

instance Read (Term Char) where
    readsPrec d = readParen (d > 11) $ maybeToList . readFull

instance Read (Term Void) where
    readsPrec d = fmap (first (fmap (\c -> error $ "Unknown term: " ++ [c])))
        . readsPrec d

readTerm :: String -> Maybe (Term Char, String)
readTerm = \case
    ('(' : cs) -> case readFull cs of
        Just (t, ')' : rest) -> Just (t, rest)
        _                    -> Nothing
    (c : cs) -> case c of
        'S' -> Just (S, cs)
        'K' -> Just (K, cs)
        'I' -> Just (I, cs)
        'B' -> Just (B, cs)
        'T' -> Just (T, cs)
        'V' -> Just (V, cs)
        'L' -> Just (L, cs)
        'M' -> Just (M, cs)
        'C' -> Just (C, cs)
        _ | isLower c -> Just (X c, cs)
          | otherwise -> Nothing
    [] -> Nothing

readTerms :: String -> ([Term Char], String)
readTerms s = case readTerm s of
    Nothing      -> ([], s)
    Just (x, s') -> let (xs, r) = readTerms s' in (x : xs, r)

readFull :: String -> Maybe (Term Char, String)
readFull s =
    let (xs, s') = readTerms s
    in  case xs of
            []      -> Nothing
            (_ : _) -> Just (foldl1 (:>) xs, s')

steps :: Term v -> [Term v]
steps x = x : maybe [] steps (step1 x)

step1, reduceKs, reduceIs, reduceOrders, reduceExploders
    :: Term v -> Maybe (Term v)
step1 t = reduceKs t <|> reduceIs t <|> reduceOrders t <|> reduceExploders t
reduceKs = reduction $ \case
    K :> x :> _ -> Just x
    _           -> Nothing
reduceIs = reduction $ \case
    I :> x -> Just x
    _      -> Nothing
reduceOrders = reduction $ \case
    B :> x :> y :> z -> Just $ x :> (y :> z)
    C :> x :> y :> z -> Just $ x :> z :> y
    T      :> x :> y -> Just $ y :> x
    V :> x :> y :> z -> Just $ z :> x :> y
    _                -> Nothing
reduceExploders = reduction $ \case
    L :> x      :> y -> Just $ x :> (y :> y)
    M           :> x -> Just $ x :> x
    S :> x :> y :> z -> Just $ x :> z :> (y :> z)
    _                -> Nothing

reduction :: (Term v -> Maybe (Term v)) -> Term v -> Maybe (Term v)
reduction s = go
  where
    go x = s x <|> case x of
        l :> r -> ((:>) <$> go l <*> pure r) <|> ((:>) <$> pure l <*> go r)
        _      -> Nothing

evaluate :: Term v -> Term v
evaluate = \case
    x :> y -> evaluate x |> evaluate y
    x      -> x

tryStep :: Term v -> Term v
tryStep = \case
    S :> x :> y :> z  -> x |> z |> (y |> z)
    K      :> x :> _y -> x
    I           :> x  -> x
    B :> x :> y :> z  -> x |> (y |> z)
    T      :> x :> y  -> y |> x
    V :> x :> y :> z  -> z |> x |> y
    L      :> x :> y  -> x |> (y |> y)
    M           :> x  -> x |> x
    C :> x :> y :> z  -> x |> z |> y
    x                 -> x

(|>) :: Term v -> Term v -> Term v
(|>) l r = tryStep (l :> r)
infixl 9 |>

abstract :: Eq v => v -> Term v -> Term v
abstract x = go
  where
    go = \case
        X x' | x == x' -> I
        l :> r         -> case (go l, go r) of
            (K :> l', K :> r') -> K :> (l' :> r')
            (K :> l', I      ) -> l'
            (I      , K :> r') -> T :> r'
            (I      , I      ) -> M
            (T :> l', K :> r') -> V :> l' :> r'
            (K :> l', M      ) -> L :> l'
            (K :> l', r'     ) -> B :> l' :> r'
            (l'     , K :> r') -> C :> l' :> r'
            (l'     , r'     ) -> S :> l' :> r'
        r -> K :> r
