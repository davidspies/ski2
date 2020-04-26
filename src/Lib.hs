{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Lib where

import           Control.Applicative
import           Control.Monad.ST
import           Control.Monad.Trans            ( lift )
import           Control.Monad.Trans.Maybe
import           Control.Monad.Yield.ST
import           Data.Bifunctor
import           Data.Char                      ( isLower )
import           Data.Maybe
import           Data.STRef
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
        l :> r -> (:> r) <$> go l <|> (l :>) <$> go r
        _      -> Nothing

evaluate :: Term v -> Term v
evaluate = \case
    x :> y -> evaluate x |> evaluate y
    x      -> x

tryStep :: Term v -> Term v
tryStep x = fromMaybe x (maybeStep x)

maybeStep :: Term v -> Maybe (Term v)
maybeStep = \case
    S :> x :> y :> z -> Just $ x |> z |> (y |> z)
    K      :> x :> _ -> Just x
    I           :> x -> Just x
    B :> x :> y :> z -> Just $ x |> (y |> z)
    T      :> x :> y -> Just $ y |> x
    V :> x :> y :> z -> Just $ z |> x |> y
    L      :> x :> y -> Just $ x |> (y |> y)
    M           :> x -> Just $ x |> x
    C :> x :> y :> z -> Just $ x |> z |> y
    _                -> Nothing

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

isWHNF :: Term v -> Bool
isWHNF = \case
    x@(l :> _) | isJust $ maybeStep x -> False
               | otherwise            -> isWHNF l
    _ -> True

newtype TermRef s = TermRef (STRef s (Term (TermRef s)))

subOut :: Term (TermRef s) -> ST s (Term (TermRef s))
subOut = \case
    t@(l :> r) | isWHNF t  -> (l :>) <$> subOut r
               | otherwise -> X . TermRef <$> newSTRef t
    t -> return t

inlineWHNF :: Term (TermRef s) -> ST s (Term (TermRef s))
inlineWHNF = \case
    l :> r          -> (:>) <$> inlineWHNF l <*> inlineWHNF r
    X (TermRef ref) -> do
        x <- readSTRef ref
        y <- inlineWHNF x
        writeSTRef ref y
        return $ if isWHNF y then y else X (TermRef ref)
    x -> return x

stepLS, stepS :: forall s . Term (TermRef s) -> MaybeT (ST s) (Term (TermRef s))
stepLS t0 = do
    t0' <- lift $ inlineWHNF t0
    liftMaybe (reduceKs t0' <|> reduceIs t0' <|> reduceOrders t0') <|> go t0'
  where
    go :: Term (TermRef s) -> MaybeT (ST s) (Term (TermRef s))
    go t = case t of
        l :> r -> do
            r' <- lift $ subOut r
            case l :> r' of
                L :> x      :> y -> return $ x :> (y :> y)
                M           :> x -> return $ x :> x
                S :> x :> y :> z -> return $ x :> z :> (y :> z)
                _                -> (:> r') <$> go l
        X (TermRef ref) -> do
            v  <- lift $ readSTRef ref >>= runMaybeT . stepLS
            v' <- case v of
                Nothing -> do
                    val <- lift $ inline =<< readSTRef ref
                    error $ "Not inlined: " ++ show val
                Just v' -> return v'
            lift $ writeSTRef ref v'
            return $ X $ TermRef ref
        _ -> empty
stepS t = stepLS t <|> case t of
    l :> r -> (:> r) <$> stepS l <|> (l :>) <$> stepS r
    _      -> empty

fastSteps :: Term Void -> [Term Void]
fastSteps t0 = runYieldST $ go (absurd <$> t0)
  where
    go :: Term (TermRef s) -> YieldST s (Term Void) ()
    go t = do
        yield =<< stToPrim (inline t)
        stToPrim (runMaybeT $ stepS t) >>= \case
            Just t' -> go t'
            Nothing -> return ()

inline :: Term (TermRef s) -> ST s (Term Void)
inline = \case
    X (TermRef ref) -> inline =<< readSTRef ref
    l :> r          -> (:>) <$> inline l <*> inline r
    x               -> return $ error "unreachable" <$> x

liftMaybe :: Monad m => Maybe a -> MaybeT m a
liftMaybe = maybe empty return
