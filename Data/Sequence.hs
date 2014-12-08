-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Sequence
-- Copyright   :  (c) Ross Paterson 2005
--                (c) Louis Wasserman 2009
--                (c) David Feuer 2014
-- License     :  BSD-style

{-# LANGUAGE
  CPP
 ,DataKinds
 ,ScopedTypeVariables
 ,KindSignatures
 ,GADTs
 ,RankNTypes
 ,TypeFamilies
 ,StandaloneDeriving
 ,GeneralizedNewtypeDeriving
 ,DeriveFunctor
 ,FlexibleInstances
 ,FlexibleContexts
 ,DeriveFoldable
 ,DeriveDataTypeable
 #-}

module Data.Sequence (Seq, (<|), (|>), (><), index, empty, viewl, viewr, ViewL(..), ViewR(..), splitAt) where
import Data.Foldable
-- import Data.Coerce
import Data.Monoid
import GHC.Exts
import Data.Data
import Prelude hiding (splitAt)
import Control.Applicative hiding (empty)
import Data.Traversable

infixr 5 `consTree`
infixl 5 `snocTree`

infixr 5 ><
infixr 5 <| , :<
infixl 5 |> , :>

data Nat = Z | S Nat

data Tree23 (n::Nat) a where
  Elem :: a -> Tree23 Z a
  Node2 :: {-# UNPACK #-} !Int -> Tree23 n a -> Tree23 n a -> Tree23 (S n) a
  Node3 :: {-# UNPACK #-} !Int -> Tree23 n a -> Tree23 n a -> Tree23 n a -> Tree23 (S n) a

traverse23 :: Applicative f => (a -> f b) -> Tree23 k a -> f (Tree23 k b)
traverse23 f (Elem a) = Elem <$> f a
traverse23 f (Node2 v a b) = Node2 v <$> traverse23 f a <*> traverse23 f b
traverse23 f (Node3 v a b c) = Node3 v <$> traverse23 f a <*> traverse23 f b <*> traverse23 f c

size23 :: Tree23 (n::Nat) a -> Int
size23 (Elem _) = 1
size23 (Node2 n _ _) = n
size23 (Node3 n _ _ _) = n

node2 :: Tree23 n a -> Tree23 n a -> Tree23 (S n) a
node2 a b = Node2 (size23 a + size23 b) a b

node3 :: Tree23 n a -> Tree23 n a -> Tree23 n a -> Tree23 (S n) a
node3 a b c = Node3 (size23 a + size23 b + size23 c) a b c

consTree        :: Tree23 n a -> FingerTree n a -> FingerTree n a
consTree a Empty        = Single a
consTree a (Single b)   = deep (One a) Empty (One b)
consTree a (Deep s (Four b c d e) m sf) = m `seq`
    Deep (size23 a + s) (Two a b) (node3 c d e `consTree` m) sf
consTree a (Deep s (Three b c d) m sf) =
    Deep (size23 a + s) (Four a b c d) m sf
consTree a (Deep s (Two b c) m sf) =
    Deep (size23 a + s) (Three a b c) m sf
consTree a (Deep s (One b) m sf) =
    Deep (size23 a + s) (Two a b) m sf

snocTree        :: FingerTree n a -> Tree23 n a -> FingerTree n a
snocTree Empty a        =  Single a
snocTree (Single a) b   =  deep (One a) Empty (One b)
snocTree (Deep s pr m (Four a b c d)) e = m `seq`
    Deep (s + size23 e) pr (m `snocTree` node3 a b c) (Two d e)
snocTree (Deep s pr m (Three a b c)) d =
    Deep (s + size23 d) pr m (Four a b c d)
snocTree (Deep s pr m (Two a b)) c =
    Deep (s + size23 c) pr m (Three a b c)
snocTree (Deep s pr m (One a)) b =
    Deep (s + size23 b) pr m (Two a b)

newtype Seq a = Seq (FingerTree Z a)

empty :: Seq a
empty = Seq Empty

instance Functor Seq where
  fmap f (Seq xs) = Seq (mapFT f xs)

instance Foldable Seq where
  foldMap f (Seq xs) = foldMapFT f xs
#if __GLASGOW_HASKELL__ >= 709
  length (Seq xs) = sizeFT xs
#endif

instance Traversable Seq where
  traverse f (Seq xs) = Seq <$> traverseFT f xs

(<|) :: a -> Seq a -> Seq a
a <| (Seq s) = Seq (Elem a `consTree` s)

(|>) :: Seq a -> a -> Seq a
(Seq s) |> a = Seq (s `snocTree` Elem a)

map23 :: (a -> b) -> Tree23 n a -> Tree23 n b
map23 f (Elem x) = Elem (f x)
map23 f (Node2 k a b) = Node2 k (map23 f a) (map23 f b)
map23 f (Node3 k a b c) = Node3 k (map23 f a) (map23 f b) (map23 f c)

foldMap23 :: Monoid m => (a -> m) -> Tree23 n a -> m
foldMap23 f (Elem x) = f x
foldMap23 f (Node2 _ x y) = foldMap23 f x <> foldMap23 f y
foldMap23 f (Node3 _ x y z) = foldMap23 f x <> (foldMap23 f y <> foldMap23 f z)

data Digit (n::Nat) a =  One (Tree23 n a)
                       | Two (Tree23 n a) (Tree23 n a)
                       | Three(Tree23 n a) (Tree23 n a) (Tree23 n a)
                       | Four (Tree23 n a) (Tree23 n a) (Tree23 n a) (Tree23 n a)

sizeDigit :: Digit n a -> Int
sizeDigit (One t) = size23 t
sizeDigit (Two t u) = size23 t + size23 u
sizeDigit (Three t u v) = size23 t + size23 u + size23 v
sizeDigit (Four t u v w) = size23 t + size23 u + size23 v + size23 w

mapDigit :: (a -> b) -> Digit n a -> Digit n b
mapDigit f (One x) = One (map23 f x)
mapDigit f (Two x y) = Two (map23 f x) (map23 f y)
mapDigit f (Three x y z) = Three (map23 f x) (map23 f y) (map23 f z)
mapDigit f (Four x y z w) = Four (map23 f x) (map23 f y) (map23 f z) (map23 f w)

foldMapDigit :: Monoid m => (a -> m) -> Digit n a -> m
foldMapDigit f (One x) = foldMap23 f x
foldMapDigit f (Two x y) = foldMap23 f x <> foldMap23 f y
foldMapDigit f (Three x y z) = foldMap23 f x <> (foldMap23 f y <> foldMap23 f z)
foldMapDigit f (Four x y z w) = foldMap23 f x <> (foldMap23 f y <> (foldMap23 f z <> foldMap23 f w))

traverseDigit :: Applicative f => (a -> f b) -> Digit n a -> f (Digit n b)
traverseDigit f (One a) = One <$> traverse23 f a
traverseDigit f (Two a b) = Two <$> traverse23 f a <*> traverse23 f b
traverseDigit f (Three a b c) = Three <$> traverse23 f a <*> traverse23 f b <*> traverse23 f c
traverseDigit f (Four a b c d) = Four <$> traverse23 f a <*> traverse23 f b <*> traverse23 f c <*> traverse23 f d

data FingerTree (n::Nat) a =  Empty
                            | Single (Tree23 n a)
                            | Deep {-# UNPACK #-} !Int (Digit n a) (FingerTree (S n) a) (Digit n a)

mapFT :: (a -> b) -> FingerTree n a -> FingerTree n b
mapFT _f Empty = Empty
mapFT f (Single t) = Single (map23 f t)
mapFT f (Deep n pr m sf) = Deep n (mapDigit f pr) (mapFT f m) (mapDigit f sf)

foldMapFT :: Monoid m => (a -> m) -> FingerTree n a -> m
foldMapFT _f Empty = mempty
foldMapFT f (Single t) = foldMap23 f t
foldMapFT f (Deep _ pr m sf) = foldMapDigit f pr <> (foldMapFT f m <> foldMapDigit f sf)

traverseFT :: Applicative f => (a -> f b) -> FingerTree n a -> f (FingerTree n b)
traverseFT _ Empty = pure Empty
traverseFT f (Single x) = Single <$> traverse23 f x
traverseFT f (Deep v pr m sf) =
    Deep v <$> traverseDigit f pr <*> traverseFT f m <*>
        traverseDigit f sf


sizeFT :: FingerTree n a -> Int
sizeFT Empty = 0
sizeFT (Single t) = size23 t
sizeFT (Deep n _ _ _) = n

deep :: Digit n a -> FingerTree (S n) a -> Digit n a -> FingerTree n a
deep pr m sf = Deep (sizeDigit pr + sizeFT m + sizeDigit sf) pr m sf

(><) :: Seq a -> Seq a -> Seq a
Seq xs >< Seq ys = Seq (appendTree0 xs ys)

data Place a = Place {-# UNPACK #-} !Int a

index :: Seq a -> Int -> a
Seq xs `index` i = lookupTree i xs

lookupTree :: Int -> FingerTree n a -> a
lookupTree _ Empty = error "lookupTree of empty tree"
lookupTree i (Single x) = lookup23 i x
lookupTree i (Deep totalSize pr m sf)
  | i < spr     =  lookupDigit i pr
  | i < spm     =  lookupTree (i - spr) m
  | otherwise   =  lookupDigit (i - spm) sf
  where
    spr     = sizeDigit pr
    spm     = totalSize - sizeDigit sf

lookupDigit :: Int -> Digit n a -> a
lookupDigit i (One x) = lookup23 i x
lookupDigit i (Two x y)
  | i < sx = lookup23 i x
  | otherwise = lookup23 (i - sx) y
  where sx = size23 x
lookupDigit i (Three x y z)
  | i < sx = lookup23 i x
  | i < sxy = lookup23 (i - sx) y
  | otherwise = lookup23 (i - sxy) z
  where sx = size23 x
        sxy = sx + size23 y
lookupDigit i (Four x y z w)
  | i < sx = lookup23 i x
  | i < sxy = lookup23 (i - sx) y
  | i < sxyz = lookup23 (i - sxy) z
  | otherwise = lookup23 (i - sxyz) z
  where sx = size23 x
        sxy = sx + size23 y
        sxyz = sxy + size23 z

lookup23 :: Int -> Tree23 n a -> a
lookup23 i (Elem a) = i `seq` a
lookup23 i (Node2 _ a b)
  | i < sa = lookup23 i a
  | otherwise = lookup23 (i - sa) b
  where sa = size23 a
lookup23 i (Node3 _ a b c)
  | i < sa = lookup23 i a
  | i < sab = lookup23 (i - sa) b
  | otherwise = lookup23 (i - sab) c
  where sa = size23 a
        sab = sa + size23 b

data Split t a = Split t a t

splitNode :: Int -> Tree23 (S n) a -> Split (Maybe (Digit n a)) (Tree23 n a)
splitNode (i::Int) (Node2 _ a b)
  | i < sa      = Split Nothing a (Just (One b))
  | otherwise   = Split (Just (One a)) b Nothing
  where
    sa      = size23 a
splitNode i (Node3 _ a b c)
  | i < sa      = Split Nothing a (Just (Two b c))
  | i < sab     = Split (Just (One a)) b (Just (One c))
  | otherwise   = Split (Just (Two a b)) c Nothing
  where
    sa      = size23 a
    sab     = sa + size23 b

splitDigit :: Int -> Digit n a -> Split (Maybe (Digit n a)) (Tree23 n a)
splitDigit i (One a) = i `seq` Split Nothing a Nothing
splitDigit i (Two a b)
  | i < sa      = Split Nothing a (Just (One b))
  | otherwise   = Split (Just (One a)) b Nothing
  where
    sa      = size23 a
splitDigit i (Three a b c)
  | i < sa      = Split Nothing a (Just (Two b c))
  | i < sab     = Split (Just (One a)) b (Just (One c))
  | otherwise   = Split (Just (Two a b)) c Nothing
  where
    sa      = size23 a
    sab     = sa + size23 b
splitDigit i (Four a b c d)
  | i < sa      = Split Nothing a (Just (Three b c d))
  | i < sab     = Split (Just (One a)) b (Just (Two c d))
  | i < sabc    = Split (Just (Two a b)) c (Just (One d))
  | otherwise   = Split (Just (Three a b c)) d Nothing
  where
    sa      = size23 a
    sab     = sa + size23 b
    sabc    = sab + size23 c

digitToTree     :: Digit n a -> FingerTree n a
digitToTree (One a) = Single a
digitToTree (Two a b) = deep (One a) Empty (One b)
digitToTree (Three a b c) = deep (Two a b) Empty (One c)
digitToTree (Four a b c d) = deep (Two a b) Empty (Two c d)

-- | Given the size of a digit and the digit itself, efficiently converts
-- it to a FingerTree.
digitToTree' :: Int -> Digit n a -> FingerTree n a
digitToTree' n (Four a b c d) = Deep n (Two a b) Empty (Two c d)
digitToTree' n (Three a b c) = Deep n (Two a b) Empty (One c)
digitToTree' n (Two a b) = Deep n (One a) Empty (One b)
digitToTree' n (One a) = n `seq` Single a

nodeToDigit :: Tree23 (S n) a -> Digit n a
nodeToDigit (Node2 _ a b) = Two a b
nodeToDigit (Node3 _ a b c) = Three a b c


data Maybe2 a b = Nothing2 | Just2 a b

-- | View of the left end of a sequence.
data ViewL a
    = EmptyL        -- ^ empty sequence
    | a :< Seq a    -- ^ leftmost element and the rest of the sequence
#if __GLASGOW_HASKELL__
--    deriving (Eq, Ord, Show, Read, Data)
#else
--    deriving (Eq, Ord, Show, Read)
#endif

-- | /O(1)/. Analyse the left end of a sequence.
viewl           ::  Seq a -> ViewL a
viewl (Seq xs)  =  case viewLTree xs of
    Nothing2 -> EmptyL
    Just2 (Elem x) xs' -> x :< Seq xs'

viewLTree       :: FingerTree n a -> Maybe2 (Tree23 n a) (FingerTree n a)
viewLTree Empty                 = Nothing2
viewLTree (Single a)            = Just2 a Empty
viewLTree (Deep s (One a) m sf) = Just2 a (pullL (s - size23 a) m sf)
viewLTree (Deep s (Two a b) m sf) =
    Just2 a (Deep (s - size23 a) (One b) m sf)
viewLTree (Deep s (Three a b c) m sf) =
    Just2 a (Deep (s - size23 a) (Two b c) m sf)
viewLTree (Deep s (Four a b c d) m sf) =
    Just2 a (Deep (s - size23 a) (Three b c d) m sf)

{-# INLINE pullL #-}
pullL :: Int -> FingerTree (S n) a -> Digit n a -> FingerTree n a
pullL s m sf = case viewLTree m of
    Nothing2        -> digitToTree' s sf
    Just2 pr m'     -> Deep s (nodeToDigit pr) m' sf

-- | View of the left end of a sequence.
data ViewR a
    = EmptyR        -- ^ empty sequence
    | Seq a :> a   -- ^ rightmost element and the rest of the sequence
#if __GLASGOW_HASKELL__
--    deriving (Eq, Ord, Show, Read, Data)
#else
--    deriving (Eq, Ord, Show, Read)
#endif

-- | /O(1)/. Analyse the right end of a sequence.
viewr           ::  Seq a -> ViewR a
viewr (Seq xs)  =  case viewRTree xs of
    Nothing2 -> EmptyR
    Just2 xs' (Elem x) -> Seq xs' :> x

viewRTree       :: FingerTree n a -> Maybe2 (FingerTree n a) (Tree23 n a)
viewRTree Empty                 = Nothing2
viewRTree (Single z)            = Just2 Empty z
viewRTree (Deep s pr m (One z)) = Just2 (pullR (s - size23 z) pr m) z
viewRTree (Deep s pr m (Two y z)) =
    Just2 (Deep (s - size23 z) pr m (One y)) z
viewRTree (Deep s pr m (Three x y z)) =
    Just2 (Deep (s - size23 z) pr m (Two x y)) z
viewRTree (Deep s pr m (Four w x y z)) =
    Just2 (Deep (s - size23 z) pr m (Three w x y)) z


{-# INLINE pullR #-}
pullR :: Int -> Digit n a -> FingerTree (S n) a -> FingerTree n a
pullR s pr m = case viewRTree m of
    Nothing2        -> digitToTree' s pr
    Just2 m' sf     -> Deep s pr m' (nodeToDigit sf)

deepL ::
    forall (n :: Nat) a.
    Maybe (Digit n a)
    -> FingerTree ('S n) a -> Digit n a -> FingerTree n a
deepL Nothing m sf      = pullL (sizeFT m + sizeDigit sf) m sf
deepL (Just pr) m sf    = deep pr m sf

deepR ::
    forall (n :: Nat) a.
    Digit n a
    -> FingerTree ('S n) a
    -> Maybe (Digit n a)
    -> FingerTree n a
deepR pr m Nothing      = pullR (sizeFT m + sizeDigit pr) pr m
deepR pr m (Just sf)    = deep pr m sf

splitTree :: Int -> FingerTree n a -> Split (FingerTree n a) (Tree23 n a)
splitTree _ Empty = error "splitTree of empty tree"
splitTree i (Single x) = i `seq` Split Empty x Empty
splitTree i (Deep _ pr m sf)
  | i < spr     = case splitDigit i pr of
            Split l x r -> Split (maybe Empty digitToTree l) x (deepL r m sf)
  | i < spm     = case splitTree im m of
            Split ml xs mr -> case splitNode (im - sizeFT ml) xs of
                Split l x r -> Split (deepR pr ml l) x (deepL r mr sf)
  | otherwise   = case splitDigit (i - spm) sf of
            Split l x r -> Split (deepR pr m l) x (maybe Empty digitToTree r)
  where
    spr     = sizeDigit pr
    spm     = spr + sizeFT m
    im      = i - spr

splitAt                 :: Int -> Seq a -> (Seq a, Seq a)
splitAt i (Seq xs)      = case split i xs of
                             (l, r) -> (Seq l, Seq r)

split :: Int -> FingerTree Z a ->
    (FingerTree Z a, FingerTree Z a)
split i Empty   = i `seq` (Empty, Empty)
split i xs
  | sizeFT xs > i = case splitTree i xs of
                      Split l x r -> (l, consTree x r)
  | otherwise   = (xs, Empty)

instance Monoid (Seq a) where
  mempty = empty
  mappend = (><)

appendTree0 :: FingerTree Z a -> FingerTree Z a -> FingerTree Z a
appendTree0 Empty xs =
    xs
appendTree0 xs Empty =
    xs
appendTree0 (Single x) xs =
    x `consTree` xs
appendTree0 xs (Single x) =
    xs `snocTree` x
appendTree0 (Deep s1 pr1 m1 sf1) (Deep s2 pr2 m2 sf2) =
    Deep (s1 + s2) pr1 (addDigits0 m1 sf1 pr2 m2) sf2

addDigits0 :: FingerTree (S Z) a -> Digit Z a -> Digit Z a -> FingerTree (S Z) a -> FingerTree (S Z) a
addDigits0 m1 (One a) (One b) m2 =
    appendTree1 m1 (node2 a b) m2
addDigits0 m1 (One a) (Two b c) m2 =
    appendTree1 m1 (node3 a b c) m2
addDigits0 m1 (One a) (Three b c d) m2 =
    appendTree2 m1 (node2 a b) (node2 c d) m2
addDigits0 m1 (One a) (Four b c d e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits0 m1 (Two a b) (One c) m2 =
    appendTree1 m1 (node3 a b c) m2
addDigits0 m1 (Two a b) (Two c d) m2 =
    appendTree2 m1 (node2 a b) (node2 c d) m2
addDigits0 m1 (Two a b) (Three c d e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits0 m1 (Two a b) (Four c d e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits0 m1 (Three a b c) (One d) m2 =
    appendTree2 m1 (node2 a b) (node2 c d) m2
addDigits0 m1 (Three a b c) (Two d e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits0 m1 (Three a b c) (Three d e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits0 m1 (Three a b c) (Four d e f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits0 m1 (Four a b c d) (One e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits0 m1 (Four a b c d) (Two e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits0 m1 (Four a b c d) (Three e f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits0 m1 (Four a b c d) (Four e f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2

appendTree1 :: FingerTree (S n) a -> Tree23 (S n) a -> FingerTree (S n) a -> FingerTree (S n) a
appendTree1 Empty a xs =
    a `consTree` xs
appendTree1 xs a Empty =
    xs `snocTree` a
appendTree1 (Single x) a xs =
    x `consTree` a `consTree` xs
appendTree1 xs a (Single x) =
    xs `snocTree` a `snocTree` x
appendTree1 (Deep s1 pr1 m1 sf1) a (Deep s2 pr2 m2 sf2) =
    Deep (s1 + size23 a + s2) pr1 (addDigits1 m1 sf1 a pr2 m2) sf2

addDigits1 ::
    forall (n :: Nat) a.
    FingerTree ('S (S n)) a
    -> Digit (S n) a
    -> Tree23 (S n) a
    -> Digit (S n) a
    -> FingerTree ('S (S n)) a
    -> FingerTree ('S (S n)) a
addDigits1 m1 (One a) b (One c) m2 =
    appendTree1 m1 (node3 a b c) m2
addDigits1 m1 (One a) b (Two c d) m2 =
    appendTree2 m1 (node2 a b) (node2 c d) m2
addDigits1 m1 (One a) b (Three c d e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits1 m1 (One a) b (Four c d e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits1 m1 (Two a b) c (One d) m2 =
    appendTree2 m1 (node2 a b) (node2 c d) m2
addDigits1 m1 (Two a b) c (Two d e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits1 m1 (Two a b) c (Three d e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits1 m1 (Two a b) c (Four d e f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits1 m1 (Three a b c) d (One e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits1 m1 (Three a b c) d (Two e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits1 m1 (Three a b c) d (Three e f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits1 m1 (Three a b c) d (Four e f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits1 m1 (Four a b c d) e (One f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits1 m1 (Four a b c d) e (Two f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits1 m1 (Four a b c d) e (Three f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits1 m1 (Four a b c d) e (Four f g h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2

appendTree2 ::
    forall (n :: Nat) a.
    FingerTree (S n) a
    -> Tree23 (S n) a -> Tree23 (S n) a -> FingerTree (S n) a -> FingerTree (S n) a
appendTree2 Empty a b xs =
    a `consTree` b `consTree` xs
appendTree2 xs a b Empty =
    xs `snocTree` a `snocTree` b
appendTree2 (Single x) a b xs =
    x `consTree` a `consTree` b `consTree` xs
appendTree2 xs a b (Single x) =
    xs `snocTree` a `snocTree` b `snocTree` x
appendTree2 (Deep s1 pr1 m1 sf1) a b (Deep s2 pr2 m2 sf2) =
    Deep (s1 + size23 a + size23 b + s2) pr1 (addDigits2 m1 sf1 a b pr2 m2) sf2

addDigits2 ::
    forall (n :: Nat) a.
    FingerTree ('S (S n)) a
    -> Digit (S n) a
    -> Tree23 (S n) a
    -> Tree23 (S n) a
    -> Digit (S n) a
    -> FingerTree ('S (S n)) a
    -> FingerTree ('S (S n)) a
addDigits2 m1 (One a) b c (One d) m2 =
    appendTree2 m1 (node2 a b) (node2 c d) m2
addDigits2 m1 (One a) b c (Two d e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits2 m1 (One a) b c (Three d e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits2 m1 (One a) b c (Four d e f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits2 m1 (Two a b) c d (One e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits2 m1 (Two a b) c d (Two e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits2 m1 (Two a b) c d (Three e f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits2 m1 (Two a b) c d (Four e f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits2 m1 (Three a b c) d e (One f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits2 m1 (Three a b c) d e (Two f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits2 m1 (Three a b c) d e (Three f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits2 m1 (Three a b c) d e (Four f g h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
addDigits2 m1 (Four a b c d) e f (One g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits2 m1 (Four a b c d) e f (Two g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits2 m1 (Four a b c d) e f (Three g h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
addDigits2 m1 (Four a b c d) e f (Four g h i j) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2

appendTree3 :: FingerTree (S n) a -> Tree23 (S n) a -> Tree23 (S n) a -> Tree23 (S n) a -> FingerTree (S n) a -> FingerTree (S n) a
appendTree3 Empty a b c xs =
    a `consTree` b `consTree` c `consTree` xs
appendTree3 xs a b c Empty =
    xs `snocTree` a `snocTree` b `snocTree` c
appendTree3 (Single x) a b c xs =
    x `consTree` a `consTree` b `consTree` c `consTree` xs
appendTree3 xs a b c (Single x) =
    xs `snocTree` a `snocTree` b `snocTree` c `snocTree` x
appendTree3 (Deep s1 pr1 m1 sf1) a b c (Deep s2 pr2 m2 sf2) =
    Deep (s1 + size23 a + size23 b + size23 c + s2) pr1 (addDigits3 m1 sf1 a b c pr2 m2) sf2


addDigits3 ::
    forall (n :: Nat) a.
    FingerTree ('S (S n)) a
    -> Digit (S n) a
    -> Tree23 (S n) a
    -> Tree23 (S n) a
    -> Tree23 (S n) a
    -> Digit (S n) a
    -> FingerTree ('S (S n)) a
    -> FingerTree ('S (S n)) a
addDigits3 m1 (One a) b c d (One e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits3 m1 (One a) b c d (Two e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits3 m1 (One a) b c d (Three e f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits3 m1 (One a) b c d (Four e f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits3 m1 (Two a b) c d e (One f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits3 m1 (Two a b) c d e (Two f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits3 m1 (Two a b) c d e (Three f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits3 m1 (Two a b) c d e (Four f g h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
addDigits3 m1 (Three a b c) d e f (One g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits3 m1 (Three a b c) d e f (Two g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits3 m1 (Three a b c) d e f (Three g h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
addDigits3 m1 (Three a b c) d e f (Four g h i j) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
addDigits3 m1 (Four a b c d) e f g (One h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits3 m1 (Four a b c d) e f g (Two h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
addDigits3 m1 (Four a b c d) e f g (Three h i j) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
addDigits3 m1 (Four a b c d) e f g (Four h i j k) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k) m2


appendTree4 :: FingerTree (S n) a -> Tree23 (S n) a -> Tree23 (S n) a -> Tree23 (S n) a -> Tree23 (S n) a -> FingerTree (S n) a -> FingerTree (S n) a
appendTree4 Empty a b c d xs =
    a `consTree` b `consTree` c `consTree` d `consTree` xs
appendTree4 xs a b c d Empty =
    xs `snocTree` a `snocTree` b `snocTree` c `snocTree` d
appendTree4 (Single x) a b c d xs =
    x `consTree` a `consTree` b `consTree` c `consTree` d `consTree` xs
appendTree4 xs a b c d (Single x) =
    xs `snocTree` a `snocTree` b `snocTree` c `snocTree` d `snocTree` x
appendTree4 (Deep s1 pr1 m1 sf1) a b c d (Deep s2 pr2 m2 sf2) =
    Deep (s1 + size23 a + size23 b + size23 c + size23 d + s2) pr1 (addDigits4 m1 sf1 a b c d pr2 m2) sf2



addDigits4 ::
    forall (n :: Nat) a.
    FingerTree ('S (S n)) a
    -> Digit (S n) a
    -> Tree23 (S n) a
    -> Tree23 (S n) a
    -> Tree23 (S n) a
    -> Tree23 (S n) a
    -> Digit (S n) a
    -> FingerTree ('S (S n)) a
    -> FingerTree ('S (S n)) a
addDigits4 m1 (One a) b c d e (One f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits4 m1 (One a) b c d e (Two f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits4 m1 (One a) b c d e (Three f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits4 m1 (One a) b c d e (Four f g h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
addDigits4 m1 (Two a b) c d e f (One g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits4 m1 (Two a b) c d e f (Two g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits4 m1 (Two a b) c d e f (Three g h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
addDigits4 m1 (Two a b) c d e f (Four g h i j) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
addDigits4 m1 (Three a b c) d e f g (One h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits4 m1 (Three a b c) d e f g (Two h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
addDigits4 m1 (Three a b c) d e f g (Three h i j) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
addDigits4 m1 (Three a b c) d e f g (Four h i j k) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k) m2
addDigits4 m1 (Four a b c d) e f g h (One i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
addDigits4 m1 (Four a b c d) e f g h (Two i j) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
addDigits4 m1 (Four a b c d) e f g h (Three i j k) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k) m2
addDigits4 m1 (Four a b c d) e f g h (Four i j k l) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node3 j k l) m2
