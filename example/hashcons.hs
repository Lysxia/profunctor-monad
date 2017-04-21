{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DefaultSignatures #-}

import Control.Arrow (Kleisli (..))
import Control.Applicative
import Control.Monad.State hiding (lift)
import Data.Functor.Identity
import Data.Hashable (Hashable)
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as H
import GHC.Generics

import Profunctor.Monad hiding ((=.))
import Profunctor.Monad

-- * Hashconsing

-- | Hashes are just produced by counting.
newtype I = I Int
  deriving (Eq, Show, Hashable)

-- | Hashconsing monad transformer.
newtype HashConsingT t m a = HashConsingT (StateT (HashMap I t, HashMap t I) m a)
  deriving (Functor, Applicative, Monad, Alternative, MonadIO)

runHashConsingT :: HashConsingT t m a -> m (a, (HashMap I t, HashMap t I))
runHashConsingT (HashConsingT s) = runStateT s (H.empty, H.empty)

runHashConsing :: HashConsingT t Identity a -> (a, (HashMap I t, HashMap t I))
runHashConsing = runIdentity . runHashConsingT

cons :: (Eq t, Hashable t, Monad m) => t -> HashConsingT t m I
cons t = HashConsingT $ do
  (to, from) <- get
  case H.lookup t from of
    Just i -> pure i
    Nothing -> do
      let i = I (H.size to)
      put (H.insert i t to, H.insert t i from)
      pure i

uncons :: Monad m => I -> HashConsingT t m t
uncons i = HashConsingT $ do
  (to, _) <- get
  case H.lookup i to of
    Just t -> pure t
    Nothing -> fail "Non-existingT key"

-- * Binary tree

data TreeF a = Leaf | Node a a
  deriving (Eq, Show, Generic)

instance Hashable a => Hashable (TreeF a)

newtype Tree = Tree (TreeF Tree)
  deriving (Eq, Show)

pattern L :: Tree
pattern L = Tree Leaf

pattern N :: Tree -> Tree -> Tree
pattern N l r = Tree (Node l r)

type TreeI = TreeF I

type HCTreeT = HashConsingT TreeI

leaf :: Monad m => HCTreeT m I
leaf = cons Leaf

node :: Monad m => I -> I -> HCTreeT m I
node i j = cons (Node i j)

hashConsTree :: Monad m => Tree -> HCTreeT m I
hashConsTree L = leaf
hashConsTree (N l r) = do
  i <- hashConsTree l
  j <- hashConsTree r
  node i j

size :: Tree -> Int
size t =
  let (_, (h, _)) = runHashConsing (hashConsTree t)
  in H.size h

fibTree :: Int -> Tree
fibTree 0 = L
fibTree 1 = L
fibTree n = N (fibTree (n - 1)) (fibTree (n - 2))

-- * Parser/Printer

newtype ParserT m x a = ParserT (String -> m (String, a))

runParserT :: (Monad m, Alternative m) => ParserT m x a -> String -> m a
runParserT (ParserT p) s = do
  (left, a) <- p s
  case left of
    "" -> pure a
    _ -> empty

newtype PrinterT m x a = PrinterT (x -> m (String, a))

runPrinterT :: Functor m => PrinterT m x a -> x -> m String
runPrinterT (PrinterT q) x = fst <$> q x

class PMonadTrans t where
  lift :: Monad m => m a -> t m x a

instance PMonadTrans ParserT where
  lift ma = ParserT $ \s -> (,) s <$> ma

instance PMonadTrans PrinterT where
  lift ma = PrinterT $ \_ -> (,) "" <$> ma

instance Monad m => Cofunctor (ParserT m) where
  type First (ParserT m) = Kleisli m
  lmap _ (ParserT p) = ParserT p

instance Monad m => Cofunctor (PrinterT m) where
  type First (PrinterT m) = Kleisli m
  lmap (Kleisli f) (PrinterT q) = PrinterT (f >=> q)

-- Might also use a @'Functor1' p@ constraint,
-- but that would require @UndecidableInstances@.
class Cofunctor p => IParser p where
  anyChar :: p Char Char

  char :: forall x. Char -> p x ()

instance (Monad m, Alternative m) => IParser (ParserT m) where
  anyChar = ParserT $ \s ->
    case s of
      "" -> empty
      c : s' -> pure (s', c)

  char c = ParserT $ \s ->
    case s of
      c' : s' | c == c' -> pure (s', ())
      _ -> empty

instance Monad m => IParser (PrinterT m) where
  anyChar = PrinterT $ \c -> pure ([c], c)

  char c = PrinterT $ \_ -> pure ([c], ())

-- | A type synonym to clean up types.
type P p a = p a a

-- | Fixed underlying monad to make things simpler.
type M = HCTreeT IO

-- | Parser/printer of hashconsed trees.
--
-- A tree is represented by this grammar (prefix notation):
--
-- > <tree> ::=
-- >   '0'               -- Leaf
-- >   '1' <tree> <tree> -- Node
--
-- Monadic implementation.
ppTree
  :: forall p
  .  (Monad1 (p M), IParser (p M), First (p M) ~ Kleisli M, PMonadTrans p)
  => P (p M) I
ppTree = with @Monad @(p M) @TreeI $ uncons =: do
  c0 <- firstChar =. anyChar
  case c0 of
    '0' -> lift leaf
    '1' -> do
      i <- c1 =. ppTree
      j <- c2 =. ppTree
      lift (node i j)
    _ -> fail "Invalid character"
  where
    firstChar Leaf = '0'
    firstChar (Node _ _) = '1'
    c1 (Node i _) = i
    c2 (Node _ j) = j

-- | Parser/printer of hashconsed trees.
-- Should be mostly equivalent to @'ppTree'@.
--
-- Applicative/alternative implementation, mostly.
ppTree2
  :: forall p
  .  ( Alternative1 (p M), Monad1 (p M), PMonadTrans p
     , IParser (p M), First (p M) ~ Kleisli M)
  => P (p M) I
ppTree2 =
  with @Alternative @(p M) @TreeI $
     uncons =:
       (   (guard . isLeaf) =: char '0' *> lift leaf
       <|> (guard . isNode) =: char '1' *> ppNode'
       )
  where
    ppNode' = with @Monad @(p M) @TreeI $ do
      i <- c1 =. ppTree2
      j <- c2 =. ppTree2
      lift (node i j)

    c1 (Node i _) = i
    c2 (Node _ j) = j

isLeaf, isNode :: TreeF a -> Bool

isLeaf Leaf = True
isLeaf _ = False

isNode (Node _ _) = True
isNode _ = False

-- * Main

main :: IO ()
main = do
  let t = fibTree 7
  (s, _) <- runHashConsingT $ do
    putStrLn' $ "Size: " ++ show (size t)
    putStrLn' "First printer"
    i <- hashConsTree t
    s <- runPrinterT ppTree i
    putStrLn' s
    putStrLn' "First parser"
    i' <- runParserT ppTree s
    assertEqual i i'
    pure s
  -- Reset hashcons state.
  void $ runHashConsingT $ do
    putStrLn' "Second parser"
    i'' <- runParserT ppTree2 s
    putStrLn' "Second printer"
    s' <- runPrinterT ppTree2 i''
    assertEqual s s'
    i <- hashConsTree t
    assertEqual i i''

putStrLn' :: MonadIO m => String -> m ()
putStrLn' = liftIO . putStrLn

assertEqual
  :: (MonadIO m, Alternative m, Eq a, Show a) => a -> a -> m ()
assertEqual a b = when (a /= b) $ do
  liftIO $ do
    print a
    print b
  empty

-- * Functor/Applicative/Monad/Alternative

instance Monad m => Functor (ParserT m x) where fmap = liftA

instance Monad m => Applicative (ParserT m x) where
  pure a = ParserT (\s -> pure (s, a))
  (<*>) = ap

instance Monad m => Monad (ParserT m x) where
  ParserT p >>= f = ParserT $ \s -> do
    (s', a) <- p s
    let ParserT p' = f a
    p' s'

instance (Monad m, Alternative m) => Alternative (ParserT m x) where
  empty = ParserT $ \_ -> empty
  ParserT q <|> ParserT q' = ParserT (\s -> q s <|> q' s)

instance Monad m => Functor (PrinterT m x) where fmap = liftA

instance Monad m => Applicative (PrinterT m x) where
  pure a = PrinterT (\_ -> pure ("", a))
  (<*>) = ap

instance Monad m => Monad (PrinterT m x) where
  PrinterT q >>= f = PrinterT $ \x -> do
    (s, a) <- q x
    let PrinterT q' = f a
    (s', b) <- q' x
    pure (s ++ s', b)

instance (Monad m, Alternative m) => Alternative (PrinterT m x) where
  empty = PrinterT $ \_ -> empty
  PrinterT q <|> PrinterT q' = PrinterT (\x -> q x <|> q' x)
