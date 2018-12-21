{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveFunctor #-}

module Probability
  ( Distribution (unDistribution)
  , mkDistribution
  , simplify
  , uniform
  , bernoulli
  ) where

import Data.List (sortBy, groupBy)
import Data.Function (on)

type Probability = Rational
newtype Distribution a
  = Distribution { unDistribution :: [(a, Probability)] }
  deriving (Functor, Show)

cong :: ([(a, Probability)] -> [(b, Probability)]) -> Distribution a -> Distribution b
cong f = Distribution . f . unDistribution

valid :: Distribution a -> Bool
valid (Distribution l) = sum (snd <$> l) == 1

mkDistribution :: [(a, Probability)] -> Maybe (Distribution a)
mkDistribution l = if valid d then Just d else Nothing where
  d = Distribution l

simplify :: Ord a => Distribution a -> Distribution a
simplify = cong go where
  go = concatMap collapse . groupBy ((==) `on` fst) . sortBy (compare `on` fst)
  collapse [] = []
  collapse ((a, p) : l) = pure $ (a, p + sum (snd <$> l))

distort :: (Probability -> Probability) -> Distribution a -> Distribution a
distort f = cong $ fmap (fmap f)

instance Applicative Distribution where
  pure a = Distribution [(a, 1)]
  Distribution lf <*> Distribution lx = Distribution (combine <$> lf <*> lx) where
    combine (f, p) (x, p1) = (f x, p * p1)

join :: Distribution (Distribution a) -> Distribution a
join (Distribution l) = Distribution $ do
  (d, p) <- l
  unDistribution $ distort (p *) d

instance Monad Distribution where
  (>>=) = (join .) . flip fmap

uniform :: [a] -> Distribution a
uniform l = Distribution $ (, 1 / fromIntegral (length l)) <$> l

bernoulli :: Probability -> Maybe (Distribution Bool)
bernoulli p
  | 0 <= p && p <= 1 = Just $ Distribution [(True, p), (False, 1 - p)]
  | otherwise        = Nothing
