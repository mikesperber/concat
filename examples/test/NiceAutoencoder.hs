{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ViewPatterns        #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}

 
module Main where

import ConCat.Deep
import ConCat.Misc (R, Unop)
import ConCat.Additive (Additive)

import ConCat.Rebox ()

import Data.Vector.Sized (Vector(..))
import qualified Data.Vector.Sized as V
import Data.IndexedListLiterals (Only(..), IndexedListLiterals)
import Data.Key

import GHC.TypeLits (KnownNat)
import GHC.Natural
import GHC.Generics ((:.:)(..), (:*:)(..), U1, Par1(..))

import Data.Bifunctor(first, bimap)

import System.Random(Random,RandomGen,split,random, randomR, getStdGen, StdGen)

import Data.Constraint.Nat(Div)

import Prelude hiding (tanh, zipWith)

import Data.Key (Zip)

import Data.Maybe

import Data.Singletons
import Data.Singletons.TypeLits

input' = [ [81.368,-17.4,-16.5,7.019],
           [79.837,-17.4,-16.8,6.928],
           [86.927,-17.35,-16.9,6.9],
           [88.933,-17.3,-17.0,6.9] ]
{-# NOINLINE input' #-}

listLengthSing :: [a] -> SomeSing Nat
listLengthSing list = toSing (intToNatural (length list))
{-# NOINLINE listLengthSing #-}

toVectors :: KnownNat n => [[R]] -> [Vector n R]
toVectors lists = map (fromJust . V.fromList) lists

runNet :: KnownNat n => AutoencoderPars n -> [Vector n R] -> AutoencoderPars n
runNet rand inputs =
  let samples = map (\x -> (x, x)) inputs
  in last (trainNTimes 10 0.1 autoencoder rand samples)
{-# NOINLINE runNet #-}

main :: IO ()
main = do
  g <- getStdGen
  let s = listLengthSing (head input')
  case s of
    SomeSing (SNat :: Sing n) ->
      case toVectors @n input' of
        vecs ->
          print (runNet (fst (random g)) vecs)

type AutoencoderPars n = ((Vector (n `Div` 2) --+ Vector n)
                          :*: (Vector (n `Div` 2) --+ Vector (n `Div` 2))
                          :*: (Vector n --+ Vector (n `Div` 2))
                          :*: (Vector n --+ Vector n)
                         ) R

type Autoencoder n = AutoencoderPars n -> Vector n R -> Vector n R

autoencoder :: KnownNat n => Autoencoder n
autoencoder = affine @. affTanh @. affRelu @. affTanh
{-# INLINE autoencoder #-}

instance (KnownNat l, Random a) => Random (Vector l a) where
  randomR (v1, v2) = first (V.zipWith3 (((.).(.).(.)) fst (curry randomR)) v1 v2 . V.unfoldrN split) . split
  random = first (V.unfoldrN random) . split

instance Random (f (g p)) => Random ((f :.: g) p) where
  randomR (Comp1 l, Comp1 u) = first (Comp1 . fst . randomR (l, u)) . split
  random = first (Comp1 . fst . random) . split

instance Random a  => Random (Par1 a) where
  randomR (Par1 l, Par1 u) = first (Par1 . fst . randomR (l, u)) . split
  random = first (Par1 . fst . random) . split

instance (Random (f p), Random (g p)) => Random ((f :*: g) p) where
  randomR (l1 :*: l2, u1 :*: u2) (split -> first split -> ((g, g'), g''))
    = (fst (randomR (l1,u1) g) :*: fst (randomR (l2,u2) g'), g'')
  random (split -> first split -> ((g, g'), g'')) = (fst (random g) :*: fst (random g'), g'')

tanh' :: Floating a => a -> a
tanh' = \ x -> (exp (2*x) - 1) / (exp (2*x) + 1)
{-# INLINE tanh' #-}

tanh :: (Functor f, Floating a) => Unop (f a)
tanh = fmap tanh'
{-# INLINE tanh #-}

affTanh :: (Foldable a, Zip a, Functor b, Floating s, Additive s)
        => (a --+ b) s -> (a s -> b s)
affTanh = \ l -> tanh . (affine l)
{-# INLINE affTanh #-}
