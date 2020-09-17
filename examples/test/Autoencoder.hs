{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ViewPatterns        #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}

{-
{-# OPTIONS_GHC -fplugin-opt=ConCat.Plugin:trace #-}
{-# OPTIONS_GHC -fplugin-opt=ConCat.Plugin:showResiduals #-}
{-# OPTIONS_GHC -fplugin-opt=ConCat.Plugin:showCcc #-}


{-# LANGUAGE CPP #-}
-- #include "ConCat/Ops.inc"

-}
module Main where

import ConCat.Deep
import ConCat.Misc(R, Unop)
import ConCat.Additive(Additive, sumA)

import ConCat.AltCat (joinPF, scale)
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
import qualified Prelude as P

import Data.Key (Zip)

import Control.Monad (forM_)

import Data.Singletons
import Data.Singletons.TypeLits

import Text.Read(readMaybe)

import qualified Data.Csv as Csv
import qualified Data.ByteString.Lazy as BL
import qualified Data.Vector as Vec

import qualified Data.Csv as Csv

import Debug.Trace (traceShowId)

{-# NOINLINE readCsv #-}
readCsv :: FilePath -> IO (SomeSing Nat, [[Double]])
readCsv path = do
  csvData <- BL.readFile path
  case (Csv.decode Csv.HasHeader csvData :: Either String (Vec.Vector [Double])) of
    Left err -> do
      putStrLn err
      error "geht nicht"
    Right v -> do
      let i = length (Vec.head v)
      let s = toSing (intToNatural i)
      return (s, Vec.toList v)

{-# NOINLINE foo #-}
foo :: KnownNat n => [[Double]] -> Maybe [V.Vector n R]
foo vss =
  mapM V.fromList (take 4 vss)

main :: IO ()
main = do
  g <- getStdGen
  let runNet :: KnownNat n => [Vector n R] -> [String]
      runNet inputs =
        let samples = map (\x -> (x, x)) inputs
            rand = traceShowId $ fst (random g)
            trainedParameters = last $ trainNTimes 10 0.1 autoencoder rand samples
        in flip concatMap inputs  $ \input ->
           ["input: " ++ show input
           ++ "output: " ++  show (autoencoder trainedParameters input)]
  (s, vs) <- readCsv "all_cool_energies_no_ts.csv"
  case s of
    SomeSing (SNat :: Sing n) ->
      case foo @n vs of
        Nothing ->
          putStrLn "HELP"
        Just vecs ->
          print (head (runNet vecs))
  -- x :: Maybe (Vec.Vector [Double]) <- readCsv "all_cool_energies_no_ts.csv"
  -- case x of
  --   Nothing -> putStrLn "got nothing"
  --   Just v -> do

  {-

type AutoencoderPars n = ((Vector (n `Div` 2) --+ Vector n)
--                          :*: (Vector (n `Div` 2) --+ Vector (n `Div` 2))
                          :*: (Vector n --+ Vector (n `Div` 2))
--                          :*: (Vector n --+ Vector n)
                         ) R

-}

type AutoencoderPars n = (Vector n --+ Vector n) R

type Autoencoder n = AutoencoderPars n -> Vector n R -> Vector n R

autoencoder :: KnownNat n => Autoencoder n
--autoencoder = affineV2 @. affTanhV @. affReluV @. affTanhV
--autoencoder = affine @. affTanh @. affRelu @. affTanh
--autoencoder = affTanh @. affRelu
autoencoder = affTanh
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
