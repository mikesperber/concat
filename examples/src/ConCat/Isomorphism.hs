{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -Wall #-}

-- | Category of Isomorphisms.

module ConCat.Isomorphism where

import Prelude hiding (id, (.), const)  -- Coming from ConCat.AltCat.

import ConCat.Misc ((:*))
import ConCat.AltCat
import qualified ConCat.Category
import ConCat.Rep

infix 0 :<->
data Iso k a b = (a `k` b) :<-> (b `k` a)

-- Helpful?
instance HasRep (Iso k a b) where
  type Rep (Iso k a b) = (a `k` b) :* (b `k` a)
  abst (f,f') = f :<-> f'
  repr (f :<-> f') = (f,f')

inverse :: Iso k a b -> Iso k b a
inverse (f :<-> f') = f' :<-> f
{-# INLINE inverse #-}

instance Category k => Category (Iso k) where
  type Ok (Iso k) = Ok k
  id = id :<-> id
  (g :<-> g') . (f :<-> f') = (g . f) :<-> (f' . g')
  {- INLINE id #-}
  {- INLINE (.) #-}

instance AssociativePCat k => AssociativePCat (Iso k) where
  lassocP = lassocP :<-> rassocP
  rassocP = rassocP :<-> lassocP
  {- INLINE lassocP #-}
  {- INLINE rassocP #-}

instance MonoidalPCat k => MonoidalPCat (Iso k) where
  (f :<-> f') *** (g :<-> g') = (f *** g) :<-> (f' *** g')
  {- INLINE (***) #-}

instance BraidedPCat k => BraidedPCat (Iso k) where
  swapP = swapP :<-> swapP
  {-# INLINE swapP #-}

instance AssociativeSCat k => AssociativeSCat (Iso k) where
  lassocS = lassocS :<-> rassocS
  rassocS = rassocS :<-> lassocS
  {- INLINE lassocS #-}
  {- INLINE rassocS #-}

instance MonoidalSCat k => MonoidalSCat (Iso k) where
  (f :<-> f') +++ (g :<-> g') = (f +++ g) :<-> (f' +++ g')
  {- INLINE (+++) #-}

instance BraidedSCat k => BraidedSCat (Iso k) where
  swapS = swapS :<-> swapS
  {-# INLINE swapS #-}

instance UnitCat k => UnitCat (Iso k) where
  lunit   = lunit   :<-> lcounit
  runit   = runit   :<-> rcounit
  lcounit = lcounit :<-> lunit
  rcounit = rcounit :<-> runit
  {-# INLINE lunit #-}
  {-# INLINE runit #-}
  {-# INLINE lcounit #-}
  {-# INLINE rcounit #-}

isoFwd :: Iso k a b -> (a `k` b)
isoFwd (f :<-> _) = f

isoRev :: Iso k a b -> (b `k` a)
isoRev (_ :<-> f') = f'

infix 0 <->
type (<->) = Iso (->)

-- Old notation
pattern Iso :: (a `k` b) -> (b `k` a) -> Iso k a b
pattern Iso f f' = f :<-> f'
