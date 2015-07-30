{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NullaryTypeClasses #-}

module Example56 where

import Data.Map as M
import Data.Maybe as MB
import Data.List as L
import Control.Monad
import Data.Maybe
import GCDerivation
import Example23

{- Example 5.6 -}

instance WavefrontDimension where
  fl _ o = True

instance PolicyDimension where
  lr _ o = o /= "r1"

instance ProtectionDimension where
  is = const True

instance ThresholdDimension where
  dk = Ind 1

pref3 = pre 3 prefix_pe

mp_b = m_plus al_final "B" pref3
-- 0

mm_b = m_minus al_final "B" pref3
-- 0

res56 = expose_ck al_final prefix_pe
-- ["A","B","E"]
