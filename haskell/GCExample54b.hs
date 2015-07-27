{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NullaryTypeClasses #-}

module GCExample54 where

import Data.Map as M
import Data.Maybe as MB
import Data.List as L
import Control.Monad
import Data.Maybe
import GCDerivation
import GCExample23

{- Example 5.4, part 2 -}

instance WavefrontDimension where
  fl _ o =  not (o == "r1")

instance PolicyDimension where
  lr _ = const True

instance ProtectionDimension where
  is = const True

pref_54 = take 12 prefix_pe
wgt_54  = wgt al_final pref_54
wlt_54  = wlt al_final pref_54

mp_e = m_plus al_final "E" prefix_pe
-- 1

mm_e = m_minus al_final "E" prefix_pe
-- 0

ex_res_54 = expose_c al_final prefix_pe
-- ["B","E"] -- OK

