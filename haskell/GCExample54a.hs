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

{- Example 5.4, part 1 -}

instance WavefrontDimension where
  fl _ o = True

instance PolicyDimension where
  lr _ = const True

instance ProtectionDimension where
  is = const True

pref_54 = take 12 prefix_pe
wgt_54  = wgt al_final pref_54
wlt_54  = wlt al_final pref_54

-- [BUG] the result is different in this case
mp_e = m_plus al_final "E" prefix_pe
-- 1

mm_e = m_minus al_final "E" prefix_pe
-- 1

-- BUG: the difference b/w mp_e and mm_e should be > 0
-- Check the parameters of m_plus and m_minus
ex_res_54 = expose_c al_final prefix_pe

