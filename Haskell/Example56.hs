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

{- 

In contrast with Example 5.6 from the paper, the index i in the log
prefix, which delivers M(B, pre i prefix_pe) = 1 is not 3, but
5. However, since the definition of M_k(o, P) accepts any index (which
is existentially quantified), the object B will still make it to the
result res56 of the expose_ck function, and, hence, will be exposed.

-}

pre3 = pre 5 prefix_pe

mp_b = m_plus al_final "B" pre3
-- 1

mm_b = m_minus al_final "B" pre3
-- 0

res56 = expose_ck al_final prefix_pe
-- ["B"]
-- Seems OK


