{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NullaryTypeClasses #-}

module Example58 where

import Data.Map as M
import Data.Maybe as MB
import Data.List as L
import Control.Monad
import Data.Maybe
import GCDerivation
import Example23

{- Example 5.8 -}

instance WavefrontDimension where
  fl _ = const True

instance PolicyDimension where
  lr _ = const True

instance ProtectionDimension where
  ds = const True

instance ThresholdDimension where
  dk = Inf

res58a = expose_d al_final prefix_pe
-- ["C","B","D"]
-- OK

res58b = expose_rcd al_final prefix_pe
-- ["C","B","D"]
-- OK (?)
