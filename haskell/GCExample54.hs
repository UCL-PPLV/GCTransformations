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

{- Example 5.4 -}

-- taking a specific policy dimension
instance WavefrontDimension where
    fl _ =  const True

instance PolicyDimension where
  lr _ = const True

instance ProtectionDimension where
  is = const True

-- TODO: BUG!
ex_res_54 = expose_c al_final prefix_pe

