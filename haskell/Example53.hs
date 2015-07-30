{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NullaryTypeClasses #-}

module GCExample53 where

import Data.Map as M
import Data.Maybe as MB
import Data.List as L
import Control.Monad
import Data.Maybe
import GCDerivation
import GCExample23

{- Example 5.3 -}

-- taking a specific policy dimension
instance WavefrontDimension where
    fl _ =  const True

instance PolicyDimension where
  lr _ id = id == "A"

m_53 = m al_final (Just "b") prefix_pe

-- also try 
mp_53 = m_plus al_final b prefix_pe
mm_53 = m_plus al_final b prefix_pe