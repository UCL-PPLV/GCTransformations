{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NullaryTypeClasses #-}

module GCExample51 where

import Data.Map as M
import Data.Maybe as MB
import Data.List as L
import Control.Monad
import Data.Maybe
import GCDerivation
import GCExample23

{- Example 5.3 -}

-- taking a specific policy dimension
instance PolicyDimension where
  lr _ id = id == "A"

