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

{- Example 5.1 -}

-- Taking FL = empty in the wavefront dimension
instance WavefrontDimension where
    fl _ =  const False

-- remove the last entry
pref_51 = take 12 prefix_pe

-- wavefronts from the example
wf_51   = wavefront pref_51    -- OK

wgt_51  = wgt al_final pref_51 -- OK
wlt_51  = wlt al_final pref_51 -- OK

