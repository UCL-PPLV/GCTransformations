{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NullaryTypeClasses #-}

module Example51 where

import Data.Map as M
import Data.Maybe as MB
import Data.List as L
import Control.Monad
import Data.Maybe
import GCDerivation
import Example23

{- Example 5.1 -}

-- Taking FL = empty in the wavefront dimension
instance WavefrontDimension where
    fl _ =  const False

-- remove the last entry
pref_51 = take 12 prefix_pe

-- wavefronts from the example
wf_51   = wavefront pref_51  
-- [("r1","f2"),("A","f1"),("r1","f3"),("A","f2"),("r1","f1")]
-- OK

wgt_51  = wgt al_final pref_51
-- [("r1","f1"),("r1","f2"),("r1","f3"),("A","f1"),("A","f2"),("A","f3")]
-- OK

wlt_51  = wlt al_final pref_51
-- [("r1","f2"),("r1","f3"),("r1","f1")]
-- OK
