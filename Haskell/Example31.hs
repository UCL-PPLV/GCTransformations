{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NullaryTypeClasses #-}

module Example31 where

import Data.Map as M
import Data.Maybe as MB
import Data.List as L
import Control.Monad
import Data.Maybe
import GCDerivation
import Example23


{- Example 3.1 -}

ex_apex_res :: [ObjId]
ex_apex_res = expose_apex al_final prefix_pe 
-- ["E"]
-- OK

