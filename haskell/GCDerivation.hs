{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NullaryTypeClasses #-}

module GCDerivation where

import Data.Map as M
import Data.List as L
import Control.Monad
import Data.Maybe

{-----------------------------------------------------------------}
{--                   Basic definitions                         --}
{-----------------------------------------------------------------}

type FName = String
type ObjId = String
type k :-> v = M.Map k v

-- An object is represented by its id (Int) and a list of objects ids,
-- to which it points with its fields (String :-> Int)
data Object = O {
  objid :: ObjId,
  fields :: FName :-> (Maybe ObjId)
} deriving (Eq, Ord, Show)

type ObjectOrNull = Maybe Object
type Ref = Maybe ObjId
type AL = [Object]

-- Mapping fields to allocated values
-- The parameter AL is always passed as list 
h :: AL -> Object -> FName -> ObjectOrNull
h als o fname = do
  -- Find the object ID or Nothinr
  fObjId <- join $ M.lookup fname $ fields o
  -- Find the object
  L.find (\ob -> objid ob == fObjId) als

-- An alias
obj_f = h
pre k = take k

data ActionKind = T | M | A deriving (Eq, Ord, Show)
data LogEntry = LE {
  kind   :: ActionKind,
  source  :: Object,
  field   :: FName,
  old     :: Ref,
  new     :: Ref
} deriving (Eq, Ord, Show)
  
type Log = [LogEntry]

fields' = toList . fields

-- Definition of the wavefront
wavefront :: Log -> [(Object, FName)]
wavefront p = [(source pi, field pi) | pi <- p, kind pi == T]

-- Definition of behind/ahead
behind p (o, f) = elem (o, f) $ wavefront p
ahead p = not . (behind p)

-- The initial expose_apex function
-- for giving the reachable object

{-----------------------------------------------------------------}
{--     The initial expose function of the apex algorithm       --}
{-----------------------------------------------------------------}

expose_apex :: AL -> [LogEntry] -> [ObjectOrNull]
expose_apex als p = nub $ [obj_f als o f |
  i <- [0 .. length p - 1],
  let pi = p !! i
      o = source pi
      f = field pi
      prepi = pre i p,
  elem (kind pi) [M, A],
  elem (o, f) $ wavefront prepi]

{-----------------------------------------------------------------}
{-- Implementing different partitions over the precision axes   --}
{-----------------------------------------------------------------}

-- So far, we are representing partitions via boolean selector functions

{------=-------------------------}
{- 5.1: The Wavefront Dimension -}
{-------=------------------------}

class WavefrontDimension where
  fl, ol :: Object -> Bool
  fl = not . ol
  ol = not . fl

-- All fields of all objects ever
all_fields :: [Object] -> [FName]
all_fields als = [fname | o <- als, fname <- keys $ fields o]

{- two views to the wavefront -}
wgt, wlt :: WavefrontDimension => [Object] -> Log -> [(Object, FName)]

{- 

The second component of the concatenation iterates over all available
fields f' of the allocated objects and all objects o in the
wavefront, pairing them and returning the combinations.

-}

wgt als p =
  let wf = wavefront p in
  nub $ [(o, f) | (o, f) <- wf, fl o] ++
        [(o, f) | (o, _) <- wf, f <- all_fields als, ol o]

{- 

Check, whether the following reading of the quantifiers is accurate:
essentially, the second component of the concatenation iterates over
all available fields f' of the allocated objects and all objects o in
the wavefront. It then checks whether the pair (o, f') belongs to the
wavefront wf, and in this case returns pairing of this object with all
possible fields.

-}

wlt als p =
  let wf = wavefront p
      fs = all_fields als in
  nub $ [(o, f) | (o, f) <- wf, fl o] ++
        [(o, f) | f' <- fs, (o, _) <- wf, elem (o, f') wf, f <- fs, ol o]

-- instance WavefrontDimension where
--    ol =  const True

{-----------------------------------------------------}
{-   5.2, 5.4: The Policy and Protection Dimensions  -}
{-----------------------------------------------------}

class PolicyDimension where
  sr, lr :: Object -> Bool
  sr = not . lr
  lr = not . sr

class ProtectionDimension where
  is, ds :: ObjectOrNull -> Bool
  is o = (not $ isNothing o) && (not $ ds o)
  ds o = (not $ isNothing o) && (not $ is o)

deref :: [Object] -> Ref -> ObjectOrNull
deref als ref = do
  r <- ref
  L.find (\o -> objid o == r) als

-- expose_r from Section 5.2.1
expose_r :: (WavefrontDimension, ProtectionDimension, PolicyDimension) =>
         AL -> [LogEntry] -> [ObjectOrNull]
expose_r als p = nub $ [obj_f als o f |
  i <- [0 .. length p - 1],
  let pi = p !! i
      o = source pi
      f = field pi
      prepi = pre i p,
  elem (kind pi) [M, A],
  elem (o, f) $ wgt als prepi,
  sr o,
  is $ deref als $ new pi,
  is $ obj_f als o f]

-- 5.2.2: Cross-wavefront counts
