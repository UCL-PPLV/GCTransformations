{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NullaryTypeClasses #-}

module GCDerivation where

import Data.Map as M
import Data.Maybe as MB
import Data.List as L
import Control.Monad

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
h :: AL -> ObjId -> FName -> ObjectOrNull
h als oid fname = do
  -- Find the object by id "oid"
  o <- L.find (\ob -> objid ob == oid) als 
  -- Find the object ID or Nothing for the field name "fname"
  fObjId <- join $ M.lookup fname $ fields o
  -- Find the object for the id "fObjId"
  L.find (\ob -> objid ob == fObjId) als

-- An alias
obj_f = h
pre k = take k

data ActionKind = T | M | A deriving (Eq, Ord, Show)
data LogEntry = LE {
  kind    :: ActionKind,
  source  :: ObjId,
  field   :: FName,
  old     :: Ref,
  new     :: Ref
} deriving (Eq, Ord, Show)
  
type Log = [LogEntry]

fields' = toList . fields

-- Definition of the wavefront
wavefront :: Log -> [(ObjId, FName)]
wavefront p = [(source pi, field pi) | pi <- p, kind pi == T]

-- Definition of behind/ahead
behind p (o, f) = elem (o, f) $ wavefront p
ahead p = not . (behind p)

-- util function for mapping a list of Maybe-objects to their IDs
ids :: [ObjectOrNull] -> [ObjId]
ids ons = [objid o | Just o <- ons]

{-----------------------------------------------------------------}
{--     The initial expose function of the apex algorithm       --}
{-----------------------------------------------------------------}

-- The initial expose_apex function
-- for giving the reachable object

expose_apex :: AL -> [LogEntry] -> [ObjId]
expose_apex als p = ids $ nub $ 
 [obj_f als o f |
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

{--------------------------------}
{- 5.1: The Wavefront Dimension -}
{--------------------------------}

class WavefrontDimension where
  fl, ol :: [Object] -> ObjId -> Bool
  fl als = not . (ol als)
  ol als = not . (fl als)

-- All fields of all objects ever
all_fields :: [Object] -> [FName]
all_fields als = [fname | o <- als, fname <- keys $ fields o]

{- two views to the wavefront -}
wgt, wlt :: WavefrontDimension => [Object] -> Log -> [(ObjId, FName)]

{- 

The second component of the concatenation iterates over all available
fields f' of the allocated objects and all objects o in the
wavefront, pairing them and returning the combinations.

-}

-- util function for getting all fields of an object by id
obj_fields :: [Object] -> ObjId -> [FName]
obj_fields als id = 
 let tmp = do o <- L.find (\ob -> objid ob == id) als
              return $ keys $ fields o
 in case tmp of Just fs -> fs; _ -> []
           

wgt als p =
  let wf = wavefront p in
  nub $ [(o, f) | (o, f) <- wf, fl als o] 
        ++
        [(o, f) | (o, f') <- wf, -- *some* o's field is in wf
                  f <- obj_fields als o, 
                  ol als o]

{- 

Check, whether the following reading of the quantifiers is accurate:
essentially, the second component of the concatenation iterates over
all available fields f' of the allocated objects and all objects o in
the wavefront. It then checks whether the pair (o, f') belongs to the
wavefront wf, and in this case returns pairing of this object with all
possible fields.

-}

all_fields_in_wf als o wf = 
  let ofs = obj_fields als o
      wfs = [f | (o', f) <- wf, o' == o]   
  in  (sort ofs) == (sort wfs)

wlt als p =
  let wf = wavefront p
      fs = all_fields als in
  nub $ [(o, f) | (o, f)  <- wf, fl als o] ++
        [(o, f) | (o, f) <- wf, 
                  -- *all* o's fields are in the wf                  
                  all_fields_in_wf als o wf,
                  elem f $ obj_fields als o,
                  ol als o]

-- {-----------------------------------------------------}
-- {-   5.2, 5.4: The Policy and Protection Dimensions  -}
-- {-----------------------------------------------------}

class PolicyDimension where
  sr, lr :: [Object] -> ObjId -> Bool
  sr als = not . (lr als)
  lr als = not . (sr als)

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
         AL -> [LogEntry] -> [ObjId]
expose_r als p = ids $ nub $ [obj_f als o f |
  i <- [0 .. length p - 1],
  let pi = p !! i
      o = source pi
      f = field pi
      prepi = pre i p,
  elem (kind pi) [M, A],
  elem (o, f) $ wgt als prepi,
  sr als o,
  is $ deref als $ new pi,
  is $ obj_f als o f]

-- 5.2.2: Cross-wavefront counts

m_plus, m_minus :: (WavefrontDimension, PolicyDimension) =>
                   AL -> ObjId -> Log -> Int

m_plus als o p = length $ [pi |
  i <- [0 .. length p - 1],
  let pi = p !! i
      prepi = pre i p,
  elem (kind pi) [M, A],
  new pi == Just o,
  elem (source pi, field pi) $ wgt als prepi,
  lr als $ source pi]

m_minus als o p = length $ [pi |
  i <- [0 .. length p - 1],
  let pi = p !! i
      prepi = pre i p,
  elem (kind pi) [M, A],
  new pi == Just o,
  elem (source pi, field pi) $ wlt als prepi,
  lr als $ source pi]

m :: (WavefrontDimension, PolicyDimension) =>
     AL -> Ref -> Log -> Int
m als ref p = 
 case ref of
  Just o -> m_plus als o p - m_minus als o p
  Nothing -> 0

maybeId :: ObjectOrNull -> Ref
maybeId on = do
  o <- on
  return $ objid o

-- Collection by counting
expose_c :: (WavefrontDimension, ProtectionDimension, PolicyDimension) =>
         AL -> [LogEntry] -> [ObjId]
expose_c als p = ids $ nub $ [n |
  i <- [0 .. length p - 1],
  let pi = p !! i
      n  = deref als $ new pi,
  m als (maybeId n) p > 0, is n]

expose_rc :: (WavefrontDimension, ProtectionDimension, PolicyDimension) =>
         AL -> [LogEntry] -> [ObjId]
expose_rc als p = nub $ expose_r als p ++ expose_c als p


{-----------------------------------------------------}
{-            5.3: The Threshold Dimensions          -}
{-----------------------------------------------------}

data I = Inf | Ind Int deriving (Eq, Ord, Show)

-- This is relevant for the mutator, not the collector
class ThresholdDimension where
  dk :: I

gt :: I -> I -> Bool
gt x y = case (x, y) of 
   (Inf, _) -> True
   (Ind n, Ind m) -> n >= m
   _ -> False

-- Definition of M_k(o, P)
mk :: (WavefrontDimension, PolicyDimension, ThresholdDimension) =>
     AL -> Ref -> Log -> I
mk als ref p = 
  let ms = [m als ref p | 
       i <- [0 .. length p - 1],
       let prepi = pre i p,
       (Ind $ m als ref prepi) `gt` dk]
  in  if L.null ms 
      then Ind $ m als ref p
      else Inf   

-- Collection by counting with arbitrary dimension
expose_ck :: (WavefrontDimension, ProtectionDimension, 
              PolicyDimension, ThresholdDimension) =>
         AL -> [LogEntry] -> [ObjId]
expose_ck als p = ids $ nub $ [n |
  i <- [0 .. length p - 1],
  let pi = p !! i
      n  = deref als $ new pi,
  mk als (maybeId n) p `gt` (Ind 0), is n]

expose_rck :: (WavefrontDimension, ProtectionDimension, 
              PolicyDimension, ThresholdDimension) =>
          AL -> [LogEntry] -> [ObjId]
expose_rck als p = nub $ expose_ck als p ++ expose_ck als p

{-----------------------------------------------------}
{-        5.4: Protection Dimension (contd.)         -}
{-----------------------------------------------------}

expose_d :: (WavefrontDimension, ProtectionDimension, PolicyDimension) =>
         AL -> [LogEntry] -> [ObjId]
expose_d als p = ids $ nub $ [o |
  i <- [0 .. length p - 1],
  let pi = p !! i
      o  = deref als $ old pi
      prepi = pre i p,
  kind pi == M,
  not $ elem (source pi, field pi) $ wlt als prepi,
  ds o]

-- Final version of the expose function

expose_rcd :: (WavefrontDimension, ProtectionDimension, PolicyDimension) =>
              AL -> [LogEntry] -> [ObjId]
expose_rcd als p = nub $ expose_rc als p ++ expose_d als p

{-----------------------------------------------------------------}
{--                    The  examples from the paper             --}
{-----------------------------------------------------------------}


