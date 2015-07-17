{-# LANGUAGE TypeOperators #-}

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

-- TODO