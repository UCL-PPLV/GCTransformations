{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NullaryTypeClasses #-}

module GCExample23 where

import Data.Map as M
import Data.Maybe as MB
import Data.List as L
import Control.Monad
import Data.Maybe
import GCDerivation

{- Example 2.3 -}

-- Initial objects
r1, a, b, c, d, e :: Object
r1 = O "r1" $ fromList $ 
              [("f1", Nothing), ("f2", Just "A"), ("f3", Just "E")]
a  = O "A" $ fromList $ 
             [("f1", Nothing), ("f2", Nothing), ("f3", Nothing)]
b = O "B" empty
c = O "C" $ fromList [("f", Just "B")]
d = O "D" $ fromList [("f", Just "E")]
e = O "E" empty

-- Final set of the objects
al_final = [r1, a, b, c, d, e]

prefix_pe :: [LogEntry]
prefix_pe = [
  LE T "r1" "f2" (Just "A") (Just "A"),
  LE T "A"  "f1" Nothing    Nothing,
  LE T "r1" "f3" Nothing    Nothing,
  --
  LE M "r1" "f1" Nothing    (Just "B"),
  LE M "A"  "f1" Nothing    (Just "B"),
  LE M "r1" "f3" Nothing    (Just "E"),
  --
  LE M "A"  "f2" (Just "C")  Nothing,
  LE M "r1" "f1" (Just "B")  Nothing,
  LE T "A"  "f2" Nothing     Nothing,
  --
  LE T "r1" "f1" Nothing    Nothing,
  LE M "A"  "f3" (Just "D") Nothing,
  LE M "A"  "f1" (Just "B") Nothing,
  --
  LE T "A"  "f3" Nothing    Nothing]

-- Computing the wavefront

wf_pe :: [(ObjId, FName)]
wf_pe = wavefront prefix_pe 
-- try wf_pre from the interpreter
-- Okay, that works!
