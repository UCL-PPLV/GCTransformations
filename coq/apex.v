Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat.
Require Import Ssreflect.eqtype Ssreflect.ssrfun Ssreflect.seq.
Require Import MathComp.path.
Require Import Eqdep pred idynamic ordtype pcm finmap unionmap heap coding. 
Require Import hgraphs logs.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Section ApexAlgo.

(* Initial graph an heap *)
Variables (h0 : heap) (g0: graph h0).

(* A collector log p will all unique entires *)
Variables  (p : log) (upf : uniq p).

(* Final heap and graph for the log p with the corresponding certificate epf *)
Variables (h : heap) (g: graph h).
Variable (epf : executeLog g0 p = Some (ExRes g)).

(* Dereferencing an object field *)
Notation "o '#' f" := (nth null (fields g o) f)
  (at level 43, left associativity).

(******************************************************************)
(*    Apex procedure for exposing reachable objects in the graph  *)
(******************************************************************)

(* Eval compute in let lst := [:: 1; 2; 3] in take (index 1 lst) lst. *)

(* 

To simplify the implementation, we ensure that all entries in the log
are unique (see the assumption 'upf'). Therefore, the prefix 'prepi'
is unambiguously defined for each entry in the log, and is computed by
an entry itself, not a specific index.
*)

Definition expose_apex : seq ptr := 
  [seq let o := (source pi) in
       let f := (fld pi)    in 
       o#f | pi <- p &
             let k     := (kind pi)             in   
             let o     := (source pi)           in
             let f     := (fld pi)              in   
             let prepi := (take (index pi p) p) in
             (kindMA k) && ((o, f) \in wavefront prepi)].

(* Now, we have to show that only reachable objects are exposed by the
'expose_apex' procedure... *)

(*

The intuition is as follows: 'expose_apex' rescans the log prefix, and
for each object entry in it (pi) checks, whether it's allocation or
modification (kindMA k), and furthermore, it can affect any of the
knowledge that has been already traced by the collector
previoiusly. For the last, we check whether this object-field pair (o,
f) has been traced, i.e., whether it belongs to the wavefront,
preceding the actual entry being examined. 

So, what the correctness statement should look like? Presumably,
something as follows:

1. First, we define all reachable objects at the moments tracing was
done (we now have a certified function for this). We take a union of
all these reachable objects in the graph.

2. TODO


*)




End ApexAlgo.


