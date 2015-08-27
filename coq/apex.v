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

(* A good log p wrt. initial heap h0 *)
Variables (p : log) (pf: goodLog (keys_of h0) p) (upf : uniq p).

(* Final heap and graph *)
Variables (h : heap) (g: graph h).
Variable (epf : executeLog g0 p = Some (ExRes g)).

(* Dereferencing an object field *)
Notation "o '#' f" := (nth null (fields g o) f)
  (at level 43, left associativity).

(******************************************************************)
(*    Apex procedure for exposing reachable objects in the graph  *)
(******************************************************************)

Eval compute in let lst := [:: 1; 2; 3] in take (index 1 lst) lst.


(* 

To simplify the implementation, we ensure that all entries in the log
are unique (see the assumption 'upf'). Therefore, the prefix 'prepi'
is unambiguously defined for each entry in the log, and is computed by
an entry itself, not a specific index.
*)

Definition expose_apex := 
  [seq let o := (source pi) in
       let f := (fld pi)    in 
       o#f | pi <- p &
             let o     := (source pi)           in
             let f     := (fld pi)              in   
             let k     := (kind pi)             in   
             let prepi := (take (index pi p) p) in
             (kindMA k) && ((o, f) \in wavefront prepi)].



End ApexAlgo.
