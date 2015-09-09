Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat.
Require Import Ssreflect.eqtype Ssreflect.ssrfun Ssreflect.seq.
Require Import MathComp.path.
Require Import Eqdep pred prelude idynamic ordtype pcm finmap unionmap heap coding. 
Require Import hgraphs logs wavefronts apex partitions.
Require Import WavefrontDimension.
Set Implicit Arguments. 
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Section PolicyDimension.

Variable e0 : LogEntry.
(* Initial graph an heap *)
Variables (h0 : heap) (g0: graph h0).

(* A collector log p will all unique entires *)
Variables  (p : log).

(* Final heap and graph for the log p with the corresponding certificate epf *)
Variables (h : heap) (g: graph h).
Variable (epf : executeLog g0 p = Some (ExRes g)).

Variables (wp pp : par2).

(* Wavefront partition *)
Notation FL := (pr1 wp).
Notation OL := (pr2 wp).

(* Policy partition *)
Notation SR := (pr1 pp).
Notation LR := (pr2 pp).

Notation w_gt := (W_gt g wp).

(* Consider expose_r from Section 5.2.1 of the paper, taking IS =
   True, so it's not mentioned so far. In this shape, expose_r is exactly
   expose_apex, instantiated with W_gt and restricted to the SR part of
   the partition. The LR-part will be processed further. *)

Definition expose_r : seq ptr := 
  [seq let pi := pe.1.2    in
       let o  := source pi in
       let f  := fld pi    in 
       o#f@g | pe <- prefixes e0 p &
               let: (pre, pi, _) := pe          in   
               let k             := (kind pi)   in   
               let o             := (source pi) in
               let f             := (fld pi)    in   
               [&& (kindMA k), ((o, f) \in w_gt pre) &
                   SR o]].

(* TODO: use seq.undup to remove duplicates  *)

Search _ (undup _) (size _).

End PolicyDimension.