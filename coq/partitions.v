Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat.
Require Import Ssreflect.eqtype Ssreflect.ssrfun Ssreflect.seq.
Require Import MathComp.path.
Require Import Eqdep pred prelude idynamic ordtype pcm finmap unionmap heap coding. 
Require Import hgraphs logs wavefronts apex.
Set Implicit Arguments. 
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Section Partitions.

(* Abstract interface for two-partition of the object space *)

Structure par2 := Par2 {
  pr1 : ptr -> bool;
  pr2 : ptr -> bool;
  pr_coh : forall o, addb (pr1 o) (pr2 o)
}.

End Partitions.


