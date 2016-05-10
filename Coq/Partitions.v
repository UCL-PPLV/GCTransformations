From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep pred prelude idynamic ordtype pcm finmap unionmap heap coding. 
Require Import Hgraphs Logs Wavefronts Apex.
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


