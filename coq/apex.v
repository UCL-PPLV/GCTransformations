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

[1] First, we define all reachable objects at the moments tracing was
    done (we now have a certified function for this).  

Specifically, such objects are those that are pointed to by the fields
in T-entries. 

*)

(* Collect all traced objects from the log *)
Definition tracedObjects3 : seq (ptr * nat * ptr) :=
  [seq (source pi, fld pi, old pi) | pi <- p & (kind pi) == T]. 

Definition tracedObjFields : seq (ptr * nat) := unzip1 tracedObjects3.
Definition tracedTargets : seq ptr := unzip2 tracedObjects3.

(* 

We need to prove the following facts about traced objects:

T1: If (pi \in p) then (old pi) \in dom h, where h is a heap, obtained
    by replaying (take (index pi p) p). In other words, the tracked
    object belong to the heap.

T2: Graph monotonicity: let (hn, gn) = replayLog (take n p), then (dom
    hn <= dom h) -- the domain of the graph only grows.

T1 an T2 combined give us that tracked objects form a subset of the
final heap h.


[2] Next, we define the set of actual objects in the final heap-graph
    with respect to traced objects.

*)

Definition actualTargets : seq ptr := 
  [seq (pf.1)#(pf.2) | pf <- tracedObjFields].

(*

[3] Finally, the following theorem states the soundness of the
    expose_apex procedure: it adds to the tracedTargets a set of
    pointers, such that the union of the two contains the actual
    targets by the end of the log execution.

*)

Theorem expose_apex_sound : 
  {subset actualTargets <= tracedTargets ++ expose_apex}.
Proof.
admit.
Admitted.

End ApexAlgo.


