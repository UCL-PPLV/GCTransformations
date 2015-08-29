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
Variables  (p : log).

(* Final heap and graph for the log p with the corresponding certificate epf *)
Variables (h : heap) (g: graph h).
Variable (epf : executeLog g0 p = Some (ExRes g)).

(* Dereferencing an object field *)
Notation "o '#' f" := (nth null (fields g o) f)
  (at level 43, left associativity).

(******************************************************************)
(*    Apex procedure for exposing reachable objects in the graph  *)
(******************************************************************)

(* An auxiliary function that generates all prefixes for elements of a
list l0 *)

Fixpoint zip_num' (l : log) n :=
  match l with
  | [::]  => [::]
  | e::l' => (e, n) :: zip_num' l' (n.+1)
  end.

(* Lemma zip_num_elems' e n l: forall m, *)
(*   (e, n) \in zip_num' l (m - size l) -> *)
(*   (size l <= m) -> m <= n + size l -> *)
(*   nth e l (n + size l - m) = e. *)
(* Proof. *)
(* elim: l=>//=x xs Hi m D H1 H2. *)
(* case/orP: D. *)
(* - case/eqP=>G1 G2; subst e n. *)
(*   suff S: (m - (size xs).+1 + (size xs).+1 - m) = 0. *)
(*   by rewrite S. *)
(*   rewrite subnK//; suff X a : a - a = 0 by []; last by elim: a. *)
(* rewrite subnSK //= =>G. *)
(* suff S: n + (size xs).+1 - m = (n + (size xs) - m).+1. *)
(* rewrite S/=; apply: Hi=>//; first by apply: ltnW. *)
(* rewrite -addn1 addnA -[(_ - _).+1]addn1 -!(addnC 1) addnA. *)
(* rewrite addnBA ?addnA//. *)
(* by apply: (leq_trans H2); apply: leq_addr. *)
(* Qed. *)

Definition zip_num l := zip_num' l 0.

(* Lemma zip_num_elems e n l:  *)
(*   (e, n) \in zip_num l -> nth e l n = e. *)
(* Proof. *)
(* set m := size l. *)
(* move: () *)

Fixpoint prefs_els_rec (l0 l : log) n := 
  match l with 
  | [::]  => [::]
  | e::l' => (take n l0, e, n) :: prefs_els_rec l0 l' (n.+1)
  end.

Definition prefs_els l := prefs_els_rec l l 0.
 
Lemma prefs_take1' l: forall pr e n,
  (pr, e, n) \in (prefs_els_rec l l (size l - size l)) ->
  (size l <= size l) -> 
  (pr = take n l).
Proof.
elim/list_ind: l {-2 4 5}l=>// x xs Hi l pr e n/= D H.
rewrite !inE /=in D; case/orP: D; first by case/eqP=>Z1 Z2 Z3; subst pr e n. 
by rewrite subnSK// =>G; apply: (Hi _ _ _  _ G); apply: ltnW.
Qed.

Lemma prefs_take1 l pr e n:
   (pr, e, n) \in prefs_els l -> pr = take n l.
Proof.
move=>H. 
have N: forall n, n - n = 0 by elim.
have X: (pr, e, n) \in (prefs_els_rec l l (size l - size l)).
- by rewrite N. 
by apply: (prefs_take1' X); apply: leqnn.
Qed.


(* Default log entry *)
Variable e0 : LogEntry.

(* An alternative definition of a log decomposition procedure *)
Fixpoint prefs_els_rec2 (l : log) n := 
  if n is n'.+1 then (take n l, nth e0 l n) :: prefs_els_rec2 l n' else [::].
Definition prefs_els2 l := prefs_els_rec2 l (size l - 1).

Lemma take_nth_drop (n : nat) s:
  n < size s ->
  take n s ++ (nth e0 s n) :: drop n.+1 s = s.
Proof.
elim: s n => [|x s IHs] [|n]=>//=[_|]; first by rewrite drop0.
rewrite -[n.+1]addn1 -[(size s).+1]addn1 ltn_add2r=>/IHs=>H.
by rewrite addn1 -{4}H.
Qed.


Definition expose_apex : seq ptr := 
  [seq let pi := pe.2     in
       let o  := source pi in
       let f  := fld pi    in 
       o#f | pe <- prefs_els2 p &
             let: (pre, pi)    := pe          in   
             let k             := (kind pi)   in   
             let o             := (source pi) in
             let f             := (fld pi)    in   
             (kindMA k) && ((o, f) \in wavefront pre)].

Search _ (take _) (nth _).

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


