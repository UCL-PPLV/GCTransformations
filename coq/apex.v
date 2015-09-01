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

Definition zip_num l := zip_num' l 0.

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
Fixpoint prefixes_rec (l : log) n := 
  if n is n'.+1 then (take n' l, nth e0 l n', n') :: prefixes_rec l n' else [::].
Definition prefixes l := prefixes_rec l (size l).

(* Some properties of our selector function "prefixes". *)
Lemma take_nth_drop (n : nat) s:
  n < size s ->
  take n s ++ (nth e0 s n) :: drop n.+1 s = s.
Proof.
elim: s n => [|x s IHs] [|n]=>//=[_|]; first by rewrite drop0.
rewrite -[n.+1]addn1 -[(size s).+1]addn1 ltn_add2r=>/IHs=>H.
by rewrite addn1 -{4}H.
Qed.

(* Adequacy of prefixes *)

Lemma in_prefixes' l e pr i: (pr, e, i) \in prefixes l ->
  i < size l /\ nth e0 l i = e.
Proof.
rewrite /prefixes.
elim: (size l)=>//=n Hi.
case/orP; last first.
- by case/Hi=>H1 H2; split=>//; apply: (ltn_trans H1); apply:ltnSn.
by case/eqP=>Z1 Z2 Z3; subst pr e i.
Qed.

Lemma in_prefixes l e pr i: (pr, e, i) \in prefixes l -> e \in l.
Proof.
case/in_prefixes'=>H1 H2.
have X: exists2 j, j < size l & nth e0 l j = e by exists i=>//.
by move/nthP: X.
Qed.

Lemma prefixes_in' l e j n : 
  e \in l -> j < n -> nth e0 l j = e ->
  (take j l, e, j) \in prefixes_rec l n.
Proof.
elim: n=>//=n Hi H1 H2 H3; case B: (j == n).
- by move/eqP: B=>B; subst j; rewrite inE H3 eqxx.
have X: j < n by rewrite ltnS leq_eqVlt B/= in H2.
by rewrite inE; move:(Hi H1 X H3)=>->; rewrite orbC.
Qed.

Lemma prefixes_in l e: e \in l -> 
  exists i, (take i l, e, i) \in prefixes l.
Proof.
by move=>D; case/(nthP e0): (D)=>j H1 H2; exists j; apply: prefixes_in'.
Qed.

Definition expose_apex : seq ptr := 
  [seq let pi := pe.1.2    in
       let o  := source pi in
       let f  := fld pi    in 
       o#f | pe <- prefixes p &
             let: (pre, pi, _) := pe          in   
             let k             := (kind pi)   in   
             let o             := (source pi) in
             let f             := (fld pi)    in   
             (kindMA k) && ((o, f) \in wavefront pre)].


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


