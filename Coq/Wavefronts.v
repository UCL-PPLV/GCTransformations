Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat.
Require Import Ssreflect.eqtype Ssreflect.ssrfun Ssreflect.seq.
Require Import MathComp.path.
Require Import Eqdep pred idynamic ordtype pcm finmap unionmap heap coding. 
Require Import Hgraphs Logs.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

(*******************************************************************************)
(* Definitions of wavefronts and indexed log prefixes with a number of
   lemmas about them. *)
(*******************************************************************************)


Section Wavefronts.

(* Definition of a wavefront *)
Definition wavefront (l : log) := 
  [seq (source pi, fld pi) | pi <- l & kind pi == T].

(* Default log entry *)
Variable e0 : LogEntry.

Definition prefixes l := 
  map (fun n => (take n l, nth e0 l n, n)) (iota 0 (size l)).

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

Lemma in_prefixes_full l e pr i: (pr, e, i) \in prefixes l ->
  [/\ i < size l, nth e0 l i = e & pr = take i l].
Proof.
case/mapP=>n H; case=>Z1 Z2 Z3; subst i e pr; split=>//.
by rewrite mem_iota add0n in H; case/andP: H.
Qed.

Lemma in_prefixes l e pr i: (pr, e, i) \in prefixes l -> e \in l.
Proof.
case/in_prefixes_full=>H1 H2.
have X: exists2 j, j < size l & nth e0 l j = e by exists i=>//.
by move/nthP: X.
Qed.

Lemma prefixes_in l e: e \in l -> 
  exists i, (take i l, e, i) \in prefixes l.
Proof.
move=>D; case/(nthP e0): (D)=>j H1 H2; exists j.
apply/mapP; exists j; first by rewrite mem_iota add0n.
by rewrite H2.
Qed.

Lemma prefixes_num l n  : 
  n < size l -> exists e, (take n l, e, n) \in prefixes l.
Proof.
move=>D; exists (nth e0 l n); apply/mapP; exists n=>//.
by rewrite mem_iota add0n.
Qed.

Lemma prefV l pr e n:
  (pr, e, n) \in prefixes l -> 
  [/\ pr = take n l, 
      e = (nth e0 l n) & 
      l = pr ++ e :: drop n.+1 l].
Proof.
move=>H; case: (in_prefixes_full H)=>G1 G2 G3.
by rewrite G3 -G2; split=>//; move: (take_nth_drop G1)=>->.
Qed.

Lemma prefix_rev l1 l2 l et e :
  e \in l2 -> l = l1 ++ et :: l2  ->
  exists i, (take i l, e, i) \in prefixes l /\ et \in take i l.
Proof.
case/splitP=>{l2}l2 l3.
rewrite -cat_cons -cats1 cat_cons -catA cat1s -cat_cons catA.
set i := size (l1 ++ et :: l2); move=>E; exists i.
have X1 : e \in l by rewrite E mem_cat inE eqxx orbC.  
have X2: i < size l
  by rewrite/i E!size_cat -addnA ltn_add2l -{1}[size (_::l2)]addn0 ltn_add2l. 
have Y: forall a, a - a = 0 by elim.
have X3: nth e0 l i = e by rewrite E nth_cat /i ltnn Y/=. 
split; last by rewrite E take_size_cat /i// mem_cat inE eqxx orbC.
apply/mapP; exists i; last by rewrite X3.
by rewrite mem_iota add0n.
Qed.


Lemma prefix_wavefront l1 l2 l et e :
  e \in l2 -> l = l1 ++ et :: l2  -> kind et == T ->
  exists i pre, (pre, e, i) \in prefixes l /\ 
                (source et, fld et) \in (wavefront pre).
Proof.
move=>H1 H2 T; case:(prefix_rev H1 H2)=>i[H3 H4].
exists i, (take i l); split=>//.
by apply/mapP; exists et=>//; rewrite mem_filter T. 
Qed.

Lemma wavefront_trace l o : o \in wavefront l ->
   exists (e : LogEntry) (l1 l2 : seq LogEntry),
     [/\ l = l1 ++ e :: l2, kind e == T, source e = o.1 & fld e = o.2].
Proof.
case/mapP=>e; rewrite mem_filter=>/andP[H1].
by case/in_split=>l1[l2][E]->/=; exists e, l1, l2.
Qed.

End Wavefronts.

