Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat.
Require Import Ssreflect.eqtype Ssreflect.ssrfun Ssreflect.seq.
Require Import MathComp.path.
Require Import Eqdep pred idynamic ordtype pcm finmap unionmap heap coding. 
Require Import hgraphs logs.
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

Lemma in_prefixes_full l e pr i: (pr, e, i) \in prefixes l ->
  [/\ i < size l, nth e0 l i = e & pr = take i l].
Proof.
rewrite /prefixes.
elim: (size l)=>//=n Hi.
case/orP; last first.
- by case/Hi=>H1 H2; split=>//; apply: (ltn_trans H1); apply:ltnSn.
by case/eqP=>Z1 Z2 Z3; subst pr e i.
Qed.

Lemma in_prefixes l e pr i: (pr, e, i) \in prefixes l -> e \in l.
Proof.
case/in_prefixes_full=>H1 H2.
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

Lemma prefixes_num' l j n  : 
  j < n -> n <= size l -> exists e, (take j l, e, j) \in prefixes_rec l n.
Proof.
elim: n=>//=n Hi H1 H2; case B: (j == n); last first.
- have X: j < n by rewrite ltnS leq_eqVlt B/= in H1.
  have Y: n <= size l by apply:ltnW. 
  by case: (Hi X Y)=>e G; exists e; rewrite inE G orbC.
move/eqP: B=>B; subst j=>{H1 Hi}.
exists (nth e0 l n).
by rewrite inE eqxx.
Qed.

Lemma prefixes_num l n  : 
  n < size l -> exists e, (take n l, e, n) \in prefixes l.
Proof.
by move/(@prefixes_num' l n (size l))=>H; apply:H; apply:leqnn.
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
move: (prefixes_in' X1 X2 X3)=>H; split=>//.
by rewrite E take_size_cat /i// mem_cat inE eqxx orbC.
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

End Wavefronts.


