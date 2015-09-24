Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat.
Require Import Ssreflect.eqtype Ssreflect.ssrfun Ssreflect.seq.
Require Import MathComp.path.
Require Import Eqdep pred prelude idynamic ordtype pcm finmap unionmap heap coding. 
Require Import Hgraphs Logs Wavefronts.
Require Import WavefrontDimension.
Set Implicit Arguments. 
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Lemma find_first {A: eqType} (l : seq A) f : has f l ->
  exists e l1 l2, [/\ l = l1 ++ e :: l2, f e & ~~ has f l1].
Proof.
elim:l=>//= e l Hi; case X : (f e)=>/=.
- by move=> _; exists e, [::], l; rewrite cat0s.
case/Hi=>e'[l1][l2][E1]H1 H2.
by exists e', (e:: l1), l2; rewrite E1/= X H2/= H1. 
Qed.

(* The sequence l is positive (wrt. to pos/neg functions), if it can
   be parititioned by negative elements to sequences with non-negative
   pos/neg balances, as established by the following lemmas. *)

Inductive PositiveSeq {A : eqType} (pos neg : A -> bool) (l : seq A) : Prop :=
  | MT of l = [::]
  | NegSplit l1 e l2 of l = l1 ++ e :: l2 & neg e & ~~ has neg l2 & 
                        has pos (e :: l2) & PositiveSeq pos neg l1.

Lemma countNeg {A : eqType} (f : A -> bool) (l : seq A) : 
  ~~ has f l -> count f l = 0.
Proof.
elim: l=>//=e l Hi/norP[H1 /Hi]H2; rewrite H2 addn0.
by move/negbRL: H1=>->.
Qed.

Lemma countPos {A : eqType} (f : A -> bool) (l : seq A) : 
  has f l -> count f l >= 1.
Proof. by elim: l=>//=e l Hi/orP; case=>[->|/Hi /(ltn_addl (f e))]. Qed.

Lemma posChunkCount {A : eqType} (pos neg : A -> bool) e l :
  neg e -> ~~ has neg l -> has pos (e :: l) -> 
  count neg (e :: l) <= count pos (e :: l).
Proof.
move=>H1 H2 /= H3; rewrite H1 (countNeg H2) addn0.
case/orP: H3=>/=[->|H3]; first by apply: leq_addr.
by move/(ltn_addl (pos e)): (countPos H3).
Qed.

Lemma posCount {A : eqType} pos neg (l : seq A) : 
  PositiveSeq pos neg l -> count neg l <= count pos l.
Proof.
elim=>{l}[l->|l l1 e l2 -> H1 H2 H3 _ Hi]//; rewrite !count_cat.
by apply: leq_add=>//; last by apply: posChunkCount.
Qed.

Section MutatorCount.

Variable e0 : LogEntry.

Definition M_plus l o f n : nat := size 
             [seq (o, f, n)
                  | pe <- prefixes e0 l &
                    let: (pre, pi) := pe in   
                    [&& (kindMA (kind pi)), (new pi) == n, 
                    (source pi, fld pi) == (o, f) &
                    (* TODO: over-approximate wavefront with w_gt *)
                    ((o, f) \in wavefront pre)]].

(* A number of removed references from behind of wavefront to the
   field object o (check old pi). *)

Definition M_minus l o f n : nat := size 
             [seq (o, f, n)
                  | pe <- prefixes e0 l &
                    let: (pre, pi) := pe in   
                    [&& (kindMA (kind pi)), (old pi) == n, 
                    (source pi, fld pi) == (o, f) &
                    (* TODO: under-approximate wavefront with w_gt *)
                    ((o, f) \in wavefront pre)]].


(* TODO: We now prove that the values of M+ and M- for a log, starting
   with an appropriate T-entry can be expressed as counts of new- and
   old- mutations.
 *)

Definition mpos o f n (pi : LogEntry)  := 
  [&& (kindMA (kind pi)), (new pi) == n & (source pi, fld pi) == (o, f)].

Definition mneg o f n (pi : LogEntry)  := 
  [&& (kindMA (kind pi)), (old pi) == n & (source pi, fld pi) == (o, f)].

Lemma seq_inc {A : Type } (f g : nat -> A) n : forall i, f i.+1 = g i ->
  [seq f i | i <- iota 1 n] = [seq g i | i <- iota 0 n].


Lemma m_plus_count et l o f n :
  kind et = T -> fld et = f -> source et = o ->
  M_plus (et :: l) o f n = count (mpos o f n) (et :: l).
Proof.
move=>H1 H2 H3; rewrite /M_plus size_map size_filter.

Search  _ (count _) (_ :: _).

Lemma prefix_cons e l  : 
  prefixes e0 (e :: l) = 
  ([::], e) :: [seq (e :: pe.1, pe.2) | pe <- prefixes e0 l].
Proof.
congr (_ :: _); rewrite /prefixes -seq.map_comp.

have H : forall i, 
         (fun n => (take n (e :: l), nth e0 (e :: l) n)) i.+1 = 
         ((fun pe : seq LogEntry * LogEntry => (e :: pe.1, pe.2)) \o
           (fun n : nat => (take n l, nth e0 l n))) i by case.





case/mapP=>n H1 H2; rewrite /= inE in H1.
case/orP: H1=>[|H1]; [by move/eqP=>Z; subst n; left|right]. 
rewrite mem_iota in H1; case/andP: H1=>H G.
have S: exists m, n = m.+1 by clear G H2; case: n H=>//n _; exists n.
by case: S=>[m]Z; subst n; case: H2=>/=-> _; exists (take m l).
Qed.





(* TODO: Our subsequent goal is to show that the result of lemma
   posCount is applicable for a "good" log l and pos := match (s, f,
   new), neg := match (s, f, old). In other words, we need to prove
   that each such log (starting from the corresponding T-entry is a
   subject of PositiveSeq). *)








(* A T-entry e records exactly the new value of a MA-entry *)

Definition matchingTFull ema := fun e =>
   [&& kind e == T, fld e == fld ema,
       source e == source ema & new e == new ema].

Definition matchingT ema := fun e =>
   [&& kind e == T, fld e == fld ema & source e == source ema].


(* Okay, can we reformulate M_plus and M_minus as something more
   suitable for processing in a specific case: basically, computing a
   number of plus and minus entries in the intermediate log. *)


(* 
A general invariant for the mutator count for a specific object-field
(o, f) should state that for any triple (o, f, n), if 

- l = et :: l2, and et traces (o, f)
- there is no entry in l that traces "n" of (o, f),

Then M+(o, f, n) >= M-(o, f, n). 

The tricky part of the proof is dealing with decrements of the mutator
count. In this case, we should show that previously the inequality
was, actually, strict, as there should've been an immeditely preceding
entry, assigning this field. The last fact should be a separate lemma. 

Also, we need to prove some distributivity facts of M+ and M- over
logs.
 

*)





Lemma mut_count_trimmed h0 (g0 : graph h0) l h (g : graph h) et ema l2 :
   executeLog g0 l = Some {| hp := h; gp := g |} ->
   l = (et :: rcons l2 ema) -> kind et == T ->
   matchingMA (source et) (fld et) ema ->
   source et # fld et @ g = new ema ->
   ~~ has (matchingTFull ema) l ->
   M_minus l (source ema) (fld ema) (new ema) <
   M_plus l (source ema) (fld ema) (new ema).
Proof. 
(* 

The proof of this fact goes by induction on l2, however, the inductive
invariant is somewhat tricky. In particular, we should ensure that for
each decrement of the mutator count, there should be a preceding
entry, which increases it. So, see a more general previous statement.



 *)
Admitted.



Lemma mut_count h0 (g0 : graph h0) l h (g : graph h) et ema l1 l2 l3 :
   executeLog g0 l = Some {| hp := h; gp := g |} ->
   l = l1 ++ (et :: rcons l2 ema) ++ l3 -> kind et == T ->
   matchingMA (source et) (fld et) ema ->
   source et # fld et @ g = new ema ->
   ~~ has (matchingTFull ema) l ->
   ~~ has (matchingT ema) l1 ->
   ~~ has (matchingMA (source et) (fld et)) l3 ->
   M_minus l (source ema) (fld ema) (new ema) <
   M_plus l (source ema) (fld ema) (new ema).
Proof. 

(* 

The proof of this lemma should be reucible to the proof of the
previous fact, mu_count_clean, which trims the lists l1 and l3,
because of the following reasons:

   - l1 doesn't have entries that can affect the wavefront wrt. ema's
     parameters (o, f), so excluding it doesn't change M+ and M-.
   
   - l3 doesn't have MA-entries with the same source/field, hence it
     doesn't affect the values of M+ and M-

   The proofs of these "trimming" lemmas should be explicitly
   constructed. So, for now see the previous statement

*)

Admitted. 


(* The following lemma is the key for the proof of expose_c soundness,
   as it justifies the use of the mutator count as a valid way to expose
   reachable objects. *)

Lemma mut_count_fires h0 (g0 : graph h0) l h (g : graph h) et ema l1 l2 l3 :
   executeLog g0 l = Some {| hp := h; gp := g |} ->
   l = l1 ++ et :: l2 ++ ema :: l3 -> kind et == T ->
   matchingMA (source et) (fld et) ema ->
   source et # fld et @ g = new ema ->
   ~~ has (matchingTFull ema) l ->
   ~~ has (matchingMA (source et) (fld et)) l3 ->
   (source ema, fld ema, new ema) \in 
       [seq (source pi, fld pi, new pi) | 
        pi <- l & (M_minus l (source ema) (fld ema) (new pi) < 
                   M_plus  l (source ema) (fld ema) (new pi))].
Proof.
move=>pf E K M E1 H1 H2.
suff X: (M_minus l (source ema) (fld ema) (new ema) < 
         M_plus  l (source ema) (fld ema) (new ema)).
- apply/mapP; exists ema=>//.
  by rewrite mem_filter X E//= mem_cat inE mem_cat inE eqxx -!(orbC true). 
have X: has (matchingT ema) (l1 ++ [:: et]).
- rewrite has_cat/= -!(orbC false)/=; apply/orP; right.
  rewrite /matchingT; case/andP: M=>_/andP[/eqP->]/eqP->. 
  by rewrite K !eqxx.
case: (find_first X)=>et'[l1'][l2'][E2]H3 H4.
rewrite -cat_cons catA -(cat_rcons et) -cats1 E2 -!catA in E.
rewrite cat_cons -(cat_rcons ema) -cats1 in E.
rewrite catA cats1 -rcons_cat -(cat_cons et') in E. 
case/andP: (H3)=>Z/andP[/eqP A2]/eqP A1.
case/andP: (M)=>_/andP[/eqP B1]/eqP B2.
rewrite B1 -A1 B2 -A2 in M E1 H2.
by apply: (@mut_count h0 g0 l h g et' ema l1' (l2' ++ l2) l3)=>//.
Qed.


(* TODO: Now, we have explicitly excluded all cases when there are
   some T-entries, tracing the same object (new ema), yet there is an
   entry et, which marks (o, f) as traced. The proof should account
   for the fact that in this setting the negative count cannot be
   bigger than positive count. Perhaps, we should focus on the *first*
   T-entry et, such that its (o, f) records the right field and the
   last MA-entry, which contributes to the (o, f) in the graph.

 *)


(* Hmm, are you sure that there is no bug there? What about the
following 3-entry log:

<Type, Source, Field, Old, New>
--------------------------
<T, o, f, n, n>
<M, o, f, n, n'>
<M, o, f, n', n>

This results is M+(o) = 1 and M-(o) = 1, hence M(o) = 0. Hmm, but then
this case is covered, since the object is correctly captured in the
T-entry itself. Interesting.

 *)

End MutatorCount.
