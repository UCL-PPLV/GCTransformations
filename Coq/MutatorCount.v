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

Section MutatorCount.

Variable e0 : LogEntry.
(* Initial graph an heap *)

(* A number of references from behind of wavefront to o, obtained as a
   result of mutation. *)

Definition M_plus l o f n : nat := size 
             [seq (o, f, n)
                  | pe <- prefixes e0 l &
                    let: (pre, pi, _) := pe in   
                    [&& (kindMA (kind pi)), (new pi) == n, 
                    (* TODO: over-approximate wavefront with w_gt *)
                    (source pi, fld pi) == (o, f) &
                    ((o, f) \in wavefront (proj1_sig pre))]].

(* A number of removed references from behind of wavefront to the
   field object o (check old pi). *)

Definition M_minus l o f n : nat := size 
             [seq (o, f, n)
                  | pe <- prefixes e0 l &
                    let: (pre, pi, _) := pe in   
                    [&& (kindMA (kind pi)), (old pi) == n, 
                    (* TODO: under-approximate wavefront with w_gt *)
                    (source pi, fld pi) == (o, f) &
                    ((o, f) \in wavefront (proj1_sig pre))]].

(* A T-entry e records exactly the new value of a MA-entry *)

Definition matchingTFull ema := fun e =>
   [&& kind e == T, fld e == fld ema,
       source e == source ema & new e == new ema].

Definition matchingT ema := fun e =>
   [&& kind e == T, fld e == fld ema & source e == source ema].


(* Lemma mut_count_inv h0 (g0 : graph h0) l h (g : graph h) et l2 : *)
(*    executeLog g0 l = Some {| hp := h; gp := g |} -> *)
(*    l = et :: l2 -> kind et == T -> *)
(*    ~~ has (matchingTFull ema) l -> *)
(*    M_minus l (source et) (fld et) (new et) <= *)
(*    M_plus l (source et) (fld et) (new et). *)
(* Proof.  *)
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
