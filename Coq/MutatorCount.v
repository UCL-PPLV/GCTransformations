Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat.
Require Import Ssreflect.eqtype Ssreflect.ssrfun Ssreflect.seq.
Require Import MathComp.path.
Require Import Eqdep pred prelude idynamic ordtype pcm finmap unionmap heap coding. 
Require Import Hgraphs Logs Wavefronts.
Require Import WavefrontDimension.
Set Implicit Arguments. 
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Section MutatorCount.

Variable e0 : LogEntry.
(* Initial graph an heap *)
Variables (h0 : heap) (g0: graph h0).


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

Definition matchingT ema := fun e =>
   [&& kind e == T, fld e == fld ema,
       source e == source ema & new e == new ema].


Lemma mut_count l h (g : graph h) et ema l1 l2 l3 :
   executeLog g0 l = Some {| hp := h; gp := g |} ->
   l = l1 ++ et :: l2 ++ ema :: l3 -> kind et == T ->
   matchingMA (source et) (fld et) ema ->
   source et # fld et @ g = new ema ->
   ~~ has (matchingT ema) l ->
   ~~ has (matchingMA (source et) (fld et)) l3 ->
   M_minus l (source ema) (fld ema) (new ema) <
   M_plus l (source ema) (fld ema) (new ema).
Proof. Admitted. 


(* The following lemma is the key for the proof of expose_c soundness,
   as it justifies the use of the mutator count as a valid way to expose
   reachable objects. *)

Lemma mut_count_fires l h (g : graph h) et ema l1 l2 l3 :
   executeLog g0 l = Some {| hp := h; gp := g |} ->
   l = l1 ++ et :: l2 ++ ema :: l3 -> kind et == T ->
   matchingMA (source et) (fld et) ema ->
   source et # fld et @ g = new ema ->
   ~~ has (matchingT ema) l ->
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
by apply: (@mut_count l h g et ema l1 l2 l3).
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
