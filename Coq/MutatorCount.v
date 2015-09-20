Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat.
Require Import Ssreflect.eqtype Ssreflect.ssrfun Ssreflect.seq.
Require Import MathComp.path.
Require Import Eqdep pred prelude idynamic ordtype pcm finmap unionmap heap coding. 
Require Import Hgraphs Logs Wavefronts Apex Partitions.
Require Import WavefrontDimension.
Set Implicit Arguments. 
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Section MutatorCount.

Variable e0 : LogEntry.
(* Initial graph an heap *)
Variables (h0 : heap) (g0: graph h0).

Variables (polp : par2).

(* Policy partition *)
Notation SR := (pr1 polp).
Notation LR := (pr2 polp).


(* Importantly, in the following two definitions, we compute the
   sizes, not just of entries pi, but of the corresponding pairs
   (source pi, fld pi). This should facilitate the following proofs,
   as it allows for better partitioning of the contributions into
   positive and negative mutator counts (count_predC). Furthermore, we
   will have to show that M_plus >= M_minus for every pair (o, f) of
   the partition. *)

(* A number of references from behind of wavefront to o, obtained as a
   result of mutation. *)

Definition M_plus l o : nat := size
     [seq let pi := pe.1.2 in (source pi, fld pi)
                  | pe <- prefixes e0 l &
                    let: (pre, pi, _) := pe in   
                    [&& (kindMA (kind pi)), (new pi) == o, 
                    (* TODO: over-approximate wavefront with w_gt *)
                    ((source pi, fld pi) \in wavefront (proj1_sig pre)) & 
                    LR (source pi)]].

(* A number of removed references from behind of wavefront to the
   field object o (check old pi). *)

Definition M_minus l o : nat := size 
     [seq let pi := pe.1.2 in (source pi, fld pi)
                  | pe <- prefixes e0 l &
                    let: (pre, pi, _) := pe in   
                    [&& (kindMA (kind pi)), (old pi) == o, 
                    (* TODO: under-approximate wavefront with w_gt *)
                    ((source pi, fld pi) \in wavefront (proj1_sig pre)) & 
                    LR (source pi)]].


(* The following lemma is the key for the proof of expose_c soundness,
   as it justifies the use of the mutator count as a valid way to expose
   reachable objects. *)

Lemma mut_count_fires l h (g : graph h) et ema l1 l2 :
   executeLog g0 l = Some {| hp := h; gp := g |} ->
   l = l1 ++ et :: l2 -> kind et == T ->
   ema \in l2 -> kindMA (kind ema) ->
   source et = source ema -> fld et = fld ema ->
   source ema # fld ema @ g = new ema ->
   new ema != new et -> LR (source ema) ->
   new ema \in [seq new pi | pi <- l & (M_minus l (new pi) < M_plus l (new pi))].
Proof.
move=>pf E K D Km E1 E2 G N L.
suff X: (M_minus l (new ema) < M_plus l (new ema)).
- apply/mapP; exists ema=>//;
  by rewrite mem_filter X E//= mem_cat inE D -!(orbC true).

(* TODO: it should help to _partition_ sequences in M_plus and M_minus
   into subsequences, corresponding to appropriate (o, f)-entries*)

(* elim/last_ind: l2 D l h g pf E G=>//l2 e Hi D l pf h g E G.  *)
(* rewrite -cats1 mem_cat inE/= in D; case/orP: D; last first. *)
(* move/eqP=>Z; subst ema. *)


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

(* TODO *)

Admitted.

End MutatorCount.
