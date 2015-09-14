Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat.
Require Import Ssreflect.eqtype Ssreflect.ssrfun Ssreflect.seq.
Require Import MathComp.path.
Require Import Eqdep pred prelude idynamic ordtype pcm finmap unionmap heap coding. 
Require Import Hgraphs Logs Wavefronts Apex Partitions.
Require Import WavefrontDimension.
Set Implicit Arguments. 
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Section PolicyDimension.

Variable e0 : LogEntry.
(* Initial graph an heap *)
Variables (h0 : heap) (g0: graph h0).

(* A collector log p will all unique entires *)
Variables  (p : log).

(* Final heap and graph for the log p with the corresponding certificate epf *)
Variables (h : heap) (g: graph h).
Variable (epf : executeLog g0 p = Some (ExRes g)).

Variables (wp polp prp : par2).

(* Wavefront partition *)
Notation FL := (pr1 wp).
Notation OL := (pr2 wp).

(* Policy partition *)
Notation SR := (pr1 polp).
Notation LR := (pr2 polp).

(* Protection partition *)
Notation IS := (pr1 prp).
Notation DS := (pr2 prp).

Notation w_gt := (W_gt g wp).
Notation w_lt := (W_lt g wp).

(* Consider expose_r from Section 5.2.1 of the paper, taking IS =
   True, so it's not mentioned so far. In this shape, expose_r is exactly
   expose_apex, instantiated with W_gt and restricted to the SR part of
   the partition. The LR-part will be processed further. *)

Definition expose_r : seq ptr := 
  [seq let pi := pe.1.2    in
       let o  := source pi in
       let f  := fld pi    in 
       o#f@g | pe <- prefixes e0 p &
               let: (pre, pi, _) := pe          in   
               let k             := (kind pi)   in   
               let o             := (source pi) in
               let f             := (fld pi)    in   
               let n             := (new pi)    in   
               [&& (kindMA k), ((o, f) \in w_gt pre),
                   SR o, IS n & IS (o#f@g)]].


(* A lemma, similar to the one, proved for expose_apex *)

Lemma expose_r_fires et l1 l2 : 
  let o := source et in
  let f := fld    et in
  let x := o # f @ g in
  p = l1 ++ et :: l2  ->
  kind et == T        ->
  (forall q, IS q) -> SR o -> 
  x \in tracedTargets p ++ expose_r.
Proof.
move=>/=E K H1 H2.
rewrite mem_cat; apply/orP.
case: (traced_objects epf E K); [left | right].
- by apply/tracedTargetsP; exists et, l1, l2.
case/hasP: b=>ema D/andP[K2]/andP[/eqP E2]/andP[/eqP E3]/eqP E4; rewrite E2 E3.
case: (prefix_wavefront e0 D E K)=>i[pre][G1]/(w_gt_approx epf wp) G2.
apply/mapP'; exists (pre, ema, i)=>//=; split=>//.
by apply/mem_filter'; rewrite !H1 -!(andbC true) K2/= -E2 -E3 G2; split.
Qed.

(* A number of references from behind of wavefront to o, obtained as a
   result of mutation. *)
Definition M_plus l o : nat := size
     [seq let pi := pe.1.2 in pi
                  | pe <- prefixes e0 l &
                    let: (pre, pi, _) := pe in   
                    [&& (kindMA (kind pi)), (new pi) == o, 
                    (* TODO: over-approximate wavefront with w_gt *)
                    ((source pi, fld pi) \in wavefront (proj1_sig pre)) & 
                    LR (source pi)]].

(* A number of removed references from behind of wavefront to o (check
old pi). *)

Definition M_minus l o : nat := size 
     [seq let pi := pe.1.2 in pi
                  | pe <- prefixes e0 l &
                    let: (pre, pi, _) := pe in   
                    [&& (kindMA (kind pi)), (old pi) == o, 
                    (* TODO: under-approximate wavefront with w_gt *)
                    ((source pi, fld pi) \in wavefront (proj1_sig pre)) & 
                    LR (source pi)]].


(* The following lemma is the key for the proof of expose_c soundness,
   as it justifies the use of the mutator count as a valid way to expose
   reachable objects. *)

Lemma mut_count_fires l h' (g' : graph h') et ema l1 l2 n :
   executeLog g0 l = Some {| hp := h'; gp := g' |} ->
   l = l1 ++ et :: l2 -> kind et == T ->
   ema \in l2 -> kindMA (kind ema) ->
   source et = source ema -> fld et = fld ema ->
   source ema # fld ema @ g' = n ->
   n \in [seq new pi | pi <- l & (M_minus l (new pi) < M_plus l (new pi))].
Proof.
move=>pf E K D Km E1 E2 G; clear epf p h g. 
rename h' into h; rename g' into g.
elim/last_ind: l2 D l pf h g E=>// l2 e Hi D l pf h' g' E. 

(* Hmm, are you sure that there is no bug there? What about the
following 3-entry log:

<Type, Source, Field, Old, New>
--------------------------
<T, o, f, n, n>
<M, o, f, n, n'>
<M, o, f, n', n>

Result M(o) = 0



 *)

(* TODO *)



Admitted.









Definition expose_c : seq ptr := 
     [seq new pi | pi <- p &
                   let n := new pi in
                   [&& (M_plus p n > M_minus p n) & IS n]].


Lemma expose_c_fires et l1 l2 : 
  let o := source et in
  let f := fld    et in
  let x := o # f @ g in
  p = l1 ++ et :: l2  ->
  kind et == T        ->
  (forall q, IS q) -> LR o -> 
  x \in tracedTargets p ++ expose_c.
Proof.
move=>/=E K H1 H2.
rewrite mem_cat; apply/orP.
case: (traced_objects epf E K); [left | right].
- by apply/tracedTargetsP; exists et, l1, l2.
case/hasP: b=>ema D/andP[K2]/andP[/eqP E2]/andP[/eqP E3]/eqP E4; rewrite E2 E3. 
rewrite E2 ?E3 in H2 E4.
rewrite /expose_c E4.
case/mapP: (mut_count_fires epf E K D K2 E2 E3 E4)=>e H3 E'.
apply/mapP; exists e=>//.
by rewrite !mem_filter ?H1 -?(andbC true)/= in H3 *.
Qed.


(* Okay, now we need to figure out, why the inequlaity (M_plus n >
   M_minus n) exposes the sound superset of missed objects wrt. the
   prefix p. Intuitively, this is by the following argument.

   M_plus is number of prefixes of p, where 'o' occurs as a target,
   and some of its corresponding source fields values are
   traced. M_plus is a number of prefixes of p, where 'o' occurs as a
   target, and *all* of its source fields values are traced. The
   difference between the two being equal zero indicates that all
   affected object fields of interest were in fact observed by tracing
   (M_minus makes sure of that thanks to the all-check in the
   definition of W_lt).

   THe actual explanation of this difference (dubbed Mutator Count)
   from the paper is as follows. The mutator count is the number of
   pointers to an object from object fields behind the wavefront. This
   quantity is computed with respect to a given wavefront. We assume
   that some objects in the heap are rescanned objects (SR) that do
   not affect the mutator count. The mutator count computation is
   therefore parameterized by a set of objects LR from which the count
   should be computed.

 *)

Admitted.

End PolicyDimension.