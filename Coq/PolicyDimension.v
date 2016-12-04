From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep pred prelude idynamic ordtype pcm finmap unionmap heap coding. 
Require Import Hgraphs Logs Wavefronts Apex Partitions.
Require Import WavefrontDimension MutatorCount.
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
  [seq let pi := pe.2      in
       let o  := source pi in
       let f  := fld pi    in 
       o#f@g | pe <- prefixes e0 p &
               let: (pre, pi)    := pe          in   
               let k             := (kind pi)   in   
               let o             := (source pi) in
               let f             := (fld pi)    in   
               let n             := (new pi)    in   
               [&& (kindMA k), ((o, f) \in w_gt pre),
                   SR o & IS n]].

Definition expose_c : seq ptr := 
  [seq new pi | pi <- p &
                let n := new pi    in
                let o := source pi in
                let f := fld pi    in
                [&& (M_plus e0 p o f n > M_minus e0 p o f n), LR o & IS n]].

(* Lemmas: similar to the one, proved for expose_apex *)

Lemma expose_r_fires et l1 l2 : 
  let o := source et in
  let f := fld    et in
  let x := o # f @ g in
  IS x -> SR o -> 
  p = l1 ++ et :: l2  ->
  kind et == T        ->
  x \in alreadyMarked p ++ expose_r.
Proof.
move=>/=H1 H2 E K.
rewrite mem_cat; apply/orP.
case: (traced_objects epf E K); [left | right].
- by apply/alreadyMarkedP; exists et, l1, l2.
case/hasP: b=>ema D/andP[K2]/andP[/eqP E2]/andP[/eqP E3]/eqP E4; rewrite E2 E3.
case: (prefix_wavefront e0 D E K)=>pre[G1]/(w_gt_approx epf wp) G2.
apply/mapP; exists (pre, ema)=>//=.
rewrite mem_filter K2 -E2 -E3 H2 G1 -!(andbC true)/=.
apply/andP; split; last by rewrite -E4 H1.
by apply: G2; case/prefV: G1=>[i][Y1] Y2 Y3; exists i.
Qed.

Lemma expose_c_fires et l1 l2 : 
  let o := source et in
  let f := fld    et in
  let x := o # f @ g in
  IS x -> LR o ->
  p = l1 ++ et :: l2  ->
  kind et == T        ->
  x \in alreadyMarked p ++ expose_c.
Proof.
move=>/=H1 H2 E K.
rewrite mem_cat; apply/orP.
case: (traced_objects' epf E K)=>B.
- by left; apply/alreadyMarkedP; exists et, l1, l2.
case: B=> ema[l3][l4]/andP[M]/andP[/eqP E2]/andP[/eqP E3]N.
case X: (has (matchingTFull ema) p).
- case/hasP: X=>e /in_split[l5][l6]E'/andP[K'/andP[E3']]/andP[E2']E4'.
  by left; apply/alreadyMarkedP; exists e, l5, l6; move/eqP: E4'=>->.  
move/negbT: X=>X; subst l2.
right; rewrite /expose_c.
case/mapP: (mut_count_fires e0 epf E K M E2 X N)=>e H3[Z1 Z2 Z3].
case/andP: M=>_/andP[/eqP Y1]/eqP Y2.
apply/mapP; exists e=>//; last by rewrite -Z3. 
rewrite !mem_filter -!Z1 -!Z2 in H3 *.
rewrite Y1 in H2; rewrite H2/=.
by case/andP: H3=>->->/=; rewrite andbC -Z3 -E2. 
Qed.

Lemma expose_rc_fires et l1 l2 :
  let o := source et in
  let f := fld    et in
  let x := o # f @ g in
  IS x -> p = l1 ++ et :: l2  -> kind et == T ->
  x \in alreadyMarked p ++ expose_r ++ expose_c.
Proof.
move=>o f x H1 E K.
case H2: (SR o).
- move: (expose_r_fires H1 H2 E K); rewrite -/x=>G.
  by rewrite catA mem_cat G.
move: (pr_coh polp o); rewrite H2/==>{H2}H2.
move: (expose_c_fires H1 H2 E K); rewrite -/x=>G.
rewrite !mem_cat in G *.
by case/orP: G=>->//; rewrite -!(orbC true).
Qed.
  
End PolicyDimension.