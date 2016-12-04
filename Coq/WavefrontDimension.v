From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep pred prelude idynamic ordtype pcm finmap unionmap heap coding. 
Require Import Hgraphs Logs Wavefronts Apex Partitions.
Set Implicit Arguments. 
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Section WavefrontDimension.

(* Initial graph an heap *)
Variables (h0 : heap) (g0: graph h0).

(* A collector log p will all unique entires *)
Variables  (p : log).

(* Final heap and graph for the log p with the corresponding certificate epf *)
Variables (h : heap) (g: graph h).
Variable (epf : executeLog g0 p = Some (ExRes g)).

Variable wp : par2.
Notation FL := (pr1 wp).
Notation OL := (pr2 wp).

Definition all_obj_fields (e : ptr) := 
    [seq (e, f) | f <- iota 0 (size (fields g e))]. 

Definition all_obj_fields_wf l :=
    flatten [seq (all_obj_fields e.1) | e <- wavefront l].

(* W_gt approximates the set of object fields behind the wavefront by
   taking all_obj_fields of an object instead specific traced fields
   in the wavefront.

   Importantly, this is a *certified* function, as it needs to work
   only on prefixes of p (in order to determine the size of the field
   map for an object being processed correctly), hence the type of its
   argument, which is not just a log, but a prefix of the main GC log
   p, for which the expose procedure is run. *)

Definition W_gt l := 
   let wfl := [seq ef <- wavefront l         | FL ef.1] in
   let wol := [seq ef <- all_obj_fields_wf l | OL ef.1] in
       wfl ++ wol.

Lemma w_gt_approx l : 
  prefix l p -> {subset wavefront l <= W_gt l}.
Proof.
case=>n pf/=.
move=>o; rewrite /W_gt mem_cat !mem_filter.
case X: (FL o.1)=>//=H; first by rewrite H.
move: (pr_coh wp (o.1)); rewrite X=>/=->/=.
apply/flatten_mapP; exists o=>//.
apply/mapP; exists o.2; last by rewrite -surjective_pairing.
case: (wavefront_trace H)=>e[l1][l2][H1]H2 H3 H4.
move: (cat_take_drop n p); rewrite -pf=>/sym.
rewrite H1 -catA cat_cons=>H5.
move: (trace_fsize epf H2 H5); rewrite H3 H4.
by rewrite mem_iota add0n. 
Qed.

Variable e0 : LogEntry.

(* expose_apex is sound with W_gt for *any* wavefront partition *)

Corollary w_gt_expose_apex_sound : 
  {subset needToBeMarked p g
            <= markedObjects p ++ expose_apex e0 p g W_gt}.
Proof. by apply: (expose_apex_sound e0 epf w_gt_approx). Qed.

(* W_gt is an underapproximation the set of object fields' values
   behind the wavefront. Therefore, it over-approximates the set of
   object fields ahead of the wavefront. We can show that it returns a
   subset of all objects in the wavefront, as its OL-part only reports
   the objects whose *all* fields were traced in the wavefront. *)

Definition W_lt l := 
   let wfl := [seq ef | ef <- wavefront l & FL ef.1] in
   let wol := [seq ef | ef <- wavefront l & 
                        (OL ef.1) && 
                        (*  All fields of this object are in the wavefront *)
                        all (fun e => e \in wavefront l)
                            (all_obj_fields_wf l)]
   in  wfl ++ wol.

End WavefrontDimension.

