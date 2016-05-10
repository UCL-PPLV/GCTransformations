From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep pred idynamic ordtype pcm finmap unionmap heap coding. 
Require Import Hgraphs Logs Wavefronts.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 


(********************************************************************************)
(* Implementation of the Apex 'expose' function and the proof of its soundness. *)
(********************************************************************************)

Definition prefix {A : eqType} (l1 l : seq A) := exists n, l1 = take n l.

Section ApexAlgo.

(* Default log entry *)
Variable e0 : LogEntry.

(* Initial graph an heap *)
Variables (h0 : heap) (g0: graph h0).

(* A collector log p will all unique entires *)
Variables  (p : log).

(* Final heap and graph for the log p with the corresponding certificate epf *)
Variables (h : heap) (g: graph h).
Variable (epf : executeLog g0 p = Some (ExRes g)).

(******************************************************************)
(*    Apex procedure for exposing reachable objects in the graph  *)
(******************************************************************)

(* A candidate for approximating wavefront *)
Variable wf_approx : log -> seq (ptr * nat).

Hypothesis wfp : forall l, prefix l p ->
   {subset wavefront l <= wf_approx l}. 

Definition expose_apex : seq ptr := 
  [seq let pi := pe.2      in
       let o  := source pi in
       let f  := fld pi    in 
       o#f@g | pe <- prefixes e0 p &
               let: (pre, pi)    := pe          in   
               let k             := (kind pi)   in   
               let o             := (source pi) in
               let f             := (fld pi)    in   
               (kindMA k) && ((o, f) \in wf_approx pre)].

(* The following lemma roughly corresponds to "pre-safety" of the
   expose_apex procedure. It states that if there is an MA-entry 'ema'
   in the log, preceded by some T-entry 'et', and moreover, the value
   n of the new field, introduced by 'ema' made it to the final graph
   as a value of field 'f' of the object 'o', traced by 'et' (o#f =
   n), then this value is going to be reported by expose_apex.  *)

Lemma expose_apex_fires l1 l2 et ema :
  let o := source ema in
  let f := fld    ema in
  let n := new    ema in
  p = l1 ++ et :: l2 -> ema \in l2 -> 
  kindMA (kind ema) -> kind et == T ->
  source et = o -> fld et = f -> o#f@g = n ->
  n \in expose_apex.
Proof.  
move=>/=E D Kma Kt S F N.
case: (prefix_wavefront e0 D E Kt)=>pre[H1]/wfp H2.
apply/mapP; exists (pre, ema)=>//=.
rewrite mem_filter -S -F H1 Kma -!(andbC true)/=; apply: H2.
by case/prefV: H1=>i[G1] G2 G3; exists i.
Qed.

(******************************************************************)
(*                 Correctness of expose_apex                     *)
(******************************************************************)

(* The following theorem states the soundness of the expose_apex
   procedure: it adds to the tracedTargets (retrieved from the
   T-entries) a set of objects, delivered by 'expose_apex', such that
   the union of the two contains the *actual targets* of all traced
   object-fields by the end of the log execution. *)

Theorem expose_apex_sound : 
  {subset actualTargets p g <= tracedTargets p ++ expose_apex}.
Proof.
move=>x/actualTargetsP=>[[et]][l1][l2][E]K Z; subst x.
rewrite mem_cat; apply/orP.
case: (traced_objects epf E K); [left | right].
- by apply/tracedTargetsP; exists et, l1, l2. 
case/hasP: b=>ema D/andP[K2]/andP[/eqP E2]/andP[/eqP E3]/eqP E4.
rewrite E2 E3 in E4 *;  rewrite E4.
by apply: (expose_apex_fires E D).
Qed.

End ApexAlgo.

Section ApexVanilla.

(* Runnin Apex with the defalut wavefront function *)

Variable e0 : LogEntry.
Variables (h0 : heap) (g0: graph h0) (p : log).
Variables (h : heap) (g: graph h).
Variable (epf : executeLog g0 p = Some (ExRes g)).

(* Indeed, this is trivially sound  *)

Corollary vanilla_expose_apex_sound : 
  {subset actualTargets p g
            <= tracedTargets p ++ expose_apex e0 p g wavefront}.
Proof. by apply: (expose_apex_sound e0 epf)=>l _. Qed.

End ApexVanilla.