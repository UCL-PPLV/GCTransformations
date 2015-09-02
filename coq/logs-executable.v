Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat.
Require Import Ssreflect.eqtype Ssreflect.ssrfun Ssreflect.seq.
Require Import MathComp.path.
Require Import Eqdep pred prelude idynamic ordtype pcm finmap unionmap heap coding. 
Require Import hgraphs.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 


(* Implementation of the mutator/collector logs and their execution *)
Section GCLog.

Inductive ActionKind : Set := T | M | A of nat.

Definition eq_kind k1 k2 := match (k1, k2) with
  | (T, T) => true
  | (M, M) => true
  | (A x, A y) => x == y
  | _ => false
  end.

Lemma eqkP : Equality.axiom eq_kind.
Proof.
do [case]; do?[constructor]=>//; do ?[by case; constructor].
move=>n; case; do?[constructor]=>//; rewrite /eq_kind.
move=>m; case X: (n == m).
by move/eqP: X=>X; subst m; constructor.
by constructor; case=>Z; subst m; move/eqP: X. 
Qed.

Canonical kind_eqMixin := EqMixin eqkP.
Canonical kind_eqType := Eval hnf in EqType ActionKind kind_eqMixin.

Definition kindMA k := match k with
  | M   => true
  | A _ => true
  | _   => false
  end.

Record LogEntry : Set := Entry {
  kind    : ActionKind;
  source  : ptr;
  fld     : nat;
  old     : ptr;
  new     : ptr }.

Definition eq_entry e1 e2 :=
  [&& (kind e1 == kind e2), (source e1 == source e2),
      (fld e1 == fld e2)  , (old e1 == old e2) & (new e1 == new e2)].

(* Well, this is super-boring. Can it be automated a la Haskell? *)
Lemma eqeP: Equality.axiom eq_entry.
Proof.
move=>e1 e2; rewrite /eq_entry.
case: e1; case: e2=>//==> k1 s1 f1 o1 n1 k2 s2 f2 o2 n2.
case X:(k2 == k1)=>/=; last by constructor; move/eqP:X=>X H; apply: X; case: H.
case Y:(s2 == s1)=>/=; last by constructor; move/eqP:Y=>Y H; apply: Y; case: H.
case Z:(f2 == f1)=>/=; last by constructor; move/eqP:Z=>Z H; apply: Z; case: H.
case U:(o2 == o1)=>/=; last by constructor; move/eqP:U=>U H; apply: U; case: H.
case V:(n2 == n1)=>/=; last by constructor; move/eqP:V=>V H; apply: V; case: H.
by constructor; move: X Y Z U V; do![move/eqP=>->].
Qed.

Canonical entry_eqMixin := EqMixin eqeP.
Canonical entry_eqType := Eval hnf in EqType LogEntry entry_eqMixin.

Definition log := seq LogEntry.

(* A set of pointers *)
Definition ptr_set := ptrmap_pcm_Encoded unit_st_Encoded.

End GCLog.

Section ExecuteLogs.

(* 

It reflect boolean condition into a certificate of type P via the
function g, and then uses the obtained certificate in the continuation
f. If the boolean check is failed, the result is undefined, hence both
the condK combinator and its argument f have the result type option.

*)
Definition condK P R (c : bool) 
  (g : is_true c -> P) (f : P -> option R) := 
  (if c as z return _ = z -> _ 
   then fun (efl : c = true) => f (g efl)
   else fun _ => None) (erefl _). 

Lemma condKE P R (c : bool) (g : is_true c -> P) (f : P -> option R) :
  c -> {pf | condK g f = f pf}.
Proof.
rewrite /condK=>X. 
by suff Z: c = true=>//; subst c; apply: exist.
Qed.

Lemma condK_true P R (c : bool) (g : is_true c -> P) (f : P -> option R) z :
  condK g f = Some z -> c.
Proof.
rewrite /condK; case Z: (c == true); first by move/eqP: Z=>Z; subst c. 
move/negbT: Z=>Z; have X: c = false by clear g; case: c Z.
by subst c.
Qed.

(*

The following function executeLog is partial and certified:

- If it returns None, then something must have gone wrong, because the
  log was malformed. 

- If the result is Some (h, g), then h is the resulting heap and g is
  its new graph certificate, which is threaded through the execution.

*)

Record ExecuteResult := ExRes {hp : heap; gp : graph hp}.

Fixpoint executeLog (h : heap) (g : graph h) (l : log) : 
    option ExecuteResult := match l with 

  (* Empty log - return heap and its graph certificate *)    
  | [::] => Some (ExRes g)

  (* Check for allocation with new graph certificate *)
  | (Entry (A fnum) x fld old y) :: ls => 
      condK (@allocG h g y fnum x fld old y) (fun g' => executeLog g' ls)

  (* Check for modification with new graph certificate *)
  | (Entry M x fld old new) :: ls =>
      condK (@modifyG h g x fld old new) (fun g' => executeLog g' ls)

  (* Tracing entry - do nothing, but enforce "sanity requirements" *)
  | (Entry T x fld old new) :: ls => 
      condK (@traceG h g x fld old new) (fun _ => executeLog g ls)
  end.


Lemma takeSn A n (a : A) l : take n.+1 (a :: l) = a :: (take n  l).
Proof. by []. Qed.

(* We can combing good logs transitively *)
Lemma replayLogCons h0 (g0: graph h0) x l h1 g1 h g:
    executeLog g0 [:: x] = Some {| hp := h1; gp := g1 |}
 -> executeLog g1 l = Some {| hp := h; gp := g |}
 -> executeLog g0 (x::l) = Some {| hp := h; gp := g |}.
Proof.
case: x=>k s f o nw; case: k=>/=[||n]; move=>E; move:(condK_true E)=> C H1.
- case: (condKE (traceG (new:=nw)) 
        (fun _ : trace g0 s f = h0 => Some {| hp := h0; gp := g0 |}) C)=>? E2.
  rewrite E2 in E; case: E=>Z; subst h1.
  have Eg: g0 = g1 by apply: (proof_irrelevance g0 g1). subst g1.
  by case: (condKE (traceG (new:=nw)) (fun _ => executeLog g0 l) C); rewrite H1.
- case: (condKE (modifyG g0 f (new:=nw))
        (fun pf => Some {| hp := (modify g0 s f nw); gp := pf |}) C)=>/=pg E2.
  rewrite E2 in E=>{E2}; case: pg E=>g' pg; case=>Z; subst h1; clear g'.
  case: (condKE (modifyG g0 f (new:=nw)) (fun pf => executeLog pf l) C)=>g'->.
  by rewrite -(proof_irrelevance g1 g') H1.
case: (condKE (allocG g0 n f (new:=nw))
        (fun pf => Some {| hp := alloc g0 nw n s f; gp := pf |}) C)=>/=pg E2.
rewrite E2 in E=>{E2}; case: pg E=>g' pg; case=>Z; subst h1; clear g'.
case: (condKE (allocG g0 n f (new:=nw)) 
      ((executeLog (h:=alloc g0 nw n s f))^~ l) C)=>g'->.
by rewrite -(proof_irrelevance g1 g') H1.
Qed.

(* By the way, the proofs are remarkably robust: almost nothing had to
be changed after refactoring of alloc! *)

(* We can reconstruct the intermediate graph for the cons *)
Lemma replayLogCons2 h0 (g0: graph h0) x l er : 
  executeLog g0 (x :: l) = Some er ->
  {er | let: (er1, er2) := er in 
        executeLog g0 [:: x] = Some er1 /\ 
        executeLog (gp er1) l = Some er2 }.
Proof.
case:er=>h g; case: x=>k s f o nw; case: k=>[||n];
move=>/=E; move:(condK_true E)=> C.
- apply: (exist _ (ExRes g0, ExRes g)); split=>//=.
  + by case: (condKE (traceG (new:=nw)) 
        (fun _ : trace g0 s f = h0 => Some {| hp := h0; gp := g0 |}) C). 
  by case: (condKE (traceG (new:=nw)) 
           (fun _ : trace g0 s f = h0 => executeLog g0 l) C)=>_<-. 
- case: (condKE (modifyG g0 f (new:=nw)) 
        (fun g' : _ => Some {| hp := modify g0 s f nw; gp := g' |}) C)=>g1 E2.
  apply: (exist _ (ExRes g1, ExRes g)); split=>//=.
  case: (condKE (modifyG g0 f (new:=nw)) 
        ((executeLog (h:=modify g0 s f nw))^~ l) C)=>g2 E3.
  by move: (proof_irrelevance g1 g2)=>Z; subst g2; rewrite -E3.
case: (condKE (allocG g0 n f (new:=nw))
       (fun g' : _ => Some {| hp := alloc g0 nw n s f; gp := g' |}) C)=>g1 E2.
apply: (exist _ (ExRes g1, ExRes g)); split=>//=.
case: (condKE (allocG g0 n f (new:=nw)) 
      ((executeLog (h:=alloc g0 nw n s f))^~ l) C)=>g2 E3.
by move: (proof_irrelevance g1 g2)=>Z; subst g2; rewrite -E3.
Qed.

(* [REM] All this business with inversion on the results via condKE
and condK_true should be automated somehow. What is the general
pattern? *)


Lemma replayLogRcons h0 (g0: graph h0) l e:
  {er | executeLog g0 (rcons l e) = Some er} ->
  {er | executeLog g0 l = Some er}.
Proof.
elim: l e h0 g0=>[e h0 g0|x l Hi e h0 g0 H]; last first.
- rewrite rcons_cons in H.
  case: H=>er /replayLogCons2[[er1 er2]][H1]H2.
  have X: {er : ExecuteResult | executeLog (gp er1) (rcons l e) = Some er}.
  - by apply: (exist _ er2).
  move: (Hi e _ (gp er1) X)=>{X}[]=>er3 H3.
  case: er1 H1 H2 H3=>h1 g1 H1; case: er3=>h2 g2 H2 H3; simpl in H2, H3.
  by move: (replayLogCons H1 H3)=>H4; apply: (exist _ (ExRes g2)). 

(* Base case is the interesting one *)
case=>[[h g]]/=; case: e=>k s f o nw; case: k=>[||n];
move=>E; move:(condK_true E)=> C.
- case: (condKE (traceG (new:=nw)) 
        (fun _ : trace g0 s f = h0 => Some {| hp := h0; gp := g0 |}) C)=>? E2.
  by rewrite E2 in E; apply: (exist _ (ExRes g)).
- case: (condKE (modifyG g0 f (new:=nw)) 
        (fun pf => Some {| hp := _; gp := pf |}) C)=>[pg E2].
  by rewrite E2 in E; apply: (exist _ (ExRes g0)). 
case: (condKE (allocG g0 n f (new:=nw)) 
      (fun g'=> Some {| hp := _; gp := g' |}) C)=>g' E2. 
by rewrite E2 in E; apply: (exist _ (ExRes g0)). 
Qed.

(* (* T-entries do not affect the execution *) *)
(* Lemma replayLogRconsT h0 (g0 : graph h0) l e h g h' g' :  *)
(*   executeLog g0 l = Some {| hp := h'; gp := g' |} -> *)
(*   executeLog g0 (rcons l e) = Some {| hp := h; gp := g |} -> *)
(*   kind e == T -> *)
(*   h = h' /\ nth null (fields g (source e)) (fld e) = (new e). *)
(* Proof. *)
(* case: e=>k s f o nw; case: k=>//=H1 H2 _. rewrite -cats1 in H2. *)
(* Search _ (rcons). *)

Lemma replayLogCat h0 (g0: graph h0) l1 l2 h g:
  executeLog g0 (l1 ++ l2) = Some (@ExRes h g) ->
  {er | executeLog g0 l1 = Some er}.
Proof.
elim/last_ind: l2 h g=>[h g|l2 e Hi h g H].
- by rewrite cats0; apply: (exist _ (ExRes g)).
rewrite -rcons_cat in H.
have X: {er | executeLog g0 (rcons (l1 ++ l2) e) = Some er}.
- by apply: (exist _ (ExRes g)).
by case/replayLogRcons: X=>[[h1 g1]]/Hi.
Qed.

(*******************************************************************************)
(* [Replaying logs]: the following certified definition is very
important, as it states that if a log (l) managed to deliver a graph
successfully, we can reconstruct heaps and graphs for *all* its
intermediate stages, expressed as (take n l).  *)
(*******************************************************************************)

Lemma replayLogLm h0 (g0: graph h0) l er:
  executeLog g0 l = Some er ->
  forall n, {er | executeLog g0 (take n l) = Some er}.
Proof.
move=>H n; case Y : (n < size l); last first.
- rewrite ltnNge in Y; move/negbFE: Y=>/take_oversize=>->. 
  by apply: (exist _ er).
rewrite -[l](cat_take_drop n) in H.
by case:er H=>h g /replayLogCat.
Qed.

(* The following is a certified function extracting an intermediate result *)
Definition replayLog h0 (g0: graph h0) l er
    (pf : executeLog g0 l = Some er) (n : nat) : ExecuteResult := 
  match replayLogLm pf n with exist er _ => er end.

Theorem replayLogReplays h0 (g0: graph h0) l er
    (pf : executeLog g0 l = Some er) (n : nat) :
  executeLog g0 (take n l) = Some (replayLog pf n). 
Proof. by rewrite /replayLog; case: (replayLogLm pf n). Qed.

End ExecuteLogs.

Section Wavefronts.

(* Definition of a wavefront *)
Definition wavefront (p : log) := 
  [seq (source pi, fld pi) | pi <- p & kind pi == T].

End Wavefronts.
