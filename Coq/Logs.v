From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep pred prelude idynamic ordtype pcm finmap unionmap heap coding. 
Require Import Hgraphs.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 


(*******************************************************************************)
(* Definitions of GC logs and entries with a number of proved facts
   about the effects different entries (e.g., of M/A-type) have on the
   execution of the log. In essence, these lemmas tie the "semantic"
   of the heap mutation and tracing (expressed in terms of
   heap-graphs) with the "syntactic" way of reasoning about it in
   terms of GC logs. *)
(*******************************************************************************)


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

(* Dereferencing an object field *)

Notation "o '#' f '@' g" := (nth null (fields g o) f)
  (at level 43, left associativity).



Section ExecuteLogs.

(* The following function boolean condition into a certificate of type
   P via the function g, and then uses the obtained certificate in the
   continuation f. If the boolean check is failed, the result is
   undefined, hence both the condK combinator and its argument f have
   the result type option.  *)

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

(* [TODO] Emphasize that in the following lemmas *overconstraining*
   lemmas allocG, modifyG and other didn't change the proofs! The
   complexity is all hidden in hgraphs.v file. *)

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
- case: (condKE (modifyG (new:=nw))
        (fun pf => Some {| hp := (modify g0 s f nw); gp := pf |}) C)=>/=pg E2.
  rewrite E2 in E=>{E2}; case: pg E=>g' pg; case=>Z; subst h1; clear g'.
  case: (condKE (modifyG (new:=nw)) (fun pf => executeLog pf l) C)=>g'->.
  by rewrite -(proof_irrelevance g1 g') H1.
case: (condKE (allocG n (new:=nw))
        (fun pf => Some {| hp := alloc g0 nw n s f; gp := pf |}) C)=>/=pg E2.
rewrite E2 in E=>{E2}; case: pg E=>g' pg; case=>Z; subst h1; clear g'.
case: (condKE (allocG n (new:=nw)) 
      ((executeLog (h:=alloc g0 nw n s f))^~ l) C)=>g'->.
by rewrite -(proof_irrelevance g1 g') H1.
Qed.

(* By the way, the proofs are remarkably robust: almost nothing had to
be changed after refactoring of alloc! *)

(* We can reconstruct the intermediate graph for the cons *)
Lemma replayLogCons2 h0 (g0: graph h0) x l h g : 
  executeLog g0 (x :: l) = Some {| hp := h; gp := g |} ->
  exists h1 g1, 
     executeLog g0 [:: x] = Some {| hp := h1; gp := g1 |} /\
     executeLog g1 l = Some {| hp := h; gp := g |}.
Proof.
case: x=>k s f o nw; case: k=>[||n];
move=>/=E; move:(condK_true E)=> C.
- exists h0, g0; split=>//=.
  + by case: (condKE (traceG (new:=nw)) 
        (fun _ : trace g0 s f = h0 => Some {| hp := h0; gp := g0 |}) C). 
  by case: (condKE (traceG (new:=nw)) 
           (fun _ : trace g0 s f = h0 => executeLog g0 l) C)=>_<-. 
- case: (condKE (modifyG (new:=nw)) 
        (fun g' : _ => Some {| hp := modify g0 s f nw; gp := g' |}) C)=>g1 E2.
  exists _, g1; split=>//=.
  case: (condKE (modifyG (new:=nw)) 
        ((executeLog (h:=modify g0 s f nw))^~ l) C)=>g2 E3.
  by move: (proof_irrelevance g1 g2)=>Z; subst g2; rewrite -E3.
case: (condKE (allocG n (new:=nw))
       (fun g' : _ => Some {| hp := alloc g0 nw n s f; gp := g' |}) C)=>g1 E2.
exists _, g1; split=>//=.
case: (condKE (allocG n (new:=nw)) 
      ((executeLog (h:=alloc g0 nw n s f))^~ l) C)=>g2 E3.
by move: (proof_irrelevance g1 g2)=>Z; subst g2; rewrite -E3.
Qed.

(* [REM] All this business with inversion on the results via condKE
and condK_true should be automated somehow. What is the general
pattern? *)


Lemma replayLogRcons h0 (g0: graph h0) l e h (g : graph h):
  executeLog g0 (rcons l e) = Some {| hp := h; gp := g |} ->
  exists h1 g1, 
     executeLog g0 l = Some {| hp := h1; gp := g1 |} /\ 
     executeLog g1 [:: e] = Some {| hp := h; gp := g |}.
Proof.
elim: l h g e h0 g0=>[h g e h0 g0|x l Hi h g e h0 g0 H]; last first.
- rewrite rcons_cons in H.
  move: H=>/replayLogCons2=>[[h1][g1]][H1]H2.
  case (Hi _ _ _ _ _ H2)=>h3[g3][H3]H4.  
  by move: (replayLogCons H1 H3)=>H5; exists h3, g3. 
   
(* Base case is the interesting one *)
case: e=>k s f o nw; case: k=>/=[||n] E; move:(condK_true E)=> C.
- case: (condKE (traceG (new:=nw)) 
        (fun _ : trace g0 s f = h0 => Some {| hp := h; gp := g |}) C)=>? E2.
  by exists h0, g0. 
- case: (condKE (modifyG (new:=nw)) 
        (fun pf => Some {| hp := _; gp := pf |}) C)=>[pg E2].
  by exists h0, g0. 
case: (condKE (allocG n (new:=nw)) 
      (fun g'=> Some {| hp := _; gp := g' |}) C)=>g' E2. 
by exists h0, g0. 
Qed.

Lemma replayLogRcons2 h0 (g0: graph h0) l e h (g : graph h) h1 (g1: graph h1):
  executeLog g0 l = Some {| hp := h1; gp := g1 |} ->
  executeLog g1 [:: e] = Some {| hp := h; gp := g |} ->
  executeLog g0 (rcons l e) = Some {| hp := h; gp := g |}.
Proof.
move=>H1 H2.
elim: l e h0 g0 H1 H2=>//.
- move=>e h0 g0; case=>Z; subst h1; rewrite [rcons _ _]/=.
  by rewrite (proof_irrelevance g0 g1).
move=>x l Hi e h0 g0.
rewrite rcons_cons.
move/replayLogCons2=>[h2][g2][E]S H2.
move: (Hi e h2 g2 S H2)=>H. 
by apply: (@replayLogCons _ g0 x (rcons l e) _ g2 _ g E H).
Qed.

Lemma replayLogCat h0 (g0: graph h0) l1 l2 h g:
  executeLog g0 (l1 ++ l2) = Some (@ExRes h g) ->
  exists er, executeLog g0 l1 = Some er.
Proof.
elim/last_ind: l2 h g=>[h g|l2 e Hi h g H].
- by rewrite cats0; exists (ExRes g).
rewrite -rcons_cat in H.
by case/replayLogRcons: H=>h1[g1][]/Hi.
Qed.

Lemma replayLogCat2 h0 (g0: graph h0) l1 l2 h g:
  executeLog g0 (l1 ++ l2) = Some {| hp := h; gp := g |} ->
  exists h1 g1,
    executeLog g0 l1 = Some{| hp := h1; gp := g1 |} /\
    executeLog g1 l2 = Some{| hp := h; gp := g |}.
Proof.
    move => ex; move: (replayLogCat ex)=>[[h' g']] ex_pref; exists h', g'.
    split =>//; rewrite -ex; move: ex; elim/last_ind: l2 h g.
    rewrite cats0 => h g ex_init; rewrite {1}/executeLog sym =>//.
    move => s x hyp h g; rewrite -rcons_cat.
    move => ex; case: (replayLogRcons ex) => h1. case => g1;
    case => ex' ex_rcon; move: (hyp h1 g1 ex') => f.
    rewrite -f in ex'; rewrite (replayLogRcons2 ex' ex_rcon) ex =>//.
Qed.

(* The size of fields in an existing object doesn't change *)

Lemma fsize_preserv h0 (g0: graph h0) l1 l2 h g h' g' o:
  o \in dom h' ->
  executeLog g0 l1 = Some (@ExRes h' g') ->
  executeLog g0 (l1 ++ l2) = Some (@ExRes h g) ->
  size (fields g' o) = size (fields g o) /\
  o \in dom h.
Proof.
move=>D H1; elim/last_ind:l2 h g=>[h g|l2 e Hi h g].
- by rewrite cats0 H1; case=>Z; subst h'; rewrite (proof_irrelevance g' g).
rewrite -rcons_cat=>/replayLogRcons[h1][g1][/(Hi h1 g1)][->]{Hi g' H1 D h'}D. 
case: e=>k s f o' nw; case: k=>//=[||n]/=E; move:(condK_true E)=> C.
- case: (condKE (traceG (new:=nw)) 
        (fun _  => Some {| hp := h1; gp := g1 |}) C)=>? E2.
  by rewrite E2 in E; case: E=>Z; subst h1; rewrite (proof_irrelevance g1 g).
- case: (condKE (modifyG (new:=nw)) 
        (fun pf => Some {| hp := _; gp := pf |}) C)=>[pg E2].
  rewrite E2 in E; case: E=>E{E2 pg}; subst h.
  case /and3P: C; move=> s_nw_dom f_in_sz;  move /andP;  case.
  move => o_val_valid; move: (conj f_in_sz o_val_valid).
  move /andP => second_part; move: (conj s_nw_dom second_part).
  move /andP => C'.
  by rewrite (modify_size g o C') -(modifyDom g1 s f nw).
case: (condKE (allocG n (new:=nw)) 
      (fun g'=> Some {| hp := _; gp := g' |}) C)=>g' E2. 
rewrite E2 in E; case: E=>Z; subst h.      
rewrite eqxx /= -(andbC true)/= in C.
  case /and3P: C; move=> s_nw_dom f_in_sz;  move /andP;  case.
  move => o_val_valid; move: (conj f_in_sz o_val_valid).
  move /andP => second_part; move: (conj s_nw_dom second_part).
  move /andP => C'.
rewrite (alloc_size g C' D); split=>//.
by move/(allocDom g1 nw n s f): D.
Qed.

(*******************************************************************************)
(* [Replaying logs]: the following certified definition is very
important, as it states that if a log (l) managed to deliver a graph
successfully, we can reconstruct heaps and graphs for *all* its
intermediate stages, expressed as (take n l).  *)
(*******************************************************************************)

Lemma replayLogP h0 (g0: graph h0) l er:
  executeLog g0 l = Some er ->
  forall n, exists er, executeLog g0 (take n l) = Some er.
Proof.
move=>H n; case Y : (n < size l); last first.
- rewrite ltnNge in Y; move/negbFE: Y=>/take_oversize=>->. 
  by exists er.
rewrite -[l](cat_take_drop n) in H.
by case:er H=>h g /replayLogCat.
Qed.


(*******************************************************************************)
(*                Entry-specific lemmas about log executions                   *)
(*******************************************************************************)


(* T-entries do not affect the execution *)

Lemma replayLogRconsT h0 (g0 : graph h0) l e h g :
  executeLog g0 (rcons l e) = Some {| hp := h; gp := g |} ->
  kind e == T ->
  [/\ executeLog g0 l = Some {| hp := h; gp := g |}, 
      nth null (fields g (source e)) (fld e) = (new e) &
      fld e < size (fields g (source e))].
Proof.
case: e=>k s f o nw; case: k=>//= H2 _.
move/replayLogRcons: H2=>[h1][g1][H3]/= E.
move:(condK_true E)=>C.
case: (condKE (traceG (new:=nw)) 
   (fun _ : _ => Some {| hp := h1; gp := g1 |}) C)=>? E2.
rewrite E2 in E. 
case: E=>Z; subst h1.
rewrite (proof_irrelevance g g1).
case/andP: (C)=>/andP=>[[G]]/eqP Z1 /andP [G'] /eqP Z2.
by subst nw o.  
Qed.

(* An entry that can affect the value of s.f in the final graph. *)

Definition matchingMA s f := fun ema =>
  [&& kindMA (kind ema), s == source ema & f == fld ema].


(* The entry 'e', which doesn't modify a value of the field 'f' of
   object 'o' doesn't affect the value of o.f in the final graph. *)

Lemma replayLogRconsMA_neg h0 (g0 : graph h0) l e s f h g :
  executeLog g0 (rcons l e) = Some {| hp := h; gp := g |} ->
  ~~ matchingMA s f e ->
  exists h' g', 
    executeLog g0 l = Some {| hp := h'; gp := g' |} /\ 
    nth null (fields g s) f = nth null (fields g' s) f.
Proof.
case/replayLogRcons=>h1[g1][H1]H2 M; exists h1, g1; split=>//.
case: e M H2=>k s' f' o n; rewrite /matchingMA/=; case: k=>//=[_|H2|fnum H2];
move=>E; move:(condK_true E)=>C.
(* Trace *)
- case: (condKE (traceG (new:=n)) 
     (fun _ : _ => Some {| hp := h1; gp := g1 |}) C)=>? E2.
  by rewrite E2 in E; case: E=>Z; subst h1; rewrite (proof_irrelevance g g1).
(* Modify *)
- case: (condKE (modifyG (new:=n))
        (fun g' : _ => Some {|hp := modify g1 s' f' n; gp := g'|}) C)=>g' E2.
  rewrite E2 in E; case: E=>Z; subst h. 
  case /and3P: C; move=> s_nw_dom f_in_sz;  move /andP;  case.
  move => o_val_valid; move: (conj f_in_sz o_val_valid).
  move /andP => second_part; move: (conj s_nw_dom second_part).
  move /andP => C'.
  by move: (modify_field g s f C'); move/negbTE: H2=>->.
(* Allocate *)
case: (condKE (allocG fnum (new:=n)) (fun g' : _ =>
       Some {| hp := alloc g1 n fnum s' f'; gp := g' |}) C)=>g' E2.
rewrite E2 in E; case: E=>Z; subst h. 
rewrite eqxx [_ && true]andbC /= in C.
  case /and3P: C; move=> s_nw_dom f_in_sz;  move /andP;  case.
  move => o_val_valid; move: (conj f_in_sz o_val_valid).
  move /andP => second_part; move: (conj s_nw_dom second_part).
  move /andP => C'.
by move: (alloc_field g s f C'); move/negbTE: H2=>->.
Qed.

Lemma replayLogRconsMA h0 (g0 : graph h0) l e s f h g :
  executeLog g0 (rcons l e) = Some {| hp := h; gp := g |} ->
  matchingMA s f e ->
  exists h' g', 
    executeLog g0 l = Some {| hp := h'; gp := g' |} /\ 
    nth null (fields g s) f = new e.
Proof.
case/replayLogRcons=>h1[g1][H1]H2 M; exists h1, g1; split=>//.
case: e M H2=>k s' f' o n; rewrite /matchingMA/=; case: k=>//=[H2|fnum H2];
move=>E; move:(condK_true E)=>C;
case/andP: H2=>/eqP Z1/eqP Z2; subst s' f'.
- case: (condKE (modifyG (new:=n))
        (fun g' : _ => Some {|hp := modify g1 s f n; gp := g'|}) C)=>g' E2.
  rewrite E2 in E; case: E=>Z; subst h. 
  case /and3P: C; move=> s_nw_dom f_in_sz;  move /andP;  case.
  move => o_val_valid; move: (conj f_in_sz o_val_valid).
  move /andP => second_part; move: (conj s_nw_dom second_part).
  move /andP => C'.
  move: (@modify_field _ _ s f n o g s f C').
  by rewrite !eqxx/= leqNgt =>->; case/andP: C'=>_/andP[->]/=.
case: (condKE (allocG fnum (new:=n))
        (fun g' : _ =>
         Some {| hp := alloc g1 n fnum s f; gp := g' |}) C)=>g' E2.
rewrite E2 in E; case: E=>Z; subst h. 
rewrite eqxx -(andbC true) /= in C.
  case /and3P: C; move=> s_nw_dom f_in_sz;  move /andP;  case.
  move => o_val_valid; move: (conj f_in_sz o_val_valid).
  move /andP => second_part; move: (conj s_nw_dom second_part).
  move /andP => C'.
move: (alloc_field g s f C'); rewrite !eqxx/= leqNgt =>->.
by case/andP: C'=>_/andP[->].
Qed.

(*******************************************************************************)
(*            Lemmas about different entries and their configurations          *)
(*******************************************************************************)

Lemma in_split {A : eqType} e (l : seq A): 
  e \in l <-> exists l1 l2, l = l1 ++ e :: l2.
Proof.
split=>[|[l1][l2]->]; last first.
- by rewrite mem_cat orbC inE eqxx.
elim:l=>//x xs Hi; rewrite inE/=; case/orP.
- by move/eqP=>Z; subst x; exists [::], xs; rewrite cat0s.
by case/Hi=>l1[l2]->; exists (x :: l1), l2. 
Qed.

(* Initial graph an heap *)
Variables (h0 : heap) (g0: graph h0).

(* [trace_pure]: If there is no matching MA-entries for the T-entry
   'et' in the corresponding suffix of 'l', then et's recorded value
   survives till the final graph. *)

Lemma trace_pure l h' (g' : graph h') et l1 l2: 
  kind et == T -> 
  executeLog g0 l = Some {| hp := h'; gp := g' |} ->
  ~~ has (matchingMA (source et) (fld et)) l2 -> 
  l = l1 ++ et :: l2 -> 
  source et # fld et @ g' = new et.
Proof.
move=>Kt; elim/last_ind:l2 l l1 h' g'=>
  [l l1 h' g' pf _|l2 e Hi l l1 h' g' H1 H2].
- by rewrite cats1=>Z; subst l; case: (replayLogRconsT pf Kt).
rewrite has_rcons negb_or in H2; case/andP: H2=>H2 H3.
rewrite -cats1 -cat_rcons catA cats1 cat_rcons. 
set l' := (l1 ++ et :: l2)=>H4; subst l.
case: (replayLogRconsMA_neg H1 H2)=>h1[g1][H5]E; rewrite E.
move/eqP: (eq_refl l'); rewrite {2}/l'=>H6.
by apply: (Hi _ _ _ _ H5 H3 H6).
Qed.

(* The following lemma states that if there is an object in the suffix
   l2 of the log, which altered the field 'f' of the object 'o', then
   there is such entry, whose contributed value has actually survived
   till the final graph g'.  *)

Lemma pickLastMAInSuffix' l l1 l2 h' (g' : graph h') o f:
  l = l1 ++ l2 ->
  executeLog g0 l = Some {| hp := h'; gp := g' |} ->
  has (matchingMA o f) l2 ->
  exists ema l3 l4, 
     [&& matchingMA o f ema, o#f@g' == new ema, l2 == l3 ++ ema :: l4 &
         ~~ has (matchingMA o f) l4].
Proof.
elim/last_ind: l2 l h' g'=>//ls e Hi l h' g' E H1 H2.
rewrite !has_rcons in H2 *; rewrite -rcons_cat in E; subst l.
case X: [&& kindMA (kind e), o == source e & f == fld e]; last first.

(* First case: the last entry not a matching one *)
- move/negbT: X; rewrite negb_and. 
  case G: (~~ kindMA (kind e))=>//=.

  (* (a) It is a T-entry => by induction hypothesis *) 
  + move=>_; have T: kind e == T by case: (kind e) G.
    case: (replayLogRconsT H1 T)=>H3 H4 H4'.
    move/eqP: T=>T; rewrite /matchingMA T /=  in H2 Hi *.
    case: (Hi _ _ _ (erefl (l1 ++ ls)) H3 H2)=>ema[l3][l4]/andP[M].
    case/andP=>M1/andP[M2]M3; exists ema, l3, (rcons l4 e).
    rewrite M M1 /= andbC/=; move/eqP:M2=>->. 
    rewrite rcons_cat rcons_cons eqxx has_rcons negb_or M3 -!(andbC true)/=.
    by move/negbTE: G=>->. 

(* (b) It's and MA-entry with different source/field *)
- move=>G1; have K : (kindMA (kind e)) by move/negbFE: G.
  rewrite /matchingMA K (negbTE G1)/= in H2 Hi *. 
  have N: ~~ matchingMA o f e by rewrite /matchingMA K.
  case: (replayLogRconsMA_neg H1 N)=>h1[g1][H3]E.
  case: (Hi _ _ _ (erefl (l1 ++ ls)) H3 H2)=>ema[l3][l4]/andP[M].
  case/andP=>M1/andP[M2]M3; exists ema, l3, (rcons l4 e).
  rewrite M E M1/=; move/eqP:M2=>->. 
  rewrite rcons_cat rcons_cons eqxx has_rcons negb_or M3 -!(andbC true)/=.
  by move/negbFE: G=>->/=. 

(* Now we have a matching entry, which actually contributes. *)
case: (replayLogRconsMA H1 X)=>h1[g1][G1]E.
by exists e, ls, [::]; rewrite /matchingMA X E cats1/= !eqxx.
Qed.


Lemma pickLastMAInSuffix l l1 l2 h' (g' : graph h') o f:
  l = l1 ++ l2 ->
  executeLog g0 l = Some {| hp := h'; gp := g' |} ->
  has (fun e => [&& kindMA (kind e), o == source e & f == fld e]) l2 ->
  has (fun e => [&& kindMA (kind e), o == source e,  f == fld e & 
                    o#f@g' == new e]) l2.
Proof.
move=>E H1 H2.
case: (pickLastMAInSuffix' E H1 H2)=>e[l3][l4].
case/andP=>M1/andP[M2]/andP[M3]M4; apply/hasP; exists e.
- by apply/in_split; exists l3, l4; apply/eqP.
by rewrite M2 -!(andbC true).
Qed.

Require Import Coq.Logic.Classical_Prop.

Lemma existsMAInSufix l h' (g' : graph h') o f:
    executeLog g0 l = Some {| hp := h'; gp := g'|} ->
    ~~ (o#f@g0 == o#f@g') ->
    exists ema l1 l2, [&& matchingMA o f ema, new ema == o#f@g',
        l == l1 ++ ema::l2 & ~~ has (matchingMA o f) l2].
Proof.
    move => execute field_changed.
    suff D: has (matchingMA o f) l.
    remember (Nil entry_eqType) as emp.
    have eq: l = emp ++ l.
    by rewrite Heqemp cat0s.
    move: (pickLastMAInSuffix' eq execute D).
    case=> ema'; case=> l1'; case=> l2'  hasMA.
    exists ema'; exists l1'; exists l2'.
    move: hasMA; move /and4P; case.
    move =>t1 t2 t3 t4.
    apply/andP. apply conj. exact t1. apply /andP.
    apply conj; move: t2; move /eqP /sym /eqP. done.
    move => t2. apply /andP. by apply conj.
    apply contraT => notHasMa.
    suff D: o # f @ g0 == o # f @ g'.
    move: D; move: field_changed; move /negbTE => D; rewrite D=>//.
    move: execute notHasMa; move:field_changed => _.
    elim/last_ind: l o f h' g' g0 => [o f h' g' g1 | l x ].
    rewrite /executeLog; case; move => h_eq matchMA.
    move: (eqG g1 g' o) => eq_fld; move: (eq_fld h_eq).
    move => flds; rewrite -flds =>//.
    move  => C o f h' g' g1 exec no_ma.
    move: (eqG g1 g0 o).
    suff P: h0 = h0.  Focus 2. done.
    move => fld.
    move: (fld P) => flds_eq; rewrite flds_eq; move: P fld => _ _.
    rewrite has_rcons in no_ma; move: no_ma; move /orP /not_or_and.
    case; move /negP => not_x;  move /negP => not_l.
    move: (replayLogRconsMA_neg exec not_x).
    case. move => h2; case; move => g2; case;
    move => exec_l;  move: (C o f h2 g2 g1 exec_l not_l).
    rewrite flds_eq; move => t1 t2;  move: t1;  rewrite t2 =>//.
Qed.

Lemma oldSignificance ema l h (g : graph h) :
    kindMA (kind ema) ->
    executeLog g0 (rcons l ema) = Some {| hp := h; gp := g |} ->
    exists h1 (g1: graph h1), ((source ema) # (fld ema) @ g1 = old ema /\
    executeLog g0 l = Some {| hp := h1; gp := g1 |}).
Proof.
    move => kind_ema ex.
    move: (replayLogRcons ex); case => h1; case => g1.
    case => ex_prefix ex_rcon; exists h1, g1; split =>//.
    move: ex_rcon.
    rewrite /executeLog.
    move: kind_ema.
    case ema => k s f o n.
    rewrite /matchingMA/=.
    case: k=>//=[H2|fnum H2].
    move=>E; move:(condK_true E); move /and4P; case => _ _ _ /eqP =>//.
    move=>E; move:(condK_true E); move /and4P; case => _ _ _ /eqP =>//.
Qed.

(* The following lemma states that for any T-entry, its captured
   o.f-value is either in the graph, or there exists an MA-antry
   *behind* it in the log, which overrides the value of o.f. *)

Lemma traced_objects h (g : graph h) l
                     (epf : executeLog g0 l = Some (ExRes g)) et l1 l2 :
  let o := source et in
  let f := fld    et in
  let n := new    et in
  l = l1 ++ et :: l2 -> kind et == T -> 
  o#f@g = n \/
  has (fun e => [&& kindMA (kind e), o == source e, f == fld e & 
                    o#f@g == new e]) l2.
Proof.
move=>/= E Kt.
case H: (has (matchingMA (source et) (fld et)) l2); [right|left]; last first.
- by apply: (@trace_pure l h g et l1 l2 Kt epf)=>//; apply/negbT.
rewrite /matchingMA in H *; rewrite -cat_rcons in E. 
by apply: (pickLastMAInSuffix E epf H).
Qed.

(* And alternative lemma with more refined conclusion *)
Lemma traced_objects' h (g : graph h) l
                     (epf : executeLog g0 l = Some (ExRes g)) et l1 l2 :
  let o := source et in
  let f := fld    et in
  let n := new    et in
  l = l1 ++ et :: l2 -> kind et == T -> 
  o#f@g = n \/
  exists ema l3 l4, 
     [&& matchingMA o f ema, o#f@g == new ema, l2 == l3 ++ ema :: l4 &
         ~~ has (matchingMA o f) l4].
Proof.
move=>/= E Kt.
case H: (has (matchingMA (source et) (fld et)) l2); [right|left]; last first.
- by apply: (@trace_pure l h g et l1 l2 Kt epf)=>//; apply/negbT.
rewrite /matchingMA in H *; rewrite -cat_rcons in E. 
by apply: (pickLastMAInSuffix' E epf H).
Qed.

Lemma trace_fsize l h' (g' : graph h') et l1 l2: 
  executeLog g0 l = Some {| hp := h'; gp := g' |} ->
  kind et == T -> 
  l = l1 ++ et :: l2 -> 
  fld et < size (fields g' (source et)).
Proof.
move=>H Kt; rewrite -cat_rcons=>E; subst l.
case: (replayLogCat H)=>[[h1 g1]]H1.
suff D: source et \in dom h1 /\ fld et < size (fields g1 (source et)).
by case: D=> D1 D2; case: (fsize_preserv D1 H1 H)=><- _.
clear H h' g' l2; case: et Kt H1=>k s f o nw; case: k=>//= _. 
case/replayLogRcons=>/=h[g][H1] E; move:(condK_true E)=> C.
case: (condKE (traceG (new:=nw)) 
      (fun _ : _ => Some {| hp := h; gp := g |}) C)=>? E2.
rewrite E2 in E; case: E=>Z {E2}; subst h1; rewrite (Heaps.prelude.proof_irrelevance g1 g).
by case/andP: C=>/andP[]->_/andP[->].
Qed.


(******************************************************************)
(*   Definitions of traced object, fields, and actual objects     *)
(******************************************************************)

(* A collector log p will all unique entires *)
Variables  (p : log).

(* Final heap and graph for the log p with the corresponding certificate epf *)
Variables (h : heap) (g: graph h).
Variable (epf : executeLog g0 p = Some (ExRes g)).

(* Collect all traced objects from the log *)
Definition tracedEntries : seq LogEntry :=
  [seq pi <- p | (kind pi) == T]. 

Definition tracedObjFields := 
  [seq (source et, fld et) | et <- tracedEntries].

Definition alreadyMarked :=
  [seq new et | et <- tracedEntries].

(* Next, we define the set of actual objects in the final heap-graph
   with respect to traced objects. *)

Definition needToBeMarked : seq ptr := 
  [seq (pf.1)#(pf.2)@g | pf <- tracedObjFields].

Lemma tracedEntriesP e: e \in tracedEntries <->
  kind e == T /\ exists l1 l2, p = l1 ++ e :: l2.
Proof.
split=>[|[H][l1][l2]E]. 
- rewrite /tracedEntries mem_filter=>/andP[->]H; split=>//.
  by apply/in_split.
rewrite /tracedEntries mem_filter H/= E.
by rewrite mem_cat inE eqxx orbC.
Qed.

Lemma tracedObjFieldsP sf: sf \in tracedObjFields ->
  exists et l1 l2, 
  [/\ (source et, fld et) = sf, p = l1 ++ et :: l2 & kind et == T].
Proof.
case/mapP=>et/tracedEntriesP[H1][l1][l2]H2 H3; subst sf.
by exists et, l1, l2.
Qed.

Lemma alreadyMarkedP x : x \in alreadyMarked <->   
  exists et l1 l2, 
  [/\ p = l1 ++ et :: l2, kind et == T & x = new et].
Proof.
split=>[|[et][l1][l2][E]K N].
- case/mapP=>et/tracedEntriesP[H1][l1][l2]H2 H3; subst x.
  by exists et, l1, l2.
apply/mapP; exists et=>//.
by apply/tracedEntriesP; split=>//; exists l1, l2.
Qed.

Lemma needToBeMarkedP x : x \in needToBeMarked ->   
  exists et l1 l2, 
  [/\ p = l1 ++ et :: l2, kind et == T & x = (source et)#(fld et)@g].
Proof.
case/mapP=>xf H Z; subst x.
case/tracedObjFieldsP: H=>et[l1][l2][H1]H2 H3; subst xf.
by exists et, l1, l2.
Qed.


End ExecuteLogs.

