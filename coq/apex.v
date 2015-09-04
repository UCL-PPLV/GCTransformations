Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat.
Require Import Ssreflect.eqtype Ssreflect.ssrfun Ssreflect.seq.
Require Import MathComp.path.
Require Import Eqdep pred idynamic ordtype pcm finmap unionmap heap coding. 
Require Import hgraphs logs.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Section ApexAlgo.

(* Initial graph an heap *)
Variables (h0 : heap) (g0: graph h0).

(* A collector log p will all unique entires *)
Variables  (p : log).

(* Final heap and graph for the log p with the corresponding certificate epf *)
Variables (h : heap) (g: graph h).
Variable (epf : executeLog g0 p = Some (ExRes g)).

(* Dereferencing an object field *)
Notation "o '#' f '@' g" := (nth null (fields g o) f)
  (at level 43, left associativity).

(******************************************************************)
(*    Auxiliary functions for log processing and fact about them  *)
(******************************************************************)

(* An auxiliary function that generates all prefixes for elements of a
list l0 *)

Fixpoint zip_num' (l : log) n :=
  match l with
  | [::]  => [::]
  | e::l' => (e, n) :: zip_num' l' (n.+1)
  end.

Definition zip_num l := zip_num' l 0.

Fixpoint prefs_els_rec (l0 l : log) n := 
  match l with 
  | [::]  => [::]
  | e::l' => (take n l0, e, n) :: prefs_els_rec l0 l' (n.+1)
  end.

Definition prefs_els l := prefs_els_rec l l 0.
 
Lemma prefs_take1' l: forall pr e n,
  (pr, e, n) \in (prefs_els_rec l l (size l - size l)) ->
  (size l <= size l) -> 
  (pr = take n l).
Proof.
elim/list_ind: l {-2 4 5}l=>// x xs Hi l pr e n/= D H.
rewrite !inE /=in D; case/orP: D; first by case/eqP=>Z1 Z2 Z3; subst pr e n. 
by rewrite subnSK// =>G; apply: (Hi _ _ _  _ G); apply: ltnW.
Qed.

Lemma prefs_take1 l pr e n:
   (pr, e, n) \in prefs_els l -> pr = take n l.
Proof.
move=>H. 
have N: forall n, n - n = 0 by elim.
have X: (pr, e, n) \in (prefs_els_rec l l (size l - size l)).
- by rewrite N. 
by apply: (prefs_take1' X); apply: leqnn.
Qed.


(* Default log entry *)
Variable e0 : LogEntry.

(* An alternative definition of a log decomposition procedure *)
Fixpoint prefixes_rec (l : log) n := 
  if n is n'.+1 then (take n' l, nth e0 l n', n') :: prefixes_rec l n' else [::].
Definition prefixes l := prefixes_rec l (size l).

(* Some properties of our selector function "prefixes". *)
Lemma take_nth_drop (n : nat) s:
  n < size s ->
  take n s ++ (nth e0 s n) :: drop n.+1 s = s.
Proof.
elim: s n => [|x s IHs] [|n]=>//=[_|]; first by rewrite drop0.
rewrite -[n.+1]addn1 -[(size s).+1]addn1 ltn_add2r=>/IHs=>H.
by rewrite addn1 -{4}H.
Qed.

(* Adequacy of prefixes *)

Lemma in_prefixes_full l e pr i: (pr, e, i) \in prefixes l ->
  [/\ i < size l, nth e0 l i = e & pr = take i l].
Proof.
rewrite /prefixes.
elim: (size l)=>//=n Hi.
case/orP; last first.
- by case/Hi=>H1 H2; split=>//; apply: (ltn_trans H1); apply:ltnSn.
by case/eqP=>Z1 Z2 Z3; subst pr e i.
Qed.

Lemma in_prefixes l e pr i: (pr, e, i) \in prefixes l -> e \in l.
Proof.
case/in_prefixes_full=>H1 H2.
have X: exists2 j, j < size l & nth e0 l j = e by exists i=>//.
by move/nthP: X.
Qed.

Lemma prefixes_in' l e j n : 
  e \in l -> j < n -> nth e0 l j = e ->
  (take j l, e, j) \in prefixes_rec l n.
Proof.
elim: n=>//=n Hi H1 H2 H3; case B: (j == n).
- by move/eqP: B=>B; subst j; rewrite inE H3 eqxx.
have X: j < n by rewrite ltnS leq_eqVlt B/= in H2.
by rewrite inE; move:(Hi H1 X H3)=>->; rewrite orbC.
Qed.

Lemma prefixes_in l e: e \in l -> 
  exists i, (take i l, e, i) \in prefixes l.
Proof.
by move=>D; case/(nthP e0): (D)=>j H1 H2; exists j; apply: prefixes_in'.
Qed.

Lemma prefixes_num' l j n  : 
  j < n -> n <= size l -> exists e, (take j l, e, j) \in prefixes_rec l n.
Proof.
elim: n=>//=n Hi H1 H2; case B: (j == n); last first.
- have X: j < n by rewrite ltnS leq_eqVlt B/= in H1.
  have Y: n <= size l by apply:ltnW. 
  by case: (Hi X Y)=>e G; exists e; rewrite inE G orbC.
move/eqP: B=>B; subst j=>{H1 Hi}.
exists (nth e0 l n).
by rewrite inE eqxx.
Qed.

Lemma prefixes_num l n  : 
  n < size l -> exists e, (take n l, e, n) \in prefixes l.
Proof.
by move/(@prefixes_num' l n (size l))=>H; apply:H; apply:leqnn.
Qed.

Lemma prefV l pr e n:
  (pr, e, n) \in prefixes l -> 
  [/\ pr = take n l, 
      e = (nth e0 l n) & 
      l = pr ++ e :: drop n.+1 l].
Proof.
move=>H; case: (in_prefixes_full H)=>G1 G2 G3.
by rewrite G3 -G2; split=>//; move: (take_nth_drop G1)=>->.
Qed.

Lemma prefix_rev l1 l2 l et e :
  e \in l2 -> l = l1 ++ et :: l2  ->
  exists i, (take i l, e, i) \in prefixes l /\ et \in take i l.
Proof.
case/splitP=>{l2}l2 l3.
rewrite -cat_cons -cats1 cat_cons -catA cat1s -cat_cons catA.
set i := size (l1 ++ et :: l2); move=>E; exists i.
have X1 : e \in l by rewrite E mem_cat inE eqxx orbC.  
have X2: i < size l
  by rewrite/i E!size_cat -addnA ltn_add2l -{1}[size (_::l2)]addn0 ltn_add2l. 
have Y: forall a, a - a = 0 by elim.
have X3: nth e0 l i = e by rewrite E nth_cat /i ltnn Y/=. 
move: (prefixes_in' X1 X2 X3)=>H; split=>//.
by rewrite E take_size_cat /i// mem_cat inE eqxx orbC.
Qed.

Lemma prefix_wavefront l1 l2 l et e :
  e \in l2 -> l = l1 ++ et :: l2  -> kind et == T ->
  exists i pre, (pre, e, i) \in prefixes l /\ 
                (source et, fld et) \in (wavefront pre).
Proof.
move=>H1 H2 T; case:(prefix_rev H1 H2)=>i[H3 H4].
exists i, (take i l); split=>//.
by apply/mapP; exists et=>//; rewrite mem_filter T. 
Qed.

(******************************************************************)
(*    Apex procedure for exposing reachable objects in the graph  *)
(******************************************************************)

Definition expose_apex : seq ptr := 
  [seq let pi := pe.1.2    in
       let o  := source pi in
       let f  := fld pi    in 
       o#f@g | pe <- prefixes p &
               let: (pre, pi, _) := pe          in   
               let k             := (kind pi)   in   
               let o             := (source pi) in
               let f             := (fld pi)    in   
               (kindMA k) && ((o, f) \in wavefront pre)].


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
case: (prefix_wavefront D E Kt)=>i[pre][H1] H2.
apply/mapP; exists (pre, ema, i)=>//=.
by rewrite mem_filter Kma/= -S -F H2 H1.
Qed.

(* [trace_pure]: If there is no matching MA-entries for the T-entry
   'et' in the corresponding suffix of 'l', then et's recorded value
   survives till the final graph. *)

Lemma trace_pure l h' (g' : graph h') et l1 l2: 
  kind et == T -> 
  executeLog g0 l = Some {| hp := h'; gp := g' |} ->
  ~~ has (matchingMA (source et) (fld et)) l2 -> l = l1 ++ et :: l2 -> 
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

Lemma pickLastMAInSuffix l l1 l2 h' (g' : graph h') o f:
  l = l1 ++ l2 ->
  executeLog g0 l = Some {| hp := h'; gp := g' |} ->
  has (fun e => [&& kindMA (kind e), o == source e & f == fld e]) l2 ->
  has (fun e => [&& kindMA (kind e), o == source e,  f == fld e & 
                    o#f@g' == new e]) l2.
Proof.
elim/last_ind: l2 l h' g'=>//ls e Hi l h' g' E H1 H2.
rewrite !has_rcons in H2 *; rewrite -rcons_cat in E; subst l.
case X: [&& kindMA (kind e), o == source e & f == fld e]; last first.

(* First case: the last entry not a matching one *)
- move/negbT: X; rewrite negb_and. 
  case G: (~~ kindMA (kind e))=>//=.

  (* (a) It is a T-entry => by induction hypothesis *) 
  + move=>_; have T: kind e == T by case: (kind e) G.
    case: (replayLogRconsT H1 T)=>H3 H4.
    move/eqP: T=>T; rewrite T /= in H2.
    by move: (Hi _ _ _ (erefl (l1 ++ ls)) H3 H2)=>->; rewrite orbC.

(* (b) It's and MA-entry with different source/field *)
- move=>G1; have K : (kindMA (kind e)) by move/negbFE: G.
  rewrite K (negbTE G1)/= in H2. 
  have N: ~~ matchingMA o f e by rewrite /matchingMA K.
  case: (replayLogRconsMA_neg H1 N)=>h1[g1][H3]E.
  by move: (Hi _ _ _ (erefl (l1 ++ ls)) H3 H2); rewrite E orbC=>->.

(* Now we have a matching entry, which actually contributes. *)
apply/orP; left; clear H2 Hi.
suff S: o # f @ g' == new e by case/andP: X=>->/andP[]->->.
by case: (replayLogRconsMA H1 X)=>h1[g1][_]->.
Qed.

(* The following lemmas that for any T-entry, its captured o.f-value
   is either in the graph, or there exists an MA-antry *behind* it in
   the log, which overrides the value of o.f. *)

Lemma traced_objects et l1 l2 :
  let o := source et in
  let f := fld    et in
  let n := new    et in
  p = l1 ++ et :: l2 -> kind et == T -> 
  o#f@g = n \/
  has (fun e => [&& kindMA (kind e), o == source e, f == fld e & 
                    o#f@g == new e]) l2.
Proof.
move=>/= E Kt.
case H: (has (matchingMA (source et) (fld et)) l2); [right|left]; last first.
- by apply: (@trace_pure p h g et l1 l2 Kt epf)=>//; apply/negbT.
rewrite /matchingMA in H *; rewrite -cat_rcons in E. 
by apply: (pickLastMAInSuffix E epf H).
Qed.

(*  Need to prove existence of such object in the prefix now ...*)


(* Collect all traced objects from the log *)
Definition tracedObjects3 : seq (ptr * nat * ptr) :=
  [seq (source pi, fld pi, old pi) | pi <- p & (kind pi) == T]. 

Definition tracedObjFields : seq (ptr * nat) := unzip1 tracedObjects3.
Definition tracedTargets : seq ptr := unzip2 tracedObjects3.

(* Next, we define the set of actual objects in the final heap-graph
   with respect to traced objects. *)

Definition actualTargets : seq ptr := 
  [seq (pf.1)#(pf.2)@g | pf <- tracedObjFields].

(* The following theorem states the soundness of the expose_apex
   procedure: it adds to the tracedTargets a set of pointers, such
   that the union of the two contains the actual targets by the end of
   the log execution. *)


Theorem expose_apex_sound : 
  {subset actualTargets <= tracedTargets ++ expose_apex}.
Proof.
admit.
Admitted.

End ApexAlgo.


