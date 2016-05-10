From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep pred prelude idynamic ordtype pcm finmap unionmap heap coding. 
Require Import Hgraphs Logs Wavefronts.
Require Import WavefrontDimension.
Set Implicit Arguments. 
Unset Strict Implicit.
Unset Printing Implicit Defensive. 


(* Defining positive sequences *)
Section Positive.

(* The sequence l is positive (wrt. to pos/neg functions), if it can
   be parititioned by negative elements to sequences with non-negative
   pos/neg balances, as established by the following lemmas. *)

Inductive PositiveSeqSmall {A : eqType} (pos neg : A -> bool) 
                      (l : seq A)  (needPos : bool) : Prop :=

  (* Positive elements resets the context needPos to false *)
  | Pos l1 e  of [/\ l = rcons l1 e, pos e, 
                 neg e = false & PositiveSeqSmall pos neg l1 false]

  | Neg l1 e  of [/\ l = rcons l1 e, pos e = false, 
                 neg e, PositiveSeqSmall pos neg l1 true & needPos = false]

  | MT        of l = [::] &  needPos = false

  (* Neutral element just propagates the knowledge about interleaving. *)
  | Neut l1 e of [/\ l = rcons l1 e, pos e = false, 
                     neg e = false & PositiveSeqSmall pos neg l1 needPos]

  | PosNeg l1 e of [/\ l = rcons l1 e, pos e = true, 
                    neg e = true & PositiveSeqSmall pos neg l1 true].


Lemma rcons_inj {A : eqType} l l' (a a' : A) :
  rcons l a = rcons l' a' -> (l, a) = (l', a').
Proof.
elim: l l'. 
- move=>l'/=; case: l'=>//=; first by case=>->.
  by move=> x l; case=>->; case: l.
move=>x l Hi l'; case: l'; first by case=>->; case: l Hi.
by move=>x' l'; rewrite !rcons_cons; case=>Z; subst x'=>/Hi[]<-<-.
Qed.

Lemma posCount_gen {A : eqType} pos neg (l : seq A) next : 
  PositiveSeqSmall pos neg l next -> 
  if next then count neg l < count pos l else count neg l <= count pos l.
Proof.
elim/last_ind: l next; first by case=>//; case=>//l e[]; case: l.
move=>l e Hi; case.
- by case=>//l' e'[/rcons_inj][]Z1 Z2 P N//; subst l' e'=>/Hi H;
     rewrite -!size_filter !filter_rcons P N/= ?size_rcons !size_filter.
case; do?[by move=>->]=>l' e'[/rcons_inj][]Z1 Z2 P N; subst l' e'=>/Hi H;
rewrite -!size_filter !filter_rcons P N/= ?size_rcons !size_filter//.   
- by apply (leq_trans H); apply: leqnSn.
by apply (ltn_trans H); apply: ltnSn.
Qed.

Lemma posCount {A : eqType} pos neg (l : seq A) next : 
  PositiveSeqSmall pos neg l next -> count neg l <= count pos l.
Proof. by move/posCount_gen; case: next=>//; apply: ltnW. Qed.

(* Alternative definition of positive sequences *)
Inductive PositiveSeqLarge {A : eqType} (pos neg : A -> bool) (l : seq A) : Prop :=
  | NonNeg of ~~ has neg l
  | NegSplit en ep l1 l2 l3 of l = l1 ++ ep :: l3 ++ en :: l2 & 
                               neg en & pos ep & 
                               ~~ has neg l2 & ~~ has neg l3 &
                               PositiveSeqLarge pos neg (rcons l1 ep).

Lemma countNeg {A : eqType} (f : A -> bool) (l : seq A) :
  ~~ has f l -> count f l = 0.
Proof.
by elim: l=>//=e l Hi/norP[H1 /Hi]H2; rewrite H2 addn0; move/negbRL: H1=>->.
Qed.

Lemma strictlyPos {A : eqType} (pos neg : A -> bool) (l: seq A):
  PositiveSeqLarge pos neg l -> 
  (exists l' e, l = rcons l' e /\ pos e) ->
  count neg l < count pos l.
Proof.
elim=>{l}[l H[l'][e][Z]P1|l en ep l1 l2 l3->{l}N P H1 H2 Hi H3[l'][e][Z]P1].
- by subst l; rewrite (countNeg H) -cats1/= count_cat/= P1/= addn0 addnC.
have X: (exists (l' : seq A) (e : A), rcons l1 ep = rcons l' e /\ pos e)
        by exists l1, ep. 
move/H3: X=>{H3}H3. 
case: (lastP l2) H1 Z=>/=[_|l e' H1].
- rewrite cats1 -rcons_cons -rcons_cat=>/rcons_inj[]Z1 Z2; subst l' en. 
  rewrite -cats1 !count_cat/= N P P1 (countNeg H2)!addn0/= addnA.
  rewrite -cats1 !count_cat /= !addn0 P/= -(ltn_add2r 1) in H3.
  by apply: (leq_trans H3); rewrite addnAC; apply: leq_addr.
rewrite -rcons_cons -rcons_cat -rcons_cons -rcons_cat=>/rcons_inj[]Z1 Z2. 
subst l' e'.
rewrite -cats1 !count_cat/= !count_cat/=  N P P1 (countNeg H2)!addn0/= addnA !add0n.
rewrite -cats1 has_cat negb_or in H1. 
case/andP:H1=>/=; rewrite orbC=>/==>H1/negPf->/=.
rewrite (countNeg H1) !addn0 addnA.
rewrite -cats1 !count_cat /= !addn0 P/= -(ltn_add2r 1) in H3.
by apply: (leq_trans H3); rewrite addnAC; apply: leq_addr.
Qed.

Lemma posCountLarge {A : eqType} pos neg (l : seq A) :
  PositiveSeqLarge pos neg l -> count neg l <= count pos l.
Proof.
elim=>{l}[l/countNeg->|l en ep l1 l2 l3->{l}N P H1 H2 Hi H3]//.
rewrite -cat_cons catA -(cat_rcons ep) !count_cat/=. 
rewrite (countNeg H1) (countNeg H2) !addn0.
rewrite -cats1 !count_cat/= !addn0 N P/=.
rewrite -cats1 !count_cat/= !addn0 P/= in H3.
have X: (exists (l' : seq A) (e : A), rcons l1 ep = rcons l' e /\ pos e)
        by exists l1 ,ep. 
move: (strictlyPos Hi X); rewrite -cats1 !count_cat /= P !addn0/=.
by rewrite -addn1=>G; apply: (leq_trans G); rewrite -addnA; apply: leq_addr.
Qed.

Lemma find_last {A: eqType} (l : seq A) f : has f l ->
  exists e l1 l2, [/\ l = l1 ++ e :: l2, f e & ~~ has f l2].
Proof.
elim/last_ind: l=>//= l e Hi; case X : (f e)=>/=.
- by move=>_; exists e, l, [::]; rewrite cats1. 
rewrite -cats1 has_cat/= orbC X/=.
case/Hi=>e'[l1][l2][E1]H1 H2; subst l.
exists e', l1, (rcons l2 e); rewrite cats1 rcons_cat rcons_cons. 
by split=>//; rewrite -cats1 has_cat /= orbC X H2.
Qed.

Definition PositiveSeqNonInd {A : eqType} (pos neg : A -> bool) (l : seq A) : Prop :=
  forall en l1 l2, neg en -> l = l1 ++ en :: l2 ->
  exists ep l3 l4, [/\ l1 = l3 ++ ep :: l4, pos ep & ~~ has neg l4].

(* Lemma positiveNonIndLarge  {A : eqType} (pos neg : A -> bool) (l : seq A) :  *)
(*   PositiveSeqNonInd pos neg l -> PositiveSeqLarge pos neg l. *)
(* Proof. *)
(* elim/last_ind: l=>[_|l e Hi]; first by constructor 1.  *)
(* case Y: (neg e). *)
(* (* e is negative *) *)
(* move/(_ e l [::] Y); rewrite cats1=>/(_ (erefl _))[ep][l1][l2][E]P H2. *)
(* apply: (@NegSplit _ pos neg (rcons l e) e ep l1 [::] l2)=>//. *)
(* - by rewrite E rcons_cat rcons_cons cats1.  *)
(* admit. *)
(* Admitted. *)

Definition hasPrePos {A : eqType} (pos neg : A -> bool) (l : seq A) :=
  exists l1 ep l2, [/\ l = l1 ++ ep :: l2, pos ep & ~~ has neg l2].

(* TODO: Start here! *)

Lemma tryOurLemma {A : eqType} (pos neg : A -> bool) (l: seq A) : 
  PositiveSeqLarge pos neg l.
Proof.
elim/last_ind: l=>[|l e Hi]; first by constructor 1.
case X: (neg e); last first. 
- case: Hi=>[H|en ep l1 l2 l3 E N P H1 H2 Hi].
  - by constructor 1; rewrite -cats1 has_cat/= X; rewrite orbC/=.
  - apply: (@NegSplit _ pos neg (rcons l e) en ep l1 (rcons l2 e) l3)=>//.
    - by rewrite E rcons_cat rcons_cons rcons_cat rcons_cons.
    by rewrite -cats1 has_cat /= X orbC.

(* This is specific to our logs and should be extracted and proved separately *)
suff Z : hasPrePos pos neg l.

case: Hi=>[H|en ep l1 l2 l3 E N P H1 H2 Hi].
- case: Z=>l1[ep][l2][Z]P H'. 
  apply: (@NegSplit _ pos neg (rcons l e) e ep l1 [::] l2 _ X P)=>//.
  - by subst l; rewrite rcons_cat rcons_cons cats1.
  constructor 1; subst l; rewrite -cats1.
  rewrite !has_cat !negb_or/= -!(andbC true)/= in H *.
  by case/ andP: H=>->/andP[->].

case: Z=>l4[epp][l5][Z]P' H'. 

Check (@NegSplit _ pos neg (rcons l e) e epp).

(* OKay, now there is the plan: 

- Prove the hasPrePos property for the valid logs, ending with the negative node.
- Parametrize this lemma with this property appropriately.

*)

(* move: (@NegSplit _ pos neg (rcons (l1 ++ ep :: l3) en) en ep l1 [::] l3). *)
(* rewrite {1}rcons_cat rcons_cons -cats1=>/(_ (erefl _) N P is_true_true H2 Hi)=>H. *)
(* rewrite -!(cat_cons) catA -cat_rcons in E. *)


Admitted.
  
End Positive.

Section MutatorCount.

Variable e0 : LogEntry.

Definition mpos o f n (pi : LogEntry)  := 
  [&& (kindMA (kind pi)), (new pi) == n & (source pi, fld pi) == (o, f)].

Definition mneg o f n (pi : LogEntry)  := 
  [&& (kindMA (kind pi)), (old pi) == n & (source pi, fld pi) == (o, f)].

(* A number of added references from behind of wavefront to the
   field object o (check new pi). *)

Definition M_plus l o f n : nat := size 
             [seq (o, f, n)
                  | pe <- prefixes e0 l &
                    mpos o f n pe.2 &&
                    (* TODO: over-approximate wavefront with w_gt *)
                    ((o, f) \in wavefront pe.1)].

(* A number of removed references from behind of wavefront to the
   field object o (check old pi). *)

Definition M_minus l o f n : nat := size 
             [seq (o, f, n)
                  | pe <- prefixes e0 l &
                    mneg o f n pe.2 &&
                    (* TODO: under-approximate wavefront with w_gt *)
                    ((o, f) \in wavefront pe.1)].


Lemma m_plus_count et l o f n :
  kind et = T -> fld et = f -> source et = o ->
  M_plus (et :: l) o f n = count (mpos o f n) (et :: l).
Proof.
move=>H1 H2 H3; rewrite /M_plus size_map size_filter prefix_cons/=.
rewrite [mpos o f n et]/mpos !H1/= !add0n.
rewrite (wavefront_filterT e0 l (mpos o f n) H1 H2 H3).
have X : {in (prefixes e0 l),
         (fun pe : seq LogEntry * LogEntry => mpos o f n pe.2) =1
         (mpos o f n) \o snd} by [].
by rewrite (eq_in_count X) count_comp prefix_snd.
Qed.

Lemma m_minus_count et l o f n :
  kind et = T -> fld et = f -> source et = o ->
  M_minus (et :: l) o f n = count (mneg o f n) (et :: l).
Proof.
move=>H1 H2 H3; rewrite /M_minus size_map size_filter prefix_cons/=.
rewrite [mneg o f n et]/mneg !H1/= !add0n.
rewrite (wavefront_filterT e0 l (mneg o f n) H1 H2 H3).
have X : {in (prefixes e0 l),
         (fun pe : seq LogEntry * LogEntry => mneg o f n pe.2) =1
         (mneg o f n) \o snd} by [].
by rewrite (eq_in_count X) count_comp prefix_snd.
Qed.


(* The following two lemmas generalize these mutator count results to
   non-trimmed logs forom the left (under the appropriate conditions
   on l1).  *)

Lemma m_plus_triml l1 l2 o f n :
  ~~ has (fun e => [&& kind e == T, fld e == f & source e == o]) l1 ->
  M_plus (l1 ++ l2) o f n = M_plus l2 o f n.
Proof.
move=>H.
rewrite /M_plus !size_map prefix_catl/= filter_cat size_cat.
have X: size [seq pe <- prefixes e0 l1 | 
              mpos o f n pe.2 & (o, f) \in wavefront pe.1] = 0.
- rewrite size_filter; apply: countNeg.
  apply/hasP=>[[[pre pi]]]=>A.
  case/andP=>/andP/=[H1]/andP[H2]/eqP[]H3 H4/mapP[et]; rewrite mem_filter.
  case/andP=>/eqP G1 G2[] G3 G4.
  move/prefV: (A)=>[i][_]_ Z.
  have Y: et \in l1 by rewrite Z mem_cat G2.
  by move/hasPn: H=>/(_ _ Y); rewrite G1 -G4 -G3 !eqxx.
rewrite X add0n !size_filter; clear X.
rewrite -(count_comp (fun pe : log * LogEntry =>
          mpos o f n pe.2 && ((o, f) \in wavefront pe.1))
         (fun pe => (l1 ++ pe.1, pe.2))).
apply: eq_in_count=>pre D/=; congr (_ && _).
rewrite /wavefront; apply/Bool.eq_iff_eq_true; split;
case/mapP=>e; rewrite mem_filter=>/andP[/eqP H1]G []H2 H3.
- rewrite mem_cat in G; case/orP:G=>G.
  - by move/hasPn: H=>/(_ _ G); rewrite H1 H2 H3 !eqxx.
  apply/mapP; exists e; last by subst o f.  
  by rewrite mem_filter H1 G eqxx.
apply/mapP; exists e; last by subst o f.  
by rewrite mem_filter mem_cat H1 G orbC.
Qed.


Lemma m_minus_triml l1 l2 o f n :
  ~~ has (fun e => [&& kind e == T, fld e == f & source e == o]) l1 ->
  M_minus (l1 ++ l2) o f n = M_minus l2 o f n.
Proof.
move=>H.
rewrite /M_minus !size_map prefix_catl/= filter_cat size_cat.
have X: size [seq pe <- prefixes e0 l1 | 
              mneg o f n pe.2 & (o, f) \in wavefront pe.1] = 0.
- rewrite size_filter; apply: countNeg.
  apply/hasP=>[[[pre pi]]]=>A.
  case/andP=>/andP/=[H1]/andP[H2]/eqP[]H3 H4/mapP[et]; rewrite mem_filter.
  case/andP=>/eqP G1 G2[] G3 G4.
  move/prefV: (A)=>[i][_]_ Z.
  have Y: et \in l1 by rewrite Z mem_cat G2.
  by move/hasPn: H=>/(_ _ Y); rewrite G1 -G4 -G3 !eqxx.
rewrite X add0n !size_filter; clear X.
rewrite -(count_comp (fun pe : log * LogEntry =>
          mneg o f n pe.2 && ((o, f) \in wavefront pe.1))
         (fun pe => (l1 ++ pe.1, pe.2))).
apply: eq_in_count=>pre D/=; congr (_ && _).
rewrite /wavefront; apply/Bool.eq_iff_eq_true; split;
case/mapP=>e; rewrite mem_filter=>/andP[/eqP H1]G []H2 H3.
- rewrite mem_cat in G; case/orP:G=>G.
  - by move/hasPn: H=>/(_ _ G); rewrite H1 H2 H3 !eqxx.
  apply/mapP; exists e; last by subst o f.  
  by rewrite mem_filter H1 G eqxx.
apply/mapP; exists e; last by subst o f.  
by rewrite mem_filter mem_cat H1 G orbC.
Qed.


(* TODO: Okay, now (1) we can express M_plus and M_minus in terms of
   counts of positive and negative elements and (2) we know that for
   positive sequences the positive count is always greated or equal
   than a negative count. Now, we need to establish that a valid log
   always forms a positive sequence. In other words, we need to prove
   that each such log (starting from the corresponding T-entry is a
   subject of PositiveSeq). *)


(* A T-entry e records exactly the new value of a MA-entry *)

Definition matchingTFull ema := fun e =>
   [&& kind e == T, fld e == fld ema,
       source e == source ema & new e == new ema].

Definition matchingT ema := fun e =>
   [&& kind e == T, fld e == fld ema & source e == source ema].



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
