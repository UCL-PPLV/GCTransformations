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

Lemma psn_rcons {A : eqType} (pos neg : A -> bool) l e :
  PositiveSeqNonInd pos neg (rcons l e) -> neg e = false ->
  PositiveSeqNonInd pos neg l.
Proof.
move=>H P en l1 l2 N E; apply: (H en l1 (rcons l2 e) N); subst l.
by rewrite rcons_cat; congr (_++_).
Qed.

Lemma cat_inj {A : eqType} (l1 l2 l3 : seq A) :
  l1 ++ l3 = l2 ++ l3 -> l1 = l2.
Proof.
elim/last_ind: l3; first by rewrite !cats0.
by move=>l3 x Hi; rewrite -!rcons_cat=>/rcons_inj[]/Hi.
Qed.

Lemma cancel_back {A : eqType} (f : A -> bool) l1 l2 e1 e2 k1 k2 :
  rcons l1 e1 ++ k1 = rcons l2 e2 ++ k2 ->
  ~~ has f k1 -> ~~ has f k2 -> f e1 -> f e2 ->
  [/\ l1 = l1, k1 = k2 & e1 = e2].
Proof.
elim/last_ind: k1 k2.
- case/lastP; first by rewrite ?cats0; move=>/rcons_inj[]->->.
  move=>l x; rewrite ?cats0 -rcons_cat=>/rcons_inj[]->->_ H G.
  by rewrite has_rcons G in H.
move=>l x Hi; case/lastP; rewrite ?cats0.
- rewrite -rcons_cat=>/rcons_inj[]=>Z1 Z2 H1 H2 G1 G2.
  by subst e2 l2; rewrite has_rcons G2 in H1.
move=>l' x'; rewrite -!rcons_cat=>/rcons_inj[]=>Z1 Z2 H1 H2 G1 G2; subst x'.
rewrite !has_rcons !Bool.negb_orb in H1 H2.
case/andP: H1=>H H1; case/andP: H2=>_ H2.
case: (Hi _ Z1 H1 H2 G1 G2)=>_ Y2 Y3; subst l' e2.
by move/cat_inj/rcons_inj: Z1=>[].  
Qed.
 
Lemma psl_prefix {A : eqType} (pos neg : A -> bool) l :
  PositiveSeqLarge pos neg  l->
  forall l3 ep l4, l = rcons l3 ep ++ l4 ->
  pos ep -> ~~ has neg l4 ->
  PositiveSeqLarge pos neg (rcons l3 ep).
Proof.
elim=>{l}.
- move=>l H l1 ep l2 Z P N; subst l.
  constructor 1; rewrite has_cat has_rcons /= !Bool.negb_orb in H.
  by rewrite has_rcons; case/andP: H=>/andP[]=>/negbTE->/negbTE->.
move=> l en ep l1 l2 l3 E H1 H2 H3 H4 H5 Hi l4 ep' l5 Z P N.
rewrite -cat_rcons in E.
have X: PositiveSeqLarge pos neg (rcons l1 ep).
apply: (Hi l1 ep [::])=>//; last by rewrite cats0.
clear X.
have X: has neg (rcons l4 ep').
- case B: (has neg (rcons l4 ep'))=>//.
  suff X: (has neg (rcons l4 ep' ++ l5)) != (has neg (rcons l1 ep ++ l3 ++ en :: l2)).
  + by rewrite -Z E in X; move/negbTE: X; rewrite eqxx.
  by rewrite !has_cat B/=; move/negbTE: N=>->; rewrite has_rcons H1 -!(orbC true)/=.
move: (find_last X)=>[en'][l6][l7][E']Z1 Z2; clear X.
rewrite Z in E; clear Z l.
suff X: l6 = rcons l1 ep ++ l3.
- subst l6. rewrite cat_rcons -catA in E'.
  by apply: (@NegSplit _ pos neg (rcons l4 ep') _ _ _ _ _ E').
rewrite E' in E; clear E' l4.
rewrite -cat_rcons -catA in E. rewrite [_ ++ l3 ++ _]catA in E.
rewrite -cat_rcons in E.
have X: ~~ has neg (l7 ++ l5).
  by rewrite has_cat; move/negbTE: N=>->; move/negbTE: Z2=>->.
case: (cancel_back E X H3 Z1 H1)=>W1 W2 W3. rewrite W2 in E;subst en'.
by move/cat_inj/rcons_inj: E=>[].
Qed.

(*
* We need to state that every "+" which is a predecessor
* of a "-" is different.
*)

Definition OnlyNegatives {A : eqType } neg pos (l : seq A) (t : PositiveSeqNonInd pos neg l) (l : seq A) : seq A :=
    filter neg l.

 Lemma positiveNonIndLarge  {A : eqType} (pos neg : A -> bool) (l : seq A) :
   PositiveSeqNonInd pos neg l -> PositiveSeqLarge pos neg l.
Proof.
elim/last_ind: l=>[_|l e Hi]; first by constructor 1.
case Y: (neg e)=>H; last first.
- have D: PositiveSeqNonInd pos neg l by apply: (psn_rcons H Y).
  case: (Hi D).
  + by move=>N; constructor 1; rewrite has_rcons Bool.negb_orb N Y.
  move=>en ep l1 l2 l3 E H1 H2 H3 H4 H5.  
  apply: (@NegSplit _ pos neg (rcons l e) en ep l1 (rcons l2 e) l3)=>//.
  - subst l; rewrite -!cats1 -!catA !cat_cons; congr (_++_).
    by rewrite !cats1; congr (_::_); rewrite rcons_cat; congr (_++_).
  - by rewrite has_rcons Bool.negb_orb H3 Y.
move: (H e l [::] Y); rewrite -cats1/=. case/(_ erefl)=>ep[l3][l4][E]P N.
suff D: PositiveSeqNonInd pos neg l.
- apply: (@NegSplit _ pos neg (l ++ [::e]) e ep l3 [::] l4 _ Y P _ N)=>//.
  - by rewrite E -catA; subst l.
  by subst l; apply: (@psl_prefix _ _ _ _ (Hi D) l3 ep l4)=>//; rewrite cat_rcons.
clear Hi; move=>en l1 l2 N' E'.
have Z: rcons l e = l1 ++ en :: rcons l2 e by rewrite E' rcons_cat/=.
by move: (H en l1 (rcons l2 e) N' Z).
Qed.  
 

Definition hasPrePos {A : eqType} (pos neg : A -> bool) (l : seq A) :=
  exists l1 ep l2, [/\ l = l1 ++ ep :: l2, pos ep & ~~ has neg l2].

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

Lemma m_plus_trimr l l1 l2 et o f n:
    kind et == T ->
    fld et == f ->
    source et == o ->
    l = (et :: l1) ++ l2 ->
     ~~ has (matchingMA o f) l2 ->
     M_plus ((et :: l1) ++ l2) o f n =
     M_plus (et :: l1) o f n.
Proof.
    move /eqP => kind_et /eqP => fld_et /eqP => source_et le_eq no_match_l2.
    rewrite cat_cons; rewrite cat_cons in le_eq.
    move: (m_plus_count (l1 ++ l2) n kind_et fld_et source_et).
    move => transform; rewrite transform -cat_cons count_cat.
    have D: count (mpos o f n) l2 = 0; clear transform le_eq;
    move: no_match_l2.  elim/last_ind: l2=>//.
    move => s x hyp; rewrite has_rcons; move /norP.
    case => not_match_x not_match_s; rewrite -cats1 count_cat {2}/count {2}/mpos.
    rewrite /matchingMA in not_match_x.
    have: ~~ [&& kindMA (kind x), new x == n & (source x, fld x) == (o, f)].
    move: not_match_x; move /nandP; case => kind_x.
    apply /nandP; left =>//.
    apply /nandP; right; apply /nandP; right.
    apply /eqP; case; move: kind_x; move /nandP; case.
    move => t1 t2 t3; move: t2; move /sym; rewrite /negb in t1.
    move /eqP => eq;  move: t1; destruct (o == source x) as []eqn:? =>//.
    move => t1 t2 t3; move: t3; move /sym; rewrite /negb in t1.
    move /eqP => eq; move: t1; destruct (f == fld x) as []eqn:? =>//.
    move => not_ma_x; move: (negbTE not_ma_x); move => not_ma_x_eq.
    rewrite not_ma_x_eq addn0; apply /eqP; rewrite addn_eq0; apply /andP; split.
    move: (hyp not_match_s); move /eqP=>//.
    done.
    rewrite D addn0;  move => _; apply /sym.
    move: (m_plus_count l1 n kind_et fld_et source_et)=>//.
Qed.

Lemma m_minus_trimr l l1 l2 et o f n:
    kind et == T ->
    fld et == f ->
    source et == o ->
    l = (et :: l1) ++ l2 ->
     ~~ has (matchingMA o f) l2 ->
     M_minus ((et :: l1) ++ l2) o f n =
     M_minus (et :: l1) o f n.
Proof.
    move /eqP => kind_et /eqP => fld_et /eqP => source_et le_eq no_match_l2.
    rewrite cat_cons; rewrite cat_cons in le_eq.
    move: (m_minus_count (l1 ++ l2) n kind_et fld_et source_et).
    move => transform; rewrite transform -cat_cons count_cat.
    have D: count (mneg o f n) l2 = 0; clear transform le_eq;
    move: no_match_l2.  elim/last_ind: l2=>//.
    move => s x hyp; rewrite has_rcons; move /norP.
    case => not_match_x not_match_s; rewrite -cats1 count_cat {2}/count {2}/mneg.
    rewrite /matchingMA in not_match_x.
    have: ~~ [&& kindMA (kind x), old x == n & (source x, fld x) == (o, f)].
    move: not_match_x; move /nandP; case => kind_x.
    apply /nandP; left =>//.
    apply /nandP; right; apply /nandP; right.
    apply /eqP; case; move: kind_x; move /nandP; case.
    move => t1 t2 t3; move: t2; move /sym; rewrite /negb in t1.
    move /eqP => eq;  move: t1; destruct (o == source x) as []eqn:? =>//.
    move => t1 t2 t3; move: t3; move /sym; rewrite /negb in t1.
    move /eqP => eq; move: t1; destruct (f == fld x) as []eqn:? =>//.
    move => not_ma_x; move: (negbTE not_ma_x); move => not_ma_x_eq.
    rewrite not_ma_x_eq addn0; apply /eqP; rewrite addn_eq0; apply /andP; split.
    move: (hyp not_match_s); move /eqP=>//.
    done.
    rewrite D addn0;  move => _; apply /sym.
    move: (m_minus_count l1 n kind_et fld_et source_et)=>//.
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


(*
* if a o.f was not pointing to n at some point and it currently is
* pointing to n => the last MA for o.f had new = n.
*)

Lemma is_seq l et l1 h0 (g0: graph h0) h' (g': graph h') n:
    kind et == T ->
    l = (et::l1) ->
    executeLog g0 l = Some {| hp := h'; gp := g' |} ->
    ~~ (n == new et) ->
    PositiveSeqNonInd (mpos (source et) (fld et) n) (mneg (source et) (fld et) n) l.
Proof.
    move => et_t seqs ex not_eq_fld.
    case => [knd o' f' old' new' l_prefix l_suffix is_neg l_eq].
    set ema := {| kind := knd; source := o'; fld := f'; old := old'; new := new' |}.
    rewrite -/ema in is_neg l_eq; rewrite /mneg in is_neg.
    rewrite seqs in ex.
    move: (replayLogCons2 ex).
    case => [h1]; case => [g1]; case => [ex_et _].
    have D:  [:: et] = rcons [::] et; rewrite /rcons =>//.
    rewrite D in ex_et.
    move: (replayLogRconsT ex_et et_t); rewrite /executeLog.
    case; case => h_eq.
    move: (eqG g0 g1 (source et)) => g_eq.
    move: (g_eq h_eq); clear g_eq h_eq.
    move => g_eq; rewrite -g_eq => init_fld _.
    clear ex_et D g_eq g1 h1; rewrite -cat_rcons in l_eq.
    rewrite l_eq in seqs; rewrite -seqs in ex.
    case: (replayLogCat ex) => [[hx gx]]; move: is_neg.
    move /andP; case => ema_ma is_neg exec_til_ema.
    move: (oldSignificance ema_ma exec_til_ema).
    case => h1; case => g1; case; move => src exec_l_prefix.
    move: is_neg.
    move /andP; case; move /eqP => ema_n.
    rewrite ema_n in src;  move /eqP.
    rewrite /ema /source /fld in src.
    case;  move => o_et f_et; rewrite -f_et -o_et in init_fld.
    rewrite -init_fld -src eq_sym in not_eq_fld.
    move: (existsMAInSufix exec_l_prefix not_eq_fld).
    case => ema'; case => l3'; case => l4'; move /and4P;  case.
    move => match_o_f_ema  new_ema_val l_prefix_eq no_ma.
    exists ema'; exists l3'; exists l4'; split.
    move: l_prefix_eq; move /eqP =>//.
    rewrite /mpos; apply/and3P.
    rewrite /matchingMA in match_o_f_ema.
    move: match_o_f_ema; move /and3P.
    case; move => kindma' /eqP o_ema' /eqP f_ema'; split.
    done.
    rewrite src in new_ema_val=>//.
    rewrite -o_ema' -f_ema' o_et f_et =>//.
    rewrite -o_et -f_et.
    apply /hasPn; rewrite /mneg; move: no_ma.
    move /hasPn; rewrite /matchingMA.
    move => no_ma x' x'_in_l4.
    move: (no_ma x' x'_in_l4).
    move /nandP; case => not_ma.
    apply /nandP; left =>//.
    apply /nandP; right;  apply /nandP; right.
    apply /eqP; case; move: not_ma; move /nandP; case.
    move => t1 t2 t3; move: t2; move /sym; rewrite /negb in t1.
    move /eqP => eq;  move: t1.
    destruct (o' == source x') as []eqn:? =>//.
    move => t1 t2 t3; move: t3; move /sym; rewrite /negb in t1.
    move /eqP => eq; move: t1.
    destruct (f' == fld x') as []eqn:? =>//.
Qed.

Lemma mut_count_trimmed h0 (g0 : graph h0) l h (g : graph h) et ema l2 :
   executeLog g0 l = Some {| hp := h; gp := g |} ->
   l = (et :: rcons l2 ema) -> kind et == T ->
   matchingMA (source et) (fld et) ema ->
   source et # fld et @ g = new ema ->
   ~~ has (matchingTFull ema) l ->
   M_minus l (source ema) (fld ema) (new ema) <
   M_plus l (source ema) (fld ema) (new ema).
Proof.
    move => ex l_eq et_kind matchMA_ema.
    have D: mpos (source ema) (fld ema) (new ema) ema.
    rewrite /matchingMA in matchMA_ema.
    rewrite /mpos; move: matchMA_ema; move /and3P;
    case => ema_kind  ema_src ema_fld; apply /and3P; split=>//.
    rewrite l_eq in ex; move: (replayLogCons2 ex).
    case => [h1]; case => [g1]; case => [ex_et _].
    have D':  [:: et] = rcons [::] et; rewrite /rcons =>//.
    rewrite D' in ex_et.
    move: (replayLogRconsT ex_et et_kind); rewrite /executeLog.
    case; case => h_eq.
    move: (eqG g0 g1 (source et)) => g_eq; move: (g_eq h_eq); clear g_eq h_eq.
    move => g_eq; rewrite -g_eq => init_fld _; clear ex_et D' g_eq g1 h1.
    move => end_fld no_match_ema; rewrite l_eq in no_match_ema.
    rewrite -has_rev rev_cons has_rcons in no_match_ema.
    move: no_match_ema; move /norP; case => not_ema_et _.
    rewrite /matchingTFull in not_ema_et; move: matchMA_ema.
    rewrite /matchingMA; move /and3P.
    case => kind_ema src_eq fld_eq; rewrite et_kind fld_eq src_eq in not_ema_et.
    move: not_ema_et.
    move /nandP; rewrite {1}/negb; case =>//.
    move /nandP; rewrite {1}/negb; case =>//.
    move /nandP; rewrite {1}/negb; case =>//.
    rewrite eq_sym; move => new_neq; rewrite -l_eq in ex.
    move: (positiveNonIndLarge (is_seq et_kind l_eq ex new_neq)).
    have D': exists l' e, l = rcons l' e /\ (mpos (source et) (fld et) (new ema)) e.
    exists (et::l2), ema; split.
    rewrite rcons_cons=>//.
    move /eqP in fld_eq; move /eqP in src_eq.
    rewrite -src_eq -fld_eq in D =>//.
    move => posLarge; move: (strictlyPos posLarge D')  => count_fact.
    set f := (fld et); have wtf1: (fld et) = f; rewrite /f=>//.
    set o := (source et); have wtf2: (source et) = o; rewrite /o=>//.
    move /eqP in et_kind.
    move: (m_plus_count (rcons l2 ema) (new ema) et_kind wtf1 wtf2).
    move: (m_minus_count (rcons l2 ema) (new ema) et_kind wtf1 wtf2).
    move => m_minus_value m_plus_value.
    move /eqP in src_eq; move /eqP in fld_eq.
    rewrite -l_eq -wtf1 -wtf2 fld_eq src_eq in m_plus_value m_minus_value.
    rewrite src_eq fld_eq in count_fact; rewrite m_plus_value m_minus_value =>//.
Qed.
(*

The proof of this fact goes by induction on l2, however, the inductive
invariant is somewhat tricky. In particular, we should ensure that for
each decrement of the mutator count, there should be a preceding
entry, which increases it. So, see a more general previous statement.



 *)
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

    move => ex_total l_eq et_kind et_ema heap_state
            not_traced no_trace_l1 no_match_l3.
    rewrite /matchingT in no_trace_l1.
    move: (m_plus_triml  ((et :: rcons l2 ema) ++ l3) (new ema) no_trace_l1)
          (m_minus_triml  ((et :: rcons l2 ema) ++ l3) (new ema) no_trace_l1).
    move => short_mplus short_mminus.
    rewrite -l_eq in short_mplus short_mminus; rewrite short_mplus short_mminus.
    clear short_mplus short_mminus; assert (et_ema' := et_ema).
    move: et_ema; rewrite /matchingMA; move /and3P.
    case => kind_ema source_ema fld_ema.
    set l_suff := (et :: rcons l2 ema) ++ l3.
    have D: l_suff = (et :: rcons l2 ema) ++ l3. done.
    rewrite (eqP fld_ema) (eqP source_ema) in no_match_l3.
    move: (m_plus_trimr (new ema) et_kind fld_ema source_ema D no_match_l3)
          (m_minus_trimr (new ema) et_kind fld_ema source_ema D no_match_l3).
    move => shorten_plus shorten_minus; rewrite shorten_plus shorten_minus.
    clear shorten_plus shorten_minus no_match_l3 no_trace_l1.
    rewrite l_eq in ex_total; move: (replayLogCat2 ex_total).
    case => h1; case => g1; case => _ ex_suff.
    case: (replayLogCat ex_suff)=>[[h2 g2]] ex_important.
    set l' := (et :: rcons l2 ema); rewrite -rcons_cons in ex_important.
    have match_ema: matchingMA (source ema) (fld ema) ema.
    rewrite /matchingMA; apply /and3P=>//.
    move: (replayLogRconsMA ex_important match_ema).
    case => h'; case => g'; case => _ final_heap; clear h' g'.
    have: ~~ has (matchingTFull ema) l'.
    rewrite has_count -eqn0Ngt; rewrite has_count -eqn0Ngt in not_traced.
    rewrite l_eq in not_traced.
    rewrite count_cat addn_eq0 count_cat addn_eq0 -/l' in not_traced.
    move: not_traced; move /and3P; case => t1 t2 t3 =>//.
    move => has_no_t'; rewrite -(eqP fld_ema) -(eqP source_ema) in final_heap.
    rewrite rcons_cons in ex_important.
    have dumb: l' = et :: rcons l2 ema. done.
    move: (mut_count_trimmed ex_important dumb et_kind et_ema' final_heap has_no_t').
    rewrite -/l'=>//.
Qed.

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


(* TODO: relaxing mutator counts *)


Variables (wf_lt wf_gt : log -> seq (ptr * nat)).

Hypothesis Hwfg : forall l p, prefix p l -> {subset wavefront p <= wf_gt p}. 
Hypothesis Hwfl : forall l p, prefix p l -> {subset wf_lt p <= wavefront l}. 

End MutatorCount.
