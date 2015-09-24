Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat.
Require Import Ssreflect.eqtype Ssreflect.ssrfun Ssreflect.seq.
Require Import MathComp.path.
Require Import Eqdep pred prelude idynamic ordtype pcm finmap unionmap heap coding. 
Require Import Hgraphs Logs.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

(*******************************************************************************)
(* Definitions of wavefronts and indexed log prefixes with a number of
   lemmas about them. *)
(*******************************************************************************)


Section Wavefronts.

(* Default log entry *)
Variable e0 : LogEntry.

Definition prefixes l := 
  map (fun n => (take n l, nth e0 l n)) (iota 0 (size l)).

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

Lemma in_prefixes_full l e pr: (pr, e) \in prefixes l ->
  exists i, [/\ i < size l, nth e0 l i = e & pr = take i l].
Proof.
case/mapP=>n H; case=>Z2 Z3; subst e pr; exists n; split=>//.
by rewrite mem_iota add0n in H; case/andP: H.
Qed.

Lemma in_prefixes l e pr: (pr, e) \in prefixes l -> e \in l.
Proof.
case/in_prefixes_full=>n [H1]H2 H3.
have X: exists2 j, j < size l & nth e0 l j = e by exists n=>//.
by move/nthP: X.
Qed.

Lemma prefixes_in l e: e \in l -> 
  exists i, (take i l, e) \in prefixes l.
Proof.
move=>D; case/(nthP e0): (D)=>j H1 H2; exists j.
apply/mapP; exists j; first by rewrite mem_iota add0n.
by rewrite H2.
Qed.

Lemma prefixes_num l n  : 
  n < size l -> exists e, (take n l, e) \in prefixes l.
Proof.
move=>D; exists (nth e0 l n); apply/mapP; exists n=>//.
by rewrite mem_iota add0n.
Qed.

Lemma prefV l pr e :
  (pr, e) \in prefixes l -> exists n,
  [/\ pr = take n l, 
      e = (nth e0 l n) & 
      l = pr ++ e :: drop n.+1 l].
Proof.
move=>H; case: (in_prefixes_full H)=>n[G1] G2 G3.
exists n; rewrite G2; split=>//; rewrite G3. 
by move: (take_nth_drop G1); rewrite G2=>->.
Qed.

Lemma prefix_rev l1 l2 l et e :
  e \in l2 -> l = l1 ++ et :: l2  ->
  exists i, (take i l, e) \in prefixes l /\ et \in take i l.
Proof.
case/splitP=>{l2}l2 l3.
rewrite -cat_cons -cats1 cat_cons -catA cat1s -cat_cons catA.
set i := size (l1 ++ et :: l2); move=>E; exists i.
have X1 : e \in l by rewrite E mem_cat inE eqxx orbC.  
have X2: i < size l
  by rewrite/i E!size_cat -addnA ltn_add2l -{1}[size (_::l2)]addn0 ltn_add2l. 
have Y: forall a, a - a = 0 by elim.
have X3: nth e0 l i = e by rewrite E nth_cat /i ltnn Y/=. 
split; last by rewrite E take_size_cat /i// mem_cat inE eqxx orbC.
apply/mapP; exists i; last by rewrite X3.
by rewrite mem_iota add0n.
Qed.

(* A helper lemma abot prefixes *)

Lemma in_prefix_cons l e pre pi : 
  (pre, pi) \in prefixes (e :: l) ->  
  (pre, pi) = ([::], e) \/ exists l1, pre = e :: l1.
Proof.
case/mapP=>n H1 H2; rewrite /= inE in H1.
case/orP: H1=>[|H1]; [by move/eqP=>Z; subst n; left|right]. 
rewrite mem_iota in H1; case/andP: H1=>H G.
have S: exists m, n = m.+1 by clear G H2; case: n H=>//n _; exists n.
by case: S=>[m]Z; subst n; case: H2=>/=-> _; exists (take m l).
Qed.

(* More helper lemmas *)

Lemma seq_iota_add {A : Type } (f g : nat -> A) m n : (forall i, f (i + m) = g i) ->
  [seq f i | i <- iota m n] = [seq g i | i <- iota 0 n].
Proof.
move=>H.
elim: n=>//n Hi.
rewrite -![n.+1]addn1 !iota_add !map_cat; congr (_ ++ _)=>//={Hi}.
by rewrite add0n addnC H. 
Qed.

Lemma seq_iota_inc {A : Type } (f g : nat -> A) n : (forall i, f i.+1 = g i) ->
  [seq f i | i <- iota 1 n] = [seq g i | i <- iota 0 n].
Proof. by move=>H; apply: seq_iota_add=>i; rewrite addn1. Qed.


Lemma prefix_cons e l  : 
  prefixes (e :: l) = 
  ([::], e) :: [seq (e :: pe.1, pe.2) | pe <- prefixes l].
Proof.
congr (_ :: _); rewrite /prefixes -seq.map_comp.
by apply: seq_iota_inc. 
Qed.

Lemma prefix_catl l1 l2  : 
  prefixes (l1 ++ l2) = 
  prefixes l1 ++ [seq (l1 ++ pe.1, pe.2) | pe <- prefixes l2].
Proof.
rewrite /prefixes size_cat iota_add add0n map_cat; congr (_ ++ _).
- apply/eq_in_map=>i; rewrite mem_iota add0n=>/andP[]_ N. 
  by rewrite take_cat nth_cat !N/=.
rewrite -seq.map_comp; apply: seq_iota_add=>i/=. 
have X a : a - a = 0 by elim: a.
case: i=>[|i]; first by rewrite add0n take_cat nth_cat !ltnn !X.
have Y: i.+1 + size l1 < size l1 = false
     by rewrite -[i.+1]addn1 addnC -{2}[size l1]addn0 ltn_add2l.  
by rewrite take_cat nth_cat !Y -!addnBA ?X ?addn0=>//.
Qed.

Lemma prefix_snd l : map snd (prefixes l) = l.
Proof.
rewrite /prefixes -seq.map_comp/=.
suff X: l = [seq nth e0 l i | i <- iota 0 (size l)]
        by rewrite {4}X; apply/eq_in_map=>i D/=.
elim: l=>//e l/= Hi; congr (_ :: _).
by rewrite {1}Hi; apply/sym; apply:(seq_iota_inc).
Qed.

Lemma count_comp {A B : eqType} (f : B -> bool) g (l : seq A) :
  count (f \o g) l = count f (map g l).
Proof. by rewrite count_map. Qed.

Lemma find_first {A: eqType} (l : seq A) f : has f l ->
  exists e l1 l2, [/\ l = l1 ++ e :: l2, f e & ~~ has f l1].
Proof.
elim:l=>//= e l Hi; case X : (f e)=>/=.
- by move=> _; exists e, [::], l; rewrite cat0s.
case/Hi=>e'[l1][l2][E1]H1 H2.
by exists e', (e:: l1), l2; rewrite E1/= X H2/= H1. 
Qed.


(***************************************************************************)
(*                              Wavefronts                                 *)
(***************************************************************************)


(* Definition of a wavefront *)
Definition wavefront (l : log) := 
  [seq (source pi, fld pi) | pi <- l & kind pi == T].

Lemma prefix_wavefront l1 l2 l et e :
  e \in l2 -> l = l1 ++ et :: l2  -> kind et == T ->
  exists pre, (pre, e) \in prefixes l /\ 
              (source et, fld et) \in (wavefront pre).
Proof.
move=>H1 H2 T; case:(prefix_rev H1 H2)=>i[H3 H4].
exists (take i l); split=>//.
by apply/mapP; exists et=>//; rewrite mem_filter T. 
Qed.

Lemma wavefront_trace l o : o \in wavefront l ->
   exists (e : LogEntry) (l1 l2 : seq LogEntry),
     [/\ l = l1 ++ e :: l2, kind e == T, source e = o.1 & fld e = o.2].
Proof.
case/mapP=>e; rewrite mem_filter=>/andP[H1].
by case/in_split=>l1[l2][E]->/=; exists e, l1, l2.
Qed.

Lemma wavefront_filterT et l f o g :
  kind et = T -> fld et = f ->  source et = o -> 
  count (fun pe : log * LogEntry =>
      (g pe.2) && ((o, f) \in wavefront pe.1))
      [seq (et :: pe.1, pe.2) | pe <- prefixes l] = 
  count (fun pe => g pe.2) (prefixes l).
Proof.
move=>H1 H2 H3; rewrite count_map; apply: eq_in_count=>/=pe H.
by rewrite andbC /wavefront /= H1 /= H2 H3/= inE eqxx.
Qed.

End Wavefronts.

