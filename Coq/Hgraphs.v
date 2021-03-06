From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep pred prelude idynamic ordtype pcm finmap unionmap heap coding. 
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 


(*******************************************************************************)
(* Implementation of object graphs and graph-manipulating machinery,
   such as allocation and modification. *)
(*******************************************************************************)

Section GraphDefinitions.

Variable node : ordType. (* type of nodes *)
Variable edge : node -> pred node.

End GraphDefinitions.

(* We implement field mapping as a list of pointers *)
Definition graph (h : heap) := 
  valid h /\ 
  forall x, x \in dom h -> 
    exists (fs : seq ptr) (d: bool),
      h = x :-> (fs, d) \+ free x h /\
      {subset fs <= [predU pred1 null & dom h]}. 

Local Notation ptr_set := (@union_map [ordType of ptr] unitSet).

Section HeapGraphs.
Variables (h : heap) (g : graph h).

Lemma contents_pfx (x : ptr) v : 
        find x h = Some v -> idyn_tp v = ((seq ptr) * bool)%type. 
Proof. 
move=>F; case/find_some/(proj2 g): F (F)=>xs[d][E] _.
by move: (proj1 g); rewrite E => V; rewrite hfindPtUn //; case=><-.
Qed.

(* the contents of node x; that is, the mark bit and edges of x *)

Definition contents (x : ptr) : (seq ptr) * bool := 
  match find x h as f return _ = f -> _ with
    Some v => fun epf => icoerce id (idyn_val v) (contents_pfx epf)
  | None => fun epf => ([::], false)
  end (erefl _).

CoInductive contents_spec (x : ptr) : bool -> (seq ptr) * bool -> Type := 
| has_some (xsd : seq ptr * bool) of 
    h = x :-> xsd \+ free x h & valid h & 
    x \in dom h & {subset xsd.1 <= [predU pred1 null & dom h]} :
    contents_spec x true xsd
| has_none of x \notin dom h : contents_spec x false ([::], false). 

Lemma edgeP x : contents_spec x (x \in dom h) (contents x).  
Proof.
case: (g) => V G; case Dx : (x \in dom h); last first.
- case: {G} dom_find (Dx)=>// N _.
  rewrite /contents; move: (@contents_pfx x); rewrite N /= => _.
  by apply: has_none; rewrite Dx. 
suff [Ex S] : h = x :-> (contents x) \+ free x h /\
              {subset (contents x).1 <= [predU pred1 null & dom h]}. 
- by apply: has_some=>//; rewrite -Ex.
case/G: {G} Dx=>xs'[d'][E'] S.
rewrite /contents; move: (@contents_pfx x). 
rewrite E' hfindPtUn -E'//==>Ex.
by rewrite !ieqc /=.  
Qed.

(* the edge relation of a graph *)

Definition edge x := 
  [pred y | [&& x \in dom h, y != null & 
    let: xs := (contents x).1 in y \in xs]].

(* Reachability *)
Definition reachable x y :=
  x \in dom h -> y \in dom h ->
  exists p, path edge x p /\ last x p = y.

End HeapGraphs.

Notation fields g x := (@contents _ g x).1.

(* Whether an object is D-protected *)
Notation dprot g x := (@contents _ g x).2.

Lemma graphPt z h (g: graph h) : 
  z \in dom h -> exists (d : bool),
      h = z :-> (fields g z, d) \+ free z h.
Proof.
move=>D; case: edgeP; last by rewrite D.
move=>[xs]d->V _ _; exists d=>/=; congr (_ \+ _).
by rewrite hfreePtUn.
Qed.

Lemma graphNoPt z h (g: graph h) : 
  z \notin dom h -> (fields g z) = [::].
Proof. by move=>D; case: edgeP=>//; move/negbTE: D=>->. Qed.

(* restating the graph properties in terms of booleans *)

Lemma validG h (g : graph h) : valid h.
Proof. by case: g. Qed.

Lemma edgeE h (g : graph h) h' x c : 
        h = x :-> c \+ h' -> contents g x = c.
Proof.
case: edgeP; first by move=>xs -> V Dx _ /(hcancelV V) []. 
by move=>Dx E; rewrite E hdomPtUn inE eq_refl /= andbT -E (validG g) in Dx.
Qed.

Implicit Arguments edgeE [h g h' x c].

Lemma edgeG h (g : graph h) x : 
        {subset (fields g x) <= [predU pred1 null & dom h]}.
Proof. by case: edgeP=>//= _ z; rewrite !inE orbb=>->. Qed.

Require Import Coq.Logic.ProofIrrelevance.
Lemma eqG h1 (g1 : graph h1) h2 (g2 : graph h2) x : 
        h1 = h2 -> contents g1 x = contents g2 x.
Proof. by move=>E; rewrite -E in g2 *; rewrite (proof_irrelevance _ g1 g2). Qed.


(******************************************************************)
(*    Manipulating heap graphs: allocation and field update       *)
(******************************************************************)


(* Auxiliary lemmas *)
Lemma ncons_elem (T : ordType) n (z e : T) : z \in ncons n e [::] ->  z = e.
Proof.
by elim: n=>//= n Hi; rewrite inE=>/orP []//; move/eqP.
Qed.


Lemma ncons_elems (T : ordType) n (z e : T) xs: 
  z \in ncons n e xs ->  z = e \/ z \in xs.
Proof.
elim: n=>/=[|n Hi]; first by right.
by rewrite inE=>/orP []//; move/eqP; left.
Qed.

Lemma set_nth_elems z fs fld new:
  z \in set_nth null fs fld new -> [\/ z == null, z == new | z \in fs].
Proof.
elim: fs fld=>[fld|x xs H].
- by rewrite set_nth_nil; move/ncons_elems; rewrite inE; case=>->;
  [constructor 1 | constructor 2].
elim=>[|n Hi G].
- rewrite inE=>/orP. 
  case; first by move/eqP=>->; constructor 2.
  by move=>J; constructor 3; rewrite inE J orbC.
rewrite inE in G; case/orP: G.
- by move/eqP=>->; constructor 3; rewrite inE eq_refl.
move/H; case; do?[move/eqP=>->].
- by constructor 1.
- by constructor 2.
by move=>G; constructor 3; rewrite inE; apply/orP; right.
Qed.

Lemma notin_eq (x y : ptr) (h : heap) : 
      y \notin dom h -> x \in dom h -> x != y.
Proof.
by case B: (x==y)=>//; move/eqP: B=>B; subst y; move/negbTE=>->.
Qed.

(***********************************************************************)
(* Modify an existing object x's field fld in the heap and return the  *)
(* pair (new_heap, old_heap_value)                                     *) 
(***********************************************************************)

Definition modify h (g: graph h) (x : ptr) (fld : nat) (new : ptr) := 
  if x \in dom h 
  then let: fs := (contents g x).1 in
       let: d  := (contents g x).2 in
       if size fs <= fld then h
       else x :-> (set_nth null fs fld new, d) \+ free x h
  else h.

(* Modify preserves the graph-ness *)
(*

The following lemma will serve as a "proxy" when executing logs wrt. a
specific heap. Therefore, even though the definition of modify by
itself doesn't require that "(x \in dom h)", we put it into the lemma
anyway, making the clients satisfy it. The same applies for the trace
funciton defined below.

*)


(* [TODO]: Probably, I should refactor all these non used so far side
   conditions into some additional structure. *)

Lemma modifyG h (g : graph h) x fld old new : 
  let: res := modify g x fld new in
    (x \in dom h) && 
    ((new \in dom h) || (new == null)) &&
    ((fld < size (fields g x)) &&  
     ((old \in [predU pred1 null & dom h]) &&
     ((nth null (contents g x).1 fld) == old))) ->
  graph res.
Proof.
move=>Dn; rewrite /modify; case: ifP=>Dx//=; case: ifP=>_//=.
split=>[|y].
- move: ((proj2 g) x Dx)=>[fs][d][E _]; rewrite !hvalidPtUn.
  move: (proj1 g)=>V; rewrite E hfreePtUn; last by rewrite E in V.
  rewrite E in V; move/hvalidPt_cond: (V)=>->/=.
  by move/validR: V=>->; rewrite domF inE eq_refl. 
move=> Dy; rewrite hdomPtUn inE in Dy.
case/andP: Dy=>V'/orP; case=>[/eqP Z|Dy].
- subst y; exists (set_nth null (fields g x) fld new), (contents g x).2.
  rewrite hfreePtUn; last first; [| split=>//].
  + rewrite hvalidPtUn; move/hvalidPt_cond: (V')=>->/=.
    by move/validR: (V')=>->; rewrite domF inE eq_refl.   
- move=>z G; rewrite inE /= inE/=; apply/orP.
  rewrite hdomPtUn inE V'/=.
  move: ((proj2 g) _ Dx)=>[fs][d][E]G'; rewrite (edgeE E) in G.
  move:(G' z)=>{G'}G'; move/set_nth_elems: G.
  case; first by move=>->; left.
  + move/eqP=>Z; subst new. 
    case/andP: Dn; case/andP=> _; case/orP; last by move=>-> _; left.
    by move=>D; right; rewrite domF inE; case X: (x == z).
  move/G'; rewrite inE/=inE=>/orP; case; first by left.
  by rewrite domF inE=>->; right; case X: (x == z).

have Y: y == x = false by apply/eqP =>E; rewrite domF inE E eq_refl in Dy.
have Dy': y \in dom h by rewrite domF inE eq_sym Y in Dy.
move/(graphPt g): (Dy')=>[d]E.
exists (fields g y), d; split.

- rewrite hfreePtUn2=>//; rewrite Y/=; rewrite joinCA/=; congr (_ \+ _).
  rewrite {1}E hfreePtUn2; last by move: (proj1 g); rewrite {1} E.
  by rewrite eq_sym Y freeF eq_sym Y.

move=>z; rewrite !inE hdomPtUn inE V'/=.
case: edgeP=>[fs E' _ _ /(_ z)|]; last by rewrite Dy'.
move=>H Dz; move/H :Dz; rewrite !inE=>/orP; case; first by move=>->.
move=>Dz; rewrite domF inE; case X: (x == z); apply/orP.
- by constructor 2.
by right; rewrite Dz orbC.
Qed.

Lemma modifyDom h (g : graph h) x fld new : 
  dom h =i dom (modify g x fld new).
Proof.
rewrite /modify; case: ifP=>//D; case: ifP=>//H z.
have V: valid (x :-> (set_nth null (fields g x) fld new, (contents g x).2) \+
                 free x h).
- move: ((proj2 g) x D)=>[fs][d][E _]; rewrite !hvalidPtUn.
  move: (proj1 g)=>V; rewrite E hfreePtUn; last by rewrite E in V.
  rewrite E in V; move/hvalidPt_cond: (V)=>->/=.
  by move/validR: V=>->; rewrite domF inE eq_refl. 
rewrite hdomPtUn !inE /= domF inE V.  
by case Y: (x == z)=>//=; move/eqP: Y=>Y; subst z; rewrite D.
Qed.

(***********************************************************************)
(* Allocate a new object with the id x (also serves as its pointer)    *)
(* fnum is the number of its fields, and assign it to a field of and   *)
(* existing object in the heap.                                        *)
(***********************************************************************)

(* First, we define the "pure" allocation, without assignment *)
Definition pre_alloc h (x : ptr) (fnum : nat) := 
   if (x != null) && (x \notin dom h) 
   then let: fs := ncons fnum null [::] in x :-> (fs, false) \+ h
   else h.

(* Now we prove that the pre-allocation of a fresh pointer preserves *)
(* graph-ness. *)
Lemma pre_allocG h (g : graph h) x fnum : graph (pre_alloc h x fnum).
Proof.
rewrite /pre_alloc; case X: ((x != null) && (x \notin dom h))=>//.
case/andP: X=> N Ni; rewrite /pre_alloc; split=>[|y D].
- by rewrite hvalidPtUn N Ni/=; case: g=>->. 
case:g=>V /(_ y) H; rewrite hdomPtUn inE in D.
case/andP: D=>V' /orP; case=>[/eqP Z|D].
- subst y; exists (ncons fnum null [::]), false; split.
  + by rewrite (@hfreePtUn _ _ _ _ V').
  by move=>z /ncons_elem->.
move/H: (D)=>[fs][d]{H}[E H]; exists fs, d; split; last first.
- move=>z /(H z); rewrite !inE/= !inE hdomPtUn !inE V'/=.
  by case/orP=>->//=; apply/or3P; constructor 3.
rewrite freeUnL; last first.
- rewrite hdomPt inE N/=; apply/eqP=>G; subst y. 
  by move/negbTE: Ni; rewrite D.
by rewrite joinA -[_\+x:->_]joinC -joinA; congr (_ \+ _).
Qed.

Lemma pre_allocDom h (g : graph h) x fnum : 
  (x != null) && (x \notin dom h) -> 
  x :: keys_of h =i keys_of (pre_alloc h x fnum).
Proof.
move=>X; move: (pre_allocG g x fnum)=>g'.
case/andP: X g'=>N Ni.
rewrite /pre_alloc N Ni/==>g' z; rewrite !inE keys_dom eq_sym.
by rewrite keys_dom hdomPtUn inE (proj1 g')/=.
Qed.

(* Now, the full-blown allocation and assignment. *)
Definition alloc h (g: graph h) y fnum x fld := 
  modify (pre_allocG g y fnum) x fld y.

Lemma allocDom h (g : graph h) y fnum x fld : 
  {subset dom h <= dom (alloc g y fnum x fld)}.
Proof.
move=>z D. rewrite /alloc.
rewrite -(modifyDom (pre_allocG g y fnum) x fld y).
rewrite /pre_alloc; case X: ((y != null) && (y \notin dom h))=>//.
rewrite hdomPtUn !inE D orbC andbC/=.
by rewrite hvalidPtUn (proj1 g) andbC/= andbC X.
Qed.

Lemma pre_alloc_fields h (g : graph h) n fnum s: 
  s != n ->
  fields (pre_allocG g n fnum) s = fields g s.
Proof.
move/negbTE=>N; set g1 :=  pre_allocG g n fnum; move: g1.
rewrite /pre_alloc; case A: ((n != null) && (n \notin dom h))=>g1; last first.
- by rewrite (proof_irrelevance _ g g1).
case: edgeP; last first.
- move/negbTE.
  rewrite hdomPtUn inE andbC eq_sym N /= (proj1 g1) andbC/= => /negbT.
  by move/(graphNoPt g)=>->.
move=>xs E1 V D _.
rewrite hfreePtUn2// N/= joinA [s :-> _ \+ _]joinC -joinA in E1.
by case: (hcancelV V E1)=>_ V' E2; rewrite (@edgeE h g _ _ _ E2).
Qed.

Lemma allocG h (g: graph h) y fnum x fld old new :            
  let: res := alloc g y fnum x fld in
  (y != null) && (y \notin dom h) &&
  (x \in dom h) && (new == y) &&
  ((fld < size (fields g x)) &&  
   ((old \in [predU pred1 null & dom h]) &&
   ((nth null (contents g x).1 fld) == old))) ->
  graph res.
Proof.
move=>pf.
case/andP:(pf)=>/andP[]/andP[]=> pf2 pf3 pf4 pf5.
suff X: (x \in dom (pre_alloc h y fnum)) &&
        ((y \in dom (pre_alloc h y fnum)) || (y == null)) &&
        ((fld < size (fields (pre_allocG g y fnum) x)) &&  
         ((old \in [predU pred1 null & dom (pre_alloc h y fnum)]) &&
         ((nth null (contents (pre_allocG g y fnum) x).1 fld) == old)))
  by apply: (modifyG X).
have X: x != y.
- case B: (x == y)=>//; move/eqP:B=>B; subst y;
  by case/andP: pf=>/andP[]/andP[]/andP[_]/negbTE=>->.
move:(pre_allocG g y fnum) (pre_alloc_fields g fnum X). 
rewrite /pre_alloc pf2/==>g' E.
suff F: fld < size (fields g' x).
suff P: nth null (fields g' x) fld == old.
- rewrite F P /=; case:(g')=>V' _.
  rewrite inE /= !hdomPtUn !V' !inE !eqxx !(andbC _ true)/=.
  apply/andP; split; first by rewrite pf3 orbC.
  move: pf5. rewrite !inE /= =>/andP[_] /==>/andP[].
  move /orP; case.
  move => old_is_null old_heap; apply /or3P; constructor 1; exact old_is_null.
  move => old_in_dom old_heap; apply /or3P; constructor 3; exact old_in_dom.
  Focus 2. by rewrite E; case/andP: pf5.
  case /and3P: pf5; move => t1 t2 t3; rewrite E; exact t3.
Qed.

(***********************************************************************)
(* Trace a field of an existing object in a heap                       *) 
(***********************************************************************)

Definition trace h (g: graph h) (x : ptr) (fld : nat) := 
  if x \in dom h 
  then let: fs := fields g x
       in   if size fs <= fld then h
            else h
  else h.

(* Tracing (trivially) preserves the graph-ness *)
Lemma traceG h (g : graph h) x fld old new : 
  let: res := trace g x fld in
  (* The are not "safety", but rather "sanity" requirements *)
  (x \in dom h) && (old == new) && 
  ((fld < size (fields g x)) &&
   (old == nth null (fields g x) fld)) -> 
  res = h.
Proof.
by move=>Dn; rewrite /trace; case: ifP=>Dx//=; case: ifP=>_//=.
Qed.

(***********************************************************************)
(*            Invariant lemmas about modify and alloc                  *) 
(***********************************************************************)

(*  Relevant changes due to modifications.  *)

Lemma modify_field h1 (g1 : graph h1) s' f' n o
                   (g : graph (modify g1 s' f' n)) s f: 
  (s' \in dom h1) && ((n \in dom h1) || (n == null)) && 
  ((f' < size (fields g1 s')) &&  
   (o \in [predU pred1 null & dom h1])) -> 
  if (s == s') && (f == f') 
  then nth null (fields g s) f = (if size (fields g1 s) <= f then null else n)
  else nth null (fields g s) f = nth null (fields g1 s) f.
Proof.
move=>C; move: (modifyDom g1 s' f' n)=>K. 
case/andP: C=>/andP [H1 H2] _.
move: g K; rewrite /modify H1; case: ifP=>H3 g K.
- move: (proof_irrelevance _ g g1)=>Z; subst g1.
  case: ifP=>///andP[/eqP E1/eqP E2]; subst s' f'.
  by rewrite (nth_default _ H3) H3.

move: g.
set h := s' :-> (set_nth null (fields g1 s') f' n, (contents g1 s').2)
            \+ free s' h1=>g.
have E1: h = s' :-> (set_nth null (fields g1 s') f' n, (contents g1 s').2)
                \+ free s' h1 by [].
move:(@edgeE h g (free s' h1) _ _ E1)=> E2; case: ifP.
- case/andP=>/eqP Z1/eqP Z2; subst s' f'; rewrite H3 E2.
  by rewrite nth_set_nth/= eqxx.
move/negbT; rewrite negb_and=>/orP H4; apply/sym; case: edgeP; last first.
- case: edgeP=>//[[xs' d']] E3 V D1 _ D2.
  rewrite E1 in D1. move: (K s); rewrite  D1. 
  by move/negbTE: D2=>->.
move=>[xs d] E3 V D G.
case: edgeP=>//; last first.
- by move: (K s); rewrite D=>G'; move/negbTE; rewrite -G'.
move=>[xs' d'] E4 V' D' _.
case X: (s == s'); last first. 

- rewrite hfreePtUn2 // ?X in E4; rewrite {1}E1/= in E4.
  rewrite {3}E3 in E4.
  rewrite hfreePtUn2 ?(eq_sym s') ?X in E4; last by rewrite E3 in V. 
  rewrite joinA -[_ \+ s:->_]joinC -!joinA in E4.
  suff V1: valid (s :-> (xs, d) \+
                    (s' :-> (set_nth null (fields g1 s') f' n,
                             (contents g1 s').2) \+ free s' (free s h1))).
    by case: (hcancelV V1 E4)=>->.
  rewrite E1 {3}E3 hfreePtUn2 ?(eq_sym s') ?X in V'; last by rewrite E3 in V.
  by rewrite joinA -[_ \+ s:->_]joinC -!joinA in V'.

move/eqP:(X)=>Z; subst s'.
rewrite {3}E3 hfreePtUn -?E3 // in E1.
rewrite E4 in V' E1; case: (hcancelV V' E1)=>[][]Z1 Z2 _ _.
subst xs' d'; clear E1.
have D2: s \in dom h1 by rewrite E3 hdomPtUn inE/=-E3 V eqxx.
move: (graphPt g1 D2)=>[d']E5; rewrite {1}E3 in E5; rewrite E3 in V.
case: (hcancelV V E5)=>[][]Z1 Z2 _ _; subst xs d'.
have H5: f != f' by case: H4=>//; move/negbTE; rewrite X.
by move/negbTE: H5=>H5; rewrite nth_set_nth/= H5. 
Qed.

Lemma modify_size h1 (g1 : graph h1) s f n o
                   (g : graph (modify g1 s f n)) o': 
  (s \in dom h1) && ((n \in dom h1) || (n == null)) && 
  ((f < size (fields g1 s)) && (o \in [predU pred1 null & dom h1])) -> 
  size (fields g o') = size (fields g1 o').
Proof.
move=>C; move: (modifyDom g1 s f n)=>K. 
case/andP: C=>/andP [H1 H2] _.
move: g K; rewrite /modify H1; case: ifP=>H3 g K.
- by move: (proof_irrelevance _ g g1)=>Z; subst g1.
move: g; set h := s :-> (set_nth null (fields g1 s) f n,
                           (contents g1 s).2) \+ free s h1=>g.
have E1: h = s :-> (set_nth null (fields g1 s) f n, (contents g1 s).2)
               \+ free s h1 by [].
case A: (s == o').
- move/eqP:A=>A; subst o'.
  move:(@edgeE h g (free s h1) _ _ E1)=>->; apply/sym.
  rewrite size_set_nth; move/negbT: H3; rewrite -ltnNge=>H3.
  case X : (f.+1 == size (fields g1 s)).
  - by move/eqP: X=>->; rewrite /maxn ltnn.
  suff Y: f.+1 < size (fields g1 s) by rewrite /maxn Y.
  by rewrite !ltnNge in H3 *; rewrite leq_eqVlt eq_sym X/= H3.

case B: (o' \in dom h1).
- move: (graphPt g1 B)=>[d]G1. 
  rewrite (K o') in B.
  move/(graphPt g): (B)=>[d']; rewrite /h.
  rewrite hfreePtUn2 -?E1 ?(proj1 g)// eq_sym A joinA [o':-> _ \+_]joinC -joinA=>E.
  move: (proj1 g)=>V; rewrite E1 in V.
  rewrite !{3}G1 hfreePtUn2 -?G1 ?(proj1 g1)//A in V. 
  rewrite !{3}G1 hfreePtUn2 -?G1 ?(proj1 g1)//A in E.
  rewrite !joinA ![s :->_\+_]joinC -!joinA in V E. 
  by case: (hcancelV V E)=>[][]->.

move/negbT: B=>D; rewrite (graphNoPt g1 D).
rewrite (K o') -/h in D.
by rewrite (graphNoPt g D).
Qed.

(*  Relevant changes due to allocations.  *)

Lemma pre_alloc_field h (g : graph h) n fnum s f: 
  nth null (fields (pre_allocG g n fnum) s) f = nth null (fields g s) f.
Proof.
set g1 :=  pre_allocG g n fnum; move: g1.
rewrite /pre_alloc; case A: ((n != null) && (n \notin dom h))=>g1; last first.
- by rewrite (proof_irrelevance _ g g1).
move: (pre_allocDom g fnum A) => K; rewrite /pre_alloc A in K .
case B: (s == n).
- move/eqP: B=>Z; subst s.
  case/andP:A=>A1 A2; move: (graphNoPt g A2)=>->.
  rewrite (edgeE (erefl (n :-> (ncons fnum null [::], false) \+ h))).
  by rewrite nth_ncons; case: ifP=>_; rewrite !nth_nil.
case D: (s \in dom h); last first.
- move/negbT: D=>D.
  rewrite (graphNoPt g D) nth_nil.
  have X: s \notin dom (n :-> (ncons fnum null [::], false) \+ h)
    by rewrite -!keys_dom -K inE B keys_dom; move/negbTE: D=>->.
  by rewrite (graphNoPt g1 X) nth_nil.
apply/sym; case: edgeP; last by move/negbTE; rewrite D.
move=>xs E V _ S; move:g1; rewrite E=>g1.
case: edgeP; last first.
- rewrite joinC -joinA hdomPtUn inE eqxx/=.
  by rewrite joinC -joinA in g1; rewrite (proj1 g1).
move=>xs' E2 V2 D2 _.
rewrite hfreePtUn2// B /=in E2.
rewrite [n :-> _ \+ _]joinC -joinA in V2 E2.
by case: (hcancelV V2 E2)=>->.
Qed.

(*  Relevant changes due to allocation of new objects.  *)

Lemma alloc_field h1 (g1 : graph h1) s' f' fnum n o
                   (g : graph (alloc g1 n fnum s' f')) s f: 
  (n != null) && (n \notin dom h1) && (s' \in dom h1) &&
  ((f' < size (fields g1 s')) && (o \in [predU pred1 null & dom h1])) ->
  if (s == s') && (f == f') 
  then nth null (fields g s) f = (if size (fields g1 s) <= f then null else n)
  else nth null (fields g s) f = nth null (fields g1 s) f.
Proof.
move: g; rewrite /alloc. 
set g2 := (pre_allocG g1 n fnum); rewrite /g2=>g C.
case/andP: (C)=>/andP[C1]C2 C3; move: (@pre_allocDom h1 g1 n fnum C1)=>P.

have X1: n \in dom (pre_alloc h1 n fnum) by rewrite -keys_dom -P inE eqxx.
have X2: s' \in dom (pre_alloc h1 n fnum)
         by rewrite -keys_dom -P inE keys_dom C2 orbC.
have X3: (o \in [predU pred1 null & dom (pre_alloc h1 n fnum)]).
  move:C3; rewrite !inE/==>/andP[_]/orP; rewrite !inE/=. 
  case; first by move=>->.
  by rewrite -!keys_dom -P inE=>->; rewrite -2!(orbC true).
have X3' : (f' < size (fields (pre_allocG g1 n fnum) s')).
  rewrite pre_alloc_fields; first by case/andP:C3.
  by case/andP:C=>/andP[]/andP[_]A1 A2 _; apply: (@notin_eq _ _ h1)=>//.
have X4:  (s' \in dom (pre_alloc h1 n fnum)) && 
          ((n \in dom (pre_alloc h1 n fnum)) || (n == null)) && 
          ((f' < size (fields (pre_allocG g1 n fnum) s')) &&
           (o  \in [predU pred1 null & dom (pre_alloc h1 n fnum)])).
          by rewrite X1 X2 X3 X3'.
move: (modify_field g  s f X4); rewrite (pre_alloc_field g1 n fnum s f).
case: ifP=>//X.
case/andP: X=>/eqP Z1 /eqP Z2; subst f' s'=>->.
case/andP: C1=>_/negbTE C1.
suff N: s != n by rewrite (pre_alloc_fields g1 fnum N).
by move/negbT: C1=>C1; apply: (@notin_eq _ _ h1).
Qed.

Lemma alloc_size h1 (g1 : graph h1) s f fnum n o
                   (g : graph (alloc g1 n fnum s f)) o':
  (n != null) && (n \notin dom h1) && (s \in dom h1) &&
  ((f < size (fields g1 s)) && (o \in [predU pred1 null & dom h1])) ->
  o' \in dom h1 ->
  size (fields g o') = size (fields g1 o').
Proof.
move: g; rewrite /alloc. 
set g2 := (pre_allocG g1 n fnum); rewrite /g2=>g C.
case/andP: (C)=>/andP[C1]C2 C3; move: (@pre_allocDom h1 g1 n fnum C1)=>P.
have X1: n \in dom (pre_alloc h1 n fnum) by rewrite -keys_dom -P inE eqxx.
have X2: s \in dom (pre_alloc h1 n fnum)
         by rewrite -keys_dom -P inE keys_dom C2 orbC.
have X3: o \in [predU pred1 null & dom (pre_alloc h1 n fnum)].
  move:C3; rewrite !inE/==>/andP[_]/orP; rewrite !inE/=. 
  case; first by move=>->.
  by rewrite -!keys_dom -P inE=>->; rewrite -2!(orbC true).
have X3' : (f < size (fields (pre_allocG g1 n fnum) s)).
  rewrite pre_alloc_fields; first by case/andP:C3.
  by case/andP:C=>/andP[]/andP[_]A1 A2 _; apply: (@notin_eq _ _ h1)=>//.
have X4:  (s \in dom (pre_alloc h1 n fnum)) && 
          ((n \in dom (pre_alloc h1 n fnum)) || (n == null)) && 
          ((f < size (fields (pre_allocG g1 n fnum) s)) &&
           (o  \in [predU pred1 null & dom (pre_alloc h1 n fnum)])).
          by rewrite X1 X2 X3 X3'.

move: (modify_size g o' X4)=>->D; apply/sym.
suff N: o' != n by rewrite (pre_alloc_fields g1 fnum N).
case B: (o' == n)=>//; move/eqP: B=>Z; subst o'.
by case/andP:C1=>_ /negbTE; rewrite D.
Qed.

(************************************************************************)
(*                   [Sanity Constraints]                               *)
(************************************************************************)

(*

In the development of the mutator/collector actions, along with the
definition of GC logc from the file logs.v, we exercise a curious pattern.

Specifically, we define the functions, such as alloc, trace and modify
to be almost-total: they don't even require the target pointer to be
in the heap and return the "default" result. 

However, these function are used only together with the accompanying
*G-lemmas, which proved an "abstract view" on the modification in the
graph topology, resulting from the application of the
heap-manipulating code. This is, in some sence, reminiscent to the
heap/math dichotomy observed previoiusly, so the actual activity
happens on the level of *graphs*, instead of the level of *heaps*.

Furthermore, the same "abstract graph view" *G-lemmas serve an
additional purpose to impose extra conditions on the values, involved
into the heap manipulation, even though these values might be
irrelevant for the exectuoin of a heap-manipulating procedure. For
instance, the "traceG" lemma imposes a "sanity" requirements on x, old
and new values:

(x \in dom h) && (old == new) && (old \in [predU pred1 null & dom h])

However, the trace procedure itself is agnostic wrt. to these
values. So, why we need them? 

The answer is that we want to ensure that clients only use them in
this specific setting. For example, take the function "executeLog"
from the logs.v file. It's written in a "failure-passing" CPS,
incorporating the boolean reflection on the conditions to be
checked. These conditions are inferred by Coq automatically from the
types of lemmas that actually implement the "operational content",
e.g., traceG, modifyG, etc. Employing these lemmas enforces the check
for sanity conditions. 

As the final client of this approach, let's take a look at the
"goodToExecute" theorem, which states, when a log is safe to execute
wrt. to a specific heap without actually executing it. Had we
forgotten some of the conditions in the definition "goodLog", we
wouldn't able to prove the theorem. And these conditions ensure that
the log is adequate wrt. the heap evolution.

A particularly peculiar case is the tracing transition. The transition
by itself doesn't change the graph topology: it merely examines its
contents. However, as it's being reflected in the GC log, its
view-lemma "traceG" ensures that the old and the new elements are the
same. In some sense, this lemma serves as a "rich specification" for
the actual procedure.  It also enforces some sanity conditions, which
are to be enforced when executing the appropriate log entry.

*)
