Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat.
Require Import Ssreflect.eqtype Ssreflect.ssrfun Ssreflect.seq.
Require Import MathComp.path.
Require Import Eqdep pred idynamic ordtype pcm finmap unionmap heap coding. 
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Section GraphDefinitions.

Variable node : ordType. (* type of nodes *)
Variable edge : node -> pred node.

End GraphDefinitions.

(* We implement field mapping as a list of pointers *)
Definition graph (h : heap) := 
  valid h /\ 
  forall x, x \in dom h -> 
    exists (fs : seq ptr),
      h = x :-> fs \+ free x h /\
      {subset fs <= [predU pred1 null & dom h]}. 

Local Notation ptr_set := (@union_map [ordType of ptr] unitSet).

Section HeapGraphs.
Variables (h : heap) (g : graph h).

Lemma contents_pfx (x : ptr) v : 
        find x h = Some v -> idyn_tp v = seq ptr. 
Proof. 
move=>F; case/find_some/(proj2 g): F (F)=>xs[E] _.
by move: (proj1 g); rewrite E => V; rewrite hfindPtUn //; case=><-.
Qed.

(* the contents of node x; that is, the mark bit and edges of x *)

Definition contents (x : ptr) : seq ptr := 
  match find x h as f return _ = f -> _ with
    Some v => fun epf => icoerce id (idyn_val v) (contents_pfx epf)
  | None => fun epf => [::]
  end (erefl _).

CoInductive contents_spec (x : ptr) : bool -> seq ptr -> Type := 
| has_some (xs : seq ptr) of 
    h = x :-> xs \+ free x h & valid h & 
    x \in dom h & {subset xs <= [predU pred1 null & dom h]} :
    contents_spec x true xs
| has_none of x \notin dom h : contents_spec x false [::]. 

Lemma edgeP x : contents_spec x (x \in dom h) (contents x). 
Proof.
case: (g) => V G; case Dx : (x \in dom h); last first.
- case: {G} dom_find (Dx)=>// N _.
  rewrite /contents; move: (@contents_pfx x); rewrite N /= => _.
  by apply: has_none; rewrite Dx. 
suff [Ex S] : h = x :-> (contents x) \+ free x h /\
              {subset (contents x) <= [predU pred1 null & dom h]}. 
- by apply: has_some=>//; rewrite -Ex.
case/G: {G} Dx=>xs'[E'] S.
rewrite /contents; move: (@contents_pfx x).
rewrite E' hfindPtUn -E'// =>Ex.
by rewrite !ieqc /=.  
Qed.

(* the edge relation of a graph *)

Definition edge x := 
  [pred y | [&& x \in dom h, y != null & 
    let: xs := contents x in y \in xs]].

(* graph is connected from x if it has a path from x to every other node *)
Definition connected x :=
  forall y, y \in dom h -> exists p, path edge x p /\ last x p = y.

End HeapGraphs.

Notation fields g x := (@contents _ g x).

Lemma graphPt z h (g: graph h) : 
  z \in dom h -> h = z :-> (fields g z) \+ free z h.
Proof. by move=>D; case: edgeP; last by rewrite D. Qed.

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

(* Allocate a new object with the id x (also serves as its pointer) *)
(* fnum is the number of its fields  *)

Definition alloc h (x : ptr) (fnum : nat) := 
   let: fs := ncons fnum null [::]
   in   x :-> fs \+ h.

(* Now we prove that the allocation of a fresh pointer preserves *)
(* graph-ness. *)
Lemma allocG h (g : graph h) x fnum : 
  (x != null) && (x \notin dom h) -> 
  graph (alloc h x fnum).
Proof.
case/andP=> N Ni; rewrite /alloc; split=>[|y D].
- by rewrite hvalidPtUn N Ni/=; case: g=>->. 
case:g=>V /(_ y) H; rewrite hdomPtUn inE in D.
case/andP: D=>V' /orP; case=>[/eqP Z|D].
- subst y; exists (ncons fnum null [::]); split.
  + by rewrite (@hfreePtUn _ _ _ _ V').
  by move=>z /ncons_elem->.
move/H: (D)=>[fs]{H}[E H]; exists fs; split; last first.
- move=>z /(H z); rewrite !inE/= !inE hdomPtUn !inE V'/=.
  by case/orP=>->//=; apply/or3P; constructor 3.
rewrite freeUnL; last first.
- rewrite hdomPt inE N/=; apply/eqP=>G; subst y. 
  by move/negbTE: Ni; rewrite D.
by rewrite joinA -[_\+x:->_]joinC -joinA; congr (_ \+ _).
Qed.


(* Modify an existing object x's field fld in the heap and return the
pair (new_heap, old_heap_value) *)

Definition modify h (g: graph h) (x : ptr) (fld : nat) (new : ptr) := 
  if x \in dom h 
  then let: fs := contents g x
       in   if size fs <= fld then (h, null)
            else let: h' := x :-> set_nth null fs fld new \+ free x h
                 in   (h', nth null fs fld)  
  else (h, null).

(* Modify preserves the graph-ness *)
Lemma modifyG h (g : graph h) x fld new : 
  let: res := modify g x fld new in
  (new \in dom h) || (new == null) -> 
  graph res.1 /\ (res.2 \in [predU pred1 null & dom h]).
Proof.
move=>Dn; rewrite /modify; case: ifP=>Dx//=; case: ifP=>_//=.
split; last first. 
- case: edgeP; last by rewrite Dx.
  move=>xs _ _ _ H.
  case X: (fld < size xs); first by apply: (H _ (mem_nth _ X)).
  + move/negbT: X=>X; rewrite -ltnNge /= in X.
  by rewrite (nth_default null X) inE/=.
split=>[|y].
- move: ((proj2 g) x Dx)=>[fs][E _]; rewrite !hvalidPtUn.
  move: (proj1 g)=>V; rewrite E hfreePtUn; last by rewrite E in V.
  rewrite E in V; move/hvalidPt_cond: (V)=>->/=.
  by move/validR: V=>->; rewrite domF inE eq_refl. 
move=> Dy; rewrite hdomPtUn inE in Dy.
case/andP: Dy=>V'/orP; case=>[/eqP Z|Dy].
- subst y; exists (set_nth null (fields g x) fld new).
  rewrite hfreePtUn; last first; [| split=>//].
  + rewrite hvalidPtUn; move/hvalidPt_cond: (V')=>->/=.
    by move/validR: (V')=>->; rewrite domF inE eq_refl. 
  
- move=>z G; rewrite inE /= inE/=; apply/orP.
  rewrite hdomPtUn inE V'/=.
  move: ((proj2 g) _ Dx)=>[fs][E]G'; rewrite (edgeE E) in G.
  move:(G' z)=>{G'}G'; move/set_nth_elems: G.
  case; first by move=>->; left.
  + move/eqP=>Z; subst new. case/orP: Dn; last by move=>->; left.
    by move=>D; right; rewrite domF inE; case X: (x == z).
  move/G'; rewrite inE/=inE=>/orP; case; first by left.
  by rewrite domF inE=>->; right; case X: (x == z).

have Y: y == x = false by apply/eqP =>E; rewrite domF inE E eq_refl in Dy.
have Dy': y \in dom h by rewrite domF inE eq_sym Y in Dy.
move/(graphPt g): (Dy')=>E.
exists (fields g y); split.

- rewrite hfreePtUn2=>//; rewrite Y/=; rewrite joinCA; congr (_ \+ _).
  rewrite {1}E hfreePtUn2; last by move: (proj1 g); rewrite {1} E.
  by rewrite eq_sym Y freeF eq_sym Y.

move=>z; rewrite !inE hdomPtUn inE V'/=.
case: edgeP=>[fs E' _ _ /(_ z)|]; last by rewrite Dy'.
move=>H Dz; move/H :Dz; rewrite !inE=>/orP; case; first by move=>->.
move=>Dz; rewrite domF inE; case X: (x == z); apply/orP.
- by constructor 2.
by right; rewrite Dz orbC.
Qed.