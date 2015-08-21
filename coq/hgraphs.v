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


(* Allocate a new object with the id x (also serves as its pointer) *)
(* fnum is the number of its fields  *)

Definition alloc h (x : ptr) (fnum : nat) := 
   let: fs := ncons fnum null [::]
   in   x :-> fs \+ h.

(* Auxiliary lemma *)
Lemma ncons_elem (T : ordType) n (z e : T) : z \in ncons n e [::] ->  z = e.
Proof.
by elim: n=>//= n Hi; rewrite inE=>/orP []//; move/eqP.
Qed.

(* Now we prove that the allocation of a fresh pointer preserves *)
(* graph-ness. *)
Lemma allocG h (g : graph h) x fnum : 
  x != null -> x \notin dom h -> graph (alloc h x fnum).
Proof.
move=> N Ni; rewrite /alloc; split=>[|y D].
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





