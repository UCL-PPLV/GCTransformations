Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat.
Require Import Ssreflect.eqtype Ssreflect.ssrfun Ssreflect.seq.
Require Import MathComp.path.
Require Import Eqdep pred idynamic ordtype pcm finmap unionmap heap coding. 
Require Import hgraphs.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 


(* Implementation of the mutator/collector logs and their execution *)
Section CollectorLog.

Inductive ActionKind : Set := T | M | A of nat.

Record LogEntry : Set := Entry {
  kind    : ActionKind;
  source  : ptr;
  fld     : nat;
  old     : ptr;
  new     : ptr }.

Definition log := seq LogEntry.

(* A set of pointers *)
Definition ptr_set := ptrmap_pcm_Encoded unit_st_Encoded.

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
  c -> exists pf, condK g f = f pf.
Proof.
rewrite /condK=>X; by suff Z: c = true by subst c; eexists.
Qed.

(*

The following function executeLog is partial and certified:

- If it returns None, then something must have gone wrong, because the
  log was malformed (TODO: define a check for good logs).

- If the result is Some (h, g), then h is the resulting heap and g is
  its new graph certificate, which is threaded through the execution.

*)

Record ExecuteResult := ExRes {hp : heap; gp : graph hp}.

Fixpoint executeLog (h : heap) (g : graph h) (l : log) : 
    option ExecuteResult := match l with 

  (* Empty log - return heap and its graph certificate *)    
  | [::] => Some (ExRes g)

  (* Check for allocation with new graph certificate *)
  | (Entry (A fnum) x _ _ _) :: ls => 
      condK (@allocG h g x fnum) (fun g' => executeLog g' ls)

  (* Check for modification with new graph certificate *)
  | (Entry M x fld old new) :: ls =>
      condK (@modifyG h g x fld new) (fun pf => executeLog (proj1 pf) ls)
  (* Tracing entry - don nothing *)
  | (Entry T _ _ _ _) :: ls => executeLog g ls
  end.


(* 

We next define the "good" logs, which lead to consistent
executions. The definition is recursive and is parametrized by the set
"obs" of already allocated objects, which also serves as an
accumulator.

 *)


Fixpoint goodLog (obs : seq ptr) (l : log) : bool := match l with 
  (* Empty log is good *)    
  | [::] => true

  (* Allocation *)
  | (Entry (A fnum) x _ _ _) :: ls => 
      (x != null) && (x \notin obs)      && 
      goodLog (x :: obs) ls
      
  (* Modification *)
  | (Entry M x fld old new) :: ls =>
      (old \in [predU pred1 null & obs]) &&
      (new \in [predU pred1 null & obs]) && 
      goodLog obs ls                                  

  (* Tracing entry *)
  | (Entry T x fld old new) :: ls => 
      (old \in [predU pred1 null & obs]) &&
      (new \in [predU pred1 null & obs]) &&
      goodLog obs ls
  end.

Lemma goodEqSub (obs obs' : seq ptr) l :
  obs =i obs' -> goodLog obs l = goodLog obs' l.
Proof.
elim: l obs obs'=>//x ls Hi obs obs' H.
case: x=>//=k x fld old new; case: k=>/=; move: (H old) (H new)=>H2 H3;
rewrite ?inE/= -?H2 -?H3; do? [by congr (_ && _); apply: Hi].
move=>_; rewrite H; do![congr (_ && _)].
by apply: Hi=>z; rewrite !inE -H.
Qed.

(* The following theorem states that good logs are good for execution *)

Theorem goodToExecute h (g: graph h) (l : log) :
  goodLog (keys_of h) l -> exists er, executeLog g l = Some er.
Proof.
elim: l h g=>[|e ls]G h g; first by eexists.
case: e=>k x fld old new/=; case: k=>/=[||fnum]; first by case/andP=>_ H; apply: G.

- case/andP=>/andP[H1 H2 H3].
  have X: (new \in dom h) || (new == null) by rewrite !inE/= orbC keys_dom in H2.
  case: (condKE (modifyG g x fld (new:=new)) 
        (fun pf => executeLog (proj1 pf) ls) X)=>/=[[g' H4]]=>->; apply: G.
  suff S: keys_of h =i keys_of (modify g x fld new).1.
  by rewrite -(goodEqSub ls S).

(* TODO: Use H3 and prove the equality of domains: 

   keys_of h =i keys_of (modify g x fld new).1 *)
  admit.  

case/andP=>/andP[H1]H2 H3.
have X: (x != null) && (x \notin dom h) by rewrite -keys_dom H1 H2.
case: (condKE (allocG g fnum) (fun pf => executeLog pf ls) X)=>/=[g']->.
apply: G; 
suff S: x :: keys_of h =i keys_of (alloc h x fnum) by rewrite -(goodEqSub ls S).

(* TODO: Use H3 and prove another equality:
   x :: keys_of h =i keys_of (alloc h x fnum)  *)









(* TODO:

- Define a "good" logs wrt. initial g-heap and a set of objects
  (recursively) [DONE].

- Prove a lemma, stating that executing a good log leads to the graph
  [IN PROGRESS].

- Implement the basic expose (apex) function

*)

End ExecuteLogs.





