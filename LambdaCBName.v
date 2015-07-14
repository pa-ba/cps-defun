(** Calculation of an abstract machine for the call-by-name lambda
calculus. The resulting abstract machine (almost) coincides with the
Krivine machine. The relation to the Krivine machine is explained
below. *)

Require Import List.
Require Import ListIndex.
Require Import Tactics.

(** * Syntax *)

Inductive Expr : Set := 
| Var : nat -> Expr
| Abs : Expr -> Expr
| App : Expr -> Expr -> Expr.

(** * Semantics *)


(** We start with the evaluator for this language, which is taken from
Ager et al. "A functional correspondence between evaluators and
abstract machines" (we use Haskell syntax to describe the evaluator):
<<
type Env   = [Thunk]
data Thunk = Thunk (() -> Value)
data Value = Clo (Thunk -> Value)


eval :: Expr -> Env -> Value
eval (Var i)   e = case e !! i of
                     Thunk t -> t ()
eval (Abs x)   e = Clo (\t -> eval x (t : e))
eval (App x y) e = case eval x e of
                     Clo f -> f (Thunk (\_ -> eval y e))
>>
After defunctionalisation and translation into relational form we
obtain the semantics below.  *)

Inductive Thunk : Set  :=
  | thunk : Expr -> list Thunk -> Thunk.

Definition Env : Set := list Thunk.

Inductive Value : Set :=
| Clo : Expr -> Env -> Value.

Reserved Notation "x ⇓[ e ] y" (at level 80, no associativity).

Inductive eval : Expr -> Env -> Value -> Prop :=
| eval_var e e' x i v : nth e i = Some (thunk x e') -> x ⇓[e'] v -> Var i ⇓[e] v
| eval_abs e x : Abs x ⇓[e] Clo x e
| eval_app e e' x x' v y  : x ⇓[e] Clo x' e' -> x' ⇓[thunk y e :: e'] v -> App x y ⇓[e] v
where "x ⇓[ e ] y" := (eval x e y).

(** * Abstract machine *)

Inductive CONT : Set :=
| APP : Expr -> Env -> CONT -> CONT
| HALT : CONT
.

Inductive Conf : Set := 
| eval'' : Expr -> Env -> CONT -> Conf
| apply : CONT -> Value -> Conf.

Notation "⟨ x , e , c ⟩" := (eval'' x e c).
Notation "⟪ c , v ⟫" := (apply c v).



Reserved Notation "x ==> y" (at level 80, no associativity).
Inductive AM : Conf -> Conf -> Prop :=
| am_var i e c x e' : nth e i = Some (thunk x e') -> ⟨Var i, e, c⟩ ==> ⟨x, e', c⟩
| am_abs x e c : ⟨Abs x, e, c⟩ ==> ⟪c, Clo x e⟫
| am_app x y e c : ⟨App x y, e, c⟩ ==> ⟨x, e, APP y e c⟩
| am_APP y e c x' e' : ⟪APP y e c, Clo x' e'⟫ ==> ⟨x', thunk y e::e', c⟩
where "x ==> y" := (AM x y).

(** The only difference between the above machine and the Krivine
machine is that the former produces via the rule [am_abs] a state of
the form [⟪...⟫], which is then immediately consumed by the rule
[am_APP]. These two rules [am_abs] and [am_APP] can therefore be fused
into a single rule. The resulting machine is exactly coincides with
the Krivine machine. *)


(** * Calculation *)

(** Boilerplate to import calculation tactics *)

Module AM <: Preorder.
Definition Conf := Conf.
Definition VM := AM.
End AM.
Module AMCalc := Calculation AM.
Import AMCalc.

(** Specification of the abstract machine *)

Theorem spec x e r c : x ⇓[e] r -> ⟨x, e, c⟩ =>> ⟪c, r⟫.

(** Setup the induction proof *)

Proof.
  intros.
  generalize dependent c.
  induction H;intros.

(** Calculation of the abstract machine *)

(** - [Var i ⇓[e] v] *)

  begin
    ⟪c, v ⟫.
  <<= {apply IHeval}
    ⟨x, e', c ⟩.
  <== {apply am_var}
    ⟨Var i, e, c⟩.
  [].

(** - [Abs x ⇓[e] Clo x e] *)

  begin
    ⟪c, Clo x e⟫.
  <== { apply am_abs }
    ⟨Abs x, e, c⟩.
  [].

(** - [App x y ⇓[e] w] *)

  begin
    ⟪c, v⟫.
  <<= { apply IHeval2 }
    ⟨x', (thunk y e::e'), c⟩.
  <== { apply am_APP }
    ⟪APP y e c, Clo x' e'⟫.
  <<= {apply IHeval1}
    ⟨x, e, APP y e c⟩.
  <== {apply am_app}
    ⟨App x y, e, c⟩.
  [].
Qed.
  
(** * Soundness *)

Lemma determ_am : determ AM.
  intros C c1 c2 V. induction V; intro V'; inversion V'; subst; congruence.
Qed.
  

Definition terminates (p : Expr) : Prop := exists r, p ⇓[nil] r.

Theorem sound x C : terminates x -> ⟨x, nil, HALT⟩ =>>! C -> 
                          exists r, C = ⟪HALT, r⟫ /\ x ⇓[nil] r.
Proof.
  unfold terminates. intros. destruct H as [r T].
  
  pose (spec x nil r HALT) as H'. exists r. split. pose (determ_trc determ_am) as D.
  unfold determ in D. eapply D. eassumption. split. eauto. intro. destruct H. 
  inversion H. assumption.
Qed.
  
