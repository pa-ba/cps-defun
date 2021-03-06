(** Calculation of an abstract machine for the call-by-value lambda
calculus + arithmetic. The resulting abstract machine coincides with
the CEK machine (extended with arithmetic). *)

Require Import List.
Require Import ListIndex.
Require Import Tactics.

(** * Syntax *)

Inductive Expr : Set := 
| Val : nat -> Expr 
| Add : Expr -> Expr -> Expr
| Var : nat -> Expr
| Abs : Expr -> Expr
| App : Expr -> Expr -> Expr.

(** * Semantics *)

(** The evaluator for this language is given as follows:
<<
type Env = [Value]
data Value =  Num Int | Fun (Value -> Value)


eval ::  Expr -> Env -> Value
eval (Val n) e   = Num n
eval (Add x y) e = case eval x e of
                     Num n -> case eval y e of
                                Num m -> Num (n+m)
eval (Var i) e   = e !! i
eval (Abs x) e   = Fun (\v -> eval x (v:e))
eval (App x y) e = case eval x e of
                     Fun f -> f (eval y e)
>>
After defunctionalisation and translation into relational form we
obtain the semantics below. *)

Inductive Value : Set :=
| Num : nat -> Value
| Clo : Expr -> list Value -> Value.

Definition Env := list Value.

Reserved Notation "x ⇓[ e ] y" (at level 80, no associativity).

Inductive eval : Expr -> Env -> Value -> Prop :=
| eval_val e n : Val n ⇓[e] Num n
| eval_add e x y m n : x ⇓[e] Num n -> y ⇓[e] Num m -> Add x y ⇓[e] Num (n + m)
| eval_var e i v : nth e i = Some v -> Var i ⇓[e] v
| eval_abs e x : Abs x ⇓[e] Clo x e
| eval_app e e' x x' w y v : x ⇓[e] Clo x' e' -> y ⇓[e] v -> x' ⇓[v :: e'] w -> App x y ⇓[e] w
where "x ⇓[ e ] y" := (eval x e y).

(** * Abstract machine *)

Inductive CONT : Set :=
| NEXT : Expr -> Env -> CONT -> CONT
| ADD : nat -> CONT -> CONT
| FUN : Expr -> Env -> CONT -> CONT
| ARG : Expr -> Env -> CONT -> CONT
| HALT : CONT
.

Inductive Conf : Set := 
| eval'' : Expr -> Env -> CONT -> Conf
| apply : CONT -> Value -> Conf.

Notation "⟨ x , e , c ⟩" := (eval'' x e c).
Notation "⟪ c , v ⟫" := (apply c v).



Reserved Notation "x ==> y" (at level 80, no associativity).
Inductive AM : Conf -> Conf -> Prop :=
| am_val n e c : ⟨Val n, e, c⟩ ==> ⟪c, Num n⟫
| am_add x y e c : ⟨Add x y, e, c⟩ ==> ⟨x, e, NEXT y e c⟩
| am_var i e c v : nth e i = Some v -> ⟨Var i, e, c⟩ ==> ⟪c, v⟫
| am_abs x e c : ⟨Abs x, e, c⟩ ==> ⟪c, Clo x e⟫
| am_app x y e c : ⟨App x y, e, c⟩ ==> ⟨x, e, ARG y e c⟩
| am_NEXT y e c n : ⟪NEXT y e c, Num n⟫ ==> ⟨y, e, ADD n c⟩
| am_ADD c n m : ⟪ADD n c, Num m⟫ ==> ⟪c, Num (n+m)⟫
| am_FUN x' e' c v : ⟪FUN x' e' c, v⟫ ==> ⟨x', v::e', c⟩
| am_ARG y e c x' e' : ⟪ARG y e c, Clo x' e'⟫ ==> ⟨y, e, FUN x' e' c⟩
where "x ==> y" := (AM x y).


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

(** - [Val n ⇓[e] Num n]: *)

  begin
  ⟪c, Num n⟫.
  <== { apply am_val }
  ⟨Val n, e, c⟩.
  [].

(** - [Add x y ⇓[e] Num (n + m)]: *)

  begin
    ⟪c, Num (n + m)⟫.
  <== { apply am_ADD }
      ⟪ADD n c, Num m⟫.
  <<= { apply IHeval2 }
      ⟨y, e, ADD n c⟩.
  <== { apply am_NEXT }
      ⟪NEXT y e c, Num n⟫.
  <<= { apply IHeval1 }
      ⟨x, e, NEXT y e c⟩.
  <== {apply am_add}
      ⟨Add x y, e, c ⟩.
  [].

(** - [Var i ⇓[e] v] *)

  begin
    ⟪c, v ⟫.
  <== {apply am_var}
    ⟨Var i, e, c ⟩.
   [].

(** - [Abs x ⇓[e] Clo x e] *)

  begin
    ⟪c, Clo x e⟫.
  <== { apply am_abs }
    ⟨Abs x, e, c⟩.
  [].

(** - [App x y ⇓[e] w] *)

  begin
    ⟪c, w⟫.
  <<= { apply IHeval3 }
    ⟨x', (v::e'), c⟩.
  <== { apply am_FUN }
    ⟪FUN x' e' c, v⟫.
  <<= {apply IHeval2}
    ⟨y, e, FUN x' e' c⟩.
  <== {apply am_ARG}
    ⟪ARG y e c, Clo x' e'⟫.
  <<= {apply IHeval1}
    ⟨x, e, ARG y e c⟩.
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
  
