(** Calculation of an abstract machine for arithmetic expressions. *)

Require Import List.
Require Import ListIndex.
Require Import Tactics.

(** * Syntax *)

Inductive Expr : Set := 
| Val (n : nat) : Expr 
| Add (x y: Expr) : Expr.

(** * Semantics *)

Fixpoint eval (e: Expr) : nat :=
  match e with
    | Val n => n
    | Add x y => eval x + eval y
  end.

(** * Abstract machine *)

Inductive CONT : Set :=
| NEXT : Expr -> CONT -> CONT
| ADD : nat -> CONT -> CONT
| HALT : CONT
.

Inductive Conf : Set := 
| eval'' : Expr -> CONT -> Conf
| apply : CONT -> nat -> Conf.

Notation "⟨ x , c ⟩" := (eval'' x c).
Notation "⟪ c , v ⟫" := (apply c v).



Reserved Notation "x ==> y" (at level 80, no associativity).
Inductive AM : Conf -> Conf -> Prop :=
| am_val n c : ⟨Val n, c⟩ ==> ⟪c, n⟫
| am_add x y c : ⟨Add x y, c⟩ ==> ⟨x, NEXT y c⟩
| am_NEXT y c n : ⟪NEXT y c, n⟫ ==> ⟨y, ADD n c⟩
| am_ADD c n m : ⟪ADD n c, m⟫ ==> ⟪c, n+m⟫
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

Theorem spec x c : ⟨x, c⟩ =>> ⟪c, eval x⟫.

(** Setup the induction proof *)

Proof.
  intros.
  generalize dependent c.
  induction x;intros.

(** Calculation of the abstract machine *)

  begin
  ⟪c, eval (Val n)⟫.
  =   {reflexivity}
  ⟪c, n⟫.
  <== { apply am_val }
  ⟨Val n, c⟩.
  [].

  begin
    ⟪c, eval (Add x1 x2) ⟫.
  =   {reflexivity}
    ⟪c, eval x1 + eval x2 ⟫.
  <== { apply am_ADD }
      ⟪ADD (eval x1) c, eval x2⟫.
  <<= { apply IHx2 }
      ⟨x2, ADD (eval x1) c⟩.
  <== { apply am_NEXT }
      ⟪NEXT x2 c, eval x1⟫.
  <<= { apply IHx1 }
      ⟨x1, NEXT x2 c⟩.
  <== {apply am_add}
      ⟨Add x1 x2, c ⟩.
  [].

Qed.
  
