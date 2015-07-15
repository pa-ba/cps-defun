(** Calculation of an abstract machine for arithmetic expressions +
exceptions. The calculation uses two continuations. As a result, the
continuations are branching. The result appears to be inferior
compared to the standard approach (as in [Exceptions.v]) *)

Require Import List.
Require Import ListIndex.
Require Import Tactics.

(** * Syntax *)

Inductive Expr : Set := 
| Val (n : nat) : Expr 
| Add (x y: Expr) : Expr
| Throw : Expr
| Catch : Expr -> Expr -> Expr.

(** * Semantics *)


Fixpoint eval (x: Expr) : option nat :=
  match x with
    | Val n => Some n
    | Add x1 x2 => match eval x1 with
                   | Some n => match eval x2 with
                                 | Some m => Some (n + m)
                                 | None => None
                               end
                   | None => None
                   end
    | Throw => None
    | Catch x1 x2 => match eval x1 with
                     | Some n => Some n
                     | None => eval x2
                     end
  end.

(** * Abstract machine *)

Inductive CONT : Set :=
| NEXT : Expr -> CONT -> CONT -> CONT
| ADD : nat -> CONT -> CONT
| HAND : Expr -> CONT -> CONT -> CONT
| HALT : CONT
.

Inductive Conf : Set := 
| eval'' : Expr -> CONT -> CONT -> Conf
| exec : CONT -> nat -> Conf
| fail : CONT -> Conf.

Notation "⟨ x , sc , fc ⟩" := (eval'' x sc fc).
Notation "⟪ c , v ⟫" := (exec c v).
Notation "⟨| c |⟩" := (fail c).



Reserved Notation "x ==> y" (at level 80, no associativity).
Inductive AM : Conf -> Conf -> Prop :=
| am_val n sc fc : ⟨Val n, sc, fc⟩ ==> ⟪sc, n⟫
| am_add x y sc fc : ⟨Add x y, sc, fc⟩ ==> ⟨x, NEXT y sc fc, fc⟩
| am_throw sc fc : ⟨Throw, sc, fc⟩ ==> ⟨|fc|⟩
| am_catch x1 x2 sc fc : ⟨Catch x1 x2, sc, fc ⟩ ==> ⟨x1, sc, HAND x2 sc fc⟩
| am_NEXT y sc fc n : ⟪NEXT y sc fc, n⟫ ==> ⟨y, ADD n sc, fc⟩
| am_ADD c n m : ⟪ADD n c, m⟫ ==> ⟪c, n+m⟫
| am_HAND_fail x2 sc fc : ⟨|HAND x2 sc fc |⟩ ==> ⟨x2, sc, fc⟩
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

Theorem spec x sc fc : ⟨x, sc, fc⟩ =>> match eval x with
                                       | Some n => ⟪sc, n⟫
                                       | None   => ⟨|fc |⟩
                                       end.
(** Setup the induction proof *)

Proof.
  intros.
  generalize dependent sc.
  generalize dependent fc.
  induction x;intros.

(** Calculation of the abstract machine *)

  begin
  ⟪sc, n⟫.
  <== { apply am_val }
  ⟨Val n, sc, fc⟩.
  [].

  begin
    match eval x1 with
    | Some n => match eval x2 with
                | Some m => ⟪sc, n+m⟫
                | None => ⟨|fc|⟩
                end
    | None => ⟨| fc |⟩
    end.
  <<= { apply am_ADD }
    match eval x1 with
    | Some n => match eval x2 with
                | Some m => ⟪ADD n sc, m⟫
                | None => ⟨|fc|⟩
                end
    | None => ⟨| fc |⟩
    end.
  <<= { apply IHx2 }
    match eval x1 with
    | Some n => ⟨x2, ADD n sc, fc⟩
    | None => ⟨| fc |⟩
    end.
  <<= { apply am_NEXT }
    match eval x1 with
    | Some n => ⟪NEXT x2 sc fc, n⟫
    | None => ⟨| fc |⟩
    end.
  <<= { apply IHx1 }
      ⟨x1, NEXT x2 sc fc, fc⟩.
  <== {apply am_add}
      ⟨Add x1 x2, sc, fc⟩.
  [].


  begin
    ⟨|fc|⟩.
  <== {apply am_throw}
    ⟨Throw, sc, fc ⟩. 
  [].

  begin
      match eval x1 with
      | Some n => ⟪sc, n⟫
      | None   => match eval x2 with
                  | Some m => ⟪sc, m⟫
                  | None   => ⟨|fc|⟩
                  end
      end.
  <<= {apply IHx2}
      match eval x1 with
      | Some n => ⟪sc, n⟫
      | None   => ⟨x2, sc, fc⟩
      end.
  <<= {apply am_HAND_fail}
      match eval x1 with
      | Some n => ⟪sc, n⟫
      | None   => ⟨|HAND x2 sc fc|⟩
      end.
  <<= {apply IHx1}
      ⟨x1, sc, HAND x2 sc fc⟩.
  <== {apply am_catch}
      ⟨Catch x1 x2, sc, fc⟩.
  [].
Qed.
  
