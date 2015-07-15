(** Calculation of an abstract machine for arithmetic expressions +
exceptions. *)

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
| NEXT : Expr -> CONT -> CONT
| ADD : nat -> CONT -> CONT
| HAND : Expr -> CONT -> CONT
| HALT : CONT
.

Inductive Conf : Set := 
| eval'' : Expr -> CONT -> Conf
| exec : CONT -> nat -> Conf
| fail : CONT -> Conf.

Notation "⟨ x , c ⟩" := (eval'' x c).
Notation "⟪ c , v ⟫" := (exec c v).
Notation "⟨| c |⟩" := (fail c).



Reserved Notation "x ==> y" (at level 80, no associativity).
Inductive AM : Conf -> Conf -> Prop :=
| am_val n c : ⟨Val n, c⟩ ==> ⟪c, n⟫
| am_add x y c : ⟨Add x y, c⟩ ==> ⟨x, NEXT y c⟩
| am_throw  c : ⟨Throw, c ⟩ ==> ⟨|c |⟩
| am_catch x1 x2 c : ⟨Catch x1 x2, c ⟩ ==> ⟨x1, HAND x2 c⟩
| am_NEXT y c n : ⟪NEXT y c, n⟫ ==> ⟨y, ADD n c⟩
| am_NEXT_fail y c : ⟨|NEXT y c|⟩ ==> ⟨|c|⟩
| am_ADD c n m : ⟪ADD n c, m⟫ ==> ⟪c, n+m⟫
| am_ADD_fail c n : ⟨|ADD n c|⟩ ==> ⟨|c|⟩
| am_HAND_fail x2 c : ⟨|HAND x2 c |⟩ ==> ⟨x2, c⟩
| am_HAND x2 c n : ⟪HAND x2 c, n⟫ ==> ⟪c, n⟫
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

Theorem spec x c : ⟨x, c⟩ =>> match eval x with
                              | Some n => ⟪c, n⟫
                              | none   => ⟨|c |⟩
                              end.
(** Setup the induction proof *)

Proof.
  intros.
  generalize dependent c.
  induction x;intros.

(** Calculation of the abstract machine *)

  begin
    match eval (Val n) with
     | Some n' => ⟪c, n' ⟫
     | None => ⟨|c |⟩
    end.
  =   {reflexivity}
  ⟪c, n⟫.
  <== { apply am_val }
  ⟨Val n, c⟩.
  [].

  begin
    match eval (Add x1 x2) with
     | Some n => ⟪c, n ⟫
     | None => ⟨|c |⟩
     end.
  =   {reflexivity}
    match eval x1 with
    | Some n => match eval x2 with
                | Some m => ⟪c, n+m⟫
                | None => ⟨|c|⟩
                end
    | None => ⟨| c |⟩
    end.
  <<= { apply am_ADD }
    match eval x1 with
    | Some n => match eval x2 with
                | Some m => ⟪ADD n c, m⟫
                | None => ⟨|c|⟩
                end
    | None => ⟨| c |⟩
    end.
  
  <<= { apply am_ADD_fail }
    match eval x1 with
    | Some n => match eval x2 with
                | Some m => ⟪ADD n c, m⟫
                | None => ⟨|ADD n c|⟩
                end
    | None => ⟨| c |⟩
    end.
  <<= { apply IHx2 }
    match eval x1 with
    | Some n => ⟨x2, ADD n c⟩
    | None => ⟨| c |⟩
    end.
  <<= { apply am_NEXT }
    match eval x1 with
    | Some n => ⟪NEXT x2 c, n⟫
    | None => ⟨| c |⟩
    end.
  <<= { apply am_NEXT_fail }
    match eval x1 with
    | Some n => ⟪NEXT x2 c, n⟫
    | None => ⟨| NEXT x2 c |⟩
    end.
  <<= { apply IHx1 }
      ⟨x1, NEXT x2 c⟩.
  <== {apply am_add}
      ⟨Add x1 x2, c ⟩.
  [].


  begin
    match eval Throw with
    | Some n => ⟪c, n ⟫
    | None => ⟨|c |⟩
    end.
  = {reflexivity}
    ⟨|c |⟩.
  <== {apply am_throw}
    ⟨Throw, c ⟩. 
  [].

  begin
    match eval (Catch x1 x2) with
    | Some n => ⟪c, n ⟫
    | None => ⟨|c |⟩
    end.
  simpl.
  = {reflexivity}
      match eval x1 with
      | Some n => ⟪c, n⟫
      | None   => match eval x2 with
                  | Some m => ⟪c, m⟫
                  | None   => ⟨|c|⟩
                  end
      end.
  <<= {apply IHx2}
      match eval x1 with
      | Some n => ⟪c, n⟫
      | None   => ⟨x2, c⟩
      end.
  <<= {apply am_HAND_fail}
      match eval x1 with
      | Some n => ⟪c, n⟫
      | None   => ⟨|HAND x2 c|⟩
      end.
  <<= {apply am_HAND}
      match eval x1 with
      | Some n => ⟪HAND x2 c, n⟫
      | None   => ⟨|HAND x2 c|⟩
      end.
  <<= {apply IHx1}
      ⟨x1, HAND x2 c⟩.
  <== {apply am_catch}
      ⟨Catch x1 x2, c⟩.
  [].
Qed.
  
