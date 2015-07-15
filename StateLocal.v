(** Calculation of an abstract machine for arithmetic expressions +
exceptions + local state . *)

Require Import List.
Require Import ListIndex.
Require Import Tactics.

(** * Syntax *)

Inductive Expr : Set := 
| Val : nat -> Expr 
| Add : Expr -> Expr -> Expr
| Throw : Expr
| Catch : Expr -> Expr -> Expr
| Get : Expr
| Put : Expr -> Expr -> Expr.

(** * Semantics *)

Definition State := nat.

Fixpoint eval (x: Expr) (q : State) : option (nat * State) :=
  match x with
    | Val n => Some (n , q)
    | Add x1 x2 => match eval x1 q with
                   | Some (n, q') => match eval x2 q' with
                                     | Some (m, q'') => Some ((n + m), q'')
                                     | None => None
                                     end
                   | None => None
                   end
    | Throw => None
    | Catch x1 x2 => match eval x1 q with
                     | Some (n, q') => Some (n, q')
                     | None => eval x2 q
                     end
    | Get => Some (q, q)
    | Put x1 x2 => match eval x1 q with
                   | Some (n, q') => eval x2 n
                   | None => None
                   end
  end.

(** * Abstract machine *)

Inductive CONT : Set :=
| NEXT : Expr -> CONT -> CONT
| ADD : nat -> CONT -> CONT
| HAND : Expr -> State -> CONT -> CONT
| PUT : Expr -> CONT -> CONT
| HALT : CONT
.

Inductive Conf : Set := 
| eval'' : Expr -> State -> CONT -> Conf
| exec : CONT -> State -> nat -> Conf
| fail : CONT -> Conf.

Notation "⟨ x , q , c ⟩" := (eval'' x q c).
Notation "⟪ c , q , v ⟫" := (exec c q v).
Notation "⟨| c |⟩" := (fail c).



Reserved Notation "x ==> y" (at level 80, no associativity).
Inductive AM : Conf -> Conf -> Prop :=
| am_val n q c : ⟨Val n, q, c⟩ ==> ⟪c, q, n⟫
| am_add x y c q : ⟨Add x y, q, c⟩ ==> ⟨x, q, NEXT y c⟩
| am_throw q c : ⟨Throw, q, c ⟩ ==> ⟨|c|⟩
| am_catch x1 x2 c q : ⟨Catch x1 x2, q,  c ⟩ ==> ⟨x1, q, HAND x2 q c⟩
| am_get q c : ⟨Get, q, c ⟩ ==> ⟪c, q, q ⟫
| am_put x1 x2 q c : ⟨Put x1 x2, q, c⟩ ==> ⟨x1, q, PUT x2 c⟩
| am_NEXT y c n q : ⟪NEXT y c, q, n⟫ ==> ⟨y, q, ADD n c⟩
| am_NEXT_fail y c : ⟨|NEXT y c|⟩ ==> ⟨|c|⟩
| am_ADD c n m q : ⟪ADD n c, q, m⟫ ==> ⟪c, q, n+m⟫
| am_ADD_fail c n : ⟨|ADD n c|⟩ ==> ⟨|c|⟩
| am_HAND_fail x2 c q : ⟨|HAND x2 q c|⟩ ==> ⟨x2, q, c⟩
| am_HAND x2 c n q q' : ⟪HAND x2 q' c, q, n⟫ ==> ⟪c, q, n⟫
| am_PUT x2 c q' n : ⟪PUT x2 c, q', n⟫ ==> ⟨x2, n, c⟩
| am_PUT_fail x2 c : ⟨|PUT x2 c|⟩ ==> ⟨|c|⟩
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

Theorem spec x q c : ⟨x, q, c⟩ =>> match eval x q with
                                 | Some (n, q') => ⟪c, q', n⟫
                                 | None         => ⟨|c|⟩
                                 end.
(** Setup the induction proof *)

Proof.
  intros.
  generalize dependent c.
  generalize dependent q.
  induction x;intros.

(** Calculation of the abstract machine *)

  begin
  ⟪c, q, n⟫.
  <== { apply am_val }
  ⟨Val n, q, c⟩.
  [].

  begin
    match eval x1 q with
    | Some (n, q') => match eval x2 q' with
                      | Some (m, q'') => ⟪c, q'', n+m⟫
                      | None          => ⟨|c|⟩
                      end
    | None         => ⟨|c|⟩
    end.
  <<= { apply am_ADD }
    match eval x1 q with
    | Some (n, q') => match eval x2 q' with
                      | Some (m, q'') => ⟪ADD n c, q'', m⟫
                      | None          => ⟨|c|⟩
                      end
    | None         => ⟨|c|⟩
    end.
  <<= { apply am_ADD_fail }
    match eval x1 q with
    | Some (n, q') => match eval x2 q' with
                      | Some (m, q'') => ⟪ADD n c, q'', m⟫
                      | None          => ⟨|ADD n c|⟩
                      end
    | None         => ⟨|c|⟩
    end.
  <<= { apply IHx2 }
    match eval x1 q with
    | Some (n, q') => ⟨x2, q', ADD n c⟩
    | None         => ⟨|c|⟩
    end.
  <<= { apply am_NEXT }
    match eval x1 q with
    | Some (n, q') => ⟪NEXT x2 c, q', n⟫
    | None         => ⟨|c|⟩
    end.
  <<= { apply am_NEXT_fail }
    match eval x1 q with
    | Some (n, q') => ⟪NEXT x2 c, q', n⟫
    | None         => ⟨|NEXT x2 c|⟩
    end.
  <<= { apply IHx1 }
      ⟨x1, q, NEXT x2 c⟩.
  <== {apply am_add}
      ⟨Add x1 x2, q, c⟩.
  [].


  begin
    ⟨|c|⟩.
  <== {apply am_throw}
    ⟨Throw, q, c ⟩. 
  [].

  begin
    match eval x1 q with
    | Some (n, q') => ⟪c, q', n⟫
    | None         => match eval x2 q with
                      | Some (m, q') => ⟪c, q', m⟫
                      | None         => ⟨|c|⟩
                      end
    end.
  <<= {apply IHx2}
    match eval x1 q with
    | Some (n, q') => ⟪c, q', n⟫
    | None         => ⟨x2, q, c⟩
    end.
  <<= {apply am_HAND_fail}
    match eval x1 q with
    | Some (n, q') => ⟪c, q', n⟫
    | None         => ⟨|HAND x2 q c|⟩
    end.
  <<= {apply am_HAND}
    match eval x1 q with
    | Some (n, q') => ⟪HAND x2 q c, q', n⟫
    | None         => ⟨|HAND x2 q c|⟩
    end.
  <<= {apply IHx1}
      ⟨x1, q, HAND x2 q c⟩.
  <== {apply am_catch}
      ⟨Catch x1 x2, q, c⟩.
  [].

  begin
    ⟪c, q, q ⟫.
  <== {apply am_get}
    ⟨Get, q, c ⟩.
  [].


  begin
    match eval x1 q with
    | Some (n, q') => match eval x2 n with
                      | Some (m, q'') => ⟪c, q'', m⟫
                      | None          => ⟨|c|⟩
                      end
    | None         => ⟨|c|⟩
    end.
  <<= {apply IHx2}
    match eval x1 q with
    | Some (n, q') => ⟨x2, n, c⟩
    | None         => ⟨|c|⟩
    end.
  <<= {apply am_PUT}
    match eval x1 q with
    | Some (n, q') => ⟪PUT x2 c, q', n⟫
    | None         => ⟨|c|⟩
    end.
  <<= {apply am_PUT_fail}
    match eval x1 q with
    | Some (n, q') => ⟪PUT x2 c, q', n⟫
    | None         => ⟨|PUT x2 c|⟩
    end.
  <<= {apply IHx1}
    ⟨x1, q, PUT x2 c⟩.
  <== {apply am_put}
    ⟨Put x1 x2, q, c⟩.
  [].
Qed.
  
