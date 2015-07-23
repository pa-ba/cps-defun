(** Calculation of an abstract machine for arithmetic expressions +
 state + unbounded loops. *)

Require Import List.
Require Import ListIndex.
Require Import Tactics.

(** * Syntax *)

Inductive Expr : Set := 
| Val : nat -> Expr 
| Add : Expr -> Expr -> Expr
| Get : Expr.

Inductive Stmt : Set :=
| Put : Expr -> Stmt
| Seqn : Stmt -> Stmt -> Stmt
| While : Expr -> Stmt -> Stmt.

(** * Semantics *)

Definition State := nat.
Reserved Notation "x ⇓[ q ] y" (at level 80, no associativity).

Inductive eval : Expr -> State -> nat -> Prop :=
| eval_val q n : Val n ⇓[q] n
| eval_add q x y m n : x ⇓[q] n -> y ⇓[q] m -> Add x y ⇓[q] (n + m)
| eval_get q : Get ⇓[q] q
where "x ⇓[ q ] y" := (eval x q y).

Reserved Notation "x ↓[ q ] q'" (at level 80, no associativity).

Inductive run : Stmt -> State -> State -> Prop :=
| run_put x q v : x ⇓[q] v -> Put x ↓[q] v
| run_seqn x1 x2 q1 q2 q3 : x1 ↓[q1] q2 -> x2 ↓[q2] q3 -> Seqn x1 x2 ↓[q1] q3
| run_while_exit x1 x2 q : x1 ⇓[q] 0 -> While x1 x2 ↓[q] q
| run_while_cont v x1 x2 q1 q2 q3 : x1 ⇓[q1] v -> v > 0 -> x2 ↓[q1] q2 -> While x1 x2 ↓[q2] q3 
                   -> While x1 x2 ↓[q1] q3
where "x ↓[ q ] y" := (run x q y).

(** * Abstract machine *)

Inductive CONT : Set :=
| NEXT : Expr -> State -> CONT -> CONT
| ADD : nat -> CONT -> CONT
| PUT : CONT -> CONT
| SEQN : Stmt -> CONT -> CONT
| CHECK : Expr -> Stmt -> State -> CONT -> CONT
| WHILE : Expr -> Stmt -> CONT -> CONT
| HALT : CONT
.


Inductive Conf : Set := 
| eval'' : Expr -> State -> CONT -> Conf
| run'' : Stmt -> State -> CONT -> Conf
| exec : CONT -> nat -> Conf
| exec' : CONT -> State -> Conf
.

Notation "⟨ x , q , c ⟩" := (eval'' x q c).
Notation "⟨| x , q , c |⟩" := (run'' x q c).
Notation "⟪ c , v ⟫" := (exec c v).
Notation "⟪| c , q |⟫" := (exec' c q).


Reserved Notation "x ==> y" (at level 80, no associativity).
Inductive AM : Conf -> Conf -> Prop :=
| am_val n q c : ⟨Val n, q, c⟩ ==> ⟪c, n⟫
| am_add x y c q : ⟨Add x y, q, c⟩ ==> ⟨x, q, NEXT y q c⟩
| am_get q c : ⟨Get, q, c ⟩ ==> ⟪c, q ⟫
| am_put x q c : ⟨|Put x, q, c|⟩ ==> ⟨x, q, PUT c⟩                          
| am_seqn x1 x2 q1 c : ⟨|Seqn x1 x2, q1, c|⟩ ==> ⟨|x1, q1, SEQN x2 c|⟩
| am_while x1 x2 q c : ⟨|While x1 x2, q, c |⟩ ==> ⟨x1, q, CHECK x1 x2 q c⟩
| am_NEXT y c n q : ⟪NEXT y q c, n⟫ ==> ⟨y, q, ADD n c⟩
| am_ADD c n m : ⟪ADD n c, m⟫ ==> ⟪c, n+m⟫
| am_PUT c n : ⟪PUT c, n⟫ ==> ⟪|c, n|⟫
| am_SEQN x2 c q2 : ⟪| SEQN x2 c, q2|⟫ ==> ⟨|x2, q2, c |⟩
| am_CHECK_0 c q x1 x2 : ⟪CHECK x1 x2 q c, 0⟫ ==> ⟪|c, q|⟫
| am_CHECK_S c q v x1 x2 : v > 0 -> ⟪CHECK x1 x2 q c, v⟫ ==> ⟨|x2, q, WHILE x1 x2 c|⟩
| am_WHILE x1 x2 c q2 : ⟪|WHILE x1 x2 c, q2 |⟫ ==> ⟨|While x1 x2, q2, c|⟩
where "x ==> y" := (AM x y).

(** * Calculation *)

(** Boilerplate to import calculation tactics *)

Module AM <: Preorder.
Definition Conf := Conf.
Definition VM := AM.
End AM.
Module AMCalc := Calculation AM.
Import AMCalc.

(** Specification of the abstract machine for expressions *)

Theorem specExpr x q v c : x ⇓[q] v -> ⟨x, q, c⟩ =>> ⟪c, v⟫.
(** Setup the induction proof *)

Proof.
  intros.
  generalize dependent c.
  induction H;intros.

(** Calculation of the abstract machine *)

  begin
  ⟪c, n⟫.
  <== { apply am_val }
  ⟨Val n, q, c⟩.
  [].

  begin
    ⟪c, n + m ⟫.
  <== { apply am_ADD }
    ⟪ADD n c, m ⟫.
  <<= { apply IHeval2 }
    ⟨y, q, ADD n c⟩.
  <<= { apply am_NEXT }
    ⟪NEXT y q c , n⟫.
  <<= { apply IHeval1 }
      ⟨x, q, NEXT y q c⟩.
  <== {apply am_add}
      ⟨Add x y, q, c⟩.
  [].


  begin
    ⟪c, q⟫.
  <== {apply am_get}
    ⟨Get, q, c ⟩.
  [].
Qed.
  
Theorem specStmt x q q' c : x ↓[q] q' -> ⟨| x, q, c|⟩ =>> ⟪|c, q'|⟫.
(** Setup the induction proof *)

Proof.
  intros.
  generalize dependent c.
  induction H;intros.

(** Calculation of the abstract machine *)

  begin
    ⟪|c, v|⟫.
  <<= { apply am_PUT }
    ⟪PUT c, v⟫.
  <<= { apply specExpr }
    ⟨x, q, PUT c⟩.
  <<= { apply am_put }
    ⟨|Put x, q, c|⟩.
  [].

  begin
    ⟪|c, q3 |⟫.
  <<= {apply IHrun2}
    ⟨|x2, q2, c |⟩.
  <== {apply am_SEQN}
    ⟪| SEQN x2 c, q2|⟫.
  <<= {apply IHrun1}
    ⟨|x1, q1, SEQN x2 c |⟩.
  <== {apply am_seqn}
    ⟨|Seqn x1 x2, q1, c |⟩.
  [].

  begin
    ⟪|c, q|⟫.
  <== {apply am_CHECK_0}
    ⟪CHECK x1 x2 q c, 0⟫.
  <<= {apply specExpr}
    ⟨x1, q, CHECK x1 x2 q c⟩.
  <== {apply am_while}
    ⟨|While x1 x2, q, c |⟩.
  [].

  begin
    ⟪|c, q3 |⟫.
  <<= {apply IHrun2}
    ⟨|While x1 x2, q2, c|⟩.
  <== {apply am_WHILE}
    ⟪|WHILE x1 x2 c, q2|⟫.
  <<= {apply IHrun1}
    ⟨|x2, q1, WHILE x1 x2 c|⟩.
  <== {apply am_CHECK_S}
    ⟪CHECK x1 x2 q1 c, v⟫.
  <<= {apply specExpr}
    ⟨x1, q1, CHECK x1 x2 q1 c⟩.
  <== {apply am_while}
    ⟨|While x1 x2, q1, c |⟩.
  [].
Qed.
  
(** * Soundness *)

Lemma determ_am : determ AM.
Proof.
  intros C c1 c2 V.
  induction V; intro V'; inversion V'; subst; try congruence;
  match goal with
  | [H : 0>0 |- _]  => inversion H
  end.              
Qed.
  


Definition terminates (p : Stmt) : Prop := exists r, p ↓[0] r.

Theorem sound x C : terminates x -> ⟨|x, 0, HALT|⟩ =>>! C -> 
                    exists r, C = ⟪|HALT, r|⟫ /\ x ↓[0] r.
Proof.
  unfold terminates. intros. destruct H as [r T].
  
  pose (specStmt x 0 r HALT) as H'. exists r. split. pose (determ_trc determ_am) as D.
  unfold determ in D. eapply D. eassumption. split. eauto. intro. destruct H. 
  inversion H. assumption.
Qed.
  
