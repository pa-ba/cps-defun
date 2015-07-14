(** Calculation of an abstract machine for the call-by-need lambda
calculus + arithmetic. *)

Require Import List.
Require Import ListIndex.
Require Import Tactics.
Require Import Heap.

(** * Syntax *)

Inductive Expr : Set := 
| Val : nat -> Expr 
| Add : Expr -> Expr -> Expr
| Var : nat -> Expr
| Abs : Expr -> Expr
| App : Expr -> Expr -> Expr.

(** * Semantics *)

(** The evaluator for this language is taken from Ager et al. "A
functional correspondence between call-by-need evaluators and lazy
abstract machines". We use Haskell syntax to define the
evaluator. Moreover, we use an abstract interface to a heap
implementation:
<<
type Heap a
type Loc

empty :: Heap a
deref :: Heap a -> Loc -> a
update :: Heap a -> Loc -> a -> Heap a
alloc :: Heap a -> a -> (Heap a, Loc)
>>
Moreover, we assume that `Heap` forms a functor with an associated function
<<
hmap :: (a -> b) -> Heap a -> Heap b
>>
which in addition to functoriality also satisfies the following laws:
<<
hmap f empty = empty                                             (hmap-empty)
deref (hmap f h) l = f (deref h l)                               (hmap-deref)
hmap f (update h l e) = update (hmap f h) l (f e)                (hmap-update)
alloc (hmap f h) (f e) = (h', l) <=> alloc h e = (hmap f h', l)  (hmap-alloc)
>>

The evaluator itself is defined as follows:
<<
type Env   = [Loc]
data HElem = Thunk (Heap HElem -> (Value, Heap HElem)) | Value Value
data Value = Num Int | Clo (Loc -> Heap HElem -> (Value, Heap HElem))
	

eval :: Expr -> Env -> Heap HElem -> (Value, Heap HElem)
eval (Val n)   e h = (Num n, h)
eval (Add x y) e h = case eval x e h of
                       (Num n, h') -> case eval y e h' of
                                        (Num m, h'') -> (Num (n + m), h'')
eval (Var i)   e h = case deref h (e !! i) of
                       Thunk t -> let (v, h') = t h
                                  in (v, update h' (e !! i) (Value v))
                       Value v -> (v, h)
eval (Abs x)   e h = (Clo (\ l h' -> eval x (l : e) h') , h)
eval (App x y) e h = case eval x e h of
                       (Clo , h') -> let (h'',l) = alloc h' (Thunk (\h -> eval y e h))
                                     in f l h''
>>
After defunctionalisation and translation into relational form we
obtain the semantics below.  *)

Definition Env : Set := list Loc.

Inductive Value : Set :=
| Num : nat -> Value
| Clo : Expr -> Env -> Value.

Inductive HElem : Set  :=
  | thunk : Expr -> Env -> HElem
  | value : Value -> HElem.


Definition Heap := Heap.Heap HElem.

Reserved Notation "x ⇓[ e , h , h' ] y" (at level 80, no associativity).

Inductive eval : Expr -> Env -> Heap -> Heap -> Value -> Prop :=
| eval_val e n (h h' : Heap) : Val n ⇓[e,h,h] Num n
| eval_add e x y m n h h' h'' : x ⇓[e,h,h'] Num n -> y ⇓[e,h',h''] Num m -> Add x y ⇓[e,h,h''] Num (n + m)
| eval_var_thunk e e' x i l v h h' : nth e i = Some l -> deref h l = Some (thunk x e') -> x ⇓[e',h,h'] v -> 
                          Var i ⇓[e,h,update h' l (value v)] v
| eval_var_val e i l v h : nth e i = Some l -> deref h l = Some (value v) -> 
                          Var i ⇓[e,h,h] v
| eval_abs e x h : Abs x ⇓[e,h,h] Clo x e
| eval_app e e' x x' x'' y l h h' h'' h''' : x ⇓[e,h,h'] Clo x' e' -> alloc h' (thunk y e) = (h'',l) ->
                              x' ⇓[l :: e',h'',h'''] x'' -> App x y ⇓[e,h,h'''] x''
where "x ⇓[ e , h , h' ] y" := (eval x e h h' y).

(** * Abstract machine *)

Inductive CONT : Set :=
| ADD : nat -> CONT -> CONT
| NEXT : Expr -> Env -> CONT -> CONT
| UPDATE : Loc -> CONT -> CONT
| APP : Expr -> Env -> CONT -> CONT
| HALT : CONT
.



Inductive Conf : Set := 
| eval'' : Expr -> Env -> Heap -> CONT -> Conf
| apply : CONT -> Heap -> Value -> Conf.

Notation "⟨ x , e , h , c ⟩" := (eval'' x e h c).
Notation "⟪ c , h , v ⟫" := (apply c h v).


Reserved Notation "x ==> y" (at level 80, no associativity).
Inductive AM : Conf -> Conf -> Prop :=
| am_val n e h c :  ⟨Val n, e, h, c⟩ ==> ⟪c, h, Num n⟫
| am_add x y e h c : ⟨Add x y, e, h, c ⟩ ==> ⟨x, e, h, NEXT y e c⟩
| am_var i e h c l x e' :   nth e i = Some l -> deref h l = Some (thunk x e') ->
                            ⟨Var i, e, h, c⟩ ==> ⟨x, e', h, UPDATE l c⟩
| am_var_val i e h c l v : nth e i = Some l -> deref h l = Some (value v) ->
                           ⟨Var i, e, h, c⟩ ==> ⟪c, h, v⟫
| am_abs x e h c : ⟨Abs x, e, h, c ⟩ ==> ⟪c, h, Clo x e ⟫
| am_app x y e h c : ⟨App x y, e, h, c ⟩ ==> ⟨x, e, h, APP y e c⟩
| am_ADD n c h'' m : ⟪ADD n c, h'', Num m⟫ ==> ⟪c, h'', Num (n + m)⟫
| am_NEXT y e c h' n : ⟪NEXT y e c, h', Num n ⟫ ==> ⟨y, e, h', ADD n c⟩
| am_UPDATE l c h' v : ⟪UPDATE l c, h', v ⟫ ==> ⟪c, update h' l (value v), v ⟫
| am_APP y e c h' x' e' h'' l : alloc h' (thunk y e) = (h'', l) ->
                                ⟪APP y e c, h', Clo x' e' ⟫ ==> ⟨x', l :: e', h'', c ⟩

where "x ==> y" := (AM x y).

(** * Calculation *)

(** Boilerplate to import calculation tactics *)

Module VM <: Preorder.
Definition Conf := Conf.
Definition VM := AM.
End VM.
Module VMCalc := Calculation VM.
Import VMCalc.

(** Specification of the abstract machine *)

Theorem spec x e v c h h' : x ⇓[e,h,h'] v -> ⟨x, e, h, c⟩ 
                                 =>> ⟪c, h' , v⟫.

(** Setup the induction proof *)

Proof.
  intros.
  generalize dependent c.
  induction H;intros.

(** Calculation of the abstract machine *)

(** - [Val n ⇓[e,h,h] Num n]: *)

  begin
  ⟪c, h, Num n⟫.
  <== { apply am_val }
  ⟨Val n, e, h, c⟩.
  [].

(** - [Add x y ⇓[e,h,h''] Num (m + n)]: *)

  begin
    ⟪c, h'', Num (n + m)⟫.
  <== { apply am_ADD }
    ⟪ADD n c, h'', Num m⟫.
  <<= { apply IHeval2 }
   ⟨y, e, h', ADD n c⟩.
  <== { apply am_NEXT }
   ⟪NEXT y e c, h', Num n ⟫.
  <<= { apply IHeval1 }
   ⟨x, e, h, NEXT y e c⟩.
  <== {apply am_add}
   ⟨Add x y, e, h, c ⟩.
  [].

(** - [Var i ⇓[e,h,update h' l (value v)] v] *)

  (* assert (deref (convH h) l = Some (thunk' (comp' x WRITE) e')) *)
  (*   by (unfold convH; rewrite hmap_deref; rewrite H0; reflexivity). *)
  begin
    ⟪c, update h' l (value v), v ⟫.
  <== {apply am_UPDATE }
    ⟪UPDATE l c, h', v ⟫.
  <<= {apply IHeval}
    ⟨x, e', h, UPDATE l c⟩.
  <== {apply am_var}
    ⟨Var i, e, h, c⟩.
  [].

(** - [Var i ⇓[e,h,h] v] *)

  begin
    ⟪c, h, v ⟫.
  <== {eapply am_var_val}
    ⟨Var i, e, h, c⟩.
  [].

(** - [Abs x ⇓[e,h,h] Clo x e] *)

  begin
    ⟪c, h, Clo x e ⟫.
  <== { apply am_abs }
    ⟨Abs x, e, h, c ⟩.
  [].
  
(** - [App x y ⇓[e,h,h'''] x''] *)
    
  begin
    ⟪c, h''', x'' ⟫.
  <<= { apply IHeval2 }
    ⟨x', l :: e', h'', c ⟩.
  <== { apply am_APP }
    ⟪APP y e c, h', Clo x' e' ⟫.
  <<= { apply IHeval1 }
    ⟨x, e, h, APP y e c⟩.
  <== { apply am_app }
    ⟨App x y, e, h, c ⟩.
  [].
Qed.
    
(** * Soundness *)


(** Custom tactic to apply inversion *)
Ltac inv := match goal with
              | [H1 : nth ?e ?i = Some ?l1,
                 H2 : nth ?e ?i = Some ?l2 |- _] => rewrite H1 in H2; inversion H2; subst; clear H1 H2
              | [H1 : deref ?h ?l = Some ?v1,
                 H2 : deref ?h ?l = Some ?v2 |- _] => rewrite H1 in H2; inversion H2; subst; clear H1 H2
              | [H1 : alloc ?h ?l = _,
                 H2 : alloc ?h ?l = _ |- _] => rewrite H1 in H2; inversion H2; subst; clear H1 H2
              | _ => idtac
            end.

Lemma determ_vm : determ AM.
  intros C C1 C2 V. induction V; intro V'; inversion V'; subst; repeat inv; reflexivity.
Qed.
  

Definition terminates (p : Expr) : Prop := exists r h, p ⇓[nil,empty,h] r.


Theorem sound x C : terminates x -> ⟨x, nil, empty , HALT⟩ =>>! C -> 
                          exists v h, C = ⟪HALT, h, v⟫ /\ x ⇓[nil,empty,h] v.
Proof.
  unfold terminates. intros. destruct H as [r T]. destruct T as [h T].
  
  pose (spec x nil r HALT) as H'. exists r. exists h. split. pose (determ_trc determ_vm) as D.
  unfold determ in D. eapply D. eassumption. split. apply H'. assumption. intro Con. destruct Con.
  inversion H. assumption.
Qed.