From Coq Require Import Lists.List Nat Arith.EqNat Bool.Bool.
Require Import Program.Tactics.
Import ListNotations.
Open Scope bool_scope.

Ltac induct x := induction x; simpl; intros; simpl; try reflexivity; try discriminate.

Ltac gendep x := generalize dependent x.

Ltac induct' x H := induction x using H; simpl; intros; simpl; try reflexivity; try discriminate.

Ltac inv H := inversion H; subst.

Ltac fdestr := try match goal with
| H : False |- ?G => destruct H
end.

Notation "f ˙ g" := (fun x => f (g x)) (at level 80).

Definition set (A : Type) := A -> bool.
Definition uni {A : Type} (a b : set A) :=
  fun x => (a x) || (b x).
Definition inters {A : Type} (a b : set A) :=
  fun x => (a x) && (b x).
Definition compl {A : Type} (a : set A) :=
  fun x => negb (a x).

Class DecEq {A : Type} := {
  deq (x y : A) : {x = y} + {x <> y}
}.

Print sumbool.

Definition deqb {A : Type} `{EqA : DecEq A} (a b : A) :=
  (if deq a b then true else false).
  
Theorem deqb_eq : forall (A: Type) `{EqA : DecEq A} (x y : A), deqb x y = true <-> x = y.
Proof.
  unfold deqb.
  intros.
  destruct (deq x y); now split.
Qed.

Notation "a =? b" := (if deq a b then true else false) (at level 70, no associativity).
Notation "a == b" := (deq a b) (at level 70, no associativity).

#[export] Program Instance DecEqPair {A B : Type} `(EqA : DecEq A, EqB : DecEq B) : @DecEq (prod A B) := {}.
Next Obligation.
Proof.
  destruct EqA as [H1].
  destruct EqB as [H2].
  destruct (H1 a0 a), (H2 b0 b);
  try (right; subst; intro; apply n; now inversion H).
  + left. now subst.
Qed.

Scheme Equality for list.

#[export] Program Instance DecEqList {A: Type} `(EqA : DecEq A) : @DecEq (list A) := {}.
Next Obligation.
Proof.
  eapply list_eq_dec; apply deqb_eq.
Qed.