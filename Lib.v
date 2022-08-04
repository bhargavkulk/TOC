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

Fixpoint pair_up {A B} a l : list (A * B) :=
  match l with
  | [] => []
  | x :: l' => (a, x) :: pair_up a l'
  end.

Fixpoint cross_product {A B} l1 l2 : list (A * B) :=
  match l1, l2 with
  | [], _ => []
  | _, [] => []
  | x :: l1', _ => pair_up x l2 ++ cross_product l1' l2
  end.

Fixpoint powerset {A} (l : list A) :=
match l with
| []      => [[]]
| x :: xs => map (fun l => x :: l) (powerset xs) ++ (powerset xs)
end.

Lemma flat_map_comp :
forall A B C
  (f : B -> list C)
  (g : A -> list B)
  l,
  flat_map f (flat_map g l) = flat_map (fun x => flat_map f (g x)) l.
Proof.
  intros.
  gendep f.
  gendep g.
  induct l.
  - rewrite <- IHl.
    apply flat_map_app.
Qed.

Lemma existsb_orb : forall A (f : A -> bool) l,
  existsb f l = true <-> existsb (fun a => f a || false) l = true.
Proof.
  induct l.
  - split; intros.
    + apply orb_true_iff in H as [H | H].
      * apply orb_true_iff. left.
        apply orb_true_iff. now left.
      * apply orb_true_iff. right.
        now apply IHl in H.
    + apply orb_true_iff in H as [H | H].
      apply orb_true_iff in H as [H | H].
      * apply orb_true_iff. now left.
      * discriminate.
      * apply orb_true_iff. right.
        now apply IHl in H.
Qed.