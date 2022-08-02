From Coq Require Import Lists.List Nat Arith.EqNat Bool.Bool.
Require Import TOC.Lib.
Import ListNotations.
Open Scope bool_scope.

Record dfa (Q Σ : Type) := {
  states : list Q;
  char : list Σ;
  s : Q;
  F : set Q;
  δ : Q -> Σ -> Q;
}.

Arguments states {Q} {Σ}.
Arguments char {Q} {Σ}.
Arguments s {Q} {Σ}.
Arguments F {Q} {Σ}.
Arguments δ {Q} {Σ}.

Fixpoint delta_star {Q Σ : Type} (M : dfa Q Σ) (p : Q) (x : list Σ) :=
  match x with
  | [] => p
  | x :: xs => delta_star M (δ M p x) xs
end.

Section DeltaCap.

Variables Q Σ : Type.
Variable M : dfa Q Σ.

Lemma delta_cons : forall p a x, 
  delta_star M (δ M p a) x = delta_star M p (a :: x).
Proof. reflexivity. Qed.

Lemma delta_cat : forall p x y,
  delta_star M p (x ++ y) = delta_star M (delta_star M p x) y.
Proof.
  intros p x.
  gendep p.
  induct x.
  - rewrite IHx. reflexivity.
Qed.

Lemma delta_single: forall p a,
    δ M p a = delta_star M p [a].
Proof. reflexivity. Qed.

Lemma delta_step: forall w p x,
  delta_star M p (w ++ [x]) = δ M (delta_star M p w) x.
Proof.
  intros.
  gendep p.
  gendep x.
  induct w.
  - auto.
Qed.

End DeltaCap.

Definition acceptb {Q Σ : Type} (M : dfa Q Σ) (q : Q) (word : list Σ): bool :=
  F M (delta_star M q word).

Definition lang {Q Σ : Type} (M : dfa Q Σ) (word : list Σ) :=
  acceptb M (s M) word.

Section DfaAcceptance.

Variables Q Σ : Type.
Variable M : dfa Q Σ.

Lemma acceptb_nil : forall p,
  acceptb M p [] = F M p.
Proof. reflexivity. Qed.

Lemma acceptb_cons : forall p a w,
  acceptb M p (a :: w) = acceptb M (δ M p a) w.
Proof. reflexivity. Qed.

End DfaAcceptance.

Section Complement.

Definition compl_dfa {Q Σ: Type} (M: dfa Q Σ): dfa Q Σ := {|
  states := M.(states);
  char := M.(char);
  s := M.(s);
  F := fun x => negb (M.(F) x);
  δ := M.(δ);
|}.

Variables Q Σ : Type.
Variable M : dfa Q Σ.

Lemma compl_dfa_star: forall p w,
  delta_star M p w = delta_star (compl_dfa M) p w.
Proof.
  intros.
  induct' w rev_ind.
  - simpl in *.
    rewrite delta_step.
    rewrite delta_step.
    rewrite IHw.
    reflexivity.
Qed.

Theorem compl_dfa_correct: forall w,
  lang M w = true <-> lang (compl_dfa M) w = false.
Proof.
  intros.
  unfold lang.
  unfold acceptb.
  split;
    rewrite compl_dfa_star;
    simpl;
    apply Bool.negb_false_iff.
Qed.

Lemma compl_dfa_correct_corr:
  forall word,
  lang M word = false <-> lang (compl_dfa M) word = true.
Proof.
  intros.
  unfold lang.
  unfold acceptb.
  split;
    rewrite compl_dfa_star;
    simpl;
    intros;
    apply Bool.negb_true_iff;
    assumption.
Qed.

End Complement.

Section Product.

Fixpoint pair_up {A B: Type} (a: A) (l: list B): list (A * B) :=
  match l with
  | [] => []
  | x :: l' => (a, x) :: pair_up a l'
  end.

Fixpoint cross_product {A B: Type} (l1: list A) (l2: list B): list (A * B) :=
  match l1, l2 with
  | [], _ => []
  | _, [] => []
  | x :: l1', _ => pair_up x l2 ++ cross_product l1' l2
  end.

(* assuming M_1.(char) == M_2.(char) *)
Definition inters_dfa {A B C: Type} (M_1: dfa A B) (M_2: dfa C B) :
@dfa (A * C) B := {|
  states := cross_product (states M_1) (states M_2);
  char := (char M_1);
  s := (s M_1, s M_2);
  F := fun p => match p with (a, c) => (F M_1 a) && (F M_2 c) end;
  δ := fun p x => match p with (a, c) => (δ M_1 a x, δ M_2 c x) end;
|}.

Lemma inters_dfa_star:
  forall (A B Σ: Type) (M_1: dfa A Σ) (M_2: dfa B Σ) (p: A) (q: B) (w: list Σ),
  delta_star (inters_dfa M_1 M_2) (p, q) w = (delta_star M_1 p w, delta_star M_2 q w).
Proof.
  induct' w rev_ind.
  - (* w = w'x *)
    rewrite delta_step.
    rewrite IHw.
    simpl.
    rewrite delta_step.
    rewrite delta_step.
    reflexivity.
Qed.

Theorem inters_dfa_correct: 
  forall {A B Σ: Type} (M_1: dfa A Σ) (M_2: dfa B Σ) (w: list Σ),
  lang (inters_dfa M_1 M_2) w = true <-> (lang M_1 w = true) /\ (lang M_2 w = true).
Proof.
  unfold lang.
  split;
    simpl;
    rewrite inters_dfa_star;
    apply Bool.andb_true_iff.
Qed.

Lemma inters_dfa_correct_corr:
  forall {A B Σ: Type} (M_1: dfa A Σ) (M_2: dfa B Σ) (w: list Σ),
  lang (inters_dfa M_1 M_2) w = false <-> (lang M_1 w = false) \/ (lang M_2 w = false).
Proof.
  unfold lang.
  split;
    simpl;
    rewrite inters_dfa_star;
    apply Bool.andb_false_iff.
Qed.

Definition union_dfa {A B Σ: Type} (M_1: dfa A Σ) (M_2: dfa B Σ): dfa (A * B) Σ :=
  compl_dfa (inters_dfa (compl_dfa M_1) (compl_dfa M_2)).

Theorem union_dfa_correct:
  forall {A B Σ: Type} (M_1: dfa A Σ) (M_2: dfa B Σ) (w: list Σ),
  lang (union_dfa M_1 M_2) w = true <-> (lang M_1 w = true) \/ (lang M_2 w = true).
Proof.
  split; unfold union_dfa; intros.
  - apply compl_dfa_correct_corr in H.
    apply inters_dfa_correct_corr in H.
    destruct H as [H | H];
    apply compl_dfa_correct in H;
    [left | right];
    assumption.
  - apply compl_dfa_correct_corr.
    apply inters_dfa_correct_corr.
    destruct H as [H | H];
    apply compl_dfa_correct in H;
    [left | right];
    assumption.
Qed.

End Product.