From Coq Require Import Lists.List Nat Arith.EqNat Bool.Bool.
From TOC Require Import Lib DFA.
Import ListNotations.
Open Scope bool_scope.

Record nfa (Q Σ : Type) := {
  nstates : list Q;
  nchar : list Σ;
  ns : Q;
  nF : set Q;
  nδ : Q -> Σ -> list Q;
}.

Arguments nstates {Q} {Σ}.
Arguments nchar {Q} {Σ}.
Arguments ns {Q} {Σ}.
Arguments nF {Q} {Σ}.
Arguments nδ {Q} {Σ}.

Fixpoint ndelta_star {Q Σ : Type}
  (M : nfa Q Σ) (q : Q) (w : list Σ) :=
match w with
| []      => [q]
| x :: w' => flat_map (fun p => ndelta_star M p w') (nδ M q x)
end.

Lemma flat_map_comp :
forall (A B C : Type)
  (f : B -> list C)
  (g : A -> list B)
  (l : list A),
  flat_map f (flat_map g l) = flat_map (fun x => flat_map f (g x)) l.
Proof.
  intros.
  gendep f.
  gendep g.
  induct l.
  - rewrite <- IHl.
    apply flat_map_app.
Qed.

Theorem ndelta_step : forall (Q Σ : Type)
  (M : nfa Q Σ) (w : list Σ) (x : Σ) (q : Q),
  ndelta_star M q (w ++ [x]) = flat_map (fun p => nδ M p x) (ndelta_star M q w).
Proof.
  intros Q Σ M w.
  induct w.
  - rewrite app_nil_r.
    generalize (nδ M q x).
    induct l.
    + rewrite IHl.
      reflexivity.
  - simpl.
    rewrite flat_map_comp.
    generalize (nδ M q a).
    induct l.
    rewrite IHl.
    rewrite IHw.
    reflexivity.
Qed.

Section DfaToNfa.

Definition dfa_to_nfa {Q Σ : Type}
  (M : dfa Q Σ) : nfa Q Σ := {|
  nstates := M.(states);
  nchar := M.(char);
  ns := M.(s);
  nF := M.(F);
  nδ := fun p x => [M.(δ) p x];
|}.

Definition nacceptb {Q Σ : Type}
  (M : nfa Q Σ) (q : Q) (word : list Σ): bool :=
  existsb M.(nF) (ndelta_star M q word).

Definition nlang {Q Σ : Type} (M : nfa Q Σ) (word : list Σ) :=
  nacceptb M M.(ns) word.

Lemma dfa_to_nfa_step : forall (Q Σ : Type)
  (M : dfa Q Σ) (w : list Σ) (q: Q),
  [delta_star M q w] = ndelta_star (dfa_to_nfa M) q w.
Proof.
  induct' w rev_ind.
  now rewrite delta_step, ndelta_step, <- IHw.
Qed.

Theorem dfa_to_nfa_correct : forall (Q Σ : Type)
  (M : dfa Q Σ) (w : list Σ),
  lang M w = true <-> nlang (dfa_to_nfa M) w = true.
Proof.
  intros.
  unfold lang.
  unfold acceptb.
  unfold nlang.
  unfold nacceptb.
  induct' w rev_ind.
  - split; intros.
    + now rewrite H.
    + now repeat rewrite orb_false_r in H.
  - split; intros.
    + simpl in *.
      rewrite <- dfa_to_nfa_step in IHw.
      rewrite <- dfa_to_nfa_step.
      simpl in *.
      now rewrite orb_false_r.
    + simpl in *.
      rewrite <- dfa_to_nfa_step in H.
      simpl in H.
      now repeat rewrite orb_false_r in H.
Qed.

End DfaToNfa.

Section NfaToDfa.

Fixpoint powerset {A : Type} (l : list A) :=
match l with
| []      => [[]]
| x :: xs => map (fun l => x :: l) (powerset xs) ++ (powerset xs)
end.

Definition powerset_states {Q Σ : Type} (M : nfa Q Σ) := powerset M.(nstates).

Definition powerset_F {Q Σ : Type}
  (M : nfa Q Σ) (q : list Q) :=
  existsb M.(nF) q.

Definition powerset_delta {Q Σ : Type}
  (M : nfa Q Σ) (q : list Q) (x : Σ) :=
  flat_map (fun s => M.(nδ) s x) q.

Definition powerset_dfa {Q Σ : Type}
  (M : nfa Q Σ) : @dfa (list Q) Σ := {|
  states := powerset_states M;
  char := M.(nchar);
  s := [M.(ns)];
  F := powerset_F M;
  δ := powerset_delta M;
|}.

Theorem powerset_dfa_step : forall (Q Σ : Type)
  (M : nfa Q Σ) (w : list Σ),
  delta_star (powerset_dfa M) (powerset_dfa M).(s) w = ndelta_star M M.(ns) w.
Proof.
  intros Q Σ M w.
  induct' w rev_ind.
  - rewrite delta_step.
    rewrite ndelta_step.
    simpl in *.
    unfold powerset_delta.
    now rewrite IHw.
Qed.

Lemma existsb_orb : forall (A : Type) (f : A -> bool) (l : list A),
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

Theorem powerset_dfa_correct : forall (Q Σ : Type) (M : nfa Q Σ) (w : list Σ),
  lang (powerset_dfa M) w = true <-> nlang M w = true.
Proof.
  intros.
  unfold lang.
  unfold acceptb.
  unfold nlang.
  unfold nacceptb.
  induct' w rev_ind.
  - unfold powerset_F.
    now rewrite powerset_dfa_step.
Qed.

End NfaToDfa.