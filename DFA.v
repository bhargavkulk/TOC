(*|
.. coq:: none
|*)
From Coq Require Import Lists.List Nat Arith.EqNat Bool.Bool.
Require Import TOC.Lib.
Import ListNotations.
Open Scope bool_scope.
(*|
===========
DFAs in Coq
===========

.. contents:: Table of Contents

:alectryon/pygments/coq/tacn: induct induct' inv

DFAs are defined as a 5-tuples; A DFA :math:`M` is defined as 
:math:`(Q, \Sigma, s, F, \delta)`, where:

:math:`Q`
  is the finite set of states.

:math:`\Sigma`
  is the finite set of input symbols, also called the alphabet.

:math:`\delta : Q \times \Sigma \to Q`
  is the transition function.

:math:`s \in Q`
  is the initial or start state.

:math:`F \subseteq Q`
  is the set of final or accept states.

The Coq formalization is as follows:

.. coq::
|*)
Record dfa (Q Σ : Type) := {
  states : list Q;
  char : list Σ;
  s : Q;
  F : Q -> bool;
  δ : Q -> Σ -> Q;
}.

(*|
.. coq:: none
|*)
Arguments states {Q} {Σ}.
Arguments char {Q} {Σ}.
Arguments s {Q} {Σ}.
Arguments F {Q} {Σ}.
Arguments δ {Q} {Σ}.

(*|

:coq:`Type` is effectively infinite, so finiteness is ensured by also asking 
for a list of the states and characters of the alphabet. As a notion of finite 
sets has not been developed in this project, the notion of being a final state 
is defined as a boolean predicate; if :coq:`M.(F) q` is :coq:`true` then 
it is a final state, else it is not.

Computation
-----------

Computation is defined here using the :math:`\delta^*` function which is
defined in Coq as :coq:`delta_star`:

.. coq::
|*)
Fixpoint delta_star {Q Σ : Type} (M : dfa Q Σ) (p : Q) (x : list Σ) :=
  match x with
  | [] => p
  | x :: xs => delta_star M (M.(δ) p x) xs
end.
(*|

Some properties about :math:`\delta^*` are now proved.

.. coq::
|*)
Section DeltaStar.

  Variables Q Σ : Type.
  Variable M : dfa Q Σ.

  Lemma delta_cons : forall p a x, 
    delta_star M (δ M p a) x = delta_star M p (a :: x). (* .no-goals *)
  Proof. (* .no-goals *) trivial. Qed.

  Lemma delta_cat : forall p x y,
    delta_star M p (x ++ y) = delta_star M (delta_star M p x) y. (* .no-goals *)
  Proof. (* .no-goals *)
    intros p x. (* .no-goals *)
    gendep p.
    induct x.
(*|

The :coq:`induct` tactic is a custom tactic which tries to discharge the base 
case, because most base cases in induction proofs are easily solvablw with 
basic tactics. As you can see here, :coq:`induct x` skips the base case, and
moves on to the inductive case.

.. coq::
|*)
    - (* .no-goals *) rewrite IHx. reflexivity.
  Qed.

  Lemma delta_single: forall p a,
      M.(δ) p a = delta_star M p [a]. (* .no-goals *)
  Proof. (* .no-goals *) trivial. (* .no-goals *) Qed.

(*|

The following theorem, :coq:`delta_step` is important for future proofs. It is 
also another way to look at the :math:`\delta^*` function.

.. coq::
|*)

  Theorem delta_step: forall w p x,
    delta_star M p (w ++ [x]) = M.(δ) (delta_star M p w) x. (* .no-goals *)
  Proof. (* .no-goals *)
    induct w.
    - (* .no-goals *) rewrite IHw. reflexivity. (* .fold *)
  Qed.

End DeltaStar.

(*|

Acceptance for DFAs
-------------------

Acceptance of a word :math:`w` by a dfa :math:`M` is as simple as checking if 
:math:`\delta^*(s, w) \in F`.

.. coq::
|*)

Definition acceptb {Q Σ} (M : dfa Q Σ) word : bool :=
  M.(F) (delta_star M M.(s) word).

(*|

Complement of a DFA
-------------------

The complement construction of a DFA is very simpl. You only need to turn final 
states into non-final states and vice-versa. This is achieved in Coq by 
performing the boolean negation of :coq:`M.(F)`

.. coq::
|*)

Section Complement.

  Definition compl_dfa {Q Σ} (M: dfa Q Σ): dfa Q Σ := {|
    states := M.(states);
    char := M.(char);
    s := M.(s);
    F := fun x => negb (M.(F) x);
    δ := M.(δ);
  |}.

  Variables Q Σ : Type.
  Variable M : dfa Q Σ.

(*|

The lemma that follows is a **mirorring** lemma. It shows how both the original 
DFA and the complement DFA *move* together or *mirror* each other i.e. for the 
same input string, the complement DFA **must** land on the same state as the 
original DFA, provided we start from the same state.

.. coq::
|*)

  Lemma compl_dfa_step: forall p w,
    delta_star M p w = delta_star (compl_dfa M) p w. (* .no-goals *)
  Proof. (* .no-goals *)
    intros. (* .no-goals *)
    induct' w rev_ind.
    - (* .no-goals *) simpl in *.
      rewrite delta_step.
      rewrite delta_step.
      rewrite IHw.
      reflexivity.
  Qed.

(*|

We can then use this lemma to prove that our complement DFA constructions is 
actually correct i.e. 
:math:`w \in L(M) \longleftrightarrow w \notin L(\overline M)`.

.. coq::
|*)

  Theorem compl_dfa_correct: forall w,
    acceptb M w = true <-> acceptb (compl_dfa M) w = false. (* .no-goals *)
  Proof. (* .no-goals *)
    intros.
    unfold acceptb. (* .no-goals *)
    split. (* .no-goals *)
    all: rewrite compl_dfa_step;
         simpl;
         apply Bool.negb_false_iff.
  Qed.

(*|
.. coq:: none
|*)
  Lemma compl_dfa_correct_corr:
    forall word,
    acceptb M word = false <-> acceptb (compl_dfa M) word = true.
  Proof.
    intros.
    unfold acceptb.
    split.
    all: rewrite compl_dfa_step;
         simpl;
         intros;
         apply Bool.negb_true_iff;
         assumption.
  Qed.
(*|
.. coq::
|*)

End Complement.

(*|

Product Construction: Intersection and Union
--------------------------------------------

The intersection of two DFAs is now defined. Given DFAs :math:`M_1` and 
:math:`M_2` with the same :math:`\Sigma` we can define the intersection DFA 
:math:`M_\cap` as:

- :math:`Q_\cap = Q_1 \times Q_2`
- :math:`s_\cap = (s_1, s_2)`
- :math:`F_\cap = F_1 \cap F_2` i.e. :math:`(q_1, q_2) \in F_\cap \longleftrightarrow q_1 \in F_1 \wedge q_2 \in F_2` 
- :math:`\delta_\cap(q_1, q_2) = (\delta_1(q_1), \delta_2(q_2))`

|*)
Section Product.
Fixpoint pair_up {A B} a l : list (A * B) :=
  match l with
  | [] => []
  | x :: l' => (a, x) :: pair_up a l'
  end. (* .none *)
Fixpoint cross_product {A B} l1 l2 : list (A * B) :=
  match l1, l2 with
  | [], _ => []
  | _, [] => []
  | x :: l1', _ => pair_up x l2 ++ cross_product l1' l2
  end. (* .none *)

Definition inters_dfa {Q_1 Q_2 Σ} (M_1: dfa Q_1 Σ) (M_2: dfa Q_2 Σ) :
dfa (Q_1 * Q_2) Σ := {|
  states := cross_product (states M_1) (states M_2);
  char := (char M_1);
  s := (s M_1, s M_2);
  F := fun p => match p with (a, c) => (F M_1 a) && (F M_2 c) end;
  δ := fun p x => match p with (a, c) => (δ M_1 a x, δ M_2 c x) end;
|}.

(*|

What follows is the mirroring lemma for the intersection DFA...

.. coq::
|*)
Lemma inters_dfa_step Q_1 Q_2 Σ:
  forall (M_1: dfa Q_1 Σ) (M_2: dfa Q_2 Σ) p q w,
    delta_star (inters_dfa M_1 M_2) (p, q) w 
      = (delta_star M_1 p w, delta_star M_2 q w). (* .no-goals *)
Proof. (* .no-goals *)
  induct' w rev_ind.
  - (* .no-goals *) rewrite delta_step.
    rewrite IHw.
    simpl.
    rewrite delta_step.
    rewrite delta_step.
    reflexivity.
Qed.

(*|
...and the correctness of the intersection DFA.

.. coq::
|*)
Theorem inters_dfa_correct Q_1 Q_2 Σ: 
  forall (M_1: dfa Q_1 Σ) (M_2: dfa Q_2 Σ) w,
  acceptb (inters_dfa M_1 M_2) w = true
    <-> (acceptb M_1 w = true) /\ (acceptb M_2 w = true). (* .no-goals *)
Proof.
  unfold acceptb. (* .no-goals *)
  split.
  all: simpl;
       rewrite inters_dfa_step;
       apply Bool.andb_true_iff.
Qed.

(*|
.. coq:: none
|*)
Lemma inters_dfa_correct_corr Q_1 Q_2 Σ:
  forall (M_1: dfa Q_1 Σ) (M_2: dfa Q_2 Σ) w,
  acceptb (inters_dfa M_1 M_2) w = false 
    <-> (acceptb M_1 w = false) \/ (acceptb M_2 w = false).
Proof.
  unfold acceptb.
  split.
  all: simpl;
       rewrite inters_dfa_step;
       apply Bool.andb_false_iff.
Qed.
(*|

The union DFA is defined very easily using DeMorgan's law:

.. math::
  
  M_\cup = \overline{\overline{M_1} \cap \overline{M_2}}

, which we define as such in Coq...

.. coq::
|*)
Definition union_dfa {Q_1 Q_2 Σ} (M_1: dfa Q_1 Σ) (M_2: dfa Q_2 Σ) :=
  compl_dfa (inters_dfa (compl_dfa M_1) (compl_dfa M_2)).

(*|

...and then prove its correctness.

.. coq::
|*)
Theorem union_dfa_correct Q_1 Q_2 Σ:
  forall (M_1: dfa Q_1 Σ) (M_2: dfa Q_2 Σ) w,
  acceptb (union_dfa M_1 M_2) w = true 
    <-> (acceptb M_1 w = true) \/ (acceptb M_2 w = true). (* .no-goals *)
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