(*|
.. raw:: html

  <style>
    .highlight, .code .hll {
      background-color: #ffffff;
    }

    .alectryon-coqdoc .doc .code, .alectryon-coqdoc .doc .comment,
    .alectryon-coqdoc .doc .inlinecode, .alectryon-mref, .alectryon-block,
    .alectryon-io, .alectryon-toggle-label, .alectryon-banner {
      font-family: 'Fira Code', monospace;
    }
  </style>

===========
NFAs in Coq
===========

:alectryon/pygments/coq/tacn: induct induct' inv

.. contents:: Table of Contents

.. coq:: none
|*)
From Coq Require Import Lists.List Nat Arith.EqNat Bool.Bool.
From TOC Require Import Lib DFA.
Import ListNotations.
Open Scope bool_scope.

(*|
NFAs are defined as a 5-tuples; A NFA :math:`M` is defined as 
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

.. coq:: none
|*)
Record nfa (Q Σ : Type) := {
  nstates : list Q;
  nchar : list Σ;
  ns : Q;
  nF : Q -> bool;
  nδ : Q -> Σ -> list Q;
}.

(*|
.. coq:: none
|*)
Arguments nstates {Q} {Σ}.
Arguments nchar {Q} {Σ}.
Arguments ns {Q} {Σ}.
Arguments nF {Q} {Σ}.
Arguments nδ {Q} {Σ}.

(*|
Computation
-----------

Computation is defined here again using the :math:`\delta^*` function:

.. math::

    &\delta^* : Q \times \Sigma^* \to \mathcal{P}(Q) \\
    &\delta^*(q, \varepsilon) = \{q\} \\
    &\delta^*(q, x \cdot w') = \bigcup_{s \in \delta(q, x)}\delta^* (s, w)

This function intuitively computes the list of possible states that the NFA 
could land on given a certain input string and a starting state. This is 
defined in Coq as:

.. coq::
|*)
Fixpoint ndelta_star {Q Σ} (M : nfa Q Σ) q w :=
match w with
| []      => [q]
| x :: w' => flat_map (fun p => ndelta_star M p w') (nδ M q x)
end.

(*|

The following theorem, :coq:`ndelta_step` is similiar to the :coq:`delta_step` 
theorem proved for DFAs_.

.. _DFAs: DFA.html

.. coq::
|*)
Theorem ndelta_step Q Σ : forall (M : nfa Q Σ) w x q,
  ndelta_star M q (w ++ [x]) 
    = flat_map (fun p => nδ M p x) (ndelta_star M q w). (* .no-goals *)
Proof.
  intros M w.
  induct w.
  - rewrite app_nil_r.
    generalize (nδ M q x).
    induct l.
    + rewrite IHl.
      reflexivity.
  - simpl.
    Check flat_map_comp. (* .unfold .no-goals .no-hyps .no-in *)
    rewrite flat_map_comp.
    generalize (nδ M q a).
    induct l.
    + rewrite IHl.
      rewrite IHw.
      reflexivity.
Qed.

(*|

Acceptance for NFAs
-------------------

Acceptance of a word :math:`w` by a nfa :math:`M` is as simple as checking if
there exists a state :math:`q \in \delta^*(s, w)` such that, :math:`q \in F`. 

.. coq::
|*)
Definition nacceptb {Q Σ} (M : nfa Q Σ) word : bool :=
  existsb M.(nF) (ndelta_star M M.(ns) word).

(*|

Equivalence of DFAs and NFAs
----------------------------

To show that DFAs and NFAs are equally *powerful*, we only need to convert one 
to other and vice-versa, and show that the conversion is correct.

DFA :math:`\longrightarrow` NFA
```````````````````````````````

Given a dfa :math:`M`, the corresponding NFA :math:`N` is defined as:

- :math:`Q_N = Q_M`
- :math:`s_N = s_M`
- :math:`F_N = F_M`
- :math:`\delta_N(p, x) = \{\delta_M(p, x)\}`

.. coq::
|*)

Section DfaToNfa.

  Definition dfa_to_nfa {Q Σ} (M : dfa Q Σ) : nfa Q Σ := {| 
    nstates := M.(states);
    nchar := M.(char);
    ns := M.(s);
    nF := M.(F);
    nδ := fun p x => [M.(δ) p x]; 
  |}.

(*|

As we did for the the proofs for `DFAs <DFA.html>`_, we prove a mirroring 
lemma...

.. coq::
|*)

  Lemma dfa_to_nfa_step Q Σ: forall (M : dfa Q Σ) w q,
    [delta_star M q w] = ndelta_star (dfa_to_nfa M) q w. (* .no-goals *)
  Proof.
    induct' w rev_ind.
    Check delta_step. (* .unfold .no-goals .no-hyps .no-in *)
    now rewrite delta_step, ndelta_step, <- IHw.
  Qed.

(*|

...and then prove our ocnstruction is correct.

.. coq::
|*)
  Theorem dfa_to_nfa_correct Q Σ : forall (M : dfa Q Σ) w,
    acceptb M w = true 
      <-> nacceptb (dfa_to_nfa M) w = true. (* .no-goals *)
  Proof.
    intros.
    unfold acceptb.
    unfold nacceptb.
    induct' w rev_ind.
    - split; intros.
      + now rewrite H.
      Check orb_false_r. (* .unfold .no-goals .no-hyps .no-in *)
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

(*|

NFA :math:`\longrightarrow` DFA
```````````````````````````````

This construction, also called the powerset construction is a bit more involved.
Here on, :math:`N` is a NFA and :math:`M` is the DFA constructed from :math:`N`.
|*)

Section NfaToDfa.
(*|

Firstly, :math:`Q_M = \mathcal{P}(Q_N)`.

.. coq::
|*)
  Definition powerset_states {Q Σ} (M : nfa Q Σ) := 
    powerset M.(nstates).

(*|

Then, :math:`F_M = \{q \subseteq \mathcal{P}(Q) \mid \exists p \in q, p \in F_N\}`

.. coq::
|*)
  Definition powerset_F {Q Σ} (M : nfa Q Σ) q :=
    existsb M.(nF) q.
(*|

Then, :math:`\delta_M = \bigcup_{p \in q}\delta_N(p, x)`

.. coq::
|*)
  Definition powerset_delta {Q Σ} (M : nfa Q Σ) q x :=
    flat_map (fun s => M.(nδ) s x) q.

(*|

And with that we can construct a DFA from an NFA.

.. coq::
|*)
  Definition powerset_dfa {Q Σ} (M : nfa Q Σ) 
    : dfa (list Q) Σ := {|
    states := powerset_states M;
    char := M.(nchar);
    s := [M.(ns)];
    F := powerset_F M;
    δ := powerset_delta M;
  |}.

(*|

We then prove the mirroring lemma...

.. coq::
|*)
  Theorem powerset_dfa_step Q Σ: forall (M : nfa Q Σ) w,
    delta_star (powerset_dfa M) (powerset_dfa M).(s) w 
      = ndelta_star M M.(ns) w. (* .no-goals *)
  Proof.
    induct' w rev_ind.
    - rewrite delta_step.
      rewrite ndelta_step.
      simpl in *.
      unfold powerset_delta.
      now rewrite IHw.
  Qed.

(*|

...then prove the correctness of the construction.

.. coq::
|*)
  Theorem powerset_dfa_correct Q Σ: forall (M : nfa Q Σ) w,
    acceptb (powerset_dfa M) w = true <-> nacceptb M w = true. (* .no-goals *)
  Proof.
    intros.
    unfold acceptb.
    unfold nacceptb.
    induct' w rev_ind.
    - unfold powerset_F.
      now rewrite powerset_dfa_step.
  Qed.

End NfaToDfa.

(*|
Back to `project index <index.html>`_.
|*)