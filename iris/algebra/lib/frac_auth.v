From iris.algebra Require Export frac auth updates local_updates.
From iris.algebra Require Import proofmode_classes.
From iris.prelude Require Import options.

(** Authoritative CMRA where both parts can be fractional. This CMRA allows the
  original elements [● a] and [◯ a] to be split into fractional parts [●F dq a]
  and [◯F{q} a]. Using  [●F a ≡ ●F{#1} a] or [◯F a ≡ ◯F{1} a] is in effect the
  same as using the original [● a] and [◯ a].

  These fractions don't split the same way, to make the laws more useful. A
  fractional authoritative element [●F dq a] says that the authoritative
  element is actually [a]. Splitting the fraction duplicates this knowledge:
  [●F{#q1+q2} a ≡ ●F{#q1} a ⋅ ●F{#q2} a]. A fractional non-authoritative
  element [◯F{q} a] only says that the authoritative element is *at least* [a],
  and splitting the fraction splits this lower bound:
  [◯F{q1+q2} (a1 ⋅ a2) ≡ ◯F{q1} a1 ⋅ ◯F{q2} a2].
*)

Definition frac_authR {SI : sidx} (A : cmra) : cmra :=
  authR (optionUR (prodR fracR A)).
Definition frac_authUR {SI : sidx} (A : cmra) : ucmra :=
  authUR (optionUR (prodR fracR A)).

Definition frac_auth_auth {SI : sidx} {A : cmra}
    (dq : dfrac) (x : A) : frac_authR A :=
  ●{dq} (Some (1%Qp,x)).
Definition frac_auth_frag {SI : sidx}
    {A : cmra} (q : frac) (x : A) : frac_authR A :=
  ◯ (Some (q,x)).

Global Typeclasses Opaque frac_auth_auth frac_auth_frag.

Global Instance: Params (@frac_auth_auth) 3 := {}.
Global Instance: Params (@frac_auth_frag) 3 := {}.

Notation "●F dq a" := (frac_auth_auth dq a)
  (at level 10, dq custom dfrac at level 1, format "●F dq  a").
Notation "◯F{ q } a" := (frac_auth_frag q a) (at level 10, format "◯F{ q }  a").
Notation "◯F a" := (frac_auth_frag 1 a) (at level 10).

Section frac_auth.
  Context {SI : sidx} {A : cmra}.
  Implicit Types a b : A.

  Global Instance frac_auth_auth_ne dq : NonExpansive (@frac_auth_auth SI A dq).
  Proof. solve_proper. Qed.
  Global Instance frac_auth_auth_proper dq :
    Proper ((≡) ==> (≡)) (@frac_auth_auth SI A dq).
  Proof. solve_proper. Qed.
  Global Instance frac_auth_frag_ne q : NonExpansive (@frac_auth_frag SI A q).
  Proof. solve_proper. Qed.
  Global Instance frac_auth_frag_proper q :
    Proper ((≡) ==> (≡)) (@frac_auth_frag SI A q).
  Proof. solve_proper. Qed.

  Global Instance frac_auth_auth_discrete dq a : Discrete a → Discrete (●F{dq} a).
  Proof. intros; apply auth_auth_discrete; [apply Some_discrete|]; apply _. Qed.
  Global Instance frac_auth_frag_discrete q a : Discrete a → Discrete (◯F{q} a).
  Proof. intros; apply auth_frag_discrete, Some_discrete; apply _. Qed.

  Lemma frac_auth_dfrac_validN dq n a : ✓ dq → ✓{n} a → ✓{n} (●F{dq} a ⋅ ◯F a).
  Proof. by rewrite auth_both_dfrac_validN Some_validN. Qed.
  Lemma frac_auth_validN n a : ✓{n} a → ✓{n} (●F a ⋅ ◯F a).
  Proof. by apply frac_auth_dfrac_validN. Qed.
  Lemma frac_auth_dfrac_valid dq a : ✓ dq → ✓ a → ✓ (●F{dq} a ⋅ ◯F a).
  Proof. intros. by apply auth_both_dfrac_valid_2. Qed.
  Lemma frac_auth_valid a : ✓ a → ✓ (●F a ⋅ ◯F a).
  Proof. by apply frac_auth_dfrac_valid. Qed.

  Lemma frac_auth_agreeN n dq a b : ✓{n} (●F{dq} a ⋅ ◯F b) → a ≡{n}≡ b.
  Proof.
    rewrite auth_both_dfrac_validN /= => -[? [Hincl Hvalid]].
    by move: Hincl=> /Some_includedN_exclusive /(_ Hvalid ) [??].
  Qed.
  Lemma frac_auth_agree dq a b : ✓ (●F{dq} a ⋅ ◯F b) → a ≡ b.
  Proof.
    intros. apply equiv_dist=> n. by eapply frac_auth_agreeN, cmra_valid_validN.
  Qed.
  Lemma frac_auth_agree_L `{!LeibnizEquiv A} dq a b :
    ✓ (●F{dq} a ⋅ ◯F b) →
    a = b.
  Proof. intros. by eapply leibniz_equiv, frac_auth_agree. Qed.

  Lemma frac_auth_includedN n dq q a b :
    ✓{n} (●F{dq} a ⋅ ◯F{q} b) →
    Some b ≼{n} Some a.
  Proof.
    by rewrite auth_both_dfrac_validN /= => -[? [/Some_pair_includedN [_ ?] _]].
  Qed.
  Lemma frac_auth_included `{!CmraDiscrete A} dq q a b :
    ✓ (●F{dq} a ⋅ ◯F{q} b) → Some b ≼ Some a.
  Proof.
    by rewrite auth_both_dfrac_valid_discrete /=
      => -[? [/Some_pair_included [_ ?] _]].
  Qed.
  Lemma frac_auth_includedN_total `{!CmraTotal A} n dq q a b :
    ✓{n} (●F{dq} a ⋅ ◯F{q} b) → b ≼{n} a.
  Proof. intros. by eapply Some_includedN_total, frac_auth_includedN. Qed.
  Lemma frac_auth_included_total `{!CmraDiscrete A, !CmraTotal A} dq q a b :
    ✓ (●F{dq} a ⋅ ◯F{q} b) → b ≼ a.
  Proof. intros. by eapply Some_included_total, frac_auth_included. Qed.

  Lemma frac_auth_auth_dfrac_validN n dq a : ✓{n} (●F{dq} a) ↔ ✓ dq ∧ ✓{n} a.
  Proof.
    rewrite auth_auth_dfrac_validN Some_validN. split.
    - by intros [?[]].
    - intros [??]; by split.
  Qed.
  Lemma frac_auth_auth_validN n a : ✓{n} (●F a) ↔ ✓{n} a.
  Proof.
    rewrite frac_auth_auth_dfrac_validN. split.
    - by intros [_ ?].
    - done.
  Qed.

  Lemma frac_auth_auth_dfrac_valid dq a : ✓ (●F{dq} a) ↔ ✓ dq ∧ ✓ a.
  Proof.
    rewrite auth_auth_dfrac_valid Some_valid. split.
    - by intros [?[]].
    - intros [??]; by split.
  Qed.
  Lemma frac_auth_auth_valid a : ✓ (●F a) ↔ ✓ a.
  Proof.
    rewrite frac_auth_auth_dfrac_valid. split.
    - by intros [_ ?].
    - done.
  Qed.

  Lemma frac_auth_frag_validN n q a : ✓{n} (◯F{q} a) ↔ (q ≤ 1)%Qp ∧ ✓{n} a.
  Proof. by rewrite /frac_auth_frag auth_frag_validN. Qed.
  Lemma frac_auth_frag_valid q a : ✓ (◯F{q} a) ↔ (q ≤ 1)%Qp ∧ ✓ a.
  Proof. by rewrite /frac_auth_frag auth_frag_valid. Qed.

  Lemma frac_auth_auth_dfrac_op dq1 dq2 a :
    ●F{dq1⋅dq2} a ≡ ●F{dq1} a ⋅ ●F{dq2} a.
  Proof. by rewrite /frac_auth_auth -auth_auth_dfrac_op. Qed.
  Lemma frac_auth_frag_op q1 q2 a1 a2 :
    ◯F{q1+q2} (a1 ⋅ a2) ≡ ◯F{q1} a1 ⋅ ◯F{q2} a2.
  Proof. done. Qed.

  Lemma frac_auth_auth_dfrac_op_validN n dq1 dq2 a b :
    ✓{n} (●F{dq1} a ⋅ ●F{dq2} b) → ✓ (dq1 ⋅ dq2)  ∧ a ≡{n}≡ b.
  Proof.
    rewrite auth_auth_dfrac_op_validN.
    intros [?[[_?]%Some_dist_inj%pair_dist_inj ?]]; by split.
  Qed.
  Lemma frac_auth_auth_op_validN n a b :
    ✓{n} (●F a ⋅ ●F b) → False.
  Proof. by intros [? _]%frac_auth_auth_dfrac_op_validN. Qed.

  Lemma frac_auth_auth_dfrac_op_valid dq1 dq2 a b :
    ✓ (●F{dq1} a ⋅ ●F{dq2} b) → ✓ (dq1 ⋅ dq2) ∧ a ≡ b.
  Proof.
    rewrite auth_auth_dfrac_op_valid.
    intros [?[[_?]%Some_equiv_inj%pair_equiv_inj ?]]; by split.
  Qed.
  Lemma frac_auth_auth_op_valid a b :
    ✓ (●F a ⋅ ●F b) → False.
  Proof. by intros [? _]%frac_auth_auth_dfrac_op_valid. Qed.

  Lemma frac_auth_frag_op_validN n q1 q2 a b :
    ✓{n} (◯F{q1} a ⋅ ◯F{q2} b) ↔ (q1 + q2 ≤ 1)%Qp ∧ ✓{n} (a ⋅ b).
  Proof. by rewrite -frac_auth_frag_op frac_auth_frag_validN. Qed.
  Lemma frac_auth_frag_op_valid q1 q2 a b :
    ✓ (◯F{q1} a ⋅ ◯F{q2} b) ↔ (q1 + q2 ≤ 1)%Qp ∧ ✓ (a ⋅ b).
  Proof. by rewrite -frac_auth_frag_op frac_auth_frag_valid. Qed.

  Global Instance frac_auth_is_op (q q1 q2 : frac) (a a1 a2 : A) :
    IsOp q q1 q2 → IsOp a a1 a2 → IsOp' (◯F{q} a) (◯F{q1} a1) (◯F{q2} a2).
  Proof. by rewrite /IsOp' /IsOp=> /leibniz_equiv_iff -> ->. Qed.

  Global Instance frac_auth_is_op_core_id (q q1 q2 : frac) (a  : A) :
    CoreId a → IsOp q q1 q2 → IsOp' (◯F{q} a) (◯F{q1} a) (◯F{q2} a).
  Proof.
    rewrite /IsOp' /IsOp=> ? /leibniz_equiv_iff ->.
    by rewrite -frac_auth_frag_op -core_id_dup.
  Qed.

  Lemma frac_auth_update q a b a' b' :
    (a,b) ~l~> (a',b') → ●F a ⋅ ◯F{q} b ~~> ●F a' ⋅ ◯F{q} b'.
  Proof.
    intros. by apply auth_update, option_local_update, prod_local_update_2.
  Qed.

  Lemma frac_auth_update_1 a b a' : ✓ a' → ●F a ⋅ ◯F b ~~> ●F a' ⋅ ◯F a'.
  Proof.
    intros. by apply auth_update, option_local_update, exclusive_local_update.
  Qed.

  Lemma frac_auth_update_auth_persist dq a : ●F{dq} a ~~> ●F□ a.
  Proof. apply auth_update_auth_persist. Qed.
  Lemma frac_auth_updateP_auth_unpersist a :
    ●F□ a ~~>: λ k, ∃ q, k = ●F{#q} a.
  Proof. apply auth_updateP_auth_unpersist. Qed.
  Lemma frac_auth_updateP_both_unpersist q a b :
    ●F□ a ⋅ ◯F{q} b ~~>: λ k, ∃ q', k = ●F{#q'} a ⋅ ◯F{q} b.
  Proof. apply auth_updateP_both_unpersist. Qed.
End frac_auth.

Definition frac_authURF {SI : sidx} (F : rFunctor) : urFunctor :=
  authURF (optionURF (prodRF (constRF fracR) F)).

Global Instance frac_authURF_contractive {SI : sidx} F :
  rFunctorContractive F → urFunctorContractive (frac_authURF F).
Proof. apply _. Qed.

Definition frac_authRF {SI : sidx} (F : rFunctor) : rFunctor :=
  authRF (optionURF (prodRF (constRF fracR) F)).

Global Instance frac_authRF_contractive {SI : sidx} F :
  rFunctorContractive F → rFunctorContractive (frac_authRF F).
Proof. apply _. Qed.
