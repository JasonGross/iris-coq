From iris.bi Require Export derived_connectives extensions.
From iris.bi Require Export sbi updates internal_eq plainly cmra.
From iris.si_logic Require Export bi.
From iris.bi Require Import derived_laws derived_laws_later.
From iris.base_logic Require Export upred.
From iris.prelude Require Import options.
Import uPred_primitive.

Local Existing Instance entails_po.

(** BI instances for [uPred], and re-stating the remaining primitive laws in
terms of the BI interface. This file does *not* unseal. *)

(** [uPred_pure] is a derived notion on [uPred] in terms of [uPred_si_pure].
However, in terms of the BI hierarchy, [bi_pure] it is a primitive notion that
is "below" the concept of an [Sbi], so we cannot use the fact that [uPred] is an
SBI to our advantage here. Below we define [uPred_pure] and derive its laws from
those of [uPred_si_pure]. *)
Definition uPred_pure {M} (φ : Prop) : uPred M := uPred_si_pure ⌜ φ ⌝.
Definition uPred_emp {M} : uPred M := uPred_pure True.

Local Lemma pure_ne {M} n : Proper (iff ==> dist n) (@uPred_pure M).
Proof. intros φ1 φ2 Hφ. apply si_pure_ne. by rewrite Hφ. Qed.

Local Lemma pure_intro {M} (φ : Prop) (P : uPred M) :
  φ → uPred_entails P (uPred_pure φ).
Proof.
  intros. trans (uPred_si_pure (∀ x : False, True) : uPred M).
  - etrans; last apply si_pure_forall_2. by apply forall_intro.
  - by apply si_pure_mono, bi.pure_intro.
Qed.

Local Lemma pure_elim' {M} (φ : Prop) (P : uPred M) :
  (φ → uPred_entails (uPred_pure True) P) →
  uPred_entails (uPred_pure φ) P.
Proof.
  intros HφP. etrans; last apply persistently_elim.
  etrans; last apply si_pure_si_emp_valid.
  apply si_pure_mono. apply bi.pure_elim'=> ?.
  rewrite -(si_emp_valid_si_pure True). by apply si_emp_valid_mono, HφP.
Qed.

Lemma uPred_bi_mixin (M : ucmra) :
  BiMixin
    uPred_entails uPred_emp uPred_pure uPred_and uPred_or uPred_impl
    (@uPred_forall M) (@uPred_exist M) uPred_sep uPred_wand.
Proof.
  split.
  - exact: entails_po.
  - exact: equiv_entails.
  - exact: pure_ne.
  - exact: and_ne.
  - exact: or_ne.
  - exact: impl_ne.
  - exact: forall_ne.
  - exact: exist_ne.
  - exact: sep_ne.
  - exact: wand_ne.
  - exact: pure_intro.
  - exact: pure_elim'.
  - exact: and_elim_l.
  - exact: and_elim_r.
  - exact: and_intro.
  - exact: or_intro_l.
  - exact: or_intro_r.
  - exact: or_elim.
  - exact: impl_intro_r.
  - exact: impl_elim_l'.
  - exact: @forall_intro.
  - exact: @forall_elim.
  - exact: @exist_intro.
  - exact: @exist_elim.
  - exact: sep_mono.
  - exact: True_sep_1.
  - exact: True_sep_2.
  - exact: sep_comm'.
  - exact: sep_assoc'.
  - exact: wand_intro_r.
  - exact: wand_elim_l'.
Qed.

Lemma uPred_bi_persistently_mixin (M : ucmra) :
  BiPersistentlyMixin
    uPred_entails uPred_emp uPred_and
    (@uPred_exist M) uPred_sep uPred_persistently.
Proof.
  split.
  - exact: persistently_ne.
  - exact: persistently_mono.
  - exact: persistently_idemp_2.
  - (* emp ⊢ <pers> emp (ADMISSIBLE) *)
    trans (uPred_forall (M:=M) (λ _ : False, uPred_persistently uPred_emp)).
    + apply forall_intro=>-[].
    + etrans; first exact: persistently_forall_2.
      by apply persistently_mono, pure_intro.
  - (* ((<pers> P) ∧ (<pers> Q)) ⊢ <pers> (P ∧ Q) (ADMISSIBLE) *)
    intros P Q.
    trans (uPred_forall (M:=M) (λ b : bool, uPred_persistently (if b then P else Q))).
    + apply forall_intro=>[[]].
      * apply and_elim_l.
      * apply and_elim_r.
    + etrans; first exact: persistently_forall_2.
      apply persistently_mono. apply and_intro.
      * etrans; first apply (forall_elim true). done.
      * etrans; first apply (forall_elim false). done.
  - exact: @persistently_exist_1.
  - (* <pers> P ∗ Q ⊢ <pers> P (ADMISSIBLE) *)
    intros. etrans; first exact: sep_comm'.
    etrans; last exact: True_sep_2.
    apply sep_mono; last done. by apply pure_intro.
  - exact: persistently_and_sep_l_1.
Qed.

Lemma uPred_bi_later_mixin (M : ucmra) :
  BiLaterMixin
    uPred_entails uPred_pure uPred_or uPred_impl
    (@uPred_forall M) (@uPred_exist M) uPred_sep uPred_persistently uPred_later.
Proof.
  split.
  - apply contractive_ne, later_contractive.
  - exact: later_mono.
  - exact: later_intro.
  - exact: @later_forall_2.
  - exact: @later_exist_false.
  - exact: later_sep_1.
  - exact: later_sep_2.
  - exact: later_persistently_1.
  - exact: later_persistently_2.
  - exact: later_false_em.
Qed.

Canonical Structure uPredI (M : ucmra) : bi :=
  {| bi_ofe_mixin := ofe_mixin_of (uPred M);
     bi_bi_mixin := uPred_bi_mixin M;
     bi_bi_later_mixin := uPred_bi_later_mixin M;
     bi_bi_persistently_mixin := uPred_bi_persistently_mixin M |}.

Lemma uPred_sbi_mixin M : SbiMixin (uPredI M) uPred_si_pure uPred_si_emp_valid.
Proof.
  split.
  - exact: si_pure_ne.
  - exact: si_emp_valid_ne.
  - exact: si_pure_mono.
  - exact: si_emp_valid_mono.
  - exact: si_emp_valid_si_pure.
  - exact: si_pure_si_emp_valid.
  - exact: si_pure_impl_2.
  - exact: @si_pure_forall_2.
  - exact: persistently_impl_si_pure.
  - exact: si_pure_later.
  - (* Absorbing (<si_pure> Pi) (ADMISSIBLE) *)
    intros Pi. apply True_sep_2.
  - exact: @si_emp_valid_later_1.
  - (* <si_emp_valid> P -∗ <si_emp_valid> <affine> P (ADMISSIBLE) *)
    intros P. apply si_emp_valid_mono, and_intro; [|done].
    apply bi.True_intro.
Qed.
Lemma uPred_sbi_prop_ext_mixin M : SbiPropExtMixin (uPredI M) uPred_si_emp_valid.
Proof. apply sbi_prop_ext_mixin. apply prop_ext_2. Qed.
Global Instance uPred_sbi M : Sbi (uPredI M) :=
  {| sbi_sbi_mixin := uPred_sbi_mixin M;
     sbi_sbi_prop_ext_mixin := uPred_sbi_prop_ext_mixin M |}.

Lemma uPred_bupd_mixin M : BiBUpdMixin (uPredI M) uPred_bupd.
Proof.
  split.
  - exact: bupd_ne.
  - exact: bupd_intro.
  - exact: bupd_mono.
  - exact: bupd_trans.
  - exact: bupd_frame_r.
Qed.
Global Instance uPred_bi_bupd M : BiBUpd (uPredI M) :=
  {| bi_bupd_mixin := uPred_bupd_mixin M |}.

(** extra BI instances *)

Global Instance uPred_affine M : BiAffine (uPredI M) | 0.
Proof. intros P. exact: bi.pure_intro. Qed.
(* Also add this to the global hint database, otherwise [eauto] won't work for
many lemmas that have [BiAffine] as a premise. *)
Global Hint Immediate uPred_affine : core.

Global Instance uPred_persistently_forall M : BiPersistentlyForall (uPredI M).
Proof. exact: @persistently_forall_2. Qed.

Global Instance uPred_pure_forall M : BiPureForall (uPredI M).
Proof.
  intros A φ. etrans; [apply si_pure_forall_2|].
  apply si_pure_mono, pure_forall_2.
Qed.

Global Instance uPred_later_contractive {M} : BiLaterContractive (uPredI M).
Proof. exact: @later_contractive. Qed.

Global Instance uPred_sbi_emp_valid_exist {M} : SbiEmpValidExist (uPredI M).
Proof. exact: @si_emp_valid_exist_1. Qed.

Global Instance uPred_bi_bupd_sbi M : BiBUpdSbi (uPredI M).
Proof. exact: bupd_si_pure. Qed.

(** Re-state/export lemmas about Iris-specific primitive connectives (own, valid) *)

Module uPred.

Section restate.
  Context {M : ucmra}.
  Implicit Types φ : Prop.
  Implicit Types P Q : uPred M.
  Implicit Types A : Type.

  (* Force implicit argument M *)
  Notation "P ⊢ Q" := (bi_entails (PROP:=uPredI M) P%I Q%I).
  Notation "P ⊣⊢ Q" := (equiv (A:=uPredI M) P%I Q%I).

  Global Instance ownM_ne : NonExpansive (@uPred_ownM M) := uPred_primitive.ownM_ne.

  (** Re-exporting primitive lemmas that are not in any interface *)
  Lemma ownM_valid (a : M) : uPred_ownM a ⊢ ✓ a.
  Proof. exact: uPred_primitive.ownM_valid. Qed.
  Lemma ownM_op (a1 a2 : M) :
    uPred_ownM (a1 ⋅ a2) ⊣⊢ uPred_ownM a1 ∗ uPred_ownM a2.
  Proof. exact: uPred_primitive.ownM_op. Qed.
  Lemma persistently_ownM_core (a : M) : uPred_ownM a ⊢ <pers> uPred_ownM (core a).
  Proof. exact: uPred_primitive.persistently_ownM_core. Qed.
  Lemma ownM_unit P : P ⊢ uPred_ownM ε.
  Proof. exact: uPred_primitive.ownM_unit. Qed.
  Lemma later_ownM a : ▷ uPred_ownM a ⊢ ∃ b, uPred_ownM b ∧ ▷ (a ≡ b).
  Proof. exact: uPred_primitive.later_ownM. Qed.
  Lemma bupd_ownM_updateP x (Φ : M → Prop) :
    x ~~>: Φ → uPred_ownM x ⊢ |==> ∃ y, ⌜Φ y⌝ ∧ uPred_ownM y.
  Proof. exact: uPred_primitive.bupd_ownM_updateP. Qed.
  Lemma ownM_forall {A} (f : A → M) :
    (∀ a, uPred_ownM (f a)) ⊢ ∃ z, uPred_ownM z ∧ (∀ a, f a ≼ z).
  Proof. exact: uPred_primitive.ownM_forall. Qed.

  (** We restate the unsealing lemmas for the BI layer. The sealing lemmas
  are partially applied so that they also rewrite under binders. *)
  Local Lemma uPred_emp_unseal :
    bi_emp = @upred.uPred_si_pure_def M (siprop.siProp_pure_def True).
  Proof. by rewrite -upred.uPred_si_pure_unseal -siprop.siProp_pure_unseal. Qed.
  Local Lemma uPred_pure_unseal :
    bi_pure = λ φ, @upred.uPred_si_pure_def M (siprop.siProp_pure_def φ).
  Proof. by rewrite -upred.uPred_si_pure_unseal -siprop.siProp_pure_unseal. Qed.
  Local Lemma uPred_si_pure_unseal : si_pure = @upred.uPred_si_pure_def M.
  Proof. by rewrite -upred.uPred_si_pure_unseal. Qed.
  Local Lemma uPred_si_emp_valid_unseal :
    si_emp_valid = @upred.uPred_si_emp_valid_def M.
  Proof. by rewrite -upred.uPred_si_emp_valid_unseal. Qed.
  Local Lemma uPred_and_unseal : bi_and = @upred.uPred_and_def M.
  Proof. by rewrite -upred.uPred_and_unseal. Qed.
  Local Lemma uPred_or_unseal : bi_or = @upred.uPred_or_def M.
  Proof. by rewrite -upred.uPred_or_unseal. Qed.
  Local Lemma uPred_impl_unseal : bi_impl = @upred.uPred_impl_def M.
  Proof. by rewrite -upred.uPred_impl_unseal. Qed.
  Local Lemma uPred_forall_unseal : @bi_forall _ = @upred.uPred_forall_def M.
  Proof. by rewrite -upred.uPred_forall_unseal. Qed.
  Local Lemma uPred_exist_unseal : @bi_exist _ = @upred.uPred_exist_def M.
  Proof. by rewrite -upred.uPred_exist_unseal. Qed.
  Local Lemma uPred_sep_unseal : bi_sep = @upred.uPred_sep_def M.
  Proof. by rewrite -upred.uPred_sep_unseal. Qed.
  Local Lemma uPred_wand_unseal : bi_wand = @upred.uPred_wand_def M.
  Proof. by rewrite -upred.uPred_wand_unseal. Qed.
  Local Lemma uPred_persistently_unseal :
    bi_persistently = @upred.uPred_persistently_def M.
  Proof. by rewrite -upred.uPred_persistently_unseal. Qed.
  Local Lemma uPred_later_unseal : bi_later = @upred.uPred_later_def M.
  Proof. by rewrite -upred.uPred_later_unseal. Qed.
  Local Lemma uPred_bupd_unseal : bupd = @upred.uPred_bupd_def M.
  Proof. by rewrite -upred.uPred_bupd_unseal. Qed.

  Local Definition uPred_unseal :=
    (uPred_emp_unseal, uPred_pure_unseal,
    uPred_si_pure_unseal, uPred_si_emp_valid_unseal,
    uPred_and_unseal, uPred_or_unseal,
    uPred_impl_unseal, uPred_forall_unseal, uPred_exist_unseal,
    uPred_sep_unseal, uPred_wand_unseal,
    uPred_persistently_unseal, uPred_later_unseal,
    upred.uPred_ownM_unseal, @uPred_bupd_unseal).
End restate.

(** A tactic for rewriting with the above lemmas. Unfolds [uPred] goals that use
the BI layer. This is used by [base_logic.algebra] and [base_logic.bupd_alt]. *)
Ltac unseal := rewrite !uPred_unseal /=.
End uPred.
