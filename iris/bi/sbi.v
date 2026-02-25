From iris.si_logic Require Export bi.
From iris.bi Require Import derived_laws derived_laws_later.
From iris.prelude Require Import options.
Set Default Proof Using "Type*".

(** The Step-indexed BI (SBI) interface describes BIs with a step-indexed
structure. An SBI has an operation [si_pure : siProp → PROP] that embeds an
[siProp] (a pure step-indexed proposition, think of [siProp ≈ nat → Prop]) into
the logic while preserving the step-index, and [si_emp_valid : PROP → siProp]
expresses that a proposition is valid (under assumption [emp]) at a given
step-index. One should think of [si_pure] as a step-indexed version of
[bi_pure] and [si_emp_valid] as a step-indexed version of [bi_emp_valid], in
both cases with [siProp] instead of [Prop].

Note that typically, all [bi] instances with a non-trivial [▷] operator should
have an [Sbi] instance. However, it is possible to omit [Sbi] and just prove
[BiLöb] directly if one does not need the additional results provided by [Sbi].
This may change in the future, and [▷] might be moved to [Sbi].

** Derived definitions/results

For any SBI we obtain the following results:

- "Internal equality" [x ≡ y], which compares [x, y : A] for [A : ofe], by
  internalizing [dist n x y] into the logic. This notion is defined as
  [x ≡ y := <si_pure> siProp_internal_eq P Q], see [iris.bi.internal_eq].
- "Internal validity" [✓ x], which expresses validity of [x : A] for [A : cmra]
  by internalizing [cmra_validN n x] into the logic. This notion is defined as
  [✓ x := <si_pure> siProp_cmra_valid x], see [iris.bi.cmra].
- The "plainly modality" [■ P], which says that a proposition [P] holds without
  depending on any resources (but preserving the step-index). It is different
  from the persistence modality ([<pers>]/[□]), which says that the proposition
  only depends on non-exclusive resources (also preserving the step-index). The
  plainly modality is defined as [■ P := <si_pure> <si_emp_valid> P], see
  [iris.bi.plainly].
- The class of "plain" propositions, which is defined as [Plain P := P ⊢ ■ P],
  see [iris.bi.plainly].
- Generic soundness theorems (which follow from soundness of [siProp]):
  + [pure_soundness : (⊢ ⌜ φ ⌝) → φ]
  + [later_soundness : (⊢ ▷ P) → ⊢ P]
  + [internal_eq_soundness : (⊢ x ≡ y) → x ≡ y]
- Internal characterizations of [NonExpansive] and [Contractive]:
  + [ne_internal_eq : NonExpansive f ↔ ∀ x1 x2, x1 ≡ x2 ⊢ f x1 ≡ f x2]
  + [contractive_internal_eq : Contractive f ↔ ∀ x1 x2, ▷ (x1 ≡ x2) ⊢ f x1 ≡ f x2]
- Later is contractive [sbi_later_contractive], which in turn gives Löb
  induction, i.e., an instance of [BiLöb] (allowing one to use the [iLöb] tactic).

** Prototypical instance

For [uPred M ≈ nat → M → Prop], we define (recall [siProp ≈ nat → Prop]):

  si_pure (φ : siProp) : uPred M := λ n r, φ n
  si_emp_valid (P : uPred M) : siProp := λ n, P n ε

In an affine BI like [uPred] we could have equivalently defined [si_emp_valid]
as [λ n, ∀ x, ✓{n} x → P n x]. However, for a linear version of [uPred] (without
monotonicity condition on [M]), one really needs [ε]. Otherwise the law
[si_emp_valid_affinely_2] does not hold, i.e., [si_emp_valid P] does not say
[P] holds under [<affine>].

** [Sbi] versus [siProp]

End-users should always use the generic SBI definitions, instead of [siProp],
even when using [siProp] itself. In particular, one should always use [≡]/[✓]
instead of [siProp_internal_eq]/[siProp_cmra_valid]. The latter definitions are
used privately to define [≡]/[✓] and are not meant for end-users.

Lemmas about internal equality and validity are stated universally over any
SBI. For example, we have:

  internal_eq_sym `{!Sbi PROP} {A : ofe} (a b : A) :
    a ≡ b ⊢@{PROP} b ≡ a
  prod_includedI `{!Sbi PROP}{A B : cmra} (x y : A * B) :
    x ≼ y ⊣⊢ x.1 ≼ y.1 ∧ x.2 ≼ y.2

instead of versions specialized to [siProp] (using [siProp_internal_eq]).

The reason we state lemmas generically is that one can directly use them in any
SBI without having to distribute [si_pure], making proofs in user-space much
easier.

** Proving SBI lemmas for custom OFEs and CMRAs

To prove lemmas such as [prod_includedI], we typically want to drop down to the
model of [siProp] and lift the corresponding step-indexed lemmas on OFEs/CMRAs.
This is done using the tactic [sbi_unfold], see [iris.bi.sbi_unfold]. Consider
the example [prod_includedI] discussed above, calling [sbi_unfold] gives:

  ∀ n : nat, x ≼{n} y ↔ x.1 ≼{n} y.1 ∧ x.2 ≼{n} y.2

This is exactly the step-indexed lemma [prod_includedN]. See [iris.bi.algebra]
how step-indexed lemmas about OFEs and CMRAs are lifted to SBIs. *)

(* We enable primitive projections in this file to improve the performance of
the Iris proofmode: primitive projections for the bi-records makes the proofmode
faster. *)
Local Set Primitive Projections.

Class SiPure (PROP : Type) : Type := si_pure : siProp → PROP.
Global Instance : Params (@si_pure) 2 := {}.
Global Hint Mode SiPure ! : typeclass_instances.
Global Arguments si_pure {_}%_type_scope {_} _%_bi_scope.
Global Typeclasses Opaque si_pure.
Notation "<si_pure> Pi" := (si_pure Pi) : bi_scope.
Notation "<si_pure>@{ PROP } Pi" := (@si_pure PROP _ Pi) (only parsing) : bi_scope.

Class SiEmpValid (PROP : Type) : Type := si_emp_valid : PROP → siProp.
Global Instance : Params (@si_emp_valid) 2 := {}.
Global Hint Mode SiEmpValid ! : typeclass_instances.
Global Typeclasses Opaque si_emp_valid.
Global Arguments si_emp_valid {_}%_type_scope {_} _%_bi_scope.
Notation "<si_emp_valid> P" := (si_emp_valid P) : bi_scope.

Record SbiMixin (PROP : bi) `(!SiPure PROP, SiEmpValid PROP) := {
  (** [si_pure] and [si_emp_valid] are non-expansive and monotone *)
  sbi_mixin_si_pure_ne : NonExpansive (si_pure (PROP:=PROP));
  sbi_mixin_si_emp_valid_ne : NonExpansive (si_emp_valid (PROP:=PROP));
  sbi_mixin_si_pure_mono Pi Qi :
    (Pi ⊢@{siPropI} Qi) → <si_pure> Pi ⊢@{PROP} <si_pure> Qi;
  sbi_mixin_si_emp_valid_mono P Q :
    (P ⊢@{PROP} Q) → <si_emp_valid> P ⊢@{siPropI} <si_emp_valid> Q;

  (** [si_emp_valid] is a left inverse for [si_pure] *)
  sbi_mixin_si_emp_valid_si_pure Pi :
    <si_emp_valid> <si_pure>@{PROP} Pi ⊣⊢@{siPropI} Pi;
  (** The other way around does not hold, i.e., [<si_pure> <si_emp_valid> P] is
  not equivalent to [P]. This is easy to see in the prototypical model ([uPred]
  above) as the conversion erases the resources. (In other words, plainly
  is not the identity.) The best we get is that if [<si_pure> <si_emp_valid> P]
  (i.e., [P] holds under then empty resource), then [P] holds persistently.
  Note that this is [■ P ⊢ <pers> P] (the usual elimination rule for plainly)
  but that notation is defined as a derived notion on top of this interface. *)
  sbi_mixin_si_pure_si_emp_valid (P : PROP) :
    <si_pure> <si_emp_valid> P ⊢ <pers> P;

  (** [si_pure] commutes with implication, universal quantification, and later.
  The commuting rules for other connectives (and other directions) are derived. *)
  sbi_mixin_si_pure_impl_2 Pi Qi :
    (<si_pure> Pi → <si_pure> Qi) ⊢@{PROP} <si_pure> (Pi → Qi);
  sbi_mixin_si_pure_forall_2 {A} (Φi : A → siProp) :
    (∀ x, <si_pure> Φi x) ⊢@{PROP} <si_pure> (∀ x, Φi x);
  (** This rule generalizes that persistent propositions are closed under
  implication and wand (subject to other conditions), see [impl_persistent] and
  [wand_persistent]. *)
  sbi_mixin_persistently_impl_si_pure Pi (Q : PROP) :
    (<si_pure> Pi → <pers> Q) ⊢ <pers> (<si_pure> Pi → Q);
  sbi_mixin_si_pure_later Pi :
    <si_pure> ▷ Pi ⊣⊢@{PROP} ▷ <si_pure> Pi;

  (** [si_pure] is absorbing (i.e., we have [P ∗ <si_pure> φ ⊢ <si_pure> φ].
  This is similar to [bi_pure] being absorbing. *)
  sbi_mixin_si_pure_absorbing Pi :
    Absorbing (PROP:=PROP) (<si_pure> Pi);

  (** [si_emp_valid] commutes with later. The commuting rules for other
  connectives (and other directions) are derived. *)
  sbi_mixin_si_emp_valid_later_1 (P : PROP) :
    <si_emp_valid> ▷ P ⊢@{siPropI} ▷ <si_emp_valid> P;
  (** The following rule expresses that [si_emp_valid] actually ensures [P]
  holds with the empty resource, i.e., under the affinely modality. *)
  sbi_mixin_si_emp_valid_affinely_2 (P : PROP) :
    <si_emp_valid> P ⊢@{siPropI} <si_emp_valid> <affine> P;
}.

(** There is one more law we would like to include in [Sbi], and that is:

  ∀ P Q : PROP, <si_emp_valid> (P ∗-∗ Q) ⊢@{siPropI} P ≡ Q

However, this law cannot be part of the mixin above since it uses [≡] which is
defined in terms of [Sbi]. So instead we state the law using lower-level
primitives such as [siProp_internal_eq]. However, we want to avoid users having
to see this low-level form, so we make this law a separate mixin that users are
not expected to construct directly, but instead using the [sbi_prop_ext_mixin]
smart constructor (see [iris.bi.internal_eq]). This is separate from [SbiMixin]
since it is easier to have a smart constructor for a single law than for all
laws.

Similarly, when using the [Sbi] class, end-users should not use the field of the
mixin, but rather one of the following lemmas:

  prop_ext_2 : ■ (P ∗-∗ Q) ⊢@{PROP} P ≡ Q
  prop_ext_si_emp_valid_2 : <si_emp_valid> (P ∗-∗ Q) ⊢@{siPropI} P ≡ Q
*)
Record SbiPropExtMixin (PROP : bi) `(!SiEmpValid PROP) := {
  sbi_mixin_prop_ext_si_emp_valid_2 (P Q : PROP) :
    <si_emp_valid> (P ∗-∗ Q) ⊢@{siPropI} siProp_internal_eq P Q;
}.

Class Sbi (PROP : bi) := {
  #[global] sbi_si_pure :: SiPure PROP;
  #[global] sbi_si_emp_valid :: SiEmpValid PROP;
  sbi_sbi_mixin : SbiMixin PROP sbi_si_pure sbi_si_emp_valid;
  sbi_sbi_prop_ext_mixin : SbiPropExtMixin PROP sbi_si_emp_valid;
}.
Global Hint Mode Sbi ! : typeclass_instances.
Global Arguments sbi_si_pure : simpl never.
Global Arguments sbi_si_emp_valid : simpl never.

(** [SbiEmpValidExist] generalizes that plainly [■] commutes with existentials
and disjunction (in both directions), see [plainly_exist] and [plainly_or]. This
law does not hold for every SBI.

For instance, for [monPred I PROP] it only
holds if [I] has a bottom element: Assume that [I] uses equality as its order,
and [PROP:=siProp], then [<si_emp_valid> P] means that [P] holds for any [i].
So on the LHS we can have a different [x] for each [i], while on the RHS we need
one [i] for any [x]. However, if [I] has a bottom element, we can obtain the
witness [x] for the bottom element on the LHS, and use monotonicy to conclude it
holds for any [i] on the RHS. See also [monPred_sbi_emp_valid_exist]. *)
Class SbiEmpValidExist PROP `{!Sbi PROP} :=
  si_emp_valid_exist_1 : ∀ {A} (Φ : A → PROP),
    <si_emp_valid> (∃ x, Φ x) ⊢@{siPropI} ∃ x, <si_emp_valid> Φ x.
Global Arguments SbiEmpValidExist _ {_}.
Global Arguments si_emp_valid_exist_1 _ {_ _} _.
Global Hint Mode SbiEmpValidExist ! - : typeclass_instances.

(** [siProp] is an SBI by taking [<si_pure>] and [<si_emp_valid>] to be the
identity. Although this instance is trivial, it is a very useful one. It means
that all lemmas and instances about internal equality [≡] and internal validity
[✓] also apply to [siProp] (and we do not need to state specialized versions). *)
Lemma siprop_sbi_mixin : SbiMixin siProp id id.
Proof.
  split; rewrite /si_pure /si_emp_valid; try (done || apply _).
  intros P. by rewrite bi.affine_affinely.
Qed.
Lemma siprop_sbi_prop_ext_mixin : SbiPropExtMixin siProp id.
Proof. split; intros P Q. apply siProp_primitive.prop_ext_2. Qed.

Global Instance siprop_sbi : Sbi siPropI :=
  {| sbi_sbi_mixin := siprop_sbi_mixin;
     sbi_sbi_prop_ext_mixin := siprop_sbi_prop_ext_mixin |}.
Global Instance siprop_sbi_emp_valid_exist : SbiEmpValidExist siPropI.
Proof. done. Qed.

(** ** The primitive laws *)
Section sbi_laws.
  Context `{!Sbi PROP}.
  Implicit Types Pi Qi Ri : siProp.
  Implicit Types P Q R : PROP.

  Global Instance si_pure_ne : NonExpansive (si_pure (PROP:=PROP)).
  Proof. eapply sbi_mixin_si_pure_ne, sbi_sbi_mixin. Qed.
  Global Instance si_emp_valid_ne : NonExpansive (si_emp_valid (PROP:=PROP)).
  Proof. eapply sbi_mixin_si_emp_valid_ne, sbi_sbi_mixin. Qed.
  Lemma si_pure_mono Pi Qi :
    (Pi ⊢@{siPropI} Qi) → <si_pure> Pi ⊢@{PROP} <si_pure> Qi.
  Proof. eapply sbi_mixin_si_pure_mono, sbi_sbi_mixin. Qed.
  Lemma si_emp_valid_mono P Q :
    (P ⊢@{PROP} Q) → <si_emp_valid> P ⊢@{siPropI} <si_emp_valid> Q.
  Proof. eapply sbi_mixin_si_emp_valid_mono, sbi_sbi_mixin. Qed.

  Lemma si_emp_valid_si_pure Pi :
    <si_emp_valid> <si_pure>@{PROP} Pi ⊣⊢@{siPropI} Pi.
  Proof. eapply sbi_mixin_si_emp_valid_si_pure, sbi_sbi_mixin. Qed.
  Lemma si_pure_si_emp_valid (P : PROP) :
    <si_pure> <si_emp_valid> P ⊢ <pers> P.
  Proof. eapply sbi_mixin_si_pure_si_emp_valid, sbi_sbi_mixin. Qed.

  Lemma si_pure_impl_2 Pi Qi :
    (<si_pure> Pi → <si_pure> Qi) ⊢@{PROP} <si_pure> (Pi → Qi).
  Proof. eapply sbi_mixin_si_pure_impl_2, sbi_sbi_mixin. Qed.
  Lemma si_pure_forall_2 {A} (Φi : A → siProp) :
   (∀ x, <si_pure> Φi x) ⊢@{PROP} <si_pure> (∀ x, Φi x).
  Proof. eapply sbi_mixin_si_pure_forall_2, sbi_sbi_mixin. Qed.
  Lemma persistently_impl_si_pure Pi (Q : PROP) :
    (<si_pure> Pi → <pers> Q) ⊢ <pers> (<si_pure> Pi → Q).
  Proof. eapply sbi_mixin_persistently_impl_si_pure, sbi_sbi_mixin. Qed.
  Lemma si_pure_later Pi :
    <si_pure> ▷ Pi ⊣⊢@{PROP} ▷ <si_pure> Pi.
  Proof. eapply sbi_mixin_si_pure_later, sbi_sbi_mixin. Qed.
  Global Instance si_pure_absorbing Pi :
    Absorbing (PROP:=PROP) (<si_pure> Pi).
  Proof. eapply sbi_mixin_si_pure_absorbing, sbi_sbi_mixin. Qed.

  Lemma si_emp_valid_affinely_2 (P : PROP) :
    <si_emp_valid> P ⊢@{siPropI} <si_emp_valid> <affine> P.
  Proof. eapply sbi_mixin_si_emp_valid_affinely_2, sbi_sbi_mixin. Qed.
  Lemma si_emp_valid_later_1 (P : PROP) :
    <si_emp_valid> ▷ P ⊢@{siPropI} ▷ <si_emp_valid> P.
  Proof. eapply sbi_mixin_si_emp_valid_later_1, sbi_sbi_mixin. Qed.
End sbi_laws.

(** ** The derived laws *)
Section sbi_derived.
  Context `{!Sbi PROP}.
  Implicit Types Pi Qi Ri : siProp.
  Implicit Types P Q R : PROP.

  Global Instance si_pure_proper : Proper ((⊣⊢) ==> (⊣⊢)) (si_pure (PROP:=PROP)).
  Proof. apply (ne_proper _). Qed.
  Global Instance si_emp_valid_proper :
    Proper ((⊣⊢) ==> (⊣⊢)) (si_emp_valid (PROP:=PROP)).
  Proof. apply (ne_proper _). Qed.

  Global Instance si_pure_mono' : Proper ((⊢) ==> (⊢)) (si_pure (PROP:=PROP)).
  Proof. intros Pi Qi. apply si_pure_mono. Qed.
  Global Instance si_pure_flip_mono' :
    Proper (flip (⊢) ==> flip (⊢)) (si_pure (PROP:=PROP)).
  Proof. solve_proper. Qed.
  Global Instance si_emp_valid_mono' :
    Proper ((⊢) ==> (⊢)) (si_emp_valid (PROP:=PROP)).
  Proof. intros P Q. apply si_emp_valid_mono. Qed.
  Global Instance si_emp_valid_flip_mono' :
    Proper (flip (⊢) ==> flip (⊢)) (si_emp_valid (PROP:=PROP)).
  Proof. solve_proper. Qed.

  Global Instance si_pure_persistent Pi : Persistent (PROP:=PROP) (<si_pure> Pi).
  Proof.
    rewrite /Persistent.
    by rewrite -{1}(si_emp_valid_si_pure (PROP:=PROP) Pi) si_pure_si_emp_valid.
  Qed.

  (** Commuting rules of [<si_pure>] *)
  Lemma si_pure_forall {A} (Φi : A → siProp) :
    <si_pure> (∀ x, Φi x) ⊣⊢@{PROP} ∀ x, <si_pure> Φi x.
  Proof.
    apply (anti_symm _); [|apply si_pure_forall_2].
    apply bi.forall_intro=> x. by rewrite (bi.forall_elim x).
  Qed.
  Lemma si_pure_exist {A} (Φi : A → siProp) :
    <si_pure> (∃ x, Φi x) ⊣⊢@{PROP} ∃ x, <si_pure> Φi x.
  Proof.
    apply (anti_symm _).
    - rewrite -(bi.persistent_persistently (∃ x, <si_pure> _)).
      rewrite -si_pure_si_emp_valid. f_equiv. apply bi.exist_elim=> x.
      by rewrite -(bi.exist_intro x) si_emp_valid_si_pure.
    - apply bi.exist_elim=> x. by rewrite -(bi.exist_intro x).
  Qed.
  Lemma si_pure_and Pi Qi :
    <si_pure> (Pi ∧ Qi) ⊣⊢@{PROP} <si_pure> Pi ∧ <si_pure> Qi.
  Proof. rewrite !bi.and_alt si_pure_forall. by f_equiv=> -[]. Qed.
  Lemma si_pure_and_sep Pi Qi :
    <si_pure> (Pi ∧ Qi) ⊣⊢@{PROP} <si_pure> Pi ∗ <si_pure> Qi.
  Proof.
    rewrite si_pure_and.
    apply (anti_symm _); [apply (bi.persistent_and_sep_1 _ _)|].
    apply bi.and_intro; [apply (bi.sep_elim_l _ _)|apply (bi.sep_elim_r _ _)].
  Qed.
  Lemma si_pure_or Pi Qi :
    <si_pure> (Pi ∨ Qi) ⊣⊢@{PROP} <si_pure> Pi ∨ <si_pure> Qi.
  Proof. rewrite !bi.or_alt si_pure_exist. by f_equiv=> -[]. Qed.
  Lemma si_pure_pure φ : <si_pure> ⌜ φ ⌝ ⊣⊢@{PROP} ⌜ φ ⌝.
  Proof.
    rewrite bi.pure_alt si_pure_exist (bi.pure_alt φ). f_equiv=> _.
    apply (anti_symm _); [apply bi.True_intro|].
    trans (∀ _ : Empty_set, <si_pure>@{PROP} True)%I; [by apply bi.forall_intro|].
    rewrite -si_pure_forall. f_equiv. apply bi.True_intro.
  Qed.
  Lemma si_pure_impl Pi Qi :
    <si_pure> (Pi → Qi) ⊣⊢@{PROP} (<si_pure> Pi → <si_pure> Qi).
  Proof.
    apply (anti_symm _); [|apply si_pure_impl_2].
    apply bi.impl_intro_l. by rewrite -si_pure_and bi.impl_elim_r.
  Qed.
  Lemma si_pure_impl_wand Pi Qi :
    <si_pure> (Pi → Qi) ⊣⊢@{PROP} (<si_pure> Pi -∗ <si_pure> Qi).
  Proof.
    apply (anti_symm _).
    - apply bi.wand_intro_l. by rewrite -si_pure_and_sep bi.impl_elim_r.
    - rewrite si_pure_impl. apply bi.impl_intro_l.
      by rewrite bi.persistent_and_affinely_sep_l bi.affinely_elim bi.wand_elim_r.
  Qed.
  Lemma si_pure_iff Pi Qi :
    <si_pure> (Pi ↔ Qi) ⊣⊢@{PROP} (<si_pure> Pi ↔ <si_pure> Qi).
  Proof. by rewrite /bi_iff si_pure_and -!si_pure_impl. Qed.
  Lemma si_pure_impl_iff_wand Pi Qi :
    <si_pure> (Pi ↔ Qi) ⊣⊢@{PROP} (<si_pure> Pi ∗-∗ <si_pure> Qi).
  Proof. by rewrite /bi_wand_iff si_pure_and -!si_pure_impl_wand. Qed.
  Lemma si_pure_laterN n Pi :
    <si_pure> ▷^n Pi ⊣⊢@{PROP} ▷^n <si_pure> Pi.
  Proof.
    induction n as [|n IH]; simpl; [done|].
    by rewrite si_pure_later IH.
  Qed.
  Lemma si_pure_except_0 Pi : <si_pure> ◇ Pi ⊣⊢@{PROP} ◇ <si_pure> Pi.
  Proof. by rewrite /bi_except_0 si_pure_or si_pure_later si_pure_pure. Qed.
  Lemma absorbingly_si_pure Pi : <absorb> <si_pure> Pi ⊣⊢@{PROP} <si_pure> Pi.
  Proof. by rewrite bi.absorbing_absorbingly. Qed.
  Lemma persistently_si_pure Pi : <pers> <si_pure> Pi ⊣⊢@{PROP} <si_pure> Pi.
  Proof. by rewrite bi.persistent_persistently. Qed.

  Global Instance si_pure_timeless Pi :
    Timeless Pi → Timeless (PROP:=PROP) (<si_pure> Pi).
  Proof.
    rewrite /Timeless=> HP. by rewrite -si_pure_later -si_pure_except_0 HP.
  Qed.

  (** Version of primitive [si_pure_si_emp_valid] for [Absorbing P] and with
  [<affine>] added. *)
  Lemma si_pure_si_emp_valid_elim P `{!Absorbing P} :
    <si_pure> <si_emp_valid> P ⊢ P.
  Proof. rewrite si_pure_si_emp_valid. by apply bi.persistently_elim. Qed.
  Lemma affinely_si_pure_si_emp_valid P :
    <affine> <si_pure> <si_emp_valid> P ⊢ P.
  Proof. rewrite si_pure_si_emp_valid. apply bi.intuitionistically_elim. Qed.

  (** Commuting rules of [<si_emp_valid>] *)
  Lemma si_emp_valid_affinely P :
    <si_emp_valid> <affine> P ⊣⊢@{siPropI} <si_emp_valid> P.
  Proof.
    apply (anti_symm _);
      [by rewrite bi.affinely_elim|apply si_emp_valid_affinely_2].
  Qed.
  Lemma si_emp_valid_persistently P :
    <si_emp_valid> <pers> P ⊣⊢@{siPropI} <si_emp_valid> P.
  Proof.
    apply (anti_symm _).
    - by rewrite -si_emp_valid_affinely -{2}(bi.intuitionistically_elim P).
    - rewrite -(si_emp_valid_si_pure (PROP:=PROP) (si_emp_valid P)).
      by rewrite si_pure_si_emp_valid. 
  Qed.
  Lemma si_emp_valid_intuitionistically P :
    <si_emp_valid> □ P ⊣⊢@{siPropI} <si_emp_valid> P.
  Proof.
    by rewrite /bi_intuitionistically si_emp_valid_affinely si_emp_valid_persistently.
  Qed.

  Lemma si_emp_valid_pure φ : <si_emp_valid> (⌜ φ ⌝ : PROP) ⊣⊢@{siPropI} ⌜ φ ⌝.
  Proof.
    by rewrite -(si_emp_valid_si_pure (PROP:=PROP) ⌜ φ ⌝) si_pure_pure.
  Qed.
  Lemma si_emp_valid_emp : <si_emp_valid> (emp : PROP) ⊣⊢@{siPropI} True.
  Proof.
    rewrite -bi.affinely_emp -bi.affinely_True_emp.
    by rewrite !si_emp_valid_affinely si_emp_valid_pure.
  Qed.

  Lemma si_emp_valid_forall {A} (Φ : A → PROP) :
    <si_emp_valid> (∀ x, Φ x) ⊣⊢@{siPropI} ∀ x, <si_emp_valid> (Φ x).
  Proof.
    apply (anti_symm _).
    - apply bi.forall_intro=> x. by rewrite (bi.forall_elim x).
    - rewrite -(si_emp_valid_si_pure (PROP:=PROP) (∀ x : A, _)).
      rewrite si_pure_forall -si_emp_valid_affinely bi.affinely_forall.
      by setoid_rewrite affinely_si_pure_si_emp_valid.
  Qed.
  Lemma si_emp_valid_exist_2 {A} (Φ : A → PROP) :
    (∃ x, <si_emp_valid> Φ x) ⊢@{siPropI} <si_emp_valid> (∃ x, Φ x).
  Proof. apply bi.exist_elim=> x. by rewrite -(bi.exist_intro x). Qed.
  Lemma si_emp_valid_exist `{!SbiEmpValidExist PROP} {A} (Φ : A → PROP) :
    <si_emp_valid> (∃ x, Φ x) ⊣⊢@{siPropI} ∃ x, <si_emp_valid> Φ x.
  Proof.
    apply (anti_symm _); [apply: si_emp_valid_exist_1|apply si_emp_valid_exist_2].
  Qed.

  Lemma si_emp_valid_and P Q :
    <si_emp_valid> (P ∧ Q) ⊣⊢@{siPropI} <si_emp_valid> P ∧ <si_emp_valid> Q.
  Proof. rewrite !bi.and_alt si_emp_valid_forall. by f_equiv=> -[]. Qed.
  Lemma si_emp_valid_or_2 P Q :
    <si_emp_valid> P ∨ <si_emp_valid> Q ⊢@{siPropI} <si_emp_valid> (P ∨ Q).
  Proof. rewrite !bi.or_alt -si_emp_valid_exist_2. by f_equiv=> -[]. Qed.
  Lemma si_emp_valid_or `{!SbiEmpValidExist PROP} P Q :
    <si_emp_valid> (P ∨ Q) ⊣⊢@{siPropI} <si_emp_valid> P ∨ <si_emp_valid> Q.
  Proof. rewrite !bi.or_alt si_emp_valid_exist. by f_equiv=> -[]. Qed.

  Lemma si_emp_valid_impl_si_pure Pi Q :
    (Pi → <si_emp_valid> Q) ⊢@{siPropI} <si_emp_valid> (<si_pure> Pi → Q).
  Proof.
    rewrite -(si_emp_valid_si_pure (PROP:=PROP) (_ → _)) -si_emp_valid_affinely.
    f_equiv. apply bi.impl_intro_l. rewrite bi.affinely_and_r.
    by rewrite -si_pure_and bi.impl_elim_r affinely_si_pure_si_emp_valid.
  Qed.

  Lemma si_emp_valid_sep `{!BiPositive PROP} P Q :
    <si_emp_valid> (P ∗ Q) ⊣⊢@{siPropI} <si_emp_valid> P ∧ <si_emp_valid> Q.
  Proof.
    rewrite -si_emp_valid_intuitionistically bi.intuitionistically_sep.
    rewrite -bi.and_sep_intuitionistically si_emp_valid_and.
    by rewrite !si_emp_valid_intuitionistically.
  Qed.
  Lemma si_emp_valid_wand_si_pure Pi Q :
    (Pi → <si_emp_valid> Q) ⊢@{siPropI} <si_emp_valid> (<affine> <si_pure> Pi -∗ Q).
  Proof.
    by rewrite -bi.persistent_impl_wand_affinely -si_emp_valid_impl_si_pure.
  Qed.

  Lemma si_emp_valid_later P :
    <si_emp_valid> ▷ P ⊣⊢@{siPropI} ▷ <si_emp_valid> P.
  Proof.
    apply (anti_symm _); [apply si_emp_valid_later_1|].
    rewrite -(si_emp_valid_si_pure (PROP:=PROP) (▷ _)). rewrite si_pure_later.
    rewrite si_pure_si_emp_valid.
    by rewrite bi.later_persistently si_emp_valid_persistently.
  Qed.
  Lemma si_emp_valid_laterN n P :
    <si_emp_valid> ▷^n P ⊣⊢@{siPropI} ▷^n <si_emp_valid> P.
  Proof.
    induction n as [|n IH]; simpl; [done|].
    by rewrite si_emp_valid_later IH.
  Qed.

  Lemma si_emp_valid_except_0 P :
    <si_emp_valid> ◇ P ⊣⊢@{siPropI} ◇ <si_emp_valid> P.
  Proof.
    apply (anti_symm _).
    - trans (▷ <si_emp_valid> P ∧ <si_emp_valid> ◇ P)%I.
      { apply bi.and_intro, reflexivity.
        by rewrite -si_emp_valid_later bi.except_0_into_later. }
      rewrite bi.later_false_em bi.and_or_r. apply bi.or_elim.
      { rewrite bi.and_elim_l. apply bi.or_intro_l. }
      apply bi.or_intro_r'. rewrite si_emp_valid_impl_si_pure -si_emp_valid_and.
      f_equiv. rewrite si_pure_later si_pure_pure.
      by rewrite bi.and_or_l bi.impl_elim_l bi.and_elim_r idemp.
    - rewrite /bi_except_0 -si_emp_valid_or_2.
      by rewrite si_emp_valid_later si_emp_valid_pure.
  Qed.

  Global Instance si_emp_valid_timeless P :
    Timeless P → Timeless (<si_emp_valid> P).
  Proof.
    rewrite /Timeless=> HP.
    by rewrite -si_emp_valid_later -si_emp_valid_except_0 HP.
  Qed.

  (** Relating [⊢] in [siProp] to [⊢] in [PROP] *)
  Lemma si_emp_valid_emp_valid P : (⊢@{siPropI} <si_emp_valid> P) ↔ ⊢ P.
  Proof.
    rewrite /bi_emp_valid. split; intros HP.
    - rewrite -bi.affinely_True_emp -si_pure_pure.
      by rewrite bi.True_emp HP affinely_si_pure_si_emp_valid.
    - by rewrite -bi.True_emp -si_emp_valid_emp HP.
  Qed.
  Lemma si_pure_emp_valid Pi : (⊢@{PROP} <si_pure> Pi) ↔ ⊢@{siPropI} Pi.
  Proof. by rewrite -si_emp_valid_emp_valid si_emp_valid_si_pure. Qed.
  Lemma si_pure_entails Pi Qi :
    (<si_pure> Pi ⊢@{PROP} <si_pure> Qi) ↔ (Pi ⊢@{siPropI} Qi).
  Proof.
    split; [|by intros ->].
    intros HPQ. rewrite -(si_emp_valid_si_pure (PROP:=PROP) Pi) HPQ.
    by rewrite si_emp_valid_si_pure.
  Qed.
  Global Instance si_pure_inj : Inj (⊣⊢) (⊣⊢) (si_pure (PROP:=PROP)).
  Proof.
    intros Pi Qi HPQ.
    apply (anti_symm _); apply si_pure_entails; by rewrite HPQ.
  Qed.

  (** Soundness lemmas *)
  (** The version for internal equality [internal_eq_soundness] can be found in
  [iris.bi.internal_eq]. *)
  Lemma pure_soundness φ : (⊢@{PROP} ⌜ φ ⌝) → φ.
  Proof.
    rewrite -si_pure_pure si_pure_emp_valid.
    apply siProp_primitive.pure_soundness.
  Qed.

  Lemma later_soundness P : (⊢ ▷ P) → ⊢ P.
  Proof.
    rewrite -!si_emp_valid_emp_valid si_emp_valid_later.
    apply siProp_primitive.later_soundness.
  Qed.

  Lemma laterN_soundness P n : (⊢ ▷^n P) → ⊢ P.
  Proof.
    induction n as [|n IH]; intros ?; simpl; [done|].
    by apply IH, later_soundness.
  Qed.
End sbi_derived.
