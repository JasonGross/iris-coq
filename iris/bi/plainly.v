From iris.algebra Require Import monoid.
From iris.bi Require Export internal_eq.
From iris.bi Require Import derived_laws_later big_op.
From iris.prelude Require Import options.
Import interface.bi derived_laws.bi derived_laws_later.bi.

(* The sections add [BiAffine] and the like, which is only picked up with "Type"*. *)
Set Default Proof Using "Type*".

Definition plainly `{!Sbi PROP} (P : PROP) : PROP :=
  <si_pure> <si_emp_valid> P.
Global Arguments plainly : simpl never.
Global Instance: Params (@plainly) 2 := {}.
Global Typeclasses Opaque plainly.

Notation "■ P" := (plainly P) : bi_scope.

Class Plain `{!Sbi PROP} (P : PROP) := plain : P ⊢ ■ P.
Global Arguments Plain {_ _} _%_I : simpl never.
Global Arguments plain {_ _} _%_I {_}.
Global Hint Mode Plain + - ! : typeclass_instances.
Global Instance: Params (@Plain) 1 := {}.

Global Hint Extern 100 (Plain (match ?x with _ => _ end)) =>
  destruct x : typeclass_instances.

Global Instance siProp_plain (P : siProp) : Plain P | 0.
Proof. done. Qed.

Definition plainly_if `{!Sbi PROP} (p : bool) (P : PROP) : PROP :=
  (if p then ■ P else P)%I.
Global Arguments plainly_if {_ _} !_ _%_I /.
Global Instance: Params (@plainly_if) 2 := {}.
Global Typeclasses Opaque plainly_if.

Notation "■? p P" := (plainly_if p P) : bi_scope.

Section plainly.
  Context `{!Sbi PROP}.
  Implicit Types P Q : PROP.

  Local Hint Resolve pure_intro forall_intro : core.
  Local Hint Resolve or_elim or_intro_l' or_intro_r' : core.
  Local Hint Resolve and_intro and_elim_l' and_elim_r' : core.

  Global Instance plainly_ne : NonExpansive (plainly (PROP:=PROP)).
  Proof. solve_proper. Qed.
  Global Instance plainly_proper : Proper ((⊣⊢) ==> (⊣⊢)) (@plainly PROP _).
  Proof. apply ne_proper, _. Qed.

  Lemma plainly_mono P Q : (P ⊢ Q) → ■ P ⊢ ■ Q.
  Proof. intros. by apply si_pure_mono, si_emp_valid_mono. Qed.
  Global Instance plainly_mono' : Proper ((⊢) ==> (⊢)) (@plainly PROP _).
  Proof. intros P Q; apply plainly_mono. Qed.
  Global Instance plainly_flip_mono' :
    Proper (flip (⊢) ==> flip (⊢)) (@plainly PROP _).
  Proof. intros P Q; apply plainly_mono. Qed.

  Lemma plainly_elim_persistently P : ■ P ⊢ <pers> P.
  Proof. apply si_pure_si_emp_valid. Qed.
  Lemma plainly_idemp_2 P : ■ P ⊢ ■ ■ P.
  Proof. by rewrite /plainly si_emp_valid_si_pure. Qed.
  Lemma plainly_forall_2 {A} (Ψ : A → PROP) : (∀ a, ■ (Ψ a)) ⊢ ■ (∀ a, Ψ a).
  Proof. by rewrite /plainly si_emp_valid_forall si_pure_forall. Qed.
  Lemma plainly_exist_1 `{!SbiEmpValidExist PROP} {A} (Ψ : A → PROP) :
    ■ (∃ a, Ψ a) ⊢ ∃ a, ■ (Ψ a).
  Proof. by rewrite /plainly si_emp_valid_exist si_pure_exist. Qed.
  Lemma plainly_impl_plainly P Q : (■ P → ■ Q) ⊢ ■ (■ P → Q).
  Proof. by rewrite /plainly si_pure_impl_2 -si_emp_valid_impl_si_pure. Qed.
  Lemma plainly_emp_intro P : P ⊢ ■ emp.
  Proof. rewrite /plainly si_emp_valid_emp si_pure_pure. apply True_intro. Qed.
  Lemma plainly_absorb P Q : ■ P ∗ Q ⊢ ■ P.
  Proof. by rewrite /plainly sep_elim_l. Qed.
  Lemma later_plainly P : ▷ ■ P ⊣⊢ ■ ▷ P.
  Proof. by rewrite /plainly -si_pure_later -si_emp_valid_later. Qed.
  Lemma later_plainly_1 P : ▷ ■ P ⊢ ■ (▷ P).
  Proof. by rewrite later_plainly. Qed.
  Lemma later_plainly_2 P : ■ ▷ P ⊢ ▷ ■ P.
  Proof. by rewrite later_plainly. Qed.

  Lemma affinely_plainly_elim P : <affine> ■ P ⊢ P.
  Proof.
    by rewrite plainly_elim_persistently /bi_affinely persistently_and_emp_elim.
  Qed.

  Lemma persistently_elim_plainly P : <pers> ■ P ⊣⊢ ■ P.
  Proof.
    apply (anti_symm _).
    - by rewrite persistently_into_absorbingly /bi_absorbingly comm plainly_absorb.
    - by rewrite {1}plainly_idemp_2 plainly_elim_persistently.
  Qed.
  Lemma persistently_if_elim_plainly P p : <pers>?p ■ P ⊣⊢ ■ P.
  Proof. destruct p; last done. exact: persistently_elim_plainly. Qed.

  Lemma plainly_persistently_elim P : ■ <pers> P ⊣⊢ ■ P.
  Proof.
    apply (anti_symm _).
    - rewrite -{1}(left_id True%I bi_and (■ _)%I) (plainly_emp_intro True).
      rewrite -{2}(persistently_and_emp_elim P).
      rewrite !and_alt -plainly_forall_2. by apply forall_mono=> -[].
    - by rewrite {1}plainly_idemp_2 (plainly_elim_persistently P).
  Qed.

  Lemma absorbingly_elim_plainly P : <absorb> ■ P ⊣⊢ ■ P.
  Proof.
    by rewrite -(persistently_elim_plainly P) absorbingly_elim_persistently.
  Qed.

  Lemma plainly_and_sep_elim P Q : ■ P ∧ Q ⊢ (emp ∧ P) ∗ Q.
  Proof. by rewrite plainly_elim_persistently persistently_and_sep_elim_emp. Qed.
  Lemma plainly_and_sep_assoc P Q R : ■ P ∧ (Q ∗ R) ⊣⊢ (■ P ∧ Q) ∗ R.
  Proof. by rewrite -(persistently_elim_plainly P) persistently_and_sep_assoc. Qed.
  Lemma plainly_and_emp_elim P : emp ∧ ■ P ⊢ P.
  Proof. by rewrite plainly_elim_persistently persistently_and_emp_elim. Qed.
  Lemma plainly_into_absorbingly P : ■ P ⊢ <absorb> P.
  Proof. by rewrite plainly_elim_persistently persistently_into_absorbingly. Qed.
  Lemma plainly_elim P `{!Absorbing P} : ■ P ⊢ P.
  Proof. by rewrite plainly_elim_persistently persistently_elim. Qed.

  Lemma plainly_idemp_1 P : ■ ■ P ⊢ ■ P.
  Proof. by rewrite plainly_into_absorbingly absorbingly_elim_plainly. Qed.
  Lemma plainly_idemp P : ■ ■ P ⊣⊢ ■ P.
  Proof. apply (anti_symm _); auto using plainly_idemp_1, plainly_idemp_2. Qed.

  Lemma plainly_intro' P Q : (■ P ⊢ Q) → ■ P ⊢ ■ Q.
  Proof. intros <-. apply plainly_idemp_2. Qed.

  Lemma plainly_pure φ : ■ ⌜φ⌝ ⊣⊢@{PROP} ⌜φ⌝.
  Proof. by rewrite /plainly si_emp_valid_pure si_pure_pure. Qed.
  Lemma plainly_si_pure Pi : ■ <si_pure> Pi ⊣⊢@{PROP} <si_pure> Pi.
  Proof. by rewrite /plainly si_emp_valid_si_pure. Qed.
  Lemma plainly_forall {A} (Ψ : A → PROP) : ■ (∀ a, Ψ a) ⊣⊢ ∀ a, ■ (Ψ a).
  Proof. by rewrite /plainly si_emp_valid_forall si_pure_forall. Qed.
  Lemma plainly_exist_2 {A} (Ψ : A → PROP) : (∃ a, ■ (Ψ a)) ⊢ ■ (∃ a, Ψ a).
  Proof. apply exist_elim=> x. by rewrite (exist_intro x). Qed.
  Lemma plainly_exist `{!SbiEmpValidExist PROP} {A} (Ψ : A → PROP) :
    ■ (∃ a, Ψ a) ⊣⊢ ∃ a, ■ (Ψ a).
  Proof. apply (anti_symm _); auto using plainly_exist_1, plainly_exist_2. Qed.
  Lemma plainly_and P Q : ■ (P ∧ Q) ⊣⊢ ■ P ∧ ■ Q.
  Proof. rewrite !and_alt plainly_forall. by apply forall_proper=> -[]. Qed.
  Lemma plainly_or_2 P Q : ■ P ∨ ■ Q ⊢ ■ (P ∨ Q).
  Proof. rewrite !or_alt -plainly_exist_2. by apply exist_mono=> -[]. Qed.
  Lemma plainly_or `{!SbiEmpValidExist PROP} P Q : ■ (P ∨ Q) ⊣⊢ ■ P ∨ ■ Q.
  Proof. rewrite !or_alt plainly_exist. by apply exist_proper=> -[]. Qed.
  Lemma plainly_impl P Q : ■ (P → Q) ⊢ ■ P → ■ Q.
  Proof.
    apply impl_intro_l; rewrite -plainly_and.
    apply plainly_mono, impl_elim with P; auto.
  Qed.

  Lemma plainly_emp_2 : emp ⊢@{PROP} ■ emp.
  Proof. apply plainly_emp_intro. Qed.

  Lemma plainly_sep_dup P : ■ P ⊣⊢ ■ P ∗ ■ P.
  Proof.
    apply (anti_symm _).
    - rewrite -{1}(idemp bi_and (■ _)%I).
      by rewrite -{2}(emp_sep (■ _)%I) plainly_and_sep_assoc and_elim_l.
    - by rewrite plainly_absorb.
  Qed.

  Lemma plainly_and_sep_l_1 P Q : ■ P ∧ Q ⊢ ■ P ∗ Q.
  Proof. by rewrite -{1}(emp_sep Q) plainly_and_sep_assoc and_elim_l. Qed.
  Lemma plainly_and_sep_r_1 P Q : P ∧ ■ Q ⊢ P ∗ ■ Q.
  Proof. by rewrite !(comm _ P) plainly_and_sep_l_1. Qed.

  Lemma plainly_True_emp : ■ True ⊣⊢@{PROP} ■ emp.
  Proof. apply (anti_symm _); eauto using plainly_mono, plainly_emp_intro. Qed.
  Lemma plainly_and_sep P Q : ■ (P ∧ Q) ⊢ ■ (P ∗ Q).
  Proof.
    rewrite plainly_and.
    rewrite -{1}plainly_idemp -plainly_and -{1}(emp_sep Q).
    by rewrite plainly_and_sep_assoc (comm bi_and) plainly_and_emp_elim.
  Qed.

  Lemma plainly_affinely_elim P : ■ <affine> P ⊣⊢ ■ P.
  Proof.
   by rewrite /bi_affinely plainly_and -plainly_True_emp plainly_pure left_id.
  Qed.

  Lemma intuitionistically_plainly_elim P : □ ■ P ⊢ □ P.
  Proof. rewrite intuitionistically_affinely plainly_elim_persistently //. Qed.
  Lemma intuitionistically_plainly P : □ ■ P ⊢ ■ □ P.
  Proof.
    rewrite /bi_intuitionistically plainly_affinely_elim affinely_elim.
    rewrite persistently_elim_plainly plainly_persistently_elim. done.
  Qed.

  Lemma and_sep_plainly P Q : ■ P ∧ ■ Q ⊣⊢ ■ P ∗ ■ Q.
  Proof.
    apply (anti_symm _); auto using plainly_and_sep_l_1.
    apply and_intro.
    - by rewrite plainly_absorb.
    - by rewrite comm plainly_absorb.
  Qed.
  Lemma plainly_sep_2 P Q : ■ P ∗ ■ Q ⊢ ■ (P ∗ Q).
  Proof. by rewrite -plainly_and_sep plainly_and -and_sep_plainly. Qed.
  Lemma plainly_sep `{!BiPositive PROP} P Q : ■ (P ∗ Q) ⊣⊢ ■ P ∗ ■ Q.
  Proof.
    apply (anti_symm _); auto using plainly_sep_2.
    rewrite -(plainly_affinely_elim (_ ∗ _)).
    rewrite affinely_sep -and_sep_plainly. apply and_intro.
    - by rewrite (affinely_elim_emp Q) right_id affinely_elim.
    - by rewrite (affinely_elim_emp P) left_id affinely_elim.
  Qed.

  Lemma plainly_wand P Q : ■ (P -∗ Q) ⊢ ■ P -∗ ■ Q.
  Proof. apply wand_intro_r. by rewrite plainly_sep_2 wand_elim_l. Qed.

  Lemma plainly_entails_l P Q : (P ⊢ ■ Q) → P ⊢ ■ Q ∗ P.
  Proof. intros; rewrite -plainly_and_sep_l_1; auto. Qed.
  Lemma plainly_entails_r P Q : (P ⊢ ■ Q) → P ⊢ P ∗ ■ Q.
  Proof. intros; rewrite -plainly_and_sep_r_1; auto. Qed.

  Lemma plainly_impl_wand_2 P Q : ■ (P -∗ Q) ⊢ ■ (P → Q).
  Proof.
    apply plainly_intro', impl_intro_r.
    rewrite -{2}(emp_sep P) plainly_and_sep_assoc.
    by rewrite (comm bi_and) plainly_and_emp_elim wand_elim_l.
  Qed.

  Lemma impl_wand_plainly_2 P Q : (■ P -∗ Q) ⊢ (■ P → Q).
  Proof. apply impl_intro_l. by rewrite plainly_and_sep_l_1 wand_elim_r. Qed.

  Lemma impl_wand_affinely_plainly P Q : (■ P → Q) ⊣⊢ (<affine> ■ P -∗ Q).
  Proof. by rewrite -(persistently_elim_plainly P) impl_wand_intuitionistically. Qed.

  Lemma persistently_impl_plainly P Q : (■ P → <pers> Q) ⊢ <pers> (■ P → Q).
  Proof. by apply persistently_impl_si_pure. Qed.
  Lemma persistently_wand_affinely_plainly P Q :
    (<affine> ■ P -∗ <pers> Q) ⊢ <pers> (<affine> ■ P -∗ Q).
  Proof.
    rewrite -!impl_wand_affinely_plainly. apply: persistently_impl_plainly.
  Qed.

  Lemma plainly_wand_affinely_plainly P Q :
    (<affine> ■ P -∗ ■ Q) ⊢ ■ (<affine> ■ P -∗ Q).
  Proof. rewrite -!impl_wand_affinely_plainly. apply plainly_impl_plainly. Qed.

  Section plainly_affine_bi.
    Context `{!BiAffine PROP}.

    Lemma plainly_emp : ■ emp ⊣⊢@{PROP} emp.
    Proof. by rewrite -!True_emp plainly_pure. Qed.

    Lemma plainly_and_sep_l P Q : ■ P ∧ Q ⊣⊢ ■ P ∗ Q.
    Proof.
      apply (anti_symm (⊢));
        eauto using plainly_and_sep_l_1, sep_and with typeclass_instances.
    Qed.
    Lemma plainly_and_sep_r P Q : P ∧ ■ Q ⊣⊢ P ∗ ■ Q.
    Proof. by rewrite !(comm _ P) plainly_and_sep_l. Qed.

    Lemma plainly_impl_wand P Q : ■ (P → Q) ⊣⊢ ■ (P -∗ Q).
    Proof.
      apply (anti_symm (⊢)); auto using plainly_impl_wand_2.
      apply plainly_intro', wand_intro_l.
      by rewrite -plainly_and_sep_r plainly_elim impl_elim_r.
    Qed.

    Lemma impl_wand_plainly P Q : (■ P → Q) ⊣⊢ (■ P -∗ Q).
    Proof.
      apply (anti_symm (⊢)).
      - by rewrite -impl_wand_1.
      - by rewrite impl_wand_plainly_2.
    Qed.
  End plainly_affine_bi.

  (* Conditional plainly *)
  Global Instance plainly_if_ne p : NonExpansive (@plainly_if PROP _ p).
  Proof. solve_proper. Qed.
  Global Instance plainly_if_proper p : Proper ((⊣⊢) ==> (⊣⊢)) (@plainly_if PROP _ p).
  Proof. solve_proper. Qed.
  Global Instance plainly_if_mono' p : Proper ((⊢) ==> (⊢)) (@plainly_if PROP _ p).
  Proof. solve_proper. Qed.
  Global Instance plainly_if_flip_mono' p :
    Proper (flip (⊢) ==> flip (⊢)) (@plainly_if PROP _ p).
  Proof. solve_proper. Qed.

  Lemma plainly_if_mono p P Q : (P ⊢ Q) → ■?p P ⊢ ■?p Q.
  Proof. by intros ->. Qed.

  Lemma plainly_if_pure p φ : ■?p ⌜φ⌝ ⊣⊢@{PROP} ⌜φ⌝.
  Proof. destruct p; simpl; auto using plainly_pure. Qed.
  Lemma plainly_if_and p P Q : ■?p (P ∧ Q) ⊣⊢ ■?p P ∧ ■?p Q.
  Proof. destruct p; simpl; auto using plainly_and. Qed.
  Lemma plainly_if_or_2 p P Q : ■?p P ∨ ■?p Q ⊢ ■?p (P ∨ Q).
  Proof. destruct p; simpl; auto using plainly_or_2. Qed.
  Lemma plainly_if_or `{!SbiEmpValidExist PROP} p P Q :
    ■?p (P ∨ Q) ⊣⊢ ■?p P ∨ ■?p Q.
  Proof. destruct p; simpl; auto using plainly_or. Qed.
  Lemma plainly_if_exist_2 {A} p (Ψ : A → PROP) : (∃ a, ■?p (Ψ a)) ⊢ ■?p (∃ a, Ψ a).
  Proof. destruct p; simpl; auto using plainly_exist_2. Qed.
  Lemma plainly_if_exist `{!SbiEmpValidExist PROP} {A} p (Ψ : A → PROP) :
    ■?p (∃ a, Ψ a) ⊣⊢ ∃ a, ■?p (Ψ a).
  Proof. destruct p; simpl; auto using plainly_exist. Qed.
  Lemma plainly_if_sep_2 `{!BiPositive PROP} p P Q : ■?p P ∗ ■?p Q  ⊢ ■?p (P ∗ Q).
  Proof. destruct p; simpl; auto using plainly_sep_2. Qed.

  Lemma plainly_if_idemp p P : ■?p ■?p P ⊣⊢ ■?p P.
  Proof. destruct p; simpl; auto using plainly_idemp. Qed.

  (* Properties of plain propositions *)
  Global Instance Plain_proper : Proper ((≡) ==> iff) (@Plain PROP _).
  Proof. solve_proper. Qed.

  Lemma plain_plainly_2 P `{!Plain P} : P ⊢ ■ P.
  Proof. done. Qed.
  Lemma plain_plainly P `{!Plain P, !Absorbing P} : ■ P ⊣⊢ P.
  Proof. apply (anti_symm _), plain_plainly_2, _. by apply plainly_elim. Qed.
  Lemma plainly_intro P Q `{!Plain P} : (P ⊢ Q) → P ⊢ ■ Q.
  Proof. by intros <-. Qed.

  (* Typeclass instances *)
  Global Instance plainly_absorbing P : Absorbing (■ P).
  Proof. by rewrite /Absorbing /bi_absorbingly comm plainly_absorb. Qed.
  Global Instance plainly_if_absorbing P p :
    Absorbing P → Absorbing (plainly_if p P).
  Proof. intros; destruct p; simpl; apply _. Qed.

  (* Not an instance, see the bottom of this file *)
  Lemma plain_persistent P : Plain P → Persistent P.
  Proof. intros. by rewrite /Persistent -plainly_elim_persistently. Qed.

  Global Instance impl_persistent P Q :
    Absorbing P → Plain P → Persistent Q → Persistent (P → Q).
  Proof.
    intros. by rewrite /Persistent {2}(plain P) -persistently_impl_plainly
                       -(persistent Q) (plainly_into_absorbingly P) absorbing.
  Qed.

  Global Instance plainly_persistent P : Persistent (■ P).
  Proof. by rewrite /Persistent persistently_elim_plainly. Qed.

  Global Instance wand_persistent P Q :
    Plain P → Persistent Q → Absorbing Q → Persistent (P -∗ Q).
  Proof.
    intros. rewrite /Persistent {2}(plain P). trans (<pers> (■ P → Q))%I.
    - rewrite -persistently_impl_plainly impl_wand_affinely_plainly -(persistent Q).
      by rewrite affinely_plainly_elim.
    - apply persistently_mono, wand_intro_l. by rewrite sep_and impl_elim_r.
  Qed.

  Global Instance limit_preserving_Plain `{!Cofe A} (Φ : A → PROP) :
    NonExpansive Φ → LimitPreserving (λ x, Plain (Φ x)).
  Proof. intros. apply limit_preserving_entails; solve_proper. Qed.

  (* Instances for big operators *)
  Global Instance plainly_sep_weak_homomorphism
      `{!BiPositive PROP, !BiAffine PROP} :
    WeakMonoidHomomorphism bi_sep bi_sep (≡) (@plainly PROP _).
  Proof. split; try apply _. apply plainly_sep. Qed.
  Global Instance plainly_sep_entails_weak_homomorphism :
    WeakMonoidHomomorphism bi_sep bi_sep (flip (⊢)) (@plainly PROP _).
  Proof. split; try apply _. intros P Q; by rewrite plainly_sep_2. Qed.
  Global Instance plainly_sep_entails_homomorphism `{!BiAffine PROP} :
    MonoidHomomorphism bi_sep bi_sep (flip (⊢)) (@plainly PROP _).
  Proof. split; try apply _. simpl. rewrite plainly_emp. done. Qed.

  Global Instance plainly_sep_homomorphism `{!BiAffine PROP} :
    MonoidHomomorphism bi_sep bi_sep (≡) (@plainly PROP _).
  Proof. split; try apply _. apply plainly_emp. Qed.
  Global Instance plainly_and_homomorphism :
    MonoidHomomorphism bi_and bi_and (≡) (@plainly PROP _).
  Proof. split; [split|]; try apply _; [apply plainly_and | apply plainly_pure]. Qed.
  Global Instance plainly_or_homomorphism `{!SbiEmpValidExist PROP} :
    MonoidHomomorphism bi_or bi_or (≡) (@plainly PROP _).
  Proof. split; [split|]; try apply _; [apply plainly_or | apply plainly_pure]. Qed.

  Lemma big_sepL_plainly `{!BiAffine PROP} {A} (Φ : nat → A → PROP) l :
    ■ ([∗ list] k↦x ∈ l, Φ k x) ⊣⊢ [∗ list] k↦x ∈ l, ■ (Φ k x).
  Proof. apply (big_opL_commute _). Qed.
  Lemma big_andL_plainly {A} (Φ : nat → A → PROP) l :
    ■ ([∧ list] k↦x ∈ l, Φ k x) ⊣⊢ [∧ list] k↦x ∈ l, ■ (Φ k x).
  Proof. apply (big_opL_commute _). Qed.
  Lemma big_orL_plainly `{!SbiEmpValidExist PROP} {A} (Φ : nat → A → PROP) l :
    ■ ([∨ list] k↦x ∈ l, Φ k x) ⊣⊢ [∨ list] k↦x ∈ l, ■ (Φ k x).
  Proof. apply (big_opL_commute _). Qed.

  Lemma big_sepL2_plainly `{!BiAffine PROP} {A B} (Φ : nat → A → B → PROP) l1 l2 :
    ■ ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2)
    ⊣⊢ [∗ list] k↦y1;y2 ∈ l1;l2, ■ (Φ k y1 y2).
  Proof. by rewrite !big_sepL2_alt plainly_and plainly_pure big_sepL_plainly. Qed.

  Lemma big_sepM_plainly `{!BiAffine PROP, Countable K} {A} (Φ : K → A → PROP) m :
    ■ ([∗ map] k↦x ∈ m, Φ k x) ⊣⊢ [∗ map] k↦x ∈ m, ■ (Φ k x).
  Proof. apply (big_opM_commute _). Qed.

  Lemma big_sepM2_plainly `{!BiAffine PROP, Countable K} {A B}
      (Φ : K → A → B → PROP) m1 m2 :
    ■ ([∗ map] k↦x1;x2 ∈ m1;m2, Φ k x1 x2) ⊣⊢ [∗ map] k↦x1;x2 ∈ m1;m2, ■ (Φ k x1 x2).
  Proof. by rewrite !big_sepM2_alt plainly_and plainly_pure big_sepM_plainly. Qed.

  Lemma big_sepS_plainly `{!BiAffine PROP, Countable A} (Φ : A → PROP) X :
    ■ ([∗ set] y ∈ X, Φ y) ⊣⊢ [∗ set] y ∈ X, ■ (Φ y).
  Proof. apply (big_opS_commute _). Qed.

  Lemma big_sepMS_plainly `{!BiAffine PROP, Countable A} (Φ : A → PROP) X :
    ■ ([∗ mset] y ∈ X, Φ y) ⊣⊢ [∗ mset] y ∈ X, ■ (Φ y).
  Proof. apply (big_opMS_commute _). Qed.

  (* Plainness instances *)
  Global Instance pure_plain φ : Plain (PROP:=PROP) ⌜φ⌝.
  Proof. by rewrite /Plain plainly_pure. Qed.
  Global Instance emp_plain : Plain (PROP:=PROP) emp.
  Proof. apply plainly_emp_intro. Qed.
  Global Instance and_plain P Q : Plain P → Plain Q → Plain (P ∧ Q).
  Proof. intros. by rewrite /Plain plainly_and -!plain. Qed.
  Global Instance or_plain P Q : Plain P → Plain Q → Plain (P ∨ Q).
  Proof. intros. by rewrite /Plain -plainly_or_2 -!plain. Qed.
  Global Instance forall_plain {A} (Ψ : A → PROP) :
    (∀ x, Plain (Ψ x)) → Plain (∀ x, Ψ x).
  Proof.
    intros. rewrite /Plain plainly_forall. apply forall_mono=> x. by rewrite -plain.
  Qed.
  Global Instance exist_plain {A} (Ψ : A → PROP) :
    (∀ x, Plain (Ψ x)) → Plain (∃ x, Ψ x).
  Proof.
    intros. rewrite /Plain -plainly_exist_2. apply exist_mono=> x. by rewrite -plain.
  Qed.

  Global Instance impl_plain P Q : Absorbing P → Plain P → Plain Q → Plain (P → Q).
  Proof.
    intros. by rewrite /Plain {2}(plain P) -plainly_impl_plainly -(plain Q)
                       (plainly_into_absorbingly P) absorbing.
  Qed.
  Global Instance wand_plain P Q :
    Plain P → Plain Q → Absorbing Q → Plain (P -∗ Q).
  Proof.
    intros. rewrite /Plain {2}(plain P). trans (■ (■ P → Q))%I.
    - rewrite -plainly_impl_plainly impl_wand_affinely_plainly -(plain Q).
      by rewrite affinely_plainly_elim.
    - apply plainly_mono, wand_intro_l. by rewrite sep_and impl_elim_r.
  Qed.
  Global Instance sep_plain P Q : Plain P → Plain Q → Plain (P ∗ Q).
  Proof. intros. by rewrite /Plain -plainly_sep_2 -!plain. Qed.

  Global Instance plainly_plain P : Plain (■ P).
  Proof. by rewrite /Plain plainly_idemp. Qed.
  Global Instance persistently_plain P : Plain P → Plain (<pers> P).
  Proof.
    rewrite /Plain=> HP.
    rewrite {1}HP plainly_persistently_elim persistently_elim_plainly //.
  Qed.
  Global Instance affinely_plain P : Plain P → Plain (<affine> P).
  Proof. rewrite /bi_affinely. apply _. Qed.
  Global Instance intuitionistically_plain P : Plain P → Plain (□ P).
  Proof. rewrite /bi_intuitionistically. apply _. Qed.
  Global Instance absorbingly_plain P : Plain P → Plain (<absorb> P).
  Proof. rewrite /bi_absorbingly. apply _. Qed.
  Global Instance from_option_plain {A} P (Ψ : A → PROP) (mx : option A) :
    (∀ x, Plain (Ψ x)) → Plain P → Plain (from_option Ψ P mx).
  Proof. destruct mx; apply _. Qed.

  Global Instance si_pure_plain Pi : Plain (PROP:=PROP) (<si_pure> Pi).
  Proof. by rewrite /Plain plainly_si_pure. Qed.
  Global Instance si_emp_valid_plain P : Plain (<si_emp_valid> P).
  Proof. by rewrite /Plain. Qed.

  Global Instance big_sepL_nil_plain {A} (Φ : nat → A → PROP) :
    Plain ([∗ list] k↦x ∈ [], Φ k x).
  Proof. simpl; apply _. Qed.
  Global Instance big_sepL_plain {A} (Φ : nat → A → PROP) l :
    (∀ k x, Plain (Φ k x)) → Plain ([∗ list] k↦x ∈ l, Φ k x).
  Proof. revert Φ. induction l as [|x l IH]=> Φ ? /=; apply _. Qed.
  Global Instance big_andL_nil_plain {A} (Φ : nat → A → PROP) :
    Plain ([∧ list] k↦x ∈ [], Φ k x).
  Proof. simpl; apply _. Qed.
  Global Instance big_andL_plain {A} (Φ : nat → A → PROP) l :
    (∀ k x, Plain (Φ k x)) → Plain ([∧ list] k↦x ∈ l, Φ k x).
  Proof. revert Φ. induction l as [|x l IH]=> Φ ? /=; apply _. Qed.
  Global Instance big_orL_nil_plain {A} (Φ : nat → A → PROP) :
    Plain ([∨ list] k↦x ∈ [], Φ k x).
  Proof. simpl; apply _. Qed.
  Global Instance big_orL_plain {A} (Φ : nat → A → PROP) l :
    (∀ k x, Plain (Φ k x)) → Plain ([∨ list] k↦x ∈ l, Φ k x).
  Proof. revert Φ. induction l as [|x l IH]=> Φ ? /=; apply _. Qed.

  Global Instance big_sepL2_nil_plain {A B}
      (Φ : nat → A → B → PROP) :
    Plain ([∗ list] k↦y1;y2 ∈ []; [], Φ k y1 y2).
  Proof. simpl; apply _. Qed.
  Global Instance big_sepL2_plain {A B} (Φ : nat → A → B → PROP) l1 l2 :
    (∀ k x1 x2, Plain (Φ k x1 x2)) →
    Plain ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2).
  Proof. rewrite big_sepL2_alt. apply _. Qed.

  Global Instance big_sepM_empty_plain `{Countable K} {A} (Φ : K → A → PROP) :
    Plain ([∗ map] k↦x ∈ ∅, Φ k x).
  Proof. rewrite big_opM_empty. apply _. Qed.
  Global Instance big_sepM_plain `{Countable K} {A} (Φ : K → A → PROP) m :
    (∀ k x, Plain (Φ k x)) → Plain ([∗ map] k↦x ∈ m, Φ k x).
  Proof.
    induction m using map_ind;
      [rewrite big_opM_empty|rewrite big_opM_insert //]; apply _.
  Qed.

  Global Instance big_sepM2_empty_plain `{Countable K}
      {A B} (Φ : K → A → B → PROP) :
    Plain ([∗ map] k↦x1;x2 ∈ ∅;∅, Φ k x1 x2).
  Proof. rewrite big_sepM2_empty. apply _. Qed.
  Global Instance big_sepM2_plain `{Countable K}
      {A B} (Φ : K → A → B → PROP) m1 m2 :
    (∀ k x1 x2, Plain (Φ k x1 x2)) →
    Plain ([∗ map] k↦x1;x2 ∈ m1;m2, Φ k x1 x2).
  Proof. intros. rewrite big_sepM2_alt. apply _. Qed.

  Global Instance big_sepS_empty_plain `{Countable A} (Φ : A → PROP) :
    Plain ([∗ set] x ∈ ∅, Φ x).
  Proof. rewrite big_opS_empty. apply _. Qed.
  Global Instance big_sepS_plain `{Countable A} (Φ : A → PROP) X :
    (∀ x, Plain (Φ x)) → Plain ([∗ set] x ∈ X, Φ x).
  Proof.
    induction X using set_ind_L;
      [rewrite big_opS_empty|rewrite big_opS_insert //]; apply _.
  Qed.
  Global Instance big_sepMS_empty_plain `{Countable A} (Φ : A → PROP) :
    Plain ([∗ mset] x ∈ ∅, Φ x).
  Proof. rewrite big_opMS_empty. apply _. Qed.
  Global Instance big_sepMS_plain `{Countable A} (Φ : A → PROP) X :
    (∀ x, Plain (Φ x)) → Plain ([∗ mset] x ∈ X, Φ x).
  Proof.
    induction X using gmultiset_ind;
      [rewrite big_opMS_empty|rewrite big_opMS_insert]; apply _.
  Qed.

  Global Instance plainly_timeless P : Timeless P → Timeless (■ P).
  Proof. rewrite /plainly. apply _. Qed.

  (* Interaction with equality *)
  Lemma plainly_internal_eq {A : ofe} (a b : A) : ■ (a ≡ b) ⊣⊢@{PROP} a ≡ b.
  Proof.
    apply (anti_symm (⊢)).
    { by rewrite plainly_elim. }
    apply (internal_eq_rewrite' a b (λ  b, ■ (a ≡ b))%I); [solve_proper|done|].
    rewrite -(internal_eq_refl True%I a) plainly_pure; auto.
  Qed.

  Global Instance internal_eq_plain {A : ofe} (a b : A) :
    Plain (PROP:=PROP) (a ≡ b).
  Proof. by intros; rewrite /Plain plainly_internal_eq. Qed.

  Lemma prop_ext P Q : P ≡ Q ⊣⊢ ■ (P ∗-∗ Q).
  Proof. by rewrite /plainly -prop_ext_si_emp_valid si_pure_internal_eq. Qed.
  Lemma prop_ext_2 P Q : ■ (P ∗-∗ Q) ⊢ P ≡ Q.
  Proof. by rewrite prop_ext. Qed.

  Lemma plainly_alt P : ■ P ⊣⊢ <affine> P ≡ emp.
  Proof.
    rewrite -plainly_affinely_elim. apply (anti_symm (⊢)).
    - rewrite prop_ext. apply plainly_mono, and_intro; apply wand_intro_l.
      + by rewrite affinely_elim_emp left_id.
      + by rewrite left_id.
    - rewrite internal_eq_sym (internal_eq_rewrite _ _ plainly).
      by rewrite -plainly_True_emp plainly_pure True_impl.
  Qed.

  Lemma plainly_alt_absorbing P `{!Absorbing P} : ■ P ⊣⊢ P ≡ True.
  Proof.
    apply (anti_symm (⊢)).
    - rewrite prop_ext. apply plainly_mono, and_intro; apply wand_intro_l; auto.
    - rewrite internal_eq_sym (internal_eq_rewrite _ _ plainly).
      by rewrite plainly_pure True_impl.
  Qed.

  Lemma plainly_True_alt P : ■ (True -∗ P) ⊣⊢ P ≡ True.
  Proof.
    apply (anti_symm (⊢)).
    - rewrite prop_ext. apply plainly_mono, and_intro; apply wand_intro_l; auto.
      by rewrite wand_elim_r.
    - rewrite internal_eq_sym (internal_eq_rewrite _ _
        (λ Q, ■ (True -∗ Q))%I ltac:(shelve)); last solve_proper.
      by rewrite -entails_wand // -(plainly_emp_intro True) True_impl.
  Qed.

  Global Instance internal_eq_timeless P Q :
    Timeless P → Timeless Q → Timeless (PROP := PROP) (P ≡ Q).
  Proof. rewrite prop_ext. apply _. Qed.

  (* Interaction with ▷ *)
  Lemma laterN_plainly n P : ▷^n ■ P ⊣⊢ ■ ▷^n P.
  Proof. induction n as [|n IH]; simpl; auto. by rewrite IH later_plainly. Qed.

  Lemma later_plainly_if p P : ▷ ■?p P ⊣⊢ ■?p ▷ P.
  Proof. destruct p; simpl; auto using later_plainly. Qed.
  Lemma laterN_plainly_if n p P : ▷^n ■?p P ⊣⊢ ■?p (▷^n P).
  Proof. destruct p; simpl; auto using laterN_plainly. Qed.

  Lemma except_0_plainly_1 P : ◇ ■ P ⊢ ■ ◇ P.
  Proof. by rewrite /bi_except_0 -plainly_or_2 -later_plainly plainly_pure. Qed.
  Lemma except_0_plainly P : ◇ ■ P ⊣⊢ ■ ◇ P.
  Proof. by rewrite /plainly si_emp_valid_except_0 si_pure_except_0. Qed.
  Global Instance later_plain P : Plain P → Plain (▷ P).
  Proof. intros. by rewrite /Plain -later_plainly {1}(plain P). Qed.
  Global Instance laterN_plain n P : Plain P → Plain (▷^n P).
  Proof. induction n; apply _. Qed.
  Global Instance except_0_plain P : Plain P → Plain (◇ P).
  Proof. rewrite /bi_except_0; apply _. Qed.

End plainly.

(* When declared as an actual instance, [plain_persistent] will cause
failing proof searches to take exponential time, as Coq will try to
apply it the instance at any node in the proof search tree.

To avoid that, we declare it using a [Hint Immediate], so that it will
only be used at the leaves of the proof search tree, i.e. when the
premise of the hint can be derived from just the current context. *)
Global Hint Immediate plain_persistent : typeclass_instances.
