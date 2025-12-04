From stdpp Require Import strings.
From iris.bi Require Import bi.

Unset Mangle Names.

Section tests.
  Context `{!Sbi PROP}.

  (** The following tests should *not* include a [∀ n', n' ≤ n → ..] *)
  Check "test_impl".
  Lemma test_impl {A : ofe} (x y z : A) :
    x ≡ y ⊢@{PROP} y ≡ z → x ≡ z.
  Proof. sbi_unfold. Show. Abort.

  Check "test_impl_impl_and".
  Lemma test_impl_impl_and {A : ofe} (x y z : A) :
    ⊢@{PROP} x ≡ y → y ≡ z → x ≡ z ∧ z ≡ x.
  Proof. sbi_unfold. Show. Abort.

  Check "test_exist_impl".
  Lemma test_exist_impl {A : ofe} (x z : A) :
    ⊢@{PROP} (∃ y, x ≡ y ∧ y ≡ z) → x ≡ z.
  Proof. sbi_unfold. Show. Abort.

  Check "test_exist_impl".
  Lemma test_exist_impl {A : ofe} (x z : A) :
    ⊢@{PROP} x ≡ z → ∃ y, x ≡ y ∧ y ≡ z.
  Proof. sbi_unfold. Show. Abort.

  Check "test_si_pure_exist".
  Lemma test_si_pure_exist {A : ofe} (x z : A) :
    ⊢@{PROP} <si_pure> (∃ y, <si_pure> (x ≡ y) ∧ y ≡ z) → x ≡ z.
  Proof. sbi_unfold. Show. Abort.

  Check "test_equiv_exist".
  Lemma test_iff_exist {A : ofe} (x z : A) :
    x ≡ z ⊣⊢@{PROP} ∃ y, x ≡ y ∧ y ≡ z.
  Proof. sbi_unfold. Show. Abort.

  Check "test_iff_exist".
  Lemma test_iff_exist {A : ofe} (x z : A) :
    ⊢@{PROP} x ≡ z ↔ ∃ y, x ≡ y ∧ y ≡ z.
  Proof. sbi_unfold. Show. Abort.

  Check "test_wand_iff_exist".
  Lemma test_iff_exist {A : ofe} (x z : A) :
    ⊢@{PROP} x ≡ z ∗-∗ ∃ y, x ≡ y ∧ y ≡ z.
  Proof. sbi_unfold. Show. Abort.

  Check "test_wand_iff_exist".
  Lemma test_iff_exist_later {A : ofe} (x z : A) :
    ⊢@{PROP} ▷ (x ≡ z) ∗-∗ ∃ y, ▷ (x ≡ y ∧ y ≡ z).
  Proof. sbi_unfold. Show. Abort.

  (** The following tests should include a [∀ n', n' ≤ n → ..] *)
  Check "test_exist_impl".
  Lemma test_exist_impl {A : ofe} (x z : A) :
    ⊢@{PROP} x ≡ z → ∃ y, x ≡ y → y ≡ z.
  Proof. sbi_unfold. Show. Abort.

  Check "test_forall_impl".
  Lemma test_forall_impl {A : ofe} (x z : A) :
    ⊢@{PROP} (∀ y, x ≡ y → y ≡ z) → x ≡ z.
  Proof. sbi_unfold. Show. Abort.
End tests.
