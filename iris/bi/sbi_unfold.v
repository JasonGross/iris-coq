From iris.bi Require Export cmra internal_eq.
From iris.prelude Require Import options.
Local Set Default Proof Using "Type*".

(** The tactic takes a (bi-)entailment of plain propositions and turns it into a
a (bi-)implication in the pure step-indexed model. For example, given the goal:

  x ≼ y ⊣⊢ x.1 ≼ y.1 ∧ x.2 ≼ y.2

The tactic [sbi_unfold] turns it into

  ∀ n, x ≼{n} y ↔ x.1 ≼{n} y.1 ∧ x.2 ≼{n} y.2

The tactic [sbi_unfold] works for goals of the shape [⊢ P], [P ⊢ Q], [P ⊣⊢ Q].
Here, [P] and [Q] should be in the "plain" subset of propositions, i.e., [⌜ _ ⌝],
[<si_pure>], [✓], [≡], [≼], closed under [∧], [∨], [→], [∀], [∃], [▷], and
[match]. The separating connectives [∗]/[-∗] are translated to [∧]/[→].

The tactic attempts to minimize the number of "down closures"
[∀ n'. n' ≤ n → ..] due to the use of nested implications. For example, given:

  ⊢ x.1 ≼ y.1 → x.2 ≼ y.2 → x ≼ y

The tactic [sbi_unfold] turns it into

  ∀ n, x.1 ≼{n} y.1 → x.2 ≼{n} y.2 → x ≼{n} y

Instead of (the logically equivalent, but more verbose):

  ∀ n, ∀ n' ≤ n. x.1 ≼{n'} y.1 → ∀ n'' ≤ n'. x.2 ≼{n''} y.2 → x ≼{n''} y

The tactic is implemented using the type class [SbiUnfold clo P Pi], which takes
a proposition [P] (which is intended to be plain) as input and produces its
interpretation [Pi : nat → Prop] in the step-indexed model as output, so that
the down closure of [Pi] is equivalent to [P].

The input indicator [clo] indicates whether the output [Pi] should be down closed,
i.e., [Pi] should satisfy [Pi n1 → n2 ≤ n1 → Pi n2]. In this case there is no
need to explicitly down close [Pi]. We use the [clo] parameter to avoid needless
down closures in the translation of implications (see the example above). In
the instance [sbi_unfold_impl] for [P → Q] we call [SbiUnfold] on [Q] with [clo]
being [NotClosed]. This optimization is sound because [∀ n' ≤ n, Pi n' → Qi n']
and [∀ n' ≤ n, Pi n' → downclose Qi n'] are equivalent if [Pi] is downclosed. *)

(** Use a [Module] to avoid polluting the global namespace with the constructor
names, one should use [sbi_unfold_closure_indicator.NotClosed]. *)
Module sbi_unfold_closure_indicator.
  Inductive sbi_unfold_closure_indicator := DownClosed | NotClosed.
End sbi_unfold_closure_indicator.

Export sbi_unfold_closure_indicator (sbi_unfold_closure_indicator).
Import sbi_unfold_closure_indicator (DownClosed, NotClosed).

Class SbiUnfold `{!Sbi PROP} (clo : sbi_unfold_closure_indicator)
    (P : PROP) (Pi : nat → Prop) := {
  sbi_unfold_closed n1 n2 : clo = DownClosed → Pi n1 → n2 ≤ n1 → Pi n2;
  (* If [closed] then [SiProp_downclose] is not needed, so use the smart
  constructor [SbiUnfold_closed] below. *)
  sbi_unfold_as_si_pure : P ⊣⊢ <si_pure> SiProp_downclose Pi;
}.
Global Hint Mode SbiUnfold + + + ! - : typeclass_instances.

Lemma SbiUnfold_closed `{Sbi PROP} clo (P : PROP) Pi
    (Piclosed : ∀ n1 n2, Pi n1 → n2 ≤ n1 → Pi n2) :
  P ⊣⊢ <si_pure> SiProp Pi Piclosed → SbiUnfold clo P Pi.
Proof.
  intros HP. split; [naive_solver|]. rewrite HP.
  f_equiv. split=> n; rewrite /siProp_holds /=; naive_solver eauto with lia.
Qed.

(* Implications and bi-implications need to be down closed when [clo = true],
see e.g., [sbi_unfold_impl]. We use the following definition and smart
constructor to achieve that without having two instances. Occurrences of
[sbi_unfold_maybe_downclose] will be simplified away by the top-level
[sbi_unfold] tactic. *)
Definition sbi_unfold_maybe_downclose (clo : sbi_unfold_closure_indicator)
    (Pi : nat → Prop) (n : nat) : Prop :=
  if clo is DownClosed then ∀ n', n' ≤ n → Pi n' else Pi n.

Lemma SbiUnfold_downclose `{Sbi PROP} clo (P : PROP) Pi :
  P ⊣⊢ <si_pure> SiProp_downclose Pi →
  SbiUnfold clo P (sbi_unfold_maybe_downclose clo Pi).
Proof.
  destruct clo; [|by split].
  intros HP. split; [naive_solver eauto with lia|]. rewrite HP.
  f_equiv. split=> n; rewrite /siProp_holds /=; naive_solver eauto with lia.
Qed.

Lemma sbi_unfold_closed_weaken `{Sbi PROP} clo (P : PROP) Pi :
  SbiUnfold DownClosed P Pi → SbiUnfold clo P Pi.
Proof. intros [??]; split; naive_solver. Qed.

(** This instance can be applied to any [P : siProp] so it has cost 100 to make
sure it's only used if no other instance can be used. *)
Global Instance sbi_unfold_siprop clo (P : siProp) :
  SbiUnfold clo P (siProp_holds P) | 100.
Proof. apply: SbiUnfold_closed; [by eauto using siProp_closed|]. by split. Qed.

Section sbi_unfold.
  Context `{Sbi PROP}.
  Implicit Types P Q : PROP.
  Local Arguments siProp_holds !_.
  Local Notation SbiUnfold := (SbiUnfold (PROP:=PROP)).

  (** The top-level lemmas used by the tactic *)
  Lemma sbi_unfold_entails `{!SbiUnfold DownClosed P Pi, !SbiUnfold NotClosed Q Qi} :
    (P ⊢ Q) ↔ ∀ n, Pi n → Qi n.
  Proof.
    destruct select (SbiUnfold _ P _) as [? HP].
    destruct select (SbiUnfold _ Q _) as [? HQ].
    rewrite HP HQ si_pure_entails.
    split; [intros []|split]; naive_solver eauto with lia.
  Qed.

  Lemma sbi_unfold_equiv `{!SbiUnfold DownClosed P Pi, !SbiUnfold DownClosed Q Qi} :
    P ⊣⊢ Q ↔ ∀ n, Pi n ↔ Qi n.
  Proof.
    pose proof @sbi_unfold_closed_weaken.
    rewrite bi.equiv_entails !sbi_unfold_entails. naive_solver.
  Qed.

  Lemma sbi_unfold_emp_valid `{!SbiUnfold NotClosed Q Qi} :
    (⊢ Q) ↔ ∀ n, Qi n.
  Proof.
    destruct select (SbiUnfold _ Q _) as [? HQ].
    rewrite HQ si_pure_emp_valid /bi_emp_valid. siProp.unseal.
    split; [intros []|split]; naive_solver eauto with lia.
  Qed.

  (** The instances *)
  Global Instance sbi_unfold_pure clo φ : SbiUnfold clo ⌜ φ ⌝ (λ _, φ).
  Proof.
    apply: SbiUnfold_closed. rewrite -si_pure_pure. f_equiv. by siProp.unseal.
  Qed.

  Global Instance sbi_unfold_internal_eq {A : ofe} clo (x y : A) :
    SbiUnfold clo (x ≡ y) (λ n, x ≡{n}≡ y).
  Proof.
    apply: SbiUnfold_closed; [by eauto using dist_le|].
    intros ?. rewrite /internal_eq. f_equiv. by siProp.unseal.
  Qed.

  Global Instance sbi_unfold_internal_cmra_valid {A : cmra} clo (x : A) :
    SbiUnfold clo (✓ x) (λ n, ✓{n} x).
  Proof.
    apply: SbiUnfold_closed; [by eauto using cmra_validN_le|].
    intros ?. rewrite /internal_cmra_valid. f_equiv. by siProp.unseal.
  Qed.

  Global Instance sbi_unfold_internal_included {A : cmra} clo (x y : A) :
    SbiUnfold clo (x ≼ y) (λ n, x ≼{n} y).
  Proof.
    apply: SbiUnfold_closed; [by eauto using cmra_includedN_le|].
    intros ?. rewrite /internal_included /internal_eq -si_pure_exist.
    f_equiv. by siProp.unseal.
  Qed.

  Global Instance sbi_unfold_si_pure clo (Psi : siProp) Pi :
    bi.sbi_unfold.SbiUnfold clo Psi Pi →
    SbiUnfold clo (<si_pure> Psi) Pi.
  Proof. intros [? HP]. split; [done|]. by rewrite HP. Qed.

  Global Instance sbi_unfold_and clo P Q Pi Qi :
    SbiUnfold clo P Pi →
    SbiUnfold clo Q Qi →
    SbiUnfold clo (P ∧ Q) (λ n, Pi n ∧ Qi n).
  Proof.
    intros [? HP] [? HQ]. split; [naive_solver|].
    rewrite HP HQ -si_pure_and. f_equiv.
    siProp.unseal. split=> n /=. destruct clo; naive_solver.
  Qed.

  Global Instance sbi_unfold_sep clo P Q Pi Qi :
    SbiUnfold clo P Pi →
    SbiUnfold clo Q Qi →
    SbiUnfold clo (P ∗ Q) (λ n, Pi n ∧ Qi n).
  Proof.
    intros [? HP] [? HQ]. split; [naive_solver|].
    rewrite HP HQ -si_pure_and_sep. f_equiv.
    siProp.unseal. split=> n /=. destruct clo; naive_solver.
  Qed.

  (** The instance for disjunction needs the sub-expressions to be already down
  closed because [∨] and [∀] do not commute. *)
  Global Instance sbi_unfold_or clo P Q Pi Qi :
    SbiUnfold DownClosed P Pi →
    SbiUnfold DownClosed Q Qi →
    SbiUnfold clo (P ∨ Q) (λ n, Pi n ∨ Qi n).
  Proof.
    intros [? HP] [? HQ]. apply: SbiUnfold_closed; [naive_solver|].
    intros ?. rewrite HP HQ -si_pure_or. f_equiv.
    split=> n /=; siProp.unseal; naive_solver.
  Qed.

  Global Instance sbi_unfold_impl clo P Q Pi Qi :
    SbiUnfold DownClosed P Pi →
    SbiUnfold NotClosed Q Qi →
    SbiUnfold clo (P → Q) (sbi_unfold_maybe_downclose clo (λ n, Pi n → Qi n)).
  Proof.
    intros [? HP] [? HQ]. apply SbiUnfold_downclose.
    rewrite HP HQ -si_pure_impl. f_equiv.
    split=> n /=; siProp.unseal; naive_solver eauto with lia.
  Qed.

  Global Instance sbi_unfold_wand clo P Q Pi Qi :
    SbiUnfold DownClosed P Pi →
    SbiUnfold NotClosed Q Qi →
    SbiUnfold clo (P -∗ Q) (sbi_unfold_maybe_downclose clo (λ n, Pi n → Qi n)).
  Proof.
    intros [? HP] [? HQ]. apply SbiUnfold_downclose.
    rewrite HP HQ -si_pure_impl_wand. f_equiv. 
    split=> n /=; siProp.unseal; naive_solver eauto with lia.
  Qed.

  Global Instance sbi_unfold_iff clo P Q Pi Qi :
    SbiUnfold DownClosed P Pi →
    SbiUnfold DownClosed Q Qi →
    SbiUnfold clo (P ↔ Q) (sbi_unfold_maybe_downclose clo (λ n, Pi n ↔ Qi n)).
  Proof.
    intros [? HP] [? HQ]. apply SbiUnfold_downclose.
    rewrite HP HQ -si_pure_iff. f_equiv.
    split=> n /=; rewrite /bi_iff; siProp.unseal; naive_solver eauto with lia.
  Qed.

  Global Instance sbi_unfold_iff_wand clo P Q Pi Qi :
    SbiUnfold DownClosed P Pi →
    SbiUnfold DownClosed Q Qi →
    SbiUnfold clo (P ∗-∗ Q) (sbi_unfold_maybe_downclose clo (λ n, Pi n ↔ Qi n)).
  Proof.
    intros [? HP] [? HQ]. apply SbiUnfold_downclose.
    rewrite HP HQ -si_pure_impl_iff_wand. f_equiv.
    split=> n /=; rewrite /bi_iff; siProp.unseal; naive_solver eauto with lia.
  Qed.

  Global Instance sbi_unfold_forall {A} clo (Φ : A → PROP) Φi :
    (∀ x, SbiUnfold clo (Φ x) (Φi x)) →
    SbiUnfold clo (∀ x, Φ x) (λ n, ∀ x, Φi x n).
  Proof.
    intros HΦ. split; [naive_solver|]. etrans; [f_equiv=> x; apply HΦ|].
    rewrite -si_pure_forall. f_equiv.
    split=> n /=; siProp.unseal; destruct clo; naive_solver eauto with lia.
  Qed.

  (** The instance for existential needs the sub-expression to be already down
  closed because [∃] and [∀] do not commute. *)
  Global Instance sbi_unfold_exist {A} clo (Φ : A → PROP) Φi :
    (∀ x, SbiUnfold DownClosed (Φ x) (Φi x)) →
    SbiUnfold clo (∃ x, Φ x) (λ n, ∃ x, Φi x n).
  Proof.
    intros HΦ. apply: SbiUnfold_closed; [naive_solver|].
    intros ?. etrans; [f_equiv=> x; apply HΦ|].
    rewrite -si_pure_exist. f_equiv.
    split=> n /=; siProp.unseal; destruct clo; naive_solver eauto with lia.
  Qed.

  Global Instance sbi_unfold_later clo P Pi :
    SbiUnfold clo P Pi →
    SbiUnfold clo (▷ P) (λ n, match n with 0 => True | S n' => Pi n' end).
  Proof.
    intros [? HP]. split.
    { intros [] []; naive_solver eauto with lia. }
    rewrite HP -si_pure_later. f_equiv.
    split=> n /=; siProp.unseal; simpl. split.
    - destruct n; intros ? []; naive_solver eauto with lia.
    - destruct n; [done|]. intros HPi n' ?. apply (HPi (S n')); lia.
  Qed.
End sbi_unfold.

(** We use a [Hint Extern] to translate [match]. Intuitively, we want an
instance:

  SbiUnfold (match x with Cj => Pj end) (λ n, match x with Cj => Pij n end)

Here, we have [SbiUnfold Pj Pij] for the branch of each constructor [Cj] in
the [match]. Actually generating [λ n, match x with Cj => Pij n end] is quite
fiddly. *)

(* A helper to help with HO-unification in the [Hint Extern] below. *)
Local Lemma sbi_unfold_tceq `{Sbi PROP} clo (P : PROP) Pi Pi' :
  SbiUnfold clo P Pi' → TCEq Pi Pi' → SbiUnfold clo P Pi.
Proof. by intros ? ->. Qed.

Global Hint Extern 0 (SbiUnfold _ (match ?x with _ => _ end) ?Pi) =>
  (* Use [unshelve] to turn the evar [Pi] into an explicit goal *)
  unshelve (let Pi' := open_constr:(_) in unify Pi Pi');
    [(* Refine [Pi] with [λ n, match x with .. => Pij n end], where each [Pij]
     is a new evar for constructor [j]. These evars are then shelved. *)
     intros ?; destruct x; shelve
    |(* Create an [SbiUnfold] goal for each constructor *)
     destruct x;
     (* These goals are of the form [SbiUnfold ?P (λ n, ?Pi_j)]. Since Coq's HO
     unification cannot handle the lambda reliably, we turn these goals into
     [SbiUnfold ?P ?Pi_j'] and generate equality goals [TCEq (λ n, ?Pi_j) ?Pi_j']
     that are solved later. *)
     class_apply sbi_unfold_tceq] :
  typeclass_instances.

Ltac sbi_unfold :=
  match goal with
  | |- ⊢ _ => apply sbi_unfold_emp_valid
  | |- _ ⊣⊢ _ => apply sbi_unfold_equiv
  | |- _ ⊢ _ => apply sbi_unfold_entails
  | |- _ => fail "sbi_unfold: not a BI entailment"
  end;
  (* Some instances leave a down closure, which we simplify *)
  lazy [sbi_unfold_maybe_downclose].
