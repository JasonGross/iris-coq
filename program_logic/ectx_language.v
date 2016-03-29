From iris.algebra Require Export base.
From iris.program_logic Require Export language.

(* We need to make thos arguments indices that we want canonical structure
   inference to use a keys. *)
Class ectx_language (expr val ectx state : Type) := EctxLanguage {
  of_val : val → expr;
  to_val : expr → option val;
  empty_ectx : ectx;
  comp_ectx : ectx → ectx → ectx;
  fill : ectx → expr → expr;
  atomic : expr → Prop;
  head_step : expr → state → expr → state → option expr → Prop;

  to_of_val v : to_val (of_val v) = Some v;
  of_to_val e v : to_val e = Some v → of_val v = e;
  val_stuck e1 σ1 e2 σ2 ef : head_step e1 σ1 e2 σ2 ef → to_val e1 = None;

  fill_empty e : fill empty_ectx e = e;
  fill_comp K1 K2 e : fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e;
  fill_inj K e1 e2 : fill K e1 = fill K e2 → e1 = e2;
  fill_not_val K e : to_val e = None → to_val (fill K e) = None;

  (* There are a whole lot of sensible axioms we could demand for comp_ectx
     and empty_ectx. However, this one is enough. *)
  ectx_positive K1 K2 :
    empty_ectx = comp_ectx K1 K2 →
    K1 = empty_ectx ∧ K2 = empty_ectx;

  step_by_val K K' e1 e1' σ1 e2 σ2 ef :
    fill K e1 = fill K' e1' →
    to_val e1 = None →
    head_step e1' σ1 e2 σ2 ef →
    exists K'', K' = comp_ectx K K'';

  atomic_not_val e : atomic e → to_val e = None;
  atomic_step e1 σ1 e2 σ2 ef :
    atomic e1 →
    head_step e1 σ1 e2 σ2 ef →
    is_Some (to_val e2);
  atomic_fill e K :
    atomic (fill K e) →
    to_val e = None →
    K = empty_ectx;
}.
Arguments of_val {_ _ _ _ _} _.
Arguments to_val {_ _ _ _ _} _.
Arguments empty_ectx {_ _ _ _ _}.
Arguments comp_ectx {_ _ _ _ _} _ _.
Arguments fill {_ _ _ _ _} _ _.
Arguments atomic {_ _ _ _ _} _.
Arguments head_step {_ _ _ _ _} _ _ _ _ _.

Arguments to_of_val {_ _ _ _ _} _.
Arguments of_to_val {_ _ _ _ _} _ _ _.
Arguments val_stuck {_ _ _ _ _} _ _ _ _ _ _.
Arguments fill_empty {_ _ _ _ _} _.
Arguments fill_comp {_ _ _ _ _} _ _ _.
Arguments fill_inj {_ _ _ _ _} _ _ _ _.
Arguments fill_not_val {_ _ _ _ _} _ _ _.
Arguments ectx_positive {_ _ _ _ _} _ _ _.
Arguments step_by_val {_ _ _ _ _} _ _ _ _ _ _ _ _ _ _ _.
Arguments atomic_not_val {_ _ _ _ _} _ _.
Arguments atomic_step {_ _ _ _ _} _ _ _ _ _ _ _.
Arguments atomic_fill {_ _ _ _ _} _ _ _ _.

(* From an ectx_language, we can construct a language. *)
Section Language.
  Context {expr val ectx state : Type} {Λ : ectx_language expr val ectx state}.
  Implicit Types (e : expr) (K : ectx).

  Definition head_reducible (e : expr) (σ : state) :=
    ∃ e' σ' ef, head_step e σ e' σ' ef.

  Inductive prim_step (e1 : expr) (σ1 : state)
    (e2 : expr) (σ2: state) (ef: option expr) : Prop :=
  Ectx_step K e1' e2' :
    e1 = fill K e1' → e2 = fill K e2' →
    head_step e1' σ1 e2' σ2 ef → prim_step e1 σ1 e2 σ2 ef.

  Lemma val_prim_stuck e1 σ1 e2 σ2 ef :
    prim_step e1 σ1 e2 σ2 ef → to_val e1 = None.
  Proof. intros [??? -> -> ?]; eauto using fill_not_val, val_stuck. Qed.

  Lemma atomic_prim_step e1 σ1 e2 σ2 ef :
  atomic e1 → prim_step e1 σ1 e2 σ2 ef → is_Some (to_val e2).
  Proof.
    intros Hatomic [K e1' e2' -> -> Hstep].
    assert (K = empty_ectx) as -> by eauto 10 using atomic_fill, val_stuck.
    eapply atomic_step; first done. by rewrite !fill_empty.
  Qed.

  Canonical Structure ectx_lang : language := {|
    language.expr := expr; language.val := val; language.state := state;
    language.of_val := of_val; language.to_val := to_val;
    language.atomic := atomic; language.prim_step := prim_step;
    language.to_of_val := to_of_val; language.of_to_val := of_to_val;
    language.val_stuck := val_prim_stuck; language.atomic_not_val := atomic_not_val;
    language.atomic_step := atomic_prim_step
  |}.

  (* Some lemmas about this language *)
  Lemma head_prim_reducible e σ :
    head_reducible e σ → reducible e σ.
  Proof.
    intros (e'&?&?&?). do 3 eexists.
    eapply Ectx_step with (K:=empty_ectx); rewrite ?fill_empty; done.
  Qed.

  Lemma head_reducible_prim_step e1 σ1 e2 σ2 ef :
    head_reducible e1 σ1 → prim_step e1 σ1 e2 σ2 ef →
    head_step e1 σ1 e2 σ2 ef.
  Proof.
    intros Hred Hstep. destruct Hstep as [? ? ? ? ? Hstep]; subst.
    rename e1' into e1. rename e2' into e2.
    destruct Hred as (e2'&σ2'&ef'&HstepK).
    destruct (step_by_val K empty_ectx e1 (fill K e1) σ1 e2' σ2' ef')
      as [K' [-> _]%ectx_positive];
      eauto using fill_empty, fill_not_val, val_stuck.
    by rewrite !fill_empty.
  Qed.

  (* Every evaluation context is a context. *)
  Global Instance ectx_lang_ctx K : LanguageCtx ectx_lang (fill K).
  Proof.
    split.
    - eauto using fill_not_val.
    - intros ????? [K' e1' e2' Heq1 Heq2 Hstep].
      by exists (comp_ectx K K') e1' e2'; rewrite ?Heq1 ?Heq2 ?fill_comp.
    - intros e1 σ1 e2 σ2 ? Hnval [K'' e1'' e2'' Heq1 -> Hstep].
      destruct (step_by_val K K'' e1 e1'' σ1 e2'' σ2 ef) as [K' ->]; eauto.
      rewrite -fill_comp in Heq1; apply fill_inj in Heq1.
      exists (fill K' e2''); rewrite -fill_comp; split; auto.
      econstructor; eauto.
  Qed.
End Language.
  
Arguments ectx_lang {_ _ _ _} _ : clear implicits.





  