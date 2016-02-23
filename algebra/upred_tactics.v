From algebra Require Export upred.
From algebra Require Export upred_big_op.

Module upred_reflection. Section upred_reflection.
  Context {M : cmraT}.

  Inductive expr :=
    | ETrue : expr
    | EVar : nat → expr
    | ESep : expr → expr → expr.
  Fixpoint eval (Σ : list (uPred M)) (e : expr) : uPred M :=
    match e with
    | ETrue => True
    | EVar n => from_option True%I (Σ !! n)
    | ESep e1 e2 => eval Σ e1 ★ eval Σ e2
    end.
  Fixpoint flatten (e : expr) : list nat :=
    match e with
    | ETrue => []
    | EVar n => [n]
    | ESep e1 e2 => flatten e1 ++ flatten e2
    end.

  Notation eval_list Σ l :=
    (uPred_big_sep ((λ n, from_option True%I (Σ !! n)) <$> l)).
  Lemma eval_flatten Σ e : eval Σ e ≡ eval_list Σ (flatten e).
  Proof.
    induction e as [| |e1 IH1 e2 IH2];
      rewrite /= ?right_id ?fmap_app ?big_sep_app ?IH1 ?IH2 //. 
  Qed.
  Lemma flatten_entails Σ e1 e2 :
    flatten e2 `contains` flatten e1 → eval Σ e1 ⊑ eval Σ e2.
  Proof.
    intros. rewrite !eval_flatten. by apply big_sep_contains, fmap_contains.
  Qed.
  Lemma flatten_equiv Σ e1 e2 :
    flatten e2 ≡ₚ flatten e1 → eval Σ e1 ≡ eval Σ e2.
  Proof. intros He. by rewrite !eval_flatten He. Qed.

  Fixpoint prune (e : expr) : expr :=
    match e with
    | ETrue => ETrue
    | EVar n => EVar n
    | ESep e1 e2 =>
       match prune e1, prune e2 with
       | ETrue, e2' => e2'
       | e1', ETrue => e1'
       | e1', e2' => ESep e1' e2'
       end
    end.
  Lemma flatten_prune e : flatten (prune e) = flatten e.
  Proof.
    induction e as [| |e1 IH1 e2 IH2]; simplify_eq/=; auto.
    rewrite -IH1 -IH2. by repeat case_match; rewrite ?right_id_L.
  Qed.
  Lemma prune_correct Σ e : eval Σ (prune e) ≡ eval Σ e.
  Proof. by rewrite !eval_flatten flatten_prune. Qed.

  Fixpoint cancel_go (n : nat) (e : expr) : option expr :=
    match e with
    | ETrue => None
    | EVar n' => if decide (n = n') then Some ETrue else None
    | ESep e1 e2 => 
       match cancel_go n e1 with
       | Some e1' => Some (ESep e1' e2)
       | None => ESep e1 <$> cancel_go n e2
       end
    end.
  Definition cancel (n: nat) (e: expr) : option expr := prune <$> cancel_go n e.
  Lemma flatten_cancel_go e e' n :
    cancel_go n e = Some e' → flatten e ≡ₚ n :: flatten e'.
  Proof.
    revert e'; induction e as [| |e1 IH1 e2 IH2]; intros;
      repeat (simplify_option_eq || case_match); auto.
    * by rewrite IH1 //.
    * by rewrite IH2 // Permutation_middle.
  Qed.
  Lemma flatten_cancel e e' n :
    cancel n e = Some e' → flatten e ≡ₚ n :: flatten e'.
  Proof.
    rewrite /cancel fmap_Some=> -[e'' [? ->]].
    by rewrite flatten_prune -flatten_cancel_go.
  Qed.
  Lemma cancel_entails Σ e1 e2 e1' e2' n :
    cancel n e1 = Some e1' → cancel n e2 = Some e2' →
    eval Σ e1' ⊑ eval Σ e2' → eval Σ e1 ⊑ eval Σ e2.
  Proof.
    intros ??. rewrite !eval_flatten.
    rewrite (flatten_cancel e1 e1' n) // (flatten_cancel e2 e2' n) //; csimpl.
    apply uPred.sep_mono_r.
  Qed.

  Class Quote (Σ1 Σ2 : list (uPred M)) (P : uPred M) (e : expr) := {}.
  Global Instance quote_True Σ : Quote Σ Σ True ETrue.
  Global Instance quote_var Σ1 Σ2 P i:
    rlist.QuoteLookup Σ1 Σ2 P i → Quote Σ1 Σ2 P (EVar i) | 1000.
  Global Instance quote_sep Σ1 Σ2 Σ3 P1 P2 e1 e2 :
    Quote Σ1 Σ2 P1 e1 → Quote Σ2 Σ3 P2 e2 → Quote Σ1 Σ3 (P1 ★ P2) (ESep e1 e2).
  End upred_reflection.

  Ltac quote :=
    match goal with
    | |- ?P1 ⊑ ?P2 =>
      lazymatch type of (_ : Quote [] _ P1 _) with Quote _ ?Σ2 _ ?e1 =>
      lazymatch type of (_ : Quote Σ2 _ P2 _) with Quote _ ?Σ3 _ ?e2 =>
        change (eval Σ3 e1 ⊑ eval Σ3 e2)
      end end
    end.
End upred_reflection.

Tactic Notation "cancel" constr(P) :=
  let rec lookup Σ n :=
    match Σ with
    | P :: _ => n
    | _ :: ?Σ => lookup Σ (S n)
    end in
  upred_reflection.quote;
  match goal with
  | |- upred_reflection.eval ?Σ _ ⊑ upred_reflection.eval _ _ =>
    let n' := lookup Σ 0%nat in
    eapply upred_reflection.cancel_entails with (n:=n');
      [cbv; reflexivity|cbv; reflexivity|simpl]
  end.