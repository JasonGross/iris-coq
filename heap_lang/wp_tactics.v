From iris.algebra Require Export upred_tactics.
From iris.heap_lang Require Export tactics derived substitution.
Import uPred.

(** wp-specific helper tactics *)
Ltac wp_bind K :=
  lazymatch eval hnf in K with
  | [] => idtac
  | _ => etrans; [|fast_by apply (wp_bind K)]; simpl
  end.

Ltac wp_done := rewrite /= ?to_of_val; fast_done.

Ltac wp_value_head :=
  match goal with
  | |- _ ⊢ wp _ _ _ =>
    etrans; [|eapply wp_value_pvs; wp_done]; lazy beta;
    (* sometimes, we will have to do a final view shift, so only apply
    pvs_intro if we obtain a consecutive wp *)
    try (
      etrans; [|apply pvs_intro];
      match goal with |- _ ⊢ wp _ _ _ => simpl | _ => fail end)
  end.

Ltac wp_finish := intros_revert ltac:(
  rewrite /= ?to_of_val; try strip_later; try wp_value_head).

Tactic Notation "wp_value" :=
  lazymatch goal with
  | |- _ ⊢ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    wp_bind K; wp_value_head) || fail "wp_value: cannot find value in" e
  | _ => fail "wp_value: not a wp"
  end.

Tactic Notation "wp_rec" :=
  lazymatch goal with
  | |- _ ⊢ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    match eval hnf in e' with App ?e1 _ =>
(* hnf does not reduce through an of_val *)
(*      match eval hnf in e1 with Rec _ _ _ => *)
    wp_bind K; etrans; [|eapply wp_rec; wp_done]; simpl_subst; wp_finish
(*      end *) end) || fail "wp_rec: cannot find 'Rec' in" e
  | _ => fail "wp_rec: not a 'wp'"
  end.

Tactic Notation "wp_lam" :=
  lazymatch goal with
  | |- _ ⊢ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    match eval hnf in e' with App ?e1 _ =>
(*    match eval hnf in e1 with Rec BAnon _ _ => *)
    wp_bind K; etrans; [|eapply wp_lam; wp_done]; simpl_subst; wp_finish
(*    end *) end) || fail "wp_lam: cannot find 'Lam' in" e
  | _ => fail "wp_lam: not a 'wp'"
  end.

Tactic Notation "wp_let" := wp_lam.
Tactic Notation "wp_seq" := wp_let.

Tactic Notation "wp_op" :=
  lazymatch goal with
  | |- _ ⊢ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    match eval hnf in e' with
    | BinOp LtOp _ _ => wp_bind K; apply wp_lt; wp_finish
    | BinOp LeOp _ _ => wp_bind K; apply wp_le; wp_finish
    | BinOp EqOp _ _ => wp_bind K; apply wp_eq; wp_finish
    | BinOp _ _ _ =>
       wp_bind K; etrans; [|eapply wp_bin_op; try fast_done]; wp_finish
    | UnOp _ _ =>
       wp_bind K; etrans; [|eapply wp_un_op; try fast_done]; wp_finish
    end) || fail "wp_op: cannot find 'BinOp' or 'UnOp' in" e
  | _ => fail "wp_op: not a 'wp'"
  end.

Tactic Notation "wp_proj" :=
  lazymatch goal with
  | |- _ ⊢ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    match eval hnf in e' with
    | Fst _ => wp_bind K; etrans; [|eapply wp_fst; wp_done]; wp_finish
    | Snd _ => wp_bind K; etrans; [|eapply wp_snd; wp_done]; wp_finish
    end) || fail "wp_proj: cannot find 'Fst' or 'Snd' in" e
  | _ => fail "wp_proj: not a 'wp'"
  end.

Tactic Notation "wp_if" :=
  lazymatch goal with
  | |- _ ⊢ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    match eval hnf in e' with
    | If _ _ _ =>
      wp_bind K;
      etrans; [|eapply wp_if_true || eapply wp_if_false]; wp_finish
    end) || fail "wp_if: cannot find 'If' in" e
  | _ => fail "wp_if: not a 'wp'"
  end.

Tactic Notation "wp_match" :=
  lazymatch goal with
  | |- _ ⊢ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    match eval hnf in e' with
    | Case _ _ _ =>
      wp_bind K;
      etrans; [|first[eapply wp_match_inl; wp_done|eapply wp_match_inr; wp_done]];
      simpl_subst; wp_finish
    end) || fail "wp_match: cannot find 'Match' in" e
  | _ => fail "wp_match: not a 'wp'"
  end.

Tactic Notation "wp_focus" open_constr(efoc) :=
  lazymatch goal with
  | |- _ ⊢ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    match e' with
    | efoc => unify e' efoc; wp_bind K
    end) || fail "wp_focus: cannot find" efoc "in" e
  | _ => fail "wp_focus: not a 'wp'"
  end.
