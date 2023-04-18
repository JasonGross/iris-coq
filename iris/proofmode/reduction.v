From iris.bi Require Import bi telescopes.
From iris.proofmode Require Import base environments.
From iris.prelude Require Import options.

(** The following tactics should be used when performing computation in the
proofmode:

- Use [cbv]/[vm_compute] (depending on expected size of computation) if the
  expected result is a simple term (say, a boolean, number, list of strings),
  and the input term does *not* involve user terms (such as bodies of hypotheses
  in the proof mode environment).
- Use [lazy] if the expected result is a simple term and the input term *does*
  involve user terms.
- Use [pm_eval] otherwise, particularly to compute new proof mode environments
  and to lookup items in the proof mode environment.

The reduction [pm_eval] avoids reducing anything user-visible to make sure
we do not reduce e.g., before unification happens in [iApply]. This needs to
contain all definitions used in the user-visible statements in [coq_tactics],
and their dependencies.

Examples:

- [envs_lookup i Δ], where [Δ] is a proof mode environment. This should be
  computed using [pm_eval] because [Δ] involves user terms and the result is
  also a user term (a hypothesis).
- [dom Δ], where [Δ] is a proof mode environment. This should be computed with
  [lazy] because [Δ] involves user terms and the result is a list of strings.
  This should *never* be computed using [cbv]/[vm_compute] as that would eagerly
  unfold all hypotheses in [Δ]. Note that in this specific case one could also
  use [pm_eval] because all definitions in [dom] are whitelisted by [pm_eval].
  However, [lazy] is more useful when considering [f (dom Δ)] where [f] is not
  whitelisted, as [pm_eval] would simply get stuck.
- [tc_to_bool (BiAffine PROP)]. This should be computed using [lazy] as [PROP]
  involves user terms (a BI canonical structure instance) and the result is a
  mere Boolean. This term trivially normalizes with [lazy] to a Boolean (which
  is present as implicit parameter derived by TC search), while [cbv] would
  eagerly normalize the whole of [PROP] (i.e., all BI operations contained in
  the record). *)
Declare Reduction pm_eval := cbv [
  (* base *)
  base.negb base.beq
  base.Pos_succ base.ascii_beq base.string_beq base.positive_beq base.ident_beq
  (* environments *)
  env_lookup env_lookup_delete env_delete env_app env_replace
  env_dom env_intuitionistic env_spatial env_counter env_spatial_is_nil envs_dom
  envs_lookup envs_lookup_delete envs_delete envs_snoc envs_app
  envs_simple_replace envs_replace envs_split
  envs_clear_spatial envs_clear_intuitionistic envs_incr_counter
  envs_split_go envs_split
  env_to_prop_go env_to_prop env_to_prop_and_go env_to_prop_and
  (* PM list and option functions *)
  pm_app pm_option_bind pm_from_option pm_option_fun
].
Ltac pm_eval t :=
  eval pm_eval in t.
Ltac pm_reduce :=
  (* Use [change_no_check] instead of [change] to avoid performing the
  conversion check twice. *)
  match goal with |- ?u => let v := pm_eval u in change_no_check v end.

Ltac pm_reflexivity :=
  pm_reduce; notypeclasses refine eq_refl.

(** Called by many tactics for redexes that are created by instantiation.
    This cannot create any envs redexes so we just do the cbn part. *)
Declare Reduction pm_prettify := cbn [
  (* telescope combinators *)
  tele_fold tele_bind tele_app
  (* BI connectives *)
  bi_persistently_if bi_affinely_if bi_absorbingly_if bi_intuitionistically_if
  bi_wandM bi_laterN
  bi_tforall bi_texist
].
Ltac pm_prettify :=
  (* Use [change_no_check] instead of [change] to avoid performing the
  conversion check twice. *)
  match goal with |- ?u => let v := eval pm_prettify in u in change_no_check v end.
