From stdpp Require Export namespaces.
From iris.algebra Require Import reservation_map agree frac.
From iris.algebra Require Export dfrac.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export own.
From iris.base_logic.lib Require Import ghost_map.
From iris.prelude Require Import options.
Import uPred.

(** This file provides a generic mechanism for a language-level point-to
connective [l ↦{dq} v] reflecting the physical heap.  This library is designed to
be used as a singleton (i.e., with only a single instance existing in any
proof), with the [gen_heapGS] typeclass providing the ghost names of that unique
instance.  That way, [pointsto] does not need an explicit [gname] parameter.
This mechanism can be plugged into a language and related to the physical heap
by using [gen_heap_interp σ] in the state interpretation of the weakest
precondition. See heap-lang for an example.

If you are looking for a library providing "ghost heaps" independent of the
physical state, you will likely want explicit ghost names to disambiguate
multiple heaps and are thus better off using [ghost_map], or (if you need more
flexibility), directly using the underlying [algebra.lib.gmap_view].

This library is generic in the types [L] for locations and [V] for values and
supports fractional permissions.  Next to the point-to connective [l ↦{dq} v],
which keeps track of the value [v] of a location [l], this library also provides
a way to attach "meta" or "ghost" data to locations. This is done as follows:

- When one allocates a location, in addition to the point-to connective [l ↦ v],
  one also obtains the token [meta_token l ⊤]. This token is an exclusive
  resource that denotes that no meta data has been associated with the
  namespaces in the mask [⊤] for the location [l].
- Meta data tokens can be split w.r.t. namespace masks, i.e.
  [meta_token l (E1 ∪ E2) ⊣⊢ meta_token l E1 ∗ meta_token l E2] if [E1 ## E2].
- Meta data can be set using the update [meta_token l E ==∗ meta l N x] provided
  [↑N ⊆ E], and [x : A] for any countable [A]. The [meta l N x] connective is
  persistent and denotes the knowledge that the meta data [x] has been
  associated with namespace [N] to the location [l].

To make the mechanism as flexible as possible, the [x : A] in [meta l N x] can
be of any countable type [A]. This means that you can associate e.g. single
ghost names, but also tuples of ghost names, etc.

To further increase flexibility, the [meta l N x] and [meta_token l E]
connectives are annotated with a namespace [N] and mask [E]. That way, one can
assign a map of meta information to a location. This is particularly useful when
building abstractions, then one can gradually assign more ghost information to a
location instead of having to do all of this at once. We use namespaces so that
these can be matched up with the invariant namespaces. *)

(** To implement this mechanism, we use three pieces of ghost state:

- A [ghost_map L V], which keeps track of the values of locations.
- A [ghost_map L gname], which keeps track of the meta information of
  locations. More specifically, this RA introduces an indirection: it keeps
  track of a ghost name for each location.
- The ghost names in the aforementioned authoritative RA refer to namespace maps
  [reservation_map (agree positive)], which store the actual meta information.
  This indirection is needed because we cannot perform frame preserving updates
  in an authoritative fragment without owning the full authoritative element
  (in other words, without the indirection [meta_set] would need [gen_heap_interp]
  as a premise).
 *)

(** The CMRAs we need, and the global ghost names we are using. *)

Class gen_heapGpreS (L V : Type) (Σ : gFunctors) `{Countable L} := {
  #[local] gen_heapGpreS_heap :: ghost_mapG Σ L V;
  #[local] gen_heapGpreS_meta :: ghost_mapG Σ L gname;
  #[local] gen_heapGpreS_meta_data :: inG Σ (reservation_mapR (agreeR positiveO));
}.

Class gen_heapGS (L V : Type) (Σ : gFunctors) `{Countable L} := GenHeapGS {
  #[local] gen_heap_inG :: gen_heapGpreS L V Σ;
  gen_heap_name : gname;
  gen_meta_name : gname
}.
Global Arguments GenHeapGS L V Σ {_ _ _} _ _.
Global Arguments gen_heap_name {L V Σ _ _} _ : assert.
Global Arguments gen_meta_name {L V Σ _ _} _ : assert.

Definition gen_heapΣ (L V : Type) `{Countable L} : gFunctors := #[
  ghost_mapΣ L V;
  ghost_mapΣ L gname;
  GFunctor (reservation_mapR (agreeR positiveO))
].

Global Instance subG_gen_heapGpreS {Σ L V} `{Countable L} :
  subG (gen_heapΣ L V) Σ → gen_heapGpreS L V Σ.
Proof. solve_inG. Qed.

Section definitions.
  Context `{Countable L, hG : !gen_heapGS L V Σ}.

  Definition gen_heap_interp (σ : gmap L V) : iProp Σ := ∃ m : gmap L gname,
    (* The [⊆] is used to avoid assigning ghost information to the locations in
    the initial heap (see [gen_heap_init]). *)
    ⌜ dom m ⊆ dom σ ⌝ ∗
    ghost_map_auth (gen_heap_name hG) 1 σ ∗
    ghost_map_auth (gen_meta_name hG) 1 m.

  Local Definition pointsto_def (l : L) (dq : dfrac) (v: V) : iProp Σ :=
    l ↪[gen_heap_name hG]{dq} v.
  Local Definition pointsto_aux : seal (@pointsto_def). Proof. by eexists. Qed.
  Definition pointsto := pointsto_aux.(unseal).
  Local Definition pointsto_unseal : @pointsto = @pointsto_def :=
    pointsto_aux.(seal_eq).

  Local Definition meta_token_def (l : L) (E : coPset) : iProp Σ :=
    ∃ γm, l ↪[gen_meta_name hG]□ γm ∗ own γm (reservation_map_token E).
  Local Definition meta_token_aux : seal (@meta_token_def). Proof. by eexists. Qed.
  Definition meta_token := meta_token_aux.(unseal).
  Local Definition meta_token_unseal :
    @meta_token = @meta_token_def := meta_token_aux.(seal_eq).

  (** [reservation_map_data] uses a [positive] instead of a [namespace] as key.
  For [meta_set] to hold, we can pick any positive in [↑ N], which we obtain
  using [coPpick]. *)
  Local Definition meta_def `{Countable A} (l : L) (N : namespace) (x : A) : iProp Σ :=
    ∃ γm, l ↪[gen_meta_name hG]□ γm ∗
          own γm (reservation_map_data (coPpick (↑ N)) (to_agree (encode x))).
  Local Definition meta_aux : seal (@meta_def). Proof. by eexists. Qed.
  Definition meta := meta_aux.(unseal).
  Local Definition meta_unseal : @meta = @meta_def := meta_aux.(seal_eq).
End definitions.
Global Arguments meta {L _ _ V Σ _ A _ _} l N x.

Local Notation "l ↦ dq v" := (pointsto l dq v)
  (at level 20, dq custom dfrac at level 1, format "l  ↦ dq  v") : bi_scope.

Section gen_heap.
  Context {L V} `{Countable L, !gen_heapGS L V Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : V → iProp Σ.
  Implicit Types σ : gmap L V.
  Implicit Types m : gmap L gname.
  Implicit Types l : L.
  Implicit Types v : V.

  (** General properties of pointsto *)
  Global Instance pointsto_timeless l dq v : Timeless (l ↦{dq} v).
  Proof. rewrite pointsto_unseal. apply _. Qed.
  Global Instance pointsto_fractional l v : Fractional (λ q, l ↦{#q} v)%I.
  Proof. rewrite pointsto_unseal. apply _. Qed.
  Global Instance pointsto_as_fractional l q v :
    AsFractional (l ↦{#q} v) (λ q, l ↦{#q} v)%I q.
  Proof. rewrite pointsto_unseal. apply _. Qed.
  Global Instance pointsto_persistent l v : Persistent (l ↦□ v).
  Proof. rewrite pointsto_unseal. apply _. Qed.

  Lemma pointsto_valid l dq v : l ↦{dq} v -∗ ⌜✓ dq⌝%Qp.
  Proof. rewrite pointsto_unseal. apply ghost_map_elem_valid. Qed.
  Lemma pointsto_valid_2 l dq1 dq2 v1 v2 :
    l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
  Proof. rewrite pointsto_unseal. apply ghost_map_elem_valid_2. Qed.
  (** Almost all the time, this is all you really need. *)
  Lemma pointsto_agree l dq1 dq2 v1 v2 : l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ ⌜v1 = v2⌝.
  Proof. rewrite pointsto_unseal. apply ghost_map_elem_agree. Qed.

  Global Instance pointsto_combine_sep_gives l dq1 dq2 v1 v2 :
    CombineSepGives (l ↦{dq1} v1) (l ↦{dq2} v2) ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝ | 30.
  Proof.
    rewrite /CombineSepGives. iIntros "[H1 H2]".
    iDestruct (pointsto_valid_2 with "H1 H2") as %?. eauto.
  Qed.

  Lemma pointsto_combine l dq1 dq2 v1 v2 :
    l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ l ↦{dq1 ⋅ dq2} v1 ∗ ⌜v1 = v2⌝.
  Proof. rewrite pointsto_unseal. apply ghost_map_elem_combine. Qed.

  Global Instance pointsto_combine_as l dq1 dq2 v1 v2 :
    CombineSepAs (l ↦{dq1} v1) (l ↦{dq2} v2) (l ↦{dq1 ⋅ dq2} v1) | 60.
    (* higher cost than the Fractional instance, which kicks in for #qs *)
  Proof.
    rewrite /CombineSepAs. iIntros "[H1 H2]".
    iDestruct (pointsto_combine with "H1 H2") as "[$ _]".
  Qed.

  Lemma pointsto_frac_ne l1 l2 dq1 dq2 v1 v2 :
    ¬ ✓(dq1 ⋅ dq2) → l1 ↦{dq1} v1 -∗ l2 ↦{dq2} v2 -∗ ⌜l1 ≠ l2⌝.
  Proof. rewrite pointsto_unseal. apply ghost_map_elem_frac_ne. Qed.
  Lemma pointsto_ne l1 l2 dq2 v1 v2 : l1 ↦ v1 -∗ l2 ↦{dq2} v2 -∗ ⌜l1 ≠ l2⌝.
  Proof. rewrite pointsto_unseal. apply ghost_map_elem_ne. Qed.

  (** Permanently turn any points-to predicate into a persistent
      points-to predicate. *)
  Lemma pointsto_persist l dq v : l ↦{dq} v ==∗ l ↦□ v.
  Proof. rewrite pointsto_unseal. apply ghost_map_elem_persist. Qed.

  (** Recover fractional ownership for read-only element. *)
  Lemma pointsto_unpersist l v :
    l ↦□ v ==∗ ∃ q, l ↦{# q} v.
  Proof. rewrite pointsto_unseal. apply ghost_map_elem_unpersist. Qed.

  (** Framing support *)
  Global Instance frame_pointsto p l v q1 q2 q :
    FrameFractionalQp q1 q2 q →
    Frame p (l ↦{#q1} v) (l ↦{#q2} v) (l ↦{#q} v) | 5.
  Proof. apply: frame_fractional. Qed.

  (** General properties of [meta] and [meta_token] *)
  Global Instance meta_token_timeless l N : Timeless (meta_token l N).
  Proof. rewrite meta_token_unseal. apply _. Qed.
  Global Instance meta_timeless `{Countable A} l N (x : A) : Timeless (meta l N x).
  Proof. rewrite meta_unseal. apply _. Qed.
  Global Instance meta_persistent `{Countable A} l N (x : A) : Persistent (meta l N x).
  Proof. rewrite meta_unseal. apply _. Qed.

  Lemma meta_token_union_1 l E1 E2 :
    E1 ## E2 → meta_token l (E1 ∪ E2) -∗ meta_token l E1 ∗ meta_token l E2.
  Proof.
    rewrite meta_token_unseal /meta_token_def. intros ?. iDestruct 1 as (γm1) "[#Hγm Hm]".
    rewrite reservation_map_token_union //. iDestruct "Hm" as "[Hm1 Hm2]".
    iSplitL "Hm1"; eauto.
  Qed.
  Lemma meta_token_union_2 l E1 E2 :
    meta_token l E1 -∗ meta_token l E2 -∗ meta_token l (E1 ∪ E2).
  Proof.
    rewrite meta_token_unseal /meta_token_def.
    iIntros "(%γm1 & #Hγm1 & Hm1) (%γm2 & #Hγm2 & Hm2)".
    iCombine "Hγm1 Hγm2" gives %[_ ->].
    iCombine "Hm1 Hm2" gives %?%reservation_map_token_valid_op.
    iExists γm2. iFrame "Hγm2". rewrite reservation_map_token_union //. by iSplitL "Hm1".
  Qed.
  Lemma meta_token_union l E1 E2 :
    E1 ## E2 → meta_token l (E1 ∪ E2) ⊣⊢ meta_token l E1 ∗ meta_token l E2.
  Proof.
    intros; iSplit; first by iApply meta_token_union_1.
    iIntros "[Hm1 Hm2]". by iApply (meta_token_union_2 with "Hm1 Hm2").
  Qed.
  Lemma meta_token_valid_2 l E1 E2 :
    meta_token l E1 -∗ meta_token l E2 -∗ ⌜E1 ## E2⌝.
  Proof.
    rewrite meta_token_unseal /meta_token_def.
    iIntros "(%γm1 & #Hγm1 & Hm1) (%γm2 & #Hγm2 & Hm2)".
    iCombine "Hγm1 Hγm2" gives %[_ ->].
    by iCombine "Hm1 Hm2" gives %?%reservation_map_token_valid_op.
  Qed.

  Global Instance meta_token_combine_as l E1 E2 :
    CombineSepGives (meta_token l E1) (meta_token l E2) ⌜E1 ## E2⌝.
  Proof.
    rewrite /CombineSepGives. iIntros "[H1 H2]".
    iDestruct (meta_token_valid_2 with "H1 H2") as %?; auto.
  Qed.

  Lemma meta_token_ne l1 l2 E :
    E ≠ ∅ → meta_token l1 ⊤ -∗ meta_token l2 E -∗ ⌜l1 ≠ l2⌝.
  Proof.
    iIntros "%HE H1 H2" (->). iCombine "H1 H2" gives %Hdisj.
    destruct HE. by apply disjoint_top_l_L.
  Qed.

  Lemma meta_token_difference l E1 E2 :
    E1 ⊆ E2 → meta_token l E2 ⊣⊢ meta_token l E1 ∗ meta_token l (E2 ∖ E1).
  Proof.
    intros. rewrite {1}(union_difference_L E1 E2) //.
    by rewrite meta_token_union; last set_solver.
  Qed.

  Lemma meta_agree `{Countable A} l i (x1 x2 : A) :
    meta l i x1 -∗ meta l i x2 -∗ ⌜x1 = x2⌝.
  Proof.
    rewrite meta_unseal /meta_def.
    iIntros "(%γm1 & Hγm1 & Hm1) (%γm2 & Hγm2 & Hm2)".
    iCombine "Hγm1 Hγm2" gives %[_ ->].
    iCombine "Hm1 Hm2" gives %Hγ; iPureIntro.
    move: Hγ. rewrite -reservation_map_data_op reservation_map_data_valid.
    move=> /to_agree_op_inv_L. naive_solver.
  Qed.
  Lemma meta_set `{Countable A} E l (x : A) N :
    ↑ N ⊆ E → meta_token l E ==∗ meta l N x.
  Proof.
    rewrite meta_token_unseal meta_unseal /meta_token_def /meta_def.
    iDestruct 1 as (γm) "[Hγm Hm]". iExists γm. iFrame "Hγm".
    iApply (own_update with "Hm").
    apply reservation_map_alloc; last done.
    pose proof (coPpick_elem_of (↑ N) (nclose_non_empty _)); set_solver.
  Qed.

  Lemma meta_meta_token_valid `{Countable A} l (x : A) N E :
    meta l N x -∗ meta_token l E -∗ ⌜↑N ⊈ E⌝.
  Proof.
    rewrite meta_token_unseal meta_unseal /meta_token_def /meta_def.
    iIntros "(%γm & #Hγm & Hm1) (%γm' & #Hγm' & Hm2) %Hsub".
    iCombine "Hγm Hγm'" gives %[_ <-].
    iCombine "Hm1 Hm2" gives %Hvalid. iPureIntro.
    rewrite reservation_map_valid_eq /= left_id_L right_id_L in Hvalid.
    destruct Hvalid as [_ Hvalid]. specialize (Hvalid (coPpick (↑ N))).
    rewrite lookup_singleton_eq in Hvalid.
    pose proof (coPpick_elem_of (↑ N) (nclose_non_empty _)); set_solver.
  Qed.
  Lemma meta_meta_token_valid' `{Countable A} l (x : A) N E :
    ↑N ⊆ E → meta l N x -∗ meta_token l E -∗ False.
  Proof.
    iIntros (?) "#Hmeta Htoken".
    by iDestruct (meta_meta_token_valid with "Hmeta Htoken") as %?.
  Qed.

  Global Instance combine_sep_gives_meta_meta_token_1
      `{Countable A} l (x : A) N E :
    CombineSepGives (meta l N x) (meta_token l E) ⌜↑N ⊈ E⌝.
  Proof.
    rewrite /CombineSepGives. iIntros "[#Hmeta Htoken]".
    iDestruct (meta_meta_token_valid with "Hmeta Htoken") as %?. by eauto.
  Qed.

  Global Instance combine_sep_gives_meta_meta_token_2
      `{Countable A} l (x : A) N E :
    CombineSepGives (meta_token l E) (meta l N x) ⌜↑N ⊈ E⌝.
  Proof.
    rewrite /CombineSepGives. iIntros "[Htoken #Hmeta]".
    iCombine "Hmeta Htoken" gives %?; eauto.
  Qed.

  (** Update lemmas *)
  Lemma gen_heap_alloc σ l v :
    σ !! l = None →
    gen_heap_interp σ ==∗ gen_heap_interp (<[l:=v]>σ) ∗ l ↦ v ∗ meta_token l ⊤.
  Proof.
    iIntros (Hσl). rewrite /gen_heap_interp pointsto_unseal /pointsto_def
      meta_token_unseal /meta_token_def /=.
    iDestruct 1 as (m Hσm) "[Hσ Hm]".
    iMod (ghost_map_insert l with "Hσ") as "[Hσ Hl]"; first done.
    iMod (own_alloc (reservation_map_token ⊤)) as (γm) "Hγm".
    { apply reservation_map_token_valid. }
    iMod (ghost_map_insert_persist l with "Hm") as "[Hm Hlm]".
    { move: Hσl. rewrite -!not_elem_of_dom. set_solver. }
    iModIntro. iFrame "Hl". iSplitL "Hσ Hm"; last by eauto with iFrame.
    iExists (<[l:=γm]> m). iFrame. iPureIntro.
    rewrite !dom_insert_L. set_solver.
  Qed.

  Lemma gen_heap_alloc_big σ σ' :
    σ' ##ₘ σ →
    gen_heap_interp σ ==∗
    gen_heap_interp (σ' ∪ σ) ∗ ([∗ map] l ↦ v ∈ σ', l ↦ v) ∗ ([∗ map] l ↦ _ ∈ σ', meta_token l ⊤).
  Proof.
    revert σ; induction σ' as [| l v σ' Hl IH] using map_ind; iIntros (σ Hdisj) "Hσ".
    { rewrite left_id_L. auto. }
    iMod (IH with "Hσ") as "[Hσ'σ Hσ']"; first by eapply map_disjoint_insert_l.
    decompose_map_disjoint.
    rewrite !big_opM_insert // -insert_union_l //.
    by iMod (gen_heap_alloc with "Hσ'σ") as "($ & $ & $)";
      first by apply lookup_union_None.
  Qed.

  Lemma gen_heap_valid σ l dq v : gen_heap_interp σ -∗ l ↦{dq} v -∗ ⌜σ !! l = Some v⌝.
  Proof.
    iDestruct 1 as (m Hσm) "[Hσ _]". iIntros "Hl".
    rewrite /gen_heap_interp pointsto_unseal.
    by iCombine "Hσ Hl" gives %?.
  Qed.

  Lemma gen_heap_update σ l v1 v2 :
    gen_heap_interp σ -∗ l ↦ v1 ==∗ gen_heap_interp (<[l:=v2]>σ) ∗ l ↦ v2.
  Proof.
    iDestruct 1 as (m Hσm) "[Hσ Hm]".
    iIntros "Hl". rewrite /gen_heap_interp pointsto_unseal /pointsto_def.
    iCombine "Hσ Hl" gives %Hl.
    iMod (ghost_map_update with "Hσ Hl") as "[Hσ Hl]".
    iModIntro. iFrame "Hl". iExists m. iFrame.
    iPureIntro. apply elem_of_dom_2 in Hl.
    rewrite dom_insert_L. set_solver.
  Qed.
End gen_heap.

(** This variant of [gen_heap_init] should only be used when absolutely needed.
The key difference to [gen_heap_init] is that the [inG] instances in the new
[gen_heapGS] instance are related to the original [gen_heapGpreS] instance,
whereas [gen_heap_init] forgets about that relation. *)
Lemma gen_heap_init_names `{Countable L, !gen_heapGpreS L V Σ} σ :
  ⊢ |==> ∃ γh γm : gname,
    let hG := GenHeapGS L V Σ γh γm in
    gen_heap_interp σ ∗ ([∗ map] l ↦ v ∈ σ, l ↦ v) ∗ ([∗ map] l ↦ _ ∈ σ, meta_token l ⊤).
Proof.
  iMod (ghost_map_alloc_empty (K:=L) (V:=V)) as (γh) "Hh".
  iMod (ghost_map_alloc_empty (K:=L) (V:=gname)) as (γm) "Hm".
  iExists γh, γm.
  iAssert (gen_heap_interp (hG:=GenHeapGS _ _ _ γh γm) ∅) with "[Hh Hm]" as "Hinterp".
  { iExists ∅; simpl. iFrame "Hh Hm". by rewrite dom_empty_L. }
  iMod (gen_heap_alloc_big with "Hinterp") as "(Hinterp & $ & $)".
  { apply map_disjoint_empty_r. }
  rewrite right_id_L. done.
Qed.

Lemma gen_heap_init `{Countable L, !gen_heapGpreS L V Σ} σ :
  ⊢ |==> ∃ _ : gen_heapGS L V Σ,
    gen_heap_interp σ ∗ ([∗ map] l ↦ v ∈ σ, l ↦ v) ∗ ([∗ map] l ↦ _ ∈ σ, meta_token l ⊤).
Proof.
  iMod (gen_heap_init_names σ) as (γh γm) "Hinit".
  iExists (GenHeapGS _ _ _ γh γm).
  done.
Qed.
