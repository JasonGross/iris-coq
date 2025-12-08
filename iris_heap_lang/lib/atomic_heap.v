From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export atomic.
From iris.heap_lang Require Export derived_laws.
From iris.heap_lang Require Import notation proofmode.
From iris.prelude Require Import options.

(** A general logically atomic interface for a heap. All parameters are
implicit, since it is expected that there is only one [heapGS_gen] in scope that
could possibly apply. For example:

  Context `{!heapGS_gen hlc Σ, !atomic_heap}.

Or, for libraries that require later credits:

  Context `{!heapGS Σ, !atomic_heap}.

Only one instance of this class should ever be in scope. To write a library that
is generic over the lock, just add a [`{!atomic_heap}] implicit parameter around
the code and [`{!atomic_heapGS Σ}] around the proofs. To use a particular atomic
heap instance, use [Local Existing Instance <atomic_heap instance>].

When writing an instance of this class, please take care not to shadow the class
projections (e.g., either use [Local Definition alloc] or avoid the name [alloc]
altogether), and do not register an instance -- just make it a [Definition] that
others can register later.
*)

(** This is the namespace that atomic heap implementations may use for their
invariants (the [heap_inv] field of [atomic_heap] below).

We hardcode it since one should have only one instance of [atomic_heap], so
having it as a parameter of this module is unnecessary. An alternative would be
adding it as a field of the class. This however would make it impossible for
the client to open its own invariants around heap operations, as they won't be
able to prove disjointness between their namespaces and the heap's. *)
Definition atomic_heapN := nroot .@ "atomic_heap".

Class atomic_heap := AtomicHeap {
  (* -- operations -- *)
  alloc : val;
  free : val;
  load : val;
  store : val;
  cmpxchg : val;
  (** * Ghost state *)
  (** The assumptions about [Σ], and the singleton [gname]s (if needed) *)
  atomic_heapGS : gFunctors → Type;
  (** [heap_inv] is an invariant that is assumed to hold by all operations. It
      can't be allocated through the interface. Instead, implementations should
      provide an initialization lemma that builds [atomic_heapGS] and [heap_inv]
      so that clients can obtain a closed proof (once they have chosen an
      implementation).

      The invariant has to be allocated together with [atomic_heapGS] since it
      is likely to contain singleton ghost state. The initialization lemma is
      not part of the interface as it can only be applied by providing an
      implementation-specific [Σ : gFunctors]. *)
  heap_inv `{!heapGS_gen hlc Σ} {H : atomic_heapGS Σ} : iProp Σ;
  #[global] heap_inv_persistent `{!heapGS_gen hlc Σ} {H : atomic_heapGS Σ} ::
    Persistent (heap_inv (H:=H));
  (* -- predicates -- *)
  pointsto `{!heapGS_gen hlc Σ} {H : atomic_heapGS Σ} (l : loc) (dq: dfrac) (v : val) : iProp Σ;
  (* -- pointsto properties -- *)
  #[global] pointsto_timeless `{!heapGS_gen hlc Σ} {H : atomic_heapGS Σ} l q v ::
    Timeless (pointsto (H:=H) l q v);
  #[global] pointsto_fractional `{!heapGS_gen hlc Σ} {H : atomic_heapGS Σ} l v ::
    Fractional (λ (q : Qp), pointsto (H:=H) l (DfracOwn q) v);
  #[global] pointsto_persistent `{!heapGS_gen hlc Σ} {H : atomic_heapGS Σ} l v ::
    Persistent (pointsto (H:=H) l DfracDiscarded v);
  #[global] pointsto_as_fractional `{!heapGS_gen hlc Σ} {H : atomic_heapGS Σ} l q v ::
    AsFractional (pointsto (H:=H) l (DfracOwn q) v) (λ q, pointsto (H:=H) l (DfracOwn q) v) q;
  #[global] pointsto_combine_sep_gives `{!heapGS_gen hlc Σ} {H : atomic_heapGS Σ}
    l dq1 dq2 v1 v2 ::
    CombineSepGives (pointsto (H:=H) l dq1 v1) (pointsto (H:=H) l dq2 v2)
      ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝;
  #[global] pointsto_combine_as `{!heapGS_gen hlc Σ} {H : atomic_heapGS Σ}
    l dq1 dq2 v1 v2 ::
    CombineSepAs (pointsto (H:=H) l dq1 v1) (pointsto (H:=H) l dq2 v2)
      (pointsto (H:=H) l (dq1 ⋅ dq2) v1) | 60; (* higher cost than Fractional *)
  pointsto_persist `{!heapGS_gen hlc Σ} {H : atomic_heapGS Σ} l dq v :
    pointsto (H:=H) l dq v ==∗ pointsto (H:=H) l DfracDiscarded v;
  (* -- operation specs -- *)
  alloc_spec `{!heapGS_gen hlc Σ} {H : atomic_heapGS Σ} (v : val) :
    heap_inv (H:=H) -∗
    {{{ True }}} alloc v {{{ l, RET #l; pointsto (H:=H) l (DfracOwn 1) v }}};
  free_spec `{!heapGS_gen hlc Σ} {H : atomic_heapGS Σ} (l : loc) (v : val) :
    heap_inv (H:=H) -∗
    {{{ pointsto (H:=H) l (DfracOwn 1) v }}} free #l {{{ l, RET #l; True }}};
  load_spec `{!heapGS_gen hlc Σ} {H : atomic_heapGS Σ} (l : loc) :
    heap_inv (H:=H) -∗
    <<{ ∀∀ (v : val) q, pointsto (H:=H) l q v }>>
      load #l @ ↑atomic_heapN
    <<{ pointsto (H:=H) l q v | RET v }>>;
  store_spec `{!heapGS_gen hlc Σ} {H : atomic_heapGS Σ} (l : loc) (w : val) :
    heap_inv (H:=H) -∗
    <<{ ∀∀ v, pointsto (H:=H) l (DfracOwn 1) v }>>
      store #l w @ ↑atomic_heapN
    <<{ pointsto (H:=H) l (DfracOwn 1) w | RET #() }>>;
  (* This spec is slightly weaker than it could be: It is sufficient for [w1]
  *or* [v] to be unboxed.  However, by writing it this way the [val_is_unboxed]
  is outside the atomic triple, which makes it much easier to use -- and the
  spec is still good enough for all our applications.
  The postcondition deliberately does not use [bool_decide] so that users can
  [destruct (decide (a = b))] and it will simplify in both places. *)
  cmpxchg_spec `{!heapGS_gen hlc Σ} {H : atomic_heapGS Σ} (l : loc) (w1 w2 : val) :
    val_is_unboxed w1 →
    heap_inv (H:=H) -∗
    <<{ ∀∀ v, pointsto (H:=H) l (DfracOwn 1) v }>>
      cmpxchg #l w1 w2 @ ↑atomic_heapN
    <<{ if decide (v = w1)
        then pointsto (H:=H) l (DfracOwn 1) w2 else pointsto (H:=H) l (DfracOwn 1) v
      | RET (v, #if decide (v = w1) then true else false) }>>;
}.

Global Arguments alloc : simpl never.
Global Arguments free : simpl never.
Global Arguments load : simpl never.
Global Arguments store : simpl never.
Global Arguments cmpxchg : simpl never.
Global Arguments pointsto : simpl never.

Existing Class atomic_heapGS.
Global Hint Mode atomic_heapGS + + : typeclass_instances.
Global Hint Extern 0 (atomic_heapGS _) => progress simpl : typeclass_instances.

Local Notation CAS e1 e2 e3 := (Snd (cmpxchg e1 e2 e3)).

Definition faa_atomic `{!atomic_heap} : val :=
  rec: "faa" "l" "n" :=
    let: "m" := load "l" in
    if: CAS "l" "m" ("m" + "n") then "m" else "faa" "l" "n".

(** Notation for heap primitives, in a module so you can import it separately. *)
Module notation.
  Notation "l ↦ dq v" := (pointsto l dq v)
    (at level 20, dq custom dfrac at level 1, format "l  ↦ dq  v") : bi_scope.

  Notation "'ref' e" := (alloc e) : expr_scope.
  Notation "! e" := (load e) : expr_scope.
  Notation "e1 <- e2" := (store e1 e2) : expr_scope.

  Notation CAS e1 e2 e3 := (Snd (cmpxchg e1 e2 e3)).
  Notation FAA e1 e2 := (faa_atomic e1 e2).
End notation.

Section derived.
  Context `{!heapGS_gen hlc Σ, !atomic_heap, !atomic_heapGS Σ}.

  Import notation.

  Lemma pointsto_agree l dq1 dq2 v1 v2 :
    l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "Hl1 Hl2". by iCombine "Hl1" "Hl2" gives %[_ ->].
  Qed.

  Lemma pointsto_combine l dq1 dq2 v1 v2 :
    l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ l ↦{dq1 ⋅ dq2} v1 ∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "Hl1 Hl2".
    iDestruct (pointsto_agree with "[$][$]") as "->".
    by iCombine "Hl1 Hl2" as "$".
  Qed.

  Lemma cas_spec (l : loc) (w1 w2 : val) :
    val_is_unboxed w1 →
    heap_inv -∗
    <<{ ∀∀ v, pointsto l (DfracOwn 1) v }>>
      CAS #l w1 w2 @ ↑atomic_heapN
    <<{ if decide (v = w1)
        then pointsto l (DfracOwn 1) w2 else pointsto l (DfracOwn 1) v
      | RET #if decide (v = w1) then true else false }>>.
  Proof.
    iIntros (?) "#Hheap %Φ AU".
    awp_apply cmpxchg_spec; [done..|].
    iApply (aacc_aupd_commit with "AU"); first done.
    iIntros (v) "H↦". iAaccIntro with "H↦"; first by eauto with iFrame.
    iIntros "$ !> HΦ !>". wp_pures. done.
  Qed.

  Lemma faa_spec (l : loc) (i2 : Z) :
    heap_inv -∗
    <<{ ∀∀ i1 : Z, pointsto l (DfracOwn 1) #i1 }>>
      FAA #l #i2 @ ↑atomic_heapN
    <<{ pointsto l (DfracOwn 1) #(i1 + i2) | RET #i1 }>>.
  Proof.
    iIntros "#Hheap %Φ AU". rewrite /faa_atomic. iLöb as "IH".
    wp_pures. awp_apply load_spec; first done.
    iApply (aacc_aupd_abort with "AU"); first done.
    iIntros (i1) "H↦". iAaccIntro with "H↦"; first by eauto with iFrame.
    iIntros "$ !> AU !>". wp_pures.
    awp_apply cas_spec; [done..|].
    iApply (aacc_aupd with "AU"); first done.
    iIntros (m) "Hl".
    iAaccIntro with "Hl"; first by eauto with iFrame.
    iIntros "Hl"; destruct (decide (#m = #i1)); simplify_eq.
    - iModIntro. iRight. iFrame. iIntros "Hpost". iModIntro. by wp_pures.
    - iModIntro. iLeft. iFrame. iIntros "AU". iModIntro. wp_pure.
      by iApply "IH".
  Qed.
End derived.

(** Proof that the primitive physical operations of heap_lang satisfy said interface. *)
Definition primitive_alloc : val :=
  λ: "v", ref "v".
Definition primitive_free : val :=
  λ: "v", Free "v".
Definition primitive_load : val :=
  λ: "l", !"l".
Definition primitive_store : val :=
  λ: "l" "x", "l" <- "x".
Definition primitive_cmpxchg : val :=
  λ: "l" "e1" "e2", CmpXchg "l" "e1" "e2".

Section proof.
  Context `{!heapGS_gen hlc Σ}.

  Lemma primitive_alloc_spec (v : val) :
    True -∗ {{{ True }}} primitive_alloc v {{{ l, RET #l; l ↦ v }}}.
  Proof.
    iIntros "_ %Φ !> _ HΦ". wp_lam. wp_alloc l. iApply "HΦ". done.
  Qed.

  Lemma primitive_free_spec (l : loc) (v : val) :
    True -∗ {{{ l ↦ v }}} primitive_free #l {{{ l, RET #l; True }}}.
  Proof.
    iIntros "_ %Φ !> Hl HΦ". wp_lam. wp_free. iApply "HΦ". done.
  Qed.

  Lemma primitive_load_spec (l : loc) :
    True -∗
    <<{ ∀∀ (v : val) q, l ↦{q} v }>> primitive_load #l @ ↑atomic_heapN
    <<{ l ↦{q} v | RET v }>>.
  Proof.
    iIntros "_ %Φ AU". wp_lam.
    iMod "AU" as (v q) "[H↦ [_ Hclose]]".
    wp_load. iMod ("Hclose" with "H↦") as "HΦ". done.
  Qed.

  Lemma primitive_store_spec (l : loc) (w : val) :
    True -∗
    <<{ ∀∀ v, l ↦ v }>> primitive_store #l w @ ↑atomic_heapN
    <<{ l ↦ w | RET #() }>>.
  Proof.
    iIntros "_ %Φ AU". wp_lam. wp_let.
    iMod "AU" as (v) "[H↦ [_ Hclose]]".
    wp_store. iMod ("Hclose" with "H↦") as "HΦ". done.
  Qed.

  Lemma primitive_cmpxchg_spec (l : loc) (w1 w2 : val) :
    val_is_unboxed w1 →
    True -∗
    <<{ ∀∀ (v : val), l ↦ v }>>
      primitive_cmpxchg #l w1 w2 @ ↑atomic_heapN
    <<{ if decide (v = w1) then l ↦ w2 else l ↦ v
      | RET (v, #if decide (v = w1) then true else false) }>>.
  Proof.
    iIntros (?) "_ %Φ AU". wp_lam. wp_pures.
    iMod "AU" as (v) "[H↦ [_ Hclose]]".
    destruct (decide (v = w1)) as [Heq|Hne];
      [wp_cmpxchg_suc|wp_cmpxchg_fail];
    iMod ("Hclose" with "H↦") as "HΦ"; done.
  Qed.
End proof.

(* NOT an instance because users should choose explicitly to use it
     (using [Existing Instance]). *)
Definition primitive_atomic_heap : atomic_heap :=
  {| atomic_heapGS _ := TCTrue
   ; alloc_spec _ _ _ _ := primitive_alloc_spec
   ; free_spec _ _ _ _ := primitive_free_spec
   ; load_spec _ _ _ _ := primitive_load_spec
   ; store_spec _ _ _ _ := primitive_store_spec
   ; cmpxchg_spec _ _ _ _ := primitive_cmpxchg_spec
   ; pointsto_persist _ _ _ _ := primitive_laws.pointsto_persist |}.
