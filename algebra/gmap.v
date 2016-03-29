From iris.algebra Require Export cmra option.
From iris.prelude Require Export gmap.
From iris.algebra Require Import upred.

Section cofe.
Context `{Countable K} {A : cofeT}.
Implicit Types m : gmap K A.

Instance gmap_dist : Dist (gmap K A) := λ n m1 m2,
  ∀ i, m1 !! i ≡{n}≡ m2 !! i.
Program Definition gmap_chain (c : chain (gmap K A))
  (k : K) : chain (option A) := {| chain_car n := c n !! k |}.
Next Obligation. by intros c k n i ?; apply (chain_cauchy c). Qed.
Instance gmap_compl : Compl (gmap K A) := λ c,
  map_imap (λ i _, compl (gmap_chain c i)) (c 0).
Definition gmap_cofe_mixin : CofeMixin (gmap K A).
Proof.
  split.
  - intros m1 m2; split.
    + by intros Hm n k; apply equiv_dist.
    + intros Hm k; apply equiv_dist; intros n; apply Hm.
  - intros n; split.
    + by intros m k.
    + by intros m1 m2 ? k.
    + by intros m1 m2 m3 ?? k; trans (m2 !! k).
  - by intros n m1 m2 ? k; apply dist_S.
  - intros n c k; rewrite /compl /gmap_compl lookup_imap.
    feed inversion (λ H, chain_cauchy c 0 n H k); simpl; auto with lia.
    by rewrite conv_compl /=; apply reflexive_eq.
Qed.
Canonical Structure gmapC : cofeT := CofeT gmap_cofe_mixin.
Global Instance gmap_discrete : Discrete A → Discrete gmapC.
Proof. intros ? m m' ? i. by apply (timeless _). Qed.
(* why doesn't this go automatic? *)
Global Instance gmapC_leibniz: LeibnizEquiv A → LeibnizEquiv gmapC.
Proof. intros; change (LeibnizEquiv (gmap K A)); apply _. Qed.

Global Instance lookup_ne n k :
  Proper (dist n ==> dist n) (lookup k : gmap K A → option A).
Proof. by intros m1 m2. Qed.
Global Instance lookup_proper k :
  Proper ((≡) ==> (≡)) (lookup k : gmap K A → option A) := _.
Global Instance alter_ne f k n :
  Proper (dist n ==> dist n) f → Proper (dist n ==> dist n) (alter f k).
Proof.
  intros ? m m' Hm k'.
  by destruct (decide (k = k')); simplify_map_eq; rewrite (Hm k').
Qed.
Global Instance insert_ne i n :
  Proper (dist n ==> dist n ==> dist n) (insert (M:=gmap K A) i).
Proof.
  intros x y ? m m' ? j; destruct (decide (i = j)); simplify_map_eq;
    [by constructor|by apply lookup_ne].
Qed.
Global Instance singleton_ne i n :
  Proper (dist n ==> dist n) (singletonM i : A → gmap K A).
Proof. by intros ???; apply insert_ne. Qed.
Global Instance delete_ne i n :
  Proper (dist n ==> dist n) (delete (M:=gmap K A) i).
Proof.
  intros m m' ? j; destruct (decide (i = j)); simplify_map_eq;
    [by constructor|by apply lookup_ne].
Qed.

Instance gmap_empty_timeless : Timeless (∅ : gmap K A).
Proof.
  intros m Hm i; specialize (Hm i); rewrite lookup_empty in Hm |- *.
  inversion_clear Hm; constructor.
Qed.
Global Instance gmap_lookup_timeless m i : Timeless m → Timeless (m !! i).
Proof.
  intros ? [x|] Hx; [|by symmetry; apply: timeless].
  assert (m ≡{0}≡ <[i:=x]> m)
    by (by symmetry in Hx; inversion Hx; cofe_subst; rewrite insert_id).
  by rewrite (timeless m (<[i:=x]>m)) // lookup_insert.
Qed.
Global Instance gmap_insert_timeless m i x :
  Timeless x → Timeless m → Timeless (<[i:=x]>m).
Proof.
  intros ?? m' Hm j; destruct (decide (i = j)); simplify_map_eq.
  { by apply: timeless; rewrite -Hm lookup_insert. }
  by apply: timeless; rewrite -Hm lookup_insert_ne.
Qed.
Global Instance gmap_singleton_timeless i x :
  Timeless x → Timeless ({[ i := x ]} : gmap K A) := _.
End cofe.

Arguments gmapC _ {_ _} _.

(* CMRA *)
Section cmra.
Context `{Countable K} {A : cmraT}.
Implicit Types m : gmap K A.

Instance gmap_op : Op (gmap K A) := merge op.
Instance gmap_core : Core (gmap K A) := fmap core.
Instance gmap_valid : Valid (gmap K A) := λ m, ∀ i, ✓ (m !! i).
Instance gmap_validN : ValidN (gmap K A) := λ n m, ∀ i, ✓{n} (m !! i).

Lemma lookup_op m1 m2 i : (m1 ⋅ m2) !! i = m1 !! i ⋅ m2 !! i.
Proof. by apply lookup_merge. Qed.
Lemma lookup_core m i : core m !! i = core (m !! i).
Proof. by apply lookup_fmap. Qed.

Lemma gmap_included_spec (m1 m2 : gmap K A) : m1 ≼ m2 ↔ ∀ i, m1 !! i ≼ m2 !! i.
Proof.
  split; [by intros [m Hm] i; exists (m !! i); rewrite -lookup_op Hm|].
  revert m2. induction m1 as [|i x m Hi IH] using map_ind=> m2 Hm.
  { exists m2. by rewrite left_id. }
  destruct (IH (delete i m2)) as [m2' Hm2'].
  { intros j. move: (Hm j); destruct (decide (i = j)) as [->|].
    - intros _. rewrite Hi. apply: cmra_unit_least.
    - rewrite lookup_insert_ne // lookup_delete_ne //. }
  destruct (Hm i) as [my Hi']; simplify_map_eq.
  exists (partial_alter (λ _, my) i m2')=>j; destruct (decide (i = j)) as [->|].
  - by rewrite Hi' lookup_op lookup_insert lookup_partial_alter.
  - move: (Hm2' j). by rewrite !lookup_op lookup_delete_ne //
      lookup_insert_ne // lookup_partial_alter_ne.
Qed.

Definition gmap_cmra_mixin : CMRAMixin (gmap K A).
Proof.
  split.
  - by intros n m1 m2 m3 Hm i; rewrite !lookup_op (Hm i).
  - by intros n m1 m2 Hm i; rewrite !lookup_core (Hm i).
  - by intros n m1 m2 Hm ? i; rewrite -(Hm i).
  - intros m; split.
    + by intros ? n i; apply cmra_valid_validN.
    + intros Hm i; apply cmra_valid_validN=> n; apply Hm.
  - intros n m Hm i; apply cmra_validN_S, Hm.
  - by intros m1 m2 m3 i; rewrite !lookup_op assoc.
  - by intros m1 m2 i; rewrite !lookup_op comm.
  - by intros m i; rewrite lookup_op !lookup_core cmra_core_l.
  - by intros m i; rewrite !lookup_core cmra_core_idemp.
  - intros x y; rewrite !gmap_included_spec; intros Hm i.
    by rewrite !lookup_core; apply cmra_core_preserving.
  - intros n m1 m2 Hm i; apply cmra_validN_op_l with (m2 !! i).
    by rewrite -lookup_op.
  - intros n m m1 m2 Hm Hm12.
    assert (∀ i, m !! i ≡{n}≡ m1 !! i ⋅ m2 !! i) as Hm12'
      by (by intros i; rewrite -lookup_op).
    set (f i := cmra_extend n (m !! i) (m1 !! i) (m2 !! i) (Hm i) (Hm12' i)).
    set (f_proj i := proj1_sig (f i)).
    exists (map_imap (λ i _, (f_proj i).1) m, map_imap (λ i _, (f_proj i).2) m);
      repeat split; intros i; rewrite /= ?lookup_op !lookup_imap.
    + destruct (m !! i) as [x|] eqn:Hx; rewrite !Hx /=; [|constructor].
      rewrite -Hx; apply (proj2_sig (f i)).
    + destruct (m !! i) as [x|] eqn:Hx; rewrite /=; [apply (proj2_sig (f i))|].
      pose proof (Hm12' i) as Hm12''; rewrite Hx in Hm12''.
      by symmetry; apply option_op_positive_dist_l with (m2 !! i).
    + destruct (m !! i) as [x|] eqn:Hx; simpl; [apply (proj2_sig (f i))|].
      pose proof (Hm12' i) as Hm12''; rewrite Hx in Hm12''.
      by symmetry; apply option_op_positive_dist_r with (m1 !! i).
Qed.
Canonical Structure gmapR : cmraT := CMRAT gmap_cofe_mixin gmap_cmra_mixin.
Global Instance gmap_cmra_unit : CMRAUnit gmapR.
Proof.
  split.
  - by intros i; rewrite lookup_empty.
  - by intros m i; rewrite /= lookup_op lookup_empty (left_id_L None _).
  - apply gmap_empty_timeless.
Qed.
Global Instance gmap_cmra_discrete : CMRADiscrete A → CMRADiscrete gmapR.
Proof. split; [apply _|]. intros m ? i. by apply: cmra_discrete_valid. Qed.

(** Internalized properties *)
Lemma gmap_equivI {M} m1 m2 : (m1 ≡ m2) ⊣⊢ (∀ i, m1 !! i ≡ m2 !! i : uPred M).
Proof. by uPred.unseal. Qed.
Lemma gmap_validI {M} m : (✓ m) ⊣⊢ (∀ i, ✓ (m !! i) : uPred M).
Proof. by uPred.unseal. Qed.
End cmra.

Arguments gmapR _ {_ _} _.

Section properties.
Context `{Countable K} {A : cmraT}.
Implicit Types m : gmap K A.
Implicit Types i : K.
Implicit Types a : A.

Lemma lookup_validN n m i x : ✓{n} m → m !! i ≡{n}≡ Some x → ✓{n} x.
Proof. by move=> /(_ i) Hm Hi; move:Hm; rewrite Hi. Qed.
Lemma lookup_valid m i x : ✓ m → m !! i ≡ Some x → ✓ x.
Proof. move=> Hm Hi. move:(Hm i). by rewrite Hi. Qed.
Lemma insert_validN n m i x : ✓{n} x → ✓{n} m → ✓{n} <[i:=x]>m.
Proof. by intros ?? j; destruct (decide (i = j)); simplify_map_eq. Qed.
Lemma insert_valid m i x : ✓ x → ✓ m → ✓ <[i:=x]>m.
Proof. by intros ?? j; destruct (decide (i = j)); simplify_map_eq. Qed.
Lemma singleton_validN n i x : ✓{n} ({[ i := x ]} : gmap K A) ↔ ✓{n} x.
Proof.
  split; [|by intros; apply insert_validN, cmra_unit_validN].
  by move=>/(_ i); simplify_map_eq.
Qed.
Lemma singleton_valid i x : ✓ ({[ i := x ]} : gmap K A) ↔ ✓ x.
Proof. rewrite !cmra_valid_validN. by setoid_rewrite singleton_validN. Qed.

Lemma insert_singleton_opN n m i x :
  m !! i = None ∨ m !! i ≡{n}≡ Some (core x) → <[i:=x]> m ≡{n}≡ {[ i := x ]} ⋅ m.
Proof.
  intros Hi j; destruct (decide (i = j)) as [->|];
    [|by rewrite lookup_op lookup_insert_ne // lookup_singleton_ne // left_id].
  rewrite lookup_op lookup_insert lookup_singleton.
  by destruct Hi as [->| ->]; constructor; rewrite ?cmra_core_r.
Qed.
Lemma insert_singleton_op m i x :
  m !! i = None ∨ m !! i ≡ Some (core x) → <[i:=x]> m ≡ {[ i := x ]} ⋅ m.
Proof. rewrite !equiv_dist; naive_solver eauto using insert_singleton_opN. Qed.

Lemma core_singleton (i : K) (x : A) :
  core ({[ i := x ]} : gmap K A) = {[ i := core x ]}.
Proof. apply map_fmap_singleton. Qed.
Lemma op_singleton (i : K) (x y : A) :
  {[ i := x ]} ⋅ {[ i := y ]} = ({[ i := x ⋅ y ]} : gmap K A).
Proof. by apply (merge_singleton _ _ _ x y). Qed.

Global Instance gmap_persistent m : (∀ x : A, Persistent x) → Persistent m.
Proof. intros ? i. by rewrite lookup_core persistent. Qed.
Global Instance gmap_singleton_persistent i (x : A) :
  Persistent x → Persistent {[ i := x ]}.
Proof. intros. by rewrite /Persistent core_singleton persistent. Qed.

Lemma singleton_includedN n m i x :
  {[ i := x ]} ≼{n} m ↔ ∃ y, m !! i ≡{n}≡ Some y ∧ x ≼{n} y.
Proof.
  split.
  - move=> [m' /(_ i)]; rewrite lookup_op lookup_singleton.
    case (m' !! i)=> [y|]=> Hm.
    + exists (x ⋅ y); eauto using cmra_includedN_l.
    + by exists x.
  - intros (y&Hi&[z ?]).
    exists (<[i:=z]>m)=> j; destruct (decide (i = j)) as [->|].
    + rewrite Hi lookup_op lookup_singleton lookup_insert. by constructor.
    + by rewrite lookup_op lookup_singleton_ne // lookup_insert_ne // left_id.
Qed.
Lemma dom_op m1 m2 : dom (gset K) (m1 ⋅ m2) ≡ dom _ m1 ∪ dom _ m2.
Proof.
  apply elem_of_equiv; intros i; rewrite elem_of_union !elem_of_dom.
  unfold is_Some; setoid_rewrite lookup_op.
  destruct (m1 !! i), (m2 !! i); naive_solver.
Qed.

Lemma insert_updateP (P : A → Prop) (Q : gmap K A → Prop) m i x :
  x ~~>: P → (∀ y, P y → Q (<[i:=y]>m)) → <[i:=x]>m ~~>: Q.
Proof.
  intros Hx%option_updateP' HP n mf Hm.
  destruct (Hx n (mf !! i)) as ([y|]&?&?); try done.
  { by generalize (Hm i); rewrite lookup_op; simplify_map_eq. }
  exists (<[i:=y]> m); split; first by auto.
  intros j; move: (Hm j)=>{Hm}; rewrite !lookup_op=>Hm.
  destruct (decide (i = j)); simplify_map_eq/=; auto.
Qed.
Lemma insert_updateP' (P : A → Prop) m i x :
  x ~~>: P → <[i:=x]>m ~~>: λ m', ∃ y, m' = <[i:=y]>m ∧ P y.
Proof. eauto using insert_updateP. Qed.
Lemma insert_update m i x y : x ~~> y → <[i:=x]>m ~~> <[i:=y]>m.
Proof. rewrite !cmra_update_updateP; eauto using insert_updateP with subst. Qed.

Lemma singleton_updateP (P : A → Prop) (Q : gmap K A → Prop) i x :
  x ~~>: P → (∀ y, P y → Q {[ i := y ]}) → {[ i := x ]} ~~>: Q.
Proof. apply insert_updateP. Qed.
Lemma singleton_updateP' (P : A → Prop) i x :
  x ~~>: P → {[ i := x ]} ~~>: λ m, ∃ y, m = {[ i := y ]} ∧ P y.
Proof. apply insert_updateP'. Qed.
Lemma singleton_update i (x y : A) : x ~~> y → {[ i := x ]} ~~> {[ i := y ]}.
Proof. apply insert_update. Qed.

Lemma singleton_updateP_empty `{Empty A, !CMRAUnit A}
    (P : A → Prop) (Q : gmap K A → Prop) i :
  ∅ ~~>: P → (∀ y, P y → Q {[ i := y ]}) → ∅ ~~>: Q.
Proof.
  intros Hx HQ n gf Hg.
  destruct (Hx n (from_option ∅ (gf !! i))) as (y&?&Hy).
  { move:(Hg i). rewrite !left_id.
    case _: (gf !! i); simpl; auto using cmra_unit_validN. }
  exists {[ i := y ]}; split; first by auto.
  intros i'; destruct (decide (i' = i)) as [->|].
  - rewrite lookup_op lookup_singleton.
    move:Hy; case _: (gf !! i); first done.
    by rewrite right_id.
  - move:(Hg i'). by rewrite !lookup_op lookup_singleton_ne // !left_id.
Qed.
Lemma singleton_updateP_empty' `{Empty A, !CMRAUnit A} (P: A → Prop) i :
  ∅ ~~>: P → ∅ ~~>: λ m, ∃ y, m = {[ i := y ]} ∧ P y.
Proof. eauto using singleton_updateP_empty. Qed.

Section freshness.
Context `{Fresh K (gset K), !FreshSpec K (gset K)}.
Lemma updateP_alloc_strong (Q : gmap K A → Prop) (I : gset K) m x :
  ✓ x → (∀ i, m !! i = None → i ∉ I → Q (<[i:=x]>m)) → m ~~>: Q.
Proof.
  intros ? HQ n mf Hm. set (i := fresh (I ∪ dom (gset K) (m ⋅ mf))).
  assert (i ∉ I ∧ i ∉ dom (gset K) m ∧ i ∉ dom (gset K) mf) as [?[??]].
  { rewrite -not_elem_of_union -dom_op -not_elem_of_union; apply is_fresh. }
  exists (<[i:=x]>m); split.
  { by apply HQ; last done; apply not_elem_of_dom. }
  rewrite insert_singleton_opN; last by left; apply not_elem_of_dom.
  rewrite -assoc -insert_singleton_opN;
    last by left; apply not_elem_of_dom; rewrite dom_op not_elem_of_union.
  by apply insert_validN; [apply cmra_valid_validN|].
Qed.
Lemma updateP_alloc (Q : gmap K A → Prop) m x :
  ✓ x → (∀ i, m !! i = None → Q (<[i:=x]>m)) → m ~~>: Q.
Proof. move=>??. eapply updateP_alloc_strong with (I:=∅); by eauto. Qed.
Lemma updateP_alloc_strong' m x (I : gset K) :
  ✓ x → m ~~>: λ m', ∃ i, i ∉ I ∧ m' = <[i:=x]>m ∧ m !! i = None.
Proof. eauto using updateP_alloc_strong. Qed.
Lemma updateP_alloc' m x :
  ✓ x → m ~~>: λ m', ∃ i, m' = <[i:=x]>m ∧ m !! i = None.
Proof. eauto using updateP_alloc. Qed.
End freshness.

(* Allocation is a local update: Just use composition with a singleton map. *)
(* Deallocation is *not* a local update. The trouble is that if we
   own {[ i ↦ x ]}, then the frame could always own "core x", and prevent
   deallocation. *)

(* Applying a local update at a position we own is a local update. *)
Global Instance gmap_alter_update `{!LocalUpdate Lv L} i :
  LocalUpdate (λ m, ∃ x, m !! i = Some x ∧ Lv x) (alter L i).
Proof.
  split; first apply _.
  intros n m1 m2 (x&Hix&?) Hm j; destruct (decide (i = j)) as [->|].
  - rewrite lookup_alter !lookup_op lookup_alter Hix /=.
    move: (Hm j); rewrite lookup_op Hix.
    case: (m2 !! j)=>[y|] //=; constructor. by apply (local_updateN L).
  - by rewrite lookup_op !lookup_alter_ne // lookup_op.
Qed.
End properties.

(** Functor *)
Instance gmap_fmap_ne `{Countable K} {A B : cofeT} (f : A → B) n :
  Proper (dist n ==> dist n) f → Proper (dist n ==>dist n) (fmap (M:=gmap K) f).
Proof. by intros ? m m' Hm k; rewrite !lookup_fmap; apply option_fmap_ne. Qed.
Instance gmap_fmap_cmra_monotone `{Countable K} {A B : cmraT} (f : A → B)
  `{!CMRAMonotone f} : CMRAMonotone (fmap f : gmap K A → gmap K B).
Proof.
  split; try apply _.
  - by intros n m ? i; rewrite lookup_fmap; apply (validN_preserving _).
  - intros m1 m2; rewrite !gmap_included_spec=> Hm i.
    by rewrite !lookup_fmap; apply: included_preserving.
Qed.
Definition gmapC_map `{Countable K} {A B} (f: A -n> B) :
  gmapC K A -n> gmapC K B := CofeMor (fmap f : gmapC K A → gmapC K B).
Instance gmapC_map_ne `{Countable K} {A B} n :
  Proper (dist n ==> dist n) (@gmapC_map K _ _ A B).
Proof.
  intros f g Hf m k; rewrite /= !lookup_fmap.
  destruct (_ !! k) eqn:?; simpl; constructor; apply Hf.
Qed.

Program Definition gmapCF K `{Countable K} (F : cFunctor) : cFunctor := {|
  cFunctor_car A B := gmapC K (cFunctor_car F A B);
  cFunctor_map A1 A2 B1 B2 fg := gmapC_map (cFunctor_map F fg)
|}.
Next Obligation.
  by intros K ?? F A1 A2 B1 B2 n f g Hfg; apply gmapC_map_ne, cFunctor_ne.
Qed.
Next Obligation.
  intros K ?? F A B x. rewrite /= -{2}(map_fmap_id x).
  apply map_fmap_setoid_ext=>y ??; apply cFunctor_id.
Qed.
Next Obligation.
  intros K ?? F A1 A2 A3 B1 B2 B3 f g f' g' x. rewrite /= -map_fmap_compose.
  apply map_fmap_setoid_ext=>y ??; apply cFunctor_compose.
Qed.
Instance gmapCF_contractive K `{Countable K} F :
  cFunctorContractive F → cFunctorContractive (gmapCF K F).
Proof.
  by intros ? A1 A2 B1 B2 n f g Hfg; apply gmapC_map_ne, cFunctor_contractive.
Qed.

Program Definition gmapRF K `{Countable K} (F : rFunctor) : rFunctor := {|
  rFunctor_car A B := gmapR K (rFunctor_car F A B);
  rFunctor_map A1 A2 B1 B2 fg := gmapC_map (rFunctor_map F fg)
|}.
Next Obligation.
  by intros K ?? F A1 A2 B1 B2 n f g Hfg; apply gmapC_map_ne, rFunctor_ne.
Qed.
Next Obligation.
  intros K ?? F A B x. rewrite /= -{2}(map_fmap_id x).
  apply map_fmap_setoid_ext=>y ??; apply rFunctor_id.
Qed.
Next Obligation.
  intros K ?? F A1 A2 A3 B1 B2 B3 f g f' g' x. rewrite /= -map_fmap_compose.
  apply map_fmap_setoid_ext=>y ??; apply rFunctor_compose.
Qed.
Instance gmapRF_contractive K `{Countable K} F :
  rFunctorContractive F → rFunctorContractive (gmapRF K F).
Proof.
  by intros ? A1 A2 B1 B2 n f g Hfg; apply gmapC_map_ne, rFunctor_contractive.
Qed.