Require Export modures.logic prelude.strings.
Require Import prelude.stringmap.

Inductive env (M : cmraT) :=
  | Enil : env M
  | Eadd : env M → string → uPred M → env M.

Delimit Scope proof_scope with env.
Arguments Enil {_}.
Arguments Eadd {_} _%proof_scope _%string _%uPred_scope.

(* Context manupulation stuff *)
Instance env_lookup {M} : Lookup string (uPred M) (env M) :=
  fix go x E {struct E} := let _ : Lookup _ _ _ := @go in
  match E with
  | Enil => None
  | Eadd E x' P => if decide (x = x') then Some P else E !! x
  end.
Inductive env_wf {M} : env M → Prop :=
  | Enil_wf : env_wf Enil
  | Eadd_wf E x P : E !! x = None → env_wf E → env_wf (Eadd E x P).

Fixpoint env_to_list {M} (E : env M) : list (uPred M) :=
  match E with Enil => [] | Eadd E _ P => P :: env_to_list E end.
Coercion env_to_list : env >-> list.
Instance env_dom {M} : Dom (env M) stringset :=
  fix go E := let _ : Dom _ _ := @go in
  match E with Enil => ∅ | Eadd E x _ => {[ x ]} ∪ dom stringset E end.

Fixpoint env_add_list {M}
    (E : env M) (xPs : list (string * uPred M)) : option (env M) :=
  match xPs with
  | [] => Some E
  | (x,P) :: xPs => guard (E !! x = None); env_add_list (Eadd E x P) xPs
  end.

Fixpoint env_split {M} (xs : list string) (E : env M) : (env M * env M) :=
  match E with
  | Enil => (Enil, Enil)
  | Eadd E x P => 
     let (E1,E2) := env_split xs E in
     if decide (x ∈ xs) then (Eadd E1 x P, E2) else (E1, Eadd E2 x P)
  end.

Fixpoint env_replace {M}
    (x : string) (xPs : list (string * uPred M)) (E : env M) : option (env M) :=
  match E with
  | Enil => None
  | Eadd E y P => 
     if decide (x = y)
     then env_add_list E xPs
     else guard (y ∉ fst <$> xPs); E' ← env_replace x xPs E; Some (Eadd E' y P)
  end.

(* The entailment *)
Definition uPred_proofmode {M} (Ebox Estar : env M) (Q : uPred M) : Prop :=
  env_wf Ebox → env_wf Estar →
  (□ (uPred_big_and Ebox) ★ uPred_big_sep Estar)%I ⊆ Q.
Arguments uPred_proofmode _ _%proof_scope _%proof_scope _%uPred_scope.

(* Notations in a module so we can Import them when needed without cluttering
the scopes *)
Module notations.
Notation "​" := Enil (format "​") : proof_scope.
Notation "E H : P" := (Eadd E H P)
  (at level 199, left associativity, format "E H  :  P '//'") : proof_scope.
Notation "Ebox '--------------------------------------' □ Estar '--------------------------------------' ★ Q" :=
  (uPred_proofmode Ebox Estar Q%I)
  (at level 199, left associativity,
  format "Ebox '--------------------------------------' □ '//' Estar '--------------------------------------' ★ '//' Q").
Notation "Estar '--------------------------------------' ★ Q" :=
  (uPred_proofmode Enil Estar Q%I)
  (at level 199, left associativity,
  format "Estar '--------------------------------------' ★ '//' Q").
Notation "Ebox '--------------------------------------' □ Q" :=
  (uPred_proofmode Ebox Enil Q%I)
  (at level 199, left associativity,
  format "Ebox '--------------------------------------' □ '//' Q").
Notation "Q ​" := (uPred_proofmode Enil Enil Q%I) (at level 1).
End notations.

(* Coq versions of the tactics *)
Section tactics.
Context (M : cmraT).
Implicit Types Ebox Estar : env M.
Implicit Types P Q : uPred M.

Lemma uSound P Q : uPred_proofmode Enil Enil (P → Q) → P ⊆ Q.
Proof.
  intros HPQ; apply uPred.impl_elim with P; [|reflexivity].
  etransitivity; [|apply HPQ; constructor]; simpl.
  rewrite uPred.always_const, (left_id _ _); apply uPred.True_intro.
Qed.

(* basic *)
Lemma uConst Ebox Estar (P : Prop) :
  P → uPred_proofmode Ebox Estar (uPred_const P).
Proof. by intros ???; apply uPred.const_intro. Qed.
Lemma uExact Ebox Estar x P :
  Estar !! x = Some P → uPred_proofmode Ebox Estar P.
Proof. intros ???. Admitted.
Lemma uStarRename Ebox Estar Estar' x y P Q :
  Estar !! x = Some P →
  env_replace x [(y,P)] Estar = Some Estar' →
  uPred_proofmode Ebox Estar' Q →
  uPred_proofmode Ebox Estar Q.
Proof.
  intros Hx Hx' HQ ??.
Admitted.
Lemma uStarClear Ebox Estar Estar' x P Q :
  Estar !! x = Some P →
  env_replace x [] Estar = Some Estar' →
  uPred_proofmode Ebox Estar' Q →
  uPred_proofmode Ebox Estar Q.
Proof.
  intros Hx Hx' HQ ??.
Admitted.
Lemma uStarExFalso Ebox Estar x Q :
  Estar !! x = Some False%I →
  uPred_proofmode Ebox Estar Q.
Proof.
  intros Hx ??.
Admitted.

(* implication *)
Lemma uIntro Ebox Estar x P Q :
  Ebox !! x = None →
  uPred_proofmode Ebox (Eadd Enil x P) Q →
  uPred_proofmode Ebox Estar (P → Q).
Proof.
  intros Hx HP ??. 
Admitted.
Lemma uBoxedIntro Ebox Estar x P Q :
  Ebox !! x = None →
  uPred_proofmode (Eadd Ebox x P) Estar Q →
  uPred_proofmode Ebox Estar (□ P → Q).
Proof.
  intros Hx HP ??. 
Admitted.

(* star *)
Lemma uStarDestruct Ebox Estar Estar' x y1 y2 P1 P2 Q :
  Estar !! x = Some (P1 ★ P2)%I →
  env_replace x [(y1,P1); (y2,P2)] Estar = Some Estar' →
  uPred_proofmode Ebox Estar' Q →
  uPred_proofmode Ebox Estar Q.
Proof.
  intros Hx Hx' HQ ??.
Admitted.

Lemma uStarSplit Ebox Estar Estar1 Estar2 xs Q1 Q2 :
  env_split xs Estar = (Estar1,Estar2) →
  uPred_proofmode Ebox Estar1 Q1 →
  uPred_proofmode Ebox Estar2 Q2 →
  uPred_proofmode Ebox Estar (Q1 ★ Q2).
Proof.
  intros Hx HQ1 HQ2 ??.
Admitted.

(* existential *)
Lemma uStarExistDestruct {A} Ebox Estar Estar' x y (P : A → uPred M) Q :
  Estar !! x = Some (∃ x, P x)%I →
  (∀ a,
    env_replace x [(y,P a)] Estar = Some Estar' ∧
    uPred_proofmode Ebox Estar' Q) →
  uPred_proofmode Ebox Estar Q.
Proof.
  intros Hx HQ ??.
Admitted.

(* wand *)
Lemma uWandIntro Ebox Estar x P Q :
  Estar !! x = None →
  uPred_proofmode Ebox (Eadd Estar x P) Q →
  uPred_proofmode Ebox Estar (P -★ Q).
Proof.
  intros Hx HP ??. 
Admitted.

(* Conjunction *)
Lemma uSplit Ebox Estar P Q :
  uPred_proofmode Ebox Estar P → uPred_proofmode Ebox Estar Q →
  uPred_proofmode Ebox Estar (P ∧ Q).
Proof. intros HP HQ ??; apply uPred.and_intro; auto. Qed.

(* Disjunction *)
Lemma uLeft Ebox Estar P Q :
  uPred_proofmode Ebox Estar P → uPred_proofmode Ebox Estar (P ∨ Q).
Proof. intros HP ??; apply uPred.or_intro_l; auto. Qed.
Lemma uRight Ebox Estar P Q :
  uPred_proofmode Ebox Estar Q → uPred_proofmode Ebox Estar (P ∨ Q).
Proof. intros HQ ??; apply uPred.or_intro_r; auto. Qed.
End tactics.

Import notations.

(* To avoid unfolding in the hypotheses, but it still unfolds too much if
any of the below appears in an hypothesis. We should figure out how to do
this better. *)

Ltac ucbv := cbv [
  fmap lookup decide mguard mbind (* operational classes *)
  env_replace env_lookup env_split env_add_list (* env *)
  option_guard option_bind option_eq_dec option_eq_None_dec (* option *)
  list_fmap fst elem_of_list_dec list_eq_dec List.list_eq_dec list_rect (* list *)
  sumbool_rec sumbool_rect (* sumbool *)
  bool_eq_dec bool_rec bool_rect bool_dec (* bool *)
  assci_eq_dec ascii_to_digits Ascii.ascii_dec Ascii.ascii_rec Ascii.ascii_rect
  string_eq_dec string_rec string_rect (* strings *)].

(* Generate a fresh variable for the starred context *)
Ltac uFreshStarName :=
  match goal with
  | |- uPred_proofmode _ ?Estar _ =>
     eval vm_compute in (fresh_string_of_set (dom stringset Estar) "?")
  end.

(* Grammar of intro-patterns, still very incomplete: need also stuff for False,
and, or and exist *)
Inductive intro_pat :=
  | IClear : intro_pat
  | IAnom : intro_pat
  | IName :> string → intro_pat
  | ISep :> intro_seps → intro_pat
with intro_seps :=
  | ISepNil : intro_seps
  | ISepCons : intro_pat → intro_seps → intro_seps.

Inductive intro_list :=
  | IListNil : intro_list
  | IListCons : intro_pat → intro_list → intro_list.

Notation "'_" := IClear : intro_pat_scope. (* just _ yields in clashes *)
Notation "?" := IAnom : intro_pat_scope.
Notation "★[ ] " := ISepNil : intro_pat_scope.
Notation "★[ x ] " := (ISepCons x ISepNil) : intro_pat_scope.
Notation "★[ x ; .. ; y ] " :=
  (ISepCons x .. (ISepCons y ISepNil) ..) : intro_pat_scope.
Notation ">[ ] " := IListNil : intro_pat_scope.
Notation ">[ x ] " := (IListCons x IListNil) : intro_pat_scope.
Notation ">[ x ; .. ; y ] " :=
  (IListCons x .. (IListCons y IListNil) ..) : intro_pat_scope.
Open Scope intro_pat_scope.

Ltac sanitize_intro_pat pat :=
  match type of pat with
  | intro_pat => pat
  | intro_seps => constr:(ISep pat)
  | string => constr:(IName pat)
  | _ => fail 2 "invalid intro_pat" pat
  end.

Tactic Notation "uIntro" constr(x) := first
  [ apply uIntro with x; [by vm_compute|]
  | apply uWandIntro with x; [by vm_compute|] ].
Tactic Notation "uIntro" := let x := uFreshStarName in uIntro x.
Tactic Notation "uExFalso" constr(x) := apply uStarExFalso with x; reflexivity.
Tactic Notation "uSepDestruct" constr(x) "as" constr(y1) constr(y2) :=
  eapply uStarDestruct with _ x y1 y2 _ _;
    [ucbv; reflexivity|ucbv; reflexivity|]. (* just reflexivity is slow *)
Tactic Notation "uRename" constr(x) "into" constr(y) :=
  eapply uStarRename with _ x y _; [ucbv; reflexivity|ucbv; reflexivity|].
Tactic Notation "uClear" constr(x) :=
  eapply uStarClear with _ x _; [ucbv; reflexivity|ucbv; reflexivity|].

(* Probably nicer to implement some of this intro-pattern stuff in Coq, or to
optimize a bit to avoid duplicate renamings *)

(* Currently works just for star, it considers some ad-hoc cases. It takes a
list of names for generated hypotheses. *)
Tactic Notation "uDestruct" constr(z) "as" constr(pat) :=
  let rec go z pat :=
    match pat with
    | IAnom => idtac
    | IClear => uClear z
    | IName ?y => uRename z into y
    | ISep ISepNil => uExFalso z
    | ISep (ISepCons _ ISepNil) => fail 2 "singleton separating intro_pat"
    (* this code is horrible and probably wrong *)
    | ISep (ISepCons ?pat1 (ISepCons ?pat2 ISepNil)) =>
       let y1 := uFreshStarName in
       let y2 := eval compute in (y1 +:+ "'") in (* need decent way to generate multiple fresh names *)
       uSepDestruct z as y1 y2; go y1 pat1; go y2 pat2
    | ISep (ISepCons ?pat ?seps) =>
       let y1 := uFreshStarName in
       let y2 := eval compute in (y1 +:+ "'") in
       uSepDestruct z as y1 y2;
       go y1 pat;
       let pat' := constr:(ISep seps) in go y2 pat'
    end
  in let pat := sanitize_intro_pat pat in go z pat.

Tactic Notation "uIntros" constr(pat) :=
  let rec go pat :=
    match pat with
    | IListNil => idtac
    | IListCons (IName ?y) ?pat => uIntro y; go pat
    | IListCons ?pat1 ?pat2 =>
       let z := uFreshStarName in uIntro z; uDestruct z as pat1; go pat2
    | _ => fail 2 "intro failed" pat
    end
  in
    match type of pat with
    | intro_list => go pat
    | _ =>
       let pat := sanitize_intro_pat pat in
       let pats := constr:(IListCons pat IListNil) in go pats
    end.

Tactic Notation "uLeft" := apply uLeft.
Tactic Notation "uRight" := apply uRight.
Tactic Notation "uSplit" := apply uSplit.
Tactic Notation "uSplit" constr(xs') :=
  eapply uStarSplit with (xs:=xs'); [ucbv; reflexivity| |].
Tactic Notation "uExact" constr(x) := by apply uExact with x.
Tactic Notation "uAssumption" :=
  let rec go Estar P :=
    lazymatch Estar with
    | Enil => fail 2 "assumption failed"
    | Eadd ?Estar ?x P => uExact x
    | Eadd ?Estar _ _ => go Estar P
    end
  in match goal with |- uPred_proofmode _ ?Estar ?P => go Estar P end.

(* Make sure that by and done solve trivial things in proof mode *)
Hint Extern 0 (uPred_proofmode _ _ _) => by apply uConst.
Hint Extern 0 (uPred_proofmode _ _ _) => uAssumption.

Import notations.

Lemma demo (M : cmraT) (P1 P2 P3 P4 Q : uPred M) (P5 : nat → uPredC M):
    (P2 ★ (P3 ★ Q) ★ True ★ P1 ★ P2 ★ (P4 ★ (∃ x:nat, P5 x ∨ P3)) ★ True)%I
  ⊆ (P1 -★ (True ★ True) -★ ((P2 ★ P3) ★ Q ★ P1 ★ True) ∧ (P2 ∨ False) ∧ (False → P5 0))%I.
Proof.
  (* enter proof mode *)
  apply uSound.
  (* Intro-patterns do something :) *)
  uIntros >[★["H2"; ★["H4";"H4'"]; ?; "H6"; "H7"; "foo"; '_]; "bla"; ★[?;?]].
  (* To test destruct: can also be part of the intro-pattern *)
  uDestruct "foo" as ★['_; "meh"].
  repeat uSplit; [|by uLeft|uIntros ★[]].
  (* split takes a list of hypotheses just for the LHS *)
  uSplit ["H2";"H4"].
  * by uSplit ["H2"].
  * uSplit ["H4'"]. uAssumption. by uSplit ["H6"].
Time Qed.
