(** * LogRel.DeclarativeSubst: stability of declarative typing by substitution. *)
From Coq Require Import CRelationClasses.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations LContexts Context NormalForms Weakening UntypedReduction
  GenericTyping DeclarativeTyping DeclarativeInstance AlgorithmicTyping.
From LogRel Require Import LogicalRelation Validity Fundamental.
From LogRel.LogicalRelation Require Import Induction Escape Irrelevance Transitivity.
From LogRel.Substitution Require Import Properties Irrelevance.

(** Currently, this is obtained as a consequence of the fundamental lemma. 
However, it could be alternatively proven much earlier, by a direct induction. *)

Set Printing Primitive Projection Parameters.

Import DeclarativeTypingProperties.

Lemma typing_subst (wl : wfLCon) : WfDeclInductionConcl
  (fun _ _ => True)
  (fun wl Γ A => forall Δ σ, [|- Δ]< wl > -> [Δ |-s σ : Γ]< wl > -> [Δ |- A[σ]]< wl >)
  (fun wl Γ A t => forall Δ σ, [|- Δ]< wl > -> [Δ |-s σ : Γ]< wl > -> [Δ |- t[σ] : A[σ]]< wl >)
  (fun wl Γ A B => forall Δ σ σ', [|- Δ]< wl > -> [Δ |-s σ ≅ σ' : Γ]< wl > -> [Δ |- A[σ] ≅ B[σ']]< wl >)
  (fun wl Γ A t u => forall Δ σ σ', [|- Δ]< wl > -> [Δ |-s σ ≅ σ' : Γ]< wl > -> [Δ |- t[σ] ≅ u[σ'] : A[σ]]< wl >) wl.
Proof.
  unshelve (repeat split ; [shelve|..]).
  - intros Γ ? Ht * HΔ Hσ.
    unshelve eapply Fundamental_subst in Hσ as [].
    3,5: boundary.
    1: now eapply wfLCon_le_id.
    apply Fundamental in Ht as [VΓ [VA _]].
    unshelve eapply Wescape, VA ; tea.
    1: now eapply wfLCon_le_id.
    unshelve eapply irrelevanceSubst ; eassumption.
  - intros * Ht * HΔ Hσ.
    unshelve eapply Fundamental_subst in Hσ as [].
    3,5: boundary.
    1: now eapply wfLCon_le_id.    
    apply Fundamental in Ht as [VΓ [VA] [Vt]].
    unshelve eapply WescapeTerm, Vt ; tea.
    1: now eapply wfLCon_le_id.
    unshelve eapply irrelevanceSubst ; eassumption.
  - intros * Ht * HΔ Hσ.
    unshelve eapply Fundamental_subst_conv in Hσ as [].
    3,5: boundary.
    1: now eapply wfLCon_le_id.
    apply Fundamental in Ht as [VΓ VA ? Vconv] ; cbn in *.
    unshelve eapply WescapeEq.
    2: unshelve eapply VA ; tea ; try irrValid.
    cbn.
    unshelve eapply WtransEq.
    5: now apply Vconv.
    + unshelve (Wirrelevance0 ; [ reflexivity | ]).
      2-3: unshelve eapply VA ; tea.
      all: try irrValid.
      Unshelve.
      1: now eapply wfLCon_le_id.
      1: assumption.
      now irrValid.
  - intros * Ht * HΔ Hσ.
    unshelve eapply Fundamental_subst_conv in Hσ as [].
    3,5: boundary.
    1: now eapply wfLCon_le_id.
    apply Fundamental in Ht as [VΓ VA Vt Vu Vtu] ; cbn in *.
    unshelve eapply WescapeEqTerm.
    2: now unshelve eapply VA ; tea ; try irrValid.
    cbn.
    eapply WtransEqTerm.
    + cbn.
      unshelve eapply Vtu.
    + cbn.
      eapply Vu.
      all: irrValid.
Qed.


Section MoreSubst.

  Lemma ctx_refl wl Γ :
    [|- Γ]< wl > ->
    [|- Γ ≅ Γ]< wl >.
  Proof.
    induction 1.
    all: constructor; tea.
    now econstructor.
  Qed.

  Lemma subst_wk wl (Γ Δ Δ' : context) (ρ : Δ' ≤ Δ) σ :
    [|- Δ']< wl > ->
    [Δ |-s σ : Γ]< wl > ->
    [Δ' |-s σ⟨ρ⟩ : Γ]< wl >.
  Proof.
    intros ?.
    induction 1 as [|σ Γ A].
    1: now econstructor.
    econstructor.
    - asimpl ; cbn in * ; asimpl.
      eassumption.
    - asimpl ; cbn in * ; asimpl.
      unfold funcomp.
      eapply typing_meta_conv.
      1: eapply typing_wk ; eassumption.
      asimpl.
      reflexivity.
  Qed.

  Corollary well_subst_up wl (Γ Δ : context) A σ :
    [Δ |- A]< wl > ->
    [Δ |-s σ : Γ]< wl > ->
    [Δ ,, A |-s σ⟨↑⟩ : Γ]< wl >.
  Proof.
    intros HA Hσ.
    eapply subst_wk with (ρ := wk_step A wk_id) in Hσ.
    - eapply well_subst_ext ; [|eassumption].
      bsimpl.
      now reflexivity.
    - econstructor.
      all: gen_typing.
  Qed.

  Lemma id_subst wl (Γ : context) :
    [|- Γ]< wl > ->
    [Γ |-s tRel : Γ]< wl >.
  Proof.
    induction 1.
    all: econstructor.
    - eapply well_subst_ext.
      2: now eapply well_subst_up.
      now asimpl.
    - eapply typing_meta_conv.
      1: now do 2 econstructor.
      cbn ; now renamify.
  Qed.

  Lemma subst_refl wl (Γ Δ : context) σ :
    [Γ |-s σ : Δ]< wl > ->
    [Γ |-s σ ≅ σ : Δ]< wl >.
  Proof.
    induction 1.
    all: econstructor ; tea.
    now eapply TermRefl.
  Qed.

  Theorem typing_subst1 wl Γ T :
  (forall (t : term), [Γ |- t : T]< wl > ->
    forall (A : term), [Γ,, T |- A]< wl > -> [Γ |- A[t..]]< wl >) ×
  (forall (t : term), [Γ |- t : T]< wl > ->
    forall (A u : term), [Γ,, T |- u : A]< wl > -> [Γ |- u[t..] : A[t..]]< wl >) ×
  (forall (t t' : term), [Γ |- t ≅ t' : T]< wl > ->
    forall (A B : term), [Γ,, T |- A ≅ B]< wl > -> [Γ |- A[t..] ≅ B[t'..]]< wl >) ×
  (forall (t t' : term), [Γ |- t ≅ t' : T]< wl > ->
    forall (A u v : term), [Γ,, T |- u ≅ v : A]< wl > -> [Γ |- u[t..] ≅ v[t'..] : A[t..]]< wl >).
  Proof.
    repeat match goal with |- _ × _ => split end.
    all: intros * Ht * Hty.
    all: assert ([|- Γ]< wl >) by gen_typing.
    all: assert ([Γ |-s tRel : Γ]< wl >) as Hsubst by now eapply id_subst.
    3-4: apply subst_refl in Hsubst.
    all: eapply typing_subst ; tea.
    all: econstructor ; cbn ; refold ; now asimpl.
  Qed.

  Theorem typing_substmap1 wl Γ T :
  (forall (t : term), [Γ ,, T |- t : T⟨↑⟩]< wl > ->
    forall (A : term), [Γ,, T |- A]< wl > -> 
      [Γ,, T |- A[t]⇑]< wl >) ×
  (forall (t : term), [Γ ,, T |- t : T⟨↑⟩]< wl > ->
    forall (A u : term), [Γ,, T |- u : A]< wl > -> 
      [Γ,, T |- u[t]⇑ : A[t]⇑]< wl >) ×
  (forall (t t' : term), [Γ ,, T |- t ≅ t' : T⟨↑⟩]< wl > ->
    forall (A B : term), [Γ,, T |- A ≅ B]< wl > ->
      [Γ,, T |- A[t]⇑ ≅ B[t']⇑]< wl >) ×
  (forall (t t' : term), [Γ ,, T |- t ≅ t' : T⟨↑⟩]< wl > ->
    forall (A u v : term), [Γ,, T |- u ≅ v : A]< wl > -> 
      [Γ,, T |- u[t]⇑ ≅ v[t']⇑ : A[t]⇑]< wl >).
  Proof.
    repeat match goal with |- _ × _ => split end.
    all: intros * Ht * Hty.
    all: assert ([|- Γ,, T]< wl > × [|- Γ]< wl >) as [] by (split; repeat boundary).
    all : assert (Hsubst : [Γ ,, T |-s ↑ >> tRel : Γ]< wl >)
            by (change (?x >> ?y) with y⟨x⟩; eapply well_subst_up; [boundary| now eapply id_subst]).
    3-4: apply subst_refl in Hsubst.
    all: eapply typing_subst ; tea.
    all: econstructor ; cbn ; refold; bsimpl; try rewrite <- rinstInst'_term; tea.
  Qed.

  Lemma conv_well_subst1 (wl : wfLCon) (Γ : context) A A' :
    [Γ |- A]< wl > ->
    [Γ |- A']< wl > ->
    [Γ |- A ≅ A']< wl > ->
    [Γ,, A |-s tRel : Γ,, A']< wl >.
  Proof.
    intros HA HA' Hconv.
    econstructor.
    - change (↑ >> tRel) with (tRel⟨↑⟩).
      eapply well_subst_up ; tea.
      now eapply id_subst ; gen_typing.
    - refold.
      eapply wfTermConv.
      1: constructor; [gen_typing|now econstructor].
      rewrite <- rinstInst'_term; do 2 erewrite <- wk1_ren_on; eapply typing_wk; tea.
      gen_typing.
  Qed.

  Theorem stability1 (wl : wfLCon) (Γ : context) A A' :
    [Γ |- A]< wl > ->
    [Γ |- A']< wl > ->
    [Γ |- A ≅ A']< wl > ->
    (forall (T : term), [Γ,, A' |-[de] T]< wl > -> [Γ,, A |-[de] T]< wl >)
    × (forall (T t : term), [Γ,, A' |-[ de ] t : T]< wl > -> [Γ,, A |-[de] t : T]< wl >)
    × (forall (T T' : term), [Γ,, A' |-[ de ] T ≅ T']< wl > -> [Γ,, A |-[de] T ≅ T']< wl >)
    × (forall (T t u : term),
          [Γ,, A' |-[ de ] t ≅ u : T]< wl > -> [Γ,, A |-[de] t ≅ u : T]< wl >).
  Proof.
    intros * ? ? Hconv.
    eapply (conv_well_subst1 _) in Hconv ; tea.
    pose proof (Hconv' := Hconv).
    apply subst_refl in Hconv'.
    assert [|- Γ,, A]< wl > by gen_typing.
    repeat match goal with |- _ × _ => split end.
    all: intros * Hty.
    all: eapply typing_subst in Hty ; tea.
    all: repeat (rewrite idSubst_term in Hty ; [..|reflexivity]).
    all: eassumption.
  Qed.

End MoreSubst.

Lemma elimSuccHypTy_ty wl Γ P :
  [|- Γ]< wl > ->
  [Γ,, tNat |- P]< wl > ->
  [Γ |-[ de ] elimSuccHypTy P]< wl >.
Proof.
  intros HΓ HP.
  unfold elimSuccHypTy.
  econstructor.
  1: now econstructor.
  eapply wft_simple_arr.
  1: now eapply HP.
  eapply typing_subst.
  - now eapply HP.
  - boundary.
  - econstructor.
    + bsimpl.
      eapply well_subst_ext.
      2: eapply well_subst_up.
      3: eapply id_subst ; tea.
      2: now econstructor.
      now bsimpl.
    + cbn.
      econstructor.
      eapply typing_meta_conv.
      1: now do 2 econstructor ; tea ; econstructor.
      reflexivity.
Qed.

Lemma elimSuccHypTy_conv wl Γ P P' :
  [|- Γ]< wl > ->
  [Γ,, tNat |- P]< wl > ->
  [Γ,, tNat |- P ≅ P' ]< wl > ->
  [Γ |- elimSuccHypTy P ≅ elimSuccHypTy P']< wl >.
Proof.
  intros.
  unfold elimSuccHypTy.
  constructor.
  2: constructor.
  1-2: now constructor.
  eapply convty_simple_arr; tea.
  eapply typing_substmap1; tea.
  do 2 constructor ; unshelve refine (wfVar _ _ (in_here _ _)).
  constructor; boundary.
Qed.

Lemma conv_well_subst wl (Γ Δ : context) :
  [|- Γ]< wl > ->
  [ |- Γ ≅ Δ]< wl > ->
  [Γ |-s tRel : Δ]< wl >.
Proof.
  intros HΓ.
  induction 1 as [| * ? HA] in HΓ |- *.
  - now econstructor.
  - assert [Γ |- A]< wl > by now inversion HΓ.
    assert [|- Γ]< wl > by now inversion HΓ.
    econstructor ; tea.
    + eapply well_subst_ext, well_subst_up ; eauto.
      reflexivity.
    + eapply wfTermConv.
      1: econstructor; [gen_typing| now econstructor].
      rewrite <- rinstInst'_term; do 2 erewrite <- wk1_ren_on.
      now eapply typing_wk.
Qed.

(* Stability and symmetry with redundant hypothesis on the well-formed contexts *)

Section Stability0.

  Let PCon (wl : wfLCon) (Γ : context) := True.
  Let PTy (wl : wfLCon) (Γ : context) (A : term) := forall Δ,
    [|-Δ]< wl > -> [|- Δ ≅ Γ]< wl > -> [Δ |- A]< wl >.
  Let PTm (wl : wfLCon) (Γ : context) (A t : term) := forall Δ,
    [|-Δ]< wl > -> [|- Δ ≅ Γ]< wl > -> [Δ |- t : A]< wl >.
  Let PTyEq (wl : wfLCon) (Γ : context) (A B : term) := forall Δ,
    [|-Δ]< wl > -> [|- Δ ≅ Γ]< wl > -> [Δ |- A ≅ B]< wl >.
  Let PTmEq (wl : wfLCon) (Γ : context) (A t u : term) := forall Δ,
    [|-Δ]< wl > -> [|- Δ ≅ Γ]< wl > -> [Δ |- t ≅ u : A]< wl >.

  Theorem stability0 (wl : wfLCon) : WfDeclInductionConcl PCon PTy PTm PTyEq PTmEq wl.
  Proof.
    red; prod_splitter; intros Γ * Hty; red.
    1: easy.
    all: intros ?? Hconv; eapply (conv_well_subst _) in Hconv ; tea.
    all: pose proof (Hconv' := Hconv); apply  subst_refl in Hconv'.
    all: eapply typing_subst in Hty; tea.
    all: repeat (rewrite idSubst_term in Hty ; [..|reflexivity]).
    all: eassumption.
  Qed.

  Definition convCtxSym0 {wl Γ Δ} : [|- Δ]< wl > -> [|-Γ]< wl > -> [|- Δ ≅ Γ]< wl > -> [|- Γ ≅ Δ]< wl >.
  Proof.
    induction 3.
    all: constructor; inversion H; inversion H0; subst; refold.
    1: now eauto.
    eapply stability0 ; tea.
    1: now symmetry.
    now eauto.
  Qed.

End Stability0.
