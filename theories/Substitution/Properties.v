From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations LContexts Context NormalForms Weakening GenericTyping Monad LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Irrelevance Escape Reflexivity Weakening Neutral Induction Monotonicity.
From LogRel.Substitution Require Import Irrelevance.

Set Universe Polymorphism.

Section Properties.
Context `{GenericTypingProperties}.


Lemma wellformedSubst {wl Γ σ Δ} (VΓ : [||-v Γ]< wl >) (wfΔ : [|- Δ]< wl >) :
  [Δ ||-v σ : Γ | VΓ| wfΔ]< wl > -> [Δ |-s σ : Γ ]< wl >.
Proof.
  revert σ; pattern Γ, VΓ; apply validity_rect; clear Γ VΓ.
  - intros. apply well_sempty.
  - intros * ih σ [tl hd].
    eapply well_scons.
    + now apply ih.
    + now Wescape.
Qed.

Lemma wellformedSubstEq {wl Γ σ σ' Δ} (VΓ : [||-v Γ]< wl >) (wfΔ : [|- Δ]< wl >) (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ]< wl >) :
  [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | Vσ]< wl > -> [Δ |-s σ ≅ σ' : Γ]< wl >.
Proof.
  revert σ σ' Vσ; pattern Γ, VΓ; apply validity_rect; clear Γ VΓ.
  - intros. apply conv_sempty.
  - intros * ih ??? [tl hd]. apply conv_scons.
    + now eapply ih.
    + now Wescape.
Qed.

Lemma consSubstS {wl Γ σ t l A Δ} (VΓ : [||-v Γ]< wl >) (wfΔ : [|- Δ]< wl >)
  (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ]< wl >) (VA : [Γ ||-v<l> A | VΓ]< wl >)
  (Vt : W[ Δ ||-<l> t : A[σ] | validTy VA wfΔ Vσ]< wl >) :
  [Δ ||-v (t .: σ) : Γ ,, A | validSnoc VΓ VA | wfΔ]< wl >.
Proof.  unshelve econstructor; eassumption. Defined.


Lemma consSubstSEq {wl Γ σ σ' t l A Δ} (VΓ : [||-v Γ]< wl >) (wfΔ : [|- Δ]< wl >)
  (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ]< wl >)
  (Vσσ' : [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | Vσ]< wl >)
  (VA : [Γ ||-v<l> A | VΓ]< wl >)
  (Vt : W[Δ ||-<l> t : A[σ] | validTy VA wfΔ Vσ]< wl >) :
  [Δ ||-v (t .: σ) ≅  (t .: σ') : Γ ,, A | validSnoc VΓ VA | wfΔ | consSubstS VΓ wfΔ Vσ VA Vt]< wl >.
Proof.
  unshelve econstructor.
  1: eassumption.
  eapply WreflLRTmEq ; exact Vt.
Qed.

Lemma consSubstSEq' {wl Γ σ σ' t u l A Δ} (VΓ : [||-v Γ]< wl >) (wfΔ : [|- Δ]< wl >)
  (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ]< wl >)
  (Vσσ' : [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | Vσ]< wl >)
  (VA : [Γ ||-v<l> A | VΓ]< wl >)
  (Vt : W[Δ ||-<l> t : A[σ] | validTy VA wfΔ Vσ]< wl >)
  (Vtu : W[Δ ||-<l> t ≅ u : A[σ] | validTy VA wfΔ Vσ]< wl >) :
  [Δ ||-v (t .: σ) ≅  (u .: σ') : Γ ,, A | validSnoc VΓ VA | wfΔ | consSubstS VΓ wfΔ Vσ VA Vt]< wl >.
Proof.
  unshelve econstructor; tea.
Qed.  


Lemma consSubstSvalid {wl Γ σ t l A Δ} {VΓ : [||-v Γ]< wl >} {wfΔ : [|- Δ]< wl >}
  (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ]< wl >) {VA : [Γ ||-v<l> A | VΓ]< wl >}
  (Vt : [ Γ ||-v<l> t : A | VΓ | VA]< wl >) :
  [Δ ||-v (t[σ] .: σ) : Γ ,, A | validSnoc VΓ VA | wfΔ]< wl >.
Proof. unshelve eapply consSubstS; tea; now eapply validTm. Defined.

Set Printing Primitive Projection Parameters.

Lemma consSubstSEqvalid {wl Γ σ σ' t l A Δ} {VΓ : [||-v Γ]< wl >} {wfΔ : [|- Δ]< wl >}
  (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ]< wl >)
  (Vσ' : [Δ ||-v σ' : Γ | VΓ | wfΔ]< wl >) 
  (Vσσ' : [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | Vσ]< wl >)
  {VA : [Γ ||-v<l> A | VΓ]< wl >}
  (Vt : [Γ ||-v<l> t : A | VΓ | VA]< wl >) :
  [Δ ||-v (t[σ] .: σ) ≅  (t[σ'] .: σ') : Γ ,, A | validSnoc VΓ VA | wfΔ | consSubstSvalid Vσ Vt]< wl >.
Proof.
  unshelve econstructor; intros; tea.
  now apply validTmExt.
Qed.

Lemma wkSubstS {wl Γ} (VΓ : [||-v Γ]< wl >) : 
  forall {σ  Δ Δ'}  (wfΔ : [|- Δ]< wl >) (wfΔ' : [|- Δ']< wl >) (ρ : Δ' ≤ Δ),
  [Δ ||-v σ : Γ | VΓ | wfΔ]< wl > -> [Δ' ||-v σ ⟨ ρ ⟩ : Γ | VΓ | wfΔ']< wl >.
Proof.
  pattern Γ, VΓ ; apply validity_rect; clear Γ VΓ.
  - constructor.
  - intros * ih * [tl hd]. unshelve econstructor.
    + eapply ih; eassumption.
    + eapply WLRTmRedIrrelevant'.
      2: eapply (WwkTerm _ wfΔ') ; exact hd.
      now asimpl.
Defined.


Lemma wkSubstSEq {wl Γ} (VΓ : [||-v Γ]< wl >) :
  forall {σ σ' Δ Δ'}  (wfΔ : [|- Δ]< wl >) (wfΔ' : [|- Δ']< wl >) (ρ : Δ' ≤ Δ)
  (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ]< wl >),
  [Δ  ||-v σ ≅ σ' : Γ | VΓ | wfΔ | Vσ]< wl > ->
  [Δ' ||-v σ ⟨ ρ ⟩ ≅ σ' ⟨ ρ ⟩ : Γ | VΓ | wfΔ' | wkSubstS VΓ wfΔ wfΔ' ρ Vσ]< wl >.
Proof.
  pattern Γ, VΓ; apply validity_rect; clear Γ VΓ.
  - constructor.
  - intros * ih * [tl hd]; unshelve econstructor.
    + eapply ih ; eassumption.
    + eapply WLRTmEqIrrelevant'.
      2: eapply (WwkTermEq _ wfΔ') ; exact hd.
      now asimpl.
Qed.

Lemma wk1SubstS {wl Γ σ Δ F} (VΓ : [||-v Γ]< wl >) (wfΔ : [|- Δ]< wl >) (wfF : [Δ |- F]< wl >) :
  [Δ ||-v σ : Γ | VΓ | wfΔ ]< wl > ->
  [Δ ,, F ||-v σ ⟨ @wk1 Δ F ⟩ : Γ | VΓ | wfc_cons wfΔ wfF]< wl >.
Proof. eapply wkSubstS. Defined.

Lemma wk1SubstSEq {wl Γ σ σ' Δ F} (VΓ : [||-v Γ]< wl >)
  (wfΔ : [|- Δ]< wl >) (wfF : [Δ |- F]< wl >)
  (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ ]< wl >) :
  [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | Vσ]< wl > ->
  let ρ := @wk1 Δ F in
  [Δ ,, F ||-v σ ⟨ ρ ⟩ ≅ σ' ⟨ ρ ⟩ : Γ | VΓ | wfc_cons wfΔ wfF | wk1SubstS VΓ wfΔ wfF Vσ]< wl >.
Proof.
  intro vσσ'. eapply wkSubstSEq ; eassumption.
Qed.

Lemma consWkSubstS {wl Γ F Δ Ξ σ a l VΓ wfΔ } VF
  (ρ : Ξ ≤ Δ) wfΞ {RF}:
  [Δ ||-v σ : Γ | VΓ | wfΔ]< wl > ->
  W[Ξ ||-<l> a : F[σ]⟨ρ⟩ | RF]< wl > ->
  [Ξ ||-v (a .: σ⟨ρ⟩) : Γ,, F | validSnoc (l:=l) VΓ VF | wfΞ]< wl >.
Proof.
  intros. unshelve eapply consSubstS.  2: Wirrelevance.
  now eapply wkSubstS.
Qed.

Lemma consWkSubstSEq' {wl Γ Δ Ξ A σ σ' a b l} {VΓ : [||-v Γ]< wl >} {wfΔ : [|- Δ]< wl >}
  (VA : [Γ ||-v<l> A | VΓ]< wl >)
  (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ]< wl >)
  (Vσσ' : [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | Vσ]< wl >)
  (ρ : Ξ ≤ Δ) wfΞ {RA}
  (Ra : W[Ξ ||-<l> a : A[σ]⟨ρ⟩ | RA]< wl >)
  (Rab : W[Ξ ||-<l> a ≅ b : A[σ]⟨ρ⟩ | RA]< wl >) 
  (Vawkσ := consWkSubstS VA ρ wfΞ Vσ Ra) :
  [Ξ ||-v (a .: σ⟨ρ⟩) ≅  (b .: σ'⟨ρ⟩) : Γ ,, A | validSnoc VΓ VA | wfΞ | Vawkσ]< wl >.
Proof.
  unshelve eapply consSubstSEq'.
  - unshelve eapply irrelevanceSubstEq.
    4: now eapply wkSubstSEq.
    tea.
  - Wirrelevance0; tea. now bsimpl.
Qed.  


Lemma liftSubstS {wl Γ σ Δ lF F} (VΓ : [||-v Γ]< wl >) (wfΔ : [|- Δ]< wl >)
  (VF : [Γ ||-v<lF> F | VΓ]< wl >)
  (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ ]< wl >) :
  let VΓF := validSnoc VΓ VF in
  let ρ := @wk1 Δ F[σ] in
  let wfΔF := wfc_cons wfΔ (Wescape (validTy VF wfΔ Vσ)) in
  [Δ ,, F[σ] ||-v (tRel 0 .: σ ⟨ ρ ⟩) : Γ ,, F | VΓF | wfΔF ]< wl >.
Proof.
  intros; unshelve econstructor.
  - now eapply wk1SubstS.
  - eapply Wvar0 ; unfold ρ; [now bsimpl|].
    now eapply Wescape, VF.
Defined.

Lemma liftSubstSrealign {wl Γ σ σ' Δ lF F} {VΓ : [||-v Γ]< wl >} {wfΔ : [|- Δ]< wl >}
  (VF : [Γ ||-v<lF> F | VΓ]< wl >)
  {Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ ]< wl >} :
  let VΓF := validSnoc VΓ VF in
  let ρ := @wk1 Δ F[σ]  in
  let wfΔF := wfc_cons wfΔ (Wescape (validTy VF wfΔ Vσ)) in
  [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | Vσ]< wl > ->
  [Δ ||-v σ' : Γ | VΓ | wfΔ ]< wl > ->
  [Δ ,, F[σ] ||-v (tRel 0 .: σ'⟨ρ⟩) : Γ ,, F | VΓF | wfΔF]< wl >.
Proof.
  intros; unshelve econstructor.
  + now eapply wk1SubstS.
  + cbn.
    assert [Δ,, F[σ] |-[ ta ] tRel 0 : F[S >> (tRel 0 .: σ'⟨ρ⟩)]]< wl >.
    { replace F[_ >> _] with F[σ']⟨S⟩ by (unfold ρ; now bsimpl).
      eapply ty_conv. 1: apply (ty_var wfΔF (in_here _ _)).
      cbn; renToWk. eapply convty_wk; tea.
      eapply WescapeEq;  unshelve eapply validTyExt; cycle 3; tea. }
    apply WneuTerm; tea.
    - apply convneu_var; tea.
Qed.

Lemma liftSubstS' {wl Γ σ Δ lF F} {VΓ : [||-v Γ]< wl >} {wfΔ : [|- Δ]< wl >}
  (VF : [Γ ||-v<lF> F | VΓ]< wl >)
  (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ ]< wl >) :
  let VΓF := validSnoc VΓ VF in
  let wfΔF := wfc_cons wfΔ (Wescape (validTy VF wfΔ Vσ)) in
  [Δ ,, F[σ] ||-v up_term_term σ : Γ ,, F | VΓF | wfΔF ]< wl >.
Proof.
  eapply irrelevanceSubstExt.
  2: eapply liftSubstS.
  intros ?; now bsimpl.
Qed.

Lemma liftSubstSEq {wl Γ σ σ' Δ lF F} (VΓ : [||-v Γ]< wl >) (wfΔ : [|- Δ]< wl >)
  (VF : [Γ ||-v<lF> F | VΓ]< wl >)
  (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ ]< wl >) :
  let VΓF := validSnoc VΓ VF in
  let ρ := @wk1 Δ F[σ] in
  let wfΔF := wfc_cons wfΔ (Wescape (validTy VF wfΔ Vσ)) in
  let Vliftσ := liftSubstS VΓ wfΔ VF Vσ in
  [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | Vσ]< wl > ->
  [Δ ,, F[σ] ||-v (tRel 0 .: σ ⟨ ρ ⟩) ≅ (tRel 0 .: σ' ⟨ ρ ⟩) : Γ ,, F | VΓF | wfΔF | Vliftσ]< wl >.
Proof.
  intros; unshelve econstructor.
  + now apply wk1SubstSEq.
  + apply WreflLRTmEq; exact (validHead Vliftσ).
Qed.

Lemma liftSubstSEq' {wl Γ σ σ' Δ lF F} {VΓ : [||-v Γ]< wl >} {wfΔ : [|- Δ]< wl >}
  (VF : [Γ ||-v<lF> F | VΓ]< wl >)
  {Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ ]< wl >} :
  let VΓF := validSnoc VΓ VF in
  let ρ := wk_up F (@wk_id Γ) in
  let wfΔF := wfc_cons wfΔ (Wescape (validTy VF wfΔ Vσ)) in
  let Vliftσ := liftSubstS' VF Vσ in
  [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | Vσ]< wl > ->
  [Δ ,, F[σ] ||-v up_term_term σ ≅ up_term_term σ' : Γ ,, F | VΓF | wfΔF | Vliftσ]< wl >.
Proof.
  intros.
  eapply irrelevanceSubstEq.
  unshelve eapply irrelevanceSubstEqExt.
  6: now eapply liftSubstSEq.
  all: intros ?; now bsimpl.
  Unshelve. all: tea.
Qed.

Lemma liftSubstSrealign' {wl Γ σ σ' Δ lF F} {VΓ : [||-v Γ]< wl >} {wfΔ : [|- Δ]< wl >}
  (VF : [Γ ||-v<lF> F | VΓ]< wl >)
  {Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ ]< wl >} :
  let VΓF := validSnoc VΓ VF in
  let ρ := wk_up F (@wk_id Γ) in
  let wfΔF := wfc_cons wfΔ (Wescape (validTy VF wfΔ Vσ)) in
  [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | Vσ]< wl > ->
  [Δ ||-v σ' : Γ | VΓ | wfΔ ]< wl > ->
  [Δ ,, F[σ] ||-v up_term_term σ' : Γ ,, F | VΓF | wfΔF]< wl >.
Proof.
  intros.
  eapply irrelevanceSubstExt.
  2: eapply liftSubstSrealign; tea.
  intros ?; now bsimpl.
Qed.

Lemma wk1ValidTy {wl Γ lA A lF F} {VΓ : [||-v Γ]< wl >} (VF : [Γ ||-v<lF> F | VΓ]< wl >) :
  [Γ ||-v<lA> A | VΓ]< wl > -> 
  [Γ ,, F ||-v<lA> A ⟨ @wk1 Γ F ⟩ | validSnoc VΓ VF ]< wl >.
Proof.
  assert (forall σ, (A ⟨@wk1 Γ F⟩)[σ] = A[↑ >> σ]) as h by (intros; asimpl; now rewrite wk1_ren) ;
  intros [VA VAext]; unshelve econstructor.
  - abstract (intros * [tl _]; rewrite h; exact (VA _ _ wfΔ tl)).
  - intros * [tl _] [tleq _].
    rewrite (h σ'); unshelve eapply WLRTyEqSym.
    2: eapply VA; eassumption.
    rewrite (h σ).
    eapply VAext. 1: exact (validTail vσ).
    eapply symmetrySubstEq. eassumption.
Qed.

Lemma wk1ValidTyEq {wl Γ lA A B lF F} {VΓ : [||-v Γ]< wl >} (VF : [Γ ||-v<lF> F | VΓ]< wl >) 
  {VA : [Γ ||-v<lA> A | VΓ]< wl >} :
  [Γ ||-v<lA> A ≅ B | VΓ | VA]< wl > -> 
  [Γ ,, F ||-v<lA> A ⟨ @wk1 Γ F ⟩ ≅ B ⟨ @wk1 Γ F ⟩ | validSnoc VΓ VF | wk1ValidTy VF VA]< wl >.
Proof.
  assert (forall A σ, (A ⟨@wk1 Γ F⟩)[σ] = A[↑ >> σ]) as h by (intros; asimpl; now rewrite wk1_ren).
  intros []; constructor; intros.
  Wirrelevance0 ; [symmetry ; now apply h | rewrite (h B) ].
  unshelve eapply validTyEq ; [assumption | now eapply validTail ].
Qed.

Lemma wk1ValidTm {wl Γ lA t A lF F} {VΓ : [||-v Γ]< wl >}
  (VF : [Γ ||-v<lF> F | VΓ]< wl >)
  (VA : [Γ ||-v<lA> A | VΓ]< wl >)
  (Vt : [Γ ||-v<lA> t : A | VΓ | VA]< wl >) (ρ := @wk1 Γ F):
  [Γ,, F ||-v<lA> t⟨ρ⟩ : A⟨ρ⟩ | validSnoc VΓ VF | wk1ValidTy VF VA]< wl >.
Proof.
  assert (forall A σ, (A ⟨@wk1 Γ F⟩)[σ] = A[↑ >> σ]) as h by (intros; asimpl; now rewrite wk1_ren).
  constructor; intros; repeat rewrite h.
  - instValid (validTail Vσ) ; now Wirrelevance.
  - instValidExt (validTail Vσ') (eqTail Vσσ') ; now Wirrelevance. 
Qed.

Lemma wk1ValidTmEq {wl Γ lA t u A lF F} {VΓ : [||-v Γ]< wl >}
  (VF : [Γ ||-v<lF> F | VΓ]< wl >)
  (VA : [Γ ||-v<lA> A | VΓ]< wl >)
  (Vtu : [Γ ||-v<lA> t ≅ u : A | VΓ | VA]< wl >) (ρ := @wk1 Γ F):
  [Γ,, F ||-v<lA> t⟨ρ⟩ ≅ u⟨ρ⟩ : A⟨ρ⟩ | validSnoc VΓ VF | wk1ValidTy VF VA]< wl >.
Proof.
  assert (forall A σ, (A ⟨@wk1 Γ F⟩)[σ] = A[↑ >> σ]) as h by (intros; asimpl; now rewrite wk1_ren).
  constructor; intros ; repeat rewrite h.
  instValid (validTail Vσ); Wirrelevance.
  now rewrite h.
Qed.


Lemma embValidTy@{u i j k l} {wl Γ l l' A}
    {VΓ : [VR@{i j k l}| ||-v Γ]< wl >} (h : l << l')
    (VA : typeValidity@{u i j k l} wl Γ VΓ l A (*[Γ ||-v<l> A |VΓ]< wl >*)) :
    typeValidity@{u i j k l} wl Γ VΓ l' A (*[Γ ||-v<l'> A |VΓ]< wl >*).
Proof.
  unshelve econstructor.
  - intros ??? Vσ; destruct (validTy VA _  Vσ) as [d pack] ; exists d ; intros.
    exists (pack wl' Ho) ; eapply LR_embedding ; tea.
    now eapply pack.
  - intros ; cbn. Wirrelevance0 ; [ reflexivity | unshelve eapply validTyExt].
  3: eassumption.
  all: tea.
Defined.

Lemma embValidTyOne @{u i j k l} {wl Γ l A}
    {VΓ : [VR@{i j k l}| ||-v Γ]< wl >}
    (VA : typeValidity@{u i j k l} wl Γ VΓ l A (*[Γ ||-v<l> A |VΓ]*)) :
    typeValidity@{u i j k l} wl Γ VΓ one A (*[Γ ||-v<one> A |VΓ]*).
Proof.
  destruct l; tea; now eapply (embValidTy Oi).
Defined.

Lemma soundCtxId {wl Γ} (VΓ : [||-v Γ]< wl >) :
  ∑ wfΓ : [|- Γ]< wl >, [Γ ||-v tRel : Γ | VΓ | wfΓ]< wl >.
Proof.
  enough (G : ∑ Δ (e : Δ = Γ) (wfΔ : [|-Δ]< wl >), [VΓ |Δ ||-v tRel : Γ | wfΔ]< wl >).
  1: now destruct G as [? [-> ?]].
  pattern Γ, VΓ; apply validity_rect; clear Γ VΓ.
  - exists ε, eq_refl, wfc_nil; constructor.
  - intros * [Δ [e [wfΔ Vid]]].
    exists (Δ,, A[tRel]); unshelve eexists. 
    1: asimpl; now rewrite e.
    unshelve eexists.
    + apply wfc_cons; tea.
      eapply Wescape.
      apply (validTy VA wfΔ Vid).
    + eapply irrelevanceSubstExt.
      2: eapply irrelevanceSubst; now unshelve eapply liftSubstS.
      intros []; [| bsimpl]; reflexivity.
Qed.

Definition soundCtx {wl Γ} (VΓ : [||-v Γ]< wl >) : [|-Γ]< wl > := (soundCtxId VΓ).π1.

Definition idSubstS {wl Γ} (VΓ : [||-v Γ]< wl >) : [Γ ||-v tRel : Γ | VΓ | _]< wl > := (soundCtxId VΓ).π2.

Lemma reflIdSubstS {wl Γ} (VΓ : [||-v Γ]< wl >) : [Γ ||-v tRel ≅ tRel : Γ | VΓ | _ | idSubstS VΓ]< wl >.
Proof.  apply reflSubst. Qed.

Lemma substS_wk {wl Γ Δ} (ρ : Δ ≤ Γ) :
  forall (VΓ : [||-v Γ]< wl >)
  (VΔ : [||-v Δ]< wl >) 
  {Ξ σ} (wfΞ : [|- Ξ]< wl >), [VΔ | Ξ ||-v σ : _ | wfΞ]< wl > -> [VΓ | Ξ ||-v ρ >> σ : _ | wfΞ]< wl >.
Proof.
  destruct ρ as [? wwk]; induction wwk.
  + intros; rewrite (invValidityEmpty VΓ); constructor.
  + intros.
    pose proof (invValiditySnoc VΔ) as [? [? [? eq]]].
    rewrite eq in X; cbn in X; inversion X.
    eapply irrelevanceSubstExt.
    1: rewrite <- (scons_eta' σ); reflexivity.
    cbn. asimpl.
    now eapply IHwwk.
  + intros.
    pose proof (invValiditySnoc VΔ) as [? [? [? eq]]].
    rewrite eq in X; cbn in X; inversion X.
    eapply irrelevanceSubstExt.
    1:{ rewrite <- (scons_eta' σ); cbn; unfold up_ren; rewrite scons_comp'; cbn. reflexivity. }
    asimpl.
    pose proof (invValiditySnoc VΓ) as [? [? [? eq']]].
    rewrite eq'.
    unshelve eapply consSubstS.
    * now eapply IHwwk.
    * Wirrelevance.
Defined.

Lemma substSEq_wk {wl Γ Δ} (ρ : Δ ≤ Γ) :
  forall (VΓ : [||-v Γ]< wl >)
  (VΔ : [||-v Δ]< wl >) 
  Ξ σ σ' (wfΞ : [|- Ξ]< wl >)
  (Vσ : [VΔ | Ξ ||-v σ : _ | wfΞ]< wl >),
  [VΔ | Ξ ||-v σ' : _ | wfΞ]< wl > -> 
  [VΔ | Ξ ||-v σ ≅ σ' : _ | wfΞ | Vσ]< wl > -> 
  [VΓ | Ξ ||-v ρ >> σ ≅ ρ >> σ' : _ | wfΞ | substS_wk ρ VΓ VΔ wfΞ Vσ]< wl >.
Proof.
  destruct ρ as [? wwk]; induction wwk.
  + intros; rewrite (invValidityEmpty VΓ); constructor.
  + intros.
    pose proof (invValiditySnoc VΔ) as [? [? [? eq]]].
    revert Vσ X X0; rewrite eq; intros Vσ Vσ' Vσσ'.
    cbn; asimpl; eapply irrelevanceSubstEq.
    unshelve eapply IHwwk; tea.
    1,2: now eapply validTail.
    now eapply eqTail.
    Unshelve. tea.
+ intros ??????.
  set (ρ0 := {| well_wk := _ |}); unfold ρ0.
  pose proof (invValiditySnoc VΔ) as [? [VΓ0 [? eq]]].
  pose proof (invValiditySnoc VΓ) as [? [VΔ0 [? eqΓ]]].
  rewrite eq; intros Vσ Vσ' Vσσ'.
  assert (subst_eq : forall τ : nat -> term, τ var_zero .: (ρ >> ↑ >> τ) =1 (0 .: ρ >> S) >> τ).
  1:{ intros τ;  asimpl; reflexivity. }
  pose proof (v := substS_wk ρ0 VΓ _ wfΞ Vσ).
  cbn; asimpl ; eapply irrelevanceSubstEq; unshelve eapply irrelevanceSubstEqExt.
  2,5: apply subst_eq.
  - eapply irrelevanceSubstExt.
    1: symmetry; apply subst_eq.
    exact v.
  - eapply irrelevanceSubstEq.
    eapply consSubstSEq'.
    * exact (IHwwk VΔ0 VΓ0 Ξ (↑ >> σ) (↑ >> σ') wfΞ (validTail Vσ) (validTail Vσ') (eqTail Vσσ')).
    * Wirrelevance0. 
      2: now eapply eqHead. 
      now asimpl.
    Unshelve. 2: tea.
    rewrite eqΓ in v.
    Wirrelevance0 ; [reflexivity | ].
    eapply (validHead v).
Qed.

Lemma wkValidTy {l wl Γ Δ A} (ρ : Δ ≤ Γ)
  (VΓ : [||-v Γ]< wl >)
  (VΔ : [||-v Δ]< wl >)
  (VA : [Γ ||-v<l> A | VΓ]< wl >) :
  [Δ ||-v<l> A⟨ρ⟩ | VΔ]< wl >.
Proof.
  assert (h : forall σ, A⟨ρ⟩[σ] = A[ ρ >> σ]) by (intros; now asimpl).
  unshelve econstructor.
  - intros; rewrite h.
    eapply validTy; tea.
    now eapply substS_wk.
  - intros; Wirrelevance0; rewrite h; [reflexivity|].
    eapply validTyExt.
    1: now eapply substS_wk.
    now eapply substSEq_wk.
    Unshelve. 2,3: tea.
Qed.

Lemma wkValidTm {l wl Γ Δ A t} (ρ : Δ ≤ Γ)
  (VΓ : [||-v Γ]< wl >)
  (VΔ : [||-v Δ]< wl >)
  (VA : [Γ ||-v<l> A | VΓ]< wl >)
  (Vt : [Γ ||-v<l> t : A | VΓ | VA]< wl >) :
  [Δ ||-v<l> t⟨ρ⟩ : A⟨ρ⟩ | VΔ | wkValidTy ρ VΓ VΔ VA]< wl >.
Proof.
  assert (hA : forall σ, A⟨ρ⟩[σ] = A[ρ >> σ]) by (intros; now asimpl).
  assert (ht : forall σ, t⟨ρ⟩[σ] = t[ρ >> σ]) by (intros; now asimpl).
  unshelve econstructor.
  - intros; rewrite ht.
    Wirrelevance0; [symmetry; apply hA|].
    eapply validTm, Vt.
  - intros; do 2 rewrite ht.
    Wirrelevance0; [symmetry; apply hA|].
    eapply validTmExt; [apply Vt|now eapply substS_wk|].
    now eapply substSEq_wk.
    Unshelve. all: tea.
    now eapply substS_wk.
Qed.

Lemma wkValidTyEq {l wl Γ Δ A B} (ρ : Δ ≤ Γ)
  (VΓ : [||-v Γ]< wl >)
  (VΔ : [||-v Δ]< wl >)
  (VA : [Γ ||-v<l> A | VΓ]< wl >)
  (VAB : [Γ ||-v<l> A ≅ B | VΓ | VA]< wl >) :
  [Δ ||-v<l> A⟨ρ⟩ ≅ B⟨ρ⟩ | VΔ | wkValidTy ρ VΓ VΔ VA]< wl >.
Proof.
  assert (h : forall A σ, A⟨ρ⟩[σ] = A[ ρ >> σ]) by (intros; now asimpl).
  unshelve econstructor; intros; Wirrelevance0; rewrite h; [reflexivity|].
  now eapply validTyEq.
  Unshelve. 1: tea.
    now eapply substS_wk.
Qed.




End Properties.
