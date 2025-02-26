From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations LContexts Context NormalForms Weakening GenericTyping Monad LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Irrelevance Escape Reflexivity Weakening Neutral Induction Monotonicity.
From LogRel.Substitution Require Import Irrelevance.

Set Universe Polymorphism.

Section Properties.
Context `{GenericTypingProperties}.


Lemma wellformedSubst {wl Γ σ Δ wl' f} (VΓ : [||-v Γ]< wl >) (wfΔ : [|- Δ]< wl' >) :
  [Δ ||-v σ : Γ | VΓ| wfΔ| f]< wl > -> [Δ |-s σ : Γ ]< wl' >.
Proof.
  revert σ; pattern Γ, VΓ; apply validity_rect; clear Γ VΓ.
  - intros. now apply well_sempty.
  - intros * ih σ ; cbn ; erewrite Hsub ; intros [tl hd].
    eapply well_scons.
    + now apply ih.
    + now Wescape.
Qed.

Lemma wellformedSubstEq {wl Γ σ σ' Δ wl' f}
  (VΓ : [||-v Γ]< wl >)
  (wfΔ : [|- Δ]< wl' >)
  (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ | f]< wl >) :
  [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | Vσ | f]< wl > ->
  [Δ |-s σ ≅ σ' : Γ]< wl' >.
Proof.
  revert σ σ' Vσ; pattern Γ, VΓ; apply validity_rect; clear Γ VΓ.
  - intros. apply conv_sempty.
  - intros * ih ??? ; cbn ; rewrite Hext ; intros [tl hd].
    apply conv_scons.
    + now eapply ih.
    + now Wescape.
Qed.

Lemma consSubstS {wl Γ σ t l A Δ wl' f} (VΓ : [||-v Γ]< wl >) (wfΔ : [|- Δ]< wl' >)
  (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ | f]< wl >) (VA : [Γ ||-v<l> A | VΓ]< wl >)
  (Vt : W[ Δ ||-<l> t : A[σ] | validTy VA f wfΔ Vσ]< wl' >) :
  [Δ ||-v (t .: σ) : Γ ,, A | validSnoc' VΓ VA | wfΔ | f]< wl >.
Proof.  unshelve econstructor; eassumption. Defined.


Lemma consSubstSEq {wl Γ σ σ' t l A Δ wl' f} (VΓ : [||-v Γ]< wl >) (wfΔ : [|- Δ]< wl' >)
  (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ| f ]< wl >)
  (Vσσ' : [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | Vσ| f ]< wl >)
  (VA : [Γ ||-v<l> A | VΓ]< wl >)
  (Vt : W[Δ ||-<l> t : A[σ] | validTy VA f wfΔ Vσ]< wl' >) :
  [Δ ||-v (t .: σ) ≅  (t .: σ') : Γ ,, A | validSnoc' VΓ VA | wfΔ | consSubstS VΓ wfΔ Vσ VA Vt| f]< wl >.
Proof.
  unshelve econstructor.
  1: eassumption.
  eapply WreflLRTmEq ; exact Vt.
Qed.

Lemma consSubstSEq' {wl Γ σ σ' t u l A Δ wl' f} (VΓ : [||-v Γ]< wl >) (wfΔ : [|- Δ]< wl' >)
  (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ| f ]< wl >)
  (Vσσ' : [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | Vσ| f ]< wl >)
  (VA : [Γ ||-v<l> A | VΓ]< wl >)
  (Vt : W[Δ ||-<l> t : A[σ] | validTy VA f wfΔ Vσ]< wl' >)
  (Vtu : W[Δ ||-<l> t ≅ u : A[σ] | validTy VA f wfΔ Vσ]< wl' >) :
  [Δ ||-v (t .: σ) ≅  (u .: σ') : Γ ,, A | validSnoc' VΓ VA | wfΔ | consSubstS VΓ wfΔ Vσ VA Vt | f]< wl >.
Proof.
  unshelve econstructor; tea.
Qed.  


Lemma consSubstSvalid {wl Γ σ t l A Δ wl' f} {VΓ : [||-v Γ]< wl >} {wfΔ : [|- Δ]< wl' >}
  (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ| f ]< wl >) {VA : [Γ ||-v<l> A | VΓ]< wl >}
  (Vt : [ Γ ||-v<l> t : A | VΓ | VA]< wl >) :
  [Δ ||-v (t[σ] .: σ) : Γ ,, A | validSnoc' VΓ VA | wfΔ | f]< wl >.
Proof. unshelve eapply consSubstS; tea; now eapply validTm. Defined.

Set Printing Primitive Projection Parameters.

Lemma consSubstSEqvalid {wl Γ σ σ' t l A Δ wl' f} {VΓ : [||-v Γ]< wl >} {wfΔ : [|- Δ]< wl' >}
  (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ| f ]< wl >)
  (Vσ' : [Δ ||-v σ' : Γ | VΓ | wfΔ| f ]< wl >) 
  (Vσσ' : [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | Vσ| f ]< wl >)
  {VA : [Γ ||-v<l> A | VΓ]< wl >}
  (Vt : [Γ ||-v<l> t : A | VΓ | VA]< wl >) :
  [Δ ||-v (t[σ] .: σ) ≅  (t[σ'] .: σ') : Γ ,, A | validSnoc' VΓ VA | wfΔ | consSubstSvalid Vσ Vt | f]< wl >.
Proof.
  unshelve econstructor; intros; tea.
  now apply validTmExt.
Qed.

Lemma wkSubstS {wl Γ} (VΓ : [||-v Γ]< wl >) : 
  forall {σ  Δ Δ' wl' f}  (wfΔ : [|- Δ]< wl' >) (wfΔ' : [|- Δ']< wl' >) (ρ : Δ' ≤ Δ),
  [Δ ||-v σ : Γ | VΓ | wfΔ| f ]< wl > -> [Δ' ||-v σ ⟨ ρ ⟩ : Γ | VΓ | wfΔ'| f ]< wl >.
Proof.
  pattern Γ, VΓ ; apply validity_rect; clear Γ VΓ.
  - intros ; cbn in * ; rewrite Hsub. now constructor.
  - intros * ih * ; cbn ; do 2 rewrite Hsub ; intros [tl hd].
    unshelve econstructor.
    + eapply ih; eassumption.
    + eapply WLRTmRedIrrelevant'.
      2: eapply (WwkTerm _ wfΔ') ; exact hd.
      now asimpl.
Defined.


Lemma wkSubstSEq {wl Γ} (VΓ : [||-v Γ]< wl >) :
  forall {σ σ' Δ Δ' wl' f}  (wfΔ : [|- Δ]< wl' >) (wfΔ' : [|- Δ']< wl' >) (ρ : Δ' ≤ Δ)
  (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ| f ]< wl >),
  [Δ  ||-v σ ≅ σ' : Γ | VΓ | wfΔ | Vσ| f ]< wl > ->
  [Δ' ||-v σ ⟨ ρ ⟩ ≅ σ' ⟨ ρ ⟩ : Γ | VΓ | wfΔ' | wkSubstS VΓ wfΔ wfΔ' ρ Vσ| f ]< wl >.
Proof.
  pattern Γ, VΓ; apply validity_rect; clear Γ VΓ.
  - intros ; cbn ; rewrite Hext ; now constructor.
  - intros * ih * ; cbn ; do 2 rewrite Hext ; intros [tl hd].
    rewrite Hsub ; cbn.
    unshelve econstructor.
    + unshelve eapply irrelevanceSubstEq.
      4: now eapply ih.
      eassumption.
    + eapply WLRTmEqIrrelevant'.
      2: eapply (WwkTermEq _ wfΔ') ; exact hd.
      now asimpl.
Qed.

Lemma wk1SubstS {wl Γ σ Δ F wl' f} (VΓ : [||-v Γ]< wl >) (wfΔ : [|- Δ]< wl' >) (wfF : [Δ |- F]< wl' >) :
  [Δ ||-v σ : Γ | VΓ | wfΔ | f ]< wl > ->
  [Δ ,, F ||-v σ ⟨ @wk1 Δ F ⟩ : Γ | VΓ | wfc_cons wfΔ wfF| f ]< wl >.
Proof. eapply wkSubstS. Defined.

Lemma wk1SubstSEq {wl Γ σ σ' Δ F wl' f} (VΓ : [||-v Γ]< wl >)
  (wfΔ : [|- Δ]< wl' >) (wfF : [Δ |- F]< wl' >)
  (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ | f ]< wl >) :
  [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | Vσ| f ]< wl > ->
  let ρ := @wk1 Δ F in
  [Δ ,, F ||-v σ ⟨ ρ ⟩ ≅ σ' ⟨ ρ ⟩ : Γ | VΓ | wfc_cons wfΔ wfF | wk1SubstS VΓ wfΔ wfF Vσ| f ]< wl >.
Proof.
  intro vσσ'. eapply wkSubstSEq ; eassumption.
Qed.

Lemma consWkSubstS {wl Γ F Δ Ξ σ wl'} {f : wl' ≤ε wl} {a l VΓ wfΔ } VF
  (ρ : Ξ ≤ Δ) wfΞ {RF}:
  [Δ ||-v σ : Γ | VΓ | wfΔ| f ]< wl > ->
  W[Ξ ||-<l> a : F[σ]⟨ρ⟩ | RF]< wl' > ->
  [Ξ ||-v (a .: σ⟨ρ⟩) : Γ,, F | validSnoc' (l:=l) VΓ VF | wfΞ | f]< wl >.
Proof.
  intros. unshelve eapply consSubstS.  2: Wirrelevance.
  now eapply wkSubstS.
Qed.

Lemma consWkSubstSEq' {wl Γ Δ Ξ A σ σ' a b l wl' f} {VΓ : [||-v Γ]< wl >} {wfΔ : [|- Δ]< wl' >}
  (VA : [Γ ||-v<l> A | VΓ]< wl >)
  (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ| f ]< wl >)
  (Vσσ' : [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | Vσ| f ]< wl >)
  (ρ : Ξ ≤ Δ) wfΞ {RA}
  (Ra : W[Ξ ||-<l> a : A[σ]⟨ρ⟩ | RA]< wl' >)
  (Rab : W[Ξ ||-<l> a ≅ b : A[σ]⟨ρ⟩ | RA]< wl' >) 
  (Vawkσ := consWkSubstS VA ρ wfΞ Vσ Ra) :
  [Ξ ||-v (a .: σ⟨ρ⟩) ≅  (b .: σ'⟨ρ⟩) : Γ ,, A | validSnoc' VΓ VA | wfΞ | Vawkσ | f]< wl >.
Proof.
  unshelve eapply consSubstSEq'.
  2: unshelve eapply irrelevanceSubstEq.
  5: now eapply wkSubstSEq.
  2: tea.
  1,2: Wirrelevance0; tea ; now bsimpl.
Qed.  


Lemma liftSubstS {wl Γ σ Δ lF F wl' f} (VΓ : [||-v Γ]< wl >) (wfΔ : [|- Δ]< wl' >)
  (VF : [Γ ||-v<lF> F | VΓ]< wl >)
  (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ | f]< wl >) :
  let VΓF := validSnoc' VΓ VF in
  let ρ := @wk1 Δ F[σ] in
  let wfΔF := wfc_cons wfΔ (Wescape (validTy VF f wfΔ Vσ)) in
  [Δ ,, F[σ] ||-v (tRel 0 .: σ ⟨ ρ ⟩) : Γ ,, F | VΓF | wfΔF | f]< wl >.
Proof.
  intros; unshelve econstructor.
  - now eapply wk1SubstS.
  - eapply Wvar0 ; unfold ρ; [now bsimpl|].
    now eapply Wescape, VF.
Defined.

Lemma liftSubstSrealign {wl Γ σ σ' Δ lF F wl' f} {VΓ : [||-v Γ]< wl >} {wfΔ : [|- Δ]< wl' >}
  (VF : [Γ ||-v<lF> F | VΓ]< wl >)
  {Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ | f ]< wl >} :
  let VΓF := validSnoc' VΓ VF in
  let ρ := @wk1 Δ F[σ]  in
  let wfΔF := wfc_cons wfΔ (Wescape (validTy VF f wfΔ Vσ)) in
  [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | Vσ| f ]< wl > ->
  [Δ ||-v σ' : Γ | VΓ | wfΔ | f ]< wl > ->
  [Δ ,, F[σ] ||-v (tRel 0 .: σ'⟨ρ⟩) : Γ ,, F | VΓF | wfΔF | f ]< wl >.
Proof.
  intros; unshelve econstructor.
  + now eapply wk1SubstS.
  + cbn.
    assert [Δ,, F[σ] |-[ ta ] tRel 0 : F[S >> (tRel 0 .: σ'⟨ρ⟩)] ]< wl' >.
    { replace F[_ >> _] with F[σ']⟨S⟩ by (unfold ρ; now bsimpl).
      eapply ty_conv. 1: apply (ty_var wfΔF (in_here _ _)).
      cbn; renToWk. eapply convty_wk; tea.
      eapply WescapeEq;  unshelve eapply validTyExt; cycle 3; tea. }
    apply WneuTerm; tea.
    - apply convneu_var; tea.
Qed.

Lemma liftSubstS' {wl Γ σ Δ lF F wl' f} {VΓ : [||-v Γ]< wl >} {wfΔ : [|- Δ]< wl' >}
  (VF : [Γ ||-v<lF> F | VΓ]< wl >)
  (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ | f ]< wl >) :
  let VΓF := validSnoc' VΓ VF in
  let wfΔF := wfc_cons wfΔ (Wescape (validTy VF f wfΔ Vσ)) in
  [Δ ,, F[σ] ||-v up_term_term σ : Γ ,, F | VΓF | wfΔF | f ]< wl >.
Proof.
  eapply irrelevanceSubstExt.
  2: eapply liftSubstS.
  intros ?; now bsimpl.
Qed.

Lemma liftSubstSEq {wl Γ σ σ' Δ lF F wl' f} (VΓ : [||-v Γ]< wl >) (wfΔ : [|- Δ]< wl' >)
  (VF : [Γ ||-v<lF> F | VΓ]< wl >)
  (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ | f ]< wl >) :
  let VΓF := validSnoc' VΓ VF in
  let ρ := @wk1 Δ F[σ] in
  let wfΔF := wfc_cons wfΔ (Wescape (validTy VF f wfΔ Vσ)) in
  let Vliftσ := liftSubstS VΓ wfΔ VF Vσ in
  [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | Vσ| f ]< wl > ->
  [Δ ,, F[σ] ||-v (tRel 0 .: σ ⟨ ρ ⟩) ≅ (tRel 0 .: σ' ⟨ ρ ⟩) : Γ ,, F | VΓF | wfΔF | Vliftσ| f ]< wl >.
Proof.
  intros; unshelve econstructor.
  + now apply wk1SubstSEq.
  + apply WreflLRTmEq. exact (projT2 Vliftσ).
Qed.

Lemma liftSubstSEq' {wl Γ σ σ' Δ lF F wl' f} {VΓ : [||-v Γ]< wl >} {wfΔ : [|- Δ]< wl' >}
  (VF : [Γ ||-v<lF> F | VΓ]< wl >)
  {Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ | f ]< wl >} :
  let VΓF := validSnoc' VΓ VF in
  let ρ := wk_up F (@wk_id Γ) in
  let wfΔF := wfc_cons wfΔ (Wescape (validTy VF f wfΔ Vσ)) in
  let Vliftσ := liftSubstS' VF Vσ in
  [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | Vσ| f ]< wl > ->
  [Δ ,, F[σ] ||-v up_term_term σ ≅ up_term_term σ' : Γ ,, F | VΓF | wfΔF | Vliftσ| f ]< wl >.
Proof.
  intros.
  eapply irrelevanceSubstEq.
  unshelve eapply irrelevanceSubstEqExt.
  6: now eapply liftSubstSEq.
  all: intros ?; now bsimpl.
  Unshelve. all: tea.
Qed.

Lemma liftSubstSrealign' {wl Γ σ σ' Δ lF F wl' f} {VΓ : [||-v Γ]< wl >} {wfΔ : [|- Δ]< wl' >}
  (VF : [Γ ||-v<lF> F | VΓ]< wl >)
  {Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ | f ]< wl >} :
  let VΓF := validSnoc' VΓ VF in
  let ρ := wk_up F (@wk_id Γ) in
  let wfΔF := wfc_cons wfΔ (Wescape (validTy VF f wfΔ Vσ)) in
  [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | Vσ| f ]< wl > ->
  [Δ ||-v σ' : Γ | VΓ | wfΔ | f ]< wl > ->
  [Δ ,, F[σ] ||-v up_term_term σ' : Γ ,, F | VΓF | wfΔF| f ]< wl >.
Proof.
  intros.
  eapply irrelevanceSubstExt.
  2: eapply liftSubstSrealign; tea.
  intros ?; now bsimpl.
Qed.

Lemma wk1ValidTy {wl Γ lA A lF F} {VΓ : [||-v Γ]< wl >} (VF : [Γ ||-v<lF> F | VΓ]< wl >) :
  [Γ ||-v<lA> A | VΓ]< wl > -> 
  [Γ ,, F ||-v<lA> A ⟨ @wk1 Γ F ⟩ | validSnoc' VΓ VF ]< wl >.
Proof.
  assert (forall σ, (A ⟨@wk1 Γ F⟩)[σ] = A[↑ >> σ]) as h by (intros; asimpl; now rewrite wk1_ren) ;
  intros [VA VAext]; unshelve econstructor.
  - abstract (intros * [tl _]; rewrite h; exact (VA _ _ _ _ wfΔ tl)).
  - intros * [tl _] [tleq _].
    rewrite (h σ'); unshelve eapply WLRTyEqSym.
    2: eapply VA; eassumption.
    rewrite (h σ).
    eapply VAext. 1: exact (projT1 vσ).
    eapply symmetrySubstEq. eassumption.
Qed.

Lemma wk1ValidTyEq {wl Γ lA A B lF F} {VΓ : [||-v Γ]< wl >} (VF : [Γ ||-v<lF> F | VΓ]< wl >) 
  {VA : [Γ ||-v<lA> A | VΓ]< wl >} :
  [Γ ||-v<lA> A ≅ B | VΓ | VA]< wl > -> 
  [Γ ,, F ||-v<lA> A ⟨ @wk1 Γ F ⟩ ≅ B ⟨ @wk1 Γ F ⟩ | validSnoc' VΓ VF | wk1ValidTy VF VA]< wl >.
Proof.
  assert (forall A σ, (A ⟨@wk1 Γ F⟩)[σ] = A[↑ >> σ]) as h by (intros; asimpl; now rewrite wk1_ren).
  intros []; constructor; intros.
  Wirrelevance0 ; [symmetry ; now apply h | rewrite (h B) ].
  unshelve eapply validTyEq ; [assumption | | now eapply projT1 ].
Qed.

Lemma wk1ValidTm {wl Γ lA t A lF F} {VΓ : [||-v Γ]< wl >}
  (VF : [Γ ||-v<lF> F | VΓ]< wl >)
  (VA : [Γ ||-v<lA> A | VΓ]< wl >)
  (Vt : [Γ ||-v<lA> t : A | VΓ | VA]< wl >) (ρ := @wk1 Γ F):
  [Γ,, F ||-v<lA> t⟨ρ⟩ : A⟨ρ⟩ | validSnoc' VΓ VF | wk1ValidTy VF VA]< wl >.
Proof.
  assert (forall A σ, (A ⟨@wk1 Γ F⟩)[σ] = A[↑ >> σ]) as h by (intros; asimpl; now rewrite wk1_ren).
  constructor; intros; repeat rewrite h.
  - instValid (projT1 Vσ) ; now Wirrelevance.
  - instValidExt (projT1 Vσ') (fst Vσσ') ; now Wirrelevance. 
Qed.

Lemma wk1ValidTmEq {wl Γ lA t u A lF F} {VΓ : [||-v Γ]< wl >}
  (VF : [Γ ||-v<lF> F | VΓ]< wl >)
  (VA : [Γ ||-v<lA> A | VΓ]< wl >)
  (Vtu : [Γ ||-v<lA> t ≅ u : A | VΓ | VA]< wl >) (ρ := @wk1 Γ F):
  [Γ,, F ||-v<lA> t⟨ρ⟩ ≅ u⟨ρ⟩ : A⟨ρ⟩ | validSnoc' VΓ VF | wk1ValidTy VF VA]< wl >.
Proof.
  assert (forall A σ, (A ⟨@wk1 Γ F⟩)[σ] = A[↑ >> σ]) as h by (intros; asimpl; now rewrite wk1_ren).
  constructor; intros ; repeat rewrite h.
  instValid (projT1 Vσ); Wirrelevance.
  now rewrite h.
Qed.


Lemma embValidTy@{u i j k l} {wl Γ l l' A}
    {VΓ : [VR@{i j k l}| ||-v Γ]< wl >} (h : l << l')
    (VA : typeValidity@{u i j k l} wl Γ VΓ l A (*[Γ ||-v<l> A |VΓ]< wl >*)) :
    typeValidity@{u i j k l} wl Γ VΓ l' A (*[Γ ||-v<l'> A |VΓ]< wl >*).
Proof.
  unshelve econstructor.
  - intros ????? Vσ; destruct (validTy VA _  _ Vσ) as [d pack] ; exists d ; intros.
    exists (pack _ Ho) ; eapply LR_embedding ; tea.
    now eapply pack.
  - intros ; cbn ; Wirrelevance0 ; [ reflexivity | unshelve eapply validTyExt].
    7: eassumption.
    all: tea.
Defined.

Lemma embValidTyOne @{u i j k l} {wl Γ l A}
    {VΓ : [VR@{i j k l}| ||-v Γ]< wl >}
    (VA : typeValidity@{u i j k l} wl Γ VΓ l A (*[Γ ||-v<l> A |VΓ]*)) :
    typeValidity@{u i j k l} wl Γ VΓ one A (*[Γ ||-v<one> A |VΓ]*).
Proof.
  destruct l; tea; now eapply (embValidTy Oi).
Defined.

Lemma soundCtxId {wl Γ wl' f} (VΓ : [||-v Γ]< wl >) :
  ∑ wfΓ : [|- Γ]< wl' >, [Γ ||-v tRel : Γ | VΓ | wfΓ | f]< wl >.
Proof.
  enough (G : ∑ Δ (e : Δ = Γ) (wfΔ : [|-Δ]< wl' >), [VΓ |Δ ||-v tRel : Γ | wfΔ | f]< wl >).
  1: now destruct G as [? [-> ?]].
  pattern Γ, VΓ; apply validity_rect; clear Γ VΓ.
  - exists ε, eq_refl, wfc_nil ; cbn ; rewrite Hsub.
    now constructor.
  - intros * [Δ [e [wfΔ Vid]]].
    exists (Δ,, A[tRel]); unshelve eexists. 
    1: asimpl; now rewrite e.
    unshelve eexists.
    + apply wfc_cons; tea.
      eapply Wescape.
      now apply (validTy VA f wfΔ Vid).
    + eapply irrelevanceSubstExt.
      2: eapply irrelevanceSubst; now unshelve eapply liftSubstS.
      intros []; [| bsimpl]; reflexivity.
Qed.

Definition soundCtx {wl Γ} (VΓ : [||-v Γ]< wl >) : [|-Γ]< wl > := (soundCtxId (f:= wfLCon_le_id _) VΓ).π1.

Definition idSubstS {wl Γ} (VΓ : [||-v Γ]< wl >) : [Γ ||-v tRel : Γ | VΓ | _ | _]< wl > :=
  (soundCtxId (f:= wfLCon_le_id _) VΓ).π2.

Lemma reflIdSubstS {wl Γ} (VΓ : [||-v Γ]< wl >) : [Γ ||-v tRel ≅ tRel : Γ | VΓ | _ | idSubstS VΓ | _]< wl >.
Proof.  apply reflSubst. Qed.

Lemma substS_wk {wl Γ Δ wl' f} (ρ : Δ ≤ Γ) :
  forall (VΓ : [||-v Γ]< wl >)
  (VΔ : [||-v Δ]< wl >) 
  {Ξ σ} (wfΞ : [|- Ξ]< wl' >), [VΔ | Ξ ||-v σ : _ | wfΞ | f]< wl > -> [VΓ | Ξ ||-v ρ >> σ : _ | wfΞ | f]< wl >.
Proof.
  destruct ρ as [? wwk]; induction wwk.
  + intros; cbn in *.
    destruct VΓ as [G Gad].
    destruct (VR_inv Gad) as [Heq [Hext HG]] ; cbn in *.
    rewrite Heq ; now constructor.
  + intros.
    destruct VΔ as [D Dad].
    pose proof (VR_inv Dad) as [l [VG [Gad [VA [Hsub [Hext eq]]]]]] ; cbn in *.
    rewrite Hsub in X.
    destruct X as [Htl Hhd].
    eapply irrelevanceSubstExt.
    1: rewrite <- (scons_eta' σ); reflexivity.
    cbn. asimpl.
    unshelve eapply IHwwk ; [now exists VG | ].
    exact Htl.
  + intros VΔ VΓ **.
    pose proof (VR_inv (VAd.adequate VΓ)) as [l [VG [Gad [VAren [Hsub [Hext eq]]]]]] ; cbn in *.
    rewrite Hsub in X.
    destruct X as [Htl Hhd].
    cbn in *.
    eapply irrelevanceSubstExt.
    1:{ rewrite <- (scons_eta' σ); cbn; unfold up_ren; rewrite scons_comp'; cbn. reflexivity. }
    asimpl.
    pose proof (VR_inv (VAd.adequate VΔ)) as [l' [VD [Dad [VA [Hsub' [Hext' eq']]]]]] ; cbn in *.
    rewrite Hsub'.
    unshelve eapply (consSubstS (Build_VAdequate _ Dad)). 
    * now eapply (IHwwk (Build_VAdequate _ Dad) (Build_VAdequate _ Gad)).
    * Wirrelevance.
Defined.
Axiom todo : False.
Lemma substSEq_wk {wl Γ Δ wl' f} (ρ : Δ ≤ Γ) :
  forall (VΓ : [||-v Γ]< wl >)
  (VΔ : [||-v Δ]< wl >) 
  Ξ σ σ' (wfΞ : [|- Ξ]< wl' >)
  (Vσ : [VΔ | Ξ ||-v σ : _ | wfΞ | f]< wl >),
  [VΔ | Ξ ||-v σ' : _ | wfΞ | f]< wl > -> 
  [VΔ | Ξ ||-v σ ≅ σ' : _ | wfΞ | Vσ | f]< wl > -> 
  [VΓ | Ξ ||-v ρ >> σ ≅ ρ >> σ' : _ | wfΞ | substS_wk ρ VΓ VΔ wfΞ Vσ | f]< wl >.
Proof.
  destruct ρ as [? wwk]; induction wwk.
  - intros * Vσ' Vσσ'.
    destruct VΓ as [G Gad].
    pose proof (VR_inv Gad) as [Heq [Hext HG]] ; cbn in *.
    rewrite HG, Hext.
    now constructor.
  - intros ??????.
    destruct VΔ as [D Dad].
    pose proof (VR_inv Dad) as [l [VD [Dad' [VAren [Hsub [Hext eq]]]]]].
    rewrite eq; intros Vσ Vσ' Vσσ'.
    cbn in Vσσ', Vσ' ; rewrite Hext in Vσσ'.
    rewrite Hsub in Vσ'.
    cbn; fsimpl.
    unshelve eapply irrelevanceSubstEq.
    1,2: assumption.
    2: unshelve eapply IHwwk ; cbn in *.
    1: econstructor ; exact Dad'.
    2: exact (projT1 Vσ').
    2: exact (fst Vσσ').
  - intros ??????.
    set (ρ0 := {| well_wk := _ |}); unfold ρ0.
    intros Vσ Vσ' Vσσ'.
    pose proof (v := substS_wk ρ0 VΓ _ wfΞ Vσ).
    destruct VΓ as [G Gad].
    pose proof (VR_inv (VAd.adequate VΔ)) as [l [VD [Dad' [VA [Hsub [Hext eq]]]]]].
    pose proof (VR_inv Gad) as [l' [VG [Gad' [VA' [Hsub' [Hext' eq']]]]]].
    rewrite Hext in Vσσ'.
    rewrite Hsub in Vσ'.
    assert (subst_eq : forall τ : nat -> term, τ var_zero .: (ρ >> ↑ >> τ) =1 (0 .: ρ >> S) >> τ).
    1:{ intros τ;  asimpl; reflexivity. }
    eapply irrelevanceSubstEq.
    unshelve eapply irrelevanceSubstEqExt.
    2,5: apply subst_eq.
    + eapply irrelevanceSubstExt.
      1: symmetry; apply subst_eq.
      exact v.
    + eapply irrelevanceSubstEq.
      eapply consSubstSEq'.
      * unshelve eapply (IHwwk _ (Build_VAdequate _ Dad') Ξ (↑ >> σ) (↑ >> σ') wfΞ _ (projT1 Vσ') (fst Vσσ')).
      * Wirrelevance0. 
        2: now eapply (snd Vσσ').
        now asimpl.
        Unshelve.
        2: exact (Build_VAdequate _ Gad').
        2: exact VA'.
        cbn in v ; rewrite Hsub' in v.
        Wirrelevance0 ; [reflexivity | now eapply (projT2 v) ].
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
  Unshelve. 1,2: tea.
  now eapply substS_wk.
Qed.




End Properties.
