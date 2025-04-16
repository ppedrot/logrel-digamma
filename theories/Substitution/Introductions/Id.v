From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations LContexts Context NormalForms Weakening GenericTyping Monad LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Induction Irrelevance Escape Reflexivity Monotonicity Split Weakening Neutral Transitivity Reduction Application Universe Id.
From LogRel.Substitution Require Import Irrelevance Properties Monotonicity Conversion SingleSubst Reflexivity Reduction.
From LogRel.Substitution.Introductions Require Import Universe Var.

Set Universe Polymorphism.

Section Id.
Context `{GenericTypingProperties}.

  Lemma IdValid {wl Γ l A x y} 
    (VΓ : [||-v Γ]< wl >) 
    (VA : [_ ||-v<l> A | VΓ]< wl >) 
    (Vx : [_ ||-v<l> x : _ | _ | VA]< wl >)
    (Vy : [_ ||-v<l> y : _ | _ | VA]< wl >) :
    [_ ||-v<l> tId A x y | VΓ]< wl >.
  Proof.
    unshelve econstructor; intros.
    - instValid vσ; cbn ; now eapply WIdRed.
    - instAllValid vσ vσ' vσσ'; eapply WIdCongRed; refold; tea.
      eapply wft_Id; now Wescape.
  Qed.

  Lemma IdCongValid {wl Γ l A A' x x' y y'}
    (VΓ : [||-v Γ]< wl >) 
    (VA : [_ ||-v<l> A | VΓ]< wl >) 
    (VA' : [_ ||-v<l> A' | VΓ]< wl >) 
    (VAA' : [_ ||-v<l> A ≅ A' | VΓ | VA]< wl >) 
    (Vx : [_ ||-v<l> x : _ | _ | VA]< wl >)
    (Vx' : [_ ||-v<l> x' : _ | _ | VA]< wl >)
    (Vxx' : [_ ||-v<l> x ≅ x' : _ | _ | VA]< wl >)
    (Vy : [_ ||-v<l> y : _ | _ | VA]< wl >) 
    (Vy' : [_ ||-v<l> y' : _ | _ | VA]< wl >) 
    (Vyy' : [_ ||-v<l> y ≅ y' : _ | _ | VA]< wl >) 
    (VId : [_ ||-v<l> tId A x y | VΓ]< wl >) :
    [_ ||-v<l> tId A x y ≅ tId A' x' y' | VΓ | VId]< wl >.
  Proof.
    constructor; intros.
    instValid Vσ; eapply WIdCongRed; refold; tea.
    eapply wft_Id. 
    2,3: eapply ty_conv.
    all: now Wescape.
  Qed.


  Lemma IdTmValid {wl Γ l A x y} 
    (VΓ : [||-v Γ]< wl >) 
    (VU := UValid VΓ)
    (VAU : [_ ||-v<one> A : U | VΓ | VU]< wl >) 
    (VA := univValid VΓ VU VAU)
    (Vx : [_ ||-v<l> x : _ | _ | VA]< wl >)
    (Vy : [_ ||-v<l> y : _ | _ | VA]< wl >) :
    [_ ||-v<one> tId A x y : _ | VΓ | VU]< wl >.
  Proof. 
    unshelve econstructor; intros.
    - instValid Vσ.
      unshelve econstructor ; [ shelve | ].
      intros wl'' Ho Ho'.
      pose (f' := over_tree_le Ho').
      unshelve eapply WIdRedU; refold ; tea.
    - instAllValid Vσ Vσ' Vσσ'.
      unshelve eapply WIdCongRedU; refold; tea.
  Qed.
    
  Lemma IdTmCongValid {wl Γ l A A' x x' y y'}
    (VΓ : [||-v Γ]< wl >) 
    (VU := UValid VΓ)
    (VAU : [_ ||-v<one> A : _ | VΓ | VU]< wl >) 
    (VA := univValid VΓ VU VAU)
    (VAU' : [_ ||-v<one> A' : _ | VΓ | VU]< wl >) 
    (VAAU' : [_ ||-v<one> A ≅ A' : _ | VΓ | VU]< wl >) 
    (Vx : [_ ||-v<l> x : _ | _ | VA]< wl >)
    (Vx' : [_ ||-v<l> x' : _ | _ | VA]< wl >)
    (Vxx' : [_ ||-v<l> x ≅ x' : _ | _ | VA]< wl >)
    (Vy : [_ ||-v<l> y : _ | _ | VA]< wl >) 
    (Vy' : [_ ||-v<l> y' : _ | _ | VA]< wl >) 
    (Vyy' : [_ ||-v<l> y ≅ y' : _ | _ | VA]< wl >) :
    [_ ||-v<one> tId A x y ≅ tId A' x' y' : _ | VΓ | VU]< wl >.
  Proof.
    constructor; intros; instValid Vσ.
    unshelve eapply WIdCongRedU; refold; tea.
    1: now eapply univValid.
    all: eapply WLRTmRedConv ; [ eapply univEqValid; irrValid | ].
    all: Wirrelevance0 ; [ reflexivity | eassumption].
    Unshelve.
    all: eassumption.
Qed.    

  Lemma reflValid {wl Γ l A x} 
    (VΓ : [||-v Γ]< wl >) 
    (VA : [_ ||-v<l> A | VΓ]< wl >) 
    (Vx : [_ ||-v<l> x : _ | _ | VA]< wl >)
    (VId : [_ ||-v<l> tId A x x | VΓ]< wl >) :
    [_ ||-v<l> tRefl A x : _ | _ | VId]< wl >.
  Proof.
    unshelve econstructor; intros.
    - instValid Vσ; now unshelve eapply WreflRed.
    - instAllValid Vσ Vσ' Vσσ'; Wescape; now unshelve eapply WreflCongRed.
  Qed.

  Lemma reflCongValid {wl Γ l A A' x x'}
    (VΓ : [||-v Γ]< wl >) 
    (VA : [_ ||-v<l> A | VΓ]< wl >) 
    (VA' : [_ ||-v<l> A' | VΓ]< wl >) 
    (VAA' : [_ ||-v<l> A ≅ A' | VΓ | VA]< wl >) 
    (Vx : [_ ||-v<l> x : _ | _ | VA]< wl >)
    (Vx' : [_ ||-v<l> x' : _ | _ | VA]< wl >)
    (Vxx' : [_ ||-v<l> x ≅ x' : _ | _ | VA]< wl >)
    (VId : [_ ||-v<l> tId A x x | VΓ]< wl >) :
    [_ ||-v<l> tRefl A x ≅ tRefl A' x' : _ | _ | VId]< wl >.
  Proof.
    constructor; intros; instValid Vσ.
    Wescape; unshelve eapply WreflCongRed; refold; tea.
    now eapply ty_conv.
  Qed.

  Lemma subst_scons2 (P e y : term) (σ : nat -> term) : P[e .: y..][σ] = P [e[σ] .: (y[σ] .: σ)].
  Proof. now asimpl. Qed.
  
  Lemma subst_upup_scons2 (P e y : term) (σ : nat -> term) : P[up_term_term (up_term_term σ)][e .: y..] = P [e .: (y .: σ)].
  Proof. now asimpl. Qed.

  Lemma consSubstS' {wl Γ σ t l A Δ wl' f} 
    (VΓ : [||-v Γ]< wl >)
    (VΓA : [||-v Γ ,, A]< wl >)
    (wfΔ : [|- Δ]< wl' >)
    (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ | f]< wl >)
    (VA : [Γ ||-v<l> A | VΓ]< wl >)
    (Vt : W[ Δ ||-<l> t : A[σ] | validTy VA f wfΔ Vσ]< wl' >) :
    [Δ ||-v (t .: σ) : Γ ,, A | VΓA | wfΔ | f]< wl >.
  Proof.
    pose proof (consSubstS VΓ wfΔ Vσ VA Vt).
    irrValid.
  Qed.

  Lemma consSubstSEq'' {wl Γ σ σ' t u l A Δ wl' f} 
    (VΓ : [||-v Γ]< wl >)
    (VΓA : [||-v Γ ,, A]< wl >)
    (wfΔ : [|- Δ]< wl' >)
    (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ | f]< wl >)
    (Vσσ' : [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | Vσ | f]< wl >)
    (VA : [Γ ||-v<l> A | VΓ]< wl >)
    (Vt : W[Δ ||-<l> t : A[σ] | validTy VA f wfΔ Vσ]< wl' >)
    (Vtu : W[Δ ||-<l> t ≅ u : A[σ] | validTy VA f wfΔ Vσ]< wl' >)
    (Vσt : [_ ||-v (t .: σ) : _ | VΓA | wfΔ | f]< wl >) :
    [Δ ||-v (t .: σ) ≅  (u .: σ') : Γ ,, A | VΓA | wfΔ | Vσt | f]< wl >.
  Proof.
    pose proof (consSubstSEq' VΓ wfΔ Vσ Vσσ' VA Vt Vtu).
    irrValid.
  Qed.  


  Lemma idElimMotiveCtxIdValid {wl Γ l A x}
    (VΓ : [||-v Γ]< wl >) 
    (VA : [_ ||-v<l> A | VΓ]< wl >) 
    (Vx : [_ ||-v<l> x : _ | _ | VA]< wl >) :
    [Γ,, A ||-v< l > tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) | validSnoc' VΓ VA]< wl >.
  Proof.
    unshelve eapply IdValid.
    - now eapply wk1ValidTy.
    - now eapply wk1ValidTm.
    - exact (var0Valid VΓ VA).
  Qed.
  
  Lemma idElimMotiveCtxIdCongValid {wl Γ l A A' x x'}
    (VΓ : [||-v Γ]< wl >) 
    (VA : [_ ||-v<l> A | VΓ]< wl >) 
    (VA' : [_ ||-v<l> A' | VΓ]< wl >) 
    (VAA' : [_ ||-v<l> A ≅ A' | VΓ | VA]< wl >)
    (Vx : [_ ||-v<l> x : _ | _ | VA]< wl >) 
    (Vx' : [_ ||-v<l> x' : _ | _ | VA]< wl >) 
    (Vxx' : [_ ||-v<l> x ≅ x' : _ | _ | VA]< wl >) 
    (VId : [Γ,, A ||-v< l > tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) | validSnoc' VΓ VA]< wl >) :
    [_ ||-v<l> _ ≅ tId A'⟨@wk1 Γ A'⟩ x'⟨@wk1 Γ A'⟩ (tRel 0) | validSnoc' VΓ VA | VId]< wl >.
  Proof.
    assert (h : forall t, t⟨@wk1 Γ A'⟩ = t⟨@wk1 Γ A⟩) by reflexivity.
    unshelve eapply IdCongValid.
    - now eapply wk1ValidTy.
    - rewrite h; now eapply wk1ValidTy.
    - rewrite h; now eapply wk1ValidTyEq.
    - now eapply wk1ValidTm.
    - rewrite h; now eapply wk1ValidTm.
    - rewrite h; now eapply wk1ValidTmEq.
    - eapply var0Valid.
    - eapply var0Valid.
    - eapply reflValidTm; eapply var0Valid.
  Qed.
  
  
  Lemma idElimMotiveScons2Valid {wl Γ l A x y e}
    (VΓ : [||-v Γ]< wl >) 
    (VA : [_ ||-v<l> A | VΓ]< wl >) 
    (Vx : [_ ||-v<l> x : _ | _ | VA]< wl >)
    (Vy : [Γ ||-v<l> y : _ | _ | VA]< wl >)
    (VId : [Γ ||-v<l> tId A x y | VΓ]< wl >)
    (Ve : [_ ||-v<l> e : _ | _ | VId]< wl >) 
    (VΓext : [||-v (Γ ,, A) ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)]< wl >)
    Δ σ wl' f (wfΔ: [ |-[ ta ] Δ]< wl' >) (vσ: [VΓ | Δ ||-v σ : _ | wfΔ | f]< wl >) :
      [VΓext | Δ ||-v (e[σ] .: (y[σ] .: σ)) : _ | wfΔ| f]< wl >.
  Proof.
    intros; unshelve eapply consSubstS'; tea.
    2: now eapply consSubstSvalid.
    1: now eapply idElimMotiveCtxIdValid.
    instValid vσ; Wirrelevance.
  Qed.
  
  Lemma substIdElimMotive {wl Γ l A x P y e}
    (VΓ : [||-v Γ]< wl >) 
    (VA : [_ ||-v<l> A | VΓ]< wl >) 
    (Vx : [_ ||-v<l> x : _ | _ | VA]< wl >)
    (VΓext : [||-v (Γ ,, A) ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)]< wl >)
    (VP : [_ ||-v<l> P | VΓext]< wl >)
    (Vy : [Γ ||-v<l> y : _ | _ | VA]< wl >)
    (VId : [Γ ||-v<l> tId A x y | VΓ]< wl >)
    (Ve : [_ ||-v<l> e : _ | _ | VId]< wl >) : 
    [_ ||-v<l> P[e .: y ..] | VΓ]< wl >.
  Proof.
    opector; intros.
    - rewrite subst_scons2; eapply validTy; tea; now eapply idElimMotiveScons2Valid.
    - Wirrelevance0 ; rewrite subst_scons2;[reflexivity|].
      unshelve eapply validTyExt.
      7,8: eapply idElimMotiveScons2Valid; cycle 1; tea.
      1: tea.
      eapply consSubstSEq''.
      + now unshelve eapply consSubstSEqvalid.
      + instValid vσ; Wirrelevance.
      + instAllValid vσ vσ' vσσ'; Wirrelevance.
      Unshelve. 2: now eapply idElimMotiveCtxIdValid.
  Qed.
  

  Lemma subst_idElimMotive_substupup {wl Γ Δ l A x P y e σ wl' f}
    (VΓ : [||-v Γ]< wl >) 
    (wfΔ : [|- Δ]< wl' >)
    (Vσ : [_ ||-v σ : _ | VΓ | wfΔ | f]< wl >)
    (VA : [_ ||-v<l> A | VΓ]< wl >) 
    (RVA := validTy VA f wfΔ Vσ)
    (Vx : [_ ||-v<l> x : _ | _ | VA]< wl >)
    (VΓext : [||-v (Γ ,, A) ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)]< wl >)
    (VP : [_ ||-v<l> P | VΓext]< wl >)
    (Ry : W[ _ ||-< l > y : _ | RVA]< wl' >)
    (RId : W[Δ ||-<l> tId A[σ] x[σ] y]< wl' >)
    (Re : W[ _ ||-< l > e : _ | RId]< wl' >) :
    W[Δ ||-<l> P[up_term_term (up_term_term σ)][e .: y ..]]< wl' >.
  Proof.
    pose (VΓA := validSnoc' VΓ VA). 
    rewrite subst_upup_scons2.
    unshelve eapply validTy; cycle 4 ; tea.
    unshelve eapply consSubstS'; tea.
    + now eapply consSubstS.
    + now eapply idElimMotiveCtxIdValid.
    + Wirrelevance.
  Qed.
  
  Lemma irrelevanceSubst' {wl Γ} (VΓ VΓ' : [||-v Γ]< wl >) {σ Δ Δ' wl' f}
    (wfΔ : [|- Δ]< wl' >) (wfΔ' : [|- Δ']< wl' >) : Δ = Δ' ->
    [Δ ||-v σ : Γ | VΓ | wfΔ | f]< wl > -> [Δ' ||-v σ : Γ | VΓ' | wfΔ' |f]< wl >.
  Proof.
    intros ->; eapply irrelevanceSubst.
  Qed.

  Lemma idElimMotive_Idsubst_eq {Γ Δ A x σ} : 
    tId A[σ]⟨@wk1 Δ A[σ]⟩ x[σ]⟨@wk1 Δ A[σ]⟩ (tRel 0) = (tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0))[up_term_term σ].
  Proof. now bsimpl. Qed.
  
  Lemma red_idElimMotive_substupup {wl Γ Δ l A x P σ wl' f}
    (VΓ : [||-v Γ]< wl >) 
    (wfΔ : [|- Δ]< wl' >)
    (Vσ : [_ ||-v σ : _ | VΓ | wfΔ | f]< wl >)
    (VA : [_ ||-v<l> A | VΓ]< wl >) 
    (Vx : [_ ||-v<l> x : _ | _ | VA]< wl >)
    (VΓext : [||-v (Γ ,, A) ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)]< wl >)
    (VP : [_ ||-v<l> P | VΓext]< wl >) :
   W[(Δ ,, A[σ]),, tId A[σ]⟨@wk1 Δ A[σ]⟩ x[σ]⟨@wk1 Δ A[σ]⟩ (tRel 0) ||-<l> P[up_term_term (up_term_term σ)]]< wl' >.
  Proof.
    pose (VΓA := validSnoc' VΓ VA). 
    instValid Vσ.
    unshelve eapply validTy; cycle 4; tea.
    * Wescape. 
      assert [|- Δ,, A[σ]]< wl' > by now eapply wfc_cons.
      eapply wfc_cons; tea.
      eapply wft_Id.
      1: now eapply wft_wk.
      1: now eapply ty_wk.
      rewrite wk1_ren_on; now eapply ty_var0.
    * epose (v1:= liftSubstS' VA Vσ).
      epose (v2:= liftSubstS' _ v1).
      eapply irrelevanceSubst'.
      1: now erewrite idElimMotive_Idsubst_eq.
      eapply v2.
      Unshelve. 2: now eapply idElimMotiveCtxIdValid.
  Qed.

  Lemma irrelevanceSubstEq' {wl Γ} (VΓ VΓ' : [||-v Γ]< wl >) {σ σ' Δ Δ' wl' f}
    (wfΔ : [|- Δ]< wl' >) (wfΔ' : [|- Δ']< wl' >)
    (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ | f]< wl >) (Vσ' : [Δ' ||-v σ : Γ | VΓ' | wfΔ' | f]< wl >) :
    Δ = Δ' ->
    [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | Vσ | f]< wl > -> [Δ' ||-v σ ≅ σ' : Γ | VΓ' | wfΔ' | Vσ' | f]< wl >.
  Proof.
    intros ->; eapply irrelevanceSubstEq.
  Qed.
  
  Lemma red_idElimMotive_substupup_cong {wl Γ Δ l A x P σ σ' wl' f}
    (VΓ : [||-v Γ]< wl >) 
    (wfΔ : [|- Δ]< wl' >)
    (Vσ : [_ ||-v σ : _ | VΓ | wfΔ | f]< wl >)
    (Vσ' : [_ ||-v σ' : _ | VΓ | wfΔ | f]< wl >)
    (Vσσ' : [_ ||-v σ ≅ σ' : _ | VΓ | wfΔ | Vσ| f]< wl >)
    (VA : [_ ||-v<l> A | VΓ]< wl >) 
    (Vx : [_ ||-v<l> x : _ | _ | VA]< wl >)
    (VΓext : [||-v (Γ ,, A) ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)]< wl >)
    (VP : [_ ||-v<l> P | VΓext]< wl >) 
    (RPσ : W[(Δ ,, A[σ]),, tId A[σ]⟨@wk1 Δ A[σ]⟩ x[σ]⟨@wk1 Δ A[σ]⟩ (tRel 0) ||-<l> P[up_term_term (up_term_term σ)]]< wl' >) :
    W[_ ||-< l > _ ≅ P[up_term_term (up_term_term σ')]| RPσ]< wl' >.
  Proof.
    pose (VΓA := validSnoc' VΓ VA). 
    instAllValid Vσ Vσ' Vσσ'.
    Wirrelevance0 ; [reflexivity | ] ; unshelve eapply validTyExt; cycle 3 ; tea.
    * Wescape. 
      assert [|- Δ,, A[σ]]< wl' > by now eapply wfc_cons.
      eapply wfc_cons; tea.
      eapply wft_Id.
      1: now eapply wft_wk.
      1: now eapply ty_wk.
      rewrite wk1_ren_on; now eapply ty_var0.
    * epose (v1:= liftSubstS' VA Vσ).
      epose (v2:= liftSubstS' _ v1).
      eapply irrelevanceSubst'.
      1: now erewrite idElimMotive_Idsubst_eq.
      eapply v2.
      Unshelve. 2: now eapply idElimMotiveCtxIdValid.
    * eapply irrelevanceSubst'.
      1: now erewrite idElimMotive_Idsubst_eq.
      eapply liftSubstSrealign'.
      + now eapply liftSubstSEq'.
      + now eapply liftSubstSrealign'.
      Unshelve. 
      2: now eapply idElimMotiveCtxIdValid.
    * eapply irrelevanceSubstEq'.
      1: now erewrite idElimMotive_Idsubst_eq.
      eapply liftSubstSEq'.
      now eapply liftSubstSEq'.
      Unshelve.
      2: now eapply idElimMotiveCtxIdValid.
  Qed.

  Lemma redEq_idElimMotive_substupup {wl Γ Δ l A A' x x' P P' σ wl' f}
    (VΓ : [||-v Γ]< wl >) 
    (wfΔ : [|- Δ]< wl' >)
    (Vσ : [_ ||-v σ : _ | VΓ | wfΔ | f]< wl >)
    (VA : [_ ||-v<l> A | VΓ]< wl >) 
    (VA' : [_ ||-v<l> A' | VΓ]< wl >) 
    (VAA' : [_ ||-v<l> A ≅ A' | _ | VA]< wl >)
    (Vx : [_ ||-v<l> x : _ | _ | VA]< wl >)
    (Vx' : [_ ||-v<l> x' : _ | _ | VA]< wl >)
    (Vxx' : [_ ||-v<l> x ≅ x' : _ | _ | VA]< wl >)
    (VΓext : [||-v (Γ ,, A) ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)]< wl >)
    (VP : [_ ||-v<l> P | VΓext]< wl >)
    (VP' : [_ ||-v<l> P' | VΓext]< wl >)
    (VPP' : [_ ||-v<l> P ≅ P' | _ | VP]< wl >) 
    (VPsubstupup : W[(Δ ,, A[σ]),, tId A[σ]⟨@wk1 Δ A[σ]⟩ x[σ]⟨@wk1 Δ A[σ]⟩ (tRel 0) ||-<l> P[up_term_term (up_term_term σ)]]< wl' >) :
    W[_ ||-<l> _ ≅ P'[up_term_term (up_term_term σ)] | VPsubstupup]< wl' >.
  Proof.
    pose (VΓA := validSnoc' VΓ VA). 
    instValid Vσ.
    Wirrelevance0 ; [reflexivity | ] ; unshelve eapply validTyEq; cycle 4; tea.
    * Wescape. 
      assert [|- Δ,, A[σ]]< wl' > by now eapply wfc_cons.
      eapply wfc_cons; tea.
      eapply wft_Id.
      1: now eapply wft_wk.
      1: now eapply ty_wk.
      rewrite wk1_ren_on; now eapply ty_var0.
    * epose (v1:= liftSubstS' VA Vσ).
      epose (v2:= liftSubstS' _ v1).
      eapply irrelevanceSubst'.
      1: now erewrite idElimMotive_Idsubst_eq.
      eapply v2.
      Unshelve. 2: now eapply idElimMotiveCtxIdValid.
  Qed.


  Lemma substEq_idElimMotive_substupupEq {wl Γ Δ l A x P y y' e e' σ σ' wl' f}
    (VΓ : [||-v Γ]< wl >) 
    (wfΔ : [|- Δ]< wl' >)
    (Vσ : [_ ||-v σ : _ | VΓ | wfΔ | f]< wl >)
    (Vσ' : [_ ||-v σ' : _ | VΓ | wfΔ | f]< wl >)
    (Vσσ' : [_ ||-v σ ≅ σ' : _ | VΓ | wfΔ | Vσ | f]< wl >)
    (VA : [_ ||-v<l> A | VΓ]< wl >) 
    (RVA := validTy VA f wfΔ Vσ)
    (RVA' := validTy VA f wfΔ Vσ')
    (Vx : [_ ||-v<l> x : _ | _ | VA]< wl >)
    (VΓext : [||-v (Γ ,, A) ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)]< wl >)
    (VP : [_ ||-v<l> P | VΓext]< wl >)
    (Ry : W[  _ ||-< l > y : _ | RVA]< wl' >)
    (Ry' : W[  _ ||-< l > y' : _ | RVA']< wl' >)
    (Ryy' : W[  _ ||-< l > y ≅ y' : _ | RVA]< wl' >)
    (RId : W[Δ ||-<l> tId A[σ] x[σ] y]< wl' >)
    (RId' : W[Δ ||-<l> tId A[σ'] x[σ'] y']< wl' >)
    (Re : W[ _ ||-< l > e : _ | RId]< wl' >)
    (Re' : W[ _ ||-< l > e' : _ | RId']< wl' >)
    (Ree' : W[ _ ||-< l > e ≅ e' : _ | RId]< wl' >)
    (RPsubst : W[Δ ||-<l> P[up_term_term (up_term_term σ)][e .: y ..]]< wl' >) :
    W[Δ ||-< l > P[up_term_term (up_term_term σ)][e .: y ..] ≅ P[up_term_term (up_term_term σ')][e' .: y' ..] | RPsubst]< wl' >.
  Proof.
    pose (VΓA := validSnoc' VΓ VA). 
    Wirrelevance0; rewrite subst_upup_scons2; [reflexivity|].
    unshelve eapply validTyExt; cycle 3; tea.
    - unshelve eapply consSubstS'; tea.
      + now eapply consSubstS.
      + now eapply idElimMotiveCtxIdValid.
      + Wirrelevance.
    - unshelve eapply consSubstS'; tea.
      + now eapply consSubstS.
      + now eapply idElimMotiveCtxIdValid.
      + Wirrelevance.
    - unshelve eapply consSubstSEq''; tea.
      4,5: Wirrelevance.
      2: now eapply idElimMotiveCtxIdValid.
      2: unshelve eapply consSubstSEq'; tea.
  Qed.

  Lemma substEq_idElimMotive_substupup {wl Γ Δ l A x P y y' e e' σ wl' f}
    (VΓ : [||-v Γ]< wl >) 
    (wfΔ : [|- Δ]< wl' >)
    (Vσ : [_ ||-v σ : _ | VΓ | wfΔ| f]< wl >)
    (VA : [_ ||-v<l> A | VΓ]< wl >) 
    (RVA := validTy VA f wfΔ Vσ)
    (Vx : [_ ||-v<l> x : _ | _ | VA]< wl >)
    (VΓext : [||-v (Γ ,, A) ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)]< wl >)
    (VP : [_ ||-v<l> P | VΓext]< wl >)
    (Ry : W[  _ ||-< l > y : _ | RVA]< wl' >)
    (Ry' : W[  _ ||-< l > y' : _ | RVA]< wl' >)
    (Ryy' : W[  _ ||-< l > y ≅ y' : _ | RVA]< wl' >)
    (RId : W[Δ ||-<l> tId A[σ] x[σ] y]< wl' >)
    (RId' : W[Δ ||-<l> tId A[σ] x[σ] y']< wl' >)
    (Re : W[ _ ||-< l > e : _ | RId]< wl' >)
    (Re' : W[ _ ||-< l > e' : _ | RId']< wl' >)
    (Ree' : W[ _ ||-< l > e ≅ e' : _ | RId]< wl' >)
    (RPsubst : W[Δ ||-<l> P[up_term_term (up_term_term σ)][e .: y ..]]< wl' >) :
    W[Δ ||-< l > P[up_term_term (up_term_term σ)][e .: y ..] ≅ P[up_term_term (up_term_term σ)][e' .: y' ..] | RPsubst]< wl' >.
  Proof.
    eapply substEq_idElimMotive_substupupEq; tea; eapply reflSubst.
  Qed.

  Set Printing Primitive Projection Parameters.

  Lemma substExt_idElimMotive_substupup {wl Γ Δ l A A' x x' P P' y y' e e' σ wl' f}
    (VΓ : [||-v Γ]< wl >) 
    (wfΔ : [|- Δ]< wl' >)
    (Vσ : [_ ||-v σ : _ | VΓ | wfΔ | f]< wl >)
    (VA : [_ ||-v<l> A | VΓ]< wl >) 
    (VA' : [_ ||-v<l> A' | VΓ]< wl >) 
    (VAA' : [_ ||-v<l> A ≅ A' | _ | VA]< wl >)
    (RVA := validTy VA f wfΔ Vσ)
    (Vx : [_ ||-v<l> x : _ | _ | VA]< wl >)
    (Vx' : [_ ||-v<l> x' : _ | _ | VA]< wl >)
    (Vxx' : [_ ||-v<l> x ≅ x' : _ | _ | VA]< wl >)
    (VΓext : [||-v (Γ ,, A) ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)]< wl >)
    (VP : [_ ||-v<l> P | VΓext]< wl >)
    (VP' : [_ ||-v<l> P' | VΓext]< wl >)
    (VPP' : [_ ||-v<l> P ≅ P' | _ | VP]< wl >) 
    (Ry : W[  _ ||-< l > y : _ | RVA]< wl' >)
    (Ry' : W[  _ ||-< l > y' : _ | RVA]< wl' >)
    (Ryy' : W[  _ ||-< l > y ≅ y' : _ | RVA]< wl' >)
    (RId : W[Δ ||-<l> tId A[σ] x[σ] y]< wl' >)
    (RId' : W[Δ ||-<l> tId A[σ] x[σ] y']< wl' >)
    (Re : W[ _ ||-< l > e : _ | RId]< wl' >)
    (Re' : W[ _ ||-< l > e' : _ | RId']< wl' >)
    (Ree' : W[ _ ||-< l > e ≅ e' : _ | RId]< wl' >)
    (RPsubst : W[Δ ||-<l> P[up_term_term (up_term_term σ)][e .: y ..]]< wl' >) :
    W[ Δ ||-< l > P[up_term_term (up_term_term σ)][e .: y ..] ≅ P'[up_term_term (up_term_term σ)][e' .: y' ..] | RPsubst]< wl' >.
  Proof.
    pose (VΓA := validSnoc' VΓ VA). 
    eapply WLRTransEq.
    eapply substEq_idElimMotive_substupup.
    2,4,8: tea. all:tea.
    Wirrelevance0; rewrite subst_upup_scons2; [reflexivity|].
    unshelve eapply validTyEq; cycle 4; tea.
    eapply irrelevanceSubst.
    unshelve eapply consSubstS.
    3: now eapply idElimMotiveCtxIdValid.
    1: now eapply consSubstS.
    Wirrelevance.
    Unshelve. 2: eapply subst_idElimMotive_substupup; cycle 1; tea.
  Qed.


  Lemma substExtIdElimMotive {wl Γ l A x P y y' e e'}
    (VΓ : [||-v Γ]< wl >) 
    (VA : [_ ||-v<l> A | VΓ]< wl >) 
    (Vx : [_ ||-v<l> x : _ | _ | VA]< wl >)
    (VΓext : [||-v (Γ ,, A) ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)]< wl >)
    (VP : [_ ||-v<l> P | VΓext]< wl >)
    (Vy : [Γ ||-v<l> y : _ | _ | VA]< wl >)
    (Vy' : [Γ ||-v<l> y' : _ | _ | VA]< wl >)
    (Vyy' : [Γ ||-v<l> y ≅ y' : _ | _ | VA]< wl >)
    (VId : [Γ ||-v<l> tId A x y | VΓ]< wl >)
    (VId' : [Γ ||-v<l> tId A x y' | VΓ]< wl >)
    (Ve : [_ ||-v<l> e : _ | _ | VId]< wl >) 
    (Ve' : [_ ||-v<l> e' : _ | _ | VId']< wl >) 
    (Vee' : [_ ||-v<l> e ≅ e' : _ | _ | VId]< wl >) 
    (VPey : [_ ||-v<l> P[e .: y ..] | VΓ]< wl >) : 
    [_ ||-v<l> P[e .: y ..] ≅ P[e' .: y' ..] | VΓ | VPey]< wl >.
  Proof.
    constructor; intros.
    Wirrelevance0; rewrite subst_scons2; [reflexivity|]. 
    unshelve eapply validTyExt.
    7,8: eapply idElimMotiveScons2Valid; cycle 1; tea.
    1: tea.
    instValid Vσ; unshelve eapply consSubstSEq''.
    4: now eapply idElimMotiveCtxIdValid.
    2: eapply consSubstSEq'; [now eapply reflSubst|]; Wirrelevance.
    all: Wirrelevance.
    Unshelve. 1:tea. Wirrelevance.
  Qed.

  Lemma substEqIdElimMotive {wl Γ l A A' x x' P P' y y' e e'}
    (VΓ : [||-v Γ]< wl >) 
    (VA : [_ ||-v<l> A | VΓ]< wl >) 
    (VA' : [_ ||-v<l> A' | VΓ]< wl >) 
    (VAA' : [_ ||-v<l> A ≅ A' | VΓ | VA]< wl >) 
    (Vx : [_ ||-v<l> x : _ | _ | VA]< wl >)
    (Vx' : [_ ||-v<l> x' : _ | _ | VA]< wl >)
    (Vxx' : [_ ||-v<l> x ≅ x' : _ | _ | VA]< wl >)
    (VΓext : [||-v (Γ ,, A) ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)]< wl >)
    (VP : [_ ||-v<l> P | VΓext]< wl >)
    (VP' : [_ ||-v<l> P | VΓext]< wl >)
    (VPP' : [_ ||-v<l> P ≅ P' | _ | VP]< wl >)
    (Vy : [Γ ||-v<l> y : _ | _ | VA]< wl >)
    (Vy' : [Γ ||-v<l> y' : _ | _ | VA]< wl >)
    (Vyy' : [Γ ||-v<l> y ≅ y' : _ | _ | VA]< wl >)
    (VId : [Γ ||-v<l> tId A x y | VΓ]< wl >)
    (Ve : [_ ||-v<l> e : _ | _ | VId]< wl >) 
    (Ve' : [_ ||-v<l> e' : _ | _ | VId]< wl >) 
    (Vee' : [_ ||-v<l> e ≅ e' : _ | _ | VId]< wl >) 
    (VPey : [_ ||-v<l> P[e .: y ..] | VΓ]< wl >) : 
    [_ ||-v<l> P[e .: y ..] ≅ P'[e' .: y' ..] | VΓ | VPey]< wl >.
  Proof.
    assert (VId' : [Γ ||-v<l> tId A x y' | VΓ]< wl >) by now eapply IdValid.
    assert [Γ ||-v< l > e' : tId A x y' | VΓ | VId']< wl >.
    1:{
      eapply conv; tea.
      eapply IdCongValid; tea.
      1: eapply reflValidTy.
      now eapply reflValidTm.
    }
    eapply transValidTyEq.
    - eapply substExtIdElimMotive.
      2: tea. all: tea.
      Unshelve. eapply substIdElimMotive; cycle 1; tea.
    - constructor; intros; Wirrelevance0; rewrite subst_scons2; [reflexivity|].
      unshelve eapply validTyEq.
      8: tea. 1,2: tea.
      eapply idElimMotiveScons2Valid; tea.
  Qed.
    
  (* Lemma liftSubstS' {wl Γ σ Δ lF F} 
    {VΓ : [||-v Γ]} 
    {wfΔ : [|- Δ]}
    (VF : [Γ ||-v<lF> F | VΓ])
    (VΓF : [||-v Γ,, F])
    {wfΔF : [|- Δ ,, F[σ]]}
    (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ ]) :
    [Δ ,, F[σ] ||-v up_term_term σ : Γ ,, F | VΓF | wfΔF ].
  Proof.
    eapply irrelevanceSubst.
    now unshelve eapply liftSubstS'.
  Qed. *)


  Lemma IdElimValid {wl Γ l A x P hr y e}
    (VΓ : [||-v Γ]< wl >) 
    (VA : [_ ||-v<l> A | VΓ]< wl >) 
    (Vx : [_ ||-v<l> x : _ | _ | VA]< wl >)
    (VΓext : [||-v (Γ ,, A) ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)]< wl >)
    (VP : [_ ||-v<l> P | VΓext]< wl >)
    (VPhr := substIdElimMotive VΓ VA Vx VΓext VP Vx (IdValid VΓ VA Vx Vx) (reflValid VΓ VA Vx _))
    (Vhr : [_ ||-v<l> hr : _ | _ | VPhr ]< wl >)
    (Vy : [_ ||-v<l> y : _ | _ | VA]< wl >) 
    (VId : [Γ ||-v<l> tId A x y | VΓ]< wl >)
    (Ve : [_ ||-v<l> e : _ | _ | VId]< wl >)
    (VPye := substIdElimMotive VΓ VA Vx VΓext VP Vy VId Ve) :
    [_ ||-v<l> tIdElim A x P hr y e : _ | _ | VPye]< wl >.
  Proof.
    unshelve epose (h := _ : [||-v Γ,, A]< wl >). 1: now eapply validSnoc'.
    constructor; intros.
    - instValid Vσ.
      eapply (TreeTmSplit (DTree_fusion _ _ _)).
      intros wl'' Ho HA.
      pose (f':= over_tree_le Ho).
      pose (RIAxy := (WRed (tId A x y)[σ] RVId wl'' (over_tree_fusion_l Ho))).
      assert (Re: [Δ ||-< l > e[σ] : (tId A x y)[σ] | LRId' (invLRId RIAxy)]< wl'' >).
      { enough [Δ ||-< l > e[σ] : (tId A x y)[σ] | LRId' (invLRId RIAxy) ]< wl'' > by eauto.
        refold.
        irrelevanceRefl ; unshelve eapply RVe.
        1: now eapply over_tree_fusion_l.
        now eapply over_tree_fusion_r ; exact Ho.
      }
      pose proof (IdRedTy_inv (invLRId RIAxy)) as [eA ex ey] ; refold.
      pose proof (hred := Re.(IdRedTm.red)); unfold_id_outTy; rewrite <-eA,<-ex,<-ey in hred.
      unshelve epose proof (Hyp := red_idElimMotive_substupup _ _ _ _ _ _ _).
      13,17: tea.
      2: tea.
      enough (X : W[ Δ ||-< l > tIdElim A[σ] x[σ] P[up_term_term (up_term_term σ)] hr[σ] y[σ] (IdRedTm.nf Re) : P[e .: y..][σ] | HA ]< wl'' >).
      { cbn in * ; eapply WredSubstTerm.
        1: exact X.
        escape ; Wescape.
        destruct hred.
        rewrite subst_scons2, <-subst_upup_scons2.
        eapply redtm_idElim ; tea.
        1,3: now eapply wft_Ltrans.
        1,3: now eapply ty_Ltrans.
        rewrite subst_scons2 in RRVhr.
        rewrite subst_upup_scons2 ; now eapply ty_Ltrans.
      }
      pose proof (redTmFwdConv Re hred (IdProp_whnf _ _ (IdRedTm.prop Re))) as [Rnf Rnfeq].
      eapply WLRTmRedConv.
      2: unshelve eapply WidElimPropRed ; refold; tea.
      + eapply WLRTransEq.
        1: eapply substEq_idElimMotive_substupup.  
        6: now eapply TmLogtoW.
        2: eassumption.
        4: eapply WreflLRTmEq.
        2,3,4,5 : eapply WTm_Ltrans' ; [ eassumption | eassumption].
        1: eassumption.
        1: now eapply WLRTmEqSym, TmEqLogtoW.
        cbn ; Wirrelevance0 ; [ | now eapply WreflLRTyEq ] ; now bsimpl.
      + now eapply WLtrans.
      + intros.
        eapply subst_idElimMotive_substupup ; cycle 1 ; tea.
        cbn ; Wirrelevance0 ; [reflexivity | now eapply WTm_Ltrans].
      + now eapply WTm_Ltrans'.
      + now eapply WLtrans.
      + now eapply TmLogtoW'.
      + now eapply WTm_Ltrans'.
      + eapply invLRId.
        eapply RVId, over_tree_fusion_l ; exact Ho.
      + unshelve eapply red_idElimMotive_substupup.
        3: eassumption.
        4: now eapply (Validity_Ltrans' f).
        * now eapply wfc_Ltrans.
        * now eapply WfC_Ltrans.
        * eapply subst_Ltrans', subst_Ltrans ; eassumption.
        * now eapply TmValidity_Ltrans.
        * now eapply Validity_Ltrans'.
      + intros ; cbn in *.
        eapply substEq_idElimMotive_substupup ; cycle 1; tea.
        1,3: Wirrelevance.
        eapply WLRTmRedConv; tea; now eapply WLRTyEqSym.
      + cbn ; Wirrelevance0 ; [ | now eapply WTm_Ltrans].
        now bsimpl.
      + exact (IdRedTm.prop Re).
        Unshelve.
        2: rewrite subst_upup_scons2, <- subst_scons2 ; now eapply WLtrans.
        all: try now eapply wfc_Ltrans + now eapply wfLCon_le_id.
        all: tea; try now eapply wfLCon_le_trans.
        1,3,4: now eapply subst_Ltrans.
        now eapply WLtrans.
    - instAllValid Vσ Vσ' Vσσ'.
      Wirrelevance0.
      2: unshelve eapply WidElimCongRed; refold.
      1: refold; now rewrite subst_upup_scons2, subst_scons2.
      all: try now eapply WLRCumulative.
      all: tea; try now eapply WLRTmRedIrrelevantCum'.
      all: tea; try now eapply WLRTmEqIrrelevantCum'.
      all: tea; try now eapply WLRTyEqIrrelevantCum'.
      2,4: now eapply red_idElimMotive_substupup.
      + intros wl'' f' ** ; eapply subst_idElimMotive_substupup; cycle 1; tea.
        all: now eapply WLRTmRedIrrelevantCum'.
        Unshelve.
        * now eapply wfLCon_le_trans.
        * now eapply wfc_Ltrans.
        * now eapply subst_Ltrans.
        * now eapply WLRCumulative.
      + intros wl'' f' **; eapply subst_idElimMotive_substupup; cycle 1; tea.
        all: now eapply WLRTmRedIrrelevantCum'.
        Unshelve.
        * now eapply wfLCon_le_trans.
        * now eapply wfc_Ltrans.
        * now eapply subst_Ltrans.
        * now eapply WLRCumulative.
      + now eapply red_idElimMotive_substupup_cong.
      + intros wl'' f' **; eapply substEq_idElimMotive_substupupEq; cycle 2; tea.
        all: try now eapply WLRTmRedIrrelevantCum' + now eapply WLRTmEqIrrelevantCum'.
        now eapply eqsubst_Ltrans.
        Unshelve. 3,4: now eapply WLRCumulative.
        3: assumption.
        * now eapply wfc_Ltrans.
        * now eapply subst_Ltrans.
      + cbn. intros wl'' f' **.
        eapply substEq_idElimMotive_substupup; cycle 1.
        1: eassumption.
        all: try now eapply WLRTmRedIrrelevantCum' + now eapply WLRTmEqIrrelevantCum'.
        2: eassumption.
        eapply WLRTmRedConv ; [ now eapply WLRTyEqSym, WLRTyEqIrrelevantCum' | ].
        now eapply WLRTmRedIrrelevantCum'.
    +  Set Printing Primitive Projection Parameters.
       intros; eapply substEq_idElimMotive_substupup; cycle 1; tea.
       all: try now eapply WLRTmRedIrrelevantCum'.
       all: try now eapply WLRTmEqIrrelevantCum'.
       eapply WLRTmRedConv; [| now eapply WLRTmRedIrrelevantCum'].
       eapply WLRTyEqSym ; now eapply WLRTyEqIrrelevantCum'.
    + cbn ; Wirrelevance0 ; [ | eassumption] ; now rewrite subst_upup_scons2, subst_scons2.
    + cbn ; Wirrelevance0 ; [ | eassumption] ; now rewrite subst_upup_scons2, subst_scons2.
    + cbn ; Wirrelevance0 ; [ | eassumption] ; now rewrite subst_upup_scons2, subst_scons2.
      Unshelve. all: tea.
      all: try now eapply wfc_Ltrans + now eapply wfLCon_le_trans.
      all: try now eapply WLtrans + now eapply subst_Ltrans.
      all: try now eapply WLRCumulative.
  Qed.

  Lemma IdElimCongValid {wl Γ l A A' x x' P P' hr hr' y y' e e'}
    (VΓ : [||-v Γ]< wl >) 
    (VA : [_ ||-v<l> A | VΓ]< wl >) 
    (VA' : [_ ||-v<l> A' | VΓ]< wl >) 
    (VAA' : [_ ||-v<l> A ≅ A' | _ | VA]< wl >)
    (Vx : [_ ||-v<l> x : _ | _ | VA]< wl >)
    (Vx' : [_ ||-v<l> x' : _ | _ | VA]< wl >)
    (Vxx' : [_ ||-v<l> x ≅ x' : _ | _ | VA]< wl >)
    (VΓext : [||-v (Γ ,, A) ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)]< wl >)
    (VP : [_ ||-v<l> P | VΓext]< wl >)
    (VP' : [_ ||-v<l> P' | VΓext]< wl >)
    (VPP' : [_ ||-v<l> P ≅ P' | _ | VP]< wl >)
    (VPhr := substIdElimMotive VΓ VA Vx VΓext VP Vx (IdValid VΓ VA Vx Vx) (reflValid VΓ VA Vx _))
    (Vhr : [_ ||-v<l> hr : _ | _ | VPhr ]< wl >)
    (Vhr' : [_ ||-v<l> hr' : _ | _ | VPhr ]< wl >)
    (Vhrhr' : [_ ||-v<l> hr ≅ hr' : _ | _ | VPhr]< wl >)
    (Vy : [_ ||-v<l> y : _ | _ | VA]< wl >) 
    (Vy' : [_ ||-v<l> y' : _ | _ | VA]< wl >) 
    (Vyy' : [_ ||-v<l> y ≅ y' : _ | _ | VA]< wl >) 
    (VId : [Γ ||-v<l> tId A x y | VΓ]< wl >)
    (Ve : [_ ||-v<l> e : _ | _ | VId]< wl >)
    (Ve' : [_ ||-v<l> e' : _ | _ | VId]< wl >)
    (Vee' : [_ ||-v<l> e ≅ e' : _ | _ | VId]< wl >)
    (VPye := substIdElimMotive VΓ VA Vx VΓext VP Vy VId Ve) :
    [_ ||-v<l> tIdElim A x P hr y e ≅ tIdElim A' x' P' hr' y' e' : _ | _ | VPye]< wl >.
  Proof.
    assert [_ ||-v<l> x' : _ | _ | VA']< wl > by now eapply conv.
    assert [_ ||-v<l> y' : _ | _ | VA']< wl > by now eapply conv.
    assert (VΓext' : [||-v (Γ ,, A'),, tId A'⟨@wk1 Γ A'⟩ x'⟨@wk1 Γ A'⟩ (tRel 0)]< wl >).
    1: eapply validSnoc'; now eapply idElimMotiveCtxIdValid.
    assert (h : forall t, t⟨@wk1 Γ A'⟩ = t⟨@wk1 Γ A⟩) by reflexivity.
    assert (VPalt' : [_ ||-v<l> P' | VΓext']< wl >).
    1:{
      eapply convCtx2'; tea.
      1: eapply convCtx1; tea; [now eapply symValidTyEq| ].
      1,3: now eapply idElimMotiveCtxIdValid.
      eapply idElimMotiveCtxIdCongValid; tea.
      Unshelve. 1: now eapply idElimMotiveCtxIdValid. tea.
    }
    constructor; intros.
    instValid Vσ.
    Wirrelevance0.
    2: unshelve eapply WidElimCongRed; refold.
    1: refold; now rewrite subst_upup_scons2, subst_scons2.
    all: first [now eapply WLRCumulative | solve [Wirrelevance | WirrelevanceCum] | now eapply WLRTmRedConv | tea].

    + intros ; eapply subst_idElimMotive_substupup; cycle 1; tea; WirrelevanceCum.
      Unshelve. all: tea.
      * now eapply wfLCon_le_trans.
      * now eapply wfc_Ltrans.
      * now eapply subst_Ltrans.
      * WirrelevanceCum.
    + eapply WLRTmRedConv; [ | now WirrelevanceCum].
      WirrelevanceCum.
    + eapply red_idElimMotive_substupup ; tea.
    + intros; eapply subst_idElimMotive_substupup; cycle 1; tea.
      1,2: WirrelevanceCum.
      Unshelve. all: tea.
      1,5: WirrelevanceCum.
      * now eapply wfLCon_le_trans.
      * now eapply wfc_Ltrans.
      * now eapply subst_Ltrans.
    + unshelve eapply WIdRed; tea.
      1,2: now WirrelevanceCum0.
      eapply WLRTmRedConv; now WirrelevanceCum0.
    + eapply red_idElimMotive_substupup; tea.
    + eapply redEq_idElimMotive_substupup.
      6-8: tea. 3-5: tea. all: tea.
    + intros wl'' f' **.
      assert W[_ ||-<l> y'0 : _ | (WLtrans f' RVA)]< wl'' >.
      { eapply WLRTmRedConv; tea ; [ eapply WLRTyEqSym | ].
        2: now WirrelevanceCum0.
        now eapply WEq_Ltrans.
      }
      eapply substExt_idElimMotive_substupup.
      7: tea. 2,3,5,6: tea. all: tea; try solve [WirrelevanceCum].
      1: eapply WLRTmRedConv; tea; [ eapply WLRTyEqSym | ] ; tea.
      2: now WirrelevanceCum0.
      eapply WIdCongRed; tea; [now Wescape|.. | now eapply WreflLRTmEq].
      1: now eapply WEq_Ltrans.
      now eapply WTmEq_Ltrans.
      Unshelve. 2: now eapply WLRCumulative.
      all: try now eapply WLtrans + now WirrelevanceCum0 + tea.
      1: now eapply wfLCon_le_trans.
      1: now eapply wfc_Ltrans.
      1: now eapply subst_Ltrans.
      1,2: eapply WIdRed ; eauto.
      all: now eapply WTm_Ltrans.
    + intros; eapply substEq_idElimMotive_substupup; cycle 1; tea;
        try solve [WirrelevanceCum].
      eapply WLRTmRedConv. 2:WirrelevanceCum.
      eapply WLRTyEqSym; WirrelevanceCum.
      Unshelve. all: tea ; try now eapply WLRCumulative.
      1: now eapply wfLCon_le_trans.
      1: now eapply wfc_Ltrans.
      1: now eapply subst_Ltrans.
    + intros; eapply substEq_idElimMotive_substupup; cycle 1; tea;
        try solve [WirrelevanceCum].
      eapply WLRTmRedConv. 2:WirrelevanceCum.
      eapply WLRTyEqSym; WirrelevanceCum.
      Unshelve. all: tea; try now eapply WLRCumulative.
      1: now eapply wfLCon_le_trans.
      1: now eapply wfc_Ltrans.
      1: now eapply subst_Ltrans.
    + eapply WLRTmRedConv; tea.
      rewrite subst_upup_scons2; change (tRefl A'[σ] x'[σ]) with (tRefl A' x')[σ].
      rewrite <- subst_scons2.
      eapply validTyEq. eapply substEqIdElimMotive.
      6,7: tea.  5-8: tea. 2-4: tea. 1: tea.
      2: eapply conv.
      1,3: now eapply reflValid.
      1: eapply symValidTyEq; now eapply IdCongValid.
      now eapply reflCongValid.
      Unshelve. all: now eapply IdValid.
    + eapply WLRTmRedConv; tea.
      2: now WirrelevanceCum0.
      now WirrelevanceCum.
    + eapply WLRTmRedConv; tea.
      2: now WirrelevanceCum0.
      1: WirrelevanceCum0 ; [reflexivity | ].
      now eapply IdCongValid ; tea.
      Unshelve.
      all: tea.
      1,2: now WirrelevanceCum0.
  Qed.


  Lemma IdElimReflValid {wl Γ l A x P hr y B z}
    (VΓ : [||-v Γ]< wl >) 
    (VA : [_ ||-v<l> A | VΓ]< wl >) 
    (Vx : [_ ||-v<l> x : _ | _ | VA]< wl >)
    (VΓext : [||-v (Γ ,, A) ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)]< wl >)
    (VP : [_ ||-v<l> P | VΓext]< wl >)
    (VPhr := substIdElimMotive VΓ VA Vx VΓext VP Vx (IdValid VΓ VA Vx Vx) (reflValid VΓ VA Vx _))
    (Vhr : [_ ||-v<l> hr : _ | _ | VPhr ]< wl >)
    (Vy : [_ ||-v<l> y : _ | _ | VA]< wl >) 
    (Vxy : [_ ||-v<l> x ≅ y : _ | _ | VA]< wl >) 
    (VB : [_ ||-v<l> B | VΓ]< wl >)
    (VAB : [_ ||-v<l> _ ≅ B | VΓ | VA]< wl >)
    (Vz : [_ ||-v<l> z : _ | _ | VB]< wl >) 
    (Vxz : [_ ||-v<l> x ≅ z : _ | _ | VA]< wl >) 
    (VId : [Γ ||-v<l> tId A x y | VΓ]< wl >) 
    (VRefl : [_ ||-v<l> tRefl B z : _ | _ | VId]< wl >)
    (VPye := substIdElimMotive VΓ VA Vx VΓext VP Vy VId VRefl) :
    [_ ||-v<l> tIdElim A x P hr y (tRefl B z) ≅ hr : _ | _ | VPye]< wl >.
  Proof.
    constructor; intros.
    assert [Γ ||-v< l > P[tRefl A x .: x..] ≅ P[tRefl B z .: y..] | VΓ | VPhr]< wl >.
    1:{
      eapply substExtIdElimMotive; cycle 1; tea.
      1: now eapply reflValid.
      eapply reflCongValid; tea.
      eapply conv; tea.
      now eapply symValidTyEq.
      Unshelve. now eapply IdValid.
    }
    eapply redwfSubstValid; cycle 1.
    + eapply conv; tea.
    + constructor; intros.
      instValid Vσ0; Wescape.
      constructor.
      - eapply ty_conv; now tea.
      - rewrite subst_scons2, <- subst_upup_scons2.
        eapply redtm_idElimRefl; refold; tea.
        * eapply Wescape. now eapply red_idElimMotive_substupup.
        * rewrite subst_upup_scons2; change (tRefl ?A[?σ] ?x[_]) with (tRefl A x)[σ].
          now rewrite <- subst_scons2.
        * now eapply ty_conv.
  Qed.

End Id.


  

