From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations LContexts Context NormalForms Weakening
  GenericTyping Monad LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Escape Reflexivity Neutral Weakening Monotonicity Irrelevance Application Reduction Transitivity NormalRed.
From LogRel.Substitution Require Import Irrelevance Monotonicity Properties SingleSubst.
From LogRel.Substitution.Introductions Require Import Pi.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.


Section LambdaValid.
Context `{GenericTypingProperties}.





Context {Γ wl F G l} {VΓ : [||-v Γ]< wl >} (VF : [Γ ||-v<l> F | VΓ]< wl >) 
  (VΓF := validSnoc' VΓ VF)
  (VG : [Γ ,, F ||-v<l> G | VΓF]< wl >)
  (VΠFG := PiValid VΓ VF VG).


Lemma consWkEq {Δ Ξ} σ (ρ : Δ ≤ Ξ) a Z : Z[up_term_term σ]⟨wk_up F[σ] ρ⟩[a..] = Z[a .: σ⟨ρ⟩].
Proof. bsimpl; cbn; now rewrite rinstInst'_term_pointwise. Qed.

Lemma consWkEq' {Δ Ξ} σ (ρ : Δ ≤ Ξ) a Z : Z[up_term_term σ][a .: ρ >> tRel] = Z[a .: σ⟨ρ⟩].
Proof. bsimpl; cbn; now rewrite rinstInst'_term_pointwise. Qed.

Lemma lamBetaRed {t} (Vt : [Γ ,, F ||-v<l> t : G | VΓF | VG]< wl >) 
  {Δ σ wl' f} (wfΔ : [ |-[ ta ] Δ]< wl' >) (Vσ : [VΓ | Δ ||-v σ : Γ | wfΔ | f]< wl >) 
  {Δ0 a} (ρ : Δ0 ≤ Δ) (wfΔ0 : [|-Δ0]< wl' >)
  (RFσ : [Δ0 ||-<l> F[σ]⟨ρ⟩]< wl' >) 
  (ha : [RFσ | _ ||- a : _]< wl' >)
  (RGσ : W[Δ0 ||-<l> G[up_term_term σ][a .: ρ >> tRel]]< wl' >) :
    W[_ ||-<l> tApp (tLambda F t)[σ]⟨ρ⟩ a : _ | RGσ]< wl' > × 
    W[_ ||-<l> tApp (tLambda F t)[σ]⟨ρ⟩ a ≅ t[a .: σ⟨ρ⟩] : _ | RGσ]< wl' >.
Proof.
  pose proof (Vσa := consWkSubstS VF ρ wfΔ0 Vσ (TmLogtoW _ ha)); instValid Vσa.
  pose proof (VσUp :=  liftSubstS' VF Vσ).
  instValid Vσ ; instValid VσUp ; escape ; Wescape.
  split.
  all: Wirrelevance0 ; [ now rewrite consWkEq' | ].
  all: eapply WredwfSubstTerm; tea.
  all: constructor; tea.
  all: do 2 rewrite <- consWkEq.
  all: eapply redtm_beta; tea.
  all: fold subst_term; renToWk ; eapply ty_wk; tea.
  all: eapply wfc_cons; tea; eapply wft_wk; tea.
Qed.

Lemma betaValid {t a} (Vt : [Γ ,, F ||-v<l> t : G | VΓF | VG]< wl >) 
  (Va : [Γ ||-v<l> a : F | VΓ | VF]< wl >) :
  [Γ ||-v<l> tApp (tLambda F t) a ≅ t[a..] : G[a..] | VΓ | substS VG Va]< wl >.
Proof.
  constructor; intros. instValid Vσ.
  pose (Vσa := consSubstS _ _ Vσ _ RVa). instValid Vσa.
  pose proof (VσUp :=  liftSubstS' VF Vσ).
  instValid Vσ. instValid VσUp. escape ; Wescape.
  assert (eq : forall t, t[a..][σ] = t[up_term_term σ][a[σ]..]) by (intros; now bsimpl).
  assert (eq' : forall t, t[a..][σ] = t[a[σ].: σ]) by (intros; now bsimpl).
  Wirrelevance0. 1: symmetry; apply eq.
  rewrite eq;  eapply WredwfSubstTerm; tea.
  1: rewrite <- eq; rewrite eq'; Wirrelevance.
  constructor; tea.
  * do 2 (rewrite <- eq; rewrite eq'); tea.
  * eapply redtm_beta; tea.
    Unshelve. 2:rewrite <- eq; now rewrite eq'.
Qed.

Lemma lamValid0 {t} (Vt : [Γ ,, F ||-v<l> t : G | VΓF | VG]< wl >) 
  {Δ σ wl' f} (wfΔ : [ |-[ ta ] Δ]< wl' >) (Vσ : [VΓ | Δ ||-v σ : Γ | wfΔ | f]< wl >) :
  W[Δ ||-< l > (tLambda F t)[σ] : (tProd F G)[σ] | validTy VΠFG f wfΔ Vσ]< wl' >.
Proof.
  pose proof (VσUp :=  liftSubstS' VF Vσ).
  instValid Vσ. instValid VσUp. Wescape ; escape.
  pose (RΠ := WnormRedΠ RVΠFG); refold.
  enough W[Δ ||-< l > (tLambda F t)[σ] : (tProd F G)[σ] | RΠ]< wl' > by Wirrelevance.
  assert [Δ |- (tLambda F t)[σ] : (tProd F G)[σ]]< wl' > by (Wescape; cbn; gen_typing).
  unshelve econstructor.
  1: now constructor.
  intros wl'' Hover Hover' ; cbn.
  pose proof (f' := over_tree_le Hover).
  unshelve eexists (tLambda F t)[σ] _ _ ; intros; cbn in *.
  1: shelve.
  - do 2 eapply DTree_fusion ; [ .. | eapply DTree_fusion | eapply DTree_fusion].
    all: shelve.
  - now eapply redtmwf_refl, ty_Ltrans.
  - eapply convtm_eta; tea.
    1,2: now eapply wft_Ltrans.
    1,3: now eapply ty_Ltrans.
    1,2: constructor; tea; try now eapply wft_Ltrans.
    1,4: now eapply convty_Ltrans ; [ eassumption | eapply WescapeEq, WreflLRTyEq].
    1-4: now eapply ty_Ltrans.
    assert (eqσ : forall Z, Z[up_term_term σ] = Z[up_term_term σ]⟨upRen_term_term S⟩[(tRel 0) ..])
    by (intro; bsimpl; cbn; now rewrite rinstInst'_term_pointwise).
    assert [Δ,, F[σ] |-[ ta ] tApp (tLambda F[σ] t[up_term_term σ])⟨S⟩ (tRel 0) ⤳*  t[up_term_term σ]⟨upRen_term_term S⟩[(tRel 0)..] : G[up_term_term σ]]< wl' >.
    {
      rewrite (eqσ G). eapply redtm_beta.
      * renToWk; eapply wft_wk; tea; gen_typing.
      * renToWk; eapply ty_wk; tea.
        eapply wfc_cons; [gen_typing | eapply wft_wk; gen_typing].
      * fold ren_term; refine (ty_var _ (in_here _ _)); gen_typing.
    }
    eapply convtm_Ltrans ; [eassumption |].
    eapply convtm_exp; tea.
    + rewrite <- eqσ; tea.
    + rewrite <- eqσ; tea.
    + unshelve eapply WescapeEq, WreflLRTyEq; [|tea].
    + rewrite <- (eqσ t); eapply WescapeEqTerm; now eapply WreflLRTmEq.
  - cbn.
    econstructor 1 ; cbn; intros.
    + apply reflLRTyEq.
    + rewrite Poly.eq_subst_2.
      irrelevance0; [symmetry; apply Poly.eq_subst_2|].
      unshelve eapply (validTm Vt _ h _) ; tea.
      1: exact (f0 •ε (f' •ε f)).
      eapply consSubstS ; Wirrelevance0; [|eapply TmLogtoW ; tea].
      now bsimpl.
      * eapply over_tree_fusion_l ; exact Ho'.
      * eapply over_tree_fusion_r ; exact Ho'.
        Unshelve.
        1-7: shelve.
        2,4: eassumption.
        change ([VΓ | Δ0 ||-v σ⟨ρ⟩ : Γ | h | (f0 •ε f') •ε f ]< wl >).
        unshelve eapply wkSubstS ; [ | now eapply subst_Ltrans].
        now eapply wfc_Ltrans ; [exact (f0 •ε f') | ].
  - cbn in *.
    set (Helper := PolyRed.posRed _ _ _ _).
    irrelevance0 ; [ reflexivity | ].
    unshelve eapply (WRedTm _ (fst (lamBetaRed Vt _ _ _ _ _ ha _))).
    1: econstructor ; intros wl''' Ho'' ; eapply Helper ; exact Ho''. 
    all: unfold Helper ; clear Helper ; cbn.
    + exact ((f0 •ε f') •ε f).
    + now eapply wfc_Ltrans ; [exact (f0 •ε f') | ].
    + now eapply subst_Ltrans.
    + eassumption.
    + exact Ho.
    + exact Ho'.
  - cbn in *.
    epose  (Vσa := consWkSubstS VF ρ Hd (subst_Ltrans (f0 •ε f') _ Vσ) (TmLogtoW _ ha)).
    epose  (Vσb := consWkSubstS VF ρ Hd (subst_Ltrans (f0 •ε f') _ Vσ) (TmLogtoW _ hb)).
    unshelve refine (let Vσab : [_ ||-v _ ≅ (b .: σ⟨ρ⟩) : _ | _ | _ | Vσa | _]< wl > := _ in _).
    1:{ unshelve eapply consSubstSEq'.
        1,3: enough (equal : F[σ⟨ρ⟩] = F[σ]⟨ρ⟩) ; [ | now bsimpl].
        1,2 : Wirrelevance0 ; [rewrite equal ; reflexivity | ].
        1: eapply TmLogtoW ; exact ha.
        1: eapply TmEqLogtoW ; exact eq.
        unshelve eapply irrelevanceSubstEq ; [eassumption | eassumption | ..].
        2: eapply wkSubstSEq.
        unshelve eapply reflSubst.
        Unshelve. 1-6: shelve.
        4: now eapply subst_Ltrans.
        all: now eapply wfc_Ltrans ; [exact (f0 •ε f') | ].
      }
      eapply LREqTermHelper ; [ irrelevanceRefl | ..].
    1,2: eapply (WRedTmEq _ (snd (lamBetaRed Vt _ _ _ _ _ _ _))).
    1: eapply over_tree_fusion_l, over_tree_fusion_l ; exact Hoeq.
    1: eapply over_tree_fusion_r, over_tree_fusion_l ; exact Hoeq.
    + irrelevance0; rewrite consWkEq';[reflexivity|].
      unshelve eapply validTyExt ; cycle 6; tea.
      1: eapply over_tree_fusion_l, over_tree_fusion_l, over_tree_fusion_r ; exact Hoeq.
      1: eapply over_tree_fusion_r, over_tree_fusion_l, over_tree_fusion_r ; exact Hoeq.
      Unshelve.
      1,2: shelve.
      1: eapply over_tree_fusion_l, over_tree_fusion_r, over_tree_fusion_r ; exact Hoeq.
      1: eapply over_tree_fusion_l ; do 3 (eapply over_tree_fusion_r) ; exact Hoeq.
      1,8: rewrite consWkEq'; eapply validTy; tea.
      all: try eassumption.
      2,5: now eapply wfc_Ltrans ; [exact (f0 •ε f') | ].
      1,3: exact ((f0 •ε f') •ε f).
      1,2: now eapply subst_Ltrans.
    + epose (X := validTmExt Vt _ _ _ Vσb Vσab).
      irrelevance0 ; [ | eapply (WRedTmEq _ X)].
      1: now rewrite consWkEq'.      
      1: eapply over_tree_fusion_r ; do 3 (eapply over_tree_fusion_r) ; exact Hoeq.
      Unshelve.
      1: eapply over_tree_fusion_l, over_tree_fusion_l, over_tree_fusion_r ; exact Hoeq.
Qed.

Lemma lamValid {t} (Vt : [Γ ,, F ||-v<l> t : G | VΓF | VG]< wl >)
   :
    [Γ ||-v<l> tLambda F t : tProd F G | VΓ | VΠFG ]< wl >.
Proof.
  opector. 1: intros ;  now apply lamValid0.
  intros.
  pose (VσUp :=  liftSubstS' VF Vσ).
  pose proof (VσUp' :=  liftSubstS' VF Vσ').
  pose proof (VσUprea :=  liftSubstSrealign' VF Vσσ' Vσ').
  pose proof (VσσUp := liftSubstSEq' VF Vσσ').
  instAllValid Vσ Vσ' Vσσ';  instValid VσUp'; instAllValid VσUp VσUprea VσσUp.
  pose (RΠ := normRedΠ RVΠFG); refold.
  enough [RΠ | Δ ||- (tLambda F t)[σ] ≅ (tLambda F t)[σ'] : (tProd F G)[σ]]< wl > by irrelevance.
  unshelve econstructor.
  - change [RΠ | Δ ||- (tLambda F t)[σ] : (tProd F G)[σ]]< wl >.
    eapply normLambda.
    epose (lamValid0 Vt wfΔ Vσ).
    irrelevance.
  - change [RΠ | Δ ||- (tLambda F t)[σ'] : (tProd F G)[σ]]< wl >.
    eapply normLambda.
    eapply LRTmRedConv.
    2: epose (lamValid0 Vt wfΔ Vσ'); irrelevance.
    eapply LRTyEqSym. eapply (validTyExt VΠFG); tea.
    Unshelve. 2: now eapply validTy.
  - refold; cbn; escape.
    eapply convtm_eta; refold; tea.
    2,4: constructor; first [assumption|now eapply lrefl|idtac].
    + gen_typing.
    + eapply ty_conv; [tea|now symmetry].
    + eapply ty_conv; [tea|].
      assert (Vσ'σ := symmetrySubstEq _ _ _ _ _ Vσ' Vσσ').
      assert (Vupσ'σ := liftSubstSEq' VF Vσ'σ).
      unshelve eassert (VG' := validTyExt VG _ _ _ Vupσ'σ).
      { eapply liftSubstSrealign'; tea. }
      eapply escapeEq, VG'.
    + eapply ty_conv; [now eapply ty_lam|].
      symmetry; now eapply convty_prod.
    + assert (eqσ : forall σ Z, Z[up_term_term σ] = Z[up_term_term σ]⟨upRen_term_term S⟩[(tRel 0) ..])
      by (intros; bsimpl; cbn; now rewrite rinstInst'_term_pointwise).
      eapply convtm_exp.
      * rewrite (eqσ σ G). eapply redtm_beta.
        -- renToWk; eapply wft_wk; tea; gen_typing.
        -- renToWk; eapply ty_wk; tea.
           eapply wfc_cons; [gen_typing | eapply wft_wk; gen_typing].
        -- fold ren_term; refine (ty_var _ (in_here _ _)); gen_typing.
      * eapply redtm_conv.  2: now symmetry.
        rewrite (eqσ σ' G). eapply redtm_beta.
        -- renToWk; eapply wft_wk; tea; gen_typing.
        -- renToWk; eapply ty_wk; tea.
           eapply wfc_cons; [gen_typing | eapply wft_wk; gen_typing].
        -- fold ren_term. eapply ty_conv.
           refine (ty_var _ (in_here _ _)). 1: gen_typing.
           cbn; renToWk; eapply convty_wk; tea; gen_typing.
      * tea.
      * fold ren_term; rewrite <- eqσ; tea.
      * fold ren_term; rewrite <- eqσ.
        eapply ty_conv; [tea|symmetry; tea].
      * now eapply lrefl.
      * fold ren_term. 
        set (x := ren_term _ _); change x with (t[up_term_term σ]⟨upRen_term_term S⟩); clear x.
        set (x := ren_term _ _); change x with (t[up_term_term σ']⟨upRen_term_term S⟩); clear x.
        do 2 rewrite <- eqσ ; eapply escapeEqTerm; now eapply validTmExt.
  - refold; cbn; intros.
    pose proof (Vσa := consWkSubstS VF ρ h Vσ ha).
    assert (ha' : [ _||-<l> a : _| wk ρ h RVF0]< wl >).
    1: {
      eapply LRTmRedConv; tea.
      irrelevance0; [reflexivity|].
      eapply wkEq; eapply (validTyExt VF); tea.
    }
    pose proof (Vσa' := consWkSubstS VF ρ h Vσ' ha').
    assert (Vσσa : [_ ||-v _ ≅ (a .: σ'⟨ρ⟩) : _ | _ | _ | Vσa]< wl >).
    {
      unshelve eapply consSubstSEq'.
      2: eapply reflLRTmEq; irrelevance0; [|exact ha]; now bsimpl.
      eapply irrelevanceSubstEq; now eapply wkSubstSEq.
      Unshelve. all: tea.
    }
    eapply LREqTermHelper.
    1,2: eapply lamBetaRed; tea.
    + irrelevance0; rewrite consWkEq';[reflexivity|].
      unshelve eapply validTyExt; cycle 3; tea. 
      Unshelve. rewrite consWkEq'; eapply validTy; tea.
    + epose proof (validTmExt Vt _ _ Vσa' Vσσa).
      irrelevance. now rewrite consWkEq'.
Qed.



Lemma ηeqEqTermConvNf {σ Δ f} (ρ := @wk1 Γ F)
  (wfΔ : [|- Δ]< wl >) (Vσ : [Δ ||-v σ : Γ | VΓ| wfΔ]< wl >)
  (RΠFG := normRedΠ (validTy VΠFG wfΔ Vσ))
  (Rf : [Δ ||-<l> f[σ] : (tProd F G)[σ] | RΠFG ]< wl >) :
  [Δ ,, F[σ] |- tApp f⟨ρ⟩[up_term_term σ] (tRel 0) ≅ tApp (PiRedTm.nf Rf)⟨↑⟩ (tRel 0) : G[up_term_term σ]]< wl >.
Proof.
  refold.
  pose (VσUp :=  liftSubstS' VF Vσ).
  instValid Vσ; instValid VσUp; escape.
  destruct (PiRedTm.red Rf); cbn in *.
  assert (wfΔF : [|- Δ,, F[σ]]< wl >) by gen_typing.
  unshelve epose proof (r := PiRedTm.app Rf (@wk1 Δ F[σ]) wfΔF (var0 _ _ _)).
  1: now rewrite wk1_ren_on.
  assumption.
  assert (eqσ : forall σ Z, Z[up_term_term σ] = Z[up_term_term σ][(tRel 0) .: @wk1 Δ F[σ] >> tRel])
  by (intros; bsimpl; cbn; now rewrite rinstInst'_term_pointwise).
  eapply convtm_exp. 
  7: rewrite eqσ; eapply escapeEqTerm; eapply reflLRTmEq; irrelevance.
  * eapply redtm_meta_conv. 3: reflexivity.
    1: eapply redtm_app.
    2: eapply (ty_var wfΔF (in_here _ _)).
    1:{
      replace (f⟨_⟩[_]) with f[σ]⟨@wk1 Δ F[σ]⟩ by (unfold ρ; now bsimpl).
      eapply redtm_meta_conv. 3: reflexivity.
      1: eapply redtm_wk; tea.
      now rewrite wk1_ren_on.
    }
    fold ren_term. rewrite eqσ; now bsimpl. 
  * rewrite <- (wk1_ren_on Δ F[σ]); unshelve eapply redtmwf_refl.
    rewrite eqσ; eapply escapeTerm ; irrelevance.
    Unshelve. 2,4: rewrite <- eqσ; tea.
  * tea.
  * rewrite eqσ; eapply escapeTerm ; irrelevance.
    Unshelve. 2: rewrite <- eqσ; tea.
  * rewrite eqσ; eapply escapeTerm ; irrelevance.
    Unshelve. 2: rewrite <- eqσ; tea.
  * unshelve eapply escapeEq, reflLRTyEq; [|tea].
Qed.

Lemma isLRFun_isWfFun : forall {σ Δ f} (wfΔ : [|- Δ]< wl >) (vσ : [Δ ||-v σ : Γ | VΓ | wfΔ]< wl >) (RΠFG : [Δ ||-< l > (tProd F G)[σ]]< wl >)
  (p : [Δ ||-Π f[σ] : tProd F[σ] G[up_term_term σ] | normRedΠ0 (Induction.invLRΠ RΠFG)]< wl >),
  isWfFun Δ F[σ] G[up_term_term σ] (PiRedTm.nf p).
Proof.
intros.
instValid vσ.
destruct RΠFG; simpl in *.
destruct p as [nf ? isfun]; simpl in *.
destruct isfun as [A t vA vt|]; simpl in *; constructor; tea.
+ rewrite <- (@wk_id_ren_on Δ).
  unshelve eapply escapeConv, vA; tea.
+ rewrite <- (wk_id_ren_on Δ F[σ]), <- (wk_id_ren_on Δ A).
  now unshelve eapply escapeEq, vA.
+ assert (Hrw : forall t, t[tRel 0 .: @wk1 Δ A >> tRel] = t).
  { intros; bsimpl; apply idSubst_term; intros []; reflexivity. }
  assert [Δ |- F[σ]]< wl > by now eapply escape.
  assert (wfΔF : [|- Δ,, F[σ]]< wl >) by now apply wfc_cons.
  unshelve eassert (vt0 := vt _ (tRel 0) (@wk1 Δ F[σ]) _ _); tea.
  { eapply var0; [now bsimpl|tea]. }
  eapply escapeTerm in vt0.
  now rewrite !Hrw in vt0.
+ assert (Hrw : forall t, t[tRel 0 .: @wk1 Δ A >> tRel] = t).
  { intros; bsimpl; apply idSubst_term; intros []; reflexivity. }
  assert [Δ |- A].
  { rewrite <- (@wk_id_ren_on Δ).
    unshelve eapply escapeConv, vA; tea. }
  assert (wfΔA : [|- Δ,, A]< wl >) by now apply wfc_cons.
  assert [Δ |-[ ta ] A ≅ F[σ]]< wl >.
  { rewrite <- (wk_id_ren_on Δ F[σ]), <- (wk_id_ren_on Δ A).
    symmetry; now unshelve eapply escapeEq, vA. }
  assert [Δ,, A ||-< l > G[up_term_term σ]]< wl >.
  { eapply validTy with (wfΔ := wfΔA); tea.
    unshelve econstructor; [shelve|]; cbn.
    apply var0conv; [|tea].
    replace F[↑ >> up_term_term σ] with F[σ]⟨@wk1 Δ A⟩ by now bsimpl.
    rewrite <- (wk1_ren_on Δ A); eapply convty_wk; tea.
    Unshelve.
    eapply irrelevanceSubstExt with (σ := σ⟨@wk1 Δ A⟩).
    { now bsimpl. }
    now eapply wkSubstS.
  }
  rewrite <- (Hrw t); eapply escapeTerm.
  irrelevance0; [apply Hrw|unshelve apply vt].
  - apply wfc_cons; tea.
  - apply var0conv; tea.
    rewrite <- (wk1_ren_on Δ A A).
    apply convty_wk; [now apply wfc_cons|].
    rewrite <- (wk_id_ren_on Δ F[σ]), <- (wk_id_ren_on Δ A).
    symmetry; now unshelve eapply escapeEq, vA.
  Unshelve.
  all: tea.
Qed.

Lemma ηeqEqTerm {σ Δ f g} (ρ := @wk1 Γ F)
  (Vfg : [Γ ,, F ||-v<l> tApp f⟨ρ⟩ (tRel 0) ≅ tApp g⟨ρ⟩ (tRel 0) : G | VΓF | VG ]< wl >)
  (wfΔ : [|- Δ]< wl >) (Vσ : [Δ ||-v σ : Γ | VΓ| wfΔ]< wl >)
  (RΠFG := validTy VΠFG wfΔ Vσ)
  (Rf : [Δ ||-<l> f[σ] : (tProd F G)[σ] | RΠFG ]< wl >)
  (Rg : [Δ ||-<l> g[σ] : (tProd F G)[σ] | RΠFG ]< wl >) :
  [Δ ||-<l> f[σ] ≅ g[σ] : (tProd F G)[σ] | RΠFG ]< wl >.
Proof.
  set (RΠ := normRedΠ RΠFG); refold.
  enough [Δ ||-<l> f[σ] ≅ g[σ] : (tProd F G)[σ] | RΠ ]< wl > by irrelevance.
  opector.
  - change [Δ ||-<l> f[σ] : (tProd F G)[σ] | RΠ ]< wl >; irrelevance.
  - change [Δ ||-<l> g[σ] : (tProd F G)[σ] | RΠ ]< wl >; irrelevance.
  - cbn; pose (VσUp :=  liftSubstS' VF Vσ).
    instValid Vσ; instValid VσUp; escape.
    eapply convtm_eta; tea.
    + destruct (PiRedTm.red p0); cbn in *; tea.
    + now eapply isLRFun_isWfFun.
    + destruct (PiRedTm.red p); cbn in *; tea.
    + now eapply isLRFun_isWfFun.
    + etransitivity ; [symmetry| etransitivity]; tea; eapply ηeqEqTermConvNf.
  - match goal with H : [_ ||-Π f[σ] : _ | _]< wl > |- _ => rename H into Rfσ end.
    match goal with H : [_ ||-Π g[σ] : _ | _]< wl > |- _ => rename H into Rgσ end.
    cbn; intros ?? ρ' h ha.
    set (ν := (a .: σ⟨ρ'⟩)).
    pose (Vν := consWkSubstS VF ρ' h Vσ ha).
    instValid Vσ; instValid Vν; escape.
    assert (wfΔF : [|- Δ,, F[σ]]< wl >) by gen_typing.
    cbn in *.
    assert (eq : forall t, t⟨ρ⟩[a .: σ⟨ρ'⟩] = t[σ]⟨ρ'⟩) by (intros; unfold ρ; now bsimpl).
    do 2 rewrite eq in RVfg.
    eapply transEqTerm; [|eapply transEqTerm].
    2: irrelevance; symmetry; apply consWkEq'.
    + eapply LRTmEqSym; eapply redwfSubstTerm.
      1: unshelve epose proof (r := PiRedTm.app Rfσ ρ' h ha); irrelevance.
      eapply redtmwf_appwk; tea.
      1: exact (PiRedTm.red Rfσ).
      now bsimpl.
    + eapply redwfSubstTerm.
      1: unshelve epose proof (r := PiRedTm.app Rgσ ρ' h ha); irrelevance.
      eapply redtmwf_appwk; tea.
      1: exact (PiRedTm.red Rgσ).
      now bsimpl.
Qed.

Lemma etaeqValid {f g} (ρ := @wk1 Γ F)
  (Vf : [Γ ||-v<l> f : tProd F G | VΓ | VΠFG ]< wl >)
  (Vg : [Γ ||-v<l> g : tProd F G | VΓ | VΠFG ]< wl >) 
  (Vfg : [Γ ,, F ||-v<l> tApp f⟨ρ⟩ (tRel 0) ≅ tApp g⟨ρ⟩ (tRel 0) : G | VΓF | VG ]< wl >) :
  [Γ ||-v<l> f ≅ g : tProd F G | VΓ | VΠFG]< wl >.
Proof.
  constructor; intros ??? Vσ; instValid Vσ; now eapply ηeqEqTerm.
Qed.

End LambdaValid.
