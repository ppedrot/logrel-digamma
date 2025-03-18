From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations LContexts Context NormalForms Weakening
  GenericTyping Monad LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Escape Reflexivity Neutral Split Weakening Monotonicity Irrelevance Application Reduction Transitivity NormalRed.
From LogRel.Substitution Require Import Irrelevance Monotonicity Properties SingleSubst.
From LogRel.Substitution.Introductions Require Import Pi.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.


Section LambdaValid.
Context `{GenericTypingProperties}.

Lemma ηeqEqTermConvNf_strong {Γ wl F G l σ Δ h wl' f} (ρ := @wk1 Γ F)
  (VΓ : [||-v Γ ]< wl >)
  (VF : [Γ ||-v< l > F | VΓ ]< wl >)
  (VΓF : [||-v Γ,, F ]< wl >)
  (VG : [Γ,, F ||-v< l > G | VΓF ]< wl >)
  (VΠFG : [Γ ||-v< l > tProd F G | VΓ ]< wl >)
  (wfΔ : [|- Δ]< wl' >) (Vσ : [Δ ||-v σ : Γ | VΓ| wfΔ | f]< wl >)
  (HFG : [ Δ ||-< l > tProd F[σ] G[up_term_term σ] ]< wl' >)
  (RΠFG := normRedΠ HFG) 
  (Rh : [ Δ ||-< l > h[σ] : (tProd F G)[σ] | RΠFG ]< wl' >)
  (VσUp : [validSnoc' VΓ VF | Δ,, F[σ] ||-v up_term_term σ : Γ,, F
         | wfc_cons wfΔ (Wescape (validTy VF f wfΔ Vσ)) | f ]< wl >)
  (RVF : [ Δ ||-< l > F[σ] ]< wl' >)
  (RVG : [ Δ,, F[σ] ||-< l > G[up_term_term σ] ]< wl' >) :
  [Δ ,, F[σ] |- tApp h⟨ρ⟩[up_term_term σ] (tRel 0) ≅ tApp (PiRedTm.nf Rh)⟨↑⟩ (tRel 0) : G[up_term_term σ]]< wl' >.
Proof.
  refold.
  escape ;  Wescape.
  destruct (PiRedTm.red Rh); cbn in *.
  assert (wfΔF : [|- Δ,, F[σ]]< wl' >) by gen_typing.
  unshelve epose (rTree := PiRedTm.appTree Rh (@wk1 Δ F[σ]) (wfLCon_le_id wl') wfΔF (var0 _ _ _)).
  1: now rewrite wk1_ren_on.
  assumption.
  unshelve eapply convtm_over_tree ; [ eapply DTree_fusion ; shelve | intros wl'' Homax].
  pose (Ho := over_tree_fusion_l Homax).
  pose (Ho' := over_tree_fusion_r Homax).  
  unshelve epose proof (r := PiRedTm.app Rh (@wk1 Δ F[σ]) (wfLCon_le_id wl') wfΔF (var0 _ _ _) Ho Ho').
  1: now rewrite wk1_ren_on.
  assumption.
  assert (eqσ : forall σ Z, Z[up_term_term σ] = Z[up_term_term σ][(tRel 0) .: @wk1 Δ F[σ] >> tRel])
  by (intros; bsimpl; cbn; now rewrite rinstInst'_term_pointwise).
  eapply convtm_exp. 
  7: rewrite eqσ; eapply escapeEqTerm; eapply reflLRTmEq ; irrelevance.
  * eapply redtm_Ltrans ; [eapply over_tree_le ; eassumption | ].
    eapply redtm_meta_conv. 3: reflexivity.
    1: eapply redtm_app.
    2: eapply (ty_var wfΔF (in_here _ _)).
    1:{
      replace (h⟨_⟩[_]) with h[σ]⟨@wk1 Δ F[σ]⟩ by (unfold ρ; now bsimpl).
      eapply redtm_meta_conv. 3: reflexivity.
      1: eapply redtm_wk; tea.
      now rewrite wk1_ren_on.
    }
    fold ren_term. rewrite eqσ; now bsimpl. 
  * rewrite <- (wk1_ren_on Δ F[σ]); unshelve eapply redtmwf_refl.
    rewrite eqσ; eapply escapeTerm ; irrelevance.
    Unshelve.
    2,4: rewrite <- eqσ; tea.
    2,3: eapply Ltrans ; [ now eapply over_tree_le | eassumption ].
  * eapply wft_Ltrans ; [now eapply over_tree_le | tea].
  * rewrite eqσ; eapply escapeTerm ; irrelevance.
    Unshelve. 2: rewrite <- eqσ.
    2: eapply Ltrans ; [ now eapply over_tree_le | eassumption ].
  * rewrite eqσ; eapply escapeTerm ; irrelevance.
    Unshelve. 2: rewrite <- eqσ.
    2: eapply Ltrans ; [ now eapply over_tree_le | eassumption ].
  * unshelve eapply escapeEq, reflLRTyEq; [|tea].
    2: eapply Ltrans ; [ now eapply over_tree_le | eassumption ].
Qed.


Section WithContext.
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
  - econstructor 1 ; cbn; intros.
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
  - set (Helper := PolyRed.posRed _ _ _ _).
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
  pose (WRΠ := WnormRedΠ RVΠFG); refold.
  enough W[Δ ||-< l > (tLambda F t)[σ] ≅ (tLambda F t)[σ'] : (tProd F G)[σ] | WRΠ]< wl' >
    by Wirrelevance.
  unshelve epose (Helper:= lamValid0 Vt wfΔ Vσ).
  escape ; Wescape.
  cbn.
  unfold WRΠ, WnormRedΠ.
  cbn.
  unshelve econstructor ; [do 2 (eapply DTree_fusion) | intros wl'' Ho Ho'].
  1,2: shelve.
  1: eapply DTree_fusion ; shelve.
  1: do 2 eapply DTree_fusion ; shelve.
  cbn in *.
  match goal with |- context[LRPi' ?P] => set (Q := P) in * end.
  clearbody Q.
  pose (RΠ:= normRedΠ (WRed (tProd F G)[σ] RVΠFG wl'' Ho)) ; refold.
  pose proof (f' := over_tree_le Ho).
  unshelve econstructor.
  - eapply normLambda ; refold.
    irrelevanceRefl ; eapply Helper.
    do 2 (eapply over_tree_fusion_l) ; exact Ho'.
  - eapply normLambda ; refold.
    eapply LRTmRedConv.
    2: irrelevanceRefl.
    2: eapply (lamValid0 Vt wfΔ Vσ'), over_tree_fusion_r, over_tree_fusion_l; exact Ho'.
    eapply LRTyEqSym.
    unshelve eapply (validTyExt VΠFG) ; cycle 2 ; tea.
    eapply over_tree_fusion_l, over_tree_fusion_l, over_tree_fusion_r ; exact Ho'.
    Unshelve. 1-5: shelve.
    do 2 (eapply over_tree_fusion_l) ; do 2 (eapply over_tree_fusion_r) ; exact Ho'.
    2: eapply (validTy VΠFG f wfΔ Vσ').
    1,2: eapply over_tree_fusion_r, over_tree_fusion_l, over_tree_fusion_r ; exact Ho'.
  - intros ; do 2 (eapply DTree_fusion) ; [ .. | eapply DTree_fusion | do 2 eapply DTree_fusion].
    all: shelve.
  - refold; cbn.
    eapply convtm_Ltrans ; [exact f' | ].
    eapply convtm_eta; refold; tea.
    1,3: constructor; first [assumption|now eapply lrefl|idtac].
    + eapply ty_conv; [tea| now symmetry].
    + eapply ty_conv; [tea|].
      assert (Vσ'σ := symmetrySubstEq _ _ _ _ _ _ Vσ' Vσσ').
      assert (Vupσ'σ := liftSubstSEq' VF Vσ'σ).
      unshelve eassert (VG' := validTyExt VG _ _ _ _ Vupσ'σ).
      { eapply liftSubstSrealign'; tea. }
      eapply WescapeEq, VG'.
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
        do 2 rewrite <- eqσ ; eapply WescapeEqTerm; now eapply validTmExt.
  - refold; cbn; intros.
    pose (wfd' := wfc_Ltrans (f0 •ε f') wfΔ).
    epose (Vσa := consWkSubstS VF ρ Hd (subst_Ltrans (f0 •ε f') _ Vσ) (TmLogtoW _ ha)).
    unshelve refine (let ha' : [ _||-<l> a : _| wk_Ltrans ρ _ Hd (WRed F[σ'] RVF0 _ _ )]< _ > :=
                       _ in _). 
    3: eapply over_tree_fusion_l ; do 3 (eapply over_tree_fusion_r) ; exact Ho'.
    1: eauto.
    1: {
      eapply LRTmRedConv; tea.
      irrelevance0; [reflexivity|].
      eapply wkEq_Ltrans ; unshelve eapply (validTyExt VF).
      Unshelve.
      4,6,7,19: eassumption.
      1: eapply over_tree_fusion_r, over_tree_fusion_l ; do 2 (eapply over_tree_fusion_r).
      1: exact Ho'.
      1: do 4 (eapply over_tree_fusion_r) ; exact Ho'.
      1-8: shelve.
      all: eassumption.
    }
    epose (Vσa' := consWkSubstS VF ρ Hd (subst_Ltrans (f0 •ε f') _ Vσ')
                           (TmLogtoW _ ha')).
    unshelve refine (let Vσσa : [_ ||-v _ ≅ (a .: σ'⟨ρ⟩) : _ | _ | _ | Vσa | _]< _ > :=
      _ in _).
    {
      unshelve eapply consSubstSEq'.
      3: eapply WreflLRTmEq.
      1,3: Wirrelevance0; [|exact (TmLogtoW _ ha)]; now bsimpl.
      eapply irrelevanceSubstEq.
      unshelve eapply wkSubstSEq ; eauto.
      2: now eapply (eqsubst_Ltrans). 
      Unshelve.
      1-8: shelve.
      all: tea.
    }
    eapply LREqTermHelper ; [ irrelevanceRefl | ..].
    1,2: unshelve eapply (WRedTmEq _ (snd (lamBetaRed Vt _ _ _ _ _ _ _))).
    6,15: eassumption.
    4,11: eapply (subst_Ltrans (f0 •ε f')) ; eassumption.
    all: try eassumption.
    2: do 2 (eapply over_tree_fusion_l) ; exact Ho'0.
    3: eapply over_tree_fusion_l, over_tree_fusion_l, over_tree_fusion_r ; exact Ho'0.
    1,2: shelve.
    1: eapply over_tree_fusion_r, over_tree_fusion_l, over_tree_fusion_r ; exact Ho'0.
    1: eapply over_tree_fusion_r, over_tree_fusion_l ; exact Ho'0.
    + irrelevance0; rewrite consWkEq';[reflexivity|].
      unshelve eapply validTyExt; cycle 6; tea.
      eapply over_tree_fusion_l, over_tree_fusion_r, over_tree_fusion_r, over_tree_fusion_r ; exact Ho'0.
      exact (over_tree_fusion_r (over_tree_fusion_l (over_tree_fusion_r (over_tree_fusion_r Ho'0)))).
      Unshelve.
      3,4: shelve.
      all: now rewrite consWkEq'; eapply validTy; tea.
    + epose (X := validTmExt Vt _ _ _ Vσa' Vσσa).
      irrelevance0 ; [ | eapply (WRedTmEq _ X)].
      1: now rewrite consWkEq'.      
      1: do 2 (eapply over_tree_fusion_l) ; do 2 (eapply over_tree_fusion_r) ; exact Ho'0.
      Unshelve.
      2: do 4 (eapply over_tree_fusion_r) ; exact Ho'0.
Qed.


Lemma ηeqEqTermConvNf {σ Δ h wl' f} (ρ := @wk1 Γ F)
  (wfΔ : [|- Δ]< wl' >) (Vσ : [Δ ||-v σ : Γ | VΓ| wfΔ | f]< wl >)
  (RΠFG := WnormRedΠ (validTy VΠFG f wfΔ Vσ))
  (RVG := (validTy VG f (wfc_cons wfΔ (Wescape (validTy VF f wfΔ Vσ))) (liftSubstS' VF Vσ)))
  (Rh : W[Δ ||-<l> h[σ] : (tProd F G)[σ] | RΠFG ]< wl' >) :
  forall wl'' (Ho : over_tree wl' wl'' (WT _ RΠFG))
         (Ho' : over_tree wl' wl'' (WTTm _ Rh))
         (Ho'' : over_tree wl' wl'' (WT F[σ] (validTy VF f wfΔ Vσ)))
         (Ho''' : over_tree wl' wl'' (WT G[up_term_term σ] RVG)),
    [Δ ,, F[σ] |- tApp h⟨ρ⟩[up_term_term σ] (tRel 0) ≅
                    tApp (PiRedTm.nf (WRedTm _ Rh _ Ho Ho'))⟨↑⟩ (tRel 0) : G[up_term_term σ]]< wl'' >.
Proof.
  refold.
  pose (VσUp :=  liftSubstS' VF Vσ).
  instValid Vσ; instValid VσUp; escape ; Wescape.
  intros wl'' Ho Ho' Ho'' Ho'''.
  pose (f':= over_tree_le Ho).
  unshelve eapply ηeqEqTermConvNf_strong.
  3-5,8,9: eassumption.
  1: now eapply wfLCon_le_trans.
  1: now eapply wfc_Ltrans.
  1: eapply subst_Ltrans ; eassumption.
  1: now eapply subst_Ltrans.
  1: now eapply RVF.
  1: now eapply RVG.
Qed.

Lemma isLRFun_isWfFun :
  forall {σ Δ h wl' f} (wfΔ : [|- Δ]< wl' >)
         (vσ : [Δ ||-v σ : Γ | VΓ | wfΔ | f]< wl >)
         (RΠFG : [Δ ||-< l > (tProd F G)[σ]]< wl >)
         (p : [Δ ||-Π h[σ] : tProd F[σ] G[up_term_term σ] | normRedΠ0 (Induction.invLRΠ RΠFG)]< wl >),
    isWfFun wl' Δ F[σ] G[up_term_term σ] (PiRedTm.nf p).
Proof.
intros.
instValid vσ.
destruct RΠFG; simpl in *.
destruct p as [nf ? ? ? isfun]; simpl in *.
destruct isfun as [A t vtree vA vt|]; simpl in *; constructor; tea.
+ rewrite <- (@wk_id_ren_on Δ).
  unshelve eapply escapeConv, vA; tea.
+ rewrite <- (wk_id_ren_on Δ F[σ]), <- (wk_id_ren_on Δ A).
  now unshelve eapply escapeEq, vA.
+ assert (Hrw : forall t, t[tRel 0 .: @wk1 Δ A >> tRel] = t).
  { intros; bsimpl; apply idSubst_term; intros []; reflexivity. }
  assert [Δ |- F[σ]]< wl' > by now eapply Wescape.
  assert (wfΔF : [|- Δ,, F[σ]]< wl' >) by now apply wfc_cons.
  unshelve eassert (vt0 := vt _ _ (tRel 0) (@wk1 Δ F[σ]) _ _ _).
  4:{ eapply var0; [now bsimpl|tea]. }
  1,2: eassumption.
  eapply ty_over_tree.
  intros wl''' Homax.
  epose (Ho := over_tree_fusion_l Homax).
  epose (Ho' := over_tree_fusion_r Homax).
  specialize (vt0 _ Ho Ho').
  eapply escapeTerm in vt0.
  now rewrite !Hrw in vt0.
+ assert (Hrw : forall t, t[tRel 0 .: @wk1 Δ A >> tRel] = t).
  { intros; bsimpl; apply idSubst_term; intros []; reflexivity. }
  assert [Δ |- A]< wl' >.
  { rewrite <- (@wk_id_ren_on Δ).
    unshelve eapply escapeConv, vA; tea. }
  assert (wfΔA : [|- Δ,, A]< wl' >) by now apply wfc_cons.
  assert [Δ |-[ ta ] A ≅ F[σ]]< wl' >.
  { rewrite <- (wk_id_ren_on Δ F[σ]), <- (wk_id_ren_on Δ A).
    symmetry; now unshelve eapply escapeEq, vA. }
  assert W[Δ,, A ||-< l > G[up_term_term σ]]< wl' >.
  { eapply validTy with (wfΔ := wfΔA); tea.
    unshelve econstructor; [shelve|]; cbn.
    exists (leaf _) ; intros wl'' Ho Ho'.
    apply var0conv; [|tea].
    replace F[↑ >> up_term_term σ] with F[σ]⟨@wk1 Δ A⟩ by now bsimpl.
    rewrite <- (wk1_ren_on Δ A); eapply convty_wk; tea.
    1: eapply wfc_Ltrans; [now eapply over_tree_le | eassumption].
    1: eapply convty_Ltrans; [now eapply over_tree_le | eassumption].
    1: eapply wft_Ltrans; [now eapply over_tree_le | eassumption].
    Unshelve.
    1: eassumption.
    eapply irrelevanceSubstExt with (σ := σ⟨@wk1 Δ A⟩).
    { now bsimpl. }
    now eapply wkSubstS.
  }
  rewrite <- (Hrw t); unshelve eapply WescapeTerm ; [ | eassumption | ].
  econstructor ; intros wl'' Ho Ho'.
  irrelevance0; [apply Hrw| unshelve apply vt].
  3: apply wfc_cons; tea.
  1: assumption.
  - apply var0conv; tea.
    rewrite <- (wk1_ren_on Δ A A).
    apply convty_wk; [now apply wfc_cons|].
    rewrite <- (wk_id_ren_on Δ F[σ]), <- (wk_id_ren_on Δ A).
    symmetry; now unshelve eapply escapeEq, vA.
  - eapply over_tree_fusion_l ; exact Ho'.
  - eapply over_tree_fusion_r ; exact Ho'.
+ now eapply convneu_Ltrans. 
Qed.

End WithContext.

Lemma ηeqEqTerm_strong {Γ wl F G l σ Δ h g wl' f} (ρ := @wk1 Γ F)
  (VΓ : [||-v Γ ]< wl >)
  (VF : [Γ ||-v< l > F | VΓ ]< wl >)
  (VΓF := validSnoc' VΓ VF)
  (VG : [Γ,, F ||-v< l > G | VΓF ]< wl >)
  (VΠFG : [Γ ||-v< l > tProd F G | VΓ ]< wl >)
  (Vfg : [Γ,, F ||-v< l > tApp h⟨ρ⟩ (tRel 0) ≅ tApp g⟨ρ⟩ (tRel 0) : G | VΓF | VG ]< wl >)
  (wfΔ : [|- Δ]< wl' >) (Vσ : [Δ ||-v σ : Γ | VΓ| wfΔ | f]< wl >)
  (HFG : [ Δ ||-< l > tProd F[σ] G[up_term_term σ] ]< wl' >)
  (RΠFG := normRedΠ HFG : [Δ ||-< l > tProd F[σ] G[up_term_term σ] ]< wl'>) 
  (Rh : [ Δ ||-< l > h[σ] : (tProd F G)[σ] | RΠFG ]< wl' >)
  (Rg : [ Δ ||-< l > g[σ] : (tProd F G)[σ] | RΠFG ]< wl' >)
  (RVF : [ Δ ||-< l > F[σ] ]< wl' >)
  (RVG : [ Δ,, F[σ] ||-< l > G[up_term_term σ] ]< wl' >) :
  [Δ ||-<l> h[σ] ≅ g[σ] : (tProd F G)[σ] | RΠFG ]< wl' >.
Proof.
  set (RΠ := normRedΠ (RΠFG)); refold.
  unshelve econstructor.
  1,2: assumption.
  - intros ; do 2 eapply DTree_fusion ; [ .. | eapply DTree_fusion ] ; shelve.
  - cbn; pose (VσUp :=  liftSubstS' VF Vσ).
    instValid Vσ; instValid VσUp; escape ; Wescape.
    eapply convtm_eta; tea.
    + destruct (PiRedTm.red Rh); cbn in *; tea.
    + unshelve eapply isLRFun_isWfFun.
      5: eassumption.
      5: eapply irrelevanceTy, Validity_Ltrans' ; exact VG.
      2: eapply irrelevanceTy, Validity_Ltrans' ; exact VF.
      1: now eapply WfC_Ltrans. 
      1: now eapply wfLCon_le_id.
      now eapply subst_Ltrans'.
    + destruct (PiRedTm.red Rg); cbn in *; tea.
    + unshelve eapply isLRFun_isWfFun.
      5: eassumption.
      5: eapply irrelevanceTy, Validity_Ltrans' ; exact VG.
      2: eapply irrelevanceTy, Validity_Ltrans' ; exact VF.
      1: now eapply WfC_Ltrans. 
      1: now eapply wfLCon_le_id.
      now eapply subst_Ltrans'.
    + etransitivity ; [symmetry| etransitivity]; tea.
      1,2: now eapply ηeqEqTermConvNf_strong.
  - cbn; intros ?? wl'' ρ' f' Hd ha wl''' Ho Ho'.
    set (ν := (a .: σ⟨ρ'⟩)).
    unshelve epose (Vν := consWkSubstS VF ρ' Hd (subst_Ltrans f' _ Vσ) (TmLogtoW _ ha)).
    { now eapply wfc_Ltrans. }
    instValid Vσ; instValid Vν; escape ; Wescape.
    assert (wfΔF : [|- Δ,, F[σ]]< wl' >) by gen_typing.
    assert (eq : forall t, t⟨ρ⟩[a .: σ⟨ρ'⟩] = t[σ]⟨ρ'⟩) by (intros; unfold ρ; now bsimpl).
    cbn in *.
    eapply transEqTerm; [|eapply transEqTerm].
    2:{ irrelevance0 ; [ | eapply RVfg].
        symmetry ; apply consWkEq'.
        do 2 (eapply over_tree_fusion_l) ; exact Ho'.
    }
    + eapply LRTmEqSym; eapply redwfSubstTerm.
      1: unshelve epose proof (r := PiRedTm.app Rh ρ' f' Hd ha _).
      2: eapply over_tree_fusion_l, over_tree_fusion_r ; exact Ho'.
      irrelevance0 ; [ | eapply r] ; [now bsimpl | ..].
      eapply over_tree_fusion_l ; do 2 (eapply over_tree_fusion_r) ; exact Ho'.
      rewrite eq.
      eapply redtmwf_Ltrans ; [now eapply over_tree_le | ].
      eapply redtmwf_appwk; tea.
      1: eapply redtmwf_Ltrans ; [ eassumption | exact (PiRedTm.red Rh) ].
      now bsimpl.
    + eapply redwfSubstTerm.
      1: unshelve epose proof (r := PiRedTm.app Rg ρ' f' Hd ha _).
      2: eapply over_tree_fusion_l, over_tree_fusion_r ; exact Ho'.
      irrelevance0 ; [ | eapply r] ; [now bsimpl | ..].
      eapply over_tree_fusion_r, over_tree_fusion_l ; exact Ho'.
      rewrite eq.
      eapply redtmwf_Ltrans ; [now eapply over_tree_le | ].
      eapply redtmwf_appwk; tea.
      1: eapply redtmwf_Ltrans ; [ eassumption | exact (PiRedTm.red Rg) ].
      now bsimpl.
      Unshelve.
      1-4: eassumption.
      do 3 eapply over_tree_fusion_r ; exact Ho'.
Qed.



Lemma ηeqEqTerm {Γ wl F G l} {VΓ : [||-v Γ]< wl >} (VF : [Γ ||-v<l> F | VΓ]< wl >) 
  (VΓF := validSnoc' VΓ VF)
  (VG : [Γ ,, F ||-v<l> G | VΓF]< wl >)
  (VΠFG := PiValid VΓ VF VG)
  {σ Δ g h wl' f} (ρ := @wk1 Γ F)
  (Vfg : [Γ ,, F ||-v<l> tApp h⟨ρ⟩ (tRel 0) ≅ tApp g⟨ρ⟩ (tRel 0) : G | VΓF | VG ]< wl >)
  (wfΔ : [|- Δ]< wl' >) (Vσ : [Δ ||-v σ : Γ | VΓ| wfΔ | f]< wl >)
  (RΠFG := validTy VΠFG f wfΔ Vσ)
  (Rh : W[Δ ||-<l> h[σ] : (tProd F G)[σ] | RΠFG ]< wl' >)
  (Rg : W[Δ ||-<l> g[σ] : (tProd F G)[σ] | RΠFG ]< wl' >) :
  W[Δ ||-<l> h[σ] ≅ g[σ] : (tProd F G)[σ] | RΠFG ]< wl' >.
Proof.
  pose (VσUp :=  liftSubstS' VF Vσ).
  instValid Vσ; instValid VσUp; escape ; Wescape.
  unshelve econstructor ; [ | intros wl'' Ho Ho'].
  1: do 2 (eapply DTree_fusion) ; shelve.
  pose (f' := over_tree_le Ho).
  irrelevanceRefl ; eapply ηeqEqTerm_strong.
  4: irrelevanceRefl ; eapply Rh.
  5: irrelevanceRefl ; eapply Rg.
  6: eapply RVF.
  7: eapply RVG.
  2: eapply Vfg.
  1: eassumption.
  1: now eapply subst_Ltrans.
  1: now do 2 (eapply over_tree_fusion_l) ; exact Ho'.
  1: now eapply over_tree_fusion_r, over_tree_fusion_l ; exact Ho'.
  1: now eapply over_tree_fusion_l, over_tree_fusion_r ; exact Ho'.
  1: now do 2 (eapply over_tree_fusion_r) ; exact Ho'.
  Unshelve.
  2: now eapply wfc_Ltrans.
  1: eapply RΠFG.
  all: eassumption.
Qed.

Lemma etaeqValid {Γ wl F G l} {VΓ : [||-v Γ]< wl >} (VF : [Γ ||-v<l> F | VΓ]< wl >) 
  (VΓF := validSnoc' VΓ VF)
  (VG : [Γ ,, F ||-v<l> G | VΓF]< wl >)
  (VΠFG := PiValid VΓ VF VG)
  {f g} (ρ := @wk1 Γ F)
  (Vf : [Γ ||-v<l> f : tProd F G | VΓ | VΠFG ]< wl >)
  (Vg : [Γ ||-v<l> g : tProd F G | VΓ | VΠFG ]< wl >) 
  (Vfg : [Γ ,, F ||-v<l> tApp f⟨ρ⟩ (tRel 0) ≅ tApp g⟨ρ⟩ (tRel 0) : G | VΓF | VG ]< wl >) :
  [Γ ||-v<l> f ≅ g : tProd F G | VΓ | VΠFG]< wl >.
Proof.
  constructor; intros ????? Vσ; instValid Vσ; now eapply ηeqEqTerm.
Qed.

End LambdaValid.
