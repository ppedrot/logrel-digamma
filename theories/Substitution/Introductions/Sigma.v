From Coq Require Import ssrbool.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations LContexts Context NormalForms Weakening
  GenericTyping LogicalRelation Monad Validity.
From LogRel.LogicalRelation Require Import Escape Reflexivity Neutral Weakening Monotonicity Split Irrelevance Reduction NormalRed Induction Transitivity.
From LogRel.Substitution Require Import Irrelevance Properties SingleSubst Reflexivity Monotonicity.
From LogRel.Substitution.Introductions Require Import Universe Poly.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Section SigmaValidity.
  Context `{GenericTypingProperties}.
  Context {l wl Γ F G} (VΓ : [||-v Γ]< wl >)
    (VF : [Γ ||-v< l > F | VΓ ]< wl >)
    (VG : [Γ ,, F ||-v< l > G | validSnoc' VΓ VF]< wl >).

  Lemma SigRed {Δ σ wl' f} (wfΔ : [ |-[ ta ] Δ]< wl' >) (Vσ : [VΓ | Δ ||-v σ : _ | wfΔ | f]< wl >)
    : W[ Δ ||-< l > (tSig F G)[σ] ]< wl' >.
  Proof.
    econstructor ; intros wl'' Ho.
    pose proof (f' := over_tree_le Ho).
    eapply LRSig'.
    pose (p := substPolyRed VΓ VF VG _ Vσ).
    escape ; Wescape; cbn; econstructor; tea;
    destruct (WpolyRedId p);
    destruct (WpolyRedEqId p (substPolyRedEq VΓ VF VG _ Vσ Vσ (reflSubst _ _ _ Vσ))); escape ; Wescape.
    - eapply redtywf_refl, wft_Ltrans ; [eassumption | ]. gen_typing.
    - eapply convty_Ltrans ; [eassumption | ] ; gen_typing.
    - eapply convty_Ltrans ; [eassumption | ] ; gen_typing.
    - eapply p.
      eassumption.
  Defined.

  Lemma SigEqRed {Δ σ σ' wl' f} (tΔ : [ |-[ ta ] Δ]< wl' >)
    (Vσ : [VΓ | Δ ||-v σ : _ | tΔ | f]< wl >)
    (Vσ' : [VΓ | Δ ||-v σ' : _ | tΔ | f]< wl >)
    (Vσσ' : [VΓ | Δ ||-v σ ≅ σ' : _ | tΔ | Vσ | f]< wl >)
    : W[ Δ ||-< l > (tSig F G)[σ] ≅ (tSig F G)[σ'] | SigRed tΔ Vσ ]< wl' >.
  Proof.
    pose (p := substPolyRed VΓ VF VG _ Vσ).
    pose (p' := substPolyRed VΓ VF VG _ Vσ').
    pose (peq := substPolyRedEq VΓ VF VG _ Vσ Vσ' Vσσ').
    econstructor; intros wl'' Ho Ho' ; cbn.
    pose (peq' := substPolyRedEq VΓ VF VG _ Vσ Vσ (reflSubst VΓ f tΔ Vσ)).
    pose proof (f' := over_tree_le Ho).
    fold p ; fold p' ; fold peq ; fold peq'.
    destruct (WpolyRedEqId p peq'), (WpolyRedId p), (WpolyRedId p'), (WpolyRedEqId p peq).
    escape ; Wescape.
    econstructor ; cbn.
    - eapply redtywf_refl, wft_Ltrans ; [eassumption | ] ; gen_typing.
    - eapply convty_Ltrans ; [eassumption | ] ; gen_typing.
    - eapply convty_Ltrans ; [eassumption | ] ; gen_typing.
    - eapply peq ; eassumption.
  Defined.

  Lemma SigValid : [Γ ||-v< l > tSig F G | VΓ]< wl >.
  Proof. unshelve econstructor; intros; [now eapply SigRed| now eapply SigEqRed].  Defined.
  
End SigmaValidity.

Section SigmaCongValidity.

  Context `{GenericTypingProperties}.
  Context {wl Γ F G F' G' l}
    (VΓ : [||-v Γ]< wl >)
    (VF : [ Γ ||-v< l > F | VΓ ]< wl >)
    (VG : [ Γ ,, F ||-v< l > G | validSnoc' VΓ VF ]< wl >)
    (VF' : [ Γ ||-v< l > F' | VΓ ]< wl >)
    (VG' : [ Γ ,, F' ||-v< l > G' | validSnoc' VΓ VF' ]< wl >)
    (VFF' : [ Γ ||-v< l > F ≅ F' | VΓ | VF ]< wl >)
    (VGG' : [ Γ ,, F ||-v< l > G ≅ G' | validSnoc' VΓ VF | VG ]< wl >).

  Lemma SigCongRed {Δ σ wl' f} (wfΔ : [|- Δ]< wl' >) (Vσ : [VΓ | Δ ||-v σ : _ | wfΔ | f]< wl >)
    : W[ Δ ||-< l > (tSig F G)[σ] ≅ (tSig F' G')[σ] | validTy (SigValid VΓ VF VG) f wfΔ Vσ ]< wl' >.
  Proof.
    econstructor ; intros wl'' Ho Ho' ; cbn.
    pose proof (f' := over_tree_le Ho).
    set (p := substPolyRed VΓ VF VG _ Vσ).
    set (p' := substPolyRed VΓ VF' VG' _ Vσ).
    pose (peq := substEqPolyRedEq VΓ VF VG _ Vσ VF' VG' VFF' VGG').
    set (peq' := (substPolyRedEq _ _ _ _ _ _ _)).
    destruct (WpolyRedEqId p peq'), (WpolyRedId p), (WpolyRedId p'), (WpolyRedEqId p peq).
    escape; Wescape ; econstructor; cbn; tea.
    - eapply redtywf_refl, wft_Ltrans ; [eassumption | ] ; gen_typing.
    - eapply convty_Ltrans ; [eassumption | ] ; gen_typing.
    - eapply convty_Ltrans ; [eassumption | ] ; gen_typing.
    - eapply peq ; eassumption.
  Qed.

  Lemma SigCong : [ Γ ||-v< l > tSig F G ≅ tSig F' G' | VΓ | SigValid VΓ VF VG ]< wl >.
  Proof.  econstructor; intros; eapply SigCongRed.  Qed.

End SigmaCongValidity.


Lemma up_subst_single {t σ a} : t[up_term_term σ][a..] = t[a .: σ].
Proof. now asimpl. Qed.

Lemma wk_id_shift {t a Γ} : t[a .: @wk_id Γ >> tRel] = t[a..].
Proof. now bsimpl. Qed.

Lemma split_valid_subst_wk_id {Γ G σ} :
 G[σ] = G[up_term_term (↑ >> σ)][σ var_zero .: (@wk_id Γ) >> tRel].
Proof.  now rewrite wk_id_shift, up_subst_single, scons_eta'. Qed.

Section SigInjValid.
  Context `{GenericTypingProperties}.
  Context {l wl Γ F G} (VΓ : [||-v Γ]< wl >) (VΣ : [Γ ||-v<l> tSig F G | VΓ]< wl >).
  
  Lemma domSigValid : [Γ ||-v<l> F | VΓ]< wl >.
  Proof.
    unshelve econstructor.
    - intros ????? Vσ; instValid Vσ.
      exists (WT _ RVΣ) ; intros wl'' Ho.
      unshelve eapply (polyRedId (normRedΣ0 (invLRΣ _))) ; refold.
      2: now eapply RVΣ.
    - refold.
      intros ?????? Vσ Vσ' Vσσ' ; instAllValid Vσ Vσ' Vσσ'.
      econstructor ; intros wl'' Ho Ho' ; cbn.
      set (P := (polyRedId _)); destruct P.
      irrelevanceRefl; unshelve eapply (polyRedEqId _ (normEqRedΣ _ _)) ; refold.
      4: now unshelve eapply REVΣ.
  Qed.

  Lemma codSigValid : [Γ,, F ||-v<l> G | validSnoc' VΓ domSigValid ]< wl >.
  Proof.
    pose (domSigValid).
    assert (h : forall (Δ : context) (wl' : wfLCon) (σ : nat -> term) (f : wl' ≤ε wl) (wfΔ : [ |-[ ta ] Δ]< wl' >),
      [validSnoc' VΓ domSigValid | Δ ||-v σ : Γ,, F | wfΔ | f]< wl > -> W[Δ ||-< l > G[σ]]< wl' >).
    1:{
      intros ???? wfΔ Vσ ; instValid (projT1 Vσ).
      erewrite split_valid_subst_wk_id.
      eapply (TreeSplit (DTree_fusion _ _ (DTree_fusion _ _ _))) ; intros wl'' Ho.
      pose proof (f':= over_tree_le Ho).
      econstructor.
      intros wl''' Ho'.
      pose proof (f'':= over_tree_le Ho').
      unshelve eapply (PolyRed.posRed (normRedΣ0 (invLRΣ _)) (wk_id) (wfLCon_le_id _)).
      3: eapply RVΣ, over_tree_fusion_l ; exact Ho.
      1: now eapply wfc_Ltrans. 
      1: irrelevance0 ; [ | unshelve eapply (projT2 Vσ)].
      1: now rewrite wk_id_ren_on.
      3: eassumption.
      1: eapply over_tree_fusion_l, over_tree_fusion_r ; exact Ho.
      1: eapply over_tree_fusion_r, over_tree_fusion_r ; exact Ho.
    }
    unshelve econstructor; tea.
    intros ????? wfΔ Vσ Vσ' Vσσ' ; instAllValid (projT1 Vσ) (projT1 Vσ') (fst Vσσ').
    unshelve eapply (TreeEqSplit _).
    1: do 3 eapply DTree_fusion ; [.. | eapply DTree_fusion | eapply DTree_fusion] ; shelve.
    intros wl'' Ho.
    epose (p := normRedΣ0 (invLRΣ (WRed _ RVΣ _ _))) ;
      epose (q := normEqRedΣ _ (WRedEq _ REVΣ _ _ _) ); fold subst_term in *.
    pose proof (f':= over_tree_le Ho).
    assert [PolyRed.shpRed p wk_id (wfLCon_le_id _) (wfc_Ltrans f' wfΔ) | Δ ||- σ' var_zero : (ParamRedTy.dom p)⟨wk_id⟩]< wl'' >.
    1:{
      eapply LRTmRedConv.
      2: eapply (projT2 Vσ').
      rewrite wk_id_ren_on; cbn.
      eapply LRTyEqSym, REt.
      1: do 3 (eapply over_tree_fusion_l) ; exact Ho.
      1: eapply over_tree_fusion_r ; do 2 (eapply over_tree_fusion_l) ; exact Ho.
      Unshelve.
      9: eapply over_tree_fusion_l, over_tree_fusion_r, over_tree_fusion_l ; exact Ho.
      9: eapply over_tree_fusion_r, over_tree_fusion_r, over_tree_fusion_l ; exact Ho.
      7: eapply over_tree_fusion_l, over_tree_fusion_l, over_tree_fusion_r ; exact Ho.
      6: eapply over_tree_fusion_r, over_tree_fusion_l, over_tree_fusion_r ; exact Ho.
      5: do 2 (eapply over_tree_fusion_l) ; do 2 (eapply over_tree_fusion_r) ; exact Ho.
      all: shelve. }
    econstructor.
    intros wl''' Ho1 Ho2.
    pose proof (f'':= over_tree_le Ho1).
    irrelevance0.
    1: erewrite split_valid_subst_wk_id ; reflexivity.
    eapply transEq; cycle 1.
    - erewrite split_valid_subst_wk_id.
      unshelve eapply (PolyRedEq.posRed q wk_id (wfLCon_le_id _) (wfc_Ltrans f' wfΔ)).
      1: now irrelevance.
      1: do 2 (eapply over_tree_fusion_l) ; exact Ho2.
      1: eapply over_tree_fusion_r, over_tree_fusion_l ; exact Ho2.
    - unshelve eapply (PolyRed.posExt p wk_id (wfLCon_le_id _) (wfc_Ltrans f' wfΔ)); tea.
      1: irrelevance0; [|eapply (projT2 Vσ)] ; [now rewrite wk_id_ren_on | ].
      3: irrelevance0; [|eapply (snd Vσσ')]; [ now rewrite wk_id_ren_on | ].
      Unshelve.
      2: eapply over_tree_fusion_l, over_tree_fusion_r ; exact Ho2.
      3: eapply over_tree_fusion_l, over_tree_fusion_r, over_tree_fusion_r ; exact Ho2.
      3: eapply over_tree_fusion_r, over_tree_fusion_r, over_tree_fusion_r ; exact Ho2.
      1: eapply over_tree_fusion_l ; do 3 (eapply over_tree_fusion_r) ; exact Ho.
      1: eapply over_tree_fusion_r, over_tree_fusion_l ; do 2 (eapply over_tree_fusion_r) ; exact Ho.
      2,3: do 4 (eapply over_tree_fusion_r) ; exact Ho.
  Qed.
  
End SigInjValid.



Section SigTmValidity.

  Context `{GenericTypingProperties}.
  Context {wl Γ F G} (VΓ : [||-v Γ]< wl >)
    (VF : [ Γ ||-v< one > F | VΓ ]< wl >)
    (VU : [ Γ ,, F ||-v< one > U | validSnoc' VΓ VF ]< wl >)
    (VFU : [ Γ ||-v< one > F : U | VΓ | UValid VΓ ]< wl >)
    (VGU : [ Γ ,, F ||-v< one > G : U | validSnoc' VΓ VF | VU ]< wl >) .

  Lemma sigTmEq {Δ σ σ' wl' f} (tΔ : [ |-[ ta ] Δ]< wl' >)
    (Vσ : [VΓ | Δ ||-v σ : _ | tΔ | f]< wl >)
    (Vσ' : [VΓ | Δ ||-v σ' : _ | tΔ | f]< wl >)
    (Vσσ' : [VΓ | Δ ||-v σ ≅ σ' : _ | tΔ | Vσ | f ]< wl >)
    : [Δ |-[ ta ] tSig F[σ] G[up_term_term σ] ≅ tSig F[σ'] G[up_term_term σ'] : U]< wl' >.
  Proof.
    pose proof (Vuσ := liftSubstS' VF Vσ).
    pose proof (Vureaσ' := liftSubstSrealign' VF Vσσ' Vσ').
    pose proof (Vuσσ' := liftSubstSEq' VF Vσσ').
    instAllValid Vσ Vσ' Vσσ'; instAllValid Vuσ Vureaσ' Vuσσ'; escape ; Wescape.
    eapply convtm_sig; tea.
  Qed.

  Lemma SigRedU {Δ σ wl' f} (tΔ : [ |-[ ta ] Δ]< wl' >) (Vσ : [VΓ | Δ ||-v σ : _ | tΔ | f]< wl >)
    : W[ Δ ||-< one > (tSig F G)[σ] : U | validTy (UValid VΓ) f tΔ Vσ ]< wl' >.
  Proof.
    pose proof (Vσσ := reflSubst _ _ _ Vσ).
    pose proof (Vuσ := liftSubstS' VF Vσ).
    pose proof (Vuσσ := liftSubstSEq' VF Vσσ).
    instAllValid Vσ Vσ Vσσ; instAllValid Vuσ Vuσ Vuσσ; escape ; Wescape.
    econstructor; cbn.
    intros wl'' Ho Ho' ; cbn.
    econstructor ; cbn.
    - eapply redtmwf_refl, ty_Ltrans ; [eassumption | ] ; cbn in *.
      now eapply ty_sig.
    - constructor.
    - eapply convtm_Ltrans ; [eassumption | now eapply convtm_sig].
    - cbn.
      unshelve refine (LRCumulative (WRed _ (SigRed _ _ _ tΔ Vσ) _ _)).
      1,2: unshelve eapply univValid ; tea; try irrValid.
      eassumption.
  Defined.

  Lemma SigValidU : [ Γ ||-v< one > tSig F G : U | VΓ | UValid VΓ ]< wl >.
  Proof.
    econstructor.
    - intros Δ ? σ ? tΔ Vσ.
      exact (SigRedU tΔ Vσ).
    - intros Δ ? σ σ' ? tΔ Vσ Vσ' Vσσ'.
      pose proof (univValid (l' := zero) _ _ VFU) as VF0.
      pose proof (irrelevanceTy (validSnoc' VΓ VF)
                    (validSnoc' (l := zero) VΓ VF0)
                    (univValid (l' := zero) _ _ VGU)) as VG0.
      unshelve econstructor.
      1: do 3 eapply DTree_fusion ; shelve.
      intros wl'' Ho Ho'.
      unshelve econstructor ; cbn.
      + eapply (SigRedU tΔ Vσ).
        do 3 (eapply over_tree_fusion_l) ; exact Ho'.
      + eapply (SigRedU tΔ Vσ').
        eapply over_tree_fusion_r ; do 2 (eapply over_tree_fusion_l) ; exact Ho'.
      + eapply (LRCumulative (WRed _ (SigRed VΓ VF0 VG0 tΔ Vσ) _ _)).
      + eapply convtm_Ltrans ; [ | exact (sigTmEq tΔ Vσ Vσ' Vσσ')].
        now eapply over_tree_le.
      + eapply (LRCumulative (WRed _ (SigRed VΓ VF0 VG0 tΔ Vσ') _ _)).
      + pose (X := SigEqRed VΓ VF0 VG0 tΔ Vσ Vσ' Vσσ').
        eapply LRTyEqIrrelevantCum, X.
        eapply over_tree_fusion_l, over_tree_fusion_l, over_tree_fusion_r ; exact Ho'.
        Unshelve.
        5: eapply over_tree_fusion_r, over_tree_fusion_l, over_tree_fusion_r ; exact Ho'.
        5: eapply over_tree_fusion_l, over_tree_fusion_r, over_tree_fusion_r ; exact Ho'.
        4: eapply over_tree_fusion_r, over_tree_fusion_r, over_tree_fusion_r ; exact Ho'.
        all: now constructor.
  Qed.

End SigTmValidity.


Section SigTmCongruence.

  Context `{GenericTypingProperties}.
  Context {wl Γ F G F' G'}
    (VΓ : [||-v Γ]< wl >)
    (VF : [ Γ ||-v< one > F | VΓ ]< wl >)
    (VU : [ Γ ,, F ||-v< one > U | validSnoc' VΓ VF ]< wl >)
    (VFU : [ Γ ||-v< one > F : U | VΓ | UValid VΓ ]< wl >)
    (VGU : [ Γ ,, F ||-v< one > G : U | validSnoc' VΓ VF | VU ]< wl >)
    (VF' : [ Γ ||-v< one > F' | VΓ ]< wl >)
    (VU' : [ Γ ,, F' ||-v< one > U | validSnoc' VΓ VF' ]< wl >)
    (VF'U : [ Γ ||-v< one > F' : U | VΓ | UValid VΓ ]< wl >)
    (VG'U : [ Γ ,, F' ||-v< one > G' : U | validSnoc' VΓ VF' | VU' ]< wl >)
    (VFF' : [ Γ ||-v< one > F ≅ F' : U | VΓ | UValid VΓ ]< wl >)
    (VGG' : [ Γ ,, F ||-v< one > G ≅ G' : U | validSnoc' VΓ VF | VU ]< wl >).

  Lemma SigCongTm : [ Γ ||-v< one > tSig F G ≅ tSig F' G' : U | VΓ | UValid VΓ ]< wl >.
  Proof.
    econstructor.
    intros Δ wl' σ f tΔ Vσ.
    pose proof (univValid (l' := zero) _ _ VFU) as VF0.
    pose proof (univValid (l' := zero) _ _ VF'U) as VF'0.
    pose proof (Vσσ := reflSubst _ _ _ Vσ).
    pose proof (Vuσ := liftSubstS' VF Vσ).
    pose proof (Vuσσ := liftSubstSEq' VF Vσσ).
    instAllValid Vσ Vσ Vσσ; instAllValid Vuσ Vuσ Vuσσ; escape ; Wescape.
    pose proof (irrelevanceTy (validSnoc' VΓ VF)
                  (validSnoc' (l := zero) VΓ VF0)
                  (univValid (l' := zero) _ _ VGU)) as VG0.
    pose proof (irrelevanceTy (validSnoc' VΓ VF')
                  (validSnoc' (l := zero) VΓ VF'0)
                  (univValid (l' := zero) _ _ VG'U)) as VG'0.
    econstructor ; intros wl'' Ho Ho' ; cbn in Ho.
    unshelve econstructor ; cbn.
    - eapply (SigRedU VΓ VF VU VFU VGU tΔ Vσ).
      eapply over_tree_fusion_l, over_tree_fusion_l ; exact Ho'.
    - eapply (SigRedU VΓ VF' VU' VF'U VG'U tΔ Vσ).
      eapply over_tree_fusion_r, over_tree_fusion_l ; exact Ho'.
    - unshelve eapply (LRCumulative (WRed _ (SigRed VΓ VF0 VG0 tΔ Vσ) _ _)).
      eapply over_tree_fusion_l, over_tree_fusion_l, over_tree_fusion_r ; exact Ho'.
    - eapply convtm_Ltrans ; [eassumption | ] ; now eapply convtm_sig.
    - unshelve eapply (LRCumulative (WRed _ (SigRed VΓ VF'0 VG'0 tΔ Vσ) _ _)).
      eapply over_tree_fusion_r, over_tree_fusion_l, over_tree_fusion_r ; exact Ho'.
    - eapply LRTyEqIrrelevantCum' ; [reflexivity | ].
      unshelve refine (WRedEq _ (SigCongRed VΓ VF0 VG0 VF'0 VG'0 _ _ tΔ Vσ) _ _ _).
      + exact (univEqValid VΓ (UValid VΓ) VF0 VFF').
      + pose proof (univEqValid (validSnoc' VΓ VF) VU (univValid (l' := zero) _ _ VGU) VGG') as VGG'0.
        refine (irrelevanceTyEq _ _ _ _ VGG'0).
      + eapply over_tree_fusion_l, over_tree_fusion_r, over_tree_fusion_r ; exact Ho'.
      + eapply over_tree_fusion_r, over_tree_fusion_r, over_tree_fusion_r ; exact Ho'.
  Qed.

End SigTmCongruence.

Section ProjRed.
  Context `{GenericTypingProperties}.

  Lemma fstRed {l wl Δ F G} {p}
    (RΣ : [Δ ||-Σ<l> tSig F G]< wl >)
    (RF : [Δ ||-<l> F]< wl >)
    (Rp : [Δ ||-<l> p : _ | LRSig' (normRedΣ0 RΣ)]< wl >) :
    ([Δ ||-<l> tFst p : _ | RF]< wl > × [Δ ||-<l> tFst p ≅ tFst Rp.(SigRedTm.nf) : _ | RF]< wl >) ×
      [Δ ||-<l> tFst Rp.(SigRedTm.nf) : _ | RF]< wl >.
  Proof.
    assert [Δ ||-<l> tFst Rp.(SigRedTm.nf) : _ | RF]< wl >.
    1:{
      assert (wfΔ : [|-Δ]< wl >) by (escape; gen_typing).
      pose (r := SigRedTm.fstRed Rp (@wk_id Δ) ((idε) wl) wfΔ).
      rewrite wk_id_ren_on in r.
      irrelevance.
    }
    split; tea.
    irrelevanceRefl.
    eapply redSubstTerm; tea. 
    eapply redtm_fst; now destruct (SigRedTm.red Rp).
  Qed.

  Lemma fstRedEq {l wl Δ F G} {p p'}
    (RΣ : [Δ ||-Σ<l> tSig F G]< wl >)
    (RF : [Δ ||-<l> F]< wl >)
    (RΣn := LRSig' (normRedΣ0 RΣ))
    (Rpp' : [Δ ||-<l> p ≅ p' : _ | RΣn]< wl >) 
    (Rp := SigRedTmEq.redL Rpp')
    (Rp' := SigRedTmEq.redR Rpp') :
    [× [Δ ||-<l> tFst p ≅ tFst Rp.(SigRedTm.nf) : _ | RF]< wl >,
    [Δ ||-<l> tFst p' ≅ tFst Rp'.(SigRedTm.nf) : _ | RF]< wl > &
    [Δ ||-<l> tFst Rp.(SigRedTm.nf) ≅ tFst Rp'.(SigRedTm.nf) : _ | RF]< wl >].
  Proof.
    split.
    - now eapply fstRed.
    - now eapply fstRed.
    - assert (wfΔ : [|-Δ]< wl >) by (escape; gen_typing).
      epose (e := SigRedTmEq.eqFst Rpp' wk_id ((idε) wl) wfΔ).
      do 2 rewrite wk_id_ren_on in e.
      irrelevance.
  Qed.

  
  Lemma sndRed {l wl Δ F G} {p}
    (RΣ : [Δ ||-Σ<l> tSig F G]< wl >)
    (RF : [Δ ||-<l> F]< wl >)
    (RΣn := LRSig' (normRedΣ0 RΣ))
    (Rp : [Δ ||-<l> p : _ | LRSig' (normRedΣ0 RΣ)]< wl >)
    (RGfstp : W[Δ ||-<l> G[(tFst p)..]]< wl >) 
    (RGfstpEq : W[Δ ||-<l> G[(tFst p)..] ≅ G[(tFst Rp.(SigRedTm.nf))..] | RGfstp]< wl >) :
    W[Δ ||-<l> tSnd p : _ | RGfstp]< wl > × W[Δ ||-<l> tSnd p ≅ tSnd Rp.(SigRedTm.nf) : _ | RGfstp]< wl >.
  Proof.
    eapply WredSubstTerm. 
    2: eapply redtm_snd; now destruct (SigRedTm.red Rp).
    assert (wfΔ : [|-Δ]< wl >) by (escape; gen_typing).
    eapply WLRTmRedConv.
    + unshelve eapply WLRTyEqSym. 2: tea.
      shelve.
    + econstructor ; intros wl'' Ho Ho'.      
      epose proof (r := SigRedTm.sndRed Rp (@wk_id Δ) ((idε) wl) wfΔ).
      rewrite <- (wk_id_ren_on Δ (SigRedTm.nf Rp)).
      irrelevance0 ; [reflexivity | eapply r].
      Unshelve.
      eapply over_tree_fusion_l ; exact Ho'.
      4: eapply over_tree_fusion_r ; exact Ho'.
      assumption.
      * unshelve epose proof (Heq := redtywf_whnf (ParamRedTy.red RΣ) whnf_tSig).
        inversion Heq.
        econstructor ; intros wl' Ho.
        cbn.
        replace G[tFst (SigRedTm.nf Rp)⟨wk_id⟩ .: _wk_id Δ >> tRel]
          with G[tFst (SigRedTm.nf Rp) .: (@wk_id Δ) >> tRel] by now bsimpl.
        rewrite H12.
        unshelve eapply (PolyRed.posRed _ (@wk_id Δ) ((idε) wl) wfΔ _ Ho).
        2: exact (ParamRedTy.polyRed RΣ).
        replace (tFst (SigRedTm.nf Rp)) with (tFst (SigRedTm.nf Rp))⟨@wk_id Δ⟩ by now bsimpl.
        irrelevance0 ; [  | eapply (SigRedTm.fstRed Rp wk_id ((idε) wl) wfΔ)].
        cbn ; now rewrite H11.
      * cbn.
        replace G[tFst (SigRedTm.nf Rp)⟨wk_id⟩ .: _wk_id Δ >> tRel] with G[(tFst (SigRedTm.nf Rp))..] by now bsimpl.
        eassumption.
  Qed.
  
  Lemma sndRedEq {l wl Δ F G} {p p'}
    (RΣ : [Δ ||-Σ<l> tSig F G]< wl >)
    (RF : [Δ ||-<l> F]< wl >)
    (RΣn := LRSig' (normRedΣ0 RΣ))
    (Rpp' : [Δ ||-<l> p ≅ p' : _ | RΣn]< wl >) 
    (Rp := SigRedTmEq.redL Rpp')
    (Rp' := SigRedTmEq.redR Rpp')
    (RGfstp : W[Δ ||-<l> G[(tFst p)..]]< wl >) 
    (RGfstpEq : W[Δ ||-<l> G[(tFst p)..] ≅ G[(tFst Rp.(SigRedTm.nf))..] | RGfstp]< wl >)
    (RGfstp' : W[Δ ||-<l> G[(tFst p')..]]< wl >) 
    (RGfstpEq' : W[Δ ||-<l> G[(tFst p')..] ≅ G[(tFst Rp'.(SigRedTm.nf))..] | RGfstp']< wl >) :
    [× W[Δ ||-<l> tSnd p ≅ tSnd Rp.(SigRedTm.nf) : _ | RGfstp]< wl >,
    W[Δ ||-<l> tSnd p' ≅ tSnd Rp'.(SigRedTm.nf) : _ | RGfstp']< wl > &
    W[Δ ||-<l> tSnd Rp.(SigRedTm.nf) ≅ tSnd Rp'.(SigRedTm.nf) : _ | RGfstp]< wl >].
  Proof.
    split.
    - now eapply sndRed.
    - now eapply sndRed.
    - assert (wfΔ : [|-Δ]< wl >) by (escape; gen_typing).
      unshelve eapply WLRTmEqRedConv; cycle 2.
      1:{ econstructor ; intros wl'' Ho.
          eapply (PolyRed.posRed (ParamRedTy.polyRed (normRedΣ0 RΣ))) ; exact Ho.
      }
      2:{ econstructor ; intros wl'' Ho Ho'.
          epose proof (e := SigRedTmEq.eqSnd Rpp' wk_id ((idε) wl) wfΔ).
          cbn in*.
          rewrite <- (wk_id_ren_on Δ (SigRedTm.nf Rp)).
          rewrite <- (wk_id_ren_on Δ (SigRedTm.nf Rp')).
          eapply e.
          eassumption.
      }
    + unshelve eapply WLRTyEqSym. 2: tea.
      rewrite wk_id_shift; rewrite wk_id_ren_on; tea.
  Qed.


  Context {l wl Γ F G } (VΓ : [||-v Γ]< wl >)
    (VF : [Γ ||-v< l > F | VΓ ]< wl >)
    (VG : [Γ ,, F ||-v< l > G | validSnoc' VΓ VF]< wl >)
    (VΣ := SigValid VΓ VF VG).

  Lemma fstValid {p} (Vp : [Γ ||-v<l> p : _ | VΓ | VΣ]< wl >): [Γ ||-v<l> tFst p : _ | VΓ | VF]< wl >.
  Proof.
    unshelve econstructor.
    - intros ???? wfΔ Vσ.
      instValid Vσ.
      econstructor ; intros wl'' Ho Ho'.
      unshelve eapply fstRed ; fold subst_term in *.
      3: irrelevance0 ; [ | eapply RVp].
      2: eapply invLRΣ, (WRed _ RVΣ _ _) ; refold.
      1: now bsimpl. 
      Unshelve.
      1: now eapply over_tree_fusion_l, over_tree_fusion_l ; exact Ho'.
      1: now eapply over_tree_fusion_r, over_tree_fusion_l ; exact Ho'.
      now eapply over_tree_fusion_r ; exact Ho'.
    - intros ????? wfΔ Vσ Vσ' Vσσ'.
      instAllValid Vσ Vσ' Vσσ'.
      eexists (DTree_fusion _ _ _).
      intros wl'' Ho Ho'.
      epose proof (Hyp:= invLRΣ (WRed _ RVΣ _ _)); fold subst_term in *.
      epose proof (Hyp2 := WRedTmEq _ REVp _ _ _).
      unshelve refine (let RΣinv := _ : [Δ ||-Σ< l > (tSig F G)[σ] ]< wl'' > in _).
      1: now eapply ( (invLRΣ (WRed _ (validTy VΣ f wfΔ Vσ) _ _))).
      unshelve eassert (RΣinv' : [_ ||-<_> p[σ] ≅ p[σ'] : (tSig F G)[σ] | LRSig' (normRedΣ0 RΣinv)]< wl'' >).
      all: fold subst_term in *.
      1: now irrelevance.      
      unshelve edestruct (fstRedEq RΣinv (WRed _ RVF _ (over_tree_fusion_r Ho')) RΣinv').
      eapply LREqTermHelper; tea; eapply reflLRTyEq.
      Unshelve.
      3: eapply over_tree_fusion_l, over_tree_fusion_l, over_tree_fusion_l ; exact Ho'.
      1: eapply over_tree_fusion_r, over_tree_fusion_l, over_tree_fusion_l ; exact Ho'.
      1: eapply over_tree_fusion_l, over_tree_fusion_r, over_tree_fusion_l ; exact Ho'.
      1: eapply over_tree_fusion_r, over_tree_fusion_r, over_tree_fusion_l ; exact Ho'.
  Qed.  
  
  Lemma fstCongValid {p p'} 
    (Vp : [Γ ||-v<l> p : _ | VΓ | VΣ]< wl >)
    (Vp' : [Γ ||-v<l> p' : _ | VΓ | VΣ]< wl >) 
    (Vpp' : [Γ ||-v<l> p ≅ p' : _ | VΓ | VΣ]< wl >)
    : [Γ ||-v<l> tFst p ≅ tFst p' : _ | VΓ | VF]< wl >.
  Proof.
    constructor; intros ???? wfΔ Vσ.
    instValid Vσ; instValidExt Vσ (reflSubst _ _ _ Vσ).
    unshelve econstructor ; [ do 2 eapply DTree_fusion ; shelve | ].
    intros wl'' Ho Ho'.
    unshelve refine (let RΣinv := _ : [Δ ||-Σ< l > (tSig F G)[σ] ]< wl'' > in _).
    1: now eapply ( (invLRΣ (WRed _ (validTy VΣ f wfΔ Vσ) _ _))).
    unshelve eassert (RΣinv' : [_ ||-<_> p[σ] ≅ p'[σ] : (tSig F G)[σ] | LRSig' (normRedΣ0 RΣinv)]< wl'' >).
    all: fold subst_term in *.
    1: irrelevanceRefl ; eapply RVpp', over_tree_fusion_l, over_tree_fusion_l ; exact Ho'. 
    destruct (fstRedEq RΣinv (WRed _ RVF _ (over_tree_fusion_r (over_tree_fusion_l Ho'))) RΣinv').
    eapply LREqTermHelper; tea.
    eapply REVF, over_tree_fusion_l, over_tree_fusion_r  ; exact Ho'.
    Unshelve.
    2,3: do 2 eapply over_tree_fusion_r ; exact Ho'.
  Qed.  
  
  Lemma sndValid {p} (Vp : [Γ ||-v<l> p : _ | VΓ | VΣ]< wl >)
    (VGfst := substS VG (fstValid Vp)) : 
    [Γ ||-v<l> tSnd p : _ | VΓ | VGfst]< wl >.
  Proof.
    unshelve econstructor.
    - intros ???? wfΔ Vσ.
      instValid Vσ.
      unshelve eapply TreeTmSplit ; [do 2 eapply DTree_fusion ; shelve | ].
      intros wl'' Ho Ho'.
      pose (f':= over_tree_le Ho).
      unshelve refine (let RΣinv := _ : [Δ ||-Σ< l > (tSig F G)[σ] ]< wl'' > in _).
      1: now eapply ( (invLRΣ (WRed _ (validTy VΣ f wfΔ Vσ) _ _))).
      unshelve refine (let RΣinv' : [_ ||-<_> p[σ] : (tSig F G)[σ] | LRSig' (normRedΣ0 RΣinv)]< wl'' > := _ in _).
      all: fold subst_term in *.
      1: irrelevanceRefl ; eapply RVp, over_tree_fusion_l, over_tree_fusion_l ; exact Ho.
      destruct (fstRed RΣinv (WRed _ RVF _ (over_tree_fusion_r (over_tree_fusion_l Ho))) RΣinv')
        as [[Rfstp Rfstpeq] Rfstnf].
      unshelve epose (Vpσ := consSubstS _ _ (subst_Ltrans f' _ Vσ) (Validity_Ltrans _ VF) (TmLogtoW' Rfstp _)).
      2: unshelve epose (Vnfσ := consSubstS _ _ (subst_Ltrans f' _ Vσ) (Validity_Ltrans _ VF) (TmLogtoW' Rfstnf _)).
      3: unshelve epose (Veqσ := consSubstSEq' _ _ _ _ (Validity_Ltrans _ VF) (TmLogtoW' Rfstp _) (TmEqLogtoW' Rfstpeq _)).
      7: now eapply reflSubst.
      5: now eapply subst_Ltrans.
      1,2,3: now eapply wfc_Ltrans.
      instAllValid Vpσ Vnfσ Veqσ.
      unshelve epose (fst (sndRed RΣinv (WRed _ RVF _ (over_tree_fusion_r (over_tree_fusion_l Ho))) RΣinv' _ _)).
      all: fold subst_term in *.
      + rewrite up_subst_single ; exact RVG.
      + cbn ; Wirrelevance0; rewrite up_subst_single ; [reflexivity | eassumption ].
      + cbn in * ; Wirrelevance0 ; [ | eapply w] ; rewrite up_subst_single ; now bsimpl. 
        Unshelve.
        3,4: eapply over_tree_fusion_l, over_tree_fusion_r ; exact Ho.
        now constructor.
    - intros ????? wfΔ Vσ Vσ' Vσσ'.
      pose proof (Vfstp := fstValid Vp).
      instAllValid Vσ Vσ' Vσσ'.
      unshelve eapply TreeTmEqSplit ; [do 3 eapply DTree_fusion ; shelve | ].
      intros wl'' Ho Ho'.
      pose (f':= over_tree_le Ho).
      pose (HF := (WRed _ RVF _ (over_tree_fusion_r (over_tree_fusion_r (over_tree_fusion_l Ho))))).
      unshelve refine (let RΣinv := _ : [Δ ||-Σ< l > (tSig F G)[σ] ]< wl'' > in _).
      1: now eapply ( (invLRΣ (WRed _ (validTy VΣ f wfΔ Vσ) _ _))).
      unshelve refine (let RΣinv' := _ : [Δ ||-Σ< l > (tSig F G)[σ'] ]< wl'' > in _).
      1: now eapply ( (invLRΣ (WRed _ (validTy VΣ f wfΔ Vσ') _ _))).
      unshelve refine (let RHp : [_ ||-<_> p[σ] : (tSig F G)[σ] | LRSig' (normRedΣ0 RΣinv)]< wl'' > := _ in _).
      1: irrelevanceRefl ; eapply RVp ; do 3 (eapply over_tree_fusion_l) ; exact Ho.
      unshelve refine (let RHp' : [_ ||-<_> p[σ'] : (tSig F G)[σ'] | LRSig' (normRedΣ0 RΣinv')]< wl'' > := _ in _).
      1: irrelevanceRefl ; eapply RVp0, over_tree_fusion_r, over_tree_fusion_l, over_tree_fusion_l ; exact Ho.
      unshelve refine (let RHp'' : [_ ||-<_>  p[σ] ≅ p[σ'] : (tSig F G)[σ] | LRSig' (normRedΣ0 RΣinv)]< wl'' > := _ in _).
      all: fold subst_term in *.
      1: irrelevanceRefl ; eapply REVp, over_tree_fusion_l, over_tree_fusion_r, over_tree_fusion_l ; exact Ho.
      destruct (fstRed RΣinv HF RHp''.(SigRedTmEq.redL)) as [[Rfstp Rfstpeq] Rfstnf].
      unshelve epose (Vpσ := consSubstS _ _ (subst_Ltrans f' _ Vσ) (Validity_Ltrans _ VF) (TmLogtoW' Rfstp _)).
      2: unshelve epose (Vnfσ := consSubstS _ _ (subst_Ltrans f' _ Vσ) (Validity_Ltrans _ VF) (TmLogtoW' Rfstnf _)).
      3: unshelve epose (Veqσ := consSubstSEq' _ _ _ _ (Validity_Ltrans _ VF) (TmLogtoW' Rfstp _) (TmEqLogtoW' Rfstpeq _)).
      7: now eapply reflSubst.
      5: now eapply subst_Ltrans.
      1,2,3: now eapply wfc_Ltrans.
      instAllValid Vpσ Vnfσ Veqσ.
      destruct (fstRed RΣinv HF RHp''.(SigRedTmEq.redR)) as [[Rfstp' Rfstpeq'] Rfstnf'].
      unshelve epose (Vpσ' := consSubstS _ _ (subst_Ltrans f' _ Vσ) (Validity_Ltrans _ VF) (TmLogtoW' Rfstp' _)).
      2: unshelve epose (Vnfσ' := consSubstS _ _ (subst_Ltrans f' _ Vσ) (Validity_Ltrans _ VF) (TmLogtoW' Rfstnf' _)).
      3: unshelve epose (Veqσ' := consSubstSEq' _ _ _ _ (Validity_Ltrans _ VF) (TmLogtoW' Rfstp' _) (TmEqLogtoW' Rfstpeq' _)).
      7: now eapply reflSubst.
      5: now eapply subst_Ltrans.
      1,2,3: now eapply wfc_Ltrans.
      instAllValid Vpσ' Vnfσ' Veqσ'.
      unshelve epose proof (r := sndRedEq RΣinv HF RHp'' _ _ _ _).
      all: fold subst_term in *.
      + rewrite up_subst_single ; exact RVG.
      + cbn ; Wirrelevance0; rewrite up_subst_single ; [reflexivity | eassumption ].
      + rewrite up_subst_single ; eassumption.
      + cbn ; Wirrelevance0; rewrite up_subst_single ; [reflexivity | eassumption ].
      + destruct r; Wirrelevance0; cycle 1.
        1: eapply WLREqTermHelper.
        1,2,4: tea.
        2: now rewrite singleSubstComm'.
        unshelve epose (Veqσ0 := consSubstSEq' _ _ _ _ (Validity_Ltrans _ VF) (TmLogtoW' Rfstp _) (WTmEq_Ltrans' _ _ _ REVfstp)).
        5: now eapply reflSubst.
        3: now eapply subst_Ltrans.
        1: now eapply wfc_Ltrans.
        1: assumption.
        instAllValid Vpσ Vpσ' Veqσ0.
        cbn ; Wirrelevance0; rewrite up_subst_single; tea; reflexivity.
        Unshelve.
        5,7,9: eapply over_tree_fusion_l, over_tree_fusion_l, over_tree_fusion_r ; exact Ho.
        4,5: eapply over_tree_fusion_r, over_tree_fusion_l, over_tree_fusion_r ; exact Ho.
        all: now constructor.
Qed.

  Lemma sndCongValid {p p'} 
    (Vp : [Γ ||-v<l> p : _ | VΓ | VΣ]< wl >)
    (Vp' : [Γ ||-v<l> p' : _ | VΓ | VΣ]< wl >) 
    (Vpp' : [Γ ||-v<l> p ≅ p' : _ | VΓ | VΣ]< wl >)
    (VGfst := substS VG (fstValid Vp)) : 
    [Γ ||-v<l> tSnd p ≅ tSnd p' : _ | VΓ | VGfst]< wl >.
  Proof.
    constructor; intros ???? wfΔ Vσ.
    pose proof (VGfsteq:= substSEq (reflValidTy _ VF) VG (reflValidTy _ VG) (fstValid Vp) (fstValid Vp') (fstCongValid Vp Vp' Vpp')). 
    cbn in VGfsteq.
    instValid Vσ ; instValidExt Vσ (reflSubst _ _ _ Vσ).
    unshelve eapply TreeTmEqSplit ; [do 3 eapply DTree_fusion ; shelve | ].
    intros wl'' Ho Ho'.
    pose (f':= over_tree_le Ho).
    pose (HF := (WRed _ RVF _ (over_tree_fusion_r (over_tree_fusion_r (over_tree_fusion_l Ho))))).
    unshelve refine (let RΣinv := _ : [Δ ||-Σ< l > (tSig F G)[σ] ]< wl'' > in _).
    1: now eapply ( (invLRΣ (WRed _ (validTy VΣ f wfΔ Vσ) _ _))).
    unshelve refine (let RHp : [_ ||-<_> p[σ] : (tSig F G)[σ] | LRSig' (normRedΣ0 RΣinv)]< wl'' > := _ in _).
    1: irrelevanceRefl ; eapply RVp ; do 3 (eapply over_tree_fusion_l) ; exact Ho.
    unshelve refine (let RHp' : [_ ||-<_> p'[σ] : (tSig F G)[σ] | LRSig' (normRedΣ0 RΣinv)]< wl'' > := _ in _).
    1: irrelevanceRefl ; eapply RVp', over_tree_fusion_r, over_tree_fusion_l, over_tree_fusion_l ; exact Ho.
    unshelve refine (let RHp'' : [_ ||-<_>  p[σ] ≅ p'[σ] : (tSig F G)[σ] | LRSig' (normRedΣ0 RΣinv)]< wl'' > := _ in _).
    all: fold subst_term in *.
    1: irrelevanceRefl ; eapply RVpp', over_tree_fusion_l, over_tree_fusion_r, over_tree_fusion_l ; exact Ho.
    destruct (fstRed RΣinv HF RHp''.(SigRedTmEq.redL)) as [[Rfstp Rfstpeq] Rfstnf].
    unshelve epose (Vpσ := consSubstS _ _ (subst_Ltrans f' _ Vσ) (Validity_Ltrans _ VF) (TmLogtoW' Rfstp _)).
    2: unshelve epose (Vnfσ := consSubstS _ _ (subst_Ltrans f' _ Vσ) (Validity_Ltrans _ VF) (TmLogtoW' Rfstnf _)).
    3: unshelve epose (Veqσ := consSubstSEq' _ _ _ _ (Validity_Ltrans _ VF) (TmLogtoW' Rfstp _) (TmEqLogtoW' Rfstpeq _)).
    7: now eapply reflSubst.
    5: now eapply subst_Ltrans.
    1,2,3: now eapply wfc_Ltrans.
    instAllValid Vpσ Vnfσ Veqσ.
    destruct (fstRed RΣinv HF RHp''.(SigRedTmEq.redR)) as [[Rfstp' Rfstpeq'] Rfstnf'].
    unshelve epose (Vpσ' := consSubstS _ _ (subst_Ltrans f' _ Vσ) (Validity_Ltrans _ VF) (TmLogtoW' Rfstp' _)).
    2: unshelve epose (Vnfσ' := consSubstS _ _ (subst_Ltrans f' _ Vσ) (Validity_Ltrans _ VF) (TmLogtoW' Rfstnf' _)).
    3: unshelve epose (Veqσ' := consSubstSEq' _ _ _ _ (Validity_Ltrans _ VF) (TmLogtoW' Rfstp' _) (TmEqLogtoW' Rfstpeq' _)).
    7: now eapply reflSubst.
    5: now eapply subst_Ltrans.
    1,2,3: now eapply wfc_Ltrans.
    instAllValid Vpσ' Vnfσ' Veqσ'.
    unshelve epose proof (r := sndRedEq RΣinv HF RHp'' _ _ _ _).
    all: fold subst_term in *.
    + rewrite up_subst_single ; exact RVG.
    + cbn ; Wirrelevance0; rewrite up_subst_single ; [reflexivity | eassumption ].
    + rewrite up_subst_single ; eassumption.
    + cbn ; Wirrelevance0; rewrite up_subst_single ; [reflexivity | eassumption ].
    + destruct r; Wirrelevance0; cycle 1.
      1: eapply WLREqTermHelper.
      1,2,4: tea.
      2: now rewrite singleSubstComm'.
      cbn ; Wirrelevance0 ; rewrite up_subst_single ; change (tFst ?p[?σ]) with (tFst p)[σ]; rewrite <- singleSubstComm.
      1: reflexivity.
      eapply WEq_Ltrans ; eassumption.
      Unshelve.
      5-8: eapply over_tree_fusion_l, over_tree_fusion_l, over_tree_fusion_r ; exact Ho.
      1-3: now constructor.
      assumption.
  Qed.

  
End ProjRed.



Section PairRed.
  Context `{GenericTypingProperties}.

  Lemma pairFstRed {wl Γ A B a b l}
    (RA : [Γ ||-<l> A]< wl >)
    (RB : W[Γ ,, A ||-<l> B]< wl >)
    (RBa : W[Γ ||-<l> B[a..]]< wl >)
    (Ra : [Γ ||-<l> a : A | RA]< wl >)
    (Rb : W[Γ ||-<l> b : _ | RBa ]< wl >) :
    [Γ ||-<l> tFst (tPair A B a b) : _ | RA]< wl > × [Γ ||-<l> tFst (tPair A B a b) ≅ a : _ | RA]< wl >.
  Proof.
    escape ; Wescape.
    eapply redSubstTerm; tea.
    eapply redtm_fst_beta; tea.
  Qed.

  Lemma WpairFstRed {wl Γ A B a b l}
    (RA : W[Γ ||-<l> A]< wl >)
    (RB : W[Γ ,, A ||-<l> B]< wl >)
    (RBa : W[Γ ||-<l> B[a..]]< wl >)
    (Ra : W[Γ ||-<l> a : A | RA]< wl >)
    (Rb : W[Γ ||-<l> b : _ | RBa ]< wl >) :
    W[Γ ||-<l> tFst (tPair A B a b) : _ | RA]< wl > × W[Γ ||-<l> tFst (tPair A B a b) ≅ a : _ | RA]< wl >.
  Proof.
    Wescape.
    eapply WredSubstTerm; tea.
    eapply redtm_fst_beta; tea.
  Qed.
    
    

  Lemma pairSndRed {wl Γ A B a b l}
    (RA : [Γ ||-<l> A]< wl >)
    (RB : [Γ ,, A ||-<l> B]< wl >)
    (RBa : [Γ ||-<l> B[a..]]< wl >)
    (RBfst : [Γ ||-<l> B[(tFst (tPair A B a b))..] ]< wl >)
    (RBconv : [Γ ||-<l> B[a..] ≅ B[(tFst (tPair A B a b))..] | RBa ]< wl >)
    (Ra : [Γ ||-<l> a : A | RA]< wl >)
    (Rb : [Γ ||-<l> b : _ | RBa ]< wl >) :
    [Γ ||-<l> tSnd (tPair A B a b) : _ | RBfst ]< wl > × [Γ ||-<l> tSnd (tPair A B a b) ≅ b : _ | RBfst]< wl >.
  Proof.
    escape.
    eapply redSubstTerm; tea.
    2: eapply redtm_snd_beta; tea.
    now eapply LRTmRedConv.
  Qed.

  

  Lemma WpairSndRed {wl Γ A B a b l}
    (RA : W[Γ ||-<l> A]< wl >)
    (RB : W[Γ ,, A ||-<l> B]< wl >)
    (RBa : W[Γ ||-<l> B[a..]]< wl >)
    (RBfst : W[Γ ||-<l> B[(tFst (tPair A B a b))..] ]< wl >)
    (RBconv : W[Γ ||-<l> B[a..] ≅ B[(tFst (tPair A B a b))..] | RBa ]< wl >)
    (Ra : W[Γ ||-<l> a : A | RA]< wl >)
    (Rb : W[Γ ||-<l> b : _ | RBa ]< wl >) :
    W[Γ ||-<l> tSnd (tPair A B a b) : _ | RBfst ]< wl > × W[Γ ||-<l> tSnd (tPair A B a b) ≅ b : _ | RBfst]< wl >.
  Proof.
    escape ; Wescape.
    eapply WredSubstTerm; tea.
    2: eapply redtm_snd_beta; tea.
    now eapply WLRTmRedConv.
  Qed.

  Lemma pairRed {wl Γ A B a b l}
    (RΣ0 : [Γ ||-Σ<l> tSig A B]< wl >)
    (RΣ := normRedΣ0 RΣ0)
    (RA : [Γ ||-<l> A]< wl >)
    (RBa : W[Γ ||-<l> B[a..]]< wl >)
    (RBconv : W[Γ ||-<l> B[a..] ≅ B[(tFst (tPair A B a b))..] | RBa ]< wl >)
    (RBfst : W[Γ ||-<l> B[(tFst (tPair A B a b))..] ]< wl >)
    (Ra : [Γ ||-<l> a : A | RA]< wl >)
    (Rb : W[Γ ||-<l> b : _ | RBa ]< wl >) :
    [Γ ||-<l> tPair A B a b : _ | LRSig' RΣ]< wl >.
  Proof.
    destruct (polyRedId RΣ); escape ; Wescape. 
    unshelve eexists (tPair A B a b) _ _.
    - intros ?? ρ ? wfΔ.
      rewrite wk_fst; irrelevanceRefl; unshelve eapply wkTerm.
      1:tea.
      2: eapply (Tm_Ltrans f) ; unshelve eapply pairFstRed; now tea.
    - intros ; do 2 eapply DTree_fusion ; [ .. | eapply DTree_fusion] ; shelve.
    - eapply redtmwf_refl; cbn.
      eapply ty_pair; now tea.
    - eapply convtm_eta_sig; tea.
      + now eapply ty_pair.
      + constructor; tea.
        2-4: now (unshelve eapply WescapeEq, WreflLRTyEq; [|tea]).
        now (unshelve eapply escapeEq, reflLRTyEq; [|tea]).
      + now eapply ty_pair.
      + constructor; tea.
        2-4: (unshelve eapply WescapeEq, WreflLRTyEq; [|tea]).
        now (unshelve eapply escapeEq, reflLRTyEq; [|tea]).
      + enough [Γ |- tFst (tPair A B a b) ≅ a : A]< wl >.
        1: transitivity a; tea; now symmetry.
        eapply convtm_exp.
        * now eapply redtm_fst_beta.
        * now eapply redtmwf_refl.
        * tea.
        * tea.
        * tea.
        * unshelve eapply escapeEq, reflLRTyEq; [|tea].
        * eapply escapeEqTerm; now eapply reflLRTmEq.
      + enough [Γ |- tSnd (tPair A B a b) ≅ b : B[(tFst (tPair A B a b))..]]< wl >.
        1: transitivity b; tea; now symmetry.
        eapply convtm_conv; tea.
        eapply convtm_exp.
        * eapply redtm_conv; [| now symmetry]; now eapply redtm_snd_beta.
        * now eapply redtm_refl.
        * tea.
        * tea.
        * tea.
        * now unshelve eapply WescapeEq, WreflLRTyEq; [|tea].
        * eapply WescapeEqTerm; now eapply WreflLRTmEq.
    - unshelve econstructor; cbn; intros.
      + now constructor.
      + irrelevance0; [reflexivity|eapply wkTerm, Tm_Ltrans].
        apply Ra.
        Unshelve. 1-5: shelve. all: now tea.
      + eapply DTree_fusion ; shelve.
      + now apply reflLRTyEq.
      + now apply reflLRTyEq.
      + cbn in *.
        assert (Hrw : B[a⟨ρ⟩ .: ρ >> tRel] = B[a..]⟨ρ⟩) by now bsimpl.
        irrelevance0; [symmetry; apply Hrw|eapply wkTerm].
        eapply (WTm_Ltrans f _ Rb), over_tree_fusion_l ; exact Ho'. 
        Unshelve. 1-5: shelve.
        1: now eapply wfc_Ltrans ; [ now eapply over_tree_le | ].
        1: now eapply over_tree_fusion_r ; exact Ho'.
    - intros ?? ρ ? wfΔ ???.
      pose (f' := over_tree_le Ho).
      irrelevance0.
      2: rewrite wk_snd; eapply wkTerm; eapply pairSndRed.
      now rewrite subst_ren_subst_mixed.
      1: cbn in *. eapply w.
      2: eapply RBconv.
      3: unshelve eapply Tm_Ltrans ; [ | now eapply wfLCon_le_trans| | exact Ra ].
      3: eapply Rb.
      Unshelve. 4-8: shelve.
      5: eapply RBfst.
      4: now eapply wfc_Ltrans ; [ now eapply over_tree_le | ].
      all: unshelve eapply over_tree_Ltrans ; [| eassumption | ].
      1: do 2 eapply over_tree_fusion_l ; exact Ho'.
      1: eapply over_tree_fusion_r, over_tree_fusion_l ; exact Ho'.
      1: eapply over_tree_fusion_l, over_tree_fusion_r ; exact Ho'.
      1: eapply over_tree_fusion_l ; do 2 eapply over_tree_fusion_r ; exact Ho'.
      1: do 3 eapply over_tree_fusion_r ; exact Ho'.
  Qed.
  
  Lemma WpairRed {wl Γ A B a b l}
    (RΣ : W[Γ ||-<l> tSig A B]< wl >)
    (RA : W[Γ ||-<l> A]< wl >)
    (RBa : W[Γ ||-<l> B[a..]]< wl >)
    (RBconv : W[Γ ||-<l> B[a..] ≅ B[(tFst (tPair A B a b))..] | RBa ]< wl >)
    (RBfst : W[Γ ||-<l> B[(tFst (tPair A B a b))..] ]< wl >)
    (Ra : W[Γ ||-<l> a : A | RA]< wl >)
    (Rb : W[Γ ||-<l> b : _ | RBa ]< wl >) :
    W[Γ ||-<l> tPair A B a b : _ | RΣ]< wl >.
  Proof.
    unshelve econstructor ; [do 2 eapply DTree_fusion ; shelve | ].
    intros wl' Ho Ho'.
    pose (f' := over_tree_le Ho).
    irrelevanceRefl ; unshelve eapply pairRed.
    3,5: now eapply WLtrans.
    3: now eapply WEq_Ltrans.
    4: now eapply WTm_Ltrans.
    + unshelve eapply invLRΣ, RΣ.
      eapply over_tree_fusion_l, over_tree_fusion_l ; exact Ho'.
    + eapply RA.
      eapply over_tree_fusion_r, over_tree_fusion_l ; exact Ho'.
    + eapply Ra.
      eapply over_tree_fusion_l, over_tree_fusion_r ; exact Ho'.
      Unshelve.
      now constructor.
  Qed.
  
  Lemma isLRPair_isWfPair {wl Γ A B l p} (wfΓ : [|- Γ]< wl >) (ΣA : [Γ ||-Σ<l> tSig A B]< wl >)
  (RA : [Γ ||-<l> A]< wl >)
  (Rp : [Γ ||-Σ p : _ | normRedΣ0 ΣA]< wl >) :
    isWfPair wl Γ A B (SigRedTm.nf Rp).
  Proof.
  destruct Rp; simpl; intros.
  destruct ispair as [A' B' a b HA Htree HB Ha Hbtree Hb|]; [|constructor; tea].
  assert (Hrw : forall A t, t[tRel 0 .: @wk1 Γ A >> tRel] = t).
  { intros; bsimpl; apply idSubst_term; intros []; reflexivity. }
  assert (Hrw' : forall a t, t[a .: @wk_id Γ >> tRel] = t[a..]).
  { intros; now bsimpl. }
  assert [Γ |-[ ta ] A]< wl >.
  { now unshelve eapply escape. }
  assert [Γ |-[ ta ] A']< wl >.
  { rewrite <- (wk_id_ren_on Γ A'); unshelve eapply escapeConv, HA.
    1: now eapply wfLCon_le_id.
    now gen_typing. }
  assert [|-[ ta ] Γ,, A']< wl >.
  { now eapply wfc_cons. }
  assert [Γ |-[ ta ] A ≅ A']< wl >.
  { rewrite <- (wk_id_ren_on Γ A), <- (wk_id_ren_on Γ A').
    eapply escapeEq; unshelve apply HA ; [ | now gen_typing].
    now eapply wfLCon_le_id.
  }
  assert (RB :
    forall (Δ : context) wl' (a : term) (ρ : Δ ≤ Γ) f (h : [ |-[ ta ] Δ]< wl' >)
       (ha : [PolyRedPack.shpRed (normRedΣ0 ΣA) ρ f h | Δ ||- a
             : (ParamRedTyPack.dom (normRedΣ0 ΣA))⟨ρ⟩]< wl' >),
     W[Δ ||-<l> B[a .: ρ >> tRel]]< wl' >
  ).
  { intros Δ ? a0 ? ? ? ha0.
    econstructor ; intros wl'' Ho.
    unshelve econstructor.
    + eapply (PolyRedPack.posRed _ _ _ _ ha0).
      eassumption.
    + eapply PolyRedPack.posAd, PolyRed.toAd. }
  constructor; tea.
  - rewrite <- (Hrw A' B); unshelve eapply Wescape, RB; tea.
    1: now eapply wfLCon_le_id.
    apply var0conv; cbn; [|tea].
    rewrite <- (@wk1_ren_on Γ A' A'); apply convty_wk; [tea|now symmetry].
  - rewrite <- (Hrw A' B'); unshelve eapply WescapeConv.
    3:{ eexists (PolyRedPack.posTree (normRedΣ0 ΣA) _ _ _ _).
        intros ; eapply (PolyRed.posRed (normRedΣ0 ΣA)).
        exact Ho.
    }
    eexists (Htree _ _ _ _ _ _ _).
    intros ; eapply HB.
    exact Hover'.
    Unshelve.
    1: now eapply wfLCon_le_id.
    1: tea.
    apply var0conv; cbn; [|tea].
    rewrite <- (@wk1_ren_on Γ A' A'); apply convty_wk; [tea|now symmetry].
  - rewrite <- (Hrw A B'); unshelve eapply WescapeConv.
    3:{ eexists (PolyRedPack.posTree (normRedΣ0 ΣA) _ _ _ _).
        intros ; eapply (PolyRed.posRed (normRedΣ0 ΣA)).
        exact Ho.
    }
    eexists (Htree _ _ _ _ _ _ _).
    intros ; eapply HB ; exact Hover'.
    Unshelve.
    1: now eapply wfLCon_le_id.
    1: tea.
    + apply wfc_cons; tea.
    + apply var0; cbn; [now bsimpl|tea].
  - rewrite <- (Hrw A B), <- (Hrw A B'); unshelve eapply WescapeEq.
    2:{ eexists (PolyRedPack.posTree (normRedΣ0 ΣA) _ _ _ _).
        intros ; eapply (PolyRed.posRed (normRedΣ0 ΣA)).
        exact Ho.
    }
    eexists (Htree _ _ _ _ _ _ _).
    intros ; eapply HB ; exact Hover'.
    Unshelve.
    1: now eapply wfLCon_le_id.
    1: tea.
    + apply wfc_cons; tea.
    + apply var0; cbn; [now bsimpl|tea].
  - rewrite <- (Hrw A' B), <- (Hrw A' B'); unshelve eapply WescapeEq.
    2:{ eexists (PolyRedPack.posTree (normRedΣ0 ΣA) _ _ _ _).
        intros ; eapply (PolyRed.posRed (normRedΣ0 ΣA)).
        exact Ho.
    }
    eexists (Htree _ _ _ _ _ _ _).
    intros ; eapply HB ; exact Hover'.
    Unshelve.
    1: now eapply wfLCon_le_id.
    1: tea.
    + apply var0conv; cbn; tea.
      rewrite <- (@wk1_ren_on Γ A' A'); apply convty_wk; [tea|now symmetry].
  - rewrite <- (wk_id_ren_on Γ A), <- (wk_id_ren_on Γ a).
    unshelve eapply escapeTerm, Ha ; [ | now gen_typing].
    now eapply wfLCon_le_id.
  - rewrite <- Hrw'.
    unshelve eapply Wescape, RB; tea.
    + now eapply wfLCon_le_id.
    + rewrite <- (wk_id_ren_on Γ a); now unshelve apply Ha.
  - rewrite <- Hrw'; unshelve eapply WescapeConv.
    3:{ eexists (PolyRedPack.posTree (normRedΣ0 ΣA) _ _ _ _).
        intros ; eapply (PolyRed.posRed (normRedΣ0 ΣA)).
        exact Ho.
    }
    eexists (Htree _ _ _ _ _ _ _).
    intros ; eapply HB ; exact Hover'.
    Unshelve.
    1: now eapply wfLCon_le_id.
    1: tea.
    rewrite <- (wk_id_ren_on Γ a); now unshelve apply Ha.
  - rewrite <- !Hrw'; unshelve eapply WescapeEq.
    2:{ eexists (PolyRedPack.posTree (normRedΣ0 ΣA) _ _ _ _).
        intros ; eapply (PolyRed.posRed (normRedΣ0 ΣA)).
        exact Ho.
    }
    eexists (Htree _ _ _ _ _ _ _).
    intros ; eapply HB ; exact Hover'.
    Unshelve.
    1: now eapply wfLCon_le_id.
    1: tea.
    rewrite <- (wk_id_ren_on Γ a); now unshelve apply Ha.
  - rewrite <- Hrw', <- (wk_id_ren_on Γ b), <- (wk_id_ren_on Γ a).
    unshelve eapply WescapeTerm.
    2:{ eexists (PolyRedPack.posTree (normRedΣ0 ΣA) _ _ _ _).
        intros ; eapply (PolyRed.posRed (normRedΣ0 ΣA)).
        exact Ho.
    }
    eexists (Hbtree _ _ _ _ _).
    intros ; eapply Hb ; exact Hover'.
    Unshelve.
    1: now eapply wfLCon_le_id.
    1: tea.
  Qed.

  Lemma isLRPair_isPair {wl Γ A B l p} (ΣA : [Γ ||-Σ<l> tSig A B]< wl >) (Rp : [Γ ||-Σ p : _ | normRedΣ0 ΣA]< wl >) :
    isPair (SigRedTm.nf Rp).
  Proof.
  destruct Rp; simpl; intros.
  destruct ispair; constructor; tea.
  now eapply convneu_whne.
  Qed.

  Lemma sigEtaRed {wl Γ A B l p p'}
    (RΣ0 : [Γ ||-Σ<l> tSig A B]< wl >)
    (RΣ := LRSig' (normRedΣ0 RΣ0))
    (RA : [Γ ||-<l> A]< wl >)
    (RBfst : W[Γ ||-<l> B[(tFst p)..]]< wl >)
    (RBfst' : W[Γ ||-<l> B[(tFst p')..]]< wl >)
    (Rp : [Γ ||-<l> p : _ | RΣ]< wl >)
    (Rp' : [Γ ||-<l> p' : _ |  RΣ]< wl >)
    (RBfstEq0 : W[Γ ||-<l> B[(tFst p)..] ≅ B[(tFst p')..] | RBfst]< wl >)
    (RBfstnf : W[Γ ||-<l> B[(tFst Rp.(SigRedTm.nf))..]]< wl >)
    (RBfstEq : W[Γ ||-<l> B[(tFst p)..] ≅ B[(tFst Rp.(SigRedTm.nf))..] | RBfst]< wl >)
    (RBfstEq' : W[Γ ||-<l> B[(tFst p')..] ≅ B[(tFst Rp'.(SigRedTm.nf))..] | RBfst']< wl >)
    (Rfstpp' : [Γ ||-<l> tFst p ≅ tFst p' : _ | RA]< wl >)
    (Rsndpp' : W[Γ ||-<l> tSnd p ≅ tSnd p' : _ | RBfst]< wl >) :
    [Γ ||-<l> p ≅ p' : _ | RΣ]< wl >.
  Proof.
    destruct (sndRed RΣ0 RA Rp RBfst RBfstEq).
    destruct (sndRed RΣ0 RA Rp' RBfst' RBfstEq').
    eexists Rp Rp' _.
    - destruct (polyRedId (normRedΣ0 RΣ0)) as [_ RB].
      assert ([Γ ||-<l> SigRedTm.nf Rp : _ | RΣ]< wl > × [Γ ||-<l> p ≅ SigRedTm.nf Rp : _ | RΣ]< wl >) as [Rnf Rpnf].
      1: eapply (redTmFwdConv Rp (SigRedTm.red Rp)), isPair_whnf, isLRPair_isPair.
      assert ([Γ ||-<l> SigRedTm.nf Rp' : _ | RΣ]< wl >× [Γ ||-<l> p' ≅ SigRedTm.nf Rp' : _ | RΣ]< wl >) as [Rnf' Rpnf'].
      1: eapply (redTmFwdConv Rp' (SigRedTm.red Rp')), isPair_whnf, isLRPair_isPair.
      destruct (fstRed RΣ0 RA Rp) as [[Rfstp Rfsteq] Rfstnf].
      destruct (fstRed RΣ0 RA Rp') as [[Rfstp' Rfsteq'] Rfstnf'].
      destruct (sndRed RΣ0 RA Rp RBfst RBfstEq).
      destruct (sndRed RΣ0 RA Rp' RBfst' RBfstEq').
      escape ; Wescape.
      assert [|- Γ]< wl > by now eapply wfc_wft.
      eapply convtm_eta_sig; tea.
      1, 2: now eapply isLRPair_isWfPair.
      + transitivity (tFst p).
        1: now symmetry.
        transitivity (tFst p'); tea.
      + eapply convtm_conv; tea.
        transitivity (tSnd p).
        1: now symmetry.
        transitivity (tSnd p'); tea.
        eapply convtm_conv; tea.
        now symmetry.
    - intros; do 2 rewrite wk_fst. 
      irrelevanceRefl. eapply wkTermEq, (TmEq_Ltrans f).
      destruct (fstRed RΣ0 RA Rp) as [[Rfstp Rfsteq] Rfstnf].
      destruct (fstRed RΣ0 RA Rp') as [[Rfstp' Rfsteq'] Rfstnf'].
      eapply transEqTerm; tea.
      eapply transEqTerm; tea.
      now eapply LRTmEqSym.
      Unshelve. 2: tea.
      intros ; eapply DTree_fusion ; [ | eapply DTree_fusion] ; shelve.
    - intros. do 2 rewrite wk_snd.
      eapply LRTmEqRedConv.
      2:{
        eapply wkTermEq. 
        unshelve eapply (WRedTmEq) ; cycle 3.
        eapply (WTmEq_Ltrans f).
        eapply WtransEqTerm; tea.
        eapply WLRTmEqRedConv; tea.
        eapply WtransEqTerm; tea.
        now eapply WLRTmEqSym.
        Unshelve.
        1: eapply over_tree_fusion_l ; exact Ho'.
        1: eapply over_tree_fusion_l, over_tree_fusion_r ; exact Ho'.
        1: shelve.
        eapply wfc_Ltrans ; [now eapply over_tree_le | assumption].
      }
      rewrite wk_fst, <- subst_ren_subst_mixed.
      eapply wkEq. 
      unshelve eapply WRedEq.
      cbn ; Wirrelevance0 ; [reflexivity | ].
      eapply (WEq_Ltrans f).
      eapply WLRTyEqSym.
      eapply WtransEq; tea.
      now eapply WLRTyEqSym.
      Unshelve. all: tea.
      1: now do 2 eapply over_tree_fusion_r ; exact Ho'.
  Qed.

  Lemma subst_sig {A B σ} : (tSig A B)[σ] = (tSig A[σ] B[up_term_term σ]).
  Proof. reflexivity. Qed.

  Lemma subst_pair {A B a b σ} : (tPair A B a b)[σ] = (tPair A[σ] B[up_term_term σ] a[σ] b[σ]).
  Proof. reflexivity. Qed.
  
  Lemma subst_fst {p σ} : (tFst p)[σ] = tFst p[σ].
  Proof. reflexivity. Qed.
  
  Lemma subst_snd {p σ} : (tSnd p)[σ] = tSnd p[σ].
  Proof. reflexivity. Qed.
  
  Lemma pairFstRedEq {wl Γ A A' B B' a a' b b' l}
    (RA : [Γ ||-<l> A]< wl >)
    (RA' : [Γ ||-<l> A']< wl >)
    (RAA' :[Γ ||-<l> A ≅ A' | RA]< wl >)
    (RB : W[Γ ,, A ||-<l> B]< wl >)
    (RB' : W[Γ ,, A' ||-<l> B']< wl >)
    (RBa : W[Γ ||-<l> B[a..]]< wl >)
    (RBa' : W[Γ ||-<l> B'[a'..]]< wl >)
    (Ra : [Γ ||-<l> a : A | RA]< wl >)
    (Ra' : [Γ ||-<l> a' : A' | RA']< wl >)
    (Raa' : [Γ ||-<l> a ≅ a' : A | RA]< wl >)
    (Rb : W[Γ ||-<l> b : _ | RBa ]< wl >)
    (Rb' : W[Γ ||-<l> b' : _ | RBa' ]< wl >) :
    [Γ ||-<l> tFst (tPair A B a b) ≅ tFst (tPair A' B' a' b') : _ | RA]< wl >.
  Proof.
    destruct (pairFstRed RA RB RBa Ra Rb).
    destruct (pairFstRed RA' RB' RBa' Ra' Rb').
    eapply transEqTerm; tea.
    eapply transEqTerm; tea.
    eapply LRTmEqRedConv.
    + now eapply LRTyEqSym.
    + now eapply LRTmEqSym.
  Qed.

  Lemma WpairFstRedEq {wl Γ A A' B B' a a' b b' l}
    (RA : W[Γ ||-<l> A]< wl >)
    (RA' : W[Γ ||-<l> A']< wl >)
    (RAA' : W[Γ ||-<l> A ≅ A' | RA]< wl >)
    (RB : W[Γ ,, A ||-<l> B]< wl >)
    (RB' : W[Γ ,, A' ||-<l> B']< wl >)
    (RBa : W[Γ ||-<l> B[a..]]< wl >)
    (RBa' : W[Γ ||-<l> B'[a'..]]< wl >)
    (Ra : W[Γ ||-<l> a : A | RA]< wl >)
    (Ra' : W[Γ ||-<l> a' : A' | RA']< wl >)
    (Raa' : W[Γ ||-<l> a ≅ a' : A | RA]< wl >)
    (Rb : W[Γ ||-<l> b : _ | RBa ]< wl >)
    (Rb' : W[Γ ||-<l> b' : _ | RBa' ]< wl >) :
    W[Γ ||-<l> tFst (tPair A B a b) ≅ tFst (tPair A' B' a' b') : _ | RA]< wl >.
  Proof.
    unshelve econstructor.
    - do 2 eapply DTree_fusion ; [.. | eapply DTree_fusion ] ; shelve.
    - intros wl' Ho Ho' ; pose (f':= over_tree_le Ho).
      eapply pairFstRedEq ; tea.
      2,3: now eapply WLtrans.
      5,6: now eapply WTm_Ltrans.
      + eapply RAA', over_tree_fusion_l, over_tree_fusion_l ;exact Ho'.
      + eapply Ra, over_tree_fusion_r, over_tree_fusion_l ;exact Ho'.
      + eapply Ra', over_tree_fusion_l, over_tree_fusion_r ;exact Ho'.
      + eapply Raa', over_tree_fusion_l, over_tree_fusion_r, over_tree_fusion_r ;exact Ho'.
        Unshelve.
        2,3: tea.
        2: now do 3 (eapply over_tree_fusion_r) ; exact Ho'. 
  Qed.
  
  Lemma pairSndRedEq {wl Γ A A' B B' a a' b b' l}
    (RA : W[Γ ||-<l> A]< wl >)
    (RA' : W[Γ ||-<l> A']< wl >)
    (RAA' :W[Γ ||-<l> A ≅ A' | RA]< wl >)
    (RB : W[Γ ,, A ||-<l> B]< wl >)
    (RB' : W[Γ ,, A' ||-<l> B']< wl >)
    (RBa : W[Γ ||-<l> B[a..]]< wl >)
    (RBa' : W[Γ ||-<l> B'[a'..]]< wl >)
    (RBaBa' : W[Γ ||-<l> B[a..] ≅ B'[a'..] | RBa ]< wl >)
    (RBfst : W[Γ ||-<l> B[(tFst (tPair A B a b))..] ]< wl >)
    (RBconv : W[Γ ||-<l> B[a..] ≅ B[(tFst (tPair A B a b))..] | RBa ]< wl >)
    (RBfst' : W[Γ ||-<l> B'[(tFst (tPair A' B' a' b'))..] ]< wl >)
    (RBconv' : W[Γ ||-<l> B'[a'..] ≅ B'[(tFst (tPair A' B' a' b'))..] | RBa' ]< wl >)
    (Ra : W[Γ ||-<l> a : A | RA]< wl >)
    (Ra' : W[Γ ||-<l> a' : A' | RA']< wl >)
    (Rb : W[Γ ||-<l> b : _ | RBa ]< wl >)
    (Rb' : W[Γ ||-<l> b' : _ | RBa' ]< wl >) 
    (Rbb' : W[Γ ||-<l> b ≅ b' : _ | RBa]< wl >) :
    W[Γ ||-<l> tSnd (tPair A B a b) ≅ tSnd (tPair A' B' a' b') : _ | RBfst]< wl >.
  Proof.
    destruct (WpairSndRed RA RB RBa RBfst RBconv Ra Rb).
    destruct (WpairSndRed RA' RB' RBa' RBfst' RBconv' Ra' Rb').
    eapply WtransEqTerm; tea.
    eapply WLRTmEqRedConv; tea.
    eapply WtransEqTerm; tea.
    eapply WLRTmEqRedConv; cycle 1.
    + now eapply WLRTmEqSym.
    + eapply WLRTyEqSym; eapply WtransEq; cycle 1; tea.
  Qed.


  Lemma pairFstValid {wl Γ A B a b l}
    (VΓ : [||-v Γ]< wl >)
    (VA : [ Γ ||-v<l> A | VΓ ]< wl >)
    (VB : [ Γ ,, A ||-v<l> B | validSnoc' VΓ VA]< wl >)
    (VΣ := SigValid VΓ VA VB)
    (Va : [Γ ||-v<l> a : A | VΓ | VA]< wl >)
    (VBa := substS VB Va)
    (Vb : [Γ ||-v<l> b : B[a..] | VΓ | VBa]< wl >) :
    [Γ ||-v<l> tFst (tPair A B a b) : _ | VΓ | VA]< wl > ×
    [Γ ||-v<l> tFst (tPair A B a b) ≅ a : _ | VΓ | VA]< wl >.
  Proof.
    assert (h : forall {Δ wl' σ f} (wfΔ : [|-  Δ]< wl' >) (Vσ : [VΓ | Δ ||-v σ : Γ | wfΔ | f]< wl >),
      W[ Δ ||-< l > (tFst (tPair A B a b))[σ] : A[σ] | validTy VA f wfΔ Vσ]< wl' > ×
      W[ Δ ||-< l > (tFst (tPair A B a b))[σ] ≅ a[σ] : A[σ] | validTy VA f wfΔ Vσ]< wl' >).
    1:{
      intros ???? wfΔ Vσ; instValid Vσ.
      unshelve eapply WpairFstRed; tea; fold subst_term.
      + now rewrite <- singleSubstComm'.
      + unshelve eapply (snd (WpolyRedId _)).
        now eapply substPolyRed ; tea.
      + Wirrelevance0; tea; now rewrite singleSubstComm'.
    }
    split; unshelve econstructor.
    - apply h.
    - intros ????? wfΔ Vσ Vσ' Vσσ'.
      instAllValid Vσ Vσ' Vσσ'.
      unshelve eapply WpairFstRedEq; tea; fold subst_term.
      1,2: now rewrite <- singleSubstComm'.
      all: try (Wirrelevance0; tea; now rewrite singleSubstComm').
      + unshelve eapply (snd (WpolyRedId _)).
        now eapply substPolyRed ; tea.
      + unshelve eapply (snd (WpolyRedId _)).
        now eapply substPolyRed ; tea.
    - apply h.
  Qed.
  
  Lemma pairSndValid {wl Γ A B a b l}
    (VΓ : [||-v Γ]< wl >)
    (VA : [ Γ ||-v<l> A | VΓ ]< wl >)
    (VB : [ Γ ,, A ||-v<l> B | validSnoc' VΓ VA]< wl >)
    (VΣ := SigValid VΓ VA VB)
    (Va : [Γ ||-v<l> a : A | VΓ | VA]< wl >)
    (VBa := substS VB Va)
    (Vb : [Γ ||-v<l> b : B[a..] | VΓ | VBa]< wl >)
    (Vfstall := pairFstValid VΓ VA VB Va Vb)
    (VBfst := substS VB (fst Vfstall)) :
    [Γ ||-v<l> tSnd (tPair A B a b) : _ | VΓ | VBfst]< wl > ×
    [Γ ||-v<l> tSnd (tPair A B a b) ≅ b : _ | VΓ | VBfst]< wl >.
  Proof.
    pose proof (VBfsteq := substSEq (reflValidTy _ VA) VB (reflValidTy _ VB) Va (fst Vfstall) (symValidTmEq (snd (Vfstall)))).
    cbn in VBfsteq.
    assert (h : forall {Δ wl' σ f} (wfΔ : [|-  Δ]< wl' >) (Vσ : [VΓ | Δ ||-v σ : Γ | wfΔ | f]< wl >),
      W[ Δ ||-< l > (tSnd (tPair A B a b))[σ] : _  | validTy VBfst f wfΔ Vσ ]< wl' > ×
      W[ Δ ||-< l > (tSnd (tPair A B a b))[σ] ≅ b[σ] : _ | validTy VBfst f wfΔ Vσ ]< wl' >).
    1:{
      intros ???? wfΔ Vσ ; instValid Vσ.
      Wirrelevance0. 1: now rewrite singleSubstComm'.
      unshelve eapply WpairSndRed; tea; fold subst_term.
      + now rewrite <- singleSubstComm'.
      + unshelve eapply (snd (WpolyRedId _)).
        now eapply substPolyRed ; tea.
      + rewrite <- subst_pair, <- subst_fst; Wirrelevance0;
        rewrite <- singleSubstComm'; tea; reflexivity.
        Unshelve. now rewrite <- singleSubstComm'.
      + Wirrelevance0; tea; now rewrite <- singleSubstComm'.
    }
    split; unshelve econstructor.
    - apply h.
    - intros ????? wfΔ Vσ Vσ' Vσσ' ; instAllValid Vσ Vσ' Vσσ'.
      Wirrelevance0. 1: now rewrite singleSubstComm'.
      unshelve eapply pairSndRedEq; tea; fold subst_term.
      1,2: now rewrite <- singleSubstComm'.
      all: try (Wirrelevance0; tea; now rewrite <- singleSubstComm').
      1,2: unshelve eapply (snd (WpolyRedId _)).
      1,2: now eapply substPolyRed ; tea.
      all: rewrite <- subst_pair, <- subst_fst.
      2: rewrite <- singleSubstComm'; tea.
      all: Wirrelevance0; rewrite <- singleSubstComm'; try reflexivity; tea.
      Unshelve. now rewrite <- singleSubstComm'.
    - apply h.
  Qed.


  Lemma pairValid {wl Γ A B a b l}
    (VΓ : [||-v Γ]< wl >)
    (VA : [ Γ ||-v<l> A | VΓ ]< wl >)
    (VB : [ Γ ,, A ||-v<l> B | validSnoc' VΓ VA]< wl >)
    (VΣ := SigValid VΓ VA VB)
    (Va : [Γ ||-v<l> a : A | VΓ | VA]< wl >)
    (VBa := substS VB Va)
    (Vb : [Γ ||-v<l> b : B[a..] | VΓ | VBa]< wl >) :
    [Γ ||-v<l> tPair A B a b : _ | VΓ | VΣ]< wl >.
  Proof.
    destruct (pairFstValid VΓ VA VB Va Vb) as [Vfst Vfsteq].
    destruct (pairSndValid VΓ VA VB Va Vb) as [Vsnd Vsndeq].
    pose proof (VBfst := substS VB Vfst).
    pose proof (VBfsteq := substSEq (reflValidTy _ VA) VB (reflValidTy _ VB) Va Vfst (symValidTmEq Vfsteq)).
    cbn in VBfsteq.
    assert (pairSubstRed : forall (Δ : context) wl' (σ : nat -> term) f (wfΔ : [ |-[ ta ] Δ]< wl' >)
      (Vσ : [VΓ | Δ ||-v σ : Γ | wfΔ | f]< wl >),
      W[Δ ||-<l> (tPair A B a b)[σ] : (tSig A B)[σ] | validTy VΣ f wfΔ Vσ]< wl' >).
    1:{
      intros ???? wfΔ Vσ.
      instValid Vσ; instValidExt Vσ (reflSubst _ _ _ Vσ).
      pose (Vaσ := consSubstSvalid Vσ Va); instValid Vaσ.
      rewrite <- up_subst_single in RVB.
      assert (RVb' : W[Δ ||-< l > b[σ] : B[up_term_term σ][(a[σ])..] | RVB]< wl' >)
        by (Wirrelevance0; tea; apply  singleSubstComm').
      unshelve epose (p := WpairFstRed RVA _ RVB RVa RVb').
      1: unshelve eapply (snd (WpolyRedId _)).
      1: now eapply substPolyRed ; tea.
      destruct p as [Rfst Rfsteq%WLRTmEqSym].
      pose proof (Vfstσ := consSubstS _ _ Vσ VA Rfst).
      epose proof (Veqσ := consSubstSEq' _ _ Vσ (reflSubst _ _ _ Vσ) VA RVa Rfsteq).
      instValid Vfstσ; instValidExt Vfstσ Veqσ.
      unshelve epose (WpairRed RVΣ RVA RVB _ _ RVa RVb'); fold subst_term in *.
      + Wirrelevance0 ; tea ; now rewrite up_subst_single.
      + now rewrite up_subst_single.
      + Wirrelevance0 ; tea ; now bsimpl.
    }
    unshelve econstructor.
    1: intros; now eapply pairSubstRed.
    intros ????? wfΔ Vσ Vσ' Vσσ'.
    instAllValid Vσ Vσ' Vσσ'.
    set (p := _[_]); set (p' := _[_]).
    pose proof (Rp0 := pairSubstRed _ _ _ f wfΔ Vσ).
    pose proof (Rp0' := pairSubstRed _ _ _ f wfΔ Vσ').
    unshelve eapply TreeTmEqSplit.
    1: do 4 eapply DTree_fusion ; shelve.
    intros wl'' Ho HA.
    pose (f':= over_tree_le Ho).
    pose (HRVΣ := WRed _ RVΣ _ (over_tree_fusion_l (over_tree_fusion_l (over_tree_fusion_l (over_tree_fusion_l Ho))))).
    pose (HRVΣ' := WRed _ RVΣ0 _ (over_tree_fusion_r (over_tree_fusion_l (over_tree_fusion_l (over_tree_fusion_l Ho))))).
    pose (RΣ := normRedΣ HRVΣ); pose (RΣ' := normRedΣ HRVΣ'); fold subst_term in *.
    assert (Rp : [Δ ||-<l> p : _ | RΣ]< wl'' >).
    { irrelevance0 ; [ reflexivity | unshelve eapply Rp0].
      + now eapply over_tree_fusion_l, over_tree_fusion_r, over_tree_fusion_l, over_tree_fusion_l ; exact Ho.
      + now eapply over_tree_fusion_l, over_tree_fusion_r, over_tree_fusion_r, over_tree_fusion_l ; exact Ho.
    }
    assert (Rp' : [Δ ||-<l> p' : _ | RΣ]< wl'' >).
    { eapply LRTmRedConv; [|unshelve eapply (pairSubstRed _ _ _ f wfΔ Vσ')].
      1: eapply LRTyEqSym ; unshelve eapply REVΣ.
      + now eapply over_tree_fusion_l, over_tree_fusion_r, over_tree_fusion_l, over_tree_fusion_l ; exact Ho.
      + now eapply over_tree_fusion_l, over_tree_fusion_l, over_tree_fusion_r, over_tree_fusion_l ; exact Ho.
      + now eapply over_tree_fusion_r, over_tree_fusion_l, over_tree_fusion_r, over_tree_fusion_l ; exact Ho.
      + now eapply over_tree_fusion_r, over_tree_fusion_r, over_tree_fusion_l, over_tree_fusion_l ; exact Ho.
    }
    pose (HRVA := WRed _ RVA _ (over_tree_fusion_r (over_tree_fusion_r (over_tree_fusion_r (over_tree_fusion_l Ho))))).
    Wirrelevance0.
    1: symmetry; apply subst_sig.
    destruct (fstRed (invLRΣ HRVΣ) HRVA Rp) as [[Rfstp Rfsteq] Rfstnf].
    destruct (fstRed (invLRΣ HRVΣ) HRVA Rp') as [[Rfstp' Rfsteq'] Rfstnf'].
    epose (Vfstpσ := consSubstS _ _ (subst_Ltrans f' _ Vσ) VA (TmLogtoW' Rfstp _)).
    epose (Vfstnfσ := consSubstS _ _ (subst_Ltrans f' _ Vσ) VA (TmLogtoW' Rfstnf _)).
    epose (Vfsteqσ := consSubstSEq' _ _ (subst_Ltrans f' _ Vσ) (reflSubst _ _ _ _) VA (TmLogtoW' Rfstp _) (TmEqLogtoW' Rfsteq _)).
    epose (Vfstpσ' := consSubstS _ _ (subst_Ltrans f' _ Vσ) VA (TmLogtoW' Rfstp' _)).
    epose (Vfstnfσ' := consSubstS _ _ (subst_Ltrans f' _ Vσ) VA (TmLogtoW' Rfstnf' _)).
    epose (Vfsteqσ' := consSubstSEq' _ _ (subst_Ltrans f' _ Vσ) (reflSubst _ _ _ _) VA (TmLogtoW' Rfstp' _) (TmEqLogtoW' Rfsteq' _)).
    pose (Vuσ := liftSubstS' VA Vσ).
    pose (Vuσ' := liftSubstS' VA Vσ').
    pose (Vurσ' := liftSubstSrealign' VA Vσσ' Vσ').
    Unshelve. 2-9: shelve.
    3: now eapply WLtrans.
    2-7: now eapply wfc_Ltrans.
    instValid Vuσ; instValid Vuσ'; instValid Vurσ'.
    assert(Rfstpp' : [Δ ||-< l > tFst p ≅ tFst p' : A[σ] | HRVA]< wl'' >). 
    1:{
      eapply pairFstRedEq; tea ; fold subst_term in *.
      1: irrelevanceRefl ; eapply REVA ; shelve.
      1: now eapply (WLtrans f'), RVB.
      1: now eapply (WLtrans f'), RVB0.
      1: irrelevanceRefl ; eapply RVa ; shelve.
      1: irrelevanceRefl ; eapply RVa0 ; shelve.
      1: irrelevanceRefl ; eapply REVa ; shelve.
      1,2: eapply (WTm_Ltrans f') ; Wirrelevance0 ; [ | eassumption].
      1,2: now rewrite singleSubstComm'.
      Unshelve. 1-8: shelve. all: fold subst_term.
      10,11: now rewrite <- singleSubstComm'.
      1: eapply RVA0.
      all: shelve.
    }
    unshelve epose proof (Vfstppσ := consSubstSEq' _ _ (subst_Ltrans f' _ Vσ) (reflSubst _ _ _ _) VA _ (TmEqLogtoW' Rfstpp' _)).
    1: now eapply wfc_Ltrans.
    1: now eapply (TmLogtoW' Rfstp _).
    instAllValid Vfstpσ Vfstnfσ Vfsteqσ.
    instAllValid Vfstpσ' Vfstnfσ' Vfsteqσ'.
    instValidExt Vfstpσ' Vfstppσ.
    rewrite <- up_subst_single in RVB2.
    rewrite <- up_subst_single in RVB3, REVB.
    rewrite <- up_subst_single in RVB4.
    rewrite <- up_subst_single in RVB5, REVB0.
    eapply TmEqLogtoW'.
    unshelve eapply (sigEtaRed _ HRVA RVB2 RVB4 Rp Rp' _ _ _ _ Rfstpp').
    + Wirrelevance0; rewrite up_subst_single ;tea ; reflexivity.
    + eassumption.
    + Wirrelevance0 ; [ | eassumption] ; now rewrite up_subst_single. 
    + Wirrelevance0 ; [ | eassumption] ; now rewrite up_subst_single. 
    + unshelve eapply pairSndRedEq; tea; fold subst_term.
      1,2,6,7: now eapply WLtrans.
      1,2: rewrite <- singleSubstComm' ; now eapply WLtrans.
      1: now eapply WEq_Ltrans.
      1: Wirrelevance0 ; [ | eapply WEq_Ltrans] ; now rewrite <- singleSubstComm'.
      1:{ Wirrelevance0.
          2: rewrite <- subst_pair, <- subst_fst, <- singleSubstComm'.
          2: now eapply (WEq_Ltrans' f'), RVBfsteq.
          now bsimpl.
      }
      3,4: now eapply WTm_Ltrans'.
      3,4: Wirrelevance0 ; [ | now eapply WTm_Ltrans] ; now rewrite <- singleSubstComm'.
      3: Wirrelevance0 ; [ | now eapply WTmEq_Ltrans] ; now rewrite <- singleSubstComm'.
      all: rewrite <- subst_pair, <- subst_fst.
      1: rewrite <- singleSubstComm' ; now eapply WLtrans.
      1: Wirrelevance0 ; [ | eapply WEq_Ltrans] ; now rewrite <- singleSubstComm'.
      Unshelve. 1-8: shelve.
      all: try eassumption.
      2,4,8: now eapply over_tree_fusion_l, over_tree_fusion_l, over_tree_fusion_l, over_tree_fusion_r ; exact Ho.
      * now eapply over_tree_fusion_r, over_tree_fusion_l, over_tree_fusion_l, over_tree_fusion_r ; exact Ho.
      * now eapply over_tree_fusion_l, over_tree_fusion_r, over_tree_fusion_l, over_tree_fusion_r ; exact Ho.
      * now eapply over_tree_fusion_r, over_tree_fusion_r, over_tree_fusion_l, over_tree_fusion_r ; exact Ho.
      * now eapply over_tree_fusion_l, over_tree_fusion_l, over_tree_fusion_r, over_tree_fusion_r ; exact Ho.
      * now eapply over_tree_fusion_r, over_tree_fusion_l, over_tree_fusion_r, over_tree_fusion_r ; exact Ho.
      * now eapply over_tree_fusion_l, over_tree_fusion_r, over_tree_fusion_r, over_tree_fusion_r ; exact Ho.
      * now eapply WLtrans.
        Unshelve. now constructor.
Qed.        

  Lemma sigEtaValid {wl Γ A B p p' l}
    (VΓ : [||-v Γ]< wl >)
    (VA : [ Γ ||-v<l> A | VΓ ]< wl >)
    (VB : [ Γ ,, A ||-v<l> B | validSnoc' VΓ VA]< wl >)
    (VΣ := SigValid VΓ VA VB)
    (Vp : [Γ ||-v<l> p : _ | VΓ | VΣ]< wl >)
    (Vp' : [Γ ||-v<l> p' : _ | VΓ | VΣ]< wl >)
    (Vfstpp' : [Γ ||-v<l> tFst p ≅ tFst p' : _ | VΓ | VA]< wl >)
    (Vfst := fstValid VΓ VA VB Vp)
    (VBfst := substS VB Vfst)
    (Vsndpp' : [Γ ||-v<l> tSnd p ≅ tSnd p' : _| VΓ | VBfst]< wl >) :
    [Γ ||-v<l> p ≅ p' : _ | VΓ | VΣ]< wl >.
  Proof.
    pose proof (Vfst' := fstValid VΓ VA VB Vp').
    pose proof (VBfst' := substS VB Vfst').
    pose proof (VBfsteq := substSEq (reflValidTy _ VA) VB (reflValidTy _ VB) Vfst Vfst' Vfstpp').
    cbn in VBfsteq.
    constructor; intros ???? wfΔ Vσ; instValid Vσ.
    unshelve eapply TreeTmEqSplit.
    1: do 3 eapply DTree_fusion ; shelve.
    intros wl'' Ho HA.
    pose (f':= over_tree_le Ho).
    pose (HRVΣ := WRed _ RVΣ _ (over_tree_fusion_l (over_tree_fusion_l (over_tree_fusion_l Ho)))).
    pose (RΣ0 := invLRΣ HRVΣ).
    pose (RΣ := LRSig' (normRedΣ0 RΣ0)).
    fold subst_term in *.
    assert (Rp : [Δ ||-<l> p[σ] : _ | RΣ]< wl'' >).
    { irrelevance0 ; [ reflexivity | unshelve eapply RVp].
      + now eapply over_tree_fusion_l, over_tree_fusion_r, over_tree_fusion_l; exact Ho.
      + now eapply over_tree_fusion_l, over_tree_fusion_r, over_tree_fusion_r ; exact Ho.
    }
    assert (Rp' : [Δ ||-<l> p'[σ] : _ | RΣ]< wl'' >).
    { irrelevance0 ; [ reflexivity | unshelve eapply RVp'].
      + now eapply over_tree_fusion_l, over_tree_fusion_r, over_tree_fusion_l ; exact Ho.
      + now eapply over_tree_fusion_l, over_tree_fusion_l, over_tree_fusion_r ; exact Ho.
    }
    pose (HRVA := WRed _ RVA _ (over_tree_fusion_r (over_tree_fusion_r (over_tree_fusion_r Ho)))).
    destruct (fstRed RΣ0 HRVA Rp) as [[Rfstp Rfsteq] Rfstnf].
    destruct (fstRed RΣ0 HRVA Rp') as [[Rfstp' Rfsteq'] Rfstnf'].
    epose (Vfstpσ := consSubstS _ _ (subst_Ltrans f' _ Vσ) VA (TmLogtoW' Rfstp _)).
    epose (Vfstnfσ := consSubstS _ _ (subst_Ltrans f' _ Vσ) VA (TmLogtoW' Rfstnf _)).
    epose (Vfsteqσ := consSubstSEq' _ _ (subst_Ltrans f' _ Vσ) (reflSubst _ _ _ _) VA (TmLogtoW' Rfstp _) (TmEqLogtoW' Rfsteq _)).
    epose (Vfstpσ' := consSubstS _ _ (subst_Ltrans f' _ Vσ) VA (TmLogtoW' Rfstp' _)).
    epose (Vfstnfσ' := consSubstS _ _ (subst_Ltrans f' _ Vσ) VA (TmLogtoW' Rfstnf' _)).
    epose (Vfsteqσ' := consSubstSEq' _ _ (subst_Ltrans f' _ Vσ) (reflSubst _ _ _ _) VA (TmLogtoW' Rfstp' _) (TmEqLogtoW' Rfsteq' _)).
    Unshelve.
    all: try now eapply wfc_Ltrans.
    2-4: shelve.
    instAllValid Vfstpσ Vfstnfσ Vfsteqσ.
    instAllValid Vfstpσ' Vfstnfσ' Vfsteqσ'.
    Wirrelevance0.
    1: now rewrite subst_sig.
    eapply TmEqLogtoW.
    unshelve eapply (sigEtaRed RΣ0 HRVA _ _ Rp Rp') ; tea.
    1,2: rewrite <- subst_fst,<- singleSubstComm'; tea.
    1,2: now eapply WLtrans.
    + cbn ; Wirrelevance0; rewrite <- subst_fst, <- singleSubstComm'; try reflexivity; tea.
      now unshelve eapply WEq_Ltrans ; cycle 3.
    + now rewrite up_subst_single. 
    + cbn ; Wirrelevance0; rewrite up_subst_single; try reflexivity; tea.
    + cbn ; Wirrelevance0; rewrite up_subst_single; try reflexivity; tea.
    + irrelevanceRefl ; eapply RVfstpp'.
      now eapply over_tree_fusion_r, over_tree_fusion_l, over_tree_fusion_r ; exact Ho.
    + cbn ; Wirrelevance0. 1: now rewrite <- subst_fst, <- singleSubstComm'.
      now unshelve eapply WTmEq_Ltrans ; cycle 3.
      Unshelve.
      3: now do 3 eapply over_tree_fusion_r ; exact Ho.
      all: now constructor.
  Qed.

End PairRed.



