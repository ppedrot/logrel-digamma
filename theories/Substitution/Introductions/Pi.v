From Coq Require Import ssrbool.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations LContexts Context NormalForms Weakening
  GenericTyping Monad LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Escape Reflexivity Neutral Weakening Split Irrelevance.
From LogRel.Substitution Require Import Irrelevance Properties.
From LogRel.Substitution.Introductions Require Import Universe Poly.

Set Universe Polymorphism.

(* Lemma eq_subst_1 F G Δ σ : G[up_term_term σ] = G[tRel 0 .: σ⟨ @wk1 Δ F[σ] ⟩].
Proof.
  now bsimpl.
Qed.

Lemma eq_subst_2 G a ρ σ : G[up_term_term σ][a .: ρ >> tRel] = G[a .: σ⟨ρ⟩].
Proof.
  bsimpl ; now substify.
Qed. *)

Section PolyRedPi.
  Context `{GenericTypingProperties}.

  Lemma LRPiPoly0 {wl Γ l A B} (PAB : PolyRed wl Γ l A B) : [Γ ||-Π<l> tProd A B]< wl >.
  Proof.
    econstructor; tea; pose proof (polyRedId PAB) as []; escape.
    + eapply redtywf_refl ; Wescape ; gen_typing.
    + unshelve eapply escapeEq; tea; eapply reflLRTyEq.
    + cbn ; Wescape ; eapply convty_prod; tea.
      * unshelve eapply escapeEq ; tea ; now eapply reflLRTyEq.
      * unshelve eapply WescapeEq ; tea ; now eapply WreflLRTyEq.
  Defined.

  Definition LRPiPoly {wl Γ l A B} (PAB : PolyRed wl Γ l A B) : [Γ ||-<l> tProd A B]< wl > := LRPi' (LRPiPoly0 PAB).

  Lemma LRPiPolyEq0 {wl Γ l A A' B B'} (PAB : PolyRed wl Γ l A B) (Peq : PolyRedEq PAB A' B') :
    [Γ |- A']< wl > -> [Γ ,, A' |- B']< wl > ->
    [Γ ||-Π tProd A B ≅ tProd A' B' | LRPiPoly0 PAB]< wl >.
  Proof.
    econstructor; cbn; tea.
    + eapply redtywf_refl; gen_typing.
    + pose proof (polyRedEqId PAB Peq) as []; now escape.
    + pose proof (polyRedEqId PAB Peq) as []; escape ; Wescape.
      eapply convty_prod; tea.
      eapply escape; now apply (polyRedId PAB).
  Qed.

  Lemma LRPiPolyEq {wl Γ l A A' B B'} (PAB : PolyRed wl Γ l A B) (Peq : PolyRedEq PAB A' B') :
    [Γ |- A']< wl > -> [Γ ,, A' |- B']< wl > ->
    [Γ ||-<l> tProd A B ≅ tProd A' B' | LRPiPoly PAB]< wl >.
  Proof.
    now eapply LRPiPolyEq0.
  Qed.

  Lemma LRPiPolyEq' {wl Γ l A A' B B'} (PAB : PolyRed wl Γ l A B) (Peq : PolyRedEq PAB A' B') (RAB : [Γ ||-<l> tProd A B]< wl >):
    [Γ |- A']< wl > -> [Γ ,, A' |- B']< wl > ->
    [Γ ||-<l> tProd A B ≅ tProd A' B' | RAB]< wl >.
  Proof.
    intros; irrelevanceRefl; now eapply LRPiPolyEq.
  Qed.
  
End PolyRedPi.


Section PiTyValidity.

  Context `{GenericTypingProperties}.
  Context {l wl Γ F G} (vΓ : [||-v Γ]< wl >)
    (vF : [Γ ||-v< l > F | vΓ ]< wl >)
    (vG : [Γ ,, F ||-v< l > G | validSnoc' vΓ vF]< wl >).

  Lemma PiRed {Δ σ wl'} f (tΔ : [ |-[ ta ] Δ]< wl' >)
    (vσ : [vΓ | Δ ||-v σ : _ | tΔ | f]< wl >)
    : W[ Δ ||-< l > (tProd F G)[σ] ]< wl' >.
  Proof.
    pose (p := substPolyRed vΓ vF vG _ vσ).
    exists (WPol _ _ _ _ _ p) ; intros wl'' Hover.
    pose proof (over_tree_le Hover).
    eapply LRPi'.

    destruct (WpolyRedId p);
      destruct (WpolyRedEqId p (substPolyRedEq vΓ vF vG _ vσ vσ (reflSubst _ _ _ vσ))); Wescape.
    cbn ; econstructor; tea.
    - eapply redtywf_refl, wft_Ltrans ; [eassumption | gen_typing].
    - eapply convty_Ltrans ; [eassumption | gen_typing].
    - eapply convty_Ltrans ; [eassumption | gen_typing].
    - now eapply p.
  Defined.

  Lemma PiEqRed1 {Δ σ σ' wl' f} (tΔ : [ |-[ ta ] Δ]< wl' >)
    (vσ : [vΓ | Δ ||-v σ : _ | tΔ | f]< wl >)
    (vσ' : [vΓ | Δ ||-v σ' : _ | tΔ | f]< wl >)
    (vσσ' : [vΓ | Δ ||-v σ ≅ σ' : _ | tΔ | vσ | f]< wl >)
    : W[ Δ ||-< l > (tProd F G)[σ] ≅ (tProd F G)[σ'] | PiRed f tΔ vσ ]< wl' >.
  Proof.
    unfold PiRed ; cbn.
    set (p := substPolyRed vΓ vF vG _ vσ).
    set (p' := substPolyRed vΓ vF vG _ vσ').
    destruct (WpolyRedEqId p (substPolyRedEq vΓ vF vG tΔ vσ vσ (reflSubst vΓ f tΔ vσ))) as [Q1 Q2] ; cbn.
    set (peq := substPolyRedEq vΓ vF vG _ vσ vσ' vσσ').
    destruct (WpolyRedId p); destruct (WpolyRedId p'); destruct (WpolyRedEqId p peq).
    cbn.
    unfold PiRed.
    exists (WPolEq _ _ _ peq).
    cbn.
    intros wl'' Hover Hover'.
    Wescape; econstructor ; cbn ; tea.
    - eapply redtywf_refl, wft_Ltrans ; [ now eapply over_tree_le | gen_typing].
    - eapply convty_Ltrans ; [ now eapply over_tree_le | gen_typing].
    - eapply convty_Ltrans ; [ now eapply over_tree_le | gen_typing].
    - eapply peq.
      assumption.
  Defined.

  Lemma PiValid : [Γ ||-v< l > tProd F G | vΓ]< wl >.
  Proof.
    unshelve econstructor.
    - intros Δ wl' σ. eapply PiRed.
    - intros Δ wl' σ σ' f. eapply PiEqRed1.
  Defined.

End PiTyValidity.

Section PiTyDomValidity.

  Context `{GenericTypingProperties}.
  Context {l wl Γ F G} (vΓ : [||-v Γ]< wl >)
    (vΠFG : [Γ ||-v< l > tProd F G | vΓ ]< wl >).

  Lemma PiValidDom : [Γ ||-v< l > F | vΓ]< wl >.
  Proof.
  unshelve econstructor.
  - intros Δ wl' σ f vΔ vσ ; instValid vσ.
    exists (WT _ (validTy vΠFG f vΔ vσ)).
    intros wl'' Hover.
    pose (Help := WRed _ (validTy vΠFG f vΔ vσ) wl'' Hover).
    cbn in RvΠFG; apply Induction.invLRΠ in Help ; fold subst_term in Help.
    destruct Help as [dom ? red ? ? ? [? ? Hdom]].
    assert (Hrw : F[σ] = dom); [|subst dom].
    { eapply redtywf_whnf in red as [=]; [tea|constructor]. }
    rewrite <- (wk_id_ren_on Δ F[σ]).
    eapply Hdom ; [ now eapply wfLCon_le_id | eapply wfc_Ltrans ; eauto].
    now eapply over_tree_le.
  - intros Δ wl' σ σ' f vΔ vσ vσ' vσσ'.
    cbn; refold.
    assert (vΠ := validTyExt vΠFG _ _ vσ vσ' vσσ').
    exists (WTEq _ vΠ).
    cbn ; refold ; intros wl'' Hover Hover'.
    pose (Help := WRed _ (validTy vΠFG f vΔ vσ) wl'' Hover).
    apply Induction.invLRΠ in Help ; fold subst_term in Help.
    pose (Help2 := WRedEq _ vΠ wl'' Hover Hover').
    eapply LRTyEqIrrelevant' with (lrA' := LRPi' Help) in Help2 ; [|reflexivity].
    destruct Help as [dom ? red ? ? ? []].
    destruct Help2 as [dom' ? red' ? ? [Heq]]; simpl in *.
    specialize (Heq Δ wk_id _ (idε _) (wfc_Ltrans (over_tree_le Hover) vΔ)).
    assert (Hrw : F[σ] = dom).
    { eapply redtywf_whnf in red as [=]; [tea|constructor]. }
    assert (Hrw' : F[σ'] = dom').
    { eapply redtywf_whnf in red' as [=]; [tea|constructor]. }
    rewrite wk_id_ren_on, <- Hrw' in Heq.
    eapply Transitivity.transEq; [|eapply Heq].
    rewrite <- (wk_id_ren_on Δ dom) in Hrw; rewrite <- Hrw.
    now eapply reflLRTyEq.
  Qed.

  Lemma PiValidCod : [Γ,, F ||-v< l > G | validSnoc' vΓ PiValidDom]< wl >.
  Proof.
  unshelve econstructor.
  - intros Δ wl' σ f vΔ [vσ v0].
    instValid vσ; cbn in *.
    unshelve eapply TreeSplit.
    + eapply DTree_fusion ; [eapply DTree_fusion | exact (WTTm _ v0)].
      * exact (WT _ (validTy PiValidDom f vΔ vσ)).
      * exact (WT _ RvΠFG).
    + intros wl'' Hover.
      pose (Ho := over_tree_fusion_l (over_tree_fusion_l Hover)).
      pose (Ho' := over_tree_fusion_r (over_tree_fusion_l Hover)).
      pose (Ho'' := over_tree_fusion_r Hover).
      pose (Help:= WRed _ RvΠFG _ Ho').
      apply Induction.invLRΠ in Help.
      destruct Help as [dom cod red ? ? ? [? ? Hdom ? Hcod _ _]].
      specialize (Hcod Δ (σ 0) wl'' wk_id (idε _) (wfc_Ltrans (over_tree_le Hover) vΔ)).
      assert (HF : F[↑ >> σ] = dom).
      { eapply redtywf_whnf in red as [=]; [tea|constructor]. }
      assert (HG0 : G[up_term_term (↑ >> σ)] = cod).
      { eapply redtywf_whnf in red as [=]; [tea|constructor]. }
      assert (HG : G[σ] = cod[σ 0 .: @wk_id Δ >> tRel]).
      { rewrite <- HG0; bsimpl; apply ext_term; intros []; reflexivity. }
      rewrite HG.
      econstructor.
      intros wl''' Hover' ; eapply Hcod.
      exact Hover'.
      Unshelve. irrelevance0; [|unshelve eapply v0 ; eauto].
      now rewrite wk_id_ren_on.
  - intros Δ wl' σ σ' f vΔ [vσ v0] [vσ' v0'] [vσσ' v00'].
    cbn; refold.
    assert (vΠ := validTyExt vΠFG _ _ vσ vσ' vσσ').
    instValid vσ.
    eapply TreeEqSplit.
    intros wl'' Hover HGRed.
    epose (Ho := over_tree_fusion_l (over_tree_fusion_l (over_tree_fusion_l Hover))).
    epose (Ho' := over_tree_fusion_r (over_tree_fusion_l (over_tree_fusion_l Hover))).
    epose (Ho2 := over_tree_fusion_l (over_tree_fusion_r (over_tree_fusion_l Hover))).
    epose (Ho3 := over_tree_fusion_r (over_tree_fusion_r (over_tree_fusion_l Hover))).
    epose (Ho4 := over_tree_fusion_l (over_tree_fusion_l (over_tree_fusion_r Hover))).
    epose (Ho5 := over_tree_fusion_r (over_tree_fusion_l (over_tree_fusion_r Hover))).
    epose (Ho6 := over_tree_fusion_l (over_tree_fusion_r (over_tree_fusion_r Hover))).
    epose (Ho7 := over_tree_fusion_r (over_tree_fusion_r (over_tree_fusion_r Hover))).
    pose (Help := WRed _ RvΠFG _ Ho).
    pose (Help2 := WRedEq _ vΠ _ Ho' Ho2).
    cbn in Help; apply Induction.invLRΠ in Help.
    eapply LRTyEqIrrelevant' with (lrA' := LRPi' Help) in Help2; [|reflexivity].
    destruct Help as [dom cod red ? ? ? [? ? ? ? ? ? Hcod]].
    destruct Help2 as [dom' cod' red' ? ? [Hdom' ? Hcod']]; simpl in *.
    specialize (Hcod' Δ (σ' 0) _ wk_id (idε _) (wfc_Ltrans (over_tree_le Ho) vΔ)).
    assert (HF : F[↑ >> σ] = dom).
    { eapply redtywf_whnf in red as [=]; [tea|constructor]. }
    assert (HF' : F[↑ >> σ'] = dom').
    { eapply redtywf_whnf in red' as [=]; [tea|constructor]. }
    assert (HG0 : G[up_term_term (↑ >> σ)] = cod).
    { eapply redtywf_whnf in red as [=]; [tea|constructor]. }
    assert (HG : G[σ] = cod[σ 0 .: @wk_id Δ >> tRel]).
    { rewrite <- HG0; bsimpl; apply ext_term; intros []; reflexivity. }
    assert (HG0' : G[up_term_term (↑ >> σ')] = cod').
    { eapply redtywf_whnf in red' as [=]; [tea|constructor]. }
    assert (HG' : G[σ'] = cod'[σ' 0 .: @wk_id Δ >> tRel]).
    { rewrite <- HG0'; bsimpl; apply ext_term; intros []; reflexivity. }
    rewrite HG'.
    assert (Hσ0 : [shpRed Δ wl'' wk_id ((idε) wl'') (wfc_Ltrans (over_tree_le Ho) vΔ) | _ ||- σ 0 : _]< wl'' >).
    { irrelevance0; [| unshelve eapply v0 ; [exact Ho3 | exact Ho4 ]].
      now rewrite wk_id_ren_on. }
    assert (Hσ0' : [shpRed Δ wl'' wk_id ((idε) wl'') (wfc_Ltrans (over_tree_le Ho) vΔ) | _ ||- σ' 0 : _]< wl'' >).
    { eapply LRTmRedConv; [|unshelve eapply v0' ; [exact Ho5 | exact Ho6] ].
      eapply LRTyEqSym; rewrite HF'.
      rewrite <- (wk_id_ren_on Δ dom').
      unshelve eapply Hdom' ; [exact ((idε) wl'') | ].
      exact (wfc_Ltrans (over_tree_le Ho) vΔ).
    }
    eassert (Hcod0 := Hcod Δ _ (σ 0) (σ' 0) wk_id ((idε) wl'') (wfc_Ltrans (over_tree_le Ho) vΔ) Hσ0 Hσ0').
    econstructor.
    intros wl''' Hover' Hover''.
    eapply Transitivity.transEq; [| unshelve eapply Hcod'].
    eapply Transitivity.transEq; [|unshelve eapply Hcod0].
    1:{ unshelve (irrelevance0; [|eapply reflLRTyEq]); try now symmetry.
        shelve.
        unshelve eapply posRed.
        4: eauto.
        eapply over_tree_fusion_l ; exact Hover''.
    }
    2:{ irrelevance0; [| unshelve eapply v00' ; auto ; exact Ho7].
        now rewrite wk_id_ren_on.
    }
    1: now eapply over_tree_fusion_l.
    3: eauto.
    1,3: eapply over_tree_fusion_l, over_tree_fusion_r ; exact Hover''.
    1: do 3 (eapply over_tree_fusion_r) ; exact Hover''.
    eapply over_tree_fusion_l, over_tree_fusion_r, over_tree_fusion_r ; exact Hover''.
  Qed.

End PiTyDomValidity.

Section PiTyCongruence.

  Context `{GenericTypingProperties}.
  Context {wl Γ F G F' G' l}
    (vΓ : [||-v Γ]< wl >)
    (vF : [ Γ ||-v< l > F | vΓ ]< wl >)
    (vG : [ Γ ,, F ||-v< l > G | validSnoc' vΓ vF ]< wl >)
    (vF' : [ Γ ||-v< l > F' | vΓ ]< wl >)
    (vG' : [ Γ ,, F' ||-v< l > G' | validSnoc' vΓ vF' ]< wl >)
    (vFF' : [ Γ ||-v< l > F ≅ F' | vΓ | vF ]< wl >)
    (vGG' : [ Γ ,, F ||-v< l > G ≅ G' | validSnoc' vΓ vF | vG ]< wl >).

  Lemma PiEqRed2 {Δ σ wl' f} (tΔ : [ |-[ ta ] Δ]< wl' >) (vσ : [vΓ | Δ ||-v σ : _ | tΔ | f]< wl >)
    : W[ Δ ||-< l > (tProd F G)[σ] ≅ (tProd F' G')[σ] | validTy (PiValid vΓ vF vG) f tΔ vσ ]< wl' >.
  Proof.
    unfold PiValid, PiRed ; cbn.
    set (p := substPolyRed vΓ vF vG _ vσ).
    set (p' := substPolyRed vΓ vF' vG' _ vσ).
    set (peq := substEqPolyRedEq vΓ vF vG _ vσ vF' vG' vFF' vGG').
    set (peq' := (substPolyRedEq vΓ vF vG tΔ vσ vσ (reflSubst vΓ f tΔ vσ))).
    destruct (WpolyRedEqId p peq') ; cbn.
    destruct (WpolyRedId p); destruct (WpolyRedId p') ; destruct (WpolyRedEqId p peq) ; cbn.
    Wescape; cbn; tea.
    econstructor ; intros wl'' Hover Hover'; cbn.
    econstructor ; cbn in *.
    - eapply redtywf_refl, wft_Ltrans ; [now eapply (over_tree_le Hover) | ].
      gen_typing.
    - eapply convty_Ltrans ; [ now eapply over_tree_le | ] ; cbn.
      now gen_typing.
    - eapply convty_Ltrans ; [ now eapply over_tree_le | ] ; cbn.
      now gen_typing.
    - eapply peq.
      exact Hover'.
  Qed.

  Lemma PiCong : [ Γ ||-v< l > tProd F G ≅ tProd F' G' | vΓ | PiValid vΓ vF vG ]< wl >.
  Proof.
    econstructor. intros Δ wl' σ f. eapply PiEqRed2.
  Qed.

End PiTyCongruence.


Section PiTmValidity.

  Context `{GenericTypingProperties}.
  Context {wl Γ F G} (VΓ : [||-v Γ]< wl >)
    (VF : [ Γ ||-v< one > F | VΓ ]< wl >)
    (VU : [ Γ ,, F ||-v< one > U | validSnoc' VΓ VF ]< wl >)
    (VFU : [ Γ ||-v< one > F : U | VΓ | UValid VΓ ]< wl >)
    (VGU : [ Γ ,, F ||-v< one > G : U | validSnoc' VΓ VF | VU ]< wl >) .
    (* (VF := univValid (l':=zero) _ _ vFU)
    (VG := univValid (l':=zero) _ _ vGU). *)

  Lemma prodTyEqU {Δ σ σ' wl' f} (tΔ : [ |-[ ta ] Δ]< wl' >)
    (Vσ : [VΓ | Δ ||-v σ : _ | tΔ | f]< wl >)
    (Vσ' : [VΓ | Δ ||-v σ' : _ | tΔ | f]< wl >)
    (Vσσ' : [VΓ | Δ ||-v σ ≅ σ' : _ | tΔ | Vσ | f ]< wl >)
    : [Δ |-[ ta ] tProd F[σ] G[up_term_term σ] ≅ tProd F[σ'] G[up_term_term σ'] : U]< wl' >.
  Proof.
    pose proof (Vuσ := liftSubstS' VF Vσ).
    pose proof (Vureaσ' := liftSubstSrealign' VF Vσσ' Vσ').
    pose proof (Vuσσ' := liftSubstSEq' VF Vσσ').
    instAllValid Vσ Vσ' Vσσ'; instAllValid Vuσ Vureaσ' Vuσσ' ; Wescape.
    eapply convtm_prod; tea.
  Qed.

  Lemma PiRedU {Δ σ wl' f} (tΔ : [ |-[ ta ] Δ]< wl' >) (Vσ : [VΓ | Δ ||-v σ : _ | tΔ | f]< wl >)
    : W[ Δ ||-< one > (tProd F G)[σ] : U | validTy (UValid VΓ) f tΔ Vσ ]< wl' >.
  Proof.
    pose proof (Vσσ := reflSubst _ _ _ Vσ).
    pose proof (Vuσ := liftSubstS' VF Vσ).
    pose proof (Vuσσ := liftSubstSEq' VF Vσσ).
    instAllValid Vσ Vσ Vσσ; instAllValid Vuσ Vuσ Vuσσ; Wescape.
    econstructor ; intros wl'' Hover Hover'.
    econstructor; cbn.
    - apply redtmwf_refl; cbn in *. eapply ty_Ltrans ; [now eapply over_tree_le | ].
      now eapply ty_prod.
    - constructor.
    - eapply convtm_Ltrans ; [now eapply over_tree_le | ].
      now eapply convtm_prod.
    - cbn. unshelve refine (WRed _ (WLRCumulative (PiRed _ _ _ _ tΔ Vσ)) _ _). 
      1: unshelve eapply univValid; tea; try irrValid.
      1: unshelve eapply univValid; tea; try irrValid.
      exact Hover'.
  Defined.

  Lemma PiValidU : [ Γ ||-v< one > tProd F G : U | VΓ | UValid VΓ ]< wl >.
  Proof.
    econstructor.
    - intros Δ wl' σ f tΔ Vσ.
      exact (PiRedU tΔ Vσ).
    - intros Δ wl' σ σ' f tΔ Vσ Vσ' Vσσ'.
      pose proof (univValid (l' := zero) _ _ VFU) as VF0.
      pose proof (irrelevanceTy (validSnoc' VΓ VF)
                    (validSnoc' (l := zero) VΓ VF0)
                    (univValid (l' := zero) _ _ VGU)) as VG0.
      pose proof (Help := PiEqRed1 VΓ VF0 VG0 tΔ Vσ Vσ' Vσσ').
      econstructor ; intros.
      unshelve econstructor ; cbn.
      + eapply (PiRedU tΔ Vσ), over_tree_fusion_l, over_tree_fusion_l ; exact Hover'.
      + eapply (PiRedU tΔ Vσ'), over_tree_fusion_r, over_tree_fusion_l ; exact Hover'.
      + unshelve eapply PiRedU ; cycle 1 ; try eassumption.
        do 2 (eapply over_tree_fusion_l) ; exact Hover'.
      + cbn ; eapply convtm_Ltrans; [ now eapply over_tree_le | ]. 
        exact (prodTyEqU tΔ Vσ Vσ' Vσσ').
      + unshelve eapply PiRedU ; cycle 1 ; try eassumption.
        eapply over_tree_fusion_r, over_tree_fusion_l ; exact Hover'.
      + cbn ; unshelve eapply LRTyEqIrrelevantCum'. 
        4: reflexivity.
        3: eapply Help. 
        eapply over_tree_fusion_l, over_tree_fusion_r ; exact Hover'.
        Unshelve.
        now do 2 (eapply over_tree_fusion_r) ; exact Hover'.
  Qed.

End PiTmValidity.


Section PiTmCongruence.

  Context `{GenericTypingProperties}.
  Context {wl Γ F G F' G'}
    (vΓ : [||-v Γ]< wl >)
    (vF : [ Γ ||-v< one > F | vΓ ]< wl >)
    (vU : [ Γ ,, F ||-v< one > U | validSnoc' vΓ vF ]< wl >)
    (vFU : [ Γ ||-v< one > F : U | vΓ | UValid vΓ ]< wl >)
    (vGU : [ Γ ,, F ||-v< one > G : U | validSnoc' vΓ vF | vU ]< wl >)
    (vF' : [ Γ ||-v< one > F' | vΓ ]< wl >)
    (vU' : [ Γ ,, F' ||-v< one > U | validSnoc' vΓ vF' ]< wl >)
    (vF'U : [ Γ ||-v< one > F' : U | vΓ | UValid vΓ ]< wl >)
    (vG'U : [ Γ ,, F' ||-v< one > G' : U | validSnoc' vΓ vF' | vU' ]< wl >)
    (vFF' : [ Γ ||-v< one > F ≅ F' : U | vΓ | UValid vΓ ]< wl >)
    (vGG' : [ Γ ,, F ||-v< one > G ≅ G' : U | validSnoc' vΓ vF | vU ]< wl >).

  Lemma PiCongTm : [ Γ ||-v< one > tProd F G ≅ tProd F' G' : U | vΓ | UValid vΓ ]< wl >.
  Proof.
    econstructor.
    intros Δ wl' σ f tΔ Vσ.
    pose proof (univValid (l' := zero) _ _ vFU) as vF0.
    pose proof (univValid (l' := zero) _ _ vF'U) as vF'0.
    pose proof (Vσσ := reflSubst _ _ _ Vσ).
    pose proof (Vuσ := liftSubstS' vF Vσ).
    pose proof (Vuσσ := liftSubstSEq' vF Vσσ).
    instAllValid Vσ Vσ Vσσ; instAllValid Vuσ Vuσ Vuσσ; Wescape.
    pose proof (irrelevanceTy (validSnoc' vΓ vF)
                  (validSnoc' (l := zero) vΓ vF0)
                  (univValid (l' := zero) _ _ vGU)) as vG0.
    pose proof (irrelevanceTy (validSnoc' vΓ vF')
                  (validSnoc' (l := zero) vΓ vF'0)
                  (univValid (l' := zero) _ _ vG'U)) as vG'0.
    pose proof (univEqValid (validSnoc' vΓ vF) vU (univValid (l' := zero) _ _ vGU) vGG') as vGG'0.
    epose (Help:= PiEqRed2 vΓ vF0 vG0 vF'0 vG'0 _ _ tΔ Vσ).
    econstructor ; intros wl'' Hover.
    unshelve econstructor ; cbn.
    - eapply (PiRedU vΓ vF vU vFU vGU tΔ Vσ).
      do 2 (eapply over_tree_fusion_l) ; exact Hover'.
    - eapply (PiRedU vΓ vF' vU' vF'U vG'U tΔ Vσ).
      eapply over_tree_fusion_r, over_tree_fusion_l ; exact Hover'.
    - unshelve eapply PiRedU ; cycle 4 ; try eassumption.
      eapply over_tree_fusion_l, over_tree_fusion_r, over_tree_fusion_r ; exact Hover'.
    - cbn.
      eapply convtm_Ltrans ; [eapply over_tree_le ; exact Hover | ].
      now eapply convtm_prod.
    - unshelve eapply PiRedU ; cycle 4 ; try eassumption.
      eapply over_tree_fusion_r, over_tree_fusion_r, over_tree_fusion_r ; exact Hover'.
    - cbn.
      unshelve eapply LRTyEqIrrelevantCum'.
      4: reflexivity.
      3: unshelve eapply Help.
      1: eapply over_tree_fusion_l, over_tree_fusion_l, over_tree_fusion_r ; exact Hover'.
      1: eapply over_tree_fusion_r, over_tree_fusion_l, over_tree_fusion_r ; exact Hover'.
      Unshelve.
      + exact (univEqValid vΓ (UValid vΓ) vF0 vFF').
      + refine (irrelevanceTyEq _ _ _ _ vGG'0).
Qed.

End PiTmCongruence.

