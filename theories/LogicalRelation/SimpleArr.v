From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Notations Utils BasicAst LContexts Context NormalForms Weakening GenericTyping LogicalRelation Monad.
From LogRel.LogicalRelation Require Import Induction Irrelevance Weakening Neutral Escape Reflexivity NormalRed Reduction Monotonicity Transitivity Application.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Section SimpleArrow.
  Context `{GenericTypingProperties}.
  
  Lemma shiftPolyRed {wl Γ l A B} :
    [Γ ||-<l> A]< wl > ->
    [Γ ||-<l> B]< wl > ->
    PolyRed wl Γ l A B⟨↑⟩.
  Proof.
    intros; escape; unshelve econstructor.
    - intros; eapply wk ; eauto.
      now eapply Ltrans.
    - intros.
      now econstructor.
    - intros; bsimpl; rewrite <- rinstInst'_term; eapply wk.
      + now eapply wfc_Ltrans.
      + eapply Ltrans ; [ | eassumption].
        eapply wfLCon_le_trans ; eauto.
    - intros ; now econstructor.
    - now escape.
    - renToWk; eapply wft_wk; gen_typing.
    - intros; irrelevance0.
      2: replace (subst_term _ _) with B⟨ρ⟩.
      2: eapply wkEq, reflLRTyEq.
      all: bsimpl; now rewrite rinstInst'_term.
      Unshelve. 1: tea.
      + now eapply wfc_Ltrans.
      + eapply Ltrans ; [ | eassumption].
        eapply wfLCon_le_trans ; eauto.
  Qed.


  Lemma ArrRedTy0 {wl Γ l A B} :
    [Γ ||-<l> A]< wl > ->
    [Γ ||-<l> B]< wl > ->
    [Γ ||-Π<l> arr A B]< wl >.
  Proof.
    intros RA RB; escape.
    unshelve econstructor; [exact A| exact B⟨↑⟩|..]; tea.
    - eapply redtywf_refl.
      now eapply wft_simple_arr.
    - now unshelve eapply escapeEq, reflLRTyEq.
    - eapply convty_simple_arr; tea.
      all: now unshelve eapply escapeEq, reflLRTyEq.
    - now eapply shiftPolyRed.
  Qed.

  Lemma ArrRedTy {wl Γ l A B} :
    [Γ ||-<l> A]< wl > ->
    [Γ ||-<l> B]< wl > ->
    [Γ ||-<l> arr A B]< wl >.
  Proof. intros; eapply LRPi'; now eapply ArrRedTy0. Qed.

  Lemma WArrRedTy {wl Γ l A B} :
    W[Γ ||-<l> A]< wl > ->
    W[Γ ||-<l> B]< wl > ->
    W[Γ ||-<l> arr A B]< wl >.
  Proof.
    intros [WTA WRedA] [WTB WRedB].
    exists (DTree_fusion _ WTA WTB).
    intros ; eapply ArrRedTy.
    - now eapply WRedA, over_tree_fusion_l.
    - now eapply WRedB, over_tree_fusion_r.
  Qed.

  Lemma shiftPolyRedEq {wl Γ l A A' B B'}
    (RA : [Γ ||-<l> A]< wl >)
    (RB : [Γ ||-<l> B]< wl >)
    (PAB : PolyRed wl Γ l A B⟨↑⟩) :
    [Γ ||-<l> A ≅ A' | RA]< wl > ->
    [Γ ||-<l> B ≅ B' | RB]< wl > ->
    PolyRedEq PAB A' B'⟨↑⟩.
  Proof.
    intros; escape; unshelve econstructor.
    - intros ; now econstructor.
    - intros; irrelevanceRefl; eapply wkEq.
      unshelve eapply (Eq_Ltrans f) ; eassumption.
    - intros; irrelevance0; rewrite shift_subst_scons; [reflexivity|].
      eapply wkEq, (Eq_Ltrans (wfLCon_le_trans _ f)) ; eassumption.
      Unshelve. all: eauto.
      now eapply wfc_Ltrans.
  Qed.

  Lemma arrRedCong0 {wl Γ l A A' B B'}
    (RA : [Γ ||-<l> A]< wl >)
    (RB : [Γ ||-<l> B]< wl >)
    (tyA' : [Γ |- A']< wl >)
    (tyB' : [Γ |- B']< wl >)
    (RAB : [Γ ||-Π<l> arr A B]< wl >) :
    [Γ ||-<l> A ≅ A' | RA]< wl > ->
    [Γ ||-<l> B ≅ B' | RB]< wl > ->
    [Γ ||-Π arr A B ≅ arr A' B' | normRedΠ0 RAB]< wl >.
  Proof.
    intros RAA' RBB'; escape.
    unshelve econstructor; cycle 2.
    + eapply redtywf_refl; now eapply wft_simple_arr.
    + now cbn.
    + now eapply convty_simple_arr.
    + now eapply shiftPolyRedEq.
  Qed.
    
  Lemma arrRedCong {wl Γ l A A' B B'}
    (RA : [Γ ||-<l> A]< wl >) (RB : [Γ ||-<l> B]< wl >)
    (tyA' : [Γ |- A']< wl >) (tyB' : [Γ |- B']< wl >) :
    [Γ ||-<l> A ≅ A' | RA]< wl > ->
    [Γ ||-<l> B ≅ B' | RB]< wl > ->
    [Γ ||-<l> arr A B ≅ arr A' B' | normRedΠ (ArrRedTy RA RB)]< wl >.
  Proof.
    intros; now eapply arrRedCong0.
  Qed.

  Lemma arrRedCong' {wl Γ l A A' B B'}
    (RA : [Γ ||-<l> A]< wl >) (RB : [Γ ||-<l> B]< wl >)
    (tyA' : [Γ |- A']< wl >) (tyB' : [Γ |- B']< wl >)
    (RAB : [Γ ||-<l> arr A B]< wl >) :
    [Γ ||-<l> A ≅ A' | RA]< wl > ->
    [Γ ||-<l> B ≅ B' | RB]< wl > ->
    [Γ ||-<l> arr A B ≅ arr A' B' | RAB]< wl >.
  Proof.
    intros; irrelevanceRefl; now eapply arrRedCong.
  Qed.

  Lemma WarrRedCong' {wl Γ l A A' B B'}
    (RA : W[Γ ||-<l> A]< wl >) (RB : W[Γ ||-<l> B]< wl >)
    (tyA' : [Γ |- A']< wl >) (tyB' : [Γ |- B']< wl >)
    (RAB : W[Γ ||-<l> arr A B]< wl >) :
    W[Γ ||-<l> A ≅ A' | RA]< wl > ->
    W[Γ ||-<l> B ≅ B' | RB]< wl > ->
    W[Γ ||-<l> arr A B ≅ arr A' B' | RAB]< wl >.
  Proof.
    intros [WTAA WEqA] [WTBB WEqB].
    exists (DTree_fusion _ (DTree_fusion _ (WT _ RA) (WT _ RB))
              (DTree_fusion _ WTAA WTBB)).
    intros wl' Hover hover'.
    pose proof (f := over_tree_le Hover).
    eapply arrRedCong'.
    1,2: now eapply wft_Ltrans.
    - unshelve eapply WEqA.
      + now do 2 (eapply over_tree_fusion_l).
      + now eapply over_tree_fusion_l, over_tree_fusion_r.
    - unshelve eapply WEqB.
      + now eapply over_tree_fusion_r, over_tree_fusion_l.
      + now do 2 (eapply over_tree_fusion_r).
  Qed.

  Lemma polyRedArrExt {wl Γ l A B C} :
    PolyRed wl Γ l A B -> PolyRed wl Γ l A C -> PolyRed wl Γ l A (arr B C).
  Proof.
    intros [tyA tyB RA RTree RB RBExtTree RBext] [_ tyC RA' RTree' RC RCExtTree RCext].
    unshelve econstructor.
    6: now eapply wft_simple_arr.
    1,5: eassumption.
    + intros ; eapply DTree_fusion.
       * unshelve eapply RTree.
         3-5: eassumption.
         2: irrelevance0 ; [ reflexivity | eassumption].
       * unshelve eapply RTree'.
         3-5: eassumption.
         2: irrelevance0 ; [ reflexivity | eassumption].
    + intros; rewrite subst_arr; refold.
      apply ArrRedTy; [eapply RB| eapply RC].
      cbn in *.
      * now eapply over_tree_fusion_l.
      * now eapply over_tree_fusion_r.
    + intros ; eapply DTree_fusion.
       * unshelve eapply (RBExtTree _ _ a b).
         2-4: eassumption.
         1-3 : irrelevance0 ; [ reflexivity | eassumption].
       * unshelve eapply (RCExtTree _ _ a b).
         2-4: eassumption.
         1-3: irrelevance0 ; [reflexivity | eassumption].
    + intros.
      irrelevance0; rewrite subst_arr; [refold; reflexivity|]; refold.
      unshelve eapply arrRedCong.
      3,4: eapply escapeConv ; first [eapply RBext | eapply RCext] ; cycle 1.
      7,8: first [eapply RBext| eapply RCext].
      all: cbn in *.
      Unshelve.
      all: try (eapply over_tree_fusion_l ; eassumption).
      all: try (eapply over_tree_fusion_r ; eassumption).
  Qed.

  Lemma polyRedEqArrExt {wl Γ l A A' B B' C C'}
    (PAB : PolyRed wl Γ l A B) (PAC : PolyRed wl Γ l A C) 
    (PAB' : PolyRed wl Γ l A' B') (PAC' : PolyRed wl Γ l A' C') 
    (PABC : PolyRed wl Γ l A (arr B C))
    (PABeq : PolyRedEq PAB A' B')
    (PACeq : PolyRedEq PAC A' C')
    : PolyRedEq PABC A' (arr B' C').
  Proof.
    econstructor.
    + intros; irrelevanceRefl; now unshelve eapply (PolyRedEq.shpRed PABeq).
    + intros; irrelevance0; rewrite subst_arr; refold; [reflexivity|].
      pose proof (f' := over_tree_le Ho).
      apply arrRedCong.
      * eapply escapeConv.
        unshelve eapply (PolyRedEq.posRed PABeq) ; cycle 1 ; try eassumption.
        -- now irrelevance0.
        -- do 3 (eapply over_tree_fusion_l) ; exact Ho' .
        -- eapply over_tree_fusion_r ; do 2 (eapply over_tree_fusion_l) ; exact Ho'.
      * eapply escape; unshelve eapply (PolyRed.posRed).
        5: exact f.
        4: eapply LRTmRedConv; tea.
        4: irrelevanceRefl; unshelve eapply (PolyRedEq.shpRed PABeq).
        1,2,3,4: eassumption.
        eapply over_tree_fusion_r, over_tree_fusion_l ; exact Ho'.
      * unshelve eapply (PolyRedEq.posRed PABeq).
        2,3: eassumption.
        1: now irrelevanceRefl.
        all: cbn in *.
        1: now do 3 (eapply over_tree_fusion_l).
        now eapply over_tree_fusion_r ; do 2 (eapply over_tree_fusion_l).
      * unshelve eapply (PolyRedEq.posRed PACeq).
        2,3: eassumption.
        1: now irrelevanceRefl.
        all: cbn in *.
        eapply over_tree_fusion_l, over_tree_fusion_r ; exact Ho'.
        do 2 (eapply over_tree_fusion_r) ; exact Ho'.
  Qed.

  Lemma idred {wl Γ l A} (RA : [Γ ||-<l> A]< wl >) :
    [Γ ||-<l> idterm A : arr A A | ArrRedTy RA RA]< wl >.
  Proof.
    eassert [_ | Γ,, A ||- tRel 0 : A⟨_⟩]< wl > as hrel.
    {
      eapply var0.
      1: reflexivity.
      now escape.
    }
    Unshelve.
    all: cycle -1.
    { 
      erewrite <- wk1_ren_on.
      eapply wk ; tea.
      escape.
      gen_typing.
    }
    eapply reflLRTmEq in hrel.
    normRedΠ ΠAA.
    pose proof (reflLRTyEq RA).
    escape.
    assert (h : forall Δ wl' a (ρ : Δ ≤ Γ) (f : wl' ≤ε wl)
                       (wfΔ : [|- Δ]< wl' >) RA
                       (ha : [Δ ||-<l> a : A⟨ρ⟩ | RA]< wl' >),
      [Δ ||-<l> tApp (idterm A)⟨ρ⟩ a : A⟨ρ⟩| RA]< wl' > ×
      [Δ ||-<l> tApp (idterm A)⟨ρ⟩ a ≅ a : A⟨ρ⟩| RA]< wl' >
    ).
    1:{
      intros; cbn; escape.
      assert [Δ |- A⟨ρ⟩]< wl' > by (eapply wft_wk ; eauto ; now eapply wft_Ltrans).
      assert [Δ |- A⟨ρ⟩ ≅ A⟨ρ⟩]< wl' >
        by (eapply convty_wk ; eauto ; now eapply convty_Ltrans).
      eapply redSubstTerm; tea.
      now eapply redtm_id_beta.
    }
    unshelve econstructor; cbn.
    4: eapply redtmwf_refl; now eapply ty_id.
    - intros ; now econstructor.
    - intros ; now econstructor.
    - eapply convtm_id; tea.
      eapply wfc_wft; now escape.
    - unshelve econstructor 1.
      + intros ; now econstructor.
      + intros; cbn; apply reflLRTyEq.
      + intros; cbn.
        irrelevance0; [|eapply (Tm_Ltrans Ho') ; exact ha].
        cbn; bsimpl; now rewrite rinstInst'_term.
    - intros; cbn; irrelevance0.
      2: eapply h ; eauto.
      2: now eapply wfLCon_le_trans.
      2: now eapply wfc_Ltrans.
      + bsimpl; now rewrite rinstInst'_term.
      + now eapply (Tm_Ltrans Ho').
    - intros ; cbn; irrelevance0; cycle 1.
      1: eapply transEqTerm;[|eapply transEqTerm].
      + eapply h.
        * now eapply wfLCon_le_trans.
        * now eapply wfc_Ltrans.
        * now eapply (Tm_Ltrans Hoa).
      + eapply (TmEq_Ltrans Hoa) ; eassumption.
      + eapply (TmEq_Ltrans Hoa),LRTmEqSym ; now eapply h.
      + bsimpl; now rewrite rinstInst'_term.
  Qed.

  Section SimpleAppTerm.
    Context {wl Γ t u F G l}
      {RF : [Γ ||-<l> F]< wl >}
      (RG : [Γ ||-<l> G]< wl >)
      (hΠ := normRedΠ (ArrRedTy RF RG))
      (Rt : [Γ ||-<l> t : arr F G | hΠ]< wl >)
      (Ru : [Γ ||-<l> u : F | RF]< wl >)
      (WRG := Build_WLogRel l wl Γ G (leaf _)
                (fun wl Hover => Ltrans (over_tree_le Hover) RG)).

    Lemma simple_app_id : W[Γ ||-<l> tApp (PiRedTm.nf Rt) u : G | WRG ]< wl >.
    Proof.
      unshelve eapply WLRTmRedIrrelevant'.
      5: eapply app_id.
      1: tea.
      1,2: now bsimpl.
      eassumption.
    Qed.

    Lemma simple_appTerm0 :
        W[Γ ||-<l> tApp t u : G | WRG]< wl >
        × W[Γ ||-<l> tApp t u ≅ tApp (PiRedTm.nf Rt) u : G | WRG]< wl >.
    Proof.
      eapply WLRTmTmEqIrrelevant'.
      2: now eapply appTerm0.
      now bsimpl.
      Unshelve. 1: tea.
      now bsimpl.
    Qed.

  End SimpleAppTerm.

  Lemma simple_appTerm {wl Γ t u F G l}
    {RF : [Γ ||-<l> F]< wl >}
    (RG : [Γ ||-<l> G]< wl >) 
    (RΠ : [Γ ||-<l> arr F G]< wl >)
    (Rt : [Γ ||-<l> t : arr F G | RΠ]< wl >)
    (Ru : [Γ ||-<l> u : F | RF]< wl >) :
    W[Γ ||-<l> tApp t u : G| (LogtoW RG)]< wl >.
  Proof.
    unshelve eapply WLRTmRedIrrelevant'.
    5: unshelve eapply appTerm.
    6-9: eauto.
    1: eapply LogtoW.
    1,2: now bsimpl.
  Qed.

    
  Lemma Wsimple_appTerm {wl Γ t u F G l}
    {RF : W[Γ ||-<l> F]< wl >}
    (RG : W[Γ ||-<l> G]< wl >) 
    (RΠ : W[Γ ||-<l> arr F G]< wl >)
    (Rt : W[Γ ||-<l> t : arr F G | RΠ]< wl >)
    (Ru : W[Γ ||-<l> u : F | RF]< wl >) :
    W[Γ ||-<l> tApp t u : G| RG]< wl >.
  Proof.
    unshelve eapply WLRTmRedIrrelevant'.
    5: unshelve eapply WappTerm.
    6-9: eauto.
    1,2: now bsimpl.
  Qed.


  Lemma simple_appcongTerm {wl Γ t t' u u' F G l}
    {RF : [Γ ||-<l> F]< wl >}
    (RG : [Γ ||-<l> G]< wl >)
    (RΠ : [Γ ||-<l> arr F G]< wl >) 
    (Rtt' : [Γ ||-<l> t ≅ t' : _ | RΠ]< wl >)
    (Ru : [Γ ||-<l> u : F | RF]< wl >)
    (Ru' : [Γ ||-<l> u' : F | RF]< wl >)
    (Ruu' : [Γ ||-<l> u ≅ u' : F | RF ]< wl >) :
      W[Γ ||-<l> tApp t u ≅ tApp t' u' : G | (LogtoW RG)]< wl >.
  Proof.
    unshelve eapply WLRTmEqIrrelevant'.
    5: unshelve eapply appcongTerm.
    7-12: tea.
    1: eapply LogtoW.
    1,2: now bsimpl.
  Qed.
    

  Lemma Wsimple_appcongTerm {wl Γ t t' u u' F G l}
    {RF : W[Γ ||-<l> F]< wl >}
    (RG : W[Γ ||-<l> G]< wl >)
    (RΠ : W[Γ ||-<l> arr F G]< wl >) 
    (Rtt' : W[Γ ||-<l> t ≅ t' : _ | RΠ]< wl >)
    (Ru : W[Γ ||-<l> u : F | RF]< wl >)
    (Ru' : W[Γ ||-<l> u' : F | RF]< wl >)
    (Ruu' : W[Γ ||-<l> u ≅ u' : F | RF ]< wl >) :
      W[Γ ||-<l> tApp t u ≅ tApp t' u' : G | RG]< wl >.
  Proof.
    unshelve eapply WLRTmEqIrrelevant'.
    5: unshelve eapply WappcongTerm.
    7-12: tea.
    1,2: now bsimpl.
  Qed.

  Lemma wkRedArr {wl Γ l A B f} 
    (RA : [Γ ||-<l> A]< wl >) 
    (RB : [Γ ||-<l> B]< wl >) 
    {Δ} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]< wl >) :
    [Γ ||-<l> f : arr A B | ArrRedTy RA RB]< wl > ->
    [Δ ||-<l> f⟨ρ⟩ : arr A⟨ρ⟩ B⟨ρ⟩ | ArrRedTy (wk ρ wfΔ RA) (wk ρ wfΔ RB)]< wl >.
  Proof.
    intro; irrelevance0.
    2: unshelve eapply wkTerm; cycle 3; tea.
    symmetry; apply wk_arr.
  Qed.

  Definition compred_appTree {wl Γ l A B C f g} 
    (RA : [Γ ||-<l> A]< wl >) 
    (RB : [Γ ||-<l> B]< wl >) 
    (RC : [Γ ||-<l> C]< wl >) :
    [LRPi' (normRedΠ0 (invLRΠ (ArrRedTy RA RB))) | Γ ||- f : arr A B ]< wl > ->
    [LRPi' (normRedΠ0 (invLRΠ (ArrRedTy RB RC))) | Γ ||- g : arr B C ]< wl > ->
    forall Δ wl' a (ρ : Δ ≤ Γ) (tau : wl' ≤ε wl)
                       (wfΔ : [|- Δ]< wl' >)
                       (ha : [PolyRedPack.shpRed (normRedΠ0 (invLRΠ (ArrRedTy RA RB))) ρ tau wfΔ | Δ ||- a
                               : (ParamRedTyPack.dom (normRedΠ0 (invLRΠ (ArrRedTy RA RB))))⟨ρ⟩ ]< wl' >),
    DTree wl'.
  Proof.
    intros Rf Rg * ha.
    unshelve eapply DTree_bind_over.
    - eapply DTree_fusion.
      + now unshelve eapply (PiRedTm.appTree (a := a) Rf).
      + now unshelve eapply (PolyRedPack.posTree (normRedΠ0 (invLRΠ (ArrRedTy RA RB)))).
    - intros wl'' Hover.
      pose proof (f' := over_tree_le Hover).
      unshelve eapply (PiRedTm.appTree Rg).
      3: eassumption.
      2: now eapply wfLCon_le_trans.
      2: now eapply wfc_Ltrans.
      2: irrelevance0 ; [ | eapply (PiRedTm.app Rf)] .
      2: eapply over_tree_fusion_l ; eassumption.
      cbn.
      bsimpl.
      now rewrite rinstInst'_term.
      Unshelve.
      now eapply over_tree_fusion_r.
  Defined.
  
  Lemma compred {wl Γ l A B C u v} 
    (RA : [Γ ||-<l> A]< wl >) 
    (RB : [Γ ||-<l> B]< wl >) 
    (RC : [Γ ||-<l> C]< wl >) :
    [Γ ||-<l> u : arr A B | ArrRedTy RA RB]< wl > ->
    [Γ ||-<l> v : arr B C | ArrRedTy RB RC]< wl > ->
    [Γ ||-<l> comp A v u : arr A C | ArrRedTy RA RC]< wl >.
  Proof.
    intros Ru Rv.
    normRedΠin Ru; normRedΠin Rv; normRedΠ ΠAC.
    pose (d := compred_appTree RA RB RC Ru Rv).
    assert (h : forall Δ wl' a (ρ : Δ ≤ Γ) (f : wl' ≤ε wl)
                       (wfΔ : [|- Δ]< wl' >) RA
                       (ha : [Δ ||-<l> a : A⟨ρ⟩ | RA]< wl' >),
               W[Δ ||-<l> tApp v⟨ρ⟩ (tApp u⟨ρ⟩ a) : _ | Wwk ρ wfΔ (WLtrans f (LogtoW RC))]< wl' >).
    1:{
      intros.
      eapply WLRTmRedIrrelevant' ; [reflexivity | ].
      unshelve eapply Wsimple_appTerm.
      5: eapply simple_appTerm.
      3: eapply TmLogtoW.
      2,3: eapply wkRedArr.
      1,2: irrelevance0 ; [reflexivity | ].
      1,2: eapply (Tm_Ltrans f) ; eassumption.
      eassumption.
      Unshelve.
      3,6: eassumption.
      1: eapply LogtoW.
      1,2: eapply wk ; try eassumption.
      all: now eapply (Ltrans f).
    }
    assert (heq : forall Δ wl' a b (ρ : Δ ≤ Γ) (f : wl' ≤ε wl)
                         (wfΔ : [|- Δ]< wl' >) RA
                         (ha : [Δ ||-<l> a : A⟨ρ⟩ | RA]< wl' >)
                         (hb : [Δ ||-<l> b : A⟨ρ⟩ | RA]< wl' >)
                         (hab : [Δ ||-<l> a ≅ b: A⟨ρ⟩ | RA]< wl' >),
               W[Δ ||-<l> tApp v⟨ρ⟩ (tApp u⟨ρ⟩ a) ≅ tApp v⟨ρ⟩ (tApp u⟨ρ⟩ b) : _ |
                  Wwk ρ wfΔ (WLtrans f (LogtoW RC))]< wl' >).
    1:{
      intros.
      eapply WLRTmEqIrrelevant' ; [reflexivity | ].
      eapply Wsimple_appcongTerm ; [| | | unshelve eapply simple_appcongTerm ].
      1: eapply TmEqLogtoW.
      1,8: unshelve eapply reflLRTmEq, wkRedArr, (Tm_Ltrans' f).
      2,7,11,12,17-19: eassumption.
      1-4: now eapply (Ltrans f).
      1,2: unshelve eapply simple_appTerm.
      7,9: unshelve eapply wkRedArr, (Tm_Ltrans' f).
      13,14: irrelevance.
      6,10: now eapply ArrRedTy.
      all: try eassumption.
      5: eapply wk ; eauto.
      all: now eapply (Ltrans f).
      Unshelve.
      now eapply LogtoW, wk, (Ltrans f).
    }
    escape.
    assert (beta : forall Δ wl' a (ρ : Δ ≤ Γ) (f : wl' ≤ε wl)
                          (wfΔ : [|- Δ]< wl' >) RA
                          (ha : [Δ ||-<l> a : A⟨ρ⟩ | RA]< wl' >),
               W[Δ ||-<l> tApp (comp A v u)⟨ρ⟩ a : _ | Wwk ρ wfΔ (WLtrans f (LogtoW RC))]< wl' > ×
               W[Δ ||-<l> tApp (comp A v u)⟨ρ⟩ a ≅ tApp v⟨ρ⟩ (tApp u⟨ρ⟩ a) : _ |
                  Wwk ρ wfΔ (WLtrans f (LogtoW RC))]< wl' >).
    1:{
      intros; cbn. 
      assert (eq : forall t : term, t⟨↑⟩⟨upRen_term_term ρ⟩ = t⟨ρ⟩⟨↑⟩) by (intros; now asimpl).
      do 2 rewrite eq.
      eapply WredSubstTerm.
      + now eapply h.
      + eapply redtm_comp_beta.
        6: cbn in *; now escape.
        5: now erewrite wk_arr; eapply ty_wk, ty_Ltrans; tea.
        4: eapply typing_meta_conv.
        4: now eapply ty_wk, ty_Ltrans; tea.
        4: exact (wk_arr (A := A) (B := B) ρ).
        1-3: now eapply wft_wk, wft_Ltrans.
    }
    econstructor.
    - eapply redtmwf_refl.
      eapply ty_comp ; cycle 2 ; now tea.
    - cbn. eapply convtm_comp; cycle 6; tea.
      erewrite <- wk1_ren_on.
      eapply WescapeEqTerm.
      eapply WreflLRTmEq.
      do 2 erewrite <- wk1_ren_on.
      eapply h.
      eapply var0; now bsimpl.
      { now eapply wfc_ty. }
      unshelve eapply escapeEq, reflLRTyEq; tea.
      unshelve eapply escapeEq, reflLRTyEq; tea.
      Unshelve. 3: gen_typing.
      3: now eapply wfLCon_le_id.
      3: now eapply wk; tea; gen_typing.
      1:{ intros ; eapply DTree_fusion.
          + now unshelve eapply (fst (beta _ _ _ _ _ Hd _ ha)).
          + unshelve eapply (WTTmEq (Wwk ρ Hd (WLtrans f (LogtoW RC))) _).
            3: now unshelve eapply (snd (beta _ _ _ _ _ _ _ ha)).
      }
      intros ; eapply DTree_fusion.
      + now unshelve eapply (WTTmEq _ (heq _ _ _ _ _ _ Hd _ ha hb eq)).
      + exact (WT C⟨ρ⟩ (Wwk ρ Hd (WLtrans f (LogtoW RC)))).
    - unshelve econstructor 1; intros; cbn.
      + eapply h ; eassumption.
      + apply reflLRTyEq.
      + assert (Hrw : forall t, t⟨↑⟩[a .: ρ >> tRel] = t⟨ρ⟩).
        { intros; bsimpl; symmetry; now apply rinstInst'_term. }
        do 2 rewrite Hrw; irrelevance0; [symmetry; apply Hrw|].
        unshelve eapply h.
        7: exact Ho'.
        cbn ; now eapply over_tree_le.
    - intros; cbn in *.
      irrelevance0.
      2: unshelve eapply (fst (beta _ _ _ _ _ _ _ _)) ; cbn.
      3,4,6: eassumption.
      + bsimpl; now rewrite rinstInst'_term.
      + now eapply over_tree_le.
      + now eapply over_tree_fusion_l.
    - intros * hb hab ** ; irrelevance0; cycle 1 ; cbn in *.
      1: eapply transEqTerm;[|eapply transEqTerm].
      1:{ unshelve eapply (snd (beta _ _ _ _ _ _ _ _)) ; cbn in *.
          2,3,5: eassumption.
          * now eapply over_tree_le.
          * now eapply over_tree_fusion_r.
      }
      2:{ eapply LRTmEqSym.
          unshelve eapply  (snd (beta _ _ _ _ _ _ _ _)).
          2: eassumption.
          cbn in *.
          eapply over_tree_fusion_r ; eassumption.
      }
      cbn in *.
      irrelevance0 ; [ reflexivity | ].
      2: cbn ;  bsimpl ; now rewrite rinstInst'_term.
      unshelve eapply heq.
      2,3,6-8: eassumption.
      + now eapply over_tree_fusion_r.
      + now eapply over_tree_fusion_l.
  Qed.

End SimpleArrow.
