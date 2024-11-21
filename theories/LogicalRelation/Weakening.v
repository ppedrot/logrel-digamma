From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Notations Utils BasicAst LContexts Context NormalForms UntypedValues Weakening GenericTyping Monad LogicalRelation DeclarativeInstance.
From LogRel.LogicalRelation Require Import Induction Irrelevance Reflexivity Transitivity Escape.

Set Universe Polymorphism.

Section Weakenings.
  Context `{GenericTypingProperties}.

  Lemma wkU {wl Γ Δ l A} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]< wl >) (h : [Γ ||-U<l> A]< wl >) : [Δ ||-U<l> A⟨ρ⟩]< wl >.
  Proof. destruct h; econstructor; tea; change U with U⟨ρ⟩; gen_typing. Defined.

  Lemma wkPoly {wl Γ l shp pos Δ}  (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]< wl >) : 
    PolyRed wl Γ l shp pos -> 
    PolyRed wl Δ l shp⟨ρ⟩ pos⟨wk_up shp ρ⟩.
  Proof.
    intros []; unshelve econstructor.
    - intros ?? ρ' ??; replace (_⟨_⟩) with (shp⟨ρ' ∘w ρ⟩) by now bsimpl.
      now eapply shpRed.
    - intros ?? a ρ' **.
      unshelve eapply (posTree _ k' _ (ρ' ∘w ρ) f) ; eauto.
      now irrelevance.
    - intros ? a k' ρ' **. 
      replace (pos⟨_⟩[a .: ρ' >> tRel]) with (pos[ a .: (ρ' ∘w ρ) >> tRel]) by now bsimpl.
      set (f' := over_tree_le Ho).
      econstructor ; unshelve eapply posRed ; [ | eassumption | eassumption |..].
      irrelevance.
      cbn.
      assumption.
    - now eapply wft_wk.
    - eapply wft_wk; tea; eapply wfc_cons; tea; now eapply wft_wk.
    - intros ?? a b ρ'  wfΔ' ** ; cbn in *.
      replace (_[b .: ρ' >> tRel]) with (pos[ b .: (ρ' ∘w ρ) >> tRel]) by (now bsimpl).
      unshelve epose (posExt _ _ a b (ρ' ∘w ρ) wfΔ' Hd _ _ _ k'' Ho) ; irrelevance.
  Qed.
  
  Lemma wkΠ  {wl Γ Δ A l}
    (ρ : Δ ≤ Γ)
    (wfΔ : [|- Δ]< wl >)
    (ΠA : [Γ ||-Π< l > A]< wl >) :
      [Δ ||-Π< l > A⟨ρ⟩]< wl >.
  Proof.
    destruct ΠA; econstructor.
    4: now eapply wkPoly.
    1,3: rewrite wk_prod; now eapply redtywf_wk + now eapply convty_wk.
    now apply convty_wk.
  Defined.

  Lemma wkΣ {wl Γ Δ A l} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]< wl >) (ΣA : [Γ ||-Σ< l > A]< wl >) :
    [Δ ||-Σ< l > A⟨ρ⟩]< wl >.
  Proof.
    destruct ΣA; econstructor.
    4: now eapply wkPoly.
    1,3: rewrite wk_sig; now eapply redtywf_wk + now eapply convty_wk.
    now apply convty_wk.
  Defined.

  Lemma wkNat {wl Γ A Δ} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]< wl >) : [Γ ||-Nat A]< wl > -> [Δ ||-Nat A⟨ρ⟩]< wl >.
  Proof. 
    intros []; constructor.
    change tNat with tNat⟨ρ⟩.
    gen_typing. 
  Qed.

  Lemma wkBool {wl Γ A Δ} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]< wl >) : [Γ ||-Bool A]< wl > -> [Δ ||-Bool A⟨ρ⟩]< wl >.
  Proof. 
    intros []; constructor.
    change tBool with tBool⟨ρ⟩.
    gen_typing. 
  Qed.

  Lemma wkEmpty {wl Γ A Δ} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]< wl >) : [Γ ||-Empty A]< wl > -> [Δ ||-Empty A⟨ρ⟩]< wl >.
  Proof. 
    intros []; constructor.
    change tEmpty with tEmpty⟨ρ⟩.
    gen_typing. 
  Qed.

  Lemma wkId@{i j k l} {wl Γ l A Δ} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]< wl >) :
    IdRedTy@{i j k l} wl Γ l A -> IdRedTy@{i j k l} wl Δ l A⟨ρ⟩.
    (* [Γ ||-Id<l> A] -> [Δ ||-Id<l> A⟨ρ⟩]. *)
  Proof. 
    intros []; unshelve econstructor.
    6: erewrite wk_Id; now eapply redtywf_wk.
    3: rewrite wk_Id; gen_typing.
    - apply tyKripke ; auto.
      now apply wfLCon_le_id.
    - intros; rewrite wk_comp_ren_on; now apply tyKripke.
    - unshelve eapply (tyKripkeTm _ _ _ _ _ _ _ (idε _) (idε _)); [eapply wk_id| gen_typing| now rewrite wk_comp_runit| irrelevance].
    - unshelve eapply (tyKripkeTm _ _ _ _ _ _ _ (idε _) (idε _)) ; [eapply wk_id| gen_typing| now rewrite wk_comp_runit| irrelevance].
    (* could also employ reflexivity instead *)
    - unshelve eapply (tyKripkeTmEq _ _ _ _ _ _ _ (idε _) (idε _)); [eapply wk_id| gen_typing| now rewrite wk_comp_runit|irrelevance].
    - unshelve eapply (tyKripkeTmEq _ _ _ _ _ _ _ (idε _) (idε _)); [eapply wk_id| gen_typing| now rewrite wk_comp_runit|irrelevance].
    - apply perLRTmEq.
    - intros; irrelevance0.  
      1: now rewrite wk_comp_ren_on.
      cbn in *. unshelve eapply (tyKripkeEq _ _ k' k''); tea.
      3: irrelevance; now rewrite wk_comp_ren_on.
      bsimpl; setoid_rewrite H10; now bsimpl.
    - intros; irrelevance0.  
      1: now rewrite wk_comp_ren_on.
      unshelve eapply (tyKripkeTm _ _ k'); tea.
      3: irrelevance; now rewrite wk_comp_ren_on.
      bsimpl; setoid_rewrite H10; now bsimpl.
    - intros; irrelevance0.  
      1: now rewrite wk_comp_ren_on.
      unshelve eapply (tyKripkeTmEq _ _ k'); tea.
      3: irrelevance; now rewrite wk_comp_ren_on.
      bsimpl; setoid_rewrite H10; now bsimpl.
  Defined.
  
  Lemma wk@{i j k l} {wl Γ Δ A l} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]< wl >) :
    [LogRel@{i j k l} l | Γ ||- A]< wl > -> [LogRel@{i j k l} l | Δ ||- A⟨ρ⟩]< wl >.
  Proof.
    intros lrA. revert Δ ρ wfΔ . pattern l, wl, Γ, A, lrA.
    eapply LR_rect_TyUr@{i j k l l}; clear l wl Γ A lrA.
    - intros **. apply LRU_. now eapply wkU.
    - intros ????[ty]???. apply LRne_.
      exists (ty⟨ρ⟩); [| change U with U⟨ρ⟩] ;gen_typing.
    - intros ????? ihdom ihcod ???. apply LRPi'; eapply (wkΠ ρ wfΔ ΠA).
    - intros; eapply LRNat_; now eapply wkNat.
    - intros; eapply LRBool_; now eapply wkBool.
    - intros; eapply LREmpty_; now eapply wkEmpty.
    - intros ????? ihdom ihcod ???. apply LRSig'; eapply (wkΣ ρ wfΔ ΠA).
    - intros; apply LRId'; now eapply wkId.
  Defined.

  Corollary Wwk@{i j k l} {wl Γ Δ A l} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]< wl >) :
    WLogRel@{i j k l} l wl Γ A ->
    WLogRel@{i j k l} l wl Δ A⟨ρ⟩.
  Proof.
    intros [].
    exists WT ; intros.
    eapply wk.
    - eapply wfc_Ltrans ; eauto ; now eapply over_tree_le.
    - now eapply WRed.
  Defined.

  (* Sanity checks for Π and Σ: we do compute correctly with wk *)
  #[local]
  Lemma wkΠ_eq {wl Γ Δ A l} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]< wl >) (ΠA : [Γ ||-Π< l > A]< wl >) :
    wk ρ wfΔ (LRPi' ΠA) = LRPi' (wkΠ ρ wfΔ ΠA).
  Proof. reflexivity. Qed.
  
  #[local]
  Lemma wkΣ_eq {wl Γ Δ A l} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]< wl >) (ΠA : [Γ ||-Σ< l > A]< wl >) :
    wk ρ wfΔ (LRSig' ΠA) = LRSig' (wkΣ ρ wfΔ ΠA).
  Proof. reflexivity. Qed.
  
  Set Printing Primitive Projection Parameters.

  Lemma wkPolyEq {wl Γ l shp shp' pos pos' Δ}  (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]< wl >) (PA : PolyRed wl Γ l shp pos) : 
    PolyRedEq PA shp' pos' -> PolyRedEq (wkPoly ρ wfΔ PA) shp'⟨ρ⟩ pos'⟨wk_up shp' ρ⟩.
  Proof.
    intros []; unshelve econstructor.
    - intros ??? ρ' f wfΔ' ?; eapply DTree_fusion.
      + unshelve eapply posTree ; [ | | exact (ρ' ∘w ρ) |..] ; auto.
        irrelevance.
      + eapply (PolyRedPack.posTree PA (ρ' ∘w ρ) f wfΔ').
        irrelevance.
    - intros ? ρ' k' f wfΔ'; replace (_⟨_⟩) with (shp'⟨ρ' ∘w ρ⟩) by now bsimpl.
      pose (shpRed _ (ρ' ∘w ρ) _ f wfΔ'); irrelevance.
    - intros ??? ρ' f wfΔ' ha k'' Ho Ho' ; cbn in *.
      replace (_[_ .: ρ' >> tRel]) with (pos'[ a .: (ρ' ∘w ρ) >> tRel]) by now bsimpl.
      irrelevance0.
      2: unshelve eapply posRed.
      3,4: eassumption.
      + now bsimpl.
      + irrelevance.
      + eapply over_tree_fusion_r ; eassumption.
      + eapply over_tree_fusion_l ; eassumption.
  Qed.

Lemma wkEq@{i j k l} {wl Γ Δ A B l} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]< wl >) (lrA : [Γ ||-<l> A]< wl >) : 
    [LogRel@{i j k l} l | Γ ||- A ≅ B | lrA]< wl > ->
    [LogRel@{i j k l} l | Δ ||- A⟨ρ⟩ ≅ B⟨ρ⟩ | wk ρ wfΔ lrA]< wl >.
  Proof.
    revert B Δ ρ wfΔ. pattern l, wl, Γ, A, lrA.
    eapply LR_rect_TyUr; clear l wl Γ A lrA.
    - intros ??? ????? ? [] ; constructor; change U with U⟨ρ⟩; gen_typing.
    - intros * [ty].
      exists ty⟨ρ⟩.
      1: gen_typing.
      cbn ; change U with U⟨ρ⟩; eapply convneu_wk; assumption.
    - intros * ?? * []; rewrite wkΠ_eq ; eexists.
      4: now eapply wkPolyEq.
      + rewrite wk_prod;  gen_typing.
      + now eapply convty_wk.
      + rewrite wk_prod.
        replace (tProd _ _) with (ΠA.(outTy)⟨ρ⟩) by (cbn; now bsimpl).
        now eapply convty_wk.
    - intros * []; constructor.
      change tNat with tNat⟨ρ⟩; gen_typing.
    - intros * []; constructor.
      change tBool with tBool⟨ρ⟩; gen_typing.
    - intros * []; constructor.
      change tEmpty with tEmpty⟨ρ⟩; gen_typing.
    - intros * ?? * []; rewrite wkΣ_eq ; eexists.
      4: now eapply wkPolyEq.
      + rewrite wk_sig;  gen_typing.
      + now eapply convty_wk.
      + rewrite wk_sig.
        replace (tSig _ _) with (ΠA.(outTy)⟨ρ⟩) by (cbn; now bsimpl).
        now eapply convty_wk.
    - intros * _ _ * [] ; assert [|-Γ]< wl > by (escape; gen_typing); econstructor; cbn.
      1: erewrite wk_Id; now eapply redtywf_wk.
      1: unfold_id_outTy; cbn; rewrite 2!wk_Id; now eapply convty_wk.
      2,3: eapply (IA.(IdRedTy.tyKripkeTmEq) _ _ _ (idε _) (idε _)); [now rewrite wk_comp_runit| irrelevance].
      eapply (IA.(IdRedTy.tyKripkeEq) _ _ _ (idε _) (idε _)); [now rewrite wk_comp_runit| irrelevance].
      Unshelve. all: tea.
  Qed.

  Lemma WwkEq@{i j k l} {wl Γ Δ A B l} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]< wl >)
    (lrA : WLogRel@{i j k l} l wl Γ A) : 
    W[ Γ ||-< l > A ≅ B | lrA]< wl > ->
    W[ Δ ||-< l > A⟨ρ⟩ ≅ B⟨ρ⟩ | Wwk@{i j k l} ρ wfΔ lrA]< wl >.
  Proof.
    intros [].
    exists WTEq.
    intros.
    unshelve eapply wkEq.
    now eapply WRedEq.
  Qed.

  Lemma isLRFun_ren : forall wl Γ Δ t A l (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]< wl >) (ΠA : [Γ ||-Π< l > A]< wl >),
    isLRFun ΠA t -> isLRFun (wkΠ ρ wfΔ ΠA) t⟨ρ⟩.
  Proof.
    intros * [A' t' Htree Hdom Ht|]; [unshelve econstructor 1 | ] ; fold ren_term.
    - intros Ξ k' ? ρ' f * ha; cbn.
      eapply DTree_fusion.
      + eapply (Htree _ _ a (ρ' ∘w ρ) f Hd).
        irrelevance.
      + eapply (PolyRed.posTree ΠA (ρ' ∘w ρ) f Hd).
        irrelevance.
    - intros Ξ wl' ρ' f *; cbn.
      assert (eq : forall t, t⟨ρ' ∘w ρ⟩ = t⟨ρ⟩⟨ρ'⟩) by now bsimpl.
      irrelevance0 ; [apply eq| ].
      assert (eq' : forall t, t⟨ρ' ∘w ρ⟩ = (ren_term ρ t)⟨ρ'⟩) by now bsimpl.
      rewrite <- eq'.
      now unshelve eapply Hdom.
    - intros Ξ wl' a ρ' f wfΞ ha wl'' Ho Ho'; cbn in *.
      assert (eq : forall t, t⟨ρ' ∘w ρ⟩ = t⟨ρ⟩⟨ρ'⟩) by now bsimpl.
      unshelve eassert (Ht0 := Ht Ξ wl' a (ρ' ∘w ρ) f wfΞ _ wl'' (over_tree_fusion_r Ho') (over_tree_fusion_l Ho')).
      replace ((ren_term (upRen_term_term ρ) t')[a .: ρ' >> tRel]) with (t'[a .: (ρ' ∘w ρ) >> tRel]) by now bsimpl.
      irrelevance0; [|apply Ht0].
      now bsimpl.
    - constructor.
      change [Δ |- f⟨ρ⟩ ~ f⟨ρ⟩ : (tProd (PiRedTy.dom ΠA) (PiRedTy.cod ΠA))⟨ρ⟩]< wl >.
      now eapply convneu_wk.
  Qed.

  (* TODO: use program or equivalent to have only the first field non-opaque *)
  Lemma wkΠTerm {wl Γ Δ u A l} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]< wl >) (ΠA : [Γ ||-Π< l > A]< wl >) 
    (ΠA' := wkΠ ρ wfΔ ΠA) : 
    [Γ||-Π u : A | ΠA]< wl > -> 
    [Δ ||-Π u⟨ρ⟩ : A⟨ρ⟩ | ΠA' ]< wl >.
  Proof.
    intros [t].
    unshelve econstructor ; [exact (t⟨ρ⟩) | ..].
    all: try change (tProd _ _) with (ΠA.(outTy)⟨ρ⟩).
    - intros ?? a ρ' f ??.
      eapply DTree_fusion ; [apply (appTree _ _ a (ρ' ∘w ρ) f Hd) | eapply (PolyRed.posTree ΠA (ρ' ∘w ρ) f Hd)].
      all: irrelevance0 ; [ | eassumption] .
      all: subst ΠA'; bsimpl; try rewrite scons_comp'; reflexivity.
    - now eapply redtmwf_wk.
    - now apply convtm_wk.
    - now apply isLRFun_ren.
    - intros ? a wl' ρ' f ?? wl'' Ho Ho' ; cbn in *.
      replace ((t ⟨ρ⟩)⟨ ρ' ⟩) with (t⟨ρ' ∘w ρ⟩) by now bsimpl.
      irrelevance0.
      2: unshelve apply app ; [| | eassumption| subst ΠA'; irrelevance |..] ; auto. 
      + subst ΠA'; bsimpl; try rewrite scons_comp'; reflexivity.
      + now eapply over_tree_fusion_r.
      + now eapply over_tree_fusion_l.
    - intros ??? wl' ρ' f ??????? ; cbn in *.
      replace ((t ⟨ρ⟩)⟨ ρ' ⟩) with (t⟨ρ' ∘w ρ⟩) by now bsimpl.
      irrelevance0.
      2: unshelve apply eq; [| | eassumption|..] ; auto ; try (subst ΠA'; irrelevance).
      + subst ΠA'; bsimpl; try rewrite scons_comp'; reflexivity.
      + now eapply over_tree_fusion_r.
      + now eapply over_tree_fusion_l.
  Defined.


  Lemma wkNeNf {wl Γ Δ k A} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]< wl >) : 
    [Γ ||-NeNf k : A]< wl > -> [Δ ||-NeNf k⟨ρ⟩ : A⟨ρ⟩]< wl >.
  Proof.
    intros []; constructor. all: gen_typing.
  Qed.  


  Lemma isLRPair_ren : forall wl Γ Δ t A l (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]< wl >) (ΣA : [Γ ||-Σ< l > A]< wl >),
    isLRPair ΣA t -> isLRPair (wkΣ ρ wfΔ ΣA) t⟨ρ⟩.
  Proof.
    assert (eq : forall Γ Δ Ξ (ρ : Δ ≤ Γ) (ρ' : Ξ ≤ Δ) t, t⟨ρ' ∘w ρ⟩ = t⟨ρ⟩⟨ρ'⟩) by now bsimpl.
    intros * [A' B' a b Hdom codTree Hcod Hfst sndTree Hsnd|]; unshelve econstructor ; tea ; refold.
    - refold; intros Ξ wl' a' ρ' f wfΞ ha'.
      eapply DTree_fusion.
      + unshelve eapply (codTree Ξ wl' a' (ρ' ∘w ρ) f wfΞ _).
        irrelevance0 ; [symmetry | exact ha'].
        now apply eq.
      + unshelve eapply (PolyRed.posTree ΣA (ρ' ∘w ρ) f wfΞ).
        2: irrelevance0 ; [symmetry | exact ha'].
        now apply eq.
    - refold; intros Ξ wl' ρ' f wfΞ ; cbn.
      erewrite <- eq.
      irrelevance0; [|now unshelve apply Hfst].
      now bsimpl.
    - intros Ξ wl' ρ' f wfΞ.
      eapply DTree_fusion.
      + unshelve eapply (sndTree _ _ (ρ' ∘w ρ)) ; now eauto.
      + eapply (PolyRed.posTree ΣA (ρ' ∘w ρ) f wfΞ).
        now eapply Hfst.
    - intros Ξ wl' ρ' f wfΞ.
      irrelevance0; [apply eq|].
      rewrite <- eq.
      now unshelve apply Hdom.
    - intros Ξ wl' a' ρ' f wfΞ ha' wl'' Ho Ho'; cbn in *.
      unshelve eassert (Hcod0 := Hcod Ξ wl' a' (ρ' ∘w ρ) f wfΞ _ wl'' _ (over_tree_fusion_l Ho')).
      { exact (over_tree_fusion_r Ho'). }
      replace (B'⟨upRen_term_term ρ⟩[a' .: ρ' >> tRel]) with B'[a' .: (ρ' ∘w ρ) >> tRel] by now bsimpl.
      irrelevance0; [|apply Hcod0].
      now bsimpl.
    - refold; intros Ξ wl' ρ' f wfΞ wl'' Ho Ho' ; cbn in *.
      rewrite <- (eq _ _ _ ρ ρ' b).
      irrelevance0; [| unshelve apply (Hsnd _ _ _ f wfΞ)].
      + now bsimpl.
      + now eapply over_tree_fusion_r.
      + now eapply over_tree_fusion_l.
    - change [Δ |- p⟨ρ⟩ ~ p⟨ρ⟩ : (tSig (SigRedTy.dom ΣA) (SigRedTy.cod ΣA))⟨ρ⟩]< wl >.
      now eapply convneu_wk.
  Qed.

  Lemma wkΣTerm {wl Γ Δ u A l} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]< wl >) (ΠA : [Γ ||-Σ< l > A]< wl >) 
    (ΠA' := wkΣ ρ wfΔ ΠA) : 
    [Γ||-Σ u : A | ΠA]< wl > -> 
    [Δ ||-Σ u⟨ρ⟩ : A⟨ρ⟩ | ΠA' ]< wl >.
  Proof.
    intros [t]. 
    unshelve eexists (t⟨ρ⟩) _ _; try (cbn; rewrite wk_sig).
    - intros ?? ρ' f wfΔ'; rewrite wk_comp_ren_on; irrelevance0.
      2: now unshelve eapply fstRed.
      cbn; symmetry; apply wk_comp_ren_on.
    - intros ?? ρ' f wfΔ' ; eapply DTree_fusion.
      + now eapply (sndTree _ _ (ρ' ∘w ρ) f wfΔ') ; eauto.
      + eapply (PolyRed.posTree ΠA (ρ' ∘w ρ) f wfΔ').
        now eapply fstRed.
    - now eapply redtmwf_wk.
    - eapply convtm_wk; eassumption.
    - apply isLRPair_ren; assumption.
    - intros ? wl' ρ' f ? wl'' Ho Ho' ;  irrelevance0.
      2: rewrite wk_comp_ren_on; unshelve eapply sndRed ; [ | eassumption | eassumption |.. ].
      + rewrite <- wk_comp_ren_on; cbn; now rewrite <- wk_up_ren_subst.
      + now eapply over_tree_fusion_r.
      + now eapply over_tree_fusion_l.
  Defined.

  Lemma wkTerm {wl Γ Δ t A l} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]< wl >) (lrA : [Γ ||-<l> A]< wl >) : 
    [Γ ||-<l> t : A | lrA]< wl > -> [Δ ||-<l> t⟨ρ⟩ : A⟨ρ⟩ | wk ρ wfΔ lrA]< wl >.
  Proof.
    revert t Δ ρ wfΔ. pattern l, wl, Γ, A, lrA.
    eapply LR_rect_TyUr; clear l wl Γ A lrA.
    - intros ??????? ρ ? [te]; exists te⟨ρ⟩;  try change U with U⟨ρ⟩.
      + gen_typing.
      + apply isType_ren; assumption.
      + now apply convtm_wk.
      + apply RedTyRecBwd ; apply wk; [assumption|]; now apply (RedTyRecFwd h).
    - intros ??????? ρ ? [te]. exists te⟨ρ⟩; cbn.
      + now eapply redtmwf_wk.
      + apply convneu_wk; assumption.
    - intros; now apply wkΠTerm. 
    - intros ???? NA t ? ρ wfΔ; revert t; pose (NA' := wkNat ρ wfΔ NA).
      set (G := _); enough (h : G × (forall t, NatProp NA t -> NatProp NA' t⟨ρ⟩)) by apply h.
      subst G; apply NatRedInduction.
      + intros; econstructor; tea; change tNat with tNat⟨ρ⟩; gen_typing.
      + constructor.
      + now constructor.
      + intros; constructor. 
        change tNat with tNat⟨ρ⟩.
        now eapply wkNeNf.
    - intros ???? NA t ? ρ wfΔ; revert t; pose (NA' := wkBool ρ wfΔ NA).
      set (G := _); enough (h : G × (forall t, BoolProp NA t -> BoolProp NA' t⟨ρ⟩)) by apply h.
      subst G ; split.
      2:{ intros t Ht ; inversion Ht ; subst; econstructor.
          change tBool with tBool⟨ρ⟩.
          now eapply wkNeNf. }
      intros t Ht. induction Ht. econstructor.
      + change tBool with tBool⟨ρ⟩; gen_typing.
      + change tBool with tBool⟨ρ⟩; gen_typing.
      + destruct prop ; econstructor.
        change tBool with tBool⟨ρ⟩.
        now eapply wkNeNf.
    - intros ???? NA t ? ρ wfΔ; revert t; pose (NA' := wkEmpty ρ wfΔ NA).
      set (G := _); enough (h : G × (forall t, EmptyProp (k := wl) Γ t -> EmptyProp (k := wl) Δ t⟨ρ⟩)) by apply h.
      subst G.
      split.
      2:{ intros t Ht. inversion Ht. subst. econstructor.
          change tEmpty with tEmpty⟨ρ⟩.
          now eapply wkNeNf. }
      intros t Ht. induction Ht. econstructor.
      + change tEmpty with tEmpty⟨ρ⟩; gen_typing.
      + change tEmpty with tEmpty⟨ρ⟩; gen_typing.
      + destruct prop. econstructor.
        change tEmpty with tEmpty⟨ρ⟩.
        now eapply wkNeNf.
    - intros; now apply wkΣTerm. 
    - intros * _ _ * [??? prop]; econstructor; unfold_id_outTy; cbn; rewrite ?wk_Id.
      1: now eapply redtmwf_wk.
      1: now eapply convtm_wk.
      destruct prop.
      2: constructor; unfold_id_outTy; cbn; rewrite wk_Id; now eapply wkNeNf.
      assert [|-Γ]< wl > by (escape; gen_typing); constructor; cbn.
      1: now eapply wft_wk.
      1: now eapply ty_wk.
      2,3: eapply (IA.(IdRedTy.tyKripkeTmEq) _ _ _ (idε _) (idε _)); [now rewrite wk_comp_runit| irrelevance].
      eapply (IA.(IdRedTy.tyKripkeEq) _ _ _ (idε _) (idε _)); [now rewrite wk_comp_runit| irrelevance].
      Unshelve. all: tea.
  Qed.


  Lemma WwkTerm@{i j k l} {wl Γ Δ t A l} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]< wl >)
    (lrA : WLogRel@{i j k l} l wl Γ A) : 
    W[ Γ ||-< l > t : A | lrA]< wl > ->
    W[ Δ ||-< l > t⟨ρ⟩ : A⟨ρ⟩ | Wwk@{i j k l} ρ wfΔ lrA]< wl >.
  Proof.
    intros [].
    exists WTTm.
    intros.
    eapply wkTerm.
    now eapply WRedTm.
  Qed.
  
  Lemma wkUTerm {wl Γ Δ l A t} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]< wl >) (h : [Γ ||-U<l> A]< wl >) :
    [LogRelRec l| Γ ||-U t : A | h ]< wl > -> [LogRelRec l | Δ||-U t⟨ρ⟩ : A⟨ρ⟩ | wkU ρ wfΔ h]< wl >.
  Proof.
    intros [te]. exists te⟨ρ⟩; change U with U⟨ρ⟩.
    - gen_typing.
    - apply isType_ren; assumption.
    - now apply convtm_wk.
    - destruct l; [destruct (elim (URedTy.lt h))|cbn].
      eapply (wk (l:=zero)); eassumption.
  Defined.

  Lemma wkNeNfEq {wl Γ Δ k k' A} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]< wl >) : 
    [Γ ||-NeNf k ≅ k' : A]< wl > -> [Δ ||-NeNf k⟨ρ⟩ ≅ k'⟨ρ⟩ : A⟨ρ⟩]< wl >.
  Proof.
    intros []; constructor. gen_typing.
  Qed.  

  Lemma wkTermEq {wl Γ Δ t u A l} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]< wl >) (lrA : [Γ ||-<l> A]< wl >) : 
    [Γ ||-<l> t ≅ u : A | lrA]< wl > -> [Δ ||-<l> t⟨ρ⟩ ≅ u⟨ρ⟩: A⟨ρ⟩ | wk ρ wfΔ lrA]< wl >.
  Proof.
    revert t u Δ ρ wfΔ. pattern l, wl, Γ, A, lrA.
    eapply LR_rect_TyUr; clear l wl Γ A lrA.
    - intros ???????? ρ ? [rL rR].
      unshelve econstructor.
      + exact (wkUTerm ρ wfΔ h rL).
      + exact (wkUTerm ρ wfΔ h rR).
      + apply RedTyRecBwd; apply wk; [assumption|]; now apply (RedTyRecFwd h).
      + cbn. change U with U⟨ρ⟩. 
        now eapply convtm_wk.
      + apply RedTyRecBwd; apply wk; [assumption|]; now apply (RedTyRecFwd h).
      + apply TyEqRecBwd. eapply wkEq. now apply TyEqRecFwd.
    - intros ???????? ρ ? [tL tR].
      exists (tL⟨ρ⟩) (tR⟨ρ⟩); cbn.
      1,2: now eapply redtmwf_wk. 
      now eapply convneu_wk.
    - intros * ?? * []; rewrite wkΠ_eq. 
      unshelve econstructor; cbn; try rewrite wk_prod.
      1,2: now eapply wkΠTerm.
      + intros ? a ? ρ' * ? ; eapply DTree_fusion.
        * unshelve eapply eqTree ; try assumption.
          exact (ρ' ∘w ρ).
          now irrelevance.
        * eapply (PolyRed.posTree ΠA (ρ' ∘w ρ) f Hd).
          now irrelevance.
      + now eapply convtm_wk.
      + intros ? a ? ρ' * ?. 
        replace (_ ⟨ ρ' ⟩) with (PiRedTm.nf redL) ⟨ρ' ∘w ρ⟩ by now bsimpl.
        replace (_ ⟨ ρ' ⟩) with (PiRedTm.nf redR) ⟨ρ' ∘w ρ⟩ by now bsimpl.
        irrelevance0.  2: unshelve eapply eqApp; [| exact f |..]; try irrelevance ; auto. 
        * now rewrite <- wk_up_ren_subst.
        * now eapply over_tree_fusion_r.
        * now eapply over_tree_fusion_l.
    - intros ???? NA t u ? ρ wfΔ; revert t u; pose (NA' := wkNat ρ wfΔ NA).
      set (G := _); enough (h : G × (forall t u, NatPropEq NA t u -> NatPropEq NA' t⟨ρ⟩ u⟨ρ⟩)) by apply h.
      subst G; apply NatRedEqInduction.
      + intros; econstructor; tea; change tNat with tNat⟨ρ⟩; gen_typing.
      + constructor.
      + now constructor.
      + intros; constructor. 
        change tNat with tNat⟨ρ⟩.
        now eapply wkNeNfEq.
    - intros ???? NA t u ? ρ wfΔ Ht.
      induction Ht ; econstructor.
      + change tBool with tBool⟨ρ⟩; gen_typing.
      + change tBool with tBool⟨ρ⟩; gen_typing.
      + change tBool with tBool⟨ρ⟩; gen_typing.
      + inversion prop ; subst ; econstructor.
        change tBool with tBool⟨ρ⟩.
          now eapply wkNeNfEq.
    - intros ???? NA t u ? ρ wfΔ Ht.
      induction Ht ; econstructor.
      + change tEmpty with tEmpty⟨ρ⟩; gen_typing.
      + change tEmpty with tEmpty⟨ρ⟩; gen_typing.
      + change tEmpty with tEmpty⟨ρ⟩; gen_typing.
      + inversion prop ; subst ; econstructor.
        change tEmpty with tEmpty⟨ρ⟩.
        now eapply wkNeNfEq.
    - intros * ?? * []; rewrite wkΣ_eq. 
      unshelve econstructor; cbn; try rewrite wk_sig.
      1,2: now eapply wkΣTerm.
      + intros ? ? ρ' * ?? ; eapply DTree_fusion.
        * unshelve eapply eqTree ; try assumption.
          exact (ρ' ∘w ρ).
        * eapply (PolyRed.posTree ΠA (ρ' ∘w ρ) f Hd).
          eapply (redL.(SigRedTm.fstRed)).
      + now eapply convtm_wk.
      + intros; cbn; do 2 rewrite wk_comp_ren_on.
        irrelevance0. 2: now unshelve eapply eqFst.
        now rewrite wk_comp_ren_on.
      + intros; cbn; irrelevance0.
        2: do 2 rewrite wk_comp_ren_on; unshelve eapply (eqSnd _ _ _ f Hd).
        * rewrite wk_comp_ren_on; now rewrite <- wk_up_ren_subst.
        * now eapply over_tree_fusion_r.
        * now eapply over_tree_fusion_l.
    - intros * _ _ * [????? prop]; econstructor; unfold_id_outTy; cbn; rewrite ?wk_Id.
      1,2: now eapply redtmwf_wk.
      1: now eapply convtm_wk.
      destruct prop.
      2: constructor; unfold_id_outTy; cbn; rewrite wk_Id; now eapply wkNeNfEq.
      assert [|-Γ]< wl > by (escape; gen_typing); constructor; cbn.
      1,2: now eapply wft_wk.
      1,2: now eapply ty_wk.
      1,2:eapply (IA.(IdRedTy.tyKripkeEq) _ _ _ (idε _) (idε _)); [now rewrite wk_comp_runit| irrelevance].
      all: eapply (IA.(IdRedTy.tyKripkeTmEq) _ _ _ (idε _) (idε _)); [now rewrite wk_comp_runit| irrelevance].
      Unshelve. all: tea.
  Qed.
End Weakenings.


Section Red_Ltrans.
  Context `{GenericTypingProperties}.
  
Lemma Id_Ltrans@{h i j k l} (l : TypeLevel) (wl : wfLCon) (Γ : context) (A : term)
  (IA : IdRedTy@{i j k l} wl Γ l A)
  (ih1 : forall wl' : wfLCon,
      wl' ≤ε wl -> [LogRel@{i j k l} l | Γ ||- IdRedTy.ty@{i j k l} IA ]< wl' >)
  (ih2 : forall (Δ : context) (wl' : wfLCon) (ρ : Δ ≤ Γ),
      wl' ≤ε wl -> [ |-[ ta ] Δ ]< wl' > ->
      forall wl'' : wfLCon,
        wl'' ≤ε wl' ->
        [LogRel@{i j k l} l | Δ ||- (IdRedTy.ty@{i j k l} IA)⟨ρ⟩ ]< wl'' >)
  (wl' : wfLCon)
  (f : wl' ≤ε wl)
  (Hg : [ |-[ ta ] Γ ]< wl >) : IdRedTy@{i j k l} wl' Γ l A.
Proof.
  unshelve econstructor.
  6: econstructor ; [eapply wft_Ltrans, (IdRedTy.red IA).(tyr_wf_r _ _ _ _) ; eauto |
                      eapply redty_Ltrans ; eauto].
  3: now eapply (IdRedTy.red IA).(tyr_wf_red _ _ _ _).
  3: eapply convty_Ltrans ; eauto ; now eapply (IdRedTy.eq IA).
  + now eapply ih1.
  + intros * f' Hd ; eapply ih2 ; [ | eassumption | now eapply wfLCon_le_id].
    now eapply wfLCon_le_trans.
  + irrelevance0 ; [ now eapply (wk_id_ren_on Γ (IdRedTy.ty IA)) | ].
    destruct (wk_id_ren_on Γ  (IdRedTy.lhs IA)). 
    eapply (IdRedTy.tyKripkeTm IA wk_id _ _ (wfLCon_le_id _) f Hg (wfc_Ltrans f Hg)).
    * now bsimpl.
    * irrelevance0 ; [symmetry ; now eapply (wk_id_ren_on Γ (IdRedTy.ty IA)) | ].
      now eapply (IdRedTy.lhsRed).
  + irrelevance0 ; [ now eapply (wk_id_ren_on Γ (IdRedTy.ty IA)) | ].
    destruct (wk_id_ren_on Γ  (IdRedTy.rhs IA)).
    eapply (IdRedTy.tyKripkeTm IA wk_id _ _ (wfLCon_le_id _) f Hg (wfc_Ltrans f Hg)).
    * now bsimpl.
    * irrelevance0 ; [symmetry ; now eapply (wk_id_ren_on Γ (IdRedTy.ty IA)) | ].
      now eapply (IdRedTy.rhsRed).
  + irrelevance0 ; [ now eapply (wk_id_ren_on Γ (IdRedTy.ty IA)) | ].
    destruct (wk_id_ren_on Γ  (IdRedTy.lhs IA)).
    eapply (IdRedTy.tyKripkeTmEq IA wk_id _ _ (wfLCon_le_id _) f Hg (wfc_Ltrans f Hg)).
    * now bsimpl.
    * irrelevance0 ; [symmetry ; now eapply (wk_id_ren_on Γ (IdRedTy.ty IA)) | ].
      now eapply (IdRedTy.lhsRedRefl).
  + irrelevance0 ; [ now eapply (wk_id_ren_on Γ (IdRedTy.ty IA)) | ].
    destruct (wk_id_ren_on Γ  (IdRedTy.rhs IA)).
    eapply (IdRedTy.tyKripkeTmEq IA wk_id _ _ (wfLCon_le_id _) f Hg (wfc_Ltrans f Hg)).
    * now bsimpl.
    * irrelevance0 ; [symmetry ; now eapply (wk_id_ren_on Γ (IdRedTy.ty IA)) | ].
      now eapply (IdRedTy.rhsRedRefl).
  + econstructor.
    * intros ??? ; eapply (LREqTermSymConv); [eassumption | ].
      now eapply reflLRTyEq.
    * intros ????? ; eapply (transEqTerm@{h i j k l}) ; eassumption.
  + intros ?? wl'' wl''' ??? f' f'' ??? Heq Hyp.
    irrelevance0 ; [reflexivity | ].
    eapply (IdRedTy.tyKripkeEq IA _ _ _ (f' •ε f) f'' wfΔ wfΞ _ Heq).
    irrelevance0 ; [ reflexivity | eassumption].
  + intros ?? wl'' wl''' ??? f' f'' ??? Heq Hyp.
    irrelevance0 ; [reflexivity | ].
    eapply (IdRedTy.tyKripkeTm IA _ _ _ (f' •ε f) f'' wfΔ wfΞ _ Heq).
    irrelevance0 ; [ reflexivity | eassumption].
  + intros ?? wl'' wl''' ??? f' f'' ???? Heq Hyp.
    irrelevance0 ; [reflexivity | ].
    eapply (IdRedTy.tyKripkeTmEq IA _ _ _ (f' •ε f) f'' wfΔ wfΞ _ _ Heq).
    irrelevance0 ; [ reflexivity | eassumption].
Defined.

  Lemma Ltrans@{h i j k l} {wl Γ wl' A l} :
    (wl' ≤ε wl) ->
    [LogRel@{i j k l} l | Γ ||- A]< wl > ->
    [LogRel@{i j k l} l | Γ ||- A]< wl' >.
  Proof.
    intros f lrA. revert wl' f. pattern l, wl, Γ, A, lrA.
    eapply LR_rect_TyUr@{i j k l l}; clear l wl Γ A lrA.
    - intros * [??? []] ??. apply LRU_.
      econstructor ; eauto ; [now eapply wfc_Ltrans | econstructor ].
      + now eapply wft_Ltrans.
      + now eapply redty_Ltrans.
    - intros ????[ty[]]??. apply LRne_ ; econstructor ; [econstructor | ].
      + now eapply wft_Ltrans.
      + now eapply redty_Ltrans.
      + now eapply convneu_Ltrans.
    - intros ???? [] ihdom ihcod wl' f ; cbn in *.
      apply LRPi' ; econstructor ; [destruct red ; econstructor |..].
      + now eapply wft_Ltrans.
      + now eapply redty_Ltrans.
      + now eapply convty_Ltrans.
      + now eapply convty_Ltrans.
      + unshelve econstructor.
        4,5: destruct polyRed ; now eapply wft_Ltrans.
        * intros * f' Hd.
          eapply (PolyRed.shpRed polyRed) ; [eapply wfLCon_le_trans | ] ; eauto.
        * intros ???? f' Hd ha ; cbn in *.
          eapply (PolyRed.posTree polyRed) ; eauto.
        * intros ???? f' ??? Hover ; cbn in *.
          eapply (PolyRed.posRed polyRed) ; eassumption.
        * intros ???? f' ????? Hover Hover' ; cbn in *.
          eapply (PolyRed.posExt polyRed) ; eassumption.
    - intros ????? wl' f.
      eapply LRNat_ ; econstructor.
      eapply redtywf_Ltrans ; eauto.
      now eapply NA.(NatRedTy.red).
    - intros ????? wl' f.
      eapply LRBool_ ; econstructor.
      eapply redtywf_Ltrans ; eauto.
      now eapply NA.(BoolRedTy.red).
    - intros ????? wl' f.
      eapply LREmpty_ ; econstructor.
      eapply redtywf_Ltrans ; eauto.
      now eapply NA.(EmptyRedTy.red).
    - intros ???? [] ihdom ihcod wl' f ; cbn in *.
      apply (LRSig'@{i j k l}) ; econstructor ; [destruct red ; econstructor |..].
      + now eapply wft_Ltrans.
      + now eapply redty_Ltrans.
      + now eapply convty_Ltrans.
      + now eapply convty_Ltrans.
      + unshelve econstructor.
        4,5: destruct polyRed ; now eapply wft_Ltrans.
        * intros * f' Hd.
          eapply (PolyRed.shpRed polyRed) ; [eapply wfLCon_le_trans | ] ; eauto.
        * intros ???? f' Hd ha ; cbn in *.
          eapply (PolyRed.posTree polyRed) ; eauto.
        * intros ???? f' ??? Hover ; cbn in *.
          eapply (PolyRed.posRed polyRed) ; eassumption.
        * intros ???? f' ????? Hover Hover' ; cbn in *.
          eapply (PolyRed.posExt polyRed) ; eassumption.
    - intros ????? ih1 ih2 wl' f. 
      apply (LRId'@{i j k l}).
      eapply (Id_Ltrans@{h i j k l}) ; eauto.
      now eapply (wfc_convty (IdRedTy.eq IA)).
  Defined.

  
Lemma Eq_Ltrans@{h i j k l} {wl Γ wl' A B l} (f : wl' ≤ε wl) (lrA : [Γ ||-<l> A]< wl >) : 
    [LogRel@{i j k l} l | Γ ||- A ≅ B | lrA]< wl > ->
    [LogRel@{i j k l} l | Γ ||- A ≅ B | Ltrans@{h i j k l} f lrA]< wl' >.
Proof.
  revert B wl' f. pattern l, wl, Γ, A, lrA.
  eapply LR_rect_TyUr@{i j k l l}; clear l wl Γ A lrA.
  - intros ???? [??? []] ???[] ; cbn in *.
    constructor ; constructor.
    + now eapply wft_Ltrans.
    + destruct red ; now eapply redty_Ltrans.
  - intros ???? [?[]] ???[?[]] ; cbn in *.
    econstructor ; [econstructor | ].
    + now eapply wft_Ltrans.
    + now eapply redty_Ltrans.
    + now eapply convneu_Ltrans.
  - intros ???? [] ihdom ihcod B wl' f []; cbn in *.
    econstructor ; [destruct red0 ; econstructor |..].
    + now eapply wft_Ltrans.
    + now eapply redty_Ltrans.
    + now eapply convty_Ltrans.
    + now eapply convty_Ltrans.
    + unshelve econstructor ; cbn in *.
      * intros * ? ; now eapply (PolyRedEq.posTree polyRed0).
      * intros * ; now eapply (PolyRedEq.shpRed polyRed0).
      * cbn ; intros * Ho' ; now eapply (PolyRedEq.posRed polyRed0).
  - intros ???? [[]] B wl' f [[]] ; cbn in *.
    econstructor ; econstructor.
    + now eapply wft_Ltrans.
    + now eapply redty_Ltrans.
  - intros ???? [[]] B wl' f [[]] ; cbn in *.
    econstructor ; econstructor.
    + now eapply wft_Ltrans.
    + now eapply redty_Ltrans.
  - intros ???? [[]] B wl' f [[]] ; cbn in *.
    econstructor ; econstructor.
    + now eapply wft_Ltrans.
    + now eapply redty_Ltrans.
  - intros ???? [] ihdom ihcod B wl' f [] ; cbn in *.
    econstructor ; [destruct red0 ; econstructor | ..].
    + now eapply wft_Ltrans.
    + now eapply redty_Ltrans.
    + now eapply convty_Ltrans.
    + now eapply convty_Ltrans.
    + unshelve econstructor ; cbn.
      * intros * ? ; now eapply (PolyRedEq.posTree polyRed0).
      * intros * ; now eapply (PolyRedEq.shpRed polyRed0).
      * cbn ; intros * Ho' ; now eapply (PolyRedEq.posRed polyRed0).
  - intros ????? ih1 ih2 ????.
    assert (Hg:= (wfc_convty (IdRedTy.eq IA))).
    eapply (@Build_IdRedTyEq _ _ _ _ _ _ wl' Γ A _ B) ; cbn.
    + unshelve econstructor.
      * now eapply wft_Ltrans, (IdRedTyEq.red X).(tyr_wf_r _ _ _ _).
      * now eapply redty_Ltrans, (IdRedTyEq.red X).(tyr_wf_red _ _ _ _).
    + eapply convty_Ltrans ; [ eassumption | ].
      eapply (IdRedTyEq.eq X). 
    + eapply ih1.
      now eapply (IdRedTyEq.tyRed X).
    + irrelevance0 ; [ now eapply (wk_id_ren_on Γ (IdRedTy.ty IA)) | ].
      destruct (wk_id_ren_on Γ  (IdRedTy.lhs IA)).
      destruct (wk_id_ren_on Γ  (IdRedTyEq.lhs X)).
      eapply (IdRedTy.tyKripkeTmEq IA wk_id _ _ (wfLCon_le_id _) f Hg (wfc_Ltrans f Hg)).
      * now bsimpl.
      * irrelevance0 ; [ symmetry ; now eapply (wk_id_ren_on Γ (IdRedTy.ty IA)) | ].
        exact (IdRedTyEq.lhsRed X).
    + irrelevance0 ; [ now eapply (wk_id_ren_on Γ (IdRedTy.ty IA)) | ].
      destruct (wk_id_ren_on Γ  (IdRedTy.rhs IA)).
      destruct (wk_id_ren_on Γ  (IdRedTyEq.rhs X)).
      eapply (IdRedTy.tyKripkeTmEq IA wk_id _ _ (wfLCon_le_id _) f Hg (wfc_Ltrans f Hg)).
      * now bsimpl.
      * irrelevance0 ; [ symmetry ; now eapply (wk_id_ren_on Γ (IdRedTy.ty IA)) | ].
        exact (IdRedTyEq.rhsRed X).
Qed.


Lemma isLRFun_Ltrans : forall wl wl' Γ t A l (f : wl' ≤ε wl) (ΠA : [Γ ||-Π< l > A]< wl >)
                              (ΠA' : [Γ ||-Π< l > A]< wl' >),
    isLRFun ΠA t -> isLRFun ΠA' t.
Proof.
  intros * f * Hyp.
  unshelve epose (Heq := redtywf_det _ _ (redtywf_Ltrans f ΠA.(ParamRedTyPack.red)) ΠA'.(ParamRedTyPack.red)).
  1,2: now econstructor.
  inversion Heq.
  induction Hyp as [?? funTree e r | t Heqt].
  - unshelve econstructor.
    + intros Δ wl'' a ρ f' Hd ha ; cbn.
      eapply DTree_fusion.
      * unshelve eapply funTree.
        6: irrelevance0 ; [ | exact ha] ; now f_equal.
        2: assumption.
        now eapply wfLCon_le_trans.
      * unshelve eapply (PolyRedPack.posTree ΠA).
        5: eassumption.
        4: irrelevance0 ; [ | exact ha] ; now f_equal.
        now eapply wfLCon_le_trans.
    + intros Δ wl'' ρ f' Hd ; cbn.
      irrelevance0 ; [ | unshelve eapply e] ; [now f_equal | ..].
      2: assumption.
      now eapply wfLCon_le_trans.
    + intros Δ wl'' a ρ f' Hd ha wl''' Ho Ho'.
      irrelevance0 ; [ | unshelve eapply r].
      now f_equal.
      3: eassumption.
      now eapply wfLCon_le_trans.
      cbn in *.
      3: now eapply over_tree_fusion_l.
      now eapply over_tree_fusion_r.
  - econstructor 2.
    cbn in *.
    rewrite <- H11, <- H12.
    now eapply convneu_Ltrans.
Qed.

Lemma isLRPair_Ltrans : forall wl wl' Γ t A l (f : wl' ≤ε wl) (ΣA : [Γ ||-Σ< l > A]< wl >)
                              (ΣA' : [Γ ||-Σ< l > A]< wl' >),
    isLRPair ΣA t -> isLRPair ΣA' t.
Proof.
  intros * f * Hyp.
  unshelve epose (Heq := redtywf_det _ _ (redtywf_Ltrans f ΣA.(ParamRedTyPack.red)) ΣA'.(ParamRedTyPack.red)).
  1,2: now econstructor.
  inversion Heq.
  induction Hyp as [????? fstTree ?? sndTree | t Heqt].
  - unshelve econstructor.
    + intros Δ wl'' a' ρ f' Hd ha ; cbn.
      eapply DTree_fusion.
      * unshelve eapply fstTree.
        6: irrelevance0 ; [ | exact ha] ; now f_equal.
        2: assumption.
        now eapply wfLCon_le_trans.
      * unshelve eapply (PolyRedPack.posTree ΣA).
        5: eassumption.
        4: irrelevance0 ; [ | exact ha] ; now f_equal.
        now eapply wfLCon_le_trans.
    + intros Δ wl'' ρ f' Hd ; cbn.
      irrelevance0 ; [ | unshelve eapply rfst] ; [now f_equal | ..].
      2: assumption.
      now eapply wfLCon_le_trans.
    + intros Δ wl'' ρ f' Hd.
      eapply DTree_fusion.
      * eapply sndTree.
        1,3: eassumption.
        now eapply wfLCon_le_trans.
      * unshelve  eapply (PolyRed.posTree ΣA).
        6: now unshelve eapply rfst.
        2,4: eassumption.
        now eapply wfLCon_le_trans.
    + intros Δ wl'' ρ f' Hd.
      irrelevance0 ; [ | unshelve eapply rdom ; eauto].
      now f_equal.
      now eapply wfLCon_le_trans.
    + intros Δ wl'' a' ρ f' Hd ha wl''' Ho Ho' ; cbn in *.
      irrelevance0 ; [ | unshelve eapply rcod].
      1: now f_equal.
      3: eassumption.
      * now eapply wfLCon_le_trans.
      * irrelevance0 ; [ | exact ha] ; now f_equal.
      * cbn in * ; now eapply over_tree_fusion_r.
      * cbn in * ; now eapply over_tree_fusion_l.
    + intros Δ wl'' ρ f' Hd wl''' Ho Ho' ; cbn in *.
      irrelevance0 ; [ | unshelve eapply rsnd].
      1: now f_equal.
      3: eassumption.
      * now eapply wfLCon_le_trans.
      * cbn in * ; now eapply over_tree_fusion_r.
      * cbn in * ; now eapply over_tree_fusion_l.
  - econstructor 2.
    cbn in *.
    rewrite <- H11, <- H12.
    now eapply convneu_Ltrans.
Qed.

Lemma NatTm_Ltrans (l : TypeLevel) (wl : wfLCon) (Γ : context) (A : term)
  (NA : [Γ ||-Nat A ]< wl >) (t : term) (wl' : wfLCon) (f : wl' ≤ε wl) (NA' : [Γ ||-Nat A ]< wl' >) :
  [LRNat_ l NA | Γ ||- t : A ]< wl > -> [ (LRNat_ l NA') | Γ ||- t : A ]< wl' >.
Proof.
  revert t.
  set (G := _); enough (h : G × (forall t, NatProp NA t -> NatProp NA' t)) by apply h.
  subst G; apply NatRedInduction.
  - intros t nf Hred Heq Hprop Hprop'.
    econstructor ; [now eapply redtmwf_Ltrans | | ].
    + now eapply convtm_Ltrans.
    + assumption.
  - now econstructor.
  - intros n Hn Hn' ; now econstructor.
  - intros ; econstructor.
    destruct r ; econstructor.
    + now eapply ty_Ltrans.
    + now eapply convneu_Ltrans.
Qed.

Lemma IdTm_Ltrans (l : TypeLevel) (wl wl' : wfLCon) (Γ : context) (A : term) (f : wl' ≤ε wl)
  (IA : [Γ ||-Id< l > A ]< wl >) (IA' : [Γ ||-Id< l > A ]< wl' >)
  (ih1 : forall (t : term),
      [IdRedTy.tyRed IA | Γ ||- t : IdRedTy.ty IA ]< wl > ->
      [IdRedTy.tyRed IA' | Γ ||- t : IdRedTy.ty IA' ]< wl' >)
  (ih2 : forall (Δ : context) (ρ : Δ ≤ Γ) (wfΔ : [ |-[ ta ] Δ ]< wl' >)
                (t : term) (wl'' : wfLCon) (f' : wl'' ≤ε wl'),
      [IdRedTy.tyKripke IA ρ f wfΔ | Δ ||- t : (IdRedTy.ty IA)⟨ρ⟩ ]< wl' > ->
      [IdRedTy.tyKripke IA' ρ f' (wfc_Ltrans f' wfΔ) | Δ ||- t : (IdRedTy.ty IA')⟨ρ⟩ ]< wl'' >) :
      forall (t : term),
        [LRId' IA | Γ ||- t : A ]< wl > -> [LRId' IA' | Γ ||- t : A ]< wl' >.
Proof.
  intros t Ht.
  unshelve epose (Heq := redtywf_det _ _ (redtywf_Ltrans f (IdRedTy.red IA))
                           (IdRedTy.red IA')).
  1,2 : now econstructor.
  inversion Heq.
  assert (Hg:= (wfc_convty (IdRedTy.eq IA))).
  econstructor ; cbn.
  - cbv in H11,H12,H13 ; cbv. 
    rewrite <- H11, <- H12, <- H13.
    now eapply redtmwf_Ltrans ; [ | eapply (IdRedTm.red Ht)].
  - cbv in H11,H12,H13 ; cbv. 
    rewrite <- H11, <- H12, <- H13.
    now eapply convtm_Ltrans ; [ | eapply (IdRedTm.eq Ht)].
  - destruct (IdRedTm.prop Ht).
    + econstructor.
      * now eapply wft_Ltrans.
      * now eapply ty_Ltrans.
      * irrelevance0 ; [ | unshelve eapply Eq_Ltrans].
        5: eassumption.
        all: assumption.
      * assert (Help : IdRedTyPack.lhs (IdRedTy.toPack IA') = IdRedTyPack.lhs (IdRedTy.toPack IA)).
        { now eauto. }
        rewrite Help.
        irrelevance0.
        2:{ erewrite <- (wk_id_ren_on Γ (IdRedTyPack.lhs (IdRedTy.toPack IA))).
            erewrite <- wk_id_ren_on.
            eapply (IdRedTy.tyKripkeTmEq IA wk_id wk_id _ (wfLCon_le_id _) f Hg (wfc_Ltrans f Hg)).
            * now bsimpl.
            * irrelevance0 ; [rewrite wk_id_ren_on ; reflexivity | ].
              eassumption.
        }
        rewrite H11 ; bsimpl.
        reflexivity.
      * assert (Help : IdRedTyPack.rhs (IdRedTy.toPack IA') = IdRedTyPack.rhs (IdRedTy.toPack IA)).
        { now eauto. }
        rewrite Help.
        irrelevance0.
        2:{ erewrite <- (wk_id_ren_on Γ (IdRedTyPack.rhs (IdRedTy.toPack IA))).
            erewrite <- wk_id_ren_on.
            eapply (IdRedTy.tyKripkeTmEq IA wk_id wk_id _ (wfLCon_le_id _) f Hg (wfc_Ltrans f Hg)).
            * now bsimpl.
            * irrelevance0 ; [rewrite wk_id_ren_on ; reflexivity | ].
              eassumption.
        }
        rewrite H11 ; bsimpl.
        reflexivity.
    + econstructor.
      destruct r ; econstructor.
      * eapply ty_Ltrans ; [eassumption | ].
        assert (Help : IdRedTyPack.outTy (IdRedTy.toPack IA') = IdRedTyPack.outTy (IdRedTy.toPack IA)) by eauto.
        now rewrite Help.
      * eapply convneu_Ltrans ; [eassumption | ].
        assert (Help : IdRedTyPack.outTy (IdRedTy.toPack IA') = IdRedTyPack.outTy (IdRedTy.toPack IA)) by eauto.
        now rewrite Help.
Qed.

Lemma ΠTm_Ltrans (l : TypeLevel) (wl wl' : wfLCon) (Γ : context) (f : wl' ≤ε wl) (A : term)
  (ΠA : [Γ ||-Π< l > A ]< wl >)
  (ΠA' : [Γ ||-Π< l > A ]< wl' >)
  (ihdom : forall (Δ : context) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ ]< wl' >) (t : term)
                  (wl'' : wfLCon) (f' : wl'' ≤ε wl'),
      [PolyRed.shpRed ΠA ρ f h | Δ ||- t : (ParamRedTy.dom ΠA)⟨ρ⟩ ]< wl' > ->
      [Ltrans f' (PolyRed.shpRed ΠA ρ f h) | Δ ||- t : (ParamRedTy.dom ΠA)⟨ρ⟩ ]< wl'' >)
  (ihcod : forall (Δ : context) (a : term) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ ]< wl' >)
                  (ha : [PolyRed.shpRed ΠA ρ f h | Δ ||- a : (ParamRedTy.dom ΠA)⟨ρ⟩ ]< wl' >)
                  (wl'' : wfLCon) (Ho : over_tree wl' wl'' (PolyRed.posTree ΠA ρ f h ha))
                  (t : term) (wl''' : wfLCon) (f'' : wl''' ≤ε wl''),
      [PolyRed.posRed ΠA ρ f h ha Ho | Δ  ||- t : (ParamRedTy.cod ΠA)[a .: ρ >> tRel] ]< wl'' > ->
      [Ltrans f'' (PolyRed.posRed ΠA ρ f h ha Ho) | Δ  ||- t : (ParamRedTy.cod ΠA)[a .: ρ >> tRel] ]< wl''' >) :
  forall (t : term),
    [Γ ||-Π t : A | ΠA ]< wl > ->  [Γ ||-Π t : A | ΠA' ]< wl' >.
Proof.
  intros t [].
  unshelve econstructor ; [ | | eapply redtmwf_Ltrans ; eauto |..].
  1: exact nf.
  1:{ cbn in * ; intros.
      eapply DTree_fusion.
      * unshelve eapply appTree.
        4: eapply wfLCon_le_trans.
        3-6: eassumption.
        2: irrelevance0 ; [ | eassumption ].
        f_equal.
        unshelve epose (Heq := redtywf_det _ _ (redtywf_Ltrans f ΠA.(ParamRedTyPack.red)) ΠA'.(ParamRedTyPack.red)) ; [now econstructor | now econstructor | ].
        now inversion Heq.
    * eapply (PolyRed.posTree ΠA ρ (f0 •ε f) Hd).
      irrelevance0 ; [ | eassumption].
      f_equal.
      unshelve epose (Heq := redtywf_det _ _ (redtywf_Ltrans f ΠA.(ParamRedTyPack.red)) ΠA'.(ParamRedTyPack.red)) ; [now econstructor | now econstructor | ].
      now inversion Heq.
  }
  all: unshelve epose (Heq := redtywf_det _ _ (redtywf_Ltrans f ΠA.(ParamRedTyPack.red)) ΠA'.(ParamRedTyPack.red)) ; [now econstructor | now econstructor | ].
  all: inversion Heq.
  2: eapply convtm_Ltrans ; [eauto | now rewrite <- Heq].
  2: eapply isLRFun_Ltrans ; eauto.
  1: now rewrite <- Heq.
  + cbn in * ; intros. 
    irrelevance0 ; [ | unshelve eapply app].
    6: now eapply over_tree_fusion_r.
    * now f_equal.
    * now eapply over_tree_fusion_l.
  + cbn in * ; intros.
    irrelevance0 ; [ | unshelve eapply eq].
    9: now eapply over_tree_fusion_l.
    2: now eapply over_tree_fusion_r.
    1: now f_equal.
    1,2: irrelevance0 ; [ | eassumption] ; now f_equal.
Defined.

Lemma ΣTm_Ltrans (l : TypeLevel) (wl wl' : wfLCon) (Γ : context) (f : wl' ≤ε wl) (A : term)
  (ΣA : [Γ ||-Σ< l > A ]< wl >)
  (ΣA' : [Γ ||-Σ< l > A ]< wl' >)
  (ihdom : forall (Δ : context) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ ]< wl' >) (t : term)
                  (wl'' : wfLCon) (f' : wl'' ≤ε wl'),
      [PolyRed.shpRed ΣA ρ f h | Δ ||- t : (ParamRedTy.dom ΣA)⟨ρ⟩ ]< wl' > ->
      [Ltrans f' (PolyRed.shpRed ΣA ρ f h) | Δ ||- t : (ParamRedTy.dom ΣA)⟨ρ⟩ ]< wl'' >)
  (ihcod : forall (Δ : context) (a : term) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ ]< wl' >)
                  (ha : [PolyRed.shpRed ΣA ρ f h | Δ ||- a : (ParamRedTy.dom ΣA)⟨ρ⟩ ]< wl' >)
                  (wl'' : wfLCon) (Ho : over_tree wl' wl'' (PolyRed.posTree ΣA ρ f h ha))
                  (t : term) (wl''' : wfLCon) (f'' : wl''' ≤ε wl''),
      [PolyRed.posRed ΣA ρ f h ha Ho | Δ  ||- t : (ParamRedTy.cod ΣA)[a .: ρ >> tRel] ]< wl'' > ->
      [Ltrans f'' (PolyRed.posRed ΣA ρ f h ha Ho) | Δ  ||- t : (ParamRedTy.cod ΣA)[a .: ρ >> tRel] ]< wl''' >) :
  forall (t : term),
    [Γ ||-Σ t : A | ΣA ]< wl > ->  [Γ ||-Σ t : A | ΣA' ]< wl' >.
Proof.
  intros t [].
  unshelve econstructor.
  4: eapply redtmwf_Ltrans ; eauto.
  1: exact nf.
  2:{ cbn in * ; intros.
      eapply DTree_fusion.
      * unshelve eapply sndTree.
        3: eapply wfLCon_le_trans.
        2-5: eassumption.
      * eapply (PolyRed.posTree ΣA ρ (f0 •ε f) Hd).
        eapply fstRed.
  }
  all: unshelve epose (Heq := redtywf_det _ _ (redtywf_Ltrans f ΣA.(ParamRedTyPack.red)) ΣA'.(ParamRedTyPack.red)) ; [now econstructor | now econstructor | ].
  all: inversion Heq.
  3: eapply convtm_Ltrans ; [eauto | ].
  2,3: cbv ; cbv in Heq ; now rewrite <- Heq.
  2: eapply isLRPair_Ltrans ; now eauto.
  + cbn in * ; intros.
    irrelevance0 ; [ | unshelve eapply fstRed].
    * now f_equal.
    * now eapply wfLCon_le_trans.
    * assumption.
  + cbn in * ; intros.
    irrelevance0 ; [ | unshelve eapply sndRed].
    4: eassumption.
    * now f_equal.
    * now eapply wfLCon_le_trans.
    * now eapply over_tree_fusion_r.
    * now eapply over_tree_fusion_l.
Defined.
  
Lemma Tm_Ltrans@{h i j k l} {wl Γ wl' t A l} (f : wl' ≤ε wl) (lrA : [Γ ||-<l> A]< wl >) : 
    [LogRel@{i j k l} l | Γ ||- t : A | lrA]< wl > ->
    [LogRel@{i j k l} l | Γ ||- t : A | Ltrans@{h i j k l} f lrA]< wl' >.
Proof.
  revert t wl' f. pattern l, wl, Γ, A, lrA.
  eapply LR_rect_TyUr@{i j k l l}; clear l wl Γ A lrA.
  - intros ???? [??? []] ???[?[]].
    econstructor ; [ econstructor | eassumption |.. ].
    + now eapply ty_Ltrans.
    + now eapply redtm_Ltrans.
    + now eapply convtm_Ltrans.
    + apply RedTyRecBwd ; apply RedTyRecFwd in rel.
      now eapply Ltrans ; eauto.
  - intros ???? [?[]] ???[?[]] ; cbn in *.
    econstructor ; [econstructor ; cbn | ].
    + now eapply ty_Ltrans.
    + now eapply redtm_Ltrans.
    + now eapply convneu_Ltrans.
  - intros ???? [] ihdom ihcod t wl' f ?.
    cbn in *.
    unshelve eapply ΠTm_Ltrans ; intros.
    6: eassumption.
    1: eassumption.
    + now eapply ihdom.
    + now eapply ihcod. 
  - intros ; irrelevance0 ; [ reflexivity | unshelve eapply NatTm_Ltrans].
    5: eassumption.
    2: assumption.
    destruct NA ; econstructor ; now eapply redtywf_Ltrans.
  - intros ???? NA t ? f ; revert t ; cbn.
    intros t Ht. induction Ht. econstructor.
    + now eapply redtmwf_Ltrans.
    + now eapply convtm_Ltrans.
    + destruct prop as [ | | m Hne] ; econstructor.
      destruct Hne ; econstructor.
      * now eapply ty_Ltrans.
      * now eapply convneu_Ltrans.
  - intros ???? NA t ? f Ht ; cbn.
    induction Ht ; econstructor.
    + now eapply redtmwf_Ltrans.
    + now eapply convtm_Ltrans.
    + destruct prop as [m Hne] ; econstructor.
      destruct Hne ; econstructor.
      * now eapply ty_Ltrans.
      * now eapply convneu_Ltrans.
  - intros ????? ihdom ihcod t wl' f ?; cbn in *.
    eapply ΣTm_Ltrans.
    + intros ; eauto.
    + intros ; eauto.
    + assumption.
      Unshelve. assumption.
  - intros * ih1 ih2 *.
    unshelve eapply IdTm_Ltrans.
    eassumption.
    + intros ; eapply ih1 ; auto.
    + intros ; eapply ih2.
      rewrite <- (wk_id_ren_on Δ t0).
      eapply (IdRedTy.tyKripkeTm IA ρ).
      * now bsimpl.
      * eassumption.
Qed.

Lemma TmEq_Ltrans@{h i j k l} {wl Γ wl' t u A l} (f : wl' ≤ε wl) (lrA : [Γ ||-<l> A]< wl >) : 
    [LogRel@{i j k l} l | Γ ||- t ≅ u : A | lrA]< wl > ->
    [LogRel@{i j k l} l | Γ ||- t ≅ u : A | Ltrans@{h i j k l} f lrA]< wl' >.
Proof.
  revert t u wl' f. pattern l, wl, Γ, A, lrA.
  eapply LR_rect_TyUr@{i j k l l}; clear l wl Γ A lrA.
  - intros ???? [??? []] ???? [].
    unshelve econstructor.
    + destruct redL.
      econstructor.
      * now eapply redtmwf_Ltrans.
      * assumption.
      * now eapply convtm_Ltrans.
      * apply RedTyRecBwd ; clear relEq ; apply RedTyRecFwd in relL.
        now eapply Ltrans.
    + destruct redR.
      econstructor.
      * now eapply redtmwf_Ltrans.
      * assumption.
      * now eapply convtm_Ltrans.
      * apply RedTyRecBwd ; clear relEq ; apply RedTyRecFwd in relR.
        now eapply Ltrans.
    + apply RedTyRecBwd ; clear relEq ; apply RedTyRecFwd in relL.
      now eapply Ltrans.
    + cbn in *.
      now eapply convtm_Ltrans.
    + apply RedTyRecBwd ; clear relEq ; apply RedTyRecFwd in relR.
      now eapply Ltrans.
    + eapply TyEqRecBwd, Eq_Ltrans ; cbn.
      now eapply TyEqRecFwd.
  - intros ???? [?[]] ???? [] ; cbn in *.
    econstructor.
    + now eapply redtmwf_Ltrans.
    + now eapply redtmwf_Ltrans.
    + now eapply convneu_Ltrans.
  - intros ????? ihdom ihcod t u wl' f [].
    cbn.
    unshelve econstructor ; cbn in *.
    + unshelve eapply ΠTm_Ltrans ; [ | eassumption | ..].
      1,4: eassumption.
      * intros ; now eapply Tm_Ltrans.
      * intros ; now eapply Tm_Ltrans.
    + unshelve eapply ΠTm_Ltrans ; [ | eassumption | ..].
      1,4: eassumption.
      * intros ; now eapply Tm_Ltrans.
      * intros ; now eapply Tm_Ltrans.
    + intros ; eapply eqTree.
      eassumption.
    + intros ; cbn in *.
      now eapply convtm_Ltrans.
    + intros ; cbn in *.
      eapply eqApp.
      assumption.
  - intros * ; revert t u.
    set (NA' := {| NatRedTy.red := redtywf_Ltrans f (NatRedTy.red NA) |}).
    set (G := _); enough (h : G × (forall t u, NatPropEq NA t u -> NatPropEq NA' t u)) by apply h.
    subst G; apply NatRedEqInduction.
    + intros t u nt nu Hredt Hredu Heq Hprop Hprop'.
      econstructor.
      1,2: now eapply redtmwf_Ltrans.
      * now eapply convtm_Ltrans.
      * assumption.
    + now econstructor.
    + intros n Hn Hn' ; now econstructor.
    + intros ; econstructor.
      destruct r ; econstructor.
      now eapply convneu_Ltrans.
  - intros ???? NA t ? wl' f Heq.
    induction Heq ; cbn. econstructor.
    1,2: now eapply redtmwf_Ltrans.
    + now eapply convtm_Ltrans.
    + destruct prop as [ | | m Hne] ; econstructor.
      econstructor.
      now destruct r ; eapply convneu_Ltrans.
  - intros ???? NA t u wl' f Heq ; cbn.
    induction Heq ; econstructor.
    1,2: now eapply redtmwf_Ltrans.
    + now eapply convtm_Ltrans.
    + destruct prop as [m Hne] ; econstructor ; econstructor.
      now destruct r ; eapply convneu_Ltrans.
  - cbn ; intros ????? ihdom ihcod t u wl' f []; cbn in *.
    unshelve econstructor ; cbn.
    + unshelve eapply ΣTm_Ltrans.
      2,3,6: eassumption.
      * intros.
        irrelevance0 ; [ | unshelve eapply Tm_Ltrans].
        5: eassumption.
        1,2: now auto.
      * intros.
        irrelevance0 ; [ | unshelve eapply Tm_Ltrans].
        5: eassumption.
        1,2: now trivial.
    + unshelve eapply ΣTm_Ltrans.
      2,3,6: eassumption.
      * intros.
        irrelevance0 ; [ | unshelve eapply Tm_Ltrans].
        5: eassumption.
        1,2: now auto.
      * intros.
        irrelevance0 ; [ | unshelve eapply Tm_Ltrans].
        5: eassumption.
        1,2: now trivial.
    + intros ; eapply DTree_fusion.
      * eapply eqTree.
        1,3: eassumption.
        now eapply wfLCon_le_trans.
      * eapply (PolyRed.posTree ΠA ρ (f0 •ε f) Hd).
        now eapply (SigRedTm.fstRed redL). 
    + cbn ; now eapply convtm_Ltrans.
    + cbn ; intros ; now unshelve eapply eqFst.
    + cbn in * ; intros.
      irrelevance0 ; [ reflexivity | unshelve eapply eqSnd].
      3: eassumption.
      * now eapply wfLCon_le_trans.
      * now eapply over_tree_fusion_r.
      * now eapply over_tree_fusion_l.
  - intros ????? ih1 ih2 ???? [].
    unshelve econstructor ; cbn.
    3,4: now eapply redtmwf_Ltrans.
    1: now eapply convtm_Ltrans.
    destruct prop.
    + econstructor.
      1,2: now eapply wft_Ltrans.
      1,2: now eapply ty_Ltrans.
      1,2:irrelevance0 ; [ | now eapply Eq_Ltrans] ; reflexivity.
      all: now eapply ih1.
    + econstructor.
      destruct r ; econstructor.
      now eapply convneu_Ltrans.
      Unshelve. all: assumption.
Qed.
  
End Red_Ltrans.
