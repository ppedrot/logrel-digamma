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

