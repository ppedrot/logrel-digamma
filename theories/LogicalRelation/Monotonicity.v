From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Notations Utils BasicAst LContexts Context NormalForms UntypedValues Weakening GenericTyping Monad LogicalRelation DeclarativeInstance.
From LogRel.LogicalRelation Require Import Induction Irrelevance Reflexivity Transitivity Escape Weakening.

Set Universe Polymorphism.

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
        5,6: destruct polyRed ; now eapply wft_Ltrans.
        * intros * f' Hd.
          eapply (PolyRed.shpRed polyRed) ; [eapply wfLCon_le_trans | ] ; eauto.
        * intros ???? f' Hd ha ; cbn in *.
          eapply (PolyRed.posTree polyRed) ; eauto.
        * intros ???? f' ??? Hover ; cbn in *.
          eapply (PolyRed.posRed polyRed) ; eassumption.
        * intros ???? f' ????? ; cbn in *.
          eapply (PolyRed.posExtTree polyRed (a := a) (b := b)) ; eassumption.
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
        5,6: destruct polyRed ; now eapply wft_Ltrans.
        * intros * f' Hd.
          eapply (PolyRed.shpRed polyRed) ; [eapply wfLCon_le_trans | ] ; eassumption.
        * intros ???? f' Hd ha ; cbn in *.
          eapply (PolyRed.posTree polyRed) ; eassumption.
        * intros ???? f' ??? Hover ; cbn in *.
          eapply (PolyRed.posRed polyRed) ; eassumption.
        * intros ???? f' ????? ; cbn in *.
          eapply (PolyRed.posExtTree polyRed (a := a)) ; eassumption.
        * intros ???? f' ????? Hover Hover' ; cbn in *.
          eapply (PolyRed.posExt polyRed) ; eassumption.
    - intros ????? ih1 ih2 wl' f. 
      apply (LRId'@{i j k l}).
      eapply (Id_Ltrans@{h i j k l}) ; eauto.
      now eapply (wfc_convty (IdRedTy.eq IA)).
  Defined.

  Lemma WLtrans@{h i j k l} {wl Γ wl' A l} :
    (wl' ≤ε wl) ->
    WLogRel@{i j k l} l wl Γ A  ->
    WLogRel@{i j k l} l wl' Γ A.
  Proof.
    intros f HA ; unshelve econstructor.
    - eapply DTree_Ltrans ; [eassumption | ].
      exact (WT _ HA).
    - intros wl'' Hover.
      eapply (WRed _ HA).
      now eapply over_tree_Ltrans.
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

Lemma Eq_Ltrans'@{h i j k l} {wl Γ wl' A B l} (f : wl' ≤ε wl) lrA lrA' : 
    [LogRel@{i j k l} l | Γ ||- A ≅ B | lrA]< wl > ->
    [LogRel@{i j k l} l | Γ ||- A ≅ B | lrA']< wl' >.
Proof.
  intros Heq ; irrelevance0 ; [reflexivity | ].
  now eapply (Eq_Ltrans f).
Qed.

Lemma WEq_Ltrans@{h i j k l} {wl Γ wl' A B l}
    (f : wl' ≤ε wl) (lrA : W[Γ ||-<l> A]< wl >) :
    WLogRelEq@{i j k l} l wl Γ A B lrA ->
    WLogRelEq@{i j k l} l wl' Γ A B (WLtrans@{h i j k l} f lrA).
  Proof.
    intros Heq ; unshelve econstructor.
    - eapply DTree_Ltrans ; [eassumption | ].
      exact (WTEq _ Heq).
    - intros wl'' Hover Hover'.
      eapply (WRedEq _ Heq).
      now eapply over_tree_Ltrans.
  Defined.      

  
Lemma WEq_Ltrans'@{h i j k l} {wl Γ wl' A B l}
    (f : wl' ≤ε wl) lrA lrA' :
    WLogRelEq@{i j k l} l wl Γ A B lrA ->
    WLogRelEq@{i j k l} l wl' Γ A B lrA'.
Proof.
  intros Heq ; eapply WLRTyEqIrrelevant' ; [reflexivity | ].
  now eapply (WEq_Ltrans f).
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
  unshelve econstructor ; [ | | | eapply redtmwf_Ltrans ; eauto |..].
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
  1:{ cbn in * ; intros.
      eapply DTree_fusion.
      * unshelve eapply (eqTree _ a b).
        3: now eapply wfLCon_le_trans.
        2,3: eassumption.
        all: irrelevance0 ; [ | eassumption ] ; f_equal.
        all: unshelve epose (Heq := redtywf_det _ _ (redtywf_Ltrans f ΠA.(ParamRedTyPack.red)) ΠA'.(ParamRedTyPack.red)) ;
          [now econstructor | now econstructor | ].
        all: now inversion Heq.
      * eapply (PolyRed.posExtTree ΠA (a:= a) (b := b) ρ (f0 •ε f) Hd).
        all: irrelevance0 ; [ f_equal | eassumption].
        all: unshelve epose (Heq := redtywf_det _ _ (redtywf_Ltrans f ΠA.(ParamRedTyPack.red)) ΠA'.(ParamRedTyPack.red)) ;
          [now econstructor | now econstructor | ].
        all: now inversion Heq.
  }
  all: unshelve epose (Heq := redtywf_det _ _ (redtywf_Ltrans f ΠA.(ParamRedTyPack.red)) ΠA'.(ParamRedTyPack.red)) ;
    [now econstructor | now econstructor | ].
  all: inversion Heq.
  2: eapply convtm_Ltrans ; [now eauto | now rewrite <- Heq].
  2: eapply isLRFun_Ltrans ; now eauto.
  1: now rewrite <- Heq.
  + cbn in * ; intros. 
    irrelevance0 ; [ | unshelve eapply app].
    6: now eapply over_tree_fusion_r.
    * now f_equal.
    * now eapply over_tree_fusion_l.
  + cbn in * ; intros.
    irrelevance0 ; [ | unshelve eapply eq].
    11: eapply over_tree_fusion_l ; exact Hoeq.
    * now f_equal.
    * now eapply over_tree_fusion_r.
    * now eapply over_tree_fusion_l.
    * eapply over_tree_fusion_l ; exact Hob.
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

Lemma Tm_Ltrans'@{h i j k l} {wl Γ wl' t A l} (f : wl' ≤ε wl) lrA lrA' : 
    [LogRel@{i j k l} l | Γ ||- t : A | lrA]< wl > ->
    [LogRel@{i j k l} l | Γ ||- t : A | lrA']< wl' >.
Proof.
  intros Hyp ; irrelevance0 ; [reflexivity | unshelve eapply Tm_Ltrans].
  2-4: eassumption.
Qed.

Lemma WTm_Ltrans@{h i j k l} {wl Γ wl' A t l}
    (f : wl' ≤ε wl) (lrA : W[Γ ||-<l> A]< wl >) :
    WLogRelTm@{i j k l} l wl Γ t A lrA ->
    WLogRelTm@{i j k l} l wl' Γ t A (WLtrans@{h i j k l} f lrA).
  Proof.
    intros Ht ; unshelve econstructor.
    - eapply DTree_Ltrans ; [eassumption | ].
      exact (WTTm _ Ht).
    - intros wl'' Hover Hover'.
      eapply (WRedTm _ Ht).
      now eapply over_tree_Ltrans.
  Defined.

  Lemma WTm_Ltrans'@{h i j k l} {wl Γ wl' A t l}
    (f : wl' ≤ε wl) lrA lrA' :
    WLogRelTm@{i j k l} l wl Γ t A lrA ->
    WLogRelTm@{i j k l} l wl' Γ t A lrA'.
  Proof.
    intros Ht.
    eapply WLRTmRedIrrelevant' ; [reflexivity | ].
    now eapply (WTm_Ltrans f).
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

Lemma TmEq_Ltrans'@{h i j k l} {wl Γ wl' t u A l} (f : wl' ≤ε wl) lrA lrA': 
    [LogRel@{i j k l} l | Γ ||- t ≅ u : A | lrA]< wl > ->
    [LogRel@{i j k l} l | Γ ||- t ≅ u : A | lrA']< wl' >.
Proof.
  intros Ht ; irrelevance0 ; [reflexivity | ].
  now eapply (TmEq_Ltrans f).
Qed.

Lemma WTmEq_Ltrans@{h i j k l} {wl Γ wl' t u A l}
    (f : wl' ≤ε wl) (lrA : W[Γ ||-<l> A]< wl >) :
    WLogRelTmEq@{i j k l} l wl Γ t u A lrA ->
    WLogRelTmEq@{i j k l} l wl' Γ t u A (WLtrans@{h i j k l} f lrA).
  Proof.
    intros Htu ; unshelve econstructor.
    - eapply DTree_Ltrans ; [eassumption | ].
      exact (WTTmEq _ Htu).
    - intros wl'' Hover Hover'.
      eapply (WRedTmEq _ Htu).
      now eapply over_tree_Ltrans.
  Defined.

  Lemma WTmEq_Ltrans'@{h i j k l} {wl Γ wl' t u A l}
    (f : wl' ≤ε wl) lrA lrA' :
    WLogRelTmEq@{i j k l} l wl Γ t u A lrA ->
    WLogRelTmEq@{i j k l} l wl' Γ t u A lrA'.
  Proof.
    intros Ht.
    eapply WLRTmEqIrrelevant' ; [reflexivity | ].
    now eapply (WTmEq_Ltrans f).
  Qed.
  
End Red_Ltrans.

Section Injection.
  Context `{GenericTypingProperties}.

Definition LogtoW@{h i j k l} {l : TypeLevel} {wl Γ A}
  (RA : [ LogRel@{i j k l} l | Γ ||- A ]< wl >) :
  WLogRel@{i j k l} l wl Γ A.
Proof.
  exists (leaf wl).
  intros wl' f ; exact (Ltrans@{h i j k l} f RA).
Defined.

Definition TmLogtoW@{h i j k l} {l : TypeLevel} {wl Γ t A}
  (RA : [ LogRel@{i j k l} l | Γ ||- A ]< wl >)
  (Rt : [ LogRel@{i j k l} l | Γ ||- t : A | RA ]< wl >) :
  WLogRelTm@{i j k l} l wl Γ t A (LogtoW@{h i j k l} RA).
Proof.
  exists (leaf wl).
  intros wl' f f' ; now eapply Tm_Ltrans.
Defined.

Definition TmLogtoW'@{h i j k l} {l : TypeLevel} {wl Γ t A}
  {RA : [ LogRel@{i j k l} l | Γ ||- A ]< wl >}
  (Rt : [ LogRel@{i j k l} l | Γ ||- t : A | RA ]< wl >)
  (WRA : WLogRel@{i j k l} l wl Γ A) :
  WLogRelTm@{i j k l} l wl Γ t A WRA.
Proof.
  Wirrelevance0 ; [reflexivity | now eapply TmLogtoW@{h i j k l}].
Defined.

Definition EqLogtoW@{h i j k l} {l : TypeLevel} {wl Γ A B}
  (RA : [ LogRel@{i j k l} l | Γ ||- A ]< wl >)
  (Rt : [ LogRel@{i j k l} l | Γ ||- A ≅ B | RA ]< wl >) :
  WLogRelEq@{i j k l} l wl Γ A B (LogtoW@{h i j k l} RA).
Proof.
  exists (leaf wl).
  intros wl' f f' ; now eapply Eq_Ltrans.
Defined.

Definition EqLogtoW'@{h i j k l} {l : TypeLevel} {wl Γ A B}
  {RA : [ LogRel@{i j k l} l | Γ ||- A ]< wl >}
  (Rt : [ LogRel@{i j k l} l | Γ ||- A ≅ B | RA ]< wl >)
  (WRA : WLogRel@{i j k l} l wl Γ A) :
  WLogRelEq@{i j k l} l wl Γ A B WRA.
Proof.
  Wirrelevance0 ; [reflexivity | now eapply EqLogtoW@{h i j k l}].
Defined.


Definition TmEqLogtoW@{h i j k l} {l : TypeLevel} {wl Γ t u A}
  (RA : [ LogRel@{i j k l} l | Γ ||- A ]< wl >)
  (Rt : [ LogRel@{i j k l} l | Γ ||- t ≅ u : A | RA ]< wl >) :
  WLogRelTmEq@{i j k l} l wl Γ t u A (LogtoW@{h i j k l} RA).
Proof.
  exists (leaf wl).
  intros wl' f f' ; now eapply TmEq_Ltrans.
Defined.

Definition TmEqLogtoW'@{h i j k l} {l : TypeLevel} {wl Γ t u A}
  {RA : [ LogRel@{i j k l} l | Γ ||- A ]< wl >}
  (Rt : [ LogRel@{i j k l} l | Γ ||- t ≅ u : A | RA ]< wl >)
  (WRA : WLogRel@{i j k l} l wl Γ A) :
  WLogRelTmEq@{i j k l} l wl Γ t u A WRA.
Proof.
  Wirrelevance0 ; [reflexivity | now eapply TmEqLogtoW@{h i j k l}].
Defined.


End Injection.

Section Weakening_Ltrans.
  Context `{GenericTypingProperties}.

  Lemma wk_Ltrans@{h i j k l} {wl Γ Δ wl' A l}
    (ρ : Δ ≤ Γ) 
    (f : wl' ≤ε wl)
    (wfΔ : [|- Δ]< wl' >) :
    [LogRel@{i j k l} l | Γ ||- A]< wl > ->
    [LogRel@{i j k l} l | Δ ||- A⟨ρ⟩]< wl' >.
  Proof.
    intros ; now eapply (wk@{i j k l}), (Ltrans@{h i j k l}).
  Defined.

  Lemma Wwk_Ltrans@{h i j k l} {wl Γ Δ wl' A l}
    (ρ : Δ ≤ Γ) 
    (f : wl' ≤ε wl)
    (wfΔ : [|- Δ]< wl' >) :
    WLogRel@{i j k l} l wl Γ A ->
    WLogRel@{i j k l} l wl' Δ A⟨ρ⟩.
  Proof.
    intros ; now eapply (Wwk@{i j k l}), (WLtrans@{h i j k l}).
  Defined.

  Lemma wkEq_Ltrans@{h i j k l} {wl Γ Δ wl' A B l} (ρ : Δ ≤ Γ) (f : wl' ≤ε wl)
    (wfΔ : [|- Δ]< wl' >)
    (lrA : [Γ ||-<l> A]< wl >) : 
    [LogRel@{i j k l} l | Γ ||- A ≅ B | lrA]< wl > ->
    [LogRel@{i j k l} l | Δ ||- A⟨ρ⟩ ≅ B⟨ρ⟩ | wk_Ltrans@{h i j k l} ρ f wfΔ lrA]< wl' >.
  Proof.
    intros ; now eapply (wkEq@{i j k l}), (Eq_Ltrans@{h i j k l}).
  Defined.

  Lemma WwkEq_Ltrans@{h i j k l} {wl Γ Δ wl' A B l}
    (ρ : Δ ≤ Γ) 
    (f : wl' ≤ε wl)
    (wfΔ : [|- Δ]< wl' >)
    (lrA : W[Γ ||-<l> A]< wl >) :
    WLogRelEq@{i j k l} l wl Γ A B lrA ->
    WLogRelEq@{i j k l} l wl' Δ A⟨ρ⟩ B⟨ρ⟩ (Wwk_Ltrans@{h i j k l} ρ f wfΔ lrA).
  Proof.
    intros ; now eapply (WwkEq@{i j k l}), (WEq_Ltrans@{h i j k l}).
  Defined.

  Lemma wkTm_Ltrans@{h i j k l} {wl Γ Δ wl' t A l} (ρ : Δ ≤ Γ) (f : wl' ≤ε wl)
    (wfΔ : [|- Δ]< wl' >)
    (lrA : [Γ ||-<l> A]< wl >) : 
    [LogRel@{i j k l} l | Γ ||- t : A | lrA]< wl > ->
    [LogRel@{i j k l} l | Δ ||- t⟨ρ⟩ : A⟨ρ⟩ | wk_Ltrans@{h i j k l} ρ f wfΔ lrA]< wl' >.
  Proof.
    intros ; now eapply (wkTerm@{i j k l}), (Tm_Ltrans@{h i j k l}).
  Defined.
    
  Lemma WwkTm_Ltrans@{h i j k l} {wl Γ Δ wl' t A l}
    (ρ : Δ ≤ Γ) 
    (f : wl' ≤ε wl)
    (wfΔ : [|- Δ]< wl' >)
    (lrA : W[Γ ||-<l> A]< wl >) :
    WLogRelTm@{i j k l} l wl Γ t A lrA ->
    WLogRelTm@{i j k l} l wl' Δ t⟨ρ⟩ A⟨ρ⟩ (Wwk_Ltrans@{h i j k l} ρ f wfΔ lrA).
  Proof.
    intros ; now eapply (WwkTerm@{i j k l}), (WTm_Ltrans@{h i j k l}).
  Defined.

  Lemma wkTmEq_Ltrans@{h i j k l} {wl Γ Δ wl' t u A l} (ρ : Δ ≤ Γ) (f : wl' ≤ε wl)
    (wfΔ : [|- Δ]< wl' >)
    (lrA : [Γ ||-<l> A]< wl >) : 
    [LogRel@{i j k l} l | Γ ||- t ≅ u : A | lrA]< wl > ->
    [LogRel@{i j k l} l | Δ ||- t⟨ρ⟩ ≅ u⟨ρ⟩ : A⟨ρ⟩ | wk_Ltrans@{h i j k l} ρ f wfΔ lrA]< wl' >.
  Proof.
    intros ; now eapply (wkTermEq@{i j k l}), (TmEq_Ltrans@{h i j k l}).
  Defined.
    
  Lemma WwkEqTm_Ltrans@{h i j k l} {wl Γ Δ wl' t u A l}
    (ρ : Δ ≤ Γ) 
    (f : wl' ≤ε wl)
    (wfΔ : [|- Δ]< wl' >)
    (lrA : W[Γ ||-<l> A]< wl >) :
    WLogRelTmEq@{i j k l} l wl Γ t u A lrA ->
    WLogRelTmEq@{i j k l} l wl' Δ t⟨ρ⟩ u⟨ρ⟩ A⟨ρ⟩ (Wwk_Ltrans@{h i j k l} ρ f wfΔ lrA).
  Proof.
    intros ; now eapply (WwkTermEq@{i j k l}), (WTmEq_Ltrans@{h i j k l}).
  Defined.

  
End Weakening_Ltrans.
