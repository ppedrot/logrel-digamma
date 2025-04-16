From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Notations Utils BasicAst LContexts Context NormalForms Weakening GenericTyping Monad LogicalRelation.
From LogRel.LogicalRelation Require Import Induction Irrelevance Weakening Neutral Escape Reflexivity NormalRed Reduction Monotonicity Split Transitivity Universe.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Section IdRed.
  Context `{GenericTypingProperties}.

  Lemma mkIdRedTy {wl Γ l A} :
    forall (ty lhs rhs  : term)
      (tyRed : [Γ ||-<l> ty]< wl >),
      [Γ |- A :⤳*: tId ty lhs rhs]< wl > ->
      [tyRed | Γ ||- lhs : _]< wl > ->
      [tyRed | Γ ||- rhs : _]< wl > ->
      [Γ ||-Id<l> A]< wl >.
  Proof.
    intros; unshelve econstructor ; cycle 3; tea.
    1: intros; eapply wk ; [assumption | now eapply Ltrans ].
    2,3: now eapply reflLRTmEq.
    2: now apply perLRTmEq.
    - eapply  convty_Id. 
      1: eapply escapeEq; now eapply reflLRTyEq.
      1,2: eapply escapeEqTerm; now eapply reflLRTmEq.
    - cbn; intros.
      irrelevance0; [| eapply wkEq, Eq_Ltrans ; eassumption].
      bsimpl; rewrite H11; now bsimpl.
      Unshelve. all:tea.
    - cbn; intros; irrelevance0; [| now eapply wkTerm, Tm_Ltrans ; eassumption].
      bsimpl; rewrite H11; now bsimpl.
      Unshelve. all:tea.
    - cbn; intros; irrelevance0; [| now eapply wkTermEq, TmEq_Ltrans ; eassumption].
      bsimpl; rewrite H11; now bsimpl.
      Unshelve. all:tea.
  Defined.

  Lemma IdRed0 {wl Γ l A t u} (RA : [Γ ||-<l> A]< wl >) :
      [RA | Γ ||- t : _]< wl > ->
      [RA | Γ ||- u : _]< wl > ->
      [Γ ||-Id<l> tId A t u]< wl >.
  Proof.
    intros; eapply mkIdRedTy.
    1: eapply redtywf_refl; escape; gen_typing.
    all: tea.
  Defined.
  
  Lemma IdRed {wl Γ l A t u} (RA : [Γ ||-<l> A]< wl >) :
      [RA | Γ ||- t : _]< wl > ->
      [RA | Γ ||- u : _]< wl > ->
      [Γ ||-<l> tId A t u]< wl >.
  Proof. intros; apply LRId'; now eapply IdRed0. Defined.

  Lemma WIdRed {wl Γ l A t u} (RA : W[Γ ||-<l> A]< wl >) :
      W[Γ ||-< l > t : _ | RA]< wl > ->
      W[Γ ||-< l > u : _ | RA]< wl > ->
      W[Γ ||-<l> tId A t u]< wl >.
  Proof.
    intros Ht Hu ; econstructor ; intros wl' Ho.
    unshelve eapply IdRed.
    - eapply RA, over_tree_fusion_l ; exact Ho.
    - eapply Ht, over_tree_fusion_l, over_tree_fusion_r ; exact Ho.
    - eapply Hu, over_tree_fusion_r, over_tree_fusion_r ; exact Ho.
  Defined.
  
  Lemma IdRedTy_inv {wl Γ l A t u} (RIA : [Γ ||-Id<l> tId A t u]< wl >) :
    [× A = RIA.(IdRedTy.ty), t = RIA.(IdRedTy.lhs) & u = RIA.(IdRedTy.rhs)].
  Proof.
    pose proof (redtywf_whnf RIA.(IdRedTy.red) whnf_tId) as e; injection e; now split.
  Qed.

  Lemma IdCongRed {wl Γ l A A' t t' u u'} 
    (RA : [Γ ||-<l> A]< wl >)
    (RIA : [Γ ||-<l> tId A t u]< wl >) :
    [Γ |- tId A' t' u']< wl > ->
    [RA | _ ||- _ ≅ A']< wl > ->
    [RA | _ ||- t ≅ t' : _]< wl > ->
    [RA | _ ||- u ≅ u' : _]< wl > ->
    [RIA | _ ||- _ ≅ tId A' t' u']< wl >.
  Proof.
    intros.
    enough [LRId' (invLRId RIA) | _ ||- _ ≅ tId A' t' u']< wl > by irrelevance.
    pose proof (IdRedTy_inv (invLRId (RIA))) as [ety elhs erhs].
    econstructor.
    + now eapply redtywf_refl.
    + unfold_id_outTy; rewrite <- ety, <- elhs, <- erhs; eapply convty_Id; now escape.
    + irrelevance.
    + cbn; rewrite <- elhs; irrelevance.
    + cbn; rewrite <- erhs; irrelevance.
  Qed.

  Lemma WIdCongRed {wl Γ l A A' t t' u u'} 
    (RA : W[Γ ||-<l> A]< wl >)
    (RIA : W[Γ ||-<l> tId A t u]< wl >) :
    [Γ |- tId A' t' u']< wl > ->
    W[ _ ||-< l > _ ≅ A' | RA]< wl > ->
    W[ _ ||-< l > t ≅ t' : _ | RA]< wl > ->
    W[ _ ||-< l > u ≅ u' : _ | RA]< wl > ->
    W[ _ ||-< l > _ ≅ tId A' t' u' | RIA]< wl >.
  Proof.
    intros Hty HA Ht Hu ; unshelve econstructor.
    1: do 2 eapply DTree_fusion ; shelve.
    intros wl' Ho Ho'.
    pose (f := over_tree_le Ho).
    unshelve eapply IdCongRed.
    - eapply RA, over_tree_fusion_l, over_tree_fusion_l ; exact Ho'.
    - now eapply wft_Ltrans.
    - eapply HA, over_tree_fusion_r, over_tree_fusion_l ; exact Ho'.
    - eapply Ht, over_tree_fusion_l, over_tree_fusion_r ; exact Ho'.
    - eapply Hu, over_tree_fusion_r, over_tree_fusion_r ; exact Ho'.
  Qed.
    
    
  Lemma IdRedU@{i j k l} {wl Γ l A t u}
      (RU : [LogRel@{i j k l} l | Γ ||- U]< wl >)
      (RU' := invLRU RU)
      (RA : [LogRel@{i j k l} (URedTy.level RU') | Γ ||- A]< wl >) :
      [RU | Γ ||- A : U]< wl > ->
      [RA | Γ ||- t : _]< wl > ->
      [RA | Γ ||- u : _]< wl > ->
      [RU | Γ ||- tId A t u : U]< wl >.
  Proof.
    intros RAU Rt Ru.
    enough [LRU_ RU' | _ ||- tId A t u : U]< wl > by irrelevance.
    econstructor.
    - eapply redtmwf_refl; escape; now eapply ty_Id.
    - constructor.
    - eapply convtm_Id; eapply escapeEq + eapply escapeEqTerm; now eapply reflLRTmEq + eapply reflLRTyEq.
    - eapply RedTyRecBwd. eapply IdRed; irrelevanceCum.
    Unshelve. irrelevanceCum.
  Qed.

  Lemma WIdRedU@{i j k l} {wl Γ l l' A t u}
      (RU : WLogRel@{i j k l} l wl Γ U)
      (RA : WLogRel@{i j k l} l' wl Γ A) :
      W[Γ ||-< l > A : U | RU]< wl > ->
      W[Γ ||-< l' > t : _ | RA]< wl > ->
      W[Γ ||-< l' > u : _ | RA]< wl > ->
      W[Γ ||-< l > tId A t u : U | RU]< wl >.
  Proof.
    intros HA Ht Hu ; unshelve econstructor.
    1: do 2 eapply DTree_fusion ; [ .. | eapply DTree_fusion] ; shelve.
    intros wl' Ho Ho'.
    pose (f := over_tree_le Ho).
    unshelve eapply IdRedU.
    - unshelve eapply UnivEq.
      3: unshelve eapply HA.
      1: eapply over_tree_fusion_l, over_tree_fusion_l ; exact Ho'.
      eapply over_tree_fusion_r, over_tree_fusion_l ; exact Ho'.
    - unshelve eapply HA.
      eapply over_tree_fusion_r, over_tree_fusion_l ; exact Ho'.
    - irrelevanceRefl ; unshelve eapply Ht.
      1: eapply over_tree_fusion_l, over_tree_fusion_r ; exact Ho'.
      eapply over_tree_fusion_l, over_tree_fusion_r, over_tree_fusion_r ; exact Ho'.
    - irrelevanceRefl ; unshelve eapply Hu.
      1: eapply over_tree_fusion_l, over_tree_fusion_r ; exact Ho'.
      now do 3 eapply over_tree_fusion_r ; exact Ho'.
  Qed.

  
  Lemma IdCongRedU@{i j k l} {wl Γ l A A' t t' u u'} 
      (RU : [LogRel@{i j k l} l | Γ ||- U]< wl >)
      (RU' := invLRU RU)
      (RA : [LogRel@{i j k l} (URedTy.level RU') | Γ ||- A]< wl >)
      (RA' : [LogRel@{i j k l} (URedTy.level RU') | Γ ||- A']< wl >) :
    [RU | Γ ||- A : U]< wl > ->
    [RU | Γ ||- A' : U]< wl > ->
    [RU | _ ||- A ≅ A' : U]< wl > ->
    [RA | _ ||- t : _]< wl > ->
    [RA' | _ ||- t' : _]< wl > ->
    [RA | _ ||- t ≅ t' : _]< wl > ->
    [RA | _ ||- u : _]< wl > ->
    [RA' | _ ||- u' : _]< wl > ->
    [RA | _ ||- u ≅ u' : _]< wl > ->
    [RU | _ ||- tId A t u ≅ tId A' t' u' : U]< wl >.
  Proof.
    intros RAU RAU' RAAU' Rt Rt' Rtt' Ru Ru' Ruu'.
    enough [LRU_ RU' | _ ||- tId A t u ≅ tId A' t' u': U]< wl > by irrelevance.
    opector.
    - change [LRU_ RU' | _ ||- tId A t u : _]< wl >.
      enough [RU | _ ||- tId A t u : _]< wl > by irrelevance. 
      now unshelve eapply IdRedU.
    - change [LRU_ RU' | _ ||- tId A' t' u' : _]< wl >. 
      enough [RU | _ ||- tId A' t' u' : _]< wl > by irrelevance. 
      now unshelve eapply IdRedU.
    - eapply RedTyRecBwd. eapply IdRed; irrelevanceCum.
      Unshelve. clear dependent RA'; irrelevanceCum.
    - pose proof (redtmwf_whnf (URedTm.red u0) whnf_tId) as <-.
      pose proof (redtmwf_whnf (URedTm.red u1) whnf_tId) as <-.
      eapply convtm_Id; now escape.
    - eapply RedTyRecBwd. eapply IdRed; irrelevanceCum.
      Unshelve. irrelevanceCum.
    - eapply TyEqRecFwd.
      eapply LRTyEqIrrelevantCum.
      unshelve eapply IdCongRed; tea.
      + escape; gen_typing.
      + now eapply UnivEqEq.
      Unshelve. now eapply IdRed.
  Qed.

  Lemma WIdCongRedU@{i j k l} {wl Γ l l' A A' t t' u u'}
      (RU : WLogRel@{i j k l} l wl Γ U)
      (RA : WLogRel@{i j k l} l' wl Γ A)
      (RA' : WLogRel@{i j k l} l' wl Γ A') :
      W[Γ ||-< l > A : U | RU]< wl > ->
      W[Γ ||-< l > A' : U | RU]< wl > ->
      W[Γ ||-< l > A ≅ A' : U | RU]< wl > ->
      W[Γ ||-< l' > t : _ | RA]< wl > ->
      W[Γ ||-< l' > t' : _ | RA']< wl > ->
      W[Γ ||-< l' > t ≅ t' : _ | RA]< wl > ->
      W[Γ ||-< l' > u : _ | RA]< wl > ->
      W[Γ ||-< l' > u' : _ | RA']< wl > ->
      W[Γ ||-< l' > u ≅ u' : _ | RA]< wl > ->
      W[Γ ||-< l > tId A t u ≅ tId A' t' u' : U | RU]< wl >.
  Proof.
    intros HA HA' HAeq Ht Ht' Hteq Hu Hu' Hueq ; unshelve econstructor.
    1: do 4 eapply DTree_fusion ; shelve.
    intros wl' Ho Ho'.
    pose (f := over_tree_le Ho).
    unshelve eapply IdCongRedU.
    - unshelve eapply UnivEq.
      3: unshelve eapply HA.
      1: eapply over_tree_fusion_l, over_tree_fusion_l, over_tree_fusion_l, over_tree_fusion_l ; exact Ho'.
      eapply over_tree_fusion_r, over_tree_fusion_l, over_tree_fusion_l, over_tree_fusion_l ; exact Ho'.
    - unshelve eapply UnivEq.
      3: unshelve eapply HA'.
      1: eapply over_tree_fusion_l, over_tree_fusion_r, over_tree_fusion_l, over_tree_fusion_l ; exact Ho'.
      eapply over_tree_fusion_r, over_tree_fusion_r, over_tree_fusion_l, over_tree_fusion_l ; exact Ho'.
    - unshelve eapply HA.
      eapply over_tree_fusion_r, over_tree_fusion_l, over_tree_fusion_l, over_tree_fusion_l ; exact Ho'.
    - unshelve eapply HA'.
      eapply over_tree_fusion_r, over_tree_fusion_r, over_tree_fusion_l, over_tree_fusion_l ; exact Ho'.
    - unshelve eapply HAeq.
      eapply over_tree_fusion_l, over_tree_fusion_l, over_tree_fusion_r, over_tree_fusion_l ; exact Ho'.
    - irrelevanceRefl ; unshelve eapply Ht.
      1: eapply over_tree_fusion_r, over_tree_fusion_l, over_tree_fusion_r, over_tree_fusion_l ; exact Ho'.
      eapply over_tree_fusion_l, over_tree_fusion_r, over_tree_fusion_r, over_tree_fusion_l ; exact Ho'.
    - irrelevanceRefl ; unshelve eapply Ht'.
      1: eapply over_tree_fusion_r, over_tree_fusion_r, over_tree_fusion_r, over_tree_fusion_l ; exact Ho'.
      eapply over_tree_fusion_l, over_tree_fusion_l, over_tree_fusion_l, over_tree_fusion_r ; exact Ho'.
    - irrelevanceRefl ; unshelve eapply Hteq.
      1: eapply over_tree_fusion_r, over_tree_fusion_l, over_tree_fusion_r, over_tree_fusion_l ; exact Ho'.
      eapply over_tree_fusion_r, over_tree_fusion_l, over_tree_fusion_l, over_tree_fusion_r ; exact Ho'.
    - irrelevanceRefl ; unshelve eapply Hu.
      1: eapply over_tree_fusion_r, over_tree_fusion_l, over_tree_fusion_r, over_tree_fusion_l ; exact Ho'.
      eapply over_tree_fusion_l, over_tree_fusion_r, over_tree_fusion_l, over_tree_fusion_r ; exact Ho'.
    - irrelevanceRefl ; unshelve eapply Hu'.
      1: eapply over_tree_fusion_r, over_tree_fusion_r, over_tree_fusion_r, over_tree_fusion_l ; exact Ho'.
      eapply over_tree_fusion_r, over_tree_fusion_r, over_tree_fusion_l, over_tree_fusion_r ; exact Ho'.
    - irrelevanceRefl ; unshelve eapply Hueq.
      1: eapply over_tree_fusion_r, over_tree_fusion_l, over_tree_fusion_r, over_tree_fusion_l ; exact Ho'.
      eapply over_tree_fusion_l, over_tree_fusion_l, over_tree_fusion_r, over_tree_fusion_r ; exact Ho'.
      Unshelve.
      all: now constructor.
  Qed.
    


Lemma reflRed {wl Γ l A x} (RA : [Γ ||-<l> A]< wl >) (Rx : [RA | _ ||- x : _]< wl >) (RIA : [Γ ||-<l> tId A x x]< wl >) :
  [RIA | _ ||- tRefl A x : _]< wl >.
Proof.
  set (RIA' := invLRId RIA).
  enough [LRId' RIA' | _ ||- tRefl A x : _]< wl > by irrelevance.
  pose proof (IdRedTy_inv RIA') as [eA ex ex'].
  assert (e : tId (IdRedTy.ty RIA') (IdRedTy.lhs RIA') (IdRedTy.rhs RIA') = tId A x x).
  1: f_equal; now symmetry.
  econstructor; unfold_id_outTy; cbn; rewrite ?e.
  + eapply redtmwf_refl; eapply ty_refl; now escape.
  + eapply convtm_refl; [eapply escapeEq; eapply reflLRTyEq|eapply escapeEqTerm; now eapply reflLRTmEq].
  + constructor; cbn.
    1,2: now escape.
    all: irrelevance0; tea.
    1: eapply reflLRTyEq.
    * rewrite <- ex; now eapply reflLRTmEq.
    * rewrite <- ex'; now eapply reflLRTmEq.
  Unshelve.  all: tea.
Qed.

Lemma reflRed' {wl Γ l A x} (RA : [Γ ||-<l> A]< wl >) (Rx : [RA | _ ||- x : _]< wl >) 
  (RIA := IdRed RA Rx Rx): [RIA | _ ||- tRefl A x : _]< wl >.
Proof. now eapply reflRed. Qed.


Lemma WreflRed {wl Γ l A x} (RA : W[Γ ||-<l> A]< wl >) (Rx : W[ _ ||-< l > x : _ | RA]< wl >) (RIA : W[Γ ||-<l> tId A x x]< wl >) :
  W[_ ||-< l > tRefl A x : _ | RIA]< wl >.
Proof.
  unshelve econstructor.
  1: eapply DTree_fusion ; shelve.
  intros wl' Ho Ho'.
  pose (f := over_tree_le Ho).
  unshelve eapply reflRed.
  - eapply RA, over_tree_fusion_l ; exact Ho'.
  - eapply Rx, over_tree_fusion_r ; exact Ho'.
  Qed.
    
  
Lemma WreflRed' {wl Γ l A x} (RA : W[Γ ||-<l> A]< wl >) (Rx : W[_ ||-< l > x : _ | RA]< wl >) 
  (RIA := WIdRed RA Rx Rx): W[_ ||-< l > tRefl A x : _ | RIA]< wl >.
Proof. now eapply WreflRed. Qed.

Lemma reflCongRed {wl Γ l A A' x x'} 
  (RA : [Γ ||-<l> A]< wl >)
  (TA' : [Γ |- A']< wl >)
  (RAA' : [RA | _ ||- _ ≅ A']< wl >)
  (Rx : [RA | _ ||- x : _]< wl >) 
  (Tx' : [Γ |- x' : A']< wl >)
  (Rxx' : [RA | _ ||- x ≅ x' : _]< wl >) 
  (RIA : [Γ ||-<l> tId A x x]< wl >) :
  [RIA | _ ||- tRefl A x ≅ tRefl A' x' : _]< wl >.
Proof.
  set (RIA' := invLRId RIA).
  enough [LRId' RIA' | _ ||- tRefl A x ≅ tRefl A' x' : _]< wl > by irrelevance.
  pose proof (IdRedTy_inv RIA') as [eA ex ex'].
  assert (e : tId (IdRedTy.ty RIA') (IdRedTy.lhs RIA') (IdRedTy.rhs RIA') = tId A x x).
  1: f_equal; now symmetry.
  assert [Γ |- tId A x x ≅ tId A' x' x']< wl > by (escape ; gen_typing).
  econstructor; unfold_id_outTy; cbn; rewrite ?e.
  1,2: eapply redtmwf_refl.
  1: escape; gen_typing.
  - eapply ty_conv; [| now symmetry]; now eapply ty_refl.
  - eapply convtm_refl; now escape.
  - constructor; cbn.
    1-4: now escape.  
    all: irrelevance0; tea.
    1: apply reflLRTyEq.
    1,2: rewrite <- ex; tea; now eapply reflLRTmEq.
    1,2: rewrite <- ex'; tea; now eapply reflLRTmEq.
  Unshelve. all: tea.
Qed.

Lemma WreflCongRed {wl Γ l A A' x x'} 
  (RA : W[Γ ||-<l> A]< wl >)
  (TA' : [Γ |- A']< wl >)
  (RAA' : W[_ ||-< l > _ ≅ A' | RA]< wl >)
  (Rx : W[_ ||-< l > x : _ | RA]< wl >) 
  (Tx' : [Γ |- x' : A']< wl >)
  (Rxx' : W[_ ||-< l > x ≅ x' : _ | RA]< wl >) 
  (RIA : W[Γ ||-<l> tId A x x]< wl >) :
  W[_ ||-< l > tRefl A x ≅ tRefl A' x' : _ | RIA]< wl >.
Proof.
  unshelve econstructor.
  1: do 2 eapply DTree_fusion ; shelve.
  intros wl' Ho Ho'.
  pose (f := over_tree_le Ho).
  unshelve eapply reflCongRed.
  - eapply RA, over_tree_fusion_l, over_tree_fusion_l; exact Ho'.
  - now eapply wft_Ltrans.
  - eapply RAA', over_tree_fusion_r, over_tree_fusion_l; exact Ho'.
  - eapply Rx, over_tree_fusion_l, over_tree_fusion_r ; exact Ho'.
  - now eapply ty_Ltrans.
  - eapply Rxx', over_tree_fusion_r, over_tree_fusion_r ; exact Ho'.
  Qed.


  
Definition idElimProp {wl Γ l} (A x P hr y e : term) {IA : [Γ ||-Id<l> tId A x y]< wl >} (Pe : IdProp IA e) : term :=
  match Pe with
  | IdRedTm.reflR _ _ _ _ _ => hr
  | IdRedTm.neR _ => tIdElim A x P hr y e
  end.

Lemma idElimPropIrr {wl Γ l} {A x P hr y e : term} {IA : [Γ ||-Id<l> tId A x y]< wl >} (Pe Pe' : IdProp IA e) :
  idElimProp A x P hr y e Pe = idElimProp A x P hr y e Pe'.
Proof.
  destruct Pe; cbn.
  2: dependent inversion Pe'; try reflexivity.
  2:  subst; match goal with H : [_ ||-NeNf _ : _]< wl > |- _ => destruct H as [_ ?%convneu_whne]; inv_whne end; tea.
  refine (match Pe' as Pe0  in IdRedTm.IdProp _ e return match e as e return IdProp _ e -> Type with | tRefl A0 x0 => fun Pe0 => hr = idElimProp A x P hr y (tRefl A0 x0) Pe0 | _ => fun _ => unit end Pe0 with | IdRedTm.reflR _ _ _ _ _ => _ | IdRedTm.neR r  => _ end).
  1: reflexivity.
  1: match type of r with [_ ||-NeNf ?t : _]< wl > =>  destruct t ; try easy end. 
  exfalso; destruct r as [_ ?%convneu_whne]; inv_whne.
Qed.

Lemma IdProp_refl_inv {wl Γ l A x y A' x'} {IA : [Γ ||-Id<l> tId A x y]< wl >} (Pe : IdProp IA (tRefl A' x')) :
  IdProp IA (tRefl A' x').
Proof.
  econstructor; inversion Pe.
  all: try match goal with H : [_ ||-NeNf _ : _]< _ > |- _ => destruct H as [_ ?%convneu_whne]; inv_whne end; tea.
Defined.

Lemma IdRedTm_whnf_prop {wl Γ l A x y e} {IA : [Γ ||-Id<l> tId A x y]< wl >} (Re : [_ ||-Id<l> e : _ | IA]< wl >) :
  whnf e -> IdProp IA e.
Proof.
  intros wh; rewrite (redtmwf_whnf (IdRedTm.red Re) wh).
  exact (IdRedTm.prop Re).
Qed.

Lemma idElimPropRed {wl Γ l A x P hr y e}
  (RA : [Γ ||-<l> A]< wl >)
  (Rx : [RA | _ ||- x : _]< wl >)
  (RP0 : [Γ ,, A ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) ||-<l> P]< wl >)
  (RP : forall y e (Ry : [RA | Γ ||- y : _]< wl >) (RIAxy : [Γ ||-<l> tId A x y]< wl >),
    [ RIAxy | _ ||- e : _]< wl > -> [Γ ||-<l> P[e .: y..]]< wl >)
  (RPeq : forall A' x' y y' e e' 
    (RA' : [Γ ||-<l> A']< wl >)
    (RAA' : [RA | _ ||- _ ≅ A']< wl >)
    (Rx' : [RA | _ ||- x' : _]< wl >)
    (Rxx' : [RA | _ ||- x ≅ x' : _]< wl >)
    (Ry : [RA | Γ ||- y : _]< wl >)
    (Ry' : [RA' | _ ||- y' : _]< wl >)
    (Ryy' : [RA | Γ ||- y ≅ y' : _]< wl >)
    (RIAxy : [Γ ||-<l> tId A x y]< wl >)
    (RIAxy' : [Γ ||-<l> tId A x y']< wl >)
    (Re : [ RIAxy | _ ||- e : _]< wl >)
    (Re' : [ RIAxy' | _ ||- e' : _]< wl >)
    (Ree' : [ RIAxy | _ ||- e ≅ e' : _]< wl >),
    [RP y e Ry RIAxy Re | Γ ||- P[e .: y..] ≅ P[e' .: y' ..]]< wl >)
  (Rhr : [RP x (tRefl A x) Rx (IdRed RA Rx Rx) (reflRed' RA Rx) | _ ||- hr : _]< wl >)
  (Ry : [RA | _ ||- y : _]< wl >)
  (RIAxy : [Γ ||-<l> tId A x y]< wl >)
  (Re : [RIAxy | _ ||- e : _]< wl >) 
  (RIAxy0 : [Γ ||-Id<l> tId A x y]< wl >)
  (Pe : IdProp RIAxy0 e) :
  [RP y e Ry _ Re | _ ||- tIdElim A x P hr y e : _]< wl > ×
  [RP y e Ry _ Re | _ ||- tIdElim A x P hr y e ≅ idElimProp A x P hr y e Pe : _]< wl >.
Proof.
  pose proof (IdRedTy_inv RIAxy0) as [eA ex ey].
  eapply redSubstTerm.
  - destruct Pe; cbn in *.
    + eapply LRTmRedConv; tea.
      unshelve eapply RPeq; cycle 3; tea.
      2,3: eapply transEqTerm; [|eapply LRTmEqSym]; rewrite ?ex, ?ey; irrelevance.
      * eapply reflLRTyEq.
      * eapply reflCongRed; tea.
        1: irrelevance0; [symmetry; tea|]; tea.
        rewrite ex; irrelevance.
    + eapply neuTerm.
      * escape; eapply ty_IdElim; tea.
      * destruct r.
        pose proof (reflLRTyEq RA).
        pose proof (reflLRTyEq RP0).
        pose proof Rx as ?%reflLRTmEq.
        pose proof Ry as ?%reflLRTmEq.
        pose proof Rhr as ?%reflLRTmEq.
        escape; eapply convneu_IdElim; tea.
        eapply convneu_conv; tea. unfold_id_outTy.
        rewrite <- eA, <- ex, <- ey; eapply convty_Id; tea.
  - destruct Pe; cbn in *.
    + escape; eapply redtm_idElimRefl; tea.
      * eapply ty_conv; tea; rewrite eA; now symmetry.
      * now rewrite eA.
      * rewrite eA, ex, ey; etransitivity; tea; now symmetry.
      * now rewrite eA, ex.
    + eapply redtm_refl; escape; now eapply ty_IdElim.
Qed.

Lemma WidElimPropRed {wl Γ l A x P hr y e}
  (RA : W[Γ ||-<l> A]< wl >)
  (Rx : W[_ ||-< l > x : _ | RA]< wl >)
  (RP0 : W[Γ ,, A ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) ||-<l> P]< wl >)
  (RP : forall y e (Ry : W[Γ ||-< l > y : _| RA]< wl >)
               (RIAxy : W[Γ ||-<l> tId A x y]< wl >),
    W[_ ||-< l > e : _ | RIAxy]< wl > -> W[Γ ||-<l> P[e .: y..]]< wl >)
  (RPeq : forall A' x' y y' e e' 
    (RA' : W[Γ ||-<l> A']< wl >)
    (RAA' : W[_ ||-< l > _ ≅ A' | RA]< wl >)
    (Rx' : W[_ ||-< l > x' : _ | RA]< wl >)
    (Rxx' : W[_ ||-< l > x ≅ x' : _ | RA]< wl >)
    (Ry : W[Γ ||-< l > y : _ | RA]< wl >)
    (Ry' : W[_ ||-< l > y' : _ | RA']< wl >)
    (Ryy' : W[Γ ||-< l > y ≅ y' : _ | RA]< wl >)
    (RIAxy : W[Γ ||-<l> tId A x y]< wl >)
    (RIAxy' : W[Γ ||-<l> tId A x y']< wl >)
    (Re : W[ _ ||-< l > e : _ | RIAxy]< wl >)
    (Re' : W[ _ ||-< l > e' : _ | RIAxy']< wl >)
    (Ree' : W[ _ ||-< l > e ≅ e' : _ | RIAxy]< wl >),
    W[ Γ ||-< l > P[e .: y..] ≅ P[e' .: y' ..] | RP y e Ry RIAxy Re]< wl >)
  (Rhr : W[_ ||-< l > hr : _ | RP x (tRefl A x) Rx (WIdRed RA Rx Rx) (WreflRed' RA Rx) ]< wl >)
  (Ry : W[_ ||-< l > y : _ | RA]< wl >)
  (RIAxy : W[Γ ||-<l> tId A x y]< wl >)
  (Re : W[_ ||-< l > e : _ | RIAxy ]< wl >)
  (RIAxy0 : [Γ ||-Id<l> tId A x y]< wl >)
  (Pe : IdProp RIAxy0 e) :
  W[ _ ||-< l > tIdElim A x P hr y e : _ | RP y e Ry _ Re]< wl > ×
  W[ _ ||-< l > tIdElim A x P hr y e ≅ idElimProp A x P hr y e Pe : _ | RP y e Ry _ Re]< wl >.
Proof.
  pose proof (IdRedTy_inv RIAxy0) as [eA ex ey].
  eapply WredSubstTerm.
  - destruct Pe ; cbn in *.
    + eapply WLRTmRedConv ; [ | exact Rhr].
      unshelve eapply RPeq; cycle 4; tea.
      2,3: Wirrelevance0 ; [ symmetry ; exact eA | ].
      2,3: eapply TmEqLogtoW, transEqTerm; [|eapply LRTmEqSym]; now rewrite ?ex, ?ey.
      * eapply WreflLRTyEq.
      * eapply WreflCongRed; tea.
        2:rewrite ex ; Wirrelevance0 ; [symmetry ; exact eA | ].
        2: now eapply TmEqLogtoW.
        Wirrelevance0; [symmetry; exact eA|] ; now eapply EqLogtoW.
    + eapply WneuTerm.
      * escape ; Wescape; eapply ty_IdElim; tea.
      * destruct r.
        pose proof (WreflLRTyEq RA).
        pose proof (WreflLRTyEq RP0).
        pose proof Rx as ?%WreflLRTmEq.
        pose proof Ry as ?%WreflLRTmEq.
        pose proof Rhr as ?%WreflLRTmEq.
        Wescape ; escape; eapply convneu_IdElim; tea.
        eapply convneu_conv; tea. unfold_id_outTy.
        rewrite <- eA, <- ex, <- ey; eapply convty_Id; tea.
  - destruct Pe; cbn in *.
    + escape ; Wescape ; eapply redtm_idElimRefl; tea.
      * eapply ty_conv; tea; rewrite eA; now symmetry.
      * now rewrite eA.
      * rewrite eA, ex, ey; etransitivity; tea; now symmetry.
      * now rewrite eA, ex.
    + eapply redtm_refl; escape; Wescape ; now eapply ty_IdElim.
Qed.
    

Lemma idElimRed {wl Γ l A x P hr y e}
  (RA : [Γ ||-<l> A]< wl >)
  (Rx : [RA | _ ||- x : _]< wl >)
  (RP0 : [Γ ,, A ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) ||-<l> P]< wl >)
  (RP : forall y e (Ry : [RA | Γ ||- y : _]< wl >) (RIAxy : [Γ ||-<l> tId A x y]< wl >),
    [ RIAxy | _ ||- e : _]< wl > -> [Γ ||-<l> P[e .: y..]]< wl >)
  (RPeq : forall A' x' y y' e e' 
    (RA' : [Γ ||-<l> A']< wl >)
    (RAA' : [RA | _ ||- _ ≅ A']< wl >)
    (Rx' : [RA | _ ||- x' : _]< wl >)
    (Rxx' : [RA | _ ||- x ≅ x' : _]< wl >)
    (Ry : [RA | Γ ||- y : _]< wl >)
    (Ry' : [RA' | _ ||- y' : _]< wl >)
    (Ryy' : [RA | Γ ||- y ≅ y' : _]< wl >)
    (RIAxy : [Γ ||-<l> tId A x y]< wl >)
    (RIAxy' : [Γ ||-<l> tId A x y']< wl >)
    (Re : [ RIAxy | _ ||- e : _]< wl >)
    (Re' : [ RIAxy' | _ ||- e' : _]< wl >)
    (Ree' : [ RIAxy | _ ||- e ≅ e' : _]< wl >),
    [RP y e Ry RIAxy Re | Γ ||- P[e .: y..] ≅ P[e' .: y' ..]]< wl >)
  (Rhr : [RP x (tRefl A x) Rx (IdRed RA Rx Rx) (reflRed' RA Rx) | _ ||- hr : _]< wl >)
  (Ry : [RA | _ ||- y : _]< wl >)
  (RIAxy : [Γ ||-<l> tId A x y]< wl >)
  (RIAxy' := LRId' (invLRId RIAxy))
  (Re : [RIAxy' | _ ||- e : _]< wl >) :
  [RP y e Ry _ Re | _ ||- tIdElim A x P hr y e : _]< wl > ×
  [RP y e Ry _ Re | _ ||- tIdElim A x P hr y e ≅ tIdElim A x P hr y (IdRedTm.nf Re) : _]< wl >.
Proof.
  pose proof (IdRedTy_inv (invLRId RIAxy)) as [eA ex ey].
  pose proof (hred := Re.(IdRedTm.red)); unfold_id_outTy; rewrite <-eA,<-ex,<-ey in hred.
  eapply redSubstTerm.
  - pose proof (redTmFwdConv Re hred (IdProp_whnf _ _ (IdRedTm.prop Re))) as [Rnf Rnfeq].
    eapply LRTmRedConv.
    2: eapply idElimPropRed; tea; exact (IdRedTm.prop Re).
    unshelve eapply LRTyEqSym.
    2: now eapply RP.
    eapply RPeq; cycle 2; first [eapply reflLRTyEq | now eapply reflLRTmEq | tea].
    Unshelve. all: tea.
  - escape; eapply redtm_idElim; tea; apply hred.
Qed.

Lemma WidElimRed {wl Γ l A x P hr y e}
  (RA : W[Γ ||-<l> A]< wl >)
  (Rx : W[_ ||-< l > x : _ | RA]< wl >)
  (RP0 : W[Γ ,, A ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) ||-<l> P]< wl >)
  (RP : forall y e
               (Ry : W[Γ ||-< l > y : _| RA]< wl >) (RIAxy : W[Γ ||-<l> tId A x y]< wl >),
    W[_ ||-< l > e : _ | RIAxy]< wl > -> W[Γ ||-<l> P[e .: y..]]< wl >)
  (RPeq : forall A' x' y y' e e' 
    (RA' : W[Γ ||-<l> A']< wl >)
    (RAA' : W[_ ||-< l > _ ≅ A' | RA]< wl >)
    (Rx' : W[_ ||-< l > x' : _ | RA]< wl >)
    (Rxx' : W[_ ||-< l > x ≅ x' : _ | RA]< wl >)
    (Ry : W[Γ ||-< l > y : _ | RA]< wl >)
    (Ry' : W[_ ||-< l > y' : _ | RA']< wl >)
    (Ryy' : W[Γ ||-< l > y ≅ y' : _ | RA]< wl >)
    (RIAxy : W[Γ ||-<l> tId A x y]< wl >)
    (RIAxy' : W[Γ ||-<l> tId A x y']< wl >)
    (Re : W[ _ ||-< l > e : _ | RIAxy]< wl >)
    (Re' : W[ _ ||-< l > e' : _ | RIAxy']< wl >)
    (Ree' : W[ _ ||-< l > e ≅ e' : _ | RIAxy]< wl >),
    W[ Γ ||-< l > P[e .: y..] ≅ P[e' .: y' ..] | RP y e Ry RIAxy Re]< wl >)
  (Rhr : W[_ ||-< l > hr : _ | RP x (tRefl A x) Rx (WIdRed RA Rx Rx) (WreflRed' RA Rx) ]< wl >)
  (Ry : W[_ ||-< l > y : _ | RA]< wl >)
  (RIAxy : [Γ ||-<l> tId A x y]< wl >)
  (RIAxy' := LRId' (invLRId RIAxy))
  (Re : [RIAxy' | _ ||- e : _]< wl >) :
  W[ _ ||-< l > tIdElim A x P hr y e : _ | RP y e Ry _ (TmLogtoW _ Re)]< wl > ×
   W[ _ ||-< l > tIdElim A x P hr y e ≅ tIdElim A x P hr y (IdRedTm.nf Re) : _ | RP y e Ry _ (TmLogtoW _ Re)]< wl >.
Proof.
  pose proof (IdRedTy_inv (invLRId RIAxy)) as [eA ex ey].
  pose proof (hred := Re.(IdRedTm.red)); unfold_id_outTy; rewrite <-eA,<-ex,<-ey in hred.
  eapply WredSubstTerm.
  - pose proof (redTmFwdConv Re hred (IdProp_whnf _ _ (IdRedTm.prop Re))) as [Rnf Rnfeq].
    eapply WLRTmRedConv.
    2: eapply WidElimPropRed; tea.
    2: exact (IdRedTm.prop Re).
    unshelve eapply WLRTyEqSym.
    2: eapply RP ; tea.
    1: now eapply TmLogtoW.
    eapply RPeq; cycle 2; first [eapply WreflLRTyEq | now eapply WreflLRTmEq | tea].
    1: now eapply TmLogtoW.
    1: now eapply TmEqLogtoW.
    Unshelve. 1: now tea.
    2: eapply TmLogtoW ; eassumption.
  - Wescape.  eapply redtm_idElim; tea; apply hred.
Qed.


Lemma idElimPropCongRed {wl Γ l A A' x x' P P' hr hr' y y' e e'}
  (RA : [Γ ||-<l> A]< wl >)
  (RA' : [Γ ||-<l> A']< wl >)
  (RAA' : [RA | Γ ||- A ≅ A']< wl >)
  (Rx : [RA | _ ||- x : _]< wl >)
  (Rx' : [RA' | _ ||- x' : _]< wl >)
  (Rxx' : [RA | _ ||- x ≅ x' : _]< wl >)
  (RP0 : [Γ ,, A ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) ||-<l> P]< wl >)
  (RP0' : [Γ ,, A' ,, tId A'⟨@wk1 Γ A'⟩ x'⟨@wk1 Γ A'⟩ (tRel 0) ||-<l> P']< wl >)
  (RPP0 : [RP0 | _ ||- _ ≅ P']< wl >)
  (RP : forall y e (Ry : [RA | Γ ||- y : _]< wl >) (RIAxy : [Γ ||-<l> tId A x y]< wl >),
    [ RIAxy | _ ||- e : _]< wl > -> [Γ ||-<l> P[e .: y..]]< wl >)
  (RP' : forall y' e' (Ry' : [RA' | Γ ||- y' : _]< wl >) (RIAxy' : [Γ ||-<l> tId A' x' y']< wl >),
    [ RIAxy' | _ ||- e' : _]< wl > -> [Γ ||-<l> P'[e' .: y'..]]< wl >)
  (RPP' : forall y y' e e' 
    (Ry : [RA | Γ ||- y : _]< wl >)
    (Ry' : [RA' | Γ ||- y' : _]< wl >)
    (Ryy' : [RA | _ ||- y ≅ y' : _]< wl >)
    (RIAxy : [Γ ||-<l> tId A x y]< wl >)
    (RIAxy' : [Γ ||-<l> tId A' x' y']< wl >)
    (Re : [ RIAxy | _ ||- e : _]< wl >)
    (Re' : [ RIAxy' | _ ||- e' : _]< wl >)
    (Ree' : [ RIAxy | _ ||- e ≅ e' : _]< wl >),
    [RP y e Ry _ Re | _ ||- P[e .: y..] ≅ P'[e' .: y'..]]< wl >)
  (RPeq : forall A' x' y y' e e' 
    (RA' : [Γ ||-<l> A']< wl >)
    (RAA' : [RA | _ ||- _ ≅ A']< wl >)
    (Rx' : [RA | _ ||- x' : _]< wl >)
    (Rxx' : [RA | _ ||- x ≅ x' : _]< wl >)
    (Ry : [RA | Γ ||- y : _]< wl >)
    (Ry' : [RA' | _ ||- y' : _]< wl >)
    (Ryy' : [RA | Γ ||- y ≅ y' : _]< wl >)
    (RIAxy : [Γ ||-<l> tId A x y]< wl >)
    (RIAxy' : [Γ ||-<l> tId A x y']< wl >)
    (Re : [ RIAxy | _ ||- e : _]< wl >)
    (Re' : [ RIAxy' | _ ||- e' : _]< wl >)
    (Ree' : [ RIAxy | _ ||- e ≅ e' : _]< wl >),
    [RP y e Ry RIAxy Re | Γ ||- P[e .: y..] ≅ P[e' .: y' ..]]< wl >)
  (RPeq' : forall A1 x1 y' y1 e' e1 
    (RA1 : [Γ ||-<l> A1]< wl >)
    (RAA1 : [RA' | _ ||- _ ≅ A1]< wl >)
    (Rx1 : [RA' | _ ||- x1 : _]< wl >)
    (Rxx1 : [RA' | _ ||- x' ≅ x1 : _]< wl >)
    (Ry' : [RA' | Γ ||- y' : _]< wl >)
    (Ry1 : [RA1 | _ ||- y1 : _]< wl >)
    (Ryy1 : [RA' | Γ ||- y' ≅ y1 : _]< wl >)
    (RIAxy' : [Γ ||-<l> tId A' x' y']< wl >)
    (RIAxy1 : [Γ ||-<l> tId A' x' y1]< wl >)
    (Re' : [ RIAxy' | _ ||- e' : _]< wl >)
    (Re1 : [ RIAxy1 | _ ||- e1 : _]< wl >)
    (Ree1 : [ RIAxy' | _ ||- e' ≅ e1 : _]< wl >),
    [RP' y' e' Ry' RIAxy' Re' | Γ ||- P'[e' .: y'..] ≅ P'[e1 .: y1 ..]]< wl >)
  (Rhr : [RP x (tRefl A x) Rx (IdRed RA Rx Rx) (reflRed' RA Rx) | _ ||- hr : _]< wl >)
  (Rhr' : [RP' x' (tRefl A' x') Rx' (IdRed RA' Rx' Rx') (reflRed' RA' Rx') | _ ||- hr' : _]< wl >)
  (Rhrhr' : [RP x (tRefl A x) Rx (IdRed RA Rx Rx) (reflRed' RA Rx) | _ ||- hr ≅ hr' : _]< wl >)
  (Ry : [RA | _ ||- y : _]< wl >)
  (Ry' : [RA' | _ ||- y' : _]< wl >)
  (Ryy' : [RA | _ ||- y ≅ y' : _]< wl >)
  (RIAxy : [Γ ||-<l> tId A x y]< wl >)
  (RIAxy' : [Γ ||-<l> tId A' x' y']< wl >)
  (Re : [RIAxy | _ ||- e : _]< wl >) 
  (Re' : [RIAxy' | _ ||- e' : _]< wl >) 
  (Ree' : [RIAxy | _ ||- e ≅ e' : _]< wl >)
  (RIAxy0 : [Γ ||-Id<l> tId A x y]< wl >)
  (Pee' : IdPropEq RIAxy0 e e') :
  [RP y e Ry _ Re | _ ||- tIdElim A x P hr y e ≅ tIdElim A' x' P' hr' y' e' : _]< wl >.
Proof.
  pose proof (IdRedTy_inv RIAxy0) as [eA ex ey].
  (* pose proof (IdRedTy_inv (invLRId RIAxy))) as [eA ex ey].
  pose proof (IdRedTy_inv (invLRId RIAxy')) as [eA' ex' ey']. *)
  pose proof (IdPropEq_whnf _ _ _ Pee') as [whe whe'].
  assert (Rei : [LRId' RIAxy0 | _ ||- e : _]< wl >) by irrelevance.
  assert (Rei' : [LRId' (invLRId RIAxy') | _ ||- e' : _]< wl >) by irrelevance.
  pose proof (IdRedTm_whnf_prop Rei whe).
  pose proof (IdRedTm_whnf_prop Rei' whe').
  eapply LREqTermHelper.
  1,2: unshelve eapply idElimPropRed; tea.
  1: now eapply RPP'.
  destruct Pee'; cbn in *.
  + unshelve erewrite (idElimPropIrr X), (idElimPropIrr X0).
    1,2: now eapply IdProp_refl_inv.
    cbn; eapply LRTmEqRedConv; tea.
    eapply RPeq; cycle 3; tea.
    1,4: rewrite ex, ey; eapply transEqTerm; [|eapply LRTmEqSym]; irrelevance.
    2: eapply reflLRTyEq.
    eapply reflCongRed; tea.
    1: irrelevance.
    rewrite ex; irrelevance.
  + unshelve erewrite (idElimPropIrr X), (idElimPropIrr X0); destruct r; unfold_id_outTy.
    * econstructor; escape ; constructor; unfold_id_outTy.
      1: rewrite <- ex, <- ey, <-eA; tea.
      now eapply lrefl.
    * econstructor; pose proof (IdRedTy_inv (invLRId RIAxy')) as [eA' ex' ey'].
      escape; constructor; unfold_id_outTy.
      all: rewrite <- ex', <- ey', <-eA'; tea.
      eapply convneu_conv; [now eapply urefl|].
      rewrite <- ex, <- ey, <-eA; now eapply convty_Id.
    * cbn. escape; eapply neuTermEq.
      - now eapply ty_IdElim.
      - eapply ty_conv; [now eapply ty_IdElim|].
        symmetry; eapply escapeEq; now eapply RPP'.
        Unshelve. all: tea.
      - eapply convneu_IdElim; tea.
        now rewrite ex, ey, eA.
Qed.

Lemma WidElimPropCongRed {wl Γ l A A' x x' P P' hr hr' y y' e e'}
  (RA : W[Γ ||-<l> A]< wl >)
  (RA' : W[Γ ||-<l> A']< wl >)
  (RAA' : W[ Γ ||-< l > A ≅ A' | RA]< wl >)
  (Rx : W[ _ ||-< l > x : _ | RA]< wl >)
  (Rx' : W[ _ ||-< l > x' : _ | RA']< wl >)
  (Rxx' : W[ _ ||-< l > x ≅ x' : _ | RA]< wl >)
  (RP0 : W[Γ ,, A ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) ||-<l> P]< wl >)
  (RP0' : W[Γ ,, A' ,, tId A'⟨@wk1 Γ A'⟩ x'⟨@wk1 Γ A'⟩ (tRel 0) ||-<l> P']< wl >)
  (RPP0 : W[ _ ||-< l > _ ≅ P' | RP0]< wl >)
  (RP : forall y e (Ry : W[ Γ ||-< l > y : _ | RA]< wl >) (RIAxy : W[Γ ||-<l> tId A x y]< wl >),
    W[ _ ||-< l > e : _ | RIAxy]< wl > -> W[Γ ||-<l> P[e .: y..]]< wl >)
  (RP' : forall y' e' (Ry' : W[ Γ ||-< l > y' : _ | RA']< wl >) (RIAxy' : W[Γ ||-<l> tId A' x' y']< wl >),
    W[ _ ||-< l > e' : _ | RIAxy']< wl > -> W[Γ ||-<l> P'[e' .: y'..]]< wl >)
  (RPP' : forall y y' e e' 
    (Ry : W[ Γ ||-< l > y : _ | RA]< wl >)
    (Ry' : W[ Γ ||-< l > y' : _ | RA']< wl >)
    (Ryy' : W[ _ ||-< l > y ≅ y' : _ | RA]< wl >)
    (RIAxy : W[Γ ||-<l> tId A x y]< wl >)
    (RIAxy' : W[Γ ||-<l> tId A' x' y']< wl >)
    (Re : W[ _ ||-< l > e : _ | RIAxy]< wl >)
    (Re' : W[ _ ||-< l > e' : _ | RIAxy']< wl >)
    (Ree' : W[ _ ||-< l > e ≅ e' : _ | RIAxy]< wl >),
    W[ _ ||-< l > P[e .: y..] ≅ P'[e' .: y'..] | RP y e Ry _ Re]< wl >)
  (RPeq : forall A' x' y y' e e' 
    (RA' : W[Γ ||-<l> A']< wl >)
    (RAA' : W[ _ ||-< l > _ ≅ A' | RA]< wl >)
    (Rx' : W[ _ ||-< l > x' : _ | RA]< wl >)
    (Rxx' : W[ _ ||-< l > x ≅ x' : _ | RA]< wl >)
    (Ry : W[ Γ ||-< l > y : _ | RA]< wl >)
    (Ry' : W[ _ ||-< l > y' : _ | RA']< wl >)
    (Ryy' : W[ Γ ||-< l > y ≅ y' : _ | RA]< wl >)
    (RIAxy : W[Γ ||-<l> tId A x y]< wl >)
    (RIAxy' : W[Γ ||-<l> tId A x y']< wl >)
    (Re : W[ _ ||-< l > e : _ | RIAxy]< wl >)
    (Re' : W[ _ ||-< l > e' : _ | RIAxy']< wl >)
    (Ree' : W[ _ ||-< l > e ≅ e' : _ | RIAxy]< wl >),
    W[Γ ||-< l > P[e .: y..] ≅ P[e' .: y' ..] | RP y e Ry RIAxy Re]< wl >)
  (RPeq' : forall A1 x1 y' y1 e' e1 
    (RA1 : W[Γ ||-<l> A1]< wl >)
    (RAA1 : W[ _ ||-< l > _ ≅ A1 | RA']< wl >)
    (Rx1 : W[ _ ||-< l > x1 : _ | RA']< wl >)
    (Rxx1 : W[ _ ||-< l > x' ≅ x1 : _ | RA']< wl >)
    (Ry' : W[ Γ ||-< l > y' : _ | RA']< wl >)
    (Ry1 : W[ _ ||-< l > y1 : _ | RA1]< wl >)
    (Ryy1 : W[ Γ ||-< l > y' ≅ y1 : _ | RA']< wl >)
    (RIAxy' : W[Γ ||-<l> tId A' x' y']< wl >)
    (RIAxy1 : W[Γ ||-<l> tId A' x' y1]< wl >)
    (Re' : W[ _ ||-< l > e' : _ | RIAxy']< wl >)
    (Re1 : W[ _ ||-< l > e1 : _ | RIAxy1]< wl >)
    (Ree1 : W[ _ ||-< l > e' ≅ e1 : _ | RIAxy']< wl >),
    W[Γ ||-< l > P'[e' .: y'..] ≅ P'[e1 .: y1 ..] | RP' y' e' Ry' RIAxy' Re' ]< wl >)
  (Rhr : W[ _ ||-< l > hr : _ | RP x (tRefl A x) Rx (WIdRed RA Rx Rx) (WreflRed' RA Rx)]< wl >)
  (Rhr' : W[ _ ||-< l > hr' : _ | RP' x' (tRefl A' x') Rx' (WIdRed RA' Rx' Rx') (WreflRed' RA' Rx') ]< wl >)
  (Rhrhr' : W[ _ ||-< l > hr ≅ hr' : _ | RP x (tRefl A x) Rx (WIdRed RA Rx Rx) (WreflRed' RA Rx)]< wl >)
  (Ry : W[ _ ||-< l > y : _ | RA]< wl >)
  (Ry' : W[ _ ||-< l > y' : _ | RA']< wl >)
  (Ryy' : W[ _ ||-< l > y ≅ y' : _ | RA]< wl >)
  (RIAxy : [Γ ||-<l> tId A x y]< wl >)
  (RIAxy' : [Γ ||-<l> tId A' x' y']< wl >)
  (WRIAxy : W[Γ ||-<l> tId A x y]< wl >)
  (WRe : W[ _ ||-< l > e : _ | WRIAxy]< wl >) 
  (Re : [ _ ||-< l > e : _ | RIAxy]< wl >) 
  (Re' : [ _ ||-< l > e' : _ | RIAxy']< wl >) 
  (Ree' : [_ ||-< l > e ≅ e' : _ | RIAxy]< wl >)
  (RIAxy0 : [Γ ||-Id<l> tId A x y]< wl >)
  (Pee' : IdPropEq RIAxy0 e e') :
  W[_ ||-< l > tIdElim A x P hr y e ≅ tIdElim A' x' P' hr' y' e' : _ | RP y e Ry _ WRe ]< wl >.
Proof.
  pose proof (IdRedTy_inv RIAxy0) as [eA ex ey].
  (* pose proof (IdRedTy_inv (invLRId RIAxy))) as [eA ex ey].
  pose proof (IdRedTy_inv (invLRId RIAxy')) as [eA' ex' ey']. *)
  pose proof (IdPropEq_whnf _ _ _ Pee') as [whe whe'].
  assert (Rei : [LRId' RIAxy0 | _ ||- e : _]< wl >) by irrelevance.
  assert (Rei' : [LRId' (invLRId RIAxy') | _ ||- e' : _]< wl >) by irrelevance.
  pose proof (IdRedTm_whnf_prop Rei whe).
  pose proof (IdRedTm_whnf_prop Rei' whe').
  eapply WLREqTermHelper.
  1,2: unshelve eapply WidElimPropRed; tea.
  1: now eapply LogtoW.
  1: now eapply TmLogtoW.
  - intros ; eapply RPP' ; tea.
    1: now eapply TmLogtoW.
    now eapply TmEqLogtoW'.
  - destruct Pee'; cbn in *.
    + unshelve erewrite (idElimPropIrr X), (idElimPropIrr X0).
      1,2: now eapply IdProp_refl_inv.
      cbn; eapply WLRTmEqRedConv; tea.
      eapply RPeq; cycle 3; tea.
      1,4: rewrite ex, ey; eapply WtransEqTerm; [|eapply WLRTmEqSym].
      1,2,3,4: Wirrelevance0 ; [ symmetry | now eapply TmEqLogtoW] ; eauto.
      2: now eapply WreflLRTyEq.
      eapply WreflCongRed; tea.
      1: Wirrelevance0 ; [ symmetry | now eapply EqLogtoW] ; eauto.
      rewrite ex ; Wirrelevance0 ; [ symmetry | now eapply TmEqLogtoW] ; eauto.
  + unshelve erewrite (idElimPropIrr X), (idElimPropIrr X0); destruct r; unfold_id_outTy.
    * econstructor; Wescape ; constructor; unfold_id_outTy.
      1: rewrite <- ex, <- ey, <-eA; tea.
      now eapply lrefl.
    * econstructor; pose proof (IdRedTy_inv (invLRId RIAxy')) as [eA' ex' ey'].
      escape ; Wescape; constructor; unfold_id_outTy.
      all: rewrite <- ex', <- ey', <-eA'; tea.
      eapply convneu_conv; [now eapply urefl|].
      rewrite <- ex, <- ey, <-eA; now eapply convty_Id.
    * cbn. Wescape ; escape; eapply WneuTermEq.
      -- now eapply ty_IdElim.
      -- eapply ty_conv; [now eapply ty_IdElim|].
         symmetry; eapply WescapeEq; eapply RPP' ; tea.
         1: now eapply TmLogtoW.
         1: now eapply TmEqLogtoW.
         Unshelve. all: tea.
         now eapply TmLogtoW.
      -- eapply convneu_IdElim; tea.
         now rewrite ex, ey, eA.
Qed.


Lemma WidElimCongRed {wl Γ l A A' x x' P P' hr hr' y y' e e'}
  (RA : W[Γ ||-<l> A]< wl >)
  (RA' : W[Γ ||-<l> A']< wl >)
  (RAA' : W[ Γ ||-< l > A ≅ A' | RA]< wl >)
  (Rx : W[ _ ||-< l > x : _ | RA]< wl >)
  (Rx' : W[ _ ||-< l > x' : _ | RA']< wl >)
  (Rxx' : W[ _ ||-< l > x ≅ x' : _ | RA]< wl >)
  (RP0 : W[Γ ,, A ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) ||-<l> P]< wl >)
  (RP0' : W[Γ ,, A' ,, tId A'⟨@wk1 Γ A'⟩ x'⟨@wk1 Γ A'⟩ (tRel 0) ||-<l> P']< wl >)
  (RPP0 : W[ _ ||-< l > _ ≅ P' | RP0]< wl >)
  (RP : forall wl' (f :  wl' ≤ε wl) (WRA : W[Γ ||-<l> A]< wl' >)
               y e (Ry : W[ Γ ||-< l > y : _ | WRA]< wl' >)
               (RIAxy : W[Γ ||-<l> tId A x y]< wl' >),
    W[ _ ||-< l > e : _ | RIAxy]< wl' > -> W[Γ ||-<l> P[e .: y..]]< wl' >)
  (RP' : forall wl' (f :  wl' ≤ε wl) (WRA' : W[Γ ||-<l> A']< wl' >)
                y' e' (Ry' : W[ Γ ||-< l > y' : _ | WRA']< wl' >)
                (RIAxy' : W[Γ ||-<l> tId A' x' y']< wl' >),
    W[ _ ||-< l > e' : _ | RIAxy']< wl' > -> W[Γ ||-<l> P'[e' .: y'..]]< wl' >)
  (RPP' : forall wl' (f :  wl' ≤ε wl)
                 (WRA : W[Γ ||-<l> A]< wl' >) (WRA' : W[Γ ||-<l> A']< wl' >)
                 y y' e e' 
    (Ry : W[ Γ ||-< l > y : _ | WRA]< wl' >)
    (Ry' : W[ Γ ||-< l > y' : _ | WRA']< wl' >)
    (Ryy' : W[ _ ||-< l > y ≅ y' : _ | WRA]< wl' >)
    (RIAxy : W[Γ ||-<l> tId A x y]< wl' >)
    (RIAxy' : W[Γ ||-<l> tId A' x' y']< wl' >)
    (Re : W[ _ ||-< l > e : _ | RIAxy]< wl' >)
    (Re' : W[ _ ||-< l > e' : _ | RIAxy']< wl' >)
    (Ree' : W[ _ ||-< l > e ≅ e' : _ | RIAxy]< wl' >),
      W[ _ ||-< l > P[e .: y..] ≅ P'[e' .: y'..] | RP wl' f WRA y e Ry _ Re]< wl' >)
  (RPeq : forall wl' (f :  wl' ≤ε wl) A' x' y y' e e'
                 (WRA : W[Γ ||-<l> A]< wl' >)
                 (RA' : W[Γ ||-<l> A']< wl' >)
                 (RAA' : W[ _ ||-< l > _ ≅ A' | WRA]< wl' >)
                 (Rx' : W[ _ ||-< l > x' : _ | WRA]< wl' >)
                 (Rxx' : W[ _ ||-< l > x ≅ x' : _ | WRA]< wl' >)
                 (Ry : W[ Γ ||-< l > y : _ | WRA]< wl' >)
                 (Ry' : W[ _ ||-< l > y' : _ | RA']< wl' >)
                 (Ryy' : W[ Γ ||-< l > y ≅ y' : _ | WRA]< wl' >)
                 (RIAxy : W[Γ ||-<l> tId A x y]< wl' >)
                 (RIAxy' : W[Γ ||-<l> tId A x y']< wl' >)
                 (Re : W[ _ ||-< l > e : _ | RIAxy]< wl' >)
                 (Re' : W[ _ ||-< l > e' : _ | RIAxy']< wl' >)
                 (Ree' : W[ _ ||-< l > e ≅ e' : _ | RIAxy]< wl' >),
      W[Γ ||-< l > P[e .: y..] ≅ P[e' .: y' ..] | RP wl' f WRA y e Ry RIAxy Re]< wl' >)
  (RPeq' : forall wl' (f :  wl' ≤ε wl) A1 x1 y' y1 e' e1
                  (WRA' : W[Γ ||-<l> A']< wl' >)
                  (RA1 : W[Γ ||-<l> A1]< wl' >)
                  (RAA1 : W[ _ ||-< l > _ ≅ A1 | WRA']< wl' >)
                  (Rx1 : W[ _ ||-< l > x1 : _ | WRA']< wl' >)
                  (Rxx1 : W[ _ ||-< l > x' ≅ x1 : _ | WRA']< wl' >)
                  (Ry' : W[ Γ ||-< l > y' : _ | WRA']< wl' >)
                  (Ry1 : W[ _ ||-< l > y1 : _ | RA1]< wl' >)
                  (Ryy1 : W[ Γ ||-< l > y' ≅ y1 : _ | WRA']< wl' >)
                  (RIAxy' : W[Γ ||-<l> tId A' x' y']< wl' >)
                  (RIAxy1 : W[Γ ||-<l> tId A' x' y1]< wl' >)
                  (Re' : W[ _ ||-< l > e' : _ | RIAxy']< wl' >)
                  (Re1 : W[ _ ||-< l > e1 : _ | RIAxy1]< wl' >)
                  (Ree1 : W[ _ ||-< l > e' ≅ e1 : _ | RIAxy']< wl' >),
    W[Γ ||-< l > P'[e' .: y'..] ≅ P'[e1 .: y1 ..] | RP' wl' f WRA' y' e' Ry' RIAxy' Re' ]< wl' >)
  (Rhr : W[ _ ||-< l > hr : _ | RP wl (idε _) RA x (tRefl A x) Rx (WIdRed RA Rx Rx) (WreflRed' RA Rx)]< wl >)
  (Rhr' : W[ _ ||-< l > hr' : _ | RP' _ (idε _) RA' x' (tRefl A' x') Rx' (WIdRed RA' Rx' Rx') (WreflRed' RA' Rx') ]< wl >)
  (Rhrhr' : W[ _ ||-< l > hr ≅ hr' : _ | RP _ (idε _) RA x (tRefl A x) Rx (WIdRed RA Rx Rx) (WreflRed' RA Rx)]< wl >)
  (Ry : W[ _ ||-< l > y : _ | RA]< wl >)
  (Ry' : W[ _ ||-< l > y' : _ | RA']< wl >)
  (Ryy' : W[ _ ||-< l > y ≅ y' : _ | RA]< wl >)
  (WRIAxy : W[Γ ||-<l> tId A x y]< wl >)
  (WRIAxy' : W[Γ ||-<l> tId A' x' y']< wl >)
  (WRe : W[ _ ||-< l > e : _ | WRIAxy]< wl >) 
  (WRe' : W[ _ ||-< l > e' : _ | WRIAxy']< wl >) 
  (WRee' : W[_ ||-< l > e ≅ e' : _ | WRIAxy]< wl >) :
  W[_ ||-< l > tIdElim A x P hr y e ≅ tIdElim A' x' P' hr' y' e' : _ | RP wl (wfLCon_le_id _) RA y e Ry _ WRe ]< wl >.
Proof.
  unshelve eapply TreeTmEqSplit ; [do 3 eapply DTree_fusion ; shelve | ].
  intros wl' Ho HA.
  pose (f:= over_tree_le Ho).
  pose (RIAxy := WRed _ WRIAxy wl' (over_tree_fusion_l (over_tree_fusion_l (over_tree_fusion_l Ho)))).
  pose (RIAxy' := WRed _ WRIAxy' wl' (over_tree_fusion_r (over_tree_fusion_l (over_tree_fusion_l Ho)))).
  unshelve epose (Re := WRedTm _ WRe wl' _ (over_tree_fusion_l (over_tree_fusion_r (over_tree_fusion_l Ho)))).
  1: now do 3 eapply over_tree_fusion_l ; exact Ho.
  unshelve epose (Re' := WRedTm _ WRe' wl' _ (over_tree_fusion_r (over_tree_fusion_r (over_tree_fusion_l Ho)))).
  1: eapply over_tree_fusion_r, over_tree_fusion_l, over_tree_fusion_l ; exact Ho.
  assert (Req : [LRId' (invLRId RIAxy) | _ ||- e ≅ e' : _]< wl' >).
  { irrelevanceRefl ; eapply WRee', over_tree_fusion_l, over_tree_fusion_l, over_tree_fusion_r ; exact Ho.
  }
  cbn in Req; inversion Req; unfold_id_outTy.
  pose proof (IdRedTy_inv (invLRId RIAxy)) as [eA ex ey].
  pose proof redL as [? _]; pose proof redR as [? _].
  rewrite <-eA,<-ex,<-ey in redL, redR.
  pose proof (IdPropEq_whnf _ _ _ prop) as [whL whR].
  pose proof (redTmFwdConv Re redL whL) as [RnfL RnfLeq].
  assert (redR' : [Γ |-[ ta ] e' :⤳*: nfR : tId A' x' y' ]< wl' >).
  { eapply redtmwf_conv ; [eassumption | eapply convty_Ltrans ; [eassumption | ] ] ; escape ; Wescape.
    eapply convty_Id ; now tea.
  }
  epose proof (redTmFwdConv Re' redR' whR) as [RnfR RnfReq].
  eapply WLREqTermHelper ; cycle -1.
  - eapply WLRTmEqRedConv.
    2: eapply WidElimPropCongRed.
    17: exact prop.
    all: try (now eapply WLtrans) + (now eapply WEq_Ltrans) + (now eapply WTm_Ltrans) + (now eapply WTmEq_Ltrans).
    all: try (now eapply WEq_Ltrans') + (now eapply WTm_Ltrans') + (now eapply WTmEq_Ltrans').
    all: tea.
    + eapply RPeq; cycle 2; first [eapply WreflLRTmEq | eapply WLRTmEqSym| eapply WreflLRTyEq| tea].
      1,2,3,4,6: now eapply WTm_Ltrans.
      now eapply TmEqLogtoW.
    + intros ; unshelve eapply RPP' ; now eauto.
    + intros ; unshelve eapply RPeq ; cycle 6 ; eassumption.
    + intros ; unshelve eapply RPeq' ; cycle 11 ; eassumption.
    + enough [LRId' (invLRId RIAxy) | _ ||- nfL ≅ nfR : _]< wl' > by irrelevance.
      exists nfL nfR; tea; eapply redtmwf_refl; unfold_id_outTy; tea.
  - assert (Re1 : [LRId' (invLRId RIAxy) | _ ||- e : _]< wl' >) by irrelevance.
    rewrite (redtmwf_det whL (IdProp_whnf _ _ Re1.(IdRedTm.prop)) redL Re1.(IdRedTm.red)).
    cbn ; Wirrelevance0 ; [ reflexivity | ] ; eapply WidElimRed ; tea.
    + now eapply WLtrans.
    + intros ; unshelve eapply RPeq ; cycle 11 ; try eassumption.
      now eapply WLtrans.
    + now eapply WTm_Ltrans'.
  - assert (Re1' : [LRId' (invLRId RIAxy') | _ ||- e' : _]< wl' >) by irrelevance.
    rewrite (redtmwf_det whR (IdProp_whnf _ _ Re1'.(IdRedTm.prop)) redR Re1'.(IdRedTm.red)).
    cbn ; Wirrelevance0 ; [ reflexivity | ] ; eapply WidElimRed ; tea.
    + now eapply WLtrans.
    + intros ; unshelve eapply RPeq' ; cycle 11 ; try eassumption.
      now eapply WLtrans.
    + now eapply WTm_Ltrans'.
  - cbn ; Wirrelevance0 ; [ reflexivity | eapply RPP'].
    1,3: now eapply WTm_Ltrans.
    all: now eapply WTmEq_Ltrans.
    Unshelve. 
    all: tea.
    4: exact (over_tree_fusion_l (over_tree_fusion_l (over_tree_fusion_l Ho))).
    1-3: now constructor.
    1:unshelve eapply RP' ; eauto.
    all: try (now eapply WLtrans) + (now eapply WEq_Ltrans) + (now eapply WTm_Ltrans) + (now eapply WTmEq_Ltrans).
    now eapply TmLogtoW.
Qed.
  
Lemma idElimCongRed {wl Γ l A A' x x' P P' hr hr' y y' e e'}
  (RA : [Γ ||-<l> A]< wl >)
  (RA' : [Γ ||-<l> A']< wl >)
  (RAA' : [RA | Γ ||- A ≅ A']< wl >)
  (Rx : [RA | _ ||- x : _]< wl >)
  (Rx' : [RA' | _ ||- x' : _]< wl >)
  (Rxx' : [RA | _ ||- x ≅ x' : _]< wl >)
  (RP0 : [Γ ,, A ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) ||-<l> P]< wl >)
  (RP0' : [Γ ,, A' ,, tId A'⟨@wk1 Γ A'⟩ x'⟨@wk1 Γ A'⟩ (tRel 0) ||-<l> P']< wl >)
  (RPP0 : [RP0 | _ ||- _ ≅ P']< wl >)
  (RP : forall y e (Ry : [RA | Γ ||- y : _]< wl >) (RIAxy : [Γ ||-<l> tId A x y]< wl >),
    [RIAxy | _ ||- e : _]< wl > -> [Γ ||-<l> P[e .: y..]]< wl >)
  (RP' : forall y' e' (Ry' : [RA' | Γ ||- y' : _]< wl >) (RIAxy' : [Γ ||-<l> tId A' x' y']< wl >),
    [ RIAxy' | _ ||- e' : _]< wl > -> [Γ ||-<l> P'[e' .: y'..]]< wl >)
  (RPP' : forall y y' e e' 
    (Ry : [RA | Γ ||- y : _]< wl >)
    (Ry' : [RA' | Γ ||- y' : _]< wl >)
    (Ryy' : [RA | _ ||- y ≅ y' : _]< wl >)
    (RIAxy : [Γ ||-<l> tId A x y]< wl >)
    (RIAxy' : [Γ ||-<l> tId A' x' y']< wl >)
    (Re : [RIAxy | _ ||- e : _]< wl >)
    (Re' : [ RIAxy' | _ ||- e' : _]< wl >)
    (Ree' : [RIAxy | _ ||- e ≅ e' : _]< wl >),
    [RP y e Ry _ Re | _ ||- P[e .: y..] ≅ P'[e' .: y'..]]< wl >)
  (RPeq : forall A' x' y y' e e' 
    (RA' : [Γ ||-<l> A']< wl >)
    (RAA' : [RA | _ ||- _ ≅ A']< wl >)
    (Rx' : [RA | _ ||- x' : _]< wl >)
    (Rxx' : [RA | _ ||- x ≅ x' : _]< wl >)
    (Ry : [RA | Γ ||- y : _]< wl >)
    (Ry' : [RA' | _ ||- y' : _]< wl >)
    (Ryy' : [RA | Γ ||- y ≅ y' : _]< wl >)
    (RIAxy : [Γ ||-<l> tId A x y]< wl >)
    (RIAxy' : [Γ ||-<l> tId A x y']< wl >)
    (Re : [RIAxy | _ ||- e : _]< wl >)
    (Re' : [ RIAxy' | _ ||- e' : _]< wl >)
    (Ree' : [RIAxy | _ ||- e ≅ e' : _]< wl >),
    [RP y e Ry RIAxy Re | Γ ||- P[e .: y..] ≅ P[e' .: y' ..]]< wl >)
  (RPeq' : forall A1 x1 y' y1 e' e1 
    (RA1 : [Γ ||-<l> A1]< wl >)
    (RAA1 : [RA' | _ ||- _ ≅ A1]< wl >)
    (Rx1 : [RA' | _ ||- x1 : _]< wl >)
    (Rxx1 : [RA' | _ ||- x' ≅ x1 : _]< wl >)
    (Ry' : [RA' | Γ ||- y' : _]< wl >)
    (Ry1 : [RA1 | _ ||- y1 : _]< wl >)
    (Ryy1 : [RA' | Γ ||- y' ≅ y1 : _]< wl >)
    (RIAxy' : [Γ ||-<l> tId A' x' y']< wl >)
    (RIAxy1 : [Γ ||-<l> tId A' x' y1]< wl >)
    (Re' : [ RIAxy' | _ ||- e' : _]< wl >)
    (Re1 : [ RIAxy1 | _ ||- e1 : _]< wl >)
    (Ree1 : [ RIAxy' | _ ||- e' ≅ e1 : _]< wl >),
    [RP' y' e' Ry' RIAxy' Re' | Γ ||- P'[e' .: y'..] ≅ P'[e1 .: y1 ..]]< wl >)
  (Rhr : [RP x (tRefl A x) Rx (IdRed RA Rx Rx) (reflRed' RA Rx) | _ ||- hr : _]< wl >)
  (Rhr' : [RP' x' (tRefl A' x') Rx' (IdRed RA' Rx' Rx') (reflRed' RA' Rx') | _ ||- hr' : _]< wl >)
  (Rhrhr' : [RP x (tRefl A x) Rx (IdRed RA Rx Rx) (reflRed' RA Rx) | _ ||- hr ≅ hr' : _]< wl >)
  (Ry : [RA | _ ||- y : _]< wl >)
  (Ry' : [RA' | _ ||- y' : _]< wl >)
  (Ryy' : [RA | _ ||- y ≅ y' : _]< wl >)
  (RIAxy : [Γ ||-<l> tId A x y]< wl >)
  (RIAxy' : [Γ ||-<l> tId A' x' y']< wl >)
  (Re : [RIAxy | _ ||- e : _]< wl >) 
  (Re' : [RIAxy' | _ ||- e' : _]< wl >) 
  (Ree' : [RIAxy | _ ||- e ≅ e' : _]< wl >)  :
  [RP y e Ry _ Re | _ ||- tIdElim A x P hr y e ≅ tIdElim A' x' P' hr' y' e' : _]< wl >.
Proof.
  pose proof (IdRedTy_inv (invLRId RIAxy)) as [eA ex ey].
  assert (RIAxyeq : [RIAxy | _ ||- _ ≅ tId A' x' y']< wl >) by (escape; now eapply IdCongRed).
  assert (Req : [LRId' (invLRId RIAxy) | _ ||- e ≅ e' : _]< wl >) by irrelevance.
  cbn in Req; inversion Req; unfold_id_outTy.
  pose proof redL as [? _]; pose proof redR as [? _].
  rewrite <-eA,<-ex,<-ey in redL, redR.
  pose proof (IdPropEq_whnf _ _ _ prop) as [whL whR].
  pose proof (redTmFwdConv Re redL whL) as [RnfL RnfLeq].
  unshelve epose proof (redTmFwdConv Re' _ whR) as [RnfR RnfReq].
  1: eapply redtmwf_conv; tea; now escape.
  eapply LREqTermHelper; cycle -1.
  - eapply LRTmEqRedConv.
    2: eapply idElimPropCongRed.
    16: exact prop.
    all: tea.
    1: eapply RPeq; cycle 2; first [now eapply reflLRTmEq | now eapply LRTmEqSym| eapply reflLRTyEq| tea].
    enough [LRId' (invLRId RIAxy) | _ ||- nfL ≅ nfR : _]< wl > by irrelevance.
    exists nfL nfR; tea; eapply redtmwf_refl; unfold_id_outTy; tea.
  - assert (Re1 : [LRId' (invLRId RIAxy) | _ ||- e : _]< wl >) by irrelevance.
    rewrite (redtmwf_det whL (IdProp_whnf _ _ Re1.(IdRedTm.prop)) redL Re1.(IdRedTm.red)).
    irrelevanceRefl; eapply idElimRed; tea.
  - assert (Re1' : [LRId' (invLRId RIAxy') | _ ||- e' : _]< wl >) by irrelevance.
    rewrite (redtmwf_det whR (IdProp_whnf _ _ Re1'.(IdRedTm.prop)) redR Re1'.(IdRedTm.red)).
    irrelevanceRefl; eapply idElimRed; tea.
    Unshelve. 
    all: tea.
    now eapply RP'.
  - now eapply RPP'.
Qed.

End IdRed.
