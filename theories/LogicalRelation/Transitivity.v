Require Import PeanoNat.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Notations Utils BasicAst LContexts Context NormalForms Weakening GenericTyping Monad LogicalRelation DeclarativeInstance.
From LogRel.LogicalRelation Require Import Induction ShapeView Reflexivity Irrelevance.

Set Universe Polymorphism.

Section Transitivity.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.

(*Set Printing Universes.*)

 Lemma transEq@{i j k l} {wl Γ A B C lA lB} 
  {RA : [LogRel@{i j k l} lA | Γ ||- A]< wl >}
  {RB : [LogRel@{i j k l} lB | Γ ||- B]< wl >}
  (RAB : [Γ ||-<lA> A ≅ B | RA]< wl >)
   (RBC : [Γ ||-<lB> B ≅ C | RB]< wl >) :
  [Γ ||-<lA> A ≅ C | RA]< wl >.
 Proof. now eapply LRTransEq. Qed.

 Lemma WtransEq@{i j k l} {wl Γ A B C lA lB} 
  {RA : WLogRel@{i j k l} lA wl Γ A }
  {RB : WLogRel@{i j k l} lB wl Γ B }
  (RAB : W[Γ ||-<lA> A ≅ B | RA]< wl >)
   (RBC : W[Γ ||-<lB> B ≅ C | RB]< wl >) :
  W[Γ ||-<lA> A ≅ C | RA]< wl >.
 Proof. now eapply WLRTransEq. Qed.


Lemma transEqTermU@{h i j k} {wl Γ l UU t u v} {h : [Γ ||-U<l> UU]< wl >} :
  [LogRelRec@{i j k} l | Γ ||-U t ≅ u : UU| h]< wl > ->
  [LogRelRec@{i j k} l | Γ ||-U u ≅ v : UU| h]< wl > ->
  [LogRelRec@{i j k} l | Γ ||-U t ≅ v : UU| h]< wl >.
Proof.
  intros [rL ?? redL] [? rR] ; exists rL rR redL; tea.
  + etransitivity; tea.
    unshelve erewrite (redtmwf_det _ _ (URedTm.red redR) (URedTm.red redL0))  ; tea.
    all: apply isType_whnf; apply URedTm.type.
  + apply TyEqRecFwd; unshelve eapply transEq@{h i j k}.
    4,5: now apply (TyEqRecFwd h). 
Qed.

Lemma transEqTermNeu {wl Γ A t u v} {RA : [Γ ||-ne A]< wl >} :
  [Γ ||-ne t ≅ u : A | RA]< wl > ->
  [Γ ||-ne u ≅ v : A | RA]< wl > ->
  [Γ ||-ne t ≅ v : A| RA]< wl >.
Proof.
  intros [tL] [? tR]; exists tL tR; tea.
  etransitivity; tea.
  unshelve erewrite (redtmwf_det _ _ redR redL0); tea.
  all: eapply whnf_whne, convneu_whne; first [eassumption|symmetry; eassumption].
Qed.


Lemma transEqTermΠ {wl Γ lA A t u v} {ΠA : [Γ ||-Π<lA> A]< wl >}
  (ihdom : forall (Δ : context) wl' (ρ : Δ ≤ Γ) (f : wl' ≤ε wl) (h : [ |-[ ta ] Δ]< wl' >) (t u v : term),
    [PolyRed.shpRed ΠA ρ f h | Δ ||- t ≅ u : _]< wl' > ->
    [PolyRed.shpRed ΠA ρ f h | Δ ||- u ≅ v : _]< wl' > ->
    [PolyRed.shpRed ΠA ρ f h | Δ ||- t ≅ v : _]< wl' >)
  (ihcod : forall (Δ : context) wl' (a : term) (ρ : Δ ≤ Γ) (f : wl' ≤ε wl) (h : [ |-[ ta ] Δ]< wl' >)
                  (ha : [PolyRed.shpRed ΠA ρ f h | Δ ||- a : _]< wl' >) wl''
                  (Hover : over_tree wl' wl'' (PolyRed.posTree ΠA ρ f h ha)) (t u v : term),
    [PolyRed.posRed ΠA ρ f h ha Hover | Δ ||- t ≅ u : _]< wl'' > ->
    [PolyRed.posRed ΠA ρ f h ha Hover | Δ ||- u ≅ v : _]< wl'' > ->
    [PolyRed.posRed ΠA ρ f h ha Hover | Δ ||- t ≅ v : _]< wl'' >) :
  [Γ ||-Π t ≅ u : A | ΠA ]< wl > ->
  [Γ ||-Π u ≅ v : A | ΠA ]< wl > ->
  [Γ ||-Π t ≅ v : A | ΠA ]< wl >.
Proof.
  intros [tL] [? tR].
  assert (forall t (red : [Γ ||-Π t : _ | ΠA]< wl >), whnf (PiRedTm.nf red)).
  { intros ? [? ? ? ? isfun]; simpl ; destruct isfun; constructor; tea.
    now eapply convneu_whne. }
  unshelve epose proof (e := redtmwf_det _ _ (PiRedTm.red redR) (PiRedTm.red redL)); tea.
  1,2: now eauto.  
  unshelve eexists ; [exact tL | exact tR | ..].
  - intros ; do 2 (eapply DTree_fusion).
    + eapply eqTree ; eauto.
    + eapply eqTree0 ; eauto.
    + eapply (PiRedTm.appTree tL) ; eauto.
    + eapply (PiRedTm.appTree tR) ; eauto.
  - etransitivity; tea. now rewrite e.
  - intros ; eapply ihcod.
    1: eapply eqApp ; cbn in * ; now do 2 (eapply over_tree_fusion_l).
    rewrite e; apply eqApp0.
    now eapply over_tree_fusion_r, over_tree_fusion_l.
Qed.

Lemma transEqTermΣ {wl Γ lA A t u v} {ΣA : [Γ ||-Σ<lA> A]< wl >}
  (ihdom : forall (Δ : context) wl' (ρ : Δ ≤ Γ) (f : wl' ≤ε wl) (h : [ |-[ ta ] Δ]< wl' >) (t u v : term),
    [PolyRed.shpRed ΣA ρ f h | Δ ||- t ≅ u : _]< wl' > ->
    [PolyRed.shpRed ΣA ρ f h | Δ ||- u ≅ v : _]< wl' > ->
    [PolyRed.shpRed ΣA ρ f h | Δ ||- t ≅ v : _]< wl' >)
  (ihcod : forall (Δ : context) wl' (a : term) (ρ : Δ ≤ Γ) (f : wl' ≤ε wl) (h : [ |-[ ta ] Δ]< wl' >)
                  (ha : [PolyRed.shpRed ΣA ρ f h | Δ ||- a : _]< wl' >)  wl'' 
                  (Hover : over_tree wl' wl'' (PolyRed.posTree ΣA ρ f h ha)) (t u v : term),
    [PolyRed.posRed ΣA ρ f h ha Hover | Δ ||- t ≅ u : _]< wl'' > ->
    [PolyRed.posRed ΣA ρ f h ha Hover | Δ ||- u ≅ v : _]< wl'' > ->
    [PolyRed.posRed ΣA ρ f h ha Hover | Δ ||- t ≅ v : _]< wl'' >) :
  [Γ ||-Σ t ≅ u : A | ΣA ]< wl > ->
  [Γ ||-Σ u ≅ v : A | ΣA ]< wl > ->
  [Γ ||-Σ t ≅ v : A | ΣA ]< wl >.
Proof.
  intros [tL ?? eqfst eqtree eqsnd] [? tR ? eqfst' eqtree' eqsnd'].
  assert (forall t (red : [Γ ||-Σ t : _ | ΣA]< wl >), whnf (SigRedTm.nf red)).
  { intros ? [? ? ? ? ? ispair]; simpl ; destruct ispair; constructor; tea.
    now eapply convneu_whne. }
  unshelve epose proof (e := redtmwf_det _ _ (SigRedTm.red redR) (SigRedTm.red redL)); tea.
  1,2: now eauto.
  unshelve eexists ; [exact tL | exact tR |..].
  - intros ; eapply DTree_fusion ; [eapply DTree_fusion | ].
    + eapply eqtree ; eauto.
    + eapply eqtree' ; eauto.
    + eapply (PolyRed.posTree ΣA ρ f Hd (SigRedTm.fstRed redL ρ f Hd)).
  - etransitivity; tea. now rewrite e.
  - intros; eapply ihdom ; [eapply eqfst| rewrite e; eapply eqfst'].
  - intros; eapply ihcod; [eapply eqsnd|] ; cbn in *.
    + now do 2 (eapply over_tree_fusion_l).
    + rewrite e. 
      eapply LRTmEqRedConv.
      2: eapply eqsnd'.
      eapply PolyRed.posExt.
      1: eapply (SigRedTm.fstRed tL).
      eapply LRTmEqSym. rewrite <- e.
      eapply eqfst.
      now eapply over_tree_fusion_r, over_tree_fusion_l.
      Unshelve.
      now eapply over_tree_fusion_r.
Qed.


Lemma transNeNfEq {wl Γ t u v A} :
  [Γ ||-NeNf t ≅ u : A]< wl > ->
  [Γ ||-NeNf u ≅ v : A]< wl > ->
  [Γ ||-NeNf t ≅ v : A]< wl >.
Proof.
  intros [] []; econstructor; tea; now etransitivity.
Qed.

Lemma transEqTermNat {wl Γ A} (NA : [Γ ||-Nat A]< wl >) :
  (forall t u, 
    [Γ ||-Nat t ≅ u : A | NA]< wl > -> forall v,
    [Γ ||-Nat u ≅ v : A | NA]< wl > ->  
    [Γ ||-Nat t ≅ v : A | NA]< wl >) ×
  (forall t u,
    NatPropEq NA t u -> forall v,
    NatPropEq NA u v ->
    NatPropEq NA t v).
Proof.
  apply NatRedEqInduction.
  - intros * ???? ih ? uv; inversion uv; subst.
    destruct (NatPropEq_whnf prop), (NatPropEq_whnf prop0). 
    unshelve epose proof (redtmwf_det _ _ redR redL0); tea; subst.
    econstructor; tea.
    1: now etransitivity.
    now eapply ih.
  - easy.
  - intros * ? ih ? uv.
    inversion uv ; subst.
    + econstructor; now eapply ih.
    + match goal with H : [_ ||-NeNf _ ≅ _ : _ ]< wl > |- _ => destruct H; apply convneu_whne in conv; inv_whne end.
  - intros ?? tu ? uv; inversion uv; subst.
    1,2: destruct tu; symmetry in conv; apply convneu_whne in conv; inv_whne.
    econstructor; now eapply transNeNfEq.
Qed.

Lemma and_two P Q : Q -> (Q -> P) -> (P × Q).
Proof.
  firstorder.
Qed.

Lemma transEqTermEmpty {wl Γ A} (NA : [Γ ||-Empty A]< wl >) :
  (forall t u, 
    [Γ ||-Empty t ≅ u : A | NA]< wl > -> forall v,
    [Γ ||-Empty u ≅ v : A | NA]< wl > ->  
    [Γ ||-Empty t ≅ v : A | NA]< wl >) ×
  (forall t u,
    EmptyPropEq wl Γ t u -> forall v,
    EmptyPropEq wl Γ u v ->
    EmptyPropEq wl Γ t v).
Proof.
  eapply and_two.
  - intros ?? tu ? uv; inversion uv; subst.
    destruct tu.
    econstructor; now eapply transNeNfEq.
  - intros HH.
    intros t u tu v uv. inversion uv; subst.
    inversion tu; subst.
    unshelve eapply EmptyPropEq_whnf in prop as HH1. 2: tea. destruct HH1.
    unshelve eapply EmptyPropEq_whnf in prop0 as HH2. 2: tea. destruct HH2.
    unshelve epose proof (redtmwf_det _ _ redL redR0); tea; subst.
    econstructor; tea.
    1: now etransitivity.
    eapply HH; eauto.
Qed.


Lemma transEqTermBool {wl Γ A} (NA : [Γ ||-Bool A]< wl >) :
  (forall t u, 
    [Γ ||-Bool t ≅ u : A | NA]< wl > -> forall v,
    [Γ ||-Bool u ≅ v : A | NA]< wl > ->  
    [Γ ||-Bool t ≅ v : A | NA]< wl >) ×
  (forall t u,
    BoolPropEq NA t u -> forall v,
    BoolPropEq NA u v ->
    BoolPropEq NA t v).
Proof.
  eapply and_two.
  - intros * ih ? uv; inversion uv; inversion ih ; subst.
    all: auto ; try now econstructor.
    econstructor ; now eapply transNeNfEq.
  - intros HH.
    intros t u tu v uv. inversion uv; subst.
    inversion tu; subst.
    unshelve eapply BoolPropEq_whnf in prop as HH1. destruct HH1.
    unshelve eapply BoolPropEq_whnf in prop0 as HH2. destruct HH2.
    unshelve epose proof (redtmwf_det _ _ redL redR0); tea; subst.
    econstructor; tea.
    1: now etransitivity.
    eapply HH; eauto.
Qed.


Lemma transIdPropEq {wl Γ l A} (IA : [Γ ||-Id<l> A]< wl >) t u v :
  IdPropEq IA t u -> IdPropEq IA u v -> IdPropEq IA t v.
Proof.
  intros [] h; inversion h; subst.
  - now econstructor.
  - match goal with H : [_ ||-NeNf _ ≅ _ : _ ]< wl > |- _ => destruct H; apply convneu_whne in conv; inv_whne end.
  - match goal with H : [_ ||-NeNf _ ≅ _ : _ ]< wl > |- _ => destruct H; symmetry in conv; apply convneu_whne in conv; inv_whne end.
  - econstructor; now eapply transNeNfEq.
Qed.

Lemma IdPropEq_whnf {wl Γ l A} (IA : [Γ ||-Id<l> A]< wl >) t u : IdPropEq IA t u -> whnf t × whnf u.
Proof.
  intros []; split; constructor; destruct r; eapply convneu_whne; tea; now symmetry.
Qed.

Lemma transTmEqId {wl Γ l A} (IA : [Γ ||-Id<l> A]< wl >) t u v :
  [Γ ||-Id<l> t ≅ u : _ | IA]< wl > -> [Γ ||-Id<l> u ≅ v : _| IA]< wl > -> [Γ ||-Id<l> t ≅ v : _| IA]< wl >.
Proof.
  intros [??? red ? prop] [?? red' ?? prop'].
  pose proof prop as [_ wh]%IdPropEq_whnf.
  pose proof prop' as [wh' _]%IdPropEq_whnf.
  pose proof (redtmwf_det wh wh' red red'); subst.
  unshelve econstructor; cycle 2; tea.
  1: now etransitivity.
  now eapply transIdPropEq.
Qed.


Lemma transEqTerm@{h i j k l} {wl Γ lA A t u v} 
  {RA : [LogRel@{i j k l} lA | Γ ||- A]< wl >} :
  [Γ ||-<lA> t ≅ u : A | RA]< wl > ->
  [Γ ||-<lA> u ≅ v : A | RA]< wl > ->
  [Γ ||-<lA> t ≅ v : A | RA]< wl >.
Proof. 
  revert t u v; pattern lA, wl, Γ, A, RA; apply LR_rect_TyUr; clear lA wl Γ A RA; intros l wl Γ.
  - intros *; apply transEqTermU@{h i j k}.
  - intros *; apply transEqTermNeu.
  - intros * ?????. apply transEqTermΠ; tea.
  - intros ? NA **; now eapply (fst (transEqTermNat NA)).
  - intros ? NA **; now eapply (fst (transEqTermBool NA)).
  - intros ? NA **; now eapply (fst (transEqTermEmpty NA)).
  - intros * ?????; apply transEqTermΣ; tea.
  - intros; now eapply transTmEqId.
Qed.

Lemma WtransEqTerm@{h i j k l} {wl Γ lA A t u v} 
  {RA : WLogRel@{i j k l} lA wl Γ A} :
  W[Γ ||-<lA> t ≅ u : A | RA]< wl > ->
  W[Γ ||-<lA> u ≅ v : A | RA]< wl > ->
  W[Γ ||-<lA> t ≅ v : A | RA]< wl >.
Proof.
  intros [d Hd] [d' Hd'].
  exists (DTree_fusion _ d d').
  intros wl' Hover Hover' ; eapply transEqTerm.
  - eapply Hd ; now eapply over_tree_fusion_l.
  - eapply Hd' ; now eapply over_tree_fusion_r.
Qed.  

#[global]
Instance perLRTmEq@{i j k l} {wl Γ l A} (RA : [LogRel@{i j k l} l | Γ ||- A]< wl >):
  Coq.Classes.CRelationClasses.PER (fun t u => [RA | _ ||- t ≅ u : _]< wl >).
Proof.
  econstructor.
  - intros ???; now eapply LRTmEqSym.
  - intros ???; now eapply transEqTerm.
Qed.

#[global]
Instance perWLRTmEq@{i j k l} {wl Γ l A} (RA : WLogRel@{i j k l} l wl Γ A):
  Coq.Classes.CRelationClasses.PER@{Set k} (fun t u => W[ _ ||-< l > t ≅ u : _ | RA]< wl >).
Proof.
  econstructor.
  - intros ???; now eapply WLRTmEqSym.
  - intros ???; now eapply WtransEqTerm.
Qed.

Lemma LREqTermSymConv {wl Γ t u G G' l RG RG'} :
  [Γ ||-<l> t ≅ u : G | RG]< wl > -> 
  [Γ ||-<l> G' ≅ G | RG']< wl > ->
  [Γ ||-<l> u ≅ t : G' | RG']< wl >.
Proof.
  intros Rtu RGG'.
  eapply LRTmEqSym; eapply LRTmEqRedConv; tea.
  now eapply LRTyEqSym.
Qed.

Lemma WLREqTermSymConv {wl Γ t u G G' l RG RG'} :
  W[Γ ||-<l> t ≅ u : G | RG]< wl > -> 
  W[Γ ||-<l> G' ≅ G | RG']< wl > ->
  W[Γ ||-<l> u ≅ t : G' | RG']< wl >.
Proof.
  intros Rtu RGG'.
  eapply WLRTmEqSym; eapply WLRTmEqRedConv; tea.
  now eapply WLRTyEqSym.
Qed.

Lemma LREqTermHelper {wl Γ t t' u u' G G' l RG RG'} :
  [Γ ||-<l> t ≅ u : G | RG]< wl > -> 
  [Γ ||-<l> t' ≅ u' : G' | RG']< wl > -> 
  [Γ ||-<l> G ≅ G' | RG]< wl > ->
  [Γ ||-<l> u ≅ u' : G | RG]< wl > -> 
  [Γ ||-<l> t ≅ t' : G | RG]< wl >.
Proof.
  intros Rtu Rtu' RGG' Ruu'.
  do 2  (eapply transEqTerm; tea).
  now eapply LREqTermSymConv.
Qed.

Lemma WLREqTermHelper {wl Γ t t' u u' G G' l RG RG'} :
  W[Γ ||-<l> t ≅ u : G | RG]< wl > -> 
  W[Γ ||-<l> t' ≅ u' : G' | RG']< wl > -> 
  W[Γ ||-<l> G ≅ G' | RG]< wl > ->
  W[Γ ||-<l> u ≅ u' : G | RG]< wl > -> 
  W[Γ ||-<l> t ≅ t' : G | RG]< wl >.
Proof.
  intros Rtu Rtu' RGG' Ruu'.
  do 2  (eapply WtransEqTerm; tea).
  now eapply WLREqTermSymConv.
Qed. 

End Transitivity.


