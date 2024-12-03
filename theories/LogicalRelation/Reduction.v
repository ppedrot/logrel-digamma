(* From Coq.Classes Require Import CRelationClasses. *)
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Notations Utils BasicAst LContexts Context NormalForms UntypedReduction Weakening GenericTyping Monad LogicalRelation DeclarativeInstance.
From LogRel.LogicalRelation Require Import Induction Reflexivity Universe Escape Irrelevance.

Set Universe Polymorphism.

Section Reduction.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.

Lemma redSubst {wl Γ A B l} :
  [Γ ||-<l> B]< wl > ->
  [Γ |- A ⤳* B]< wl > ->
  ∑ (RA : [Γ ||-<l> A]< wl >), [Γ ||-<l> A ≅ B | RA]< wl >.
Proof.
  intros RB; revert A; pattern l, wl, Γ, B, RB; apply LR_rect_TyUr; clear l wl Γ B RB; intros l wl Γ.
  - intros ? [] ? redA. unshelve eexists.
    + apply LRU_; econstructor; tea; etransitivity; tea.
      constructor; tea; gen_typing.
    + now constructor.
  - intros B [t] A ?. unshelve eexists.
    + apply LRne_; exists t; tea; etransitivity; tea.
      constructor; tea; gen_typing.
    + exists t; tea.
  - intros B [dom cod] A ? ihdom ihcod; cbn in *; unshelve eexists.
    + apply LRPi'; unshelve eexists dom cod ; tea; etransitivity; tea.
      constructor; tea; gen_typing.
    + unshelve eexists dom cod ; tea; cbn.
      unshelve econstructor;intros.
      2,3: apply reflLRTyEq.
      now eapply leaf.
  - intros B [red] A ?; unshelve eexists.
    + apply LRNat_; constructor; tea; etransitivity; tea.
      constructor; tea; gen_typing.
    + now constructor.
  - intros B [red] A ?; unshelve eexists.
    + apply LRBool_; constructor; tea; etransitivity; tea.
      constructor; tea; gen_typing.
    + now constructor.
  - intros B [red] A ?; unshelve eexists.
    + apply LREmpty_; constructor; tea; etransitivity; tea.
      constructor; tea; gen_typing.
    + now constructor.
  - intros B [dom cod] A ? ihdom ihcod; cbn in *; unshelve eexists.
    + apply LRSig'; unshelve eexists dom cod; tea; etransitivity; tea.
      constructor; tea; gen_typing.
    + unshelve eexists dom cod; tea; cbn.
      unshelve econstructor;intros; try now apply reflLRTyEq.
      now eapply leaf.
  - intros ? [ty lhs rhs] ih _ X redX; unshelve eexists.
    + apply LRId'; unshelve eexists ty lhs rhs _ _; tea.
      etransitivity; tea; constructor; tea; gen_typing.
    + exists ty lhs rhs; tea; eapply reflLRTyEq.
Qed.

Lemma WredSubst {wl Γ A B l} :
  W[Γ ||-<l> B]< wl > ->
  [Γ |- A ⤳* B]< wl > ->
  ∑ (RA : W[Γ ||-<l> A]< wl >), W[Γ ||-<l> A ≅ B | RA]< wl >.
Proof.
  intros [] ?.
  unshelve econstructor.
  - exists WT.
    intros.
    eapply redSubst.
    + eapply WRed ; try assumption.
    + eapply redty_Ltrans ; eauto.
      now eapply over_tree_le.
  - exists WT.
    cbn ; intros.
    now destruct (redSubst (WRed wl' Hover) (redty_Ltrans (over_tree_le Hover) H10)).
Qed.   
    
Lemma redwfSubst {wl Γ A B l} :
  [Γ ||-<l> B]< wl > ->
  [Γ |- A :⤳*: B]< wl > ->
  ∑ (RA : [Γ ||-<l> A]< wl >), [Γ ||-<l> A ≅ B | RA]< wl >.
Proof.
  intros ? []; now eapply redSubst.
Qed.

Lemma redSubstTerm {wl Γ A t u l} (RA : [Γ ||-<l> A]< wl >) :
  [Γ ||-<l> u : A | RA]< wl > ->
  [Γ |- t ⤳* u : A ]< wl > ->
  [Γ ||-<l> t : A | RA]< wl > × [Γ ||-<l> t ≅ u : A | RA]< wl >.
Proof.
  revert t u; pattern l, wl, Γ, A, RA; apply LR_rect_TyUr; clear l wl Γ A RA; intros l wl Γ.
  - intros ? h ?? ru' redtu; pose (ru := ru'); destruct ru' as [T].
    assert [Γ |- A ≅ U]< wl > by (destruct h; gen_typing).
    assert [Γ |- t : U]< wl > by (eapply ty_conv; [gen_typing| now escape]).
    assert (redtu' : [Γ |-[ ta ] t ⤳* u]< wl >) by gen_typing.
    destruct (redSubst (A:=t) (RedTyRecFwd h rel) redtu') as [rTyt0].
    pose proof (rTyt := RedTyRecBwd h rTyt0).
    unshelve refine (let rt : [LRU_ h | Γ ||- t : A]< wl >:= _ in _).
    + exists T; tea; constructor; destruct red; tea.
      etransitivity; tea; eapply redtm_conv; tea; now escape.
    + split; tea; exists rt ru rTyt; tea.
      apply TyEqRecFwd; irrelevance.
  - intros ???? ru' ?; pose (ru := ru'); destruct ru' as [n].
    assert [Γ |- A ≅ neRedTy.ty neA]< wl >. 1:{
      destruct neA; cbn in *.
      eapply convty_exp.
       2: apply redtywf_refl; gen_typing.
       2: apply convty_term, convtm_convneu ; eauto.
       gen_typing.
       now constructor.
    }
    assert [Γ |-[ ta ] t ⤳* u : neRedTy.ty neA]< wl > by (eapply redtm_conv; tea). 
    assert [Γ |-[ ta ] t : neRedTy.ty neA]< wl > by (eapply ty_conv; tea; gen_typing). 
    unshelve refine (let rt : [LRne_ l neA | Γ ||- t : A]< wl > := _ in _).
    + exists n; tea; destruct red; constructor; tea; now etransitivity.
    + split; tea; exists n n; tea; destruct red; constructor; tea; now etransitivity. 
  - intros ? ΠA ihdom ihcod ?? ru' ?; pose (ru := ru'); destruct ru' as [f].
    assert [Γ |- A ≅ ΠA.(outTy)]< wl >. 1:{
      destruct ΠA as [?? []]. cbn in *.
      eapply convty_exp; tea.
      now apply redtywf_refl.
    }
    assert [Γ |-[ ta ] t ⤳* u : ΠA.(outTy)]< wl > by now eapply redtm_conv. 
    assert [Γ |-[ ta ] t : ΠA.(outTy)]< wl > by (eapply ty_conv; gen_typing).
    unshelve refine (let rt : [LRPi' ΠA | Γ ||- t : A]< wl > := _ in _).
    1: exists f appTree ; tea ; constructor ; destruct red ; tea ; etransitivity ; tea.
    split; tea; unshelve eexists ; tea.
    intros; cbn. eapply eq; tea.
    now apply reflLRTmEq.
  - intros ? NA t ? Ru red; inversion Ru; subst.
    assert [Γ |- A ≅ tNat]< wl > by (destruct NA; gen_typing).
    assert [Γ |- t :⤳*: nf : tNat]< wl >. 1:{
      constructor. 1: gen_typing.
      etransitivity. 2: gen_typing.
      now eapply redtm_conv.
    }
    split; econstructor; tea.
    now eapply reflNatRedTmEq.
  - intros ? NA t ? Ru red; inversion Ru; subst.
    assert [Γ |- A ≅ tBool]< wl > by (destruct NA; gen_typing).
    assert [Γ |- t :⤳*: nf : tBool]< wl >. 1:{
      constructor. 
      1: eapply ty_conv; gen_typing.
      etransitivity. 2: gen_typing.
      now eapply redtm_conv.
    }
    split; econstructor; tea.
    now eapply reflBoolRedTmEq.
  - intros ? NA t ? Ru red; inversion Ru; subst.
    assert [Γ |- A ≅ tEmpty]< wl > by (destruct NA; gen_typing).
    assert [Γ |- t :⤳*: nf : tEmpty]< wl >. 1:{
      constructor. 
      1: eapply ty_conv; gen_typing.
      etransitivity. 2: gen_typing.
      now eapply redtm_conv.
    }
    split; econstructor; tea.
    now eapply reflEmptyRedTmEq.
    Unshelve. 2: tea.
  - intros ? PA ihdom ihcod ?? ru' ?; pose (ru := ru'); destruct ru' as [p].
    assert [Γ |- A ≅ PA.(outTy)]< wl >. 1:{
      destruct PA as [?? []]. cbn in *.
      eapply convty_exp; tea.
      now apply redtywf_refl.
    }
    assert [Γ |-[ ta ] t ⤳* u : PA.(outTy)]< wl > by now eapply redtm_conv. 
    assert [Γ |-[ ta ] t : PA.(outTy)]< wl > by (eapply ty_conv; gen_typing).
    unshelve refine (let rt : [LRSig' PA | Γ ||- t : A]< wl > := _ in _).
    1: unshelve eexists p _ _; tea; constructor; destruct red; tea; etransitivity; tea.
    split; tea; exists rt ru sndTree; tea; intros; cbn; now apply reflLRTmEq.
  - intros ? IA ih _ t u [nf ?? prop] redt.
    assert [Γ |- A ≅ IA.(IdRedTy.outTy)]< wl > by (destruct IA; unfold IdRedTy.outTy; cbn; gen_typing).
    assert [Γ |-[ ta ] t ⤳* u : IA.(IdRedTy.outTy)]< wl > by now eapply redtm_conv. 
    assert [Γ |-[ ta ] t : IA.(IdRedTy.outTy)]< wl > by (eapply ty_conv; gen_typing).
    assert [Γ |-[ ta ] t :⤳*: nf : IA.(IdRedTy.outTy)]< wl >.
    1: constructor; [apply red|etransitivity; tea; apply red].
    split; eexists; tea.
    now eapply reflIdPropEq.
Qed.

Lemma WredSubstTerm {wl Γ A t u l}
  (RA : W[Γ ||-<l> A]< wl >) :
  W[Γ ||-<l> u : A | RA]< wl > ->
  [Γ |- t ⤳* u : A ]< wl > ->
  W[Γ ||-<l> t : A | RA]< wl > × W[Γ ||-<l> t ≅ u : A | RA]< wl >.
Proof.
  intros [] ?.
  split ; exists WTTm ; intros.
  all: pose proof (Hyp := over_tree_le Hover).
  all: eapply redSubstTerm ; [now eapply WRedTm | ].
  all: now eapply redtm_Ltrans.
Qed.

Lemma redwfSubstTerm {wl Γ A t u l} (RA : [Γ ||-<l> A]< wl >) :
  [Γ ||-<l> u : A | RA]< wl > ->
  [Γ |- t :⤳*: u : A ]< wl > ->
  [Γ ||-<l> t : A | RA]< wl > × [Γ ||-<l> t ≅ u : A | RA]< wl >.
Proof.
  intros ? []; now eapply redSubstTerm.
Qed.


Lemma redFwd {wl Γ l A B} :
  [Γ ||-<l> A]< wl > ->
  [Γ |- A :⤳*: B]< wl > ->
  whnf B ->
  [Γ ||-<l> B]< wl >.
Proof.
  intros RA; revert B; pattern l, wl, Γ, A, RA; apply LR_rect_TyUr; clear l wl Γ A RA.
  - intros ???? [??? red] ? red' ?. 
    eapply LRU_.  unshelve erewrite (redtywf_det _ _ red' red); tea.
    1: constructor. econstructor; tea. eapply redtywf_refl; gen_typing.
  - intros ???? [? red] ? red' ?.
    eapply LRne_.
    unshelve erewrite (redtywf_det _ _ red' red); tea.
    1: constructor; now eapply convneu_whne.
    econstructor; tea.
    eapply redtywf_refl; gen_typing.
  - intros ???? [?? red] ?? ? red' ?.
    eapply LRPi'. 
    unshelve erewrite (redtywf_det _ _ red' red); tea.
    1: constructor.
    econstructor.
    + eapply redtywf_refl; gen_typing.
    + eassumption.
    + eassumption.
    + eassumption.
  - intros ???? [red] ? red' ?.
    eapply LRNat_.
    unshelve erewrite (redtywf_det _ _ red' red); tea.
    1: constructor.
    econstructor; tea.
    eapply redtywf_refl; gen_typing.
  - intros ???? [red] ? red' ?.
    eapply LRBool_.
    unshelve erewrite (redtywf_det _ _ red' red); tea.
    1: constructor.
    econstructor; tea.
    eapply redtywf_refl; gen_typing.
  - intros ???? [red] ? red' ?.
    eapply LREmpty_.
    unshelve erewrite (redtywf_det _ _ red' red); tea.
    1: constructor.
    econstructor; tea.
    eapply redtywf_refl; gen_typing.
  - intros ???? [?? red] ?? ? red' ?.
    eapply LRSig'. 
    unshelve erewrite (redtywf_det _ _ red' red); tea.
    1: constructor.
    econstructor.
    + eapply redtywf_refl; gen_typing.
    + eassumption.
    + eassumption.
    + eassumption.
  - intros ???? [???? red] _ _ ? red' ?.
    eapply LRId'; unshelve erewrite (redtywf_det _ _ red' red); tea; [constructor|].
    econstructor; tea. eapply redtywf_refl; gen_typing.
Qed.

Lemma WredFwd {wl Γ l A B} :
  W[Γ ||-<l> A]< wl > ->
  [Γ |- A :⤳*: B]< wl > ->
  whnf B ->
  W[Γ ||-<l> B]< wl >.
Proof.
  intros [] red whB.
  exists WT ; intros.
  pose proof (Hyp := over_tree_le Ho).
  unshelve eapply redFwd.
  - exact A.
  - now eapply WRed.
  - unshelve econstructor.
    + now eapply wft_Ltrans ; destruct red.
    + now eapply redty_Ltrans ; destruct red.
  - assumption.
Qed.


Lemma redFwdConv {wl Γ l A B} (RA : [Γ ||-<l> A]< wl >) : [Γ |- A :⤳*: B]< wl > -> whnf B -> [Γ ||-<l> B]< wl > × [Γ ||-<l> A ≅ B | RA]< wl >.
Proof.
  intros red wh. pose (RB := redFwd RA red wh).
  destruct (redwfSubst RB red).
  split; tea; irrelevance.
Qed.

Lemma IdProp_whnf {wl Γ l A} (IA : [Γ ||-Id<l> A]< wl >) t : IdProp IA t -> whnf t.
Proof. intros []; constructor; destruct r; now eapply convneu_whne. Qed.


Lemma redTmFwd {wl Γ l A t u} {RA : [Γ ||-<l> A]< wl >} : 
  [Γ ||-<l> t : A | RA]< wl > ->
  [Γ |- t :⤳*: u : A]< wl > ->
  whnf u ->
  [Γ ||-<l> u : A | RA]< wl >.
Proof.
  revert t u; pattern l,wl, Γ,A,RA; apply LR_rect_TyUr; clear l wl Γ A RA.
  - intros ??????? [? red] red' ?.
    unshelve erewrite (redtmwf_det _ _ red' red); tea.
    1: now eapply isType_whnf.
    econstructor; tea.
    1: eapply redtmwf_refl; gen_typing.
    eapply RedTyRecBwd. eapply redFwd. 
    2,3: gen_typing.
    now eapply RedTyRecFwd.
  - intros ???? ??? [? red] red' ?.
    unshelve erewrite (redtmwf_det _ _ red' red); tea.
    1: constructor; now eapply convneu_whne.
    econstructor; tea.
    eapply redtmwf_refl; gen_typing.
  - intros ????????? [? red] red' ?.
    unshelve erewrite (redtmwf_det _ _ red' red); tea.
    1: eapply isFun_whnf; destruct isfun; constructor; tea; now eapply convneu_whne.
    econstructor; tea.
    eapply redtmwf_refl; gen_typing.
  - intros ??????? Rt red' ?; inversion Rt; subst.
    unshelve erewrite (redtmwf_det _ _ red' red); tea.
    1: now eapply NatProp_whnf.
    econstructor; tea.
    eapply redtmwf_refl; gen_typing.
  - intros ??????? Rt red' ?; inversion Rt; subst.
    unshelve erewrite (redtmwf_det _ _ red' red); tea.
    1: now eapply BoolProp_whnf.
    econstructor; tea.
    eapply redtmwf_refl; gen_typing.
  - intros ??????? Rt red' ?; inversion Rt; subst.
    unshelve erewrite (redtmwf_det _ _ red' red); tea.
    1: now eapply EmptyProp_whnf.
    econstructor; tea.
    eapply redtmwf_refl; gen_typing.
    Unshelve. 2: tea.
  - intros ????????? [? red] red' ?.
    unshelve erewrite (redtmwf_det _ _ red' red); tea.
    1: eapply isPair_whnf; destruct ispair; constructor; tea; now eapply convneu_whne.
    econstructor; tea.
    eapply redtmwf_refl; gen_typing.
  - intros ????????? [? red] red' ?.
    unshelve erewrite (redtmwf_det _ _ red' red); tea.
    1: now eapply IdProp_whnf.
    econstructor; tea.
    eapply redtmwf_refl; gen_typing.
Qed.

Lemma WredTmFwd {wl Γ l A t u} {RA : W[Γ ||-<l> A]< wl >} : 
  W[Γ ||-<l> t : A | RA]< wl > ->
  [Γ |- t :⤳*: u : A]< wl > ->
  whnf u ->
  W[Γ ||-<l> u : A | RA]< wl >.
Proof.
  intros [] [wfA red] whu.
  exists WTTm ; intros.
  pose proof (Hyp := over_tree_le Hover).
  eapply redTmFwd ; try assumption.
  - now eapply WRedTm.
  - econstructor.
    + now eapply ty_Ltrans.
    + now eapply redtm_Ltrans.
Qed.  

End Reduction.
