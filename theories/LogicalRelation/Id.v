From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Notations Utils BasicAst LContexts Context NormalForms Weakening GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Induction Irrelevance Weakening Neutral Escape Reflexivity NormalRed Reduction Monotonicity Transitivity Universe.

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
