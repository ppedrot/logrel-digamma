
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations LContexts Context NormalForms Weakening GenericTyping LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Irrelevance Reflexivity Transitivity.

Set Universe Polymorphism.

Section Irrelevances.
Context `{GenericTypingProperties}.


Lemma VRirrelevant wl Γ {vsubst vsubst' veqsubst veqsubst'}
  (vr : VR (wl := wl) Γ vsubst veqsubst) (vr' : VR (wl := wl) Γ vsubst' veqsubst') :
  (forall Δ wl' σ f wfd wfd',
      vsubst Δ wl' σ f wfd  <~> vsubst' Δ wl' σ f wfd') ×
    (forall Δ wl' f wfd wfd' σ σ' vs vs',
        veqsubst Δ wl' σ σ' f wfd vs <~> veqsubst' Δ wl' σ σ' f wfd' vs').
Proof.
  revert vsubst' veqsubst' vr'.
  pattern Γ, vsubst, veqsubst, vr.
  apply VR_rect; clear Γ vsubst veqsubst vr.
  - intros ?????? h.
    destruct (VR_inv h) as [Hsub' [Hext' eq]] ; subst.
    split.
    + intros ; split ; intros.
      * rewrite Hsub'.
        now econstructor.
      * rewrite Hsub.
        now econstructor.
    + intros ; split ; intros.
      * rewrite Hext'.
        now econstructor.
      * erewrite Hext ; now econstructor.
  - intros ?????????? ih ?? h.
    destruct (VR_inv h) as [l' [VΓ' [VΓad' [VA' [Hsub' [Hext' eq]]]]]] ; subst.
    specialize (ih _ _ VΓad'); destruct ih as [ih1 ih2].
    split.
    + intros ; rewrite Hsub', Hsub ; split ; intros [Htail Hhead].
      all: unshelve econstructor.
      1,2: eapply ih1 ; eassumption.
      1,2: now Wirrelevance.
    + intros ; rewrite Hext, Hext' ; split ; intros [Htail Hhead].
      all: unshelve econstructor.
      1,3: eapply ih2 ; eassumption.
      all: now Wirrelevance.
Qed.

Lemma irrelevanceSubst {wl Γ} (VΓ VΓ' : [||-v Γ]< wl >) {σ Δ wl'} f
  (wfΔ wfΔ' : [|- Δ]< wl' >) :
  [Δ ||-v σ : Γ | VΓ | wfΔ | f ]< wl > -> [Δ ||-v σ : Γ | VΓ' | wfΔ' | f ]< wl >.
Proof.
  apply (fst (VRirrelevant wl Γ VΓ.(VAd.adequate) VΓ'.(VAd.adequate))).
Qed.

Lemma irrelevanceSubstEq {wl Γ} (VΓ VΓ' : [||-v Γ]< wl >) {σ σ' Δ wl'}
  f (wfΔ wfΔ' : [|- Δ]< wl' >)
  (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ | f]< wl >) (Vσ' : [Δ ||-v σ : Γ | VΓ' | wfΔ' | f]< wl >) :
  [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | Vσ | f]< wl > -> [Δ ||-v σ ≅ σ' : Γ | VΓ' | wfΔ' | Vσ' | f]< wl >.
Proof.
  apply (snd (VRirrelevant wl Γ VΓ.(VAd.adequate) VΓ'.(VAd.adequate))).
Qed.

Set Printing Primitive Projection Parameters.

Lemma reflSubst {wl Γ} (VΓ : [||-v Γ]< wl >) :
  forall {σ Δ wl'} f (wfΔ : [|- Δ]< wl' >)
  (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ | f]< wl >),
  [Δ ||-v σ ≅ σ : Γ | VΓ | wfΔ | Vσ | f]< wl >.
Proof.
  pattern Γ, VΓ; apply validity_rect; clear Γ VΓ.
  - intros.
    unfold validEmpty ; cbn.
    rewrite Hext ; now constructor.
  - intros * ih *. cbn in * ; rewrite Hext.
    unshelve econstructor.
    1: apply ih.
    apply WreflLRTmEq.
    revert Vσ.
    rewrite Hsub ; cbn ; intros [Htail Hhead].
    exact Hhead.
Qed.

Lemma symmetrySubstEq {wl Γ} (VΓ VΓ' : [||-v Γ]< wl >) :
  forall {σ σ' Δ wl'} f (wfΔ wfΔ' : [|- Δ]< wl' >)
  (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ | f]< wl >) (Vσ' : [Δ ||-v σ' : Γ | VΓ' | wfΔ'| f]< wl >),
    [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | Vσ | f]< wl > ->
    [Δ ||-v σ' ≅ σ : Γ | VΓ' | wfΔ' | Vσ' | f]< wl >.
Proof.
  revert VΓ'; pattern Γ, VΓ; apply validity_rect; clear Γ VΓ.
  - intros ???? [[vSubst vSubstEq] Vad] * ?.
    cbn in *.
    destruct (VR_inv Vad) as [Hsub' [Hext' eq]] ; subst.
    rewrite Hext' ; constructor.
  - intros * ih [[vSubst vSubstEq] Vad] *.
    destruct (VR_inv Vad) as [l' [VΓ' [VΓad' [VA' [Hsub' [Hext' eq]]]]]] ; subst.
    cbn in *.
    rewrite Hext, Hext'.
    revert Vσ ; rewrite (Hsub Δ wl' σ f wfΔ) ; cbn.
    revert Vσ' ; rewrite (Hsub' Δ wl' σ' f wfΔ') ; cbn.
    intros [Vtl Vhd] [Vtl' Vhd'] [Htail Hhead].
    unshelve econstructor.
    unshelve eapply ih in Htail ; [now exists VΓ'  | .. ].
    1: exact wfΔ'.    
    1: assumption.
    1: exact Htail.
    eapply WLRTmEqSym. cbn in *.
    revert Hhead. apply WLRTmEqRedConv.
    eapply validTyExt. 2:eassumption.
    now eapply (fst (VRirrelevant wl Γ VΓ.(VAd.adequate) VΓad')).
Qed.

Lemma transSubstEq {wl Γ} (VΓ : [||-v Γ]< wl >) :
  forall {σ σ' σ'' Δ wl' f} (wfΔ : [|- Δ]< wl' >)
    (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ| f ]< wl >)
    (Vσ' : [Δ ||-v σ' : Γ | VΓ | wfΔ| f ]< wl >),
    [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | Vσ| f ]< wl > ->
    [Δ ||-v σ' ≅ σ'' : Γ | VΓ | wfΔ | Vσ'| f ]< wl > ->
    [Δ ||-v σ ≅ σ'' : Γ | VΓ | wfΔ | Vσ| f ]< wl >.
Proof.
  pattern Γ, VΓ; apply validity_rect; clear Γ VΓ.
  - intros ; cbn.
    rewrite Hext ; now constructor.
  - intros * ih * ; cbn in *.
    do 3 rewrite Hext.
    revert Vσ Vσ' ; do 2 rewrite Hsub ; cbn.
    intros [] [] [] [] ; unshelve econstructor ; cbn in *.
    1: now eapply ih.
    eapply WtransEqTerm; tea.
    eapply WLRTmEqRedConv; tea.
    unshelve eapply WLRTyEqSym; tea.
    2: unshelve eapply validTyExt.
    7,8,9: eassumption.
    now tea.
Qed.

Lemma irrelevanceTy {wl Γ} : forall (VΓ VΓ' : [||-v Γ]< wl >) {l A},
  [Γ ||-v<l> A | VΓ]< wl > -> [Γ ||-v<l> A | VΓ']< wl >.
Proof.
  intros VΓ VΓ' l A [VA VAext]; unshelve econstructor; intros.
  - unshelve eapply VA. 3: eapply irrelevanceSubst. all:eassumption.
  - eapply VAext; [eapply irrelevanceSubst| eapply irrelevanceSubstEq]; eassumption.
Qed.

Lemma irrelevanceTy' {wl Γ Γ' A A' l} (VΓ : [||-v Γ]< wl >) (VΓ' : [||-v Γ']< wl >) (VA : [Γ ||-v<l> A | VΓ]< wl >) : 
  A = A' -> Γ = Γ' -> [Γ' ||-v<l> A' | VΓ']< wl >.
Proof.
  intros eqA eqΓ; subst; now eapply irrelevanceTy.
Qed.

Lemma irrelevanceLift {l A F G wl Γ} (VΓ : [||-v Γ]< wl >)
  (VF: [Γ ||-v<l> F | VΓ]< wl >) (VG: [Γ ||-v<l> G | VΓ]< wl >)
  (VFeqG : [Γ ||-v<l> F ≅ G | VΓ | VF]< wl >) :
  [Γ ,, F ||-v<l> A | validSnoc' VΓ VF]< wl > ->
  [Γ ,, G ||-v<l> A | validSnoc' VΓ VG]< wl >.
Proof.
  intros [VA VAext]; unshelve econstructor.
  - intros ????? [hd tl]. eapply VA.
    unshelve econstructor. 1: eassumption.
    eapply WLRTmRedConv. 2: eassumption.
    eapply WLRTyEqSym; unshelve eapply VFeqG; eassumption.
  - intros ?????? [??] [??] [??]. eapply VAext.
    + unshelve econstructor. 1: eassumption.
      eapply WLRTmRedConv. 2: eassumption.
      eapply WLRTyEqSym; unshelve eapply VFeqG; eassumption.
    + unshelve econstructor. 1: eassumption.
      eapply WLRTmEqRedConv. 2: eassumption.
      eapply WLRTyEqSym; unshelve eapply VFeqG; eassumption.
Qed.

Lemma irrelevanceTyEq {wl Γ l A B} (VΓ VΓ' : [||-v Γ]< wl >) (VA : [Γ ||-v<l> A | VΓ]< wl >) (VA' : [Γ||-v<l> A | VΓ']< wl >) :
  [Γ ||-v< l > A ≅ B | VΓ | VA]< wl > -> [Γ ||-v< l > A ≅ B | VΓ' | VA']< wl >.
Proof.
  intros [h]; constructor; intros.
  Wirrelevance0 ; [reflexivity | ].
  unshelve apply h. 1,2:eassumption.
  eapply irrelevanceSubst; eassumption.
Qed.

Lemma irrelevanceTyEq' {wl Γ l A A' B} (VΓ VΓ' : [||-v Γ]< wl >) (VA : [Γ ||-v<l> A | VΓ]< wl >) (VA' : [Γ||-v<l> A' | VΓ']< wl >) : A = A' ->
  [Γ ||-v< l > A ≅ B | VΓ | VA]< wl > -> [Γ ||-v< l > A' ≅ B | VΓ' | VA']< wl >.
Proof.
  intros ->; now eapply irrelevanceTyEq.
Qed.

Lemma symValidTyEq {wl Γ l A B} {VΓ : [||-v Γ]< wl >} {VA : [Γ ||-v<l> A | VΓ]< wl >} (VB : [Γ ||-v<l> B | VΓ]< wl >) :
  [Γ ||-v<l> A ≅ B | VΓ | VA]< wl > -> [Γ ||-v<l> B ≅ A | VΓ | VB]< wl >.
Proof.
  intros; constructor; intros.
  eapply WLRTyEqSym; now eapply validTyEq.
  Unshelve. all: tea.
Qed.

Lemma transValidTyEq {wl Γ l A B C} {VΓ : [||-v Γ]< wl >}
  {VA : [Γ ||-v<l> A | VΓ]< wl >} {VB : [Γ ||-v<l> B | VΓ]< wl >} :
  [Γ ||-v<l> A ≅ B | VΓ | VA]< wl > -> [Γ ||-v<l> B ≅ C | VΓ | VB]< wl > -> [Γ ||-v<l> A ≅ C | VΓ | VA]< wl >.
Proof.
  constructor; intros; eapply WLRTransEq; now eapply validTyEq.
  Unshelve. all: tea.
Qed.

Lemma irrelevanceTm'' {wl Γ l l' t A} (VΓ VΓ' : [||-v Γ]< wl >) (VA : [Γ ||-v<l> A | VΓ]< wl >) (VA' : [Γ||-v<l'> A | VΓ']< wl >) :
  [Γ ||-v<l> t : A | VΓ | VA]< wl > -> [Γ ||-v<l'> t : A | VΓ' | VA']< wl >.
Proof.
  intros [h1 h2]; unshelve econstructor.
  - intros. Wirrelevance0 ; [reflexivity | ].
    unshelve apply h1. 1,2:eassumption.
    eapply irrelevanceSubst; eassumption.
  - intros. Wirrelevance0 ; [reflexivity | ].
    unshelve eapply h2. 1,2: eassumption.
    1,2: eapply irrelevanceSubst; eassumption.
    eapply irrelevanceSubstEq; eassumption.
Qed.

Lemma irrelevanceTm' {wl Γ l l' t A A'} (VΓ VΓ' : [||-v Γ]< wl >) (VA : [Γ ||-v<l> A | VΓ]< wl >) (VA' : [Γ||-v<l'> A' | VΓ']< wl >) :
  A = A' -> [Γ ||-v<l> t : A | VΓ | VA]< wl > -> [Γ ||-v<l'> t : A' | VΓ' | VA']< wl >.
Proof.
  intros ->; now eapply irrelevanceTm''.
Qed.

Lemma irrelevanceTm {wl Γ l t A} (VΓ VΓ' : [||-v Γ]< wl >) (VA : [Γ ||-v<l> A | VΓ]< wl >) (VA' : [Γ||-v<l> A | VΓ']< wl >) :
  [Γ ||-v<l> t : A | VΓ | VA]< wl > -> [Γ ||-v<l> t : A | VΓ' | VA']< wl >.
Proof.
  now eapply irrelevanceTm''.
Qed.



Lemma irrelevanceTmLift {l t A F G wl Γ} (VΓ : [||-v Γ]< wl >)
  (VF: [Γ ||-v<l> F | VΓ]< wl >) (VG: [Γ ||-v<l> G | VΓ]< wl >)
  (VFeqG : [Γ ||-v<l> F ≅ G | VΓ | VF]< wl >)
  (VA : [Γ ,, F ||-v<l> A | validSnoc' VΓ VF]< wl >)
  (VA' : [Γ ,, G ||-v<l> A | validSnoc' VΓ VG]< wl >)  :
  [Γ ,, F ||-v<l> t : A | validSnoc' VΓ VF | VA]< wl > ->
  [Γ ,, G ||-v<l> t : A | validSnoc' VΓ VG | VA']< wl >.
Proof.
  intros [Vt Vtext]; unshelve econstructor.
  - intros ????? [hd tl]. Wirrelevance0 ; [reflexivity | ].
    unshelve eapply Vt; tea.
    unshelve econstructor; tea.
    eapply WLRTmRedConv; tea.
    eapply WLRTyEqSym; unshelve eapply VFeqG; eassumption.
  - intros ?????? [??] [??] [??]. Wirrelevance0 ; [reflexivity | ].
    unshelve eapply Vtext; tea.
    + unshelve econstructor; tea.
      eapply WLRTmRedConv; tea.
      eapply WLRTyEqSym; unshelve eapply VFeqG; eassumption.
    + unshelve econstructor; tea.
      eapply WLRTmRedConv; tea.
      eapply WLRTyEqSym; unshelve eapply VFeqG; eassumption.
    + unshelve econstructor; tea.
      eapply WLRTmEqRedConv; tea.
      eapply WLRTyEqSym; unshelve eapply VFeqG; eassumption.
Qed.

Lemma irrelevanceTmEq {wl Γ l t u A} (VΓ VΓ' : [||-v Γ]< wl >) (VA : [Γ ||-v<l> A | VΓ]< wl >) (VA' : [Γ||-v<l> A | VΓ']< wl >) :
  [Γ ||-v<l> t ≅ u : A | VΓ | VA]< wl > -> [Γ ||-v<l> t ≅ u : A | VΓ' | VA']< wl >.
Proof.
  intros [h]; constructor; intros; Wirrelevance0 ; [reflexivity | ].
  unshelve apply h; tea.
  eapply irrelevanceSubst; eassumption.
Qed.

Lemma irrelevanceTmEq' {wl Γ l t u A A'} (VΓ VΓ' : [||-v Γ]< wl >) (VA : [Γ ||-v<l> A | VΓ]< wl >) (VA' : [Γ||-v<l> A' | VΓ']< wl >) :
  A = A' -> [Γ ||-v<l> t ≅ u : A | VΓ | VA]< wl > -> [Γ ||-v<l> t ≅ u : A' | VΓ' | VA']< wl >.
Proof.
  intros ->; now eapply irrelevanceTmEq.
Qed.

Lemma symValidTmEq {wl Γ l t u A} {VΓ : [||-v Γ]< wl >} {VA : [Γ ||-v<l> A | VΓ]< wl >} :
  [Γ ||-v<l> t ≅ u : A| VΓ | VA]< wl > -> [Γ ||-v<l> u ≅ t : A | VΓ | VA]< wl >.
Proof.
  intros; constructor; intros.
  eapply WLRTmEqSym; now eapply validTmEq.
Qed.

Lemma transValidTmEq {wl Γ l t u v A} {VΓ : [||-v Γ]< wl >}
  {VA : [Γ ||-v<l> A | VΓ]< wl >} :
  [Γ ||-v<l> t ≅ u : A | VΓ | VA]< wl > -> 
  [Γ ||-v<l> u ≅ v : A | VΓ | VA]< wl > -> 
  [Γ ||-v<l> t ≅ v : A | VΓ | VA]< wl >.
Proof.
  constructor; intros; eapply WtransEqTerm; now eapply validTmEq.
Qed.

Lemma irrelevanceSubstExt {wl Γ} (VΓ : [||-v Γ]< wl >) {σ σ' Δ wl' f} (wfΔ : [|- Δ]< wl' >) :
  σ =1 σ' -> [Δ ||-v σ : Γ | VΓ | wfΔ | f]< wl > -> [Δ ||-v σ' : Γ | VΓ | wfΔ | f]< wl >.
Proof.
  revert σ σ'; pattern Γ, VΓ; apply validity_rect; clear Γ VΓ.
  - intros ; cbn ; rewrite Hsub. now constructor.
  - intros ????????? ih ?? eq ; cbn ; do 2 rewrite Hsub.
    intros [Hhead Htail] ; unshelve econstructor.
    + eapply ih. 2: eassumption.
      now rewrite eq.
    + rewrite <- (eq var_zero).
      Wirrelevance. now rewrite eq.
Qed.

Lemma irrelevanceSubstEqExt {wl Γ} (VΓ : [||-v Γ]< wl >) {σ1 σ1' σ2 σ2' Δ wl' f}
  (wfΔ : [|- Δ]< wl' >) (eq1 : σ1 =1 σ1') (eq2 : σ2 =1 σ2')
  (Vσ1 : [Δ ||-v σ1 : Γ | VΓ | wfΔ| f ]< wl >) :
  [Δ ||-v σ1 ≅ σ2 : Γ | VΓ | wfΔ | Vσ1| f ]< wl > ->
  [Δ ||-v σ1' ≅ σ2' : Γ | VΓ | wfΔ | irrelevanceSubstExt VΓ wfΔ eq1 Vσ1| f ]< wl >.
Proof.
  revert σ1 σ1' σ2 σ2' eq1 eq2 Vσ1; pattern Γ, VΓ; apply validity_rect; clear Γ VΓ.
  - intros ; cbn.
    rewrite (Hext Δ wl' σ1') ; now constructor.
  - intros ????????? ih ???? eq1 eq2 ? ; cbn in *.
    rewrite (Hext Δ wl' σ1'), (Hext Δ wl' σ1).
    intros [Htail Hhead].
    unshelve econstructor.
    + eapply irrelevanceSubstEq.
      unshelve eapply ih.
      6: eassumption. 
      all: now (rewrite eq1 + rewrite eq2).
    + cbn in *. Wirrelevance0 ; [reflexivity | ].
      rewrite <- (eq1 var_zero); rewrite <- (eq2 var_zero).
      Wirrelevance.
      rewrite eq1; reflexivity.
      Unshelve.
      2:{ eapply (validTy VA f wfΔ).
          eapply (transport (Hsub Δ wl' σ1' f wfΔ)
                    (irrelevanceSubstExt (validSnoc VΓ VA Hsub Hext) wfΔ eq1 Vσ1)).π1.
      }
Qed.

End Irrelevances.

Ltac irrValid :=
  match goal with
  | [_ : _ |- [||-v _]< _ >] => idtac
  | [_ : _ |- [ _ ||-v _ : _ | _ | _| _ ]< _ >] => eapply irrelevanceSubst
  | [_ : _ |- [ _ ||-v _ ≅ _ : _ | _ | _ | _ | _ ]< _ >] => eapply irrelevanceSubstEq
  | [_ : _ |- [_ ||-v<_> _ | _]< _ >] => eapply irrelevanceTy
  | [_ : _ |- [_ ||-v<_> _ ≅ _ | _ | _]< _ >] => eapply irrelevanceTyEq
  | [_ : _ |- [_ ||-v<_> _ : _ | _ | _]< _ >] => eapply irrelevanceTm
  | [_ : _ |- [_ ||-v<_> _ ≅ _ : _ | _ | _]< _ >] => eapply irrelevanceTmEq
  end; eassumption.
