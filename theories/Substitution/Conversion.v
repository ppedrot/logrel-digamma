From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations LContexts Context NormalForms Weakening GenericTyping LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Irrelevance Escape Reflexivity Weakening Neutral.
From LogRel.Substitution Require Import Properties Irrelevance.

Set Universe Polymorphism.

Section Conversion.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.

Lemma conv {wl Γ t A B l} (VΓ : [||-v Γ]< wl >)
  (VA : [Γ ||-v<l> A | VΓ]< wl >)
  (VB : [Γ ||-v<l> B | VΓ]< wl >)
  (VeqAB : [Γ ||-v<l> A ≅ B | VΓ | VA]< wl >)
  (Vt : [Γ ||-v<l> t : A | VΓ | VA]< wl >) :
  [Γ ||-v<l> t : B | VΓ | VB]< wl >.
Proof.
  constructor; intros; [eapply LRTmRedConv| eapply LRTmEqRedConv].
  1,3: now unshelve now eapply validTyEq.
  1: now eapply validTm.
  now eapply validTmExt.
Qed.

Lemma convsym {wl Γ t A B l} (VΓ : [||-v Γ]< wl >)
  (VA : [Γ ||-v<l> A | VΓ]< wl >)
  (VB : [Γ ||-v<l> B | VΓ]< wl >)
  (VeqAB : [Γ ||-v<l> A ≅ B | VΓ | VA]< wl >)
  (Vt : [Γ ||-v<l> t : B | VΓ | VB]< wl >) :
  [Γ ||-v<l> t : A | VΓ | VA]< wl >.
Proof.
  constructor; intros; [eapply LRTmRedConv| eapply LRTmEqRedConv].
  1,3: unshelve eapply LRTyEqSym; tea; [|now unshelve now eapply validTyEq].
  1:  now unshelve now eapply validTm.
  now eapply validTmExt.
Qed.

Lemma convEq {wl Γ t u A B l} (VΓ : [||-v Γ]< wl >)
  (VA : [Γ ||-v<l> A | VΓ]< wl >)
  (VB : [Γ ||-v<l> B | VΓ]< wl >)
  (VeqAB : [Γ ||-v<l> A ≅ B | VΓ | VA]< wl >)
  (Vt : [Γ ||-v<l> t ≅ u : A | VΓ | VA]< wl >) :
  [Γ ||-v<l> t ≅ u : B | VΓ | VB]< wl >.
Proof.
  constructor; intros; eapply LRTmEqRedConv.
  1: now unshelve now eapply validTyEq.
  now eapply validTmEq.
Qed.


Lemma convSubstCtx1 {wl Γ Δ A B l σ} 
  (VΓ : [||-v Γ]< wl >)
  (wfΔ : [|- Δ]< wl >)
  (VΓA : [||-v Γ ,, A]< wl >) 
  (VΓB : [||-v Γ ,, B]< wl >) 
  (VA : [_ ||-v<l> A | VΓ]< wl >)
  (VB : [_ ||-v<l> B | VΓ]< wl >)
  (VAB : [_ ||-v<l> A ≅ B | VΓ | VA]< wl >)
  (Vσ : [_ ||-v σ : _ | VΓA | wfΔ]< wl >) :
  [_ ||-v σ : _ | VΓB | wfΔ]< wl >.
Proof.
  pose proof (invValiditySnoc VΓA) as [? [? [?]]]; subst.
  pose proof (invValiditySnoc VΓB) as [? [? [?]]]; subst.
  eapply irrelevanceSubstExt.
  1: rewrite <- scons_eta'; reflexivity.
  unshelve eapply consSubstS.
  1: epose (validTail Vσ); irrValid.
  eapply LRTmRedConv.
  2: irrelevanceRefl; eapply validHead.
  now eapply validTyEq.
  Unshelve. 6: tea.
    2: eapply irrelevanceSubst; now eapply validTail.
    tea.
Qed.

Lemma convSubstEqCtx1 {wl Γ Δ A B l σ σ'} 
  (VΓ : [||-v Γ]< wl >)
  (wfΔ : [|- Δ]< wl >)
  (VΓA : [||-v Γ ,, A]< wl >) 
  (VΓB : [||-v Γ ,, B]< wl >) 
  (VA : [_ ||-v<l> A | VΓ]< wl >)
  (VB : [_ ||-v<l> B | VΓ]< wl >)
  (VAB : [_ ||-v<l> A ≅ B | VΓ | VA]< wl >)
  (Vσ : [_ ||-v σ : _ | VΓA | wfΔ]< wl >) 
  (Vσ' : [_ ||-v σ' : _ | VΓA | wfΔ]< wl >) 
  (Vσσ' : [_ ||-v σ ≅ σ' : _ | VΓA | wfΔ | Vσ]< wl >) 
  (VσB : [_ ||-v σ : _ | VΓB | wfΔ]< wl >) :
  [_ ||-v σ ≅ σ' : _ | VΓB | wfΔ | VσB]< wl >.
Proof.
  pose proof (invValiditySnoc VΓA) as [? [? [?]]]; subst.
  pose proof (invValiditySnoc VΓB) as [? [? [?]]]; subst.
  eapply irrelevanceSubstEq.
  eapply irrelevanceSubstEqExt.
  1: rewrite <- scons_eta'; reflexivity.
  unshelve eapply consSubstSEq'.
  8: now eapply eqTail.
  3: irrValid.
  3: eapply LRTmEqRedConv.
  4: now eapply eqHead.
  2: irrelevanceRefl; eapply validTyEq; irrValid.
  eapply LRTmRedConv.
  2: irrelevanceRefl; eapply validHead.
  eapply validTyExt.
  1: now eapply validTail.
  eapply reflSubst.
  Unshelve.
  1: now rewrite scons_eta'.
  9: tea.
  7: tea.
  2,6: irrValid.
  1,2: tea.
  1,2: eapply irrelevanceSubst; now eapply validTail.
Qed.


Lemma convCtx1 {wl Γ A B P l} 
  (VΓ : [||-v Γ]< wl >)
  (VΓA : [||-v Γ ,, A]< wl >) 
  (VΓB : [||-v Γ ,, B]< wl >) 
  (VA : [_ ||-v<l> A | VΓ]< wl >)
  (VB : [_ ||-v<l> B | VΓ]< wl >)
  (VAB : [_ ||-v<l> A ≅ B | VΓ | VA]< wl >)
  (VP : [_ ||-v<l> P | VΓA]< wl >) :
  [_ ||-v<l> P | VΓB]< wl >.
Proof.
  opector; intros.
  - eapply validTy; tea; eapply convSubstCtx1; tea; now eapply symValidTyEq.
  - irrelevanceRefl; unshelve eapply validTyExt.
    3,4: tea. 
    1,2:  eapply convSubstCtx1; tea; now eapply symValidTyEq.
    eapply convSubstEqCtx1; cycle 2; tea; now eapply symValidTyEq.
    Unshelve. all: tea.
Qed.

Lemma convEqCtx1 {wl Γ A B P Q l} 
  (VΓ : [||-v Γ]< wl >)
  (VΓA : [||-v Γ ,, A]< wl >) 
  (VΓB : [||-v Γ ,, B]< wl >) 
  (VA : [_ ||-v<l> A | VΓ]< wl >)
  (VB : [_ ||-v<l> B | VΓ]< wl >)
  (VAB : [_ ||-v<l> A ≅ B | VΓ | VA]< wl >)
  (VP : [_ ||-v<l> P | VΓA]< wl >)
  (VPB : [_ ||-v<l> P | VΓB]< wl >)
  (VPQ : [_ ||-v<l> P ≅ Q | VΓA | VP]< wl >) :
  [_ ||-v<l> P ≅ Q | VΓB | VPB]< wl >.
Proof.
  constructor; intros; irrelevanceRefl.
  eapply validTyEq; tea.
  Unshelve. 1: tea. 
  unshelve eapply convSubstCtx1; cycle 5; tea; now eapply symValidTyEq.
Qed.

Lemma convSubstCtx2 {wl Γ Δ A1 B1 A2 B2 l σ} 
  (VΓ : [||-v Γ]< wl >)
  (wfΔ : [|- Δ]< wl >)
  (VA1 : [_ ||-v<l> A1 | VΓ]< wl >)
  (VB1 : [_ ||-v<l> B1 | VΓ]< wl >)
  (VAB1 : [_ ||-v<l> A1 ≅ B1 | VΓ | VA1]< wl >)
  (VΓA1 := validSnoc VΓ VA1) 
  (VΓB1 := validSnoc VΓ VB1) 
  (VA2 : [_ ||-v<l> A2 | VΓA1]< wl >)
  (VB2 : [_ ||-v<l> B2 | VΓA1]< wl >)
  (VAB : [_ ||-v<l> A2 ≅ B2 | VΓA1 | VA2]< wl >)
  (VB2' := convCtx1 VΓ VΓA1 VΓB1 VA1 VB1 VAB1 VB2)
  (VΓA12 := validSnoc VΓA1 VA2) 
  (VΓB12 := validSnoc VΓB1 VB2') 
  (Vσ : [_ ||-v σ : _ | VΓA12 | wfΔ]< wl >) :
  [_ ||-v σ : _ | VΓB12 | wfΔ]< wl >.
Proof.
  eapply irrelevanceSubstExt.
  1: rewrite <- scons_eta'; reflexivity.
  unshelve eapply consSubstS.
  + eapply convSubstCtx1; tea.
    now eapply validTail.
  + eapply LRTmRedConv.
    2: now eapply validHead.
    eapply validTyEq; tea.
  Unshelve. all: tea.
Qed.

Lemma convSubstCtx2' {wl Γ Δ A1 B1 A2 B2 l σ} 
  (VΓ : [||-v Γ]< wl >)
  (wfΔ : [|- Δ]< wl >)
  (VΓA1 : [||-v Γ ,, A1]< wl >) 
  (VΓA12 : [||-v Γ ,, A1 ,, A2]< wl >) 
  (VΓB12 : [||-v Γ ,, B1 ,, B2]< wl >) 
  (VA1 : [_ ||-v<l> A1 | VΓ]< wl >)
  (VB1 : [_ ||-v<l> B1 | VΓ]< wl >)
  (VAB1 : [_ ||-v<l> A1 ≅ B1 | VΓ | VA1]< wl >)
  (VA2 : [_ ||-v<l> A2 | VΓA1]< wl >)
  (VB2 : [_ ||-v<l> B2 | VΓA1]< wl >)
  (VAB : [_ ||-v<l> A2 ≅ B2 | VΓA1 | VA2]< wl >)
  (Vσ : [_ ||-v σ : _ | VΓA12 | wfΔ]< wl >) :
  [_ ||-v σ : _ | VΓB12 | wfΔ]< wl >.
Proof.
  eapply irrelevanceSubst.
  eapply convSubstCtx2; irrValid.
  Unshelve. all: tea; irrValid.
Qed.

Lemma convSubstEqCtx2 {wl Γ Δ A1 B1 A2 B2 l σ σ'} 
  (VΓ : [||-v Γ]< wl >)
  (wfΔ : [|- Δ]< wl >)
  (VA1 : [_ ||-v<l> A1 | VΓ]< wl >)
  (VB1 : [_ ||-v<l> B1 | VΓ]< wl >)
  (VAB1 : [_ ||-v<l> A1 ≅ B1 | VΓ | VA1]< wl >)
  (VΓA1 := validSnoc VΓ VA1) 
  (VΓB1 := validSnoc VΓ VB1) 
  (VA2 : [_ ||-v<l> A2 | VΓA1]< wl >)
  (VB2 : [_ ||-v<l> B2 | VΓA1]< wl >)
  (VAB : [_ ||-v<l> A2 ≅ B2 | VΓA1 | VA2]< wl >)
  (VB2' := convCtx1 VΓ VΓA1 VΓB1 VA1 VB1 VAB1 VB2)
  (VΓA12 := validSnoc VΓA1 VA2) 
  (VΓB12 := validSnoc VΓB1 VB2') 
  (Vσ : [_ ||-v σ : _ | VΓA12 | wfΔ]< wl >) 
  (Vσ' : [_ ||-v σ' : _ | VΓA12 | wfΔ]< wl >) 
  (Vσσ' : [_ ||-v σ ≅ σ' : _ | VΓA12 | wfΔ | Vσ]< wl >) 
  (VσB : [_ ||-v σ : _ | VΓB12 | wfΔ]< wl >) :
  [_ ||-v σ ≅ σ' : _ | VΓB12 | wfΔ | VσB]< wl >.
Proof.
  eapply irrelevanceSubstEq.
  eapply irrelevanceSubstEqExt.
  1: rewrite <- scons_eta'; reflexivity.
  unshelve eapply consSubstSEq'.
  8:{ eapply convSubstEqCtx1; tea.
    1: now eapply validTail.
    now eapply eqTail.
  }
  3,4: irrValid.
  2: eapply convSubstCtx1; tea; now eapply validTail. 
  3: eapply LRTmEqRedConv.
  4: now eapply eqHead.
  2: irrelevanceRefl; eapply validTyEq; irrValid.
  eapply LRTmRedConv.
  2: irrelevanceRefl; eapply validHead.
  eapply validTyExt.
  1: now eapply validTail.
  eapply reflSubst.
  Unshelve.
  1: now rewrite scons_eta'.
  11: tea.
  1,2,6: irrValid.
  1: tea.
  2: eapply convSubstCtx1; tea.
  1,2: now eapply validTail.
Qed. 

Lemma convSubstEqCtx2' {wl Γ Δ A1 B1 A2 B2 l σ σ'} 
  (VΓ : [||-v Γ]< wl >)
  (wfΔ : [|- Δ]< wl >)
  (VA1 : [_ ||-v<l> A1 | VΓ]< wl >)
  (VB1 : [_ ||-v<l> B1 | VΓ]< wl >)
  (VAB1 : [_ ||-v<l> A1 ≅ B1 | VΓ | VA1]< wl >)
  (VΓA1 : [||-v Γ ,, A1]< wl >) 
  (VΓB1 : [||-v Γ ,, B1]< wl >) 
  (VA2 : [_ ||-v<l> A2 | VΓA1]< wl >)
  (VB2 : [_ ||-v<l> B2 | VΓA1]< wl >)
  (VAB : [_ ||-v<l> A2 ≅ B2 | VΓA1 | VA2]< wl >)
  (VB2' : [_ ||-v<l> B2 | VΓB1]< wl >)
  (VΓA12 : [||-v Γ ,, A1 ,, A2]< wl >) 
  (VΓB12 : [||-v Γ ,, B1,, B2]< wl >) 
  (Vσ : [_ ||-v σ : _ | VΓA12 | wfΔ]< wl >) 
  (Vσ' : [_ ||-v σ' : _ | VΓA12 | wfΔ]< wl >) 
  (Vσσ' : [_ ||-v σ ≅ σ' : _ | VΓA12 | wfΔ | Vσ]< wl >) 
  (VσB : [_ ||-v σ : _ | VΓB12 | wfΔ]< wl >) :
  [_ ||-v σ ≅ σ' : _ | VΓB12 | wfΔ | VσB]< wl >.
Proof.
  eapply irrelevanceSubstEq.
  eapply convSubstEqCtx2; irrValid.
  Unshelve.  all: tea; irrValid.
Qed.

Lemma convCtx2 {wl Γ A1 B1 A2 B2 P l} 
  (VΓ : [||-v Γ]< wl >)
  (VA1 : [_ ||-v<l> A1 | VΓ]< wl >)
  (VB1 : [_ ||-v<l> B1 | VΓ]< wl >)
  (VAB1 : [_ ||-v<l> A1 ≅ B1 | VΓ | VA1]< wl >)
  (VΓA1 := validSnoc VΓ VA1) 
  (VΓB1 := validSnoc VΓ VB1) 
  (VA2 : [_ ||-v<l> A2 | VΓA1]< wl >)
  (VB2 : [_ ||-v<l> B2 | VΓA1]< wl >)
  (VAB : [_ ||-v<l> A2 ≅ B2 | VΓA1 | VA2]< wl >)
  (VB2' := convCtx1 VΓ VΓA1 VΓB1 VA1 VB1 VAB1 VB2)
  (VΓA12 := validSnoc VΓA1 VA2) 
  (VΓB12 := validSnoc VΓB1 VB2') 
  (VP : [_ ||-v<l> P | VΓA12]< wl >) :
  [_ ||-v<l> P | VΓB12]< wl >.
Proof.
  assert [_ ||-v<l> A2 | VΓB1]< wl > by now eapply convCtx1.
  assert [_ ||-v<l> B1 ≅ A1 | _ | VB1]< wl > by now eapply symValidTyEq.
  assert [_ ||-v<l> B2 ≅ A2 | _ | VB2']< wl > by (eapply convEqCtx1; tea; now eapply symValidTyEq).
  opector; intros.
  - eapply validTy; tea; now eapply convSubstCtx2'.
  - irrelevanceRefl; unshelve eapply validTyExt.
    3,4: tea. 
    1,2:  now eapply convSubstCtx2'.
    eapply convSubstEqCtx2'; tea.
    Unshelve. tea.
Qed.

Lemma convCtx2' {wl Γ A1 A2 B1 B2 P l} 
  (VΓ : [||-v Γ]< wl >)
  (VA1 : [_ ||-v<l> A1 | VΓ]< wl >)
  (VB1 : [_ ||-v<l> B1 | VΓ]< wl >)
  (VAB1 : [_ ||-v<l> A1 ≅ B1 | VΓ | VA1]< wl >)
  (VΓA1 : [||-v Γ ,, A1]< wl >) 
  (VΓB1 : [||-v Γ ,, B1]< wl >) 
  (VA2 : [_ ||-v<l> A2 | VΓA1]< wl >)
  (VB2 : [_ ||-v<l> B2 | VΓA1]< wl >)
  (VAB : [_ ||-v<l> A2 ≅ B2 | VΓA1 | VA2]< wl >)
  (VB2' : [_ ||-v<l> B2 | VΓB1]< wl >)
  (VΓA12 : [||-v Γ ,, A1 ,, A2]< wl >) 
  (VΓB12 : [||-v Γ ,, B1,, B2]< wl >)
  (VP : [_ ||-v<l> P | VΓA12]< wl >) :
  [_ ||-v<l> P | VΓB12]< wl >.
Proof.
  eapply irrelevanceTy; eapply convCtx2; irrValid.
  Unshelve. all: tea; irrValid.
Qed.


End Conversion.
