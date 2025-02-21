From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations LContexts Context NormalForms Weakening GenericTyping LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Irrelevance Escape Reflexivity Weakening Neutral Reduction Transitivity.

Set Universe Polymorphism.

Section Reduction.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.

Lemma redwfSubstValid {wl Γ A t u l}
  (VΓ : [||-v Γ]< wl >)
  (red : [Γ ||-v t :⤳*: u : A | VΓ]< wl >)
  (VA : [Γ ||-v<l> A | VΓ]< wl >)
  (Vu : [Γ ||-v<l> u : A | VΓ | VA]< wl >) :
  [Γ ||-v<l> t : A | VΓ | VA]< wl > × [Γ ||-v<l> t ≅ u : A | VΓ | VA]< wl >.
Proof.
  assert (Veq : [Γ ||-v<l> t ≅ u : A | VΓ | VA]< wl >).
  {
    constructor; intros; eapply redwfSubstTerm.
    1: now eapply validTm.
    now eapply validRed.
  }
  split; tea; constructor; intros.
  - eapply redwfSubstTerm.
    1: now eapply validTm.
    now eapply validRed.
  - eapply transEqTerm. 2: eapply transEqTerm.
    + now eapply validTmEq.
    + now eapply validTmExt.
    + eapply LRTmEqSym. eapply LRTmEqRedConv.
      1: eapply LRTyEqSym; now eapply validTyExt.
      now eapply validTmEq.
      Unshelve. all: tea.
Qed.
   
End Reduction.
