From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations LContexts Context NormalForms Weakening GenericTyping LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Irrelevance Escape Reflexivity Weakening Neutral.

Set Universe Polymorphism.

Section Reflexivity.
Context `{GenericTypingProperties}.

Lemma reflValidTy {wl Γ A l} (VΓ : [||-v Γ]< wl >)
  (VA : [Γ ||-v<l> A | VΓ]< wl >) :
  [Γ ||-v<l> A ≅ A | VΓ | VA]< wl >.
Proof.
  constructor; intros.
  now apply WreflLRTyEq.
Qed.

Lemma reflValidTm {wl Γ t A l} (VΓ : [||-v Γ]< wl >)
  (VA : [Γ ||-v<l> A | VΓ]< wl >)
  (Vt : [Γ ||-v<l> t : A | VΓ | VA]< wl >) :
  [Γ ||-v<l> t ≅ t : A | VΓ | VA]< wl >.
Proof.
  constructor; intros; apply WreflLRTmEq; now eapply validTm.
Qed.

End Reflexivity.
