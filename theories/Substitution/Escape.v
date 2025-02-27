
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations LContexts Context NormalForms Weakening GenericTyping Monad LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Irrelevance Escape Reflexivity Weakening Neutral.
From LogRel.Substitution Require Import Irrelevance Properties.

Set Universe Polymorphism.

Section Escape.
Context `{GenericTypingProperties}.

Lemma reducibleTy {wl Γ l A} (VΓ : [||-v Γ]< wl >)
  (VA : [Γ ||-v<l> A | VΓ]< wl >) :
  W[Γ ||-<l> A]< wl >.
Proof.
  replace A with A[tRel] by now asimpl.
  unshelve eapply validTy; tea.
  3: now apply idSubstS.
Qed.

Lemma reducibleTyEq {wl Γ l A B} (VΓ : [||-v Γ]< wl >) (VA : [Γ ||-v<l> A | VΓ]< wl >) :
  [Γ ||-v<l> A ≅ B | VΓ | VA]< wl > ->
  W[Γ ||-<l> A ≅ B | reducibleTy VΓ VA]< wl >.
Proof.
  intros.
  replace A with A[tRel] by now asimpl.
  replace B with B[tRel] by now asimpl.
  unshelve epose proof (validTyEq X _ _ (idSubstS VΓ)).
  Wirrelevance.
Qed.

Lemma reducibleTm {wl Γ l A t}
  (VΓ : [||-v Γ]< wl >)
  (VA : [Γ ||-v<l> A | VΓ]< wl >) : 
  [Γ ||-v<l> t : A | VΓ | VA]< wl > ->
  W[Γ ||-<l> t : A | reducibleTy VΓ VA]< wl >.
Proof.
  intros.
  replace A with A[tRel] by now asimpl.
  replace t with t[tRel] by now asimpl.
  unshelve epose proof (validTm X _ _ (idSubstS VΓ)).
  Wirrelevance.
Qed.

Lemma reducibleTmEq {wl Γ l A t u}
  (VΓ : [||-v Γ]< wl >)
  (VA : [Γ ||-v<l> A | VΓ]< wl >) : 
  [Γ ||-v<l> t ≅ u : A | VΓ | VA]< wl > ->
  W[Γ ||-<l> t ≅ u : A | reducibleTy VΓ VA]< wl >.
Proof.
  intros.
  replace A with A[tRel] by now asimpl.
  replace t with t[tRel] by now asimpl.
  replace u with u[tRel] by now asimpl.
  unshelve epose proof (validTmEq X _ _ (idSubstS VΓ)).
  Wirrelevance.
Qed.

Lemma escapeTy {wl Γ l A} (VΓ : [||-v Γ]< wl >)
  (VA : [Γ ||-v<l> A | VΓ]< wl >) : [Γ |- A]< wl >.
Proof. eapply Wescape; now eapply reducibleTy. Qed.


Lemma escapeEq {wl Γ l A B} (VΓ : [||-v Γ]< wl >) (VA : [Γ ||-v<l> A | VΓ]< wl >) : 
  [Γ ||-v<l> A ≅ B | VΓ | VA]< wl > -> [Γ |- A ≅ B]< wl >.
Proof.
  intros; unshelve eapply WescapeEq; tea.
  1: now eapply reducibleTy.
  now eapply reducibleTyEq.
Qed.

Lemma escapeTm {wl Γ l A t} (VΓ : [||-v Γ]< wl >) (VA : [Γ ||-v<l> A | VΓ]< wl >) : 
  [Γ ||-v<l> t : A | VΓ | VA]< wl > -> [Γ |- t : A]< wl >.
Proof.
  intros; unshelve eapply WescapeTerm; tea.
  1: now eapply reducibleTy.
  now eapply reducibleTm.
Qed.

Lemma escapeTmEq {wl Γ l A t u} (VΓ : [||-v Γ]< wl >) (VA : [Γ ||-v<l> A | VΓ]< wl >) : 
  [Γ ||-v<l> t ≅ u : A | VΓ | VA]< wl > -> [Γ |- t ≅ u : A]< wl >.
Proof.
  intros; unshelve eapply WescapeEqTerm; tea.
  1: now eapply reducibleTy.
  now eapply reducibleTmEq.
Qed.

End Escape.
