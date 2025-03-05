From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations LContexts Context NormalForms Weakening GenericTyping Monad LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Induction Irrelevance Escape Reflexivity Weakening Neutral Transitivity Reduction Universe.
From LogRel.Substitution Require Import Irrelevance Properties Conversion Reflexivity.

Set Universe Polymorphism.

Section Universe.
Context `{GenericTypingProperties} {Γ : context} {wl : wfLCon}.

Lemma UValid (VΓ : [||-v Γ]< wl >) : [Γ ||-v<one> U | VΓ]< wl >.
Proof.
  unshelve econstructor; intros.
  - exists (leaf _ ) ; intros ; eapply LRU_.
    pose proof (wfc_Ltrans Ho wfΔ).
    econstructor; tea; [constructor | ].
    cbn; eapply redtywf_refl ; now gen_typing.
  - exists (leaf _) ; intros ; cbn in *; constructor.
    pose proof (X := wfc_Ltrans Hover wfΔ).
    eapply redtywf_refl; now gen_typing.
Defined.

Lemma univValid {A l l'} (VΓ : [||-v Γ]< wl >)
  (VU : [Γ ||-v<l> U | VΓ]< wl >)
  (VA : [Γ ||-v<l> A : U | VΓ | VU]< wl >) :
  [Γ ||-v<l'> A| VΓ]< wl >.
Proof.
  unshelve econstructor; intros.
  - instValid vσ ; now eapply WUnivEq.
  - instAllValid vσ vσ' vσσ'; now eapply WUnivEqEq.
Qed.

Lemma univEqValid {A B l l'} (VΓ : [||-v Γ]< wl >)
  (VU : [Γ ||-v<l'> U | VΓ]< wl >)
  (VA : [Γ ||-v<l> A | VΓ]< wl >)
  (VAB : [Γ ||-v<l'> A ≅ B : U | VΓ | VU]< wl >) :
  [Γ ||-v<l> A ≅ B | VΓ | VA]< wl >.
Proof.
  constructor; intros; instValid Vσ.
  now eapply WUnivEqEq.
Qed.

End Universe.
