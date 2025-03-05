From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations LContexts Context NormalForms Weakening GenericTyping LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Induction Irrelevance Escape Reflexivity Weakening Neutral Transitivity Reduction Application.
From LogRel.Substitution Require Import Irrelevance Properties Conversion SingleSubst Reflexivity.

Set Universe Polymorphism.

Section Application.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.

Set Printing Universes.

Lemma appValid {Γ wl F G t u l}
  {VΓ : [||-v Γ]< wl >}
  {VF : [Γ ||-v<l> F | VΓ]< wl >}
  {VΠFG : [Γ ||-v<l> tProd F G | VΓ]< wl >}
  (Vt : [Γ ||-v<l> t : tProd F G | VΓ | VΠFG]< wl >)
  (Vu : [Γ ||-v<l> u : F | VΓ | VF]< wl >)
  (VGu := substSΠ VΠFG Vu) :
  [Γ ||-v<l> tApp t u : G[u..] | VΓ | VGu]< wl >.
Proof.
  opector; intros.
  - instValid Vσ.
    epose (WappTerm RVΠFG RVt RVu (substSΠaux VΠFG Vu _ _ _ f wfΔ Vσ)).
    Wirrelevance. 
    fold subst_term ; now bsimpl.
  - instAllValid Vσ Vσ' Vσσ'. 
    unshelve epose (WappcongTerm _ REVt RVu _ REVu (substSΠaux VΠFG Vu _ _ _ f wfΔ Vσ)).
    2: Wirrelevance.
    eapply WLRTmRedConv; tea.
    unshelve eapply WLRTyEqSym. 2,3: tea.
    fold subst_term ; now bsimpl.
Qed.

Lemma appcongValid {Γ wl F G t u a b l}
  {VΓ : [||-v Γ]< wl >}
  {VF : [Γ ||-v<l> F | VΓ]< wl >}
  {VΠFG : [Γ ||-v<l> tProd F G | VΓ]< wl >}
  (Vtu : [Γ ||-v<l> t ≅ u : tProd F G | VΓ | VΠFG]< wl >)
  (Va : [Γ ||-v<l> a : F | VΓ | VF]< wl >)
  (Vb : [Γ ||-v<l> b : F | VΓ | VF]< wl >)
  (Vab : [Γ ||-v<l> a ≅ b : F | VΓ | VF]< wl >)
  (VGa := substSΠ VΠFG Va) :
  [Γ ||-v<l> tApp t a ≅ tApp u b : G[a..] | VΓ | VGa]< wl >.
Proof.
  constructor; intros; instValid Vσ.
  unshelve epose proof (WappcongTerm _ RVtu _ _ _ (substSΠaux VΠFG Va _ _ _ f wfΔ Vσ)); fold subst_term; cycle 5.
  all: try Wirrelevance.
  1: fold subst_term ; now bsimpl.  
  now eapply WLRCumulative.
Qed.

End Application.
