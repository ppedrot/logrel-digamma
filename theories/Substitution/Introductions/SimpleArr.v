From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations LContexts Context NormalForms Weakening
  GenericTyping Monad LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Escape Reflexivity Neutral Weakening Irrelevance.
From LogRel.Substitution Require Import Irrelevance Properties Conversion.
From LogRel.Substitution.Introductions Require Import Universe Pi Application Lambda Var.

Set Universe Polymorphism.

Section SimpleArrValidity.

  Context `{GenericTypingProperties}.

  Lemma simpleArrValid {l wl Γ F G} (VΓ : [||-v Γ]< wl >)
    (VF : [Γ ||-v< l > F | VΓ ]< wl >)
    (VG : [Γ ||-v< l > G | VΓ]< wl >) :
    [Γ ||-v<l> arr F G | VΓ]< wl >.
  Proof.
    unshelve eapply PiValid; tea.
    replace G⟨↑⟩ with G⟨@wk1 Γ F⟩ by now bsimpl.
    now eapply wk1ValidTy.
  Qed.

  Lemma simpleArrCongValid {l wl Γ F F' G G'} (VΓ : [||-v Γ]< wl >)
    (VF : [Γ ||-v< l > F | VΓ ]< wl >)
    (VF' : [Γ ||-v< l > F' | VΓ ]< wl >)
    (VeqF : [Γ ||-v< l > F ≅ F' | VΓ | VF]< wl >)
    (VG : [Γ ||-v< l > G | VΓ ]< wl >)
    (VG' : [Γ ||-v< l > G' | VΓ ]< wl >)
    (VeqG : [Γ ||-v< l > G ≅ G' | VΓ | VG]< wl >) :
    [Γ ||-v<l> arr F G ≅ arr F' G' | VΓ | simpleArrValid _ VF VG]< wl >.
  Proof.
    eapply irrelevanceTyEq.
    unshelve eapply PiCong; tea.
    + replace G⟨↑⟩ with G⟨@wk1 Γ F⟩ by now bsimpl.
      now eapply wk1ValidTy.
    + replace G'⟨↑⟩ with G'⟨@wk1 Γ F'⟩ by now bsimpl.
      now eapply wk1ValidTy.
    + replace G'⟨↑⟩ with G'⟨@wk1 Γ F⟩ by now bsimpl.
      eapply irrelevanceTyEq'.
      2: now eapply wk1ValidTyEq.
      now bsimpl.
    Unshelve. 2: tea.
  Qed.

  Lemma simple_appValid {wl Γ t u F G l}
    (VΓ : [||-v Γ]< wl >)
    {VF : [Γ ||-v<l> F | VΓ]< wl >}
    (VG : [Γ ||-v<l> G | VΓ]< wl >)
    (VΠ : [Γ ||-v<l> arr F G | VΓ]< wl >)
    (Vt : [Γ ||-v<l> t : arr F G | _ | VΠ]< wl >)
    (Vu : [Γ ||-v<l> u : F | _ | VF]< wl >) :
    [Γ ||-v<l> tApp t u : G| _ | VG]< wl >.
  Proof.
    eapply irrelevanceTm'.
    2: eapply appValid; tea.
    now bsimpl.
  Unshelve. all: tea.
  Qed.

  Lemma simple_idValid {wl Γ A l}
    (VΓ : [||-v Γ]< wl >)
    {VF : [Γ ||-v<l> A | VΓ]< wl >}
    (VΠ : [Γ ||-v<l> arr A A | VΓ]< wl >) :
    [Γ ||-v<l> idterm A : arr A A | _ | VΠ]< wl >.
  Proof.
    eapply irrelevanceTm'.
    2: unshelve eapply lamValid.
    5: unshelve eapply var0Valid.
    - now rewrite wk1_ren_on.
    - tea.
  Qed.

  Lemma simple_compValid {wl Γ A B C f g l}
    (VΓ : [||-v Γ]< wl >)
    {VA : [Γ ||-v<l> A | VΓ]< wl >}
    (VB : [Γ ||-v<l> B | VΓ]< wl >)
    (VC : [Γ ||-v<l> C | VΓ]< wl >)
    (VAB : [Γ ||-v<l> arr A B | VΓ]< wl >)
    (VBC : [Γ ||-v<l> arr B C | VΓ]< wl >)
    (VAC : [Γ ||-v<l> arr A C | VΓ]< wl >)
    (Vf : [Γ ||-v<l> f : arr A B | _ | VAB]< wl >)
    (Vg : [Γ ||-v<l> g : arr B C | _ | VBC]< wl >) :
    [Γ ||-v<l> comp A g f : arr A C | _ | VAC]< wl >.
  Proof.
    eapply irrelevanceTm'.
    2: unshelve eapply lamValid.
    5: unshelve eapply simple_appValid.
    9: unshelve eapply simple_appValid.
    13: eapply var0Valid.
    4: eapply wk1ValidTy; exact VC.
    4: eapply wk1ValidTy; exact VB.
    - now rewrite wk1_ren_on.
    - eassumption.
    - do 2 erewrite wk1_ren_on. rewrite<- arr_ren1.
      erewrite<- wk1_ren_on.
      now eapply wk1ValidTy.
    - eapply irrelevanceTm'. 2: erewrite<- wk1_ren_on;now eapply wk1ValidTm.
      rewrite wk1_ren_on. rewrite arr_ren1.
      do 2 rewrite wk1_ren_on. reflexivity.
    - do 2 erewrite wk1_ren_on. rewrite<- arr_ren1.
      erewrite<- wk1_ren_on.
      now eapply wk1ValidTy.
    - eapply irrelevanceTm'. 2: erewrite<- wk1_ren_on;now eapply wk1ValidTm.
      rewrite wk1_ren_on. rewrite arr_ren1.
      do 2 rewrite wk1_ren_on. reflexivity.

      Unshelve. all: tea.
  Qed.

End SimpleArrValidity.
