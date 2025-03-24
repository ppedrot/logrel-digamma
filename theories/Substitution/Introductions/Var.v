(** * LogRel.Introductions.Var : Validity of variables. *)
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations LContexts Context NormalForms Weakening
  GenericTyping LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Escape Irrelevance Reflexivity Transitivity Universe Weakening Neutral Induction NormalRed.
From LogRel.Substitution Require Import Irrelevance Properties Conversion Reflexivity SingleSubst Escape Monotonicity.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Section Var.
  Context `{GenericTypingProperties}.
  
  Lemma var0Valid {wl Γ l A} (VΓ : [||-v Γ]< wl >) (VA : [Γ ||-v<l> A | VΓ]< wl >) :
    [Γ,, A ||-v<l> tRel 0 : _ | validSnoc' VΓ VA | wk1ValidTy _ VA ]< wl >.
  Proof.
    constructor; intros; cbn.
    + epose (projT2 Vσ) ; cbn in * ; Wirrelevance. 
    + epose (snd Vσσ') ; Wirrelevance.
  Qed.
  
  Lemma var0Valid' {wl Γ l A} (VΓ : [||-v Γ,,A]< wl >) (VA : [Γ,,A ||-v<l> A⟨↑⟩ | VΓ]< wl >) :
    [Γ,, A ||-v<l> tRel 0 : _ | VΓ | VA ]< wl >.
  Proof.
    pose proof (invValidity VΓ) as [k [G [AG [eq1 [eq2 Hyp]]]]]; subst.
    constructor; intros; cbn.
    + epose proof (X := Vσ) ; rewrite eq1 in  X. 
      epose (projT2 X) ; cbn in * ; Wirrelevance. 
    + epose proof (X := Vσσ') ; rewrite eq2 in  X. 
      epose (snd X) ; Wirrelevance.
  Qed.

  Lemma in_ctx_valid {wl Γ A n} (hin : in_ctx Γ n A) :
    forall (VΓ : [||-v Γ]< wl >), ∑ l, [Γ ||-v<l> A | VΓ]< wl >.
  Proof.
    induction hin as [| ???? hin ih]; intros VΓ;
      pose proof (invValidity VΓ) as [k [G [AG [eq1 [eq2 Hyp]]]]]; subst.
    2: destruct (ih G).
    all: erewrite Hyp,  <- wk1_ren_on.
    all: eexists.
    all: now eapply irrelevanceTy, wk1ValidTy.
    Unshelve.
    2,4: eassumption.
  Qed.

  Lemma varnValid {wl Γ A n} (hin : in_ctx Γ n A) :
    forall l (VΓ : [||-v Γ]< wl >) (VA : [Γ ||-v<l> A | VΓ]< wl >),
    [Γ ||-v<l> tRel n : _ | VΓ | VA ]< wl >.
  Proof.
    induction hin as [| ???? hin ih]; intros l VΓ VA.
    1: eapply var0Valid'.
    pose proof (invValidity VΓ) as [k [G [AG [eq1 [eq2 Hyp]]]]]; subst.
    destruct (in_ctx_valid hin G) as [? h].
    pose proof (h' := wk1ValidTm AG _ (ih _ _ h)).
    cbn zeta in h'; rewrite wk1_ren_on in h'.
    eapply irrelevanceTm'; tea.
    now rewrite wk1_ren_on.
  Qed.
  
  Lemma var1Valid {wl Γ l A B} (VΓ : [||-v (Γ,, A) ,, B]< wl >)
    (VA : [_ ||-v<l> A⟨↑⟩⟨↑⟩ | VΓ]< wl >) :
    [(Γ,, A) ,, B ||-v<l> tRel 1 : _ | VΓ | VA ]< wl >.
  Proof.
    eapply varnValid; do 2 constructor.
  Qed.
  
End Var.
