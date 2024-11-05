(** * LogRel.LogicalRelation.Reflexivity: reflexivity of the logical relation. *)
Require Import PeanoNat.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst LContexts Context NormalForms Weakening GenericTyping Monad LogicalRelation DeclarativeInstance.
From LogRel.LogicalRelation Require Import Induction Escape.

Set Universe Polymorphism.

Section Reflexivities.
  Context `{GenericTypingProperties}.
  
  Definition reflLRTyEq {l wl Γ A} (lr : [ Γ ||-< l > A ]< wl > ) : [ Γ ||-< l > A ≅ A | lr ]< wl >.
  Proof.
    pattern l, wl, Γ, A, lr; eapply LR_rect_TyUr; intros ???? [] **.
    all: try match goal with H : PolyRed _ _ _ _ _ |- _ => destruct H; econstructor; tea end.
    all: try now econstructor.
    Unshelve.
    all: cbn in * ; try eassumption.
    (* econstructor; tea; now eapply escapeEqTerm. *)
  Qed.

  (* Deprecated *)
  Corollary LRTyEqRefl {l wl Γ A eqTy redTm eqTm}
    (lr : LogRel l wl Γ A eqTy redTm eqTm) : eqTy A.
  Proof.
    pose (R := Build_LRPack wl Γ A eqTy redTm eqTm). 
    pose (Rad := Build_LRAdequate (pack:=R) lr).
    change [Rad | _ ||- _ ≅ A ]< _ >; now eapply reflLRTyEq.
  Qed.

  Lemma NeNfEqRefl {wl Γ k A} : [Γ ||-NeNf k : A]< wl > -> [Γ ||-NeNf k ≅ k : A]< wl >.
  Proof.
    intros []; now econstructor.
  Qed.

  Lemma reflNatRedTmEq {wl Γ A} {NA : [Γ ||-Nat A]< wl >} :
      (forall t : term, [Γ ||-Nat t : A | NA]< wl > -> [Γ ||-Nat t ≅ t : A | NA]< wl >)
    × (forall t : term, NatProp NA t -> NatPropEq NA t t).
  Proof.
    eapply NatRedInduction.
    1-3: now econstructor.
    intros; econstructor.
    now eapply NeNfEqRefl.
  Qed.

  Lemma reflBoolRedTmEq {wl Γ A} {NA : [Γ ||-Bool A]< wl >} :
      (forall t : term, [Γ ||-Bool t : A | NA]< wl > -> [Γ ||-Bool t ≅ t : A | NA]< wl >)
    × (forall t : term, BoolProp NA t -> BoolPropEq NA t t).
  Proof.
    split.
    - intros t Ht. induction Ht.
      econstructor; eauto.
      destruct prop; econstructor.
      now eapply NeNfEqRefl.
    - intros ? [].
      + econstructor.
      + econstructor.
      + econstructor.
        now eapply NeNfEqRefl.
  Qed.

  Lemma reflEmptyRedTmEq {wl Γ A} {NA : [Γ ||-Empty A]< wl >} :
      (forall t : term, [Γ ||-Empty t : A | NA]< wl > -> [Γ ||-Empty t ≅ t : A | NA]< wl >)
    × (forall t : term, @EmptyProp _ _ _ wl Γ t -> @EmptyPropEq _ _ wl Γ t t).
  Proof.
    split.
    - intros t Ht. induction Ht.
      econstructor; eauto.
      destruct prop; econstructor.
      now eapply NeNfEqRefl.
    - intros ? []. econstructor.
      now eapply NeNfEqRefl.
  Qed.

  Lemma reflIdPropEq {wl Γ l A} (IA : [Γ ||-Id<l> A]< wl >) t (Pt : IdProp IA t) : IdPropEq IA t t.
  Proof.
    destruct Pt; constructor; tea; now eapply NeNfEqRefl.
  Qed.

  Lemma reflIdRedTmEq {wl Γ l A} (IA : [Γ ||-Id<l> A]< wl >) t (Rt : [Γ ||-Id<l> t : _ | IA]< wl >) : [Γ ||-Id<l> t ≅ t : _ | IA]< wl >.
  Proof. destruct Rt; econstructor; tea; now eapply reflIdPropEq. Qed.

  Definition reflLRTmEq@{h i j k l} {l wl Γ A} (lr : [ LogRel@{i j k l} l | Γ ||- A ]< wl > ) :
    forall t,
      [ Γ ||-<l> t : A | lr ]< wl > ->
      [ Γ ||-<l> t ≅ t : A | lr ]< wl >.
  Proof.
    pattern l, wl, Γ, A, lr; eapply LR_rect_TyUr; clear l wl Γ A lr; intros l wl Γ A.
    - intros h t [? ? ? ? Rt%RedTyRecFwd@{j k h i k}] ; cbn in *.
      (* Need an additional universe level h < i *)
      Unset Printing Notations.
      pose proof (reflLRTyEq@{h i k j} Rt).
      unshelve econstructor.
      all : cbn.
      1-2: econstructor ; tea ; cbn.
      1-3,5: eapply RedTyRecBwd; tea.
      1: cbn; easy.
      now eapply TyEqRecBwd.
    - intros [] t [].
      econstructor ; cbn in *.
      all: eassumption.
    - intros ??? t [].
      unshelve econstructor ; cbn in *.
      1-2: now econstructor.
      all: cbn; now eauto.
    - intros; now apply reflNatRedTmEq.
    - intros; now apply reflBoolRedTmEq.
    - intros; now apply reflEmptyRedTmEq.
    - intros ??? t [].
      unshelve econstructor ; cbn in *.
      1-2: now econstructor.
      all: cbn; now eauto.
    - intros; now eapply reflIdRedTmEq.
  Qed.
  
  (* Deprecated *)
  Corollary LRTmEqRefl@{h i j k l} {l wl Γ A eqTy redTm eqTm} (lr : LogRel@{i j k l} l wl Γ A eqTy redTm eqTm) :
    forall t, redTm t -> eqTm t t.
  Proof.
    pose (R := Build_LRPack wl Γ A eqTy redTm eqTm). 
    pose (Rad := Build_LRAdequate (pack:=R) lr).
    intros t ?; change [Rad | _ ||- t ≅ t : _ ]< _ >; now eapply reflLRTmEq.
  Qed.

End Reflexivities.

