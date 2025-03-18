(** * LogRel.LogicalRelation.Reflexivity: reflexivity of the logical relation. *)
Require Import PeanoNat.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst LContexts Context NormalForms Weakening GenericTyping Monad LogicalRelation DeclarativeInstance.
From LogRel.LogicalRelation Require Import Induction Escape.

Set Universe Polymorphism.

Section Reflexivities.
  Context `{GenericTypingProperties}.
  
  Definition reflLRTyEq {l wl Γ A} (lr : [ Γ ||-< l > A ]< wl > ) :
    [ Γ ||-< l > A ≅ A | lr ]< wl >.
  Proof.
    pattern l, wl, Γ, A, lr; eapply LR_rect_TyUr; intros ???? [] **.
    all: try match goal with H : PolyRed _ _ _ _ _ |- _ => destruct H; econstructor; tea end.
    all: try now econstructor.
    Unshelve.
    all: cbn in * ; eassumption.
    (* econstructor; tea; now eapply escapeEqTerm. *)
  Qed.
  

  Definition WreflLRTyEq {l wl Γ A} (lr : W[ Γ ||-< l > A ]< wl > ) :
    W[ Γ ||-< l > A ≅ A | lr ]< wl >.
  Proof.
    exists (WT _ lr).
    intros ; now eapply reflLRTyEq.
  Defined.

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
(*
  Definition reflLRTmEq_inv@{h i j k l} {l wl Γ A} (lr : [ LogRel@{i j k l} l | Γ ||- A ]< wl > ) :
    forall t,
      [ Γ ||-<l> t ≅ t : A | lr ]< wl > ->
      [ Γ ||-<l> t : A | lr ]< wl >.
  Proof.
    pattern l, wl, Γ, A, lr; eapply LR_rect_TyUr; clear l wl Γ A lr; intros l wl Γ A.
    - intros h t [? ? ? ? Rt%RedTyRecFwd@{j k h i k}] ; cbn in *.
      (* Need an additional universe level h < i *)
      destruct redL.
      now unshelve econstructor.
    - intros ? t [???[]].
      econstructor ; cbn in *.
      1: eassumption.
      now eapply lrefl.
    - intros ??? t [].
      unshelve econstructor ; cbn in *.
      4: now eapply (PiRedTm.red redL).
      1,2: shelve. 
      1: now eapply (PiRedTm.refl redL).
      1: now eapply (PiRedTm.isfun redL).
      + cbn in *.
        intros.
        eapply (PiRedTm.app redL) ; eassumption.
      + cbn in * ; intros.
        eapply (PiRedTm.eq redL) ; eassumption.
    - intros NA t Nt ; cbn in *.
      epose (test := NatRedEqInduction _ _ _ NA
                       (fun t u Htu => [Γ ||-Nat t : A | NA ]< wl >)
                       (fun t u Htu => NatProp NA t)).
      cbn in *.
      eapply test.
      5: eassumption.
      2: now constructor.
      2: intros ; now constructor.
      2:{ intros. constructor ; destruct r.
          
          Search hyp: Notations.conv_neu_conv.
          2: now eapply lrefl.
          destruct Nt.
          Print TermRedWf.
          
      ; destruct Nt.
      econstructor.
      + eassumption.
      + etransitivity ; [ | eassumption].
        now symmetry.
      + About NatRedEqInduction.
        pose (test := NatRedEqInduction _ _ _ NA).
        
        
        Print NatPropEq.
        refine (fix f := match prop with
                              | zeroRed => _
                              | succReq n n' Hnn' => f' Hnn'
                              | neReq _ _ => _
                              end
                  with f' := match Hnn' with
                               | Build_NatRedTmEq _ _ _ _ => _
                                  end
                ).
               ). 
       

        
        eapply X0.
        replace (PiRedTm.nf redL) with (PiRedTm.nf redR) at 2.
        1: now eapply eqApp.
        eapply whredtm_det.
        all: econstructor.
        2,4: destruct redL, redR ; cbn in *.
        2,3: inversion isfun ; inversion isfun0 ; subst ; constructor.
        2-5: now eapply convneu_whne.
        * now eapply (PiRedTm.red redR).
        * now eapply (PiRedTm.red redL).
      + cbn in *.
        intros.
        
          destruct redR ; cbn in *.
          inversion isfun ; subst ; constructor.
          now eapply convneu_whne.
        
      destruct redL ; cbn in *.
      
      1-2: now econstructor.
      + intros ; now eapply eqTree.
      + 
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
*)
  Definition WreflLRTmEq@{h i j k l} {l wl Γ A}
    (lr : WLogRel@{i j k l} l wl Γ A ) :
    forall t,
      W[ Γ ||-<l> t : A | lr ]< wl > ->
      W[ Γ ||-<l> t ≅ t : A | lr ]< wl >.
  Proof.
    intros t [WTt WRedt] ; exists (WTt).
    intros wl' Hover Hover' ; eapply reflLRTmEq@{h i j k l}.
    now eapply WRedt.
  Defined.
  
  (* Deprecated *)
  Corollary LRTmEqRefl@{h i j k l} {l wl Γ A eqTy redTm eqTm} (lr : LogRel@{i j k l} l wl Γ A eqTy redTm eqTm) :
    forall t, redTm t -> eqTm t t.
  Proof.
    pose (R := Build_LRPack wl Γ A eqTy redTm eqTm). 
    pose (Rad := Build_LRAdequate (pack:=R) lr).
    intros t ?; change [Rad | _ ||- t ≅ t : _ ]< _ >; now eapply reflLRTmEq.
  Qed.

End Reflexivities.

