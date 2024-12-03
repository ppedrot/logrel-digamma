From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations LContexts Context NormalForms Weakening GenericTyping Monad LogicalRelation.
From LogRel.LogicalRelation Require Import Induction Irrelevance.

Section Split.
  Context `{GenericTypingProperties}.

  Lemma Split@{i j k l} {wl : wfLCon} {lA Γ A} {n : nat} {ne : not_in_LCon wl n} :
    WLogRel@{i j k l} lA (wl ,,l (ne, true)) Γ A ->
    WLogRel@{i j k l} lA (wl ,,l (ne, false)) Γ A ->
    WLogRel@{i j k l} lA wl Γ A.
  Proof.
    intros [WTt WRedt] [WTf WRedf].
    exists (ϝnode _ WTt WTf).
    intros wl' Hover.
    cbn in *.
    destruct (decidInLCon wl' n) ; [ | | now inversion Hover].
    - now eapply WRedt.
    - now eapply WRedf.
  Defined.

  Lemma EqSplit@{i j k l} {wl : wfLCon} {lA Γ A B} {n : nat} {ne : not_in_LCon wl n}
    HAt HAf :
    WLogRelEq@{i j k l} lA (wl ,,l (ne, true)) Γ A B HAt ->
    WLogRelEq@{i j k l} lA (wl ,,l (ne, false)) Γ A B HAf ->
    WLogRelEq@{i j k l} lA wl Γ A B (Split HAt HAf).
  Proof.
    intros [WTt WRedt] [WTf WRedf].
    exists (ϝnode _ WTt WTf).
    intros wl' Hover Hover' ; cbn in *.
    destruct (decidInLCon wl' n) ; [ | | now inversion Hover].
    - now eapply WRedt.
    - now eapply WRedf.
  Qed.

  Corollary EqSplit'@{i j k l} {wl : wfLCon} {lA Γ A B} {n : nat} {ne : not_in_LCon wl n}
    HAt HAf HA :
    WLogRelEq@{i j k l} lA (wl ,,l (ne, true)) Γ A B HAt ->
    WLogRelEq@{i j k l} lA (wl ,,l (ne, false)) Γ A B HAf ->
    WLogRelEq@{i j k l} lA wl Γ A B HA.
  Proof.
    intros HBt HBf ; eapply WLRTyEqIrrelevant' ; [reflexivity | ].
    eapply EqSplit ; eassumption.
  Qed. 

  Lemma TmSplit@{i j k l} {wl : wfLCon} {lA Γ t A} {n : nat} {ne : not_in_LCon wl n}
    HAt HAf :
    WLogRelTm@{i j k l} lA (wl ,,l (ne, true)) Γ t A HAt ->
    WLogRelTm@{i j k l} lA (wl ,,l (ne, false)) Γ t A HAf ->
    WLogRelTm@{i j k l} lA wl Γ t A (Split HAt HAf).
  Proof.
    intros [WTt WRedt] [WTf WRedf].
    exists (ϝnode _ WTt WTf).
    intros wl' Hover Hover' ; cbn in *.
    destruct (decidInLCon wl' n) ; [ | | now inversion Hover].
    - now eapply WRedt.
    - now eapply WRedf.
  Qed.

  Corollary TmSplit'@{i j k l} {wl : wfLCon} {lA Γ t A} {n : nat} {ne : not_in_LCon wl n}
    HAt HAf HA :
    WLogRelTm@{i j k l} lA (wl ,,l (ne, true)) Γ t A HAt ->
    WLogRelTm@{i j k l} lA (wl ,,l (ne, false)) Γ t A HAf ->
    WLogRelTm@{i j k l} lA wl Γ t A HA.
  Proof.
    intros Htt Htf ; eapply WLRTmRedIrrelevant' ; [reflexivity | ].
    eapply TmSplit ; eassumption.
  Qed. 

  Lemma TmEqSplit@{i j k l} {wl : wfLCon} {lA Γ t u A} {n : nat} {ne : not_in_LCon wl n}
    HAt HAf :
    WLogRelTmEq@{i j k l} lA (wl ,,l (ne, true)) Γ t u A HAt ->
    WLogRelTmEq@{i j k l} lA (wl ,,l (ne, false)) Γ t u A HAf ->
    WLogRelTmEq@{i j k l} lA wl Γ t u A (Split HAt HAf).
  Proof.
    intros [WTt WRedt] [WTf WRedf].
    exists (ϝnode _ WTt WTf).
    intros wl' Hover Hover' ; cbn in *.
    destruct (decidInLCon wl' n) ; [ | | now inversion Hover].
    - now eapply WRedt.
    - now eapply WRedf.
  Qed.

  Lemma TmEqSplit'@{i j k l} {wl : wfLCon} {lA Γ t u A} {n : nat} {ne : not_in_LCon wl n}
    HAt HAf HA :
    WLogRelTmEq@{i j k l} lA (wl ,,l (ne, true)) Γ t u A HAt ->
    WLogRelTmEq@{i j k l} lA (wl ,,l (ne, false)) Γ t u A HAf ->
    WLogRelTmEq@{i j k l} lA wl Γ t u A HA.
  Proof.
    intros Htt Htf ; eapply WLRTmEqIrrelevant' ; [reflexivity | ].
    eapply TmEqSplit ; eassumption.
  Qed. 
  
End Split.
