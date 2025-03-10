From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations LContexts Context NormalForms Weakening GenericTyping Monad LogicalRelation.
From LogRel.LogicalRelation Require Import Induction Irrelevance Monotonicity.

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

  Lemma TreeSplit@{i j k l} {wl : wfLCon} {lA Γ A}
    (d : DTree wl) :
    (forall wl', over_tree wl wl' d -> WLogRel@{i j k l} lA wl' Γ A) ->
    WLogRel@{i j k l} lA wl Γ A.
  Proof.
    eapply (split_to_over_tree@{l}).
    intros ; now eapply (Split).
  Qed.

  Lemma TreeEqSplit@{i j k l} {wl : wfLCon} {lA Γ A B}
    (d : DTree wl) :
    (forall wl', over_tree wl wl' d -> forall HA,
          WLogRelEq@{i j k l} lA wl' Γ A B HA) ->
    forall HA,
    WLogRelEq@{i j k l} lA wl Γ A B HA.
  Proof.
    intros Hyp ; pattern wl.
    eapply (split_to_over_tree@{l}).
    - intros wl' n ne HAt HAf HA ; cbn in *.
      unshelve eapply EqSplit' ; eauto.
      all: eapply WLtrans@{k i j k l} ; [ | eassumption ].
      all: now eapply LCon_le_step, wfLCon_le_id.
    - intros wl' Hover HA.
      now eapply Hyp.
  Qed.

 Lemma TreeTmSplit@{i j k l} {wl : wfLCon} {lA Γ t A}
    (d : DTree wl) :
    (forall wl', over_tree wl wl' d -> forall HA,
          WLogRelTm@{i j k l} lA wl' Γ A t HA) ->
    forall HA,
    WLogRelTm@{i j k l} lA wl Γ A t HA.
  Proof.
    intros Hyp ; pattern wl.
    eapply (split_to_over_tree@{l}).
    - intros wl' n ne HAt HAf HA ; cbn in *.
      unshelve eapply TmSplit' ; eauto.
      all: eapply WLtrans@{k i j k l} ; [ | eassumption ].
      all: now eapply LCon_le_step, wfLCon_le_id.
    - intros wl' Hover HA.
      now eapply Hyp.
  Qed.
  
  Lemma TreeTmEqSplit@{i j k l} {wl : wfLCon} {lA Γ t u A}
    (d : DTree wl) :
    (forall wl', over_tree wl wl' d -> forall HA,
          WLogRelTmEq@{i j k l} lA wl' Γ A t u HA) ->
    forall HA,
    WLogRelTmEq@{i j k l} lA wl Γ A t u HA.
  Proof.
    intros Hyp ; pattern wl.
    eapply (split_to_over_tree@{l}).
    - intros wl' n ne HAt HAf HA ; cbn in *.
      unshelve eapply TmEqSplit' ; eauto.
      all: eapply WLtrans@{k i j k l} ; [ | eassumption ].
      all: now eapply LCon_le_step, wfLCon_le_id.
    - intros wl' Hover HA.
      now eapply Hyp.
  Qed.
  
End Split.
