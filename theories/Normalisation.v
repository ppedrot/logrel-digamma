(** * LogRel.Normalisation: well-typed terms always reduce to a normal form. *)
From Coq Require Import CRelationClasses.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations LContexts Context NormalForms Weakening UntypedReduction
  GenericTyping DeclarativeTyping DeclarativeInstance.
From LogRel Require Import Monad LogicalRelation Validity Fundamental.
From LogRel.LogicalRelation Require Import Escape Neutral Induction ShapeView Reflexivity Monotonicity.
From LogRel.Substitution Require Import Escape Poly.

Inductive WN (wl : wfLCon) (t : term) :=
| WN_ret : forall (wn_val : term)
                  (wn_red : [ t ⤳* wn_val ]< wl >)
                  (wn_whnf : whnf wn_val),
    WN wl t
| ϝWN {n} {ne : not_in_LCon wl n} :
  forall (t' : term)
         (wn_red : [ t ⤳* t' ]< wl >)
         (wn_whnf : alphane wl n t'),
  WN (wl ,,l (ne, true)) t ->
  WN (wl ,,l (ne, false)) t ->
  WN wl t.

Fixpoint WN_size {wl t} (d : WN wl t) : nat :=
  match d with
  | WN_ret _ _ _ _ _ => 0
  | ϝWN _ _ _ _ _ Ht Hf => S ((WN_size Ht) + (WN_size Hf))
  end.

Lemma WN_wk : forall wl t (ρ : nat -> nat), WN wl t -> WN wl t⟨ρ⟩.
Proof.
  intros * ; induction 1 as [?? r | ].
  - econstructor 1 with r⟨ρ⟩.
    + now apply credalg_wk.
    + now apply whnf_ren.
  - eapply ϝWN ; [ | | eassumption | eassumption].
    + now apply credalg_wk.
    + now apply alphane_ren.
Qed.

Lemma WN_Ltrans {wl wl' : wfLCon}  {t}: wl' ≤ε wl -> WN wl t -> WN wl' t.
Proof.
  intros * f H.
  revert wl' f ; induction H as [?? r | ] ; intros.
  + econstructor 1 with r ; tea.
    now eapply redalg_Ltrans.
  + destruct (decidInLCon wl' n) as [i | i | notin].
    * eapply IHWN1.
      now eapply LCon_le_in_LCon .
    * eapply IHWN2.
      now eapply LCon_le_in_LCon .
    * unshelve eapply ϝWN ; [ | eassumption | | | | eapply IHWN1 | eapply IHWN2].
      2: eapply redalg_Ltrans ; eassumption.
      1: eapply alphane_Ltrans ; eassumption.
      all: now eapply LCon_le_up.
Defined.

Lemma WN_size_Ltrans {wl wl' : wfLCon} {t} (f: wl' ≤ε wl) (H : WN wl t) :
  WN_size (WN_Ltrans f H) <= WN_size H.
Proof.
  revert wl' f.
  induction H ; intros.
  - now constructor.
  - cbn ; destruct (decidInLCon wl' n) ; cbn.
    + etransitivity ; [now eapply IHWN1 | ].
      etransitivity ; [now eapply PeanoNat.Nat.le_succ_diag_r | ].
      now eapply le_n_S, PeanoNat.Nat.le_add_r.
    + etransitivity ; [now eapply IHWN2 | ].
      etransitivity ; [now eapply PeanoNat.Nat.le_succ_diag_r | ].
      now eapply le_n_S, PeanoNat.Nat.le_add_l.
    + eapply le_n_S, PeanoNat.Nat.add_le_mono.
      * now eapply IHWN1.
      * now eapply IHWN2.
Qed.
      

Lemma WN_exp : forall wl t u, [t ⤳* u]< wl > -> WN wl u -> WN wl t.
Proof.
  intros wl t u ? ; induction 1 as [?? r | ].
  - econstructor 1 with r; tea.
    now etransitivity.
  - unshelve eapply ϝWN ; [ | eassumption | eassumption | now etransitivity | | eapply IHWN1 | eapply IHWN2].
    1: eassumption.
    all: eapply redalg_Ltrans ; eauto.
    all: now eapply LCon_le_step, wfLCon_le_id.
Qed.

Lemma WN_red : forall wl t u, [t ⤳* u]< wl > -> WN wl t -> WN wl u.
Proof.
  intros wl t u Hred Hyp ; revert u Hred.
  induction Hyp as [?? r | ] ; intros u Hred.
  - econstructor 1 with r; tea.
    now eapply whred_red_det ; eauto.
  - unshelve eapply ϝWN ; [ | |  | | | eapply IHHyp1 | eapply IHHyp2].
    3: eassumption.
    1: eapply whred_red_alphane ; now eauto.
    all: eapply redalg_Ltrans ; eauto.
    all: now eapply LCon_le_step, wfLCon_le_id.
Qed.

Definition drop : wfLCon -> wfLCon.
Proof.
  intros [l Hl].
  destruct l.
  - exists nil ; assumption.
  - exists l.
    now inversion Hl ; subst.
Defined.

Lemma drop_equal (wl : wfLCon) {n} b {ne : not_in_LCon wl n} :
  drop (wl ,,l (ne, b)) = wl.
Proof.
  destruct wl as [l Hl] ; cbn.
  reflexivity.
Qed.


Lemma WN_whnf : forall wl t, whnf t -> WN wl t.
Proof.
intros; econstructor 1 with t; tea.
reflexivity.
Qed.

Lemma WN_isFun : forall wl t, isFun t -> WN wl t.
Proof.
intros wl t []; apply WN_whnf; now constructor.
Qed.

Lemma WN_isPair : forall wl t, isPair t -> WN wl t.
Proof.
intros wl t []; apply WN_whnf; now constructor.
Qed.

Lemma WN_split {wl : wfLCon} {t n} {ne : not_in_LCon wl n} :
  WN (wl,,l (ne, true)) t ->
  WN (wl,,l (ne, false)) t ->
  WN wl t.
Proof.
  intros HAt HAf.
  remember (WN_size HAt + WN_size HAf) as m.
  apply eq_sym, PeanoNat.Nat.eq_le_incl in Heqm.
  revert t wl n ne HAt HAf Heqm.
  induction m ; intros ; cbn in *.
  - enough (H : WN_size HAt = 0 /\ WN_size HAf = 0).
    + destruct H ; destruct HAt as [? red | ]; cbn in *.
      * destruct (alphane_disjunction_redalg red) as [ | [t'' [Ht Hne]]].
        -- now econstructor 1.
        -- unshelve econstructor 2 ; try eassumption.
           now econstructor 1.
      * now inversion H.
    + now apply PeanoNat.Nat.eq_add_0, PeanoNat.Nat.le_0_r.
  - destruct HAt as [? red | k ke ? red ] ; cbn in *.
    + destruct (alphane_disjunction_redalg red) as [ | [t'' [Ht Hne]]].
      * now econstructor 1.
      * unshelve econstructor 2 ; try eassumption.
        now econstructor 1.
    + destruct (alphane_disjunction_redalg red) as [ | [t'' [Ht Hne]]].
      * enough (Hyp : forall (X : not_in_LCon wl k) (b : bool),
                   WN (wl,,l (X, b)) t).
        -- unshelve econstructor 2 ; try eassumption.
           ++ now inversion ke.
           ++ eapply alphane_backtrans ; try eassumption.
              now eapply LCon_le_step, wfLCon_le_id.
           ++ now eapply Hyp.
           ++ now eapply Hyp.
        -- intros X b.
           eapply le_S_n in Heqm.
           destruct b ; unshelve eapply (IHm _ _ n).
           ++ abstract (inversion ke ; subst ;
                        econstructor ; intros ; now eauto).
           ++ unshelve eapply (WN_Ltrans _ HAt1).
              eapply LCon_le_in_LCon ; [now eapply LCon_le_up, LCon_le_step, wfLCon_le_id | ].
              now eapply in_there_l, in_here_l.
           ++ unshelve eapply (WN_Ltrans _ HAf) ; now eapply LCon_le_up, LCon_le_step, wfLCon_le_id.
           ++ abstract (inversion ke ; subst ;
                        econstructor ; intros ; now eauto).
           ++ unshelve eapply (WN_Ltrans _ HAt2).
              eapply LCon_le_in_LCon ; [now eapply LCon_le_up, LCon_le_step, wfLCon_le_id | ].
              now eapply in_there_l, in_here_l.
           ++ unshelve eapply (WN_Ltrans _ HAf) ; now eapply LCon_le_up, LCon_le_step, wfLCon_le_id.
           ++ etransitivity ; [ | eassumption].
              eapply PeanoNat.Nat.add_le_mono ; [ | now apply WN_size_Ltrans].
              etransitivity ; [ | eapply PeanoNat.Nat.le_add_r ].
              now apply WN_size_Ltrans.
           ++ etransitivity ; [ | eassumption].
              eapply PeanoNat.Nat.add_le_mono ; [ | now apply WN_size_Ltrans].
              etransitivity ; [ | eapply PeanoNat.Nat.le_add_l ].
              now apply WN_size_Ltrans.
      * unshelve econstructor 2 ; [.. | eassumption] ; eauto.
        unshelve econstructor 2 ; [ .. |  eassumption | eassumption].
        3: eassumption.
        assumption.
Qed.
  
Module Nf.

Definition nf : tag.
Proof.
constructor.
Qed.

#[export] Instance WfContextNf : WfContext nf := fun wl Γ => True.
#[export] Instance WfTypeNf : WfType nf := fun wl Γ A => True.
#[export] Instance TypingNf : Typing nf := fun wl Γ A t => True.
#[export] Instance ConvTypeNf : ConvType nf :=
  fun wl Γ A B => WN wl A × WN wl B.
#[export] Instance ConvTermNf : ConvTerm nf :=
  fun wl Γ A t u =>  WN wl t × WN wl u.
#[export] Instance ConvNeuConvNf : ConvNeuConv nf := fun wl Γ A m n => whne m × whne n.
#[export] Instance RedTypeNf : RedType nf := fun wl Γ A B => [A ⤳* B ]< wl >.
#[export] Instance RedTermNf : RedTerm nf := fun wl Γ A t u => [t ⤳* u ]< wl >.

#[export, refine] Instance WfCtxDeclProperties : WfContextProperties (ta := nf) := {}.
Proof.
all: try constructor.
Qed.

#[export, refine] Instance WfTypeDeclProperties : WfTypeProperties (ta := nf) := {}.
Proof.
all: try constructor.
Qed.

#[export, refine] Instance TypingDeclProperties : TypingProperties (ta := nf) := {}.
Proof.
all: try constructor.
Qed.

#[export, refine] Instance ConvTypeDeclProperties : ConvTypeProperties (ta := nf) := {}.
Proof.
all: try (intros; split; apply WN_whnf; now constructor).
+ intros * []; now split.
+ intros; split.
  - intros t u []; now split.
  - intros t u v [] []; now split.
+ intros * ? []; split; now apply WN_wk.
+ intros * ? ? []; split; now eapply WN_exp.
+ intros * ? [] ; split.
  all: now eapply WN_Ltrans.
+ intros * [HAt HBt] [HAf HBf] ; split ; now eapply WN_split.
Qed.

#[export, refine] Instance ConvTermDeclProperties : ConvTermProperties (ta := nf) := {}.
Proof.
  all: try (intros; split; apply WN_whnf; now constructor).
  - intros; split.
    + intros t u []; now split.
    + intros t u v [] []; now split.
  - intros * [] ?; now split.
  - intros * ? []; split; now apply WN_wk.
  - intros * ? ? ? ? ? ? []; split; now eapply WN_exp.
  - intros * ? []; split; now apply WN_whnf, whnf_whne.
  - intros * ? ? ? Hf ? Hg []; split.
    + apply WN_isFun; destruct Hf as [|? []]; now constructor.
    + apply WN_isFun; destruct Hg as [|? []]; now constructor.
  - intros * ? ? ? Hp ? Hp' ?; split; apply WN_isPair.
    + destruct Hp as [|? []]; now constructor.
    + destruct Hp' as [|? []]; now constructor.
  - intros * ? Hin ; split.
    + econstructor 1.
      * econstructor 2 ; [ | reflexivity].
        now eapply alphaRed.
      * destruct b ; cbn ; now constructor.
    + destruct b ; cbn ; econstructor 1 ; try reflexivity.
      all: now constructor.
  - intros * f [] ; split.
    all: now eapply WN_Ltrans.
  - intros * [] [] ; split ; now eapply WN_split.
Qed.

#[export, refine] Instance ConvNeuDeclProperties : ConvNeuProperties (ta := nf) := {}.
Proof.
+ intros; split.
  - intros t u []; now split.
  - intros t u v [] []; now split.
+ intros * [] ?; now split.
+ intros * ? []; split; now apply whne_ren.
+ intros * []; assumption.
+ intros; split; constructor.
+ intros * [] ?; split; now constructor.
+ intros * ? ? ? []; split; now constructor.
+ intros * ? []; split; now constructor.
+ intros * ? ? ? []; split; now constructor.
+ intros * []; split ; now constructor.
+ intros * []; split; now constructor.
+ intros * []; split; now constructor.
+ intros * ??????? []; split; now constructor.
+ intros * f [] ; split ; assumption.
+ intros * f [] ; split ; assumption.
Qed.

#[export, refine] Instance RedTermDeclProperties : RedTermProperties (ta := nf) := {}.
Proof.
all: try now (intros; apply redalg_one_step; constructor).
+ intros; now apply credalg_wk.
+ intros; eassumption.
+ now constructor.
+ intros; now apply redalg_app.
+ intros; now apply redalg_natElim.
+ intros; now apply redalg_boolElim.
+ intros * H ; induction H ; [ now eapply redIdAlg | econstructor 2 ; [ | eassumption]].
  now eapply alphaSubst.
+ intros; now apply redalg_natEmpty.
+ intros; now apply redalg_fst.
+ intros; now apply redalg_snd.
+ intros; now eapply redalg_idElim.
+ intros; assumption.
+ intros; now eapply redIdAlg.
+ intros ; now eapply RedAlgTrans.
+ intros ; now eapply redalg_Ltrans.
Qed.

#[export, refine] Instance RedTypeDeclProperties : RedTypeProperties (ta := nf) := {}.
Proof.
all: try now intros; eassumption.
+ intros; now apply credalg_wk.
+ constructor.
+ intros; now eapply redIdAlg.
+ intros ; now eapply RedAlgTrans.
+ intros ; now eapply redalg_Ltrans.
Qed.

#[export] Instance DeclarativeTypingProperties : GenericTypingProperties nf _ _ _ _ _ _ _ _ _ _ := {}.

End Nf.

Section Normalisation.

  Import Nf.

  Theorem typing_nf {wl} : WfDeclInductionConcl
    (fun _ _ => True)
    (fun wl Γ A => True)
    (fun wl Γ A t => True)
    (fun wl Γ A B => WN wl A × WN wl B)
    (fun wl Γ A t u => WN wl t × WN wl u)
  wl.
  Proof.
    red.
    prod_splitter.
    all: intros * H%Fundamental.
    - constructor.
    - constructor.
    - constructor.
    - destruct H as [? ? ? H].
      apply escapeEq in H as []; now split.
    - destruct H as [? ? ? ? H].
      apply escapeTmEq in H as []; now split.
  Qed.

  Import DeclarativeTypingData.

  Corollary normalisation {wl Γ A t} : [Γ |-[de] t : A]< wl > -> WN wl t.
  Proof. now intros ?%TermRefl%typing_nf. Qed.

  Corollary type_normalisation {wl Γ A} : [Γ |-[de] A]< wl > -> WN wl A.
  Proof. now intros ?%TypeRefl%typing_nf. Qed.

End Normalisation.

Import DeclarativeTypingProperties.

Record cored wl t t' : Prop := { _ : [t' ⤳ t]< wl > }.

Lemma cored_acc_backtrans wl wl' t (f : wl' ≤ε wl):
  Acc (cored wl') t ->
  Acc (cored wl) t.
Proof.
  induction 1 as [? H IH] ; econstructor ; intros t' [Hred].
  eapply IH.
  econstructor ; eapply red_Ltrans ; eassumption.
Qed.

Theorem typing_SN wl Γ t :
  well_formed wl Γ t ->
  Acc (cored wl) t.
Proof.
  intros [[] Hty].
  all: first [apply TypeRefl in Hty|apply TermRefl in Hty].
  all: eapply typing_nf in Hty as [? _].
  all: induction w as [?? wh red | ].
  - all: induction red.
    + econstructor.
      intros t' [red].
      exfalso.
      eapply whnf_nored ; tea.
    + econstructor.
      intros t'' [red'].
      eapply ored_det in red' as <-; [|exact o].
      apply IHred; tea.
  - clear IHw2 w1 w2 wn_red wn_whnf.
    eapply cored_acc_backtrans ; try eassumption.
    now eapply LCon_le_step, wfLCon_le_id.
  - induction red.
    + econstructor ; intros t' [Hred ].
      exfalso.
      now eapply whnf_nored.
    + econstructor.
      intros t'' [red'].
      eapply ored_det in red' as <-; [|exact o].
      apply IHred; now tea.
  - eapply cored_acc_backtrans ; try eassumption.
    now eapply LCon_le_step, wfLCon_le_id.
Qed.
