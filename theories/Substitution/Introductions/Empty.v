From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations LContexts Context NormalForms Weakening GenericTyping LogicalRelation Monad Validity.
From LogRel.LogicalRelation Require Import Induction Irrelevance Escape Reflexivity Weakening Monotonicity Split Neutral Transitivity Reduction Application Universe SimpleArr.
From LogRel.Substitution Require Import Irrelevance Properties Conversion SingleSubst Reflexivity Monotonicity.
From LogRel.Substitution.Introductions Require Import Universe Pi SimpleArr Var.

Set Universe Polymorphism.

Section Empty.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.


Lemma emptyRed {wl Γ l} : [|- Γ]< wl > -> [Γ ||-<l> tEmpty]< wl >.
Proof. 
  intros; eapply LREmpty_; constructor; eapply redtywf_refl; gen_typing.
Defined.


Lemma emptyValid {wl Γ l} (VΓ : [||-v Γ]< wl >) : [Γ ||-v<l> tEmpty | VΓ]< wl >.
Proof.
  unshelve econstructor; intros.
  + now eapply LogtoW, emptyRed.
  + eapply EqLogtoW.
    cbn; constructor; eapply redtywf_refl; gen_typing.
Defined.


Lemma emptyconvValid {wl Γ l} (VΓ : [||-v Γ]< wl >) (VEmpty : [Γ ||-v<l> tEmpty | VΓ]< wl >) : 
  [Γ ||-v<l> tEmpty ≅ tEmpty | VΓ | VEmpty]< wl >.
Proof.
  constructor; intros ; cbn.
  Wirrelevance0 ; [reflexivity | eapply EqLogtoW].
  enough [Δ ||-<l> tEmpty ≅ tEmpty | emptyRed wfΔ]< wl' > by irrelevance.
  constructor; cbn; eapply redtywf_refl; gen_typing.
  Unshelve.
  2: exact (emptyRed wfΔ).
  assumption.
Qed.

(* TODO: also appears in Nat.v, should probably be more central *)
Lemma redUOne {wl Γ} : [|- Γ]< wl > -> [Γ ||-U<one> U]< wl >.
Proof.
  intros ; econstructor; [easy| gen_typing|eapply redtywf_refl; gen_typing].
Defined.

Lemma emptyTermRed {wl Δ} (wfΔ : [|-Δ]< wl >) : [Δ ||-<one> tEmpty : U | LRU_ (redUOne wfΔ)]< wl >.
Proof.
  econstructor.
  + eapply redtmwf_refl; gen_typing.
  + constructor.
  + gen_typing.
  + now eapply (emptyRed (l:= zero)).
Defined.

Lemma emptyTermValid {wl Γ} (VΓ : [||-v Γ]< wl >):  [Γ ||-v<one> tEmpty : U | VΓ | UValid VΓ]< wl >.
Proof.
  constructor; intros.
  - exists (leaf _) ; intros.
    now eapply emptyTermRed. 
  - exists (leaf _) ; intros.
    eexists (emptyTermRed _) (emptyTermRed _) (emptyRed _); cbn.
    + eapply convtm_Ltrans ; [eassumption | now gen_typing].
    + now eapply (emptyRed (l:=zero)), wfc_Ltrans.
    + constructor; eapply redtywf_refl, wft_Ltrans ; [eassumption | ].
      now gen_typing.
      Unshelve. now eapply wfc_Ltrans.
Qed.


(* TODO: move *)
Lemma up_single_subst {t σ u} : t[up_term_term σ][u..] = t[u .:  σ].
Proof.  now bsimpl. Qed.

(* TODO: move *)
Lemma up_liftSubst_eq {σ t u} : t[up_term_term σ][u]⇑ = t[u .: ↑ >> up_term_term σ].
Proof.
  bsimpl. eapply ext_term; intros [|n]; cbn.
  1: reflexivity.
  unfold funcomp; now rewrite  rinstInst'_term.
Qed.

(* TODO: move *)
Lemma liftSubst_singleSubst_eq {t u v: term} : t[u]⇑[v..] = t[u[v..]..].
Proof. now bsimpl. Qed.

Definition emptyElim {wl Γ A} (P : term) {n} (NA : [Γ ||-Empty A]< wl >) (p : EmptyProp (k := wl) Γ n) : term.
Proof.
  destruct p.
  - exact (tEmptyElim P ne).
Defined.

Section EmptyElimRed.
  Context {wl Γ l P}
    (wfΓ : [|- Γ]< wl >)
    (NN : [Γ ||-Empty tEmpty]< wl >)
    (RN := LREmpty_ _ NN)
    (RP : [Γ,, tEmpty ||-<l> P]< wl >)
    (RPpt : forall n, [Γ ||-<l> n : _ | RN]< wl > -> W[Γ ||-<l> P[n..]]< wl >)
    (RPext : forall n n' (Rn : [Γ ||-<l> n : _ | RN]< wl >),
      [Γ ||-<l> n' : _ | RN]< wl > ->
      [Γ ||-<l> n ≅ n' : _ | RN]< wl > ->
      W[Γ ||-<l> P[n..] ≅ P[n'..] | RPpt _ Rn]< wl >).

  Definition emptyRedElimStmt :=
    (forall n (Rn : [Γ ||-<l> n : _ | RN]< wl >), 
      W[Γ ||-<l> tEmptyElim P n : _ | RPpt _ Rn ]< wl > ×
      W[Γ ||-<l> tEmptyElim P n ≅ tEmptyElim P (EmptyRedTm.nf Rn) : _ | RPpt _ Rn]< wl >) ×
    (forall n (Nn : EmptyProp Γ n) (Rn : [Γ ||-<l> n : _ | RN]< wl >), 
      W[Γ ||-<l> tEmptyElim P n : P[n..] | RPpt _ Rn ]< wl > ×
      W[Γ ||-<l> tEmptyElim P n ≅ emptyElim P NN Nn : _ | RPpt _ Rn]< wl >).

  Lemma emptyElimRedAux : emptyRedElimStmt.
  Proof.
    escape.
    apply EmptyRedInduction.
    - intros ? nf red ? nfprop ih.
      assert [Γ ||-<l> nf : _ | RN]< wl >. 1:{
        econstructor; tea.
        eapply redtmwf_refl; gen_typing.
      }
      eapply WredSubstTerm.
      + eapply WLRTmRedConv. 
        2: unshelve eapply ih; tea.
        eapply RPext. 
        2: eapply LRTmEqSym.
        1,2: eapply redwfSubstTerm; tea.
      + eapply redtm_emptyelim; tea.
        cbn; gen_typing.
    - intros ? [] ?.
      apply Wreflect.
      + apply Wcompleteness.
      + now eapply ty_emptyElim.
      + now eapply ty_emptyElim.
      + eapply convneu_emptyElim; tea.
        { eapply escapeEq, reflLRTyEq. }
    Unshelve. all: tea.
  Qed.

  Lemma emptyElimRed : forall n (Rn : [Γ ||-<l> n : _ | RN]< wl >), W[Γ ||-<l> tEmptyElim P n : _ | RPpt _ Rn ]< wl >.
  Proof. intros. apply (fst emptyElimRedAux). Qed.
End EmptyElimRed.


Section EmptyElimRedEq.
  Context {wl Γ l P Q}
    (wfΓ : [|- Γ]< wl >)
    (NN : [Γ ||-Empty tEmpty]< wl >)
    (RN := LREmpty_ _ NN)
    (RP : [Γ,, tEmpty ||-<l> P]< wl >)
    (RQ : [Γ,, tEmpty ||-<l> Q]< wl >)
    (eqPQ : [Γ,, tEmpty |- P ≅ Q]< wl >)
    (RPpt : forall n, [Γ ||-<l> n : _ | RN]< wl > -> W[Γ ||-<l> P[n..]]< wl >)
    (RQpt : forall n, [Γ ||-<l> n : _ | RN]< wl > -> W[Γ ||-<l> Q[n..]]< wl >)
    (RPQext : forall n n' (Rn : [Γ ||-<l> n : _ | RN]< wl >),
      [Γ ||-<l> n' : _ | RN]< wl > ->
      [Γ ||-<l> n ≅ n' : _ | RN]< wl > ->
      W[Γ ||-<l> P[n..] ≅ Q[n'..] | RPpt _ Rn]< wl >).    

  Lemma RPext : forall n n' (Rn : [Γ ||-<l> n : _ | RN]< wl >),
      [Γ ||-<l> n' : _ | RN]< wl > ->
      [Γ ||-<l> n ≅ n' : _ | RN]< wl > ->
      W[Γ ||-<l> P[n..] ≅ P[n'..] | RPpt _ Rn]< wl >.
  Proof.
    intros. eapply WtransEq; [| eapply WLRTyEqSym ]; eapply RPQext; cycle 1; tea.
    now eapply reflLRTmEq.
    Unshelve. 2,3: eauto.
  Qed.

  Lemma emptyElimRedAuxLeft : @emptyRedElimStmt _ _ _ P NN RPpt.
  Proof.
    eapply emptyElimRedAux; tea.
    + eapply RPext.
  Qed.

  Lemma emptyElimRedAuxRight : @emptyRedElimStmt _ _ _ Q NN RQpt.
  Proof.
    eapply emptyElimRedAux; tea.
    + intros. eapply WtransEq; [eapply WLRTyEqSym |]; eapply RPQext; cycle 1; tea.
      now eapply reflLRTmEq.
    Unshelve. all:tea.
  Qed.

  Lemma emptyElimRedEqAux :
    (forall n n' (Rnn' : [Γ ||-<l> n ≅ n' : _ | RN]< wl >) (Rn : [Γ ||-<l> n : _ | RN]< wl >) (Rn' : [Γ ||-<l> n' : _ | RN]< wl >),
      W[Γ ||-<l> tEmptyElim P n ≅ tEmptyElim Q n' : _ | RPpt _ Rn ]< wl >) ×
    (forall n n' (Rnn' : EmptyPropEq wl Γ n n') (Rn : [Γ ||-<l> n : _ | RN]< wl >) (Rn' : [Γ ||-<l> n' : _ | RN]< wl >),
      W[Γ ||-<l> tEmptyElim P n ≅ tEmptyElim Q n' : _ | RPpt _ Rn ]< wl >).
  Proof.
    apply EmptyRedEqInduction.
    - intros ?? nfL nfR redL redR ? prop ih RL RR; edestruct @EmptyPropEq_whnf; eauto. 
      assert [Γ ||-<l> nfL : _ | RN]< wl > by (eapply redTmFwd; cycle 1; tea).
      assert [Γ ||-<l> nfR : _ | RN]< wl > by (eapply redTmFwd; cycle 1; tea).
      eapply WLREqTermHelper.
      * eapply (fst emptyElimRedAuxLeft).
      * eapply (fst emptyElimRedAuxRight).
      * eapply RPQext. 1: tea.
        now econstructor.
      * eapply WLRTmEqRedConv.
        + eapply RPext; tea. 
          eapply LRTmEqSym; eapply redwfSubstTerm; cycle 1; tea.
        + unshelve erewrite (redtmwf_det _ _ (EmptyRedTm.red RL) redL); tea.
          1: dependent inversion RL; subst; cbn; now eapply EmptyProp_whnf.
          unshelve erewrite (redtmwf_det _ _ (EmptyRedTm.red RR) redR); tea.
          1: dependent inversion RR; subst; cbn; now eapply EmptyProp_whnf.
          now eapply ih.
        Unshelve. tea. 2, 4: tea. 
    - intros ?? neueq ??. escape. inversion neueq.
      assert [Γ |- P[ne..] ≅ Q[ne'..]]< wl >. 1:{
        eapply WescapeEq. eapply RPQext; tea.
        econstructor.
        1,2: now eapply redtmwf_refl.
        2: now constructor.
        gen_typing.
      }
      eapply WneuTermEq.
      + eapply ty_emptyElim; tea.
      + eapply ty_conv. 
        1: eapply ty_emptyElim; tea.
        now symmetry.
      + eapply convneu_emptyElim ; tea.
      Unshelve. tea.
  Qed.

  Lemma emptyElimRedEq :
    (forall n n' (Rnn' : [Γ ||-<l> n ≅ n' : _ | RN]< wl >) (Rn : [Γ ||-<l> n : _ | RN]< wl >) (Rn' : [Γ ||-<l> n' : _ | RN]< wl >), 
      W[Γ ||-<l> tEmptyElim P n ≅ tEmptyElim Q n' : _ | RPpt _ Rn ]< wl >).
  Proof. apply emptyElimRedEqAux. Qed.
End EmptyElimRedEq.



Section EmptyElimValid.
  Context {wl Γ l P}
    (VΓ : [||-v Γ]< wl >)
    (VN := emptyValid (l:=l) VΓ)
    (VΓN := validSnoc' VΓ VN)
    (VP : [Γ ,, tEmpty ||-v<l> P | VΓN]< wl >).
  

  Lemma emptyElimValid {n}
    (Vn : [Γ ||-v<l> n : tEmpty | VΓ | VN]< wl >)
    (VPn := substS VP Vn)
    : [Γ ||-v<l> tEmptyElim P n : _ | VΓ | VPn]< wl >.
  Proof.
    constructor; intros.
    - instValid Vσ; cbn.
      epose proof (Vuσ := liftSubstS' VN Vσ).
      instValid Vuσ; escape ; Wescape.
      unshelve eapply TreeTmSplit.
      1: do 2 eapply DTree_fusion ; shelve.
      intros wl'' Ho HA.
      pose (f' := over_tree_le Ho).
      Wirrelevance0.  1: now rewrite singleSubstComm'.
      unshelve eapply emptyElimRed; tea.
      + econstructor ; eapply redtywf_refl.
        eapply wft_term, ty_empty, wfc_Ltrans ; eassumption.
      + intros m Rm ; cbn in *.
        rewrite up_single_subst. 
        unshelve eapply validTy.
        6 : eassumption.
        1: now eapply wfLCon_le_trans.
        1: now eapply wfc_Ltrans.
        unshelve econstructor; [| cbn ; now eapply TmLogtoW].
        now eapply subst_Ltrans.
      + irrelevanceRefl.
        eapply RVn, over_tree_fusion_l, over_tree_fusion_l ; exact Ho.
      + eapply RVP, over_tree_fusion_r, over_tree_fusion_l ; exact Ho.
      + intros m m' Rm Rm' Rmm'; cbn.
        Wirrelevance0. 1: now rewrite up_single_subst.
        rewrite up_single_subst.
        unshelve eapply validTyExt; cycle 3 ; tea.
        1: now eapply wfLCon_le_trans.
        1: now eapply wfc_Ltrans.
        1,2: unshelve econstructor; [now eapply subst_Ltrans | now eapply TmLogtoW].
        unshelve econstructor; [|cbn ; now eapply TmEqLogtoW].
        eapply eqsubst_Ltrans.
        bsimpl; cbn; now eapply reflSubst.
        Unshelve.
        3: eapply  over_tree_fusion_l, over_tree_fusion_r ; exact Ho.
        now constructor.
    - instAllValid Vσ Vσ' Vσσ'.
      pose (Vuσ := liftSubstS' VN Vσ).
      pose proof (Vuσ' := liftSubstS' VN Vσ').
      pose proof (Vuσrea :=  liftSubstSrealign' VN Vσσ' Vσ').
      pose proof (Vuσσ' := liftSubstSEq' VN Vσσ').
      instValid Vuσ'; instAllValid Vuσ Vuσrea Vuσσ'; escape ; Wescape.
      unshelve eapply TreeTmEqSplit.
      1: do 2 eapply DTree_fusion ; [ .. | eapply DTree_fusion] ; shelve.
      intros wl'' Ho HA.
      pose (f' := over_tree_le Ho).
      Wirrelevance0.  1: now rewrite singleSubstComm'.
      unshelve eapply emptyElimRedEq; tea; fold subst_term.
      + econstructor ; eapply redtywf_refl.
        eapply wft_term, ty_empty, wfc_Ltrans ; eassumption.
      + intros m Rm.
        rewrite up_single_subst. 
        unshelve eapply validTy; cycle 5; tea.
        1: unshelve econstructor; [now eapply subst_Ltrans | now eapply TmLogtoW].
      + irrelevanceRefl.
        eapply RVn, over_tree_fusion_l, over_tree_fusion_l ; exact Ho.
      + eapply RVP0, over_tree_fusion_r, over_tree_fusion_l ; exact Ho.
      + eapply RVP, over_tree_fusion_l, over_tree_fusion_r ; exact Ho.
      + now eapply convty_Ltrans.
      + intros m Rm.
        rewrite up_single_subst. 
        unshelve eapply validTy; cycle 5; tea.
        1: unshelve econstructor; [now eapply subst_Ltrans | now eapply TmLogtoW].
      + intros m m' Rm Rm' Rmm'; cbn.
        Wirrelevance0. 1: now rewrite up_single_subst.
        rewrite up_single_subst.
        unshelve eapply validTyExt ;cycle 6.
        7: eassumption.
        1,2: unshelve econstructor; [now eapply subst_Ltrans | now eapply TmLogtoW].
        1: unshelve econstructor; [|cbn ; now eapply TmEqLogtoW].
        1: now eapply eqsubst_Ltrans.
      + irrelevanceRefl ; eapply REVn.
        eapply over_tree_fusion_l, over_tree_fusion_r, over_tree_fusion_r ; exact Ho.
      + irrelevanceRefl ; eapply RVn0.
        eapply over_tree_fusion_r, over_tree_fusion_r, over_tree_fusion_r ; exact Ho.
        Unshelve.
        all: try eassumption.
  Qed.
End EmptyElimValid.

Lemma emptyElimCongValid {wl Γ l P Q n n'}
    (VΓ : [||-v Γ]< wl >)
    (VN := emptyValid (l:=l) VΓ)
    (VΓN := validSnoc' VΓ VN)
    (VP : [Γ ,, tEmpty ||-v<l> P | VΓN]< wl >)
    (VQ : [Γ ,, tEmpty ||-v<l> Q | VΓN]< wl >)
    (VPQ : [Γ ,, tEmpty ||-v<l> P ≅ Q | VΓN | VP]< wl >)
    (Vn : [Γ ||-v<l> n : _ | VΓ | VN]< wl >)
    (Vn' : [Γ ||-v<l> n' : _ | VΓ | VN]< wl >)
    (Veqn : [Γ ||-v<l> n ≅ n' : _ | VΓ | VN]< wl >)
    (VPn := substS VP Vn) :
    [Γ ||-v<l> tEmptyElim P n ≅ tEmptyElim Q n' : _ | VΓ | VPn]< wl >.
Proof.
  constructor; intros.
  pose (Vuσ := liftSubstS' VN Vσ).
  instValid Vσ; instValid Vuσ; escape ; Wescape.
  unshelve eapply TreeTmEqSplit.
  1: do 2 eapply DTree_fusion ; [ .. | eapply DTree_fusion | eapply DTree_fusion] ; shelve.
  intros wl'' Ho HA.
  pose proof (f':= over_tree_le Ho).
  Wirrelevance0.  1: now rewrite singleSubstComm'.
  unshelve eapply emptyElimRedEq; tea; fold subst_term.
  - unshelve econstructor.
    eapply redtywf_refl, wft_term, ty_empty.
    now eapply wfc_Ltrans.
  - intros m Rm.
    rewrite up_single_subst. 
    unshelve eapply validTy; cycle 4; tea.
    + now eapply wfc_Ltrans.
    + unshelve econstructor; [ | now eapply TmLogtoW].
      now eapply subst_Ltrans.
  - irrelevanceRefl ; eapply RVn.
    eapply over_tree_fusion_l, over_tree_fusion_l, over_tree_fusion_r ; exact Ho.
  - eapply RVP, over_tree_fusion_l, over_tree_fusion_l ; exact Ho.
  - eapply RVQ, over_tree_fusion_r, over_tree_fusion_l ; exact Ho.
  - now eapply convty_Ltrans.
  - intros m Rm ; cbn in *.
    rewrite up_single_subst. 
    unshelve eapply validTy; cycle 4; tea.
    + now eapply wfc_Ltrans.
    + unshelve econstructor; [ | now eapply TmLogtoW].
      now eapply subst_Ltrans.
  - intros m m' Rm Rm' Rmm'; cbn.
    Wirrelevance0. 1: now rewrite up_single_subst.
    rewrite up_single_subst.
    eapply WtransEq; cycle 1.
    + unshelve eapply validTyEq. 
      9: eassumption.
      3: unshelve econstructor; [ | now eapply TmLogtoW].
      2: now eapply subst_Ltrans.
    + unshelve eapply validTyExt; cycle 3 ; tea.
      3: unshelve econstructor; [ now eapply subst_Ltrans | now eapply TmLogtoW].
      1: unshelve econstructor; [ now eapply subst_Ltrans | now eapply TmLogtoW].
      1: unshelve econstructor; [ eapply eqsubst_Ltrans | now eapply TmEqLogtoW].
      bsimpl. eapply reflSubst.
  - irrelevanceRefl ; eapply RVeqn.
    now eapply over_tree_fusion_r, over_tree_fusion_l, over_tree_fusion_r ; exact Ho.
  - irrelevanceRefl ; eapply RVn'.
    now eapply over_tree_fusion_l, over_tree_fusion_r, over_tree_fusion_r ; exact Ho.
    Unshelve.
    2,6,7: now do 3 (eapply over_tree_fusion_r) ; exact Ho.
    all: assumption.
Qed.

End Empty.
