From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations LContexts Context NormalForms Weakening GenericTyping Monad LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Induction Irrelevance Escape Reflexivity Weakening Monotonicity Split Neutral Transitivity Reduction Application Universe SimpleArr.
From LogRel.Substitution Require Import Irrelevance Properties Conversion SingleSubst Reflexivity Monotonicity.
From LogRel.Substitution.Introductions Require Import Universe Pi SimpleArr Var.

Set Universe Polymorphism.

Section Nat.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.


Lemma natRed {wl Γ l} : [|- Γ]< wl > -> [Γ ||-<l> tNat]< wl >.
Proof. 
  intros; eapply LRNat_; constructor; eapply redtywf_refl; gen_typing.
Defined.

Lemma WnatRed {wl Γ l} : [|- Γ]< wl > -> W[Γ ||-<l> tNat]< wl >.
Proof.
  intros ; now eapply LogtoW, natRed.
Defined.

Lemma natValid {wl Γ l} (VΓ : [||-v Γ]< wl >) : [Γ ||-v<l> tNat | VΓ]< wl >.
Proof.
  unshelve econstructor; intros.
  + now eapply WnatRed.
  + cbn ; eapply EqLogtoW.
    constructor; eapply redtywf_refl.
    now gen_typing.
Defined.

Lemma natconvValid {wl Γ l} (VΓ : [||-v Γ]< wl >) (VNat : [Γ ||-v<l> tNat | VΓ]< wl >) : 
  [Γ ||-v<l> tNat ≅ tNat | VΓ | VNat]< wl >.
Proof.
  constructor; intros ; cbn.
  unshelve eapply EqLogtoW' ; [exact (natRed wfΔ) | ].
  constructor; cbn; eapply redtywf_refl; gen_typing.
Qed.

Lemma redUOne {wl Γ} : [|- Γ]< wl > -> [Γ ||-U<one> U]< wl >.
Proof.
  intros ; econstructor; [easy| gen_typing|eapply redtywf_refl; gen_typing].
Defined.

Lemma natTermRed {wl Δ} (wfΔ : [|-Δ]< wl >) : [Δ ||-<one> tNat : U | LRU_ (redUOne wfΔ)]< wl >.
Proof.
  econstructor.
  + eapply redtmwf_refl; gen_typing.
  + constructor.
  + gen_typing.
  + now eapply (natRed (l:= zero)).
Defined.

Lemma natTermValid {wl Γ} (VΓ : [||-v Γ]< wl >):  [Γ ||-v<one> tNat : U | VΓ | UValid VΓ]< wl >.
Proof.
  constructor; intros.
  - eapply TmLogtoW' ; eapply natTermRed.
    Unshelve. assumption.
  - unshelve eapply TmEqLogtoW'.
    1: cbn ; eapply LRU_ ; unshelve econstructor ; [ | now econstructor | eassumption |.. ].
    1: eapply redtywf_refl ; gen_typing.
    eexists (natTermRed wfΔ) (natTermRed wfΔ) (natRed wfΔ); cbn.
    + gen_typing.
    + now eapply (natRed (l:=zero)).
    + constructor; eapply redtywf_refl; gen_typing.
Qed.

Lemma zeroRed {wl Γ l} {NN : [Γ ||-Nat tNat]< wl >} (wfΓ : [|- Γ]< wl >): [Γ ||-<l> tZero : _ | LRNat_ l NN]< wl >.
Proof.
  exists tZero.
  1,2: gen_typing.
  constructor.
Defined.

Lemma WzeroRed {wl Γ l} {NN : [Γ ||-Nat tNat]< wl >} (wfΓ : [|- Γ]< wl >): W[Γ ||-<l> tZero : _ | LogtoW (LRNat_ l NN)]< wl >.
Proof.
  exists (leaf _).
  intros wl' Ho Ho' ; pose (f := over_tree_le Ho).
  exists tZero.
  + eapply redtmwf_Ltrans ; [eassumption | now gen_typing].
  + eapply convtm_Ltrans ; [eassumption | now gen_typing].
  + constructor.
Defined.

Lemma zeroRedEq {wl Γ l} {NN : [Γ ||-Nat tNat]< wl >} (wfΓ : [|- Γ]< wl >): [Γ ||-<l> tZero ≅ tZero : _ | LRNat_ l NN]< wl >.
Proof.
  exists tZero tZero.
  1-3: gen_typing.
  constructor.
Defined.

Lemma WzeroRedEq {wl Γ l} {NN : [Γ ||-Nat tNat]< wl >} (wfΓ : [|- Γ]< wl >):
  W[Γ ||-<l> tZero ≅ tZero : _ | LogtoW (LRNat_ l NN)]< wl >.
Proof.
  exists (leaf _) ; intros wl' Ho Ho' ; pose (f := over_tree_le Ho).
  exists tZero tZero.
  1,2: eapply redtmwf_Ltrans ; [eassumption | now gen_typing].
  + eapply convtm_Ltrans ; [eassumption | now gen_typing].
  + constructor.
Defined.

Lemma zeroValid {wl Γ l} (VΓ : [||-v Γ]< wl >): 
  [Γ ||-v<l> tZero : tNat | VΓ | natValid VΓ]< wl >.
Proof.
  constructor; intros ; cbn.
  + eapply TmLogtoW, zeroRed ; assumption.
  + eapply TmEqLogtoW, zeroRedEq; tea.
Qed.

Lemma succRed {wl Γ l n} {NN : [Γ ||-Nat tNat]< wl >} :
  [Γ ||-<l> n : _ | LRNat_ l NN]< wl > ->
  [Γ ||-<l> tSucc n : _ | LRNat_ l NN]< wl >.
Proof.
  intros Rn; exists (tSucc n).
  + eapply redtmwf_refl; eapply ty_succ; now escape.
  + eapply convtm_succ; eapply escapeEqTerm; now eapply reflLRTmEq.
  + now constructor.
Defined.

Lemma WsuccRed {wl Γ l n} {NN : [Γ ||-Nat tNat]< wl >} :
  W[Γ ||-<l> n : _ | LogtoW (LRNat_ l NN) ]< wl > ->
  W[Γ ||-<l> tSucc n : _ | LogtoW (LRNat_ l NN)]< wl >.
Proof.
  intros Rn ; exists (WTTm _ Rn).
  intros wl' Ho Ho' ; exists (tSucc n).
  + eapply redtmwf_refl; eapply ty_succ, ty_Ltrans ; [ | now Wescape].
    now eapply over_tree_le.
  + eapply convtm_succ; eapply escapeEqTerm, reflLRTmEq.
    now unshelve eapply Rn.
  + constructor ; now unshelve eapply Rn.
Defined.

Lemma succRedEq {wl Γ l n n'} {NN : [Γ ||-Nat tNat]< wl >} :
  [Γ ||-<l> n : _ | LRNat_ l NN]< wl > ->
  [Γ ||-<l> n' : _ | LRNat_ l NN]< wl > ->
  [Γ ||-<l> n ≅ n' : _ | LRNat_ l NN]< wl > ->
  [Γ ||-<l> tSucc n ≅ tSucc n' : _ | LRNat_ l NN]< wl >.
Proof.
  intros ???; escape; exists (tSucc n) (tSucc n').
  1,2: eapply redtmwf_refl; now eapply ty_succ.
  + now eapply convtm_succ.
  + now constructor.
Defined.

Lemma WsuccRedEq {wl Γ l n n'} {NN : [Γ ||-Nat tNat]< wl >} :
  W[Γ ||-<l> n : _ | LogtoW (LRNat_ l NN)]< wl > ->
  W[Γ ||-<l> n' : _ | LogtoW (LRNat_ l NN) ]< wl > ->
  W[Γ ||-<l> n ≅ n' : _ | LogtoW (LRNat_ l NN)]< wl > ->
  W[Γ ||-<l> tSucc n ≅ tSucc n' : _ | LogtoW (LRNat_ l NN)]< wl >.
Proof.
  intros Rn Rn' Rnn'.
  econstructor ; intros wl' Ho Ho'.
  pose (f:= over_tree_le Ho) ; Wescape.
  exists (tSucc n) (tSucc n').
  1,2: now eapply redtmwf_refl, ty_succ, ty_Ltrans.
  - now eapply convtm_succ, convtm_Ltrans.
  - constructor ; eapply Rnn'.
    eassumption.
Defined.

Lemma succRedInv {wl Γ l n} {NN : [Γ ||-Nat tNat]< wl >} :
  [Γ ||-<l> tSucc n : _ | LRNat_ l NN]< wl > ->
  [Γ ||-<l> n : _ | LRNat_ l NN]< wl >.
Proof.
  intros RSn; inversion RSn; subst. 
  unshelve epose proof (redtmwf_whnf red _). 1: constructor.
  subst. inversion prop; subst; tea.
  match goal with H : [ _ ||-NeNf _ : _]< wl > |- _ => destruct H; apply convneu_whne in refl; inv_whne end.
Qed.

Lemma succValid {wl Γ l n} (VΓ : [||-v Γ]< wl >) 
  (Vn : [Γ ||-v<l> n : tNat | VΓ | natValid VΓ]< wl >) :
  [Γ ||-v<l> tSucc n : tNat | VΓ | natValid VΓ]< wl >.
Proof.
  constructor; intros; cbn.
  - instValid Vσ ; now unshelve eapply WsuccRed.
  - instAllValid Vσ Vσ' Vσσ'; now unshelve eapply WsuccRedEq.
Qed.

Lemma succcongValid {wl Γ l n n'} (VΓ : [||-v Γ]< wl >) 
  (Vn : [Γ ||-v<l> n : tNat | VΓ | natValid VΓ]< wl >)
  (Vn' : [Γ ||-v<l> n' : tNat | VΓ | natValid VΓ]< wl >)
  (Veqn : [Γ ||-v<l> n ≅ n' : tNat | VΓ | natValid VΓ]< wl >) :
  [Γ ||-v<l> tSucc n ≅ tSucc n' : tNat | VΓ | natValid VΓ]< wl >.
Proof.
  constructor; intros; cbn; instValid Vσ; now unshelve eapply WsuccRedEq.
Qed.


Lemma elimSuccHypTy_subst {P} σ :
  elimSuccHypTy P[up_term_term σ] = (elimSuccHypTy P)[σ].
Proof.
  unfold elimSuccHypTy.
  cbn. rewrite shift_up_eq.
  rewrite liftSubstComm. cbn. 
  now rewrite up_liftSubst_eq.
Qed.


Lemma liftSubst_singleSubst_eq {t u v: term} : t[u]⇑[v..] = t[u[v..]..].
Proof. now bsimpl. Qed.


Definition natElim {wl Γ A} (P hz hs : term) {n} {NA : [Γ ||-Nat A]< wl >} (p : NatProp NA n) : term.
Proof.
  destruct p.
  - exact hz.
  - exact (tApp (tApp hs n) (tNatElim P hz hs n)).
  - exact (tNatElim P hz hs ne).
Defined.

Section NatElimRed.
  Context {wl Γ l P hs hz}
    (wfΓ : [|- Γ]< wl >)
    (NN : [Γ ||-Nat tNat]< wl >)
    (RN := (LRNat_ _ NN))
    (RP : [Γ,, tNat ||-<l> P]< wl >)
    (RPpt : forall n, [Γ ||-<l> n : _ | RN]< wl > -> W[Γ ||-<l> P[n..]]< wl >)
    (RPext : forall n n' (Rn : [Γ ||-<l> n : _ | RN]< wl >),
      [Γ ||-<l> n' : _ | RN]< wl > ->
      [Γ ||-<l> n ≅ n' : _ | RN]< wl > ->
      W[Γ ||-<l> P[n..] ≅ P[n'..] | RPpt _ Rn]< wl >)
    (RPz := RPpt _ (zeroRed wfΓ))
    (Rhz : W[Γ ||-<l> hz : P[tZero..] | RPz]< wl >) 
    (RPs : W[Γ ||-<l> elimSuccHypTy P]< wl >)
    (Rhs : W[Γ ||-<l> hs : _ | RPs]< wl >).

  Definition natRedElimStmt :=
    (forall n (Rn : [Γ ||-<l> n : _ | RN]< wl >), 
      W[Γ ||-<l> tNatElim P hz hs n : _ | RPpt _ Rn ]< wl > ×
      W[Γ ||-<l> tNatElim P hz hs n ≅ tNatElim P hz hs (NatRedTm.nf Rn) : _ | RPpt _ Rn]< wl >) ×
    (forall n (Nn : NatProp NN n) (Rn : [Γ ||-<l> n : _ | RN]< wl >), 
      W[Γ ||-<l> tNatElim P hz hs n : _ | RPpt _ Rn ]< wl > ×
      W[Γ ||-<l> tNatElim P hz hs n ≅ natElim P hz hs Nn : _ | RPpt _ Rn]< wl >).

  Lemma natElimRedAux : natRedElimStmt.
  Proof.
    escape ; Wescape.
    apply NatRedInduction.
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
      + eapply redtm_natelim; tea.
        cbn; gen_typing.
    - intros. 
      eapply WredSubstTerm.
      2: eapply redtm_natElimZero; tea.
      Wirrelevance.
    - intros n Rn ih RSucc; change [Γ ||-<l> n : tNat | RN]< wl > in Rn.
      eapply WredSubstTerm.
      2: eapply redtm_natElimSucc; tea.
      2: now escape.
      eapply Wsimple_appTerm.
      2: eapply ih.
      Wirrelevance0.
      2: unshelve eapply (WappTerm RPs Rhs (TmLogtoW _ Rn)).
      now bsimpl.
    - intros ? [] ?.
      eapply Wreflect.
      + apply Wcompleteness.
      + now eapply ty_natElim.
      + now eapply ty_natElim.
      + eapply convneu_natElim; tea.
        { eapply escapeEq, reflLRTyEq. }
        { now eapply WescapeEqTerm, WreflLRTmEq. }
        { eapply WescapeEqTerm; now eapply WreflLRTmEq. }
    Unshelve.
    * eapply WArrRedTy; now eapply RPpt.
    * rewrite subst_arr. eapply WArrRedTy.
      2: rewrite liftSubst_singleSubst_eq; cbn.
      all: now eapply RPpt.
    * exact l.
    * assumption.
  Qed.

  Lemma natElimRed : forall n (Rn : [Γ ||-<l> n : _ | RN]< wl >), W[Γ ||-<l> tNatElim P hz hs n : _ | RPpt _ Rn ]< wl >.
  Proof. intros. apply (fst natElimRedAux). Qed.
End NatElimRed.


Section NatElimRedEq.
  Context {wl Γ l P Q hs hs' hz hz'}
    (wfΓ : [|- Γ]< wl >)
    (NN : [Γ ||-Nat tNat]< wl >)
    (RN := LRNat_ _ NN)
    (RP : [Γ,, tNat ||-<l> P]< wl >)
    (RQ : [Γ,, tNat ||-<l> Q]< wl >)
    (eqPQ : [Γ,, tNat |- P ≅ Q]< wl >)
    (RPpt : forall n, [Γ ||-<l> n : _ | RN]< wl > -> W[Γ ||-<l> P[n..]]< wl >)
    (RQpt : forall n, [Γ ||-<l> n : _ | RN]< wl > -> W[Γ ||-<l> Q[n..]]< wl >)
    (RPQext : forall n n' (Rn : [Γ ||-<l> n : _ | RN]< wl >),
      [Γ ||-<l> n' : _ | RN]< wl > ->
      [Γ ||-<l> n ≅ n' : _ | RN]< wl > ->
      W[Γ ||-<l> P[n..] ≅ Q[n'..] | RPpt _ Rn]< wl >)
    (RPz := RPpt _ (zeroRed wfΓ))
    (RQz := RQpt _ (zeroRed wfΓ))
    (Rhz : W[Γ ||-<l> hz : P[tZero..] | RPz]< wl >) 
    (RQhz : W[Γ ||-<l> hz' : Q[tZero..] | RQz]< wl >) 
    (RPQhz : W[Γ ||-<l> hz ≅ hz' : _ | RPz]< wl >)
    (RPs : W[Γ ||-<l> elimSuccHypTy P]< wl >)
    (RQs : W[Γ ||-<l> elimSuccHypTy Q]< wl >)
    (Rhs : W[Γ ||-<l> hs : _ | RPs]< wl >)
    (RQhs : W[Γ ||-<l> hs' : _ | RQs]< wl >)
    (RPQhs : W[Γ ||-<l> hs ≅ hs' : _ | RPs ]< wl >)
    .

  Lemma RPext : forall n n' (Rn : [Γ ||-<l> n : _ | RN]< wl >),
      [Γ ||-<l> n' : _ | RN]< wl > ->
      [Γ ||-<l> n ≅ n' : _ | RN]< wl > ->
      W[Γ ||-<l> P[n..] ≅ P[n'..] | RPpt _ Rn]< wl >.
  Proof.
    intros. eapply WtransEq; [| eapply WLRTyEqSym ]; eapply RPQext; cycle 1; tea.
    now eapply reflLRTmEq.
    Unshelve. 2,3: eauto.
  Qed.

  Lemma natElimRedAuxLeft : @natRedElimStmt _ _ _ P hs hz NN RPpt.
  Proof.
    eapply natElimRedAux; tea.
    + eapply RPext.
  Qed.

  Lemma natElimRedAuxRight : @natRedElimStmt _ _ _ Q hs' hz' NN RQpt.
  Proof.
    eapply natElimRedAux; tea.
    + intros. eapply WtransEq; [eapply WLRTyEqSym |]; eapply RPQext; cycle 1; tea.
      now eapply reflLRTmEq.
    Unshelve. all:tea.
  Qed.

  Lemma natElimRedEqAux :
    (forall n n' (Rnn' : [Γ ||-<l> n ≅ n' : _ | RN]< wl >) (Rn : [Γ ||-<l> n : _ | RN]< wl >) (Rn' : [Γ ||-<l> n' : _ | RN]< wl >), 
      W[Γ ||-<l> tNatElim P hz hs n ≅ tNatElim Q hz' hs' n' : _ | RPpt _ Rn ]< wl >) ×
    (forall n n' (Rnn' : NatPropEq NN n n') (Rn : [Γ ||-<l> n : _ | RN]< wl >) (Rn' : [Γ ||-<l> n' : _ | RN]< wl >), 
      W[Γ ||-<l> tNatElim P hz hs n ≅ tNatElim Q hz' hs' n' : _ | RPpt _ Rn ]< wl >).
  Proof.
    apply NatRedEqInduction.
    - intros ?? nfL nfR redL redR ? prop ih RL RR ; destruct (NatPropEq_whnf prop).
      assert [Γ ||-<l> nfL : _ | RN]< wl > by (eapply redTmFwd; cycle 1; tea).
      assert [Γ ||-<l> nfR : _ | RN]< wl > by (eapply redTmFwd; cycle 1; tea).
      eapply WLREqTermHelper.
      * eapply (fst natElimRedAuxLeft).
      * eapply (fst natElimRedAuxRight).
      * eapply RPQext. 1: tea.
        now econstructor.
      * eapply WLRTmEqRedConv.
        + eapply RPext; tea. 
          eapply LRTmEqSym; eapply redwfSubstTerm; cycle 1; tea.
        + unshelve erewrite (redtmwf_det _ _ (NatRedTm.red RL) redL); tea.
          1: dependent inversion RL; subst; cbn; now eapply NatProp_whnf.
          unshelve erewrite (redtmwf_det _ _ (NatRedTm.red RR) redR); tea.
          1: dependent inversion RR; subst; cbn; now eapply NatProp_whnf.
          now eapply ih.
        Unshelve. tea.
    - intros. eapply WLREqTermHelper.
      * unshelve eapply (snd natElimRedAuxLeft); constructor.
      * unshelve eapply (snd natElimRedAuxRight); tea; constructor.
      * eapply RPQext; [unshelve eapply zeroRed| unshelve eapply zeroRedEq]; tea.
      * cbn; Wirrelevance.
    - intros ??? ih Rn Rn'. pose proof (succRedInv Rn); pose proof (succRedInv Rn').
      eapply WLREqTermHelper.
      * unshelve eapply (snd natElimRedAuxLeft); now constructor.
      * unshelve eapply (snd natElimRedAuxRight); tea; now constructor.
      * eapply RPQext; [unshelve eapply succRed| unshelve eapply succRedEq]; tea.
      * cbn.
        eapply Wsimple_appcongTerm.
        4: now eapply ih.
        + Wirrelevance0. 2: eapply WappcongTerm; tea.
          now bsimpl.
          1,2: eapply TmLogtoW ; eassumption.
          now eapply TmEqLogtoW.
        + eapply (fst natElimRedAuxLeft).
        + eapply WLRTmRedConv. 2: eapply (fst natElimRedAuxRight).
          eapply WLRTyEqSym; now eapply RPQext.
        Unshelve. 2,4,5: tea.
        1: eapply WArrRedTy; now eapply RPpt.
        rewrite subst_arr. eapply WArrRedTy.
        2: rewrite liftSubst_singleSubst_eq; cbn.
        all: now eapply RPpt.
    - intros ?? neueq ??. escape ; Wescape. inversion neueq.
      assert [Γ |- P[ne..] ≅ Q[ne'..]]< wl >. 1:{
        eapply WescapeEq. eapply RPQext; tea.
        econstructor.
        1,2: now eapply redtmwf_refl.
        2: now constructor.
        gen_typing.
      }
      eapply WneuTermEq.
      + eapply ty_natElim; tea.
      + eapply ty_conv. 
        1: eapply ty_natElim; tea.
        now symmetry.
      + eapply convneu_natElim ; tea.
      Unshelve. tea.
  Qed.

  Lemma natElimRedEq :
    (forall n n' (Rnn' : [Γ ||-<l> n ≅ n' : _ | RN]< wl >) (Rn : [Γ ||-<l> n : _ | RN]< wl >) (Rn' : [Γ ||-<l> n' : _ | RN]< wl >), 
      W[Γ ||-<l> tNatElim P hz hs n ≅ tNatElim Q hz' hs' n' : _ | RPpt _ Rn ]< wl >).
  Proof. apply natElimRedEqAux. Qed.
End NatElimRedEq.



Section NatElimValid.
  Context {wl Γ l P}
    (VΓ : [||-v Γ]< wl >)
    (VN := natValid (l:=l) VΓ)
    (VΓN := validSnoc' VΓ VN)
    (VP : [Γ ,, tNat ||-v<l> P | VΓN]< wl >).
  
  Lemma elimSuccHypTyValid :
    [Γ ||-v<l> elimSuccHypTy P | VΓ]< wl >.
  Proof.
    unfold elimSuccHypTy.
    unshelve eapply PiValid.
    1: exact VN.
    eapply simpleArrValid; tea.
    eapply substLiftS; tea.
    eapply irrelevanceTm.
    eapply succValid.
    eapply irrelevanceTm.
    change tNat with tNat⟨@wk1 Γ tNat⟩ at 2.
    eapply var0Valid.
    Unshelve. all: tea.
  Qed.

  Context {hz hs}
    (VPz := substS VP (zeroValid VΓ))
    (Vhz : [Γ ||-v<l> hz : P[tZero..] | VΓ | VPz]< wl >) 
    (Vhs : [Γ ||-v<l> hs : _ | VΓ | elimSuccHypTyValid]< wl >).

  Lemma natElimValid {n}
    (Vn : [Γ ||-v<l> n : tNat | VΓ | VN]< wl >)
    (VPn := substS VP Vn)
    : [Γ ||-v<l> tNatElim P hz hs n : _ | VΓ | VPn]< wl >.
  Proof.
    constructor; intros.
    - instValid Vσ; cbn.
      epose proof (Vuσ := liftSubstS' VN Vσ).
      unshelve eapply TreeTmSplit ; [eapply DTree_fusion ; [eapply DTree_fusion | ] ; shelve | ].
      intros wl'' Ho HA.
      pose (f':= over_tree_le Ho).
      Wirrelevance0.  1: now rewrite singleSubstComm'.
      instValid Vuσ; escape ; Wescape.
      unshelve eapply natElimRed; tea.
      + econstructor ; eapply redtywf_refl, wft_term.
        now eapply ty_nat, wfc_Ltrans.
      + intros m Rm.
        rewrite up_single_subst.
        unshelve eapply validTy.
        6: eassumption.
        * now eapply wfLCon_le_trans.
        * now eapply wfc_Ltrans.
        * unshelve econstructor ; [ | now eapply TmLogtoW].
          now bsimpl ; unshelve eapply subst_Ltrans.
      + cbn.
        set (Help := {|  NatRedTy.red := redtywf_refl (wft_term (ty_nat (wfc_Ltrans f' wfΔ))) |}).
        change [Δ ||-< l > n[σ] : tNat | LRNat_ _ Help ]< wl'' >.
        irrelevanceRefl.
        unshelve eapply RVn.
        1: eapply over_tree_fusion_r, over_tree_fusion_l ; exact Ho.
        eapply over_tree_fusion_r ; exact Ho.
      + now eapply wfc_Ltrans.
      + rewrite elimSuccHypTy_subst.
        unshelve eapply validTy ;[ .. | eapply elimSuccHypTyValid | ].
        3: unshelve eapply subst_Ltrans ; cycle 1 ; eassumption.
        now eapply wfc_Ltrans.
      + eapply RVP ; do 2 eapply (over_tree_fusion_l).
        exact Ho.
      + intros m m' Rm Rm' Rmm'; cbn.
        Wirrelevance0. 1: now rewrite up_single_subst.
        rewrite up_single_subst.
        unshelve eapply validTyExt ; cycle 2 ; tea.
        1: now eapply wfLCon_le_trans.
        1: now eapply wfc_Ltrans.
        1,2: unshelve econstructor; [bsimpl ; now unshelve eapply subst_Ltrans| cbn].
        1,2: now eapply TmLogtoW.
        unshelve econstructor; [ | cbn].
        * fsimpl; cbn; now unshelve eapply reflSubst.
        * now eapply TmEqLogtoW.
      + Wirrelevance0.
        2: eapply WTm_Ltrans ; eassumption.
        now bsimpl.
      + Wirrelevance0.
        2: eapply WTm_Ltrans ; eassumption.
        now rewrite elimSuccHypTy_subst.
        Unshelve.
        all: eassumption.
    - instAllValid Vσ Vσ' Vσσ'.
      pose (Vuσ := liftSubstS' VN Vσ).
      pose proof (Vuσ' := liftSubstS' VN Vσ').
      pose proof (Vuσrea :=  liftSubstSrealign' VN Vσσ' Vσ').
      pose proof (Vuσσ' := liftSubstSEq' VN Vσσ').
      instValid Vuσ'; instAllValid Vuσ Vuσrea Vuσσ'; escape ; Wescape.
      unshelve eapply TreeTmEqSplit ; [do 3 (eapply DTree_fusion) ; shelve | ].
      intros wl'' Ho HA.
      pose (f':= over_tree_le Ho).
      Wirrelevance0.  1: now rewrite singleSubstComm'.
      unshelve eapply natElimRedEq ; tea; fold subst_term.
      15,16: Wirrelevance0 ; [ now rewrite elimSuccHypTy_subst | unshelve eapply WTm_Ltrans ; cycle 3 ; eassumption].
      15: Wirrelevance0 ; [ now rewrite elimSuccHypTy_subst | unshelve eapply WTmEq_Ltrans ; cycle 3 ; eassumption].
      12,13: Wirrelevance0 ; [ | unshelve eapply WTm_Ltrans ; cycle 3 ; eassumption] ; now bsimpl.
      12: Wirrelevance0 ; [ | unshelve eapply WTmEq_Ltrans ; cycle 3 ; eassumption] ; now bsimpl.
      6,7: rewrite elimSuccHypTy_subst; unshelve eapply validTy ; [.. | unshelve eapply elimSuccHypTyValid | ].
      8,11: unshelve eapply subst_Ltrans ; [ .. | eassumption | | eassumption].
      4,6,7: now eapply wfc_Ltrans.
      + econstructor ; eapply redtywf_refl, wft_term.
        now eapply ty_nat, wfc_Ltrans.
      + intros m Rm.
        rewrite up_single_subst. 
        unshelve eapply validTy; cycle 4; tea.
        2: unshelve econstructor; [| now eapply TmLogtoW].
        1: unshelve eapply subst_Ltrans ; [ .. | eassumption | | eassumption].
      + cbn.
        set (Help := {| NatRedTy.red := _ |}).
        change [Δ ||-< l > n[σ] : tNat | LRNat_ _ Help ]< wl'' >.
        irrelevanceRefl.
        unshelve eapply RVn.
        1: eapply over_tree_fusion_r, over_tree_fusion_l, over_tree_fusion_r ; exact Ho.
        eapply over_tree_fusion_l, over_tree_fusion_r, over_tree_fusion_l ; exact Ho.
      + cbn. intros m Rm.
        rewrite up_single_subst. 
        unshelve eapply validTy; cycle 4; tea.
        2: unshelve econstructor; [| now eapply TmLogtoW].
        1: unshelve eapply subst_Ltrans ; [ .. | eassumption | | eassumption].
      + unshelve eapply validTy ; cycle 4; tea.
        do 3 eapply (over_tree_fusion_l) ; exact Ho.
      + unshelve eapply validTy ; cycle 4; tea.
        eapply over_tree_fusion_r  ; do 2 eapply (over_tree_fusion_l); exact Ho.
      + now eapply convty_Ltrans.
      + intros m m' Rm Rm' Rmm'; cbn.
        Wirrelevance0. 1: now rewrite up_single_subst.
        rewrite up_single_subst.
        unshelve eapply validTyExt ; cycle 3 ; tea.
        2: now eapply wfc_Ltrans.
        2,3: unshelve econstructor; [| now eapply TmLogtoW].
        2,3: unshelve eapply subst_Ltrans ; [ .. | eassumption] ; eassumption.
        unshelve econstructor; [|now eapply TmEqLogtoW].
        bsimpl.
        now unshelve eapply eqsubst_Ltrans.
      + cbn.
        set (Help := {| NatRedTy.red := _ |}).
        change [Δ ||-< l > n[σ] ≅ n[σ'] : tNat | LRNat_ _ Help ]< wl'' >.
        irrelevanceRefl.
        unshelve eapply REVn.
        1: eapply over_tree_fusion_r, over_tree_fusion_l, over_tree_fusion_r ; exact Ho.
        do 2 eapply over_tree_fusion_r ; eapply over_tree_fusion_l ; exact Ho.
      + cbn.
        set (Help := {| NatRedTy.red := _ |}).
        change [Δ ||-< l > n[σ'] : tNat | LRNat_ _ Help ]< wl'' >.
        irrelevanceRefl.
        unshelve eapply RVn0.
        1: eapply over_tree_fusion_r, over_tree_fusion_l, over_tree_fusion_r ; exact Ho.
        1: eapply over_tree_fusion_l, over_tree_fusion_l, over_tree_fusion_r ; exact Ho.
        Unshelve. all: now constructor.
Qed.    

  Lemma natElimZeroValid  : 
    [Γ ||-v<l> tNatElim P hz hs tZero ≅ hz : _ | VΓ | VPz]< wl >.
  Proof.
    constructor; intros.
    epose proof (Vuσ := liftSubstS' VN Vσ).
    instValid Vσ; instValid Vuσ; escape ; Wescape.
    unshelve eapply TreeTmEqSplit ; [eapply DTree_fusion ; [eapply DTree_fusion | ] ; shelve | ].
    intros wl'' Ho HA.
    pose (f':= over_tree_le Ho).
    Wirrelevance0.  1: now rewrite singleSubstComm'.
    unshelve eapply (snd (natElimRedAux _ _ _ _ _ _ _ _) _ NatRedTm.zeroR); tea; fold subst_term.
    2: econstructor ; eapply  (redtywf_refl (wft_term (ty_nat (wfc_Ltrans f' wfΔ)))).
    1: now eapply wfc_Ltrans.
    7: irrelevanceRefl ; eapply (WRedTm _ (validTm (zeroValid _) _ _ Vσ)).
    1: unshelve eapply (WRed _ (validTy VP _ _ Vuσ)).
    1: eapply over_tree_fusion_l, over_tree_fusion_l ; exact Ho.
    + intros m Rm.
      rewrite up_single_subst. 
      unshelve eapply validTy ; cycle 5 ; tea.
      3: now eapply wfc_Ltrans.
      unshelve econstructor; [now eapply subst_Ltrans | ].
      now eapply TmLogtoW.
    + intros m m' Rm Rm' Rmm'; cbn.
      Wirrelevance0. 1: now rewrite up_single_subst.
      rewrite up_single_subst.
      unshelve eapply validTyExt ; cycle 3.
      1: eassumption.
      3: unshelve econstructor; [now eapply subst_Ltrans | now eapply TmLogtoW].
      1: unshelve econstructor; [now eapply subst_Ltrans | now eapply TmLogtoW].
      unshelve econstructor; [eapply eqsubst_Ltrans | now eapply TmEqLogtoW].
      bsimpl; cbn; eapply reflSubst.
    + Wirrelevance0.
      2: eapply WTm_Ltrans.
      2: now eapply RVhz.
      now bsimpl.
    + rewrite elimSuccHypTy_subst. unshelve eapply validTy.
      6: eapply elimSuccHypTyValid.
      3: now eapply subst_Ltrans ; eassumption.
      now eapply wfc_Ltrans.
    + Wirrelevance0.
      now rewrite elimSuccHypTy_subst.
      eapply WTm_Ltrans.
      eauto.
      Unshelve.
      3,5-9: eassumption.
      3: now eapply over_tree_fusion_r, over_tree_fusion_l ; exact Ho.
      shelve.
    + now eapply over_tree_fusion_r ; exact Ho.
  Qed.

  Lemma natElimSuccValid {n}
    (Vn : [Γ ||-v<l> n : tNat | VΓ | VN]< wl >) 
    (VPSn := substS VP (succValid _ Vn)) : 
    [Γ ||-v<l> tNatElim P hz hs (tSucc n) ≅ tApp (tApp hs n) (tNatElim P hz hs n) : _ | VΓ | VPSn]< wl >.
  Proof.
    constructor; intros.
    epose proof (Vuσ := liftSubstS' VN Vσ).
    instValid Vσ; instValid Vuσ; escape.
    unshelve eapply TreeTmEqSplit ; [do 2 eapply DTree_fusion ; shelve | ].
    intros wl'' Ho HA.
    pose (f':= over_tree_le Ho).
    Wirrelevance0.  1: now rewrite singleSubstComm'.
    pose (Ho1 := over_tree_fusion_l (over_tree_fusion_l Ho)).
    pose (Ho2 := over_tree_fusion_r (over_tree_fusion_l Ho)).
    epose (NSn := NatRedTm.succR (WRedTm _ RVn _ Ho1 Ho2)).
    unshelve eapply (snd (natElimRedAux _ _ _ _ _ _ _ _) _ NSn); tea; fold subst_term.
    1: now eapply wfc_Ltrans.
    1: unshelve eapply (WRed _ (validTy VP _ _ Vuσ)).
    1: now eapply (over_tree_fusion_l (over_tree_fusion_r Ho)).
    + intros m Rm.
      rewrite up_single_subst. 
      unshelve eapply validTy; cycle 4 ; tea.
      1: now eapply wfc_Ltrans.
      unshelve econstructor; [now eapply subst_Ltrans| cbn].
      Wirrelevance0 ; [ reflexivity | now eapply TmLogtoW ; exact Rm].
    + intros m m' Rm Rm' Rmm'; cbn.
      Wirrelevance0. 1: now rewrite up_single_subst.
      rewrite up_single_subst.
      unshelve eapply validTyExt; cycle 3 ; tea ; cycle 1.
      1: now eapply wfc_Ltrans.
      1,2: unshelve econstructor; [now eapply subst_Ltrans| cbn].
      1,2: Wirrelevance0 ; [reflexivity | now eapply TmLogtoW].
      unshelve econstructor; [eapply eqsubst_Ltrans |].
      1: bsimpl; cbn; now eapply reflSubst.
      Wirrelevance0 ; [reflexivity | now eapply TmEqLogtoW].
    + Wirrelevance0.
      2: eapply WTm_Ltrans.
      2: now eapply RVhz.
      now bsimpl.
    + rewrite elimSuccHypTy_subst.
      unshelve eapply validTy.
      6: eapply elimSuccHypTyValid.
      3: now eapply subst_Ltrans ; eassumption.
      now eapply wfc_Ltrans.
    + Wirrelevance0.
      2: eapply WTm_Ltrans.
      2: now eapply RVhs.
       now rewrite elimSuccHypTy_subst. 
    + eapply succRed ; cbn in *.
      unshelve eapply (WRedTm _ RVn).
      now eapply over_tree_fusion_r, over_tree_fusion_r, Ho.
      Unshelve.
      all: assumption.
  Qed.

End NatElimValid.

Lemma natElimCongValid {wl Γ l P Q hz hz' hs hs' n n'}
    (VΓ : [||-v Γ]< wl >)
    (VN := natValid (l:=l) VΓ)
    (VΓN := validSnoc' VΓ VN)
    (VP : [Γ ,, tNat ||-v<l> P | VΓN]< wl >)
    (VQ : [Γ ,, tNat ||-v<l> Q | VΓN]< wl >)
    (VPQ : [Γ ,, tNat ||-v<l> P ≅ Q | VΓN | VP]< wl >)
    (VPz := substS VP (zeroValid VΓ))
    (VQz := substS VQ (zeroValid VΓ))
    (Vhz : [Γ ||-v<l> hz : P[tZero..] | VΓ | VPz]< wl >) 
    (Vhz' : [Γ ||-v<l> hz' : Q[tZero..] | VΓ | VQz]< wl >)
    (Vheqz : [Γ ||-v<l> hz ≅ hz' : P[tZero..] | VΓ | VPz]< wl >)
    (VPs := elimSuccHypTyValid VΓ VP)
    (VQs := elimSuccHypTyValid VΓ VQ)
    (Vhs : [Γ ||-v<l> hs : _ | VΓ | VPs]< wl >) 
    (Vhs' : [Γ ||-v<l> hs' : _ | VΓ | VQs]< wl >)
    (Vheqs : [Γ ||-v<l> hs ≅ hs' : _ | VΓ | VPs]< wl >) 
    (Vn : [Γ ||-v<l> n : _ | VΓ | VN]< wl >)
    (Vn' : [Γ ||-v<l> n' : _ | VΓ | VN]< wl >)
    (Veqn : [Γ ||-v<l> n ≅ n' : _ | VΓ | VN]< wl >)
    (VPn := substS VP Vn) :
    [Γ ||-v<l> tNatElim P hz hs n ≅ tNatElim Q hz' hs' n' : _ | VΓ | VPn]< wl >.
Proof.
  constructor; intros.
  pose (Vuσ := liftSubstS' VN Vσ).
  instValid Vσ; instValid Vuσ; escape ; Wescape.
  unshelve eapply TreeTmEqSplit.
  1: do 2 eapply DTree_fusion ; [eapply DTree_fusion | eapply DTree_fusion | ..] ; shelve.
  intros wl'' Ho HA.
  pose (f':= over_tree_le Ho).
  Wirrelevance0.  1: now rewrite singleSubstComm'.
  unshelve eapply natElimRedEq; tea; fold subst_term.
  1: econstructor ; eapply  (redtywf_refl (wft_term (ty_nat (wfc_Ltrans f' wfΔ)))).
  14,15: Wirrelevance0 ; [ now rewrite elimSuccHypTy_subst | now eapply WTm_Ltrans ].
  14: Wirrelevance0 ; [ now rewrite elimSuccHypTy_subst | now eapply WTmEq_Ltrans ].
  11,12: Wirrelevance0 ; [ rewrite up_single_subst | now eapply WTm_Ltrans] ; now bsimpl.
  11: Wirrelevance0 ; [rewrite up_single_subst | now eapply WTmEq_Ltrans] ; now bsimpl.
  5,6: rewrite elimSuccHypTy_subst; eapply validTy ; [ now eapply elimSuccHypTyValid | ].
  5,6: now eapply subst_Ltrans.
  + intros m Rm.
    rewrite up_single_subst. 
    unshelve eapply validTy; cycle 4; tea.
    1: now eapply wfc_Ltrans.
    now unshelve econstructor; [eapply subst_Ltrans| eapply TmLogtoW].
  + irrelevanceRefl.
    unshelve eapply RVn.
    1: eapply over_tree_fusion_l, over_tree_fusion_l, over_tree_fusion_l ; exact Ho.
    eapply over_tree_fusion_r, over_tree_fusion_l, over_tree_fusion_l; exact Ho.
  + now eapply wfc_Ltrans.
  + intros m Rm.
    rewrite up_single_subst. 
    unshelve eapply validTy; cycle 4; tea.
    1: now eapply wfc_Ltrans.
    now unshelve econstructor; [eapply subst_Ltrans| eapply TmLogtoW].
  + unshelve eapply validTy; cycle 4; tea.
    eapply over_tree_fusion_l, over_tree_fusion_r ; exact Ho.
  + unshelve eapply validTy; cycle 4; tea.
    eapply over_tree_fusion_r, over_tree_fusion_r ; exact Ho.
  + now eapply convty_Ltrans.
  + intros m m' Rm Rm' Rmm'; cbn.
    Wirrelevance0. 1: now rewrite up_single_subst.
    rewrite up_single_subst.
    eapply WtransEq; cycle 1.
    * unshelve eapply validTyEq.
      9: eassumption.
      1: now eapply wfLCon_le_trans.
      1: now eapply wfc_Ltrans.
      now unshelve econstructor; [eapply subst_Ltrans| eapply TmLogtoW].
    * unshelve eapply validTyExt; cycle 3 ; tea.
      1: now eapply wfLCon_le_trans.
      1: now eapply wfc_Ltrans.
      1,2: now unshelve econstructor; [eapply subst_Ltrans| eapply TmLogtoW].
      unshelve econstructor; [eapply eqsubst_Ltrans| now eapply TmEqLogtoW].
      bsimpl. eapply reflSubst.
  + irrelevance0 ; [ | eapply (WRedTmEq _ RVeqn)].
    reflexivity.
    eapply over_tree_fusion_l, over_tree_fusion_r, over_tree_fusion_l ; exact Ho.
  + irrelevance0 ; [ | eapply (WRedTm _ RVn')].
    reflexivity.
    eapply over_tree_fusion_r, over_tree_fusion_r, over_tree_fusion_l ; exact Ho.
    Unshelve.
    all: tea.
    all: now eapply wfc_Ltrans.
Qed.

Lemma elimSuccHypTyCongValid {wl Γ l P P'}
    (VΓ : [||-v Γ]< wl >)
    (VN := natValid (l:=l) VΓ)
    (VΓN := validSnoc' VΓ VN)
    (VP : [Γ ,, tNat ||-v<l> P | VΓN]< wl >)
    (VP' : [Γ ,, tNat ||-v<l> P' | VΓN]< wl >)
    (VeqP : [Γ ,, tNat ||-v<l> P ≅ P' | VΓN | VP]< wl >) :
    [Γ ||-v<l> elimSuccHypTy P ≅ elimSuccHypTy P' | VΓ | elimSuccHypTyValid VΓ VP]< wl >.
  Proof.
    unfold elimSuccHypTy.
    eapply irrelevanceTyEq.
    assert [Γ,, tNat ||-v< l > P'[tSucc (tRel 0)]⇑ | validSnoc' VΓ VN]< wl >. 1:{
      eapply substLiftS; tea.
      eapply irrelevanceTm.
      eapply succValid.
      eapply irrelevanceTm.
      change tNat with tNat⟨@wk1 Γ tNat⟩ at 2.
      eapply var0Valid.
    }
    eapply PiCong.
    - eapply simpleArrValid; tea.
    - eapply reflValidTy.
    - eapply simpleArrCongValid; tea.
      eapply substLiftSEq; tea.
    Unshelve. all: tea.
    unshelve eapply irrelevanceTm; tea.
    2: eapply succValid.
    unshelve eapply irrelevanceTm'; cycle -1.
    1: unshelve eapply var0Valid.
    1,2 : tea.
    now bsimpl.
  Qed.

End Nat.
