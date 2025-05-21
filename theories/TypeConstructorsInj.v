(** * LogRel.TypeConstructorsInj: injectivity and no-confusion of type constructors, and many consequences, including subject reduction. *)
From Coq Require Import CRelationClasses.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations LContexts Context NormalForms Weakening UntypedReduction
  GenericTyping DeclarativeTyping DeclarativeInstance.
From LogRel Require Import Monad LogicalRelation Validity Fundamental DeclarativeSubst.
From LogRel.LogicalRelation Require Import Escape Irrelevance Neutral Induction NormalRed Split.
From LogRel.Substitution Require Import Escape Monotonicity Poly.
From LogRel.Substitution.Introductions Require Import Pi Sigma.
                                       
Set Printing Primitive Projection Parameters.

Import DeclarativeTypingProperties.

Section TypeConstructors.

  Definition type_hd_view (wl : wfLCon) (Γ : context) {T T' : term} (nfT : isType T) (nfT' : isType T') : Type :=
    match nfT, nfT' with
      | @UnivType s, @UnivType s' => s = s'
      | @ProdType A B, @ProdType A' B' => [Γ |- A' ≅ A]< wl > × [Γ,, A' |- B ≅ B']< wl >
      | BoolType, BoolType => True
      | NatType, NatType => True
      | EmptyType, EmptyType => True
      | NeType _, NeType _ => [Γ |- T ≅ T' : U]< wl >
      | @SigType A B, @SigType A' B' => [Γ |- A' ≅ A]< wl > × [Γ,, A' |- B ≅ B']< wl >
      | @IdType A x y, @IdType A' x' y' => [× [Γ |- A' ≅ A]< wl >, [Γ |- x ≅ x' : A]< wl > & [Γ |- y ≅ y' : A]< wl >]
      | _, _ => False
    end.

  Lemma type_hd_view_over_tree (wl : wfLCon) (Γ : context) {T T' : term} (nfT : isType T) (nfT' : isType T') (d : DTree wl) :
    (forall wl', over_tree wl wl' d -> type_hd_view wl' Γ nfT nfT') ->
    type_hd_view wl Γ nfT nfT'.
  Proof.
    eapply split_to_over_tree.
    clear wl d ; intros wl n ne.
    destruct nfT, nfT' ; cbn ; eauto.
    - intros [HAt HBt] [HAf HBf] ; split.
      + now eapply ϝTypeConv. 
      + now eapply ϝTypeConv. 
    - intros [HAt HBt] [HAf HBf] ; split.
      + now eapply ϝTypeConv. 
      + now eapply ϝTypeConv.
    - intros [HAt HBt] [HAf HBf] ; split.
      + now eapply ϝTypeConv. 
      + now eapply ϝTermConv. 
      + now eapply ϝTermConv.
    - intros HAt HAf.
      now eapply ϝTermConv. 
  Qed.                

  Lemma ty_conv_inj : forall (wl : wfLCon) (Γ : context) (T T' : term) (nfT : isType T) (nfT' : isType T'),
    [Γ |- T ≅ T']< wl > ->
    type_hd_view wl Γ nfT nfT'.
  Proof.
    intros * Hconv.
    eapply Fundamental in Hconv as [HΓ HT HT' Hconv].
    eapply reducibleTyEq in Hconv.
    set (HTred := reducibleTy _ HT) in *.
    clearbody HTred.
    clear HT.
    eapply reducibleTy in HT'.
    unshelve eapply type_hd_view_over_tree.
    1: eapply DTree_fusion ; [eapply DTree_fusion | ] ; shelve.
    intros wl' Ho.
    pose proof (HTRed := WRed _ HTred _ (over_tree_fusion_l (over_tree_fusion_l Ho))).
    assert (HConv : [HTRed | Γ ||- T ≅ T' ]< wl' >).
    { irrelevanceRefl ; unshelve eapply Hconv.
      1: now eapply (over_tree_fusion_l (over_tree_fusion_l Ho)).
      now eapply (over_tree_fusion_r Ho).
    }
    assert (HΓ' : [||-v Γ ]< wl' >).
    { eapply WfC_Ltrans ; eauto.
      now eapply over_tree_le.
    }
    clear HΓ.
    pose proof (HTRed' := WRed _ HT' _ (over_tree_fusion_r (over_tree_fusion_l Ho))).
    clear HTred HT' Hconv Ho.
    revert nfT T' nfT' HΓ' HTRed' HConv. 
    revert HTRed. 
    generalize (eq_refl : one = one).
    generalize one at 1 3 ; intros l eql HTred; revert eql.
    pattern l, wl', Γ, T, HTred ; apply LR_rect_TyUr ; clear l wl wl' Γ T HTred.
    all: intros ? wl Γ T.
    - intros [] -> nfT T' nfT' HΓ HT' [].
      assert (T' = U) as HeqT' by (eapply redtywf_whnf ; gen_typing); subst.
      assert (T = U) as HeqU by (eapply redtywf_whnf ; gen_typing). 
      destruct nfT ; inversion HeqU ; subst.
      2: now exfalso ; gen_typing.
      clear HeqU.
      Set Printing All.
      remember U as T eqn:HeqU in nfT' |- * at 2.
      destruct nfT'; inversion HeqU ; subst.
      2: now exfalso ; gen_typing.
      now reflexivity.
    - Unset Printing All.
      intros [nT ? ne] -> nfT T' nfT' HΓ HT' [nT' ? ne']; cbn in *.
      assert (T = nT) as <- by
        (apply (red_whnf (l := wl)) ; gen_typing).
      assert (T' = nT') as <- by
        (apply (red_whnf (l:= wl)) ; gen_typing).
      destruct nfT.
      1-7: apply convneu_whne in ne; inversion ne.
      destruct nfT'.
      1-7: symmetry in ne'; apply convneu_whne in ne'; inversion ne'.
      cbn. all: cbn ; try now gen_typing.
    - intros [dom cod red] _ _ -> nfT T' nfT' HΓ HT'[dom' cod' red']; cbn in *.
      assert (T = tProd dom cod) as HeqT by (apply (red_whnf (l := wl)) ; gen_typing). 
      assert (T' = tProd dom' cod') as HeqT' by (apply (red_whnf (l := wl)) ; gen_typing).
      destruct nfT; cycle -1.
      1: subst ; exfalso ; gen_typing.
      all: try congruence.
      destruct nfT'; cycle -1.
      1: subst ; exfalso ; gen_typing.
      all: try congruence.
      inversion HeqT ; inversion HeqT' ; subst ; clear HeqT HeqT'; cbn.
      destruct (polyRedEqId (normRedΠ0 (invLRΠ HT')) (PolyRedEqSym _ polyRed0)).
      split; now Wescape.
    - intros [] -> nfT T' nfT' HΓ HT' [].
      assert (T' = tNat) as HeqT' by (eapply (redtywf_whnf (l:= wl)) ; gen_typing).
      assert (T = tNat) as HeqT by (eapply (redtywf_whnf (l:= wl)) ; gen_typing).
      destruct nfT; inversion HeqT.
      + destruct nfT'; inversion HeqT'.
        * constructor.
        * exfalso; subst; inversion w.
      + exfalso; subst; inversion w.
    - intros [] -> nfT T' nfT' HΓ HT' [].
      assert (T' = tBool) as HeqT' by (eapply (redtywf_whnf (l:= wl)) ; gen_typing).
      assert (T = tBool) as HeqT by (eapply (redtywf_whnf (l:= wl)) ; gen_typing).
      destruct nfT; inversion HeqT.
      + destruct nfT'; inversion HeqT'.
        * constructor.
        * exfalso; subst; inversion w.
      + exfalso; subst; inversion w.
    - intros [] -> nfT T' nfT' HΓ HT' [].
      assert (T' = tEmpty) as HeqT' by (eapply (redtywf_whnf (l:= wl)) ; gen_typing).
      assert (T = tEmpty) as HeqT by (eapply (redtywf_whnf (l:= wl)) ; gen_typing).
      destruct nfT; inversion HeqT.
      + destruct nfT'; inversion HeqT'.
        * econstructor.
        * exfalso; subst; inversion w.
      + exfalso; subst; inversion w.
    - intros [dom cod red] _ _ -> nfT T' nfT' HΓ HT' [dom' cod' red'].
      assert (T = tSig dom cod) as HeqT by (apply (red_whnf (l:= wl)) ; gen_typing). 
      assert (T' = tSig dom' cod') as HeqT' by (apply (red_whnf (l:= wl)) ; gen_typing).
      destruct nfT; cycle -1.
      1: subst; inv_whne.
      all: try congruence.
      destruct nfT'; cycle -1.
      1: subst; inv_whne.
      all: try congruence.
      inversion HeqT ; inversion HeqT' ; subst ; clear HeqT HeqT'; cbn.
      destruct (polyRedEqId (normRedΣ0 (invLRΣ HT')) (PolyRedEqSym _ polyRed0)).
      split; now Wescape.
    - intros [??? ty] _ _ -> nfT T' nfT' HΓ HT' [??? ty']; cbn in *.
      assert (T = ty) as HeqT by (apply (red_whnf (l:= wl)); gen_typing).
      assert (T' = ty') as HeqT' by (apply (red_whnf (l:= wl)); gen_typing).
      destruct nfT; cycle -1; [subst; inv_whne|..]; unfold ty in *; try congruence.
      destruct nfT'; cycle -1; [subst; inv_whne|..]; unfold ty' in *; try congruence.
      cbn; inversion HeqT; inversion HeqT'; subst; escape; now split.
  Qed.

(*
    
  Lemma red_ty_complete : forall (wl : wfLCon) (Γ : context) (T T' : term),
    isType T ->
    [Γ |- T ≅ T']< wl > ->
    ∑ d T'', isType T'' × (forall wl', over_tree wl wl' d -> [Γ |- T' ⤳* T'']< wl' >).
 Proof.
   intros * tyT Hconv.
   eapply Fundamental in Hconv as [HΓ HT HT' Hconv].
   eapply reducibleTyEq in Hconv.
   set (HTred := reducibleTy _ HT) in *.
   clearbody HTred.
   clear HT.
   assert (Hyp : forall d : DTree wl,
              Ssig (fun wl' : wfLCon => over_tree wl wl' d)).
   { clear.
     induction d.
     - exists k.
       now eapply wfLCon_le_id.
     - cbn.
       clear IHd2 ; destruct IHd1 as [wl' Hyp].
       exists wl'.
       pose (H := over_tree_le Hyp _ _ (in_here_l _)).
       now rewrite (decidInLCon_true H).
   }
   pose (d := DTree_fusion _ (WT _ HTred) (WTEq _ Hconv)).
   specialize (Hyp d) ; destruct Hyp as [wl' Hwl'].

   
    exists (DTree_fusion _ (WT _ HTred) (WTEq _ Hconv)).
    destruct HTred as [d HTred].
    destruct HTred as [[] lr] ; cbn in *.
    destruct lr.
    all: destruct Hconv; eexists; split; [lazymatch goal with H : [_ |- _ :⤳*: _] |- _ => apply H end|]; constructor.
    eapply convneu_whne; now symmetry.
  Qed.


  Corollary red_ty_compl_univ_l Γ T :
    [Γ |- U ≅ T]< wl > ->
    [Γ |- T ⤳* U]< wl >.
  Proof.
    intros HT.
    pose proof HT as HT'.
    unshelve eapply red_ty_complete in HT' as (T''&[? nfT]).
    2: econstructor.
    enough (T'' = U) as -> by easy.
    assert [Γ |- U ≅ T'']< wl > as Hconv by
      (etransitivity ; [eassumption|now eapply RedConvTyC]).
    unshelve eapply ty_conv_inj in Hconv.
    1: econstructor.
    1: eassumption.
    now destruct nfT, Hconv.
  Qed.

  Corollary red_ty_compl_univ_r Γ T :
    [Γ |- T ≅ U]< wl > ->
    [Γ |- T ⤳* U]< wl >.
  Proof.
    intros.
    eapply red_ty_compl_univ_l.
    now symmetry.
  Qed.

  Corollary red_ty_compl_nat_l Γ T :
    [Γ |- tNat ≅ T]< wl > ->
    [Γ |- T ⤳* tNat]< wl >.
  Proof.
    intros HT.
    pose proof HT as HT'.
    unshelve eapply red_ty_complete in HT' as (T''&[? nfT]).
    2: econstructor.
    enough (T'' = tNat) as -> by easy.
    assert [Γ |- tNat ≅ T'']< wl > as Hconv by
      (etransitivity ; [eassumption|now eapply RedConvTyC]).
    unshelve eapply ty_conv_inj in Hconv.
    1: econstructor.
    1: eassumption.
    now destruct nfT, Hconv.
  Qed.

  Corollary red_ty_compl_nat_r Γ T :
    [Γ |- T ≅ tNat]< wl > ->
    [Γ |- T ⤳* tNat]< wl >.
  Proof.
    intros.
    eapply red_ty_compl_nat_l.
    now symmetry.
  Qed.

  Corollary red_ty_compl_empty_l Γ T :
    [Γ |- tEmpty ≅ T]< wl > ->
    [Γ |- T ⤳* tEmpty]< wl >.
  Proof.
    intros HT.
    pose proof HT as HT'.
    unshelve eapply red_ty_complete in HT' as (T''&[? nfT]).
    2: econstructor.
    enough (T'' = tEmpty) as -> by easy.
    assert [Γ |- tEmpty ≅ T'']< wl > as Hconv by
      (etransitivity ; [eassumption|now eapply RedConvTyC]).
    unshelve eapply ty_conv_inj in Hconv.
    1: econstructor.
    1: eassumption.
    now destruct nfT, Hconv.
  Qed.

  Corollary red_ty_compl_empty_r Γ T :
    [Γ |- T ≅ tEmpty]< wl > ->
    [Γ |- T ⤳* tEmpty]< wl >.
  Proof.
    intros.
    eapply red_ty_compl_empty_l.
    now symmetry.
  Qed.

  Corollary red_ty_compl_prod_l Γ A B T :
    [Γ |- tProd A B ≅ T]< wl > ->
    ∑ A' B', [× [Γ |- T ⤳* tProd A' B']< wl >, [Γ |- A' ≅ A]< wl > & [Γ,, A' |- B ≅ B']< wl >].
  Proof.
    intros HT.
    pose proof HT as HT'.
    unshelve eapply red_ty_complete in HT as (T''&[? nfT]).
    2: econstructor.
    assert [Γ |- tProd A B ≅ T'']< wl > as Hconv by 
      (etransitivity ; [eassumption|now eapply RedConvTyC]).
    unshelve eapply ty_conv_inj in Hconv.
    1: constructor.
    1: assumption.
    destruct nfT, Hconv.
    do 2 eexists ; split.
    all: eassumption.
  Qed.

  Corollary prod_ty_inj Γ A B  A' B' :
    [Γ |- tProd A B ≅ tProd A' B']< wl > ->
    [Γ |- A' ≅ A]< wl > × [Γ,, A' |- B ≅ B']< wl >.
  Proof.
    intros Hty.
    unshelve eapply ty_conv_inj in Hty.
    1-2: constructor.
    now eassumption.
  Qed.

  Corollary red_ty_compl_sig_l Γ A B T :
    [Γ |- tSig A B ≅ T]< wl > ->
    ∑ A' B', [× [Γ |- T ⤳* tSig A' B']< wl >, [Γ |- A' ≅ A]< wl > & [Γ,, A' |- B ≅ B']< wl >].
  Proof.
    intros HT.
    pose proof HT as HT'.
    unshelve eapply red_ty_complete in HT as (T''&[? nfT]).
    2: econstructor.
    assert [Γ |- tSig A B ≅ T'']< wl > as Hconv by 
      (etransitivity ; [eassumption|now eapply RedConvTyC]).
    unshelve eapply ty_conv_inj in Hconv.
    1: constructor.
    1: assumption.
    destruct nfT, Hconv.
    do 2 eexists ; split.
    all: eassumption.
  Qed.
  
  Corollary red_ty_compl_sig_r Γ A B T :
    [Γ |- T ≅ tSig A B]< wl > ->
    ∑ A' B', [× [Γ |- T ⤳* tSig A' B']< wl >, [Γ |- A' ≅ A]< wl > & [Γ,, A' |- B ≅ B']< wl >].
  Proof.
    intros; eapply red_ty_compl_sig_l; now symmetry.
  Qed.

  Corollary sig_ty_inj Γ A B  A' B' :
    [Γ |- tSig A B ≅ tSig A' B']< wl > ->
    [Γ |- A' ≅ A]< wl > × [Γ,, A' |- B ≅ B']< wl >.
  Proof.
    intros Hty.
    unshelve eapply ty_conv_inj in Hty.
    1-2: constructor.
    now eassumption.
  Qed.

  Corollary red_ty_compl_id_l Γ A x y T :
    [Γ |- tId A x y ≅ T]< wl > ->
    ∑ A' x' y', [× [Γ |- T ⤳* tId A' x' y']< wl >, [Γ |- A' ≅ A]< wl >, [Γ |- x ≅ x' : A]< wl > & [Γ |- y ≅ y' : A]< wl >].
  Proof.
    intros HT.
    pose proof HT as HT'.
    unshelve eapply red_ty_complete in HT as (T''&[? nfT]).
    2: econstructor.
    assert [Γ |- tId A x y ≅ T'']< wl > as Hconv by 
      (etransitivity ; [eassumption|now eapply RedConvTyC]).
    unshelve eapply ty_conv_inj in Hconv.
    1: constructor.
    1: assumption.
    destruct nfT, Hconv.
    do 3 eexists ; split; eassumption.
  Qed.
  
  Corollary red_ty_compl_id_r Γ A x y T :
    [Γ |- T ≅ tId A x y]< wl > ->
    ∑ A' x' y', [× [Γ |- T ⤳* tId A' x' y']< wl >, [Γ |- A' ≅ A]< wl >, [Γ |- x ≅ x' : A]< wl > & [Γ |- y ≅ y' : A]< wl >].
  Proof.
    intros; eapply red_ty_compl_id_l; now symmetry.
  Qed.

  Corollary id_ty_inj {Γ A A' x x' y y'} :
    [Γ |- tId A x y ≅ tId A' x' y']< wl > ->
    [× [Γ |- A' ≅ A]< wl >, [Γ |- x ≅ x' : A]< wl > & [Γ |- y ≅ y' : A]< wl >].
  Proof.
    intros Hty.
    unshelve eapply ty_conv_inj in Hty.
    1-2: constructor.
    now eassumption.
  Qed.
*)
End TypeConstructors.

Section Boundary.

  Lemma in_ctx_wf wl Γ n decl :
    [|- Γ]< wl > ->
    in_ctx Γ n decl ->
    [Γ |- decl]< wl >.
  Proof.
    intros HΓ Hin.
    induction Hin.
    - inversion HΓ ; subst ; cbn in * ; refold.
      renToWk.
      now apply typing_wk.
    - inversion HΓ ; subst ; cbn in * ; refold.
      renToWk.
      now eapply typing_wk.
  Qed.

  Lemma scons2_well_subst {wl Γ A B} : 
    (forall a b, [Γ |- a : A]< wl > -> [Γ |- b : B[a..]]< wl > -> [Γ |-s (b .: a ..) : (Γ ,, A),, B]< wl >)
    × (forall a a' b b', [Γ |- a ≅ a' : A]< wl > -> [Γ |- b ≅ b' : B[a..]]< wl > -> [Γ |-s (b .: a..) ≅ (b' .: a'..) : (Γ ,, A),, B]< wl >).
  Proof.
    assert (h : forall (a : term) σ, ↑ >> (a .: σ) =1 σ) by reflexivity.
    assert (h' : forall a σ t, t[↑ >> (a .: σ)] = t[σ]) by (intros; now setoid_rewrite h).
    split; intros; econstructor.
    - asimpl; econstructor.
      2: cbn; rewrite h'; now asimpl.
      asimpl; eapply id_subst; gen_typing.
    - cbn; now rewrite h'.
    - asimpl; econstructor.
      2: cbn; rewrite h'; now asimpl.
      asimpl; eapply subst_refl; eapply id_subst; gen_typing.
    - cbn; now rewrite h'.
  Qed.

  Lemma typing_subst2 {wl Γ A B} :
    [|- Γ]< wl > ->
    (forall P a b, [Γ |- a : A]< wl > -> [Γ |- b : B[a..]]< wl > -> [Γ,, A,, B |- P]< wl > -> [Γ |- P[b .: a ..]]< wl >)
    × (forall P P' a a' b b', [Γ |- a ≅ a' : A]< wl > -> [Γ |- b ≅ b' : B[a..]]< wl > -> [Γ,, A ,, B |- P ≅ P']< wl > -> [Γ |- P[b .: a..] ≅ P'[b' .: a'..]]< wl >).
  Proof.
    intros;split; intros; eapply typing_subst; tea; now eapply scons2_well_subst.
  Qed.

  Lemma shift_subst_eq t a : t⟨↑⟩[a..] = t.
  Proof. now asimpl. Qed.

  Lemma idElimMotiveCtx {wl Γ A x} : 
    [Γ |- A]< wl > ->
    [Γ |- x : A]< wl > ->
    [|- (Γ,, A),, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)]< wl >.
  Proof.
    intros; assert [|- Γ]< wl > by boundary.
    assert [|- Γ,, A]< wl > by now econstructor.
    econstructor; tea.
    econstructor.
    1: now eapply wft_wk. 
    1:  eapply ty_wk; tea; econstructor; tea.
    rewrite wk1_ren_on; now eapply ty_var0.
  Qed.

  Lemma idElimMotiveCtxConv {wl Γ Γ' A A' x x'} :
    [|- Γ ≅ Γ']< wl > ->
    [Γ |- A ≅ A']< wl > ->
    [Γ |- x ≅ x' : A]< wl > ->
    [ |- (Γ,, A),, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)]< wl > ->
    [ |- (Γ',, A'),, tId A'⟨@wk1 Γ' A'⟩ x'⟨@wk1 Γ' A'⟩ (tRel 0)]< wl > ->
    [ |- (Γ',, A'),, tId A'⟨@wk1 Γ' A'⟩ x'⟨@wk1 Γ' A'⟩ (tRel 0) ≅ (Γ,, A),, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)]< wl >.
  Proof.
    intros.
    assert [|- Γ]< wl > by boundary.
    assert [Γ |- A]< wl > by boundary.
    eapply convCtxSym0; tea.
    econstructor.
    1: econstructor; tea; now eapply ctx_refl.
    erewrite (wk1_irr (t:=A')), (wk1_irr (t:=x')); econstructor.
    1,2: eapply typing_wk; tea; gen_typing.
    rewrite wk1_ren_on; eapply TermRefl; now eapply ty_var0.
  Qed.

  Let PCon (wl : wfLCon) (Γ : context) := True.
  Let PTy (wl : wfLCon) (Γ : context) (A : term) := True.
  Let PTm (wl : wfLCon) (Γ : context) (A t : term) := [Γ |- A]< wl >.
  Let PTyEq (wl : wfLCon) (Γ : context) (A B : term) := [Γ |- A]< wl > × [Γ |- B]< wl >.
  Let PTmEq (wl : wfLCon) (Γ : context) (A t u : term) := [× [Γ |- A]< wl >, [Γ |- t : A]< wl > & [Γ |- u : A]< wl >].

  Lemma boundary (wl : wfLCon) : WfDeclInductionConcl PCon PTy PTm PTyEq PTmEq wl.
  Proof.
    subst PCon PTy PTm PTyEq PTmEq.
    red; prod_splitter; try now constructor.
    - intros Γ A t H; apply Fundamental in H as [? VA _].
      now eapply escapeTy.
    - intros Γ A B H; apply Fundamental in H as [? VA VB _]; split.
      + now eapply escapeTy.
      + now eapply escapeTy.
    - intros Γ A t u H; apply Fundamental in H as [? VA Vt Vu]; prod_splitter.
      + now eapply escapeTy.
      + now eapply escapeTm.
      + now eapply escapeTm.
  Qed.

End Boundary.

Corollary boundary_tm wl Γ A t : [Γ |- t : A]< wl > -> [Γ |- A]< wl >.
Proof.
  now intros ?%boundary.
Qed.

Corollary boundary_ty_conv_l wl Γ A B : [Γ |- A ≅ B]< wl > -> [Γ |- A]< wl >.
Proof.
  now intros ?%boundary.
Qed.

Corollary boundary_ty_conv_r wl Γ A B : [Γ |- A ≅ B]< wl > -> [Γ |- B]< wl >.
Proof.
  now intros ?%boundary.
Qed.

Corollary boundary_red_ty_r wl Γ A B : [Γ |- A ⤳* B]< wl > -> [Γ |- B]< wl >.
Proof.
  now intros ?%RedConvTyC%boundary.
Qed.

Corollary boundary_tm_conv_l wl Γ A t u : [Γ |- t ≅ u : A]< wl > -> [Γ |- t : A]< wl >.
Proof.
  now intros []%boundary.
Qed.

Corollary boundary_tm_conv_r wl Γ A t u : [Γ |- t ≅ u : A]< wl > -> [Γ |- u : A]< wl >.
Proof.
  now intros []%boundary.
Qed.

Corollary boundary_tm_conv_ty wl Γ A t u : [Γ |- t ≅ u : A]< wl > -> [Γ |- A]< wl >.
Proof.
  now intros []%boundary.
Qed.

Corollary boundary_red_tm_r wl Γ A t u : [Γ |- t ⤳* u : A]< wl > -> [Γ |- u : A]< wl >.
Proof.
  now intros []%RedConvTeC%boundary.
Qed.

Corollary boundary_red_tm_ty wl Γ A t u : [Γ |- t ⤳* u : A]< wl > -> [Γ |- A]< wl >.
Proof.
  now intros []%RedConvTeC%boundary.
Qed.

#[export] Hint Resolve
  boundary_tm boundary_ty_conv_l boundary_ty_conv_r
  boundary_tm_conv_l boundary_tm_conv_r boundary_tm_conv_ty
  boundary_red_tm_l boundary_red_tm_r boundary_red_tm_ty
  boundary_red_ty_r : boundary.

Lemma boundary_ctx_conv_l wl (Γ Δ : context) :
  [ |- Γ ≅ Δ]< wl > ->
  [|- Γ]< wl >.
Proof.
  destruct 1.
  all: econstructor ; boundary.
Qed.

#[export] Hint Resolve boundary_ctx_conv_l : boundary.

Corollary conv_ctx_refl_l wl (Γ Δ : context) :
[ |- Γ ≅ Δ]< wl > ->
[|- Γ ≅ Γ]< wl >.
Proof.
  intros.
  eapply ctx_refl ; boundary.
Qed.
(*
Corollary red_ty_compl_prod_r wl Γ A B T :
  [Γ |- T ≅ tProd A B]< wl > ->
  ∑ A' B', [× [Γ |- T ⤳* tProd A' B']< wl >, [Γ |- A ≅ A']< wl > & [Γ,, A |- B' ≅ B]]< wl >.
Proof.
  intros HT.
  symmetry in HT.
  eapply red_ty_compl_prod_l in HT as (?&?&[HA ? HB]).
  do 2 eexists ; split ; tea.
  1: now symmetry.
  symmetry.
  eapply stability1 ; tea.
  1-2: now boundary.
  now symmetry.
Qed.
*)
Section Stability.

  Lemma conv_well_subst (wl : wfLCon) (Γ Δ : context) :
    [ |- Γ ≅ Δ]< wl > ->
    [Γ |-s tRel : Δ]< wl >.
  Proof.
    intros; eapply conv_well_subst; tea; boundary.
  Qed.

  Let PCon (wl : wfLCon) (Γ : context) := True.
  Let PTy (wl : wfLCon) (Γ : context) (A : term) := forall Δ,
    [|- Δ ≅ Γ]< wl > -> [Δ |- A]< wl >.
  Let PTm (wl : wfLCon) (Γ : context) (A t : term) := forall Δ,
    [|- Δ ≅ Γ]< wl > -> [Δ |- t : A]< wl >.
  Let PTyEq (wl : wfLCon) (Γ : context) (A B : term) := forall Δ,
    [|- Δ ≅ Γ]< wl > -> [Δ |- A ≅ B]< wl >.
  Let PTmEq (wl : wfLCon) (Γ : context) (A t u : term) := forall Δ,
    [|- Δ ≅ Γ]< wl > -> [Δ |- t ≅ u : A]< wl >.

  Theorem stability wl : WfDeclInductionConcl PCon PTy PTm PTyEq PTmEq wl.
  Proof.
    red; prod_splitter; intros; red;intros; eapply stability0; tea; boundary.
  Qed.


  #[global] Instance ConvCtxSym (wl : wfLCon) : Symmetric (ConvCtx wl).
  Proof.
    intros Γ Δ.
    induction 1.
    all: constructor ; tea.
    eapply stability ; tea.
    now symmetry.
  Qed.

  Corollary conv_ctx_refl_r (wl : wfLCon) (Γ Δ : context) :
    [ |- Γ ≅ Δ]< wl > ->
    [|- Δ ≅ Δ]< wl >.
  Proof.
    intros H.
    symmetry in H.
    now eapply ctx_refl ; boundary.
  Qed.

  #[global] Instance ConvCtxTrans (wl : wfLCon) : Transitive (ConvCtx wl).
  Proof.
    intros Γ1 Γ2 Γ3 H1 H2.
    induction H1 in Γ3, H2 |- *.
    all: inversion H2 ; subst ; clear H2.
    all: constructor.
    1: eauto.
    etransitivity ; tea.
    now eapply stability.
  Qed.

End Stability.

(** ** Generation *)

(** The generation lemma (the name comes from the PTS literature), gives a 
stronger inversion principle on typing derivations, that give direct access
to the last non-conversion rule, and bundle together all conversions.

Note that because we do not yet know that [Γ |- t : T] implies [Γ |- T],
we cannot use reflexivity in the case where the last rule was not a conversion
one, and we get the slightly clumsy disjunction of either an equality or a
conversion proof. We get a better version of generation later on, once we have
this implication. *)

Inductive termGenData (wl : wfLCon) (Γ : context) : term -> term -> Type :=
    | termGentRel n decl : [|- Γ]< wl > -> in_ctx Γ n decl -> termGenData wl Γ (tRel n) decl
    | termGentProd A B : [Γ |- A : U]< wl > -> [Γ,, A |- B : U]< wl > -> termGenData wl Γ (tProd A B) U
    | termGentLambda A t B : [Γ |- A]< wl > -> [Γ,, A |- t : B]< wl > -> termGenData wl Γ (tLambda A t) (tProd A B)
    | termGentApp f a A B : [Γ |- f : tProd A B]< wl > -> [Γ |- a : A]< wl > -> termGenData wl Γ (tApp f a) B[a..]
(*    | termGentSort k A : False -> termGenData wl Γ (tSort k) A*) 
    | termGentNat : termGenData wl Γ tNat U
    | termGentZero : termGenData wl Γ tZero tNat
    | termGentSucc n : [Γ |- n : tNat]< wl > -> termGenData wl Γ (tSucc n) tNat
    | termGentNatElim P hz hs n :
      [Γ,, tNat |- P]< wl > -> [Γ |- hz : P[tZero..]]< wl > -> [Γ |- hs : elimSuccHypTy P]< wl > ->
      [Γ |- n : tNat]< wl > -> termGenData wl Γ (tNatElim P hz hs n) P[n..]
    | termGentBool : termGenData wl Γ tBool U
    | termGentTrue : termGenData wl Γ tTrue tBool
    | termGentFalse : termGenData wl Γ tFalse tBool
    | termGentBoolElim P ht hf n :
      [Γ,, tBool |- P]< wl > -> [Γ |- ht : P[tTrue..]]< wl > -> [Γ |- hf : P[tFalse..]]< wl > ->
      [Γ |- n : tBool]< wl > -> termGenData wl Γ (tBoolElim P ht hf n) P[n..]
    | termGentAlpha n : [Γ |- n : tNat]< wl > -> termGenData wl Γ (tAlpha n) tBool
    | termGentEmpty : termGenData wl Γ tEmpty U
    | termGentEmptyElim P e :
      [Γ,, tEmpty |- P]< wl > -> [Γ |- e : tEmpty]< wl > -> termGenData wl Γ (tEmptyElim P e) P[e..]
    | termGentSig A B : [Γ |- A : U]< wl > -> [Γ ,, A |- B : U]< wl > -> termGenData wl Γ (tSig A B) U
    | termGentPair A B a b :
      [Γ |- A]< wl > -> [Γ,, A |- B]< wl > -> [Γ |- a : A]< wl > ->
      [Γ |- b : B[a..]]< wl > -> termGenData wl Γ (tPair A B a b) (tSig A B)
    | termGentFst p A B : [Γ |- p : tSig A B]< wl > -> termGenData wl Γ (tFst p) A
    | termGentSnd p A B : [Γ |- p : tSig A B]< wl > -> termGenData wl Γ (tSnd p) B[(tFst p)..]
    | termGentId A x y : [Γ |- A : U]< wl > -> [Γ |- x : A]< wl > -> [Γ |- y : A]< wl > -> termGenData wl Γ (tId A x y) U
    | termGentRefl A x : [Γ |- A]< wl > -> [Γ |- x : A]< wl > -> termGenData wl Γ (tRefl A x) (tId A x x)
    | termGentIdElim A x P hr y e : 
      [Γ |- A]< wl > -> [Γ |- x : A]< wl > -> [Γ,, A,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) |- P]< wl > ->
      [Γ |- hr : P[tRefl A x .: x..]]< wl > -> [Γ |- y : A]< wl > -> [Γ |- e : tId A x y]< wl > ->
      termGenData wl Γ (tIdElim A x P hr y e) P[e .: y..]
    | ϝtermGen {t A At Af} {n} {ne : not_in_LCon (pi1 wl) n} :
      [Γ |- At ≅ A]< wl ,,l (ne, true) > ->
      termGenData (wl ,,l (ne, true)) Γ t At ->
      [Γ |- Af ≅ A]< wl ,,l (ne, false) > ->
      termGenData (wl ,,l (ne, false)) Γ t Af ->
      termGenData wl Γ t A.
 



(*
Definition termGenData (wl : wfLCon) (Γ : context) (t T : term) : Type :=
  match t with
    | tRel n => ∑ decl, [× T = decl, [|- Γ]< wl >& in_ctx Γ n decl]
    | tProd A B =>  [× T = U, [Γ |- A : U]< wl > & [Γ,, A |- B : U]< wl >]
    | tLambda A t => ∑ B, [× T = tProd A B, [Γ |- A]< wl > & [Γ,, A |- t : B]< wl >]
    | tApp f a => ∑ A B, [× T = B[a..], [Γ |- f : tProd A B]< wl > & [Γ |- a : A]< wl >]
    | tSort _ => False
    | tNat => T = U
    | tZero => T = tNat
    | tSucc n => T = tNat × [Γ |- n : tNat]< wl >
    | tNatElim P hz hs n =>
      [× T = P[n..], [Γ,, tNat |- P]< wl >, [Γ |- hz : P[tZero..]]< wl >, [Γ |- hs : elimSuccHypTy P]< wl > & [Γ |- n : tNat]< wl >]
    | tBool => T = U
    | tTrue => T = tBool
    | tFalse => T = tBool
    | tBoolElim P ht hf n =>
      [× T = P[n..], [Γ,, tBool |- P]< wl >, [Γ |- ht : P[tTrue..]]< wl >, [Γ |- hf : P[tFalse..]]< wl > & [Γ |- n : tBool]< wl >]
    | tAlpha n => T = tBool × [Γ |- n : tNat]< wl >
    | tEmpty => T = U
    | tEmptyElim P e =>
      [× T = P[e..], [Γ,, tEmpty |- P]< wl > & [Γ |- e : tEmpty]< wl >]
    | tSig A B => [× T = U, [Γ |- A : U]< wl > & [Γ ,, A |- B : U]< wl >]
    | tPair A B a b =>
     [× T = tSig A B, [Γ |- A]< wl >, [Γ,, A |- B]< wl >, [Γ |- a : A]< wl > & [Γ |- b : B[a..]]< wl >]
    | tFst p => ∑ A B, T = A × [Γ |- p : tSig A B]< wl >
    | tSnd p => ∑ A B, T = B[(tFst p)..] × [Γ |- p : tSig A B]< wl >
    | tId A x y => [× T = U, [Γ |- A : U]< wl >, [Γ |- x : A]< wl > & [Γ |- y : A]< wl >]
    | tRefl A x => [× T = tId A x x, [Γ |- A]< wl > & [Γ |- x : A]< wl >]
    | tIdElim A x P hr y e => 
      [× T = P[e .: y..], [Γ |- A]< wl >, [Γ |- x : A]< wl >, [Γ,, A,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) |- P]< wl >, [Γ |- hr : P[tRefl A x .: x..]]< wl >, [Γ |- y : A]< wl > & [Γ |- e : tId A x y]< wl >]
  end.
*)


Lemma termGen wl Γ t A :
  [Γ |- t : A]< wl > ->
  ∑ A', termGenData wl Γ t A' × ((A' = A) + [Γ |- A' ≅ A]< wl >).
Proof.
  induction 1 ; cbn.
  all: try now (eexists ; split ; [..|left ; reflexivity] ; now econstructor).
  - destruct IHTypingDecl as [? [? [-> | ]]].
    + prod_splitter; tea; now right.
    + prod_splitter; tea; right; now eapply TypeTrans.
  - eexists ; split ; [..|left ; reflexivity].
    destruct IHTypingDecl1 as [At [HAt Heqt]] ; destruct IHTypingDecl2 as [Af [HAf Heqf]] ; econstructor.
    2,4: eassumption.
    + destruct Heqt ; [ subst | now eauto].
      econstructor.
      now boundary.
    + destruct Heqf ; [ subst | now eauto].
      econstructor.
      now boundary.
Qed.

Lemma neutral_ty_inv wl Γ A :
  [Γ |- A]< wl > -> whne A -> [Γ |- A : U]< wl >.
Proof.
  intros Hty Hne.
  unshelve eapply TypeRefl, ty_conv_inj in Hty.
  - now constructor.
  - now constructor.
  - cbn in *.
    apply Fundamental in Hty; destruct Hty.
    now eapply escapeTm.
Qed.

Lemma prod_ty_inv wl Γ A B :
  [Γ |- tProd A B]< wl > ->
  [Γ |- A]< wl > × [Γ,, A |- B]< wl >.
Proof.
  intros Hty.
  apply Fundamental in Hty; destruct Hty.
  pose proof (HA := PiValidDom _ VA).
  pose proof (HB := PiValidCod _ VA).
  split ; now eapply escapeTy.
Qed.

Lemma sig_ty_inv wl Γ A B :
  [Γ |- tSig A B]< wl > ->
  [Γ |- A]< wl > × [Γ,, A |- B]< wl >.
Proof.
  intros Hty.
  apply Fundamental in Hty; destruct Hty.
  pose proof (HA := domSigValid _ VA).
  pose proof (HB := codSigValid _ VA).
  split ; now eapply escapeTy.
Qed.
(*
Lemma id_ty_inv wl Γ A x y :
  [Γ |- tId A x y]< wl > ->
  [Γ |- A]< wl > × [Γ |- x : A]< wl > × [Γ |- y : A]< wl >.
Proof.
  intros Hty.
  apply Fundamental in Hty; destruct Hty.
  split ; [eapply escapeTy |..].
  
  apply TypeRefl id_ty_inj in Hty as [HA HB].
  prod_splitter; boundary.
Qed.
*)
Lemma termGen' wl Γ t A :
[Γ |- t : A]< wl > ->
∑ A', (termGenData wl Γ t A') × [Γ |- A' ≅ A]< wl >.
Proof.
intros * H.
destruct (termGen _ _ _ _ H) as [? [? [->|]]].
2: now eexists.
eexists ; split ; tea.
econstructor.
boundary.
Qed.

Lemma typing_eta' (wl : wfLCon) (Γ : context) A B f :
  [Γ |- f : tProd A B]< wl > ->
  [Γ,, A |- eta_expand f : B]< wl >.
Proof.
  intros Hf.
  eapply typing_eta ; tea.
  - eapply prod_ty_inv.
    boundary.
  - eapply prod_ty_inv.
    boundary.
Qed.

Theorem subject_reduction_one wl Γ A t t' :
    [Γ |- t : A]< wl > ->
    [t ⤳ t']< wl > ->
    [Γ |- t ≅ t' : A]< wl >.
Proof.
  intros Hty Hred.
  destruct (termGen' _ _ _ _ Hty) as [A' [tG Hconv]].
  induction tG in Hred, Hconv, A |- *.
  all: try (now inversion Hred).
  - inversion Hred.
    + subst.      
      econstructor ; [ | eassumption].
      pose proof (boundary_tm _ _ _ _ t).
      eapply prod_ty_inv in H.
      econstructor ; eauto.
      1: 
      Check eta_expand.
  
  intros Hty Hred.
  induction Hred in Hty, A |- *.
  - apply termGen' in Hty as (?&((?&?&[-> Hty])&Heq)).
    apply termGen' in Hty as (?&((?&[->])&Heq')).
    eapply prod_ty_inj in Heq' as [? HeqB].
    econstructor.
    1: econstructor ; gen_typing.
    etransitivity ; tea.
    eapply typing_subst1 ; tea.
    now econstructor.
  - apply termGen' in Hty as (?&((?&?&[->])&Heq)).
    econstructor ; tea.
    econstructor.
    + now eapply IHHred.
    + now econstructor.
  - apply termGen' in Hty as [?[[->]?]].
    econstructor; tea.
    econstructor.
    1-3: now econstructor.
    now eapply IHHred.
  - apply termGen' in Hty as [?[[->]?]].
    now do 2 econstructor.
  - apply termGen' in Hty as [?[[-> ???(?&[->]&?)%termGen']?]].
    now do 2 econstructor.
  - apply termGen' in Hty as [?[[->]?]].
    econstructor ; tea.
    econstructor.
    1: now econstructor.
    now eapply IHHred.
  - apply termGen' in Hty as [? [[?[?[->]]]]].
    eapply TermConv; tea ; refold.
    now econstructor.
  - apply termGen' in Hty as [?[[?[?[-> h]]]]].
    apply termGen' in h as [?[[->] u]].
    destruct (sig_ty_inj _ _ _ _ _ u).
    eapply TermConv; refold.
    2: etransitivity;[|tea]; now symmetry.
    econstructor; tea.
  - apply termGen' in Hty as [? [[?[?[->]]]]].
    eapply TermConv; tea ; refold.
    now econstructor.
  - apply termGen' in Hty as [?[[?[?[-> h]]]]].
    apply termGen' in h as [?[[->] u]].
    destruct (sig_ty_inj _ _ _ _ _ u).
    assert [Γ |- B[(tFst (tPair A0 B a b))..] ≅ A]< wl >.
    1:{ etransitivity; tea. eapply typing_subst1; tea.
      eapply TermConv; refold. 2: now symmetry.
      eapply TermRefl; refold; gen_typing.
    }
    eapply TermConv; tea; refold.
    now econstructor.
  - apply termGen' in Hty as [? [[-> ????? h]]].
    apply termGen' in h as [? [[->] h']].
    pose proof h' as []%id_ty_inj.
    econstructor; tea.
    econstructor; tea.
    1: now econstructor.
    + eapply TermConv; refold; [etransitivity; tea|]; now symmetry.
    + eapply TermConv; refold; now symmetry.
  - apply termGen' in Hty as [? [[-> ????? h]]].
    econstructor; tea; econstructor; tea.
    all: now first [eapply TypeRefl |eapply TermRefl| eauto].
  Qed.


  Theorem subject_reduction_one_type wl Γ A A' :
  [Γ |- A]< wl > ->
  [A ⤳ A']< wl > ->
  [Γ |- A ≅ A']< wl >.
Proof.
  intros Hty Hred.
  destruct Hred.
  all: inversion Hty ; subst ; clear Hty ; refold.
  all: econstructor.
  all: eapply subject_reduction_one ; tea.
  all: now econstructor.
Qed.

Theorem subject_reduction Γ t t' A :
  [Γ |- t : A]< wl > ->
  [t ⤳* t']< wl > ->
  [Γ |- t ⤳* t' : A]< wl >.
Proof.
  intros Hty Hr; split ; refold.
  - assumption.
  - assumption.
  - induction Hr.
    + now constructor.
    + eapply subject_reduction_one in o ; tea.
      etransitivity ; tea.
      eapply IHHr.
      now boundary.
Qed.

Theorem subject_reduction_type wl Γ A A' :
[Γ |- A]< wl > ->
[A ⤳* A']< wl > ->
[Γ |- A ⤳* A']< wl >.
Proof.
  intros Hty Hr; split; refold.
  - assumption.
  - assumption.
  - induction Hr.
    + now constructor.
    + eapply subject_reduction_one_type in o ; tea.
      etransitivity ; tea.
      eapply IHHr.
      now boundary.
Qed.

Corollary conv_red_l wl Γ A A' A'' : [Γ |-[de] A' ≅ A'']< wl > -> [A' ⤳* A]< wl > -> [Γ |-[de] A ≅ A'']< wl >.
Proof.
  intros Hconv **.
  etransitivity ; tea.
  symmetry.
  eapply RedConvTyC, subject_reduction_type ; tea.
  boundary.
Qed.

Lemma Uterm_isType wl Γ A :
  [Γ |-[de] A : U]< wl > ->
  whnf A ->
  isType A.
Proof.
  intros Hty Hwh.
  destruct Hwh.
  all: try solve [now econstructor].
  all: exfalso.
  all: eapply termGen' in Hty ; cbn in *.
  all: prod_hyp_splitter ; try easy.
  all: subst.
  all:
    match goal with
      H : [_ |-[de] _ ≅ U] |- _ => unshelve eapply ty_conv_inj in H as Hconv
    end.
  all: try now econstructor.
  all: try now cbn in Hconv.
Qed.
  
Lemma type_isType wl Γ A :
  [Γ |-[de] A]< wl > ->
  whnf A ->
  isType A.
Proof.
  intros [] ; refold; cycle -1.
  1: intros; now eapply Uterm_isType.
  all: econstructor.
Qed.

Lemma fun_isFun wl Γ A B t:
  [Γ |-[de] t : tProd A B]< wl > ->
  whnf t ->
  isFun t.
Proof.
  intros Hty Hwh.
  destruct Hwh.
  all: try now econstructor.
  all: eapply termGen' in Hty ; cbn in *.
  all: exfalso.
  all: prod_hyp_splitter ; try easy.
  all: subst.
  all:
    match goal with
      H : [_ |-[de] _ ≅ tProd _ _]< wl > |- _ => unshelve eapply ty_conv_inj in H as Hconv
    end.
  all: try now econstructor.
  all: now cbn in Hconv.
Qed.

Lemma nat_isNat Γ t:
  [Γ |-[de] t : tNat]< wl > ->
  whnf t ->
  isNat t.
Proof.
  intros Hty Hwh.
  destruct Hwh.
  all: try now econstructor.
  all: eapply termGen' in Hty ; cbn in *.
  all: exfalso.
  all: prod_hyp_splitter ; try easy.
  all: subst.
  all:
    match goal with
      H : [_ |-[de] _ ≅ tNat]< wl > |- _ => unshelve eapply ty_conv_inj in H as Hconv
    end.
  all: try now econstructor.
  all: now cbn in Hconv.
Qed.

Lemma empty_isEmpty Γ t:
  [Γ |-[de] t : tEmpty]< wl > ->
  whnf t ->
  whne t.
Proof.
  intros Hty Hwh.
  destruct Hwh ; try easy.
  all: eapply termGen' in Hty ; cbn in *.
  all: exfalso.
  all: prod_hyp_splitter ; try easy.
  all: subst.
  all:
    match goal with
      H : [_ |-[de] _ ≅ tEmpty]< wl > |- _ => unshelve eapply ty_conv_inj in H as Hconv
    end.
  all: try now econstructor.
  all: now cbn in Hconv.
Qed.

Lemma id_isId Γ t {A x y} :
  [Γ |-[de] t : tId A x y]< wl > ->
  whnf t ->
  whne t + ∑ A' x', t = tRefl A' x'.
Proof.
  intros Hty wh; destruct wh; try easy.
  all: eapply termGen' in Hty; cbn in *; exfalso.
  all: prod_hyp_splitter ; try easy; subst.
  all:
    match goal with
      H : [_ |-[de] _ ≅ tId _ _ _]< wl > |- _ => unshelve eapply ty_conv_inj in H as Hconv
    end; try econstructor.
  all: now cbn in Hconv.
Qed.


Lemma neutral_isNeutral wl Γ A t :
  [Γ |-[de] t : A]< wl > ->
  whne A ->
  whnf t ->
  whne t.
Proof.
  intros (?&Hgen&Hconv)%termGen' HwA Hwh.
  set (iA := NeType HwA).
  destruct Hwh ; cbn in * ; try easy.
  all: exfalso.
  all: prod_hyp_splitter.
  all: subst.
  all: unshelve eapply ty_conv_inj in Hconv ; tea.
  all: try now econstructor.
  all: now cbn in Hconv.
Qed.
  Lemma isType_WRed_to_Red : forall (wl : wfLCon) (Γ : context) (T : term) l,
        isType T ->
        W[ Γ ||-< l > T ]< wl > ->
        [ Γ ||-< l > T ]< wl >.
  Proof.
    intros ???? [] ; intros Hyp.
    - destruct s.
      assert (forall d : DTree wl,
                 Ssig (fun wl' : wfLCon => over_tree wl wl' d)).
      { clear.
        induction d.
        - exists k.
          now eapply wfLCon_le_id.
        - cbn.
          clear IHd2 ; destruct IHd1 as [wl' Hyp].
          exists wl'.
          pose (H := over_tree_le Hyp _ _ (in_here_l _)).
          now rewrite (decidInLCon_true H).
      }
      specialize (H (WT _ Hyp)) as [wl' Ho].
      pose proof (Red := WRed _ Hyp _ Ho).
      eapply invLRU in Red ; destruct Red.
      eapply LRU_.
      econstructor.
      1: eassumption.
      now Wescape ; gen_typing.
      eapply redtywf_refl ; now Wescape.
    - assert (WHA : W[ Γ ||-< l > A ]< wl >).
      { exists (WT _ Hyp).
        intros wl' Ho ; destruct Hyp as [d Hd] ; cbn in * ; specialize (Hd wl' Ho).
        eapply invLRΠ in Hd.
        destruct Hd as [X Y red ????]. Print whnf.
        pose proof (Heq := redtywf_whnf red (whnf_tProd)) ; inversion Heq ; subst ; clear Heq.
        destruct polyRed.
        erewrite <- (wk_id_ren_on Γ X).
        eapply shpRed.
        1: now eapply wfLCon_le_id.
        gen_typing.
      }
      assert (WHB : W[ Γ,, A ||-< l > B ]< wl >) by admit.
      eapply LRPi'.
      econstructor ; [ .. | unshelve econstructor].
      1: eapply redtywf_refl ; now Wescape.
      1,2: econstructor ; now Wescape.
      5,6: now Wescape.
      + econstructor ; now Wescape.
      + 
      
      { eapply (TreeSplit (WT _ Hyp)).
        intros wl' Ho ; destruct Hyp as [d Hd] ; cbn in * ; specialize (Hd wl' Ho).
        eapply invLRΠ in Hd.
        destruct Hd as [X Y red ????]. Print whnf.
        pose proof (Heq := redtywf_whnf red (whnf_tProd)) ; inversion Heq ; subst ; clear Heq.
        destruct polyRed.
        About FundTmVar.
        Print FundTm.
        About PiValidCod.
        erewrite <- (wk_id_ren_on Γ X).
        eapply shpRed.
        1: now eapply wfLCon_le_id.
        
        
        Print wk_id.
        Unset Printing Notations. Print wk_well_wk.

      Wescape.
      eapply LRPi'.
      cbn.
      econstructor.
      1: now eapply redtywf_refl.
      gen_typing.
      1: as.

      About LRLRΠ_.

      ∑ wl', [ Γ ||-< l > U ]< wl' >).
      { destruct Hyp as [d Hd].
        unshelve eexists _ ; [ | eapply Hd].
        Print DTree.
        all: clear Hd.
        revert wl d.
        refine (fix f wl d := match d as d0 in (DTree _) return wfLCon with
                              | leaf _ => _
                              | @ϝnode _ n ne dt df => _
                              end).
                             ; induction d.
        + assumption.
        + unshelve eapply wfLCons ; [exact IHd1 | .. ].
          exact IHd1.
        + now eapply wfLCon_le_id.
        + cbn.
        
      About WUnivEq.
      pose (wl' := DTree_path _ _ (WT _ Hyp)).
      About DTree_path.
      Print invLRU.
      eapply LRU_.
      econstructor.
