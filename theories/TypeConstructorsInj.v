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
*)

  Corollary prod_ty_inj wl Γ A B  A' B' :
    [Γ |- tProd A B ≅ tProd A' B']< wl > ->
    [Γ |- A' ≅ A]< wl > × [Γ,, A' |- B ≅ B']< wl >.
  Proof.
    intros Hconv.
    unshelve eapply ty_conv_inj in Hconv ; try now econstructor.
    now eassumption.
Qed.

    
  (*
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
*)
  Corollary sig_ty_inj wl Γ A B  A' B' :
    [Γ |- tSig A B ≅ tSig A' B']< wl > ->
    [Γ |- A' ≅ A]< wl > × [Γ,, A' |- B ≅ B']< wl >.
  Proof.
    intros Hty.
    unshelve eapply ty_conv_inj in Hty.
    1-2: constructor.
    now eassumption.
  Qed.
(*
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
*)
  Corollary id_ty_inj {wl Γ A A' x x' y y'} :
    [Γ |- tId A x y ≅ tId A' x' y']< wl > ->
    [× [Γ |- A' ≅ A]< wl >, [Γ |- x ≅ x' : A]< wl > & [Γ |- y ≅ y' : A]< wl >].
  Proof.
    intros Hty.
    unshelve eapply ty_conv_inj in Hty.
    1-2: constructor.
    now eassumption.
  Qed.
  
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
 




Fixpoint termGenData2 (wl : wfLCon) (Γ : context) (t T : term) : Type :=
  match t with
    | tRel n => ∑ decl, [× T = decl, [|- Γ]< wl >& in_ctx Γ n decl]
    | tProd A B =>  [× T = U, [Γ |- A : U]< wl > & [Γ,, A |- B : U]< wl >]
    | tLambda A t => ∑ B, [× T = tProd A B, [Γ |- A]< wl > & [Γ,, A |- t : B]< wl >]
    | tApp f a => ∑ A B C, [× T = B[a..], [Γ |- f : tProd A B]< wl >, [Γ |- a : A]< wl >, [Γ |- C ≅ tProd A B]< wl > & termGenData2 wl Γ f C]
    | tSort _ => False
    | tNat => T = U
    | tZero => T = tNat
    | tSucc n => ∑ X, [× T = tNat × [Γ |- n : tNat]< wl >, [Γ |- X ≅ tNat]< wl > & termGenData2 wl Γ n X] 
    | tNatElim P hz hs n =>
        ∑ X, [× T = P[n..], [Γ,, tNat |- P]< wl >, [Γ |- hz : P[tZero..]]< wl >, [Γ |- hs : elimSuccHypTy P]< wl >, [Γ |- n : tNat]< wl >,
                            [Γ |- X ≅ tNat]< wl > & termGenData2 wl Γ n X ]
    | tBool => T = U
    | tTrue => T = tBool
    | tFalse => T = tBool
    | tBoolElim P ht hf n =>
        ∑ X, [× T = P[n..], [Γ,, tBool |- P]< wl >, [Γ |- ht : P[tTrue..]]< wl >, [Γ |- hf : P[tFalse..]]< wl >, [Γ |- n : tBool]< wl >,
        [Γ |- X ≅ tBool]< wl > & termGenData2 wl Γ n X  ]
    | tAlpha n => ∑ X, [× T = tBool, [Γ |- n : tNat]< wl >, [Γ |- X ≅ tNat]< wl > & termGenData2 wl Γ n X] 
    | tEmpty => T = U
    | tEmptyElim P e =>
        ∑ X, [× T = P[e..], [Γ,, tEmpty |- P]< wl >, [Γ |- e : tEmpty]< wl >,
        [Γ |- X ≅ tEmpty]< wl > & termGenData2 wl Γ e X  ]
    | tSig A B => [× T = U, [Γ |- A : U]< wl > & [Γ ,, A |- B : U]< wl >]
    | tPair A B a b =>
     [× T = tSig A B, [Γ |- A]< wl >, [Γ,, A |- B]< wl >, [Γ |- a : A]< wl > & [Γ |- b : B[a..]]< wl >]
    | tFst p => ∑ A B X, [× T = A, [Γ |- p : tSig A B]< wl >, [Γ |- X ≅ tSig A B]< wl > & termGenData2 wl Γ p X]
    | tSnd p => ∑ A B X, [× T = B[(tFst p)..], [Γ |- p : tSig A B]< wl >,
                       [Γ |- X ≅ tSig A B]< wl > & termGenData2 wl Γ p X]
    | tId A x y => [× T = U, [Γ |- A : U]< wl >, [Γ |- x : A]< wl > & [Γ |- y : A]< wl >]
    | tRefl A x => [× T = tId A x x, [Γ |- A]< wl > & [Γ |- x : A]< wl >]
    | tIdElim A x P hr y e => 
        ∑ X, [× T = P[e .: y..], [Γ |- A]< wl >, [Γ |- x : A]< wl >, [Γ,, A,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) |- P]< wl >, [Γ |- hr : P[tRefl A x .: x..]]< wl >, [Γ |- y : A]< wl >, [Γ |- e : tId A x y]< wl >,
        [Γ |- X ≅ tId A x y]< wl > & termGenData2 wl Γ e X]
  end.

Inductive termGenData3 (wl : wfLCon) (Γ : context) : term -> term -> Type :=
| retGen t T : termGenData2 wl Γ t T -> termGenData3 wl Γ t T
| splitGen {t A At Af} {n} {ne : not_in_LCon (pi1 wl) n} :
  [Γ |- At ≅ A]< wl ,,l (ne, true) > ->
  termGenData3 (wl ,,l (ne, true)) Γ t At ->
  [Γ |- Af ≅ A]< wl ,,l (ne, false) > ->
  termGenData3 (wl ,,l (ne, false)) Γ t Af ->
  termGenData3 wl Γ t A.

Lemma termGen_escape  wl Γ t A :
  [ |-[ de ] Γ ]< wl > -> 
  termGenData2  wl Γ t A -> [Γ |- t : A]< wl >.
Proof.
  induction t ; cbn in * ; intros Ht Hyp ; eauto.
  all : try now (destruct Hyp as [? [? ? ?]] ; subst ; econstructor ; now eauto).
  all: try now destruct Hyp.
  all: try now (destruct Hyp as [? ? ?] ; subst ; econstructor ; now eauto).
  all: try now (destruct Hyp as [? [? [? [? ?]]]] ; subst ; econstructor ; now eauto).
  all: try (now subst ; econstructor).
  - destruct Hyp as [? [[? ?] ? ?]] ; subst.
    now econstructor.
Qed.


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

Lemma termGen_alt wl Γ t A :
  [Γ |- t : A]< wl > ->
  ∑ d, forall wl', over_tree wl wl' d -> ∑ A', (termGenData2 wl' Γ t A') × ((A' = A) + [Γ |- A' ≅ A]< wl' >).
Proof.
  intros Hty ; induction Hty.
  all: try now (exists (leaf _) ; intros wl' Ho ; eapply (WfContextDecl_trans _ Ho) in w ;
                       eexists ; split ; [..|left ; reflexivity] ; cbn ; econstructor 1 ; cbn ; by_prod_splitter).
  all: try now (((destruct IHHty1 as [d1 H1], IHHty2 as [d2 H2] ; exists (DTree_fusion _ d1 d2) ; intros wl' Ho) + 
               (destruct IHHty as [d1 H1] ; exists d1 ; intros wl' Ho)) ;
                ((eapply (TypingDecl_trans _ (over_tree_le Ho)) in Hty1, Hty2) +
                   (eapply (TypingDecl_trans _ (over_tree_le Ho)) in Hty  ; eapply (WfTypeDecl_trans _ (over_tree_le Ho)) in w) +
               (eapply (TypingDecl_trans _ (over_tree_le Ho)) in Hty));
            ((specialize (H1 wl' (over_tree_fusion_l Ho)) ; specialize (H2 wl' (over_tree_fusion_r Ho))) + (specialize (H1 wl' Ho))) ;
                (eexists ; split ; [..|left ; reflexivity] ; cbn ; by_prod_splitter)).
  - destruct IHHty1 as [d1 H1], IHHty2 as [d2 H2] ; exists (DTree_fusion _ d1 d2) ; intros wl' Ho.
    eapply (TypingDecl_trans _ (over_tree_le Ho)) in Hty1, Hty2.
    specialize (H1 wl' (over_tree_fusion_l Ho)) ; specialize (H2 wl' (over_tree_fusion_r Ho)).
    eexists ; split ; [..|left ; reflexivity] ; cbn.
    destruct H1 as [C [HGen Hyp]].
    do 3 eexists ; split ; try (now eauto).
    destruct Hyp ; [ subst | eassumption].
    eapply TypeRefl ; now eapply boundary_tm in Hty1.
  - destruct IHHty as [d H]; exists d ; intros wl' Ho ;
      eapply (TypingDecl_trans _ (over_tree_le Ho)) in Hty;
      try (eapply (WfTypeDecl_trans _ (over_tree_le Ho)) in w ).
    specialize (H wl' Ho) as [A'' [HGen [Heq | Hconv]]] ; subst.
    + eexists ; split ;  [..|left ; reflexivity].
      eexists ; split ; tea; eauto ; econstructor ; now boundary.
    + eexists ; split ;  [..|left ; reflexivity].
      exists A'' ; split ; tea; now eauto.
  - destruct IHHty1 as [d1 H1], IHHty2 as [d2 H2], IHHty3 as [d3 H3] ; exists (DTree_fusion _ d1 (DTree_fusion _ d2 d3)) ; intros wl' Ho ;
      eapply (TypingDecl_trans _ (over_tree_le Ho)) in Hty1, Hty2, Hty3 ;
      try (eapply (WfTypeDecl_trans _ (over_tree_le Ho)) in w ).
    specialize (H3 wl' (over_tree_fusion_r (over_tree_fusion_r Ho))) as [A'' [HGen [Heq | Hconv]]] ; subst.
    + eexists ; split ;  [..|left ; reflexivity].
      eexists ; split ; tea; eauto ; econstructor ; now boundary.
    + eexists ; split ;  [..|left ; reflexivity].
      exists A'' ; split ; tea; now eauto.
  - destruct IHHty as [d H]; exists d ; intros wl' Ho ;
      eapply (TypingDecl_trans _ (over_tree_le Ho)) in Hty;
      try (eapply (WfTypeDecl_trans _ (over_tree_le Ho)) in w ).
    specialize (H wl' Ho) as [A'' [HGen [Heq | Hconv]]] ; subst.
    + eexists ; split ;  [..|left ; reflexivity].
      eexists ; split ; tea; eauto ; econstructor ; now boundary.
    + eexists ; split ;  [..|left ; reflexivity].
      exists A'' ; split ; tea; now eauto.
  - destruct IHHty as [d H]; exists d ; intros wl' Ho ;
      eapply (TypingDecl_trans _ (over_tree_le Ho)) in Hty.
    specialize (H wl' Ho) as [A'' [HGen [Heq | Hconv]]] ; subst.
    + eexists ; split ;  [..|left ; reflexivity].
      eexists ; split ; tea; eauto ; econstructor ; now boundary.
    + eexists ; split ;  [..|left ; reflexivity].
      exists A'' ; split ; tea; now eauto.
  - destruct IHHty1 as [d1 H1], IHHty2 as [d2 H2], IHHty3 as [d3 H3] ; exists (DTree_fusion _ d1 (DTree_fusion _ d2 d3)) ; intros wl' Ho ;
      eapply (TypingDecl_trans _ (over_tree_le Ho)) in Hty1, Hty2, Hty3 ;
      try (eapply (WfTypeDecl_trans _ (over_tree_le Ho)) in w ).
    specialize (H3 wl' (over_tree_fusion_r (over_tree_fusion_r Ho))) as [A'' [HGen [Heq | Hconv]]] ; subst.
    + eexists ; split ;  [..|left ; reflexivity].
      eexists ; split ; tea; eauto ; econstructor ; now boundary.
    + eexists ; split ;  [..|left ; reflexivity].
      exists A'' ; split ; tea; now eauto.
  - destruct IHHty1 as [d1 H1], IHHty2 as [d2 H2] ; exists (DTree_fusion _ d1 d2) ; intros wl' Ho.
    eapply (TypingDecl_trans _ (over_tree_le Ho)) in Hty1, Hty2.
    eapply (WfTypeDecl_trans _ (over_tree_le Ho)) in w, w0.
    eexists ; split ; [..|left ; reflexivity] ; cbn.
    now by_prod_splitter.
  - destruct IHHty as [d H] ; exists d ; intros wl' Ho ;
      eapply (TypingDecl_trans _ (over_tree_le Ho)) in Hty.
    specialize (H wl' Ho) as [A'' [HGen [Heq | Hconv]]] ; subst.
    + eexists ; split ;  [..|left ; reflexivity] ; cbn.
      eexists ; eexists ; eexists ; split ; tea; eauto ; econstructor ; now boundary.
    + eexists ; split ;  [..|left ; reflexivity].
      eexists ; eexists ; exists A'' ; split ; tea; now eauto.    
  - destruct IHHty as [d H] ; exists d ; intros wl' Ho ;
      eapply (TypingDecl_trans _ (over_tree_le Ho)) in Hty.
    specialize (H wl' Ho) as [A'' [HGen [Heq | Hconv]]] ; subst.
    + eexists ; split ;  [..|left ; reflexivity] ; cbn.
      eexists ; eexists ; eexists ; split ; tea; eauto ; econstructor ; now boundary.
    + eexists ; split ;  [..|left ; reflexivity].
      eexists ; eexists ; exists A'' ; split ; tea; now eauto.    
    
  - destruct IHHty1 as [d1 H1], IHHty2 as [d2 H2], IHHty3 as [d3 H3] ; exists (DTree_fusion _ d1 (DTree_fusion _ d2 d3)) ; intros wl' Ho ;
      eapply (TypingDecl_trans _ (over_tree_le Ho)) in Hty1, Hty2, Hty3 ;
      try (eapply (WfTypeDecl_trans _ (over_tree_le Ho)) in w ).
    eexists ; split ;  [..|left ; reflexivity] ; cbn ; now by_prod_splitter.
  - destruct IHHty1 as [d1 H1], IHHty2 as [d2 H2], IHHty3 as [d3 H3], IHHty4 as [d4 H4].
    exists (DTree_fusion _ (DTree_fusion _ d1 d2) (DTree_fusion _ d3 d4)) ; intros wl' Ho.
    eapply (TypingDecl_trans _ (over_tree_le Ho)) in Hty1, Hty2, Hty3, Hty4.
    eapply (WfTypeDecl_trans _ (over_tree_le Ho)) in w, w0.
    specialize (H4 wl' (over_tree_fusion_r (over_tree_fusion_r Ho))) as [A'' [HGen [Heq | Hconv]]] ; subst.
    + eexists ; split ;  [..|left ; reflexivity].
      eexists ; split ; tea; eauto ; econstructor ; now boundary.
    + eexists ; split ;  [..|left ; reflexivity].
      eexists ; now by_prod_splitter.
  - destruct IHHty as [d1 H1].
    exists d1 ; intros wl' Ho.
    eapply (TypingDecl_trans _ (over_tree_le Ho)) in Hty.
    eapply (ConvTypeDecl_trans _ (over_tree_le Ho)) in c.
    specialize (H1 wl' Ho) as [? [? [-> | ]]].
    + prod_splitter; tea; now right.
    + prod_splitter; tea; right; now eapply TypeTrans.
  - unshelve eexists.
    1: econstructor 2 ; [exact (projT1 IHHty1) | exact (projT1 IHHty2)].
    destruct IHHty1 as [d1 H1], IHHty2 as [d2 H2] ; intros wl' Ho ; cbn in *.
    destruct (decidInLCon wl' n) ; try now inversion Ho.
    + now specialize (H1 wl' Ho).
    + now specialize (H2 wl' Ho).
Qed.
(*
Proof.
  intros Hty.
  induction Hty.
  all: try (eexists ; split ; [..|left ; reflexivity] ; cbn ; econstructor 1 ; cbn ; by_prod_splitter).
  - destruct IHHty1 as [? [? [-> | ]]].
    + destruct IHHty2 as [? [? [-> | ]]].
      * remember (tProd A B) ; induction t ; subst.
        -- eexists ; split ; [.. | left ; reflexivity] ; cbn ; econstructor 1 ; cbn.
           eexists ; eexists ; now split.
        -- eexists ; split ; [ .. | left ; reflexivity] ; cbn ; econstructor 2 ; cbn.
    + 
    
    eexists ; split ; [.. | left ; reflexivity] ; cbn ; econstructor 1 ; cbn.
    eexists ; eexists ; split ; [reflexivity | now eauto | now eauto | ].
    clear IHHty2 ; destruct IHHty1 as [? [? [-> | ]]].
    
  - destruct IHHty as [? [? [-> | ]]].
    + prod_splitter; tea; now right.
    + prod_splitter; tea; right; now eapply TypeTrans.
  - eexists ; split ; [..|left ; reflexivity].
    destruct IHHty1 as [At [HAt Heqt]] ; destruct IHHty2 as [Af [HAf Heqf]] ; cbn ; econstructor 2. 
    2,4: eassumption.
    + destruct Heqt ; [ subst | now eauto].
      econstructor.
      now boundary.
    + destruct Heqf ; [ subst | now eauto].
      econstructor.
      now boundary.
Qed.
*)

Lemma termGen_alt' wl Γ t A :
[Γ |- t : A]< wl > ->
∑ d, forall wl', over_tree wl wl' d -> ∑ A', (termGenData2 wl' Γ t A') × [Γ |- A' ≅ A]< wl' >.
Proof.
intros * H.
destruct (termGen_alt _ _ _ _ H) as [d Hd] ; exists d ; intros wl' Ho.
  specialize (Hd wl' Ho) as [? [? [->|]]].
- eexists ; split ; tea.
  eapply (TypingDecl_trans _ (over_tree_le Ho)) in H.
  econstructor.
  boundary.
- now eexists.
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

Lemma subject_reduction_one_aux wl Γ A t t' :
    [Γ |- t : A]< wl > ->
    [t ⤳ t']< wl > ->
    termGenData2 wl Γ t A ->
    [Γ |- t ≅ t' : A]< wl >.
Proof.
  intros Hty Hred.
  induction Hred in Hty, A |- * ; intros HGen ; cbn in *.
  - destruct HGen as [A' [B' [C [Heq ?? Hconv [B'' [Heq' ?]]]]]] ; subst.
    symmetry in Hconv ; eapply prod_ty_inj in Hconv as [? HeqB].
    econstructor ; tea.
    all: now econstructor.
  - destruct HGen as [A' [B' [C [Heq ?? Hconv HGen]]]] ; subst.
    econstructor ; [ | now econstructor].
    econstructor ; [ | eassumption].
    eapply IHHred ; tea.
    econstructor ; [ eassumption| now symmetry].
  - destruct HGen as [A' [Heq ???? Hconv HGen]] ; subst.
    econstructor ; tea ; try now econstructor.
    econstructor ; [ | eassumption].
    eapply IHHred ; [ | eassumption].
    now econstructor ; [ | symmetry].
  - destruct HGen as [A' [Heq ???? Hconv HGen]] ; subst.
    now econstructor ; tea.
  - destruct HGen as [A' [Heq ???? Hconv [A'' [[Heq' ?] Hconv']]]] ; subst.
    now econstructor ; tea.
  - destruct HGen as [A' [Heq ?? Hconv HGen]] ; subst.
    econstructor ; tea ; try now econstructor.
    econstructor ; [ | eassumption].
    eapply IHHred ; [ | eassumption].
    now econstructor ; [ | symmetry].
  - destruct HGen as [A' [Heq ?? Hconv HGen]] ; subst.
    econstructor ; tea ; try now econstructor.
    econstructor ; [ | eassumption].
    eapply IHHred ; [ | eassumption].
    now econstructor ; [ | symmetry].
  - destruct HGen as [A' [Heq ???? Hconv HGen]] ; subst.
    now econstructor ; tea.
  - destruct HGen as [A' [Heq ??????]] ; subst.
    now econstructor ; tea.
  - destruct HGen as [X [Heq HnSucc Hconv HGen]] ; subst.
    econstructor.
    assert (Hyp :  [Γ |-[ de ] n ≅ n' : tNat ]< wl > -> [Γ |-[ de ] nSucc k n ≅ nSucc k n' : tNat ]< wl >).
    { clear ; intros H ; induction k ; [now eauto | ].
      cbn ; now econstructor.
    }
    assert (Hyp2 : forall X n, termGenData2 wl Γ (tSucc n) X -> ∑ X', [Γ |-[ de ] X' ≅ X]< wl > × (termGenData2 wl Γ n X')).
    { clear ; intros X n Hyp ; cbn in *.
      destruct Hyp as [X' [[Heq Hn] Hconv HGen]] ; subst.
      exists X' ; now split.
    }
    assert (Hyp3 : forall X, termGenData2 wl Γ (nSucc k n) X -> ∑ X', [Γ |-[ de ] X' ≅ X]< wl > × (termGenData2 wl Γ n X')).
    { intros X' HGen'.
      unshelve epose proof (HX := termGen_escape _ _ _ _ _ HGen') ; [now boundary | ].
      revert X' HX HGen' ; clear - Hyp2 ; induction k ; intros X' HX HGen ; [ exists X' ; split ; eauto | ].
      1: eapply TypeRefl ; now eapply boundary_tm in HX.
      cbn in * ; eapply Hyp2 in HGen as [X'' [??]].
      unshelve epose proof (HX' := termGen_escape _ _ _ _ _ t) ; [now boundary | ].
      eapply IHk in t as [X''' [??]] ; eauto.
      exists X''' ; split ; eauto.
      now etransitivity.
    }
    eapply Hyp.
    specialize (Hyp3 _ HGen) as [X' [Hconv' HGen']].
    econstructor ; [ eapply (IHHred _ _ HGen') | now etransitivity].
    Unshelve.
    eapply termGen_escape ; eauto ; now boundary.
  - destruct HGen as [X [Heq Hn HX HGen]] ; subst.
    econstructor ; eauto.
    now boundary.
  - destruct HGen as [X [Y [Z [Heq Hp]]]] ; subst.
    unshelve econstructor ; [exact Y | ].
    econstructor ; [ | eassumption].
    eapply IHHred ; [ | eassumption].
    now econstructor ; [ | symmetry].
  - destruct HGen as [X [Y [Z [Heq Hp Hconv [??]]]]] ; subst.
    eapply sig_ty_inj in Hconv ; destruct Hconv.
    econstructor ; [ | now symmetry].
    econstructor ; eauto.
  - destruct HGen as [X [Y [Z [Heq Hp]]]] ; subst.
    econstructor.
    econstructor ; [ | eassumption].
    eapply IHHred ; [ | eassumption].
    now econstructor ; [ | symmetry].
  - destruct HGen as [X [Y [Z [Heq Hp Hconv [??]]]]] ; subst.
    eapply sig_ty_inj in Hconv ; destruct Hconv.
    enough [Γ |- Y[(tFst (tPair A0 B a b))..] ≅ B[(tFst (tPair A0 B a b))..]]< wl > as K.
    1: econstructor ; [ | now symmetry] ; now econstructor ; tea.
    eapply typing_subst1 ; [ | now symmetry].
    eapply TermConv; refold. 2: now symmetry.
    now eapply TermRefl; refold; gen_typing.
  - destruct HGen as [X [Heq ?????? Hconv [???]]] ; subst.
    destruct (id_ty_inj Hconv).
    econstructor ; tea.
    + econstructor ; [ | now symmetry] ; now auto.
    + econstructor ; [ | now symmetry].
      etransitivity ; [now symmetry | eassumption].
    + econstructor ; now symmetry.
  - destruct HGen as [X [Heq ?????? Hconv HGen]] ; subst.
    econstructor ; tea.
    all: try (now eapply TermRefl + now eapply TypeRefl) ; tea.
    econstructor ; [ | eassumption].
    eapply IHHred ; [ | eassumption].
    econstructor ; [ eassumption | now symmetry].
Qed.    

Theorem subject_reduction_one wl Γ A t t' :
    [Γ |- t : A]< wl > ->
    [t ⤳ t']< wl > ->
    [Γ |- t ≅ t' : A]< wl >.
Proof.
  intros Hty Hred.
  pose proof (termGen_alt wl Γ t A Hty) as [d Hd].
  eapply convtm_over_tree with d.
  intros wl' Ho.
  specialize (Hd wl' Ho) as [X [HGen [Heq | Hconv]]] ; subst.
  2: econstructor ; [ | eassumption].
  all: eapply subject_reduction_one_aux ; eauto.
  2,4: eapply red_Ltrans ; eauto ; now eapply over_tree_le.
  2: econstructor ; [ | now symmetry].
  all: eapply TypingDecl_trans ; [now eapply over_tree_le | eassumption].
Qed.


Theorem subject_reduction_one_type wl Γ A A' :
  [Γ |- A]< wl > ->
  [A ⤳ A']< wl > ->
  [Γ |- A ≅ A']< wl >.
Proof.
  intros Hty Hred.
  remember A.
  destruct Hred.
  all: rewrite Heqt in Hty ; induction Hty.
  all: try now inversion Heqt.
  all: try (econstructor ; eapply subject_reduction_one ; [ now rewrite Heqt | now econstructor]).
  all: try now (eapply ϝTypeConv ; [eapply IHHty1 | eapply IHHty2] ; eauto ; now eapply red_Ltrans ; [eapply LCon_le_step, wfLCon_le_id | ]).
  eapply ϝTypeConv ; [eapply IHHty1 | eapply IHHty2] ; eauto.
  all: now econstructor.
Qed.


Theorem subject_reduction wl Γ t t' A :
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
  eapply termGen_alt in Hty as [d Hd] ; cbn in *.
  epose proof (Ho := DTree_leftmost_over _ d).
  specialize (Hd _ Ho) as [A' [HGen [Heq | Hconv]]] ; subst.
  all: destruct Hwh.
  all: try solve [now econstructor].
  all: exfalso ; cbn in *.
  all: prod_hyp_splitter.
  all: try (now inversion e).
  all: try (now inversion HGen).
  all: subst.
  all:
    match goal with
      H : [_ |-[de] _ ≅ U]< _ > |- _ => unshelve eapply ty_conv_inj in H as Hconv
    end.
  all: try now econstructor.
  all: try now cbn in Hconv.
Qed.
  
Lemma type_isType wl Γ A :
  [Γ |-[de] A]< wl > ->
  whnf A ->
  isType A.
Proof.
  induction 1 ; refold; cycle -1.
  all: try now econstructor.
  2: intros; now eapply Uterm_isType.
  now eauto.
Qed.

Lemma fun_isFun wl Γ A B t:
  [Γ |-[de] t : tProd A B]< wl > ->
  whnf t ->
  isFun t.
Proof.
  intros Hty Hwh.
  eapply termGen_alt in Hty as [d Hd] ; cbn in *.
  epose proof (Ho := DTree_leftmost_over _ d).
  specialize (Hd _ Ho) as [A' [HGen [Heq | Hconv]]] ; subst ; cbn in *.
  all: destruct Hwh.
  all: try now econstructor.
  all: exfalso ; cbn in *.
  all: prod_hyp_splitter ; try easy.
  all: try (now inversion e).
  all: try (now inversion HGen).
  all: subst.
  all:
    match goal with
      H : [_ |-[de] _ ≅ tProd _ _]< _ > |- _ => unshelve eapply ty_conv_inj in H as Hconv
    end.
  all: try now econstructor.
  all: now cbn in Hconv.
Qed.


Lemma nat_isNat wl Γ t:
  [Γ |-[de] t : tNat]< wl > ->
  whnf t ->
  isNat t.
Proof.
  intros Hty Hwh.
  eapply termGen_alt in Hty as [d Hd] ; cbn in *.
  epose proof (Ho := DTree_leftmost_over _ d).
  specialize (Hd _ Ho) as [A' [HGen [Heq | Hconv]]] ; subst.
  all: destruct Hwh.
  all: try now econstructor.
  all: exfalso ; cbn in *.
  all: prod_hyp_splitter ; try easy.
  all: try (now inversion e).
  all: try (now inversion HGen).
  all: subst.
  all:
    match goal with
      H : [_ |-[de] _ ≅ tNat]< _ > |- _ => unshelve eapply ty_conv_inj in H as Hconv
    end.
  all: try now econstructor.
  all: now cbn in Hconv.
Qed.

Lemma bool_isBool wl Γ t:
  [Γ |-[de] t : tBool]< wl > ->
  whnf t ->
  isBool t.
Proof.
  intros Hty Hwh.
  eapply termGen_alt in Hty as [d Hd] ; cbn in *.
  epose proof (Ho := DTree_leftmost_over _ d).
  specialize (Hd _ Ho) as [A' [HGen [Heq | Hconv]]] ; subst.
  all: destruct Hwh.
  all: try now econstructor.
  all: exfalso ; cbn in *.
  all: prod_hyp_splitter ; try easy.
  all: try (now inversion e).
  all: try (now inversion HGen).
  all: subst.
  all:
    match goal with
      H : [_ |-[de] _ ≅ tBool]< _ > |- _ => unshelve eapply ty_conv_inj in H as Hconv
    end.
  all: try now econstructor.
  all: now cbn in Hconv.
Qed.

Lemma empty_isEmpty wl Γ t:
  [Γ |-[de] t : tEmpty]< wl > ->
  whnf t ->
  whne t.
Proof.
  intros Hty Hwh.
  eapply termGen_alt in Hty as [d Hd] ; cbn in *.
  epose proof (Ho := DTree_leftmost_over _ d).
  specialize (Hd _ Ho) as [A' [HGen [Heq | Hconv]]] ; subst.
  all: destruct Hwh ; try easy.
  all: exfalso ; cbn in *.
  all: prod_hyp_splitter ; try easy.
  all: try (now inversion e).
  all: try (now inversion HGen).
  all: subst.
  all:
    match goal with
      H : [_ |-[de] _ ≅ tEmpty]< _ > |- _ => unshelve eapply ty_conv_inj in H as Hconv
    end.
  all: try now econstructor.
  all: now cbn in Hconv.
Qed.

Lemma id_isId wl Γ t {A x y} :
  [Γ |-[de] t : tId A x y]< wl > ->
  whnf t ->
  whne t + ∑ A' x', t = tRefl A' x'.
Proof.
  intros Hty wh.
  eapply termGen_alt in Hty as [d Hd] ; cbn in *.
  epose proof (Ho := DTree_leftmost_over _ d).
  specialize (Hd _ Ho) as [A' [HGen [Heq | Hconv]]] ; subst.
  all: destruct wh ; try easy.
  all: exfalso ; cbn in *.
  all: prod_hyp_splitter ; try easy.
  all: try (now inversion e).
  all: try (now inversion HGen).
  all: subst.
  all:
    match goal with
      H : [_ |-[de] _ ≅ tId _ _ _]< _ > |- _ => unshelve eapply ty_conv_inj in H as Hconv
    end; try econstructor.
  all: now cbn in Hconv.
Qed.


Lemma neutral_isNeutral wl Γ A t :
  [Γ |-[de] t : A]< wl > ->
  whne A ->
  whnf t ->
  whne t.
Proof.
  intros Hty HwA Hwh.
  eapply termGen_alt in Hty as [d Hd] ; cbn in *.
  epose proof (Ho := DTree_leftmost_over _ d).
  specialize (Hd _ Ho) as [A' [HGen [Heq | Hconv]]] ; subst.
  all: set (iA := NeType HwA).
  all: destruct Hwh ; cbn in * ; try easy.
  all: exfalso.
  all: prod_hyp_splitter.
  all: subst ; try (now inversion HwA).
  all: try unshelve eapply ty_conv_inj in Hconv ; tea.
  all: try now econstructor.
  all: now cbn in Hconv.
Qed.
