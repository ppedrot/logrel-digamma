Require Import PeanoNat.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations LContexts Context NormalForms UntypedReduction Weakening GenericTyping Monad LogicalRelation DeclarativeInstance.
From LogRel.LogicalRelation Require Import Induction Reflexivity Irrelevance Escape Weakening Monotonicity.

Set Universe Polymorphism.

Section Neutral.
Context `{GenericTypingProperties}.

Definition neu {l wl Γ A} :
  [Γ |- A]< wl > ->
  [ Γ |- A ~ A : U]< wl > ->
  [Γ ||-<l> A]< wl >.
Proof.
  intros wtyA reflA. apply LRne_.
  exists A; [gen_typing|..]; assumption.
Defined.

Lemma neU {l wl Γ A n} (h : [Γ ||-U<l> A]< wl >) :
  [Γ |- n : A]< wl > ->
  [Γ |- n ~ n : A]< wl > ->
  [LogRelRec l | Γ ||-U n : A | h]< wl >.
Proof.
  assert [Γ |- A ≅ U]< wl > by (destruct h; gen_typing).
  intros; exists n.
  * eapply redtmwf_conv; tea; now eapply redtmwf_refl.
  * now eapply NeType, convneu_whne.
  * apply convtm_convneu ; tea.
    1: now constructor.
    now eapply convneu_conv.
  * eapply RedTyRecBwd, neu. 1,2: gen_typing.
Defined.

Set Printing Primitive Projection Parameters.

Lemma neuEq {l wl Γ A B} (RA : [Γ ||-<l> A]< wl >) :
  [Γ |- A]< wl > -> [Γ |- B]< wl > ->
  [Γ |- A ~ B : U]< wl > ->
  [Γ ||-<l> A ≅ B | RA]< wl >.
Proof.
  intros wtyA wtyB eqAB.
  unshelve irrelevance0. 1: assumption. 3: reflexivity.
  1: apply neu; try assumption; now eapply lrefl.
  econstructor.
  1: now apply redtywf_refl.
  all: cbn; assumption.
Qed.


Lemma ty_app_ren {wl Γ Δ A f a dom cod} (ρ : Δ ≤ Γ) :
  [Γ |- f : A]< wl > -> [Γ |- A ≅ tProd dom cod]< wl > -> [Δ |- a : dom⟨ρ⟩]< wl > -> [Δ |- tApp f⟨ρ⟩ a : cod[a .: ρ >> tRel]]< wl >.
Proof.
  intros.
  replace (cod[a .: ρ >> tRel]) with (cod⟨wk_up dom ρ⟩[a..]) by (now bsimpl).
  unshelve eapply ty_app. 3: eassumption.
  replace (tProd _ _) with (tProd dom cod)⟨ρ⟩ by now bsimpl.
  gen_typing.
Qed.

Lemma convneu_app_ren {wl Γ Δ A f g a b dom cod} (ρ : Δ ≤ Γ) :
  [Γ |- f ~ g : A]< wl > ->
  [Γ |- A ≅ tProd dom cod]< wl > ->
  [Δ |- a ≅ b : dom⟨ρ⟩]< wl > ->
  [Δ |- tApp f⟨ρ⟩ a ~ tApp g⟨ρ⟩ b : cod[a .: ρ >> tRel]]< wl >.
Proof.
  intros.
  replace (cod[a .: ρ >> tRel]) with (cod⟨wk_up dom ρ⟩[a..]) by (now bsimpl).
  unshelve eapply convneu_app. 3: eassumption.
  replace (tProd _ _) with (tProd dom cod)⟨ρ⟩ by now bsimpl.
  gen_typing.
Qed.


Record complete {l wl Γ A} (RA : [Γ ||-<l> A]< wl >) := {
  reflect : forall n n',
    [Γ |- n : A]< wl > ->
    [Γ |- n' : A]< wl > ->
    [Γ |- n ~ n' : A]< wl > ->
    [Γ ||-<l> n : A | RA]< wl > × [Γ ||-<l> n ≅ n' : A| RA]< wl >;
}.

Lemma complete_reflect_simpl {l wl Γ A} (RA : [Γ ||-<l> A]< wl >) (c : complete RA) :
  forall n, [Γ |- n : A]< wl > -> [Γ |- n ~ n : A]< wl > -> [Γ ||-<l> n : A | RA]< wl >.
Proof.
intros; eapply c.
all: eassumption.
Qed.

Lemma complete_var0 {l wl Γ A A'} (RA : [Γ ,, A ||-<l> A']< wl >) :
  complete RA ->
  [Γ ,, A |- A⟨↑⟩ ≅ A']< wl > ->
  [Γ |- A]< wl > ->
  [Γ ,, A ||-<l> tRel 0 : A' | RA]< wl >.
Proof.
  intros cRA conv HA.
  assert [Γ ,, A |- tRel 0 : A']< wl >
  by (eapply ty_conv; tea; escape; eapply (ty_var (wfc_wft EscRA) (in_here _ _))).
  eapply complete_reflect_simpl; tea.
  - eapply convneu_var; tea.
Qed.



Lemma complete_U : forall l wl Γ A (RA : [Γ ||-U< l > A]< wl >), complete (LRU_ RA).
Proof.
intros l wl Γ A h0; split.
- intros ???? h; pose proof (lrefl h); pose proof (urefl h).
  assert [Γ |- A ≅ U]< wl > by (destruct h0; gen_typing); split.
  2: unshelve econstructor.
  1-3: now apply neU.
  + eapply RedTyRecBwd, neu. 1,2: try gen_typing.
  + cbn. gen_typing.
  + eapply RedTyRecBwd; apply neu. 1,2: gen_typing.
  + eapply TyEqRecBwd. eapply neuEq. all: try gen_typing.
    all: eapply ty_ne_term, tm_ne_conv; tea; gen_typing.
Qed.

Lemma complete_ne : forall l wl Γ A (RA : [Γ ||-ne A]< wl >), complete (LRne_ l RA).
Proof.
intros l wl Γ A h0; split.
- destruct h0 as [B []]; intros ** ; assert ([Γ |- A ≅ B]< wl >) by gen_typing ; split.
  + exists n; cbn.
    * eapply redtmwf_refl ; gen_typing.
    * eapply lrefl; eapply convneu_conv; eassumption.
  + exists n n'; cbn.
    1,2: eapply redtmwf_refl ; eapply ty_conv; gen_typing.
    gen_typing.
Qed.

Lemma complete_Pi : forall l wl Γ A (RA : [Γ ||-Π< l > A]< wl >),
  (forall (Δ : context) (wl' : wfLCon) (ρ : Δ ≤ Γ) (f : wl' ≤ε wl) (h : [ |-[ ta ] Δ]< wl' >),
        complete (PolyRed.shpRed RA ρ f h)) ->
  (forall (Δ : context) (wl' : wfLCon) (a : term) (ρ : Δ ≤ Γ) (f : wl' ≤ε wl) (h : [ |-[ ta ] Δ]< wl' >)
          (ha : [PolyRed.shpRed RA ρ f h | Δ ||- a : _]< wl' >)
          (wl'' : wfLCon) (Ho : over_tree wl' wl'' (PolyRed.posTree RA ρ f h ha)),
        complete (PolyRed.posRed RA ρ f h ha Ho)) ->
  complete (LRPi' RA).
Proof.
intros l wl Γ A ΠA0 ihdom ihcod; split.
- set (ΠA := ΠA0); destruct ΠA0 as [dom cod].
  simpl in ihdom, ihcod.
  assert [Γ |- A ≅ tProd dom cod]< wl > by gen_typing.
  assert [Γ |- dom]< wl >.
  {
    erewrite <- wk_id_ren_on.
    eapply escape, polyRed ; [now eapply wfLCon_le_id | ].
    gen_typing.
  }
  assert [|- Γ ,, dom]< wl > as Hext by gen_typing.
  assert [Γ,, dom |-[ ta ] tRel 0 : dom⟨@wk1 Γ dom⟩]< wl >.
  {
    eapply ty_var ; tea.
    rewrite wk1_ren_on.
    econstructor.
  }
  assert [Γ,, dom |-[ ta ] tRel 0 ~ tRel 0 : dom⟨@wk1 Γ dom⟩]< wl >
    by now apply convneu_var.
  assert [PolyRed.shpRed polyRed (wk1 dom) (wfLCon_le_id _) Hext | Γ,, dom ||- tRel 0 : dom⟨wk1 dom⟩]< wl >
    by now eapply ihdom.
  assert [Γ ,, dom |- cod]< wl >.
  {
    replace cod with cod[tRel 0 .: @wk1 Γ dom >> tRel].
    2: bsimpl; rewrite scons_eta'; now asimpl.
    unshelve eapply (wft_over_tree).
    + exact (PolyRed.posTree polyRed _ _ _ X).
    + intros wl' Hover.
      unshelve eapply escape, polyRed.
      5: eassumption.
  }
  assert (forall n Δ wl' a (ρ : Δ ≤ Γ) (f : wl' ≤ε wl),
             [|- Δ]< wl' > -> [Γ |- n : A]< wl' > ->
             [Δ |- a : dom⟨ρ⟩]< wl' > ->
             [Δ |-[ ta ] tApp n⟨ρ⟩ a : cod[a .: ρ >> tRel]]< wl' >)
    as Happ.
    {
      intros.
      eapply typing_meta_conv.
      1: eapply ty_app ; tea.
      1: eapply typing_meta_conv.
      1: eapply ty_wk.
      - eassumption.
      - eapply ty_conv ; tea.
        eapply convty_Ltrans ; [eassumption | ].
        eassumption.
      - cbn ; reflexivity.
      - now bsimpl. 
    }
    assert (forall n, [Γ |- n : A]< wl > ->
                      [Γ,, dom |-[ ta ] tApp n⟨@wk1 Γ dom⟩ (tRel 0) : cod]< wl >).
    {
      intros.
      eapply typing_meta_conv.
      1: apply Happ ; tea.
      2: bsimpl. now eapply wfLCon_le_id. rewrite scons_eta' ; now bsimpl.
    }
  assert (forall n n',
    [Γ |- n : A]< wl > -> [Γ |- n' : A]< wl > ->
    [Γ |- n ~ n : A]< wl > -> [Γ |- n' ~ n' : A]< wl > -> 
    [Γ |- n ~ n' : A]< wl > ->
    [Γ |-[ ta ] n ≅ n' : tProd dom cod]< wl >).
  {
    intros.
    eapply convtm_eta ; tea.
    - now eapply ty_conv.
    - constructor.
      now eapply convneu_conv.
    - now eapply ty_conv.
    - econstructor.
      now eapply convneu_conv.
    - unshelve eapply convtm_over_tree.
      { now eapply (PolyRed.posTree polyRed _ _ _ X). }
      intros wl' Hover.
      pose proof (over_tree_le Hover).
      eapply (convneu_Ltrans (over_tree_le Hover)) in H20.
      eapply convneu_app_ren in H20 ; tea ; cycle -1.
      2: unshelve eapply ihcod in H20 as [_ hred].
      6: exact Hover.
      1: now eapply convtm_Ltrans, escapeEqTerm, reflLRTmEq.
      4: now eapply convty_Ltrans.
      + erewrite <- wk1_ren_on.
        eapply convtm_meta_conv.
        1: now escape.
        1: bsimpl; rewrite scons_eta' ; now bsimpl.
        now bsimpl.
        + eapply ty_Ltrans, typing_meta_conv ; eauto.
          bsimpl. rewrite scons_eta'. now bsimpl.
      + eapply ty_Ltrans, typing_meta_conv ; eauto.
        bsimpl. rewrite scons_eta'. now bsimpl.
  }

  unshelve refine (let funred : forall n,
                       [Γ |- n : A]< wl > ->
                       [Γ |- n ~ n : A]< wl > ->
                       [Γ ||-Π n : A | ΠA]< wl > := _ in _).
  {
    intros. exists n (fun _ _ _ _ _ _ _ => leaf _) ; cbn.
    - eapply redtmwf_refl.
      gen_typing.
    - eauto.
    - constructor; now eapply convneu_conv.
    - intros.
      eapply ihcod ; last first.
      + eapply convne_meta_conv.
        1: eapply convneu_app.
        * eapply convne_meta_conv.
          1: eapply convneu_wk ; [eapply wfc_Ltrans ; eassumption | ].
          1: eapply convneu_conv ; tea.
          1: eapply convneu_Ltrans ; [ | eassumption].
          2: eapply convty_Ltrans ; [ | eauto].
          1,2: eapply wfLCon_le_trans ; eassumption.
          all: cbn ; easy.
        * unshelve eapply escapeEqTerm, reflLRTmEq, Tm_Ltrans.
          3,5: eassumption.
        * now bsimpl.
        * reflexivity.
      + eapply Happ.
        * now eapply wfLCon_le_trans.
        * now eapply wfc_Ltrans.
        * now eapply ty_Ltrans ; [now eapply wfLCon_le_trans | ].
        * now eapply ty_Ltrans ; [ | now escape].
      + eapply Happ ; tea.
        * now eapply wfLCon_le_trans.
        * now eapply wfc_Ltrans.
        * now eapply ty_Ltrans ; [now eapply wfLCon_le_trans | ].
        * now eapply ty_Ltrans ; [ | now escape].
    - intros.
      eapply ihcod ; last first.
      + eapply convneu_Ltrans ; [eassumption | ].
        eapply convne_meta_conv.
        1: eapply convneu_app.
        * eapply convne_meta_conv.
          1: eapply convneu_wk.
          2: eapply convneu_Ltrans, convneu_conv ; [eassumption | ..] ; tea.
          all: cbn ; easy.
        * now escape.
        * now bsimpl.
        * reflexivity. 
      + unshelve eapply ty_conv.
        2: eapply Happ ; tea.
        5:{ symmetry.
            unshelve eapply escapeEq, PolyRed.posExt.
            8: eassumption. all: eassumption.
        }
        * now eapply wfLCon_le_trans.
        * now eapply wfc_Ltrans.
        * now eapply ty_Ltrans ; [ eapply wfLCon_le_trans | ].
        * now eapply ty_Ltrans ; [ eassumption | escape ].
      + eapply ty_Ltrans, Happ ; [now eauto | ..] ; tea.
        2:now escape.
        now eapply ty_Ltrans.
  }

  intros ???? h.
  pose proof (lrefl h); pose proof (urefl h).
  split. 1: now apply funred.
  unshelve econstructor.
  1,2: now apply funred.
  all: cbn; clear funred.
  2: now eauto.
  + intros.
    now eapply leaf.
  + intros. apply ihcod; cbn.
    1,2: eapply ty_Ltrans ; [now eapply over_tree_le | ].
    1,2: pose proof (escapeTerm _ ha); eapply ty_app_ren.
    all: try eassumption.
    1,3: now eapply ty_Ltrans.
    1,2: now eapply convty_Ltrans.
    eapply convneu_Ltrans, convneu_app_ren ; [now eapply over_tree_le |.. ].
    3: eapply escapeEqTerm; eapply reflLRTmEq ; eassumption.
    1: now eapply convneu_Ltrans.
    now eapply convty_Ltrans.
Qed.

Arguments ParamRedTy.outTy /.



Lemma complete_Sig : forall l wl Γ A (RA : [Γ ||-Σ< l > A]< wl >),
  (forall (Δ : context) (wl' : wfLCon) (ρ : Δ ≤ Γ) (f : wl' ≤ε wl) (h : [ |-[ ta ] Δ]< wl' >),
        complete (PolyRed.shpRed RA ρ f h)) ->
  (forall (Δ : context) (wl' : wfLCon) (a : term) (ρ : Δ ≤ Γ) (f : wl' ≤ε wl) (h : [ |-[ ta ] Δ]< wl' >)
          (ha : [PolyRed.shpRed RA ρ f h | Δ ||- a : _]< wl' >)
          (wl'' : wfLCon) (Ho : over_tree wl' wl'' (PolyRed.posTree RA ρ f h ha)),
        complete (PolyRed.posRed RA ρ f h ha Ho)) ->
  complete (LRSig' RA).
Proof.
  intros l wl Γ A ΣA0 ihdom ihcod.
  set (ΣA := ΣA0); destruct ΣA0 as [dom cod] ; cbn in *.

  assert [Γ |- A ≅ ΣA.(outTy)]< wl >
    by (destruct ΣA; cbn in *; gen_typing).
  assert [Γ |- ΣA.(outTy)]< wl >
    by (destruct ΣA; cbn in *; gen_typing).
  assert [Γ |- dom]< wl >.
  {
    erewrite <- wk_id_ren_on.
    eapply escape, polyRed.
    + now eapply wfLCon_le_id.
    + now gen_typing.
  } 
  assert [|- Γ ,, dom]< wl > as Hext by gen_typing.
  assert [Γ,, dom |-[ ta ] tRel 0 : dom⟨@wk1 Γ dom⟩]< wl >.
  {
    eapply ty_var ; tea.
    rewrite wk1_ren_on.
    now econstructor.
  }
  assert [Γ,, dom |-[ ta ] tRel 0 ~ tRel 0 : dom⟨@wk1 Γ dom⟩]< wl >
    by now apply convneu_var.
  assert [PolyRed.shpRed polyRed (wk1 dom) (wfLCon_le_id _) Hext | Γ,, dom ||- tRel 0 : dom⟨wk1 dom⟩]< wl >
    by now eapply ihdom.
  assert [Γ ,, dom |- cod]< wl >.
  {
    replace cod with cod[tRel 0 .: @wk1 Γ dom >> tRel].
    2: bsimpl; rewrite scons_eta'; now asimpl.
    unshelve eapply (wft_over_tree).
    + exact (PolyRed.posTree polyRed _ _ _ X).
    + intros wl' Hover.
      unshelve eapply escape, polyRed.
      5: eassumption.
  }
  assert (hfst : forall n Δ wl' (ρ : Δ ≤ Γ) (f : wl' ≤ε wl) (h : [ |- Δ]< wl' >),
             [Γ |- n : A]< wl' > -> [Γ |- n ~ n : A]< wl' > ->
             [PolyRedPack.shpRed ΣA ρ f h | Δ ||- tFst n⟨ρ⟩ : _]< wl' >).
    1:{
      intros; eapply complete_reflect_simpl.
      * now eapply ihdom.
      * rewrite wk_fst; eapply ty_wk; tea.
        eapply ty_fst, ty_conv ; [eassumption | ].
        now eapply convty_Ltrans.
      * rewrite wk_fst; eapply convneu_wk; tea.
        eapply convneu_fst, convneu_conv ; [eassumption | ].
        now eapply convty_Ltrans.
    }
    assert (hconv_fst : forall n n' Δ wl' (ρ : Δ ≤ Γ) (f : wl' ≤ε wl) (h : [ |- Δ]< wl' >),
               [Γ |- n : A]< wl' > -> [Γ |- n' : A]< wl' > -> [Γ |- n ~ n' : A]< wl' > ->
               [PolyRedPack.shpRed ΣA ρ f h | Δ ||- tFst n⟨ρ⟩ ≅ tFst n'⟨ρ⟩ : _]< wl' >).
    1:{
      intros.
      eapply ihdom.
      * rewrite wk_fst; eapply ty_wk; tea.
        eapply ty_fst, ty_conv ; [eassumption | now eapply convty_Ltrans].
      * rewrite wk_fst ; eapply ty_wk ; tea.
        eapply ty_fst, ty_conv ; [eassumption | now eapply convty_Ltrans].
      * repeat rewrite wk_fst; eapply convneu_wk; tea.
        eapply convneu_fst, convneu_conv ; [eassumption | now eapply convty_Ltrans].
    }
  assert (hconv : forall n n',
  [Γ |- n : A]< wl > -> [Γ |- n' : A]< wl > ->
  [Γ |- n ~ n : A]< wl > -> [Γ |- n' ~ n' : A]< wl > ->
  [Γ |- n ~ n' : A]< wl > -> [Γ |-[ ta ] n ≅ n' : tSig dom cod]< wl >).
  {
    intros.
    eapply convtm_eta_sig ; cbn in * ; tea.
    - now eapply ty_conv.
    - econstructor.
      now eapply convneu_conv.
    - now eapply ty_conv.
    - econstructor.
      now eapply convneu_conv.
    - eapply convtm_meta_conv.
      1: eapply escapeEqTerm, ihdom.
      4: now rewrite wk_id_ren_on.
      4: reflexivity.
      all: rewrite wk_id_ren_on.
      + now eapply ty_fst, ty_conv.
      + now eapply ty_fst, ty_conv.
      + eapply convneu_fst, convneu_conv ; tea.
      Unshelve.
        * now eapply wfLCon_le_id.
        * now gen_typing.
    - eapply convtm_meta_conv.
      3: reflexivity.
      1: unshelve eapply convtm_over_tree.
      2: intros ; eapply escapeEqTerm, (ihcod _ _ (tFst n) wk_id).
      Unshelve.
      1: unshelve eapply ((PolyRed.posTree polyRed wk_id (wfLCon_le_id _))).
      2: now gen_typing.
      11: exact H21.
      5: rewrite <- (wk_id_ren_on Γ n) ; now eapply hfst.
      1,2,3: pose proof (Hyp := over_tree_le H21).
      + eapply typing_meta_conv.
        eapply ty_snd, ty_conv ; [now eapply ty_Ltrans | ].
        now eapply convty_Ltrans.
        now bsimpl.
      + eapply ty_conv.
        eapply ty_snd, ty_conv ; [now eapply ty_Ltrans | ].
        now eapply convty_Ltrans.
        symmetry.
        replace (cod[(tFst n')..]) with (cod[(tFst n') .: (@wk_id Γ) >> tRel]) by (now bsimpl).
        erewrite <- (wk_id_ren_on _ n), <- (wk_id_ren_on _ n').
        unshelve eapply escapeEq, polyRed.(PolyRed.posExt).
        4: now eapply hfst.
        4: now eapply hfst.
        now eapply wfLCon_le_id.
        now gen_typing.
        2: now eapply hconv_fst.
        revert H21 ; now destruct (wk_id_ren_on Γ n).
      + eapply convneu_Ltrans ; [eassumption | ].
        eapply convne_meta_conv.
        1:now eapply convneu_snd, convneu_conv.
        1: now bsimpl.
        easy.
      + now bsimpl.
  }
  split.
  unshelve refine ( let funred : forall n,
    [Γ |- n : A]< wl > ->
    [Γ |- n ~ n : A]< wl > -> [Γ ||-Σ n : A | ΣA]< wl > := _ in _).
  {
    intros n **.
    cbn in *.
    unshelve eexists n _ _.
    - intros. eapply hfst.
      + now eapply ty_Ltrans.
      + now eapply convneu_Ltrans.
    - intros ; now eapply leaf. 
    - eapply redtmwf_refl; now eapply ty_conv.
    - eauto.
    - constructor ; cbn ; now eapply convneu_conv.
    - intros.
      cbn.
     pose proof (Hyp := over_tree_le Ho).
      eapply complete_reflect_simpl.
      * eapply ihcod.
      * rewrite wk_snd.
        eapply typing_meta_conv.
        1: eapply ty_wk ; tea.
        1: now eapply wfc_Ltrans.
        1: eapply ty_snd, ty_conv.
        1: now eapply ty_Ltrans ; [ eapply wfLCon_le_trans | ].
        now eapply convty_Ltrans ; [eapply wfLCon_le_trans | ].
        now bsimpl.
      * eapply convneu_Ltrans ; [eassumption | ].
        eapply convne_meta_conv.
        3: reflexivity.
        1: rewrite wk_snd.
        1: eapply convneu_wk ; tea.
        1: eapply convneu_Ltrans ; [eassumption | ].
        1: now eapply convneu_snd, convneu_conv.
        now bsimpl.
  }

  intros ???? h.
  pose proof (lrefl h); pose proof (urefl h).  
  unshelve refine (let Rn :[Γ ||-Σ n : A | ΣA]< wl > := _ in _).
    1: eapply funred; tea; now eapply lrefl.
    unshelve refine (let Rn' :[Γ ||-Σ n' : A | ΣA]< wl > := _ in _).
    1: eapply funred; tea; now eapply urefl.
    assert (forall Δ wl' (ρ : Δ ≤ Γ) (f : wl' ≤ε wl) (h : [ |- Δ]< wl' >),
      [Δ |- cod[tFst n⟨ρ⟩ .: ρ >> tRel] ≅ cod[tFst n'⟨ρ⟩ .: ρ >> tRel]]< wl' >).
    { intros ; eapply convty_over_tree.
      intros wl'' Ho ; eapply escapeEq; unshelve eapply (PolyRed.posExt ΣA).
      2,3,5: eassumption.
      + eapply Rn.
      + eapply Rn'.
      + eapply hconv_fst.
        1,2: now eapply ty_Ltrans.
        now eapply convneu_Ltrans.
    }
    split; tea; unshelve eexists Rn Rn' _.
    + intros ; now eapply leaf.
    + cbn.
      eapply hconv ; tea.
    + cbn. intros. eapply hconv_fst.
      1,2: now eapply ty_Ltrans.
      now eapply convneu_Ltrans.
    + intros; cbn; eapply ihcod.
      all: pose proof (Hyp := over_tree_le Ho).
      1,2: eapply ty_Ltrans ; [eassumption | ].
      3: eapply convneu_Ltrans ; [eassumption | ].
      all: rewrite wk_fst; rewrite !wk_snd.
      2: eapply ty_conv; [| symmetry ; eapply H20 ; eauto].
      2: rewrite wk_fst.
      all: rewrite <- subst_ren_subst_mixed.
      1,2: eapply ty_wk ; tea.
      1,2: eapply ty_Ltrans ; [eassumption | ].
      1,2: now eapply ty_snd, ty_conv.
      * eapply convneu_wk; tea.
        eapply convneu_snd, convneu_Ltrans ; [eassumption | ].
        now eapply convneu_conv.
Qed.




Lemma complete_Nat {l wl Γ A} (NA : [Γ ||-Nat A]< wl >) : complete (LRNat_ l NA).
Proof.
  split.
  - intros. 
    assert [Γ |- A ≅ tNat]< wl > by (destruct NA; gen_typing). 
    assert [Γ |- n : tNat]< wl > by now eapply ty_conv.
    split; econstructor.
    1,4,5: eapply redtmwf_refl; tea; now eapply ty_conv.
    2,4: do 2 constructor; tea.
    1,4: eapply convtm_convneu ; [now constructor|..].
    all: eapply convneu_conv; [|eassumption].
    all: first [assumption|now eapply lrefl].
Qed.

Lemma complete_Empty {l wl Γ A} (NA : [Γ ||-Empty A]< wl >) : complete (LREmpty_ l NA).
Proof.
  split.
  - intros. 
    assert [Γ |- A ≅ tEmpty]< wl > by (destruct NA; gen_typing). 
    assert [Γ |- n : tEmpty]< wl > by now eapply ty_conv.
    split; econstructor.
    1,4,5: eapply redtmwf_refl; tea; now eapply ty_conv.
    2,4: do 2 constructor; tea.
    1,4: eapply convtm_convneu ; [now constructor|..].
    all: eapply convneu_conv; [|eassumption].
    all: try first [assumption|now eapply lrefl].
Qed.

Lemma complete_Bool {l wl Γ A} (NA : [Γ ||-Bool A]< wl >) : complete (LRBool_ l NA).
Proof.
  split.
  - intros. 
    assert [Γ |- A ≅ tBool]< wl > by (destruct NA; gen_typing). 
    assert [Γ |- n : tBool]< wl > by now eapply ty_conv.
    split; econstructor.
    1,4,5: eapply redtmwf_refl; tea; now eapply ty_conv.
    2,4: do 2 constructor; tea.
    1,4: eapply convtm_convneu ; [now constructor|..].
    all: eapply convneu_conv; [|eassumption].
    all: try first [assumption|now eapply lrefl].
Qed.

Lemma complete_Id {l wl Γ A} (IA : [Γ ||-Id<l> A]< wl >) :
  complete (LRId' IA).
Proof.
  split; intros.
  assert [Γ |- A ≅ IA.(IdRedTy.outTy)]< wl > by (destruct IA; unfold IdRedTy.outTy; cbn; gen_typing).
  assert [Γ |- n : IA.(IdRedTy.outTy)]< wl > by now eapply ty_conv.
  split; econstructor.
  1,4,5: eapply redtmwf_refl; tea; now eapply ty_conv.
  2,4: do 2 constructor; tea.
  1,4: eapply convtm_convneu ; [now constructor|..].
  all: eapply convneu_conv; tea; now eapply lrefl.
Qed.

Lemma completeness {l wl Γ A} (RA : [Γ ||-<l> A]< wl >) : complete RA.
Proof.
revert l wl Γ A RA; eapply LR_rect_TyUr; cbn; intros.
- now apply complete_U.
- now apply complete_ne.
- now apply complete_Pi.
- now apply complete_Nat.
- now apply complete_Bool.
- now apply complete_Empty.
- now apply complete_Sig.
- now apply complete_Id.
Qed.

Lemma neuTerm {l wl Γ A} (RA : [Γ ||-<l> A]< wl >) {n} :
  [Γ |- n : A]< wl > ->
  [Γ |- n ~ n : A]< wl > ->
  [Γ ||-<l> n : A | RA]< wl >.
Proof.
  intros.  now eapply completeness.
Qed.

Lemma neuTermEq {l wl Γ A} (RA : [Γ ||-<l> A]< wl >) {n n'} :
  [Γ |- n : A]< wl > ->
  [Γ |- n' : A]< wl > ->
  [Γ |- n ~ n' : A]< wl > ->
  [Γ ||-<l> n ≅ n' : A| RA]< wl >.
Proof.
  intros; now eapply completeness.
Qed.

Lemma var0conv {l wl Γ A A'} (RA : [Γ ,, A ||-<l> A']< wl >) :
  [Γ,, A |- A⟨↑⟩ ≅ A']< wl > ->
  [Γ |- A]< wl > ->
  [Γ ,, A ||-<l> tRel 0 : A' | RA]< wl >.
Proof.
  apply complete_var0 ; now eapply completeness.
Qed.

Lemma var0 {l wl Γ A A'} (RA : [Γ ,, A ||-<l> A']< wl >) :
  A⟨↑⟩ = A' ->
  [Γ |- A]< wl > ->
  [Γ ,, A ||-<l> tRel 0 : A' | RA]< wl >.
Proof.
  intros eq.
  apply var0conv.
  rewrite eq.
  unshelve eapply escapeEq; tea.
  eapply reflLRTyEq.
Qed.

End Neutral.
