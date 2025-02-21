From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations LContexts Context NormalForms Weakening GenericTyping Monad LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Induction Irrelevance Escape Reflexivity Weakening Neutral Monotonicity Transitivity NormalRed.
From LogRel.Substitution Require Import Irrelevance Properties Conversion.

Set Universe Polymorphism.

Section SingleSubst.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.

Lemma singleSubstComm G t σ : G[t..][σ] = G[t[σ] .: σ].
Proof. now asimpl. Qed.


Lemma substS {wl Γ F G t l} {VΓ : [||-v Γ]< wl >}
  {VF : [Γ ||-v<l> F | VΓ]< wl >}
  (VG : [Γ,, F ||-v<l> G | validSnoc VΓ VF]< wl >)
  (Vt : [Γ ||-v<l> t : F | VΓ | VF]< wl >) :
  [Γ ||-v<l> G[t..] | VΓ]< wl >.
Proof.
  opector; intros; rewrite singleSubstComm.
  - unshelve eapply validTy. 3,4:  tea.
    now eapply consSubstSvalid.
  - irrelevance0. 1: symmetry; apply singleSubstComm.
    eapply validTyExt.
    1: eapply consSubstS; now  eapply validTm.
    now eapply consSubstSEqvalid.
    Unshelve. all: eassumption.
Qed.

Lemma substSEq {wl Γ F F' G G' t t' l} {VΓ : [||-v Γ]< wl >} 
  {VF : [Γ ||-v<l> F | VΓ]< wl >}
  {VF' : [Γ ||-v<l> F' | VΓ]< wl >}
  (VFF' : [Γ ||-v<l> F ≅ F' | VΓ | VF]< wl >)
  (VΓF := validSnoc VΓ VF)
  (VΓF' := validSnoc VΓ VF')
  {VG : [Γ,, F ||-v<l> G | VΓF]< wl >}
  (VG' : [Γ,, F' ||-v<l> G' | VΓF']< wl >)
  (VGG' : [Γ ,, F ||-v<l> G ≅ G' | VΓF | VG]< wl >)
  (Vt : [Γ ||-v<l> t : F | VΓ | VF]< wl >)
  (Vt' : [Γ ||-v<l> t' : F' | VΓ | VF']< wl >)
  (Vtt' : [Γ ||-v<l> t ≅ t' : F | VΓ | VF]< wl >)
  (VGt := substS VG Vt) :
  [Γ ||-v<l> G[t..] ≅ G'[t'..] | VΓ | VGt]< wl >.
Proof.
  constructor; intros.
  assert (VtF' : [Γ ||-v<l> t : F' | VΓ | VF']< wl >) by now eapply conv.
  pose proof (consSubstSvalid Vσ Vt').
  pose proof (consSubstSvalid Vσ VtF').
  rewrite singleSubstComm; irrelevance0.
  1: symmetry; apply singleSubstComm.
  eapply transEq.
  - unshelve now eapply validTyEq.
    2: now eapply consSubstSvalid.
  - eapply validTyExt; tea.
    unshelve econstructor.
    1: eapply reflSubst.
    eapply validTmEq.
    now eapply convEq.
    Unshelve. all: tea.
Qed.




Lemma substSTm {wl Γ F G t f l} {VΓ : [||-v Γ]< wl >}
  {VF : [Γ ||-v<l> F | VΓ]< wl >}
  (VΓF := validSnoc VΓ VF)
  {VG : [Γ,, F ||-v<l> G | VΓF]< wl >}
  (Vt : [Γ ||-v<l> t : F | VΓ | VF]< wl >) 
  (Vf : [Γ ,, F ||-v<l> f : G | VΓF | VG]< wl >)
  (VGt := substS VG Vt) :
  [Γ ||-v<l> f[t..] : G[t..] | VΓ | VGt]< wl >.
Proof.
  constructor; intros; rewrite !singleSubstComm; irrelevance0. 
  1,3: symmetry; apply singleSubstComm.
  - now eapply validTm.
  - eapply validTmExt; tea.
    1: now apply consSubstSvalid.
    now apply consSubstSEqvalid.
    Unshelve. 1,3: eassumption.
    now apply consSubstSvalid.
Qed.

Lemma substSTmEq {wl Γ F F' G G' t t' f f' l} (VΓ : [||-v Γ]< wl >) 
  (VF : [Γ ||-v<l> F | VΓ]< wl >)
  (VF' : [Γ ||-v<l> F' | VΓ]< wl >)
  (VFF' : [Γ ||-v<l> F ≅ F' | VΓ | VF]< wl >)
  (VΓF := validSnoc VΓ VF)
  (VΓF' := validSnoc VΓ VF')
  (VG : [Γ,, F ||-v<l> G | VΓF]< wl >)
  (VG' : [Γ,, F' ||-v<l> G' | VΓF']< wl >)
  (VGG' : [Γ ,, F ||-v<l> G ≅ G' | VΓF | VG]< wl >)
  (Vt : [Γ ||-v<l> t : F | VΓ | VF]< wl >)
  (Vt' : [Γ ||-v<l> t' : F' | VΓ | VF']< wl >)
  (Vtt' : [Γ ||-v<l> t ≅ t' : F | VΓ | VF]< wl >) 
  (Vf : [Γ ,, F ||-v<l> f : G | VΓF | VG]< wl >)
  (Vf' : [Γ ,, F' ||-v<l> f' : G' | VΓF' | VG']< wl >)
  (Vff' : [Γ ,, F ||-v<l> f ≅ f' : G | VΓF | VG]< wl >) :
  [Γ ||-v<l> f[t..] ≅ f'[t'..] : G[t..] | VΓ | substS VG Vt]< wl >.
Proof.
  constructor; intros; rewrite !singleSubstComm; irrelevance0. 
  1: symmetry; apply singleSubstComm.
  eapply transEqTerm.
  + unshelve now eapply validTmEq.
    2: now eapply consSubstSvalid.
  + assert (Vσt : [Δ ||-v (t[σ] .: σ) : _ | VΓF' | wfΔ]< wl >)
     by (eapply consSubstSvalid; tea; now eapply conv).
    assert (Vσt' : [Δ ||-v (t'[σ] .: σ) : _ | VΓF' | wfΔ]< wl >)
     by (eapply consSubstSvalid; tea; now eapply conv).
    assert (Vσtσt' : [Δ ||-v (t[σ] .: σ) ≅ (t'[σ] .: σ) : _ | VΓF' | wfΔ | Vσt]< wl >).
    1:{
      constructor.
      - bsimpl; epose (reflSubst _  _ Vσ); now eapply irrelevanceSubstEq.
      - bsimpl; eapply validTmEq. now eapply convEq.
    }
    eapply LRTmEqRedConv.
    2: eapply (validTmExt Vf' _ Vσt Vσt' Vσtσt').
    eapply LRTyEqSym. now eapply validTyEq.
    Unshelve. 2: now eapply consSubstSvalid.
Qed.

(* Skipping a series of lemmas on single substitution of a weakened term *)


Lemma liftSubstComm G t σ : G[t]⇑[σ] = G[t[σ] .: ↑ >> σ].
Proof. now bsimpl. Qed.


Lemma substLiftS {wl Γ F G t l} (VΓ : [||-v Γ]< wl >)
  (VF : [Γ ||-v<l> F | VΓ]< wl >)
  (VΓF := validSnoc VΓ VF)
  (VG : [Γ,, F ||-v<l> G | VΓF]< wl >)
  (VF' := wk1ValidTy VF VF)
  (Vt : [Γ,, F ||-v<l> t : F⟨@wk1 Γ F⟩ | VΓF | VF']< wl >) :
  [Γ ,, F ||-v<l> G[t]⇑ | VΓF]< wl >.
Proof.
  assert (h : forall Δ σ (wfΔ: [|- Δ]< wl >)
    (vσ: [VΓF | Δ ||-v σ : Γ,, F | wfΔ]< wl >),
    [VΓF | Δ ||-v (t[σ] .: ↑ >> σ) : _ | wfΔ ]< wl >).
  1:{
    unshelve econstructor.
    + asimpl; now eapply validTail.
    + cbn. irrelevance0.
      2: now eapply validTm.
      now bsimpl.
  }
  opector; intros; rewrite liftSubstComm.
  - unshelve eapply validTy; cycle 2; tea; now eapply h.
  - irrelevance0.
    2: unshelve eapply validTyExt.
    8: now eapply h.
    4: now eapply (h _ _  _ vσ).
    1: now bsimpl.
    1: tea.
    constructor.
    + asimpl; eapply irrelevanceSubstEq; now eapply eqTail.
    + cbn. irrelevance0.
      2: now eapply validTmExt.
      now bsimpl.
      Unshelve. all:tea.
Qed.

Lemma substLiftSEq {wl Γ F G G' t l} (VΓ : [||-v Γ]< wl >)
  (VF : [Γ ||-v<l> F | VΓ]< wl >)
  (VΓF := validSnoc VΓ VF)
  (VG : [Γ,, F ||-v<l> G | VΓF]< wl >)
  (VG' : [Γ,, F ||-v<l> G' | VΓF]< wl >)
  (VGeq : [Γ,, F ||-v<l> G ≅ G' | VΓF | VG]< wl >)
  (VF' := wk1ValidTy VF VF)
  (Vt : [Γ,, F ||-v<l> t : F⟨@wk1 Γ F⟩ | VΓF | VF']< wl >) :
  [Γ ,, F ||-v<l> G[t]⇑ ≅ G'[t]⇑ | VΓF | substLiftS _ VF VG Vt]< wl >.
Proof.
  constructor; intros; rewrite liftSubstComm.
  assert (Vσt : [Δ ||-v (t[σ] .: ↑ >> σ) : _ | VΓF | wfΔ ]< wl >). 1:{
    unshelve econstructor.
    + bsimpl. now eapply validTail.
    + bsimpl. instValid Vσ. irrelevance.
  }
  instValid Vσt. irrelevance.
Qed.

Lemma substLiftSEq' {wl Γ F G G' t t' l} (VΓ : [||-v Γ]< wl >)
  (VF : [Γ ||-v<l> F | VΓ]< wl >)
  (VΓF := validSnoc VΓ VF)
  (VG : [Γ,, F ||-v<l> G | VΓF]< wl >)
  (VG' : [Γ,, F ||-v<l> G' | VΓF]< wl >)
  (VGeq : [Γ,, F ||-v<l> G ≅ G' | VΓF | VG]< wl >)
  (VF' := wk1ValidTy VF VF)
  (Vt : [Γ,, F ||-v<l> t : F⟨@wk1 Γ F⟩ | VΓF | VF']< wl >) 
  (Vt' : [Γ,, F ||-v<l> t' : F⟨@wk1 Γ F⟩ | VΓF | VF']< wl >)
  (Vtt' : [Γ,, F ||-v<l> t ≅ t' : F⟨@wk1 Γ F⟩ | VΓF | VF']< wl >) :
  [Γ ,, F ||-v<l> G[t]⇑ ≅ G'[t']⇑ | VΓF | substLiftS _ VF VG Vt]< wl >.
Proof.
  eapply transValidTyEq.
  1: eapply substLiftSEq; [| exact VGeq]; tea.
  constructor; intros; irrelevance0; rewrite liftSubstComm ; [reflexivity|].
  instValid Vσ.
  eapply validTyExt.
  + unshelve eapply consSubstS.
    6: now eapply validTail.
    3: exact VF. 
    irrelevance.
  + unshelve eapply consSubstSEq'.
    1: now eapply validTail.
    1,3: irrelevance.
    eapply reflSubst.
    Unshelve. 3: tea. now eapply substLiftS.
Qed.


Lemma singleSubstPoly {wl Γ F G t l lF}
  (RFG : PolyRed wl Γ l F G)
  {RF : [Γ ||-<lF> F]< wl >}
  (Rt : [Γ ||-<lF> t : F | RF]< wl >) :
  W[Γ ||-<l> G[t..]]< wl >.
Proof.
  replace G[t..] with G[t .: wk_id (Γ:=Γ) >> tRel] by now bsimpl.
  econstructor ; intros wl' Hover.
  unshelve eapply (PolyRed.posRed RFG).
  5: eassumption.
  2: escape; now gen_typing.
  1: now eapply wfLCon_le_id.
  irrelevance0 ; [ | eassumption].
  now bsimpl.
Qed.

Lemma singleSubstΠ1 {wl Γ F G t l lF}
  (ΠFG : [Γ ||-<l> tProd F G]< wl >)
  {RF : [Γ ||-<lF> F]< wl >}
  (Rt : [Γ ||-<lF> t : F | RF]< wl >) :
  W[Γ ||-<l> G[t..]]< wl >.
Proof.
  eapply singleSubstPoly; tea.
  eapply (ParamRedTy.polyRed (normRedΠ0 (invLRΠ ΠFG))).
Qed.

Lemma singleSubstΣ1 {wl Γ F G t l lF}
  (ΠFG : [Γ ||-<l> tSig F G]< wl >)
  {RF : [Γ ||-<lF> F]< wl >}
  (Rt : [Γ ||-<lF> t : F | RF]< wl >) :
  W[Γ ||-<l> G[t..]]< wl >.
Proof.
  eapply singleSubstPoly; tea.
  eapply (ParamRedTy.polyRed (normRedΣ0 (invLRΣ ΠFG))).
Qed.

Lemma singleSubstPoly2 {wl Γ F F' G G' t t' l lF lF'}
  {RFG : PolyRed wl Γ l F G}
  (RFGeq : PolyRedEq RFG F' G')
  {RF : [Γ ||-<lF> F]< wl >}
  {RF' : [Γ ||-<lF'> F']< wl >}
  (Rt : [Γ ||-<lF> t : F | RF]< wl >) 
  (Rt' : [Γ ||-<lF'> t' : F' | RF']< wl >) 
  (Rteq : [Γ ||-<lF> t ≅ t' : F | RF]< wl >)
  (RGt : W[Γ ||-<lF> G[t..]]< wl >)
  (RGt' : W[Γ ||-<lF'> G'[t'..]]< wl >) :
  W[Γ ||-<lF> G[t..] ≅ G'[t'..] | RGt ]< wl >.
Proof.
  assert (wfΓ : [|-Γ]< wl >) by (escape ; gen_typing).
  assert [Γ ||-<l> t' : F⟨wk_id (Γ:=Γ)⟩ | PolyRed.shpRed RFG wk_id (wfLCon_le_id _) wfΓ]< wl >.
  {
    eapply LRTmRedConv; tea.
    eapply LRTyEqSym. 
    replace F' with F'⟨wk_id (Γ := Γ)⟩ by now bsimpl.
    eapply (PolyRedEq.shpRed RFGeq).
  }
  eapply WtransEq.
  2: (replace G'[t'..] with G'[t' .: wk_id (Γ:=Γ) >> tRel] by now bsimpl).
  2: econstructor ; intros ; irrelevance0 ; [ | unshelve eapply (PolyRedEq.posRed RFGeq wk_id)].
  econstructor ; intros ; irrelevance0 ; [ | unshelve eapply (PolyRed.posExt (a:= t) RFG wk_id)].
  1: now bsimpl.
  3,14: eassumption.
  1,10 : now eapply wfLCon_le_id.
  2,10: eapply over_tree_fusion_l, over_tree_fusion_l ; exact Hover'.
  5: eapply over_tree_fusion_l, over_tree_fusion_r ; exact Hover'.
  5: eapply over_tree_fusion_r, over_tree_fusion_l ; exact Hover'.
  7: eapply over_tree_fusion_r, over_tree_fusion_r ; exact Hover'.
  3,6: eassumption.
  1,2: irrelevance0 ; [ | eassumption] ; now bsimpl.
  reflexivity.
  Unshelve.
  1: now eapply wfLCon_le_id.
  1: assumption.
  3-5: now econstructor.
  2: econstructor ; intros.
  2: unshelve eapply (PolyRed.posRed RFG).
  4,5: eassumption.
Qed.

Lemma singleSubstΠ2 {wl Γ F F' G G' t t' l lF lF'}
  {ΠFG : [Γ ||-<l> tProd F G]< wl >}
  (ΠFGeq : [Γ ||-<l> tProd F G ≅ tProd F' G' | ΠFG]< wl >)
  {RF : [Γ ||-<lF> F]< wl >}
  {RF' : [Γ ||-<lF'> F']< wl >}
  (Rt : [Γ ||-<lF> t : F | RF]< wl >) 
  (Rt' : [Γ ||-<lF'> t' : F' | RF']< wl >) 
  (Rteq : [Γ ||-<lF> t ≅ t' : F | RF]< wl >)
  (RGt : W[Γ ||-<lF> G[t..]]< wl >)
  (RGt' : W[Γ ||-<lF'> G'[t'..]]< wl >) :
  W[Γ ||-<lF> G[t..] ≅ G'[t'..] | RGt ]< wl >.
Proof.
  eapply singleSubstPoly2; tea.
  pose (hΠ := normRedΠ0 (invLRΠ ΠFG)).
  assert (heq : [Γ ||-<l> tProd F G ≅ tProd F' G' | LRPi' hΠ]< wl >) by irrelevance.
  destruct heq as [?? red' ?? polyRed]; cbn in *.
  assert (h' :=redtywf_whnf red' whnf_tProd).
  symmetry in h'; injection h'; clear h'; intros ;  subst.
  exact polyRed.
Qed.

Lemma substSΠaux {wl Γ F G t l} 
  {VΓ : [||-v Γ]< wl >}
  {VF : [Γ ||-v<l> F | VΓ]< wl >}
  (VΠFG : [Γ ||-v<l> tProd F G | VΓ]< wl >)
  (Vt : [Γ ||-v<l> t : F | VΓ | VF]< wl >)
  (Δ : context) (σ : nat -> term) 
  (wfΔ : [ |-[ ta ] Δ]< wl >) (vσ : [VΓ | Δ ||-v σ : Γ | wfΔ]< wl >) :
  W[Δ ||-< l > G[up_term_term σ][t[σ]..]]< wl >.
Proof.
  eapply singleSubstΠ1.
  eapply (validTy VΠFG); tea.
  now eapply validTm.
  Unshelve. all: eassumption.
Qed.

Lemma singleSubstComm' G t σ : G[t..][σ] = G[up_term_term σ][t[σ]..].
Proof. now asimpl. Qed.

Lemma substSΠ {wl Γ F G t l} 
  {VΓ : [||-v Γ]< wl >}
  {VF : [Γ ||-v<l> F | VΓ]< wl >}
  (VΠFG : [Γ ||-v<l> tProd F G | VΓ]< wl >)
  (Vt : [Γ ||-v<l> t : F | VΓ | VF]< wl >) :
  W[Γ ||-v<l> G[t..] | VΓ]< wl >.
Proof.
  opector; intros.
  - rewrite singleSubstComm'; now eapply substSΠaux.
  - rewrite singleSubstComm'.
    irrelevance0. 1: symmetry; apply singleSubstComm'.
    eapply singleSubstΠ2.
    1: eapply (validTyExt VΠFG).
    1, 2: tea.
    1, 2: now eapply validTm.
    1: now eapply validTmExt.
    now eapply substSΠaux.
    Unshelve. all: tea.
    now eapply substSΠaux.
Qed.

Lemma substSΠeq {wl Γ F F' G G' t u l} 
  {VΓ : [||-v Γ]< wl >}
  {VF : [Γ ||-v<l> F | VΓ]< wl >}
  {VF' : [Γ ||-v<l> F' | VΓ]< wl >}
  {VΠFG : [Γ ||-v<l> tProd F G | VΓ]< wl >}
  (VΠFG' : [Γ ||-v<l> tProd F' G' | VΓ]< wl >)
  (VΠFGeq : [Γ ||-v<l> tProd F G ≅ tProd F' G' | VΓ | VΠFG]< wl >)
  (Vt : [Γ ||-v<l> t : F | VΓ | VF]< wl >) 
  (Vu : [Γ ||-v<l> u : F' | VΓ | VF']< wl >) 
  (Vtu : [Γ ||-v<l> t ≅ u : F | VΓ | VF]< wl >) 
  (VGt := substSΠ VΠFG Vt) :
  [Γ ||-v<l> G[t..] ≅ G'[u..] | VΓ | VGt]< wl >.
Proof.
  constructor; intros.
  rewrite singleSubstComm'.
  irrelevance0.
  1: symmetry; apply singleSubstComm'.
  eapply singleSubstΠ2.
  1: now eapply (validTyEq VΠFGeq).
  3: now eapply validTmEq.
  1,2: now eapply validTm.
  now eapply substSΠaux.
  Unshelve. all: tea.
  now eapply substSΠaux.
Qed.


End SingleSubst.
