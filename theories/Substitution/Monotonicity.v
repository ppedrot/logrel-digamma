From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations LContexts Context NormalForms Weakening GenericTyping LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Irrelevance Reflexivity Transitivity Monotonicity.
From LogRel.Substitution Require Import Irrelevance.


Set Universe Polymorphism.

Section Monotonicity.
Context `{GenericTypingProperties}.

Lemma VPack_Ltrans {wl wl' Γ} : (wl' ≤ε wl) -> VPack wl Γ -> VPack wl' Γ.
Proof.
  intros f [rel Hrel] ; unshelve econstructor.
  - intros ? wl'' σ f' wfd ; unshelve eapply rel.
    3,5: eassumption.
    now eapply wfLCon_le_trans.
  - intros ? wl'' ?? f' ? Hyp ; cbn in * ; unshelve eapply (Hrel _ _ σ σ' _ _).
    5: eassumption.
Defined.

Lemma Validity_Ltrans {l Γ A wl wl' P} (f: wl' ≤ε wl) :
  [ P | Γ ||-v< l > A ]< wl > -> [ VPack_Ltrans f P | Γ ||-v< l > A ]< wl' >.
Proof.
  intros [red eq] ; unshelve econstructor.
  - intros ? wl'' ? f' ? Hyp.
    unshelve eapply red.
    3: eassumption.
  - intros ? wl'' ?? f' ????.
    cbn in *.
    now unshelve eapply eq.
Defined.    
(*
Lemma VPackAd_Ltrans wl wl' Γ VP
  (f : wl' ≤ε wl) :
  VPackAdequate (Γ := Γ) (wl := wl) VR VP ->
  VPackAdequate (Γ := Γ) (wl := wl') VR (VPack_Ltrans f VP).
Proof.
  destruct VP as [red ext] ; cbn in *.
  induction 1.
  - constructor 1.
    + intros ? wl'' ? f' ? ; cbn in * ; now eapply Hsub.
    + intros ? wl'' ?? f' ?? ; cbn in * ; now eapply Hext.
  - unshelve econstructor 2 ; cbn in *.
    1: eassumption.
    1: eapply VPack_Ltrans ; eauto.
    1: eapply Validity_Ltrans ; now eauto.
    all: cbn.
    2: eassumption.
    + intros ? wl'' ? f' ?.
      rewrite Hsub.
    
    6: intros ; eapply Hext. eassumption.
    

    intros HAd ? wl'' ? f' ?.
  cbn in *.
  destruct VP as [rel Hrel] ; cbn in *.
  set (X:= HAd Δ wl'' σ (f' •ε f) wfΔ).
  Set Printing Implicit.
  induction X.
  - now econstructor.
  - cbn in *.
    change f0 with (f' •ε f).
    unshelve econstructor ; cbn in *.
    2: now eapply VPack_Ltrans.
    4: eassumption.
    2: now eapply Validity_Ltrans.
    + intros ; cbn.
      erewrite Hsub.
      destruct  VΓ ; cbn.
      unfold VPack_Ltrans.
      f_equal.
      
    + intros ? wl'' ? f' ? Hyp ; cbn in *.
      unshelve econstructor.
      * now eapply Himpsub.
      * Wirrelevance0 ; [reflexivity | ].
  unshelve eapply Himpsub ; [ | | eassumption].
  + intros ? wl'' ? f' ? Hyp ; cbn in *.
    eapply Hrevsub.
    destruct Hyp.
    unshelve econstructor.
    eassumption.
    cbn in *.
    Wirrelevance.
  + cbn in * ; intros ? wl'' ?? f'' ? Hyp Hyp2.
    unshelve econstructor.
    * now eapply Himpeq.
    * Wirrelevance0 ; [reflexivity | ].
  now eapply Himpeq.
  + cbn in * ; intros ? wl'' ?? f'' ? Hyp Hyp2.
    eapply Hreveq.
    destruct Hyp2 ; unshelve econstructor.
    * assumption.
    * Wirrelevance.
Defined.
*)
Lemma WfC_Ltrans {wl wl' Γ} : (wl' ≤ε wl) ->
  [ VR | ||-v Γ ]< wl > ->
  [ VR | ||-v Γ ]< wl' >.
Proof.
  intros f [rel Hrel] ; unshelve econstructor.
  - now eapply VPack_Ltrans.
  - cbn in *.
    destruct rel as [vs eqs] ; cbn in *.
    induction Hrel.
    + unshelve econstructor.
      * intros ; now rewrite Hsub.
      * intros ; now rewrite Hext. 
    + unshelve econstructor 2.
      1: eassumption.
      1: now eapply VPack_Ltrans.
      1: now eapply Validity_Ltrans.
      all: cbn in *.
      2: eassumption.
      * intros ; now erewrite Hsub.
      * intros ; cbn.
        erewrite Hext.
        assert ((eq_ind_r
          (fun T : Type =>
           T =
           snocValidSubst wl' Γ (VPack_Ltrans f VΓ) A l (Validity_Ltrans f VA) Δ
             wl'0 σ f0 wfΔ) eq_refl (Hsub Δ wl'0 σ (f0 •ε f) wfΔ)) =
                  (Hsub Δ wl'0 σ (f0 •ε f) wfΔ)).
        { generalize ((Hsub Δ wl'0 σ (f0 •ε f) wfΔ)).
          intros e.
          refine (match e with
                  | eq_refl => eq_refl
                  end).
        }
        rewrite <- H10 at 1.
        reflexivity.
Defined.        

Lemma Validity_Ltrans'
  {l Γ A wl wl'} (f: wl' ≤ε wl)
  (VΓ : [VR (wl := wl) | ||-v Γ]< wl >) :
  [ Γ ||-v< l > A | VΓ ]< wl > ->
  [ WfC_Ltrans f VΓ | Γ ||-v< l > A ]< wl' >.
Proof.
  intros [red ext] ; unshelve econstructor.
  - intros ? wl'' ? f' ? Hyp.
    unshelve eapply red.
    3: eassumption.
  - intros ? wl'' ?? f' ????.
    cbn in *.
    now unshelve eapply ext.
Defined.

Arguments Validity_Ltrans [_ _ _ _ _ _ ].

Lemma TmValidity_Ltrans 
  {l Γ t A wl wl'}
  (f: wl' ≤ε wl)
  (VΓ : [VR (wl := wl) | ||-v Γ]< wl >)
  (VA : [Γ ||-v<l> A |VΓ]< wl >) :
  [ Γ ||-v< l > t : A | VΓ | VA ]< wl > ->
  [ Γ ||-v< l > t : A | _ | Validity_Ltrans' f _ VA ]< wl' >.
Proof.
  intros [Ht Htext].
  unshelve econstructor.
  - intros ? wl'' ? f'' ??.
    Wirrelevance0 ; [reflexivity | unshelve eapply Ht ].
    3: eassumption.
  - intros ? wl'' ?? f'' ?? Hs' Heq.
    Wirrelevance0 ; [ reflexivity | eapply Htext].
    + eassumption.
    + eassumption.
Qed.


Lemma TyEqValidity_Ltrans 
  {l Γ A B wl wl'}
  (f: wl' ≤ε wl)
  (VΓ : [VR (wl := wl) | ||-v Γ]< wl >)
  (VA : [Γ ||-v<l> A | VΓ]< wl >) :
  [ Γ ||-v< l > A ≅ B | VΓ | VA ]< wl > ->
  [ Γ ||-v< l > A ≅ B | _ | Validity_Ltrans' f _ VA ]< wl' >.
Proof.
  intros [HB].
  unshelve econstructor.
  intros ? wl'' ? f'' ??.
  Wirrelevance0 ; [reflexivity | unshelve eapply HB ].
  3: eassumption.
Qed.

Lemma TmEqValidity_Ltrans 
  {l Γ t u A wl wl'}
  (f: wl' ≤ε wl)
  (VΓ : [VR (wl := wl) | ||-v Γ]< wl >)
  (VA : [Γ ||-v<l> A | VΓ]< wl >) :
  [ Γ ||-v< l > t ≅ u : A | VΓ | VA ]< wl > ->
  [ Γ ||-v< l > t ≅ u : A | _ | Validity_Ltrans' f _ VA ]< wl' >.
Proof.
  intros [Htu].
  unshelve econstructor.
  intros ? wl'' ? f'' ??.
  Wirrelevance0 ; [reflexivity | unshelve eapply Htu ].
  3: eassumption.
Qed.

Lemma subst_Ltrans {Γ Δ σ wl wl' wl''}
  {f: wl' ≤ε wl}
  (f': wl'' ≤ε wl')
  {VΓ : [||-v Γ ]< wl >}
  {wfΔ : [ |-[ ta ] Δ ]< wl' >}
  (wfΔ' : [ |-[ ta ] Δ ]< wl'' >) : 
  [VΓ | Δ ||-v σ : Γ | wfΔ | f ]< wl > ->
  [VΓ | Δ ||-v σ : Γ | wfΔ' | (f' •ε f) ]< wl >.
Proof.
  revert σ.
  pattern Γ, VΓ.
  eapply validity_rect.
  - intros * ; cbn. do 2 rewrite Hsub ; trivial.
  - intros * IH σ ; cbn ; do 2 rewrite Hsub.
    intros [red eq] ; unshelve econstructor.
    + eapply IH ; eassumption.
    + cbn in * ; Wirrelevance0 ; [reflexivity | ].
      eapply WTm_Ltrans ; eassumption.
      Unshelve.
      eassumption.
Defined.

Lemma subst_Ltrans' {Γ Δ σ wl wl' wl''}
  {f: wl' ≤ε wl}
  (f': wl'' ≤ε wl')
  {VΓ : [||-v Γ ]< wl >}
  (wfΔ' : [ |-[ ta ] Δ ]< wl'' >) : 
  [VΓ | Δ ||-v σ : Γ | wfΔ' | (f' •ε f) ]< wl > ->
  [VPack_Ltrans f VΓ | Δ ||-v σ : Γ | wfΔ' | f' ]< wl' >.
Proof.
  revert σ.
  pattern Γ, VΓ.
  eapply validity_rect.
  - intros * ; cbn. rewrite Hsub ; trivial.
  - intros * IH σ ; cbn ; rewrite Hsub.
    intros [red eq] ; unshelve econstructor.
    + eapply IH ; eassumption.
    + cbn in * ; Wirrelevance0 ; [reflexivity | ].
      eassumption.
Defined.

Lemma eqsubst_Ltrans {Γ Δ σ σ' wl wl' wl''}
  (f: wl' ≤ε wl)
  (f': wl'' ≤ε wl')
  (VΓ : [||-v Γ ]< wl >)
  (wfΔ : [ |-[ ta ] Δ ]< wl' >)
  (wfΔ' : [ |-[ ta ] Δ ]< wl'' >)
  (Vσ: [VΓ | Δ ||-v σ : Γ | wfΔ | f ]< wl >) :
  [VΓ | Δ ||-v σ ≅ σ' : Γ | wfΔ | Vσ | f ]< wl > ->
  [VΓ | Δ ||-v σ ≅ σ' : Γ | wfΔ' | subst_Ltrans f' wfΔ' Vσ | (f' •ε f) ]< wl >.
Proof.
  revert σ σ' Vσ.
  pattern Γ, VΓ.
  eapply validity_rect.
  - intros * ? ; cbn in *.
    erewrite (Hext Δ wl'' σ σ' (f' •ε f) wfΔ' _) ; now constructor.
  - intros * IH σ σ' Vσ Vσσ'.
    cbn.
    erewrite (Hext Δ wl'' σ σ' (f' •ε f) wfΔ').
    econstructor.
    + cbn in * ; eapply irrelevanceSubstEq.      
      eapply IH.
      rewrite Hext in Vσσ' ; destruct Vσσ' ; eassumption.
    + cbn in * ; Wirrelevance0 ; [reflexivity | ].
      rewrite Hext in Vσσ' ; destruct Vσσ'.
      unshelve eapply WTmEq_Ltrans ; [ | eassumption | | eassumption].
Qed.

Lemma eqsubst_Ltrans' {Γ Δ σ σ' wl wl' wl''}
  (f: wl' ≤ε wl)
  (f': wl'' ≤ε wl')
  (VΓ : [||-v Γ ]< wl >)
  (wfΔ : [ |-[ ta ] Δ ]< wl' >)
  (wfΔ' : [ |-[ ta ] Δ ]< wl'' >)
  (Vσ: [VΓ | Δ ||-v σ : Γ | wfΔ' | (f' •ε f) ]< wl >) :
  [VΓ | Δ ||-v σ ≅ σ' : Γ | wfΔ' | Vσ | (f' •ε f) ]< wl > ->
  [VPack_Ltrans f VΓ | Δ ||-v σ ≅ σ' : Γ | wfΔ' | subst_Ltrans' f' wfΔ' Vσ | f' ]< wl' >.
Proof.
  revert σ σ' Vσ.
  pattern Γ, VΓ.
  eapply validity_rect.
  - intros * ? ; cbn in *.
    erewrite (Hext Δ wl'' σ σ' (f' •ε f) wfΔ' _) ; now constructor.
  - intros * IH σ σ' Vσ Vσσ'.
    cbn.
    erewrite (Hext Δ wl'' σ σ' (f' •ε f) wfΔ').
    econstructor.
    + cbn in * ; eapply irrelevanceSubstEq.      
      eapply IH.
      rewrite Hext in Vσσ' ; destruct Vσσ' ; eassumption.
    + cbn in * ; Wirrelevance0 ; [reflexivity | ].
      rewrite Hext in Vσσ' ; destruct Vσσ'.
      eassumption.
Qed.
      
End Monotonicity.
