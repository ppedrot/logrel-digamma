(** * LogRel.LogicalRelation.Irrelevance: symmetry and irrelevance of the logical relation. *)
Require Import PeanoNat.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Notations Utils BasicAst LContexts Context NormalForms Weakening GenericTyping Monad LogicalRelation DeclarativeInstance.
From LogRel.LogicalRelation Require Import Induction ShapeView Reflexivity Escape.

Set Universe Polymorphism.
Set Printing Universes.

(** We show a general version of irrelevance, saying that if A and A' are reducible (at levels logical relation levels lA, lA')
and A' is reducibly convertible to A, then the reducibility predicates they decode to are equivalent.
From this, both a simpler version of irrelevance and symmetry follow, by using reflexivity
in the right places. *)
(** Interestingly, we also show irrelevance with respect to universe levels, which is crucial
in later parts of the development, where this avoids creating spurious constraints on universe levels.*)


Section Irrelevances.
Context `{GenericTypingProperties}.


(** *** Equivalences of LRPack *)

Section EquivLRPack.
  Universe i i' v.

  Notation "A <≈> B" := (prod@{v v} (A -> B) (B -> A)) (at level 90).

  Definition equivLRPack {wl wl' Γ Γ' A A'} (P: LRPack@{i} wl Γ A) (P': LRPack@{i'} wl' Γ' A'):=
    and3@{v v v} 
      (forall B, [P | Γ ||- A ≅ B]< wl > <≈> [P' | Γ' ||- A' ≅ B]< wl' >)
      (forall t, [P | Γ ||- t : A]< wl > <≈> [P' | Γ' ||- t : A']< wl' >)
      (forall t u, [P | Γ ||- t ≅ u : A]< wl > <≈> [P' | Γ' ||- t ≅ u : A']< wl' >).
End EquivLRPack.

Lemma symLRPack@{i i' v} {wl wl' Γ Γ' A A'} {P: LRPack@{i} wl Γ A} {P': LRPack@{i'} wl' Γ' A'} :
    equivLRPack@{i i' v} P P' -> equivLRPack@{i' i v} P' P.
Proof.
  intros [eqT rTm eqTm]; constructor;split ;
    apply eqT + apply rTm + apply eqTm.
Qed.
  

Record equivPolyRed@{i j k l i' j' k' l' v}
  {wl Γ l l' shp shp' pos pos'}
  {PA : PolyRed@{i j k l} wl Γ l shp pos}
  {PA' : PolyRed@{i' j' k' l'} wl Γ l' shp' pos'} :=
  {
    eqvShp : forall {Δ wl'} (ρ : Δ ≤ Γ) (f : wl' ≤ε wl) (wfΔ : [  |- Δ]< wl' >),
      equivLRPack@{k k' v} (PolyRed.shpRed PA ρ f wfΔ) (PolyRed.shpRed PA' ρ f wfΔ) ;
    eqvTree : forall {Δ wl' a} (ρ : Δ ≤ Γ) (f : wl' ≤ε wl) (wfΔ : [  |- Δ]< wl' >)
                     (ha : [PolyRed.shpRed PA ρ f wfΔ| Δ ||- a : _]< wl' >)
                     (ha' : [PolyRed.shpRed PA' ρ f wfΔ | Δ ||- a : _]< wl' >),
      DTree wl' ;
    eqvPos : forall {Δ wl' a} (ρ : Δ ≤ Γ) (f : wl' ≤ε wl) (wfΔ : [  |- Δ]< wl' >)
          (ha : [PolyRed.shpRed PA ρ f wfΔ| Δ ||- a : _]< wl' >)
          (ha' : [PolyRed.shpRed PA' ρ f wfΔ | Δ ||- a : _]< wl' >),
    forall {wl''} (Ho : over_tree wl' wl'' (PolyRed.posTree PA ρ f wfΔ ha))
           (Ho' : over_tree wl' wl'' (PolyRed.posTree PA' ρ f wfΔ ha'))
           (Ho'' : over_tree wl' wl'' (eqvTree ρ f wfΔ ha ha')),
          equivLRPack@{k k' v} 
            (PolyRed.posRed PA ρ f wfΔ ha Ho)
            (PolyRed.posRed PA' ρ f wfΔ ha' Ho')
  }.

Arguments equivPolyRed : clear implicits.
Arguments equivPolyRed {_ _ _ _ _ _ _ _} _ _.

Lemma equivPolyRedSym@{i j k l i' j' k' l' v}
  {wl Γ l l' shp shp' pos pos'}
  {PA : PolyRed@{i j k l} wl Γ l shp pos}
  {PA' : PolyRed@{i' j' k' l'} wl Γ l' shp' pos'} :
  equivPolyRed@{i j k l i' j' k' l' v} PA PA' ->
  equivPolyRed@{i' j' k' l' i j k l v} PA' PA.
Proof.
  intros eqv; unshelve econstructor; intros.
  - eapply eqv.(eqvTree) ; eassumption.
  - eapply symLRPack; eapply eqv.(eqvShp).
  - eapply symLRPack; eapply eqv.(eqvPos); now eauto.
Qed.


(** *** Lemmas for product types *)

(** A difficulty is that we need to show the equivalence right away, rather than only an implication,
because of contravariance in the case of Π types. To save up work, we factor out some lemmas to
avoid having to basically duplicate their proofs. *)

Section ΠIrrelevanceLemmas.
Universe i j k l i' j' k' l' v.
Context {wl Γ lA A lA' A'} 
  (ΠA : ParamRedTy@{i j k l} tProd wl Γ lA A) 
  (ΠA' : ParamRedTy@{i' j' k' l'} tProd wl Γ lA' A')
  (RA := LRPi' ΠA)
  (RA' := LRPi' ΠA')
  (eqDom : [Γ |- ΠA.(ParamRedTy.dom) ≅ ΠA'.(ParamRedTy.dom)]< wl >)
  (eqPi : [Γ |- ΠA.(outTy) ≅ ΠA'.(outTy)]< wl >)
  (eqv : equivPolyRed ΠA ΠA').


Lemma ΠIrrelevanceTyEq B : [Γ ||-<lA> A ≅ B | RA]< wl > -> [Γ ||-<lA'> A' ≅ B | RA']< wl >.
Proof.
  intros  [????? []] ; cbn in *; econstructor ; [| | |unshelve econstructor].
  - now gen_typing.
  - transitivity (ParamRedTyPack.dom ΠA); [now symmetry|tea].
  - cbn; etransitivity; [|tea]; now symmetry.
  - intros.
    unshelve eapply (DTree_fusion _ _).
    + eapply DTree_fusion.
      * eapply (PolyRed.posTree ΠA) ; now eapply eqv.(eqvShp).
      * eapply eqv.(eqvTree) ; eauto. now eapply eqv.(eqvShp).
    + eapply posTree ; now eapply eqv.(eqvShp).
  - intros; now apply eqv.(eqvShp).
  - intros; cbn in *.
    unshelve eapply eqv.(eqvPos).
    now eapply eqv.(eqvShp).
    3: eapply posRed.
    + do 2 (eapply over_tree_fusion_l) ; eassumption.
    + eapply over_tree_fusion_r, over_tree_fusion_l ; eassumption.
    + eapply over_tree_fusion_r. eassumption.
Qed.


Lemma ΠIrrelevanceTm t : [Γ ||-<lA> t : A | RA]< wl > -> [Γ ||-<lA'> t : A' | RA']< wl >.
Proof.
  intros []; cbn in *; unshelve econstructor; tea.
  - intros ; eapply DTree_fusion.
    + eapply DTree_fusion.
      * eapply (PolyRed.posTree ΠA) ; now eapply eqv.(eqvShp).
      * eapply eqv.(eqvTree) ; eauto. now eapply eqv.(eqvShp).
    + eapply appTree ; now eapply eqv.(eqvShp).
  - intros ; eapply DTree_fusion.
    + eapply (PolyRed.posExtTree ΠA (a := a) (b := b)) ; now eapply eqv.(eqvShp).
    + eapply (eqTree _ a b) ; now eapply eqv.(eqvShp).
  - now eapply redtmwf_conv.
  - eapply (convtm_conv refl).
    now apply eqPi.
  - destruct isfun as [A'' t' funtree eqdom eqapp| ] ; cbn in *.
    + econstructor.
      * intros ; now eapply eqv.(eqvShp).
      * intros; unshelve eapply eqv.(eqvPos); [| | | eauto ] ; cbn in *.
        -- now apply eqv.(eqvShp).
        -- do 2 (eapply over_tree_fusion_l) ; exact Ho'.
        -- eapply over_tree_fusion_r, over_tree_fusion_l ; exact Ho'.
        -- eapply eqapp.
           eapply over_tree_fusion_r ; exact Ho'.
    + constructor; now eapply convneu_conv.
  - intros; unshelve eapply eqv.(eqvPos).
    now apply eqv.(eqvShp).
    3: eapply app.
    + do 2 (eapply over_tree_fusion_l) ; eassumption.
    + eapply over_tree_fusion_r, over_tree_fusion_l ; eassumption.
    + eapply over_tree_fusion_r ; eassumption.
  - intros; unshelve eapply eqv.(eqvPos), eq.
    all: try now eapply eqv.(eqvShp).
    3-5: eapply over_tree_fusion_r ; eassumption.
    + do 2 (eapply over_tree_fusion_l) ; eassumption.
    + eapply over_tree_fusion_r, over_tree_fusion_l ; eassumption.
Defined.

Lemma ΠIrrelevanceTmEq t u : [Γ ||-<lA> t ≅ u : A | RA]< wl > -> [Γ ||-<lA'> t ≅ u : A' | RA']< wl >.
Proof.
  intros [] ; cbn in *; unshelve econstructor.
  1,2: now eapply ΠIrrelevanceTm.
  - intros ; eapply DTree_fusion.
    + eapply DTree_fusion.
      * eapply (PolyRed.posTree ΠA) ; now eapply eqv.(eqvShp).
      * eapply eqv.(eqvTree) ; eauto ; now eapply eqv.(eqvShp).
    + eapply eqTree ; now eapply eqv.(eqvShp).
  - now eapply convtm_conv.
  - intros; unshelve eapply eqv.(eqvPos).
    now apply eqv.(eqvShp).
    3: apply eqApp.
    + do 2 (eapply over_tree_fusion_l) ; eassumption.
    + eapply over_tree_fusion_r, over_tree_fusion_l ; eassumption.
    + eapply over_tree_fusion_r ; eassumption.
Qed.

End ΠIrrelevanceLemmas.


Lemma ΠIrrelevanceLRPack@{i j k l i' j' k' l' v}
  {wl Γ lA A lA' A'} 
  (ΠA : ParamRedTy@{i j k l} tProd wl Γ lA A) 
  (ΠA' : ParamRedTy@{i' j' k' l'} tProd wl Γ lA' A')
  (RA := LRPi' ΠA)
  (RA' := LRPi' ΠA')
  (eqDom : [Γ |- ΠA.(ParamRedTy.dom) ≅ ΠA'.(ParamRedTy.dom)]< wl >)
  (eqPi : [Γ |- ΠA.(outTy) ≅ ΠA'.(outTy) ]< wl >)
  (eqv : equivPolyRed ΠA ΠA')
  : equivLRPack@{k k' v} RA RA'.
Proof.
  pose proof (equivPolyRedSym eqv).
  constructor.
  - split; now apply ΠIrrelevanceTyEq.
  - split; now apply ΠIrrelevanceTm.
  - split; now apply ΠIrrelevanceTmEq.
Qed.


(** *** Lemmas for dependent sum types *)

Section ΣIrrelevanceLemmas.
Universe i j k l i' j' k' l' v.
Context {wl Γ lA A lA' A'} 
  (ΣA : ParamRedTy@{i j k l} tSig wl Γ lA A) 
  (ΣA' : ParamRedTy@{i' j' k' l'} tSig wl Γ lA' A')
  (RA := LRSig' ΣA)
  (RA' := LRSig' ΣA')
  (eqDom : [Γ |- ΣA.(ParamRedTy.dom) ≅ ΣA'.(ParamRedTy.dom)]< wl >)
  (eqSig : [Γ |- ΣA.(outTy) ≅ ΣA'.(outTy)]< wl >)
  (eqv : equivPolyRed ΣA ΣA').

Lemma ΣIrrelevanceTyEq B : [Γ ||-<lA> A ≅ B | RA]< wl > -> [Γ ||-<lA'> A' ≅ B | RA']< wl >.
Proof.
  intros  [????? []] ; cbn in *; econstructor; [| | | unshelve econstructor].
  - now gen_typing.
  - transitivity (ParamRedTyPack.dom ΣA); [now symmetry|tea].
  - cbn; etransitivity; [|tea]; now symmetry.
  - intros ; eapply DTree_fusion.
    + eapply DTree_fusion.
      * eapply (PolyRed.posTree ΣA) ; now apply eqv.(eqvShp).
      * eapply eqv.(eqvTree) ; eauto ; now eapply eqv.(eqvShp).
    + eapply posTree ; now apply eqv.(eqvShp).
  - intros; now apply eqv.(eqvShp).
  - intros; cbn; unshelve eapply eqv.(eqvPos).
    3: eauto.
    now eapply eqv.(eqvShp).
    3: eapply posRed.
    + do 2 (eapply over_tree_fusion_l) ; eassumption.
    + eapply over_tree_fusion_r, over_tree_fusion_l ; eassumption.
    + eapply over_tree_fusion_r ; eassumption.
Qed.

Lemma ΣIrrelevanceTm t : [Γ ||-<lA> t : A | RA]< wl > -> [Γ ||-<lA'> t : A' | RA']< wl >.
Proof.
  intros []; cbn in *; unshelve econstructor.
  3: intros ; eapply DTree_fusion ; [ eapply DTree_fusion ; [unshelve eapply (PolyRed.posTree ΣA) | eapply eqv.(eqvTree) ; eauto] | unshelve eapply sndTree ].
  Unshelve.
  all: try eapply fstRed ; tea ; try now apply eqv.(eqvShp).
  - intros; unshelve eapply eqv.(eqvShp); now auto.
  - now eapply redtmwf_conv.
  - now eapply convtm_conv.
  - destruct ispair as [A₀ B₀ a b|n Hn] ; cbn in *.
    + unshelve econstructor.
      2,4: intros; now unshelve eapply eqv.(eqvShp).
      all: cbn in *.
      * intros ; eapply DTree_fusion ; [eapply DTree_fusion | ].
        -- eapply (PolyRed.posTree ΣA ρ f Hd).
           now eapply eqv.(eqvShp).
        -- eapply eqv.(eqvTree) ; [ | eauto].
           now eapply eqv.(eqvShp).
        -- eapply codTree.
           now eapply eqv.(eqvShp).
      * intros ; eapply DTree_fusion ; [eapply DTree_fusion | ].
        -- eapply (PolyRed.posTree ΣA).
           eapply rfst.
        -- eapply eqv.(eqvTree) ; [ now eapply rfst | ].
           now eapply eqv.(eqvShp), rfst.
        -- now eapply rsndTree ; eauto.
      * intros ; unshelve eapply eqv.(eqvPos) ; [ now eapply eqv.(eqvShp) | | | eapply rcod].
          all: cbn in *.
        -- do 2 (eapply over_tree_fusion_l) ; exact Ho'.
        -- eapply over_tree_fusion_r, over_tree_fusion_l ; exact Ho'.
        -- eapply over_tree_fusion_r ; exact Ho'.
      * intros ; unshelve eapply eqv.(eqvPos) ; [ | | | eapply rsnd ] ; cbn in *.
        -- do 2 (eapply over_tree_fusion_l) ; exact Ho'.
        -- eapply over_tree_fusion_r, over_tree_fusion_l ; exact Ho'.
        -- eapply over_tree_fusion_r ; exact Ho'.
    + constructor; now eapply convneu_conv.
  - cbn in *.
    intros ; unshelve eapply eqv.(eqvPos) ; eauto.
    3: eapply sndRed.
    + do 2 (eapply over_tree_fusion_l) ; eassumption.
    + eapply over_tree_fusion_r, over_tree_fusion_l ; eassumption.
    + eapply over_tree_fusion_r ; eassumption.
Defined.

Lemma ΣIrrelevanceTmEq t u : [Γ ||-<lA> t ≅ u : A | RA]< wl > -> [Γ ||-<lA'> t ≅ u : A' | RA']< wl >.
Proof.
  intros [] ; cbn in *; unshelve econstructor.
  1,2: now eapply ΣIrrelevanceTm.
  - intros ; eapply DTree_fusion ;
      [ eapply DTree_fusion ; [unshelve eapply (PolyRed.posTree ΣA) | eapply eqv.(eqvTree) ; eauto]
      | unshelve eapply eqTree ].
    6,7: now eapply (SigRedTm.fstRed redL).
    all: eauto ; unshelve eapply eqv.(eqvShp) ; try eapply (SigRedTm.fstRed redL).
  - now eapply convtm_conv.
  - intros; unshelve eapply eqv.(eqvShp); auto.
  - intros; unshelve eapply eqv.(eqvPos); auto ; cbn in *.
    4: eapply eqSnd.
    + do 2 (eapply over_tree_fusion_l) ; eassumption.
    + eapply over_tree_fusion_r, over_tree_fusion_l ; eassumption.
    + eapply over_tree_fusion_r ; eassumption.
Qed.

End ΣIrrelevanceLemmas.

Lemma ΣIrrelevanceLRPack@{i j k l i' j' k' l' v}
  {wl Γ lA A lA' A'} 
  (ΣA : ParamRedTy@{i j k l} tSig wl Γ lA A) 
  (ΣA' : ParamRedTy@{i' j' k' l'} tSig wl Γ lA' A')
  (RA := LRSig' ΣA)
  (RA' := LRSig' ΣA')
  (eqDom : [Γ |- ΣA.(ParamRedTy.dom) ≅ ΣA'.(ParamRedTy.dom)]< wl >)
  (eqSig : [Γ |- ΣA.(outTy) ≅ ΣA'.(outTy) ]< wl >)
  (eqv : equivPolyRed ΣA ΣA')
  : equivLRPack@{k k' v} RA RA'.
Proof.
  pose proof (equivPolyRedSym eqv).
  constructor.
  - split; now apply ΣIrrelevanceTyEq.
  - split; now apply ΣIrrelevanceTm.
  - split; now apply ΣIrrelevanceTmEq.
Qed.

(** *** Lemmas for conversion of reducible neutral terms at arbitrary types *)

Lemma NeNfconv {wl Γ k A A'} : [Γ |- A']< wl > -> [Γ |- A ≅ A']< wl > -> [Γ ||-NeNf k : A]< wl > -> [Γ ||-NeNf k : A']< wl >.
Proof.
  intros ?? []; econstructor; tea. all: gen_typing.
Qed.

Lemma NeNfEqconv {wl Γ k k' A A'} : [Γ |- A']< wl > -> [Γ |- A ≅ A']< wl > -> [Γ ||-NeNf k ≅ k' : A]< wl > -> [Γ ||-NeNf k ≅ k' : A']< wl >.
Proof.
  intros ?? []; econstructor; tea. gen_typing.
Qed.

(** *** Irrelevance for Identity types *)

Section IdIrrelevance.
  Universe i j k l i' j' k' l' v.
  Context {wl Γ lA A lA' A'} 
    (IA : IdRedTy@{i j k l} wl Γ lA A) 
    (IA' : IdRedTy@{i' j' k' l'} wl Γ lA' A')
    (RA := LRId' IA)
    (RA' := LRId' IA')
    (eqId : [Γ |- IA.(IdRedTy.outTy) ≅ IA'.(IdRedTy.outTy)]< wl >)
    (eqv : equivLRPack@{k k' v} IA.(IdRedTy.tyRed) IA'.(IdRedTy.tyRed))
    (* (eqty : [Γ |- IA.(IdRedTy.ty) ≅  IA'.(IdRedTy.ty)]< wl >) *)
    (lhsconv : [IA.(IdRedTy.tyRed) | Γ ||- IA.(IdRedTy.lhs) ≅  IA'.(IdRedTy.lhs) : _ ]< wl >)
    (rhsconv : [IA.(IdRedTy.tyRed) | Γ ||- IA.(IdRedTy.rhs) ≅  IA'.(IdRedTy.rhs) : _]< wl >).

  Let APer := IA.(IdRedTy.tyPER).
  #[local]
  Existing Instance APer.

  Lemma IdIrrelevanceTyEq B : [Γ ||-<lA> A ≅ B | RA]< wl > -> [Γ ||-<lA'> A' ≅ B | RA']< wl >.
  Proof.
    intros  [????] ; cbn in *; econstructor; tea; try now apply eqv.
    - etransitivity; tea; now symmetry.
    - apply eqv; etransitivity; tea; now symmetry.
    - apply eqv; etransitivity; tea; now symmetry.
  Qed.
  
  Lemma IdIrrelevanceProp t : IdProp IA t -> IdProp IA' t. 
  Proof.
    intros []; constructor; tea; cycle -1.
    1: eapply NeNfconv; tea; unfold_id_outTy ; destruct IA'; escape; cbn in *; gen_typing.
    all: apply eqv; tea.
    all: etransitivity; [now symmetry|]; tea.
  Qed.

  Lemma IdIrrelevanceTm t : [Γ ||-<lA> t : A | RA]< wl > -> [Γ ||-<lA'> t : A' | RA']< wl >.
  Proof.
    intros []; cbn in *; unshelve econstructor; unfold_id_outTy; tea.
    - now eapply redtmwf_conv.
    - now eapply convtm_conv.
    - now eapply IdIrrelevanceProp.
  Qed.

  Lemma IdIrrelevancePropEq t u : IdPropEq IA t u -> IdPropEq IA' t u.
  Proof.
    intros []; constructor ; tea; cycle -1.
    1: eapply NeNfEqconv; tea; unfold_id_outTy ; destruct IA'; escape; cbn in *; gen_typing.
    all: apply eqv; tea.
    all: etransitivity; [now symmetry|]; tea.
  Qed.
  
  Lemma IdIrrelevanceTmEq t u : [Γ ||-<lA> t ≅ u : A | RA]< wl > -> [Γ ||-<lA'> t ≅ u : A' | RA']< wl >.
  Proof.
    intros []; cbn in *; unshelve econstructor; unfold_id_outTy.
    3,4: now eapply redtmwf_conv.
    - now eapply convtm_conv.
    - now eapply IdIrrelevancePropEq.
  Qed.
  
End IdIrrelevance.

Lemma IdIrrelevanceLRPack@{i j k l i' j' k' l' v}
  {wl Γ lA A lA' A'} 
  (IA : IdRedTy@{i j k l} wl Γ lA A) 
  (IA' : IdRedTy@{i' j' k' l'} wl Γ lA' A')
  (RA := LRId' IA)
  (RA' := LRId' IA')
  (eqId : [Γ |- IA.(IdRedTy.outTy) ≅ IA'.(IdRedTy.outTy)]< wl >)
  (eqv : equivLRPack@{k k' v} IA.(IdRedTy.tyRed) IA'.(IdRedTy.tyRed))
  (lhsconv : [IA.(IdRedTy.tyRed) | Γ ||- IA.(IdRedTy.lhs) ≅  IA'.(IdRedTy.lhs) : _ ]< wl >)
  (rhsconv : [IA.(IdRedTy.tyRed) | Γ ||- IA.(IdRedTy.rhs) ≅  IA'.(IdRedTy.rhs) : _]< wl >)
  : equivLRPack@{k k' v} RA RA'.
Proof.
  pose proof (IA.(IdRedTy.tyPER)).
  pose proof (symLRPack eqv).
  assert (eqId' : [Γ |- IA'.(IdRedTy.outTy) ≅ IA.(IdRedTy.outTy)]< wl >) by now symmetry.
  assert [IA'.(IdRedTy.tyRed) | Γ ||- IA'.(IdRedTy.lhs) ≅  IA.(IdRedTy.lhs) : _ ]< wl > by (apply eqv; now symmetry).
  assert [IA'.(IdRedTy.tyRed) | Γ ||- IA'.(IdRedTy.rhs) ≅  IA.(IdRedTy.rhs) : _ ]< wl > by (apply eqv; now symmetry).
  constructor.
  - split; now apply IdIrrelevanceTyEq.
  - split; now apply IdIrrelevanceTm.
  - split; now apply IdIrrelevanceTmEq.
Qed.



(** *** Irrelevance for neutral types *)

Lemma NeIrrelevanceLRPack@{i j k l i' j' k' l' v}
  {wl Γ A A'} lA lA'
  (neA : [Γ ||-ne A]< wl >)
  (neA' : [Γ ||-ne A']< wl >)
  (RA := LRne_@{i j k l} lA neA)
  (RA' := LRne_@{i' j' k' l'} lA' neA')
  (eqAA' : [Γ ||-ne A ≅ A' | neA ]< wl >)
  : equivLRPack@{k k' v} RA RA'.
Proof.
  destruct neA as [ty], neA' as [ty'], eqAA' as [ty0']; cbn in *.
  assert (ty0' = ty'); [|subst].
  { eapply redtywf_det; tea; constructor; eapply convneu_whne; first [eassumption|symmetry; eassumption]. }
  assert [Γ |- ty ≅ ty']< wl > as convty by gen_typing.
  split.
  + intros ?; split; intros []; econstructor; cbn in *; tea.
    all: etransitivity ; [| tea]; tea; now symmetry.
  + intros ?; split; intros []; econstructor; cbn in *; tea.
    1,3: now eapply redtmwf_conv.
    all: now eapply convneu_conv; first [eassumption|symmetry; eassumption|gen_typing].
  + intros ??; split; intros []; econstructor; cbn in *.
    1-2,4-5: now eapply redtmwf_conv.
    all: now eapply convneu_conv; first [eassumption|symmetry; eassumption|gen_typing].
Qed.



Section NatIrrelevant.
  Universe i j k l i' j' k' l'.

  Context {wl Γ lA lA' A A'} (NA : [Γ ||-Nat A]< wl >) (NA' : [Γ ||-Nat A']< wl >)
    (RA := LRNat_@{i j k l} lA NA) (RA' := LRNat_@{i' j' k' l'} lA' NA').
  
  Lemma NatIrrelevanceTyEq B : [Γ ||-<lA> A ≅ B | RA]< wl > -> [Γ ||-<lA'> A' ≅ B | RA']< wl >.
  Proof.
    intros []; now econstructor.
  Qed.

  Lemma NatIrrelevanceTm :
    (forall t, [Γ ||-<lA> t : A | RA]< wl > -> [Γ ||-<lA'> t : A' | RA']< wl >)
    × (forall t, NatProp NA t -> NatProp NA' t).
  Proof.
    apply NatRedInduction; now econstructor.
  Qed.
   
  Lemma NatIrrelevanceTmEq :
    (forall t u, [Γ ||-<lA> t ≅ u : A | RA]< wl > -> [Γ ||-<lA'> t ≅ u : A' | RA']< wl >)
    × (forall t u, NatPropEq NA t u -> NatPropEq NA' t u).
  Proof.
    apply NatRedEqInduction; now econstructor.
  Qed.
End NatIrrelevant.

Lemma NatIrrelevanceLRPack@{i j k l i' j' k' l' v}
  {wl Γ lA lA' A A'} (NA : [Γ ||-Nat A]< wl >) (NA' : [Γ ||-Nat A']< wl >)
  (RA := LRNat_@{i j k l} lA NA) (RA' := LRNat_@{i' j' k' l'} lA' NA') :
  equivLRPack@{k k' v} RA RA'.
Proof.
  constructor.
  - split; apply NatIrrelevanceTyEq.
  - split; apply NatIrrelevanceTm.
  - split; apply NatIrrelevanceTmEq.
Qed.

Section EmptyIrrelevant.
  Universe i j k l i' j' k' l'.

  Context {wl Γ lA lA' A A'} (NA : [Γ ||-Empty A]< wl >) (NA' : [Γ ||-Empty A']< wl >)
    (RA := LREmpty_@{i j k l} lA NA) (RA' := LREmpty_@{i' j' k' l'} lA' NA').
  
  Lemma EmptyIrrelevanceTyEq B : [Γ ||-<lA> A ≅ B | RA]< wl > -> [Γ ||-<lA'> A' ≅ B | RA']< wl >.
  Proof.
    intros []; now econstructor.
  Qed.

  Lemma EmptyIrrelevanceTm :
    (forall t, [Γ ||-<lA> t : A | RA]< wl > -> [Γ ||-<lA'> t : A' | RA']< wl >).
  Proof.
    intros t Ht. induction Ht; now econstructor.
  Qed.
   
  Lemma EmptyIrrelevanceTmEq :
    (forall t u, [Γ ||-<lA> t ≅ u : A | RA]< wl > -> [Γ ||-<lA'> t ≅ u : A' | RA']< wl >).
  Proof.
    intros t u Htu. induction Htu. now econstructor.
  Qed.
End EmptyIrrelevant.

Lemma EmptyIrrelevanceLRPack@{i j k l i' j' k' l' v}
  {wl Γ lA lA' A A'} (NA : [Γ ||-Empty A]< wl >) (NA' : [Γ ||-Empty A']< wl >)
  (RA := LREmpty_@{i j k l} lA NA) (RA' := LREmpty_@{i' j' k' l'} lA' NA') :
  equivLRPack@{k k' v} RA RA'.
Proof.
  constructor.
  - split; apply EmptyIrrelevanceTyEq.
  - split; apply EmptyIrrelevanceTm.
  - split; apply EmptyIrrelevanceTmEq.
Qed.


Section BoolIrrelevant.
  Universe i j k l i' j' k' l'.

  Context {wl Γ lA lA' A A'} (NA : [Γ ||-Bool A]< wl >) (NA' : [Γ ||-Bool A']< wl >)
    (RA := LRBool_@{i j k l} lA NA) (RA' := LRBool_@{i' j' k' l'} lA' NA').
  
  Lemma BoolIrrelevanceTyEq B : [Γ ||-<lA> A ≅ B | RA]< wl > -> [Γ ||-<lA'> A' ≅ B | RA']< wl >.
  Proof.
    intros []; now econstructor.
  Qed.

  Lemma BoolIrrelevanceTm :
    (forall t, [Γ ||-<lA> t : A | RA]< wl > -> [Γ ||-<lA'> t : A' | RA']< wl >).
  Proof.
    intros t Ht. induction Ht ; econstructor ; eauto.
    induction prop ; now econstructor.
  Qed.
   
  Lemma BoolIrrelevanceTmEq :
    (forall t u, [Γ ||-<lA> t ≅ u : A | RA]< wl > -> [Γ ||-<lA'> t ≅ u : A' | RA']< wl >).
  Proof.
    intros t u Htu. induction Htu. econstructor ; eauto.
    induction prop ; now econstructor.
  Qed.

End BoolIrrelevant.

Lemma BoolIrrelevanceLRPack@{i j k l i' j' k' l' v}
  {wl Γ lA lA' A A'} (NA : [Γ ||-Bool A]< wl >) (NA' : [Γ ||-Bool A']< wl >)
  (RA := LRBool_@{i j k l} lA NA) (RA' := LRBool_@{i' j' k' l'} lA' NA') :
  equivLRPack@{k k' v} RA RA'.
Proof.
  constructor.
  - split; apply BoolIrrelevanceTyEq.
  - split; apply BoolIrrelevanceTm.
  - split; apply BoolIrrelevanceTmEq.
Qed.


(** The main proof *)

Section LRIrrelevant.
Universe u v.
(** u is a small universe level that may be instanciated to Set. v is a large universe level *)

Notation "A <≈> B" := (prod@{v v} (A -> B) (B -> A)) (at level 90).

Section LRIrrelevantInductionStep.


Universe i j k l i' j' k' l'.

#[local]
Definition IHStatement lA lA' :=
  (forall l0 (ltA : l0 << lA) (ltA' : l0 << lA'),
      prod@{v v}
        (forall wl Γ t, [ LogRelRec@{i j k} lA l0 ltA | Γ ||- t ]< wl > <≈> [ LogRelRec@{i' j' k'} lA' l0 ltA' | Γ ||- t ]< wl >)
        (forall wl Γ t
           (lr1 : [ LogRelRec@{i j k} lA l0 ltA | Γ ||- t ]< wl >)
           (lr2 : [ LogRelRec@{i' j' k'} lA' l0 ltA' | Γ ||- t ]< wl >)
           u,
            [ LogRelRec@{i j k} lA l0 ltA | Γ ||- t ≅ u | lr1 ]< wl > <≈>
            [ LogRelRec@{i' j' k'} lA' l0 ltA' | Γ ||- t ≅ u | lr2 ]< wl >)).



#[local]
Lemma UnivIrrelevanceLRPack
  {wl Γ lA lA' A A'}
  (IH : IHStatement lA lA')
  (hU : [Γ ||-U<lA> A]< wl >) (hU' : [Γ ||-U<lA'> A']< wl >)
  (RA := LRU_@{i j k l} hU) (RA' := LRU_@{i' j' k' l'} hU') :
  equivLRPack@{k k' v} RA RA'.
Proof.
  revert IH; destruct hU as [_ []], hU' as [_ []]; intro IH; destruct (IH zero Oi Oi) as [IHty IHeq].
  constructor.
  + intros; cbn; split; intros []; now constructor.

  + intros ?; destruct (IHty wl Γ t) as [tfwd tbwd]; split; intros [];
      unshelve econstructor.
    6: apply  tfwd; assumption.
    9: apply tbwd; assumption.
    all : tea.
  + cbn ; intros ? ?;
    destruct (IHty wl Γ t) as [tfwd tbwd];
    destruct (IHty wl Γ u) as [ufwd ubwd].
    split; intros [[] []]; cbn in *; unshelve econstructor.
    3: apply tfwd; assumption.
    5: apply tbwd; assumption.
    6: apply ufwd; assumption.
    8: apply ubwd; assumption.
    (* all: apply todo. *)
    all: cbn.
    6: refine (fst (IHeq _ _ _ _ _ _) _); eassumption.
    7: refine (snd (IHeq _ _ _ _ _ _) _); eassumption.
    (* Regression here: now/eassumption adds universe constraints that we do not want to accept but can't prevent *)
    1-4:econstructor; cycle -1; [|tea..].
    1: eapply tfwd; eassumption.
    1: eapply ufwd; eassumption.
    1: eapply tbwd; eassumption.
    1: eapply ubwd; eassumption.
    all: cbn; tea.
Qed.


(** ** The main theorem *)

#[local]
Lemma LRIrrelevantPreds {lA lA'}
  (IH : IHStatement lA lA') (wl : wfLCon)
  (Γ : context) (A A' : term)
  {eqTyA redTmA : term -> Type@{k}}
  {eqTyA' redTmA' : term -> Type@{k'}}
  {eqTmA : term -> term -> Type@{k}}
  {eqTmA' : term -> term -> Type@{k'}}
  (lrA : LogRel@{i j k l} lA wl Γ A eqTyA redTmA eqTmA)
  (lrA' : LogRel@{i' j' k' l'} lA' wl Γ A' eqTyA' redTmA' eqTmA')
  (RA := Build_LRPack wl Γ A eqTyA redTmA eqTmA)
  (RA' := Build_LRPack wl Γ A' eqTyA' redTmA' eqTmA') :
  eqTyA A' ->
  equivLRPack@{k k' v} RA RA'.
Proof.
  intros he.
  set (s := ShapeViewConv lrA lrA' he).
  induction lrA as [? ? h1 | ? ? neA | ?? A ΠA HAad IHdom IHcod | ??? NA | ??? NA| ??? NA| ?? A ΠA HAad IHdom IHcod | ??? IAP IAad IHPar]
    in RA, A', RA', eqTyA', eqTmA', redTmA', lrA', he, s |- *.
  - destruct lrA' ; try solve [destruct s] ; clear s.
    now apply UnivIrrelevanceLRPack.
  - destruct lrA'  ; try solve [destruct s] ; clear s.
    now unshelve eapply NeIrrelevanceLRPack.
  - destruct lrA' as [| | ?? A' ΠA' HAad'| | | | |] ; try solve [destruct s] ; clear s.
    pose (PA := ParamRedTy.from HAad).
    pose (PA' := ParamRedTy.from HAad').
    destruct he as [dom0 cod0 ??? [domRed codTree codRed]], ΠA' as [dom1 cod1];
    assert (tProd dom0 cod0 = tProd dom1 cod1) as ePi
    by (eapply whredty_det ; gen_typing).
    inversion ePi ; subst ; clear ePi.
    unshelve eapply (ΠIrrelevanceLRPack PA PA') ; [ | | unshelve econstructor]. 
    + eassumption.
    + eassumption.
    + intros ; eapply codTree ; eassumption.
    + intros; unshelve eapply IHdom.
      2: eapply (LRAd.adequate (PolyRed.shpRed PA' _ _ _)).
      now eapply domRed.
    + intros; cbn in * ; unshelve eapply IHcod.
      eapply (LRAd.adequate (PolyRed.posRed PA' _ _ _ _ _)).
      now eapply codRed.
  - destruct lrA' ; try solve [destruct s] ; clear s.
    now unshelve eapply NatIrrelevanceLRPack.
  - destruct lrA' ; try solve [destruct s] ; clear s.
    now unshelve eapply BoolIrrelevanceLRPack.
  - destruct lrA' ; try solve [destruct s] ; clear s.
    now unshelve eapply EmptyIrrelevanceLRPack.
  - destruct lrA' as [| | | | | |?? A' ΠA' HAad'| ] ; try solve [destruct s] ; clear s.
    pose (PA := ParamRedTy.from HAad).
    pose (PA' := ParamRedTy.from HAad').
    destruct he as [dom0 cod0 ??? [domRed codTree codRed]], ΠA' as [dom1 cod1];
    assert (tSig dom0 cod0 = tSig dom1 cod1) as ePi
    by (eapply whredty_det ; gen_typing).
    inversion ePi ; subst ; clear ePi.
    eapply (ΣIrrelevanceLRPack PA PA'); [| |unshelve econstructor].
    + eassumption.
    + eassumption.
    + intros ; eapply codTree ; eassumption.
    + intros; unshelve eapply IHdom.
      2: eapply (LRAd.adequate (PolyRed.shpRed PA' _ _ _)).
      eapply domRed.
    + intros; unshelve eapply IHcod.
      2: eapply (LRAd.adequate (PolyRed.posRed PA' _ _ _ _ _)).
      now eapply codRed.
  - destruct lrA' as [| | | | | | | ?? A' IAP' IAad'] ; try solve [destruct s] ; clear s.
    pose (IA := IdRedTy.from IAad); pose (IA' := IdRedTy.from IAad').
    assert (IA'.(IdRedTy.outTy) = he.(IdRedTyEq.outTy)) as eId.
    1: eapply whredty_det; constructor; try constructor; [apply IA'.(IdRedTy.red)| apply he.(IdRedTyEq.red)].
    inversion eId; destruct he, IAP'; cbn in *. subst; clear eId.
    eapply (IdIrrelevanceLRPack IA IA'); tea.
    eapply IHPar; tea.
    apply IA'.(IdRedTy.tyRed).
    (* unshelve eapply escapeEq.  2: apply IdRedTy.tyRed.  now cbn. *)
Qed.


#[local]
Lemma LRIrrelevantCumPolyRed {lA}
  (IH : IHStatement lA lA) (wl : wfLCon)
  (Γ : context) (shp pos : term)
  (PA : PolyRed@{i j k l} wl Γ lA shp pos)
  (IHshp : forall (Δ : context) (wl' : wfLCon) (ρ : Δ ≤ Γ) (f : wl' ≤ε wl),
      [ |-[ ta ] Δ]< wl' > -> [Δ ||-< lA > shp⟨ρ⟩]< wl' >)
  (IHTree : forall (Δ : context) (wl' : wfLCon) (a : term) (ρ : Δ ≤ Γ) (f : wl' ≤ε wl)
                  (h : [ |-[ ta ] Δ]< wl' >),
          [PolyRed.shpRed PA ρ f h | _ ||- a : _]< wl' > -> DTree wl')
  (IHpos : forall (Δ : context) (wl' : wfLCon) (a : term) (ρ : Δ ≤ Γ) (f : wl' ≤ε wl)
                  (h : [ |-[ ta ] Δ]< wl' >)
                  (Ha : [PolyRed.shpRed PA ρ f h | _ ||- a : _]< wl' >),
    forall (wl'' : wfLCon)
           (Hover : over_tree wl' wl'' (IHTree _ _ _ ρ f h Ha)),
          [Δ ||-< lA > pos[a .: ρ >> tRel]]< wl'' >) :
  PolyRed@{i' j' k' l'} wl Γ lA shp pos.
Proof.
  unshelve econstructor.
  + exact IHshp.
  + intros Δ wl' a ρ f tΔ ra.
    eapply DTree_fusion.
    * eapply IHTree.
      pose (shpRed := PA.(PolyRed.shpRed) ρ f tΔ).
      destruct (LRIrrelevantPreds IH _ _ _ _
                  (LRAd.adequate shpRed)
                  (LRAd.adequate (IHshp Δ _ ρ f tΔ))
                  (reflLRTyEq shpRed)) as [_ irrTmRed _].
      now eapply (snd (irrTmRed a)).
    * eapply (PA.(PolyRed.posTree)).
      pose (shpRed := PA.(PolyRed.shpRed) ρ f tΔ).
      destruct (LRIrrelevantPreds IH _ _ _ _
                  (LRAd.adequate shpRed)
                  (LRAd.adequate (IHshp Δ _ ρ f tΔ))
                  (reflLRTyEq shpRed)) as [_ irrTmRed _].
      now eapply (snd (irrTmRed a)).
  + intros Δ wl' a ρ f tΔ ra wl'' Hover ; cbn in *.
    eapply IHpos.
    eapply over_tree_fusion_l ; eassumption.
  + intros.
    eapply (PA.(PolyRed.posExtTree) (a := a) (b := b)).
    all: pose (shpRed := PA.(PolyRed.shpRed) ρ f Hd).
    all: destruct (LRIrrelevantPreds IH _ _ _ _
                  (LRAd.adequate shpRed)
                  (LRAd.adequate (IHshp Δ _ ρ f Hd))
                  (reflLRTyEq shpRed)) as [_ irrTmRed irrTmEq].
    * now eapply (snd (irrTmRed a)).
    * now eapply (snd (irrTmRed b)).
    * now eapply (snd (irrTmEq a b)).
  + now destruct PA.
  + now destruct PA.
  + cbn. intros Δ wl' a b ρ f tΔ ra rb rab wl''.
    set (p := LRIrrelevantPreds _ _ _ _ _ _ _ _).
    destruct p as [_ irrTmRed irrTmEq].
    pose (ra' := snd (irrTmRed a) ra) ; cbn in *.
    intros Hoa Hob Hoab.
    pose (posRed := PA.(PolyRed.posRed) ρ f tΔ ra' (over_tree_fusion_r Hoa)).
    destruct (LRIrrelevantPreds IH _ _ _ _
                (LRAd.adequate posRed)
                (LRAd.adequate (IHpos Δ _ a ρ f tΔ ra' wl'' (over_tree_fusion_l Hoa)))
                (reflLRTyEq posRed)) as [irrTyEq _ _].
    eapply (fst (irrTyEq (pos[b .: ρ >> tRel]))).
    eapply PolyRed.posExt ; [ | eassumption].
    now eapply over_tree_fusion_r.
Qed.


Unset Printing Universes.
#[local]
Lemma LRIrrelevantCumTy {lA}
  (IH : IHStatement lA lA) (wl : wfLCon)
  (Γ : context) (A : term)
  : [ LogRel@{i j k l} lA | Γ ||- A ]< wl > -> [ LogRel@{i' j' k' l'} lA | Γ ||- A ]< wl >.
Proof.
  intros lrA; revert IH; pattern lA, wl, Γ, A, lrA; eapply LR_rect_TyUr ; clear lA wl Γ A lrA.
  all: intros lA wl Γ A.
  - intros [] ?; eapply LRU_; now econstructor.
  - intros; now eapply LRne_.
  - intros [] IHdom IHcod IH; cbn in *.
    eapply LRPi'; unshelve econstructor.
    3,4,5: tea.
    unshelve eapply LRIrrelevantCumPolyRed; tea.
    + intros * ha ; now eapply (PolyRed.posTree polyRed ρ f h ha).
    + intros; now eapply IHdom.
    + intros; now eapply IHcod.
  - intros; now eapply LRNat_.
  - intros; now eapply LRBool_.
  - intros; now eapply LREmpty_.
  - intros [] IHdom IHcod IH; cbn in *.
    eapply LRSig'; unshelve econstructor.
    3,4,5: tea.
    unshelve eapply LRIrrelevantCumPolyRed; tea.
    + intros * ha ; now eapply (PolyRed.posTree polyRed ρ f h ha).
    + intros; now eapply IHdom.
    + intros; now eapply IHcod.
  - intros [] IHPar IHKripke IH. 
    specialize (IHPar IH) ; cbn in *. pose (IHK Δ wl' ρ f wfΔ := IHKripke Δ wl' ρ f wfΔ IH).
    cbn in *; eapply LRId'.
    assert (eqv: equivLRPack tyRed IHPar).
    1: eapply LRIrrelevantPreds; tea; try eapply reflLRTyEq; now eapply LRAd.adequate.
    assert (eqvK : forall Δ wl' (ρ : Δ ≤ Γ) f (wfΔ : [|- Δ]< wl' >),
               equivLRPack (tyKripke Δ wl' ρ f wfΔ) (IHK Δ wl' ρ f wfΔ)).
    1: intros; eapply LRIrrelevantPreds; tea; try eapply reflLRTyEq; now eapply LRAd.adequate.
    unshelve econstructor.
    4-7: tea.
    1-4: now apply eqv.
    2-4: intros * ? ?%eqvK; apply eqvK; eauto.
    econstructor.
    + intros ?? ?%eqv; apply eqv; now symmetry.
    + intros ??? ?%eqv ?%eqv; apply eqv; now etransitivity.
Qed.



#[local]
Lemma IrrRec0 : IHStatement zero zero.
Proof.
  intros ? ltA; inversion ltA.
Qed.

(** Safety check: we did not add constraints we did not mean to *)
Fail Fail Constraint i < i'.
Fail Fail Constraint i' < i.
Fail Fail Constraint j < j'.
Fail Fail Constraint j' < j.
Fail Fail Constraint k < k'.
Fail Fail Constraint k' < k.
Fail Fail Constraint l < l'.
Fail Fail Constraint l' < l.

End LRIrrelevantInductionStep.

#[local]
Theorem IrrRec@{i j k l i' j' k' l'} {lA} {lA'} :
  IHStatement@{i j k l i' j' k' l'} lA lA'.
Proof.
  intros l0 ltA ltA'.
  destruct ltA. destruct ltA'. cbn in *.
  split.
  - intros wl Γ t. split.
    + eapply (LRIrrelevantCumTy@{u i j k u i' j' k'} IrrRec0@{u i j k u i' j' k'}).
    + eapply (LRIrrelevantCumTy@{u i' j' k' u i j k} IrrRec0@{u i' j' k' u i j k}).
  - intros wl Γ t lr1 lr2 u.
    destruct (LRIrrelevantPreds@{u i j k u i' j' k'} IrrRec0@{u i j k u i' j' k'} wl Γ t t
                (lr1 : LRPackAdequate (LogRel@{u i j k} zero) lr1)
                (lr2 : LRPackAdequate (LogRel@{u i' j' k'} zero) lr2)
                (reflLRTyEq lr1)) as [tyEq _ _].
    exact (tyEq u).
Qed.

#[local]
Theorem LRIrrelevantCum@{i j k l i' j' k' l'}
  (wl : wfLCon) (Γ : context) (A A' : term) {lA lA'}
  {eqTyA redTmA : term -> Type@{k}}
  {eqTyA' redTmA' : term -> Type@{k'}}
  {eqTmA : term -> term -> Type@{k}}
  {eqTmA' : term -> term -> Type@{k'}}
  (lrA : LogRel@{i j k l} lA wl Γ A eqTyA redTmA eqTmA)
  (lrA' : LogRel@{i' j' k' l'} lA' wl Γ A' eqTyA' redTmA' eqTmA') :
  eqTyA A' ->
  @and3@{v v v} (forall B, eqTyA B <≈> eqTyA' B)
    (forall t, redTmA t <≈> redTmA' t)
    (forall t u, eqTmA t u <≈> eqTmA' t u).
Proof.
  exact (LRIrrelevantPreds@{i j k l i' j' k' l'} IrrRec wl Γ A A' lrA lrA').
Qed.

Theorem LRIrrelevantPack@{i j k l} 
  (wl : wfLCon) (Γ : context) (A A' : term) {lA lA'} 
  (RA : [ LogRel@{i j k l} lA | Γ ||- A ]< wl >)
  (RA' : [ LogRel@{i j k l} lA' | Γ ||- A' ]< wl >)
  (RAA' : [Γ ||-<lA> A ≅ A' | RA]< wl >) :
  equivLRPack@{v v v} RA RA'.
Proof.
  pose proof (LRIrrelevantCum@{i j k l i j k l} wl Γ A A' (LRAd.adequate RA) (LRAd.adequate RA') RAA') as [].
  constructor; eauto.
Defined.

Theorem LRTransEq@{i j k l} 
  (wl : wfLCon) (Γ : context) (A B C : term) {lA lB} 
  (RA : [ LogRel@{i j k l} lA | Γ ||- A ]< wl >)
  (RB : [ LogRel@{i j k l} lB | Γ ||- B ]< wl >)
  (RAB : [Γ ||-<lA> A ≅ B | RA]< wl >)
  (RBC : [Γ ||-<lB> B ≅ C | RB]< wl >) :
  [Γ ||-<lA> A ≅ C | RA]< wl >.
Proof.
  pose proof (LRIrrelevantPack wl Γ A B RA RB RAB) as [h _ _].
  now apply h.
Defined.

Corollary WLRTransEq@{i j k l} 
  (wl : wfLCon) (Γ : context) (A B C : term) {lA lB} 
  (RA : WLogRel@{i j k l} lA wl Γ A)
  (RB : WLogRel@{i j k l} lB wl Γ B)
  (RAB : WLogRelEq@{i j k l} lA wl Γ A B RA)
  (RBC : WLogRelEq@{i j k l} lB wl Γ B C RB) :
  W[Γ ||-<lA> A ≅ C | RA]< wl >.
Proof.
  exists (DTree_fusion _ (DTree_fusion _ (WT _ RB) (WTEq _ RBC)) (WTEq _ RAB)).
  intros wl' Hover Hover'.
  eapply LRTransEq.
  - unshelve eapply (WRedEq _ RAB).
    now eapply over_tree_fusion_r.
  - unshelve eapply (WRedEq _ RBC).
    + now eapply over_tree_fusion_l, over_tree_fusion_l.
    + now eapply over_tree_fusion_r, over_tree_fusion_l.
Defined.


Theorem LRCumulative@{i j k l i' j' k' l'} {lA}
  {wl : wfLCon} {Γ : context} {A : term}
  : [ LogRel@{i j k l} lA | Γ ||- A ]< wl > -> [ LogRel@{i' j' k' l'} lA | Γ ||- A ]< wl >.
Proof.
  exact (LRIrrelevantCumTy@{i j k l i' j' k' l'} IrrRec wl Γ A).
Qed.

Corollary LRCumulative' @{i j k l i' j' k' l'} {lA}
  {wl : wfLCon} {Γ : context} {A A' : term}
  : A = A' -> [ LogRel@{i j k l} lA | Γ ||- A ]< wl > -> [ LogRel@{i' j' k' l'} lA | Γ ||- A' ]< wl >.
Proof.
  intros ->; apply LRCumulative.
Qed.
End LRIrrelevant.


#[local]
Corollary TyEqIrrelevantCum wl Γ A {lA eqTyA redTmA eqTmA lA' eqTyA' redTmA' eqTmA'}
  (lrA : LogRel lA wl Γ A eqTyA redTmA eqTmA) (lrA' : LogRel lA' wl Γ A eqTyA' redTmA' eqTmA') :
  forall B, eqTyA B -> eqTyA' B.
Proof.
  apply (LRIrrelevantCum _ _ _ _ lrA lrA').
  now eapply LRTyEqRefl.
Qed.

Corollary LRTyEqIrrelevantCum@{i j k l i' j' k' l'} lA lA' wl Γ A
  (lrA : [LogRel@{i j k l} lA | Γ ||- A]< wl >) (lrA' : [LogRel@{i' j' k' l'} lA' | Γ ||- A]< wl >) :
  forall B, [Γ ||-< lA > A ≅ B | lrA]< wl > -> [Γ ||-< lA' > A ≅ B | lrA']< wl >.
Proof.
  destruct lrA, lrA'.
  cbn in *.
  now eapply TyEqIrrelevantCum.
Qed.

Corollary LRTyEqIrrelevantCum'@{i j k l i' j' k' l'} lA lA' wl Γ A A' (e : A = A')
  (lrA : [LogRel@{i j k l} lA | Γ ||- A]< wl >) (lrA' : [LogRel@{i' j' k' l'} lA' | Γ ||- A']< wl >) :
  forall B, [Γ ||-< lA > A ≅ B | lrA]< wl > -> [Γ ||-< lA' > A' ≅ B | lrA']< wl >.
Proof.
  revert lrA'; rewrite <- e; now apply LRTyEqIrrelevantCum.
Qed.

Corollary LRTyEqIrrelevant'@{i j k l} lA lA' wl Γ A A' (e : A = A')
  (lrA : [LogRel@{i j k l} lA | Γ ||- A]< wl >) (lrA' : [LogRel@{i j k l} lA' | Γ ||- A']< wl >) :
  forall B, [Γ ||-< lA > A ≅ B | lrA]< wl > -> [Γ ||-< lA' > A' ≅ B | lrA']< wl >.
Proof.
  revert lrA'; rewrite <- e; now apply LRTyEqIrrelevantCum.
Qed.

Corollary WLRTyEqIrrelevant'@{i j k l} lA lA' wl Γ A A' (e : A = A')
  (lrA : WLogRel@{i j k l} lA wl Γ A) (lrA' :WLogRel@{i j k l} lA' wl Γ A') :
  forall B, W[Γ ||-< lA > A ≅ B | lrA]< wl > -> W[Γ ||-< lA' > A' ≅ B | lrA']< wl >.
Proof.
  intros B [] ; unshelve econstructor.
  - eapply DTree_fusion.
    + exact WTEq.
    + exact (WT _ lrA).
  - intros wl' Hover Hover' ; eapply LRTyEqIrrelevant' ; [eassumption | ].
    unshelve eapply WRedEq.
    + now eapply over_tree_fusion_r.
    + now eapply over_tree_fusion_l.
Qed.

#[local]
Corollary RedTmIrrelevantCum wl Γ A {lA eqTyA redTmA eqTmA lA' eqTyA' redTmA' eqTmA'}
  (lrA : LogRel lA wl Γ A eqTyA redTmA eqTmA) (lrA' : LogRel lA' wl Γ A eqTyA' redTmA' eqTmA') :
  forall t, redTmA t -> redTmA' t.
Proof.
  apply (LRIrrelevantCum _ _ _ _ lrA lrA').
  now eapply LRTyEqRefl.
Qed.

Corollary LRTmRedIrrelevantCum@{i j k l i' j' k' l'} lA lA' wl Γ A
  (lrA : [LogRel@{i j k l} lA | Γ ||- A]< wl >) (lrA' : [LogRel@{i' j' k' l'} lA' | Γ ||- A]< wl >) :
  forall t, [Γ ||-< lA > t : A | lrA]< wl > -> [Γ ||-< lA' > t : A | lrA']< wl >.
Proof.
  destruct lrA, lrA'.
  cbn in *.
  now eapply RedTmIrrelevantCum.
Qed.

Corollary LRTmRedIrrelevantCum'@{i j k l i' j' k' l'} lA lA' wl Γ A A' (e : A = A')
  (lrA : [LogRel@{i j k l} lA | Γ ||- A]< wl >) (lrA' : [LogRel@{i' j' k' l'} lA' | Γ ||- A']< wl >) :
  forall t, [Γ ||-< lA > t : A | lrA]< wl > -> [Γ ||-< lA' > t : A' | lrA']< wl >.
Proof.
  revert lrA'; rewrite <- e; now apply LRTmRedIrrelevantCum.
Qed.

Corollary LRTmRedIrrelevant'@{i j k l} lA lA' wl Γ A A' (e : A = A')
  (lrA : [LogRel@{i j k l} lA | Γ ||- A]< wl >) (lrA' : [LogRel@{i j k l} lA' | Γ ||- A']< wl >) :
  forall t, [Γ ||-< lA > t : A | lrA]< wl > -> [Γ ||-< lA' > t : A' | lrA']< wl >.
Proof.
  revert lrA'; rewrite <- e; now apply LRTmRedIrrelevantCum.
Qed.

Corollary WLRTmRedIrrelevant'@{i j k l} lA lA' wl Γ A A' (e : A = A')
  (lrA : WLogRel@{i j k l} lA wl Γ A) (lrA' :WLogRel@{i j k l} lA' wl Γ A') :
  forall t, W[Γ ||-< lA > t : A | lrA]< wl > -> W[Γ ||-< lA' > t : A' | lrA']< wl >.
Proof.
  intros t [] ; unshelve econstructor.
  - eapply DTree_fusion.
    + exact WTTm.
    + exact (WT _ lrA).
  - intros wl' Hover Hover' ; eapply LRTmRedIrrelevant' ; [eassumption | ].
    unshelve eapply WRedTm.
    + now eapply over_tree_fusion_r.
    + now eapply over_tree_fusion_l.
Qed.


#[local]
Corollary TmEqIrrelevantCum wl Γ A {lA eqTyA redTmA eqTmA lA' eqTyA' redTmA' eqTmA'}
  (lrA : LogRel lA wl Γ A eqTyA redTmA eqTmA) (lrA' : LogRel lA' wl Γ A eqTyA' redTmA' eqTmA') :
  forall t u, eqTmA t u -> eqTmA' t u.
Proof.
  apply (LRIrrelevantCum _ _ _ _ lrA lrA').
  now eapply LRTyEqRefl.
Qed.

Corollary LRTmEqIrrelevantCum@{i j k l i' j' k' l'} lA lA' wl Γ A
  (lrA : [LogRel@{i j k l} lA | Γ ||- A]< wl >) (lrA' : [LogRel@{i' j' k' l'} lA' | Γ ||- A]< wl >) :
  forall t u, [Γ ||-< lA > t ≅ u : A | lrA]< wl > -> [Γ ||-< lA' > t ≅ u : A | lrA']< wl >.
Proof.
  destruct lrA, lrA'.
  cbn in *.
  now eapply TmEqIrrelevantCum.
Qed.

Corollary LRTmEqIrrelevantCum'@{i j k l i' j' k' l'} lA lA' wl Γ A A' (e : A = A')
  (lrA : [LogRel@{i j k l} lA | Γ ||- A]< wl >) (lrA' : [LogRel@{i' j' k' l'} lA' | Γ ||- A']< wl >) :
  forall t u, [Γ ||-< lA > t ≅ u : A | lrA]< wl > -> [Γ ||-< lA' > t ≅ u : A' | lrA']< wl >.
Proof.
  revert lrA'; rewrite <- e; now apply LRTmEqIrrelevantCum.
Qed.

Corollary LRTmEqIrrelevant'@{i j k l} lA lA' wl Γ A A' (e : A = A')
  (lrA : [LogRel@{i j k l} lA | Γ ||- A]< wl >) (lrA' : [LogRel@{i j k l} lA' | Γ ||- A']< wl >) :
  forall t u, [Γ ||-< lA > t ≅ u : A | lrA]< wl > -> [Γ ||-< lA' > t ≅ u : A' | lrA']< wl >.
Proof.
  revert lrA'; rewrite <- e; now apply LRTmEqIrrelevantCum.
Qed.

Corollary WLRTmEqIrrelevant'@{i j k l} lA lA' wl Γ A A' (e : A = A')
  (lrA : WLogRel@{i j k l} lA wl Γ A) (lrA' :WLogRel@{i j k l} lA' wl Γ A') :
  forall t u, W[Γ ||-< lA > t ≅ u : A | lrA]< wl > -> W[Γ ||-< lA' > t ≅ u : A' | lrA']< wl >.
Proof.
  intros t u [] ; unshelve econstructor.
  - eapply DTree_fusion.
    + exact WTTmEq.
    + exact (WT _ lrA).
  - intros wl' Hover Hover' ; eapply LRTmEqIrrelevant' ; [eassumption | ].
    unshelve eapply WRedTmEq.
    + now eapply over_tree_fusion_r.
    + now eapply over_tree_fusion_l.
Qed.


Corollary TyEqSym wl Γ A A' {lA eqTyA redTmA eqTmA lA' eqTyA' redTmA' eqTmA'}
  (lrA : LogRel lA wl Γ A eqTyA redTmA eqTmA) (lrA' : LogRel lA' wl Γ A' eqTyA' redTmA' eqTmA') :
  eqTyA A' -> eqTyA' A.
Proof.
  intros.
  apply (LRIrrelevantCum _ _ _ _ lrA lrA').
  1: eauto.
  now eapply LRTyEqRefl.
Qed.

Corollary LRTyEqSym lA lA' wl Γ A A' (lrA : [Γ ||-< lA > A]< wl >) (lrA' : [Γ ||-< lA'> A']< wl >) :
  [Γ ||-< lA > A ≅ A' | lrA]< wl > -> [Γ ||-< lA' > A' ≅ A | lrA']< wl >.
Proof.
  destruct lrA, lrA'.
  cbn in *.
  now eapply TyEqSym.
Qed.

Corollary WLRTyEqSym lA lA' wl Γ A A' (lrA : W[Γ ||-< lA > A]< wl >) (lrA' : W[Γ ||-< lA'> A']< wl >) :
  W[Γ ||-< lA > A ≅ A' | lrA]< wl > -> W[Γ ||-< lA' > A' ≅ A | lrA']< wl >.
Proof.
  destruct lrA as [d Hd], lrA' as [d' Hd'].
  intros [deq Hdeq] ; cbn in *.
  exists (DTree_fusion _ d deq).
  intros wl' Hover Hover' ; eapply LRTyEqSym.
  unshelve eapply Hdeq.
  - now eapply over_tree_fusion_l.
  - now eapply over_tree_fusion_r.
Qed.

#[local]
Corollary RedTmConv wl Γ A A' {lA eqTyA redTmA eqTmA lA' eqTyA' redTmA' eqTmA'}
  (lrA : LogRel lA wl Γ A eqTyA redTmA eqTmA) (lrA' : LogRel lA' wl Γ A' eqTyA' redTmA' eqTmA') :
  eqTyA A' ->
  forall t, redTmA t -> redTmA' t.
Proof.
  apply (LRIrrelevantCum _ _ _ _ lrA lrA').
Qed.

Corollary LRTmRedConv lA lA' wl Γ A A' (lrA : [Γ ||-< lA > A]< wl >) (lrA' : [Γ ||-< lA'> A' ]< wl >) :
  [Γ ||-< lA > A ≅ A' | lrA ]< wl > ->
  forall t, [Γ ||-< lA > t : A | lrA]< wl > -> [Γ ||-< lA' > t : A' | lrA']< wl >.
Proof.
  destruct lrA, lrA'.
  cbn in *.
  now eapply RedTmConv.
Qed.

Corollary WLRTmRedConv lA lA' wl Γ A A' (lrA : W[Γ ||-< lA > A]< wl >) (lrA' : W[Γ ||-< lA'> A' ]< wl >) :
  W[Γ ||-< lA > A ≅ A' | lrA ]< wl > ->
  forall t, W[Γ ||-< lA > t : A | lrA]< wl > -> W[Γ ||-< lA' > t : A' | lrA']< wl >.
Proof.
  destruct lrA as [d Hd], lrA' as [d' Hd'].
  intros [deq Hdeq] t [deqt Hdeqt] ; cbn in *.
  exists (DTree_fusion _ (DTree_fusion _ d deq) deqt).
  intros wl' Hover Hover' ; eapply LRTmRedConv.
  - cbn in *. unshelve eapply Hdeq.
    + now do 2 (eapply over_tree_fusion_l).
    + now eapply over_tree_fusion_r, over_tree_fusion_l.
  - eapply Hdeqt.
    now eapply over_tree_fusion_r.
Qed.

Corollary PolyRedEqSym {wl Γ l l' shp shp' pos pos'}
  {PA : PolyRed wl Γ l shp pos}
  (PA' : PolyRed wl Γ l' shp' pos') :
  PolyRedEq PA shp' pos' -> PolyRedEq PA' shp pos.
Proof.
  intros []; unshelve econstructor.
  - intros; eapply DTree_fusion.
    + eapply (PolyRedPack.posTree PA) ; eauto.
      eapply LRTmRedConv; tea.
      now eapply LRTyEqSym.
    + eapply posTree.
      eapply LRTmRedConv; tea.
      now eapply LRTyEqSym.
  - intros ; eapply LRTyEqSym; eauto.
  - intros.
    assert (f' :  k'' ≤ε k') by (now eapply over_tree_le).
    eapply LRTyEqSym. unshelve eapply (posRed _ _ k') ; tea ; unshelve eauto.
    + eapply LRTmRedConv; tea.
      now eapply LRTyEqSym.
    + eapply over_tree_fusion_l ; now eauto.
    + eapply over_tree_fusion_r ; now eauto.
      Unshelve.
      all: assumption.
Qed.

#[local]
Corollary TmEqRedConv wl Γ A A' {lA eqTyA redTmA eqTmA lA' eqTyA' redTmA' eqTmA'}
  (lrA : LogRel lA wl Γ A eqTyA redTmA eqTmA) (lrA' : LogRel lA' wl Γ A' eqTyA' redTmA' eqTmA') :
  eqTyA A' ->
  forall t u, eqTmA t u -> eqTmA' t u.
Proof.
  apply (LRIrrelevantCum _ _ _ _ lrA lrA').
Qed.

Corollary LRTmEqRedConv lA lA' wl Γ A A' (lrA : [Γ ||-< lA > A]< wl >) (lrA' : [Γ ||-< lA'> A']< wl >) :
  [Γ ||-< lA > A ≅ A' | lrA ]< wl > ->
  forall t u, [Γ ||-< lA > t ≅ u : A | lrA]< wl > -> [Γ ||-< lA' > t ≅ u : A' | lrA']< wl >.
Proof.
  destruct lrA, lrA'.
  cbn in *.
  now eapply TmEqRedConv.
Qed.

Corollary WLRTmEqRedConv lA lA' wl Γ A A' (lrA : W[Γ ||-< lA > A]< wl >) (lrA' : W[Γ ||-< lA'> A']< wl >) :
  W[Γ ||-< lA > A ≅ A' | lrA ]< wl > ->
  forall t u, W[Γ ||-< lA > t ≅ u : A | lrA]< wl > -> W[Γ ||-< lA' > t ≅ u : A' | lrA']< wl >.
Proof.
  destruct lrA, lrA' ; intros [WEq WRedEq] t u [WTmEq WRedTmEq].
  unshelve econstructor.
  + eapply DTree_fusion ; [eapply DTree_fusion | ].
    * exact WEq.
    * exact WT.
    * exact WTmEq.
  + intros wl' Hover Hover' ; cbn in *.
    eapply LRTmEqRedConv.
    2: unshelve eapply WRedTmEq.
    eapply WRedEq.
    * now do 2 (eapply over_tree_fusion_l).
    * now eapply over_tree_fusion_r, over_tree_fusion_l.
    * now eapply over_tree_fusion_r.
Qed.

Corollary LRTmTmEqIrrelevant' lA lA' wl Γ A A' (e : A = A')
  (lrA : [Γ ||-< lA > A]< wl >) (lrA' : [Γ ||-< lA'> A']< wl >) :
  forall t u, 
  [Γ ||-<lA> t : A | lrA]< wl > × [Γ ||-< lA > t ≅ u : A | lrA]< wl > -> 
  [Γ ||-<lA'> t : A' | lrA']< wl > × [Γ ||-< lA' > t ≅ u : A' | lrA']< wl >.
Proof.
  intros ?? []; split; [eapply LRTmRedIrrelevant'| eapply LRTmEqIrrelevant']; tea.
Qed.

Corollary WLRTmTmEqIrrelevant' lA lA' wl Γ A A' (e : A = A')
  (lrA : W[Γ ||-< lA > A]< wl >) (lrA' : W[Γ ||-< lA'> A']< wl >) :
  forall t u, 
  W[Γ ||-<lA> t : A | lrA]< wl > × W[Γ ||-< lA > t ≅ u : A | lrA]< wl > -> 
  W[Γ ||-<lA'> t : A' | lrA']< wl > × W[Γ ||-< lA' > t ≅ u : A' | lrA']< wl >.
Proof.
  intros ?? []; split; [eapply WLRTmRedIrrelevant'| eapply WLRTmEqIrrelevant']; tea.
Qed.  
  
Set Printing Primitive Projection Parameters.

Lemma NeNfEqSym {wl Γ k k' A} : [Γ ||-NeNf k ≅ k' : A]< wl > -> [Γ ||-NeNf k' ≅ k : A]< wl >.
Proof.
  intros []; constructor; tea; now symmetry.
Qed.

Lemma LRTmEqSym@{h i j k l} lA wl Γ A (lrA : [LogRel@{i j k l} lA | Γ ||- A]< wl >) : forall t u,
  [Γ ||-<lA> t ≅ u : A |lrA]< wl > -> [Γ ||-<lA> u ≅ t : A |lrA]< wl >.
Proof.
  pattern lA, wl, Γ, A, lrA. apply LR_rect_TyUr; clear lA wl Γ A lrA.
  - intros * []. unshelve econstructor; try eassumption.
    1: symmetry; eassumption.
    (* Need an additional universe level h < i *)
    eapply TyEqSym@{h i j k h i j k}. 3:exact relEq.
    all: eapply LogRelRec_unfold; eapply LRAd.adequate; eassumption.
  - intros * []. unshelve econstructor.
    3,4: eassumption.
    symmetry; eassumption.
  - intros * ihdom ihcod * []. unshelve econstructor.
    1,2: eassumption.
    2: symmetry; eassumption.
    + intros ; eapply eqTree ; eauto.
    + intros. apply ihcod. eapply eqApp ; now eauto.
  - intros ???? NA.
    set (G := _); enough (h : G × (forall t u, NatPropEq NA t u -> NatPropEq NA u t)) by apply h.
    subst G; apply NatRedEqInduction.
    1-3: now econstructor.
    intros; constructor; now eapply NeNfEqSym.
  - intros ???? NA.
    intros t u [? ? ? ? ? ? ? prop]. destruct prop.
    all: try (econstructor; eauto ; now econstructor).
    econstructor ; eauto.
    2: econstructor; now eapply NeNfEqSym.
    symmetry; eassumption.
  - intros ???? NA.
    intros t u [? ? ? ? ? ? ? prop]. destruct prop. econstructor; eauto.
    2: econstructor; now eapply NeNfEqSym.
    symmetry; eassumption.
  - intros * ihshp ihpos * []; unshelve econstructor.
    1,2: tea.
    2: now symmetry.
    + intros ; eapply DTree_fusion.
      * eapply DTree_fusion.
        -- now eapply eqTree.
        -- exact (PolyRed.posTree ΠA _ _ _ (SigRedTm.fstRed redL ρ f Hd)).
      * eapply (PolyRed.posExtTree ΠA ρ f Hd).
        -- eapply (SigRedTm.fstRed redL ρ f Hd).
        -- eapply (SigRedTm.fstRed redR ρ f Hd).
        -- now eapply eqFst.
    + intros; now eapply ihshp.
    + intros; unshelve eapply ihpos.
      eapply LRTmEqRedConv.
      2: unshelve eapply (eqSnd _ k') ; eauto ; cbn in *.
      * eapply PolyRed.posExt.
        -- eassumption.
        -- now eapply over_tree_fusion_r. 
      * now eapply over_tree_fusion_r, over_tree_fusion_l. 
      * now do 2 (eapply over_tree_fusion_l). 
  - intros ???? [] ???? [????? hprop]; unshelve econstructor; unfold_id_outTy; cbn in *.
    3,4: tea.
    1: now symmetry.
    destruct hprop; econstructor; tea.
    now eapply NeNfEqSym.    
Qed.

Lemma WLRTmEqSym@{h i j k l} lA wl Γ A (lrA : WLogRel@{i j k l} lA wl Γ A) : forall t u,
    W[Γ ||-<lA> t ≅ u : A |lrA]< wl > -> W[Γ ||-<lA> u ≅ t : A |lrA]< wl >.
Proof.
  intros t u [d Hd] ; exists d.
  intros wl' Hover Hover' ; now eapply LRTmEqSym.
Qed.

End Irrelevances.



(** ** Tactics for irrelevance, with and without universe cumulativity *)

Ltac irrelevanceCum0 :=
  lazymatch goal with
  | [|- [_ ||-<_> _]< _ >] => (now eapply LRCumulative) + eapply LRCumulative'
  | [|- [_ | _ ||- _ ≅ _ ]< _ > ] => eapply LRTyEqIrrelevantCum'
  | [|- [_ ||-<_> _ ≅ _ | _ ]< _ > ] => eapply LRTyEqIrrelevantCum'
  | [|- [_ | _ ||- _ : _ ]< _ > ] => eapply LRTmRedIrrelevantCum'
  | [|- [_ ||-<_> _ : _ | _ ]< _ > ] => eapply LRTmRedIrrelevantCum'
  | [|- [_ | _ ||- _ ≅ _ : _ ]< _ > ] => eapply LRTmEqIrrelevantCum'
  | [|- [_ ||-<_> _ ≅ _ : _ | _ ]< _ > ] => eapply LRTmEqIrrelevantCum'
  end.

Ltac irrelevanceCum := irrelevanceCum0 ; [|eassumption] ; try first [reflexivity| now bsimpl].

Ltac irrelevanceCumRefl := irrelevanceCum0 ; [reflexivity|].

Ltac irrelevance0 :=
  lazymatch goal with
  | [|- [_ | _ ||- _ ≅ _ ]< _ > ] => eapply LRTyEqIrrelevant'
  | [|- [_ ||-<_> _ ≅ _ | _ ]< _ > ] => eapply LRTyEqIrrelevant'
  | [|- [_ | _ ||- _ : _ ]< _ > ] => eapply LRTmRedIrrelevant'
  | [|- [_ ||-<_> _ : _ | _ ]< _ > ] => eapply LRTmRedIrrelevant'
  | [|- [_ | _ ||- _ ≅ _ : _ ]< _ > ] => eapply LRTmEqIrrelevant'
  | [|- [_ ||-<_> _ ≅ _ : _ | _ ]< _ > ] => eapply LRTmEqIrrelevant'
  | [|- [_ ||-<_> _ : _ | _]< _ > × [_ ||-<_> _≅ _ : _ | _]< _ >] => eapply LRTmTmEqIrrelevant'
  end.

Ltac irrelevance := irrelevance0 ; [|eassumption] ; try first [reflexivity| now bsimpl].

Ltac irrelevanceRefl := irrelevance0 ; [reflexivity|].
