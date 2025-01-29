From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations LContexts Context NormalForms Weakening GenericTyping LogicalRelation.

Set Primitive Projections.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

Create HintDb substitution.
#[global] Hint Constants Opaque : substitution.
#[global] Hint Variables Transparent : substitution.
Ltac substitution := eauto with substitution.


(* The type of our inductively defined validity relation:
  for some R : VRel, R Γ eqSubst says
  that according to R, Γ is valid and the associated substitution validity and equality
  are validSubst and eqSubst.
  One should think of VRel as a functional relation taking one argument Γ and returning
  2 outputs validSubst and eqSubst *)

  Definition VRel@{i j | i < j +} `{ta : tag} `{!WfContext ta} {wl : wfLCon} :=
    forall
      (Γ : context)
      (validSubst : forall (Δ : context) (σ : nat -> term) (wfΔ : [|- Δ]< wl >), Type@{i})
      (eqSubst : forall (Δ : context) (σ σ' : nat -> term) (wfΔ : [|- Δ ]< wl >), validSubst Δ σ wfΔ -> Type@{i})
    , Type@{j}.

(* A VPack contains the data corresponding to the codomain of VRel seen as a functional relation *)

Module VPack.

  Record VPack@{i} `{ta : tag} `{!WfContext ta} {wl : wfLCon} {Γ : context} :=
  {
    validSubst : forall (Δ : context) (σ : nat -> term) (wfΔ : [|- Δ]< wl >), Type@{i} ;
    eqSubst : forall (Δ : context) (σ σ' : nat -> term) (wfΔ : [|- Δ ]< wl >), validSubst Δ σ wfΔ -> Type@{i} ;
  }.

  Arguments VPack : clear implicits.
  Arguments VPack {_ _}.
  Arguments Build_VPack {_ _}.
End VPack.

Export VPack(VPack,Build_VPack).

Notation "[ P | Δ ||-v σ : Γ | wfΔ ]< wl >" := (@VPack.validSubst _ _ wl Γ P Δ σ wfΔ) (at level 0, P, Δ, σ, wl, Γ, wfΔ at level 50).
Notation "[ P | Δ ||-v σ ≅ σ' : Γ | wfΔ | vσ ]< wl >" := (@VPack.eqSubst _ _ wl Γ P Δ σ σ' wfΔ vσ) (at level 0, P, Δ, σ, σ', wl, Γ, wfΔ, vσ at level 50).

(* An VPack it adequate wrt. a VRel when its three unpacked components are *)
#[universes(polymorphic)] Definition VPackAdequate@{i j} `{ta : tag} `{!WfContext ta} {wl : wfLCon} {Γ : context}
  (R : VRel@{i j}) (P : VPack@{i} wl Γ) : Type@{j} :=
  R Γ P.(VPack.validSubst) P.(VPack.eqSubst).

Arguments VPackAdequate _ _ /.

Module VAd.

  Record > VAdequate `{ta : tag} `{!WfContext ta} {wl : wfLCon} {Γ : context} {R : VRel} :=
  {
    pack :> VPack wl Γ ;
    adequate :> VPackAdequate R pack
  }.

  Arguments VAdequate : clear implicits.
  Arguments VAdequate {_ _}.
  Arguments Build_VAdequate {_ _ _ _ _}.

End VAd.

Export VAd(VAdequate,Build_VAdequate).
(* These coercions would be defined using the >/:> syntax in the definition of the record,
  but this fails here due to the module being only partially exported *)
Coercion VAd.pack : VAdequate >-> VPack.
Coercion VAd.adequate : VAdequate >-> VPackAdequate.

Notation "[ R | ||-v Γ ]< wl >"                            := (VAdequate wl Γ R) (at level 0, R, wl, Γ at level 50).
Notation "[ R | Δ ||-v σ : Γ | RΓ | wfΔ ]< wl >"           := (RΓ.(@VAd.pack _ _ wl Γ R).(VPack.validSubst) Δ σ wfΔ) (at level 0, R, Δ, σ, wl, Γ, RΓ, wfΔ at level 50).
Notation "[ R | Δ ||-v σ ≅ σ' : Γ | RΓ | wfΔ | vσ ]< wl >" := (RΓ.(@VAd.pack _ _ wl Γ R).(VPack.eqSubst) Δ σ σ' wfΔ vσ) (at level 0, R, Δ, σ, σ', wl, Γ, RΓ, wfΔ, vσ at level 50).

Record typeValidity@{u i j k l} `{ta : tag} `{!WfContext ta}
  `{!WfType ta} `{!Typing ta} `{!ConvType ta}
  `{!ConvTerm ta} `{!ConvNeuConv ta} `{!RedType ta} `{!RedTerm ta}
  {wl : wfLCon} {Γ : context} {VΓ : VPack@{u} wl Γ}
  {l : TypeLevel} {A : term} :=
  {
    validTy : forall {Δ : context} {σ : nat -> term}
      (wfΔ : [|- Δ ]< wl >)
      (vσ : [ VΓ | Δ ||-v σ : Γ | wfΔ ]< wl >)
      , WLogRel@{i j k l} l wl Δ (A [ σ ]);
    validTyExt : forall {Δ : context} {σ σ' : nat -> term}
      (wfΔ : [|- Δ ]< wl >)
      (vσ  : [ VΓ | Δ ||-v σ  : Γ | wfΔ ]< wl >)
      (vσ' : [ VΓ | Δ ||-v σ' : Γ | wfΔ ]< wl >)
      (vσσ' : [ VΓ | Δ ||-v σ ≅ σ' : Γ | wfΔ | vσ ]< wl >)
      , WLogRelEq@{i j k l} l wl Δ (A [ σ ]) (A [ σ' ]) (validTy wfΔ vσ)
  }.

Arguments typeValidity : clear implicits.
Arguments typeValidity {_ _ _ _ _ _ _ _ _}.

Notation "[ P | Γ ||-v< l > A ]< wl >" := (typeValidity wl Γ P l A) (at level 0, P, wl, Γ, l, A at level 50).

Definition emptyValidSubst `{ta : tag} `{!WfContext ta} {wl : wfLCon} : forall (Δ : context) (σ : nat -> term) (wfΔ : [|- Δ]< wl >), Type := fun _ _ _ => unit.
Definition emptyEqSubst@{u} `{ta : tag} `{!WfContext ta} {wl : wfLCon} : forall (Δ : context) (σ σ' : nat -> term) (wfΔ : [|- Δ]< wl >), emptyValidSubst@{u} Δ σ wfΔ -> Type@{u} := fun _ _ _ _ _ => unit.
Definition emptyVPack `{ta : tag} `{!WfContext ta} {wl : wfLCon} : VPack wl ε :=
  Build_VPack _ _ emptyValidSubst emptyEqSubst.

Section snocValid.
  Universe u i j k l.
  Context `{ta : tag} `{!WfContext ta}
  `{!WfType ta} `{!Typing ta} `{!ConvType ta}
  `{!ConvTerm ta} `{!ConvNeuConv ta} `{!RedType ta} `{!RedTerm ta}
  {wl : wfLCon} {Γ : context} {VΓ : VPack@{u} wl Γ} {A : term} {l : TypeLevel}
  {vA : typeValidity@{u i j k l} wl Γ VΓ l A (* [ VΓ | Γ ||-v< l > A ]< wl > *)}.

  Record snocValidSubst {Δ : context} {σ : nat -> term} {wfΔ : [|- Δ]< wl >} : Type :=
    {
      validTail : [ VΓ | Δ ||-v ↑ >> σ : Γ | wfΔ ]< wl > ;
      validHead : W[ Δ ||-< l > σ var_zero : A[↑ >> σ] | validTy vA wfΔ validTail ]< wl >
    }.

  Arguments snocValidSubst : clear implicits.

  Record snocEqSubst {Δ : context} {σ σ' : nat -> term} {wfΔ : [|- Δ]< wl >} {vσ : snocValidSubst Δ σ wfΔ} : Type :=
    {
      eqTail : [ VΓ | Δ ||-v ↑ >> σ ≅ ↑ >> σ' : Γ | wfΔ | validTail vσ ]< wl > ;
      eqHead : W[ Δ ||-< l > σ var_zero ≅ σ' var_zero : A[↑ >> σ] | validTy vA wfΔ (validTail vσ) ]< wl >
    }.

  Definition snocVPack := Build_VPack@{u (* max(u,k) *)} wl (Γ ,, A) snocValidSubst (@snocEqSubst).
End snocValid.


Arguments snocValidSubst : clear implicits.
Arguments snocValidSubst {_ _ _ _ _ _ _ _ _}.

Arguments snocEqSubst : clear implicits.
Arguments snocEqSubst {_ _ _ _ _ _ _ _ _}.

Arguments snocVPack : clear implicits.
Arguments snocVPack {_ _ _ _ _ _ _ _ _}.

Unset Elimination Schemes.

Inductive VR@{i j k l} `{ta : tag}
  `{WfContext ta} `{WfType ta} `{Typing ta}
  `{ConvType ta} `{ConvTerm ta} `{ConvNeuConv ta}
  `{RedType ta} `{RedTerm ta} {wl : wfLCon} : VRel@{k l} :=
  | VREmpty : VR ε emptyValidSubst@{k} emptyEqSubst@{k}
  | VRSnoc : forall {Γ A l}
    (VΓ : VPack@{k} wl Γ)
    (VΓad : VPackAdequate@{k l} VR VΓ)
    (VA : typeValidity@{k i j k l} wl Γ VΓ l A (*[ VΓ | Γ ||-v< l > A ]*)),
    VR (Γ ,, A) (snocValidSubst wl Γ VΓ A l VA) (snocEqSubst wl Γ VΓ A l VA).


Set Elimination Schemes.

Notation "[||-v Γ ]< wl >"                             := [ VR | ||-v Γ ]< wl > (at level 0, wl, Γ at level 50).
Notation "[ Δ ||-v σ : Γ | VΓ | wfΔ ]< wl >"           := [ VR | Δ ||-v σ : Γ | VΓ | wfΔ ]< wl >  (at level 0, Δ, σ, wl, Γ, VΓ, wfΔ at level 50).
Notation "[ Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | vσ ]< wl >" := [ VR | Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | vσ ]< wl > (at level 0, Δ, σ, σ', wl, Γ, VΓ, wfΔ, vσ at level 50).
Notation "[ Γ ||-v< l > A | VΓ ]< wl >"                := [ VΓ | Γ ||-v< l > A ]< wl > (at level 0, wl, Γ, l , A, VΓ at level 50).


Section MoreDefs.
  Context `{ta : tag} `{WfContext ta} `{WfType ta} `{Typing ta}
  `{ConvType ta} `{ConvTerm ta} `{ConvNeuConv ta} `{RedType ta} `{RedTerm ta}.

  Definition validEmpty@{i j k l} {wl } : [VR@{i j k l}| ||-v ε ]< wl > := Build_VAdequate emptyVPack VREmpty.

  Definition validSnoc@{i j k l} {wl Γ} {A l}
    (VΓ : [VR@{i j k l}| ||-v Γ]< wl >) (VA : [Γ ||-v< l > A | VΓ]< wl >)
    : [||-v Γ ,, A ]< wl > :=
    Build_VAdequate (snocVPack wl Γ VΓ A l VA) (VRSnoc VΓ VΓ VA).

  Record termValidity@{i j k l} {wl Γ l} {t A : term}
    {VΓ : [VR@{i j k l} (wl := wl) | ||-v Γ]< wl >}
    {VA : typeValidity@{k i j k l} wl Γ VΓ l A (*[Γ ||-v<l> A |VΓ]< wl >*)} : Type :=
    {
      validTm : forall {Δ σ}
        (wfΔ : [|- Δ]< wl >) (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ]< wl >),
        W[Δ ||-<l> t[σ] : A[σ] | validTy VA wfΔ Vσ ]< wl > ;
      validTmExt : forall {Δ : context} {σ σ' : nat -> term}
        (wfΔ : [|- Δ ]< wl >)
        (Vσ  : [Δ ||-v σ  : Γ | VΓ | wfΔ ]< wl >)
        (Vσ' : [ Δ ||-v σ' : Γ | VΓ | wfΔ ]< wl >)
        (Vσσ' : [ Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | Vσ ]< wl >),
        W[Δ ||-<l> t[σ] ≅ t[σ'] : A[σ] | validTy VA wfΔ Vσ ]< wl >
    }.

  Record typeEqValidity@{i j k l} {wl Γ l} {A B : term}
    {VΓ : [VR@{i j k l}| ||-v Γ]< wl >}
    {VA : typeValidity@{k i j k l} wl Γ VΓ l A (*[Γ ||-v<l> A |VΓ]< wl >*)} : Type :=
    {
      validTyEq : forall {Δ σ}
        (wfΔ : [|- Δ]< wl >) (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ]< wl >),
        W[Δ ||-<l> A[σ] ≅ B[σ] | validTy VA wfΔ Vσ]< wl >
    }.

  Record termEqValidity@{i j k l} {wl Γ l} {t u A : term}
    {VΓ : [VR@{i j k l}| ||-v Γ]< wl >}
    {VA : typeValidity@{k i j k l} wl Γ VΓ l A (*[Γ ||-v<l> A |VΓ]< wl >*)} : Type :=
    {
      validTmEq : forall {Δ σ}
        (wfΔ : [|- Δ]< wl >) (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ]< wl >),
        W[Δ ||-<l> t[σ] ≅ u[σ] : A[σ] | validTy VA wfΔ Vσ]< wl >
    }.

  Record tmEqValidity {wl Γ l} {t u A : term} {VΓ : [||-v Γ]< wl >} : Type :=
    {
      Vty  : [Γ ||-v< l > A | VΓ]< wl > ;
      Vlhs : @termValidity wl Γ l t A VΓ Vty ;
      Vrhs : @termValidity wl Γ l u A VΓ Vty ;
      Veq  : @termEqValidity wl Γ l t u A VΓ Vty
    }.

  Record redValidity {wl Γ} {t u A : term} {VΓ : [||-v Γ]< wl >} : Type :=
    {
      validRed : forall {Δ σ}
        (wfΔ : [|- Δ]< wl >) (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ]< wl >),
        [Δ |- t[σ] :⤳*: u[σ] : A[σ]]< wl >
    }.
End MoreDefs.

Arguments termValidity : clear implicits.
Arguments termValidity {_ _ _ _ _ _ _ _ _}.
Arguments Build_termValidity {_ _ _ _ _ _ _ _ _}.

Arguments typeEqValidity : clear implicits.
Arguments typeEqValidity {_ _ _ _ _ _ _ _ _}.
Arguments Build_typeEqValidity {_ _ _ _ _ _ _ _ _}.

Arguments termEqValidity : clear implicits.
Arguments termEqValidity {_ _ _ _ _ _ _ _ _}.
Arguments Build_termEqValidity {_ _ _ _ _ _ _ _ _}.

Arguments tmEqValidity : clear implicits.
Arguments tmEqValidity {_ _ _ _ _ _ _ _ _}.
Arguments Build_tmEqValidity {_ _ _ _ _ _ _ _ _}.

Arguments redValidity : clear implicits.
Arguments redValidity {_ _ _ _ _ _ _ _ _}.
Arguments Build_redValidity {_ _ _ _ _ _ _ _ _}.

Notation "[ Γ ||-v< l > t : A | VΓ | VA ]< wl >"     := (termValidity wl Γ l t A VΓ VA) (at level 0, wl, Γ, l, t, A, VΓ, VA at level 50).
Notation "[ Γ ||-v< l > A ≅ B | VΓ | VA ]< wl >"     := (typeEqValidity wl Γ l A B VΓ VA) (at level 0, wl, Γ, l, A, B, VΓ, VA at level 50).
Notation "[ Γ ||-v< l > t ≅ u : A | VΓ | VA ]< wl >" := (termEqValidity wl Γ l t u A VΓ VA) (at level 0, wl, Γ, l, t, u, A, VΓ, VA at level 50).
Notation "[ Γ ||-v< l > t ≅ u : A | VΓ ]< wl >"      := (tmEqValidity wl Γ l t u A VΓ) (at level 0, wl, Γ, l, t, u, A, VΓ at level 50).
Notation "[ Γ ||-v t :⤳*: u : A | VΓ ]< wl >"      := (redValidity wl Γ t u A VΓ) (at level 0, wl, Γ, t, u, A, VΓ at level 50).

Section Inductions.
  Context `{ta : tag} `{WfContext ta} `{WfType ta} `{Typing ta}
    `{ConvType ta} `{ConvTerm ta} `{ConvNeuConv ta} `{RedType ta} `{RedTerm ta}.
  
  Theorem VR_rect {wl}
    (P : forall {Γ vSubst vSubstExt}, VR Γ vSubst vSubstExt -> Type)
    (hε : P VREmpty)
    (hsnoc : forall {Γ A l VΓ VΓad VA},
      P VΓad -> P (VRSnoc (wl := wl) (Γ := Γ) (A := A) (l := l) VΓ VΓad VA)) :
    forall {Γ vSubst vSubstExt} (VΓ : VR Γ vSubst vSubstExt), P VΓ.
  Proof.
    fix ih 4.
    destruct VΓ; [exact hε | apply hsnoc].
    now unshelve eapply ih.
  Defined.

  Theorem validity_rect {wl}
    (P : forall {Γ : context}, [||-v Γ]< wl > -> Type)
    (hε : P validEmpty)
    (hsnoc : forall {Γ A l} (VΓ : [||-v Γ]< wl >) (VA : [Γ ||-v< l > A | VΓ]< wl >), P VΓ -> P (validSnoc VΓ VA)) :
    forall {Γ : context} (VΓ : [||-v Γ]< wl >), P VΓ.
  Proof.
    intros Γ [[s eq] VΓad]; revert Γ s eq VΓad.
    apply VR_rect.
    - apply hε.
    - intros *; apply hsnoc.
  Defined.

  Lemma invValidity {wl Γ} (VΓ : [||-v Γ]< wl >) :
    match Γ as Γ return [||-v Γ]< wl > -> Type with
    | nil => fun VΓ₀ => VΓ₀ = validEmpty
    | (A :: Γ)%list => fun VΓ₀ =>
      ∑ l (VΓ : [||-v Γ]< wl >) (VA : [Γ ||-v< l > A | VΓ]< wl >), VΓ₀ = validSnoc VΓ VA
    end VΓ.
  Proof.
    pattern Γ, VΓ. apply validity_rect.
    - reflexivity.
    - intros; do 3 eexists; reflexivity.
  Qed.

  Lemma invValidityEmpty {wl} (VΓ : [||-v ε]< wl >) : VΓ = validEmpty.
  Proof. apply (invValidity VΓ). Qed.

  Lemma invValiditySnoc {wl Γ A} (VΓ₀ : [||-v Γ ,, A ]< wl >) :
      ∑ l (VΓ : [||-v Γ]< wl >) (VA : [Γ ||-v< l > A | VΓ]< wl >), VΓ₀ = validSnoc VΓ VA.
  Proof. apply (invValidity VΓ₀). Qed.

End Inductions.

(* Tactics to instantiate validity proofs in the context with
  valid substitions *)

Definition wfCtxOfsubstS `{GenericTypingProperties}
  {wl Γ Δ σ} {VΓ : [||-v Γ]< wl >} {wfΔ : [|- Δ]< wl >} :
  [Δ ||-v σ : Γ | VΓ | wfΔ]< wl > -> [|- Δ]< wl > := fun _ => wfΔ.

Ltac instValid vσ :=
  let wfΔ := (eval unfold wfCtxOfsubstS in (wfCtxOfsubstS vσ)) in
  repeat lazymatch goal with
  | [H : typeValidity _ _ _ _ _ |- _] =>
    let X := fresh "R" H in
    try pose (X := validTy H wfΔ vσ) ;
    block H
  | [H : termValidity _ _ _ _ _ _ _ |- _] =>
    let X := fresh "R" H in
    try pose (X := validTm H wfΔ vσ) ;
    block H
  | [H : typeEqValidity _ _ _ _ _ _ _ |- _] =>
    let X := fresh "R" H in
    try pose (X := validTyEq H wfΔ vσ) ;
    block H
  | [H : termEqValidity _ _ _ _ _ _ _ _ |- _] =>
    let X := fresh "R" H in
    try pose (X := validTmEq H wfΔ vσ) ;
    block H
  end; unblock.

Ltac instValidExt vσ' vσσ' :=
  repeat lazymatch goal with
  | [H : typeValidity _ _ _ _ _ |- _] =>
    let X := fresh "RE" H in
    try pose (X := validTyExt H _ _ vσ' vσσ') ;
    block H
  | [H : termValidity _ _ _ _ _ _ _ |- _] =>
    let X := fresh "RE" H in
    try pose (X := validTmExt H _ _ vσ' vσσ') ;
    block H
  end; unblock.

Ltac instAllValid vσ vσ' vσσ' :=
  instValid vσ ;
  instValid vσ' ;
  instValidExt vσ' vσσ'.
