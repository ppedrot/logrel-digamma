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
      (validSubst : forall (Δ : context) (wl' : wfLCon) (σ : nat -> term)
                           (f: wl' ≤ε wl) (wfΔ : [|- Δ]< wl' >), Type@{i})
      (eqSubst : forall (Δ : context) (wl' : wfLCon) (σ σ' : nat -> term) (f : wl' ≤ε wl)
                        (wfΔ : [|- Δ ]< wl' >), validSubst Δ wl' σ f wfΔ -> Type@{i})
    , Type@{j}.

(*  Definition VRel@{i j | i < j +} `{ta : tag} `{!WfContext ta} {wl : wfLCon} :=
    forall
      (Γ : context)
      (Δ : context)
      (wl' : wfLCon)
      (σ : nat -> term)
      (f : wl' ≤ε wl)
      (wfΔ : [|- Δ]< wl' >)
      (validSubst: Type@{i})
      (eqSubst: (nat -> term) -> validSubst -> Type@{i})
      
    , Type@{j}.
 *)

(* A VPack contains the data corresponding to the codomain of VRel seen as a functional relation *)

Module VPack.

  Record VPack@{i} `{ta : tag} `{!WfContext ta} {wl : wfLCon} {Γ : context} :=
  {
    validSubst : forall (Δ : context) (wl' : wfLCon) (σ : nat -> term)
                        (f : wl' ≤ε wl) (wfΔ : [|- Δ]< wl' >), Type@{i} ;
    eqSubst : forall (Δ : context) (wl' : wfLCon) (σ σ': nat -> term)
                     (f : wl' ≤ε wl) (wfΔ : [|- Δ ]< wl' >),
      validSubst Δ wl' σ f wfΔ -> Type@{i} ;
  }.

  Arguments VPack : clear implicits.
  Arguments VPack {_ _}.
  Arguments Build_VPack {_ _}.
End VPack.



Export VPack(VPack,Build_VPack).



Notation "[ P | Δ ||-v σ : Γ | wfΔ | f ]< wl >" := (@VPack.validSubst _ _ wl Γ P Δ _ σ f wfΔ) (at level 0, P, Δ, σ, wl, Γ, wfΔ, f at level 50).
Notation "[ P | Δ ||-v σ ≅ σ' : Γ | wfΔ | vσ | f ]< wl >" := (@VPack.eqSubst _ _ wl Γ P Δ _ σ σ' f wfΔ vσ) (at level 0, P, Δ, σ, σ', wl, Γ, wfΔ, vσ, f at level 50).

(* An VPack it adequate wrt. a VRel when its three unpacked components are *)
#[universes(polymorphic)] Definition VPackAdequate@{i j} `{ta : tag} `{!WfContext ta} {wl : wfLCon} {Γ : context}
  (R : VRel@{i j}) (P : VPack@{i} wl Γ) : Type@{j} :=
  R Γ (P.(VPack.validSubst)) (P.(VPack.eqSubst)).

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
Notation "[ R | Δ ||-v σ : Γ | RΓ | wfΔ | f ]< wl >"           := (RΓ.(@VAd.pack _ _ wl Γ R).(VPack.validSubst) Δ _ σ f wfΔ) (at level 0, R, Δ, σ, wl, Γ, RΓ, wfΔ, f at level 50).
Notation "[ R | Δ ||-v σ ≅ σ' : Γ | RΓ | wfΔ | vσ | f ]< wl >" := (RΓ.(@VAd.pack _ _ wl Γ R).(VPack.eqSubst) Δ _ σ σ' f wfΔ vσ) (at level 0, R, Δ, σ, σ', wl, Γ, RΓ, wfΔ, vσ, f at level 50).

Record typeValidity@{u i j k l} `{ta : tag} `{!WfContext ta}
  `{!WfType ta} `{!Typing ta} `{!ConvType ta}
  `{!ConvTerm ta} `{!ConvNeuConv ta} `{!RedType ta} `{!RedTerm ta}
  {wl : wfLCon} {Γ : context} {VΓ : VPack@{u} wl Γ}
  {l : TypeLevel} {A : term} :=
  {
    validTy : forall {Δ : context} {wl': wfLCon} {σ : nat -> term}
                     (f : wl' ≤ε wl)
                     (wfΔ : [|- Δ ]< wl' >)
                     (vσ : [ VΓ | Δ ||-v σ : Γ | wfΔ | f ]< wl >),
      WLogRel@{i j k l} l wl' Δ (A [ σ ]);
    validTyExt : forall {Δ : context} {wl': wfLCon} {σ σ' : nat -> term}
                        (f : wl' ≤ε wl)
                        (wfΔ : [|- Δ ]< wl' >)
                        (vσ  : [ VΓ | Δ ||-v σ  : Γ | wfΔ | f ]< wl >)
                        (vσ' : [ VΓ | Δ ||-v σ' : Γ | wfΔ | f ]< wl >)
                        (vσσ' : [ VΓ | Δ ||-v σ ≅ σ' : Γ | wfΔ | vσ | f ]< wl >)
    , WLogRelEq@{i j k l} l wl' Δ (A [ σ ]) (A [ σ' ]) (validTy f wfΔ vσ)
  }.

Arguments typeValidity : clear implicits.
Arguments typeValidity {_ _ _ _ _ _ _ _ _}.

Notation "[ P | Γ ||-v< l > A ]< wl >" := (typeValidity wl Γ P l A) (at level 0, P, wl, Γ, l, A at level 50).



Definition emptyValidSubst `{ta : tag} `{!WfContext ta} {wl : wfLCon} :
  forall (Δ : context) (wl' : wfLCon) (σ : nat -> term) (f : wl' ≤ε wl) (wfΔ : [|- Δ]< wl' >), Type :=
  fun _ _ _ _ _ => unit.
Definition emptyEqSubst@{u} `{ta : tag} `{!WfContext ta} {wl : wfLCon} :
  forall (Δ : context) (wl' : wfLCon) (σ σ' : nat -> term) (f : wl' ≤ε wl) (wfΔ : [|- Δ]< wl' >),
    emptyValidSubst@{u} Δ wl' σ f wfΔ -> Type@{u} := fun _ _ _ _ _ _ _ => unit.

Definition emptyVPack `{ta : tag} `{!WfContext ta} {wl : wfLCon} : VPack wl ε :=
  Build_VPack _ _ emptyValidSubst emptyEqSubst.

Section snocValid.
  Universe u i j k l.
  Context `{ta : tag} `{!WfContext ta}
  `{!WfType ta} `{!Typing ta} `{!ConvType ta}
  `{!ConvTerm ta} `{!ConvNeuConv ta} `{!RedType ta} `{!RedTerm ta}
  {wl : wfLCon} {Γ : context} {VΓ : VPack@{u} wl Γ} {A : term} {l : TypeLevel}
  {vA : typeValidity@{u i j k l} wl Γ VΓ l A (* [ VΓ | Γ ||-v< l > A ]< wl > *)}.


  Definition snocValidSubst {Δ : context} {wl' : wfLCon} {σ : nat -> term} {f : wl' ≤ε wl}
    {wfΔ : [|- Δ]< wl' >} : Type@{u}.
  Proof.
    unshelve eapply sigT@{u k}.
    1: exact [ VΓ | Δ ||-v ↑ >> σ : Γ | wfΔ | f ]< wl >.
    1: exact (fun validTail => W[ Δ ||-< l > σ var_zero : A[↑ >> σ] | validTy vA f wfΔ validTail ]< wl' >).
    Defined.

  Arguments snocValidSubst : clear implicits.
  
  Definition snocEqSubst {Δ : context} {wl' : wfLCon} {σ σ' : nat -> term} {f : wl' ≤ε wl}
                 {wfΔ : [|- Δ]< wl' >} {vσ : snocValidSubst Δ wl' σ f wfΔ} : Type@{u}.
  Proof.
    unshelve eapply prod@{u k}.
    - exact [ VΓ | Δ ||-v ↑ >> σ ≅ ↑ >> σ' : Γ | wfΔ | projT1@{u k} vσ | f ]< wl >.
    - exact (W[ Δ ||-< l > σ var_zero ≅ σ' var_zero : A[↑ >> σ] | validTy vA f wfΔ (projT1@{u k} vσ) ]< wl' >).
  Defined.
  
(*   Record snocValidSubst {Δ : context} {wl' : wfLCon} {σ : nat -> term} {f : wl' ≤ε wl}
    {wfΔ : [|- Δ]< wl' >} :=
   { validTail : [ VΓ | Δ ||-v ↑ >> σ : Γ | wfΔ | f ]< wl > ;
     validHead : W[ Δ ||-< l > σ var_zero : A[↑ >> σ] | validTy vA f wfΔ validTail ]< wl' >
    }.

  Arguments snocValidSubst : clear implicits.

  Record snocEqSubst {Δ : context} {wl' : wfLCon} {σ σ' : nat -> term} {f : wl' ≤ε wl}
    {wfΔ : [|- Δ]< wl' >} {vσ : snocValidSubst Δ wl' σ f wfΔ} : Type :=
    {
      eqTail : [ VΓ | Δ ||-v ↑ >> σ ≅ ↑ >> σ' : Γ | wfΔ | validTail vσ | f ]< wl > ;
      eqHead : W[ Δ ||-< l > σ var_zero ≅ σ' var_zero : A[↑ >> σ] | validTy vA f wfΔ (validTail vσ) ]< wl' >
    }.
 *)

  Definition snocVPack := Build_VPack@{u (* max(u,k) *)} wl (Γ ,, A) snocValidSubst (@snocEqSubst).
  
  
  
End snocValid.


Arguments snocValidSubst : clear implicits.
Arguments snocValidSubst {_ _ _ _ _ _ _ _ _}.

Arguments snocEqSubst : clear implicits.
Arguments snocEqSubst {_ _ _ _ _ _ _ _ _}.

Arguments snocVPack : clear implicits.
Arguments snocVPack {_ _ _ _ _ _ _ _ _}.

Unset Elimination Schemes.

Definition transport@{k} {A B : Type@{k}} (e : eq A B) (x : A) : B.
Proof.
  now destruct e.
Defined.

Inductive VR@{i j k l} `{ta : tag}
  `{WfContext ta} `{WfType ta} `{Typing ta}
  `{ConvType ta} `{ConvTerm ta} `{ConvNeuConv ta}
  `{RedType ta} `{RedTerm ta} {wl : wfLCon} : VRel@{k l} (wl := wl)  :=
| VREmpty : forall (sub : forall Δ wl' σ f wfΔ, Type@{k})
                  (ext : forall Δ wl' σ σ' f wfΔ Hyp, Type@{k})
                   (Hsub: forall Δ wl' σ f wfΔ, sub Δ wl' σ f wfΔ = unit)
                   (Hext : forall Δ wl' σ σ' f wfΔ Hyp, ext Δ wl' σ σ' f wfΔ Hyp = unit),
    VR ε sub ext
| VRSnoc : forall {Γ A l} (sub : forall Δ wl' σ f wfΔ, Type@{k})
                  (ext : forall Δ wl' σ σ' f wfΔ Hyp, Type@{k})
                  (VΓ : VPack@{k} wl Γ)
                  (VΓad : VPackAdequate@{k l} VR VΓ)
                  (VA : typeValidity@{k i j k l} wl Γ VΓ l A (*[ VΓ | Γ ||-v< l > A ]*))
                  (Hsub: forall Δ wl' σ f wfΔ, sub Δ wl' σ f wfΔ =
                                                 snocValidSubst _ _ _ _ _ _ Δ wl' σ f wfΔ)
                  (Hext : forall Δ wl' σ σ' f wfΔ Hyp,
                      ext Δ wl' σ σ' f wfΔ Hyp =
                        snocEqSubst _ Γ VΓ _ _ VA Δ wl' σ σ' f wfΔ
                          (transport (Hsub Δ wl' σ f wfΔ) Hyp)),
    VR (Γ ,, A) sub ext.


(*
Definition VREmpty'@{i j k l} `{ta : tag}
  `{WfContext ta} `{WfType ta} `{Typing ta}
  `{ConvType ta} `{ConvTerm ta} `{ConvNeuConv ta}
  `{RedType ta} `{RedTerm ta} {wl : wfLCon} : VR@{i j k l} (wl := wl) ε emptyValidSubst@{k} emptyEqSubst.
Proof.
  eapply VREmpty.
  - intros ; now econstructor.
  - intros ; now econstructor.
Defined. *)

Definition VRSnoc'@{i j k l} `{ta : tag}
  `{WfContext ta} `{WfType ta} `{Typing ta}
  `{ConvType ta} `{ConvTerm ta} `{ConvNeuConv ta}
  `{RedType ta} `{RedTerm ta} {wl : wfLCon} {Γ A l}
  (VΓ : VPack@{k} wl Γ)
  (VΓad : VPackAdequate@{k l} VR@{i j k l} VΓ)
  (VA : typeValidity@{k i j k l} wl Γ VΓ l A (*[ VΓ | Γ ||-v< l > A ]*)) :
    VR@{i j k l} (Γ ,, A) (snocValidSubst@{k i j k l} wl Γ VΓ A l VA)
      (snocEqSubst@{k i j k l} wl Γ VΓ A l VA).
Proof.
  intros ; unshelve eapply VRSnoc.
  all: easy.
Defined.


Set Elimination Schemes.

Notation "[||-v Γ ]< wl >"                             := [ VR | ||-v Γ ]< wl > (at level 0, wl, Γ at level 50).
Notation "[ Δ ||-v σ : Γ | VΓ | wfΔ | f ]< wl >"           := [ VR | Δ ||-v σ : Γ | VΓ | wfΔ | f ]< wl >  (at level 0, Δ, σ, wl, Γ, VΓ, wfΔ, f at level 50).
Notation "[ Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | vσ | f ]< wl >" := [ VR | Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | vσ | f ]< wl > (at level 0, Δ, σ, σ', wl, Γ, VΓ, wfΔ, vσ, f at level 50).
Notation "[ Γ ||-v< l > A | VΓ ]< wl >"                := [ VΓ | Γ ||-v< l > A ]< wl > (at level 0, wl, Γ, l , A, VΓ at level 50).


Section MoreDefs.
  Context `{ta : tag} `{WfContext ta} `{WfType ta} `{Typing ta}
  `{ConvType ta} `{ConvTerm ta} `{ConvNeuConv ta} `{RedType ta} `{RedTerm ta}.

  Definition validEmpty {wl }
    {sub : forall Δ wl' σ f wfΔ, Type}
    {ext : forall Δ wl' σ σ' f wfΔ Hyp, Type}
    (Hsub: forall (Δ : context) (wl' : wfLCon) (σ : nat -> term)
                  (f : wl' ≤ε wl) (wfΔ : [|- Δ]< wl' >),
        sub Δ wl' σ f wfΔ = unit)
    (Hext : forall (Δ : context) (wl' : wfLCon) (σ σ' : nat -> term)
                   (f : wl' ≤ε wl) (wfΔ : [|- Δ]< wl' >)
                   (Hyp : sub Δ wl' σ f wfΔ),
        ext Δ wl' σ σ' f wfΔ Hyp = unit) :
    [VR| ||-v ε ]< wl >.
  Proof.
    unshelve eapply Build_VAdequate.
    - unshelve econstructor ; assumption.
    - now eapply VREmpty.
  Defined.

  Definition validSnoc {wl Γ} {A l}
    (VΓ : [VR| ||-v Γ]< wl >) (VA : (typeValidity wl Γ VΓ l A))
    {sub : forall Δ wl' σ f wfΔ, Type}
    {ext : forall Δ wl' σ σ' f wfΔ Hyp, Type}
    (Hsub: forall (Δ : context) (wl' : wfLCon) (σ : nat -> term)
                  (f : wl' ≤ε wl) (wfΔ : [|- Δ]< wl' >),
        sub Δ wl' σ f wfΔ = snocValidSubst _ _ _ _ _ _ Δ wl' σ f wfΔ)
    (Hext : forall (Δ : context) (wl' : wfLCon) (σ σ' : nat -> term)
                   (f : wl' ≤ε wl) (wfΔ : [|- Δ]< wl' >)
                   (Hyp : sub Δ wl' σ f wfΔ),
        ext Δ wl' σ σ' f wfΔ Hyp =
          snocEqSubst _ Γ VΓ _ _ VA Δ wl' σ σ' f wfΔ
            (transport (Hsub Δ wl' σ f wfΔ) Hyp)) :
    [VR | ||-v Γ ,, A ]< wl >.
  Proof.
    unshelve eapply Build_VAdequate.
    - unshelve econstructor ; assumption.
    - cbn ; now unshelve eapply (VRSnoc _ _ VΓ VΓ VA). 
  Defined.

  Definition validSnoc' {wl Γ} {A l}
    (VΓ : [VR| ||-v Γ]< wl >) (VA : (typeValidity wl Γ VΓ l A)) :
    [VR | ||-v Γ ,, A ]< wl >.
  Proof.
    unshelve eapply Build_VAdequate.
    - unshelve eapply snocVPack.
      3: eassumption.
    - unshelve eapply (VRSnoc _ _ VΓ VΓ VA).
      1,2: intros ; reflexivity.
  Defined.


  Record termValidity@{i j k l} {wl Γ l} {t A : term}
    {VΓ : [VR@{i j k l} (wl := wl) | ||-v Γ]< wl >}
    {VA : typeValidity@{k i j k l} wl Γ VΓ l A (*[Γ ||-v<l> A |VΓ]< wl >*)} : Type :=
    {
      validTm : forall {Δ wl' σ} (f : wl' ≤ε wl)
                       (wfΔ : [|- Δ]< wl' >) (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ | f ]< wl >),
        W[Δ ||-<l> t[σ] : A[σ] | validTy VA f wfΔ Vσ ]< wl' > ;
      validTmExt : forall {Δ : context} {wl' : wfLCon} {σ σ' : nat -> term}
                          (f : wl' ≤ε wl)
                          (wfΔ : [|- Δ ]< wl' >)
                          (Vσ  : [Δ ||-v σ  : Γ | VΓ | wfΔ | f ]< wl >)
                          (Vσ' : [ Δ ||-v σ' : Γ | VΓ | wfΔ | f ]< wl >)
                          (Vσσ' : [ Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | Vσ | f ]< wl >),
        W[Δ ||-<l> t[σ] ≅ t[σ'] : A[σ] | validTy VA f wfΔ Vσ ]< wl' >
    }.

  Record typeEqValidity@{i j k l} {wl Γ l} {A B : term}
    {VΓ : [VR@{i j k l}| ||-v Γ]< wl >}
    {VA : typeValidity@{k i j k l} wl Γ VΓ l A (*[Γ ||-v<l> A |VΓ]< wl >*)} : Type :=
    {
      validTyEq : forall {Δ wl' σ}
                          (f : wl' ≤ε wl)
                          (wfΔ : [|- Δ]< wl' >) (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ | f ]< wl >),
        W[Δ ||-<l> A[σ] ≅ B[σ] | validTy VA f wfΔ Vσ]< wl' >
    }.

  Record termEqValidity@{i j k l} {wl Γ l} {t u A : term}
    {VΓ : [VR@{i j k l}| ||-v Γ]< wl >}
    {VA : typeValidity@{k i j k l} wl Γ VΓ l A (*[Γ ||-v<l> A |VΓ]< wl >*)} : Type :=
    {
      validTmEq : forall {Δ wl' σ} (f : wl' ≤ε wl)
                         (wfΔ : [|- Δ]< wl' >)
                         (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ | f ]< wl >),
        W[Δ ||-<l> t[σ] ≅ u[σ] : A[σ] | validTy VA f wfΔ Vσ]< wl' >
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
      validRed : forall {Δ wl' σ} (f : wl' ≤ε wl)
        (wfΔ : [|- Δ]< wl' >) (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ | f ]< wl >),
        [Δ |- t[σ] :⤳*: u[σ] : A[σ]]< wl' >
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

  Set Printing Universes.

  
  Theorem VR_rect@{h i j k l} {wl : wfLCon}
    (P : forall {Γ : context}
                {vSubst}
                 {vSubstExt},
        VR@{h i j k} (wl := wl) Γ vSubst vSubstExt -> Type@{l})
    (hε : forall {vSubst vSubstExt} Hsub Hext,
        P (VREmpty@{h i j k} vSubst vSubstExt Hsub Hext))
    (hsnoc : forall {Γ: context} {A l} {vSubst vSubstExt}
                    (VΓ : VPack@{j} wl Γ) (VΓad : VPackAdequate@{j k} VR@{h i j k} VΓ)
                    {VA} Hsub Hext,
        P VΓad ->
        P (VRSnoc@{h i j k} (A := A) (l := l) vSubst vSubstExt VΓ VΓad VA Hsub Hext)) :
    forall {Γ : context} {vSubst vSubstExt}
           (VΓ : VR@{h i j k} Γ vSubst vSubstExt), P VΓ.
  Proof.
    fix ih 4.
    destruct VΓ; [eapply hε | apply hsnoc].
    now unshelve eapply ih.
  Defined.

  
  Theorem VR_inv {wl Γ vSubst vSubstExt}
    (VΓ : VR (wl := wl) Γ vSubst vSubstExt) :
    match Γ as Γ return (VR Γ vSubst vSubstExt)  -> Type with
    | nil => fun VΓ₀ =>
               ∑ Hsub Hext, VΓ₀ = VREmpty vSubst vSubstExt Hsub Hext
    | (A :: Γ)%list => fun (VΓ₀ : VR _ _ _) =>
                         ∑ l (VΓ' : VPack wl Γ) (VΓad : VPackAdequate VR VΓ')
      (VA : typeValidity wl Γ VΓ' l A) Hsub Hext,
      VΓ₀ = VRSnoc (Γ := Γ) (wl := wl) (A := A) vSubst vSubstExt VΓ' VΓad VA Hsub Hext
    end VΓ .
  Proof.
    destruct Γ.
    1,2: refine (match VΓ with
            | VREmpty _ _ _ _ => _
            | VRSnoc _ _ _ _ _ _ _ => _
              end).
    2,3: intros X x ; easy. 
    all: repeat (unshelve eexists _ ; [assumption | ]).
    all: reflexivity.
  Defined.

  Corollary invValidity {wl Γ}
    (VΓ : [||-v Γ]< wl >) :
  match Γ as Γ return [||-v Γ]< wl > -> Type with
  | nil => fun VΓ₀ =>
             ∑ Hsub Hext, VΓ₀ = Build_VAdequate VΓ₀.(VAd.pack) (VREmpty _ _ Hsub Hext)
  | (A :: Γ)%list =>
      fun VΓ₀ =>
        ∑ l VΓ' VA Hsub Hext,
        VΓ₀ = validSnoc (A := A) (l := l) (ext := VΓ₀.(VAd.pack).(VPack.eqSubst)) VΓ' VA  Hsub Hext
    end VΓ.
  Proof.
    destruct VΓ as [[sub ext] GAd].
    destruct Γ ; cbn in *.
    1,2: refine (match GAd with
            | VREmpty vSubst vExt Hsub Hext => _
            | VRSnoc sub ext VG VGAd VA Hsub Hext => _
                 end).
    2,3: intros X x ; easy.
    all: repeat (unshelve eexists _ ; [assumption | ]).
    1: reflexivity.
    exists (Build_VAdequate _ VGAd), VA, Hsub, Hext.
    reflexivity.
  Defined.
    

  Theorem validity_rect {wl}
    (P : forall {Γ : context}, [||-v Γ]< wl > -> Type)
    (hε : forall sub ext Hsub Hext,
        P (Γ := ε) (validEmpty (sub := sub) (ext := ext) Hsub Hext))
    (hsnoc : forall {Γ A l} (VΓ : [||-v Γ]< wl >) (VA : [Γ ||-v< l > A | VΓ]< wl >)
      sub ext Hsub Hext,
        P VΓ -> P (validSnoc VΓ VA (sub := sub) (ext := ext) Hsub Hext)) :
    forall {Γ : context} (VΓ : [||-v Γ]< wl >), P VΓ.
  Proof.
    cbn.
    intros Γ [[s eq] VΓad]; revert Γ s eq VΓad.
    cbn.
    apply VR_rect.
    - cbn ; intros.
      now apply hε.
    - intros * Hyp. cbn in *.
      unshelve eapply hsnoc in Hyp.
      5,6,7: eassumption.
      exact Hyp.
  Defined.
  
 (* Lemma invValidity {wl Γ} (VΓ : [||-v Γ]< wl >) :
    match Γ as Γ return [||-v Γ]< wl > -> Type with
    | nil => fun VΓ₀ => VΓ₀ = validEmpty
    | (A :: Γ)%list => fun VΓ₀ =>
      ∑ l (VΓ : [||-v Γ]< wl >) (VA : [Γ ||-v< l > A | VΓ]< wl >), VΓ₀ = validSnoc VΓ VA
    end VΓ.
  Proof.
    pattern Γ, VΓ. apply validity_rect.
    - reflexivity.
    - intros; do 3 eexists; reflexivity.
  Qed. *)

 (* Lemma invValidityEmpty {wl} (VΓ : [||-v ε]< wl >) : VΓ = validEmpty.
  Proof. apply (invValidity VΓ). Qed.

  Lemma invValiditySnoc {wl Γ A} (VΓ₀ : [||-v Γ ,, A ]< wl >) :
      ∑ l (VΓ : [||-v Γ]< wl >) (VA : [Γ ||-v< l > A | VΓ]< wl >), VΓ₀ = validSnoc VΓ VA.
  Proof. apply (invValidity VΓ₀). Qed.
*)
End Inductions.

(* Tactics to instantiate validity proofs in the context with
  valid substitions *)

Definition wfCtxOfsubstS `{GenericTypingProperties}
  {wl Γ Δ wl' σ} {f : wl' ≤ε wl} {VΓ : [||-v Γ]< wl >} {wfΔ : [|- Δ]< wl' >} :
  [Δ ||-v σ : Γ | VΓ | wfΔ | f ]< wl > -> [|- Δ]< wl' > := fun _ => wfΔ.

Ltac instValid vσ :=
  let wfΔ := (eval unfold wfCtxOfsubstS in (wfCtxOfsubstS vσ)) in
  repeat lazymatch goal with
  | [H : typeValidity _ _ _ _ _ |- _] =>
    let X := fresh "R" H in
    try pose (X := validTy H _ wfΔ vσ) ;
    block H
  | [H : termValidity _ _ _ _ _ _ _ |- _] =>
    let X := fresh "R" H in
    try pose (X := validTm H _ wfΔ vσ) ;
    block H
  | [H : typeEqValidity _ _ _ _ _ _ _ |- _] =>
    let X := fresh "R" H in
    try pose (X := validTyEq H _ wfΔ vσ) ;
    block H
  | [H : termEqValidity _ _ _ _ _ _ _ _ |- _] =>
    let X := fresh "R" H in
    try pose (X := validTmEq H _ wfΔ vσ) ;
    block H
  end; unblock.

Ltac instValidExt vσ' vσσ' :=
  repeat lazymatch goal with
  | [H : typeValidity _ _ _ _ _ |- _] =>
    let X := fresh "RE" H in
    try pose (X := validTyExt H _ _ _ vσ' vσσ') ;
    block H
  | [H : termValidity _ _ _ _ _ _ _ |- _] =>
    let X := fresh "RE" H in
    try pose (X := validTmExt H _ _ _ vσ' vσσ') ;
    block H
  end; unblock.

Ltac instAllValid vσ vσ' vσσ' :=
  instValid vσ ;
  instValid vσ' ;
  instValidExt vσ' vσσ'.

Lemma VPack_Ltrans `{ta : tag} `{!WfContext ta} {wl wl' Γ} : (wl' ≤ε wl) -> VPack wl Γ -> VPack wl' Γ.
Proof.
  intros f [H1 H2] ; unshelve econstructor.
  - intros ? wl'' s f' wfd ; unshelve eapply H1.
    3,5: eassumption.
    now eapply wfLCon_le_trans.
  - intros ? wl'' ?? f' ? Hyp ; cbn in *.
    unshelve eapply (H2 _ _ σ σ' _ _).
    5: eassumption.
Defined.

Lemma Validity_Ltrans `{ta : tag}
  `{WfContext ta} `{WfType ta} `{Typing ta}
  `{ConvType ta} `{ConvTerm ta} `{ConvNeuConv ta}
  `{RedType ta} `{RedTerm ta} {l Γ A wl wl' P} (f: wl' ≤ε wl) :
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
Lemma test @{i j k l} `{ta : tag}
  `{WfContext ta} `{WfType ta} `{Typing ta}
  `{ConvType ta} `{ConvTerm ta} `{ConvNeuConv ta}
  `{RedType ta} `{RedTerm ta} {wl wl' : wfLCon} (f : wl' ≤ε wl) :
  forall
    (Γ : context)
    (Δ : context)
    (wl'' : wfLCon)
    (σ : nat -> term)
    (f' : wl'' ≤ε wl')
    (wfΔ : [|- Δ]< wl'' >)
    (validSubst: Type@{i})
    (eqSubst: (nat -> term) -> validSubst -> Type@{i}),
    VR@{i j k l} Γ Δ wl'' σ (f' •ε f) wfΔ validSubst eqSubst ->
    VR@{i j k l} Γ Δ wl'' σ f' wfΔ validSubst eqSubst.
Proof.
  intros * Hyp.
  induction Hyp as [ | ? ? ? ? wl'' ? f''].
  - econstructor.
  - assert ((snocValidSubst@{k i j k l} wl Γ VΓ A l VA Δ wl'' σ f'' wfΔ) =
              (snocValidSubst@{k i j k l} wl' Γ (VPack_Ltrans f VΓ) A l (Validity_Ltrans f VA) Δ wl'' σ f' wfΔ)).
    destruct VΓ, VA ; cbn.
    unfold Validity_Ltrans ; cbn.
    Set Printing Implicit.
*)
