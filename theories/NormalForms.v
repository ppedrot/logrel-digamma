(** * LogRel.NormalForms: definition of normal and neutral forms, and properties. *)
From Coq Require Import ssrbool.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst LContexts Context.

(** ** Weak-head normal forms and neutrals. *)

Inductive whnf : term -> Type :=
  | whnf_tSort {s} : whnf (tSort s)
  | whnf_tProd {A B} : whnf (tProd A B)
  | whnf_tLambda {A t} : whnf (tLambda A t)
  | whnf_tNat : whnf tNat
  | whnf_tZero : whnf tZero
  | whnf_tSucc {n} : whnf (tSucc n)
  | whnf_tEmpty : whnf tEmpty
  | whnf_tBool : whnf tBool
  | whnf_tTrue : whnf tTrue
  | whnf_tFalse : whnf tFalse
  | whnf_tSig {A B} : whnf (tSig A B)
  | whnf_tPair {A B a b} : whnf (tPair A B a b)
  | whnf_tId {A x y} : whnf (tId A x y)
  | whnf_tRefl {A x} : whnf (tRefl A x)
  | whnf_whne {n} : whne n -> whnf n
with whne : term -> Type :=
  | whne_tRel {v} : whne (tRel v)
  | whne_tApp {n t} : whne n -> whne (tApp n t)
  | whne_tNatElim {P hz hs n} : whne n -> whne (tNatElim P hz hs n)
  | whne_tBoolElim {P hz hs n} : whne n -> whne (tBoolElim P hz hs n)
  | whne_tEmptyElim {P e} : whne e -> whne (tEmptyElim P e)
  | whne_tFst {p} : whne p -> whne (tFst p)
  | whne_tSnd {p} : whne p -> whne (tSnd p)
  | whne_tIdElim {A x P hr y e} : whne e -> whne (tIdElim A x P hr y e)
  | whne_containsne {n t} : whne t -> whne (tAlpha (nSucc n t)).

#[global] Hint Constructors whne whnf : gen_typing.

Ltac inv_whne :=
  repeat lazymatch goal with
    | H : whne _ |- _ =>
    try solve [inversion H] ; block H
  end; unblock.

Lemma neSort s : whne (tSort s) -> False.
Proof.
  inversion 1.
Qed.

Lemma nePi A B : whne (tProd A B) -> False.
Proof.
  inversion 1.
Qed.

Lemma neLambda A t : whne (tLambda A t) -> False.
Proof.
  inversion 1.
Qed.


Lemma containsnewhnf {n} t : whne t -> whnf (nSucc n t).
Proof.
  intro H.
  induction n ; cbn ; now econstructor.
Qed.


Lemma nenattoterm {n} : whne (nat_to_term n) -> False.
Proof.
  intro H.
  induction n ; cbn in * ; inversion H.
Qed.

Lemma containsnenattoterm {n} : whne (tAlpha (nat_to_term n)) -> False.
Proof.
  intro H ; inversion H ; subst ; clear H.
  revert n0 H0.
  unfold nat_to_term ; cbn.
  induction n ; cbn in * ; intros.
  - induction n0 ; cbn in *.
    + rewrite H0 in H1 ; inversion H1.
    + change (match tZero with tZero => False | _ => True end).
      now rewrite <- H0.
  - destruct n0 ; cbn in *.
    + rewrite H0 in H1 ; now inversion H1.
    + eapply IHn.
      now eapply tSucc_inj.
Qed.

Lemma whnfnattoterm t : whnf (nat_to_term t).
Proof.
  induction t  ; cbn ; now econstructor.
Qed.

Lemma nSucc_cases {k k' t t'} :
  nSucc k t = nSucc k' t' ->
  (t = t') + (t = nSucc (k' - k) t') + (t' = nSucc (k - k') t).
Proof.
  revert k' t t' ; induction k ; intros k' t t' Heq ; cbn in *.
  - left ; right.
    now rewrite PeanoNat.Nat.sub_0_r.
  - destruct k' ; cbn in *.
    + right ; now symmetry.
    + eapply IHk.
      now inversion Heq.
Qed.

Lemma nSucc_injnat {k k' t} :
  nSucc k t = nSucc k' t -> k = k'.
Proof.
  revert k' t ; induction k ; intros ; cbn in *.
  - destruct k' ; [reflexivity | cbn in *].
    induction t ; cbn in * ; inversion H.
    enough (Hyp : nSucc k' (tSucc t) = tSucc (nSucc k' t)).
    { rewrite Hyp in H1 ; now apply IHt. }
    clear ; induction k' ; [reflexivity | cbn].
    now rewrite IHk'.
  - destruct k' ; cbn in *.
    2: f_equal ; eapply IHk ; now inversion H.
    induction t ; cbn in * ; inversion H.
    enough (Hyp : nSucc k (tSucc t) = tSucc (nSucc k t)).
    { rewrite Hyp in H1 ; now apply IHt. }
    clear ; induction k ; [reflexivity | cbn].
    now rewrite IHk.
Qed.

Lemma nSuccneinj {k k' t t'} :
  whne t -> nSucc k t = nSucc k' t' -> t' = nSucc (k - k') t.
Proof.
  revert k' t t' ; induction k ; intros k' t t' Hne Heq.
  - destruct k' ; cbn in * ; [now auto | ].
    subst ; now inversion Hne.
  - destruct k' ; cbn in * ; [now auto | ].
    inversion Heq.
    now eapply IHk.
Qed.  
  

#[global] Hint Resolve neSort nePi neLambda : gen_typing.

(** ** Restricted classes of normal forms *)

Inductive isType : term -> Type :=
  | UnivType {s} : isType (tSort s)
  | ProdType { A B} : isType (tProd A B)
  | NatType : isType tNat
  | EmptyType : isType tEmpty
  | BoolType : isType tBool
  | SigType {A B} : isType (tSig A B)
  | IdType {A x y} : isType (tId A x y)
  | NeType {A}  : whne A -> isType A.

Inductive isPosType : term -> Type :=
  | UnivPos {s} : isPosType (tSort s)
  | NatPos : isPosType tNat
  | EmptyPos : isPosType tEmpty
  | BoolPos : isPosType tBool
  | IdPos {A x y} : isPosType (tId A x y)
  | NePos {A}  : whne A -> isPosType A.

Inductive isFun : term -> Type :=
  | LamFun {A t} : isFun (tLambda A t)
  | NeFun  {f} : whne f -> isFun f.

Inductive isNat : term -> Type :=
  | ZeroNat : isNat tZero
  | SuccNat {t} : isNat (tSucc t)
  | NeNat {n} : whne n -> isNat n.

Inductive isBool : term -> Type :=
  | TrueBool : isBool tTrue
  | FalseBool : isBool tFalse
  | NeBool {n} : whne n -> isBool n.

Inductive isPair : term -> Type :=
  | PairPair {A B a b} : isPair (tPair A B a b)
  | NePair {p} : whne p -> isPair p.

Definition isPosType_isType t (i : isPosType t) : isType t.
Proof. destruct i; now constructor. Defined.

Coercion isPosType_isType : isPosType >-> isType.

Definition isType_whnf t (i : isType t) : whnf t.
Proof. destruct i; now constructor. Defined.

Coercion isType_whnf : isType >-> whnf.

Definition isFun_whnf t (i : isFun t) : whnf t.
Proof. destruct i; now constructor. Defined.

Coercion isFun_whnf : isFun >-> whnf.

Definition isPair_whnf t (i : isPair t) : whnf t.
Proof. destruct i; now constructor. Defined.

Coercion isPair_whnf : isPair >-> whnf.

Definition isNat_whnf t (i : isNat t) : whnf t :=
  match i with
  | ZeroNat => whnf_tZero
  | SuccNat => whnf_tSucc
  | NeNat n => whnf_whne n
  end.

Definition isBool_whnf t (i : isBool t) : whnf t :=
  match i with
  | TrueBool => whnf_tTrue
  | FalseBool => whnf_tFalse
  | NeBool n => whnf_whne n
  end.

#[global] Hint Resolve isPosType_isType isType_whnf isFun_whnf isNat_whnf isBool_whnf isPair_whnf : gen_typing.
#[global] Hint Constructors isPosType isType isFun isNat isBool : gen_typing.

(** ** Canonical forms *)

Inductive isCanonical : term -> Type :=
  | can_tSort {s} : isCanonical (tSort s)
  | can_tProd {A B} : isCanonical (tProd A B)
  | can_tLambda {A t} : isCanonical (tLambda A t)
  | can_tNat : isCanonical tNat
  | can_tZero : isCanonical tZero
  | can_tSucc {n} : isCanonical (tSucc n)
  | can_tEmpty : isCanonical tEmpty
  | can_tBool : isCanonical tBool
  | can_tTrue : isCanonical tTrue
  | can_tFalse : isCanonical tFalse
  | can_tSig {A B} : isCanonical (tSig A B)
  | can_tPair {A B a b}: isCanonical (tPair A B a b)
  | can_tId {A x y}: isCanonical (tId A x y)
  | can_tRefl {A x}: isCanonical (tRefl A x).

#[global] Hint Constructors isCanonical : gen_typing.

(** ** Normal and neutral forms are stable by renaming *)

Section RenWhnf.

  Variable (ρ : nat -> nat).

  Lemma nSucc_ren n t : (nSucc n t)⟨ρ⟩ = nSucc n (t⟨ρ⟩).
  Proof.
    induction n ; cbn ; auto.
    now rewrite IHn.
  Qed.
  
  Lemma whne_ren t : whne t -> whne (t⟨ρ⟩).
  Proof.
    induction 1 ; cbn.
    all: try now econstructor.
    rewrite nSucc_ren.
    now econstructor.
  Qed.

  Lemma whnf_ren t : whnf t -> whnf (t⟨ρ⟩).
  Proof.
    induction 1 ; cbn.
    all: econstructor.
    now eapply whne_ren.
  Qed.

  Lemma isType_ren A : isType A -> isType (A⟨ρ⟩).
  Proof.
    induction 1 ; cbn.
    all: econstructor.
    now eapply whne_ren.
  Qed.

  Lemma isPosType_ren A : isPosType A -> isPosType (A⟨ρ⟩).
  Proof.
    destruct 1 ; cbn.
    all: econstructor.
    now eapply whne_ren.
  Qed.

  Lemma isFun_ren f : isFun f -> isFun (f⟨ρ⟩).
  Proof.
    induction 1 ; cbn.
    all: econstructor.
    now eapply whne_ren.
  Qed.

  Lemma isPair_ren f : isPair f -> isPair (f⟨ρ⟩).
  Proof.
    induction 1 ; cbn.
    all: econstructor.
    now eapply whne_ren.
  Qed.

  Lemma isCanonical_ren t : isCanonical t <~> isCanonical (t⟨ρ⟩).
  Proof.
    split.
    all: destruct t ; cbn ; inversion 1.
    all: now econstructor.
  Qed.

End RenWhnf.

#[global] Hint Resolve whne_ren whnf_ren isType_ren isPosType_ren isFun_ren isCanonical_ren : gen_typing.


Inductive alphane (wl : wfLCon) (n : nat) : term -> Type :=
  | alphane_tRel (ne : not_in_LCon wl n) : alphane wl n (tAlpha (nat_to_term n))
  | alphane_tApp {t u} : alphane wl n t -> alphane wl n (tApp t u)
  | alphane_tNatElim {P hz hs m} : alphane wl n m -> alphane wl n (tNatElim P hz hs m)
  | alphane_tBoolElim {P hz hs m} : alphane wl n m -> alphane wl n (tBoolElim P hz hs m)
  | alphane_tEmptyElim {P e} : alphane wl n e -> alphane wl n (tEmptyElim P e)
  | alphane_tFst {p} : alphane wl n p -> alphane wl n (tFst p)
  | alphane_tSnd {p} : alphane wl n p -> alphane wl n (tSnd p)
  | alphane_tIdElim {A x P hr y e} : alphane wl n e -> alphane wl n (tIdElim A x P hr y e)
  | alphane_containsne {k t} : alphane wl n t -> alphane wl n (tAlpha (nSucc k t)).


Lemma nSuccalphaneinj {wl n k k' t t'} :
  alphane wl n t -> nSucc k t = nSucc k' t' -> t' = nSucc (k - k') t.
Proof.
  revert k' t t' ; induction k ; intros k' t t' Hne Heq.
  - cbn in * ; revert t t' Hne Heq.
    induction k' ; cbn in * ; intros ; [now auto | ].
    subst ; now inversion Hne.
  - destruct k' ; cbn in * ; [now auto | ].
    inversion Heq.
    now eapply IHk.
Qed.

Lemma alphane_ren wl n t (ρ : nat -> nat) : alphane wl n t -> alphane wl n (t⟨ρ⟩).
Proof.
  induction 1 ; cbn.
  all: try now econstructor.
  - cbn ; unfold nat_to_term ; rewrite nSucc_ren ; cbn.
    now econstructor.
  - rewrite nSucc_ren ; now econstructor.
Qed.

Lemma alphane_Ltrans {wl wl' n t} (f : wl' ≤ε wl) :
  alphane wl n t -> (not_in_LCon (pi1 wl') n) -> alphane wl' n t.
Proof.
  intros Hyp ; revert wl' f ; induction Hyp ; intros wl' f Hne.
  all: now econstructor.
Qed.

Lemma alphane_backtrans  {wl wl' n t} (f : wl' ≤ε wl) :
  alphane wl' n t -> alphane wl n t.
Proof.
  intros Hyp ; revert wl f ; induction Hyp ; intros wl f.
  all: try now econstructor.
  econstructor.
  now eapply not_in_LCon_le_not_in_LCon.
Qed.

Lemma alphane_whne_false {wl n t} :
  whne t -> alphane wl n t -> False.
Proof.
  induction 1 ; intros Hyp ; try now inversion Hyp.
  - inversion Hyp ; subst.
    + symmetry in H1 ; eapply nSuccneinj in H1 ; auto.
      destruct (n0 - n) ; cbn in * ; subst ; [now inversion H | ].
      now inversion H1.
    + eapply nSuccalphaneinj in H0; eauto.
      destruct (k - n0) ; cbn in * ; subst ; auto.
      now inversion H.
Qed.    

Lemma alphane_isNat_false {wl n t} :
  alphane wl n t -> isNat t -> False.
Proof.
  intros H ; induction 1 ; try now inversion H.
  now eapply alphane_whne_false.
Qed.

Lemma alphane_nf_false {wl n t} :
  alphane wl n t -> whnf t -> False.
Proof.
  intros H ; induction 1 ; try now inversion H.
  now eapply alphane_whne_false.
Qed.
