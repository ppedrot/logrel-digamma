(** * LogRel.UntypedReduction: untyped reduction, used to define algorithmic typing.*)
From Coq Require Import CRelationClasses.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations LContexts Context NormalForms Weakening.

(** ** Reductions *)

(** *** One-step reduction. *)

Inductive OneRedAlg  {l : wfLCon} : term -> term -> Type :=
| BRed {A a t} :
    [ tApp (tLambda A t) a ⤳ t[a..] ]< l >
| appSubst {t u a} :
    [ t ⤳ u ]< l > ->
    [ tApp t a ⤳ tApp u a ]< l >
| natElimSubst {P hz hs n n'} :
    [ n ⤳ n' ]< l > ->
    [ tNatElim P hz hs n ⤳ tNatElim P hz hs n' ]< l >
| natElimZero {P hz hs} :
    [ tNatElim P hz hs tZero ⤳ hz ]< l >
| natElimSucc {P hz hs n} :
    [ tNatElim P hz hs (tSucc n) ⤳ tApp (tApp hs n) (tNatElim P hz hs n) ]< l >
| emptyElimSubst {P e e'} :
    [e ⤳ e']< l > ->
    [tEmptyElim P e ⤳ tEmptyElim P e']< l >     
| boolElimSubst {P hz hs n n'} :
    [ n ⤳ n' ]< l > ->
    [ tBoolElim P hz hs n ⤳ tBoolElim P hz hs n' ]< l >
| boolElimTrue {P ht hf} :
    [ tBoolElim P ht hf tTrue ⤳ ht ]< l >
| boolElimFalse {P ht hf} :
  [ tBoolElim P ht hf tFalse ⤳ hf ]< l >
| alphaSubst {n n' k} :
  [ n ⤳ n' ]< l > -> [ tAlpha (nSucc k n) ⤳ tAlpha (nSucc k n') ]< l >
| alphaRed {n b} : in_LCon (pi1 l) n b ->
                   [ tAlpha (nat_to_term n) ⤳ bool_to_term b]< l >   
| fstSubst {p p'} :
    [ p ⤳ p']< l > ->
    [ tFst p ⤳ tFst p']< l >
| fstPair {A B a b} :
    [ tFst (tPair A B a b) ⤳ a ]< l >
| sndSubst {p p'} :
    [ p ⤳ p']< l > ->
    [ tSnd p ⤳ tSnd p']< l >
| sndPair {A B a b} :
    [ tSnd (tPair A B a b) ⤳ b ]< l >
| idElimRefl {A x P hr y A' z} :
  [ tIdElim A x P hr y (tRefl A' z) ⤳ hr ]< l >
| idElimSubst {A x P hr y e e'} :
  [e ⤳ e']< l > ->
  [ tIdElim A x P hr y e ⤳ tIdElim A x P hr y e' ]< l >

where "[ t ⤳ t' ]< l >" := (@OneRedAlg l t t') : typing_scope.

(* Keep in sync with OneRedTermDecl! *)

(** *** Multi-step reduction *)

Inductive RedClosureAlg {l} : term -> term -> Type :=
  | redIdAlg {t} :
    [ t ⤳* t ]< l >
  | redSuccAlg {t t' u} :
    [ t ⤳ t']< l > ->
    [ t' ⤳* u ]< l > ->
    [ t ⤳* u ]< l >
  where "[ t ⤳* t' ]< l >" := (RedClosureAlg (l := l) t t') : typing_scope.

#[export] Instance RedAlgTrans {l} : PreOrder (RedClosureAlg (l := l)).
  Proof.
    split.
    - now econstructor.
    - intros * ; induction 1.
      1: easy.
      intros.
      now econstructor.
  Qed.

(** ** Properties *)

(** *** Weak-head normal forms do not reduce *)

Ltac inv_whne :=
  match goal with [ H : whne _ |- _ ] => inversion H end.

Ltac inv_alphane :=
  match goal with [ H : alphane _ _ _ |- _ ] => inversion H end.


Lemma whne_nored {l} n u :
  whne n -> [n ⤳ u]< l > -> False.
Proof.
  intros ne red.
  induction red in ne |- *.
  all: inversion ne ; subst ; clear ne.
  2: auto.
  all: try now inv_whne.
  1:{ eapply nSuccneinj in H ; auto ; subst.
      destruct (n0 - k) ; cbn in * ; [now apply IHred | ].
      now inversion red.
  }
  clear i ; revert n0 H ; induction n ; cbn in * ; intros.
  - destruct n0.
    * inversion H0 ; subst ; simpl in H ;  rewrite H in H0 ; now inversion H0.
    * change (match nSucc (S n0) t with | tSucc _ => False | _ => True end).
      now rewrite H.
  - induction n0 ; cbn in *.
    * rewrite H in H0 ; inversion H0.
    * apply (IHn n0) ; now apply tSucc_inj.
Qed.

Lemma whnf_nored {l} n u :
  whnf n -> [n ⤳ u]< l > -> False.
Proof.
  intros nf red.
  induction red in nf |- *.
  all: try (inversion nf; subst; inv_whne; subst; apply IHred; now constructor).
  all: inversion nf; subst ; inv_whne; subst; try now inv_whne.
  - eapply nSuccneinj in H0 ; auto ; subst.
    destruct (n0 - k) ; cbn in * ; now apply IHred ; constructor.
  - now eapply containsnenattoterm.
Qed.

Lemma alphane_nored {l n} m u :
  alphane l n m -> [m ⤳ u]< l > -> False.
Proof.
  intros ne red.
  induction red in ne |- *.
  all: inversion ne ; subst ; clear ne.
  2: auto.
  all: try now inv_alphane.
  - unfold nat_to_term in H0.
    assert (Hyp : ∑ k', n0 = nSucc k' tZero).
    { clear - H0.
      revert n H0 ; induction k ; cbn ; intros ; [now exists n | ].
      destruct n ; cbn in * ; [now inversion H0 | ].
      inversion H0 ; subst.
      now eapply IHk.
    }
    destruct Hyp as [k' Heq] ; subst.
    destruct k' ; cbn in * ; now inversion red.
  - eapply nSuccalphaneinj in H ; eauto ; subst.
    destruct (k0 - k) ; cbn in * ; [now apply IHred | ].
    now inversion red.
  - eapply notinLConnotinLCon ; [eassumption | ].
    eapply nattoterminj in H0 ; subst.
    eassumption.
  - pose proof (Hyp := nSuccalphaneinj H0 H).
    destruct (k - n0) ; cbn in * ; [subst ; now inv_alphane | now inversion Hyp].
Qed.

(** *** Determinism of reduction *)

Lemma ored_det {l t u v} :
  [t ⤳ u]< l > -> [t ⤳ v]< l > ->
  u = v.
Proof.
  intros red red'.
  induction red in v, red' |- *.
  - inversion red' ; subst ; clear red'.
    + reflexivity.
    + exfalso.
      eapply whnf_nored.
      2: eassumption.
      now econstructor.
  - inversion red' ; subst ; clear red'.
    + exfalso.
      eapply whnf_nored.
      2: eassumption.
      now econstructor.
    + f_equal.
      eauto.
  - inversion red'; subst.
    2,3: exfalso; eapply whnf_nored; tea; constructor.
    f_equal; eauto.
  - inversion red'; try reflexivity; subst.
    exfalso; eapply whnf_nored; tea; constructor.
  - inversion red'; try reflexivity; subst.
    exfalso; eapply whnf_nored; tea; constructor.
  - inversion red'; subst.
    f_equal; eauto.
  - inversion red'; subst; clear red'.
    1: f_equal; now eapply IHred.
    all: exfalso; eapply whnf_nored; tea; constructor.
  - inversion red'; try reflexivity; subst.
    exfalso; eapply whnf_nored; tea; constructor.
  - inversion red'; try reflexivity; subst.
    exfalso; eapply whnf_nored; tea; constructor.
  - inversion red' ; subst.
    + destruct (nSucc_cases H) as [ [e | e] | e] ; subst.
      * eapply IHred in H0 ; subst.
        apply nSucc_injnat in H ; now subst.
      * remember (k - k0) as j ; destruct j ; cbn in *.
        -- apply IHred in H0 ; subst.
           apply nSucc_injnat in H ; now subst.
        -- now inversion H0.
      * remember (k0 - k) as j ; destruct j ; cbn in *.
        -- apply IHred in H0 ; subst.
           apply nSucc_injnat in H ; now subst.
        -- now inversion red.
    + exfalso ; eapply whnf_nored ; [ | exact red].
      unfold nat_to_term in H ; destruct (nSucc_cases H) as [ [e | e] | e] ; subst.
      * now constructor.
      * remember (k - n0) as j ; destruct j ; cbn in * ; subst.
        -- now constructor.
        -- now inversion e.
      * remember (n0 - k) as j ; destruct j ; cbn in * ; subst.
        all: now constructor.
  - inversion red' ; subst.
    + exfalso ; eapply whnf_nored ; [ | exact H0].
      unfold nat_to_term in H ; destruct (nSucc_cases H) as [ [e | e] | e] ; subst.
      * now constructor.
      * remember (n - k) as j ; destruct j ; cbn in * ; subst.
        all: now constructor.
      * remember (k - n) as j ; destruct j ; cbn in * ; subst.
        -- now constructor.
        -- now inversion e.
    + erewrite (uniqueinLCon (pi2 l) i) ; trivial.
      rewrite (nattoterminj H) in H0 ; assumption.
  - inversion red'; subst; clear red'.
    1: f_equal; now eapply IHred.
    all: exfalso; eapply whnf_nored; tea; constructor.
  - inversion red'; subst; try reflexivity.
    exfalso; eapply whnf_nored; tea; constructor.
  - inversion red'; subst; clear red'.
    1: f_equal; now eapply IHred.
    exfalso; eapply whnf_nored; tea; constructor.
  - inversion red'; subst; try reflexivity.
    exfalso; eapply whnf_nored; tea; constructor.
  - inversion red'; subst; try reflexivity.
    exfalso; eapply whnf_nored;tea; constructor.
  - inversion red'; subst.
    2: f_equal; eauto.
    exfalso; eapply whnf_nored;tea; constructor.
Qed.

Lemma red_whne {l} t u : [t ⤳* u]< l > -> whne t -> t = u.
Proof.
  intros [] ?.
  1: reflexivity.
  exfalso.
  eauto using whne_nored.
Qed.

Lemma red_whnf {l} t u : [t ⤳* u]< l > -> whnf t -> t = u.
Proof.
  intros [] ?.
  1: reflexivity.
  exfalso.
  eauto using whnf_nored.
Qed.

Lemma whred_red_det {l} t u u' :
  whnf u ->
  [t ⤳* u]< l > -> [t ⤳* u']< l > ->
  [u' ⤳* u]< l >.
Proof.
  intros whnf red red'.
  induction red in whnf, u', red' |- *.
  - eapply red_whnf in red' as -> ; tea.
    now econstructor.
  - destruct red' as [? | ? ? ? o'].
    + now econstructor.
    + unshelve epose proof (ored_det o o') as <-.
      now eapply IHred.
Qed.

Corollary whred_det {l}  t u u' :
  whnf u -> whnf u' ->
  [t ⤳* u]< l > -> [t ⤳* u']< l > ->
  u = u'.
Proof.
  intros.
  eapply red_whnf ; tea.
  now eapply whred_red_det.
Qed.

(** *** Stability by weakening *)

Lemma oredalg_wk {l} (ρ : nat -> nat) (t u : term) :
[t ⤳ u]< l > ->
[t⟨ρ⟩ ⤳ u⟨ρ⟩]< l >.
Proof.
  intros Hred.
  induction Hred in ρ |- *.
  2-9, 12-17: cbn; asimpl; now econstructor.
  - cbn ; asimpl.
    evar (t' : term).
    replace (subst_term _ t) with t'.
    all: subst t'.
    1: econstructor.
    now asimpl.
  - cbn ; do 2 rewrite nSucc_ren.
    now constructor.
  - enough (Heqb : (bool_to_term b)⟨ρ⟩ = bool_to_term b) ; [ | now induction b].
    cbn ; rewrite Heqb ; clear Heqb.
    enough (Heqn : (nat_to_term n)⟨ρ⟩ = nat_to_term n) ; [ | clear ; induction n ; auto].
    2: unfold nat_to_term in * ; cbn in * ; now rewrite IHn.
    rewrite Heqn.
    now apply alphaRed.
Qed.

Lemma credalg_wk {l} (ρ : nat -> nat) (t u : term) :
[t ⤳* u]< l > ->
[t⟨ρ⟩ ⤳* u⟨ρ⟩]< l >.
Proof.
  induction 1 ; econstructor ; eauto using oredalg_wk.
Qed.

(** Derived rules *)

Lemma redalg_app {l t t' u} : [t ⤳* t']< l > -> [tApp t u ⤳* tApp t' u]< l >.
Proof.
induction 1.
+ reflexivity.
+ econstructor; [|eassumption].
  now econstructor.
Qed.

Lemma redalg_natElim {l P hs hz t t'} : [t ⤳* t']< l > -> [tNatElim P hs hz t ⤳* tNatElim P hs hz t']< l >.
Proof.
induction 1.
+ reflexivity.
+ econstructor; [|eassumption].
  now econstructor.
Qed.


Lemma redalg_boolElim {l P ht hf t t'} : [t ⤳* t']< l > -> [tBoolElim P ht hf t ⤳* tBoolElim P ht hf t']< l >.
Proof.
induction 1.
+ reflexivity.
+ econstructor; [|eassumption].
  now econstructor.
Qed.

Lemma redalg_natEmpty {l P t t'} : [t ⤳* t']< l > -> [tEmptyElim P t ⤳* tEmptyElim P t']< l >.
Proof.
induction 1.
+ reflexivity.
+ econstructor; [|eassumption].
  now econstructor.
Qed.

Lemma redalg_fst {l t t'} : [t ⤳* t']< l > -> [tFst t ⤳* tFst t']< l >.
Proof.
  induction 1; [reflexivity|].
  econstructor; tea; now constructor.
Qed.

Lemma redalg_snd {l t t'} : [t ⤳* t']< l > -> [tSnd t ⤳* tSnd t']< l >.
Proof.
  induction 1; [reflexivity|].
  econstructor; tea; now constructor.
Qed.

Lemma redalg_idElim {l A x P hr y t t'} : [t ⤳* t']< l > -> [tIdElim A x P hr y t ⤳* tIdElim A x P hr y t']< l >.
Proof.
  induction 1; [reflexivity|].
  econstructor; tea; now constructor.
Qed.

Lemma redalg_one_step {l t t'} : [t ⤳ t']< l > -> [t ⤳* t']< l >.
Proof. intros; econstructor;[tea|reflexivity]. Qed.

Lemma red_Ltrans {l l' t t'} (f : l' ≤ε l) : [ t ⤳ t' ]< l > -> [ t ⤳ t' ]< l' >.
Proof.
  intro H ; induction H ; try now econstructor.
Qed.

Lemma redalg_Ltrans {l l' t t'} : l' ≤ε l -> [t ⤳* t']< l > -> [t ⤳* t']< l' >.
Proof.
  intros Hinf Hred ; induction Hred ; try easy.
  econstructor ; try easy.
  now eapply red_Ltrans.
Qed.
  
Lemma alphane_disjunction_red {wl : wfLCon} {t t' n b} {ne : not_in_LCon wl n} :
  [ t ⤳ t' ]< wl ,,l (ne, b) > ->
  ([ t ⤳ t' ]< wl >) + (alphane wl n t).
Proof.
  intros Hyp ; induction Hyp.
  all: try now (left ; econstructor).
  all: try now (destruct IHHyp ; [ now left ; econstructor | now right ; econstructor]).
  destruct (PeanoNat.Nat.eq_dec n0 n) ; [subst | ].
  - right ; now econstructor.
  - left.
    enough (in_LCon wl n0 b0).
    + now econstructor.
    + inversion i ; subst.
      * now now exfalso.
      * assumption.
Qed.

Lemma alphane_disjunction_redalg {wl : wfLCon} {t t' n b} {ne : not_in_LCon wl n} :
  [ t ⤳* t' ]< wl ,,l (ne, b) > ->
  ([ t ⤳* t' ]< wl >) + (∑ t'', [ t ⤳* t'' ]< wl > × (alphane wl n t'')).
Proof.
  intros Hyp ; induction Hyp.
  - left ; now econstructor.
  - pose proof (Help := alphane_disjunction_red o).
    destruct Help ; [ | right ; eexists ; split ; [ | eassumption] ; now constructor].
    destruct IHHyp as [ | [t'' [Hred Ht'']]] ; [left ; now econstructor | ].
    right ; exists t'' ; split ; tea.
    now econstructor.
Qed.

Lemma red_alphane {l n} t u : [t ⤳* u]< l > -> alphane l n t -> t = u.
Proof.
  intros [] ?.
  1: reflexivity.
  exfalso.
  eauto using alphane_nored.
Qed.

Lemma whred_red_alphane {l n} t u u' :
  alphane l n u ->
  [t ⤳* u]< l > -> [t ⤳* u']< l > ->
  [u' ⤳* u]< l >.
Proof.
  intros whnf red red'.
  induction red in whnf, u', red' |- *.
  - eapply red_alphane in red' as -> ; tea.
    now econstructor.
  - destruct red' as [? | ? ? ? o'].
    + now econstructor.
    + unshelve epose proof (ored_det o o') as <-.
      now eapply IHred.
Qed.
