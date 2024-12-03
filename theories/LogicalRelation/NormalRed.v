
From Coq Require Import CRelationClasses.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations LContexts Context NormalForms UntypedReduction Weakening GenericTyping Monad LogicalRelation.
From LogRel.LogicalRelation Require Import Induction Irrelevance Escape Reflexivity Weakening Neutral Transitivity Reduction.

Set Universe Polymorphism.

Ltac redSubst :=
  match goal with
  | [H : [_ |- ?X :⤳*: ?Y]< _ > |- _] => 
    assert (X = Y)by (eapply redtywf_whnf ; gen_typing); subst; clear H
  end.


Section Normalization.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.


Program Definition normRedNe0 {wl Γ A} (h : [Γ ||-ne A]< wl >) (wh : whne A) :
  [Γ ||-ne A]< wl > :=
  {| neRedTy.ty := A |}.
Next Obligation.
  pose proof (LRne_ zero h); escape; now eapply redtywf_refl.
Qed.
Next Obligation. destruct h; now redSubst. Qed.



Program Definition normRedΠ0 {wl Γ F G l} (h : [Γ ||-Π<l> tProd F G]< wl >)
  : [Γ ||-Π<l> tProd F G]< wl > :=
  {| PiRedTyPack.dom := F ;
     PiRedTyPack.cod := G |}.
Solve All Obligations with 
  intros; pose proof (e := redtywf_whnf (PiRedTyPack.red h) whnf_tProd);
  symmetry in e; injection e; clear e; 
  destruct h ; intros; cbn in *; subst; eassumption.


Program Definition normRedΣ0 {wl Γ F G l} (h : [Γ ||-Σ<l> tSig F G]< wl >)
  : [Γ ||-Σ<l> tSig F G]< wl > :=
  {| PiRedTyPack.dom := F ;
     PiRedTyPack.cod := G |}.
Solve All Obligations with 
  intros; pose proof (e := redtywf_whnf (PiRedTyPack.red h) whnf_tSig);
  symmetry in e; injection e; clear e; 
  destruct h ; intros; cbn in *; subst; eassumption.
  
Definition normRedΠ {wl Γ F G l} (h : [Γ ||-<l> tProd F G]< wl >)
  : [Γ ||-<l> tProd F G]< wl > :=
  LRPi' (normRedΠ0 (invLRΠ h)).


Definition normRedΣ {wl Γ F G l} (h : [Γ ||-<l> tSig F G]< wl >) : [Γ ||-<l> tSig F G]< wl > :=
  LRSig' (normRedΣ0 (invLRΣ h)).

#[program]
Definition normEqRedΣ {wl Γ F F' G G' l} (h : [Γ ||-<l> tSig F G]< wl >) 
  (heq : [Γ ||-<l> _ ≅ tSig F' G' | h]< wl >) : [Γ ||-<l> _ ≅ tSig F' G' | normRedΣ h]< wl > :=
  {|
    PiRedTyEq.dom := F';
    PiRedTyEq.cod := G';
  |}.
Solve All Obligations with
  intros; assert[Γ ||-<l> _ ≅ tSig F' G' | normRedΣ h]< wl > as [?? red] by irrelevance;
  pose proof (e := redtywf_whnf red whnf_tSig);
  symmetry in e; injection e; clear e; 
  destruct h ; intros; cbn in *; subst; eassumption.

#[program]
Definition normLambda {wl Γ F F' G t l RΠ} 
  (Rlam : [Γ ||-<l> tLambda F' t : tProd F G | normRedΠ RΠ ]< wl >) :
  [Γ ||-<l> tLambda F' t : tProd F G | normRedΠ RΠ ]< wl > :=
  {| PiRedTm.nf := tLambda F' t |}.
Obligation 3.
eapply (PiRedTm.appTree Rlam ρ f Hd ha).
Defined.
Obligation 5.
pose proof (e := redtmwf_whnf (PiRedTm.red Rlam) whnf_tLambda).
destruct Rlam as [????? app eqq].
eapply (f_equal (ren_term ρ)) in e ; cbn in *.
rewrite e.
now eapply app.
Defined.
Solve All Obligations with
  intros;
  pose proof (e := redtmwf_whnf (PiRedTm.red Rlam) whnf_tLambda);
  destruct Rlam as [????? app eqq]; cbn in *; subst;
first [eapply app | now eapply eqq| eassumption].


#[program]
Definition normPair {wl Γ F F' G G' f g l RΣ} 
  (Rp : [Γ ||-<l> tPair F' G' f g : tSig F G | normRedΣ RΣ ]< wl >) :
  [Γ ||-<l> tPair F' G' f g : tSig F G | normRedΣ RΣ ]< wl > :=
  {| SigRedTm.nf := tPair F' G' f g |}.
Obligation 4.
eapply (SigRedTm.sndTree Rp) ; eassumption.
Defined.
Obligation 5.
  intros;
  pose proof (e := redtmwf_whnf (SigRedTm.red Rp) whnf_tPair);
    destruct Rp as [??? fstRed ?? sndRed]; cbn in * ; now subst.
Defined.
Next Obligation.
  intros;
    pose proof (e := redtmwf_whnf (SigRedTm.red Rp) whnf_tPair);
    destruct Rp as [??? fstRed ?? sndRed]; cbn in *; now subst.
Defined.
Next Obligation.
  intros;
    pose proof (e := redtmwf_whnf (SigRedTm.red Rp) whnf_tPair);
    destruct Rp as [??? fstRed ?? sndRed]; cbn in *; now subst.
Defined.
Next Obligation.
  intros;
    pose proof (e := redtmwf_whnf (SigRedTm.red Rp) whnf_tPair);
    destruct Rp as [??? fstRed ?? sndRed]; cbn in *; subst.
  now eapply fstRed.
Defined.
Next Obligation.
  intros;
    destruct Rp as [??? fstRed ?? sndRed]; cbn in *.
  unfold normPair_obligation_3 in * ; cbn in * ; revert Ho.
  destruct (redtmwf_whnf red whnf_tPair) ; subst ; cbn in *.
  intros Ho.
  irrelevanceRefl ; unshelve eapply sndRed.
  4,5: eassumption.
Defined.

Definition invLRcan {wl Γ l A} (lr : [Γ ||-<l> A]< wl >) (w : isType A) : [Γ ||-<l> A]< wl > :=
  match w as w in isType A return forall (lr : [Γ ||-<l> A]< wl >), invLRTy lr (reflexivity A) w -> [Γ ||-<l> A]< wl > with
  | UnivType => fun _ x => LRU_ x
  | ProdType => fun _ x => LRPi' (normRedΠ0 x)
  | NatType => fun _ x => LRNat_ _ x
  | BoolType => fun _ x => LRBool_ _ x
  | EmptyType => fun _ x => LREmpty_  _ x
  | SigType => fun _ x => LRSig' (normRedΣ0 x)
  | IdType => fun _ x => LRId' x
  | NeType wh => fun _ x => LRne_ _ (normRedNe0 x wh)
  end lr (invLR lr (reflexivity A) w).

End Normalization.

(** ** Tactics for normalizing the proof relevant components of a reducible type *)

(* Normalizes a term reducible at a Π type *)

Ltac normRedΠin X :=
  let g := type of X in
  match g with
  | [ LRAd.pack ?R | _ ||- ?t : _]< _ > =>
    let X' := fresh X in
    rename X into X' ;
    assert (X : [_ ||-<_> t : _ | LRPi' (normRedΠ0 (invLRΠ R))]< _ >) by irrelevance; clear X'
  | [ LRAd.pack ?R | _ ||- _ ≅ ?B]< _ > =>
    let X' := fresh X in
    rename X into X' ;
    assert (X : [_ ||-<_> _ ≅ B | LRPi' (normRedΠ0 (invLRΠ R))]< _ >) by irrelevance; clear X'
  | [ LRAd.pack ?R | _ ||- ?t ≅ ?u : _]< _ > =>
    let X' := fresh X in
    rename X into X' ;
    assert (X : [_ ||-<_> t ≅ u : _ | LRPi' (normRedΠ0 (invLRΠ R))]< _ >) by irrelevance; clear X'
  end.

Goal forall `{GenericTypingProperties} wl Γ A B l R f X
  (RABX : [Γ ||-<l> arr A B ≅ X | R]< wl >)
  (Rf : [Γ ||-<l> f : arr A B | R]< wl >)
  (Rff : [Γ ||-<l> f ≅ f : arr A B | R]< wl >)
, True.
Proof.
  intros.
  normRedΠin Rf.
  normRedΠin Rff.
  normRedΠin RABX.
  constructor.
Qed.

(* Normalizes a goal reducible at a Π type *)

Ltac normRedΠ id :=
  let G := fresh "G" in
  set (G := _);
  let g := eval unfold G in G in
  match g with
  | [ LRAd.pack ?R | _ ||- ?t : _]< _ > =>
    pose (id := normRedΠ0 (invLRΠ R)); subst G;
    enough [_ ||-<_> t : _ | LRPi' id]< _ > by irrelevance
  end.

(* Normalizes a term reducible at a Π type *)

Ltac normRedΣin X :=
  let g := type of X in
  match g with
  | [ LRAd.pack ?R | _ ||- ?t : _]< _ > =>
    let X' := fresh X in
    rename X into X' ;
    assert (X : [_ ||-<_> t : _ | LRSig' (normRedΣ0 (invLRΣ R))]< _ >) by irrelevance; clear X'
  | [ LRAd.pack ?R | _ ||- _ ≅ ?B]< _ > =>
    let X' := fresh X in
    rename X into X' ;
    assert (X : [_ ||-<_> _ ≅ B | LRSig' (normRedΣ0 (invLRΣ R))]< _ >) by irrelevance; clear X'
  | [ LRAd.pack ?R | _ ||- ?t ≅ ?u : _]< _ > =>
    let X' := fresh X in
    rename X into X' ;
    assert (X : [_ ||-<_> t ≅ u : _ | LRSig' (normRedΣ0 (invLRΣ R))]< _ >) by irrelevance; clear X'
  end.

