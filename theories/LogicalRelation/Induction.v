(** * LogRel.LogicalRelation.Induction: good induction principles for the logical relation. *)
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context LContexts NormalForms Weakening UntypedReduction Monad
GenericTyping LogicalRelation.

Set Universe Polymorphism.

(** As Coq is not currently able to define induction principles for nested inductive types
as our LR, we need to prove them by hand. We use this occasion to write down principles which
do not directly correspond to what LR would give us. More precisely, our induction principles:
- handle the two levels uniformly, rather than having to do two separate
  proofs, one at level zero and one at level one;
- apply directly to an inhabitant of the bundled logical relation, rather than the raw LR;
- give a more streamlined minor premise to prove for the case of Π type reducibility,
  which hides the separation needed in LR between the reducibility data and its adequacy
  (ie the two ΠA and ΠAad arguments to constructor LRPi).
Also, and crucially, all induction principles are universe-polymorphic, so that their usage
does not create global constraints on universes. *)

Section Inductions.
  Context `{ta : tag}
    `{!WfContext ta} `{!WfType ta} `{!Typing ta}
    `{!ConvType ta} `{!ConvTerm ta} `{!ConvNeuConv ta}
    `{!RedType ta} `{!RedTerm ta}.

(** ** Embedding *)

(** Reducibility at a lower level implies reducibility at a higher level, and their decoding are the
same. Both need to be proven simultaneously, because of contravariance in the product case. *)
  
  Fixpoint LR_embedding@{i j k l} {l l'} (l_ : l << l')
    {wl Γ A rEq rTe rTeEq} (lr : LogRel@{i j k l} l wl Γ A rEq rTe rTeEq)
    {struct lr} 
    : (LogRel@{i j k l} l' wl Γ A rEq rTe rTeEq) :=
    let embedPolyAd {wl Γ A B} {PA : PolyRedPack wl Γ A B}
          (PAad : PolyRedPackAdequate _ PA) :=
        {|
          PolyRedPack.shpAd (Δ : context) (wl' : wfLCon) (ρ : Δ ≤ _)
            (f : wl' ≤ε _) (h : [  |- Δ]< wl' >) :=
            LR_embedding l_ (PAad.(PolyRedPack.shpAd) ρ f h) ;
          PolyRedPack.posAd (Δ : context) (wl' : wfLCon)
            (a : term) (ρ : Δ ≤ Γ) (f : wl' ≤ε _) (Hd : [ |- Δ ]< wl' >)
            (ha : [(PolyRedPack.shpRed) PA ρ f Hd | Δ ||- a : _ ]< wl' >)
            (wl'' : wfLCon) (Ho : over_tree wl' wl'' _) :=
            LR_embedding l_ (PAad.(PolyRedPack.posAd) ρ f Hd ha Ho)
        |}
              in
    match lr with
    | LRU _ H =>
        match
          (match l_ with Oi => fun H' => elim H'.(URedTy.lt) end H)
        with end
    | LRne _ neA => LRne _ neA
    | LRPi _ ΠA ΠAad => LRPi _ ΠA (embedPolyAd ΠAad)
    | LRNat _ NA => LRNat _ NA
    | LRBool _ NA => LRBool _ NA
    | LREmpty _ NA => LREmpty _ NA
    | LRSig _ PA PAad => LRSig _ PA (embedPolyAd PAad)
    | LRId _ IA IAad => 
        let embedIdAd := 
          {| IdRedTyPack.tyAd := LR_embedding l_ IAad.(IdRedTyPack.tyAd) ;
            IdRedTyPack.tyKripkeAd (Δ : context) (wl' : wfLCon) (ρ : Δ ≤ _) (f : wl' ≤ε _) (wfΔ : [  |- Δ]< wl' >) :=
              LR_embedding l_ (IAad.(IdRedTyPack.tyKripkeAd) ρ f wfΔ) |} 
        in LRId _ IA embedIdAd
    end.

  Lemma WLR_embedding@{i j k l} {l l'} (l_ : l << l')
    {wl Γ A } (lr : WLogRel@{i j k l} l wl Γ A)
    : (WLogRel@{i j k l} l' wl Γ A).
  Proof.
    exists (WT _ lr).
    intros wl' Ho. eapply LRbuild.
    eapply LR_embedding ; [eassumption | ].
    unshelve eapply WRed ; [ |  eassumption | eassumption].
  Defined.

  Lemma WLREq_embedding@{i j k l} {l l'} (l_ : l << l')
    {wl Γ A B} (lr : WLogRel@{i j k l} l wl Γ A)
    (Heq: WLogRelEq@{i j k l} l wl Γ A B lr)
    : (WLogRelEq@{i j k l} l' wl Γ A B (WLR_embedding l_ lr)).
  Proof.
    exists (WTEq _ Heq).
    intros wl' Ho Ho'.
    cbn.
    now unshelve eapply WRedEq.
  Defined.

  Lemma WLRTm_embedding@{i j k l} {l l'} (l_ : l << l')
    {wl Γ t A} (lr : WLogRel@{i j k l} l wl Γ A)
    (Ht: WLogRelTm@{i j k l} l wl Γ t A lr)
    : (WLogRelTm@{i j k l} l' wl Γ t A (WLR_embedding l_ lr)).
  Proof.
    exists (WTTm _ Ht).
    intros wl' Ho Ho'.
    cbn.
    now unshelve eapply WRedTm.
  Defined.

  Lemma WLRTmEq_embedding@{i j k l} {l l'} (l_ : l << l')
    {wl Γ t u A} (lr : WLogRel@{i j k l} l wl Γ A)
    (Heq: WLogRelTmEq@{i j k l} l wl Γ t u A lr)
    : (WLogRelTmEq@{i j k l} l' wl Γ t u A (WLR_embedding l_ lr)).
  Proof.
    exists (WTTmEq _ Heq).
    intros wl' Ho Ho'.
    cbn.
    now unshelve eapply WRedTmEq.
  Defined.
  (** A basic induction principle, that handles only the first point in the list above *)

  Notation PolyHyp P wl Γ ΠA HAad G :=
    ((forall {Δ wl'} (ρ : Δ ≤ Γ) (f : wl' ≤ε wl) (h : [ |- Δ]< wl' >), P (HAad.(PolyRedPack.shpAd) ρ f h)) ->
      (forall {Δ wl' a} (ρ : Δ ≤ Γ) (f : wl' ≤ε wl) (h : [ |- Δ ]< wl' >) 
              (ha : [ ΠA.(PolyRedPack.shpRed) ρ f h | Δ ||- a : _ ]< wl' >)
              {wl'' : wfLCon} (Ho : over_tree wl' wl'' _),
          P (HAad.(PolyRedPack.posAd) ρ f h ha Ho)) -> G).


  Theorem LR_rect@{i j k o}
    (l : TypeLevel)
    (rec : forall l', l' << l -> RedRel@{i j})
    (P : forall {wl c t rEq rTe rTeEq},
      LR@{i j k} rec wl c t rEq rTe rTeEq  -> Type@{o}) :

    (forall (wl : wfLCon) (Γ : context) A (h : [Γ ||-U<l> A]< wl >),
      P (LRU rec h)) ->

    (forall (wl : wfLCon) (Γ : context) (A : term) (neA : [Γ ||-ne A]< wl >),
      P (LRne rec neA)) -> 

    (forall (wl : wfLCon) (Γ : context) (A : term) (ΠA : PiRedTy@{j} wl Γ A) (HAad : PiRedTyAdequate (LR rec) ΠA),
      PolyHyp P wl Γ ΠA HAad (P (LRPi rec ΠA HAad))) ->

    (forall wl Γ A (NA : [Γ ||-Nat A]< wl >), P (LRNat rec NA)) ->

    (forall wl Γ A (NA : [Γ ||-Bool A]< wl >), P (LRBool rec NA)) ->

    (forall wl Γ A (NA : [Γ ||-Empty A]< wl >), P (LREmpty rec NA)) ->

    (forall (wl : wfLCon) (Γ : context) (A : term) (ΠA : SigRedTy@{j} wl Γ A) (HAad : SigRedTyAdequate (LR rec) ΠA),
      PolyHyp P wl Γ ΠA HAad (P (LRSig rec ΠA HAad))) ->

    (forall wl Γ A (IA : IdRedTyPack@{j} wl Γ A) (IAad : IdRedTyAdequate (LR rec) IA), 
      P IAad.(IdRedTyPack.tyAd) ->
      (forall Δ wl' (ρ : Δ ≤ Γ) (f : wl' ≤ε wl) (wfΔ : [|-Δ]< wl' >), P (IAad.(IdRedTyPack.tyKripkeAd) ρ f wfΔ)) ->
      P (LRId rec IA IAad)) ->

    forall (wl : wfLCon) (Γ : context) (t : term) (rEq rTe : term -> Type@{j})
      (rTeEq  : term -> term -> Type@{j}) (lr : LR@{i j k} rec wl Γ t rEq rTe rTeEq),
      P lr.
  Proof.
    cbn.
    intros HU Hne HPi HNat HBool HEmpty HSig HId.
    fix HRec 7.
    destruct lr.
    - eapply HU.
    - eapply Hne.
    - eapply HPi.
      all: intros ; eapply HRec.
    - eapply HNat.
    - eapply HBool.
    - eapply HEmpty.
    - eapply HSig.
      all: intros; eapply HRec.
    - eapply HId; intros; eapply HRec.
  Defined.

  Definition LR_rec@{i j k} := LR_rect@{i j k Set}.
  
  Notation PolyHypLogRel P wl Γ ΠA G :=
    ((forall {Δ wl'} (ρ : Δ ≤ Γ) (f : wl' ≤ε wl) (h : [ |- Δ]< wl' >),
         P (ΠA.(PolyRed.shpRed) ρ f h).(LRAd.adequate)) ->
    (forall {Δ wl' a} (ρ : Δ ≤ Γ) (f : wl' ≤ε wl) (h : [ |- Δ ]< wl' >) 
            (ha : [ Δ ||-< _ > a : ΠA.(ParamRedTy.dom)⟨ρ⟩ |  ΠA.(PolyRed.shpRed) ρ f h ]< wl' >)
            {wl'' : wfLCon} (Ho : over_tree wl' wl'' _),
      P (ΠA.(PolyRed.posRed) ρ f h ha Ho).(LRAd.adequate)) -> G).

  (** Induction principle specialized to LogRel as the reducibility relation on lower levels *)
  Theorem LR_rect_LogRelRec@{i j k l o}
    (P : forall {l wl Γ t rEq rTe rTeEq},
    LogRel@{i j k l} l wl Γ t rEq rTe rTeEq -> Type@{o}) :

    (forall l (wl : wfLCon) (Γ : context) A (h : [Γ ||-U<l> A]< wl >),
      P (LRU (LogRelRec l) h)) ->

    (forall (l : TypeLevel) (wl : wfLCon) (Γ : context) (A : term) (neA : [Γ ||-ne A]< wl >),
      P (LRne (LogRelRec l) neA)) ->

    (forall (l : TypeLevel) (wl : wfLCon) (Γ : context) (A : term) (ΠA : ParamRedTy@{i j k l} tProd wl Γ l A),
      PolyHypLogRel P wl Γ ΠA (P (LRPi' ΠA).(LRAd.adequate ))) ->
    
    (forall l wl Γ A (NA : [Γ ||-Nat A]< wl >), P (LRNat (LogRelRec l) NA)) ->
    
    (forall l wl Γ A (NA : [Γ ||-Bool A]< wl >), P (LRBool (LogRelRec l) NA)) ->

    (forall l wl Γ A (NA : [Γ ||-Empty A]< wl >), P (LREmpty (LogRelRec l) NA)) ->
    
    (forall (l : TypeLevel) (wl : wfLCon) (Γ : context) (A : term) (ΠA : ParamRedTy@{i j k l} tSig wl Γ l A),
      PolyHypLogRel P wl Γ ΠA (P (LRSig' ΠA).(LRAd.adequate ))) ->
    
    (forall l wl Γ A (IA :  [Γ ||-Id<l> A]< wl >), 
      P (IA.(IdRedTy.tyRed).(LRAd.adequate)) -> 
      (forall Δ wl' (ρ : Δ ≤ Γ) (f : wl' ≤ε wl) (wfΔ : [|-Δ]< wl' >), P (IA.(IdRedTy.tyKripke) ρ f wfΔ).(LRAd.adequate)) ->
      
      P (LRId' IA).(LRAd.adequate)) ->

    forall (l : TypeLevel) (wl : wfLCon) (Γ : context) (t : term) (rEq rTe : term -> Type@{k})
      (rTeEq  : term -> term -> Type@{k}) (lr : LR@{j k l} (LogRelRec@{i j k} l) wl Γ t rEq rTe rTeEq),
      P lr.
  Proof.
    intros ?? HPi ??? HSig HId **; eapply LR_rect@{j k l o}.
    1,2,4,5,6: auto.
    - intros; eapply (HPi _ _ _ _ (ParamRedTy.from HAad)); eauto.
    - intros; eapply (HSig _ _ _ _ (ParamRedTy.from HAad)); eauto.
    - intros; eapply (HId _ _ _ _ (IdRedTy.from IAad)) ; eauto.
  Defined.

  Notation PolyHypTyUr P wl Γ ΠA G :=
    ((forall {Δ wl'} (ρ : Δ ≤ Γ) (f : wl' ≤ε wl) (h : [ |- Δ]< wl' >), P (ΠA.(PolyRed.shpRed) ρ f h)) ->
    (forall {Δ wl' a} (ρ : Δ ≤ Γ) (f : wl' ≤ε wl) (h : [ |- Δ ]< wl' >) 
            (ha : [ ΠA.(PolyRed.shpRed) ρ f h | Δ ||- a : ΠA.(ParamRedTy.dom)⟨ρ⟩ ]< wl' >)
            {wl'' : wfLCon} (Ho : over_tree wl' wl'' _),
      P (ΠA.(PolyRed.posRed) ρ f h ha Ho)) -> G).

  Theorem LR_rect_TyUr@{i j k l o}
    (P : forall {l wl Γ A}, [LogRel@{i j k l} l | Γ ||- A]< wl > -> Type@{o}) :

    (forall l (wl : wfLCon) (Γ : context) A (h : [Γ ||-U<l> A]< wl >),
      P (LRU_ h)) ->

    (forall (l : TypeLevel) (wl : wfLCon) (Γ : context) (A : term) (neA : [Γ ||-ne A]< wl >),
      P (LRne_ l neA)) ->

    (forall (l : TypeLevel) (wl : wfLCon) (Γ : context) (A : term) (ΠA : ParamRedTy@{i j k l} tProd wl Γ l A),
      PolyHypTyUr P wl Γ ΠA (P (LRPi' ΠA))) ->

    (forall l wl Γ A (NA : [Γ ||-Nat A]< wl >), P (LRNat_ l NA)) ->

    (forall l wl Γ A (NA : [Γ ||-Bool A]< wl >), P (LRBool_ l NA)) ->

    (forall l wl Γ A (NA : [Γ ||-Empty A]< wl >), P (LREmpty_ l NA)) ->
    
    (forall (l : TypeLevel) (wl : wfLCon) (Γ : context) (A : term) (ΠA : ParamRedTy@{i j k l} tSig wl Γ l A),
      PolyHypTyUr P wl Γ ΠA (P (LRSig' ΠA))) ->
    
    (forall l wl Γ A (IA :  [Γ ||-Id<l> A]< wl >), 
      P (IA.(IdRedTy.tyRed)) -> 
      (forall Δ wl' (ρ : Δ ≤ Γ) (f : wl' ≤ε wl) (wfΔ : [|-Δ]< wl' >), P (IA.(IdRedTy.tyKripke) ρ f wfΔ)) ->
      
      P (LRId' IA)) ->

    forall (l : TypeLevel) (wl : wfLCon) (Γ : context) (A : term) (lr : [LogRel@{i j k l} l | Γ ||- A]< wl >),
      P lr.
  Proof.
    intros HU Hne HPi HNat HBool HEmpty HSig HId l wl Γ A lr.
    apply (LR_rect_LogRelRec@{i j k l o} (fun l wl Γ A _ _ _ lr => P l wl Γ A (LRbuild lr))).
    all: auto.
  Defined.

  (* Specialized version for level 0, used in the general version *)

  Theorem LR_rect_TyUr0@{i j k l o} (l:=zero)
    (P : forall {wl Γ A}, [LogRel@{i j k l} l | Γ ||- A]< wl > -> Type@{o}) :

    (forall (wl : wfLCon) (Γ : context) (A : term) (neA : [Γ ||-ne A]< wl >), P (LRne_ l neA)) ->

    (forall (wl : wfLCon) (Γ : context) (A : term) (ΠA : ParamRedTy@{i j k l} tProd wl Γ l A),
      PolyHypTyUr P wl Γ ΠA (P (LRPi' ΠA))) ->

    (forall wl Γ A (NA : [Γ ||-Nat A]< wl >), P (LRNat_ l NA)) ->

    (forall wl Γ A (NA : [Γ ||-Bool A]< wl >), P (LRBool_ l NA)) ->

    (forall wl Γ A (NA : [Γ ||-Empty A]< wl >), P (LREmpty_ l NA)) ->
    
    (forall (wl : wfLCon) (Γ : context) (A : term) (ΠA : ParamRedTy@{i j k l} tSig wl Γ l A),
      PolyHypTyUr P wl Γ ΠA (P (LRSig' ΠA))) ->
    
    (forall wl Γ A (IA :  [Γ ||-Id<l> A]< wl >), 
      P (IA.(IdRedTy.tyRed)) ->
      (forall Δ wl' (ρ : Δ ≤ Γ) (f : wl' ≤ε wl) (wfΔ : [|-Δ]< wl' >), P (IA.(IdRedTy.tyKripke) ρ f wfΔ)) ->
      P (LRId' IA)) ->

    forall (wl : wfLCon) (Γ : context) (A : term) (lr : [LogRel@{i j k l} l | Γ ||- A]< wl >),
      P lr.
  Proof.
    intros HU Hne HPi HNat HBool HEmpty HSig wl Γ A lr.
    change _ with (match l as l return [Γ ||-<l> A]< wl > -> Type@{o} with zero => P wl Γ A | one => fun _ => unit end lr).
    generalize l wl Γ A lr.
    eapply LR_rect_TyUr; intros [] *; constructor + auto.
    exfalso. pose (x := URedTy.lt h). inversion x.
  Defined. 

  (* Induction principle with inductive hypothesis for the universe at lower levels *)
    
  Theorem LR_rect_TyUrGen@{i j k l o}
    (P : forall {l wl Γ A}, [LogRel@{i j k l} l | Γ ||- A]< wl > -> Type@{o}) :

    (forall l (wl : wfLCon) (Γ : context) A (h : [Γ ||-U<l> A]< wl >),
     (forall X (RX : [Γ ||-< URedTy.level h > X ]< wl >), P RX) -> P (LRU_ h)) ->

    (forall (l : TypeLevel) (wl : wfLCon) (Γ : context) (A : term) (neA : [Γ ||-ne A]< wl >),
      P (LRne_ l neA)) ->

    (forall (l : TypeLevel) (wl : wfLCon) (Γ : context) (A : term) (ΠA : ParamRedTy@{i j k l} tProd wl Γ l A),
      PolyHypTyUr P wl Γ ΠA (P (LRPi' ΠA))) ->

    (forall l wl Γ A (NA : [Γ ||-Nat A]< wl >), P (LRNat_ l NA)) ->

    (forall l wl Γ A (NA : [Γ ||-Bool A]< wl >), P (LRBool_ l NA)) ->

    (forall l wl Γ A (NA : [Γ ||-Empty A]< wl >), P (LREmpty_ l NA)) ->
    
    (forall (l : TypeLevel) (wl : wfLCon) (Γ : context) (A : term) (ΠA : ParamRedTy@{i j k l} tSig wl Γ l A),
      PolyHypTyUr P wl Γ ΠA (P (LRSig' ΠA))) ->
    
    (forall l wl Γ A (IA :  [Γ ||-Id<l> A]< wl >),
       P (IA.(IdRedTy.tyRed)) -> 
      (forall Δ wl' (ρ : Δ ≤ Γ) (f : wl' ≤ε wl) (wfΔ : [|-Δ]< wl' >), P (IA.(IdRedTy.tyKripke) ρ f wfΔ)) ->
      P (LRId' IA)) ->

    forall (l : TypeLevel) (wl : wfLCon) (Γ : context) (A : term) (lr : [LogRel@{i j k l} l | Γ ||- A]< wl >),
      P lr.
  Proof.
    intros HU Hne HPi HNat HBool HEmpty HSig HId.
    apply LR_rect_TyUr; tea; intros l wl Γ A h ; pose proof (x :=URedTy.lt h); inversion x ; subst.
    eapply HU. rewrite <- H0. clear h H0 x. revert wl Γ. eapply LR_rect_TyUr0; auto.
  Defined.

End Inductions.

(** ** Inversion principles *)

Section Inversions.
  Context `{ta : tag}
    `{!WfContext ta} `{!WfType ta} `{!Typing ta}
    `{!ConvType ta} `{!ConvTerm ta} `{!ConvNeuConv ta}
    `{!RedType ta} `{!RedTerm ta} `{!RedTypeProperties}
    `{!ConvNeuProperties}.
  
  Definition invLRTy {wl Γ l A A'} (lr : [Γ ||-<l> A]< wl >) (r : [A ⤳* A']< wl >) (w : isType A') :=
    match w return Type with
    | UnivType => [Γ ||-U<l> A]< wl >
    | ProdType => [Γ ||-Π<l> A]< wl >
    | NatType => [Γ ||-Nat A]< wl >
    | BoolType => [Γ ||-Bool A]< wl >
    | EmptyType => [Γ ||-Empty A]< wl >
    | SigType => [Γ ||-Σ<l> A]< wl >
    | IdType => [Γ||-Id<l> A]< wl >
    | NeType _ => [Γ ||-ne A]< wl >
    end.

  Lemma invLR {wl Γ l A A'} (lr : [Γ ||-<l> A]< wl >) (r : [A ⤳* A']< wl >) (w : isType A') : invLRTy lr r w.
  Proof.
    unfold invLRTy.
    revert A' r w.
    pattern l, wl, Γ, A, lr ; eapply LR_rect_TyUr; clear l wl Γ A lr.
    - intros * h ? red whA.
      assert (A' = U) as ->.
      {
        eapply whred_det.
        1-3: gen_typing.
        eapply redty_red, h.
      }
      dependent inversion whA.
      1: assumption.
      exfalso.
      gen_typing.
    - intros * ? A' red whA.
      enough ({w' & whA = NeType w'}) as [? ->] by easy.
      destruct neA as [A'' redA neA''].
      apply convneu_whne in neA''.
      assert (A' = A'') as <-.
      + eapply whred_det.
        1-3: gen_typing.
        eapply redty_red, redA.
      + dependent inversion whA ; subst.
        all: inv_whne.
        all: now eexists.
    - intros ???? PiA _ _ A' red whA.
      enough (∑ dom cod, A' = tProd cod dom) as (?&?&->).
      + dependent inversion whA ; subst.
        2: exfalso ; gen_typing.
        assumption.
      + destruct PiA as [?? redA].
        do 2 eexists.
        eapply whred_det.
        1-3: gen_typing.
        eapply redty_red, redA.
    - intros ???? [redA] ???.
      enough (A' = tNat) as ->.
      + dependent inversion w. 
        1: now econstructor.
        inv_whne.
      + eapply whred_det; tea.
        all: gen_typing.
    - intros ???? [redA] ???.
      enough (A' = tBool) as ->.
      + dependent inversion w. 
        1: now econstructor.
        inv_whne.
      + eapply whred_det; tea.
        all: gen_typing.
    - intros ???? [redA] ???.
      enough (A' = tEmpty) as ->.
      + dependent inversion w. 
        1: now econstructor.
        inv_whne.
      + eapply whred_det; tea.
        all: gen_typing.
    - intros ???? PA _ _ A' red whA.
      enough (∑ dom cod, A' = tSig cod dom) as (?&?&->).
      + dependent inversion whA ; subst.
        2: inv_whne.
        assumption.
      + destruct PA as [?? redA].
        do 2 eexists.
        eapply whred_det.
        1-3: gen_typing.
        eapply redty_red, redA.
    - intros ???? IA _ _ A' red whA'.
      enough (∑ B x y, A' = tId B x y) as [?[?[? ->]]].
      + dependent inversion whA'; tea; inv_whne.
      + destruct IA; do 3 eexists; eapply whred_det.
        1-3: gen_typing.
        now eapply redtywf_red.
  Qed.

  Lemma invLRU {wl Γ l} : [Γ ||-<l> U]< wl > -> [Γ ||-U<l> U]< wl >.
  Proof.
    intros.
    now unshelve eapply (invLR _ redIdAlg UnivType).
  Qed.

  Lemma invLRne {wl Γ l A} : whne A -> [Γ ||-<l> A]< wl > -> [Γ ||-ne A]< wl >.
  Proof.
    intros.
    now unshelve eapply  (invLR _ redIdAlg (NeType _)).
  Qed.

  Lemma invLRΠ {wl Γ l dom cod} : [Γ ||-<l> tProd dom cod]< wl > -> [Γ ||-Π<l> tProd dom cod]< wl >.
  Proof.
    intros.
    now unshelve eapply  (invLR _ redIdAlg ProdType).
  Qed.
  
  Lemma invLRΣ {wl Γ l dom cod} : [Γ ||-<l> tSig dom cod]< wl > -> [Γ ||-Σ<l> tSig dom cod]< wl >.
  Proof.
    intros.
    now unshelve eapply  (invLR _ redIdAlg SigType).
  Qed.

  Lemma invLRId {wl Γ l A x y} : [Γ ||-<l> tId A x y]< wl > -> [Γ ||-Id<l> tId A x y]< wl >.
  Proof.
    intros.
    now unshelve eapply (invLR _ redIdAlg IdType).
  Qed.

  (* invLRNat is useless *)

End Inversions.
