(** * LogRel.AlgorithmicTyping: definition of algorithmic conversion and typing. *)
From Coq Require Import ssrbool.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations LContexts Context NormalForms Weakening UntypedReduction GenericTyping DeclarativeTyping.

Section Definitions.

  (** We locally disable typing notations to be able to use them in the definition
  here before declaring the right instance. *)
  Close Scope typing_scope.

(** ** Conversion *)

  (** **** Conversion of types *)
  Inductive ConvTypeAlg (wl : wfLCon) : context -> term -> term  -> Type :=
    | typeConvRed {Γ A A' B B'} :
      [A ⤳* A']< wl > ->
      [B ⤳* B']< wl > ->
      [Γ |- A' ≅h B']< wl > ->
      [Γ |- A ≅ B]< wl >
  (** **** Conversion of types reduced to weak-head normal forms *)
  with ConvTypeRedAlg (wl : wfLCon) : context -> term -> term -> Type :=
    | typePiCongAlg {Γ A B A' B'} :
      [ Γ |- A ≅ A']< wl > ->
      [ Γ ,, A |- B ≅ B']< wl > ->
      [ Γ |- tProd A B ≅h tProd A' B']< wl >
    | typeUnivConvAlg {Γ} :
      [Γ |- U ≅h U]< wl >
    | typeNatConvAlg {Γ} :
      [Γ |- tNat ≅h tNat]< wl >
    | typeBoolConvAlg {Γ} :
      [Γ |- tBool ≅h tBool]< wl >
    | typeEmptyConvAlg {Γ} :
      [Γ |- tEmpty ≅h tEmpty]< wl >
    | typeSigCongAlg {Γ A B A' B'} :
      [ Γ |- A ≅ A']< wl > ->
      [ Γ ,, A |- B ≅ B']< wl > ->
      [ Γ |- tSig A B ≅h tSig A' B']< wl >
    | typeIdCongAlg {Γ A A' x x' y y'} :
      [ Γ |- A ≅ A']< wl > ->
      [ Γ |- x ≅ x' : A]< wl > ->
      [ Γ |- y ≅ y' : A]< wl > ->
      [ Γ |- tId A x y ≅h tId A' x' y']< wl >
    | typeNeuConvAlg {Γ M N T} :
      [ Γ |- M ~ N ▹ T]< wl > -> 
      [ Γ |- M ≅h N]< wl >
  (** **** Conversion of neutral terms *)
  with ConvNeuAlg (wl : wfLCon) : context -> term -> term  -> term -> Type :=
    | neuVarConvAlg {Γ n decl} :
      in_ctx Γ n decl ->
      [Γ |- tRel n ~ tRel n ▹ decl]< wl >
    | neuAppCongAlg {Γ m n t u A B} :
      [ Γ |- m ~h n ▹ tProd A B ]< wl > ->
      [ Γ |- t ≅ u : A ]< wl > ->
      [ Γ |- tApp m t ~ tApp n u ▹ B[t..] ]< wl >
    | neuNatElimCong {Γ n n' P P' hz hz' hs hs'} :
    (** Here, we know by invariant that the inferred type has to be tNat,
    so there should be no need to check that, but with parameterized/indexed
    inductive we need to recover informations from the neutrals to construct
    the context for the predicate and the type of the branches. *)
      [Γ |- n ~h n' ▹ tNat]< wl > ->
      [Γ,, tNat |- P ≅ P']< wl > ->
      [Γ |- hz ≅ hz' : P[tZero..]]< wl > ->
      [Γ |- hs ≅ hs' : elimSuccHypTy P]< wl > ->
      [Γ |- tNatElim P hz hs n ~ tNatElim P' hz' hs' n' ▹ P[n..]]< wl >
    | neuBoolElimCong {Γ n n' P P' ht ht' hf hf'} :
      [Γ |- n ~h n' ▹ tBool]< wl > ->
      [Γ,, tBool |- P ≅ P']< wl > ->
      [Γ |- ht ≅ ht' : P[tTrue..]]< wl > ->
      [Γ |- hf ≅ hf' : P[tFalse..]]< wl > ->
      [Γ |- tBoolElim P ht hf n ~ tBoolElim P' ht' hf' n' ▹ P[n..]]< wl >
    | neuEmptyElimCong {Γ P P' e e'} :
      [Γ |- e ~h e' ▹ tEmpty]< wl > ->
      [Γ ,, tEmpty |- P ≅ P']< wl > ->
      [Γ |- tEmptyElim P e ~ tEmptyElim P' e' ▹ P[e..]]< wl >
    | neuFstCongAlg {Γ m n A B} :
      [ Γ |- m ~h n ▹ tSig A B ]< wl > ->
      [ Γ |- tFst m ~ tFst n ▹ A ]< wl >
    | neuSndCongAlg {Γ m n A B} :
      [ Γ |- m ~h n ▹ tSig A B ]< wl > ->
      [ Γ |- tSnd m ~ tSnd n ▹ B[(tFst m)..] ]< wl >
    | neuIdEmlimCong {Γ A A' A'' x x' x'' P P' hr hr' y y' y'' e e'} :
      [Γ |- e ~h e' ▹ tId A'' x'' y'']< wl > ->
      (* [Γ |- A'' ]< wl > -> *)
      (* [Γ |- A'' ≅ A]< wl > -> *)
      (* [Γ |- x'' ◃ A]< wl > -> *)
      (* [Γ |- x'' ≅ x : A]< wl > -> *)
      (* [Γ |- y'' ◃ A]< wl > -> *)
      (* [Γ |- y'' ≅ y : A]< wl > -> *)
      [Γ |- A ≅ A']< wl > ->
      [Γ |- x ≅ x' : A]< wl > ->
      [Γ ,, A ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) |- P ≅ P']< wl > ->
      [Γ |- hr ≅ hr' : P[tRefl A x .: x..]]< wl > ->
      [Γ |- y ≅ y' : A]< wl > ->
      [Γ |- tIdElim A x P hr y e ~ tIdElim A' x' P' hr' y' e' ▹ P[e .: y..] ]< wl >
    | neuAlphaCong {Γ n n' k} :
      [Γ |- n ~ n' ▹ tNat]< wl > ->
      [Γ |- tAlpha (nSucc k n) ~ tAlpha (nSucc k n') ▹ tBool]< wl >
  (** **** Conversion of neutral terms at a type reduced to weak-head normal form*)
  with ConvNeuRedAlg (wl : wfLCon) : context -> term -> term -> term -> Type :=
    | neuConvRed {Γ m n A A'} :
      [Γ |- m ~ n ▹ A]< wl > ->
      [A ⤳* A']< wl > ->
      isType A' ->
      [Γ |- m ~h n ▹ A']< wl >
  (** **** Conversion of terms *)
  with ConvTermAlg (wl : wfLCon) : context -> term -> term -> term -> Type :=
    | termConvRed {Γ t t' u u' A A'} :
      [A ⤳* A']< wl > ->
      [t ⤳* t']< wl > ->
      [u ⤳* u' ]< wl > ->
      [Γ |- t' ≅h u' : A']< wl > ->
      [Γ |- t ≅ u : A]< wl >
    | ϝtermConv_l {Γ n P ht hf t} {ne : not_in_LCon (pi1 wl) n} :
      [Γ |- ht ≅ t : P[tTrue..]]< wl ,,l (ne, true) > ->
      [Γ |- hf ≅ t : P[tFalse..]]< wl ,,l (ne, false) > ->
      [Γ |- tBoolElim P ht hf (tAlpha (nat_to_term n)) ≅ t : P[(tAlpha (nat_to_term n))..]]< wl >
    | ϝtermConv_r {Γ n P ht hf t} {ne : not_in_LCon (pi1 wl) n} :
      whnf t ->
      [Γ |- t ≅ ht : P[tTrue..]]< wl ,,l (ne, true) > ->
      [Γ |- t ≅ hf : P[tFalse..]]< wl ,,l (ne, false) > ->
      [Γ |- t ≅ tBoolElim P ht hf (tAlpha (nat_to_term n)) : P[(tAlpha (nat_to_term n))..]]< wl >
  (** **** Conversion of terms reduced to a weak-head normal form at a reduced type *)
  with ConvTermRedAlg (wl : wfLCon) : context -> term -> term -> term -> Type :=
    | termPiCongAlg {Γ A B A' B'} :
      [ Γ |- A ≅ A' : U]< wl > ->
      [ Γ ,, A |- B ≅ B' : U]< wl > ->
      [ Γ |- tProd A B ≅h tProd A' B' : U]< wl >
    | termNatReflAlg {Γ} :
      [Γ |- tNat ≅h tNat : U]< wl >
    | termZeroReflAlg {Γ} :
      [Γ |- tZero ≅h tZero : tNat]< wl >
    | termSuccCongAlg {Γ t t'} :
      [Γ |- t ≅ t' : tNat]< wl > ->
      [Γ |- tSucc t ≅h tSucc t' : tNat]< wl >
    | termBoolReflAlg {Γ} :
      [Γ |- tBool ≅h tBool : U]< wl >
    | termTrueReflAlg {Γ} :
      [Γ |- tTrue ≅h tTrue : tBool]< wl >
    | termFalseReflAlg {Γ} :
      [Γ |- tFalse ≅h tFalse : tBool]< wl >
    | termEmptyReflAlg {Γ} :
      [Γ |- tEmpty ≅h tEmpty : U]< wl >
    | termFunConvAlg {Γ : context} {f g A B} :
      isFun f ->
      isFun g ->
      [ Γ,, A |- eta_expand f ≅ eta_expand g : B]< wl > -> 
      [ Γ |- f ≅h g : tProd A B]< wl >
    | termSigCongAlg {Γ A B A' B'} :
      [ Γ |- A ≅ A' : U]< wl > ->
      [ Γ ,, A |- B ≅ B' : U]< wl > ->
      [ Γ |- tSig A B ≅h tSig A' B' : U]< wl >
    | termPairConvAlg {Γ : context} {p q A B} :
      whnf p ->
      whnf q ->
      [ Γ |- tFst p ≅ tFst q : A]< wl > -> 
      [ Γ |- tSnd p ≅ tSnd q : B[(tFst p)..]]< wl > -> 
      [ Γ |- p ≅h q : tSig A B]< wl >
    | termIdCongAlg {Γ A A' x x' y y'} :
      [Γ |- A ≅ A' : U]< wl > ->
      [Γ |- x ≅ x' : A]< wl > ->
      [Γ |- y ≅ y' : A]< wl > ->
      [Γ |- tId A x y ≅h tId A' x' y' : U]< wl >
    | termIdReflCong {Γ A A' A'' x x' y y'} :
      [Γ |- A ≅ A']< wl > ->
      [Γ |- x ≅ x' : A]< wl > ->
      [Γ |- tRefl A x ≅h tRefl A' x' : tId A'' y y' ]< wl >
    | termNeuConvAlg {Γ m n T P} :
      [Γ |- m ~ n ▹ T]< wl > ->
      isPosType P ->
      [Γ |- m ≅h n : P]< wl >

  where "[ Γ |- A ≅ B ]< wl >" := (ConvTypeAlg wl Γ A B)
  and "[ Γ |- A ≅h B ]< wl >" := (ConvTypeRedAlg wl Γ A B)
  and "[ Γ |- m ~ n ▹ T ]< wl >" := (ConvNeuAlg wl Γ T m n)
  and "[ Γ |- m ~h n ▹ T ]< wl >" := (ConvNeuRedAlg wl Γ T m n)
  and "[ Γ |- t ≅ u : T ]< wl >" := (ConvTermAlg wl Γ T t u)
  and "[ Γ |- t ≅h u : T ]< wl >" := (ConvTermRedAlg wl Γ T t u)
  and "[ t ⤳ t' ]< wl >" := (@OneRedAlg wl t t')
  and "[ t ⤳* t' ]< wl >" := (@RedClosureAlg wl t t').

(** ** Typing *)

  (** **** Type well-formation *)
  Inductive WfTypeAlg (wl : wfLCon) : context -> term -> Type :=
    | wfTypeU Γ : [ Γ |- U ]< wl >
    | wfTypeProd {Γ A B} :
      [Γ |- A ]< wl > ->
      [Γ,, A |- B]< wl > ->
      [Γ |- tProd A B]< wl >
    | wfTypeNat {Γ} :
      [Γ |- tNat]< wl >
    | wfTypeBool {Γ} :
      [Γ |- tBool]< wl >
    | wfTypeEmpty {Γ} :
        [Γ |- tEmpty]< wl >
    | wfTypeSig {Γ A B} :
      [Γ |- A ]< wl > ->
      [Γ,, A |- B]< wl > ->
      [Γ |- tSig A B]< wl >
    | wfTypeId {Γ A x y} :
      [Γ |- A]< wl > ->
      [Γ |- x ◃ A]< wl > ->
      [Γ |- y ◃ A]< wl > ->
      [Γ |- tId A x y]< wl >
    | wfTypeUniv {Γ A} :
      ~ isCanonical A ->
      [Γ |- A ▹h U]< wl > ->
      [Γ |- A]< wl >
  (** **** Type inference *)
  with InferAlg (wl : wfLCon) : context -> term -> term -> Type :=
    | infVar {Γ n decl} :
      in_ctx Γ n decl ->
      [Γ |- tRel n ▹ decl]< wl >
    | infProd {Γ} {A B} :
      [ Γ |- A ▹h U]< wl > -> 
      [Γ ,, A |- B ▹h U ]< wl > ->
      [ Γ |- tProd A B ▹ U ]< wl >
    | infLam {Γ} {A B t} :
      [ Γ |- A]< wl > ->
      [ Γ ,, A |- t ▹ B ]< wl > -> 
      [ Γ |- tLambda A t ▹ tProd A B]< wl >
    | infApp {Γ} {f a A B} :
      [ Γ |- f ▹h tProd A B ]< wl > -> 
      [ Γ |- a ◃ A ]< wl > -> 
      [ Γ |- tApp f a ▹ B[a..] ]< wl >
    | infNat {Γ} :
      [Γ |- tNat ▹ U]< wl >
    | infZero {Γ} :
      [Γ |- tZero ▹ tNat]< wl >
    | infSucc {Γ t} :
      [Γ |- t ▹h tNat]< wl > ->
      [Γ |- tSucc t ▹ tNat]< wl >
    | infNatElim {Γ P hz hs n} :
      [Γ |- n ▹h tNat]< wl > ->
      [Γ,, tNat |- P]< wl > ->
      [Γ |- hz ◃ P[tZero..]]< wl > ->
      [Γ |- hs ◃ elimSuccHypTy P]< wl > ->
      [Γ |- tNatElim P hz hs n ▹ P[n..]]< wl >
    | infBool {Γ} :
      [Γ |- tBool ▹ U]< wl >
    | infTrue {Γ} :
      [Γ |- tTrue ▹ tBool]< wl >
    | infFalse {Γ} :
      [Γ |- tFalse ▹ tBool]< wl >
    | infAlpha {Γ t} :
      [Γ |- t ▹h tNat]< wl > ->
      [Γ |- tAlpha t ▹ tBool]< wl >
    | infBoolElim {Γ P ht hf n} :
      [Γ |- n ▹h tBool]< wl > ->
      [Γ,, tBool |- P]< wl > ->
      [Γ |- ht ◃ P[tTrue..]]< wl > ->
      [Γ |- hf ◃ P[tFalse..]]< wl > ->
      [Γ |- tBoolElim P ht hf n ▹ P[n..]]< wl >
    | infEmpty {Γ} :
      [Γ |- tEmpty ▹ U]< wl >
    | infEmptyElim {Γ P e} :
      [Γ |- e ▹h tEmpty]< wl > ->
      [Γ ,, tEmpty |- P ]< wl > ->
      [Γ |- tEmptyElim P e ▹ P[e..]]< wl >
    | infSig {Γ} {A B} :
      [ Γ |- A ▹h U]< wl > -> 
      [Γ ,, A |- B ▹h U ]< wl > ->
      [ Γ |- tSig A B ▹ U ]< wl >
    | infPair {Γ A B a b} :
      [ Γ |- A]< wl > -> 
      [Γ ,, A |- B]< wl > ->
      [Γ |- a ◃ A]< wl > ->
      [Γ |- b ◃ B[a..]]< wl > ->
      [Γ |- tPair A B a b ▹ tSig A B]< wl >
    | infFst {Γ A B p} :
      [Γ |- p ▹h tSig A B]< wl > ->
      [Γ |- tFst p ▹ A]< wl >
    | infSnd {Γ A B p} :
      [Γ |- p ▹h tSig A B]< wl > ->
      [Γ |- tSnd p ▹ B[(tFst p)..]]< wl >
    | infId {Γ A x y} :
      [Γ |- A ▹h U]< wl > ->
      [Γ |- x ◃ A]< wl > ->
      [Γ |- y ◃ A]< wl > ->
      [Γ |- tId A x y ▹ U]< wl >
    | infRefl {Γ A x} :
      [Γ |- A]< wl > ->
      [Γ |- x ◃ A]< wl > ->
      [Γ |- tRefl A x ▹ tId A x x]< wl >
    | infIdElim {Γ A x P hr y e} :
      [Γ |- A]< wl > ->
      [Γ |- x ◃ A]< wl > ->
      [Γ,, A,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) |- P]< wl > ->
      [Γ |- hr ◃ P[tRefl A x .: x..]]< wl > ->
      [Γ |- y ◃ A]< wl > ->
      [Γ |- e ◃ tId A x y]< wl > ->
      [Γ |- tIdElim A x P hr y e ▹ P[e .: y..]]< wl >
  (** **** Inference of a type reduced to weak-head normal form*)
  with InferRedAlg (wl : wfLCon) : context -> term -> term -> Type :=
    | infRed {Γ t A A'} :
      [Γ |- t ▹ A ]< wl > ->
      [ A ⤳* A']< wl > ->
      [Γ |- t ▹h A']< wl >
  (** **** Type-checking *)
  with CheckAlg (wl : wfLCon) : context -> term -> term -> Type :=
    | checkConv {Γ t A A'} :
      [ Γ |- t ▹ A ]< wl > -> 
      [ Γ |- A ≅ A']< wl > -> 
      [ Γ |- t ◃ A' ]< wl >

  where "[ Γ |- A ]< wl >" := (WfTypeAlg wl Γ A)
  and "[ Γ |- t ▹ T ]< wl >" := (InferAlg wl Γ T t)
  and "[ Γ |- t ▹h T ]< wl >" := (InferRedAlg wl Γ T t)
  and "[ Γ |- t ◃ T ]< wl >" := (CheckAlg wl Γ T t).

  (** Context well-formation *)
  Inductive WfContextAlg (wl : wfLCon) : context -> Type :=
  | conNilAlg : [|- ε]< wl >
  | conConsAlg {Γ A} :
    [|- Γ]< wl > ->
    [ Γ |- A]< wl > ->
    [|- Γ,, A]< wl >
  where "[ |- Γ ]< wl >" := (WfContextAlg wl Γ).

End Definitions.

(** ** Instances *)
Module AlgorithmicTypingData.

  Definition al : tag.
  Proof.
  constructor.
  Qed.

  #[export] Instance WfContext_Algo : WfContext al := WfContextAlg.
  #[export] Instance WfType_Algo : WfType al := WfTypeAlg.
  #[export] Instance Inferring_Algo : Inferring al := InferAlg.
  #[export] Instance InferringRed_Algo : InferringRed al := InferRedAlg.
  #[export] Instance Checking_Algo : Checking al := CheckAlg.
  #[export] Instance ConvType_Algo : ConvType al := ConvTypeAlg.
  #[export] Instance ConvTypeRed_Algo : ConvTypeRed al :=  ConvTypeRedAlg.
  #[export] Instance ConvTerm_Algo : ConvTerm al := ConvTermAlg.
  #[export] Instance ConvTermRed_Algo : ConvTermRed al := ConvTermRedAlg.
  #[export] Instance ConvNeu_Algo : ConvNeu al := ConvNeuAlg.
  #[export] Instance ConvNeuRed_Algo : ConvNeuRed al := ConvNeuRedAlg.

  Ltac fold_algo :=
    change WfContextAlg with (wf_context (ta := al)) in * ;
    change WfTypeAlg with (wf_type (ta := al)) in *;
    change InferAlg with (inferring (ta := al)) in * ;
    change InferRedAlg with (infer_red (ta := al)) in * ;
    change CheckAlg with (check (ta := al)) in * ;
    change ConvTypeAlg with (conv_type (ta := al)) in * ;
    change ConvTypeRedAlg with (conv_type_red (ta := al)) in * ;
    change ConvTermAlg with (conv_term (ta := al)) in * ;
    change ConvTermRedAlg with (conv_term_red (ta := al)) in * ;
    change ConvNeuAlg with (conv_neu (ta := al)) in * ;
    change ConvTypeRedAlg with (conv_type_red (ta := al)) in * ;
    change ConvTermRedAlg with (conv_term_red (ta := al)) in * ;
    change ConvNeuRedAlg with (conv_neu_red (ta := al)) in *.

  Smpl Add fold_algo : refold.

End AlgorithmicTypingData.

(** ** Induction principles *)

(** Similarly to declarative typing, we need some massaging to turn the output of 
Scheme to something that fits our purpose, and we also define a function that computes
the conclusion of a proof by induction. *)
Section InductionPrinciples.
  Import AlgorithmicTypingData.

Scheme 
    Minimality for ConvTypeAlg Sort Type with
    Minimality for ConvTypeRedAlg Sort Type with
    Minimality for ConvNeuAlg Sort Type with
    Minimality for ConvNeuRedAlg Sort Type with
    Minimality for ConvTermAlg Sort Type with
    Minimality for ConvTermRedAlg Sort Type.

Scheme
    Minimality for WfTypeAlg Sort Type with
    Minimality for InferAlg Sort Type with
    Minimality for InferRedAlg Sort Type with
      Minimality for CheckAlg Sort Type.

Combined Scheme _AlgoConvInduction from
    ConvTypeAlg_rect_nodep,
    ConvTypeRedAlg_rect_nodep,
    ConvNeuAlg_rect_nodep,
    ConvNeuRedAlg_rect_nodep,
    ConvTermAlg_rect_nodep,
    ConvTermRedAlg_rect_nodep.

Combined Scheme _AlgoTypingInduction from
    WfTypeAlg_rect_nodep,
    InferAlg_rect_nodep,
    InferRedAlg_rect_nodep,
    CheckAlg_rect_nodep.

Let _AlgoConvInductionType :=
  ltac:(let ind := fresh "ind" in
      pose (ind := _AlgoConvInduction);
      refold ;
      let ind_ty := type of ind in
      exact ind_ty).

Let AlgoConvInductionType :=
  ltac: (let ind := eval cbv delta [_AlgoConvInductionType] zeta
    in _AlgoConvInductionType in
    let ind' := polymorphise ind in
  exact ind').

Lemma AlgoConvInduction : AlgoConvInductionType.
Proof.
  intros PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq **.
  pose proof (_AlgoConvInduction PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq) as H.
  destruct H with (wl := wl) as [?[?[?[?[?]]]]] ; cycle -1.
  1: by_prod_splitter.
  all: assumption.
Qed.

Let _AlgoTypingInductionType :=
  ltac:(let ind := fresh "ind" in
      pose (ind := _AlgoTypingInduction);
      refold ;
      let ind_ty := type of ind in
      exact ind_ty).

Let AlgoTypingInductionType :=
  ltac: (let ind := eval cbv delta [_AlgoTypingInductionType] zeta
    in _AlgoTypingInductionType in
    let ind' := polymorphise ind in
  exact ind').

Lemma AlgoTypingInduction : AlgoTypingInductionType.
Proof.
  intros wl PTy PInf PInfRed PCheck **.
  pose proof (_AlgoTypingInduction wl PTy PInf PInfRed PCheck) as H.
  destruct H as [?[?[?]]] ; cycle -1.
  1: by_prod_splitter.
  all: assumption.
Qed.

Definition AlgoConvInductionConcl :=
  ltac:(
    let t := eval cbv delta [AlgoConvInductionType] beta in AlgoConvInductionType in
    let t' := remove_steps t in
    exact t').

Definition AlgoTypingInductionConcl :=
  ltac:(
    let t := eval cbv delta [AlgoTypingInductionType] beta in AlgoTypingInductionType in
    let t' := remove_steps t in
    exact t').

End InductionPrinciples.

Arguments AlgoConvInductionConcl PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq : rename.
Arguments AlgoTypingInductionConcl PTy PInf PInfRed PCheck : rename.

(** ** Stability by weakening *)

Section TypingWk.
  Import AlgorithmicTypingData.
  
  Let PTyEq (wl : wfLCon) (Γ : context) (A B : term) := forall Δ (ρ : Δ ≤ Γ),
    [Δ |- A⟨ρ⟩ ≅ B⟨ρ⟩]< wl >.
  Let PTyRedEq (wl : wfLCon) (Γ : context) (A B : term) := forall Δ (ρ : Δ ≤ Γ),
      [Δ |- A⟨ρ⟩ ≅h B⟨ρ⟩]< wl >.
  Let PNeEq (wl : wfLCon) (Γ : context) (A t u : term) := forall Δ (ρ : Δ ≤ Γ),
    [Δ |- t⟨ρ⟩ ~ u⟨ρ⟩ ▹ A⟨ρ⟩]< wl >.
  Let PNeRedEq (wl : wfLCon) (Γ : context) (A t u : term) := forall Δ (ρ : Δ ≤ Γ),
    [Δ |- t⟨ρ⟩ ~h u⟨ρ⟩ ▹ A⟨ρ⟩]< wl >.
  Let PTmEq (wl : wfLCon) (Γ : context) (A t u : term) := forall Δ (ρ : Δ ≤ Γ),
    [Δ |- t⟨ρ⟩ ≅ u⟨ρ⟩ : A⟨ρ⟩]< wl >.
  Let PTmRedEq (wl : wfLCon) (Γ : context) (A t u : term) := forall Δ (ρ : Δ ≤ Γ),
      [Δ |- t⟨ρ⟩ ≅h u⟨ρ⟩ : A⟨ρ⟩]< wl >.

  Theorem algo_conv_wk (wl : wfLCon) :
    AlgoConvInductionConcl PTyEq PTyRedEq
      PNeEq PNeRedEq PTmEq PTmRedEq wl.
  Proof.
    subst PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq.
    apply AlgoConvInduction ; clear wl.
    - intros.
      econstructor.
      all: eauto using credalg_wk.
    - intros * ? ? ? IHB ? *.
      cbn.
      econstructor.
      1: now eauto.
      now eapply IHB with(ρ := wk_up _ ρ).
    - econstructor.
    - intros.
      now econstructor.
    - intros.
      now econstructor.
    - intros.
      now econstructor.
    - intros * ??? IHB ? *; do 2 rewrite <- wk_sig.
      econstructor.
      1: eauto.
      now eapply IHB.
    - intros; now econstructor.
    - intros.
      now econstructor.
    - intros * ? ? ?.
      eapply convne_meta_conv.
      1: econstructor ; eauto using in_ctx_wk.
      all: reflexivity.
    - intros * ? IHm ? IHt ? ?.
      cbn in *.
      eapply convne_meta_conv ; [econstructor|..] ; refold.
      + eauto.
      + eauto.
      + now asimpl.
      + reflexivity.
    - intros * ? IHn ? IHP ? IHz ? IHs *.
      cbn.
      eapply convne_meta_conv ; [econstructor|..] ; refold.
      + eauto.
      + now eapply (IHP _ (wk_up tNat ρ)).
      + eapply convtm_meta_conv.
        * eapply IHz.
        * now bsimpl.
        * reflexivity.
      + eapply convtm_meta_conv.
        * eapply IHs.
        * unfold elimSuccHypTy.
          now bsimpl.
        * reflexivity.
      + now bsimpl.
      + now bsimpl.
    - intros * ? IHn ? IHP ? IHt ? IHf *.
      cbn.
      eapply convne_meta_conv ; [econstructor|..] ; refold.
      + eauto.
      + now eapply (IHP _ (wk_up tBool ρ)).
      + eapply convtm_meta_conv.
        * eapply IHt.
        * now bsimpl.
        * reflexivity.
      + eapply convtm_meta_conv.
        * eapply IHf.
        * now bsimpl.
        * reflexivity.
      + now bsimpl.
      + now bsimpl.
    - intros * ? IHe ? IHP *.
      cbn.
      eapply convne_meta_conv ; [econstructor|..] ; refold.
      + eauto.
      + now eapply (IHP _ (wk_up tEmpty ρ)).
      + now bsimpl.
      + now bsimpl.
    - intros * ? IH *; cbn.
      econstructor; now eapply IH.
    - intros ???? A? ? IH *; cbn.
      rewrite (subst_ren_wk_up (A:=A)).
      econstructor; now eapply IH.
    - intros * ? IHe (*?? ?? ??*) ?? ?? ? IHp **; erewrite <-2!wk_idElim, subst_ren_wk_up2.
      econstructor; eauto.
      + rewrite 2!(wk_up_wk1 ρ).
        eapply IHp; constructor; tea.
      + rewrite wk_refl, <- subst_ren_wk_up2; eauto.
    - intros.
      cbn ; do 2 rewrite nSucc_ren.
      now econstructor.
    - intros.
      econstructor.
      + eauto.
      + eauto using credalg_wk.
      + gen_typing. 
    - intros.
      econstructor.
      1-3: eauto using credalg_wk.
      now eauto.
    - intros * ? Ht ? Hf *.
      cbn ; unfold nat_to_term ; rewrite nSucc_ren ; cbn.
      rewrite (subst_ren_wk_up (A := tBool)) ; cbn ; rewrite nSucc_ren ; cbn.
      change (nSucc n tZero) with (nat_to_term n).
      unshelve eapply ϝtermConv_l ; [assumption | ..].
      + change tTrue with (tTrue⟨ρ⟩).
        rewrite <- (wk_up_ren_on _ _ _ tBool), <- subst_ren_wk_up.
        now eapply Ht.
      + change tFalse with (tFalse⟨ρ⟩).
        rewrite <- (wk_up_ren_on _ _ _ tBool), <- subst_ren_wk_up.
        now eapply Hf.
    - intros * ?? Ht ? Hf *.
      cbn ; unfold nat_to_term ; rewrite nSucc_ren ; cbn.
      rewrite (subst_ren_wk_up (A := tBool)) ; cbn ; rewrite nSucc_ren ; cbn.
      change (nSucc n tZero) with (nat_to_term n).
      unshelve eapply ϝtermConv_r ; [assumption | ..].
      + now eapply whnf_ren.
      + change tTrue with (tTrue⟨ρ⟩).
        rewrite <- (wk_up_ren_on _ _ _ tBool), <- subst_ren_wk_up.
        now eapply Ht.
      + change tFalse with (tFalse⟨ρ⟩).
        rewrite <- (wk_up_ren_on _ _ _ tBool), <- subst_ren_wk_up.
        now eapply Hf.
    - intros * ? ? ? IHB ? ?.
      cbn.
      econstructor.
      1: now eauto.
      now eapply IHB with(ρ := wk_up _ ρ).
    - now econstructor.
    - now econstructor.
    - now econstructor.
    - now econstructor.
    - now econstructor.
    - now econstructor.
    - now econstructor.
    - intros * ? ? ? IH ? ?.
      cbn.
      econstructor.
      1-2: gen_typing.
      specialize IH with(ρ := wk_up _ ρ).
      cbn in *.
      assert (eq: forall t, t⟨ρ⟩⟨↑⟩ = t⟨↑⟩⟨up_ren ρ⟩) by now asimpl.
      do 2 rewrite eq.
      apply IH.
    - intros * ??? IHB *. 
      do 2 rewrite <- wk_sig.
      econstructor.
      1: now eauto.
      now eapply IHB.
    - intros * ??? IHfst ? IHsnd *.
      rewrite <- wk_sig.
      econstructor.
      1,2: gen_typing.
      1: eauto.
      rewrite wk_fst, <- subst_ren_wk_up; eauto.
    - intros; econstructor; eauto.
    - intros; econstructor; eauto.
    - intros.
      econstructor.
      + eauto.
      + eauto using isPosType_ren.
  Qed.

  Let PTy (wl : wfLCon) (Γ : context) (A : term) := forall Δ (ρ : Δ ≤ Γ), [Δ |- A⟨ρ⟩]< wl >.
  Let PInf (wl : wfLCon) (Γ : context) (A t : term) := forall Δ (ρ : Δ ≤ Γ),
    [Δ |- t⟨ρ⟩ ▹ A⟨ρ⟩]< wl >.
  Let PInfRed (wl : wfLCon) (Γ : context) (A t : term) := forall Δ (ρ : Δ ≤ Γ),
    [Δ |- t⟨ρ⟩ ▹h A⟨ρ⟩]< wl >.
  Let PCheck (wl : wfLCon) (Γ : context) (A t : term) := forall Δ (ρ : Δ ≤ Γ),
  [Δ |- t⟨ρ⟩ ◃ A⟨ρ⟩]< wl >.

  Theorem algo_typing_wk (wl : wfLCon) :
    AlgoTypingInductionConcl wl (PTy wl) (PInf wl) (PInfRed wl) (PCheck wl).
  Proof.
    subst PTy PInf PInfRed PCheck.
    apply AlgoTypingInduction.
    - constructor.
    - intros * ? ? ? IHB **.
      cbn.
      econstructor.
      + now eauto.
      + now eapply IHB with(ρ := wk_up _ ρ).
    - intros.
      now econstructor.
    - now constructor.
    - now constructor.
    - intros * ? ? ? IHB **.
      rewrite <-wk_sig.
      econstructor.
      + now eauto.
      + now eapply IHB.
    - intros; rewrite <- wk_Id; econstructor; eauto.
    - constructor.
      + now intros ?%isCanonical_ren.
      + eauto. 
    - intros.
      eapply typing_meta_conv.
      + now econstructor ; eapply in_ctx_wk.
      + reflexivity.
    - intros * ? ? ? IHB.
      cbn.
      econstructor.
      + eauto.
      + now eapply IHB with(ρ := wk_up _ ρ).
    - intros * ? ? ? IHt ? ?.
      cbn.
      econstructor.
      + now eauto.
      + now eapply IHt with(ρ := wk_up _ ρ).
    - intros.
      cbn in *.
      eapply typing_meta_conv.
      + now econstructor.
      + now asimpl.
    - now econstructor.
    - now econstructor.
    - now econstructor.
    - intros * ? IHn ? IHP ? IHz ? IHs *.
      cbn in *.
      eapply typing_meta_conv.
      1: econstructor.
      + eauto.
      + eapply IHP with (ρ := wk_up _ ρ).
      + eapply typing_meta_conv.
        1: eapply IHz.
        now bsimpl.
      + eapply typing_meta_conv.
        1: eapply IHs.
        unfold elimSuccHypTy.
        now bsimpl.
      + now bsimpl.
    - now econstructor.
    - now econstructor.
    - now econstructor.
    - intros ; cbn.
      now econstructor.
    - intros * ? IHn ? IHP ? IHt ? IHf *.
      cbn in *.
      eapply typing_meta_conv.
      1: econstructor.
      + eauto.
      + eapply IHP with (ρ := wk_up _ ρ).
      + eapply typing_meta_conv.
        1: eapply IHt.
        now bsimpl.
      + eapply typing_meta_conv.
        1: eapply IHf.
        now bsimpl.
      + now bsimpl.
    - intros.
      now econstructor.
    - intros * ? IHe ? IHP *.
      cbn in *.
      eapply typing_meta_conv.
      1: econstructor.
      + eauto.
      + eapply IHP with (ρ := wk_up _ ρ).
      + now bsimpl. 
    - intros * ??? IHB *.
      rewrite <- wk_sig.
      econstructor; eauto.
    - intros * ???????? *.
      rewrite <- wk_pair, <-wk_sig.
      econstructor.
      1-3: now eauto.
      rewrite <- subst_ren_wk_up; eauto.
    - intros * ?? *.
      rewrite <- wk_fst; now econstructor.
    - intros ? A ?? ? IH *.
      rewrite <- wk_snd, (subst_ren_wk_up (A:=A)).
      econstructor.
      now eapply IH.
    - intros; rewrite <- wk_Id; econstructor; eauto.
    - intros; rewrite <- wk_refl; econstructor; eauto.
    - intros; erewrite <- wk_idElim, subst_ren_wk_up2; econstructor; eauto.
      + rewrite 2!(wk_up_wk1 ρ); eauto.
      + rewrite wk_refl, <- subst_ren_wk_up2; eauto.
    - intros.
      econstructor.
      + eauto.
      + eauto using credalg_wk.
    - intros.
      econstructor.
      + eauto.
      + now eapply algo_conv_wk.
  Qed.

  Corollary algo_conv_shift (wl : wfLCon) : AlgoConvInductionConcl
      (fun (wl : wfLCon) (Γ : context) (A B : term) => forall T, [Γ,, T |- A⟨↑⟩ ≅ B⟨↑⟩]< wl >)
      (fun (wl : wfLCon) (Γ : context) (A B : term) => forall T, [Γ,, T |- A⟨↑⟩ ≅h B⟨↑⟩]< wl >)
      (fun (wl : wfLCon) (Γ : context) (A m n : term) => forall T, [Γ,, T |- m⟨↑⟩ ~ n⟨↑⟩ ▹ A⟨↑⟩]< wl >)
      (fun (wl : wfLCon) (Γ : context) (A m n : term) => forall T, [Γ,, T |- m⟨↑⟩ ~h n⟨↑⟩ ▹ A⟨↑⟩]< wl >)
      (fun (wl : wfLCon) (Γ : context) (A t u : term) => forall T, [Γ,, T |- t⟨↑⟩ ≅ u⟨↑⟩ : A⟨↑⟩]< wl >)
      (fun (wl : wfLCon) (Γ : context) (A t u : term) => forall T, [Γ,, T |- t⟨↑⟩ ≅h u⟨↑⟩ : A⟨↑⟩]< wl >)
  wl.
  Proof.
    red.
    repeat match goal with |- _ × _ => split end.
    all: intros Γ * Hty T.
    all: eapply algo_conv_wk in Hty.
    all: specialize (Hty _ (@wk1 Γ T)).
    all: repeat rewrite <- (extRen_term _ _ (@wk1_ren Γ T)) ; refold.
    all: now eapply Hty.
  Qed.

  Corollary algo_typing_shift (wl : wfLCon) : AlgoTypingInductionConcl wl
  (fun  (Γ : context) (A : term) => forall T, [Γ,, T |- A⟨↑⟩]< wl >)
  (fun  (Γ : context) (A t : term) => forall T, [Γ,, T |- t⟨↑⟩ ▹ A⟨↑⟩]< wl >)
  (fun  (Γ : context) (A t : term) => forall T, [Γ,, T |- t⟨↑⟩ ▹h A⟨↑⟩]< wl >)
  (fun  (Γ : context) (A t : term) => forall T, [Γ,, T |- t⟨↑⟩ ◃ A⟨↑⟩]< wl >).
  Proof.
  red.
  repeat match goal with |- _ × _ => split end.
  all: intros Γ * Hty T.
  all: eapply algo_typing_wk in Hty.
  all: specialize (Hty _ (@wk1 Γ T)).
  all: repeat rewrite <- (extRen_term _ _ (@wk1_ren Γ T)) ; refold.
  all: now eapply Hty.
  Qed.

End TypingWk.

(** ** Relation to weak-head normal forms *)

(** We show that the predicates that should apply only to weak-head normal forms/neutrals
indeed imply that the relevant arguments are such weak-head normal forms/neutrals. *)
Section AlgTypingWh.

  Let PTyEq (wl : wfLCon) (Γ : context) (A B : term) := True.
  Let PTyRedEq (wl : wfLCon) (Γ : context) (A B : term) := 
    isType A × isType B.
  Let PNeEq (wl : wfLCon) (Γ : context) (A t u : term) := 
    whne t × whne u.
  Let PNeRedEq (wl : wfLCon) (Γ : context) (A t u : term) :=
    [× whne t, whne u & whnf A].
  Let PTmEq (wl : wfLCon) (Γ : context) (A t u : term) := True.
  Let PTmRedEq (wl : wfLCon) (Γ : context) (A t u : term) := 
    [× whnf t, whnf u & isType A].

  Theorem algo_conv_wh (wl : wfLCon) :
    AlgoConvInductionConcl PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq wl.
  Proof.
    subst PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq; cbn.
    apply AlgoConvInduction.
    all: intros ; prod_splitter ; prod_hyp_splitter.
    all: try solve [now constructor].
    all: now gen_typing.
  Qed.
End AlgTypingWh.


(** ** Determinism: there is at most one inferred type *)

Section AlgoTypingDet.

Import AlgorithmicTypingData.

Let PTyEq (wl : wfLCon) (Γ : context) (A B : term) := True.
Let PTyRedEq (wl : wfLCon) (Γ : context) (A B : term) := True.
Let PNeEq (wl : wfLCon) (Γ : context) (A t u : term) := 
  forall A' u', [Γ |-[al] t ~ u' ▹ A']< wl > -> A' = A.
Let PNeRedEq (wl : wfLCon) (Γ : context) (A t u : term) :=
  forall A' u', [Γ |-[al] t ~h u' ▹ A']< wl > -> A' = A.
Let PTmEq (wl : wfLCon) (Γ : context) (A t u : term) := True.
Let PTmRedEq (wl : wfLCon) (Γ : context) (A t u : term) := True.

Theorem algo_conv_det (wl : wfLCon) :
  AlgoConvInductionConcl PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq wl.
Proof.
  subst PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq; cbn.
  apply AlgoConvInduction.
  all: try easy.
  - intros * ? * Hconv.
    inversion Hconv ; subst ; clear Hconv.
    now eapply in_ctx_inj.
  - intros * ? IH ? ? ?? Hconv.
    inversion Hconv ; subst ; clear Hconv ; refold.
    apply IH in H6.
    now inversion H6.
  - intros * ? IH ?????? ?? Hconv.
    inversion Hconv ; subst ; clear Hconv ; refold.
    now reflexivity.
  - intros * ? IH ?????? ?? Hconv.
    inversion Hconv ; subst ; clear Hconv ; refold.
    now reflexivity.
  - intros * ? IH ?? ?? Hconv.
    inversion Hconv ; subst ; clear Hconv ; refold.
    now reflexivity.
  - intros * ? IH ?? Hconv.
    inversion Hconv; subst; clear Hconv; refold.
    apply IH in H3.
    now inversion H3.
  - intros * ? IH ?? Hconv.
    inversion Hconv; subst; clear Hconv; refold.
    apply IH in H3.
    now inversion H3.
  - intros * ? IH (*? _ ? _ ? _*) ? _ ? _ ? _ ? _ ? _ * Hconv.
    inversion Hconv; now subst.
  - intros * ? IH ? ?  Hconv.
    inversion Hconv ; subst ; clear Hconv ; refold.
    reflexivity.
  - intros * ? IH ???? Hconv.
    inversion Hconv ; subst ; clear Hconv ; refold.
    eapply IH in H2 as ->.
    eapply whred_det ; eauto.
    all: now eapply isType_whnf.
Qed.

Theorem algo_typing_det (wl : wfLCon) :
  AlgoTypingInductionConcl wl
    (fun _ _ => True)
    (fun Γ A t => forall A', [Γ |-[al] t ▹ A']< wl > -> A' = A)
    (fun Γ A t => whnf A -> forall A', whnf A' -> [Γ |-[al] t ▹h A']< wl > -> A' = A)
    (fun _ _ _ => True).
Proof.
  apply AlgoTypingInduction.
  all: try easy.
  - intros * ? ? Hinf.
    inversion Hinf ; subst ; clear Hinf.
    now eapply in_ctx_inj.
  - intros * ? IHA ? IHB ? Hconv.
    now inversion Hconv.
  - intros * ?? ? IHt ? Hconv.
    inversion Hconv ; subst ; clear Hconv ; refold.
    eapply IHt in H7 ; subst.
    now reflexivity.
  - intros * ? IHf ?? ? Hconv.
    inversion Hconv ; subst ; clear Hconv ; refold.
    eapply IHf in H6.
    2-3:gen_typing.
    now inversion H6.
  - intros * Hconv.
    now inversion Hconv.
  - intros * Hconv.
    now inversion Hconv.
  - intros * ?? ? Hconv.
    now inversion Hconv.
  - intros * ? IH ?????? ? Hconv.
    now inversion Hconv.
  - intros * Hconv.
    now inversion Hconv.
  - intros * Hconv.
    now inversion Hconv.
  - intros * Hconv.
    now inversion Hconv.
  - intros * ? IH ? Hconv.
    now inversion Hconv.
  - intros * ? IH ??????? Hconv.
    now inversion Hconv.
  - intros * Hconv.
    now inversion Hconv.
  - intros * ? IH ?? ? Hconv.
    now inversion Hconv.
  - intros * ? IH ??? Hconv.
    now inversion Hconv.
  - intros * ????????? Hconv.
    now inversion Hconv.
  - intros * ? IH ? Hconv.
    inversion Hconv; subst; refold.
    apply IH in H3; try constructor.
    now inversion H3.
  - intros * ? IH ? Hconv.
    inversion Hconv; subst; refold.
    apply IH in H3; try constructor.
    now inversion H3.
  - intros * ?????? * Hconv; inversion Hconv; now subst.
  - intros * ???? * Hconv; now inversion Hconv.
  - intros * ???????????? * Hconv; now inversion Hconv.
  - intros * ? IH ?? ?? Hconv.
    inversion Hconv ; subst ; clear Hconv ; refold.
    eapply IH in H3 ; subst.
    now eapply whred_det.
Qed.

End AlgoTypingDet.
