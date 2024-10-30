From LogRel.AutoSubst Require Import core unscoped Ast Extra.
Require Import PeanoNat.
From LogRel Require Import Utils BasicAst Notations Context LContexts NormalForms Weakening GenericTyping.

Set Primitive Projections.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

Definition Type_le_step (wl : wfLCon) (n : nat) (ne : not_in_LCon wl n) (b : bool)
  (P : forall wl', wl' ≤ε wl -> Type) : 
  forall wl', wl' ≤ε wl,,l (ne, b) -> Type :=
  fun wl' f => P wl' (wfLCon_le_trans f (LCon_le_step _ (wfLCon_le_id _))).
Arguments Type_le_step [_ _ _ _] _ [_] _.

Definition Pred_le_step (wl : wfLCon) (n : nat) (ne : not_in_LCon wl n) (b : bool)
  (P : forall wl', wl' ≤ε wl -> Type)
  (Q : forall wl' (f: wl' ≤ε wl), P wl' f -> Type)  :
  forall wl' (f : wl' ≤ε wl,,l (ne, b)), Type_le_step P f -> Type :=
  fun wl' f p => Q wl' (wfLCon_le_trans f (LCon_le_step _ (wfLCon_le_id _))) p.
Arguments Pred_le_step [_ _ _ _ _] _ [_] _.

Definition dPred_le_step (wl : wfLCon)
  (n : nat) (ne : not_in_LCon wl n) (b : bool)
  (P : forall wl', wl' ≤ε wl -> Type)
  (Q : forall wl' (f: wl' ≤ε wl), P wl' f -> Type)
  (R : forall wl' (f : wl' ≤ε wl) (p : P wl' f), Q wl' f p -> Type) :
  forall wl' (f : wl' ≤ε wl,,l (ne, b)) (p : Type_le_step P f), Pred_le_step Q f p -> Type :=
  fun wl' f p q => R wl' (wfLCon_le_trans f (LCon_le_step _ (wfLCon_le_id _))) p q.
Arguments dPred_le_step [_ _ _ _ _ _] _ [_] _.


Definition Type_le_down (wl wl' : wfLCon) (f: wl' ≤ε wl)
  (P : forall wl', wl' ≤ε wl -> Type) : 
  forall wl'', wl'' ≤ε wl' -> Type :=
  fun wl'' f' => P wl'' (wfLCon_le_trans f' f).
Arguments Type_le_down [_ _] _ _ [_] _.

Definition Pred_le_down (wl wl' : wfLCon) (f: wl' ≤ε wl)
  (P : forall wl', wl' ≤ε wl -> Type)
  (Q : forall wl' (f: wl' ≤ε wl), P wl' f -> Type)  :
  forall wl'' (f' : wl'' ≤ε wl'), Type_le_down f P f' -> Type :=
  fun wl'' f' p => Q wl'' (wfLCon_le_trans f' f) p.
Arguments Pred_le_down [_ _] _ [_] _ [_] _.

Definition dPred_le_down (wl wl' : wfLCon) (f: wl' ≤ε wl)
  (P : forall wl', wl' ≤ε wl -> Type)
  (Q : forall wl' (f: wl' ≤ε wl), P wl' f -> Type)
  (R : forall wl' (f : wl' ≤ε wl) (p : P wl' f), Q wl' f p -> Type) :
  forall wl'' (f' : wl'' ≤ε wl') (p : Type_le_down f P f'), Pred_le_down f Q f' p -> Type :=
  fun wl'' f' p q => R wl'' (wfLCon_le_trans f' f) p q.
Arguments dPred_le_down [_ _] _ [_ _] _ [_] _.

(*Inductive Dial@{i} (wl : wfLCon) (P : forall wl', wl' ≤ε wl -> Type@{i}) : Type@{i} :=
| eta : P wl (wfLCon_le_id _) -> Dial wl P
| ϝdig {n} {ne : not_in_LCon (pi1 wl) n} :
  Dial (wl ,,l (ne, true)) (Type_le_step P) ->
  Dial (wl ,,l (ne, false)) (Type_le_step P) ->
  Dial wl P.

Definition Dbind (wl : wfLCon) (P Q : forall wl', wl' ≤ε wl -> Type)
  (f : forall wl' (f : wl' ≤ε wl), P wl' f -> Dial wl' (Type_le_down f Q))
  (p : Dial wl P) : Dial wl Q.
Proof.
  induction p.
  - eapply f ; try eassumption.
  - unshelve eapply ϝdig.
    2: eassumption.
    + eapply IHp1.
      intros ; eapply f ; try eassumption.
    + eapply IHp2.
      intros ; eapply f ; try eassumption.
Qed.

Fixpoint BType (wl : wfLCon)
  (P : forall wl', wl' ≤ε wl -> Type)
  (Q : forall wl' (f: wl' ≤ε wl), P wl' f -> Type)
  (p : Dial wl P) : Type :=
  match p with
  | eta _ _ x => Q wl (wfLCon_le_id _) x
  | ϝdig _ _ pt pf => prod (@BType _ _ (Pred_le_step Q) pt) (BType _ _ (Pred_le_step Q) pf)
  end.

Fixpoint dBType (wl : wfLCon) 
  (P : forall wl', wl' ≤ε wl -> Type)
  (Q : forall wl' (f: wl' ≤ε wl), P wl' f -> Type)
  (R : forall wl' (f : wl' ≤ε wl) (p : P wl' f), Q wl' f p -> Type)
  (p : Dial wl P) :
  BType wl P Q p -> Type :=
  match p as p0 return BType _ _ _ p0 -> Type with
  | eta _ _ x => fun q => R wl (wfLCon_le_id _) x q
  | ϝdig _ _ pt pf => fun q => let (qt, qf) := q in
                               prod (dBType _ _ _ (dPred_le_step R) pt qt)
                                 (dBType _ _ _ (dPred_le_step R) pf qf)
  end.

Fixpoint dBType2 (wl : wfLCon) 
  (P : forall wl', wl' ≤ε wl -> Type)
  (Q : forall wl' (f : wl' ≤ε wl), P wl' f -> Type)
  (R : forall wl' (f : wl' ≤ε wl), P wl' f -> Type)
  (S : forall wl' (f : wl' ≤ε wl) (p : P wl' f), Q wl' f p -> R wl' f p -> Type)
  (p : Dial wl P) :
  BType wl P Q p -> BType wl P R p -> Type :=
  match p as p0 return BType _ _ _ p0 -> BType _ _ _ p0 -> Type with
  | eta _ _ x => fun q r => S wl (wfLCon_le_id _) x q r
  | ϝdig _ _ pt pf => fun q r => let (qt, qf) := q in
                                 let (rt, rf) := r in
                                 prod (dBType2 _ _ _ _
                                         (fun wl' f p q =>
                                            S wl' (f •ε (LCon_le_step _ (wfLCon_le_id _))) p q) pt qt rt)
                                      (dBType2 _ _ _ _
                                         (fun wl' f p q =>
                                            S wl' (f •ε (LCon_le_step _ (wfLCon_le_id _))) p q) pf qf rf)
  end.

(*Fixpoint BType_dep (wl : wfLCon) (P : wfLCon -> Type)
  (Q : forall wl', P wl' -> Type)
  (R : forall wl' p, Q wl' p -> Type)
  (p : Dial wl P) :
  BType wl P Pe Q Qe p -> Type :=
  match p with
  | eta _ _ x => fun H => R wl x H
  | ϝdig _ _ pt pf => fun H => prod (BType_dep _ P Q R pt (fst H))
                                 (BType_dep _ P Q R pf (snd H))
  end.
 *)
*)
Inductive DTree (k : wfLCon) : Type :=
| leaf : DTree k
| ϝnode {n} {ne : not_in_LCon (pi1 k) n} :
  DTree (k ,,l (ne, true)) ->
  DTree (k ,,l (ne, false)) ->
  DTree k.

Inductive over_tree (k k' : wfLCon) :
  DTree k -> Type :=
| over_leaf : k' ≤ε k -> over_tree k k' (leaf k)
| over_nodeT {n} {ne : not_in_LCon (pi1 k) n} kt kf :
  in_LCon k' n true ->
  over_tree (k ,,l (ne, true)) k' kt ->
  over_tree k k' (ϝnode (ne := ne) k kt kf)
| over_nodeF {n} {ne : not_in_LCon (pi1 k) n} kt kf :
  in_LCon k' n false ->
  over_tree (k ,,l (ne, false)) k' kf ->
  over_tree k k' (ϝnode (ne := ne) k kt kf).

Lemma over_tree_le k k' d : over_tree k k' d -> k' ≤ε k.
Proof.
  induction 1 as [ | ???????? IH | ???????? IH] ; [assumption | | ].
  all: exact (IH •ε (LCon_le_step _ (wfLCon_le_id _))).
Qed.
