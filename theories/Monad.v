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

Fixpoint DTree_bind (k : wfLCon) (F : forall k' (f : k' ≤ε k), DTree k')
  (d : DTree k) : DTree k.
Proof.
  refine (match d with
          | leaf _ => F k (wfLCon_le_id _)
          | @ϝnode _ n ne dt df => @ϝnode _ n ne _ _
          end).
  + unshelve eapply DTree_bind ; [ | assumption].
    intros k' f ; eapply F, wfLCon_le_trans ; [eassumption | ].
    now eapply LCon_le_step, wfLCon_le_id.
  + unshelve eapply DTree_bind ; [ | assumption].
    intros k' f ; eapply F, wfLCon_le_trans ; [eassumption | ].
    now eapply LCon_le_step, wfLCon_le_id.
Defined.

Fixpoint DTree_Ltrans (k k' : wfLCon) (f : k' ≤ε k) (d : DTree k) : DTree k'.
Proof.
  refine (match d with
          | leaf _ => leaf _
          | @ϝnode _ n ne dt df => _
          end).
  destruct (decidInLCon k' n) as [ Hint | Hinf | Hnotin].
  - refine (DTree_Ltrans (k,,l (ne, true)) k' _ dt).
    now eapply LCon_le_in_LCon.
  - refine (DTree_Ltrans (k,,l (ne, false)) k' _ df).
    now eapply LCon_le_in_LCon.
  - refine (@ϝnode _ n Hnotin _ _).
    + unshelve eapply (DTree_Ltrans _ _ _ dt).
      now eapply LCon_le_up.
    + unshelve eapply (DTree_Ltrans _ _ _ df).
      now eapply LCon_le_up.
Defined.

Fixpoint DTree_fusion (k : wfLCon) (d d' : DTree k) : DTree k.
Proof.
  refine (match d with
          | leaf _ => d'
          | @ϝnode _ n ne dt df => @ϝnode _ n ne _ _
          end).
  - refine (DTree_fusion _ dt _).
    unshelve eapply (DTree_Ltrans _ _ _ d').
    eapply LCon_le_step ; now apply wfLCon_le_id.
  - refine (DTree_fusion _ df _).
    unshelve eapply (DTree_Ltrans _ _ _ d').
    eapply LCon_le_step ; now apply wfLCon_le_id.
Defined.


Fixpoint over_tree (k k' : wfLCon) (d : DTree k) : SProp :=
  match d with
  | leaf _ => k' ≤ε k
  | @ϝnode _ n ne kt kf =>
      match (decidInLCon k' n) with
      | or_inltrue H => over_tree (k ,,l (ne, true)) k' kt
      | or_inlfalse H => over_tree (k ,,l (ne, false)) k' kf
      | or_notinl _ => SFalse
      end
  end.

(*Inductive over_tree (k k' : wfLCon) :
  DTree k -> SProp :=
| over_leaf : k' ≤ε k -> over_tree k k' (leaf k)
| over_nodeT {n} {ne : not_in_LCon (pi1 k) n} kt kf :
  in_LCon k' n true ->
  over_tree (k ,,l (ne, true)) k' kt ->
  over_tree k k' (ϝnode (ne := ne) k kt kf)
| over_nodeF {n} {ne : not_in_LCon (pi1 k) n} kt kf :
  in_LCon k' n false ->
  over_tree (k ,,l (ne, false)) k' kf ->
  over_tree k k' (ϝnode (ne := ne) k kt kf).
*)

Lemma over_tree_le {k k' d} : over_tree k k' d -> k' ≤ε k.
Proof.
  induction d as [ | k n ne kt IHt kf IHf] ; cbn ; intros H ; auto.
  destruct (decidInLCon k' n).
  - exact ((IHt H) •ε (LCon_le_step _ (wfLCon_le_id _))).
  - exact ((IHf H) •ε (LCon_le_step _ (wfLCon_le_id _))).
  - now inversion H.
Qed.

Lemma le_over_tree {k k' k'' d} : k'' ≤ε k' -> over_tree k k' d -> over_tree k k'' d.
Proof.
  induction d as [ | k n ne kt IHt kf IHf] ; cbn ; intros Hinf Hinf' ; auto.
  - now eapply wfLCon_le_trans.
  - destruct (decidInLCon k' n).
    + erewrite (decidInLCon_true (Hinf _ _ i)).
      now eapply IHt.
    + erewrite (decidInLCon_false (Hinf _ _ i)).
      now eapply IHf.
    + now inversion Hinf'.
Qed.
  

Lemma over_tree_Ltrans (k k' k'' : wfLCon) (f : k' ≤ε k) (d : DTree k) :
  over_tree k' k'' (DTree_Ltrans k k' f d) -> over_tree k k'' d.
Proof.
  intros Hyp ; assert (f' : k'' ≤ε k') by now eapply over_tree_le.
  revert k' k'' f f' Hyp ; induction d as [  | k n ne kt IHt kf IHf] ; cbn ; intros k' k'' f f' Hyp.
  - eapply wfLCon_le_trans ; eassumption.
  - destruct (decidInLCon k' n).
    + destruct (decidInLCon k'' n).
      * eapply IHt ; eassumption.
      * exfalso.
        assert (H := uniqueinLCon k''.(pi2) (f' _ _ i) i0) ; now inversion H.
      * exfalso.
        eapply notinLConnotinLCon ; eauto.
    + destruct (decidInLCon k'' n).
      * exfalso.
        assert (H := uniqueinLCon k''.(pi2) (f' _ _ i) i0) ; now inversion H.
      * eapply IHf ; eassumption.
      * exfalso.
        eapply notinLConnotinLCon ; eauto.
    + cbn in * ; destruct (decidInLCon k'' n).
      * eapply IHt ; [ | eassumption].
        eapply wfLCon_le_trans ; [ eapply LCon_le_in_LCon ; eassumption | now eapply (idε _)].
      * eapply IHf ; [ | eassumption].
        eapply wfLCon_le_trans ; [ eapply LCon_le_in_LCon ; eassumption | now eapply (idε _)].
      * assumption.
Qed.

Lemma Ltrans_over_tree (k k' k'' : wfLCon) (f : k' ≤ε k) (f' : k'' ≤ε k') (d : DTree k) :
  over_tree k k'' d -> over_tree k' k'' (DTree_Ltrans k k' f d).
Proof.
  revert k' k'' f f' ; induction d as [  | k n ne kt IHt kf IHf] ; intros * f' ; cbn.
  - now eauto.
  - destruct (decidInLCon k' n).
    + rewrite (decidInLCon_true (f' n _ i)) ; intros H.
      now eapply IHt.
    + rewrite (decidInLCon_false (f' n _ i)) ; intros H.
      now eapply IHf.
    + cbn in *.
      destruct (decidInLCon k'' n) ; cbn ; intros H ; eauto.
      * eapply IHt ; eauto.
        now eapply LCon_le_in_LCon ; eauto.
      * eapply IHf ; eauto.
        now eapply LCon_le_in_LCon ; eauto.
Qed.
      
Lemma over_tree_fusion_l k k' d d' :
  over_tree k k' (DTree_fusion k d d') ->
  over_tree k k' d.
Proof.
  revert d' ; induction d as [ | k n ne kt IHt kf IHf] ; intros d' Hov.
  - eapply over_tree_le ; eassumption.
  - cbn in * ; subst.
    destruct (decidInLCon k' n).
    + eapply IHt ; eassumption.
    + eapply IHf ; eassumption.
    + assumption.
Qed.


Lemma over_tree_fusion_r k k' d d' :
  over_tree k k' (DTree_fusion k d d') ->
  over_tree k k' d'.
Proof.
  revert d' ; induction d as [ | k n ne kt IHt kf IHf] ; intros d' Hov.
  - eassumption.
  - cbn in * ; subst.
    destruct (decidInLCon k' n).
    + eapply over_tree_Ltrans, IHt ; eassumption.
    + eapply over_tree_Ltrans, IHf ; eassumption.
    + now inversion Hov.
Qed.

Arguments over_tree_fusion_l [_ _ _ _] _.
Arguments over_tree_fusion_r [_ _ _ _] _.

Fixpoint DTree_bind_over (k : wfLCon) (d : DTree k) :
  (forall k' (H : over_tree k k' d), DTree k') -> DTree k.
Proof.
  refine (match d with
          | leaf _ => fun F => _
          | @ϝnode _ n ne dt df => fun F => _
          end).
  - now eapply F, wfLCon_le_id.
  - eapply (@ϝnode _ n ne).
    + unshelve eapply DTree_bind_over ; [ assumption | ].
      intros k' f ; eapply F. cbn in *.
      now rewrite (@decidInLCon_true k' n (over_tree_le f _ _ (in_here_l _))).
    + unshelve eapply DTree_bind_over ; [ assumption | ].
      intros k' f ; eapply F. cbn in *.
      now rewrite (@decidInLCon_false k' n (over_tree_le f _ _ (in_here_l _))).
Defined.

Lemma DTree_bind_over_over k k' d P :
  over_tree k k' (DTree_bind_over k d P) ->
  over_tree k k' d.
Proof.
  induction d ; cbn in * ; intros H.
  - now eapply over_tree_le.
  - destruct (decidInLCon k' n) ; cbn in *.
    + eapply IHd1.
      eassumption.
    + eapply IHd2.
      eassumption.
    + assumption.
Qed.

Fixpoint DTree_path (k k' : wfLCon) (d : DTree k) :
  over_tree k k' d -> wfLCon.
Proof.
  refine (match d with
          | leaf _ => fun H => k
          | @ϝnode _ n ne dt df => _
          end).
  cbn in *.
  refine (match decidInLCon k' n with
          | or_inltrue _ => _
          | or_inlfalse _ => _
          | or_notinl _ => _
          end).
  all: refine (fun H => _).
  1,2: exact (DTree_path _ _ _ H).
  now inversion H.
Defined.

Lemma DTree_path_le k k' d (Hover : over_tree k k' d) :
  (DTree_path k k' d Hover) ≤ε k.
Proof.
  induction d ; cbn.
  - now eapply wfLCon_le_id.
  - cbn in *.
    revert Hover ; destruct (decidInLCon k' n) ; intros Hover.
    + eapply wfLCon_le_trans ; [eapply IHd1 | ].
      now eapply LCon_le_step, wfLCon_le_id.
    + eapply wfLCon_le_trans ; [eapply IHd2 | ].
      now eapply LCon_le_step, wfLCon_le_id.
    + now destruct Hover.
Qed.
    
Fixpoint DTree_path_over k k' d :
  forall Hover : over_tree k k' d,
    over_tree k (DTree_path k k' d Hover) d.
Proof.
  refine (match d as d0 return
                forall Hover,
                  over_tree k (DTree_path k k' d0 Hover) d0
          with
          | leaf _ => fun Hover => _
          | @ϝnode _ n ne dt df => _
          end).
  - now eapply wfLCon_le_id.
  - cbn in *.
     destruct (decidInLCon k' n) ; cbn in * ; intros Hover.
    + rewrite (decidInLCon_true (DTree_path_le _ k' dt Hover _ _ (in_here_l _))).
      now eapply DTree_path_over.
    + rewrite (decidInLCon_false (DTree_path_le _ k' df Hover _ _ (in_here_l _))).
      now eapply DTree_path_over.
    + now destruct Hover.
Defined.

Lemma DTree_path_inf k k' d Hover :
  k' ≤ε (DTree_path k k' d Hover).
Proof.
  induction d as [  | k n ne kt IHt kf IHf] ; cbn in * ; [assumption | ].
  destruct (decidInLCon k' n) ; cbn in *.
  - now apply IHt.
  - now apply IHf.
  - now inversion Hover.
Qed.


Lemma DTree_bind_DTree_path (k k' : wfLCon) (d : DTree k)
  (P : forall k' (H : over_tree k k' d), DTree k')
  (Hover : over_tree k k' d)
  (Hover' : over_tree k k' (DTree_bind_over k d P)) :
  over_tree (DTree_path k k' d Hover) k' (P _ (DTree_path_over k k' d Hover)).
Proof.
  revert P Hover Hover'.
  induction d as [  | k n ne kt IHt kf IHf] ; cbn in * ; intros.
  - assumption.
  - destruct (decidInLCon k' n) ; cbn in *.
    + set (P' := fun (k' : wfLCon) (f : over_tree (k,,l (ne, true)) k' kt) =>
                 P k'
                   (@eq_sind_r (or_inLCon k' n)
                      (@or_inltrue k' n
                         (@over_tree_le (k,,l (ne, true)) k' kt f n true (@in_here_l k n true)))
                      (fun o : or_inLCon k' n =>
                       match o with
                       | @or_inltrue _ _ _ => over_tree (k,,l (ne, true)) k' kt
                       | @or_inlfalse _ _ _ => over_tree (k,,l (ne, false)) k' kf
                       | @or_notinl _ _ _ => SFalse
                       end) f (decidInLCon k' n)
                      (@decidInLCon_true k' n
                         (@over_tree_le (k,,l (ne, true)) k' kt f n true (@in_here_l k n true))))).
      now eapply (IHt P' Hover Hover').
    + set (P' := fun (k' : wfLCon) (f : over_tree (k,,l (ne, false)) k' kf) =>
                 P k'
                   (@eq_sind_r (or_inLCon k' n)
                      (@or_inlfalse k' n
                         (@over_tree_le (k,,l (ne, _)) k' kf f n _ (@in_here_l k n _)))
                      (fun o : or_inLCon k' n =>
                       match o with
                       | @or_inltrue _ _ _ => over_tree (k,,l (ne, true)) k' kt
                       | @or_inlfalse _ _ _ => over_tree (k,,l (ne, false)) k' kf
                       | @or_notinl _ _ _ => SFalse
                       end) f (decidInLCon k' n)
                      (@decidInLCon_false k' n
                         (@over_tree_le (k,,l (ne, false)) k' kf f n _ (@in_here_l k n _))))).
      now eapply (IHf P' Hover Hover').
    + now destruct Hover.
Qed.

      
Lemma split_to_over_tree 
  (P : wfLCon -> Type)
  (Pe : forall wl n (ne : not_in_LCon (pi1 wl) n), P (wl ,,l (ne, true)) -> P (wl ,,l (ne, false)) -> P wl)
  (wl : wfLCon)
  (d : DTree wl)
  (H : forall wl', over_tree wl wl' d -> P wl') : P wl. 
Proof.
  induction d.
  - apply H.
    now intros n b Hin.
  - apply (Pe _ n ne).
    + apply IHd1.
      intros wl' Hover ; cbn in *.
      apply H.
      unshelve erewrite (decidInLCon_true _) ; [ | assumption].
      apply (over_tree_le Hover) ; now constructor.
    + apply IHd2.
      intros wl' Hover ; cbn in *.
      apply H.
      unshelve erewrite (decidInLCon_false _) ; [ | assumption].
      apply (over_tree_le Hover) ; now constructor.
Qed.

Lemma dsplit_to_over_tree (wl : wfLCon)
  (P : forall wl', wl' ≤ε wl -> Type)
  (Pe : forall wl' n (ne : not_in_LCon (pi1 wl') n) f ft ff,
      P (wl' ,,l (ne, true)) ft -> P (wl' ,,l (ne, false)) ff -> P wl' f)
  (d : DTree wl)
  (H : forall wl' f, over_tree wl wl' d -> P wl' f) : P wl (idε _). 
Proof.
  enough (Hyp : forall wl' f, P wl' f) by apply Hyp.
  revert P Pe H.
  induction d ; intros P Pe H wl' f.
  - now apply H.
  - cbn in * ; destruct (decidInLCon wl' n).
    + pose proof (Hinf := LCon_le_step (l := k) (b := true) ne (wfLCon_le_id _)).
      specialize (IHd1 (fun wl' f => P wl' (wfLCon_le_trans f Hinf))).
      cbn in *.
      assert (Hinf' : wl' ≤ε (k,,l (ne, true))).
      { now eapply LCon_le_in_LCon. }
      change (P wl' (Hinf' •ε Hinf)).
      eapply IHd1.
      * intros ; eauto.
      * intros wl'' f' Hover.
        apply H ; cbn.
        unshelve erewrite (decidInLCon_true _) ; [ | assumption].
        now eapply f'; econstructor.
    + pose proof (Hinf := LCon_le_step (l := k) (b := false) ne (wfLCon_le_id _)).
      specialize (IHd2 (fun wl' f => P wl' (wfLCon_le_trans f Hinf))).
      cbn in *.
      assert (Hinf' : wl' ≤ε (k,,l (ne, false))).
      { now eapply LCon_le_in_LCon. }
      change (P wl' (Hinf' •ε Hinf)).
      eapply IHd2.
      * intros ; eauto.
      * intros wl'' f' Hover.
        apply H ; cbn.
        unshelve erewrite (decidInLCon_false _) ; [ | assumption].
        now eapply f'; econstructor.
    + unshelve eapply (Pe _ _ n0).
      1,2: now eapply wfLCon_le_trans ; [ eapply LCon_le_step | eapply (idε _)].
      * pose proof (Hinf := LCon_le_step (l := k) (b := true) ne (wfLCon_le_id _)).
        specialize (IHd1 (fun wl' f => P wl' (wfLCon_le_trans f Hinf))).
        cbn in *.
        pose proof (Hinf' := LCon_le_up (b := true) ne n0 f).
        change (P (wl',,l (n0, true)) (Hinf' •ε Hinf)).
        eapply IHd1 ; [now eauto |..].
        intros wl'' f' Hover.
        eapply H.
        unshelve erewrite (decidInLCon_true _) ; [ | assumption].
        now eapply f'; econstructor.
      * pose proof (Hinf := LCon_le_step (l := k) (b := false) ne (wfLCon_le_id _)).
        specialize (IHd2 (fun wl' f => P wl' (wfLCon_le_trans f Hinf))).
        cbn in *.
        pose proof (Hinf' := LCon_le_up (b := false) ne n0 f).
        change (P (wl',,l (n0, false)) (Hinf' •ε Hinf)).
        eapply IHd2 ; [now eauto |..].
        intros wl'' f' Hover.
        eapply H.
        unshelve erewrite (decidInLCon_false _) ; [ | assumption].
        now eapply f'; econstructor.
Qed.        

Section Typing.

  Context `{GenericTypingProperties}.
  
  Lemma wfc_over_tree {wl Γ} (d : DTree wl) :
    (forall wl', over_tree wl wl' d -> [ |- Γ ]< wl' >) ->
    [ |- Γ ]< wl >.
  Proof.
    apply split_to_over_tree.
    intros * Ht Hf ; now eapply (wfc_ϝ Ht Hf).
  Qed.

  Lemma wft_over_tree {wl Γ A} (d : DTree wl) :
    (forall wl', over_tree wl wl' d -> [ Γ |- A ]< wl' >) ->
    [ Γ |- A ]< wl >.
  Proof.
    apply split_to_over_tree.
    intros * Ht Hf ; now eapply (wft_ϝ Ht Hf).
  Qed.
  
  Lemma ty_over_tree {wl Γ t A} (d : DTree wl) :
    (forall wl', over_tree wl wl' d -> [Γ |- t : A]< wl' >) ->
    [Γ |- t : A]< wl >.
  Proof.
    apply split_to_over_tree.
    intros * Ht Hf ; now eapply (ty_ϝ Ht Hf).
  Qed.

  Lemma convty_over_tree {wl Γ A B} (d : DTree wl) :
    (forall wl', over_tree wl wl' d -> [Γ |- A ≅ B]< wl' >) ->
    [Γ |- A ≅ B]< wl >.
  Proof.
    apply split_to_over_tree.
    intros * Ht Hf ; now eapply (convty_ϝ Ht Hf).
  Qed.

  Lemma convtm_over_tree {wl Γ t u A} (d : DTree wl) :
    (forall wl', over_tree wl wl' d -> [Γ |- t ≅ u : A]< wl' >) ->
    [Γ |- t ≅ u : A]< wl >.
  Proof.
    apply split_to_over_tree.
    intros * Ht Hf ; now eapply (convtm_ϝ Ht Hf).
  Qed.

  Lemma convneu_over_tree {wl Γ t u A} (d : DTree wl) :
    (forall wl', over_tree wl wl' d -> [Γ |- t ~ u : A]< wl' >) ->
    [Γ |-  t ~ u : A]< wl >.
  Proof.
    apply split_to_over_tree.
    intros * Ht Hf ; now eapply (convneu_ϝ Ht Hf).
  Qed.

End Typing.


