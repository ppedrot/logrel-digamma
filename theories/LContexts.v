Require Import ssreflect.
Require Import Coq.Arith.EqNat PeanoNat.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils.

Notation LCon := (list (prod nat bool)).

Inductive in_LCon : LCon -> nat -> bool -> SProp :=
| in_here_l (l : LCon) {n b} : in_LCon (cons (n,b) l) n b
| in_there_l {l : LCon} {n b d} : in_LCon l n b -> in_LCon (cons d l) n b.


Inductive not_in_LCon : LCon -> nat -> SProp :=
| not_in_nil : forall n, not_in_LCon nil n
| not_in_there : forall {l n m b}, ((n = m) -> False) -> not_in_LCon l n
                                 -> not_in_LCon (cons (m,b) l) n.

Inductive wf_LCon : LCon -> SProp :=
| wf_nil : wf_LCon nil
| wf_cons : forall {l n b}, wf_LCon l -> not_in_LCon l n -> wf_LCon (cons (n,b) l).

Inductive SFalse : SProp := .

Inductive Sor (A B : SProp) : SProp :=  Sinl : A -> Sor A B | Sinr : B -> Sor A B.

Inductive Ssig (A : Type) (P : A -> SProp) : Type :=
  Sexist : forall x : A, P x -> Ssig A P.

Arguments Ssig [A]%type_scope P%type_scope.
Arguments Sexist [A]%type_scope P%function_scope x _.

Fixpoint nSucc (n : nat) (t : term) : term :=
  match n with
  | 0 => t
  | S n => tSucc (nSucc n t)
  end.

Definition nat_to_term (n : nat) : term := nSucc n tZero.


Definition bool_to_term (b : bool) : term :=
  match b with
  | true => tTrue
  | false => tFalse
  end.

Record wfLCon :=
  {pi1 : LCon ; pi2 : wf_LCon pi1}.

Coercion pi1 : wfLCon >-> LCon.

Lemma notinLConnotinLCon {l n b} : not_in_LCon l n -> in_LCon l n b -> False.
Proof.
  intros notinl inl.
  enough (H : SFalse) by inversion H.
  induction inl.
  - inversion notinl ; subst.
    easy.
  - eapply IHinl.
    now inversion notinl ; subst.
Qed.

Lemma nattoterminj {n m} : nat_to_term n = nat_to_term m -> n = m.
Proof.
  revert m.
  induction n ; cbn in *.
  - induction m ; try reflexivity ; cbn.
    intro H.
    exfalso.
    change (match tZero as t0 return Type with
            | tZero => False
            | _ => True
            end).
    now rewrite H.
  - intros m H.
    induction m ; cbn in *.
    + exfalso.
      change (match tZero as t0 return Type with
              | tZero => False
              | _ => True
              end).
      now rewrite <- H.
    + erewrite (IHn m) ; try reflexivity.
      now inversion H.
Qed.

Lemma uniqueinLCon {l n b b'} : wf_LCon l -> in_LCon l n b -> in_LCon l n b' -> b = b'.
Proof.
  intros wfl inl inl'.
  destruct b ; destruct b' ; auto.
  all: enough (H : SFalse) by inversion H.
  - revert inl inl' ; induction wfl ; intros.
    + now inversion inl.
    + inversion inl ; subst.
      * inversion inl' ; subst ; trivial.
        exfalso.
        exact (notinLConnotinLCon n1 H3).
      * inversion inl' ; subst.
        -- exfalso ; exact (notinLConnotinLCon n1 H3).
        -- exact (IHwfl H3 H4).
  - revert inl inl' ; induction wfl ; intros.
    + now inversion inl.
    + inversion inl ; subst.
      * inversion inl' ; subst ; trivial.
        exfalso.
        exact (notinLConnotinLCon n1 H3).
      * inversion inl' ; subst.
        -- exfalso ; exact (notinLConnotinLCon n1 H3).
        -- exact (IHwfl H3 H4).
Qed.

Inductive or_inLCon l n : Type :=
| or_inltrue : in_LCon l n true -> or_inLCon l n
| or_inlfalse : in_LCon l n false -> or_inLCon l n
| or_notinl : not_in_LCon l n -> or_inLCon l n.
Arguments or_inltrue [_ _] _.
Arguments or_inlfalse [_ _] _.
Arguments or_notinl [_ _] _.

Fixpoint decidInLCon l n : or_inLCon l n .
Proof.
  unshelve refine (match l with
                   | nil => _
                   | cons (m, b) q => _
                   end).
  - econstructor 3 ; now econstructor.
  - unshelve refine
      (match (decidInLCon q n) with
       | or_inltrue H => _
       | or_inlfalse H => _ 
       | or_notinl H => _
       end).
    + econstructor 1. now econstructor.
    + econstructor 2 ; now econstructor.
    + case (eq_nat_decide n m).
      * intro neqm.
        rewrite <- (proj1 (eq_nat_is_eq n m) neqm).
        case b.
        -- econstructor 1 ; now econstructor.
        -- econstructor 2 ; now econstructor.
      * intro noteq.
        econstructor 3.
        econstructor ; try assumption.
        intro neqm ; rewrite neqm in noteq.
        eapply noteq.
        exact (eq_nat_refl _).
Defined.

Lemma decidInLCon_true (l : wfLCon) n (Hin: in_LCon l n true) :
  decidInLCon l n = or_inltrue Hin.
Proof.
  destruct (decidInLCon l n).
  + reflexivity.
  + exfalso.
    assert (H := uniqueinLCon l.(pi2) Hin i) ; now inversion H.
  + exfalso.
    now eapply notinLConnotinLCon.
Qed.

Lemma decidInLCon_false (l : wfLCon) n (Hin: in_LCon l n false) :
  decidInLCon l n = or_inlfalse Hin.
Proof.
  destruct (decidInLCon l n).
  + exfalso.
    assert (H := uniqueinLCon l.(pi2) Hin i) ; now inversion H.
  + reflexivity.
  + exfalso.
    now eapply notinLConnotinLCon.
Qed.

Lemma decidInLCon_notinLCon (l : wfLCon) n (Hin: not_in_LCon l n) :
  decidInLCon l n = or_notinl Hin.
Proof.
  destruct (decidInLCon l n).
  + exfalso.
    now eapply notinLConnotinLCon.
  + exfalso.
    now eapply notinLConnotinLCon.
  + reflexivity. 
Qed.

Arguments decidInLCon_true [_ _] _.
Arguments decidInLCon_false [_ _] _.
Arguments decidInLCon_notinLCon [_ _] _.

(*  induction l.
  - right.
    now econstructor.
  - induction IHl as [IHl | IHl ].
    + induction IHl as [IHl | IHl].
      * left ; left ; now econstructor.
      * left ; right ; now econstructor.
    + destruct a as [m b].
      case (eq_nat_decide n m).
      * intro neqm.
        rewrite <- (proj1 (eq_nat_is_eq n m) neqm).
        case b.
        -- left ; left ; now econstructor.
        -- left ; right ; now econstructor.
      * intro noteq.
        right.
        econstructor ; try assumption.
        intro neqm ; rewrite neqm in noteq.
        eapply noteq.
        exact (eq_nat_refl _).
Defined.        *)
        
      
Definition wfLCons (l : wfLCon) {n : nat} (ne : not_in_LCon (pi1 l) n) (b : bool) : wfLCon.
Proof.
  exists (cons (n,b) (pi1 l)).
  econstructor ; trivial.
  exact (pi2 l).
Defined.

Notation " l ',,l' ( ne , b ) " := (wfLCons l ne b) (at level 20, ne, b at next level).

Definition LCon_le (l l' : LCon) : SProp :=
  forall n b, in_LCon l' n b -> in_LCon l n b.

Definition wfLCon_le (l l' : wfLCon) : SProp :=
  LCon_le (pi1 l) (pi1 l').

Notation " l ≤ε l' " := (wfLCon_le l l') (at level 40).

Definition wfLCon_le_id l : l ≤ε l := fun n b ne => ne.

Notation " 'idε' " := (wfLCon_le_id) (at level 40).

Definition wfLCon_le_trans {l l' l''} : l ≤ε l' -> l' ≤ε l'' -> l ≤ε l'' :=
  fun f f' n b ne => f n b (f' n b ne).

Notation " a •ε b " := (wfLCon_le_trans a b) (at level 40).

Lemma LCon_le_in_LCon {l l' n b} {ne : not_in_LCon (pi1 l') n} :
  l ≤ε l' -> in_LCon l n b -> l ≤ε (l' ,,l (ne , b)).
Proof.
  intros f inl m b' inl'.
  destruct l as [l wfl] ; destruct l' as [l' wfl'] ; cbn in *.
  unfold wfLCon_le in f ; cbn in f.
  clear wfl wfl'.
  inversion inl' ; subst.
  - assumption.
  - now apply f.
Qed.

Lemma LCon_le_step {l l' n b} (ne : not_in_LCon (pi1 l') n) :
  l' ≤ε l -> l' ,,l (ne , b) ≤ε l.
Proof.
  intros f m b' inl.
  apply in_there_l ; now eapply (f m b').
Qed.
  
Lemma LCon_le_up {l l' n b} (ne : not_in_LCon (pi1 l) n) (ne' : not_in_LCon (pi1 l') n) :
  l' ≤ε l -> l' ,,l (ne' , b) ≤ε (l ,,l (ne , b)).
Proof.
  intros f m b' inl.
  eapply LCon_le_in_LCon.
  - now eapply LCon_le_step.
  - now eapply in_here_l.
  - exact inl.
Qed.

Lemma not_in_LCon_le_not_in_LCon {l l' n} (ne : not_in_LCon (pi1 l') n) :
  l' ≤ε l -> not_in_LCon (pi1 l) n.
Proof.
  intros f ; destruct (decidInLCon l n) as [i | i | ] ; [.. | assumption].
  1,2: exfalso ; eapply notinLConnotinLCon ; eauto.
Qed.
