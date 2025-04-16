From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations LContexts Context NormalForms Weakening GenericTyping Monad LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Induction Irrelevance Reflexivity Transitivity Monotonicity Split.
From LogRel.Substitution Require Import Irrelevance Properties Monotonicity.


Set Universe Polymorphism.

Section Split.
Context `{GenericTypingProperties}.

Lemma validTySplit {wl : wfLCon} {Γ l A} {n : nat} {ne : not_in_LCon wl n}
  {VΓt : [||-v Γ ]< (wl ,,l (ne, true)) >}
  {VΓf : [||-v Γ ]< (wl ,,l (ne, false)) >}
  {VΓ : [||-v Γ]< wl >} :
  [Γ ||-v<l> A | VΓt]< wl ,,l (ne, true) > ->
  [Γ ||-v<l> A | VΓf]< wl ,,l (ne, false) > ->
  [Γ ||-v<l> A | VΓ]< wl >.
Proof.
  intros [VAt VAextt] [VAf VAextf].
  unshelve econstructor.
  - intros ??????.
    destruct (decidInLCon wl' n) as [ i | i | notin].
    + pose (f' := LCon_le_in_LCon (ne := ne) f i).
      pose (f'':= @LCon_le_step wl wl n true ne (wfLCon_le_id _)).
      unshelve eapply VAt ; tea.
      change f with (f' •ε f'') in vσ.
      eapply subst_Ltrans' in vσ.
      unshelve eapply irrelevanceSubst.
      * exists (VPack_Ltrans f'' VΓ).
        now eapply  WfC_Ltrans.
      * assumption.
      * exact vσ.
    + pose (f' := LCon_le_in_LCon (ne := ne) f i).
      pose (f'':= @LCon_le_step wl wl n false ne (wfLCon_le_id _)).
      unshelve eapply VAf ; tea.
      change f with (f' •ε f'') in vσ.
      eapply subst_Ltrans' in vσ.
      unshelve eapply irrelevanceSubst.
      * exists (VPack_Ltrans f'' VΓ).
        now eapply  WfC_Ltrans.
      * assumption.
      * exact vσ.
    + unshelve eapply Split.
      2: exact notin.
      * pose (i := @in_here_l wl' n true).
        pose (f' := @LCon_le_up wl wl' n true ne notin f). 
        pose (f'':= @LCon_le_step wl wl n true ne (wfLCon_le_id _)).
        pose (f''':= @LCon_le_step wl' wl' n true notin (wfLCon_le_id _)).
        unshelve eapply VAt ; tea.
        2: unshelve epose proof (X:= subst_Ltrans f''' _ vσ).
        1,2: now eapply wfc_Ltrans.
        change (f''' •ε f)  with (f' •ε f'') in X.
        eapply subst_Ltrans' in vσ.
        unshelve eapply irrelevanceSubst.
        -- exists (VPack_Ltrans f'' VΓ).
           now eapply  WfC_Ltrans.
        -- now eapply wfc_Ltrans.
        -- assumption.
      * pose (i := @in_here_l wl' n false).
        pose (f' := @LCon_le_up wl wl' n false ne notin f). 
        pose (f'':= @LCon_le_step wl wl n false ne (wfLCon_le_id _)).
        pose (f''':= @LCon_le_step wl' wl' n false notin (wfLCon_le_id _)).
        unshelve eapply VAf ; tea.
        2: unshelve epose proof (X:= subst_Ltrans f''' _ vσ).
        1,2: now eapply wfc_Ltrans.
        change (f''' •ε f)  with (f' •ε f'') in X.
        eapply subst_Ltrans' in vσ.
        unshelve eapply irrelevanceSubst.
        -- exists (VPack_Ltrans f'' VΓ).
           now eapply  WfC_Ltrans.
        -- now eapply wfc_Ltrans.
        -- assumption.
  - cbn.
    intros.
    destruct (decidInLCon wl' n) as [ i | i | notin] ; cbn in *.
    + pose (f' := LCon_le_in_LCon (ne := ne) f i).
      pose (f'':= @LCon_le_step wl wl n true ne (wfLCon_le_id _)).
      unshelve eapply VAextt.
      * change f with (f' •ε f'') in vσ'.
        eapply subst_Ltrans' in vσ'.
        unshelve eapply irrelevanceSubst ; [ | assumption | ]. 
        1: now eapply  WfC_Ltrans.
        exact vσ'.
      * change f with (f' •ε f'') in vσσ'.
        unshelve eapply eqsubst_Ltrans' in vσσ'.
        unshelve eapply irrelevanceSubstEq ; [ | assumption | | ]. 
        1: now eapply  WfC_Ltrans.
        2: exact vσσ'.
    + pose (f' := LCon_le_in_LCon (ne := ne) f i).
      pose (f'':= @LCon_le_step wl wl n false ne (wfLCon_le_id _)).
      unshelve eapply VAextf.
      * change f with (f' •ε f'') in vσ'.
        eapply subst_Ltrans' in vσ'.
        unshelve eapply irrelevanceSubst ; [ | assumption | ]. 
        1: now eapply WfC_Ltrans.
        exact vσ'.
      * change f with (f' •ε f'') in vσσ'.
        unshelve eapply eqsubst_Ltrans' in vσσ'.
        unshelve eapply irrelevanceSubstEq ; [ | assumption | | ]. 
        1: now eapply  WfC_Ltrans.
        2: exact vσσ'.
    + unshelve eapply EqSplit.
      * pose (i := @in_here_l wl' n true).
        pose (f' := @LCon_le_up wl wl' n true ne notin f). 
        pose (f'':= @LCon_le_step wl wl n true ne (wfLCon_le_id _)).
        pose (f''':= @LCon_le_step wl' wl' n true notin (wfLCon_le_id _)).
        unshelve eapply VAextt ; tea.
        -- unshelve epose proof (X:= subst_Ltrans f''' _ vσ').
           1: now eapply wfc_Ltrans.
           change (f''' •ε f)  with (f' •ε f'') in X.
           eapply subst_Ltrans' in X.
           unshelve eapply irrelevanceSubst.
           ++ exists (VPack_Ltrans f'' VΓ).
              now eapply  WfC_Ltrans.
           ++ now eapply wfc_Ltrans.
           ++ assumption.
        -- unshelve epose proof (X:= eqsubst_Ltrans f''' _ _ vσσ').
           1: now eapply wfc_Ltrans.
           change (f''' •ε f)  with (f' •ε f'') in X.
           eapply eqsubst_Ltrans' in X.
           unshelve eapply irrelevanceSubstEq.
           1: cbn ; exists (VPack_Ltrans f'' VΓ) ; now eapply  WfC_Ltrans.
           1:  now eapply wfc_Ltrans.
           2: eassumption.
      * pose (i := @in_here_l wl' n false).
        pose (f' := @LCon_le_up wl wl' n false ne notin f). 
        pose (f'':= @LCon_le_step wl wl n false ne (wfLCon_le_id _)).
        pose (f''':= @LCon_le_step wl' wl' n false notin (wfLCon_le_id _)).
        unshelve eapply VAextf ; tea.
        -- unshelve epose proof (X:= subst_Ltrans f''' _ vσ').
           1: now eapply wfc_Ltrans.
           change (f''' •ε f)  with (f' •ε f'') in X.
           eapply subst_Ltrans' in X.
           unshelve eapply irrelevanceSubst.
           ++ exists (VPack_Ltrans f'' VΓ).
              now eapply  WfC_Ltrans.
           ++ now eapply wfc_Ltrans.
           ++ assumption.
        -- unshelve epose proof (X:= eqsubst_Ltrans f''' _ _ vσσ').
           1: now eapply wfc_Ltrans.
           change (f''' •ε f)  with (f' •ε f'') in X.
           eapply eqsubst_Ltrans' in X.
           unshelve eapply irrelevanceSubstEq.
           1: cbn ; exists (VPack_Ltrans f'' VΓ) ; now eapply  WfC_Ltrans.
           1:  now eapply wfc_Ltrans.
           2: eassumption.
Defined.


Lemma validEqTySplit {wl : wfLCon} {Γ l A B} {n : nat} {ne : not_in_LCon wl n}
  {VΓt : [||-v Γ ]< (wl ,,l (ne, true)) >}
  {VΓf : [||-v Γ ]< (wl ,,l (ne, false)) >}
  {VΓ : [||-v Γ]< wl >}
  {VAt : [Γ ||-v<l> A | VΓt]< wl ,,l (ne, true) >}
  {VAf : [Γ ||-v<l> A | VΓf]< wl ,,l (ne, false) >} :
  [Γ ||-v<l> A ≅ B | VΓt | VAt]< _ > ->
  [Γ ||-v<l> A ≅ B | VΓf | VAf]< _ > ->
  [Γ ||-v<l> A ≅ B | VΓ | validTySplit VAt VAf]< wl >.
Proof.
  intros [VBt] [VBf].
  unshelve econstructor.
  - intros ?????? ; cbn.
    destruct (decidInLCon wl' n) as [ i | i | notin].
    + now eapply VBt.
    + now eapply VBf.
    + eapply EqSplit.
      * now eapply VBt.
      * now eapply VBf.
Qed.

Lemma validEqTySplit' {wl : wfLCon} {Γ l A B} {n : nat} {ne : not_in_LCon wl n}
  {VΓt : [||-v Γ ]< (wl ,,l (ne, true)) >}
  {VΓf : [||-v Γ ]< (wl ,,l (ne, false)) >}
  {VΓ : [||-v Γ]< wl >}
  {VAt : [Γ ||-v<l> A | VΓt]< wl ,,l (ne, true) >}
  {VAf : [Γ ||-v<l> A | VΓf]< wl ,,l (ne, false) >}
  {VA : [Γ ||-v<l> A | VΓ]< wl >}:
  [Γ ||-v<l> A ≅ B | VΓt | VAt]< _ > ->
  [Γ ||-v<l> A ≅ B | VΓf | VAf]< _ > ->
  [Γ ||-v<l> A ≅ B | VΓ | VA ]< wl >.
Proof.
  intros.
  unshelve eapply irrelevanceTyEq ; [eassumption | | ].
  2: now eapply validEqTySplit.
Qed.  

Lemma validTmSplit {wl : wfLCon} {Γ l A t} {n : nat} {ne : not_in_LCon wl n}
  {VΓt : [||-v Γ ]< (wl ,,l (ne, true)) >}
  {VΓf : [||-v Γ ]< (wl ,,l (ne, false)) >}
  {VΓ : [||-v Γ]< wl >}
  {VAt : [Γ ||-v<l> A | VΓt]< wl ,,l (ne, true) >}
  {VAf : [Γ ||-v<l> A | VΓf]< wl ,,l (ne, false) >} :
  [Γ ||-v<l> t : A | VΓt | VAt]< _ > ->
  [Γ ||-v<l> t : A | VΓf | VAf]< _ > ->
  [Γ ||-v<l> t : A | VΓ | validTySplit VAt VAf]< wl >.
Proof.
  intros [Vtt Vtextt] [Vtf Vtextf].
  unshelve econstructor.
  - intros ?????? ; cbn.
    destruct (decidInLCon wl' n) as [ i | i | notin].
    + now eapply Vtt.
    + now eapply Vtf.
    + eapply TmSplit.
      * now eapply Vtt.
      * now eapply Vtf.
  - intros ; cbn.
    destruct (decidInLCon wl' n) as [ i | i | notin].
    + pose (f' := LCon_le_in_LCon (ne := ne) f i).
      pose (f'':= @LCon_le_step wl wl n true ne (wfLCon_le_id _)).
      unshelve eapply Vtextt.
      * change f with (f' •ε f'') in Vσ'.
        eapply subst_Ltrans' in Vσ'.
        unshelve eapply irrelevanceSubst ; [ | assumption | ]. 
        1: now eapply  WfC_Ltrans.
        exact Vσ'.
      * change f with (f' •ε f'') in Vσσ'.
        unshelve eapply eqsubst_Ltrans' in Vσσ'.
        unshelve eapply irrelevanceSubstEq ; [ | assumption | | ]. 
        1: now eapply  WfC_Ltrans.
        2: exact Vσσ'.
    + pose (f' := LCon_le_in_LCon (ne := ne) f i).
      pose (f'':= @LCon_le_step wl wl n false ne (wfLCon_le_id _)).
      unshelve eapply Vtextf.
      * change f with (f' •ε f'') in Vσ'.
        eapply subst_Ltrans' in Vσ'.
        unshelve eapply irrelevanceSubst ; [ | assumption | ]. 
        1: now eapply  WfC_Ltrans.
        exact Vσ'.
      * change f with (f' •ε f'') in Vσσ'.
        unshelve eapply eqsubst_Ltrans' in Vσσ'.
        unshelve eapply irrelevanceSubstEq ; [ | assumption | | ]. 
        1: now eapply  WfC_Ltrans.
        2: exact Vσσ'.
    + unshelve eapply TmEqSplit.
      * pose (i := @in_here_l wl' n true).
        pose (f' := @LCon_le_up wl wl' n true ne notin f). 
        pose (f'':= @LCon_le_step wl wl n true ne (wfLCon_le_id _)).
        pose (f''':= @LCon_le_step wl' wl' n true notin (wfLCon_le_id _)).
        unshelve eapply Vtextt ; tea.
        -- unshelve epose proof (X:= subst_Ltrans f''' _ Vσ').
           1: now eapply wfc_Ltrans.
           change (f''' •ε f)  with (f' •ε f'') in X.
           eapply subst_Ltrans' in X.
           unshelve eapply irrelevanceSubst.
           ++ exists (VPack_Ltrans f'' VΓ).
              now eapply  WfC_Ltrans.
           ++ now eapply wfc_Ltrans.
           ++ assumption.
        -- unshelve epose proof (X:= eqsubst_Ltrans f''' _ _ Vσσ').
           1: now eapply wfc_Ltrans.
           change (f''' •ε f)  with (f' •ε f'') in X.
           eapply eqsubst_Ltrans' in X.
           unshelve eapply irrelevanceSubstEq.
           1: cbn ; exists (VPack_Ltrans f'' VΓ) ; now eapply  WfC_Ltrans.
           1:  now eapply wfc_Ltrans.
           2: eassumption.
      * pose (i := @in_here_l wl' n false).
        pose (f' := @LCon_le_up wl wl' n false ne notin f). 
        pose (f'':= @LCon_le_step wl wl n false ne (wfLCon_le_id _)).
        pose (f''':= @LCon_le_step wl' wl' n false notin (wfLCon_le_id _)).
        unshelve eapply Vtextf ; tea.
        -- unshelve epose proof (X:= subst_Ltrans f''' _ Vσ').
           1: now eapply wfc_Ltrans.
           change (f''' •ε f)  with (f' •ε f'') in X.
           eapply subst_Ltrans' in X.
           unshelve eapply irrelevanceSubst.
           ++ exists (VPack_Ltrans f'' VΓ).
              now eapply  WfC_Ltrans.
           ++ now eapply wfc_Ltrans.
           ++ assumption.
        -- unshelve epose proof (X:= eqsubst_Ltrans f''' _ _ Vσσ').
           1: now eapply wfc_Ltrans.
           change (f''' •ε f)  with (f' •ε f'') in X.
           eapply eqsubst_Ltrans' in X.
           unshelve eapply irrelevanceSubstEq.
           1: cbn ; exists (VPack_Ltrans f'' VΓ) ; now eapply  WfC_Ltrans.
           1:  now eapply wfc_Ltrans.
           2: eassumption.
Qed.

Lemma validTmSplit' {wl : wfLCon} {Γ l A t} {n : nat} {ne : not_in_LCon wl n}
  {VΓt : [||-v Γ ]< (wl ,,l (ne, true)) >}
  {VΓf : [||-v Γ ]< (wl ,,l (ne, false)) >}
  {VΓ : [||-v Γ]< wl >}
  {VAt : [Γ ||-v<l> A | VΓt]< wl ,,l (ne, true) >}
  {VAf : [Γ ||-v<l> A | VΓf]< wl ,,l (ne, false) >}
  {VA : [Γ ||-v<l> A | VΓ]< wl >}:
  [Γ ||-v<l> t : A | VΓt | VAt]< _ > ->
  [Γ ||-v<l> t : A | VΓf | VAf]< _ > ->
  [Γ ||-v<l> t : A | VΓ | VA]< wl >.
Proof.
  intros.
  unshelve eapply irrelevanceTm ; [eassumption | | ].
  2: now eapply validTmSplit.
Qed.  

Lemma validEqTmSplit {wl : wfLCon} {Γ l t u A} {n : nat} {ne : not_in_LCon wl n}
  {VΓt : [||-v Γ ]< (wl ,,l (ne, true)) >}
  {VΓf : [||-v Γ ]< (wl ,,l (ne, false)) >}
  {VΓ : [||-v Γ]< wl >}
  {VAt : [Γ ||-v<l> A | VΓt]< wl ,,l (ne, true) >}
  {VAf : [Γ ||-v<l> A | VΓf]< wl ,,l (ne, false) >} :
  [Γ ||-v<l> t ≅ u : A | VΓt | VAt]< _ > ->
  [Γ ||-v<l> t ≅ u : A | VΓf | VAf]< _ > ->
  [Γ ||-v<l> t ≅ u : A | VΓ | validTySplit VAt VAf]< wl >.
Proof.
  intros [Vtut] [Vtuf].
  unshelve econstructor.
  - intros ; cbn.
    destruct (decidInLCon wl' n) as [ i | i | notin].
    + now eapply Vtut.
    + now eapply Vtuf.
    + eapply TmEqSplit.
      * now eapply Vtut.
      * now eapply Vtuf.
Qed.
        

Lemma validEqTmSplit' {wl : wfLCon} {Γ l t u A} {n : nat} {ne : not_in_LCon wl n}
  {VΓt : [||-v Γ ]< (wl ,,l (ne, true)) >}
  {VΓf : [||-v Γ ]< (wl ,,l (ne, false)) >}
  {VΓ : [||-v Γ]< wl >}
  {VAt : [Γ ||-v<l> A | VΓt]< wl ,,l (ne, true) >}
  {VAf : [Γ ||-v<l> A | VΓf]< wl ,,l (ne, false) >}
  {VA : [Γ ||-v<l> A | VΓ]< wl >}:
  [Γ ||-v<l> t ≅ u : A | VΓt | VAt]< _ > ->
  [Γ ||-v<l> t ≅ u : A | VΓf | VAf]< _ > ->
  [Γ ||-v<l> t ≅ u : A | VΓ | VA]< wl >.
Proof.
  intros.
  unshelve eapply irrelevanceTmEq ; [eassumption | | ].
  2: now eapply validEqTmSplit.
Qed.  

Lemma WfCSplit {wl : wfLCon} {Γ} {n : nat} {ne : not_in_LCon wl n} :
  [||-v Γ ]< (wl ,,l (ne, true)) > ->
  [||-v Γ ]< (wl ,,l (ne, false)) > ->
  [||-v Γ ]< wl >.
Proof.
  intros VGt VGf.
  epose (Ht := invValidity VGt).
  epose (Hf := invValidity VGf).
  induction Γ as [ | A ? ?] ; cbn in *.
  - now eapply validEmpty'.
  - cbn in *.
    destruct Ht as [lt [VGt' [VAt [Hsubt [Hextt Heqt]]]]].
    destruct Hf as [lf [VGf' [VAf [Hsubf [Hextf Heqf]]]]].
    unshelve eapply validSnoc'.
    1: destruct lt ; [destruct lf ; [exact zero | exact one] | exact one].
    1: now eapply IHΓ.
    all: cbn.
    1:{ destruct lt, lf.
        all: eapply validTySplit ; try eassumption.
        1,2 : eapply embValidTy ; try eassumption.
        all: now constructor.
    }
Qed.

End Split.
