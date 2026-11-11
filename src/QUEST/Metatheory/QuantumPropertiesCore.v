From SQIR Require Import SQIR.
Require Import Coq.Program.Equality.
Require Import Lia Permutation Reals List.
Require Import SST QUEST session.
Require Import substitution.
From Paco Require Import paco.


Lemma free_qubits_incr_free_expression:
forall e b n q,
In q (get_qubits_expression e) <->
In q (get_qubits_expression (incr_free_expression b n e)).
Proof.
  induction e using expression_deep_ind; simpl; intros; cleanup; simpl; try solve [intuition eauto].
  
  split; intros;
  apply in_flat_map in H0; cleanup.
  eapply Forall_forall in H; eauto.
  eapply H in H1.
  eapply in_flat_map; 
  eexists; split.
  apply in_map_iff;
  eexists; split; eauto.
  eauto.

  apply in_map_iff in H0; cleanup.
  eapply Forall_forall in H; eauto.
  eapply H in H1.
  eapply in_flat_map; 
  eexists; split; eauto.
Qed.
  

Lemma free_qubits_incr_free:
forall P a b n m q,
In q (free_qubits P) <->
In q (free_qubits (incr_free a b m n P)).
Proof.
  induction P using process_deep_ind; simpl; intros; cleanup; simpl; try solve [intuition eauto].
  {(*p_var*)
    unfold get_qubits; split; intros Hq.
    - apply in_flat_map in Hq as [e [He Hexpr]].
      apply in_flat_map.
      match goal with
      | |- exists e', In e' (map (incr_free_expression ?cutoff ?shift) lz) /\ _ =>
          exists (incr_free_expression cutoff shift e); split;
          [apply in_map_iff; exists e; split; [reflexivity|exact He]
          |apply (proj1 (free_qubits_incr_free_expression e cutoff shift q)); exact Hexpr]
      end.
    - apply in_flat_map in Hq as [e [He Hexpr]].
      apply in_map_iff in He as [e0 [He Hsource]].
      subst e.
      apply in_flat_map.
      exists e0; split; [exact Hsource|].
      match type of Hexpr with
      | In q (get_qubits_expression (incr_free_expression ?cutoff ?shift e0)) =>
          apply (proj2 (free_qubits_incr_free_expression e0 cutoff shift q)); exact Hexpr
      end.
  }
  {(*p_end*)
    induction lz; simpl in *; 
    intuition eauto.
    apply in_app_iff.
    apply in_app_iff in H1; split_ors; eauto.
    left; eapply free_qubits_incr_free_expression in H1; eauto.

    apply in_app_iff.
    apply in_app_iff in H1; split_ors; eauto.
    left; eapply free_qubits_incr_free_expression in H1; eauto.
  }
  {(*p_send*)
    repeat rewrite app_nil_r.
    intuition eauto.
    apply in_app_iff.
    apply in_app_iff in H; split_ors; eauto.
    left; eapply free_qubits_incr_free_expression in H; eauto.
    right; eapply IHP; eauto.

    apply in_app_iff.
    apply in_app_iff in H; split_ors; eauto.
    left; eapply free_qubits_incr_free_expression in H; eauto.
    right; eapply IHP; eauto.
  }
  {(*p_recv*)
    split; intros.
    {
      apply in_flat_map in H0; cleanup.
      eapply In_to_list_onth in H0; cleanup.
      apply onth_move_out in H0; cleanup.
      eapply SForall_forall in H; eauto.
      eapply H in H1.

      eapply in_flat_map.
      eexists; split; [|eauto].
      eapply onth_to_list_In.
      eapply onth_move_in; eauto.
      eapply onth_move_in; eauto.
    }
    {
      apply in_flat_map in H0; cleanup.
      eapply In_to_list_onth in H0; cleanup.
      apply onth_move_out in H0; cleanup.
      apply onth_move_out in H0; cleanup.
      eapply SForall_forall in H; eauto.
      eapply H in H1.

      eapply in_flat_map.
      eexists; split; [|eauto].
      eapply onth_to_list_In.
      eapply onth_move_in; eauto.
    }
  }
  {(*p_ite*)
    repeat rewrite app_nil_r.
    intuition eauto;
    apply in_app_iff; apply in_app_iff in H; intuition eauto.
     left; eapply free_qubits_incr_free_expression in H0; eauto.
     right.
    apply in_app_iff; apply in_app_iff in H0; intuition eauto.
    left; apply IHP1; eauto.
    right; apply IHP2; eauto.
    left; eapply free_qubits_incr_free_expression in H0; eauto.
     right.
     apply in_app_iff; apply in_app_iff in H0; intuition eauto.
    left; eapply IHP1; eauto.
    right; eapply IHP2; eauto.
  }
  {
    apply IHP.
  }
  {
    apply IHP.
  }
  {(*p_unitary*)
    intuition eauto;
    eapply in_app_iff; apply in_app_iff in H; intuition eauto.

    left.
    induction lz; simpl in *; 
    intuition eauto.
    apply in_app_iff.
    apply in_app_iff in H0; split_ors; eauto.
    left; eapply free_qubits_incr_free_expression in H; eauto.
    right; eapply IHP; eauto.

    left.
    induction lz; simpl in *; 
    intuition eauto.
    apply in_app_iff.
    apply in_app_iff in H0; split_ors; eauto.
    left; eapply free_qubits_incr_free_expression in H; eauto.
    right; eapply IHP; eauto.
  }
  {(*p_measure*)
    repeat rewrite app_nil_r.
    intuition eauto;
    apply in_app_iff; apply in_app_iff in H; intuition eauto.
     left; eapply free_qubits_incr_free_expression in H0; eauto.
    right; apply IHP; eauto.
    left; eapply free_qubits_incr_free_expression in H0; eauto.
    right; eapply IHP; eauto.
  }
Qed.

Lemma free_process_var_in_process_shift:
forall P n m k,
free_process_var_in_process (n + k) P m = free_process_var_in_process n P (m + k).
Proof. 
  induction P using process_deep_ind; simpl; intros.
  - f_equal; lia.
  - reflexivity.
  - apply IHP.
  - induction llp; inversion H; subst; simpl;
      try match goal with
      | IH : SForall _ _ -> _ |- _ => rewrite IH by assumption
      end;
      repeat match goal with
      | IH : forall n m k,
          free_process_var_in_process (n + k) _ m =
          free_process_var_in_process n _ (m + k) |- _ =>
          rewrite IH
      end;
      reflexivity.
  - rewrite IHP1, IHP2; reflexivity.
  - replace (S (n + k)) with (S n + k) by lia.
    apply IHP.
  - apply IHP.
  - apply IHP.
  - apply IHP.
Qed.

Lemma existsb_fold_right:
forall [A : Type] (P : A -> bool) (l : list A),
existsb P l = fold_right (fun x : A => orb (P x)) false l.
Proof.
  induction l; simpl; eauto.
Qed.

Lemma free_qubits_substitutionP:
  forall P P' e x m n,
  In e (free_qubits (substitutionP x m n P' P)) ->
  (In e (free_qubits P) \/ (free_process_var_in_process 0 P x = true /\ In e (free_qubits P'))).
  Proof.
    induction P using process_deep_ind; simpl; intros; cleanup; simpl; try solve [intuition eauto].
    {(*p_var*)
      rewrite Nat.add_0_r.
      destruct (Nat.ltb n x) eqn:Hlt.
      - left; exact H.
      - destruct (Nat.eqb n x) eqn:Heq.
        + right; split.
          * reflexivity.
          * apply (proj2 (free_qubits_incr_free P' 0 0 n0 m e)); exact H.
        + left; exact H.
    }
    {(*p_send*)
      apply in_app_iff in H.
      destruct H as [H|H].
      - left; apply in_app_iff; left; exact H.
      destruct (IHP P' e x m n H) as [Hfree|[Hvar Hq]].
      + left; apply in_app_iff; right; exact Hfree.
      + right; split; [exact Hvar|exact Hq].
    }
  {(*p_recv*)
    apply in_flat_map in H0; cleanup.
    eapply In_to_list_onth in H0; cleanup.
    apply onth_move_out in H0; cleanup.
    apply onth_move_out in H0; cleanup.
    eapply SForall_forall in H; eauto.
    eapply H in H1.
    split_ors; cleanup.
    - left.
      eapply in_flat_map.
      eexists; split; [|eauto].
      eapply onth_to_list_In.
      eapply onth_move_in; eauto.
    - right; split.
      + rewrite <- existsb_fold_right.
        eapply existsb_exists.
        eexists; split; eauto.
        eapply onth_to_list_In.
        eapply onth_move_in in H0; eauto.
        rewrite H0; eauto.
      + eauto.
  }
  {(*p_ite*)
    repeat rewrite in_app_iff in H.
    repeat rewrite in_app_iff.
    destruct H as [H|[H|H]].
    - left; left; exact H.
    - destruct (IHP1 P' e0 x m n H) as [Hfree|[Hvar Hq]].
      + left; right; left; exact Hfree.
      + right; split.
        * apply Bool.orb_true_iff; left; exact Hvar.
        * exact Hq.
    - destruct (IHP2 P' e0 x m n H) as [Hfree|[Hvar Hq]].
      + left; right; right; exact Hfree.
      + right; split.
        * apply Bool.orb_true_iff; right; exact Hvar.
        * exact Hq.
  }
  {(*p_rec*)
    destruct (IHP P' e (S x) (S m) n H) as [Hfree|[Hvar Hq]].
    - left; exact Hfree.
    - right; split.
      + replace (S x) with (x + 1) in Hvar by lia.
        rewrite <- (free_process_var_in_process_shift P 0 x 1) in Hvar.
        exact Hvar.
      + exact Hq.
  }
  {(*p_unitary*)
    apply in_app_iff in H.
    destruct H as [H|H].
    - left; apply in_app_iff; left; exact H.
    - destruct (IHP P' e x m n0 H) as [Hfree|[Hvar Hq]].
      + left; apply in_app_iff; right; exact Hfree.
      + right; split; assumption.
  }
  {(*p_measure*)
    apply in_app_iff in H.
    destruct H as [H|H].
    - left; apply in_app_iff; left; exact H.
    - destruct (IHP P' e x m (S n) H) as [Hfree|[Hvar Hq]].
      + left; apply in_app_iff; right; exact Hfree.
      + right; split; assumption.
  }
Qed.

Lemma free_qubits_substitutionP_rec:
  forall P e x m n,
  In e (free_qubits (substitutionP x m n (p_rec P) P)) -> In e (free_qubits P).
Proof.
  intros P e x m n H.
  pose proof (free_qubits_substitutionP P (p_rec P) e x m n H) as Hsub.
  simpl in Hsub.
  destruct Hsub as [Hsub|[_ Hsub]]; exact Hsub.
Qed.


Lemma bmergelis_nil:
forall ll l n, 
bmergelis ll = nil ->
onth n ll = Some l ->
l = nil.
Proof.
  induction ll; simpl; intros; cleanup;
  destruct n; simpl in *; cleanup; eauto.
  apply bmerge_nil in H; cleanup; eauto.
  destruct o; eauto.
  apply bmerge_nil in H; cleanup; eauto.
Qed.

Lemma get_qubits_In:
forall lz q,
In q (get_qubits lz) <->
exists e, In e lz /\ In q (get_qubits_expression e).
Proof.
  intros; unfold get_qubits.
  apply in_flat_map.
Qed.

Lemma typed_expression_free_qubit:
  forall context e s q,
    typecheck_expression context e s ->
    In q (get_qubits_expression e) -> in_qubit_context context q.
Proof.
  intros context e.
  induction e using expression_deep_ind.
  - intros s q Hty Hin.
    inversion Hty; subst; simpl in Hin; try contradiction.
    destruct Hin as [<-|[]]. assumption.
  - intros s q Hty Hin.
    inversion Hty; subst; simpl in Hin; contradiction.
  - intros s q Hty Hin.
    apply in_flat_map in Hin. destruct Hin as [e' [He' Hq]].
    inversion Hty; subst; simpl in He'; try contradiction.
    all: rewrite Forall_forall in H;
      first [destruct He' as [He'|[He'|[]]];
               [subst e'; eapply H with (x:=a); simpl; eauto
               |subst e'; eapply H with (x:=b); simpl; eauto]
            |destruct He' as [He'|[]];
               subst e'; eapply H with (x:=a); simpl; eauto].
Qed.

Lemma free_qubits_recv_In:
  forall lP q,
    In q (fold_right (@app qubit_reference) nil
      (to_list (smap free_qubits lP))) ->
    exists P0, In P0 (to_list lP) /\ In q (free_qubits P0).
Proof.
  induction lP as [Phead|opt tail IH]; simpl; intros q Hfree.
  - exists Phead; split; simpl; auto.
    rewrite app_nil_r in Hfree. exact Hfree.
  - destruct opt as [P0|]; simpl in Hfree.
    + apply in_app_iff in Hfree as [Hhead|Htail].
      * exists P0; split; simpl; auto.
      * destruct (IH q Htail) as [P1 [Hin Hq]].
        exists P1; split; simpl; auto.
    + destruct (IH q Hfree) as [P1 [Hin Hq]].
      exists P1; split; simpl; auto.
Qed.

Lemma typecheck_process_free_qubits:
forall P context T,
typecheck_process context P T ->
forall q,
In q (free_qubits P) -> in_qubit_context context q.
Proof.
  intros P context T Htyping.
  refine (typecheck_process_deep_ind
    (fun context P T => forall q, In q (free_qubits P) -> in_qubit_context context q)
    _ _ _ _ _ _ _ _ _ _ context P T Htyping).
  - intros ctxNew P0 T0 Htyped IH q Hfree.
    simpl in Hfree. apply IH in Hfree.
    unfold in_qubit_context in *; simpl in *; exact Hfree.
  - intros ctxMeas z P0 T0 Hz Htyped IH q Hfree.
    simpl in Hfree. apply in_app_iff in Hfree as [Hzfree|HPfree].
    + rewrite app_nil_r in Hzfree.
      eapply typed_expression_free_qubit; eauto.
    + destruct z as [v|x|op args]; simpl in *.
      * destruct v; simpl in *; try solve [inversion Hz].
        inversion Hz; subst.
        apply IH in HPfree.
        unfold in_qubit_context, remove_measured_expression_from_context,
          remove_from_qubit_context in HPfree; simpl in HPfree.
        destruct (qr_dec q0 q) as [Heq|Hneq].
        -- subst q0. simpl in HPfree. discriminate.
        -- simpl in HPfree. exact HPfree.
      * apply IH in HPfree.
        unfold in_qubit_context, remove_measured_expression_from_context,
          remove_from_variable_context in *; simpl in *; exact HPfree.
      * inversion Hz.
  - intros ctxU n U lz P0 T0 Hlen Hexprs Hnodup Htyped IH q Hfree.
    simpl in Hfree. apply in_app_iff in Hfree as [Hlz|HP].
    + apply get_qubits_In in Hlz as [e [He Hq]].
      rewrite Forall_forall in Hexprs.
      specialize (Hexprs e He).
      eapply typed_expression_free_qubit; eauto.
    + apply IH; exact HP.
  - intros ctxEnd lz Htyped Hnodup q Hfree.
    apply get_qubits_In in Hfree as [e [He Hq]].
    apply (proj1 (Htyped e)) in He.
    eapply typed_expression_free_qubit; eauto.
  - intros ctxSend part eSend P0 l B T0 Hexpr Htyped IH q Hfree.
    simpl in Hfree. apply in_app_iff in Hfree as [He|HP].
    + rewrite app_nil_r in He.
      eapply typed_expression_free_qubit; eauto.
    + destruct B; simpl in *; try exact (IH q HP).
      destruct eSend as [v|x|op args]; simpl in *.
      * destruct v; try solve [inversion Hexpr].
        unfold in_qubit_context, remove_from_qubit_context in IH; simpl in IH.
        specialize (IH q HP).
        assert (q <> q0) as Hneq.
        { intro Heq. subst q0.
          destruct (qr_dec q q); simpl in IH; congruence. }
        destruct (qr_dec q0 q); simpl in IH; [congruence|exact IH].
      * exact (IH q HP).
      * inversion Hexpr.
  - intros ctxRecv part lP lBT Htyped IH q Hfree.
    apply free_qubits_recv_In in Hfree as [P0 [HP Hq]].
    apply In_to_list_onth in HP as [n Hnth].
    destruct (SForall2_onth_l n lP lBT _ P0 Htyped Hnth)
      as [BT [HBT Hbranch]].
    destruct (SForall2_onth_l n lP lBT _ P0 IH Hnth)
      as [BT' [HBT' IHbranch]].
    rewrite HBT in HBT'. inversion HBT'; subst BT'.
    specialize (IHbranch q Hq).
    unfold in_qubit_context in *; simpl in *; exact IHbranch.
  - intros ctxIf eIf P1 P0 T0 Hbool Htyped1 IH1 Htyped0 IH0 q Hfree.
    simpl in Hfree. apply in_app_iff in Hfree as [He|Hbranches].
    + apply in_app_iff in He as [He|[]].
      eapply typed_expression_free_qubit; eauto.
    + apply in_app_iff in Hbranches as [HP1|HP0].
      * apply IH1; exact HP1.
      * apply IH0; exact HP0.
  - intros ctxRec P0 T0 Htyped IH Honly q Hfree.
    apply IH in Hfree.
    unfold in_qubit_context in *; simpl in *; exact Hfree.
  - intros ctxVar qctx X lz T0 Hproc Honly Hinc Hlist Hnodup q Hfree.
    simpl in Hfree.
    apply get_qubits_In in Hfree as [z [Hz Hq]].
    eapply typed_expression_free_qubit.
    + apply Hlist; exact Hz.
    + exact Hq.
  - intros ctxSub P0 T0 T' Htyped IH Hsub q Hfree.
    apply IH; exact Hfree.
Qed.

Lemma nth_error_NoDup_l_neq:
  forall {A B : Type} (l : list (A * B))
  {ab1 ab2 : A * B} (n m : nat),
  nth_error l n = Some ab1 ->
  nth_error l m = Some ab2 ->
  NoDup (map fst l) ->
  fst ab1 <> fst ab2 -> n <> m.
Proof.
  induction l; simpl; intros; cleanup.
  erewrite nth_error_nil in H; cleanup.
  destruct n, m; simpl in *; try congruence; cleanup; intuition eauto.
Qed.

Definition free_qubits_session (M: session) := 
flat_map free_qubits (map snd M.(elems _ _)).

Definition list_intersection {A} (AEQ: EqDec A) (l1 l2: list A) :=
filter (fun a : A => (inb l2 a)) l1.

Definition list_diff {A} (AEQ: EqDec A) (l1 l2: list A) :=
filter (fun a : A => negb (inb l2 a)) l1.
  
Lemma free_qubits_session_in_one:
forall M e,
In e (free_qubits_session M) <-> (exists p P, In (p, P) M.(elems _ _) /\ In e (free_qubits P)).
Proof.
  unfold free_qubits_session.
  intros M; destruct M; cleanup; simpl.
  generalize dependent m.
  generalize dependent n.
  induction elems; simpl; intros; cleanup.
  intuition eauto.
  cleanup; eapply i; eauto. 

  split; intros.
  {
    destruct a; simpl in *.
    apply in_app_iff in H; split_ors; eauto.

    specialize (IHelems H2 (fun x => if participant_dec x p then None else m x)).
    
    eapply IHelems in H; cleanup.
    do 2 eexists; split; eauto.
    intros; case_analysis; cleanup.
    intuition cleanup.
    exfalso; apply H1.
    apply in_map_iff; eexists; split; eauto.
    simpl; eauto.
    intuition eauto.
    eapply i; eauto.
    eapply i in H3.
    split_ors; cleanup; eauto.
    exfalso; eauto.
  }
  {
    cleanup.
    apply in_app_iff.
    split_ors; cleanup; eauto.
    destruct (participant_dec p a.1); cleanup.

    destruct a; simpl in *.
    exfalso; apply H1.
    apply in_map_iff; eexists; split; eauto.
    simpl; eauto.

    destruct a; simpl in *.
    specialize (IHelems H2 (fun x => if participant_dec x p0 then None else m x)).
    right.
    eapply IHelems; cleanup.
    intros; case_analysis; cleanup.
    intuition cleanup.
    exfalso; apply H1.
    apply in_map_iff; eexists; split; eauto.
    simpl; eauto.
    intuition eauto.
    eapply i; eauto.
    eapply i in H3.
    split_ors; cleanup; eauto.
    exfalso; eauto.

    do 2 eexists; split; eauto.
  }
Qed.

Lemma typecheck_session_unfoldM `{good_merge} :
    forall delta G qc M0 M1,
    unfoldM M0 M1 ->
    typecheck_session qc M0 delta G ->
    typecheck_session qc M1 delta G.
Proof.
    intros delta G qc0 M0 M1 Hunfold Htyped0.
    pose proof (unfoldM_preserves_session_participants M0 M1 Hunfold)
        as Hparticipants.
    unfold unfoldM in Hunfold.
    unfold typecheck_session in *.
    destruct Htyped0 as
        [lqc [Hreg [Hbal [Hassoc [Hpart [Hlen [Hperm Htc]]]]]]].
    exists lqc.
    split; [exact Hreg|].
    split; [exact Hbal|].
    split; [exact Hassoc|].
    split; [exact Hpart|].
    split; [exact Hlen|].
    split.
    - eapply Permutation_trans; eassumption.
    - intros pt T0 qc' Hin.
      destruct (Htc pt T0 qc' Hin) as [Psrc [Hlook HtypedP]].
      destruct (Hunfold pt) as [[Hnone0 Hnone1]
          |[P0 [P1 [Hsome0 [Hsome1 Hpre]]]]].
      + rewrite Hnone0 in Hlook; discriminate.
      + rewrite Hsome0 in Hlook; inversion Hlook; subst Psrc.
        exists P1; split; [exact Hsome1|].
        eapply typecheck_process_precongruence; eauto.
Qed.

Lemma typecheck_session_free_qubits `{good_merge}:
forall M delta G context,
typecheck_session context M delta G ->
forall e,
In e (free_qubits_session M) -> context e = Some tt.
Proof.
  intros M delta G context Htyped e Hin.
  apply free_qubits_session_in_one in Hin.
  destruct Hin as [p [P [Hlookup Hfree]]].
  assert (Hmap : M p = Some P).
  { apply (proj2 (specs _ _ M) p P); exact Hlookup. }
  unfold typecheck_session in Htyped.
  destruct Htyped as [lqc [Hreg [Hbal [Hassoc [Hpart
    [Hlength [Hperm Hcomponent]]]]]]].
  assert (Hp_session : In p (session_participants M)).
  { unfold session_participants. apply in_map with (f := fst) in Hlookup.
    exact Hlookup. }
  assert (Hp_delta : In p (map fst (elems participant ltt delta))).
  { eapply Permutation_in; [apply Permutation_sym; exact Hperm|exact Hp_session]. }
  apply in_map_iff in Hp_delta.
  destruct Hp_delta as [[p' T] [Hp' HinDelta]].
  simpl in Hp'. subst p'.
  destruct (in_combine_ex_r (elems participant ltt delta) lqc
      ltac:(rewrite Hlength; lia) (p, T) HinDelta)
    as [qc Hcombined].
  destruct (Hcomponent p T qc Hcombined) as [P' [HP' HtypedP]].
  rewrite Hmap in HP'; inversion HP'; subst P'.
  pose proof (typecheck_process_free_qubits P (nil, nil, qc) T
      HtypedP e Hfree) as Hlocal.
  unfold in_qubit_context in Hlocal; simpl in Hlocal.
  apply in_combine_r in Hcombined.
  unfold FMap.partition, covers in Hpart.
  destruct Hpart as [Hcovers _].
  apply (proj2 (Hcovers e tt)).
  exists qc; split; assumption.
Qed.


Lemma Permutation_filter:
forall A f (l1 l2: list A),
Permutation l1 l2 ->
Permutation (filter f l1) (filter f l2).
Proof. 
  intros A f l1 l2 Hperm.
  induction Hperm; simpl.
  - reflexivity.
  - destruct (f x); simpl; [now apply perm_skip|exact IHHperm].
  - destruct (f x), (f y); simpl; try reflexivity; apply perm_swap.
  - etransitivity; eauto.
Qed.

Lemma free_qubits_insert_in:
    forall M p P,
    Permutation (free_qubits_session (insert M p P)) (free_qubits P ++ free_qubits_session (delete M p)).
Proof.
  intros M p P.
  unfold free_qubits_session.
  simpl.
  assert (Heq: equivalent (insert M p P) (insert (delete M p) p P)). {
    unfold equivalent, included; simpl; split; intros k v H;
      repeat case_analysis; cleanup; eauto.
  }
  pose proof (equivalent_Permutation _ _ _ _ Heq) as Hperm.
  assert (Hflat:
      Permutation
        (flat_map free_qubits (map snd (elems _ _ (insert M p P))))
        (flat_map free_qubits (map snd (elems _ _ (insert (delete M p) p P))))).
  {
    apply Permutation_flat_map.
    apply Permutation_map; exact Hperm.
  }
  etransitivity; [exact Hflat|].
  assert (Hnot: ~ In p (map fst (remove_fst (elems _ _ M) p))). {
    eapply remove_not_In_2.
    exact (proj1 (specs _ _ M)).
  }
  assert (Hreplace:
      replace_or_add (remove_fst (elems _ _ M) p) (p, P) =
      app (remove_fst (elems _ _ M) p) ((p, P)::nil)).
  {
    induction (remove_fst (elems _ _ M) p) as [|[q Q] tl IH]; simpl.
    - reflexivity.
    - destruct (participant_dec q p) as [Hqp|Hneq].
      + subst q. exfalso. apply Hnot. simpl. auto.
      + simpl. f_equal. apply IH. intro Hin. apply Hnot. simpl. auto.
  }
  change (Permutation
    (flat_map free_qubits
      (map snd (replace_or_add (remove_fst (elems _ _ M) p) (p, P))))
    (free_qubits P ++
      flat_map free_qubits (map snd (remove_fst (elems _ _ M) p)))).
  rewrite Hreplace, map_app, flat_map_app. simpl. rewrite app_nil_r.
  apply Permutation_app_comm.
Qed.

Lemma inb_false:
forall A AEQ l (a:A),
@inb A AEQ l a = false ->
~In a l.
Proof.
  unfold not; intros.
  eapply inb_spec in H0; eauto.
Qed. 

(* A typed session is qubit-use linear when every qubit in its global qubit context is still mentioned by the session.  The session typing judgment already ensures the converse: every mentioned qubit belongs to the context. *)
Definition qubit_use_linear (context: qubit_context) (M: session) : Prop :=
  forall q, context q = Some tt -> In q (free_qubits_session M).

Lemma typecheck_process_qubit_use_linear:
forall P context T,
typecheck_process context P T ->
forall q, in_qubit_context context q -> In q (free_qubits P).
Proof.
  intros P context T Htyping.
  refine (typecheck_process_deep_ind
    (fun context P T => forall q, in_qubit_context context q -> In q (free_qubits P))
    _ _ _ _ _ _ _ _ _ _ context P T Htyping).
  - intros ctx P0 T0 Htyped IH q Hq.
    simpl. apply IH. exact Hq.
  - intros ctx z P0 T0 Hz Htyped IH q Hq.
    simpl. apply in_app_iff.
    destruct z as [v|x|op args].
    + destruct v; try inversion Hz.
      unfold in_qubit_context in *; simpl in *.
      unfold remove_measured_expression_from_context, remove_from_qubit_context in IH.
      simpl in IH.
      destruct (qr_dec q0 q) as [Heq|Hneq].
      * subst q. left. simpl. auto.
      * right. apply IH. simpl. destruct (qr_dec q0 q); [congruence|exact Hq].
    + right. apply IH. exact Hq.
    + inversion Hz.
  - intros ctx n U lz P0 T0 Hlen Hexprs Hnodup Htyped IH q Hq.
    simpl. apply in_app_iff. right. apply IH. exact Hq.
  - intros ctx lz Htyped Hnodup q Hq.
    simpl.
    apply get_qubits_In.
    exists (Val (QVal q)).
    split.
    + apply (proj2 (Htyped (Val (QVal q)))).
      constructor. exact Hq.
    + simpl. auto.
  - intros ctx p e P0 l B T0 Hexpr Htyped IH q Hq.
    simpl. apply in_app_iff.
    destruct B; simpl in *; try (right; apply IH; exact Hq).
    destruct e as [v|x|op args]; simpl in *.
    + destruct v; try inversion Hexpr.
      unfold in_qubit_context in *; simpl in *.
      unfold remove_from_qubit_context in IH. simpl in IH.
      destruct (qr_dec q0 q) as [Heq|Hneq].
      * subst q. left. simpl. auto.
      * right. apply IH. simpl. destruct (qr_dec q0 q); [congruence|exact Hq].
    + right. apply IH. exact Hq.
    + inversion Hexpr.
  - intros ctx p lP lBT Htyped IH q Hq.
    assert (Hrecv : forall lP0 lBT0,
      SForall2 (fun P BT => typecheck_process (insert_into_variable_context ctx BT.1) P BT.2) lP0 lBT0 ->
      SForall2 (fun P BT => forall q, in_qubit_context (insert_into_variable_context ctx BT.1) q -> In q (free_qubits P)) lP0 lBT0 ->
      forall q, in_qubit_context ctx q ->
        In q (fold_right (@app qubit_reference) nil (to_list (smap free_qubits lP0)))).
    { intros lP0. induction lP0 as [Phead|slot tail IHrecv]; intros lBT0 Htyped0 IH0 q0 Hq0.
      - inversion Htyped0; subst. inversion IH0; subst. simpl in *. eauto.
      - destruct slot as [Phead|].
        + inversion Htyped0; subst. inversion IH0; subst. simpl.
          apply in_app_iff. left. eauto.
        + inversion Htyped0; subst. inversion IH0; subst. simpl.
          eapply IHrecv; eauto. }
    simpl. eapply Hrecv; eauto.
  - intros ctx e P1 P0 T0 Hbool Htyped1 IH1 Htyped0 IH0 q Hq.
    simpl. apply in_app_iff. right. apply in_app_iff. left. apply IH1. exact Hq.
  - intros ctx P0 T0 Htyped IH Honly q Hq.
    simpl. apply IH. exact Hq.
  - intros ctx qctx X T0 lz Hproc Honly Hequiv Hlist Hnodup q Hq.
    simpl. apply get_qubits_In. exists (Val (QVal q)). split.
    + apply (proj2 (Hlist (Val (QVal q)))).
      constructor. exact Hq.
    + simpl. auto.
  - intros ctx P0 T0 T' Htyped IH Hsub q Hq.
    apply IH. exact Hq.
Qed.

Lemma typecheck_session_qubit_use_linear `{good_merge}:
forall M delta G context,
typecheck_session context M delta G ->
qubit_use_linear context M.
Proof.
  intros M delta G context Htyped q Hq.
  unfold typecheck_session in Htyped.
  destruct Htyped as [lqc [Hreg [Hbalanced [Hassoc [Hpartition
    [Hlength [Hperm Hcomponent]]]]]]].
  unfold FMap.partition, FMap.covers in Hpartition.
  destruct Hpartition as [Hcovers Hdisjoint].
  destruct (proj1 (Hcovers q tt) Hq) as [qc [Hqc Hqcq]].
  destruct (in_combine_ex_l (elems participant ltt delta) lqc ltac:(lia) qc Hqc)
    as [[p T] Htriple].
  destruct (Hcomponent p T qc Htriple) as [P [HP Hproc]].
  assert (HfreeP : In q (free_qubits P)).
  { eapply typecheck_process_qubit_use_linear; [exact Hproc|].
    unfold in_qubit_context. simpl. exact Hqcq. }
  apply (proj2 (free_qubits_session_in_one M q)).
  exists p, P. split.
  - unfold session_participants in Hperm.
    apply (proj2 (specs _ _ M) p P). exact HP.
  - exact HfreeP.
Qed.

Lemma typecheck_session_qubit_use_exact `{good_merge}:
forall M delta G context,
typecheck_session context M delta G ->
forall q, In q (free_qubits_session M) <-> context q = Some tt.
Proof.
  intros M delta G context Htyped q.
  split.
  - intro Hin.
    pose proof (typecheck_session_free_qubits M delta G
      context Htyped q Hin) as Hctx.
    exact Hctx.
  - apply (typecheck_session_qubit_use_linear M delta G context Htyped q).
Qed.

Lemma qubit_state_key_in_free_qubits `{good_merge}:
forall qstate context M delta G,
typecheck_session context M delta G ->
state_only_contains_qubits_in_context context qstate ->
forall q,
In q (map fst (proj1_sig (projT1 qstate)).(elems _ _)) ->
In q (free_qubits_session M).
Proof.
  intros qstate context M delta G Htyped Hstate q Hkey.
  apply (proj2 (typecheck_session_qubit_use_exact M delta G context
    Htyped q)).
  apply (proj2 (Hstate q)).
  apply in_map_iff in Hkey.
  destruct Hkey as [[q' owner] [Heq Hin]].
  simpl in Heq; subst q'.
  apply specs in Hin.
  congruence.
Qed.

Lemma list_diff_nil_of_included:
forall l1 l2,
(forall q, In q l1 -> In q l2) ->
list_diff qr_dec l1 l2 = nil.
Proof.
  intros l1 l2 Hincluded.
  unfold list_diff.
  induction l1 as [|q l1 IH]; simpl; [reflexivity|].
  assert (Hinb: @inb qubit_reference qr_dec l2 q = true).
  { apply inb_spec. apply Hincluded. simpl; auto. }
  rewrite Hinb; simpl.
  apply IH.
  intros q' Hin.
  apply Hincluded. simpl; auto.
Qed.


