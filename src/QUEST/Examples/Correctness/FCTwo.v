(* Merged from FCTwoPrelude.v. *)
Require Import Lia Permutation String Coq.Program.Equality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import SST.
Require Import QUEST.
Require Import QuantumGateTeleportation.
Require Import ExamplesHelpers FunctionalCorrectnessHelpers.
From SQIR Require Import SQIR.
Require Import SQIR.UnitaryOps.
Require Import SQIR.Equivalences.

Open Scope R_scope.
Open Scope C_scope.

Definition cz: Matrix (Nat.pow 2 2) (Nat.pow 2 2) :=
fun n m =>
match n, m with
| 0, 0 => 1
| 1, 1 => 1
| 2, 2 => 1
| 3, 3 => -1
| _, _ => 0
end.

Close Scope R_scope.
Close Scope C_scope.

Fixpoint has_Tau (P1: process) :=
match P1 with
| p_send _ _ _ _  => False
| p_recv _ _ => False
| p_var _ _  => False
| p_end _ => False
| p_rec P => has_Tau P
| _ => True
end.

Fixpoint no_newq (P1: process) :=
match P1 with
| p_send _ _ _ P' => no_newq P'
| p_recv _ lP => fold_right and True (to_list (smap no_newq lP))
| p_unitary _ _ _ P' => no_newq P'
| p_measure _ P' => no_newq P'
| p_ite _ P0 P1 => (no_newq P0) /\ (no_newq P1)
| p_newq _ => False
| p_rec P' => no_newq P'
| _ => True
end.

Definition no_newq_session (s: session) :=
forall p P1, s p = Some P1 ->  no_newq P1.

(* Two communications that transfer the same wire do not commute: the later
   receiver owns it after both steps. *)
Definition should_swap_payloads_disjoint (v v' : value) : bool :=
  match v, v' with
  | QVal q, QVal q' => if qr_dec q q' then false else true
  | _, _ => true
  end.

Definition should_swap x y :=
    match x, y with
    | Tau (Pt p), Tau (Pt q) => false
    | Tau (Pt r), Transmit (Pt p) (Pt q) _ _ =>
    false
    | Transmit (Pt p) (Pt q) _ _, Tau (Pt r) => andb (negb (String.eqb r p)) (negb (String.eqb r q))
    | Transmit (Pt p) (Pt q) _ v, Transmit (Pt r) (Pt s) _ v' =>
      andb (should_swap_payloads_disjoint v v')
        (andb
          (andb
            (andb (negb (String.eqb p r)) (negb (String.eqb p s)))
            (andb (negb (String.eqb q r)) (negb (String.eqb q s))))
          (orb (String.ltb r p) (andb (String.eqb r p) (String.ltb s q))))
    end.

Definition should_swap_no_newq x y :=
    match x, y with
    | Tau (Pt p), Tau (Pt q) => (String.ltb q p)
    | Tau (Pt r), Transmit (Pt p) (Pt q) _ _ =>
    false
    | Transmit (Pt p) (Pt q) _ _, Tau (Pt r) => andb (negb (String.eqb r p)) (negb (String.eqb r q))
    | Transmit (Pt p) (Pt q) _ _, Transmit (Pt r) (Pt s) _ _ =>
      andb
      (andb
        (andb (negb (String.eqb p r)) (negb (String.eqb p s)))
        (andb (negb (String.eqb q r)) (negb (String.eqb q s))))
      (orb (String.ltb r p) (andb (String.eqb r p) (String.ltb s q) ))
    end.

Fixpoint insert_into (f: action -> action -> bool) a la :=
match la with
| nil => a::nil
| a'::la' =>
  if f a a' then
    a'::(insert_into f a la')
  else
    a::la
end.

Fixpoint partial_sort (f: action -> action -> bool) la :=
match la with
| nil => nil
| a'::la' => insert_into f a' (partial_sort f la')
end.

Fixpoint pairwise_sorted (f: action -> action -> bool) la:=
match la with
| nil => True
| a :: nil => True
| a1::la1 =>
  match la1 with
  | nil => True
  | a2::_ => (f a1 a2 = false) /\ pairwise_sorted f la1
  end
end.

Lemma ltb_antisym:
forall s s',
String.ltb s s' = true ->
String.ltb s' s = false.
Proof.
  unfold String.ltb; intros.
  rewrite compare_antisym.
  destruct (s ?= s')%string; simpl; eauto.
Qed.

Lemma should_swap_true_swap:
forall a a0,
should_swap a a0 = true ->
should_swap a0 a = false.
Proof.
  intros a a0 Hswap.
  destruct a as [pt|p q l v], a0 as [pt0|r s l0 v0].
  - destruct pt as [name], pt0 as [name0].
    simpl in Hswap; discriminate.
  - destruct pt as [name], r as [name1], s as [name2].
    simpl in Hswap; discriminate.
  - destruct p as [name], q as [name0], pt0 as [name1].
    simpl; reflexivity.
  - destruct p as [name], q as [name0], r as [name1], s as [name2].
    simpl in Hswap |- *.
    destruct (String.eqb name name1) eqn:Heq.
    + apply andb_true_iff in Hswap as [_ Hendpoints_order].
      cbn [negb andb] in Hendpoints_order; discriminate.
    + assert (Heq_reverse : String.eqb name1 name = false).
      { rewrite String.eqb_sym; exact Heq. }
      cbn [negb andb] in Hswap.
      repeat (apply andb_true_iff in Hswap as [_ Hswap]).
      apply orb_true_iff in Hswap as [Hlt | Htie].
      * pose proof (ltb_antisym name1 name Hlt) as Hreverse.
        rewrite Heq_reverse, Hreverse; cbn [orb].
        repeat rewrite andb_false_r; reflexivity.
      * rewrite Heq_reverse in Htie; cbn [andb orb] in Htie; discriminate.
Qed.

Lemma should_swap_no_newq_true_swap:
forall a a0,
should_swap_no_newq a a0 = true ->
should_swap_no_newq a0 a = false.
Proof.
  intros; destruct a, a0;
  simpl in *; repeat case_analysis;
  cleanup; try congruence.
  rewrite ltb_antisym; cleanup; simpl; eauto.
  clean_bool; cleanup; simpl; eauto.
  repeat (rewrite eqb_sym; cleanup; simpl).
  eauto.
  eapply ltb_antisym in H0; cleanup; eauto.
Qed.

Lemma insert_into_pairwise_sorted:
forall f la a,
(forall a a0, f a a0 = true -> f a0 a = false) ->
pairwise_sorted f la -> pairwise_sorted f (insert_into f a la).
Proof.
  induction la; simpl; intros; eauto.
  repeat case_analysis; simpl; cleanup; eauto.
  eapply H in HD0; eauto.

  cleanup; repeat case_analysis; cleanup.
  split; eauto.
  apply (IHla a0) in H1; clear IHla; eauto.
  simpl in *; cleanup; eauto.

  apply (IHla a2) in H1; clear IHla; eauto.
  simpl in H1; cleanup; eauto.
Qed.

Lemma partial_sort_pairwise_sorted:
forall f la,
(forall a a0, f a a0 = true -> f a0 a = false) ->
pairwise_sorted f (partial_sort f la).
Proof.
  induction la; simpl; intros; eauto.
  apply insert_into_pairwise_sorted; eauto.
Qed.

Lemma pairwise_sorted_take_two :
forall f a a' la,
pairwise_sorted f (a::a'::la) ->
f a a' = false /\ pairwise_sorted f (a'::la).
Proof. simpl; eauto. Qed.

Opaque pairwise_sorted.

Lemma ltb_neq:
forall s s', String.ltb s s' = true -> s <> s'.
Proof.
  intros s s' Hlt Heq.
  pose proof (ltb_antisym s s' Hlt) as Hlt_reverse.
  congruence.
Qed.

Definition equivalent_states (s' s'': state):=
unfoldM (snd s'') (snd s') /\
equivalent (proj1_sig (projT1 (fst s''))) (proj1_sig (projT1 (fst s'))) /\
(proj1_sig (projT2 (fst s''))) = (proj1_sig (projT2 (fst s'))).

Lemma equivalent_states_unfold_sessions:
forall s1 s2,
equivalent_states s1 s2 ->
unfoldM (snd s2) (snd s1).
Proof.
  intros s1 s2 Hstates.
  unfold equivalent_states in Hstates.
  exact (proj1 Hstates).
Qed.

Lemma equivalent_states_trans:
forall s1 s2 s3,
equivalent_states s1 s2 ->
equivalent_states s2 s3 ->
equivalent_states s1 s3.
Proof.
  intros s1 s2 s3 H12 H23.
  unfold equivalent_states in *.
  destruct H12 as [Hs12 [Hq12 Hv12]].
  destruct H23 as [Hs23 [Hq23 Hv23]].
  simpl in *.
  split.
  - eapply unfoldM_trans; [exact Hs23|exact Hs12].
  - split.
    + eapply equivalent_trans; eauto.
    + congruence.
Qed.

Lemma step_equivalent_states:
forall s1 s1' s2 a pi,
step s1 a s2 pi ->
equivalent_states s1 s1' ->
exists s2',
step s1' a s2' pi /\
equivalent_states s2 s2'.
Proof.
  fix IH 6.
  intros; destruct a.
  {
    inversion H; clear H; cleanup.
    {
      simpl in *.
      eapply_fresh equivalent_states_unfold_sessions in H0; eauto; cleanup.
      simpl in *.
      destruct s1' as [q0 M0]; simpl in *.
      eexists; split.
      - eapply Congr with (M1' := s0); [exact Hx|].
        econstructor; eauto.
      - unfold equivalent_states in *; cleanup; simpl in *.
        split.
        + apply unfoldM_refl.
        + split; cleanup; eauto.

      assume_fresh (length (elems _ _ (` (projT1 q0))) = length (elems _ _ (` (projT1 q_state1)))).
      rewrite HA;
      eapply ExamplesHelpers.insert_equiv_lemma; eauto.
    }
    {
      simpl in *.
      eapply_fresh equivalent_states_unfold_sessions in H0; eauto; cleanup.
      simpl in *.
      destruct s1' as [q0 M0]; simpl in *.
      eexists; split.
      - eapply Congr with (M1' := s0); [exact Hx|].
        solve [econstructor; eauto].
      - unfold equivalent_states in *; cleanup; simpl in *.
      split.
      + apply unfoldM_refl.
      + split; cleanup; eauto.
    }
    {
      simpl in *.
      eapply_fresh equivalent_states_unfold_sessions in H0; eauto; cleanup.
      simpl in *.
      destruct s1' as [q0 M0]; simpl in *.
      eexists; split.
      - eapply Congr with (M1' := s0); [exact Hx|].
        solve [econstructor; eauto].
      - unfold equivalent_states in *; cleanup; simpl in *.
      split.
      + apply unfoldM_refl.
      + split; cleanup; eauto.
    }
    {
      simpl in *.
      simpl in *.
      destruct s1'; simpl in *.
      unfold equivalent_states in H0; simpl in H0.
      destruct H0 as [Hsession [Hmapstate Hvectorstate]].
      assert_fresh ((` (projT1 q0)) q = Some (p, n)). {
        change (equivalent (` (projT1 q0)) (` (projT1 q_state1))) in Hmapstate.
        exact (proj2 Hmapstate q (p, n) Hlookup).
      }
      set (qm0 := ` (projT1 q0)).
      set (qm1 := ` (projT1 q_state1)).
      set (sv0 := ` (projT2 q0)).
      set (sv1 := ` (projT2 q_state1)).
      change (equivalent qm0 qm1) in Hmapstate.
      change (sv0 = sv1) in Hvectorstate.
      pose proof (FMap.equivalent_Permutation _ _ _ _ Hmapstate) as Hperm.
      assert (Hmaplen : Datatypes.length (elems _ _ qm0) =
        Datatypes.length (elems _ _ qm1)).
      { apply Permutation_length; exact Hperm. }
      assert (Hlen0 : 0 < Datatypes.length (elems _ _ qm0)).
      { rewrite Hmaplen; exact Hlen. }
      assert (Hnonzero0 : norm
        (proj n (Datatypes.length (elems _ _ qm0)) r × sv0) <> 0%R).
      { rewrite Hmaplen, Hvectorstate; exact Hnonzero. }
      set (m0 := measure_qubit_from_nonzero qm0 (proj2_sig (projT1 q0))
        sv0 (proj2_sig (projT2 q0)) q p n r HA Hlen0 Hnonzero0).
      set (m1 := measure_qubit_from_nonzero qm1
        (proj2_sig (projT1 q_state1)) sv1
        (proj2_sig (projT2 q_state1)) q p n r Hlookup Hlen Hnonzero).
      change ((pi0, q_state2) = m1) in H4.
      assert (Hprob : proj1_sig (fst m0) = proj1_sig pi0).
      {
        pose proof (f_equal (fun z => proj1_sig (fst z)) H4) as Hprob1.
        simpl in Hprob1.
        rewrite Hprob1.
        unfold m0, m1, measure_qubit_from_nonzero, measure_qubit_nonzero.
        simpl.
        rewrite Hmaplen, Hvectorstate.
        reflexivity.
      }
      assert (Hmapfun : forall q', qm0 q' = qm1 q').
      {
        intros q'.
        destruct Hmapstate as [H01 H10].
        destruct (qm0 q') as [v0|] eqn:E0;
        destruct (qm1 q') as [v1|] eqn:E1.
        - pose proof (H01 q' v0 E0) as Heq.
          rewrite E1 in Heq; inversion Heq; reflexivity.
        - pose proof (H01 q' v0 E0) as Heq.
          rewrite E1 in Heq; discriminate.
        - pose proof (H10 q' v1 E1) as Heq.
          rewrite E0 in Heq; discriminate.
        - reflexivity.
      }
      assert (Hmapout : equivalent
        (proj1_sig (projT1 (snd m0)))
        (proj1_sig (projT1 (snd m1)))).
      {
        unfold m0, m1, measure_qubit_from_nonzero,
          measure_qubit_nonzero; simpl.
        assert (Hmapout_fun : forall q',
          (Primitives.remove_and_reindex_qubit_map qm0 q n) q' =
          (Primitives.remove_and_reindex_qubit_map qm1 q n) q').
        {
          intros q'.
          unfold Primitives.remove_and_reindex_qubit_map,
            Primitives.reindex_quantum_map, FMap.delete; simpl.
          destruct (qr_dec q q'); [reflexivity|].
          rewrite Hmapfun; reflexivity.
        }
        unfold equivalent, included; split; intros q' v Hlookup'.
        - rewrite <- Hmapout_fun; exact Hlookup'.
        - rewrite Hmapout_fun; exact Hlookup'.
      }
      assert (Hvectorout :
        proj1_sig (projT2 (snd m0)) = proj1_sig (projT2 (snd m1))).
      {
        set (rem0 := Nat.pred (Datatypes.length (elems _ _ qm0))).
        set (rem1 := Nat.pred (Datatypes.length (elems _ _ qm1))).
        set (dim0 := eq_sym (Nat.succ_pred_pos
          (Datatypes.length (elems _ _ qm0)) Hlen0)).
        set (dim1 := eq_sym (Nat.succ_pred_pos
          (Datatypes.length (elems _ _ qm1)) Hlen)).
        set (sv0' := transport_state_vector dim0 sv0).
        set (sv1' := transport_state_vector dim1 sv1).
        set (formula0 := normalize_removed_wire
          (@Mmult (2 ^ rem0) (2 ^ (S rem0)) 1
            (remove_measured_wire_operator rem0 n r)
            (proj n (S rem0) r × sv0'))).
        set (formula1 := normalize_removed_wire
          (@Mmult (2 ^ rem1) (2 ^ (S rem1)) 1
            (remove_measured_wire_operator rem1 n r)
            (proj n (S rem1) r × sv1'))).
        assert (Hformula0 : proj1_sig (projT2 (snd m0)) = formula0).
        {
          unfold m0, formula0, measure_qubit_from_nonzero,
            measure_qubit_nonzero.
          cbn -[transport_state_vector normalize_removed_wire
            remove_measured_wire proj Mmult remove_and_reindex_qubit_map
            measure_qubit_nonzero_at_dimension].
          apply FunctionalCorrectnessHelpers.measure_at_dimension_vector.
        }
        assert (Hformula1 : proj1_sig (projT2 (snd m1)) = formula1).
        {
          unfold m1, formula1, measure_qubit_from_nonzero,
            measure_qubit_nonzero.
          cbn -[transport_state_vector normalize_removed_wire
            remove_measured_wire proj Mmult remove_and_reindex_qubit_map
            measure_qubit_nonzero_at_dimension].
          apply FunctionalCorrectnessHelpers.measure_at_dimension_vector.
        }
        assert (Hsv' : sv0' = sv1').
        {
          unfold sv0', sv1'.
          rewrite (FunctionalCorrectnessHelpers.transport_state_vector_value
            _ _ dim0 sv0).
          rewrite (FunctionalCorrectnessHelpers.transport_state_vector_value
            _ _ dim1 sv1).
          exact Hvectorstate.
        }
        rewrite Hformula0, Hformula1.
        unfold formula0, formula1, rem0, rem1.
        rewrite Hmaplen, Hsv'.
        reflexivity.
      }
      pose proof (f_equal (@snd _ _) H4) as Hqstate2.
      simpl in Hqstate2.
      exists (snd m0, insert s0 p
        (subst_expression_in_process 0 0 (Val (Bool r)) P)); split.
      - rewrite <- Hprob.
        eapply Congr with (M1' := s0); [exact Hsession|].
        eapply Meas with (q_state1 := q0) (q_state2 := snd m0)
          (pi := fst m0) (Hlookup := HA) (Hlen := Hlen0)
          (Hnonzero := Hnonzero0); eauto.
      - unfold equivalent_states; simpl.
        split; [apply unfoldM_refl|].
        + split.
          * rewrite Hqstate2; exact Hmapout.
          * rewrite Hqstate2; exact Hvectorout.
    }
    {
      simpl in *.
      eapply_fresh equivalent_states_unfold_sessions in H0; eauto; cleanup.
      simpl in *.
      destruct s1'; simpl in *.
      destruct H0 as [Hsession [Hmaps Hvector]].
      set (qm0 := ` (projT1 q)).
      set (qm1 := ` (projT1 q_state1)).
      set (sv0 := ` (projT2 q)).
      set (sv1 := ` (projT2 q_state1)).
      change (equivalent qm0 qm1) in Hmaps.
      change (sv0 = sv1) in Hvector.
      assert (Hmapfun : forall q', qm0 q' = qm1 q').
      {
        intros q'.
        destruct Hmaps as [H01 H10].
        destruct (qm0 q') as [v0|] eqn:E0;
        destruct (qm1 q') as [v1|] eqn:E1.
        - pose proof (H01 q' v0 E0) as Heq.
          rewrite E1 in Heq; inversion Heq; reflexivity.
        - pose proof (H01 q' v0 E0) as Heq.
          rewrite E1 in Heq; discriminate.
        - pose proof (H10 q' v1 E1) as Heq.
          rewrite E0 in Heq; discriminate.
        - reflexivity.
      }
      pose proof (FMap.equivalent_Permutation _ _ _ _ Hmaps) as Hperm.
      assert (Hmaplen : Datatypes.length (elems _ _ qm0) =
        Datatypes.length (elems _ _ qm1)).
      { apply Permutation_length; exact Hperm. }
      assert (Hpositive1 : 0 < Datatypes.length (elems _ _ qm1)).
      {
        unfold qm1.
        pose proof H3 as Happly.
        unfold apply_unitary in Happly.
        destruct (lt_dec 0 (Datatypes.length
          (elems _ _ (` (projT1 q_state1))))) as [Hpos|Hpos];
          [exact Hpos|discriminate].
      }
      assert (Hbound1 : Datatypes.length lq <=
        Datatypes.length (elems _ _ qm1)).
      {
        unfold qm1.
        pose proof H3 as Happly.
        unfold apply_unitary in Happly.
        destruct (lt_dec 0 (Datatypes.length
          (elems _ _ (` (projT1 q_state1))))) as [Hpos|Hpos];
          [|discriminate].
        destruct (le_dec (Datatypes.length lq)
          (Datatypes.length (elems _ _ (` (projT1 q_state1)))))
          as [Hbound|Hbound];
          [exact Hbound|discriminate].
      }
      assert (Hpositive0 : 0 < Datatypes.length (elems _ _ qm0)).
      { rewrite Hmaplen; exact Hpositive1. }
      assert (Hbound0 : Datatypes.length lq <=
        Datatypes.length (elems _ _ qm0)).
      { rewrite Hmaplen; exact Hbound1. }
      assert (Hgetall : forall qs,
        get_all_values qm0 qs = get_all_values qm1 qs).
      {
        intros qs; induction qs as [|q' qs IHtail]; simpl; [reflexivity|].
        rewrite Hmapfun, IHtail; reflexivity.
      }
      assert (Hresult_vector : forall
        (qm : finite_map qubit_reference (participant * nat))
        (Hqm : quantum_map_wf qm)
        (sv : state_vector (Datatypes.length (elems _ _ qm)))
        (Hsv : state_vector_wf sv) qs',
        apply_unitary qm Hqm sv Hsv U lq eq_refl Hdim = Some qs' ->
        exists lpn,
          get_all_values qm lq = Some lpn /\
          exists (Hindices :
            Datatypes.length (map snd lpn) = Datatypes.length lq /\
            NoDup (map snd lpn) /\
            Forall (fun i => i < Datatypes.length (elems _ _ qm))
              (map snd lpn)),
            proj1_sig (projT2 qs') =
              @Mmult (2 ^ Datatypes.length (elems _ _ qm))
                (2 ^ Datatypes.length (elems _ _ qm)) 1
                (uc_eval (proj1_sig (base_to_ucom U (map snd lpn) Hindices)))
                sv).
      {
        intros qm Hqm sv Hsv qs' Happly.
        unfold apply_unitary in Happly.
        destruct (lt_dec 0 (Datatypes.length (elems _ _ qm)))
          as [Hstate|Hstate]; [|discriminate].
        destruct (le_dec (Datatypes.length lq)
          (Datatypes.length (elems _ _ qm))) as [Hdimle|Hdimle];
          [|discriminate].
        destruct (NoDup_dec (TEQ := qr_dec) lq) as [Hnd|Hnd];
          [|discriminate].
        destruct (get_all_values_certified qm lq) as [cert|] eqn:Hcert;
          [|discriminate].
        cbn in Happly; inversion Happly; subst qs'.
        set (lpn := proj1_sig cert).
        set (Hindexes := apply_unitary_indexes_wf qm Hqm lq
          (Datatypes.length lq) Hdim eq_refl lpn Hnd (proj2_sig cert)).
        set (HindexTriple := conj (proj1 Hindexes)
          (conj (proj1 (proj2 Hindexes))
            (proj1 (proj2 (proj2 Hindexes))))).
        exists lpn; split; [unfold lpn; exact (proj2_sig cert)|].
        exists HindexTriple.
        unfold apply_unitary_to_state; simpl.
        set (Hbase := Primitives.apply_unitary_to_state_obligation_2
          (Datatypes.length (elems _ _ qm)) (Datatypes.length lq) Hdimle U
          (map snd lpn) Hindexes).
        assert (HbaseEq : Hbase = HindexTriple).
        { unfold Hbase; apply proof_irrelevance. }
        rewrite HbaseEq; reflexivity.
      }
      pose proof (Hresult_vector qm1 (proj2_sig (projT1 q_state1)) sv1
        (proj2_sig (projT2 q_state1)) q_state2 H3) as Hsource_result.
      destruct Hsource_result as [lpn1 [Hget1 [Hidx1 Hvec1]]].
      assert (Hcert0_exists : exists cert,
        get_all_values_certified qm0 lq = Some cert).
      {
        unfold get_all_values_certified.
        rewrite Hgetall, Hget1.
        eexists; reflexivity.
      }
      destruct Hcert0_exists as [cert0 Hcert0].
      assert (Htarget_exists : exists q_state2',
        apply_unitary qm0 (proj2_sig (projT1 q)) sv0
          (proj2_sig (projT2 q)) U lq eq_refl Hdim = Some q_state2').
      {
        unfold apply_unitary.
        destruct (lt_dec 0 (Datatypes.length (elems _ _ qm0)))
          as [Hstate|Hstate]; [|lia].
        destruct (le_dec (Datatypes.length lq)
          (Datatypes.length (elems _ _ qm0))) as [Hdimle|Hdimle]; [|lia].
        destruct (NoDup_dec (TEQ := qr_dec) lq) as [Hnd|Hnd];
          [|contradiction].
        rewrite Hcert0.
        eexists; reflexivity.
      }
      destruct Htarget_exists as [q_state2' Happly0].
      pose proof (Hresult_vector qm0 (proj2_sig (projT1 q)) sv0
        (proj2_sig (projT2 q)) q_state2' Happly0) as Htarget_result.
      destruct Htarget_result as [lpn0 [Hget0 [Hidx0 Hvec0]]].
      assert (Hlpn : lpn0 = lpn1).
      {
        rewrite Hgetall in Hget0.
        rewrite Hget1 in Hget0.
        inversion Hget0; reflexivity.
      }
      subst lpn0.
      assert (Hbase_irrel : forall d0 d1 (Hd : d0 = d1)
        (lpn : list (participant * nat))
        (Hproof0 : Datatypes.length (map snd lpn) = Datatypes.length lq /\
          NoDup (map snd lpn) /\
          Forall (fun i => i < d0) (map snd lpn))
        (Hproof1 : Datatypes.length (map snd lpn) = Datatypes.length lq /\
          NoDup (map snd lpn) /\
          Forall (fun i => i < d1) (map snd lpn)),
        uc_eval (proj1_sig
          (@base_to_ucom d0 (Datatypes.length lq) U (map snd lpn) Hproof0)) =
        uc_eval (proj1_sig
          (@base_to_ucom d1 (Datatypes.length lq) U (map snd lpn) Hproof1))).
      {
        intros d0 d1 Hd lpn Hproof0 Hproof1.
        destruct Hd.
        assert (Hproofeq : Hproof0 = Hproof1) by apply proof_irrelevance.
        rewrite Hproofeq; reflexivity.
      }
      assert (Hgate :
        uc_eval (proj1_sig
          (@base_to_ucom (Datatypes.length (elems _ _ qm0))
            (Datatypes.length lq) U (map snd lpn1) Hidx0)) =
        uc_eval (proj1_sig
          (@base_to_ucom (Datatypes.length (elems _ _ qm1))
            (Datatypes.length lq) U (map snd lpn1) Hidx1))).
      {
        exact (Hbase_irrel _ _ Hmaplen lpn1 Hidx0 Hidx1).
      }
      assert (Hvectorout :
        proj1_sig (projT2 q_state2') = proj1_sig (projT2 q_state2)).
      {
        rewrite Hvec0, Hvec1, Hgate, Hvector.
        rewrite Hmaplen.
        reflexivity.
      }
      assert (Happly_map : forall
        (qm : finite_map qubit_reference (participant * nat))
        (Hqm : quantum_map_wf qm)
        (sv : state_vector (Datatypes.length (elems _ _ qm)))
        (Hsv : state_vector_wf sv) qs',
        apply_unitary qm Hqm sv Hsv U lq eq_refl Hdim = Some qs' ->
        proj1_sig (projT1 qs') = qm).
      {
        intros qm Hqm sv Hsv qs' Happly.
        unfold apply_unitary in Happly.
        destruct (lt_dec 0 (Datatypes.length (elems _ _ qm)))
          as [Hstate|Hstate]; [|discriminate].
        destruct (le_dec (Datatypes.length lq)
          (Datatypes.length (elems _ _ qm))) as [Hdimle|Hdimle];
          [|discriminate].
        destruct (NoDup_dec (TEQ := qr_dec) lq) as [Hnd|Hnd];
          [|discriminate].
        destruct (get_all_values_certified qm lq) as [cert|] eqn:Hcert;
          [|discriminate].
        cbn in Happly; inversion Happly; reflexivity.
      }
      pose proof (Happly_map qm0 (proj2_sig (projT1 q)) sv0
        (proj2_sig (projT2 q)) q_state2' Happly0) as Hmap0.
      pose proof (Happly_map qm1 (proj2_sig (projT1 q_state1)) sv1
        (proj2_sig (projT2 q_state1)) q_state2 H3) as Hmap1.
      assert (Howned0 : Forall
        (fun q' => exists n, qm0 q' = Some (p, n)) lq).
      {
        apply Forall_forall; intros q' Hin.
        match goal with
        | [Howned_src : Forall _ lq |- _] =>
            apply Forall_forall with (x := q') in Howned_src;
              [|exact Hin];
            destruct Howned_src as [n Howner];
            exists n;
            rewrite Hmapfun;
            exact Howner
        end.
      }
      exists (q_state2', insert s0 p P); split.
      - eapply Congr with (M1' := s0); [exact Hsession|].
        eapply Unitary with (Hlen := eq_refl) (Hdim := Hdim); eauto.
      - unfold equivalent_states; simpl.
        split; [apply unfoldM_refl|].
        + split.
          * unfold equivalent, included; split; intros q' v Hlookup.
            -- rewrite Hmap1.
               rewrite Hmap0 in Hlookup.
               rewrite Hmapfun in Hlookup; exact Hlookup.
            -- rewrite Hmap0.
               rewrite Hmap1 in Hlookup.
               rewrite <- Hmapfun in Hlookup; exact Hlookup.
          * exact Hvectorout.
    }
    {
      destruct s1' as [q_state1' M1''].
      destruct H0 as [Hsession [Hmap Hvector]].
      assert (Htrans : forall M N K, unfoldM M N -> unfoldM N K -> unfoldM M K).
      {
        intros M N K HMN HNK pt.
        destruct (HMN pt) as [[HM HN]|[P [Q [HM [HN HPQ]]]]].
        - destruct (HNK pt) as [[HN' HK]|[Q' [R [HN' [HK HQR]]]]].
          + left; split; congruence.
          + rewrite HN in HN'; discriminate.
        - destruct (HNK pt) as [[HN' HK]|[Q' [R [HN' [HK HQR]]]]].
          + rewrite HN in HN'; discriminate.
          + rewrite HN in HN'; inversion HN'; subst Q'.
            right; exists P, R; split; [exact HM|]; split; [exact HK|].
            eapply gttT; eauto.
      }
      assert (Hsrc : equivalent_states (q_state1, M1') (q_state1', M1')).
      {
        unfold equivalent_states; simpl.
        split; [apply unfoldM_refl|].
        split; assumption.
      }
      pose proof (IH (q_state1, M1') (q_state1', M1') (q_state2, M2)
        (Tau p) pi H2 Hsrc) as Hrec.
      destruct Hrec as [s2' [Hstep Hstates]].
      destruct s2' as [q_state2' M2''].
      destruct Hstates as [Hsession2 [Hmap2 Hvector2]].
      assert (Hsource_unfold : unfoldM M1'' M1').
      {
        eapply Htrans.
        - exact Hsession.
        - exact H1.
      }
      exists (q_state2', M2''); split.
      - eapply Congr with (M1' := M1'); eauto.
      - unfold equivalent_states; simpl.
        split; [exact Hsession2|].
        split; assumption.
    }
  }
  {
    inversion H; clear H; cleanup.
    {
      simpl in *.
      unfold equivalent_states in H0; simpl in H0.
      destruct H0 as [Hsession [Hmaps Hvector]].
      destruct s1'; simpl in *.
      eexists; split.
      - eapply Congr with (M1' := s0); [exact Hsession|].
        solve [econstructor; eauto].
      - unfold equivalent_states; simpl.
        split; [apply unfoldM_refl|].
        split; assumption.
    }
    {
      simpl in *.
      unfold equivalent_states in H0; simpl in H0.
      destruct s1'; simpl in *.
      destruct H0 as [Hsession [Hmaps Hvector]].
      assert_fresh ((` (projT1 q0)) v0 = Some (p, n)). {
        eapply (proj2 Hmaps); exact Hlookup.
      }
      eexists; split.
      - eapply Congr with (M1' := s0); [exact Hsession|].
        eapply Comm_Q with (n := n) (Hlookup := HA); eauto.
      - unfold equivalent_states; simpl.
        split; [apply unfoldM_refl|].
        + split.
          * unfold transfer_qubit_from_lookup; simpl.
            eapply ExamplesHelpers.insert_equiv_lemma; exact Hmaps.
          * simpl; exact Hvector.
    }
    {
      destruct s1' as [q_state1' M1''].
      destruct H0 as [Hsession [Hmap Hvector]].
      assert (Htrans : forall M N K, unfoldM M N -> unfoldM N K -> unfoldM M K).
      {
        intros M N K HMN HNK pt.
        destruct (HMN pt) as [[HM HN]|[P [Q [HM [HN HPQ]]]]].
        - destruct (HNK pt) as [[HN' HK]|[Q' [R [HN' [HK HQR]]]]].
          + left; split; congruence.
          + rewrite HN in HN'; discriminate.
        - destruct (HNK pt) as [[HN' HK]|[Q' [R [HN' [HK HQR]]]]].
          + rewrite HN in HN'; discriminate.
          + rewrite HN in HN'; inversion HN'; subst Q'.
            right; exists P, R; split; [exact HM|]; split; [exact HK|].
            eapply gttT; eauto.
      }
      assert (Hsrc : equivalent_states (q_state1, M1') (q_state1', M1')).
      {
        unfold equivalent_states; simpl.
        split; [apply unfoldM_refl|].
        split; assumption.
      }
      pose proof (IH (q_state1, M1') (q_state1', M1') (q_state2, M2)
        (Transmit p q l v) pi H2 Hsrc) as Hrec.
      destruct Hrec as [s2' [Hstep Hstates]].
      destruct s2' as [q_state2' M2''].
      destruct Hstates as [Hsession2 [Hmap2 Hvector2]].
      assert (Hsource_unfold : unfoldM M1'' M1').
      {
        eapply Htrans.
        - exact Hsession.
        - exact H1.
      }
      exists (q_state2', M2''); split.
      - eapply Congr with (M1' := M1'); eauto.
      - unfold equivalent_states; simpl.
        split; [exact Hsession2|].
        split; assumption.
    }
  }
Unshelve.
- intro Hin.
  unfold equivalent_states in H0; simpl in H0.
  destruct H0 as [_ [Hmaps _]].
  pose proof (FMap.equivalent_Permutation _ _ _ _ Hmaps) as Hperm.
  apply in_map_iff in Hin as [[q' v] [Hfst Hin]].
  simpl in Hfst; subst q'.
  apply Hfresh.
  apply in_map_iff.
  exists (q, v); split; [reflexivity|].
  eapply Permutation_in; [exact Hperm|exact Hin].
- apply Permutation_length.
  exact (FMap.equivalent_Permutation _ _ _ _ e).
Qed.

Lemma multistep_equivalent_states:
forall la s1 s1' s2 pi,
multistep s1 la s2 pi ->
equivalent_states s1 s1' ->
exists s2',
multistep s1' la s2' pi /\
equivalent_states s2 s2'.
Proof.
  intros la s1 s1' s2 pi Hmulti.
  revert s1'.
  induction Hmulti as
    [qstate M M' HMM'|s1 s2 s3 r1 r2 a la Hstep Htail IH];
    intros s1' Hstates.
  - destruct s1' as [qstate' M'']; simpl in Hstates.
    unfold equivalent_states in Hstates; simpl in Hstates.
    destruct Hstates as [Hunfold [Hmaps Hvector]].
    exists (qstate', M''); split.
    + apply ms_refl, equivalent_refl.
    + unfold equivalent_states; simpl.
      split.
      * eapply unfoldM_trans; [exact Hunfold|].
        apply equivalent_unfoldM; exact HMM'.
      * split; assumption.
  - destruct (step_equivalent_states _ _ _ _ _ Hstep Hstates)
      as [s2' [Hstep' Hstates']].
    destruct (IH s2' Hstates') as [s3' [Htail' Hstates'']].
    exists s3'; split.
    + eapply ms_step; eauto.
    + exact Hstates''.
Qed.

Opaque insert equivalent.

Section MultistepShouldSwapNoNewqHelpers.
Context {a a0 : action} {s s' : state} {pi : R}
  (H : multistep s (a :: a0 :: nil) s' pi)
  (H0 : should_swap_no_newq a a0 = true)
  (H1 : no_newq_session (snd s)).

Lemma Hbase_gates_commute : forall dim m n
      (U : base_Unitary m) (V : base_Unitary n) l1 l2 Hidx1 Hidx2,
    length l1 = m -> length l2 = n ->
    (forall i j, In i l1 -> In j l2 -> i <> j) ->
    uc_eval (proj1_sig (@base_to_ucom dim m U l1 Hidx1)) ×
      uc_eval (proj1_sig (@base_to_ucom dim n V l2 Hidx2)) =
    uc_eval (proj1_sig (@base_to_ucom dim n V l2 Hidx2)) ×
      uc_eval (proj1_sig (@base_to_ucom dim m U l1 Hidx1)).
Proof.
    intros dim m n U V l1 l2 Hidx1 Hidx2 Hlen1 Hlen2 Hdisj.
    assert (Hdisj_rev : forall i j, In i l2 -> In j l1 -> i <> j).
    { intros i j Hi Hj Heq. apply (Hdisj j i Hj Hi). symmetry; exact Heq. }
    dependent destruction U; dependent destruction V.
    - destruct l1 as [|i [|i' l1]]; simpl in Hlen1; try discriminate.
      destruct l2 as [|j [|j' l2]]; simpl in Hlen2; try discriminate.
      inversion Hlen1; inversion Hlen2; subst.
      simpl; symmetry.
      pose proof (@U_V_comm dim i j (U_R r r0 r1) (U_R r2 r3 r4)
        (Hdisj i j (or_introl eq_refl) (or_introl eq_refl))) as Hcomm.
      unfold uc_equiv in Hcomm; simpl in Hcomm; exact Hcomm.
    - destruct l1 as [|i [|i' l1]]; simpl in Hlen1; try discriminate.
      destruct l2 as [|j [|k [|x l2]]]; simpl in Hlen2; try discriminate.
      inversion Hlen1; inversion Hlen2; subst.
      simpl; symmetry.
      pose proof (@U_CNOT_comm dim i j k (U_R r r0 r1)
        (Hdisj i j (or_introl eq_refl) (or_introl eq_refl))
        (Hdisj i k (or_introl eq_refl) (or_intror (or_introl eq_refl)))) as Hcomm.
      unfold uc_equiv in Hcomm; simpl in Hcomm; exact Hcomm.
    - destruct l1 as [|i [|j [|x l1]]]; simpl in Hlen1; try discriminate.
      destruct l2 as [|k [|k' l2]]; simpl in Hlen2; try discriminate.
      inversion Hlen1; inversion Hlen2; subst.
      simpl.
      pose proof (@U_CNOT_comm dim k i j (U_R r r0 r1)
        (Hdisj_rev k i (or_introl eq_refl) (or_introl eq_refl))
        (Hdisj_rev k j (or_introl eq_refl) (or_intror (or_introl eq_refl)))) as Hcomm.
      unfold uc_equiv in Hcomm; simpl in Hcomm; exact Hcomm.
    - destruct l1 as [|i [|j [|x l1]]]; simpl in Hlen1; try discriminate.
      destruct l2 as [|k [|x [|x' l2]]]; simpl in Hlen2; try discriminate.
      inversion Hlen1; inversion Hlen2; subst.
      simpl; symmetry.
      pose proof (@CNOT_CNOT_comm dim i j k x
        (Hdisj_rev k i (or_introl eq_refl) (or_introl eq_refl))
        (Hdisj_rev k j (or_introl eq_refl) (or_intror (or_introl eq_refl)))
        (Hdisj_rev x i (or_intror (or_introl eq_refl)) (or_introl eq_refl))
        (Hdisj_rev x j (or_intror (or_introl eq_refl))
          (or_intror (or_introl eq_refl)))) as Hcomm.
      unfold uc_equiv in Hcomm; simpl in Hcomm; exact Hcomm.
Qed.

Lemma Hproj_base_commute : forall total gate_dim
      (U : base_Unitary gate_dim) l
      (Hidx : length l = gate_dim /\ NoDup l /\
        Forall (fun i => i < total) l) q result,
    (forall i, In i l -> q <> i) ->
    proj q total result ×
      uc_eval (proj1_sig (@base_to_ucom total gate_dim U l Hidx)) =
    uc_eval (proj1_sig (@base_to_ucom total gate_dim U l Hidx)) ×
      proj q total result.
Proof.
    intros total gate_dim U l Hidx q result Hdisj.
    dependent destruction U.
    - destruct Hidx as [Hlen [Hnd Hbounds]].
      destruct l as [|i [|i' l]]; simpl in Hlen; try discriminate.
      change (pad_u total q (bool_to_matrix result) ×
        ueval_r total i (U_R r r0 r1) =
        ueval_r total i (U_R r r0 r1) ×
          pad_u total q (bool_to_matrix result)).
      unfold ueval_r.
      apply pad_A_B_commutes.
      + intro Heq. subst q. apply (Hdisj i); simpl; auto.
      + auto with wf_db.
      + auto with wf_db.
    - destruct Hidx as [Hlen [Hnd Hbounds]].
      destruct l as [|wire0 [|wire1 [|extra l]]];
        simpl in Hlen; try discriminate.
      change (pad_u total q (bool_to_matrix result) ×
        ueval_cnot total wire0 wire1 =
        ueval_cnot total wire0 wire1 × pad_u total q (bool_to_matrix result)).
      unfold ueval_cnot.
      apply pad_A_ctrl_commutes.
      + intro Heq. subst q. apply (Hdisj wire0); simpl; auto.
      + intro Heq. subst q. apply (Hdisj wire1); simpl; auto.
      + auto with wf_db.
      + auto with wf_db.
Qed.

Lemma Hproj_base_norm : forall total gate_dim
      (U : base_Unitary gate_dim) l
      (Hidx : length l = gate_dim /\ NoDup l /\
        Forall (fun i => i < total) l) q result
      (sv : state_vector total) (Hsv : state_vector_wf sv),
    (forall i, In i l -> q <> i) ->
    @norm (2 ^ total)
      (proj q total result ×
        (uc_eval (proj1_sig (@base_to_ucom total gate_dim U l Hidx)) × sv)) =
    @norm (2 ^ total) (proj q total result × sv).
Proof.
    intros total gate_dim U l Hidx q result sv Hsv Hdisj.
    set (Ufull := uc_eval
      (proj1_sig (@base_to_ucom total gate_dim U l Hidx))).
    assert (Hcomm : proj q total result × Ufull = Ufull × proj q total result).
    { unfold Ufull; apply Hproj_base_commute; exact Hdisj. }
    rewrite <- Mmult_assoc, Hcomm, Mmult_assoc.
    apply norm_unitary.
    - exact (proj2_sig (@base_to_ucom total gate_dim U l Hidx)).
    - apply WF_mult; [apply WF_proj|exact (proj1 Hsv)].
Qed.

Lemma Hinsert_tensor : forall (prefix suffix : nat)
      (A : Square (2 ^ prefix)) (B : Square (2 ^ suffix)) (bit : bool),
    WF_Matrix A -> WF_Matrix B ->
    @Mmult ((2 ^ prefix * 2) * 2 ^ suffix)
      ((2 ^ prefix * 1) * 2 ^ suffix) ((2 ^ prefix * 1) * 2 ^ suffix)
      ((I (2 ^ prefix) ⊗ ket (if bit then 1 else 0)) ⊗ I (2 ^ suffix))
      ((A ⊗ I 1) ⊗ B) =
    @Mmult ((2 ^ prefix * 2) * 2 ^ suffix)
      ((2 ^ prefix * 2) * 2 ^ suffix) ((2 ^ prefix * 1) * 2 ^ suffix)
      ((A ⊗ I 2) ⊗ B)
      ((I (2 ^ prefix) ⊗ ket (if bit then 1 else 0)) ⊗ I (2 ^ suffix)).
Proof.
    intros prefix suffix A B bit HA HB.
    set (k := ket (if bit then 1 else 0)).
    assert (Hleft : (I (2 ^ prefix) ⊗ k) × (A ⊗ I 1) = A ⊗ k).
    {
      rewrite (@kron_mixed_product (2 ^ prefix) (2 ^ prefix) (2 ^ prefix)
        2 1 1 (I (2 ^ prefix)) k A (I 1)).
      rewrite Mmult_1_l by exact HA.
      rewrite Mmult_1_r by (unfold k; auto with wf_db).
      reflexivity.
    }
    assert (Hright : (A ⊗ I 2) × (I (2 ^ prefix) ⊗ k) = A ⊗ k).
    {
      rewrite (@kron_mixed_product (2 ^ prefix) (2 ^ prefix) (2 ^ prefix)
        2 2 1 A (I 2) (I (2 ^ prefix)) k).
      rewrite Mmult_1_r by exact HA.
      rewrite Mmult_1_l by (unfold k; auto with wf_db).
      reflexivity.
    }
    transitivity ((A ⊗ k) ⊗ B).
    - rewrite (@kron_mixed_product (2 ^ prefix * 2) (2 ^ prefix * 1)
        (2 ^ prefix * 1) (2 ^ suffix) (2 ^ suffix) (2 ^ suffix)
        (I (2 ^ prefix) ⊗ k) (I (2 ^ suffix))
        (A ⊗ I 1) B).
      rewrite Hleft.
      rewrite Mmult_1_l by exact HB.
      reflexivity.
    - rewrite (@kron_mixed_product (2 ^ prefix * 2) (2 ^ prefix * 2)
        (2 ^ prefix * 1) (2 ^ suffix) (2 ^ suffix) (2 ^ suffix)
        (A ⊗ I 2) B (I (2 ^ prefix) ⊗ k) (I (2 ^ suffix))).
      rewrite Hright.
      rewrite Mmult_1_r by exact HB.
      reflexivity.
Qed.

Lemma Hpad_u_split_left : forall n i j (A : Square 2),
    WF_Matrix A -> j < i -> i <= n ->
    pad_u n j A = pad_u i j A ⊗ I (2 ^ (n - i)).
Proof.
    intros n i j A HA Hji Hin.
    unfold pad_u, pad.
    bdestruct (j + 1 <=? n); [|lia].
    bdestruct (j + 1 <=? i); [|lia].
    replace (n - (j + 1)) with ((i - (j + 1)) + (n - i)) by lia.
    replace (2 ^ (i - (j + 1) + (n - i)))
      with (2 ^ (i - (j + 1)) * 2 ^ (n - i))
      by (rewrite Nat.pow_add_r; reflexivity).
    symmetry.
    transitivity ((I (2 ^ j) ⊗ A) ⊗
      (I (2 ^ (i - (j + 1))) ⊗ I (2 ^ (n - i)))).
    - apply kron_assoc; auto with wf_db.
    - rewrite id_kron; reflexivity.
Qed.

Lemma Hpad_u_split_right : forall n i j (A : Square 2),
    WF_Matrix A -> i <= n -> i <= j -> j < n ->
    pad_u n j A = I (2 ^ i) ⊗ pad_u (n - i) (j - i) A.
Proof.
    intros n i j A HA Hin Hij Hjn.
    unfold pad_u, pad.
    bdestruct (j + 1 <=? n); [|lia].
    bdestruct (j - i + 1 <=? n - i); [|lia].
    replace j with (i + (j - i)) at 1 by lia.
    rewrite <- (pow_two_split j i ltac:(lia)).
    rewrite <- (id_kron (2 ^ i) (2 ^ (j - i))).
    replace (n - (j + 1)) with ((n - i) - ((j - i) + 1)) by lia.
    assert (Hpow :
      2 ^ (n - i) = 2 ^ (j - i) *
        (2 * 2 ^ ((n - i) - ((j - i) + 1)))).
    {
      replace (j - i + 1) with (S (j - i)) by lia.
      pose proof (pow_two_split (n - i) (S (j - i)) ltac:(lia)) as Hsplit.
      rewrite Nat.pow_succ_r in Hsplit by lia.
      nia.
    }
    transitivity ((I (2 ^ i) ⊗ I (2 ^ (j - i))) ⊗
      (A ⊗ I (2 ^ ((n - i) - ((j - i) + 1))))).
    - apply kron_assoc; auto with wf_db.
    - symmetry.
      transitivity (I (2 ^ i) ⊗
        (I (2 ^ (j - i)) ⊗
          (A ⊗ I (2 ^ ((n - i) - ((j - i) + 1)))))).
      + f_equal.
        * exact Hpow.
        * exact Hpow.
        * apply kron_assoc; auto with wf_db.
        * symmetry; apply kron_assoc; auto with wf_db.
Qed.

Lemma Hkron_identity_middle : forall m n p q
    (A : Matrix m n) (B : Matrix p q),
    (A ⊗ I 1) ⊗ B = A ⊗ B.
Proof.
    intros m n p q A B.
    rewrite kron_1_r; reflexivity.
Qed.

Lemma Hinsert_pad_u_intertwine_away : forall (n index wire : nat) result
    (U : Square 2),
    index <= n -> wire < n -> wire <> index -> WF_Matrix U ->
    @Mmult ((2 ^ index * 2) * 2 ^ (n - index))
      ((2 ^ index * 1) * 2 ^ (n - index))
      ((2 ^ index * 1) * 2 ^ (n - index))
      (insert_measured_wire_operator n index result)
      (pad_u n wire U) =
    @Mmult ((2 ^ index * 2) * 2 ^ (n - index))
      ((2 ^ index * 2) * 2 ^ (n - index))
      ((2 ^ index * 1) * 2 ^ (n - index))
      (pad_u (S n) (if wire <? index then wire else S wire) U)
      (insert_measured_wire_operator n index result).
Proof.
    intros n index wire result U Hindex Hwire Hneq HU.
    destruct (lt_dec wire index) as [Hbefore|Hafter].
    - assert (Hlift : (if wire <? index then wire else S wire) = wire).
      {
        assert (Hltb : wire <? index = true) by (apply Nat.ltb_lt; exact Hbefore).
        rewrite Hltb; reflexivity.
      }
      rewrite Hlift.
      pose proof (Hpad_u_split_left n index wire U HU Hbefore Hindex)
        as Hsmall.
      pose proof (Hpad_u_split_left (S n) index wire U HU Hbefore ltac:(lia))
        as Hlarge.
      assert (Hsmall_factor :
        pad_u n wire U =
          (pad_u index wire U ⊗ I 1) ⊗ I (2 ^ (n - index))).
      {
        transitivity (pad_u index wire U ⊗ I (2 ^ (n - index))).
        - exact Hsmall.
        - symmetry; apply Hkron_identity_middle.
      }
      assert (Hpow : 2 ^ (S n - index) = 2 * 2 ^ (n - index)).
      {
        replace (S n - index) with (S (n - index)) by lia.
        rewrite Nat.pow_succ_r by lia.
        nia.
      }
      assert (Hlarge_factor :
        pad_u (S n) wire U =
          (pad_u index wire U ⊗ I 2) ⊗ I (2 ^ (n - index))).
      {
        rewrite Hlarge, Hpow.
        rewrite <- (id_kron 2 (2 ^ (n - index))).
        symmetry; apply kron_assoc; auto with wf_db.
      }
      rewrite Hsmall_factor, Hlarge_factor.
      unfold insert_measured_wire_operator.
      apply Hinsert_tensor; auto with wf_db.
    - assert (Hbefore : index < wire) by lia.
      assert (Hlift : (if wire <? index then wire else S wire) = S wire).
      {
        assert (Hltb : wire <? index = false) by (apply Nat.ltb_ge; lia).
        rewrite Hltb; reflexivity.
      }
      rewrite Hlift.
      pose proof (Hpad_u_split_right n index wire U HU Hindex
        ltac:(lia) Hwire) as Hsmall.
      pose proof (Hpad_u_split_right (S n) (S index) (S wire) U HU
        ltac:(lia) ltac:(lia) ltac:(lia)) as Hlarge.
      set (B := pad_u (n - index) (wire - index) U).
      assert (Hsmall_factor :
        pad_u n wire U =
          (I (2 ^ index) ⊗ I 1) ⊗ B).
      {
        unfold B.
        transitivity (I (2 ^ index) ⊗
          pad_u (n - index) (wire - index) U).
        - exact Hsmall.
        - symmetry; apply Hkron_identity_middle.
      }
      assert (Hlarge_factor :
        pad_u (S n) (S wire) U =
          (I (2 ^ index) ⊗ I 2) ⊗ B).
      {
        unfold B.
        rewrite Hlarge.
        replace (S n - S index) with (n - index) by lia.
        replace (S wire - S index) with (wire - index) by lia.
        replace (2 ^ (S index)) with (2 ^ index * 2) by
          (rewrite Nat.pow_succ_r; lia).
        rewrite <- (id_kron (2 ^ index) 2).
        reflexivity.
      }
      rewrite Hsmall_factor, Hlarge_factor.
      unfold insert_measured_wire_operator.
      apply Hinsert_tensor.
      + auto with wf_db.
      + unfold B; apply WF_pad_u; exact HU.
Qed.

Lemma Hinsert_pad_u_at_index : forall (n index : nat) result
    (U : Square 2),
    index < n -> WF_Matrix U ->
    @Mmult ((2 ^ index * 2) * 2 ^ (n - index))
      ((2 ^ index * 1) * 2 ^ (n - index))
      ((2 ^ index * 1) * 2 ^ (n - index))
      (insert_measured_wire_operator n index result)
      (pad_u n index U) =
    @Mmult ((2 ^ index * 2) * 2 ^ (n - index))
      ((2 ^ index * 2) * 2 ^ (n - index))
      ((2 ^ index * 1) * 2 ^ (n - index))
      (pad_u (S n) (S index) U)
      (insert_measured_wire_operator n index result).
Proof.
  intros n index result U Hindex HU.
  pose proof (Hpad_u_split_right n index index U HU ltac:(lia)
    ltac:(lia) Hindex) as Hsmall.
  pose proof (Hpad_u_split_right (S n) (S index) (S index) U HU
    ltac:(lia) ltac:(lia) ltac:(lia)) as Hlarge.
  set (B := pad_u (n - index) 0 U).
  assert (Hsmall' : pad_u n index U = I (2 ^ index) ⊗ B).
  {
    unfold B in *.
    rewrite Hsmall.
    replace (index - index) with 0 by lia.
    reflexivity.
  }
  assert (Hlarge' : pad_u (S n) (S index) U = I (2 ^ (S index)) ⊗ B).
  {
    unfold B in *.
    rewrite Hlarge.
    replace (S n - S index) with (n - index) by lia.
    replace (S index - S index) with 0 by lia.
    reflexivity.
  }
  assert (HB : WF_Matrix B).
  { unfold B; apply WF_pad_u; exact HU. }
  assert (Hiden : I (2 ^ index) ⊗ I 2 = I (2 ^ (S index))).
  {
    rewrite id_kron.
    f_equal.
    all: rewrite Nat.pow_succ_r; nia.
  }
  assert (Hsmall_tensor :
    ((I (2 ^ index) ⊗ I 1) ⊗ B) = I (2 ^ index) ⊗ B).
  { apply Hkron_identity_middle. }
  pose proof (Hinsert_tensor index (n - index) (I (2 ^ index)) B
    result (WF_I _) HB) as Htensor.
  rewrite Hsmall', Hlarge'.
  unfold insert_measured_wire_operator.
  rewrite <- Hsmall_tensor at 1.
  rewrite <- Hiden.
  exact Htensor.
Qed.

Lemma Hinsert_pad_u_intertwine : forall (n index wire : nat) result
    (U : Square 2),
    index <= n -> wire < n -> WF_Matrix U ->
    @Mmult ((2 ^ index * 2) * 2 ^ (n - index))
      ((2 ^ index * 1) * 2 ^ (n - index))
      ((2 ^ index * 1) * 2 ^ (n - index))
      (insert_measured_wire_operator n index result)
      (pad_u n wire U) =
    @Mmult ((2 ^ index * 2) * 2 ^ (n - index))
      ((2 ^ index * 2) * 2 ^ (n - index))
      ((2 ^ index * 1) * 2 ^ (n - index))
      (pad_u (S n) (if wire <? index then wire else S wire) U)
      (insert_measured_wire_operator n index result).
Proof.
  intros n index wire result U Hindex Hwire HU.
  destruct (lt_dec wire index) as [Hbefore|Hnotbefore].
  - exact (@Hinsert_pad_u_intertwine_away n index wire result U
      Hindex Hwire ltac:(lia) HU).
  - destruct (Nat.eq_dec wire index) as [Heq|Hafter].
    + subst wire.
      replace (if index <? index then index else S index) with (S index)
        by (bdestruct (index <? index); lia).
      exact (@Hinsert_pad_u_at_index n index result U ltac:(lia) HU).
    + exact (@Hinsert_pad_u_intertwine_away n index wire result U
        Hindex Hwire ltac:(lia) HU).
Qed.

Lemma Hget_value : forall
    (qm : finite_map qubit_reference (participant * fin))
    (qs : list qubit_reference) (values : list (participant * fin))
    (owner : participant) (idx : fin),
    get_all_values qm qs = Some values ->
    In (owner, idx) values ->
    exists q, In q qs /\ qm q = Some (owner, idx).
Proof.
    intros qm qs; induction qs as [|q qs IH];
      intros values owner idx Hget Hin.
    - simpl in Hget; inversion Hget; subst; contradiction.
    - simpl in Hget.
      destruct (qm q) as [v|] eqn:Hhead; try discriminate.
      destruct (get_all_values qm qs) as [vs|] eqn:Htail; try discriminate.
      inversion Hget; subst values.
      simpl in Hin; destruct Hin as [Heq|Hin].
      + inversion Heq; subst; exists q; split; [left; reflexivity|exact Hhead].
      + destruct (IH vs owner idx eq_refl Hin) as [q' [Hin' Hlookup']].
        exists q'; split; [right; exact Hin'|exact Hlookup'].
Qed.

Lemma Hindex_unique : forall qm (Hqm : quantum_map_wf qm)
      q q' owner owner' idx idx',
    qm q = Some (owner, idx) -> qm q' = Some (owner', idx') ->
    owner <> owner' -> idx <> idx'.
Proof.
    intros qm Hqm q q' owner owner' idx idx' Hq Hq' Howner Heq.
    destruct Hqm as [Hnd _].
    pose proof (specs qubit_reference (participant * fin) qm) as [_ Hspec].
    assert (Hin : In (q, (owner, idx)) (elems qubit_reference (participant * fin) qm))
      by (apply Hspec; exact Hq).
    assert (Hin' : In (q', (owner', idx')) (elems qubit_reference (participant * fin) qm))
      by (apply Hspec; exact Hq').
    assert (Heq' : (q, (owner, idx)) = (q', (owner', idx'))).
    {
      eapply NoDup_In_inj with
        (l := elems qubit_reference (participant * fin) qm)
        (f := fun qv : qubit_reference * (participant * fin) => snd (snd qv));
        eauto.
    }
    inversion Heq'; subst; contradiction.
Qed.

Lemma Hqubits_distinct_if_owners_distinct : forall
    (qm : finite_map qubit_reference (participant * fin))
    q q' owner owner' idx idx',
    qm q = Some (owner, idx) ->
    qm q' = Some (owner', idx') ->
    owner <> owner' ->
    q <> q'.
Proof.
    intros qm q q' owner owner' idx idx' Hq Hq' Howner Heq.
    subst q'.
    rewrite Hq in Hq'.
    inversion Hq'; subst; contradiction.
Qed.

Lemma Hqubit_not_in_list_owned_by_other : forall
    (qm : finite_map qubit_reference (participant * fin))
    q owner owner' index lq,
    qm q = Some (owner, index) ->
    Forall (fun q' => exists index', qm q' = Some (owner', index')) lq ->
    owner <> owner' ->
    ~ In q lq.
Proof.
    intros qm q owner owner' index lq Hlookup Howners Hneq Hin.
    rewrite Forall_forall in Howners.
    destruct (Howners q Hin) as [index' Hlookup'].
    rewrite Hlookup in Hlookup'.
    inversion Hlookup'; congruence.
Qed.

Lemma Hmeasure_output_removed_lookup : forall
    qm (Hqm : quantum_map_wf qm)
    sv (Hsv : state_vector_wf sv)
    q owner index result Hlookup Hlen Hnonzero,
    (` (projT1 (snd (measure_qubit_from_nonzero
      qm Hqm sv Hsv q owner index result Hlookup Hlen Hnonzero)))) q = None.
Proof.
    intros qm Hqm sv Hsv q owner index result Hlookup Hlen Hnonzero.
    rewrite measure_qubit_nonzero_map.
    destruct (remove_and_reindex_qubit_map qm q index q)
      as [value|] eqn:Hremoved; [|reflexivity].
    exfalso.
    assert (Hne : remove_and_reindex_qubit_map qm q index q <> None)
      by (rewrite Hremoved; discriminate).
    apply (proj1 (@remove_and_reindex_qubit_map_lookup_none
      qm q index q)) in Hne.
    destruct Hne as [Hneq _].
    apply Hneq; reflexivity.
Qed.

Lemma Hmeasure_output_lookup_neq : forall
    (qm : finite_map qubit_reference (participant * fin))
    (Hqm : quantum_map_wf qm)
    (sv : state_vector (Datatypes.length
      (elems qubit_reference (participant * fin) qm)))
    (Hsv : state_vector_wf sv) q owner index result Hlookup Hlen Hnonzero
    (qs_after : quantum_state) q' owner' index',
    qs_after = snd (measure_qubit_from_nonzero qm Hqm sv Hsv
      q owner index result Hlookup Hlen Hnonzero) ->
    (` (projT1 qs_after)) q' = Some (owner', index') ->
    q <> q'.
Proof.
  intros qm Hqm sv Hsv q owner index result Hlookup Hlen Hnonzero
    qs_after q' owner' index' Hsame Hlookup_after Heq.
  subst q'.
  pose proof (@Hmeasure_output_removed_lookup qm Hqm sv Hsv
    q owner index result Hlookup Hlen Hnonzero) as Hremoved.
  rewrite measure_qubit_nonzero_map in Hremoved.
  rewrite Hsame in Hlookup_after.
  rewrite measure_qubit_nonzero_map in Hlookup_after.
  rewrite Hremoved in Hlookup_after.
  discriminate.
Qed.

Lemma base_gates_commute_for_disjoint_owners : forall
    (m n : nat) (U : base_Unitary m) (V : base_Unitary n)
    (qm : finite_map qubit_reference (participant * fin))
    (Hqm : quantum_map_wf qm)
    (owner1 owner0 : participant)
    (lq1 lq0 : list qubit_reference)
    (lpn1 lpn0 : list (participant * fin))
    (Hidx1 : Datatypes.length (map snd lpn1) = m /\
      NoDup (map snd lpn1) /\
      Forall (fun i => (i < Datatypes.length
        (elems qubit_reference (participant * fin) qm))%nat) (map snd lpn1))
    (Hidx0 : Datatypes.length (map snd lpn0) = n /\
      NoDup (map snd lpn0) /\
      Forall (fun i => (i < Datatypes.length
        (elems qubit_reference (participant * fin) qm))%nat) (map snd lpn0))
    (Hget1 : get_all_values qm lq1 = Some lpn1)
    (Hget0 : get_all_values qm lq0 = Some lpn0)
    (Howners1 : Forall (fun q => exists i, qm q = Some (owner1, i)) lq1)
    (Howners0 : Forall (fun q => exists i, qm q = Some (owner0, i)) lq0),
    owner1 <> owner0 ->
    uc_eval (proj1_sig (@base_to_ucom
      (Datatypes.length (elems qubit_reference (participant * fin) qm))
      m U (map snd lpn1) Hidx1)) ×
      uc_eval (proj1_sig (@base_to_ucom
      (Datatypes.length (elems qubit_reference (participant * fin) qm))
      n V (map snd lpn0) Hidx0)) =
    uc_eval (proj1_sig (@base_to_ucom
      (Datatypes.length (elems qubit_reference (participant * fin) qm))
      n V (map snd lpn0) Hidx0)) ×
      uc_eval (proj1_sig (@base_to_ucom
      (Datatypes.length (elems qubit_reference (participant * fin) qm))
      m U (map snd lpn1) Hidx1)).
Proof.
  intros m n U V qm Hqm owner1 owner0 lq1 lq0 lpn1 lpn0
    Hidx1 Hidx0 Hget1 Hget0 Howners1 Howners0 Howner_neq.
  eapply Hbase_gates_commute with
    (l1 := map snd lpn1) (l2 := map snd lpn0)
    (Hidx1 := Hidx1) (Hidx2 := Hidx0).
  - exact (proj1 Hidx1).
  - exact (proj1 Hidx0).
  - intros i j Hi Hj.
    apply in_map_iff in Hi as [[owner idx] [Heqi Hin1]].
    simpl in Heqi; subst i.
    apply in_map_iff in Hj as [[owner' idx'] [Heqj Hin0]].
    simpl in Heqj; subst j.
    destruct (Hget_value qm lq1 lpn1 owner idx Hget1 Hin1)
      as [q1 [Hin_q1 Hlookup1]].
    destruct (Hget_value qm lq0 lpn0 owner' idx' Hget0 Hin0)
      as [q0 [Hin_q0 Hlookup0]].
    rewrite Forall_forall in Howners1, Howners0.
    specialize (Howners1 q1 Hin_q1).
    specialize (Howners0 q0 Hin_q0).
    destruct Howners1 as [n1 Howner1].
    destruct Howners0 as [n0 Howner0].
    rewrite Hlookup1 in Howner1.
    rewrite Hlookup0 in Howner0.
    assert (Howner1eq : (owner, idx) = (owner1, n1)) by congruence.
    assert (Howner0eq : (owner', idx') = (owner0, n0)) by congruence.
    injection Howner1eq as Howner1name Howner1idx.
    injection Howner0eq as Howner0name Howner0idx.
    subst owner owner'.
    intro Heq.
    eapply (Hindex_unique qm Hqm q1 q0 owner1 owner0 idx idx'); eauto.
Qed.

Lemma Hremove_lookup : forall
    (qm : finite_map qubit_reference (participant * nat))
    (q measured : qubit_reference) (index : nat)
    (owner : participant) (old_index : nat),
    q <> measured ->
    qm q = Some (owner, old_index) ->
    remove_and_reindex_qubit_map qm measured index q =
      Some (owner, shift_wire_index index old_index).
Proof.
    intros qm q measured index owner old_index Hneq Hlookup.
    unfold remove_and_reindex_qubit_map, reindex_quantum_map.
    change (option_map (shift_qubit_index index)
      (delete (KEQ:=qr_dec) qm measured q) =
      Some (owner, shift_wire_index index old_index)).
    destruct (qr_dec measured q) as [Heq|Hneq'].
    - congruence.
    - rewrite delete_neq by exact Hneq'.
    rewrite Hlookup; reflexivity.
Qed.

Lemma lift_shift_wire_index : forall index wire,
    index <> wire ->
    (if shift_wire_index index wire <? index
      then shift_wire_index index wire
      else S (shift_wire_index index wire)) = wire.
Proof.
  intros index wire Hneq.
  unfold shift_wire_index.
  destruct (index <? wire) eqn:Hlt.
  - apply Nat.ltb_lt in Hlt.
    destruct wire as [|wire]; simpl in *; [lia|].
    destruct (wire <? index) eqn:Hpred.
    + apply Nat.ltb_lt in Hpred; lia.
    + reflexivity.
  - apply Nat.ltb_ge in Hlt.
    assert (Hcmp : wire <? index = true).
    { apply Nat.ltb_lt; lia. }
    rewrite Hcmp; reflexivity.
Qed.

Definition insert_measurement_bit (f : nat -> bool) (i : nat) (b : bool)
    : nat -> bool :=
  fun k => if k <? i then f k else if k =? i then b else f (Nat.pred k).

Lemma insert_measurement_bit_prefix : forall f i b k,
    k < i -> insert_measurement_bit f i b k = f k.
Proof.
  intros f i b k Hki; unfold insert_measurement_bit.
  destruct (k <? i) eqn:Hlt; [reflexivity|].
  apply Nat.ltb_ge in Hlt; lia.
Qed.

Lemma insert_measurement_bit_at : forall f i b,
    insert_measurement_bit f i b i = b.
Proof.
  intros f i b; unfold insert_measurement_bit.
  destruct (i <? i) eqn:Hlt; [apply Nat.ltb_lt in Hlt; lia|].
  destruct (i =? i) eqn:Heq; [reflexivity|].
  apply Nat.eqb_neq in Heq; contradiction.
Qed.

Lemma insert_measurement_bit_suffix : forall f i b k,
    i < k -> insert_measurement_bit f i b k = f (Nat.pred k).
Proof.
  intros f i b k Hik; unfold insert_measurement_bit.
  destruct (k <? i) eqn:Hlt; [apply Nat.ltb_lt in Hlt; lia|].
  destruct (k =? i) eqn:Heq; [apply Nat.eqb_eq in Heq; lia|].
  reflexivity.
Qed.

Definition lift_measurement_index (i wire : nat) : nat :=
  if wire <? i then wire else S wire.

Lemma insert_measurement_bit_at_lift : forall f i b wire,
    wire <> i ->
    insert_measurement_bit f i b (lift_measurement_index i wire) = f wire.
Proof.
  intros f i b wire Hneq.
  unfold lift_measurement_index.
  destruct (wire <? i) eqn:Hwi.
  - apply Nat.ltb_lt in Hwi.
    rewrite insert_measurement_bit_prefix by exact Hwi.
    reflexivity.
  - apply Nat.ltb_ge in Hwi.
    assert (Hlt : i < wire) by lia.
    rewrite insert_measurement_bit_suffix by lia.
    simpl; reflexivity.
Qed.

Lemma insert_measurement_bit_at_lift_all : forall f i b wire,
    insert_measurement_bit f i b (lift_measurement_index i wire) = f wire.
Proof.
  intros f i b wire.
  destruct (Nat.eq_dec wire i) as [->|Hneq].
  - unfold lift_measurement_index.
    rewrite Nat.ltb_irrefl.
    rewrite insert_measurement_bit_suffix by lia.
    simpl; reflexivity.
  - apply insert_measurement_bit_at_lift; exact Hneq.
Qed.

Lemma insert_measurement_bit_update : forall f i b wire value,
    insert_measurement_bit (update f wire value) i b =
      update (insert_measurement_bit f i b)
        (lift_measurement_index i wire) value.
Proof.
  intros f i b wire value.
  destruct (Nat.eq_dec wire i) as [->|Hneq].
  - apply functional_extensionality; intro k.
    unfold update, lift_measurement_index.
    rewrite Nat.ltb_irrefl.
    destruct (Nat.lt_trichotomy k i) as [Hki|[Hki|Hki]].
    + rewrite insert_measurement_bit_prefix by exact Hki.
      bdestruct (k =? i); [lia|].
      bdestruct (k =? S i); [lia|].
      rewrite insert_measurement_bit_prefix by exact Hki.
      reflexivity.
    + subst k.
      rewrite insert_measurement_bit_at.
      bdestruct (i =? S i); [lia|].
      rewrite insert_measurement_bit_at.
      reflexivity.
    + bdestruct (k =? S i).
      * subst k.
        rewrite insert_measurement_bit_suffix by lia.
        simpl Nat.pred.
        bdestruct (i =? i); try lia.
        bdestruct (S i =? S i); try lia.
        reflexivity.
      * assert (Hksi : k <> S i) by congruence.
        rewrite insert_measurement_bit_suffix by lia.
        destruct (Nat.eqb (Nat.pred k) i) eqn:Hpred.
        -- apply Nat.eqb_eq in Hpred.
           assert (k = S i) by (destruct k; simpl in *; lia).
           contradiction.
        -- destruct (Nat.eqb k (S i)) eqn:Hks.
           ++ apply Nat.eqb_eq in Hks; contradiction.
           ++ apply Nat.eqb_neq in Hks.
           rewrite insert_measurement_bit_suffix by lia.
           reflexivity.
  - apply functional_extensionality; intro k.
    unfold update.
    destruct (Nat.lt_trichotomy k i) as [Hki|[Hki|Hki]].
    + destruct (Nat.lt_trichotomy wire i) as [Hwi|[Hwi|Hwi]].
      * assert (Hlift : lift_measurement_index i wire = wire).
        { unfold lift_measurement_index.
          assert (Hltb : wire <? i = true) by (apply Nat.ltb_lt; exact Hwi).
          rewrite Hltb; reflexivity. }
        rewrite Hlift, !insert_measurement_bit_prefix by assumption.
        reflexivity.
      * subst wire; contradiction.
      * assert (Hlift : lift_measurement_index i wire = S wire).
        { unfold lift_measurement_index.
          assert (Hgeb : wire <? i = false) by (apply Nat.ltb_ge; lia).
          rewrite Hgeb; reflexivity. }
        rewrite Hlift, !insert_measurement_bit_prefix by assumption.
        destruct (k =? wire) eqn:Hkw; [apply Nat.eqb_eq in Hkw; lia|].
        destruct (k =? S wire) eqn:Hksw; [apply Nat.eqb_eq in Hksw; lia|].
        reflexivity.
    + subst k.
      rewrite !insert_measurement_bit_at.
      destruct (Nat.lt_trichotomy wire i) as [Hwi|[Hwi|Hwi]].
      * assert (Hlift : lift_measurement_index i wire = wire).
        { unfold lift_measurement_index.
          assert (Hltb : wire <? i = true) by (apply Nat.ltb_lt; exact Hwi).
          rewrite Hltb; reflexivity. }
        rewrite Hlift.
        destruct (i =? wire) eqn:Hiw;
          [apply Nat.eqb_eq in Hiw; lia|].
        reflexivity.
      * subst wire; contradiction.
      * assert (Hlift : lift_measurement_index i wire = S wire).
        { unfold lift_measurement_index.
          assert (Hgeb : wire <? i = false) by (apply Nat.ltb_ge; lia).
          rewrite Hgeb; reflexivity. }
        rewrite Hlift.
        destruct (i =? wire) eqn:Hiw; [apply Nat.eqb_eq in Hiw; lia|].
        destruct (i =? S wire) eqn:Hisw;
          [apply Nat.eqb_eq in Hisw; lia|].
        reflexivity.
    + destruct (Nat.lt_trichotomy wire i) as [Hwi|[Hwi|Hwi]].
      * assert (Hlift : lift_measurement_index i wire = wire).
        { unfold lift_measurement_index.
          assert (Hltb : wire <? i = true) by (apply Nat.ltb_lt; exact Hwi).
          rewrite Hltb; reflexivity. }
        rewrite Hlift, !insert_measurement_bit_suffix by lia.
        destruct (Nat.pred k =? wire) eqn:Hpk;
          [apply Nat.eqb_eq in Hpk; lia|].
        destruct (k =? wire) eqn:Hkw; [apply Nat.eqb_eq in Hkw; lia|].
        reflexivity.
      * subst wire; contradiction.
      * assert (Hlift : lift_measurement_index i wire = S wire).
        { unfold lift_measurement_index.
          assert (Hgeb : wire <? i = false) by (apply Nat.ltb_ge; lia).
          rewrite Hgeb; reflexivity. }
        rewrite Hlift, !insert_measurement_bit_suffix by lia.
        destruct (Nat.pred k =? wire) eqn:Hpk.
        -- apply Nat.eqb_eq in Hpk.
           assert (Hk : k = S wire) by (destruct k; simpl in *; lia).
           rewrite Hpk, Hk, !Nat.eqb_refl; reflexivity.
        -- apply Nat.eqb_neq in Hpk.
           destruct (k =? S wire) eqn:Hksw; [apply Nat.eqb_eq in Hksw; lia|].
           reflexivity.
Qed.

Lemma Hinsert_measured_wire_f_to_vec : forall n i b f,
    i <= n ->
    @Mmult (2 ^ (S n)) (2 ^ n) 1
      (insert_measured_wire_operator n i b) (f_to_vec n f) =
      f_to_vec (S n) (insert_measurement_bit f i b).
Proof.
  intros n i b f Hi.
  set (g := insert_measurement_bit f i b).
  assert (Hfirst : @Mmult (2 ^ i * 2) (2 ^ i * 1) 1
      (I (2 ^ i) ⊗ ket (if b then 1 else 0)) (f_to_vec i f) =
      f_to_vec i f ⊗ ket (if b then 1 else 0)).
  {
    transitivity ((I (2 ^ i) ⊗ ket (if b then 1 else 0)) ×
      (f_to_vec i f ⊗ I 1)).
    - apply f_equal.
      symmetry; apply kron_1_r.
    - rewrite (@kron_mixed_product (2 ^ i) (2 ^ i) 1 2 1 1
        (I (2 ^ i)) (ket (if b then 1 else 0)) (f_to_vec i f) (I 1)).
      rewrite Mmult_1_l by auto with wf_db.
      rewrite Mmult_1_r by auto with wf_db.
      reflexivity.
  }
  destruct (Nat.eq_dec i n) as [Heq|Hlt].
  - subst n.
    assert (Hsame : f_to_vec i g = f_to_vec i f).
    { apply f_to_vec_eq; intros k Hk.
      unfold g; apply insert_measurement_bit_prefix; lia. }
    assert (Hbit : g i = b).
    { unfold g; apply insert_measurement_bit_at. }
    simpl.
    rewrite Hsame, Hbit.
    unfold insert_measured_wire_operator.
    rewrite Nat.sub_diag.
    simpl.
    rewrite kron_1_r by auto with wf_db.
    replace (Nat.b2n b) with (if b then 1 else 0) by (destruct b; reflexivity).
    transitivity (@Mmult (2 ^ i * 2) (2 ^ i * 1) 1
      (I (2 ^ i) ⊗ ket (if b then 1 else 0)) (f_to_vec i f)).
    + apply Mmult_change_dims; nia.
    + exact Hfirst.
  - assert (Hlt' : i < n) by lia.
    assert (Hprefix : f_to_vec i g = f_to_vec i f).
    { apply f_to_vec_eq; intros k Hk.
      unfold g; apply insert_measurement_bit_prefix; lia. }
    assert (Hbit : g i = b).
    { unfold g; apply insert_measurement_bit_at. }
    pose proof (f_to_vec_split 0 n i f Hlt') as Hsource.
    pose proof (f_to_vec_split 0 (S n) i g ltac:(lia)) as Htarget.
    replace (i + 1) with (S i) in Hsource by lia.
    replace (S n - 1 - i) with (n - i) in Htarget by lia.
    replace (i + 1) with (S i) in Htarget by lia.
    assert (Htail : f_to_vec (n - i) (shift g (S i)) =
        ket (if f i then 1 else 0) ⊗
          f_to_vec (n - 1 - i) (shift f (S i))).
    {
      assert (Hshift : f_to_vec (n - i) (shift g (S i)) =
          f_to_vec (n - i) (shift f i)).
      { apply f_to_vec_eq; intros k Hk.
        unfold shift, g.
        rewrite insert_measurement_bit_suffix by lia.
        replace (Nat.pred (k + S i)) with (k + i) by lia.
        reflexivity. }
      pose proof (f_to_vec_split 0 (n - i) 0 (shift f i)
        ltac:(lia)) as Hsplit_tail.
      replace (n - i - 1 - 0) with (n - 1 - i) in Hsplit_tail by lia.
      simpl in Hsplit_tail.
      rewrite kron_1_l in Hsplit_tail by auto with wf_db.
      assert (Hshift2 : f_to_vec (n - 1 - i) (shift (shift f i) 1) =
          f_to_vec (n - 1 - i) (shift f (S i))).
      { apply f_to_vec_eq; intros k Hk.
        unfold shift; f_equal; lia. }
      rewrite Hshift2 in Hsplit_tail.
      unfold shift in Hsplit_tail; simpl in Hsplit_tail.
      rewrite Hshift.
      destruct (f i); simpl in *; exact Hsplit_tail.
    }
    rewrite Hprefix, Hbit, Htail in Htarget.
    rewrite kron_assoc in Hsource by auto with wf_db.
    rewrite Hsource, Htarget.
    unfold insert_measured_wire_operator.
    assert (Hcompact : (2 ^ i * 1) * 2 ^ (n - i) = 2 ^ n).
    { rewrite Nat.mul_1_r. apply pow_two_split; lia. }
    assert (Hfull : (2 ^ i * 2) * 2 ^ (n - i) = 2 ^ (S n)).
    {
      replace ((2 ^ i * 2) * 2 ^ (n - i)) with
        ((2 ^ i * 2 ^ (n - i)) * 2) by nia.
      rewrite pow_two_split by lia.
      rewrite Nat.pow_succ_r by lia.
      nia.
    }
    transitivity (@Mmult ((2 ^ i * 2) * 2 ^ (n - i))
      ((2 ^ i * 1) * 2 ^ (n - i)) 1
      ((I (2 ^ i) ⊗ ket (if b then 1 else 0)) ⊗ I (2 ^ (n - i)))
      (f_to_vec i f ⊗
        (ket (if f i then 1 else 0) ⊗
          f_to_vec (n - 1 - i) (shift f (S i))))).
    + symmetry.
      exact (@Mmult_change_dims
        ((2 ^ i * 2) * 2 ^ (n - i)) (2 ^ (S n))
        ((2 ^ i * 1) * 2 ^ (n - i)) (2 ^ n) 1 1
        ((I (2 ^ i) ⊗ ket (if b then 1 else 0)) ⊗ I (2 ^ (n - i)))
        (f_to_vec i f ⊗
          (ket (if f i then 1 else 0) ⊗
            f_to_vec (n - 1 - i) (shift f (S i))))
        Hfull Hcompact eq_refl).
    + assert (Htail_dim : 2 ^ (n - i) = 2 * 2 ^ (n - 1 - i)).
      { replace (n - i) with (S (n - 1 - i)) by lia.
        rewrite (Nat.pow_succ_r 2 (n - 1 - i) ltac:(lia)); reflexivity. }
      rewrite Htail_dim.
      transitivity
        ((@Mmult (2 ^ i * 2) (2 ^ i * 1) 1
            (I (2 ^ i) ⊗ ket (if b then 1 else 0)) (f_to_vec i f)) ⊗
         (@Mmult (2 * 2 ^ (n - 1 - i)) (2 * 2 ^ (n - 1 - i)) 1
            (I (2 * 2 ^ (n - 1 - i)))
            (ket (if f i then 1 else 0) ⊗
              f_to_vec (n - 1 - i) (shift f (S i))))).
      * exact (@kron_mixed_product'
          (2 ^ i * 2) (2 ^ i * 1) (2 ^ i) 1
          (2 * 2 ^ (n - 1 - i)) (2 * 2 ^ (n - 1 - i))
          (2 * 2 ^ (n - 1 - i)) 1
          ((2 ^ i * 2) * (2 * 2 ^ (n - 1 - i)))
          ((2 ^ i * 1) * (2 * 2 ^ (n - 1 - i))) 1
          (I (2 ^ i) ⊗ ket (if b then 1 else 0))
          (I (2 * 2 ^ (n - 1 - i)))
          (f_to_vec i f)
          (ket (if f i then 1 else 0) ⊗
            f_to_vec (n - 1 - i) (shift f (S i)))
          ltac:(rewrite Nat.mul_1_r; reflexivity) eq_refl eq_refl eq_refl eq_refl).
      * rewrite Hfirst, Mmult_1_l by auto with wf_db.
        replace (Nat.b2n b) with (if b then 1 else 0)
          by (destruct b; reflexivity).
        reflexivity.
Qed.

Lemma Hinsert_cnot_intertwine : forall n i c t b,
    i <= n -> c < n -> t < n -> c <> t ->
    @Mmult (2 ^ (S n)) (2 ^ n) (2 ^ n)
      (insert_measured_wire_operator n i b) (pad_ctrl n c t σx) =
    @Mmult (2 ^ (S n)) (2 ^ (S n)) (2 ^ n)
      (pad_ctrl (S n) (lift_measurement_index i c)
        (lift_measurement_index i t) σx)
      (insert_measured_wire_operator n i b).
Proof.
  intros n i c t b Hi Hc Ht Hct.
  apply equal_on_basis_states_implies_equal.
  - apply WF_mult.
    + unfold insert_measured_wire_operator; repeat apply WF_kron;
        auto with wf_db.
    + apply WF_pad_ctrl; apply WF_σx.
  - apply WF_mult.
    + apply WF_pad_ctrl; apply WF_σx.
    + unfold insert_measured_wire_operator; repeat apply WF_kron;
        auto with wf_db.
  - intros f.
    rewrite Mmult_assoc.
    rewrite Mmult_assoc.
    rewrite f_to_vec_cnot by lia.
    rewrite !Hinsert_measured_wire_f_to_vec by lia.
    rewrite (insert_measurement_bit_update f i b t
      (f t ⊕ f c)).
    assert (Hlift_c : lift_measurement_index i c < S n).
    { unfold lift_measurement_index; destruct (c <? i); lia. }
    assert (Hlift_t : lift_measurement_index i t < S n).
    { unfold lift_measurement_index; destruct (t <? i); lia. }
    assert (Hlift_ct : lift_measurement_index i c <> lift_measurement_index i t).
    {
      unfold lift_measurement_index.
      destruct (c <? i) eqn:Hci'; destruct (t <? i) eqn:Hti';
        apply Nat.ltb_lt in Hci' || apply Nat.ltb_ge in Hci';
        apply Nat.ltb_lt in Hti' || apply Nat.ltb_ge in Hti';
        simpl; congruence || lia.
    }
    rewrite f_to_vec_cnot by assumption.
    rewrite !insert_measurement_bit_at_lift_all.
    reflexivity.
Qed.

Lemma Hget_remove_and_reindex : forall
    (qm : finite_map qubit_reference (participant * fin))
    (measured : qubit_reference) index lq lpn,
    ~ In measured lq ->
    get_all_values qm lq = Some lpn ->
    get_all_values (remove_and_reindex_qubit_map qm measured index) lq =
      Some (map (fun owner_index =>
        (fst owner_index, shift_wire_index index (snd owner_index))) lpn).
Proof.
  intros qm measured index lq.
  remember (remove_and_reindex_qubit_map qm measured index) as qm' eqn:Hmap.
  induction lq as [|q lq IH]; intros lpn Hnot Hget.
  - simpl in Hget |- *. inversion Hget; reflexivity.
  - simpl in Hget |- *.
    destruct (qm q) as [[owner old_index]|] eqn:Hlookup; [|discriminate].
    destruct (get_all_values qm lq) as [values|] eqn:Htail;
      [|discriminate].
    inversion Hget; subst lpn.
    assert (Hneq : q <> measured).
    { intro Heq; subst q; apply Hnot; left; reflexivity. }
    assert (Hlookup' : qm' q = Some (owner,
        shift_wire_index index old_index)).
    { rewrite Hmap.
      exact (Hremove_lookup qm q measured index owner old_index Hneq Hlookup). }
    rewrite Hlookup'.
    rewrite (IH values).
    + reflexivity.
    + intros Hin; apply Hnot; right; exact Hin.
    + reflexivity.
Qed.

Lemma Hremove_lookup_inv : forall
    (qm : finite_map qubit_reference (participant * fin))
    (q measured : qubit_reference) (index : fin)
    (owner : participant) (new_index : fin),
    q <> measured ->
    remove_and_reindex_qubit_map qm measured index q = Some (owner, new_index) ->
    exists old_index, qm q = Some (owner, old_index) /\
      new_index = shift_wire_index index old_index.
Proof.
    intros qm q measured index owner new_index Hneq Hlookup.
    unfold remove_and_reindex_qubit_map, reindex_quantum_map in Hlookup.
    change (option_map (shift_qubit_index index)
      (delete (KEQ:=qr_dec) qm measured q) = Some (owner, new_index)) in Hlookup.
    rewrite delete_neq in Hlookup by congruence.
    destruct (qm q) as [[old_owner old_index]|] eqn:Hsource; simpl in Hlookup;
      try discriminate.
    inversion Hlookup; subst owner new_index.
    exists old_index; split; reflexivity.
Qed.

Lemma Hresult_vector : forall
    (qm : finite_map qubit_reference (participant * fin))
    (Hqm : quantum_map_wf qm)
    (sv : state_vector (Datatypes.length (elems qubit_reference (participant * fin) qm)))
    (Hsv : state_vector_wf sv) (dim : nat) (U : base_Unitary dim)
    (lq : list qubit_reference) (Hlq : Datatypes.length lq = dim)
    (Hdim : dim > 0) qs',
    apply_unitary qm Hqm sv Hsv U lq Hlq Hdim = Some qs' ->
    exists lpn,
      get_all_values qm lq = Some lpn /\
      exists (Hidx : Datatypes.length (map snd lpn) = dim /\
        NoDup (map snd lpn) /\
        Forall (fun i => i < Datatypes.length (elems qubit_reference (participant * fin) qm))
          (map snd lpn)),
      proj1_sig (projT2 qs') =
        @Mmult (2 ^ Datatypes.length (elems qubit_reference (participant * fin) qm))
          (2 ^ Datatypes.length (elems qubit_reference (participant * fin) qm)) 1
          (uc_eval (proj1_sig (@base_to_ucom _ _ U (map snd lpn) Hidx))) sv.
Proof.
    intros qm Hqm sv Hsv dim U lq Hlq Hdim qs' Happly.
    unfold apply_unitary in Happly.
    destruct (lt_dec 0 (Datatypes.length (elems qubit_reference (participant * fin) qm)))
      as [Hstate|Hstate]; [|discriminate].
    destruct (le_dec dim
      (Datatypes.length (elems qubit_reference (participant * fin) qm)))
      as [Hdimle|Hdimle]; [|discriminate].
    destruct (NoDup_dec (TEQ := qr_dec) lq) as [Hnd|Hnd]; [|discriminate].
    destruct (get_all_values_certified qm lq) as [cert|] eqn:Hcert; [|discriminate].
    cbn in Happly; inversion Happly; subst qs'.
    set (lpn := proj1_sig cert).
    set (Hidxs := apply_unitary_indexes_wf qm Hqm lq dim
      Hdim Hlq lpn Hnd (proj2_sig cert)).
    set (Hidx := conj (proj1 Hidxs)
      (conj (proj1 (proj2 Hidxs)) (proj1 (proj2 (proj2 Hidxs))))).
    exists lpn; split; [unfold lpn; exact (proj2_sig cert)|].
    exists Hidx.
    unfold apply_unitary_to_state; simpl.
    set (Hbase := Primitives.apply_unitary_to_state_obligation_2
      (Datatypes.length (elems qubit_reference (participant * fin) qm))
      dim Hdimle U (map snd lpn) Hidxs).
    assert (HbaseEq : Hbase = Hidx) by (unfold Hbase, Hidx; apply proof_irrelevance).
    rewrite HbaseEq; reflexivity.
Qed.

Lemma Happly_map : forall
    (qm : finite_map qubit_reference (participant * fin))
    (Hqm : quantum_map_wf qm)
    (sv : state_vector (Datatypes.length (elems qubit_reference (participant * fin) qm)))
    (Hsv : state_vector_wf sv) (dim : nat) (U : base_Unitary dim)
    (lq : list qubit_reference) (Hlq : Datatypes.length lq = dim)
    (Hdim : dim > 0) qs',
    apply_unitary qm Hqm sv Hsv U lq Hlq Hdim = Some qs' ->
    proj1_sig (projT1 qs') = qm.
Proof.
    intros qm Hqm sv Hsv dim U lq Hlq Hdim qs' Happly.
    unfold apply_unitary in Happly.
    destruct (lt_dec 0 (Datatypes.length (elems qubit_reference (participant * fin) qm)))
      as [Hstate|Hstate]; [|discriminate].
    destruct (le_dec dim
      (Datatypes.length (elems qubit_reference (participant * fin) qm)))
      as [Hdimle|Hdimle]; [|discriminate].
    destruct (NoDup_dec (TEQ := qr_dec) lq) as [Hnd|Hnd]; [|discriminate].
    destruct (get_all_values_certified qm lq) as [cert|] eqn:Hcert; [|discriminate].
    cbn in Happly; inversion Happly; reflexivity.
Qed.

Lemma Happly_exists : forall
    (qm : finite_map qubit_reference (participant * fin))
    (Hqm : quantum_map_wf qm)
    (sv : state_vector (Datatypes.length (elems qubit_reference (participant * fin) qm)))
    (Hsv : state_vector_wf sv) (dim : nat) (U : base_Unitary dim)
    (lq : list qubit_reference) (Hlq : Datatypes.length lq = dim)
    (Hdim : dim > 0),
    dim <= Datatypes.length (elems qubit_reference (participant * fin) qm) ->
    NoDup lq ->
    (exists owner, Forall (fun q => exists n, qm q = Some (owner, n)) lq) ->
    exists qs', apply_unitary qm Hqm sv Hsv U lq Hlq Hdim = Some qs'.
Proof.
    intros qm Hqm sv Hsv dim U lq Hlq Hdim Hsize Hnd [owner Howned].
    assert (Hget : exists vs, get_all_values qm lq = Some vs).
    {
      apply get_all_values_some_of_lookups.
      intros q Hin.
      apply Forall_forall with (x := q) in Howned; [|exact Hin].
      destruct Howned as [n Hlookup]. eauto.
    }
    destruct Hget as [vs Hget].
    assert (Hcert : exists cert, get_all_values_certified qm lq = Some cert).
    {
      unfold get_all_values_certified. rewrite Hget. eexists; reflexivity.
    }
    destruct Hcert as [cert Hcert].
    unfold apply_unitary.
    destruct (lt_dec 0 (Datatypes.length (elems qubit_reference (participant * fin) qm)))
      as [Hpositive|Hpositive]; [|lia].
    destruct (le_dec dim
      (Datatypes.length (elems qubit_reference (participant * fin) qm)))
      as [Hle|Hle]; [|lia].
    destruct (NoDup_dec (TEQ := qr_dec) lq) as [Hnd'|Hnd']; [|contradiction].
    destruct (get_all_values_certified qm lq) as [cert'|] eqn:Hcert'.
    - eexists; reflexivity.
    - rewrite Hcert in Hcert'; discriminate.
Qed.

Lemma Happly_size : forall
    (qm : finite_map qubit_reference (participant * fin))
    (Hqm : quantum_map_wf qm)
    (sv : state_vector (Datatypes.length (elems qubit_reference (participant * fin) qm)))
    (Hsv : state_vector_wf sv) (dim : nat) (U : base_Unitary dim)
    (lq : list qubit_reference) (Hlq : Datatypes.length lq = dim)
    (Hdim : dim > 0) qs',
    apply_unitary qm Hqm sv Hsv U lq Hlq Hdim = Some qs' ->
    dim <= Datatypes.length (elems qubit_reference (participant * fin) qm).
Proof.
    intros qm Hqm sv Hsv dim U lq Hlq Hdim qs' Happly.
    unfold apply_unitary in Happly.
    destruct (lt_dec 0 (Datatypes.length (elems qubit_reference (participant * fin) qm)))
      as [Hpositive|Hpositive]; [|discriminate].
    destruct (le_dec dim
      (Datatypes.length (elems qubit_reference (participant * fin) qm)))
      as [Hsize|Hsize]; [exact Hsize|discriminate].
Qed.

(* Package the state-level work for the gate/measurement branch of
   multistep_should_swap_no_newq.  Keeping the extraction of the gate's wire
   indices and the measurement norm argument here makes that branch smaller
   and avoids repeating this proof in the operational case split. *)
Lemma Hunitary_measurement_branch_setup : forall
    (qm : finite_map qubit_reference (participant * fin))
    (Hqm : quantum_map_wf qm)
    (sv : state_vector (Datatypes.length
      (elems qubit_reference (participant * fin) qm)))
    (Hsv : state_vector_wf sv)
    (lq : list qubit_reference)
    (U : base_Unitary (Datatypes.length lq))
    (Hdim : Datatypes.length lq > 0) (qs_after : quantum_state)
    (q : qubit_reference) (measured_owner gate_owner : participant)
    (index : fin) (result : bool),
    apply_unitary qm Hqm sv Hsv U lq eq_refl Hdim = Some qs_after ->
    Forall (fun qi => exists i, qm qi = Some (gate_owner, i)) lq ->
    qm q = Some (measured_owner, index) ->
    measured_owner <> gate_owner ->
    norm (proj index
      (Datatypes.length (elems qubit_reference (participant * fin) qm))
      result × proj1_sig (projT2 qs_after)) <> 0%R ->
    proj1_sig (projT1 qs_after) = qm /\
    exists lpn,
      get_all_values qm lq = Some lpn /\
      exists (Hidx : Datatypes.length (map snd lpn) = Datatypes.length lq /\
        NoDup (map snd lpn) /\
        Forall (fun i => i < Datatypes.length
          (elems qubit_reference (participant * fin) qm)) (map snd lpn)),
        (forall i, In i (map snd lpn) -> index <> i) /\
        proj1_sig (projT2 qs_after) =
          @Mmult (2 ^ Datatypes.length
              (elems qubit_reference (participant * fin) qm))
            (2 ^ Datatypes.length
              (elems qubit_reference (participant * fin) qm)) 1
            (uc_eval (proj1_sig
              (@base_to_ucom _ _ U (map snd lpn) Hidx))) sv /\
        norm (proj index
          (Datatypes.length (elems qubit_reference (participant * fin) qm))
          result × sv) =
        norm (proj index
          (Datatypes.length (elems qubit_reference (participant * fin) qm))
          result × (uc_eval (proj1_sig
            (@base_to_ucom _ _ U (map snd lpn) Hidx)) × sv)) /\
        norm (proj index
          (Datatypes.length (elems qubit_reference (participant * fin) qm))
          result × sv) <> 0%R /\
        (norm (proj index
          (Datatypes.length (elems qubit_reference (participant * fin) qm))
          result × sv) ^ 2)%R =
        (norm (proj index
          (Datatypes.length (elems qubit_reference (participant * fin) qm))
          result × (uc_eval (proj1_sig
            (@base_to_ucom _ _ U (map snd lpn) Hidx)) × sv)) ^ 2)%R.
Proof.
  intros qm Hqm sv Hsv lq U Hdim qs_after q measured_owner gate_owner
    index result Happly Howners Hlookup Howners_neq Hnonzero_after.
  pose proof (Happly_map qm Hqm sv Hsv (Datatypes.length lq) U lq
    eq_refl Hdim qs_after Happly) as Hmap_after.
  cbn in Hmap_after.
  split; [exact Hmap_after|].
  assert (Hq_not_in_lq : ~ In q lq).
  {
    eapply Hqubit_not_in_list_owned_by_other; eauto.
  }
  destruct (Hresult_vector qm Hqm sv Hsv (Datatypes.length lq) U lq
    eq_refl Hdim qs_after Happly) as [lpn [Hget [Hidx Hvec]]].
  assert (Hindex_disjoint : forall i, In i (map snd lpn) -> index <> i).
  {
    intros i Hi.
    apply in_map_iff in Hi as [[owner' idx] [Hidxi Hin_values]].
    simpl in Hidxi; subst i.
    destruct (Hget_value qm lq lpn owner' idx Hget Hin_values)
      as [qi [Hin_qi Hlookup_qi]].
    rewrite Forall_forall in Howners.
    destruct (Howners qi Hin_qi) as [idx' Howned].
    change (qm qi = Some (gate_owner, idx')) in Howned.
    rewrite Hlookup_qi in Howned.
    inversion Howned; subst owner' idx'.
    exact (@Hindex_unique qm Hqm q qi measured_owner gate_owner
      index idx Hlookup Hlookup_qi Howners_neq).
  }
  pose proof (@Hproj_base_norm
    (Datatypes.length (elems qubit_reference (participant * fin) qm))
    (Datatypes.length lq) U (map snd lpn) Hidx index result
    sv Hsv Hindex_disjoint) as Hnorm_gate.
  pose proof Hnonzero_after as Hnonzero_after_gate.
  rewrite Hvec in Hnonzero_after_gate.
  cbn in Hnonzero_after_gate.
  assert (Hnonzero_before_gate :
    norm (proj index
      (Datatypes.length (elems qubit_reference (participant * fin) qm))
      result × sv) <> 0%R).
  {
    intro Hzero.
    apply Hnonzero_after_gate.
    rewrite Hnorm_gate; exact Hzero.
  }
  assert (Hprobability_gate :
    (norm (proj index
      (Datatypes.length (elems qubit_reference (participant * fin) qm))
      result × sv) ^ 2)%R =
    (norm (proj index
      (Datatypes.length (elems qubit_reference (participant * fin) qm))
      result × (uc_eval (proj1_sig
        (@base_to_ucom (Datatypes.length
          (elems qubit_reference (participant * fin) qm))
          (Datatypes.length lq) U (map snd lpn) Hidx)) × sv)) ^ 2)%R).
  { rewrite Hnorm_gate; reflexivity. }
  exists lpn; split; [exact Hget|].
  exists Hidx.
  split; [exact Hindex_disjoint|].
  split; [exact Hvec|].
  split; [symmetry; exact Hnorm_gate|].
  split; [exact Hnonzero_before_gate|].
  exact Hprobability_gate.
Qed.

Lemma normalize_removed_wire_positive : forall n (v : state_vector n),
    0 < n -> normalize_removed_wire v =
      (1 / @norm (2 ^ n) v)%R .* v.
Proof.
  intros [|n] v Hn; [lia|reflexivity].
Qed.

Definition remove_measured_wire_operator_full
    (total remaining index : nat) (result : bool)
    (Htotal : total = S remaining) : Matrix (2 ^ remaining) (2 ^ total) :=
  eq_rect (2 ^ (S remaining))
    (fun cols => Matrix (2 ^ remaining) cols)
    (remove_measured_wire_operator remaining index result)
    (2 ^ total) (f_equal (fun n => 2 ^ n) (eq_sym Htotal)).

Lemma remove_measured_wire_operator_full_apply : forall
    total remaining index result (Htotal : total = S remaining)
    (v : state_vector total),
    @Mmult (2 ^ remaining) (2 ^ total) 1
      (remove_measured_wire_operator_full total remaining index result Htotal)
      v =
    @Mmult (2 ^ remaining) (2 ^ (S remaining)) 1
      (remove_measured_wire_operator remaining index result)
      (transport_state_vector Htotal v).
Proof.
  intros total remaining index result Htotal v.
  dependent destruction Htotal.
  unfold remove_measured_wire_operator_full.
  cbn [eq_sym f_equal eq_rect].
  reflexivity.
Qed.

Definition insert_measured_wire_operator_full
    (total remaining index : nat) (result : bool)
    (Htotal : total = S remaining) : Matrix (2 ^ total) (2 ^ remaining) :=
  eq_rect (2 ^ (S remaining))
    (fun rows => Matrix rows (2 ^ remaining))
    (insert_measured_wire_operator remaining index result)
    (2 ^ total) (f_equal (fun n => 2 ^ n) (eq_sym Htotal)).

Lemma remove_insert_measured_wire_operator_full : forall
    total remaining index result (Htotal : total = S remaining),
    index <= remaining ->
    @Mmult (2 ^ remaining) (2 ^ total) (2 ^ remaining)
      (remove_measured_wire_operator_full total remaining index result Htotal)
      (insert_measured_wire_operator_full total remaining index result Htotal) =
    I (2 ^ remaining).
Proof.
  intros total remaining index result Htotal Hindex.
  dependent destruction Htotal.
  cbn [remove_measured_wire_operator_full insert_measured_wire_operator_full
    eq_rect f_equal].
  apply remove_insert_measured_wire_operator; exact Hindex.
Qed.

Lemma insert_remove_measured_wire_operator_full : forall
    total remaining index result (Htotal : total = S remaining),
    index <= remaining ->
    @Mmult (2 ^ total) (2 ^ remaining) (2 ^ total)
      (insert_measured_wire_operator_full total remaining index result Htotal)
      (remove_measured_wire_operator_full total remaining index result Htotal) =
    proj index total result.
Proof.
  intros total remaining index result Htotal Hindex.
  dependent destruction Htotal.
  cbn [remove_measured_wire_operator_full insert_measured_wire_operator_full
    eq_rect f_equal].
  apply insert_remove_measured_wire_operator; exact Hindex.
Qed.

Lemma remove_measured_wire_operator_full_wf : forall
    total remaining index result (Htotal : total = S remaining),
    index <= remaining ->
    @WF_Matrix (2 ^ remaining) (2 ^ total)
      (remove_measured_wire_operator_full total remaining index result Htotal).
Proof.
  intros total remaining index result Htotal Hindex.
  dependent destruction Htotal.
  cbn [remove_measured_wire_operator_full eq_rect f_equal].
  apply remove_measured_wire_operator_wf; exact Hindex.
Qed.

Lemma Hnormalized_inserted_gate_commute : forall m n
    (A : Square m) (B : Square n) (P : Square m) (sv : Vector m)
    (remove_wire : Vector m -> Vector n)
    (insert_wire : Vector n -> Vector m),
    insert_wire (remove_wire (P × sv)) = P × sv ->
    insert_wire (B × remove_wire (P × sv)) =
      A × insert_wire (remove_wire (P × sv)) ->
    remove_wire (insert_wire (B × remove_wire (P × sv))) =
      B × remove_wire (P × sv) ->
    P × (A × sv) = A × (P × sv) ->
    norm (B × remove_wire (P × sv)) = norm (remove_wire (P × sv)) ->
    (1 / norm (remove_wire (P × (A × sv))))%R .*
        remove_wire (P × (A × sv)) =
      B × ((1 / norm (remove_wire (P × sv)))%R .*
        remove_wire (P × sv)).
Proof.
  intros m n A B P sv remove_wire insert_wire Hinsert_projector
    Hinsert_gate Hremove_insert_gate Hprojector_gate Hnorm_gate.
  set (v := remove_wire (P × sv)).
  assert (Hvector : remove_wire (P × (A × sv)) = B × v).
  {
    rewrite Hprojector_gate.
    rewrite <- Hinsert_projector at 1.
    rewrite <- Hinsert_gate at 1.
    rewrite Hremove_insert_gate.
    reflexivity.
  }
  rewrite Hvector.
  unfold v.
  rewrite Hnorm_gate.
  symmetry; apply Mscale_mult_dist_r.
Qed.

Lemma Hinsert_base_to_ucom_intertwine_full : forall
    total remaining index gate_dim (U : base_Unitary gate_dim)
    (l0 l : list nat)
    (Hidx0 : length l0 = gate_dim /\ NoDup l0 /\
      Forall (fun i => i < remaining) l0)
    (Hidx : length l = gate_dim /\ NoDup l /\
      Forall (fun i => i < total) l)
    result (Htotal : total = S remaining),
    index <= remaining ->
    l = map (fun wire => if wire <? index then wire else S wire) l0 ->
    @Mmult (2 ^ total) (2 ^ remaining) (2 ^ remaining)
      (insert_measured_wire_operator_full total remaining index result Htotal)
      (uc_eval (proj1_sig (@base_to_ucom remaining gate_dim U l0 Hidx0))) =
    @Mmult (2 ^ total) (2 ^ total) (2 ^ remaining)
      (uc_eval (proj1_sig (@base_to_ucom total gate_dim U l Hidx)))
      (insert_measured_wire_operator_full total remaining index result Htotal).
Proof.
  intros total remaining index gate_dim U l0 l Hidx0 Hidx result Htotal
    Hindex Hwirelist.
  dependent destruction Htotal.
  cbn [insert_measured_wire_operator_full eq_rect f_equal].
  dependent destruction U.
  - destruct Hidx0 as [Hlen0 [Hnd0 Hbounds0]].
    destruct Hidx as [Hlen [Hnd Hbounds]].
    destruct l0 as [|wire0 [|extra l0]]; simpl in Hlen0; try discriminate.
    destruct l as [|wire [|extra l]]; simpl in Hlen; try discriminate.
    inversion Hwirelist; subst.
    assert (Hwire0 : wire0 < remaining).
    { inversion Hbounds0; assumption. }
    assert (Hwire : (if wire0 <? index then wire0 else S wire0) < S remaining).
    { destruct (wire0 <? index) eqn:Hcmp;
        apply Nat.ltb_lt in Hcmp || apply Nat.ltb_ge in Hcmp; lia. }
    assert (Hfull : (2 ^ index * 2) * 2 ^ (remaining - index) = 2 ^ (S remaining)).
    {
      replace ((2 ^ index * 2) * 2 ^ (remaining - index))
        with ((2 ^ index * 2 ^ (remaining - index)) * 2) by lia.
      rewrite pow_two_split by exact Hindex. simpl; lia.
    }
    assert (Hcompact : (2 ^ index * 1) * 2 ^ (remaining - index) = 2 ^ remaining).
    { rewrite Nat.mul_1_r; apply pow_two_split; exact Hindex. }
    change
      (@Mmult (2 ^ (S remaining)) (2 ^ remaining) (2 ^ remaining)
        (insert_measured_wire_operator remaining index result)
        (ueval_r remaining wire0 (U_R r r0 r1)) =
       @Mmult (2 ^ (S remaining)) (2 ^ (S remaining)) (2 ^ remaining)
        (ueval_r (S remaining) (if wire0 <? index then wire0 else S wire0)
          (U_R r r0 r1))
        (insert_measured_wire_operator remaining index result)).
    rewrite (@Mmult_change_dims (2 ^ (S remaining))
      ((2 ^ index * 2) * 2 ^ (remaining - index))
      (2 ^ remaining) ((2 ^ index * 1) * 2 ^ (remaining - index))
      (2 ^ remaining) (2 ^ remaining)
      (insert_measured_wire_operator remaining index result)
      (ueval_r remaining wire0 (U_R r r0 r1))
      (eq_sym Hfull) (eq_sym Hcompact) eq_refl).
    rewrite (@Mmult_change_dims (2 ^ (S remaining))
      ((2 ^ index * 2) * 2 ^ (remaining - index))
      (2 ^ (S remaining)) ((2 ^ index * 2) * 2 ^ (remaining - index))
      (2 ^ remaining) (2 ^ remaining)
      (ueval_r (S remaining)
        (if wire0 <? index then wire0 else S wire0) (U_R r r0 r1))
      (insert_measured_wire_operator remaining index result)
      (eq_sym Hfull) (eq_sym Hfull) eq_refl).
    unfold ueval_r.
    exact (@Hinsert_pad_u_intertwine remaining index wire0 result
      (rotation r r0 r1) Hindex Hwire0 (WF_rotation r r0 r1)).
  -
    destruct Hidx0 as [Hlen0 [Hnd0 Hbounds0]].
    destruct Hidx as [Hlen [Hnd Hbounds]].
    destruct l0 as [|c [|t [|extra l0]]]; simpl in Hlen0; try discriminate.
    destruct l as [|c' [|t' [|extra l]]]; simpl in Hlen; try discriminate.
    simpl in Hwirelist.
    inversion Hwirelist; subst.
    pose proof Hbounds0 as Hbounds0forall.
    rewrite Forall_forall in Hbounds0forall.
    assert (Hc : c < remaining) by (apply Hbounds0forall; simpl; auto).
    assert (Ht : t < remaining) by (apply Hbounds0forall; simpl; auto).
    assert (Hc' : (if c <? index then c else S c) < S remaining).
    { destruct (c <? index) eqn:Hcmp;
        apply Nat.ltb_lt in Hcmp || apply Nat.ltb_ge in Hcmp; lia. }
    assert (Ht' : (if t <? index then t else S t) < S remaining).
    { destruct (t <? index) eqn:Hcmp;
        apply Nat.ltb_lt in Hcmp || apply Nat.ltb_ge in Hcmp; lia. }
    assert (Hct : c <> t).
    {
      apply NoDup_cons_iff in Hnd0 as [Hnotin _].
      intro Heq; subst t; apply Hnotin; now left.
    }
    assert (Hfull : (2 ^ index * 2) * 2 ^ (remaining - index) = 2 ^ (S remaining)).
    {
      replace ((2 ^ index * 2) * 2 ^ (remaining - index))
        with ((2 ^ index * 2 ^ (remaining - index)) * 2) by lia.
      rewrite pow_two_split by exact Hindex. simpl; lia.
    }
    assert (Hcompact : (2 ^ index * 1) * 2 ^ (remaining - index) = 2 ^ remaining).
    { rewrite Nat.mul_1_r; apply pow_two_split; exact Hindex. }
    change
      (@Mmult (2 ^ (S remaining)) (2 ^ remaining) (2 ^ remaining)
        (insert_measured_wire_operator remaining index result)
        (ueval_cnot remaining c t) =
       @Mmult (2 ^ (S remaining)) (2 ^ (S remaining)) (2 ^ remaining)
        (ueval_cnot (S remaining) (if c <? index then c else S c)
          (if t <? index then t else S t))
        (insert_measured_wire_operator remaining index result)).
    rewrite (@Mmult_change_dims (2 ^ (S remaining))
      ((2 ^ index * 2) * 2 ^ (remaining - index))
      (2 ^ remaining) ((2 ^ index * 1) * 2 ^ (remaining - index))
      (2 ^ remaining) (2 ^ remaining)
      (insert_measured_wire_operator remaining index result)
      (ueval_cnot remaining c t)
      (eq_sym Hfull) (eq_sym Hcompact) eq_refl).
    rewrite (@Mmult_change_dims (2 ^ (S remaining))
      ((2 ^ index * 2) * 2 ^ (remaining - index))
      (2 ^ (S remaining)) ((2 ^ index * 2) * 2 ^ (remaining - index))
      (2 ^ remaining) (2 ^ remaining)
      (ueval_cnot (S remaining) (if c <? index then c else S c)
        (if t <? index then t else S t))
      (insert_measured_wire_operator remaining index result)
      (eq_sym Hfull) (eq_sym Hfull) eq_refl).
    unfold ueval_cnot.
    pose proof (@Hinsert_cnot_intertwine remaining index c t result
      Hindex Hc Ht Hct) as Hcnot_intertwine.
    unfold lift_measurement_index in Hcnot_intertwine.
    rewrite (@Mmult_change_dims (2 ^ (S remaining))
      ((2 ^ index * 2) * 2 ^ (remaining - index))
      (2 ^ remaining) ((2 ^ index * 1) * 2 ^ (remaining - index))
      (2 ^ remaining) (2 ^ remaining)
      (insert_measured_wire_operator remaining index result)
      (pad_ctrl remaining c t σx)
      (eq_sym Hfull) (eq_sym Hcompact) eq_refl) in Hcnot_intertwine.
    rewrite (@Mmult_change_dims (2 ^ (S remaining))
      ((2 ^ index * 2) * 2 ^ (remaining - index))
      (2 ^ (S remaining)) ((2 ^ index * 2) * 2 ^ (remaining - index))
      (2 ^ remaining) (2 ^ remaining)
      (pad_ctrl (S remaining) (if c <? index then c else S c)
        (if t <? index then t else S t) σx)
      (insert_measured_wire_operator remaining index result)
      (eq_sym Hfull) (eq_sym Hfull) eq_refl) in Hcnot_intertwine.
    exact Hcnot_intertwine.
Qed.

Lemma proj_wire_dimension_irrelevant : forall n m index result,
    n = m -> proj index n result = proj index m result.
Proof. intros n m index result Hnm; destruct Hnm; reflexivity. Qed.

Lemma remove_measured_wire_operator_dimension_irrelevant : forall
    n m index result,
    n = m -> remove_measured_wire_operator n index result =
      remove_measured_wire_operator m index result.
Proof. intros n m index result Hnm; destruct Hnm; reflexivity. Qed.

Lemma measure_qubit_nonzero_full_vector : forall
    (qm : finite_map qubit_reference (participant * fin))
    (Hqm : quantum_map_wf qm)
    (sv : state_vector (Datatypes.length
      (elems qubit_reference (participant * fin) qm)))
    (Hsv : state_vector_wf sv)
    q owner index result (Hlookup : qm q = Some (owner, index))
    (Hlen : 0 < Datatypes.length
      (elems qubit_reference (participant * fin) qm))
    (Hnonzero : norm
      (proj index
        (Datatypes.length (elems qubit_reference (participant * fin) qm))
        result × sv) <> 0%R)
    (Htotal : Datatypes.length
      (elems qubit_reference (participant * fin) qm) =
      S (Datatypes.length (elems qubit_reference (participant * fin)
        (remove_and_reindex_qubit_map qm q index)))),
    proj1_sig (projT2 (snd
      (measure_qubit_nonzero qm Hqm sv Hsv q owner index result
        Hlookup Hlen Hnonzero))) =
    normalize_removed_wire
      (@Mmult
        (2 ^ Datatypes.length (elems qubit_reference (participant * fin)
          (remove_and_reindex_qubit_map qm q index)))
        (2 ^ Datatypes.length (elems qubit_reference (participant * fin) qm))
        1
        (remove_measured_wire_operator_full
          (Datatypes.length (elems qubit_reference (participant * fin) qm))
          (Datatypes.length (elems qubit_reference (participant * fin)
            (remove_and_reindex_qubit_map qm q index))) index result Htotal)
        (@Mmult
          (2 ^ Datatypes.length (elems qubit_reference (participant * fin) qm))
          (2 ^ Datatypes.length (elems qubit_reference (participant * fin) qm))
          1
          (proj index
            (Datatypes.length (elems qubit_reference (participant * fin) qm))
            result) sv)).
Proof.
  intros qm Hqm sv Hsv q owner index result Hlookup Hlen Hnonzero Htotal.
  set (n := Datatypes.length (elems qubit_reference (participant * fin) qm)).
  assert (Hremaining : Datatypes.length (elems qubit_reference
      (participant * fin) (remove_and_reindex_qubit_map qm q index)) =
      Nat.pred n).
  { unfold n. eapply remove_and_reindex_qubit_map_length; exact Hlookup. }
  unfold n in Hremaining.
  unfold measure_qubit_nonzero.
  cbn -[transport_state_vector normalize_removed_wire
    remove_measured_wire_operator_full remove_measured_wire_operator
    proj Mmult remove_and_reindex_qubit_map].
  rewrite FunctionalCorrectnessHelpers.transport_state_vector_value at 1.
  unfold remove_measured_wire.
  rewrite remove_measured_wire_operator_full_apply.
  pose proof (@transport_state_vector_proj _ _ Htotal index result sv)
    as Hprojected_transport.
  unfold n.
  rewrite Hprojected_transport.
  rewrite (FunctionalCorrectnessHelpers.transport_state_vector_value
    _ _ (eq_sym (Nat.succ_pred_pos
      (Datatypes.length (elems qubit_reference (participant * fin) qm)) Hlen)) sv).
  rewrite (FunctionalCorrectnessHelpers.transport_state_vector_value
    _ _ Htotal sv).
  rewrite (remove_measured_wire_operator_dimension_irrelevant
    (Nat.pred (Datatypes.length (elems qubit_reference (participant * fin) qm)))
    (Datatypes.length (elems qubit_reference (participant * fin)
      (remove_and_reindex_qubit_map qm q index))) index result
    (eq_sym Hremaining)).
  rewrite (proj_wire_dimension_irrelevant
    (S (Nat.pred (Datatypes.length (elems qubit_reference (participant * fin) qm))))
    (S (Datatypes.length (elems qubit_reference (participant * fin)
      (remove_and_reindex_qubit_map qm q index)))) index result
    (f_equal S (eq_sym Hremaining))).
  rewrite <- Hremaining.
  reflexivity.
Qed.

(* The quantum-state part of swapping a gate with a measurement on a
   disjoint owner.  The compact gate is reindexed after the measured wire is
   removed; the normalized post-measurement vector is then exactly the same
   as measuring after the full-space gate. *)
Lemma Hunitary_measurement_commute_state : forall
    (qm : finite_map qubit_reference (participant * fin))
    (Hqm : quantum_map_wf qm)
    (sv : state_vector (Datatypes.length
      (elems qubit_reference (participant * fin) qm)))
    (Hsv : state_vector_wf sv)
    (lq : list qubit_reference)
    (U : base_Unitary (Datatypes.length lq))
    (Hdim : Datatypes.length lq > 0) (qs_after : quantum_state)
    (q : qubit_reference) (measured_owner gate_owner : participant)
    (index : fin) (result : bool)
    (Happly : apply_unitary qm Hqm sv Hsv U lq eq_refl Hdim = Some qs_after)
    (Hnd : NoDup lq)
    (Howners : Forall
      (fun qi => exists i, qm qi = Some (gate_owner, i)) lq)
    (Hlookup_after : (` (projT1 qs_after)) q =
      Some (measured_owner, index))
    (Hlen_after : 0 < Datatypes.length
      (elems qubit_reference (participant * fin) (` (projT1 qs_after))))
    (Hnonzero_after : norm (proj index
      (Datatypes.length (elems qubit_reference (participant * fin)
        (` (projT1 qs_after)))) result × (` (projT2 qs_after))) <> 0%R)
    (Hlookup : qm q = Some (measured_owner, index))
    (Hlen : 0 < Datatypes.length
      (elems qubit_reference (participant * fin) qm))
    (Hnonzero_before : norm (proj index
      (Datatypes.length (elems qubit_reference (participant * fin) qm))
      result × sv) <> 0%R)
    (Howners_neq : measured_owner <> gate_owner),
    exists qs_reordered,
      let measured_before := measure_qubit_from_nonzero
        qm Hqm sv Hsv q measured_owner index result Hlookup Hlen Hnonzero_before in
      let measured_after := measure_qubit_from_nonzero
        (` (projT1 qs_after)) (proj2_sig (projT1 qs_after))
        (` (projT2 qs_after)) (proj2_sig (projT2 qs_after))
        q measured_owner index result Hlookup_after Hlen_after Hnonzero_after in
      apply_unitary
        (` (projT1 (snd measured_before)))
        (proj2_sig (projT1 (snd measured_before)))
        (` (projT2 (snd measured_before)))
        (proj2_sig (projT2 (snd measured_before)))
        U lq eq_refl Hdim = Some qs_reordered /\
      proj1_sig (projT1 qs_reordered) =
        proj1_sig (projT1 (snd measured_after)) /\
      proj1_sig (projT2 qs_reordered) =
        proj1_sig (projT2 (snd measured_after)) /\
      proj1_sig (fst measured_before) = proj1_sig (fst measured_after).
Proof.
  intros qm Hqm sv Hsv lq U Hdim qs_after q measured_owner gate_owner
    index result Happly Hnd Howners Hlookup_after Hlen_after Hnonzero_after
    Hlookup Hlen Hnonzero_before Howners_neq.
  pose proof (Happly_map qm Hqm sv Hsv (Datatypes.length lq) U lq
    eq_refl Hdim qs_after Happly) as Hmap_after.
  cbn in Hmap_after.
  assert (Hnonzero_after_source :
      norm (proj index
        (Datatypes.length (elems qubit_reference (participant * fin) qm))
        result × (` (projT2 qs_after))) <> 0%R).
  { rewrite <- Hmap_after; exact Hnonzero_after. }
  pose proof (@Hunitary_measurement_branch_setup qm Hqm sv Hsv lq U Hdim
    qs_after q measured_owner gate_owner index result Happly Howners Hlookup
    Howners_neq Hnonzero_after_source)
    as [Hmap_after_setup [lpn [Hget [Hidx [Hindex_disjoint
      [Hvec [Hnorm_before_gate [Hnonzero_before_gate Hprobability_gate]]]]]]]].
  set (measured_before := measure_qubit_from_nonzero
    qm Hqm sv Hsv q measured_owner index result Hlookup Hlen Hnonzero_before).
  set (measured_after := measure_qubit_from_nonzero
    (` (projT1 qs_after)) (proj2_sig (projT1 qs_after))
    (` (projT2 qs_after)) (proj2_sig (projT2 qs_after))
    q measured_owner index result Hlookup_after Hlen_after Hnonzero_after).
  set (qm0 := proj1_sig (projT1 (snd measured_before))).
  set (Hqm0 := proj2_sig (projT1 (snd measured_before))).
  set (sv0 := proj1_sig (projT2 (snd measured_before))).
  set (Hsv0 := proj2_sig (projT2 (snd measured_before))).
  assert (Hmap_before : qm0 = remove_and_reindex_qubit_map qm q index).
  {
    unfold qm0, measured_before.
    apply measure_qubit_nonzero_map.
  }
  assert (Hq_not_in_lq : ~ In q lq).
  {
    eapply Hqubit_not_in_list_owned_by_other; eauto.
  }
  assert (Howners0 : Forall
      (fun qi => exists i, qm0 qi = Some (gate_owner, i)) lq).
  {
    rewrite Forall_forall; intros qi Hin.
    rewrite Forall_forall in Howners.
    destruct (Howners qi Hin) as [old_index Hlookup_i].
    exists (shift_wire_index index old_index).
    rewrite Hmap_before.
    apply Hremove_lookup.
    - intro Heq; subst qi; apply Hq_not_in_lq; exact Hin.
    - exact Hlookup_i.
  }
  assert (Hqm0_length : Datatypes.length
      (elems qubit_reference (participant * fin) qm0) =
      Nat.pred (Datatypes.length
        (elems qubit_reference (participant * fin) qm))).
  {
    rewrite Hmap_before.
    eapply remove_and_reindex_qubit_map_length; exact Hlookup.
  }
  pose proof Hidx as Hidx_parts.
  destruct Hidx_parts as [Hlpn_length [Hlpn_nodup Hlpn_bounds]].
  assert (Hindex_lt : index < Datatypes.length
      (elems qubit_reference (participant * fin) qm)).
  {
    eapply quantum_map_lookup_index_lt; eauto.
  }
  assert (Hnd_with_measured : NoDup (index :: map snd lpn)).
  {
    constructor.
    - intro Hin.
      pose proof (Hindex_disjoint index Hin) as Hneq.
      congruence.
    - exact Hlpn_nodup.
  }
  assert (Hsubset : incl (index :: map snd lpn)
      (List.seq 0 (Datatypes.length
        (elems qubit_reference (participant * fin) qm)))).
  {
    intros i [Heq|Hin].
    - subst i; apply List.in_seq; split; [lia|exact Hindex_lt].
    - apply List.in_seq; split; [lia|].
      rewrite Forall_forall in Hlpn_bounds.
      apply Hlpn_bounds; exact Hin.
  }
  pose proof (@NoDup_incl_length nat (index :: map snd lpn)
    (List.seq 0 (Datatypes.length
      (elems qubit_reference (participant * fin) qm)))
    Hnd_with_measured Hsubset) as Hlength_bound.
  rewrite List.seq_length in Hlength_bound.
  simpl in Hlength_bound.
  rewrite Hlpn_length in Hlength_bound.
  assert (Hsize0 : Datatypes.length lq <=
      Datatypes.length (elems qubit_reference (participant * fin) qm0)).
  {
    rewrite Hqm0_length.
    simpl in Hlength_bound; lia.
  }
  destruct (Happly_exists qm0 Hqm0 sv0 Hsv0 (Datatypes.length lq) U lq
    eq_refl Hdim Hsize0 Hnd
    (ex_intro _ gate_owner Howners0)) as [qs_reordered Happly_reordered].
  destruct (Hresult_vector qm0 Hqm0 sv0 Hsv0 (Datatypes.length lq) U lq
    eq_refl Hdim qs_reordered Happly_reordered)
    as [lpn0 [Hget0 [Hidx0 Hvec0]]].
  pose proof (@Hget_remove_and_reindex qm q index lq lpn
    Hq_not_in_lq Hget) as Hget_shifted.
  rewrite <- Hmap_before in Hget_shifted.
  assert (Hlpn0 : lpn0 = map (fun owner_index =>
      (fst owner_index, shift_wire_index index (snd owner_index))) lpn).
  { congruence. }
  set (remaining := Datatypes.length
    (elems qubit_reference (participant * fin) qm0)).
  assert (Htotal : Datatypes.length
      (elems qubit_reference (participant * fin) qm) = S remaining).
  {
    unfold remaining.
    rewrite Hqm0_length.
    symmetry; apply Nat.succ_pred_pos; exact Hlen.
  }
  assert (Hindex_bound : index <= remaining).
  {
    pose proof (quantum_map_lookup_index_lt qm Hqm q measured_owner index
      Hlookup) as Hlt.
    rewrite Htotal in Hlt; lia.
  }
  assert (Hwirelist : map snd lpn =
      map (fun wire => if wire <? index then wire else S wire)
        (map snd lpn0)).
  {
    rewrite Hlpn0, !map_map.
    apply map_ext_in; intros [owner old_index] Hin; simpl.
    rewrite lift_shift_wire_index.
    - reflexivity.
    - intro Hbad.
      assert (Hinwire : In old_index (map snd lpn)).
      {
        apply in_map_iff.
        exists (owner, old_index); split; [reflexivity|exact Hin].
      }
      pose proof (Hindex_disjoint old_index Hinwire) as Hneq.
      apply Hneq; exact Hbad.
  }
  set (total := Datatypes.length
    (elems qubit_reference (participant * fin) qm)).
  set (A := uc_eval (proj1_sig (@base_to_ucom total
    (Datatypes.length lq) U (map snd lpn) Hidx))).
  set (B := uc_eval (proj1_sig (@base_to_ucom remaining
    (Datatypes.length lq) U (map snd lpn0) Hidx0))).
  set (P := proj index total result).
  set (remove_wire := fun v : Vector (2 ^ total) =>
    @Mmult (2 ^ remaining) (2 ^ total) 1
      (remove_measured_wire_operator_full total remaining index result
        Htotal) v).
  set (insert_wire := fun v : Vector (2 ^ remaining) =>
    @Mmult (2 ^ total) (2 ^ remaining) 1
      (insert_measured_wire_operator_full total remaining index result
        Htotal) v).
  assert (Hinsert_gate :
      insert_wire (B × remove_wire (P × sv)) =
      A × insert_wire (remove_wire (P × sv))).
  {
    unfold insert_wire, remove_wire, A, B.
    pose proof (@Hinsert_base_to_ucom_intertwine_full total remaining index
      (Datatypes.length lq) U (map snd lpn0) (map snd lpn)
      Hidx0 Hidx result Htotal Hindex_bound Hwirelist) as Hintertwine.
    rewrite <- Mmult_assoc, Hintertwine, Mmult_assoc.
    reflexivity.
  }
  assert (Hremove_insert_gate :
      remove_wire (insert_wire (B × remove_wire (P × sv))) =
      B × remove_wire (P × sv)).
  {
    unfold remove_wire, insert_wire.
    rewrite <- Mmult_assoc.
    rewrite remove_insert_measured_wire_operator_full by exact Hindex_bound.
    rewrite Mmult_1_l.
    - reflexivity.
    - unfold B; apply WF_mult.
      + exact (proj1 (proj2_sig (@base_to_ucom remaining
          (Datatypes.length lq) U (map snd lpn0) Hidx0))).
      + apply WF_mult.
        * apply remove_measured_wire_operator_full_wf; exact Hindex_bound.
        * apply WF_mult; [apply WF_proj|exact (proj1 Hsv)].
  }
  assert (Hprojector_gate :
    @Mmult (2 ^ total) (2 ^ total) 1 P
      (@Mmult (2 ^ total) (2 ^ total) 1 A sv) =
    @Mmult (2 ^ total) (2 ^ total) 1 A
      (@Mmult (2 ^ total) (2 ^ total) 1 P sv)).
  {
    unfold P, A, total.
    pose proof (@Hproj_base_commute
      (Datatypes.length (elems qubit_reference (participant * fin) qm))
      (Datatypes.length lq) U (map snd lpn) Hidx index result
      Hindex_disjoint) as Hcommute.
    transitivity (@Mmult
      (2 ^ Datatypes.length (elems qubit_reference (participant * fin) qm))
      (2 ^ Datatypes.length (elems qubit_reference (participant * fin) qm)) 1
      (@Mmult
        (2 ^ Datatypes.length (elems qubit_reference (participant * fin) qm))
        (2 ^ Datatypes.length (elems qubit_reference (participant * fin) qm))
        (2 ^ Datatypes.length (elems qubit_reference (participant * fin) qm))
        (proj index
          (Datatypes.length (elems qubit_reference (participant * fin) qm))
          result)
        (uc_eval (proj1_sig (@base_to_ucom
          (Datatypes.length (elems qubit_reference (participant * fin) qm))
          (Datatypes.length lq) U (map snd lpn) Hidx)))) sv).
    - symmetry.
      apply Mmult_assoc.
    - transitivity (@Mmult
        (2 ^ Datatypes.length (elems qubit_reference (participant * fin) qm))
        (2 ^ Datatypes.length (elems qubit_reference (participant * fin) qm)) 1
        (@Mmult
          (2 ^ Datatypes.length (elems qubit_reference (participant * fin) qm))
          (2 ^ Datatypes.length (elems qubit_reference (participant * fin) qm))
          (2 ^ Datatypes.length (elems qubit_reference (participant * fin) qm))
          (uc_eval (proj1_sig (@base_to_ucom
            (Datatypes.length (elems qubit_reference (participant * fin) qm))
            (Datatypes.length lq) U (map snd lpn) Hidx)))
          (proj index
            (Datatypes.length (elems qubit_reference (participant * fin) qm))
            result)) sv).
      + apply (f_equal (fun X : Square
          (2 ^ Datatypes.length (elems qubit_reference (participant * fin) qm)) =>
          @Mmult
            (2 ^ Datatypes.length (elems qubit_reference (participant * fin) qm))
            (2 ^ Datatypes.length (elems qubit_reference (participant * fin) qm))
            1 X sv)).
        exact Hcommute.
      + apply Mmult_assoc.
  }
  assert (Hnorm_gate_compact : norm (B × remove_wire (P × sv)) =
      norm (remove_wire (P × sv))).
  {
    unfold B, remove_wire.
    apply norm_unitary.
    - exact (proj2_sig (@base_to_ucom remaining
        (Datatypes.length lq) U (map snd lpn0) Hidx0)).
    - apply WF_mult.
      + apply remove_measured_wire_operator_full_wf; exact Hindex_bound.
      + apply WF_mult; [apply WF_proj|exact (proj1 Hsv)].
  }
  assert (Hinsert_projector :
      insert_wire (remove_wire (P × sv)) = P × sv).
  {
    unfold insert_wire, remove_wire.
    rewrite <- Mmult_assoc.
    rewrite insert_remove_measured_wire_operator_full by exact Hindex_bound.
    rewrite <- Mmult_assoc, proj_twice_eq.
    reflexivity.
  }
  assert (Hnormalized :
    (1 / norm (remove_wire (P × (A × sv))))%R .*
      remove_wire (P × (A × sv)) =
    B × ((1 / norm (remove_wire (P × sv)))%R .*
      remove_wire (P × sv))).
  {
    exact (@Hnormalized_inserted_gate_commute
      (2 ^ total) (2 ^ remaining) A B P sv remove_wire insert_wire
      Hinsert_projector Hinsert_gate Hremove_insert_gate Hprojector_gate
      Hnorm_gate_compact).
  }
  unfold measured_before, measured_after.
  exists qs_reordered.
  split.
  - exact Happly_reordered.
  - split.
    + pose proof (Happly_map qm0 Hqm0 sv0 Hsv0
        (Datatypes.length lq) U lq eq_refl Hdim qs_reordered
        Happly_reordered) as Hmap_reordered.
      cbn in Hmap_reordered.
      rewrite !measure_qubit_nonzero_map, Hmap_after_setup.
      exact Hmap_reordered.
    + split.
      * pose proof (@measure_qubit_nonzero_full_vector
          qm Hqm sv Hsv q measured_owner index result Hlookup Hlen
          Hnonzero_before Htotal) as Hvector_before.
        destruct qs_after as [[qm_after Hqm_after] [sv_after Hsv_after]].
        cbn in Hmap_after, Hvec, Hlookup_after, Hlen_after, Hnonzero_after.
        subst qm_after.
        subst qm0.
        assert (Htotal_removed : Datatypes.length
            (elems qubit_reference (participant * fin) qm) = S
            (Datatypes.length (elems qubit_reference (participant * fin)
              (remove_and_reindex_qubit_map qm q index)))).
        {
          unfold remaining in Htotal; exact Htotal.
        }
        pose proof (@measure_qubit_nonzero_full_vector
          qm Hqm sv_after Hsv_after q measured_owner index result
          Hlookup_after Hlen_after Hnonzero_after Htotal_removed)
          as Hvector_after.
        unfold remaining in Htotal.
        assert (Htotal_removed_eq : Htotal_removed = Htotal).
        { apply proof_irrelevance. }
        rewrite Htotal_removed_eq in Hvector_after.
        cbn in Hvec.
        assert (Hremaining_positive : 0 < remaining).
        {
          unfold remaining.
          lia.
        }
        change (sv0 = normalize_removed_wire
          (remove_wire (P × sv))) in Hvector_before.
        change (` (projT2 (snd measured_after)) =
          normalize_removed_wire (remove_wire (P × sv_after)))
          in Hvector_after.
        assert (Hvector_norm_after :
            normalize_removed_wire (remove_wire (P × sv_after)) =
            normalize_removed_wire (remove_wire (P × (A × sv)))).
        { rewrite Hvec; reflexivity. }
        rewrite Hvector_norm_after in Hvector_after.
        rewrite Hvector_before in Hvec0.
        pose proof (@normalize_removed_wire_positive remaining
          (remove_wire (P × sv)) Hremaining_positive) as Hnorm_before.
        rewrite Hnorm_before in Hvec0.
        pose proof (@normalize_removed_wire_positive remaining
          (remove_wire (P × (A × sv))) Hremaining_positive) as Hnorm_after.
        rewrite Hnorm_after in Hvector_after.
        change (` (projT2 qs_reordered) =
          ` (projT2 (snd measured_after))).
        rewrite Hvector_after.
        unfold B in Hnormalized.
        rewrite Hnormalized.
        exact Hvec0.
      * unfold measure_qubit_from_nonzero, measure_qubit_nonzero.
        cbn.
        assert (Hdim_after : Datatypes.length
            (elems qubit_reference (participant * fin) (` (projT1 qs_after))) =
            Datatypes.length (elems qubit_reference (participant * fin) qm)).
        { exact (f_equal (fun m => Datatypes.length
            (elems qubit_reference (participant * fin) m)) Hmap_after). }
        set (sv_after0 := ` (projT2 qs_after)).
        assert (Hnorm_after_source :
            norm (proj index
              (Datatypes.length (elems qubit_reference (participant * fin)
                (` (projT1 qs_after)))) result × sv_after0) =
            norm (proj index
              (Datatypes.length (elems qubit_reference (participant * fin) qm))
              result × (uc_eval (proj1_sig (@base_to_ucom
                (Datatypes.length (elems qubit_reference (participant * fin) qm))
                (Datatypes.length lq) U (map snd lpn) Hidx)) × sv))).
        {
          pose proof (@transport_state_vector_norm
            (Datatypes.length (elems qubit_reference (participant * fin)
              (` (projT1 qs_after))))
            (Datatypes.length (elems qubit_reference (participant * fin) qm))
            Hdim_after
            (proj index (Datatypes.length (elems qubit_reference
              (participant * fin) (` (projT1 qs_after)))) result × sv_after0))
            as Htransport_norm.
          rewrite <- Htransport_norm.
          rewrite (@transport_state_vector_proj
            (Datatypes.length (elems qubit_reference (participant * fin)
              (` (projT1 qs_after))))
            (Datatypes.length (elems qubit_reference (participant * fin) qm))
            Hdim_after index result sv_after0).
          rewrite (FunctionalCorrectnessHelpers.transport_state_vector_value
            _ _ Hdim_after sv_after0).
          unfold sv_after0.
          rewrite Hvec.
          reflexivity.
        }
        rewrite Hnorm_after_source.
        rewrite <- Hnorm_before_gate.
        rewrite !Rmult_1_r.
        reflexivity.
Qed.

Lemma swap_disjoint_unitary_steps : forall
    (name name0 : string) (s0 s'0 : session) (P P0 : process)
    (q_state1 q_state2 qstate : quantum_state)
    (lq lq0 : list qubit_reference)
    (U : base_Unitary (length lq))
    (U0 : base_Unitary (length lq0))
    (Hdim : length lq > 0) (Hdim0 : length lq0 > 0)
    (Happly1 : apply_unitary (` (projT1 q_state1))
      (proj2_sig (projT1 q_state1)) (` (projT2 q_state1))
      (proj2_sig (projT2 q_state1)) U lq eq_refl Hdim = Some q_state2)
    (Hproc1 : s0 (Pt name) = Some
      (p_unitary (length lq) U
        (map (fun z => Val (QVal z)) lq) P))
    (Hnd1 : NoDup lq)
    (Howners1 : Forall (fun q => exists n,
      (` (projT1 q_state1)) q = Some (Pt name, n)) lq)
    (Happly0 : apply_unitary (` (projT1 q_state2))
      (proj2_sig (projT1 q_state2)) (` (projT2 q_state2))
      (proj2_sig (projT2 q_state2)) U0 lq0 eq_refl Hdim0 = Some qstate)
    (Hproc0 : insert s0 (Pt name) P (Pt name0) = Some
      (p_unitary (length lq0) U0
        (map (fun z => Val (QVal z)) lq0) P0))
    (Hnd0 : NoDup lq0)
    (Howners0 : Forall (fun q => exists n,
      (` (projT1 q_state2)) q = Some (Pt name0, n)) lq0)
    (Hsession : unfoldM
      (insert (insert s0 (Pt name) P) (Pt name0) P0) s'0)
    (Hnames : name0 <> name)
    (Hparticipants : Pt name <> Pt name0),
    exists s'',
      multistep (q_state1, s0)
        (Tau (Pt name0) :: Tau (Pt name) :: nil) s'' (1 * (1 * 1)) /\
      equivalent_states (qstate, s'0) s''.
Proof.
  intros name name0 s0 s'0 P P0 q_state1 q_state2 qstate
    lq lq0 U U0 Hdim Hdim0 Happly1 Hproc1 Hnd1 Howners1
    Happly0 Hproc0 Hnd0 Howners0 Hsession Hnames Hparticipants.
  erewrite insert_neq in Hproc0; eauto.
  destruct q_state1 as [[qm Hqm] [sv Hsv]].
  destruct q_state2 as [[qm2 Hqm2] [sv2 Hsv2]].
  destruct qstate as [[qm3 Hqm3] [sv3 Hsv3]].
  cbn in Happly1, Happly0, Hproc1, Hproc0.
  pose proof (Happly_map qm Hqm sv Hsv (length lq) U lq eq_refl Hdim _ Happly1)
    as Hmap2.
  cbn in Hmap2.
  subst qm2.
  pose proof (Happly_map qm Hqm2 sv2 Hsv2 (length lq0) U0 lq0 eq_refl Hdim0 _ Happly0)
    as Hmap3.
  cbn in Hmap3.
  subst qm3.
  pose proof (Happly_size qm Hqm sv Hsv (length lq) U lq eq_refl Hdim _ Happly1)
    as Hsize.
  pose proof (Happly_size qm Hqm2 sv2 Hsv2 (length lq0) U0 lq0 eq_refl Hdim0 _ Happly0)
    as Hsize0.
  destruct (Hresult_vector qm Hqm sv Hsv (length lq) U lq eq_refl Hdim _ Happly1)
    as [lpn1 [Hget1 [Hidx1 Hvec1]]].
  destruct (Hresult_vector qm Hqm2 sv2 Hsv2 (length lq0) U0 lq0 eq_refl Hdim0 _ Happly0)
    as [lpn0 [Hget0 [Hidx0 Hvec2]]].
  destruct (Happly_exists qm Hqm sv Hsv (length lq0) U0 lq0 eq_refl Hdim0
    Hsize0 Hnd0 (ex_intro _ (Pt name0) Howners0)) as [qrev0 Hrev0].
  pose proof (Happly_map qm Hqm sv Hsv (length lq0) U0 lq0 eq_refl Hdim0
    _ Hrev0) as Hmaprev0.
  cbn in Hmaprev0.
  destruct qrev0 as [[qmrev Hqmrev] [svrev Hsvrev]].
  cbn in Hmaprev0.
  subst qmrev.
  pose (qrev0 := @existT
    ({x : finite_map qubit_reference (participant * fin) | quantum_map_wf x})
    (fun qm' =>
      {q : state_vector (length (elems qubit_reference (participant * fin) (`qm'))) |
        state_vector_wf q})
    (exist _ qm Hqmrev) (exist _ svrev Hsvrev)).
  destruct (Happly_exists qm Hqmrev svrev Hsvrev
    (length lq) U lq eq_refl Hdim Hsize Hnd1
    (ex_intro _ (Pt name) Howners1)) as [qrev1 Hrev1].
  pose proof (Happly_map qm Hqmrev svrev Hsvrev (length lq) U lq eq_refl Hdim
    _ Hrev1) as Hmaprev1.
  cbn in Hmaprev1.
  destruct qrev1 as [[qmrev1 Hqmrev1] [svrev1 Hsvrev1]].
  cbn in Hmaprev1.
  subst qmrev1.
  pose (qrev1 := @existT
    ({x : finite_map qubit_reference (participant * fin) | quantum_map_wf x})
    (fun qm' =>
      {q : state_vector (length (elems qubit_reference (participant * fin) (`qm'))) |
        state_vector_wf q})
    (exist _ qm Hqmrev1) (exist _ svrev1 Hsvrev1)).
  destruct (Hresult_vector qm Hqm sv Hsv (length lq0) U0 lq0 eq_refl Hdim0
    qrev0 Hrev0) as [lpn0' [Hget0' [Hidx0' Hvec0]]].
  destruct (Hresult_vector qm Hqmrev svrev Hsvrev
    (length lq) U lq eq_refl Hdim qrev1 Hrev1)
    as [lpn1' [Hget1' [Hidx1' Hvec3]]].
  assert (Hlpn0 : lpn0' = lpn0) by congruence.
  assert (Hlpn1 : lpn1' = lpn1) by congruence.
  subst lpn0'; subst lpn1'.
  assert (Hidx0eq : Hidx0' = Hidx0) by apply proof_irrelevance.
  assert (Hidx1eq : Hidx1' = Hidx1) by apply proof_irrelevance.
  rewrite Hidx0eq in Hvec0.
  rewrite Hidx1eq in Hvec3.
  set (op1 := uc_eval (proj1_sig (@base_to_ucom _ _ U (map snd lpn1) Hidx1))).
  set (op0 := uc_eval (proj1_sig (@base_to_ucom _ _ U0 (map snd lpn0) Hidx0))).
  assert (Hcomm : op1 × op0 = op0 × op1).
  {
    unfold op1, op0.
    eapply base_gates_commute_for_disjoint_owners with
      (owner1 := Pt name) (owner0 := Pt name0); eauto.
  }
  cbn in Hvec1, Hvec2, Hvec0, Hvec3.
  assert (Hvector : sv3 = svrev1).
  {
    rewrite Hvec2, Hvec1, Hvec3, Hvec0.
    rewrite <- Mmult_assoc.
    unfold op0, op1 in Hcomm.
    rewrite <- Hcomm, Mmult_assoc.
    reflexivity.
  }
  exists (qrev1, insert (insert s0 (Pt name0) P0) (Pt name) P).
  split.
  - eapply ms_step with (s2 := (qrev0, insert s0 (Pt name0) P0)).
    + eapply Unitary with (dim := length lq0) (p := Pt name0)
        (U := U0) (lq := lq0) (P := P0)
        (Hlen := eq_refl) (Hdim := Hdim0); eauto.
    + eapply ms_step with
        (s2 := (qrev1, insert (insert s0 (Pt name0) P0) (Pt name) P)).
      * eapply Unitary with (dim := length lq) (p := Pt name)
          (U := U) (lq := lq) (P := P)
          (Hlen := eq_refl) (Hdim := Hdim); eauto.
        rewrite insert_neq by congruence; exact Hproc1.
      * eapply ms_refl; apply equivalent_refl.
  - unfold equivalent_states; simpl.
    split.
    + eapply unfoldM_trans.
      * apply equivalent_unfoldM.
        apply equivalent_sym, insert_insert_comm; exact Hparticipants.
      * exact Hsession.
    + split.
      * apply equivalent_refl.
      * symmetry; exact Hvector.
Qed.

Lemma Hunfold_trans : forall M0 M1 M2,
    unfoldM M0 M1 -> unfoldM M1 M2 -> unfoldM M0 M2.
Proof.
    intros M0 M1 M2 H01 H12 pt.
    destruct (H01 pt) as [[Hnone0 Hnone1]|[P0 [P1 [Hmap0 [Hmap1 Hpre01]]]]].
    - destruct (H12 pt) as [[Hnone1' Hnone2]|[P1' [P2 [Hmap1' [Hmap2 Hpre12]]]]].
      + left; split; congruence.
      + rewrite Hnone1 in Hmap1'; discriminate.
    - destruct (H12 pt) as [[Hnone1' Hnone2]|[P1' [P2 [Hmap1' [Hmap2 Hpre12]]]]].
      + rewrite Hmap1 in Hnone1'; discriminate.
      + rewrite Hmap1 in Hmap1'; inversion Hmap1'; subst P1'.
        right; exists P0, P2; split; [exact Hmap0|].
        split; [exact Hmap2|]. eapply gttT; eauto.
Qed.

Lemma Hlookup_frame : forall M0 p P Msrc actor Pcur,
    p <> actor ->
    unfoldM (insert M0 p P) Msrc ->
    Msrc actor = Some Pcur ->
    exists Pbase, M0 actor = Some Pbase /\ precongP Pbase Pcur.
Proof.
    intros M0 p P Msrc actor Pcur Hneq Hsrc Hlookup.
    specialize (Hsrc actor).
    rewrite insert_neq in Hsrc by congruence.
    destruct Hsrc as [[Hbase Hsrc]|[Pbase [Psrc [Hbase [Hsrc Hpre]]]]].
    - rewrite Hlookup in Hsrc; discriminate.
    - rewrite Hlookup in Hsrc; inversion Hsrc; subst Psrc.
      exists Pbase; split; [exact Hbase|exact Hpre].
Qed.

Lemma Hunfold_other_process : forall Msrc Mdst actor Pdst,
    unfoldM Msrc Mdst -> Mdst actor = Some Pdst ->
    exists Psrc, Msrc actor = Some Psrc /\ precongP Psrc Pdst.
Proof.
    intros Msrc Mdst actor Pdst Hunfold Hlookup.
    specialize (Hunfold actor).
    destruct Hunfold as [[Hnone_src Hnone_dst]|[Psrc [Pmid [Hsrc [Hdst Hpre]]]]].
    - rewrite Hlookup in Hnone_dst; discriminate.
    - rewrite Hlookup in Hdst; inversion Hdst; subst Pmid.
      exists Psrc; auto.
Qed.

Lemma Hmake_unfold : forall (M0 : session) (actor : participant) Pbase Pcur,
    M0 actor = Some Pbase -> precongP Pbase Pcur ->
    unfoldM M0 (insert M0 actor Pcur).
Proof.
    intros M0 actor Pbase Pcur Hbase Hpre pt.
    destruct (participant_dec pt actor) as [Heq|Hneq].
    - subst pt. rewrite insert_eq.
      right; exists Pbase, Pcur; repeat split; eauto.
    - rewrite insert_neq by congruence.
      destruct (M0 pt) as [Ppt|] eqn:Hpt.
      + right; exists Ppt, Ppt; repeat split; eauto; constructor.
      + left; split; reflexivity.
Qed.

Lemma Hmake_target_unfold : forall (M0 : session) (actor : participant) Pcur Q,
    unfoldM (insert (insert M0 actor Pcur) actor Q)
      (insert M0 actor Q).
Proof.
    intros M0 actor Pcur Q pt.
    destruct (participant_dec pt actor) as [Heq|Hneq].
    - subst pt. rewrite !insert_eq.
      right; exists Q, Q; repeat split; eauto; constructor.
    - rewrite !insert_neq by congruence.
      destruct (M0 pt) as [Ppt|] eqn:Hpt.
      + right; exists Ppt, Ppt; repeat split; eauto; constructor.
      + left; split; reflexivity.
Qed.

Lemma Hinsert_frame : forall M0 Msrc p P actor Q,
    p <> actor ->
    unfoldM (insert M0 p P) Msrc ->
    unfoldM (insert (insert M0 actor Q) p P) (insert Msrc actor Q).
Proof.
    intros M0 Msrc p P actor Q Hneq Hsrc pt.
    destruct (participant_dec pt p) as [Hp|Hp].
    - subst pt. rewrite insert_eq.
      specialize (Hsrc p).
      rewrite insert_eq in Hsrc.
      destruct Hsrc as [[Hnone Hnone']|[Pbase [Pcur [Hbase [Hcur Hpre]]]]].
      + discriminate.
      + inversion Hbase; subst Pbase.
        right; exists P, Pcur; split.
        * reflexivity.
        * split.
          -- rewrite insert_neq by congruence; exact Hcur.
          -- exact Hpre.
    - destruct (participant_dec pt actor) as [Ha|Ha].
      + subst pt. rewrite insert_neq by congruence.
        rewrite !insert_eq. right; exists Q, Q; repeat split; eauto; constructor.
      + rewrite insert_neq by congruence.
        rewrite insert_neq by congruence.
        specialize (Hsrc pt).
        rewrite insert_neq in Hsrc by congruence.
        rewrite insert_neq by congruence; exact Hsrc.
Qed.

Lemma Hinsert_unfold : forall M0 Msrc p P,
    unfoldM M0 Msrc -> unfoldM (insert M0 p P) (insert Msrc p P).
Proof.
    intros M0 Msrc p P Hsrc pt.
    destruct (participant_dec pt p) as [Heq|Hneq].
    - subst pt; rewrite !insert_eq.
      right; exists P, P; repeat split; eauto; constructor.
    - rewrite !insert_neq by congruence.
      apply Hsrc.
Qed.

Lemma Hinsert_comm_unfold : forall M p P actor Q,
    p <> actor ->
    unfoldM (insert (insert M p P) actor Q)
      (insert (insert M actor Q) p P).
Proof.
    intros M p P actor Q Hneq.
    apply equivalent_unfoldM.
    apply insert_insert_comm; exact Hneq.
Qed.

Lemma Hinsert_same_frame : forall M p P Q,
    unfoldM (insert (insert M p P) p Q) (insert M p Q).
Proof.
    intros M p P Q pt.
    destruct (participant_dec pt p) as [Heq|Hneq].
    - subst pt; rewrite !insert_eq.
      right; exists Q, Q; repeat split; eauto; constructor.
    - rewrite !insert_neq by congruence.
      destruct (M pt) as [Ppt|] eqn:Hpt.
      + right; exists Ppt, Ppt; repeat split; eauto; constructor.
      + left; split; reflexivity.
Qed.

Lemma Hto_list_smap : forall A B (f : A -> B) (xs : slist A),
    to_list (smap f xs) = map f (to_list xs).
Proof.
    intros A B f xs; induction xs as [x|ox xs IH]; simpl.
    - reflexivity.
    - destruct ox; simpl; rewrite ?IH; reflexivity.
Qed.

Lemma Hfold_prop : forall (l : list Prop),
    fold_right and True l <-> Forall (fun P : Prop => P) l.
Proof.
    induction l as [|P l IH]; simpl.
    - split; [constructor|]. intros Hfold; inversion Hfold; constructor.
    split.
    - intros [HP Htail]; constructor; [exact HP|apply (proj1 IH); exact Htail].
    - intros Hforall; inversion Hforall; subst.
      split; [assumption|apply (proj2 IH); assumption].
Qed.

Lemma Hincr_no_newq : forall P fvP fvE m k,
    no_newq P -> no_newq (incr_free fvP fvE m k P).
Proof.
    intros P; induction P using process_deep_ind;
      intros fvP fvE m k Hnn; simpl in *.
    - constructor.
    - constructor.
    - eapply IHP; exact Hnn.
    - repeat rewrite Hto_list_smap in *.
      pose proof (proj1 (Hfold_prop _) Hnn) as HnnF.
      apply (proj2 (Hfold_prop _)).
      apply Forall_forall; intros Qprop HQ.
      apply in_map_iff in HQ as [Q' [HQprop HQ']].
      apply in_map_iff in HQ' as [Q [HQ' HQ0]].
      subst Qprop; subst Q'.
      assert (HnnQ : no_newq Q).
      { apply Forall_forall with (x := no_newq Q) in HnnF.
        - exact HnnF.
        - apply in_map; exact HQ0. }
      match goal with
      | [Hllp : SForall _ llp |- _] =>
          pose proof (proj2 (SForall_forall process
            (fun R => forall fvP fvE m k, no_newq R ->
              no_newq (incr_free fvP fvE m k R)) llp) Hllp) as Hforall
      end.
      apply In_to_list_onth in HQ0 as [i Hnth].
      specialize (Hforall i Q Hnth fvP (S fvE) m k HnnQ).
      exact Hforall.
    - destruct Hnn as [Hnn1 Hnn0].
      split; [eapply IHP1|eapply IHP2]; eauto.
    - eapply IHP; exact Hnn.
    - contradiction.
    - eapply IHP; exact Hnn.
    - eapply IHP; exact Hnn.
Qed.

Lemma Hsubst_no_newq : forall x m n P Q,
    no_newq P -> no_newq Q -> no_newq (substitutionP x m n P Q).
Proof.
    intros x m n P Q HnnP; revert x m n HnnP.
    induction Q using process_deep_ind;
      intros xsub msub nsub HnnP HnnQ; simpl in *.
    - destruct (Nat.ltb n xsub) eqn:Hlt; simpl.
      + constructor.
      + destruct (Nat.eqb n xsub) eqn:Heq; simpl.
        * eapply Hincr_no_newq; eauto.
        * constructor.
    - constructor.
    - eapply IHQ; eauto.
    - repeat rewrite Hto_list_smap in *.
      pose proof (proj1 (Hfold_prop _) HnnQ) as HnnF.
      apply (proj2 (Hfold_prop _)).
      apply Forall_forall; intros Qprop HQprop.
      apply in_map_iff in HQprop as [Q' [Heq HQ']].
      apply in_map_iff in HQ' as [Q [Heq' HQ0]].
      subst Qprop; subst Q'.
      assert (HnnQ' : no_newq Q).
      { apply Forall_forall with (x := no_newq Q) in HnnF.
        - exact HnnF.
        - apply in_map; exact HQ0. }
      match goal with
      | [Hllp : SForall _ llp |- _] =>
          pose proof (proj2 (SForall_forall process
            (fun R => forall x m n, no_newq P -> no_newq R ->
              no_newq (substitutionP x m n P R)) llp) Hllp) as Hforall
      end.
      apply In_to_list_onth in HQ0 as [i Hnth].
      specialize (Hforall i Q Hnth xsub msub (S nsub) HnnP HnnQ').
      exact Hforall.
    - destruct HnnQ as [Hnn1 Hnn0].
      split; [eapply IHQ1|eapply IHQ2]; eauto.
    - eapply IHQ; eauto.
    - contradiction.
    - eapply IHQ; eauto.
    - eapply IHQ; eauto.
Qed.

Lemma Hsubst_expr_no_newq : forall n d e P,
    no_newq P -> no_newq (subst_expression_in_process n d e P).
Proof.
    intros n d e P; revert n d e.
    induction P using process_deep_ind;
      intros nsub dsub esub Hnn; simpl in *.
    - constructor.
    - constructor.
    - eapply IHP; exact Hnn.
    - repeat rewrite Hto_list_smap in *.
      pose proof (proj1 (Hfold_prop _) Hnn) as HnnF.
      apply (proj2 (Hfold_prop _)).
      apply Forall_forall; intros Qprop HQprop.
      apply in_map_iff in HQprop as [Q' [Heq HQ']].
      apply in_map_iff in HQ' as [Q [Heq' HQ0]].
      subst Qprop; subst Q'.
      assert (HnnQ : no_newq Q).
      { apply Forall_forall with (x := no_newq Q) in HnnF.
        - exact HnnF.
        - apply in_map; exact HQ0. }
      match goal with
      | [Hllp : SForall _ llp |- _] =>
          pose proof (proj2 (SForall_forall process
            (fun R => forall n d e, no_newq R ->
              no_newq (subst_expression_in_process n d e R)) llp) Hllp) as Hforall
      end.
      apply In_to_list_onth in HQ0 as [i Hnth].
      specialize (Hforall i Q Hnth (S nsub) (S dsub) esub HnnQ).
      exact Hforall.
    - destruct Hnn as [Hnn1 Hnn0].
      split; [eapply IHP1|eapply IHP2]; eauto.
    - eapply IHP; exact Hnn.
    - contradiction.
    - eapply IHP; exact Hnn.
    - eapply IHP; exact Hnn.
Qed.

Lemma Hprecong_no_newq : forall P Q,
    precongP P Q -> no_newq P -> no_newq Q.
Proof.
    intros P Q Hpre; induction Hpre; intros Hnn.
    - exact Hnn.
    - simpl in Hnn.
      apply IHHpre.
      eapply Hsubst_no_newq; eauto.
    - apply IHHpre2, IHHpre1; exact Hnn.
Qed.

Lemma Hunfold_no_newq : forall M0 M1,
    unfoldM M0 M1 -> no_newq_session M0 -> no_newq_session M1.
Proof.
    intros M0 M1 Hunfold Hnn pt Q Hlookup.
    specialize (Hunfold pt).
    destruct Hunfold as [[Hnone0 Hnone1]|[P0 [P1 [Hmap0 [Hmap1 Hpre]]]]].
    - rewrite Hnone1 in Hlookup; discriminate.
    - rewrite Hmap1 in Hlookup; inversion Hlookup; subst Q.
      eapply Hprecong_no_newq; [exact Hpre|].
      eapply Hnn; exact Hmap0.
Qed.

Lemma Hinsert_no_newq : forall M p P,
    no_newq_session M -> no_newq P -> no_newq_session (insert M p P).
Proof.
    intros M p P Hnn Hproc pt Q Hlookup.
    destruct (participant_dec pt p) as [Heq|Hneq].
    - subst pt; rewrite insert_eq in Hlookup; inversion Hlookup; subst Q; exact Hproc.
    - rewrite insert_neq in Hlookup by congruence.
      eapply Hnn; exact Hlookup.
Qed.

Lemma Htau_preserves_no_newq : forall qs M0 Msrc actor qs' Mdst r,
    no_newq_session M0 ->
    unfoldM M0 Msrc ->
    step (qs, Msrc) (Tau actor) (qs', Mdst) r ->
    no_newq_session Mdst.
Proof.
    fix IH 10.
    intros qs M0 Msrc actor qs' Mdst r Hnn Hsrc Hstep.
    dependent destruction Hstep; simpl in *; try discriminate.
    - pose proof (Hunfold_no_newq _ _ Hsrc Hnn) as Hnn_src.
      pose proof (Hnn_src actor (p_newq P) H2) as Hbad.
      simpl in Hbad; contradiction.
    - pose proof (Hunfold_no_newq _ _ Hsrc Hnn) as Hnn_if0.
      pose proof (Hnn_if0 actor (p_ite e P1 P0) H2) as Hproc.
      simpl in Hproc; destruct Hproc as [_ Hproc].
      eapply Hinsert_no_newq; eauto.
    - pose proof (Hunfold_no_newq _ _ Hsrc Hnn) as Hnn_if1.
      pose proof (Hnn_if1 actor (p_ite e P1 P0) H2) as Hproc.
      simpl in Hproc; destruct Hproc as [Hproc _].
      eapply Hinsert_no_newq; eauto.
    - pose proof (Hunfold_no_newq _ _ Hsrc Hnn) as Hnn_meas.
      pose proof (Hnn_meas actor (p_measure (Val (QVal q)) P) H2) as Hproc.
      simpl in Hproc.
      assert (Hbody : no_newq
        (subst_expression_in_process 0 0 (Val (Bool r)) P)).
      { eapply Hsubst_expr_no_newq; exact Hproc. }
      eapply Hinsert_no_newq; eauto.
    - pose proof (Hunfold_no_newq _ _ Hsrc Hnn) as Hnn_unit.
      match goal with
      | [Hmap : ?M ?p = Some (p_unitary ?d ?U ?lqs ?P) |- _] =>
          pose proof (Hnn_unit p (p_unitary d U lqs P) Hmap) as Hproc
      end.
      simpl in Hproc.
      eapply Hinsert_no_newq; eauto.
    - pose proof (Hunfold_no_newq _ _ Hsrc Hnn) as Hnn_congr.
      pose proof (IH qs Msrc M1' actor qs' Mdst r Hnn_congr H2 Hstep)
        as Hnn_mid.
      exact Hnn_mid.
Qed.

End MultistepShouldSwapNoNewqHelpers.

Section MultistepShouldSwapNoNewqHelpers.
Context {a a0 : action} {s s' : state} {pi : R}
  (H : multistep s (a :: a0 :: nil) s' pi)
  (H0 : should_swap_no_newq a a0 = true)
  (H1 : no_newq_session (snd s)).

Lemma Htau_insert : forall qs M0 p P actor qs' Mdst r,
    p <> actor ->
    step (qs, M0) (Tau actor) (qs', Mdst) r ->
    exists Mdst',
      step (qs, insert M0 p P) (Tau actor) (qs', Mdst') r /\
      equivalent Mdst' (insert Mdst p P).
Proof.
    fix IH 10.
    intros qs M0 p P actor qs' Mdst r Hneq Hstep.
    dependent destruction Hstep; simpl in *; try discriminate.
    - exists (insert (insert M0 p P) actor
        (subst_expression_in_process 0 0 (Val (QVal q)) P0)).
      split.
      + eapply New with (Hfresh := Hfresh).
        rewrite insert_neq by congruence; exact H2.
      + eapply insert_insert_comm; exact Hneq.
    - exists (insert (insert M0 p P) actor P0). split.
      + eapply If_0.
        * rewrite insert_neq by congruence; exact H2.
        * exact H3.
      + eapply insert_insert_comm; exact Hneq.
    - exists (insert (insert M0 p P) actor P1). split.
      + eapply If_1.
        * rewrite insert_neq by congruence; exact H2.
        * exact H3.
      + eapply insert_insert_comm; exact Hneq.
    - exists (insert (insert M0 p P) actor
        (subst_expression_in_process 0 0 (Val (Bool r)) P0)).
      split.
      + set (measured := measure_qubit_from_nonzero
          (` (projT1 qs)) (proj2_sig (projT1 qs))
          (` (projT2 qs)) (proj2_sig (projT2 qs))
          q actor n r Hlookup Hlen Hnonzero).
        eapply Meas with (pi := fst measured) (q_state2 := snd measured).
        * rewrite insert_neq by congruence; exact H2.
        * unfold measured; reflexivity.
      + eapply insert_insert_comm; exact Hneq.
    - exists (insert (insert M0 p P) actor P0). split.
      + eapply Unitary; eauto.
        rewrite insert_neq by congruence; exact H2.
      + eapply insert_insert_comm; exact Hneq.
    - destruct (IH qs M1' p P actor qs' Mdst r Hneq Hstep)
        as [Mdst' [Hlift Htarget]].
      exists Mdst'. split; [|exact Htarget].
      eapply Congr with (M1' := insert M1' p P).
      + eapply unfoldM_insert; exact H2.
      + exact Hlift.
Qed.

Lemma Htau_other_process : forall qs Msrc actor qs' Mdst r p Pdst,
    p <> actor ->
    step (qs, Msrc) (Tau actor) (qs', Mdst) r ->
    Mdst p = Some Pdst ->
    exists Psrc, Msrc p = Some Psrc /\ precongP Psrc Pdst.
Proof.
    fix IH 10.
    intros qs Msrc actor qs' Mdst r p Pdst Hneq Hstep Hlookup.
    dependent destruction Hstep; simpl in *; try discriminate.
    - rewrite insert_neq in Hlookup by congruence.
      exists Pdst; split; [exact Hlookup|constructor].
    - rewrite insert_neq in Hlookup by congruence.
      exists Pdst; split; [exact Hlookup|constructor].
    - rewrite insert_neq in Hlookup by congruence.
      exists Pdst; split; [exact Hlookup|constructor].
    - exists Pdst.
      rewrite insert_neq in Hlookup0 by congruence.
      split; [exact Hlookup0|constructor].
    - rewrite insert_neq in Hlookup by congruence.
      exists Pdst; split; [exact Hlookup|constructor].
    - destruct (IH qs M1' actor qs' Mdst r p Pdst Hneq Hstep Hlookup)
        as [Pmid [HmapMid HpreIn]].
      specialize (H2 p).
      destruct H2 as [[HnoneSrc HnoneMid]|[Psrc [Pmid0 [HmapSrc [HmapMid0 HpreSrc]]]]].
      + rewrite HmapMid in HnoneMid; discriminate.
      + rewrite HmapMid in HmapMid0; inversion HmapMid0; subst Pmid0.
        exists Psrc; split; [exact HmapSrc|].
        eapply gttT; eassumption.
Qed.

Lemma Htau_frame : forall qs M0 p P Msrc actor qs' Mdst r,
    p <> actor ->
    unfoldM (insert M0 p P) Msrc ->
    step (qs, Msrc) (Tau actor) (qs', Mdst) r ->
    exists Q Mout,
      step (qs, M0) (Tau actor) (qs', Mout) r /\
      equivalent Mout (insert M0 actor Q) /\
      unfoldM (insert (insert M0 actor Q) p P) Mdst.
Proof.
    fix IH 12.
    intros qs M0 p P Msrc actor qs' Mdst r Hneq Hsrc Hstep.
    dependent destruction Hstep; simpl in *; try discriminate.
    - destruct (Hlookup_frame M0 p P Msrc actor (p_newq P0)
        Hneq Hsrc H2) as [Pbase [Hbase Hpre]].
      set (Mbase := insert M0 actor (p_newq P0)).
      set (Q := subst_expression_in_process 0 0 (Val (QVal q)) P0).
      exists Q, (insert Mbase actor Q). split.
      + eapply Congr with (M1' := Mbase).
        * unfold Mbase. eapply Hmake_unfold; eauto.
        * eapply New with (Hfresh := Hfresh).
          unfold Mbase; rewrite insert_eq; reflexivity.
      + split.
        * unfold Mbase, Q. apply insert_insert_noop.
        * eapply Hinsert_frame; eauto.
    - destruct (Hlookup_frame M0 p P Msrc actor (p_ite e P1 P0)
        Hneq Hsrc H2) as [Pbase [Hbase Hpre]].
      set (Mbase := insert M0 actor (p_ite e P1 P0)).
      exists P0, (insert Mbase actor P0). split.
      + eapply Congr with (M1' := Mbase).
        * unfold Mbase. eapply Hmake_unfold; eauto.
        * eapply If_0.
          -- unfold Mbase; rewrite insert_eq; reflexivity.
          -- exact H3.
      + split.
        * unfold Mbase. apply insert_insert_noop.
        * eapply Hinsert_frame; eauto.
    - destruct (Hlookup_frame M0 p P Msrc actor (p_ite e P1 P0)
        Hneq Hsrc H2) as [Pbase [Hbase Hpre]].
      set (Mbase := insert M0 actor (p_ite e P1 P0)).
      exists P1, (insert Mbase actor P1). split.
      + eapply Congr with (M1' := Mbase).
        * unfold Mbase. eapply Hmake_unfold; eauto.
        * eapply If_1.
          -- unfold Mbase; rewrite insert_eq; reflexivity.
          -- exact H3.
      + split.
        * unfold Mbase. apply insert_insert_noop.
        * eapply Hinsert_frame; eauto.
    - destruct (Hlookup_frame M0 p P Msrc actor
        (p_measure (Val (QVal q)) P0) Hneq Hsrc H2)
        as [Pbase [Hbase Hpre]].
      set (Mbase := insert M0 actor (p_measure (Val (QVal q)) P0)).
      set (Q := subst_expression_in_process 0 0 (Val (Bool r)) P0).
      exists Q, (insert Mbase actor Q).
      set (measured := measure_qubit_from_nonzero
        (` (projT1 qs)) (proj2_sig (projT1 qs))
        (` (projT2 qs)) (proj2_sig (projT2 qs))
        q actor n r Hlookup Hlen Hnonzero).
      split.
      + eapply Congr with (M1' := Mbase).
        * unfold Mbase. eapply Hmake_unfold; eauto.
        * eapply Meas with (pi := fst measured) (q_state2 := snd measured).
          -- unfold Mbase; rewrite insert_eq; reflexivity.
          -- unfold measured; reflexivity.
      + split.
        * unfold Mbase, Q. apply insert_insert_noop.
        * eapply Hinsert_frame; eauto.
    - destruct (Hlookup_frame M0 p P Msrc actor
        (p_unitary dim U (map (fun z => Val (QVal z)) lq) P0)
        Hneq Hsrc H2) as [Pbase [Hbase Hpre]].
      set (Mbase := insert M0 actor
        (p_unitary dim U (map (fun z => Val (QVal z)) lq) P0)).
      exists P0, (insert Mbase actor P0). split.
      + eapply Congr with (M1' := Mbase).
        * unfold Mbase. eapply Hmake_unfold; eauto.
        * eapply Unitary; eauto.
          unfold Mbase; rewrite insert_eq; reflexivity.
      + split.
        * unfold Mbase. apply insert_insert_noop.
        * eapply Hinsert_frame; eauto.
    - pose proof (Hunfold_trans _ _ _ Hsrc H2) as Hsrc'.
      destruct (IH qs M0 p P M1' actor qs' Mdst r Hneq Hsrc' Hstep)
        as [Q [Mout [Hnew [Hequiv Htarget]]]].
      exists Q, Mout; split; [exact Hnew|]. split; assumption.
Qed.

End MultistepShouldSwapNoNewqHelpers.

Transparent pairwise_sorted insert equivalent.
Close Scope C_scope.
Close Scope R_scope.

(* Merged from QGTPath1Helpers.v. *)
Module QGTPath1HelperDefinitions.
From SQIR Require Import SQIR UnitaryOps.
Require Import FunctionalCorrectnessHelpers.
Require Import Primitives.
Require Import FMap.
Require Import SST.
Require Import Lra Psatz Bool.
Local Open Scope R_scope.
Local Open Scope C_scope.

Definition qgt_branch_scalar (x y : bool) : Complex.C :=
  (if Bool.eqb x y then 1 - Ci else 1 + Ci) / (2 * sqrt 2).

Definition qgt_epr_preparation : Matrix 16 4 :=
  ((pad_ctrl 4 2 3 σx) × (pad_u 4 2 hadamard)) ×
    (I 4 ⊗ (ket 0 ⊗ ket 0)).

Definition qgt_final_correction : Matrix 16 16 :=
  (pad_u 4 1 (phase_shift (PI / 2))) ×
    pad_u 4 0 (phase_shift (PI / 2)).

Definition qgt_final_correction_dag : Matrix 16 16 :=
  (pad_u 4 1 (phase_shift (- PI / 2))) ×
    pad_u 4 0 (phase_shift (- PI / 2)).

Definition qgt_full_branch (x y : bool) : Matrix 16 4 :=
  qgt_final_correction ×
    (proj 3 4 y ×
      (bob_pre_measure_operator_four ×
        (proj 2 4 x ×
          (alice_pre_measure_operator_four × qgt_epr_preparation)))).

Lemma qgt_pad_h_ancilla :
  pad_u 4 2 hadamard = I 4 ⊗ (hadamard ⊗ I 2).
Proof.
  unfold pad_u, pad.
  bdestruct (2 + 1 <=? 4); [|lia].
  replace (2 ^ 2)%nat with 4%nat by reflexivity.
  replace (4 - (2 + 1))%nat with 1%nat by lia.
  simpl Nat.pow.
  apply kron_assoc; auto with wf_db.
Qed.

Lemma qgt_pad_cnot_ancilla :
  pad_ctrl 4 2 3 σx = I 4 ⊗ cnot.
Proof.
  unfold pad_ctrl, pad.
  bdestruct (2 <? 3); [|lia].
  replace (3 - 2 - 1)%nat with 0%nat by lia.
  simpl Nat.pow.
  bdestruct (2 + (1 + 0 + 1) <=? 4); [|lia].
  repeat rewrite kron_1_r by auto with wf_db.
  f_equal; apply cnot_decomposition.
Qed.

Lemma qgt_epr_preparation_factor :
  qgt_epr_preparation = I 4 ⊗ EPRpair.
Proof.
  unfold qgt_epr_preparation.
  rewrite qgt_pad_cnot_ancilla, qgt_pad_h_ancilla.
  change (@Mmult 16 16 4
    (@Mmult 16 16 16 (I 4 ⊗ cnot) (I 4 ⊗ (hadamard ⊗ I 2)))
    (I 4 ⊗ (ket 0 ⊗ ket 0)) = I 4 ⊗ EPRpair).
  assert (Hfirst :
    @Mmult 16 16 16 (I 4 ⊗ cnot) (I 4 ⊗ (hadamard ⊗ I 2)) =
    I 4 ⊗ (cnot × (hadamard ⊗ I 2))).
  {
    transitivity ((I 4 × I 4) ⊗ (cnot × (hadamard ⊗ I 2))).
    - exact (@kron_mixed_product 4 4 4 4 4 4
        (I 4) cnot (I 4) (hadamard ⊗ I 2)).
    - rewrite Mmult_1_l by auto with wf_db; reflexivity.
  }
  rewrite Hfirst.
  assert (Hsecond :
    @Mmult 16 16 4 (I 4 ⊗ (cnot × (hadamard ⊗ I 2)))
      (I 4 ⊗ (ket 0 ⊗ ket 0)) =
    I 4 ⊗ ((cnot × (hadamard ⊗ I 2)) × (ket 0 ⊗ ket 0))).
  {
    transitivity ((I 4 × I 4) ⊗
      ((cnot × (hadamard ⊗ I 2)) × (ket 0 ⊗ ket 0))).
    - exact (@kron_mixed_product 4 4 4 4 4 1
        (I 4) (cnot × (hadamard ⊗ I 2)) (I 4) (ket 0 ⊗ ket 0)).
    - rewrite Mmult_1_l by auto with wf_db; reflexivity.
  }
  rewrite Hsecond.
  rewrite EPRpair_creation.
  reflexivity.
Qed.

Lemma qgt_epr_preparation_input : forall (input : Matrix 4 1),
  WF_Matrix input ->
  pad_ctrl 4 2 3 σx ×
    (pad_u 4 2 hadamard × ((input ⊗ ket 0) ⊗ ket 0)) =
  qgt_epr_preparation × input.
Proof.
  intros input Hinput.
  assert (Hancillas :
    (I 4 ⊗ (ket 0 ⊗ ket 0)) × input =
      (input ⊗ ket 0) ⊗ ket 0).
  {
    replace input with (input ⊗ I 1) at 1.
    - transitivity ((I 4 × input) ⊗ ((ket 0 ⊗ ket 0) × I 1)).
      + exact (@kron_mixed_product 4 4 1 4 1 1 (I 4) (ket 0 ⊗ ket 0)
          input (I 1)).
      + rewrite Mmult_1_l by exact Hinput.
        rewrite Mmult_1_r by auto with wf_db.
        symmetry; rewrite kron_assoc by auto with wf_db; reflexivity.
    - rewrite kron_1_r by exact Hinput; reflexivity.
  }
  rewrite <- Hancillas.
  unfold qgt_epr_preparation.
  repeat rewrite Mmult_assoc.
  reflexivity.
Qed.

Lemma qgt_transport_pad_u : forall (n m : nat) (Hnm : n = m)
    (i : nat) (U : Matrix 2 2) (v : state_vector n),
  transport_state_vector Hnm
    (@Mmult (Nat.pow 2 n) (Nat.pow 2 n) 1 (pad_u n i U) v) =
  (@Mmult (Nat.pow 2 m) (Nat.pow 2 m) 1 (pad_u m i U)
    (transport_state_vector Hnm v)).
Proof. intros; destruct Hnm; reflexivity. Qed.

Lemma qgt_transport_pad_ctrl : forall (n m : nat) (Hnm : n = m)
    (i j : nat) (U : Matrix 2 2) (v : state_vector n),
  transport_state_vector Hnm
    (@Mmult (Nat.pow 2 n) (Nat.pow 2 n) 1 (pad_ctrl n i j U) v) =
  (@Mmult (Nat.pow 2 m) (Nat.pow 2 m) 1 (pad_ctrl m i j U)
    (transport_state_vector Hnm v)).
Proof. intros; destruct Hnm; reflexivity. Qed.

Lemma qgt_transport_state_vector_compose : forall (n m p : nat)
    (Hnm : n = m) (Hmp : m = p) (v : state_vector n),
  transport_state_vector (eq_trans Hnm Hmp) v =
    transport_state_vector Hmp (transport_state_vector Hnm v).
Proof. intros; destruct Hnm, Hmp; reflexivity. Qed.

Definition qgt_gap_ctrl (U : Matrix 2 2) : Matrix 8 8 :=
  Mplus (((ket 1 × bra 1) ⊗ I 2) ⊗ U)
    (((ket 0 × bra 0) ⊗ I 2) ⊗ I 2).

Lemma qgt_pad_h3 : pad_u 3 2 hadamard = I 4 ⊗ hadamard.
Proof.
  unfold pad_u, pad.
  bdestruct (2 + 1 <=? 3); [|lia].
  replace (2 ^ 2)%nat with 4%nat by reflexivity.
  replace (3 - (2 + 1))%nat with 0%nat by lia.
  simpl Nat.pow.
  rewrite kron_1_r by auto with wf_db.
  reflexivity.
Qed.

Lemma qgt_controlled_h_gap :
  pad_u 3 2 hadamard × qgt_gap_ctrl σx × pad_u 3 2 hadamard =
  qgt_gap_ctrl σz.
Proof.
  rewrite qgt_pad_h3.
  unfold qgt_gap_ctrl.
  rewrite Mmult_assoc.
  rewrite Mmult_plus_distr_r.
  rewrite Mmult_plus_distr_l.
  set (A1 := (ket 1 × bra 1) ⊗ I 2).
  set (A0 := (ket 0 × bra 0) ⊗ I 2).
  assert (Hhx : hadamard × (σx × hadamard) = σz).
  { rewrite <- Mmult_assoc, MmultHX, Mmult_assoc, MmultHH.
    rewrite Mmult_1_r by auto with wf_db; reflexivity. }
  assert (Hhih : hadamard × (I 2 × hadamard) = I 2).
  { rewrite Mmult_1_l by auto with wf_db.
    rewrite MmultHH; reflexivity. }
  assert (Hfirst :
    (I 4 ⊗ hadamard) × ((A1 ⊗ σx) × (I 4 ⊗ hadamard)) =
    A1 ⊗ σz).
  {
    assert (Hinner : (A1 ⊗ σx) × (I 4 ⊗ hadamard) =
        A1 ⊗ (σx × hadamard)).
    {
      transitivity ((A1 × I 4) ⊗ (σx × hadamard)).
      - exact (@kron_mixed_product 4 4 4 2 2 2 A1 σx (I 4) hadamard).
      rewrite Mmult_1_r by (unfold A1; repeat apply WF_kron; auto with wf_db); reflexivity.
    }
    rewrite Hinner.
    transitivity ((I 4 × A1) ⊗ (hadamard × (σx × hadamard))).
    - exact (@kron_mixed_product 4 4 4 2 2 2
        (I 4) hadamard A1 (σx × hadamard)).
    - rewrite Mmult_1_l by (unfold A1; repeat apply WF_kron; auto with wf_db).
      rewrite Hhx; reflexivity.
  }
  assert (Hsecond :
    (I 4 ⊗ hadamard) × ((A0 ⊗ I 2) × (I 4 ⊗ hadamard)) =
    A0 ⊗ I 2).
  {
    assert (Hinner : (A0 ⊗ I 2) × (I 4 ⊗ hadamard) =
        A0 ⊗ (I 2 × hadamard)).
    {
      transitivity ((A0 × I 4) ⊗ (I 2 × hadamard)).
      - exact (@kron_mixed_product 4 4 4 2 2 2 A0 (I 2) (I 4) hadamard).
      - rewrite Mmult_1_r by (unfold A0; repeat apply WF_kron; auto with wf_db); reflexivity.
    }
    rewrite Hinner.
    transitivity ((I 4 × A0) ⊗ (hadamard × (I 2 × hadamard))).
    - exact (@kron_mixed_product 4 4 4 2 2 2
        (I 4) hadamard A0 (I 2 × hadamard)).
    - rewrite Mmult_1_l by (unfold A0; repeat apply WF_kron; auto with wf_db).
      rewrite Hhih; reflexivity.
  }
  f_equal; assumption.
Qed.

Definition qgt_basis4 (a b c d : bool) : Matrix 16 1 :=
  f_to_vec 4 (fun i => match i with
    | 0%nat => a | 1%nat => b | 2%nat => c | _ => d end).

Definition qgt_basis3 (a b c : bool) : Matrix 8 1 :=
  f_to_vec 3 (fun i => match i with
    | 0%nat => a | 1%nat => b | _ => c end).

Lemma qgt_basis3_tensor : forall a b c,
  qgt_basis3 a b c = ket (if a then 1 else 0) ⊗
    ket (if b then 1 else 0) ⊗ ket (if c then 1 else 0).
Proof.
  intros a b c; unfold qgt_basis3.
  change (I 1 ⊗ ket (if a then 1 else 0) ⊗
    ket (if b then 1 else 0) ⊗ ket (if c then 1 else 0) =
    ket (if a then 1 else 0) ⊗ ket (if b then 1 else 0) ⊗
    ket (if c then 1 else 0)).
  rewrite kron_1_l by auto with wf_db.
  reflexivity.
Qed.

Lemma qgt_basis4_tensor : forall a b c d,
  qgt_basis4 a b c d =
    ket (if a then 1 else 0) ⊗ ket (if b then 1 else 0) ⊗
    ket (if c then 1 else 0) ⊗ ket (if d then 1 else 0).
Proof.
  intros a b c d.
  unfold qgt_basis4.
  change (I 1 ⊗ ket (if a then 1 else 0) ⊗ ket (if b then 1 else 0) ⊗
    ket (if c then 1 else 0) ⊗ ket (if d then 1 else 0) =
    ket (if a then 1 else 0) ⊗ ket (if b then 1 else 0) ⊗
    ket (if c then 1 else 0) ⊗ ket (if d then 1 else 0)).
  rewrite kron_1_l by auto with wf_db.
  reflexivity.
Qed.

Lemma qgt_epr_basis : forall (a b : bool),
  qgt_epr_preparation ×
    (ket (if a then 1 else 0) ⊗ ket (if b then 1 else 0)) =
  (ket (if a then 1 else 0) ⊗ ket (if b then 1 else 0)) ⊗ EPRpair.
Proof.
  intros a b.
  rewrite qgt_epr_preparation_factor.
  replace (ket (if a then 1 else 0) ⊗ ket (if b then 1 else 0)) with
    ((ket (if a then 1 else 0) ⊗ ket (if b then 1 else 0)) ⊗ I 1)
    at 1 by exact (@kron_1_r 4 1
      (ket (if a then 1 else 0) ⊗ ket (if b then 1 else 0))).
  transitivity ((I 4 × (ket (if a then 1 else 0) ⊗ ket (if b then 1 else 0))) ⊗
    (EPRpair × I 1)).
  - exact (@kron_mixed_product 4 4 1 4 1 1
      (I 4) EPRpair
      (ket (if a then 1 else 0) ⊗ ket (if b then 1 else 0)) (I 1)).
  - rewrite Mmult_1_l by auto with wf_db.
    rewrite Mmult_1_r by auto with wf_db.
    reflexivity.
Qed.


Lemma qgt_epr_input_basis : forall (a b : bool),
  qgt_epr_preparation ×
    (ket (if a then 1 else 0) ⊗ ket (if b then 1 else 0)) =
  / √ 2 .* (Mplus (qgt_basis4 a b false false) (qgt_basis4 a b true true)).
Proof.
  intros a b.
  rewrite qgt_epr_basis.
  unfold EPRpair.
  rewrite Mscale_kron_dist_r.
  rewrite kron_plus_distr_l.
  rewrite <- !kron_assoc by auto with wf_db.
  f_equal.
  f_equal.
  - symmetry; apply qgt_basis4_tensor.
  - symmetry; apply qgt_basis4_tensor.
Qed.

Lemma qgt_Cexp_PI : Cexp PI = -(C1 : Complex.C).
Proof.
  rewrite Cexp_PI.
  change (RtoC (-1)%R = - RtoC (1)%R).
  apply RtoC_opp.
Qed.

Lemma qgt_pad_h4_square :
  pad_u 4 2 hadamard × pad_u 4 2 hadamard = I 16.
Proof.
  rewrite !qgt_pad_h_ancilla.
  transitivity ((I 4 × I 4) ⊗
    ((hadamard ⊗ I 2) × (hadamard ⊗ I 2))).
  - exact (@kron_mixed_product 4 4 4 4 4 4
      (I 4) (hadamard ⊗ I 2) (I 4) (hadamard ⊗ I 2)).
  - rewrite Mmult_1_l by auto with wf_db.
    transitivity (I 4 ⊗ ((hadamard × hadamard) ⊗ (I 2 × I 2))).
    + f_equal.
      exact (@kron_mixed_product 2 2 2 2 2 2
        hadamard (I 2) hadamard (I 2)).
    + rewrite MmultHH.
      rewrite Mmult_1_l by auto with wf_db.
      rewrite id_kron.
      replace (2 * 2)%nat with 4%nat by reflexivity.
      rewrite id_kron; reflexivity.
Qed.

Lemma qgt_alice_pre_simpl :
  alice_pre_measure_operator_four =
  pad_ctrl 4 0 2 σx × pad_u 4 2 hadamard.
Proof.
  unfold alice_pre_measure_operator_four.
  rewrite <- Mmult_assoc, qgt_pad_h4_square.
  rewrite Mmult_1_l by auto with wf_db.
  reflexivity.
Qed.

Lemma qgt_kron_identity_mult : forall n m p
    (A : Matrix m m) (B : Matrix m p),
  (I n ⊗ A) × (I n ⊗ B) = I n ⊗ (A × B).
Proof.
  intros n m p A B.
  transitivity ((I n × I n) ⊗ (A × B)).
  - exact (@kron_mixed_product n n n m m p (I n) A (I n) B).
  - rewrite Mmult_1_l by auto with wf_db.
    reflexivity.
Qed.

Lemma qgt_pad_bob_ctrl :
  pad_ctrl 4 1 3 σx = I 2 ⊗ qgt_gap_ctrl σx.
Proof.
  unfold pad_ctrl, pad, qgt_gap_ctrl.
  bdestruct (1 <? 3); [|lia].
  replace (3 - 1 - 1)%nat with 1%nat by lia.
  replace (1 + (1 + 1 + 1))%nat with 4%nat by lia.
  bdestruct (4 <=? 4); [|lia].
  simpl Nat.pow.
  rewrite kron_1_r by auto with wf_db.
  reflexivity.
Qed.

Lemma qgt_pad_bob_hcxh :
  pad_u 4 3 hadamard × pad_ctrl 4 1 3 σx × pad_u 4 3 hadamard =
  I 2 ⊗ qgt_gap_ctrl σz.
Proof.
  assert (Hpad : pad_u 4 3 hadamard = I 2 ⊗ pad_u 3 2 hadamard).
  {
    pose proof (@Hpad_u_split_right 4 1 3 hadamard WF_hadamard
      ltac:(lia) ltac:(lia) ltac:(lia)) as H.
    simpl in H.
    exact H.
  }
  rewrite Hpad, qgt_pad_bob_ctrl.
  change (((I 2 ⊗ pad_u 3 2 hadamard) ×
    (I 2 ⊗ qgt_gap_ctrl σx)) ×
    (I 2 ⊗ pad_u 3 2 hadamard) = I 2 ⊗ qgt_gap_ctrl σz).
  rewrite qgt_kron_identity_mult.
  rewrite qgt_kron_identity_mult.
  f_equal.
  exact qgt_controlled_h_gap.
Qed.

Lemma qgt_kron3_action : forall m n p
    (A : Matrix m m) (B : Matrix n n) (C : Matrix p p)
    (v : Matrix m 1) (w : Matrix n 1) (z : Matrix p 1),
  ((A ⊗ B) ⊗ C) × ((v ⊗ w) ⊗ z) =
    ((A × v) ⊗ (B × w)) ⊗ (C × z).
Proof.
  intros m n p A B C v w z.
  transitivity (((A ⊗ B) × (v ⊗ w)) ⊗ (C × z)).
  - exact (@kron_mixed_product (m*n) (m*n) 1 p p 1
      (A ⊗ B) C (v ⊗ w) z).
  - f_equal.
    exact (@kron_mixed_product m m 1 n n 1 A B v w).
Qed.

Lemma qgt_rank1_projector_basis : forall (b : bool),
  (ket 1 × bra 1) × ket (if b then 1 else 0) =
  if b then ket 1 else Zero.
Proof.
  intros []; simpl.
  - rewrite Mmult_assoc, bra1ket1.
    rewrite Mmult_1_r by auto with wf_db.
    reflexivity.
  - rewrite Mmult_assoc, bra1ket0, Mmult_0_r.
    reflexivity.
Qed.

Lemma qgt_rank0_projector_basis : forall (b : bool),
  (ket 0 × bra 0) × ket (if b then 1 else 0) =
  if b then Zero else ket 0.
Proof.
  intros []; simpl.
  - rewrite Mmult_assoc, bra0ket1, Mmult_0_r.
    reflexivity.
  - rewrite Mmult_assoc, bra0ket0.
    rewrite Mmult_1_r by auto with wf_db.
    reflexivity.
Qed.

Lemma qgt_gap_ctrl_z_basis3 : forall b c d,
  qgt_gap_ctrl σz × qgt_basis3 b c d =
  (if andb b d then -1 else 1) .* qgt_basis3 b c d.
Proof.
  intros b c d.
  destruct b, c, d; simpl.
  all: rewrite !qgt_basis3_tensor.
  all: unfold qgt_gap_ctrl.
  all: rewrite Mmult_plus_distr_r.
  all: repeat rewrite qgt_kron3_action.
  all: repeat rewrite qgt_rank1_projector_basis.
  all: repeat rewrite qgt_rank0_projector_basis.
  all: repeat rewrite Mmult_1_l by auto with wf_db.
  all: try rewrite Z0_spec.
  all: try rewrite Z1_spec.
  all: autorewrite with ket_db.
  all: Csimpl.
  all: reflexivity.
Qed.

Lemma qgt_gap_ctrl_z_basis4 : forall a b c d,
  (I 2 ⊗ qgt_gap_ctrl σz) × qgt_basis4 a b c d =
  (if andb b d then -1 else 1) .* qgt_basis4 a b c d.
Proof.
  intros a b c d.
  rewrite qgt_basis4_tensor.
  replace (ket (if a then 1 else 0) ⊗ ket (if b then 1 else 0) ⊗
      ket (if c then 1 else 0) ⊗ ket (if d then 1 else 0)) with
    (ket (if a then 1 else 0) ⊗
      (ket (if b then 1 else 0) ⊗ ket (if c then 1 else 0) ⊗
        ket (if d then 1 else 0))) by
    (repeat rewrite <- kron_assoc by auto with wf_db; reflexivity).
  rewrite <- qgt_basis3_tensor.
  transitivity ((I 2 × ket (if a then 1 else 0)) ⊗
    (qgt_gap_ctrl σz × qgt_basis3 b c d)).
  - exact (@kron_mixed_product 2 2 1 8 8 1
      (I 2) (qgt_gap_ctrl σz) (ket (if a then 1 else 0))
      (qgt_basis3 b c d)).
  - rewrite Mmult_1_l by auto with wf_db.
    rewrite qgt_gap_ctrl_z_basis3.
    rewrite Mscale_kron_dist_r.
    repeat rewrite kron_assoc by auto with wf_db.
    reflexivity.
Qed.

Lemma qgt_alice_project_basis : forall a b c d x,
  proj 2 4 x × (alice_pre_measure_operator_four ×
    qgt_basis4 a b c d) =
  (if andb c (xorb x a) then - (/ √ 2) else / √ 2) .*
    qgt_basis4 a b x d.
Proof.
  intros a b c d x.
  rewrite qgt_alice_pre_simpl.
  unfold qgt_basis4.
  repeat rewrite Mmult_assoc.
  rewrite f_to_vec_hadamard by lia.
  repeat rewrite Mscale_mult_dist_r.
  repeat rewrite Mmult_plus_distr_l.
  repeat rewrite Mscale_mult_dist_r.
  repeat rewrite Mmult_assoc.
  repeat rewrite (@f_to_vec_cnot 4 0 2 _) by lia.
  repeat rewrite Mscale_mult_dist_r.
  repeat rewrite Mmult_plus_distr_l.
  repeat rewrite Mscale_mult_dist_r.
  repeat rewrite Mmult_assoc.
  repeat rewrite (@f_to_vec_proj _ 2 4 _) by lia.
  cbn [update b2R].
  rewrite ?Cexp_0, ?qgt_Cexp_PI, ?Cexp_neg.
  destruct a, b, c, d, x; simpl.
  all: replace (0 * PI)%R with 0 by ring.
  all: replace (1 * PI)%R with PI by ring.
  all: rewrite ?Cexp_0, ?qgt_Cexp_PI.
  all: autorewrite with ket_db; Csimpl; f_equal;
    repeat rewrite RtoC_opp; Csimpl; C_field; reflexivity.
Qed.

Lemma qgt_bob_project_basis : forall a b c d y,
  proj 3 4 y × (bob_pre_measure_operator_four × qgt_basis4 a b c d) =
  ((if andb b d then -1 else 1) *
    (if d then (if y then Ci else - Ci) / √ 2 else / √ 2)) .*
      qgt_basis4 a b c y.
Proof.
  intros a b c d y.
  unfold bob_pre_measure_operator_four.
  replace (pad_u 4 3 hadamard ×
      (pad_ctrl 4 1 3 σx × pad_u 4 3 hadamard)) with
    ((pad_u 4 3 hadamard × pad_ctrl 4 1 3 σx) ×
      pad_u 4 3 hadamard) at 1 by apply Mmult_assoc.
  rewrite qgt_pad_bob_hcxh.
  replace ((pad_u 4 3 hadamard ×
      (pad_u 4 3 (phase_shift (- PI / 2)) × (I 2 ⊗ qgt_gap_ctrl σz))) ×
      qgt_basis4 a b c d) with
    (pad_u 4 3 hadamard ×
      (pad_u 4 3 (phase_shift (- PI / 2)) ×
        ((I 2 ⊗ qgt_gap_ctrl σz) × qgt_basis4 a b c d))) at 1
    by (repeat rewrite Mmult_assoc; reflexivity).
  rewrite qgt_gap_ctrl_z_basis4.
  repeat rewrite Mscale_mult_dist_r.
  unfold qgt_basis4.
  rewrite f_to_vec_phase_shift by lia.
  repeat rewrite Mscale_mult_dist_r.
  rewrite f_to_vec_hadamard by lia.
  repeat rewrite Mscale_mult_dist_r.
  repeat rewrite Mmult_plus_distr_l.
  repeat rewrite Mscale_mult_dist_r.
  repeat rewrite (@f_to_vec_proj _ 3 4 _) by lia.
  destruct a, b, c, d, y; simpl.
  all: replace (1 * (- PI / 2))%R with (- PI / 2)%R by ring.
  all: replace (1 * PI)%R with PI by ring.
  all: replace (- PI / 2)%R with (-(PI / 2))%R by lra.
  all: replace (0 * (-(PI / 2)))%R with 0%R by ring.
  all: replace (0 * PI)%R with 0%R by ring.
  all: rewrite ?Cexp_0, ?qgt_Cexp_PI, ?Cexp_neg, ?Cexp_PI2.
  all: rewrite ?Copp_Ci.
  all: autorewrite with ket_db.
  all: Csimpl; f_equal; C_field.
Qed.

Lemma qgt_final_correction_basis : forall a b x y,
  qgt_final_correction × qgt_basis4 a b x y =
  (Cexp (b2R a * (PI / 2)) * Cexp (b2R b * (PI / 2))) .*
    qgt_basis4 a b x y.
Proof.
  intros a b x y.
  unfold qgt_final_correction, qgt_basis4.
  repeat rewrite Mmult_assoc.
  rewrite (@f_to_vec_phase_shift 4 0 (PI / 2) _) by lia.
  repeat rewrite Mscale_mult_dist_r.
  rewrite (@f_to_vec_phase_shift 4 1 (PI / 2) _) by lia.
  rewrite Mscale_assoc.
  f_equal.
Qed.

Lemma qgt_final_correction_dag_basis : forall a b x y,
  qgt_final_correction_dag × qgt_basis4 a b x y =
  (Cexp (b2R a * (- PI / 2)) * Cexp (b2R b * (- PI / 2))) .*
    qgt_basis4 a b x y.
Proof.
  intros a b x y.
  unfold qgt_final_correction_dag, qgt_basis4.
  repeat rewrite Mmult_assoc.
  rewrite (@f_to_vec_phase_shift 4 0 (- PI / 2) _) by lia.
  repeat rewrite Mscale_mult_dist_r.
  rewrite (@f_to_vec_phase_shift 4 1 (- PI / 2) _) by lia.
  rewrite Mscale_assoc.
  f_equal.
Qed.

Lemma qgt_cz_wf : WF_Matrix cz.
Proof.
  unfold cz; intros i j Hout.
  destruct i as [|[|[|[|i]]]], j as [|[|[|[|j]]]];
    simpl in *; try lia; reflexivity.
Qed.

Lemma qgt_cz_basis : forall (a b : bool),
  cz × (ket (if a then 1 else 0) ⊗ ket (if b then 1 else 0)) =
  (if andb a b then -1 else 1) .*
    (ket (if a then 1 else 0) ⊗ ket (if b then 1 else 0)).
Proof.
  intros a b.
  apply mat_equiv_eq.
  - apply WF_mult.
    + apply qgt_cz_wf.
    + repeat apply WF_kron; auto with wf_db.
  - repeat apply WF_scale; repeat apply WF_kron; auto with wf_db.
  - unfold mat_equiv; by_cell_no_intros.
    all: destruct a, b.
    all: unfold cz, Mmult, kron, ket, scale, qubit0, qubit1;
      simpl; Csimpl; reflexivity.
Qed.

Lemma qgt_target_basis4 : forall (a b x y : bool),
  (cz × (ket (if a then 1 else 0) ⊗ ket (if b then 1 else 0))) ⊗
    (ket (if x then 1 else 0) ⊗ ket (if y then 1 else 0)) =
  (if andb a b then -1 else 1) .* qgt_basis4 a b x y.
Proof.
  intros a b x y.
  rewrite qgt_cz_basis.
  rewrite Mscale_kron_dist_l.
  rewrite kron_assoc by auto with wf_db.
  rewrite qgt_basis4_tensor.
  rewrite <- !kron_assoc by auto with wf_db.
  reflexivity.
Qed.

Lemma qgt_basis2_tensor : forall (f : nat -> bool),
  f_to_vec 2 f = ket (if f 0%nat then 1 else 0) ⊗ ket (if f 1%nat then 1 else 0).
Proof.
  intros f.
  unfold f_to_vec.
  change (I 1 ⊗ ket (if f 0%nat then 1 else 0) ⊗
    ket (if f 1%nat then 1 else 0) =
    ket (if f 0%nat then 1 else 0) ⊗ ket (if f 1%nat then 1 else 0)).
  rewrite kron_1_l by auto with wf_db.
  reflexivity.
Qed.

Lemma qgt_target_map_apply_basis : forall (a b x y : bool),
  (cz ⊗ (ket (if x then 1 else 0) ⊗ ket (if y then 1 else 0))) ×
      (ket (if a then 1 else 0) ⊗ ket (if b then 1 else 0)) =
  ((cz × (ket (if a then 1 else 0) ⊗ ket (if b then 1 else 0))) ⊗
      (ket (if x then 1 else 0) ⊗ ket (if y then 1 else 0))).
Proof.
  intros a b x y.
  replace (ket (if a then 1 else 0) ⊗ ket (if b then 1 else 0)) with
    ((ket (if a then 1 else 0) ⊗ ket (if b then 1 else 0)) ⊗ I 1)
    at 1 by exact (@kron_1_r 4 1
      (ket (if a then 1 else 0) ⊗ ket (if b then 1 else 0))).
  transitivity ((cz ×
      (ket (if a then 1 else 0) ⊗ ket (if b then 1 else 0))) ⊗
    ((ket (if x then 1 else 0) ⊗ ket (if y then 1 else 0)) × I 1)).
  - exact (@kron_mixed_product 4 4 1 4 1 1 cz
      (ket (if x then 1 else 0) ⊗ ket (if y then 1 else 0))
      (ket (if a then 1 else 0) ⊗ ket (if b then 1 else 0)) (I 1)).
  - rewrite Mmult_1_r by auto with wf_db.
    reflexivity.
Qed.

Lemma qgt_full_branch_on_basis : forall (a b x y : bool),
  Bool.eqb x y = false ->
  qgt_full_branch x y ×
    (ket (if a then 1 else 0) ⊗ ket (if b then 1 else 0)) =
  qgt_branch_scalar x y .*
    ((cz × (ket (if a then 1 else 0) ⊗ ket (if b then 1 else 0))) ⊗
      (ket (if x then 1 else 0) ⊗ ket (if y then 1 else 0))).
Proof.
  intros a b x y Hxy.
  unfold qgt_full_branch.
  repeat rewrite Mmult_assoc.
  rewrite qgt_epr_input_basis.
  repeat rewrite Mscale_mult_dist_r.
  repeat rewrite Mmult_plus_distr_l.
  repeat rewrite qgt_alice_project_basis.
  repeat rewrite Mscale_mult_dist_r.
  repeat rewrite Mmult_plus_distr_l.
  repeat rewrite qgt_bob_project_basis.
  repeat rewrite Mscale_mult_dist_r.
  repeat rewrite qgt_final_correction_basis.
  rewrite qgt_target_basis4.
  destruct a, b, x, y; simpl in Hxy; try discriminate.
  all: simpl.
  all: rewrite ?Rmult_1_l, ?Rmult_0_l.
  all: rewrite ?Cexp_0, ?Cexp_PI2.
  all: Csimpl.
  all: repeat rewrite Mscale_assoc.
  all: rewrite <- Mscale_plus_distr_l.
  all: repeat rewrite Mscale_assoc.
  all: rewrite ?Ci2.
  all: unfold qgt_branch_scalar.
  all: Csimpl.
  all: simpl.
  all: f_equal; C_field.
  all: lca.
Qed.

Definition qgt_full_branch_dag (x y : bool) : Matrix 16 4 :=
  qgt_final_correction_dag ×
    (proj 3 4 y ×
      (bob_pre_measure_operator_four ×
        (proj 2 4 x ×
          (alice_pre_measure_operator_four × qgt_epr_preparation)))).

Lemma qgt_full_branch_dag_on_basis : forall (a b x y : bool),
  Bool.eqb x y = true ->
  qgt_full_branch_dag x y ×
    (ket (if a then 1 else 0) ⊗ ket (if b then 1 else 0)) =
  qgt_branch_scalar x y .*
    ((cz × (ket (if a then 1 else 0) ⊗ ket (if b then 1 else 0))) ⊗
      (ket (if x then 1 else 0) ⊗ ket (if y then 1 else 0))).
Proof.
  intros a b x y Hxy.
  unfold qgt_full_branch_dag.
  repeat rewrite Mmult_assoc.
  rewrite qgt_epr_input_basis.
  repeat rewrite Mscale_mult_dist_r.
  repeat rewrite Mmult_plus_distr_l.
  repeat rewrite qgt_alice_project_basis.
  repeat rewrite Mscale_mult_dist_r.
  repeat rewrite Mmult_plus_distr_l.
  repeat rewrite qgt_bob_project_basis.
  repeat rewrite Mscale_mult_dist_r.
  repeat rewrite qgt_final_correction_dag_basis.
  rewrite qgt_target_basis4.
  destruct a, b, x, y; simpl in Hxy; try discriminate.
  all: simpl.
  all: rewrite ?Rmult_1_l, ?Rmult_0_l.
  all: replace (- PI / 2)%R with (-(PI / 2))%R by lra.
  all: rewrite ?Cexp_0, ?Cexp_neg, ?Cexp_PI2.
  all: rewrite ?Copp_Ci.
  all: Csimpl.
  all: repeat rewrite Mscale_assoc.
  all: rewrite <- Mscale_plus_distr_l.
  all: repeat rewrite Mscale_assoc.
  all: rewrite ?Ci2.
  all: unfold qgt_branch_scalar.
  all: Csimpl.
  all: simpl.
  all: f_equal; C_field.
  all: lca.
Qed.

Lemma qgt_full_branch_dag_matrix : forall (x y : bool),
  Bool.eqb x y = true ->
  qgt_full_branch_dag x y =
    qgt_branch_scalar x y .*
      (cz ⊗ (ket (if x then 1 else 0) ⊗ ket (if y then 1 else 0))).
Proof.
  intros x y Hxy.
  apply (@equal_on_basis_states_implies_equal 16 2 _ _).
  - unfold qgt_full_branch_dag, qgt_final_correction_dag,
      bob_pre_measure_operator_four, alice_pre_measure_operator_four,
      qgt_epr_preparation.
    repeat apply WF_mult; repeat apply WF_kron; auto with wf_db.
  - repeat apply WF_scale; repeat apply WF_kron; apply qgt_cz_wf || auto with wf_db.
  - intros f.
    rewrite qgt_basis2_tensor.
    rewrite Mscale_mult_dist_l.
    rewrite qgt_target_map_apply_basis.
    destruct (f 0%nat), (f 1%nat).
    + exact (qgt_full_branch_dag_on_basis true true x y Hxy).
    + exact (qgt_full_branch_dag_on_basis true false x y Hxy).
    + exact (qgt_full_branch_dag_on_basis false true x y Hxy).
    + exact (qgt_full_branch_dag_on_basis false false x y Hxy).
Qed.

Lemma qgt_full_branch_matrix : forall (x y : bool),
  Bool.eqb x y = false ->
  qgt_full_branch x y =
    qgt_branch_scalar x y .*
      (cz ⊗ (ket (if x then 1 else 0) ⊗ ket (if y then 1 else 0))).
Proof.
  intros x y Hxy.
  apply (@equal_on_basis_states_implies_equal 16 2 _ _).
  - unfold qgt_full_branch, qgt_final_correction,
      bob_pre_measure_operator_four, alice_pre_measure_operator_four,
      qgt_epr_preparation.
    repeat apply WF_mult; repeat apply WF_kron; auto with wf_db.
  - repeat apply WF_scale; repeat apply WF_kron; apply qgt_cz_wf || auto with wf_db.
  - intros f.
    rewrite qgt_basis2_tensor.
    rewrite Mscale_mult_dist_l.
    rewrite qgt_target_map_apply_basis.
    destruct (f 0%nat), (f 1%nat).
    + exact (qgt_full_branch_on_basis true true x y Hxy).
    + exact (qgt_full_branch_on_basis true false x y Hxy).
    + exact (qgt_full_branch_on_basis false true x y Hxy).
    + exact (qgt_full_branch_on_basis false false x y Hxy).
Qed.

(* The current protocol prepares |01> + |10>, applies X to Alice's
   measurement qubit, and uses opposite phase corrections on the two data
   qubits.  Keep the earlier branch operators above as the |00> + |11>
   calculation used by the original protocol. *)
Definition qgt_epr_preparation_current : Matrix 16 4 :=
  pad_u 4 3 σx × qgt_epr_preparation.

Definition alice_pre_measure_operator_four_current : Matrix 16 16 :=
  pad_u 4 2 σx × alice_pre_measure_operator_four.

Definition qgt_final_correction_current (x y : bool) : Matrix 16 16 :=
  (if Bool.eqb x y
   then pad_u 4 1 (phase_shift (PI / 2))
   else pad_u 4 1 (phase_shift (- PI / 2))) ×
  (if Bool.eqb x y
   then pad_u 4 0 (phase_shift (- PI / 2))
   else pad_u 4 0 (phase_shift (PI / 2))).

Definition qgt_final_correction_two_current (x y : bool) : Matrix 4 4 :=
  (if Bool.eqb x y
   then pad_u 2 1 (phase_shift (PI / 2))
   else pad_u 2 1 (phase_shift (- PI / 2))) ×
  (if Bool.eqb x y
   then pad_u 2 0 (phase_shift (- PI / 2))
   else pad_u 2 0 (phase_shift (PI / 2))).

Definition qgt_full_branch_current (x y : bool) : Matrix 16 4 :=
  qgt_final_correction_current x y ×
    (proj 3 4 y ×
      (bob_pre_measure_operator_four ×
        (proj 2 4 x ×
          (alice_pre_measure_operator_four_current ×
            qgt_epr_preparation_current)))).

Definition qgt_current_branch_scalar (x y : bool) : Complex.C :=
  if Bool.eqb x y then
    (if x then 1 else -1) * (1 + Ci) / (2 * sqrt 2)
  else
    (if x then 1 else -1) * (1 - Ci) / (2 * sqrt 2).

Lemma qgt_pad_x_alice :
  pad_u 4 2 σx = I 4 ⊗ (σx ⊗ I 2).
Proof.
  unfold pad_u, pad.
  bdestruct (2 + 1 <=? 4); [|lia].
  replace (2 ^ 2)%nat with 4%nat by reflexivity.
  replace (4 - (2 + 1))%nat with 1%nat by lia.
  simpl Nat.pow.
  apply kron_assoc; auto with wf_db.
Qed.

Lemma qgt_pad_u_alice_generic : forall (U : Matrix 2 2),
  WF_Matrix U ->
  pad_u 4 2 U = I 4 ⊗ (U ⊗ I 2).
Proof.
  intros U Hwf.
  unfold pad_u, pad.
  bdestruct (2 + 1 <=? 4); [|lia].
  replace (2 ^ 2)%nat with 4%nat by reflexivity.
  replace (4 - (2 + 1))%nat with 1%nat by lia.
  simpl Nat.pow.
  apply kron_assoc; auto with wf_db.
Qed.

Lemma qgt_pad_x_last :
  pad_u 4 3 σx = I 8 ⊗ σx.
Proof.
  unfold pad_u, pad.
  bdestruct (3 + 1 <=? 4); [|lia].
  replace (2 ^ 3)%nat with 8%nat by reflexivity.
  replace (4 - (3 + 1))%nat with 0%nat by lia.
  simpl Nat.pow.
  rewrite kron_1_r by auto with wf_db.
  reflexivity.
Qed.

Lemma qgt_sigma_x_ket_flip : forall b : bool,
  σx × ket (if b then 1 else 0) = ket (if negb b then 1 else 0).
Proof.
  intros [].
  all: apply mat_equiv_eq.
  all: try (apply WF_mult; auto with wf_db).
  all: try auto with wf_db.
  all: unfold mat_equiv; by_cell_no_intros.
  all: unfold σx, Mmult, ket, qubit0, qubit1; simpl; Csimpl; reflexivity.
Qed.

Lemma qgt_pad_x_alice_basis : forall a b c d,
  pad_u 4 2 σx × qgt_basis4 a b c d =
  qgt_basis4 a b (negb c) d.
Proof.
  intros a b c d.
  rewrite qgt_pad_x_alice, !qgt_basis4_tensor.
  replace (ket (if a then 1 else 0) ⊗ ket (if b then 1 else 0) ⊗
      ket (if c then 1 else 0) ⊗ ket (if d then 1 else 0)) with
    ((ket (if a then 1 else 0) ⊗ ket (if b then 1 else 0)) ⊗
      (ket (if c then 1 else 0) ⊗ ket (if d then 1 else 0))) at 1
    by (repeat rewrite <- kron_assoc by auto with wf_db; reflexivity).
  transitivity ((I 4 ×
      (ket (if a then 1 else 0) ⊗ ket (if b then 1 else 0))) ⊗
    ((σx ⊗ I 2) ×
      (ket (if c then 1 else 0) ⊗ ket (if d then 1 else 0)))).
  - exact (@kron_mixed_product 4 4 1 4 4 1 (I 4) (σx ⊗ I 2)
      (ket (if a then 1 else 0) ⊗ ket (if b then 1 else 0))
      (ket (if c then 1 else 0) ⊗ ket (if d then 1 else 0))).
  - rewrite Mmult_1_l by auto with wf_db.
    transitivity ((ket (if a then 1 else 0) ⊗ ket (if b then 1 else 0)) ⊗
      ((σx × ket (if c then 1 else 0)) ⊗ (I 2 × ket (if d then 1 else 0)))).
    + f_equal.
      exact (@kron_mixed_product 2 2 1 2 2 1 σx (I 2)
        (ket (if c then 1 else 0)) (ket (if d then 1 else 0))).
    + rewrite qgt_sigma_x_ket_flip.
      rewrite Mmult_1_l by auto with wf_db.
      repeat rewrite <- kron_assoc by auto with wf_db.
      reflexivity.
Qed.

Lemma qgt_pad_x_last_basis : forall a b c d,
  pad_u 4 3 σx × qgt_basis4 a b c d =
  qgt_basis4 a b c (negb d).
Proof.
  intros a b c d.
  assert (Hsplit : forall a b c d,
    qgt_basis4 a b c d = qgt_basis3 a b c ⊗
      ket (if d then 1 else 0)).
  {
    intros a0 b0 c0 d0.
    rewrite qgt_basis4_tensor, qgt_basis3_tensor.
    repeat rewrite <- kron_assoc by auto with wf_db.
    reflexivity.
  }
  rewrite qgt_pad_x_last, !Hsplit.
  transitivity ((I 8 × qgt_basis3 a b c) ⊗
    (σx × ket (if d then 1 else 0))).
  - exact (@kron_mixed_product 8 8 1 2 2 1 (I 8) σx
      (qgt_basis3 a b c) (ket (if d then 1 else 0))).
  - assert (Hwf3 : WF_Matrix (qgt_basis3 a b c)).
    { rewrite qgt_basis3_tensor; repeat apply WF_kron; auto with wf_db. }
    rewrite Mmult_1_l by exact Hwf3.
    rewrite qgt_sigma_x_ket_flip.
    rewrite qgt_basis3_tensor.
    reflexivity.
Qed.

Lemma qgt_epr_preparation_current_input_basis : forall (a b : bool),
  qgt_epr_preparation_current ×
    (ket (if a then 1 else 0) ⊗ ket (if b then 1 else 0)) =
  / √ 2 .* (Mplus (qgt_basis4 a b false true)
                   (qgt_basis4 a b true false)).
Proof.
  intros a b.
  unfold qgt_epr_preparation_current.
  repeat rewrite Mmult_assoc.
  rewrite qgt_epr_input_basis.
  rewrite Mscale_mult_dist_r, Mmult_plus_distr_l.
  rewrite qgt_pad_x_last_basis, qgt_pad_x_last_basis.
  reflexivity.
Qed.

Lemma qgt_bool_projector_x_flip : forall b : bool,
  bool_to_matrix b × σx = σx × bool_to_matrix (negb b).
Proof.
  intros [].
  all: apply mat_equiv_eq.
  all: try (apply WF_mult; auto with wf_db).
  all: try auto with wf_db.
  all: unfold mat_equiv; by_cell_no_intros.
  all: unfold bool_to_matrix, σx, ket, bra, Mmult, qubit0, qubit1;
    simpl; Csimpl; reflexivity.
Qed.

Lemma qgt_proj_x_flip_alice : forall x,
  proj 2 4 x × pad_u 4 2 σx =
  pad_u 4 2 σx × proj 2 4 (negb x).
Proof.
  intros x.
  unfold proj.
  assert (Hwfproj : WF_Matrix (bool_to_matrix x)) by auto with wf_db.
  assert (Hwfproj' : WF_Matrix (bool_to_matrix (negb x))) by auto with wf_db.
  rewrite (qgt_pad_u_alice_generic (bool_to_matrix x) Hwfproj).
  rewrite qgt_pad_x_alice.
  rewrite (qgt_pad_u_alice_generic (bool_to_matrix (negb x)) Hwfproj').
  transitivity ((I 4 × I 4) ⊗
    ((bool_to_matrix x ⊗ I 2) × (σx ⊗ I 2))).
  - exact (@kron_mixed_product 4 4 4 4 4 4
      (I 4) (bool_to_matrix x ⊗ I 2)
      (I 4) (σx ⊗ I 2)).
  - rewrite Mmult_1_l by auto with wf_db.
    transitivity (I 4 ⊗
      ((σx ⊗ I 2) × (bool_to_matrix (negb x) ⊗ I 2))).
    + f_equal.
      transitivity ((bool_to_matrix x × σx) ⊗ (I 2 × I 2)).
      * exact (@kron_mixed_product 2 2 2 2 2 2
           (bool_to_matrix x) (I 2) σx (I 2)).
      * rewrite qgt_bool_projector_x_flip.
        rewrite Mmult_1_l by auto with wf_db.
        pose proof (@kron_mixed_product 2 2 2 2 2 2
          σx (I 2) (bool_to_matrix (negb x)) (I 2)) as Hmixed.
        rewrite Mmult_1_l in Hmixed by auto with wf_db.
        symmetry.
        exact Hmixed.
    + symmetry.
      transitivity ((I 4 × I 4) ⊗
        ((σx ⊗ I 2) × (bool_to_matrix (negb x) ⊗ I 2))).
      * exact (@kron_mixed_product 4 4 4 4 4 4
          (I 4) (σx ⊗ I 2) (I 4) (bool_to_matrix (negb x) ⊗ I 2)).
      * rewrite Mmult_1_l by auto with wf_db.
        reflexivity.
Qed.

Lemma qgt_alice_project_basis_current : forall a b c d x,
  proj 2 4 x ×
    (alice_pre_measure_operator_four_current × qgt_basis4 a b c d) =
  (if andb c (xorb (negb x) a) then - (/ √ 2) else / √ 2) .*
    qgt_basis4 a b x d.
Proof.
  intros a b c d x.
  unfold alice_pre_measure_operator_four_current.
  rewrite Mmult_assoc.
  rewrite <- Mmult_assoc.
  rewrite qgt_proj_x_flip_alice.
  rewrite Mmult_assoc.
  rewrite qgt_alice_project_basis.
  rewrite Mscale_mult_dist_r.
  rewrite qgt_pad_x_alice_basis.
  rewrite negb_involutive.
  reflexivity.
Qed.

Lemma qgt_final_correction_current_basis : forall a b x y,
  qgt_final_correction_current x y × qgt_basis4 a b x y =
  (if Bool.eqb x y
   then Cexp (b2R a * (- PI / 2)) * Cexp (b2R b * (PI / 2))
   else Cexp (b2R a * (PI / 2)) * Cexp (b2R b * (- PI / 2))) .*
    qgt_basis4 a b x y.
Proof.
  intros a b x y.
  destruct x, y.
  all: unfold qgt_final_correction_current, qgt_basis4.
  all: cbn [Bool.eqb].
  all: repeat rewrite Mmult_assoc.
  all: rewrite (@f_to_vec_phase_shift 4 0 _ _) by lia.
  all: repeat rewrite Mscale_mult_dist_r.
  all: rewrite (@f_to_vec_phase_shift 4 1 _ _) by lia.
  all: repeat rewrite Mscale_assoc; f_equal.
Qed.

Lemma qgt_current_branch_on_basis : forall (a b x y : bool),
  qgt_full_branch_current x y ×
    (ket (if a then 1 else 0) ⊗ ket (if b then 1 else 0)) =
  qgt_current_branch_scalar x y .*
    ((cz × (ket (if a then 1 else 0) ⊗ ket (if b then 1 else 0))) ⊗
      (ket (if x then 1 else 0) ⊗ ket (if y then 1 else 0))).
Proof.
  intros a b x y.
  unfold qgt_full_branch_current.
  repeat rewrite Mmult_assoc.
  rewrite qgt_epr_preparation_current_input_basis.
  repeat rewrite Mscale_mult_dist_r.
  repeat rewrite Mmult_plus_distr_l.
  repeat rewrite qgt_alice_project_basis_current.
  repeat rewrite Mscale_mult_dist_r.
  repeat rewrite Mmult_plus_distr_l.
  repeat rewrite qgt_bob_project_basis.
  repeat rewrite Mscale_mult_dist_r.
  rewrite qgt_final_correction_current_basis.
  rewrite qgt_target_basis4.
  destruct a, b, x, y; simpl.
  all: rewrite ?Rmult_1_l, ?Rmult_0_l.
  all: replace (- PI / 2)%R with (-(PI / 2))%R by lra.
  all: rewrite ?Cexp_0, ?Cexp_neg, ?Cexp_PI2, ?Copp_Ci.
  all: Csimpl.
  all: repeat rewrite Mscale_assoc.
  all: rewrite <- Mscale_plus_distr_l.
  all: repeat rewrite Mscale_assoc.
  all: unfold qgt_current_branch_scalar.
  all: Csimpl.
  all: simpl.
  all: f_equal; C_field.
  all: lca.
Qed.

Lemma qgt_current_branch_matrix : forall x y,
  qgt_full_branch_current x y =
    qgt_current_branch_scalar x y .*
      (cz ⊗ (ket (if x then 1 else 0) ⊗ ket (if y then 1 else 0))).
Proof.
  intros x y.
  apply (@equal_on_basis_states_implies_equal 16 2 _ _).
  - unfold qgt_full_branch_current, qgt_final_correction_current,
      alice_pre_measure_operator_four_current, qgt_epr_preparation_current.
    destruct (Bool.eqb x y); simpl.
    all: unfold bob_pre_measure_operator_four,
      alice_pre_measure_operator_four, qgt_epr_preparation.
    all: repeat apply WF_mult; repeat apply WF_kron; auto with wf_db.
  - repeat apply WF_scale; repeat apply WF_kron;
      apply qgt_cz_wf || auto with wf_db.
  - intros f.
    rewrite qgt_basis2_tensor.
    rewrite Mscale_mult_dist_l.
    rewrite qgt_target_map_apply_basis.
    destruct (f 0%nat), (f 1%nat).
    + exact (qgt_current_branch_on_basis true true x y).
    + exact (qgt_current_branch_on_basis true false x y).
    + exact (qgt_current_branch_on_basis false true x y).
    + exact (qgt_current_branch_on_basis false false x y).
Qed.

Definition qgt_insert_alice (x : bool) : Matrix 16 8 :=
  insert_measured_wire_operator 3 2 x.

Definition qgt_insert_bob (y : bool) : Matrix 8 4 :=
  insert_measured_wire_operator 2 2 y.

Definition qgt_final_correction_two : Matrix 4 4 :=
  pad_u 2 1 (phase_shift (PI / 2)) ×
    pad_u 2 0 (phase_shift (PI / 2)).

Definition qgt_final_correction_two_dag : Matrix 4 4 :=
  pad_u 2 1 (phase_shift (- PI / 2)) ×
    pad_u 2 0 (phase_shift (- PI / 2)).

Lemma qgt_insert_preserves_length : forall
    (qm : finite_map qubit_reference (participant * fin)) q old value,
  qm q = Some old ->
  length (elems qubit_reference (participant * fin)
    (insert (KEQ := qr_dec) qm q value)) =
  length (elems qubit_reference (participant * fin) qm).
Proof.
  intros qm q old value Hlookup.
  unfold insert; simpl.
  apply (@replace_or_add_In_length qubit_reference (participant * fin)
    qr_dec (elems qubit_reference (participant * fin) qm) q).
  exists old.
  apply (proj2 (specs qubit_reference (participant * fin) qm) q old).
  exact Hlookup.
Qed.

Lemma qgt_get_all_values_singleton : forall
    (qm : finite_map qubit_reference (participant * fin)) q owner index values,
  get_all_values qm [q] = Some values ->
  qm q = Some (owner, index) ->
  values = [(owner, index)].
Proof.
  intros qm q owner index values Hvalues Hlookup.
  simpl in Hvalues.
  rewrite Hlookup in Hvalues.
  inversion Hvalues; reflexivity.
Qed.

Lemma qgt_get_all_values_pair : forall
    (qm : finite_map qubit_reference (participant * fin)) q0 q1
    owner0 index0 owner1 index1 values,
  get_all_values qm (q0 :: q1 :: nil) = Some values ->
  qm q0 = Some (owner0, index0) ->
  qm q1 = Some (owner1, index1) ->
  values = (owner0, index0) :: (owner1, index1) :: nil.
Proof.
  intros qm q0 q1 owner0 index0 owner1 index1 values Hvalues Hlookup0 Hlookup1.
  simpl in Hvalues.
  rewrite Hlookup0, Hlookup1 in Hvalues.
  inversion Hvalues; reflexivity.
Qed.

Lemma qgt_final_correction_insert_intertwine : forall x y,
  qgt_insert_alice x ×
    (qgt_insert_bob y × qgt_final_correction_two) =
  qgt_final_correction × (qgt_insert_alice x × qgt_insert_bob y).
Proof.
  intros x y.
  set (Sgate := phase_shift (PI / 2)).
  set (IB := qgt_insert_bob y).
  set (IA := qgt_insert_alice x).
  set (C2 := pad_u 2 1 Sgate × pad_u 2 0 Sgate).
  set (C3 := pad_u 3 1 Sgate × pad_u 3 0 Sgate).
  set (C4 := pad_u 4 1 Sgate × pad_u 4 0 Sgate).
  assert (Hinsert_bob_1 : IB × pad_u 2 1 Sgate = pad_u 3 1 Sgate × IB).
  { unfold IB, qgt_insert_bob, Sgate.
    exact (@Hinsert_pad_u_intertwine 2 2 1 y (phase_shift (PI / 2))
      ltac:(lia) ltac:(lia) ltac:(auto with wf_db)). }
  assert (Hinsert_bob_0 : IB × pad_u 2 0 Sgate = pad_u 3 0 Sgate × IB).
  { unfold IB, qgt_insert_bob, Sgate.
    exact (@Hinsert_pad_u_intertwine 2 2 0 y (phase_shift (PI / 2))
      ltac:(lia) ltac:(lia) ltac:(auto with wf_db)). }
  assert (Hinsert_alice_1 : IA × pad_u 3 1 Sgate = pad_u 4 1 Sgate × IA).
  { unfold IA, qgt_insert_alice, Sgate.
    exact (@Hinsert_pad_u_intertwine 3 2 1 x (phase_shift (PI / 2))
      ltac:(lia) ltac:(lia) ltac:(auto with wf_db)). }
  assert (Hinsert_alice_0 : IA × pad_u 3 0 Sgate = pad_u 4 0 Sgate × IA).
  { unfold IA, qgt_insert_alice, Sgate.
    exact (@Hinsert_pad_u_intertwine 3 2 0 x (phase_shift (PI / 2))
      ltac:(lia) ltac:(lia) ltac:(auto with wf_db)). }
  assert (Hbob_correction : IB × C2 = C3 × IB).
  {
    unfold C2, C3.
    transitivity ((IB × pad_u 2 1 Sgate) × pad_u 2 0 Sgate).
    - symmetry; apply Mmult_assoc.
    - transitivity (pad_u 3 1 Sgate × (IB × pad_u 2 0 Sgate)).
      + rewrite Hinsert_bob_1; apply Mmult_assoc.
      + rewrite Hinsert_bob_0; symmetry; apply Mmult_assoc.
  }
  assert (Halice_correction : IA × C3 = C4 × IA).
  {
    unfold C3, C4.
    transitivity ((IA × pad_u 3 1 Sgate) × pad_u 3 0 Sgate).
    - symmetry; apply Mmult_assoc.
    - transitivity (pad_u 4 1 Sgate × (IA × pad_u 3 0 Sgate)).
      + rewrite Hinsert_alice_1; apply Mmult_assoc.
      + rewrite Hinsert_alice_0; symmetry; apply Mmult_assoc.
  }
  change (IA × (IB × C2) = C4 × (IA × IB)).
  transitivity (IA × (C3 × IB)).
  - rewrite Hbob_correction; reflexivity.
  - transitivity ((IA × C3) × IB).
    + symmetry; apply Mmult_assoc.
    + rewrite Halice_correction; apply Mmult_assoc.
Qed.

Lemma qgt_final_correction_insert_intertwine_dag : forall x y,
  qgt_insert_alice x ×
    (qgt_insert_bob y × qgt_final_correction_two_dag) =
  qgt_final_correction_dag ×
    (qgt_insert_alice x × qgt_insert_bob y).
Proof.
  intros x y.
  set (Sdag := phase_shift (- PI / 2)).
  set (IB := qgt_insert_bob y).
  set (IA := qgt_insert_alice x).
  set (C2 := pad_u 2 1 Sdag × pad_u 2 0 Sdag).
  set (C3 := pad_u 3 1 Sdag × pad_u 3 0 Sdag).
  set (C4 := pad_u 4 1 Sdag × pad_u 4 0 Sdag).
  assert (Hinsert_bob_1 : IB × pad_u 2 1 Sdag = pad_u 3 1 Sdag × IB).
  { unfold IB, qgt_insert_bob, Sdag.
    exact (@Hinsert_pad_u_intertwine 2 2 1 y (phase_shift (- PI / 2))
      ltac:(lia) ltac:(lia) ltac:(auto with wf_db)). }
  assert (Hinsert_bob_0 : IB × pad_u 2 0 Sdag = pad_u 3 0 Sdag × IB).
  { unfold IB, qgt_insert_bob, Sdag.
    exact (@Hinsert_pad_u_intertwine 2 2 0 y (phase_shift (- PI / 2))
      ltac:(lia) ltac:(lia) ltac:(auto with wf_db)). }
  assert (Hinsert_alice_1 : IA × pad_u 3 1 Sdag = pad_u 4 1 Sdag × IA).
  { unfold IA, qgt_insert_alice, Sdag.
    exact (@Hinsert_pad_u_intertwine 3 2 1 x (phase_shift (- PI / 2))
      ltac:(lia) ltac:(lia) ltac:(auto with wf_db)). }
  assert (Hinsert_alice_0 : IA × pad_u 3 0 Sdag = pad_u 4 0 Sdag × IA).
  { unfold IA, qgt_insert_alice, Sdag.
    exact (@Hinsert_pad_u_intertwine 3 2 0 x (phase_shift (- PI / 2))
      ltac:(lia) ltac:(lia) ltac:(auto with wf_db)). }
  assert (Hbob_correction : IB × C2 = C3 × IB).
  {
    unfold C2, C3.
    transitivity ((IB × pad_u 2 1 Sdag) × pad_u 2 0 Sdag).
    - symmetry; apply Mmult_assoc.
    - transitivity (pad_u 3 1 Sdag × (IB × pad_u 2 0 Sdag)).
      + rewrite Hinsert_bob_1; apply Mmult_assoc.
      + rewrite Hinsert_bob_0; symmetry; apply Mmult_assoc.
  }
  assert (Halice_correction : IA × C3 = C4 × IA).
  {
    unfold C3, C4.
    transitivity ((IA × pad_u 3 1 Sdag) × pad_u 3 0 Sdag).
    - symmetry; apply Mmult_assoc.
    - transitivity (pad_u 4 1 Sdag × (IA × pad_u 3 0 Sdag)).
      + rewrite Hinsert_alice_1; apply Mmult_assoc.
      + rewrite Hinsert_alice_0; symmetry; apply Mmult_assoc.
  }
  change (IA × (IB × C2) = C4 × (IA × IB)).
  transitivity (IA × (C3 × IB)).
  - rewrite Hbob_correction; reflexivity.
  - transitivity ((IA × C3) × IB).
    + symmetry; apply Mmult_assoc.
    + rewrite Halice_correction; apply Mmult_assoc.
Qed.

Lemma qgt_final_correction_insert_intertwine_current : forall x y,
  qgt_insert_alice x ×
    (qgt_insert_bob y × qgt_final_correction_two_current x y) =
  qgt_final_correction_current x y ×
    (qgt_insert_alice x × qgt_insert_bob y).
Proof.
  intros x y.
  set (S := phase_shift (PI / 2)).
  set (Sdag := phase_shift (- PI / 2)).
  set (IB := qgt_insert_bob y).
  set (IA := qgt_insert_alice x).
  destruct (Bool.eqb x y) eqn:Hxy.
  - set (C2 := pad_u 2 1 S × pad_u 2 0 Sdag).
    set (C3 := pad_u 3 1 S × pad_u 3 0 Sdag).
    set (C4 := pad_u 4 1 S × pad_u 4 0 Sdag).
    assert (Hinsert_bob_1 : IB × pad_u 2 1 S = pad_u 3 1 S × IB).
    { unfold IB, qgt_insert_bob, S.
      exact (@Hinsert_pad_u_intertwine 2 2 1 y (phase_shift (PI / 2))
        ltac:(lia) ltac:(lia) ltac:(auto with wf_db)). }
    assert (Hinsert_bob_0 : IB × pad_u 2 0 Sdag = pad_u 3 0 Sdag × IB).
    { unfold IB, qgt_insert_bob, Sdag.
      exact (@Hinsert_pad_u_intertwine 2 2 0 y (phase_shift (- PI / 2))
        ltac:(lia) ltac:(lia) ltac:(auto with wf_db)). }
    assert (Hinsert_alice_1 : IA × pad_u 3 1 S = pad_u 4 1 S × IA).
    { unfold IA, qgt_insert_alice, S.
      exact (@Hinsert_pad_u_intertwine 3 2 1 x (phase_shift (PI / 2))
        ltac:(lia) ltac:(lia) ltac:(auto with wf_db)). }
    assert (Hinsert_alice_0 : IA × pad_u 3 0 Sdag = pad_u 4 0 Sdag × IA).
    { unfold IA, qgt_insert_alice, Sdag.
      exact (@Hinsert_pad_u_intertwine 3 2 0 x (phase_shift (- PI / 2))
        ltac:(lia) ltac:(lia) ltac:(auto with wf_db)). }
    assert (Hbob_correction : IB × C2 = C3 × IB).
    {
      unfold C2, C3.
      transitivity ((IB × pad_u 2 1 S) × pad_u 2 0 Sdag).
      - symmetry; apply Mmult_assoc.
      - transitivity (pad_u 3 1 S × (IB × pad_u 2 0 Sdag)).
        + rewrite Hinsert_bob_1; apply Mmult_assoc.
        + rewrite Hinsert_bob_0; symmetry; apply Mmult_assoc.
    }
    assert (Halice_correction : IA × C3 = C4 × IA).
    {
      unfold C3, C4.
      transitivity ((IA × pad_u 3 1 S) × pad_u 3 0 Sdag).
      - symmetry; apply Mmult_assoc.
      - transitivity (pad_u 4 1 S × (IA × pad_u 3 0 Sdag)).
        + rewrite Hinsert_alice_1; apply Mmult_assoc.
        + rewrite Hinsert_alice_0; symmetry; apply Mmult_assoc.
    }
    unfold qgt_final_correction_two_current, qgt_final_correction_current.
    rewrite Hxy.
    change (IA × (IB × C2) = C4 × (IA × IB)).
    transitivity (IA × (C3 × IB)).
    + rewrite Hbob_correction; reflexivity.
    + transitivity ((IA × C3) × IB).
      * symmetry; apply Mmult_assoc.
      * rewrite Halice_correction; apply Mmult_assoc.
  - set (C2 := pad_u 2 1 Sdag × pad_u 2 0 S).
    set (C3 := pad_u 3 1 Sdag × pad_u 3 0 S).
    set (C4 := pad_u 4 1 Sdag × pad_u 4 0 S).
    assert (Hinsert_bob_1 : IB × pad_u 2 1 Sdag = pad_u 3 1 Sdag × IB).
    { unfold IB, qgt_insert_bob, Sdag.
      exact (@Hinsert_pad_u_intertwine 2 2 1 y (phase_shift (- PI / 2))
        ltac:(lia) ltac:(lia) ltac:(auto with wf_db)). }
    assert (Hinsert_bob_0 : IB × pad_u 2 0 S = pad_u 3 0 S × IB).
    { unfold IB, qgt_insert_bob, S.
      exact (@Hinsert_pad_u_intertwine 2 2 0 y (phase_shift (PI / 2))
        ltac:(lia) ltac:(lia) ltac:(auto with wf_db)). }
    assert (Hinsert_alice_1 : IA × pad_u 3 1 Sdag = pad_u 4 1 Sdag × IA).
    { unfold IA, qgt_insert_alice, Sdag.
      exact (@Hinsert_pad_u_intertwine 3 2 1 x (phase_shift (- PI / 2))
        ltac:(lia) ltac:(lia) ltac:(auto with wf_db)). }
    assert (Hinsert_alice_0 : IA × pad_u 3 0 S = pad_u 4 0 S × IA).
    { unfold IA, qgt_insert_alice, S.
      exact (@Hinsert_pad_u_intertwine 3 2 0 x (phase_shift (PI / 2))
        ltac:(lia) ltac:(lia) ltac:(auto with wf_db)). }
    assert (Hbob_correction : IB × C2 = C3 × IB).
    {
      unfold C2, C3.
      transitivity ((IB × pad_u 2 1 Sdag) × pad_u 2 0 S).
      - symmetry; apply Mmult_assoc.
      - transitivity (pad_u 3 1 Sdag × (IB × pad_u 2 0 S)).
        + rewrite Hinsert_bob_1; apply Mmult_assoc.
        + rewrite Hinsert_bob_0; symmetry; apply Mmult_assoc.
    }
    assert (Halice_correction : IA × C3 = C4 × IA).
    {
      unfold C3, C4.
      transitivity ((IA × pad_u 3 1 Sdag) × pad_u 3 0 S).
      - symmetry; apply Mmult_assoc.
      - transitivity (pad_u 4 1 Sdag × (IA × pad_u 3 0 S)).
        + rewrite Hinsert_alice_1; apply Mmult_assoc.
        + rewrite Hinsert_alice_0; symmetry; apply Mmult_assoc.
    }
    unfold qgt_final_correction_two_current, qgt_final_correction_current.
    rewrite Hxy.
    change (IA × (IB × C2) = C4 × (IA × IB)).
    transitivity (IA × (C3 × IB)).
    + rewrite Hbob_correction; reflexivity.
    + transitivity ((IA × C3) × IB).
      * symmetry; apply Mmult_assoc.
      * rewrite Halice_correction; apply Mmult_assoc.
Qed.

Lemma qgt_measured_branch_ray : forall (x y : bool)
    (input : Matrix 4 1) (alice_post : Matrix 8 1)
    (bob_pre : Matrix 8 1) (bob_post : Matrix 4 1),
  @ray_equiv 16 1
    (qgt_insert_alice x × alice_post)
    (proj 2 4 x ×
      (alice_pre_measure_operator_four ×
        (qgt_epr_preparation × input))) ->
  bob_pre = bob_pre_measure_operator_three × alice_post ->
  @ray_equiv 8 1
    (qgt_insert_bob y × bob_post)
    (proj 2 3 y × bob_pre) ->
  @ray_equiv 16 1
    (qgt_insert_alice x ×
      (qgt_insert_bob y × (qgt_final_correction_two × bob_post)))
    (qgt_full_branch x y × input).
Proof.
  intros x y input alice_post bob_pre bob_post Halice Hbob_pre Hbob.
  set (P_alice := proj 2 4 x).
  set (P_bob_three := proj 2 3 y).
  set (P_bob_four := proj 3 4 y).
  set (B_three := bob_pre_measure_operator_three).
  set (B_four := bob_pre_measure_operator_four).
  set (IA := qgt_insert_alice x).
  set (IB := qgt_insert_bob y).
  set (C2 := qgt_final_correction_two).
  set (C4 := qgt_final_correction).
  assert (Hbob_lifted : @ray_equiv 16 1
      (qgt_insert_alice x × (qgt_insert_bob y × bob_post))
      (qgt_insert_alice x × (P_bob_three × bob_pre))).
  {
    exact (@ray_equiv_linear 16 8 1 (qgt_insert_alice x)
      (qgt_insert_bob y × bob_post) (P_bob_three × bob_pre) Hbob).
  }
  assert (Hprojector_intertwine :
      qgt_insert_alice x × (P_bob_three × bob_pre) =
      P_bob_four × (qgt_insert_alice x × bob_pre)).
  {
    unfold P_bob_three, P_bob_four, qgt_insert_alice.
    transitivity ((insert_measured_wire_operator 3 2 x × proj 2 3 y) × bob_pre).
    - symmetry; apply Mmult_assoc.
    - rewrite (insert_measured_wire_projector_intertwine x y) at 1.
      apply Mmult_assoc.
  }
  assert (Hbob_intertwine :
      qgt_insert_alice x × bob_pre =
      B_four × (qgt_insert_alice x × alice_post)).
  {
    rewrite Hbob_pre.
    unfold B_three, B_four, qgt_insert_alice.
    transitivity
      ((insert_measured_wire_operator 3 2 x × bob_pre_measure_operator_three) × alice_post).
    - symmetry; apply Mmult_assoc.
    - rewrite (insert_measured_wire_bob_pre_measure_intertwine x) at 1.
      apply Mmult_assoc.
  }
  assert (Hprojected_bob : @ray_equiv 16 1
      (P_bob_four × (B_four × (qgt_insert_alice x × alice_post)))
      (P_bob_four ×
        (B_four × (P_alice ×
          (alice_pre_measure_operator_four ×
            (qgt_epr_preparation × input)))))).
  {
    pose proof (@ray_equiv_linear 16 16 1 B_four
      (qgt_insert_alice x × alice_post)
      (P_alice ×
        (alice_pre_measure_operator_four ×
          (qgt_epr_preparation × input))) Halice) as Hbob_linear.
    exact (@ray_equiv_linear 16 16 1 P_bob_four
      (B_four × (qgt_insert_alice x × alice_post))
      (B_four ×
        (P_alice ×
          (alice_pre_measure_operator_four ×
            (qgt_epr_preparation × input)))) Hbob_linear).
  }
  assert (Hbefore_correction : @ray_equiv 16 1
      (qgt_insert_alice x × (qgt_insert_bob y × bob_post))
      (P_bob_four ×
        (B_four × (P_alice ×
          (alice_pre_measure_operator_four ×
            (qgt_epr_preparation × input)))))).
  {
    eapply ray_equiv_trans; [exact Hbob_lifted|].
    eapply ray_equiv_trans.
    - rewrite Hprojector_intertwine, Hbob_intertwine.
      apply ray_equiv_refl.
    - exact Hprojected_bob.
  }
  assert (Hcorrection_lift :
      IA × (IB × (C2 × bob_post)) =
      C4 × (IA × (IB × bob_post))).
  {
    transitivity ((IA × (IB × C2)) × bob_post).
    - rewrite <- (Mmult_assoc IB C2 bob_post) at 1.
      symmetry; apply Mmult_assoc.
    - transitivity ((C4 × (IA × IB)) × bob_post).
      + unfold IA, IB, C2, C4.
        rewrite qgt_final_correction_insert_intertwine.
        reflexivity.
      + transitivity (C4 × ((IA × IB) × bob_post)).
        * apply Mmult_assoc.
        * f_equal; apply Mmult_assoc.
  }
  assert (Hfull_expand :
      qgt_full_branch x y × input =
      C4 × (P_bob_four ×
        (B_four × (P_alice ×
          (alice_pre_measure_operator_four ×
            (qgt_epr_preparation × input)))))).
  {
    unfold qgt_full_branch.
    repeat rewrite Mmult_assoc.
    reflexivity.
  }
  eapply ray_equiv_trans.
  - rewrite Hcorrection_lift.
    apply ray_equiv_refl.
  - eapply ray_equiv_trans.
    + exact (@ray_equiv_linear 16 16 1 C4
        (IA × (IB × bob_post))
        (P_bob_four ×
          (B_four × (P_alice ×
            (alice_pre_measure_operator_four ×
              (qgt_epr_preparation × input))))) Hbefore_correction).
    + rewrite Hfull_expand.
      apply ray_equiv_refl.
Qed.

Lemma qgt_measured_branch_ray_dag : forall (x y : bool)
    (input : Matrix 4 1) (alice_post : Matrix 8 1)
    (bob_pre : Matrix 8 1) (bob_post : Matrix 4 1),
  @ray_equiv 16 1
    (qgt_insert_alice x × alice_post)
    (proj 2 4 x ×
      (alice_pre_measure_operator_four ×
        (qgt_epr_preparation × input))) ->
  bob_pre = bob_pre_measure_operator_three × alice_post ->
  @ray_equiv 8 1
    (qgt_insert_bob y × bob_post)
    (proj 2 3 y × bob_pre) ->
  @ray_equiv 16 1
    (qgt_insert_alice x ×
      (qgt_insert_bob y × (qgt_final_correction_two_dag × bob_post)))
    (qgt_full_branch_dag x y × input).
Proof.
  intros x y input alice_post bob_pre bob_post Halice Hbob_pre Hbob.
  set (P_alice := proj 2 4 x).
  set (P_bob_three := proj 2 3 y).
  set (P_bob_four := proj 3 4 y).
  set (B_three := bob_pre_measure_operator_three).
  set (B_four := bob_pre_measure_operator_four).
  set (IA := qgt_insert_alice x).
  set (IB := qgt_insert_bob y).
  set (C2 := qgt_final_correction_two_dag).
  set (C4 := qgt_final_correction_dag).
  assert (Hbob_lifted : @ray_equiv 16 1
      (qgt_insert_alice x × (qgt_insert_bob y × bob_post))
      (qgt_insert_alice x × (P_bob_three × bob_pre))).
  {
    exact (@ray_equiv_linear 16 8 1 (qgt_insert_alice x)
      (qgt_insert_bob y × bob_post) (P_bob_three × bob_pre) Hbob).
  }
  assert (Hprojector_intertwine :
      qgt_insert_alice x × (P_bob_three × bob_pre) =
      P_bob_four × (qgt_insert_alice x × bob_pre)).
  {
    unfold P_bob_three, P_bob_four, qgt_insert_alice.
    transitivity ((insert_measured_wire_operator 3 2 x × proj 2 3 y) × bob_pre).
    - symmetry; apply Mmult_assoc.
    - rewrite (insert_measured_wire_projector_intertwine x y) at 1.
      apply Mmult_assoc.
  }
  assert (Hbob_intertwine :
      qgt_insert_alice x × bob_pre =
      B_four × (qgt_insert_alice x × alice_post)).
  {
    rewrite Hbob_pre.
    unfold B_three, B_four, qgt_insert_alice.
    transitivity
      ((insert_measured_wire_operator 3 2 x × bob_pre_measure_operator_three) × alice_post).
    - symmetry; apply Mmult_assoc.
    - rewrite (insert_measured_wire_bob_pre_measure_intertwine x) at 1.
      apply Mmult_assoc.
  }
  assert (Hprojected_bob : @ray_equiv 16 1
      (P_bob_four × (B_four × (qgt_insert_alice x × alice_post)))
      (P_bob_four ×
        (B_four × (P_alice ×
          (alice_pre_measure_operator_four ×
            (qgt_epr_preparation × input)))))).
  {
    pose proof (@ray_equiv_linear 16 16 1 B_four
      (qgt_insert_alice x × alice_post)
      (P_alice ×
        (alice_pre_measure_operator_four ×
          (qgt_epr_preparation × input))) Halice) as Hbob_linear.
    exact (@ray_equiv_linear 16 16 1 P_bob_four
      (B_four × (qgt_insert_alice x × alice_post))
      (B_four ×
        (P_alice ×
          (alice_pre_measure_operator_four ×
            (qgt_epr_preparation × input)))) Hbob_linear).
  }
  assert (Hbefore_correction : @ray_equiv 16 1
      (qgt_insert_alice x × (qgt_insert_bob y × bob_post))
      (P_bob_four ×
        (B_four × (P_alice ×
          (alice_pre_measure_operator_four ×
            (qgt_epr_preparation × input)))))).
  {
    eapply ray_equiv_trans; [exact Hbob_lifted|].
    eapply ray_equiv_trans.
    - rewrite Hprojector_intertwine, Hbob_intertwine.
      apply ray_equiv_refl.
    - exact Hprojected_bob.
  }
  assert (Hcorrection_lift :
      IA × (IB × (C2 × bob_post)) =
      C4 × (IA × (IB × bob_post))).
  {
    transitivity ((IA × (IB × C2)) × bob_post).
    - rewrite <- (Mmult_assoc IB C2 bob_post) at 1.
      symmetry; apply Mmult_assoc.
    - transitivity ((C4 × (IA × IB)) × bob_post).
      + unfold IA, IB, C2, C4.
        rewrite qgt_final_correction_insert_intertwine_dag.
        reflexivity.
      + transitivity (C4 × ((IA × IB) × bob_post)).
        * apply Mmult_assoc.
        * f_equal; apply Mmult_assoc.
  }
  assert (Hfull_expand :
      qgt_full_branch_dag x y × input =
      C4 × (P_bob_four ×
        (B_four × (P_alice ×
          (alice_pre_measure_operator_four ×
            (qgt_epr_preparation × input)))))).
  {
    unfold qgt_full_branch_dag.
    repeat rewrite Mmult_assoc.
    reflexivity.
  }
  eapply ray_equiv_trans.
  - rewrite Hcorrection_lift.
    apply ray_equiv_refl.
  - eapply ray_equiv_trans.
    + exact (@ray_equiv_linear 16 16 1 C4
        (IA × (IB × bob_post))
        (P_bob_four ×
          (B_four × (P_alice ×
            (alice_pre_measure_operator_four ×
              (qgt_epr_preparation × input))))) Hbefore_correction).
    + rewrite Hfull_expand.
      apply ray_equiv_refl.
Qed.

Lemma qgt_measured_branch_ray_current : forall (x y : bool)
    (input : Matrix 4 1) (alice_post : Matrix 8 1)
    (bob_pre : Matrix 8 1) (bob_post : Matrix 4 1),
  @ray_equiv 16 1
    (qgt_insert_alice x × alice_post)
    (proj 2 4 x ×
      (alice_pre_measure_operator_four_current ×
        (qgt_epr_preparation_current × input))) ->
  bob_pre = bob_pre_measure_operator_three × alice_post ->
  @ray_equiv 8 1
    (qgt_insert_bob y × bob_post)
    (proj 2 3 y × bob_pre) ->
  @ray_equiv 16 1
    (qgt_insert_alice x ×
      (qgt_insert_bob y ×
        (qgt_final_correction_two_current x y × bob_post)))
    (qgt_full_branch_current x y × input).
Proof.
  intros x y input alice_post bob_pre bob_post Halice Hbob_pre Hbob.
  set (P_alice := proj 2 4 x).
  set (P_bob_three := proj 2 3 y).
  set (P_bob_four := proj 3 4 y).
  set (B_three := bob_pre_measure_operator_three).
  set (B_four := bob_pre_measure_operator_four).
  set (IA := qgt_insert_alice x).
  set (IB := qgt_insert_bob y).
  set (C2 := qgt_final_correction_two_current x y).
  set (C4 := qgt_final_correction_current x y).
  assert (Hbob_lifted : @ray_equiv 16 1
      (qgt_insert_alice x × (qgt_insert_bob y × bob_post))
      (qgt_insert_alice x × (P_bob_three × bob_pre))).
  {
    exact (@ray_equiv_linear 16 8 1 (qgt_insert_alice x)
      (qgt_insert_bob y × bob_post) (P_bob_three × bob_pre) Hbob).
  }
  assert (Hprojector_intertwine :
      qgt_insert_alice x × (P_bob_three × bob_pre) =
      P_bob_four × (qgt_insert_alice x × bob_pre)).
  {
    unfold P_bob_three, P_bob_four, qgt_insert_alice.
    transitivity ((insert_measured_wire_operator 3 2 x × proj 2 3 y) × bob_pre).
    - symmetry; apply Mmult_assoc.
    - rewrite (insert_measured_wire_projector_intertwine x y) at 1.
      apply Mmult_assoc.
  }
  assert (Hbob_intertwine :
      qgt_insert_alice x × bob_pre =
      B_four × (qgt_insert_alice x × alice_post)).
  {
    rewrite Hbob_pre.
    unfold B_three, B_four, qgt_insert_alice.
    transitivity
      ((insert_measured_wire_operator 3 2 x × bob_pre_measure_operator_three) × alice_post).
    - symmetry; apply Mmult_assoc.
    - rewrite (insert_measured_wire_bob_pre_measure_intertwine x) at 1.
      apply Mmult_assoc.
  }
  assert (Hprojected_bob : @ray_equiv 16 1
      (P_bob_four × (B_four × (qgt_insert_alice x × alice_post)))
      (P_bob_four ×
        (B_four × (P_alice ×
          (alice_pre_measure_operator_four_current ×
            (qgt_epr_preparation_current × input)))))).
  {
    pose proof (@ray_equiv_linear 16 16 1 B_four
      (qgt_insert_alice x × alice_post)
      (P_alice ×
        (alice_pre_measure_operator_four_current ×
          (qgt_epr_preparation_current × input))) Halice) as Hbob_linear.
    exact (@ray_equiv_linear 16 16 1 P_bob_four
      (B_four × (qgt_insert_alice x × alice_post))
      (B_four ×
        (P_alice ×
          (alice_pre_measure_operator_four_current ×
            (qgt_epr_preparation_current × input)))) Hbob_linear).
  }
  assert (Hbefore_correction : @ray_equiv 16 1
      (qgt_insert_alice x × (qgt_insert_bob y × bob_post))
      (P_bob_four ×
        (B_four × (P_alice ×
          (alice_pre_measure_operator_four_current ×
            (qgt_epr_preparation_current × input)))))).
  {
    eapply ray_equiv_trans; [exact Hbob_lifted|].
    eapply ray_equiv_trans.
    - rewrite Hprojector_intertwine, Hbob_intertwine.
      apply ray_equiv_refl.
    - exact Hprojected_bob.
  }
  assert (Hcorrection_lift :
      IA × (IB × (C2 × bob_post)) =
      C4 × (IA × (IB × bob_post))).
  {
    transitivity ((IA × (IB × C2)) × bob_post).
    - rewrite <- (Mmult_assoc IB C2 bob_post) at 1.
      symmetry; apply Mmult_assoc.
    - transitivity ((C4 × (IA × IB)) × bob_post).
      + unfold IA, IB, C2, C4.
        rewrite qgt_final_correction_insert_intertwine_current.
        reflexivity.
      + transitivity (C4 × ((IA × IB) × bob_post)).
        * apply Mmult_assoc.
        * f_equal; apply Mmult_assoc.
  }
  assert (Hfull_expand :
      qgt_full_branch_current x y × input =
      C4 × (P_bob_four ×
        (B_four × (P_alice ×
          (alice_pre_measure_operator_four_current ×
            (qgt_epr_preparation_current × input)))))).
  {
    unfold qgt_full_branch_current.
    repeat rewrite Mmult_assoc.
    reflexivity.
  }
  eapply ray_equiv_trans.
  - rewrite Hcorrection_lift.
    apply ray_equiv_refl.
  - eapply ray_equiv_trans.
    + exact (@ray_equiv_linear 16 16 1 C4
        (IA × (IB × bob_post))
        (P_bob_four ×
          (B_four × (P_alice ×
            (alice_pre_measure_operator_four_current ×
              (qgt_epr_preparation_current × input))))) Hbefore_correction).
    + rewrite Hfull_expand.
      apply ray_equiv_refl.
Qed.

Lemma qgt_cdividend_nonzero : forall (x y : bool),
  Bool.eqb x y = false -> qgt_branch_scalar x y <> 0.
Proof.
  intros x y Hxy.
  unfold qgt_branch_scalar.
  rewrite Hxy.
  apply Cdiv_nonzero.
  - intro Hnum.
    apply (f_equal (@fst R R)) in Hnum.
    simpl in Hnum.
    lra.
  - rewrite <- RtoC_mult.
    apply RtoC_neq.
    intro Hden.
    apply Rmult_integral in Hden.
    destruct Hden as [Hden | Hden].
    + lra.
    + assert (Hsqrt : sqrt 2 <> 0).
      { apply sqrt_neq_0_compat; lra. }
      contradiction.
Qed.

Lemma qgt_cdividend_nonzero_equal : forall (x y : bool),
  Bool.eqb x y = true -> qgt_branch_scalar x y <> 0.
Proof.
  intros x y Hxy.
  unfold qgt_branch_scalar.
  rewrite Hxy.
  apply Cdiv_nonzero.
  - intro Hnum.
    apply (f_equal (@fst R R)) in Hnum.
    simpl in Hnum.
    lra.
  - rewrite <- RtoC_mult.
    apply RtoC_neq.
    intro Hden.
    apply Rmult_integral in Hden.
    destruct Hden as [Hden | Hden].
    + lra.
    + assert (Hsqrt : sqrt 2 <> 0).
      { apply sqrt_neq_0_compat; lra. }
      contradiction.
Qed.

Lemma qgt_kron_apply_right_vector : forall m n
    (A : Matrix m m) (B : Matrix n 1) (v : Matrix m 1),
  WF_Matrix B -> WF_Matrix v ->
  (A ⊗ B) × v = (A × v) ⊗ B.
Proof.
  intros m n A B v HB Hv.
  replace v with (v ⊗ I 1) at 1 by
    (rewrite kron_1_r by exact Hv; reflexivity).
  transitivity ((A × v) ⊗ (B × I 1)).
  - exact (@kron_mixed_product m m 1 n 1 1 A B v (I 1)).
  - rewrite Mmult_1_r by exact HB.
    reflexivity.
Qed.

Lemma qgt_current_branch_input : forall (x y : bool) (input : Matrix 4 1),
  WF_Matrix input ->
  qgt_full_branch_current x y × input =
    qgt_current_branch_scalar x y .*
      (cz × input ⊗
        (ket (if x then 1 else 0) ⊗ ket (if y then 1 else 0))).
Proof.
  intros x y input Hinput.
  rewrite qgt_current_branch_matrix.
  rewrite Mscale_mult_dist_l.
  rewrite qgt_kron_apply_right_vector.
  - reflexivity.
  - repeat apply WF_kron; try apply qgt_cz_wf; auto with wf_db.
  - exact Hinput.
Qed.

Lemma qgt_current_branch_scalar_nonzero : forall x y,
  qgt_current_branch_scalar x y <> 0.
Proof.
  intros x y.
  unfold qgt_current_branch_scalar.
  destruct (Bool.eqb x y); apply Cdiv_nonzero.
  - intro Hnum.
    apply (f_equal (@fst R R)) in Hnum.
    destruct x; simpl in Hnum; lra.
  - rewrite <- RtoC_mult.
    apply RtoC_neq.
    intro Hden.
    apply Rmult_integral in Hden.
    destruct Hden as [Hden | Hden].
    + lra.
    + assert (Hsqrt : sqrt 2 <> 0).
      { apply sqrt_neq_0_compat; lra. }
      contradiction.
  - intro Hnum.
    apply (f_equal (@fst R R)) in Hnum.
    destruct x; simpl in Hnum; lra.
  - rewrite <- RtoC_mult.
    apply RtoC_neq.
    intro Hden.
    apply Rmult_integral in Hden.
    destruct Hden as [Hden | Hden].
    + lra.
    + assert (Hsqrt : sqrt 2 <> 0).
      { apply sqrt_neq_0_compat; lra. }
      contradiction.
Qed.

Lemma qgt_append_ket : forall n (b : bool) (v : Matrix (2 ^ n) 1),
  WF_Matrix v ->
  (I (2 ^ n) ⊗ ket (if b then 1 else 0)) × v =
    v ⊗ ket (if b then 1 else 0).
Proof.
  intros n b v Hv.
  rewrite qgt_kron_apply_right_vector.
  - rewrite Mmult_1_l by exact Hv.
    reflexivity.
  - auto with wf_db.
  - exact Hv.
Qed.

Lemma qgt_insert_last_wire_two : forall (b : bool) (v : Matrix 4 1),
  WF_Matrix v ->
  insert_measured_wire_operator 2 2 b × v =
    v ⊗ ket (if b then 1 else 0).
Proof.
  intros b v Hv.
  unfold insert_measured_wire_operator.
  replace (2 - 2)%nat with 0%nat by reflexivity.
  simpl Nat.pow.
  rewrite kron_1_r by (repeat apply WF_kron; auto with wf_db).
  exact (@qgt_append_ket 2 b v Hv).
Qed.

Lemma qgt_insert_output_pair_tensor : forall (x y : bool)
    (v : Matrix 4 1),
  WF_Matrix v ->
  qgt_insert_alice x × (qgt_insert_bob y × v) =
    (v ⊗ ket (if x then 1 else 0)) ⊗ ket (if y then 1 else 0).
Proof.
  intros x y v Hv.
  unfold qgt_insert_alice, qgt_insert_bob.
  change (insert_measured_wire_operator 3 2 x ×
    (insert_measured_wire_operator 2 2 y × v) =
    (v ⊗ ket (if x then 1 else 0)) ⊗ ket (if y then 1 else 0)).
  rewrite (qgt_insert_last_wire_two y v Hv).
  change (((I 4 ⊗ ket (if x then 1 else 0)) ⊗ I 2) ×
      (v ⊗ ket (if y then 1 else 0)) =
    (v ⊗ ket (if x then 1 else 0)) ⊗ ket (if y then 1 else 0)).
  transitivity (((I 4 ⊗ ket (if x then 1 else 0)) × v) ⊗
    (I 2 × ket (if y then 1 else 0))).
  - exact (@kron_mixed_product 8 4 1 2 2 1
      (I 4 ⊗ ket (if x then 1 else 0)) (I 2) v
      (ket (if y then 1 else 0))).
  - rewrite Mmult_1_l by auto with wf_db.
    f_equal.
    + exact (@qgt_append_ket 2 x v Hv).
Qed.

Lemma qgt_full_branch_input : forall (x y : bool) (input : Matrix 4 1),
  WF_Matrix input ->
  Bool.eqb x y = false ->
  qgt_full_branch x y × input =
    qgt_branch_scalar x y .*
      ((cz × input) ⊗
        (ket (if x then 1 else 0) ⊗ ket (if y then 1 else 0))).
Proof.
  intros x y input Hinput Hxy.
  rewrite qgt_full_branch_matrix by exact Hxy.
  rewrite Mscale_mult_dist_l.
  rewrite qgt_kron_apply_right_vector.
  - reflexivity.
  - repeat apply WF_kron; try apply qgt_cz_wf; auto with wf_db.
  - exact Hinput.
Qed.

Lemma qgt_full_branch_dag_input : forall (x y : bool) (input : Matrix 4 1),
  WF_Matrix input ->
  Bool.eqb x y = true ->
  qgt_full_branch_dag x y × input =
    qgt_branch_scalar x y .*
      ((cz × input) ⊗
        (ket (if x then 1 else 0) ⊗ ket (if y then 1 else 0))).
Proof.
  intros x y input Hinput Hxy.
  rewrite qgt_full_branch_dag_matrix by exact Hxy.
  rewrite Mscale_mult_dist_l.
  rewrite qgt_kron_apply_right_vector.
  - reflexivity.
  - repeat apply WF_kron; try apply qgt_cz_wf; auto with wf_db.
  - exact Hinput.
Qed.

Lemma qgt_remove_output_pair : forall (x y : bool) (v : Matrix 4 1),
  WF_Matrix v ->
  (remove_measured_wire_operator 2 2 y ×
    remove_measured_wire_operator 3 2 x) ×
  (qgt_insert_alice x × (qgt_insert_bob y × v)) = v.
Proof.
  intros x y v Hv.
  set (RA := remove_measured_wire_operator 3 2 x).
  set (RB := remove_measured_wire_operator 2 2 y).
  set (IA := insert_measured_wire_operator 3 2 x).
  set (IB := insert_measured_wire_operator 2 2 y).
  transitivity (RB × ((RA × IA) × (IB × v))).
  - unfold RA, RB, IA, IB, qgt_insert_alice, qgt_insert_bob.
    transitivity (remove_measured_wire_operator 2 2 y ×
      (remove_measured_wire_operator 3 2 x ×
        (insert_measured_wire_operator 3 2 x ×
          (insert_measured_wire_operator 2 2 y × v)))).
    + apply Mmult_assoc.
    + f_equal; symmetry; apply Mmult_assoc.
  - unfold RA, RB, IA, IB, qgt_insert_alice, qgt_insert_bob.
    change (@Mmult 4 8 4 (remove_measured_wire_operator 2 2 y)
      (@Mmult 8 8 4
        (@Mmult 8 16 8 (remove_measured_wire_operator 3 2 x)
          (insert_measured_wire_operator 3 2 x))
        (@Mmult 8 4 1 (insert_measured_wire_operator 2 2 y) v)) = v).
    assert (HcancelA :
      @Mmult 8 16 8 (remove_measured_wire_operator 3 2 x)
        (insert_measured_wire_operator 3 2 x) = I 8).
    { exact (@remove_insert_measured_wire_operator 3 2 x ltac:(lia)). }
    rewrite HcancelA.
    assert (HwfIBv : WF_Matrix
      (insert_measured_wire_operator 2 2 y × v)).
    {
      exact (@WF_mult 8 4 1 (insert_measured_wire_operator 2 2 y) v
        (@insert_measured_wire_operator_wf 2 2 y ltac:(lia)) Hv).
    }
    transitivity (remove_measured_wire_operator 2 2 y ×
      (insert_measured_wire_operator 2 2 y × v)).
    + exact (f_equal
        (fun z : Matrix 8 1 => remove_measured_wire_operator 2 2 y × z)
        (@Mmult_1_l 8 1
          (insert_measured_wire_operator 2 2 y × v) HwfIBv)).
    + rewrite <- Mmult_assoc.
      change (@Mmult 4 4 1
        (@Mmult 4 8 4 (remove_measured_wire_operator 2 2 y)
          (insert_measured_wire_operator 2 2 y)) v = v).
    assert (HcancelB :
      @Mmult 4 8 4 (remove_measured_wire_operator 2 2 y)
        (insert_measured_wire_operator 2 2 y) = I 4).
    { exact (@remove_insert_measured_wire_operator 2 2 y ltac:(lia)). }
    rewrite HcancelB.
      rewrite (@Mmult_1_l 4 1 v Hv).
      reflexivity.
Qed.

End QGTPath1HelperDefinitions.
Export QGTPath1HelperDefinitions.
Close Scope C_scope.
Close Scope R_scope.

(* Merged from FCTwoStepDecompose.v. *)
Require Import Lia Permutation String Coq.Program.Equality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import SST session QUEST QuantumGateTeleportation ExamplesHelpers FunctionalCorrectnessHelpers.
From SQIR Require Import SQIR.
Require Import SQIR.UnitaryOps SQIR.Equivalences.
Open Scope nat_scope.
Lemma step_tau_decompose : forall qs M actor qs' M' r,
  step (qs,M) (Tau actor) (qs',M') r ->
  exists Mbase Mcore,
    unfoldM M Mbase /\
    step (qs,Mbase) (Tau actor) (qs',Mcore) r /\
    unfoldM Mcore M'.
Proof.
  intros qs M actor qs' M' r Hstep.
  dependent induction Hstep; try discriminate.
  - exists M, s2; split; [apply unfoldM_refl|].
    split; [eapply New; eauto|apply unfoldM_refl].
  - exists M, s2; split; [apply unfoldM_refl|].
    split; [eapply If_0; eauto|apply unfoldM_refl].
  - exists M, s2; split; [apply unfoldM_refl|].
    split; [eapply If_1; eauto|apply unfoldM_refl].
  - exists M, s2; split; [apply unfoldM_refl|].
    split; [eapply Meas; eauto; reflexivity|apply unfoldM_refl].
  - exists M, (insert M actor P); split; [apply unfoldM_refl|].
    split; [eapply Unitary; eauto|apply unfoldM_refl].
  - destruct (IHHstep qs M1' actor qs' M' ltac:(reflexivity) eq_refl ltac:(reflexivity))
      as [Mbase [Mcore [Hbase [Hcore Hout]]]].
    exists Mbase, Mcore; split.
    + eapply unfoldM_trans; eauto.
    + split; [exact Hcore|exact Hout].
Qed.

(* Merged from FCTwoMeasurementCommute.v. *)
Require Import Lia.
Require Import Arith.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import SST session QUEST QuantumGateTeleportation ExamplesHelpers FunctionalCorrectnessHelpers.
From SQIR Require Import SQIR UnitaryOps Equivalences.
Open Scope nat_scope.

Definition measurement_contraction (n i : nat) (b : bool)
    : Matrix (2 ^ n) (2 ^ (S n)) :=
  @Mmult (2 ^ n) (2 ^ (S n)) (2 ^ (S n))
    (remove_measured_wire_operator n i b) (proj i (S n) b).

Lemma bra_projector_same_probe : forall (b : bool),
  @Mmult 1 2 2 (bra (if b then 1%nat else 0%nat)) (bool_to_matrix b) =
    bra (if b then 1%nat else 0%nat).
Proof.
  intros []; cbn [bool_to_matrix bra].
  - rewrite <- Mmult_assoc.
    transitivity (I 1 × bra 1).
    + exact (f_equal (fun X : Square 1 => X × bra 1) bra1ket1).
    + rewrite Mmult_1_l by auto with wf_db.
      reflexivity.
  - rewrite <- Mmult_assoc.
    transitivity (I 1 × bra 0).
    + exact (f_equal (fun X : Square 1 => X × bra 0) bra0ket0).
    + rewrite Mmult_1_l by auto with wf_db.
      reflexivity.
Qed.

Lemma pad_u_last_factor_probe : forall n i (U : Square 2),
    i < n -> WF_Matrix U ->
    pad_u (S n) i U = pad_u n i U ⊗ I 2.
Proof.
  intros n i U Hi HU.
  pose proof (Hpad_u_split_left (S n) n i U HU ltac:(lia) ltac:(lia)) as H.
  replace (S n - n) with 1 in H by lia.
  simpl in H.
  exact H.
Qed.

Lemma remove_operator_last_factor_probe : forall n i b,
    i < n ->
    remove_measured_wire_operator n i b =
      remove_measured_wire_operator (n-1) i b ⊗ I 2.
Proof.
  intros n i b Hi.
  unfold remove_measured_wire_operator.
  replace (n - i) with (S (n - 1 - i)) by lia.
  rewrite Nat.pow_succ_r by lia.
  replace (2 * 2 ^ (n - 1 - i)) with (2 ^ (n - 1 - i) * 2) by nia.
  rewrite <- (id_kron (2 ^ (n - 1 - i)) 2).
  symmetry.
  rewrite <- kron_assoc by auto with wf_db.
  reflexivity.
Qed.

Lemma measurement_contraction_last_factor_probe : forall n i b,
    i < n ->
    measurement_contraction (S n) i b =
      measurement_contraction n i b ⊗ I 2.
Proof.
  intros n i b Hi.
  unfold measurement_contraction, proj.
  rewrite remove_operator_last_factor_probe by lia.
  rewrite pad_u_last_factor_probe by (lia || auto with wf_db).
  replace (S n - 1) with n by lia.
  transitivity (@Mmult (2 ^ n * 2) (2 ^ (S n) * 2) (2 ^ (S n) * 2)
    (remove_measured_wire_operator n i b ⊗ I 2)
    (pad_u (S n) i (bool_to_matrix b) ⊗ I 2)).
  - apply (@Mmult_change_dims (2 ^ (S n)) (2 ^ n * 2)
      (2 ^ (S (S n))) (2 ^ (S n) * 2)
      (2 ^ (S (S n))) (2 ^ (S n) * 2)
      (remove_measured_wire_operator n i b ⊗ I 2)
      (pad_u (S n) i (bool_to_matrix b) ⊗ I 2)).
    + rewrite Nat.pow_succ_r; nia.
    + rewrite Nat.pow_succ_r; nia.
    + rewrite Nat.pow_succ_r; nia.
  - transitivity (@kron (2 ^ n) (2 ^ (S n)) 2 2
      (@Mmult (2 ^ n) (2 ^ (S n)) (2 ^ (S n))
        (remove_measured_wire_operator n i b)
        (pad_u (S n) i (bool_to_matrix b)))
      (@Mmult 2 2 2 (I 2) (I 2))).
    + exact (@kron_mixed_product (2 ^ n) (2 ^ (S n)) (2 ^ (S n))
        2 2 2 (remove_measured_wire_operator n i b) (I 2)
          (pad_u (S n) i (bool_to_matrix b)) (I 2)).
    + rewrite Mmult_1_l by auto with wf_db.
      reflexivity.
Qed.

Lemma remove_operator_penultimate_factor_probe : forall n b,
    remove_measured_wire_operator (S n) n b =
      remove_measured_wire_operator n n b ⊗ I 2.
Proof.
  intros n b.
  unfold remove_measured_wire_operator.
  replace (S n - n) with 1 by lia.
  replace (n - n) with 0 by lia.
  simpl.
  rewrite kron_1_r.
  reflexivity.
Qed.

Lemma kron_identity_compose_probe : forall m n p
    (A : Matrix m n) (B : Matrix n p),
    @Mmult (m * 2) (n * 2) (p * 2) (A ⊗ I 2) (B ⊗ I 2) =
      (@Mmult m n p A B) ⊗ I 2.
Proof.
  intros m n p A B.
  transitivity (@kron m p 2 2
    (@Mmult m n p A B) (@Mmult 2 2 2 (I 2) (I 2))).
  - exact (@kron_mixed_product m n p 2 2 2 A (I 2) B (I 2)).
  - rewrite Mmult_1_l by auto with wf_db.
    reflexivity.
Qed.

Lemma kron_identity_compose_power_probe : forall k
    (A : Matrix (2 ^ k) (2 ^ (S k)))
    (B : Matrix (2 ^ (S k)) (2 ^ (S (S k)))),
    @Mmult (2 ^ (S k)) (2 ^ (S (S k))) (2 ^ (S (S (S k))))
      (A ⊗ I 2) (B ⊗ I 2) =
    (@Mmult (2 ^ k) (2 ^ (S k)) (2 ^ (S (S k))) A B) ⊗ I 2.
Proof.
  intros k A B.
  transitivity (@Mmult (2 ^ k * 2) (2 ^ (S k) * 2)
      (2 ^ (S (S k)) * 2) (A ⊗ I 2) (B ⊗ I 2)).
  - symmetry.
    apply (@Mmult_change_dims (2 ^ k * 2) (2 ^ (S k))
      (2 ^ (S k) * 2) (2 ^ (S (S k)))
      (2 ^ (S (S k)) * 2) (2 ^ (S (S (S k))))
      (A ⊗ I 2) (B ⊗ I 2)).
    + rewrite Nat.pow_succ_r; nia.
    + rewrite (Nat.pow_succ_r 2 (S k) ltac:(lia)).
      apply Nat.mul_comm.
    + rewrite (Nat.pow_succ_r 2 (S (S k)) ltac:(lia)).
      apply Nat.mul_comm.
  - apply kron_identity_compose_probe.
Qed.

Lemma projector_penultimate_factor_probe : forall n b,
    proj n (S (S n)) b = proj n (S n) b ⊗ I 2.
Proof.
  intros n b.
  unfold proj.
  rewrite (Hpad_u_split_left (S (S n)) (S n) n (bool_to_matrix b)
    ltac:(destruct b; unfold bool_to_matrix; auto with wf_db)
    ltac:(lia) ltac:(lia)).
  replace (S (S n) - S n) with 1 by lia.
  simpl.
  reflexivity.
Qed.

Lemma measurement_contraction_penultimate_factor_probe : forall n b,
    measurement_contraction (S n) n b =
      measurement_contraction n n b ⊗ I 2.
Proof.
  intros n b.
  unfold measurement_contraction.
  rewrite remove_operator_penultimate_factor_probe.
  rewrite projector_penultimate_factor_probe.
  transitivity (@Mmult (2 ^ n * 2) (2 ^ (S n) * 2) (2 ^ (S n) * 2)
    (remove_measured_wire_operator n n b ⊗ I 2)
    (proj n (S n) b ⊗ I 2)).
  - apply (@Mmult_change_dims (2 ^ (S n)) (2 ^ n * 2)
      (2 ^ (S (S n))) (2 ^ (S n) * 2)
      (2 ^ (S (S n))) (2 ^ (S n) * 2)
      (remove_measured_wire_operator n n b ⊗ I 2)
      (proj n (S n) b ⊗ I 2)).
    + rewrite Nat.pow_succ_r; nia.
    + rewrite Nat.pow_succ_r; nia.
    + rewrite Nat.pow_succ_r; nia.
  - apply (kron_identity_compose_probe (2 ^ n) (2 ^ (S n))
      (2 ^ (S n)) (remove_measured_wire_operator n n b)
      (proj n (S n) b)).
Qed.

Lemma measurement_contraction_last_factor_le_probe : forall n i b,
    i <= n ->
    measurement_contraction (S n) i b =
      measurement_contraction n i b ⊗ I 2.
Proof.
  intros n i b Hi.
  destruct (Nat.eq_dec i n) as [Heq|Hne].
  - rewrite Heq.
    apply measurement_contraction_penultimate_factor_probe.
  - apply measurement_contraction_last_factor_probe; lia.
Qed.

Lemma measurement_contraction_last_probe : forall n b,
    measurement_contraction n n b = I (2 ^ n) ⊗ bra (if b then 1 else 0).
Proof.
  intros n b.
  unfold measurement_contraction.
  assert (Hremove : remove_measured_wire_operator n n b =
      I (2 ^ n) ⊗ bra (if b then 1 else 0)).
  {
    unfold remove_measured_wire_operator.
    replace (n - n) with 0 by lia.
    simpl.
    rewrite kron_1_r.
    reflexivity.
  }
  assert (Hproj : proj n (S n) b =
      I (2 ^ n) ⊗ bool_to_matrix b).
  {
    unfold proj, pad_u, pad.
    bdestruct (n + 1 <=? S n); [|lia].
    replace (S n - (n + 1)) with 0 by lia.
    simpl.
    rewrite kron_1_r.
    reflexivity.
  }
  rewrite Hremove, Hproj.
  transitivity (@Mmult (2 ^ n * 1) (2 ^ n * 2) (2 ^ n * 2)
    (I (2 ^ n) ⊗ bra (if b then 1 else 0))
    (I (2 ^ n) ⊗ bool_to_matrix b)).
  - apply (@Mmult_change_dims (2 ^ n) (2 ^ n * 1)
      (2 ^ (S n)) (2 ^ n * 2) (2 ^ (S n)) (2 ^ n * 2)
      (I (2 ^ n) ⊗ bra (if b then 1 else 0))
      (I (2 ^ n) ⊗ bool_to_matrix b)).
    + nia.
    + rewrite Nat.pow_succ_r; nia.
    + rewrite Nat.pow_succ_r; nia.
  - transitivity ((I (2 ^ n) × I (2 ^ n)) ⊗
      (bra (if b then 1 else 0) × bool_to_matrix b)).
    + exact (@kron_mixed_product (2 ^ n) (2 ^ n) (2 ^ n) 1 2 2
        (I (2 ^ n)) (bra (if b then 1 else 0))
        (I (2 ^ n)) (bool_to_matrix b)).
    + rewrite Mmult_1_l by auto with wf_db.
      pose proof (bra_projector_same_probe b) as Hb.
      exact (f_equal (fun X : Matrix 1 2 => I (2 ^ n) ⊗ X) Hb).
Qed.

Lemma bra_last_tensor_commute_probe : forall m n
    (A : Matrix m n) (b : bool),
    WF_Matrix A ->
    @Mmult (m * 1) (m * 2) (n * 2)
      (I m ⊗ bra (if b then 1%nat else 0%nat)) (A ⊗ I 2) =
    @Mmult (m * 1) (n * 1) (n * 2)
      (A ⊗ I 1) (I n ⊗ bra (if b then 1%nat else 0%nat)).
Proof.
  intros m n A b HA.
  transitivity (A ⊗ bra (if b then 1 else 0)).
  - transitivity ((I m × A) ⊗
      (bra (if b then 1%nat else 0%nat) × I 2)).
    + exact (@kron_mixed_product m m n 1 2 2
        (I m) (bra (if b then 1%nat else 0%nat)) A (I 2)).
    + rewrite Mmult_1_l by exact HA.
      rewrite Mmult_1_r by auto with wf_db.
      reflexivity.
  - symmetry.
    transitivity ((A × I n) ⊗ (I 1 × bra (if b then 1%nat else 0%nat))).
    + exact (@kron_mixed_product m n n 1 1 2
        A (I 1) (I n) (bra (if b then 1%nat else 0%nat))).
    + rewrite Mmult_1_r by exact HA.
      rewrite Mmult_1_l by auto with wf_db.
      reflexivity.
Qed.

Lemma bra_last_tensor_commute_power_probe : forall n
    (A : Matrix (2 ^ n) (2 ^ (S n))) (b : bool),
    WF_Matrix A ->
    @Mmult (2 ^ n) (2 ^ (S n)) (2 ^ (S (S n)))
      (I (2 ^ n) ⊗ bra (if b then 1 else 0)) (A ⊗ I 2) =
    @Mmult (2 ^ n) (2 ^ (S n)) (2 ^ (S (S n)))
      A (I (2 ^ (S n)) ⊗ bra (if b then 1 else 0)).
Proof.
  intros n A b HA.
  pose proof (bra_last_tensor_commute_probe
    (2 ^ n) (2 ^ (S n)) A b HA) as H.
  rewrite (@kron_1_r (2 ^ n) (2 ^ (S n)) A) in H.
  transitivity (@Mmult (2 ^ n * 1) (2 ^ n * 2) (2 ^ (S n) * 2)
    (I (2 ^ n) ⊗ bra (if b then 1 else 0)) (A ⊗ I 2)).
  - symmetry.
    apply (@Mmult_change_dims (2 ^ n * 1) (2 ^ n)
      (2 ^ n * 2) (2 ^ (S n)) (2 ^ (S n) * 2) (2 ^ (S (S n)))
      (I (2 ^ n) ⊗ bra (if b then 1 else 0)) (A ⊗ I 2)).
    + nia.
    + rewrite Nat.pow_succ_r; nia.
    + rewrite Nat.pow_succ_r by lia.
      apply Nat.mul_comm.
  - transitivity (@Mmult (2 ^ n * 1) (2 ^ (S n) * 1) (2 ^ (S n) * 2)
      A (I (2 ^ (S n)) ⊗ bra (if b then 1 else 0))).
    + exact H.
    + apply (@Mmult_change_dims (2 ^ n * 1) (2 ^ n)
        (2 ^ (S n) * 1) (2 ^ (S n)) (2 ^ (S n) * 2)
        (2 ^ (S (S n))) A
        (I (2 ^ (S n)) ⊗ bra (if b then 1 else 0))).
      * nia.
      * nia.
      * rewrite Nat.pow_succ_r by lia.
        apply Nat.mul_comm.
Qed.

Lemma measurement_contraction_pair_commute_probe : forall n i j b1 b2,
    i < j -> j <= n ->
    @Mmult (2 ^ (n - 1)) (2 ^ n) (2 ^ (S n))
      (measurement_contraction (n - 1) (j - 1) b2)
      (measurement_contraction n i b1) =
    @Mmult (2 ^ (n - 1)) (2 ^ n) (2 ^ (S n))
      (measurement_contraction (n - 1) i b1)
      (measurement_contraction n j b2).
Proof.
  induction n as [|n IH]; intros i j b1 b2 Hij Hjn.
  - lia.
  - destruct (Nat.eq_dec j (S n)) as [Hlast|Hnotlast].
    + subst j.
      replace (S n - 1) with n by lia.
      rewrite (measurement_contraction_last_probe n b2).
      destruct (Nat.eq_dec i n) as [Hadjacent|Hseparate].
      * rewrite Hadjacent.
        rewrite (measurement_contraction_penultimate_factor_probe n b1).
        rewrite (measurement_contraction_last_probe (S n) b2).
        apply bra_last_tensor_commute_power_probe.
        apply WF_mult.
        -- apply remove_measured_wire_operator_wf; lia.
        -- apply WF_proj.
      *
        assert (Hlt : i < n) by lia.
        rewrite (measurement_contraction_last_factor_probe n i b1 Hlt).
        rewrite (measurement_contraction_last_probe (S n) b2).
        apply bra_last_tensor_commute_power_probe.
        apply WF_mult.
        -- apply remove_measured_wire_operator_wf; lia.
        -- apply WF_proj.
    + assert (Hjlt : j < S n) by lia.
      destruct n as [|n'].
      * lia.
      * assert (Hjle : j <= S n') by lia.
        replace (S (S n') - 1) with (S n') by lia.
        rewrite (measurement_contraction_last_factor_le_probe n' (j - 1) b2 ltac:(lia)).
        rewrite (measurement_contraction_last_factor_le_probe (S n') i b1 ltac:(lia)).
        rewrite (measurement_contraction_last_factor_le_probe n' i b1 ltac:(lia)) at 2.
        rewrite (measurement_contraction_last_factor_le_probe (S n') j b2 ltac:(lia)).
        rewrite (kron_identity_compose_power_probe n'
          (measurement_contraction n' (j - 1) b2)
          (measurement_contraction (S n') i b1)).
        rewrite (kron_identity_compose_power_probe n'
          (measurement_contraction n' i b1)
          (measurement_contraction (S n') j b2)).
        f_equal.
        pose proof IH as IH'.
        repeat (replace (S n' - 1) with n' in IH' by lia).
        apply IH'; lia.
Qed.

Definition contraction_apply {m n} (A : Matrix (2 ^ m) (2 ^ n))
    (v : state_vector n) : state_vector m := @Mmult (2 ^ m) (2 ^ n) 1 A v.

Lemma measure_qubit_probability_value : forall
    (qm : finite_map qubit_reference (participant * fin))
    (Hqm : quantum_map_wf qm)
    (sv : state_vector (length (elems qubit_reference (participant * fin) qm)))
    (Hsv : state_vector_wf sv) q owner index result
    (Hlookup : qm q = Some (owner,index)) (Hlen : 0 < length
      (elems qubit_reference (participant * fin) qm))
    (Hnonzero : norm (proj index
      (length (elems qubit_reference (participant * fin) qm)) result × sv) <> 0%R),
    proj1_sig (fst (measure_qubit_from_nonzero qm Hqm sv Hsv q owner index
      result Hlookup Hlen Hnonzero)) =
    (norm (proj index (length (elems qubit_reference (participant * fin) qm))
      result × sv) ^ 2)%R.
Proof. reflexivity. Qed.

Lemma positive_scale_nonzero_measurement : forall m (v : Matrix m 1) c,
    v <> Zero -> (c > 0)%R -> RtoC c .* v <> Zero.
Proof.
  intros m v c Hnonzero Hpositive Hscaled.
  apply Hnonzero.
  transitivity (RtoC (/ c) .* (RtoC c .* v)).
  - rewrite Mscale_assoc, <- RtoC_mult.
    replace (/ c * c)%R with 1%R by (field; lra).
    cbn [RtoC].
    rewrite Mscale_1_l.
    reflexivity.
  - rewrite Hscaled, Mscale_0_r.
    reflexivity.
Qed.

Lemma normalize_removed_wire_positive_scale_measurement : forall n
    (v : state_vector n) (Hv : @WF_Matrix (2 ^ n) 1 v) c,
    v <> Zero -> (c > 0)%R ->
    normalize_removed_wire (RtoC c .* v) = normalize_removed_wire v.
Proof.
  intros [|n] v Hv c Hnonzero Hpositive.
  - reflexivity.
  - unfold normalize_removed_wire.
    rewrite norm_scale, Cmod_R, Rabs_pos_eq by lra.
    rewrite Mscale_assoc.
    f_equal.
    rewrite <- RtoC_mult.
    f_equal.
    pose proof (positive_norm_of_nonzero (S n) v Hv Hnonzero) as Hnorm.
    field; lra.
Qed.

Lemma normalized_measurement_pair_commute : forall n i j b1 b2
    (v : state_vector (S n)),
    i < j -> j <= n -> @WF_Matrix (2 ^ (S n)) 1 v ->
    contraction_apply (measurement_contraction n i b1) v <> Zero ->
    contraction_apply (measurement_contraction (n - 1) (j - 1) b2)
      (normalize_removed_wire (contraction_apply (measurement_contraction n i b1) v)) <> Zero ->
    contraction_apply (measurement_contraction n j b2) v <> Zero /\
    contraction_apply (measurement_contraction (n - 1) i b1)
      (normalize_removed_wire (contraction_apply (measurement_contraction n j b2) v)) <> Zero /\
    normalize_removed_wire
      (contraction_apply (measurement_contraction (n - 1) (j - 1) b2)
        (normalize_removed_wire (contraction_apply (measurement_contraction n i b1) v))) =
    normalize_removed_wire
      (contraction_apply (measurement_contraction (n - 1) i b1)
        (normalize_removed_wire (contraction_apply (measurement_contraction n j b2) v))).
Proof.
  intros n i j b1 b2 v Hij Hjn Hv Hfirst Hsecond.
  destruct n as [|n']; [lia|].
  rename n' into n.
  simpl in *.
  replace (n - 0) with n in * by lia.
  replace (n - 0) with n in * by lia.
  assert (Hnpos : 0 < S n) by lia.
  assert (HC1 : WF_Matrix (measurement_contraction (S n) i b1)).
  { unfold measurement_contraction; apply WF_mult.
    - apply remove_measured_wire_operator_wf; lia.
    - apply WF_proj. }
  assert (HC2 : WF_Matrix (measurement_contraction n (j - 1) b2)).
  { unfold measurement_contraction; apply WF_mult.
    - apply remove_measured_wire_operator_wf; lia.
    - apply WF_proj. }
  assert (HC3 : WF_Matrix (measurement_contraction (S n) j b2)).
  { unfold measurement_contraction; apply WF_mult.
    - apply remove_measured_wire_operator_wf; lia.
    - apply WF_proj. }
  assert (HC4 : WF_Matrix (measurement_contraction n i b1)).
  { unfold measurement_contraction; apply WF_mult.
    - apply remove_measured_wire_operator_wf; lia.
    - apply WF_proj. }
  set (v1 := contraction_apply (measurement_contraction (S n) i b1) v).
  assert (Hv1 : @WF_Matrix (2 ^ (S n)) 1 v1).
  { unfold v1, contraction_apply; apply WF_mult; assumption. }
  assert (Hnorm1 : (0 < @norm (2 ^ (S n)) v1)%R).
  { unfold v1; apply positive_norm_of_nonzero; assumption. }
  set (c1 := (1 / @norm (2 ^ (S n)) v1)%R).
  change (contraction_apply (measurement_contraction n (j - 1) b2)
    ((1 / @norm (2 ^ (S n)) v1)%R .* v1) <> Zero) in Hsecond.
  assert (Hc1 : (c1 > 0)%R).
  { unfold c1; apply Rdiv_lt_0_compat; lra. }
  assert (Hscale1 : normalize_removed_wire v1 = RtoC c1 .* v1).
  { pose proof (@normalize_removed_wire_positive (S n) v1 Hnpos) as H.
    unfold c1; exact H. }
  set (z1 := contraction_apply (measurement_contraction n (j - 1) b2) v1).
  assert (Hz1wf : @WF_Matrix (2 ^ n) 1 z1).
  { unfold z1, contraction_apply; apply WF_mult; [exact HC2|exact Hv1]. }
  assert (Hz1 : z1 <> Zero).
  {
    unfold z1.
    intro Hzero.
    apply Hsecond.
    unfold contraction_apply.
    unfold contraction_apply in Hzero.
    rewrite Mscale_mult_dist_r, Hzero, Mscale_0_r.
    reflexivity.
  }
  pose proof (measurement_contraction_pair_commute_probe (S n) i j b1 b2
    Hij Hjn) as Hpair.
  assert (Hpairv :
      contraction_apply (measurement_contraction n (j - 1) b2) v1 =
      contraction_apply (measurement_contraction n i b1)
        (contraction_apply (measurement_contraction (S n) j b2) v)).
  {
    unfold contraction_apply, v1.
    pose proof (f_equal
      (fun A : Matrix (2 ^ (S n - 1)) (2 ^ (S (S n))) =>
        @Mmult (2 ^ (S n - 1)) (2 ^ (S (S n))) 1 A v) Hpair) as H.
    cbn beta in H.
    replace (S n - 1) with n in H by lia.
    rewrite !Mmult_assoc in H.
    exact H.
  }
  assert (Hright : contraction_apply (measurement_contraction (S n) j b2) v <> Zero).
  {
    intro Hzero.
    apply Hz1.
    unfold z1, contraction_apply.
    unfold contraction_apply in Hpairv, Hzero.
    rewrite Hpairv, Hzero, Mmult_0_r.
    reflexivity.
  }
  assert (Hrightwf : @WF_Matrix (2 ^ (S n)) 1
      (contraction_apply (measurement_contraction (S n) j b2) v)).
  { unfold contraction_apply; apply WF_mult; assumption. }
  assert (Hnorm2 :
      (0 < @norm (2 ^ (S n))
        (contraction_apply (measurement_contraction (S n) j b2) v))%R).
  { apply positive_norm_of_nonzero; assumption. }
  set (c2 := (1 / @norm (2 ^ (S n))
    (contraction_apply (measurement_contraction (S n) j b2) v))%R).
  assert (Hc2 : (c2 > 0)%R).
  { unfold c2; apply Rdiv_lt_0_compat; lra. }
  assert (Hscale2 :
      normalize_removed_wire (contraction_apply (measurement_contraction (S n) j b2) v) =
        RtoC c2 .* (contraction_apply (measurement_contraction (S n) j b2) v)).
  { pose proof (@normalize_removed_wire_positive (S n)
      (contraction_apply (measurement_contraction (S n) j b2) v)
      Hnpos) as H.
    unfold c2; exact H. }
  set (z2 := contraction_apply (measurement_contraction n i b1)
    (contraction_apply (measurement_contraction (S n) j b2) v)).
  assert (Hz2wf : @WF_Matrix (2 ^ n) 1 z2).
  { unfold z2, contraction_apply; apply WF_mult; [exact HC4|exact Hrightwf]. }
  assert (Hz2 : z2 <> Zero).
  { unfold z2; rewrite <- Hpairv; exact Hz1. }
  assert (Hout2 : contraction_apply (measurement_contraction n i b1)
      (normalize_removed_wire (contraction_apply (measurement_contraction (S n) j b2) v)) <> Zero).
  {
    assert (Hout2eq : contraction_apply (measurement_contraction n i b1)
        (normalize_removed_wire (contraction_apply (measurement_contraction (S n) j b2) v)) =
      RtoC c2 .* z2).
    { rewrite Hscale2.
      unfold contraction_apply.
      rewrite Mscale_mult_dist_r.
      unfold z2, contraction_apply.
      reflexivity. }
    rewrite Hout2eq.
    apply positive_scale_nonzero_measurement; assumption.
  }
  assert (Hout1eq :
      contraction_apply (measurement_contraction n (j - 1) b2)
        (normalize_removed_wire v1) = RtoC c1 .* z1).
  { rewrite Hscale1.
    unfold contraction_apply.
    rewrite Mscale_mult_dist_r.
    unfold z1, contraction_apply.
    reflexivity. }
  assert (Hout2eq :
      contraction_apply (measurement_contraction n i b1)
        (normalize_removed_wire (contraction_apply (measurement_contraction (S n) j b2) v)) =
      RtoC c2 .* z2).
  { rewrite Hscale2.
    unfold contraction_apply.
    rewrite Mscale_mult_dist_r.
    unfold z2, contraction_apply.
    reflexivity. }
  split; [exact Hright|].
  split; [exact Hout2|].
  pose proof (f_equal
    (fun x => normalize_removed_wire
      (contraction_apply (measurement_contraction n (j - 1) b2) x))
    Hscale1) as Hnormalized_left.
  pose proof (f_equal
    (fun x => normalize_removed_wire
      (contraction_apply (measurement_contraction n i b1) x))
    Hscale2) as Hnormalized_right.
  assert (Hz12 : z1 = z2).
  { unfold z1, z2; exact Hpairv. }
  transitivity (normalize_removed_wire
    (contraction_apply (measurement_contraction n (j - 1) b2)
      (normalize_removed_wire v1))).
  - symmetry; exact Hnormalized_left.
  - transitivity (normalize_removed_wire
      (contraction_apply (measurement_contraction n i b1)
        (normalize_removed_wire
          (contraction_apply (measurement_contraction (S n) j b2) v)))).
    + rewrite Hout1eq, Hout2eq, <- Hz12.
      transitivity (normalize_removed_wire z1).
      * apply normalize_removed_wire_positive_scale_measurement; assumption.
      * symmetry; apply normalize_removed_wire_positive_scale_measurement; assumption.
    + exact Hnormalized_right.
Qed.

Lemma shift_wire_index_pair : forall i j wire,
    i < j ->
    shift_wire_index (j - 1) (shift_wire_index i wire) =
    shift_wire_index i (shift_wire_index j wire).
Proof.
  intros i j wire Hij.
  unfold shift_wire_index.
  destruct (i <? wire) eqn:Hi.
  - assert (Hilt : i < wire) by (apply Nat.ltb_lt; exact Hi).
    destruct (j <? wire) eqn:Hj.
    + assert (Hjlt : j < wire) by (apply Nat.ltb_lt; exact Hj).
      destruct ((j - 1) <? Nat.pred wire) eqn:Hleft.
      * assert (Hleftlt : j - 1 < Nat.pred wire)
          by (apply Nat.ltb_lt; exact Hleft).
        destruct (i <? Nat.pred wire) eqn:Hright.
        -- try rewrite Hj; try rewrite Hleft; try rewrite Hright;
             simpl; f_equal; lia.
        -- assert (Hrightge : Nat.pred wire <= i)
             by (apply Nat.ltb_ge; exact Hright); lia.
      * assert (Hleftge : Nat.pred wire <= j - 1)
          by (apply Nat.ltb_ge; exact Hleft); lia.
    + assert (Hjge : wire <= j) by (apply Nat.ltb_ge; exact Hj).
      destruct ((j - 1) <? Nat.pred wire) eqn:Hleft.
      * assert (Hleftlt : j - 1 < Nat.pred wire)
          by (apply Nat.ltb_lt; exact Hleft); lia.
      * try rewrite Hi; try rewrite Hj; try rewrite Hleft;
          simpl; reflexivity.
  - assert (Hige : wire <= i) by (apply Nat.ltb_ge; exact Hi).
    destruct (j <? wire) eqn:Hj.
    + assert (Hjlt : j < wire) by (apply Nat.ltb_lt; exact Hj); lia.
    + assert (Hjge : wire <= j) by (apply Nat.ltb_ge; exact Hj).
      destruct ((j - 1) <? wire) eqn:Hleft.
      * assert (Hleftlt : j - 1 < wire)
          by (apply Nat.ltb_lt; exact Hleft); lia.
      * try rewrite Hi; try rewrite Hj; try rewrite Hleft;
          simpl; reflexivity.
Qed.

Lemma remove_two_qubits_commute : forall
    (qm : finite_map qubit_reference (participant * fin))
    (q1 q2 : qubit_reference) i j,
    q1 <> q2 -> i < j ->
    equivalent
      (remove_and_reindex_qubit_map
        (remove_and_reindex_qubit_map qm q1 i) q2 (j - 1))
      (remove_and_reindex_qubit_map
        (remove_and_reindex_qubit_map qm q2 j) q1 i).
Proof.
  intros qm q1 q2 i j Hneq Hij.
  assert (Hlookup : forall key,
      (remove_and_reindex_qubit_map
        (remove_and_reindex_qubit_map qm q1 i) q2 (j - 1)) key =
      (remove_and_reindex_qubit_map
        (remove_and_reindex_qubit_map qm q2 j) q1 i) key).
  {
    intros key.
    unfold remove_and_reindex_qubit_map, reindex_quantum_map; simpl.
    destruct (qr_dec key q1) as [Heq1|Hkey1];
      destruct (qr_dec key q2) as [Heq2|Hkey2].
    - exfalso; apply Hneq; congruence.
    - subst key.
      destruct (qr_dec q2 q1) as [Heq|Hneq']; [congruence|].
      destruct (qr_dec q1 q1); [reflexivity|congruence].
    - subst key.
      destruct (qr_dec q1 q2) as [Heq|Hneq']; [congruence|].
      destruct (qr_dec q2 q2); [reflexivity|congruence].
    - repeat (rewrite delete_neq by congruence).
      destruct (qr_dec q1 key) as [Heq1|Hneq1']; [congruence|].
      destruct (qr_dec q2 key) as [Heq2|Hneq2']; [congruence|].
      destruct (qm key) as [[owner wire]|] eqn:Hqmkey; simpl; [|reflexivity].
      unfold shift_qubit_index; simpl.
      f_equal.
      f_equal.
      apply shift_wire_index_pair; exact Hij.
  }
  unfold equivalent, included; split; intros key value Hvalue.
  - rewrite Hlookup in Hvalue; exact Hvalue.
  - rewrite <- Hlookup in Hvalue; exact Hvalue.
Qed.

Lemma measurement_contraction_norm : forall n i b
    (v : state_vector (S n)),
    i <= n -> @WF_Matrix (2 ^ (S n)) 1 v ->
    @norm (2 ^ n) (contraction_apply (measurement_contraction n i b) v) =
    @norm (2 ^ (S n)) (proj i (S n) b × v).
Proof.
  intros n i b v Hi Hv.
  unfold contraction_apply, measurement_contraction.
  set (w := @Mmult (2 ^ n) (2 ^ (S n)) 1
    (remove_measured_wire_operator n i b) (proj i (S n) b × v)).
  assert (Hw : @WF_Matrix (2 ^ n) 1 w).
  {
    unfold w; apply WF_mult.
    - apply remove_measured_wire_operator_wf; exact Hi.
    - apply WF_mult; [apply WF_proj|exact Hv].
  }
  assert (Hpreserve : @norm (2 ^ (S n))
      (@Mmult (2 ^ (S n)) (2 ^ n) 1
        (insert_measured_wire_operator n i b) w) = @norm (2 ^ n) w).
  { exact (@insert_measured_wire_operator_preserves_norm n i b w Hi Hw). }
  rewrite Mmult_assoc at 1.
  fold w.
  rewrite <- Hpreserve.
  unfold w.
  rewrite <- Mmult_assoc.
  rewrite insert_remove_measured_wire_operator by exact Hi.
  rewrite <- Mmult_assoc, proj_twice_eq.
  reflexivity.
Qed.

Lemma measurement_contraction_pair_apply : forall n i j b1 b2
    (v : state_vector (S n)),
    i < j -> j <= n ->
    contraction_apply (measurement_contraction (n - 1) (j - 1) b2)
      (contraction_apply (measurement_contraction n i b1) v) =
    contraction_apply (measurement_contraction (n - 1) i b1)
      (contraction_apply (measurement_contraction n j b2) v).
Proof.
  intros n i j b1 b2 v Hij Hjn.
  destruct n as [|n']; [lia|].
  rename n' into n.
  simpl in *.
  pose proof (measurement_contraction_pair_commute_probe (S n) i j b1 b2
    Hij Hjn) as Hpair.
  pose proof (f_equal
    (fun A : Matrix (2 ^ (S n - 1)) (2 ^ (S (S n))) =>
      @Mmult (2 ^ (S n - 1)) (2 ^ (S (S n))) 1 A v) Hpair) as H.
  cbn beta in H.
  replace (S n - 1) with n in H by lia.
  rewrite !Mmult_assoc in H.
  unfold contraction_apply.
  replace (n - 0) with n by lia.
  exact H.
Qed.

Lemma measurement_pair_probability_product_commute : forall n i j b1 b2
    (v : state_vector (S n)),
    i < j -> j <= n -> @WF_Matrix (2 ^ (S n)) 1 v ->
    contraction_apply (measurement_contraction n i b1) v <> Zero ->
    contraction_apply (measurement_contraction (n - 1) (j - 1) b2)
      (normalize_removed_wire (contraction_apply (measurement_contraction n i b1) v)) <> Zero ->
    ((@norm (2 ^ (S n)) (proj i (S n) b1 × v) ^ 2) *
      (@norm (2 ^ n) (proj (j - 1) n b2 ×
        normalize_removed_wire (contraction_apply (measurement_contraction n i b1) v)) ^ 2))%R =
    ((@norm (2 ^ (S n)) (proj j (S n) b2 × v) ^ 2) *
      (@norm (2 ^ n) (proj i n b1 ×
        normalize_removed_wire (contraction_apply (measurement_contraction n j b2) v)) ^ 2))%R.
Proof.
  intros n i j b1 b2 v Hij Hjn Hv Hfirst Hsecond.
  destruct n as [|n']; [lia|].
  rename n' into n.
  simpl in Hfirst, Hsecond.
  replace (n - 0) with n in * by lia.
  assert (Hnpos : 0 < S n) by lia.
  set (v1 := contraction_apply (measurement_contraction (S n) i b1) v).
  assert (Hv1 : @WF_Matrix (2 ^ (S n)) 1 v1).
  { unfold v1, contraction_apply; apply WF_mult; [|exact Hv].
    unfold measurement_contraction; apply WF_mult.
    - apply remove_measured_wire_operator_wf; lia.
    - apply WF_proj. }
  assert (Hfirst' : v1 <> Zero) by exact Hfirst.
  pose proof (positive_norm_of_nonzero (S n) v1 Hv1 Hfirst') as Hnorm1pos.
  set (c1 := (1 / @norm (2 ^ (S n)) v1)%R).
  assert (Hscale1 : normalize_removed_wire v1 = RtoC c1 .* v1).
  { pose proof (@normalize_removed_wire_positive (S n) v1 Hnpos) as H.
    unfold c1; exact H. }
  set (Hmeas2 := contraction_apply (measurement_contraction n (j - 1) b2)).
  assert (Hsecond_normalized : Hmeas2 (normalize_removed_wire v1) <> Zero).
  {
    assert (Hsecond_scaled : Hmeas2 (RtoC c1 .* v1) <> Zero).
    { unfold Hmeas2, v1, c1; exact Hsecond. }
    rewrite Hscale1; exact Hsecond_scaled.
  }
  assert (Hsecond_for_pair :
      contraction_apply (measurement_contraction (S n - 1) (j - 1) b2)
        (normalize_removed_wire v1) <> Zero).
  { replace (S n - 1) with n by lia; exact Hsecond_normalized. }
  pose proof (normalized_measurement_pair_commute (S n) i j b1 b2 v
    Hij Hjn Hv Hfirst Hsecond_for_pair)
    as [Hright [Hout2 Hfinal]].
  set (v2 := contraction_apply (measurement_contraction (S n) j b2) v).
  assert (Hv2 : @WF_Matrix (2 ^ (S n)) 1 v2).
  { unfold v2, contraction_apply; apply WF_mult; [|exact Hv].
    unfold measurement_contraction; apply WF_mult.
    - apply remove_measured_wire_operator_wf; lia.
    - apply WF_proj. }
  pose proof (positive_norm_of_nonzero (S n) v2 Hv2 Hright) as Hnorm2pos.
  set (z1 := Hmeas2 v1).
  set (Hmeas1 := contraction_apply (measurement_contraction n i b1)).
  set (z2 := Hmeas1 v2).
  assert (Hz12 : z1 = z2).
  {
    unfold z1, z2, Hmeas2, Hmeas1, v1, v2.
    pose proof (measurement_contraction_pair_apply (S n) i j b1 b2 v
      Hij Hjn) as Hpair_apply.
    replace (S n - 1) with n in Hpair_apply by lia.
    exact Hpair_apply.
  }
  assert (Hnormc1 : @norm (2 ^ (S n)) v1 =
      @norm (2 ^ (S (S n))) (proj i (S (S n)) b1 × v)).
  { unfold v1; apply measurement_contraction_norm; [lia|exact Hv]. }
  assert (Hnormc2 : @norm (2 ^ n)
      (contraction_apply (measurement_contraction n (j - 1) b2)
        (normalize_removed_wire v1)) =
      @norm (2 ^ (S n))
        (proj (j - 1) (S n) b2 × normalize_removed_wire v1)).
  {
    apply measurement_contraction_norm; [lia|].
    exact (proj1 (normalize_removed_wire_wf (S n) v1 Hv1 Hfirst')).
  }
  assert (Hnormc3 : @norm (2 ^ (S n)) v2 =
      @norm (2 ^ (S (S n))) (proj j (S (S n)) b2 × v)).
  { unfold v2; apply measurement_contraction_norm; [lia|exact Hv]. }
  assert (Hnormc4 : @norm (2 ^ n)
      (contraction_apply (measurement_contraction n i b1)
        (normalize_removed_wire v2)) =
      @norm (2 ^ (S n))
        (proj i (S n) b1 × normalize_removed_wire v2)).
  {
    apply measurement_contraction_norm; [lia|].
    exact (proj1 (normalize_removed_wire_wf (S n) v2 Hv2 Hright)).
  }
  assert (Hnorm_second_forward :
      @norm (2 ^ n)
        (contraction_apply (measurement_contraction n (j - 1) b2)
          (normalize_removed_wire v1)) =
      ((1 / @norm (2 ^ (S n)) v1)%R * @norm (2 ^ n) z1)%R).
  {
    rewrite Hscale1.
    unfold contraction_apply, z1, Hmeas2.
    rewrite Mscale_mult_dist_r, norm_scale, Cmod_R, Rabs_pos_eq.
    - unfold c1; reflexivity.
    - unfold c1; apply Rlt_le; apply Rdiv_lt_0_compat; lra.
  }
  assert (Hnorm_second_reverse :
      @norm (2 ^ n)
        (contraction_apply (measurement_contraction n i b1)
          (normalize_removed_wire v2)) =
      ((1 / @norm (2 ^ (S n)) v2)%R * @norm (2 ^ n) z2)%R).
  {
    pose proof (@normalize_removed_wire_positive (S n) v2 Hnpos) as Hscale2.
    rewrite Hscale2.
    unfold contraction_apply, z2, Hmeas1.
    rewrite Mscale_mult_dist_r, norm_scale, Cmod_R, Rabs_pos_eq.
    - reflexivity.
    - apply Rlt_le; apply Rdiv_lt_0_compat; lra.
  }
  pose proof (@normalize_removed_wire_positive (S n) v1 Hnpos) as Hscale_def1.
  pose proof (@normalize_removed_wire_positive (S n) v2 Hnpos) as Hscale_def2.
  pose proof Hnormc2 as Hnormc2_scaled.
  rewrite Hscale_def1 in Hnormc2_scaled.
  pose proof Hnormc4 as Hnormc4_scaled.
  rewrite Hscale_def2 in Hnormc4_scaled.
  pose proof Hnorm_second_forward as Hnorm_second_forward_scaled.
  rewrite Hscale_def1 in Hnorm_second_forward_scaled.
  pose proof Hnorm_second_reverse as Hnorm_second_reverse_scaled.
  rewrite Hscale_def2 in Hnorm_second_reverse_scaled.
  assert (Hprob1 :
      @norm (2 ^ (S n)) (proj (j - 1) (S n) b2 × normalize_removed_wire v1) =
      ((1 / @norm (2 ^ (S n)) v1)%R * @norm (2 ^ n) z1)%R).
  {
    transitivity (@norm (2 ^ n)
      (contraction_apply (measurement_contraction n (j - 1) b2)
        (normalize_removed_wire v1))).
    - symmetry; exact Hnormc2_scaled.
    - exact Hnorm_second_forward_scaled.
  }
  assert (Hprob2 :
      @norm (2 ^ (S n)) (proj i (S n) b1 × normalize_removed_wire v2) =
      ((1 / @norm (2 ^ (S n)) v2)%R * @norm (2 ^ n) z2)%R).
  {
    transitivity (@norm (2 ^ n)
      (contraction_apply (measurement_contraction n i b1)
        (normalize_removed_wire v2))).
    - symmetry; exact Hnormc4_scaled.
    - exact Hnorm_second_reverse_scaled.
  }
  assert (Hprob1_scaled :
      @norm (2 ^ (S n))
        (proj (j - 1) (S n) b2 × ((1 / @norm (2 ^ (S n)) v1)%R .* v1)) =
      ((1 / @norm (2 ^ (S n)) v1)%R * @norm (2 ^ n) z1)%R).
  {
    transitivity (@norm (2 ^ n)
      (contraction_apply (measurement_contraction n (j - 1) b2)
        ((1 / @norm (2 ^ (S n)) v1)%R .* v1))).
    - symmetry; exact Hnormc2_scaled.
    - exact Hnorm_second_forward_scaled.
  }
  assert (Hprob2_scaled :
      @norm (2 ^ (S n))
        (proj i (S n) b1 × ((1 / @norm (2 ^ (S n)) v2)%R .* v2)) =
      ((1 / @norm (2 ^ (S n)) v2)%R * @norm (2 ^ n) z2)%R).
  {
    transitivity (@norm (2 ^ n)
      (contraction_apply (measurement_contraction n i b1)
        ((1 / @norm (2 ^ (S n)) v2)%R .* v2))).
    - symmetry; exact Hnormc4_scaled.
    - exact Hnorm_second_reverse_scaled.
  }
  replace (@norm (2 ^ (S (S n))) (proj i (S (S n)) b1 × v))
    with (@norm (2 ^ (S n)) v1) by exact Hnormc1.
  replace (@norm (2 ^ (S (S n))) (proj j (S (S n)) b2 × v))
    with (@norm (2 ^ (S n)) v2) by exact Hnormc3.

  rewrite Hprob1, Hprob2, Hz12.
  field; lra.
Qed.

Lemma normalized_measurement_pair_commute_reverse : forall n i j b1 b2
    (v : state_vector (S n)),
    i < j -> j <= n -> @WF_Matrix (2 ^ (S n)) 1 v ->
    contraction_apply (measurement_contraction n j b2) v <> Zero ->
    contraction_apply (measurement_contraction (n - 1) i b1)
      (normalize_removed_wire
        (contraction_apply (measurement_contraction n j b2) v)) <> Zero ->
    contraction_apply (measurement_contraction n i b1) v <> Zero /\
    contraction_apply (measurement_contraction (n - 1) (j - 1) b2)
      (normalize_removed_wire
        (contraction_apply (measurement_contraction n i b1) v)) <> Zero /\
    normalize_removed_wire
      (contraction_apply (measurement_contraction (n - 1) (j - 1) b2)
        (normalize_removed_wire
          (contraction_apply (measurement_contraction n i b1) v))) =
    normalize_removed_wire
      (contraction_apply (measurement_contraction (n - 1) i b1)
        (normalize_removed_wire
          (contraction_apply (measurement_contraction n j b2) v))).
Proof.
  intros n i j b1 b2 v Hij Hjn Hv Hhigh Hlow_after_high.
  destruct n as [|n']; [lia|].
  rename n' into n.
  simpl in *.
  replace (n - 0) with n in * by lia.
  assert (Hnpos : 0 < S n) by lia.
  assert (Hhigh_wf : @WF_Matrix (2 ^ (S n)) 1
      (contraction_apply (measurement_contraction (S n) j b2) v)).
  {
    unfold contraction_apply; apply WF_mult.
    - unfold measurement_contraction; apply WF_mult.
      + apply remove_measured_wire_operator_wf; lia.
      + apply WF_proj.
    - exact Hv.
  }
  pose proof (positive_norm_of_nonzero (S n)
    (contraction_apply (measurement_contraction (S n) j b2) v)
    Hhigh_wf Hhigh) as Hnorm_high.
  set (chigh := (1 / @norm (2 ^ (S n))
    (contraction_apply (measurement_contraction (S n) j b2) v))%R).
  assert (Hchigh : (chigh > 0)%R).
  { unfold chigh; apply Rdiv_lt_0_compat; lra. }
  assert (Hnormalize_high : normalize_removed_wire
      (contraction_apply (measurement_contraction (S n) j b2) v) =
      RtoC chigh .* contraction_apply (measurement_contraction (S n) j b2) v).
  {
    pose proof (@normalize_removed_wire_positive (S n)
      (contraction_apply (measurement_contraction (S n) j b2) v) Hnpos) as H.
    unfold chigh; exact H.
  }
  assert (Hjoint : contraction_apply (measurement_contraction n i b1)
      (contraction_apply (measurement_contraction (S n) j b2) v) <> Zero).
  {
    assert (Hscaled : contraction_apply (measurement_contraction n i b1)
        (normalize_removed_wire
          (contraction_apply (measurement_contraction (S n) j b2) v)) =
      RtoC chigh .* contraction_apply (measurement_contraction n i b1)
        (contraction_apply (measurement_contraction (S n) j b2) v)).
    {
      rewrite Hnormalize_high.
      unfold contraction_apply.
      exact (@Mscale_mult_dist_r (2 ^ n) (2 ^ (S n)) 1
        (RtoC chigh) (measurement_contraction n i b1)
        (contraction_apply (measurement_contraction (S n) j b2) v)).
    }
    intro Hzero; apply Hlow_after_high.
    change (contraction_apply (measurement_contraction n i b1)
      (normalize_removed_wire
        (contraction_apply (measurement_contraction (S n) j b2) v)) = Zero).
    rewrite Hscaled, Hzero, Mscale_0_r.
    reflexivity.
  }
  pose proof (measurement_contraction_pair_apply (S n) i j b1 b2 v
    Hij Hjn) as Hpair.
  replace (S n - 1) with n in Hpair by lia.
  assert (Hjoint_reverse : contraction_apply
      (measurement_contraction n (j - 1) b2)
      (contraction_apply (measurement_contraction (S n) i b1) v) <> Zero).
  {
    rewrite Hpair; exact Hjoint.
  }
  assert (Hlow : contraction_apply (measurement_contraction (S n) i b1) v <> Zero).
  {
    intro Hzero; apply Hjoint_reverse.
    rewrite Hzero.
    unfold contraction_apply.
    exact (@Mmult_0_r (2 ^ n) (2 ^ (S n)) 1
      (measurement_contraction n (j - 1) b2)).
  }
  assert (Hlow_wf : @WF_Matrix (2 ^ (S n)) 1
      (contraction_apply (measurement_contraction (S n) i b1) v)).
  {
    unfold contraction_apply; apply WF_mult.
    - unfold measurement_contraction; apply WF_mult.
      + apply remove_measured_wire_operator_wf; lia.
      + apply WF_proj.
    - exact Hv.
  }
  pose proof (positive_norm_of_nonzero (S n)
    (contraction_apply (measurement_contraction (S n) i b1) v)
    Hlow_wf Hlow) as Hnorm_low.
  set (clow := (1 / @norm (2 ^ (S n))
    (contraction_apply (measurement_contraction (S n) i b1) v))%R).
  assert (Hclow : (clow > 0)%R).
  { unfold clow; apply Rdiv_lt_0_compat; lra. }
  assert (Hnormalize_low : normalize_removed_wire
      (contraction_apply (measurement_contraction (S n) i b1) v) =
      RtoC clow .* contraction_apply (measurement_contraction (S n) i b1) v).
  {
    pose proof (@normalize_removed_wire_positive (S n)
      (contraction_apply (measurement_contraction (S n) i b1) v) Hnpos) as H.
    unfold clow; exact H.
  }
  assert (Hhigh_after_low : contraction_apply
      (measurement_contraction n (j - 1) b2)
      (normalize_removed_wire
        (contraction_apply (measurement_contraction (S n) i b1) v)) <> Zero).
  {
    rewrite Hnormalize_low.
    unfold contraction_apply.
    rewrite Mscale_mult_dist_r.
    apply positive_scale_nonzero_measurement; [exact Hjoint_reverse|exact Hclow].
  }
  assert (Hhigh_after_low' : contraction_apply
      (measurement_contraction (S n - 1) (j - 1) b2)
      (normalize_removed_wire
        (contraction_apply (measurement_contraction (S n) i b1) v)) <> Zero).
  { replace (S n - 1) with n by lia; exact Hhigh_after_low. }
  destruct (normalized_measurement_pair_commute (S n) i j b1 b2 v
    Hij Hjn Hv Hlow Hhigh_after_low') as [_ [_ Hfinal]].
  split; [exact Hlow|].
  split.
  - change (contraction_apply (measurement_contraction n (j - 1) b2)
      (normalize_removed_wire
        (contraction_apply (measurement_contraction (S n) i b1) v)) <> Zero).
    exact Hhigh_after_low.
  - replace (S n - 1) with n in Hfinal by lia.
    change (normalize_removed_wire
      (contraction_apply (measurement_contraction n (j - 1) b2)
        (normalize_removed_wire
          (contraction_apply (measurement_contraction (S n) i b1) v))) =
      normalize_removed_wire
      (contraction_apply (measurement_contraction n i b1)
        (normalize_removed_wire
          (contraction_apply (measurement_contraction (S n) j b2) v)))).
    exact Hfinal.
Qed.


Lemma measure_output_vector_contraction : forall
    (a a0 : action) (s s' : state) (pi : R)
    (Hglobal : multistep s (a :: a0 :: nil) s' pi)
    (Hswap : should_swap_no_newq a a0 = true)
    (Hnn : no_newq_session (snd s))
    (qm : finite_map qubit_reference (participant * fin))
    (Hqm : quantum_map_wf qm)
    (sv : state_vector (length (elems qubit_reference
      (participant * fin) qm))) (Hsv : state_vector_wf sv)
    q owner index result
    (Hlookup : qm q = Some (owner,index))
    (Hlen : 0 < length (elems qubit_reference (participant * fin) qm))
    (Hnonzero : norm (proj index
      (length (elems qubit_reference (participant * fin) qm)) result × sv)
      <> 0%R)
    (Htotal : length (elems qubit_reference (participant * fin) qm) =
      S (length (elems qubit_reference (participant * fin)
        (remove_and_reindex_qubit_map qm q index)))),
    proj1_sig (projT2 (snd (measure_qubit_from_nonzero qm Hqm sv Hsv
      q owner index result Hlookup Hlen Hnonzero))) =
    normalize_removed_wire
      (contraction_apply
        (measurement_contraction
          (length (elems qubit_reference (participant * fin)
            (remove_and_reindex_qubit_map qm q index))) index result)
        (transport_state_vector Htotal sv)).
Proof.
  intros a a0 s s' pi Hglobal Hswap Hnn qm Hqm sv Hsv q owner index result
    Hlookup Hlen Hnonzero Htotal.
  pose proof (measure_qubit_nonzero_full_vector
    qm Hqm sv Hsv q owner index result Hlookup Hlen Hnonzero Htotal)
    as Hvector.
  unfold measure_qubit_from_nonzero.
  rewrite Hvector.
  unfold contraction_apply, measurement_contraction.
  rewrite remove_measured_wire_operator_full_apply.
  rewrite (transport_state_vector_proj
    (length (elems qubit_reference (participant * fin) qm))
    (S (length (elems qubit_reference (participant * fin)
      (remove_and_reindex_qubit_map qm q index))))
    Htotal index result sv).
  rewrite <- Mmult_assoc.
  reflexivity.
Qed.

(* Merged from FCTwoTransferSupport.v. *)
Require Import Lia Permutation String Coq.Program.Equality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import SST session QUEST QuantumGateTeleportation ExamplesHelpers FunctionalCorrectnessHelpers.
From SQIR Require Import SQIR.
Require Import SQIR.UnitaryOps SQIR.Equivalences.
Open Scope nat_scope.
Lemma replace_or_add_fst_same : forall A B (AEQ : EqDec A)
    (l : list (A*B)) a b,
    In a (map fst l) ->
    map fst (replace_or_add l (a,b)) = map fst l.
Proof.
  intros A B AEQ l; induction l as [|[x y] tl IH]; intros a b Hin; simpl in *.
  - contradiction.
  - destruct (AEQ x a) as [Heq|Hneq].
    + simpl. rewrite Heq. reflexivity.
    + simpl. f_equal. apply IH. destruct Hin as [Hin|Hin]; [congruence|exact Hin].
Qed.
Lemma transfer_keys_local : forall
  (qm : finite_map qubit_reference (participant * fin))
  (Hqm : quantum_map_wf qm)
  (sv : state_vector (length (elems qubit_reference (participant * fin) qm)))
  (Hsv : state_vector_wf sv) (new : participant) (q : qubit_reference)
  (old : participant) (n : fin) (Hlookup : qm q = Some (old,n)),
  map fst (elems qubit_reference (participant * fin)
    (proj1_sig (projT1 (transfer_qubit_from_lookup qm Hqm sv Hsv new q old n Hlookup)))) =
  map fst (elems qubit_reference (participant * fin) qm).
Proof.
  intros qm Hqm sv Hsv new q old n Hlookup.
  unfold transfer_qubit_from_lookup; simpl.
  eapply replace_or_add_fst_same.
  apply in_map_iff.
  exists (q,(old,n)); split; [reflexivity|].
  apply (proj2 ((proj2 (specs _ _ qm)) q (old,n))).
  exact Hlookup.
Qed.

Lemma get_all_values_insert_away : forall
  (qm : finite_map qubit_reference (participant * fin))
  (q : qubit_reference) (v : participant * fin) (l : list qubit_reference),
  ~ In q l -> get_all_values (insert (KEQ:=qr_dec) qm q v) l = get_all_values qm l.
Proof.
  intros qm q v l; induction l as [|a l IH]; intros Hnot.
  - reflexivity.
  - cbn [get_all_values].
  assert (Hneq : q <> a) by (intro Heq; apply Hnot; left; symmetry; exact Heq).
  rewrite insert_neq by exact Hneq.
  rewrite IH by (intro Hin; apply Hnot; right; exact Hin).
  reflexivity.
Qed.

Lemma apply_unitary_transfer_away : forall
    (qm : finite_map qubit_reference (participant * fin))
    (Hqm : quantum_map_wf qm)
    (sv : state_vector (length (elems qubit_reference (participant * fin) qm)))
    (Hsv : state_vector_wf sv)
    (new old owner : participant) (q : qubit_reference) (n : fin)
    (Hlookup : qm q = Some (old,n))
    (lq : list qubit_reference) (dim : nat) (U : base_Unitary dim)
    (Hlen : length lq = dim) (Hnd : NoDup lq) (Hdim : dim > 0) (qsT : quantum_state),
    apply_unitary (insert (KEQ:=qr_dec) qm q (new,n))
      (Primitives.transfer_qubit_obligation_2 qm Hqm new q old n (eq_sym Hlookup))
      sv
      (Primitives.transfer_qubit_obligation_3 qm Hqm sv Hsv new q old n (eq_sym Hlookup))
      U lq Hlen Hdim = Some qsT ->
    ~ In q lq ->
    Forall (fun qi => exists i, (insert (KEQ:=qr_dec) qm q (new,n)) qi = Some (owner, i)) lq ->
    exists qs0 : quantum_state,
      apply_unitary qm Hqm sv Hsv U lq Hlen Hdim = Some qs0 /\
      proj1_sig (projT2 qsT) = proj1_sig (projT2 qs0).
Proof.
  intros qm Hqm sv Hsv new old owner q n Hlookup lq dim U Hlen Hnd Hdim qsT HapplyT Hnot HownersT.
  assert (Hlenmap : length (elems qubit_reference (participant * fin)
    (insert (KEQ:=qr_dec) qm q (new,n))) = length (elems qubit_reference (participant * fin) qm)).
  {
    pose proof (proj2 ((proj2 (specs _ _ qm)) q (old,n)) Hlookup) as Hin.
    unfold insert; simpl.
    rewrite replace_or_add_In_length with (a:=q); [reflexivity|].
    exists (old,n); exact Hin.
  }
  assert (Howners : Forall (fun qi => exists i, qm qi = Some (owner, i)) lq).
  {
    apply Forall_forall; intros qi Hin.
    rewrite Forall_forall in HownersT.
    destruct (HownersT qi Hin) as [i HownT].
    assert (Hqi : qi <> q).
    { intro Heq; subst qi; apply Hnot; exact Hin. }
    exists i. rewrite insert_neq in HownT by congruence. exact HownT.
  }
  pose proof (Happly_size (insert (KEQ:=qr_dec) qm q (new,n))
    (Primitives.transfer_qubit_obligation_2 qm Hqm new q old n (eq_sym Hlookup))
    sv (Primitives.transfer_qubit_obligation_3 qm Hqm sv Hsv new q old n (eq_sym Hlookup))
    dim U lq Hlen Hdim qsT HapplyT) as HsizeT.
  assert (Hsize : dim <= length (elems qubit_reference (participant * fin) qm)).
  { rewrite <- Hlenmap; exact HsizeT. }
  destruct (Happly_exists qm Hqm sv Hsv dim U lq Hlen Hdim Hsize
    Hnd (ex_intro _ owner Howners)) as [qs0 Happly0].
  exists qs0; split; [exact Happly0|].
  destruct (Hresult_vector (insert (KEQ:=qr_dec) qm q (new,n))
    (Primitives.transfer_qubit_obligation_2 qm Hqm new q old n (eq_sym Hlookup))
    sv (Primitives.transfer_qubit_obligation_3 qm Hqm sv Hsv new q old n (eq_sym Hlookup))
    dim U lq Hlen Hdim qsT HapplyT)
    as [lpnT [HgetT [HidxT HvecT]]].
  destruct (Hresult_vector qm Hqm sv Hsv dim U lq Hlen Hdim qs0 Happly0)
    as [lpn0 [Hget0 [Hidx0 Hvec0]]].
  rewrite get_all_values_insert_away in HgetT by exact Hnot.
  assert (Hlpn : lpnT = lpn0) by congruence.
  subst lpn0.
  assert (Hbase_irrel : forall d0 d1 (Hd : d0 = d1)
    (lpn : list (participant * fin))
    (Hproof0 : length (map snd lpn) = dim /\
      NoDup (map snd lpn) /\ Forall (fun i => i < d0) (map snd lpn))
    (Hproof1 : length (map snd lpn) = dim /\
      NoDup (map snd lpn) /\ Forall (fun i => i < d1) (map snd lpn)),
    uc_eval (proj1_sig (base_to_ucom U (map snd lpn) Hproof0)) =
    uc_eval (proj1_sig (base_to_ucom U (map snd lpn) Hproof1))).
  { intros d0 d1 Hd lpn Hp0 Hp1. destruct Hd.
    assert (Hp : Hp0 = Hp1) by apply proof_irrelevance.
    rewrite Hp; reflexivity. }
  assert (Hgate :
    uc_eval (proj1_sig (base_to_ucom U (map snd lpnT) HidxT)) =
    uc_eval (proj1_sig (base_to_ucom U (map snd lpnT) Hidx0))).
  { exact (Hbase_irrel _ _ Hlenmap lpnT HidxT Hidx0). }
  rewrite HvecT, Hvec0, Hgate, Hlenmap.
  reflexivity.
Qed.

(* Merged from FCTwoMeasurementTransfer.v. *)
Require Import Lia Permutation String Coq.Program.Equality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import SST session QUEST QuantumGateTeleportation ExamplesHelpers FunctionalCorrectnessHelpers.
From SQIR Require Import SQIR.
Require Import SQIR.UnitaryOps SQIR.Equivalences.
Open Scope nat_scope.
Lemma measure_qubit_from_nonzero_all_proofs_irrel : forall
  (qm : finite_map qubit_reference (participant * fin))
  (sv : state_vector (length (elems qubit_reference (participant * fin) qm)))
  (q : qubit_reference) (owner : participant) (index : fin) (result : bool)
  (Hqm1 Hqm2 : quantum_map_wf qm) (Hsv1 Hsv2 : state_vector_wf sv)
  (Hlookup1 Hlookup2 : qm q = Some (owner,index))
  (Hlen1 Hlen2 : (0 < length (elems qubit_reference (participant * fin) qm))%nat)
  (Hnz1 Hnz2 : norm (proj index (length (elems qubit_reference (participant * fin) qm)) result × sv) <> 0%R),
  measure_qubit_from_nonzero qm Hqm1 sv Hsv1 q owner index result Hlookup1 Hlen1 Hnz1 =
  measure_qubit_from_nonzero qm Hqm2 sv Hsv2 q owner index result Hlookup2 Hlen2 Hnz2.
Proof.
  intros qm sv q owner index result Hqm1 Hqm2 Hsv1 Hsv2 Hlookup1 Hlookup2 Hlen1 Hlen2 Hnz1 Hnz2.
  assert (E1 : Hqm1 = Hqm2) by apply proof_irrelevance; subst Hqm2.
  assert (E2 : Hsv1 = Hsv2) by apply proof_irrelevance; subst Hsv2.
  assert (E3 : Hlookup1 = Hlookup2) by apply proof_irrelevance; subst Hlookup2.
  assert (E4 : Hlen1 = Hlen2) by apply proof_irrelevance; subst Hlen2.
  assert (E5 : Hnz1 = Hnz2) by apply proof_irrelevance; subst Hnz2.
  reflexivity.
Qed.


Lemma transport_qmap_measure_cast : forall n m (Hmn : m = n)
    (Hn : 0 < n) (Hm : 0 < m) (v : state_vector n),
  transport_state_vector
    (eq_trans (eq_sym Hmn) (eq_sym (Nat.succ_pred_pos m Hm))) v =
  transport_state_vector (eq_sym (Nat.succ_pred_pos n Hn)) v.
Proof.
  intros n m Hmn Hn Hm v.
  destruct Hmn.
  assert (Hm = Hn) by apply proof_irrelevance.
  subst Hm.
  assert (Hp : eq_trans (eq_sym eq_refl) (eq_sym (Nat.succ_pred_pos m Hn)) = eq_sym (Nat.succ_pred_pos m Hn)) by apply proof_irrelevance.
  rewrite Hp; reflexivity.
Qed.
Lemma insert_existing_length : forall
    (qm : finite_map qubit_reference (participant * fin))
    (q : qubit_reference) (old : participant) (n : fin) (new : participant)
    (Hlookup : qm q = Some (old,n)),
    length (elems qubit_reference (participant * fin)
      (insert (KEQ:=qr_dec) qm q (new,n))) =
    length (elems qubit_reference (participant * fin) qm).
Proof.
  intros qm q old n new Hlookup.
  pose proof (proj2 ((proj2 (specs _ _ qm)) q (old,n)) Hlookup) as Hin.
  unfold insert; simpl.
  rewrite (replace_or_add_In_length qubit_reference (participant * fin) qr_dec
    (elems qubit_reference (participant * fin) qm) q); eauto.
Qed.

Lemma remove_transfer_commute : forall
    (qm : finite_map qubit_reference (participant * fin))
    (q measured : qubit_reference) (index : fin)
    (old new : participant) (n : fin),
    qm q = Some (old,n) -> q <> measured ->
    equivalent
      (remove_and_reindex_qubit_map (insert (KEQ:=qr_dec) qm q (new,n)) measured index)
      (insert (KEQ:=qr_dec)
        (remove_and_reindex_qubit_map qm measured index) q
        (new, shift_wire_index index n)).
Proof.
  intros qm q measured index old new n Hlookup Hqmneq.
  unfold equivalent, included; split.
  - intros key [owner idx] Hmap.
    destruct (qr_dec key q) as [Heq|Hkeyneq].
    + subst key.
      rewrite (Hremove_lookup (insert (KEQ:=qr_dec) qm q (new,n)) q
        measured index new n Hqmneq ltac:(rewrite insert_eq; reflexivity)) in Hmap.
      inversion Hmap; subst owner idx.
      rewrite insert_eq; reflexivity.
    + assert (Hkeymeas : key <> measured).
      {
        intro Heq; subst key.
        pose proof (remove_and_reindex_qubit_map_lookup_none
          (insert (KEQ:=qr_dec) qm q (new,n)) measured index measured) as Hnone.
        assert (Hnotnone : remove_and_reindex_qubit_map
          (insert (KEQ:=qr_dec) qm q (new,n)) measured index measured <> None)
          by (rewrite Hmap; discriminate).
        apply (proj1 Hnone) in Hnotnone; tauto.
      }
      destruct (Hremove_lookup_inv
        (insert (KEQ:=qr_dec) qm q (new,n)) key measured index owner idx
        Hkeymeas Hmap) as [n0 [HkeyT Hshift]].
      rewrite insert_neq in HkeyT by congruence.
      rewrite (Hremove_lookup (insert (KEQ:=qr_dec) qm q (new,n)) key
        measured index owner n0 Hkeymeas ltac:(rewrite insert_neq by congruence; exact HkeyT))
        in Hmap.
      inversion Hmap; subst idx.
      rewrite insert_neq by congruence.
      rewrite (Hremove_lookup qm key measured index owner n0 Hkeymeas HkeyT).
      reflexivity.
  - intros key [owner idx] Hmap.
    destruct (qr_dec key q) as [Heq|Hkeyneq].
    + subst key.
      rewrite insert_eq in Hmap.
      inversion Hmap; subst owner idx.
      rewrite (Hremove_lookup (insert (KEQ:=qr_dec) qm q (new,n)) q
        measured index new n Hqmneq ltac:(rewrite insert_eq; reflexivity)).
      reflexivity.
    + rewrite insert_neq in Hmap by congruence.
      assert (Hkeymeas : key <> measured).
      {
        intro Heq; subst key.
        pose proof (remove_and_reindex_qubit_map_lookup_none
          qm measured index measured) as Hnone.
        assert (Hnotnone : remove_and_reindex_qubit_map qm measured index measured <> None)
          by (rewrite Hmap; discriminate).
        apply (proj1 Hnone) in Hnotnone; tauto.
      }
      destruct (Hremove_lookup_inv qm key measured index owner idx
        Hkeymeas Hmap) as [n0 [Hkey Hshift]].
      assert (HkeyT : insert (KEQ:=qr_dec) qm q (new,n) key = Some (owner,n0)).
      { rewrite insert_neq by congruence; exact Hkey. }
      rewrite (Hremove_lookup (insert (KEQ:=qr_dec) qm q (new,n)) key
        measured index owner n0 Hkeymeas HkeyT).
      rewrite <- Hshift; reflexivity.
Qed.

Lemma measure_transfer_outputs : forall
    (qm : finite_map qubit_reference (participant * fin)) (Hqm : quantum_map_wf qm)
    (sv : state_vector (length (elems qubit_reference (participant * fin) qm)))
    (Hsv : state_vector_wf sv) (old new actor : participant)
    (q measured : qubit_reference) (n measured_index : fin) (result : bool)
    (Hlookup : qm q = Some (old,n)) (Hdistinct : q <> measured)
    (Hmeasured : (insert (KEQ:=qr_dec) qm q (new,n)) measured = Some (actor,measured_index))
    (HlenT : (0 < length (elems qubit_reference (participant * fin)
      (insert (KEQ:=qr_dec) qm q (new,n))))%nat)
    (HnonzeroT : norm (proj measured_index
      (length (elems qubit_reference (participant * fin)
        (insert (KEQ:=qr_dec) qm q (new,n)))) result × sv) <> 0%R),
    let qmT := insert (KEQ:=qr_dec) qm q (new,n) in
    let HqmT := Primitives.transfer_qubit_obligation_2 qm Hqm new q old n (eq_sym Hlookup) in
    let HsvT := Primitives.transfer_qubit_obligation_3 qm Hqm sv Hsv new q old n (eq_sym Hlookup) in
    let Hlookup0 := ltac:(rewrite insert_neq in Hmeasured by congruence; exact Hmeasured) in
    let Hlen0 : (0 < length (elems qubit_reference (participant * fin) qm))%nat :=
      ltac:(pose proof (@insert_existing_length qm q old n new Hlookup) as Hkeys;
        rewrite <- Hkeys; exact HlenT) in
    let Hnonzero0 := ltac:(pose proof (@insert_existing_length qm q old n new Hlookup) as Hkeys;
      rewrite Hkeys in HnonzeroT; exact HnonzeroT) in
    let mT := measure_qubit_from_nonzero qmT HqmT sv HsvT measured actor measured_index result Hmeasured HlenT HnonzeroT in
    let m0 := measure_qubit_from_nonzero qm Hqm sv Hsv measured actor measured_index result Hlookup0 Hlen0 Hnonzero0 in
    proj1_sig (fst mT) = proj1_sig (fst m0) /\
    proj1_sig (projT2 (snd mT)) = proj1_sig (projT2 (snd m0)) /\
    equivalent (` (projT1 (snd mT)))
      (insert (KEQ:=qr_dec) (` (projT1 (snd m0))) q
        (new, shift_wire_index measured_index n)).
Proof.
  intros qm Hqm sv Hsv old new actor q measured n measured_index result
    Hlookup Hdistinct Hmeasured HlenT HnonzeroT.
  pose proof (insert_existing_length qm q old n new Hlookup) as Hlenmap.
  assert (Hsource_transport : transport_state_vector (eq_sym Hlenmap) sv = sv).
  { apply FunctionalCorrectnessHelpers.transport_state_vector_value. }
  assert (Hlookup0 : qm measured = Some (actor,measured_index)).
  { rewrite insert_neq in Hmeasured by congruence; exact Hmeasured. }
  assert (Hlen0 : (0 < length (elems qubit_reference (participant * fin) qm))%nat).
  { rewrite <- Hlenmap; exact HlenT. }
  assert (Hnonzero0 : norm
    (proj measured_index (length (elems qubit_reference (participant * fin) qm))
      result × sv) <> 0%R).
  { rewrite Hlenmap in HnonzeroT; exact HnonzeroT. }
  set (qmT := insert (KEQ:=qr_dec) qm q (new,n)).
  set (HqmT := Primitives.transfer_qubit_obligation_2 qm Hqm new q old n (eq_sym Hlookup)).
  set (HsvT := Primitives.transfer_qubit_obligation_3 qm Hqm sv Hsv new q old n (eq_sym Hlookup)).
  set (mT := measure_qubit_from_nonzero qmT HqmT sv HsvT measured actor measured_index result Hmeasured HlenT HnonzeroT).
  set (m0 := measure_qubit_from_nonzero qm Hqm sv Hsv measured actor measured_index result Hlookup0 Hlen0 Hnonzero0).
  assert (HoutT : proj1_sig (projT2 (snd mT)) =
    normalize_removed_wire
      (@Mmult (2 ^ Nat.pred (length (elems qubit_reference (participant * fin) qmT)))
        (2 ^ S (Nat.pred (length (elems qubit_reference (participant * fin) qmT)))) 1
        (remove_measured_wire_operator
          (Nat.pred (length (elems qubit_reference (participant * fin) qmT)))
          measured_index result)
        (proj measured_index
          (S (Nat.pred (length (elems qubit_reference (participant * fin) qmT))))
          result × transport_state_vector
            (eq_sym (Nat.succ_pred_pos
              (length (elems qubit_reference (participant * fin) qmT)) HlenT)) sv))).
  { unfold mT, measure_qubit_from_nonzero, measure_qubit_nonzero.
    apply FunctionalCorrectnessHelpers.measure_at_dimension_vector. }
  assert (Hout0 : proj1_sig (projT2 (snd m0)) =
    normalize_removed_wire
      (@Mmult (2 ^ Nat.pred (length (elems qubit_reference (participant * fin) qm)))
        (2 ^ S (Nat.pred (length (elems qubit_reference (participant * fin) qm)))) 1
        (remove_measured_wire_operator
          (Nat.pred (length (elems qubit_reference (participant * fin) qm)))
          measured_index result)
        (proj measured_index
          (S (Nat.pred (length (elems qubit_reference (participant * fin) qm))))
          result × transport_state_vector
            (eq_sym (Nat.succ_pred_pos
              (length (elems qubit_reference (participant * fin) qm)) Hlen0)) sv))).
  { unfold m0, measure_qubit_from_nonzero, measure_qubit_nonzero.
    apply FunctionalCorrectnessHelpers.measure_at_dimension_vector. }
  split.
  - unfold mT, m0; simpl.
    unfold insert in Hlenmap; simpl in Hlenmap; rewrite Hlenmap; reflexivity.
  - split.
    + match goal with
      | |- context[measure_qubit_from_nonzero qmT ?QWF ?V ?VWF measured actor measured_index result ?Hlk ?Hlen ?Hnz] =>
          let Heq := fresh in
          assert (Heq : measure_qubit_from_nonzero qmT QWF V VWF measured actor measured_index result Hlk Hlen Hnz = mT)
            by (apply measure_qubit_from_nonzero_all_proofs_irrel; apply proof_irrelevance);
          rewrite Heq
      end.
      match goal with
      | |- context[measure_qubit_from_nonzero qm Hqm sv Hsv measured actor measured_index result ?Hlk ?Hlen ?Hnz] =>
          let Heq := fresh in
          assert (Heq : measure_qubit_from_nonzero qm Hqm sv Hsv measured actor measured_index result Hlk Hlen Hnz = m0)
            by (apply measure_qubit_from_nonzero_all_proofs_irrel; apply proof_irrelevance);
          rewrite Heq
      end.
      dependent rewrite Hlenmap.
      rewrite HoutT, Hout0.
      assert (Hpred : Nat.pred (length (elems qubit_reference (participant * fin) qmT)) = Nat.pred (length (elems qubit_reference (participant * fin) qm))).
      { unfold qmT; rewrite Hlenmap; reflexivity. }
      f_equal.
      - exact Hpred.
      - f_equal.
        + f_equal; exact Hpred.
        + f_equal; f_equal; exact Hpred.
        + apply remove_measured_wire_operator_dimension_irrelevant; exact Hpred.
        + rewrite (proj_wire_dimension_irrelevant
            (S (Nat.pred (length (elems qubit_reference (participant * fin) qmT))))
            (S (Nat.pred (length (elems qubit_reference (participant * fin) qm))))
            measured_index result (f_equal S Hpred)).
          f_equal.
          - f_equal; f_equal; exact Hpred.
          - f_equal; f_equal; exact Hpred.
          - rewrite <- Hsource_transport at 1.
            rewrite <- QGTPath1HelperDefinitions.qgt_transport_state_vector_compose.
            exact (@transport_qmap_measure_cast
              (length (elems qubit_reference (participant * fin) qm))
              (length (elems qubit_reference (participant * fin) qmT))
              Hlenmap Hlen0 HlenT sv).
      + match goal with
      | |- context[measure_qubit_from_nonzero qmT ?QWF ?V ?VWF measured actor measured_index result ?Hlk ?Hlen ?Hnz] =>
          let Heq := fresh in
          assert (Heq : measure_qubit_from_nonzero qmT QWF V VWF measured actor measured_index result Hlk Hlen Hnz = mT)
            by (apply measure_qubit_from_nonzero_all_proofs_irrel; apply proof_irrelevance);
          rewrite Heq
      end.
      match goal with
      | |- context[measure_qubit_from_nonzero qm Hqm sv Hsv measured actor measured_index result ?Hlk ?Hlen ?Hnz] =>
          let Heq := fresh in
          assert (Heq : measure_qubit_from_nonzero qm Hqm sv Hsv measured actor measured_index result Hlk Hlen Hnz = m0)
            by (apply measure_qubit_from_nonzero_all_proofs_irrel; apply proof_irrelevance);
          rewrite Heq
      end.
      unfold mT, m0.
      rewrite !measure_qubit_nonzero_map.
      unfold qmT; apply remove_transfer_commute with (old := old) (new := new) (n := n); assumption.

Qed.

(* Merged from FCTwoTransferTau.v. *)
Require Import Lia Permutation String Coq.Program.Equality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import SST session QUEST QuantumGateTeleportation ExamplesHelpers FunctionalCorrectnessHelpers.
From SQIR Require Import SQIR.
Require Import SQIR.UnitaryOps SQIR.Equivalences.

Open Scope nat_scope.
Lemma transfer_tau_new : forall (qs : quantum_state) (M : session)
    (old new : participant) (q : qubit_reference) (n : fin)
    (Hlookup : (` (projT1 qs)) q = Some (old,n))
    (actor : participant) (qs' : quantum_state) (M' : session) (r : R),
    actor <> old -> actor <> new ->
    step (transfer_qubit_from_lookup (` (projT1 qs)) (proj2_sig (projT1 qs))
      (` (projT2 qs)) (proj2_sig (projT2 qs)) new q old n Hlookup, M)
      (Tau actor) (qs',M') r ->
    exists (qs0 : quantum_state) (n0 : fin) (Hlookup0 : (` (projT1 qs0)) q = Some (old,n0)),
      step (qs,M) (Tau actor) (qs0,M') r /\
      equivalent (` (projT1 qs'))
        (` (projT1 (transfer_qubit_from_lookup (` (projT1 qs0))
          (proj2_sig (projT1 qs0)) (` (projT2 qs0)) (proj2_sig (projT2 qs0))
          new q old n0 Hlookup0))) /\
      proj1_sig (projT2 qs') =
        proj1_sig (projT2 (transfer_qubit_from_lookup (` (projT1 qs0))
          (proj2_sig (projT1 qs0)) (` (projT2 qs0)) (proj2_sig (projT2 qs0))
          new q old n0 Hlookup0)).
Proof.
  intros qs M old new q n Hlookup actor qs' M' r Hactorold Hactornew Hstep.
  dependent induction Hstep; simpl in *; try discriminate.
  - (* New *)
    set (qtr := transfer_qubit_from_lookup (` (projT1 qs))
      (proj2_sig (projT1 qs)) (` (projT2 qs)) (proj2_sig (projT2 qs))
      new q old n Hlookup).
    assert (Hfresh0 : ~ In q0 (map fst (elems qubit_reference
      (participant * fin) (` (projT1 qs))))).
    {
      intro Hin.
      apply Hfresh.
      change (In q0 (map fst (elems qubit_reference
        (participant * fin) (` (projT1 qtr))))).
      unfold qtr.
      rewrite (@transfer_keys_local
        (` (projT1 qs)) (proj2_sig (projT1 qs)) (` (projT2 qs))
        (proj2_sig (projT2 qs)) new q old n Hlookup).
      exact Hin.
    }
    assert (Hqneq : q0 <> q).
    {
      intro Heq; subst q0.
      apply Hfresh0.
      apply in_map_iff.
      exists (q, (old,n)); split; [reflexivity|].
      apply (proj2 ((proj2 (specs _ _ (` (projT1 qs)))) q (old,n))).
      exact Hlookup.
    }
    set (qs0 := add_new_qubit qs actor q0 Hfresh0).
    assert (Hlookup0 : (` (projT1 qs0)) q = Some (old,n)).
    {
      unfold qs0, add_new_qubit; cbn [projT1 proj1_sig].
      rewrite insert_neq by congruence.
      exact Hlookup.
    }
    exists qs0, n, Hlookup0.
    split.
    + unfold qs0.
      eapply New with (Hfresh := Hfresh0).
      exact H.
    + split.
      * assert (Hlen : length (@replace_or_add qubit_reference (participant * fin) qr_dec
          (elems qubit_reference (participant * fin) (` (projT1 qs)))
          (q, (new,n))) = length (elems qubit_reference
            (participant * fin) (` (projT1 qs)))).
        { eapply (@replace_or_add_In_length qubit_reference (participant * fin) qr_dec
            (elems qubit_reference (participant * fin) (` (projT1 qs))) q).
          - exists (old,n).
            apply (proj2 ((proj2 (specs _ _ (` (projT1 qs)))) q (old,n))).
            exact Hlookup. }
        unfold qs0, add_new_qubit, transfer_qubit_from_lookup; simpl.
        rewrite Hlen.
        eapply insert_insert_comm.
        congruence.
      * simpl. reflexivity.
  - (* If 0 *)
    exists qs, n, Hlookup.
    split.
    + eapply If_0; eauto.
    + simpl. split; [apply equivalent_refl|reflexivity].
  - (* If 1 *)
    exists qs, n, Hlookup.
    split.
    + eapply If_1; eauto.
    + simpl. split; [apply equivalent_refl|reflexivity].
  - (* Meas *)
    assert (Hdistinct : q <> q0).
    {
      destruct (qr_dec q q0) as [Heq|Hneq]; [|exact Hneq].
      subst q0; simpl in Hlookup0; inversion Hlookup0; congruence.
    }
    assert (HmeasuredT : insert (KEQ:=qr_dec) (` (projT1 qs)) q (new,n) q0 =
      Some (actor,n0)) by exact Hlookup0.
    assert (Hlookup_base : (` (projT1 qs)) q0 = Some (actor,n0)).
    { rewrite insert_neq in HmeasuredT by congruence; exact HmeasuredT. }
    assert (HlenT : (0 < length (elems qubit_reference (participant * fin)
      (insert (KEQ:=qr_dec) (` (projT1 qs)) q (new,n))))%nat) by exact Hlen.
    assert (HnonzeroT : norm
      (proj n0
        (length (elems qubit_reference (participant * fin)
          (insert (KEQ:=qr_dec) (` (projT1 qs)) q (new,n))))
        r × (` (projT2 qs))) <> 0%R).
    { exact Hnonzero. }
    assert (Hlen_base : (0 < length (elems qubit_reference (participant * fin)
      (` (projT1 qs))))%nat).
    {
      pose proof (@insert_existing_length (` (projT1 qs)) q old n new Hlookup)
        as Hkeys.
      rewrite <- Hkeys; exact HlenT.
    }
    assert (Hnonzero_base : norm (proj n0
      (length (elems qubit_reference (participant * fin) (` (projT1 qs))))
      r × (` (projT2 qs))) <> 0%R).
    {
      pose proof (@insert_existing_length (` (projT1 qs)) q old n new Hlookup)
        as Hkeys.
      rewrite Hkeys in HnonzeroT; exact HnonzeroT.
    }
    set (mT := measure_qubit_from_nonzero
      (insert (KEQ:=qr_dec) (` (projT1 qs)) q (new,n))
      (Primitives.transfer_qubit_obligation_2 (` (projT1 qs))
        (proj2_sig (projT1 qs)) new q old n (eq_sym Hlookup))
      (` (projT2 qs))
      (Primitives.transfer_qubit_obligation_3 (` (projT1 qs))
        (proj2_sig (projT1 qs)) (` (projT2 qs)) (proj2_sig (projT2 qs))
        new q old n (eq_sym Hlookup))
      q0 actor n0 r HmeasuredT HlenT HnonzeroT).
    set (m0 := measure_qubit_from_nonzero (` (projT1 qs))
      (proj2_sig (projT1 qs)) (` (projT2 qs)) (proj2_sig (projT2 qs))
      q0 actor n0 r Hlookup_base Hlen_base Hnonzero_base).
    set (mT0 := measure_qubit_from_nonzero
      (insert (KEQ:=qr_dec) (` (projT1 qs)) q (new,n))
      (Primitives.transfer_qubit_obligation_2 (` (projT1 qs))
        (proj2_sig (projT1 qs)) new q old n (eq_sym Hlookup))
      (` (projT2 qs))
      (Primitives.transfer_qubit_obligation_3 (` (projT1 qs))
        (proj2_sig (projT1 qs)) (` (projT2 qs)) (proj2_sig (projT2 qs))
        new q old n (eq_sym Hlookup))
      q0 actor n0 r Hlookup0 Hlen Hnonzero).
    assert (HmTproof : mT0 = mT).
    { unfold mT0, mT; apply measure_qubit_from_nonzero_all_proofs_irrel;
      apply proof_irrelevance. }
    destruct (@measure_transfer_outputs (` (projT1 qs))
      (proj2_sig (projT1 qs)) (` (projT2 qs)) (proj2_sig (projT2 qs))
      old new actor q q0 n n0 r Hlookup Hdistinct HmeasuredT HlenT HnonzeroT)
      as [Hprob [Hvec Hmap]].
    assert (Hlookup_after :
      (` (projT1 (snd m0))) q = Some (old, shift_wire_index n0 n)).
    {
      unfold m0, measure_qubit_from_nonzero, measure_qubit_nonzero; simpl.
      eapply Hremove_lookup; [exact Hdistinct|exact Hlookup].
    }
    exists (snd m0), (shift_wire_index n0 n), Hlookup_after.
    split.
    + change (step (qs, M) (Tau actor)
        (snd m0, insert M actor
          (subst_expression_in_process 0 0 (Val (Bool r)) P))
        (proj1_sig (fst mT))).
      replace (proj1_sig (fst mT)) with (proj1_sig (fst m0))
        by (symmetry; exact Hprob).
      eapply Meas with (pi := fst m0) (q_state2 := snd m0).
      * exact H.
      * unfold m0; reflexivity.
    + split.
      * unfold mT, m0 in Hmap; simpl in Hmap.
        exact Hmap.
      * change (` (projT2 (snd mT0)) = ` (projT2 (snd m0))).
        rewrite HmTproof.
        lazymatch type of Hvec with
        | context [measure_qubit_from_nonzero
            (` (projT1 qs)) ?QWF (` (projT2 qs)) ?VWF q0 actor n0 r
            ?Hlk ?Hln ?Hnz] =>
            let m0h := constr:(measure_qubit_from_nonzero
              (` (projT1 qs)) QWF (` (projT2 qs)) VWF
              q0 actor n0 r Hlk Hln Hnz) in
            assert (Hm0eq : m0 = m0h) by
              (unfold m0; apply measure_qubit_from_nonzero_all_proofs_irrel;
               apply proof_irrelevance);
            rewrite Hm0eq
        end.
        exact Hvec.
  - (* Unitary *)
    assert (Hnot : ~ In q lq).
    {
      intro Hin.
      rewrite Forall_forall in H2.
      destruct (H2 q Hin) as [i Howner].
      destruct (qr_dec q q) as [Heq|Hneq]; [|congruence].
      simpl in Howner.
      inversion Howner; subst.
      apply Hactornew; congruence.
    }
    assert (Howners0 : Forall (fun qi => exists i,
      (` (projT1 qs)) qi = Some (actor,i)) lq).
    {
      apply Forall_forall; intros qi Hin.
      rewrite Forall_forall in H2.
      destruct (H2 qi Hin) as [i Howner].
      assert (Hqi : qi <> q).
      { intro Heq; subst qi; apply Hnot; exact Hin. }
      exists i.
      destruct (qr_dec q qi) as [Heq|Hneq]; [congruence|].
      simpl in Howner; exact Howner.
    }
    destruct (apply_unitary_transfer_away
      (` (projT1 qs)) (proj2_sig (projT1 qs))
      (` (projT2 qs)) (proj2_sig (projT2 qs))
      new old actor q n Hlookup lq dim U Hlen H1 Hdim qs' H0 Hnot H2)
      as [qs0 [Happly0 Hvec]].
    assert (Hlookup0 : (` (projT1 qs0)) q = Some (old,n)).
    {
      pose proof (Happly_map (` (projT1 qs)) (proj2_sig (projT1 qs))
        (` (projT2 qs)) (proj2_sig (projT2 qs)) dim U lq Hlen Hdim qs0 Happly0)
        as Hmap0.
      rewrite Hmap0; exact Hlookup.
    }
    pose proof (Happly_map
      (insert (KEQ:=qr_dec) (` (projT1 qs)) q (new,n))
      (Primitives.transfer_qubit_obligation_2 (` (projT1 qs))
        (proj2_sig (projT1 qs)) new q old n (eq_sym Hlookup))
      (` (projT2 qs))
      (Primitives.transfer_qubit_obligation_3 (` (projT1 qs))
        (proj2_sig (projT1 qs)) (` (projT2 qs)) (proj2_sig (projT2 qs))
        new q old n (eq_sym Hlookup)) dim U lq Hlen Hdim qs' H0) as HmapT.
    pose proof (Happly_map (` (projT1 qs)) (proj2_sig (projT1 qs))
      (` (projT2 qs)) (proj2_sig (projT2 qs)) dim U lq Hlen Hdim qs0 Happly0)
      as Hmap0.
    exists qs0, n, Hlookup0.
    split.
    + eapply Unitary with (Hlen := Hlen) (Hdim := Hdim); eauto.
    + split.
      * rewrite HmapT, Hmap0.
        apply equivalent_refl.
      * exact Hvec.
  - (* Congr *)
    destruct (IHHstep M' qs' actor n q new Hactornew old Hactorold M1' qs Hlookup)
      as [qs0 [n0 [Hlookup0 [Htau0 [Hmap0 Hvec0]]]]].
    + reflexivity.
    + reflexivity.
    + reflexivity.
    exists qs0, n0, Hlookup0.
    split.
    + eapply Congr; eauto.
    + split; assumption.
Qed.

(* Merged from FCTwoMapCommutation.v. *)
Require Import Lia Permutation String Coq.Program.Equality.
Require Import SST session QUEST QuantumGateTeleportation ExamplesHelpers FunctionalCorrectnessHelpers.
From SQIR Require Import SQIR.
Require Import SQIR.UnitaryOps SQIR.Equivalences.
Open Scope nat_scope.
Lemma reverse_four_inserts : forall A B (AEQ : EqDec A) (M : finite_map A B)
  (k1 k2 k3 k4 : A) (v1 v2 v3 v4 : B),
  k1 <> k2 -> k1 <> k3 -> k1 <> k4 ->
  k2 <> k3 -> k2 <> k4 -> k3 <> k4 ->
  equivalent
    (insert (KEQ:=AEQ) (insert (KEQ:=AEQ) (insert (KEQ:=AEQ) (insert (KEQ:=AEQ) M k1 v1) k2 v2) k3 v3) k4 v4)
    (insert (KEQ:=AEQ) (insert (KEQ:=AEQ) (insert (KEQ:=AEQ) (insert (KEQ:=AEQ) M k4 v4) k3 v3) k2 v2) k1 v1).
Proof.
  intros A B AEQ M k1 k2 k3 k4 v1 v2 v3 v4 H12 H13 H14 H23 H24 H34.
  unfold equivalent, included; split; intros key value Hmap.
  - destruct (AEQ key k1) as [->|Hk1].
    + rewrite insert_neq in Hmap by congruence.
      rewrite insert_neq in Hmap by congruence.
      rewrite insert_neq in Hmap by congruence.
      rewrite insert_eq in Hmap. inversion Hmap; subst value.
      rewrite insert_eq; reflexivity.
    + destruct (AEQ key k2) as [->|Hk2].
      * rewrite insert_neq in Hmap by congruence.
        rewrite insert_neq in Hmap by congruence.
        rewrite insert_eq in Hmap. inversion Hmap; subst value.
        rewrite insert_neq by congruence. rewrite insert_eq; reflexivity.
      * destruct (AEQ key k3) as [->|Hk3].
        -- rewrite insert_neq in Hmap by congruence.
           rewrite insert_eq in Hmap. inversion Hmap; subst value.
           rewrite insert_neq by congruence. rewrite insert_neq by congruence.
           rewrite insert_eq; reflexivity.
        -- destruct (AEQ key k4) as [->|Hk4].
           ++ rewrite insert_eq in Hmap. inversion Hmap; subst value.
              rewrite insert_neq by congruence. rewrite insert_neq by congruence.
              rewrite insert_neq by congruence. rewrite insert_eq; reflexivity.
           ++ repeat (rewrite insert_neq in Hmap by congruence).
              repeat (rewrite insert_neq by congruence).
              exact Hmap.
  - destruct (AEQ key k4) as [->|Hk4].
    + rewrite insert_neq in Hmap by congruence.
      rewrite insert_neq in Hmap by congruence.
      rewrite insert_neq in Hmap by congruence.
      rewrite insert_eq in Hmap. inversion Hmap; subst value.
      rewrite insert_eq; reflexivity.
    + destruct (AEQ key k3) as [->|Hk3].
      * rewrite insert_neq in Hmap by congruence.
        rewrite insert_neq in Hmap by congruence.
        rewrite insert_eq in Hmap. inversion Hmap; subst value.
        rewrite insert_neq by congruence. rewrite insert_eq; reflexivity.
      * destruct (AEQ key k2) as [->|Hk2].
        -- rewrite insert_neq in Hmap by congruence.
           rewrite insert_eq in Hmap. inversion Hmap; subst value.
           rewrite insert_neq by congruence. rewrite insert_neq by congruence.
           rewrite insert_eq; reflexivity.
        -- destruct (AEQ key k1) as [->|Hk1].
           ++ rewrite insert_eq in Hmap. inversion Hmap; subst value.
              rewrite insert_neq by congruence. rewrite insert_neq by congruence.
              rewrite insert_neq by congruence. rewrite insert_eq; reflexivity.
           ++ repeat (rewrite insert_neq in Hmap by congruence).
              repeat (rewrite insert_neq by congruence).
              exact Hmap.
Qed.

(* Merged from FCTwoTransferCommutation.v. *)
Require Import Lia Permutation String Coq.Program.Equality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import SST session QUEST QuantumGateTeleportation ExamplesHelpers FunctionalCorrectnessHelpers.
From SQIR Require Import SQIR.
Require Import SQIR.UnitaryOps SQIR.Equivalences.
Open Scope nat_scope.
Lemma two_transfers_commute : forall
  (qm : finite_map qubit_reference (participant * fin))
  (Hqm : quantum_map_wf qm)
  (sv : state_vector (length (elems qubit_reference (participant * fin) qm)))
  (Hsv : state_vector_wf sv)
  (q1 q2 : qubit_reference) (old1 old2 new1 new2 : participant)
  (n1 n2 : fin)
  (Hlookup1 : qm q1 = Some (old1,n1))
  (Hlookup2 : qm q2 = Some (old2,n2)) (Hneq : q1 <> q2),
  let qm1 := insert (KEQ:=qr_dec) qm q1 (new1,n1) in
  let Hqm1 := Primitives.transfer_qubit_obligation_2 qm Hqm new1 q1 old1 n1 (eq_sym Hlookup1) in
  let Hsv1 := Primitives.transfer_qubit_obligation_3 qm Hqm sv Hsv new1 q1 old1 n1 (eq_sym Hlookup1) in
  let Hlookup2' : qm1 q2 = Some (old2,n2) := ltac:(unfold qm1; rewrite insert_neq by congruence; exact Hlookup2) in
  let qs12 := transfer_qubit_from_lookup qm1 Hqm1 sv Hsv1 new2 q2 old2 n2 Hlookup2' in
  let qm2 := insert (KEQ:=qr_dec) qm q2 (new2,n2) in
  let Hqm2 := Primitives.transfer_qubit_obligation_2 qm Hqm new2 q2 old2 n2 (eq_sym Hlookup2) in
  let Hsv2 := Primitives.transfer_qubit_obligation_3 qm Hqm sv Hsv new2 q2 old2 n2 (eq_sym Hlookup2) in
  let Hlookup1' : qm2 q1 = Some (old1,n1) := ltac:(unfold qm2; rewrite insert_neq by congruence; exact Hlookup1) in
  let qs21 := transfer_qubit_from_lookup qm2 Hqm2 sv Hsv2 new1 q1 old1 n1 Hlookup1' in
  equivalent (` (projT1 qs12)) (` (projT1 qs21)) /\
  ` (projT2 qs12) = ` (projT2 qs21).
Proof.
  intros qm Hqm sv Hsv q1 q2 old1 old2 new1 new2 n1 n2 Hlookup1 Hlookup2 Hneq.
  split.
  - unfold equivalent, included; split.
    + intros key value Hmap.
      unfold transfer_qubit_from_lookup in *; simpl in *.
      eapply insert_insert_comm; eauto.
    + intros key value Hmap.
      unfold transfer_qubit_from_lookup in *; simpl in *.
      eapply insert_insert_comm; eauto.
  - reflexivity.
Qed.

(* Merged from FCTwoSwapHelpers.v. *)
Require Import Lia Permutation String Coq.Program.Equality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import SST session QUEST QuantumGateTeleportation ExamplesHelpers FunctionalCorrectnessHelpers.
From SQIR Require Import SQIR.
From SQIR Require Import UnitaryOps Equivalences.


Open Scope nat_scope.
Opaque pairwise_sorted insert equivalent.

Lemma step_transmit_extract : forall (qs : quantum_state) (M : session)
  (p q : participant) (l : label) (v : value)
  (qs' : quantum_state) (M' : session) (r : R),
  step (qs,M) (Transmit p q l v) (qs',M') r ->
  exists Mbase e P lQ Q,
    unfoldM M Mbase /\
    Mbase p = Some (p_send q l e P) /\
    Mbase q = Some (p_recv p lQ) /\
    p <> q /\ onth l lQ = Some Q /\ evaluate_expression e = Some v /\
    ( (forall q0, v <> QVal q0) /\ qs' = qs /\ r = 1%R
    \/ exists q0 n (Hlookup : (` (projT1 qs)) q0 = Some (p,n)),
        v = QVal q0 /\
        qs' = transfer_qubit_from_lookup (` (projT1 qs))
          (proj2_sig (projT1 qs)) (` (projT2 qs)) (proj2_sig (projT2 qs))
          q q0 p n Hlookup /\ r = 1%R) /\
    unfoldM (insert (insert Mbase q
      (subst_expression_in_process 0 0 (Val v) Q)) p P) M'.
Proof.
  fix IH 10.
  intros qs M p q l v qs' M' r Hstep.
  dependent destruction Hstep; simpl in *; try discriminate.
  - exists M, e, P, lQ, Q.
    repeat split; try assumption; try apply unfoldM_refl.
    left; repeat split; try assumption; try reflexivity; apply unfoldM_refl.
  - exists M, e, P, lQ, Q.
    repeat split; try assumption; try apply unfoldM_refl.
    right; repeat eexists; try reflexivity; try eassumption; apply unfoldM_refl.
  - destruct (IH qs M1' p q l v qs' M' r Hstep)
      as [Mbase [e [P [lQ [Q [Hsource [Hp [Hq [Hpq [Hon [Heval Hresult]]]]]]]]]]].
    destruct Hresult as [Hkind Houtput].
    exists Mbase, e, P, lQ, Q.
    repeat split; try assumption.
    all: eapply unfoldM_trans; eassumption.
Qed.

Lemma transfer_lookup_new_owner : forall
  (qm : finite_map qubit_reference (participant * fin))
  (Hqm : quantum_map_wf qm)
  (sv : state_vector (length (elems qubit_reference (participant * fin) qm)))
  (Hsv : state_vector_wf sv) new q old n
  (Hlookup : qm q = Some (old,n)),
  proj1_sig (projT1
    (transfer_qubit_from_lookup qm Hqm sv Hsv new q old n Hlookup)) q =
      Some (new,n).
Proof.
  intros; unfold transfer_qubit_from_lookup; simpl; apply insert_eq.
Qed.

Lemma two_transfers_payloads_disjoint : forall p1 q1 l1 v1 p2 q2 l2 v2
    s s' pi,
  multistep s
    (Transmit p1 q1 l1 v1 :: Transmit p2 q2 l2 v2 :: nil) s' pi ->
  p1 <> p2 -> p1 <> q2 -> q1 <> p2 -> q1 <> q2 ->
  should_swap_payloads_disjoint v1 v2 = true.
Proof.
  intros p1 q1 l1 v1 p2 q2 l2 v2 s s' pi Hmulti Hp1 Hp2 Hq1 Hq2.
  destruct s as [qs0 M0].
  inversion Hmulti as [|st0 st1 st2 r1 r2 a la Hstep1 Htail]; subst.
  inversion Htail as [|st1' st2' st3' r3 r4 a' la' Hstep2 Htail2]; subst.
  destruct st1 as [qs1 M1].
  destruct v1 as [n1|b1|w1]; destruct v2 as [n2|b2|w2]; simpl; try reflexivity.
  destruct (step_transmit_extract _ _ _ _ _ _ _ _ _ Hstep1)
    as [Mb1 [e1 [P1 [lQ1 [Q1 [Hsrc1 [Hsend1 [Hrecv1 [Hpq1
      [Hon1 [Heval1 [Hkind1 Hout1]]]]]]]]]]]].
  destruct st2' as [qs2 M2].
  destruct (step_transmit_extract _ _ _ _ _ _ _ _ _ Hstep2)
    as [Mb2 [e2 [P2 [lQ2 [Q2 [Hsrc2 [Hsend2 [Hrecv2 [Hpq2
      [Hon2 [Heval2 [Hkind2 Hout2]]]]]]]]]]]].
  destruct Hkind1 as [[Hclass1 [Hqs1c Hr1c]]|
    [q0 [n0 [Hlookup0 [Hv0 [Hqs1 Hrtx1]]]]]].
  - exfalso; exact (Hclass1 w1 eq_refl).
  - inversion Hv0; subst q0.
    destruct Hkind2 as [[Hclass2 [Hqs2c Hr2c]]|
      [q3 [n3 [Hlookup3 [Hv3 [Hqs2 Hrtx2]]]]]].
    + exfalso; exact (Hclass2 w2 eq_refl).
    + inversion Hv3; subst q3.
      destruct (qr_dec w1 w2) as [Heq|Hneq].
      * subst w2; subst qs1.
        pose proof (@transfer_lookup_new_owner
          (` (projT1 qs0)) (proj2_sig (projT1 qs0))
          (` (projT2 qs0)) (proj2_sig (projT2 qs0)) q1 w1 p1 n0 Hlookup0)
          as Howner.
        pose proof Hlookup3 as Hlookup3copy.
        rewrite Howner in Hlookup3copy.
        inversion Hlookup3copy; subst; congruence.
      * reflexivity.
Qed.

Lemma Hlookup_frame_two : forall M0 p P q Q Msrc actor Pcur,
  p <> actor -> q <> actor ->
  unfoldM (insert (insert M0 q Q) p P) Msrc ->
  Msrc actor = Some Pcur ->
  exists Pbase, M0 actor = Some Pbase /\ precongP Pbase Pcur.
Proof.
  intros M0 p P q Q Msrc actor Pcur Hp Hq Hsrc Hlookup.
  destruct (Hlookup_frame (insert M0 q Q) p P Msrc actor Pcur Hp Hsrc Hlookup)
    as [Pmid [Hmid Hpre2]].
  destruct (Hlookup_frame M0 q Q (insert M0 q Q) actor Pmid Hq
    (unfoldM_refl _) Hmid) as [Pbase [Hbase Hpre1]].
  exists Pbase; split; [exact Hbase|].
  eapply gttT; eassumption.
Qed.

Lemma Htau_frame_two : forall qs M0 p P q Q Msrc actor qs' Mdst r,
  p <> actor -> q <> actor ->
  unfoldM (insert (insert M0 q Q) p P) Msrc ->
  step (qs,Msrc) (Tau actor) (qs',Mdst) r ->
  exists R Mout,
    step (qs,M0) (Tau actor) (qs',Mout) r /\
    equivalent Mout (insert M0 actor R) /\
    unfoldM (insert (insert (insert M0 actor R) q Q) p P) Mdst.
Proof.
  fix IH 15.
  intros qs M0 p P q Q Msrc actor qs' Mdst r Hp Hq Hsrc Hstep.
  dependent destruction Hstep; simpl in *; try discriminate.
  - destruct (Hlookup_frame_two M0 p P q Q Msrc actor (p_newq P0)
      Hp Hq Hsrc ltac:(match goal with Hcur : ?src actor = Some ?proc |- _ => exact Hcur end))
      as [Pbase [Hbase Hpre]].
    set (Mbase := insert M0 actor (p_newq P0)).
    set (R := subst_expression_in_process 0 0 (Val (QVal q0)) P0).
    exists R, (insert Mbase actor R). split.
    + eapply Congr with (M1' := Mbase).
      * unfold Mbase; eapply Hmake_unfold; eauto.
      * eapply New with (Hfresh := Hfresh).
        unfold Mbase; rewrite insert_eq; reflexivity.
    + split.
      * unfold Mbase, R; apply insert_insert_noop.
      * eapply unfoldM_trans.
        -- apply Hinsert_unfold. apply Hinsert_comm_unfold; congruence.
        -- eapply Hinsert_frame; eauto.
  - destruct (Hlookup_frame_two M0 p P q Q Msrc actor (p_ite e P1 P0)
      Hp Hq Hsrc ltac:(match goal with Hcur : ?src actor = Some ?proc |- _ => exact Hcur end))
      as [Pbase [Hbase Hpre]].
    set (Mbase := insert M0 actor (p_ite e P1 P0)).
    exists P0, (insert Mbase actor P0). split.
    + eapply Congr with (M1' := Mbase).
      * unfold Mbase; eapply Hmake_unfold; eauto.
      * eapply If_0.
        -- unfold Mbase; rewrite insert_eq; reflexivity.
        -- lazymatch goal with Heval : evaluate_expression e = Some (Bool false) |- _ => exact Heval end.
    + split.
      * unfold Mbase; apply insert_insert_noop.
      * eapply unfoldM_trans.
        -- apply Hinsert_unfold. apply Hinsert_comm_unfold; congruence.
        -- eapply Hinsert_frame; eauto.
  - destruct (Hlookup_frame_two M0 p P q Q Msrc actor (p_ite e P1 P0)
      Hp Hq Hsrc ltac:(match goal with Hcur : ?src actor = Some ?proc |- _ => exact Hcur end))
      as [Pbase [Hbase Hpre]].
    set (Mbase := insert M0 actor (p_ite e P1 P0)).
    exists P1, (insert Mbase actor P1). split.
    + eapply Congr with (M1' := Mbase).
      * unfold Mbase; eapply Hmake_unfold; eauto.
      * eapply If_1.
        -- unfold Mbase; rewrite insert_eq; reflexivity.
        -- lazymatch goal with Heval : evaluate_expression e = Some (Bool true) |- _ => exact Heval end.
    + split.
      * unfold Mbase; apply insert_insert_noop.
      * eapply unfoldM_trans.
        -- apply Hinsert_unfold. apply Hinsert_comm_unfold; congruence.
        -- eapply Hinsert_frame; eauto.
  - destruct (Hlookup_frame_two M0 p P q Q Msrc actor
      (p_measure (Val (QVal q0)) P0) Hp Hq Hsrc
      ltac:(match goal with Hcur : ?src actor = Some ?proc |- _ => exact Hcur end))
      as [Pbase [Hbase Hpre]].
    set (Mbase := insert M0 actor (p_measure (Val (QVal q0)) P0)).
    set (R := subst_expression_in_process 0 0 (Val (Bool r)) P0).
    exists R, (insert Mbase actor R).
    set (measured := measure_qubit_from_nonzero
      (` (projT1 qs)) (proj2_sig (projT1 qs))
      (` (projT2 qs)) (proj2_sig (projT2 qs))
      q0 actor n r Hlookup Hlen Hnonzero).
    split.
    + eapply Congr with (M1' := Mbase).
      * unfold Mbase; eapply Hmake_unfold; eauto.
      * eapply Meas with (pi := fst measured) (q_state2 := snd measured).
        -- unfold Mbase; rewrite insert_eq; reflexivity.
        -- unfold measured; reflexivity.
    + split.
      * unfold Mbase, R; apply insert_insert_noop.
      * eapply unfoldM_trans.
        -- apply Hinsert_unfold. apply Hinsert_comm_unfold; congruence.
        -- eapply Hinsert_frame; eauto.
  - destruct (Hlookup_frame_two M0 p P q Q Msrc actor
      (p_unitary dim U (map (fun z => Val (QVal z)) lq) P0)
      Hp Hq Hsrc ltac:(match goal with Hcur : ?src actor = Some ?proc |- _ => exact Hcur end))
      as [Pbase [Hbase Hpre]].
    set (Mbase := insert M0 actor
      (p_unitary dim U (map (fun z => Val (QVal z)) lq) P0)).
    exists P0, (insert Mbase actor P0). split.
    + eapply Congr with (M1' := Mbase).
      * unfold Mbase; eapply Hmake_unfold; eauto.
      * eapply Unitary; eauto.
        unfold Mbase; rewrite insert_eq; reflexivity.
    + split.
      * unfold Mbase; apply insert_insert_noop.
      * eapply unfoldM_trans.
        -- apply Hinsert_unfold. apply Hinsert_comm_unfold; congruence.
        -- eapply Hinsert_frame; eauto.
  - pose proof (Hunfold_trans _ _ _ Hsrc H) as Hsrc'.
    destruct (IH qs M0 p P q Q M1' actor qs' Mdst r Hp Hq Hsrc' Hstep)
      as [R [Mout [Hnew [Hequiv Htarget]]]].
    exists R, Mout; split; [exact Hnew|]. split; assumption.
Qed.

Lemma equivalent_insert_lookup : forall (Mafter Mbase : session)
  (actor : participant) (R : process) (p : participant) (P : process),
  equivalent Mafter (insert Mbase actor R) ->
  p <> actor -> (forall R0, P <> p_rec R0) ->
  Mbase p = Some P -> Mafter p = Some P.
Proof.
  intros Mafter Mbase actor R p P Hequiv Hneq Hnonrec Hlookup.
  eapply unfoldM_lookup_nonrec.
  - apply equivalent_unfoldM, equivalent_sym; exact Hequiv.
  - rewrite insert_neq by congruence; exact Hlookup.
  - exact Hnonrec.
Qed.

Lemma tx_tau_swap : forall (qs0 : quantum_state) (M0 : session)
  (p q : participant) (l : label) (v : value) (qs1 : quantum_state)
  (M1 : session) (actor : participant) (qs2 : quantum_state) (M2 : session)
  (rtx rtau : R),
  step (qs0,M0) (Transmit p q l v) (qs1,M1) rtx ->
  step (qs1,M1) (Tau actor) (qs2,M2) rtau ->
  p <> actor -> q <> actor ->
  exists qsrev Mrev,
    multistep (qs0,M0) (Tau actor :: Transmit p q l v :: nil)
      (qsrev,Mrev) (rtx * (rtau * 1)) /\
    unfoldM Mrev M2 /\
    equivalent (` (projT1 qsrev)) (` (projT1 qs2)) /\
    proj1_sig (projT2 qsrev) = proj1_sig (projT2 qs2).
Proof.
  intros qs0 M0 p q l v qs1 M1 actor qs2 M2 rtx rtau Htx Htau Hp Ha.
  destruct (step_transmit_extract _ _ _ _ _ _ _ _ _ Htx)
    as [Mbase [e [P [lQ [Q [Hbase [Hsend [Hrecv [Hneq [Honth [Heval Hresult]]]]]]]]]]].
  destruct (@step_tau_decompose qs1 M1 actor qs2 M2 rtau Htau)
    as [Mtausrc [Mtaudst [Htausrc [Htauc Htauout]]]].
  destruct Hresult as [Hkind Htxout].
  destruct Hkind as [[Hnotq [Hqs1 Hrtx]]
    |[q0 [n [Hlookup [Hv [Hqs1 Hrtx]]]]]].
  - subst qs1.
    set (Q' := subst_expression_in_process 0 0 (Val v) Q).
    assert (Hsource : unfoldM (insert (insert Mbase q Q') p P) Mtausrc).
    { eapply unfoldM_trans; [exact Htxout|exact Htausrc]. }
    destruct (@Htau_frame_two qs0 Mbase p P q Q' Mtausrc actor
      qs2 Mtaudst rtau Hp Ha Hsource Htauc)
      as [R [Mafter [Htaubase [Hafter Htarget]]]].
    assert (Hsend_after : Mafter p = Some (p_send q l e P)).
    { eapply equivalent_insert_lookup; [exact Hafter|exact Hp|intros R0 Hrec; discriminate|exact Hsend]. }
    assert (Hrecv_after : Mafter q = Some (p_recv p lQ)).
    { eapply equivalent_insert_lookup; [exact Hafter|exact Ha|intros R0 Hrec; discriminate|exact Hrecv]. }
    set (Mrev := insert (insert Mafter q Q') p P).
    assert (Hsession : unfoldM Mrev M2).
    {
      eapply unfoldM_trans.
      - apply unfoldM_insert_two. apply equivalent_unfoldM. exact Hafter.
      - eapply unfoldM_trans; [exact Htarget|exact Htauout].
    }
    exists qs2, Mrev; split.
    + replace (rtx * (rtau * 1))%R with (rtau * (1 * 1))%R
        by (rewrite Hrtx; ring).
      eapply ms_step with (s2 := (qs2,Mafter)).
      * eapply Congr with (M1' := Mbase).
        -- exact Hbase.
        -- exact Htaubase.
      * eapply ms_step with (s2 := (qs2,Mrev)).
        -- exact (@Comm_C p q l e P lQ l Q v Mafter qs2
             Hsend_after Hrecv_after Hneq Honth Heval Hnotq).
        -- eapply ms_refl. apply equivalent_refl.
    + split; [exact Hsession|].
      split; [apply equivalent_refl|reflexivity].
  - subst qs1.
    subst v.
    set (Q' := subst_expression_in_process 0 0 (Val (QVal q0)) Q).
    assert (Hsource : unfoldM (insert (insert Mbase q Q') p P) Mtausrc).
    { eapply unfoldM_trans; [exact Htxout|exact Htausrc]. }
    destruct (@Htau_frame_two
      (transfer_qubit_from_lookup (` (projT1 qs0))
        (proj2_sig (projT1 qs0)) (` (projT2 qs0))
        (proj2_sig (projT2 qs0)) q q0 p n Hlookup)
      Mbase p P q Q' Mtausrc actor qs2 Mtaudst rtau Hp Ha Hsource Htauc)
      as [R [Mafter [Htaubase [Hafter Htarget]]]].
    destruct (transfer_tau_new qs0 Mbase p q q0 n Hlookup actor qs2 Mafter rtau
      ltac:(congruence) ltac:(congruence) Htaubase)
      as [qsTau [n0 [Hlookup0 [Htaupre [Hmap Hvec]]]]].
    assert (Hsend_after : Mafter p = Some (p_send q l e P)).
    { eapply equivalent_insert_lookup; [exact Hafter|exact Hp|intros R0 Hrec; discriminate|exact Hsend]. }
    assert (Hrecv_after : Mafter q = Some (p_recv p lQ)).
    { eapply equivalent_insert_lookup; [exact Hafter|exact Ha|intros R0 Hrec; discriminate|exact Hrecv]. }
    set (Mrev := insert (insert Mafter q Q') p P).
    set (qsrev := transfer_qubit_from_lookup (` (projT1 qsTau))
      (proj2_sig (projT1 qsTau)) (` (projT2 qsTau))
      (proj2_sig (projT2 qsTau)) q q0 p n0 Hlookup0).
    assert (Hsession : unfoldM Mrev M2).
    {
      eapply unfoldM_trans.
      - apply unfoldM_insert_two. apply equivalent_unfoldM. exact Hafter.
      - eapply unfoldM_trans; [exact Htarget|exact Htauout].
    }
    exists qsrev, Mrev; split.
    + replace (rtx * (rtau * 1))%R with (rtau * (1 * 1))%R
        by (rewrite Hrtx; ring).
      eapply ms_step with (s2 := (qsTau,Mafter)).
      * eapply Congr with (M1' := Mbase).
        -- exact Hbase.
        -- exact Htaupre.
      * eapply ms_step with (s2 := (qsrev,Mrev)).
        -- unfold qsrev, Mrev.
           exact (@Comm_Q p q l e P lQ l Q q0 Mafter qsTau
             (transfer_qubit_from_lookup (` (projT1 qsTau))
               (proj2_sig (projT1 qsTau)) (` (projT2 qsTau))
               (proj2_sig (projT2 qsTau)) q q0 p n0 Hlookup0)
             n0 Hlookup0 Hsend_after Hrecv_after Hneq Honth Heval eq_refl).
        -- eapply ms_refl. apply equivalent_refl.
    + split; [exact Hsession|].
      split.
      * unfold qsrev; apply equivalent_sym; exact Hmap.
      * unfold qsrev; symmetry; exact Hvec.
Qed.

Lemma should_swap_tx_facts : forall (p q r s : participant)
  (l l' : label) (v v' : value),
  should_swap (Transmit p q l v) (Transmit r s l' v') = true ->
  p <> r /\ p <> s /\ q <> r /\ q <> s /\
  should_swap_payloads_disjoint v v' = true.
Proof.
  intros [pn] [qn] [rn] [sn] l l' v v' Hswap; simpl in *.
  apply andb_true_iff in Hswap as [Hpayload Hrest].
  apply andb_true_iff in Hrest as [Hendpoints Horder].
  apply andb_true_iff in Hendpoints as [Hleft Hright].
  apply andb_true_iff in Hleft as [Hpr Hps].
  apply andb_true_iff in Hright as [Hqr Hqs].
  apply negb_true_iff in Hpr; apply String.eqb_neq in Hpr.
  apply negb_true_iff in Hps; apply String.eqb_neq in Hps.
  apply negb_true_iff in Hqr; apply String.eqb_neq in Hqr.
  apply negb_true_iff in Hqs; apply String.eqb_neq in Hqs.
  repeat split; try assumption.
  - intro Heq; inversion Heq; subst; contradiction.
  - intro Heq; inversion Heq; subst; contradiction.
  - intro Heq; inversion Heq; subst; contradiction.
  - intro Heq; inversion Heq; subst; contradiction.
Qed.

Lemma should_swap_payloads_disjoint_qneq : forall q1 q2,
  should_swap_payloads_disjoint (QVal q1) (QVal q2) = true -> q1 <> q2.
Proof.
  intros q1 q2 H; simpl in H.
  destruct (qr_dec q1 q2); congruence.
Qed.

Lemma should_swap_tx_tau_facts : forall (p q r : participant)
  (l : label) (v : value),
  should_swap (Transmit p q l v) (Tau r) = true ->
  p <> r /\ q <> r.
Proof.
  intros [pn] [qn] [rn] l v Hswap; simpl in Hswap.
  apply andb_true_iff in Hswap as [Hpr Hqr].
  apply negb_true_iff in Hpr; apply String.eqb_neq in Hpr.
  apply negb_true_iff in Hqr; apply String.eqb_neq in Hqr.
  split.
  - intro Heq; inversion Heq; subst; contradiction.
  - intro Heq; inversion Heq; subst; contradiction.
Qed.

Lemma Hinsert_pair_override : forall (M : session) (p q : participant)
  (Qpre Ppre Qout Pout : process),
  p <> q ->
  unfoldM
    (insert (insert (insert (insert M q Qpre) p Ppre) q Qout) p Pout)
    (insert (insert M q Qout) p Pout).
Proof.
  intros M p q Qpre Ppre Qout Pout Hneq.
  eapply unfoldM_trans.
  - apply Hinsert_unfold with (p := p) (P := Pout).
    apply Hinsert_comm_unfold; congruence.
  - eapply unfoldM_trans.
    + apply Hinsert_unfold with (p := p) (P := Pout).
      apply Hinsert_unfold with (p := p) (P := Ppre).
      exact (@Hinsert_same_frame M q Qpre Qout).
    + exact (@Hinsert_same_frame (insert M q Qout) p Ppre Pout).
Qed.

Lemma transfer_qubit_from_lookup_proof_irrel : forall
  (qm : finite_map qubit_reference (participant * fin))
  (Hqm : quantum_map_wf qm)
  (sv : state_vector (length (elems qubit_reference (participant * fin) qm)))
  (Hsv : state_vector_wf sv) (new : participant) (q : qubit_reference)
  (old : participant) (n : fin)
  (Hlookup1 Hlookup2 : qm q = Some (old,n)),
  transfer_qubit_from_lookup qm Hqm sv Hsv new q old n Hlookup1 =
  transfer_qubit_from_lookup qm Hqm sv Hsv new q old n Hlookup2.
Proof.
  intros; assert (Hlookup1 = Hlookup2) by apply proof_irrelevance; subst; reflexivity.
Qed.

Lemma tx_tx_swap : forall (qs0 : quantum_state) (M0 : session)
  (p1 q1 : participant) (l1 : label) (v1 : value)
  (qs1 : quantum_state) (M1 : session)
  (p2 q2 : participant) (l2 : label) (v2 : value)
  (qs2 : quantum_state) (M2 : session) (r1 r2 : R),
  step (qs0,M0) (Transmit p1 q1 l1 v1) (qs1,M1) r1 ->
  step (qs1,M1) (Transmit p2 q2 l2 v2) (qs2,M2) r2 ->
  p1 <> p2 -> p1 <> q2 -> q1 <> p2 -> q1 <> q2 ->
  should_swap_payloads_disjoint v1 v2 = true ->
  exists qsrev Mrev,
    multistep (qs0,M0)
      (Transmit p2 q2 l2 v2 :: Transmit p1 q1 l1 v1 :: nil)
      (qsrev,Mrev) (r1 * (r2 * 1)) /\
    unfoldM Mrev M2 /\
    equivalent (` (projT1 qsrev)) (` (projT1 qs2)) /\
    proj1_sig (projT2 qsrev) = proj1_sig (projT2 qs2).
Proof.
  intros qs0 M0 p1 q1 l1 v1 qs1 M1 p2 q2 l2 v2 qs2 M2 r1 r2
    Htx1 Htx2 H12 H14 H32 H34 Hpayload.
  destruct (step_transmit_extract qs0 M0 p1 q1 l1 v1 qs1 M1 r1 Htx1)
    as [B1 [e1 [P1 [lQ1 [C1 [Hbase1 [Hsend1 [Hrecv1 [Hneq1
      [Honth1 [Heval1 Hresult1]]]]]]]]]]].
  destruct (step_transmit_extract qs1 M1 p2 q2 l2 v2 qs2 M2 r2 Htx2)
    as [B2 [e2 [P2 [lQ2 [C2 [Hbase2 [Hsend2 [Hrecv2 [Hneq2
      [Honth2 [Heval2 Hresult2]]]]]]]]]]].
  destruct Hresult1 as [Hkind1 Htx1out].
  destruct Hresult2 as [Hkind2 Htx2out].
  set (R1 := subst_expression_in_process 0 0 (Val v1) C1).
  set (R2 := subst_expression_in_process 0 0 (Val v2) C2).
  assert (Hfirst_to_B2 : unfoldM
      (insert (insert B1 q1 R1) p1 P1) B2).
  { eapply unfoldM_trans; eassumption. }
  destruct (@Hlookup_frame_two B1 p1 P1 q1 R1 B2 p2
      (p_send q2 l2 e2 P2) H12 H32 Hfirst_to_B2 Hsend2)
    as [P2base [Hbase2p Hpre2p]].
  destruct (@Hlookup_frame_two B1 p1 P1 q1 R1 B2 q2
      (p_recv p2 lQ2) H14 H34 Hfirst_to_B2 Hrecv2)
    as [Q2base [Hbase2q Hpre2q]].
  set (Bnorm2 := insert (insert B1 q2 (p_recv p2 lQ2)) p2
    (p_send q2 l2 e2 P2)).
  assert (Hnorm2 : unfoldM B1 Bnorm2).
  {
    eapply unfoldM_trans.
    - eapply Hmake_unfold; eassumption.
    - eapply Hmake_unfold.
      + unfold Bnorm2; rewrite insert_neq by congruence; exact Hbase2p.
      + exact Hpre2p.
  }
  assert (Hstart : unfoldM M0 Bnorm2).
  { eapply unfoldM_trans; [exact Hbase1|exact Hnorm2]. }
  assert (Hsend2norm : Bnorm2 p2 = Some (p_send q2 l2 e2 P2)).
  { unfold Bnorm2; rewrite insert_eq; reflexivity. }
  assert (Hrecv2norm : Bnorm2 q2 = Some (p_recv p2 lQ2)).
  { unfold Bnorm2; rewrite insert_neq by congruence; rewrite insert_eq; reflexivity. }
  set (MmidRev2 := insert (insert Bnorm2 q2 R2) p2 P2).
  set (Mrev := insert (insert MmidRev2 q1 R1) p1 P1).
  assert (Hsend1rev : MmidRev2 p1 = Some (p_send q1 l1 e1 P1)).
  { unfold MmidRev2, Bnorm2; repeat rewrite insert_neq by congruence; exact Hsend1. }
  assert (Hrecv1rev : MmidRev2 q1 = Some (p_recv p1 lQ1)).
  { unfold MmidRev2, Bnorm2; repeat rewrite insert_neq by congruence; exact Hrecv1. }
  assert (Hforward : unfoldM
      (insert (insert (insert (insert B1 q1 R1) p1 P1) q2 R2) p2 P2) M2).
  {
    eapply unfoldM_trans.
    - apply unfoldM_insert_two. exact Hfirst_to_B2.
    - exact Htx2out.
  }
  set (Fforward := insert (insert (insert (insert B1 q1 R1) p1 P1) q2 R2) p2 P2).
  set (Fmid1 := insert (insert (insert (insert B1 p1 P1) q1 R1) q2 R2) p2 P2).
  set (Fmid2 := insert (insert (insert (insert B1 p1 P1) q1 R1) p2 P2) q2 R2).
  set (Freverse := insert (insert (insert (insert B1 q2 R2) p2 P2) q1 R1) p1 P1).
  assert (Hpair1 : equivalent (insert (insert B1 q1 R1) p1 P1)
      (insert (insert B1 p1 P1) q1 R1)).
  { apply insert_insert_comm; congruence. }
  assert (Hpair2 : equivalent
      (insert (insert (insert (insert B1 p1 P1) q1 R1) q2 R2) p2 P2)
      (insert (insert (insert (insert B1 p1 P1) q1 R1) p2 P2) q2 R2)).
  { apply insert_insert_comm; congruence. }
  assert (Hfour : equivalent Fmid2 Freverse).
  { unfold Fmid2, Freverse.
    exact (@reverse_four_inserts participant process participant_dec B1
      p1 q1 p2 q2 P1 R1 P2 R2 Hneq1 H12 H14 H32 H34 Hneq2). }
  assert (Hfour_unfold : unfoldM Freverse Fforward).
  {
    eapply unfoldM_trans.
    - apply equivalent_unfoldM, equivalent_sym; exact Hfour.
    - eapply unfoldM_trans.
      + apply equivalent_unfoldM, equivalent_sym; exact Hpair2.
      + unfold Fmid1, Fforward.
        apply unfoldM_insert_two.
        apply equivalent_unfoldM, equivalent_sym; exact Hpair1.
  }
  assert (Hrev_session : unfoldM Mrev M2).
  {
    eapply unfoldM_trans.
    - apply unfoldM_insert_two.
      exact (Hinsert_pair_override B1 p2 q2 (p_recv p2 lQ2)
        (p_send q2 l2 e2 P2) R2 P2 ltac:(congruence)).
    - eapply unfoldM_trans; [exact Hfour_unfold|exact Hforward].
  }
  destruct Hkind1 as [[Hnotq1 [Hqs1 Hr1]]
    |[w1 [n1 [Hlookup1 [Hv1 [Hqs1 Hr1]]]]]].
  - subst qs1.
    destruct Hkind2 as [[Hnotq2 [Hqs2 Hr2]]
      |[w2 [n2 [Hlookup2 [Hv2 [Hqs2 Hr2]]]]]].
    + subst qs2.
      set (Mrev2step :=
        @Comm_C p2 q2 l2 e2 P2 lQ2 l2 C2 v2 Bnorm2 qs0
          Hsend2norm Hrecv2norm Hneq2 Honth2 Heval2 Hnotq2).
      assert (Hstep2rev : step (qs0,M0) (Transmit p2 q2 l2 v2)
          (qs0,MmidRev2) 1%R).
      { eapply Congr with (M1' := Bnorm2); [exact Hstart|].
        unfold Mrev2step, MmidRev2; exact Mrev2step. }
      assert (Hstep1rev : step (qs0,MmidRev2) (Transmit p1 q1 l1 v1)
          (qs0,Mrev) 1%R).
      { unfold Mrev; exact (@Comm_C p1 q1 l1 e1 P1 lQ1 l1 C1 v1
          MmidRev2 qs0 Hsend1rev Hrecv1rev Hneq1 Honth1 Heval1 Hnotq1). }
      exists qs0, Mrev; split.
      * replace (r1 * (r2 * 1))%R with (1 * (1 * 1))%R by (rewrite Hr1, Hr2; ring).
        eapply ms_step; [exact Hstep2rev|].
        eapply ms_step; [exact Hstep1rev|].
        eapply ms_refl; apply equivalent_refl.
      * split; [exact Hrev_session|].
        split; [apply equivalent_refl|reflexivity].
    + subst v2.
      subst qs2.
      set (qsMid := transfer_qubit_from_lookup (` (projT1 qs0))
        (proj2_sig (projT1 qs0)) (` (projT2 qs0))
        (proj2_sig (projT2 qs0)) q2 w2 p2 n2 Hlookup2).
      set (Mrev2step :=
        @Comm_Q p2 q2 l2 e2 P2 lQ2 l2 C2 w2 Bnorm2 qs0 qsMid n2
          Hlookup2 Hsend2norm Hrecv2norm Hneq2 Honth2 Heval2 eq_refl).
      assert (Hstep2rev : step (qs0,M0) (Transmit p2 q2 l2 (QVal w2))
          (qsMid,MmidRev2) 1%R).
      { eapply Congr with (M1' := Bnorm2); [exact Hstart|].
        unfold Mrev2step, MmidRev2; exact Mrev2step. }
      assert (Hstep1rev : step (qsMid,MmidRev2) (Transmit p1 q1 l1 v1)
          (qsMid,Mrev) 1%R).
      { unfold Mrev; exact (@Comm_C p1 q1 l1 e1 P1 lQ1 l1 C1 v1
          MmidRev2 qsMid Hsend1rev Hrecv1rev Hneq1 Honth1 Heval1 Hnotq1). }
      exists qsMid, Mrev; split.
      * replace (r1 * (r2 * 1))%R with (1 * (1 * 1))%R by (rewrite Hr1, Hr2; ring).
        eapply ms_step; [exact Hstep2rev|].
        eapply ms_step; [exact Hstep1rev|].
        eapply ms_refl; apply equivalent_refl.
      * split; [exact Hrev_session|].
        split; [apply equivalent_refl|reflexivity].
  - subst v1.
    subst qs1.
    destruct Hkind2 as [[Hnotq2 [Hqs2 Hr2]]
      |[w2 [n2 [Hlookup2 [Hv2 [Hqs2 Hr2]]]]]].
    + subst qs2.
      set (Mrev2step :=
        @Comm_C p2 q2 l2 e2 P2 lQ2 l2 C2 v2 Bnorm2 qs0
          Hsend2norm Hrecv2norm Hneq2 Honth2 Heval2 Hnotq2).
      assert (Hstep2rev : step (qs0,M0) (Transmit p2 q2 l2 v2)
          (qs0,MmidRev2) 1%R).
      { eapply Congr with (M1' := Bnorm2); [exact Hstart|].
        unfold Mrev2step, MmidRev2; exact Mrev2step. }
      assert (Hlookup1rev : (` (projT1 qs0)) w1 = Some (p1,n1)) by exact Hlookup1.
      set (qsrev := transfer_qubit_from_lookup (` (projT1 qs0))
        (proj2_sig (projT1 qs0)) (` (projT2 qs0))
        (proj2_sig (projT2 qs0)) q1 w1 p1 n1 Hlookup1rev).
      assert (Hstep1rev : step (qs0,MmidRev2) (Transmit p1 q1 l1 (QVal w1))
          (qsrev,Mrev) 1%R).
      { unfold qsrev, Mrev.
        exact (@Comm_Q p1 q1 l1 e1 P1 lQ1 l1 C1 w1 MmidRev2 qs0
          (transfer_qubit_from_lookup (` (projT1 qs0))
            (proj2_sig (projT1 qs0)) (` (projT2 qs0))
            (proj2_sig (projT2 qs0)) q1 w1 p1 n1 Hlookup1rev)
          n1 Hlookup1rev Hsend1rev Hrecv1rev Hneq1 Honth1 Heval1 eq_refl). }
      exists qsrev, Mrev; split.
      * replace (r1 * (r2 * 1))%R with (1 * (1 * 1))%R by (rewrite Hr1, Hr2; ring).
        eapply ms_step; [exact Hstep2rev|].
        eapply ms_step; [exact Hstep1rev|].
        eapply ms_refl; apply equivalent_refl.
      * split; [exact Hrev_session|].
        split; [apply equivalent_refl|reflexivity].
    + subst v2.
      assert (Hwire : w1 <> w2).
      { eapply should_swap_payloads_disjoint_qneq; exact Hpayload. }
      set (qsOrig := qs0).
      destruct qs0 as [[qm Hqm] [sv Hsv]]; simpl in *.
      assert (Hlookup2base : qm w2 = Some (p2,n2)).
      {
        pose proof Hlookup2 as Hlookup2tmp.
        unfold transfer_qubit_from_lookup in Hlookup2tmp; simpl in Hlookup2tmp.
        rewrite insert_neq in Hlookup2tmp by exact Hwire.
        exact Hlookup2tmp.
      }
      set (qm1 := insert (KEQ:=qr_dec) qm w1 (q1,n1)).
      set (Hqm1 := Primitives.transfer_qubit_obligation_2 qm Hqm q1 w1 p1 n1
        (eq_sym Hlookup1)).
      set (Hsv1 := Primitives.transfer_qubit_obligation_3 qm Hqm sv Hsv q1 w1 p1 n1
        (eq_sym Hlookup1)).
      assert (Hlookup2after1 : qm1 w2 = Some (p2,n2)).
      { unfold qm1; rewrite insert_neq by congruence; exact Hlookup2base. }
      set (qsAfter1 := transfer_qubit_from_lookup qm Hqm sv Hsv q1 w1 p1 n1 Hlookup1).
      set (qsForward := transfer_qubit_from_lookup qm1 Hqm1 sv Hsv1
        q2 w2 p2 n2 Hlookup2after1).
      assert (Hforward_eq : qs2 = qsForward).
      {
        rewrite Hqs2.
        unfold qsForward, qsAfter1, qm1, Hqm1, Hsv1.
        eapply transfer_qubit_from_lookup_proof_irrel.
      }
      set (qm2 := insert (KEQ:=qr_dec) qm w2 (q2,n2)).
      set (Hqm2 := Primitives.transfer_qubit_obligation_2 qm Hqm q2 w2 p2 n2
        (eq_sym Hlookup2base)).
      set (Hsv2 := Primitives.transfer_qubit_obligation_3 qm Hqm sv Hsv q2 w2 p2 n2
        (eq_sym Hlookup2base)).
      assert (Hlookup1after2 : qm2 w1 = Some (p1,n1)).
      { unfold qm2; rewrite insert_neq by congruence; exact Hlookup1. }
      set (qsMid := transfer_qubit_from_lookup qm Hqm sv Hsv q2 w2 p2 n2 Hlookup2base).
      set (qsrev := transfer_qubit_from_lookup qm2 Hqm2 sv Hsv2
        q1 w1 p1 n1 Hlookup1after2).
      pose proof (@two_transfers_commute qm Hqm sv Hsv w1 w2 p1 p2 q1 q2
        n1 n2 Hlookup1 Hlookup2base Hwire) as [_ Hveccomm].
      assert (Hmapcomm : equivalent (` (projT1 qsForward)) (` (projT1 qsrev))).
      {
        unfold qsForward, qsrev, qsMid, transfer_qubit_from_lookup; simpl.
        apply insert_insert_comm; exact Hwire.
      }
      assert (Hstep2rev : step (qsOrig,M0)
          (Transmit p2 q2 l2 (QVal w2)) (qsMid,MmidRev2) 1%R).
      {
        eapply Congr with (M1' := Bnorm2); [exact Hstart|].
        unfold MmidRev2, Bnorm2, R2.
        exact (@Comm_Q p2 q2 l2 e2 P2 lQ2 l2 C2 w2 Bnorm2 qsOrig qsMid n2
          Hlookup2base Hsend2norm Hrecv2norm Hneq2 Honth2 Heval2 eq_refl).
      }
      assert (Hstep1rev : step (qsMid,MmidRev2)
          (Transmit p1 q1 l1 (QVal w1)) (qsrev,Mrev) 1%R).
      {
        unfold qsrev, Mrev, R1.
        exact (@Comm_Q p1 q1 l1 e1 P1 lQ1 l1 C1 w1 MmidRev2 qsMid qsrev n1
          Hlookup1after2 Hsend1rev Hrecv1rev Hneq1 Honth1 Heval1 eq_refl).
      }
      exists qsrev, Mrev; split.
      * replace (r1 * (r2 * 1))%R with (1 * (1 * 1))%R by (rewrite Hr1, Hr2; ring).
        eapply ms_step; [exact Hstep2rev|].
        eapply ms_step; [exact Hstep1rev|].
        eapply ms_refl; apply equivalent_refl.
      * split; [exact Hrev_session|].
        split.
        -- rewrite Hforward_eq; apply equivalent_sym; exact Hmapcomm.
        -- rewrite Hforward_eq; symmetry; exact Hveccomm.
Qed.

Transparent pairwise_sorted insert equivalent.

(* Merged from FCTwoTauSwap.v. *)
Require Import Lia Permutation String Coq.Program.Equality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import SST session QUEST QuantumGateTeleportation ExamplesHelpers FunctionalCorrectnessHelpers.
From SQIR Require Import SQIR UnitaryOps Equivalences.


Open Scope nat_scope.
Lemma tau_swap_transport_state_vector_compose : forall n m k
    (Hnm : n = m) (Hmk : m = k) (v : state_vector n),
    transport_state_vector Hmk (transport_state_vector Hnm v) =
      transport_state_vector (eq_trans Hnm Hmk) v.
Proof.
  intros n m k Hnm Hmk v.
  destruct Hnm, Hmk; reflexivity.
Qed.

Lemma tau_swap_normalize_transport : forall n m (Hnm : n = m)
    (v : state_vector n),
    transport_state_vector Hnm (normalize_removed_wire v) =
      normalize_removed_wire (transport_state_vector Hnm v).
Proof.
  intros n m Hnm v; destruct Hnm; reflexivity.
Qed.

Lemma tau_swap_contraction_transport : forall n m (Hnm : n = m)
    (i : fin) (b : bool) (v : state_vector (S n)),
    transport_state_vector Hnm
      (contraction_apply (measurement_contraction n i b) v) =
    contraction_apply (measurement_contraction m i b)
      (transport_state_vector (f_equal S Hnm) v).
Proof.
  intros n m Hnm i b v; destruct Hnm; reflexivity.
Qed.

Inductive tau_core : quantum_state -> session -> participant ->
    quantum_state -> session -> R -> Prop :=
| tau_core_new : forall (p : participant) (P : process) (M : session)
    (qs : quantum_state) (q : qubit_reference)
    (Hfresh : ~ In q (map fst (elems qubit_reference
      (participant * fin) (` (projT1 qs)))))
    (Hproc : M p = Some (p_newq P)),
    tau_core qs M p (add_new_qubit qs p q Hfresh)
      (insert M p (subst_expression_in_process 0 0 (Val (QVal q)) P)) 1%R
| tau_core_if0 : forall (p : participant) (e : expression)
    (P1 P0 : process) (M : session) (qs : quantum_state)
    (Hproc : M p = Some (p_ite e P1 P0))
    (Heval : evaluate_expression e = Some (Bool false)),
    tau_core qs M p qs (insert M p P0) 1%R
| tau_core_if1 : forall (p : participant) (e : expression)
    (P1 P0 : process) (M : session) (qs : quantum_state)
    (Hproc : M p = Some (p_ite e P1 P0))
    (Heval : evaluate_expression e = Some (Bool true)),
    tau_core qs M p qs (insert M p P1) 1%R
| tau_core_meas : forall (p : participant) (q : qubit_reference)
    (P : process) (M : session) (qs qs' : quantum_state)
    (n : fin) (result : bool)
    (prob : {x : R | (x > 0)%R})
    (Hlookup : (` (projT1 qs)) q = Some (p,n))
    (Hlen : 0 < length (elems qubit_reference (participant * fin) (` (projT1 qs))))
    (Hnonzero : norm (proj n
      (length (elems qubit_reference (participant * fin) (` (projT1 qs))))
      result × (` (projT2 qs))) <> 0%R)
    (Hproc : M p = Some (p_measure (Val (QVal q)) P))
    (Hmeasure : (prob,qs') = measure_qubit_from_nonzero (` (projT1 qs))
      (proj2_sig (projT1 qs)) (` (projT2 qs)) (proj2_sig (projT2 qs))
      q p n result Hlookup Hlen Hnonzero),
    tau_core qs M p qs'
      (insert M p (subst_expression_in_process 0 0 (Val (Bool result)) P))
      (proj1_sig prob)
| tau_core_unitary : forall (dim : nat) (p : participant)
    (U : base_Unitary dim) (lq : list qubit_reference) (P : process)
    (M : session) (qs qs' : quantum_state)
    (Hlen : length lq = dim) (Hdim : dim > 0)
    (Hproc : M p = Some (p_unitary dim U (map (fun z => Val (QVal z)) lq) P))
    (Happly : apply_unitary (` (projT1 qs)) (proj2_sig (projT1 qs))
      (` (projT2 qs)) (proj2_sig (projT2 qs)) U lq Hlen Hdim = Some qs')
    (Hnd : NoDup lq)
    (Howners : Forall (fun q => exists n, (` (projT1 qs)) q = Some (p,n)) lq),
    tau_core qs M p qs' (insert M p P) 1%R.

Lemma tau_core_to_step : forall qs M p qs' M' r,
    tau_core qs M p qs' M' r -> step (qs,M) (Tau p) (qs',M') r.
Proof.
  intros qs M p qs' M' r Hcore; induction Hcore.
  - simpl; eapply New; eassumption.
  - simpl; eapply If_0; eassumption.
  - simpl; eapply If_1; eassumption.
  - simpl; eapply Meas; eassumption.
  - simpl; eapply Unitary; eassumption.
Qed.

Lemma step_tau_decompose_core : forall qs M actor qs' M' r,
  step (qs,M) (Tau actor) (qs',M') r ->
  exists Mbase Mcore,
    unfoldM M Mbase /\ tau_core qs Mbase actor qs' Mcore r /\ unfoldM Mcore M'.
Proof.
  intros qs M actor qs' M' r Hstep.
  dependent induction Hstep; try discriminate.
  - exists M,s2; split; [apply unfoldM_refl|].
    split; [eapply tau_core_new; eauto|apply unfoldM_refl].
  - exists M,s2; split; [apply unfoldM_refl|].
    split; [eapply tau_core_if0; eauto|apply unfoldM_refl].
  - exists M,s2; split; [apply unfoldM_refl|].
    split; [eapply tau_core_if1; eauto|apply unfoldM_refl].
  - exists M,s2; split; [apply unfoldM_refl|].
    split.
    + set (measured := measure_qubit_from_nonzero
        (` (projT1 qs)) (proj2_sig (projT1 qs))
        (` (projT2 qs)) (proj2_sig (projT2 qs))
        q actor n r Hlookup Hlen Hnonzero).
      eapply tau_core_meas with
        (prob := fst measured) (n := n) (result := r)
        (Hlookup := Hlookup) (Hlen := Hlen) (Hnonzero := Hnonzero).
      * exact H.
      * unfold measured; reflexivity.
    + apply unfoldM_refl.
  - exists M,s2; split; [apply unfoldM_refl|].
    split; [eapply tau_core_unitary; eauto|apply unfoldM_refl].
  - destruct (IHHstep qs M1' actor qs' M' ltac:(reflexivity) eq_refl ltac:(reflexivity))
      as [Mbase [Mcore [Hsrc [Hcore Hout]]]].
    exists Mbase,Mcore; split.
    + eapply unfoldM_trans; eassumption.
    + split; assumption.
Qed.

Lemma tau_if0_first_swap : forall (qs : quantum_state) (M : session)
  (p : participant) (e : expression) (P1 P0 : process) (Mmid : session)
  (q : participant) (qs2 : quantum_state) (Mend : session) (r : R),
  p <> q ->
  M p = Some (p_ite e P1 P0) ->
  evaluate_expression e = Some (Bool false) ->
  unfoldM (insert M p P0) Mmid ->
  step (qs,Mmid) (Tau q) (qs2,Mend) r ->
  exists s'',
    multistep (qs,M) (Tau q :: Tau p :: nil) s'' (r * (1 * 1)) /\
    equivalent_states (qs2,Mend) s''.
Proof.
  intros qs M p e P1 P0 Mmid q qs2 Mend r Hneq Hlookup Heval Hmid Hsecond.
  destruct (@Htau_frame qs M p P0 Mmid q qs2 Mend r Hneq Hmid Hsecond)
    as [Q [Mq [Hq [Hq_equiv Htarget]]]].
  assert (Hif : step (qs2,insert M q Q) (Tau p)
      (qs2,insert (insert M q Q) p P0) 1%R).
  { eapply If_0.
    - rewrite insert_neq by congruence; exact Hlookup.
    - exact Heval. }
  assert (Hsource_equiv : equivalent_states
      (qs2,insert M q Q) (qs2,Mq)).
  { unfold equivalent_states; simpl.
    split; [apply equivalent_unfoldM; exact Hq_equiv|].
    split; [apply equivalent_refl|reflexivity]. }
  destruct (step_equivalent_states _ _ _ _ _ Hif Hsource_equiv)
    as [sLift [Hif_lifted Hstateeq]].
  destruct sLift as [qsLift Mlift].
  exists (qsLift,Mlift); split.
  - eapply ms_step with (s2 := (qs2,Mq)).
    + exact Hq.
    + eapply ms_step with (s2 := (qsLift,Mlift)).
      * exact Hif_lifted.
      * eapply ms_refl; apply equivalent_refl.
  - unfold equivalent_states; simpl.
    split.
    + eapply Hunfold_trans; [exact (proj1 Hstateeq)|exact Htarget].
    + exact (proj2 Hstateeq).
Qed.

Lemma tau_if1_first_swap : forall (qs : quantum_state) (M : session)
  (p : participant) (e : expression) (P1 P0 : process) (Mmid : session)
  (q : participant) (qs2 : quantum_state) (Mend : session) (r : R),
  p <> q ->
  M p = Some (p_ite e P1 P0) ->
  evaluate_expression e = Some (Bool true) ->
  unfoldM (insert M p P1) Mmid ->
  step (qs,Mmid) (Tau q) (qs2,Mend) r ->
  exists s'',
    multistep (qs,M) (Tau q :: Tau p :: nil) s'' (r * (1 * 1)) /\
    equivalent_states (qs2,Mend) s''.
Proof.
  intros qs M p e P1 P0 Mmid q qs2 Mend r Hneq Hlookup Heval Hmid Hsecond.
  destruct (@Htau_frame qs M p P1 Mmid q qs2 Mend r Hneq Hmid Hsecond)
    as [Q [Mq [Hq [Hq_equiv Htarget]]]].
  assert (Hif : step (qs2,insert M q Q) (Tau p)
      (qs2,insert (insert M q Q) p P1) 1%R).
  { eapply If_1.
    - rewrite insert_neq by congruence; exact Hlookup.
    - exact Heval. }
  assert (Hsource_equiv : equivalent_states
      (qs2,insert M q Q) (qs2,Mq)).
  { unfold equivalent_states; simpl.
    split; [apply equivalent_unfoldM; exact Hq_equiv|].
    split; [apply equivalent_refl|reflexivity]. }
  destruct (step_equivalent_states _ _ _ _ _ Hif Hsource_equiv)
    as [sLift [Hif_lifted Hstateeq]].
  destruct sLift as [qsLift Mlift].
  exists (qsLift,Mlift); split.
  - eapply ms_step with (s2 := (qs2,Mq)).
    + exact Hq.
    + eapply ms_step with (s2 := (qsLift,Mlift)).
      * exact Hif_lifted.
      * eapply ms_refl; apply equivalent_refl.
  - unfold equivalent_states; simpl.
    split.
    + eapply Hunfold_trans; [exact (proj1 Hstateeq)|exact Htarget].
    + exact (proj2 Hstateeq).
Qed.

Lemma tau_if0_first_swap_unfolded_source : forall
  (qs : quantum_state) (M Mbase : session) (p q : participant)
  (e : expression) (P1 P0 : process) (Mmid : session)
  (qs2 : quantum_state) (Mend : session) (r : R),
  p <> q ->
  unfoldM M Mbase ->
  Mbase p = Some (p_ite e P1 P0) ->
  evaluate_expression e = Some (Bool false) ->
  unfoldM (insert Mbase p P0) Mmid ->
  step (qs,Mmid) (Tau q) (qs2,Mend) r ->
  exists s'',
    multistep (qs,M) (Tau q :: Tau p :: nil) s'' (r * (1 * 1)) /\
    equivalent_states (qs2,Mend) s''.
Proof.
  intros qs M Mbase p q e P1 P0 Mmid qs2 Mend r Hneq Hsource
    Hlookup Heval Hmid Hsecond.
  destruct (@tau_if0_first_swap qs Mbase p e P1 P0 Mmid q qs2 Mend r
      Hneq Hlookup Heval Hmid Hsecond) as [sbase [Hbase Hbase_eq]].
  assert (Hstates : equivalent_states (qs,Mbase) (qs,M)).
  { unfold equivalent_states; simpl.
    split; [exact Hsource|].
    split; [apply equivalent_refl|reflexivity]. }
  destruct (multistep_equivalent_states _ _ _ _ _ Hbase Hstates)
    as [slift [Hlift Hlift_eq]].
  exists slift; split; [exact Hlift|].
  eapply equivalent_states_trans; eassumption.
Qed.

Lemma tau_if1_first_swap_unfolded_source : forall
  (qs : quantum_state) (M Mbase : session) (p q : participant)
  (e : expression) (P1 P0 : process) (Mmid : session)
  (qs2 : quantum_state) (Mend : session) (r : R),
  p <> q ->
  unfoldM M Mbase ->
  Mbase p = Some (p_ite e P1 P0) ->
  evaluate_expression e = Some (Bool true) ->
  unfoldM (insert Mbase p P1) Mmid ->
  step (qs,Mmid) (Tau q) (qs2,Mend) r ->
  exists s'',
    multistep (qs,M) (Tau q :: Tau p :: nil) s'' (r * (1 * 1)) /\
    equivalent_states (qs2,Mend) s''.
Proof.
  intros qs M Mbase p q e P1 P0 Mmid qs2 Mend r Hneq Hsource
    Hlookup Heval Hmid Hsecond.
  destruct (@tau_if1_first_swap qs Mbase p e P1 P0 Mmid q qs2 Mend r
      Hneq Hlookup Heval Hmid Hsecond) as [sbase [Hbase Hbase_eq]].
  assert (Hstates : equivalent_states (qs,Mbase) (qs,M)).
  { unfold equivalent_states; simpl.
    split; [exact Hsource|].
    split; [apply equivalent_refl|reflexivity]. }
  destruct (multistep_equivalent_states _ _ _ _ _ Hbase Hstates)
    as [slift [Hlift Hlift_eq]].
  exists slift; split; [exact Hlift|].
  eapply equivalent_states_trans; eassumption.
Qed.

Lemma tau_if0_second_swap : forall (qs : quantum_state) (M : session)
  (p q : participant) (qs1 : quantum_state) (M1 Msrc : session) (r : R)
  (e : expression) (P1 P0 : process),
  p <> q ->
  step (qs,M) (Tau p) (qs1,M1) r ->
  unfoldM M1 Msrc ->
  Msrc q = Some (p_ite e P1 P0) ->
  evaluate_expression e = Some (Bool false) ->
  exists s'',
    multistep (qs,M) (Tau q :: Tau p :: nil) s'' (1 * (r * 1))%R /\
    equivalent_states (qs1,insert Msrc q P0) s''.
Proof.
  intros qs M p q qs1 M1 Msrc r e P1 P0 Hneq Hfirst Hmid Hlookup Heval.
  destruct (@Hunfold_other_process M1 Msrc q (p_ite e P1 P0) Hmid Hlookup)
    as [Pmid [Hm1_lookup Hpre_mid]].
  destruct (@Htau_other_process qs M p qs1 M1 r q Pmid
      ltac:(congruence) Hfirst Hm1_lookup) as [Psrc [Hsrc_lookup Hpre_src]].
  assert (Hpre : precongP Psrc (p_ite e P1 P0)).
  { eapply gttT; eassumption. }
  set (Mif := insert M q (p_ite e P1 P0)).
  assert (Hsource : unfoldM M Mif).
  { unfold Mif; eapply Hmake_unfold; eassumption. }
  assert (Htarget : unfoldM (insert Mif q P0) (insert M q P0)).
  { unfold Mif; apply Hmake_target_unfold. }
  assert (Hifcore : step (qs,Mif) (Tau q) (qs,insert Mif q P0) 1%R).
  { eapply If_0.
    - unfold Mif; rewrite insert_eq; reflexivity.
    - exact Heval. }
  assert (Hif : step (qs,M) (Tau q) (qs,insert Mif q P0) 1%R).
  { eapply Congr with (M1' := Mif) (M2 := insert Mif q P0).
    - exact Hsource.
    - exact Hifcore. }
  assert (Hsource_equiv : equivalent_states
      (qs,insert M q P0) (qs,insert Mif q P0)).
  { unfold equivalent_states; simpl.
    split; [exact Htarget|].
    split; [apply equivalent_refl|reflexivity]. }
  destruct (@Htau_insert qs M q P0 p qs1 M1 r ltac:(congruence) Hfirst)
    as [Mrev [Hp Hrev_equiv]].
  destruct (step_equivalent_states _ _ _ _ _ Hp Hsource_equiv)
    as [sLift [Hp_lifted Hstateeq]].
  destruct sLift as [qsLift Mlift].
  assert (Hrev_unfold : unfoldM Mrev (insert Msrc q P0)).
  { eapply Hunfold_trans.
    - apply equivalent_unfoldM; exact Hrev_equiv.
    - apply Hinsert_unfold; exact Hmid. }
  exists (qsLift,Mlift); split.
  -
    eapply ms_step with (s2 := (qs,insert Mif q P0)).
    + exact Hif.
    + eapply ms_step with (s2 := (qsLift,Mlift)).
      * exact Hp_lifted.
      * eapply ms_refl; apply equivalent_refl.
  - eapply (equivalent_states_trans
      (qs1,insert Msrc q P0) (qs1,Mrev) (qsLift,Mlift)).
    + unfold equivalent_states; simpl.
      split; [exact Hrev_unfold|].
      split; [apply equivalent_refl|reflexivity].
    + exact Hstateeq.
Qed.

Lemma tau_if1_second_swap : forall (qs : quantum_state) (M : session)
  (p q : participant) (qs1 : quantum_state) (M1 Msrc : session) (r : R)
  (e : expression) (P1 P0 : process),
  p <> q ->
  step (qs,M) (Tau p) (qs1,M1) r ->
  unfoldM M1 Msrc ->
  Msrc q = Some (p_ite e P1 P0) ->
  evaluate_expression e = Some (Bool true) ->
  exists s'',
    multistep (qs,M) (Tau q :: Tau p :: nil) s'' (1 * (r * 1))%R /\
    equivalent_states (qs1,insert Msrc q P1) s''.
Proof.
  intros qs M p q qs1 M1 Msrc r e P1 P0 Hneq Hfirst Hmid Hlookup Heval.
  destruct (@Hunfold_other_process M1 Msrc q (p_ite e P1 P0) Hmid Hlookup)
    as [Pmid [Hm1_lookup Hpre_mid]].
  destruct (@Htau_other_process qs M p qs1 M1 r q Pmid
      ltac:(congruence) Hfirst Hm1_lookup) as [Psrc [Hsrc_lookup Hpre_src]].
  assert (Hpre : precongP Psrc (p_ite e P1 P0)).
  { eapply gttT; eassumption. }
  set (Mif := insert M q (p_ite e P1 P0)).
  assert (Hsource : unfoldM M Mif).
  { unfold Mif; eapply Hmake_unfold; eassumption. }
  assert (Htarget : unfoldM (insert Mif q P1) (insert M q P1)).
  { unfold Mif; apply Hmake_target_unfold. }
  assert (Hifcore : step (qs,Mif) (Tau q) (qs,insert Mif q P1) 1%R).
  { eapply If_1.
    - unfold Mif; rewrite insert_eq; reflexivity.
    - exact Heval. }
  assert (Hif : step (qs,M) (Tau q) (qs,insert Mif q P1) 1%R).
  { eapply Congr with (M1' := Mif) (M2 := insert Mif q P1).
    - exact Hsource.
    - exact Hifcore. }
  assert (Hsource_equiv : equivalent_states
      (qs,insert M q P1) (qs,insert Mif q P1)).
  { unfold equivalent_states; simpl.
    split; [exact Htarget|].
    split; [apply equivalent_refl|reflexivity]. }
  destruct (@Htau_insert qs M q P1 p qs1 M1 r ltac:(congruence) Hfirst)
    as [Mrev [Hp Hrev_equiv]].
  destruct (step_equivalent_states _ _ _ _ _ Hp Hsource_equiv)
    as [sLift [Hp_lifted Hstateeq]].
  destruct sLift as [qsLift Mlift].
  assert (Hrev_unfold : unfoldM Mrev (insert Msrc q P1)).
  { eapply Hunfold_trans.
    - apply equivalent_unfoldM; exact Hrev_equiv.
    - apply Hinsert_unfold; exact Hmid. }
  exists (qsLift,Mlift); split.
  - eapply ms_step with (s2 := (qs,insert Mif q P1)).
    + exact Hif.
    + eapply ms_step with (s2 := (qsLift,Mlift)).
      * exact Hp_lifted.
      * eapply ms_refl; apply equivalent_refl.
  - eapply (equivalent_states_trans
      (qs1,insert Msrc q P1) (qs1,Mrev) (qsLift,Mlift)).
    + unfold equivalent_states; simpl.
      split; [exact Hrev_unfold|].
      split; [apply equivalent_refl|reflexivity].
    + exact Hstateeq.
Qed.

Lemma tau_if0_second_swap_unfolded_source : forall
  (qs : quantum_state) (M Mbase : session) (p q : participant)
  (qs1 : quantum_state) (Mcore Msrc : session) (r : R)
  (e : expression) (P1 P0 : process),
  p <> q ->
  unfoldM M Mbase ->
  step (qs,Mbase) (Tau p) (qs1,Mcore) r ->
  unfoldM Mcore Msrc ->
  Msrc q = Some (p_ite e P1 P0) ->
  evaluate_expression e = Some (Bool false) ->
  exists s'',
    multistep (qs,M) (Tau q :: Tau p :: nil) s'' (1 * (r * 1))%R /\
    equivalent_states (qs1,insert Msrc q P0) s''.
Proof.
  intros qs M Mbase p q qs1 Mcore Msrc r e P1 P0 Hneq Hsource
    Hfirst Hmid Hlookup Heval.
  destruct (@tau_if0_second_swap qs Mbase p q qs1 Mcore Msrc r e P1 P0
      Hneq Hfirst Hmid Hlookup Heval) as [sbase [Hbase Hbase_eq]].
  assert (Hstates : equivalent_states (qs,Mbase) (qs,M)).
  { unfold equivalent_states; simpl.
    split; [exact Hsource|].
    split; [apply equivalent_refl|reflexivity]. }
  destruct (multistep_equivalent_states _ _ _ _ _ Hbase Hstates)
    as [slift [Hlift Hlift_eq]].
  exists slift; split; [exact Hlift|].
  eapply equivalent_states_trans; eassumption.
Qed.

Lemma tau_if1_second_swap_unfolded_source : forall
  (qs : quantum_state) (M Mbase : session) (p q : participant)
  (qs1 : quantum_state) (Mcore Msrc : session) (r : R)
  (e : expression) (P1 P0 : process),
  p <> q ->
  unfoldM M Mbase ->
  step (qs,Mbase) (Tau p) (qs1,Mcore) r ->
  unfoldM Mcore Msrc ->
  Msrc q = Some (p_ite e P1 P0) ->
  evaluate_expression e = Some (Bool true) ->
  exists s'',
    multistep (qs,M) (Tau q :: Tau p :: nil) s'' (1 * (r * 1))%R /\
    equivalent_states (qs1,insert Msrc q P1) s''.
Proof.
  intros qs M Mbase p q qs1 Mcore Msrc r e P1 P0 Hneq Hsource
    Hfirst Hmid Hlookup Heval.
  destruct (@tau_if1_second_swap qs Mbase p q qs1 Mcore Msrc r e P1 P0
      Hneq Hfirst Hmid Hlookup Heval) as [sbase [Hbase Hbase_eq]].
  assert (Hstates : equivalent_states (qs,Mbase) (qs,M)).
  { unfold equivalent_states; simpl.
    split; [exact Hsource|].
    split; [apply equivalent_refl|reflexivity]. }
  destruct (multistep_equivalent_states _ _ _ _ _ Hbase Hstates)
    as [slift [Hlift Hlift_eq]].
  exists slift; split; [exact Hlift|].
  eapply equivalent_states_trans; eassumption.
Qed.

(* When either core action is a conditional, the state is unchanged and the
   existing framing lemmas give the swapped execution directly. *)
Lemma tau_if0_first_core_swap : forall
  (qs : quantum_state) (M Mbase : session) (p q : participant)
  (e : expression) (P1 P0 : process) (Mbase2 : session)
  (qs2 : quantum_state) (Mcore : session) (r2 : R),
  p <> q -> unfoldM M Mbase ->
  Mbase p = Some (p_ite e P1 P0) ->
  evaluate_expression e = Some (Bool false) ->
  unfoldM (insert Mbase p P0) Mbase2 ->
  tau_core qs Mbase2 q qs2 Mcore r2 ->
  exists s'',
    multistep (qs,M) (Tau q :: Tau p :: nil) s'' (r2 * (1 * 1))%R /\
    equivalent_states (qs2,Mcore) s''.
Proof.
  intros qs M Mbase p q e P1 P0 Mbase2 qs2 Mcore r2
    Hneq Hsource Hproc Heval Hmid Hsecond.
  eapply tau_if0_first_swap_unfolded_source; eauto using tau_core_to_step.
Qed.

Lemma tau_if1_first_core_swap : forall
  (qs : quantum_state) (M Mbase : session) (p q : participant)
  (e : expression) (P1 P0 : process) (Mbase2 : session)
  (qs2 : quantum_state) (Mcore : session) (r2 : R),
  p <> q -> unfoldM M Mbase ->
  Mbase p = Some (p_ite e P1 P0) ->
  evaluate_expression e = Some (Bool true) ->
  unfoldM (insert Mbase p P1) Mbase2 ->
  tau_core qs Mbase2 q qs2 Mcore r2 ->
  exists s'',
    multistep (qs,M) (Tau q :: Tau p :: nil) s'' (r2 * (1 * 1))%R /\
    equivalent_states (qs2,Mcore) s''.
Proof.
  intros qs M Mbase p q e P1 P0 Mbase2 qs2 Mcore r2
    Hneq Hsource Hproc Heval Hmid Hsecond.
  eapply tau_if1_first_swap_unfolded_source; eauto using tau_core_to_step.
Qed.

Lemma tau_if0_second_core_swap : forall
  (qs : quantum_state) (M Mbase : session) (p q : participant)
  (qs1 : quantum_state) (Mfirst Mbase2 : session) (r1 : R)
  (e : expression) (P1 P0 : process),
  p <> q -> unfoldM M Mbase ->
  step (qs,Mbase) (Tau p) (qs1,Mfirst) r1 ->
  unfoldM Mfirst Mbase2 ->
  Mbase2 q = Some (p_ite e P1 P0) ->
  evaluate_expression e = Some (Bool false) ->
  exists s'',
    multistep (qs,M) (Tau q :: Tau p :: nil) s'' (1 * (r1 * 1))%R /\
    equivalent_states (qs1,insert Mbase2 q P0) s''.
Proof.
  intros qs M Mbase p q qs1 Mfirst Mbase2 r1 e P1 P0
    Hneq Hsource Hfirst Hmid Hproc Heval.
  eapply tau_if0_second_swap_unfolded_source; eauto.
Qed.

Lemma tau_if1_second_core_swap : forall
  (qs : quantum_state) (M Mbase : session) (p q : participant)
  (qs1 : quantum_state) (Mfirst Mbase2 : session) (r1 : R)
  (e : expression) (P1 P0 : process),
  p <> q -> unfoldM M Mbase ->
  step (qs,Mbase) (Tau p) (qs1,Mfirst) r1 ->
  unfoldM Mfirst Mbase2 ->
  Mbase2 q = Some (p_ite e P1 P0) ->
  evaluate_expression e = Some (Bool true) ->
  exists s'',
    multistep (qs,M) (Tau q :: Tau p :: nil) s'' (1 * (r1 * 1))%R /\
    equivalent_states (qs1,insert Mbase2 q P1) s''.
Proof.
  intros qs M Mbase p q qs1 Mfirst Mbase2 r1 e P1 P0
    Hneq Hsource Hfirst Hmid Hproc Heval.
  eapply tau_if1_second_swap_unfolded_source; eauto.
Qed.

Lemma tau_unitary_unitary_core_swap : forall
  (qs : quantum_state) (M Mbase : session) (name name0 : string)
  (qs1 : quantum_state) (Mbase2 : session) (qs2 : quantum_state)
  (lq lq0 : list qubit_reference)
  (U : base_Unitary (length lq)) (U0 : base_Unitary (length lq0))
  (P P0 : process) (Hdim : length lq > 0) (Hdim0 : length lq0 > 0),
  name <> name0 ->
  unfoldM M Mbase ->
  Mbase (Pt name) = Some
    (p_unitary (length lq) U (map (fun z => Val (QVal z)) lq) P) ->
  apply_unitary (` (projT1 qs)) (proj2_sig (projT1 qs))
    (` (projT2 qs)) (proj2_sig (projT2 qs)) U lq eq_refl Hdim = Some qs1 ->
  NoDup lq ->
  Forall (fun q => exists n, (` (projT1 qs)) q = Some (Pt name,n)) lq ->
  unfoldM (insert Mbase (Pt name) P) Mbase2 ->
  Mbase2 (Pt name0) = Some
    (p_unitary (length lq0) U0 (map (fun z => Val (QVal z)) lq0) P0) ->
  apply_unitary (` (projT1 qs1)) (proj2_sig (projT1 qs1))
    (` (projT2 qs1)) (proj2_sig (projT2 qs1)) U0 lq0 eq_refl Hdim0 = Some qs2 ->
  NoDup lq0 ->
  Forall (fun q => exists n, (` (projT1 qs1)) q = Some (Pt name0,n)) lq0 ->
  exists s'',
    multistep (qs,M) (Tau (Pt name0) :: Tau (Pt name) :: nil) s''
      (1 * (1 * 1))%R /\
    equivalent_states (qs2,insert Mbase2 (Pt name0) P0) s''.
Proof.
  intros qs M Mbase name name0 qs1 Mbase2 qs2 lq lq0 U U0 P P0
    Hdim Hdim0 Hnames Hsource Hproc1 Happly1 Hnd1 Howners1 Hmid
    Hproc0 Happly0 Hnd0 Howners0.
  destruct (@Hlookup_frame Mbase (Pt name) P Mbase2 (Pt name0)
      (p_unitary (length lq0) U0 (map (fun z => Val (QVal z)) lq0) P0)
      ltac:(intro Heq; inversion Heq; subst; congruence) Hmid Hproc0)
    as [Psrc [Hsrc Hpre]].
  set (Mcommon := insert Mbase (Pt name0)
    (p_unitary (length lq0) U0 (map (fun z => Val (QVal z)) lq0) P0)).
  assert (Hcommon : unfoldM M Mcommon).
  {
    unfold Mcommon.
    eapply unfoldM_trans; [exact Hsource|].
    eapply Hmake_unfold; eassumption.
  }
  assert (Hsession : unfoldM
      (insert (insert Mcommon (Pt name) P) (Pt name0) P0)
      (insert Mbase2 (Pt name0) P0)).
  {
    eapply unfoldM_trans.
    - apply equivalent_unfoldM.
      unfold Mcommon.
      apply insert_insert_noop_2.
    - apply Hinsert_unfold; exact Hmid.
  }
  destruct (@swap_disjoint_unitary_steps name name0 Mcommon
      (insert Mbase2 (Pt name0) P0) P P0 qs qs1 qs2 lq lq0 U U0
      Hdim Hdim0 Happly1
      ltac:(unfold Mcommon; rewrite insert_neq by congruence; exact Hproc1)
      Hnd1 Howners1 Happly0
      ltac:(unfold Mcommon; rewrite insert_neq by congruence;
        rewrite insert_eq; reflexivity)
      Hnd0 Howners0 Hsession ltac:(congruence)
      ltac:(intro Heq; inversion Heq; congruence))
    as [scommon [Hreverse Hfinal]].
  assert (Hsource_states : equivalent_states (qs,Mcommon) (qs,M)).
  {
    unfold equivalent_states; simpl.
    split; [exact Hcommon|].
    split; [apply equivalent_refl|reflexivity].
  }
  destruct (multistep_equivalent_states _ _ _ _ _ Hreverse Hsource_states)
    as [sfinal [Hlift Hlift_eq]].
  exists sfinal; split; [exact Hlift|].
  eapply equivalent_states_trans; eassumption.
Qed.

Lemma tau_unitary_measure_core_swap : forall
  (a a0 : action) (s s' : state) (pi : R)
  (Hglobal : multistep s (a :: a0 :: nil) s' pi)
  (Hswap : should_swap_no_newq a a0 = true)
  (Hnn : no_newq_session (snd s))
  (qs : quantum_state) (M Mbase : session) (name name0 : string)
  (qs1 : quantum_state) (Mbase2 : session) (qs2 : quantum_state)
  (lq : list qubit_reference) (U : base_Unitary (length lq))
  (P P0 : process) (qref : qubit_reference) (index : fin) (result : bool)
  (prob : {x : R | (x > 0)%R})
  (Hdim : length lq > 0)
  (Hnames : name <> name0)
  (Hsource : unfoldM M Mbase)
  (Hproc1 : Mbase (Pt name) = Some
    (p_unitary (length lq) U (map (fun z => Val (QVal z)) lq) P))
  (Happly1 : apply_unitary (` (projT1 qs)) (proj2_sig (projT1 qs))
    (` (projT2 qs)) (proj2_sig (projT2 qs)) U lq eq_refl Hdim = Some qs1)
  (Hnd : NoDup lq)
  (Howners : Forall (fun q => exists n,
    (` (projT1 qs)) q = Some (Pt name,n)) lq)
  (Hmid : unfoldM (insert Mbase (Pt name) P) Mbase2)
  (Hlookup : (` (projT1 qs1)) qref = Some (Pt name0,index))
  (Hlen : 0 < length (elems qubit_reference (participant * fin)
    (` (projT1 qs1))))
  (Hnonzero : norm (proj index
    (length (elems qubit_reference (participant * fin) (` (projT1 qs1))))
    result × (` (projT2 qs1))) <> 0%R)
  (Hproc0 : Mbase2 (Pt name0) = Some (p_measure (Val (QVal qref)) P0))
  (Hmeasure : (prob,qs2) = measure_qubit_from_nonzero
    (` (projT1 qs1)) (proj2_sig (projT1 qs1))
    (` (projT2 qs1)) (proj2_sig (projT2 qs1))
    qref (Pt name0) index result Hlookup Hlen Hnonzero),
  exists s'',
    multistep (qs,M) (Tau (Pt name0) :: Tau (Pt name) :: nil) s''
      (proj1_sig prob * (1 * 1))%R /\
    equivalent_states (qs2,
      insert Mbase2 (Pt name0)
        (subst_expression_in_process 0 0 (Val (Bool result)) P0)) s''.
Proof.
  intros a a0 s s' pi Hglobal Hswap Hnn qs M Mbase name name0 qs1 Mbase2
    qs2 lq U P P0 qref index result prob Hdim Hnames Hsource Hproc1
    Happly1 Hnd Howners Hmid Hlookup Hlen Hnonzero Hproc0 Hmeasure.
  destruct (@Hlookup_frame Mbase (Pt name) P Mbase2 (Pt name0)
      (p_measure (Val (QVal qref)) P0)
      ltac:(intro Heq; inversion Heq; subst; congruence) Hmid Hproc0)
    as [Psrc [Hsrc Hpre]].
  set (Mcommon := insert Mbase (Pt name0) (p_measure (Val (QVal qref)) P0)).
  assert (Hcommon : unfoldM M Mcommon).
  {
    unfold Mcommon.
    eapply unfoldM_trans; [exact Hsource|].
    eapply Hmake_unfold; eassumption.
  }
  set (Pbody := subst_expression_in_process 0 0 (Val (Bool result)) P0).
  set (Mreverse := insert (insert Mcommon (Pt name0) Pbody) (Pt name) P).
  set (Mcore := insert Mbase2 (Pt name0) Pbody).
  assert (Hsession : unfoldM Mreverse Mcore).
  {
    unfold Mreverse, Mcore.
    eapply unfoldM_trans.
    - apply equivalent_unfoldM.
      eapply equivalent_trans.
      + unfold Mcommon.
        apply equivalent_sym, insert_insert_comm.
        intro Heq; inversion Heq; congruence.
      + unfold Mcommon.
        apply insert_insert_noop_2.
    - apply Hinsert_unfold; exact Hmid.
  }
  destruct qs as [[qm Hqm] [sv Hsv]].
  destruct qs1 as [[qm1 Hqm1] [sv1 Hsv1]].
  cbn in Happly1, Hlookup, Hlen, Hnonzero, Hmeasure.
  pose (qs := (@existT
      {x : finite_map qubit_reference (participant * fin) | quantum_map_wf x}
      (fun qm' => {q : state_vector
          (length (elems qubit_reference (participant * fin) (`qm'))) |
        state_vector_wf q})
      (exist _ qm Hqm) (exist _ sv Hsv))).
  pose (qs1 := (@existT
      {x : finite_map qubit_reference (participant * fin) | quantum_map_wf x}
      (fun qm' => {q : state_vector
          (length (elems qubit_reference (participant * fin) (`qm'))) |
        state_vector_wf q})
      (exist _ qm1 Hqm1) (exist _ sv1 Hsv1))).
  pose proof (Happly_map qm Hqm sv Hsv (length lq) U lq eq_refl
      Hdim qs1 Happly1) as Hmap.
  cbn in Hmap.
  subst qm1.
  assert (Hlookup0 : (` (projT1 qs)) qref = Some (Pt name0,index)).
  { exact Hlookup. }
  assert (Hlen0 : 0 < length (elems qubit_reference
      (participant * fin) (` (projT1 qs)))).
  { exact Hlen. }
  assert (Hnonzero_initial_map : norm (proj index
      (length (elems qubit_reference (participant * fin)
        (` (projT1 qs)))) result × (` (projT2 qs1))) <> 0%R).
  { exact Hnonzero. }
  pose proof (@Hunitary_measurement_branch_setup
      (` (projT1 qs)) (proj2_sig (projT1 qs))
      (` (projT2 qs)) (proj2_sig (projT2 qs)) lq U Hdim qs1 qref
      (Pt name0) (Pt name) index result Happly1 Howners Hlookup0
      ltac:(intro Heq; inversion Heq; subst; congruence)
      Hnonzero_initial_map) as
      [Hmap_after [lpn [Hget [Hidx [Hindex_disjoint
        [Hvec [Hnorm_before [Hnonzero_before Hprobability]]]]]]]].
  cbn in Hmap_after.
  set (measured_before := measure_qubit_from_nonzero
      (` (projT1 qs)) (proj2_sig (projT1 qs))
      (` (projT2 qs)) (proj2_sig (projT2 qs))
      qref (Pt name0) index result Hlookup0 Hlen0 Hnonzero_before).
  set (measured_after := measure_qubit_from_nonzero
      (` (projT1 qs1)) (proj2_sig (projT1 qs1))
      (` (projT2 qs1)) (proj2_sig (projT2 qs1))
      qref (Pt name0) index result Hlookup Hlen Hnonzero).
  destruct (@Hunitary_measurement_commute_state
      (` (projT1 qs)) (proj2_sig (projT1 qs))
      (` (projT2 qs)) (proj2_sig (projT2 qs)) lq U Hdim qs1 qref
      (Pt name0) (Pt name) index result Happly1 Hnd Howners Hlookup
      Hlen Hnonzero Hlookup0 Hlen0 Hnonzero_before
      ltac:(intro Heq; inversion Heq; subst; congruence))
    as [qsreordered [Happly_reordered
      [Hmap_reordered [Hvec_reordered Hprob_reordered]]]].
  assert (Hprob_eq : proj1_sig prob =
      proj1_sig (fst measured_before)).
  {
    pose proof (f_equal (fun x => proj1_sig (fst x)) Hmeasure) as Hp.
    change (proj1_sig prob = proj1_sig (fst measured_after)) in Hp.
    unfold measured_after in Hp.
    unfold measured_before, measured_after in Hprob_reordered.
    exact (eq_trans Hp (eq_sym Hprob_reordered)).
  }
  assert (Hstate_eq : qs2 = snd measured_after).
  { exact (f_equal (@snd _ _) Hmeasure). }
  assert (Howners_before : Forall
      (fun q => exists n, (` (projT1 (snd measured_before))) q =
        Some (Pt name,n)) lq).
  {
    rewrite Forall_forall in Howners.
    rewrite Forall_forall; intros qi Hqi.
    destruct (Howners qi Hqi) as [old_index Hqi_lookup].
    change (qm qi = Some (Pt name,old_index)) in Hqi_lookup.
    assert (Hqi_neq : qi <> qref).
    {
      intros Heq; apply
        (@Hqubits_distinct_if_owners_distinct qm qref qi
        (Pt name0) (Pt name) index old_index Hlookup0 Hqi_lookup
        ltac:(intro Howner; inversion Howner; congruence)).
      symmetry; exact Heq.
    }
    unfold measured_before.
    rewrite measure_qubit_nonzero_map.
    exists (shift_wire_index index old_index).
    unfold remove_and_reindex_qubit_map, reindex_quantum_map, FMap.delete.
    simpl.
    destruct (qr_dec qref qi) as [Heq|Hneq].
    - exfalso; apply Hqi_neq; symmetry; exact Heq.
    - rewrite Hqi_lookup; reflexivity.
  }
  assert (Hmeas_step : step (qs,Mcommon) (Tau (Pt name0))
      (snd measured_before, insert Mcommon (Pt name0) Pbody)
      (proj1_sig (fst measured_before))).
  {
    unfold Mcommon, Pbody.
    eapply Meas with (pi := fst measured_before)
      (q_state2 := snd measured_before).
    - rewrite insert_eq; reflexivity.
    - unfold measured_before; reflexivity.
  }
  assert (Hunitary_step : step
      (snd measured_before, insert Mcommon (Pt name0) Pbody)
      (Tau (Pt name))
      (qsreordered, insert (insert Mcommon (Pt name0) Pbody) (Pt name) P)
      1%R).
  {
    eapply Unitary with (dim := length lq) (U := U) (lq := lq)
      (Hlen := eq_refl) (Hdim := Hdim).
    - unfold Mcommon; repeat rewrite insert_neq by congruence; exact Hproc1.
    - exact Happly_reordered.
    - exact Hnd.
    - exact Howners_before.
  }
  assert (Hreverse : multistep (qs,Mcommon)
      (Tau (Pt name0) :: Tau (Pt name) :: nil)
      (qsreordered, Mreverse)
      (proj1_sig (fst measured_before) * (1 * 1))%R).
  {
    unfold Mreverse.
    eapply ms_step with
      (s2 := (snd measured_before, insert Mcommon (Pt name0) Pbody)).
    - exact Hmeas_step.
    - eapply ms_step with
        (s2 := (qsreordered,
          insert (insert Mcommon (Pt name0) Pbody) (Pt name) P)).
      + exact Hunitary_step.
      + replace (1 * 1)%R with 1%R by ring.
        eapply ms_refl; apply equivalent_refl.
  }
  assert (Hweight : (proj1_sig (fst measured_before) * (1 * 1))%R =
      (proj1_sig prob * (1 * 1))%R).
  { rewrite Hprob_eq; reflexivity. }
  assert (Hsource_states : equivalent_states (qs,Mcommon) (qs,M)).
  {
    unfold equivalent_states; simpl.
    split; [exact Hcommon|].
    split; [apply equivalent_refl|reflexivity].
  }
  destruct (multistep_equivalent_states _ _ _ _ _ Hreverse Hsource_states)
    as [sfinal [Hlift Hlift_eq]].
  exists sfinal; split.
  - rewrite <- Hweight; exact Hlift.
  - assert (Hfinal : equivalent_states (qs2,Mcore)
        (qsreordered,Mreverse)).
    {
      unfold equivalent_states; simpl.
      split; [exact Hsession|].
      unfold measured_after in Hstate_eq, Hmap_reordered, Hvec_reordered.
      split.
      - rewrite <- Hstate_eq in Hmap_reordered.
        rewrite Hmap_reordered; apply equivalent_refl.
      - rewrite <- Hstate_eq in Hvec_reordered.
        rewrite Hvec_reordered; reflexivity.
    }
    eapply equivalent_states_trans; eassumption.
Qed.

Lemma tau_measure_unitary_core_swap : forall
  (a a0 : action) (s s' : state) (pi : R)
  (Hglobal : multistep s (a :: a0 :: nil) s' pi)
  (Hswap : should_swap_no_newq a a0 = true)
  (Hnn : no_newq_session (snd s))
  (qs : quantum_state) (M Mbase : session) (name name0 : string)
  (qref : qubit_reference) (index : fin) (result : bool)
  (prob : {x : R | (x > 0)%R})
  (qs1 : quantum_state) (Mbase2 : session) (qs2 : quantum_state)
  (lq : list qubit_reference) (U : base_Unitary (length lq))
  (P P0 : process)
  (Hsource : unfoldM M Mbase)
  (Hproc1 : Mbase (Pt name) = Some
    (p_measure (Val (QVal qref)) P))
  (Hlookup : (` (projT1 qs)) qref = Some (Pt name,index))
  (Hlen : 0 < length (elems qubit_reference (participant * fin)
    (` (projT1 qs))))
  (Hnonzero : norm (proj index
    (length (elems qubit_reference (participant * fin) (` (projT1 qs))))
    result × (` (projT2 qs))) <> 0%R)
  (Hmeasure : (prob,qs1) = measure_qubit_from_nonzero
    (` (projT1 qs)) (proj2_sig (projT1 qs))
    (` (projT2 qs)) (proj2_sig (projT2 qs))
    qref (Pt name) index result Hlookup Hlen Hnonzero)
  (Hmid : unfoldM (insert Mbase (Pt name)
    (subst_expression_in_process 0 0 (Val (Bool result)) P)) Mbase2)
  (Hproc0 : Mbase2 (Pt name0) = Some
    (p_unitary (length lq) U (map (fun z => Val (QVal z)) lq) P0))
  (Hdim : length lq > 0)
  (Happly0 : apply_unitary (` (projT1 qs1)) (proj2_sig (projT1 qs1))
    (` (projT2 qs1)) (proj2_sig (projT2 qs1)) U lq eq_refl
    Hdim = Some qs2)
  (Hnd : NoDup lq)
  (Howners : Forall (fun q => exists n,
    (` (projT1 qs1)) q = Some (Pt name0,n)) lq)
  (Hnames : name <> name0),
  exists s'',
    multistep (qs,M) (Tau (Pt name0) :: Tau (Pt name) :: nil) s''
      (1 * (proj1_sig prob * (1 * 1)))%R /\
    equivalent_states (qs2,insert Mbase2 (Pt name0) P0) s''.
Proof.
  intros a a0 s s' pi Hglobal Hswap Hnn qs M Mbase name name0
    qref index result prob qs1 Mbase2 qs2 lq U P P0 Hsource Hproc1
    Hlookup Hlen Hnonzero Hmeasure Hmid Hproc0 Hdim Happly0 Hnd Howners Hnames.
  destruct (@Hlookup_frame Mbase (Pt name)
      (subst_expression_in_process 0 0 (Val (Bool result)) P)
      Mbase2 (Pt name0)
      (p_unitary (length lq) U (map (fun z => Val (QVal z)) lq) P0)
      ltac:(intro Heq; inversion Heq; subst; congruence) Hmid Hproc0)
    as [Psrc [Hsrc Hpre]].
  set (Pbody := subst_expression_in_process 0 0 (Val (Bool result)) P).
  set (Uproc := p_unitary (length lq) U
    (map (fun z => Val (QVal z)) lq) P0).
  set (Mcommon := insert Mbase (Pt name0) Uproc).
  assert (Hcommon : unfoldM M Mcommon).
  {
    unfold Mcommon.
    eapply unfoldM_trans; [exact Hsource|].
    eapply Hmake_unfold; eassumption.
  }
  set (Mreverse := insert (insert Mcommon (Pt name0) P0) (Pt name) Pbody).
  set (Mcore := insert Mbase2 (Pt name0) P0).
  assert (Hsession : unfoldM Mreverse Mcore).
  {
    unfold Mreverse, Mcore, Mcommon, Uproc, Pbody.
    eapply unfoldM_trans.
    - apply equivalent_unfoldM.
      eapply equivalent_trans.
      + apply equivalent_sym, insert_insert_comm.
        intro Heq; inversion Heq; congruence.
      + apply insert_insert_noop_2.
    - apply Hinsert_unfold; exact Hmid.
  }
  destruct qs as [[qm Hqm] [sv Hsv]].
  destruct qs1 as [[qm1 Hqm1] [sv1 Hsv1]].
  cbn in Happly0, Hlookup, Hmeasure, Howners.
  pose (qs := (@existT
      {x : finite_map qubit_reference (participant * fin) | quantum_map_wf x}
      (fun qm' => {q : state_vector
          (length (elems qubit_reference (participant * fin) (`qm'))) |
        state_vector_wf q})
      (exist _ qm Hqm) (exist _ sv Hsv))).
  pose (qs1 := (@existT
      {x : finite_map qubit_reference (participant * fin) | quantum_map_wf x}
      (fun qm' => {q : state_vector
          (length (elems qubit_reference (participant * fin) (`qm'))) |
        state_vector_wf q})
      (exist _ qm1 Hqm1) (exist _ sv1 Hsv1))).
  set (measured_before := measure_qubit_from_nonzero
      (` (projT1 qs)) (proj2_sig (projT1 qs))
      (` (projT2 qs)) (proj2_sig (projT2 qs))
      qref (Pt name) index result Hlookup Hlen Hnonzero).
  assert (Hstate_measure : qs1 = snd measured_before).
  {
    pose proof (f_equal (@snd _ _) Hmeasure) as H.
    change (qs1 = snd measured_before) in H.
    unfold measured_before.
    exact H.
  }
  assert (Hmap_measure : proj1_sig (projT1 (snd measured_before)) =
      remove_and_reindex_qubit_map qm qref index).
  { unfold measured_before; apply measure_qubit_nonzero_map. }
  assert (Hmap_qm1 : qm1 = remove_and_reindex_qubit_map qm qref index).
  {
    pose proof Hmap_measure as H.
    rewrite <- Hstate_measure in H.
    cbn in H.
    exact H.
  }
  assert (Howners_full : Forall
      (fun qi => exists old_index, qm qi = Some (Pt name0,old_index)) lq).
  {
    rewrite Forall_forall in Howners |- *; intros qi Hqi.
    destruct (Howners qi Hqi) as [new_index Hnew].
    change (proj1_sig (projT1 qs1) qi =
      Some (Pt name0,new_index)) in Hnew.
    assert (Hqi_neq : qi <> qref).
    {
      intro Heq.
      eapply (@Hmeasure_output_lookup_neq qm Hqm sv Hsv qref
        (Pt name) index result Hlookup Hlen Hnonzero qs1 qi
        (Pt name0) new_index Hstate_measure Hnew).
      symmetry; exact Heq.
    }
    assert (Hnew' : (` (projT1 (snd measured_before))) qi =
        Some (Pt name0,new_index)).
    { rewrite <- Hstate_measure; exact Hnew. }
    destruct (@Hremove_lookup_inv qm qi qref index (Pt name0)
        new_index Hqi_neq ltac:(rewrite <- Hmap_measure; exact Hnew'))
      as [old_index [Hold Hshift]].
    exists old_index; exact Hold.
  }
  assert (Hsize : length lq <= length (elems qubit_reference
      (participant * fin) qm)).
  {
    pose proof (@Happly_size qm1 Hqm1 sv1 Hsv1 (length lq) U lq
      eq_refl Hdim qs2 Happly0) as Hsize1.
    rewrite Hmap_qm1 in Hsize1.
    (* The measured map is one wire shorter than the original map. *)
    pose proof (@remove_and_reindex_qubit_map_length qm qref (Pt name)
      index Hlookup)
      as Hlen_removed.
    lia.
  }
  destruct (@Happly_exists qm Hqm sv Hsv (length lq) U lq eq_refl
      Hdim Hsize Hnd (ex_intro _ (Pt name0) Howners_full))
    as [qsfull Happly_full].
  destruct qsfull as [[qmfull Hqmfull] [svfull Hsvfull]].
  pose (qsfull_pkg := (@existT
      {x : finite_map qubit_reference (participant * fin) | quantum_map_wf x}
      (fun qm' => {q : state_vector
          (length (elems qubit_reference (participant * fin) (`qm'))) |
        state_vector_wf q})
      (exist _ qmfull Hqmfull) (exist _ svfull Hsvfull))).
  pose proof (@Happly_map qm Hqm sv Hsv (length lq) U lq eq_refl
      Hdim qsfull_pkg Happly_full) as Hmap_full_eq.
  cbn in Hmap_full_eq.
  subst qmfull.
  set (qsfull := qsfull_pkg).
  assert (Hmap_full : (` (projT1 qsfull)) qref = Some (Pt name,index)).
  {
    exact Hlookup.
  }
  assert (Hlen_full : 0 < length (elems qubit_reference
      (participant * fin) (` (projT1 qsfull)))).
  {
    exact Hlen.
  }
  destruct (@Hresult_vector qm Hqm sv Hsv (length lq) U lq eq_refl
      Hdim qsfull Happly_full)
    as [lpn [Hget [Hidx Hvec]]].
  assert (Hindex_disjoint : forall i, In i (map snd lpn) -> index <> i).
  {
    intros i Hi.
    apply in_map_iff in Hi as [[owner' idx] [Hidxi Hin_values]].
    simpl in Hidxi; subst i.
    destruct (Hget_value qm lq lpn owner' idx Hget Hin_values)
      as [qi [Hin_qi Hlookup_qi]].
    rewrite Forall_forall in Howners_full.
    destruct (Howners_full qi Hin_qi) as [idx' Howned].
    rewrite Hlookup_qi in Howned; inversion Howned; subst owner' idx'.
    exact (@Hindex_unique qm Hqm qref qi (Pt name) (Pt name0)
      index idx Hlookup Hlookup_qi ltac:(intro Heq; inversion Heq; congruence)).
  }
  assert (Hnorm_gate : norm (proj index
      (length (elems qubit_reference (participant * fin) qm)) result ×
      proj1_sig (projT2 qsfull)) =
    norm (proj index
      (length (elems qubit_reference (participant * fin) qm)) result × sv)).
  {
    rewrite Hvec; cbn.
    exact (@Hproj_base_norm (length (elems qubit_reference
      (participant * fin) qm)) (length lq) U (map snd lpn) Hidx
      index result sv Hsv Hindex_disjoint).
  }
  assert (Hnonzero_full : norm (proj index
      (length (elems qubit_reference (participant * fin) qm)) result ×
      proj1_sig (projT2 qsfull)) <> 0%R).
  {
    rewrite Hnorm_gate; exact Hnonzero.
  }
  assert (Hnonzero_full_qs : norm (proj index
      (length (elems qubit_reference (participant * fin)
        (` (projT1 qsfull)))) result × proj1_sig (projT2 qsfull)) <> 0%R).
  { exact Hnonzero_full. }
  set (measured_after := measure_qubit_from_nonzero
      (` (projT1 qsfull)) (proj2_sig (projT1 qsfull))
      (` (projT2 qsfull)) (proj2_sig (projT2 qsfull))
      qref (Pt name) index result Hmap_full Hlen_full Hnonzero_full).
  destruct (@Hunitary_measurement_commute_state
      qm Hqm sv Hsv lq U Hdim qsfull
      qref (Pt name) (Pt name0) index result Happly_full Hnd
      Howners_full Hmap_full Hlen_full Hnonzero_full_qs Hlookup Hlen Hnonzero
      ltac:(intro Heq; inversion Heq; congruence))
    as [qsreordered [Happly_reordered
      [Hmap_reordered [Hvec_reordered Hprob_reordered]]]].
  assert (Happly0_rewritten : apply_unitary
      (` (projT1 (snd measured_before)))
      (proj2_sig (projT1 (snd measured_before)))
      (` (projT2 (snd measured_before)))
      (proj2_sig (projT2 (snd measured_before))) U lq eq_refl
      Hdim = Some qs2).
  {
    rewrite <- Hstate_measure; exact Happly0.
  }
  assert (Hqs2 : qs2 = qsreordered).
  {
    unfold measured_before in Happly0_rewritten.
    change (apply_unitary
      (` (projT1 (measure_qubit_from_nonzero qm Hqm sv Hsv qref
        (Pt name) index result Hlookup Hlen Hnonzero).2))
      (proj2_sig (projT1 (measure_qubit_from_nonzero qm Hqm sv Hsv qref
        (Pt name) index result Hlookup Hlen Hnonzero).2))
      (` (projT2 (measure_qubit_from_nonzero qm Hqm sv Hsv qref
        (Pt name) index result Hlookup Hlen Hnonzero).2))
      (proj2_sig (projT2 (measure_qubit_from_nonzero qm Hqm sv Hsv qref
        (Pt name) index result Hlookup Hlen Hnonzero).2)) U lq eq_refl
      Hdim = Some qs2) in Happly0_rewritten.
    rewrite Happly_reordered in Happly0_rewritten.
    inversion Happly0_rewritten; reflexivity.
  }
  assert (Hprob_eq : proj1_sig prob = proj1_sig (fst measured_after)).
  {
    pose proof (f_equal (fun x => proj1_sig (fst x)) Hmeasure) as Hp.
    change (proj1_sig prob = proj1_sig (fst measured_before)) in Hp.
    unfold measured_before, measured_after in Hprob_reordered.
    exact (eq_trans Hp Hprob_reordered).
  }
  assert (Hunitary_step : step (qs,Mcommon) (Tau (Pt name0))
      (qsfull, insert Mcommon (Pt name0) P0) 1%R).
  {
    eapply Unitary with (dim := length lq) (U := U) (lq := lq)
      (Hlen := eq_refl) (Hdim := Hdim).
    - unfold Mcommon, Uproc; rewrite insert_eq; reflexivity.
    - exact Happly_full.
    - exact Hnd.
    - exact Howners_full.
  }
  assert (Hmeasure_step : step
      (qsfull,insert Mcommon (Pt name0) P0) (Tau (Pt name))
      (snd measured_after,
        insert (insert Mcommon (Pt name0) P0) (Pt name) Pbody)
      (proj1_sig (fst measured_after))).
  {
    unfold Mcommon, Uproc, Pbody.
    eapply Meas with (pi := fst measured_after)
      (q_state2 := snd measured_after).
    - repeat rewrite insert_neq by congruence; exact Hproc1.
    - unfold measured_after; reflexivity.
  }
  assert (Hreverse : multistep (qs,Mcommon)
      (Tau (Pt name0) :: Tau (Pt name) :: nil)
      (snd measured_after,Mreverse)
      (1 * (proj1_sig (fst measured_after) * (1 * 1)))%R).
  {
    unfold Mreverse.
    eapply ms_step with (s2 := (qsfull,insert Mcommon (Pt name0) P0)).
    - exact Hunitary_step.
    - eapply ms_step with
        (s2 := (snd measured_after,
          insert (insert Mcommon (Pt name0) P0) (Pt name) Pbody)).
      + exact Hmeasure_step.
      + replace (1 * 1)%R with 1%R by ring.
        eapply ms_refl; apply equivalent_refl.
  }
  assert (Hweight : (1 * (proj1_sig (fst measured_after) * (1 * 1)))%R =
      (1 * (proj1_sig prob * (1 * 1)))%R).
  { rewrite Hprob_eq; reflexivity. }
  assert (Hsource_states : equivalent_states (qs,Mcommon) (qs,M)).
  {
    unfold equivalent_states; simpl.
    split; [exact Hcommon|].
    split; [apply equivalent_refl|reflexivity].
  }
  destruct (multistep_equivalent_states _ _ _ _ _ Hreverse Hsource_states)
    as [sfinal [Hlift Hlift_eq]].
  exists sfinal; split.
  - rewrite <- Hweight; exact Hlift.
  - assert (Hfinal : equivalent_states
        (qs2,insert Mbase2 (Pt name0) P0) (snd measured_after,Mreverse)).
    {
      unfold equivalent_states; simpl.
      split; [exact Hsession|].
      rewrite Hqs2.
      unfold measured_after in Hmap_reordered, Hvec_reordered.
      split.
      - rewrite Hmap_reordered; apply equivalent_refl.
      - symmetry; exact Hvec_reordered.
    }
    eapply equivalent_states_trans; eassumption.
Qed.

Lemma tau_measure_measure_core_swap : forall
  (a a0 : action) (s s' : state) (pi : R)
  (Hglobal : multistep s (a :: a0 :: nil) s' pi)
  (Hswap : should_swap_no_newq a a0 = true)
  (Hnn : no_newq_session (snd s))
  (qs : quantum_state) (M Mbase : session) (name name0 : string)
  (qref qref0 : qubit_reference) (index index0 : fin)
  (result result0 : bool) (prob prob0 : {x : R | (x > 0)%R})
  (qs1 : quantum_state) (Mbase2 : session) (qs2 : quantum_state)
  (P P0 : process)
  (Hsource : unfoldM M Mbase)
  (Hproc1 : Mbase (Pt name) = Some
    (p_measure (Val (QVal qref)) P))
  (Hlookup1 : (` (projT1 qs)) qref = Some (Pt name,index))
  (Hlen1 : 0 < length (elems qubit_reference (participant * fin)
    (` (projT1 qs))))
  (Hnonzero1 : norm (proj index
    (length (elems qubit_reference (participant * fin) (` (projT1 qs))))
    result × (` (projT2 qs))) <> 0%R)
  (Hmeasure1 : (prob,qs1) = measure_qubit_from_nonzero
    (` (projT1 qs)) (proj2_sig (projT1 qs))
    (` (projT2 qs)) (proj2_sig (projT2 qs))
    qref (Pt name) index result Hlookup1 Hlen1 Hnonzero1)
  (Hmid : unfoldM (insert Mbase (Pt name)
    (subst_expression_in_process 0 0 (Val (Bool result)) P)) Mbase2)
  (Hlookup2 : (` (projT1 qs1)) qref0 = Some (Pt name0,index0))
  (Hlen2 : 0 < length (elems qubit_reference (participant * fin)
    (` (projT1 qs1))))
  (Hnonzero2 : norm (proj index0
    (length (elems qubit_reference (participant * fin)
      (` (projT1 qs1)))) result0 × (` (projT2 qs1))) <> 0%R)
  (Hproc0 : Mbase2 (Pt name0) = Some
    (p_measure (Val (QVal qref0)) P0))
  (Hmeasure2 : (prob0,qs2) = measure_qubit_from_nonzero
    (` (projT1 qs1)) (proj2_sig (projT1 qs1))
    (` (projT2 qs1)) (proj2_sig (projT2 qs1))
    qref0 (Pt name0) index0 result0 Hlookup2 Hlen2 Hnonzero2)
  (Hnames : name <> name0),
  exists rrev s'',
    multistep (qs,M) (Tau (Pt name0) :: Tau (Pt name) :: nil) s'' rrev /\
    equivalent_states (qs2,insert Mbase2 (Pt name0)
      (subst_expression_in_process 0 0 (Val (Bool result0)) P0)) s'' /\
    rrev = (proj1_sig prob0 * (proj1_sig prob * (1 * 1)))%R.
Proof.
  intros a a0 s s' pi Hglobal Hswap Hnn qs M Mbase name name0
    qref qref0 index index0 result result0 prob prob0 qs1 Mbase2 qs2
    P P0 Hsource Hproc1 Hlookup1 Hlen1 Hnonzero1 Hmeasure1 Hmid
    Hlookup2 Hlen2 Hnonzero2 Hproc0 Hmeasure2 Hnames.
  destruct qs as [[qm Hqm] [sv Hsv]].
  destruct qs1 as [[qm1 Hqm1] [sv1 Hsv1]].
  cbn in Hlookup1, Hlookup2, Hmeasure1, Hmeasure2, Hnonzero1,
    Hnonzero2.
  pose (qs := (@existT
      {x : finite_map qubit_reference (participant * fin) | quantum_map_wf x}
      (fun qm' => {q : state_vector
          (length (elems qubit_reference (participant * fin) (`qm'))) |
        state_vector_wf q})
      (exist _ qm Hqm) (exist _ sv Hsv))).
  pose (qs1 := (@existT
      {x : finite_map qubit_reference (participant * fin) | quantum_map_wf x}
      (fun qm' => {q : state_vector
          (length (elems qubit_reference (participant * fin) (`qm'))) |
        state_vector_wf q})
      (exist _ qm1 Hqm1) (exist _ sv1 Hsv1))).
  set (measured1 := measure_qubit_from_nonzero
    qm Hqm sv Hsv qref (Pt name) index result Hlookup1 Hlen1 Hnonzero1).
  set (measured2 := measure_qubit_from_nonzero
    qm1 Hqm1 sv1 Hsv1 qref0 (Pt name0) index0 result0 Hlookup2 Hlen2 Hnonzero2).
  assert (Hstate1 : qs1 = snd measured1).
  {
    pose proof (f_equal (@snd _ _) Hmeasure1) as H.
    change (qs1 = snd measured1) in H.
    unfold measured1; exact H.
  }
  assert (Hstate2 : qs2 = snd measured2).
  {
    pose proof (f_equal (@snd _ _) Hmeasure2) as H.
    change (qs2 = snd measured2) in H.
    unfold measured2; exact H.
  }
  assert (Hmap1 : qm1 = remove_and_reindex_qubit_map qm qref index).
  {
    pose proof (f_equal (fun st => proj1_sig (projT1 st)) Hstate1) as H.
    unfold measured1 in H.
    change (qm1 = proj1_sig (projT1
      (snd (measure_qubit_from_nonzero qm Hqm sv Hsv qref
        (Pt name) index result Hlookup1 Hlen1 Hnonzero1)))) in H.
    transitivity (proj1_sig (projT1
      (snd (measure_qubit_from_nonzero qm Hqm sv Hsv qref
        (Pt name) index result Hlookup1 Hlen1 Hnonzero1)))).
    - exact H.
    - apply measure_qubit_nonzero_map.
  }
  assert (Hqref_neq : qref0 <> qref).
  {
    intro Heq.
    eapply (@Hmeasure_output_lookup_neq qm Hqm sv Hsv qref
      (Pt name) index result Hlookup1 Hlen1 Hnonzero1
      qs1 qref0 (Pt name0) index0 Hstate1 Hlookup2).
    symmetry; exact Heq.
  }
  assert (Hlookup2_full_exists : exists old_index,
      qm qref0 = Some (Pt name0,old_index) /\
      index0 = shift_wire_index index old_index).
  {
    pose proof Hlookup2 as Hlookup2_removed.
    rewrite Hmap1 in Hlookup2_removed.
    eapply Hremove_lookup_inv; eauto.
  }
  destruct Hlookup2_full_exists as [index0_full
    [Hlookup2_full Hindex0_shift]].
  assert (Hindices_neq : index <> index0_full).
  {
    intro Heq.
    eapply (@Hindex_unique qm Hqm qref qref0 (Pt name) (Pt name0)
      index index0_full Hlookup1 Hlookup2_full).
    - intro Howner; inversion Howner; congruence.
    - exact Heq.
  }
  assert (Hlength_removed1 : length (elems qubit_reference
      (participant * fin) (remove_and_reindex_qubit_map qm qref index)) =
      Nat.pred (length (elems qubit_reference (participant * fin) qm))).
  {
    eapply remove_and_reindex_qubit_map_length; exact Hlookup1.
  }
  assert (Hlength_removed0 : length (elems qubit_reference
      (participant * fin) (remove_and_reindex_qubit_map qm qref0 index0_full)) =
      Nat.pred (length (elems qubit_reference (participant * fin) qm))).
  {
    eapply remove_and_reindex_qubit_map_length; exact Hlookup2_full.
  }
  assert (Hlen_removed1 : 0 < length (elems qubit_reference
      (participant * fin) (remove_and_reindex_qubit_map qm qref0 index0_full))).
  {
    rewrite Hlength_removed0.
    pose proof Hlen2 as Hlen_qm1.
    change (0 < length (elems qubit_reference (participant * fin) qm1))
      in Hlen_qm1.
    pose proof (f_equal (fun m => length (elems qubit_reference
      (participant * fin) m)) Hmap1) as Hlen_map1.
    rewrite Hlen_map1 in Hlen_qm1.
    rewrite Hlength_removed1 in Hlen_qm1.
    exact Hlen_qm1.
  }
  set (n := length (elems qubit_reference (participant * fin)
      (remove_and_reindex_qubit_map qm qref index))).
  assert (Hn_positive : 0 < n).
  {
    unfold n.
    rewrite Hlength_removed1.
    rewrite Hlength_removed0 in Hlen_removed1.
    exact Hlen_removed1.
  }
  assert (Hmap1_length : length (elems qubit_reference
      (participant * fin) qm1) = n).
  {
    unfold n.
    pose proof (f_equal (fun m => length (elems qubit_reference
      (participant * fin) m)) Hmap1) as H.
    exact H.
  }
  assert (Htotal1 : length (elems qubit_reference (participant * fin) qm) = S n).
  {
    unfold n.
    rewrite Hlength_removed1.
    symmetry; apply Nat.succ_pred_pos; exact Hlen1.
  }
  assert (Hlength_removed2 : length (elems qubit_reference
      (participant * fin) (remove_and_reindex_qubit_map qm1 qref0 index0)) =
      Nat.pred (length (elems qubit_reference (participant * fin) qm1))).
  {
    eapply remove_and_reindex_qubit_map_length; exact Hlookup2.
  }
  assert (Htotal2_map : length (elems qubit_reference (participant * fin) qm1) =
      S (length (elems qubit_reference
      (participant * fin) (remove_and_reindex_qubit_map qm1 qref0 index0)))).
  {
    rewrite Hlength_removed2.
    symmetry; apply Nat.succ_pred_pos; exact Hlen2.
  }
  assert (Htotal2 : n = S (length (elems qubit_reference
      (participant * fin) (remove_and_reindex_qubit_map qm1 qref0 index0)))).
  { rewrite <- Hmap1_length; exact Htotal2_map. }
  set (svfull := transport_state_vector Htotal1 sv).
  assert (Hsvfull : state_vector_wf svfull).
  { unfold svfull; apply transport_state_vector_wf; exact Hsv. }
  assert (Hvector1 : sv1 = normalize_removed_wire
      (contraction_apply (measurement_contraction n index result) svfull)).
  {
    pose proof (@measure_output_vector_contraction a a0 s s' pi
      Hglobal Hswap Hnn qm Hqm sv Hsv qref (Pt name) index result
      Hlookup1 Hlen1 Hnonzero1 Htotal1) as Hvector.
    pose proof (f_equal (fun st => proj1_sig (projT2 st)) Hstate1) as Hstate_vector.
    cbn in Hstate_vector.
    unfold measured1 in Hstate_vector.
    change (sv1 = proj1_sig (projT2 (snd
      (measure_qubit_from_nonzero qm Hqm sv Hsv qref (Pt name)
        index result Hlookup1 Hlen1 Hnonzero1)))) in Hstate_vector.
    rewrite Hstate_vector; exact Hvector.
  }
  assert (Hvector2 : proj1_sig (projT2 qs2) = normalize_removed_wire
      (contraction_apply
        (measurement_contraction
          (length (elems qubit_reference (participant * fin)
            (remove_and_reindex_qubit_map qm1 qref0 index0))) index0 result0)
        (transport_state_vector Htotal2_map sv1))).
  {
    pose proof (@measure_output_vector_contraction a a0 s s' pi
      Hglobal Hswap Hnn qm1 Hqm1 sv1 Hsv1 qref0 (Pt name0) index0 result0
      Hlookup2 Hlen2 Hnonzero2 Htotal2_map) as Hvector.
    pose proof (f_equal (fun st => proj1_sig (projT2 st)) Hstate2) as Hstate_vector.
    transitivity (proj1_sig (projT2 (snd measured2))).
    - exact Hstate_vector.
    - exact Hvector.
  }
  set (m := length (elems qubit_reference (participant * fin)
      (remove_and_reindex_qubit_map qm1 qref0 index0))).
  assert (Hindex_bound : index <= n).
  {
    pose proof (quantum_map_lookup_index_lt qm Hqm qref (Pt name)
      index Hlookup1) as H.
    rewrite Htotal1 in H; lia.
  }
  assert (Hindex0_full_bound : index0_full <= n).
  {
    pose proof (quantum_map_lookup_index_lt qm Hqm qref0 (Pt name0)
      index0_full Hlookup2_full) as H.
    rewrite Htotal1 in H; lia.
  }
  assert (Hindex0_bound : index0 < n).
  {
    pose proof (quantum_map_lookup_index_lt qm1 Hqm1 qref0 (Pt name0)
      index0 Hlookup2) as H.
    rewrite Hmap1_length in H; exact H.
  }
  assert (Hfirst_wf : @WF_Matrix (2 ^ n) 1
      (contraction_apply (measurement_contraction n index result) svfull)).
  {
    unfold contraction_apply; apply WF_mult.
    - unfold measurement_contraction; apply WF_mult.
      + apply remove_measured_wire_operator_wf; exact Hindex_bound.
      + apply WF_proj.
    - exact (proj1 Hsvfull).
  }
  assert (Hfirst_nonzero : contraction_apply
      (measurement_contraction n index result) svfull <> Zero).
  {
    apply (proj1 (@norm_nonzero_iff_nonzero (2 ^ n)
      (contraction_apply (measurement_contraction n index result) svfull)
      Hfirst_wf)).
    rewrite (@measurement_contraction_norm n index result svfull
      Hindex_bound (proj1 Hsvfull)).
    pose proof (@transport_state_vector_proj _ _ Htotal1 index result sv)
      as Hproject.
    unfold svfull.
    rewrite <- Hproject, transport_state_vector_norm.
    exact Hnonzero1.
  }
  assert (Hproject2_nonzero : norm (proj index0 n result0 ×
      normalize_removed_wire
        (contraction_apply (measurement_contraction n index result) svfull)) <> 0%R).
  {
    pose proof Hnonzero2 as H.
    rewrite Hmap1_length in H.
    rewrite Hvector1 in H.
    exact H.
  }
  assert (Hnormalized_wf : state_vector_wf
      (normalize_removed_wire
        (contraction_apply (measurement_contraction n index result) svfull))).
  {
    apply normalize_removed_wire_wf.
    - exact Hfirst_wf.
    - exact Hfirst_nonzero.
  }
  replace n with (S m) in * by (unfold m; symmetry; exact Htotal2).
  assert (Hindex0_rem_bound : index0 <=
      length (elems qubit_reference (participant * fin)
        (remove_and_reindex_qubit_map qm1 qref0 index0))).
  {
    pose proof Hindex0_bound as H; lia.
  }
  assert (Hsecond_nonzero : contraction_apply
      (measurement_contraction m index0 result0)
      (normalize_removed_wire
        (contraction_apply (measurement_contraction (S m) index result) svfull)) <> Zero).
  {
    assert (Hsecond_wf : @WF_Matrix
        (2 ^ m) 1
        (contraction_apply
          (measurement_contraction m index0 result0)
          (normalize_removed_wire
            (contraction_apply (measurement_contraction (S m) index result) svfull)))).
    {
      unfold contraction_apply; apply WF_mult.
      - unfold measurement_contraction; apply WF_mult.
        + apply remove_measured_wire_operator_wf; exact Hindex0_rem_bound.
        + apply WF_proj.
      - exact (proj1 Hnormalized_wf).
    }
    apply (proj1 (@norm_nonzero_iff_nonzero
      (2 ^ m)
      (contraction_apply
        (measurement_contraction m index0 result0)
        (normalize_removed_wire
          (contraction_apply (measurement_contraction (S m) index result) svfull)))
      Hsecond_wf)).
    rewrite (@measurement_contraction_norm m index0 result0
      (normalize_removed_wire
        (contraction_apply (measurement_contraction (S m) index result) svfull))
      Hindex0_rem_bound (proj1 Hnormalized_wf)).
    exact Hproject2_nonzero.
  }
  assert (Hvector2_compact : proj1_sig (projT2 qs2) = normalize_removed_wire
      (contraction_apply (measurement_contraction m index0 result0)
        (normalize_removed_wire
          (contraction_apply (measurement_contraction (S m) index result) svfull)))).
  {
    rewrite Hvector2.
    rewrite Hvector1.
    f_equal.
    f_equal.
    apply FunctionalCorrectnessHelpers.transport_state_vector_value.
  }
  assert (Hindex0_low : index < index0_full ->
      index0 = index0_full - 1).
  {
    intros Hlt.
    rewrite Hindex0_shift.
    unfold shift_wire_index.
    destruct (index <? index0_full) eqn:Htest.
    - apply Nat.ltb_lt in Htest; lia.
    - apply Nat.ltb_ge in Htest; lia.
  }
  assert (Hindex0_high : index0_full < index -> index0 = index0_full).
  {
    intros Hlt.
    rewrite Hindex0_shift.
    unfold shift_wire_index.
    destruct (index <? index0_full) eqn:Htest.
    - apply Nat.ltb_lt in Htest; lia.
    - reflexivity.
  }
  set (index_rev := shift_wire_index index0_full index).
  assert (Hindex_rev_low : index < index0_full -> index_rev = index).
  {
    intros Hlt; unfold index_rev, shift_wire_index.
    destruct (index0_full <? index) eqn:Htest.
    - apply Nat.ltb_lt in Htest; lia.
    - reflexivity.
  }
  assert (Hindex_rev_high : index0_full < index ->
      index_rev = index - 1).
  {
    intros Hlt; unfold index_rev, shift_wire_index.
    destruct (index0_full <? index) eqn:Htest.
    - apply Nat.ltb_lt in Htest; lia.
    - apply Nat.ltb_ge in Htest; lia.
  }
  assert (Hreverse_first_nonzero : contraction_apply
      (measurement_contraction (S m) index0_full result0) svfull <> Zero).
  {
    destruct (Nat.lt_trichotomy index index0_full) as [Hlow|[Heq|Hhigh]].
    - destruct (@normalized_measurement_pair_commute (S m) index index0_full
        result result0 svfull Hlow Hindex0_full_bound (proj1 Hsvfull)
        Hfirst_nonzero ltac:(replace (S m - 1) with m by lia;
          pose proof Hsecond_nonzero as H;
          rewrite Hindex0_low in H by exact Hlow; exact H))
        as [Hfirst_rev [Hsecond_rev Hvectors]].
      replace (S m - 1) with m in Hsecond_rev by lia.
      replace (S m - 1) with m in Hvectors by lia.
      exact Hfirst_rev.
    - exfalso; exact (Hindices_neq Heq).
    - destruct (@normalized_measurement_pair_commute_reverse (S m)
        index0_full index result0 result svfull Hhigh Hindex_bound
        (proj1 Hsvfull) Hfirst_nonzero
        ltac:(replace (S m - 1) with m by lia;
          pose proof Hsecond_nonzero as H;
          rewrite Hindex0_high in H by exact Hhigh; exact H))
        as [Hfirst_rev [Hsecond_rev Hvectors]].
      replace (S m - 1) with m in Hsecond_rev by lia.
      replace (S m - 1) with m in Hvectors by lia.
      exact Hfirst_rev.
  }
  assert (Hreverse_second_nonzero : contraction_apply
      (measurement_contraction m index_rev result)
      (normalize_removed_wire
        (contraction_apply (measurement_contraction (S m) index0_full result0)
          svfull)) <> Zero).
  {
    destruct (Nat.lt_trichotomy index index0_full) as [Hlow|[Heq|Hhigh]].
    - destruct (@normalized_measurement_pair_commute (S m) index index0_full
        result result0 svfull Hlow Hindex0_full_bound (proj1 Hsvfull)
        Hfirst_nonzero ltac:(replace (S m - 1) with m by lia;
          pose proof Hsecond_nonzero as H;
          rewrite Hindex0_low in H by exact Hlow; exact H))
        as [Hfirst_rev [Hsecond_rev Hvectors]].
      replace (S m - 1) with m in Hsecond_rev by lia.
      replace (S m - 1) with m in Hvectors by lia.
      rewrite Hindex_rev_low by exact Hlow; exact Hsecond_rev.
    - exfalso; exact (Hindices_neq Heq).
    - destruct (@normalized_measurement_pair_commute_reverse (S m)
        index0_full index result0 result svfull Hhigh Hindex_bound
        (proj1 Hsvfull) Hfirst_nonzero
        ltac:(replace (S m - 1) with m by lia;
          pose proof Hsecond_nonzero as H;
          rewrite Hindex0_high in H by exact Hhigh; exact H))
        as [Hfirst_rev [Hsecond_rev Hvectors]].
      replace (S m - 1) with m in Hsecond_rev by lia.
      replace (S m - 1) with m in Hvectors by lia.
      rewrite Hindex_rev_high by exact Hhigh; exact Hsecond_rev.
  }
  assert (Hpair_vector : normalize_removed_wire
      (contraction_apply (measurement_contraction m index0 result0)
        (normalize_removed_wire
          (contraction_apply (measurement_contraction (S m) index result)
            svfull))) =
    normalize_removed_wire
      (contraction_apply (measurement_contraction m index_rev result)
        (normalize_removed_wire
          (contraction_apply (measurement_contraction (S m) index0_full result0)
            svfull)))).
  {
    destruct (Nat.lt_trichotomy index index0_full) as [Hlow|[Heq|Hhigh]].
    - destruct (@normalized_measurement_pair_commute (S m) index index0_full
        result result0 svfull Hlow Hindex0_full_bound (proj1 Hsvfull)
        Hfirst_nonzero ltac:(replace (S m - 1) with m by lia;
          pose proof Hsecond_nonzero as H;
          rewrite Hindex0_low in H by exact Hlow; exact H))
        as [Hfirst_rev [Hsecond_rev Hvectors]].
      replace (S m - 1) with m in Hsecond_rev by lia.
      replace (S m - 1) with m in Hvectors by lia.
      rewrite Hindex0_low by exact Hlow.
      rewrite Hindex_rev_low by exact Hlow.
      exact Hvectors.
    - exfalso; exact (Hindices_neq Heq).
    - destruct (@normalized_measurement_pair_commute_reverse (S m)
        index0_full index result0 result svfull Hhigh Hindex_bound
        (proj1 Hsvfull) Hfirst_nonzero
        ltac:(replace (S m - 1) with m by lia;
          pose proof Hsecond_nonzero as H;
          rewrite Hindex0_high in H by exact Hhigh; exact H))
        as [Hfirst_rev [Hsecond_rev Hvectors]].
      replace (S m - 1) with m in Hsecond_rev by lia.
      replace (S m - 1) with m in Hvectors by lia.
      symmetry.
      rewrite Hindex0_high by exact Hhigh.
      rewrite Hindex_rev_high by exact Hhigh.
      exact Hvectors.
  }
  assert (Hprob1_value : proj1_sig prob =
      (norm (proj index (length (elems qubit_reference (participant * fin) qm))
        result × sv) ^ 2)%R).
  {
    pose proof (f_equal (fun x => proj1_sig (fst x)) Hmeasure1) as H.
    cbn in H.
    exact H.
  }
  assert (Hprob0_value : proj1_sig prob0 =
      (norm (proj index0 (length (elems qubit_reference (participant * fin) qm1))
        result0 × sv1) ^ 2)%R).
  {
    pose proof (f_equal (fun x => proj1_sig (fst x)) Hmeasure2) as H.
    cbn in H.
    exact H.
  }
  assert (Hn_eq : n = S m).
  {
    pose proof (f_equal (fun x => length (elems qubit_reference
      (participant * fin) x)) Hmap1) as H.
    unfold n, m in *.
    lia.
  }
  assert (Hreverse_first_full_wf : @WF_Matrix (2 ^ (S m)) 1
      (contraction_apply
        (measurement_contraction (S m) index0_full result0) svfull)).
  {
    unfold contraction_apply; apply WF_mult.
    - unfold measurement_contraction; apply WF_mult.
      + apply remove_measured_wire_operator_wf; exact Hindex0_full_bound.
      + apply WF_proj.
    - exact (proj1 Hsvfull).
  }
  assert (Hreverse_first_norm_nonzero : @norm (2 ^ (S m))
      (contraction_apply
        (measurement_contraction (S m) index0_full result0) svfull) <> 0%R).
  {
    exact (proj2 (@norm_nonzero_iff_nonzero (2 ^ (S m))
      (contraction_apply
        (measurement_contraction (S m) index0_full result0) svfull)
      Hreverse_first_full_wf) Hreverse_first_nonzero).
  }
  assert (Hreverse_project_nonzero : @norm
      (2 ^ (length (elems qubit_reference (participant * fin) qm)))
      (@Mmult (2 ^ (length (elems qubit_reference (participant * fin) qm)))
        (2 ^ (length (elems qubit_reference (participant * fin) qm))) 1
        (proj index0_full
          (length (elems qubit_reference (participant * fin) qm)) result0)
        sv) <> 0%R).
  {
    rewrite (@measurement_contraction_norm (S m) index0_full result0
      svfull Hindex0_full_bound (proj1 Hsvfull)) in
      Hreverse_first_norm_nonzero.
    pose proof (@transport_state_vector_proj _ _ Htotal1 index0_full
      result0 sv) as Hproject.
    pose proof (f_equal S Hn_eq) as Hdim_n.
    rewrite <- Hdim_n in Hreverse_first_norm_nonzero.
    unfold svfull in Hreverse_first_norm_nonzero.
    rewrite <- Hproject, transport_state_vector_norm in
      Hreverse_first_norm_nonzero.
    exact Hreverse_first_norm_nonzero.
  }
  set (measured_rev1 := measure_qubit_from_nonzero qm Hqm sv Hsv qref0
      (Pt name0) index0_full result0 Hlookup2_full Hlen1
      Hreverse_project_nonzero).
  set (qs_rev1 := snd measured_rev1).
  set (qm_rev1 := proj1_sig (projT1 qs_rev1)).
  set (Hqm_rev1 := proj2_sig (projT1 qs_rev1)).
  set (sv_rev1 := proj1_sig (projT2 qs_rev1)).
  set (Hsv_rev1 := proj2_sig (projT2 qs_rev1)).
  assert (Hmap_rev1 : qm_rev1 =
      remove_and_reindex_qubit_map qm qref0 index0_full).
  {
    unfold qm_rev1, qs_rev1, measured_rev1.
    apply measure_qubit_nonzero_map.
  }
  assert (Hlength_rev1 : length (elems qubit_reference (participant * fin)
      (remove_and_reindex_qubit_map qm qref0 index0_full)) =
      Nat.pred (length (elems qubit_reference (participant * fin) qm))).
  { eapply remove_and_reindex_qubit_map_length; exact Hlookup2_full. }
  assert (Hrevlen_eq : length (elems qubit_reference (participant * fin)
      (remove_and_reindex_qubit_map qm qref0 index0_full)) = n).
  {
    rewrite Hlength_rev1, <- Hlength_removed1.
    reflexivity.
  }
  assert (Htotal_rev1 : length (elems qubit_reference (participant * fin) qm) =
      S (length (elems qubit_reference (participant * fin)
        (remove_and_reindex_qubit_map qm qref0 index0_full)))).
  {
    rewrite Hlength_rev1.
    symmetry; apply Nat.succ_pred_pos; exact Hlen1.
  }
  assert (Htotal_rev1_compact : eq_trans Htotal_rev1
      (f_equal S Hrevlen_eq) = Htotal1).
  {
    apply proof_irrelevance.
  }
  assert (Htransport_rev1 : transport_state_vector
      (f_equal S Hrevlen_eq) (transport_state_vector Htotal_rev1 sv) =
      svfull).
  {
    rewrite tau_swap_transport_state_vector_compose.
    unfold svfull.
    rewrite Htotal_rev1_compact.
    reflexivity.
  }
  pose (Hrevlen_m := eq_trans Hrevlen_eq Hn_eq).
  pose (Htotal_common := eq_trans Htotal1 (f_equal S Hn_eq)).
  set (svfull_common := transport_state_vector
      (f_equal S Hn_eq) svfull).
  assert (Hsvfull_common : state_vector_wf svfull_common).
  {
    unfold svfull_common.
    unfold svfull.
    apply transport_state_vector_wf.
    apply transport_state_vector_wf; exact Hsv.
  }
  assert (Hsvfull_common_eq : svfull_common = svfull).
  {
    unfold svfull_common.
    apply FunctionalCorrectnessHelpers.transport_state_vector_value.
  }
  assert (Hvector1_common : sv1 = normalize_removed_wire
      (contraction_apply (measurement_contraction (S m) index result)
        svfull_common)).
  {
    rewrite Hvector1.
    rewrite <- Hsvfull_common_eq.
    reflexivity.
  }
  assert (Htransport_rev1_common : transport_state_vector
      (f_equal S Hrevlen_m) (transport_state_vector Htotal_rev1 sv) =
      svfull_common).
  {
    rewrite tau_swap_transport_state_vector_compose.
    unfold svfull_common, svfull.
    assert (Htotal_rev1_common : eq_trans Htotal_rev1
        (f_equal S Hrevlen_m) = Htotal_common).
    { apply proof_irrelevance. }
    rewrite Htotal_rev1_common.
    rewrite tau_swap_transport_state_vector_compose.
    reflexivity.
  }
  assert (Hvector_rev1_raw : sv_rev1 = normalize_removed_wire
      (contraction_apply
        (measurement_contraction
          (length (elems qubit_reference (participant * fin)
            (remove_and_reindex_qubit_map qm qref0 index0_full)))
          index0_full result0)
        (transport_state_vector Htotal_rev1 sv))).
  {
    pose proof (@measure_output_vector_contraction a a0 s s' pi
      Hglobal Hswap Hnn qm Hqm sv Hsv qref0 (Pt name0) index0_full result0
      Hlookup2_full Hlen1 Hreverse_project_nonzero Htotal_rev1) as Hvector.
    unfold sv_rev1, qs_rev1, measured_rev1 in *.
    exact Hvector.
  }
  assert (Hvector_rev1_common : transport_state_vector Hrevlen_m sv_rev1 =
      normalize_removed_wire
        (contraction_apply (measurement_contraction (S m) index0_full result0)
          svfull_common)).
  {
    pose proof (f_equal (transport_state_vector Hrevlen_m)
      Hvector_rev1_raw) as Hvector.
    rewrite tau_swap_normalize_transport in Hvector.
    rewrite tau_swap_contraction_transport in Hvector.
    rewrite Htransport_rev1_common in Hvector.
    exact Hvector.
  }
  assert (Hlookup_rev2 : qm_rev1 qref = Some (Pt name,index_rev)).
  {
    unfold qm_rev1, qs_rev1, measured_rev1, index_rev.
    rewrite measure_qubit_nonzero_map.
    apply Hremove_lookup.
    - intro Heq; apply Hqref_neq; symmetry; exact Heq.
    - exact Hlookup1.
  }
  assert (Hlen_rev2 : 0 < length (elems qubit_reference
      (participant * fin) qm_rev1)).
  {
    unfold qm_rev1, qs_rev1, measured_rev1.
    rewrite measure_qubit_nonzero_map, Hlength_rev1.
    rewrite Hlength_removed0 in Hlen_removed1.
    exact Hlen_removed1.
  }
  assert (Hrevlen_map : length (elems qubit_reference
      (participant * fin) qm_rev1) = S m).
  {
    unfold qm_rev1, qs_rev1, measured_rev1.
    rewrite measure_qubit_nonzero_map.
    exact Hrevlen_m.
  }
  assert (Hindex_rev_bound : index_rev <= m).
  {
    pose proof (quantum_map_lookup_index_lt qm_rev1 Hqm_rev1 qref
      (Pt name) index_rev Hlookup_rev2) as H.
    rewrite Hrevlen_map in H; lia.
  }
  assert (Hreverse_project2_nonzero : norm
      (proj index_rev
        (length (elems qubit_reference (participant * fin) qm_rev1))
        result × sv_rev1) <> 0%R).
  {
    assert (Hreverse_second_nonzero_common : contraction_apply
        (measurement_contraction m index_rev result)
        (normalize_removed_wire
          (contraction_apply
            (measurement_contraction (S m) index0_full result0)
            svfull_common)) <> Zero).
    {
      rewrite Hsvfull_common_eq.
      exact Hreverse_second_nonzero.
    }
    assert (Hreverse_first_wf_common : @WF_Matrix (2 ^ (S m)) 1
        (contraction_apply
          (measurement_contraction (S m) index0_full result0)
          svfull_common)).
    {
      unfold contraction_apply; apply WF_mult.
      - unfold measurement_contraction; apply WF_mult.
        + apply remove_measured_wire_operator_wf; exact Hindex0_full_bound.
        + apply WF_proj.
      - exact (proj1 Hsvfull_common).
    }
    assert (Hreverse_normalized_wf_common : state_vector_wf
        (normalize_removed_wire
          (contraction_apply
            (measurement_contraction (S m) index0_full result0)
            svfull_common))).
    {
      apply normalize_removed_wire_wf.
      - exact Hreverse_first_wf_common.
      - rewrite Hsvfull_common_eq; exact Hreverse_first_nonzero.
    }
    assert (Hreverse_second_wf_common : @WF_Matrix (2 ^ m) 1
        (contraction_apply (measurement_contraction m index_rev result)
          (normalize_removed_wire
            (contraction_apply
              (measurement_contraction (S m) index0_full result0)
              svfull_common)))).
    {
      unfold contraction_apply; apply WF_mult.
      - unfold measurement_contraction; apply WF_mult.
        + apply remove_measured_wire_operator_wf; exact Hindex_rev_bound.
        + apply WF_proj.
      - exact (proj1 Hreverse_normalized_wf_common).
    }
    pose proof (proj2 (@norm_nonzero_iff_nonzero (2 ^ m)
      (contraction_apply (measurement_contraction m index_rev result)
        (normalize_removed_wire
          (contraction_apply
            (measurement_contraction (S m) index0_full result0)
            svfull_common))) Hreverse_second_wf_common)
      Hreverse_second_nonzero_common) as Hnorm.
    rewrite (@measurement_contraction_norm m index_rev result
      (normalize_removed_wire
        (contraction_apply
          (measurement_contraction (S m) index0_full result0)
          svfull_common)) Hindex_rev_bound
      (proj1 Hreverse_normalized_wf_common)) in Hnorm.
    pose proof (@transport_state_vector_proj
      (length (elems qubit_reference (participant * fin)
        (remove_and_reindex_qubit_map qm qref0 index0_full)))
      (S m) Hrevlen_m index_rev result
      (proj1_sig (projT2 (snd measured_rev1)))) as Hproject_transport.
    unfold measured_rev1, sv_rev1, qs_rev1 in Hproject_transport.
    unfold sv_rev1, qs_rev1, measured_rev1 in Hvector_rev1_common.
    rewrite Hvector_rev1_common in Hproject_transport.
    rewrite Hmap_rev1.
    rewrite <- Hproject_transport in Hnorm.
    rewrite transport_state_vector_norm in Hnorm.
    unfold sv_rev1, qs_rev1, measured_rev1.
    exact Hnorm.
  }
  set (measured_rev2 := measure_qubit_from_nonzero
      qm_rev1 Hqm_rev1 sv_rev1 Hsv_rev1 qref (Pt name) index_rev result
      Hlookup_rev2 Hlen_rev2 Hreverse_project2_nonzero).
  set (qs_rev2 := snd measured_rev2).
  set (qm_rev2 := proj1_sig (projT1 qs_rev2)).
  set (sv_rev2 := proj1_sig (projT2 qs_rev2)).
  set (prob_rev1 := fst measured_rev1).
  set (prob_rev2 := fst measured_rev2).
  assert (Hmeasure_rev1 : (prob_rev1,qs_rev1) = measured_rev1).
  { unfold prob_rev1, qs_rev1; destruct measured_rev1; reflexivity. }
  assert (Hmeasure_rev2 : (prob_rev2,qs_rev2) = measured_rev2).
  { unfold prob_rev2, qs_rev2; destruct measured_rev2; reflexivity. }
  assert (Hmap_rev2 : qm_rev2 =
      remove_and_reindex_qubit_map qm_rev1 qref index_rev).
  {
    unfold qm_rev2, qs_rev2, measured_rev2.
    apply measure_qubit_nonzero_map.
  }
  assert (Hlength_rev2 : length (elems qubit_reference (participant * fin)
      (remove_and_reindex_qubit_map qm_rev1 qref index_rev)) =
      Nat.pred (length (elems qubit_reference (participant * fin) qm_rev1))).
  { eapply remove_and_reindex_qubit_map_length; exact Hlookup_rev2. }
  assert (Hrev2len_eq : length (elems qubit_reference (participant * fin)
      (remove_and_reindex_qubit_map qm_rev1 qref index_rev)) = m).
  {
    rewrite Hlength_rev2, Hrevlen_map; reflexivity.
  }
  assert (Htotal_rev2 : length (elems qubit_reference (participant * fin)
      qm_rev1) = S (length (elems qubit_reference (participant * fin)
      (remove_and_reindex_qubit_map qm_rev1 qref index_rev)))).
  {
    rewrite Hlength_rev2.
    symmetry; apply Nat.succ_pred_pos; exact Hlen_rev2.
  }
  assert (Hvector_rev2 : sv_rev2 = normalize_removed_wire
      (contraction_apply
        (measurement_contraction
          (length (elems qubit_reference (participant * fin)
            (remove_and_reindex_qubit_map qm_rev1 qref index_rev)))
          index_rev result)
        (transport_state_vector Htotal_rev2 sv_rev1))).
  {
    pose proof (@measure_output_vector_contraction a a0 s s' pi
      Hglobal Hswap Hnn qm_rev1 Hqm_rev1 sv_rev1 Hsv_rev1 qref
      (Pt name) index_rev result
      Hlookup_rev2 Hlen_rev2 Hreverse_project2_nonzero Htotal_rev2)
      as Hvector.
    unfold sv_rev2, qs_rev2, measured_rev2 in *.
    exact Hvector.
  }
  assert (Hmap2 : proj1_sig (projT1 qs2) =
      remove_and_reindex_qubit_map qm1 qref0 index0).
  {
    rewrite Hstate2.
    unfold measured2.
    apply measure_qubit_nonzero_map.
  }
  assert (Hmap_final_rev : qm_rev2 =
      remove_and_reindex_qubit_map
        (remove_and_reindex_qubit_map qm qref0 index0_full)
        qref index_rev).
  {
    rewrite Hmap_rev2, Hmap_rev1; reflexivity.
  }
  assert (Hlen_qs_rev2 : length (elems qubit_reference (participant * fin)
      qm_rev2) = m).
  {
    rewrite Hmap_rev2.
    exact Hrev2len_eq.
  }
  assert (Hrev2len_proof_irrel : Hrev2len_eq = Hlen_qs_rev2).
  { apply proof_irrelevance. }
  assert (Hvector_rev2_compact : sv_rev2 =
      normalize_removed_wire
        (contraction_apply (measurement_contraction m index_rev result)
          (normalize_removed_wire
            (contraction_apply
              (measurement_contraction (S m) index0_full result0)
              svfull_common)))).
  {
    assert (Htransport_rev2_compose :
        eq_trans Htotal_rev2 (f_equal S Hrev2len_eq) = Hrevlen_m).
    {
      unfold Hrevlen_m.
      apply proof_irrelevance.
    }
    pose proof (f_equal (transport_state_vector Hrev2len_eq)
      Hvector_rev2) as Hvector.
    rewrite tau_swap_normalize_transport in Hvector.
    rewrite tau_swap_contraction_transport in Hvector.
    rewrite tau_swap_transport_state_vector_compose in Hvector.
    rewrite Htransport_rev2_compose in Hvector.
    assert (Hvector_common : transport_state_vector Hrev2len_eq sv_rev2 =
        normalize_removed_wire
          (contraction_apply (measurement_contraction m index_rev result)
            (normalize_removed_wire
              (contraction_apply
                (measurement_contraction (S m) index0_full result0)
                svfull_common)))).
    {
      transitivity (normalize_removed_wire
        (contraction_apply (measurement_contraction m index_rev result)
          (transport_state_vector Hrevlen_m sv_rev1))).
      - exact Hvector.
      - pose proof (f_equal (fun v => normalize_removed_wire
          (contraction_apply (measurement_contraction m index_rev result) v))
          Hvector_rev1_common) as Htail.
        exact Htail.
    }
    rewrite Hrev2len_proof_irrel in Hvector_common.
    transitivity (transport_state_vector Hlen_qs_rev2 sv_rev2).
    - symmetry.
      unfold sv_rev2, qs_rev2, measured_rev2.
      unfold measure_qubit_from_nonzero.
      unfold qm_rev2, qs_rev2, measured_rev2 in Hlen_qs_rev2.
      unfold measure_qubit_from_nonzero in Hlen_qs_rev2.
      exact (@FunctionalCorrectnessHelpers.transport_state_vector_value
        _ m Hlen_qs_rev2 _).
    - exact Hvector_common.
  }
  assert (Hmap_final_commute : equivalent qm_rev2
      (proj1_sig (projT1 qs2))).
  {
    rewrite Hmap_final_rev, Hmap2, Hmap1.
    destruct (Nat.lt_trichotomy index index0_full)
      as [Hlow|[Heq|Hhigh]].
    - rewrite (Hindex0_low Hlow), (Hindex_rev_low Hlow).
      apply equivalent_sym; apply remove_two_qubits_commute.
      + intro Heq; apply Hqref_neq; symmetry; exact Heq.
      + exact Hlow.
    - exfalso; exact (Hindices_neq Heq).
    - rewrite (Hindex0_high Hhigh), (Hindex_rev_high Hhigh).
      apply remove_two_qubits_commute.
      + intro Heq'; apply Hqref_neq; exact Heq'.
      + exact Hhigh.
  }
  assert (Hvector_final : sv_rev2 = proj1_sig (projT2 qs2)).
  {
    transitivity
      (normalize_removed_wire
        (contraction_apply (measurement_contraction m index_rev result)
          (normalize_removed_wire
            (contraction_apply
              (measurement_contraction (S m) index0_full result0)
              svfull_common)))).
    - exact Hvector_rev2_compact.
    - rewrite Hvector2_compact.
      destruct (Nat.lt_trichotomy index index0_full)
        as [Hlow|[Heq|Hhigh]].
      + symmetry.
        pose proof Hpair_vector as Hpair.
        rewrite <- Hsvfull_common_eq in Hpair at 2.
        exact Hpair.
      + exfalso; exact (Hindices_neq Heq).
      + symmetry.
        pose proof Hpair_vector as Hpair.
        rewrite <- Hsvfull_common_eq in Hpair at 2.
        exact Hpair.
  }
  assert (Hsvfull_common_transport : svfull_common =
      transport_state_vector Htotal_common sv).
  {
    unfold svfull_common, svfull, Htotal_common.
    rewrite tau_swap_transport_state_vector_compose.
    reflexivity.
  }
  assert (Hfull_projector_norm : forall i b,
      @norm (2 ^ (S (S m)))
        (proj i (S (S m)) b × svfull_common) =
      @norm (2 ^ (length (elems qubit_reference (participant * fin) qm)))
        (proj i (length (elems qubit_reference (participant * fin) qm))
          b × sv)).
  {
    intros i b.
    rewrite Hsvfull_common_transport.
    pose proof (@transport_state_vector_proj
      (length (elems qubit_reference (participant * fin) qm))
      (S (S m)) Htotal_common i b sv) as Hproject.
    rewrite <- Hproject.
    rewrite transport_state_vector_norm.
    reflexivity.
  }
  assert (Hprob_rev1_value : proj1_sig prob_rev1 =
      (norm (proj index0_full
        (length (elems qubit_reference (participant * fin) qm)) result0
        × sv) ^ 2)%R).
  {
    unfold prob_rev1, measured_rev1.
    apply measure_qubit_probability_value.
  }
  assert (Hprob_rev2_value : proj1_sig prob_rev2 =
      (norm (proj index_rev
        (length (elems qubit_reference (participant * fin) qm_rev1)) result
        × sv_rev1) ^ 2)%R).
  {
    unfold prob_rev2, measured_rev2.
    apply measure_qubit_probability_value.
  }
  assert (Hprob1_common : proj1_sig prob =
      (norm (proj index (S (S m)) result × svfull_common) ^ 2)%R).
  {
    rewrite Hprob1_value.
    rewrite <- (Hfull_projector_norm index result).
    reflexivity.
  }
  assert (Hprob0_common : proj1_sig prob0 =
      (norm (proj index0 (S m) result0 ×
        normalize_removed_wire
          (contraction_apply (measurement_contraction (S m) index result)
            svfull_common)) ^ 2)%R).
  {
    rewrite Hprob0_value.
    rewrite Hmap1_length.
    rewrite Hvector1_common.
    reflexivity.
  }
  assert (Hprob_rev1_common : proj1_sig prob_rev1 =
      (norm (proj index0_full (S (S m)) result0 × svfull_common) ^ 2)%R).
  {
    rewrite Hprob_rev1_value.
    rewrite <- (Hfull_projector_norm index0_full result0).
    reflexivity.
  }
  assert (Hnorm_rev2_common :
      norm (proj index_rev (S m) result ×
        transport_state_vector Hrevlen_m sv_rev1) =
      norm (proj index_rev
        (length (elems qubit_reference (participant * fin) qm_rev1))
        result × sv_rev1)).
  {
    pose proof (@transport_state_vector_proj
      (length (elems qubit_reference (participant * fin) qm_rev1))
      (S m) Hrevlen_m index_rev result sv_rev1) as Hproject.
    transitivity (@norm (2 ^ (S m)) (transport_state_vector Hrevlen_m
      (proj index_rev
        (length (elems qubit_reference (participant * fin) qm_rev1))
        result × sv_rev1))).
    - exact (f_equal (@norm (2 ^ (S m))) (eq_sym Hproject)).
    rewrite transport_state_vector_norm.
    reflexivity.
  }
  assert (Hprob_rev2_common : proj1_sig prob_rev2 =
      (norm (proj index_rev (S m) result ×
        normalize_removed_wire
          (contraction_apply
            (measurement_contraction (S m) index0_full result0)
            svfull_common)) ^ 2)%R).
  {
    rewrite Hprob_rev2_value.
    rewrite <- Hnorm_rev2_common.
    rewrite Hvector_rev1_common.
    reflexivity.
  }
  assert (Hprob_product :
      (proj1_sig prob * proj1_sig prob0)%R =
      (proj1_sig prob_rev1 * proj1_sig prob_rev2)%R).
  {
    destruct (Nat.lt_trichotomy index index0_full)
      as [Hlow|[Heq|Hhigh]].
    - assert (Hfirst_common : contraction_apply
        (measurement_contraction (S m) index result) svfull_common <> Zero).
      {
        rewrite Hsvfull_common_eq; exact Hfirst_nonzero.
      }
      assert (Hsecond_common : contraction_apply
          (measurement_contraction m index0 result0)
          (normalize_removed_wire
            (contraction_apply
              (measurement_contraction (S m) index result)
              svfull_common)) <> Zero).
      {
        rewrite Hsvfull_common_eq; exact Hsecond_nonzero.
      }
      pose proof Hsecond_common as Hsecond_ordered.
      rewrite (Hindex0_low Hlow) in Hsecond_ordered.
      pose proof (@measurement_pair_probability_product_commute
        (S m) index index0_full result result0 svfull_common Hlow
        Hindex0_full_bound (proj1 Hsvfull_common) Hfirst_common
        ltac:(replace (S m - 1) with m by lia; exact Hsecond_ordered))
        as Hpairprob.
      pose proof Hprob0_common as Hprob0_ordered.
      rewrite (Hindex0_low Hlow) in Hprob0_ordered.
      pose proof Hprob_rev2_common as Hprob_rev2_ordered.
      rewrite (Hindex_rev_low Hlow) in Hprob_rev2_ordered.
      rewrite <- Hprob1_common, <- Hprob0_ordered,
        <- Hprob_rev1_common, <- Hprob_rev2_ordered in Hpairprob.
      exact Hpairprob.
    - exfalso; exact (Hindices_neq Heq).
    - assert (Hreverse_first_common : contraction_apply
        (measurement_contraction (S m) index0_full result0)
        svfull_common <> Zero).
      {
        rewrite Hsvfull_common_eq; exact Hreverse_first_nonzero.
      }
      assert (Hreverse_second_common : contraction_apply
          (measurement_contraction m index_rev result)
          (normalize_removed_wire
            (contraction_apply
              (measurement_contraction (S m) index0_full result0)
              svfull_common)) <> Zero).
      {
        rewrite Hsvfull_common_eq; exact Hreverse_second_nonzero.
      }
      pose proof Hreverse_second_common as Hreverse_second_ordered.
      rewrite (Hindex_rev_high Hhigh) in Hreverse_second_ordered.
      pose proof (@measurement_pair_probability_product_commute
        (S m) index0_full index result0 result svfull_common Hhigh
        Hindex_bound (proj1 Hsvfull_common) Hreverse_first_common
        ltac:(replace (S m - 1) with m by lia;
          exact Hreverse_second_ordered))
        as Hpairprob.
      pose proof Hprob0_common as Hprob0_ordered.
      rewrite (Hindex0_high Hhigh) in Hprob0_ordered.
      pose proof Hprob_rev2_common as Hprob_rev2_ordered.
      rewrite (Hindex_rev_high Hhigh) in Hprob_rev2_ordered.
      rewrite <- Hprob_rev1_common, <- Hprob_rev2_ordered,
        <- Hprob1_common, <- Hprob0_ordered in Hpairprob.
      symmetry; exact Hpairprob.
  }
  destruct (@Hlookup_frame Mbase (Pt name)
      (subst_expression_in_process 0 0 (Val (Bool result)) P)
      Mbase2 (Pt name0) (p_measure (Val (QVal qref0)) P0)
      ltac:(intro Heq; inversion Heq; subst; congruence) Hmid Hproc0)
    as [Psrc [Hsrc Hpre]].
  set (Pbody1 := subst_expression_in_process 0 0
      (Val (Bool result)) P).
  set (Pbody0 := subst_expression_in_process 0 0
      (Val (Bool result0)) P0).
  set (Mcommon := insert Mbase (Pt name0)
      (p_measure (Val (QVal qref0)) P0)).
  assert (Hcommon : unfoldM M Mcommon).
  {
    unfold Mcommon.
    eapply unfoldM_trans; [exact Hsource|].
    eapply Hmake_unfold; eassumption.
  }
  set (Mreverse := insert (insert Mcommon (Pt name0) Pbody0)
      (Pt name) Pbody1).
  set (Mcore := insert Mbase2 (Pt name0) Pbody0).
  assert (Hsession : unfoldM Mreverse Mcore).
  {
    unfold Mreverse, Mcore.
    eapply unfoldM_trans.
    - apply equivalent_unfoldM.
      eapply equivalent_trans.
      + unfold Mcommon.
        apply equivalent_sym, insert_insert_comm.
        intro Heq; inversion Heq; congruence.
      + unfold Mcommon.
        apply insert_insert_noop_2.
    - apply Hinsert_unfold; exact Hmid.
  }
  assert (Hstep_rev1 : step (qs,Mcommon) (Tau (Pt name0))
      (qs_rev1, insert Mcommon (Pt name0) Pbody0)
      (proj1_sig prob_rev1)).
  {
    unfold Mcommon, Pbody0.
    eapply Meas with (pi := prob_rev1) (q_state2 := qs_rev1).
    - rewrite insert_eq; reflexivity.
    - unfold measured_rev1; reflexivity.
  }
  assert (Hstep_rev2 : step
      (qs_rev1, insert Mcommon (Pt name0) Pbody0) (Tau (Pt name))
      (qs_rev2, insert (insert Mcommon (Pt name0) Pbody0)
        (Pt name) Pbody1)
      (proj1_sig prob_rev2)).
  {
    unfold Pbody1.
    eapply Meas with (pi := prob_rev2) (q_state2 := qs_rev2).
    - unfold Mcommon.
      transitivity (insert Mbase (Pt name0)
        (p_measure (Val (QVal qref0)) P0) (Pt name)).
      + apply (@insert_neq participant _ process
          (insert Mbase (Pt name0) (p_measure (Val (QVal qref0)) P0))
          (Pt name0) (Pt name) Pbody0).
        intro Heq; inversion Heq; congruence.
      + transitivity (Mbase (Pt name)).
        * apply (@insert_neq participant _ process Mbase (Pt name0)
            (Pt name) (p_measure (Val (QVal qref0)) P0)).
          intro Heq; inversion Heq; congruence.
        * exact Hproc1.
    - unfold measured_rev2; reflexivity.
  }
  assert (Hreverse : multistep (qs,Mcommon)
      (Tau (Pt name0) :: Tau (Pt name) :: nil)
      (qs_rev2,Mreverse)
      (proj1_sig prob_rev1 * (proj1_sig prob_rev2 * (1 * 1)))%R).
  {
    unfold Mreverse.
    eapply ms_step with
      (s2 := (qs_rev1, insert Mcommon (Pt name0) Pbody0)).
    - exact Hstep_rev1.
    - eapply ms_step with
        (s2 := (qs_rev2,
          insert (insert Mcommon (Pt name0) Pbody0) (Pt name) Pbody1)).
      + exact Hstep_rev2.
      + replace (1 * 1)%R with 1%R by ring.
        eapply ms_refl; apply equivalent_refl.
  }
  assert (Hweight :
      (proj1_sig prob_rev1 *
        (proj1_sig prob_rev2 * (1 * 1)))%R =
      (proj1_sig prob0 * (proj1_sig prob * (1 * 1)))%R).
  {
    replace (proj1_sig prob_rev1 *
      (proj1_sig prob_rev2 * (1 * 1)))%R with
      (proj1_sig prob_rev1 * proj1_sig prob_rev2)%R by ring.
    replace (proj1_sig prob0 *
      (proj1_sig prob * (1 * 1)))%R with
      (proj1_sig prob0 * proj1_sig prob)%R by ring.
    rewrite <- Hprob_product; ring.
  }
  assert (Hsource_states : equivalent_states (qs,Mcommon) (qs,M)).
  {
    unfold equivalent_states; simpl.
    split; [exact Hcommon|].
    split; [apply equivalent_refl|reflexivity].
  }
  destruct (multistep_equivalent_states _ _ _ _ _ Hreverse Hsource_states)
    as [sfinal [Hlift Hlift_eq]].
  exists (proj1_sig prob_rev1 *
      (proj1_sig prob_rev2 * (1 * 1)))%R, sfinal.
  split; [exact Hlift|].
  split.
  - assert (Hfinal : equivalent_states (qs2,Mcore)
        (qs_rev2,Mreverse)).
    {
      unfold equivalent_states; simpl.
      split; [exact Hsession|].
      split.
      - exact Hmap_final_commute.
      - exact Hvector_final.
    }
    eapply equivalent_states_trans; eassumption.
  - exact Hweight.
Qed.

Lemma multistep_tau_tau_should_swap_no_newq : forall
    (p q : participant) (s s' : state) (pi : R),
    multistep s (Tau p :: Tau q :: nil) s' pi ->
    should_swap_no_newq (Tau p) (Tau q) = true ->
    no_newq_session (snd s) ->
    exists s'',
      multistep s (Tau q :: Tau p :: nil) s'' pi /\
      equivalent_states s' s''.
Proof.
  intros p q s s' pi Hmulti Hswap Hnn.
  destruct s as [qs M]. destruct s' as [qsf Mf]. simpl in *.
  inversion Hmulti as [|s1 s2 s3 r1 r2 act rest Hstep1 Htail]; subst.
  simpl in Htail.
  inversion Htail as [|s21 s22 s23 r21 r22 act2 rest2 Hstep2 Htail2]; subst.
  simpl in Htail2.
  inversion Htail2 as [qst M2 M3 Hend|]; subst.
  destruct p as [name]; destruct q as [name0]; simpl in Hswap.
  assert (Hnames : name <> name0).
  { intro Heq; subst name0. apply (ltb_neq name name Hswap); reflexivity. }
  destruct s2 as [qs1 M1]; simpl in Hstep1, Hstep2.
  destruct (step_tau_decompose_core qs M (Pt name) qs1 M1 r1 Hstep1)
    as [Mbase1 [Mcore1 [Hsource1 [Hcore1 Hout1]]]].
  destruct (step_tau_decompose_core qs1 M1 (Pt name0) qsf M2 r21 Hstep2)
    as [Mbase2 [Mcore2 [Hsource2 [Hcore2 Hout2]]]].
  assert (Hmid : unfoldM Mcore1 Mbase2).
  { eapply unfoldM_trans; eassumption. }
  pose proof (Hunfold_no_newq _ _ Hsource1 Hnn) as Hnn_base1.
  pose proof (@Htau_preserves_no_newq qs M M (Pt name) qs1 M1 r1 Hnn
    (unfoldM_refl M) Hstep1) as Hnn_after1.
  pose proof (Hunfold_no_newq _ _ Hsource2 Hnn_after1) as Hnn_base2.
  assert (Horig_core : equivalent_states (qsf,Mf) (qsf,Mcore2)).
  {
    unfold equivalent_states; simpl.
    split.
    - eapply unfoldM_trans; [exact Hout2|].
      apply equivalent_unfoldM; exact Hend.
    - split; [apply equivalent_refl|reflexivity].
  }
  pose (core_endpoint := (qsf,Mcore2)).
  pose (qs1_step := qs1).
  pose proof (@tau_core_to_step qs Mbase1 (Pt name) qs1 Mcore1 r1 Hcore1)
    as Hstep1_core.
  dependent destruction Hcore1.
  - pose proof (Hnn_base1 (Pt name) (p_newq P) Hproc) as Hbad.
    simpl in Hbad; contradiction.
  - destruct (@tau_if0_first_core_swap qs M M0 (Pt name) (Pt name0)
      e P1 P0 Mbase2 qsf Mcore2 r21 ltac:(congruence) Hsource1 Hproc Heval
      Hmid Hcore2) as [srev [Hrev Heqrev]].
    exists srev; split.
    + replace (1 * (r21 * 1))%R with (r21 * (1 * 1))%R by ring.
      exact Hrev.
    + eapply equivalent_states_trans; [exact Horig_core|exact Heqrev].
  - destruct (@tau_if1_first_core_swap qs M M0 (Pt name) (Pt name0)
      e P1 P0 Mbase2 qsf Mcore2 r21 ltac:(congruence) Hsource1 Hproc Heval
      Hmid Hcore2) as [srev [Hrev Heqrev]].
    exists srev; split.
    + replace (1 * (r21 * 1))%R with (r21 * (1 * 1))%R by ring.
      exact Hrev.
    + eapply equivalent_states_trans; [exact Horig_core|exact Heqrev].
  - set (prob1 := measurement_probability_from_nonzero
        (length (elems qubit_reference (participant * fin) (` (projT1 qs))))
        (` (projT2 qs)) n result Hnonzero).
    set (measured1 := measure_qubit_from_nonzero
        (` (projT1 qs)) (proj2_sig (projT1 qs))
        (` (projT2 qs)) (proj2_sig (projT2 qs))
        q (Pt name) n result Hlookup Hlen Hnonzero).
    set (qs1_measured := snd measured1).
    assert (Hmeasure1 : (prob1,qs1_measured) =
        measure_qubit_from_nonzero
          (` (projT1 qs)) (proj2_sig (projT1 qs))
          (` (projT2 qs)) (proj2_sig (projT2 qs))
          q (Pt name) n result Hlookup Hlen Hnonzero).
    { unfold prob1, qs1_measured, measured1; reflexivity. }
    dependent destruction Hcore2.
    + match goal with
      | Hnew : ?Mnew ?actor0 = Some (p_newq ?Pnew) |- _ =>
          pose proof (Hnn_base2 actor0 (p_newq Pnew) Hnew) as Hbad;
          simpl in Hbad; contradiction
      end.
    + assert (Hswap_if : exists srev,
          multistep (qs,M) (Tau (Pt name0) :: Tau (Pt name) :: nil)
            srev (1 * (proj1_sig prob1 * 1))%R /\
          equivalent_states core_endpoint srev).
      {
        eapply tau_if0_second_core_swap
          with (p := Pt name) (q := Pt name0).
        all: solve [congruence | eauto using tau_core_to_step].
      }
      destruct Hswap_if as [srev [Hrev Heqrev]].
      exists srev; split.
      * replace (proj1_sig prob1 * (1 * 1))%R with
          (1 * (proj1_sig prob1 * 1))%R by ring.
        exact Hrev.
      * eapply equivalent_states_trans; [exact Horig_core|exact Heqrev].
    + assert (Hswap_if : exists srev,
          multistep (qs,M) (Tau (Pt name0) :: Tau (Pt name) :: nil)
            srev (1 * (proj1_sig prob1 * 1))%R /\
          equivalent_states core_endpoint srev).
      {
        eapply tau_if1_second_core_swap
          with (p := Pt name) (q := Pt name0).
        all: solve [congruence | eauto using tau_core_to_step].
      }
      destruct Hswap_if as [srev [Hrev Heqrev]].
      exists srev; split.
      * replace (proj1_sig prob1 * (1 * 1))%R with
          (1 * (proj1_sig prob1 * 1))%R by ring.
        exact Hrev.
      * eapply equivalent_states_trans; [exact Horig_core|exact Heqrev].
    + set (prob2 := measurement_probability_from_nonzero
          (length (elems qubit_reference (participant * fin)
            (` (projT1 qs1_step))))
          (` (projT2 qs1_step)) n0 result0 Hnonzero0).
      set (measured2 := measure_qubit_from_nonzero
          (` (projT1 qs1_step)) (proj2_sig (projT1 qs1_step))
          (` (projT2 qs1_step)) (proj2_sig (projT2 qs1_step))
          q0 (Pt name0) n0 result0 Hlookup0 Hlen0 Hnonzero0).
      set (qs2_measured := snd measured2).
      assert (Hmeasure2 : (prob2,qs2_measured) =
          measure_qubit_from_nonzero
            (` (projT1 qs1_step)) (proj2_sig (projT1 qs1_step))
            (` (projT2 qs1_step)) (proj2_sig (projT2 qs1_step))
            q0 (Pt name0) n0 result0 Hlookup0 Hlen0 Hnonzero0).
      { unfold prob2, qs2_measured, measured2; reflexivity. }
      assert (Hswap_mm :
          exists rrev srev,
            multistep (qs,M) (Tau (Pt name0) :: Tau (Pt name) :: nil)
              srev rrev /\
            equivalent_states core_endpoint srev /\
            rrev = (proj1_sig prob2 * (proj1_sig prob1 * (1 * 1)))%R).
      { eapply tau_measure_measure_core_swap; eauto. }
      destruct Hswap_mm as
        [rrev [srev [Hrev [Heqrev Hweight]]]].
      exists srev; split.
      * assert (Hrate : rrev =
            (proj1_sig prob1 * (proj1_sig prob2 * 1))%R).
        { rewrite Hweight; ring. }
        change (multistep (qs,M)
          (Tau (Pt name0) :: Tau (Pt name) :: nil) srev
          (proj1_sig prob1 * (proj1_sig prob2 * 1))%R).
        rewrite <- Hrate.
        exact Hrev.
      * eapply equivalent_states_trans; [exact Horig_core|exact Heqrev].
    + assert (Hswap_mu : exists srev,
            multistep (qs,M) (Tau (Pt name0) :: Tau (Pt name) :: nil)
              srev (1 * (proj1_sig prob1 * (1 * 1)))%R /\
            equivalent_states core_endpoint srev).
      { match goal with
        | Hdim_eq : length ?lq = ?dim |- _ => destruct Hdim_eq
        end.
        eapply tau_measure_unitary_core_swap; eauto.
        all: solve [congruence | eauto using tau_core_to_step]. }
      destruct Hswap_mu as [srev [Hrev Heqrev]].
      exists srev; split.
      * replace (proj1_sig prob1 * (1 * 1))%R with
          (1 * (proj1_sig prob1 * (1 * 1)))%R by ring.
        exact Hrev.
      * eapply equivalent_states_trans; [exact Horig_core|exact Heqrev].

  - destruct Hlen.
    dependent destruction Hcore2.
    + match goal with
      | Hnew : ?Mnew ?actor0 = Some (p_newq ?Pnew) |- _ =>
          pose proof (Hnn_base2 actor0 (p_newq Pnew) Hnew) as Hbad;
          simpl in Hbad; contradiction
      end.
    + assert (Hswap_if : exists srev,
          multistep (qs,M) (Tau (Pt name0) :: Tau (Pt name) :: nil)
            srev (1 * (1 * 1))%R /\
          equivalent_states core_endpoint srev).
      {
        eapply tau_if0_second_core_swap
          with (p := Pt name) (q := Pt name0).
        all: solve [congruence | eauto using tau_core_to_step].
      }
      destruct Hswap_if as [srev [Hrev Heqrev]].
      exists srev; split; [exact Hrev|].
      eapply equivalent_states_trans; [exact Horig_core|exact Heqrev].
    + assert (Hswap_if : exists srev,
          multistep (qs,M) (Tau (Pt name0) :: Tau (Pt name) :: nil)
            srev (1 * (1 * 1))%R /\
          equivalent_states core_endpoint srev).
      {
        eapply tau_if1_second_core_swap
          with (p := Pt name) (q := Pt name0).
        all: solve [congruence | eauto using tau_core_to_step].
      }
      destruct Hswap_if as [srev [Hrev Heqrev]].
      exists srev; split; [exact Hrev|].
      eapply equivalent_states_trans; [exact Horig_core|exact Heqrev].
    + set (prob2 := measurement_probability_from_nonzero
          (length (elems qubit_reference (participant * fin)
            (` (projT1 qs1_step))))
          (` (projT2 qs1_step)) n result Hnonzero).
      set (measured2 := measure_qubit_from_nonzero
          (` (projT1 qs1_step)) (proj2_sig (projT1 qs1_step))
          (` (projT2 qs1_step)) (proj2_sig (projT2 qs1_step))
          q (Pt name0) n result Hlookup Hlen Hnonzero).
      set (qs2_measured := snd measured2).
      assert (Hmeasure2 : (prob2,qs2_measured) =
          measure_qubit_from_nonzero
            (` (projT1 qs1_step)) (proj2_sig (projT1 qs1_step))
            (` (projT2 qs1_step)) (proj2_sig (projT2 qs1_step))
            q (Pt name0) n result Hlookup Hlen Hnonzero).
      { unfold prob2, qs2_measured, measured2; reflexivity. }
      assert (Hswap_um : exists srev,
            multistep (qs,M) (Tau (Pt name0) :: Tau (Pt name) :: nil)
              srev (proj1_sig prob2 * (1 * 1))%R /\
            equivalent_states core_endpoint srev).
      { eapply tau_unitary_measure_core_swap; eauto. }
      destruct Hswap_um as [srev [Hrev Heqrev]].
      exists srev; split.
      * change (multistep (qs,M)
          (Tau (Pt name0) :: Tau (Pt name) :: nil) srev
          (1 * (proj1_sig prob2 * 1))%R).
        replace (1 * (proj1_sig prob2 * 1))%R with
          (proj1_sig prob2 * (1 * 1))%R by ring.
        exact Hrev.
      * eapply equivalent_states_trans; [exact Horig_core|exact Heqrev].
    + match goal with
      | Hdim_eq : length ?lq = ?dim |- _ => destruct Hdim_eq
      end.
      assert (Hswap_uu : exists srev,
          multistep (qs,M) (Tau (Pt name0) :: Tau (Pt name) :: nil)
            srev (1 * (1 * 1))%R /\
          equivalent_states core_endpoint srev).
      { eapply tau_unitary_unitary_core_swap; eauto. }
      destruct Hswap_uu as [srev [Hrev Heqrev]].
      exists srev; split; [exact Hrev|].
      eapply equivalent_states_trans; [exact Horig_core|exact Heqrev].
Qed.

(* Main functional-correctness proofs. *)
Open Scope nat_scope.
Opaque pairwise_sorted insert equivalent.

Lemma finished_unfoldM_r: forall s s' : finite_map participant process,
unfoldM s s' -> finished s' -> finished s.
Proof.
  intros s s' Hunfold Hfinished p Q Hlookup.
  destruct (Hunfold p) as [[Hnone _]|[P [P' [Hsrc [Hdst Hpre]]]]].
  - rewrite Hlookup in Hnone; discriminate.
  - rewrite Hlookup in Hsrc; inversion Hsrc; subst P.
    destruct (Hfinished p P' Hdst) as [lz Hend].
    exists lz; eapply gttT; eassumption.
Qed.

Lemma multistep_should_swap:
forall (a a0 : action) (s s' : state) (pi : R),
multistep s (a::a0::nil) s' pi ->
should_swap a a0 = true ->
exists s'',
multistep s (a0::a::nil) s'' pi /\
equivalent_states s' s''.
Proof.
  intros a a0 s s' pi H Hswap.
  inversion H; subst; cleanup.
  inversion H6; subst; cleanup.
  inversion H8; subst; cleanup.
  destruct a, a0; simpl in *; repeat case_analysis; cleanup.
  - destruct (should_swap_tx_tau_facts (Pt name) (Pt name0) (Pt name1)
      l v Hswap) as [Hp Ha].
    destruct s as [qs0 M0]; destruct s2 as [qs1 M1]; simpl in *.
    destruct (tx_tau_swap qs0 M0 (Pt name) (Pt name0) l v qs1 M1
      (Pt name1) qstate s1 r1 r0 H3 H4 Hp Ha)
      as [qsrev [Mrev [Hreverse [Hunfold [Hmap Hvec]]]]].
    exists (qsrev,Mrev); split; [exact Hreverse|].
    unfold equivalent_states; simpl.
    split.
    + eapply unfoldM_trans; [exact Hunfold|].
      apply equivalent_unfoldM; exact H0.
    + split; assumption.
  - destruct (should_swap_tx_facts (Pt name) (Pt name0)
      (Pt name1) (Pt name2) l l0 v v0 Hswap)
      as [H12 [H14 [H32 [H34 Hpayload]]]].
    destruct s as [qs0 M0]; destruct s2 as [qs1 M1]; simpl in *.
    destruct (tx_tx_swap qs0 M0 (Pt name) (Pt name0) l v qs1 M1
      (Pt name1) (Pt name2) l0 v0 qstate s1 r1 r0
      H3 H4 H12 H14 H32 H34 Hpayload)
      as [qsrev [Mrev [Hreverse [Hunfold [Hmap Hvec]]]]].
    exists (qsrev,Mrev); split; [exact Hreverse|].
    unfold equivalent_states; simpl.
    split.
    + eapply unfoldM_trans; [exact Hunfold|].
      apply equivalent_unfoldM; exact H0.
    + split; assumption.
Qed.

Lemma multistep_should_swap_no_newq:
forall a a0 s s' pi,
multistep s (a::a0::nil) s' pi ->
should_swap_no_newq a a0 = true ->
no_newq_session (snd s) ->
exists s'',
multistep s (a0::a::nil) s'' pi /\
equivalent_states s' s''.
Proof.
  intros a a0 s s' pi H Hswap Hnn.
  destruct a as [actor|p q l v];
    destruct a0 as [actor0|p0 q0 l0 v0].
  - destruct actor as [name]; destruct actor0 as [name0].
    eapply multistep_tau_tau_should_swap_no_newq; eauto.
  - destruct actor as [name]; destruct p0 as [name0];
      destruct q0 as [name1]; simpl in Hswap; discriminate.
  - destruct p as [name]; destruct q as [name1];
      destruct actor0 as [name0].
    assert (Hshould : should_swap (Transmit (Pt name) (Pt name1) l v)
        (Tau (Pt name0)) = true).
    { unfold should_swap, should_swap_no_newq in *; exact Hswap. }
    eapply multistep_should_swap; eauto.
  - destruct p as [name]; destruct q as [name1];
      destruct p0 as [name0]; destruct q0 as [name2].
    unfold should_swap_no_newq in Hswap; simpl in Hswap.
    pose proof Hswap as Hparts.
    apply andb_true_iff in Hparts as [Hends Horder].
    apply andb_true_iff in Hends as [Hleft Hright].
    apply andb_true_iff in Hleft as [Hpr Hps].
    apply andb_true_iff in Hright as [Hqr Hqs].
    apply negb_true_iff in Hpr; apply String.eqb_neq in Hpr.
    apply negb_true_iff in Hps; apply String.eqb_neq in Hps.
    apply negb_true_iff in Hqr; apply String.eqb_neq in Hqr.
    apply negb_true_iff in Hqs; apply String.eqb_neq in Hqs.
    pose proof (two_transfers_payloads_disjoint (Pt name) (Pt name1) l v
      (Pt name0) (Pt name2) l0 v0 s s' pi H
      ltac:(congruence) ltac:(congruence)
      ltac:(congruence) ltac:(congruence)) as Hpayload.
    assert (Hshould : should_swap (Transmit (Pt name) (Pt name1) l v)
        (Transmit (Pt name0) (Pt name2) l0 v0) = true).
    {
      unfold should_swap; simpl.
      rewrite Hpayload; exact Hswap.
    }
    eapply multistep_should_swap; eauto.
Qed.

Lemma multistep_insert_into:
forall la a s s' pi,
multistep s (a::la) s' pi ->
exists s'',
multistep s (insert_into should_swap a la) s'' pi /\
equivalent_states s' s''.
Proof.
  induction la; simpl; intros.
  eexists; do 2 (split; eauto).
  apply unfoldM_refl.
  (split; eauto).
  apply equivalent_refl.

  case_analysis.
  2: {
    eexists; do 2 (split; eauto).
  apply unfoldM_refl.
  (split; eauto).
  apply equivalent_refl.
  }

  replace (a0 :: a :: la) with  ((a0 :: a :: nil) ++ la) in H by eauto.
  eapply multistep_app_rev in H.
  cleanup.
  apply multistep_should_swap in H; eauto; cleanup.
  eapply multistep_equivalent_states in H1; eauto; cleanup.
  eapply multistep_app in H1; eauto; simpl in *.
  inversion H1; cleanup.
  apply IHla in H9; eauto; cleanup.
  eexists; split.
  rewrite <- H6.
  econstructor; eauto.
  eapply equivalent_states_trans; eauto.
Qed.

Lemma multistep_partial_sort:
forall la s s' pi,
multistep s la s' pi ->
exists s'',
multistep s (partial_sort should_swap la) s'' pi /\
equivalent_states s' s''.
Proof.
  induction la; simpl; intros;
  inversion H; cleanup.
  eexists; do 2 (split; eauto).
  apply unfoldM_refl.
  (split; eauto).
  apply equivalent_refl.

  eapply IHla in H6; cleanup.
  edestruct (multistep_insert_into (partial_sort should_swap la)).
  econstructor; eauto.
  cleanup.
  eexists; split; [eauto|].
  eapply equivalent_states_trans; eauto.
Qed.

Lemma no_newq_recv_branch:
forall p lQ l Q,
no_newq (p_recv p lQ) ->
onth l lQ = Some Q ->
no_newq Q.
Proof.
  intros p lQ l Q Hrecv Honth.
  simpl in Hrecv.
  rewrite Hto_list_smap in Hrecv.
  apply (proj1 (Hfold_prop _)) in Hrecv.
  apply Forall_forall with (x := no_newq Q) in Hrecv.
  - apply Hrecv.
    apply in_map.
    eapply onth_to_list_In; exact Honth.
Qed.

Lemma no_newq_session_step:
forall a s s' pi,
step s a s' pi ->
no_newq_session (snd s) ->
no_newq_session (snd s').
Proof.
  fix IH 5.
  intros a s s' pi Hstep Hnn.
  destruct s as [qs M]; destruct s' as [qs' M']; simpl in *.
  destruct a.
  - eapply Htau_preserves_no_newq with (M0 := M) (Msrc := M).
    + exact Hnn.
    + apply unfoldM_refl.
    + exact Hstep.
  - dependent destruction Hstep; simpl in *; try discriminate.
    + pose proof (Hnn p (p_send q l e P) H) as Hsend.
      simpl in Hsend.
      pose proof (Hnn q (p_recv p lQ) H0) as Hrecv.
      pose proof (no_newq_recv_branch _ _ _ _ Hrecv H2) as Hcont.
      pose proof (Hsubst_expr_no_newq 0 0 (Val v) Q Hcont) as Hcont'.
      pose proof (Hinsert_no_newq M q Q' Hnn Hcont') as Hnn_recv.
      exact (Hinsert_no_newq (insert M q Q') p P Hnn_recv Hsend).
    + pose proof (Hnn p (p_send q l e P) H) as Hsend.
      simpl in Hsend.
      pose proof (Hnn q (p_recv p lQ) H0) as Hrecv.
      pose proof (no_newq_recv_branch _ _ _ _ Hrecv H2) as Hcont.
      pose proof (Hsubst_expr_no_newq 0 0 (Val (QVal v0)) Q Hcont) as Hcont'.
      pose proof (Hinsert_no_newq M q Q' Hnn Hcont') as Hnn_recv.
      exact (Hinsert_no_newq (insert M q Q') p P Hnn_recv Hsend).
    + pose proof (Hunfold_no_newq _ _ H Hnn) as Hnn_mid.
      exact (IH (Transmit p q l v) (qs, M1') (qs', M') r Hstep Hnn_mid).
Qed.

Lemma multistep_insert_into_no_newq:
forall la a s s' pi,
multistep s (a::la) s' pi ->
no_newq_session (snd s) ->
exists s'',
multistep s (insert_into should_swap_no_newq a la) s'' pi /\
equivalent_states s' s''.
Proof.
  induction la; simpl; intros.
  eexists; do 2 (split; eauto).
  apply unfoldM_refl.
  (split; eauto).
  apply equivalent_refl.

  case_analysis.
  2: {
    eexists; do 2 (split; eauto).
  apply unfoldM_refl.
  (split; eauto).
  apply equivalent_refl.
  }

  replace (a0 :: a :: la) with  ((a0 :: a :: nil) ++ la) in H by eauto.
  eapply multistep_app_rev in H.
  cleanup.
  apply multistep_should_swap_no_newq in H; eauto; cleanup.
  eapply multistep_equivalent_states in H1; eauto; cleanup.
  eapply multistep_app in H1; eauto; simpl in *.
  inversion H1; cleanup.
  apply IHla in H10; eauto; cleanup.
  eexists; split.
  rewrite <- H7.
  econstructor; eauto.
  eapply equivalent_states_trans; eauto.
  eapply no_newq_session_step; eauto.
Qed.

Lemma multistep_partial_sort_no_newq:
forall la s s' pi,
multistep s la s' pi ->
no_newq_session (snd s) ->
exists s'',
multistep s (partial_sort should_swap_no_newq la) s'' pi /\
equivalent_states s' s''.
Proof.
  induction la; simpl; intros;
  inversion H; cleanup.
  eexists; do 2 (split; eauto).
  apply unfoldM_refl.
  (split; eauto).
  apply equivalent_refl.

  eapply IHla in H7; cleanup.
  edestruct (multistep_insert_into_no_newq (partial_sort should_swap_no_newq la)).
  econstructor; eauto.
  eauto.
  cleanup.
  eexists; split; [eauto|].
  eapply equivalent_states_trans; eauto.
  eapply no_newq_session_step; eauto.
Qed.


Lemma finished_equivalent_sessions_r:
forall s s',
equivalent s s' ->
finished s' ->
finished s.
Proof.
  unfold finished; intros.
  apply H in H1; eauto.
Qed.

Lemma insert_split_two:
forall A (AEQ: EqDec A) V (m: finite_map A V) a a' v v',
insert m a v a' = Some v' ->
(a = a' /\ v = v') \/ (a <> a' /\ m a' = Some v').
Proof.
  intros; destruct (AEQ a a'); subst.
  rewrite insert_eq in H; inversion H; eauto.
  rewrite insert_neq in H; eauto.
Qed.

Lemma step_participants:
forall a s1 s2 r,
step s1 a s2 r ->
exists s, unfoldM (snd s1) s /\

((exists p P, a = Tau p /\ s p = Some P /\
(forall q l e P', P <> (p_send q l e P')) /\
(forall q lP', P <> (p_recv q lP')) /\
(forall lz, P <> (p_end lz))) \/

(exists p q P lQ l e B, a = Transmit p q l B /\ p <> q /\
s p = Some (p_send q l e P) /\ s q = Some (p_recv p lQ))).
Proof.
  intros a s1 s2 r Hstep. destruct s1 as [qstate1 M1]. destruct s2 as [qstate2 M2].
  induction Hstep.
  - exists s1. split; [apply unfoldM_refl|].
    right. exists p, q, P, lQ, l0, e, v. repeat split; eauto.
  - exists s1. split; [apply unfoldM_refl|].
    right. exists p, q, P, lQ, l0, e, (QVal v). repeat split; eauto.
  - exists s1. split; [apply unfoldM_refl|].
    left. exists p, (p_newq P).
    split; [reflexivity|]. split; [assumption|].
    repeat split; intros; discriminate.
  - exists s1. split; [apply unfoldM_refl|].
    left. exists p, (p_ite e P1 P0). split; [reflexivity|]. split; [assumption|].
    repeat split; intros; discriminate.
  - exists s1. split; [apply unfoldM_refl|].
    left. exists p, (p_ite e P1 P0). split; [reflexivity|]. split; [assumption|].
    repeat split; intros; discriminate.
  - exists s1. split; [apply unfoldM_refl|].
    left. exists p, (p_measure (Val (QVal q)) P).
    split; [reflexivity|]. split; [assumption|].
    repeat split; intros; discriminate.
  - exists s1. split; [apply unfoldM_refl|].
    left. exists p, (p_unitary dim U (map (fun z => Val (QVal z)) lq) P).
    split; [reflexivity|]. split; [assumption|].
    repeat split; intros; discriminate.
  - destruct IHHstep as [s [Hunfold Hcase]].
    exists s. split; [eapply unfoldM_trans; eauto|exact Hcase].
Qed.

Transparent equivalent.
Lemma unfoldM_equivalent:
forall (M M' : session),
unfoldM M M' -> (forall p R, M p <> Some (p_rec R)) -> equivalent M M'.
Proof.
  intros M M' Hunfold Hnonrec.
  unfold equivalent, included.
  split.
  - intros p P HM.
    eapply unfoldM_lookup_nonrec; eauto.
    intros R Hrec.
    apply (Hnonrec p R).
    rewrite HM.
    now f_equal.
  - intros p P HM'.
    destruct (Hunfold p) as [[HM HM'']|[P0 [P' [HM [HM'' Hpre]]]]].
    + rewrite HM' in HM''.
      discriminate.
    + assert (Hproc : P' = P0).
      { eapply precongP_nonrec; [exact Hpre|].
        intros R Hrec.
        apply (Hnonrec p R).
        rewrite HM.
        now f_equal. }
      rewrite HM' in HM''.
      injection HM'' as HPP'.
      assert (HP0 : P0 = P) by congruence.
      rewrite HP0 in HM.
      exact HM.
Qed.
Opaque equivalent.


Lemma has_Tau_incr_free_le : forall P fvP fvE m shift,
    has_Tau (incr_free fvP fvE m shift P) -> has_Tau P.
Proof.
  induction P; intros fvP fvE m shift Htau; simpl in *.
  - contradiction.
  - eapply IHP; exact Htau.
  - contradiction.
  - contradiction.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - contradiction.
Qed.

Lemma has_Tau_substitution_le : forall P R x m n,
    (has_Tau R -> has_Tau P) ->
    has_Tau (substitutionP x m n R P) ->
    has_Tau P.
Proof.
  induction P; intros R xsub mshift eshift Hrel Hsubst; simpl in *.
  - contradiction.
  - eapply (IHP R (S xsub) (S mshift) eshift); assumption.
  - contradiction.
  - contradiction.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - destruct (n <? xsub) eqn:Hlt; simpl in Hsubst; [contradiction|].
    destruct (n =? xsub) eqn:Heq; simpl in Hsubst.
    + apply Hrel. eapply has_Tau_incr_free_le; exact Hsubst.
    + contradiction.
Qed.

Lemma has_Tau_substitution_ge : forall P R x m n,
    has_Tau P ->
    has_Tau (substitutionP x m n R P).
Proof.
  induction P; intros R x m k Htau; simpl in *; try contradiction; try constructor.
  - eapply IHP. exact Htau.
Qed.

Lemma has_Tau_precong_backward : forall P Q,
    precongP P Q -> has_Tau Q -> has_Tau P.
Proof.
  intros P Q Hpre; induction Hpre; intros Htau.
  - exact Htau.
  - simpl. eapply (has_Tau_substitution_le P (p_rec P) 0 0 0).
    + intros Hrec; exact Hrec.
    + apply IHHpre; exact Htau.
  - apply IHHpre1. apply IHHpre2. exact Htau.
Qed.

Lemma has_Tau_precong_forward : forall P Q,
    precongP P Q -> has_Tau P -> has_Tau Q.
Proof.
  intros P Q Hpre; induction Hpre; intros Htau.
  - exact Htau.
  - apply IHHpre.
    eapply has_Tau_substitution_ge.
    simpl in Htau. exact Htau.
  - apply IHHpre2. apply IHHpre1. exact Htau.
Qed.

Lemma tau_step_has_tau:
  forall s s' p pi P,
  step s (Tau p) s' pi ->
  (snd s) p = Some P ->
  has_Tau P.
Proof.
  intros [qs M] [qs' M'] p pi P Hstep Hlookup; simpl in *.
  destruct (@step_tau_decompose_core qs M p qs' M' pi Hstep)
    as [Mbase [Mcore [Hunfold [Hcore Hout]]]].
  assert (Hactive : exists Pactive,
      Mbase p = Some Pactive /\ has_Tau Pactive).
  { inversion Hcore; subst; eexists; split; try eassumption; simpl; constructor. }
  destruct Hactive as [Pactive [Hactive Hactive_tau]].
  specialize (Hunfold p).
  rewrite Hlookup in Hunfold.
  destruct Hunfold as [[Hnone _]|[Psrc [Pdst [Hsrc [Hdst Hpre]]]]].
  - discriminate.
  - rewrite Hactive in Hdst; inversion Hdst; subst Pdst.
    inversion Hsrc; subst Psrc.
    eapply has_Tau_precong_backward; eauto.
Qed.

Lemma transmit_step_no_tau:
  forall s s' p q l B pi P Q,
  step s (Transmit p q l B) s' pi ->
  (snd s) p = Some P ->
  (snd s) p = Some Q ->
  ~has_Tau P /\ ~has_Tau Q.
Proof.
  intros [qs M] s' p q l B pi P Q Hstep HP HQ.
  assert (HPQ : P = Q) by congruence.
  subst Q.
  assert (Hnot : ~ has_Tau P).
  {
    destruct (@step_participants (Transmit p q l B) (qs, M) s' pi Hstep)
      as [Mbase [Hunfold Hparticipants]].
    destruct Hparticipants as [[p0 [P0 [Hact _]]]|Hcomm].
    - discriminate Hact.
    - destruct Hcomm as [p0 [q0 [P0 [lQ [l0 [e [B0 [Hact [Hneq [Hsend Hrecv]]]]]]]]]].
      inversion Hact; subst p0 q0 l0 B0.
      specialize (Hunfold p).
      destruct Hunfold as [[Hnone _]|[Psrc [Pdst [Hsrc [Hdst Hpre]]]]].
      + rewrite HP in Hnone. discriminate.
      + rewrite HP in Hsrc. inversion Hsrc; subst Psrc.
        rewrite Hsend in Hdst. inversion Hdst; subst Pdst.
        intro Htau.
        pose proof (has_Tau_precong_forward _ _ Hpre Htau) as Htau_base.
        simpl in Htau_base. exact Htau_base.
  }
  split; assumption.
Qed.



Ltac invert_const :=
repeat match goal with
| [H: Some _ = Some _ |- _ ] =>
  inversion H; subst; clear H
| [H: (_, _) = (_, _) |- _ ] =>
  inversion H; subst; clear H
| [H: False |- _ ] =>
  inversion H
end.

Ltac cleanup_light :=
  try logic_clean; subst;
  try invert_const; subst;
  repeat match goal with
  | [H := _ |- _] =>
    subst H
  end;
  try match goal with
  | [H : ~True |- _] =>
    exfalso; apply H; eauto
  end.

Ltac split_pairwise_sorted :=
repeat match goal with
|[H: pairwise_sorted _ (_::_::_) |- _] =>
  apply pairwise_sorted_take_two in H; logic_clean
end.

Ltac clean_process_constr:=
repeat match goal with
|[H: p_send _ _ _ _ = p_send _ _ _ _ |- _] =>
  inversion H; clear H; cleanup_light; simpl in *
|[H: p_recv _ _ = p_recv _ _ |- _] =>
  inversion H; clear H; cleanup_light; simpl in *
|[H: p_end _ = p_end _  |- _] =>
  inversion H; clear H; cleanup_light; simpl in *
|[H: p_measure _ _ _ = p_measure _ _ _ |- _] =>
  inversion H; clear H; cleanup_light; simpl in *
|[H: p_unitary _ _ _ _ = p_unitary _ _ _ _ |- _] =>
  inversion H; clear H; cleanup_light; simpl in *
|[H: p_newq _ _ = p_newq _ _ |- _] =>
  inversion H; clear H; cleanup_light; simpl in *
|[H: p_ite _ _ _ = p_ite _ _ _ |- _] =>
  inversion H; clear H; cleanup_light; simpl in *
end.


Ltac clean_inserts :=
repeat match goal with
  |[H: _ _ _ _ _ = Some _ |- _] =>
    apply insert_split_two in H; split_ors; cleanup_light; simpl in *; clean_process_constr; try congruence
  end.


Ltac close_finished_refl :=
match goal with
| Heq : equivalent ?M ?M', Hfin : finished ?M' |- _ =>
    let Hstart := fresh "Hfinished_start" in
    pose proof (finished_equivalent_sessions_r _ _ Heq Hfin) as Hstart;
    unfold finished in Hstart;
    specialize (Hstart Env);
    simpl in Hstart;
    repeat (rewrite insert_neq in Hstart by congruence);
    try rewrite insert_eq in Hstart;
    unfold P_S in Hstart; simpl in Hstart;
    destruct (Hstart _ eq_refl) as [? Hnot_end];
    pose proof (precongP_nonrec _ _ Hnot_end
      ltac:(intros R Hrec; discriminate)) as Hprocess_eq;
    discriminate Hprocess_eq
end.

Ltac invert_multistep:=
match goal with
|[H: multistep _ _ _ _ |- _] =>
  inversion H; clear H; simpl in *; cleanup_light; simpl in *;
  repeat case_analysis; simpl in *; cleanup_light; try congruence;
  try match goal with
  | [H: _ = partial_sort should_swap ?acts,
     H0: pairwise_sorted should_swap (partial_sort should_swap ?acts) |- _] =>
      rewrite <- H in H0; simpl in *
  end;
  try solve [close_finished_refl];
  try split_pairwise_sorted
end.


Opaque equivalent.

Lemma should_swap_facts:
(forall l v, should_swap (Transmit Env Alice l v) (Tau Source) = true) /\
(forall l v, should_swap (Transmit Env Bob l v) (Tau Source) = true) /\
(forall l v, should_swap (Transmit Source Bob l v) (Tau Alice) = true)/\
(forall l v, should_swap (Transmit Alice Env l v) (Tau Bob) = true) /\
(forall l v, should_swap (Transmit Source Env l v) (Tau Alice) = true)/\
(forall l v, should_swap (Transmit Source Env l v) (Tau Bob) = true) /\
(forall l v, should_swap (Transmit Env Source l v) (Tau Alice) = true) /\
(forall l v, should_swap (Transmit Env Source l v) (Tau Bob) = true).
Proof.
  simpl; intuition eauto.
Qed.

Lemma should_swap_no_newq_facts:
(forall l v, should_swap_no_newq (Transmit Env Alice l v) (Tau Source) = true) /\
(forall l v, should_swap_no_newq (Transmit Env Bob l v) (Tau Source) = true) /\
(forall l v, should_swap_no_newq (Transmit Source Bob l v) (Tau Alice) = true)/\
(forall l v, should_swap_no_newq (Transmit Alice Env l v) (Tau Bob) = true) /\
(forall l v, should_swap_no_newq (Transmit Source Env l v) (Tau Alice) = true)/\
(forall l v, should_swap_no_newq (Transmit Source Env l v) (Tau Bob) = true) /\
(forall l v, should_swap_no_newq (Transmit Env Source l v) (Tau Alice) = true) /\
(forall l v, should_swap_no_newq (Transmit Env Source l v) (Tau Bob) = true) /\
(should_swap_no_newq (Tau Bob) (Tau Alice) = true) /\
(forall l1 v1 l v, should_swap_no_newq (Transmit Source Alice l1 v1) (Transmit Env Bob l v) = true).
Proof.
  simpl; intuition eauto.
Qed.

Ltac solve_insert_goal:=
solve [repeat (try eapply insert_eq; erewrite insert_neq; [| try congruence]);
    apply insert_eq].

Ltac clear_process_constraints :=
  repeat match goal with
  |[H: forall _, _ <> p_end _|- _] =>
  clear H
  |[H: forall _ _, _ <> p_recv _ _|- _] =>
  clear H
  |[H: forall _ _ _ _, _ <> p_send _ _ _ _|- _] =>
  clear H
  end.

Ltac split_to_participants :=
  match goal with
  |[H: step _ _ _ _ |- _] =>
  eapply_fresh step_participants in H; cleanup_light;
  split_ors; cleanup_light; clean_inserts;
  simpl in *;
  match goal with
  |[H: unfoldM _ _ |- _] =>
  apply unfoldM_equivalent in H; [| unfold not; intros; clean_inserts]
  end
  end;
  repeat match goal with
    |[H: equivalent _ _,
    H0: _ _ = Some _ |- _] =>
    apply H in H0; clean_inserts
    end.

Ltac invert_tau_step :=
  match goal with
  |[H: step _ _ ?s _ |- _] =>
  destruct s;
  ((eapply step_inv_Meas in H; [| simpl; solve_insert_goal])||
  (eapply step_inv_New in H; [| simpl; solve_insert_goal])||
  (eapply step_inv_Unitary in H; [| simpl; solve_insert_goal])||
  (eapply step_inv_If in H; [| simpl; solve_insert_goal]; simpl in *; cleanup_light; split_ors)||
  (eapply tau_step_has_tau in H; [|simpl; solve_insert_goal]; simpl in *))
  end;
  cleanup_light.

Ltac invert_comm_step :=
  match goal with
  |[H: step _ _ ?s _ |- _] =>
    destruct s;
    ((eapply step_inv_Comm in H; [|solve_insert_goal|solve_insert_goal];
    split_ors)||
    (eapply transmit_step_no_tau in H; [| simpl; solve_insert_goal|simpl; solve_insert_goal])); cleanup_light; try congruence
  end.

Ltac eliminate_unfoldM :=
  match goal with
  |[H: unfoldM _ _ |- _] =>
  apply unfoldM_equivalent in H; [| unfold not; intros; clean_inserts]
  end;
  match goal with
  |[H: multistep (_, ?M) _ _ _,
  H0: equivalent _ ?M |- _] =>
  eapply multistep_equivalent_source in H; eauto
  end;
  repeat match goal with
  |[H: equivalent _ _ |- _] =>
  clear H
  end.

Ltac eliminate_insert:=
  apply insert_insert_noop ||
  apply insert_insert_noop_2 ||
  apply insert_insert_noop_3 ||
  apply insert_insert_noop_4 ||
  apply insert_insert_noop_5.

Ltac eliminate_inserts_from_multistep:=
  repeat match goal with
    | [H: multistep _ _ _ _ |- _] =>
    eapply multistep_equivalent_source in H;
    [| eapply equivalent_sym;
      (eliminate_insert ||
      (apply insert_equiv_lemma;
      eliminate_insert))
    ]
  end.

Ltac process_step' :=
eliminate_inserts_from_multistep;
invert_multistep;
split_to_participants;
clear_process_constraints;
try (invert_tau_step;
  eliminate_unfoldM);
try (invert_comm_step;
  eliminate_unfoldM).

Ltac process_step := process_step'; simpl in *; cleanup_light; simpl in *; try congruence.

(**
Arguments exist [A]%type_scope {P}%function_scope x {_}.
Arguments existT [A]%type_scope {P}%function_scope x _.
*)
Opaque U_H base_to_ucom should_swap should_swap_no_newq.

Instance qr_dec : EqDec qubit_reference := Primitives.qr_dec.

Transparent insert equivalent.

Lemma source_correct_insert_elems:
forall (m : finite_map qubit_reference (participant * fin)) q pn,
elems qubit_reference (participant * fin) (insert m q pn) =
replace_or_add (elems qubit_reference (participant * fin) m) (q, pn).
Proof. reflexivity. Qed.

Lemma source_correct_two_newq_map_index:
forall (starting_qstate : quantum_state) q0 q1,
insert
  (insert (` (projT1 starting_qstate)) q0
    (Source, length (elems qubit_reference (participant * fin)
      (` (projT1 starting_qstate))))) q1
  (Source,
    length (elems qubit_reference (participant * fin)
      (insert (` (projT1 starting_qstate)) q0
        (Source, length (elems qubit_reference (participant * fin)
          (` (projT1 starting_qstate))))))) =
insert
  (insert (` (projT1 starting_qstate)) q0
    (Source, length (elems qubit_reference (participant * fin)
      (` (projT1 starting_qstate))))) q1
  (Source,
    length (replace_or_add
      (elems qubit_reference (participant * fin)
        (` (projT1 starting_qstate)))
      (q0, (Source, length (elems qubit_reference (participant * fin)
        (` (projT1 starting_qstate))))))).
Proof.
  intros.
  rewrite source_correct_insert_elems.
  reflexivity.
Qed.

Lemma source_correct_combine_map_fst_snd : forall A B (xs : list (A * B)),
combine (map fst xs) (map snd xs) = xs.
Proof.
  intros A B xs.
  induction xs as [|[a b] xs IH]; simpl; [reflexivity|].
  f_equal; exact IH.
Qed.

Lemma Source_correct_full_existential_branch : forall
    (starting_qstate : quantum_state) (qA qB : qubit_reference)
    (x : state) (la0 : list action) (r0 : R)
    (q0 q1 : qubit_reference) (qH qC qX : quantum_state)
    (Hqm0 : quantum_map_wf
      (insert
        (insert (` (projT1 starting_qstate)) q0
          (Source, length (elems qubit_reference (participant * fin)
            (` (projT1 starting_qstate))))) q1
        (Source, length (elems qubit_reference (participant * fin)
          (insert (` (projT1 starting_qstate)) q0
            (Source, length (elems qubit_reference (participant * fin)
              (` (projT1 starting_qstate)))))))))
    (lq1 lq2 lqX : list qubit_reference)
    (Hlen1 : length lq1 = 1) (Hdim1 : 1 > 0)
    (Hlen2 : length lq2 = 2) (Hdim2 : 2 > 0)
    (HlenX : length lqX = 1) (HdimX : 1 > 0)
    (Hnames1 : [Val (QVal q0)] = map (fun z => Val (QVal z)) lq1)
    (Hnames2 : Val (QVal q0) :: Val (QVal q1) :: nil =
      map (fun z => Val (QVal z)) lq2)
    (HnamesX : [Val (QVal q1)] = map (fun z => Val (QVal z)) lqX)
    (Hpair : pairwise_sorted should_swap (Tau Source :: la0))
    (Hfresh0 : ~ In q0 (map fst (elems qubit_reference
      (participant * fin) (` (projT1 starting_qstate)))))
    (Hfresh1 : ~ In q1 (map fst (replace_or_add
      (elems qubit_reference (participant * fin)
        (` (projT1 starting_qstate)))
      (q0, (Source, length (elems qubit_reference (participant * fin)
        (` (projT1 starting_qstate))))))))
    (Hsv0 : state_vector_wf
      ((kron (n := length (elems qubit_reference (participant * fin)
        (` (projT1 starting_qstate)))) (m := 1)
          (` (projT2 starting_qstate)) ∣0⟩) ⊗ ∣0⟩))
    (HapplyH : apply_unitary
      (insert
        (insert (` (projT1 starting_qstate)) q0
          (Source, length (elems qubit_reference (participant * fin)
            (` (projT1 starting_qstate))))) q1
        (Source, length (elems qubit_reference (participant * fin)
          (insert (` (projT1 starting_qstate)) q0
            (Source, length (elems qubit_reference (participant * fin)
              (` (projT1 starting_qstate))))))))
      Hqm0
      ((kron (n := length (elems qubit_reference (participant * fin)
        (` (projT1 starting_qstate)))) (m := 1)
          (` (projT2 starting_qstate)) ∣0⟩) ⊗ ∣0⟩)
      Hsv0 U_H lq1 Hlen1 Hdim1 = Some qH)
    (HapplyC : apply_unitary (` (projT1 qH)) (proj2_sig (projT1 qH))
      (` (projT2 qH)) (proj2_sig (projT2 qH)) U_CNOT lq2 Hlen2 Hdim2 = Some qC)
    (HapplyX : apply_unitary (` (projT1 qC)) (proj2_sig (projT1 qC))
      (` (projT2 qC)) (proj2_sig (projT2 qC)) U_X lqX HlenX HdimX = Some qX)
    (Hmulti : multistep
      (qX,
        insert
          (insert
            (insert
              (insert
                (insert empty_fmap Env (P_E qA qB)) Bob P_B)
                Alice P_A)
              Source
              (p_unitary 2 U_CNOT
                (Val (QVal q0) :: Val (QVal q1) :: nil)
                (p_send Alice l_a_in (Val (QVal q0))
                  (p_send Bob l_b_in (Val (QVal q1)) (p_end nil)))))
          Source
          (p_send Alice l_a_in (Val (QVal q0))
            (p_send Bob l_b_in (Val (QVal q1)) (p_end nil))))
      la0 x r0),
    exists ln1 ln2 lnX q_state0 la1 q q2 lp1 lp2 lpX Hcnot Hh Hx Hqmwf,
      pairwise_sorted should_swap (Tau Source :: la1) /\
      multistep
        (q_state0,
          insert
            (insert
              (insert
                (insert empty_fmap Source
                  (p_send Alice l_a_in (Val (QVal q))
                    (p_send Bob l_b_in (Val (QVal q2)) (p_end nil))))
                Env (P_E qA qB)) Bob P_B) Alice P_A)
        la1 x ((1 * (1 * (1 * (1 * (1 * r0)))))%R) /\
      ~ In q (map fst (elems qubit_reference (participant * fin)
        (` (projT1 starting_qstate)))) /\
      ~ In q2 (map fst (replace_or_add
        (elems qubit_reference (participant * fin)
          (` (projT1 starting_qstate)))
        (q, (Source, length (elems qubit_reference (participant * fin)
          (` (projT1 starting_qstate))))))) /\
      Forall (fun i => i < length (elems qubit_reference
        (participant * fin) (` (projT1 q_state0)))) ln1 /\
      Forall (fun i => i < length (elems qubit_reference
        (participant * fin) (` (projT1 q_state0)))) ln2 /\
      Forall (fun i => i < length (elems qubit_reference
        (participant * fin) (` (projT1 q_state0)))) lnX /\
      Forall2 (fun q' pn => (` (projT1 q_state0)) q' = Some pn)
        (q :: nil) (combine lp1 ln1) /\
      Forall2 (fun q' pn => (` (projT1 q_state0)) q' = Some pn)
        (q :: q2 :: nil) (combine lp2 ln2) /\
      Forall2 (fun q' pn => (` (projT1 q_state0)) q' = Some pn)
        (q2 :: nil) (combine lpX lnX) /\
      projT1 q_state0 = exist
        (fun qm : finite_map qubit_reference (participant * fin) =>
          quantum_map_wf qm)
        (insert
          (insert (` (projT1 starting_qstate)) q
            (Source, length (elems qubit_reference (participant * fin)
              (` (projT1 starting_qstate))))) q2
          (Source, length (replace_or_add
            (elems qubit_reference (participant * fin)
              (` (projT1 starting_qstate)))
            (q, (Source, length (elems qubit_reference
              (participant * fin) (` (projT1 starting_qstate)))))))) Hqmwf /\
      (` (projT2 q_state0)) =
        Mmult (uc_eval (` (base_to_ucom U_X lnX Hx)))
          (Mmult (uc_eval (` (base_to_ucom U_CNOT ln2 Hcnot)))
            (Mmult (o := 1) (uc_eval (` (base_to_ucom U_H ln1 Hh)))
              ((kron (n := length (elems qubit_reference
                (participant * fin) (` (projT1 starting_qstate)))) (m := 1)
                  (` (projT2 starting_qstate)) ∣0⟩) ⊗ ∣0⟩))).
Proof.
  intros starting_qstate qA qB x la0 r0 q0 q1 qH qC qX Hqm0
    lq1 lq2 lqX Hlen1 Hdim1 Hlen2 Hdim2 HlenX HdimX
    Hnames1 Hnames2 HnamesX Hpair Hfresh0 Hfresh1 Hsv0
    HapplyH HapplyC HapplyX Hmulti.
  set (qm0 := insert
    (insert (` (projT1 starting_qstate)) q0
      (Source, length (elems qubit_reference (participant * fin)
        (` (projT1 starting_qstate))))) q1
    (Source, length (elems qubit_reference (participant * fin)
      (insert (` (projT1 starting_qstate)) q0
        (Source, length (elems qubit_reference (participant * fin)
          (` (projT1 starting_qstate)))))))) in *.
  destruct (Hresult_vector _ _ _ _ _ _ _ _ _ _ HapplyH)
    as [lpn1 [Hget1 [Hidx1 Hvec1]]].
  destruct (Hresult_vector _ _ _ _ _ _ _ _ _ _ HapplyC)
    as [lpn2 [Hget2 [Hidx2 Hvec2]]].
  destruct (Hresult_vector _ _ _ _ _ _ _ _ _ _ HapplyX)
    as [lpnX [HgetX [HidxX HvecX]]].
  assert (HmapH : (` (projT1 qH)) = qm0).
  { eapply Happly_map; exact HapplyH. }
  assert (HmapC : (` (projT1 qC)) = (` (projT1 qH))).
  { eapply Happly_map; exact HapplyC. }
  assert (HmapX : (` (projT1 qX)) = (` (projT1 qC))).
  { eapply Happly_map; exact HapplyX. }
  assert (HmapFinal : (` (projT1 qX)) =
    insert (insert (` (projT1 starting_qstate)) q0
      (Source, length (elems qubit_reference (participant * fin)
        (` (projT1 starting_qstate))))) q1
      (Source, length (replace_or_add
        (elems qubit_reference (participant * fin)
          (` (projT1 starting_qstate)))
        (q0, (Source, length (elems qubit_reference (participant * fin)
          (` (projT1 starting_qstate)))))))).
  {
    transitivity (` (projT1 qC)); [exact HmapX|].
    transitivity (` (projT1 qH)); [exact HmapC|].
    transitivity qm0; [exact HmapH|].
    unfold qm0; apply source_correct_two_newq_map_index.
  }
  assert (HmapCToInput : (` (projT1 qC)) = qm0).
  { transitivity (` (projT1 qH)); [exact HmapC|exact HmapH]. }
  assert (HmapXToInput : (` (projT1 qX)) = qm0).
  { transitivity (` (projT1 qC)); [exact HmapX|exact HmapCToInput]. }
  assert (HlenC_H : length (elems qubit_reference
    (participant * fin) (` (projT1 qC))) =
    length (elems qubit_reference (participant * fin) (` (projT1 qH)))).
  { rewrite HmapC; reflexivity. }
  assert (HlenH_input : length (elems qubit_reference
    (participant * fin) (` (projT1 qH))) =
    length (elems qubit_reference (participant * fin) qm0)).
  { rewrite HmapH; reflexivity. }
  assert (HlenC_input : length (elems qubit_reference
    (participant * fin) (` (projT1 qC))) =
    length (elems qubit_reference (participant * fin) qm0)).
  { rewrite HlenC_H, HlenH_input; reflexivity. }
  assert (HlenX_C : length (elems qubit_reference
    (participant * fin) (` (projT1 qX))) =
    length (elems qubit_reference (participant * fin) (` (projT1 qC)))).
  { rewrite HmapX; reflexivity. }
  assert (HlenX_input : length (elems qubit_reference
    (participant * fin) (` (projT1 qX))) =
    length (elems qubit_reference (participant * fin) qm0)).
  { rewrite HlenX_C, HlenC_input; reflexivity. }
  assert (HlenX_H : length (elems qubit_reference
    (participant * fin) (` (projT1 qX))) =
    length (elems qubit_reference (participant * fin) (` (projT1 qH)))).
  { rewrite HlenX_C, HlenC_H; reflexivity. }
  assert (HhWitness : length (map snd lpn1) = 1 /\
    NoDup (map snd lpn1) /\
    Forall (fun i => i < length (elems qubit_reference
      (participant * fin) (` (projT1 qX)))) (map snd lpn1)).
  {
    split; [exact (proj1 Hidx1)|].
    split; [exact (proj1 (proj2 Hidx1))|].
    rewrite HlenX_input; exact (proj2 (proj2 Hidx1)).
  }
  assert (HcnotWitness : length (map snd lpn2) = 2 /\
    NoDup (map snd lpn2) /\
    Forall (fun i => i < length (elems qubit_reference
      (participant * fin) (` (projT1 qX)))) (map snd lpn2)).
  {
    split; [exact (proj1 Hidx2)|].
    split; [exact (proj1 (proj2 Hidx2))|].
    rewrite HlenX_C, HlenC_H; exact (proj2 (proj2 Hidx2)).
  }
  assert (HxWitness : length (map snd lpnX) = 1 /\
    NoDup (map snd lpnX) /\
    Forall (fun i => i < length (elems qubit_reference
      (participant * fin) (` (projT1 qX)))) (map snd lpnX)).
  {
    split; [exact (proj1 HidxX)|].
    split; [exact (proj1 (proj2 HidxX))|].
    rewrite HlenX_C; exact (proj2 (proj2 HidxX)).
  }
  assert (Hlq1 : lq1 = q0 :: nil).
  { destruct lq1 as [|a [|b rest]]; simpl in Hlen1; try lia;
      simpl in Hnames1; inversion Hnames1; subst; reflexivity. }
  assert (Hlq2 : lq2 = q0 :: q1 :: nil).
  { destruct lq2 as [|a [|b [|c rest]]]; simpl in Hlen2; try lia;
      simpl in Hnames2; inversion Hnames2; subst; reflexivity. }
  assert (HlqX : lqX = q1 :: nil).
  { destruct lqX as [|a [|b rest]]; simpl in HlenX; try lia;
      simpl in HnamesX; inversion HnamesX; subst; reflexivity. }
  assert (Hvalues1 : Forall2 (fun q' pn => qm0 q' = Some pn) lq1 lpn1).
  {
    clear Hidx1 Hvec1.
    pose proof (get_all_values_spec qubit_reference
      (participant * fin) qm0 lq1 lpn1 Hget1) as [Hlength Hlookup].
    rewrite Hlq1 in Hlength.
    destruct lpn1 as [|pn [|pn' rest]]; simpl in Hlength; try lia.
    assert (Hq0 : qm0 q0 = Some pn).
    { apply Hlookup with (kv := (q0, pn)).
      rewrite Hlq1; simpl; left; reflexivity. }
    rewrite Hlq1. constructor; [exact Hq0|constructor].
  }
  assert (Hvalues2 : Forall2
    (fun q' pn => (` (projT1 qH)) q' = Some pn) lq2 lpn2).
  {
    clear Hidx2 Hvec2.
    pose proof (get_all_values_spec qubit_reference
      (participant * fin) (` (projT1 qH)) lq2 lpn2 Hget2)
      as [Hlength Hlookup].
    rewrite Hlq2 in Hlength.
    destruct lpn2 as [|pn0 [|pn1 [|pn2 rest]]]; simpl in Hlength; try lia.
    assert (Hq0 : (` (projT1 qH)) q0 = Some pn0).
    { apply Hlookup with (kv := (q0, pn0)).
      rewrite Hlq2; simpl; left; reflexivity. }
    assert (Hq1 : (` (projT1 qH)) q1 = Some pn1).
    { apply Hlookup with (kv := (q1, pn1)).
      rewrite Hlq2; simpl; right; left; reflexivity. }
    rewrite Hlq2. constructor; [exact Hq0|].
    constructor; [exact Hq1|constructor].
  }
  assert (HvaluesX : Forall2
    (fun q' pn => (` (projT1 qC)) q' = Some pn) lqX lpnX).
  {
    clear HidxX HvecX.
    pose proof (get_all_values_spec qubit_reference
      (participant * fin) (` (projT1 qC)) lqX lpnX HgetX)
      as [Hlength Hlookup].
    rewrite HlqX in Hlength.
    destruct lpnX as [|pn [|pn' rest]]; simpl in Hlength; try lia.
    assert (Hq1 : (` (projT1 qC)) q1 = Some pn).
    { apply Hlookup with (kv := (q1, pn)).
      rewrite HlqX; simpl; left; reflexivity. }
    rewrite HlqX. constructor; [exact Hq1|constructor].
  }
  assert (Hcombine1 : combine (map fst lpn1) (map snd lpn1) = lpn1).
  { apply source_correct_combine_map_fst_snd. }
  assert (Hcombine2 : combine (map fst lpn2) (map snd lpn2) = lpn2).
  { apply source_correct_combine_map_fst_snd. }
  assert (HcombineX : combine (map fst lpnX) (map snd lpnX) = lpnX).
  { apply source_correct_combine_map_fst_snd. }
  assert (HmultiTarget : multistep
    (qX,
      insert (insert (insert (insert empty_fmap Source
        (p_send Alice l_a_in (Val (QVal q0))
          (p_send Bob l_b_in (Val (QVal q1)) (p_end nil))))
        Env (P_E qA qB)) Bob P_B) Alice P_A)
    la0 x r0).
  {
    assert (Hinsert_congr : forall (m m' : finite_map participant process)
      (p : participant) (P : process), equivalent m m' ->
      equivalent (insert m p P) (insert m' p P)).
    {
      intros m m' p P [H12 H21].
      unfold equivalent, included in *.
      split; intros k v Hlookup.
      - destruct (participant_dec p k) as [Heq|Hneq].
        + subst k. rewrite insert_eq in Hlookup.
          inversion Hlookup; subst; apply insert_eq.
        + rewrite insert_neq in Hlookup by exact Hneq.
          rewrite insert_neq by exact Hneq.
          apply H12; exact Hlookup.
      - destruct (participant_dec p k) as [Heq|Hneq].
        + subst k. rewrite insert_eq in Hlookup.
          inversion Hlookup; subst; apply insert_eq.
        + rewrite insert_neq in Hlookup by exact Hneq.
          rewrite insert_neq by exact Hneq.
          apply H21; exact Hlookup.
    }
    set (mEnv := insert empty_fmap Env (P_E qA qB)).
    set (mBob := insert mEnv Bob P_B).
    set (mAlice := insert mBob Alice P_A).
    set (send := p_send Alice l_a_in (Val (QVal q0))
      (p_send Bob l_b_in (Val (QVal q1)) (p_end nil))).
    set (cnot := p_unitary 2 U_CNOT
      (Val (QVal q0) :: Val (QVal q1) :: nil) send).
    assert (Hdup : equivalent
      (insert (insert mAlice Source cnot) Source send)
      (insert mAlice Source send)).
    { apply insert_insert_noop. }
    assert (HswapA : equivalent
      (insert (insert mBob Alice P_A) Source send)
      (insert (insert mBob Source send) Alice P_A)).
    { apply insert_insert_comm. unfold Alice, Source; congruence. }
    assert (HswapB0 : equivalent
      (insert (insert mEnv Bob P_B) Source send)
      (insert (insert mEnv Source send) Bob P_B)).
    { apply insert_insert_comm. unfold Bob, Source; congruence. }
    pose proof (Hinsert_congr _ _ Alice P_A HswapB0) as HswapB.
    assert (HswapEnv0 : equivalent
      (insert mEnv Source send)
      (insert (insert empty_fmap Source send) Env (P_E qA qB))).
    { apply insert_insert_comm. unfold Env, Source; congruence. }
    pose proof (Hinsert_congr _ _ Bob P_B HswapEnv0) as HswapEnvB.
    pose proof (Hinsert_congr _ _ Alice P_A HswapEnvB) as HswapEnvA.
    assert (Hsession : equivalent
      (insert (insert (insert (insert empty_fmap Source send)
        Env (P_E qA qB)) Bob P_B) Alice P_A)
      (insert (insert mAlice Source cnot) Source send)).
    {
      apply equivalent_sym.
      eapply equivalent_trans; [exact Hdup|].
      eapply equivalent_trans; [exact HswapA|].
      eapply equivalent_trans; [exact HswapB|exact HswapEnvA].
    }
    eapply multistep_equivalent_source; [exact Hsession|exact Hmulti].
  }
  assert (HwfTarget : quantum_map_wf
    (insert (insert (` (projT1 starting_qstate)) q0
      (Source, length (elems qubit_reference (participant * fin)
        (` (projT1 starting_qstate))))) q1
      (Source, length (replace_or_add
        (elems qubit_reference (participant * fin)
          (` (projT1 starting_qstate)))
        (q0, (Source, length (elems qubit_reference (participant * fin)
          (` (projT1 starting_qstate))))))))).
  { rewrite <- HmapFinal. exact (proj2_sig (projT1 qX)). }
  assert (Hproj : projT1 qX = exist
    (fun qm : finite_map qubit_reference (participant * fin) =>
      quantum_map_wf qm)
    (insert (insert (` (projT1 starting_qstate)) q0
      (Source, length (elems qubit_reference (participant * fin)
        (` (projT1 starting_qstate))))) q1
      (Source, length (replace_or_add
        (elems qubit_reference (participant * fin)
          (` (projT1 starting_qstate)))
        (q0, (Source, length (elems qubit_reference (participant * fin)
          (` (projT1 starting_qstate)))))))) HwfTarget).
  {
    apply eq_sig_hprop.
    - intros; apply proof_irrelevance.
    - exact HmapFinal.
  }
  assert (Hbase_irrel : forall (d0 d1 dim : nat) (U : base_Unitary dim)
    (ln : list nat)
    (Hproof0 : length ln = dim /\ NoDup ln /\
      Forall (fun i => i < d0) ln)
    (Hproof1 : length ln = dim /\ NoDup ln /\
      Forall (fun i => i < d1) ln),
    d0 = d1 ->
    uc_eval (proj1_sig (@base_to_ucom d0 dim U ln Hproof0)) =
    uc_eval (proj1_sig (@base_to_ucom d1 dim U ln Hproof1))).
  {
    intros d0 d1 dim U ln Hproof0 Hproof1 Hd.
    subst d1.
    assert (Hproofeq : Hproof0 = Hproof1) by apply proof_irrelevance.
    subst Hproof1; reflexivity.
  }
  exists (map snd lpn1), (map snd lpn2), (map snd lpnX), qX,
    la0, q0, q1, (map fst lpn1), (map fst lpn2), (map fst lpnX),
    HcnotWitness, HhWitness, HxWitness, HwfTarget.
  repeat split.
  - exact Hpair.
  - replace ((1 * (1 * (1 * (1 * (1 * r0)))))%R) with r0 by ring.
    exact HmultiTarget.
  - exact Hfresh0.
  - exact Hfresh1.
  - exact (proj2 (proj2 HhWitness)).
  - exact (proj2 (proj2 HcnotWitness)).
  - exact (proj2 (proj2 HxWitness)).
  - rewrite Hcombine1.
    rewrite HmapXToInput.
    rewrite Hlq1 in Hvalues1.
    exact Hvalues1.
  - rewrite Hcombine2.
    rewrite HmapX, HmapC.
    rewrite Hlq2 in Hvalues2.
    exact Hvalues2.
  - rewrite HcombineX.
    rewrite HmapX.
    rewrite HlqX in HvaluesX.
    exact HvaluesX.
  - exact Hproj.
  - rewrite HvecX, Hvec2, Hvec1.
    pose proof (@Hbase_irrel
      (length (elems qubit_reference (participant * fin) (` (projT1 qC))))
      (length (elems qubit_reference (participant * fin) (` (projT1 qX))))
      1 U_X (map snd lpnX) HidxX HxWitness (eq_sym HlenX_C)) as HgateX.
    pose proof (@Hbase_irrel
      (length (elems qubit_reference (participant * fin) qm0))
      (length (elems qubit_reference (participant * fin) (` (projT1 qX))))
      1 U_H (map snd lpn1) Hidx1 HhWitness (eq_sym HlenX_input)) as HgateH.
    pose proof (@Hbase_irrel
      (length (elems qubit_reference (participant * fin) (` (projT1 qH))))
      (length (elems qubit_reference (participant * fin) (` (projT1 qX))))
      2 U_CNOT (map snd lpn2) Hidx2 HcnotWitness (eq_sym HlenX_H)) as HgateC.
    rewrite HgateX, HgateC, HgateH.
    rewrite <- HlenX_C, <- HlenX_H, <- HlenX_input.
    reflexivity.
Qed.

Opaque insert equivalent.

Lemma Source_correct:
forall starting_qstate x qA qB actions pi,

multistep (starting_qstate, insert (insert (insert (insert empty_fmap Source P_S) Env (P_E qA qB)) Bob P_B) Alice P_A)
(partial_sort should_swap actions) x pi ->
finished (snd x) ->

exists ln1 ln2 lnX q_state0 la0 q q2 lp1 lp2 lpX Hcnot Hh Hx Hqmwf,

pairwise_sorted should_swap (Tau Source :: la0) /\

multistep (q_state0,
insert (insert (insert (insert empty_fmap Source (p_send Alice l_a_in (Val (QVal q)) (p_send Bob l_b_in (Val (QVal q2)) (p_end nil)))) Env (P_E qA qB)) Bob P_B) Alice P_A) la0 x pi /\

~ In q (map fst (elems qubit_reference (participant * nat) (` (projT1 starting_qstate)))) /\

~ In q2 (map fst (replace_or_add
(elems qubit_reference (participant * nat) (` (projT1 starting_qstate)))
(q, (Source, length (elems qubit_reference (participant * nat)
(` (projT1 starting_qstate))))))) /\

Forall (fun i : nat => i < length (elems qubit_reference (participant * nat) (` (projT1 q_state0)))) ln1 /\

Forall (fun i : nat => i < length (elems qubit_reference (participant * nat) (` (projT1 q_state0))))
ln2 /\

Forall (fun i : nat => i < length (elems qubit_reference (participant * nat) (` (projT1 q_state0))))
lnX /\

Forall2 (fun q pn => (` (projT1 ( q_state0))) q = Some pn) (q::nil) (combine lp1 ln1) /\

Forall2 (fun q pn => (` (projT1 ( q_state0))) q = Some pn) (q:: q2::nil) (combine lp2 ln2) /\

Forall2 (fun q pn => (` (projT1 ( q_state0))) q = Some pn) (q2::nil) (combine lpX lnX) /\

projT1 q_state0 =
exist (fun qm : finite_map qubit_reference (participant * nat) => quantum_map_wf qm)
(insert
(insert (` (projT1 starting_qstate)) q
(Source, length (elems qubit_reference (participant * nat) (` (projT1 starting_qstate))))) q2
(Source,
length
(replace_or_add (elems qubit_reference (participant * nat) (` (projT1 starting_qstate)))
(q, (Source, length (elems qubit_reference (participant * nat) (` (projT1 starting_qstate)))))))) Hqmwf /\

` (projT2 q_state0) =
Mmult (uc_eval (` (base_to_ucom U_X lnX Hx)))
(Mmult (uc_eval (` (base_to_ucom U_CNOT ln2 Hcnot)))
(Mmult (o:=1) (uc_eval (` (base_to_ucom U_H ln1 Hh)))
((kron (n:= length (elems qubit_reference (participant * nat) (` (projT1 starting_qstate))))(m:=1) (` (projT2 starting_qstate)) ∣0⟩) ⊗ ∣0⟩))).
Proof.
  intros.
  pose proof (partial_sort_pairwise_sorted should_swap actions should_swap_true_swap) as Hsort.
  pose proof should_swap_facts as Hswap; logic_clean.

  unfold P_A, P_B, P_E, P_S in *;
  process_step.
  process_step.
  process_step.
  process_step.
  process_step.
  eapply Source_correct_full_existential_branch with
    (q0 := q0) (q1 := q1) (qH := q) (qC := q2) (qX := q3)
    (lq1 := lq) (lq2 := lq0) (lqX := lq1); eauto.
  {
    eapply multistep_equivalent_source.
    - eapply equivalent_trans.
      + apply insert_insert_noop.
      + apply equivalent_sym; apply insert_insert_noop.
    - eexact H26.
  }
  process_step.
  process_step.
  process_step.
  process_step.
  process_step.
  process_step.
  process_step.
  process_step.
  process_step.
  process_step.
Qed.

Definition action_avoids (p : participant) (a : action) : Prop :=
match a with
| Tau q => p <> q
| Transmit q r _ _ => p <> q /\ p <> r
end.

Lemma map_fst_replace_or_add_member :
forall A B (AEQ : EqDec A) (xs : list (A * B)) a b,
In a (map fst xs) ->
NoDup (map fst xs) ->
map fst (replace_or_add xs (a, b)) = map fst xs.
Proof.
  intros A B AEQ xs.
  induction xs as [|[x y] xs IH]; intros a b Hin Hnd.
  - inversion Hin.
  - simpl in *.
    inversion Hnd as [|? ? Hnotin Hnd']; subst.
    destruct (AEQ x a) as [Hxa_eq|Hxa_neq].
    + subst a. reflexivity.
    + destruct Hin as [Hxa_in|Hin].
      * congruence.
      * simpl. f_equal. apply IH; assumption.
Qed.

Transparent insert.
Lemma session_participants_insert_lookup :
forall (M : session) p P P',
M p = Some P ->
Permutation (session_participants (insert M p P')) (session_participants M).
Proof.
  intros M p P P' Hlookup.
  unfold session_participants.
  assert (Hdomain :
      map fst (elems _ _ (insert M p P')) = map fst (elems _ _ M)).
  {
    unfold insert; simpl.
    apply map_fst_replace_or_add_member.
    - apply in_map_iff. exists (p, P). split; [reflexivity|].
      apply (proj2 (proj2 (specs participant process M) p P)); exact Hlookup.
    - exact (proj1 (specs participant process M)).
  }
  rewrite Hdomain. apply Permutation_refl.
Qed.
Opaque insert.

Lemma session_participants_lookup :
forall (M : session) p P,
M p = Some P -> In p (session_participants M).
Proof.
  intros M p P Hlookup. unfold session_participants.
  apply in_map_iff. exists (p, P). split; [reflexivity|].
  apply (proj2 (proj2 (specs participant process M) p P)); exact Hlookup.
Qed.

Lemma step_session_participants :
forall qstate M a qstate' M' pi,
step (qstate, M) a (qstate', M') pi ->
Permutation (session_participants M) (session_participants M').
Proof.
  fix IH 7.
  intros qstate M a qstate' M' pi Hstep.
  dependent destruction Hstep; simpl in *.
  - eapply Permutation_trans.
    + apply Permutation_sym.
      eapply session_participants_insert_lookup with
        (M := M) (p := q) (P := p_recv p lQ) (P' := Q').
      exact H0.
    + apply Permutation_sym.
      eapply session_participants_insert_lookup with
        (M := insert M q Q') (p := p) (P := p_send q l0 e P) (P' := P).
      rewrite insert_neq by congruence. exact H.
  - eapply Permutation_trans.
    + apply Permutation_sym.
      eapply session_participants_insert_lookup with
        (M := M) (p := q) (P := p_recv p lQ) (P' := Q').
      exact H0.
    + apply Permutation_sym.
      eapply session_participants_insert_lookup with
        (M := insert M q Q') (p := p) (P := p_send q l0 e P) (P' := P).
      rewrite insert_neq by congruence. exact H.
  - apply Permutation_sym. eapply session_participants_insert_lookup; eauto.
  - apply Permutation_sym. eapply session_participants_insert_lookup; eauto.
  - apply Permutation_sym. eapply session_participants_insert_lookup; eauto.
  - apply Permutation_sym. eapply session_participants_insert_lookup; eauto.
  - apply Permutation_sym. eapply session_participants_insert_lookup; eauto.
  - eapply Permutation_trans.
    + apply unfoldM_preserves_session_participants. exact H.
    + exact (IH qstate M1' a qstate' M' r Hstep).
Qed.

Lemma step_action_participants :
forall qstate M a qstate' M' pi,
step (qstate, M) a (qstate', M') pi ->
match a with
| Tau p => In p (session_participants M)
| Transmit p q _ _ => In p (session_participants M) /\ In q (session_participants M)
end.
Proof.
  fix IH 7.
  intros qstate M a qstate' M' pi Hstep.
  dependent destruction Hstep; simpl in *.
  - split; eapply session_participants_lookup; eauto.
  - split; eapply session_participants_lookup; eauto.
  - eapply session_participants_lookup; eauto.
  - eapply session_participants_lookup; eauto.
  - eapply session_participants_lookup; eauto.
  - eapply session_participants_lookup; eauto.
  - eapply session_participants_lookup; eauto.
  - pose proof (unfoldM_preserves_session_participants M M1' H) as Hperm.
    specialize (IH qstate M1' a qstate' M' r Hstep).
    destruct a; simpl in *.
    + eapply Permutation_in; [apply Permutation_sym; exact Hperm|exact IH].
    + destruct IH as [Hp Hq]. split.
      * eapply Permutation_in; [apply Permutation_sym; exact Hperm|exact Hp].
      * eapply Permutation_in; [apply Permutation_sym; exact Hperm|exact Hq].
Qed.

Lemma step_preserves_nonrecursive_lookup :
forall qstate (M : session) a qstate' (M' : session) pi owner P,
M owner = Some P ->
(forall Q, P <> p_rec Q) ->
action_avoids owner a ->
step (qstate, M) a (qstate', M') pi ->
M' owner = Some P.
Proof.
  fix IH 12.
  intros qstate M a qstate' M' pi owner P Hlookup Hnonrec Havoids Hstep.
  dependent destruction Hstep; simpl in *.
  - destruct Havoids as [Hsender Hreceiver].
    rewrite insert_neq by congruence. rewrite insert_neq by congruence. exact Hlookup.
  - destruct Havoids as [Hsender Hreceiver].
    rewrite insert_neq by congruence. rewrite insert_neq by congruence. exact Hlookup.
  - rewrite insert_neq by congruence. exact Hlookup.
  - rewrite insert_neq by congruence. exact Hlookup.
  - rewrite insert_neq by congruence. exact Hlookup.
  - rewrite insert_neq by congruence. exact Hlookup.
  - rewrite insert_neq by congruence. exact Hlookup.
  - assert (Hlookup' : M1' owner = Some P).
    { eapply unfoldM_lookup_nonrec; eauto. }
    exact (IH qstate M1' a qstate' M' r owner P Hlookup' Hnonrec Havoids Hstep).
Qed.

Lemma step_is_alice_tau_or_avoids :
forall qstate (M : session) a qstate' (M' : session) pi P,
M Alice = Some P ->
has_Tau P ->
(forall Q, P <> p_rec Q) ->
step (qstate, M) a (qstate', M') pi ->
a = Tau Alice \/ action_avoids Alice a.
Proof.
  fix IH 11.
  intros qstate M a qstate' M' pi P Hlookup Htau Hnonrec Hstep.
  dependent destruction Hstep; simpl in *.
  - assert (Hsender : p <> Alice).
    { intro Heq. subst p. rewrite Hlookup in H. inversion H; subst P.
      unfold has_Tau in Htau; simpl in Htau; contradiction. }
    assert (Hreceiver : q <> Alice).
    { intro Heq. subst q. rewrite Hlookup in H0. inversion H0; subst P.
      unfold has_Tau in Htau; simpl in Htau; contradiction. }
    right. simpl. auto.
  - assert (Hsender : p <> Alice).
    { intro Heq. subst p. rewrite Hlookup in H. inversion H; subst P.
      unfold has_Tau in Htau; simpl in Htau; contradiction. }
    assert (Hreceiver : q <> Alice).
    { intro Heq. subst q. rewrite Hlookup in H0. inversion H0; subst P.
      unfold has_Tau in Htau; simpl in Htau; contradiction. }
    right. simpl. auto.
  - destruct (participant_dec p Alice) as [Heq|Hneq].
    + subst p. left. reflexivity.
    + right. simpl. congruence.
  - destruct (participant_dec p Alice) as [Heq|Hneq].
    + subst p. left. reflexivity.
    + right. simpl. congruence.
  - destruct (participant_dec p Alice) as [Heq|Hneq].
    + subst p. left. reflexivity.
    + right. simpl. congruence.
  - destruct (participant_dec p Alice) as [Heq|Hneq].
    + subst p. left. reflexivity.
    + right. simpl. congruence.
  - destruct (participant_dec p Alice) as [Heq|Hneq].
    + subst p. left. reflexivity.
    + right. simpl. congruence.
  - assert (Hlookup' : M1' Alice = Some P).
    { eapply unfoldM_lookup_nonrec; eauto. }
    exact (IH qstate M1' a qstate' M' r P Hlookup' Htau Hnonrec Hstep).
Qed.

Transparent should_swap_no_newq.

Lemma should_swap_no_newq_tau_nonAlice :
forall p,
In p (Alice :: Bob :: Source :: Env :: nil) ->
p <> Alice ->
should_swap_no_newq (Tau p) (Tau Alice) = true.
Proof.
  intros p Hin Hneq. simpl in Hin.
  destruct Hin as [Heq|[Heq|[Heq|[Heq|[]]]]]; subst p;
    try contradiction;
    unfold should_swap_no_newq, Alice, Bob, Source, Env; vm_compute; reflexivity.
Qed.

Lemma should_swap_no_newq_avoids_tau_alice :
forall a,
action_avoids Alice a ->
(match a with
 | Tau p => In p (Alice :: Bob :: Source :: Env :: nil)
 | Transmit _ _ _ _ => True
 end) ->
should_swap_no_newq a (Tau Alice) = true.
Proof.
  intros a Havoids Hparticipants. destruct a as [p|p q l v].
  - eapply should_swap_no_newq_tau_nonAlice; eauto.
  - simpl in *. destruct Havoids as [Hp Hq].
    destruct p as [p], q as [q].
    unfold Alice in Hp, Hq.
    unfold should_swap_no_newq, Alice.
    change (andb (negb (String.eqb "Alice" p))
      (negb (String.eqb "Alice" q)) = true).
    apply andb_true_iff. split.
    + apply negb_true_iff. apply String.eqb_neq. intro Heq.
      apply Hp. f_equal. exact Heq.
    + apply negb_true_iff. apply String.eqb_neq. intro Heq.
      apply Hq. f_equal. exact Heq.
Qed.

Lemma Alice_Tau:
forall actions a starting_state end_state P_a pi,
pairwise_sorted should_swap_no_newq (a::actions) ->
multistep starting_state actions end_state pi ->
finished (snd end_state) ->
Permutation (Alice::Bob::Source::Env::nil) (session_participants (snd starting_state)) ->
(snd starting_state) Alice = Some P_a ->
has_Tau P_a ->
(forall Q, P_a <> p_rec Q) ->
exists l s pi1 pi2,
actions = Tau Alice::l /\
step starting_state (Tau Alice) s pi1 /\
multistep s l end_state pi2 /\
pi = (pi1 * pi2)%R.
Proof.
  induction actions as [|a' actions IH]; intros a starting_state end_state P_a pi
      Hsorted Hmulti Hfinished Hparticipants HA Htau Hnonrec.
  - assert (Hstart_finished : finished (snd starting_state)).
    { inversion Hmulti; subst. eapply finished_equivalent_sessions_r; eauto. }
    unfold finished in Hstart_finished.
    specialize (Hstart_finished Alice P_a HA).
    destruct Hstart_finished as [lz Heq].
    pose proof (precongP_nonrec _ _ Heq Hnonrec) as Hprocess.
    subst P_a.
    unfold has_Tau in Htau. simpl in Htau. contradiction.
  - assert (Hdecomp :
        exists s1 pi1 pi2,
          step starting_state a' s1 pi1 /\
          multistep s1 actions end_state pi2 /\
          pi = (pi1 * pi2)%R).
    { inversion Hmulti; subst. eexists s2, r1, r2. repeat split; eauto. }
    destruct Hdecomp as [s1 [pi1 [pi2 [Hstep [Htail Hprob]]]]].
    pose proof (pairwise_sorted_take_two should_swap_no_newq a a' actions Hsorted)
      as [_ Hsorted_tail].
    destruct starting_state as [qstate M].
    destruct s1 as [qstate' M'].
    simpl in *.
    destruct (step_is_alice_tau_or_avoids _ _ _ _ _ _ _ HA Htau Hnonrec Hstep)
      as [Hfirst|Havoids].
    + subst a'.
      exists actions, (qstate', M'), pi1, pi2. repeat split; eauto.
    +
      assert (HA_next : M' Alice = Some P_a).
      { eapply step_preserves_nonrecursive_lookup; eauto. }
      assert (Hparticipants_next :
          Permutation (Alice::Bob::Source::Env::nil) (session_participants M')).
      { eapply Permutation_trans.
        - exact Hparticipants.
        - eapply step_session_participants. exact Hstep. }
      destruct (IH a' (qstate', M') end_state P_a pi2 Hsorted_tail Htail Hfinished
        Hparticipants_next HA_next Htau Hnonrec)
        as [l [state' [piA [piB [Hactions [Hstep_tail [Hmulti_tail Hprob_tail]]]]]]].
      rewrite Hactions in Hsorted_tail.
      pose proof (pairwise_sorted_take_two should_swap_no_newq a' (Tau Alice) l
        Hsorted_tail) as [Hswap_false _].
      pose proof (step_action_participants _ _ _ _ _ _ Hstep) as Hactors.
      assert (Hactor_list :
          match a' with
          | Tau p => In p (Alice::Bob::Source::Env::nil)
          | Transmit p q _ _ => In p (Alice::Bob::Source::Env::nil) /\
                                In q (Alice::Bob::Source::Env::nil)
          end).
      { destruct a'; simpl in *.
        - exact (Permutation_in p (Permutation_sym Hparticipants) Hactors).
        - destruct Hactors as [Hp Hq]. split.
          + exact (Permutation_in p (Permutation_sym Hparticipants) Hp).
          + exact (Permutation_in q (Permutation_sym Hparticipants) Hq). }
      assert (Hswap_true : should_swap_no_newq a' (Tau Alice) = true).
      { destruct a' as [p|p q lab0 val0]; simpl in Hactor_list.
        - eapply should_swap_no_newq_avoids_tau_alice; [exact Havoids|exact Hactor_list].
        - eapply should_swap_no_newq_avoids_tau_alice; [exact Havoids|constructor]. }
      rewrite Hswap_true in Hswap_false. discriminate.
Qed.

Ltac invert_Alice :=
match goal with
|[H: multistep _ _ _ _ |- _] =>
split_pairwise_sorted;
eliminate_inserts_from_multistep;
eapply Alice_Tau in H;
simpl in *; eauto; simpl; eauto;
cleanup_light; try (invert_tau_step; eliminate_unfoldM);
try solve_insert_goal;
simpl; eauto; try congruence;
[| shelve]
end.

Opaque should_swap should_swap_no_newq.
Opaque insert U_H base_to_ucom.

Lemma qgt_forall2_cons_inv : forall A B (R : A -> B -> Prop)
    (x : A) (y : B) xs ys,
    Forall2 R (x :: xs) (y :: ys) -> R x y /\ Forall2 R xs ys.
Proof.
  intros A B R x y xs ys H.
  inversion H; subst; auto.
Qed.

Lemma qgt_path1_source_wire_indices :
  forall (qm : finite_map qubit_reference (participant * fin))
    (v0 v2 : qubit_reference)
    (lp1 lp2 : list participant) (ln1 ln2 : list fin),
    qm v0 = Some (Source, 2) ->
    qm v2 = Some (Source, 3) ->
    length ln1 = 1 ->
    length ln2 = 2 ->
    Forall2 (fun (q : qubit_reference) (pn : participant * fin) =>
      qm q = Some pn) [v0] (combine lp1 ln1) ->
    Forall2 (fun (q : qubit_reference) (pn : participant * fin) =>
      qm q = Some pn) (List.cons v0 (List.cons v2 nil)) (combine lp2 ln2) ->
    ln1 = [2] /\ ln2 = (List.cons 2 (List.cons 3 nil)).
Proof.
  intros qm v0 v2 lp1 lp2 ln1 ln2 Hlookup0 Hlookup2 Hlen1 Hlen2
    Hfor1 Hfor2.
  destruct ln1 as [|i1 [|i1' rest1]]; simpl in Hlen1; try discriminate.
  inversion Hlen1; subst; clear Hlen1.
  destruct lp1 as [|p1 lp1]; simpl in Hfor1; [inversion Hfor1|].
  apply qgt_forall2_cons_inv in Hfor1 as [Hhead1 Htail1].
  rewrite Hlookup0 in Hhead1.
  inversion Hhead1; subst.
  destruct ln2 as [|i2 [|i3 [|i3' rest2]]]; simpl in Hlen2; try lia.
  inversion Hlen2; subst; clear Hlen2.
  destruct lp2 as [|p2 [|p3 lp2]]; simpl in Hfor2.
  - pose proof (Forall2_length Hfor2) as Hlengths; simpl in *; discriminate.
  - pose proof (Forall2_length Hfor2) as Hlengths; simpl in *; discriminate.
  -
  apply qgt_forall2_cons_inv in Hfor2 as [Hhead2 Htail2].
  rewrite Hlookup0 in Hhead2.
  inversion Hhead2; subst.
  simpl in Htail2.
  apply qgt_forall2_cons_inv in Htail2 as [Hhead3 Htail3].
  rewrite Hlookup2 in Hhead3.
  inversion Hhead3; subst.
  auto.
Qed.

Lemma qgt_path1_source_wire_indices_current :
  forall (qm : finite_map qubit_reference (participant * fin))
    (v0 v2 : qubit_reference)
    (lp1 lp2 lpX : list participant) (ln1 ln2 lnX : list fin),
    qm v0 = Some (Source, 2) ->
    qm v2 = Some (Source, 3) ->
    length ln1 = 1 ->
    length ln2 = 2 ->
    length lnX = 1 ->
    Forall2 (fun (q : qubit_reference) (pn : participant * fin) =>
      qm q = Some pn) [v0] (combine lp1 ln1) ->
    Forall2 (fun (q : qubit_reference) (pn : participant * fin) =>
      qm q = Some pn)
      (List.cons v0 (List.cons v2 nil)) (combine lp2 ln2) ->
    Forall2 (fun (q : qubit_reference) (pn : participant * fin) =>
      qm q = Some pn) [v2] (combine lpX lnX) ->
    ln1 = [2] /\ ln2 = (List.cons 2 (List.cons 3 nil)) /\ lnX = [3].
Proof.
  intros qm v0 v2 lp1 lp2 lpX ln1 ln2 lnX Hlookup0 Hlookup2
    Hlen1 Hlen2 HlenX Hfor1 Hfor2 HforX.
  pose proof (@qgt_path1_source_wire_indices qm v0 v2 lp1 lp2 ln1 ln2
    Hlookup0 Hlookup2 Hlen1 Hlen2 Hfor1 Hfor2) as [Hln1 Hln2].
  assert (HlnX : lnX = [3]).
  {
    destruct lnX as [|i [|i' rest]]; simpl in HlenX; try discriminate.
    inversion HlenX; subst; clear HlenX.
    destruct lpX as [|p lpX]; simpl in HforX.
    - pose proof (Forall2_length HforX) as Hlengths.
      simpl in Hlengths; discriminate.
    - apply qgt_forall2_cons_inv in HforX as [Hhead _].
      rewrite Hlookup2 in Hhead.
      inversion Hhead; reflexivity.
  }
  auto.
Qed.


Lemma qgt_qubit_list_singleton : forall (q : qubit_reference) l,
  [Val (QVal q)] = map (fun z : qubit_reference => Val (QVal z)) l ->
  l = [q].
Proof.
  intros q [|q0 [|q1 rest]] H; simpl in H; try discriminate.
  inversion H; subst; reflexivity.
Qed.
Lemma qgt_qubit_list_pair : forall (q0 q1 : qubit_reference) l,
  List.cons (Val (QVal q0)) (List.cons (Val (QVal q1)) nil) =
    map (fun z : qubit_reference => Val (QVal z)) l ->
  l = List.cons q0 (List.cons q1 nil).
Proof.
  intros q0 q1 [|a [|b [|c rest]]] H; simpl in H; try discriminate.
  inversion H; subst; reflexivity.
Qed.

