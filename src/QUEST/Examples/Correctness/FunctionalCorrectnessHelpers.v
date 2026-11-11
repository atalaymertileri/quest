From SQIR Require Import SQIR UnitaryOps.
Require Import Primitives Reals Lia.
Require Import FMap header.

Open Scope R_scope.
Open Scope C_scope.
Open Scope matrix_scope.

(* Equality of rays permits both normalization and global phase. *)
Definition ray_equiv {m n : nat} (v w : Matrix m n) : Prop :=
  exists c : Complex.C, c <> 0 /\ v = c .* w.

Lemma ray_equiv_refl : forall m n (v : Matrix m n), @ray_equiv m n v v.
Proof.
  intros; exists 1; split; [nonzero|symmetry; apply Mscale_1_l].
Qed.

Lemma ray_equiv_trans : forall m n (u v w : Matrix m n),
  @ray_equiv m n u v -> @ray_equiv m n v w -> @ray_equiv m n u w.
Proof.
  intros m n u v w [a [Ha Hu]] [b [Hb Hv]].
  exists (a*b); split; [apply Cmult_neq_0; assumption|].
  rewrite Hu, Hv, Mscale_assoc. reflexivity.
Qed.

Lemma ray_equiv_sym : forall m n (v w : Matrix m n),
  @ray_equiv m n v w -> @ray_equiv m n w v.
Proof.
  intros m n v w [c [Hc Heq]].
  exists (/c); split.
  - intro Hzero; apply Hc; exact (proj1 (Cinv_eq_0_iff c) Hzero).
  - rewrite Heq, Mscale_assoc, Cinv_l by exact Hc.
    symmetry; apply Mscale_1_l.
Qed.

Lemma ray_equiv_linear : forall m n p (A : Matrix m n) (v w : Matrix n p),
  @ray_equiv n p v w -> @ray_equiv m p (A × v) (A × w).
Proof.
  intros m n p A v w [c [Hc Heq]]. exists c; split; [exact Hc|].
  rewrite Heq. apply Mscale_mult_dist_r.
Qed.

Lemma ray_equiv_kron : forall m n p q
    (v w : Matrix m n) (a b : Matrix p q),
  @ray_equiv m n v w -> @ray_equiv p q a b ->
  @ray_equiv (m*p) (n*q) (v ⊗ a) (w ⊗ b).
Proof.
  intros m n p q v w a b [c [Hc Hv]] [d [Hd Ha]].
  exists (c*d); split; [apply Cmult_neq_0; assumption|].
  rewrite Hv, Ha, Mscale_kron_dist_l, Mscale_kron_dist_r, Mscale_assoc.
  reflexivity.
Qed.

Lemma transport_state_vector_value : forall n m (Hnm : n = m)
    (v : state_vector n), transport_state_vector Hnm v = v.
Proof. intros n m Hnm v; destruct Hnm; reflexivity. Qed.

Lemma transfer_qubit_from_lookup_vector : forall qm Hqm sv Hsv new q old n
    Hlookup,
  proj1_sig (projT2
    (transfer_qubit_from_lookup qm Hqm sv Hsv new q old n Hlookup)) = sv.
Proof. reflexivity. Qed.

Lemma normalize_removed_wire_ray : forall n (v : state_vector n),
  (0 < n)%nat -> @WF_Matrix (2^n) 1 v -> v <> Zero ->
  @ray_equiv (2^n) 1 (normalize_removed_wire v) v.
Proof.
  intros [|n] v Hn Hwf Hnonzero; [lia|].
  exists (RtoC (1 / @norm (2 ^ S n) v)); split; [|reflexivity].
  apply RtoC_neq.
  pose proof (positive_norm_of_nonzero (S n) v Hwf Hnonzero).
  unfold Rdiv; apply Rmult_integral_contrapositive_currified;
    [lra|apply Rinv_neq_0_compat; lra].
Qed.

Lemma measure_at_dimension_vector : forall
    remaining qm Hqm Hdim sv Hsv q owner index result Hlookup Hnonzero,
  proj1_sig (projT2 (snd
    (measure_qubit_nonzero_at_dimension remaining qm Hqm Hdim sv Hsv
      q owner index result Hlookup Hnonzero))) =
  normalize_removed_wire
    (@Mmult (2 ^ remaining) (2 ^ S remaining) 1
      (remove_measured_wire_operator remaining index result)
      (proj index (S remaining) result × sv)).
Proof.
  intros.
  unfold measure_qubit_nonzero_at_dimension.
  cbn -[transport_state_vector normalize_removed_wire remove_measured_wire
    proj Mmult remove_and_reindex_qubit_map].
  apply transport_state_vector_value.
Qed.

Lemma measure_at_dimension_ray : forall
    remaining qm Hqm Hdim sv Hsv q owner index result Hlookup Hnonzero,
  (0 < remaining)%nat ->
  @ray_equiv (2 ^ remaining) 1
    (proj1_sig (projT2 (snd
      (measure_qubit_nonzero_at_dimension remaining qm Hqm Hdim sv Hsv
        q owner index result Hlookup Hnonzero))))
    (@Mmult (2 ^ remaining) (2 ^ (S remaining)) 1
      (remove_measured_wire_operator remaining index result)
      (proj index (S remaining) result × sv)).
Proof.
  intros remaining qm Hqm Hdim sv Hsv q owner index result Hlookup
    Hnonzero Hremaining.
  set (projected := proj index (S remaining) result × sv).
  assert (Hindex_lt : (index < S remaining)%nat).
  {
    pose proof (quantum_map_lookup_index_lt qm Hqm q owner index Hlookup).
    rewrite Hdim in H.
    exact H.
  }
  assert (Hindex : (index <= remaining)%nat) by lia.
  assert (Hprojected_wf : @WF_Matrix (2 ^ (S remaining)) 1 projected).
  {
    unfold projected.
    apply WF_mult; [apply WF_proj|exact (proj1 Hsv)].
  }
  assert (Hprojected_nonzero : projected <> Zero).
  {
    intro Hzero.
    apply Hnonzero.
    apply (proj2 (@norm_zero_iff_zero (2 ^ (S remaining)) projected
      Hprojected_wf)).
    exact Hzero.
  }
  assert (Hprojected_fixed :
      proj index (S remaining) result × projected = projected).
  {
    unfold projected.
    rewrite <- Mmult_assoc, proj_twice_eq.
    reflexivity.
  }
  assert (Hremoved_wf :
      @WF_Matrix (2 ^ remaining) 1
        (@Mmult (2 ^ remaining) (2 ^ (S remaining)) 1
          (remove_measured_wire_operator remaining index result) projected)).
  {
    change (@WF_Matrix (2 ^ remaining) 1
      (remove_measured_wire (result := result) Hindex projected)).
    apply remove_measured_wire_wf.
    exact Hprojected_wf.
  }
  assert (Hremoved_nonzero :
      @Mmult (2 ^ remaining) (2 ^ (S remaining)) 1
        (remove_measured_wire_operator remaining index result) projected <> Zero).
  {
    change (remove_measured_wire (result := result) Hindex projected <> Zero).
    eapply remove_measured_wire_nonzero; eauto.
  }
  pose proof (@measure_at_dimension_vector remaining qm Hqm Hdim sv Hsv q
    owner index result Hlookup Hnonzero) as Hvector.
  rewrite Hvector.
  eapply normalize_removed_wire_ray; eauto.
Qed.

Lemma measure_lifted_poststate_ray : forall
    remaining qm Hqm Hdim sv Hsv q owner index result Hlookup Hnonzero,
  (0 < remaining)%nat ->
  @ray_equiv (2 ^ (S remaining)) 1
    (@Mmult (2 ^ (S remaining)) (2 ^ remaining) 1
      (insert_measured_wire_operator remaining index result)
      (proj1_sig (projT2 (snd
        (measure_qubit_nonzero_at_dimension remaining qm Hqm Hdim sv Hsv
          q owner index result Hlookup Hnonzero)))))
    (@Mmult (2 ^ (S remaining)) (2 ^ (S remaining)) 1
      (proj index (S remaining) result) sv).
Proof.
  intros remaining qm Hqm Hdim sv Hsv q owner index result Hlookup Hnonzero
    Hremaining.
  pose proof (@measure_at_dimension_ray remaining qm Hqm Hdim sv Hsv q owner
    index result Hlookup Hnonzero Hremaining) as Hmeasure.
  assert (Hindex : (index <= remaining)%nat).
  {
    pose proof (quantum_map_lookup_index_lt qm Hqm q owner index Hlookup)
      as Hindex_lt.
    rewrite Hdim in Hindex_lt; lia.
  }
  eapply ray_equiv_trans.
  - eapply ray_equiv_linear; exact Hmeasure.
  - assert (Hlift :
      @Mmult (2 ^ (S remaining)) (2 ^ remaining) 1
        (insert_measured_wire_operator remaining index result)
        (@Mmult (2 ^ remaining) (2 ^ (S remaining)) 1
          (remove_measured_wire_operator remaining index result)
          (proj index (S remaining) result × sv)) =
      @Mmult (2 ^ (S remaining)) (2 ^ (S remaining)) 1
        (proj index (S remaining) result) sv).
    {
      rewrite <- Mmult_assoc.
      rewrite insert_remove_measured_wire_operator by exact Hindex.
      rewrite <- Mmult_assoc, proj_twice_eq.
      reflexivity.
    }
    rewrite Hlift.
    apply ray_equiv_refl.
Qed.

Lemma insert_measured_wire_projector_intertwine : forall x y,
  @Mmult 16 8 8 (insert_measured_wire_operator 3 2 x) (proj 2 3 y) =
  @Mmult 16 16 8 (proj 3 4 y) (insert_measured_wire_operator 3 2 x).
Proof.
  intros x y.
  apply mat_equiv_eq.
  - apply WF_mult.
    + unfold insert_measured_wire_operator; repeat apply WF_kron;
        auto with wf_db.
    + exact (WF_proj 2 3 y).
  - apply WF_mult.
    + exact (WF_proj 3 4 y).
    + unfold insert_measured_wire_operator; repeat apply WF_kron;
        auto with wf_db.
  - unfold mat_equiv; by_cell_no_intros.
    all: unfold insert_measured_wire_operator, proj, pad_u, pad,
      Mmult, kron, I, ket, bool_to_matrix, qubit0, qubit1;
      simpl; Csimpl; lca.
Qed.

Lemma insert_measured_wire_pad_u_after_intertwine : forall x U,
  WF_Matrix U ->
  @Mmult 16 8 8 (insert_measured_wire_operator 3 2 x)
    (pad_u 3 2 U) =
  @Mmult 16 16 8 (pad_u 4 3 U)
    (insert_measured_wire_operator 3 2 x).
Proof.
  intros x U HU.
  unfold insert_measured_wire_operator, pad_u, pad.
  replace (3 - 2)%nat with 1%nat by lia.
  replace (3 - (2 + 1))%nat with 0%nat by lia.
  replace (4 - (3 + 1))%nat with 0%nat by lia.
  simpl Nat.pow.
  rewrite !kron_1_r by auto with wf_db.
  change
    (@Mmult 16 8 8 ((I 4 ⊗ ket (if x then 1 else 0)) ⊗ I 2)
      (I 4 ⊗ U) =
     @Mmult 16 16 8 (I 8 ⊗ U)
      ((I 4 ⊗ ket (if x then 1 else 0)) ⊗ I 2)).
  replace (I 8) with (I (4 * 2)) by reflexivity.
  rewrite <- (id_kron 4 2).
  rewrite (kron_assoc (I 4) (ket (if x then 1 else 0)) (I 2))
    by auto with wf_db.
  rewrite <- (kron_1_l 2 2 U) at 1 by auto with wf_db.
  change
    (@Mmult (4 * 4) (4 * 2) (4 * 2) (I 4 ⊗
      (ket (if x then 1 else 0) ⊗ I 2))
      (I 4 ⊗ (I 1 ⊗ U)) =
     @Mmult (4 * 4) (4 * 4) (4 * 2) ((I 4 ⊗ I 2) ⊗ U)
      (I 4 ⊗ (ket (if x then 1 else 0) ⊗ I 2))).
  rewrite (kron_assoc (I 4) (I 2) U) by auto with wf_db.
  assert (Hleft :
      (ket (if x then 1 else 0) ⊗ I 2) × (I 1 ⊗ U) =
      ket (if x then 1 else 0) ⊗ U).
  {
    rewrite (@kron_mixed_product 2 1 1 2 2 2
      (ket (if x then 1 else 0)) (I 2) (I 1) U).
    rewrite Mmult_1_r by auto with wf_db.
    rewrite Mmult_1_l by auto with wf_db.
    reflexivity.
  }
  assert (Hright :
      (I 2 ⊗ U) × (ket (if x then 1 else 0) ⊗ I 2) =
      ket (if x then 1 else 0) ⊗ U).
  {
    rewrite (@kron_mixed_product 2 2 1 2 2 2
      (I 2) U (ket (if x then 1 else 0)) (I 2)).
    rewrite Mmult_1_l by auto with wf_db.
    rewrite Mmult_1_r by auto with wf_db.
    reflexivity.
  }
  transitivity ((I 4 × I 4) ⊗
    (ket (if x then 1 else 0) ⊗ U)).
  - transitivity ((I 4 × I 4) ⊗
      ((ket (if x then 1 else 0) ⊗ I 2) × (I 1 ⊗ U))).
    + exact (@kron_mixed_product 4 4 4 4 2 2
        (I 4) (ket (if x then 1 else 0) ⊗ I 2) (I 4) (I 1 ⊗ U)).
    + rewrite Hleft.
      rewrite Mmult_1_l by auto with wf_db.
      reflexivity.
  - symmetry.
    transitivity ((I 4 × I 4) ⊗
      ((I 2 ⊗ U) × (ket (if x then 1 else 0) ⊗ I 2))).
    + exact (@kron_mixed_product 4 4 4 4 4 2
        (I 4) (I 2 ⊗ U) (I 4) (ket (if x then 1 else 0) ⊗ I 2)).
    + rewrite Hright.
      rewrite Mmult_1_l by auto with wf_db.
      reflexivity.
Qed.

Lemma insert_measured_wire_pad_u_before_intertwine : forall x U,
  WF_Matrix U ->
  @Mmult 16 8 8 (insert_measured_wire_operator 3 2 x)
    (pad_u 3 1 U) =
  @Mmult 16 16 8 (pad_u 4 1 U)
    (insert_measured_wire_operator 3 2 x).
Proof.
  intros x U HU.
  apply mat_equiv_eq.
  - apply WF_mult.
    + unfold insert_measured_wire_operator; repeat apply WF_kron;
        auto with wf_db.
    + exact (@WF_pad_u 3 1 U HU).
  - apply WF_mult.
    + exact (@WF_pad_u 4 1 U HU).
    + unfold insert_measured_wire_operator; repeat apply WF_kron;
        auto with wf_db.
  - unfold mat_equiv; by_cell_no_intros.
    all: unfold insert_measured_wire_operator, pad_u, pad,
      Mmult, kron, I, ket; simpl; Csimpl; lca.
Qed.

Definition insert_cnot_three_wire (x : bool) : Matrix 8 4 :=
  I 2 ⊗ ket (if x then 1 else 0) ⊗ I 2.

Definition insert_cnot_gap_cnot : Matrix 8 8 :=
  ∣1⟩⟨1∣ ⊗ I 2 ⊗ σx .+ ∣0⟩⟨0∣ ⊗ I 2 ⊗ I 2.

Lemma pad_ctrl_3_1_2_eq : pad_ctrl 3 1 2 σx = I 2 ⊗ cnot.
Proof.
  unfold pad_ctrl.
  bdestruct_all; try lia.
  unfold pad.
  replace (3 - (1 + 2))%nat with 0%nat by lia.
  replace (2 - 1 - 1)%nat with 0%nat by lia.
  simpl Nat.pow.
  bdestruct_all; try lia.
  rewrite !kron_1_r by auto with wf_db.
  f_equal.
  exact cnot_decomposition.
Qed.

Lemma insert_cnot_three_wire_intertwine : forall x,
  @Mmult 8 4 4 (insert_cnot_three_wire x) cnot =
  @Mmult 8 8 4 insert_cnot_gap_cnot (insert_cnot_three_wire x).
Proof.
  intros x.
  apply mat_equiv_eq.
  - unfold insert_cnot_three_wire; apply WF_mult;
      repeat apply WF_kron; auto with wf_db.
  - unfold insert_cnot_three_wire, insert_cnot_gap_cnot;
      apply WF_mult; repeat apply WF_kron; auto with wf_db.
  - unfold mat_equiv, insert_cnot_three_wire, insert_cnot_gap_cnot;
      by_cell_no_intros.
    all: unfold Mmult, kron, cnot, ket, bra, I, σx, qubit0, qubit1;
      simpl; Csimpl; lca.
Qed.

Lemma pad_ctrl_4_1_3_expansion :
  pad_ctrl 4 1 3 σx = I 2 ⊗ insert_cnot_gap_cnot.
Proof.
  unfold pad_ctrl.
  bdestruct_all; try lia.
  unfold pad, insert_cnot_gap_cnot.
  replace (4 - (1 + 3))%nat with 0%nat by lia.
  replace (3 - 1 - 1)%nat with 1%nat by lia.
  simpl Nat.pow.
  rewrite !kron_1_r by auto with wf_db.
  reflexivity.
Qed.

Lemma insert_measured_wire_cnot_factor : forall x,
  insert_measured_wire_operator 3 2 x =
    I 2 ⊗ insert_cnot_three_wire x.
Proof.
  intros x.
  unfold insert_measured_wire_operator, insert_cnot_three_wire.
  simpl Nat.pow.
  replace (I 4) with (I 2 ⊗ I 2) by exact (id_kron 2 2).
  change (((I 2 ⊗ I 2) ⊗ ket (if x then 1 else 0)) ⊗ I 2 =
    I 2 ⊗ ((I 2 ⊗ ket (if x then 1 else 0)) ⊗ I 2)).
  transitivity (I 2 ⊗ (I 2 ⊗ (ket (if x then 1 else 0) ⊗ I 2))).
  - rewrite (kron_assoc (I 2 ⊗ I 2) (ket (if x then 1 else 0)) (I 2))
      by auto with wf_db.
    rewrite (kron_assoc (I 2) (I 2)
      (ket (if x then 1 else 0) ⊗ I 2)) by auto with wf_db.
    reflexivity.
  - rewrite (kron_assoc (I 2) (ket (if x then 1 else 0)) (I 2))
      by auto with wf_db.
    reflexivity.
Qed.

Lemma insert_measured_wire_cnot_intertwine : forall x,
  @Mmult 16 8 8 (insert_measured_wire_operator 3 2 x)
    (pad_ctrl 3 1 2 σx) =
  @Mmult 16 16 8 (pad_ctrl 4 1 3 σx)
    (insert_measured_wire_operator 3 2 x).
Proof.
  intros x.
  rewrite !insert_measured_wire_cnot_factor, pad_ctrl_3_1_2_eq,
    pad_ctrl_4_1_3_expansion.
  change (@Mmult (2 * 8) (2 * 4) (2 * 4)
    (I 2 ⊗ insert_cnot_three_wire x) (I 2 ⊗ cnot) =
    @Mmult (2 * 8) (2 * 8) (2 * 4)
      (I 2 ⊗ insert_cnot_gap_cnot)
      (I 2 ⊗ insert_cnot_three_wire x)).
  transitivity ((I 2 × I 2) ⊗
    (insert_cnot_three_wire x × cnot)).
  - exact (@kron_mixed_product 2 2 2 8 4 4
      (I 2) (insert_cnot_three_wire x) (I 2) cnot).
  - rewrite insert_cnot_three_wire_intertwine.
    symmetry; exact (@kron_mixed_product 2 2 2 8 8 4
      (I 2) insert_cnot_gap_cnot (I 2) (insert_cnot_three_wire x)).
Qed.

Lemma insert_measured_wire_compose_intertwine : forall x
    (A B : Matrix 8 8) (A' B' : Matrix 16 16),
  @Mmult 16 8 8 (insert_measured_wire_operator 3 2 x) A =
    @Mmult 16 16 8 A' (insert_measured_wire_operator 3 2 x) ->
  @Mmult 16 8 8 (insert_measured_wire_operator 3 2 x) B =
    @Mmult 16 16 8 B' (insert_measured_wire_operator 3 2 x) ->
  @Mmult 16 8 8 (insert_measured_wire_operator 3 2 x)
      (@Mmult 8 8 8 A B) =
    @Mmult 16 16 8 (@Mmult 16 16 16 A' B')
      (insert_measured_wire_operator 3 2 x).
Proof.
  intros x A B A' B' HA HB.
  rewrite <- Mmult_assoc, HA, Mmult_assoc, HB, <- Mmult_assoc.
  reflexivity.
Qed.

Definition bob_pre_measure_operator_three : Matrix 8 8 :=
  pad_u 3 2 hadamard ×
    (pad_u 3 2 (phase_shift (-PI/2)) ×
      (pad_u 3 2 hadamard ×
        ((I 2 ⊗ cnot) × pad_u 3 2 hadamard))).

Definition bob_pre_measure_operator_four : Matrix 16 16 :=
  pad_u 4 3 hadamard ×
    (pad_u 4 3 (phase_shift (-PI/2)) ×
      (pad_u 4 3 hadamard ×
        (pad_ctrl 4 1 3 σx × pad_u 4 3 hadamard))).

Lemma insert_measured_wire_bob_pre_measure_intertwine : forall x,
  @Mmult 16 8 8 (insert_measured_wire_operator 3 2 x)
      bob_pre_measure_operator_three =
  @Mmult 16 16 8 bob_pre_measure_operator_four
      (insert_measured_wire_operator 3 2 x).
Proof.
  intros x.
  unfold bob_pre_measure_operator_three, bob_pre_measure_operator_four.
  eapply insert_measured_wire_compose_intertwine.
  - apply insert_measured_wire_pad_u_after_intertwine.
    apply WF_hadamard.
  - eapply insert_measured_wire_compose_intertwine.
    + apply insert_measured_wire_pad_u_after_intertwine.
      apply WF_phase.
    + eapply insert_measured_wire_compose_intertwine.
      * apply insert_measured_wire_pad_u_after_intertwine.
        apply WF_hadamard.
      * eapply insert_measured_wire_compose_intertwine.
        -- rewrite <- pad_ctrl_3_1_2_eq.
           apply insert_measured_wire_cnot_intertwine.
        -- apply insert_measured_wire_pad_u_after_intertwine.
           apply WF_hadamard.
Qed.

Lemma insert_measured_wire_end_intertwine : forall x (A : Matrix 8 8),
  WF_Matrix A ->
  @Mmult 16 8 8 (insert_measured_wire_operator 3 3 x) A =
  @Mmult 16 16 8 (A ⊗ I 2)
    (insert_measured_wire_operator 3 3 x).
Proof.
  intros x A HA.
  assert (Hinsert : insert_measured_wire_operator 3 3 x =
      I 8 ⊗ ket (if x then 1 else 0)).
  {
    unfold insert_measured_wire_operator.
    replace (3 - 3)%nat with 0%nat by lia.
    simpl Nat.pow.
    rewrite kron_1_r by auto with wf_db.
    reflexivity.
  }
  rewrite Hinsert.
  transitivity (A ⊗ ket (if x then 1 else 0)).
  - replace A with (A ⊗ I 1) at 1 by
      (apply kron_1_r; exact HA).
    transitivity ((I 8 × A) ⊗
      (ket (if x then 1 else 0) × I 1)).
    + exact (@kron_mixed_product 8 8 8 2 1 1
        (I 8) (ket (if x then 1 else 0)) A (I 1)).
    + rewrite Mmult_1_l by auto with wf_db.
      rewrite Mmult_1_r by auto with wf_db.
      reflexivity.
  - transitivity ((A × I 8) ⊗
      (I 2 × ket (if x then 1 else 0))).
    + rewrite Mmult_1_r by auto with wf_db.
      rewrite Mmult_1_l by auto with wf_db.
      reflexivity.
    + symmetry; exact (@kron_mixed_product 8 8 8 2 2 1
        A (I 2) (I 8) (ket (if x then 1 else 0))).
Qed.

Lemma pad_u_4_2_factor : forall U,
  WF_Matrix U ->
  pad_u 4 2 U = pad_u 3 2 U ⊗ I 2.
Proof.
  intros U HU.
  unfold pad_u, pad.
  cbn [Nat.leb].
  rewrite kron_1_r by auto with wf_db.
  reflexivity.
Qed.

Lemma pad_ctrl_4_0_2_factor :
  pad_ctrl 4 0 2 σx = pad_ctrl 3 0 2 σx ⊗ I 2.
Proof.
  unfold pad_ctrl, pad.
  cbn [Nat.ltb Nat.leb].
  rewrite kron_1_r by auto with wf_db.
  reflexivity.
Qed.

Lemma tensor_identity_product : forall (A B : Matrix 8 8),
  @Mmult 16 16 16 (A ⊗ I 2) (B ⊗ I 2) =
    @Mmult 8 8 8 A B ⊗ I 2.
Proof.
  intros A B.
  transitivity ((A × B) ⊗ (I 2 × I 2)).
  - exact (@kron_mixed_product 8 8 8 2 2 2 A (I 2) B (I 2)).
  - rewrite Mmult_1_l by auto with wf_db.
    reflexivity.
Qed.

Definition alice_pre_measure_operator_three : Matrix 8 8 :=
  pad_u 3 2 hadamard ×
    (pad_u 3 2 hadamard ×
      (pad_ctrl 3 0 2 σx × pad_u 3 2 hadamard)).

Definition alice_pre_measure_operator_four : Matrix 16 16 :=
  pad_u 4 2 hadamard ×
    (pad_u 4 2 hadamard ×
      (pad_ctrl 4 0 2 σx × pad_u 4 2 hadamard)).

Lemma alice_pre_measure_operator_four_factor :
  alice_pre_measure_operator_four =
    alice_pre_measure_operator_three ⊗ I 2.
Proof.
  unfold alice_pre_measure_operator_four, alice_pre_measure_operator_three.
  rewrite !pad_u_4_2_factor by apply WF_hadamard.
  rewrite pad_ctrl_4_0_2_factor.
  rewrite tensor_identity_product.
  rewrite tensor_identity_product.
  rewrite tensor_identity_product.
  reflexivity.
Qed.

Lemma insert_measured_wire_alice_pre_measure_intertwine : forall x,
  @Mmult 16 8 8 (insert_measured_wire_operator 3 3 x)
      alice_pre_measure_operator_three =
  @Mmult 16 16 8 alice_pre_measure_operator_four
      (insert_measured_wire_operator 3 3 x).
Proof.
  intros x.
  rewrite alice_pre_measure_operator_four_factor.
  apply insert_measured_wire_end_intertwine.
  unfold alice_pre_measure_operator_three.
  repeat apply WF_mult.
  - exact (@WF_pad_u 3 2 hadamard WF_hadamard).
  - repeat apply WF_mult.
    + exact (@WF_pad_u 3 2 hadamard WF_hadamard).
    + exact (@WF_pad_ctrl 3 0 2 σx WF_σx).
    + exact (@WF_pad_u 3 2 hadamard WF_hadamard).
Qed.

Lemma insert_two_measurements_projectors : forall x y
    (v : Matrix 16 1),
  insert_measured_wire_operator 3 2 x ×
    (insert_measured_wire_operator 2 2 y ×
      (remove_measured_wire_operator 2 2 y ×
        (proj 2 3 y ×
          (remove_measured_wire_operator 3 2 x × (proj 2 4 x × v))))) =
  proj 3 4 y × (proj 2 4 x × v).
Proof.
  intros x y v.
  set (insert_x := insert_measured_wire_operator 3 2 x).
  set (insert_y := insert_measured_wire_operator 2 2 y).
  set (remove_x := remove_measured_wire_operator 3 2 x).
  set (remove_y := remove_measured_wire_operator 2 2 y).
  set (project_x := proj 2 4 x).
  set (project_y := proj 2 3 y).
  set (lifted_y := proj 3 4 y).
  change (insert_x × (insert_y ×
    (remove_y × (project_y × (remove_x × (project_x × v))))) =
    lifted_y × (project_x × v)).
  assert (Hinsert_y : insert_y × remove_y = project_y).
  {
    unfold insert_y, remove_y, project_y.
    exact (insert_remove_measured_wire_operator 2 2 y ltac:(lia)).
  }
  assert (Hinsert_x : insert_x × remove_x = project_x).
  {
    unfold insert_x, remove_x, project_x.
    exact (insert_remove_measured_wire_operator 3 2 x ltac:(lia)).
  }
  rewrite <- (Mmult_assoc insert_y remove_y
    (project_y × (remove_x × (project_x × v)))).
  rewrite Hinsert_y.
  rewrite <- (Mmult_assoc project_y project_y
    (remove_x × (project_x × v))) at 1.
  unfold project_y.
  rewrite proj_twice_eq.
  rewrite <- (Mmult_assoc insert_x (proj 2 3 y)
    (remove_x × (project_x × v))) at 1.
  unfold insert_x.
  rewrite (insert_measured_wire_projector_intertwine x y) at 1.
  rewrite Mmult_assoc at 1.
  rewrite <- (Mmult_assoc (insert_measured_wire_operator 3 2 x)
    remove_x (project_x × v)) at 1.
  unfold insert_x in Hinsert_x.
  rewrite Hinsert_x.
  rewrite <- (Mmult_assoc project_x project_x v) at 1.
  unfold project_x.
  rewrite proj_twice_eq.
  reflexivity.
Qed.

Lemma two_measurement_lifted_ray : forall x y
    (v : Matrix 16 1) (u : Matrix 8 1) (w : Matrix 4 1),
  @ray_equiv 16 1
    (insert_measured_wire_operator 3 2 x × u)
    (proj 2 4 x × v) ->
  @ray_equiv 8 1
    (insert_measured_wire_operator 2 2 y × w)
    (proj 2 3 y × u) ->
  @ray_equiv 16 1
    (insert_measured_wire_operator 3 2 x ×
      (insert_measured_wire_operator 2 2 y × w))
    (proj 3 4 y × (proj 2 4 x × v)).
Proof.
  intros x y v u w Hfirst Hsecond.
  pose proof (@ray_equiv_linear 16 8 1
    (insert_measured_wire_operator 3 2 x)
    (insert_measured_wire_operator 2 2 y × w) (proj 2 3 y × u)
    Hsecond) as Hsecond_lifted.
  assert (Hintertwine :
      insert_measured_wire_operator 3 2 x × (proj 2 3 y × u) =
      proj 3 4 y × (insert_measured_wire_operator 3 2 x × u)).
  {
    transitivity ((insert_measured_wire_operator 3 2 x × proj 2 3 y) × u).
    - symmetry; apply Mmult_assoc.
    - rewrite (insert_measured_wire_projector_intertwine x y) at 1.
      apply Mmult_assoc.
  }
  assert (Hintertwine_ray :
      @ray_equiv 16 1
        (insert_measured_wire_operator 3 2 x × (proj 2 3 y × u))
        (proj 3 4 y × (insert_measured_wire_operator 3 2 x × u))).
  {
    rewrite Hintertwine.
    apply ray_equiv_refl.
  }
  eapply ray_equiv_trans; [exact Hsecond_lifted|].
  eapply ray_equiv_trans; [exact Hintertwine_ray|].
  exact (@ray_equiv_linear 16 16 1 (proj 3 4 y)
    (insert_measured_wire_operator 3 2 x × u) (proj 2 4 x × v)
    Hfirst).
Qed.

Lemma measure_qubit_nonzero_ray : forall
    (qm : finite_map qubit_reference (participant * nat))
    (Hqm : quantum_map_wf qm)
    (sv : state_vector (Datatypes.length
      (elems qubit_reference (participant * nat) qm)))
    (Hsv : state_vector_wf sv) q owner index result Hlookup Hlen Hnonzero,
  (0 < Nat.pred (Datatypes.length
    (elems qubit_reference (participant * nat) qm)))%nat ->
  @ray_equiv
    (2 ^ Nat.pred (Datatypes.length
      (elems qubit_reference (participant * nat) qm))) 1
    (proj1_sig (projT2 (snd
      (measure_qubit_from_nonzero qm Hqm sv Hsv q owner index result
        Hlookup Hlen Hnonzero))))
    (@Mmult
      (2 ^ Nat.pred (Datatypes.length
        (elems qubit_reference (participant * nat) qm)))
      (2 ^ S (Nat.pred (Datatypes.length
        (elems qubit_reference (participant * nat) qm)))) 1
      (remove_measured_wire_operator
        (Nat.pred (Datatypes.length
          (elems qubit_reference (participant * nat) qm))) index result)
      (proj index (S (Nat.pred (Datatypes.length
        (elems qubit_reference (participant * nat) qm)))) result ×
      transport_state_vector
        (eq_sym (Nat.succ_pred_pos
          (Datatypes.length (elems qubit_reference (participant * nat) qm))
          Hlen)) sv)).
Proof.
  intros qm Hqm sv Hsv q owner index result Hlookup Hlen Hnonzero Hremaining.
  set (len := Datatypes.length (elems qubit_reference (participant * nat) qm)).
  set (remaining := Nat.pred len).
  pose (Hdim := eq_sym (Nat.succ_pred_pos len Hlen)).
  set (sv' := transport_state_vector Hdim sv).
  set (Hsv' := @transport_state_vector_wf len (S remaining) Hdim sv Hsv).
  set (HprojectedNorm :=
    eq_trans
      (eq_sym (f_equal norm
        (@transport_state_vector_proj _ _ Hdim index result sv)))
      (@transport_state_vector_norm _ _ Hdim
        (proj index (Datatypes.length
          (elems qubit_reference (participant * nat) qm)) result × sv))).
  set (Hnonzero' := fun Hzero =>
    Hnonzero (eq_trans (eq_sym HprojectedNorm) Hzero)).
  pose proof (@measure_at_dimension_ray remaining qm Hqm Hdim sv' Hsv'
    q owner index result Hlookup Hnonzero' Hremaining) as Hray.
  unfold measure_qubit_from_nonzero, measure_qubit_nonzero in *.
  exact Hray.
Qed.
