Require Import Lia Permutation String Coq.Program.Equality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import SST.
Require Import session.
Require Import QUEST. 
Require Import QuantumTeleportation.
Require Import ExamplesHelpers FunctionalCorrectnessHelpers.
From SQIR Require Import SQIR.
Require Import SQIR.UnitaryOps.
Require Import SQIR.Equivalences.
Require Import Reals.Rtrigo1.

Require Import FCTwo.

Opaque pairwise_sorted insert equivalent U_H base_to_ucom should_swap should_swap_no_newq.

Module QTPathHelperDefinitions.
Local Open Scope R_scope.
Local Open Scope C_scope.
Local Open Scope matrix_scope.
Definition qt_basis3 (a b c : bool) : Matrix 8 1 :=
  f_to_vec 3 (fun i => match i with 0%nat => a | 1%nat => b | _ => c end).
Definition qt_basis2 (a b : bool) : Matrix 4 1 :=
  f_to_vec 2 (fun i => if i =? 0 then a else b).
Definition qt_epr_preparation : Matrix 8 2 :=
  (pad_ctrl 3 1 2 σx × pad_u 3 1 hadamard) × (I 2 ⊗ (ket 0 ⊗ ket 0)).
Definition qt_alice_pre_measure : Matrix 8 8 :=
  pad_u 3 0 hadamard × pad_ctrl 3 0 1 σx.
Definition qt_correction (x y : bool) : Matrix 2 2 :=
  if x then (if y then σz × σx else σz) else (if y then σx else I 2).
Definition qt_full_branch (x y : bool) : Matrix 2 2 :=
  qt_correction x y ×
    (remove_measured_wire_operator 1 0 y ×
      (proj 0 2 y ×
        (remove_measured_wire_operator 2 0 x ×
          (proj 0 3 x × (qt_alice_pre_measure × qt_epr_preparation))))).

Lemma qt_pad_h_ancilla : pad_u 3 1 hadamard = I 2 ⊗ (hadamard ⊗ I 2).
Proof.
  unfold pad_u, pad.
  bdestruct (1 + 1 <=? 3); [|lia].
  replace (2 ^ 1)%nat with 2%nat by reflexivity.
  replace (3 - (1 + 1))%nat with 1%nat by lia.
  simpl Nat.pow.
  apply kron_assoc; auto with wf_db.
Qed.
Lemma qt_pad_cnot_ancilla : pad_ctrl 3 1 2 σx = I 2 ⊗ cnot.
Proof.
  unfold pad_ctrl, pad.
  bdestruct (1 <? 2); [|lia].
  replace (2 - 1 - 1)%nat with 0%nat by lia.
  simpl Nat.pow.
  bdestruct (1 + (1 + 0 + 1) <=? 3); [|lia].
  repeat rewrite kron_1_r by auto with wf_db.
  f_equal; apply cnot_decomposition.
Qed.
Lemma qt_epr_preparation_factor : qt_epr_preparation = I 2 ⊗ EPRpair.
Proof.
  unfold qt_epr_preparation.
  rewrite qt_pad_cnot_ancilla, qt_pad_h_ancilla.
  change (@Mmult 8 8 2
    (@Mmult 8 8 8 (I 2 ⊗ cnot) (I 2 ⊗ (hadamard ⊗ I 2)))
    (I 2 ⊗ (ket 0 ⊗ ket 0)) = I 2 ⊗ EPRpair).
  assert (Hfirst :
    @Mmult 8 8 8 (I 2 ⊗ cnot) (I 2 ⊗ (hadamard ⊗ I 2)) =
    I 2 ⊗ (cnot × (hadamard ⊗ I 2))).
  { transitivity ((I 2 × I 2) ⊗ (cnot × (hadamard ⊗ I 2))).
    - exact (@kron_mixed_product 2 2 2 4 4 4 (I 2) cnot (I 2) (hadamard ⊗ I 2)).
    - rewrite Mmult_1_l by auto with wf_db; reflexivity. }
  rewrite Hfirst.
  assert (Hsecond :
    @Mmult 8 8 2 (I 2 ⊗ (cnot × (hadamard ⊗ I 2)))
      (I 2 ⊗ (ket 0 ⊗ ket 0)) =
    I 2 ⊗ ((cnot × (hadamard ⊗ I 2)) × (ket 0 ⊗ ket 0))).
  { transitivity ((I 2 × I 2) ⊗ ((cnot × (hadamard ⊗ I 2)) × (ket 0 ⊗ ket 0))).
    - exact (@kron_mixed_product 2 2 2 4 4 1 (I 2) (cnot × (hadamard ⊗ I 2)) (I 2) (ket 0 ⊗ ket 0)).
    - rewrite Mmult_1_l by auto with wf_db; reflexivity. }
  rewrite Hsecond, EPRpair_creation; reflexivity.
Qed.
Lemma qt_append_zeros : forall (input : Matrix 2 1),
  WF_Matrix input ->
  input ⊗ ket 0 ⊗ ket 0 = (I 2 ⊗ (ket 0 ⊗ ket 0)) × input.
Proof.
  intros input Hinput.
  rewrite kron_assoc by auto with wf_db.
  transitivity ((I 2 ⊗ (ket 0 ⊗ ket 0)) × (input ⊗ I 1)).
  - symmetry.
    transitivity ((I 2 × input) ⊗ ((ket 0 ⊗ ket 0) × I 1)).
    + exact (@kron_mixed_product 2 2 1 4 1 1
        (I 2) (ket 0 ⊗ ket 0) input (I 1)).
    + rewrite Mmult_1_l by auto with wf_db.
      rewrite Mmult_1_r by auto with wf_db.
      reflexivity.
  - rewrite kron_1_r by auto with wf_db.
    reflexivity.
Qed.
Lemma qt_append_zeros_transport : forall (n m : nat) (Hn : n = 1%nat)
  (Hnm : (n + 2 = m)%nat)
  (input : state_vector n), @state_vector_wf n input ->
  transport_state_vector Hnm
    (@kron (2 ^ (n + 1)) 1 2 1
      (@kron (2 ^ n) 1 2 1 input (ket 0)) (ket 0)) =
    @Mmult 8 2 1 (@kron 2 2 4 1 (I 2) (@kron 2 1 2 1 (ket 0) (ket 0)))
      (transport_state_vector Hn input).
Proof.
  intros n m Hn Hnm input Hinput.
  subst n; simpl in Hnm; subst m.
  rewrite !FunctionalCorrectnessHelpers.transport_state_vector_value.
  apply qt_append_zeros.
  exact (proj1 Hinput).
Qed.
Lemma qt_transport_pad_u : forall (n m : nat) (Hnm : n = m)
    (i : nat) (U : Matrix 2 2) (v : state_vector n),
  transport_state_vector Hnm
    (@Mmult (Nat.pow 2 n) (Nat.pow 2 n) 1 (pad_u n i U) v) =
  (@Mmult (Nat.pow 2 m) (Nat.pow 2 m) 1 (pad_u m i U)
    (transport_state_vector Hnm v)).
Proof. intros; destruct Hnm; reflexivity. Qed.
Lemma qt_transport_pad_ctrl : forall (n m : nat) (Hnm : n = m)
    (i j : nat) (U : Matrix 2 2) (v : state_vector n),
  transport_state_vector Hnm
    (@Mmult (Nat.pow 2 n) (Nat.pow 2 n) 1 (pad_ctrl n i j U) v) =
  (@Mmult (Nat.pow 2 m) (Nat.pow 2 m) 1 (pad_ctrl m i j U)
    (transport_state_vector Hnm v)).
Proof. intros; destruct Hnm; reflexivity. Qed.
Lemma qt_transport_state_vector_compose : forall (n m p : nat)
    (Hnm : n = m) (Hmp : m = p) (v : state_vector n),
  transport_state_vector (eq_trans Hnm Hmp) v =
    transport_state_vector Hmp (transport_state_vector Hnm v).
Proof. intros; destruct Hnm, Hmp; reflexivity. Qed.
Lemma qt_base_to_ucom_ext : forall {state_dim U_dim : nat}
  (U : base_Unitary U_dim) (l1 l2 : list nat)
  (H1 : length l1 = U_dim /\ NoDup l1 /\ Forall (fun i : nat => (i < state_dim)%nat) l1)
  (H2 : length l2 = U_dim /\ NoDup l2 /\ Forall (fun i : nat => (i < state_dim)%nat) l2),
  l1 = l2 ->
  uc_eval (` (base_to_ucom U l1 H1)) = uc_eval (` (base_to_ucom U l2 H2)).
Proof.
  intros state_dim U_dim U l1 l2 H1 H2 Heq.
  subst l2.
  Transparent base_to_ucom.
  destruct U.
  - destruct l1 as [|i [|j rest]]; simpl in H1; try lia; reflexivity.
  - destruct l1 as [|i [|j [|k rest]]]; simpl in H1; try lia; reflexivity.
Qed.
Opaque base_to_ucom.
Lemma qt_basis3_tensor : forall a b c,
  qt_basis3 a b c = ket (if a then 1 else 0) ⊗ ket (if b then 1 else 0) ⊗ ket (if c then 1 else 0).
Proof.
  intros; unfold qt_basis3.
  change (I 1 ⊗ ket (if a then 1 else 0) ⊗ ket (if b then 1 else 0) ⊗ ket (if c then 1 else 0) = ket (if a then 1 else 0) ⊗ ket (if b then 1 else 0) ⊗ ket (if c then 1 else 0)).
  rewrite kron_1_l by auto with wf_db; reflexivity.
Qed.
Lemma qt_basis2_tensor : forall a b,
  qt_basis2 a b = ket (if a then 1 else 0) ⊗ ket (if b then 1 else 0).
Proof.
  intros; unfold qt_basis2.
  replace (fun i : nat => if i =? 0 then a else b) with
    (fun i : nat => match i with 0%nat => a | _ => b end) by (apply functional_extensionality; intros []; reflexivity).
  change (I 1 ⊗ ket (if a then 1 else 0) ⊗ ket (if b then 1 else 0) = ket (if a then 1 else 0) ⊗ ket (if b then 1 else 0)).
  rewrite kron_1_l by auto with wf_db; reflexivity.
Qed.
Lemma qt_epr_basis : forall (a : bool),
  qt_epr_preparation × ket (if a then 1 else 0) =
    ket (if a then 1 else 0) ⊗ EPRpair.
Proof.
  intros a; rewrite qt_epr_preparation_factor.
  replace (ket (if a then 1 else 0)) with
    (ket (if a then 1 else 0) ⊗ I 1) at 1 by apply kron_1_r.
  transitivity ((I 2 × ket (if a then 1 else 0)) ⊗ (EPRpair × I 1)).
  - exact (@kron_mixed_product 2 2 1 4 1 1 (I 2) EPRpair
      (ket (if a then 1 else 0)) (I 1)).
  - rewrite Mmult_1_l by auto with wf_db.
    rewrite Mmult_1_r by auto with wf_db; reflexivity.
Qed.
Lemma qt_epr_input_basis : forall (a : bool),
  qt_epr_preparation × ket (if a then 1 else 0) =
    / √ 2 .* (Mplus (qt_basis3 a false false) (qt_basis3 a true true)).
Proof.
  intros a; rewrite qt_epr_basis; unfold EPRpair.
  rewrite Mscale_kron_dist_r, kron_plus_distr_l.
  rewrite <- !kron_assoc by auto with wf_db.
  f_equal; f_equal; symmetry; apply qt_basis3_tensor.
Qed.
Lemma qt_Cexp_PI : Cexp PI = -(Complex.C1 : Complex.C).
Proof.
  rewrite Cexp_PI; change (RtoC (-1)%R = - RtoC 1%R); apply RtoC_opp.
Qed.
Lemma qt_alice_project_basis : forall (a b c x : bool),
  proj 0 3 x × (qt_alice_pre_measure × qt_basis3 a b c) =
  (if andb a x then - (/ √ 2) else / √ 2) .*
    qt_basis3 x (xorb a b) c.
Proof.
  intros a b c x.
  unfold qt_alice_pre_measure, qt_basis3.
  repeat rewrite Mmult_assoc.
  rewrite (@f_to_vec_cnot 3 0 1 _) by lia.
  rewrite (@f_to_vec_hadamard 3 0 _) by lia.
  repeat rewrite Mscale_mult_dist_r.
  rewrite Mmult_plus_distr_l.
  repeat rewrite Mscale_mult_dist_r.
  repeat rewrite (@f_to_vec_proj _ 0 3 _) by lia.
  cbn [update b2R].
  rewrite ?Cexp_0, ?qt_Cexp_PI, ?Cexp_neg.
  destruct a, b, c, x; simpl.
  all: replace (0 * PI)%R with 0 by ring.
  all: replace (1 * PI)%R with PI by ring.
  all: rewrite ?Cexp_0, ?qt_Cexp_PI.
  all: autorewrite with ket_db; Csimpl; f_equal;
    repeat rewrite RtoC_opp; Csimpl; C_field; reflexivity.
Qed.
Lemma qt_remove_first_basis : forall (a b c x : bool),
  remove_measured_wire_operator 2 0 x × qt_basis3 a b c =
    if Bool.eqb a x then qt_basis2 b c else Zero.
Proof.
  intros a b c x.
  apply mat_equiv_eq.
  - apply WF_mult.
    + pose proof (remove_measured_wire_operator_wf 2 0 x ltac:(lia)) as Hwf.
      cbn [Nat.pow] in Hwf; exact Hwf.
    + unfold qt_basis3; apply WF_kron; auto with wf_db.
  - destruct (Bool.eqb a x); [unfold qt_basis2; apply WF_kron; auto with wf_db|apply WF_Zero].
  - unfold mat_equiv; by_cell_no_intros.
    all: destruct a, b, c, x; simpl;
      unfold remove_measured_wire_operator, qt_basis3, qt_basis2, f_to_vec,
        proj, kron, Mmult, I, ket, bra, bool_to_matrix, qubit0, qubit1,
        Zero, scale;
      simpl; Csimpl; lca.
Qed.

Lemma qt_remove_second_basis : forall (a b y : bool),
  remove_measured_wire_operator 1 0 y × qt_basis2 a b =
    if Bool.eqb a y then ket (if b then 1 else 0) else Zero.
Proof.
  intros a b y.
  apply mat_equiv_eq.
  - apply WF_mult.
    + pose proof (remove_measured_wire_operator_wf 1 0 y ltac:(lia)) as Hwf.
      cbn [Nat.pow] in Hwf; exact Hwf.
    + unfold qt_basis2; apply WF_kron; auto with wf_db.
  - destruct (Bool.eqb a y); [auto with wf_db|apply WF_Zero].
  - unfold mat_equiv; by_cell_no_intros.
    all: destruct a, b, y; simpl;
      unfold remove_measured_wire_operator, qt_basis2, f_to_vec,
        proj, kron, Mmult, I, ket, bra, bool_to_matrix, qubit0, qubit1,
        Zero, scale;
      simpl; Csimpl; lca.
Qed.
Lemma qt_project_remove_second_basis : forall (a b y : bool),
  remove_measured_wire_operator 1 0 y ×
    (proj 0 2 y × qt_basis2 a b) =
    if Bool.eqb a y then ket (if b then 1 else 0) else Zero.
Proof.
  intros a b y.
  assert (Hproj : proj 0 2 y × qt_basis2 a b =
      (if bool_dec a y then Complex.C1 else 0) .* qt_basis2 a b).
  { unfold qt_basis2.
    replace (fun i : nat => if i =? 0 then a else b) with
      (fun i : nat => match i with 0%nat => a | _ => b end)
      by (apply functional_extensionality; intros []; reflexivity).
    rewrite (@f_to_vec_proj _ 0 2 y) by lia.
    reflexivity. }
  rewrite Hproj, Mscale_mult_dist_r, qt_remove_second_basis.
  destruct a, b, y; simpl; Csimpl; try rewrite Mscale_1_l; try rewrite Mscale_0_l;
    Csimpl; reflexivity.
Qed.
Lemma qt_alice_measure_basis : forall (a b c x : bool),
  remove_measured_wire_operator 2 0 x ×
    (proj 0 3 x × (qt_alice_pre_measure × qt_basis3 a b c)) =
  (if andb a x then - (/ √ 2) else / √ 2) .* qt_basis2 (xorb a b) c.
Proof.
  intros a b c x.
  rewrite qt_alice_project_basis.
  rewrite Mscale_mult_dist_r.
  rewrite qt_remove_first_basis.
  destruct a, b, c, x; simpl; Csimpl; try rewrite Mscale_1_l;
    try rewrite Mscale_0_l; Csimpl; reflexivity.
Qed.
Lemma qt_correction_basis : forall (a x y : bool),
  qt_correction x y × ket (if xorb y a then 1 else 0) =
  (if andb a x then -1 else 1) .* ket (if a then 1 else 0).
Proof.
  intros a x y.
  destruct a, x, y; simpl.
  all: apply mat_equiv_eq.
  all: try (apply WF_mult; auto with wf_db).
  all: try (apply WF_scale; auto with wf_db).
  all: unfold mat_equiv; by_cell_no_intros.
  all: unfold qt_correction, σx, σz, I, Mmult, ket, qubit0, qubit1, scale;
    simpl; Csimpl; lca.
Qed.
Lemma qt_full_branch_on_basis : forall (a x y : bool),
  qt_full_branch x y × ket (if a then 1 else 0) =
    (/ 2) .* ket (if a then 1 else 0).
Proof.
  intros a x y.
  unfold qt_full_branch.
  repeat rewrite Mmult_assoc.
  rewrite qt_epr_input_basis.
  repeat rewrite Mscale_mult_dist_r.
  repeat rewrite Mmult_plus_distr_l.
  rewrite ?qt_alice_measure_basis.
  repeat rewrite Mscale_mult_dist_r.
  repeat rewrite Mmult_plus_distr_l.
  rewrite ?qt_project_remove_second_basis.
  destruct a, x, y; simpl.
  assert (Hsqrt2 : (√ 2 * √ 2)%R = 2) by (apply sqrt_sqrt; lra).
  all: repeat rewrite Mmult_0_r.
  all: repeat rewrite Mmult_1_l by auto with wf_db.
  all: autorewrite with ket_db.
  all: apply mat_equiv_eq.
  all: try (repeat apply WF_scale; auto with wf_db).
  all: unfold mat_equiv; by_cell_no_intros.
  all: unfold scale, ket, qubit0, qubit1; simpl; Csimpl; C_field; lca.
Qed.
Lemma qt_full_branch_input : forall (x y : bool) (input : Matrix 2 1),
  WF_Matrix input -> qt_full_branch x y × input = (/ 2) .* input.
Proof.
  intros x y input Hinput.
  assert (Hdecomp : input = Mplus (input 0%nat 0%nat .* ket 0) (input 1%nat 0%nat .* ket 1)).
  { apply mat_equiv_eq.
    - exact Hinput.
    - apply WF_plus; repeat apply WF_scale; auto with wf_db.
    - unfold mat_equiv; by_cell_no_intros.
      all: unfold ket, qubit0, qubit1, scale, Mplus; simpl; Csimpl; reflexivity. }
  rewrite Hdecomp.
  rewrite Mmult_plus_distr_l.
  repeat rewrite Mscale_mult_dist_r.
  rewrite (qt_full_branch_on_basis false x y), (qt_full_branch_on_basis true x y).
  rewrite !Mscale_assoc.
  rewrite (Cmult_comm (input 0%nat 0%nat) (/ 2)),
    (Cmult_comm (input 1%nat 0%nat) (/ 2)).
  rewrite <- !Mscale_assoc.
  rewrite Mscale_plus_distr_r.
  reflexivity.
Qed.
Lemma qt_normalized_branch_exact : forall
    (input : Matrix 2 1) (pre : Matrix 8 1)
    (m1 : Matrix 4 1) (m2 out : Matrix 2 1) (x y : bool),
  @state_vector_wf 1 input -> @WF_Matrix 8 1 pre ->
  pre = qt_alice_pre_measure × (qt_epr_preparation × input) ->
  m1 = @normalize_removed_wire 2
    (remove_measured_wire_operator 2 0 x × (proj 0 3 x × pre)) ->
  @WF_Matrix 4 1 m1 ->
  m2 = @normalize_removed_wire 1
    (remove_measured_wire_operator 1 0 y × (proj 0 2 y × m1)) ->
  remove_measured_wire_operator 2 0 x × (proj 0 3 x × pre) <> Zero ->
  remove_measured_wire_operator 1 0 y × (proj 0 2 y × m1) <> Zero ->
  out = qt_correction x y × m2 ->
  @state_vector_wf 1 out -> out = input.
Proof.
  intros input pre m1 m2 out x y Hinputwf Hprewf Hpre Hm1 Hm1wf
    Hm2 Hnonzero1 Hnonzero2 Hout Houtwf.
  set (raw1 := remove_measured_wire_operator 2 0 x × (proj 0 3 x × pre)).
  set (raw2 := remove_measured_wire_operator 1 0 y × (proj 0 2 y × m1)).
  assert (Hraw1wf : @WF_Matrix 4 1 raw1).
  { unfold raw1; apply WF_mult.
    - pose proof (remove_measured_wire_operator_wf 2 0 x ltac:(lia)) as Hwf.
      cbn [Nat.pow] in Hwf; exact Hwf.
    - apply WF_mult.
      + pose proof (WF_proj 0 3 x) as Hp; cbn [Nat.pow] in Hp; exact Hp.
      + exact Hprewf. }
  assert (Hraw2wf : @WF_Matrix 2 1 raw2).
  { unfold raw2; apply WF_mult.
    - pose proof (remove_measured_wire_operator_wf 1 0 y ltac:(lia)) as Hwf.
      cbn [Nat.pow] in Hwf; exact Hwf.
    - apply WF_mult.
      + pose proof (WF_proj 0 2 y) as Hp; cbn [Nat.pow] in Hp; exact Hp.
      + exact Hm1wf. }
  assert (Hnorm1 : (0 < @norm 4 raw1)%R).
  { exact (positive_norm_of_nonzero 2 raw1 Hraw1wf Hnonzero1). }
  assert (Hnorm2 : (0 < @norm 2 raw2)%R).
  { exact (positive_norm_of_nonzero 1 raw2 Hraw2wf Hnonzero2). }
  set (c1 := (1 / @norm 4 raw1)%R).
  set (c2 := (1 / @norm 2 raw2)%R).
  assert (Hc1 : (c1 > 0)%R) by (unfold c1; apply Rdiv_pos_pos; lra).
  assert (Hc2 : (c2 > 0)%R) by (unfold c2; apply Rdiv_pos_pos; lra).
  assert (Hm1scale : m1 = RtoC c1 .* raw1).
  { rewrite Hm1.
    change (@normalize_removed_wire 2 raw1 = RtoC c1 .* raw1).
    pose proof (@normalize_removed_wire_positive 2 raw1 ltac:(lia)) as H.
    unfold c1 in H; rewrite H; reflexivity. }
  assert (Hm2scale : m2 = RtoC c2 .* raw2).
  { rewrite Hm2.
    change (@normalize_removed_wire 1 raw2 = RtoC c2 .* raw2).
    pose proof (@normalize_removed_wire_positive 1 raw2 ltac:(lia)) as H.
    unfold c2 in H; rewrite H; reflexivity. }
  assert (Hraw2scale : raw2 = RtoC c1 .*
    (remove_measured_wire_operator 1 0 y ×
      (proj 0 2 y × (remove_measured_wire_operator 2 0 x ×
        (proj 0 3 x × pre))))).
  { unfold raw2, raw1.
    rewrite Hm1scale.
    repeat rewrite Mscale_mult_dist_r.
    reflexivity. }
  assert (Houtscale : out = RtoC (c2 * c1 / 2)%R .* input).
  { rewrite Hout, Hm2scale, Hraw2scale.
    repeat rewrite Mscale_mult_dist_r.
    rewrite Hpre.
    assert (Hbranch :
      qt_correction x y × (remove_measured_wire_operator 1 0 y ×
        (proj 0 2 y × (remove_measured_wire_operator 2 0 x ×
          (proj 0 3 x × (qt_alice_pre_measure ×
            (qt_epr_preparation × input)))))) = qt_full_branch x y × input).
    { unfold qt_full_branch; repeat rewrite Mmult_assoc; reflexivity. }
    transitivity (c2 .* (c1 .* (qt_full_branch x y × input))).
    - f_equal; f_equal; exact Hbranch.
    - rewrite (qt_full_branch_input x y input (proj1 Hinputwf)).
      rewrite !Mscale_assoc.
      assert (Hcoef : RtoC c2 * RtoC c1 * (/ C2) = RtoC (c2 * c1 / 2)%R).
      { rewrite <- (RtoC_mult c2 c1), <- RtoC_inv,
          <- (RtoC_mult (c2 * c1) (/ 2)); f_equal; field. }
      rewrite Hcoef; reflexivity. }
  assert (Hnormout : @norm 2 out = 1%R).
  { destruct Houtwf as [_ [_ Hwf]].
    destruct (Hwf 0%nat ltac:(lia)) as [b [Hnz Hnorm]]; exact Hnorm. }
  assert (Hnorminput : @norm 2 input = 1%R).
  { destruct Hinputwf as [_ [_ Hwf]].
    destruct (Hwf 0%nat ltac:(lia)) as [b [Hnz Hnorm]]; exact Hnorm. }
  rewrite Houtscale in Hnormout.
  assert (Hc : (c2 * c1 / 2 > 0)%R) by (apply Rdiv_pos_pos; [nra|lra]).
  rewrite norm_scale, Cmod_R, Rabs_pos_eq in Hnormout by (apply Rlt_le; exact Hc).
  rewrite Hnorminput in Hnormout.
  assert (Hscalar : (c2 * c1 / 2 = 1)%R) by lra.
  rewrite Hscalar in Houtscale.
  rewrite Mscale_1_l in Houtscale.
  exact Houtscale.
Qed.
End QTPathHelperDefinitions.
Import QTPathHelperDefinitions.

Lemma qt_measure_output_vector_fixed : forall n
    (qm : finite_map qubit_reference (participant * fin))
    (Hqm : quantum_map_wf qm)
    (sv : state_vector (length (elems qubit_reference (participant * fin) qm)))
    (Hsv : state_vector_wf sv)
    (q : qubit_reference) (owner : participant) (index : fin) (result : bool)
    (Hlookup : qm q = Some (owner,index))
    (Hlen : 0 < length (elems qubit_reference (participant * fin) qm))
    (Hnonzero : norm
      (proj index (length (elems qubit_reference (participant * fin) qm))
        result × sv) <> 0%R)
    (Hinputdim : length (elems qubit_reference (participant * fin) qm) = S n)
    (Houtdim : length (elems qubit_reference (participant * fin)
      (` (projT1 (snd (measure_qubit_nonzero qm Hqm sv Hsv
        q owner index result Hlookup Hlen Hnonzero))))) = n),
  transport_state_vector Houtdim
    (` (projT2 (snd (measure_qubit_nonzero qm Hqm sv Hsv
      q owner index result Hlookup Hlen Hnonzero)))) =
  @normalize_removed_wire n
    (@Mmult (2 ^ n) (2 ^ (S n)) 1
      (remove_measured_wire_operator n index result)
      (@Mmult (2 ^ (S n)) (2 ^ (S n)) 1
        (proj index (S n) result) (transport_state_vector Hinputdim sv))).
Proof.
  intros n qm Hqm sv Hsv q owner index result Hlookup Hlen Hnonzero
    Hinputdim Houtdim.
  destruct Houtdim.
  pose proof (@measure_qubit_nonzero_full_vector qm Hqm sv Hsv q owner
    index result Hlookup Hlen Hnonzero Hinputdim) as Hfull.
  rewrite remove_measured_wire_operator_full_apply in Hfull.
  rewrite (@transport_state_vector_proj
    (length (elems qubit_reference (participant * fin) qm))
    (S (length (elems qubit_reference (participant * fin)
      (remove_and_reindex_qubit_map qm q index))))
    Hinputdim index result sv) in Hfull.
  exact Hfull.
Qed.

Lemma qt_remove_projected_nonzero : forall n i b
    (v : state_vector (S n)) (Hi : i <= n),
  @WF_Matrix (2 ^ (S n)) 1 v ->
  norm (proj i (S n) b × v) <> 0%R ->
  @Mmult (2 ^ n) (2 ^ (S n)) 1 (remove_measured_wire_operator n i b)
    (@Mmult (2 ^ (S n)) (2 ^ (S n)) 1 (proj i (S n) b) v) <> Zero.
Proof.
  intros n i b v Hi Hwf Hnonzero.
  set (projected := proj i (S n) b × v).
  assert (Hprojected_wf : @WF_Matrix (2 ^ (S n)) 1 projected).
  { unfold projected; apply WF_mult; [apply WF_proj|exact Hwf]. }
  assert (Hprojected_fixed : proj i (S n) b × projected = projected).
  {
    unfold projected.
    rewrite <- Mmult_assoc.
    rewrite proj_twice_eq.
    reflexivity.
  }
  assert (Hprojected_nonzero : projected <> Zero).
  {
    intro Hzero.
    apply Hnonzero.
    apply (proj2 (@norm_zero_iff_zero (2 ^ (S n)) projected Hprojected_wf)).
    exact Hzero.
  }
  change (remove_measured_wire (result:=b) Hi projected <> Zero).
  eapply remove_measured_wire_nonzero; eauto.
Qed.

Lemma qt_U_I_eval_one : forall
    (Hidx : length [0] = 1 /\ NoDup [0] /\
      Forall (fun i : nat => i < 1) [0]),
  uc_eval (` (base_to_ucom U_I [0] Hidx)) = I 2.
Proof.
  intros Hidx.
  assert (Hidx0 : length [0] = 1 /\ NoDup [0] /\
      Forall (fun i : nat => i < 1) [0]).
  { split; [reflexivity|].
    split; [constructor; [simpl; tauto|constructor]|].
    constructor; [simpl; lia|constructor]. }
  assert (Hidx_eq : Hidx = Hidx0) by apply proof_irrelevance.
  rewrite Hidx_eq.
  Transparent U_I base_to_ucom ueval_r.
  unfold U_I.
  cbn [base_to_ucom uc_eval ueval_r].
  simpl.
  prep_matrix_equivalence.
  unfold pad_u, pad, rotation.
  simpl.
  autorewrite with R_db trig_db Cexp_db.
  by_cell_no_intros; lca.
Qed.

Lemma qt_U_I_eval_from_length : forall n (Hn : n = 1)
    (Hidx : length [0] = 1 /\ NoDup [0] /\
      Forall (fun i : nat => i < n) [0]),
  uc_eval (` (base_to_ucom U_I [0] Hidx)) = I (2 ^ n).
Proof.
  intros n Hn Hidx.
  subst n.
  cbn [Nat.pow].
  exact (@qt_U_I_eval_one Hidx).
Qed.

Lemma qt_U_X_eval_one : forall
    (Hidx : length [0%nat] = 1%nat /\ NoDup [0%nat] /\
      Forall (fun i : nat => (i < 1)%nat) [0%nat]),
  uc_eval (` (base_to_ucom U_X [0%nat] Hidx)) = σx.
Proof.
  intros Hidx.
  assert (Hidx0 : length [0%nat] = 1%nat /\ NoDup [0%nat] /\
      Forall (fun i : nat => (i < 1)%nat) [0%nat]).
  { split; [reflexivity|]. split; [constructor; [simpl; tauto|constructor]|].
    constructor; [simpl; lia|constructor]. }
  assert (Hidx_eq : Hidx = Hidx0) by apply proof_irrelevance.
  rewrite Hidx_eq.
  Transparent U_X base_to_ucom ueval_r.
  unfold U_X.
  cbn [base_to_ucom uc_eval ueval_r].
  simpl.
  prep_matrix_equivalence.
  unfold pad_u, pad, rotation.
  simpl.
  autorewrite with R_db trig_db Cexp_db.
  by_cell_no_intros.
  all: replace (PI * / 2)%R with (PI / 2)%R by (unfold Rdiv; reflexivity).
  all: repeat rewrite cos_PI2.
  all: repeat rewrite sin_PI2.
  all: autorewrite with R_db trig_db Cexp_db.
  all: lca.
Qed.

Lemma qt_U_Z_eval_one : forall
    (Hidx : length [0%nat] = 1%nat /\ NoDup [0%nat] /\
      Forall (fun i : nat => (i < 1)%nat) [0%nat]),
  uc_eval (` (base_to_ucom U_Z [0%nat] Hidx)) = σz.
Proof.
  intros Hidx.
  assert (Hidx0 : length [0%nat] = 1%nat /\ NoDup [0%nat] /\
      Forall (fun i : nat => (i < 1)%nat) [0%nat]).
  { split; [reflexivity|]. split; [constructor; [simpl; tauto|constructor]|].
    constructor; [simpl; lia|constructor]. }
  assert (Hidx_eq : Hidx = Hidx0) by apply proof_irrelevance.
  rewrite Hidx_eq.
  Transparent U_Z base_to_ucom ueval_r.
  unfold U_Z.
  cbn [base_to_ucom uc_eval ueval_r].
  simpl.
  prep_matrix_equivalence.
  unfold pad_u, pad, rotation.
  simpl.
  autorewrite with R_db trig_db Cexp_db.
  by_cell_no_intros.
  all: replace (PI * / 2)%R with (PI / 2)%R by (unfold Rdiv; reflexivity).
  all: repeat rewrite cos_PI2.
  all: repeat rewrite sin_PI2.
  all: repeat rewrite cos_0.
  all: repeat rewrite sin_0.
  all: autorewrite with R_db trig_db Cexp_db.
  all: lca.
Qed.

Lemma qt_U_X_eval_from_length : forall n (Hn : n = 1)
    (Hidx : length [0%nat] = 1%nat /\ NoDup [0%nat] /\
      Forall (fun i : nat => (i < n)%nat) [0%nat]),
  uc_eval (` (base_to_ucom U_X [0%nat] Hidx)) = σx.
Proof.
  intros n Hn Hidx.
  subst n.
  exact (@qt_U_X_eval_one Hidx).
Qed.

Lemma qt_U_Z_eval_from_length : forall n (Hn : n = 1)
    (Hidx : length [0%nat] = 1%nat /\ NoDup [0%nat] /\
      Forall (fun i : nat => (i < n)%nat) [0%nat]),
  uc_eval (` (base_to_ucom U_Z [0%nat] Hidx)) = σz.
Proof.
  intros n Hn Hidx.
  subst n.
  exact (@qt_U_Z_eval_one Hidx).
Qed.

Definition qt_tail_session (v : qubit_reference) : session :=
  insert
    (insert
      (insert
        (insert
          (insert
            (insert empty_fmap Env
              (p_recv Bob (slist_x (p_end [Process.Var 0]))))
            Source (p_end []))
          Alice (p_end []))
        Bob ((Env) .+ l_Env_B <. Val (QVal v) .>; (p_end [])))
      Env (p_end [Val (QVal v)]))
    Bob (p_end []).

Lemma qt_tail_session_end_entries : forall v p,
  qt_tail_session v p = None \/
  exists lz, qt_tail_session v p = Some (p_end lz).
Proof.
  intros v p.
  unfold qt_tail_session.
  cbn [FMap.m].
  destruct (participant_dec p Bob) as [->|Hnb].
  - rewrite FMap.insert_eq. right; exists []; reflexivity.
  - rewrite FMap.insert_neq in * by solve [congruence | (intro Hneq; inversion Hneq)].
    destruct (participant_dec p Env) as [->|Hne].
    + rewrite FMap.insert_eq. right; exists [Val (QVal v)]; reflexivity.
    + rewrite FMap.insert_neq in * by solve [congruence | (intro Hneq; inversion Hneq)].
      destruct (participant_dec p Alice) as [->|Hna].
      * simpl; right; exists []; reflexivity.
      * rewrite FMap.insert_neq in * by solve [congruence | (intro Hneq; inversion Hneq)].
        destruct (participant_dec p Source) as [->|Hns].
        -- rewrite FMap.insert_neq in * by solve [congruence | (intro Hneq; inversion Hneq)].
           rewrite FMap.insert_eq. right; exists []; reflexivity.
        -- repeat (rewrite FMap.insert_neq in * by solve [congruence | (intro Hneq; inversion Hneq)]).
           simpl; left; reflexivity.
Qed.

Lemma qt_step_no_from_ends : forall (qs : quantum_state) (M : session)
  (a : action) (qs' : quantum_state) (M' : session) (r : R),
  (forall p, M p = None \/ exists lz, M p = Some (p_end lz)) ->
  step (qs, M) a (qs', M') r -> False.
Proof.
  intros qs M a qs' M' r Hends Hstep.
  destruct (step_participants a (qs, M) (qs', M') r Hstep)
    as [Mbase [Hunfold [Htau | Hcomm]]].
  - destruct Htau as [p [P [Ha [Hactive [HnotSend [HnotRecv HnotEnd]]]]]].
    destruct (Hends p) as [Hnone | [lz Hlookup]].
    + pose proof (Hunfold p) as Huf_none; cbn in Huf_none.
      destruct Huf_none as [Hnonebase | [Psrc [Pdst [Hsrc_none [Hbase_none Hpre_none]]]]].
      * destruct Hnonebase as [_ HbaseNone].
        rewrite HbaseNone in Hactive; discriminate.
      * change (M p = Some Psrc) in Hsrc_none.
        rewrite Hnone in Hsrc_none; discriminate.
    + pose proof (Hunfold p) as Huf_end; cbn in Huf_end.
      destruct Huf_end as [Hnonebase | [Psrc [Pdst [Hsrc_end [Hbase_end Hpre_end]]]]].
      * destruct Hnonebase as [Hsrc_none _].
        change (M p = None) in Hsrc_none.
        rewrite Hlookup in Hsrc_none; discriminate.
      * change (M p = Some Psrc) in Hsrc_end.
        rewrite Hlookup in Hsrc_end.
        injection Hsrc_end as HsrcP.
        subst Psrc.
        pose proof (precongP_nonrec _ _ Hpre_end
          ltac:(intros R Hrec; discriminate Hrec)) as Hsame.
        rewrite Hsame in Hbase_end.
        rewrite Hbase_end in Hactive.
        injection Hactive as HPeq.
        subst P.
        exact (HnotEnd lz eq_refl).
  - destruct Hcomm as [p [q [P [lQ [l [e [B [Ha [Hneq [Hsend Hrecv]]]]]]]]]].
    destruct (Hends p) as [Hnone | [lz Hlookup]].
    + pose proof (Hunfold p) as Huf_none; cbn in Huf_none.
      destruct Huf_none as [Hnonebase | [Psrc [Pdst [Hsrc_none [Hbase_none Hpre_none]]]]].
      * destruct Hnonebase as [_ HbaseNone].
        rewrite HbaseNone in Hsend; discriminate.
      * change (M p = Some Psrc) in Hsrc_none.
        rewrite Hnone in Hsrc_none; discriminate.
    + pose proof (Hunfold p) as Huf_end; cbn in Huf_end.
      destruct Huf_end as [Hnonebase | [Psrc [Pdst [Hsrc_end [Hbase_end Hpre_end]]]]].
      * destruct Hnonebase as [Hsrc_none _].
        change (M p = None) in Hsrc_none.
        rewrite Hlookup in Hsrc_none; discriminate.
      * change (M p = Some Psrc) in Hsrc_end.
        rewrite Hlookup in Hsrc_end.
        injection Hsrc_end as HsrcP.
        subst Psrc.
        pose proof (precongP_nonrec _ _ Hpre_end
          ltac:(intros R Hrec; discriminate Hrec)) as Hsame.
        rewrite Hsame in Hbase_end.
        rewrite Hbase_end in Hsend; discriminate.
Qed.

Lemma qt_multistep_from_ends_vector : forall (qs : quantum_state) (M : session)
  (actions : list action) (s : state) (r : R),
  (forall p, M p = None \/ exists lz, M p = Some (p_end lz)) ->
  multistep (qs, M) actions s r ->
  proj1_sig (projT2 (fst s)) = proj1_sig (projT2 qs).
Proof.
  intros qs M actions s r Hends Hmulti.
  dependent induction Hmulti.
  - reflexivity.
  - exfalso.
    destruct s2 as [qs2 M2].
    exact (qt_step_no_from_ends qs M a qs2 M2 r1 Hends H).
Qed.
Opaque base_to_ucom.

Lemma qt_teleportation_branch_core :
  forall
    (starting_qstate : quantum_state)
    (end_state : state)
    (actions : list action)
    (Hstarting_length : length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))) = 1)
    (x y : bool)
    (s'' : state)
    (H5 : ` (projT2 s''.1) = ` (projT2 end_state.1))
    (v'0 : qubit_reference)
    (H2 : (` (projT1 starting_qstate)) v'0 = Some (Env, 0))
    (la0 : list action)
    (s0 : session)
    (v' : qubit_reference)
    (Hfresh : ~ In v' (map fst (elems qubit_reference (participant * fin) (` (projT1 starting_qstate)))))
    (s : session)
    (s2 : session)
    (v'2 : qubit_reference)
    (Hfresh0 : ~ In v'2 (map fst (elems qubit_reference (participant * fin) (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))))))))
    (s1 : session)
    (s''0 : state)
    (H4 : finished s''0.2)
    (H19 : ` (projT2 s''0.1) = ` (projT2 s''.1))
    (la : list action)
    (q0 : quantum_state)
    (s4 : session)
    (s3 : session)
    (lq : list qubit_reference)
    (Hlen : length lq = 1)
    (Hdim : 1 > 0)
    (H32 : apply_unitary (insert (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))))) v'2 (Source, length (elems qubit_reference (participant * fin) (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate)))))))) (Primitives.add_new_qubit_obligation_1 (add_new_qubit starting_qstate Source v' Hfresh) Source v'2 Hfresh0) (@kron (2 ^ (length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))) + 1)) 1 2 1 (@kron (2 ^ length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate)))) 1 2 1 (` (projT2 starting_qstate)) ∣0⟩) ∣0⟩) (Primitives.add_new_qubit_obligation_2 (add_new_qubit starting_qstate Source v' Hfresh) Source v'2 Hfresh0) U_H lq Hlen Hdim = Some q0)
    (H31 : [Val (QVal v')] = map (fun z : qubit_reference => Val (QVal z)) lq)
    (H34 : NoDup lq)
    (H35 : Forall (fun q : qubit_reference => exists n : fin, insert (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))))) v'2 (Source, length (elems qubit_reference (participant * fin) (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))))))) q = Some (Source, n)) lq)
    (q3 : quantum_state)
    (s6 : session)
    (s5 : session)
    (lq0 : list qubit_reference)
    (Hlen0 : length lq0 = 2)
    (Hdim0 : 2 > 0)
    (H : List.cons (Val (QVal v')) (List.cons (Val (QVal v'2)) List.nil) = map (fun z : qubit_reference => Val (QVal z)) lq0)
    (H38 : apply_unitary (` (projT1 q0)) (proj2_sig (projT1 q0)) (` (projT2 q0)) (proj2_sig (projT2 q0)) U_CNOT lq0 Hlen0 Hdim0 = Some q3)
    (H39 : NoDup lq0)
    (H40 : Forall (fun q : qubit_reference => exists n : fin, (` (projT1 q0)) q = Some (Source, n)) lq0)
    (s8 : session)
    (old : participant)
    (n : fin)
    (Hlookup : (` (projT1 q3)) v' = Some (old, n))
    (s7 : session)
    (s10 : session)
    (old0 : participant)
    (n0 : fin)
    (Hlookup0 : insert (` (projT1 q3)) v' (Alice, n) v'0 = Some (old0, n0))
    (s9 : session)
    (q : quantum_state)
    (s11 : session)
    (lq1 : list qubit_reference)
    (Hlen1 : length lq1 = 2)
    (Hdim1 : 2 > 0)
    (H37 : List.cons (Val (QVal v'0)) (List.cons (Val (QVal v')) List.nil) = map (fun z : qubit_reference => Val (QVal z)) lq1)
    (H42 : apply_unitary (insert (insert (` (projT1 q3)) v' (Alice, n)) v'0 (Alice, n0)) (Primitives.transfer_qubit_obligation_2 (insert (` (projT1 q3)) v' (Alice, n)) (Primitives.transfer_qubit_obligation_2 (` (projT1 q3)) (proj2_sig (projT1 q3)) Alice v' old n (eq_sym Hlookup)) Alice v'0 old0 n0 (eq_sym Hlookup0)) (` (projT2 q3)) (Primitives.transfer_qubit_obligation_3 (insert (` (projT1 q3)) v' (Alice, n)) (Primitives.transfer_qubit_obligation_2 (` (projT1 q3)) (proj2_sig (projT1 q3)) Alice v' old n (eq_sym Hlookup)) (` (projT2 q3)) (Primitives.transfer_qubit_obligation_3 (` (projT1 q3)) (proj2_sig (projT1 q3)) (` (projT2 q3)) (proj2_sig (projT2 q3)) Alice v' old n (eq_sym Hlookup)) Alice v'0 old0 n0 (eq_sym Hlookup0)) U_CNOT lq1 Hlen1 Hdim1 = Some q)
    (H55 : NoDup lq1)
    (H56 : Forall (fun q : qubit_reference => exists n1 : fin, insert (insert (` (projT1 q3)) v' (Alice, n)) v'0 (Alice, n0) q = Some (Alice, n1)) lq1)
    (q1 : quantum_state)
    (s12 : session)
    (lq2 : list qubit_reference)
    (Hlen2 : length lq2 = 1)
    (Hdim2 : 1 > 0)
    (H47 : [Val (QVal v'0)] = map (fun z : qubit_reference => Val (QVal z)) lq2)
    (H58 : apply_unitary (` (projT1 q)) (proj2_sig (projT1 q)) (` (projT2 q)) (proj2_sig (projT2 q)) U_H lq2 Hlen2 Hdim2 = Some q1)
    (H60 : NoDup lq2)
    (H61 : Forall (fun q0 : qubit_reference => exists n : fin, (` (projT1 q)) q0 = Some (Alice, n)) lq2)
    (q4 : quantum_state)
    (s13 : session)
    (pi1 : R)
    (q5 : qubit_reference)
    (n1 : fin)
    (Hprob : {prob : R | (prob > 0)%R})
    (Hlookup1 : (` (projT1 q1)) q5 = Some (Alice, n1))
    (Hlen3 : 0 < length (elems qubit_reference (participant * fin) (` (projT1 q1))))
    (Hnonzero : norm (proj n1 (length (elems qubit_reference (participant * fin) (` (projT1 q1)))) x × ` (projT2 q1)) <> 0%R)
    (H59 : Val (QVal v'0) = Val (QVal q5))
    (H63 : (Hprob, q4) = measure_qubit_from_nonzero (` (projT1 q1)) (proj2_sig (projT1 q1)) (` (projT2 q1)) (proj2_sig (projT2 q1)) q5 Alice n1 x Hlookup1 Hlen3 Hnonzero)
    (q6 : quantum_state)
    (s14 : session)
    (pi0 : R)
    (q7 : qubit_reference)
    (n2 : fin)
    (Hprob0 : {prob : R | (prob > 0)%R})
    (Hlookup2 : (` (projT1 q4)) q7 = Some (Alice, n2))
    (Hlen4 : 0 < length (elems qubit_reference (participant * fin) (` (projT1 q4))))
    (Hnonzero0 : norm (proj n2 (length (elems qubit_reference (participant * fin) (` (projT1 q4)))) y × ` (projT2 q4)) <> 0%R)
    (H64 : Val (QVal v') = Val (QVal q7))
    (H66 : (Hprob0, q6) = measure_qubit_from_nonzero (` (projT1 q4)) (proj2_sig (projT1 q4)) (` (projT2 q4)) (proj2_sig (projT2 q4)) q7 Alice n2 y Hlookup2 Hlen4 Hnonzero0)
    (s16 : session)
    (old1 : participant)
    (n3 : fin)
    (Hlookup3 : (` (projT1 q6)) v'2 = Some (old1, n3))
    (s15 : session)
    (s18 : session)
    (s17 : session)
    (s20 : session)
    (s19 : session)
    (s22 : session)
    (s21 : session)
    (s24 : session)
    (s23 : session)
    (u : base_Unitary 1)
    (q2 : quantum_state)
    (s26 : session)
    (s25 : session)
    (lq3 : list qubit_reference)
    (Hlen5 : length lq3 = 1)
    (Hdim3 : 1 > 0)
    (H98 : apply_unitary (insert (` (projT1 q6)) v'2 (Bob, n3)) (Primitives.transfer_qubit_obligation_2 (` (projT1 q6)) (proj2_sig (projT1 q6)) Bob v'2 old1 n3 (eq_sym Hlookup3)) (` (projT2 q6)) (Primitives.transfer_qubit_obligation_3 (` (projT1 q6)) (proj2_sig (projT1 q6)) (` (projT2 q6)) (proj2_sig (projT2 q6)) Bob v'2 old1 n3 (eq_sym Hlookup3)) u lq3 Hlen5 Hdim3 = Some q2)
    (H88 : [Val (QVal v'2)] = map (fun z : qubit_reference => Val (QVal z)) lq3)
    (H99 : NoDup lq3)
    (H100 : Forall (fun q : qubit_reference => exists n : fin, insert (` (projT1 q6)) v'2 (Bob, n3) q = Some (Bob, n)) lq3)
    (qout : quantum_state)
    (Houtmap : proj1_sig (projT1 qout) = insert (` (projT1 q6)) v'2 (Bob,n3))
    (Houtvec : forall
      (Hq6len : length (elems qubit_reference (participant * fin) (` (projT1 q6))) = 1)
      (Houtlen : length (elems qubit_reference (participant * fin) (` (projT1 qout))) = 1),
      transport_state_vector Houtlen (proj1_sig (projT2 qout)) =
        @Mmult 2 2 1 (QTPathHelperDefinitions.qt_correction x y)
          (transport_state_vector Hq6len (proj1_sig (projT2 q6))))
    (s28 : session)
    (r2 : R)
    (old2 : participant)
    (n4 : fin)
    (Hlookup4 : (` (projT1 qout)) v'2 = Some (old2, n4))
    (s27 : session)
    (H101 : multistep (transfer_qubit_from_lookup (` (projT1 qout)) (proj2_sig (projT1 qout)) (` (projT2 qout)) (proj2_sig (projT2 qout)) Env v'2 old2 n4 Hlookup4, insert (insert (insert (insert (insert (insert empty_fmap Env (p_recv Bob (slist_x (p_end [Process.Var 0])))) Source (p_end [])) Alice (p_end [])) Bob ((Env) .+ l_Env_B <. Val (QVal v'2) .>; (p_end []))) Env (p_end [Val (QVal v'2)])) Bob (p_end [])) la s''0 r2),
    proj1_sig (projT2 (fst end_state)) = proj1_sig (projT2 starting_qstate).
Proof.
  intros.
  destruct q0 as [qm_sig qv_sig].
  destruct qm_sig as [qmap0 Hqmap0].
  destruct qv_sig as [qvec0 Hqvec0].
  pose proof H32 as H32map.
  apply Happly_map in H32map.
  cbn in H32map.
  subst qmap0.
  pose proof H32 as H32vec.
  apply Hresult_vector in H32vec.
  destruct H32vec as [lp0 [Hget0 [Hidx0 Hq0vec]]].
  assert (Hv_v0 : v' <> v'0).
  { intro Heq; subst v'; apply Hfresh.
    apply In_fst_map with (ab := (v'0, (Env, 0))).
    apply (proj2 (specs qubit_reference (participant * fin) (` (projT1 starting_qstate)))); exact H2. }
  assert (Hv_v2 : v' <> v'2).
  { intro Heq; subst v'2; apply Hfresh0.
    apply In_fst_map with (ab := (v', (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate)))))).
    apply replace_or_add_In_eq. }
  apply qgt_qubit_list_singleton in H31; subst lq.
  rewrite Forall_forall in H35.
  specialize (H35 v' ltac:(simpl; auto)).
  destruct H35 as [nsource Hlookup_add].
  pose proof Hlookup_add as Hlookup_add_orig.
  rewrite insert_neq in Hlookup_add by congruence.
  rewrite insert_eq in Hlookup_add.
  rewrite Hstarting_length in Hlookup_add.
  inversion Hlookup_add; subst nsource.
  Transparent insert.
  assert (Haddlen1 : length (elems qubit_reference (participant * fin)
    (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate)))))) = 2).
  { unfold insert; simpl. rewrite replace_or_add_not_In_length.
    - rewrite Hstarting_length; reflexivity.
    - intros b Hin; apply Hfresh. apply In_fst_map with (ab := (v',b)); exact Hin. }
  assert (Haddlen2 : length (elems qubit_reference (participant * fin)
    (insert (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate)))))
      v'2 (Source, length (elems qubit_reference (participant * fin) (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))))))))) = 3).
  { unfold insert; simpl. rewrite replace_or_add_not_In_length.
    - rewrite replace_or_add_not_In_length.
      + rewrite Hstarting_length; reflexivity.
      + intros b Hin; apply Hfresh. apply In_fst_map with (ab := (v',b)); exact Hin.
    - intros b Hin; apply Hfresh0. apply In_fst_map with (ab := (v'2,b)); exact Hin. }
  assert (Hlp0 : lp0 = [(Source,1)]).
  { eapply qgt_get_all_values_singleton; [exact Hget0|exact Hlookup_add_orig]. }
  assert (Hmapidx0 : map snd lp0 = [1]) by (rewrite Hlp0; reflexivity).
  set (qmstart := (` (projT1 starting_qstate))).
  set (qm1 := insert qmstart v' (Source,
    length (elems qubit_reference (participant * fin) qmstart))).
  set (qmadd := insert qm1 v'2 (Source,
    length (elems qubit_reference (participant * fin) qm1))).
  assert (HidxOneBase : length [1] = 1 /\ NoDup [1] /\ Forall (fun i : nat => (i < 3)%nat) [1]).
  { split; [reflexivity|]. split.
    - constructor; [simpl; tauto|constructor].
    - constructor; [simpl; lia|constructor]. }
  assert (HidxOne : length [1] = 1 /\ NoDup [1] /\ Forall
    (fun i : nat => (i < length (elems qubit_reference (participant * fin) qmadd))%nat) [1]).
  { unfold qmadd, qm1, qmstart; rewrite Haddlen2; exact HidxOneBase. }
  pose proof (@QTPathHelperDefinitions.qt_base_to_ucom_ext
    (length (elems qubit_reference (participant * fin) qmadd)) 1 U_H
    (map snd lp0) [1] Hidx0 HidxOne Hmapidx0) as Hu0.
  unfold qmadd, qm1, qmstart in Hu0.
  match type of Hq0vec with
  | _ = @Mmult ?d ?d 1 _ ?input =>
      let f := constr:(fun op : Matrix d d => @Mmult d d 1 op input) in
      pose proof (f_equal f Hu0) as Hu0app
  end.
  pose proof (eq_trans Hq0vec Hu0app) as Hq0canonical.
  Opaque insert.
  Transparent U_H base_to_ucom ueval_r.
  unfold U_H in Hq0canonical.
  cbn [base_to_ucom uc_eval ueval_r] in Hq0canonical.
  simpl in Hq0canonical.
  rewrite hadamard_rotation in Hq0canonical.
  assert (HstartPlus : (length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))) + 2 = 3)%nat).
  { rewrite Hstarting_length; reflexivity. }
  assert (Hdim_start : length (elems qubit_reference (participant * fin) qmadd) =
    length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))) + 2).
  { unfold qmadd; exact (eq_trans Haddlen2 (eq_sym HstartPlus)). }
  match type of Hq0canonical with
  | _ = @Mmult ?d ?d 1 (pad_u ?n 1 hadamard) ?raw =>
      pose proof (@QTPathHelperDefinitions.qt_transport_pad_u n 3 Haddlen2 1 hadamard raw) as Hpad0
  end.
  pose proof (f_equal (transport_state_vector Haddlen2) Hq0canonical) as Hq0canonical3.
  pose proof (eq_trans Hq0canonical3 Hpad0) as Hq0canonicalPad.
  match type of Hq0canonical with
  | _ = @Mmult ?d ?d 1 (pad_u ?n 1 hadamard) ?raw =>
      pose proof (@QTPathHelperDefinitions.qt_transport_state_vector_compose
        n (length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))) + 2)
        3 Hdim_start HstartPlus raw) as Hinputcomp
  end.
  assert (Hdim_comp : eq_trans Hdim_start HstartPlus = Haddlen2) by apply proof_irrelevance.
  match type of Hinputcomp with
  | transport_state_vector (eq_trans Hdim_start HstartPlus) ?raw =
      transport_state_vector HstartPlus (transport_state_vector Hdim_start ?raw) =>
      pose proof (f_equal (fun e => transport_state_vector e raw) Hdim_comp) as Hcompcast;
      pose proof (@FunctionalCorrectnessHelpers.transport_state_vector_value
        _ _ Hdim_start raw) as Hrawdim;
      pose proof (f_equal (transport_state_vector HstartPlus) Hrawdim) as Hrawdim2;
      pose proof (eq_trans (eq_sym Hcompcast) (eq_trans Hinputcomp Hrawdim2)) as Hinputdim
  end.
  pose proof (f_equal (fun x : Matrix 8 1 =>
    @Mmult 8 8 1 (pad_u 3 1 hadamard) x) Hinputdim) as Hinputdimapp.
  pose proof (eq_trans Hq0canonicalPad Hinputdimapp) as Hq0factorpre.
  pose proof (@QTPathHelperDefinitions.qt_append_zeros_transport
    (length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate)))) 3
    Hstarting_length HstartPlus (` (projT2 starting_qstate))
    (proj2_sig (projT2 starting_qstate))) as Happend.
  pose proof (f_equal (fun x : Matrix 8 1 =>
    @Mmult 8 8 1 (pad_u 3 1 hadamard) x) Happend) as Happendapp.
  pose proof (eq_trans Hq0factorpre Happendapp) as Hq0factor.
  pose proof H38 as H38map.
  eapply Happly_map in H38map.
  cbn in H38map.
  pose proof H38 as H38vec.
  eapply Hresult_vector in H38vec.
  destruct H38vec as [lp38 [Hget38 [Hidx38 Hq3vec]]].
  apply qgt_qubit_list_pair in H; subst lq0.
  pose proof H40 as H40forall.
  rewrite Forall_forall in H40forall.
  specialize (H40forall v' ltac:(simpl; auto)).
  destruct H40forall as [idxv Hq0v].
  pose proof Hq0v as Hq0vlookup.
  cbn in Hq0v.
  rewrite insert_neq in Hq0v by congruence.
  rewrite insert_eq in Hq0v.
  rewrite Hstarting_length in Hq0v.
  inversion Hq0v; subst idxv.
  pose proof H40 as H40forall2.
  rewrite Forall_forall in H40forall2.
  specialize (H40forall2 v'2 ltac:(simpl; auto)).
  destruct H40forall2 as [idxv2 Hq0v2].
  pose proof Hq0v2 as Hq0v2lookup.
  cbn in Hq0v2.
  rewrite insert_eq in Hq0v2.
  injection Hq0v2 as Hidxv2.
  assert (Hleninner : length (elems qubit_reference (participant * fin)
    (insert (` (projT1 starting_qstate)) v'
      (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate)))))) = 2).
  { exact Haddlen1. }
  assert (Hidxv2_2 : idxv2 = 2).
  { exact (eq_trans (eq_sym Hidxv2) Hleninner). }
  subst idxv2.
    assert (Hq0v2_concrete : qmadd v'2 = Some (Source,2)).
  { unfold qmadd, qm1, qmstart; rewrite insert_eq, Hleninner; reflexivity. }
  assert (Hlp38 : lp38 = List.cons (Source,1) (List.cons (Source,2) nil)).
  { eapply qgt_get_all_values_pair; [exact Hget38|exact Hq0vlookup|exact Hq0v2_concrete]. }
  assert (Hidx12 : length (List.cons 1 (List.cons 2 nil)) = 2 /\
    NoDup (List.cons 1 (List.cons 2 nil)) /\
    Forall (fun i : nat => (i < length (elems qubit_reference (participant * fin) qmadd))%nat)
      (List.cons 1 (List.cons 2 nil))).
  { unfold qmadd, qm1, qmstart; rewrite Haddlen2; split; [reflexivity|]. split.
    - repeat constructor; simpl; intuition congruence.
    - repeat constructor; simpl; lia. }
  assert (Hmapidx38 : map snd lp38 = List.cons 1 (List.cons 2 nil)).
  { rewrite Hlp38; reflexivity. }
  pose proof (@QTPathHelperDefinitions.qt_base_to_ucom_ext
    (length (elems qubit_reference (participant * fin) qmadd)) 2 U_CNOT
    (map snd lp38) (List.cons 1 (List.cons 2 nil))
    Hidx38 Hidx12 Hmapidx38) as Hcnotext.
  assert (Hbasecnot :
    uc_eval (` (base_to_ucom U_CNOT (List.cons 1 (List.cons 2 nil)) Hidx12)) =
    pad_ctrl (length (elems qubit_reference (participant * fin) qmadd)) 1 2 σx).
  { Transparent base_to_ucom ueval_r.
    cbn [base_to_ucom uc_eval ueval_r]; reflexivity. }
  pose proof (f_equal (transport_state_vector Haddlen2) Hq3vec) as Hq3vec_cast.
  pose proof (f_equal (fun op : Matrix (2 ^ length (elems qubit_reference (participant * fin) qmadd))
      (2 ^ length (elems qubit_reference (participant * fin) qmadd)) =>
      @Mmult (2 ^ length (elems qubit_reference (participant * fin) qmadd))
        (2 ^ length (elems qubit_reference (participant * fin) qmadd)) 1 op qvec0) Hcnotext) as Hcnotapp.
  pose proof (f_equal (transport_state_vector Haddlen2) Hcnotapp) as Hcnotappcast.
  pose proof (eq_trans Hq3vec_cast Hcnotappcast) as Hq3vec_cast1.
  pose proof (f_equal (fun op : Matrix (2 ^ length (elems qubit_reference (participant * fin) qmadd))
      (2 ^ length (elems qubit_reference (participant * fin) qmadd)) =>
      @Mmult (2 ^ length (elems qubit_reference (participant * fin) qmadd))
        (2 ^ length (elems qubit_reference (participant * fin) qmadd)) 1 op qvec0) Hbasecnot) as Hbasecnotapp.
  pose proof (f_equal (transport_state_vector Haddlen2) Hbasecnotapp) as Hbasecnotappcast.
  pose proof (eq_trans Hq3vec_cast1 Hbasecnotappcast) as Hq3vec_cast2.
  pose proof (@QTPathHelperDefinitions.qt_transport_pad_ctrl
    (length (elems qubit_reference (participant * fin) qmadd)) 3 Haddlen2
    1 2 σx qvec0) as Hctrlcast.
  pose proof (eq_trans Hq3vec_cast2 Hctrlcast) as Hq3vec_cast3.
  pose proof (f_equal (fun x : Matrix 8 1 =>
    @Mmult 8 8 1 (pad_ctrl 3 1 2 σx) x) Hq0factor) as Hq0ctrl.
  pose proof (eq_trans Hq3vec_cast3 Hq0ctrl) as Hq3_vector0.
  assert (Hq3_vector :
    transport_state_vector Haddlen2 (` (projT2 q3)) =
      QTPathHelperDefinitions.qt_epr_preparation ×
        transport_state_vector Hstarting_length (` (projT2 starting_qstate))).
  { unfold QTPathHelperDefinitions.qt_epr_preparation.
    repeat rewrite <- Mmult_assoc in Hq3_vector0.
    exact Hq3_vector0. }
  assert (Hv2v0 : v'2 <> v'0).
  { intro Heq; subst v'2; apply Hfresh0.
    apply In_fst_map with (ab := (v'0, (Env, 0))).
    apply replace_or_add_In_neq.
    - intro Heq; apply Hv_v0; symmetry; exact Heq.
    - apply (proj2 (specs qubit_reference (participant * fin)
        (` (projT1 starting_qstate)))); exact H2. }
  assert (Hq3v : (` (projT1 q3)) v' = Some (Source,1)).
  { rewrite H38map; exact Hq0vlookup. }
  assert (Hq3v0 : (` (projT1 q3)) v'0 = Some (Env,0)).
  { rewrite H38map; cbn.
    rewrite insert_neq by exact Hv2v0.
    rewrite insert_neq by exact Hv_v0.
    exact H2. }
  pose proof Hlookup as Hlookup_copy.
  rewrite Hq3v in Hlookup_copy.
  injection Hlookup_copy as HownerEq HnEq.
  symmetry in HownerEq, HnEq.
  pose proof Hlookup0 as Hlookup0_copy.
  rewrite insert_neq in Hlookup0_copy by congruence.
  rewrite Hq3v0 in Hlookup0_copy.
  injection Hlookup0_copy as Howner0Eq Hn0Eq.
  symmetry in Howner0Eq, Hn0Eq.
  assert (Hq3len : length (elems qubit_reference (participant * fin) (` (projT1 q3))) = 3).
  { rewrite H38map; exact Haddlen2. }
  assert (HlenA1 : length (elems qubit_reference (participant * fin)
    (insert (` (projT1 q3)) v' (Alice,n))) =
    length (elems qubit_reference (participant * fin) (` (projT1 q3)))).
  { eapply qgt_insert_preserves_length; exact Hlookup. }
  assert (HlenA2 : length (elems qubit_reference (participant * fin)
    (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0))) =
    length (elems qubit_reference (participant * fin)
      (insert (` (projT1 q3)) v' (Alice,n)))).
  { eapply qgt_insert_preserves_length; exact Hlookup0. }
  assert (HlenA : length (elems qubit_reference (participant * fin)
    (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0))) = 3).
  { rewrite HlenA2, HlenA1, Hq3len; reflexivity. }
  assert (HqA_v'0 :
    (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0)) v'0 = Some (Alice,0)).
  { rewrite insert_eq, Hn0Eq; reflexivity. }
  assert (HqA_v' :
    (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0)) v' = Some (Alice,1)).
  { rewrite insert_neq by congruence.
    rewrite insert_eq, HnEq; reflexivity. }
  apply qgt_qubit_list_pair in H37; subst lq1.
  destruct q as [qmsig qvsig].
  destruct qmsig as [qmapA HqmapA].
  destruct qvsig as [qvecA HqvecA].
  pose proof H42 as H42map.
  eapply Happly_map in H42map.
  cbn in H42map.
  subst qmapA.
  pose proof H42 as H42vec.
  eapply Hresult_vector in H42vec.
  destruct H42vec as [lp42 [Hget42 [Hidx42 Hqvec42]]].
  assert (Hlp42 : lp42 = List.cons (Alice,0) (List.cons (Alice,1) nil)).
  { eapply qgt_get_all_values_pair; [exact Hget42|exact HqA_v'0|exact HqA_v']. }
  assert (Hidx01 : length (List.cons 0 (List.cons 1 nil)) = 2 /\
    NoDup (List.cons 0 (List.cons 1 nil)) /\
    Forall (fun i : nat => (i < length (elems qubit_reference (participant * fin)
      (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0))))%nat)
      (List.cons 0 (List.cons 1 nil))).
  { rewrite HlenA; split; [reflexivity|]. split.
    - repeat constructor; simpl; intuition congruence.
    - repeat constructor; simpl; lia. }
  assert (Hmapidx42 : map snd lp42 = List.cons 0 (List.cons 1 nil)).
  { rewrite Hlp42; reflexivity. }
  pose proof (@QTPathHelperDefinitions.qt_base_to_ucom_ext
    (length (elems qubit_reference (participant * fin)
      (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0)))) 2 U_CNOT
    (map snd lp42) (List.cons 0 (List.cons 1 nil)) Hidx42 Hidx01 Hmapidx42)
    as Hcnotext42.
  assert (Hbasecnot42 :
    uc_eval (` (base_to_ucom U_CNOT (List.cons 0 (List.cons 1 nil)) Hidx01)) =
    pad_ctrl (length (elems qubit_reference (participant * fin)
      (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0)))) 0 1 σx).
  { cbn [base_to_ucom uc_eval ueval_r]; reflexivity. }
  match type of Hqvec42 with
  | _ = @Mmult ?d ?d 1 ?op ?raw =>
      pose proof (f_equal (fun u : Matrix d d => @Mmult d d 1 u raw) Hcnotext42) as Hcnotapp42;
      pose proof (f_equal (fun u : Matrix d d => @Mmult d d 1 u raw) Hbasecnot42) as Hbaseapp42;
      pose proof (f_equal (transport_state_vector HlenA) Hqvec42) as Hq42cast;
      pose proof (f_equal (transport_state_vector HlenA) Hcnotapp42) as Hcnotapp42cast;
      pose proof (eq_trans Hq42cast Hcnotapp42cast) as Hq42cast1;
      pose proof (f_equal (transport_state_vector HlenA) Hbaseapp42) as Hbaseapp42cast;
      pose proof (eq_trans Hq42cast1 Hbaseapp42cast) as Hq42cast2;
      pose proof (@QTPathHelperDefinitions.qt_transport_pad_ctrl
        (length (elems qubit_reference (participant * fin)
          (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0))))
        3 HlenA 0 1 σx raw) as Hctrl42cast;
      pose proof (eq_trans Hq42cast2 Hctrl42cast) as Hq42cast3
  end.
  assert (Hq3_casts :
    transport_state_vector HlenA (` (projT2 q3)) =
    transport_state_vector Haddlen2 (` (projT2 q3))).
  { transitivity (` (projT2 q3)).
    - apply FunctionalCorrectnessHelpers.transport_state_vector_value.
    - symmetry; apply FunctionalCorrectnessHelpers.transport_state_vector_value. }
  pose proof (f_equal (fun x : Matrix 8 1 =>
    @Mmult 8 8 1 (pad_ctrl 3 0 1 σx) x) Hq3_casts) as Hq3cnot.
  pose proof (eq_trans Hq42cast3 Hq3cnot) as Hq_after_cnot.
  destruct q1 as [q1msig q1vsig].
  destruct q1msig as [qmap1 Hqmap1].
  destruct q1vsig as [qvec1 Hqvec1].
  pose proof H58 as H58map.
  eapply Happly_map in H58map.
  cbn in H58map.
  subst qmap1.
  apply qgt_qubit_list_singleton in H47; subst lq2.
  pose proof H58 as H58vec.
  eapply Hresult_vector in H58vec.
  destruct H58vec as [lp58 [Hget58 [Hidx58 Hq1vec]]].
  assert (Hlp58 : lp58 = [(Alice,0)]).
  { eapply qgt_get_all_values_singleton; [exact Hget58|exact HqA_v'0]. }
  assert (HidxHad0 : length [0] = 1 /\ NoDup [0] /\
    Forall (fun i : nat => (i < length (elems qubit_reference (participant * fin)
      (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0))))%nat) [0]).
  { rewrite HlenA; simpl; split; [reflexivity|]. split.
    - constructor; [simpl; tauto|constructor].
    - constructor; [simpl; lia|constructor]. }
  assert (Hmapidx58 : map snd lp58 = [0]).
  { rewrite Hlp58; reflexivity. }
  pose proof (@QTPathHelperDefinitions.qt_base_to_ucom_ext
    (length (elems qubit_reference (participant * fin)
      (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0)))) 1 U_H
    (map snd lp58) [0] Hidx58 HidxHad0 Hmapidx58) as Hhadext.
  assert (Hbasehad0 :
    uc_eval (` (base_to_ucom U_H [0] HidxHad0)) =
      pad_u (length (elems qubit_reference (participant * fin)
        (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0)))) 0 hadamard).
  { Transparent U_H base_to_ucom ueval_r.
    unfold U_H.
    cbn [base_to_ucom uc_eval ueval_r].
    simpl.
    rewrite hadamard_rotation.
    reflexivity. }
  match type of Hq1vec with
  | _ = @Mmult ?d ?d 1 ?op ?raw =>
      pose proof (f_equal (fun u : Matrix d d => @Mmult d d 1 u raw) Hhadext) as Hhadapp;
      pose proof (f_equal (fun u : Matrix d d => @Mmult d d 1 u raw) Hbasehad0) as Hbasehadapp;
      pose proof (f_equal (transport_state_vector HlenA) Hq1vec) as Hq1cast;
      pose proof (f_equal (transport_state_vector HlenA) Hhadapp) as Hhadappcast;
      pose proof (eq_trans Hq1cast Hhadappcast) as Hq1cast1;
      pose proof (f_equal (transport_state_vector HlenA) Hbasehadapp) as Hbasehadappcast;
      pose proof (eq_trans Hq1cast1 Hbasehadappcast) as Hq1cast2;
      pose proof (@QTPathHelperDefinitions.qt_transport_pad_u
        (length (elems qubit_reference (participant * fin)
          (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0))))
        3 HlenA 0 hadamard raw) as Hhadcast;
      pose proof (eq_trans Hq1cast2 Hhadcast) as Hq1cast3
  end.
  pose proof (f_equal (fun x : Matrix 8 1 =>
    @Mmult 8 8 1 (pad_u 3 0 hadamard) x) Hq_after_cnot) as Hq_cnot_h.
  pose proof (eq_trans Hq1cast3 Hq_cnot_h) as Hpre0.
  repeat rewrite <- Mmult_assoc in Hpre0.
  pose proof (f_equal (fun x : Matrix 8 1 =>
    @Mmult 8 8 1 (pad_u 3 0 hadamard × pad_ctrl 3 0 1 σx) x)
    Hq3_vector) as Hpreappend.
  pose proof (eq_trans Hpre0 Hpreappend) as Hpre1.
  assert (Hpre :
    transport_state_vector HlenA qvec1 =
      QTPathHelperDefinitions.qt_alice_pre_measure ×
        (QTPathHelperDefinitions.qt_epr_preparation ×
          transport_state_vector Hstarting_length (` (projT2 starting_qstate)))).
  { unfold QTPathHelperDefinitions.qt_alice_pre_measure.
    exact Hpre1. }
  injection H63 as Hprob_eq Hq4eq.
  subst q4.
  assert (Hq5id : q5 = v'0).
  { injection H59 as Heq; symmetry; exact Heq. }
  assert (Hn1eq : n1 = 0).
  { pose proof Hlookup1 as Hlookup1_copy.
    change ((insert (insert (` (projT1 q3)) v' (Alice,n)) v'0
      (Alice,n0)) q5 = Some (Alice,n1)) in Hlookup1_copy.
    rewrite Hq5id in Hlookup1_copy.
    rewrite HqA_v'0 in Hlookup1_copy.
    inversion Hlookup1_copy; reflexivity. }
  pose proof (@measure_qubit_nonzero_map
    (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0))
    Hqmap1 qvec1 Hqvec1 q5 Alice n1 x Hlookup1 Hlen3 Hnonzero)
    as Hmap_measure1.
  pose proof (@remove_and_reindex_qubit_map_length
    (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0))
    q5 Alice n1 Hlookup1) as Hremoved_len1.
  assert (Houtdim1 : length (elems qubit_reference (participant * fin)
      (proj1_sig (projT1 (snd (measure_qubit_nonzero
        (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0))
        Hqmap1 qvec1 Hqvec1 q5 Alice n1 x Hlookup1 Hlen3 Hnonzero))))) = 2).
  { rewrite Hmap_measure1.
    transitivity (Nat.pred (length (elems qubit_reference (participant * fin)
      (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0))))).
    - exact Hremoved_len1.
    - rewrite HlenA; reflexivity. }
  set (input := transport_state_vector Hstarting_length (` (projT2 starting_qstate))).
  set (pre := @Mmult 8 8 1 QTPathHelperDefinitions.qt_alice_pre_measure
    (@Mmult 8 2 1 QTPathHelperDefinitions.qt_epr_preparation input)).
  assert (Hinputwf : @state_vector_wf 1 input).
  { unfold input; apply transport_state_vector_wf; exact (proj2_sig (projT2 starting_qstate)). }
  assert (Hprewf : @WF_Matrix 8 1 pre).
  {
    pose proof (@transport_state_vector_wf
      (length (elems qubit_reference (participant * fin)
        (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0))))
      3 HlenA qvec1 Hqvec1) as Hq1wf.
    rewrite Hpre in Hq1wf.
    unfold pre.
    exact (proj1 Hq1wf).
  }
  set (m1 := transport_state_vector Houtdim1
    (proj1_sig (projT2 (snd (measure_qubit_nonzero
      (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0))
      Hqmap1 qvec1 Hqvec1 q5 Alice n1 x Hlookup1 Hlen3 Hnonzero))))).
  set (q4_state := snd (measure_qubit_from_nonzero
    (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0))
    Hqmap1 qvec1 Hqvec1 q5 Alice n1 x Hlookup1 Hlen3 Hnonzero)).
  assert (Houtdim1_q4 : length (elems qubit_reference (participant * fin)
      (` (projT1 q4_state))) = 2).
  { unfold q4_state; exact Houtdim1. }
  assert (Hq4vec_m1 : transport_state_vector Houtdim1_q4 (` (projT2 q4_state)) = m1).
  { unfold m1, q4_state; f_equal; apply proof_irrelevance. }
  pose proof (@qt_measure_output_vector_fixed 2
    (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0))
    Hqmap1 qvec1 Hqvec1 q5 Alice n1 x Hlookup1 Hlen3 Hnonzero HlenA
    Houtdim1) as Hm1.
  unfold m1 in Hm1.
  assert (Hm1canonical : m1 = @normalize_removed_wire 2
    (@Mmult 4 8 1 (remove_measured_wire_operator 2 0 x)
      (@Mmult 8 8 1 (proj 0 3 x) pre))).
  {
    unfold m1.
    transitivity (@normalize_removed_wire 2
      (@Mmult 4 8 1 (remove_measured_wire_operator 2 n1 x)
        (@Mmult 8 8 1 (proj n1 3 x)
          (transport_state_vector HlenA qvec1)))).
    - exact Hm1.
    - f_equal; rewrite Hpre, Hn1eq; reflexivity.
  }
  assert (Hprojcast1 : transport_state_vector HlenA
      (@Mmult
        (2 ^ length (elems qubit_reference (participant * fin)
          (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0))))
        (2 ^ length (elems qubit_reference (participant * fin)
          (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0))))
        1
        (proj 0 (length (elems qubit_reference (participant * fin)
          (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0)))) x)
        qvec1) =
      @Mmult 8 8 1 (proj 0 3 x) pre).
  {
    pose proof (@transport_state_vector_proj
      (length (elems qubit_reference (participant * fin)
        (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0))))
      3 HlenA 0 x qvec1) as Hcast.
    rewrite Hpre in Hcast.
    exact Hcast.
  }
  assert (Hnonzero_pre1 : norm (@Mmult 8 8 1 (proj 0 3 x) pre) <> 0%R).
  {
    intro Hzero.
    pose proof Hnonzero as Hnonzero_raw.
    change (norm
      (proj n1 (length (elems qubit_reference (participant * fin)
        (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0))))
        x × qvec1) <> 0%R) in Hnonzero_raw.
    rewrite Hn1eq in Hnonzero_raw.
    apply Hnonzero_raw.
    rewrite <- Hprojcast1 in Hzero.
    pose proof (@transport_state_vector_norm
      (length (elems qubit_reference (participant * fin)
        (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0))))
      3 HlenA
      (@Mmult
        (2 ^ length (elems qubit_reference (participant * fin)
          (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0))))
        (2 ^ length (elems qubit_reference (participant * fin)
          (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0))))
        1
        (proj 0 (length (elems qubit_reference (participant * fin)
          (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0)))) x)
        qvec1)) as Hnorm_transport.
    exact (eq_trans (eq_sym Hnorm_transport) Hzero).
  }
  assert (Hraw1_nonzero :
    @Mmult 4 8 1 (remove_measured_wire_operator 2 0 x)
      (@Mmult 8 8 1 (proj 0 3 x) pre) <> Zero).
  { exact (@qt_remove_projected_nonzero
      2 0 x pre ltac:(lia) Hprewf Hnonzero_pre1). }
  assert (Hq7id : q7 = v').
  { injection H64 as Heq; symmetry; exact Heq. }
  assert (Hneq_q5 : v' <> q5).
  { rewrite Hq5id; exact Hv_v0. }
  assert (Hlookup2_removed :
    remove_and_reindex_qubit_map
      (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0))
      q5 n1 v' = Some (Alice,n2)).
  {
    pose proof Hlookup2 as Hlookup2_copy.
    change (remove_and_reindex_qubit_map
      (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0))
      q5 n1 q7 = Some (Alice,n2)) in Hlookup2_copy.
    rewrite Hq7id in Hlookup2_copy.
    exact Hlookup2_copy.
  }
  destruct (@Hremove_lookup_inv
    (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0))
    v' q5 n1 Alice n2 Hneq_q5 Hlookup2_removed)
    as [nold [Hlookup_v' Hshift_n2]].
  assert (Hnold1 : nold = 1).
  { rewrite HqA_v' in Hlookup_v'; inversion Hlookup_v'; reflexivity. }
  assert (Hn2eq : n2 = 0).
  { rewrite Hn1eq, Hnold1 in Hshift_n2.
    cbn [shift_wire_index] in Hshift_n2.
    exact Hshift_n2. }
  injection H66 as Hprob0_eq Hq6eq.
  subst q6.
  pose proof (@measure_qubit_nonzero_map
    (` (projT1 q4_state)) (proj2_sig (projT1 q4_state))
    (` (projT2 q4_state)) (proj2_sig (projT2 q4_state))
    q7 Alice n2 y Hlookup2 Hlen4 Hnonzero0) as Hmap_measure2.
  pose proof (@remove_and_reindex_qubit_map_length
    (` (projT1 q4_state)) q7 Alice n2 Hlookup2) as Hremoved_len2.
  assert (Houtdim2 : length (elems qubit_reference (participant * fin)
      (` (projT1 (snd (measure_qubit_nonzero
        (` (projT1 q4_state)) (proj2_sig (projT1 q4_state))
        (` (projT2 q4_state)) (proj2_sig (projT2 q4_state))
        q7 Alice n2 y Hlookup2 Hlen4 Hnonzero0))))) = 1).
  {
    rewrite Hmap_measure2.
    transitivity (Nat.pred (length (elems qubit_reference
      (participant * fin) (` (projT1 q4_state))))).
    - exact Hremoved_len2.
    - rewrite Houtdim1_q4; reflexivity.
  }
  set (q6_state := snd (measure_qubit_nonzero
    (` (projT1 q4_state)) (proj2_sig (projT1 q4_state))
    (` (projT2 q4_state)) (proj2_sig (projT2 q4_state))
    q7 Alice n2 y Hlookup2 Hlen4 Hnonzero0)).
  set (m2 := transport_state_vector Houtdim2
    (` (projT2 (snd (measure_qubit_nonzero
      (` (projT1 q4_state)) (proj2_sig (projT1 q4_state))
      (` (projT2 q4_state)) (proj2_sig (projT2 q4_state))
      q7 Alice n2 y Hlookup2 Hlen4 Hnonzero0))))).
  pose proof (@qt_measure_output_vector_fixed 1
    (` (projT1 q4_state)) (proj2_sig (projT1 q4_state))
    (` (projT2 q4_state)) (proj2_sig (projT2 q4_state))
    q7 Alice n2 y Hlookup2 Hlen4 Hnonzero0 Houtdim1_q4 Houtdim2)
    as Hm2.
  unfold m2 in Hm2.
  assert (Hm2canonical : m2 = @normalize_removed_wire 1
    (@Mmult 2 4 1 (remove_measured_wire_operator 1 0 y)
      (@Mmult 4 4 1 (proj 0 2 y) m1))).
  {
    unfold m2.
    transitivity (@normalize_removed_wire 1
      (@Mmult 2 4 1 (remove_measured_wire_operator 1 n2 y)
        (@Mmult 4 4 1 (proj n2 2 y)
          (transport_state_vector Houtdim1_q4 (` (projT2 q4_state)))))).
    - exact Hm2.
    - f_equal; rewrite Hn2eq, Hq4vec_m1; reflexivity.
  }
  assert (Hm1wf : @WF_Matrix 4 1 m1).
  {
    pose proof (@transport_state_vector_wf
      (length (elems qubit_reference (participant * fin)
      (` (projT1 q4_state)))) 2 Houtdim1_q4
      (` (projT2 q4_state)) (proj2_sig (projT2 q4_state))) as Hwf.
    rewrite <- Hq4vec_m1.
    exact (proj1 Hwf).
  }
  assert (Hnonzero_pre2 : norm (@Mmult 4 4 1 (proj 0 2 y) m1) <> 0%R).
  {
    intro Hzero.
    pose proof Hnonzero0 as Hnonzero0_raw.
    rewrite Hn2eq in Hnonzero0_raw.
    apply Hnonzero0_raw.
    pose proof (@transport_state_vector_proj
      (length (elems qubit_reference (participant * fin)
      (` (projT1 q4_state)))) 2 Houtdim1_q4 n2 y
      (` (projT2 q4_state))) as Hprojcast2.
    rewrite Hn2eq in Hprojcast2.
    rewrite <- Hq4vec_m1 in Hzero.
    pose proof (f_equal (fun z : Matrix 4 1 => @norm 4 z) Hprojcast2)
      as Hnormcast2.
    assert (Hzero_transport :
      @norm 4 (transport_state_vector Houtdim1_q4
        (@Mmult
          (2 ^ length (elems qubit_reference (participant * fin)
            (` (projT1 q4_state))))
          (2 ^ length (elems qubit_reference (participant * fin)
            (` (projT1 q4_state)))) 1
          (proj 0 (length (elems qubit_reference (participant * fin)
            (` (projT1 q4_state)))) y)
        (` (projT2 q4_state)))) = 0%R).
    { exact (eq_trans Hnormcast2 Hzero). }
    pose proof (@transport_state_vector_norm
      (length (elems qubit_reference (participant * fin)
        (` (projT1 q4_state)))) 2 Houtdim1_q4
      (@Mmult (2 ^ length (elems qubit_reference (participant * fin)
          (` (projT1 q4_state))))
        (2 ^ length (elems qubit_reference (participant * fin)
          (` (projT1 q4_state)))) 1
        (proj 0 (length (elems qubit_reference (participant * fin)
            (` (projT1 q4_state)))) y)
        (` (projT2 q4_state)))) as Hnorm_transport2.
    exact (eq_trans (eq_sym Hnorm_transport2) Hzero_transport).
  }
  assert (Hraw2_nonzero :
    @Mmult 2 4 1 (remove_measured_wire_operator 1 0 y)
      (@Mmult 4 4 1 (proj 0 2 y) m1) <> Zero).
  { exact (@qt_remove_projected_nonzero
      1 0 y m1 ltac:(lia) Hm1wf Hnonzero_pre2). }
  assert (Hraw2wf : @WF_Matrix 2 1
      (@Mmult 2 4 1 (remove_measured_wire_operator 1 0 y)
        (@Mmult 4 4 1 (proj 0 2 y) m1))).
  {
    apply WF_mult.
    - pose proof (remove_measured_wire_operator_wf 1 0 y ltac:(lia)) as Hwf.
      cbn [Nat.pow] in Hwf; exact Hwf.
    - apply WF_mult.
      + pose proof (WF_proj 0 2 y) as Hwf.
        cbn [Nat.pow] in Hwf; exact Hwf.
      + exact Hm1wf.
  }
  assert (Houtdim2_q6 : length (elems qubit_reference (participant * fin)
      (` (projT1 q6_state))) = 1).
  { unfold q6_state; exact Houtdim2. }
  assert (Hlookup3_q6 : (` (projT1 q6_state)) v'2 = Some (old1,n3)).
  { unfold q6_state; exact Hlookup3. }
  pose proof (@insert_existing_length (` (projT1 q6_state)) v'2 old1 n3 Bob
    Hlookup3_q6) as Hinsertlen.
  assert (Hleninsert : length (elems qubit_reference (participant * fin)
      (insert (` (projT1 q6_state)) v'2 (Bob,n3))) = 1).
  { transitivity (length (elems qubit_reference (participant * fin)
      (` (projT1 q6_state)))); [exact Hinsertlen|exact Houtdim2_q6]. }
  assert (Hmapqout : proj1_sig (projT1 qout) =
      insert (` (projT1 q6_state)) v'2 (Bob,n3)).
  { exact Houtmap. }
  assert (Hlenqout : length (elems qubit_reference (participant * fin)
      (` (projT1 qout))) = 1).
  { rewrite Hmapqout; exact Hleninsert. }
  set (out := transport_state_vector Hlenqout (` (projT2 qout))).
  assert (Hq6vec_m2 : ` (projT2 q6_state) = m2).
  { unfold m2; symmetry.
    exact (FunctionalCorrectnessHelpers.transport_state_vector_value
      _ _ Houtdim2 (` (projT2 q6_state))). }
  assert (Houtm2 : out = QTPathHelperDefinitions.qt_correction x y × m2).
  {
    unfold out.
    rewrite (Houtvec Houtdim2_q6 Hlenqout).
    assert (Hq6cast : transport_state_vector Houtdim2_q6 (` (projT2 q6_state)) = m2).
    {
      unfold m2.
      replace Houtdim2 with Houtdim2_q6 by apply proof_irrelevance.
      reflexivity.
    }
    apply (f_equal (fun v : Matrix 2 1 =>
      @Mmult 2 2 1 (QTPathHelperDefinitions.qt_correction x y) v)).
    exact Hq6cast.
  }
  assert (Hm2wf : @state_vector_wf 1 m2).
  {
    rewrite Hm2canonical.
    exact (@normalize_removed_wire_wf 1
      (@Mmult 2 4 1 (remove_measured_wire_operator 1 0 y)
        (@Mmult 4 4 1 (proj 0 2 y) m1)) Hraw2wf Hraw2_nonzero).
  }
  assert (Houtwf : @state_vector_wf 1 out).
  {
    unfold out.
    apply transport_state_vector_wf.
    exact (proj2_sig (projT2 qout)).
  }
  assert (Houtcanonical : out = QTPathHelperDefinitions.qt_correction x y × m2).
  { exact Houtm2. }
  pose proof (QTPathHelperDefinitions.qt_normalized_branch_exact
    input pre m1 m2 out x y Hinputwf Hprewf eq_refl Hm1canonical
    Hm1wf Hm2canonical Hraw1_nonzero Hraw2_nonzero Houtcanonical Houtwf)
    as Hbranchresult.
  assert (Hmulti_vec : ` (projT2 s''0.1) =
      proj1_sig (projT2 (transfer_qubit_from_lookup
        (` (projT1 qout)) (proj2_sig (projT1 qout))
        (` (projT2 qout)) (proj2_sig (projT2 qout))
        Env v'2 old2 n4 Hlookup4))).
  {
    assert (Htail_ends : forall p,
      qt_tail_session v'2 p = None \/
      exists lz, qt_tail_session v'2 p = Some (p_end lz)).
    { apply qt_tail_session_end_entries. }
    change (multistep
      (transfer_qubit_from_lookup (` (projT1 qout)) (proj2_sig (projT1 qout))
        (` (projT2 qout)) (proj2_sig (projT2 qout)) Env v'2 old2 n4 Hlookup4,
       qt_tail_session v'2) la s''0 r2) in H101.
    exact (qt_multistep_from_ends_vector _ _ _ _ _ Htail_ends H101).
  }
  rewrite <- H5, <- H19, Hmulti_vec.
  rewrite (@FunctionalCorrectnessHelpers.transfer_qubit_from_lookup_vector
    (` (projT1 qout)) (proj2_sig (projT1 qout))
    (` (projT2 qout)) (proj2_sig (projT2 qout))
    Env v'2 old2 n4 Hlookup4).
  assert (Houtqout : out = ` (projT2 qout)).
  { unfold out; apply FunctionalCorrectnessHelpers.transport_state_vector_value. }
  rewrite <- Houtqout, Hbranchresult.
  unfold input.
  exact (@FunctionalCorrectnessHelpers.transport_state_vector_value
    (length (elems qubit_reference (participant * fin)
      (` (projT1 starting_qstate)))) 1 Hstarting_length
    (` (projT2 starting_qstate))).
Qed.


Lemma qt_apply_one_gate_vector_same_map : forall
    (qm : finite_map qubit_reference (participant * fin))
    (Hqm : quantum_map_wf qm)
    (sv : state_vector (length (elems qubit_reference (participant * fin) qm)))
    (Hsv : state_vector_wf sv)
    (lq : list qubit_reference) (Hlen : length lq = 1) (Hdim : 1 > 0)
    (qout : quantum_state) (u : base_Unitary 1) (G : Matrix 2 2)
    (Happly : apply_unitary qm Hqm sv Hsv u lq Hlen Hdim = Some qout)
    (Houtmap : proj1_sig (projT1 qout) = qm)
    (Hqmlen : length (elems qubit_reference (participant * fin) qm) = 1)
    (Houtlen : length (elems qubit_reference (participant * fin) (` (projT1 qout))) = 1)
    (Hgate : forall (Hidx : length [0] = 1 /\ NoDup [0] /\
      Forall (fun i : fin => i < length (elems qubit_reference (participant * fin) qm)) [0]),
      uc_eval (` (base_to_ucom u [0] Hidx)) = G),
  transport_state_vector Houtlen (proj1_sig (projT2 qout)) =
    @Mmult 2 2 1 G (transport_state_vector Hqmlen sv).
Proof.
  intros qm Hqm sv Hsv lq Hlen Hdim qout u G Happly Houtmap Hqmlen Houtlen Hgate.
  pose proof (Hresult_vector qm Hqm sv Hsv 1 u lq Hlen Hdim qout Happly) as Hresult.
  destruct Hresult as [lpn [Hget [Hidx Hvec]]].
  pose proof (proj1 Hidx) as Hidxlen.
  pose proof (proj2 (proj2 Hidx)) as Hidxbounds.
  assert (Hmapidx : map snd lpn = [0]).
  {
    destruct lpn as [|[p idx] rest]; simpl in Hidxlen; [discriminate|].
    destruct rest as [|pair rest]; simpl in Hidxlen; [|discriminate].
    simpl.
    assert (Hidxlt : idx < length (elems qubit_reference (participant * fin) qm)).
    { simpl in Hidxbounds; inversion Hidxbounds; assumption. }
    rewrite Hqmlen in Hidxlt.
    simpl in Hidxlt; assert (idx = 0) by lia; subst idx; reflexivity.
  }
  assert (Hidx0 : length [0] = 1 /\ NoDup [0] /\
      Forall (fun i : fin => i < length (elems qubit_reference (participant * fin) qm)) [0]).
  {
    split; [reflexivity|].
    split; [constructor; [simpl; tauto|constructor]|].
    constructor; [rewrite Hqmlen; simpl; lia|constructor].
  }
  pose proof (@QTPathHelperDefinitions.qt_base_to_ucom_ext
    (length (elems qubit_reference (participant * fin) qm)) 1 u
    (map snd lpn) [0] Hidx Hidx0 Hmapidx) as Hbaseext.
  assert (Hbaselpn : uc_eval (` (base_to_ucom u (map snd lpn) Hidx)) = G).
  {
    transitivity (uc_eval (` (base_to_ucom u [0] Hidx0))).
    - exact Hbaseext.
    - exact (Hgate Hidx0).
  }
  rewrite (FunctionalCorrectnessHelpers.transport_state_vector_value
    _ _ Houtlen (` (projT2 qout))).
  rewrite (FunctionalCorrectnessHelpers.transport_state_vector_value
    _ _ Hqmlen sv).
  rewrite Hvec, Hbaselpn.
  rewrite Hqmlen.
  reflexivity.
Qed.

Lemma qt_apply_U_I_vector_same_map : forall
    (qm : finite_map qubit_reference (participant * fin))
    (Hqm : quantum_map_wf qm)
    (sv : state_vector (length (elems qubit_reference (participant * fin) qm)))
    (Hsv : state_vector_wf sv)
    (lq : list qubit_reference) (Hlen : length lq = 1) (Hdim : 1 > 0)
    (qout : quantum_state)
    (Happly : apply_unitary qm Hqm sv Hsv U_I lq Hlen Hdim = Some qout)
    (Houtmap : proj1_sig (projT1 qout) = qm)
    (Hqmlen : length (elems qubit_reference (participant * fin) qm) = 1)
    (Houtlen : length (elems qubit_reference (participant * fin) (` (projT1 qout))) = 1),
  transport_state_vector Houtlen (proj1_sig (projT2 qout)) =
    @Mmult 2 2 1 (I 2) (transport_state_vector Hqmlen sv).
Proof.
  intros qm Hqm sv Hsv lq Hlen Hdim qout Happly Houtmap Hqmlen Houtlen.
  pose proof (Hresult_vector qm Hqm sv Hsv 1 U_I lq Hlen Hdim qout Happly) as Hresult.
  destruct Hresult as [lpn [Hget [Hidx Hvec]]].
  pose proof (proj1 Hidx) as Hidxlen.
  pose proof (proj2 (proj2 Hidx)) as Hidxbounds.
  assert (Hmapidx : map snd lpn = [0]).
  {
    destruct lpn as [|[p idx] rest]; simpl in Hidxlen; [discriminate|].
    destruct rest as [|pair rest]; simpl in Hidxlen; [|discriminate].
    simpl.
    assert (Hidxlt : idx < length (elems qubit_reference (participant * fin) qm)).
    { simpl in Hidxbounds; inversion Hidxbounds; assumption. }
    rewrite Hqmlen in Hidxlt.
    simpl in Hidxlt; assert (idx = 0) by lia; subst idx; reflexivity.
  }
  assert (Hidx0 : length [0] = 1 /\ NoDup [0] /\
      Forall (fun i : fin => i < length (elems qubit_reference (participant * fin) qm)) [0]).
  {
    split; [reflexivity|].
    split; [constructor; [simpl; tauto|constructor]|].
    constructor; [rewrite Hqmlen; simpl; lia|constructor].
  }
  pose proof (@QTPathHelperDefinitions.qt_base_to_ucom_ext
    (length (elems qubit_reference (participant * fin) qm)) 1 U_I
    (map snd lpn) [0] Hidx Hidx0 Hmapidx) as Hbaseext.
  assert (HbaseI : uc_eval (` (base_to_ucom U_I [0] Hidx0)) = I (2 ^ length (elems qubit_reference (participant * fin) qm))).
  { exact (@qt_U_I_eval_from_length
      (length (elems qubit_reference (participant * fin) qm)) Hqmlen Hidx0). }
  assert (Hbase_lpn : uc_eval (` (base_to_ucom U_I (map snd lpn) Hidx)) =
      I (2 ^ length (elems qubit_reference (participant * fin) qm))).
  { transitivity (uc_eval (` (base_to_ucom U_I [0] Hidx0))).
    - exact Hbaseext.
    - exact HbaseI. }
  rewrite (FunctionalCorrectnessHelpers.transport_state_vector_value _ _ Houtlen (` (projT2 qout))).
  rewrite (FunctionalCorrectnessHelpers.transport_state_vector_value _ _ Hqmlen sv).
  rewrite Hvec, Hbase_lpn.
  rewrite Hqmlen; simpl; reflexivity.
Qed.

Lemma qt_delayed_premeasure_core :
  forall
    (starting_qstate : quantum_state)
    (end_state : state)
    (actions : list action)
    (Hstarting_length : length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))) = 1)
    (s'' : state)
    (H5 : ` (projT2 s''.1) = ` (projT2 end_state.1))
    (v'1 : qubit_reference)
    (H2 : (` (projT1 starting_qstate)) v'1 = Some (Env, 0))
    (la0 : list action)
    (s0 : session)
    (v' : qubit_reference)
    (Hfresh : ~ In v' (map fst (elems qubit_reference (participant * fin) (` (projT1 starting_qstate)))))
    (s : session)
    (s2 : session)
    (v'2 : qubit_reference)
    (Hfresh0 : ~ In v'2 (map fst (elems qubit_reference (participant * fin) (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))))))))
    (s1 : session)
    (s''0 : state)
    (H4 : finished s''0.2)
    (H19 : ` (projT2 s''0.1) = ` (projT2 s''.1))
    (la1 : list action)
    (q0 : quantum_state)
    (s4 : session)
    (s3 : session)
    (lq : list qubit_reference)
    (Hlen : length lq = 1)
    (Hdim : 1 > 0)
    (H32 : apply_unitary (insert (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))))) v'2 (Source, length (elems qubit_reference (participant * fin) (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate)))))))) (Primitives.add_new_qubit_obligation_1 (add_new_qubit starting_qstate Source v' Hfresh) Source v'2 Hfresh0) (@kron (2 ^ (length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))) + 1)) 1 2 1 (@kron (2 ^ length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate)))) 1 2 1 (` (projT2 starting_qstate)) ∣0⟩) ∣0⟩) (Primitives.add_new_qubit_obligation_2 (add_new_qubit starting_qstate Source v' Hfresh) Source v'2 Hfresh0) U_H lq Hlen Hdim = Some q0)
    (H31 : [Val (QVal v')] = map (fun z : qubit_reference => Val (QVal z)) lq)
    (H34 : NoDup lq)
    (H35 : Forall (fun q : qubit_reference => exists n : fin, insert (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))))) v'2 (Source, length (elems qubit_reference (participant * fin) (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))))))) q = Some (Source, n)) lq)
    (q3 : quantum_state)
    (s6 : session)
    (s5 : session)
    (lq0 : list qubit_reference)
    (Hlen0 : length lq0 = 2)
    (Hdim0 : 2 > 0)
    (H : List.cons (Val (QVal v')) (List.cons (Val (QVal v'2)) List.nil) = map (fun z : qubit_reference => Val (QVal z)) lq0)
    (H38 : apply_unitary (` (projT1 q0)) (proj2_sig (projT1 q0)) (` (projT2 q0)) (proj2_sig (projT2 q0)) U_CNOT lq0 Hlen0 Hdim0 = Some q3)
    (H39 : NoDup lq0)
    (H40 : Forall (fun q : qubit_reference => exists n : fin, (` (projT1 q0)) q = Some (Source, n)) lq0)
    (s8 : session)
    (old : participant)
    (n : fin)
    (Hlookup : (` (projT1 q3)) v' = Some (old, n))
    (s7 : session)
    (s10 : session)
    (old0 : participant)
    (n0 : fin)
    (Hlookup0 : insert (` (projT1 q3)) v' (Alice, n) v'2 = Some (old0, n0))
    (s9 : session)
    (s12 : session)
    (old1 : participant)
    (n1 : fin)
    (Hlookup1 : insert (insert (` (projT1 q3)) v' (Alice, n)) v'2 (Bob, n0) v'1 = Some (old1, n1))
    (s11 : session)
    (q : quantum_state)
    (s13 : session)
    (lq1 : list qubit_reference)
    (Hlen1 : length lq1 = 2)
    (Hdim1 : 2 > 0)
    (H37 : List.cons (Val (QVal v'1)) (List.cons (Val (QVal v')) List.nil) = map (fun z : qubit_reference => Val (QVal z)) lq1)
    (H47 : apply_unitary (insert (insert (insert (` (projT1 q3)) v' (Alice, n)) v'2 (Bob, n0)) v'1 (Alice, n1)) (Primitives.transfer_qubit_obligation_2 (insert (insert (` (projT1 q3)) v' (Alice, n)) v'2 (Bob, n0)) (Primitives.transfer_qubit_obligation_2 (insert (` (projT1 q3)) v' (Alice, n)) (Primitives.transfer_qubit_obligation_2 (` (projT1 q3)) (proj2_sig (projT1 q3)) Alice v' old n (eq_sym Hlookup)) Bob v'2 old0 n0 (eq_sym Hlookup0)) Alice v'1 old1 n1 (eq_sym Hlookup1)) (` (projT2 q3)) (Primitives.transfer_qubit_obligation_3 (insert (insert (` (projT1 q3)) v' (Alice, n)) v'2 (Bob, n0)) (Primitives.transfer_qubit_obligation_2 (insert (` (projT1 q3)) v' (Alice, n)) (Primitives.transfer_qubit_obligation_2 (` (projT1 q3)) (proj2_sig (projT1 q3)) Alice v' old n (eq_sym Hlookup)) Bob v'2 old0 n0 (eq_sym Hlookup0)) (` (projT2 q3)) (Primitives.transfer_qubit_obligation_3 (insert (` (projT1 q3)) v' (Alice, n)) (Primitives.transfer_qubit_obligation_2 (` (projT1 q3)) (proj2_sig (projT1 q3)) Alice v' old n (eq_sym Hlookup)) (` (projT2 q3)) (Primitives.transfer_qubit_obligation_3 (` (projT1 q3)) (proj2_sig (projT1 q3)) (` (projT2 q3)) (proj2_sig (projT2 q3)) Alice v' old n (eq_sym Hlookup)) Bob v'2 old0 n0 (eq_sym Hlookup0)) Alice v'1 old1 n1 (eq_sym Hlookup1)) U_CNOT lq1 Hlen1 Hdim1 = Some q)
    (H62 : NoDup lq1)
    (H63 : Forall (fun q : qubit_reference => exists n2 : fin, insert (insert (insert (` (projT1 q3)) v' (Alice, n)) v'2 (Bob, n0)) v'1 (Alice, n1) q = Some (Alice, n2)) lq1)
    (q1 : quantum_state)
    (s14 : session)
    (lq2 : list qubit_reference)
    (Hlen2 : length lq2 = 1)
    (Hdim2 : 1 > 0)
    (H53 : [Val (QVal v'1)] = map (fun z : qubit_reference => Val (QVal z)) lq2)
    (H65 : apply_unitary (` (projT1 q)) (proj2_sig (projT1 q)) (` (projT2 q)) (proj2_sig (projT2 q)) U_H lq2 Hlen2 Hdim2 = Some q1)
    (H67 : NoDup lq2)
    (H68 : Forall (fun q0 : qubit_reference => exists n : fin, (` (projT1 q)) q0 = Some (Alice, n)) lq2),
    exists HlenA : length (elems qubit_reference (participant * fin) (` (projT1 q1))) = 3,
      (` (projT1 q1) v'1 = Some (Alice,0)) /\
      (` (projT1 q1) v' = Some (Alice,1)) /\
      transport_state_vector HlenA (` (projT2 q1)) =
        QTPathHelperDefinitions.qt_alice_pre_measure ×
          (QTPathHelperDefinitions.qt_epr_preparation ×
            transport_state_vector Hstarting_length (` (projT2 starting_qstate))).
Proof.
  intros.
  destruct q0 as [qm_sig qv_sig].
  destruct qm_sig as [qmap0 Hqmap0].
  destruct qv_sig as [qvec0 Hqvec0].
  pose proof H32 as H32map.
  apply Happly_map in H32map.
  cbn in H32map.
  subst qmap0.
  pose proof H32 as H32vec.
  apply Hresult_vector in H32vec.
  destruct H32vec as [lp0 [Hget0 [Hidx0 Hq0vec]]].
  assert (Hv_v0 : v' <> v'1).
  { intro Heq; subst v'; apply Hfresh.
    apply In_fst_map with (ab := (v'1, (Env, 0))).
    apply (proj2 (specs qubit_reference (participant * fin) (` (projT1 starting_qstate)))); exact H2. }
  assert (Hv_v2 : v' <> v'2).
  { intro Heq; subst v'2; apply Hfresh0.
    apply In_fst_map with (ab := (v', (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate)))))).
    apply replace_or_add_In_eq. }
  apply qgt_qubit_list_singleton in H31; subst lq.
  rewrite Forall_forall in H35.
  specialize (H35 v' ltac:(simpl; auto)).
  destruct H35 as [nsource Hlookup_add].
  pose proof Hlookup_add as Hlookup_add_orig.
  rewrite insert_neq in Hlookup_add by congruence.
  rewrite insert_eq in Hlookup_add.
  rewrite Hstarting_length in Hlookup_add.
  inversion Hlookup_add; subst nsource.
  Transparent insert.
  assert (Haddlen1 : length (elems qubit_reference (participant * fin)
    (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate)))))) = 2).
  { unfold insert; simpl. rewrite replace_or_add_not_In_length.
    - rewrite Hstarting_length; reflexivity.
    - intros b Hin; apply Hfresh. apply In_fst_map with (ab := (v',b)); exact Hin. }
  assert (Haddlen2 : length (elems qubit_reference (participant * fin)
    (insert (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate)))))
      v'2 (Source, length (elems qubit_reference (participant * fin) (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))))))))) = 3).
  { unfold insert; simpl. rewrite replace_or_add_not_In_length.
    - rewrite replace_or_add_not_In_length.
      + rewrite Hstarting_length; reflexivity.
      + intros b Hin; apply Hfresh. apply In_fst_map with (ab := (v',b)); exact Hin.
    - intros b Hin; apply Hfresh0. apply In_fst_map with (ab := (v'2,b)); exact Hin. }
  assert (Hlp0 : lp0 = [(Source,1)]).
  { eapply qgt_get_all_values_singleton; [exact Hget0|exact Hlookup_add_orig]. }
  assert (Hmapidx0 : map snd lp0 = [1]) by (rewrite Hlp0; reflexivity).
  set (qmstart := (` (projT1 starting_qstate))).
  set (qm1 := insert qmstart v' (Source,
    length (elems qubit_reference (participant * fin) qmstart))).
  set (qmadd := insert qm1 v'2 (Source,
    length (elems qubit_reference (participant * fin) qm1))).
  assert (HidxOneBase : length [1] = 1 /\ NoDup [1] /\ Forall (fun i : nat => (i < 3)%nat) [1]).
  { split; [reflexivity|]. split.
    - constructor; [simpl; tauto|constructor].
    - constructor; [simpl; lia|constructor]. }
  assert (HidxOne : length [1] = 1 /\ NoDup [1] /\ Forall
    (fun i : nat => (i < length (elems qubit_reference (participant * fin) qmadd))%nat) [1]).
  { unfold qmadd, qm1, qmstart; rewrite Haddlen2; exact HidxOneBase. }
  pose proof (@QTPathHelperDefinitions.qt_base_to_ucom_ext
    (length (elems qubit_reference (participant * fin) qmadd)) 1 U_H
    (map snd lp0) [1] Hidx0 HidxOne Hmapidx0) as Hu0.
  unfold qmadd, qm1, qmstart in Hu0.
  match type of Hq0vec with
  | _ = @Mmult ?d ?d 1 _ ?input =>
      let f := constr:(fun op : Matrix d d => @Mmult d d 1 op input) in
      pose proof (f_equal f Hu0) as Hu0app
  end.
  pose proof (eq_trans Hq0vec Hu0app) as Hq0canonical.
  Opaque insert.
  Transparent U_H base_to_ucom ueval_r.
  unfold U_H in Hq0canonical.
  cbn [base_to_ucom uc_eval ueval_r] in Hq0canonical.
  simpl in Hq0canonical.
  rewrite hadamard_rotation in Hq0canonical.
  assert (HstartPlus : (length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))) + 2 = 3)%nat).
  { rewrite Hstarting_length; reflexivity. }
  assert (Hdim_start : length (elems qubit_reference (participant * fin) qmadd) =
    length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))) + 2).
  { unfold qmadd; exact (eq_trans Haddlen2 (eq_sym HstartPlus)). }
  match type of Hq0canonical with
  | _ = @Mmult ?d ?d 1 (pad_u ?n 1 hadamard) ?raw =>
      pose proof (@QTPathHelperDefinitions.qt_transport_pad_u n 3 Haddlen2 1 hadamard raw) as Hpad0
  end.
  pose proof (f_equal (transport_state_vector Haddlen2) Hq0canonical) as Hq0canonical3.
  pose proof (eq_trans Hq0canonical3 Hpad0) as Hq0canonicalPad.
  match type of Hq0canonical with
  | _ = @Mmult ?d ?d 1 (pad_u ?n 1 hadamard) ?raw =>
      pose proof (@QTPathHelperDefinitions.qt_transport_state_vector_compose
        n (length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))) + 2)
        3 Hdim_start HstartPlus raw) as Hinputcomp
  end.
  assert (Hdim_comp : eq_trans Hdim_start HstartPlus = Haddlen2) by apply proof_irrelevance.
  match type of Hinputcomp with
  | transport_state_vector (eq_trans Hdim_start HstartPlus) ?raw =
      transport_state_vector HstartPlus (transport_state_vector Hdim_start ?raw) =>
      pose proof (f_equal (fun e => transport_state_vector e raw) Hdim_comp) as Hcompcast;
      pose proof (@FunctionalCorrectnessHelpers.transport_state_vector_value
        _ _ Hdim_start raw) as Hrawdim;
      pose proof (f_equal (transport_state_vector HstartPlus) Hrawdim) as Hrawdim2;
      pose proof (eq_trans (eq_sym Hcompcast) (eq_trans Hinputcomp Hrawdim2)) as Hinputdim
  end.
  pose proof (f_equal (fun x : Matrix 8 1 =>
    @Mmult 8 8 1 (pad_u 3 1 hadamard) x) Hinputdim) as Hinputdimapp.
  pose proof (eq_trans Hq0canonicalPad Hinputdimapp) as Hq0factorpre.
  pose proof (@QTPathHelperDefinitions.qt_append_zeros_transport
    (length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate)))) 3
    Hstarting_length HstartPlus (` (projT2 starting_qstate))
    (proj2_sig (projT2 starting_qstate))) as Happend.
  pose proof (f_equal (fun x : Matrix 8 1 =>
    @Mmult 8 8 1 (pad_u 3 1 hadamard) x) Happend) as Happendapp.
  pose proof (eq_trans Hq0factorpre Happendapp) as Hq0factor.
  pose proof H38 as H38map.
  eapply Happly_map in H38map.
  cbn in H38map.
  pose proof H38 as H38vec.
  eapply Hresult_vector in H38vec.
  destruct H38vec as [lp38 [Hget38 [Hidx38 Hq3vec]]].
  apply qgt_qubit_list_pair in H; subst lq0.
  pose proof H40 as H40forall.
  rewrite Forall_forall in H40forall.
  specialize (H40forall v' ltac:(simpl; auto)).
  destruct H40forall as [idxv Hq0v].
  pose proof Hq0v as Hq0vlookup.
  cbn in Hq0v.
  rewrite insert_neq in Hq0v by congruence.
  rewrite insert_eq in Hq0v.
  rewrite Hstarting_length in Hq0v.
  inversion Hq0v; subst idxv.
  pose proof H40 as H40forall2.
  rewrite Forall_forall in H40forall2.
  specialize (H40forall2 v'2 ltac:(simpl; auto)).
  destruct H40forall2 as [idxv2 Hq0v2].
  pose proof Hq0v2 as Hq0v2lookup.
  cbn in Hq0v2.
  rewrite insert_eq in Hq0v2.
  injection Hq0v2 as Hidxv2.
  assert (Hleninner : length (elems qubit_reference (participant * fin)
    (insert (` (projT1 starting_qstate)) v'
      (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate)))))) = 2).
  { exact Haddlen1. }
  assert (Hidxv2_2 : idxv2 = 2).
  { exact (eq_trans (eq_sym Hidxv2) Hleninner). }
  subst idxv2.
    assert (Hq0v2_concrete : qmadd v'2 = Some (Source,2)).
  { unfold qmadd, qm1, qmstart; rewrite insert_eq, Hleninner; reflexivity. }
  assert (Hlp38 : lp38 = List.cons (Source,1) (List.cons (Source,2) nil)).
  { eapply qgt_get_all_values_pair; [exact Hget38|exact Hq0vlookup|exact Hq0v2_concrete]. }
  assert (Hidx12 : length (List.cons 1 (List.cons 2 nil)) = 2 /\
    NoDup (List.cons 1 (List.cons 2 nil)) /\
    Forall (fun i : nat => (i < length (elems qubit_reference (participant * fin) qmadd))%nat)
      (List.cons 1 (List.cons 2 nil))).
  { unfold qmadd, qm1, qmstart; rewrite Haddlen2; split; [reflexivity|]. split.
    - repeat constructor; simpl; intuition congruence.
    - repeat constructor; simpl; lia. }
  assert (Hmapidx38 : map snd lp38 = List.cons 1 (List.cons 2 nil)).
  { rewrite Hlp38; reflexivity. }
  pose proof (@QTPathHelperDefinitions.qt_base_to_ucom_ext
    (length (elems qubit_reference (participant * fin) qmadd)) 2 U_CNOT
    (map snd lp38) (List.cons 1 (List.cons 2 nil))
    Hidx38 Hidx12 Hmapidx38) as Hcnotext.
  assert (Hbasecnot :
    uc_eval (` (base_to_ucom U_CNOT (List.cons 1 (List.cons 2 nil)) Hidx12)) =
    pad_ctrl (length (elems qubit_reference (participant * fin) qmadd)) 1 2 σx).
  { Transparent base_to_ucom ueval_r.
    cbn [base_to_ucom uc_eval ueval_r]; reflexivity. }
  pose proof (f_equal (transport_state_vector Haddlen2) Hq3vec) as Hq3vec_cast.
  pose proof (f_equal (fun op : Matrix (2 ^ length (elems qubit_reference (participant * fin) qmadd))
      (2 ^ length (elems qubit_reference (participant * fin) qmadd)) =>
      @Mmult (2 ^ length (elems qubit_reference (participant * fin) qmadd))
        (2 ^ length (elems qubit_reference (participant * fin) qmadd)) 1 op qvec0) Hcnotext) as Hcnotapp.
  pose proof (f_equal (transport_state_vector Haddlen2) Hcnotapp) as Hcnotappcast.
  pose proof (eq_trans Hq3vec_cast Hcnotappcast) as Hq3vec_cast1.
  pose proof (f_equal (fun op : Matrix (2 ^ length (elems qubit_reference (participant * fin) qmadd))
      (2 ^ length (elems qubit_reference (participant * fin) qmadd)) =>
      @Mmult (2 ^ length (elems qubit_reference (participant * fin) qmadd))
        (2 ^ length (elems qubit_reference (participant * fin) qmadd)) 1 op qvec0) Hbasecnot) as Hbasecnotapp.
  pose proof (f_equal (transport_state_vector Haddlen2) Hbasecnotapp) as Hbasecnotappcast.
  pose proof (eq_trans Hq3vec_cast1 Hbasecnotappcast) as Hq3vec_cast2.
  pose proof (@QTPathHelperDefinitions.qt_transport_pad_ctrl
    (length (elems qubit_reference (participant * fin) qmadd)) 3 Haddlen2
    1 2 σx qvec0) as Hctrlcast.
  pose proof (eq_trans Hq3vec_cast2 Hctrlcast) as Hq3vec_cast3.
  pose proof (f_equal (fun x : Matrix 8 1 =>
    @Mmult 8 8 1 (pad_ctrl 3 1 2 σx) x) Hq0factor) as Hq0ctrl.
  pose proof (eq_trans Hq3vec_cast3 Hq0ctrl) as Hq3_vector0.
  assert (Hq3_vector :
    transport_state_vector Haddlen2 (` (projT2 q3)) =
      QTPathHelperDefinitions.qt_epr_preparation ×
        transport_state_vector Hstarting_length (` (projT2 starting_qstate))).
  { unfold QTPathHelperDefinitions.qt_epr_preparation.
    repeat rewrite <- Mmult_assoc in Hq3_vector0.
    exact Hq3_vector0. }
  assert (Hv2v1 : v'2 <> v'1).
  { intro Heq; subst v'2; apply Hfresh0.
    apply In_fst_map with (ab := (v'1, (Env, 0))).
    apply replace_or_add_In_neq.
    - intro Heq; apply Hv_v0; symmetry; exact Heq.
    - apply (proj2 (specs qubit_reference (participant * fin)
        (` (projT1 starting_qstate)))); exact H2. }
  assert (Hq3v : (` (projT1 q3)) v' = Some (Source,1)).
  { rewrite H38map; exact Hq0vlookup. }
  assert (Hq3v1 : (` (projT1 q3)) v'1 = Some (Env,0)).
  { rewrite H38map; cbn.
    rewrite insert_neq by exact Hv2v1.
    rewrite insert_neq by exact Hv_v0.
    exact H2. }
  assert (Hq3v2 : (` (projT1 q3)) v'2 = Some (Source,2)).
  { rewrite H38map; exact Hq0v2_concrete. }
  assert (Hq3len : length (elems qubit_reference (participant * fin) (` (projT1 q3))) = 3).
  { rewrite H38map; exact Haddlen2. }
  pose proof Hlookup as Hlookup_copy.
  rewrite Hq3v in Hlookup_copy.
  injection Hlookup_copy as HownerEq HnEq.
  subst old n.
  pose proof Hlookup0 as Hlookup0_copy.
  rewrite insert_neq in Hlookup0_copy by congruence.
  rewrite Hq3v2 in Hlookup0_copy.
  injection Hlookup0_copy as Howner0Eq Hn0Eq.
  subst old0 n0.
  pose proof Hlookup1 as Hlookup1_copy.
  rewrite insert_neq in Hlookup1_copy by congruence.
  rewrite insert_neq in Hlookup1_copy by congruence.
  rewrite Hq3v1 in Hlookup1_copy.
  injection Hlookup1_copy as Howner1Eq Hn1Eq.
  subst old1 n1.
  assert (HlenB1 : length (elems qubit_reference (participant * fin)
      (insert (` (projT1 q3)) v' (Alice,1))) =
    length (elems qubit_reference (participant * fin) (` (projT1 q3)))).
  { eapply qgt_insert_preserves_length; exact Hlookup. }
  assert (HlenB2 : length (elems qubit_reference (participant * fin)
      (insert (insert (` (projT1 q3)) v' (Alice,1)) v'2 (Bob,2))) =
    length (elems qubit_reference (participant * fin)
      (insert (` (projT1 q3)) v' (Alice,1)))).
  { eapply qgt_insert_preserves_length; exact Hlookup0. }
  assert (HlenB3 : length (elems qubit_reference (participant * fin)
      (insert (insert (insert (` (projT1 q3)) v' (Alice,1)) v'2 (Bob,2)) v'1 (Alice,0))) =
    length (elems qubit_reference (participant * fin)
      (insert (insert (` (projT1 q3)) v' (Alice,1)) v'2 (Bob,2)))).
  { eapply qgt_insert_preserves_length; exact Hlookup1. }
  assert (HlenBefore : length (elems qubit_reference (participant * fin)
      (insert (insert (insert (` (projT1 q3)) v' (Alice,1)) v'2 (Bob,2)) v'1 (Alice,0))) = 3).
  { rewrite HlenB3, HlenB2, HlenB1, Hq3len; reflexivity. }
  assert (HqBefore_v'1 :
      (insert (insert (insert (` (projT1 q3)) v' (Alice,1)) v'2 (Bob,2)) v'1 (Alice,0)) v'1 = Some (Alice,0)).
  { rewrite insert_eq; reflexivity. }
  assert (HqBefore_v' :
      (insert (insert (insert (` (projT1 q3)) v' (Alice,1)) v'2 (Bob,2)) v'1 (Alice,0)) v' = Some (Alice,1)).
  { rewrite insert_neq by congruence.
    rewrite insert_neq by congruence.
    rewrite insert_eq; reflexivity. }
  apply qgt_qubit_list_pair in H37; subst lq1.
  destruct q as [qmsig qvsig].
  destruct qmsig as [qmapA HqmapA].
  destruct qvsig as [qvecA HqvecA].
  pose proof H47 as H47map.
  eapply Happly_map in H47map.
  cbn in H47map.
  subst qmapA.
  assert (Hq1map : proj1_sig (projT1 q1) =
      insert (insert (insert (` (projT1 q3)) v' (Alice,1)) v'2 (Bob,2)) v'1 (Alice,0)).
  {
    pose proof H65 as H65map.
    eapply Happly_map in H65map.
    cbn in H65map.
    exact H65map.
  }
  assert (HlenA : length (elems qubit_reference (participant * fin)
      (` (projT1 q1))) = 3).
  { rewrite Hq1map; exact HlenBefore. }
  assert (HqA_v'1 : (` (projT1 q1)) v'1 = Some (Alice,0)).
  { rewrite Hq1map; exact HqBefore_v'1. }
  assert (HqA_v' : (` (projT1 q1)) v' = Some (Alice,1)).
  { rewrite Hq1map; exact HqBefore_v'. }
  pose proof H47 as H47vec.
  eapply Hresult_vector in H47vec.
  destruct H47vec as [lp47 [Hget47 [Hidx47 Hq47vec]]].
  assert (Hlp47 : lp47 = List.cons (Alice,0) (List.cons (Alice,1) nil)).
  { eapply qgt_get_all_values_pair; [exact Hget47|exact HqBefore_v'1|exact HqBefore_v']. }
  assert (Hidx01 : length (List.cons 0 (List.cons 1 nil)) = 2 /\ NoDup (List.cons 0 (List.cons 1 nil)) /\
      Forall (fun i : nat => i < length (elems qubit_reference (participant * fin)
        (insert (insert (insert (` (projT1 q3)) v' (Alice,1)) v'2 (Bob,2)) v'1 (Alice,0)))%nat) (List.cons 0 (List.cons 1 nil))).
  { rewrite HlenBefore; split; [reflexivity|]. split.
    - repeat constructor; simpl; intuition congruence.
    - repeat constructor; simpl; lia. }
  assert (Hmapidx47 : map snd lp47 = List.cons 0 (List.cons 1 nil)).
  { rewrite Hlp47; reflexivity. }
  pose proof (@QTPathHelperDefinitions.qt_base_to_ucom_ext
    (length (elems qubit_reference (participant * fin)
      (insert (insert (insert (` (projT1 q3)) v' (Alice,1)) v'2 (Bob,2)) v'1 (Alice,0)))) 2 U_CNOT
    (map snd lp47) (List.cons 0 (List.cons 1 nil)) Hidx47 Hidx01 Hmapidx47) as Hcnotext47.
  assert (Hbasecnot47 :
    uc_eval (` (base_to_ucom U_CNOT (List.cons 0 (List.cons 1 nil)) Hidx01)) =
      pad_ctrl (length (elems qubit_reference (participant * fin)
        (insert (insert (insert (` (projT1 q3)) v' (Alice,1)) v'2 (Bob,2)) v'1 (Alice,0)))) 0 1 σx).
  { cbn [base_to_ucom uc_eval ueval_r]; reflexivity. }
  match type of Hq47vec with
  | _ = @Mmult ?d ?d 1 ?op ?raw =>
      pose proof (f_equal (fun u : Matrix d d => @Mmult d d 1 u raw) Hcnotext47) as Hcnotapp47;
      pose proof (f_equal (fun u : Matrix d d => @Mmult d d 1 u raw) Hbasecnot47) as Hbaseapp47;
      pose proof (f_equal (transport_state_vector HlenBefore) Hq47vec) as Hq47cast;
      pose proof (f_equal (transport_state_vector HlenBefore) Hcnotapp47) as Hcnotapp47cast;
      pose proof (eq_trans Hq47cast Hcnotapp47cast) as Hq47cast1;
      pose proof (f_equal (transport_state_vector HlenBefore) Hbaseapp47) as Hbaseapp47cast;
      pose proof (eq_trans Hq47cast1 Hbaseapp47cast) as Hq47cast2;
      pose proof (@QTPathHelperDefinitions.qt_transport_pad_ctrl
        (length (elems qubit_reference (participant * fin)
          (insert (insert (insert (` (projT1 q3)) v' (Alice,1)) v'2 (Bob,2)) v'1 (Alice,0))))
        3 HlenBefore 0 1 σx raw) as Hctrl47cast;
      pose proof (eq_trans Hq47cast2 Hctrl47cast) as Hq47cast3
  end.
  match type of Hq47vec with
  | _ = @Mmult ?d ?d 1 ?op ?raw =>
      assert (Hq3transfers :
        transport_state_vector HlenBefore raw =
        transport_state_vector Haddlen2 (` (projT2 q3))) by
        (transitivity (` (projT2 q3));
         [apply FunctionalCorrectnessHelpers.transport_state_vector_value|
          symmetry; apply FunctionalCorrectnessHelpers.transport_state_vector_value])
  end.
  pose proof (f_equal (fun x : Matrix 8 1 =>
    @Mmult 8 8 1 (pad_ctrl 3 0 1 σx) x) Hq3transfers) as Hq3cnot.
  pose proof (eq_trans Hq47cast3 Hq3cnot) as Hq_after_cnot.
  destruct q1 as [q1msig q1vsig].
  destruct q1msig as [qmap1 Hqmap1].
  destruct q1vsig as [qvec1 Hqvec1].
  pose proof H65 as H65map.
  eapply Happly_map in H65map.
  cbn in H65map.
  subst qmap1.
  apply qgt_qubit_list_singleton in H53; subst lq2.
  pose proof H65 as H65vec.
  eapply Hresult_vector in H65vec.
  destruct H65vec as [lp65 [Hget65 [Hidx65 Hq1vec]]].
  assert (Hlp65 : lp65 = [(Alice,0)]).
  { eapply qgt_get_all_values_singleton; [exact Hget65|exact HqBefore_v'1]. }
  assert (HidxHad0 : length [0] = 1 /\ NoDup [0] /\
    Forall (fun i : nat => i < length (elems qubit_reference (participant * fin)
      (insert (insert (insert (` (projT1 q3)) v' (Alice,1)) v'2 (Bob,2)) v'1 (Alice,0)))) [0]).
  { rewrite HlenBefore; simpl; split; [reflexivity|]. split.
    - constructor; [simpl; tauto|constructor].
    - constructor; [simpl; lia|constructor]. }
  assert (Hmapidx65 : map snd lp65 = [0]).
  { rewrite Hlp65; reflexivity. }
  pose proof (@QTPathHelperDefinitions.qt_base_to_ucom_ext
    (length (elems qubit_reference (participant * fin)
      (insert (insert (insert (` (projT1 q3)) v' (Alice,1)) v'2 (Bob,2)) v'1 (Alice,0)))) 1 U_H
    (map snd lp65) [0] Hidx65 HidxHad0 Hmapidx65) as Hhadext65.
  assert (Hbasehad0 : uc_eval (` (base_to_ucom U_H [0] HidxHad0)) =
      pad_u (length (elems qubit_reference (participant * fin)
        (insert (insert (insert (` (projT1 q3)) v' (Alice,1)) v'2 (Bob,2)) v'1 (Alice,0)))) 0 hadamard).
  { Transparent U_H base_to_ucom ueval_r.
    unfold U_H; cbn [base_to_ucom uc_eval ueval_r]; simpl.
    rewrite hadamard_rotation; reflexivity. }
  match type of Hq1vec with
  | _ = @Mmult ?d ?d 1 ?op ?raw =>
      pose proof (f_equal (fun u : Matrix d d => @Mmult d d 1 u raw) Hhadext65) as Hhadapp65;
      pose proof (f_equal (fun u : Matrix d d => @Mmult d d 1 u raw) Hbasehad0) as Hbasehadapp65;
      pose proof (f_equal (transport_state_vector HlenBefore) Hq1vec) as Hq1cast;
      pose proof (f_equal (transport_state_vector HlenBefore) Hhadapp65) as Hhadapp65cast;
      pose proof (eq_trans Hq1cast Hhadapp65cast) as Hq1cast1;
      pose proof (f_equal (transport_state_vector HlenBefore) Hbasehadapp65) as Hbasehadapp65cast;
      pose proof (eq_trans Hq1cast1 Hbasehadapp65cast) as Hq1cast2;
      pose proof (@QTPathHelperDefinitions.qt_transport_pad_u
        (length (elems qubit_reference (participant * fin)
          (insert (insert (insert (` (projT1 q3)) v' (Alice,1)) v'2 (Bob,2)) v'1 (Alice,0))))
        3 HlenBefore 0 hadamard raw) as Hhadcast65;
      pose proof (eq_trans Hq1cast2 Hhadcast65) as Hq1cast3
  end.
  pose proof (f_equal (fun x : Matrix 8 1 => @Mmult 8 8 1 (pad_u 3 0 hadamard) x)
    Hq_after_cnot) as Hq_cnot_h.
  pose proof (eq_trans Hq1cast3 Hq_cnot_h) as Hpre0.
  repeat rewrite <- Mmult_assoc in Hpre0.
  pose proof (f_equal (fun x : Matrix 8 1 =>
    @Mmult 8 8 1 (pad_u 3 0 hadamard × pad_ctrl 3 0 1 σx) x)
    Hq3_vector) as Hpreappend.
  pose proof (eq_trans Hpre0 Hpreappend) as Hpre1.
  exists HlenA.
  repeat split; try assumption.
  assert (Hpre : transport_state_vector HlenA qvec1 =
      QTPathHelperDefinitions.qt_alice_pre_measure ×
        (QTPathHelperDefinitions.qt_epr_preparation ×
          transport_state_vector Hstarting_length (` (projT2 starting_qstate)))).
  { unfold QTPathHelperDefinitions.qt_alice_pre_measure.
    replace HlenA with HlenBefore by apply proof_irrelevance.
    exact Hpre1. }
  exact Hpre.
Qed.

Lemma qt_teleportation_measurement_core :
  forall
    (starting_qstate : quantum_state)
    (Hstarting_length : length (elems qubit_reference (participant * fin)
      (` (projT1 starting_qstate))) = 1)
    (x y : bool)
    (v'0 v' v'2 : qubit_reference)
    (qmap : finite_map qubit_reference (participant * fin))
    (Hqmap : quantum_map_wf qmap)
    (qvec : state_vector (length (elems qubit_reference (participant * fin) qmap)))
    (Hqvec : state_vector_wf qvec)
    (HlenA : length (elems qubit_reference (participant * fin) qmap) = 3)
    (HqA_v'0 : qmap v'0 = Some (Alice,0))
    (HqA_v' : qmap v' = Some (Alice,1))
    (Hpre : transport_state_vector HlenA qvec =
      QTPathHelperDefinitions.qt_alice_pre_measure ×
        (QTPathHelperDefinitions.qt_epr_preparation ×
          transport_state_vector Hstarting_length (` (projT2 starting_qstate))))
    (q5 : qubit_reference)
    (n1 : fin)
    (Hprob : {prob : R | (prob > 0)%R})
    (Hlookup1 : qmap q5 = Some (Alice,n1))
    (Hlen3 : 0 < length (elems qubit_reference (participant * fin) qmap))
    (Hnonzero : norm (proj n1 (length (elems qubit_reference (participant * fin) qmap)) x × qvec) <> 0%R)
    (H59 : Val (QVal v'0) = Val (QVal q5))
    (q4 : quantum_state)
    (H63 : (Hprob,q4) = measure_qubit_from_nonzero qmap Hqmap qvec Hqvec
      q5 Alice n1 x Hlookup1 Hlen3 Hnonzero)
    (q7 : qubit_reference)
    (n2 : fin)
    (Hprob0 : {prob : R | (prob > 0)%R})
    (Hlookup2 : (` (projT1 q4)) q7 = Some (Alice,n2))
    (Hlen4 : 0 < length (elems qubit_reference (participant * fin) (` (projT1 q4))))
    (Hnonzero0 : norm (proj n2 (length (elems qubit_reference (participant * fin) (` (projT1 q4)))) y × ` (projT2 q4)) <> 0%R)
    (H64 : Val (QVal v') = Val (QVal q7))
    (q6 : quantum_state)
    (H66 : (Hprob0,q6) = measure_qubit_from_nonzero (` (projT1 q4))
      (proj2_sig (projT1 q4)) (` (projT2 q4)) (proj2_sig (projT2 q4))
      q7 Alice n2 y Hlookup2 Hlen4 Hnonzero0)
    (qout : quantum_state)
    (Hqoutlen : length (elems qubit_reference (participant * fin)
      (` (projT1 qout))) = 1)
    (Houtvec : forall
      (Hq6len : length (elems qubit_reference (participant * fin) (` (projT1 q6))) = 1)
      (Houtlen : length (elems qubit_reference (participant * fin) (` (projT1 qout))) = 1),
      transport_state_vector Houtlen (proj1_sig (projT2 qout)) =
        @Mmult 2 2 1 (QTPathHelperDefinitions.qt_correction x y)
          (transport_state_vector Hq6len (proj1_sig (projT2 q6))))
    (tail_session : session)
    (Htail_ends : forall p, tail_session p = None \/
      exists lz, tail_session p = Some (p_end lz))
    (old2 : participant)
    (n4 : fin)
    (Hlookup4 : (` (projT1 qout)) v'2 = Some (old2,n4))
    (la : list action)
    (s''0 : state)
    (r2 : R)
    (Htail : multistep (transfer_qubit_from_lookup (` (projT1 qout))
      (proj2_sig (projT1 qout)) (` (projT2 qout)) (proj2_sig (projT2 qout))
      Env v'2 old2 n4 Hlookup4, tail_session) la s''0 r2)
    (s'' end_state : state)
    (H5 : ` (projT2 s''.1) = ` (projT2 end_state.1))
    (H19 : ` (projT2 s''0.1) = ` (projT2 s''.1)),
    proj1_sig (projT2 (fst end_state)) = proj1_sig (projT2 starting_qstate).
Proof.
  intros.
  assert (Hv_v0 : v' <> v'0).
  { intro Heq; subst v'; rewrite HqA_v'0 in HqA_v'; inversion HqA_v'. }
  injection H63 as Hprob_eq Hq4eq.
  subst q4.
  assert (Hq5id : q5 = v'0).
  { injection H59 as Heq; symmetry; exact Heq. }
  assert (Hn1eq : n1 = 0).
  { pose proof Hlookup1 as Hlookup1_copy.
    change (qmap q5 = Some (Alice,n1)) in Hlookup1_copy.
    rewrite Hq5id in Hlookup1_copy.
    rewrite HqA_v'0 in Hlookup1_copy.
    inversion Hlookup1_copy; reflexivity. }
  pose proof (@measure_qubit_nonzero_map
    qmap
    Hqmap qvec Hqvec q5 Alice n1 x Hlookup1 Hlen3 Hnonzero)
    as Hmap_measure1.
  pose proof (@remove_and_reindex_qubit_map_length
    qmap
    q5 Alice n1 Hlookup1) as Hremoved_len1.
  assert (Houtdim1 : length (elems qubit_reference (participant * fin)
      (proj1_sig (projT1 (snd (measure_qubit_nonzero
        qmap
        Hqmap qvec Hqvec q5 Alice n1 x Hlookup1 Hlen3 Hnonzero))))) = 2).
  { rewrite Hmap_measure1.
    transitivity (Nat.pred (length (elems qubit_reference (participant * fin)
      qmap))).
    - exact Hremoved_len1.
    - rewrite HlenA; reflexivity. }
  set (input := transport_state_vector Hstarting_length (` (projT2 starting_qstate))).
  set (pre := @Mmult 8 8 1 QTPathHelperDefinitions.qt_alice_pre_measure
    (@Mmult 8 2 1 QTPathHelperDefinitions.qt_epr_preparation input)).
  assert (Hinputwf : @state_vector_wf 1 input).
  { unfold input; apply transport_state_vector_wf; exact (proj2_sig (projT2 starting_qstate)). }
  assert (Hprewf : @WF_Matrix 8 1 pre).
  {
    pose proof (@transport_state_vector_wf
      (length (elems qubit_reference (participant * fin)
        qmap))
      3 HlenA qvec Hqvec) as Hq1wf.
    rewrite Hpre in Hq1wf.
    unfold pre.
    exact (proj1 Hq1wf).
  }
  set (m1 := transport_state_vector Houtdim1
    (proj1_sig (projT2 (snd (measure_qubit_nonzero
      qmap
      Hqmap qvec Hqvec q5 Alice n1 x Hlookup1 Hlen3 Hnonzero))))).
  set (q4_state := snd (measure_qubit_from_nonzero
    qmap
    Hqmap qvec Hqvec q5 Alice n1 x Hlookup1 Hlen3 Hnonzero)).
  assert (Houtdim1_q4 : length (elems qubit_reference (participant * fin)
      (` (projT1 q4_state))) = 2).
  { unfold q4_state; exact Houtdim1. }
  assert (Hq4vec_m1 : transport_state_vector Houtdim1_q4 (` (projT2 q4_state)) = m1).
  { unfold m1, q4_state; f_equal; apply proof_irrelevance. }
  pose proof (@qt_measure_output_vector_fixed 2
    qmap
    Hqmap qvec Hqvec q5 Alice n1 x Hlookup1 Hlen3 Hnonzero HlenA
    Houtdim1) as Hm1.
  unfold m1 in Hm1.
  assert (Hm1canonical : m1 = @normalize_removed_wire 2
    (@Mmult 4 8 1 (remove_measured_wire_operator 2 0 x)
      (@Mmult 8 8 1 (proj 0 3 x) pre))).
  {
    unfold m1.
    transitivity (@normalize_removed_wire 2
      (@Mmult 4 8 1 (remove_measured_wire_operator 2 n1 x)
        (@Mmult 8 8 1 (proj n1 3 x)
          (transport_state_vector HlenA qvec)))).
    - exact Hm1.
    - f_equal; rewrite Hpre, Hn1eq; reflexivity.
  }
  assert (Hprojcast1 : transport_state_vector HlenA
      (@Mmult
        (2 ^ length (elems qubit_reference (participant * fin)
          qmap))
        (2 ^ length (elems qubit_reference (participant * fin)
          qmap))
        1
        (proj 0 (length (elems qubit_reference (participant * fin)
          qmap)) x)
        qvec) =
      @Mmult 8 8 1 (proj 0 3 x) pre).
  {
    pose proof (@transport_state_vector_proj
      (length (elems qubit_reference (participant * fin)
        qmap))
      3 HlenA 0 x qvec) as Hcast.
    rewrite Hpre in Hcast.
    exact Hcast.
  }
  assert (Hnonzero_pre1 : norm (@Mmult 8 8 1 (proj 0 3 x) pre) <> 0%R).
  {
    intro Hzero.
    pose proof Hnonzero as Hnonzero_raw.
    change (norm
      (proj n1 (length (elems qubit_reference (participant * fin)
        qmap))
        x × qvec) <> 0%R) in Hnonzero_raw.
    rewrite Hn1eq in Hnonzero_raw.
    apply Hnonzero_raw.
    rewrite <- Hprojcast1 in Hzero.
    pose proof (@transport_state_vector_norm
      (length (elems qubit_reference (participant * fin)
        qmap))
      3 HlenA
      (@Mmult
        (2 ^ length (elems qubit_reference (participant * fin)
          qmap))
        (2 ^ length (elems qubit_reference (participant * fin)
          qmap))
        1
        (proj 0 (length (elems qubit_reference (participant * fin)
          qmap)) x)
        qvec)) as Hnorm_transport.
    exact (eq_trans (eq_sym Hnorm_transport) Hzero).
  }
  assert (Hraw1_nonzero :
    @Mmult 4 8 1 (remove_measured_wire_operator 2 0 x)
      (@Mmult 8 8 1 (proj 0 3 x) pre) <> Zero).
  { exact (@qt_remove_projected_nonzero
      2 0 x pre ltac:(lia) Hprewf Hnonzero_pre1). }
  assert (Hq7id : q7 = v').
  { injection H64 as Heq; symmetry; exact Heq. }
  assert (Hneq_q5 : v' <> q5).
  { rewrite Hq5id; exact Hv_v0. }
  assert (Hlookup2_removed :
    remove_and_reindex_qubit_map
      qmap
      q5 n1 v' = Some (Alice,n2)).
  {
    pose proof Hlookup2 as Hlookup2_copy.
    change (remove_and_reindex_qubit_map
      qmap
      q5 n1 q7 = Some (Alice,n2)) in Hlookup2_copy.
    rewrite Hq7id in Hlookup2_copy.
    exact Hlookup2_copy.
  }
  destruct (@Hremove_lookup_inv
    qmap
    v' q5 n1 Alice n2 Hneq_q5 Hlookup2_removed)
    as [nold [Hlookup_v' Hshift_n2]].
  assert (Hnold1 : nold = 1).
  { rewrite HqA_v' in Hlookup_v'; inversion Hlookup_v'; reflexivity. }
  assert (Hn2eq : n2 = 0).
  { rewrite Hn1eq, Hnold1 in Hshift_n2.
    cbn [shift_wire_index] in Hshift_n2.
    exact Hshift_n2. }
  injection H66 as Hprob0_eq Hq6eq.
  subst q6.
  pose proof (@measure_qubit_nonzero_map
    (` (projT1 q4_state)) (proj2_sig (projT1 q4_state))
    (` (projT2 q4_state)) (proj2_sig (projT2 q4_state))
    q7 Alice n2 y Hlookup2 Hlen4 Hnonzero0) as Hmap_measure2.
  pose proof (@remove_and_reindex_qubit_map_length
    (` (projT1 q4_state)) q7 Alice n2 Hlookup2) as Hremoved_len2.
  assert (Houtdim2 : length (elems qubit_reference (participant * fin)
      (` (projT1 (snd (measure_qubit_nonzero
        (` (projT1 q4_state)) (proj2_sig (projT1 q4_state))
        (` (projT2 q4_state)) (proj2_sig (projT2 q4_state))
        q7 Alice n2 y Hlookup2 Hlen4 Hnonzero0))))) = 1).
  {
    rewrite Hmap_measure2.
    transitivity (Nat.pred (length (elems qubit_reference
      (participant * fin) (` (projT1 q4_state))))).
    - exact Hremoved_len2.
    - rewrite Houtdim1_q4; reflexivity.
  }
  set (q6_state := snd (measure_qubit_nonzero
    (` (projT1 q4_state)) (proj2_sig (projT1 q4_state))
    (` (projT2 q4_state)) (proj2_sig (projT2 q4_state))
    q7 Alice n2 y Hlookup2 Hlen4 Hnonzero0)).
  set (m2 := transport_state_vector Houtdim2
    (` (projT2 (snd (measure_qubit_nonzero
      (` (projT1 q4_state)) (proj2_sig (projT1 q4_state))
      (` (projT2 q4_state)) (proj2_sig (projT2 q4_state))
      q7 Alice n2 y Hlookup2 Hlen4 Hnonzero0))))).
  pose proof (@qt_measure_output_vector_fixed 1
    (` (projT1 q4_state)) (proj2_sig (projT1 q4_state))
    (` (projT2 q4_state)) (proj2_sig (projT2 q4_state))
    q7 Alice n2 y Hlookup2 Hlen4 Hnonzero0 Houtdim1_q4 Houtdim2)
    as Hm2.
  unfold m2 in Hm2.
  assert (Hm2canonical : m2 = @normalize_removed_wire 1
    (@Mmult 2 4 1 (remove_measured_wire_operator 1 0 y)
      (@Mmult 4 4 1 (proj 0 2 y) m1))).
  {
    unfold m2.
    transitivity (@normalize_removed_wire 1
      (@Mmult 2 4 1 (remove_measured_wire_operator 1 n2 y)
        (@Mmult 4 4 1 (proj n2 2 y)
          (transport_state_vector Houtdim1_q4 (` (projT2 q4_state)))))).
    - exact Hm2.
    - f_equal; rewrite Hn2eq, Hq4vec_m1; reflexivity.
  }
  assert (Hm1wf : @WF_Matrix 4 1 m1).
  {
    pose proof (@transport_state_vector_wf
      (length (elems qubit_reference (participant * fin)
      (` (projT1 q4_state)))) 2 Houtdim1_q4
      (` (projT2 q4_state)) (proj2_sig (projT2 q4_state))) as Hwf.
    rewrite <- Hq4vec_m1.
    exact (proj1 Hwf).
  }
  assert (Hnonzero_pre2 : norm (@Mmult 4 4 1 (proj 0 2 y) m1) <> 0%R).
  {
    intro Hzero.
    pose proof Hnonzero0 as Hnonzero0_raw.
    rewrite Hn2eq in Hnonzero0_raw.
    apply Hnonzero0_raw.
    pose proof (@transport_state_vector_proj
      (length (elems qubit_reference (participant * fin)
      (` (projT1 q4_state)))) 2 Houtdim1_q4 n2 y
      (` (projT2 q4_state))) as Hprojcast2.
    rewrite Hn2eq in Hprojcast2.
    rewrite <- Hq4vec_m1 in Hzero.
    pose proof (f_equal (fun z : Matrix 4 1 => @norm 4 z) Hprojcast2)
      as Hnormcast2.
    assert (Hzero_transport :
      @norm 4 (transport_state_vector Houtdim1_q4
        (@Mmult
          (2 ^ length (elems qubit_reference (participant * fin)
            (` (projT1 q4_state))))
          (2 ^ length (elems qubit_reference (participant * fin)
            (` (projT1 q4_state)))) 1
          (proj 0 (length (elems qubit_reference (participant * fin)
            (` (projT1 q4_state)))) y)
        (` (projT2 q4_state)))) = 0%R).
    { exact (eq_trans Hnormcast2 Hzero). }
    pose proof (@transport_state_vector_norm
      (length (elems qubit_reference (participant * fin)
        (` (projT1 q4_state)))) 2 Houtdim1_q4
      (@Mmult (2 ^ length (elems qubit_reference (participant * fin)
          (` (projT1 q4_state))))
        (2 ^ length (elems qubit_reference (participant * fin)
          (` (projT1 q4_state)))) 1
        (proj 0 (length (elems qubit_reference (participant * fin)
            (` (projT1 q4_state)))) y)
        (` (projT2 q4_state)))) as Hnorm_transport2.
    exact (eq_trans (eq_sym Hnorm_transport2) Hzero_transport).
  }
  assert (Hraw2_nonzero :
    @Mmult 2 4 1 (remove_measured_wire_operator 1 0 y)
      (@Mmult 4 4 1 (proj 0 2 y) m1) <> Zero).
  { exact (@qt_remove_projected_nonzero
      1 0 y m1 ltac:(lia) Hm1wf Hnonzero_pre2). }
  assert (Hraw2wf : @WF_Matrix 2 1
      (@Mmult 2 4 1 (remove_measured_wire_operator 1 0 y)
        (@Mmult 4 4 1 (proj 0 2 y) m1))).
  {
    apply WF_mult.
    - pose proof (remove_measured_wire_operator_wf 1 0 y ltac:(lia)) as Hwf.
      cbn [Nat.pow] in Hwf; exact Hwf.
    - apply WF_mult.
      + pose proof (WF_proj 0 2 y) as Hwf.
        cbn [Nat.pow] in Hwf; exact Hwf.
      + exact Hm1wf.
  }
  assert (Houtdim2_q6 : length (elems qubit_reference (participant * fin)
      (` (projT1 q6_state))) = 1).
  { unfold q6_state; exact Houtdim2. }
  assert (Hlenqout : length (elems qubit_reference (participant * fin)
      (` (projT1 qout))) = 1).
  { exact Hqoutlen. }
  set (out := transport_state_vector Hlenqout (` (projT2 qout))).
  assert (Hq6vec_m2 : ` (projT2 q6_state) = m2).
  { unfold m2; symmetry.
    exact (FunctionalCorrectnessHelpers.transport_state_vector_value
      _ _ Houtdim2 (` (projT2 q6_state))). }
  assert (Houtm2 : out = QTPathHelperDefinitions.qt_correction x y × m2).
  {
    unfold out.
    rewrite (Houtvec Houtdim2_q6 Hlenqout).
    assert (Hq6cast : transport_state_vector Houtdim2_q6 (` (projT2 q6_state)) = m2).
    {
      unfold m2.
      replace Houtdim2 with Houtdim2_q6 by apply proof_irrelevance.
      reflexivity.
    }
    apply (f_equal (fun v : Matrix 2 1 =>
      @Mmult 2 2 1 (QTPathHelperDefinitions.qt_correction x y) v)).
    exact Hq6cast.
  }
  assert (Hm2wf : @state_vector_wf 1 m2).
  {
    rewrite Hm2canonical.
    exact (@normalize_removed_wire_wf 1
      (@Mmult 2 4 1 (remove_measured_wire_operator 1 0 y)
        (@Mmult 4 4 1 (proj 0 2 y) m1)) Hraw2wf Hraw2_nonzero).
  }
  assert (Houtwf : @state_vector_wf 1 out).
  {
    unfold out.
    apply transport_state_vector_wf.
    exact (proj2_sig (projT2 qout)).
  }
  assert (Houtcanonical : out = QTPathHelperDefinitions.qt_correction x y × m2).
  { exact Houtm2. }
  pose proof (QTPathHelperDefinitions.qt_normalized_branch_exact
    input pre m1 m2 out x y Hinputwf Hprewf eq_refl Hm1canonical
    Hm1wf Hm2canonical Hraw1_nonzero Hraw2_nonzero Houtcanonical Houtwf)
    as Hbranchresult.
  assert (Hmulti_vec : ` (projT2 s''0.1) =
      proj1_sig (projT2 (transfer_qubit_from_lookup
        (` (projT1 qout)) (proj2_sig (projT1 qout))
        (` (projT2 qout)) (proj2_sig (projT2 qout))
        Env v'2 old2 n4 Hlookup4))).
  { exact (qt_multistep_from_ends_vector _ _ _ _ _ Htail_ends Htail). }
  rewrite <- H5, <- H19, Hmulti_vec.
  rewrite (@FunctionalCorrectnessHelpers.transfer_qubit_from_lookup_vector
    (` (projT1 qout)) (proj2_sig (projT1 qout))
    (` (projT2 qout)) (proj2_sig (projT2 qout))
    Env v'2 old2 n4 Hlookup4).
  assert (Houtqout : out = ` (projT2 qout)).
  { unfold out; apply FunctionalCorrectnessHelpers.transport_state_vector_value. }
  rewrite <- Houtqout, Hbranchresult.
  unfold input.
  exact (@FunctionalCorrectnessHelpers.transport_state_vector_value
    (length (elems qubit_reference (participant * fin)
      (` (projT1 starting_qstate)))) 1 Hstarting_length
    (` (projT2 starting_qstate))).
Qed.

Lemma qt_delayed_measurements_one_wire : forall
  (qmap : finite_map qubit_reference (participant * fin)) (Hqmap : quantum_map_wf qmap)
  (qvec : state_vector (length (elems qubit_reference (participant * fin) qmap))) (Hqvec : state_vector_wf qvec)
  (HlenA : length (elems qubit_reference (participant * fin) qmap) = 3)
  (qfirst : qubit_reference) (n1 : fin) (x : bool)
  (Hprob1 : {prob : R | (prob > 0)%R})
  (Hlookup1 : qmap qfirst = Some (Alice,n1))
  (Hlen1 : 0 < length (elems qubit_reference (participant * fin) qmap))
  (Hnonzero1 : norm (proj n1 (length (elems qubit_reference (participant * fin) qmap)) x × qvec) <> 0%R)
  (qmid : quantum_state)
  (Hmeasure1 : (Hprob1,qmid) = measure_qubit_from_nonzero qmap Hqmap qvec Hqvec qfirst Alice n1 x Hlookup1 Hlen1 Hnonzero1)
  (qsecond : qubit_reference) (n2 : fin) (y : bool)
  (Hprob2 : {prob : R | (prob > 0)%R})
  (Hlookup2 : (` (projT1 qmid)) qsecond = Some (Alice,n2))
  (Hlen2 : 0 < length (elems qubit_reference (participant * fin) (` (projT1 qmid))))
  (Hnonzero2 : norm (proj n2 (length (elems qubit_reference (participant * fin) (` (projT1 qmid)))) y × ` (projT2 qmid)) <> 0%R)
  (qout : quantum_state)
  (Hmeasure2 : (Hprob2,qout) = measure_qubit_from_nonzero (` (projT1 qmid)) (proj2_sig (projT1 qmid)) (` (projT2 qmid)) (proj2_sig (projT2 qmid)) qsecond Alice n2 y Hlookup2 Hlen2 Hnonzero2),
  length (elems qubit_reference (participant * fin) (` (projT1 qout))) = 1.
Proof.
  intros qmap Hqmap qvec Hqvec HlenA qfirst n1 x Hprob1 Hlookup1 Hlen1 Hnonzero1 qmid Hmeasure1 qsecond n2 y Hprob2 Hlookup2 Hlen2 Hnonzero2 qout Hmeasure2.
  injection Hmeasure1 as Hprob1_eq Hmid_eq.
  pose proof (@measure_qubit_nonzero_map qmap Hqmap qvec Hqvec qfirst Alice n1 x Hlookup1 Hlen1 Hnonzero1) as Hmap1.
  pose proof (@remove_and_reindex_qubit_map_length qmap qfirst Alice n1 Hlookup1) as Hremoved1.
  assert (Hlenmid_measure : length (elems qubit_reference (participant * fin)
      (` (projT1 (snd (measure_qubit_nonzero qmap Hqmap qvec Hqvec qfirst Alice n1 x Hlookup1 Hlen1 Hnonzero1))))) = 2).
  { rewrite Hmap1.
    transitivity (Nat.pred (length (elems qubit_reference (participant * fin) qmap))).
    - exact Hremoved1.
    - rewrite HlenA; reflexivity. }
  assert (Hlenmid : length (elems qubit_reference (participant * fin) (` (projT1 qmid))) = 2).
  { rewrite Hmid_eq. cbn [measure_qubit_from_nonzero]. exact Hlenmid_measure. }
  injection Hmeasure2 as Hprob2_eq Hout_eq.
  pose proof (@measure_qubit_nonzero_map
    (` (projT1 qmid)) (proj2_sig (projT1 qmid))
    (` (projT2 qmid)) (proj2_sig (projT2 qmid))
    qsecond Alice n2 y Hlookup2 Hlen2 Hnonzero2) as Hmap2.
  pose proof (@remove_and_reindex_qubit_map_length (` (projT1 qmid))
    qsecond Alice n2 Hlookup2) as Hremoved2.
  assert (Hlenout_measure : length (elems qubit_reference (participant * fin)
      (` (projT1 (snd (measure_qubit_nonzero
        (` (projT1 qmid)) (proj2_sig (projT1 qmid))
        (` (projT2 qmid)) (proj2_sig (projT2 qmid))
        qsecond Alice n2 y Hlookup2 Hlen2 Hnonzero2))))) = 1).
  { rewrite Hmap2, Hremoved2, Hlenmid; reflexivity. }
  assert (Hlenout : length (elems qubit_reference (participant * fin) (` (projT1 qout))) = 1).
  { rewrite Hout_eq. cbn [measure_qubit_from_nonzero]. exact Hlenout_measure. }
  exact Hlenout.
Qed.

Definition qt_delayed_tail_session (v : qubit_reference) : session :=
  insert
    (insert
      (insert
        (insert
          (insert
            (insert empty_fmap Source (p_end []))
            Env (p_recv Bob (slist_x (p_end [Process.Var 0]))))
          Alice (p_end []))
        Bob ((Env) .+ l_Env_B <. Val (QVal v) .>; (p_end [])))
      Env (p_end [Val (QVal v)]))
    Bob (p_end []).
Lemma qt_delayed_tail_session_end_entries : forall v p,
  qt_delayed_tail_session v p = None \/
  exists lz, qt_delayed_tail_session v p = Some (p_end lz).
Proof.
  intros v p.
  unfold qt_delayed_tail_session.
  cbn [FMap.m].
  destruct (participant_dec p Bob) as [->|Hnb].
  - rewrite FMap.insert_eq. right; exists []; reflexivity.
  - rewrite FMap.insert_neq in * by solve [congruence | (intro Hneq; inversion Hneq)].
    destruct (participant_dec p Env) as [->|Hne].
    + rewrite FMap.insert_eq. right; exists [Val (QVal v)]; reflexivity.
    + rewrite FMap.insert_neq in * by solve [congruence | (intro Hneq; inversion Hneq)].
      rewrite FMap.insert_neq in * by solve [congruence | (intro Hneq; inversion Hneq)].
      destruct (participant_dec p Alice) as [->|Hna].
      * rewrite FMap.insert_eq. right; exists []; reflexivity.
      * rewrite FMap.insert_neq in * by solve [congruence | (intro Hneq; inversion Hneq)].
        destruct (participant_dec p Source) as [->|Hns].
        -- simpl; right; exists []; reflexivity.
        -- repeat (rewrite FMap.insert_neq in * by solve [congruence | (intro Hneq; inversion Hneq)]).
           simpl; left; reflexivity.
Qed.

Lemma QuantumTeleportation_correct_goal_1 :
  forall
    (starting_qstate : quantum_state)
    (end_state : state)
    (actions : list action)
    (Hstarting_length : length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))) = 1)
    (s'' : state)
    (H5 : ` (projT2 s''.1) = ` (projT2 end_state.1))
    (v'0 : qubit_reference)
    (H2 : (` (projT1 starting_qstate)) v'0 = Some (Env, 0))
    (la0 : list action)
    (s0 : session)
    (v' : qubit_reference)
    (Hfresh : ~ In v' (map fst (elems qubit_reference (participant * fin) (` (projT1 starting_qstate)))))
    (s : session)
    (s2 : session)
    (v'2 : qubit_reference)
    (Hfresh0 : ~ In v'2 (map fst (elems qubit_reference (participant * fin) (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))))))))
    (s1 : session)
    (s''0 : state)
    (H4 : finished s''0.2)
    (H19 : ` (projT2 s''0.1) = ` (projT2 s''.1))
    (la : list action)
    (q0 : quantum_state)
    (s4 : session)
    (s3 : session)
    (lq : list qubit_reference)
    (Hlen : length lq = 1)
    (Hdim : 1 > 0)
    (H32 : apply_unitary (insert (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))))) v'2 (Source, length (elems qubit_reference (participant * fin) (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate)))))))) (Primitives.add_new_qubit_obligation_1 (add_new_qubit starting_qstate Source v' Hfresh) Source v'2 Hfresh0) (@kron (2 ^ (length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))) + 1)) 1 2 1 (@kron (2 ^ length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate)))) 1 2 1 (` (projT2 starting_qstate)) ∣0⟩) ∣0⟩) (Primitives.add_new_qubit_obligation_2 (add_new_qubit starting_qstate Source v' Hfresh) Source v'2 Hfresh0) U_H lq Hlen Hdim = Some q0)
    (H31 : [Val (QVal v')] = map (fun z : qubit_reference => Val (QVal z)) lq)
    (H34 : NoDup lq)
    (H35 : Forall (fun q : qubit_reference => exists n : fin, insert (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))))) v'2 (Source, length (elems qubit_reference (participant * fin) (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))))))) q = Some (Source, n)) lq)
    (q3 : quantum_state)
    (s6 : session)
    (s5 : session)
    (lq0 : list qubit_reference)
    (Hlen0 : length lq0 = 2)
    (Hdim0 : 2 > 0)
    (H : List.cons (Val (QVal v')) (List.cons (Val (QVal v'2)) List.nil) = map (fun z : qubit_reference => Val (QVal z)) lq0)
    (H38 : apply_unitary (` (projT1 q0)) (proj2_sig (projT1 q0)) (` (projT2 q0)) (proj2_sig (projT2 q0)) U_CNOT lq0 Hlen0 Hdim0 = Some q3)
    (H39 : NoDup lq0)
    (H40 : Forall (fun q : qubit_reference => exists n : fin, (` (projT1 q0)) q = Some (Source, n)) lq0)
    (s8 : session)
    (old : participant)
    (n : fin)
    (Hlookup : (` (projT1 q3)) v' = Some (old, n))
    (s7 : session)
    (s10 : session)
    (old0 : participant)
    (n0 : fin)
    (Hlookup0 : insert (` (projT1 q3)) v' (Alice, n) v'0 = Some (old0, n0))
    (s9 : session)
    (q : quantum_state)
    (s11 : session)
    (lq1 : list qubit_reference)
    (Hlen1 : length lq1 = 2)
    (Hdim1 : 2 > 0)
    (H37 : List.cons (Val (QVal v'0)) (List.cons (Val (QVal v')) List.nil) = map (fun z : qubit_reference => Val (QVal z)) lq1)
    (H42 : apply_unitary (insert (insert (` (projT1 q3)) v' (Alice, n)) v'0 (Alice, n0)) (Primitives.transfer_qubit_obligation_2 (insert (` (projT1 q3)) v' (Alice, n)) (Primitives.transfer_qubit_obligation_2 (` (projT1 q3)) (proj2_sig (projT1 q3)) Alice v' old n (eq_sym Hlookup)) Alice v'0 old0 n0 (eq_sym Hlookup0)) (` (projT2 q3)) (Primitives.transfer_qubit_obligation_3 (insert (` (projT1 q3)) v' (Alice, n)) (Primitives.transfer_qubit_obligation_2 (` (projT1 q3)) (proj2_sig (projT1 q3)) Alice v' old n (eq_sym Hlookup)) (` (projT2 q3)) (Primitives.transfer_qubit_obligation_3 (` (projT1 q3)) (proj2_sig (projT1 q3)) (` (projT2 q3)) (proj2_sig (projT2 q3)) Alice v' old n (eq_sym Hlookup)) Alice v'0 old0 n0 (eq_sym Hlookup0)) U_CNOT lq1 Hlen1 Hdim1 = Some q)
    (H55 : NoDup lq1)
    (H56 : Forall (fun q : qubit_reference => exists n1 : fin, insert (insert (` (projT1 q3)) v' (Alice, n)) v'0 (Alice, n0) q = Some (Alice, n1)) lq1)
    (q1 : quantum_state)
    (s12 : session)
    (lq2 : list qubit_reference)
    (Hlen2 : length lq2 = 1)
    (Hdim2 : 1 > 0)
    (H47 : [Val (QVal v'0)] = map (fun z : qubit_reference => Val (QVal z)) lq2)
    (H58 : apply_unitary (` (projT1 q)) (proj2_sig (projT1 q)) (` (projT2 q)) (proj2_sig (projT2 q)) U_H lq2 Hlen2 Hdim2 = Some q1)
    (H60 : NoDup lq2)
    (H61 : Forall (fun q0 : qubit_reference => exists n : fin, (` (projT1 q)) q0 = Some (Alice, n)) lq2)
    (q4 : quantum_state)
    (s13 : session)
    (pi1 : R)
    (q5 : qubit_reference)
    (n1 : fin)
    (Hprob : {prob : R | (prob > 0)%R})
    (Hlookup1 : (` (projT1 q1)) q5 = Some (Alice, n1))
    (Hlen3 : 0 < length (elems qubit_reference (participant * fin) (` (projT1 q1))))
    (Hnonzero : norm (proj n1 (length (elems qubit_reference (participant * fin) (` (projT1 q1)))) false × ` (projT2 q1)) <> 0%R)
    (H59 : Val (QVal v'0) = Val (QVal q5))
    (H63 : (Hprob, q4) = measure_qubit_from_nonzero (` (projT1 q1)) (proj2_sig (projT1 q1)) (` (projT2 q1)) (proj2_sig (projT2 q1)) q5 Alice n1 false Hlookup1 Hlen3 Hnonzero)
    (q6 : quantum_state)
    (s14 : session)
    (pi0 : R)
    (q7 : qubit_reference)
    (n2 : fin)
    (Hprob0 : {prob : R | (prob > 0)%R})
    (Hlookup2 : (` (projT1 q4)) q7 = Some (Alice, n2))
    (Hlen4 : 0 < length (elems qubit_reference (participant * fin) (` (projT1 q4))))
    (Hnonzero0 : norm (proj n2 (length (elems qubit_reference (participant * fin) (` (projT1 q4)))) false × ` (projT2 q4)) <> 0%R)
    (H64 : Val (QVal v') = Val (QVal q7))
    (H66 : (Hprob0, q6) = measure_qubit_from_nonzero (` (projT1 q4)) (proj2_sig (projT1 q4)) (` (projT2 q4)) (proj2_sig (projT2 q4)) q7 Alice n2 false Hlookup2 Hlen4 Hnonzero0)
    (s16 : session)
    (old1 : participant)
    (n3 : fin)
    (Hlookup3 : (` (projT1 q6)) v'2 = Some (old1, n3))
    (s15 : session)
    (s18 : session)
    (s17 : session)
    (s20 : session)
    (s19 : session)
    (s22 : session)
    (s21 : session)
    (s24 : session)
    (s23 : session)
    (q2 : quantum_state)
    (s26 : session)
    (s25 : session)
    (lq3 : list qubit_reference)
    (Hlen5 : length lq3 = 1)
    (Hdim3 : 1 > 0)
    (H98 : apply_unitary (insert (` (projT1 q6)) v'2 (Bob, n3)) (Primitives.transfer_qubit_obligation_2 (` (projT1 q6)) (proj2_sig (projT1 q6)) Bob v'2 old1 n3 (eq_sym Hlookup3)) (` (projT2 q6)) (Primitives.transfer_qubit_obligation_3 (` (projT1 q6)) (proj2_sig (projT1 q6)) (` (projT2 q6)) (proj2_sig (projT2 q6)) Bob v'2 old1 n3 (eq_sym Hlookup3)) U_I lq3 Hlen5 Hdim3 = Some q2)
    (H88 : [Val (QVal v'2)] = map (fun z : qubit_reference => Val (QVal z)) lq3)
    (H99 : NoDup lq3)
    (H100 : Forall (fun q : qubit_reference => exists n : fin, insert (` (projT1 q6)) v'2 (Bob, n3) q = Some (Bob, n)) lq3)
    (s28 : session)
    (r2 : R)
    (old2 : participant)
    (n4 : fin)
    (Hlookup4 : (` (projT1 q2)) v'2 = Some (old2, n4))
    (s27 : session)
    (H101 : multistep (transfer_qubit_from_lookup (` (projT1 q2)) (proj2_sig (projT1 q2)) (` (projT2 q2)) (proj2_sig (projT2 q2)) Env v'2 old2 n4 Hlookup4, insert (insert (insert (insert (insert (insert empty_fmap Env (p_recv Bob (slist_x (p_end [Process.Var 0])))) Source (p_end [])) Alice (p_end [])) Bob ((Env) .+ l_Env_B <. Val (QVal v'2) .>; (p_end []))) Env (p_end [Val (QVal v'2)])) Bob (p_end [])) la s''0 r2),
    proj1_sig (projT2 (fst end_state)) = proj1_sig (projT2 starting_qstate).
Proof.
  intros.
  destruct q0 as [qm_sig qv_sig].
  destruct qm_sig as [qmap0 Hqmap0].
  destruct qv_sig as [qvec0 Hqvec0].
  pose proof H32 as H32map.
  apply Happly_map in H32map.
  cbn in H32map.
  subst qmap0.
  pose proof H32 as H32vec.
  apply Hresult_vector in H32vec.
  destruct H32vec as [lp0 [Hget0 [Hidx0 Hq0vec]]].
  assert (Hv_v0 : v' <> v'0).
  { intro Heq; subst v'; apply Hfresh.
    apply In_fst_map with (ab := (v'0, (Env, 0))).
    apply (proj2 (specs qubit_reference (participant * fin) (` (projT1 starting_qstate)))); exact H2. }
  assert (Hv_v2 : v' <> v'2).
  { intro Heq; subst v'2; apply Hfresh0.
    apply In_fst_map with (ab := (v', (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate)))))).
    apply replace_or_add_In_eq. }
  apply qgt_qubit_list_singleton in H31; subst lq.
  rewrite Forall_forall in H35.
  specialize (H35 v' ltac:(simpl; auto)).
  destruct H35 as [nsource Hlookup_add].
  pose proof Hlookup_add as Hlookup_add_orig.
  rewrite insert_neq in Hlookup_add by congruence.
  rewrite insert_eq in Hlookup_add.
  rewrite Hstarting_length in Hlookup_add.
  inversion Hlookup_add; subst nsource.
  Transparent insert.
  assert (Haddlen1 : length (elems qubit_reference (participant * fin)
    (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate)))))) = 2).
  { unfold insert; simpl. rewrite replace_or_add_not_In_length.
    - rewrite Hstarting_length; reflexivity.
    - intros b Hin; apply Hfresh. apply In_fst_map with (ab := (v',b)); exact Hin. }
  assert (Haddlen2 : length (elems qubit_reference (participant * fin)
    (insert (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate)))))
      v'2 (Source, length (elems qubit_reference (participant * fin) (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))))))))) = 3).
  { unfold insert; simpl. rewrite replace_or_add_not_In_length.
    - rewrite replace_or_add_not_In_length.
      + rewrite Hstarting_length; reflexivity.
      + intros b Hin; apply Hfresh. apply In_fst_map with (ab := (v',b)); exact Hin.
    - intros b Hin; apply Hfresh0. apply In_fst_map with (ab := (v'2,b)); exact Hin. }
  assert (Hlp0 : lp0 = [(Source,1)]).
  { eapply qgt_get_all_values_singleton; [exact Hget0|exact Hlookup_add_orig]. }
  assert (Hmapidx0 : map snd lp0 = [1]) by (rewrite Hlp0; reflexivity).
  set (qmstart := (` (projT1 starting_qstate))).
  set (qm1 := insert qmstart v' (Source,
    length (elems qubit_reference (participant * fin) qmstart))).
  set (qmadd := insert qm1 v'2 (Source,
    length (elems qubit_reference (participant * fin) qm1))).
  assert (HidxOneBase : length [1] = 1 /\ NoDup [1] /\ Forall (fun i : nat => (i < 3)%nat) [1]).
  { split; [reflexivity|]. split.
    - constructor; [simpl; tauto|constructor].
    - constructor; [simpl; lia|constructor]. }
  assert (HidxOne : length [1] = 1 /\ NoDup [1] /\ Forall
    (fun i : nat => (i < length (elems qubit_reference (participant * fin) qmadd))%nat) [1]).
  { unfold qmadd, qm1, qmstart; rewrite Haddlen2; exact HidxOneBase. }
  pose proof (@QTPathHelperDefinitions.qt_base_to_ucom_ext
    (length (elems qubit_reference (participant * fin) qmadd)) 1 U_H
    (map snd lp0) [1] Hidx0 HidxOne Hmapidx0) as Hu0.
  unfold qmadd, qm1, qmstart in Hu0.
  match type of Hq0vec with
  | _ = @Mmult ?d ?d 1 _ ?input =>
      let f := constr:(fun op : Matrix d d => @Mmult d d 1 op input) in
      pose proof (f_equal f Hu0) as Hu0app
  end.
  pose proof (eq_trans Hq0vec Hu0app) as Hq0canonical.
  Opaque insert.
  Transparent U_H base_to_ucom ueval_r.
  unfold U_H in Hq0canonical.
  cbn [base_to_ucom uc_eval ueval_r] in Hq0canonical.
  simpl in Hq0canonical.
  rewrite hadamard_rotation in Hq0canonical.
  assert (HstartPlus : (length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))) + 2 = 3)%nat).
  { rewrite Hstarting_length; reflexivity. }
  assert (Hdim_start : length (elems qubit_reference (participant * fin) qmadd) =
    length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))) + 2).
  { unfold qmadd; exact (eq_trans Haddlen2 (eq_sym HstartPlus)). }
  match type of Hq0canonical with
  | _ = @Mmult ?d ?d 1 (pad_u ?n 1 hadamard) ?raw =>
      pose proof (@QTPathHelperDefinitions.qt_transport_pad_u n 3 Haddlen2 1 hadamard raw) as Hpad0
  end.
  pose proof (f_equal (transport_state_vector Haddlen2) Hq0canonical) as Hq0canonical3.
  pose proof (eq_trans Hq0canonical3 Hpad0) as Hq0canonicalPad.
  match type of Hq0canonical with
  | _ = @Mmult ?d ?d 1 (pad_u ?n 1 hadamard) ?raw =>
      pose proof (@QTPathHelperDefinitions.qt_transport_state_vector_compose
        n (length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))) + 2)
        3 Hdim_start HstartPlus raw) as Hinputcomp
  end.
  assert (Hdim_comp : eq_trans Hdim_start HstartPlus = Haddlen2) by apply proof_irrelevance.
  match type of Hinputcomp with
  | transport_state_vector (eq_trans Hdim_start HstartPlus) ?raw =
      transport_state_vector HstartPlus (transport_state_vector Hdim_start ?raw) =>
      pose proof (f_equal (fun e => transport_state_vector e raw) Hdim_comp) as Hcompcast;
      pose proof (@FunctionalCorrectnessHelpers.transport_state_vector_value
        _ _ Hdim_start raw) as Hrawdim;
      pose proof (f_equal (transport_state_vector HstartPlus) Hrawdim) as Hrawdim2;
      pose proof (eq_trans (eq_sym Hcompcast) (eq_trans Hinputcomp Hrawdim2)) as Hinputdim
  end.
  pose proof (f_equal (fun x : Matrix 8 1 =>
    @Mmult 8 8 1 (pad_u 3 1 hadamard) x) Hinputdim) as Hinputdimapp.
  pose proof (eq_trans Hq0canonicalPad Hinputdimapp) as Hq0factorpre.
  pose proof (@QTPathHelperDefinitions.qt_append_zeros_transport
    (length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate)))) 3
    Hstarting_length HstartPlus (` (projT2 starting_qstate))
    (proj2_sig (projT2 starting_qstate))) as Happend.
  pose proof (f_equal (fun x : Matrix 8 1 =>
    @Mmult 8 8 1 (pad_u 3 1 hadamard) x) Happend) as Happendapp.
  pose proof (eq_trans Hq0factorpre Happendapp) as Hq0factor.
  pose proof H38 as H38map.
  eapply Happly_map in H38map.
  cbn in H38map.
  pose proof H38 as H38vec.
  eapply Hresult_vector in H38vec.
  destruct H38vec as [lp38 [Hget38 [Hidx38 Hq3vec]]].
  apply qgt_qubit_list_pair in H; subst lq0.
  pose proof H40 as H40forall.
  rewrite Forall_forall in H40forall.
  specialize (H40forall v' ltac:(simpl; auto)).
  destruct H40forall as [idxv Hq0v].
  pose proof Hq0v as Hq0vlookup.
  cbn in Hq0v.
  rewrite insert_neq in Hq0v by congruence.
  rewrite insert_eq in Hq0v.
  rewrite Hstarting_length in Hq0v.
  inversion Hq0v; subst idxv.
  pose proof H40 as H40forall2.
  rewrite Forall_forall in H40forall2.
  specialize (H40forall2 v'2 ltac:(simpl; auto)).
  destruct H40forall2 as [idxv2 Hq0v2].
  pose proof Hq0v2 as Hq0v2lookup.
  cbn in Hq0v2.
  rewrite insert_eq in Hq0v2.
  injection Hq0v2 as Hidxv2.
  assert (Hleninner : length (elems qubit_reference (participant * fin)
    (insert (` (projT1 starting_qstate)) v'
      (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate)))))) = 2).
  { exact Haddlen1. }
  assert (Hidxv2_2 : idxv2 = 2).
  { exact (eq_trans (eq_sym Hidxv2) Hleninner). }
  subst idxv2.
    assert (Hq0v2_concrete : qmadd v'2 = Some (Source,2)).
  { unfold qmadd, qm1, qmstart; rewrite insert_eq, Hleninner; reflexivity. }
  assert (Hlp38 : lp38 = List.cons (Source,1) (List.cons (Source,2) nil)).
  { eapply qgt_get_all_values_pair; [exact Hget38|exact Hq0vlookup|exact Hq0v2_concrete]. }
  assert (Hidx12 : length (List.cons 1 (List.cons 2 nil)) = 2 /\
    NoDup (List.cons 1 (List.cons 2 nil)) /\
    Forall (fun i : nat => (i < length (elems qubit_reference (participant * fin) qmadd))%nat)
      (List.cons 1 (List.cons 2 nil))).
  { unfold qmadd, qm1, qmstart; rewrite Haddlen2; split; [reflexivity|]. split.
    - repeat constructor; simpl; intuition congruence.
    - repeat constructor; simpl; lia. }
  assert (Hmapidx38 : map snd lp38 = List.cons 1 (List.cons 2 nil)).
  { rewrite Hlp38; reflexivity. }
  pose proof (@QTPathHelperDefinitions.qt_base_to_ucom_ext
    (length (elems qubit_reference (participant * fin) qmadd)) 2 U_CNOT
    (map snd lp38) (List.cons 1 (List.cons 2 nil))
    Hidx38 Hidx12 Hmapidx38) as Hcnotext.
  assert (Hbasecnot :
    uc_eval (` (base_to_ucom U_CNOT (List.cons 1 (List.cons 2 nil)) Hidx12)) =
    pad_ctrl (length (elems qubit_reference (participant * fin) qmadd)) 1 2 σx).
  { Transparent base_to_ucom ueval_r.
    cbn [base_to_ucom uc_eval ueval_r]; reflexivity. }
  pose proof (f_equal (transport_state_vector Haddlen2) Hq3vec) as Hq3vec_cast.
  pose proof (f_equal (fun op : Matrix (2 ^ length (elems qubit_reference (participant * fin) qmadd))
      (2 ^ length (elems qubit_reference (participant * fin) qmadd)) =>
      @Mmult (2 ^ length (elems qubit_reference (participant * fin) qmadd))
        (2 ^ length (elems qubit_reference (participant * fin) qmadd)) 1 op qvec0) Hcnotext) as Hcnotapp.
  pose proof (f_equal (transport_state_vector Haddlen2) Hcnotapp) as Hcnotappcast.
  pose proof (eq_trans Hq3vec_cast Hcnotappcast) as Hq3vec_cast1.
  pose proof (f_equal (fun op : Matrix (2 ^ length (elems qubit_reference (participant * fin) qmadd))
      (2 ^ length (elems qubit_reference (participant * fin) qmadd)) =>
      @Mmult (2 ^ length (elems qubit_reference (participant * fin) qmadd))
        (2 ^ length (elems qubit_reference (participant * fin) qmadd)) 1 op qvec0) Hbasecnot) as Hbasecnotapp.
  pose proof (f_equal (transport_state_vector Haddlen2) Hbasecnotapp) as Hbasecnotappcast.
  pose proof (eq_trans Hq3vec_cast1 Hbasecnotappcast) as Hq3vec_cast2.
  pose proof (@QTPathHelperDefinitions.qt_transport_pad_ctrl
    (length (elems qubit_reference (participant * fin) qmadd)) 3 Haddlen2
    1 2 σx qvec0) as Hctrlcast.
  pose proof (eq_trans Hq3vec_cast2 Hctrlcast) as Hq3vec_cast3.
  pose proof (f_equal (fun x : Matrix 8 1 =>
    @Mmult 8 8 1 (pad_ctrl 3 1 2 σx) x) Hq0factor) as Hq0ctrl.
  pose proof (eq_trans Hq3vec_cast3 Hq0ctrl) as Hq3_vector0.
  assert (Hq3_vector :
    transport_state_vector Haddlen2 (` (projT2 q3)) =
      QTPathHelperDefinitions.qt_epr_preparation ×
        transport_state_vector Hstarting_length (` (projT2 starting_qstate))).
  { unfold QTPathHelperDefinitions.qt_epr_preparation.
    repeat rewrite <- Mmult_assoc in Hq3_vector0.
    exact Hq3_vector0. }
  assert (Hv2v0 : v'2 <> v'0).
  { intro Heq; subst v'2; apply Hfresh0.
    apply In_fst_map with (ab := (v'0, (Env, 0))).
    apply replace_or_add_In_neq.
    - intro Heq; apply Hv_v0; symmetry; exact Heq.
    - apply (proj2 (specs qubit_reference (participant * fin)
        (` (projT1 starting_qstate)))); exact H2. }
  assert (Hq3v : (` (projT1 q3)) v' = Some (Source,1)).
  { rewrite H38map; exact Hq0vlookup. }
  assert (Hq3v0 : (` (projT1 q3)) v'0 = Some (Env,0)).
  { rewrite H38map; cbn.
    rewrite insert_neq by exact Hv2v0.
    rewrite insert_neq by exact Hv_v0.
    exact H2. }
  pose proof Hlookup as Hlookup_copy.
  rewrite Hq3v in Hlookup_copy.
  injection Hlookup_copy as HownerEq HnEq.
  symmetry in HownerEq, HnEq.
  pose proof Hlookup0 as Hlookup0_copy.
  rewrite insert_neq in Hlookup0_copy by congruence.
  rewrite Hq3v0 in Hlookup0_copy.
  injection Hlookup0_copy as Howner0Eq Hn0Eq.
  symmetry in Howner0Eq, Hn0Eq.
  assert (Hq3len : length (elems qubit_reference (participant * fin) (` (projT1 q3))) = 3).
  { rewrite H38map; exact Haddlen2. }
  assert (HlenA1 : length (elems qubit_reference (participant * fin)
    (insert (` (projT1 q3)) v' (Alice,n))) =
    length (elems qubit_reference (participant * fin) (` (projT1 q3)))).
  { eapply qgt_insert_preserves_length; exact Hlookup. }
  assert (HlenA2 : length (elems qubit_reference (participant * fin)
    (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0))) =
    length (elems qubit_reference (participant * fin)
      (insert (` (projT1 q3)) v' (Alice,n)))).
  { eapply qgt_insert_preserves_length; exact Hlookup0. }
  assert (HlenA : length (elems qubit_reference (participant * fin)
    (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0))) = 3).
  { rewrite HlenA2, HlenA1, Hq3len; reflexivity. }
  assert (HqA_v'0 :
    (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0)) v'0 = Some (Alice,0)).
  { rewrite insert_eq, Hn0Eq; reflexivity. }
  assert (HqA_v' :
    (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0)) v' = Some (Alice,1)).
  { rewrite insert_neq by congruence.
    rewrite insert_eq, HnEq; reflexivity. }
  apply qgt_qubit_list_pair in H37; subst lq1.
  destruct q as [qmsig qvsig].
  destruct qmsig as [qmapA HqmapA].
  destruct qvsig as [qvecA HqvecA].
  pose proof H42 as H42map.
  eapply Happly_map in H42map.
  cbn in H42map.
  subst qmapA.
  pose proof H42 as H42vec.
  eapply Hresult_vector in H42vec.
  destruct H42vec as [lp42 [Hget42 [Hidx42 Hqvec42]]].
  assert (Hlp42 : lp42 = List.cons (Alice,0) (List.cons (Alice,1) nil)).
  { eapply qgt_get_all_values_pair; [exact Hget42|exact HqA_v'0|exact HqA_v']. }
  assert (Hidx01 : length (List.cons 0 (List.cons 1 nil)) = 2 /\
    NoDup (List.cons 0 (List.cons 1 nil)) /\
    Forall (fun i : nat => (i < length (elems qubit_reference (participant * fin)
      (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0))))%nat)
      (List.cons 0 (List.cons 1 nil))).
  { rewrite HlenA; split; [reflexivity|]. split.
    - repeat constructor; simpl; intuition congruence.
    - repeat constructor; simpl; lia. }
  assert (Hmapidx42 : map snd lp42 = List.cons 0 (List.cons 1 nil)).
  { rewrite Hlp42; reflexivity. }
  pose proof (@QTPathHelperDefinitions.qt_base_to_ucom_ext
    (length (elems qubit_reference (participant * fin)
      (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0)))) 2 U_CNOT
    (map snd lp42) (List.cons 0 (List.cons 1 nil)) Hidx42 Hidx01 Hmapidx42)
    as Hcnotext42.
  assert (Hbasecnot42 :
    uc_eval (` (base_to_ucom U_CNOT (List.cons 0 (List.cons 1 nil)) Hidx01)) =
    pad_ctrl (length (elems qubit_reference (participant * fin)
      (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0)))) 0 1 σx).
  { cbn [base_to_ucom uc_eval ueval_r]; reflexivity. }
  match type of Hqvec42 with
  | _ = @Mmult ?d ?d 1 ?op ?raw =>
      pose proof (f_equal (fun u : Matrix d d => @Mmult d d 1 u raw) Hcnotext42) as Hcnotapp42;
      pose proof (f_equal (fun u : Matrix d d => @Mmult d d 1 u raw) Hbasecnot42) as Hbaseapp42;
      pose proof (f_equal (transport_state_vector HlenA) Hqvec42) as Hq42cast;
      pose proof (f_equal (transport_state_vector HlenA) Hcnotapp42) as Hcnotapp42cast;
      pose proof (eq_trans Hq42cast Hcnotapp42cast) as Hq42cast1;
      pose proof (f_equal (transport_state_vector HlenA) Hbaseapp42) as Hbaseapp42cast;
      pose proof (eq_trans Hq42cast1 Hbaseapp42cast) as Hq42cast2;
      pose proof (@QTPathHelperDefinitions.qt_transport_pad_ctrl
        (length (elems qubit_reference (participant * fin)
          (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0))))
        3 HlenA 0 1 σx raw) as Hctrl42cast;
      pose proof (eq_trans Hq42cast2 Hctrl42cast) as Hq42cast3
  end.
  assert (Hq3_casts :
    transport_state_vector HlenA (` (projT2 q3)) =
    transport_state_vector Haddlen2 (` (projT2 q3))).
  { transitivity (` (projT2 q3)).
    - apply FunctionalCorrectnessHelpers.transport_state_vector_value.
    - symmetry; apply FunctionalCorrectnessHelpers.transport_state_vector_value. }
  pose proof (f_equal (fun x : Matrix 8 1 =>
    @Mmult 8 8 1 (pad_ctrl 3 0 1 σx) x) Hq3_casts) as Hq3cnot.
  pose proof (eq_trans Hq42cast3 Hq3cnot) as Hq_after_cnot.
  destruct q1 as [q1msig q1vsig].
  destruct q1msig as [qmap1 Hqmap1].
  destruct q1vsig as [qvec1 Hqvec1].
  pose proof H58 as H58map.
  eapply Happly_map in H58map.
  cbn in H58map.
  subst qmap1.
  apply qgt_qubit_list_singleton in H47; subst lq2.
  pose proof H58 as H58vec.
  eapply Hresult_vector in H58vec.
  destruct H58vec as [lp58 [Hget58 [Hidx58 Hq1vec]]].
  assert (Hlp58 : lp58 = [(Alice,0)]).
  { eapply qgt_get_all_values_singleton; [exact Hget58|exact HqA_v'0]. }
  assert (HidxHad0 : length [0] = 1 /\ NoDup [0] /\
    Forall (fun i : nat => (i < length (elems qubit_reference (participant * fin)
      (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0))))%nat) [0]).
  { rewrite HlenA; simpl; split; [reflexivity|]. split.
    - constructor; [simpl; tauto|constructor].
    - constructor; [simpl; lia|constructor]. }
  assert (Hmapidx58 : map snd lp58 = [0]).
  { rewrite Hlp58; reflexivity. }
  pose proof (@QTPathHelperDefinitions.qt_base_to_ucom_ext
    (length (elems qubit_reference (participant * fin)
      (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0)))) 1 U_H
    (map snd lp58) [0] Hidx58 HidxHad0 Hmapidx58) as Hhadext.
  assert (Hbasehad0 :
    uc_eval (` (base_to_ucom U_H [0] HidxHad0)) =
      pad_u (length (elems qubit_reference (participant * fin)
        (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0)))) 0 hadamard).
  { Transparent U_H base_to_ucom ueval_r.
    unfold U_H.
    cbn [base_to_ucom uc_eval ueval_r].
    simpl.
    rewrite hadamard_rotation.
    reflexivity. }
  match type of Hq1vec with
  | _ = @Mmult ?d ?d 1 ?op ?raw =>
      pose proof (f_equal (fun u : Matrix d d => @Mmult d d 1 u raw) Hhadext) as Hhadapp;
      pose proof (f_equal (fun u : Matrix d d => @Mmult d d 1 u raw) Hbasehad0) as Hbasehadapp;
      pose proof (f_equal (transport_state_vector HlenA) Hq1vec) as Hq1cast;
      pose proof (f_equal (transport_state_vector HlenA) Hhadapp) as Hhadappcast;
      pose proof (eq_trans Hq1cast Hhadappcast) as Hq1cast1;
      pose proof (f_equal (transport_state_vector HlenA) Hbasehadapp) as Hbasehadappcast;
      pose proof (eq_trans Hq1cast1 Hbasehadappcast) as Hq1cast2;
      pose proof (@QTPathHelperDefinitions.qt_transport_pad_u
        (length (elems qubit_reference (participant * fin)
          (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0))))
        3 HlenA 0 hadamard raw) as Hhadcast;
      pose proof (eq_trans Hq1cast2 Hhadcast) as Hq1cast3
  end.
  pose proof (f_equal (fun x : Matrix 8 1 =>
    @Mmult 8 8 1 (pad_u 3 0 hadamard) x) Hq_after_cnot) as Hq_cnot_h.
  pose proof (eq_trans Hq1cast3 Hq_cnot_h) as Hpre0.
  repeat rewrite <- Mmult_assoc in Hpre0.
  pose proof (f_equal (fun x : Matrix 8 1 =>
    @Mmult 8 8 1 (pad_u 3 0 hadamard × pad_ctrl 3 0 1 σx) x)
    Hq3_vector) as Hpreappend.
  pose proof (eq_trans Hpre0 Hpreappend) as Hpre1.
  assert (Hpre :
    transport_state_vector HlenA qvec1 =
      QTPathHelperDefinitions.qt_alice_pre_measure ×
        (QTPathHelperDefinitions.qt_epr_preparation ×
          transport_state_vector Hstarting_length (` (projT2 starting_qstate)))).
  { unfold QTPathHelperDefinitions.qt_alice_pre_measure.
    exact Hpre1. }
  injection H63 as Hprob_eq Hq4eq.
  subst q4.
  assert (Hq5id : q5 = v'0).
  { injection H59 as Heq; symmetry; exact Heq. }
  assert (Hn1eq : n1 = 0).
  { pose proof Hlookup1 as Hlookup1_copy.
    change ((insert (insert (` (projT1 q3)) v' (Alice,n)) v'0
      (Alice,n0)) q5 = Some (Alice,n1)) in Hlookup1_copy.
    rewrite Hq5id in Hlookup1_copy.
    rewrite HqA_v'0 in Hlookup1_copy.
    inversion Hlookup1_copy; reflexivity. }
  pose proof (@measure_qubit_nonzero_map
    (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0))
    Hqmap1 qvec1 Hqvec1 q5 Alice n1 false Hlookup1 Hlen3 Hnonzero)
    as Hmap_measure1.
  pose proof (@remove_and_reindex_qubit_map_length
    (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0))
    q5 Alice n1 Hlookup1) as Hremoved_len1.
  assert (Houtdim1 : length (elems qubit_reference (participant * fin)
      (proj1_sig (projT1 (snd (measure_qubit_nonzero
        (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0))
        Hqmap1 qvec1 Hqvec1 q5 Alice n1 false Hlookup1 Hlen3 Hnonzero))))) = 2).
  { rewrite Hmap_measure1.
    transitivity (Nat.pred (length (elems qubit_reference (participant * fin)
      (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0))))).
    - exact Hremoved_len1.
    - rewrite HlenA; reflexivity. }
  set (input := transport_state_vector Hstarting_length (` (projT2 starting_qstate))).
  set (pre := @Mmult 8 8 1 QTPathHelperDefinitions.qt_alice_pre_measure
    (@Mmult 8 2 1 QTPathHelperDefinitions.qt_epr_preparation input)).
  assert (Hinputwf : @state_vector_wf 1 input).
  { unfold input; apply transport_state_vector_wf; exact (proj2_sig (projT2 starting_qstate)). }
  assert (Hprewf : @WF_Matrix 8 1 pre).
  {
    pose proof (@transport_state_vector_wf
      (length (elems qubit_reference (participant * fin)
        (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0))))
      3 HlenA qvec1 Hqvec1) as Hq1wf.
    rewrite Hpre in Hq1wf.
    unfold pre.
    exact (proj1 Hq1wf).
  }
  set (m1 := transport_state_vector Houtdim1
    (proj1_sig (projT2 (snd (measure_qubit_nonzero
      (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0))
      Hqmap1 qvec1 Hqvec1 q5 Alice n1 false Hlookup1 Hlen3 Hnonzero))))).
  set (q4_state := snd (measure_qubit_from_nonzero
    (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0))
    Hqmap1 qvec1 Hqvec1 q5 Alice n1 false Hlookup1 Hlen3 Hnonzero)).
  assert (Houtdim1_q4 : length (elems qubit_reference (participant * fin)
      (` (projT1 q4_state))) = 2).
  { unfold q4_state; exact Houtdim1. }
  assert (Hq4vec_m1 : transport_state_vector Houtdim1_q4 (` (projT2 q4_state)) = m1).
  { unfold m1, q4_state; f_equal; apply proof_irrelevance. }
  pose proof (@qt_measure_output_vector_fixed 2
    (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0))
    Hqmap1 qvec1 Hqvec1 q5 Alice n1 false Hlookup1 Hlen3 Hnonzero HlenA
    Houtdim1) as Hm1.
  unfold m1 in Hm1.
  assert (Hm1canonical : m1 = @normalize_removed_wire 2
    (@Mmult 4 8 1 (remove_measured_wire_operator 2 0 false)
      (@Mmult 8 8 1 (proj 0 3 false) pre))).
  {
    unfold m1.
    transitivity (@normalize_removed_wire 2
      (@Mmult 4 8 1 (remove_measured_wire_operator 2 n1 false)
        (@Mmult 8 8 1 (proj n1 3 false)
          (transport_state_vector HlenA qvec1)))).
    - exact Hm1.
    - f_equal; rewrite Hpre, Hn1eq; reflexivity.
  }
  assert (Hprojcast1 : transport_state_vector HlenA
      (@Mmult
        (2 ^ length (elems qubit_reference (participant * fin)
          (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0))))
        (2 ^ length (elems qubit_reference (participant * fin)
          (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0))))
        1
        (proj 0 (length (elems qubit_reference (participant * fin)
          (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0)))) false)
        qvec1) =
      @Mmult 8 8 1 (proj 0 3 false) pre).
  {
    pose proof (@transport_state_vector_proj
      (length (elems qubit_reference (participant * fin)
        (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0))))
      3 HlenA 0 false qvec1) as Hcast.
    rewrite Hpre in Hcast.
    exact Hcast.
  }
  assert (Hnonzero_pre1 : norm (@Mmult 8 8 1 (proj 0 3 false) pre) <> 0%R).
  {
    intro Hzero.
    pose proof Hnonzero as Hnonzero_raw.
    change (norm
      (proj n1 (length (elems qubit_reference (participant * fin)
        (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0))))
        false × qvec1) <> 0%R) in Hnonzero_raw.
    rewrite Hn1eq in Hnonzero_raw.
    apply Hnonzero_raw.
    rewrite <- Hprojcast1 in Hzero.
    pose proof (@transport_state_vector_norm
      (length (elems qubit_reference (participant * fin)
        (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0))))
      3 HlenA
      (@Mmult
        (2 ^ length (elems qubit_reference (participant * fin)
          (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0))))
        (2 ^ length (elems qubit_reference (participant * fin)
          (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0))))
        1
        (proj 0 (length (elems qubit_reference (participant * fin)
          (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0)))) false)
        qvec1)) as Hnorm_transport.
    exact (eq_trans (eq_sym Hnorm_transport) Hzero).
  }
  assert (Hraw1_nonzero :
    @Mmult 4 8 1 (remove_measured_wire_operator 2 0 false)
      (@Mmult 8 8 1 (proj 0 3 false) pre) <> Zero).
  { exact (@qt_remove_projected_nonzero
      2 0 false pre ltac:(lia) Hprewf Hnonzero_pre1). }
  assert (Hq7id : q7 = v').
  { injection H64 as Heq; symmetry; exact Heq. }
  assert (Hneq_q5 : v' <> q5).
  { rewrite Hq5id; exact Hv_v0. }
  assert (Hlookup2_removed :
    remove_and_reindex_qubit_map
      (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0))
      q5 n1 v' = Some (Alice,n2)).
  {
    pose proof Hlookup2 as Hlookup2_copy.
    change (remove_and_reindex_qubit_map
      (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0))
      q5 n1 q7 = Some (Alice,n2)) in Hlookup2_copy.
    rewrite Hq7id in Hlookup2_copy.
    exact Hlookup2_copy.
  }
  destruct (@Hremove_lookup_inv
    (insert (insert (` (projT1 q3)) v' (Alice,n)) v'0 (Alice,n0))
    v' q5 n1 Alice n2 Hneq_q5 Hlookup2_removed)
    as [nold [Hlookup_v' Hshift_n2]].
  assert (Hnold1 : nold = 1).
  { rewrite HqA_v' in Hlookup_v'; inversion Hlookup_v'; reflexivity. }
  assert (Hn2eq : n2 = 0).
  { rewrite Hn1eq, Hnold1 in Hshift_n2.
    cbn [shift_wire_index] in Hshift_n2.
    exact Hshift_n2. }
  injection H66 as Hprob0_eq Hq6eq.
  subst q6.
  pose proof (@measure_qubit_nonzero_map
    (` (projT1 q4_state)) (proj2_sig (projT1 q4_state))
    (` (projT2 q4_state)) (proj2_sig (projT2 q4_state))
    q7 Alice n2 false Hlookup2 Hlen4 Hnonzero0) as Hmap_measure2.
  pose proof (@remove_and_reindex_qubit_map_length
    (` (projT1 q4_state)) q7 Alice n2 Hlookup2) as Hremoved_len2.
  assert (Houtdim2 : length (elems qubit_reference (participant * fin)
      (` (projT1 (snd (measure_qubit_nonzero
        (` (projT1 q4_state)) (proj2_sig (projT1 q4_state))
        (` (projT2 q4_state)) (proj2_sig (projT2 q4_state))
        q7 Alice n2 false Hlookup2 Hlen4 Hnonzero0))))) = 1).
  {
    rewrite Hmap_measure2.
    transitivity (Nat.pred (length (elems qubit_reference
      (participant * fin) (` (projT1 q4_state))))).
    - exact Hremoved_len2.
    - rewrite Houtdim1_q4; reflexivity.
  }
  set (q6_state := snd (measure_qubit_nonzero
    (` (projT1 q4_state)) (proj2_sig (projT1 q4_state))
    (` (projT2 q4_state)) (proj2_sig (projT2 q4_state))
    q7 Alice n2 false Hlookup2 Hlen4 Hnonzero0)).
  set (m2 := transport_state_vector Houtdim2
    (` (projT2 (snd (measure_qubit_nonzero
      (` (projT1 q4_state)) (proj2_sig (projT1 q4_state))
      (` (projT2 q4_state)) (proj2_sig (projT2 q4_state))
      q7 Alice n2 false Hlookup2 Hlen4 Hnonzero0))))).
  pose proof (@qt_measure_output_vector_fixed 1
    (` (projT1 q4_state)) (proj2_sig (projT1 q4_state))
    (` (projT2 q4_state)) (proj2_sig (projT2 q4_state))
    q7 Alice n2 false Hlookup2 Hlen4 Hnonzero0 Houtdim1_q4 Houtdim2)
    as Hm2.
  unfold m2 in Hm2.
  assert (Hm2canonical : m2 = @normalize_removed_wire 1
    (@Mmult 2 4 1 (remove_measured_wire_operator 1 0 false)
      (@Mmult 4 4 1 (proj 0 2 false) m1))).
  {
    unfold m2.
    transitivity (@normalize_removed_wire 1
      (@Mmult 2 4 1 (remove_measured_wire_operator 1 n2 false)
        (@Mmult 4 4 1 (proj n2 2 false)
          (transport_state_vector Houtdim1_q4 (` (projT2 q4_state)))))).
    - exact Hm2.
    - f_equal; rewrite Hn2eq, Hq4vec_m1; reflexivity.
  }
  assert (Hm1wf : @WF_Matrix 4 1 m1).
  {
    pose proof (@transport_state_vector_wf
      (length (elems qubit_reference (participant * fin)
      (` (projT1 q4_state)))) 2 Houtdim1_q4
      (` (projT2 q4_state)) (proj2_sig (projT2 q4_state))) as Hwf.
    rewrite <- Hq4vec_m1.
    exact (proj1 Hwf).
  }
  assert (Hnonzero_pre2 : norm (@Mmult 4 4 1 (proj 0 2 false) m1) <> 0%R).
  {
    intro Hzero.
    pose proof Hnonzero0 as Hnonzero0_raw.
    rewrite Hn2eq in Hnonzero0_raw.
    apply Hnonzero0_raw.
    pose proof (@transport_state_vector_proj
      (length (elems qubit_reference (participant * fin)
      (` (projT1 q4_state)))) 2 Houtdim1_q4 n2 false
      (` (projT2 q4_state))) as Hprojcast2.
    rewrite Hn2eq in Hprojcast2.
    rewrite <- Hq4vec_m1 in Hzero.
    pose proof (f_equal (fun z : Matrix 4 1 => @norm 4 z) Hprojcast2)
      as Hnormcast2.
    assert (Hzero_transport :
      @norm 4 (transport_state_vector Houtdim1_q4
        (@Mmult
          (2 ^ length (elems qubit_reference (participant * fin)
            (` (projT1 q4_state))))
          (2 ^ length (elems qubit_reference (participant * fin)
            (` (projT1 q4_state)))) 1
          (proj 0 (length (elems qubit_reference (participant * fin)
            (` (projT1 q4_state)))) false)
        (` (projT2 q4_state)))) = 0%R).
    { exact (eq_trans Hnormcast2 Hzero). }
    pose proof (@transport_state_vector_norm
      (length (elems qubit_reference (participant * fin)
        (` (projT1 q4_state)))) 2 Houtdim1_q4
      (@Mmult (2 ^ length (elems qubit_reference (participant * fin)
          (` (projT1 q4_state))))
        (2 ^ length (elems qubit_reference (participant * fin)
          (` (projT1 q4_state)))) 1
        (proj 0 (length (elems qubit_reference (participant * fin)
            (` (projT1 q4_state)))) false)
        (` (projT2 q4_state)))) as Hnorm_transport2.
    exact (eq_trans (eq_sym Hnorm_transport2) Hzero_transport).
  }
  assert (Hraw2_nonzero :
    @Mmult 2 4 1 (remove_measured_wire_operator 1 0 false)
      (@Mmult 4 4 1 (proj 0 2 false) m1) <> Zero).
  { exact (@qt_remove_projected_nonzero
      1 0 false m1 ltac:(lia) Hm1wf Hnonzero_pre2). }
  assert (Hraw2wf : @WF_Matrix 2 1
      (@Mmult 2 4 1 (remove_measured_wire_operator 1 0 false)
        (@Mmult 4 4 1 (proj 0 2 false) m1))).
  {
    apply WF_mult.
    - pose proof (remove_measured_wire_operator_wf 1 0 false ltac:(lia)) as Hwf.
      cbn [Nat.pow] in Hwf; exact Hwf.
    - apply WF_mult.
      + pose proof (WF_proj 0 2 false) as Hwf.
        cbn [Nat.pow] in Hwf; exact Hwf.
      + exact Hm1wf.
  }
  assert (Houtdim2_q6 : length (elems qubit_reference (participant * fin)
      (` (projT1 q6_state))) = 1).
  { unfold q6_state; exact Houtdim2. }
  assert (Hlookup3_q6 : (` (projT1 q6_state)) v'2 = Some (old1,n3)).
  { unfold q6_state; exact Hlookup3. }
  pose proof (@insert_existing_length (` (projT1 q6_state)) v'2 old1 n3 Bob
    Hlookup3_q6) as Hinsertlen.
  assert (Hleninsert : length (elems qubit_reference (participant * fin)
      (insert (` (projT1 q6_state)) v'2 (Bob,n3))) = 1).
  { transitivity (length (elems qubit_reference (participant * fin)
      (` (projT1 q6_state)))); [exact Hinsertlen|exact Houtdim2_q6]. }
  assert (Hmapq2 : proj1_sig (projT1 q2) =
      insert (` (projT1 q6_state)) v'2 (Bob,n3)).
  { unfold q6_state; eapply Happly_map; exact H98. }
  assert (Hlenq2 : length (elems qubit_reference (participant * fin)
      (` (projT1 q2))) = 1).
  { rewrite Hmapq2; exact Hleninsert. }
  pose proof (Hresult_vector _ _ _ _ 1 U_I lq3 Hlen5 Hdim3 q2 H98)
    as Hresultq2.
  destruct Hresultq2 as [lpn [Hgetq2 [Hidxq2 Hvecq2]]].
  pose proof (proj1 Hidxq2) as Hidxlen.
  pose proof (proj1 (proj2 Hidxq2)) as Hidxnd.
  pose proof (proj2 (proj2 Hidxq2)) as Hidxbounds.
  assert (Hmapidxq2 : map snd lpn = [0]).
  {
    destruct lpn as [|[owner idx] rest]; simpl in Hidxlen; [discriminate|].
    destruct rest as [|pair rest]; simpl in Hidxlen; [|discriminate].
    simpl.
    assert (Hidxlt : idx < length (elems qubit_reference (participant * fin)
      (insert (` (projT1 q6_state)) v'2 (Bob,n3)))).
    { simpl in Hidxbounds; inversion Hidxbounds; assumption. }
    rewrite Hleninsert in Hidxlt.
    simpl in Hidxlt; assert (idx = 0) by lia; subst idx; reflexivity.
  }
  assert (HidxI : length [0] = 1 /\ NoDup [0] /\
      Forall (fun i => i < length (elems qubit_reference (participant * fin)
        (insert (` (projT1 q6_state)) v'2 (Bob,n3)))) [0]).
  {
    split; [reflexivity|].
    split; [constructor; [simpl; tauto|constructor]|].
    constructor; [rewrite Hleninsert; simpl; lia|constructor].
  }
  pose proof (@QTPathHelperDefinitions.qt_base_to_ucom_ext
    (length (elems qubit_reference (participant * fin)
      (insert (` (projT1 q6_state)) v'2 (Bob,n3)))) 1 U_I (map snd lpn) [0]
    Hidxq2 HidxI Hmapidxq2) as HbaseIext.
  assert (HbaseI : uc_eval (` (base_to_ucom U_I [0] HidxI)) =
      I (2 ^ length (elems qubit_reference (participant * fin)
        (insert (` (projT1 q6_state)) v'2 (Bob,n3))))).
  { exact (@qt_U_I_eval_from_length
      (length (elems qubit_reference (participant * fin)
      (insert (` (projT1 q6_state)) v'2 (Bob,n3)))) Hleninsert HidxI). }
  Opaque base_to_ucom.
  assert (HbaseI_lpn : uc_eval
      (` (base_to_ucom U_I (map snd lpn) Hidxq2)) =
      I (2 ^ length (elems qubit_reference (participant * fin)
        (insert (` (projT1 q6_state)) v'2 (Bob,n3))))).
  { transitivity (uc_eval (` (base_to_ucom U_I [0] HidxI))).
    - exact HbaseIext.
    - exact HbaseI. }
  assert (Hq2vectorI : proj1_sig (projT2 q2) = ` (projT2 q6_state)).
  {
    rewrite Hvecq2.
    rewrite HbaseI_lpn.
    rewrite Mmult_1_l by exact
      (proj1
        (Primitives.transfer_qubit_obligation_3
          (` (projT1 q6_state)) (proj2_sig (projT1 q6_state))
          (` (projT2 q6_state)) (proj2_sig (projT2 q6_state))
          Bob v'2 old1 n3 (eq_sym Hlookup3_q6))).
    reflexivity.
  }
  set (out := transport_state_vector Hlenq2 (` (projT2 q2))).
  assert (Hq6vec_m2 : ` (projT2 q6_state) = m2).
  { unfold m2; symmetry.
    exact (FunctionalCorrectnessHelpers.transport_state_vector_value
      _ _ Houtdim2 (` (projT2 q6_state))). }
  assert (Houtm2 : out = m2).
  {
    unfold out.
    rewrite (FunctionalCorrectnessHelpers.transport_state_vector_value
      _ _ Hlenq2 (` (projT2 q2))).
    rewrite Hq2vectorI.
    exact Hq6vec_m2.
  }
  assert (Hm2wf : @state_vector_wf 1 m2).
  {
    rewrite Hm2canonical.
    exact (@normalize_removed_wire_wf 1
      (@Mmult 2 4 1 (remove_measured_wire_operator 1 0 false)
        (@Mmult 4 4 1 (proj 0 2 false) m1)) Hraw2wf Hraw2_nonzero).
  }
  assert (Houtwf : @state_vector_wf 1 out).
  { rewrite Houtm2; exact Hm2wf. }
  assert (Houtcanonical : out = QTPathHelperDefinitions.qt_correction false false × m2).
  {
    rewrite Houtm2.
    unfold QTPathHelperDefinitions.qt_correction; simpl.
    rewrite Mmult_1_l by exact (proj1 Hm2wf).
    reflexivity.
  }
  pose proof (QTPathHelperDefinitions.qt_normalized_branch_exact
    input pre m1 m2 out false false Hinputwf Hprewf eq_refl Hm1canonical
    Hm1wf Hm2canonical Hraw1_nonzero Hraw2_nonzero Houtcanonical Houtwf)
    as Hbranchresult.
  assert (Hmulti_vec : ` (projT2 s''0.1) =
      proj1_sig (projT2 (transfer_qubit_from_lookup
        (` (projT1 q2)) (proj2_sig (projT1 q2))
        (` (projT2 q2)) (proj2_sig (projT2 q2))
        Env v'2 old2 n4 Hlookup4))).
  {
    assert (Htail_ends : forall p,
      qt_tail_session v'2 p = None \/
      exists lz, qt_tail_session v'2 p = Some (p_end lz)).
    { apply qt_tail_session_end_entries. }
    change (multistep
      (transfer_qubit_from_lookup (` (projT1 q2)) (proj2_sig (projT1 q2))
        (` (projT2 q2)) (proj2_sig (projT2 q2)) Env v'2 old2 n4 Hlookup4,
       qt_tail_session v'2) la s''0 r2) in H101.
    exact (qt_multistep_from_ends_vector _ _ _ _ _ Htail_ends H101).
  }
  rewrite <- H5, <- H19, Hmulti_vec.
  rewrite (@FunctionalCorrectnessHelpers.transfer_qubit_from_lookup_vector
    (` (projT1 q2)) (proj2_sig (projT1 q2))
    (` (projT2 q2)) (proj2_sig (projT2 q2))
    Env v'2 old2 n4 Hlookup4).
  assert (Houtq2 : out = ` (projT2 q2)).
  { unfold out; apply FunctionalCorrectnessHelpers.transport_state_vector_value. }
  rewrite <- Houtq2, Hbranchresult.
  unfold input.
  exact (@FunctionalCorrectnessHelpers.transport_state_vector_value
    (length (elems qubit_reference (participant * fin)
      (` (projT1 starting_qstate)))) 1 Hstarting_length
    (` (projT2 starting_qstate))).
Qed.

Lemma QuantumTeleportation_correct_goal_2 :
  forall
    (starting_qstate : quantum_state)
    (end_state : state)
    (actions : list action)
    (Hstarting_length : length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))) = 1)
    (s'' : state)
    (H5 : ` (projT2 s''.1) = ` (projT2 end_state.1))
    (v'0 : qubit_reference)
    (H2 : (` (projT1 starting_qstate)) v'0 = Some (Env, 0))
    (la0 : list action)
    (s0 : session)
    (v' : qubit_reference)
    (Hfresh : ~ In v' (map fst (elems qubit_reference (participant * fin) (` (projT1 starting_qstate)))))
    (s : session)
    (s2 : session)
    (v'2 : qubit_reference)
    (Hfresh0 : ~ In v'2 (map fst (elems qubit_reference (participant * fin) (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))))))))
    (s1 : session)
    (s''0 : state)
    (H4 : finished s''0.2)
    (H19 : ` (projT2 s''0.1) = ` (projT2 s''.1))
    (la : list action)
    (q0 : quantum_state)
    (s4 : session)
    (s3 : session)
    (lq : list qubit_reference)
    (Hlen : length lq = 1)
    (Hdim : 1 > 0)
    (H32 : apply_unitary (insert (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))))) v'2 (Source, length (elems qubit_reference (participant * fin) (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate)))))))) (Primitives.add_new_qubit_obligation_1 (add_new_qubit starting_qstate Source v' Hfresh) Source v'2 Hfresh0) (@kron (2 ^ (length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))) + 1)) 1 2 1 (@kron (2 ^ length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate)))) 1 2 1 (` (projT2 starting_qstate)) ∣0⟩) ∣0⟩) (Primitives.add_new_qubit_obligation_2 (add_new_qubit starting_qstate Source v' Hfresh) Source v'2 Hfresh0) U_H lq Hlen Hdim = Some q0)
    (H31 : [Val (QVal v')] = map (fun z : qubit_reference => Val (QVal z)) lq)
    (H34 : NoDup lq)
    (H35 : Forall (fun q : qubit_reference => exists n : fin, insert (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))))) v'2 (Source, length (elems qubit_reference (participant * fin) (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))))))) q = Some (Source, n)) lq)
    (q3 : quantum_state)
    (s6 : session)
    (s5 : session)
    (lq0 : list qubit_reference)
    (Hlen0 : length lq0 = 2)
    (Hdim0 : 2 > 0)
    (H : List.cons (Val (QVal v')) (List.cons (Val (QVal v'2)) List.nil) = map (fun z : qubit_reference => Val (QVal z)) lq0)
    (H38 : apply_unitary (` (projT1 q0)) (proj2_sig (projT1 q0)) (` (projT2 q0)) (proj2_sig (projT2 q0)) U_CNOT lq0 Hlen0 Hdim0 = Some q3)
    (H39 : NoDup lq0)
    (H40 : Forall (fun q : qubit_reference => exists n : fin, (` (projT1 q0)) q = Some (Source, n)) lq0)
    (s8 : session)
    (old : participant)
    (n : fin)
    (Hlookup : (` (projT1 q3)) v' = Some (old, n))
    (s7 : session)
    (s10 : session)
    (old0 : participant)
    (n0 : fin)
    (Hlookup0 : insert (` (projT1 q3)) v' (Alice, n) v'0 = Some (old0, n0))
    (s9 : session)
    (q : quantum_state)
    (s11 : session)
    (lq1 : list qubit_reference)
    (Hlen1 : length lq1 = 2)
    (Hdim1 : 2 > 0)
    (H37 : List.cons (Val (QVal v'0)) (List.cons (Val (QVal v')) List.nil) = map (fun z : qubit_reference => Val (QVal z)) lq1)
    (H42 : apply_unitary (insert (insert (` (projT1 q3)) v' (Alice, n)) v'0 (Alice, n0)) (Primitives.transfer_qubit_obligation_2 (insert (` (projT1 q3)) v' (Alice, n)) (Primitives.transfer_qubit_obligation_2 (` (projT1 q3)) (proj2_sig (projT1 q3)) Alice v' old n (eq_sym Hlookup)) Alice v'0 old0 n0 (eq_sym Hlookup0)) (` (projT2 q3)) (Primitives.transfer_qubit_obligation_3 (insert (` (projT1 q3)) v' (Alice, n)) (Primitives.transfer_qubit_obligation_2 (` (projT1 q3)) (proj2_sig (projT1 q3)) Alice v' old n (eq_sym Hlookup)) (` (projT2 q3)) (Primitives.transfer_qubit_obligation_3 (` (projT1 q3)) (proj2_sig (projT1 q3)) (` (projT2 q3)) (proj2_sig (projT2 q3)) Alice v' old n (eq_sym Hlookup)) Alice v'0 old0 n0 (eq_sym Hlookup0)) U_CNOT lq1 Hlen1 Hdim1 = Some q)
    (H55 : NoDup lq1)
    (H56 : Forall (fun q : qubit_reference => exists n1 : fin, insert (insert (` (projT1 q3)) v' (Alice, n)) v'0 (Alice, n0) q = Some (Alice, n1)) lq1)
    (q1 : quantum_state)
    (s12 : session)
    (lq2 : list qubit_reference)
    (Hlen2 : length lq2 = 1)
    (Hdim2 : 1 > 0)
    (H47 : [Val (QVal v'0)] = map (fun z : qubit_reference => Val (QVal z)) lq2)
    (H58 : apply_unitary (` (projT1 q)) (proj2_sig (projT1 q)) (` (projT2 q)) (proj2_sig (projT2 q)) U_H lq2 Hlen2 Hdim2 = Some q1)
    (H60 : NoDup lq2)
    (H61 : Forall (fun q0 : qubit_reference => exists n : fin, (` (projT1 q)) q0 = Some (Alice, n)) lq2)
    (q4 : quantum_state)
    (s13 : session)
    (pi1 : R)
    (q5 : qubit_reference)
    (n1 : fin)
    (Hprob : {prob : R | (prob > 0)%R})
    (Hlookup1 : (` (projT1 q1)) q5 = Some (Alice, n1))
    (Hlen3 : 0 < length (elems qubit_reference (participant * fin) (` (projT1 q1))))
    (Hnonzero : norm (proj n1 (length (elems qubit_reference (participant * fin) (` (projT1 q1)))) false × ` (projT2 q1)) <> 0%R)
    (H59 : Val (QVal v'0) = Val (QVal q5))
    (H63 : (Hprob, q4) = measure_qubit_from_nonzero (` (projT1 q1)) (proj2_sig (projT1 q1)) (` (projT2 q1)) (proj2_sig (projT2 q1)) q5 Alice n1 false Hlookup1 Hlen3 Hnonzero)
    (q6 : quantum_state)
    (s14 : session)
    (pi0 : R)
    (q7 : qubit_reference)
    (n2 : fin)
    (Hprob0 : {prob : R | (prob > 0)%R})
    (Hlookup2 : (` (projT1 q4)) q7 = Some (Alice, n2))
    (Hlen4 : 0 < length (elems qubit_reference (participant * fin) (` (projT1 q4))))
    (Hnonzero0 : norm (proj n2 (length (elems qubit_reference (participant * fin) (` (projT1 q4)))) true × ` (projT2 q4)) <> 0%R)
    (H64 : Val (QVal v') = Val (QVal q7))
    (H66 : (Hprob0, q6) = measure_qubit_from_nonzero (` (projT1 q4)) (proj2_sig (projT1 q4)) (` (projT2 q4)) (proj2_sig (projT2 q4)) q7 Alice n2 true Hlookup2 Hlen4 Hnonzero0)
    (s16 : session)
    (old1 : participant)
    (n3 : fin)
    (Hlookup3 : (` (projT1 q6)) v'2 = Some (old1, n3))
    (s15 : session)
    (s18 : session)
    (s17 : session)
    (s20 : session)
    (s19 : session)
    (s22 : session)
    (s21 : session)
    (s24 : session)
    (s23 : session)
    (q2 : quantum_state)
    (s26 : session)
    (s25 : session)
    (lq3 : list qubit_reference)
    (Hlen5 : length lq3 = 1)
    (Hdim3 : 1 > 0)
    (H98 : apply_unitary (insert (` (projT1 q6)) v'2 (Bob, n3)) (Primitives.transfer_qubit_obligation_2 (` (projT1 q6)) (proj2_sig (projT1 q6)) Bob v'2 old1 n3 (eq_sym Hlookup3)) (` (projT2 q6)) (Primitives.transfer_qubit_obligation_3 (` (projT1 q6)) (proj2_sig (projT1 q6)) (` (projT2 q6)) (proj2_sig (projT2 q6)) Bob v'2 old1 n3 (eq_sym Hlookup3)) U_X lq3 Hlen5 Hdim3 = Some q2)
    (H88 : [Val (QVal v'2)] = map (fun z : qubit_reference => Val (QVal z)) lq3)
    (H99 : NoDup lq3)
    (H100 : Forall (fun q : qubit_reference => exists n : fin, insert (` (projT1 q6)) v'2 (Bob, n3) q = Some (Bob, n)) lq3)
    (s28 : session)
    (r2 : R)
    (old2 : participant)
    (n4 : fin)
    (Hlookup4 : (` (projT1 q2)) v'2 = Some (old2, n4))
    (s27 : session)
    (H101 : multistep (transfer_qubit_from_lookup (` (projT1 q2)) (proj2_sig (projT1 q2)) (` (projT2 q2)) (proj2_sig (projT2 q2)) Env v'2 old2 n4 Hlookup4, insert (insert (insert (insert (insert (insert empty_fmap Env (p_recv Bob (slist_x (p_end [Process.Var 0])))) Source (p_end [])) Alice (p_end [])) Bob ((Env) .+ l_Env_B <. Val (QVal v'2) .>; (p_end []))) Env (p_end [Val (QVal v'2)])) Bob (p_end [])) la s''0 r2),
    proj1_sig (projT2 (fst end_state)) = proj1_sig (projT2 starting_qstate).
Proof.
  intros.
  assert (Houtmap : proj1_sig (projT1 q2) =
      insert (` (projT1 q6)) v'2 (Bob,n3)).
  { eapply Happly_map; exact H98. }
  eapply qt_teleportation_branch_core; try eassumption.
  intros Hq6len Houtlen.
  pose proof (@insert_existing_length (` (projT1 q6)) v'2 old1 n3 Bob Hlookup3)
    as Hinsertlen0.
  assert (Hinsertlen : length (elems qubit_reference (participant * fin)
      (insert (` (projT1 q6)) v'2 (Bob,n3))) = 1).
  { transitivity (length (elems qubit_reference (participant * fin) (` (projT1 q6))));
    [exact Hinsertlen0|exact Hq6len]. }
  pose proof (Hresult_vector _ _ _ _ 1 U_X lq3 Hlen5 Hdim3 q2 H98) as Hresultq2.
  destruct Hresultq2 as [lpn [Hgetq2 [Hidxq2 Hvecq2]]].
  pose proof (proj1 Hidxq2) as Hidxlen.
  pose proof (proj2 (proj2 Hidxq2)) as Hidxbounds.
  assert (Hmapidxq2 : map snd lpn = [0]).
  {
    destruct lpn as [|[owner idx] rest]; simpl in Hidxlen; [discriminate|].
    destruct rest as [|pair rest]; simpl in Hidxlen; [|discriminate].
    simpl.
    assert (Hidxlt : idx < length (elems qubit_reference (participant * fin)
      (insert (` (projT1 q6)) v'2 (Bob,n3)))).
    { simpl in Hidxbounds; inversion Hidxbounds; assumption. }
    rewrite Hinsertlen in Hidxlt.
    simpl in Hidxlt; assert (idx = 0) by lia; subst idx; reflexivity.
  }
  assert (HidxI : length [0] = 1 /\ NoDup [0] /\
      Forall (fun i => i < length (elems qubit_reference (participant * fin)
        (insert (` (projT1 q6)) v'2 (Bob,n3)))) [0]).
  {
    split; [reflexivity|].
    split; [constructor; [simpl; tauto|constructor]|].
    constructor; [rewrite Hinsertlen; simpl; lia|constructor].
  }
  pose proof (@QTPathHelperDefinitions.qt_base_to_ucom_ext
    (length (elems qubit_reference (participant * fin)
      (insert (` (projT1 q6)) v'2 (Bob,n3)))) 1 U_X (map snd lpn) [0]
    Hidxq2 HidxI Hmapidxq2) as HbaseXext.
  assert (HbaseX : uc_eval (` (base_to_ucom U_X [0] HidxI)) = σx).
  { exact (@qt_U_X_eval_from_length
      (length (elems qubit_reference (participant * fin)
        (insert (` (projT1 q6)) v'2 (Bob,n3)))) Hinsertlen HidxI). }
  assert (HbaseX_lpn : uc_eval (` (base_to_ucom U_X (map snd lpn) Hidxq2)) = σx).
  { transitivity (uc_eval (` (base_to_ucom U_X [0] HidxI))).
    - exact HbaseXext.
    - exact HbaseX. }
  unfold QTPathHelperDefinitions.qt_correction; simpl.
  rewrite (FunctionalCorrectnessHelpers.transport_state_vector_value
    _ _ Houtlen (` (projT2 q2))).
  rewrite (FunctionalCorrectnessHelpers.transport_state_vector_value
    _ _ Hq6len (` (projT2 q6))).
  rewrite Hvecq2, HbaseX_lpn.
  replace (length (elems qubit_reference (participant * fin)
    (insert (` (projT1 q6)) v'2 (Bob,n3)))) with 1%nat by (symmetry; exact Hinsertlen).
  simpl.
  reflexivity.
Qed.

Lemma QuantumTeleportation_correct_goal_3 :
  forall
    (starting_qstate : quantum_state)
    (end_state : state)
    (actions : list action)
    (Hstarting_length : length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))) = 1)
    (s'' : state)
    (H5 : ` (projT2 s''.1) = ` (projT2 end_state.1))
    (v'0 : qubit_reference)
    (H2 : (` (projT1 starting_qstate)) v'0 = Some (Env, 0))
    (la0 : list action)
    (s0 : session)
    (v' : qubit_reference)
    (Hfresh : ~ In v' (map fst (elems qubit_reference (participant * fin) (` (projT1 starting_qstate)))))
    (s : session)
    (s2 : session)
    (v'2 : qubit_reference)
    (Hfresh0 : ~ In v'2 (map fst (elems qubit_reference (participant * fin) (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))))))))
    (s1 : session)
    (s''0 : state)
    (H4 : finished s''0.2)
    (H19 : ` (projT2 s''0.1) = ` (projT2 s''.1))
    (la : list action)
    (q0 : quantum_state)
    (s4 : session)
    (s3 : session)
    (lq : list qubit_reference)
    (Hlen : length lq = 1)
    (Hdim : 1 > 0)
    (H32 : apply_unitary (insert (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))))) v'2 (Source, length (elems qubit_reference (participant * fin) (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate)))))))) (Primitives.add_new_qubit_obligation_1 (add_new_qubit starting_qstate Source v' Hfresh) Source v'2 Hfresh0) (@kron (2 ^ (length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))) + 1)) 1 2 1 (@kron (2 ^ length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate)))) 1 2 1 (` (projT2 starting_qstate)) ∣0⟩) ∣0⟩) (Primitives.add_new_qubit_obligation_2 (add_new_qubit starting_qstate Source v' Hfresh) Source v'2 Hfresh0) U_H lq Hlen Hdim = Some q0)
    (H31 : [Val (QVal v')] = map (fun z : qubit_reference => Val (QVal z)) lq)
    (H34 : NoDup lq)
    (H35 : Forall (fun q : qubit_reference => exists n : fin, insert (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))))) v'2 (Source, length (elems qubit_reference (participant * fin) (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))))))) q = Some (Source, n)) lq)
    (q3 : quantum_state)
    (s6 : session)
    (s5 : session)
    (lq0 : list qubit_reference)
    (Hlen0 : length lq0 = 2)
    (Hdim0 : 2 > 0)
    (H : List.cons (Val (QVal v')) (List.cons (Val (QVal v'2)) List.nil) = map (fun z : qubit_reference => Val (QVal z)) lq0)
    (H38 : apply_unitary (` (projT1 q0)) (proj2_sig (projT1 q0)) (` (projT2 q0)) (proj2_sig (projT2 q0)) U_CNOT lq0 Hlen0 Hdim0 = Some q3)
    (H39 : NoDup lq0)
    (H40 : Forall (fun q : qubit_reference => exists n : fin, (` (projT1 q0)) q = Some (Source, n)) lq0)
    (s8 : session)
    (old : participant)
    (n : fin)
    (Hlookup : (` (projT1 q3)) v' = Some (old, n))
    (s7 : session)
    (s10 : session)
    (old0 : participant)
    (n0 : fin)
    (Hlookup0 : insert (` (projT1 q3)) v' (Alice, n) v'0 = Some (old0, n0))
    (s9 : session)
    (q : quantum_state)
    (s11 : session)
    (lq1 : list qubit_reference)
    (Hlen1 : length lq1 = 2)
    (Hdim1 : 2 > 0)
    (H37 : List.cons (Val (QVal v'0)) (List.cons (Val (QVal v')) List.nil) = map (fun z : qubit_reference => Val (QVal z)) lq1)
    (H42 : apply_unitary (insert (insert (` (projT1 q3)) v' (Alice, n)) v'0 (Alice, n0)) (Primitives.transfer_qubit_obligation_2 (insert (` (projT1 q3)) v' (Alice, n)) (Primitives.transfer_qubit_obligation_2 (` (projT1 q3)) (proj2_sig (projT1 q3)) Alice v' old n (eq_sym Hlookup)) Alice v'0 old0 n0 (eq_sym Hlookup0)) (` (projT2 q3)) (Primitives.transfer_qubit_obligation_3 (insert (` (projT1 q3)) v' (Alice, n)) (Primitives.transfer_qubit_obligation_2 (` (projT1 q3)) (proj2_sig (projT1 q3)) Alice v' old n (eq_sym Hlookup)) (` (projT2 q3)) (Primitives.transfer_qubit_obligation_3 (` (projT1 q3)) (proj2_sig (projT1 q3)) (` (projT2 q3)) (proj2_sig (projT2 q3)) Alice v' old n (eq_sym Hlookup)) Alice v'0 old0 n0 (eq_sym Hlookup0)) U_CNOT lq1 Hlen1 Hdim1 = Some q)
    (H55 : NoDup lq1)
    (H56 : Forall (fun q : qubit_reference => exists n1 : fin, insert (insert (` (projT1 q3)) v' (Alice, n)) v'0 (Alice, n0) q = Some (Alice, n1)) lq1)
    (q1 : quantum_state)
    (s12 : session)
    (lq2 : list qubit_reference)
    (Hlen2 : length lq2 = 1)
    (Hdim2 : 1 > 0)
    (H47 : [Val (QVal v'0)] = map (fun z : qubit_reference => Val (QVal z)) lq2)
    (H58 : apply_unitary (` (projT1 q)) (proj2_sig (projT1 q)) (` (projT2 q)) (proj2_sig (projT2 q)) U_H lq2 Hlen2 Hdim2 = Some q1)
    (H60 : NoDup lq2)
    (H61 : Forall (fun q0 : qubit_reference => exists n : fin, (` (projT1 q)) q0 = Some (Alice, n)) lq2)
    (q4 : quantum_state)
    (s13 : session)
    (pi1 : R)
    (q5 : qubit_reference)
    (n1 : fin)
    (Hprob : {prob : R | (prob > 0)%R})
    (Hlookup1 : (` (projT1 q1)) q5 = Some (Alice, n1))
    (Hlen3 : 0 < length (elems qubit_reference (participant * fin) (` (projT1 q1))))
    (Hnonzero : norm (proj n1 (length (elems qubit_reference (participant * fin) (` (projT1 q1)))) true × ` (projT2 q1)) <> 0%R)
    (H59 : Val (QVal v'0) = Val (QVal q5))
    (H63 : (Hprob, q4) = measure_qubit_from_nonzero (` (projT1 q1)) (proj2_sig (projT1 q1)) (` (projT2 q1)) (proj2_sig (projT2 q1)) q5 Alice n1 true Hlookup1 Hlen3 Hnonzero)
    (q6 : quantum_state)
    (s14 : session)
    (pi0 : R)
    (q7 : qubit_reference)
    (n2 : fin)
    (Hprob0 : {prob : R | (prob > 0)%R})
    (Hlookup2 : (` (projT1 q4)) q7 = Some (Alice, n2))
    (Hlen4 : 0 < length (elems qubit_reference (participant * fin) (` (projT1 q4))))
    (Hnonzero0 : norm (proj n2 (length (elems qubit_reference (participant * fin) (` (projT1 q4)))) false × ` (projT2 q4)) <> 0%R)
    (H64 : Val (QVal v') = Val (QVal q7))
    (H66 : (Hprob0, q6) = measure_qubit_from_nonzero (` (projT1 q4)) (proj2_sig (projT1 q4)) (` (projT2 q4)) (proj2_sig (projT2 q4)) q7 Alice n2 false Hlookup2 Hlen4 Hnonzero0)
    (s16 : session)
    (old1 : participant)
    (n3 : fin)
    (Hlookup3 : (` (projT1 q6)) v'2 = Some (old1, n3))
    (s15 : session)
    (s18 : session)
    (s17 : session)
    (s20 : session)
    (s19 : session)
    (s22 : session)
    (s21 : session)
    (s24 : session)
    (s23 : session)
    (q2 : quantum_state)
    (s26 : session)
    (s25 : session)
    (lq3 : list qubit_reference)
    (Hlen5 : length lq3 = 1)
    (Hdim3 : 1 > 0)
    (H98 : apply_unitary (insert (` (projT1 q6)) v'2 (Bob, n3)) (Primitives.transfer_qubit_obligation_2 (` (projT1 q6)) (proj2_sig (projT1 q6)) Bob v'2 old1 n3 (eq_sym Hlookup3)) (` (projT2 q6)) (Primitives.transfer_qubit_obligation_3 (` (projT1 q6)) (proj2_sig (projT1 q6)) (` (projT2 q6)) (proj2_sig (projT2 q6)) Bob v'2 old1 n3 (eq_sym Hlookup3)) U_Z lq3 Hlen5 Hdim3 = Some q2)
    (H88 : [Val (QVal v'2)] = map (fun z : qubit_reference => Val (QVal z)) lq3)
    (H99 : NoDup lq3)
    (H100 : Forall (fun q : qubit_reference => exists n : fin, insert (` (projT1 q6)) v'2 (Bob, n3) q = Some (Bob, n)) lq3)
    (s28 : session)
    (r2 : R)
    (old2 : participant)
    (n4 : fin)
    (Hlookup4 : (` (projT1 q2)) v'2 = Some (old2, n4))
    (s27 : session)
    (H101 : multistep (transfer_qubit_from_lookup (` (projT1 q2)) (proj2_sig (projT1 q2)) (` (projT2 q2)) (proj2_sig (projT2 q2)) Env v'2 old2 n4 Hlookup4, insert (insert (insert (insert (insert (insert empty_fmap Env (p_recv Bob (slist_x (p_end [Process.Var 0])))) Source (p_end [])) Alice (p_end [])) Bob ((Env) .+ l_Env_B <. Val (QVal v'2) .>; (p_end []))) Env (p_end [Val (QVal v'2)])) Bob (p_end [])) la s''0 r2),
    proj1_sig (projT2 (fst end_state)) = proj1_sig (projT2 starting_qstate).
Proof.
  intros.
  assert (Houtmap : proj1_sig (projT1 q2) =
      insert (` (projT1 q6)) v'2 (Bob,n3)).
  { eapply Happly_map; exact H98. }
  eapply qt_teleportation_branch_core; try eassumption.
  intros Hq6len Houtlen.
  pose proof (@insert_existing_length (` (projT1 q6)) v'2 old1 n3 Bob Hlookup3)
    as Hinsertlen0.
  assert (Hinsertlen : length (elems qubit_reference (participant * fin)
      (insert (` (projT1 q6)) v'2 (Bob,n3))) = 1).
  { transitivity (length (elems qubit_reference (participant * fin) (` (projT1 q6))));
    [exact Hinsertlen0|exact Hq6len]. }
  pose proof (Hresult_vector _ _ _ _ 1 U_Z lq3 Hlen5 Hdim3 q2 H98) as Hresultq2.
  destruct Hresultq2 as [lpn [Hgetq2 [Hidxq2 Hvecq2]]].
  pose proof (proj1 Hidxq2) as Hidxlen.
  pose proof (proj2 (proj2 Hidxq2)) as Hidxbounds.
  assert (Hmapidxq2 : map snd lpn = [0]).
  {
    destruct lpn as [|[owner idx] rest]; simpl in Hidxlen; [discriminate|].
    destruct rest as [|pair rest]; simpl in Hidxlen; [|discriminate].
    simpl.
    assert (Hidxlt : idx < length (elems qubit_reference (participant * fin)
      (insert (` (projT1 q6)) v'2 (Bob,n3)))).
    { simpl in Hidxbounds; inversion Hidxbounds; assumption. }
    rewrite Hinsertlen in Hidxlt.
    simpl in Hidxlt; assert (idx = 0) by lia; subst idx; reflexivity.
  }
  assert (HidxI : length [0] = 1 /\ NoDup [0] /\
      Forall (fun i => i < length (elems qubit_reference (participant * fin)
        (insert (` (projT1 q6)) v'2 (Bob,n3)))) [0]).
  {
    split; [reflexivity|].
    split; [constructor; [simpl; tauto|constructor]|].
    constructor; [rewrite Hinsertlen; simpl; lia|constructor].
  }
  pose proof (@QTPathHelperDefinitions.qt_base_to_ucom_ext
    (length (elems qubit_reference (participant * fin)
      (insert (` (projT1 q6)) v'2 (Bob,n3)))) 1 U_Z (map snd lpn) [0]
    Hidxq2 HidxI Hmapidxq2) as HbaseZext.
  assert (HbaseZ : uc_eval (` (base_to_ucom U_Z [0] HidxI)) = σz).
  { exact (@qt_U_Z_eval_from_length
      (length (elems qubit_reference (participant * fin)
        (insert (` (projT1 q6)) v'2 (Bob,n3)))) Hinsertlen HidxI). }
  assert (HbaseZ_lpn : uc_eval (` (base_to_ucom U_Z (map snd lpn) Hidxq2)) = σz).
  { transitivity (uc_eval (` (base_to_ucom U_Z [0] HidxI))).
    - exact HbaseZext.
    - exact HbaseZ. }
  unfold QTPathHelperDefinitions.qt_correction; simpl.
  rewrite (FunctionalCorrectnessHelpers.transport_state_vector_value
    _ _ Houtlen (` (projT2 q2))).
  rewrite (FunctionalCorrectnessHelpers.transport_state_vector_value
    _ _ Hq6len (` (projT2 q6))).
  rewrite Hvecq2, HbaseZ_lpn.
  replace (length (elems qubit_reference (participant * fin)
    (insert (` (projT1 q6)) v'2 (Bob,n3)))) with 1%nat by (symmetry; exact Hinsertlen).
  simpl.
  reflexivity.
Qed.

Lemma QuantumTeleportation_correct_goal_4 :
  forall
    (starting_qstate : quantum_state)
    (end_state : state)
    (actions : list action)
    (Hstarting_length : length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))) = 1)
    (s'' : state)
    (H5 : ` (projT2 s''.1) = ` (projT2 end_state.1))
    (v'0 : qubit_reference)
    (H2 : (` (projT1 starting_qstate)) v'0 = Some (Env, 0))
    (la0 : list action)
    (s0 : session)
    (v' : qubit_reference)
    (Hfresh : ~ In v' (map fst (elems qubit_reference (participant * fin) (` (projT1 starting_qstate)))))
    (s : session)
    (s2 : session)
    (v'2 : qubit_reference)
    (Hfresh0 : ~ In v'2 (map fst (elems qubit_reference (participant * fin) (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))))))))
    (s1 : session)
    (s''0 : state)
    (H4 : finished s''0.2)
    (H19 : ` (projT2 s''0.1) = ` (projT2 s''.1))
    (la1 : list action)
    (q0 : quantum_state)
    (s4 : session)
    (s3 : session)
    (lq : list qubit_reference)
    (Hlen : length lq = 1)
    (Hdim : 1 > 0)
    (H32 : apply_unitary (insert (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))))) v'2 (Source, length (elems qubit_reference (participant * fin) (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate)))))))) (Primitives.add_new_qubit_obligation_1 (add_new_qubit starting_qstate Source v' Hfresh) Source v'2 Hfresh0) (@kron (2 ^ (length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))) + 1)) 1 2 1 (@kron (2 ^ length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate)))) 1 2 1 (` (projT2 starting_qstate)) ∣0⟩) ∣0⟩) (Primitives.add_new_qubit_obligation_2 (add_new_qubit starting_qstate Source v' Hfresh) Source v'2 Hfresh0) U_H lq Hlen Hdim = Some q0)
    (H31 : [Val (QVal v')] = map (fun z : qubit_reference => Val (QVal z)) lq)
    (H34 : NoDup lq)
    (H35 : Forall (fun q : qubit_reference => exists n : fin, insert (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))))) v'2 (Source, length (elems qubit_reference (participant * fin) (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))))))) q = Some (Source, n)) lq)
    (q3 : quantum_state)
    (s6 : session)
    (s5 : session)
    (lq0 : list qubit_reference)
    (Hlen0 : length lq0 = 2)
    (Hdim0 : 2 > 0)
    (H : List.cons (Val (QVal v')) (List.cons (Val (QVal v'2)) List.nil) = map (fun z : qubit_reference => Val (QVal z)) lq0)
    (H38 : apply_unitary (` (projT1 q0)) (proj2_sig (projT1 q0)) (` (projT2 q0)) (proj2_sig (projT2 q0)) U_CNOT lq0 Hlen0 Hdim0 = Some q3)
    (H39 : NoDup lq0)
    (H40 : Forall (fun q : qubit_reference => exists n : fin, (` (projT1 q0)) q = Some (Source, n)) lq0)
    (s8 : session)
    (old : participant)
    (n : fin)
    (Hlookup : (` (projT1 q3)) v' = Some (old, n))
    (s7 : session)
    (s10 : session)
    (old0 : participant)
    (n0 : fin)
    (Hlookup0 : insert (` (projT1 q3)) v' (Alice, n) v'0 = Some (old0, n0))
    (s9 : session)
    (q : quantum_state)
    (s11 : session)
    (lq1 : list qubit_reference)
    (Hlen1 : length lq1 = 2)
    (Hdim1 : 2 > 0)
    (H37 : List.cons (Val (QVal v'0)) (List.cons (Val (QVal v')) List.nil) = map (fun z : qubit_reference => Val (QVal z)) lq1)
    (H42 : apply_unitary (insert (insert (` (projT1 q3)) v' (Alice, n)) v'0 (Alice, n0)) (Primitives.transfer_qubit_obligation_2 (insert (` (projT1 q3)) v' (Alice, n)) (Primitives.transfer_qubit_obligation_2 (` (projT1 q3)) (proj2_sig (projT1 q3)) Alice v' old n (eq_sym Hlookup)) Alice v'0 old0 n0 (eq_sym Hlookup0)) (` (projT2 q3)) (Primitives.transfer_qubit_obligation_3 (insert (` (projT1 q3)) v' (Alice, n)) (Primitives.transfer_qubit_obligation_2 (` (projT1 q3)) (proj2_sig (projT1 q3)) Alice v' old n (eq_sym Hlookup)) (` (projT2 q3)) (Primitives.transfer_qubit_obligation_3 (` (projT1 q3)) (proj2_sig (projT1 q3)) (` (projT2 q3)) (proj2_sig (projT2 q3)) Alice v' old n (eq_sym Hlookup)) Alice v'0 old0 n0 (eq_sym Hlookup0)) U_CNOT lq1 Hlen1 Hdim1 = Some q)
    (H55 : NoDup lq1)
    (H56 : Forall (fun q : qubit_reference => exists n1 : fin, insert (insert (` (projT1 q3)) v' (Alice, n)) v'0 (Alice, n0) q = Some (Alice, n1)) lq1)
    (q1 : quantum_state)
    (s12 : session)
    (lq2 : list qubit_reference)
    (Hlen2 : length lq2 = 1)
    (Hdim2 : 1 > 0)
    (H47 : [Val (QVal v'0)] = map (fun z : qubit_reference => Val (QVal z)) lq2)
    (H58 : apply_unitary (` (projT1 q)) (proj2_sig (projT1 q)) (` (projT2 q)) (proj2_sig (projT2 q)) U_H lq2 Hlen2 Hdim2 = Some q1)
    (H60 : NoDup lq2)
    (H61 : Forall (fun q0 : qubit_reference => exists n : fin, (` (projT1 q)) q0 = Some (Alice, n)) lq2)
    (q4 : quantum_state)
    (s13 : session)
    (pi1 : R)
    (q5 : qubit_reference)
    (n1 : fin)
    (Hprob : {prob : R | (prob > 0)%R})
    (Hlookup1 : (` (projT1 q1)) q5 = Some (Alice, n1))
    (Hlen3 : 0 < length (elems qubit_reference (participant * fin) (` (projT1 q1))))
    (Hnonzero : norm (proj n1 (length (elems qubit_reference (participant * fin) (` (projT1 q1)))) true × ` (projT2 q1)) <> 0%R)
    (H59 : Val (QVal v'0) = Val (QVal q5))
    (H63 : (Hprob, q4) = measure_qubit_from_nonzero (` (projT1 q1)) (proj2_sig (projT1 q1)) (` (projT2 q1)) (proj2_sig (projT2 q1)) q5 Alice n1 true Hlookup1 Hlen3 Hnonzero)
    (q6 : quantum_state)
    (s14 : session)
    (pi0 : R)
    (q7 : qubit_reference)
    (n2 : fin)
    (Hprob0 : {prob : R | (prob > 0)%R})
    (Hlookup2 : (` (projT1 q4)) q7 = Some (Alice, n2))
    (Hlen4 : 0 < length (elems qubit_reference (participant * fin) (` (projT1 q4))))
    (Hnonzero0 : norm (proj n2 (length (elems qubit_reference (participant * fin) (` (projT1 q4)))) true × ` (projT2 q4)) <> 0%R)
    (H64 : Val (QVal v') = Val (QVal q7))
    (H66 : (Hprob0, q6) = measure_qubit_from_nonzero (` (projT1 q4)) (proj2_sig (projT1 q4)) (` (projT2 q4)) (proj2_sig (projT2 q4)) q7 Alice n2 true Hlookup2 Hlen4 Hnonzero0)
    (s16 : session)
    (old1 : participant)
    (n3 : fin)
    (Hlookup3 : (` (projT1 q6)) v'2 = Some (old1, n3))
    (s15 : session)
    (s18 : session)
    (s17 : session)
    (s20 : session)
    (s19 : session)
    (s22 : session)
    (s21 : session)
    (s24 : session)
    (s23 : session)
    (q2 : quantum_state)
    (s26 : session)
    (s25 : session)
    (lq3 : list qubit_reference)
    (Hlen5 : length lq3 = 1)
    (Hdim3 : 1 > 0)
    (H98 : apply_unitary (insert (` (projT1 q6)) v'2 (Bob, n3)) (Primitives.transfer_qubit_obligation_2 (` (projT1 q6)) (proj2_sig (projT1 q6)) Bob v'2 old1 n3 (eq_sym Hlookup3)) (` (projT2 q6)) (Primitives.transfer_qubit_obligation_3 (` (projT1 q6)) (proj2_sig (projT1 q6)) (` (projT2 q6)) (proj2_sig (projT2 q6)) Bob v'2 old1 n3 (eq_sym Hlookup3)) U_X lq3 Hlen5 Hdim3 = Some q2)
    (H88 : [Val (QVal v'2)] = map (fun z : qubit_reference => Val (QVal z)) lq3)
    (H99 : NoDup lq3)
    (H100 : Forall (fun q : qubit_reference => exists n : fin, insert (` (projT1 q6)) v'2 (Bob, n3) q = Some (Bob, n)) lq3)
    (q8 : quantum_state)
    (s28 : session)
    (s27 : session)
    (lq4 : list qubit_reference)
    (Hlen6 : length lq4 = 1)
    (Hdim4 : 1 > 0)
    (H97 : [Val (QVal v'2)] = map (fun z : qubit_reference => Val (QVal z)) lq4)
    (H103 : apply_unitary (` (projT1 q2)) (proj2_sig (projT1 q2)) (` (projT2 q2)) (proj2_sig (projT2 q2)) U_Z lq4 Hlen6 Hdim4 = Some q8)
    (H104 : NoDup lq4)
    (H105 : Forall (fun q : qubit_reference => exists n : fin, (` (projT1 q2)) q = Some (Bob, n)) lq4)
    (s30 : session)
    (r0 : R)
    (old2 : participant)
    (n4 : fin)
    (Hlookup4 : (` (projT1 q8)) v'2 = Some (old2, n4))
    (s29 : session)
    (H106 : multistep (transfer_qubit_from_lookup (` (projT1 q8)) (proj2_sig (projT1 q8)) (` (projT2 q8)) (proj2_sig (projT2 q8)) Env v'2 old2 n4 Hlookup4, insert (insert (insert (insert (insert (insert empty_fmap Env (p_recv Bob (slist_x (p_end [Process.Var 0])))) Source (p_end [])) Alice (p_end [])) Bob ((Env) .+ l_Env_B <. Val (QVal v'2) .>; (p_end []))) Env (p_end [Val (QVal v'2)])) Bob (p_end [])) la1 s''0 r0),
    proj1_sig (projT2 (fst end_state)) = proj1_sig (projT2 starting_qstate).
Proof.

  intros.
  assert (Hmapq2 : proj1_sig (projT1 q2) =
      insert (` (projT1 q6)) v'2 (Bob,n3)).
  { eapply Happly_map; exact H98. }
  assert (Houtmap : proj1_sig (projT1 q8) =
      insert (` (projT1 q6)) v'2 (Bob,n3)).
  {
    pose proof H103 as H103map.
    eapply Happly_map in H103map.
    cbn in H103map.
    transitivity (proj1_sig (projT1 q2)); [exact H103map|exact Hmapq2].
  }
  eapply qt_teleportation_branch_core; try eassumption.
  intros Hq6len Houtlen.
  pose proof (@insert_existing_length (` (projT1 q6)) v'2 old1 n3 Bob Hlookup3)
    as Hinsertlen0.
  assert (Hinsertlen : length (elems qubit_reference (participant * fin)
      (insert (` (projT1 q6)) v'2 (Bob,n3))) = 1).
  { transitivity (length (elems qubit_reference (participant * fin)
      (` (projT1 q6)))); [exact Hinsertlen0|exact Hq6len]. }
  pose proof (Hresult_vector _ _ _ _ 1 U_X lq3 Hlen5 Hdim3 q2 H98) as Hresultq2.
  destruct Hresultq2 as [lpnX [Hgetq2 [Hidxq2 Hvecq2]]].
  pose proof (proj1 Hidxq2) as HidxlenX.
  pose proof (proj2 (proj2 Hidxq2)) as HidxboundsX.
  assert (Hmapidxq2 : map snd lpnX = [0]).
  {
    destruct lpnX as [|[owner idx] rest]; simpl in HidxlenX; [discriminate|].
    destruct rest as [|pair rest]; simpl in HidxlenX; [|discriminate].
    simpl.
    assert (Hidxlt : idx < length (elems qubit_reference (participant * fin)
      (insert (` (projT1 q6)) v'2 (Bob,n3)))).
    { simpl in HidxboundsX; inversion HidxboundsX; assumption. }
    rewrite Hinsertlen in Hidxlt.
    simpl in Hidxlt; assert (idx = 0) by lia; subst idx; reflexivity.
  }
  assert (HidxX : length [0] = 1 /\ NoDup [0] /\
      Forall (fun i => i < length (elems qubit_reference (participant * fin)
        (insert (` (projT1 q6)) v'2 (Bob,n3)))) [0]).
  {
    split; [reflexivity|].
    split; [constructor; [simpl; tauto|constructor]|].
    constructor; [rewrite Hinsertlen; simpl; lia|constructor].
  }
  pose proof (@QTPathHelperDefinitions.qt_base_to_ucom_ext
    (length (elems qubit_reference (participant * fin)
      (insert (` (projT1 q6)) v'2 (Bob,n3)))) 1 U_X (map snd lpnX) [0]
    Hidxq2 HidxX Hmapidxq2) as HbaseXext.
  assert (HbaseX : uc_eval (` (base_to_ucom U_X [0] HidxX)) = σx).
  { exact (@qt_U_X_eval_from_length
      (length (elems qubit_reference (participant * fin)
        (insert (` (projT1 q6)) v'2 (Bob,n3)))) Hinsertlen HidxX). }
  assert (HbaseX_lpn : uc_eval
      (` (base_to_ucom U_X (map snd lpnX) Hidxq2)) = σx).
  { transitivity (uc_eval (` (base_to_ucom U_X [0] HidxX))).
    - exact HbaseXext.
    - exact HbaseX. }
  assert (Hlenq2 : length (elems qubit_reference (participant * fin)
      (` (projT1 q2))) = 1).
  { rewrite Hmapq2; exact Hinsertlen. }
  pose proof (Hresult_vector _ _ _ _ 1 U_Z lq4 Hlen6 Hdim4 q8 H103) as Hresultq8.
  destruct Hresultq8 as [lpnZ [Hgetq8 [Hidxq8 Hvecq8]]].
  pose proof (proj1 Hidxq8) as HidxlenZ.
  pose proof (proj2 (proj2 Hidxq8)) as HidxboundsZ.
  assert (Hmapidxq8 : map snd lpnZ = [0]).
  {
    destruct lpnZ as [|[owner idx] rest]; simpl in HidxlenZ; [discriminate|].
    destruct rest as [|pair rest]; simpl in HidxlenZ; [|discriminate].
    simpl.
    assert (Hidxlt : idx < length (elems qubit_reference (participant * fin)
      (` (projT1 q2)))).
    { simpl in HidxboundsZ; inversion HidxboundsZ; assumption. }
    rewrite Hlenq2 in Hidxlt.
    simpl in Hidxlt; assert (idx = 0) by lia; subst idx; reflexivity.
  }
  assert (HidxZ : length [0] = 1 /\ NoDup [0] /\
      Forall (fun i => i < length (elems qubit_reference (participant * fin)
        (` (projT1 q2)))) [0]).
  {
    split; [reflexivity|].
    split; [constructor; [simpl; tauto|constructor]|].
    constructor; [rewrite Hlenq2; simpl; lia|constructor].
  }
  pose proof (@QTPathHelperDefinitions.qt_base_to_ucom_ext
    (length (elems qubit_reference (participant * fin)
      (` (projT1 q2)))) 1 U_Z (map snd lpnZ) [0]
    Hidxq8 HidxZ Hmapidxq8) as HbaseZext.
  assert (HbaseZ : uc_eval (` (base_to_ucom U_Z [0] HidxZ)) = σz).
  { exact (@qt_U_Z_eval_from_length
      (length (elems qubit_reference (participant * fin)
        (` (projT1 q2)))) Hlenq2 HidxZ). }
  assert (HbaseZ_lpn : uc_eval
      (` (base_to_ucom U_Z (map snd lpnZ) Hidxq8)) = σz).
  { transitivity (uc_eval (` (base_to_ucom U_Z [0] HidxZ))).
    - exact HbaseZext.
    - exact HbaseZ. }
  unfold QTPathHelperDefinitions.qt_correction; simpl.
  rewrite (FunctionalCorrectnessHelpers.transport_state_vector_value
    _ _ Houtlen (` (projT2 q8))).
  rewrite (FunctionalCorrectnessHelpers.transport_state_vector_value
    _ _ Hq6len (` (projT2 q6))).
  rewrite Hvecq8, HbaseZ_lpn.
  rewrite Hvecq2, HbaseX_lpn.
  replace (length (elems qubit_reference (participant * fin)
    (insert (` (projT1 q6)) v'2 (Bob,n3)))) with 1%nat
    by (symmetry; exact Hinsertlen).
  replace (length (elems qubit_reference (participant * fin)
    (` (projT1 q2)))) with 1%nat by (symmetry; exact Hlenq2).
  simpl.
  rewrite Mmult_assoc.
  reflexivity.
Qed.

Lemma QuantumTeleportation_correct_goal_5 :
  forall
    (starting_qstate : quantum_state)
    (end_state : state)
    (actions : list action)
    (Hstarting_length : length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))) = 1)
    (s'' : state)
    (H5 : ` (projT2 s''.1) = ` (projT2 end_state.1))
    (v'1 : qubit_reference)
    (H2 : (` (projT1 starting_qstate)) v'1 = Some (Env, 0))
    (la0 : list action)
    (s0 : session)
    (v' : qubit_reference)
    (Hfresh : ~ In v' (map fst (elems qubit_reference (participant * fin) (` (projT1 starting_qstate)))))
    (s : session)
    (s2 : session)
    (v'2 : qubit_reference)
    (Hfresh0 : ~ In v'2 (map fst (elems qubit_reference (participant * fin) (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))))))))
    (s1 : session)
    (s''0 : state)
    (H4 : finished s''0.2)
    (H19 : ` (projT2 s''0.1) = ` (projT2 s''.1))
    (la1 : list action)
    (q0 : quantum_state)
    (s4 : session)
    (s3 : session)
    (lq : list qubit_reference)
    (Hlen : length lq = 1)
    (Hdim : 1 > 0)
    (H32 : apply_unitary (insert (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))))) v'2 (Source, length (elems qubit_reference (participant * fin) (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate)))))))) (Primitives.add_new_qubit_obligation_1 (add_new_qubit starting_qstate Source v' Hfresh) Source v'2 Hfresh0) (@kron (2 ^ (length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))) + 1)) 1 2 1 (@kron (2 ^ length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate)))) 1 2 1 (` (projT2 starting_qstate)) ∣0⟩) ∣0⟩) (Primitives.add_new_qubit_obligation_2 (add_new_qubit starting_qstate Source v' Hfresh) Source v'2 Hfresh0) U_H lq Hlen Hdim = Some q0)
    (H31 : [Val (QVal v')] = map (fun z : qubit_reference => Val (QVal z)) lq)
    (H34 : NoDup lq)
    (H35 : Forall (fun q : qubit_reference => exists n : fin, insert (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))))) v'2 (Source, length (elems qubit_reference (participant * fin) (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))))))) q = Some (Source, n)) lq)
    (q3 : quantum_state)
    (s6 : session)
    (s5 : session)
    (lq0 : list qubit_reference)
    (Hlen0 : length lq0 = 2)
    (Hdim0 : 2 > 0)
    (H : List.cons (Val (QVal v')) (List.cons (Val (QVal v'2)) List.nil) = map (fun z : qubit_reference => Val (QVal z)) lq0)
    (H38 : apply_unitary (` (projT1 q0)) (proj2_sig (projT1 q0)) (` (projT2 q0)) (proj2_sig (projT2 q0)) U_CNOT lq0 Hlen0 Hdim0 = Some q3)
    (H39 : NoDup lq0)
    (H40 : Forall (fun q : qubit_reference => exists n : fin, (` (projT1 q0)) q = Some (Source, n)) lq0)
    (s8 : session)
    (old : participant)
    (n : fin)
    (Hlookup : (` (projT1 q3)) v' = Some (old, n))
    (s7 : session)
    (s10 : session)
    (old0 : participant)
    (n0 : fin)
    (Hlookup0 : insert (` (projT1 q3)) v' (Alice, n) v'2 = Some (old0, n0))
    (s9 : session)
    (s12 : session)
    (old1 : participant)
    (n1 : fin)
    (Hlookup1 : insert (insert (` (projT1 q3)) v' (Alice, n)) v'2 (Bob, n0) v'1 = Some (old1, n1))
    (s11 : session)
    (q : quantum_state)
    (s13 : session)
    (lq1 : list qubit_reference)
    (Hlen1 : length lq1 = 2)
    (Hdim1 : 2 > 0)
    (H37 : List.cons (Val (QVal v'1)) (List.cons (Val (QVal v')) List.nil) = map (fun z : qubit_reference => Val (QVal z)) lq1)
    (H47 : apply_unitary (insert (insert (insert (` (projT1 q3)) v' (Alice, n)) v'2 (Bob, n0)) v'1 (Alice, n1)) (Primitives.transfer_qubit_obligation_2 (insert (insert (` (projT1 q3)) v' (Alice, n)) v'2 (Bob, n0)) (Primitives.transfer_qubit_obligation_2 (insert (` (projT1 q3)) v' (Alice, n)) (Primitives.transfer_qubit_obligation_2 (` (projT1 q3)) (proj2_sig (projT1 q3)) Alice v' old n (eq_sym Hlookup)) Bob v'2 old0 n0 (eq_sym Hlookup0)) Alice v'1 old1 n1 (eq_sym Hlookup1)) (` (projT2 q3)) (Primitives.transfer_qubit_obligation_3 (insert (insert (` (projT1 q3)) v' (Alice, n)) v'2 (Bob, n0)) (Primitives.transfer_qubit_obligation_2 (insert (` (projT1 q3)) v' (Alice, n)) (Primitives.transfer_qubit_obligation_2 (` (projT1 q3)) (proj2_sig (projT1 q3)) Alice v' old n (eq_sym Hlookup)) Bob v'2 old0 n0 (eq_sym Hlookup0)) (` (projT2 q3)) (Primitives.transfer_qubit_obligation_3 (insert (` (projT1 q3)) v' (Alice, n)) (Primitives.transfer_qubit_obligation_2 (` (projT1 q3)) (proj2_sig (projT1 q3)) Alice v' old n (eq_sym Hlookup)) (` (projT2 q3)) (Primitives.transfer_qubit_obligation_3 (` (projT1 q3)) (proj2_sig (projT1 q3)) (` (projT2 q3)) (proj2_sig (projT2 q3)) Alice v' old n (eq_sym Hlookup)) Bob v'2 old0 n0 (eq_sym Hlookup0)) Alice v'1 old1 n1 (eq_sym Hlookup1)) U_CNOT lq1 Hlen1 Hdim1 = Some q)
    (H62 : NoDup lq1)
    (H63 : Forall (fun q : qubit_reference => exists n2 : fin, insert (insert (insert (` (projT1 q3)) v' (Alice, n)) v'2 (Bob, n0)) v'1 (Alice, n1) q = Some (Alice, n2)) lq1)
    (q1 : quantum_state)
    (s14 : session)
    (lq2 : list qubit_reference)
    (Hlen2 : length lq2 = 1)
    (Hdim2 : 1 > 0)
    (H53 : [Val (QVal v'1)] = map (fun z : qubit_reference => Val (QVal z)) lq2)
    (H65 : apply_unitary (` (projT1 q)) (proj2_sig (projT1 q)) (` (projT2 q)) (proj2_sig (projT2 q)) U_H lq2 Hlen2 Hdim2 = Some q1)
    (H67 : NoDup lq2)
    (H68 : Forall (fun q0 : qubit_reference => exists n : fin, (` (projT1 q)) q0 = Some (Alice, n)) lq2)
    (q2 : quantum_state)
    (s15 : session)
    (pi1 : R)
    (q4 : qubit_reference)
    (n2 : fin)
    (Hprob : {prob : R | (prob > 0)%R})
    (Hlookup2 : (` (projT1 q1)) q4 = Some (Alice, n2))
    (Hlen3 : 0 < length (elems qubit_reference (participant * fin) (` (projT1 q1))))
    (Hnonzero : norm (proj n2 (length (elems qubit_reference (participant * fin) (` (projT1 q1)))) false × ` (projT2 q1)) <> 0%R)
    (H66 : Val (QVal v'1) = Val (QVal q4))
    (H70 : (Hprob, q2) = measure_qubit_from_nonzero (` (projT1 q1)) (proj2_sig (projT1 q1)) (` (projT2 q1)) (proj2_sig (projT2 q1)) q4 Alice n2 false Hlookup2 Hlen3 Hnonzero)
    (q5 : quantum_state)
    (s16 : session)
    (pi0 : R)
    (q6 : qubit_reference)
    (n3 : fin)
    (Hprob0 : {prob : R | (prob > 0)%R})
    (Hlookup3 : (` (projT1 q2)) q6 = Some (Alice, n3))
    (Hlen4 : 0 < length (elems qubit_reference (participant * fin) (` (projT1 q2))))
    (Hnonzero0 : norm (proj n3 (length (elems qubit_reference (participant * fin) (` (projT1 q2)))) false × ` (projT2 q2)) <> 0%R)
    (H71 : Val (QVal v') = Val (QVal q6))
    (H73 : (Hprob0, q5) = measure_qubit_from_nonzero (` (projT1 q2)) (proj2_sig (projT1 q2)) (` (projT2 q2)) (proj2_sig (projT2 q2)) q6 Alice n3 false Hlookup3 Hlen4 Hnonzero0)
    (s18 : session)
    (s17 : session)
    (s20 : session)
    (s19 : session)
    (s22 : session)
    (s21 : session)
    (s24 : session)
    (s23 : session)
    (q7 : quantum_state)
    (s26 : session)
    (s25 : session)
    (lq3 : list qubit_reference)
    (Hlen5 : length lq3 = 1)
    (Hdim3 : 1 > 0)
    (H86 : [Val (QVal v'2)] = map (fun z : qubit_reference => Val (QVal z)) lq3)
    (H96 : apply_unitary (` (projT1 q5)) (proj2_sig (projT1 q5)) (` (projT2 q5)) (proj2_sig (projT2 q5)) U_I lq3 Hlen5 Hdim3 = Some q7)
    (H97 : NoDup lq3)
    (H98 : Forall (fun q : qubit_reference => exists n : fin, (` (projT1 q5)) q = Some (Bob, n)) lq3)
    (s28 : session)
    (r0 : R)
    (old2 : participant)
    (n4 : fin)
    (Hlookup4 : (` (projT1 q7)) v'2 = Some (old2, n4))
    (s27 : session)
    (H99 : multistep (transfer_qubit_from_lookup (` (projT1 q7)) (proj2_sig (projT1 q7)) (` (projT2 q7)) (proj2_sig (projT2 q7)) Env v'2 old2 n4 Hlookup4, insert (insert (insert (insert (insert (insert empty_fmap Source (p_end [])) Env (p_recv Bob (slist_x (p_end [Process.Var 0])))) Alice (p_end [])) Bob ((Env) .+ l_Env_B <. Val (QVal v'2) .>; (p_end []))) Env (p_end [Val (QVal v'2)])) Bob (p_end [])) la1 s''0 r0),
    proj1_sig (projT2 (fst end_state)) = proj1_sig (projT2 starting_qstate).
Proof.
  intros.
  pose proof (@qt_delayed_premeasure_core
    starting_qstate end_state actions Hstarting_length
    s'' H5 v'1 H2 la0 s0 v' Hfresh s s2 v'2 Hfresh0
    s1 s''0 H4 H19 la1 q0 s4 s3 lq Hlen Hdim H32 H31 H34 H35
    q3 s6 s5 lq0 Hlen0 Hdim0 H H38 H39 H40
    s8 old n Hlookup s7 s10 old0 n0 Hlookup0
    s9 s12 old1 n1 Hlookup1 s11 q s13 lq1 Hlen1 Hdim1 H37 H47 H62 H63
    q1 s14 lq2 Hlen2 Hdim2 H53 H65 H67 H68) as Hprepared.
  destruct Hprepared as [HlenA [HqA_v'1 [HqA_v' Hpre]]].
  pose proof (@qt_delayed_measurements_one_wire
    (` (projT1 q1)) (proj2_sig (projT1 q1))
    (` (projT2 q1)) (proj2_sig (projT2 q1)) HlenA
    q4 n2 false Hprob Hlookup2 Hlen3 Hnonzero q2 H70
    q6 n3 false Hprob0 Hlookup3 Hlen4 Hnonzero0 q5 H73) as Hlenq5.
  pose proof H96 as H96map.
  eapply Happly_map in H96map.
  cbn in H96map.
  assert (Hq7len : length (elems qubit_reference (participant * fin) (` (projT1 q7))) = 1).
  { rewrite H96map; exact Hlenq5. }
  pose proof (@qt_apply_U_I_vector_same_map
    (` (projT1 q5)) (proj2_sig (projT1 q5))
    (` (projT2 q5)) (proj2_sig (projT2 q5))
    lq3 Hlen5 Hdim3 q7 H96 H96map Hlenq5 Hq7len) as Hvecq7.
  assert (Houtvec : forall
      (Hq6len : length (elems qubit_reference (participant * fin) (` (projT1 q5))) = 1)
      (Houtlen : length (elems qubit_reference (participant * fin) (` (projT1 q7))) = 1),
      transport_state_vector Houtlen (` (projT2 q7)) =
        @Mmult 2 2 1 (QTPathHelperDefinitions.qt_correction false false)
          (transport_state_vector Hq6len (` (projT2 q5)))).
  { intros Hq6len Houtlen.
    replace Hq6len with Hlenq5 by apply proof_irrelevance.
    replace Houtlen with Hq7len by apply proof_irrelevance.
    unfold QTPathHelperDefinitions.qt_correction; simpl.
    exact Hvecq7. }
  pose proof H99 as Htail.
  change (multistep
    (transfer_qubit_from_lookup (` (projT1 q7)) (proj2_sig (projT1 q7))
      (` (projT2 q7)) (proj2_sig (projT2 q7)) Env v'2 old2 n4 Hlookup4,
     qt_delayed_tail_session v'2) la1 s''0 r0) in Htail.
  pose proof (qt_delayed_tail_session_end_entries v'2) as Htail_ends.
  exact (@qt_teleportation_measurement_core
    starting_qstate Hstarting_length false false v'1 v' v'2
    (` (projT1 q1)) (proj2_sig (projT1 q1))
    (` (projT2 q1)) (proj2_sig (projT2 q1))
    HlenA HqA_v'1 HqA_v' Hpre
    q4 n2 Hprob Hlookup2 Hlen3 Hnonzero H66
    q2 H70
    q6 n3 Hprob0 Hlookup3 Hlen4 Hnonzero0 H71
    q5 H73
    q7 Hq7len Houtvec
    (qt_delayed_tail_session v'2) Htail_ends
    old2 n4 Hlookup4 la1 s''0 r0 Htail s'' end_state H5 H19).
Qed.

Lemma QuantumTeleportation_correct_goal_6 :
  forall
    (starting_qstate : quantum_state)
    (end_state : state)
    (actions : list action)
    (Hstarting_length : length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))) = 1)
    (s'' : state)
    (H5 : ` (projT2 s''.1) = ` (projT2 end_state.1))
    (v'1 : qubit_reference)
    (H2 : (` (projT1 starting_qstate)) v'1 = Some (Env, 0))
    (la0 : list action)
    (s0 : session)
    (v' : qubit_reference)
    (Hfresh : ~ In v' (map fst (elems qubit_reference (participant * fin) (` (projT1 starting_qstate)))))
    (s : session)
    (s2 : session)
    (v'2 : qubit_reference)
    (Hfresh0 : ~ In v'2 (map fst (elems qubit_reference (participant * fin) (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))))))))
    (s1 : session)
    (s''0 : state)
    (H4 : finished s''0.2)
    (H19 : ` (projT2 s''0.1) = ` (projT2 s''.1))
    (la1 : list action)
    (q0 : quantum_state)
    (s4 : session)
    (s3 : session)
    (lq : list qubit_reference)
    (Hlen : length lq = 1)
    (Hdim : 1 > 0)
    (H32 : apply_unitary (insert (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))))) v'2 (Source, length (elems qubit_reference (participant * fin) (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate)))))))) (Primitives.add_new_qubit_obligation_1 (add_new_qubit starting_qstate Source v' Hfresh) Source v'2 Hfresh0) (@kron (2 ^ (length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))) + 1)) 1 2 1 (@kron (2 ^ length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate)))) 1 2 1 (` (projT2 starting_qstate)) ∣0⟩) ∣0⟩) (Primitives.add_new_qubit_obligation_2 (add_new_qubit starting_qstate Source v' Hfresh) Source v'2 Hfresh0) U_H lq Hlen Hdim = Some q0)
    (H31 : [Val (QVal v')] = map (fun z : qubit_reference => Val (QVal z)) lq)
    (H34 : NoDup lq)
    (H35 : Forall (fun q : qubit_reference => exists n : fin, insert (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))))) v'2 (Source, length (elems qubit_reference (participant * fin) (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))))))) q = Some (Source, n)) lq)
    (q3 : quantum_state)
    (s6 : session)
    (s5 : session)
    (lq0 : list qubit_reference)
    (Hlen0 : length lq0 = 2)
    (Hdim0 : 2 > 0)
    (H : List.cons (Val (QVal v')) (List.cons (Val (QVal v'2)) List.nil) = map (fun z : qubit_reference => Val (QVal z)) lq0)
    (H38 : apply_unitary (` (projT1 q0)) (proj2_sig (projT1 q0)) (` (projT2 q0)) (proj2_sig (projT2 q0)) U_CNOT lq0 Hlen0 Hdim0 = Some q3)
    (H39 : NoDup lq0)
    (H40 : Forall (fun q : qubit_reference => exists n : fin, (` (projT1 q0)) q = Some (Source, n)) lq0)
    (s8 : session)
    (old : participant)
    (n : fin)
    (Hlookup : (` (projT1 q3)) v' = Some (old, n))
    (s7 : session)
    (s10 : session)
    (old0 : participant)
    (n0 : fin)
    (Hlookup0 : insert (` (projT1 q3)) v' (Alice, n) v'2 = Some (old0, n0))
    (s9 : session)
    (s12 : session)
    (old1 : participant)
    (n1 : fin)
    (Hlookup1 : insert (insert (` (projT1 q3)) v' (Alice, n)) v'2 (Bob, n0) v'1 = Some (old1, n1))
    (s11 : session)
    (q : quantum_state)
    (s13 : session)
    (lq1 : list qubit_reference)
    (Hlen1 : length lq1 = 2)
    (Hdim1 : 2 > 0)
    (H37 : List.cons (Val (QVal v'1)) (List.cons (Val (QVal v')) List.nil) = map (fun z : qubit_reference => Val (QVal z)) lq1)
    (H47 : apply_unitary (insert (insert (insert (` (projT1 q3)) v' (Alice, n)) v'2 (Bob, n0)) v'1 (Alice, n1)) (Primitives.transfer_qubit_obligation_2 (insert (insert (` (projT1 q3)) v' (Alice, n)) v'2 (Bob, n0)) (Primitives.transfer_qubit_obligation_2 (insert (` (projT1 q3)) v' (Alice, n)) (Primitives.transfer_qubit_obligation_2 (` (projT1 q3)) (proj2_sig (projT1 q3)) Alice v' old n (eq_sym Hlookup)) Bob v'2 old0 n0 (eq_sym Hlookup0)) Alice v'1 old1 n1 (eq_sym Hlookup1)) (` (projT2 q3)) (Primitives.transfer_qubit_obligation_3 (insert (insert (` (projT1 q3)) v' (Alice, n)) v'2 (Bob, n0)) (Primitives.transfer_qubit_obligation_2 (insert (` (projT1 q3)) v' (Alice, n)) (Primitives.transfer_qubit_obligation_2 (` (projT1 q3)) (proj2_sig (projT1 q3)) Alice v' old n (eq_sym Hlookup)) Bob v'2 old0 n0 (eq_sym Hlookup0)) (` (projT2 q3)) (Primitives.transfer_qubit_obligation_3 (insert (` (projT1 q3)) v' (Alice, n)) (Primitives.transfer_qubit_obligation_2 (` (projT1 q3)) (proj2_sig (projT1 q3)) Alice v' old n (eq_sym Hlookup)) (` (projT2 q3)) (Primitives.transfer_qubit_obligation_3 (` (projT1 q3)) (proj2_sig (projT1 q3)) (` (projT2 q3)) (proj2_sig (projT2 q3)) Alice v' old n (eq_sym Hlookup)) Bob v'2 old0 n0 (eq_sym Hlookup0)) Alice v'1 old1 n1 (eq_sym Hlookup1)) U_CNOT lq1 Hlen1 Hdim1 = Some q)
    (H62 : NoDup lq1)
    (H63 : Forall (fun q : qubit_reference => exists n2 : fin, insert (insert (insert (` (projT1 q3)) v' (Alice, n)) v'2 (Bob, n0)) v'1 (Alice, n1) q = Some (Alice, n2)) lq1)
    (q1 : quantum_state)
    (s14 : session)
    (lq2 : list qubit_reference)
    (Hlen2 : length lq2 = 1)
    (Hdim2 : 1 > 0)
    (H53 : [Val (QVal v'1)] = map (fun z : qubit_reference => Val (QVal z)) lq2)
    (H65 : apply_unitary (` (projT1 q)) (proj2_sig (projT1 q)) (` (projT2 q)) (proj2_sig (projT2 q)) U_H lq2 Hlen2 Hdim2 = Some q1)
    (H67 : NoDup lq2)
    (H68 : Forall (fun q0 : qubit_reference => exists n : fin, (` (projT1 q)) q0 = Some (Alice, n)) lq2)
    (q2 : quantum_state)
    (s15 : session)
    (pi1 : R)
    (q4 : qubit_reference)
    (n2 : fin)
    (Hprob : {prob : R | (prob > 0)%R})
    (Hlookup2 : (` (projT1 q1)) q4 = Some (Alice, n2))
    (Hlen3 : 0 < length (elems qubit_reference (participant * fin) (` (projT1 q1))))
    (Hnonzero : norm (proj n2 (length (elems qubit_reference (participant * fin) (` (projT1 q1)))) false × ` (projT2 q1)) <> 0%R)
    (H66 : Val (QVal v'1) = Val (QVal q4))
    (H70 : (Hprob, q2) = measure_qubit_from_nonzero (` (projT1 q1)) (proj2_sig (projT1 q1)) (` (projT2 q1)) (proj2_sig (projT2 q1)) q4 Alice n2 false Hlookup2 Hlen3 Hnonzero)
    (q5 : quantum_state)
    (s16 : session)
    (pi0 : R)
    (q6 : qubit_reference)
    (n3 : fin)
    (Hprob0 : {prob : R | (prob > 0)%R})
    (Hlookup3 : (` (projT1 q2)) q6 = Some (Alice, n3))
    (Hlen4 : 0 < length (elems qubit_reference (participant * fin) (` (projT1 q2))))
    (Hnonzero0 : norm (proj n3 (length (elems qubit_reference (participant * fin) (` (projT1 q2)))) true × ` (projT2 q2)) <> 0%R)
    (H71 : Val (QVal v') = Val (QVal q6))
    (H73 : (Hprob0, q5) = measure_qubit_from_nonzero (` (projT1 q2)) (proj2_sig (projT1 q2)) (` (projT2 q2)) (proj2_sig (projT2 q2)) q6 Alice n3 true Hlookup3 Hlen4 Hnonzero0)
    (s18 : session)
    (s17 : session)
    (s20 : session)
    (s19 : session)
    (s22 : session)
    (s21 : session)
    (s24 : session)
    (s23 : session)
    (q7 : quantum_state)
    (s26 : session)
    (s25 : session)
    (lq3 : list qubit_reference)
    (Hlen5 : length lq3 = 1)
    (Hdim3 : 1 > 0)
    (H86 : [Val (QVal v'2)] = map (fun z : qubit_reference => Val (QVal z)) lq3)
    (H96 : apply_unitary (` (projT1 q5)) (proj2_sig (projT1 q5)) (` (projT2 q5)) (proj2_sig (projT2 q5)) U_X lq3 Hlen5 Hdim3 = Some q7)
    (H97 : NoDup lq3)
    (H98 : Forall (fun q : qubit_reference => exists n : fin, (` (projT1 q5)) q = Some (Bob, n)) lq3)
    (s28 : session)
    (r0 : R)
    (old2 : participant)
    (n4 : fin)
    (Hlookup4 : (` (projT1 q7)) v'2 = Some (old2, n4))
    (s27 : session)
    (H99 : multistep (transfer_qubit_from_lookup (` (projT1 q7)) (proj2_sig (projT1 q7)) (` (projT2 q7)) (proj2_sig (projT2 q7)) Env v'2 old2 n4 Hlookup4, insert (insert (insert (insert (insert (insert empty_fmap Source (p_end [])) Env (p_recv Bob (slist_x (p_end [Process.Var 0])))) Alice (p_end [])) Bob ((Env) .+ l_Env_B <. Val (QVal v'2) .>; (p_end []))) Env (p_end [Val (QVal v'2)])) Bob (p_end [])) la1 s''0 r0),
    proj1_sig (projT2 (fst end_state)) = proj1_sig (projT2 starting_qstate).
Proof.
  intros.
  pose proof (@qt_delayed_premeasure_core
    starting_qstate end_state actions Hstarting_length
    s'' H5 v'1 H2 la0 s0 v' Hfresh s s2 v'2 Hfresh0
    s1 s''0 H4 H19 la1 q0 s4 s3 lq Hlen Hdim H32 H31 H34 H35
    q3 s6 s5 lq0 Hlen0 Hdim0 H H38 H39 H40
    s8 old n Hlookup s7 s10 old0 n0 Hlookup0
    s9 s12 old1 n1 Hlookup1 s11 q s13 lq1 Hlen1 Hdim1 H37 H47 H62 H63
    q1 s14 lq2 Hlen2 Hdim2 H53 H65 H67 H68) as Hprepared.
  destruct Hprepared as [HlenA [HqA_v'1 [HqA_v' Hpre]]].
  pose proof (@qt_delayed_measurements_one_wire
    (` (projT1 q1)) (proj2_sig (projT1 q1))
    (` (projT2 q1)) (proj2_sig (projT2 q1)) HlenA
    q4 n2 false Hprob Hlookup2 Hlen3 Hnonzero q2 H70
    q6 n3 true Hprob0 Hlookup3 Hlen4 Hnonzero0 q5 H73) as Hlenq5.
  pose proof H96 as H96map.
  eapply Happly_map in H96map.
  cbn in H96map.
  assert (Hq7len : length (elems qubit_reference (participant * fin) (` (projT1 q7))) = 1).
  { rewrite H96map; exact Hlenq5. }
  pose proof (@qt_apply_one_gate_vector_same_map
    (` (projT1 q5)) (proj2_sig (projT1 q5))
    (` (projT2 q5)) (proj2_sig (projT2 q5))
    lq3 Hlen5 Hdim3 q7 U_X σx H96 H96map Hlenq5 Hq7len
    ltac:(intro Hidx;
      exact (@qt_U_X_eval_from_length
        (length (elems qubit_reference (participant * fin) (` (projT1 q5))))
        Hlenq5 Hidx))) as Hvecq7.
  assert (Houtvec : forall
      (Hq6len : length (elems qubit_reference (participant * fin) (` (projT1 q5))) = 1)
      (Houtlen : length (elems qubit_reference (participant * fin) (` (projT1 q7))) = 1),
      transport_state_vector Houtlen (` (projT2 q7)) =
        @Mmult 2 2 1 (QTPathHelperDefinitions.qt_correction false true)
          (transport_state_vector Hq6len (` (projT2 q5)))).
  { intros Hq6len Houtlen.
    replace Hq6len with Hlenq5 by apply proof_irrelevance.
    replace Houtlen with Hq7len by apply proof_irrelevance.
    unfold QTPathHelperDefinitions.qt_correction; simpl.
    exact Hvecq7. }
  pose proof H99 as Htail.
  change (multistep
    (transfer_qubit_from_lookup (` (projT1 q7)) (proj2_sig (projT1 q7))
      (` (projT2 q7)) (proj2_sig (projT2 q7)) Env v'2 old2 n4 Hlookup4,
     qt_delayed_tail_session v'2) la1 s''0 r0) in Htail.
  pose proof (qt_delayed_tail_session_end_entries v'2) as Htail_ends.
  exact (@qt_teleportation_measurement_core
    starting_qstate Hstarting_length false true v'1 v' v'2
    (` (projT1 q1)) (proj2_sig (projT1 q1))
    (` (projT2 q1)) (proj2_sig (projT2 q1))
    HlenA HqA_v'1 HqA_v' Hpre
    q4 n2 Hprob Hlookup2 Hlen3 Hnonzero H66
    q2 H70
    q6 n3 Hprob0 Hlookup3 Hlen4 Hnonzero0 H71
    q5 H73
    q7 Hq7len Houtvec
    (qt_delayed_tail_session v'2) Htail_ends
    old2 n4 Hlookup4 la1 s''0 r0 Htail s'' end_state H5 H19).
Qed.

Lemma QuantumTeleportation_correct_goal_7 :
  forall
    (starting_qstate : quantum_state)
    (end_state : state)
    (actions : list action)
    (Hstarting_length : length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))) = 1)
    (s'' : state)
    (H5 : ` (projT2 s''.1) = ` (projT2 end_state.1))
    (v'1 : qubit_reference)
    (H2 : (` (projT1 starting_qstate)) v'1 = Some (Env, 0))
    (la0 : list action)
    (s0 : session)
    (v' : qubit_reference)
    (Hfresh : ~ In v' (map fst (elems qubit_reference (participant * fin) (` (projT1 starting_qstate)))))
    (s : session)
    (s2 : session)
    (v'2 : qubit_reference)
    (Hfresh0 : ~ In v'2 (map fst (elems qubit_reference (participant * fin) (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))))))))
    (s1 : session)
    (s''0 : state)
    (H4 : finished s''0.2)
    (H19 : ` (projT2 s''0.1) = ` (projT2 s''.1))
    (la1 : list action)
    (q0 : quantum_state)
    (s4 : session)
    (s3 : session)
    (lq : list qubit_reference)
    (Hlen : length lq = 1)
    (Hdim : 1 > 0)
    (H32 : apply_unitary (insert (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))))) v'2 (Source, length (elems qubit_reference (participant * fin) (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate)))))))) (Primitives.add_new_qubit_obligation_1 (add_new_qubit starting_qstate Source v' Hfresh) Source v'2 Hfresh0) (@kron (2 ^ (length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))) + 1)) 1 2 1 (@kron (2 ^ length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate)))) 1 2 1 (` (projT2 starting_qstate)) ∣0⟩) ∣0⟩) (Primitives.add_new_qubit_obligation_2 (add_new_qubit starting_qstate Source v' Hfresh) Source v'2 Hfresh0) U_H lq Hlen Hdim = Some q0)
    (H31 : [Val (QVal v')] = map (fun z : qubit_reference => Val (QVal z)) lq)
    (H34 : NoDup lq)
    (H35 : Forall (fun q : qubit_reference => exists n : fin, insert (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))))) v'2 (Source, length (elems qubit_reference (participant * fin) (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))))))) q = Some (Source, n)) lq)
    (q3 : quantum_state)
    (s6 : session)
    (s5 : session)
    (lq0 : list qubit_reference)
    (Hlen0 : length lq0 = 2)
    (Hdim0 : 2 > 0)
    (H : List.cons (Val (QVal v')) (List.cons (Val (QVal v'2)) List.nil) = map (fun z : qubit_reference => Val (QVal z)) lq0)
    (H38 : apply_unitary (` (projT1 q0)) (proj2_sig (projT1 q0)) (` (projT2 q0)) (proj2_sig (projT2 q0)) U_CNOT lq0 Hlen0 Hdim0 = Some q3)
    (H39 : NoDup lq0)
    (H40 : Forall (fun q : qubit_reference => exists n : fin, (` (projT1 q0)) q = Some (Source, n)) lq0)
    (s8 : session)
    (old : participant)
    (n : fin)
    (Hlookup : (` (projT1 q3)) v' = Some (old, n))
    (s7 : session)
    (s10 : session)
    (old0 : participant)
    (n0 : fin)
    (Hlookup0 : insert (` (projT1 q3)) v' (Alice, n) v'2 = Some (old0, n0))
    (s9 : session)
    (s12 : session)
    (old1 : participant)
    (n1 : fin)
    (Hlookup1 : insert (insert (` (projT1 q3)) v' (Alice, n)) v'2 (Bob, n0) v'1 = Some (old1, n1))
    (s11 : session)
    (q : quantum_state)
    (s13 : session)
    (lq1 : list qubit_reference)
    (Hlen1 : length lq1 = 2)
    (Hdim1 : 2 > 0)
    (H37 : List.cons (Val (QVal v'1)) (List.cons (Val (QVal v')) List.nil) = map (fun z : qubit_reference => Val (QVal z)) lq1)
    (H47 : apply_unitary (insert (insert (insert (` (projT1 q3)) v' (Alice, n)) v'2 (Bob, n0)) v'1 (Alice, n1)) (Primitives.transfer_qubit_obligation_2 (insert (insert (` (projT1 q3)) v' (Alice, n)) v'2 (Bob, n0)) (Primitives.transfer_qubit_obligation_2 (insert (` (projT1 q3)) v' (Alice, n)) (Primitives.transfer_qubit_obligation_2 (` (projT1 q3)) (proj2_sig (projT1 q3)) Alice v' old n (eq_sym Hlookup)) Bob v'2 old0 n0 (eq_sym Hlookup0)) Alice v'1 old1 n1 (eq_sym Hlookup1)) (` (projT2 q3)) (Primitives.transfer_qubit_obligation_3 (insert (insert (` (projT1 q3)) v' (Alice, n)) v'2 (Bob, n0)) (Primitives.transfer_qubit_obligation_2 (insert (` (projT1 q3)) v' (Alice, n)) (Primitives.transfer_qubit_obligation_2 (` (projT1 q3)) (proj2_sig (projT1 q3)) Alice v' old n (eq_sym Hlookup)) Bob v'2 old0 n0 (eq_sym Hlookup0)) (` (projT2 q3)) (Primitives.transfer_qubit_obligation_3 (insert (` (projT1 q3)) v' (Alice, n)) (Primitives.transfer_qubit_obligation_2 (` (projT1 q3)) (proj2_sig (projT1 q3)) Alice v' old n (eq_sym Hlookup)) (` (projT2 q3)) (Primitives.transfer_qubit_obligation_3 (` (projT1 q3)) (proj2_sig (projT1 q3)) (` (projT2 q3)) (proj2_sig (projT2 q3)) Alice v' old n (eq_sym Hlookup)) Bob v'2 old0 n0 (eq_sym Hlookup0)) Alice v'1 old1 n1 (eq_sym Hlookup1)) U_CNOT lq1 Hlen1 Hdim1 = Some q)
    (H62 : NoDup lq1)
    (H63 : Forall (fun q : qubit_reference => exists n2 : fin, insert (insert (insert (` (projT1 q3)) v' (Alice, n)) v'2 (Bob, n0)) v'1 (Alice, n1) q = Some (Alice, n2)) lq1)
    (q1 : quantum_state)
    (s14 : session)
    (lq2 : list qubit_reference)
    (Hlen2 : length lq2 = 1)
    (Hdim2 : 1 > 0)
    (H53 : [Val (QVal v'1)] = map (fun z : qubit_reference => Val (QVal z)) lq2)
    (H65 : apply_unitary (` (projT1 q)) (proj2_sig (projT1 q)) (` (projT2 q)) (proj2_sig (projT2 q)) U_H lq2 Hlen2 Hdim2 = Some q1)
    (H67 : NoDup lq2)
    (H68 : Forall (fun q0 : qubit_reference => exists n : fin, (` (projT1 q)) q0 = Some (Alice, n)) lq2)
    (q2 : quantum_state)
    (s15 : session)
    (pi1 : R)
    (q4 : qubit_reference)
    (n2 : fin)
    (Hprob : {prob : R | (prob > 0)%R})
    (Hlookup2 : (` (projT1 q1)) q4 = Some (Alice, n2))
    (Hlen3 : 0 < length (elems qubit_reference (participant * fin) (` (projT1 q1))))
    (Hnonzero : norm (proj n2 (length (elems qubit_reference (participant * fin) (` (projT1 q1)))) true × ` (projT2 q1)) <> 0%R)
    (H66 : Val (QVal v'1) = Val (QVal q4))
    (H70 : (Hprob, q2) = measure_qubit_from_nonzero (` (projT1 q1)) (proj2_sig (projT1 q1)) (` (projT2 q1)) (proj2_sig (projT2 q1)) q4 Alice n2 true Hlookup2 Hlen3 Hnonzero)
    (q5 : quantum_state)
    (s16 : session)
    (pi0 : R)
    (q6 : qubit_reference)
    (n3 : fin)
    (Hprob0 : {prob : R | (prob > 0)%R})
    (Hlookup3 : (` (projT1 q2)) q6 = Some (Alice, n3))
    (Hlen4 : 0 < length (elems qubit_reference (participant * fin) (` (projT1 q2))))
    (Hnonzero0 : norm (proj n3 (length (elems qubit_reference (participant * fin) (` (projT1 q2)))) false × ` (projT2 q2)) <> 0%R)
    (H71 : Val (QVal v') = Val (QVal q6))
    (H73 : (Hprob0, q5) = measure_qubit_from_nonzero (` (projT1 q2)) (proj2_sig (projT1 q2)) (` (projT2 q2)) (proj2_sig (projT2 q2)) q6 Alice n3 false Hlookup3 Hlen4 Hnonzero0)
    (s18 : session)
    (s17 : session)
    (s20 : session)
    (s19 : session)
    (s22 : session)
    (s21 : session)
    (s24 : session)
    (s23 : session)
    (q7 : quantum_state)
    (s26 : session)
    (s25 : session)
    (lq3 : list qubit_reference)
    (Hlen5 : length lq3 = 1)
    (Hdim3 : 1 > 0)
    (H86 : [Val (QVal v'2)] = map (fun z : qubit_reference => Val (QVal z)) lq3)
    (H96 : apply_unitary (` (projT1 q5)) (proj2_sig (projT1 q5)) (` (projT2 q5)) (proj2_sig (projT2 q5)) U_Z lq3 Hlen5 Hdim3 = Some q7)
    (H97 : NoDup lq3)
    (H98 : Forall (fun q : qubit_reference => exists n : fin, (` (projT1 q5)) q = Some (Bob, n)) lq3)
    (s28 : session)
    (r0 : R)
    (old2 : participant)
    (n4 : fin)
    (Hlookup4 : (` (projT1 q7)) v'2 = Some (old2, n4))
    (s27 : session)
    (H99 : multistep (transfer_qubit_from_lookup (` (projT1 q7)) (proj2_sig (projT1 q7)) (` (projT2 q7)) (proj2_sig (projT2 q7)) Env v'2 old2 n4 Hlookup4, insert (insert (insert (insert (insert (insert empty_fmap Source (p_end [])) Env (p_recv Bob (slist_x (p_end [Process.Var 0])))) Alice (p_end [])) Bob ((Env) .+ l_Env_B <. Val (QVal v'2) .>; (p_end []))) Env (p_end [Val (QVal v'2)])) Bob (p_end [])) la1 s''0 r0),
    proj1_sig (projT2 (fst end_state)) = proj1_sig (projT2 starting_qstate).
Proof.
  intros.
  pose proof (@qt_delayed_premeasure_core
    starting_qstate end_state actions Hstarting_length
    s'' H5 v'1 H2 la0 s0 v' Hfresh s s2 v'2 Hfresh0
    s1 s''0 H4 H19 la1 q0 s4 s3 lq Hlen Hdim H32 H31 H34 H35
    q3 s6 s5 lq0 Hlen0 Hdim0 H H38 H39 H40
    s8 old n Hlookup s7 s10 old0 n0 Hlookup0
    s9 s12 old1 n1 Hlookup1 s11 q s13 lq1 Hlen1 Hdim1 H37 H47 H62 H63
    q1 s14 lq2 Hlen2 Hdim2 H53 H65 H67 H68) as Hprepared.
  destruct Hprepared as [HlenA [HqA_v'1 [HqA_v' Hpre]]].
  pose proof (@qt_delayed_measurements_one_wire
    (` (projT1 q1)) (proj2_sig (projT1 q1))
    (` (projT2 q1)) (proj2_sig (projT2 q1)) HlenA
    q4 n2 true Hprob Hlookup2 Hlen3 Hnonzero q2 H70
    q6 n3 false Hprob0 Hlookup3 Hlen4 Hnonzero0 q5 H73) as Hlenq5.
  pose proof H96 as H96map.
  eapply Happly_map in H96map.
  cbn in H96map.
  assert (Hq7len : length (elems qubit_reference (participant * fin) (` (projT1 q7))) = 1).
  { rewrite H96map; exact Hlenq5. }
  pose proof (@qt_apply_one_gate_vector_same_map
    (` (projT1 q5)) (proj2_sig (projT1 q5))
    (` (projT2 q5)) (proj2_sig (projT2 q5))
    lq3 Hlen5 Hdim3 q7 U_Z σz H96 H96map Hlenq5 Hq7len
    ltac:(intro Hidx;
      exact (@qt_U_Z_eval_from_length
        (length (elems qubit_reference (participant * fin) (` (projT1 q5))))
        Hlenq5 Hidx))) as Hvecq7.
  assert (Houtvec : forall
      (Hq6len : length (elems qubit_reference (participant * fin) (` (projT1 q5))) = 1)
      (Houtlen : length (elems qubit_reference (participant * fin) (` (projT1 q7))) = 1),
      transport_state_vector Houtlen (` (projT2 q7)) =
        @Mmult 2 2 1 (QTPathHelperDefinitions.qt_correction true false)
          (transport_state_vector Hq6len (` (projT2 q5)))).
  { intros Hq6len Houtlen.
    replace Hq6len with Hlenq5 by apply proof_irrelevance.
    replace Houtlen with Hq7len by apply proof_irrelevance.
    unfold QTPathHelperDefinitions.qt_correction; simpl.
    exact Hvecq7. }
  pose proof H99 as Htail.
  change (multistep
    (transfer_qubit_from_lookup (` (projT1 q7)) (proj2_sig (projT1 q7))
      (` (projT2 q7)) (proj2_sig (projT2 q7)) Env v'2 old2 n4 Hlookup4,
     qt_delayed_tail_session v'2) la1 s''0 r0) in Htail.
  pose proof (qt_delayed_tail_session_end_entries v'2) as Htail_ends.
  exact (@qt_teleportation_measurement_core
    starting_qstate Hstarting_length true false v'1 v' v'2
    (` (projT1 q1)) (proj2_sig (projT1 q1))
    (` (projT2 q1)) (proj2_sig (projT2 q1))
    HlenA HqA_v'1 HqA_v' Hpre
    q4 n2 Hprob Hlookup2 Hlen3 Hnonzero H66
    q2 H70
    q6 n3 Hprob0 Hlookup3 Hlen4 Hnonzero0 H71
    q5 H73
    q7 Hq7len Houtvec
    (qt_delayed_tail_session v'2) Htail_ends
    old2 n4 Hlookup4 la1 s''0 r0 Htail s'' end_state H5 H19).
Qed.

Lemma QuantumTeleportation_correct_goal_8 :
  forall
    (starting_qstate : quantum_state)
    (end_state : state)
    (actions : list action)
    (Hstarting_length : length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))) = 1)
    (s'' : state)
    (H5 : ` (projT2 s''.1) = ` (projT2 end_state.1))
    (v'1 : qubit_reference)
    (H2 : (` (projT1 starting_qstate)) v'1 = Some (Env, 0))
    (la0 : list action)
    (s0 : session)
    (v' : qubit_reference)
    (Hfresh : ~ In v' (map fst (elems qubit_reference (participant * fin) (` (projT1 starting_qstate)))))
    (s : session)
    (s2 : session)
    (v'2 : qubit_reference)
    (Hfresh0 : ~ In v'2 (map fst (elems qubit_reference (participant * fin) (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))))))))
    (s1 : session)
    (s''0 : state)
    (H4 : finished s''0.2)
    (H19 : ` (projT2 s''0.1) = ` (projT2 s''.1))
    (la : list action)
    (q0 : quantum_state)
    (s4 : session)
    (s3 : session)
    (lq : list qubit_reference)
    (Hlen : length lq = 1)
    (Hdim : 1 > 0)
    (H32 : apply_unitary (insert (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))))) v'2 (Source, length (elems qubit_reference (participant * fin) (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate)))))))) (Primitives.add_new_qubit_obligation_1 (add_new_qubit starting_qstate Source v' Hfresh) Source v'2 Hfresh0) (@kron (2 ^ (length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))) + 1)) 1 2 1 (@kron (2 ^ length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate)))) 1 2 1 (` (projT2 starting_qstate)) ∣0⟩) ∣0⟩) (Primitives.add_new_qubit_obligation_2 (add_new_qubit starting_qstate Source v' Hfresh) Source v'2 Hfresh0) U_H lq Hlen Hdim = Some q0)
    (H31 : [Val (QVal v')] = map (fun z : qubit_reference => Val (QVal z)) lq)
    (H34 : NoDup lq)
    (H35 : Forall (fun q : qubit_reference => exists n : fin, insert (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))))) v'2 (Source, length (elems qubit_reference (participant * fin) (insert (` (projT1 starting_qstate)) v' (Source, length (elems qubit_reference (participant * fin) (` (projT1 starting_qstate))))))) q = Some (Source, n)) lq)
    (q3 : quantum_state)
    (s6 : session)
    (s5 : session)
    (lq0 : list qubit_reference)
    (Hlen0 : length lq0 = 2)
    (Hdim0 : 2 > 0)
    (H : List.cons (Val (QVal v')) (List.cons (Val (QVal v'2)) List.nil) = map (fun z : qubit_reference => Val (QVal z)) lq0)
    (H38 : apply_unitary (` (projT1 q0)) (proj2_sig (projT1 q0)) (` (projT2 q0)) (proj2_sig (projT2 q0)) U_CNOT lq0 Hlen0 Hdim0 = Some q3)
    (H39 : NoDup lq0)
    (H40 : Forall (fun q : qubit_reference => exists n : fin, (` (projT1 q0)) q = Some (Source, n)) lq0)
    (s8 : session)
    (old : participant)
    (n : fin)
    (Hlookup : (` (projT1 q3)) v' = Some (old, n))
    (s7 : session)
    (s10 : session)
    (old0 : participant)
    (n0 : fin)
    (Hlookup0 : insert (` (projT1 q3)) v' (Alice, n) v'2 = Some (old0, n0))
    (s9 : session)
    (s12 : session)
    (old1 : participant)
    (n1 : fin)
    (Hlookup1 : insert (insert (` (projT1 q3)) v' (Alice, n)) v'2 (Bob, n0) v'1 = Some (old1, n1))
    (s11 : session)
    (q : quantum_state)
    (s13 : session)
    (lq1 : list qubit_reference)
    (Hlen1 : length lq1 = 2)
    (Hdim1 : 2 > 0)
    (H37 : List.cons (Val (QVal v'1)) (List.cons (Val (QVal v')) List.nil) = map (fun z : qubit_reference => Val (QVal z)) lq1)
    (H47 : apply_unitary (insert (insert (insert (` (projT1 q3)) v' (Alice, n)) v'2 (Bob, n0)) v'1 (Alice, n1)) (Primitives.transfer_qubit_obligation_2 (insert (insert (` (projT1 q3)) v' (Alice, n)) v'2 (Bob, n0)) (Primitives.transfer_qubit_obligation_2 (insert (` (projT1 q3)) v' (Alice, n)) (Primitives.transfer_qubit_obligation_2 (` (projT1 q3)) (proj2_sig (projT1 q3)) Alice v' old n (eq_sym Hlookup)) Bob v'2 old0 n0 (eq_sym Hlookup0)) Alice v'1 old1 n1 (eq_sym Hlookup1)) (` (projT2 q3)) (Primitives.transfer_qubit_obligation_3 (insert (insert (` (projT1 q3)) v' (Alice, n)) v'2 (Bob, n0)) (Primitives.transfer_qubit_obligation_2 (insert (` (projT1 q3)) v' (Alice, n)) (Primitives.transfer_qubit_obligation_2 (` (projT1 q3)) (proj2_sig (projT1 q3)) Alice v' old n (eq_sym Hlookup)) Bob v'2 old0 n0 (eq_sym Hlookup0)) (` (projT2 q3)) (Primitives.transfer_qubit_obligation_3 (insert (` (projT1 q3)) v' (Alice, n)) (Primitives.transfer_qubit_obligation_2 (` (projT1 q3)) (proj2_sig (projT1 q3)) Alice v' old n (eq_sym Hlookup)) (` (projT2 q3)) (Primitives.transfer_qubit_obligation_3 (` (projT1 q3)) (proj2_sig (projT1 q3)) (` (projT2 q3)) (proj2_sig (projT2 q3)) Alice v' old n (eq_sym Hlookup)) Bob v'2 old0 n0 (eq_sym Hlookup0)) Alice v'1 old1 n1 (eq_sym Hlookup1)) U_CNOT lq1 Hlen1 Hdim1 = Some q)
    (H62 : NoDup lq1)
    (H63 : Forall (fun q : qubit_reference => exists n2 : fin, insert (insert (insert (` (projT1 q3)) v' (Alice, n)) v'2 (Bob, n0)) v'1 (Alice, n1) q = Some (Alice, n2)) lq1)
    (q1 : quantum_state)
    (s14 : session)
    (lq2 : list qubit_reference)
    (Hlen2 : length lq2 = 1)
    (Hdim2 : 1 > 0)
    (H53 : [Val (QVal v'1)] = map (fun z : qubit_reference => Val (QVal z)) lq2)
    (H65 : apply_unitary (` (projT1 q)) (proj2_sig (projT1 q)) (` (projT2 q)) (proj2_sig (projT2 q)) U_H lq2 Hlen2 Hdim2 = Some q1)
    (H67 : NoDup lq2)
    (H68 : Forall (fun q0 : qubit_reference => exists n : fin, (` (projT1 q)) q0 = Some (Alice, n)) lq2)
    (q2 : quantum_state)
    (s15 : session)
    (pi1 : R)
    (q4 : qubit_reference)
    (n2 : fin)
    (Hprob : {prob : R | (prob > 0)%R})
    (Hlookup2 : (` (projT1 q1)) q4 = Some (Alice, n2))
    (Hlen3 : 0 < length (elems qubit_reference (participant * fin) (` (projT1 q1))))
    (Hnonzero : norm (proj n2 (length (elems qubit_reference (participant * fin) (` (projT1 q1)))) true × ` (projT2 q1)) <> 0%R)
    (H66 : Val (QVal v'1) = Val (QVal q4))
    (H70 : (Hprob, q2) = measure_qubit_from_nonzero (` (projT1 q1)) (proj2_sig (projT1 q1)) (` (projT2 q1)) (proj2_sig (projT2 q1)) q4 Alice n2 true Hlookup2 Hlen3 Hnonzero)
    (q5 : quantum_state)
    (s16 : session)
    (pi0 : R)
    (q6 : qubit_reference)
    (n3 : fin)
    (Hprob0 : {prob : R | (prob > 0)%R})
    (Hlookup3 : (` (projT1 q2)) q6 = Some (Alice, n3))
    (Hlen4 : 0 < length (elems qubit_reference (participant * fin) (` (projT1 q2))))
    (Hnonzero0 : norm (proj n3 (length (elems qubit_reference (participant * fin) (` (projT1 q2)))) true × ` (projT2 q2)) <> 0%R)
    (H71 : Val (QVal v') = Val (QVal q6))
    (H73 : (Hprob0, q5) = measure_qubit_from_nonzero (` (projT1 q2)) (proj2_sig (projT1 q2)) (` (projT2 q2)) (proj2_sig (projT2 q2)) q6 Alice n3 true Hlookup3 Hlen4 Hnonzero0)
    (s18 : session)
    (s17 : session)
    (s20 : session)
    (s19 : session)
    (s22 : session)
    (s21 : session)
    (s24 : session)
    (s23 : session)
    (q7 : quantum_state)
    (s26 : session)
    (s25 : session)
    (lq3 : list qubit_reference)
    (Hlen5 : length lq3 = 1)
    (Hdim3 : 1 > 0)
    (H86 : [Val (QVal v'2)] = map (fun z : qubit_reference => Val (QVal z)) lq3)
    (H96 : apply_unitary (` (projT1 q5)) (proj2_sig (projT1 q5)) (` (projT2 q5)) (proj2_sig (projT2 q5)) U_X lq3 Hlen5 Hdim3 = Some q7)
    (H97 : NoDup lq3)
    (H98 : Forall (fun q : qubit_reference => exists n : fin, (` (projT1 q5)) q = Some (Bob, n)) lq3)
    (q8 : quantum_state)
    (s28 : session)
    (s27 : session)
    (lq4 : list qubit_reference)
    (Hlen6 : length lq4 = 1)
    (Hdim4 : 1 > 0)
    (H95 : [Val (QVal v'2)] = map (fun z : qubit_reference => Val (QVal z)) lq4)
    (H101 : apply_unitary (` (projT1 q7)) (proj2_sig (projT1 q7)) (` (projT2 q7)) (proj2_sig (projT2 q7)) U_Z lq4 Hlen6 Hdim4 = Some q8)
    (H102 : NoDup lq4)
    (H103 : Forall (fun q : qubit_reference => exists n : fin, (` (projT1 q7)) q = Some (Bob, n)) lq4)
    (s30 : session)
    (r2 : R)
    (old2 : participant)
    (n4 : fin)
    (Hlookup4 : (` (projT1 q8)) v'2 = Some (old2, n4))
    (s29 : session)
    (H104 : multistep (transfer_qubit_from_lookup (` (projT1 q8)) (proj2_sig (projT1 q8)) (` (projT2 q8)) (proj2_sig (projT2 q8)) Env v'2 old2 n4 Hlookup4, insert (insert (insert (insert (insert (insert empty_fmap Source (p_end [])) Env (p_recv Bob (slist_x (p_end [Process.Var 0])))) Alice (p_end [])) Bob ((Env) .+ l_Env_B <. Val (QVal v'2) .>; (p_end []))) Env (p_end [Val (QVal v'2)])) Bob (p_end [])) la s''0 r2),
    proj1_sig (projT2 (fst end_state)) = proj1_sig (projT2 starting_qstate).
Proof.
  intros.
  pose proof (@qt_delayed_premeasure_core
    starting_qstate end_state actions Hstarting_length
    s'' H5 v'1 H2 la0 s0 v' Hfresh s s2 v'2 Hfresh0
    s1 s''0 H4 H19 la q0 s4 s3 lq Hlen Hdim H32 H31 H34 H35
    q3 s6 s5 lq0 Hlen0 Hdim0 H H38 H39 H40
    s8 old n Hlookup s7 s10 old0 n0 Hlookup0
    s9 s12 old1 n1 Hlookup1 s11 q s13 lq1 Hlen1 Hdim1 H37 H47 H62 H63
    q1 s14 lq2 Hlen2 Hdim2 H53 H65 H67 H68) as Hprepared.
  destruct Hprepared as [HlenA [HqA_v'1 [HqA_v' Hpre]]].
  pose proof (@qt_delayed_measurements_one_wire
    (` (projT1 q1)) (proj2_sig (projT1 q1))
    (` (projT2 q1)) (proj2_sig (projT2 q1)) HlenA
    q4 n2 true Hprob Hlookup2 Hlen3 Hnonzero q2 H70
    q6 n3 true Hprob0 Hlookup3 Hlen4 Hnonzero0 q5 H73) as Hlenq5.
  pose proof H96 as H96map.
  eapply Happly_map in H96map.
  cbn in H96map.
  assert (Hq7len : length (elems qubit_reference (participant * fin) (` (projT1 q7))) = 1).
  { rewrite H96map; exact Hlenq5. }
  pose proof (@qt_apply_one_gate_vector_same_map
    (` (projT1 q5)) (proj2_sig (projT1 q5))
    (` (projT2 q5)) (proj2_sig (projT2 q5))
    lq3 Hlen5 Hdim3 q7 U_X σx H96 H96map Hlenq5 Hq7len
    ltac:(intro Hidx;
      exact (@qt_U_X_eval_from_length
        (length (elems qubit_reference (participant * fin) (` (projT1 q5))))
        Hlenq5 Hidx))) as Hvecq7.
  pose proof H101 as H101map.
  eapply Happly_map in H101map.
  cbn in H101map.
  assert (Hq8len : length (elems qubit_reference (participant * fin) (` (projT1 q8))) = 1).
  { rewrite H101map; exact Hq7len. }
  pose proof (@qt_apply_one_gate_vector_same_map
    (` (projT1 q7)) (proj2_sig (projT1 q7))
    (` (projT2 q7)) (proj2_sig (projT2 q7))
    lq4 Hlen6 Hdim4 q8 U_Z σz H101 H101map Hq7len Hq8len
    ltac:(intro Hidx;
      exact (@qt_U_Z_eval_from_length
        (length (elems qubit_reference (participant * fin) (` (projT1 q7))))
        Hq7len Hidx))) as Hvecq8.
  assert (Houtvec : forall
      (Hq6len : length (elems qubit_reference (participant * fin) (` (projT1 q5))) = 1)
      (Houtlen : length (elems qubit_reference (participant * fin) (` (projT1 q8))) = 1),
      transport_state_vector Houtlen (` (projT2 q8)) =
        @Mmult 2 2 1 (QTPathHelperDefinitions.qt_correction true true)
          (transport_state_vector Hq6len (` (projT2 q5)))).
  { intros Hq6len Houtlen.
    replace Hq6len with Hlenq5 by apply proof_irrelevance.
    replace Houtlen with Hq8len by apply proof_irrelevance.
    unfold QTPathHelperDefinitions.qt_correction; simpl.
    rewrite Hvecq8, Hvecq7.
    rewrite Mmult_assoc.
    reflexivity. }
  pose proof H104 as Htail.
  change (multistep
    (transfer_qubit_from_lookup (` (projT1 q8)) (proj2_sig (projT1 q8))
      (` (projT2 q8)) (proj2_sig (projT2 q8)) Env v'2 old2 n4 Hlookup4,
     qt_delayed_tail_session v'2) la s''0 r2) in Htail.
  pose proof (qt_delayed_tail_session_end_entries v'2) as Htail_ends.
  exact (@qt_teleportation_measurement_core
    starting_qstate Hstarting_length true true v'1 v' v'2
    (` (projT1 q1)) (proj2_sig (projT1 q1))
    (` (projT2 q1)) (proj2_sig (projT2 q1))
    HlenA HqA_v'1 HqA_v' Hpre
    q4 n2 Hprob Hlookup2 Hlen3 Hnonzero H66
    q2 H70
    q6 n3 Hprob0 Hlookup3 Hlen4 Hnonzero0 H71
    q5 H73
    q8 Hq8len Houtvec
    (qt_delayed_tail_session v'2) Htail_ends
    old2 n4 Hlookup4 la s''0 r2 Htail s'' end_state H5 H19).
Qed.

Theorem QuantumTeleportation_correct:
forall starting_qstate end_state q actions pi,
multistep (starting_qstate, quantum_teleportation q) actions end_state pi ->
finished (snd end_state) ->
length (elems _ _ (proj1_sig (projT1 starting_qstate))) = 1 ->
(proj1_sig  (projT1 starting_qstate)) q = Some (Env, 0) ->
(proj1_sig (projT2 (fst end_state))) = ((proj1_sig (projT2 starting_qstate))).
Proof.
  unfold quantum_teleportation; simpl; intros.
  simpl in *.
  eapply multistep_partial_sort in H; cleanup; simpl in *; cleanup.
  unfold equivalent_states in *; cleanup.
  eapply finished_unfoldM_r in H3; eauto.
  clear H0.
  pose proof (partial_sort_pairwise_sorted should_swap actions should_swap_true_swap) as Hsort.
  assert_fresh (Env <> Source).
  unfold Env, Source; congruence.

  unfold P_A, P_B, P_S, P_E in *.
  pose proof should_swap_facts as Hswap; logic_clean.
  process_step.
  process_step.

    eapply multistep_partial_sort_no_newq in H4; cleanup_light; simpl in *; cleanup_light; [|intuition eauto].
    2: {
      unfold no_newq_session.
      Transparent insert.
      simpl; intros; repeat case_analysis; cleanup_light.
      unfold P_A; simpl; eauto.
      unfold P_B; simpl; eauto.
      unfold P_E; simpl; eauto.
      simpl; eauto.
      all: try (unfold P_A, P_B, P_E in *; simpl in *; eauto).
      intuition.
      Opaque insert.
    }

    unfold equivalent_states in *; cleanup_light.
    eapply finished_unfoldM_r in H4; eauto.
    clear H3.
    pose proof (partial_sort_pairwise_sorted should_swap_no_newq la0 should_swap_no_newq_true_swap) as Hsort2.
    pose proof should_swap_no_newq_facts as Hswap; logic_clean.
  
    process_step; rewrite <- H30 in Hsort2.
    process_step.
    process_step.
    process_step.
    {
      invert_Alice.
      invert_Alice.
      invert_Alice.
      invert_Alice.

      process_step.
      process_step.
      process_step.
      process_step.
      process_step.
      process_step.
      process_step.
      {
        repeat match goal with
        |[H: context [should_swap] |- _] =>
          clear H
        |[H: context [should_swap_no_newq] |- _] =>
          clear H
        |[H: ?x = ?x |- _] =>
          clear H
        |[H: _ <> _ |- _] =>
          clear H
        |[H: forall _, (Bool _) <> _ |- _] =>
          clear H
        end.
        exact (@QuantumTeleportation_correct_goal_1
          starting_qstate end_state actions H1 s'' H5
          v'0 H2 la0 s0 v'
          Hfresh s s2 v'2 Hfresh0
          s1 s''0 H4 H19 la
          q0 s4 s3 lq Hlen
          Hdim H32 H31 H34 H35
          q3 s6 s5 lq0 Hlen0
          Hdim0 H H38 H39 H40
          s8 old n Hlookup s7
          s10 old0 n0 Hlookup0 s9
          q s11 lq1 Hlen1 Hdim1
          H37 H42 H55 H56 q1
          s12 lq2 Hlen2 Hdim2 H47
          H58 H60 H61 q4 s13
          pi1 q5 n1 Hprob Hlookup1
          Hlen3 Hnonzero H59 H63 q6
          s14 pi0 q7 n2 Hprob0
          Hlookup2 Hlen4 Hnonzero0 H64 H66
          s16 old1 n3 Hlookup3 s15
          s18 s17 s20 s19 s22
          s21 s24 s23 q2 s26
          s25 lq3 Hlen5 Hdim3 H98
          H88 H99 H100 s28 r2
          old2 n4 Hlookup4 s27 H101).
      }

      process_step.
      process_step.
      {
        repeat match goal with
        |[H: context [should_swap] |- _] =>
          clear H
        |[H: context [should_swap_no_newq] |- _] =>
          clear H
        |[H: ?x = ?x |- _] =>
          clear H
        |[H: _ <> _ |- _] =>
          clear H
        |[H: forall _, (Bool _) <> _ |- _] =>
          clear H
        end.
        exact (@QuantumTeleportation_correct_goal_2
          starting_qstate end_state actions H1 s'' H5
          v'0 H2 la0 s0 v'
          Hfresh s s2 v'2 Hfresh0
          s1 s''0 H4 H19 la
          q0 s4 s3 lq Hlen
          Hdim H32 H31 H34 H35
          q3 s6 s5 lq0 Hlen0
          Hdim0 H H38 H39 H40
          s8 old n Hlookup s7
          s10 old0 n0 Hlookup0 s9
          q s11 lq1 Hlen1 Hdim1
          H37 H42 H55 H56 q1
          s12 lq2 Hlen2 Hdim2 H47
          H58 H60 H61 q4 s13
          pi1 q5 n1 Hprob Hlookup1
          Hlen3 Hnonzero H59 H63 q6
          s14 pi0 q7 n2 Hprob0
          Hlookup2 Hlen4 Hnonzero0 H64 H66
          s16 old1 n3 Hlookup3 s15
          s18 s17 s20 s19 s22
          s21 s24 s23 q2 s26
          s25 lq3 Hlen5 Hdim3 H98
          H88 H99 H100 s28 r2
          old2 n4 Hlookup4 s27 H101).
      }

      process_step.
      process_step.
      process_step.
      {
        repeat match goal with
        |[H: context [should_swap] |- _] =>
          clear H
        |[H: context [should_swap_no_newq] |- _] =>
          clear H
        |[H: ?x = ?x |- _] =>
          clear H
        |[H: _ <> _ |- _] =>
          clear H
        |[H: forall _, (Bool _) <> _ |- _] =>
          clear H
        end.
        exact (@QuantumTeleportation_correct_goal_3
          starting_qstate end_state actions H1 s'' H5
          v'0 H2 la0 s0 v'
          Hfresh s s2 v'2 Hfresh0
          s1 s''0 H4 H19 la
          q0 s4 s3 lq Hlen
          Hdim H32 H31 H34 H35
          q3 s6 s5 lq0 Hlen0
          Hdim0 H H38 H39 H40
          s8 old n Hlookup s7
          s10 old0 n0 Hlookup0 s9
          q s11 lq1 Hlen1 Hdim1
          H37 H42 H55 H56 q1
          s12 lq2 Hlen2 Hdim2 H47
          H58 H60 H61 q4 s13
          pi1 q5 n1 Hprob Hlookup1
          Hlen3 Hnonzero H59 H63 q6
          s14 pi0 q7 n2 Hprob0
          Hlookup2 Hlen4 Hnonzero0 H64 H66
          s16 old1 n3 Hlookup3 s15
          s18 s17 s20 s19 s22
          s21 s24 s23 q2 s26
          s25 lq3 Hlen5 Hdim3 H98
          H88 H99 H100 s28 r2
          old2 n4 Hlookup4 s27 H101).
      }
      process_step.
      process_step.
      process_step.
      {
        repeat match goal with
        |[H: context [should_swap] |- _] =>
          clear H
        |[H: context [should_swap_no_newq] |- _] =>
          clear H
        |[H: ?x = ?x |- _] =>
          clear H
        |[H: _ <> _ |- _] =>
          clear H
        |[H: forall _, (Bool _) <> _ |- _] =>
          clear H
        end.
        exact (@QuantumTeleportation_correct_goal_4
          starting_qstate end_state actions H1 s'' H5
          v'0 H2 la0 s0 v'
          Hfresh s s2 v'2 Hfresh0
          s1 s''0 H4 H19 la1
          q0 s4 s3 lq Hlen
          Hdim H32 H31 H34 H35
          q3 s6 s5 lq0 Hlen0
          Hdim0 H H38 H39 H40
          s8 old n Hlookup s7
          s10 old0 n0 Hlookup0 s9
          q s11 lq1 Hlen1 Hdim1
          H37 H42 H55 H56 q1
          s12 lq2 Hlen2 Hdim2 H47
          H58 H60 H61 q4 s13
          pi1 q5 n1 Hprob Hlookup1
          Hlen3 Hnonzero H59 H63 q6
          s14 pi0 q7 n2 Hprob0
          Hlookup2 Hlen4 Hnonzero0 H64 H66
          s16 old1 n3 Hlookup3 s15
          s18 s17 s20 s19 s22
          s21 s24 s23 q2 s26
          s25 lq3 Hlen5 Hdim3 H98
          H88 H99 H100 q8 s28
          s27 lq4 Hlen6 Hdim4 H97
          H103 H104 H105 s30 r0
          old2 n4 Hlookup4 s29 H106).
      }
    }
    {
      process_step.
      invert_Alice.
      invert_Alice.
      invert_Alice.
      invert_Alice.

      process_step.
      process_step.
      process_step.
      process_step.
      process_step.
      process_step.
      {
        repeat match goal with
        |[H: context [should_swap] |- _] =>
          clear H
        |[H: context [should_swap_no_newq] |- _] =>
          clear H
        |[H: ?x = ?x |- _] =>
          clear H
        |[H: _ <> _ |- _] =>
          clear H
        |[H: forall _, (Bool _) <> _ |- _] =>
          clear H
        end.
        exact (@QuantumTeleportation_correct_goal_5
          starting_qstate end_state actions H1 s'' H5
          v'1 H2 la0 s0 v'
          Hfresh s s2 v'2 Hfresh0
          s1 s''0 H4 H19 la1
          q0 s4 s3 lq Hlen
          Hdim H32 H31 H34 H35
          q3 s6 s5 lq0 Hlen0
          Hdim0 H H38 H39 H40
          s8 old n Hlookup s7
          s10 old0 n0 Hlookup0 s9
          s12 old1 n1 Hlookup1 s11
          q s13 lq1 Hlen1 Hdim1
          H37 H47 H62 H63 q1
          s14 lq2 Hlen2 Hdim2 H53
          H65 H67 H68 q2 s15
          pi1 q4 n2 Hprob Hlookup2
          Hlen3 Hnonzero H66 H70 q5
          s16 pi0 q6 n3 Hprob0
          Hlookup3 Hlen4 Hnonzero0 H71 H73
          s18 s17 s20 s19 s22
          s21 s24 s23 q7 s26
          s25 lq3 Hlen5 Hdim3 H86
          H96 H97 H98 s28 r0
          old2 n4 Hlookup4 s27 H99).
      }
      process_step.
      process_step.
      {
        repeat match goal with
        |[H: context [should_swap] |- _] =>
          clear H
        |[H: context [should_swap_no_newq] |- _] =>
          clear H
        |[H: ?x = ?x |- _] =>
          clear H
        |[H: _ <> _ |- _] =>
          clear H
        |[H: forall _, (Bool _) <> _ |- _] =>
          clear H
        end.
        exact (@QuantumTeleportation_correct_goal_6
          starting_qstate end_state actions H1 s'' H5
          v'1 H2 la0 s0 v'
          Hfresh s s2 v'2 Hfresh0
          s1 s''0 H4 H19 la1
          q0 s4 s3 lq Hlen
          Hdim H32 H31 H34 H35
          q3 s6 s5 lq0 Hlen0
          Hdim0 H H38 H39 H40
          s8 old n Hlookup s7
          s10 old0 n0 Hlookup0 s9
          s12 old1 n1 Hlookup1 s11
          q s13 lq1 Hlen1 Hdim1
          H37 H47 H62 H63 q1
          s14 lq2 Hlen2 Hdim2 H53
          H65 H67 H68 q2 s15
          pi1 q4 n2 Hprob Hlookup2
          Hlen3 Hnonzero H66 H70 q5
          s16 pi0 q6 n3 Hprob0
          Hlookup3 Hlen4 Hnonzero0 H71 H73
          s18 s17 s20 s19 s22
          s21 s24 s23 q7 s26
          s25 lq3 Hlen5 Hdim3 H86
          H96 H97 H98 s28 r0
          old2 n4 Hlookup4 s27 H99).
      }
      process_step.
      process_step.
      process_step.
      {
        repeat match goal with
        |[H: context [should_swap] |- _] =>
          clear H
        |[H: context [should_swap_no_newq] |- _] =>
          clear H
        |[H: ?x = ?x |- _] =>
          clear H
        |[H: _ <> _ |- _] =>
          clear H
        |[H: forall _, (Bool _) <> _ |- _] =>
          clear H
        end.
        exact (@QuantumTeleportation_correct_goal_7
          starting_qstate end_state actions H1 s'' H5
          v'1 H2 la0 s0 v'
          Hfresh s s2 v'2 Hfresh0
          s1 s''0 H4 H19 la1
          q0 s4 s3 lq Hlen
          Hdim H32 H31 H34 H35
          q3 s6 s5 lq0 Hlen0
          Hdim0 H H38 H39 H40
          s8 old n Hlookup s7
          s10 old0 n0 Hlookup0 s9
          s12 old1 n1 Hlookup1 s11
          q s13 lq1 Hlen1 Hdim1
          H37 H47 H62 H63 q1
          s14 lq2 Hlen2 Hdim2 H53
          H65 H67 H68 q2 s15
          pi1 q4 n2 Hprob Hlookup2
          Hlen3 Hnonzero H66 H70 q5
          s16 pi0 q6 n3 Hprob0
          Hlookup3 Hlen4 Hnonzero0 H71 H73
          s18 s17 s20 s19 s22
          s21 s24 s23 q7 s26
          s25 lq3 Hlen5 Hdim3 H86
          H96 H97 H98 s28 r0
          old2 n4 Hlookup4 s27 H99).
      }
      process_step.
      process_step.
      process_step.
      {
        repeat match goal with
        |[H: context [should_swap] |- _] =>
          clear H
        |[H: context [should_swap_no_newq] |- _] =>
          clear H
        |[H: ?x = ?x |- _] =>
          clear H
        |[H: _ <> _ |- _] =>
          clear H
        |[H: forall _, (Bool _) <> _ |- _] =>
          clear H
        end.
        exact (@QuantumTeleportation_correct_goal_8
          starting_qstate end_state actions H1 s'' H5
          v'1 H2 la0 s0 v'
          Hfresh s s2 v'2 Hfresh0
          s1 s''0 H4 H19 la
          q0 s4 s3 lq Hlen
          Hdim H32 H31 H34 H35
          q3 s6 s5 lq0 Hlen0
          Hdim0 H H38 H39 H40
          s8 old n Hlookup s7
          s10 old0 n0 Hlookup0 s9
          s12 old1 n1 Hlookup1 s11
          q s13 lq1 Hlen1 Hdim1
          H37 H47 H62 H63 q1
          s14 lq2 Hlen2 Hdim2 H53
          H65 H67 H68 q2 s15
          pi1 q4 n2 Hprob Hlookup2
          Hlen3 Hnonzero H66 H70 q5
          s16 pi0 q6 n3 Hprob0
          Hlookup3 Hlen4 Hnonzero0 H71 H73
          s18 s17 s20 s19 s22
          s21 s24 s23 q7 s26
          s25 lq3 Hlen5 Hdim3 H86
          H96 H97 H98 q8 s28
          s27 lq4 Hlen6 Hdim4 H95
          H101 H102 H103 s30 r2
          old2 n4 Hlookup4 s29 H104).
      }
    }
  Unshelve.
  Transparent insert.
  all: abstract (
    simpl;
    apply NoDup_Permutation;
    [repeat constructor; simpl; unfold Alice, Bob, Source, Env; intuition congruence
    | repeat constructor; simpl; unfold Alice, Bob, Source, Env; intuition congruence
    | intros p; simpl; unfold Alice, Bob, Source, Env; tauto]
  ).
  Opaque insert.
Qed.
 
