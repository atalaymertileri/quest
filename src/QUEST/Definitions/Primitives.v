From SQIR Require Import SQIR UnitaryOps.
Require Import Reals Nat Lia List Bool String.
Require Import Automation ListUtils FMap.
Require Import Coq.Logic.Classical_Prop.
Require Import header.

Notation "x !" := (proj1_sig x)(at level 0).

Parameter qubit_reference: Type.
Parameter Instance qr_dec: EqDec qubit_reference.
Parameter fresh_qubit_reference : forall (lq: list qubit_reference), {q: qubit_reference | ~In q lq}.

Local Open Scope nat_scope.
Definition state_vector n := Matrix (2^n) 1.

(*nat in the finite map represents qubit's index in the state. Indexes start from 0 *)
Definition quantum_map_wf (qm: finite_map qubit_reference (participant * nat)) :=
NoDup (map (fun qpn => snd (snd qpn)) qm.(elems _ _)) /\ (*Indexes are distinct*)
Forall (fun n => n < length (qm.(elems _ _)))%nat (map (fun qpn => snd (snd qpn)) qm.(elems _ _)). (*Indexes are inbounds*)

Definition state_vector_wf {dim:nat} (q: state_vector dim) :=  @WF_Matrix (2 ^ dim) 1 q /\ 
  (dim <> 0 \/ (dim = 0 /\ q 0 0 = Complex.C1)) /\
    forall n, n < dim -> exists b, norm (proj n dim b × q) <> 0%R /\ @norm (2^dim) q = 1%R .
  
Lemma inner_product_kron : forall m n (u :  Vector m) (v : Vector n),
  ⟨u ⊗ v, u ⊗ v⟩ = (⟨u, u⟩ * ⟨v, v⟩)%C.
Proof.
  intros m n u v.
  unfold inner_product.
  transitivity (((adjoint u ⊗ adjoint v) × (u ⊗ v)) O O).
  - f_equal.
    apply kron_adjoint.
  - rewrite kron_mixed_product.
    unfold kron; simpl.
    reflexivity.
Qed.

Lemma norm_kron : forall m n (u : Vector m) (v : Vector n),
  @norm (m * n) (u ⊗ v) = (@norm m u * @norm n v)%R.
Proof.
  intros m n u v.
  unfold norm.
  rewrite inner_product_kron.
  unfold Cmult; simpl.
  rewrite (norm_real u), (norm_real v).
  replace (fst ⟨u, u⟩ * fst ⟨v, v⟩ - 0 * 0)%R
    with (fst ⟨u, u⟩ * fst ⟨v, v⟩)%R by ring.
  rewrite sqrt_mult.
  - reflexivity.
  - apply inner_product_ge_0.
  - apply inner_product_ge_0.
Qed.

Lemma norm_ket0 : norm (∣0⟩) = 1%R.
Proof.
  unfold norm, inner_product, Mmult, adjoint.
  simpl.
  replace (0 + (1 * 1 - - 0 * 0) + (0 * 0 - - 0 * 0))%R
    with 1%R by ring.
  rewrite sqrt_1.
  reflexivity.
Qed.

Lemma norm_unitary : forall n (U : Square n) (v : Vector n),
  WF_Unitary U -> WF_Matrix v -> norm (U × v) = norm v.
Proof.
  intros n U v [HU Hunitary] Hv.
  assert (Hsq : (norm (U × v) ^ 2)%R = (norm v ^ 2)%R).
  {
    rewrite norm_squared, norm_squared.
    rewrite inner_product_adjoint_l.
    rewrite <- Mmult_assoc.
    rewrite Hunitary.
    rewrite Mmult_1_l by exact Hv.
    reflexivity.
  }
  pose proof (norm_ge_0 (U × v)).
  pose proof (norm_ge_0 v).
  nra.
Qed.


(*qm is ownership map from references to participants * *)
(*and also q is vector of states, so matrix of correct size - describes global state of all qubits*)
Definition quantum_state := {qm: {qm: finite_map qubit_reference (participant * nat) | quantum_map_wf qm } & 
    {q: state_vector (length (qm!.(elems _ _))) |state_vector_wf q }}.
  
(*wrote this for below, maybe should be in FMap?*)
Lemma replace_or_add_fresh_append :
  forall A B (AEQ: EqDec A) (l: list (A * B)) (a:A) (b:B),
    ~ In a (map fst l)  ->
    replace_or_add (A:=A) (B:=B) (AEQ:=AEQ) l (a, b) = l ++ [(a, b)].
Proof.
  induction l as [| [hk hv] tl IH]; simpl; intros a b Hnot.
  - reflexivity.
  - simpl in *. intros.
    destruct (AEQ hk a) as [Heq | Hneq].
    + (* hk = a contradicts freshness *)
      subst hk. exfalso. apply Hnot. left. reflexivity.
    + (* hk <> a, keep head and recurse *)
      f_equal.
      apply IH.
      intros Hin; apply Hnot. right; exact Hin.
Qed.

Lemma gen_contradiction: 
forall (P : bool ->Prop) ,
(P true /\
P false  -> False ) -> 
exists b : bool, ~(P b). 
Proof. 
  intros.
  pose proof (classic (P true /\ P false)).
  destruct H0. apply H in H0. contradiction.
  apply not_and_or in H0. destruct H0; eauto.
Qed.

Lemma replace_or_add_length_helper: 
  forall A B (AEQ:EqDec A)(a:A) (b:B) (l: list (A*B)),
  Datatypes.length l <> 0 -> 
  Datatypes.length (replace_or_add l (a, b)) <> 0.
Proof.
  intros.

assert (Hdest: (exists (b:B), In (a, b) l) \/ (forall b : B, ~ In (a, b) l)).
{
  destruct (classic (exists b : B, In (a, b) l)) as [Hex | Hnex].
  - left. exact Hex.
  - right. intros b' Hin.
    apply Hnex. exists b'. exact Hin. }
  destruct Hdest. rewrite replace_or_add_In_length; eauto.
  rewrite replace_or_add_not_In_length; eauto.

Qed.
  
Lemma proj_sum: 
forall n m, n < m -> proj n m true .+ proj n m false = (I (2^m)).
Proof. 
  intros.
  unfold proj.
  unfold pad_u.
  unfold pad.
  unfold bool_to_matrix.
  destruct (n+1 <=? m) eqn: E. 
  {
    remember (I (2 ^ n)) as I'.
    remember (∣1⟩⟨1∣) as A1.
    remember (∣0⟩⟨0∣) as A0.
    remember (I (2 ^ (m - (n + 1)))) as I''.
    setoid_rewrite <- kron_plus_distr_r. (*[] SETOID*)
    setoid_rewrite <- kron_plus_distr_l.
    assert (Mplus10: WF_Matrix A1 -> WF_Matrix A0 -> (@Mplus (Nat.pow (S (S O)) (S O)) (Nat.pow (S (S O)) (S O)) A1 A0)= I 2). {
  subst. intros.
  apply functional_extensionality.
  intros.
  apply functional_extensionality.
  intro y.
  unfold Mplus.
  assert(H100: ∣1⟩⟨1∣ 0 0 = 0%R). {
    vm_compute. repeat rewrite Rplus_0_l.
    repeat rewrite Rmult_0_l.
    repeat rewrite Rplus_0_l.
    assert ((-0)%R = 0%R) by lra.
    rewrite H2. clear H2.
    auto.
  }
  assert(H101: ∣1⟩⟨1∣ 0 1 = 0%R). {
    vm_compute. repeat rewrite Rplus_0_l.
    repeat rewrite Rmult_0_l.
    repeat rewrite Rplus_0_l.
    assert ((-0)%R = 0%R) by lra.
    rewrite H2. clear H2.
    auto.
  }
  assert(H10y: y > 1 -> ∣1⟩⟨1∣ 0 y = 0%R). {
    intros. vm_compute. repeat rewrite Rplus_0_l.
    repeat rewrite Rmult_0_l.
    repeat rewrite Rplus_0_l. 
    assert ((-0)%R = 0%R) by lra.
    rewrite H3. clear H3.
    auto.
  }

  assert(H110: ∣1⟩⟨1∣ 1 0 = 0%R). {
    vm_compute. 
    repeat rewrite Rplus_0_l.
    repeat rewrite Rmult_0_l.
    repeat rewrite Rmult_0_r.
    repeat rewrite Rplus_0_l.
    repeat rewrite Rplus_0_r.
    rewrite Rmult_1_l.
    assert ((-0)%R = 0%R) by lra.
    rewrite H2. clear H2.
    assert ((-R0)%R = R0%R) by lra.
    rewrite H2. clear H2.
    auto.
  }
  assert(H111: ∣1⟩⟨1∣ 1 1 = 1%R). {
    vm_compute. repeat rewrite Rplus_0_l.
    repeat rewrite Rmult_0_l.
    repeat rewrite Rmult_1_l.
    assert ((-0)%R = 0%R) by lra.
    rewrite H2. clear H2.
    repeat rewrite Rplus_0_r.
    assert ((-R0)%R = R0%R) by lra. rewrite H2. clear H2.
    auto.
  }

  assert(H11y: y > 1 -> ∣1⟩⟨1∣ 1 y = 0%R). {
    intros. vm_compute. 
    repeat rewrite Rplus_0_l.
    repeat rewrite Rmult_1_l.
    repeat rewrite Rmult_0_l.
    assert ((-0)%R = 0%R) by lra.
    rewrite H3. clear H3.
    repeat rewrite Rplus_0_r.
    assert (y <> 1) as Hy by lia.
    destruct y as [| y'].
    - simpl in H2; lia.
    - 
      destruct y' as [| y''].
      + simpl in H2; lia.
      + assert ((-R0)%R = R0%R) by lra. rewrite H3. auto.
  }

  assert(H000: ∣0⟩⟨0∣ 0 0 = 1%R). {
    vm_compute. repeat rewrite Rplus_0_l.
    repeat rewrite Rmult_0_l.
    repeat rewrite Rmult_1_l.
    assert ((-0)%R = 0%R) by lra.
    rewrite H2. clear H2.
    repeat rewrite Rplus_0_r.
    assert ((-R0)%R = R0%R) by lra.
    rewrite H2. clear H2.
    auto.
  }
  assert(H001: ∣0⟩⟨0∣ 0 1 = 0%R). {
    vm_compute. repeat rewrite Rplus_0_l.
    repeat rewrite Rmult_0_l.
    repeat rewrite Rmult_1_l.
    assert ((-0)%R = 0%R) by lra.
    rewrite H2. clear H2.
    repeat rewrite Rplus_0_r.
    assert ((-R0)%R = R0%R) by lra.
    rewrite H2. clear H2.
    auto.
  }
  assert(H00y: y > 1 -> ∣0⟩⟨0∣ 0 y = 0%R). {
    intros. vm_compute. 
    repeat rewrite Rplus_0_l.
    repeat rewrite Rmult_1_l.
    repeat rewrite Rmult_0_l.
    assert ((-0)%R = 0%R) by lra.
    rewrite H3. clear H3.
    repeat rewrite Rplus_0_r.
    assert (y <> 1) as Hy by lia.
    destruct y as [| y'].
    - simpl in H2; lia.
    - 
      destruct y' as [| y''].
      + simpl in H2; lia.
      + assert ((-R0)%R = R0%R) by lra. rewrite H3. auto.
  }


  assert(H010: ∣0⟩⟨0∣ 1 0 = 0%R). {
    vm_compute. repeat rewrite Rplus_0_l.
    repeat rewrite Rmult_0_l.
    repeat rewrite Rplus_0_l.
    assert ((-0)%R = 0%R) by lra.
    rewrite H2. clear H2. auto.
  }
  assert(H011: ∣0⟩⟨0∣ 1 1 = 0%R). {
    vm_compute. repeat rewrite Rplus_0_l.
    repeat rewrite Rmult_0_l.
    repeat rewrite Rplus_0_l.
    assert ((-0)%R = 0%R) by lra.
    rewrite H2. clear H2. auto.
  }
  assert(H01y: y > 1 -> ∣0⟩⟨0∣ 1 y = 0%R). {
    intros. vm_compute. 
    repeat rewrite Rplus_0_l.
    repeat rewrite Rmult_0_l.
    assert ((-0)%R = 0%R) by lra.
    rewrite H3. clear H3.
    repeat rewrite Rplus_0_l.
    auto.

  }

  assert(Hx10: forall x y, x > 1 -> ∣1⟩⟨1∣ x y = 0%R /\ ∣0⟩⟨0∣ x y = 0%R). {
    intros. split.
    pose proof (WF_qubit1 x0 0).
    unfold Mmult.
    simpl.
    rewrite H3. 
    rewrite Cplus_0_l.
    rewrite Cmult_0_l. auto. left. auto.
    pose proof (WF_qubit0 x0 0).
    unfold Mmult.
    simpl.
    rewrite Cplus_0_l.
    rewrite H3. 
    rewrite Cmult_0_l. auto. left. auto.
  }

  assert (Hx: x = 0 \/ x = 1 \/ x > 1) by lia.
  assert (Hy: y = 0 \/ y = 1 \/ y > 1) by lia.

  destruct Hx as [Hx0 | [Hx1 | Hcontra]].
  {
    destruct Hy as [Hy0 | [Hy1 | Hcontra]]; subst.
    rewrite H100. rewrite H000. unfold I. simpl. apply Cplus_0_l.
    rewrite H101. rewrite H001. unfold I. simpl. apply Cplus_0_l.
    rewrite H10y; auto.  rewrite H00y; auto.
    pose proof (WF_I 2 0 y ). rewrite H2. apply Cplus_0_l. right. lia.
  }
  {
    destruct Hy as [Hy0 | [Hy1 | Hcontra]]; subst.
    rewrite H110. rewrite H010. unfold I. simpl. apply Cplus_0_l.
    rewrite H111. rewrite H011. unfold I. simpl. apply Cplus_0_r.
    rewrite H11y; auto.  rewrite H01y; auto.
    pose proof (WF_I 2 1 y ). rewrite H2. apply Cplus_0_l. right. lia.
  }
  {
    pose proof (Hx10 x y Hcontra) as [H1xy H0xy].
    rewrite H1xy. rewrite H0xy. pose proof (WF_I 2 x y). rewrite H2. apply Cplus_0_l.
    left. lia.
  }
  }
    rewrite Mplus10. 
    subst.
    repeat rewrite id_kron.
    assert (2 ^ n * 2 * 2 ^ (m - (n + 1)) = 2^m). {
      assert (2 ^ n * 2 * 2 ^ (m - (n + 1)) = 2 ^ n * (2^1) * 2 ^ (m - (n + 1))). {
        rewrite (Nat.pow_1_r 2). auto.
      }
      rewrite H0. clear H0.
      repeat rewrite <- Nat.pow_add_r.
      assert ((n + 1 + (m - (n + 1))) = m) by lia.
      rewrite H0. clear H0. auto.
    }

  rewrite H0. clear H0. auto.
    subst. solve_wf. subst. solve_wf. 
  }
  {

    pose proof (leb_correct (1 + n) m H).
    rewrite Nat.add_comm in E.
    rewrite E in H0. discriminate. 
  }
Qed.


Lemma kron_nonzero : 
forall n m o p (A: Matrix n m ) (B: Matrix o p), o <> 0 -> p <> 0 -> WF_Matrix A -> WF_Matrix B -> A <> Zero -> B <> Zero -> A ⊗ B <> Zero.
Proof. 
    intros. 
    unfold not.
    intros Hcontra.
    assert (Hnonzero: forall n m (A: Matrix n m), A <> Zero -> exists (x y : nat), A x y <> 0%R ). {
      intros.
      assert ((forall x y, A0 x y = 0%R) -> A0 = Zero). {
        intros.
        apply functional_extensionality. intros. apply functional_extensionality.
        intros y.
        auto.
      }
      pose proof (imply_to_or (forall x y, A0 x y = 0%R ) (A0 = Zero) H6).
      destruct H7.
      pose proof (Classical_Pred_Type.not_all_ex_not nat (fun x => forall y : nat, A0 x y = 0%R)  H7).
      destruct H8 as [x Hx].
      pose proof (Classical_Pred_Type.not_all_ex_not nat (fun y => A0 x y = 0%R)  Hx).
      destruct H8 as [y Hy].
      exists x. exists y.
      auto.
      contradiction.
      }
    assert (Harg: forall i j, ( A ⊗ B) i j = 0%R). {
        rewrite Hcontra. auto.
      }
      unfold kron in Harg.
    apply Hnonzero in H3 as [xA [yA HA]].
    apply Hnonzero in H4 as [xB [yB HB]].
    specialize (Harg (xA * o + xB) (yA * p + yB)).
    rewrite Modulus.mod_add_l in Harg.
    rewrite Modulus.mod_add_l in Harg.
    rewrite Nat.div_add_l in Harg; auto.
    rewrite Nat.div_add_l in Harg; auto.
    destruct (Nat.lt_ge_cases yB p).
    destruct (Nat.lt_ge_cases xB o).
    rewrite Nat.div_small in Harg; auto. 
    rewrite Nat.div_small in Harg; auto. 
    rewrite Nat.mod_small in Harg; auto. 
    rewrite Nat.mod_small in Harg; auto. 
    rewrite Nat.add_comm in Harg. simpl in Harg. rewrite Nat.add_comm in Harg. simpl in Harg.
    apply Cmult_integral in Harg.
    destruct Harg; contradiction.
    unfold WF_Matrix in H3.
    unfold ge in H3.
    specialize (H2 xB yB).
    specialize (H2 (or_introl H4)). 
    rewrite H2 in HB.              
    contradiction.       
    unfold WF_Matrix in H2.
    unfold ge in H2.
    specialize (H2 xB yB).
    specialize (H2 (or_intror H3)). 
    rewrite H2 in HB.              
    contradiction.      
Qed.


Program Definition add_new_qubit (q_state : quantum_state) (p: participant)
(q : qubit_reference) (Hfresh : ~In q (map fst (elems _ _ (projT1 q_state)!))) : quantum_state :=
let index := length (elems _ _ (projT1 q_state)!) in 
(existT _ (exist _ (@insert _ qr_dec _ (projT1 q_state)! q (p, index)) _) (exist _ (@kron (2^index) 1 2 1 (projT2 q_state)! ∣0⟩) _)).
Next Obligation.
destruct q_state. simpl in *. clear s. destruct x. simpl in *.
split.
{
simpl.
pose proof (specs _ _ x). cleanup. rewrite replace_or_add_fresh_append; eauto. rewrite map_app. simpl.
destruct q0. apply NoDup_app_comm. simpl. constructor; eauto. 
intros Hnot. eapply Forall_forall in H2; eauto. lia.
}
{
  destruct q0.
simpl.
pose proof (specs _ _ x). rewrite replace_or_add_fresh_append. rewrite map_app. simpl.
  eapply Forall_forall. 
  intros. apply in_app_or in H2 as [H2' | Hx].
  rewrite length_app. simpl.
  eapply Forall_forall in H0; eauto. lia.
  simpl in *.
  destruct Hx.
  rewrite length_app. simpl. rewrite H2. lia. contradiction.
  auto.
}
Qed.
Next Obligation.
destruct (projT2 q_state) as [m [HmWF [Hzero Hproj]]].
simpl in *.
assert (Hnorm_m : @norm
  (2 ^ Datatypes.length
    (elems qubit_reference (participant * fin) (projT1 q_state)!)) m = 1%R).
{
  destruct Hzero as [Hdim_nonzero | [Hdim_zero Hentry]].
  - specialize (Hproj 0 ltac:(lia)) as [b [_ Hnorm]].
    exact Hnorm.
  - rewrite Hdim_zero in *.
    unfold norm, inner_product, Mmult, adjoint.
    simpl.
    rewrite Hentry.
    simpl.
    replace (0 + (1 * 1 - - 0 * 0))%R with 1%R by ring.
    rewrite sqrt_1.
    reflexivity.
}
split.
{apply WF_kron;simpl;try(auto).
rewrite replace_or_add_fresh_append. rewrite length_app. simpl. apply Nat.pow_add_r. auto.
solve_wf.
  } split. {
    destruct Hzero. left.
    apply replace_or_add_length_helper; eauto.
    cleanup; simpl; eauto.
  }
(*cond 2 for well formedness: 
forall n, n < dim -> 
exists b, norm (proj n dim b × q) <> 0%R.
*)
  rewrite replace_or_add_fresh_append. rewrite length_app. simpl.
  set (index := Datatypes.length (elems qubit_reference (participant * nat) (projT1 q_state)!)) in *.
  assert (Hindex: index = 0 \/ index <> 0) by (apply classic).
  destruct Hindex as [Hindex | Hindex].
{
  intros.
  destruct Hzero as [Hcontra | Hzero]. contradiction.
  assert (n = 0) by lia. (*basically we just need index>0 for a later part...*)
  subst.
  clear H.
  rewrite Hindex. simpl.
  unfold WF_Matrix in HmWF.
  rewrite Hindex in HmWF. simpl in HmWF.
  unfold proj.
  unfold pad_u.
  unfold pad.
  assert (0 + 1 <=? 1 = true) by eauto.
  rewrite H.
  unfold bool_to_matrix.
  exists false. simpl in *.
  rewrite kron_1_l. rewrite kron_1_r.
  unfold norm. simpl.
  cleanup; simpl.
  repeat rewrite Rplus_0_l.
  repeat rewrite Rmult_0_r.
  repeat rewrite Rmult_0_l.
  repeat rewrite Rmult_1_l.
  repeat rewrite Rplus_0_l.
  repeat rewrite Rmult_0_r.
  repeat rewrite Rmult_0_l.
  repeat rewrite Rmult_1_l.
  repeat rewrite Rminus_0_r.
  repeat rewrite Rplus_0_l.
  repeat rewrite Rmult_0_r.
  repeat rewrite Rmult_1_l.
  repeat rewrite Rplus_0_r.
  repeat rewrite Rminus_0_r.
  repeat rewrite Rmult_1_r.
  repeat rewrite Rmult_0_l.
  repeat rewrite Rplus_0_r.
  repeat rewrite Ropp_0.
  rewrite Rmult_0_r.
  rewrite Rminus_0_r.
  rewrite sqrt_1. lra.

  solve_wf.  
}
{

  intros.
   (*cases n = index or n < index*)
  destruct (Nat.eq_dec n index).
  { (*CASE 1 - n = index!*)
  subst. clear H.
  unfold proj. unfold pad_u. unfold pad.
  assert (index + 1 <=? index + 1 = true). apply Nat.leb_le. lia.
  rewrite H. 
  assert (H': (2 ^ (index + 1 - (index + 1))) = 1). {
    assert (index + 1 - (index + 1) = 0) by lia.
    rewrite H0. rewrite Nat.pow_0_r. lia.
  }
  rewrite H'. clear H'.
  exists false.
  split.
  {
  apply norm_nonzero_iff_nonzero. solve_wf.
  rewrite kron_assoc; try(solve_wf).
  remember (I (2 ^ index)) as A.
  remember ((@kron (Nat.pow (S (S O)) (S O)) (Nat.pow (S (S O))
  (S O)) (S O) (S O)
  (bool_to_matrix true) (I (S O)))) as B.
  remember m as C.
  remember (∣0⟩) as D.
  assert (Nat.pow 2 (add index 1) = mul (Nat.pow 2 index) 2). rewrite Nat.pow_add_r. eauto.
  rewrite H0. clear H0.
  assert (1 = 1 * 1). lia. 
  rewrite H0. clear H0.
  rewrite kron_mixed_product. subst.
  rewrite Mmult_1_l; auto.

  apply kron_nonzero; auto.
  solve_wf.
  unfold not.
  intros Hcontra.
  rewrite Hcontra in Hproj.
  unfold WF_Matrix in HmWF.
  assert (0 < index)by lia. (*[] THIS USES 0 < INDEX*)  
  specialize (Hproj 0 H0).
  destruct Hproj as [b [Hb _]].
  apply norm_nonzero_iff_nonzero in Hb.
  rewrite Mmult_0_r in Hb.
  contradiction. solve_wf.

  remember ((@Mmult (S (mul (S O) (S O))) (S (mul (S O) (S O))) (S O)
(@kron (Nat.pow (S (mul (S O) (S O))) (mul (S O) (S O)))
(Nat.pow (S (mul (S O) (S O))) (mul (S O) (S O)))
(mul (S O) (S O)) (mul (S O) (S O))
(bool_to_matrix false) (I (mul (S O) (S O)))) qubit0)) as A.
  simpl in HeqA.
  rewrite kron_1_r in HeqA.
  assert (A 0 0 <> 0%R). {

    subst. unfold Mmult. simpl.
    assert (⟨0∣ 0 0 = 1%R). vm_compute. assert ((- R0)%R = R0). lra.
    rewrite H0. auto.
    rewrite H0.
    repeat rewrite Cplus_0_l.
    repeat rewrite (Cmult_1_l).
    rewrite Cmult_0_r.
    rewrite Cplus_0_r.
    unfold Complex.C1. 
    unfold not.
    intros Hcontra. injection Hcontra. lra.
  }
  unfold not. intros. rewrite H1 in H0. unfold Zero in H0. contradiction.
  }
  {
    rewrite Nat.pow_add_r.
    simpl.
    rewrite norm_kron, Hnorm_m, norm_ket0.
    lra.
  }
  }
  {(*CASE 2 - n < index!!*)
  assert (n < index).
  {lia. }
  clear H. clear n0.
  specialize (Hproj n H0) as [b' [Hnorm Hnormalized]].
  exists b'.
  split.
  {

  assert (Htest : proj n (index + 1) b' = (proj n index b') ⊗ (I 2)).
  {
    unfold proj. unfold pad_u. unfold pad. 
  assert ( n + 1 <=? index + 1 = true) as H'. {apply Nat.leb_le. lia. }
  rewrite H'. clear H'. 
  assert (n + 1 <=? index = true) as H'. {unfold lt in H0. apply Nat.leb_le. lia. }
  rewrite H'.
  assert(H: 2^(index + 1 - (n + 1)) = 2^(index - (n+1)) * 2). {
    assert (index + 1 - (n + 1) = index - (n + 1) +1). lia.
    rewrite H. rewrite Nat.pow_add_r. simpl. reflexivity.
  }
  rewrite H. clear H.
  rewrite <- (id_kron (2 ^ (index - (n + 1))) 2).
  repeat rewrite <- kron_assoc; try(solve_wf).
  }
  rewrite Htest.
  apply norm_nonzero_iff_nonzero. solve_wf.
  assert (Hkron_mixed_product: 
    (@Mmult (Nat.pow (S (S O)) (add index (S O)))
(Nat.pow (S (S O)) (add index (S O))) (S O)
(@kron (Nat.pow (S (S O)) index) (Nat.pow (S (S O)) index) (S (S O))
(S (S O)) (proj n index b') (I (S (S O))))
(@kron (pow (S (S O)) index) (S O) (S (S O)) (S O) m qubit0)) = @kron _ 1 _ _  (proj n index b' × m) ((I 2) × ∣0⟩)
  ).
  remember (proj n index b') as A.
  remember (I 2) as B.
  remember m as C.
  remember ( ∣0⟩) as D.
  assert (Nat.pow 2 (add index 1) = mul (Nat.pow 2 index) 2). rewrite Nat.pow_add_r. eauto.
  rewrite H. clear H.
  apply kron_mixed_product.

  rewrite Hkron_mixed_product.

  apply kron_nonzero; auto; try(solve_wf).
  rewrite norm_nonzero_iff_nonzero in Hnorm. auto. solve_wf.
  unfold not. intro Hcontra.
  assert ( (I 2 × ∣0⟩) 0 0  = @Zero 2 1 0 0). rewrite Hcontra. auto.
  unfold Mmult in H. unfold Zero in H. simpl in H.
  unfold I in H. simpl in H.
  unfold Complex.C1 in H. rewrite Cmult_1_l in H. 
  rewrite Cmult_0_l in H.
  rewrite Cplus_0_l in H.
  rewrite Cplus_0_r in H.
  apply pair_equal_spec in H.
  destruct H as [Hcontra2 _ ]. lra.
  }
  {
    rewrite Nat.pow_add_r.
    simpl.
    rewrite norm_kron, Hnormalized, norm_ket0.
    lra.
  }
}
}
all: assumption.
Qed.

Program Definition transfer_qubit (qm : finite_map qubit_reference (participant * nat)) (HqmWf: quantum_map_wf qm) (sv : state_vector (Datatypes.length (elems qubit_reference (participant * nat) qm))) (HsvWf: state_vector_wf sv) (new: participant) (q: qubit_reference) 
: {oqs: option quantum_state | forall q_state', oqs = Some q_state' ->
exists old n, 
qm q = Some (old, n) /\
(proj1_sig (projT1 q_state')) = (insert (KEQ:= qr_dec) qm q (new, n))
/\ (projT2 q_state')! = sv}:=
match qm q with
| None => None
| Some (p, n) => exist _ (Some (existT _ (exist _ (insert (KEQ:= qr_dec) qm q (new, n)) _) (exist _ sv _))) _
end.
Next Obligation.
simpl in *. clear sv HsvWf. destruct qm. destruct specs. destruct HqmWf. simpl in *. symmetry in Heq_anonymous. rewrite <- (i q (p,n)) in Heq_anonymous.
split.
{
  simpl. apply (replace_or_add_map_NoDup qubit_reference participant nat _ elems q (p, n) (new,n));auto.
}
{simpl. apply Forall_forall. intros.  
rewrite Forall_forall in H0. 
rewrite replace_or_add_In_length.
apply H0. 
apply in_map_iff in H1 as [y [H1 H2]].
destruct(qr_dec (fst y) q).
{pose proof replace_or_add_In_snd_eq. assert( x = n).
{
  specialize (H3 _ _ qr_dec elems y (q, (new, n))).
  simpl in *. subst. specialize (H3 n0 H2 eq_refl). rewrite H3. auto.
} 
 pose proof in_map as in_map. apply (in_map _ _ (fun qpn : qubit_reference * (participant * nat) =>
snd (snd qpn)) elems (q, (p, x))). rewrite H4. assumption. }
{
  pose proof (replace_or_add_In_neq _ _ qr_dec elems y (q, (new, n))).
  rewrite H3 in H2. subst. simpl in *. apply in_map_iff. exists y. auto.
  auto.
}
exists (p, n). auto.
}
Qed.
Next Obligation.
unfold state_vector_wf in *.
symmetry in  Heq_anonymous;
eapply specs in Heq_anonymous.
repeat rewrite replace_or_add_In_length; eauto.
Qed.
Next Obligation.
  simpl.
  do 2 eexists; split; eauto.
Qed.

(* Total operational form once the map lookup has been established.  The
   proof-carrying partial API above remains available to metatheory that needs
   its postcondition. *)
Definition transfer_qubit_from_lookup
    (qm : finite_map qubit_reference (participant * nat))
    (HqmWf : quantum_map_wf qm)
    (sv : state_vector (Datatypes.length (elems qubit_reference (participant * nat) qm)))
    (HsvWf : state_vector_wf sv) (new : participant) (q : qubit_reference)
    (old : participant) (n : nat) (Hlookup : qm q = Some (old, n))
    : quantum_state :=
  existT _
    (exist _ (insert (KEQ:=qr_dec) qm q (new, n))
      (transfer_qubit_obligation_2 qm HqmWf new q old n (eq_sym Hlookup)))
    (exist _ sv
      (transfer_qubit_obligation_3 qm HqmWf sv HsvWf new q old n
        (eq_sym Hlookup))).




Fixpoint make_perm_matrix_base (size start: nat) (indexes: list nat) : base_ucom size := 
match indexes with 
| [] => uapp1 (U_R 0 0 0) 0
| h :: t => if (start =? h) then (make_perm_matrix_base size (start + 1) t)  else useq (SWAP start h) (make_perm_matrix_base size (start + 1) t)
end.

(*conditions for swap:*)

Lemma perm_matrix_well_typed:
forall  indexes size start,
size > 0 ->
Forall (fun i => i < size) indexes -> 
NoDup indexes -> 
start <= size ->
(Datatypes.length indexes + start <=  size) ->
uc_well_typed (make_perm_matrix_base size start indexes).
Proof.
  induction indexes.
  intros.
  repeat constructor. lia.
  intros.
  simpl. destruct (start =?a) eqn: E.
  apply IHindexes; auto.
  apply Forall_forall.
  intros.
  rewrite Forall_forall in H0.
  apply H0. unfold In. right. auto.
  apply NoDup_cons_iff in H1 as [_ H']. assumption.  

  apply (Nat.le_trans (start + 1) (S (Datatypes.length indexes + start)) (size)).
  rewrite Nat.add_comm.
  apply le_n_S.
  lia.

  auto.
  rewrite Nat.add_assoc.
  simpl in H3.
  lia.

  constructor.
  apply uc_well_typed_SWAP. simpl in H3. 
  repeat split; try(lia).
  rewrite Forall_forall in H0.
  apply H0. 
  
  unfold In. left. auto. 
  rewrite <- Nat.eqb_eq.
  rewrite E. auto.

  apply IHindexes. lia. 
  rewrite Forall_forall in H0. apply Forall_forall. intros.
  apply H0. unfold In. right. assumption.
  apply NoDup_cons_iff in H1 as [_ H']. assumption.  
  simpl in H2.
  apply (Nat.le_trans (start + 1) (S (Datatypes.length indexes + start)) (size)).
  rewrite Nat.add_comm.
  apply le_n_S.
  lia.
  auto.
  rewrite Nat.add_assoc.
  simpl in H3.
  lia.
Qed.

Opaque ueval_r.
Program Definition base_to_ucom {state_dim U_dim: nat} (U: base_Unitary U_dim) (l: list nat) (Hl: length l = U_dim /\ NoDup l /\ Forall (fun i => i < state_dim) l): 
{c : base_ucom state_dim | WF_Unitary (uc_eval c)}:= 
match U with
| U_R x y z => 
  match l with
  | q::nil => uapp1 (U_R x y z) q
  | _ => _
  end
| U_CNOT => 
  match l with
  | q1::q2::nil => uapp2 U_CNOT q1 q2
  | _ => _
  end
end.
Next Obligation.
eapply ueval_r_unitary.
inversion H1; eauto.
Qed.
Next Obligation.
destruct l; simpl in *; try congruence.
destruct l; simpl in *; try congruence.
Qed.
Next Obligation.
eapply ueval_cnot_unitary.
inversion H0; subst; simpl in *.
intuition eauto.
inversion H1; eauto.
inversion H1; subst.
inversion H4; eauto.
Qed.
Next Obligation.
destruct l; simpl in *; try congruence.
destruct l; simpl in *; try congruence.
destruct l; simpl in *; try congruence.
Qed.


Program Definition apply_unitary_to_state
  {state_dim U_dim : nat} (Hstate_dim: state_dim > 0) (HU_dim: U_dim <= state_dim)
  (st : state_vector state_dim) (HstWf: state_vector_wf st) (*I think state_dim must be more than 0, else we have no state to do the operation on.*)
  (U : base_Unitary U_dim) (*I think U_dim must be less than state_dim, since there must be enough distinct qubits to apply to.*)
  (indexes : list nat)
  (Hindexes: length indexes = U_dim /\ NoDup indexes /\ Forall (fun i => i < state_dim) indexes /\ U_dim > 0) (*indexes must all refer to valid, distinct qubits and match dim of gate.*)
  : { v : state_vector state_dim | state_vector_wf v /\ v = (uc_eval (base_to_ucom U indexes _)! × st)} :=
let U_full := uc_eval (base_to_ucom U indexes _) in 
let v' := Mmult (o:=1) U_full st in
  exist _ v' _. 
Next Obligation.
rename n into HnoDup.
split; eauto. 
rename f into HUdim_lt_state.
destruct HstWf as [HstWF [Hzero HstNorm]].
set (U_dim := Datatypes.length indexes).
set (U_com := (uc_eval
(base_to_ucom U indexes
(eq_ind U_dim (fun U_dim0 : nat => U_dim0 <= state_dim -> base_Unitary U_dim0 -> U_dim = U_dim0 /\ NoDup indexes /\ Forall (fun i : nat => i < state_dim)
indexes)
(fun (_ : U_dim <= state_dim) (_ : base_Unitary U_dim) => conj eq_refl (conj HnoDup HUdim_lt_state)) U_dim eq_refl HU_dim U))!)).
assert(HUnitary: WF_Unitary (U_com)). {
  destruct (
(base_to_ucom U indexes
(eq_ind U_dim (fun U_dim0 : nat => U_dim0 <= state_dim -> base_Unitary U_dim0 -> U_dim = U_dim0 /\ NoDup indexes /\ Forall (fun i : nat => i < state_dim)
indexes)
(fun (_ : U_dim <= state_dim) (_ : base_Unitary U_dim) => conj eq_refl (conj HnoDup HUdim_lt_state)) U_dim eq_refl HU_dim U))).
  simpl in *.
  subst U_com; eauto.
}
unfold state_vector_wf. split.
{
  repeat apply WF_mult; try(apply WF_pad; apply WF_uc_eval). apply WF_uc_eval. auto. }

split. { left. lia. }
intros. pose proof H. apply HstNorm in H as [b' [Hb Hnormalized]].
assert (HprojectedWF : @WF_Matrix (2 ^ state_dim) 1
    (proj n state_dim b' × st)).
{ apply (@WF_mult (2 ^ state_dim) (2 ^ state_dim) 1
    (proj n state_dim b') st); [apply WF_proj|exact HstWF]. }
assert (Hbmatrix : @Mmult (2 ^ state_dim) (2 ^ state_dim) 1
    (proj n state_dim b') st <> @Zero (2 ^ state_dim) 1).
{ apply (proj1 (@norm_nonzero_iff_nonzero (2 ^ state_dim)
    (proj n state_dim b' × st) HprojectedWF)); exact Hb. }
assert (Hexists : exists b,
    norm (proj n state_dim b × (U_com × st)) <> 0%R).
{
apply (gen_contradiction (fun b =>  norm (proj n state_dim b × (U_com × st)) = 0%R)). 
intros [Htrue Hfalse].
apply norm_zero_iff_zero in Htrue. apply norm_zero_iff_zero in Hfalse.
  assert (Hadd: @Mplus (2^state_dim) 1 (proj n state_dim true × (U_com × st))  (proj n state_dim false × (U_com × st))  = Zero ). {rewrite Htrue. rewrite Hfalse. apply Mplus_0_r. }
  rewrite <- Mmult_plus_distr_r in Hadd. rewrite proj_sum in Hadd.  rewrite Mmult_1_l in Hadd.
  destruct HUnitary as [HWF Hadj].
  assert( Hinv: @Mmult _ _ 1 ((adjoint U_com)× U_com) st = Zero).
  rewrite Mmult_assoc. rewrite Hadd. apply Mmult_0_r.
  rewrite Hadj in Hinv.
  rewrite Mmult_1_l in Hinv.
  rewrite Hinv in Hbmatrix.
  rewrite Mmult_0_r in Hbmatrix. contradiction.
  all: auto.
  all: repeat apply WF_mult; auto.
  all: try apply WF_proj.
  all: apply WF_uc_eval.
}
destruct Hexists as [b Hnonzero].
exists b. split; [exact Hnonzero|].
match goal with
| |- context [norm (?op × st)] => set (U_actual := op)
end.
assert (Hgate_eq : U_actual = U_com).
{ unfold U_actual, U_com. f_equal. }
rewrite Hgate_eq.
  rewrite (norm_unitary _ _ _ HUnitary HstWF).
  exact Hnormalized.

Qed.


Lemma combine_exists_helper:
forall A B C (la: list A) (lb:list (B*C)) c,
In c (map snd lb) ->
Datatypes.length la = Datatypes.length lb ->
exists a b, In (a,(b,c)) (combine la lb).
Proof.
  intros.
  rewrite in_map_iff in H. destruct H as [[p n] [Hpn Hin]]; subst.
  generalize H0. generalize la.
  induction lb as [|[p' x'] lpn IH]; intros lq' Hlen. contradiction.
  destruct lq' as [|hq tq]. simpl in *. inversion Hlen.
  simpl in Hin. destruct Hin as [Hin| Hin].
  inversion Hin; subst; clear Hin.
  exists hq. exists p. simpl. left. auto.
  simpl.  

  simpl in Hlen.
  assert (H': Datatypes.length tq >= Datatypes.length lpn). lia.
  pose proof (in_combine_ex_l tq lpn H' (p,n) Hin). destruct H as [q H1]. exists q. exists p. right.
  auto.
Qed. 

Definition apply_unitary_to_state_wf_helper {state_dim: nat} {P: _ -> Prop} (v : { v : state_vector state_dim | state_vector_wf v /\ P v}) : state_vector_wf v!.
destruct v, a; simpl; eauto.
Qed. 


Fixpoint get_all_values {key value : Type} (qm : finite_map key value) (qs : list key)
  : option (list value) :=
  match qs with
  | [] => Some []
  | q :: tl =>
      match qm q, get_all_values qm tl with
      | Some v, Some vs => Some (v :: vs)
      | _, _ => None
      end
  end.

Lemma get_all_values_spec : forall (key value : Type)
    (qm : finite_map key value) qs vs,
  get_all_values qm qs = Some vs ->
  length vs = length qs /\
  forall kv, In kv (combine qs vs) -> qm (fst kv) = Some (snd kv).
Proof.
  intros key value qm qs.
  induction qs as [|q tl IH]; intros vs Hget.
  - simpl in Hget; inversion Hget; subst; split; [reflexivity |].
    intros [k v] Hin; contradiction.
  - simpl in Hget.
    destruct (qm q) as [v|] eqn:Hq; try discriminate.
    destruct (get_all_values qm tl) as [vstl|] eqn:Htl; try discriminate.
    inversion Hget; subst vs.
    destruct (IH vstl eq_refl) as [Hlen Hlook].
    split; [simpl; f_equal; exact Hlen |].
    intros [k v0] Hin.
    simpl in Hin.
    destruct Hin as [Hin | Hin].
    + inversion Hin; subst; exact Hq.
    + simpl in Hin. specialize (Hlook (k, v0) Hin). exact Hlook.
Qed.

Lemma get_all_values_some_of_lookups : forall (key value : Type)
    (qm : finite_map key value) qs,
  (forall q, In q qs -> exists v, qm q = Some v) ->
  exists vs, get_all_values qm qs = Some vs.
Proof.
  intros key value qm qs.
  induction qs as [|q tl IH]; intros Hlook.
  - exists []; reflexivity.
  - destruct (Hlook q (or_introl eq_refl)) as [v Hv].
    destruct (IH (fun q' Hin => Hlook q' (or_intror Hin))) as [vs Hvs].
    exists (v :: vs); simpl; rewrite Hv, Hvs; reflexivity.
Qed.

Definition get_all_values_certified {key value : Type}
    (qm : finite_map key value) (qs : list key)
    : option {vs : list value | get_all_values qm qs = Some vs} :=
  match get_all_values qm qs as result
    return get_all_values qm qs = result ->
      option {vs : list value | get_all_values qm qs = Some vs} with
  | Some vs => fun Hresult => Some (exist _ vs Hresult)
  | None => fun _ => None
  end eq_refl.

Lemma apply_unitary_indexes_wf : forall
  (qm : finite_map qubit_reference (participant * nat))
  (HqmWF : quantum_map_wf qm) (lq : list qubit_reference) (dim : nat)
  (Hdim: dim > 0)
  (Hlq : length lq = dim) lpn,
  NoDup lq -> get_all_values qm lq = Some lpn ->
  length (map snd lpn) = dim /\
  NoDup (map snd lpn) /\
  Forall (fun i => i < length (elems qubit_reference (participant * nat) qm))
    (map snd lpn) /\ dim > 0.
Proof.
  intros qm HqmWF lq dim Hdim Hlq lpn Hnd Hget.
  pose proof (get_all_values_spec qubit_reference (participant * nat)
    qm lq lpn Hget) as [Hgetlen Hgetlookup].
  unfold quantum_map_wf in HqmWF.
  destruct HqmWF as [Hglobalnd Hbounds].
  split.
  - rewrite length_map, Hgetlen, Hlq; reflexivity.
  - split.
    + assert (Hstmt : forall A B C (la : list A) (lb : list (B * C))
          (lab : list (A * (B * C))),
        NoDup (map (fun x => snd (snd x)) lab) ->
        NoDup la -> length la = length lb ->
        (forall a bc, In (a, bc) (combine la lb) -> In (a, bc) lab) ->
        NoDup (map snd lb)).
      {
        intros A0 B0 C0 xs.
        induction xs as [|headA tailA IH];
          intros values triples Htriples Hnd0 Hlen Hsub.
        - destruct values; simpl in Hlen; [constructor | discriminate].
        - destruct values as [|[headB headC] tailBC]; simpl in Hlen; [discriminate |].
          simpl; constructor.
          + intro Hin.
            assert (Hexists : exists otherA otherB,
              In (otherA, (otherB, headC)) (combine tailA tailBC)).
            { apply combine_exists_helper; eauto. }
            destruct Hexists as [otherA [otherB Hcombined]].
            assert (Htail : In (otherA, (otherB, headC)) triples).
            { apply Hsub. simpl; right; exact Hcombined. }
            apply in_combine_l in Hcombined.
            assert (Hhead : In (headA, (headB, headC)) triples).
            { apply Hsub. simpl; left; reflexivity. }
            assert (Heq : (headA, (headB, headC)) = (otherA, (otherB, headC))).
            { eapply NoDup_In_inj with (l := triples)
                (f := fun x : A0 * (B0 * C0) => snd (snd x)); eauto. }
            pose proof (proj1 (NoDup_cons_iff headA tailA) Hnd0) as [Hnot _].
            inversion Heq; subst.
            apply Hnot; exact Hcombined.
          + eapply IH.
            * exact Htriples.
            * exact (proj2 (proj1 (NoDup_cons_iff headA tailA) Hnd0)).
            * simpl in Hlen; lia.
            * intros otherA bc Hin. apply Hsub. simpl; right; exact Hin.
      }
      eapply Hstmt with (lab := elems qubit_reference (participant * nat) qm)
        (la := lq); eauto.
      intros q bc Hin.
      pose proof (Hgetlookup (q, bc) Hin) as Hlookup.
      pose proof (specs _ _ qm) as [_ Hspecs].
      apply (proj2 (Hspecs q bc)); exact Hlookup.
      split; eauto.
    + apply Forall_forall; intros x Hin.
      rewrite Forall_forall in Hbounds.
      apply Hbounds.
      assert (Hexists : exists q p, In (q, (p, x)) (combine lq lpn)).
      { apply combine_exists_helper; [exact Hin | symmetry; exact Hgetlen]. }
      destruct Hexists as [q [p Hpair]].
      pose proof (Hgetlookup (q, (p, x)) Hpair) as Hlookup.
      pose proof (specs _ _ qm) as [_ Hspecs].
      apply in_map_iff.
      exists (q, (p, x)); split; [reflexivity |].
      apply (proj2 (Hspecs q (p, x))); exact Hlookup.
Qed.

Definition apply_unitary
  (qm : finite_map qubit_reference (participant * nat))
  (HqmWF : quantum_map_wf qm)
  (sv : state_vector (length (elems qubit_reference (participant * nat) qm)))
  (HsvWf : state_vector_wf sv) {dim : nat} (U : base_Unitary dim)
  (lq : list qubit_reference) (Hlq : length lq = dim) (Hdim' : dim > 0): option quantum_state :=
  let state_dim := length (elems qubit_reference (participant * nat) qm) in
  match lt_dec 0 state_dim with
  | left Hstate =>
      match le_dec dim state_dim with
      | left Hdim =>
      match NoDup_dec (TEQ := qr_dec) lq with
      | left Hnd =>
          match get_all_values_certified qm lq with
          | None => None
          | Some certified =>
              let lpn := proj1_sig certified in
              let Hget := proj2_sig certified in
              let Hindexes := apply_unitary_indexes_wf qm HqmWF lq dim Hdim' Hlq lpn Hnd Hget in
              let state' := apply_unitary_to_state Hstate Hdim sv HsvWf U
                (map snd lpn) Hindexes in
              Some (existT _ (exist _ qm HqmWF)
                (exist _ state'! (apply_unitary_to_state_wf_helper state')))
          end
      | right _ => None
      end
      | right _ => None
      end
  | right _ => None
  end.

(* Removing a measured wire compacts the numerical labels of every wire to its
   right.  The map's key order is independent of the state-vector wire order,
   so the transform is defined pointwise over the finite map. *)
Definition shift_wire_index (index wire_index : nat) : nat :=
  if index <? wire_index then Nat.pred wire_index else wire_index.

Definition shift_qubit_index (index : nat) (owner_index : participant * nat)
    : participant * nat :=
  (fst owner_index, shift_wire_index index (snd owner_index)).

Program Definition reindex_quantum_map
    (qm : finite_map qubit_reference (participant * nat)) (index : nat)
    : finite_map qubit_reference (participant * nat) :=
  @Build_finite_map qubit_reference (participant * nat)
    (fun q => option_map (shift_qubit_index index) (qm q))
    (map (fun qv => (fst qv, shift_qubit_index index (snd qv)))
      (elems qubit_reference (participant * nat) qm)) _.
Next Obligation.
  destruct qm as [lookup entries [Hnodup Hspecs]]. simpl in *.
  split.
  - rewrite map_map. simpl. exact Hnodup.
  - intros q v. split.
    + intro Hin.
      apply in_map_iff in Hin.
      destruct Hin as [[q' v'] [Heq Hin]].
      inversion Heq; subst.
      assert (Hq : lookup q = Some v') by (apply Hspecs; exact Hin).
      simpl. rewrite Hq. reflexivity.
    + intro Hlookup.
      simpl in Hlookup.
      destruct (lookup q) as [v'|] eqn:Hq; simpl in Hlookup; try discriminate.
      inversion Hlookup; subst v.
      apply in_map_iff.
      exists (q, v'). split; [reflexivity|].
      apply Hspecs. exact Hq.
Qed.

Definition remove_and_reindex_qubit_map
    (qm : finite_map qubit_reference (participant * nat))
    (q : qubit_reference) (index : nat)
    : finite_map qubit_reference (participant * nat) :=
  reindex_quantum_map (delete (KEQ:=qr_dec) qm q) index.

Lemma remove_and_reindex_qubit_map_lookup_none : forall
    (qm : finite_map qubit_reference (participant * nat)) q index q',
  (remove_and_reindex_qubit_map qm q index) q' <> None <->
  q' <> q /\ qm q' <> None.
Proof.
  intros qm q index q'.
  unfold remove_and_reindex_qubit_map, reindex_quantum_map.
  change
    (option_map (shift_qubit_index index)
      (delete (KEQ:=qr_dec) qm q q') <> None <->
      q' <> q /\ qm q' <> None).
  destruct (qr_dec q q') as [Heq|Hneq].
  - subst q'. rewrite delete_eq. simpl. tauto.
  - rewrite delete_neq by exact Hneq.
    destruct (qm q') as [v|] eqn:Hmap; simpl.
    + split.
      * intros _. split; [congruence|discriminate].
      * intros [_ Hnone]. discriminate.
    + split; [intro Hfalse; contradiction|].
      intros [_ Hnone]. contradiction.
Qed.

Lemma map_wire_indices_remove_fst : forall
    (l : list (qubit_reference * (participant * nat))) q,
  map (fun qv => snd (snd qv)) (remove_fst (AEQ:=qr_dec) l q) =
  map snd (remove_fst (AEQ:=qr_dec)
    (map (fun qv => (fst qv, snd (snd qv))) l) q).
Proof.
  intros l q.
  induction l as [|[qv [owner index]] l IH]; simpl; [reflexivity|].
  destruct (qr_dec qv q); simpl.
  - rewrite map_map. simpl. reflexivity.
  - f_equal. exact IH.
Qed.

Lemma quantum_map_lookup_index_lt : forall
    (qm : finite_map qubit_reference (participant * nat))
    (Hqm : quantum_map_wf qm) q owner index,
  qm q = Some (owner, index) ->
  index < length (elems qubit_reference (participant * nat) qm).
Proof.
  intros qm Hqm q owner index Hlookup.
  destruct Hqm as [_ Hbounds].
  pose proof (specs qubit_reference (participant * nat) qm) as [_ Hspecs].
  assert (Hin : In (q, (owner, index))
    (elems qubit_reference (participant * nat) qm)) by (apply Hspecs; exact Hlookup).
  apply Forall_forall with (x := index) in Hbounds.
  - exact Hbounds.
  - apply in_map_iff. exists (q, (owner, index)). auto.
Qed.

Lemma shift_qubit_index_injective_away : forall index owner owner'
    old_index old_index',
  old_index <> index ->
  old_index' <> index ->
  shift_qubit_index index (owner, old_index) =
    shift_qubit_index index (owner', old_index') ->
  old_index = old_index'.
Proof.
  intros index owner owner' old_index old_index' Hneq Hneq' Heq.
  unfold shift_qubit_index, shift_wire_index in Heq; simpl in Heq.
  injection Heq as _ Hshift.
  destruct (index <? old_index) eqn:Hlt;
    destruct (index <? old_index') eqn:Hlt'; simpl in Hshift.
  - apply Nat.ltb_lt in Hlt. apply Nat.ltb_lt in Hlt'.
    apply Nat.pred_inj; [lia|lia|exact Hshift].
  - apply Nat.ltb_lt in Hlt. apply Nat.ltb_ge in Hlt'.
    destruct old_index as [|old_index]; simpl in Hshift; [lia|].
    lia.
  - apply Nat.ltb_ge in Hlt. apply Nat.ltb_lt in Hlt'.
    destruct old_index' as [|old_index']; simpl in Hshift; [lia|].
    lia.
  - apply Nat.ltb_ge in Hlt. apply Nat.ltb_ge in Hlt'. lia.
Qed.

Lemma delete_qubit_map_length : forall
    (qm : finite_map qubit_reference (participant * nat)) q owner index,
  qm q = Some (owner, index) ->
  S (length (elems qubit_reference (participant * nat)
    (delete (KEQ:=qr_dec) qm q))) =
    length (elems qubit_reference (participant * nat) qm).
Proof.
  intros qm q owner index Hlookup.
  pose proof (specs qubit_reference (participant * nat) qm) as [_ Hspecs].
  unfold delete; simpl.
  apply (@remove_fst_length_In qubit_reference qr_dec (participant * nat)
    (elems qubit_reference (participant * nat) qm) q (owner, index)).
  apply Hspecs; exact Hlookup.
Qed.

Lemma delete_qubit_index_not_in : forall
    (qm : finite_map qubit_reference (participant * nat))
    (Hqm : quantum_map_wf qm) q owner index,
  qm q = Some (owner, index) ->
  Forall (fun qv : qubit_reference * (participant * nat) =>
    snd (snd qv) <> index)
    (elems qubit_reference (participant * nat)
      (delete (KEQ:=qr_dec) qm q)).
Proof.
  intros qm Hqm q owner index Hlookup.
  destruct Hqm as [Hindices _].
  pose proof (specs qubit_reference (participant * nat) qm) as [Hkeys Hspecs].
  apply Forall_forall.
  intros [q' [owner' index']] Hin Hindex.
  unfold delete in Hin; simpl in Hin.
  assert (Hin_source : In (q', (owner', index'))
    (elems qubit_reference (participant * nat) qm)).
  { eapply remove_fst_In; exact Hin. }
  assert (Hin_measured : In (q, (owner, index))
    (elems qubit_reference (participant * nat) qm)).
  { apply Hspecs; exact Hlookup. }
  assert (Heq : (q', (owner', index')) = (q, (owner, index))).
  {
    eapply NoDup_In_inj with
      (l := elems qubit_reference (participant * nat) qm)
      (f := fun x : qubit_reference * (participant * nat) => snd (snd x));
      eauto.
  }
  inversion Heq; subst q' owner' index'.
  assert (Hnotq : ~ In q (map fst (remove_fst (AEQ:=qr_dec)
    (elems qubit_reference (participant * nat) qm) q))).
  { exact (@remove_not_In_2 qubit_reference (participant * nat) qr_dec
      (elems qubit_reference (participant * nat) qm) q Hkeys). }
  apply Hnotq.
  apply in_map_iff.
  exists (q, (owner, index)); split; [reflexivity|exact Hin].
Qed.

Lemma NoDup_shifted_qubit_indices : forall index
    (l : list (qubit_reference * (participant * nat))),
  NoDup (map (fun qv => snd (snd qv)) l) ->
  Forall (fun qv => snd (snd qv) <> index) l ->
  NoDup (map (fun qv => snd (shift_qubit_index index (snd qv))) l).
Proof.
  intros index l.
  induction l as [|[q [owner old_index]] l IH]; intros Hnd Hnot.
  - constructor.
  - simpl in Hnd.
    inversion Hnd as [|head_index tail_indices Hfresh Htail]; subst.
    rewrite Forall_forall in Hnot.
    assert (Hhead_not : old_index <> index).
    { change (snd (snd (q, (owner, old_index))) <> index).
      apply Hnot. simpl. auto. }
    assert (Htail_not : Forall
      (fun qv : qubit_reference * (participant * nat) =>
        snd (snd qv) <> index) l).
    { apply Forall_forall. intros qv Hin. apply Hnot. simpl. auto. }
    simpl. constructor.
    + intro Hin.
      apply in_map_iff in Hin.
      destruct Hin as [[q' [owner' old_index']] [Heq Hin]].
      simpl in Heq.
      assert (Htail_index_not : old_index' <> index).
      { apply Forall_forall with
          (x := (q', (owner', old_index'))) in Htail_not; assumption. }
      assert (Hold_eq : old_index = old_index').
      {
        eapply shift_qubit_index_injective_away with
          (owner := owner') (owner' := owner').
        - exact Hhead_not.
        - exact Htail_index_not.
        - unfold shift_qubit_index; simpl. f_equal. symmetry. exact Heq.
      }
      subst old_index'.
      apply Hfresh.
      apply in_map_iff.
      exists (q', (owner', old_index)). split; [reflexivity|exact Hin].
    + apply IH; assumption.
Qed.

Lemma remove_and_reindex_qubit_map_wf : forall
    (qm : finite_map qubit_reference (participant * nat))
    (Hqm : quantum_map_wf qm) q owner index,
  qm q = Some (owner, index) ->
  quantum_map_wf (remove_and_reindex_qubit_map qm q index).
Proof.
  intros qm Hqm q owner index Hlookup.
  destruct Hqm as [Hindices Hbounds].
  pose proof (delete_qubit_map_length qm q owner index Hlookup) as Hlen.
  pose proof (delete_qubit_index_not_in qm (conj Hindices Hbounds)
    q owner index Hlookup) as Hnot.
  assert (Hdeleted_indices : NoDup (map snd (remove_fst (AEQ:=qr_dec)
    (map (fun qv : qubit_reference * (participant * nat) =>
      (fst qv, snd (snd qv)))
      (elems qubit_reference (participant * nat) qm)) q))).
  {
    apply remove_fst_map_snd_NoDup.
    rewrite map_map. simpl.
    exact Hindices.
  }
  assert (Hindex_lt : index <
    length (elems qubit_reference (participant * nat) qm)).
  { exact (quantum_map_lookup_index_lt qm (conj Hindices Hbounds)
      q owner index Hlookup). }
  unfold quantum_map_wf, remove_and_reindex_qubit_map,
    reindex_quantum_map; simpl.
  split.
  - rewrite map_map. simpl.
    eapply NoDup_shifted_qubit_indices.
    + rewrite map_wire_indices_remove_fst.
      exact Hdeleted_indices.
    + exact Hnot.
  - rewrite Forall_forall.
    intros shifted_index Hin.
    apply in_map_iff in Hin.
    destruct Hin as [shifted_qv [Heq Hin_deleted]].
    apply in_map_iff in Hin_deleted.
    destruct Hin_deleted as [qv [Hshift Hin_source]].
    simpl in Hshift. subst shifted_qv.
    simpl in Heq. subst shifted_index.
    assert (Hin_deleted_source : In qv
      (elems qubit_reference (participant * nat) qm)).
    { unfold delete in Hin_source; simpl in Hin_source.
      eapply remove_fst_In; exact Hin_source. }
    assert (Hold_lt : snd (snd qv) <
      length (elems qubit_reference (participant * nat) qm)).
    {
      apply Forall_forall with (x := snd (snd qv)) in Hbounds.
      - exact Hbounds.
      - apply in_map_iff. exists qv. auto.
    }
    assert (Hold_neq : snd (snd qv) <> index).
    { apply Forall_forall with (x := qv) in Hnot; assumption. }
    unfold delete in Hlen; simpl in Hlen.
    rewrite map_length.
    destruct qv as [q' [owner' old_index]]. simpl in *.
    unfold shift_wire_index.
    destruct (index <? old_index) eqn:Hcmp.
    + apply Nat.ltb_lt in Hcmp.
      destruct old_index; simpl in *; lia.
    + apply Nat.ltb_ge in Hcmp.
      assert (old_index < index) by lia.
      lia.
Qed.

Lemma remove_and_reindex_qubit_map_length : forall
    (qm : finite_map qubit_reference (participant * nat)) q owner index,
  qm q = Some (owner, index) ->
  length (elems qubit_reference (participant * nat)
    (remove_and_reindex_qubit_map qm q index)) =
  Nat.pred (length (elems qubit_reference (participant * nat) qm)).
Proof.
  intros qm q owner index Hlookup.
  pose proof (delete_qubit_map_length qm q owner index Hlookup) as Hdeleted.
  unfold remove_and_reindex_qubit_map, reindex_quantum_map; simpl.
  rewrite map_length.
  unfold delete in Hdeleted; simpl in Hdeleted.
  lia.
Qed.

(* The measured wire is contracted with its observed basis bra.  This leaves
   the tensor factors before and after it in their original order. *)
Definition remove_measured_wire_operator (remaining_wires index : nat)
    (result : bool) :=
  (I (2 ^ index) ⊗ bra (if result then 1 else 0)) ⊗
    I (2 ^ (remaining_wires - index)).

Definition insert_measured_wire_operator (remaining_wires index : nat)
    (result : bool) :=
  (I (2 ^ index) ⊗ ket (if result then 1 else 0)) ⊗
    I (2 ^ (remaining_wires - index)).

Definition remove_measured_wire {remaining_wires index result}
    (Hindex : index <= remaining_wires)
    (v : state_vector (S remaining_wires))
    : state_vector remaining_wires :=
  @Mmult (2 ^ remaining_wires) (2 ^ (S remaining_wires)) 1
    (remove_measured_wire_operator remaining_wires index result) v.

Lemma pow_two_split : forall n i,
  i <= n -> 2 ^ i * 2 ^ (n - i) = 2 ^ n.
Proof.
  intros n i Hi.
  replace n with (i + (n - i)) at 2 by lia.
  rewrite Nat.pow_add_r.
  reflexivity.
Qed.

Lemma remove_measured_wire_operator_wf : forall n i b,
  i <= n ->
  @WF_Matrix (2 ^ n) (2 ^ (S n))
    (remove_measured_wire_operator n i b).
Proof.
  intros n i b Hi.
  unfold remove_measured_wire_operator.
  eapply WF_kron.
  - rewrite Nat.mul_1_r. symmetry. apply pow_two_split; exact Hi.
  - replace (2 ^ i * 2 * 2 ^ (n - i))
      with ((2 ^ i * 2 ^ (n - i)) * 2) by lia.
    rewrite pow_two_split by exact Hi.
    simpl. lia.
  - eapply WF_kron.
    + reflexivity.
    + reflexivity.
    + apply WF_I.
    + auto with wf_db.
  - apply WF_I.
Qed.

Lemma remove_measured_wire_wf : forall n i b
    (v : state_vector (S n)) (Hi : i <= n),
  @WF_Matrix (2 ^ (S n)) 1 v ->
  @WF_Matrix (2 ^ n) 1 (remove_measured_wire (result:=b) Hi v).
Proof.
  intros n i b v Hi Hv.
  unfold remove_measured_wire.
  apply WF_mult.
  - apply remove_measured_wire_operator_wf; exact Hi.
  - exact Hv.
Qed.

Lemma insert_measured_wire_operator_wf : forall n i b,
  i <= n ->
  @WF_Matrix (2 ^ (S n)) (2 ^ n)
    (insert_measured_wire_operator n i b).
Proof.
  intros n i b Hi.
  unfold insert_measured_wire_operator.
  eapply WF_kron.
  - replace (2 ^ i * 2 * 2 ^ (n - i))
      with ((2 ^ i * 2 ^ (n - i)) * 2) by lia.
    rewrite pow_two_split by exact Hi.
    simpl. lia.
  - rewrite Nat.mul_1_r. symmetry. apply pow_two_split; exact Hi.
  - eapply WF_kron.
    + reflexivity.
    + reflexivity.
    + apply WF_I.
    + auto with wf_db.
  - apply WF_I.
Qed.

Lemma Mmult_change_dims : forall m m' n n' p p'
    (A : Matrix m n) (B : Matrix n p),
  m = m' -> n = n' -> p = p' ->
  @Mmult m n p A B = @Mmult m' n' p' A B.
Proof.
  intros m m' n n' p p' A B Hm Hn Hp.
  subst; reflexivity.
Qed.

Lemma insert_remove_measured_wire_operator : forall n i b,
  i <= n ->
  @Mmult (2 ^ (S n)) (2 ^ n) (2 ^ (S n))
    (insert_measured_wire_operator n i b)
    (remove_measured_wire_operator n i b) = proj i (S n) b.
Proof.
  intros n i b Hi.
  assert (Hfull : (2 ^ i * 2) * 2 ^ (n - i) = 2 ^ (S n)).
  {
    replace ((2 ^ i * 2) * 2 ^ (n - i))
      with ((2 ^ i * 2 ^ (n - i)) * 2) by lia.
    rewrite pow_two_split by exact Hi.
    simpl. lia.
  }
  assert (Hcompact : (2 ^ i * 1) * 2 ^ (n - i) = 2 ^ n).
  { rewrite Nat.mul_1_r. apply pow_two_split; exact Hi. }
  rewrite (@Mmult_change_dims (2 ^ (S n))
    ((2 ^ i * 2) * 2 ^ (n - i)) (2 ^ n)
    ((2 ^ i * 1) * 2 ^ (n - i)) (2 ^ (S n))
    ((2 ^ i * 2) * 2 ^ (n - i))
    (insert_measured_wire_operator n i b)
    (remove_measured_wire_operator n i b)
    (eq_sym Hfull) (eq_sym Hcompact) (eq_sym Hfull)).
  unfold insert_measured_wire_operator, remove_measured_wire_operator,
    proj, pad_u, pad.
  rewrite (@kron_mixed_product
    (2 ^ i * 2) (2 ^ i * 1) (2 ^ i * 2)
    (2 ^ (n - i)) (2 ^ (n - i)) (2 ^ (n - i))
    (I (2 ^ i) ⊗ ket (if b then 1 else 0)) (I (2 ^ (n - i)))
    (I (2 ^ i) ⊗ bra (if b then 1 else 0)) (I (2 ^ (n - i)))).
  rewrite (@kron_mixed_product
    (2 ^ i) (2 ^ i) (2 ^ i) 2 1 2
    (I (2 ^ i)) (ket (if b then 1 else 0))
    (I (2 ^ i)) (bra (if b then 1 else 0))).
  rewrite Mmult_1_l by auto with wf_db.
  rewrite Mmult_1_l by auto with wf_db.
  destruct b; unfold bool_to_matrix;
    bdestruct (i + 1 <=? S n); try lia;
    replace (S n - (i + 1)) with (n - i) by lia;
    reflexivity.
Qed.

Lemma remove_insert_measured_wire_operator : forall n i b,
  i <= n ->
  @Mmult (2 ^ n) (2 ^ (S n)) (2 ^ n)
    (remove_measured_wire_operator n i b)
    (insert_measured_wire_operator n i b) = I (2 ^ n).
Proof.
  intros n i b Hi.
  assert (Hfull : (2 ^ i * 2) * 2 ^ (n - i) = 2 ^ (S n)).
  {
    replace ((2 ^ i * 2) * 2 ^ (n - i))
      with ((2 ^ i * 2 ^ (n - i)) * 2) by lia.
    rewrite pow_two_split by exact Hi.
    simpl. lia.
  }
  assert (Hcompact : (2 ^ i * 1) * 2 ^ (n - i) = 2 ^ n).
  { rewrite Nat.mul_1_r. apply pow_two_split; exact Hi. }
  rewrite (@Mmult_change_dims (2 ^ n) ((2 ^ i * 1) * 2 ^ (n - i))
    (2 ^ (S n)) ((2 ^ i * 2) * 2 ^ (n - i)) (2 ^ n)
    ((2 ^ i * 1) * 2 ^ (n - i))
    (remove_measured_wire_operator n i b)
    (insert_measured_wire_operator n i b)
    (eq_sym Hcompact) (eq_sym Hfull) (eq_sym Hcompact)).
  unfold remove_measured_wire_operator, insert_measured_wire_operator.
  rewrite (@kron_mixed_product
    (2 ^ i * 1) (2 ^ i * 2) (2 ^ i * 1)
    (2 ^ (n - i)) (2 ^ (n - i)) (2 ^ (n - i))
    (I (2 ^ i) ⊗ bra (if b then 1 else 0)) (I (2 ^ (n - i)))
    (I (2 ^ i) ⊗ ket (if b then 1 else 0)) (I (2 ^ (n - i)))).
  rewrite (@kron_mixed_product
    (2 ^ i) (2 ^ i) (2 ^ i) 1 2 1
    (I (2 ^ i)) (bra (if b then 1 else 0))
    (I (2 ^ i)) (ket (if b then 1 else 0))).
  rewrite Mmult_1_l by auto with wf_db.
  rewrite Mmult_1_l by auto with wf_db.
  destruct b; simpl.
  - rewrite bra1ket1, kron_1_r.
    rewrite Nat.mul_1_r.
    rewrite <- (pow_two_split n i Hi).
    apply id_kron.
  - rewrite bra0ket0, kron_1_r.
    rewrite Nat.mul_1_r.
    rewrite <- (pow_two_split n i Hi).
    apply id_kron.
Qed.

Lemma adjoint_insert_measured_wire_operator : forall n i b,
  adjoint (insert_measured_wire_operator n i b) =
    remove_measured_wire_operator n i b.
Proof.
  intros n i b.
  unfold insert_measured_wire_operator, remove_measured_wire_operator.
  rewrite !kron_adjoint, !id_adjoint_eq.
  destruct b; simpl; rewrite ?ket0_adjoint_bra0, ?ket1_adjoint_bra1;
    reflexivity.
Qed.

Lemma insert_measured_wire_operator_preserves_norm : forall n i b
    (v : state_vector n) (Hi : i <= n),
  @WF_Matrix (2 ^ n) 1 v ->
  @norm (2 ^ (S n))
      (@Mmult (2 ^ (S n)) (2 ^ n) 1
        (insert_measured_wire_operator n i b) v) =
    @norm (2 ^ n) v.
Proof.
  intros n i b v Hi Hv.
  unfold norm.
  rewrite (@inner_product_adjoint_l (2 ^ (S n)) (2 ^ n)
    (insert_measured_wire_operator n i b) v
    (@Mmult (2 ^ (S n)) (2 ^ n) 1
      (insert_measured_wire_operator n i b) v)).
  assert (Hadjoint : @adjoint (2 ^ (S n)) (2 ^ n)
      (insert_measured_wire_operator n i b) =
    remove_measured_wire_operator n i b).
  { exact (adjoint_insert_measured_wire_operator n i b). }
  rewrite Hadjoint.
  rewrite <- Mmult_assoc.
  rewrite remove_insert_measured_wire_operator by exact Hi.
  rewrite Mmult_1_l by exact Hv.
  reflexivity.
Qed.

Lemma remove_measured_wire_nonzero : forall n i b
    (v : state_vector (S n)) (Hi : i <= n),
  @Mmult (2 ^ (S n)) (2 ^ (S n)) 1 (proj i (S n) b) v = v ->
  v <> Zero ->
  remove_measured_wire (result:=b) Hi v <> Zero.
Proof.
  intros n i b v Hi Hproject Hnonzero Hremoved.
  apply Hnonzero.
  transitivity
    (@Mmult (2 ^ (S n)) (2 ^ n) 1
      (insert_measured_wire_operator n i b)
      (remove_measured_wire (result:=b) Hi v)).
  - unfold remove_measured_wire.
    rewrite <- (@Mmult_assoc (2 ^ (S n)) (2 ^ n) (2 ^ (S n)) 1
      (insert_measured_wire_operator n i b)
      (remove_measured_wire_operator n i b) v).
    rewrite insert_remove_measured_wire_operator by exact Hi.
    symmetry; exact Hproject.
  - rewrite Hremoved.
    apply (@Mmult_0_r (2 ^ (S n)) (2 ^ n) 1
      (insert_measured_wire_operator n i b)).
Qed.

Lemma nonzero_state_vector_wf : forall n
    (v : state_vector n),
  0 < n ->
  @WF_Matrix (2 ^ n) 1 v ->
  v <> Zero ->
  @norm (2 ^ n) v = 1%R ->
  state_vector_wf v.
Proof.
  intros n v Hn Hv Hnonzero Hnorm.
  unfold state_vector_wf.
  split; [exact Hv|].
  split; [left; lia|].
  intros i Hi.
  assert (Hexists : exists b, norm (proj i n b × v) <> 0%R).
  {
    apply (gen_contradiction
      (fun b => norm (proj i n b × v) = 0%R)).
    intros [Htrue Hfalse].
    assert (Htrue_wf : @WF_Matrix (2 ^ n) 1 (proj i n true × v)).
    { apply WF_mult; [apply WF_proj|exact Hv]. }
    assert (Hfalse_wf : @WF_Matrix (2 ^ n) 1 (proj i n false × v)).
    { apply WF_mult; [apply WF_proj|exact Hv]. }
    apply norm_zero_iff_zero in Htrue; [|exact Htrue_wf].
    apply norm_zero_iff_zero in Hfalse; [|exact Hfalse_wf].
    assert (Hsum : @Mplus (2 ^ n) 1
      (proj i n true × v) (proj i n false × v) = @Zero (2 ^ n) 1).
    { rewrite Htrue, Hfalse. apply Mplus_0_r. }
    rewrite <- (@Mmult_plus_distr_r (2 ^ n) (2 ^ n) 1
      (proj i n true) (proj i n false) v) in Hsum.
    rewrite proj_sum in Hsum by lia.
    rewrite (@Mmult_1_l (2 ^ n) 1 v) in Hsum by exact Hv.
    contradiction.
  }
  destruct Hexists as [b Hb].
  exists b.
  split; assumption.
Qed.

Definition transport_state_vector {n m : nat} (Hnm : n = m)
    (v : state_vector n) : state_vector m :=
  eq_rect n state_vector v m Hnm.

Lemma transport_state_vector_wf : forall n m (Hnm : n = m)
    (v : state_vector n),
  state_vector_wf v -> state_vector_wf (transport_state_vector Hnm v).
Proof.
  intros n m Hnm v Hwf.
  destruct Hnm.
  exact Hwf.
Qed.

Lemma transport_state_vector_norm : forall n m (Hnm : n = m)
    (v : state_vector n),
  @norm (2 ^ m) (transport_state_vector Hnm v) = @norm (2 ^ n) v.
Proof.
  intros n m Hnm v.
  destruct Hnm.
  reflexivity.
Qed.

Lemma transport_state_vector_proj : forall n m (Hnm : n = m)
    (i : nat) (b : bool) (v : state_vector n),
  transport_state_vector Hnm (proj i n b × v) =
    proj i m b × transport_state_vector Hnm v.
Proof.
  intros n m Hnm i b v.
  destruct Hnm.
  reflexivity.
Qed.

Lemma positive_norm_of_nonzero : forall n (v : state_vector n),
  @WF_Matrix (2 ^ n) 1 v -> v <> Zero -> (0 < @norm (2 ^ n) v)%R.
Proof.
  intros n v Hwf Hnonzero.
  assert (Hnorm_nonzero : @norm (2 ^ n) v <> 0%R).
  {
    intro Hnorm_zero.
    apply Hnonzero.
    apply (proj1 (@norm_zero_iff_zero (2 ^ n) v Hwf)).
    exact Hnorm_zero.
  }
  pose proof (@norm_ge_0 (2 ^ n) v).
  lra.
Qed.

Definition normalize_removed_wire {n : nat} (v : state_vector n)
    : state_vector n :=
  match n as n0 return state_vector n0 with
  | 0 => I 1
  | S n0 => (1 / @norm (2 ^ (S n0)) v)%R .* v
  end.

Lemma normalize_removed_wire_wf : forall n (v : state_vector n),
  @WF_Matrix (2 ^ n) 1 v -> v <> Zero ->
  state_vector_wf (normalize_removed_wire v).
Proof.
  intros n v Hv Hnonzero.
  destruct n as [|n].
  - unfold normalize_removed_wire, state_vector_wf; simpl.
    split; [apply WF_I|].
    split.
    + right; split; [reflexivity|].
      unfold I; simpl; reflexivity.
    + intros i Hi; lia.
  - unfold normalize_removed_wire.
    assert (Hnorm_positive : (0 < @norm (2 ^ (S n)) v)%R).
    { eapply positive_norm_of_nonzero; eauto. }
    apply nonzero_state_vector_wf.
    + lia.
    + apply WF_scale. exact Hv.
    + intro Hscaled.
      apply Hnonzero.
      apply (@Mscale_div (2 ^ (S n)) 1
        (RtoC ((1 / @norm (2 ^ (S n)) v)%R)) v Zero).
      * assert (Hnorm : (0 < @norm (2 ^ (S n)) v)%R).
        { eapply positive_norm_of_nonzero; eauto. }
        assert (Hscale : (0 < (1 / @norm (2 ^ (S n)) v)%R)%R).
        { apply Rdiv_pos_pos; lra. }
        intro Hzero.
        apply RtoC_inj in Hzero.
        lra.
      * rewrite Hscaled.
        rewrite Mscale_0_r.
        reflexivity.
    + rewrite norm_scale, Cmod_R, Rabs_pos_eq.
      * field; lra.
      * apply Rlt_le.
        apply Rdiv_pos_pos; [lra|exact Hnorm_positive].
Qed.

Definition measure_qubit_nonzero_at_dimension
    (remaining_wires : nat)
    (qm : finite_map qubit_reference (participant * nat))
    (HqmWF : quantum_map_wf qm)
    (Hdim : length (elems qubit_reference (participant * nat) qm) =
      S remaining_wires)
    (sv : state_vector (S remaining_wires))
    (HsvWf : state_vector_wf sv)
    (q : qubit_reference) (owner : participant) (index : nat)
    (result : bool)
    (Hlookup : qm q = Some (owner, index))
    (Hnonzero : norm (proj index (S remaining_wires) result × sv) <> 0%R)
    : {r : R | (r > 0)%R} * quantum_state.
Proof.
  set (qm' := remove_and_reindex_qubit_map qm q index).
  assert (HqmWF' : quantum_map_wf qm').
  { unfold qm'. eapply remove_and_reindex_qubit_map_wf; eauto. }
  assert (HqmLen : length (elems qubit_reference (participant * nat) qm') =
      remaining_wires).
  {
    unfold qm'.
    pose proof (remove_and_reindex_qubit_map_length qm q owner index Hlookup)
      as Hremoved_len.
    rewrite Hdim in Hremoved_len.
    simpl in Hremoved_len.
    exact Hremoved_len.
  }
  assert (Hindex : index <= remaining_wires).
  {
    assert (Hindex_lt : index < S remaining_wires).
    {
      rewrite <- Hdim.
      eapply quantum_map_lookup_index_lt; eauto.
    }
    lia.
  }
  set (projected :=
    (@Mmult (2 ^ (S remaining_wires)) (2 ^ (S remaining_wires)) 1
      (proj index (S remaining_wires) result) sv :
      state_vector (S remaining_wires))).
  assert (HprojectedWF :
      @WF_Matrix (2 ^ (S remaining_wires)) 1 projected).
  {
    unfold projected.
    apply WF_mult; [apply WF_proj|].
    exact (proj1 HsvWf).
  }
  assert (Hprojected_fixed :
      @Mmult (2 ^ (S remaining_wires)) (2 ^ (S remaining_wires)) 1
        (proj index (S remaining_wires) result) projected = projected).
  {
    unfold projected.
    rewrite <- (@Mmult_assoc (2 ^ (S remaining_wires))
      (2 ^ (S remaining_wires)) (2 ^ (S remaining_wires)) 1
      (proj index (S remaining_wires) result)
      (proj index (S remaining_wires) result) sv).
    rewrite proj_twice_eq.
    reflexivity.
  }
  assert (Hprojected_nonzero : projected <> Zero).
  {
    intro Hzero.
    apply Hnonzero.
    apply (proj2 (@norm_zero_iff_zero
      (2 ^ (S remaining_wires)) projected HprojectedWF)).
    exact Hzero.
  }
  assert (Hnorm_positive : (0 < @norm (2 ^ (S remaining_wires)) projected)%R).
  { eapply positive_norm_of_nonzero; eauto. }
  set (removed := remove_measured_wire (result := result) Hindex projected).
  assert (HremovedWF : @WF_Matrix (2 ^ remaining_wires) 1 removed).
  {
    unfold removed.
    apply remove_measured_wire_wf.
    exact HprojectedWF.
  }
  assert (Hremoved_nonzero : removed <> Zero).
  {
    unfold removed.
    eapply remove_measured_wire_nonzero; eauto.
  }
  set (post_state := normalize_removed_wire removed).
  assert (HpostStateWf : state_vector_wf post_state).
  {
    unfold post_state.
    eapply normalize_removed_wire_wf; eauto.
  }
  assert (Hprobability :
      (0 < (@norm (2 ^ (S remaining_wires)) projected ^ 2)%R)%R).
  {
    apply pow_lt.
    exact Hnorm_positive.
  }
  refine (exist _ ((@norm (2 ^ (S remaining_wires)) projected ^ 2)%R)
    Hprobability,
    existT _ (exist _ qm' HqmWF')
      (exist _ (transport_state_vector (eq_sym HqmLen) post_state) _)).
  eapply transport_state_vector_wf.
  exact HpostStateWf.
Defined.

Lemma measure_qubit_nonzero_at_dimension_map : forall
    remaining_wires qm HqmWF Hdim sv HsvWf q owner index result Hlookup
    Hnonzero,
  proj1_sig
    (projT1
      (snd
        (measure_qubit_nonzero_at_dimension remaining_wires qm HqmWF Hdim
          sv HsvWf q owner index result Hlookup Hnonzero))) =
    remove_and_reindex_qubit_map qm q index.
Proof.
  reflexivity.
Qed.

Definition measurement_probability_from_nonzero (n : nat)
    (sv : state_vector n) (index : nat) (result : bool)
    (Hnonzero : norm (proj index n result × sv) <> 0%R)
    : {r : R | (r > 0)%R}.
Proof.
  assert (Hnorm_positive : (0 < norm (proj index n result × sv))%R).
  {
    pose proof (@norm_ge_0 (2 ^ n) (proj index n result × sv)).
    lra.
  }
  refine (exist _ ((norm (proj index n result × sv) ^ 2)%R) _).
  apply pow_lt.
  exact Hnorm_positive.
Defined.

Lemma measurement_probability_from_nonzero_value : forall n
    (sv : state_vector n) index result Hnonzero,
  proj1_sig (measurement_probability_from_nonzero n sv index result Hnonzero) =
    (norm (proj index n result × sv) ^ 2)%R.
Proof.
  reflexivity.
Qed.

Definition measure_qubit_nonzero
    (qm : finite_map qubit_reference (participant * nat))
    (HqmWF : quantum_map_wf qm)
    (sv : state_vector (length (elems qubit_reference (participant * nat) qm)))
    (HsvWf : state_vector_wf sv)
    (q : qubit_reference) (owner : participant) (index : nat)
    (result : bool)
    (Hlookup : qm q = Some (owner, index))
    (Hlen : 0 < length (elems qubit_reference (participant * nat) qm))
    (Hnonzero : norm
      (proj index (length (elems qubit_reference (participant * nat) qm))
        result × sv) <> 0%R)
    : {r : R | (r > 0)%R} * quantum_state :=
  let len := length (elems qubit_reference (participant * nat) qm) in
  let remaining_wires := Nat.pred len in
  let Hdim := eq_sym (Nat.succ_pred_pos len Hlen) in
  let sv' := transport_state_vector Hdim sv in
  let HsvWf' := @transport_state_vector_wf len (S remaining_wires)
    Hdim sv HsvWf in
  let HprojectedNorm :=
    eq_trans
      (eq_sym (f_equal norm
        (@transport_state_vector_proj len (S remaining_wires)
          Hdim index result sv)))
      (@transport_state_vector_norm len (S remaining_wires) Hdim
        (proj index len result × sv)) in
  let Hnonzero' := fun Hzero =>
    Hnonzero (eq_trans (eq_sym HprojectedNorm) Hzero) in
  (measurement_probability_from_nonzero len sv index result Hnonzero,
   snd (measure_qubit_nonzero_at_dimension remaining_wires qm HqmWF Hdim
     sv' HsvWf' q owner index result Hlookup Hnonzero')).

Lemma measure_qubit_nonzero_map : forall
    qm HqmWF sv HsvWf q owner index result Hlookup Hlen Hnonzero,
  proj1_sig
    (projT1
      (snd
        (measure_qubit_nonzero qm HqmWF sv HsvWf q owner index result
          Hlookup Hlen Hnonzero))) =
  remove_and_reindex_qubit_map qm q index.
Proof.
  reflexivity.
Qed.

(* Compatibility alias for code using the previous helper name. *)
Definition measure_qubit_from_nonzero := measure_qubit_nonzero.

Definition measure_qubit
    (qm : finite_map qubit_reference (participant * nat))
    (HqmWF : quantum_map_wf qm)
    (sv : state_vector (length (elems qubit_reference (participant * nat) qm)))
    (HsvWf : state_vector_wf sv)
    (q : qubit_reference) (owner : participant) (index : nat)
    (result : bool)
    (Hlookup : qm q = Some (owner, index))
    : option ({r : R | (r > 0)%R} * quantum_state).
Proof.
  set (len := length (elems qubit_reference (participant * nat) qm)).
  set (projected :=
    (@Mmult (2 ^ len) (2 ^ len) 1 (proj index len result) sv :
      state_vector len)).
  destruct (lt_dec 0 len) as [Hlen|Hempty].
  - destruct (Rle_lt_dec (@norm (2 ^ len) projected) 0)
      as [Hzero|Hpositive].
    + exact None.
    + assert (Hnonzero : @norm (2 ^ len) projected <> 0%R) by lra.
      exact (Some (measure_qubit_nonzero qm HqmWF sv HsvWf q owner index
        result Hlookup Hlen Hnonzero)).
  - exact None.
Defined.

Inductive value :=
| Nat (n: nat)
| Bool (b: bool)
| QVal (q: qubit_reference).

Inductive operation := 
| Plus | Minus | Leq | Not | And | Or | Beq.

Definition eval_op (o: operation) (args: list value) : option value:=
match o with
| Plus =>
    match args with
    | Nat n:: Nat m::nil => Some (Nat (n+m))
    | _ => None
    end
| Minus =>
    match args with
    | Nat n:: Nat m::nil => Some (Nat (n-m))
    | _ => None
    end
| Leq =>
    match args with
    | Nat n:: Nat m::nil => Some (Bool (n <=? m))
    | _ => None
    end
| Not =>
    match args with
    | Bool b::nil => Some (Bool (negb b))
    | _ => None
    end
| And =>
    match args with
    | Bool b:: Bool b'::nil => Some (Bool (andb b b'))
    | _ => None
    end
| Or =>
    match args with
    | Bool b:: Bool b'::nil => Some (Bool (orb b b'))
    | _ => None
    end
| Beq =>
    match args with
    | Bool b:: Bool b'::nil => Some (Bool (Bool.eqb b b'))
    | _ => None
    end
end.
