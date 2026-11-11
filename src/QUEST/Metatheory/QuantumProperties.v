From SQIR Require Import SQIR UnitaryOps.
Require Import Coq.Program.Equality.
Require Import Lia Permutation Reals List.
Require Import SST QUEST session.
Require Import substitution.
Require Export QuantumPropertiesCore.
Require Import SubjectReduction.
Require Import Progress.

Lemma transfer_qubit_from_lookup_preserves_keys : forall
    (qm : finite_map qubit_reference (participant * nat))
    (HqmWf : quantum_map_wf qm)
    (sv : state_vector (Datatypes.length (elems qubit_reference (participant * nat) qm)))
    (HsvWf : state_vector_wf sv) (new : participant) (q : qubit_reference)
    (old : participant) (n : nat) (Hlookup : qm q = Some (old, n)) q',
  proj1_sig (projT1
    (transfer_qubit_from_lookup qm HqmWf sv HsvWf new q old n Hlookup)) q' <> None
  <-> qm q' <> None.
Proof.
  intros qm HqmWf sv HsvWf new q old n Hlookup q'.
  unfold transfer_qubit_from_lookup.
  cbn [proj1_sig projT1].
  destruct (qr_dec q q') as [Heq|Hneq].
  - subst q'. rewrite insert_eq, Hlookup. simpl.
    split; intros _; discriminate.
  - rewrite insert_neq by exact Hneq. tauto.
Qed.

Theorem state_only_contains_qubits_in_context_after_step `{good_merge}:
forall M M' qstate qstate' a pi,
step (qstate, M) a (qstate', M') pi ->
(forall p P, M p = Some P -> cguardedP P) ->
forall delta delta' G G' context context',
typecheck_session context M delta G ->
state_only_contains_qubits_in_context context qstate ->
typecheck_session context' M' delta' G' ->
state_only_contains_qubits_in_context context' qstate'.
Proof.
  intros M M' qstate qstate' a pi Hstep Hguard
    delta delta' G G' context context' Htyped Hstate Htyped'.
  destruct a as [p|p q l v].
    destruct (subject_reduction_via_association_1
      M M' pi qstate qstate' delta p context G Hstep Htyped Hstate)
      as [context2 [Htyped2 Hstate2]].
    assert (Hcontexts : forall q0,
      context' q0 = Some tt <-> context2 q0 = Some tt).
    {
      intro q0.
      pose proof (typecheck_session_qubit_use_exact M' delta' G'
        context' Htyped' q0) as Hfinal.
      pose proof (typecheck_session_qubit_use_exact M' delta G
        context2 Htyped2 q0) as Hsr.
      split; intro Hctx.
      - apply (proj1 Hsr). apply (proj2 Hfinal). exact Hctx.
      - apply (proj1 Hfinal). apply (proj2 Hsr). exact Hctx.
    }
    unfold state_only_contains_qubits_in_context in *.
    intros q0; split; intro Hctx.
    + apply (proj1 (Hstate2 q0)).
      apply (proj1 (Hcontexts q0)); exact Hctx.
    + apply (proj2 (Hcontexts q0)).
      apply (proj2 (Hstate2 q0)); exact Hctx.
  - destruct (subject_reduction_via_association_2
      M M' pi qstate qstate' delta G p q l v context Hstep Htyped)
      as [context2 [delta2 [G2 [e [S
        [HstateRel [Hincluded [Hctxstep [Hgstep [Heval [Hexpr Htyped2]]]]]]]]]]].
    assert (Hmap : forall q0,
      (proj1_sig (projT1 qstate')) q0 <> None <->
      (proj1_sig (projT1 qstate)) q0 <> None).
    {
      destruct v as [n0|b0|vq].
      - simpl in HstateRel. destruct HstateRel.
        intro q0; tauto.
      - simpl in HstateRel. destruct HstateRel.
        intro q0; tauto.
      - simpl in HstateRel.
        destruct HstateRel as [old [n0 [Hlookup Heq]]].
        subst qstate'.
        intro q0.
        apply transfer_qubit_from_lookup_preserves_keys.
    }
    assert (Hcontexts : forall q0,
      context' q0 = Some tt <-> context q0 = Some tt).
    {
      intro q0.
      pose proof (typecheck_session_qubit_use_exact M' delta' G'
        context' Htyped' q0) as Hfinal.
      pose proof (typecheck_session_qubit_use_exact M' delta2 G2
        context Htyped2 q0) as Hsr.
      split; intro Hctx.
      - apply (proj1 Hsr). apply (proj2 Hfinal). exact Hctx.
      - apply (proj1 Hfinal). apply (proj2 Hsr). exact Hctx.
    }
    unfold state_only_contains_qubits_in_context in *.
    intros q0; split; intro Hctx.
    + apply (proj2 (Hmap q0)).
      apply (proj1 (Hstate q0)).
      apply (proj1 (Hcontexts q0)); exact Hctx.
    + apply (proj2 (Hcontexts q0)).
      apply (proj2 (Hstate q0)).
      apply (proj1 (Hmap q0)); exact Hctx.
Qed.

Theorem unique_ownership `{good_merge} :
forall M delta G context p q P Q,
typecheck_session context M delta G ->
M p = Some P ->
M q = Some Q ->
p <> q ->
guardP nil P ->
guardP nil Q ->
(forall e, In e (free_qubits P) -> ~In e (free_qubits Q)) /\ 
(forall e, In e (free_qubits Q) -> ~In e (free_qubits P)).
Proof.
  intros M delta G context p q P Q Htyped HP HQ Hneq HguardP HguardQ.
  unfold typecheck_session in Htyped.
  destruct Htyped as [lqc [_ [_ [_ [Hpartition
    [Hlength [Hperm Hcomponents]]]]]]].
  unfold session_participants in Hperm.
  assert (HpSession : In p (map fst (elems participant process M))).
  {
    apply in_map_iff.
    exists (p, P); split; [reflexivity|].
    apply (proj2 ((proj2 (specs _ _ M)) p P)); exact HP.
  }
  assert (HqSession : In q (map fst (elems participant process M))).
  {
    apply in_map_iff.
    exists (q, Q); split; [reflexivity|].
    apply (proj2 ((proj2 (specs _ _ M)) q Q)); exact HQ.
  }
  assert (HpDelta : In p (map fst (elems participant ltt delta))).
  { eapply Permutation_in; [apply Permutation_sym; exact Hperm|exact HpSession]. }
  assert (HqDelta : In q (map fst (elems participant ltt delta))).
  { eapply Permutation_in; [apply Permutation_sym; exact Hperm|exact HqSession]. }
  apply in_map_iff in HpDelta as [[p' Tp] [Hp' HinDeltaP]].
  apply in_map_iff in HqDelta as [[q' Tq] [Hq' HinDeltaQ]].
  simpl in Hp', Hq'; subst p' q'.
  assert (HlengthLe : length (elems participant ltt delta) <= length lqc).
  { rewrite <- Hlength; lia. }
  destruct (in_combine_ex_r (elems participant ltt delta) lqc HlengthLe
      (p, Tp) HinDeltaP) as [qcP HtripleP].
  destruct (in_combine_ex_r (elems participant ltt delta) lqc HlengthLe
      (q, Tq) HinDeltaQ) as [qcQ HtripleQ].
  destruct (Hcomponents p Tp qcP HtripleP) as [P' [HP' HtypedP]].
  destruct (Hcomponents q Tq qcQ HtripleQ) as [Q' [HQ' HtypedQ]].
  rewrite HP in HP'; inversion HP'; subst P'.
  rewrite HQ in HQ'; inversion HQ'; subst Q'.
  pose proof (typecheck_process_free_qubits P (nil, nil, qcP) Tp
    HtypedP) as HfreeP.
  pose proof (typecheck_process_free_qubits Q (nil, nil, qcQ) Tq
    HtypedQ) as HfreeQ.
  apply In_iff_nth_error in HtripleP as [np HcombinedP].
  apply In_iff_nth_error in HtripleQ as [nq HcombinedQ].
  apply nth_error_combine in HcombinedP as [HdeltaP HqcP].
  apply nth_error_combine in HcombinedQ as [HdeltaQ HqcQ].
  assert (Hindices : np <> nq).
  {
    eapply nth_error_NoDup_l_neq; [exact HdeltaP|exact HdeltaQ|apply specs|].
    intro Heq; inversion Heq; subst; contradiction.
  }
  unfold FMap.partition in Hpartition.
  destruct Hpartition as [_ Hdisjoint].
  unfold not; split; intros e HeP HeQ.
  - pose proof (HfreeP e HeP) as HlocalP.
    pose proof (HfreeQ e HeQ) as HlocalQ.
    unfold in_qubit_context in HlocalP, HlocalQ; simpl in HlocalP, HlocalQ.
    destruct (Hdisjoint np nq qcP qcQ Hindices HqcP HqcQ e)
      as [HdisjointPQ HdisjointQP].
    assert (HpresentP : qcP e <> None) by congruence.
    pose proof (HdisjointPQ HpresentP) as HabsentQ.
    rewrite HlocalQ in HabsentQ; discriminate.
  - pose proof (HfreeQ e HeP) as HlocalQ.
    pose proof (HfreeP e HeQ) as HlocalP.
    unfold in_qubit_context in HlocalP, HlocalQ; simpl in HlocalP, HlocalQ.
    destruct (Hdisjoint np nq qcP qcQ Hindices HqcP HqcQ e)
      as [HdisjointPQ HdisjointQP].
    assert (HpresentQ : qcQ e <> None) by congruence.
    pose proof (HdisjointQP HpresentQ) as HabsentP.
    rewrite HlocalP in HabsentP; discriminate.
Qed.

Lemma typecheck_process_qubit_use_exact:
forall P context T,
typecheck_process context P T ->
forall q, In q (free_qubits P) <-> context.2 q = Some tt.
Proof.
  intros P context T Htyped q.
  split.
  - intro Hin.
    eapply typecheck_process_free_qubits; eauto.
  - intro Hctx.
    eapply typecheck_process_qubit_use_linear; eauto.
Qed.

Lemma free_qubits_session_equivalent:
forall M M', equivalent M M' ->
Permutation (free_qubits_session M) (free_qubits_session M').
Proof.
  intros M M' Hequiv.
  unfold free_qubits_session.
  pose proof (equivalent_Permutation _ _ _ _ Hequiv) as Hperm.
  apply Permutation_flat_map.
  apply Permutation_map.
  exact Hperm.
Qed.

Lemma free_qubits_session_update:
forall (M : session) (p : participant) (P : process) (q : qubit_reference),
M p = Some P ->
(In q (free_qubits_session M) <->
 In q (free_qubits P) \/ In q (free_qubits_session (delete M p))).
Proof.
  intros M p P q Hlookup.
  assert (Hequiv : equivalent M (insert M p P)).
  {
    unfold equivalent, included; split.
    - intros k v Hmap.
      destruct (participant_dec k p) as [->|Hneq].
      + rewrite insert_eq; rewrite Hlookup in Hmap; inversion Hmap; reflexivity.
      + rewrite insert_neq by congruence.
        exact Hmap.
    - intros k v Hmap.
      destruct (participant_dec k p) as [->|Hneq].
      + rewrite insert_eq in Hmap; rewrite Hlookup; inversion Hmap; reflexivity.
      + rewrite insert_neq in Hmap by congruence.
        exact Hmap.
  }
  pose proof (free_qubits_session_equivalent M
    (insert M p P) Hequiv) as Hperm.
  pose proof (free_qubits_insert_in M p P) as HpermInsert.
  assert (Hmem: In q (free_qubits_session M) <->
    In q (free_qubits P) \/ In q (free_qubits_session (delete M p))).
  {
    transitivity (In q (free_qubits_session (insert M p P))).
    - split; intro Hin.
      + eapply Permutation_in; [exact Hperm|exact Hin].
      + eapply Permutation_in; [apply Permutation_sym; exact Hperm|exact Hin].
    - split; intro Hin.
      + pose proof (Permutation_in _ HpermInsert Hin) as Hconcat.
        rewrite in_app_iff in Hconcat; exact Hconcat.
      + assert (Hconcat : In q
          (free_qubits P ++ free_qubits_session (delete M p))).
        { apply in_app_iff; exact Hin. }
        eapply Permutation_in; [apply Permutation_sym; exact HpermInsert|exact Hconcat].
  }
  exact Hmem.
Qed.

Lemma free_qubits_session_insert_update:
forall (M : session) (p : participant) (P : process) (q : qubit_reference),
In q (free_qubits_session (insert M p P)) <->
In q (free_qubits P) \/ In q (free_qubits_session (delete M p)).
Proof.
  intros M p P q.
  pose proof (free_qubits_insert_in M p P) as Hperm.
  split; intro Hin.
  - pose proof (Permutation_in _ Hperm Hin) as Hconcat.
    apply in_app_iff in Hconcat; exact Hconcat.
  - assert (Hconcat : In q (free_qubits P ++ free_qubits_session (delete M p))).
    { apply in_app_iff; exact Hin. }
    eapply Permutation_in; [apply Permutation_sym; exact Hperm|exact Hconcat].
Qed.

Lemma free_qubits_session_update_same:
forall (M : session) (p : participant) (P P' : process),
M p = Some P ->
(forall q, In q (free_qubits P) <-> In q (free_qubits P')) ->
forall q,
In q (free_qubits_session M) <->
In q (free_qubits_session (insert M p P')).
Proof.
  intros M p P P' Hlookup Hsame q.
  rewrite free_qubits_session_update by exact Hlookup.
  rewrite free_qubits_session_insert_update.
  rewrite Hsame; tauto.
Qed.

Lemma free_qubits_session_update_add:
forall (M : session) (p : participant) (P P' : process) qnew,
M p = Some P ->
(forall q, In q (free_qubits P') <-> In q (free_qubits P) \/ q = qnew) ->
forall q,
In q (free_qubits_session (insert M p P')) <->
In q (free_qubits_session M) \/ q = qnew.
Proof.
  intros M p P P' qnew Hlookup Hproc q.
  pose proof (free_qubits_session_update M p P q Hlookup) as Hsrc.
  rewrite free_qubits_session_insert_update.
  rewrite Hproc, Hsrc; tauto.
Qed.

Lemma free_qubits_session_update_remove:
forall (M : session) (p : participant) (P P' : process) qremove,
M p = Some P ->
(forall q, In q (free_qubits P') <-> In q (free_qubits P) /\ q <> qremove) ->
(~ In qremove (free_qubits_session (delete M p))) ->
forall q,
In q (free_qubits_session (insert M p P')) <->
In q (free_qubits_session M) /\ q <> qremove.
Proof.
  intros M p P P' qremove Hlookup Hproc Hother q.
  pose proof (free_qubits_session_update M p P q Hlookup) as Hsrc.
  rewrite free_qubits_session_insert_update.
  rewrite Hproc, Hsrc.
  split.
  - intros [Hlocal|HotherQ].
    + destruct Hlocal as [Hold Hneq].
      split; [left; exact Hold|exact Hneq].
    + split; [right; exact HotherQ|].
      intro Heq; subst q; apply Hother; exact HotherQ.
  - intros [[Hlocal|HotherQ] Hneq].
    + left; split; [exact Hlocal|exact Hneq].
    + right; exact HotherQ.
Qed.

Lemma list_diff_ext_right:
forall l1 l2 l2',
(forall q, In q l2 <-> In q l2') ->
list_diff qr_dec l1 l2 = list_diff qr_dec l1 l2'.
Proof.
  intros l1 l2 l2' Hsame.
  unfold list_diff.
  induction l1 as [|q l1 IH]; simpl; [reflexivity|].
  assert (Hinb: inb (E:=qr_dec) l2 q =
    inb (E:=qr_dec) l2' q).
  {
    destruct (inb l2 q) eqn:Hleft,
      (inb l2' q) eqn:Hright;
      try reflexivity.
    - exfalso. apply inb_spec in Hleft.
      apply inb_false in Hright. apply Hright.
      apply (proj1 (Hsame q)); exact Hleft.
    - exfalso. apply inb_spec in Hright.
      apply inb_false in Hleft. apply Hleft.
      apply (proj2 (Hsame q)); exact Hright.
  }
  rewrite Hinb.
  destruct (inb l2' q); simpl; [exact IH|].
  now f_equal.
Qed.

Lemma free_qubits_recv_member:
forall lP P q,
In P (to_list lP) ->
In q (free_qubits P) ->
In q (flat_map (fun x => x)
  (to_list (smap free_qubits lP))).
Proof.
  intros lP P q HinP Hq.
  apply In_to_list_onth in HinP as [i Hnth].
  apply in_concat.
  exists (free_qubits P); split.
  - eapply onth_to_list_In.
    eapply onth_move_in; eauto.
  - exact Hq.
Qed.

Lemma free_qubits_substitutionP_preserves:
forall P P' x m n q,
(forall r, In r (free_qubits P) -> In r (free_qubits P')) ->
In q (free_qubits P) ->
In q (free_qubits (substitutionP x m n P' P)).
Proof.
  eapply (process_deep_ind
    (fun P => forall P' x m n q,
      (forall r, In r (free_qubits P) -> In r (free_qubits P')) ->
      In q (free_qubits P) ->
      In q (free_qubits (substitutionP x m n P' P)))).
  - intros X lz P' x m n q Hcover Hin.
    simpl in Hin |- *.
    destruct (Nat.ltb X x); simpl; [exact Hin|].
    destruct (Nat.eqb X x); simpl; [|exact Hin].
    apply (proj1 (free_qubits_incr_free P' 0 0 n m q)).
    apply Hcover; exact Hin.
  - intros lz P' x m n q Hcover Hin.
    simpl in Hin |- *; exact Hin.
  - intros pt l e P0 IH P' x m n q Hcover Hin.
    simpl in Hin |- *.
    apply in_app_iff in Hin as [He|HP].
    + apply in_app_iff; left; exact He.
    + apply in_app_iff; right.
      eapply IH; [|exact HP].
      intros r Hr; apply Hcover.
      simpl; apply in_app_iff; right; exact Hr.
  - intros pt lP IHs P' x m n q Hcover Hin.
    simpl in Hin |- *.
    destruct (free_qubits_recv_In lP q Hin) as [P0 [HinP HqP]].
    assert (Hcover0: forall r, In r (free_qubits P0) -> In r (free_qubits P')).
    {
      intros r Hr; apply Hcover.
      simpl; eapply free_qubits_recv_member; eauto.
    }
    apply In_to_list_onth in HinP as [i Hnth].
    pose proof (proj2 (SForall_forall process _ lP) IHs) as Hforall.
    specialize (Hforall i P0 Hnth P' x m (S n) q Hcover0 HqP) as HqSub.
    apply in_concat.
    exists (free_qubits (substitutionP x m (S n) P' P0)); split.
    + eapply onth_to_list_In.
      eapply onth_move_in.
      eapply onth_move_in; eauto.
    + exact HqSub.
  - intros e P1 P0 IH1 IH0 P' x m n q Hcover Hin.
    simpl in Hin |- *; repeat rewrite in_app_iff in *.
    destruct Hin as [He|[HP1|HP0]].
    + left; exact He.
    + right; left.
      eapply IH1; [|exact HP1].
      intros r Hr; apply Hcover.
      simpl; repeat rewrite in_app_iff; auto.
    + right; right.
      eapply IH0; [|exact HP0].
      intros r Hr; apply Hcover.
      simpl; repeat rewrite in_app_iff; auto.
  - intros P0 IH P' x m n q Hcover Hin.
    simpl in Hin |- *.
    eapply IH with (x := S x) (m := S m) (n := n); [|exact Hin].
    intros r Hr; apply Hcover; exact Hr.
  - intros P0 IH P' x m n q Hcover Hin.
    simpl in Hin |- *.
    eapply IH; [|exact Hin].
    intros r Hr; apply Hcover; exact Hr.
  - intros dim U lz P0 IH P' x m n q Hcover Hin.
    simpl in Hin |- *; apply in_app_iff in Hin as [Hlz|HP].
    + apply in_app_iff; left; exact Hlz.
    + apply in_app_iff; right.
      eapply IH; [|exact HP].
      intros r Hr; apply Hcover.
      simpl; apply in_app_iff; right; exact Hr.
  - intros z P0 IH P' x m n q Hcover Hin.
    simpl in Hin |- *; apply in_app_iff in Hin as [Hz|HP].
    + apply in_app_iff; left; exact Hz.
    + apply in_app_iff; right.
      eapply IH; [|exact HP].
      intros r Hr; apply Hcover.
      simpl; apply in_app_iff; right; exact Hr.
Qed.

Lemma free_qubits_precong_equiv:
forall P P', precongP P P' ->
forall q, In q (free_qubits P) <-> In q (free_qubits P').
Proof.
  intros P P' Hpre.
  induction Hpre; intro q.
  - tauto.
  - simpl.
    split.
    + intro Hin.
      apply IHHpre.
      eapply free_qubits_substitutionP_preserves with
        (P' := p_rec P) (x := 0) (m := 0) (n := 0).
      * intros r Hr; simpl; exact Hr.
      * exact Hin.
    + intro Hin.
      apply IHHpre in Hin.
      eapply free_qubits_substitutionP_rec; eauto.
  - specialize (IHHpre1 q); specialize (IHHpre2 q).
    tauto.
Qed.

Lemma free_qubits_session_unfoldM_equiv:
forall M M', unfoldM M M' ->
forall q, In q (free_qubits_session M) <-> In q (free_qubits_session M').
Proof.
  intros M M' Hunfold q.
  rewrite free_qubits_session_in_one.
  rewrite free_qubits_session_in_one.
  split; intros [p [P [Hin Hq]]].
  - pose proof (proj1 ((proj2 (specs _ _ M)) p P) Hin) as Hlookup.
    destruct (Hunfold p) as [[Hnone _]|[P0 [P1 [Hsrc [Hdst Hpre]]]]].
    + rewrite Hlookup in Hnone; discriminate.
    + rewrite Hlookup in Hsrc; inversion Hsrc; subst P0.
      exists p, P1; split.
      + apply (proj2 ((proj2 (specs _ _ M')) p P1)); exact Hdst.
      +
      apply (proj1 (free_qubits_precong_equiv P P1 Hpre q)); exact Hq.
  - pose proof (proj1 ((proj2 (specs _ _ M')) p P) Hin) as Hlookup.
    destruct (Hunfold p) as [[_ Hnone]|[P0 [P1 [Hsrc [Hdst Hpre]]]]].
    + rewrite Hlookup in Hnone; discriminate.
    + rewrite Hlookup in Hdst; inversion Hdst; subst P1.
      exists p, P0; split.
      + apply (proj2 ((proj2 (specs _ _ M)) p P0)); exact Hsrc.
      +
      apply (proj2 (free_qubits_precong_equiv P0 P Hpre q)); exact Hq.
Qed.

Lemma get_qubits_expression_substitution_local:
forall e0 n d replacement q,
In q (get_qubits_expression (subst_expression n d replacement e0)) ->
In q (get_qubits_expression e0) \/
In q (get_qubits_expression replacement).
Proof.
  intros e0.
  eapply (expression_deep_ind
    (fun e0 => forall n d replacement q,
      In q (get_qubits_expression (subst_expression n d replacement e0)) ->
      In q (get_qubits_expression e0) \/
      In q (get_qubits_expression replacement))).
  - intros v n d replacement q Hin.
    destruct v; simpl in *; try contradiction; left; exact Hin.
  - intros x n d replacement q Hin.
    unfold subst_expression in Hin; simpl in Hin.
    destruct (Nat.ltb x n) eqn:Hlt.
    + simpl in Hin; contradiction.
    + destruct (Nat.eqb x n) eqn:Heq.
      * right.
        apply (proj2 (free_qubits_incr_free_expression replacement 0 d q)).
        exact Hin.
      * simpl in Hin; contradiction.
  - intros op args IHs n d replacement q Hin.
    simpl in Hin.
    apply in_flat_map in Hin as [e [HinMap Hq]].
    apply in_map_iff in HinMap as [eOrig [Heq HinArgs]].
    rewrite Forall_forall in IHs.
    rewrite <- Heq in Hq.
    specialize (IHs eOrig HinArgs n d replacement q Hq).
    destruct IHs as [Hold|Hnew].
    + left; apply in_flat_map; exists eOrig; split; assumption.
    + right; exact Hnew.
Qed.

Lemma get_qubits_list_substitution_local:
forall l n d replacement q,
In q (get_qubits (map (subst_expression n d replacement) l)) ->
In q (get_qubits l) \/ In q (get_qubits_expression replacement).
Proof.
  intros l n d replacement q Hin.
  apply get_qubits_In in Hin as [e' [HinMap Hq]].
  apply in_map_iff in HinMap as [e [Heq HinOld]].
  rewrite <- Heq in Hq.
  destruct (get_qubits_expression_substitution_local e n d replacement q Hq)
    as [Hold|Hnew].
  - left; apply get_qubits_In; exists e; split; assumption.
  - right; exact Hnew.
Qed.

Lemma free_qubits_process_substitution_local:
forall P n d replacement q,
In q (free_qubits (subst_expression_in_process n d replacement P)) ->
In q (free_qubits P) \/ In q (get_qubits_expression replacement).
Proof.
  eapply (process_deep_ind
    (fun P => forall n d replacement q,
      In q (free_qubits (subst_expression_in_process n d replacement P)) ->
      In q (free_qubits P) \/ In q (get_qubits_expression replacement))).
  - intros x lz n d replacement q Hin; simpl in Hin.
    exact (get_qubits_list_substitution_local lz n d replacement q Hin).
  - intros lz n d replacement q Hin; simpl in Hin.
    exact (get_qubits_list_substitution_local lz n d replacement q Hin).
  - intros pt l e P0 IH n d replacement q Hin.
    simpl in Hin; apply in_app_iff in Hin as [He|HP].
    + destruct (get_qubits_list_substitution_local (e :: nil) n d replacement q He)
        as [Hold|Hnew].
      * left; apply in_app_iff; left; exact Hold.
      * right; exact Hnew.
    + destruct (IH n d replacement q HP) as [Hold|Hnew].
      * left; apply in_app_iff; right; exact Hold.
      * right; exact Hnew.
  - intros pt lP IHs n d replacement q Hin.
    simpl in Hin.
    destruct (free_qubits_recv_In
      (smap (subst_expression_in_process (S n) (S d) replacement) lP) q Hin)
      as [Psub [HinSub HqSub]].
    apply In_to_list_onth in HinSub as [idx HnthSub].
    destruct (onth_move_out idx (subst_expression_in_process (S n) (S d) replacement)
      lP Psub HnthSub) as [P0 [Hnth Hsubst]].
    rewrite <- Hsubst in HqSub.
    pose proof (proj2 (SForall_forall process _ lP) IHs) as Hforall.
    specialize (Hforall idx P0 Hnth (S n) (S d) replacement q HqSub).
    destruct Hforall as [Hold|Hnew].
    + left.
      apply in_concat.
      exists (free_qubits P0); split.
      * exact (onth_to_list_In (list qubit_reference)
          (smap free_qubits lP) idx (free_qubits P0)
          (onth_move_in process (list qubit_reference) free_qubits
            lP idx P0 Hnth)).
      * exact Hold.
    + right; exact Hnew.
  - intros e P1 P0 IH1 IH0 n d replacement q Hin.
    simpl in Hin; repeat rewrite in_app_iff in Hin.
    destruct Hin as [He|[HP1|HP0]].
    + destruct He as [He|Hnil]; [|contradiction].
      destruct (get_qubits_expression_substitution_local e n d replacement q He)
        as [Hold|Hnew].
      * left; simpl; repeat rewrite in_app_iff; auto.
      * right; exact Hnew.
    + destruct (IH1 n d replacement q HP1) as [Hold|Hnew].
      * left; simpl; repeat rewrite in_app_iff; auto.
      * right; exact Hnew.
    + destruct (IH0 n d replacement q HP0) as [Hold|Hnew].
      * left; simpl; repeat rewrite in_app_iff; auto.
      * right; exact Hnew.
  - intros P0 IH n d replacement q Hin.
    simpl in Hin; destruct (IH n d replacement q Hin) as [Hold|Hnew];
      [left|right]; assumption.
  - intros P0 IH n d replacement q Hin.
    simpl in Hin; destruct (IH (S n) (S d) replacement q Hin)
      as [Hold|Hnew]; [left|right]; assumption.
  - intros dim U lz P0 IH n d replacement q Hin.
    simpl in Hin; apply in_app_iff in Hin as [Hlz|HP].
    + destruct (get_qubits_list_substitution_local lz n d replacement q Hlz)
        as [Hold|Hnew].
      * left; simpl; apply in_app_iff; left; exact Hold.
      * right; exact Hnew.
    + destruct (IH n d replacement q HP) as [Hold|Hnew].
      * left; simpl; apply in_app_iff; right; exact Hold.
      * right; exact Hnew.
  - intros z P0 IH n d replacement q Hin.
    simpl in Hin; apply in_app_iff in Hin as [Hz|HP].
    + destruct (get_qubits_list_substitution_local (z :: nil) n d replacement q Hz)
        as [Hold|Hnew].
      * left; simpl; apply in_app_iff; left; exact Hold.
      * right; exact Hnew.
    + destruct (IH (S n) (S d) replacement q HP) as [Hold|Hnew].
      * left; simpl; apply in_app_iff; right; exact Hold.
      * right; exact Hnew.
Qed.

Lemma get_qubits_expression_substitution_preserves_local:
forall e0 n d replacement q,
In q (get_qubits_expression e0) ->
In q (get_qubits_expression (subst_expression n d replacement e0)).
Proof.
  intros e0.
  eapply (expression_deep_ind
    (fun e0 => forall n d replacement q,
      In q (get_qubits_expression e0) ->
      In q (get_qubits_expression (subst_expression n d replacement e0)))).
  - intros v n d replacement q Hin.
    destruct v; simpl in *; try contradiction; exact Hin.
  - intros x n d replacement q Hin; simpl in Hin; contradiction.
  - intros op args IHs n d replacement q Hin.
    simpl in Hin |- *.
    apply in_flat_map in Hin as [e [HinArgs Hq]].
    apply in_flat_map.
    exists (subst_expression n d replacement e); split.
    + apply in_map; exact HinArgs.
    + rewrite Forall_forall in IHs.
      apply IHs with (x:=e); assumption.
Qed.

Lemma get_qubits_list_substitution_preserves_local:
forall l n d replacement q,
In q (get_qubits l) ->
In q (get_qubits (map (subst_expression n d replacement) l)).
Proof.
  induction l as [|e l IH]; simpl; intros n d replacement q Hin.
  - contradiction.
  - apply in_app_iff in Hin as [He|Htail].
    + apply in_app_iff; left.
      eapply get_qubits_expression_substitution_preserves_local; eauto.
    + apply in_app_iff; right; eapply IH; eauto.
Qed.

Lemma free_qubits_process_substitution_preserves_local:
forall P n d replacement q,
In q (free_qubits P) ->
In q (free_qubits (subst_expression_in_process n d replacement P)).
Proof.
  eapply (process_deep_ind
    (fun P => forall n d replacement q,
      In q (free_qubits P) ->
      In q (free_qubits (subst_expression_in_process n d replacement P)))).
  - intros x lz n d replacement q Hin; simpl in *.
    eapply get_qubits_list_substitution_preserves_local; eauto.
  - intros lz n d replacement q Hin; simpl in *.
    eapply get_qubits_list_substitution_preserves_local; eauto.
  - intros pt l e P0 IH n d replacement q Hin.
    simpl in Hin |- *; apply in_app_iff in Hin as [He|HP].
    + apply in_app_iff; left.
      rewrite app_nil_r in He |- *.
      eapply get_qubits_expression_substitution_preserves_local; eauto.
    + apply in_app_iff; right; eapply IH; eauto.
  - intros pt lP IHs n d replacement q Hin.
    simpl in Hin |- *.
    destruct (free_qubits_recv_In lP q Hin) as [P0 [HinP Hq]].
    apply In_to_list_onth in HinP as [i Hnth].
    pose proof (proj2 (SForall_forall process _ lP) IHs) as Hforall.
    specialize (Hforall i P0 Hnth (S n) (S d) replacement q Hq) as HqSub.
    pose proof (onth_move_in process process
      (subst_expression_in_process (S n) (S d) replacement)
      lP i P0 Hnth) as HnthSub.
    apply free_qubits_recv_member with
      (lP := smap (subst_expression_in_process (S n) (S d) replacement) lP)
      (P := subst_expression_in_process (S n) (S d) replacement P0).
    + eapply onth_to_list_In; exact HnthSub.
    + exact HqSub.
  - intros e P1 P0 IH1 IH0 n d replacement q Hin.
    simpl in Hin |- *; repeat rewrite app_nil_r in Hin |- *.
    repeat rewrite in_app_iff in *.
    destruct Hin as [He|[HP1|HP0]].
    + left.
      eapply get_qubits_expression_substitution_preserves_local; eauto.
    + right; left; eapply IH1; eauto.
    + right; right; eapply IH0; eauto.
  - intros P0 IH n d replacement q Hin.
    simpl in Hin |- *; eapply IH; eauto.
  - intros P0 IH n d replacement q Hin.
    simpl in Hin |- *; eapply IH with (n:=S n) (d:=S d); eauto.
  - intros dim U lz P0 IH n d replacement q Hin.
    simpl in Hin |- *; apply in_app_iff in Hin as [Hlz|HP].
    + apply in_app_iff; left.
      eapply get_qubits_list_substitution_preserves_local; eauto.
    + apply in_app_iff; right; eapply IH; eauto.
  - intros z P0 IH n d replacement q Hin.
    simpl in Hin |- *; apply in_app_iff in Hin as [Hz|HP].
    + apply in_app_iff; left.
      rewrite app_nil_r in Hz |- *.
      eapply get_qubits_expression_substitution_preserves_local; eauto.
    + apply in_app_iff; right; eapply IH with (n:=S n) (d:=S d); eauto.
Qed.

Lemma typecheck_session_process_component `{good_merge}:
forall M delta G qcontext p P,
typecheck_session qcontext M delta G ->
M p = Some P ->
exists T qc, typecheck_process (nil, nil, qc) P T.
Proof.
  intros M delta G qcontext p P Htyped Hlookup.
  unfold typecheck_session in Htyped.
  destruct Htyped as [lqc [Hreg [Hbal [Hassoc [Hpart
    [Hlen [Hperm Hcomponent]]]]]]].
  destruct (typecheck_session_component_of_map qcontext M delta lqc Hperm Hlen Hcomponent p P Hlookup)
    as [n [T [qc [Hdelta [Hqc [HdeltaP Hproc]]]]]].
  exists T, qc; exact Hproc.
Qed.

Lemma typecheck_session_process_support_disjoint `{good_merge}:
forall M delta G qcontext p P q,
typecheck_session qcontext M delta G ->
M p = Some P ->
In q (free_qubits P) ->
~ In q (free_qubits_session (delete M p)).
Proof.
  intros M delta G qcontext p P q Htyped Hlookup HqP HqOther.
  unfold typecheck_session in Htyped.
  destruct Htyped as [lqc [Hreg [Hbal [Hassoc [Hpart
    [Hlen [Hperm Hcomponent]]]]]]].
  destruct (typecheck_session_component_of_map qcontext M delta lqc Hperm Hlen Hcomponent p P Hlookup)
    as [np [T [qcP [HdeltaP [HqcP [HdeltaLookupP HprocP]]]]]].
  assert (HqPqc : qcP q = Some tt).
  {
    apply (proj1 (typecheck_process_qubit_use_exact P (nil, nil, qcP) T
      HprocP q)) in HqP.
    exact HqP.
  }
  apply (proj1 (free_qubits_session_in_one (delete M p) q)) in HqOther.
  destruct HqOther as [p2 [P2 [HinEntry HqP2]]].
  pose proof (proj1 ((proj2 (specs _ _ (delete M p))) p2 P2) HinEntry)
    as HlookupDel.
  assert (Hp2 : p2 <> p).
  {
    intro Heq; subst p2.
    rewrite delete_eq in HlookupDel; discriminate.
  }
  rewrite delete_neq in HlookupDel by congruence.
  destruct (typecheck_session_component_of_map qcontext M delta lqc Hperm Hlen Hcomponent p2 P2 HlookupDel)
    as [n2 [T2 [qcP2 [HdeltaP2 [HqcP2 [HdeltaLookupP2 HprocP2]]]]]].
  assert (HqP2qc : qcP2 q = Some tt).
  {
    apply (proj1 (typecheck_process_qubit_use_exact P2 (nil, nil, qcP2) T2
      HprocP2 q)) in HqP2.
    exact HqP2.
  }
  pose proof (proj1 (specs _ _ delta)) as HnodupDelta.
  assert (Hnpn2 : np <> n2).
  {
    eapply nth_error_NoDup_l_neq; [exact HdeltaP|exact HdeltaP2|exact HnodupDelta|].
    simpl; congruence.
  }
  destruct (proj2 Hpart np n2 qcP qcP2 Hnpn2 HqcP HqcP2 q)
    as [Hdisj _].
  specialize (Hdisj ltac:(rewrite HqPqc; discriminate)).
  rewrite HqP2qc in Hdisj; discriminate.
Qed.

Definition remove_qubit_from_list (q : qubit_reference)
    (l : list qubit_reference) : list qubit_reference :=
  filter (fun q' => if qr_dec q q' then false else true) l.

Lemma inb_eq_of_in_iff:
forall l1 l2 q,
(In q l1 <-> In q l2) ->
inb (E:=qr_dec) l1 q = inb (E:=qr_dec) l2 q.
Proof.
  intros l1 l2 q Hsame.
  destruct (inb l1 q) eqn:H1,
    (inb l2 q) eqn:H2; try reflexivity.
  - exfalso; apply inb_spec in H1; apply inb_false in H2.
    apply H2; apply (proj1 Hsame); exact H1.
  - exfalso; apply inb_spec in H2; apply inb_false in H1.
    apply H1; apply (proj2 Hsame); exact H2.
Qed.

Lemma list_diff_ext_on:
forall l l1 l2,
(forall q, In q l -> (In q l1 <-> In q l2)) ->
list_diff qr_dec l l1 = list_diff qr_dec l l2.
Proof.
  intros l; induction l as [|a l IH]; intros l1 l2 Hsame; simpl.
  - reflexivity.
  - assert (Hinb : inb (E:=qr_dec) l1 a =
      inb (E:=qr_dec) l2 a).
    { apply inb_eq_of_in_iff; apply Hsame; simpl; auto. }
    rewrite Hinb.
    destruct (inb (E:=qr_dec) l2 a); simpl; [apply IH|].
    + intros q Hin; apply Hsame; simpl; auto.
    + f_equal; apply IH.
      intros q Hin; apply Hsame; simpl; auto.
Qed.

Lemma list_diff_add_fresh_qubit:
forall l l2 l2' q,
~ In q l ->
(forall r, In r l2' <-> In r l2 \/ r = q) ->
list_diff qr_dec (l ++ (q :: nil)) l2' = list_diff qr_dec l l2.
Proof.
  intros l l2 l2' q Hfresh Hsupport.
  unfold list_diff.
  rewrite filter_app.
  assert (Hsame :
    filter (fun r : qubit_reference => negb (inb (E:=qr_dec) l2' r)) l =
    filter (fun r : qubit_reference => negb (inb (E:=qr_dec) l2 r)) l).
  {
    assert (Hdiff : list_diff qr_dec l l2' = list_diff qr_dec l l2).
    {
      apply list_diff_ext_on.
      intros r Hr.
      split; intro Hmem.
      - destruct (proj1 (Hsupport r) Hmem) as [Hold|Heq]; [exact Hold|].
        subst r; exfalso; apply Hfresh; exact Hr.
      - apply (proj2 (Hsupport r)); left; exact Hmem.
    }
    exact Hdiff.
  }
  rewrite Hsame.
  assert (Hqin : In q l2').
  { apply (proj2 (Hsupport q)); right; reflexivity. }
  assert (Hinb : inb (E:=qr_dec) l2' q = true).
  { apply inb_spec; exact Hqin. }
  simpl; rewrite Hinb; simpl; rewrite app_nil_r; reflexivity.
Qed.

Lemma in_remove_qubit_from_list:
forall q l r,
In r (remove_qubit_from_list q l) <-> In r l /\ r <> q.
Proof.
  intros q l r.
  unfold remove_qubit_from_list.
  rewrite filter_In.
  destruct (qr_dec q r); simpl; intuition congruence.
Qed.

Lemma inb_remove_qubit_eq:
forall q l r,
r <> q ->
inb (E:=qr_dec) (remove_qubit_from_list q l) r =
inb (E:=qr_dec) l r.
Proof.
  intros q l r Hneq.
  apply inb_eq_of_in_iff.
  rewrite in_remove_qubit_from_list.
  tauto.
Qed.

Lemma list_diff_remove_qubit_from_both:
forall l s q,
In q s ->
list_diff qr_dec (remove_qubit_from_list q l)
  (remove_qubit_from_list q s) = list_diff qr_dec l s.
Proof.
  intros l; induction l as [|a l IH]; intros s q Hqin; simpl.
  - reflexivity.
  - unfold remove_qubit_from_list at 1.
    destruct (qr_dec q a) as [->|Hneq].
    + simpl.
      assert (Hinb : inb (E:=qr_dec) s a = true)
        by (apply inb_spec; exact Hqin).
      rewrite Hinb; simpl.
      apply IH; exact Hqin.
    + simpl.
      rewrite inb_remove_qubit_eq by congruence.
      destruct (inb (E:=qr_dec) s a); simpl.
      * apply IH; exact Hqin.
      * f_equal; apply IH; exact Hqin.
Qed.

Lemma map_fst_replace_or_add_present:
forall (l : list (qubit_reference * (participant * nat))) q v,
In q (map fst l) ->
map fst (replace_or_add  (AEQ:=qr_dec) l (q, v)) =
map fst l.
Proof.
  induction l as [|[k w] l IH]; intros q v Hin; simpl in *.
  - contradiction.
  - destruct (qr_dec k q) as [Heq|Hneq].
    + subst k; simpl.
      destruct (qr_dec q q); congruence.
    + destruct Hin as [Hin|Hin]; [congruence|].
      simpl.
      destruct (qr_dec k q); [congruence|].
      f_equal; apply IH; exact Hin.
Qed.

Lemma insert_preserves_quantum_map_keys:
forall (qm : finite_map qubit_reference (participant * nat)) q v,
In q (map fst (elems qubit_reference (participant * nat) qm)) ->
map fst (elems qubit_reference (participant * nat)
  (insert (KEQ:=qr_dec) qm q v)) =
map fst (elems qubit_reference (participant * nat) qm).
Proof.
  intros qm q v Hin.
  unfold insert; simpl.
  apply map_fst_replace_or_add_present; exact Hin.
Qed.

Lemma transfer_qubit_from_lookup_keys:
forall (qm : finite_map qubit_reference (participant * nat)) Hqm
  sv Hsv new q old n Hlookup,
map fst (elems qubit_reference (participant * nat)
  (proj1_sig (projT1 (transfer_qubit_from_lookup
    qm Hqm sv Hsv new q old n Hlookup)))) =
map fst (elems qubit_reference (participant * nat) qm).
Proof.
  intros qm Hqm sv Hsv new q old n Hlookup.
  apply insert_preserves_quantum_map_keys.
  apply in_map_iff.
  exists (q, (old, n)); split; [reflexivity|].
  apply (proj2 ((proj2 (specs _ _ qm)) q (old, n))).
  exact Hlookup.
Qed.

Lemma add_new_qubit_keys_append:
forall qs p q Hfresh,
map fst (elems qubit_reference (participant * nat)
  (proj1_sig (projT1 (add_new_qubit qs p q Hfresh)))) =
map fst (elems qubit_reference (participant * nat)
  (proj1_sig (projT1 qs))) ++ q :: nil.
Proof.
  intros qs p q Hfresh.
  unfold add_new_qubit; simpl.
  rewrite replace_or_add_fresh_append by exact Hfresh.
  rewrite map_app; simpl; reflexivity.
Qed.

Lemma remove_qubit_from_list_absent:
forall q l, ~ In q l -> remove_qubit_from_list q l = l.
Proof.
  intros q l; induction l as [|a l IH]; intro Hnot; simpl; [reflexivity|].
  destruct (qr_dec q a) as [Heq|Hneq].
  - subst a; exfalso; apply Hnot; simpl; auto.
  - f_equal; apply IH; intro Hin; apply Hnot; simpl; auto.
Qed.

Lemma map_fst_remove_fst_NoDup:
forall (l : list (qubit_reference * (participant * nat))) q,
NoDup (map fst l) ->
map fst (remove_fst (AEQ:=qr_dec) l q) =
remove_qubit_from_list q (map fst l).
Proof.
  induction l as [|[k v] tl IH]; intros q Hnd; simpl in *.
  - reflexivity.
  - inversion Hnd as [|? ? Hnot Hndtl]; subst.
    destruct (qr_dec k q) as [Heq|Hneq].
    + subst k; simpl.
      destruct (qr_dec q q); [|congruence].
      rewrite remove_qubit_from_list_absent.
      * reflexivity.
      * intro Hin; apply Hnot; simpl; exact Hin.
    + simpl.
      destruct (qr_dec q k); [congruence|].
      f_equal; apply IH; exact Hndtl.
Qed.

Lemma remove_and_reindex_qubit_map_keys:
forall qm q n,
map fst (elems qubit_reference (participant * nat)
  (remove_and_reindex_qubit_map qm q n)) =
remove_qubit_from_list q
  (map fst (elems qubit_reference (participant * nat) qm)).
Proof.
  intros qm q n.
  unfold remove_and_reindex_qubit_map, reindex_quantum_map; simpl.
  rewrite map_map.
  simpl.
  apply map_fst_remove_fst_NoDup.
  apply (proj1 (specs _ _ qm)).
Qed.

Lemma cguarded_session_unfoldM_local:
forall M M',
unfoldM M M' ->
(forall p P, M p = Some P -> cguardedP P) ->
forall p P', M' p = Some P' -> cguardedP P'.
Proof.
  intros M M' Hunfold Hguard p P' Hlookup.
  destruct (Hunfold p) as [[_ Hnone']|[P [Q [Hsrc [Hdst Hpre]]]]].
  - rewrite Hnone' in Hlookup; discriminate.
  - rewrite Hdst in Hlookup; inversion Hlookup; subst P'.
    eapply cguardedP_after_subst.
    + eapply Hguard; exact Hsrc.
    + exact Hpre.
Qed.

Theorem safety_of_qubit_registers `{good_merge}:
forall M M' qstate qstate' a pi,
step (qstate, M) a (qstate', M') pi ->
(forall p P, M p = Some P -> cguardedP P) ->
forall delta G context,
typecheck_session context M delta G ->
(list_diff qr_dec (map fst (proj1_sig (projT1 qstate)).(elems _ _)) (free_qubits_session M)) =
(list_diff qr_dec (map fst (proj1_sig (projT1 qstate')).(elems _ _))
(free_qubits_session M')).
Proof.
  intros M M' qstate qstate' a pi Hstep Hguard delta G context Htyped.
  eapply (step_ind
    (fun s1 act s2 prob =>
      forall M0 M1 qs qs' delta0 G0 context0,
        s1 = (qs, M0) ->
        s2 = (qs', M1) ->
        step s1 act s2 prob ->
        (forall p P, M0 p = Some P -> cguardedP P) ->
        typecheck_session context0 M0 delta0 G0 ->
        list_diff qr_dec
          (map fst (proj1_sig (projT1 qs)).(elems _ _))
          (free_qubits_session M0) =
        list_diff qr_dec
          (map fst (proj1_sig (projT1 qs')).(elems _ _))
          (free_qubits_session M1)));
    eauto; clear; intros; cleanup; try congruence.
  - (* Classical communication. *)
    destruct (subject_reduction_via_association_2 M0
      (insert (insert M0 q (subst_expression_in_process 0 0 (Val v) Q)) p P)
      1 qs qs delta0 G0 p q l0 v context0 H8 H10)
      as [context2 [delta2 [G2 [e2 [S [Hrel [Hinc [Hctx [Hg [Heval [Hexpr Htyped']]]]]]]]]]].
    assert (Hsupport : forall x,
      In x (free_qubits_session M0) <->
      In x (free_qubits_session
        (insert (insert M0 q (subst_expression_in_process 0 0 (Val v) Q)) p P))).
    {
      intro x.
      pose proof (typecheck_session_qubit_use_exact M0 delta0 G0 context0 H10 x).
      pose proof (typecheck_session_qubit_use_exact
        (insert (insert M0 q (subst_expression_in_process 0 0 (Val v) Q)) p P)
        delta2 G2 context0 Htyped' x).
      tauto.
    }
    apply list_diff_ext_right; exact Hsupport.
  - (* Quantum communication. *)
    destruct (subject_reduction_via_association_2 M0
      (insert (insert M0 q (subst_expression_in_process 0 0 (Val (QVal v)) Q)) p P)
      1 qs
      (transfer_qubit_from_lookup (proj1_sig (projT1 qs))
        (proj2_sig (projT1 qs)) (proj1_sig (projT2 qs))
        (proj2_sig (projT2 qs)) q v p n Hlookup)
      delta0 G0 p q l0 (QVal v) context0 H8 H10)
      as [context2 [delta2 [G2 [e2 [S [Hrel [Hinc [Hctx [Hg [Heval [Hexpr Htyped']]]]]]]]]]].
    assert (Hsupport : forall x,
      In x (free_qubits_session M0) <->
      In x (free_qubits_session
        (insert (insert M0 q (subst_expression_in_process 0 0 (Val (QVal v)) Q)) p P))).
    {
      intro x.
      pose proof (typecheck_session_qubit_use_exact M0 delta0 G0 context0 H10 x).
      pose proof (typecheck_session_qubit_use_exact
        (insert (insert M0 q (subst_expression_in_process 0 0 (Val (QVal v)) Q)) p P)
        delta2 G2 context0 Htyped' x).
      tauto.
    }
    rewrite transfer_qubit_from_lookup_keys.
    apply list_diff_ext_right; exact Hsupport.
  - (* Allocation. *)
    match goal with
    | [HtypedSession : typecheck_session ?qc0 ?M0 ?delta0 ?G0 |- _] =>
        destruct (typecheck_session_process_component M0 delta0 G0 qc0 p
          (p_newq P) HtypedSession H) as [T [qc Hproc]]
    end.
    pose proof (typecheck_process_qubit_use_exact (p_newq P)
      (nil, nil, qc) T Hproc) as Hsource.
    pose proof (typecheck_process_p_newq_post T (nil, nil, qc) P Hproc)
      as Hbody.
    set (Pnew := subst_expression_in_process 0 0 (Val (QVal q)) P).
    assert (HprocSupport : forall x,
      In x (free_qubits Pnew) <-> In x (free_qubits (p_newq P)) \/ x = q).
    {
      intro x; split.
      - intro Hx.
        pose proof (free_qubits_process_substitution_local P 0 0
          (Val (QVal q)) x Hx) as Hxsub.
        simpl in Hxsub.
        destruct Hxsub as [Hold|Hnew].
        + left; exact Hold.
        + right; simpl in Hnew; destruct Hnew as [Heq|[]]; symmetry; exact Heq.
      - intros [Hold|Heq].
        + apply free_qubits_process_substitution_preserves_local; exact Hold.
        + subst x.
          destruct (in_dec qr_dec q (free_qubits (p_newq P))) as [Hold|Habsent].
          * apply free_qubits_process_substitution_preserves_local; exact Hold.
          * assert (Hqc : qc q = None).
            {
              destruct (qc q) as [u|] eqn:Hq; [|reflexivity].
              destruct u.
              exfalso; apply Habsent.
              apply (proj2 (Hsource q)).
              unfold in_qubit_context; simpl; exact Hq.
            }
            assert (Htarget : typecheck_process
              (nil, nil, insert (KEQ:=qr_dec) qc q tt) Pnew T).
            {
              unfold Pnew.
              eapply subst_expression_in_process_quantum with
                (d := 0) (T := T) (Gsr := nil) (pvc := nil) (qc := qc).
              - exact Hqc.
              - exact Hbody.
            }
            pose proof (typecheck_process_qubit_use_exact Pnew
              (nil, nil, insert (KEQ:=qr_dec) qc q tt) T Htarget q) as HtargetSupport.
            apply (proj2 HtargetSupport).
            unfold in_qubit_context; simpl; apply insert_eq.
    }
    pose proof (free_qubits_session_update_add M0 p (p_newq P) Pnew q
      H HprocSupport) as Hsupport.
    rewrite add_new_qubit_keys_append.
    symmetry.
    apply list_diff_add_fresh_qubit.
    + exact Hfresh.
    + exact Hsupport.
  - (* False conditional. *)
    match goal with
    | [HtypedSession : typecheck_session ?qc0 ?M0 ?delta0 ?G0 |- _] =>
        destruct (typecheck_session_process_component M0 delta0 G0 qc0 p
          (p_ite e P1 P0) HtypedSession H) as [T [qc Hproc]]
    end.
    destruct (typecheck_process_p_ite_post T (nil, nil, qc) P1 P0 e Hproc)
      as [_ [_ Hbranch]].
    pose proof (typecheck_process_qubit_use_exact (p_ite e P1 P0)
      (nil, nil, qc) T Hproc) as Hsource.
    pose proof (typecheck_process_qubit_use_exact P0
      (nil, nil, qc) T Hbranch) as Htarget.
    assert (Hsame : forall x,
      In x (free_qubits (p_ite e P1 P0)) <-> In x (free_qubits P0)).
    { intro x; rewrite Hsource, Htarget; tauto. }
    pose proof (free_qubits_session_update_same M0 p (p_ite e P1 P0) P0
      H Hsame) as Hsupport.
    apply list_diff_ext_right; exact Hsupport.
  - (* True conditional. *)
    match goal with
    | [HtypedSession : typecheck_session ?qc0 ?M0 ?delta0 ?G0 |- _] =>
        destruct (typecheck_session_process_component M0 delta0 G0 qc0 p
          (p_ite e P1 P0) HtypedSession H) as [T [qc Hproc]]
    end.
    destruct (typecheck_process_p_ite_post T (nil, nil, qc) P1 P0 e Hproc)
      as [_ [Hbranch _]].
    pose proof (typecheck_process_qubit_use_exact (p_ite e P1 P0)
      (nil, nil, qc) T Hproc) as Hsource.
    pose proof (typecheck_process_qubit_use_exact P1
      (nil, nil, qc) T Hbranch) as Htarget.
    assert (Hsame : forall x,
      In x (free_qubits (p_ite e P1 P0)) <-> In x (free_qubits P1)).
    { intro x; rewrite Hsource, Htarget; tauto. }
    pose proof (free_qubits_session_update_same M0 p (p_ite e P1 P0) P1
      H Hsame) as Hsupport.
    apply list_diff_ext_right; exact Hsupport.
  - (* Measurement. *)
    match goal with
    | [HtypedSession : typecheck_session ?qc0 ?M0 ?delta0 ?G0 |- _] =>
        destruct (typecheck_session_process_component M0 delta0 G0 qc0 p
          (p_measure (Val (QVal q)) P) HtypedSession H) as [T [qc Hproc]]
    end.
    destruct (typecheck_process_p_measure_post T (nil, nil, qc) P
      (Val (QVal q)) Hproc) as [Hexpr Hcont].
    unfold insert_into_variable_context, remove_measured_expression_from_context,
      remove_from_qubit_context in Hcont; simpl in Hcont.
    assert (HtargetTyped : typecheck_process (nil, nil, delete (KEQ:=qr_dec) qc q)
      (subst_expression_in_process 0 0 (Val (Bool r)) P) T).
    {
      eapply subst_expression_in_process_classical with
        (e := Val (Bool r)) (d := 0) (B := header.Bool) (Gsr := nil) (pvc := nil)
        (qc := delete (KEQ:=qr_dec) qc q).
      - exact Hcont.
      - constructor.
      - discriminate.
    }
    pose proof (typecheck_process_qubit_use_exact
      (p_measure (Val (QVal q)) P) (nil, nil, qc) T Hproc) as Hsource.
    pose proof (typecheck_process_qubit_use_exact
      (subst_expression_in_process 0 0 (Val (Bool r)) P)
      (nil, nil, delete (KEQ:=qr_dec) qc q) T HtargetTyped) as Htarget.
    assert (HprocSupport : forall x,
      In x (free_qubits (subst_expression_in_process 0 0 (Val (Bool r)) P)) <->
      In x (free_qubits (p_measure (Val (QVal q)) P)) /\ x <> q).
    {
      intro x; split.
      - intro Hx.
        apply (proj1 (Htarget x)) in Hx.
        apply delete_Some in Hx as [Hneq Hctx].
        split.
        + apply (proj2 (Hsource x)); exact Hctx.
        + congruence.
      - intros [Hold Hneq].
        apply (proj2 (Htarget x)).
        change (delete (KEQ:=qr_dec) qc q x = Some tt).
        rewrite delete_neq by congruence.
        apply (proj1 (Hsource x)); exact Hold.
    }
    assert (HqinActor : In q (free_qubits (p_measure (Val (QVal q)) P))).
    { simpl; auto. }
    match goal with
    | [HtypedSession : typecheck_session ?qc0 ?M0 ?delta0 ?G0 |- _] =>
        pose proof (typecheck_session_process_support_disjoint M0 delta0 G0 qc0
          p (p_measure (Val (QVal q)) P) q HtypedSession H HqinActor) as Hother
    end.
    pose proof (free_qubits_session_update_remove M0 p
      (p_measure (Val (QVal q)) P)
      (subst_expression_in_process 0 0 (Val (Bool r)) P) q
      H HprocSupport Hother) as Hsupport.
    assert (HqinSession : In q (free_qubits_session M0)).
    {
      pose proof (free_qubits_session_update M0 p
        (p_measure (Val (QVal q)) P) q H) as HsourceSession.
      apply (proj2 HsourceSession); left; exact HqinActor.
    }
    assert (HtargetRemoved : forall x,
      In x (free_qubits_session
        (insert M0 p (subst_expression_in_process 0 0 (Val (Bool r)) P))) <->
      In x (remove_qubit_from_list q (free_qubits_session M0))).
    {
      intro x; rewrite Hsupport, in_remove_qubit_from_list; tauto.
    }
    assert (Hqs' : qs' = snd (measure_qubit_from_nonzero
      (proj1_sig (projT1 qs)) (proj2_sig (projT1 qs))
      (proj1_sig (projT2 qs)) (proj2_sig (projT2 qs))
      q p n r Hlookup Hlen Hnonzero)).
    {
      pose proof (f_equal snd H1) as Hsnd.
      simpl in Hsnd; exact Hsnd.
    }
    assert (Hkeys : map fst (elems qubit_reference (participant * fin)
      (proj1_sig (projT1 qs'))) =
      remove_qubit_from_list q
        (map fst (elems qubit_reference (participant * fin)
          (proj1_sig (projT1 qs))))).
    {
      rewrite Hqs'.
      unfold measure_qubit_from_nonzero.
      rewrite measure_qubit_nonzero_map, remove_and_reindex_qubit_map_keys.
      reflexivity.
    }
    rewrite (list_diff_ext_right _ _ _ HtargetRemoved).
    rewrite Hkeys.
    symmetry.
    apply list_diff_remove_qubit_from_both.
    exact HqinSession.
  - (* Unitary. *)
    destruct (typecheck_session_process_component M0 delta0 G0 context0 p
      (p_unitary (length lq) U (map (fun z => Val (QVal z)) lq) P)
      H8 H) as [T [qc Hproc]].
    destruct (typecheck_process_p_unitary_post T (nil, nil, qc) P
      (length lq) U (map (fun z => Val (QVal z)) lq) Hproc)
      as [_ [_ [_ Hcont]]].
    pose proof (typecheck_process_qubit_use_exact
      (p_unitary (length lq) U (map (fun z => Val (QVal z)) lq) P)
      (nil, nil, qc) T Hproc) as Hsource.
    pose proof (typecheck_process_qubit_use_exact P
      (nil, nil, qc) T Hcont) as Htarget.
    assert (Hsame : forall x,
      In x (free_qubits
        (p_unitary (length lq) U (map (fun z => Val (QVal z)) lq) P)) <->
      In x (free_qubits P)).
    { intro x; rewrite Hsource, Htarget; tauto. }
    pose proof (free_qubits_session_update_same M0 p
      (p_unitary (length lq) U (map (fun z => Val (QVal z)) lq) P)
      P H Hsame) as Hsupport.
    assert (Hmap : proj1_sig (projT1 qs') = proj1_sig (projT1 qs)).
    {
      unfold apply_unitary in H1.
      destruct (lt_dec 0
        (length (elems qubit_reference (participant * fin)
          (proj1_sig (projT1 qs))))) as [Hpositive|Hzero];
        try discriminate.
      destruct (le_dec (length lq)
        (length (elems qubit_reference (participant * fin)
          (proj1_sig (projT1 qs))))) as [Hbound|Hbound];
        try discriminate.
      destruct (NoDup_dec (TEQ:=qr_dec) lq) as [Hnd|Hnd];
        try discriminate.
      destruct (get_all_values_certified
        (proj1_sig (projT1 qs)) lq) as [certified|] eqn:Hcert;
        try discriminate.
      inversion H1; subst; reflexivity.
    }
    rewrite Hmap.
    apply list_diff_ext_right; exact Hsupport.
  - (* Recursive unfolding. *)
    pose proof (typecheck_session_unfoldM delta0 G0 context0 M0 M1' H H7)
      as HtypedInner.
    pose proof (cguarded_session_unfoldM_local M0 M1' H H6)
      as HguardInner.
    pose proof (H2 M1' M3 qs qs' delta0 G0 context0
      eq_refl eq_refl H1 HguardInner HtypedInner) as Hinner.
    pose proof (free_qubits_session_unfoldM_equiv M0 M1' H)
      as HsupportSource.
    rewrite (list_diff_ext_right
      (map fst (elems qubit_reference (participant * fin)
        (proj1_sig (projT1 qs))))
      (free_qubits_session M0) (free_qubits_session M1') HsupportSource).
    exact Hinner.
Qed.

(* A normalized state with any prescribed nonzero computational-basis
   measurement probability. The two basis vectors differ only at wire [i]. *)
Local Open Scope R_scope.
Local Open Scope C_scope.

Definition free_qubit_sufficiency_basis0 (i : nat) (r : bool) : nat -> bool :=
  fun k => if Nat.eqb k i then r else false.

Definition free_qubit_sufficiency_basis1 (i : nat) (r : bool) : nat -> bool :=
  fun k => if Nat.eqb k i then negb r else false.

Definition free_qubit_sufficiency_measurement_vector (n i : nat) (r : bool) (prob : R)
    : state_vector n :=
  (RtoC (sqrt prob)) .* f_to_vec n (free_qubit_sufficiency_basis0 i r) .+
  (RtoC (sqrt (1 - prob))) .* f_to_vec n (free_qubit_sufficiency_basis1 i r).

Lemma free_qubit_sufficiency_fvec_norm_one : forall n f,
  norm (f_to_vec n f) = 1%R.
Proof.
  intros n f.
  assert (Hidx : (funbool_to_nat n f < 2^n)%nat).
  { apply funbool_to_nat_bound. }
  assert (Hsq : (norm (f_to_vec n f)^2)%R = 1%R).
  {
    rewrite norm_squared.
    unfold inner_product.
    rewrite basis_f_to_vec.
    rewrite basis_vector_product_eq by exact Hidx.
    unfold I; simpl; reflexivity.
  }
  pose proof (norm_ge_0 (f_to_vec n f)) as Hnonneg.
  nra.
Qed.

Lemma free_qubit_sufficiency_fvec_inner_self : forall n f,
  ⟨f_to_vec n f, f_to_vec n f⟩ = Complex.C1.
Proof.
  intros n f.
  rewrite basis_f_to_vec.
  unfold inner_product.
  rewrite basis_vector_product_eq by apply funbool_to_nat_bound.
  unfold I; simpl; reflexivity.
Qed.

Lemma free_qubit_sufficiency_fvec_inner_diff : forall n f g,
  funbool_to_nat n f <> funbool_to_nat n g ->
  ⟨f_to_vec n f, f_to_vec n g⟩ = Complex.C0.
Proof.
  intros n f g Hneq.
  rewrite (basis_f_to_vec n f), (basis_f_to_vec n g).
  unfold inner_product.
  rewrite basis_vector_product_neq.
  - reflexivity.
  - apply funbool_to_nat_bound.
  - apply funbool_to_nat_bound.
  - exact Hneq.
Qed.

Lemma free_qubit_sufficiency_basis_vectors_orthogonal01 : forall n i r,
  (i < n)%nat ->
  ⟨f_to_vec n (free_qubit_sufficiency_basis0 i r),
   f_to_vec n (free_qubit_sufficiency_basis1 i r)⟩ = Complex.C0.
Proof.
  intros n i r Hi.
  apply free_qubit_sufficiency_fvec_inner_diff.
  intro Heq.
  pose proof
    (proj2 (funbool_to_nat_eq_iff n
      (free_qubit_sufficiency_basis0 i r) (free_qubit_sufficiency_basis1 i r)) Heq i Hi)
    as Hbits.
  unfold free_qubit_sufficiency_basis0, free_qubit_sufficiency_basis1 in Hbits.
  rewrite Nat.eqb_refl in Hbits.
  destruct r; discriminate.
Qed.

Lemma free_qubit_sufficiency_basis_vectors_orthogonal10 : forall n i r,
  (i < n)%nat ->
  ⟨f_to_vec n (free_qubit_sufficiency_basis1 i r),
   f_to_vec n (free_qubit_sufficiency_basis0 i r)⟩ = Complex.C0.
Proof.
  intros n i r Hi.
  apply free_qubit_sufficiency_fvec_inner_diff.
  intro Heq.
  pose proof
    (proj2 (funbool_to_nat_eq_iff n
      (free_qubit_sufficiency_basis1 i r) (free_qubit_sufficiency_basis0 i r)) Heq i Hi)
    as Hbits.
  unfold free_qubit_sufficiency_basis0, free_qubit_sufficiency_basis1 in Hbits.
  rewrite Nat.eqb_refl in Hbits.
  destruct r; discriminate.
Qed.

Lemma free_qubit_sufficiency_measurement_vector_norm : forall n i r prob,
  (i < n)%nat -> 0%R <= prob <= 1%R ->
  @norm (2^n) (free_qubit_sufficiency_measurement_vector n i r prob) = 1%R.
Proof.
  intros n i r prob Hi [Hprob0 Hprob1].
  assert (Hsq :
    (@norm (2^n) (free_qubit_sufficiency_measurement_vector n i r prob)^2)%R = 1%R).
  {
    unfold free_qubit_sufficiency_measurement_vector.
    rewrite norm_squared.
    repeat rewrite inner_product_plus_l.
    repeat rewrite inner_product_plus_r.
    rewrite !inner_product_scale_l, !inner_product_scale_r.
    rewrite 2!Cconj_R.
    rewrite free_qubit_sufficiency_fvec_inner_self, free_qubit_sufficiency_fvec_inner_self.
    rewrite free_qubit_sufficiency_basis_vectors_orthogonal01,
      free_qubit_sufficiency_basis_vectors_orthogonal10 by exact Hi.
    simpl; ring_simplify.
    rewrite pow2_sqrt by lra.
    rewrite pow2_sqrt by lra.
    lra.
  }
  pose proof (@norm_ge_0 (2^n)
    (free_qubit_sufficiency_measurement_vector n i r prob))
    as Hnonneg.
  nra.
Qed.

Lemma free_qubit_sufficiency_measurement_vector_project : forall n i r prob,
  (i < n)%nat ->
  proj i n r × free_qubit_sufficiency_measurement_vector n i r prob =
    (RtoC (sqrt prob)) .* f_to_vec n (free_qubit_sufficiency_basis0 i r).
Proof.
  intros n i r prob Hi.
  unfold free_qubit_sufficiency_measurement_vector.
  rewrite Mmult_plus_distr_l.
  rewrite !Mscale_mult_dist_r.
  rewrite f_to_vec_proj_eq by
    (try exact Hi; unfold free_qubit_sufficiency_basis0; now rewrite Nat.eqb_refl).
  rewrite f_to_vec_proj_neq by
    (try exact Hi; unfold free_qubit_sufficiency_basis1;
     rewrite Nat.eqb_refl; destruct r; discriminate).
  rewrite Mscale_0_r, Mplus_0_r.
  reflexivity.
Qed.

Lemma free_qubit_sufficiency_measurement_vector_project_norm : forall n i r prob,
  (i < n)%nat ->
  norm (proj i n r × free_qubit_sufficiency_measurement_vector n i r prob) =
    sqrt prob.
Proof.
  intros n i r prob Hi.
  rewrite free_qubit_sufficiency_measurement_vector_project by exact Hi.
  rewrite norm_scale, free_qubit_sufficiency_fvec_norm_one, Cmod_R, Rabs_pos_eq.
  - simpl; rewrite Rmult_1_r; reflexivity.
  - apply sqrt_pos.
Qed.

Lemma free_qubit_sufficiency_measurement_vector_project_other : forall n i j r prob,
  (i < n)%nat -> (j < n)%nat -> i <> j ->
  @Mmult (2^n) (2^n) 1 (proj j n false)
    (free_qubit_sufficiency_measurement_vector n i r prob) =
    free_qubit_sufficiency_measurement_vector n i r prob.
Proof.
  intros n i j r prob Hi Hj Hneq.
  unfold free_qubit_sufficiency_measurement_vector.
  rewrite Mmult_plus_distr_l.
  rewrite !Mscale_mult_dist_r.
  rewrite f_to_vec_proj_eq.
  2: exact Hj.
  2: {
    unfold free_qubit_sufficiency_basis0.
    assert (Nat.eqb j i = false) by (apply Nat.eqb_neq; congruence).
    now rewrite H.
  }
  rewrite f_to_vec_proj_eq.
  2: exact Hj.
  2: {
    unfold free_qubit_sufficiency_basis1.
    assert (Nat.eqb j i = false) by (apply Nat.eqb_neq; congruence).
    now rewrite H.
  }
  reflexivity.
Qed.

Lemma free_qubit_sufficiency_measurement_vector_wf : forall n i r prob,
  (i < n)%nat -> 0%R < prob <= 1%R ->
  state_vector_wf (free_qubit_sufficiency_measurement_vector n i r prob).
Proof.
  intros n i r prob Hi [Hprob0 Hprob1].
  unfold state_vector_wf.
  split.
  - unfold free_qubit_sufficiency_measurement_vector.
    apply WF_plus; apply WF_scale; apply f_to_vec_WF.
  - split.
    + left; lia.
    + intros j Hj.
      destruct (Nat.eq_dec j i) as [->|Hneq].
      * exists r; split.
        -- rewrite free_qubit_sufficiency_measurement_vector_project_norm by exact Hi.
           apply Rgt_not_eq; apply sqrt_lt_R0; exact Hprob0.
        -- apply free_qubit_sufficiency_measurement_vector_norm; [exact Hi|lra].
      * exists false; split.
        -- rewrite (free_qubit_sufficiency_measurement_vector_project_other
             n i j r prob Hi Hj ltac:(congruence)).
           rewrite free_qubit_sufficiency_measurement_vector_norm by (try exact Hi; lra).
           lra.
        -- apply free_qubit_sufficiency_measurement_vector_norm; [exact Hi|lra].
Qed.

Lemma free_qubit_sufficiency_project_probability_le_one : forall n i r (sv : state_vector n),
  state_vector_wf sv -> (i < n)%nat ->
  (norm (proj i n r × sv)^2)%R <= 1%R.
Proof.
  intros n i r sv Hwf Hi.
  destruct Hwf as [Hmat [Hdim Houts]].
  destruct (Houts 0%nat ltac:(lia)) as [b0 [_ Hnormv]].
  set (projected := proj i n r × sv).
  assert (Hinner : ⟨sv, projected⟩ = ⟨projected, projected⟩).
  {
    unfold projected.
    pose proof (@inner_product_adjoint_l (2^n) (2^n)
      (proj i n r) sv (proj i n r × sv)) as H.
    rewrite proj_adjoint in H.
    rewrite <- Mmult_assoc in H.
    rewrite proj_twice_eq in H.
    symmetry; exact H.
  }
  pose proof (Cauchy_Schwartz_ver1 sv projected) as Hcs.
  rewrite Hinner in Hcs.
  assert (Hself : ⟨projected,projected⟩ =
      RtoC (norm projected ^ 2)).
  {
    apply injective_projections; simpl.
    - symmetry; apply norm_squared.
    - apply norm_real.
  }
  rewrite Hself, Cmod_R, Rabs_pos_eq in Hcs by (apply pow2_ge_0).
  simpl in Hcs.
  rewrite <- norm_squared in Hcs.
  rewrite Hnormv in Hcs.
  pose proof (@norm_ge_0 (2^n) projected) as Hnonneg.
  nra.
Qed.

Lemma free_qubit_sufficiency_qmap_key_iff : forall
    (qm : finite_map qubit_reference (participant * fin)) q,
  qm q <> None <-> In q (map fst (elems qubit_reference (participant * fin) qm)).
Proof.
  intros qm q; split.
  - intro Hpresent.
    destruct (qm q) as [[owner n]|] eqn:Hlookup; [|contradiction].
    apply in_map_iff.
    exists (q, (owner, n)); split; [reflexivity|].
    exact (proj2 (proj2 (specs qubit_reference (participant * fin) qm)
      q (owner, n)) Hlookup).
  - intro Hin.
    apply in_map_iff in Hin as [[q' value] [Heq Hin]].
    simpl in Heq; subst q'.
    destruct value as [owner n].
    pose proof (proj1 (proj2 (specs qubit_reference (participant * fin) qm)
      q (owner, n)) Hin) as Hlookup.
    rewrite Hlookup; discriminate.
Qed.

Lemma free_qubit_sufficiency_context_key_iff : forall (context : qubit_context) q,
  context q = Some tt <->
  In q (map fst (elems qubit_reference unit context)).
Proof.
  intros context q; split.
  - intro Hlookup.
    apply in_map_iff.
    exists (q, tt); split; [reflexivity|].
    exact (proj2 (proj2 (specs qubit_reference unit context) q tt) Hlookup).
  - intro Hin.
    apply in_map_iff in Hin as [[q' u] [Heq Hin]].
    simpl in Heq; subst q'.
    destruct u.
    apply (proj1 (proj2 (specs qubit_reference unit context) q tt) Hin).
Qed.

Lemma free_qubit_sufficiency_zero_state_on_context : forall
    (p : participant) (context : qubit_context),
  exists qstate,
    state_only_contains_qubits_in_context context qstate /\
    (forall q, context q = Some tt ->
      exists n, quantum_map_of qstate q = Some (p, n)).
Proof.
  intros p context.
  set (keys := map fst (elems qubit_reference unit context)).
  assert (Hnd : NoDup keys).
  { unfold keys; exact (proj1 (specs qubit_reference unit context)). }
  set (zstate := zero_state_for_qubits p keys Hnd).
  exists (proj1_sig zstate); split.
  - unfold state_only_contains_qubits_in_context.
    intro q.
    rewrite free_qubit_sufficiency_context_key_iff.
    change (In q keys <-> quantum_map_of (proj1_sig zstate) q <> None).
    rewrite free_qubit_sufficiency_qmap_key_iff.
    rewrite (proj2_sig zstate).
    rewrite in_rev.
    tauto.
  - intros q Hcontext.
    apply free_qubit_sufficiency_context_key_iff in Hcontext.
    unfold keys in Hcontext.
    unfold zstate.
    eapply zero_state_for_qubits_owner_lookup; eauto.
Qed.

Lemma free_qubit_sufficiency_process_owned_by_context `{good_merge} : forall
    (M : session) delta G context p P,
  typecheck_session context M delta G ->
  M p = Some P ->
  exists qstate,
    state_only_contains_qubits_in_context context qstate /\
    forall q, In q (free_qubits P) ->
      exists n, quantum_map_of qstate q = Some (p, n).
Proof.
  intros M delta G context p P Htyped Hlookup.
  destruct (free_qubit_sufficiency_zero_state_on_context p context)
    as [qstate [Hstate Howners]].
  exists qstate; split; [exact Hstate|].
  intros q Hin.
  assert (Hinsession : In q (free_qubits_session M)).
  {
    apply (proj2 (free_qubits_session_in_one M q)).
    exists p, P; split.
    - apply (proj2 ((proj2 (specs participant process M)) p P)).
      exact Hlookup.
    - exact Hin.
  }
  pose proof (typecheck_session_qubit_use_exact M delta G context Htyped q)
    as Hsupport.
  apply Howners.
  apply (proj1 Hsupport); exact Hinsession.
Qed.

(* A live qubit variable cannot be silently discarded by process typing. *)
Inductive qubit_variable_occurs : nat -> process -> Prop :=
| qvo_end : forall x lz, In (Var x) lz ->
    qubit_variable_occurs x (p_end lz)
| qvo_send_expr : forall x p l e P, e = Var x ->
    qubit_variable_occurs x (p_send p l e P)
| qvo_send_cont : forall x p l e P, e <> Var x ->
    qubit_variable_occurs x P ->
    qubit_variable_occurs x (p_send p l e P)
| qvo_recv : forall x p llp P,
    In P (to_list llp) -> qubit_variable_occurs (S x) P ->
    qubit_variable_occurs x (p_recv p llp)
| qvo_newq : forall x P,
    qubit_variable_occurs (S x) P ->
    qubit_variable_occurs x (p_newq P)
| qvo_unitary : forall x n U lz P,
    qubit_variable_occurs x P ->
    qubit_variable_occurs x (p_unitary n U lz P)
| qvo_measure_expr : forall x z P, z = Var x ->
    qubit_variable_occurs x (p_measure z P)
| qvo_measure_cont : forall x z P, z <> Var x ->
    qubit_variable_occurs (S x) P ->
    qubit_variable_occurs x (p_measure z P)
| qvo_ite_left : forall x e P1 P0,
    qubit_variable_occurs x P1 ->
    qubit_variable_occurs x (p_ite e P1 P0)
| qvo_ite_right : forall x e P1 P0,
    qubit_variable_occurs x P0 ->
    qubit_variable_occurs x (p_ite e P1 P0)
| qvo_var : forall x n lz, In (Var x) lz ->
    qubit_variable_occurs x (p_var n lz).

Lemma qubit_variable_occurs_after_insert : forall ctx B x,
  in_variable_context ctx x Qubit ->
  in_variable_context (insert_into_variable_context ctx B) (S x) Qubit.
Proof.
  intros [[pc vc] qc] B x Hx.
  unfold in_variable_context, insert_into_variable_context in *.
  simpl in *; exact Hx.
Qed.

Lemma qubit_variable_occurs_after_remove : forall ctx x y,
  x <> y -> in_variable_context ctx x Qubit ->
  in_variable_context (remove_from_variable_context ctx y) x Qubit.
Proof.
  intros [[pc vc] qc] x y Hxy Hx.
  unfold in_variable_context, remove_from_variable_context in *.
  simpl in *.
  rewrite nth_updn_neq_local by exact Hxy.
  exact Hx.
Qed.

Lemma SForall2_common_branch : forall A B (R S : A -> B -> Prop)
    (llp : slist A) (lBT : slist B),
  SForall2 R llp lBT -> SForall2 S llp lBT ->
  exists P BT, In P (to_list llp) /\ R P BT /\ S P BT.
Proof.
  intros A B R S llp; induction llp as [P|slot tail IH]; intros lBT HR HS.
  - inversion HR; subst. inversion HS; subst.
    exists P, y; simpl; auto.
  - destruct slot as [P|].
    + inversion HR; subst. inversion HS; subst.
      exists P, y; simpl; auto.
    + inversion HR; subst. inversion HS; subst.
      match goal with
      | hR : SForall2 R tail ?ys, hS : SForall2 S tail ?ys |- _ =>
          destruct (IH ys hR hS) as [P [BT [Hin [HRP HSP]]]]
      end.
      exists P, BT; simpl; auto.
Qed.

Lemma typecheck_process_qubit_variable_occurs : forall ctx P T,
  typecheck_process ctx P T -> forall x,
  in_variable_context ctx x Qubit -> qubit_variable_occurs x P.
Proof.
  intros ctx0 P T Htyped.
  refine (typecheck_process_deep_ind
    (fun context P T => forall x,
      in_variable_context context x Qubit -> qubit_variable_occurs x P)
    _ _ _ _ _ _ _ _ _ _ ctx0 P T Htyped).
  - intros ctx P0 T0 Hbody IH x Hx.
    apply qvo_newq; apply IH.
    unfold in_variable_context in *; simpl in *; exact Hx.
  - intros ctx z P0 T0 Hz Hbody IH x Hx.
    destruct z as [v|y|op args].
    + destruct v as [n|b|q].
      * apply qvo_measure_cont; [discriminate|]. apply IH.
        apply qubit_variable_occurs_after_insert with (B:=header.Bool).
        unfold in_variable_context; simpl; exact Hx.
      * apply qvo_measure_cont; [discriminate|]. apply IH.
        apply qubit_variable_occurs_after_insert with (B:=header.Bool).
        unfold in_variable_context; simpl; exact Hx.
      * apply qvo_measure_cont; [discriminate|]. apply IH.
        apply qubit_variable_occurs_after_insert with (B:=header.Bool).
        unfold in_variable_context; simpl; exact Hx.
    + destruct (Nat.eq_dec y x) as [->|Hneq].
      * apply qvo_measure_expr; reflexivity.
      * apply qvo_measure_cont; [congruence|]. apply IH.
        unfold in_variable_context, insert_into_variable_context,
          remove_measured_expression_from_context,
          remove_from_variable_context in *; simpl in *.
        rewrite nth_updn_neq_local by congruence.
        exact Hx.
    + inversion Hz.
  - intros ctx n U lz P0 T0 Hlen Hexpr Hnd Hbody IH x Hx.
    apply qvo_unitary; apply IH; exact Hx.
  - intros ctx lz Hcomplete Hnd x Hx.
    apply qvo_end.
    apply (proj2 (Hcomplete (Var x))).
    apply TE_Var; exact Hx.
  - intros ctx p e P0 l B T0 Hexpr Hbody IH x Hx.
    destruct e as [v|y|op args].
    + destruct v as [n|b|q].
      * inversion Hexpr; subst B. apply qvo_send_cont; [discriminate|]. apply IH; exact Hx.
      * inversion Hexpr; subst B. apply qvo_send_cont; [discriminate|]. apply IH; exact Hx.
      * inversion Hexpr; subst B. apply qvo_send_cont; [discriminate|]. apply IH; exact Hx.
    + destruct (Nat.eq_dec y x) as [->|Hneq].
      * inversion Hexpr; subst B. apply qvo_send_expr; reflexivity.
      * apply qvo_send_cont; [congruence|]. apply IH.
        destruct B; simpl in *.
        -- exact Hx.
        -- exact Hx.
        -- apply qubit_variable_occurs_after_remove with (y:=y);
             [congruence|exact Hx].
    + inversion Hexpr; subst B; try (apply qvo_send_cont; [discriminate|apply IH; exact Hx]).
  - intros ctx p lP lBT Hbranches IHbranches x Hx.
    destruct (@SForall2_common_branch process (sort * ltt)
      (fun P0 BT => typecheck_process
        (insert_into_variable_context ctx BT.1) P0 BT.2)
      (fun P0 BT => forall x,
        in_variable_context (insert_into_variable_context ctx BT.1) x Qubit ->
        qubit_variable_occurs x P0) lP lBT Hbranches IHbranches)
      as [P0 [BT [Hin [HtypedP HoccP]]]].
    apply qvo_recv with (P:=P0); [exact Hin|].
    apply HoccP.
    apply qubit_variable_occurs_after_insert with (B:=BT.1); exact Hx.
  - intros ctx e P1 P0 T0 He Ht1 IH1 Ht0 IH0 x Hx.
    apply qvo_ite_left; apply IH1; exact Hx.
  - intros ctx P0 T0 Hbody IH Honly x Hx.
    unfold only_qubit_references_in_context in Honly.
    unfold in_variable_context in Hx; simpl in Hx.
    apply Forall_forall with (x:=Some Qubit) in Honly.
    + contradiction.
    + rewrite <- Hx.
      apply nth_In with (n:=x) (d:=None).
      assert (x < length ctx.1.2)%nat by
        (apply Nat.lt_nge; intro Hge;
         rewrite nth_overflow in Hx by exact Hge; discriminate).
      exact H0.
  - intros ctx qctx X lz T0 Hproc Honly Hequiv Hcomplete Hnd x Hx.
    unfold only_qubit_references_in_context in Honly.
    unfold in_variable_context in Hx; simpl in Hx.
    apply Forall_forall with (x:=Some Qubit) in Honly.
    + contradiction.
    + rewrite <- Hx.
      apply nth_In with (n:=x) (d:=None).
      assert (x < length ctx.1.2)%nat by
        (apply Nat.lt_nge; intro Hge;
         rewrite nth_overflow in Hx by exact Hge; discriminate).
      exact H0.
  - intros ctx P0 T0 T' Hbody IH Hsub x Hx.
    apply IH; exact Hx.
Qed.

Lemma qubit_variable_substitution_expression_support : forall x d q,
  In q (get_qubits_expression
    (subst_expression x d (Val (QVal q)) (Var x))).
Proof.
  intros x d q.
  simpl.
  rewrite Nat.ltb_irrefl, Nat.eqb_refl.
  simpl; auto.
Qed.

Lemma qubit_variable_substitution_list_support : forall l x d q,
  In (Var x) l ->
  In q (get_qubits
    (map (subst_expression x d (Val (QVal q))) l)).
Proof.
  intros l x d q Hin.
  unfold get_qubits.
  apply in_flat_map.
  exists (subst_expression x d (Val (QVal q)) (Var x)); split.
  - apply in_map_iff.
    exists (Var x); split; [reflexivity|exact Hin].
  -
  apply qubit_variable_substitution_expression_support.
Qed.

Lemma smap_compose_free_qubit_sufficiency : forall A B C (f : B -> C) (g : A -> B)
    (ll : slist A),
  smap f (smap g ll) = smap (fun x => f (g x)) ll.
Proof.
  intros A B C f g ll.
  induction ll as [x|slot tail IH]; simpl; [reflexivity|].
  destruct slot; simpl; f_equal; exact IH.
Qed.

Lemma in_fold_smap_from_branch : forall A B (f : A -> B) (g : B -> list qubit_reference)
    (ll : slist A) x q,
  In x (to_list ll) -> In q (g (f x)) ->
  In q (fold_right (@app qubit_reference) nil
    (to_list (smap (fun y => g (f y)) ll))).
Proof.
  intros A B f g ll; induction ll as [head|slot tail IH]; intros x q Hin Hq.
  - simpl in Hin; destruct Hin as [->|[]].
    simpl; rewrite app_nil_r; exact Hq.
  - destruct slot as [head|]; simpl in Hin |- *.
    + destruct Hin as [->|Hin].
      * simpl; apply in_app_iff; left; exact Hq.
      * apply in_app_iff; right; eapply IH; eauto.
    + eapply IH; eassumption.
Qed.

Lemma qubit_variable_occurs_substitution_support : forall P x d q,
  qubit_variable_occurs x P ->
  In q (free_qubits
    (subst_expression_in_process x d (Val (QVal q)) P)).
Proof.
  intros P x d q Hocc.
  revert d.
  induction Hocc; intros d; simpl.
  - apply qubit_variable_substitution_list_support; exact H.
  - subst e. simpl.
    rewrite Nat.ltb_irrefl, Nat.eqb_refl.
    simpl; left; reflexivity.
  - apply in_app_iff; right; exact (IHHocc d).
  - rewrite smap_compose_free_qubit_sufficiency.
    eapply in_fold_smap_from_branch with
      (f := subst_expression_in_process (S x) (S d) (Val (QVal q)))
      (g := free_qubits); eauto.
  - exact (IHHocc (S d)).
  - apply in_app_iff; right; exact (IHHocc d).
  - subst z. simpl.
    rewrite Nat.ltb_irrefl, Nat.eqb_refl.
    simpl; left; reflexivity.
  - apply in_app_iff; right; exact (IHHocc (S d)).
  - apply in_app_iff. right; apply in_app_iff; left; exact (IHHocc d).
  - apply in_app_iff. right; apply in_app_iff; right; exact (IHHocc d).
  - apply qubit_variable_substitution_list_support; exact H.
Qed.

Local Close Scope C_scope.
Local Close Scope R_scope.

Lemma NoDup_map_collision_local : forall A B (f : A -> B) l x y,
  NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof.
  intros A B f l.
  induction l as [|a l IH]; intros x y Hnd Hx Hy Hmap; [contradiction|].
  inversion Hnd as [|fa fl Hnot Hndtail]; subst.
  simpl in Hx, Hy.
  destruct Hx as [Hx|Hx]; destruct Hy as [Hy|Hy].
  - subst; reflexivity.
  - subst x.
    exfalso; apply Hnot.
    rewrite Hmap; apply in_map; exact Hy.
  - subst y.
    exfalso; apply Hnot.
    rewrite <- Hmap; apply in_map; exact Hx.
  - eapply IH; eauto.
Qed.

Ltac nc_finish ih gs gt rs rt ts tt :=
  eapply ih with (Gsl := gs) (Gtl := gt) (Gsr := rs) (Gtr := rt)
    (T := ts) (T' := tt);
  try rewrite updn_length; eauto.

Lemma SForall2_member_local : forall A B (R : A -> B -> Prop)
    (xs : slist A) (ys : slist B) x,
  SForall2 R xs ys -> In x (to_list xs) ->
  exists y, In y (to_list ys) /\ R x y.
Proof.
  intros A B R xs ys x Hrel.
  induction Hrel as [a b Hab|a b xs ys Hab Htail IH|xs ys Htail IH];
    intros Hin.
  - simpl in Hin. destruct Hin as [->|[]].
    exists b; split; [simpl; auto|exact Hab].
  - simpl in Hin. destruct Hin as [Heq|Hin].
    + subst x. exists b; split; [simpl; auto|exact Hab].
    + destruct (IH Hin) as [y [Hiny HR]].
      exists y; split; [simpl; right; exact Hiny|exact HR].
  - simpl in Hin. destruct (IH Hin) as [y [Hiny HR]].
    exists y; split; [simpl; exact Hiny|exact HR].
Qed.

Lemma no_collision : forall (P : process) (x : nat),
  qubit_variable_occurs x P ->
  forall (q : qubit_reference) (d : nat)
    (Gsl Gtl Gsr Gtr : variable_context) (qc : qubit_context) (T T' : ltt),
    length Gsl = x -> length Gtl = x -> qc q = Some tt ->
    typecheck_process (nil, Gsl ++ Some Qubit :: Gsr, qc) P T ->
    typecheck_process (nil, Gtl ++ Gtr, qc)
      (subst_expression_in_process (length Gsl) d (Val (QVal q)) P) T' ->
    False.
Proof.
  intros P x Hocc.
  induction Hocc; intros q d Gsl Gtl Gsr Gtr qc T T' Hlen Htlen Hqc Hsrc Htgt.
  - (* end *)
    destruct (typecheck_process_p_end_post T (nil, Gsl ++ Some Qubit :: Gsr, qc) lz Hsrc)
      as [_ [Hcomplete Hndsrc]].
    destruct (typecheck_process_p_end_post T'
      (nil, Gtl ++ Gtr, qc)
      (map (subst_expression (length Gsl) d (Val (QVal q))) lz) Htgt)
      as [_ [_ Hndtgt]].
    assert (Hslot : in_variable_context (nil, Gsl ++ Some Qubit :: Gsr, qc) x Qubit).
    { unfold in_variable_context; simpl. rewrite <- Hlen, nth_middle; reflexivity. }
    assert (Hvar : typecheck_expression (nil, Gsl ++ Some Qubit :: Gsr, qc)
      (Var x) Qubit) by (constructor; exact Hslot).
    assert (Hqval : typecheck_expression (nil, Gsl ++ Some Qubit :: Gsr, qc)
      (Val (QVal q)) Qubit).
    { constructor; unfold in_qubit_context; simpl; exact Hqc. }
    assert (Hinvar : In (Var x) lz) by (apply (proj2 (Hcomplete (Var x))); exact Hvar).
    assert (Hinq : In (Val (QVal q)) lz)
      by (apply (proj2 (Hcomplete (Val (QVal q)))); exact Hqval).
    assert (Himages : subst_expression (length Gsl) d (Val (QVal q)) (Var x) =
      subst_expression (length Gsl) d (Val (QVal q)) (Val (QVal q))).
    {
      rewrite <- Hlen. simpl. rewrite Nat.ltb_irrefl, Nat.eqb_refl.
      reflexivity.
    }
    pose proof (@NoDup_map_collision_local expression expression
      (subst_expression (length Gsl) d (Val (QVal q))) lz (Var x)
      (Val (QVal q)) Hndtgt Hinvar Hinq Himages) as Heq.
    discriminate.
  - (* send expression consumes the distinguished variable *)
    subst e.
    destruct (typecheck_process_p_send_post T p l (Var x) P
      (nil, Gsl ++ Some Qubit :: Gsr, qc) Hsrc)
      as [B [Tsrc [Hsubsrc [Hexprsrc Hcontsrc]]]].
    assert (Hslot : in_variable_context (nil, Gsl ++ Some Qubit :: Gsr, qc) x Qubit).
    { unfold in_variable_context; simpl. rewrite <- Hlen, nth_middle; reflexivity. }
    assert (HctxB : in_variable_context (nil, Gsl ++ Some Qubit :: Gsr, qc) x B).
    { inversion Hexprsrc; assumption. }
    unfold in_variable_context in HctxB, Hslot; simpl in HctxB, Hslot.
    rewrite <- Hlen, nth_middle in HctxB.
    inversion HctxB; subst B.
    assert (Htargetproc : typecheck_process (nil, Gtl ++ Gtr, qc)
      (p_send p l (subst_expression (length Gsl) d (Val (QVal q)) (Var x))
        (subst_expression_in_process (length Gsl) d (Val (QVal q)) P)) T').
    { simpl in Htgt; exact Htgt. }
    destruct (typecheck_process_p_send_post T' p l
      (subst_expression (length Gsl) d (Val (QVal q)) (Var x))
      (subst_expression_in_process (length Gsl) d (Val (QVal q)) P)
      (nil, Gtl ++ Gtr, qc) Htargetproc)
      as [Bt [Tt [Hsubt [Hexprtgt Hconttgt]]]].
    assert (Hexprval : subst_expression (length Gsl) d (Val (QVal q)) (Var x) =
      Val (QVal q)).
    { rewrite <- Hlen. simpl. rewrite Nat.ltb_irrefl, Nat.eqb_refl. reflexivity. }
    rewrite Hexprval in Hexprtgt.
    rewrite Hexprval in Hconttgt.
    inversion Hexprtgt; subst.
    assert (HsrcQ : in_qubit_context
      (remove_from_variable_context (nil, Gsl ++ Some Qubit :: Gsr, qc) (length Gsl)) q).
    { unfold in_qubit_context, remove_from_variable_context; simpl.
      unfold in_qubit_context in Hqc; simpl in Hqc; exact Hqc. }
    assert (Hqfree : In q (free_qubits P)).
    { eapply typecheck_process_qubit_use_linear; [exact Hcontsrc|exact HsrcQ]. }
    assert (Hqfree' : In q (free_qubits
      (subst_expression_in_process (length Gsl) d (Val (QVal q)) P))).
    { eapply free_qubits_process_substitution_preserves_local; exact Hqfree. }
    pose proof (typecheck_process_free_qubits _
      (remove_from_qubit_context (nil, Gtl ++ Gtr, qc) q) Tt Hconttgt q Hqfree')
      as HqctxT.
    unfold in_qubit_context, remove_from_qubit_context in HqctxT; simpl in HqctxT.
    destruct (qr_dec q q) as [_|Hneq].
    + simpl in HqctxT; discriminate.
    + exfalso; apply Hneq; reflexivity.
  - (* send continuation *)
    destruct (typecheck_process_p_send_post T p l e P
      (nil, Gsl ++ Some Qubit :: Gsr, qc) Hsrc)
      as [B [Tsrc [Hsubsrc [Hexprsrc Hcontsrc]]]].
    assert (Htargetproc : typecheck_process (nil, Gtl ++ Gtr, qc)
      (p_send p l (subst_expression (length Gsl) d (Val (QVal q)) e)
        (subst_expression_in_process (length Gsl) d (Val (QVal q)) P)) T').
    { simpl in Htgt; exact Htgt. }
    destruct (typecheck_process_p_send_post T' p l
      (subst_expression (length Gsl) d (Val (QVal q)) e)
      (subst_expression_in_process (length Gsl) d (Val (QVal q)) P)
      (nil, Gtl ++ Gtr, qc) Htargetproc) as [Bt [Tt [Hsubt [Hexprtgt Hconttgt]]]].
    destruct e as [[natv|boolv|qold]|y|op args].
    - inversion Hexprsrc; subst.
      simpl in Hexprtgt; inversion Hexprtgt; subst.
      simpl in Hcontsrc, Hconttgt.
      eapply IHHocc with (Gsl := Gsl) (Gtl := Gtl)
        (Gsr := Gsr) (Gtr := Gtr) (T := Tsrc) (T' := Tt).
      + reflexivity.
      + exact Htlen.
      + exact Hqc.
      + exact Hcontsrc.
      + exact Hconttgt.
    - inversion Hexprsrc; subst.
      simpl in Hexprtgt; inversion Hexprtgt; subst.
      simpl in Hcontsrc, Hconttgt.
      eapply IHHocc with (Gsl := Gsl) (Gtl := Gtl)
        (Gsr := Gsr) (Gtr := Gtr) (T := Tsrc) (T' := Tt).
      + reflexivity.
      + exact Htlen.
      + exact Hqc.
      + exact Hcontsrc.
      + exact Hconttgt.
    - inversion Hexprsrc; subst.
      simpl in Hexprtgt; inversion Hexprtgt; subst.
      simpl in Hcontsrc, Hconttgt.
      destruct (qr_dec q qold) as [Heq|Hneq].
      + subst qold.
        pose proof (qubit_variable_occurs_substitution_support P _ d q Hocc)
          as Hfree.
        pose proof (typecheck_process_free_qubits
          (subst_expression_in_process (length Gsl) d (Val (QVal q)) P)
          (remove_from_qubit_context (nil, Gtl ++ Gtr, qc) q)
          Tt Hconttgt q Hfree) as Hlookup.
        unfold in_qubit_context, remove_from_qubit_context in Hlookup; simpl in Hlookup.
        destruct (qr_dec q q) as [_|Hneq]; [discriminate|contradiction].
      + eapply IHHocc with (Gsl := Gsl) (Gtl := Gtl)
          (Gsr := Gsr) (Gtr := Gtr)
          (qc := delete (KEQ:=qr_dec) qc qold) (T := Tsrc) (T' := Tt).
        * reflexivity.
        * exact Htlen.
        * unfold in_qubit_context in Hqc.
          rewrite delete_neq by (symmetry; exact Hneq); exact Hqc.
        * exact Hcontsrc.
        * exact Hconttgt.
    - assert (Hyneq : y <> length Gsl).
      { intro Heq; apply H; now subst. }
      destruct (Nat.lt_ge_cases y (length Gsl)) as [Hyl|Hge].
      + assert (Hsube : subst_expression (length Gsl) d (Val (QVal q)) (Var y) = Var y).
        { unfold subst_expression; simpl.
          assert ((y <? length Gsl) = true) by (apply Nat.ltb_lt; exact Hyl).
          now rewrite H0. }
        rewrite Hsube in Hconttgt.
        destruct B; destruct Bt; simpl in Hcontsrc, Hconttgt.
        * nc_finish IHHocc Gsl Gtl Gsr Gtr Tsrc Tt.
        * nc_finish IHHocc Gsl Gtl Gsr Gtr Tsrc Tt.
        * unfold remove_from_variable_context in Hconttgt; simpl in Hconttgt.
          rewrite updn_app1 in Hconttgt by lia.
          nc_finish IHHocc Gsl (updn Gtl y None) Gsr Gtr Tsrc Tt.
        * nc_finish IHHocc Gsl Gtl Gsr Gtr Tsrc Tt.
        * nc_finish IHHocc Gsl Gtl Gsr Gtr Tsrc Tt.
        * unfold remove_from_variable_context in Hconttgt; simpl in Hconttgt.
          rewrite updn_app1 in Hconttgt by lia.
          nc_finish IHHocc Gsl (updn Gtl y None) Gsr Gtr Tsrc Tt.
        * unfold remove_from_variable_context in Hcontsrc; simpl in Hcontsrc.
          rewrite updn_app1 in Hcontsrc by exact Hyl.
          nc_finish IHHocc (updn Gsl y None) Gtl Gsr Gtr Tsrc Tt.
        * unfold remove_from_variable_context in Hcontsrc; simpl in Hcontsrc.
          rewrite updn_app1 in Hcontsrc by exact Hyl.
          nc_finish IHHocc (updn Gsl y None) Gtl Gsr Gtr Tsrc Tt.
        * unfold remove_from_variable_context in Hcontsrc, Hconttgt; simpl in Hcontsrc, Hconttgt.
          rewrite updn_app1 in Hcontsrc by exact Hyl.
          rewrite updn_app1 in Hconttgt by lia.
          nc_finish IHHocc (updn Gsl y None) (updn Gtl y None) Gsr Gtr Tsrc Tt.
      + assert (Hyg : y > length Gsl).
        { destruct (Nat.eq_dec y (length Gsl)) as [Heq|Hne]; [subst; contradiction|lia]. }
        assert (Hltb : (y <? length Gsl) = false) by (apply Nat.ltb_ge; lia).
        assert (Heqb : (y =? length Gsl) = false) by (apply Nat.eqb_neq; exact Hyneq).
        assert (Hsube : subst_expression (length Gsl) d (Val (QVal q)) (Var y) = Var (y - 1)).
        { unfold subst_expression; simpl; now rewrite Hltb, Heqb. }
        rewrite Hsube in Hconttgt.
        destruct B; destruct Bt; simpl in Hcontsrc, Hconttgt.
        * nc_finish IHHocc Gsl Gtl Gsr Gtr Tsrc Tt.
        * nc_finish IHHocc Gsl Gtl Gsr Gtr Tsrc Tt.
        * unfold remove_from_variable_context in Hconttgt; simpl in Hconttgt.
          rewrite updn_app2 in Hconttgt by lia.
          replace (y - 1 - length Gtl) with (y - length Gsl - 1) in Hconttgt by lia.
          nc_finish IHHocc Gsl Gtl Gsr (updn Gtr (y - length Gsl - 1) None) Tsrc Tt.
        * nc_finish IHHocc Gsl Gtl Gsr Gtr Tsrc Tt.
        * nc_finish IHHocc Gsl Gtl Gsr Gtr Tsrc Tt.
        * unfold remove_from_variable_context in Hconttgt; simpl in Hconttgt.
          rewrite updn_app2 in Hconttgt by lia.
          replace (y - 1 - length Gtl) with (y - length Gsl - 1) in Hconttgt by lia.
          nc_finish IHHocc Gsl Gtl Gsr (updn Gtr (y - length Gsl - 1) None) Tsrc Tt.
        * unfold remove_from_variable_context in Hcontsrc; simpl in Hcontsrc.
          rewrite updn_app2 in Hcontsrc by lia.
          replace (y - length Gsl) with (S (y - length Gsl - 1)) in Hcontsrc by lia.
          simpl in Hcontsrc.
          nc_finish IHHocc Gsl Gtl (updn Gsr (y - length Gsl - 1) None) Gtr Tsrc Tt.
        * unfold remove_from_variable_context in Hcontsrc; simpl in Hcontsrc.
          rewrite updn_app2 in Hcontsrc by lia.
          replace (y - length Gsl) with (S (y - length Gsl - 1)) in Hcontsrc by lia.
          simpl in Hcontsrc.
          nc_finish IHHocc Gsl Gtl (updn Gsr (y - length Gsl - 1) None) Gtr Tsrc Tt.
        * unfold remove_from_variable_context in Hcontsrc, Hconttgt; simpl in Hcontsrc, Hconttgt.
          rewrite updn_app2 in Hcontsrc by lia.
          rewrite updn_app2 in Hconttgt by lia.
          replace (y - length Gsl) with (S (y - length Gsl - 1)) in Hcontsrc by lia.
          simpl in Hcontsrc.
          replace (y - 1 - length Gtl) with (y - length Gsl - 1) in Hconttgt by lia.
          nc_finish IHHocc Gsl Gtl (updn Gsr (y - length Gsl - 1) None)
            (updn Gtr (y - length Gsl - 1) None) Tsrc Tt.
    - cbn [subst_expression] in Hexprtgt.
      assert (HB : B <> Qubit).
      { intro Heq; subst B; inversion Hexprsrc. }
      assert (HBt : Bt <> Qubit).
      { intro Heq; subst Bt; inversion Hexprtgt. }
      destruct B; simpl in Hcontsrc; try contradiction;
      destruct Bt; simpl in Hconttgt; try contradiction;
      eapply IHHocc with (Gsl := Gsl) (Gtl := Gtl)
        (Gsr := Gsr) (Gtr := Gtr) (T := Tsrc) (T' := Tt);
        eauto.
    - (* receive branch *)
      simpl in Hsrc, Htgt.
      destruct (typecheck_process_p_recv_post T
        (nil, Gsl ++ Some Qubit :: Gsr, qc) p llp Hsrc)
        as [lBT [Hsubsrc HbranchesSrc]].
      destruct (typecheck_process_p_recv_post T'
        (nil, Gtl ++ Gtr, qc) p
        (smap (subst_expression_in_process (S (length Gsl)) (S d)
          (Val (QVal q))) llp) Htgt)
        as [lBTt [Hsubtgt HbranchesTgt]].
      destruct (@SForall2_member_local process (sort * ltt)
        (fun P0 BT => typecheck_process
          (insert_into_variable_context
            (nil, Gsl ++ Some Qubit :: Gsr, qc) BT.1) P0 BT.2)
        llp lBT P HbranchesSrc H) as [BT [HinBT HtypedP]].
      apply In_to_list_onth in H as [i Hnth].
      pose proof (onth_move_in process process
        (subst_expression_in_process (S (length Gsl)) (S d) (Val (QVal q)))
        llp i P Hnth) as HnthSub.
      pose proof (@onth_to_list_In process
        (smap (subst_expression_in_process (S (length Gsl)) (S d)
          (Val (QVal q))) llp) i
        (subst_expression_in_process (S (length Gsl)) (S d)
          (Val (QVal q)) P) HnthSub) as HinPSub.
      destruct (@SForall2_member_local process (sort * ltt)
        (fun P1 BT1 => typecheck_process
          (insert_into_variable_context (nil, Gtl ++ Gtr, qc) BT1.1)
          P1 BT1.2)
        (smap (subst_expression_in_process (S (length Gsl)) (S d)
          (Val (QVal q))) llp) lBTt
        (subst_expression_in_process (S (length Gsl)) (S d)
          (Val (QVal q)) P) HbranchesTgt HinPSub)
        as [BTt [HinBTt HtypedTarget]].
      eapply IHHocc with (Gsl := Some BT.1 :: Gsl)
        (Gtl := Some BTt.1 :: Gtl) (Gsr := Gsr) (Gtr := Gtr)
        (T := BT.2) (T' := BTt.2).
      + simpl; now rewrite Hlen.
      + simpl; now rewrite Htlen.
      + exact Hqc.
      + exact HtypedP.
      + exact HtypedTarget.
    - (* nested allocation *)
      pose proof (typecheck_process_p_newq_post T
        (nil, Gsl ++ Some Qubit :: Gsr, qc) P Hsrc) as HbodySrc.
      simpl in Htgt.
      pose proof (typecheck_process_p_newq_post T'
        (nil, Gtl ++ Gtr, qc)
        (subst_expression_in_process (S (length Gsl)) (S d)
          (Val (QVal q)) P) Htgt) as HbodyTgt.
      eapply IHHocc with (Gsl := Some Qubit :: Gsl)
        (Gtl := Some Qubit :: Gtl) (Gsr := Gsr) (Gtr := Gtr)
        (T := T) (T' := T').
      + simpl; now rewrite Hlen.
      + simpl; now rewrite Htlen.
      + exact Hqc.
      + exact HbodySrc.
      + exact HbodyTgt.
    - (* unitary operation *)
      destruct (typecheck_process_p_unitary_post T
        (nil, Gsl ++ Some Qubit :: Gsr, qc) P n U lz Hsrc)
        as [_ [_ [_ HbodySrc]]].
      simpl in Htgt.
      destruct (typecheck_process_p_unitary_post T'
        (nil, Gtl ++ Gtr, qc)
        (subst_expression_in_process (length Gsl) d (Val (QVal q)) P) n U
        (map (subst_expression (length Gsl) d (Val (QVal q))) lz) Htgt)
        as [_ [_ [_ HbodyTgt]]].
      eapply IHHocc with (Gsl := Gsl) (Gtl := Gtl)
        (Gsr := Gsr) (Gtr := Gtr) (T := T) (T' := T').
      + exact Hlen.
      + exact Htlen.
      + exact Hqc.
      + exact HbodySrc.
      + exact HbodyTgt.
    - (* measuring the distinguished variable consumes the qubit already in qc *)
      subst z.
      rewrite <- Hlen in Htgt.
      simpl in Htgt.
      rewrite Nat.ltb_irrefl, Nat.eqb_refl in Htgt.
      simpl in Htgt.
      destruct (typecheck_process_p_measure_post T
        (nil, Gsl ++ Some Qubit :: Gsr, qc) P (Var x) Hsrc)
        as [_ HcontSrc].
      destruct (typecheck_process_p_measure_post T'
        (nil, Gtl ++ Gtr, qc)
        (subst_expression_in_process (S (length Gsl)) (S d)
          (Val (QVal q)) P) (Val (QVal q)) Htgt)
        as [_ HcontTgt].
      assert (HqfreeSrc : In q (free_qubits P)).
      {
        pose proof (typecheck_process_qubit_use_exact P
          (insert_into_variable_context
            (remove_from_variable_context
              (nil, Gsl ++ Some Qubit :: Gsr, qc) x) header.Bool)
          T HcontSrc q) as Hsupport.
        apply (proj2 Hsupport).
        unfold in_qubit_context, insert_into_variable_context,
          remove_from_variable_context; simpl; exact Hqc.
      }
      pose proof (free_qubits_process_substitution_preserves_local P
        (S (length Gsl)) (S d) (Val (QVal q)) q HqfreeSrc) as HqfreeTgt.
      pose proof (typecheck_process_free_qubits
        (subst_expression_in_process (S (length Gsl)) (S d)
          (Val (QVal q)) P)
        (insert_into_variable_context
          (remove_from_qubit_context (nil, Gtl ++ Gtr, qc) q)
          header.Bool) T' HcontTgt q HqfreeTgt) as Hqlookup.
      unfold in_qubit_context, insert_into_variable_context,
        remove_from_qubit_context in Hqlookup; simpl in Hqlookup.
      destruct (qr_dec q q) as [_|Hneq]; [discriminate|contradiction].
    - (* measuring another expression leaves the distinguished occurrence live *)
      destruct (typecheck_process_p_measure_post T
        (nil, Gsl ++ Some Qubit :: Gsr, qc) P z Hsrc)
        as [HexprSrc HcontSrc].
      simpl in Htgt.
      destruct (typecheck_process_p_measure_post T'
        (nil, Gtl ++ Gtr, qc)
        (subst_expression_in_process (S (length Gsl)) (S d)
          (Val (QVal q)) P)
        (subst_expression (length Gsl) d (Val (QVal q)) z) Htgt)
        as [HexprTgt HcontTgt].
      destruct z as [[n|b|qold]|y|op args].
      + inversion HexprSrc.
      + inversion HexprSrc.
      + simpl in HcontSrc, HcontTgt.
        destruct (qr_dec q qold) as [Heq|Hneq].
        * subst qold.
          assert (Hocc' : qubit_variable_occurs (S (length Gsl)) P).
          { rewrite Hlen; exact Hocc. }
          pose proof (qubit_variable_occurs_substitution_support P
            (S (length Gsl)) (S d) q Hocc') as Hqfree.
          pose proof (typecheck_process_free_qubits
            (subst_expression_in_process (S (length Gsl)) (S d)
              (Val (QVal q)) P)
            (insert_into_variable_context
              (remove_from_qubit_context (nil, Gtl ++ Gtr, qc) q)
              header.Bool) T' HcontTgt q Hqfree) as Hqlookup.
          unfold in_qubit_context, insert_into_variable_context,
            remove_from_qubit_context in Hqlookup; simpl in Hqlookup.
          destruct (qr_dec q q) as [_|Hneq]; [discriminate|contradiction].
        * unfold insert_into_variable_context, remove_measured_expression_from_context,
            remove_from_qubit_context in HcontSrc, HcontTgt; simpl in HcontSrc, HcontTgt.
          eapply IHHocc with (Gsl := Some header.Bool :: Gsl)
            (Gtl := Some header.Bool :: Gtl) (Gsr := Gsr) (Gtr := Gtr)
            (qc := delete (KEQ:=qr_dec) qc qold) (T := T) (T' := T').
          -- simpl; now rewrite Hlen.
          -- simpl; now rewrite Htlen.
          -- unfold in_qubit_context in Hqc.
             rewrite delete_neq by (symmetry; exact Hneq); exact Hqc.
          -- exact HcontSrc.
          -- exact HcontTgt.
      + assert (Hyneq : y <> x).
        { intro Heq; apply H; now inversion Heq. }
        destruct (Nat.lt_ge_cases y (length Gsl)) as [Hyl|Hge].
        * assert (Hsubz : subst_expression (length Gsl) d
            (Val (QVal q)) (Var y) = Var y).
          {
            unfold subst_expression; simpl.
            assert ((y <? length Gsl) = true) by (apply Nat.ltb_lt; exact Hyl).
            now rewrite H0.
          }
          rewrite Hsubz in HcontTgt.
          unfold insert_into_variable_context,
            remove_measured_expression_from_context,
            remove_from_variable_context in HcontSrc, HcontTgt; simpl in HcontSrc, HcontTgt.
          rewrite updn_app1 in HcontSrc by exact Hyl.
          rewrite updn_app1 in HcontTgt by lia.
          assert (Hcutoff :
            length (Some header.Bool :: updn Gsl y None) = S (length Gsl)).
          { simpl; rewrite updn_length; reflexivity. }
          rewrite <- Hcutoff in HcontTgt.
          eapply IHHocc with
            (Gsl := Some header.Bool :: updn Gsl y None)
            (Gtl := Some header.Bool :: updn Gtl y None)
            (Gsr := Gsr) (Gtr := Gtr) (T := T) (T' := T').
          -- simpl; rewrite updn_length; now rewrite Hlen.
          -- simpl; rewrite updn_length; now rewrite Htlen.
          -- exact Hqc.
          -- exact HcontSrc.
          -- exact HcontTgt.
        * assert (HyneqLen : y <> length Gsl).
          { intro Heq; apply Hyneq; now rewrite <- Hlen. }
          assert (Hyg : y > length Gsl) by lia.
          assert (Hltb : (y <? length Gsl) = false) by (apply Nat.ltb_ge; lia).
          assert (Heqb : (y =? length Gsl) = false).
          { apply Nat.eqb_neq; exact HyneqLen. }
          assert (Hsubz : subst_expression (length Gsl) d
            (Val (QVal q)) (Var y) = Var (y - 1)).
          { unfold subst_expression; simpl; now rewrite Hltb, Heqb. }
          rewrite Hsubz in HcontTgt.
          unfold insert_into_variable_context,
            remove_measured_expression_from_context,
            remove_from_variable_context in HcontSrc, HcontTgt; simpl in HcontSrc, HcontTgt.
          rewrite updn_app2 in HcontSrc by lia.
          replace (y - length Gsl) with (S (y - length Gsl - 1)) in HcontSrc by lia.
          simpl in HcontSrc.
          rewrite updn_app2 in HcontTgt by lia.
          replace (y - 1 - length Gtl) with (y - length Gsl - 1) in HcontTgt by lia.
          eapply IHHocc with (Gsl := Some header.Bool :: Gsl)
            (Gtl := Some header.Bool :: Gtl) (Gsr := updn Gsr (y - length Gsl - 1) None)
            (Gtr := updn Gtr (y - length Gsl - 1) None) (T := T) (T' := T').
          -- simpl; now rewrite Hlen.
          -- simpl; now rewrite Htlen.
          -- exact Hqc.
          -- exact HcontSrc.
          -- exact HcontTgt.
      + inversion HexprSrc.
    - (* conditional, left branch *)
      destruct (typecheck_process_p_ite_post T
        (nil, Gsl ++ Some Qubit :: Gsr, qc) P1 P0 e Hsrc)
        as [_ [HsrcLeft _]].
      simpl in Htgt.
      destruct (typecheck_process_p_ite_post T'
        (nil, Gtl ++ Gtr, qc)
        (subst_expression_in_process (length Gsl) d (Val (QVal q)) P1)
        (subst_expression_in_process (length Gsl) d (Val (QVal q)) P0)
        (subst_expression (length Gsl) d (Val (QVal q)) e) Htgt)
        as [_ [HtgtLeft _]].
      eapply IHHocc with (Gsl := Gsl) (Gtl := Gtl)
        (Gsr := Gsr) (Gtr := Gtr) (T := T) (T' := T').
      + exact Hlen.
      + exact Htlen.
      + exact Hqc.
      + exact HsrcLeft.
      + exact HtgtLeft.
    - (* conditional, right branch *)
      destruct (typecheck_process_p_ite_post T
        (nil, Gsl ++ Some Qubit :: Gsr, qc) P1 P0 e Hsrc)
        as [_ [_ HsrcRight]].
      simpl in Htgt.
      destruct (typecheck_process_p_ite_post T'
        (nil, Gtl ++ Gtr, qc)
        (subst_expression_in_process (length Gsl) d (Val (QVal q)) P1)
        (subst_expression_in_process (length Gsl) d (Val (QVal q)) P0)
        (subst_expression (length Gsl) d (Val (QVal q)) e) Htgt)
        as [_ [_ HtgtRight]].
      eapply IHHocc with (Gsl := Gsl) (Gtl := Gtl)
        (Gsr := Gsr) (Gtr := Gtr) (T := T) (T' := T').
      + exact Hlen.
      + exact Htlen.
      + exact Hqc.
      + exact HsrcRight.
      + exact HtgtRight.
    - (* recursive variable carries the qubit occurrence in its interface *)
      destruct (typecheck_process_p_var_post T
        (nil, Gsl ++ Some Qubit :: Gsr, qc) n lz Hsrc)
        as [Tsrc [qctxsrc [_ [_ [_ [HcompleteSrc [HndSrc _]]]]]]].
      simpl in Htgt.
      destruct (typecheck_process_p_var_post T'
        (nil, Gtl ++ Gtr, qc) n
        (map (subst_expression (length Gsl) d (Val (QVal q))) lz) Htgt)
        as [Tt [qctxtgt [_ [_ [_ [_ [HndTgt _]]]]]]].
      assert (Hslot : in_variable_context
        (nil, Gsl ++ Some Qubit :: Gsr, qc) x Qubit).
      { unfold in_variable_context; simpl. rewrite <- Hlen, nth_middle; reflexivity. }
      assert (Hvar : typecheck_expression
        (nil, Gsl ++ Some Qubit :: Gsr, qc) (Var x) Qubit).
      { constructor; exact Hslot. }
      assert (Hqval : typecheck_expression
        (nil, Gsl ++ Some Qubit :: Gsr, qc) (Val (QVal q)) Qubit).
      { constructor; unfold in_qubit_context; simpl; exact Hqc. }
      assert (Hinvar : In (Var x) lz).
      { apply (proj2 (HcompleteSrc (Var x))); exact Hvar. }
      assert (Hinq : In (Val (QVal q)) lz).
      { apply (proj2 (HcompleteSrc (Val (QVal q)))); exact Hqval. }
      assert (Himages : subst_expression (length Gsl) d
        (Val (QVal q)) (Var x) =
        subst_expression (length Gsl) d (Val (QVal q)) (Val (QVal q))).
      {
        rewrite <- Hlen. simpl. rewrite Nat.ltb_irrefl, Nat.eqb_refl.
        reflexivity.
      }
      pose proof (@NoDup_map_collision_local expression expression
        (subst_expression (length Gsl) d (Val (QVal q))) lz (Var x)
        (Val (QVal q)) HndTgt Hinvar Hinq Himages) as Heq.
      discriminate.
Qed.


Lemma qsafe_eval_op_never_qubit : forall op values q,
  eval_op op values <> Some (QVal q).
Proof.
  intros op values q.
  destruct op; destruct values as [|v1 [|v2 [|v3 rest]]];
    simpl; try discriminate.
  all: try destruct v1 as [n1|b1|q1].
  all: try destruct v2 as [n2|b2|q2].
  all: simpl; discriminate.
Qed.

Lemma qsafe_eval_qubit_value_is_literal : forall e q,
  evaluate_expression e = Some (QVal q) -> e = Val (QVal q).
Proof.
  intros [v|x|op args] q Heval; simpl in Heval.
  - destruct v as [n|b|q0]; simpl in Heval; try discriminate.
    inversion Heval; reflexivity.
  - discriminate.
  - destruct (strip_option (map evaluate_expression args)) as [values|]
      eqn:Hvalues; simpl in Heval; [|discriminate].
    exfalso; eapply qsafe_eval_op_never_qubit; exact Heval.
Qed.

Theorem free_qubit_sufficiency `{good_merge}:
forall M M' qstate qstate' a pi delta G context delta' G' context',
typecheck_session context M delta G ->
step (qstate, M) a (qstate', M') pi ->
typecheck_session context' M' delta' G' ->
(forall p P, M p = Some P -> cguardedP P) ->
variable_closed_session M ->
exists qstate_min qstate_min',
step (qstate_min, M) a (qstate_min', M') pi /\
state_only_contains_qubits_in_context context qstate_min /\
state_only_contains_qubits_in_context context' qstate_min'.
Proof.
  intros M M' qstate qstate' a pi delta G context delta' G' context'
    Htyped Hstep Htyped' Hguard Hclosed.
  clear Hclosed.
  revert delta G context delta' G' Htyped Htyped' Hguard.
  dependent induction Hstep; intros; cleanup; try congruence.
  - destruct (free_qubit_sufficiency_zero_state_on_context p context)
      as [qstate_min [Hsafe _]].
    assert (Hreplay : step (qstate_min, M) (Transmit p q l0 v)
      (qstate_min, insert (insert M q
        (subst_expression_in_process 0 0 (Val v) Q)) p P) 1).
    { eapply Comm_C; eauto. }
    exists qstate_min, qstate_min; split; [exact Hreplay|].
    split; [exact Hsafe|].
    eapply state_only_contains_qubits_in_context_after_step.
    + exact Hreplay.
    + exact Hguard.
    + exact Htyped.
    + exact Hsafe.
    + exact Htyped'.
  - assert (Heval_literal : e = Val (QVal v)).
    { eapply qsafe_eval_qubit_value_is_literal; exact H4. }
    assert (Hqfree : In v (free_qubits (p_send q l0 e P))).
    { subst e; simpl; left; reflexivity. }
    assert (Hqsession : In v (free_qubits_session M)).
    {
      apply (proj2 (free_qubits_session_update M p
        (p_send q l0 e P) v H)); left; exact Hqfree.
    }
    pose proof (typecheck_session_qubit_use_exact M delta G context Htyped v)
      as Hsupport.
    assert (Hqcontext : context v = Some tt).
    { apply (proj1 Hsupport); exact Hqsession. }
    destruct (free_qubit_sufficiency_zero_state_on_context p context)
      as [qstate_min [Hsafe Howners]].
    destruct (Howners v Hqcontext) as [nmin Hlookup_min].
    set (qstate_min' := transfer_qubit_from_lookup
      (proj1_sig (projT1 qstate_min)) (proj2_sig (projT1 qstate_min))
      (proj1_sig (projT2 qstate_min)) (proj2_sig (projT2 qstate_min))
      q v p nmin Hlookup_min).
    assert (Hreplay : step (qstate_min, M) (Transmit p q l0 (QVal v))
      (qstate_min', insert (insert M q
        (subst_expression_in_process 0 0 (Val (QVal v)) Q)) p P) 1).
    {
      unfold qstate_min'.
      eapply Comm_Q with (p := p) (q := q) (l := l0) (e := e)
        (P := P) (lQ := lQ) (Q := Q) (v := v) (s1 := M)
        (q_state := qstate_min) (q_state' :=
          transfer_qubit_from_lookup
            (proj1_sig (projT1 qstate_min)) (proj2_sig (projT1 qstate_min))
            (proj1_sig (projT2 qstate_min)) (proj2_sig (projT2 qstate_min))
            q v p nmin Hlookup_min)
        (n := nmin) (Hlookup := Hlookup_min); eauto.
    }
    exists qstate_min, qstate_min'; split; [exact Hreplay|].
    split; [exact Hsafe|].
    eapply state_only_contains_qubits_in_context_after_step.
    + exact Hreplay.
    + exact Hguard.
    + exact Htyped.
    + exact Hsafe.
    + exact Htyped'.
  - set (Pnew := subst_expression_in_process 0 0 (Val (QVal q)) P).
    destruct (typecheck_session_process_component M delta G context p
      (p_newq P) Htyped H) as [Tsrc [qcSrc Hsrc]].
    pose proof (typecheck_process_p_newq_post Tsrc (nil, nil, qcSrc) P Hsrc)
      as Hbody.
    assert (Hslot : in_variable_context (nil, [Some Qubit], qcSrc) 0 Qubit).
    { unfold in_variable_context; simpl; reflexivity. }
    pose proof (typecheck_process_qubit_variable_occurs
      (nil, [Some Qubit], qcSrc) P Tsrc Hbody 0 Hslot) as Hocc.
    assert (Hnewlookup : insert M p Pnew p = Some Pnew) by apply insert_eq.
    destruct (typecheck_session_process_component
      (insert M p Pnew) delta' G' context' p Pnew Htyped' Hnewlookup)
      as [Ttgt [qcTgt Htgt]].
    assert (HnotContext : context q <> Some tt).
    {
      intro Hqcontext.
      pose proof (typecheck_session_qubit_use_exact M delta G context Htyped q)
        as HsessionSupport.
      assert (Hqsession : In q (free_qubits_session M)).
      { apply (proj2 HsessionSupport); exact Hqcontext. }
      pose proof (free_qubits_session_update M p (p_newq P) q H)
        as Hupdate.
      destruct (proj1 Hupdate Hqsession) as [Hlocal|Hother].
      - assert (HqcSrc : qcSrc q = Some tt).
        {
          apply (proj1 (typecheck_process_qubit_use_exact
            (p_newq P) (nil, nil, qcSrc) Tsrc Hsrc q)).
          simpl; exact Hlocal.
        }
        assert (HprocSupport : forall x,
          In x (free_qubits Pnew) <-> In x (free_qubits (p_newq P))).
        {
          intro x; split.
          - intro Hx.
            pose proof (free_qubits_process_substitution_local P 0 0
              (Val (QVal q)) x Hx) as Hsub.
            simpl in Hsub.
            destruct Hsub as [Hold|Hadded].
            + simpl; exact Hold.
            + simpl in Hadded; destruct Hadded as [Heq|[]].
              subst x; simpl; exact Hlocal.
          - intro Hx.
            simpl in Hx.
            unfold Pnew.
            eapply free_qubits_process_substitution_preserves_local; exact Hx.
        }
        pose proof (typecheck_process_qubit_use_exact Pnew
          (nil, nil, qcTgt) Ttgt Htgt) as HtgtSupport.
        pose proof (typecheck_process_qubit_use_exact (p_newq P)
          (nil, nil, qcSrc) Tsrc Hsrc) as HsrcSupport.
        assert (HqcEquiv : equivalent qcTgt qcSrc).
        {
          unfold equivalent, included; split.
          - intros x [] Hlookup.
            apply (proj1 (HsrcSupport x)).
            apply (proj1 (HprocSupport x)).
            apply (proj2 (HtgtSupport x)); exact Hlookup.
          - intros x [] Hlookup.
            apply (proj1 (HtgtSupport x)).
            apply (proj2 (HprocSupport x)).
            apply (proj2 (HsrcSupport x)); exact Hlookup.
        }
        assert (HtgtAtSrc : typecheck_process (nil, nil, qcSrc) Pnew Ttgt).
        {
          eapply typecheck_process_equivalent with
            (theta1 := (nil, nil, qcTgt)) (theta2 := (nil, nil, qcSrc)).
          - exact Htgt.
          - reflexivity.
          - constructor.
          - exact HqcEquiv.
        }
        exfalso.
        eapply (no_collision P 0 Hocc q 0 nil nil nil nil qcSrc Tsrc Ttgt).
        * reflexivity.
        * reflexivity.
        * exact HqcSrc.
        * exact Hbody.
        * unfold Pnew in HtgtAtSrc; exact HtgtAtSrc.
      - pose proof (qubit_variable_occurs_substitution_support P 0 0 q Hocc)
          as Hqnewfree.
        assert (HtargetOther : ~ In q
          (free_qubits_session (delete (insert M p Pnew) p))).
        {
          eapply typecheck_session_process_support_disjoint.
          - exact Htyped'.
          - exact Hnewlookup.
          - exact Hqnewfree.
        }
        assert (HdeleteEquiv : equivalent
          (delete (insert M p Pnew) p) (delete M p)).
        {
          unfold equivalent, included; split; intros k value Hlookup;
            destruct (participant_dec p k) as [Heq|Hneq].
          - subst k; rewrite delete_eq in Hlookup; discriminate.
          - rewrite delete_neq in Hlookup by exact Hneq.
            rewrite insert_neq in Hlookup by congruence.
            rewrite delete_neq by congruence; exact Hlookup.
          - subst k; rewrite delete_eq in Hlookup; discriminate.
          - rewrite delete_neq in Hlookup by exact Hneq.
            rewrite delete_neq by congruence.
            rewrite insert_neq by congruence; exact Hlookup.
        }
        pose proof (free_qubits_session_equivalent
          (delete (insert M p Pnew) p) (delete M p) HdeleteEquiv)
          as HdeletePerm.
        apply HtargetOther.
        eapply Permutation_in.
        + apply Permutation_sym; exact HdeletePerm.
        + exact Hother.
    }
    destruct (free_qubit_sufficiency_zero_state_on_context p context)
      as [qstate_min [Hsafe _]].
    assert (HfreshMin : ~ In q
      (map fst (elems qubit_reference (participant * fin)
        (proj1_sig (projT1 qstate_min)))))
      by (intro Hin; apply HnotContext; apply (proj2 (Hsafe q));
          apply (proj2 (free_qubit_sufficiency_qmap_key_iff
            (proj1_sig (projT1 qstate_min)) q)); exact Hin).
    set (qstate_min' := add_new_qubit qstate_min p q HfreshMin).
    assert (Hreplay : step (qstate_min, M) (Tau p)
      (qstate_min', insert M p Pnew) 1).
    {
      unfold qstate_min', Pnew.
      eapply New with (p := p) (P := P) (s1 := M) (q := q)
        (Hfresh := HfreshMin); exact H.
    }
    exists qstate_min, qstate_min'; split; [exact Hreplay|].
    split; [exact Hsafe|].
    eapply state_only_contains_qubits_in_context_after_step.
    + exact Hreplay.
    + exact Hguard.
    + exact Htyped.
    + exact Hsafe.
    + exact Htyped'.
  - destruct (free_qubit_sufficiency_zero_state_on_context p context)
      as [qstate_min [Hsafe _]].
    assert (Hreplay : step (qstate_min, M) (Tau p)
      (qstate_min, insert M p P0) 1).
    { eapply If_0; eauto. }
    exists qstate_min, qstate_min; split; [exact Hreplay|].
    split; [exact Hsafe|].
    eapply state_only_contains_qubits_in_context_after_step.
    + exact Hreplay.
    + exact Hguard.
    + exact Htyped.
    + exact Hsafe.
    + exact Htyped'.
  - destruct (free_qubit_sufficiency_zero_state_on_context p context)
      as [qstate_min [Hsafe _]].
    assert (Hreplay : step (qstate_min, M) (Tau p)
      (qstate_min, insert M p P1) 1).
    { eapply If_1; eauto. }
    exists qstate_min, qstate_min; split; [exact Hreplay|].
    split; [exact Hsafe|].
    eapply state_only_contains_qubits_in_context_after_step.
    + exact Hreplay.
    + exact Hguard.
    + exact Htyped.
    + exact Hsafe.
    + exact Htyped'.
  - assert (Hqfree : In q (free_qubits (p_measure (Val (QVal q)) P))).
    { simpl; auto. }
    assert (Hqsession : In q (free_qubits_session M)).
    {
      apply (proj2 (free_qubits_session_update M p
        (p_measure (Val (QVal q)) P) q H)); left; exact Hqfree.
    }
    pose proof (typecheck_session_qubit_use_exact M delta G context Htyped q)
      as HsessionSupport.
    assert (Hqcontext : context q = Some tt).
    { apply (proj1 HsessionSupport); exact Hqsession. }
    destruct (free_qubit_sufficiency_zero_state_on_context p context)
      as [qstate_base [HbaseSafe HbaseOwners]].
    destruct (HbaseOwners q Hqcontext) as [nbase HlookupBase].
    set (qmBase := proj1_sig (projT1 qstate_base)).
    set (Nbase := length (elems qubit_reference (participant * fin) qmBase)).
    assert (HidxBase : nbase < Nbase).
    {
      unfold Nbase, qmBase.
      eapply quantum_map_lookup_index_lt.
      - exact (proj2_sig (projT1 qstate_base)).
      - exact HlookupBase.
    }
    assert (HlenBase : 0 < Nbase) by lia.
    set (qmOrig := proj1_sig (projT1 qstate)).
    set (svOrig := proj1_sig (projT2 qstate)).
    set (Norig := length (elems qubit_reference (participant * fin) qmOrig)).
    assert (HidxOrig : n < Norig).
    {
      unfold Norig, qmOrig.
      eapply quantum_map_lookup_index_lt.
      - exact (proj2_sig (projT1 qstate)).
      - exact Hlookup.
    }
    assert (HsvOrig : state_vector_wf svOrig) by exact (proj2_sig (projT2 qstate)).
    set (prob := (norm (proj n Norig r × svOrig)^2)%R).
    assert (HnormOrig : (0 < norm (proj n Norig r × svOrig))%R).
    {
      pose proof (norm_ge_0 (proj n Norig r × svOrig)) as HnormNonnegative.
      assert (HnormNonzero : norm (proj n Norig r × svOrig) <> 0%R)
        by exact Hnonzero.
      lra.
    }
    assert (HprobPos : (0 < prob)%R).
    { unfold prob; apply pow_lt; exact HnormOrig. }
    assert (HprobLe : (prob <= 1)%R).
    {
      unfold prob.
      eapply free_qubit_sufficiency_project_probability_le_one.
      - exact HsvOrig.
      - exact HidxOrig.
    }
    set (svMin := free_qubit_sufficiency_measurement_vector Nbase nbase r prob).
    assert (HsvMin : state_vector_wf svMin).
    {
      unfold svMin.
      apply free_qubit_sufficiency_measurement_vector_wf.
      - exact HidxBase.
      - split; assumption.
    }
    set (qstate_min :=
      (existT
        (fun qm : {qm : finite_map qubit_reference (participant * fin) |
            quantum_map_wf qm} =>
          {sv : state_vector
              (length (elems qubit_reference (participant * fin) (proj1_sig qm))) |
            state_vector_wf sv})
        (projT1 qstate_base)
        (exist (fun sv : state_vector Nbase => state_vector_wf sv)
          svMin HsvMin) : quantum_state)).
    assert (Hsafe : state_only_contains_qubits_in_context context qstate_min).
    { exact HbaseSafe. }
    assert (HlookupMin : qmBase q = Some (p, nbase)).
    { unfold qmBase; exact HlookupBase. }
    assert (HnonzeroMin : norm (proj nbase Nbase r × svMin) <> 0%R).
    {
      unfold svMin.
      rewrite (free_qubit_sufficiency_measurement_vector_project_norm
        Nbase nbase r prob HidxBase).
      apply Rgt_not_eq.
      apply sqrt_lt_R0; exact HprobPos.
    }
    set (piMin := measurement_probability_from_nonzero
      Nbase svMin nbase r HnonzeroMin).
    set (qstate_min' := snd (measure_qubit_from_nonzero
      qmBase (proj2_sig (projT1 qstate_base)) svMin HsvMin
      q p nbase r HlookupMin HlenBase HnonzeroMin)).
    assert (HprobEqual : proj1_sig piMin =
      proj1_sig (measurement_probability_from_nonzero
        Norig svOrig n r Hnonzero)).
    {
      unfold piMin.
      rewrite !measurement_probability_from_nonzero_value.
      unfold svMin.
      rewrite (free_qubit_sufficiency_measurement_vector_project_norm
        Nbase nbase r prob HidxBase).
      rewrite pow2_sqrt by lra.
      unfold prob, Norig, svOrig; reflexivity.
    }
    assert (Hreplay : step (qstate_min, M) (Tau p)
      (qstate_min', insert M p
        (subst_expression_in_process 0 0 (Val (Bool r)) P))
      (proj1_sig (measurement_probability_from_nonzero
        Norig svOrig n r Hnonzero))).
    {
      replace (proj1_sig (measurement_probability_from_nonzero
        Norig svOrig n r Hnonzero)) with (proj1_sig piMin)
        by exact HprobEqual.
      unfold qstate_min, qstate_min', piMin, qmBase, Nbase, svMin.
      simpl.
      eapply Meas with (p := p) (q := q) (P := P) (s1 := M)
        (q_state1 :=
          existT _ (projT1 qstate_base)
            (exist _ (free_qubit_sufficiency_measurement_vector Nbase nbase r prob) HsvMin))
        (q_state2 := snd (measure_qubit_from_nonzero
          qmBase (proj2_sig (projT1 qstate_base))
          (free_qubit_sufficiency_measurement_vector Nbase nbase r prob) HsvMin
          q p nbase r HlookupMin HlenBase HnonzeroMin))
        (n := nbase) (r := r) (pi :=
          measurement_probability_from_nonzero Nbase
            (free_qubit_sufficiency_measurement_vector Nbase nbase r prob)
            nbase r HnonzeroMin)
        (Hlookup := HlookupMin) (Hlen := HlenBase)
        (Hnonzero := HnonzeroMin).
      - exact H.
      - reflexivity.
    }
    exists qstate_min, qstate_min'; split; [exact Hreplay|].
    split; [exact Hsafe|].
    eapply state_only_contains_qubits_in_context_after_step.
    + exact Hreplay.
    + exact Hguard.
    + exact Htyped.
    + exact Hsafe.
    + exact Htyped'.
  - set (Punit := p_unitary (length lq) U
      (map (fun z => Val (QVal z)) lq) P).
    destruct (free_qubit_sufficiency_process_owned_by_context
      M delta G context p Punit Htyped H)
      as [qstate_min [Hsafe Howned]].
    assert (HlookupList : forall q0, In q0 lq ->
      exists n0, quantum_map_of qstate_min q0 = Some (p, n0)).
    {
      intros q0 Hin.
      assert (Hqfree : In q0 (free_qubits Punit)).
      {
        unfold Punit; simpl; apply in_app_iff; left.
        apply get_qubits_In.
        exists (Val (QVal q0)); split.
        - apply in_map_iff; exists q0; split; [reflexivity|exact Hin].
        - simpl; auto.
      }
      apply Howned; exact Hqfree.
    }
    set (qmMin := proj1_sig (projT1 qstate_min)).
    set (Nmin := length (elems qubit_reference (participant * fin) qmMin)).
    assert (Hincl : incl lq
      (map fst (elems qubit_reference (participant * fin) qmMin))).
    {
      intros q0 Hin.
      destruct (HlookupList q0 Hin) as [n0 Hqlookup].
      apply in_map_iff; exists (q0, (p, n0)); split; [reflexivity|].
      exact (proj2 (proj2 (specs qubit_reference
        (participant * fin) qmMin) q0 (p, n0)) Hqlookup).
    }
    pose proof (NoDup_incl_length H2 Hincl) as Hkeylen.
    rewrite length_map in Hkeylen.
    assert (Hbound : length lq <= Nmin).
    { unfold Nmin, qmMin; exact Hkeylen. }
    assert (Hpositive : 0 < Nmin) by lia.
    assert (HlookupAny : forall q0, In q0 lq ->
      exists value, qmMin q0 = Some value).
    {
      intros q0 Hin.
      destruct (HlookupList q0 Hin) as [n0 Hqlookup].
      exists (p, n0); exact Hqlookup.
    }
    destruct (apply_unitary_some_of_lookups
      qmMin (proj2_sig (projT1 qstate_min))
      (proj1_sig (projT2 qstate_min)) (proj2_sig (projT2 qstate_min))
      (length lq) U lq eq_refl Hdim H2 Hpositive Hbound
      HlookupAny) as [qstate_min' Happly].
    assert (Hreplay : step (qstate_min, M) (Tau p)
      (qstate_min', insert M p P) 1).
    {
      unfold Punit, qmMin, Nmin in *.
      eapply Unitary with (dim := length lq) (p := p) (U := U)
        (lq := lq) (P := P) (s1 := M) (q_state1 := qstate_min)
        (q_state2 := qstate_min') (Hlen := eq_refl) (Hdim := Hdim).
      - exact H.
      - exact Happly.
      - exact H2.
      - apply Forall_forall; intros q0 Hin.
        destruct (HlookupList q0 Hin) as [n0 Hqlookup].
        exists n0; exact Hqlookup.
    }
    exists qstate_min, qstate_min'; split; [exact Hreplay|].
    split; [exact Hsafe|].
    eapply state_only_contains_qubits_in_context_after_step.
    + exact Hreplay.
    + exact Hguard.
    + exact Htyped.
    + exact Hsafe.
    + exact Htyped'.
  - pose proof (typecheck_session_unfoldM delta G context M M1' H Htyped)
      as HtypedInner.
    pose proof (cguarded_session_unfoldM_local M M1' H Hguard)
      as HguardInner.
    destruct (IHHstep M1' M' qstate qstate'
      ltac:(reflexivity) ltac:(reflexivity)
      delta G context delta' G' HtypedInner Htyped' HguardInner)
      as [qstate_min [qstate_min' [Hinner [Hsafe Hsafe']]]].
    exists qstate_min, qstate_min'; split.
    + eapply Congr with (M1' := M1'); eauto.
    + split; assumption.
Qed.
