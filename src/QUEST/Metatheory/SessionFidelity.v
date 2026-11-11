From SQIR Require Import SQIR.
Require Import Lia Permutation Reals List.
Require Import Coq.Program.Equality.
Require Import SST.
Require Import QUEST session substitution balanced.
Require Import QUEST.Metatheory.QuantumProperties.
Require Import SubjectReduction.
Require Import Progress.
From Paco Require Import paco.

Lemma nth_default_value_index_lt : forall (A : Type) (default : A)
    (xs : list A) n x,
  nth n xs default = x -> x <> default -> n < Datatypes.length xs.
Proof.
  induction xs as [|a xs IH]; intros [|n] x H Hneq; simpl in H.
  - subst x; contradiction.
  - subst x; contradiction.
  - inversion H; simpl; lia.
  - specialize (IH n x H Hneq); simpl; lia.
Qed.

Lemma typecheck_expression_closed_at_context : forall context e B,
  typecheck_expression context e B ->
  closed_expression_at (Datatypes.length context.1.2) e.
Proof.
  intros context e B Htyped.
  induction Htyped; simpl; try constructor; eauto.
  - unfold in_variable_context in H; simpl in H.
    exact (@nth_default_value_index_lt (option sort) None context.1.2 x
      (Some B) H ltac:(discriminate)).
Qed.

Lemma insert_variable_context_length : forall context B,
  Datatypes.length (insert_into_variable_context context B).1.2 =
  S (Datatypes.length context.1.2).
Proof. intros [[pc vc] qc] B; reflexivity. Qed.

Lemma remove_measured_variable_context_length : forall context e,
  Datatypes.length (remove_measured_expression_from_context context e).1.2 =
  Datatypes.length context.1.2.
Proof.
  intros [[pc vc] qc] [v|x|op args]; simpl; try reflexivity.
  destruct v; simpl; try reflexivity.
  unfold remove_from_variable_context; simpl; apply updn_length.
Qed.

Lemma send_continuation_context_length : forall context B e,
  Datatypes.length
    (match B with
     | Qubit =>
         match e with
         | Val (QVal q) => remove_from_qubit_context context q
         | Var x => remove_from_variable_context context x
         | _ => context
         end
     | _ => context
     end).1.2 = Datatypes.length context.1.2.
Proof.
  intros [[pc vc] qc] B e.
  destruct B; destruct e as [[n|b|q]|x|op args];
    simpl; try reflexivity.
  unfold remove_from_variable_context; simpl; apply updn_length.
Qed.

Lemma SForall2_left_forall : forall A B (R : A -> B -> Prop) (P : A -> Prop)
    xs ys,
  (forall x y, R x y -> P x) ->
  SForall2 R xs ys -> SForall P xs.
Proof.
  intros A B R P xs ys Hproj Hrel.
  induction Hrel; constructor; eauto.
Qed.

Lemma typecheck_process_closed_at_context : forall context P T,
  typecheck_process context P T ->
  variable_closed_process_at (Datatypes.length context.1.2) P.
Proof.
  intros context P T Htyped.
  refine (typecheck_process_deep_ind
    (fun context P T =>
      variable_closed_process_at (Datatypes.length context.1.2) P)
    _ _ _ _ _ _ _ _ _ _ context P T Htyped).
  - intros ctx Proc Ty Hbody IH.
    rewrite insert_variable_context_length in IH.
    simpl in IH.
    exact (closed_newq_at (Datatypes.length ctx.1.2) Proc IH).
  - intros ctx z Proc Ty Hz Hbody IH.
    rewrite insert_variable_context_length in IH.
    rewrite remove_measured_variable_context_length in IH.
    simpl in IH.
    eapply closed_measure_at.
    + exact (typecheck_expression_closed_at_context ctx z Qubit Hz).
    + exact IH.
  - intros ctx n U lz Proc Ty Hlen Hargs Hnd Hbody IH.
    eapply closed_unitary_at.
    + apply Forall_impl_In with
        (P := fun z => typecheck_expression ctx z Qubit).
      * intros z Hin Hz.
        exact (typecheck_expression_closed_at_context ctx z Qubit Hz).
      * exact Hargs.
    + exact IH.
  - intros ctx lz Hargs Hnd.
    apply closed_end_at.
    apply Forall_forall; intros z Hin.
    exact (typecheck_expression_closed_at_context ctx z Qubit
      ((proj1 (Hargs z)) Hin)).
  - intros ctx p e Proc l B Ty Hexpr Hbody IH.
    destruct B; destruct e as [[n|b|q]|x|op args]; simpl in *;
      try solve [inversion Hexpr];
      try rewrite updn_length in IH;
      eapply closed_send_at;
      eauto using typecheck_expression_closed_at_context.
  - intros ctx p lP lBT Hbranches IH.
    eapply closed_recv_at.
    eapply SForall2_left_forall with
      (R := fun P0 BT =>
        variable_closed_process_at
          (Datatypes.length
            (insert_into_variable_context ctx (fst BT)).1.2) P0)
      (ys := lBT) in IH.
    + exact IH.
    + intros P0 BT Hclosed.
      rewrite insert_variable_context_length in Hclosed.
      exact Hclosed.
  - intros ctx e P1 P0 Ty He H1 IH1 H0 IH0.
    eapply closed_ite_at.
    + exact (typecheck_expression_closed_at_context ctx e header.Bool He).
    + exact IH1.
    + exact IH0.
  - intros ctx Proc Ty Hbody IH Honly.
    exact (closed_rec_at (Datatypes.length ctx.1.2) Proc IH).
  - intros ctx qc X lz Ty Hvar Honly Hincl Hargs Hnd.
    constructor.
    apply Forall_forall; intros z Hz.
    eapply typecheck_expression_closed_at_context.
    apply Hargs; exact Hz.
  - intros ctx Proc Ty Ty' Hbody IH Hsub.
    exact IH.
Qed.

Lemma typecheck_session_closed `{good_merge}: forall M delta G qcontext,
  typecheck_session qcontext M delta G -> variable_closed_session M.
Proof.
  intros M delta G qcontext Htyped.
  unfold typecheck_session in Htyped.
  destruct Htyped as [lqc [Hreg [Hbal [Hassoc [Hpart
    [Hlen [Hperm Hprocess]]]]]]].
  intros pt P Hlookup.
  destruct (typecheck_session_component_of_map qcontext M delta lqc Hperm Hlen Hprocess pt P Hlookup)
    as [n [T [qc [Hdelta [Hqc [HdeltaMap HtypedP]]]]]].
  exact (typecheck_process_closed_at_context (nil, nil, qc) P T HtypedP).
Qed.

Definition cguarded_session (M : session) :=
  forall pt P, M pt = Some P -> cguardedP P.

Lemma session_fidelity_initial_state : forall (p : participant) (qcontext : qubit_context),
  exists qstate dummy,
    state_covers_qubits_in_context qcontext qstate /\
    qcontext dummy = None /\
    quantum_map_of qstate dummy <> None /\
    0 < Datatypes.length
      (elems qubit_reference (participant * fin)
        (quantum_map_of qstate)).
Proof.
  intros p qcontext.
  set (qs := map fst (elems qubit_reference unit qcontext)).
  assert (Hnd : NoDup qs).
  { unfold qs; exact (proj1 (specs qubit_reference unit qcontext)). }
  set (fresh := fresh_qubit_reference qs).
  assert (Hndall : NoDup (Datatypes.app qs (Datatypes.cons (proj1_sig fresh) nil))).
  {
    apply NoDup_app.
    - exact Hnd.
    - constructor; [simpl; tauto | constructor].
    - intros q Hin Hfresh.
      simpl in Hfresh; destruct Hfresh as [Heq | Hfalse].
      + subst q; exact (proj2_sig fresh Hin).
      + contradiction.
  }
  set (zst := zero_state_for_qubits p
    (Datatypes.app qs (Datatypes.cons (proj1_sig fresh) nil)) Hndall).
  exists (proj1_sig zst), (proj1_sig fresh).
  split.
  - unfold state_covers_qubits_in_context.
    intros q Hlookup.
    assert (Hin : In q qs).
    {
      unfold qs.
      apply in_map_iff.
      exists (q, tt); split; [reflexivity |].
      exact (proj2 (proj2 (specs qubit_reference unit qcontext) q tt) Hlookup).
    }
    destruct (zero_state_for_qubits_owner_lookup p
      (Datatypes.app qs (Datatypes.cons (proj1_sig fresh) nil)) Hndall q) as [n Howner].
    + apply in_or_app; left; exact Hin.
    + change (quantum_map_of (proj1_sig zst) q <> None).
      unfold zst in Howner |- *; simpl in Howner.
      rewrite Howner; discriminate.
  - split.
    + destruct (qcontext (proj1_sig fresh)) as [u|] eqn:Hlookup.
      * destruct u.
        assert (Hin : In (proj1_sig fresh) qs).
        {
          unfold qs.
          apply in_map_iff.
          exists (proj1_sig fresh, tt); split; [reflexivity |].
          exact (proj2 (proj2 (specs qubit_reference unit qcontext)
            (proj1_sig fresh) tt) Hlookup).
        }
        exfalso; exact (proj2_sig fresh Hin).
      * reflexivity.
    + split.
      * destruct (zero_state_for_qubits_owner_lookup p
        (Datatypes.app qs (Datatypes.cons (proj1_sig fresh) nil)) Hndall
        (proj1_sig fresh)) as [n Howner].
        -- apply in_or_app; right; simpl; left; reflexivity.
        -- change (quantum_map_of (proj1_sig zst) (proj1_sig fresh) <> None).
           unfold zst in Howner |- *; simpl in Howner.
           rewrite Howner; discriminate.
      * pose proof (zero_state_for_qubits_length p
        (Datatypes.app qs (Datatypes.cons (proj1_sig fresh) nil)) Hndall) as Hlen.
        unfold zst.
        rewrite length_app in Hlen; simpl in Hlen; lia.
Qed.

Fixpoint zero_state_for_owned_qubits
    (owned : list (participant * qubit_reference))
    (Hnd : NoDup (map snd owned)) {struct owned} :
    {qstate : quantum_state |
      map fst (elems qubit_reference (participant * fin) (quantum_map_of qstate)) =
        rev (map snd owned) /\
      forall p q, In (p, q) owned ->
        exists n, quantum_map_of qstate q = Some (p, n)}.
Proof.
  destruct owned as [|[p q] owned].
  - exists empty_quantum_state; split; [reflexivity |].
    intros p q Hin; simpl in Hin; contradiction.
  - simpl in Hnd.
    pose proof (proj1 (NoDup_cons_iff q (map snd owned)) Hnd) as Hndparts.
    pose proof (proj1 Hndparts) as Hnot.
    pose proof (proj2 Hndparts) as Hndtail.
    pose (tail := zero_state_for_owned_qubits owned Hndtail).
    destruct (proj2_sig tail) as [Hkeys Howners].
    assert (Hfresh : ~ In q
      (map fst (elems qubit_reference (participant * fin)
        (quantum_map_of (proj1_sig tail))))).
    {
      intro Hin.
      apply Hnot.
      rewrite Hkeys in Hin.
      apply in_rev_elim; exact Hin.
    }
    pose (qstate := add_new_qubit_for_progress (proj1_sig tail) p q Hfresh).
    exists qstate; split.
    + unfold qstate, add_new_qubit_for_progress.
      rewrite add_new_qubit_keys_append.
      rewrite Hkeys.
      simpl; reflexivity.
    + intros p' q' Hin.
      simpl in Hin; destruct Hin as [Heq | Hin].
      * inversion Heq; subst p' q'.
        exists (Datatypes.length (elems qubit_reference (participant * fin)
          (quantum_map_of (proj1_sig tail)))).
        exact (add_new_qubit_lookup (proj1_sig tail) p q Hfresh).
      * destruct (Howners p' q' Hin) as [n Hlookup].
        assert (Hneq : q' <> q).
        {
          intro Heq; subst q'.
          apply Hnot.
          exact (in_map snd owned (p', q) Hin).
        }
        exists n.
        eapply add_new_qubit_preserves_lookup; eauto.
Defined.

Lemma zero_owned_state_with_dummy : forall (p : participant)
    (owned : list (participant * qubit_reference)),
  NoDup (map snd owned) ->
  exists qstate dummy,
    (forall owner q, In (owner, q) owned ->
      exists n, quantum_map_of qstate q = Some (owner, n)) /\
    ~ In dummy (map snd owned) /\
    (exists n, quantum_map_of qstate dummy = Some (p, n)) /\
    0 < Datatypes.length
      (elems qubit_reference (participant * fin) (quantum_map_of qstate)).
Proof.
  intros p owned Hnd.
  set (fresh := fresh_qubit_reference (map snd owned)).
  assert (Hndall : NoDup (map snd
    (Datatypes.app owned (Datatypes.cons (p, proj1_sig fresh) nil)))).
  {
    rewrite map_app; simpl.
    apply NoDup_app.
    - exact Hnd.
    - constructor; [simpl; tauto | constructor].
    - intros q Hin Hfresh.
      simpl in Hfresh; destruct Hfresh as [Heq | Hfalse].
      + subst q; exact (proj2_sig fresh Hin).
      + contradiction.
  }
  set (zst := zero_state_for_owned_qubits
    (Datatypes.app owned (Datatypes.cons (p, proj1_sig fresh) nil)) Hndall).
  exists (proj1_sig zst), (proj1_sig fresh).
  pose proof (proj2_sig zst) as [Hkeys Howners].
  split.
  - intros owner q Hin.
    apply Howners.
    apply in_app_iff; left; exact Hin.
  - split.
    + exact (proj2_sig fresh).
    + split.
      * apply Howners.
        apply in_app_iff; right; simpl; auto.
      * pose proof (f_equal (@Datatypes.length qubit_reference) Hkeys) as Hlen.
        rewrite length_map in Hlen.
        rewrite length_rev in Hlen.
        rewrite length_map, length_app in Hlen.
        simpl in Hlen; lia.
Qed.

Definition state_owner_for_qubit (p q : participant)
    (qcontextP qcontextQ : qubit_context) (qubit : qubit_reference) :=
  match qcontextP qubit with
  | Some _ => p
  | None => match qcontextQ qubit with Some _ => q | None => p end
  end.

Inductive expression_uses_qubit : expression -> qubit_reference -> Prop :=
| euq_value : forall q,
    expression_uses_qubit (Val (QVal q)) q
| euq_operator : forall op args e q,
    In e args -> expression_uses_qubit e q ->
    expression_uses_qubit (Op op args) q.

Inductive process_uses_qubit : process -> qubit_reference -> Prop :=
| puq_end : forall lz e q,
    In e lz -> expression_uses_qubit e q ->
    process_uses_qubit (p_end lz) q
| puq_send_expr : forall p l e P q,
    expression_uses_qubit e q ->
    process_uses_qubit (p_send p l e P) q
| puq_send_cont : forall p l e P q,
    process_uses_qubit P q ->
    process_uses_qubit (p_send p l e P) q
| puq_recv : forall p lP n P q,
    onth n lP = Some P -> process_uses_qubit P q ->
    process_uses_qubit (p_recv p lP) q
| puq_ite_expr : forall e P1 P0 q,
    expression_uses_qubit e q ->
    process_uses_qubit (p_ite e P1 P0) q
| puq_ite_then : forall e P1 P0 q,
    process_uses_qubit P1 q ->
    process_uses_qubit (p_ite e P1 P0) q
| puq_ite_else : forall e P1 P0 q,
    process_uses_qubit P0 q ->
    process_uses_qubit (p_ite e P1 P0) q
| puq_newq : forall P q,
    process_uses_qubit P q -> process_uses_qubit (p_newq P) q
| puq_unitary_expr : forall n U lz P e q,
    In e lz -> expression_uses_qubit e q ->
    process_uses_qubit (p_unitary n U lz P) q
| puq_unitary_cont : forall n U lz P q,
    process_uses_qubit P q ->
    process_uses_qubit (p_unitary n U lz P) q
| puq_measure_expr : forall z P q,
    expression_uses_qubit z q ->
    process_uses_qubit (p_measure z P) q
| puq_measure_cont : forall z P q,
    process_uses_qubit P q ->
    process_uses_qubit (p_measure z P) q
| puq_rec : forall P q,
    process_uses_qubit P q -> process_uses_qubit (p_rec P) q
| puq_var : forall n lz e q,
    In e lz -> expression_uses_qubit e q ->
    process_uses_qubit (p_var n lz) q.

Lemma expression_uses_qubit_in_context : forall context e B q,
  typecheck_expression context e B ->
  expression_uses_qubit e q ->
  context.2 q = Some tt.
Proof.
  intros context e B q Htyped.
  induction Htyped; intros Huses; inversion Huses; subst; simpl in *;
    try contradiction; try assumption.
  all: match goal with
  | [H : expression_uses_qubit (Op _ _) _ |- _] => inversion H; subst
  end.
  all: match goal with
  | [H : In _ (_ :: _ :: nil) |- _] => simpl in H; destruct H as [H|[H|H]]; [subst; eauto|subst; eauto|contradiction]
  | [H : In _ (_ :: nil) |- _] => simpl in H; destruct H as [H|H]; [subst; eauto|contradiction]
  end.
Qed.

Lemma qubit_context_lookup_after_measure : forall context z q,
  typecheck_expression context z Qubit ->
  (remove_measured_expression_from_context context z).2 q = Some tt ->
  context.2 q = Some tt.
Proof.
  intros context z q Htyped Hlookup.
  destruct z as [[n|b|q0]|x|op args]; simpl in Htyped, Hlookup.
  - inversion Htyped.
  - inversion Htyped.
  - apply delete_Some in Hlookup; exact (proj2 Hlookup).
  - exact Hlookup.
  - inversion Htyped.
Qed.

Lemma qubit_context_lookup_after_send : forall context B e q,
  typecheck_expression context e B ->
  (match B with
   | Qubit =>
       match e with
       | Var x => remove_from_variable_context context x
       | Val (QVal q0) => remove_from_qubit_context context q0
       | _ => context
       end
   | _ => context
   end).2 q = Some tt ->
  context.2 q = Some tt.
Proof.
  intros context B e q Htyped Hlookup.
  destruct B; simpl in Hlookup; try exact Hlookup.
  destruct e as [[n|b|q0]|x|op args]; simpl in Htyped, Hlookup.
  - inversion Htyped.
  - inversion Htyped.
  - apply delete_Some in Hlookup; exact (proj2 Hlookup).
  - exact Hlookup.
  - inversion Htyped.
Qed.

Lemma typecheck_process_uses_qubit_in_context : forall context P T q,
  typecheck_process context P T ->
  process_uses_qubit P q ->
  context.2 q = Some tt.
Proof.
  intros context P T q Htyped.
  eapply (typecheck_process_deep_ind
    (fun context P T => process_uses_qubit P q -> context.2 q = Some tt)).
  - intros ctx P0 TT Hbody IH Huses.
    inversion Huses; subst; eapply IH; eassumption.
  - intros ctx z P0 TT Hz Hbody IH Huses.
    inversion Huses; subst.
    + eapply expression_uses_qubit_in_context; eassumption.
    + eapply qubit_context_lookup_after_measure; [exact Hz |].
      apply IH; assumption.
  - intros ctx n U lz P0 TT Hlen Hfor Hnd Hbody IH Huses.
    inversion Huses; subst.
    + rewrite Forall_forall in Hfor.
      eapply expression_uses_qubit_in_context with (B := Qubit);
        [apply Hfor; eassumption | eassumption].
    + apply IH; assumption.
  - intros ctx lz Hall Hnd Huses.
    inversion Huses; subst.
    eapply expression_uses_qubit_in_context with (B := Qubit);
      [apply (proj1 (Hall e)); assumption | assumption].
  - intros ctx pt e P0 l B TT Hexpr Hbody IH Huses.
    inversion Huses; subst.
    + eapply expression_uses_qubit_in_context; eassumption.
    + destruct B; simpl in IH |- *; try (apply IH; assumption).
      destruct e as [[n|b|q0]|x|op args]; simpl in Hexpr, IH;
        try solve [inversion Hexpr].
      * destruct (qr_dec q0 q) as [Heq | Hneq].
        -- subst q0.
           match goal with
           | Hchild : process_uses_qubit P0 q |- _ =>
               pose proof (IH Hchild) as Hbad
           end.
           destruct (qr_dec q q); simpl in Hbad; discriminate.
        -- simpl in IH.
           match goal with
           | Hchild : process_uses_qubit P0 q |- _ => apply (IH Hchild)
           end.
      * match goal with
        | Hchild : process_uses_qubit P0 q |- _ => apply (IH Hchild)
        end.
  - intros ctx pt lP lBT Hbranches IHbranches Huses.
    inversion Huses; subst.
    match goal with
    | Hnth : onth ?idx ?plist = Some ?branch,
      Hchild : process_uses_qubit ?branch q |- _ =>
        destruct (SForall2_onth_l idx plist lBT _ branch Hbranches Hnth)
          as [BT [HBT HbranchTyped]];
        destruct (SForall2_onth_l idx plist lBT _ branch IHbranches Hnth)
          as [BT' [HBT' HbranchIH]];
        apply HbranchIH; exact Hchild
    end.
  - intros ctx e P1 P0 TT Hexpr Htyped1 IH1 Htyped0 IH0 Huses.
    inversion Huses; subst.
    + eapply expression_uses_qubit_in_context; eassumption.
    + apply IH1; assumption.
    + apply IH0; assumption.
  - intros ctx P0 TT Hbody IH Honly Huses.
    inversion Huses; subst; apply IH; assumption.
  - intros ctx qcontext X lz TT Hlookup Honly Hincluded Hargs Hnd Huses.
    inversion Huses; subst.
    eapply expression_uses_qubit_in_context.
    + match goal with
      | Hin : In ?expr lz |- _ => exact (proj1 (Hargs expr) Hin)
      end.
    + eassumption.
  - intros ctx P0 TT TT' Hbody IH Hsub Huses.
    apply IH; assumption.
  - exact Htyped.
Qed.

Lemma session_fidelity_initial_state_for_pair : forall
    (p q : participant) (qcontext qcontextP qcontextQ : qubit_context),
  included qcontextP qcontext ->
  included qcontextQ qcontext ->
  (forall qubit, qcontextP qubit <> None -> qcontextQ qubit = None) ->
  exists qstate,
    state_only_contains_qubits_in_context qcontext qstate /\
    (forall qubit, qcontextP qubit = Some tt ->
      exists n, quantum_map_of qstate qubit = Some (p, n)) /\
    (forall qubit, qcontextQ qubit = Some tt ->
      exists n, quantum_map_of qstate qubit = Some (q, n)).
Proof.
  intros p q qcontext qcontextP qcontextQ HincludeP HincludeQ Hdisjoint.
  set (keys := map fst (elems qubit_reference unit qcontext)).
  set (owned := map
    (fun qubit => (state_owner_for_qubit p q qcontextP qcontextQ qubit, qubit)) keys).
  assert (HownedKeys : map snd owned = keys).
  {
    unfold owned.
    rewrite map_map; simpl; apply map_id.
  }
  assert (Hnd : NoDup (map snd owned)).
  { rewrite HownedKeys; unfold keys; exact (proj1 (specs qubit_reference unit qcontext)). }
  pose (zst := zero_state_for_owned_qubits owned Hnd).
  exists (proj1_sig zst).
  pose proof (proj2_sig zst) as [Hkeys Howners].
  split.
  - unfold state_only_contains_qubits_in_context.
    intros qubit; split.
    + intro Hlookup.
      assert (HinKeys : In qubit keys).
      {
        unfold keys; apply in_map_iff.
        exists (qubit, tt); split; [reflexivity |].
        exact (proj2 (proj2 (specs qubit_reference unit qcontext)
          qubit tt) Hlookup).
      }
      assert (HinOwned : In
          (state_owner_for_qubit p q qcontextP qcontextQ qubit, qubit) owned).
      {
        unfold owned; apply in_map_iff; exists qubit; split; [reflexivity |].
        exact HinKeys.
      }
      destruct (Howners _ _ HinOwned) as [n HstateLookup].
      change (quantum_map_of (proj1_sig zst) qubit <> None).
      rewrite HstateLookup; discriminate.
    + intro HstateLookup.
      destruct (quantum_map_of (proj1_sig zst) qubit)
        as [[owner n]|] eqn:Hlookup; [|contradiction].
      assert (HinStateKeys : In qubit
          (map fst (elems qubit_reference (participant * fin)
            (quantum_map_of (proj1_sig zst))))).
      {
        apply in_map_iff; exists (qubit, (owner, n)); split.
        - reflexivity.
        - exact (proj2 (proj2 (specs qubit_reference
            (participant * fin) (quantum_map_of (proj1_sig zst)))
            qubit (owner, n)) Hlookup).
      }
      rewrite Hkeys in HinStateKeys.
      apply in_rev_elim in HinStateKeys.
      rewrite HownedKeys in HinStateKeys.
      assert (HinContextKeys : In qubit
          (map fst (elems qubit_reference unit qcontext))).
      { unfold keys; exact HinStateKeys. }
      apply in_map_iff in HinContextKeys as [[q0 u] [Heq HinContext]].
      simpl in Heq; subst q0.
      destruct u.
      apply (proj1 (proj2 (specs qubit_reference unit qcontext)
        qubit tt)); exact HinContext.
  - split.
    + intros qubit Hlookup.
      assert (HinKeys : In qubit keys).
      {
        unfold keys; apply in_map_iff.
        exists (qubit, tt); split; [reflexivity |].
        exact (proj2 (proj2 (specs qubit_reference unit qcontext)
          qubit tt) (HincludeP qubit tt Hlookup)).
      }
      assert (HinOwned : In (p, qubit) owned).
      {
        unfold owned; apply in_map_iff; exists qubit; split.
        - simpl; unfold state_owner_for_qubit; rewrite Hlookup; reflexivity.
        - exact HinKeys.
      }
      eapply Howners; exact HinOwned.
    + intros qubit Hlookup.
      assert (HinKeys : In qubit keys).
      {
        unfold keys; apply in_map_iff.
        exists (qubit, tt); split; [reflexivity |].
        exact (proj2 (proj2 (specs qubit_reference unit qcontext)
          qubit tt) (HincludeQ qubit tt Hlookup)).
      }
      assert (HqPnone : qcontextP qubit = None).
      {
        destruct (qcontextP qubit) as [u|] eqn:Hp; [|reflexivity].
        destruct u.
        pose proof (Hdisjoint qubit ltac:(rewrite Hp; discriminate)) as Hnone.
        rewrite Hlookup in Hnone; discriminate.
      }
      assert (HinOwned : In (q, qubit) owned).
      {
        unfold owned; apply in_map_iff; exists qubit; split.
        - simpl; unfold state_owner_for_qubit; rewrite HqPnone, Hlookup; reflexivity.
        - exact HinKeys.
      }
      eapply Howners; exact HinOwned.
Qed.

Lemma session_fidelity_initial_state_for_typed_pair : forall
    (p q : participant) (qcontext qcontextP qcontextQ : qubit_context)
    P Q Tp Tq,
  included qcontextP qcontext ->
  included qcontextQ qcontext ->
  (forall qubit, qcontextP qubit <> None -> qcontextQ qubit = None) ->
  typecheck_process (nil, nil, qcontextP) P Tp ->
  typecheck_process (nil, nil, qcontextQ) Q Tq ->
  exists qstate,
    state_only_contains_qubits_in_context qcontext qstate /\
    (forall qubit, In qubit (free_qubits P) ->
      exists n, quantum_map_of qstate qubit = Some (p, n)) /\
    (forall qubit, In qubit (free_qubits Q) ->
      exists n, quantum_map_of qstate qubit = Some (q, n)).
Proof.
  intros p q qcontext qcontextP qcontextQ P Q Tp Tq
    HincludeP HincludeQ Hdisjoint HtypedP HtypedQ.
  destruct (session_fidelity_initial_state_for_pair p q qcontext
    qcontextP qcontextQ HincludeP HincludeQ Hdisjoint)
    as [qstate [Honly [HownerP HownerQ]]].
  exists qstate; split; [exact Honly |].
  split.
  - intros qubit Hin.
    pose proof (typecheck_process_free_qubits P (nil, nil, qcontextP)
      Tp HtypedP qubit Hin) as Hlocal.
    unfold in_qubit_context in Hlocal; simpl in Hlocal.
    eapply HownerP; exact Hlocal.
  - intros qubit Hin.
    pose proof (typecheck_process_free_qubits Q (nil, nil, qcontextQ)
      Tq HtypedQ qubit Hin) as Hlocal.
    unfold in_qubit_context in Hlocal; simpl in Hlocal.
    eapply HownerQ; exact Hlocal.
Qed.

Lemma session_fidelity_initial_state_from_session `{good_merge} : forall
    M delta G qcontext p q P Q,
  typecheck_session qcontext M delta G ->
  M p = Some P -> M q = Some Q -> p <> q ->
  exists qstate,
    state_only_contains_qubits_in_context qcontext qstate /\
    (forall qubit, In qubit (free_qubits P) ->
      exists n, quantum_map_of qstate qubit = Some (p, n)) /\
    (forall qubit, In qubit (free_qubits Q) ->
      exists n, quantum_map_of qstate qubit = Some (q, n)).
Proof.
  intros M delta G qcontext p q P Q Htyped HP HQ Hneq.
  unfold typecheck_session in Htyped.
  destruct Htyped as [lqc [Hreg [Hbalanced [Hassoc [Hpartition
    [Hlength [Hperm HtypedProcesses]]]]]]].
  destruct (typecheck_session_component_of_map qcontext M delta lqc Hperm Hlength HtypedProcesses p P HP)
    as [np [Tp [qcP [HdeltaP [HqcP [HdeltaPmap HtypedP]]]]]].
  destruct (typecheck_session_component_of_map qcontext M delta lqc Hperm Hlength HtypedProcesses q Q HQ)
    as [nq [Tq [qcQ [HdeltaQ [HqcQ [HdeltaQmap HtypedQ]]]]]].
  assert (Hnpnq : np <> nq).
  {
    intro Heq; subst nq.
    rewrite HdeltaP in HdeltaQ; inversion HdeltaQ; congruence.
  }
  pose proof (partition_component_included qcontext lqc np qcP
    Hpartition HqcP) as HincludeP.
  pose proof (partition_component_included qcontext lqc nq qcQ
    Hpartition HqcQ) as HincludeQ.
  assert (Hdisjoint : forall qubit,
      qcP qubit <> None -> qcQ qubit = None).
  {
    intros qubit Hpresent.
    unfold FMap.partition in Hpartition.
    destruct Hpartition as [_ Hpairwise].
    destruct (Hpairwise np nq qcP qcQ Hnpnq HqcP HqcQ qubit)
      as [Hforward _].
    apply Hforward; exact Hpresent.
  }
  destruct (session_fidelity_initial_state_for_typed_pair p q qcontext
    qcP qcQ P Q Tp Tq HincludeP HincludeQ Hdisjoint HtypedP HtypedQ)
    as [qstate [Hstateonly [HownerP HownerQ]]].
  exists qstate.
  split; [exact Hstateonly |].
  split; assumption.
Qed.

Lemma cguarded_session_unfoldM : forall M M',
  unfoldM M M' -> cguarded_session M -> cguarded_session M'.
Proof.
  intros M M' Hunfold Hguard pt P' Hlookup.
  destruct (Hunfold pt) as [[_ Hnone'] | [P [Q [Hsrc [Hdst Hpre]]]]].
  - rewrite Hnone' in Hlookup; discriminate.
  - eapply cguardedP_after_subst.
    + eapply Hguard; exact Hsrc.
    + rewrite Hdst in Hlookup; inversion Hlookup; subst P'; exact Hpre.
Qed.

Lemma cguardedP_newq_body : forall P,
  cguardedP (p_newq P) -> cguardedP P.
Proof.
  intros P [Hclosed Hguard].
  split.
  - inversion Hclosed; subst; assumption.
  - inversion Hguard; subst; assumption.
Qed.

Lemma cguardedP_unitary_body : forall n U lz P,
  cguardedP (p_unitary n U lz P) -> cguardedP P.
Proof.
  intros n U lz P [Hclosed Hguard].
  split.
  - inversion Hclosed; subst; assumption.
  - inversion Hguard; subst; assumption.
Qed.

Lemma cguardedP_measure_body : forall z P,
  cguardedP (p_measure z P) -> cguardedP P.
Proof.
  intros z P [Hclosed Hguard].
  split.
  - inversion Hclosed; subst; assumption.
  - inversion Hguard; subst; assumption.
Qed.

Inductive process_head_uses_qubit : process_head_view -> qubit_reference -> Prop :=
| phu_unitary : forall n U lz q,
    In (Val (QVal q)) lz ->
    process_head_uses_qubit (ph_unitary n U lz) q
| phu_measure : forall q,
    process_head_uses_qubit (ph_measure (Val (QVal q))) q.

Lemma process_head_qubit_has_typed_context : forall P h T q,
  process_head_type P h T ->
  process_head_uses_qubit h q ->
  exists context : typing_context, context.2 q = Some tt.
Proof.
  intros P h T q Hhead.
  induction Hhead; intros Huses; try solve [inversion Huses].
  - exact (IHHhead Huses).
  - inversion Huses; subst.
    rewrite Forall_forall in H0.
    pose proof (H0 (Val (QVal q)) H6) as Htyped.
    inversion Htyped; subst; eauto.
  - inversion Huses; subst.
    inversion H; subst.
    eexists; eassumption.
  - exact (IHHhead Huses).
Qed.

Lemma expression_uses_qubit_get_qubits : forall e q,
  expression_uses_qubit e q -> In q (get_qubits_expression e).
Proof.
  intros e q Huses; induction Huses; simpl.
  - simpl; auto.
  - apply in_flat_map; eauto.
Qed.

Lemma process_head_uses_qubit_free : forall Pu h q,
  process_root_view Pu = Some h ->
  process_head_uses_qubit h q ->
  In q (free_qubits Pu).
Proof.
  intros Pu h q Hroot Huses.
  inversion Huses; subst.
  - destruct Pu; simpl in Hroot; try discriminate.
    inversion Hroot; subst; simpl.
    apply in_or_app; left; unfold get_qubits.
    apply in_flat_map.
    exists (Val (QVal q)); split; [assumption | simpl; auto].
  - destruct Pu; simpl in Hroot; try discriminate.
    inversion Hroot; subst; simpl.
    left; reflexivity.
Qed.

Lemma free_qubits_precong : forall P P',
  precongP P P' -> forall q,
  In q (free_qubits P') -> In q (free_qubits P).
Proof.
  intros P P' Hpre; induction Hpre; intros q Hin.
  - exact Hin.
  - simpl.
    eapply free_qubits_substitutionP_rec.
    apply IHHpre; exact Hin.
  - apply IHHpre1; apply IHHpre2; exact Hin.
Qed.

Lemma free_qubits_unravel : forall P,
  cguardedP P -> forall q,
  In q (free_qubits (unravelP P)) -> In q (free_qubits P).
Proof.
  intros P Hguard.
  destruct (cguardedP_unfolds P Hguard) as [_ [Hpre _]].
  apply free_qubits_precong; exact Hpre.
Qed.

Lemma get_qubits_expression_substitution : forall e0 n d replacement q,
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
    destruct IHs as [Hold | Hnew].
    + left; apply in_flat_map; exists eOrig; split; assumption.
    + right; exact Hnew.
Qed.

Lemma get_qubits_list_substitution : forall l n d replacement q,
  In q (get_qubits (map (subst_expression n d replacement) l)) ->
  In q (get_qubits l) \/ In q (get_qubits_expression replacement).
Proof.
  intros l n d replacement q Hin.
  apply get_qubits_In in Hin as [e' [HinMap Hq]].
  apply in_map_iff in HinMap as [e [Heq HinOld]].
  rewrite <- Heq in Hq.
  destruct (get_qubits_expression_substitution e n d replacement q Hq)
    as [Hold | Hnew].
  - left; apply get_qubits_In; exists e; split; assumption.
  - right; exact Hnew.
Qed.

Lemma free_qubits_process_substitution : forall P,
  (forall n d replacement q,
    In q (free_qubits (subst_expression_in_process n d replacement P)) ->
    In q (free_qubits P) \/ In q (get_qubits_expression replacement)).
Proof.
  eapply (process_deep_ind
    (fun P => forall n d replacement q,
      In q (free_qubits (subst_expression_in_process n d replacement P)) ->
      In q (free_qubits P) \/ In q (get_qubits_expression replacement))).
  - intros x lz n d replacement q Hin; simpl in Hin.
    exact (get_qubits_list_substitution lz n d replacement q Hin).
  - intros lz n d replacement q Hin.
    simpl in Hin.
    exact (get_qubits_list_substitution lz n d replacement q Hin).
  - intros pt l e P0 IH n d replacement q Hin.
    simpl in Hin; apply in_app_iff in Hin as [He|HP].
    + destruct (get_qubits_list_substitution (e :: nil) n d replacement q He)
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
      destruct (get_qubits_expression_substitution e n d replacement q He)
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
    + destruct (get_qubits_list_substitution lz n d replacement q Hlz)
        as [Hold|Hnew].
      * left; simpl; apply in_app_iff; left; exact Hold.
      * right; exact Hnew.
    + destruct (IH n d replacement q HP) as [Hold|Hnew].
      * left; simpl; apply in_app_iff; right; exact Hold.
      * right; exact Hnew.
  - intros z P0 IH n d replacement q Hin.
    simpl in Hin; apply in_app_iff in Hin as [Hz|HP].
    + destruct (get_qubits_list_substitution (z :: nil) n d replacement q Hz)
        as [Hold|Hnew].
      * left; simpl; apply in_app_iff; left; exact Hold.
      * right; exact Hnew.
    + destruct (IH (S n) (S d) replacement q HP) as [Hold|Hnew].
      * left; simpl; apply in_app_iff; right; exact Hold.
      * right; exact Hnew.
Qed.

(* Number of internal process constructors on the path to the next
   communication.  Continuations below a send/receive do not contribute. *)
Fixpoint internal_prefix_height (P : process) : nat :=
  match P with
  | p_var _ _ | p_end _ | p_send _ _ _ _ | p_recv _ _ => 0
  | p_ite _ P1 P0 => S (Nat.max (internal_prefix_height P1)
      (internal_prefix_height P0))
  | p_rec P0 | p_newq P0 | p_unitary _ _ _ P0 | p_measure _ P0 =>
      S (internal_prefix_height P0)
  end.

Lemma internal_prefix_height_expression_substitution : forall P,
  forall n_sub d_sub e_sub,
  internal_prefix_height (subst_expression_in_process n_sub d_sub e_sub P) =
  internal_prefix_height P.
Proof.
  induction P; intros n_sub d_sub e_sub; simpl; try reflexivity.
  - f_equal; apply IHP.
  - f_equal; apply IHP.
  - f_equal; apply IHP.
  - f_equal; apply IHP.
  - rewrite IHP1, IHP2; reflexivity.
Qed.

Lemma nth_boollis_self : forall n,
  nth n (boollis n) false = true.
Proof.
  induction n; simpl; [reflexivity | exact IHn].
Qed.

Lemma nth_bmerge_false_inv : forall xs ys n,
  nth n (bmerge xs ys) false = false ->
  nth n xs false = false /\ nth n ys false = false.
Proof.
  intros xs ys n; revert xs ys; induction n as [|n IH]; intros xs ys H.
  - destruct xs as [|x xt], ys as [|y yt]; simpl in *.
    + auto.
    + split; [reflexivity | exact H].
    + split; [exact H | reflexivity].
    + destruct x, y; simpl in H; try discriminate; split; reflexivity.
  - destruct xs as [|x xt], ys as [|y yt]; simpl in *.
    + auto.
    + split; [reflexivity | exact H].
    + split; [exact H | reflexivity].
    + destruct (IH xt yt H) as [Hx Hy]; split; assumption.
Qed.

Lemma internal_prefix_height_substitution_guarded : forall xs P x0 m0 d0 repl0,
  guardP xs P -> nth x0 xs false = false ->
  internal_prefix_height (substitutionP x0 m0 d0 repl0 P) =
  internal_prefix_height P.
Proof.
  intros xs P.
  revert xs.
  induction P as
    [lz|P0 IHP0|pt lb e P0 IHP0|pt cont|P0 IHP0
    |dim U lz P0 IHP0|z P0 IHP0|e P1 IHP1 P0 IHP0|k];
    intros xs x0 m0 d0 repl0 Hguard Hmask.
  - simpl; reflexivity.
  - inversion Hguard; subst; simpl.
    + f_equal. eapply IHP0; [eassumption | reflexivity].
    + f_equal. eapply IHP0; [eassumption | simpl; exact Hmask].
  - simpl; reflexivity.
  - simpl; reflexivity.
  - inversion Hguard; subst; simpl.
    f_equal; eapply IHP0; eassumption.
  - inversion Hguard; subst; simpl.
    f_equal; eapply IHP0; eassumption.
  - inversion Hguard; subst; simpl.
    f_equal; eapply IHP0; eassumption.
  - inversion Hguard; subst; simpl.
    destruct (nth_bmerge_false_inv xs0 ys x0 Hmask) as [Hmask1 Hmask0].
    f_equal.
    rewrite (IHP1 xs0 x0 m0 d0 repl0 H2 Hmask1).
    rewrite (IHP0 ys x0 m0 d0 repl0 H4 Hmask0).
    reflexivity.
  - inversion Hguard; subst; simpl.
    unfold substitutionP; simpl.
    destruct (Nat.ltb k x0) eqn:Hlt; [reflexivity |].
    destruct (Nat.eqb k x0) eqn:Heq; [|reflexivity].
    apply Nat.eqb_eq in Heq; subst x0.
    rewrite nth_boollis_self in Hmask; discriminate.
Qed.

Lemma internal_prefix_height_unfold_rec : forall P,
  cguardedP (p_rec P) ->
  internal_prefix_height (substitutionP 0 0 0 (p_rec P) P) =
  internal_prefix_height P.
Proof.
  intros P [_ Hguard].
  inversion Hguard; subst; simpl.
  - eapply internal_prefix_height_substitution_guarded; [eassumption | reflexivity].
  - eapply internal_prefix_height_substitution_guarded; [eassumption | reflexivity].
Qed.

Lemma internal_prefix_height_precong : forall P P',
  cguardedP P -> precongP P P' ->
  internal_prefix_height P' <= internal_prefix_height P.
Proof.
  intros P P' Hguard Hpre.
  revert Hguard.
  induction Hpre; intros Hguard.
  - lia.
  - assert (Hguard_sub : cguardedP
        (substitutionP 0 0 0 (p_rec P) P)).
    {
      eapply cguardedP_after_subst; [exact Hguard |].
      apply gttS; apply gttR.
    }
    specialize (IHHpre Hguard_sub).
    pose proof (internal_prefix_height_unfold_rec P Hguard) as Hunfold.
    simpl; lia.
  - pose proof (cguardedP_after_subst P P' Hguard Hpre1) as Hguard_mid.
    specialize (IHHpre1 Hguard).
    specialize (IHHpre2 Hguard_mid).
    lia.
Qed.

Lemma internal_prefix_height_unravel_le : forall P,
  cguardedP P -> internal_prefix_height (unravelP P) <= internal_prefix_height P.
Proof.
  intros P Hguard.
  destruct (cguardedP_unfolds P Hguard) as [_ [Hpre _]].
  eapply internal_prefix_height_precong; eassumption.
Qed.

Lemma internal_head_step_on_state : forall M p Pu h T qstate,
  process_head_type Pu h T ->
  process_head_view_closed h ->
  process_root_view Pu = Some h ->
  is_internal_head_view h ->
  (forall q, process_head_uses_qubit h q ->
    exists n, quantum_map_of qstate q = Some (p, n)) ->
  exists qstate' Pu' pi,
    internal_prefix_height Pu' < internal_prefix_height Pu /\
    step (qstate, insert (KEQ:=participant_dec) M p Pu) (Tau p)
      (qstate', insert (KEQ:=participant_dec)
        (insert (KEQ:=participant_dec) M p Pu) p Pu') pi.
Proof.
  intros M p Pu h T qstate Hhead Hview Hroot Hinternal Havailable.
  destruct h as [lz|q l e|q| |dim U lz|z|e|k]; simpl in Hinternal;
    try contradiction.
  - destruct Pu as [lz0|P0|sp sl e0 P0|sp cont|P0|dim0 U0 lz0 P0
      |z0 P0|e0 P1 P0|k0]; simpl in Hroot; try discriminate.
    inversion Hroot; subst.
    set (fresh := fresh_qubit_reference
      (map fst (elems qubit_reference (participant * fin)
        (quantum_map_of qstate)))).
    pose (qnew := proj1_sig fresh).
    pose (Hfresh := proj2_sig fresh).
    exists (add_new_qubit qstate p qnew Hfresh),
      (subst_expression_in_process 0 0 (Val (QVal qnew)) P0), 1%R.
    split.
    + rewrite internal_prefix_height_expression_substitution; simpl; lia.
    + eapply New with (q := qnew) (Hfresh := Hfresh).
      rewrite insert_eq; reflexivity.
  - destruct Pu as [lz0|P0|sp sl e0 P0|sp cont|P0|dim0 U0 lz0 P0
      |z0 P0|e0 P1 P0|k0]; simpl in Hroot; try discriminate.
    inversion Hroot; subst.
    dependent destruction H1.
    destruct (process_head_type_unitary_info dim U lz P0 T Hhead)
      as [context [Hlen [Htyped Hndexpr]]].
    destruct (evaluate_closed_qubit_list context lz Htyped Hview Hndexpr)
      as [lqs [Hevals [Hmap Hndqs]]].
    assert (Hlookup : forall q0, In q0 lqs ->
        exists v, quantum_map_of qstate q0 = Some v).
    {
      intros q0 Hin.
      assert (Hinlz : In (Val (QVal q0)) lz).
      { rewrite <- Hmap.
        exact (in_map (fun q => Val (QVal q)) lqs q0 Hin). }
      destruct (Havailable q0) as [n Hq].
      { constructor; exact Hinlz. }
      exists (p, n); exact Hq.
    }
    pose proof (f_equal (Datatypes.length (A:=expression)) Hmap) as Hmaplen.
    rewrite length_map in Hmaplen.
    assert (Hqslen : Datatypes.length lqs = dim) by lia.
    pose proof (base_Unitary_dim_positive dim U) as Hdim.
    assert (Hincl : incl lqs
        (map fst (elems qubit_reference (participant * fin)
          (quantum_map_of qstate)))).
    {
      intros q0 Hin.
      destruct (Hlookup q0 Hin) as [v Hq].
      apply in_map_iff.
      exists (q0, v); split; [reflexivity |].
      exact (proj2 (proj2 (specs qubit_reference
        (participant * fin) (quantum_map_of qstate)) q0 v) Hq).
    }
    pose proof (NoDup_incl_length  Hndqs Hincl) as Hkeylen.
    rewrite length_map in Hkeylen.
    assert (Hbound : dim <= Datatypes.length
        (elems qubit_reference (participant * fin) (quantum_map_of qstate))).
    { rewrite <- Hlen, <- Hmaplen; exact Hkeylen. }
    assert (Hpositive : 0 < Datatypes.length
        (elems qubit_reference (participant * fin) (quantum_map_of qstate)))
      by lia.
    destruct (apply_unitary_some_of_lookups
      (quantum_map_of qstate) (proj2_sig (projT1 qstate))
      (proj1_sig (projT2 qstate)) (proj2_sig (projT2 qstate))
      dim U lqs Hqslen Hdim Hndqs Hpositive Hbound Hlookup) as [qstate' Happly].
    exists qstate', P0, 1%R.
    split; [simpl; lia |].
    eapply Unitary with (Hlen := Hqslen) (Hdim := Hdim).
    + rewrite insert_eq; rewrite Hmap; reflexivity.
    + exact Happly.
    + exact Hndqs.
    + apply Forall_forall; intros q0 Hin.
      assert (Hinlz : In (Val (QVal q0)) lz).
      { rewrite <- Hmap.
        exact (in_map (fun q => Val (QVal q)) lqs q0 Hin). }
      destruct (Havailable q0) as [n Hq].
      * constructor; exact Hinlz.
      * exists n; unfold quantum_map_of in Hq; exact Hq.
  - destruct Pu as [lz0|P0|sp sl e0 P0|sp cont|P0|dim0 U0 lz0 P0
      |z0 P0|e0 P1 P0|k0]; simpl in Hroot; try discriminate.
    inversion Hroot; subst.
    destruct (process_head_type_measure_expr z P0 T Hhead)
      as [context Htyped].
    destruct (closed_qubit_expression_literal context z Htyped Hview)
      as [q Hq]; subst z.
    destruct (Havailable q) as [n Hlookup].
    { constructor. }
    assert (Hindex : n < Datatypes.length
        (elems qubit_reference (participant * fin) (quantum_map_of qstate))).
    { eapply quantum_map_lookup_index_lt with (p := p).
      - unfold quantum_map_of; exact (proj2_sig (projT1 qstate)).
      - exact Hlookup. }
    assert (Hpositive : 0 < Datatypes.length
        (elems qubit_reference (participant * fin) (quantum_map_of qstate)))
      by lia.
    destruct (measurement_outcome_nonzero_of_wf
        (quantum_map_of qstate) (proj1_sig (projT2 qstate))
        (proj2_sig (projT2 qstate)) n Hindex) as [r Hnonzero].
    destruct (measure_qubit_from_nonzero
        (quantum_map_of qstate) (proj2_sig (projT1 qstate))
        (proj1_sig (projT2 qstate)) (proj2_sig (projT2 qstate))
        q p n r Hlookup Hpositive Hnonzero) as [pi qstate'] eqn:Hmeasure.
    exists qstate',
        (subst_expression_in_process 0 0 (Val (Primitives.Bool r)) P0), pi!.
    split.
    + rewrite internal_prefix_height_expression_substitution; simpl; lia.
    + eapply Meas with (n := n) (r := r) (pi := pi)
        (q_state2 := qstate') (Hlookup := Hlookup)
        (Hlen := Hpositive) (Hnonzero := Hnonzero).
      * rewrite insert_eq; reflexivity.
      * symmetry; exact Hmeasure.
  - destruct Pu as [lz0|P0|sp sl e0 P0|sp cont|P0|dim0 U0 lz0 P0
      |z0 P0|e0 P1 P0|k0]; simpl in Hroot; try discriminate.
    inversion Hroot; subst.
    destruct (process_head_type_ite_expr e P1 P0 T Hhead)
      as [context Htyped].
    destruct (closed_expression_evaluates context e header.Bool Htyped Hview)
      as [v [Heval Hsort]].
    destruct v as [n|b|q].
    + inversion Hsort.
    + inversion Hsort; subst.
      destruct b.
      * exists qstate, P1, 1%R.
        split; [simpl; lia |].
        eapply If_1.
        -- rewrite insert_eq; reflexivity.
        -- exact Heval.
      * exists qstate, P0, 1%R.
        split; [simpl; lia |].
        eapply If_0.
        -- rewrite insert_eq; reflexivity.
        -- exact Heval.
    + inversion Hsort.
Qed.

Lemma progress_internal_transition_on_state : forall
    (M : session) (p : participant) P h T qstate,
  M p = Some P ->
  cguardedP P ->
  variable_closed_process_at 0 P ->
  process_head_type (unravelP P) h T ->
  process_head_view_closed h ->
  process_root_view (unravelP P) = Some h ->
  is_internal_head_view h ->
  (forall q, process_head_uses_qubit h q ->
    exists n, quantum_map_of qstate q = Some (p, n)) ->
  exists qstate' M' pi P',
    step (qstate, M) (Tau p) (qstate', M') pi /\
    M' p = Some P' /\
    internal_prefix_height P' < internal_prefix_height P.
Proof.
  intros M p P h T qstate Hlookup Hguard Hclosed Hhead Hview Hroot
    Hinternal Havailable.
  destruct (cguardedP_unfolds P Hguard) as [_ [Hpre _]].
  destruct (internal_head_step_on_state M p (unravelP P) h T qstate
    Hhead Hview Hroot Hinternal Havailable)
    as [qstate' [Pu' [pi [Hrank Hstep]]]].
  exists qstate',
    (insert (KEQ:=participant_dec)
      (insert (KEQ:=participant_dec) M p (unravelP P)) p Pu'), pi, Pu'.
  split.
  - eapply step_after_unfold_one; eauto.
  - split.
    + rewrite insert_eq; reflexivity.
    + pose proof (internal_prefix_height_unravel_le P Hguard).
      lia.
Qed.

Definition process_qubits_owned_by (M : session) (qstate : quantum_state)
    (p : participant) : Prop :=
  forall P, M p = Some P -> forall q,
    In q (free_qubits P) ->
    exists n, quantum_map_of qstate q = Some (p, n).

Definition process_qubit_owner_agrees_by (M : session) (qstate : quantum_state)
    (p : participant) : Prop :=
  forall P, M p = Some P -> forall q,
    In q (free_qubits P) -> forall owner n,
    quantum_map_of qstate q = Some (owner, n) -> owner = p.

Lemma process_qubit_owner_agreement_of_owned : forall M qstate p,
  process_qubits_owned_by M qstate p ->
  process_qubit_owner_agrees_by M qstate p.
Proof.
  intros M qstate p Howned P Hmap q Hin owner n Hlookup.
  destruct (Howned P Hmap q Hin) as [n0 Howned_lookup].
  rewrite Howned_lookup in Hlookup.
  inversion Hlookup; reflexivity.
Qed.

Lemma process_qubit_owner_agrees_unfoldM : forall M M' qstate p,
  unfoldM M M' -> process_qubit_owner_agrees_by M qstate p ->
  process_qubit_owner_agrees_by M' qstate p.
Proof.
  intros M M' qstate p Hunfold Hagree P' Hlookup q Hin owner n Hq.
  destruct (Hunfold p) as [[Hnone Hnone'] | [P [P0 [Hsrc [Hdst Hpre]]]]].
  - rewrite Hnone' in Hlookup; discriminate.
  - rewrite Hdst in Hlookup; inversion Hlookup; subst P'.
    eapply Hagree.
    + exact Hsrc.
    + eapply free_qubits_precong; eassumption.
    + exact Hq.
Qed.

Lemma process_qubits_available_from_typed_session `{good_merge} : forall
    M delta G qcontext qstate p P,
  typecheck_session qcontext M delta G ->
  M p = Some P ->
  state_covers_qubits_in_context qcontext qstate ->
  process_qubit_owner_agrees_by M qstate p ->
  process_qubits_owned_by M qstate p.
Proof.
  intros M delta G qcontext qstate p P Htyped Hlookup Hcovers Hagree.
  unfold typecheck_session in Htyped.
  destruct Htyped as [lqc [Hreg [Hbalanced [Hassoc [Hpartition
    [Hlength [Hperm HtypedProcesses]]]]]]].
  destruct (typecheck_session_component_of_map qcontext M delta lqc Hperm Hlength HtypedProcesses p P Hlookup)
    as [np [T [qc [Hdelta [Hqc [HdeltaMap HtypedP]]]]]].
  pose proof (partition_component_included qcontext lqc np qc
    Hpartition Hqc) as Hinclude.
  unfold process_qubits_owned_by.
  intros P0 Hmap q Hin.
  rewrite Hlookup in Hmap; inversion Hmap; subst P0.
  pose proof (typecheck_process_free_qubits P (nil, nil, qc) T HtypedP q Hin)
    as Hlocal.
  unfold in_qubit_context in Hlocal; simpl in Hlocal.
  assert (Hglobal : qcontext q = Some tt) by (eapply Hinclude; exact Hlocal).
  pose proof (Hcovers q Hglobal) as Hpresent.
  destruct (quantum_map_of qstate q) as [[owner n]|] eqn:Hqstate;
    [|contradiction].
  assert (Howner : owner = p) by (eapply Hagree; eauto).
  subst owner; exists n; reflexivity.
Qed.

Lemma process_qubits_available_from_typed_session_context `{good_merge} : forall
    qcontext M delta G qstate p,
  typecheck_session qcontext M delta G ->
  state_covers_qubits_in_context qcontext qstate ->
  process_qubit_owner_agrees_by M qstate p ->
  process_qubits_owned_by M qstate p.
Proof.
  intros qcontext M delta G qstate p Htyped Hcovers Hagree.
  destruct (M p) as [P|] eqn:Hlookup.
  -
    unfold typecheck_session in Htyped.
    destruct Htyped as [lqc [Hreg [Hbalanced [Hassoc [Hpartition
      [Hlength [Hperm HtypedProcesses]]]]]]].
    destruct (typecheck_session_component_of_map
      qcontext M delta lqc Hperm Hlength HtypedProcesses p P Hlookup)
      as [np [T [qc [Hdelta [Hqc [HdeltaMap HtypedP]]]]]].
    pose proof (partition_component_included qcontext lqc np qc
      Hpartition Hqc) as Hinclude.
    unfold process_qubits_owned_by.
    intros P0 Hmap q Hin.
    rewrite Hlookup in Hmap; inversion Hmap; subst P0.
    pose proof (typecheck_process_free_qubits P (nil, nil, qc) T HtypedP q Hin)
      as Hlocal.
    unfold in_qubit_context in Hlocal; simpl in Hlocal.
    assert (Hglobal : qcontext q = Some tt)
      by (eapply Hinclude; exact Hlocal).
    pose proof (Hcovers q Hglobal) as Hpresent.
    destruct (quantum_map_of qstate q) as [[owner n]|] eqn:Hqstate;
      [|contradiction].
    assert (Howner : owner = p) by (eapply Hagree; eauto).
    subst owner; exists n; reflexivity.
  -
    unfold process_qubits_owned_by.
    intros P0 Hmap q Hin.
    rewrite Hlookup in Hmap; discriminate.
Qed.

Lemma process_qubit_owner_agreement_transport : forall
    (M M' : session) qstate qstate' p P,
  process_qubits_owned_by M qstate p ->
  M p = Some P ->
  (forall P', M' p = Some P' -> forall q,
    In q (free_qubits P') -> In q (free_qubits P)) ->
  (forall q owner n, quantum_map_of qstate' q = Some (owner, n) ->
    exists n0, quantum_map_of qstate q = Some (owner, n0)) ->
  process_qubit_owner_agrees_by M' qstate' p.
Proof.
  intros M M' qstate qstate' p P Howned Hsource Hfree Hmap
    P' Htarget q Hin owner n Hlookup.
  pose proof (Hfree P' Htarget q Hin) as Hin_source.
  destruct (Hmap q owner n Hlookup) as [n0 Hlookup_source].
  destruct (Howned P Hsource q Hin_source) as [n1 Howned_source].
  rewrite Howned_source in Hlookup_source.
  inversion Hlookup_source; reflexivity.
Qed.

Lemma process_qubits_owned_by_unfoldM : forall M M' qstate p,
  unfoldM M M' -> process_qubits_owned_by M qstate p ->
  process_qubits_owned_by M' qstate p.
Proof.
  intros M M' qstate p Hunfold Howned P' Hlookup q Hin.
  destruct (Hunfold p) as [[Hnone Hnone'] | [P [P0 [Hsrc [Hdst Hpre]]]]].
  - rewrite Hnone' in Hlookup; discriminate.
  - rewrite Hdst in Hlookup; inversion Hlookup; subst P'.
    eapply Howned; [exact Hsrc |].
    eapply free_qubits_precong; eassumption.
Qed.

Lemma process_qubits_owned_by_transport : forall
    (M M' : session) qstate qstate' p P,
  process_qubits_owned_by M qstate p ->
  M p = Some P ->
  (forall P', M' p = Some P' -> forall q,
    In q (free_qubits P') -> In q (free_qubits P)) ->
  (forall q, In q (free_qubits P) ->
    exists n, quantum_map_of qstate' q = Some (p, n)) ->
  process_qubits_owned_by M' qstate' p.
Proof.
  intros M M' qstate qstate' p P Howned Hsource Hfree Hmap
    P' Htarget q Hin.
  pose proof (Hfree P' Htarget q Hin) as Hin_source.
  destruct (Howned P Hsource q Hin_source) as [n Hold].
  destruct (Hmap q Hin_source) as [n' Htarget_lookup].
  exact (ex_intro _ n' Htarget_lookup).
Qed.

Lemma eval_op_never_qubit : forall op values q,
  eval_op op values <> Some (QVal q).
Proof.
  intros op values q.
  destruct op; destruct values as [|v1 [|v2 [|v3 rest]]];
    simpl; try discriminate.
  all: try destruct v1 as [n1|b1|q1].
  all: try destruct v2 as [n2|b2|q2].
  all: simpl; discriminate.
Qed.

Lemma eval_qubit_value_is_literal : forall e q,
  evaluate_expression e = Some (QVal q) -> e = Val (QVal q).
Proof.
  intros [v|x|op args] q Heval; simpl in Heval.
  - destruct v as [n|b|q0]; simpl in Heval; try discriminate.
    inversion Heval; reflexivity.
  - discriminate.
  - destruct (strip_option (map evaluate_expression args)) as [values|]
      eqn:Hvalues; simpl in Heval; [|discriminate].
    exfalso.
    apply (eval_op_never_qubit op values q); exact Heval.
Qed.

Lemma add_new_qubit_lookup_other : forall qstate p fresh Hfresh q owner n,
  q <> fresh ->
  quantum_map_of (add_new_qubit qstate p fresh Hfresh) q = Some (owner, n) ->
  quantum_map_of qstate q = Some (owner, n).
Proof.
  intros qstate p fresh Hfresh q owner n Hneq Hlookup.
  unfold add_new_qubit, quantum_map_of in *.
  cbn [proj1_sig projT1] in Hlookup.
  rewrite insert_neq in Hlookup by (symmetry; exact Hneq).
  exact Hlookup.
Qed.

Lemma add_new_qubit_lookup_fresh : forall qstate p fresh Hfresh,
  quantum_map_of (add_new_qubit qstate p fresh Hfresh) fresh =
  Some (p, Datatypes.length (elems qubit_reference (participant * fin)
    (quantum_map_of qstate))).
Proof.
  intros qstate p fresh Hfresh.
  unfold add_new_qubit, quantum_map_of.
  cbn [proj1_sig projT1].
  rewrite insert_eq; reflexivity.
Qed.

Lemma add_new_qubit_lookup_preserves_other : forall
    qstate p fresh Hfresh q owner n,
  q <> fresh ->
  quantum_map_of qstate q = Some (owner, n) ->
  quantum_map_of (add_new_qubit qstate p fresh Hfresh) q = Some (owner, n).
Proof.
  intros qstate p fresh Hfresh q owner n Hneq Hlookup.
  unfold add_new_qubit, quantum_map_of.
  cbn [proj1_sig projT1].
  rewrite insert_neq by (symmetry; exact Hneq).
  exact Hlookup.
Qed.

Lemma remove_and_reindex_preserves_owner : forall
    (qm : finite_map qubit_reference (participant * fin))
    (measured q : qubit_reference) (index : nat) (owner : participant) (n : nat),
  q <> measured -> qm q = Some (owner, n) ->
  exists n', remove_and_reindex_qubit_map qm measured index q =
    Some (owner, n').
Proof.
  intros qm measured q index owner n Hneq Hlookup.
  exists (shift_wire_index index n).
  unfold remove_and_reindex_qubit_map.
  change (option_map (shift_qubit_index index)
    (delete (KEQ:=qr_dec) qm measured q) =
      Some (owner, shift_wire_index index n)).
  rewrite delete_neq by (symmetry; exact Hneq).
  rewrite Hlookup.
  unfold shift_qubit_index; simpl; reflexivity.
Qed.

Lemma apply_unitary_preserves_map : forall
    (qm : finite_map qubit_reference (participant * fin))
    (Hqm : quantum_map_wf qm)
    (sv : state_vector (Datatypes.length
      (elems qubit_reference (participant * fin) qm)))
    (Hsv : state_vector_wf sv) (dim : nat) (U : base_Unitary dim)
    (qs : list qubit_reference) (Hlen : Datatypes.length qs = dim)
    (Hdim : dim > 0)
    (qs' : quantum_state),
  apply_unitary qm Hqm sv Hsv U qs Hlen Hdim = Some qs' ->
  quantum_map_of qs' = qm.
Proof.
  intros qm Hqm sv Hsv dim U qs Hlen Hdim qs' Happly.
  unfold apply_unitary in Happly.
  destruct (lt_dec 0 (Datatypes.length
    (elems qubit_reference (participant * fin) qm))) as [Hpositive|Hempty];
    [|discriminate].
  destruct (le_dec dim (Datatypes.length
    (elems qubit_reference (participant * fin) qm))) as [Hbound|Htoo_large];
    [|discriminate].
  destruct (NoDup_dec (TEQ:=qr_dec) qs) as [Hnd|Hnotnd];
    [|discriminate].
  destruct (get_all_values_certified qm qs) as [certified|] eqn:Hcertified;
    [|discriminate].
  inversion Happly; reflexivity.
Qed.

Lemma quantum_map_lookup_in_keys : forall qstate q owner n,
  quantum_map_of qstate q = Some (owner, n) ->
  In q (map fst (elems qubit_reference (participant * fin)
    (quantum_map_of qstate))).
Proof.
  intros qstate q owner n Hlookup.
  apply in_map_iff; exists (q, (owner, n)); split; [reflexivity |].
  exact (proj2 (proj2 (specs qubit_reference (participant * fin)
    (quantum_map_of qstate)) q (owner, n)) Hlookup).
Qed.

Lemma add_new_qubit_lookup_back : forall qstate p fresh Hfresh q owner n,
  q <> fresh ->
  quantum_map_of (add_new_qubit qstate p fresh Hfresh) q = Some (owner, n) ->
  quantum_map_of qstate q = Some (owner, n).
Proof.
  intros qstate p fresh Hfresh q owner n Hneq Hlookup.
  unfold add_new_qubit, quantum_map_of in *.
  cbn [proj1_sig projT1] in Hlookup.
  rewrite insert_neq in Hlookup by (symmetry; exact Hneq).
  exact Hlookup.
Qed.

Lemma remove_and_reindex_lookup_back : forall
    (qm : finite_map qubit_reference (participant * fin))
    (measured q : qubit_reference) (index : nat) (owner : participant)
    (n : nat),
  remove_and_reindex_qubit_map qm measured index q = Some (owner, n) ->
  exists n0, qm q = Some (owner, n0).
Proof.
  intros qm measured q index owner n Hlookup.
  assert (Hnotnone : remove_and_reindex_qubit_map qm measured index q <> None)
    by (rewrite Hlookup; discriminate).
  apply (proj1 (remove_and_reindex_qubit_map_lookup_none qm measured index q))
    in Hnotnone as [Hneq Hpresent].
  destruct (qm q) as [[owner0 n0]|] eqn:Hsource; [|contradiction].
  assert (Hlookup' :
    option_map (shift_qubit_index index)
      (delete (KEQ:=qr_dec) qm measured q) = Some (owner, n)).
  {
    unfold remove_and_reindex_qubit_map.
    change (option_map (shift_qubit_index index)
      (delete (KEQ:=qr_dec) qm measured q) = Some (owner, n)).
    exact Hlookup.
  }
  rewrite delete_neq in Hlookup' by (symmetry; exact Hneq).
  rewrite Hsource in Hlookup'; simpl in Hlookup'.
  inversion Hlookup'; subst owner0.
  exists n0; reflexivity.
Qed.

Lemma replay_tau_step_on_state : forall qstate0 M qstate1 M' p pi qstate,
  step (qstate0, M) (Tau p) (qstate1, M') pi ->
  process_qubits_owned_by M qstate p ->
  exists qstate2 M2 pi2,
    step (qstate, M) (Tau p) (qstate2, M2) pi2.
Proof.
  intros qstate0 M qstate1 M' p pi qstate Hstep.
  revert qstate.
  dependent induction Hstep; intros qstate Howned.
  - (* New *)
    set (fresh := fresh_qubit_reference
      (map fst (elems qubit_reference (participant * fin)
        (quantum_map_of qstate)))).
    set (qnew := proj1_sig fresh).
    set (Hfresh2 := proj2_sig fresh).
    exists (add_new_qubit qstate p qnew Hfresh2),
      (insert (KEQ:=participant_dec) M p
        (subst_expression_in_process 0 0 (Val (QVal qnew)) P)), 1%R.
    eapply New with (q := qnew) (Hfresh := Hfresh2).
    exact H.
  - (* If false *)
    exists qstate, (insert (KEQ:=participant_dec) M p P0), 1%R.
    eapply If_0; [exact H | exact H0].
  - (* If true *)
    exists qstate, (insert (KEQ:=participant_dec) M p P1), 1%R.
    eapply If_1; [exact H | exact H0].
  - (* Measurement *)
    assert (Hsrc : M p = Some (p_measure (Val (QVal q)) P)).
    { exact H. }
    destruct (Howned (p_measure (Val (QVal q)) P) Hsrc q)
      as [nnew Hlookup_current].
    { simpl; auto. }
    assert (Hindex : nnew < Datatypes.length
        (elems qubit_reference (participant * fin) (quantum_map_of qstate))).
    { eapply quantum_map_lookup_index_lt with (p := p).
      - unfold quantum_map_of; exact (proj2_sig (projT1 qstate)).
      - exact Hlookup_current. }
    assert (Hpositive : 0 < Datatypes.length
        (elems qubit_reference (participant * fin) (quantum_map_of qstate)))
      by lia.
    destruct (measurement_outcome_nonzero_of_wf
      (quantum_map_of qstate) (proj1_sig (projT2 qstate))
      (proj2_sig (projT2 qstate)) nnew Hindex) as [result2 Hnonzero2].
    destruct (measure_qubit_from_nonzero
      (quantum_map_of qstate) (proj2_sig (projT1 qstate))
      (proj1_sig (projT2 qstate)) (proj2_sig (projT2 qstate))
      q p nnew result2 Hlookup_current Hpositive Hnonzero2)
      as [pi2 qstate2] eqn:Hmeasure.
    exists qstate2,
      (insert (KEQ:=participant_dec) M p
        (subst_expression_in_process 0 0 (Val (Bool result2)) P)), pi2!.
    eapply Meas with (n := nnew) (r := result2) (pi := pi2)
      (q_state2 := qstate2) (Hlookup := Hlookup_current)
      (Hlen := Hpositive) (Hnonzero := Hnonzero2).
    + exact Hsrc.
    + symmetry; exact Hmeasure.
  - (* Unitary *)
    assert (Hsrc : M p = Some
        (p_unitary dim U (map (fun z => Val (QVal z)) lq) P)).
    { exact H. }
    assert (Hlookup : forall q0, In q0 lq ->
        exists v, quantum_map_of qstate q0 = Some v).
    {
      intros q0 Hin.
      destruct (Howned
        (p_unitary dim U (map (fun z => Val (QVal z)) lq) P) Hsrc q0)
        as [nnew Hq].
      - simpl; apply in_app_iff; left.
        apply get_qubits_In.
        exists (Val (QVal q0)); split.
        + apply in_map_iff; exists q0; split; [reflexivity | exact Hin].
        + simpl; auto.
      - exists (p, nnew); exact Hq.
    }
    assert (Hincl : incl lq
        (map fst (elems qubit_reference (participant * fin)
          (quantum_map_of qstate)))).
    {
      intros q0 Hin.
      destruct (Hlookup q0 Hin) as [v Hq].
      apply in_map_iff; exists (q0, v); split; [reflexivity |].
      exact (proj2 (proj2 (specs qubit_reference
        (participant * fin) (quantum_map_of qstate)) q0 v) Hq).
    }
    pose proof (NoDup_incl_length H1 Hincl) as Hkeylen.
    rewrite length_map in Hkeylen.
    assert (Hbound : dim <= Datatypes.length
        (elems qubit_reference (participant * fin) (quantum_map_of qstate)))
      by (rewrite <- Hlen; exact Hkeylen).
    assert (Hpositive : 0 < Datatypes.length
        (elems qubit_reference (participant * fin) (quantum_map_of qstate)))
      by lia.
    destruct (apply_unitary_some_of_lookups
      (quantum_map_of qstate) (proj2_sig (projT1 qstate))
      (proj1_sig (projT2 qstate)) (proj2_sig (projT2 qstate))
      dim U lq Hlen Hdim H1 Hpositive Hbound Hlookup) as [qstate2 Happly].
    exists qstate2, (insert (KEQ:=participant_dec) M p P), 1%R.
    eapply Unitary with (Hlen := Hlen) (Hdim := Hdim).
    + exact Hsrc.
    + exact Happly.
    + exact H1.
    + apply Forall_forall; intros q0 Hin.
      destruct (Howned
        (p_unitary dim U (map (fun z => Val (QVal z)) lq) P) Hsrc q0)
        as [n Hq].
      * simpl; apply in_app_iff; left; apply get_qubits_In.
        exists (Val (QVal q0)); split.
        -- apply in_map_iff; exists q0; split; [reflexivity | exact Hin].
        -- simpl; auto.
      * exists n; exact Hq.
  - (* Congruence *)
    pose proof (process_qubits_owned_by_unfoldM M M1' qstate p
      H Howned) as Howned_mid.
    destruct (IHHstep qstate0 M1' qstate1 M' p
      ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
      qstate Howned_mid)
      as [qstate2 [M2 [pi2 Hinner]]].
    exists qstate2, M2, pi2.
    eapply Congr with (M1' := M1').
    + exact H.
    + exact Hinner.
Qed.

Lemma replay_transmit_step_on_state : forall qstate0 M qstate1 M' p q l v pi qstate,
  step (qstate0, M) (Transmit p q l v) (qstate1, M') pi ->
  process_qubits_owned_by M qstate p ->
  exists qstate2 M2,
    step (qstate, M) (Transmit p q l v) (qstate2, M2) 1%R.
Proof.
  intros qstate0 M qstate1 M' p q l v pi qstate Hstep.
  revert qstate.
  dependent induction Hstep; intros qstate Howned.
  - (* Classical communication *)
    exists qstate, s2.
    eapply Comm_C with (p := p) (q := q) (l := l) (e := e)
      (P := P) (lQ := lQ) (Q := Q) (v := v) (s1 := M)
      (q_state := qstate); eauto.
  - (* Quantum communication *)
    assert (Heval_literal : e = Val (QVal v0)).
    { eapply eval_qubit_value_is_literal; exact H3. }
    assert (Hqfree : In v0 (free_qubits (p_send q l e P))).
    {
      subst e; simpl; left; reflexivity.
    }
    destruct (Howned (p_send q l e P) H v0)
      as [ncurrent Hlookup_current].
    { exact Hqfree. }
    set (qstate2 := transfer_qubit_from_lookup
      (quantum_map_of qstate) (proj2_sig (projT1 qstate))
      (proj1_sig (projT2 qstate)) (proj2_sig (projT2 qstate))
      q v0 p ncurrent Hlookup_current).
    exists qstate2, s2.
    eapply Comm_Q with (p := p) (q := q) (l := l) (e := e)
      (P := P) (lQ := lQ) (Q := Q) (v := v0) (s1 := M)
      (q_state := qstate) (q_state' := qstate2) (n := ncurrent)
      (Hlookup := Hlookup_current); eauto.
  - (* Congruence *)
    pose proof (process_qubits_owned_by_unfoldM M M1' qstate p
      H Howned) as Howned_mid.
    destruct (IHHstep qstate0 M1' qstate1 M' p q l v
      ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
      qstate Howned_mid) as [qstate2 [M2 Hinner]].
    exists qstate2, M2.
    eapply Congr with (M1' := M1').
    + exact H.
    + exact Hinner.
Qed.

Lemma process_qubit_owner_agrees_by_after_tau_for : forall
    qstate M qstate' M' actor pi t,
  step (qstate, M) (Tau actor) (qstate', M') pi ->
  (actor = t \/ actor <> t) ->
  process_qubits_owned_by M qstate t ->
  process_qubit_owner_agrees_by M' qstate' t.
Proof.
  intros qstate M qstate' M' actor pi owner_pt Hstep.
  refine (step_ind
    (fun s a s' r => forall actor t,
      a = Tau actor -> (actor = t \/ actor <> t) ->
      process_qubits_owned_by (snd s) (fst s) t ->
      process_qubit_owner_agrees_by (snd s') (fst s') t)
    _ _ _ _ _ _ _ _ (qstate, M) (Tau actor) (qstate', M') pi Hstep
    actor owner_pt eq_refl).
  - intros p q l e P lQ l0 Q v s1 qs Hsend Hrecv Hneq Hnth Heval Hnotq
      Q' s2 actor0 t Ha Hactor Howned.
    discriminate.
  - intros p q l e P lQ l0 Q v s1 qs qs' old n Hlookup Hsend Hrecv Hneq
      Hnth Heval Htransfer Q' s2 actor0 t Ha Hactor Howned.
    discriminate.
  - intros p P s1 qs q Hfresh Hsrc q_state2 s2 actor0 t Ha Hactor Howned.
    inversion Ha; subst actor0.
    unfold process_qubit_owner_agrees_by.
    intros P' Htarget q0 Hin owner n Hlookup.
    simpl in Hlookup.
    destruct Hactor as [Heq|Hneq].
    + subst t.
      change (insert s1 p (subst_expression_in_process 0 0
        (Val (QVal q)) P) p = Some P') in Htarget.
      rewrite insert_eq in Htarget; inversion Htarget; subst P'.
      destruct (free_qubits_process_substitution P 0 0
        (Val (QVal q)) q0 Hin) as [Hold|Hnew].
      * destruct (Howned (p_newq P) Hsrc q0) as [n0 Hsource].
        -- simpl; exact Hold.
        -- simpl in Hsource.
           assert (Hneqfresh : q0 <> q).
           {
             intro Heq; subst q0.
             apply Hfresh.
             exact (quantum_map_lookup_in_keys qs q p n0 Hsource).
           }
           pose proof (add_new_qubit_lookup_other qs p q Hfresh q0 owner n
             Hneqfresh Hlookup) as Hsource'.
           rewrite Hsource in Hsource'; inversion Hsource'; reflexivity.
      * simpl in Hnew.
        destruct Hnew as [Heq|Hfalse]; [subst q0|contradiction].
        change (quantum_map_of (add_new_qubit qs p q Hfresh) q =
          Some (owner, n)) in Hlookup.
        rewrite add_new_qubit_lookup_fresh in Hlookup.
        inversion Hlookup; reflexivity.
    + change (insert s1 p (subst_expression_in_process 0 0
        (Val (QVal q)) P) t = Some P') in Htarget.
      rewrite insert_neq in Htarget by exact Hneq.
      destruct (Howned P' Htarget q0 Hin) as [n0 Hsource].
      simpl in Hsource.
      assert (Hneqfresh : q0 <> q).
      {
        intro Heq; subst q0.
        apply Hfresh.
        exact (quantum_map_lookup_in_keys qs q t n0 Hsource).
      }
      pose proof (add_new_qubit_lookup_other qs p q Hfresh q0 owner n
        Hneqfresh Hlookup) as Hsource'.
      rewrite Hsource in Hsource'; inversion Hsource'; reflexivity.
  - intros p e P1 P0 s1 qs Hsrc Heval s2 actor0 t Ha Hactor Howned.
    inversion Ha; subst actor0.
    destruct Hactor as [Heq|Hneq].
    + subst t.
      eapply process_qubit_owner_agreement_transport with
        (P := p_ite e P1 P0).
      * exact Howned.
      * exact Hsrc.
      * intros P' Htarget q0 Hin.
        change (insert s1 p P0 p = Some P') in Htarget.
        rewrite insert_eq in Htarget; inversion Htarget; subst P'.
        simpl; apply in_or_app; right; apply in_or_app; right; exact Hin.
      * intros q0 owner n Hlookup.
        exists n; exact Hlookup.
    + unfold process_qubit_owner_agrees_by.
      intros P' Htarget q0 Hin owner n Hlookup.
      change (insert s1 p P0 t = Some P') in Htarget.
      rewrite insert_neq in Htarget by exact Hneq.
      destruct (Howned P' Htarget q0 Hin) as [n0 Hsource].
      simpl in Hsource, Hlookup; rewrite Hsource in Hlookup.
      inversion Hlookup; reflexivity.
  - intros p e P1 P0 s1 qs Hsrc Heval s2 actor0 t Ha Hactor Howned.
    inversion Ha; subst actor0.
    destruct Hactor as [Heq|Hneq].
    + subst t.
      eapply process_qubit_owner_agreement_transport with
        (P := p_ite e P1 P0).
      * exact Howned.
      * exact Hsrc.
      * intros P' Htarget q0 Hin.
        change (insert s1 p P1 p = Some P') in Htarget.
        rewrite insert_eq in Htarget; inversion Htarget; subst P'.
        simpl; apply in_or_app; right; apply in_or_app; left; exact Hin.
      * intros q0 owner n Hlookup.
        exists n; exact Hlookup.
    + unfold process_qubit_owner_agrees_by.
      intros P' Htarget q0 Hin owner n Hlookup.
      change (insert s1 p P1 t = Some P') in Htarget.
      rewrite insert_neq in Htarget by exact Hneq.
      destruct (Howned P' Htarget q0 Hin) as [n0 Hsource].
      simpl in Hsource, Hlookup; rewrite Hsource in Hlookup.
      inversion Hlookup; reflexivity.
  - intros p q P s1 qs qs' n r pi0 Hlookup Hlen Hnonzero Hsrc Hmeasure s2
      actor0 t Ha Hactor Howned.
    inversion Ha; subst actor0.
    assert (Hmap_measure : quantum_map_of qs' =
      remove_and_reindex_qubit_map (quantum_map_of qs) q n).
    {
      pose proof (f_equal (fun pair => quantum_map_of (snd pair)) Hmeasure)
        as Hmap.
      unfold quantum_map_of in Hmap.
      rewrite measure_qubit_nonzero_map in Hmap.
      exact Hmap.
    }
    destruct Hactor as [Heq|Hneq].
    + subst t.
      eapply process_qubit_owner_agreement_transport with
        (P := p_measure (Val (QVal q)) P).
      * exact Howned.
      * exact Hsrc.
      * intros P' Htarget q0 Hin.
        change (insert s1 p (subst_expression_in_process 0 0
          (Val (Bool r)) P) p = Some P') in Htarget.
        rewrite insert_eq in Htarget; inversion Htarget; subst P'.
        destruct (free_qubits_process_substitution P 0 0
          (Val (Bool r)) q0 Hin) as [Hold|Hnew].
        -- simpl; right; exact Hold.
        -- simpl in Hnew; contradiction.
      * intros q0 owner n0 Hlookup0.
        simpl in Hlookup0.
        rewrite Hmap_measure in Hlookup0.
        destruct (remove_and_reindex_lookup_back (quantum_map_of qs) q q0 n
          owner n0 Hlookup0) as [nsource Hsource].
        exists nsource; exact Hsource.
    + unfold process_qubit_owner_agrees_by.
      intros P' Htarget q0 Hin owner n0 Hlookup0.
      change (insert s1 p (subst_expression_in_process 0 0
        (Val (Bool r)) P) t = Some P') in Htarget.
      rewrite insert_neq in Htarget by exact Hneq.
      destruct (Howned P' Htarget q0 Hin) as [nsource Hsource].
      simpl in Hsource, Hlookup0.
      rewrite Hmap_measure in Hlookup0.
      destruct (remove_and_reindex_lookup_back (quantum_map_of qs) q q0 n
        owner n0 Hlookup0) as [nback Hback].
      rewrite Hsource in Hback; inversion Hback; reflexivity.
  - intros dim p U lq P s1 qs qs' Hlen Hdim Hsrc Happly Hnd Hunitary_owned
      s2 actor0 t Ha Hactor Howned.
    inversion Ha; subst actor0.
    assert (Hmap_unitary : quantum_map_of qs' = quantum_map_of qs).
    { eapply apply_unitary_preserves_map; exact Happly. }
    destruct Hactor as [Heq|Hneq].
    + subst t.
      eapply process_qubit_owner_agreement_transport with
        (P := p_unitary dim U (map (fun z => Val (QVal z)) lq) P).
      * exact Howned.
      * exact Hsrc.
      * intros P' Htarget q0 Hin.
        change (insert s1 p P p = Some P') in Htarget.
        rewrite insert_eq in Htarget; inversion Htarget; subst P'.
        simpl; apply in_or_app; right; exact Hin.
      * intros q0 owner n Hlookup0.
        simpl in Hlookup0.
        rewrite Hmap_unitary in Hlookup0.
        exists n; exact Hlookup0.
    + unfold process_qubit_owner_agrees_by.
      intros P' Htarget q0 Hin owner n Hlookup0.
      change (insert s1 p P t = Some P') in Htarget.
      rewrite insert_neq in Htarget by exact Hneq.
      destruct (Howned P' Htarget q0 Hin) as [nsource Hsource].
      simpl in Hsource, Hlookup0.
      simpl in Hlookup0; rewrite Hmap_unitary, Hsource in Hlookup0.
      inversion Hlookup0; reflexivity.
  - intros M1 M1' M2 qs qs' a0 r Hunfold1 Hinner IH
      actor0 t Ha Hactor Howned.
    pose proof (process_qubits_owned_by_unfoldM M1 M1' qs t
      Hunfold1 Howned) as Hmiddle.
    pose proof (IH actor0 t Ha Hactor Hmiddle) as Hafter.
    exact Hafter.
Qed.

Definition session_avoids_qubit (M : session) (q : qubit_reference) :=
  forall pt P, M pt = Some P -> ~ In q (free_qubits P).

Lemma session_avoids_qubit_unfoldM : forall M M' q,
  unfoldM M M' -> session_avoids_qubit M q -> session_avoids_qubit M' q.
Proof.
  intros M M' q Hunfold Havoid pt P Hlookup Hin.
  destruct (Hunfold pt) as [[Hnone Hnone']|[P0 [P1 [Hsrc [Hdst Hpre]]]]].
  - rewrite Hnone' in Hlookup; discriminate.
  - rewrite Hdst in Hlookup; inversion Hlookup; subst P.
    apply (Havoid pt P0 Hsrc).
    eapply free_qubits_precong; eassumption.
Qed.

Lemma session_avoids_qubit_of_typed_session `{good_merge} : forall
    M delta G qcontext q,
  typecheck_session qcontext M delta G ->
  qcontext q = None ->
  session_avoids_qubit M q.
Proof.
  intros M delta G qcontext q Htyped Habsent pt P Hlookup Hin.
  pose proof (proj2 (free_qubits_session_in_one M q)) as Hsession.
  assert (Hin_session : In q (free_qubits_session M)).
  {
    apply Hsession; exists pt, P; split.
    - apply (proj2 (proj2 (specs participant process M) pt P)); exact Hlookup.
    - exact Hin.
  }
  pose proof (typecheck_session_free_qubits M delta G
    qcontext Htyped q Hin_session) as Hcontext.
  rewrite Habsent in Hcontext; discriminate.
Qed.

Lemma session_avoids_qubit_after_tau : forall
    qstate M qstate' M' actor pi q,
  step (qstate, M) (Tau actor) (qstate', M') pi ->
  quantum_map_of qstate q <> None ->
  session_avoids_qubit M q ->
  session_avoids_qubit M' q.
Proof.
  intros qstate M qstate' M' actor pi q Hstep.
  refine (step_ind
    (fun s a s' r => forall actor q,
      a = Tau actor -> quantum_map_of (fst s) q <> None ->
      session_avoids_qubit (snd s) q -> session_avoids_qubit (snd s') q)
    _ _ _ _ _ _ _ _ (qstate, M) (Tau actor) (qstate', M') pi Hstep
    actor q eq_refl).
  - intros p q0 l e P lQ l0 Q v s1 qs Hsend Hrecv Hneq Hnth Heval Hnotq
      Q' s2 actor0 dummy Ha Hpresent Havoid.
    discriminate.
  - intros p q0 l e P lQ l0 Q v s1 qs qs' old n Hlookup Hsend Hrecv Hneq
      Hnth Heval Htransfer Q' s2 actor0 dummy Ha Hpresent Havoid.
    discriminate.
  - intros p P s1 qs qnew Hfresh Hsrc q_state2 s2 actor0 dummy Ha Hpresent Havoid.
    inversion Ha; subst actor0.
    unfold session_avoids_qubit.
    intros pt P' Htarget Hin.
    destruct (participant_dec pt p) as [Heq|Hneq].
    + subst pt.
      change (insert s1 p (subst_expression_in_process 0 0
        (Val (QVal qnew)) P) p = Some P') in Htarget.
      rewrite insert_eq in Htarget; inversion Htarget; subst P'.
      destruct (free_qubits_process_substitution P 0 0
        (Val (QVal qnew)) dummy Hin) as [Hold|Hnew].
      * apply (Havoid p (p_newq P) Hsrc); simpl; exact Hold.
      * simpl in Hnew; destruct Hnew as [Heq|Hfalse]; [|contradiction].
        subst qnew.
        destruct (quantum_map_of qs dummy) as [[owner n0]|] eqn:Hmap;
          [|contradiction].
        apply Hfresh.
        exact (quantum_map_lookup_in_keys qs dummy owner n0 Hmap).
    + change (insert s1 p (subst_expression_in_process 0 0
        (Val (QVal qnew)) P) pt = Some P') in Htarget.
      rewrite insert_neq in Htarget by (symmetry; exact Hneq).
      eapply Havoid; eassumption.
  - intros p e P1 P0 s1 qs Hsrc Heval s2 actor0 dummy Ha Hpresent Havoid.
    inversion Ha; subst actor0.
    unfold session_avoids_qubit.
    intros pt P' Htarget Hin.
    destruct (participant_dec pt p) as [Heq|Hneq].
    + subst pt.
      change (insert s1 p P0 p = Some P') in Htarget.
      rewrite insert_eq in Htarget; inversion Htarget; subst P'.
      assert (Hin_source : In dummy (free_qubits (p_ite e P1 P0))).
      { simpl; apply in_or_app; right; apply in_or_app; right; exact Hin. }
      eapply Havoid; eassumption.
    + change (insert s1 p P0 pt = Some P') in Htarget.
      rewrite insert_neq in Htarget by (symmetry; exact Hneq).
      eapply Havoid; eassumption.
  - intros p e P1 P0 s1 qs Hsrc Heval s2 actor0 dummy Ha Hpresent Havoid.
    inversion Ha; subst actor0.
    unfold session_avoids_qubit.
    intros pt P' Htarget Hin.
    destruct (participant_dec pt p) as [Heq|Hneq].
    + subst pt.
      change (insert s1 p P1 p = Some P') in Htarget.
      rewrite insert_eq in Htarget; inversion Htarget; subst P'.
      assert (Hin_source : In dummy (free_qubits (p_ite e P1 P0))).
      { simpl; apply in_or_app; right; apply in_or_app; left; exact Hin. }
      eapply Havoid; eassumption.
    + change (insert s1 p P1 pt = Some P') in Htarget.
      rewrite insert_neq in Htarget by (symmetry; exact Hneq).
      eapply Havoid; eassumption.
  - intros p q0 P s1 qs qs' n r pi0 Hlookup Hlen Hnonzero Hsrc Hmeasure s2
      actor0 dummy Ha Hpresent Havoid.
    inversion Ha; subst actor0.
    unfold session_avoids_qubit.
    intros pt P' Htarget Hin.
    destruct (participant_dec pt p) as [Heq|Hneq].
    + subst pt.
      change (insert s1 p (subst_expression_in_process 0 0
        (Val (Bool r)) P) p = Some P') in Htarget.
      rewrite insert_eq in Htarget; inversion Htarget; subst P'.
      destruct (free_qubits_process_substitution P 0 0
        (Val (Bool r)) dummy Hin) as [Hold|Hnew].
      * apply (Havoid p (p_measure (Val (QVal q0)) P) Hsrc).
        simpl; right; exact Hold.
      * simpl in Hnew; contradiction.
    + change (insert s1 p (subst_expression_in_process 0 0
        (Val (Bool r)) P) pt = Some P') in Htarget.
      rewrite insert_neq in Htarget by (symmetry; exact Hneq).
      eapply Havoid; eassumption.
  - intros dim p U lq P s1 qs qs' Hlen Hdim Hsrc Happly Hnd Hunitary_owned
      s2 actor0 dummy Ha Hpresent Havoid.
    inversion Ha; subst actor0.
    unfold session_avoids_qubit.
    intros pt P' Htarget Hin.
    destruct (participant_dec pt p) as [Heq|Hneq].
    + subst pt.
      change (insert s1 p P p = Some P') in Htarget.
      rewrite insert_eq in Htarget; inversion Htarget; subst P'.
      assert (Hin_source : In dummy (free_qubits
        (p_unitary dim U (map (fun z => Val (QVal z)) lq) P))).
      { simpl; apply in_or_app; right; exact Hin. }
      eapply Havoid; eassumption.
    + change (insert s1 p P pt = Some P') in Htarget.
      rewrite insert_neq in Htarget by (symmetry; exact Hneq).
      eapply Havoid; eassumption.
  - intros M1 M1' M2 qs qs' a0 r Hunfold1 Hinner IH
      actor0 dummy Ha Hpresent Havoid.
    pose proof (session_avoids_qubit_unfoldM M1 M1' dummy Hunfold1 Havoid)
      as Hmiddle.
    pose proof (IH actor0 dummy Ha Hpresent Hmiddle) as Hafter.
    exact Hafter.
Qed.

Lemma quantum_map_lookup_implies_positive_length : forall qstate q owner n,
  quantum_map_of qstate q = Some (owner, n) ->
  0 < Datatypes.length (elems qubit_reference (participant * fin)
    (quantum_map_of qstate)).
Proof.
  intros qstate q owner n Hlookup.
  assert (Hindex : n < Datatypes.length (elems qubit_reference
      (participant * fin) (quantum_map_of qstate))).
  {
    eapply quantum_map_lookup_index_lt with (p := owner).
    - unfold quantum_map_of; exact (proj2_sig (projT1 qstate)).
    - exact Hlookup.
  }
  lia.
Qed.

Lemma quantum_map_lookup_after_tau : forall
    qstate M qstate' M' actor pi q,
  step (qstate, M) (Tau actor) (qstate', M') pi ->
  session_avoids_qubit M q ->
  quantum_map_of qstate q <> None ->
  quantum_map_of qstate' q <> None.
Proof.
  intros qstate M qstate' M' actor pi q Hstep.
  refine (step_ind
    (fun s a s' r => forall actor q,
      a = Tau actor -> session_avoids_qubit (snd s) q ->
      quantum_map_of (fst s) q <> None ->
      quantum_map_of (fst s') q <> None)
    _ _ _ _ _ _ _ _ (qstate, M) (Tau actor) (qstate', M') pi Hstep
    actor q eq_refl).
  - intros p q0 l e P lQ l0 Q v s1 qs Hsend Hrecv Hneq Hnth Heval Hnotq
      Q' s2 actor0 dummy Ha Havoid Hpresent.
    discriminate.
  - intros p q0 l e P lQ l0 Q v s1 qs qs' old n Hlookup Hsend Hrecv Hneq
      Hnth Heval Htransfer Q' s2 actor0 dummy Ha Havoid Hpresent.
    discriminate.
  - intros p P s1 qs qnew Hfresh Hsrc q_state2 s2 actor0 dummy Ha Havoid Hpresent.
    inversion Ha; subst actor0.
    destruct (quantum_map_of qs dummy) as [[owner n0]|] eqn:Hmap;
      [|contradiction].
    assert (Hneq : dummy <> qnew).
    {
      intro Heq; subst qnew.
      apply Hfresh.
      exact (quantum_map_lookup_in_keys qs dummy owner n0 Hmap).
    }
    change (quantum_map_of (add_new_qubit qs p qnew Hfresh) dummy <> None).
    intro Hnone.
    pose proof (add_new_qubit_lookup_preserves_other qs p qnew Hfresh
      dummy owner n0 Hneq Hmap) as Hout.
    rewrite Hnone in Hout; discriminate.
  - intros p e P1 P0 s1 qs Hsrc Heval s2 actor0 dummy Ha Havoid Hpresent.
    inversion Ha; subst actor0; exact Hpresent.
  - intros p e P1 P0 s1 qs Hsrc Heval s2 actor0 dummy Ha Havoid Hpresent.
    inversion Ha; subst actor0; exact Hpresent.
  - intros p q0 P s1 qs qs' n r pi0 Hlookup Hlen Hnonzero Hsrc Hmeasure s2
      actor0 dummy Ha Havoid Hpresent.
    inversion Ha; subst actor0.
    assert (Hneq : q0 <> dummy).
    {
      intro Heq; subst dummy.
      apply (Havoid p (p_measure (Val (QVal q0)) P) Hsrc).
      simpl; left; reflexivity.
    }
    destruct (quantum_map_of qs dummy) as [[owner n0]|] eqn:Hmap;
      [|contradiction].
    assert (Hmap_measure : quantum_map_of qs' =
      remove_and_reindex_qubit_map (quantum_map_of qs) q0 n).
    {
      pose proof (f_equal (fun pair => quantum_map_of (snd pair)) Hmeasure)
        as Hmap'.
      unfold quantum_map_of in Hmap'.
      rewrite measure_qubit_nonzero_map in Hmap'.
      exact Hmap'.
    }
    destruct (remove_and_reindex_preserves_owner (quantum_map_of qs) q0
      dummy n owner n0 ltac:(congruence) Hmap) as [n' Hnewmap].
    change (quantum_map_of qs' dummy <> None).
    rewrite Hmap_measure, Hnewmap; discriminate.
  - intros dim p U lq P s1 qs qs' Hlen Hdim Hsrc Happly Hnd Hunitary_owned
      s2 actor0 dummy Ha Havoid Hpresent.
    inversion Ha; subst actor0.
    assert (Hmap_unitary : quantum_map_of qs' = quantum_map_of qs).
    { eapply apply_unitary_preserves_map; exact Happly. }
    change (quantum_map_of qs' dummy <> None).
    rewrite Hmap_unitary; exact Hpresent.
  - intros M1 M1' M2 qs qs' a0 r Hunfold1 Hinner IH
      actor0 dummy Ha Havoid Hpresent.
    pose proof (session_avoids_qubit_unfoldM M1 M1' dummy Hunfold1 Havoid)
      as Hmiddle.
    pose proof (IH actor0 dummy Ha Hmiddle Hpresent) as Hafter.
    exact Hafter.
Qed.

Lemma cguarded_session_after_action : forall qstate M a qstate' M' pi,
  step (qstate, M) a (qstate', M') pi ->
  (exists p, a = Tau p) ->
  cguarded_session M -> cguarded_session M'.
Proof.
  intros qstate M a qstate' M' pi Hstep.
  refine (step_ind
    (fun s a s' r =>
      (exists p, a = Tau p) ->
      cguarded_session (snd s) -> cguarded_session (snd s'))
    _ _ _ _ _ _ _ _ (qstate, M) a (qstate', M') pi Hstep).
  - intros p q l e P lQ l0 Q v s1 qs Hsend Hrecv Hneq Hnth Heval Hnotq Q' s2 Htau Hguard.
    destruct Htau as [pt Htau]; discriminate.
  - intros p q l e P lQ l0 Q v s1 qs qs' n Hlookup
      Hsend Hrecv Hneq Hnth Heval Htransfer Q' s2 Htau Hguard.
    destruct Htau as [pt Htau]; discriminate.
  - intros p P s1 qs q Hfresh Hsrc q_state2 s2 Htau Hguard pt P' Htarget.
    simpl in Hguard.
    destruct (participant_dec pt p) as [Heq|Hneq].
    + subst pt.
      change (insert s1 p (subst_expression_in_process 0 0 (Val (QVal q)) P) p = Some P') in Htarget.
      pose proof (Hguard p (p_newq P) Hsrc) as Hnew.
      pose proof (cguardedP_after_subst_expr P (Val (QVal q)) 0 0
        (cguardedP_newq_body P Hnew)) as Hresult.
      rewrite insert_eq in Htarget; injection Htarget as Hsame.
      rewrite <- Hsame; exact Hresult.
    + change (insert s1 p (subst_expression_in_process 0 0 (Val (QVal q)) P) pt = Some P') in Htarget.
      rewrite insert_neq in Htarget by (symmetry; exact Hneq).
      eapply Hguard; exact Htarget.
  - intros p e P1 P0 s1 qs Hsrc Heval s2 Htau Hguard pt P' Htarget.
    simpl in Hguard.
    destruct (participant_dec pt p) as [Heq|Hneq].
    + subst pt.
      change (insert s1 p P0 p = Some P') in Htarget.
      pose proof (Hguard p (p_ite e P1 P0) Hsrc) as Hite.
      pose proof (proj2 (cguardedP_after_ite e P1 P0 Hite)) as Hresult.
      rewrite insert_eq in Htarget; injection Htarget as Hsame.
      rewrite <- Hsame; exact Hresult.
    + change (insert s1 p P0 pt = Some P') in Htarget.
      rewrite insert_neq in Htarget by (symmetry; exact Hneq).
      eapply Hguard; exact Htarget.
  - intros p e P1 P0 s1 qs Hsrc Heval s2 Htau Hguard pt P' Htarget.
    simpl in Hguard.
    destruct (participant_dec pt p) as [Heq|Hneq].
    + subst pt.
      change (insert s1 p P1 p = Some P') in Htarget.
      pose proof (Hguard p (p_ite e P1 P0) Hsrc) as Hite.
      pose proof (proj1 (cguardedP_after_ite e P1 P0 Hite)) as Hresult.
      rewrite insert_eq in Htarget; injection Htarget as Hsame.
      rewrite <- Hsame; exact Hresult.
    + change (insert s1 p P1 pt = Some P') in Htarget.
      rewrite insert_neq in Htarget by (symmetry; exact Hneq).
      eapply Hguard; exact Htarget.
  - intros p q P s1 qs qs' n r pi0 Hlookup Hlen Hnonzero Hsrc Hmeasure s2 Htau Hguard pt P' Htarget.
    simpl in Hguard.
    destruct (participant_dec pt p) as [Heq|Hneq].
    + subst pt.
      change (insert s1 p (subst_expression_in_process 0 0 (Val (Bool r)) P) p = Some P') in Htarget.
      pose proof (Hguard p (p_measure (Val (QVal q)) P) Hsrc) as Hmeas.
      pose proof (cguardedP_after_subst_expr P (Val (Bool r)) 0 0
        (cguardedP_measure_body (Val (QVal q)) P Hmeas)) as Hresult.
      rewrite insert_eq in Htarget; injection Htarget as Hsame.
      rewrite <- Hsame; exact Hresult.
    + change (insert s1 p (subst_expression_in_process 0 0 (Val (Bool r)) P) pt = Some P') in Htarget.
      rewrite insert_neq in Htarget by (symmetry; exact Hneq).
      eapply Hguard; exact Htarget.
  - intros dim p U lq P s1 qs qs' Hlen Hdim Hsrc Happly Hnd Hunitary_owned
      s2 Htau Hguard pt P' Htarget.
    simpl in Hguard.
    destruct (participant_dec pt p) as [Heq|Hneq].
    + subst pt.
      change (insert s1 p P p = Some P') in Htarget.
      pose proof (Hguard p
        (p_unitary dim U (map (fun z => Val (QVal z)) lq) P) Hsrc) as Hunitary.
      pose proof (cguardedP_unitary_body dim U
        (map (fun z => Val (QVal z)) lq) P Hunitary) as Hresult.
      rewrite insert_eq in Htarget; injection Htarget as Hsame.
      rewrite <- Hsame; exact Hresult.
    + change (insert s1 p P pt = Some P') in Htarget.
      rewrite insert_neq in Htarget by (symmetry; exact Hneq).
      eapply Hguard; exact Htarget.
  - intros M1 M1' M2 qs qs' a0 r Hunfold1 Hinner IH Htau Hguard.
    simpl in Hguard.
    pose proof (cguarded_session_unfoldM M1 M1' Hunfold1 Hguard) as Hmiddle.
    pose proof (IH Htau Hmiddle) as Hmiddle'.
    exact Hmiddle'.
Qed.

Lemma cguarded_session_after_tau : forall M M' qstate qstate' p pi,
  step (qstate, M) (Tau p) (qstate', M') pi ->
  cguarded_session M -> cguarded_session M'.
Proof.
  intros M M' qstate qstate' p pi Hstep Hguard.
  eapply cguarded_session_after_action; eauto.
Qed.

Lemma internal_prefix_height_tau_decreases : forall
    qstate M qstate' M' actor pi,
  step (qstate, M) (Tau actor) (qstate', M') pi ->
  cguarded_session M ->
  exists P P', M actor = Some P /\ M' actor = Some P' /\
    internal_prefix_height P' < internal_prefix_height P.
Proof.
  intros qstate M qstate' M' actor pi Hstep.
  refine (step_ind
    (fun s a s' r => forall actor,
      a = Tau actor -> cguarded_session (snd s) ->
      exists P P', snd s actor = Some P /\ snd s' actor = Some P' /\
        internal_prefix_height P' < internal_prefix_height P)
    _ _ _ _ _ _ _ _ (qstate, M) (Tau actor) (qstate', M') pi Hstep
    actor eq_refl).
  - intros p q l e P lQ l0 Q v s1 qs Hsend Hrecv Hneq Hnth Heval Hnotq
      Q' s2 actor0 Ha Hguard.
    discriminate.
  - intros p q l e P lQ l0 Q v s1 qs qs' n Hlookup Hsend Hrecv Hneq
      Hnth Heval Htransfer Q' s2 actor0 Ha Hguard.
    discriminate.
  - intros p P s1 qs q Hfresh Hsrc q_state2 s2 actor0 Ha Hguard.
    inversion Ha; subst actor0.
    exists (p_newq P), (subst_expression_in_process 0 0 (Val (QVal q)) P).
    split; [exact Hsrc|].
    split; [simpl; destruct (participant_dec p p); [reflexivity|contradiction]|].
    rewrite internal_prefix_height_expression_substitution; simpl; lia.
  - intros p e P1 P0 s1 qs Hsrc Heval s2 actor0 Ha Hguard.
    inversion Ha; subst actor0.
    exists (p_ite e P1 P0), P0.
    split; [exact Hsrc|].
    split; [simpl; destruct (participant_dec p p); [reflexivity|contradiction]|].
    simpl; lia.
  - intros p e P1 P0 s1 qs Hsrc Heval s2 actor0 Ha Hguard.
    inversion Ha; subst actor0.
    exists (p_ite e P1 P0), P1.
    split; [exact Hsrc|].
    split; [simpl; destruct (participant_dec p p); [reflexivity|contradiction]|].
    simpl; lia.
  - intros p q P s1 qs qs' n r pi0 Hlookup Hlen Hnonzero Hsrc Hmeasure s2
      actor0 Ha Hguard.
    inversion Ha; subst actor0.
    exists (p_measure (Val (QVal q)) P),
      (subst_expression_in_process 0 0 (Val (Bool r)) P).
    split; [exact Hsrc|].
    split; [simpl; destruct (participant_dec p p); [reflexivity|contradiction]|].
    rewrite internal_prefix_height_expression_substitution; simpl; lia.
  - intros dim p U lq P s1 qs qs' Hlen Hdim Hsrc Happly Hnd Hunitary_owned
      s2 actor0 Ha Hguard.
    inversion Ha; subst actor0.
    exists (p_unitary dim U (map (fun z => Val (QVal z)) lq) P), P.
    split; [exact Hsrc|].
    split; [simpl; destruct (participant_dec p p); [reflexivity|contradiction]|].
    simpl; lia.
  - intros M1 M1' M2 qs qs' a0 r Hunfold1 Hinner IH
      actor0 Ha Hguard.
    pose proof (cguarded_session_unfoldM M1 M1' Hunfold1 Hguard) as Hmiddle.
    destruct (IH actor0 Ha Hmiddle) as [Pmid [Pmid' [Hmid [Hmid' Hdecrease]]]].
    simpl in Hmid, Hmid'.
    destruct (Hunfold1 actor0) as [[Hnone Hnone']|
      [Psrc [P0 [Hsrc [HmidMap Hpre0]]]]].
    + rewrite Hnone' in Hmid; discriminate.
    + rewrite Hmid in HmidMap; inversion HmidMap; subst P0.
      exists Psrc, Pmid'.
      split; [exact Hsrc|].
      split; [exact Hmid'|].
      pose proof (internal_prefix_height_precong Psrc Pmid
        (Hguard actor0 Psrc Hsrc) Hpre0) as Hsource_bound.
      lia.
Qed.

Lemma internal_prefix_height_tau_nonincreasing_for : forall
    qstate M qstate' M' actor pi t,
  step (qstate, M) (Tau actor) (qstate', M') pi ->
  actor <> t ->
  cguarded_session M ->
  forall P P', M t = Some P -> M' t = Some P' ->
  internal_prefix_height P' <= internal_prefix_height P.
Proof.
  intros qstate M qstate' M' actor pi owner_pt Hstep.
  refine (step_ind
    (fun s a s' r => forall actor t,
      a = Tau actor -> actor <> t -> cguarded_session (snd s) ->
      forall P P', snd s t = Some P -> snd s' t = Some P' ->
      internal_prefix_height P' <= internal_prefix_height P)
    _ _ _ _ _ _ _ _ (qstate, M) (Tau actor) (qstate', M') pi Hstep
    actor owner_pt eq_refl).
  - intros p q l e P lQ l0 Q v s1 qs Hsend Hrecv Hneq Hnth Heval Hnotq
      Q' s2 actor0 t Ha Hactor Hguard P0 P0' Hsource Htarget.
    discriminate.
  - intros p q l e P lQ l0 Q v s1 qs qs' n Hlookup Hsend Hrecv Hneq
      Hnth Heval Htransfer Q' s2 actor0 t Ha Hactor Hguard P0 P0'
      Hsource Htarget.
    discriminate.
  - intros p P s1 qs q Hfresh Hsrc q_state2 s2 actor0 t Ha Hactor Hguard
      P0 P0' Hsource Htarget.
    inversion Ha; subst actor0.
    change (insert s1 p (subst_expression_in_process 0 0
      (Val (QVal q)) P) t = Some P0') in Htarget.
    rewrite insert_neq in Htarget by exact Hactor.
    simpl in Hsource.
    rewrite Hsource in Htarget; inversion Htarget; subst P0'; lia.
  - intros p e P1 P0 s1 qs Hsrc Heval s2 actor0 t Ha Hactor Hguard
      Psrc Pdst Hsource Htarget.
    inversion Ha; subst actor0.
    change (insert s1 p P0 t = Some Pdst) in Htarget.
    rewrite insert_neq in Htarget by exact Hactor.
    simpl in Hsource.
    rewrite Hsource in Htarget; inversion Htarget; subst Pdst; lia.
  - intros p e P1 P0 s1 qs Hsrc Heval s2 actor0 t Ha Hactor Hguard
      Psrc Pdst Hsource Htarget.
    inversion Ha; subst actor0.
    change (insert s1 p P1 t = Some Pdst) in Htarget.
    rewrite insert_neq in Htarget by exact Hactor.
    simpl in Hsource.
    rewrite Hsource in Htarget; inversion Htarget; subst Pdst; lia.
  - intros p q P s1 qs qs' n r pi0 Hlookup Hlen Hnonzero Hsrc Hmeasure s2
      actor0 t Ha Hactor Hguard Psrc Pdst Hsource Htarget.
    inversion Ha; subst actor0.
    change (insert s1 p (subst_expression_in_process 0 0
      (Val (Bool r)) P) t = Some Pdst) in Htarget.
    rewrite insert_neq in Htarget by exact Hactor.
    simpl in Hsource.
    rewrite Hsource in Htarget; inversion Htarget; subst Pdst; lia.
  - intros dim p U lq P s1 qs qs' Hlen Hdim Hsrc Happly Hnd Hunitary_owned
      s2 actor0 t Ha Hactor Hguard Psrc Pdst Hsource Htarget.
    inversion Ha; subst actor0.
    change (insert s1 p P t = Some Pdst) in Htarget.
    rewrite insert_neq in Htarget by exact Hactor.
    simpl in Hsource.
    rewrite Hsource in Htarget; inversion Htarget; subst Pdst; lia.
  - intros M1 M1' M2 qs qs' a0 r Hunfold1 Hinner IH
      actor0 t Ha Hactor Hguard P P' Hsource Htarget.
    simpl in Hsource, Htarget.
    pose proof (cguarded_session_unfoldM M1 M1' Hunfold1 Hguard) as Hmiddle.
    destruct (Hunfold1 t) as [[Hnone Hnone']|
      [Psrc [Pmid [Hsrc [Hmid Hpre0]]]]].
    + rewrite Hnone in Hsource; discriminate.
    + rewrite Hsource in Hsrc; inversion Hsrc; subst Psrc.
      pose proof (IH actor0 t Ha Hactor Hmiddle Pmid P' Hmid Htarget)
        as Hdecrease.
      pose proof (internal_prefix_height_precong P Pmid
        (Hguard t P Hsource) Hpre0) as Hsource_bound.
      lia.
Qed.


Lemma typecheck_session_component_at_delta `{good_merge} : forall
    qcontext M delta G p P T,
  typecheck_session qcontext M delta G ->
  M p = Some P -> delta p = Some T ->
  exists qc, typecheck_process (nil, nil, qc) P T.
Proof.
  intros qcontext M delta G p P T Htyped HM Hdelta.
  unfold typecheck_session in Htyped.
  destruct Htyped as [lqc [Hreg [Hbalanced [Hassoc [Hpartition
    [Hlength [Hperm HtypedProcesses]]]]]]].
  assert (HinDelta : In (p, T) (elems participant ltt delta)).
  { apply (proj2 (specs _ _ delta) p T); exact Hdelta. }
  assert (HinM : In p (session_participants M)).
  {
    unfold session_participants.
    eapply Permutation_in; [exact Hperm|].
    apply in_map_iff; exists (p, T); split; [reflexivity|exact HinDelta].
  }
  apply in_map_iff in HinM as [[p0 P0] [Hfst HinPair]].
  simpl in Hfst; subst p0.
  assert (HM0 : M p = Some P0).
  { apply (proj2 (specs _ _ M) p P0); exact HinPair. }
  rewrite HM in HM0; inversion HM0; subst P0.
  destruct (typecheck_session_component_of_map qcontext M delta lqc Hperm Hlength HtypedProcesses p P HM)
    as [n [T0 [qc [Hnth [Hqc [Hdelta0 HtypedP]]]]]].
  rewrite Hdelta in Hdelta0; inversion Hdelta0; subst T0.
  exists qc; exact HtypedP.
Qed.

Lemma typecheck_session_has_delta_component `{good_merge} : forall
    qcontext M delta G p T,
  typecheck_session qcontext M delta G ->
  delta p = Some T ->
  exists P qc, M p = Some P /\ typecheck_process (nil, nil, qc) P T.
Proof.
  intros qcontext M delta G p T Htyped Hdelta.
  unfold typecheck_session in Htyped.
  destruct Htyped as [lqc [Hreg [Hbalanced [Hassoc [Hpartition
    [Hlength [Hperm HtypedProcesses]]]]]]].
  assert (HinDelta : In (p, T) (elems participant ltt delta)).
  { apply (proj2 (specs _ _ delta) p T); exact Hdelta. }
  assert (HinM : In p (session_participants M)).
  {
    unfold session_participants.
    eapply Permutation_in; [exact Hperm|].
    apply in_map_iff; exists (p, T); split; [reflexivity|exact HinDelta].
  }
  apply in_map_iff in HinM as [[p0 P] [Hfst HinPair]].
  simpl in Hfst; subst p0.
  assert (HM : M p = Some P).
  { apply (proj2 (specs _ _ M) p P); exact HinPair. }
  destruct (typecheck_session_component_of_map qcontext M delta lqc Hperm Hlength HtypedProcesses p P HM)
    as [n [T0 [qc [Hnth [Hqc [Hdelta0 HtypedP]]]]]].
  rewrite Hdelta in Hdelta0; inversion Hdelta0; subst T0.
  exists P, qc; split; assumption.
Qed.

Lemma process_head_type_send_singleton_subtyping : forall p l e P T,
  process_head_type (p_send p l e P) (ph_send p l e) T ->
  exists context B T0,
    typecheck_expression context e B /\
    subtypeC
      (ltt_send p (fun n => if Nat.eqb n l then Some (B, T0) else None)) T.
Proof.
  intros p l e P T Hhead.
  dependent induction Hhead.
  - exists context, B, T; split; [assumption|apply stRefl].
  - destruct (IHHhead p l e P eq_refl eq_refl)
      as [context0 [B0 [T0 [Hexpr Hsub]]]].
    exists context0, B0, T0; split; [exact Hexpr|].
    eapply stTrans; eauto.
Qed.

Lemma guarded_typed_send_head_classification : forall context P q f,
  typecheck_process context P (ltt_send q f) ->
  cguardedP P -> variable_closed_process_at 0 P ->
  exists h,
    process_head_type (unravelP P) h (ltt_send q f) /\
    process_head_view_closed h /\
    process_root_view (unravelP P) = Some h /\
    (is_internal_head_view h \/
      exists l e (P' : process) (expr_context : typing_context) (B : sort)
        (T0 : ltt),
        unravelP P = p_send q l e P' /\
        typecheck_expression expr_context e B /\
        subtypeC
          (ltt_send q (fun n => if Nat.eqb n l then Some (B, T0) else None))
          (ltt_send q f)).
Proof.
  intros context P q f Htyped Hguard Hclosed.
  destruct (typecheck_process_has_head context P (ltt_send q f) Htyped)
    as [h Hhead].
  assert (Hnotvar : forall k, h <> ph_var k).
  {
    exact (process_head_type_guarded_not_var P h (ltt_send q f) nil Hhead
      (proj2 Hguard) (Forall_nil _)).
  }
  pose proof (process_head_type_unravel P h (ltt_send q f) Hhead Hguard
    Hnotvar) as HheadU.
  pose proof (process_head_type_unravel_view P h (ltt_send q f) Hhead Hguard)
    as Hroot.
  pose proof (process_head_type_closed_view P h (ltt_send q f) Hhead Hclosed)
    as Hview.
  destruct h as [lz|sp l e|sp| |dim U lz|z|e|k].
  - destruct (unravelP P) as [lz0|R|sp0 l0 e0 P0|sp0 cont0|P0
      |dim0 U0 lz0 P0|z0 P0|e0 P1 P0|k0]; simpl in Hroot; try discriminate.
    inversion Hroot; subst lz0.
    pose proof (process_head_type_end_info lz (ltt_send q f) HheadU) as Hbad.
    discriminate.
  - destruct (unravelP P) as [lz0|R|sp0 l0 e0 P0|sp0 cont0|P0
      |dim0 U0 lz0 P0|z0 P0|e0 P1 P0|k0]; simpl in Hroot; try discriminate.
    inversion Hroot; subst sp0 l0 e0.
    destruct (process_head_type_send_singleton_subtyping sp l e P0
      (ltt_send q f) HheadU)
      as [expr_context [B [T0 [Hexpr Hsub]]]].
    destruct (subtypeC_send_inv sp
      (fun n => if Nat.eqb n l then Some (B, T0) else None)
      (ltt_send q f) Hsub) as [f0 Hshape].
    inversion Hshape; subst sp.
    exists (ph_send q l e); split; [rewrite <- H1; exact HheadU|].
    split; [exact Hview|]. split; [exact Hroot|].
    right; exists l, e, P0, expr_context, B, T0.
    split; [reflexivity|]. split; [exact Hexpr|rewrite <- H1; exact Hsub].
  - destruct (unravelP P) as [lz0|R|sp0 l0 e0 P0|sp0 cont0|P0
      |dim0 U0 lz0 P0|z0 P0|e0 P1 P0|k0]; simpl in Hroot; try discriminate.
    inversion Hroot; subst sp0.
    destruct (process_head_type_recv_info sp cont0 (ltt_send q f) HheadU)
      as [f' [Htype Hcovered]].
    discriminate.
  - exists ph_newq; split; [exact HheadU|].
    split; [exact Hview|]. split; [exact Hroot|]. left; simpl; exact I.
  - exists (ph_unitary dim U lz); split; [exact HheadU|].
    split; [exact Hview|]. split; [exact Hroot|]. left; simpl; exact I.
  - exists (ph_measure z); split; [exact HheadU|].
    split; [exact Hview|]. split; [exact Hroot|]. left; simpl; exact I.
  - exists (ph_ite e); split; [exact HheadU|].
    split; [exact Hview|]. split; [exact Hroot|]. left; simpl; exact I.
  - destruct (unravelP P) as [lz0|R|sp0 l0 e0 P0|sp0 cont0|P0
      |dim0 U0 lz0 P0|z0 P0|e0 P1 P0|k0]; simpl in Hroot; discriminate.
Qed.

Lemma guarded_typed_recv_head_classification : forall context P p f,
  typecheck_process context P (ltt_recv p f) ->
  cguardedP P -> variable_closed_process_at 0 P ->
  exists h,
    process_head_type (unravelP P) h (ltt_recv p f) /\
    process_head_view_closed h /\
    process_root_view (unravelP P) = Some h /\
    (is_internal_head_view h \/
      exists (cont : slist process) (f' : fin -> option (sort * ltt)),
        unravelP P = p_recv p cont /\
        f = f' /\
        forall l B T0, f' l = Some (B, T0) -> onth l cont <> None).
Proof.
  intros context P p f Htyped Hguard Hclosed.
  destruct (typecheck_process_has_head context P (ltt_recv p f) Htyped)
    as [h Hhead].
  assert (Hnotvar : forall k, h <> ph_var k).
  {
    exact (process_head_type_guarded_not_var P h (ltt_recv p f) nil Hhead
      (proj2 Hguard) (Forall_nil _)).
  }
  pose proof (process_head_type_unravel P h (ltt_recv p f) Hhead Hguard
    Hnotvar) as HheadU.
  pose proof (process_head_type_unravel_view P h (ltt_recv p f) Hhead Hguard)
    as Hroot.
  pose proof (process_head_type_closed_view P h (ltt_recv p f) Hhead Hclosed)
    as Hview.
  destruct h as [lz|sp l e|sp| |dim U lz|z|e|k].
  - destruct (unravelP P) as [lz0|R|sp0 l0 e0 P0|sp0 cont0|P0
      |dim0 U0 lz0 P0|z0 P0|e0 P1 P0|k0]; simpl in Hroot; try discriminate.
    inversion Hroot; subst lz0.
    pose proof (process_head_type_end_info lz (ltt_recv p f) HheadU) as Hbad.
    discriminate.
  - destruct (unravelP P) as [lz0|R|sp0 l0 e0 P0|sp0 cont0|P0
      |dim0 U0 lz0 P0|z0 P0|e0 P1 P0|k0]; simpl in Hroot; try discriminate.
    inversion Hroot; subst sp0 l0 e0.
    destruct (process_head_type_send_info sp l e P0
      (ltt_recv p f) HheadU)
      as [expr_context [B [f' [T0 [Hexpr [Htype Hbranch]]]]]].
    discriminate.
  - destruct (unravelP P) as [lz0|R|sp0 l0 e0 P0|sp0 cont0|P0
      |dim0 U0 lz0 P0|z0 P0|e0 P1 P0|k0]; simpl in Hroot; try discriminate.
    inversion Hroot; subst sp0.
    destruct (process_head_type_recv_info sp cont0 (ltt_recv p f) HheadU)
      as [f' [Htype Hcovered]].
    inversion Htype; subst sp.
    exists (ph_recv p); split; [rewrite <- H1; exact HheadU|].
    split; [exact Hview|]. split; [exact Hroot|].
    right; exists cont0, f'; repeat split; assumption.
  - exists ph_newq; split; [exact HheadU|].
    split; [exact Hview|]. split; [exact Hroot|]. left; simpl; exact I.
  - exists (ph_unitary dim U lz); split; [exact HheadU|].
    split; [exact Hview|]. split; [exact Hroot|]. left; simpl; exact I.
  - exists (ph_measure z); split; [exact HheadU|].
    split; [exact Hview|]. split; [exact Hroot|]. left; simpl; exact I.
  - exists (ph_ite e); split; [exact HheadU|].
    split; [exact Hview|]. split; [exact Hroot|]. left; simpl; exact I.
  - destruct (unravelP P) as [lz0|R|sp0 l0 e0 P0|sp0 cont0|P0
      |dim0 U0 lz0 P0|z0 P0|e0 P1 P0|k0]; simpl in Hroot; discriminate.
Qed.

Lemma ctx_step_f_endpoints : forall delta delta2 p q l B,
  ctx_step_f delta p q l B delta2 ->
  p <> q /\ exists fs fr,
    delta p = Some (ltt_send q fs) /\
    delta q = Some (ltt_recv p fr).
Proof.
  intros delta delta2 p q l B Hstep.
  inversion Hstep; subst.
  split; [assumption|].
  exists xs, ys; split; assumption.
Qed.

Lemma session_fidelity_iteration_local `{good_merge} : forall
    (n : nat) (M : session) (delta : typ_ctx) (G : gtt)
    (p q : participant) (qcontext : qubit_context)
    (qstate : quantum_state) (P Q : process),
  p <> q ->
  internal_prefix_height P + internal_prefix_height Q = n ->
  M p = Some P -> M q = Some Q ->
  (exists l B delta2, ctx_step_f delta p q l B delta2) ->
  typecheck_session qcontext M delta G ->
  cguarded_session M ->
  state_only_contains_qubits_in_context qcontext qstate ->
  process_qubit_owner_agrees_by M qstate p ->
  process_qubit_owner_agrees_by M qstate q ->
  exists delta2 G2 l2 S2 qstate2 M2 pi la qcontext2,
    ctx_step_f delta p q l2 S2 delta2 /\
    gttstepC G G2 p q l2 /\
    multistep (qstate, M) la (qstate2, M2) pi /\
    typecheck_session qcontext2 M2 delta2 G2.
Proof.
  induction n using lt_wf_ind.
  intros M delta G p q qcontext qstate P Q Hneq Hrank HP HQ
    [lctx [Bctx [delta0 Hctx]]] Htyped Hguard Hstate HagreeP HagreeQ.
  destruct (ctx_step_f_endpoints delta delta0 p q lctx Bctx Hctx)
    as [Hneq_ctx [fs [fr [Hsend Hrecv]]]].
  assert (Hclosed : variable_closed_session M).
  { eapply typecheck_session_closed; exact Htyped. }
  destruct (typecheck_session_component_at_delta qcontext M delta G p P
    (ltt_send q fs) Htyped HP Hsend) as [qcP HtypedP].
  destruct (typecheck_session_component_at_delta qcontext M delta G q Q
    (ltt_recv p fr) Htyped HQ Hrecv) as [qcQ HtypedQ].
  pose proof (Hguard p P HP) as HguardP.
  pose proof (Hguard q Q HQ) as HguardQ.
  pose proof (Hclosed p P HP) as HclosedP.
  pose proof (Hclosed q Q HQ) as HclosedQ.
  assert (Hcovers : state_covers_qubits_in_context qcontext qstate).
  {
    unfold state_covers_qubits_in_context.
    intros qubit Hqubitctx.
    unfold state_only_contains_qubits_in_context in Hstate.
    apply (proj1 (Hstate qubit)); exact Hqubitctx.
  }
  pose proof (process_qubits_available_from_typed_session M delta G qcontext
    qstate p P Htyped HP Hcovers HagreeP) as HownedP.
  pose proof (process_qubits_available_from_typed_session M delta G qcontext
    qstate q Q Htyped HQ Hcovers HagreeQ) as HownedQ.
  destruct (guarded_typed_send_head_classification (nil, nil, qcP) P q fs
    HtypedP HguardP HclosedP)
    as [hP [HheadP [HviewP [HrootP HclassP]]]].
  destruct (guarded_typed_recv_head_classification (nil, nil, qcQ) Q p fr
    HtypedQ HguardQ HclosedQ)
    as [hQ [HheadQ [HviewQ [HrootQ HclassQ]]]].
  destruct HclassP as [HinternalP|HsendP].
  -
    assert (HavailableP : forall qubit,
        process_head_uses_qubit hP qubit ->
        exists n0, quantum_map_of qstate qubit = Some (p, n0)).
    {
      intros qubit Huses.
      pose proof (process_head_uses_qubit_free (unravelP P) hP qubit
        HrootP Huses) as HinU.
      pose proof (free_qubits_unravel P HguardP qubit HinU) as HinP.
      eapply HownedP; eauto.
    }
    destruct (progress_internal_transition_on_state M p P hP
      (ltt_send q fs) qstate HP HguardP HclosedP HheadP HviewP HrootP
      HinternalP HavailableP)
      as [qstate1 [M1 [pi1 [Pafter [Hstep1 [HPafter Hdrop]]]]]].
    destruct (subject_reduction_via_association_1  M M1 pi1 qstate qstate1
      delta p qcontext G Hstep1 Htyped Hstate)
      as [qcontext1 [Htyped1 Hstate1]].
    pose proof (cguarded_session_after_tau M M1 qstate qstate1 p pi1
      Hstep1 Hguard) as Hguard1.
    pose proof (process_qubit_owner_agrees_by_after_tau_for qstate M qstate1
      M1 p pi1 p Hstep1 (or_introl eq_refl) HownedP) as HagreeP1.
    pose proof (process_qubit_owner_agrees_by_after_tau_for qstate M qstate1
      M1 p pi1 q Hstep1 (or_intror Hneq) HownedQ) as HagreeQ1.
    destruct (typecheck_session_has_delta_component qcontext1 M1 delta G p
      (ltt_send q fs) Htyped1 Hsend)
      as [P1 [qcP1 [HP1 HtypedP1]]].
    destruct (typecheck_session_has_delta_component qcontext1 M1 delta G q
      (ltt_recv p fr) Htyped1 Hrecv)
      as [Q1 [qcQ1 [HQ1 HtypedQ1]]].
    pose proof (internal_prefix_height_tau_nonincreasing_for qstate M
      qstate1 M1 p pi1 q Hstep1 Hneq Hguard Q Q1 HQ HQ1) as Hother.
    rewrite HP1 in HPafter; inversion HPafter; subst Pafter.
    set (n1 := internal_prefix_height P1 + internal_prefix_height Q1).
    assert (Hrank1 : internal_prefix_height P1 + internal_prefix_height Q1 = n1)
      by reflexivity.
    assert (Hlt : n1 < n).
    {
      unfold n1; rewrite <- Hrank; simpl; lia.
    }
    destruct (H n1 Hlt M1 delta G p q qcontext1 qstate1 P1 Q1
      Hneq Hrank1 HP1 HQ1 (ex_intro _ lctx (ex_intro _ Bctx
        (ex_intro _ delta0 Hctx))) Htyped1 Hguard1 Hstate1 HagreeP1
      HagreeQ1)
      as [delta2 [G2 [l2 [S2 [qstate2 [M2 [pi2 [la [qcontext2
        [Hctx2 [Hgstep2 [Hmulti2 Htyped2]]]]]]]]]]]].
    exists delta2, G2, l2, S2, qstate2, M2, (pi1 * pi2)%R,
      (Tau p :: la), qcontext2.
    split; [exact Hctx2|]. split; [exact Hgstep2|].
    split; [eapply ms_step; [exact Hstep1|exact Hmulti2]|exact Htyped2].
  - destruct HclassQ as [HinternalQ|HrecvQ].
    +
      assert (HavailableQ : forall qubit,
          process_head_uses_qubit hQ qubit ->
          exists n0, quantum_map_of qstate qubit = Some (q, n0)).
      {
        intros qubit Huses.
        pose proof (process_head_uses_qubit_free (unravelP Q) hQ qubit
          HrootQ Huses) as HinU.
        pose proof (free_qubits_unravel Q HguardQ qubit HinU) as HinQ.
        eapply HownedQ; eauto.
      }
      destruct (progress_internal_transition_on_state M q Q hQ
        (ltt_recv p fr) qstate HQ HguardQ HclosedQ HheadQ HviewQ HrootQ
        HinternalQ HavailableQ)
        as [qstate1 [M1 [pi1 [Qafter [Hstep1 [HQafter Hdrop]]]]]].
      destruct (subject_reduction_via_association_1 M M1 pi1 qstate qstate1
        delta q qcontext G Hstep1 Htyped Hstate)
        as [qcontext1 [Htyped1 Hstate1]].
      pose proof (cguarded_session_after_tau M M1 qstate qstate1 q pi1
        Hstep1 Hguard) as Hguard1.
      pose proof (process_qubit_owner_agrees_by_after_tau_for qstate M qstate1
        M1 q pi1 p Hstep1
        (or_intror (fun Heq => Hneq (eq_sym Heq))) HownedP) as HagreeP1.
      pose proof (process_qubit_owner_agrees_by_after_tau_for qstate M qstate1
        M1 q pi1 q Hstep1 (or_introl eq_refl) HownedQ) as HagreeQ1.
      destruct (typecheck_session_has_delta_component qcontext1 M1 delta G p
        (ltt_send q fs) Htyped1 Hsend)
        as [P1 [qcP1 [HP1 HtypedP1]]].
      destruct (typecheck_session_has_delta_component qcontext1 M1 delta G q
        (ltt_recv p fr) Htyped1 Hrecv)
        as [Q1 [qcQ1 [HQ1 HtypedQ1]]].
      pose proof (internal_prefix_height_tau_nonincreasing_for qstate M
        qstate1 M1 q pi1 p Hstep1
        ltac:(intro Heq; apply Hneq; exact (eq_sym Heq)) Hguard P P1 HP HP1)
        as Hother.
      rewrite HQ1 in HQafter; inversion HQafter; subst Qafter.
      set (n1 := internal_prefix_height P1 + internal_prefix_height Q1).
      assert (Hrank1 : internal_prefix_height P1 + internal_prefix_height Q1 = n1)
        by reflexivity.
      assert (Hlt : n1 < n).
      {
        unfold n1; rewrite <- Hrank; simpl; lia.
      }
      destruct (H n1 Hlt M1 delta G p q qcontext1 qstate1 P1 Q1
        Hneq Hrank1 HP1 HQ1 (ex_intro _ lctx (ex_intro _ Bctx
          (ex_intro _ delta0 Hctx))) Htyped1 Hguard1 Hstate1 HagreeP1
        HagreeQ1)
        as [delta2 [G2 [l2 [S2 [qstate2 [M2 [pi2 [la [qcontext2
          [Hctx2 [Hgstep2 [Hmulti2 Htyped2]]]]]]]]]]]].
      exists delta2, G2, l2, S2, qstate2, M2, (pi1 * pi2)%R,
        (Tau q :: la), qcontext2.
      split; [exact Hctx2|]. split; [exact Hgstep2|].
      split; [eapply ms_step; [exact Hstep1|exact Hmulti2]|exact Htyped2].
    + destruct HrecvQ as [cont [fr_head [HrootRecv [HrecvTypesEq HrecvCovered]]]].
      destruct (typecheck_session_component_at_delta qcontext M delta G p P
        (ltt_send q fs) Htyped HP Hsend) as [qcP' HtypedP'].
      pose proof Htyped as HtypedParts.
      unfold typecheck_session in HtypedParts.
      destruct HtypedParts as [lqc [Hreg [Hbalanced [Hassoc [Hpartition
        [Hlength [Hperm HtypedProcesses]]]]]]].
      destruct HsendP as [l [e [Psend [expr_context [B [Tsend
        [HrootSend [Hexpr HsubSend]]]]]]]].
      destruct (associated_send_recv_branch delta G p q l B Tsend fr
        (ltt_send q fs) (ltt_recv p fr) Hbalanced Hassoc Hsend Hrecv
        HsubSend (stRefl (ltt_recv p fr)))
        as [fs' [fr' [Tsend' [Trecv' [HshapeSend [HshapeRecv
          [HbranchSend [HbranchRecv HsubCont]]]]]]]].
      injection HshapeSend as HfsEq.
      injection HshapeRecv as HfrEq.
      assert (HrecvActive : onth l cont <> None).
      {
        apply (HrecvCovered l B Trecv').
        assert (HrecvBranchLocal : fr l = Some (B, Trecv')).
        { rewrite <- HfrEq in HbranchRecv; exact HbranchRecv. }
        rewrite HrecvTypesEq in HrecvBranchLocal.
        exact HrecvBranchLocal.
      }
      destruct (onth l cont) as [Qbranch|] eqn:HbranchProcess.
      * destruct (cguardedP_unfolds P HguardP) as [_ [HpreP _]].
        destruct (cguardedP_unfolds Q HguardQ) as [_ [HpreQ _]].
        assert (Hsendpre : precongP P (p_send q l e Psend)).
        { rewrite <- HrootSend; exact HpreP. }
        assert (Hrecvpre : precongP Q (p_recv p cont)).
        { rewrite <- HrootRecv; exact HpreQ. }
        assert (HviewSend : closed_expression_at 0 e).
        {
          rewrite HrootSend in HrootP; simpl in HrootP.
          inversion HrootP; subst hP; exact HviewP.
        }
        destruct (closed_expression_evaluates expr_context e B Hexpr HviewSend)
          as [v [Hevaluate Hsort]].
        destruct B as [| |].
        -- destruct v as [n0|b|qv].
           ++ inversion Hsort; subst.
              set (Qafter := subst_expression_in_process 0 0
                (Val (Primitives.Nat n0)) Qbranch).
              set (Sbase := insert (KEQ:=participant_dec)
                (insert (KEQ:=participant_dec) M q (p_recv p cont)) p
                (p_send q l e Psend)).
              set (Safter := insert (KEQ:=participant_dec)
                (insert (KEQ:=participant_dec) Sbase q Qafter) p Psend).
              assert (Hinner : step (qstate, Sbase)
                (Transmit p q l (Primitives.Nat n0))
                (qstate, Safter) 1%R).
              { unfold Sbase, Safter, Qafter.
                eapply Comm_C with (p := p) (q := q) (l := l)
                  (e := e) (P := Psend) (lQ := cont) (Q := Qbranch)
                  (v := Primitives.Nat n0) (s1 := Sbase) (q_state := qstate).
                - exact l.
                - unfold Sbase; rewrite insert_eq; reflexivity.
                - unfold Sbase; rewrite insert_neq by congruence.
                  rewrite insert_eq; reflexivity.
                all: try (intros; discriminate).
                all: eauto. }
              pose proof (step_after_unfold_two M p q P Q
                (p_send q l e Psend) (p_recv p cont) Psend Qafter
                qstate qstate (Transmit p q l (Primitives.Nat n0)) 1%R
                Hneq HP HQ Hsendpre Hrecvpre Hinner) as Hstep.
              destruct (subject_reduction_via_association_2 M Safter 1%R
                qstate qstate delta G p q l (Primitives.Nat n0) qcontext
                Hstep Htyped)
                as [qcontext2 [delta2 [G2 [e2 [S2 [HstateRel [Hinclude
                  [Hctx2 [Hgstep2 [Heval2 [Htypeexpr Htyped2]]]]]]]]]]].
              exists delta2, G2, l, S2, qstate, Safter, 1%R,
                (Transmit p q l (Primitives.Nat n0) :: nil), qcontext.
              split; [exact Hctx2|]. split; [exact Hgstep2|].
              split.
              { replace 1%R with (1%R * 1%R)%R by
                  (rewrite Rmult_1_l; reflexivity).
                eapply ms_step; [exact Hstep|].
                apply ms_refl; apply equivalent_refl. }
              exact Htyped2.
           ++ inversion Hsort.
           ++ inversion Hsort.
        -- destruct v as [n0|b|qv].
           ++ inversion Hsort.
           ++ inversion Hsort; subst.
              set (Qafter := subst_expression_in_process 0 0
                (Val (Primitives.Bool b)) Qbranch).
              set (Sbase := insert (KEQ:=participant_dec)
                (insert (KEQ:=participant_dec) M q (p_recv p cont)) p
                (p_send q l e Psend)).
              set (Safter := insert (KEQ:=participant_dec)
                (insert (KEQ:=participant_dec) Sbase q Qafter) p Psend).
              assert (Hinner : step (qstate, Sbase)
                (Transmit p q l (Primitives.Bool b))
                (qstate, Safter) 1%R).
              { unfold Sbase, Safter, Qafter.
                eapply Comm_C with (p := p) (q := q) (l := l)
                  (e := e) (P := Psend) (lQ := cont) (Q := Qbranch)
                  (v := Primitives.Bool b) (s1 := Sbase) (q_state := qstate).
                - exact l.
                - unfold Sbase; rewrite insert_eq; reflexivity.
                - unfold Sbase; rewrite insert_neq by congruence.
                  rewrite insert_eq; reflexivity.
                all: try (intros; discriminate).
                all: eauto. }
              pose proof (step_after_unfold_two M p q P Q
                (p_send q l e Psend) (p_recv p cont) Psend Qafter
                qstate qstate (Transmit p q l (Primitives.Bool b)) 1%R
                Hneq HP HQ Hsendpre Hrecvpre Hinner) as Hstep.
              destruct (subject_reduction_via_association_2 M Safter 1%R
                qstate qstate delta G p q l (Primitives.Bool b) qcontext
                Hstep Htyped)
                as [qcontext2 [delta2 [G2 [e2 [S2 [HstateRel [Hinclude
                  [Hctx2 [Hgstep2 [Heval2 [Htypeexpr Htyped2]]]]]]]]]]].
              exists delta2, G2, l, S2, qstate, Safter, 1%R,
                (Transmit p q l (Primitives.Bool b) :: nil), qcontext.
              split; [exact Hctx2|]. split; [exact Hgstep2|].
              split.
              { replace 1%R with (1%R * 1%R)%R by
                  (rewrite Rmult_1_l; reflexivity).
                eapply ms_step; [exact Hstep|].
                apply ms_refl; apply equivalent_refl. }
              exact Htyped2.
           ++ inversion Hsort.
        -- destruct v as [n0|b|qv].
           ++ inversion Hsort.
           ++ inversion Hsort.
           ++ inversion Hsort; subst.
              assert (He_literal : e = Val (QVal qv)).
              { eapply eval_qubit_value_is_literal; exact Hevaluate. }
              subst e.
              assert (HfreeU : In qv (free_qubits (unravelP P))).
              { rewrite HrootSend; simpl; left; reflexivity. }
              pose proof (free_qubits_unravel P HguardP qv HfreeU) as HfreeP.
              destruct (HownedP P HP qv HfreeP) as [n0 Hlookup].
              set (qstate2 := transfer_qubit_from_lookup
                (quantum_map_of qstate) (proj2_sig (projT1 qstate))
                (proj1_sig (projT2 qstate)) (proj2_sig (projT2 qstate))
                q qv p n0 Hlookup).
              set (Qafter := subst_expression_in_process 0 0
                (Val (Primitives.QVal qv)) Qbranch).
              set (Sbase := insert (KEQ:=participant_dec)
                (insert (KEQ:=participant_dec) M q (p_recv p cont)) p
                (p_send q l (Val (Primitives.QVal qv)) Psend)).
              set (Safter := insert (KEQ:=participant_dec)
                (insert (KEQ:=participant_dec) Sbase q Qafter) p Psend).
              assert (Hinner : step (qstate, Sbase)
                (Transmit p q l (Primitives.QVal qv))
                (qstate2, Safter) 1%R).
              { unfold Sbase, Safter, Qafter, qstate2.
                eapply Comm_Q with (p := p) (q := q) (l := l)
                  (e := Val (Primitives.QVal qv)) (P := Psend)
                  (lQ := cont) (Q := Qbranch)
                  (v := qv) (s1 := Sbase) (q_state := qstate)
                  (q_state' := transfer_qubit_from_lookup
                    (quantum_map_of qstate) (proj2_sig (projT1 qstate))
                    (proj1_sig (projT2 qstate)) (proj2_sig (projT2 qstate))
                    q qv p n0 Hlookup)
                  (n := n0) (Hlookup := Hlookup).
                - exact l.
                - unfold Sbase; rewrite insert_eq; reflexivity.
                - unfold Sbase; rewrite insert_neq by congruence.
                  rewrite insert_eq; reflexivity.
                all: eauto. }
              pose proof (step_after_unfold_two M p q P Q
                (p_send q l (Val (Primitives.QVal qv)) Psend)
                (p_recv p cont) Psend Qafter
                qstate qstate2 (Transmit p q l (Primitives.QVal qv)) 1%R
                Hneq HP HQ Hsendpre Hrecvpre Hinner) as Hstep.
              destruct (subject_reduction_via_association_2 M Safter 1%R
                qstate qstate2 delta G p q l (Primitives.QVal qv) qcontext
                Hstep Htyped)
                as [qcontext2 [delta2 [G2 [e2 [S2 [HstateRel [Hinclude
                  [Hctx2 [Hgstep2 [Heval2 [Htypeexpr Htyped2]]]]]]]]]]].
              exists delta2, G2, l, S2, qstate2, Safter, 1%R,
                (Transmit p q l (Primitives.QVal qv) :: nil), qcontext.
              split; [exact Hctx2|]. split; [exact Hgstep2|].
              split.
              { replace 1%R with (1%R * 1%R)%R by
                  (rewrite Rmult_1_l; reflexivity).
                eapply ms_step; [exact Hstep|].
                apply ms_refl; apply equivalent_refl. }
              exact Htyped2.
      * exfalso; contradiction.
Qed.

Theorem session_fidelity_via_association `{good_merge}:
forall M delta G p q qcontext,
typecheck_session qcontext M delta G ->
(forall pt P, M pt = Some P -> cguardedP P) ->
(exists l B delta2, ctx_step_f delta p q l B delta2) ->

exists delta2 G2 l2 S2,
ctx_step_f delta p q l2 S2 delta2 /\
gttstepC G G2 p q l2 /\
(exists qstate qstate2 pi qcontext2 M2 la,
multistep (qstate, M) la (qstate2, M2) pi /\
typecheck_session qcontext2 M2 delta2 G2).
Proof.
  intros M delta G p q qcontext Htyped Hguard Hctx_exists.
  destruct Hctx_exists as [l0 [B0 [delta0 Hctx0]]].
  destruct (ctx_step_f_endpoints delta delta0 p q l0 B0 Hctx0)
    as [Hneq [fs [fr [Hsend Hrecv]]]].
  destruct (typecheck_session_has_delta_component qcontext M delta G p
    (ltt_send q fs) Htyped Hsend)
    as [P [qcP [HP HtypedP]]].
  destruct (typecheck_session_has_delta_component qcontext M delta G q
    (ltt_recv p fr) Htyped Hrecv)
    as [Q [qcQ [HQ HtypedQ]]].
  destruct (session_fidelity_initial_state_from_session M delta G qcontext
    p q P Q Htyped HP HQ Hneq)
    as [qstate [Hstate [HownedP HownedQ]]].
  assert (HownedPAll : process_qubits_owned_by M qstate p).
  {
    unfold process_qubits_owned_by; intros P0 Hmap qubit Hin.
    rewrite HP in Hmap; inversion Hmap; subst P0; exact (HownedP qubit Hin).
  }
  assert (HownedQAll : process_qubits_owned_by M qstate q).
  {
    unfold process_qubits_owned_by; intros Q0 Hmap qubit Hin.
    rewrite HQ in Hmap; inversion Hmap; subst Q0; exact (HownedQ qubit Hin).
  }
  pose proof (process_qubit_owner_agreement_of_owned M qstate p HownedPAll)
    as HagreeP.
  pose proof (process_qubit_owner_agreement_of_owned M qstate q HownedQAll)
    as HagreeQ.
  set (n := internal_prefix_height P + internal_prefix_height Q).
  assert (Hrank : internal_prefix_height P + internal_prefix_height Q = n)
    by reflexivity.
  destruct (session_fidelity_iteration_local n M delta G p q qcontext qstate
    P Q Hneq Hrank HP HQ
    (ex_intro _ l0 (ex_intro _ B0 (ex_intro _ delta0 Hctx0))) Htyped
    (fun pt P0 Hlookup => Hguard pt P0 Hlookup) Hstate HagreeP HagreeQ)
    as [delta2 [G2 [l2 [S2 [qstate2 [M2 [pi [la [qcontext2
      [Hctx2 [Hgstep2 [Hmulti Htyped2]]]]]]]]]]]].
  exists delta2, G2, l2, S2.
  split; [exact Hctx2|]. split; [exact Hgstep2|].
  exists qstate, qstate2, pi, qcontext2, M2, la.
  split; [exact Hmulti|exact Htyped2].
Qed.

Theorem deadlock_freedom `{good_merge}:
forall G delta q_context M,
typecheck_session q_context M delta G ->
variable_closed_session M ->
(forall p P, M p = Some P -> cguardedP P) ->
finished M \/
forall qs1,
  state_covers_qubits_in_context q_context qs1 ->
  (forall p, process_qubit_owner_agrees_by M qs1 p) ->
  exists qs2 a M' pi, step (qs1, M) a (qs2, M') pi.
Proof.
  intros G delta q_context M Htyped Hclosed Hguard.
  destruct (type_safety G delta q_context M Htyped Hclosed Hguard)
    as [Hfinished | [qstate0 [qstate1 [a [M1 [pi Hstep]]]]]].
  - left; exact Hfinished.
  - right; intros qstate Hsupport Hagree.
    assert (Hcovers : state_covers_qubits_in_context q_context qstate).
    { exact Hsupport. }
    destruct a as [p | p q l v].
    + pose proof (process_qubits_available_from_typed_session_context
        q_context M delta G qstate p Htyped Hcovers (Hagree p)) as Howned.
      destruct (replay_tau_step_on_state qstate0 M qstate1 M1 p pi
        qstate Hstep Howned) as [qstate2 [M2 [pi2 Hstep2]]].
      exists qstate2, (Tau p), M2, pi2; exact Hstep2.
    + pose proof (process_qubits_available_from_typed_session_context
        q_context M delta G qstate p Htyped Hcovers (Hagree p)) as Howned.
      destruct (replay_transmit_step_on_state qstate0 M qstate1 M1
        p q l v pi qstate Hstep Howned) as [qstate2 [M2 Hstep2]].
      exists qstate2, (Transmit p q l v), M2, 1%R; exact Hstep2.
Qed.

Lemma qubit_map_key_present_iff : forall
    (qm : finite_map qubit_reference (participant * nat)) q,
  qm q <> None <-> In q (map fst (elems qubit_reference (participant * nat) qm)).
Proof.
  intros qm q; split.
  - intro Hpresent.
    destruct (qm q) as [[owner n]|] eqn:Hlookup; [|contradiction].
    apply in_map_iff.
    exists (q, (owner, n)); split; [reflexivity|].
    exact (proj2 (proj2 (specs qubit_reference (participant * nat) qm)
      q (owner, n)) Hlookup).
  - intro Hin.
    apply in_map_iff in Hin as [[q' value] [Heq Hin]].
    simpl in Heq; subst q'.
    destruct value as [owner n].
    pose proof (proj1 (proj2 (specs qubit_reference (participant * nat) qm)
      q (owner, n)) Hin) as Hlookup.
    rewrite Hlookup; discriminate.
Qed.

Lemma qubit_context_key_present_iff : forall
    (context : qubit_context) q,
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

Lemma zero_state_exactly_on_context : forall
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
    rewrite qubit_context_key_present_iff.
    change (In q keys <-> quantum_map_of (proj1_sig zstate) q <> None).
    rewrite qubit_map_key_present_iff.
    rewrite (proj2_sig zstate).
    rewrite in_rev.
    tauto.
  - intros q Hcontext.
    apply qubit_context_key_present_iff in Hcontext.
    unfold keys in Hcontext.
    unfold zstate.
    eapply zero_state_for_qubits_owner_lookup; eauto.
Qed.
