From SQIR Require Import SQIR UnitaryOps.
From QuantumLib Require Import Matrix CauchySchwarz.
Require Import Lia Permutation Reals List.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import SST session substitution balanced.
Require Import QUEST.
Require Import Progress SessionFidelity SubjectReduction QuantumPropertiesCore QuantumProperties.
From Paco Require Import paco.

  Notation sess_path := (stream session).

  Definition live_path_s (M: session) p := 
    (forall P pt lb ex P', M p = Some P -> P = p_send pt lb ex P' -> exists la qstate qstate' pi M', multistep (qstate, M) la (qstate',M') pi /\ M' p = Some P') /\
    (forall P pt xs, M p = Some P -> P = p_recv pt xs -> exists n P', onth n xs = Some P' /\ exists la qstate qstate' pi M' v, multistep (qstate, M) la (qstate',M') pi /\ M' p = Some (subst_expression_in_process 0 0 (Val v) P')).
    
  Definition live_sess_0 M := forall M' p P, multi unfoldM M M' -> M' p = Some P -> live_path_s M' p.

  Definition qubit_context_keys (qc : qubit_context) :=
    map fst (elems qubit_reference unit qc).

  Definition owned_qubits_of_components (delta : typing_context)
      (lqc : list qubit_context) : list (participant * qubit_reference) :=
    flat_map
      (fun item =>
        map (fun qv => (fst (fst item), fst qv))
          (elems qubit_reference unit (snd item)))
      (combine (elems participant ltt delta) lqc).

  Lemma owned_qubits_of_components_keys : forall delta lqc,
      length (elems participant ltt delta) = length lqc ->
      map snd (owned_qubits_of_components delta lqc) =
      flat_map qubit_context_keys lqc.
  Proof.
    intros delta lqc Hlen.
    unfold owned_qubits_of_components, qubit_context_keys.
    revert lqc Hlen.
    induction (elems participant ltt delta) as [|e es IH];
      intros [|qc qcs] Hlen; simpl in Hlen; try lia.
    - reflexivity.
    - simpl. rewrite map_app. simpl. f_equal.
      + rewrite map_map. simpl. reflexivity.
      + apply IH. lia.
  Qed.

  Lemma flat_map_qubit_context_keys_nodup : forall (lqc : list qubit_context),
      (forall i j qc1 qc2, i <> j ->
        nth_error lqc i = Some qc1 -> nth_error lqc j = Some qc2 ->
        forall q, qc1 q <> None -> qc2 q = None) ->
      NoDup (flat_map qubit_context_keys lqc).
  Proof.
    induction lqc as [|qc lqc IH]; intros Hdisjoint; simpl.
    - constructor.
    - apply NoDup_app.
      repeat split.
      + unfold qubit_context_keys. apply (proj1 (specs qubit_reference unit qc)).
      + apply IH. intros i j qc1 qc2 Hneq Hi Hj q Hqc.
        eapply Hdisjoint with (i := S i) (j := S j); simpl; eauto; lia.
      + intros q Hhead Htail.
        apply in_flat_map in Htail as [qc2 [Hin Hkeys]].
        apply In_nth_error in Hin as [j Hnth].
        assert (HqcLookup : qc q = Some tt).
        { apply (proj2 (qubit_context_key_present_iff qc q)); exact Hhead. }
        assert (Hqc2Lookup : qc2 q = Some tt).
        { apply (proj2 (qubit_context_key_present_iff qc2 q)); exact Hkeys. }
        assert (Hqc : qc q <> None) by congruence.
        assert (Hqc2 : qc2 q <> None) by congruence.
        pose proof (Hdisjoint 0 (S j) qc qc2 ltac:(lia) eq_refl Hnth q Hqc)
          as Hnone.
        congruence.
  Qed.

  Lemma typed_session_initial_owned_state `{good_merge} : forall
      qcontext M delta G,
      typecheck_session qcontext M delta G ->
      exists qstate,
        state_only_contains_qubits_in_context qcontext qstate /\
        (forall p P, M p = Some P -> forall q,
          In q (free_qubits P) ->
          exists n, quantum_map_of qstate q = Some (p, n)).
  Proof.
    intros qcontext M delta G Htyped.
    unfold typecheck_session in Htyped.
    destruct Htyped as [lqc [Hreg [Hbalanced [Hassoc [Hpartition
      [Hlength [Hperm Hcomponents]]]]]]].
    assert (Hkeys_nd : NoDup (flat_map qubit_context_keys lqc)).
    {
      eapply flat_map_qubit_context_keys_nodup.
      intros i j qc1 qc2 Hneq Hi Hj q Hqc.
      unfold FMap.partition in Hpartition.
      destruct Hpartition as [_ Hdisjoint].
      specialize (Hdisjoint i j qc1 qc2 Hneq Hi Hj q).
      destruct Hdisjoint as [Hforward _].
      specialize (Hforward Hqc).
      exact Hforward.
    }
    set (owned := owned_qubits_of_components delta lqc).
    assert (Howned_nd : NoDup (map snd owned)).
    {
      unfold owned.
      rewrite owned_qubits_of_components_keys by (symmetry; exact Hlength).
      exact Hkeys_nd.
    }
    set (zstate := zero_state_for_owned_qubits owned Howned_nd).
    destruct (proj2_sig zstate) as [Hstate_keys Howners].
    exists (proj1_sig zstate).
    split.
    - unfold state_only_contains_qubits_in_context.
      intro q; split; intro Hctx.
      + pose proof (proj1 (qubit_context_key_present_iff qcontext q) Hctx)
          as Hcontext_key.
        unfold FMap.partition in Hpartition.
        destruct Hpartition as [Hcovers _].
        destruct (Hcovers q tt) as [Hcover _].
        destruct (Hcover Hctx) as [qc [Hqc_in Hqc_lookup]].
        assert (Hkey : In q (flat_map qubit_context_keys lqc)).
        {
          apply in_flat_map; exists qc; split; [exact Hqc_in|].
          apply (proj1 (qubit_context_key_present_iff qc q)); exact Hqc_lookup.
        }
        unfold owned in Hkey.
        rewrite <- (owned_qubits_of_components_keys delta lqc
          ltac:(symmetry; exact Hlength)) in Hkey.
        apply in_map_iff in Hkey as [[owner q0] [Heq Hin_owned]].
        simpl in Heq; subst q0.
        destruct (Howners owner q Hin_owned) as [n Hlookup].
        change (quantum_map_of (proj1_sig zstate) q <> None).
        rewrite Hlookup; discriminate.
      + destruct (quantum_map_of (proj1_sig zstate) q) as [[owner n]|]
          eqn:Hlookup; [|contradiction].
        assert (Hpresent : quantum_map_of (proj1_sig zstate) q <> None)
          by (rewrite Hlookup; discriminate).
        apply (proj1 (qubit_map_key_present_iff
          (quantum_map_of (proj1_sig zstate)) q)) in Hpresent as Hstate_key.
        rewrite Hstate_keys in Hstate_key.
        apply in_rev_elim in Hstate_key.
        unfold owned in Hstate_key.
        rewrite (owned_qubits_of_components_keys delta lqc
          ltac:(symmetry; exact Hlength)) in Hstate_key.
        apply in_flat_map in Hstate_key as [qc [Hqc_in Hqc_key]].
        assert (Hqc_lookup : qc q = Some tt).
        { apply (proj2 (qubit_context_key_present_iff qc q)); exact Hqc_key. }
        unfold FMap.partition in Hpartition.
        destruct Hpartition as [Hcovers _].
        apply (proj2 (Hcovers q tt)).
        exists qc; split; assumption.
    - intros p P Hlookup q Hin.
      destruct (typecheck_session_component_of_map qcontext M delta lqc
        Hperm Hlength Hcomponents p P Hlookup)
        as [i [T [qc [Hdelta_at [Hqc_at [Hdelta_lookup HtypedP]]]]]].
      assert (HinDelta : In (p, T) (elems participant ltt delta)).
      { apply nth_error_In with (n := i); exact Hdelta_at. }
      assert (Hlength_le : length (elems participant ltt delta) <= length lqc)
        by lia.
      destruct (in_combine_ex_r (elems participant ltt delta) lqc
        Hlength_le (p, T) HinDelta) as [qc' Hentry].
      destruct (Hcomponents p T qc' Hentry) as [P' [Hmap HtypedP']].
      rewrite Hlookup in Hmap; inversion Hmap; subst P'.
      pose proof (typecheck_process_free_qubits P (nil, nil, qc') T HtypedP' q Hin)
        as Hlocal.
      unfold in_qubit_context in Hlocal; simpl in Hlocal.
      assert (Howned : In (p, q) owned).
      {
        unfold owned, owned_qubits_of_components.
        apply in_flat_map; exists ((p, T), qc'); split; [exact Hentry|].
        apply in_map_iff; exists (q, tt); split; [reflexivity|].
        exact (proj2 (proj2 (specs qubit_reference unit qc') q tt) Hlocal).
      }
      destruct (Howners p q Howned) as [n Hqstate].
      exists n; exact Hqstate.
  Qed.

  Lemma cguarded_session_after_transmit : forall
      qstate M qstate' M' p q l v pi,
      step (qstate, M) (Transmit p q l v) (qstate', M') pi ->
      cguarded_session M -> cguarded_session M'.
  Proof.
    intros qstate M qstate' M' p q l v pi Hstep.
    refine (step_ind
      (fun s1 a s2 r =>
        a = Transmit p q l v ->
        cguarded_session (snd s1) -> cguarded_session (snd s2))
      _ _ _ _ _ _ _ _ (qstate, M) (Transmit p q l v) (qstate', M') pi
      Hstep eq_refl).
    - intros p0 q0 l0 e P lQ l0' Q v0 s1 qs Hsend Hrecv Hneq Hnth
        Heval Hnotq Q' s2 Hact Hguard.
      inversion Hact; subst.
      unfold cguarded_session in *.
      intros pt P' Htarget.
      destruct (participant_dec pt p) as [->|Hptp].
      + change (insert (insert s1 q Q') p P p = Some P') in Htarget.
        rewrite insert_eq in Htarget; inversion Htarget; subst P'.
        eapply cguardedP_after_send.
        eapply Hguard; exact Hsend.
      + destruct (participant_dec pt q) as [->|Hptq].
        * change (insert (insert s1 q Q') p P q = Some P') in Htarget.
          rewrite insert_neq in Htarget by congruence.
          rewrite insert_eq in Htarget; inversion Htarget; subst P'.
          eapply cguardedP_after_subst_expr.
          eapply cguardedP_after_recv; [eapply Hguard; exact Hrecv|exact Hnth].
        * change (insert (insert s1 q Q') p P pt = Some P') in Htarget.
          rewrite insert_neq in Htarget by congruence.
          rewrite insert_neq in Htarget by congruence.
          eapply Hguard; exact Htarget.
    - intros p0 q0 l0 e P lQ l0' Q v0 s1 qs qs' n Hlookup
        Hsend Hrecv Hneq Hnth Heval Htransfer Q' s2 Hact Hguard.
      inversion Hact; subst.
      unfold cguarded_session in *.
      intros pt P' Htarget.
      destruct (participant_dec pt p) as [->|Hptp].
      + change (insert (insert s1 q Q') p P p = Some P') in Htarget.
        rewrite insert_eq in Htarget; inversion Htarget; subst P'.
        eapply cguardedP_after_send.
        eapply Hguard; exact Hsend.
      + destruct (participant_dec pt q) as [->|Hptq].
        * change (insert (insert s1 q Q') p P q = Some P') in Htarget.
          rewrite insert_neq in Htarget by congruence.
          rewrite insert_eq in Htarget; inversion Htarget; subst P'.
          eapply cguardedP_after_subst_expr.
          eapply cguardedP_after_recv; [eapply Hguard; exact Hrecv|exact Hnth].
        * change (insert (insert s1 q Q') p P pt = Some P') in Htarget.
          rewrite insert_neq in Htarget by congruence.
          rewrite insert_neq in Htarget by congruence.
          eapply Hguard; exact Htarget.
    - intros p0 P s1 qs qnew Hfresh Hsrc qs2 s2 Hact Hguard.
      discriminate.
    - intros p0 e P1 P0 s1 qs Hsrc Heval s2 Hact Hguard.
      discriminate.
    - intros p0 e P1 P0 s1 qs Hsrc Heval s2 Hact Hguard.
      discriminate.
    - intros p0 q0 P s1 qs qs' n r pi0 Hlookup Hlen Hnonzero Hsrc
        Hmeasure s2 Hact Hguard.
      discriminate.
    - intros dim p0 U lqs P s1 qs qs' Hlen Hdim Hsrc Happly Hnd
        Howned s2 Hact Hguard.
      discriminate.
    - intros M0 M0' M1 qs qs' a r Hunfold Hinner IH Hact Hguard.
      inversion Hact; subst.
      pose proof (cguarded_session_unfoldM M0 M0' Hunfold Hguard) as Hmiddle.
      eapply IH; eauto.
  Qed.

  Lemma typed_qubit_send_continuation_no_sent_qubit `{good_merge} : forall
      qcontext M delta G p q l sent P,
      typecheck_session qcontext M delta G ->
      M p = Some (p_send q l (Val (QVal sent)) P) ->
      ~ In sent (free_qubits P).
  Proof.
    intros qcontext M delta G p q l sent P Htyped Hsend.
    destruct (typecheck_session_component_lookup qcontext M delta G p
      (p_send q l (Val (QVal sent)) P) Htyped Hsend)
      as [T [qc [Hdelta HtypedP]]].
    destruct (typecheck_process_p_send_post T q l (Val (QVal sent)) P
      (nil, nil, qc) HtypedP)
      as [B [T' [Hsub [Hexpr Hcont]]]].
    destruct B as [| |].
    - inversion Hexpr.
    - inversion Hexpr.
    - intros Hin.
      pose proof (typecheck_process_free_qubits P
        (remove_from_qubit_context (nil, nil, qc) sent) T' Hcont sent Hin)
        as Hlocal.
      unfold in_qubit_context, remove_from_qubit_context in Hlocal; simpl in Hlocal.
      destruct (qr_dec sent sent); [discriminate|contradiction].
  Qed.

  Lemma transfer_qubit_owner_lookup_other : forall
      (qm : finite_map qubit_reference (participant * fin)) Hqm
      sv Hsv new sent old n Hlookup q owner n',
      q <> sent -> qm q = Some (owner, n') ->
      quantum_map_of
        (transfer_qubit_from_lookup qm Hqm sv Hsv new sent old n Hlookup) q =
        Some (owner, n').
  Proof.
    intros qm Hqm sv Hsv new sent old n Hlookup q owner n' Hneq Hq.
    unfold transfer_qubit_from_lookup, quantum_map_of.
    cbn [proj1_sig projT1].
    rewrite insert_neq by congruence.
    exact Hq.
  Qed.

  Lemma transfer_qubit_owner_lookup_sent : forall
      (qm : finite_map qubit_reference (participant * fin)) Hqm
      sv Hsv new sent old n Hlookup,
      quantum_map_of
        (transfer_qubit_from_lookup qm Hqm sv Hsv new sent old n Hlookup) sent =
        Some (new, n).
  Proof.
    intros qm Hqm sv Hsv new sent old n Hlookup.
    unfold transfer_qubit_from_lookup, quantum_map_of.
    cbn [proj1_sig projT1].
    rewrite insert_eq; reflexivity.
  Qed.

  Lemma transfer_qubit_owner_lookup_back_other : forall
      (qm : finite_map qubit_reference (participant * fin)) Hqm
      sv Hsv new sent old n Hlookup q owner n',
      q <> sent ->
      quantum_map_of
        (transfer_qubit_from_lookup qm Hqm sv Hsv new sent old n Hlookup) q =
        Some (owner, n') ->
      qm q = Some (owner, n').
  Proof.
    intros qm Hqm sv Hsv new sent old n Hlookup q owner n' Hneq Hq.
    unfold transfer_qubit_from_lookup, quantum_map_of in Hq.
    cbn [proj1_sig projT1] in Hq.
    rewrite insert_neq in Hq by congruence.
    exact Hq.
  Qed.

  Lemma process_qubit_owner_agrees_by_after_step `{good_merge} : forall
      qcontext M delta G qstate a qstate' M' pi,
      typecheck_session qcontext M delta G ->
      state_only_contains_qubits_in_context qcontext qstate ->
      (forall t, process_qubit_owner_agrees_by M qstate t) ->
      step (qstate, M) a (qstate', M') pi ->
      forall t, process_qubit_owner_agrees_by M' qstate' t.
  Proof.
    intros qcontext M delta G qstate a qstate' M' pi Htyped Hstate
      Howners Hstep.
    refine (step_ind
      (fun s1 a s2 r =>
        typecheck_session qcontext (snd s1) delta G ->
        state_only_contains_qubits_in_context qcontext (fst s1) ->
        (forall t, process_qubit_owner_agrees_by (snd s1) (fst s1) t) ->
        forall t, process_qubit_owner_agrees_by (snd s2) (fst s2) t)
      _ _ _ _ _ _ _ _ (qstate, M) a (qstate', M') pi Hstep
      Htyped Hstate Howners).
    - intros p0 q0 l0 e P lQ l1 Q v0 s1 qs Hsend Hrecv Hneq
        Hnth Heval Hnotq Q' s2 Htyped0 Hstate0 Howners0 t.
      unfold process_qubit_owner_agrees_by.
      intros P' Htarget q0' Hin owner n Hqmap.
      destruct (participant_dec t p0) as [->|Htp].
      + change (insert (insert s1 q0 Q') p0 P p0 = Some P') in Htarget.
        rewrite insert_eq in Htarget; inversion Htarget; subst P'.
        assert (Hsendfree : In q0' (free_qubits (p_send q0 l1 e P))).
        { simpl; apply in_or_app; right; exact Hin. }
        eapply (Howners0 p0 (p_send q0 l1 e P) Hsend q0' Hsendfree owner n Hqmap).
      + destruct (participant_dec t q0) as [->|Htq].
        * change (insert (insert s1 q0 Q') p0 P q0 = Some P') in Htarget.
          rewrite insert_neq in Htarget by congruence.
          rewrite insert_eq in Htarget; inversion Htarget; subst P'.
          destruct (free_qubits_process_substitution Q 0 0 (Val v0) q0' Hin)
            as [Hold|Hnew].
          -- assert (Hrecvfree : In q0' (free_qubits (p_recv p0 lQ))).
             { eapply free_qubits_recv_member; [eapply onth_to_list_In; exact Hnth|exact Hold]. }
             eapply (Howners0 q0 (p_recv p0 lQ) Hrecv q0' Hrecvfree owner n Hqmap).
          -- destruct v0 as [natv|boolv|sent].
             ++ simpl in Hnew; contradiction.
             ++ simpl in Hnew; contradiction.
             ++ simpl in Hnew; destruct Hnew as [Heq|[]]; subst q0'.
                exfalso; apply (Hnotq sent); reflexivity.
        * change (insert (insert s1 q0 Q') p0 P t = Some P') in Htarget.
          rewrite insert_neq in Htarget by congruence.
          rewrite insert_neq in Htarget by congruence.
          eapply (Howners0 t P' Htarget q0' Hin owner n Hqmap).
    - intros p0 q0 l0 e P lQ l1 Q v0 s1 qs qs' n Hlookup
        Hsend Hrecv Hneq Hnth Heval Htransfer Q' s2 Htyped0 Hstate0
        Howners0 t.
      assert (He : e = Val (QVal v0)).
      { eapply eval_qubit_value_is_literal; exact Heval. }
      subst e.
      unfold process_qubit_owner_agrees_by.
      intros P' Htarget q0' Hin owner n' Hqmap.
      rewrite Htransfer in Hqmap; simpl in Hqmap.
      destruct (participant_dec t p0) as [->|Htp].
      + change (insert (insert s1 q0 Q') p0 P p0 = Some P') in Htarget.
        rewrite insert_eq in Htarget; inversion Htarget; subst P'.
        pose proof (typed_qubit_send_continuation_no_sent_qubit qcontext
          s1 delta G p0 q0 l1 v0 P Htyped0 Hsend) as Hnot_sent.
        assert (Hqneq : q0' <> v0).
        { intro Heq; subst q0'; apply Hnot_sent; exact Hin. }
        assert (Hsendfree : In q0' (free_qubits
          (p_send q0 l1 (Val (QVal v0)) P))).
        { simpl; right; exact Hin. }
        pose proof (transfer_qubit_owner_lookup_back_other
          (quantum_map_of qs) (proj2_sig (projT1 qs))
          (proj1_sig (projT2 qs)) (proj2_sig (projT2 qs)) q0 v0 p0 n
          Hlookup q0' owner n' Hqneq Hqmap) as Hsource.
        eapply (Howners0 p0 (p_send q0 l1 (Val (QVal v0)) P) Hsend q0'
          Hsendfree owner n' Hsource).
      + destruct (participant_dec t q0) as [->|Htq].
        * change (insert (insert s1 q0 Q') p0 P q0 = Some P') in Htarget.
          rewrite insert_neq in Htarget by congruence.
          rewrite insert_eq in Htarget; inversion Htarget; subst P'.
          destruct (free_qubits_process_substitution Q 0 0
            (Val (QVal v0)) q0' Hin) as [Hold|Hnew].
          -- assert (Hrecvfree : In q0' (free_qubits (p_recv p0 lQ))).
             { eapply free_qubits_recv_member; [eapply onth_to_list_In; exact Hnth|exact Hold]. }
             assert (Hqneq : q0' <> v0).
             {
               intro Heq; subst q0'.
               pose proof (Howners0 q0 (p_recv p0 lQ) Hrecv v0 Hrecvfree p0 n Hlookup)
                 as Howner_eq.
               congruence.
             }
             pose proof (transfer_qubit_owner_lookup_back_other
               (quantum_map_of qs) (proj2_sig (projT1 qs))
               (proj1_sig (projT2 qs)) (proj2_sig (projT2 qs)) q0 v0 p0 n
               Hlookup q0' owner n' Hqneq Hqmap) as Hsrc.
             eapply (Howners0 q0 (p_recv p0 lQ) Hrecv q0' Hrecvfree owner n' Hsrc).
          -- simpl in Hnew; destruct Hnew as [Heq|[]]; subst q0'.
             pose proof (transfer_qubit_owner_lookup_sent
               (quantum_map_of qs) (proj2_sig (projT1 qs))
               (proj1_sig (projT2 qs)) (proj2_sig (projT2 qs)) q0 v0 p0 n
               Hlookup) as Hsent.
             unfold transfer_qubit_from_lookup, quantum_map_of in Hqmap.
             cbn [proj1_sig projT1] in Hqmap.
             destruct (qr_dec v0 v0); [inversion Hqmap; reflexivity|contradiction].
        * change (insert (insert s1 q0 Q') p0 P t = Some P') in Htarget.
          rewrite insert_neq in Htarget by congruence.
          rewrite insert_neq in Htarget by congruence.
          assert (Hqneq : q0' <> v0).
          {
            intro Heq; subst q0'.
            pose proof (Howners0 t P' Htarget v0 Hin p0 n Hlookup) as Howner_eq.
            congruence.
          }
          pose proof (transfer_qubit_owner_lookup_back_other
            (quantum_map_of qs) (proj2_sig (projT1 qs))
            (proj1_sig (projT2 qs)) (proj2_sig (projT2 qs)) q0 v0 p0 n
            Hlookup q0' owner n' Hqneq Hqmap) as Hsrc.
          eapply (Howners0 t P' Htarget q0' Hin owner n' Hsrc).
    - intros p0 P s1 qs qnew Hfresh Hsrc qs2 s2 Htyped0 Hstate0
        Howners0 t.
      assert (Hcovers : state_covers_qubits_in_context qcontext qs).
      {
        unfold state_covers_qubits_in_context,
          state_only_contains_qubits_in_context in *.
        intros q Hctx; apply (proj1 (Hstate0 q)); exact Hctx.
      }
      pose proof (process_qubits_available_from_typed_session_context
        qcontext s1 delta G qs t Htyped0 Hcovers (Howners0 t)) as Howned.
      assert (Htau : step (qs, s1) (Tau p0) (qs2, s2) 1%R).
      { eapply New; eauto. }
      destruct (participant_dec t p0) as [Heq|Hneq].
      + subst t; eapply process_qubit_owner_agrees_by_after_tau_for;
          [exact Htau|left; reflexivity|exact Howned].
      + eapply process_qubit_owner_agrees_by_after_tau_for;
          [exact Htau|right; congruence|exact Howned].
    - intros p0 e P1 P0 s1 qs Hsrc Heval s2 Htyped0 Hstate0 Howners0 t.
      assert (Hcovers : state_covers_qubits_in_context qcontext qs).
      {
        unfold state_covers_qubits_in_context,
          state_only_contains_qubits_in_context in *.
        intros q Hctx; apply (proj1 (Hstate0 q)); exact Hctx.
      }
      pose proof (process_qubits_available_from_typed_session_context
        qcontext s1 delta G qs t Htyped0 Hcovers (Howners0 t)) as Howned.
      assert (Htau : step (qs, s1) (Tau p0) (qs, s2) 1%R).
      { eapply If_0; eauto. }
      destruct (participant_dec t p0) as [Heq|Hneq].
      + subst t; eapply process_qubit_owner_agrees_by_after_tau_for;
          [exact Htau|left; reflexivity|exact Howned].
      + eapply process_qubit_owner_agrees_by_after_tau_for;
          [exact Htau|right; congruence|exact Howned].
    - intros p0 e P1 P0 s1 qs Hsrc Heval s2 Htyped0 Hstate0 Howners0 t.
      assert (Hcovers : state_covers_qubits_in_context qcontext qs).
      {
        unfold state_covers_qubits_in_context,
          state_only_contains_qubits_in_context in *.
        intros q Hctx; apply (proj1 (Hstate0 q)); exact Hctx.
      }
      pose proof (process_qubits_available_from_typed_session_context
        qcontext s1 delta G qs t Htyped0 Hcovers (Howners0 t)) as Howned.
      assert (Htau : step (qs, s1) (Tau p0) (qs, s2) 1%R).
      { eapply If_1; eauto. }
      destruct (participant_dec t p0) as [Heq|Hneq].
      + subst t; eapply process_qubit_owner_agrees_by_after_tau_for;
          [exact Htau|left; reflexivity|exact Howned].
      + eapply process_qubit_owner_agrees_by_after_tau_for;
          [exact Htau|right; congruence|exact Howned].
    - intros p0 q0 P s1 qs qs' n r pi0 Hlookup Hlen Hnonzero Hsrc
        Hmeasure s2 Htyped0 Hstate0 Howners0 t.
      assert (Hcovers : state_covers_qubits_in_context qcontext qs).
      {
        unfold state_covers_qubits_in_context,
          state_only_contains_qubits_in_context in *.
        intros q Hctx; apply (proj1 (Hstate0 q)); exact Hctx.
      }
      pose proof (process_qubits_available_from_typed_session_context
        qcontext s1 delta G qs t Htyped0 Hcovers (Howners0 t)) as Howned.
      assert (Htau : step (qs, s1) (Tau p0) (qs', s2) pi0!).
      { eapply Meas; eauto. }
      destruct (participant_dec t p0) as [Heq|Hneq].
      + subst t; eapply process_qubit_owner_agrees_by_after_tau_for;
          [exact Htau|left; reflexivity|exact Howned].
      + eapply process_qubit_owner_agrees_by_after_tau_for;
          [exact Htau|right; congruence|exact Howned].
    - intros dim p0 U lqs P s1 qs qs' Hlen Hdim Hsrc Happly Hnd
        Hunitary_owned s2 Htyped0 Hstate0 Howners0 t.
      assert (Hcovers : state_covers_qubits_in_context qcontext qs).
      {
        unfold state_covers_qubits_in_context,
          state_only_contains_qubits_in_context in *.
        intros q Hctx; apply (proj1 (Hstate0 q)); exact Hctx.
      }
      pose proof (process_qubits_available_from_typed_session_context
        qcontext s1 delta G qs t Htyped0 Hcovers (Howners0 t)) as Howned.
      assert (Htau : step (qs, s1) (Tau p0) (qs', s2) 1%R).
      { eapply Unitary; eauto. }
      destruct (participant_dec t p0) as [Heq|Hneq].
      + subst t; eapply process_qubit_owner_agrees_by_after_tau_for;
          [exact Htau|left; reflexivity|exact Howned].
      + eapply process_qubit_owner_agrees_by_after_tau_for;
          [exact Htau|right; congruence|exact Howned].
    - intros M0 M0' M1 qs qs' a0 r Hunfold Hinner IH Htyped0
        Hstate0 Howners0 t.
      pose proof (typecheck_session_unfoldM delta G qcontext M0 M0'
        Hunfold Htyped0) as Htypedmid.
      assert (Hownersmid : forall t,
          process_qubit_owner_agrees_by M0' qs t).
      {
        intro t0.
        eapply process_qubit_owner_agrees_unfoldM; [exact Hunfold|exact (Howners0 t0)].
      }
      eapply IH; [exact Htypedmid|exact Hstate0|exact Hownersmid].
  Qed.

  Lemma typed_guarded_state_owners_after_step `{good_merge} : forall
      qstate M a qstate' M' pi qcontext delta G,
      step (qstate, M) a (qstate', M') pi ->
      typecheck_session qcontext M delta G ->
      cguarded_session M ->
      state_only_contains_qubits_in_context qcontext qstate ->
      (forall t, process_qubit_owner_agrees_by M qstate t) ->
      exists qcontext' delta' G',
        typecheck_session qcontext' M' delta' G' /\
        cguarded_session M' /\
        state_only_contains_qubits_in_context qcontext' qstate' /\
        (forall t, process_qubit_owner_agrees_by M' qstate' t).
  Proof.
    intros qstate M a qstate' M' pi qcontext delta G Hstep Htyped
      Hguard Hstate Howners.
    destruct a as [actor|p0 q0 l0 v0].
    - destruct (subject_reduction_via_association_1 M M' pi qstate qstate'
        delta actor qcontext G Hstep Htyped Hstate) as [qcontext' [Htyped' Hstate']].
      exists qcontext', delta, G; split; [exact Htyped'|].
      split.
      + eapply cguarded_session_after_tau; [exact Hstep|exact Hguard].
      + split; [exact Hstate'|].
        exact (process_qubit_owner_agrees_by_after_step qcontext M delta G
          qstate (Tau actor) qstate' M' pi Htyped Hstate Howners Hstep).
    - destruct (subject_reduction_via_association_2 M M' pi qstate qstate'
        delta G p0 q0 l0 v0 qcontext Hstep Htyped)
        as [qcontext' [delta' [G' [e [S [HstateRel [Hincluded
          [Hctx [Hgstep [Heval [Hexpr Htyped']]]]]]]]]]].
      exists qcontext, delta', G'; split; [exact Htyped'|].
      split.
      + eapply cguarded_session_after_transmit; [exact Hstep|exact Hguard].
      + split.
        * exact (state_only_contains_qubits_in_context_after_step
            M M' qstate qstate' (Transmit p0 q0 l0 v0) pi Hstep
            (fun pt P Hlookup => Hguard pt P Hlookup)
            delta delta' G G' qcontext qcontext Htyped Hstate Htyped').
        * exact (process_qubit_owner_agrees_by_after_step qcontext M delta G
            qstate (Transmit p0 q0 l0 v0) qstate' M' pi Htyped Hstate Howners Hstep).
  Qed.

  Lemma typed_guarded_state_owners_after_multistep `{good_merge} : forall
      qstate M la qstate' M' pi,
      multistep (qstate, M) la (qstate', M') pi ->
      forall qcontext delta G,
      typecheck_session qcontext M delta G ->
      cguarded_session M ->
      state_only_contains_qubits_in_context qcontext qstate ->
      (forall t, process_qubit_owner_agrees_by M qstate t) ->
      exists qcontext' delta' G',
        typecheck_session qcontext' M' delta' G' /\
        cguarded_session M' /\
        state_only_contains_qubits_in_context qcontext' qstate' /\
        (forall t, process_qubit_owner_agrees_by M' qstate' t).
  Proof.
    intros qstate M la qstate' M' pi Hmulti.
    dependent induction Hmulti; intros qcontext delta G Htyped Hguard Hstate Howners.
    - pose proof (equivalent_unfoldM M M' H) as Hunfold.
      pose proof (typecheck_session_unfoldM delta G qcontext M M'
        Hunfold Htyped) as Htyped'.
      pose proof (cguarded_session_unfoldM M M' Hunfold Hguard) as Hguard'.
      assert (Howners' : forall t, process_qubit_owner_agrees_by M' qstate' t).
      {
        intro t; eapply process_qubit_owner_agrees_unfoldM;
          [exact Hunfold|exact (Howners t)].
      }
      exists qcontext, delta, G; split; [exact Htyped'|].
      split; [exact Hguard'|]. split; [exact Hstate|exact Howners'].
    - destruct s2 as [qstate2 M2].
      destruct (typed_guarded_state_owners_after_step qstate M a qstate2 M2 r1
        qcontext delta G H Htyped Hguard Hstate Howners)
        as [qcontext1 [delta1 [G1 [Htyped1 [Hguard1 [Hstate1 Howners1]]]]]].
      destruct (IHHmulti qstate2 M2 qstate' M' JMeq_refl JMeq_refl
        qcontext1 delta1 G1 Htyped1 Hguard1 Hstate1 Howners1)
        as [qcontext2 [delta2 [G2 [Htyped2 [Hguard2 [Hstate2 Howners2]]]]]].
      exists qcontext2, delta2, G2; split; [exact Htyped2|].
      split; [exact Hguard2|]. split; [exact Hstate2|exact Howners2].
  Qed.

  Lemma typed_guarded_state_owners_after_multistep_exact `{good_merge} : forall
      qstate M la qstate' M' pi,
      multistep (qstate, M) la (qstate', M') pi ->
      forall qcontext delta G qcontext' delta' G',
      typecheck_session qcontext M delta G ->
      cguarded_session M ->
      state_only_contains_qubits_in_context qcontext qstate ->
      (forall t, process_qubit_owner_agrees_by M qstate t) ->
      typecheck_session qcontext' M' delta' G' ->
      cguarded_session M' /\
      state_only_contains_qubits_in_context qcontext' qstate' /\
      (forall t, process_qubit_owner_agrees_by M' qstate' t).
  Proof.
    intros qstate M la qstate' M' pi Hmulti.
    dependent induction Hmulti; intros qcontext delta G qcontext' delta' G'
      Htyped Hguard Hstate Howners HtypedEnd.
    - pose proof (equivalent_unfoldM M M' H) as Hunfold.
      pose proof (cguarded_session_unfoldM M M' Hunfold Hguard) as Hguard'.
      assert (Howners' : forall t, process_qubit_owner_agrees_by M' qstate' t).
      {
        intro t; eapply process_qubit_owner_agrees_unfoldM;
          [exact Hunfold|exact (Howners t)].
      }
      assert (Hcontexts : forall q,
          qcontext' q = Some tt <-> qcontext q = Some tt).
      {
        intro q.
        pose proof (typecheck_session_qubit_use_exact M' delta' G'
          qcontext' HtypedEnd q) as Hfinal.
        pose proof (typecheck_session_qubit_use_exact M delta G
          qcontext Htyped q) as Hinitial.
        pose proof (free_qubits_session_unfoldM_equiv M M' Hunfold q)
          as Hfree.
        split; intro Hctx.
        - apply (proj1 Hinitial).
          apply (proj2 Hfree).
          apply (proj2 Hfinal); exact Hctx.
        - apply (proj1 Hfinal).
          apply (proj1 Hfree).
          apply (proj2 Hinitial); exact Hctx.
      }
      split; [exact Hguard'|].
      split.
      * unfold state_only_contains_qubits_in_context in *.
        intro q; split; intro Hmap.
        -- apply (proj1 (Hstate q)).
           apply (proj1 (Hcontexts q)); exact Hmap.
        -- apply (proj2 (Hcontexts q)).
           apply (proj2 (Hstate q)); exact Hmap.
      * exact Howners'.
    - destruct s2 as [qstate2 M2].
      destruct (typed_guarded_state_owners_after_step qstate M a qstate2 M2 r1
        qcontext delta G H Htyped Hguard Hstate Howners)
        as [qcontext1 [delta1 [G1 [Htyped1 [Hguard1 [Hstate1 Howners1]]]]]].
      eapply IHHmulti; eauto.
  Qed.

  Lemma typed_guarded_state_after_step `{good_merge} : forall
      qstate M a qstate' M' pi qcontext delta G,
      step (qstate, M) a (qstate', M') pi ->
      typecheck_session qcontext M delta G ->
      cguarded_session M ->
      state_only_contains_qubits_in_context qcontext qstate ->
      exists qcontext' delta' G',
        typecheck_session qcontext' M' delta' G' /\
        cguarded_session M' /\
        state_only_contains_qubits_in_context qcontext' qstate'.
  Proof.
    intros qstate M a qstate' M' pi qcontext delta G Hstep Htyped
      Hguard Hstate.
    destruct a as [actor|p q l v].
    - destruct (subject_reduction_via_association_1 M M' pi qstate qstate'
        delta actor qcontext G Hstep Htyped Hstate) as [qcontext' [Htyped' Hstate']].
      exists qcontext', delta, G; split; [exact Htyped'|].
      split; [eapply cguarded_session_after_tau; eauto|exact Hstate'].
    - destruct (subject_reduction_via_association_2 M M' pi qstate qstate'
        delta G p q l v qcontext Hstep Htyped)
        as [qcontext' [delta' [G' [e [S [HstateRel [Hincluded
          [Hctx [Hgstep [Heval [Hexpr Htyped']]]]]]]]]]].
      exists qcontext, delta', G'; split; [exact Htyped'|].
      split; [eapply cguarded_session_after_transmit; eauto|].
      exact (state_only_contains_qubits_in_context_after_step
        M M' qstate qstate' (Transmit p q l v) pi Hstep
        (fun pt P Hlookup => Hguard pt P Hlookup)
        delta delta' G G' qcontext qcontext Htyped Hstate Htyped').
  Qed.

  Lemma typed_guarded_state_after_multistep `{good_merge} : forall
      qstate M la qstate' M' pi,
      multistep (qstate, M) la (qstate', M') pi ->
      forall qcontext delta G,
      typecheck_session qcontext M delta G ->
      cguarded_session M ->
      state_only_contains_qubits_in_context qcontext qstate ->
      exists qcontext' delta' G',
        typecheck_session qcontext' M' delta' G' /\
        cguarded_session M' /\
        state_only_contains_qubits_in_context qcontext' qstate'.
  Proof.
    intros qstate M la qstate' M' pi Hmulti.
    dependent induction Hmulti; intros qcontext delta G Htyped Hguard Hstate.
    - pose proof (equivalent_unfoldM M M' H) as Hunfold.
      pose proof (typecheck_session_unfoldM delta G qcontext M M'
        Hunfold Htyped) as Htyped'.
      pose proof (cguarded_session_unfoldM M M' Hunfold Hguard) as Hguard'.
      exists qcontext, delta, G; split; [exact Htyped'|].
      split; [exact Hguard'|exact Hstate].
    - destruct s2 as [qstate2 M2].
      destruct (typed_guarded_state_after_step qstate M a qstate2 M2 r1
        qcontext delta G H Htyped Hguard Hstate)
        as [qcontext1 [delta1 [G1 [Htyped1 [Hguard1 Hstate1]]]]].
      destruct (IHHmulti qstate2 M2 qstate' M' JMeq_refl JMeq_refl
        qcontext1 delta1 G1 Htyped1 Hguard1 Hstate1)
        as [qcontext2 [delta2 [G2 [Htyped2 [Hguard2 Hstate2]]]]].
      exists qcontext2, delta2, G2; split; [exact Htyped2|].
      split; [exact Hguard2|exact Hstate2].
  Qed.

  Lemma subtype_send_shape : forall T q fs,
      subtypeC T (ltt_send q fs) ->
      exists fs', T = ltt_send q fs'.
  Proof.
    intros T q fs Hsub.
    pinversion Hsub; try mon_easy.
    - exists xs. reflexivity.
  Qed.

  Lemma subtype_recv_shape : forall T q fs,
      subtypeC T (ltt_recv q fs) ->
      exists fs', T = ltt_recv q fs'.
  Proof.
    intros T q fs Hsub.
    pinversion Hsub; try mon_easy.
    - exists xs. reflexivity.
  Qed.

  Lemma subtype_send_codomain_shape : forall T q fs,
      subtypeC (ltt_send q fs) T ->
      exists fs', T = ltt_send q fs'.
  Proof.
    intros T q fs Hsub.
    pinversion Hsub; try mon_easy.
    - exists ys. reflexivity.
  Qed.

  Lemma subtype_recv_codomain_shape : forall T q fs,
      subtypeC (ltt_recv q fs) T ->
      exists fs', T = ltt_recv q fs'.
  Proof.
    intros T q fs Hsub.
    pinversion Hsub; try mon_easy.
    - exists ys. reflexivity.
  Qed.

  Lemma assoc_global_root_types `{good_merge} : forall
      qcontext M delta a b f G' l,
      typecheck_session qcontext M delta (gtt_send a b f) ->
      gttstepC (gtt_send a b f) G' a b l ->
      exists fs fr,
        delta a = Some (ltt_send b fs) /\
        delta b = Some (ltt_recv a fr).
  Proof.
    intros qcontext M delta a b f G' l Htyped Hstep.
    unfold typecheck_session in Htyped.
    destruct Htyped as [lqc [_ [_ [Hassoc _]]]].
    destruct Hassoc as [Hparts Hprojections].
    assert (Hparta : isgPartsC a (gtt_send a b f)) by constructor.
    assert (Hpartb : isgPartsC b (gtt_send a b f)) by constructor.
    destruct (Hparts a Hparta) as [Ta Hdeltaa].
    destruct (Hparts b Hpartb) as [Tb Hdeltab].
    destruct (Hprojections a Ta Hdeltaa) as [Ta' [Hproja Hsuba]].
    destruct (Hprojections b Tb Hdeltab) as [Tb' [Hprojb Hsubb]].
    destruct (proj_shape_p (gtt_send a b f) G' a b l Ta' Hproja Hstep)
      as [fa Hshapea].
    destruct (proj_shape_q (gtt_send a b f) G' a b l Tb' Hprojb Hstep)
      as [fb Hshapeb].
    rewrite Hshapea in Hsuba.
    rewrite Hshapeb in Hsubb.
    destruct (subtype_send_shape Ta b fa Hsuba) as [fs HTa].
    destruct (subtype_recv_shape Tb a fb Hsubb) as [fr HTb].
    subst Ta Tb.
    eauto.
  Qed.

  Lemma projection_nonend_has_part `{good_merge} : forall G p T,
      projC G p T -> T <> ltt_end -> isgPartsC p G.
  Proof.
    intros G p T Hproj Hnotend.
    pinversion Hproj; try mon_easy.
    - exfalso; apply Hnotend; symmetry; exact H3.
  Qed.

  Lemma typecheck_session_component_from_map `{good_merge} : forall
      qcontext M delta G p P,
      typecheck_session qcontext M delta G ->
      M p = Some P ->
      exists T qc,
        delta p = Some T /\ typecheck_process (nil, nil, qc) P T.
  Proof.
    intros qcontext M delta G p P Htyped Hmap.
    unfold typecheck_session in Htyped.
    destruct Htyped as [lqc [_ [_ [_ [_ [Hlength [Hperm Hprocess]]]]]]].
    destruct (typecheck_session_component_of_map qcontext M delta lqc
      Hperm Hlength Hprocess p P Hmap)
      as [n [T [qc [_ [_ [Hdelta HtypedP]]]]]].
    exists T, qc; split; assumption.
  Qed.

  Lemma typecheck_session_send_part `{good_merge} : forall
      qcontext M delta G p q l e P,
      typecheck_session qcontext M delta G ->
      M p = Some (p_send q l e P) ->
      isgPartsC p G.
  Proof.
    intros qcontext M delta G p q l e P Htyped Hmap.
    destruct (typecheck_session_component_from_map qcontext M delta G p
      (p_send q l e P) Htyped Hmap)
      as [T [qc [Hdelta HtypedP]]].
    destruct (typecheck_process_p_send_post T q l e P (nil, nil, qc)
      HtypedP) as [B [Ttail [Hsub [Hexpr Hcont]]]].
    destruct (subtype_send_codomain_shape T q
      (fun n => if Nat.eqb n l then Some (B, Ttail) else None) Hsub)
      as [fs Hshape].
    subst T.
    unfold typecheck_session in Htyped.
    destruct Htyped as [lqc [_ [_ [Hassoc _]]]].
    destruct Hassoc as [_ Hprojections].
    destruct (Hprojections p (ltt_send q fs) Hdelta)
      as [Tproj [Hproj Hsubproj]].
    destruct (subtype_send_codomain_shape Tproj q fs Hsubproj)
      as [fsproj Hshapeproj].
    rewrite Hshapeproj in Hproj.
    eapply projection_nonend_has_part; [exact Hproj|discriminate].
  Qed.

  Lemma typecheck_session_recv_part `{good_merge} : forall
      qcontext M delta G p q xs,
      typecheck_session qcontext M delta G ->
      M p = Some (p_recv q xs) ->
      isgPartsC p G.
  Proof.
    intros qcontext M delta G p q xs Htyped Hmap.
    destruct (typecheck_session_component_from_map qcontext M delta G p
      (p_recv q xs) Htyped Hmap)
      as [T [qc [Hdelta HtypedP]]].
    destruct (typecheck_process_p_recv_post T (nil, nil, qc) q xs
      HtypedP) as [lBT [Hsub Hbranches]].
    destruct (subtype_recv_codomain_shape T q
      (fun n => onth n lBT) Hsub) as [fs Hshape].
    subst T.
    unfold typecheck_session in Htyped.
    destruct Htyped as [lqc [_ [_ [Hassoc _]]]].
    destruct Hassoc as [_ Hprojections].
    destruct (Hprojections p (ltt_recv q fs) Hdelta)
      as [Tproj [Hproj Hsubproj]].
    destruct (subtype_recv_codomain_shape Tproj q fs Hsubproj)
      as [fsproj Hshapeproj].
    rewrite Hshapeproj in Hproj.
    eapply projection_nonend_has_part; [exact Hproj|discriminate].
  Qed.

  Lemma assoc_root_distinct `{good_merge} : forall
      qcontext M delta a f,
      typecheck_session qcontext M delta (gtt_send a a f) -> False.
  Proof.
    intros qcontext M delta a f Htyped.
    unfold typecheck_session in Htyped.
    destruct Htyped as [lqc [Hreg [_ [Hassoc _]]]].
    destruct Hassoc as [Hparts Hprojections].
    assert (Hpart : isgPartsC a (gtt_send a a f)) by constructor.
    destruct (Hparts a Hpart) as [T Hdelta].
    destruct (Hprojections a T Hdelta) as [Tproj [Hproj _]].
    pinversion Hproj; try mon_easy.
  Qed.

  Lemma gttstep_root_branch : forall p q f G' l,
      gttstepC (gtt_send p q f) G' p q l ->
      exists B, f l = Some (B, G').
  Proof.
    intros p q f G' l Hstep.
    pinversion Hstep; try mon_easy.
    - eauto.
    - exfalso; congruence.
  Qed.

  Lemma simulate_global_root_pair `{good_merge} : forall
      qcontext qstate M delta a b f,
      a <> b ->
      typecheck_session qcontext M delta (gtt_send a b f) ->
      cguarded_session M ->
      state_only_contains_qubits_in_context qcontext qstate ->
      (forall r, process_qubit_owner_agrees_by M qstate r) ->
      exists P Q delta2 G2 l B qstate2 M2 pi la qcontext2,
        M a = Some P /\
        M b = Some Q /\
        ctx_step_f delta a b l B delta2 /\
        gttstepC (gtt_send a b f) G2 a b l /\
        multistep (qstate, M) la (qstate2, M2) pi /\
        typecheck_session qcontext2 M2 delta2 G2 /\
        (forall r, r <> a -> r <> b -> M2 r = M r) /\
        (forall l e P', P = p_send b l e P' -> M2 a = Some P') /\
        (forall cont, Q = p_recv a cont ->
          exists l Qbranch v,
            onth l cont = Some Qbranch /\
            M2 b = Some
              (subst_expression_in_process 0 0 (Val v) Qbranch)).
  Proof.
    intros qcontext qstate M delta a b f Hneq Htyped Hguard Hstate Howners.
    pose proof Htyped as Htyped0.
    unfold typecheck_session in Htyped0.
    destruct Htyped0 as [lqc [Hreg [_ [_ _]]]].
    destruct (regGtt_some_cont a b f Hreg) as [lroot [[Broot Groot] Hbranch]].
    assert (Hrootstep : gttstepC (gtt_send a b f) Groot a b lroot).
    {
      pfold. apply steq with (s := Broot); assumption.
    }
    destruct (assoc_global_root_types qcontext M delta a b f Groot lroot
      Htyped Hrootstep) as [fs [fr [Hsend Hrecv]]].
    destruct (typecheck_session_has_delta_component qcontext M delta
      (gtt_send a b f) a (ltt_send b fs) Htyped Hsend)
      as [P [qcP [HP HtypedP]]].
    destruct (typecheck_session_has_delta_component qcontext M delta
      (gtt_send a b f) b (ltt_recv a fr) Htyped Hrecv)
      as [Q [qcQ [HQ HtypedQ]]].
    set (n := internal_prefix_height P + internal_prefix_height Q).
    assert (Hrank : internal_prefix_height P + internal_prefix_height Q = n)
      by reflexivity.
    destruct (session_fidelity_iteration_local n M delta (gtt_send a b f)
      a b qcontext qstate P Q Hneq Hrank HP HQ
      (ex_intro _ fs (ex_intro _ fr (conj Hsend Hrecv))) Htyped Hguard
      Hstate (Howners a) (Howners b))
      as [delta2 [G2 [l [B [qstate2 [M2 [pi [la [qcontext2
        [Hctx [Hgstep [Hmulti [Htyped2
          [Hframe [Hdone HrecvDone]]]]]]]]]]]]]]].
    exists P, Q, delta2, G2, l, B, qstate2, M2, pi, la, qcontext2.
    split; [exact HP|].
    split; [exact HQ|].
    split; [exact Hctx|].
    split; [exact Hgstep|].
    split; [exact Hmulti|].
    split; [exact Htyped2|].
    split; [exact Hframe|].
    split; [exact Hdone|exact HrecvDone].
  Qed.

  Lemma ctx_step_f_frame : forall delta delta' a b l B r,
      ctx_step_f delta a b l B delta' ->
      r <> a -> r <> b -> delta' r = delta r.
  Proof.
    intros delta delta' a b l B r Hstep Hra Hrb.
    inversion Hstep as [G G' p q l0 xs ys T T' B0 Hneq Hsend Hrecv
      Hbranchsend Hbranchrecv Hupdate]; subst.
    specialize (Hupdate r).
    destruct (participant_dec r a) as [Heq|Hneqp].
    - subst r; contradiction.
    - destruct (participant_dec r b) as [Heq|Hneqq].
      + subst r; contradiction.
      + simpl in Hupdate.
        symmetry; exact Hupdate.
  Qed.

  Lemma multistep_append : forall qstate M la qstate1 M1 pi1
      lb qstate2 M2 pi2,
      multistep (qstate, M) la (qstate1, M1) pi1 ->
      multistep (qstate1, M1) lb (qstate2, M2) pi2 ->
      multistep (qstate, M) (la ++ lb) (qstate2, M2) (pi1 * pi2)%R.
  Proof.
    intros qstate M la qstate1 M1 pi1 lb qstate2 M2 pi2 Hfirst.
    induction Hfirst; intros Hsecond.
    - simpl.
      replace (1%R * pi2)%R with pi2 by (rewrite Rmult_1_l; reflexivity).
      eapply multistep_equivalent_source; eauto.
    - simpl.
      replace (r1 * r2 * pi2)%R with (r1 * (r2 * pi2))%R by ring.
      eapply ms_step with (r1 := r1) (r2 := (r2 * pi2)%R).
      + exact H.
      + simpl.
      specialize (IHHfirst Hsecond).
      exact IHHfirst.
  Qed.

  Lemma live_send_from_balanced `{good_merge} : forall
      (k : nat) qcontext qstate M delta G p q l e P fs,
      balanced_with k p G ->
      typecheck_session qcontext M delta G ->
      cguarded_session M ->
      state_only_contains_qubits_in_context qcontext qstate ->
      (forall r, process_qubit_owner_agrees_by M qstate r) ->
      M p = Some (p_send q l e P) ->
      delta p = Some (ltt_send q fs) ->
      exists la qstate' M' pi,
        multistep (qstate, M) la (qstate', M') pi /\
        M' p = Some P.
  Proof.
    induction k using lt_wf_ind.
    intros qcontext qstate M delta G p q l e P fs Hbw Htyped Hguard
      Hstate Howners HP HdeltaP.
    pose proof (typecheck_session_send_part qcontext M delta G p q l e P
      Htyped HP) as Hpart.
    pose proof Htyped as HtypedComponents.
    unfold typecheck_session in HtypedComponents.
    destruct HtypedComponents as [lqc [Hreg [Hbalanced [_ _]]]].
    destruct G as [|a b f].
    - inversion Hpart.
    - assert (Hneqab : a <> b).
      {
        intro Heq; subst b.
        eapply assoc_root_distinct; exact Htyped.
      }
      destruct (regGtt_some_cont a b f Hreg)
        as [lroot [[Broot Groot] Hbranch]].
      assert (Hrootstep : gttstepC (gtt_send a b f) Groot a b lroot).
      { pfold; apply steq with (s := Broot); assumption. }
      destruct (assoc_global_root_types qcontext M delta a b f Groot lroot
        Htyped Hrootstep) as [fsroot [frroot [Hsendroot Hrecvroot]]].
      destruct (participant_dec p a) as [Hpa|Hpa].
      + subst p.
        rewrite HdeltaP in Hsendroot.
        inversion Hsendroot; subst q fs.
        destruct (simulate_global_root_pair qcontext qstate M delta a b f
          Hneqab Htyped Hguard Hstate Howners)
          as [Pa [Pb [delta2 [G2 [l2 [B2 [qstate2 [M2 [pi2 [la2
            [qcontext2 [Hmapa [Hmapb [Hctx [Hgstep [Hmulti
              [Htyped2 [Hframe [Hdone HrecvDone]]]]]]]]]]]]]]]]]]].
        rewrite HP in Hmapa; inversion Hmapa; subst Pa.
        exists la2, qstate2, M2, pi2.
        split; [exact Hmulti|].
        eapply Hdone; reflexivity.
      + destruct (participant_dec p b) as [Hpb|Hpb].
        * subst p.
          rewrite HdeltaP in Hrecvroot.
          discriminate.
        * destruct k as [|k0].
          -- destruct (balanced_with_nil p (gtt_send a b f) Hbw)
               as [r [Hrootpart|Hrootpart]];
               inversion Hrootpart; subst; contradiction.
          -- destruct (simulate_global_root_pair qcontext qstate M delta a b f
               Hneqab Htyped Hguard Hstate Howners)
               as [Pa [Pb [delta2 [G2 [l2 [B2 [qstate2 [M2 [pi2 [la2
                 [qcontext2 [Hmapa [Hmapb [Hctx [Hgstep [Hmulti
                   [Htyped2 [Hframe [Hdone HrecvDone]]]]]]]]]]]]]]]]]]].
             destruct (gttstep_root_branch a b f G2 l2 Hgstep)
               as [Bbranch Hbranch2].
             assert (Hbw2 : balanced_with k0 p G2).
             {
               eapply balanced_k_cont; eauto.
             }
             destruct (typed_guarded_state_owners_after_multistep_exact
               qstate M la2 qstate2 M2 pi2 Hmulti qcontext delta
               (gtt_send a b f) qcontext2 delta2 G2 Htyped Hguard Hstate
               Howners Htyped2) as [Hguard2 [Hstate2 Howners2]].
             assert (HP2 : M2 p = Some (p_send q l e P)).
             {
               rewrite (Hframe p Hpa Hpb); exact HP.
             }
             assert (HdeltaP2 : delta2 p = Some (ltt_send q fs)).
             {
               rewrite (ctx_step_f_frame delta delta2 a b l2 B2 p
                 Hctx Hpa Hpb); exact HdeltaP.
             }
             destruct (H k0 ltac:(lia) qcontext2 qstate2 M2 delta2 G2
               p q l e P fs Hbw2 Htyped2 Hguard2 Hstate2 Howners2 HP2
               HdeltaP2)
               as [la3 [qstate3 [M3 [pi3 [Hmulti3 Hdone3]]]]].
             exists (la2 ++ la3), qstate3, M3, (pi2 * pi3)%R.
             split.
             ++ eapply multistep_append; eassumption.
             ++ exact Hdone3.
  Qed.

  Lemma live_recv_from_balanced `{good_merge} : forall
      (k : nat) qcontext qstate M delta G p q xs fs,
      balanced_with k p G ->
      typecheck_session qcontext M delta G ->
      cguarded_session M ->
      state_only_contains_qubits_in_context qcontext qstate ->
      (forall r, process_qubit_owner_agrees_by M qstate r) ->
      M p = Some (p_recv q xs) ->
      delta p = Some (ltt_recv q fs) ->
      exists n Pbranch v la qstate' M' pi,
        onth n xs = Some Pbranch /\
        multistep (qstate, M) la (qstate', M') pi /\
        M' p = Some (subst_expression_in_process 0 0 (Val v) Pbranch).
  Proof.
    induction k using lt_wf_ind.
    intros qcontext qstate M delta G p q xs fs Hbw Htyped Hguard
      Hstate Howners HP HdeltaP.
    pose proof (typecheck_session_recv_part qcontext M delta G p q xs
      Htyped HP) as Hpart.
    pose proof Htyped as HtypedComponents.
    unfold typecheck_session in HtypedComponents.
    destruct HtypedComponents as [lqc [Hreg [Hbalanced [_ _]]]].
    destruct G as [|a b f].
    - inversion Hpart.
    - assert (Hneqab : a <> b).
      {
        intro Heq; subst b.
        eapply assoc_root_distinct; exact Htyped.
      }
      destruct (regGtt_some_cont a b f Hreg)
        as [lroot [[Broot Groot] Hbranch]].
      assert (Hrootstep : gttstepC (gtt_send a b f) Groot a b lroot).
      { pfold; apply steq with (s := Broot); assumption. }
      destruct (assoc_global_root_types qcontext M delta a b f Groot lroot
        Htyped Hrootstep) as [fsroot [frroot [Hsendroot Hrecvroot]]].
      destruct (participant_dec p b) as [Hpb|Hpb].
      + subst p.
        rewrite HdeltaP in Hrecvroot.
        inversion Hrecvroot; subst q fs.
        destruct (simulate_global_root_pair qcontext qstate M delta a b f
          Hneqab Htyped Hguard Hstate Howners)
          as [Pa [Pb [delta2 [G2 [l2 [B2 [qstate2 [M2 [pi2 [la2
            [qcontext2 [Hmapa [Hmapb [Hctx [Hgstep [Hmulti
              [Htyped2 [Hframe [Hdone HrecvDone]]]]]]]]]]]]]]]]]]].
        rewrite HP in Hmapb; inversion Hmapb; subst Pb.
        destruct (HrecvDone xs eq_refl)
          as [n [Pbranch [v [HbranchRecv HlookupRecv]]]].
        exists n, Pbranch, v, la2, qstate2, M2, pi2.
        split; [exact HbranchRecv|].
        split; assumption.
      + destruct (participant_dec p a) as [Hpa|Hpa].
        * subst p.
          rewrite HdeltaP in Hsendroot.
          discriminate.
        * destruct k as [|k0].
          -- destruct (balanced_with_nil p (gtt_send a b f) Hbw)
               as [r [Hrootpart|Hrootpart]];
               inversion Hrootpart; subst; contradiction.
          -- destruct (simulate_global_root_pair qcontext qstate M delta a b f
               Hneqab Htyped Hguard Hstate Howners)
               as [Pa [Pb [delta2 [G2 [l2 [B2 [qstate2 [M2 [pi2 [la2
                 [qcontext2 [Hmapa [Hmapb [Hctx [Hgstep [Hmulti
                   [Htyped2 [Hframe [Hdone HrecvDone]]]]]]]]]]]]]]]]]]].
             destruct (gttstep_root_branch a b f G2 l2 Hgstep)
               as [Bbranch Hbranch2].
             assert (Hbw2 : balanced_with k0 p G2).
             {
               eapply balanced_k_cont; eauto.
             }
             destruct (typed_guarded_state_owners_after_multistep_exact
               qstate M la2 qstate2 M2 pi2 Hmulti qcontext delta
               (gtt_send a b f) qcontext2 delta2 G2 Htyped Hguard Hstate
               Howners Htyped2) as [Hguard2 [Hstate2 Howners2]].
             assert (HP2 : M2 p = Some (p_recv q xs)).
             {
               rewrite (Hframe p Hpa Hpb); exact HP.
             }
             assert (HdeltaP2 : delta2 p = Some (ltt_recv q fs)).
             {
               rewrite (ctx_step_f_frame delta delta2 a b l2 B2 p
                 Hctx Hpa Hpb); exact HdeltaP.
             }
             destruct (H k0 ltac:(lia) qcontext2 qstate2 M2 delta2 G2
               p q xs fs Hbw2 Htyped2 Hguard2 Hstate2 Howners2 HP2
               HdeltaP2)
               as [n [Pbranch [v [la3 [qstate3 [M3 [pi3
                 [Hbranch3 [Hmulti3 Hdone3]]]]]]]]].
             exists n, Pbranch, v, (la2 ++ la3), qstate3, M3,
               (pi2 * pi3)%R.
             split; [exact Hbranch3|].
             split.
             ++ eapply multistep_append; eassumption.
             ++ exact Hdone3.
  Qed.
  
  Lemma typed_guarded_session_after_multi_unfoldM `{good_merge} : forall
      qcontext M M' delta G,
      multi unfoldM M M' ->
      typecheck_session qcontext M delta G ->
      cguarded_session M ->
      typecheck_session qcontext M' delta G /\ cguarded_session M'.
  Proof.
    intros qcontext M M' delta G Hmulti.
    induction Hmulti as [M0|M0 M1 M2 Hunfold Hmulti IH];
      intros Htyped Hguard.
    - split; assumption.
    - pose proof (typecheck_session_unfoldM delta G qcontext M0 M1
        Hunfold Htyped) as Htyped1.
      pose proof (cguarded_session_unfoldM M0 M1 Hunfold Hguard)
        as Hguard1.
      exact (IH Htyped1 Hguard1).
  Qed.

  Theorem live_ctx_to_sess `{good_merge} : forall la qcontext qstate qstate' delta M M' G pi, 
    typecheck_session qcontext M delta G ->   
    (forall p P, M p = Some P -> cguardedP P) ->
    state_only_contains_qubits_in_context qcontext qstate ->
    multistep (qstate, M) la (qstate',M') pi -> live_sess_0 M'.
Proof.
  intros la qcontext qstate qstate' delta M M' G pi Htyped Hguard
    Hstate Hsteps.
  assert (HguardM : cguarded_session M).
  { intros p0 P0 Hlookup; exact (Hguard p0 P0 Hlookup). }
  destruct (typed_guarded_state_after_multistep qstate M la qstate' M' pi
    Hsteps qcontext delta G Htyped HguardM Hstate)
    as [qcontext' [delta' [G' [Htyped' [Hguard' Hstate']]]]].
  intros M'' p P Hunfold Hlookup.
  destruct (typed_guarded_session_after_multi_unfoldM
    qcontext' M' M'' delta' G' Hunfold Htyped' Hguard')
    as [Htyped'' Hguard''].
  destruct (typed_session_initial_owned_state qcontext' M'' delta' G'
    Htyped'') as [qstate0 [Hstate0 Howned0]].
  assert (Howners0 : forall r, process_qubit_owner_agrees_by M'' qstate0 r).
  {
    intro r.
    apply process_qubit_owner_agreement_of_owned.
    unfold process_qubits_owned_by.
    intros P0 Hlookup0 q Hin.
    eapply Howned0; eassumption.
  }
  unfold live_path_s.
  split.
  - intros P0 pt lb ex Ptail Hlookup0 Hshape.
    destruct P0 as [lz|R|q0 l0 e0 R0|q0 xs0|R|n U lz R|e0 R|e0 R1 R2|n lz];
      try discriminate.
    inversion Hshape; subst.
    destruct (typecheck_session_component_from_map qcontext' M'' delta' G'
      p (p_send pt lb ex Ptail) Htyped'' Hlookup0)
      as [T [qc [Hdelta HtypedP]]].
    destruct (typecheck_process_p_send_post T pt lb ex Ptail
      (nil, nil, qc) HtypedP)
      as [B [Ttail [Hsub [Hexpression Hcontinuation]]]].
    destruct (subtype_send_codomain_shape T pt
      (fun n => if Nat.eqb n lb then Some (B, Ttail) else None) Hsub)
      as [fs Htype].
    subst T.
    pose proof (typecheck_session_send_part qcontext' M'' delta' G'
      p pt lb ex Ptail Htyped'' Hlookup0) as Hpart.
    pose proof Htyped'' as HtypedBalance.
    unfold typecheck_session in HtypedBalance.
    destruct HtypedBalance as [lqc [Hreg [Hbalanced Hrest]]].
    destruct (part_with_balanced_k p G' Hpart Hbalanced) as [k Hbw].
    destruct (live_send_from_balanced k qcontext' qstate0 M'' delta' G' p
      pt lb ex Ptail fs Hbw Htyped'' Hguard'' Hstate0 Howners0 Hlookup0
      Hdelta) as [la0 [qstate1 [M1 [pi0 [Hlive Hdone]]]]].
    exists la0, qstate0, qstate1, pi0, M1.
    split; assumption.
  - intros P0 pt xs Hlookup0 Hshape.
    destruct P0 as [lz|R|q0 l0 e0 R0|q0 xs0|R|n U lz R|e0 R|e0 R1 R2|n lz];
      try discriminate.
    inversion Hshape; subst.
    destruct (typecheck_session_component_from_map qcontext' M'' delta' G'
      p (p_recv pt xs) Htyped'' Hlookup0)
      as [T [qc [Hdelta HtypedP]]].
    destruct (typecheck_process_p_recv_post T (nil, nil, qc) pt xs
      HtypedP) as [lBT [Hsub Hbranches]].
    destruct (subtype_recv_codomain_shape T pt
      (fun n => onth n lBT) Hsub) as [fs Htype].
    subst T.
    pose proof (typecheck_session_recv_part qcontext' M'' delta' G'
      p pt xs Htyped'' Hlookup0) as Hpart.
    pose proof Htyped'' as HtypedBalance.
    unfold typecheck_session in HtypedBalance.
    destruct HtypedBalance as [lqc [Hreg [Hbalanced Hrest]]].
    destruct (part_with_balanced_k p G' Hpart Hbalanced) as [k Hbw].
    destruct (live_recv_from_balanced k qcontext' qstate0 M'' delta' G' p
      pt xs fs Hbw Htyped'' Hguard'' Hstate0 Howners0 Hlookup0 Hdelta)
      as [n [Pbranch [v [la0 [qstate1 [M1 [pi0
        [Hbranch [Hlive Hdone]]]]]]]]].
    exists n, Pbranch.
    split; [exact Hbranch|].
    exists la0, qstate0, qstate1, pi0, M1, v.
    split; assumption.
Qed.
