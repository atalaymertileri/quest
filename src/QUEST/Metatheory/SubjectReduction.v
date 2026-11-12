From SQIR Require Import SQIR UnitaryOps.
From QuantumLib Require Import Matrix CauchySchwarz.
Require Import Lia Permutation Reals List.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import SST session substitution balanced QuantumPropertiesCore.
Require Import QUEST.
Require Import Progress.
From Paco Require Import paco.


Lemma partition_delete:
forall qcontext l1 l2 p_qc q,
FMap.partition qubit_reference unit qcontext (l1 ++ p_qc :: l2) ->
(qcontext q = None \/ p_qc q <> None) ->
FMap.partition qubit_reference unit (@delete _ qr_dec _ qcontext q) (l1 ++ @delete _ qr_dec _ p_qc q :: l2).
Proof.
intros qcontext l1 l2 p_qc q Hpart Howner.
  unfold FMap.partition in Hpart |- *.
  destruct Hpart as [Hcovers Hdisjoint].

  assert (Htarget :
    nth_error (l1 ++ p_qc :: l2) (length l1) = Some p_qc).
  {
    rewrite nth_error_app2 by lia.
    rewrite Nat.sub_diag.
    reflexivity.
  }

  assert (Hnth : forall i m,
    nth_error
      (l1 ++ delete (KEQ := qr_dec) p_qc q :: l2) i = Some m ->
    (i = length l1 /\
      m = delete (KEQ := qr_dec) p_qc q) \/
    (i <> length l1 /\
      nth_error (l1 ++ p_qc :: l2) i = Some m)).
  {
    intros i m Hi.
    destruct (Nat.eq_dec i (length l1)) as [Heq | Hneq].
    - subst i.
      left; split; [reflexivity |].
      rewrite nth_error_app2 in Hi by lia.
      rewrite Nat.sub_diag in Hi.
      simpl in Hi.
      inversion Hi; reflexivity.
    - right; split; [exact Hneq |].
      destruct (lt_dec i (length l1)) as [Hlt | Hnlt].
      + rewrite nth_error_app1 in Hi by exact Hlt.
        rewrite nth_error_app1 by exact Hlt.
        exact Hi.
      + assert (Hgt : length l1 < i) by lia.
        rewrite nth_error_app2 in Hi by lia.
        rewrite nth_error_app2 by lia.
        destruct (i - length l1) eqn:Hminus; [lia |].
        simpl in *.
        exact Hi.
  }

  split.
  - unfold covers in Hcovers |- *.
    intros k v.
    destruct (qr_dec q k) as [Heq | Hneq].
    + subst k.
      split.
      * intro Hsome.
        rewrite delete_eq in Hsome.
        discriminate.
      * intros [m [Hin Hsome]].
        apply In_nth_error in Hin.
        destruct Hin as [i Hi].
        destruct (Hnth i m Hi) as
          [[Hit Hm] | [Hnot_target Hmold]].
        -- subst i m.
           rewrite delete_eq in Hsome.
           discriminate.
        -- destruct Howner as [Hnone | Hp].
           ++ assert (Hglobal : qcontext q = Some v).
              {
                apply (proj2 (Hcovers q v)).
                exists m; split.
                - apply nth_error_In with (n := i); exact Hmold.
                - exact Hsome.
              }
              congruence.
           ++ assert (Hneq_index : length l1 <> i) by lia.
              pose proof
                (Hdisjoint (length l1) i p_qc m Hneq_index
                  Htarget Hmold q) as Hd.
              destruct Hd as [Hd _].
              specialize (Hd Hp).
              rewrite Hd in Hsome.
              discriminate.
    + rewrite delete_neq by exact Hneq.
      split.
      * intro Hsome.
        apply (proj1 (Hcovers k v)) in Hsome.
        destruct Hsome as [m [Hin Hm]].
        apply in_app_iff in Hin.
        destruct Hin as [Hin | Hin].
        -- exists m; split.
           ++ apply in_app_iff; left; exact Hin.
           ++ exact Hm.
        -- simpl in Hin.
           destruct Hin as [Hin | Hin].
           ++ subst m.
              exists (delete (KEQ := qr_dec) p_qc q); split.
              ** apply in_app_iff; right; simpl; auto.
              ** rewrite delete_neq by exact Hneq; exact Hm.
           ++ exists m; split.
              ** apply in_app_iff; right; simpl; auto.
              ** exact Hm.
      * intros [m [Hin Hm]].
        apply in_app_iff in Hin.
        apply (proj2 (Hcovers k v)).
        destruct Hin as [Hin | Hin].
        -- exists m; split.
           ++ apply in_app_iff; left; exact Hin.
           ++ exact Hm.
        -- simpl in Hin.
           destruct Hin as [Hin | Hin].
           ++ subst m.
              apply delete_Some in Hm.
              destruct Hm as [_ Hm].
              exists p_qc; split.
              ** apply in_app_iff; right; simpl; auto.
              ** exact Hm.
           ++ exists m; split.
              ** apply in_app_iff; right; simpl; auto.
              ** exact Hm.

  - unfold pairwise_disjoint in Hdisjoint |- *.
    intros i j m m' Hij Hi Hj k.
    destruct (Hnth i m Hi) as [[Hit Hm] | [Hit Hiold]];
    destruct (Hnth j m' Hj) as [[Hjt Hm'] | [Hjt Hjold]].
    + subst i j m m'.
      contradiction.
    + subst i m.
      assert (Hneq_index : length l1 <> j) by lia.
      pose proof
        (Hdisjoint (length l1) j p_qc m' Hneq_index
          Htarget Hjold k) as Hd.
      destruct Hd as [Hd1 Hd2].
      split.
      * intro Hdeleted.
        apply Hd1.
        intro Hpnone.
        destruct (qr_dec q k) as [Heq | Hneq].
        -- subst k; rewrite delete_eq in Hdeleted; contradiction.
        -- rewrite delete_neq in Hdeleted by exact Hneq; contradiction.
      * intro Hm'none.
        specialize (Hd2 Hm'none).
        destruct (qr_dec q k) as [Heq | Hneq].
        -- subst k; apply delete_eq.
        -- rewrite delete_neq by exact Hneq; exact Hd2.
    + subst j m'.
      pose proof
        (Hdisjoint i (length l1) m p_qc Hit
          Hiold Htarget k) as Hd.
      destruct Hd as [Hd1 Hd2].
      split.
      * intro Hmnone.
        specialize (Hd1 Hmnone).
        destruct (qr_dec q k) as [Heq | Hneq].
        -- subst k; apply delete_eq.
        -- rewrite delete_neq by exact Hneq; exact Hd1.
      * intro Hdeleted.
        apply Hd2.
        intro Hpnone.
        destruct (qr_dec q k) as [Heq | Hneq].
        -- subst k; rewrite delete_eq in Hdeleted; contradiction.
        -- rewrite delete_neq in Hdeleted by exact Hneq; contradiction.
    + exact (Hdisjoint i j m m' Hij Hiold Hjold k).
Qed.




Lemma partition_insert_new :
forall qc z l1 x l2, 
FMap.partition _ _ qc (l1++x::l2) ->
qc z = None \/ x z <> None ->
FMap.partition qubit_reference unit
(insert (KEQ:=qr_dec) qc
z tt)
(l1 ++
insert (KEQ:=qr_dec)  x z tt
:: l2).
Proof.
    unfold FMap.partition, covers, pairwise_disjoint; simpl; intros; cleanup.
    split; intros.
    clear H0.
    destruct v.

    case_analysis; intuition eauto; cleanup; eauto.
    eexists (insert  x k tt).
    split. 
    apply in_app_iff; simpl; eauto.
    simpl; case_analysis; eauto; congruence.

    apply H in H0; cleanup.
    apply in_app_iff in H0.
    simpl in *; repeat split_ors; cleanup.
    exists m'; split; eauto.
    eexists (insert m' z tt);
    split; eauto. 
    apply in_app_iff; simpl; eauto.
    simpl; case_analysis; eauto; try congruence.

    exists m'; split; eauto.
    apply in_app_iff; simpl; eauto.
    apply H.
    apply in_app_iff in H0.
    simpl in *; repeat split_ors; cleanup.
    exists m'; simpl; eauto.
    simpl in *; case_analysis.
    exists x; split; eauto.
    apply in_app_iff; simpl; eauto.
    exists m'; split; eauto.
    apply in_app_iff; simpl; eauto.

    destruct (Nat.eq_dec i (length l1)); subst.
    rewrite nth_error_app2, Nat.sub_diag in H3; eauto.
    simpl in *; cleanup.
    simpl; case_analysis; subst.
    
    
    assert_fresh (m' k = None). {
        destruct_fresh (m' k); eauto.
        split_ors.
        edestruct H.
        rewrite H5 in H0; cleanup.
        eexists; split; eauto.
        eapply (nth_error_In _ j).
        destruct (lt_dec j (length l1)).
        rewrite nth_error_app1 in *; eauto.
        rewrite nth_error_app2 in *; 
        simpl in *.
        destruct_fresh (j - length l1).
        lia.
        simpl in *; eauto.
        lia.
        lia.
        edestruct H1; eauto.
        rewrite nth_error_app2, Nat.sub_diag; simpl; eauto.
        destruct (lt_dec j (length l1)).
        rewrite nth_error_app1 in *; eauto.
        rewrite nth_error_app2 in *; 
        simpl in *.
        destruct_fresh (j - length l1).
        lia.
        simpl in *; eauto.
        lia.
        lia.
        rewrite H3 in HD; cleanup; eauto.
    }
    intuition eauto.
    eapply H1; eauto.
    rewrite nth_error_app2, Nat.sub_diag; simpl; eauto.
    destruct (lt_dec j (length l1)).
    rewrite nth_error_app1 in *; eauto.
    rewrite nth_error_app2 in *; 
    simpl in *.
    destruct_fresh (j - length l1).
    lia.
    simpl in *; eauto.
    lia.
    lia.
    destruct (Nat.eq_dec j (length l1)); subst.

    rewrite nth_error_app2, Nat.sub_diag in H4; eauto.
    simpl in *; cleanup.
    simpl; case_analysis; subst.
    
    assert_fresh (m k = None). {
        destruct_fresh (m k); eauto.
        split_ors.
        edestruct H.
        rewrite H5 in H0; cleanup.
        eexists; split; eauto.
        eapply (nth_error_In _ i).
        destruct (lt_dec i (length l1)).
        rewrite nth_error_app1 in *; eauto.
        rewrite nth_error_app2 in *; 
        simpl in *.
        destruct_fresh (i - length l1).
        lia.
        simpl in *; eauto.
        lia.
        lia.
        edestruct H1; eauto.
        destruct (lt_dec i (length l1)).
        rewrite nth_error_app1 in *; eauto.
        rewrite nth_error_app2 in *; 
        simpl in *.
        destruct_fresh (i - length l1).
        lia.
        simpl in *; eauto.
        lia.
        lia.
        rewrite nth_error_app2, Nat.sub_diag; simpl; eauto.
        rewrite H5 in HD; cleanup; eauto.
    }
    intuition eauto.
    eapply H1; eauto.
    destruct (lt_dec i (length l1)).
    rewrite nth_error_app1 in *; eauto.
    rewrite nth_error_app2 in *; 
    simpl in *.
    destruct_fresh (i - length l1).
    lia.
    simpl in *; eauto.
    lia.
    lia.
    rewrite nth_error_app2, Nat.sub_diag; simpl; eauto.

    eapply H1.
    apply H2.
    destruct (lt_dec i (length l1)).
    rewrite nth_error_app1; eauto.
    rewrite nth_error_app1 in H3; eauto.
    rewrite nth_error_app2 in H3. 
    rewrite nth_error_app2.
    simpl in *.
    destruct_fresh (i - length l1).
    lia.
    simpl in *; eauto.
    lia.
    lia.

    destruct (lt_dec j (length l1)).
    rewrite nth_error_app1; eauto.
    rewrite nth_error_app1 in H4; eauto.
    rewrite nth_error_app2 in H4. 
    rewrite nth_error_app2.
    simpl in *.
    destruct_fresh (j - length l1).
    lia.
    simpl in *; eauto.
    lia.
    lia.
Qed.

Lemma fold_right_orb_to_or_true:
forall A l P,
fold_right (fun x : A => or (P x = true)) False l <-> fold_right (fun x : A => orb (P x)) false l = true.
Proof.
    induction l; simpl; intuition eauto; try congruence;
    cleanup; simpl; eauto.
    apply IHl in H0.
    rewrite H0; simpl; eauto. destruct (P a); simpl; eauto.
    apply Bool.orb_prop in H; intuition; cleanup; simpl; eauto.
    right; apply IHl; eauto.
Qed.

Lemma fold_right_orb_to_or_false:
forall A l P,
fold_right (fun x : A => and (P x = false)) True l <-> fold_right (fun x : A => orb (P x)) false l = false.
Proof.
    induction l; simpl; intuition eauto; try congruence;
    cleanup; simpl; eauto.
    apply IHl in H1.
    eauto.
    apply Bool.orb_false_iff in H; cleanup; eauto.
    apply Bool.orb_false_iff in H; cleanup; eauto.
    apply IHl; eauto.
Qed.



Lemma partition_None:
forall K (KEQ: EqDec K) V (m: finite_map K V) lm (k: K),
FMap.partition _ _ m lm ->
m k = None ->
forall m', In m' lm ->
m' k = None.
Proof.
unfold FMap.partition, covers; simpl; intros;
cleanup.
destruct_fresh (m' k); eauto.
assert_fresh (m k = Some v). {
    apply H; eauto.
}
congruence.
Qed.

Lemma partition_transfer_qubit:
forall lqc qcontext e np nq p_qc q_qc,
FMap.partition qubit_reference unit qcontext lqc ->
nth_error lqc np = Some p_qc ->
nth_error lqc nq = Some q_qc ->
p_qc e = Some tt ->
FMap.partition qubit_reference unit qcontext (updn (updn lqc np (delete (KEQ:= qr_dec) p_qc e)) nq (insert (KEQ:= qr_dec) q_qc e tt)).
Proof.
    unfold FMap.partition in *; intros; cleanup.
    split.
    {(*covers*)
        unfold covers in *; intros.
        destruct v.
        split; intros.
        {
            eapply H in H4; cleanup.
            eapply In_iff_nth_error in H4; cleanup.
            destruct (qr_dec k e); cleanup.
            {
                eexists; split. 
                eapply In_updn_eq.
                shelve.
                eapply insert_eq.
            }
            {
                destruct (Nat.eq_dec n nq); cleanup.
                {(* m = nq *)
                    eexists; split. 
                    eapply In_updn_eq.
                    shelve.
                    erewrite insert_neq; eauto.
                }
                destruct (Nat.eq_dec n np); cleanup.
                { (* m = np *)
                    eexists; split. 
                    eapply In_updn_neq; eauto. 
                    eapply nth_error_updn_eq.
                    shelve.
                    erewrite delete_neq; eauto.
                }
                {(*m <> np /\ m<>nq*)
                    eexists; split. 
                    eapply In_updn_neq; eauto. 
                    erewrite nth_error_updn_neq; eauto.
                    eauto.
                }
            }
        }
        {
            cleanup.
            eapply H; eauto.
            eapply in_updn in H4; split_ors; cleanup; eauto.
            eapply in_updn in H4; split_ors; cleanup; eauto.
            
            eapply delete_Some in H5; cleanup; eauto.
            eexists; split; eauto.
            eapply nth_error_In; eauto.

            eapply insert_Some in H5;
            split_ors; cleanup; eauto;
            eexists; split; eauto;
            eapply nth_error_In; eauto.
        }
    }
    {(*pairwise disjoint*)
        unfold pairwise_disjoint in *; cleanup.
        intros.
        destruct (Nat.eq_dec nq i); cleanup.
        {(*i = nq*)
            erewrite nth_error_updn_neq in H6; eauto.
            erewrite nth_error_updn_eq in H5; eauto; cleanup.
            destruct (Nat.eq_dec np j); cleanup.
            {(*j = np*)
                erewrite nth_error_updn_eq in H6; eauto; cleanup.
                split; intros.
                destruct_fresh (insert (KEQ:= qr_dec) q_qc e tt k); try congruence.
                eapply insert_Some in HD; split_ors; cleanup.
                eapply delete_eq.
                erewrite delete_neq; eauto.
                eapply H3 in H1; eauto; cleanup; eauto.
                apply H8; rewrite H7; congruence.

                destruct_fresh (delete (KEQ:=qr_dec) p_qc e k); try congruence.
                eapply delete_Some in HD; cleanup.
                erewrite insert_neq; eauto.
                eapply H3 in H1; eauto; cleanup; eauto.
                apply H1; rewrite H7; congruence.
                shelve.
            }
            {(*j <> np*)
                erewrite nth_error_updn_neq in H6; eauto.
                split; intros.
                destruct_fresh (insert (KEQ:= qr_dec) q_qc e tt k); try congruence.
                eapply insert_Some in HD; split_ors; cleanup.
                eapply H3 in H6; eauto; cleanup; eauto.
                apply H6; rewrite H2; congruence.
                
                eapply H3 in H6; cleanup.
                apply H6; rewrite H8; congruence.
                2: eauto. 
                eauto.

                destruct_fresh (insert (KEQ:= qr_dec) q_qc e tt k); try congruence.
                eapply insert_Some in HD; split_ors; cleanup.
                eapply H3 in H6; eauto; cleanup; eauto.
                apply H7 in H5; congruence.
                eapply H3 in H6; cleanup.
                apply H9 in H5; rewrite H8 in H5; congruence.
                2: eauto.
                eauto.
            }
            shelve.
        }
        {(*i <> nq*)
            erewrite nth_error_updn_neq in H5; eauto.
            destruct (Nat.eq_dec np i); cleanup.
            { (*i = np*)
                erewrite nth_error_updn_eq in H5; eauto; cleanup.
                destruct (Nat.eq_dec nq j); cleanup.
                {(*j = nq*)
                    erewrite nth_error_updn_eq in H6; eauto; cleanup.
                    split; intros.
                    destruct_fresh (delete (KEQ:= qr_dec) p_qc e k); try congruence.
                    eapply delete_Some in HD; cleanup.
                    rewrite insert_neq; eauto.
                    eapply H3 in H1; eauto; cleanup; eauto.
                    apply H1; rewrite H7; congruence.

                    destruct_fresh (insert (KEQ:=qr_dec) q_qc e tt k); try congruence.
                    eapply insert_Some in HD; split_ors; cleanup.
                    eapply delete_eq.
                    erewrite delete_neq; eauto.
                    eapply H3 in H1; eauto; cleanup; eauto.
                    apply H8; rewrite H7; congruence.
                    shelve.
                }
                {(*j <> nq*)
                    do 2 erewrite nth_error_updn_neq in H6; eauto.
                    split; intros.
                    destruct_fresh (delete (KEQ:= qr_dec) p_qc e k); try congruence.
                    eapply delete_Some in HD; cleanup.
                    eapply H3 in H6; cleanup.
                    apply H6; rewrite H8; congruence.
                    2: eauto. 
                    eauto.

                    destruct_fresh (delete (KEQ:= qr_dec) p_qc e k); try congruence.
                    eapply delete_Some in HD; cleanup.
                    eapply H3 in H6; cleanup.
                    apply H9 in H5; rewrite H8 in H5; congruence.
                    2: eauto.
                    eauto.
                }
                shelve.
            }
            {(*i <> np /\ i <> nq *)
                erewrite nth_error_updn_neq in H5; eauto.
                destruct (Nat.eq_dec nq j); cleanup.
                {(*j = np*)
                    erewrite nth_error_updn_eq in H6; eauto; cleanup.
                    split; intros.
                    destruct_fresh (insert (KEQ:= qr_dec) q_qc e tt k); try congruence.
                    eapply insert_Some in HD; split_ors; cleanup.
                    eapply H3 in H5; eauto; cleanup; eauto.
                    apply H7 in H6; rewrite H2 in H6; congruence.
                    eapply H3 in H5; cleanup.
                    apply H9 in H6; rewrite H8 in H6; congruence.
                    2: eauto.
                    eauto.

                    destruct_fresh (insert (KEQ:= qr_dec) q_qc e tt k); try congruence.
                    eapply insert_Some in HD; split_ors; cleanup.
                    eapply H3 in H5; eauto; cleanup; eauto.
                    apply H5; rewrite H2; congruence.
                    eapply H3 in H5; cleanup.
                    apply H5; rewrite H8; congruence.
                    2: eauto.
                    eauto.
                    shelve.
                }
                erewrite nth_error_updn_neq in H6; eauto.
                destruct (Nat.eq_dec np j); cleanup.
                {(*j = np*)
                    erewrite nth_error_updn_eq in H6; eauto; cleanup.
                    split; intros.
                    destruct_fresh (delete (KEQ:= qr_dec) p_qc e k); try congruence.
                    eapply delete_Some in HD; cleanup.
                    eapply H3 in H5; eauto; cleanup; eauto.
                    apply H9 in H6; rewrite H8 in H6; congruence.

                    destruct_fresh (delete (KEQ:= qr_dec) p_qc e k); try congruence.
                    eapply delete_Some in HD; cleanup.

                    eapply H3 in H5; eauto; cleanup; eauto.
                    apply H5; rewrite H8; congruence.
                    shelve.
                }
                {(*j <> np /\ j <> nq*)
                    erewrite nth_error_updn_neq in H6; eauto.
                }
            }
        }
    }
    Unshelve.
    all: try solve [try rewrite updn_length; eapply nth_error_length; eauto].
Qed.

Lemma session_participants_insert_In:
forall (M: session) p P P', 
In (p, P) (elems _ _ M) ->
Permutation (session_participants (insert M p P')) (session_participants M).
Proof.
    unfold session_participants; destruct M; simpl in *.
    clear.
    induction elems; simpl; intros; cleanup.
    split_ors; cleanup; simpl in *;
    case_analysis; cleanup; simpl; eauto.
Qed.

Lemma typecheck_expression_empty_vars_closed:
forall context e B,
typecheck_expression context e B ->
context.1.2 = nil ->
closed_expression_at 0 e.
Proof.
  intros context e B Htyped.
  induction Htyped; intros Hvars; simpl; try constructor; eauto.
  - unfold in_variable_context in H; simpl in H.
    rewrite Hvars in H; simpl in H.
    destruct x; discriminate H.
Qed.

Lemma associated_send_recv_branch `{good_merge}:
forall delta G p q l B Tsend frecv Tp Tq,
balancedG G ->
assoc_gctx delta G ->
delta p = Some Tp ->
delta q = Some Tq ->
subtypeC
  (ltt_send q (fun n => if Nat.eqb n l then Some (B, Tsend) else None)) Tp ->
subtypeC (ltt_recv p frecv) Tq ->
exists fs fr Tsend' Trecv',
Tp = ltt_send q fs /\
Tq = ltt_recv p fr /\
fs l = Some (B, Tsend') /\
fr l = Some (B, Trecv') /\
subtypeC Tsend Tsend'.
Proof.
  intros delta G p q l B Tsend frecv Tp Tq Hbal Hassoc HdeltaP HdeltaQ
    Hsend Hrecv.
  destruct Hassoc as [_ Hassoc].
  destruct (Hassoc p Tp HdeltaP) as [TprojP [HprojP HsubP]].
  destruct (Hassoc q Tq HdeltaQ) as [TprojQ [HprojQ HsubQ]].
  destruct (subtypeC_send_inv q
    (fun n => if Nat.eqb n l then Some (B, Tsend) else None) Tp Hsend)
    as [fs HshapeP].
  subst Tp.
  destruct (subtypeC_recv_inv p frecv Tq Hrecv) as [fr HshapeQ].
  subst Tq.
  destruct (subtypeC_send_inv q fs TprojP HsubP) as [fprojP HshapeProjP].
  subst TprojP.
  destruct (subtypeC_recv_inv p fr TprojQ HsubQ) as [fprojQ HshapeProjQ].
  subst TprojQ.
  assert (Hone :
    (fun n => if Nat.eqb n l then Some (B, Tsend) else None) l =
      Some (B, Tsend)).
  { rewrite Nat.eqb_refl; reflexivity. }
  destruct (subtypeC_send_branch q
    (fun n => if Nat.eqb n l then Some (B, Tsend) else None)
    fs l B Tsend Hsend Hone) as [TsendP [HsendP HsendPsub]].
  destruct (subtypeC_send_branch q fs fprojP l B TsendP HsubP HsendP)
    as [TsendProj [HsendProj _]].
  pose proof (proj_sort G p q fprojP fprojQ Hbal HprojP HprojQ) as Hsort.
  specialize (Hsort l).
  rewrite HsendProj in Hsort.
  destruct Hsort as [[HnoneP _] | [B' [TprojSend [TprojRecv
    [HprojSend HprojRecv]]]]].
  - discriminate.
  - inversion HprojSend; subst B' TprojSend.
    destruct (subtypeC_recv_branch p fr fprojQ l B TprojRecv HsubQ HprojRecv)
      as [TrecvQ [HrecvQ _]].
    exists fs, fr, TsendP, TrecvQ.
    split; [reflexivity|].
    split; [reflexivity|].
    split; [exact HsendP|].
    split; [exact HrecvQ|].
    exact HsendPsub.
Qed.

Lemma nth_error_replace_or_add_other:
forall A B (AEQ: EqDec A) (xs: list (A * B)) n ab k v,
nth_error xs n = Some ab ->
fst ab <> k ->
nth_error (replace_or_add xs (k, v)) n = Some ab.
Proof.
  induction xs as [|[a b] xs IH]; intros n ab k v Hnth Hneq; simpl in *.
  - destruct n; discriminate.
  - destruct n as [|n].
    + inversion Hnth; subst ab; simpl.
      destruct (AEQ a k) as [Heq|Hne].
      * exfalso; apply Hneq; simpl; congruence.
      * reflexivity.
    + destruct (AEQ a k) as [Heq|Hne].
      * simpl; exact Hnth.
      * simpl; f_equal; eapply IH; eauto.
Qed.

Lemma nth_error_replace_or_add_other_inv:
forall A B (AEQ: EqDec A) (xs: list (A * B)) n ab k v,
nth_error (replace_or_add xs (k, v)) n = Some ab ->
fst ab <> k ->
nth_error xs n = Some ab.
Proof.
  induction xs as [|[a b] xs IH]; intros n ab k v Hnth Hneq.
  - destruct n as [|n]; simpl in Hnth.
    + inversion Hnth; subst ab; exfalso; apply Hneq; reflexivity.
    + rewrite nth_error_nil in Hnth; discriminate Hnth.
  - destruct n as [|n].
    + simpl in Hnth |- *.
      case_analysis; simpl in *; cleanup.
      all: try solve [simpl in Hneq; exfalso; apply Hneq; reflexivity].
      all: try solve [inversion Hnth; reflexivity].
    + simpl in Hnth |- *.
      case_analysis; simpl in *; cleanup; eauto.
Qed.

Lemma nth_error_replace_or_add_at:
forall A B (AEQ: EqDec A) (xs: list (A * B)) n k old v,
NoDup (map fst xs) ->
nth_error xs n = Some (k, old) ->
nth_error (replace_or_add xs (k, v)) n = Some (k, v).
Proof.
  induction xs as [|[a b] xs IH]; intros n k old v Hnd Hnth; simpl in *.
  - destruct n; discriminate.
  - inversion Hnd as [|? ? Hnot Hnd']; subst.
    destruct n as [|n].
    + inversion Hnth; subst a old.
      destruct (AEQ k k) as [Heq|Hne]; [reflexivity|contradiction].
    + destruct (AEQ a k) as [Heq|Hne].
      * exfalso.
        apply Hnot.
        rewrite Heq.
        apply in_map_iff.
        exists (k, old).
        split; [reflexivity|].
        eapply nth_error_In; exact Hnth.
      * simpl; f_equal; eapply IH; eauto.
Qed.

Lemma nth_error_delta_insert_at:
forall delta p T T0 n,
nth_error (elems participant ltt delta) n = Some (p, T0) ->
nth_error (elems participant ltt (insert delta p T)) n = Some (p, T).
Proof.
  intros delta p T T0 n Hnth.
  unfold insert; simpl.
  eapply nth_error_replace_or_add_at; eauto.
  apply (proj1 (specs _ _ delta)).
Qed.

Lemma nth_error_delta_insert_other:
forall delta p q T T0 n,
p <> q ->
nth_error (elems participant ltt delta) n = Some (p, T0) ->
nth_error (elems participant ltt (insert delta q T)) n = Some (p, T0).
Proof.
  intros delta p q T T0 n Hneq Hnth.
  unfold insert; simpl.
  eapply nth_error_replace_or_add_other; eauto.
Qed.

Lemma nth_error_delta_insert_other_inv:
forall delta p q T T0 n,
p <> q ->
nth_error (elems participant ltt (insert delta q T)) n = Some (p, T0) ->
nth_error (elems participant ltt delta) n = Some (p, T0).
Proof.
  intros delta p q T T0 n Hneq Hnth.
  unfold insert in Hnth; simpl in Hnth.
  eapply nth_error_replace_or_add_other_inv; eauto.
Qed.

Lemma delta_insert_key_permutation:
forall delta p T,
In p (map fst (elems participant ltt delta)) ->
Permutation
  (map fst (elems participant ltt (insert delta p T)))
  (map fst (elems participant ltt delta)).
Proof.
  intros delta p T Hp.
  apply NoDup_Permutation.
  - exact (proj1 (specs _ _ (insert delta p T))).
  - exact (proj1 (specs _ _ delta)).
  - intro k; split; intro Hk.
    + apply in_map_iff in Hk as [[k' T0] [Hfst Hmem]].
      simpl in Hfst; subst k'.
      apply (proj1 ((proj2 (specs _ _ (insert delta p T))) k T0)) in Hmem.
      destruct (participant_dec p k) as [Hpk|Hpk].
      * subst k; exact Hp.
      * rewrite insert_neq in Hmem by exact Hpk.
        apply in_map_iff; exists (k, T0); split; [reflexivity|].
        apply (proj2 ((proj2 (specs _ _ delta)) k T0)); exact Hmem.
    + apply in_map_iff in Hk as [[k' T0] [Hfst Hmem]].
      simpl in Hfst; subst k'.
      apply (proj1 ((proj2 (specs _ _ delta)) k T0)) in Hmem.
      destruct (participant_dec p k) as [Hpk|Hpk].
      * subst k.
        apply in_map_iff in Hp as [[k' T1] [Hfst Hmem0]].
        simpl in Hfst; subst k'.
        apply in_map_iff; exists (p, T); split; [reflexivity|].
        apply (proj2 ((proj2 (specs _ _ (insert delta p T))) p T)).
        rewrite insert_eq; reflexivity.
      * apply in_map_iff; exists (k, T0); split; [reflexivity|].
        apply (proj2 ((proj2 (specs _ _ (insert delta p T))) k T0)).
        rewrite insert_neq by exact Hpk; exact Hmem.
Qed.

Lemma delta_insert_key_exists_after:
forall delta p q Tp,
p <> q ->
In q (map fst (elems participant ltt delta)) ->
In q (map fst (elems participant ltt (insert delta p Tp))).
Proof.
  intros delta p q Tp Hneq Hq.
  apply in_map_iff in Hq as [[q' T] [Hfst Hmem]].
  simpl in Hfst; subst q'.
  apply (proj1 ((proj2 (specs _ _ delta)) q T)) in Hmem.
  apply in_map_iff; exists (q, T); split; [reflexivity|].
  apply (proj2 ((proj2 (specs _ _ (insert delta p Tp))) q T)).
  rewrite insert_neq by exact Hneq; exact Hmem.
Qed.

Lemma delta_insert_pair_permutation:
forall delta p q Tp Tq,
p <> q ->
In p (map fst (elems participant ltt delta)) ->
In q (map fst (elems participant ltt delta)) ->
Permutation
  (map fst (elems participant ltt
    (insert (insert delta p Tp) q Tq)))
  (map fst (elems participant ltt delta)).
Proof.
  intros delta p q Tp Tq Hneq Hp Hq.
  eapply Permutation_trans.
  - apply delta_insert_key_permutation.
    eapply delta_insert_key_exists_after; eauto.
  - apply delta_insert_key_permutation; exact Hp.
Qed.

Lemma delta_insert_length:
forall delta p T,
In p (map fst (elems participant ltt delta)) ->
Datatypes.length (elems participant ltt (insert delta p T)) =
Datatypes.length (elems participant ltt delta).
Proof.
  intros delta p T Hp.
  apply in_map_iff in Hp as [[p' T0] [Hfst Hmem]].
  simpl in Hfst; subst p'.
  unfold insert; simpl.
  apply replace_or_add_In_length.
  exists T0; exact Hmem.
Qed.

Lemma delta_insert_pair_length:
forall delta p q Tp Tq,
p <> q ->
In p (map fst (elems participant ltt delta)) ->
In q (map fst (elems participant ltt delta)) ->
Datatypes.length (elems participant ltt
  (insert (insert delta p Tp) q Tq)) = Datatypes.length (elems participant ltt delta).
Proof.
  intros delta p q Tp Tq Hneq Hp Hq.
  rewrite delta_insert_length.
  - apply delta_insert_length; exact Hp.
  - eapply delta_insert_key_exists_after; eauto.
Qed.

Lemma typecheck_session_after_comm_update `{good_merge}:
forall qcontext M M' delta lqc delta2 p q np nq Tp Tq Tp' Tq'
  qcP qcQ qcP' qcQ' lqc2 G2 P' Q',
delta2 = insert (insert delta p Tp') q Tq' ->
p <> q ->
(forall pt T qc,
  In (pt, T, qc) (combine (elems participant ltt delta) lqc) ->
  exists P, M pt = Some P /\ typecheck_process (nil, nil, qc) P T) ->
regGtt G2 ->
balancedG G2 ->
assoc_gctx delta2 G2 ->
FMap.partition qubit_reference unit qcontext lqc2 ->
Datatypes.length lqc2 = Datatypes.length (elems participant ltt delta2) ->
Permutation (map fst (elems participant ltt delta2)) (session_participants M') ->
nth_error (elems participant ltt delta) np = Some (p, Tp) ->
nth_error (elems participant ltt delta) nq = Some (q, Tq) ->
nth_error lqc np = Some qcP ->
nth_error lqc nq = Some qcQ ->
nth_error (elems participant ltt delta2) np = Some (p, Tp') ->
nth_error (elems participant ltt delta2) nq = Some (q, Tq') ->
nth_error lqc2 np = Some qcP' ->
nth_error lqc2 nq = Some qcQ' ->
(forall n, n <> np -> n <> nq -> nth_error lqc2 n = nth_error lqc n) ->
M' p = Some P' ->
M' q = Some Q' ->
(forall pt, pt <> p -> pt <> q -> M' pt = M pt) ->
typecheck_process (nil, nil, qcP') P' Tp' ->
typecheck_process (nil, nil, qcQ') Q' Tq' ->
typecheck_session qcontext M' delta2 G2.
Proof.
  intros qcontext M M' delta lqc delta2 p q np nq Tp Tq Tp' Tq'
    qcP qcQ qcP' qcQ' lqc2 G2 P' Q' Hdelta2 Hneq HtypedOld
    Hreg2 Hbal2 Hassoc2 Hpart2 Hlength2 Hperm2 HdeltaP HdeltaQ
    HqcP HqcQ HdeltaP2 HdeltaQ2 HqcP2 HqcQ2 HqcOther HlookupP HlookupQ
    HlookupOther HtypedP HtypedQ.
  subst delta2.
  unfold typecheck_session.
  exists lqc2.
  split; [exact Hreg2|].
  split; [exact Hbal2|].
  split; [exact Hassoc2|].
  split; [exact Hpart2|].
  split; [exact Hlength2|].
  split; [exact Hperm2|].
  intros r T qc Hin.
  apply In_iff_nth_error in Hin.
  destruct Hin as [n Htriple].
  apply nth_error_combine in Htriple.
  destruct Htriple as [HdeltaAt HqcAt].
  pose proof (proj1 (specs _ _ (insert (insert delta p Tp') q Tq'))) as Hnodup2.
  destruct (participant_dec r p) as [Hrp|Hrp].
  - subst r.
    assert (Hindex : n = np /\ T = Tp').
    {
      eapply (nth_error_NoDup_l_index_eq 
        (elems participant ltt (insert (insert delta p Tp') q Tq'))
         n np HdeltaAt HdeltaP2 Hnodup2 eq_refl).
    }
    destruct Hindex as [-> ->].
    rewrite HqcP2 in HqcAt; inversion HqcAt; subst qc.
    exists P'; split; assumption.
  - destruct (participant_dec r q) as [Hrq|Hrq].
    + subst r.
      assert (Hindex : n = nq /\ T = Tq').
      {
        exact (nth_error_NoDup_l_index_eq 
          (elems participant ltt (insert (insert delta p Tp') q Tq'))
           n nq HdeltaAt HdeltaQ2 Hnodup2 eq_refl).
      }
      destruct Hindex as [-> ->].
      rewrite HqcQ2 in HqcAt; inversion HqcAt; subst qc.
      exists Q'; split; assumption.
    + assert (HnP : n <> np).
      {
        intro Heq; subst n.
        rewrite HdeltaP2 in HdeltaAt.
        inversion HdeltaAt; congruence.
      }
      assert (HnQ : n <> nq).
      {
        intro Heq; subst n.
        rewrite HdeltaQ2 in HdeltaAt.
        inversion HdeltaAt; congruence.
      }
      assert (HdeltaInner :
        nth_error (elems participant ltt (insert delta p Tp')) n =
          Some (r, T)).
      {
        eapply nth_error_delta_insert_other_inv; eauto.
      }
      assert (HdeltaOld :
        nth_error (elems participant ltt delta) n = Some (r, T)).
      {
        eapply nth_error_delta_insert_other_inv with
          (q := p) (T := Tp') (T0 := T) (n := n).
        - exact Hrp.
        - exact HdeltaInner.
      }
      rewrite (HqcOther n HnP HnQ) in HqcAt.
      assert (HoldTriple :
        nth_error (combine (elems participant ltt delta) lqc) n =
          Some ((r, T), qc)).
      {
        eapply nth_error_combine_merge; eauto.
      }
      apply nth_error_In in HoldTriple.
      destruct (HtypedOld r T qc HoldTriple) as [P0 [Hlookup Htyped]].
      exists P0; split.
      * rewrite (HlookupOther r Hrp Hrq); exact Hlookup.
      * exact Htyped.
Qed.

Lemma typecheck_session_component_of_map `{good_merge}:
forall (qcontext: qubit_context) (M: session) (delta: typing_context)
  (lqc: list qubit_context),
Permutation (map fst (elems participant ltt delta)) (session_participants M) ->
Datatypes.length lqc = Datatypes.length (elems participant ltt delta) ->
(forall pt T qc,
  In (pt, T, qc) (combine (elems participant ltt delta) lqc) ->
  exists P, M pt = Some P /\ typecheck_process (nil, nil, qc) P T) ->
forall p P, M p = Some P ->
exists n T qc,
nth_error (elems participant ltt delta) n = Some (p, T) /\
nth_error lqc n = Some qc /\
delta p = Some T /\
 typecheck_process (nil, nil, qc) P T.
Proof.
  intros qcontext M delta lqc Hperm Hlen Htyped p P HM.
  assert (HinM : In p (session_participants M)).
  {
    unfold session_participants.
    apply in_map_iff.
    exists (p, P); split; [reflexivity|].
    apply (proj2 ((proj2 (specs _ _ M)) p P)); exact HM.
  }
  assert (HinDelta : In p (map fst (elems participant ltt delta))).
  { eapply Permutation_in; [apply Permutation_sym; exact Hperm|exact HinM]. }
  apply in_map_iff in HinDelta as [[p' T] [Hfst Hpair]].
  simpl in Hfst; subst p'.
  assert (Hle : Datatypes.length (elems participant ltt delta) <= Datatypes.length lqc)
    by lia.
  destruct (in_combine_ex_r _ lqc Hle (p, T) Hpair) as [qc HinTriple].
  pose proof HinTriple as HinTripleOrig.
  apply In_iff_nth_error in HinTriple.
  destruct HinTriple as [n Htriple].
  apply nth_error_combine in Htriple.
  destruct Htriple as [HdeltaAt HqcAt].
  destruct (Htyped p T qc HinTripleOrig) as [P0 [HM0 Hproc]].
  rewrite HM in HM0; inversion HM0; subst P0.
  exists n, T, qc.
  repeat split; eauto.
  apply (proj1 ((proj2 (specs _ _ delta)) p T)); exact Hpair.
Qed.

Lemma partition_component_included:
forall qcontext lqc n qc,
FMap.partition qubit_reference unit qcontext lqc ->
nth_error lqc n = Some qc ->
included qc qcontext.
Proof.
  intros qcontext lqc n qc Hpart Hnth.
  unfold FMap.partition in Hpart.
  destruct Hpart as [Hcovers _].
  unfold FMap.covers in Hcovers.
  unfold included; intros k v Hqc.
  apply Hcovers.
  exists qc; split.
  - eapply nth_error_In; exact Hnth.
  - exact Hqc.
Qed.

Lemma assoc_projection_complete `{good_merge} : forall (G:gtt) (Gl:typing_context),
  regGtt G -> balancedG G -> assoc_gctx Gl G -> projectableA G.
Proof.
  intros G Gl Hreg Hbal Hassoc.
  destruct Hassoc as [Hcover Htypes].
  unfold projectableA; intros pt.
  pose proof (always_exists (Gl pt)) as Hsome.
  destruct Hsome as [T Hsome].
  destruct T as [T0|].
  - destruct (Htypes pt T0 Hsome) as [T' [Hproj Hsub]].
    exists T'; exact Hproj.
  - destruct (dec_isgPartsC G pt Hreg) as [Hpart|Hnotpart].
    + destruct (Hcover pt Hpart) as [T' Hcontra].
      rewrite Hsome in Hcontra; discriminate.
    + exists ltt_end.
      pfold; constructor; exact Hnotpart.
Qed.

Lemma assoc_on_for_ctx_step `{good_merge} : forall (G:gtt) (Gl Gl':typing_context)
  (p q:participant) (l:label) (B:sort),
  regGtt G -> balancedG G -> assoc_gctx Gl G ->
  ctx_step_f Gl p q l B Gl' ->
  exists G', assoc_gctx Gl' G' /\ gttstepC G G' p q l /\ balancedG G'.
Proof.
  intros G Gl Gl' p q l B Hreg Hbal Hassoc Hstep.
  pose proof (assoc_projection_complete G Gl Hreg Hbal Hassoc) as HprojA.
  inversion Hstep as
    [Gl0 Gl1 p0 q0 l0 fs fr S S' Ts Tr Hneq Hgp Hgq Hfs Hfr Hupdate].
  subst Gl0 Gl1 p0 q0 l0.
  subst Ts.
  destruct Hassoc as [Hcover Htypes].
  destruct (Htypes p (ltt_send q fs) Hneq) as [Tp [HprojP HsubP]].
  destruct (Htypes q (ltt_recv p fr) Hgp) as [Tq [HprojQ HsubQ]].
  destruct (subtypeC_send_inv q fs Tp HsubP) as [fp HshapeP].
  destruct (subtypeC_recv_inv p fr Tq HsubQ) as [fq HshapeQ].
  subst Tp Tq.
  destruct (subtypeC_send_branch q fs fp l B S HsubP Hgq)
    as [TprojSend [Hfp HsendSub]].
  pose proof (proj_sort G p q fp fq Hbal HprojP HprojQ l) as Hsort.
  rewrite Hfp in Hsort.
  destruct Hsort as [[Hnone _]|[S0 [Tsend0 [Trecv0 [Hfp0 Hfq0]]]]].
  - discriminate.
  - inversion Hfp0; subst S0 Tsend0.
    destruct (subtypeC_recv_branch p fr fq l B Trecv0 HsubQ Hfq0)
      as [TrecvLocal [HfrLocal HrecvSub]].
    rewrite HfrLocal in Hfs; inversion Hfs; subst S'.
    destruct (proj_to_step G p q l fp fq (B, TprojSend)
      Hbal Tr HprojP HprojQ Hfp) as [G' Hgstep].
    pose proof (balanced_step G G' p q l Hbal Hreg Hgstep HprojA) as Hbal'.
    assert (HlookupP : Gl' p = Some S).
    { specialize (Hfr p).
      destruct (participant_dec p p); [exact Hfr|contradiction]. }
    assert (HlookupQ : Gl' q = Some TrecvLocal).
    { specialize (Hfr q).
      destruct (participant_dec q p) as [Hpq|Hpq]; [congruence|].
      destruct (participant_dec q q); [exact Hfr|contradiction]. }
    assert (Hsame : forall pt, pt <> p -> pt <> q -> Gl pt = Gl' pt).
    { intros pt HptP HptQ.
      specialize (Hfr pt).
      destruct (participant_dec pt p); [congruence|].
      destruct (participant_dec pt q); [congruence|exact Hfr]. }
    exists G'; split; [|split; [exact Hgstep|exact Hbal']].
    split.
    + intros pt HptG'.
      pose proof (pt_step_back G G' p q l pt Hgstep HptG') as HptG.
      destruct (Hcover pt HptG) as [Told Hold].
      destruct (participant_dec pt p) as [->|HptP].
      * exists S; exact HlookupP.
      * destruct (participant_dec pt q) as [->|HptQ].
        -- exists TrecvLocal; exact HlookupQ.
        -- exists Told; rewrite <- (Hsame pt HptP HptQ); exact Hold.
    + intros pt T0 Hlookup.
      destruct (participant_dec pt p) as [->|HptP].
      * rewrite HlookupP in Hlookup; inversion Hlookup; subst T0.
        destruct (typ_after_step_p G G' p q l fp Hbal Hreg Hgstep HprojP)
          as [S0 [T0 [Hbranch HprojPost]]].
        rewrite Hfp in Hbranch; inversion Hbranch; subst S0 T0.
        exists TprojSend; split; [exact HprojPost|exact HsendSub].
      * destruct (participant_dec pt q) as [->|HptQ].
        -- rewrite HlookupQ in Hlookup; inversion Hlookup; subst T0.
           destruct (typ_after_step_q G G' p q l fq Hbal Hreg Hgstep HprojQ)
             as [S0 [T0 [Hbranch HprojPost]]].
           rewrite Hfq0 in Hbranch; inversion Hbranch; subst S0 T0.
           exists Trecv0; split; [exact HprojPost|exact HrecvSub].
        -- rewrite <- (Hsame pt HptP HptQ) in Hlookup.
           destruct (Htypes pt T0 Hlookup) as [Tproj [Hproj Hsub]].
           assert (Hpr : p <> pt) by congruence.
           assert (Hqr : q <> pt) by congruence.
           destruct (typ_after_step_r G G' p q pt l Tproj Hbal Hreg Hgstep
             Hpr Hqr Hproj) as [Tpost [HprojPost HsubPost]].
           exists Tpost; split; [exact HprojPost|].
           eapply stTrans; eauto.
Qed.

Definition state_covers_qubits_in_context (qcontext : qubit_context)
    (qstate : quantum_state) :=
  forall q, qcontext q = Some tt ->
    (proj1_sig (projT1 qstate)) q <> None.

Theorem subject_reduction_via_association_1_exact_with_cover `{good_merge}:
forall M M' pi qstate qstate' delta p qcontext G,
step (qstate, M) (Tau p) (qstate', M') pi ->
typecheck_session qcontext M delta G ->
state_covers_qubits_in_context qcontext qstate ->
state_only_contains_qubits_in_context qcontext qstate ->
exists qcontext2,
typecheck_session qcontext2 M' delta G /\
state_covers_qubits_in_context qcontext2 qstate' /\
state_only_contains_qubits_in_context qcontext2 qstate'.
Proof.
    intros M M' pi qstate qstate' delta p qcontext G H1.

    eapply (step_ind (fun s1 a s2 r =>
    forall M M' qstate qstate' delta p qcontext,
    a = Tau p ->
    s1 = (qstate, M) ->
    s2 = (qstate', M') ->
    step s1 a s2 r ->
    typecheck_session qcontext M delta G ->
    state_covers_qubits_in_context qcontext qstate ->
    state_only_contains_qubits_in_context qcontext qstate ->
    exists qcontext2, typecheck_session qcontext2 M' delta G /\
    state_covers_qubits_in_context qcontext2 qstate' /\
    state_only_contains_qubits_in_context qcontext2 qstate'
    )); eauto; clear; intros; cleanup; try congruence.
    { (*newq*)
        symmetry in H1; inversionc H1.
        clear H4.
        unfold typecheck_session in *; cleanup.
        assume_fresh (exists T, In (p, T) (elems _ _ delta)).
        cleanup.

        eexists (insert qcontext ?[q] tt); split.
        {
            eapply_fresh (in_combine_ex_r _ lqc) in HA; eauto.
            cleanup.
            rename y into p_qc.
            eapply_fresh In_iff_nth_error in Hx; cleanup.

            eexists (updn lqc n (insert p_qc ?q tt)).
            split; eauto.
            split; eauto.
            split; eauto.
            split.
            {
                assume_fresh (exists l1 l2, lqc = l1 ++ p_qc::l2 /\ length l1 = n).
                cleanup.
                rewrite updn_app2; eauto.
                rewrite Nat.sub_diag.
                simpl.
                eapply partition_insert_new; eauto.
                left; shelve.
            }
            split.
            rewrite updn_length; eauto.

            split.
            shelve.

            intros pt0 T0 qc0 HcomponentInput.
            eapply_fresh In_iff_nth_error in HcomponentInput; cleanup.
            eapply nth_error_combine in Hx0, Hx1.
            cleanup; simpl in *.
            destruct (participant_dec p pt0); subst.
            {(*pt0 = p*)
                eapply_fresh H9 in Hx; cleanup.
                invert_typecheck; cleanup.
                assert (Hindex : n0 = n /\ T0 = T).
                {
                    eapply nth_error_NoDup_l_index_eq with
                      (l := elems participant ltt delta)
                      (ab1 := (pt0, T0)) (ab2 := (pt0, T))
                      (n := n0) (m := n).
                    - exact H10.
                    - exact H12.
                    - apply specs.
                    - reflexivity.
                }
                destruct Hindex as [Hindex Htype]; subst n0 T0.
                rewrite nth_error_updn_eq in H11.
                2: { eapply nth_error_length; exact H13. }
                inversion H11; subst qc0.
                eexists; split; eauto.
                simpl.
                eapply subst_expression_in_process_quantum with (d:=0).
                {
                    destruct (p_qc q) as [u|] eqn:Hpqc; [|reflexivity].
                    destruct u.
                    assert (Hpqc_in : In p_qc lqc) by (eapply in_combine_r; exact Hx).
                    unfold FMap.partition in H4; destruct H4 as [Hcovers _].
                    assert (Hglobal : qcontext q = Some tt).
                    {
                        apply (proj2 (Hcovers q tt)).
                        exists p_qc; split; assumption.
                    }
                    unfold state_covers_qubits_in_context in H6.
                    apply H6 in Hglobal.
                    destruct ((proj1_sig (projT1 qstate)) q) as [owner|] eqn:Hmap;
                        [|contradiction].
                    exfalso; apply Hfresh.
                    apply in_map_iff; exists (q, owner); split; [reflexivity|].
                    apply specs; exact Hmap.
                }
                exact Hx0.
            }
            {(*pt0 <> p*)
                assert (Hn : n0 <> n).
                {
                    intro Heq; subst n0.
                    rewrite H10 in H12; inversion H12; congruence.
                }
                rewrite nth_error_updn_neq in H11 by congruence.
                assert (HoldTriple :
                    nth_error (combine (elems participant ltt delta) lqc) n0 =
                    Some ((pt0, T0), qc0)).
                { eapply nth_error_combine_merge; eauto. }
                apply nth_error_In in HoldTriple.
                destruct (H9 pt0 T0 qc0 HoldTriple) as [P0 [Hlookup Htyped]].
                exists P0; split; eauto.
            }
            lia.
        }
        split.
        {
            unfold state_covers_qubits_in_context in *; simpl in *.
            intros q0 Hctx.
            destruct (qr_dec q0 q) as [Heq|Hneq].
            - subst q0.
              destruct (qr_dec q q); simpl; congruence.
            - unfold add_new_qubit, quantum_map_of.
              cbn [proj1_sig projT1].
              destruct (qr_dec q q0) as [Heq|Hneq0].
              + exfalso; apply Hneq; symmetry; exact Heq.
              + simpl in Hctx |- *; apply H6; exact Hctx.
        }
        {
            unfold state_only_contains_qubits_in_context in *.
            intros q0.
            change
              ((insert (KEQ:= qr_dec) qcontext q tt) q0 = Some tt <->
               (insert (KEQ:= qr_dec) (proj1_sig (projT1 qstate)) q
                 (p, length (elems qubit_reference (participant * nat)
                   (proj1_sig (projT1 qstate))))) q0 <> None).
            destruct (qr_dec q q0) as [Heq|Hneq].
            - subst q0.
              repeat rewrite insert_eq; simpl.
              split; [intros _; discriminate|intros _; reflexivity].
            - repeat rewrite insert_neq by congruence.
              apply H7.
        }
    }
    {(* ite false *)
        symmetry in H2; inversion H2; subst.
        clear H5.
        unfold typecheck_session in *;
        cleanup.
        assume_fresh (exists T, In (p, T) (elems _ _ delta)).
        cleanup.

        exists qcontext.
        split; eauto.
        exists lqc.
        intuition eauto.
        shelve.

        eapply_fresh H11 in H2; cleanup.
        destruct (participant_dec p p0); cleanup.
        rewrite insert_eq; eauto.
        eexists; split; eauto.
        invert_typecheck; cleanup; eauto.
        rewrite insert_neq; eauto.
    }
    {(* ite true *)
        symmetry in H2; inversion H2; subst.
        clear H5.
        unfold typecheck_session in *;
        cleanup.
        assume_fresh (exists T, In (p, T) (elems _ _ delta)).
        cleanup.

        exists qcontext.
        split; eauto.
        exists lqc.
        intuition eauto.
        shelve.

        eapply_fresh H11 in H2; cleanup.
        destruct (participant_dec p p0); cleanup.
        rewrite insert_eq; eauto.
        eexists; split; eauto.
        invert_typecheck; cleanup; eauto.
        rewrite insert_neq; eauto.
    }
    {(* measure *)
        symmetry in H1; inversion H1; subst.
        unfold typecheck_session in *;
        cleanup.
        assume_fresh (exists T, In (p, T) (elems _ _  delta)).
        cleanup.

        exists (delete (KEQ:=qr_dec) qcontext q).
        split.
        {
            eapply_fresh (in_combine_ex_r _ lqc) in HA; eauto; cleanup.
            rename y into p_qc.
            eapply_fresh In_iff_nth_error in Hx; cleanup.
            rename n into q_index.
            rename n0 into n.

            set (lqc2 := updn lqc n (delete (KEQ:=qr_dec) p_qc q)).
            eexists lqc2.
            split; [exact H3|].
            split; [exact H4|].
            split; [exact H6|].
            split.
            {
                assert (Hlocal_n : nth_error lqc n = Some p_qc).
                { eapply nth_error_combine in Hx0; exact (proj2 Hx0). }
                assert (Hsplit : exists l1 l2,
                  lqc = l1 ++ p_qc :: l2 /\ length l1 = n).
                { apply nth_error_split; exact Hlocal_n. }
                assert (Howner : p_qc q <> None).
                {
                  destruct (H12 p T p_qc Hx) as [Pold [HMP Htyped]].
                  rewrite H in HMP; inversion HMP; subst Pold.
                  destruct (typecheck_process_p_measure_post T
                    (nil, nil, p_qc) P (Val (QVal q)) Htyped)
                    as [Hexpr _].
                  inversion Hexpr; subst.
                  unfold in_qubit_context in *; simpl in *.
                  congruence.
                }
                destruct Hsplit as [l1 [l2 [Hsplit Hsplit_len]]].
                simpl in H9.
                rewrite Hsplit in H9.
                assert (Hpart2 : FMap.partition qubit_reference unit
                  (delete (KEQ:=qr_dec) qcontext q) lqc2).
                {
                  unfold lqc2.
                  rewrite Hsplit.
                  rewrite updn_app2 by lia.
                  replace (n - length l1) with 0 by lia.
                  simpl.
                  eapply partition_delete; [exact H9|right; exact Howner].
                }
                exact Hpart2.
            }
            split.
            {
                unfold lqc2.
                rewrite updn_length.
                exact H10.
            }
            split.
            {
                eapply Permutation_trans.
                - exact H11.
                - apply Permutation_sym.
                  eapply session_participants_insert_In.
                  eapply specs; exact H.
            }
            intros p1 T0 qc HcomponentInput.
            eapply_fresh In_iff_nth_error in HcomponentInput; cleanup.
            eapply nth_error_combine in Hx0, Hx1.
            cleanup; simpl in *.
            destruct (participant_dec p p1) as [Hp|Hp].
            - subst p1.
              assert (Hindex : n0 = n /\ T0 = T).
              {
                eapply nth_error_NoDup_l_index_eq with
                  (l:=elems participant ltt delta)
                  (ab1:=(p,T0)) (ab2:=(p,T)) (n:=n0) (m:=n).
                - exact H13.
                - exact H15.
                - apply specs.
                - reflexivity.
              }
              destruct Hindex as [Hindex Htype]; subst n0 T0.
              rewrite nth_error_updn_eq in H14.
              2: { eapply nth_error_length; exact H16. }
              inversion H14; subst qc.
              exists (subst_expression_in_process 0 0 (Val (Bool r)) P).
              split; [reflexivity|].
              destruct (H12 p T p_qc Hx) as [Pold [HMP Hmeas]].
              rewrite H in HMP; inversion HMP; subst Pold.
              destruct (typecheck_process_p_measure_post T
                ([], [], p_qc) P (Val (QVal q)) Hmeas) as [_ Hcont].
              unfold remove_measured_expression_from_context,
                remove_from_qubit_context in Hcont.
              simpl in Hcont.
              eapply subst_expression_in_process_classical with
                (e:=Val (Primitives.Bool r)) (d:=0) (B:=header.Bool)
                (T:=T) (Gsr:=nil) (pvc:=nil)
                (qc:=delete (KEQ:=qr_dec) p_qc q).
              * exact Hcont.
              * simpl; constructor.
              * discriminate.
            - assert (Hindex : n0 <> n).
              { intro Heq; subst n0.
                rewrite H13 in H15; inversion H15; congruence. }
              rewrite nth_error_updn_neq in H14 by congruence.
              assert (Hold : In (p1, T0, qc)
                (combine (elems participant ltt delta) lqc)).
              {
                apply nth_error_In with (n:=n0).
                eapply nth_error_combine_merge; eauto.
              }
              destruct (H12 p1 T0 qc Hold) as [Pold [HMold Htyped]].
              exists Pold; split.
              * exact HMold.
              * exact Htyped.
            lia.
        }
        split.
        {
          unfold state_covers_qubits_in_context in *.
          cbn [measure_qubit_from_nonzero measure_qubit_nonzero].
          intros q0 Hctx.
          apply delete_Some in Hctx.
          destruct Hctx as [Hneq Hctx].
          apply H7 in Hctx.
          apply (proj2 (remove_and_reindex_qubit_map_lookup_none
            (proj1_sig (projT1 qstate)) q n q0)).
          split; [congruence|exact Hctx].
        }
        {
          unfold state_only_contains_qubits_in_context in *.
          cbn [measure_qubit_from_nonzero measure_qubit_nonzero].
          intros q0.
          split.
          - intro Hctx.
            apply delete_Some in Hctx as [Hneq Hctx].
            apply (proj2 (remove_and_reindex_qubit_map_lookup_none
              (proj1_sig (projT1 qstate)) q n q0)).
            split; [congruence|].
            apply (proj1 (H8 q0)); exact Hctx.
          - intro Hmap.
            apply (proj1 (remove_and_reindex_qubit_map_lookup_none
              (proj1_sig (projT1 qstate)) q n q0)) in Hmap
              as [Hneq Hmap].
            rewrite delete_neq by congruence.
            apply (proj2 (H8 q0)); exact Hmap.
        }
    }
    {(*Unitary*)
        symmetry in H4; inversion H4; cleanup.
        unfold typecheck_session in *;
        cleanup.
        assume_fresh (exists T, In (p, T) (elems _ _ delta)).
        cleanup.

        exists qcontext.
        split; eauto.
        exists lqc.
        intuition eauto.
        shelve.

        eapply_fresh H13 in H14; cleanup.
        destruct (participant_dec p p0); cleanup.
        rewrite insert_eq.
        eexists; split; eauto.
        invert_typecheck; cleanup; eauto.
        rewrite insert_neq; eauto.

        assert (Hsame_map :
          proj1_sig (projT1 qstate') = proj1_sig (projT1 qstate)).
        {
          unfold apply_unitary in H1.
          destruct (lt_dec 0
            (length (elems qubit_reference (participant * fin)
              (proj1_sig (projT1 qstate))))) as [Hpositive|Hzero];
            try discriminate.
          destruct (le_dec (length lq)
            (length (elems qubit_reference (participant * fin)
              (proj1_sig (projT1 qstate))))) as [Hbound|Hbound];
            try discriminate.
          destruct (NoDup_dec (TEQ := qr_dec) lq) as [Hnd|Hnd];
            try discriminate.
          destruct (get_all_values_certified
            (proj1_sig (projT1 qstate)) lq) as [certified|] eqn:Hcert;
            try discriminate.
          inversion H1; subst; reflexivity.
        }
        split.
        {
          unfold state_covers_qubits_in_context in *.
          intros q0 Hctx; rewrite Hsame_map; apply H9; exact Hctx.
        }
        {
          unfold state_only_contains_qubits_in_context in *.
          intros q0; rewrite Hsame_map; apply H10.
        }
    }
    { (* Recursion *)
        assert (Htyped_mid : typecheck_session qcontext M1' delta G).
        { eapply typecheck_session_unfoldM; eauto. }
        destruct (H2 M1' M' qstate qstate' delta p qcontext
          eq_refl eq_refl eq_refl H1 Htyped_mid H8 H9)
          as [qcontext2 [Htyped2 [Hcover2 Honly2]]].
        exists qcontext2; split; [exact Htyped2|].
        split; assumption.
    }
    Unshelve.
    all: try solve [
        match goal with
        | [H0: Permutation (map fst _)  (session_participants ?M) |- _] =>
            eapply specs, (in_map fst) in H;
            simpl in *;
            rewrite <- H0 in H;
            apply in_map_iff in H; cleanup;
             match goal with
            | [H: In ?x ?l |- exists _, In (fst ?x, _) ?l] =>
                destruct x; simpl in *; eauto
            end
        end].

    all: try solve [
        match goal with
        | [H: nth_error (combine _ ?lqc) ?n = Some _ |- exists _ _, ?lqc = _ ++ ?p_qc :: _ /\ length _ = ?n] =>
            eapply nth_error_combine in H; cleanup; simpl in *;
            apply nth_error_split; eauto
        end ].

    all: try solve [eapply specs in H; erewrite session_participants_insert_In; eauto].
    {
        destruct_fresh (qcontext q); eauto.
        exfalso; apply Hfresh.
        unfold state_covers_qubits_in_context in *.
        destruct u; apply H6 in HD.
        destruct_fresh ((projT1 qstate) ! q ); try congruence.
        apply specs in HD0.
        apply in_map_iff; eexists; split; eauto.
        simpl; eauto.
    }
Qed.

Theorem subject_reduction_via_association_1 `{good_merge}:
forall M M' pi qstate qstate' delta p qcontext G,
step (qstate, M) (Tau p) (qstate', M') pi ->
typecheck_session qcontext M delta G ->
state_only_contains_qubits_in_context qcontext qstate ->
exists qcontext2,
typecheck_session qcontext2 M' delta G /\
state_only_contains_qubits_in_context qcontext2 qstate'.
Proof.
  intros M M' pi qstate qstate' delta p qcontext G Hstep Htyped Hstate.
  assert (Hcovers : state_covers_qubits_in_context qcontext qstate).
  {
    unfold state_covers_qubits_in_context,
      state_only_contains_qubits_in_context in *.
    intros q Hctx.
    apply (proj1 (Hstate q)); exact Hctx.
  }
  destruct (subject_reduction_via_association_1_exact_with_cover
    M M' pi qstate qstate' delta p qcontext G
    Hstep Htyped Hcovers Hstate)
    as [qcontext2 [Htyped2 [_ Hstate2]]].
  exists qcontext2; split; assumption.
Qed.

Theorem subject_reduction_via_association_2 `{good_merge}: 
forall M M' pi qstate qstate' delta G p q l v qcontext,
step (qstate, M) (Transmit p q l v) (qstate', M') pi ->
typecheck_session qcontext M delta G ->
exists qcontext2 delta2 G2 e S, 
(match v with 
| QVal v => exists old n,
    exists (Hlookup : (proj1_sig (projT1 qstate)) v = Some (old, n)),
      qstate' = transfer_qubit_from_lookup
        (proj1_sig (projT1 qstate)) (proj2_sig (projT1 qstate))
        (proj1_sig (projT2 qstate)) (proj2_sig (projT2 qstate)) q v old n Hlookup
| _ => qstate = qstate'
end) /\
included qcontext2 qcontext /\
ctx_step_f delta p q l S delta2 /\
gttstepC G G2 p q l /\
evaluate_expression e = Some v /\
typecheck_expression (nil, nil, qcontext2) e S /\
typecheck_session qcontext M' delta2 G2.
Proof.
  intros M M' pi qstate qstate' delta G p q l v qcontext Hstep Htyped.
  eapply (step_ind (fun s1 a s2 r =>
    forall M0 M1 qstate0 qstate1 delta0 G0 p0 q0 l0 v0 qcontext0,
      a = Transmit p0 q0 l0 v0 ->
      s1 = (qstate0, M0) ->
      s2 = (qstate1, M1) ->
      step s1 a s2 r ->
      typecheck_session qcontext0 M0 delta0 G0 ->
      exists qcontext2 delta2 G2 e S,
        (match v0 with
         | QVal vq => exists old n,
             exists (Hlookup : (proj1_sig (projT1 qstate0)) vq = Some (old, n)),
               qstate1 = transfer_qubit_from_lookup
                 (proj1_sig (projT1 qstate0)) (proj2_sig (projT1 qstate0))
                 (proj1_sig (projT2 qstate0)) (proj2_sig (projT2 qstate0))
                 q0 vq old n Hlookup
         | _ => qstate0 = qstate1
         end) /\
        included qcontext2 qcontext0 /\
        ctx_step_f delta0 p0 q0 l0 S delta2 /\
        gttstepC G0 G2 p0 q0 l0 /\
        evaluate_expression e = Some v0 /\
        typecheck_expression (nil, nil, qcontext2) e S /\
        typecheck_session qcontext0 M1 delta2 G2)); eauto;
    clear; intros; cleanup;
    try match goal with
    | [H: Tau _ = Transmit _ _ _ _ |- _] => inversion H
    end.
    - (* Classical communication. *)
      inversion H6; subst.
      rename p0 into p; rename q0 into q; rename l1 into l0; rename v0 into v.
      unfold typecheck_session in H10.
      destruct H10 as [lqc [Hreg [Hbal [Hassoc [Hpart
        [Hlen [Hperm HtypedOld]]]]]]].
      destruct (typecheck_session_component_of_map qcontext0 M0 delta0 lqc Hperm Hlen HtypedOld
        p (p_send q l0 e P) H) as
        [np [Tp [qcP [HdeltaP [HqcP [HdeltaPmap HprocP]]]]]].
      destruct (typecheck_session_component_of_map qcontext0 M0 delta0 lqc Hperm Hlen HtypedOld
        q (p_recv p lQ) H1) as
        [nq [Tq [qcQ [HdeltaQ [HqcQ [HdeltaQmap HprocQ]]]]]].
      destruct (typecheck_process_p_send_post Tp q l0 e P
        (nil, nil, qcP) HprocP) as
        [B [Ts [HsubSend [Hexpr HcontP]]]].
      destruct (typecheck_process_p_recv_post Tq (nil, nil, qcQ) p lQ
        HprocQ) as [lBT [HsubRecv Hbranches]].
      assert (Hclosed : closed_expression_at 0 e).
      { eapply typecheck_expression_empty_vars_closed; [exact Hexpr|reflexivity]. }
      destruct (closed_expression_evaluates (nil, nil, qcP) e B Hexpr Hclosed)
        as [veval [Heval Hsort]].
      rewrite H4 in Heval; inversion Heval; subst veval.
      destruct (associated_send_recv_branch delta0 G0 p q l0 B Ts
        (fun n => onth n lBT) Tp Tq Hbal Hassoc HdeltaPmap HdeltaQmap
        HsubSend HsubRecv) as [fs [fr [Tsend [Trecv
        [HshapeP [HshapeQ [HbranchP [HbranchQ HsubSendCont]]]]]]]].
      pose proof (SForall2_onth_l l0 lQ lBT _ Q Hbranches H3)
        as Hselected.
      destruct Hselected as [BT [HnthBT HbranchProc]].
      rewrite HshapeQ in HsubRecv.
      destruct (subtypeC_recv_branch p (fun n => onth n lBT) fr l0 B Trecv
        HsubRecv HbranchQ) as [Tbranch [HbranchRecv HsubBranch]].
      rewrite HbranchRecv in HnthBT; inversion HnthBT; subst BT.
      assert (Hnpnq : np <> nq).
      { intro Heq; subst nq; rewrite HdeltaP in HdeltaQ; inversion HdeltaQ; congruence. }
      assert (HkeyP : In p (map fst (elems participant ltt delta0))).
      { apply in_map_iff; exists (p, Tp); split; [reflexivity|eapply nth_error_In; exact HdeltaP]. }
      assert (HkeyQ : In q (map fst (elems participant ltt delta0))).
      { apply in_map_iff; exists (q, Tq); split; [reflexivity|eapply nth_error_In; exact HdeltaQ]. }
      pose proof (partition_component_included qcontext0 lqc np qcP Hpart HqcP)
        as HincludeP.
      set (delta2 := insert (insert delta0 p Tsend) q Trecv).
      set (Mnew := insert (insert M0 q
        (subst_expression_in_process 0 0 (Val v) Q)) p P).
      assert (Hdelta2 : delta2 = insert (insert delta0 p Tsend) q Trecv)
        by reflexivity.
      assert (HdeltaP2 : nth_error (elems participant ltt delta2) np = Some (p, Tsend)).
      { unfold delta2; eapply nth_error_delta_insert_other.
        - congruence.
        - eapply nth_error_delta_insert_at; exact HdeltaP. }
      assert (HdeltaQ2 : nth_error (elems participant ltt delta2) nq = Some (q, Trecv)).
      { unfold delta2; eapply nth_error_delta_insert_at.
        eapply nth_error_delta_insert_other; [congruence|exact HdeltaQ]. }
      assert (Hctx : ctx_step_f delta0 p q l0 B delta2).
      { unfold delta2; eapply step_sr.
        - exact H2.
        - rewrite HshapeP in HdeltaPmap; exact HdeltaPmap.
        - rewrite HshapeQ in HdeltaQmap; exact HdeltaQmap.
        - exact HbranchP.
        - exact HbranchQ.
        intros pt; destruct (participant_dec pt p) as [->|Hp].
        - rewrite insert_neq by (symmetry; exact H2).
          rewrite insert_eq; reflexivity.
        - destruct (participant_dec pt q) as [->|Hq].
          + rewrite insert_eq; reflexivity.
          + rewrite insert_neq by (symmetry; exact Hq).
            rewrite insert_neq by (symmetry; exact Hp); reflexivity. }
      destruct (assoc_on_for_ctx_step G0 delta0 delta2 p q l0 B
        Hreg Hbal Hassoc Hctx)
        as [G2 [Hassoc2 [Hgstep Hbal2]]].
      assert (Hreg2 : regGtt G2).
      { eapply regGtt_after_step with (G:=G0) (G':=G2) (p:=p) (q:=q) (l:=l0).
        - exact Hreg.
        - exact Hbal.
        - exact Hgstep. }
      assert (Hlength2 : Datatypes.length lqc =
        Datatypes.length (elems participant ltt delta2)).
      { unfold delta2; rewrite delta_insert_pair_length; try assumption. }
      assert (HsessionPerm : Permutation (session_participants M0)
        (session_participants Mnew)).
      {
        assert (HinQpair : In (q, p_recv p lQ) (elems participant process M0)).
        { apply (proj2 ((proj2 (specs _ _ M0)) q (p_recv p lQ))); exact H1. }
        pose proof (session_participants_insert_In M0 q (p_recv p lQ)
          (subst_expression_in_process 0 0 (Val v) Q) HinQpair) as HpartQ.
        assert (HmidP : insert M0 q (subst_expression_in_process 0 0 (Val v) Q) p =
          Some (p_send q l0 e P)).
        { rewrite insert_neq by (symmetry; exact H2); exact H. }
        assert (HinMidP : In (p, p_send q l0 e P)
          (elems participant process
            (insert M0 q (subst_expression_in_process 0 0 (Val v) Q)))).
        { apply (proj2 ((proj2 (specs _ _
            (insert M0 q (subst_expression_in_process 0 0 (Val v) Q))))
            p (p_send q l0 e P))); exact HmidP. }
        pose proof (session_participants_insert_In
          (insert M0 q (subst_expression_in_process 0 0 (Val v) Q)) p
          (p_send q l0 e P) P HinMidP) as HpartP.
        unfold Mnew; eapply Permutation_trans.
        - exact (Permutation_sym HpartQ).
        - exact (Permutation_sym HpartP).
      }
      assert (Hperm2 : Permutation (map fst (elems participant ltt delta2))
        (session_participants Mnew)).
      { unfold delta2; eapply Permutation_trans.
        - apply delta_insert_pair_permutation; assumption.
        - eapply Permutation_trans; [exact Hperm|exact HsessionPerm]. }
      assert (HlookupP : Mnew p = Some P).
      { unfold Mnew; rewrite insert_eq; reflexivity. }
      assert (HlookupQ : Mnew q = Some (subst_expression_in_process 0 0 (Val v) Q)).
      { unfold Mnew; rewrite insert_neq by exact H2; rewrite insert_eq; reflexivity. }
      assert (HlookupOther : forall pt, pt <> p -> pt <> q -> Mnew pt = M0 pt).
      { intros pt Hp Hq; unfold Mnew; rewrite insert_neq by (symmetry; exact Hp);
        rewrite insert_neq by (symmetry; exact Hq); reflexivity. }
      destruct (sort_eqdec B Qubit) as [HBQ|HBQ].
      + subst B.
        inversion Hsort; subst v.
        exfalso; eapply H5; reflexivity.
      + assert (Hval : typecheck_expression (nil, nil, qcQ) (Val v) B).
        { destruct v as [n|b|vq].
          - assert (B = header.Nat) by (inversion Hsort; reflexivity); subst B; constructor.
          - assert (B = header.Bool) by (inversion Hsort; reflexivity); subst B; constructor.
          - inversion Hsort; subst B; contradiction. }
        assert (HBneq : B <> Qubit) by exact HBQ.
        pose proof (subst_expression_in_process_classical Q (Val v) 0 B Tbranch
          nil nil qcQ HbranchProc Hval HBneq) as HrecvSub.
        assert (HrecvPost : typecheck_process (nil, nil, qcQ)
          (subst_expression_in_process 0 0 (Val v) Q) Trecv).
        { eapply T_sub with (T:=Tbranch); [exact HrecvSub|exact HsubBranch]. }
        assert (HsenderPost : typecheck_process (nil, nil, qcP) P Tsend).
        { destruct B; simpl in HcontP.
          - eapply T_sub with (T:=Ts); [exact HcontP|exact HsubSendCont].
          - eapply T_sub with (T:=Ts); [exact HcontP|exact HsubSendCont].
          - exfalso; apply HBQ; reflexivity. }
        assert (HtypedNew : typecheck_session qcontext0
          Mnew delta2 G2).
        { eapply typecheck_session_after_comm_update with
            (lqc:=lqc) (np:=np) (nq:=nq) (Tp:=Tp) (Tq:=Tq)
            (Tp':=Tsend) (Tq':=Trecv) (qcP:=qcP) (qcQ:=qcQ)
            (qcP':=qcP) (qcQ':=qcQ) (lqc2:=lqc) (P':=P)
            (Q':=subst_expression_in_process 0 0 (Val v) Q); eauto.
        }
        exists qcP, delta2, G2, e, B.
        split.
        { destruct v as [n|b|vq]; simpl; try reflexivity.
          exfalso; apply (H5 vq); reflexivity. }
        split; [exact HincludeP|].
        split; [exact Hctx|].
        split; [exact Hgstep|].
        split; [exact H4|].
        split; [exact Hexpr|].
        exact HtypedNew.
    - (* Quantum communication. *)
      inversion H6; subst.
      rename p0 into p; rename q0 into q; rename l1 into l0.
      unfold typecheck_session in H10.
      destruct H10 as [lqc [Hreg [Hbal [Hassoc [Hpart
        [Hlen [Hperm HtypedOld]]]]]]].
      destruct (typecheck_session_component_of_map qcontext0 M0 delta0 lqc Hperm Hlen HtypedOld
        p (p_send q l0 e P) H) as
        [np [Tp [qcP [HdeltaP [HqcP [HdeltaPmap HprocP]]]]]].
      destruct (typecheck_session_component_of_map qcontext0 M0 delta0 lqc Hperm Hlen HtypedOld
        q (p_recv p lQ) H1) as
        [nq [Tq [qcQ [HdeltaQ [HqcQ [HdeltaQmap HprocQ]]]]]].
      destruct (typecheck_process_p_send_post Tp q l0 e P
        (nil, nil, qcP) HprocP) as
        [B [Ts [HsubSend [Hexpr HcontP]]]].
      destruct (typecheck_process_p_recv_post Tq (nil, nil, qcQ) p lQ
        HprocQ) as [lBT [HsubRecv Hbranches]].
      assert (Hclosed : closed_expression_at 0 e).
      { eapply typecheck_expression_empty_vars_closed; [exact Hexpr|reflexivity]. }
      destruct (closed_expression_evaluates (nil, nil, qcP) e B Hexpr Hclosed)
        as [veval [Heval Hsort]].
      rewrite H4 in Heval; inversion Heval; subst veval.
      inversion Hsort; subst B.
      pose proof H4 as HevalOrig.
      pose proof Hexpr as HexprOrig.
      destruct (closed_qubit_expression_literal (nil, nil, qcP) e Hexpr Hclosed)
        as [qv He].
      rewrite He in H4; simpl in H4; inversion H4; subst qv.
      rewrite He in Hexpr; inversion Hexpr.
      assert (HownerP : qcP v = Some tt) by assumption.
      rewrite He in HcontP; simpl in HcontP.
      unfold remove_from_qubit_context in HcontP; simpl in HcontP.
      destruct (associated_send_recv_branch delta0 G0 p q l0 header.Qubit Ts
        (fun n => onth n lBT) Tp Tq Hbal Hassoc HdeltaPmap HdeltaQmap
        HsubSend HsubRecv) as [fs [fr [Tsend [Trecv
        [HshapeP [HshapeQ [HbranchP [HbranchQ HsubSendCont]]]]]]]].
      pose proof (SForall2_onth_l l0 lQ lBT _ Q Hbranches H3)
        as Hselected.
      destruct Hselected as [BT [HnthBT HbranchProc]].
      rewrite HshapeQ in HsubRecv.
      destruct (subtypeC_recv_branch p (fun n => onth n lBT) fr l0
        header.Qubit Trecv HsubRecv HbranchQ)
        as [Tbranch [HbranchRecv HsubBranch]].
      rewrite HbranchRecv in HnthBT; inversion HnthBT; subst BT.
      assert (Hnpnq : np <> nq).
      { intro Heq; subst nq; rewrite HdeltaP in HdeltaQ; inversion HdeltaQ; congruence. }
      assert (HkeyP : In p (map fst (elems participant ltt delta0))).
      { apply in_map_iff; exists (p, Tp); split; [reflexivity|eapply nth_error_In; exact HdeltaP]. }
      assert (HkeyQ : In q (map fst (elems participant ltt delta0))).
      { apply in_map_iff; exists (q, Tq); split; [reflexivity|eapply nth_error_In; exact HdeltaQ]. }
      pose proof (partition_component_included qcontext0 lqc np qcP Hpart HqcP)
        as HincludeP.
      set (qcP' := delete (KEQ:=qr_dec) qcP v).
      set (qcQ' := insert (KEQ:=qr_dec) qcQ v tt).
      set (lqc2 := updn (updn lqc np qcP') nq qcQ').
      set (delta2 := insert (insert delta0 p Tsend) q Trecv).
      set (Mnew := insert (insert M0 q
        (subst_expression_in_process 0 0 (Val (QVal v)) Q)) p P).
      assert (Hdelta2 : delta2 = insert (insert delta0 p Tsend) q Trecv)
        by reflexivity.
      assert (HdeltaP2 : nth_error (elems participant ltt delta2) np = Some (p, Tsend)).
      { unfold delta2; eapply nth_error_delta_insert_other.
        - congruence.
        - eapply nth_error_delta_insert_at; exact HdeltaP. }
      assert (HdeltaQ2 : nth_error (elems participant ltt delta2) nq = Some (q, Trecv)).
      { unfold delta2; eapply nth_error_delta_insert_at.
        eapply nth_error_delta_insert_other; [congruence|exact HdeltaQ]. }
      assert (HqcQnone : qcQ v = None).
      { unfold FMap.partition in Hpart; destruct Hpart as [_ Hdisjoint].
        specialize (Hdisjoint np nq qcP qcQ Hnpnq HqcP HqcQ v) as [Hpnq _].
        apply Hpnq; rewrite HownerP; discriminate. }
      assert (Hpart2 : FMap.partition qubit_reference unit qcontext0 lqc2).
      { unfold lqc2, qcP', qcQ'; eapply partition_transfer_qubit; eauto. }
      assert (Hlength2 : Datatypes.length lqc2 =
        Datatypes.length (elems participant ltt delta2)).
      { unfold lqc2; repeat rewrite updn_length.
        unfold delta2; rewrite delta_insert_pair_length; try assumption. }
      assert (HqcP2 : nth_error lqc2 np = Some qcP').
      { unfold lqc2; rewrite nth_error_updn_neq by (symmetry; exact Hnpnq).
        rewrite nth_error_updn_eq; [reflexivity|].
        eapply nth_error_length; exact HqcP. }
      assert (HqcQ2 : nth_error lqc2 nq = Some qcQ').
      { unfold lqc2; rewrite nth_error_updn_eq.
        - reflexivity.
        - rewrite updn_length; eapply nth_error_length; exact HqcQ. }
      assert (HqcOther : forall k, k <> np -> k <> nq -> nth_error lqc2 k = nth_error lqc k).
      { intros k HnP HnQ; unfold lqc2.
        rewrite nth_error_updn_neq by (symmetry; exact HnQ).
        apply nth_error_updn_neq; symmetry; exact HnP. }
      assert (Hctx : ctx_step_f delta0 p q l0 header.Qubit delta2).
      { unfold delta2; eapply step_sr.
        - exact H2.
        - rewrite HshapeP in HdeltaPmap; exact HdeltaPmap.
        - rewrite HshapeQ in HdeltaQmap; exact HdeltaQmap.
        - exact HbranchP.
        - exact HbranchQ.
        intros pt; destruct (participant_dec pt p) as [->|Hp].
        - rewrite insert_neq by (symmetry; exact H2).
          rewrite insert_eq; reflexivity.
        - destruct (participant_dec pt q) as [->|Hq].
          + rewrite insert_eq; reflexivity.
          + rewrite insert_neq by (symmetry; exact Hq).
            rewrite insert_neq by (symmetry; exact Hp); reflexivity. }
      destruct (assoc_on_for_ctx_step G0 delta0 delta2 p q l0 header.Qubit
        Hreg Hbal Hassoc Hctx) as [G2 [Hassoc2 [Hgstep Hbal2]]].
      assert (Hreg2 : regGtt G2).
      { eapply regGtt_after_step with (G:=G0) (G':=G2) (p:=p) (q:=q) (l:=l0).
        - exact Hreg.
        - exact Hbal.
        - exact Hgstep. }
      assert (HsessionPerm : Permutation (session_participants M0)
        (session_participants Mnew)).
      {
        assert (HinQpair : In (q, p_recv p lQ) (elems participant process M0)).
        { apply (proj2 ((proj2 (specs _ _ M0)) q (p_recv p lQ))); exact H1. }
        pose proof (session_participants_insert_In M0 q (p_recv p lQ)
          (subst_expression_in_process 0 0 (Val (QVal v)) Q) HinQpair) as HpartQ.
        assert (HmidP : insert M0 q (subst_expression_in_process 0 0 (Val (QVal v)) Q) p =
          Some (p_send q l0 e P)).
        { rewrite insert_neq by (symmetry; exact H2); exact H. }
        assert (HinMidP : In (p, p_send q l0 e P)
          (elems participant process
            (insert M0 q (subst_expression_in_process 0 0 (Val (QVal v)) Q)))).
        { apply (proj2 ((proj2 (specs _ _
            (insert M0 q (subst_expression_in_process 0 0 (Val (QVal v)) Q))))
            p (p_send q l0 e P))); exact HmidP. }
        pose proof (session_participants_insert_In
          (insert M0 q (subst_expression_in_process 0 0 (Val (QVal v)) Q)) p
          (p_send q l0 e P) P HinMidP) as HpartP.
        unfold Mnew; eapply Permutation_trans.
        - exact (Permutation_sym HpartQ).
        - exact (Permutation_sym HpartP).
      }
      assert (Hperm2 : Permutation (map fst (elems participant ltt delta2))
        (session_participants Mnew)).
      { unfold delta2; eapply Permutation_trans.
        - apply delta_insert_pair_permutation; assumption.
        - eapply Permutation_trans; [exact Hperm|exact HsessionPerm]. }
      assert (HlookupP : Mnew p = Some P).
      { unfold Mnew; rewrite insert_eq; reflexivity. }
      assert (HlookupQ : Mnew q = Some
        (subst_expression_in_process 0 0 (Val (QVal v)) Q)).
      { unfold Mnew; rewrite insert_neq by exact H2; rewrite insert_eq; reflexivity. }
      assert (HlookupOther : forall pt, pt <> p -> pt <> q -> Mnew pt = M0 pt).
      { intros pt Hp Hq; unfold Mnew; rewrite insert_neq by (symmetry; exact Hp);
        rewrite insert_neq by (symmetry; exact Hq); reflexivity. }
      pose proof (subst_expression_in_process_quantum Q v 0 Tbranch nil nil qcQ
        HqcQnone HbranchProc) as HrecvSub.
      assert (HrecvPost : typecheck_process (nil, nil, qcQ')
        (subst_expression_in_process 0 0 (Val (QVal v)) Q) Trecv).
      { eapply T_sub with (T:=Tbranch); [exact HrecvSub|exact HsubBranch]. }
      assert (HsenderPost : typecheck_process (nil, nil, qcP') P Tsend).
      { eapply T_sub with (T:=Ts); [exact HcontP|exact HsubSendCont]. }
      assert (HtypedNew : typecheck_session qcontext0
        Mnew delta2 G2).
      { eapply typecheck_session_after_comm_update with
          (lqc:=lqc) (np:=np) (nq:=nq) (Tp:=Tp) (Tq:=Tq)
          (Tp':=Tsend) (Tq':=Trecv) (qcP:=qcP) (qcQ:=qcQ)
          (qcP':=qcP') (qcQ':=qcQ') (lqc2:=lqc2) (P':=P)
          (Q':=subst_expression_in_process 0 0 (Val (QVal v)) Q); eauto. }
      exists qcP, delta2, G2, e, header.Qubit.
      split.
      { exists p, n, Hlookup; reflexivity. }
      split; [exact HincludeP|].
      split; [exact Hctx|].
      split; [exact Hgstep|].
      split; [exact HevalOrig|].
      split; [exact HexprOrig|].
      exact HtypedNew.
    - (* Unfolding congruence. *)
      pose proof (typecheck_session_unfoldM delta0 G0 qcontext0 M0 M1' H H7)
        as HtypedM1.
      pose proof (H2 M1' M3 qstate0 qstate1 delta0 G0 p0 q0 l0 v0
        qcontext0 eq_refl eq_refl eq_refl H1 HtypedM1) as Hresult.
      destruct Hresult as
        [qcontext2 [delta2 [G2 [e [S [Hstate [Hinclude [Hctx
        [Hgstep [Heval [Hexpr HtypedM3]]]]]]]]]]].
      exists qcontext2, delta2, G2, e, S.
      split; [exact Hstate|].
      split; [exact Hinclude|].
      split; [exact Hctx|].
      split; [exact Hgstep|].
      split; [exact Heval|].
      split; [exact Hexpr|].
      exact HtypedM3.
Qed.
