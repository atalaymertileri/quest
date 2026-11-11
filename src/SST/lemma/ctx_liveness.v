From mathcomp Require Import ssreflect.seq all_ssreflect.
Require Import List String Coq.Arith.PeanoNat Coq.Arith.Arith Relations ZArith Datatypes Setoid Morphisms Coq.Logic.Decidable Coq.Program.Basics Coq.Init.Datatypes FMap.
Import ListNotations. 
Open Scope list_scope.
From Paco Require Import paco.
Require Import SST.
Require Import session substitution balanced.

(* Context-level liveness development.
   Main goal: derive progress/liveness properties of typing contexts
   from associated global reductions under merge assumptions. *)

Lemma assoc_step_s_f_r : forall Gl p1 q q1 l1 s1 Gl',
      ctx_step_s Gl p1 q -> 
      ctx_step_f Gl p1 q1 l1 s1 Gl' -> 
      q = q1.
Proof.
  intros.
  inversion H. subst. inversion H0. subst. clear H H0.
  rewrite H4 in H1. 
  invert_all_some. easy.
Qed.

Lemma assoc_step_sl_f_r : forall Gl p1 q q1 l s l1 s1 Gl',
      ctx_step_sl Gl p1 q l s -> 
      ctx_step_f Gl p1 q1 l1 s1 Gl' -> 
      q = q1.
Proof.
  intros.
  inversion H. subst. inversion H0. subst. clear H H0.
  rewrite H4 in H1. 
  invert_all_some. easy.
Qed.


Lemma assoc_step_r_f_r : forall Gl p1 p q1 l1 s1 Gl',
      ctx_step_r Gl q1 p -> 
      ctx_step_f Gl p1 q1 l1 s1 Gl' -> 
      p = p1.
Proof.
  intros.
  inversion H. subst. inversion H0. subst. clear H H0.
  rewrite H5 in H1. 
  invert_all_some. easy.
Qed.  

Lemma assoc_step_s_f_r_op : forall Gl p q p1 q1 l1 s1 Gl',
            ctx_step_s Gl p q ->
            ctx_step_f Gl p1 q1 l1 s1 Gl' -> 
            p <> q1.
Proof.
  intros.
  inversion H. subst. 
  inversion H0. subst. 
  clear H H0.
  specialize(participant_dec p q1); intros.
  destruct H; try easy. subst.
  rewrite H5 in H1. 
  invert_all_some.
Qed.

Lemma assoc_step_r_f_r_op : forall Gl p q p1 q1 l1 s1 Gl',
            ctx_step_r Gl q p ->
            ctx_step_f Gl p1 q1 l1 s1 Gl' -> 
            q <> p1.
Proof.
  intros.
  inversion H. subst. 
  inversion H0. subst. 
  clear H H0.
  specialize(participant_dec q p1); intros.
  destruct H; try easy. subst.
  rewrite H4 in H1. 
  invert_all_some.
Qed.

Section comp_sound_ctx.

(* Soundness bridge: association with a balanced/regular global type
   implies progress properties for context steps. *)

Lemma assoc_projA `{good_merge} : forall G Gl, regGtt G -> balancedG G -> assoc_gctx Gl G -> projectableA G.
Proof.
  intros.
  inversion H2. 
  unfold projectableA. intros.
  specialize(H3 pt). specialize(H4 pt).
  specialize(always_exists (Gl pt)); intros. destruct H5. 
  destruct x.
  - specialize(H4 l H5).
    destruct H4. exists x. easy.
  - clear H4.
    specialize(dec_isgPartsC G pt H0); intros. rewrite H5 in H3.
    destruct H4.
    - specialize(H3 H4). destruct H3. easy.
    - exists ltt_end.
      pfold. constructor. easy.
Qed.

Lemma assoc_on `{good_merge} : forall G (Gl: typ_ctx) Gl' p q l s, regGtt G -> balancedG G -> assoc_gctx Gl G -> ctx_step_f Gl p q l s Gl' -> exists G', assoc_gctx Gl' G' /\ gttstepC G G' p q l /\ balancedG G'.
Proof.
  intros.
  specialize(assoc_projA G Gl H0 H1 H2). intro Ht.
  inversion H3. subst. clear H3.
  inversion H2. clear H2.
  specialize(proj_to_step G p q l); intros.
  pose proof H10 as Ha. pose proof Ha as Hta. 
  specialize(Ha p (ltt_send q xs) H5).
  specialize(H10 q (ltt_recv p ys) H6).
  destruct H10 as (Ta,(Hb,Hc)). destruct Ha as (Tb,(Hd,He)).
  pinversion Hc. subst. pinversion He. subst. clear Hc He.
  pose proof H3 as Hparts_before.
  pose proof Hta as Hassoc_before.
  specialize(H14 l). rewrite H7 in H14.
  destruct H14 as [Hsend_none | (send_sort,(send_src,(send_cont,(Hsend_src,(Hsend_cont,Hsend_sub)))))].
  - discriminate.
  - inversion Hsend_src; subst send_sort send_src. clear Hsend_src.
    (* Balanced projections give the receiver branch matching the send branch. *)
    pose proof (proj_sort G p q ys1 ys0 H1 Hd Hb) as Hsort.
    specialize(Hsort l).
    destruct Hsort as [[Hsort_send_none Hsort_recv_none]
      | (sort,(send_tail,(recv_tail,(Hsort_send,Hsort_recv))))].
    + rewrite Hsend_cont in Hsort_send_none. discriminate.
    + rewrite Hsend_cont in Hsort_send. inversion Hsort_send; subst sort send_tail.
      specialize(H13 l). rewrite H8 in H13.
      destruct H13 as [Hrecv_none | (recv_sort,(recv_src,(recv_cont,(Hrecv_src,(Hrecv_cont,Hrecv_sub)))))].
      * rewrite Hsort_recv in Hrecv_none. discriminate.
      * inversion Hrecv_src; subst recv_sort recv_src. clear Hrecv_src.
        rewrite Hsort_recv in Hrecv_cont. inversion Hrecv_cont; subst recv_cont. clear Hrecv_cont.
      assert(exists G' : gtt, gttstepC G G' p q l) as Hglobal.
      {
        apply (H2 ys1 ys0 (s, send_cont)); try easy.
      }
      destruct Hglobal as (G',Hstep).
      pose proof (balanced_step G G' p q l H1 H0 Hstep Ht) as Hbal_after.
      exists G'. split.
      * split.
        -- intros pt Hparts_after.
           pose proof (pt_step_back G G' p q l pt Hstep Hparts_after) as Hparts_before_pt.
           destruct (Hparts_before pt Hparts_before_pt) as (Tpt,Hctx_before).
           specialize(H9 pt).
           destruct (participant_dec pt p) as [Hptp|Hptp].
           ++ subst pt. simpl in H9. exists T. exact H9.
           ++ destruct (participant_dec pt q) as [Hptq|Hptq].
              ** subst pt. simpl in H9. exists T'. exact H9.
              ** exists Tpt. rewrite <- H9. exact Hctx_before.
        -- intros pt Tctx Hctx_after.
           destruct (participant_dec pt p) as [Hptp|Hptp].
           ++ subst pt.
              specialize(H9 p).
              destruct (participant_dec p p); [simpl in H9|contradiction].
              rewrite H9 in Hctx_after. inversion Hctx_after; subst Tctx.
              destruct (typ_after_step_p G G' p q l ys1 H1 H0 Hstep Hd)
                as (sp,(Tnext,(Hbranch,Hproj_after))).
              rewrite Hsend_cont in Hbranch. inversion Hbranch; subst sp Tnext.
              exists send_cont. split. exact Hproj_after.
              pclearbot. exact Hsend_sub.
           ++ destruct (participant_dec pt q) as [Hptq|Hptq].
              ** subst pt.
                 specialize(H9 q).
                 destruct (participant_dec q p) as [Hqp|Hqp].
                 --- exfalso. apply H4. symmetry. exact Hqp.
                 --- destruct (participant_dec q q); [simpl in H9|contradiction].
                 rewrite H9 in Hctx_after. inversion Hctx_after; subst Tctx.
                 destruct (typ_after_step_q G G' p q l ys0 H1 H0 Hstep Hb)
                   as (sp,(Tnext,(Hbranch,Hproj_after))).
                 rewrite Hsort_recv in Hbranch. inversion Hbranch; subst sp Tnext.
                 exists recv_tail. split. exact Hproj_after.
                 pclearbot. exact Hrecv_sub.
              ** specialize(H9 pt).
                 destruct (participant_dec pt p) as [Heq|Hneqptp].
                 --- exfalso. apply Hptp. exact Heq.
                 --- destruct (participant_dec pt q) as [Heq|Hneqptq].
                     +++ exfalso. apply Hptq. exact Heq.
                     +++ rewrite <- H9 in Hctx_after.
                 destruct (Hassoc_before pt Tctx Hctx_after) as (Told,(Hproj_before,Hsub_before)).
                 assert(p <> pt) as Hneqp by (intro Heq; apply Hptp; symmetry; exact Heq).
                 assert(q <> pt) as Hneqq by (intro Heq; apply Hptq; symmetry; exact Heq).
                 destruct (typ_after_step_r G G' p q pt l Told H1 H0 Hstep Hneqp Hneqq Hproj_before)
                   as (Tnext,(Hproj_after,Hsub_after)).
                 exists Tnext. split. exact Hproj_after.
                 eapply stTrans; eassumption.
      * split; assumption.
  all: apply sub_mon.
Qed.

Lemma assoc_back `{good_merge} : forall G Gl G' p q l, 
        regGtt G -> balancedG G -> assoc_gctx Gl G -> gttstepC G G' p q l -> 
        (forall pt T, Gl pt = Some T -> regLtt T) ->
        exists Gl' l' s' G'',
        ctx_step_f Gl p q l' s' Gl' /\ assoc_gctx Gl' G'' /\ gttstepC G G'' p q l' /\ balancedG G''.
Proof.
  intros.
  inversion H2. rename H2 into Hka.
  specialize(step_to_pt G G' p q l); intros. specialize(step_to_pt_r G G' p q l); intros.
  fill_triv. pose proof H5 as Ht.
  specialize(H5 p). specialize(Ht q). fill_triv. destruct_exists_and.
  pose proof H6 as Ht.
  specialize(H6 p x0). specialize(Ht q x). fill_triv. destruct_exists_and.
  specialize(H4 p x0). fill_triv.
  specialize(proj_shape_p G G' p q l x2); intros.
  specialize(proj_shape_q G G' p q l x1); intros. fill_triv.
  destruct_exists_and. subst.
  pinversion H11; try mon_easy. subst. pinversion H10; try mon_easy. subst.
  clear H10 H11.
  specialize(regLtt_some_cont_send q xs); intros. fill_triv. destruct_exists_and.
  rename x into l'.
  specialize(proj_sort G p q x4 x3); intros. fill_triv.
  specialize(H14 l'). specialize(H15 l'). specialize(H11 l').
  rewrite H10 in H14.
  destruct H14; try easy. destruct_exists_and. invert_all_some.
  rewrite H13 in H11. destruct H11; try easy. destruct_exists_and. invert_all_some.
  rewrite H12 in H15. destruct H15; try easy. destruct_exists_and. invert_all_some.
  pclearbot.
  exists (insert (insert Gl q x2) p x1). exists l'. exists x.
  specialize(proj_to_step G p q l' x4 x3 (x, x5)); intros. 
  assert(p <> q).
  {
    destruct (participant_dec p q) as [Heq|Hneq].
    - subst q. rewrite H5 in H8. invert_all_some.
    - exact Hneq.
  }
  fill_triv. destruct H15 as (G'',H15). exists G''.
  repeat(split; try easy).
  - eapply step_sr with (xs:=xs) (ys:=xs0) (T:=x1) (T':=x2) (B:=x); try easy.
    intros pt.
    destruct (participant_dec pt p) as [Heqp|Hptp].
    + subst pt. destruct (participant_dec p p) as [_|Hneq]; [cbn [is_left]; apply insert_eq|contradiction].
    + cbn [is_left]. destruct (participant_dec pt q) as [Heqq|Hptq].
      * subst pt. destruct (participant_dec q p) as [Heqp|Hneq].
        -- exfalso. apply H17. symmetry. exact Heqp.
        -- cbn [is_left]. rewrite insert_neq; try congruence. apply insert_eq.
      * cbn [is_left].
        rewrite (FMap.insert_neq participant ltt (insert Gl q x2) p pt x1 (nesym Hptp)).
        rewrite (FMap.insert_neq participant ltt Gl q pt x2 (nesym Hptq)). reflexivity.
  - intros pt Hparts_after.
    destruct (participant_dec pt p) as [Heqp|Hptp].
    + subst pt. exists x1. apply insert_eq.
    + destruct (participant_dec pt q) as [Heqq|Hptq].
      * subst pt. exists x2.
        rewrite (FMap.insert_neq participant ltt (insert Gl q x2) p q x1 H17). apply insert_eq.
      * pose proof (pt_step_back G G'' p q l' pt H15 Hparts_after) as Hparts_before.
        destruct (proj1 Hka pt Hparts_before) as [T HT].
        exists T.
        rewrite (FMap.insert_neq participant ltt (insert Gl q x2) p pt x1 (nesym Hptp)).
        rewrite (FMap.insert_neq participant ltt Gl q pt x2 (nesym Hptq)). exact HT.
  - intros pt T Hctx_after.
    destruct (participant_dec pt p) as [Heqp|Hptp].
    + subst pt. rewrite insert_eq in Hctx_after. inversion Hctx_after; subst T.
      destruct (typ_after_step_p G G'' p q l' x4 H1 H0 H15 H6)
        as (s,(Tnext,(Hbranch,Hproj_after))).
      rewrite H13 in Hbranch. inversion Hbranch; subst s Tnext.
      exists x5. split; [exact Hproj_after|exact H14].
    + destruct (participant_dec pt q) as [Heqq|Hptq].
      * subst pt. rewrite (FMap.insert_neq participant ltt (insert Gl q x2) p q x1 H17) in Hctx_after.
        rewrite insert_eq in Hctx_after. inversion Hctx_after; subst T.
        destruct (typ_after_step_q G G'' p q l' x3 H1 H0 H15 H9)
          as (s,(Tnext,(Hbranch,Hproj_after))).
        rewrite H12 in Hbranch. inversion Hbranch; subst s Tnext.
        exists x7. split; [exact Hproj_after|exact H16].
      * rewrite (FMap.insert_neq participant ltt (insert Gl q x2) p pt x1 (nesym Hptp)) in Hctx_after.
        rewrite (FMap.insert_neq participant ltt Gl q pt x2 (nesym Hptq)) in Hctx_after.
        destruct (proj2 Hka pt T Hctx_after) as (Tbefore,(Hproj_before,Hsub_before)).
        assert (p <> pt) as Hneqp by congruence.
        assert (q <> pt) as Hneqq by congruence.
        destruct (typ_after_step_r G G'' p q pt l' Tbefore H1 H0 H15
          Hneqp Hneqq Hproj_before) as (Tnext,(Hproj_after,Hsub_after)).
        exists Tnext. split; [exact Hproj_after|].
        eapply stTrans; eassumption.
  - eapply balanced_step; try eassumption.
    eapply assoc_projA; eassumption.
Qed.

Lemma is_assoc_forward `{good_merge} : forall gtx gtx', 
      is_assoc gtx ->  
      multi typ_ctx_red gtx gtx' -> 
      is_assoc gtx'.
Proof.
  intros. revert H0.
  induction H1; intros; try easy.
  apply IHmulti. clear IHmulti H1. inversion H0; subst. inversion H2; subst.
  destruct_exists_and.
  specialize(assoc_on x0 x y p q l B); intros. fill_triv.
  destruct_exists_and.
  exists x1. 
  specialize(regGtt_after_step x0 H4 H5 x1 p q l); intros. fill_triv; try easy.
Qed.


End comp_sound_ctx.

Lemma part_on_ctx_step_s `{good_merge} : forall Gl p q G,
      ctx_step_s Gl p q -> 
      assoc_gctx Gl G -> 
        isgPartsC p G.
Proof.
  intros.
  inversion H0. subst. clear H0.
  unfold assoc_gctx in H1. destruct H1 as (Ha, Hb).
  specialize(Hb p (ltt_send q xs) H2).
  destruct Hb as (T',(Hc,Hd)).
  pinversion Hd; try easy. subst.
  pinversion Hc; try easy.
  apply proj_mon. apply sub_mon.
Qed.

Lemma part_on_ctx_step_sl `{good_merge} : forall Gl p q l s G,
      ctx_step_sl Gl p q l s -> 
      assoc_gctx Gl G -> 
        isgPartsC p G.
Proof.
  intros.
  inversion H0. subst. clear H0.
  unfold assoc_gctx in H1. destruct H1 as (Ha, Hb).
  specialize(Hb p (ltt_send q xs) H2).
  destruct Hb as (T',(Hc,Hd)).
  pinversion Hd; try easy. subst.
  pinversion Hc; try easy.
  apply proj_mon. apply sub_mon.
Qed.


Lemma part_on_ctx_step_r `{good_merge} : forall Gl p q G,
      ctx_step_r Gl q p -> 
      assoc_gctx Gl G -> 
        isgPartsC q G.
Proof.
  intros.
  inversion H0. subst. clear H0.
  unfold assoc_gctx in H1. destruct H1 as (Ha, Hb).
  specialize(Hb q (ltt_recv p xs) H2).
  destruct Hb as (T',(Hc,Hd)).
  pinversion Hd; try easy; try mon_easy. subst.
  pinversion Hc; try easy; try mon_easy.
Qed.

Lemma assoc_step_s_sl_r `{good_merge} : forall gtx s s0 o q l sb,
          assoc_gctx gtx (gtt_send s s0 o) -> 
          ctx_step_sl gtx s q l sb -> 
          q = s0.
Proof.
  intros.
  inversion H0. inversion H1. subst. pose proof H3 as Ht.
  specialize(H3 s (ltt_send q xs)). fill_triv. destruct_exists_and.
  pinversion H3; subst; try mon_easy; try easy.
  - assert False. apply H7. constructor.
    easy.
  - specialize(H2 s0). 
    assert(exists T : ltt, gtx s0 = Some T). apply H2. constructor.
    destruct_exists_and.
    specialize(Ht s0 x). fill_triv. destruct_exists_and.
    pinversion H8; subst; try easy; try mon_easy.
    - assert False. 
      apply H12. constructor. easy.
      pinversion H6; try mon_easy.
Qed.

Lemma assoc_step_s_r_r `{good_merge} : forall gtx s s0 o q,
          assoc_gctx gtx (gtt_send s s0 o) -> 
          ctx_step_r gtx s0 q -> 
          q = s.
Proof.
  intros.
  inversion H0. inversion H1. subst. pose proof H3 as Ht.
  specialize(H3 s0 (ltt_recv q xs)). fill_triv. destruct_exists_and.
  pinversion H3; subst; try mon_easy; try easy.
  - assert False. apply H7. constructor.
    easy.
  - specialize(H2 s). 
    assert(exists T : ltt, gtx s = Some T). apply H2. constructor.
    destruct_exists_and.
    specialize(Ht s x). fill_triv. destruct_exists_and.
    pinversion H8; subst; try easy; try mon_easy.
    - assert False. 
      apply H12. constructor. easy.
      pinversion H6; try mon_easy.
Qed.


Lemma assoc_step_sl_op `{good_merge} : forall Gl p q l s s0 o sb,
      ctx_step_sl Gl p q l sb -> 
      assoc_gctx Gl (gtt_send s s0 o) ->
      p <> s0.
Proof.  
  intros.
  inversion H0. subst. 
  inversion H1.
  specialize(H5 p (ltt_send q xs) H2).
  destruct H5 as (T', (Ha,Hb)).
  specialize(participant_dec p s0); intros. destruct H5; try easy. subst.
  pinversion Ha; try easy; try mon_easy.
  - subst. 
    assert False. apply H5. constructor. easy.
  - subst.
    pinversion Hb; try mon_easy.
Qed.

Lemma assoc_step_s_op `{good_merge} : forall Gl p q s s0 o,
      ctx_step_s Gl p q -> 
      assoc_gctx Gl (gtt_send s s0 o) ->
      p <> s0.
Proof.  
  intros.
  inversion H0. subst. 
  inversion H1.
  specialize(H5 p (ltt_send q xs) H2).
  destruct H5 as (T', (Ha,Hb)).
  specialize(participant_dec p s0); intros. destruct H5; try easy. subst.
  pinversion Ha; try easy; try mon_easy.
  - subst. 
    assert False. apply H5. constructor. easy.
  - subst.
    pinversion Hb; try mon_easy.
Qed.


Lemma assoc_step_r_op `{good_merge} : forall Gl p q s s0 o,
      ctx_step_r Gl q p -> 
      assoc_gctx Gl (gtt_send s s0 o) ->
      q <> s.
Proof.  
  intros.
  inversion H0. subst. 
  inversion H1.
  specialize(H5 q (ltt_recv p xs) H2).
  destruct H5 as (T', (Ha,Hb)).
  specialize(participant_dec q s); intros. destruct H5; try easy. subst.
  pinversion Ha; try easy; try mon_easy.
  - subst. 
    assert False. apply H5. constructor. easy.
  - subst.
    pinversion Hb; try mon_easy.
Qed.



Lemma P_after_step : forall gtx gtx', multi typ_ctx_red gtx gtx' -> (forall pt T, gtx pt = Some T -> regLtt T) -> (forall pt T, gtx' pt = Some T -> regLtt T).
Proof.
  intros gtx gtx' Hmulti.
  induction Hmulti as [G | G Gmid G' Hred Htail IH]; intros Hreg pt T Hlookup.
  - apply Hreg with pt. exact Hlookup.
  - assert (Hregmid : forall r U, Gmid r = Some U -> regLtt U).
    {
      intros r U Hmid.
      inversion Hred as [G0 G1 p q l B Hctx]; subst.
      inversion Hctx as [G2 G3 p0 q0 l0 xs ys Tsend Trecv B0 Hneq Hsend Hrecv Hsend_step Hrecv_step Hupdate]; subst.
      assert (Hreg_send : regLtt (ltt_send q xs)).
      { apply Hreg with p. exact Hsend. }
      assert (Hreg_recv : regLtt (ltt_recv p ys)).
      { apply Hreg with q. exact Hrecv. }
      specialize (Hupdate r).
      destruct (participant_dec r p) as [Hrp|Hrp].
      + subst r.
        destruct (participant_dec p p) as [_|Hfalse]; [simpl in Hupdate|contradiction].
        rewrite Hupdate in Hmid. inversion Hmid; subst U.
        pose proof (regLtt_cont q xs Hreg_send l) as Hcont.
        rewrite Hsend_step in Hcont.
        destruct Hcont as [Hnone|[s [T0 [Hbranch HregT0]]]].
        * discriminate.
        * inversion Hbranch; subst. exact HregT0.
      + destruct (participant_dec r q) as [Hrq|Hrq].
        * subst r.
          destruct (participant_dec q p) as [Hqp|Hqp].
          -- exfalso. apply Hneq. symmetry. exact Hqp.
          -- destruct (participant_dec q q) as [_|Hfalse]; [simpl in Hupdate|contradiction].
             rewrite Hupdate in Hmid. inversion Hmid; subst U.
             pose proof (regLtt_cont_r p ys Hreg_recv l) as Hcont.
             rewrite Hrecv_step in Hcont.
             destruct Hcont as [Hnone|[s [T0 [Hbranch HregT0]]]].
             ++ discriminate.
             ++ inversion Hbranch; subst. exact HregT0.
        * simpl in Hupdate.
          apply Hreg with r.
          rewrite Hupdate. exact Hmid.
    }
    exact (IH Hregmid pt T Hlookup).
Qed.

Lemma ctx_step_sl_preserved_by_other_step : forall G G' p q l B s r l' B',
    ctx_step_sl G p q l B -> ctx_step_f G s r l' B' G' ->
    p <> s -> p <> r -> ctx_step_sl G' p q l B.
Proof.
  intros G G' p q l B s r l' B' Hsl Hf Hps Hpr.
  inversion Hsl as [G0 p0 q0 xs0 l0 B0 T0 Hlookup Hbranch]; subst.
  inversion Hf as [G1 G1' s0 r0 l1 xs1 ys1 T1 T1' B1 Hsr Hsend Hrecv Hxs Hys Hupdate]; subst.
  assert (G' p = G p) as Hsame.
  {
    specialize (Hupdate p).
    destruct (participant_dec p s) as [Heq|Hneq].
    - exfalso. apply Hps. exact Heq.
    - destruct (participant_dec p r) as [Heq|Hneq'].
      + exfalso. apply Hpr. exact Heq.
      + symmetry. exact Hupdate.
  }
  econstructor; [rewrite Hsame; exact Hlookup|exact Hbranch].
Qed.

Lemma ctx_step_s_preserved_by_other_step : forall G G' p q s r l' B',
    ctx_step_s G p q -> ctx_step_f G s r l' B' G' ->
    p <> s -> p <> r -> ctx_step_s G' p q.
Proof.
  intros G G' p q s r l' B' Hs Hf Hps Hpr.
  inversion Hs as [G0 p0 q0 xs0 l0 st Hlookup Hbranch]; subst.
  inversion Hf as [G1 G1' s0 r0 l1 xs1 ys1 T1 T1' B1 Hsr Hsend Hrecv Hxs Hys Hupdate]; subst.
  assert (G' p = G p) as Hsame.
  {
    specialize (Hupdate p).
    destruct (participant_dec p s) as [Heq|Hneq].
    - exfalso. apply Hps. exact Heq.
    - destruct (participant_dec p r) as [Heq|Hneq'].
      + exfalso. apply Hpr. exact Heq.
      + symmetry. exact Hupdate.
  }
  econstructor; [rewrite Hsame; exact Hlookup|exact Hbranch].
Qed.

Lemma ctx_step_r_preserved_by_other_step : forall G G' p q s r l' B',
    ctx_step_r G p q -> ctx_step_f G s r l' B' G' ->
    p <> s -> p <> r -> ctx_step_r G' p q.
Proof.
  intros G G' p q s r l' B' Hr Hf Hps Hpr.
  inversion Hr as [G0 p0 q0 xs0 l0 st0 Hlookup Hbranch]; subst.
  inversion Hf as [G1 G1' s0 r0 l1 xs1 ys1 T1 T1' B1 Hsr Hsend Hrecv Hxs Hys Hupdate]; subst.
  assert (G' p = G p) as Hsame.
  {
    specialize (Hupdate p).
    destruct (participant_dec p s) as [Heq|Hneq].
    - exfalso. apply Hps. exact Heq.
    - destruct (participant_dec p r) as [Heq|Hneq'].
      + exfalso. apply Hpr. exact Heq.
      + symmetry. exact Hupdate.
  }
  econstructor; [rewrite Hsame; exact Hlookup|exact Hbranch].
Qed.

Section ctx_sf_df.

(* Safety and deadlock-freedom transfer from global assumptions to contexts. *)

  Variable gtx : typ_ctx.
  Hypothesis P : forall pt T, gtx pt = Some T -> regLtt T.
  
  
  
  Lemma live_is_df : live_ctx gtx -> df_ctx gtx.
  Proof.
    intros. unfold live_ctx in H. unfold df_ctx.
    intros.
    specialize(H gtx' H0).
    specialize(P_after_step gtx gtx' H0 P); intros. clear H0 P. clear gtx. rename gtx' into gtx.
    destruct H.
    unfold is_end in *. intros.
    destruct (gtx pt) eqn:Ha.
    - right. 
      destruct l as [|s o|s o]; try easy.
      - specialize(H2 pt (ltt_recv s o)). fill_triv.
        specialize(regLtt_some_cont_recv s o); intros. fill_triv. destruct_exists_and.
        assert(ctx_step_r gtx pt s).
        {
          apply step_r with o x x0; try easy.
        }
        specialize(H0 s pt). fill_triv. destruct_exists_and. 
        clear H H2 Ha H3 H4. assert False.
        clear x0 x o. revert H1 H5.
        induction H0 as [G | G Gmid Gend Hfirst Htail IH]; intros.
        - eapply H1. eapply step_on_f. exact H5.
        - eapply H1. exact Hfirst.
        easy.
      - specialize(H2 pt (ltt_send s o)). fill_triv.
        specialize(regLtt_some_cont_send s o); intros. fill_triv. destruct_exists_and.
        destruct x0 as [B0 T0].
        assert(ctx_step_sl gtx pt s x B0).
        {
          apply step_sl with o T0; try easy.
        }
        specialize(H pt s x B0). fill_triv. destruct_exists_and. 
        clear H0 H2 Ha H3 H4. assert False.
        revert H1 H5.
        induction H as [G | G Gmid Gend Hfirst Htail IH]; intros.
        - eapply H1. eapply step_on_f. exact H5.
        - eapply H1. exact Hfirst.
        easy.
    - left. easy.
  Qed.
  
  
  Context `{good_merge}.
  Hypothesis P_ass : is_assoc gtx.
  
  Lemma assoc_is_safe : safe_ctx gtx.
  Proof.
    unfold safe_ctx. intros.
    (* reduce to the case gtx' = gtx *)
    specialize(is_assoc_forward gtx gtx'); intros. fill_triv.
    specialize(P_after_step gtx'); intros. fill_triv. clear P H0 P_ass.
    clear gtx. rename gtx' into gtx.
  
    (* clean shape based on hyp *)
    inversion H1; subst; clear H1. inversion H2; subst; clear H2.
    inversion H3; subst; clear H3. rename x into G. destruct_exists_and.
    inversion H2.
    clear H6 st l0.
    pose proof H9 as Ht.
    specialize(H9 p (ltt_send q xs)). specialize(Ht q (ltt_recv p xs0)).
    fill_triv. destruct_exists_and. 
    pinversion H11; try mon_easy; subst. pinversion H10; try mon_easy; subst.
    clear H10 H11.
    specialize(proj_sort G p q ys ys0); intros. fill_triv.
    specialize(H15 l). specialize(H16 l). specialize(H10 l).
    destruct H15 as [Hxs_none|[s1 [T1 [T1' [Hxs [Hys Hsub_send]]]]]].
    - rewrite H5 in Hxs_none. discriminate.
    - rewrite H5 in Hxs. inversion Hxs; subst s1 T1.
      destruct H10 as [[Hys_none Hys0_none]|[s2 [T2 [T2' [Hys2 Hys0]]]]].
      + rewrite Hys in Hys_none. discriminate.
      + rewrite Hys in Hys2. inversion Hys2; subst s2 T2.
        destruct H16 as [Hys0_none|[s3 [T3 [T3' [Hxs0 [Hys0' Hsub_recv]]]]]].
        * rewrite Hys0 in Hys0_none. discriminate.
        * rewrite Hys0 in Hys0'. inversion Hys0'; subst s3 T3'.
          assert (Hneq : p <> q).
          { intro Heq. subst q. rewrite H0 in H1. discriminate. }
          exists (insert (insert gtx q T3) p T).
          eapply step_sr with (xs:=xs) (ys:=xs0) (T:=T) (T':=T3) (B:=B); try assumption.
          intros pt.
          destruct (participant_dec pt p) as [Heqp|Hptp].
          -- subst pt. destruct (participant_dec p p) as [_|Hfalse];
             [cbn [is_left]; apply insert_eq|contradiction].
          -- cbn [is_left]. destruct (participant_dec pt q) as [Heqq|Hptq].
             ++ subst pt. destruct (participant_dec q p) as [Heqp|Hqnp].
                ** exfalso. apply Hneq. symmetry. exact Heqp.
                ** cbn [is_left]. rewrite insert_neq; try congruence. apply insert_eq.
             ++ cbn [is_left].
                rewrite (FMap.insert_neq participant ltt (insert gtx q T3) p pt T (nesym Hptp)).
                rewrite (FMap.insert_neq participant ltt gtx q pt T3 (nesym Hptq)).
                reflexivity.
  Qed.
  
  

  Lemma assoc_step_sl_to_step_f : forall p q l xs Gl B,
        assoc_gctx Gl (gtt_send p q xs) -> 
        ctx_step_sl Gl p q l B ->
        exists Gl', ctx_step_f Gl p q l B Gl'.
  Proof.
    intros.
    unfold assoc_gctx in H0. destruct H0 as (Ha, Hb).
    pose proof Ha as Hc.
    pose proof Hb as Hd.
    specialize(Ha p). specialize(Hc q).
    assert(exists T : ltt, Gl p = Some T). apply Ha. constructor.
    assert(exists T : ltt, Gl q = Some T). apply Hc. constructor.
    clear Ha Hc.
    destruct H0 as (T,Ha). destruct H2 as (T',Hc).
    specialize(Hb p T Ha). destruct Hb as (T1,(Hb,He)). 
    specialize(Hd q T' Hc). destruct Hd as (T2,(Hd,Hf)).
    pinversion Hb; try easy.
    - subst. assert False. apply H0. constructor. easy.
    subst. clear H5 H7 Hb.
    pinversion Hd; try easy.
    - subst. assert False. apply H0. constructor. easy.
    subst. clear H6 H9 H5.
    pinversion Hf. subst. pinversion He. subst. clear He Hf.
    inversion H1. subst. rewrite H0 in Ha. inversion Ha. subst. clear Ha.
    specialize(H8 l). specialize(H10 l). specialize(H3 l). specialize(H5 l).
    rewrite H2 in H5.
    destruct H5 as [Hsend_none|[s1 [T1 [T1' [Hlocal_send [Hproj_send Hsub_send]]]]]].
    - discriminate.
    - inversion Hlocal_send; subst s1 T1.
      destruct H8 as [[Hglobal_none Hprojected_none]|[s2 [g2 [T2 [Hglobal_send [Hprojected_send Hprojection_send]]]]]].
      + rewrite Hproj_send in Hprojected_none. discriminate.
      + rewrite Hproj_send in Hprojected_send. inversion Hprojected_send; subst s2 T2.
        destruct H10 as [[Hglobal_recv_none Hprojected_recv_none]|[s3 [g3 [T3 [Hglobal_recv [Hprojected_recv Hprojection_recv]]]]]].
        * rewrite Hglobal_send in Hglobal_recv_none. discriminate.
        * rewrite Hglobal_send in Hglobal_recv. inversion Hglobal_recv; subst s3 g3.
          destruct H3 as [Hrecv_none|[s4 [T4 [T4' [Hlocal_recv [Hprojected_recv' Hsub_recv]]]]]].
          -- rewrite Hprojected_recv in Hrecv_none. discriminate.
          -- rewrite Hprojected_recv in Hprojected_recv'. inversion Hprojected_recv'; subst s4 T4'.
             exists (insert (insert Gl q T4) p T).
             eapply step_sr with (xs:=xs1) (ys:=xs0) (T:=T) (T':=T4) (B:=B); try assumption.
             intros pt.
             destruct (participant_dec pt p) as [Heqp|Hptp].
             ++ subst pt. destruct (participant_dec p p) as [_|Hfalse];
                [cbn [is_left]; apply insert_eq|contradiction].
             ++ cbn [is_left]. destruct (participant_dec pt q) as [Heqq|Hptq].
                ** subst pt. destruct (participant_dec q p) as [Heqp|Hqnp].
                   --- exfalso. apply H4. symmetry. exact Heqp.
                   --- cbn [is_left]. rewrite insert_neq; try congruence. apply insert_eq.
                ** cbn [is_left].
                   rewrite (FMap.insert_neq participant ltt (insert Gl q T4) p pt T (nesym Hptp)).
                   rewrite (FMap.insert_neq participant ltt Gl q pt T4 (nesym Hptq)).
                   reflexivity.
    all: try apply sub_mon; try apply proj_mon.
  Qed.
  
  Lemma assoc_is_live : live_ctx gtx.
  Proof.
    unfold live_ctx. intros.
    (* reduce to the case gtx' = gtx *)
    specialize(is_assoc_forward gtx gtx'); intros. fill_triv.
    specialize(P_after_step gtx gtx' H0 P); intros. fill_triv. clear P H0 P_ass.
    clear gtx. rename gtx' into gtx.
    
    (* clean shape *)
    inversion H1. rename x into G. destruct_exists_and. clear H1.
    
    split.
    (* send case *)
    - intros.
      specialize(part_on_ctx_step_sl gtx p q l B G); intros. fill_triv.
      specialize(part_with_balanced_k p G); intros. fill_triv.
      destruct H6 as (k, Ha). clear H5.
      revert Ha H1 H4 H3 H0 H2. revert gtx G l p q.
      induction k; intros. rename H2 into Hta.
      - specialize(balanced_with_nil p G); intros. fill_triv.
        destruct H2 as (r,[Hb | Hb]).
        + inversion Hb; subst.
          assert (q = r).
          { eapply assoc_step_s_sl_r; eassumption. }
          subst q.
          destruct (assoc_step_sl_to_step_f p r l xs gtx B H0 H1) as [G' Hstep].
          exists gtx, G'. split; [constructor|exact Hstep].
        + inversion Hb; subst.
          exfalso.
          pose proof (assoc_step_sl_op gtx p q l r p xs B H1 H0) as Hneq.
          apply Hneq. reflexivity.
      - rename H2 into Hka. destruct G as [|s s0 o].
        specialize(balanced_with_Sk k p gtt_end); intros.
        assert False. apply H2; try easy. easy.
        
        destruct (participant_dec p s) as [Hps|Hps].
        subst.
        - assert (Hqs : q = s0) by (eapply assoc_step_s_sl_r; eassumption).
          subst q.
          destruct (assoc_step_sl_to_step_f s s0 l o gtx B H0 H1) as [G' Hstep].
          exists gtx, G'. split; [constructor|exact Hstep].
        - specialize(regGtt_some_cont s s0 o); intros. fill_triv. destruct_exists_and.
          rename x into lbranch. destruct x0 as [sbranch Gbranch].
          specialize(assoc_back (gtt_send s s0 o) gtx Gbranch s s0 lbranch); intros.
          assert_concl_of H5 as Ht.
          {
            apply H5; try easy.
            pfold. apply steq with sbranch; try easy.
            specialize(participant_dec s s0); intros. destruct H6; try easy. subst.
            inversion H0. specialize(H6 s0).
            assert(exists T : ltt, gtx s0 = Some T). apply H6. constructor.
            destruct_exists_and. 
            specialize(H7 s0 x). fill_triv. destruct_exists_and.
            pinversion H7; subst; try easy; try mon_easy.
            assert False. apply H10. constructor. easy.
          }
          clear H5.
          destruct Ht as [Gl_next [lnext [Bnext [Gnext [H5 [H6 [H7 H8]]]]]]].
          rename Gl_next into Gl. rename lnext into l'.
          specialize(IHk Gl Gnext l p q).
          assert_concl_of IHk as Hk.
          {
            pinversion H7; subst; try easy; try mon_easy.
            assert (Hneq_sender : p <> s) by exact Hps.
            assert (Hneq_receiver : p <> s0) by (eapply assoc_step_sl_op; eassumption).
            assert(ctx_step_sl Gl p q l B).
            {
              eapply ctx_step_sl_preserved_by_other_step; eassumption.
            }
            apply IHk; try easy.
            - specialize(balanced_k_cont); intros.
              apply H10 with s s0 o l' s1; try easy.
            - assert (Hstep_global : gttstepC (gtt_send s s0 o) Gnext s s0 l').
              { pfold. exact H7. }
              exact (regGtt_after_step (gtt_send s s0 o) H3 H4 Gnext s s0 l' Hstep_global).
            - apply P_after_step with gtx; try easy.
              apply multi_step with Gl; try easy.
              - eapply step_on_f. exact H5.
              - constructor.
          }
          destruct Hk as (gt1,(gt2,(Hc,Hd))).
          exists gt1. exists gt2. split; try easy.
          apply multi_step with Gl; try easy. 
          eapply step_on_f. exact H5.
    (* recv case *)
    - intros.
      specialize(part_on_ctx_step_r gtx p q G); intros. fill_triv.
      specialize(part_with_balanced_k q G); intros. fill_triv.
      destruct H6 as (k, Ha). clear H5.
      revert Ha H1 H4 H3 H0 H2. revert gtx G p q.
      induction k; intros. rename H2 into Hta.
      - specialize(balanced_with_nil q G); intros. fill_triv.
        destruct H2 as (r,[Hb | Hb]).
        - inversion Hb. subst.
          inversion H1. subst. inversion H0. 
          specialize(H7 q (ltt_recv p xs0)). fill_triv.
          destruct_exists_and.
          pinversion H7; subst; try mon_easy; try easy.
          - assert False. 
            apply H9. constructor.
            easy.
          - pinversion H8; try mon_easy.
        - inversion Hb; subst.
          inversion H1. subst. inversion H0. 
          specialize(H7 q (ltt_recv p xs0)). fill_triv. 
          destruct_exists_and. pinversion H7; subst; try easy; try mon_easy.
          - subst. assert False.
            apply H9. constructor.
            easy.
          - subst.
            pinversion H8; try mon_easy; clear H8; subst.
            exists gtx. 
            inversion H0. specialize(H8 r).
            assert(exists T : ltt, gtx r = Some T). apply H8; constructor; clear H8.
            destruct_exists_and. specialize(H9 r x). fill_triv. destruct_exists_and.
            pinversion H9; subst; try easy; try mon_easy.
            - assert False.
              apply H17. constructor.
              easy.
            clear H21 H13.
            pinversion H14; try mon_easy. subst.
            pose proof Hta as Hk. 
            specialize(Hk r (ltt_send q xs1)). fill_triv.
            specialize(regLtt_some_cont_send q xs1); intros. fill_triv. destruct_exists_and.
            specialize(H18 x). specialize(H24 x). specialize(H16 x). specialize(H10 x).
            rewrite H13 in H18. destruct H18; try easy. destruct_exists_and.
            rewrite H18 in H24. destruct H24; try easy. destruct_exists_and.
            inversion H22; subst.
            destruct H16 as [[Hglobal_none Hprojection_none]
              | [sg [Gcont [Tproj [Hglobal_branch [Hprojection_branch Hprojection_cont]]]]]].
            - congruence.
            - rewrite Hprojection_branch in H10.
              destruct H10 as [Hprojection_none'|[sr [Trecv [Trecv_proj [Hrecv_branch [Hrecv_proj Hrecv_sub]]]]]].
              + congruence.
              + inversion Hrecv_proj; subst sr Trecv_proj.
                invert_all_some.
                assert (sg = x5) by congruence. subst sg.
                exists (insert (insert gtx r x3) q Trecv).
                exists x. exists x5. split; [constructor|].
                eapply step_sr with (xs:=xs1) (ys:=xs0) (T:=x3) (T':=Trecv) (B:=x5); try easy.
                intros pt.
                destruct (participant_dec pt r) as [Hpr|Hpr].
                * subst pt. destruct (participant_dec r r) as [_|Hfalse].
                  -- cbn [is_left].
                     rewrite (FMap.insert_neq participant ltt (insert gtx r x3) q r Trecv (nesym H12)).
                     apply insert_eq.
                  -- contradiction.
                * destruct (participant_dec pt q) as [Hpq|Hpq].
                  -- subst pt. destruct (participant_dec q r) as [Hqr|Hqr].
                     ++ exfalso. apply H12. symmetry. exact Hqr.
                     ++ cbn [is_left]. apply insert_eq.
                  -- cbn [is_left].
                     rewrite (FMap.insert_neq participant ltt (insert gtx r x3) q pt Trecv (nesym Hpq)).
                     rewrite (FMap.insert_neq participant ltt gtx r pt x3 (nesym Hpr)).
                     reflexivity.
      - rename H2 into Hka. destruct G as [|s s0 o].
        specialize(balanced_with_Sk k q gtt_end); intros.
        assert False. apply H2; try easy. easy.
        
        destruct (participant_dec q s0) as [Hq_s0|Hq_s0].
        subst.
        - specialize(assoc_step_s_r_r gtx s s0 o p); intros. fill_triv. subst.
          clear IHk Ha.
          inversion H1. subst. inversion H0.
          specialize(H6 s). assert(exists T : ltt, gtx s = Some T). apply H6. constructor. clear H6.
          pose proof H7 as Hk. destruct_exists_and.
          specialize(H7 s0 (ltt_recv s xs)). specialize(Hk s x). fill_triv.
          destruct_exists_and.
          pinversion H10; try mon_easy; subst. clear H10.
          pinversion H7; subst; try mon_easy; try easy. clear H15.
          pinversion H8; subst; try mon_easy; try easy.
          - assert False. apply H10. constructor. easy.
          clear H15 H13 H20 H17 H8 H7.
          pinversion H9; subst; try mon_easy.
          specialize(Hka s (ltt_send s0 xs0)). fill_triv.
          specialize(regLtt_some_cont_send s0 xs0); intros; fill_triv.
          destruct_exists_and.
          specialize(H14 x). specialize(H18 x). specialize(H21 x). specialize(H10 x).
          rewrite H7 in H10. destruct H10; try easy. destruct_exists_and.
          rewrite H10 in H21. destruct H21; try easy. destruct_exists_and.
          inversion H13; subst x4 x6.
          destruct H18 as [[Hglobal_none Hys_none]
            | [sg [gcont [Tproj [Hglobal [Hys Hproj]]]]]].
          - congruence.
          - rewrite Hys in H14.
            destruct H14 as [Hys_none'|[sr [Trecv [Trecv_proj [Hrecv [Hys' Hsub]]]]]].
            + congruence.
            + inversion Hys'; subst sr Trecv_proj.
              assert (sg = x1) by congruence. subst sg.
              inversion H8; subst x0.
              exists gtx.
              exists (insert (insert gtx s x2) s0 Trecv).
              exists x. exists x1. split; [constructor|].
              eapply step_sr with (xs:=xs0) (ys:=xs) (T:=x2) (T':=Trecv) (B:=x1); try easy.
              intros pt.
              destruct (participant_dec pt s) as [Hps|Hps].
              * subst pt. destruct (participant_dec s s) as [_|Hfalse].
                -- cbn [is_left].
                   rewrite (FMap.insert_neq participant ltt (insert gtx s x2) s0 s Trecv (nesym H16)).
                   apply insert_eq.
                -- contradiction.
              * destruct (participant_dec pt s0) as [Hps0|Hps0].
                -- subst pt. destruct (participant_dec s0 s) as [Hneq|Hneq].
                   ++ exfalso. apply H16. symmetry. exact Hneq.
                   ++ cbn [is_left]. apply insert_eq.
                -- cbn [is_left].
                   rewrite (FMap.insert_neq participant ltt (insert gtx s x2) s0 pt Trecv (nesym Hps0)).
                   rewrite (FMap.insert_neq participant ltt gtx s pt x2 (nesym Hps)).
                   reflexivity.
        -
          specialize(regGtt_some_cont s s0 o); intros. fill_triv. destruct_exists_and.
          rename x into lbranch. destruct x0 as [sbranch Gbranch].
          specialize(assoc_back (gtt_send s s0 o) gtx Gbranch s s0 lbranch); intros.
          assert_concl_of H5 as Ht.
          {
            apply H5; try easy.
            pfold. apply steq with sbranch; try easy.
            specialize(participant_dec s s0); intros. destruct H6; try easy. subst.
            inversion H0. specialize(H6 s0).
            assert(exists T : ltt, gtx s0 = Some T). apply H6. constructor.
            destruct_exists_and. 
            specialize(H7 s0 x). fill_triv. destruct_exists_and.
            pinversion H7; subst; try easy; try mon_easy.
            assert False. apply H10. constructor. easy.
          }
          clear H5.
          destruct Ht as [Gl_next [lnext [Bnext [Gnext [H5 [H6 [H7 H8]]]]]]].
          rename Gl_next into Gl. rename lnext into l'.
          specialize(IHk Gl Gnext p q).
          assert_concl_of IHk as Hk.
          {
            pinversion H7; subst; try easy; try mon_easy.
            assert (Hq_s : q <> s) by (eapply assoc_step_r_op; eassumption).
            assert(ctx_step_r Gl q p).
            {
              eapply ctx_step_r_preserved_by_other_step; eassumption.
            }
            apply IHk; try easy.
            - specialize(balanced_k_cont); intros.
              apply H10 with s s0 o l' s1; try easy.
            - assert (Hstep_global : gttstepC (gtt_send s s0 o) Gnext s s0 l').
              { pfold. exact H7. }
              exact (regGtt_after_step (gtt_send s s0 o) H3 H4 Gnext s s0 l' Hstep_global).
            - apply P_after_step with gtx; try easy.
              apply multi_step with Gl; try easy.
              - eapply step_on_f. exact H5.
              - constructor.
          }
          destruct Hk as (gt1,(gt2,(la,(Ba,(Hc,Hd))))).
          exists gt1. exists gt2. exists la. exists Ba. split; try easy.
          apply multi_step with Gl; try easy. 
          eapply step_on_f. exact H5.
  Qed.
        
    
End ctx_sf_df.



Section ctx_liveness.

(* Main liveness theorem for associated typing contexts. *)

Lemma assoc_step_s_to_step_f `{good_merge} : forall p q xs Gl,
      assoc_gctx Gl (gtt_send p q xs) -> 
      ctx_step_s Gl p q ->
      exists l B Gl', ctx_step_f Gl p q l B Gl'.
Proof.
  intros p q xs Gl Hassoc Hstep.
  inversion Hstep as [G0 p0 q0 xs0 l st Hsend Hbranch]; subst.
  destruct st as [B T].
  assert (Hsl : ctx_step_sl Gl p q l B) by (apply step_sl with xs0 T; assumption).
  destruct (assoc_step_sl_to_step_f p q l xs Gl B Hassoc Hsl) as [Gl' Hf].
  exists l, B, Gl'. exact Hf.
Qed.

Lemma assoc_wdef_to_step_s `{good_merge} : forall p q xs (Gl : typ_ctx),
    (forall pt T, Gl pt = Some T -> regLtt T) ->
    assoc_gctx Gl (gtt_send p q xs) -> 
    ctx_step_s Gl p q.
Proof.
  intros.
  inversion H1. clear H1.
  assert(exists T : ltt, Gl p = Some T).
  {
    apply H2; try easy. 
    constructor.
  }
  assert(exists T : ltt, Gl q = Some T).
  {
    apply H2; try easy. 
    constructor.
  }
  destruct H1 as (T, Ha).
  destruct H4 as (T', Hb).
  pose proof H3 as H4.
  specialize(H3 p T Ha). specialize(H4 q T' Hb).
  destruct H3 as (T1,(Hc,Hd)).
  destruct H4 as (T2,(He,Hf)).
  assert(isgPartsC p (gtt_send p q xs)). constructor.
  assert(isgPartsC q (gtt_send p q xs)). constructor.
  pinversion Hc; try easy; try mon_easy.
  subst.
  pinversion He; try easy; try mon_easy. 
  subst.
  clear H12 H9 H8 H1 H3 H14 H10.
  pinversion Hf; try mon_easy. subst.
  pinversion Hd; try mon_easy. subst.
  clear Hf He Hd Hc.
  specialize(H0 p (ltt_send q xs1) Ha).
  specialize(regLtt_some_cont_send q xs1 H0); intros.
  destruct H1 as (l,(sg,Hc)).
  apply step_s with xs1 l sg; assumption.
Qed.


  

Lemma wgx_forward `{good_merge} : forall n G Gl Gl' gxs, balancedG G -> regGtt G -> wdef gxs -> stnth 0 gxs = Some Gl -> stnth n gxs = Some Gl' -> assoc_gctx Gl G -> exists G', assoc_gctx Gl' G' /\ balancedG G' /\ regGtt G' /\ multiC G G'.
Proof.
  induction n; intros; try easy.
  - rewrite H3 in H4. inversion H4. subst. exists G. split. easy. split.  easy. split. easy. constructor.
  - destruct gxs; try easy.
    simpl in *. subst. 
    destruct gxs; try easy.
    - destruct n; try easy.
    - specialize(assoc_on G Gl); intros.
      pose proof H2 as Ht. unfold wdef in Ht. destruct Ht as (Ht, Hta). 
      specialize(Ht 0 t t0). simpl in Ht.
      assert(exists (p q : participant) (l : fin) (B : sort), ctx_step_f t p q l B t0).
      {
        apply Ht; try easy.
      }
      clear Ht. destruct H7 as (p1,(q1,(l1,(B1,Ha)))).
      inversion H3. subst. clear H3.
      specialize(H6 t0 p1 q1 l1 B1 H1 H0 H5 Ha).
      destruct H6 as (G',(Hb,(Hc,Hd))).
      specialize(regGtt_after_step G H1 H0 G' p1 q1 l1 Hc); intros.
      specialize(IHn G' t0 Gl' (st_cons t0 gxs)).
      assert(exists G'0 : gtt,
        assoc_gctx Gl' G'0 /\ balancedG G'0 /\ regGtt G'0 /\ multiC G' G'0).
      {
        apply IHn; try easy.
        unfold wdef in *. split.
        intros. destruct H2 as (H2, Htb).
        specialize(H2 (S n0) G1 G2). simpl in *. apply H2; try easy.
        intros. specialize(Hta (S n0) G1 pt T). apply Hta; try easy.
      }
      destruct H6. exists x. split. easy. split. easy. split. easy.
      apply multiC_step with G' p1 q1 l1; try easy.

Qed.

Lemma assoc_step_irr_s : forall n gxs p q s s0 Gl G2 l {B : sort},
        wdef gxs ->
        stnth n gxs = Some Gl -> 
        stnth (S n) gxs = Some G2 ->
        p <> s -> p <> s0 ->
        ctx_step_f Gl s s0 l B G2 ->
        ctx_step_s Gl p q -> 
        ctx_step_s G2 p q.
Proof.
  intros n gxs p q s s0 Gl G2 l B Hwf Hbefore Hafter Hps Hps0 Hf Hs.
  eapply ctx_step_s_preserved_by_other_step; eassumption.
Qed.

Lemma assoc_step_irr_r : forall n gxs p q s s0 Gl G2 l {B : sort},
        wdef gxs ->
        stnth n gxs = Some Gl -> 
        stnth (S n) gxs = Some G2 ->
        q <> s -> q <> s0 ->
        ctx_step_f Gl s s0 l B G2 ->
        ctx_step_r Gl q p -> 
        ctx_step_r G2 q p.
Proof.
  intros n gxs p q s s0 Gl G2 l B Hwf Hbefore Hafter Hqs Hqs0 Hf Hr.
  eapply ctx_step_r_preserved_by_other_step; eassumption.
Qed.

Lemma wdef_tail : forall Gl gxs, wdef (st_cons Gl gxs) -> wdef gxs.
Proof.
  intros.
  inversion H.
  split.
  - intros.
    specialize(H0 (S n) G1 G2). apply H0; try easy.
  - intros.
    specialize(H1 (S n) G1). apply H1 with pt; try easy.
Qed.

Lemma fair_path_tail : forall Gl gxs, fair_path (st_cons Gl gxs) -> fair_path gxs.
Proof.
  intros.
  unfold fair_path in *.
  intros.
  specialize(H (S n) Gl0 Gl' p q l B). 
  simpl in H. fill_triv.
  destruct H as (k1,(l1,(B1,(G1,(G2,(Ha,(Hb,(Hc,Hd)))))))).
  destruct k1; try easy.
  exists k1. exists l1. exists B1. exists G1. exists G2. easy.
Qed.

Lemma assoc_fair_live_n0_s `{good_merge} : forall m gxs Gl p q s s0 o k G1 G2 l {B : sort},
          wdef gxs -> 
          fair_path gxs ->
          stnth 0 gxs = Some Gl ->
          ctx_step_s Gl p q ->
          assoc_gctx Gl (gtt_send s s0 o) ->
          balancedG (gtt_send s s0 o) ->
          regGtt (gtt_send s s0 o) ->
          balanced_with k.+1 p (gtt_send s s0 o) ->
          stnth m gxs = Some G1 ->
          stnth m.+1 gxs = Some G2 ->
          ctx_step_f G1 s s0 l B G2 ->
          (exists (k0 l0 : fin) (B0 : sort) (G0 G3 : typ_ctx),
             0 <= k0 /\
             stnth k0 gxs = Some G0 /\ stnth k0.+1 gxs = Some G3 /\ ctx_step_f G0 p q l0 B0 G3) \/
          (exists (k0 : fin) (G0 : typ_ctx) (G' : gtt),
             0 <= k0 /\
             stnth k0 gxs = Some G0 /\
             assoc_gctx G0 G' /\
             balancedG G' /\ regGtt G' /\ balanced_with k p G' /\ ctx_step_s G0 p q).
Proof.
  induction m; intros.
  - rewrite H8 in H2. invert_all_some.
    destruct (participant_dec p s) as [Hps|Hps].
    - subst p.
      pose proof (assoc_step_s_f_r Gl s q s0 l B G2 H3 H10) as Hq.
      subst q.
      left. exists 0. exists l. exists B. exists Gl. exists G2.
      repeat split; try easy.
    - pose proof (assoc_step_s_op Gl p q s s0 o H3 H4) as Hps0.
      destruct (assoc_on (gtt_send s s0 o) Gl G2 s s0 l B H6 H5 H4 H10)
        as [G' [Hassoc' [Hstep_global Hbal']]].
      pose proof (regGtt_after_step (gtt_send s s0 o) H6 H5 G' s s0 l Hstep_global) as Hreg'.
      assert (Hbw' : balanced_with k p G').
      {
        pinversion Hstep_global; subst; try easy; try mon_easy.
        eapply balanced_k_cont; eassumption.
      }
      assert (Hsl' : ctx_step_s G2 p q).
      { eapply ctx_step_s_preserved_by_other_step; eassumption. }
      right. exists 1. exists G2. exists G'.
      split; [easy|]. split; [exact H9|]. split; [exact Hassoc'|].
      split; [exact Hbal'|]. split; [exact Hreg'|].
      split; [exact Hbw'|exact Hsl'].
  - assert(exists Gl', stnth 1 gxs = Some Gl') as Hnext_ctx.
    {
      destruct gxs; try easy. destruct gxs; try easy.
      simpl in *. exists t0. easy.
    }
    destruct Hnext_ctx as (Gl', Ha).
    destruct gxs; try easy.
    simpl in H2. inversion H2; subst.
    simpl in Ha.
    pose proof H0 as Hwf_full. unfold wdef in Hwf_full.
    destruct Hwf_full as [Hwf_steps Hwf_regular].
    assert (Hzero : stnth 0 (st_cons Gl gxs) = Some Gl) by reflexivity.
    pose proof (Hwf_steps 0 Gl Gl' Hzero Ha) as Hpath_step.
    destruct Hpath_step as (p1,(q1,(l1,(B1,Hb)))).
    destruct (participant_dec p p1) as [Hpp1|Hpp1].
    - subst. left. 
      exists 0. exists l1. exists B1. exists Gl. exists Gl'.
      specialize(assoc_step_s_f_r Gl p1 q q1 l1 B1 Gl' H3 Hb); intros. subst.
      repeat (split; try easy).
    - pose proof (assoc_on (gtt_send s s0 o) Gl Gl' p1 q1 l1 B1 H6 H5 H4 Hb) as Hassoc_step.
      destruct Hassoc_step as (G',(Hc,(Hd,He))).
      specialize(regGtt_after_step (gtt_send s s0 o) H6 H5 G' p1 q1 l1 Hd); intros.
      pinversion Hd; try easy; try mon_easy.
      - right. subst. 
        specialize(assoc_step_s_op Gl p q p1 q1 o H3 H4); intros.
        exists 1. exists Gl'. exists G'.
        repeat (split; try easy).
        - specialize(balanced_k_cont k p p1 q1 o l1 s1 G'); intros.
          apply H13; try easy.
        - specialize(assoc_step_irr_s 0 (st_cons Gl gxs) p q p1 q1 Gl Gl' l1 (B:=B1)); intros.
          apply H13; try easy.
      - subst.
        specialize(IHm gxs Gl' p q s s0 f' k G1 G2 l B).
        assert((exists (k0 l0 : fin) (B0 : sort) (G0 G3 : typ_ctx),
           0 <= k0 /\
           stnth k0 gxs = Some G0 /\
           stnth k0.+1 gxs = Some G3 /\ ctx_step_f G0 p q l0 B0 G3) \/
        (exists (k0 : fin) (G0 : typ_ctx) (G' : gtt),
           0 <= k0 /\
           stnth k0 gxs = Some G0 /\
           assoc_gctx G0 G' /\
           balancedG G' /\ regGtt G' /\ balanced_with k p G' /\ ctx_step_s G0 p q)).
        {
          specialize(assoc_step_s_f_r_op Gl p q p1 q1 l1 B1 Gl'); intros.
          fill_triv.
          apply IHm; try easy; clear IHm.
          - apply wdef_tail with Gl; try easy.
          - apply fair_path_tail with Gl; try easy.
          - specialize(assoc_step_irr_s 0 (st_cons Gl gxs) p q p1 q1 Gl Gl' l1 (B:=B1)); intros.
            apply H13; try easy.
          - specialize(step_balanced_with k.+1 (gtt_send s s0 o) (gtt_send s s0 f') p1 q1 p l1); intros.
            assert(balanced_with k.+1 p (gtt_send s s0 f') \/ p = p1 \/ p = q1).
            {
              apply H13; try easy. 
              pfold. easy.
            }
            clear H13. 
            destruct H14 as [Hbw|[Hpeq1|Hpeq2]]; try easy.
        }
        destruct H12.
        - left.
          destruct_exists_and.
          exists (S x). exists x0. exists x1. exists x2. exists x3. easy.
        - right. 
          destruct_exists_and.
          exists (S x). exists x0. exists x1. easy.
Qed.

Lemma assoc_fair_live_n0_r `{good_merge} : forall m gxs Gl p q s s0 o k G1 G2 l {B : sort},
          wdef gxs -> 
          fair_path gxs ->
          stnth 0 gxs = Some Gl ->
          ctx_step_r Gl q p ->
          assoc_gctx Gl (gtt_send s s0 o) ->
          balancedG (gtt_send s s0 o) ->
          regGtt (gtt_send s s0 o) ->
          balanced_with k.+1 q (gtt_send s s0 o) ->
          stnth m gxs = Some G1 ->
          stnth m.+1 gxs = Some G2 ->
          ctx_step_f G1 s s0 l B G2 ->
          (exists (k0 l0 : fin) (B0 : sort) (G0 G3 : typ_ctx),
             0 <= k0 /\
             stnth k0 gxs = Some G0 /\ stnth k0.+1 gxs = Some G3 /\ ctx_step_f G0 p q l0 B0 G3) \/
          (exists (k0 : fin) (G0 : typ_ctx) (G' : gtt),
             0 <= k0 /\
             stnth k0 gxs = Some G0 /\
             assoc_gctx G0 G' /\
             balancedG G' /\ regGtt G' /\ balanced_with k q G' /\ ctx_step_r G0 q p).
Proof.
  induction m; intros.
  - rewrite H8 in H2. invert_all_some.
    destruct (assoc_on (gtt_send s s0 o) Gl G2 s s0 l B H6 H5 H4 H10)
      as (G',(Hassoc',(Hglobal_step,Hbal'))).
    pose proof (regGtt_after_step (gtt_send s s0 o) H6 H5 G' s s0 l Hglobal_step) as Hreg'.
    specialize(participant_dec q s0); intros. destruct H2.
    - left. subst.
      assert (Hp : p = s).
      { eapply assoc_step_s_r_r; eassumption. }
      subst p.
      exists 0. exists l. exists B. exists Gl. exists G2.
      repeat (split; try easy).
    - right.
      exists 1. exists G2. exists G'.
      assert (Hqs : q <> s) by (eapply assoc_step_r_op; eassumption).
      assert (Hbw' : balanced_with k q G').
      {
        pinversion Hglobal_step; try easy; try mon_easy.
        subst.
        eapply balanced_k_cont; eassumption.
      }
      assert (Hrecv' : ctx_step_r G2 q p).
      {
        eapply assoc_step_irr_r with (n:=0) (gxs:=gxs) (s:=s) (s0:=s0)
          (Gl:=Gl) (G2:=G2) (l:=l) (B:=B); eassumption.
      }
      repeat (split; try assumption).
  - assert (Hnext_ctx : exists Gl', stnth 1 gxs = Some Gl').
    {
      destruct gxs; try easy. destruct gxs; try easy.
      simpl in *. exists t0. easy.
    }
    destruct Hnext_ctx as (Gl', Ha).
    destruct gxs; try easy.
    simpl in H2. inversion H2; subst.
    simpl in Ha.
    pose proof H0 as Hwf_full. unfold wdef in Hwf_full.
    destruct Hwf_full as [Hwf_steps Hwf_regular].
    assert (Hzero : stnth 0 (st_cons Gl gxs) = Some Gl) by reflexivity.
    pose proof (Hwf_steps 0 Gl Gl' Hzero Ha) as Hpath_step.
    destruct Hpath_step as (p1,(q1,(l1,(B1,Hb)))).
    destruct (participant_dec q q1) as [Hqq1|Hqq1].
    - subst. left. 
      exists 0. exists l1. exists B1. exists Gl. exists Gl'.
      specialize(assoc_step_r_f_r Gl p1 p q1 l1 B1 Gl' H3 Hb); intros. subst.
      repeat (split; try easy).
    - pose proof (assoc_on (gtt_send s s0 o) Gl Gl' p1 q1 l1 B1 H6 H5 H4 Hb)
        as Hassoc_step.
      destruct Hassoc_step as (G',(Hassoc',(Hglobal_step,Hbal'))).
      pose proof (regGtt_after_step (gtt_send s s0 o) H6 H5 G' p1 q1 l1 Hglobal_step)
        as Hreg'.
      pinversion Hglobal_step; try easy; try mon_easy.
      - right. subst.
        assert (Hneq_sender : q <> p1) by (eapply assoc_step_r_op; eassumption).
        assert (Hbw' : balanced_with k q G').
        { eapply balanced_k_cont; eassumption. }
        assert (Hrecv' : ctx_step_r Gl' q p).
        { eapply ctx_step_r_preserved_by_other_step; eassumption. }
        exists 1. exists Gl'. exists G'.
        split; [easy|]. split; [exact Ha|]. split; [exact Hassoc'|].
        split; [exact Hbal'|]. split; [exact Hreg'|].
        split; [exact Hbw'|exact Hrecv'].
      - subst.
        specialize(IHm gxs Gl' p q s s0 f' k G1 G2 l B).
        assert (Hrecursive : (exists (k0 l0 : fin) (B0 : sort) (G0 G3 : typ_ctx),
           0 <= k0 /\
           stnth k0 gxs = Some G0 /\
           stnth k0.+1 gxs = Some G3 /\ ctx_step_f G0 p q l0 B0 G3) \/
        (exists (k0 : fin) (G0 : typ_ctx) (G' : gtt),
           0 <= k0 /\
           stnth k0 gxs = Some G0 /\
           assoc_gctx G0 G' /\
           balancedG G' /\ regGtt G' /\ balanced_with k q G' /\ ctx_step_r G0 q p)).
        {
          assert (Hneq_sender : q <> p1) by (eapply assoc_step_r_f_r_op; eassumption).
          assert (Hrecv' : ctx_step_r Gl' q p).
          { eapply ctx_step_r_preserved_by_other_step; eassumption. }
          apply IHm; try easy; clear IHm.
          - apply wdef_tail with Gl; try easy.
          - apply fair_path_tail with Gl; try easy.
          - assert (Hglobal_stepC : gttstepC (gtt_send s s0 o)
                (gtt_send s s0 f') p1 q1 l1).
            { pfold. exact Hglobal_step. }
          - specialize (step_balanced_with k.+1 (gtt_send s s0 o)
              (gtt_send s s0 f') p1 q1 q l1 Hglobal_stepC H7) as Hbw_step.
            assert (Hbw' : balanced_with k.+1 q (gtt_send s s0 f')).
            {
              destruct Hbw_step as [Hbw'|[Hqp1|Hqq1']]; [exact Hbw'| |].
              - contradiction.
              - contradiction.
            }
            exact Hbw'.
        }
        destruct Hrecursive.
        - left.
          destruct_exists_and.
          exists (S x). exists x0. exists x1. exists x2. exists x3. easy.
        - right. 
          destruct_exists_and.
          exists (S x). exists x0. exists x1. easy.
Qed.



Theorem assoc_fair_live `{good_merge} : forall gtx gxs G, regGtt G -> balancedG G -> stnth 0 gxs = Some gtx -> assoc_gctx gtx G -> wdef gxs -> fair_path gxs -> live_path gxs.
Proof.
  intros.
  unfold live_path.
  split.
  - intros.
    specialize(wgx_forward n G gtx Gl gxs); intros.
    assert(exists G' : gtt, assoc_gctx Gl G' /\ balancedG G' /\ regGtt G' /\ multiC G G').
    {
      apply H8; try easy.
    }
    clear H8.
    destruct H9 as (G',(Ha,(Hb,(Hc,Hd)))).
    clear H0 H1 H2 H3 Hd. clear G gtx. rename G' into G.
    
    specialize(part_with_balanced_k p); intros.
    assert(exists k : fin, balanced_with k p G).
    {
      apply H0; try easy.
      apply part_on_ctx_step_s with Gl q; try easy.
    }
    clear H0. destruct H1 as (k, Hd).
    revert H6 H7 Ha Hb Hc Hd. revert n Gl G.
    induction k; intros.
    - specialize(balanced_with_nil p G Hd); intros.
      destruct H0 as (r,He). clear Hd.
      inversion H7. subst.
      
      unfold assoc_gctx in Ha. destruct Ha as (Ha, Hf). pose proof Hf as Hsa.
      specialize(Hf p (ltt_send q xs) H0). 
      destruct Hf as (T',(Hg,Hh)). pinversion Hh. subst.
      assert(exists l B0 Gl', ctx_step_f Gl p q l B0 Gl').
      {
        clear Hh.
        destruct He as [He | He].
        - inversion He. subst. 
          pinversion Hg; try easy. subst.
          apply assoc_step_s_to_step_f with xs0; try easy.
          apply proj_mon.
        - inversion He. subst. 
          pinversion Hg; try easy.
          apply proj_mon.
      }
      destruct H2 as (l1,(B1,(Gl', Hta))).
      unfold fair_path in H5.
      destruct (H5 n Gl Gl' p q l1 B1 H6 Hta)
        as (k0,(l0,(B0,(G1,(G2,(Hle,(Hst1,(Hst2,Hstep)))))))).
      exists k0. exists l0. exists G1. exists G2. exists B0.
      repeat split; try assumption.
      apply sub_mon.
    -
      assert((exists (k0 l : fin) (G1 G2 : typ_ctx) (B0 : sort),
        n <= k0 /\
        stnth k0 gxs = Some G1 /\ stnth k0.+1 gxs = Some G2 /\ ctx_step_f G1 p q l B0 G2) \/ 
        (exists k0 G1 G', n <= k0 /\ stnth k0 gxs = Some G1 /\ assoc_gctx G1 G' /\ balancedG G' /\ regGtt G' /\ balanced_with k p G' /\ ctx_step_s G1 p q)).
      {
        clear IHk. 
        pose proof H5 as Ht.
        unfold fair_path in Ht.
        destruct G.
        - specialize(balanced_with_Sk k p gtt_end); intros.
          assert False. apply H0; try easy. easy.
        - assert(ctx_step_s Gl p0 p1).
          {
            specialize(assoc_wdef_to_step_s); intros.
            apply H0 with o; try easy.
            inversion H4.
            intros. apply H2 with n Gl pt; try easy.
          }
          specialize(assoc_step_s_to_step_f p0 p1 o Gl Ha H0); intros.
          destruct H1 as (l,(B1,(Gl',He))).
          specialize(Ht n Gl Gl' p0 p1 l B1 H6 He).
          clear He H0. clear Gl' l B1.
          destruct Ht as (m,(l,(B0,(G1,(G2,(He,(Hf,(Hg,Hh)))))))).
          
          revert Hh Hg Hf He Hd Hc Hb Ha H7 H6 H4 H5.
          revert G1 G2 l B0 o Gl k m p q gxs p0 p1.
          induction n; intros.
          - pose proof (assoc_fair_live_n0_s
              m gxs Gl p q p0 p1 o k G1 G2 l (B:=B0)
              H4 H5 H6 H7 Ha Hb Hc Hd Hf Hg Hh) as Hlive.
            destruct Hlive as [Hfuture|Hpending].
            - left. destruct Hfuture as (k0,(l0,(B1,(G3,(G4,(Hle,(Hst1,(Hst2,Hstep)))))))).
              exists k0. exists l0. exists G3. exists G4. exists B1.
              repeat split; try assumption.
            - right. destruct Hpending as (k0,(G3,(G',(Hle,(Hst1,(Hassoc,(Hbal,(Hreg,(Hbw,Hstep))))))))).
              exists k0. exists G3. exists G'.
              split; [exact Hle|]. split; [exact Hst1|]. split; [exact Hassoc|].
              split; [exact Hbal|]. split; [exact Hreg|].
              split; [exact Hbw|exact Hstep].
          - destruct m; try easy. destruct gxs; try easy.
            specialize(IHn G1 G2 l B0 o Gl k m p q gxs p0 p1).
            assert((exists (k0 l : fin) (G1 G2 : typ_ctx) (B1 : sort),
               n <= k0 /\
               stnth k0 gxs = Some G1 /\
               stnth k0.+1 gxs = Some G2 /\ ctx_step_f G1 p q l B1 G2) \/
            (exists (k0 : fin) (G1 : typ_ctx) (G' : gtt),
               n <= k0 /\
               stnth k0 gxs = Some G1 /\
               assoc_gctx G1 G' /\
               balancedG G' /\ regGtt G' /\ balanced_with k p G' /\ ctx_step_s G1 p q)).
            {
              apply IHn; try easy.
              apply wdef_tail with t; try easy.
              apply fair_path_tail with t; try easy.
            }
            destruct H0.
            - left.
              destruct H0 as (k1,(l1,(G3,(G4,(B1,(Hi,(Hj,(Hl,Hm)))))))).
              exists (S k1). exists l1. exists G3. exists G4. exists B1. easy.
            - right.
              destruct H0 as (k1,(G3,(G',Ht))).
              exists (S k1). exists G3. exists G'. easy.
      }
      
      destruct H0; try easy.
      destruct H0 as (k0,(G1,(G',(He,(Hf,(Hg,(Hh,(Hi,(Hj,Hk))))))))).
      specialize(IHk k0 G1 G').
      assert(exists (k l : fin) (G1 G2 : typ_ctx) (B0 : sort),
        k0 <= k /\
        stnth k gxs = Some G1 /\ stnth k.+1 gxs = Some G2 /\ ctx_step_f G1 p q l B0 G2).
      {
        apply IHk; try easy.
      }
      destruct H0 as (k1,(l1,(G2,(G3,(B1,(Hl,(Hn,(Ho,Hp)))))))).
      exists k1. exists l1. exists G2. exists G3. exists B1. split; try easy.
      apply leq_trans with k0; try easy.
  - intros.
    specialize(wgx_forward n G gtx Gl gxs); intros.
    assert(exists G' : gtt, assoc_gctx Gl G' /\ balancedG G' /\ regGtt G' /\ multiC G G').
    {
      apply H8; try easy.
    }
    clear H8.
    destruct H9 as (G',(Ha,(Hb,(Hc,Hd)))).
    clear H0 H1 H2 H3 Hd. clear G gtx. rename G' into G.
    
    specialize(part_with_balanced_k q); intros.
    assert(exists k : fin, balanced_with k q G).
    {
      apply H0; try easy.
      apply part_on_ctx_step_r with Gl p; try easy.
    }
    clear H0. destruct H1 as (k, Hd).
    revert H6 H7 Ha Hb Hc Hd. revert n Gl G.
    induction k; intros.
    - specialize(balanced_with_nil q G Hd); intros.
      destruct H0 as (r,He). clear Hd.
      inversion H7. subst.
      pose proof Ha as Hta.
      unfold assoc_gctx in Ha. destruct Ha as (Ha, Hf). pose proof Hf as Hsa.
      specialize(Hf q (ltt_recv p xs) H0). 
      destruct Hf as (T',(Hg,Hh)). pinversion Hh. subst.
      assert(exists l B0 Gl', ctx_step_f Gl p q l B0 Gl').
      {
        clear Hh.
        destruct He as [He | He].
        - inversion He. subst. 
          pinversion Hg; try easy; try mon_easy.
        - inversion He. subst. 
          pinversion Hg; try easy; try mon_easy. subst.
          apply assoc_step_s_to_step_f with xs0; try easy.
          specialize(assoc_wdef_to_step_s p q xs0 Gl); intros.
          apply H2; try easy.
          inversion H4.
          intros. apply H8 with n Gl pt; try easy.
      }
      clear Hta.
      destruct H2 as (l1,(B1,(Gl', Hta))).
      unfold fair_path in H5.
      destruct (H5 n Gl Gl' p q l1 B1 H6 Hta)
        as (k0,(l0,(B0,(G1,(G2,(Hle,(Hst1,(Hst2,Hstep)))))))).
      exists k0. exists l0. exists G1. exists G2. exists B0.
      repeat split; try assumption.
      apply sub_mon.
    - assert((exists (k0 l : fin) (G1 G2 : typ_ctx) (B0 : sort),
        n <= k0 /\
        stnth k0 gxs = Some G1 /\ stnth k0.+1 gxs = Some G2 /\ ctx_step_f G1 p q l B0 G2) \/ 
        (exists k0 G1 G', n <= k0 /\ stnth k0 gxs = Some G1 /\ assoc_gctx G1 G' /\ balancedG G' /\ regGtt G' /\ balanced_with k q G' /\ ctx_step_r G1 q p)).
      {
        clear IHk. 
        pose proof H5 as Ht.
        unfold fair_path in Ht.
        destruct G.
        - specialize(balanced_with_Sk k q gtt_end); intros.
          assert False. apply H0; try easy. easy.
        - assert(ctx_step_s Gl p0 p1).
          {
            specialize(assoc_wdef_to_step_s); intros.
            apply H0 with o; try easy.
            inversion H4.
            intros.
            apply H2 with n Gl pt; try easy.
          }
          specialize(assoc_step_s_to_step_f p0 p1 o Gl Ha H0); intros.
          destruct H1 as (l,(B1,(Gl',He))).
          specialize(Ht n Gl Gl' p0 p1 l B1 H6 He).
          clear He H0. clear Gl' l B1.
          destruct Ht as (m,(l,(B0,(G1,(G2,(He,(Hf,(Hg,Hh)))))))).
          
          revert Hh Hg Hf He Hd Hc Hb Ha H7 H6 H4 H5.
          revert G1 G2 l B0 o Gl k m p q gxs p0 p1.
          induction n; intros.
          - pose proof (assoc_fair_live_n0_r
              m gxs Gl p q p0 p1 o k G1 G2 l (B:=B0)
              H4 H5 H6 H7 Ha Hb Hc Hd Hf Hg Hh) as Hlive.
            destruct Hlive as [Hfuture|Hpending].
            - left. destruct Hfuture as (k0,(l0,(B1,(G3,(G4,(Hle,(Hst1,(Hst2,Hstep)))))))).
              exists k0. exists l0. exists G3. exists G4. exists B1.
              repeat split; try assumption.
            - right. destruct Hpending as (k0,(G3,(G',(Hle,(Hst1,(Hassoc,(Hbal,(Hreg,(Hbw,Hstep))))))))).
              exists k0. exists G3. exists G'.
              split; [exact Hle|]. split; [exact Hst1|]. split; [exact Hassoc|].
              split; [exact Hbal|]. split; [exact Hreg|].
              split; [exact Hbw|exact Hstep].
          - destruct m; try easy. destruct gxs; try easy.
            specialize(IHn G1 G2 l B0 o Gl k m p q gxs p0 p1).
            assert((exists (k0 l : fin) (G1 G2 : typ_ctx) (B1 : sort),
               n <= k0 /\
               stnth k0 gxs = Some G1 /\
               stnth k0.+1 gxs = Some G2 /\ ctx_step_f G1 p q l B1 G2) \/
            (exists (k0 : fin) (G1 : typ_ctx) (G' : gtt),
               n <= k0 /\
               stnth k0 gxs = Some G1 /\
               assoc_gctx G1 G' /\
               balancedG G' /\ regGtt G' /\ balanced_with k q G' /\ ctx_step_r G1 q p)).
            {
              apply IHn; try easy.
              apply wdef_tail with t; try easy.
              apply fair_path_tail with t; try easy.
            }
            destruct H0.
            - left.
              destruct H0 as (k1,(l1,(G3,(G4,(B1,(Hi,(Hj,(Hl,Hm)))))))).
              exists (S k1). exists l1. exists G3. exists G4. exists B1. easy.
            - right.
              destruct H0 as (k1,(G3,(G',Ht))).
              exists (S k1). exists G3. exists G'. easy.
      }
      
      destruct H0; try easy.
      destruct H0 as (k0,(G1,(G',(He,(Hf,(Hg,(Hh,(Hi,(Hj,Hk))))))))).
      specialize(IHk k0 G1 G').
      assert(exists (k l : fin) (G1 G2 : typ_ctx) (B0 : sort),
        k0 <= k /\
        stnth k gxs = Some G1 /\ stnth k.+1 gxs = Some G2 /\ ctx_step_f G1 p q l B0 G2).
      {
        apply IHk; try easy.
      }
      destruct H0 as (k1,(l1,(G2,(G3,(B1,(Hl,(Hn,(Ho,Hp)))))))).
      exists k1. exists l1. exists G2. exists G3. exists B1. split; try easy.
      apply leq_trans with k0; try easy.
Qed.


Lemma is_assoc_to_live_ctx_0 `{good_merge} : forall gxs gtx, stnth 0 gxs = Some gtx -> is_assoc gtx -> live_ctx_0 gxs.
Proof.
  intros.
  unfold live_ctx_0. intros.
  unfold is_assoc in H1. destruct_exists_and.
  apply assoc_fair_live with gtx x; try easy.
Qed.


Theorem ctx_liveness `{good_merge} : forall gtx gtx' gxs, 
  is_assoc gtx -> 
  multi typ_ctx_red gtx gtx' ->
  stnth 0 gxs = Some gtx' -> 
  live_ctx_0 gxs.
Proof.
  intros.
  revert H2 H0. revert gxs.
  induction H1; intros.
  - apply is_assoc_to_live_ctx_0 with x; try easy.
  - specialize(IHmulti gxs H2).
    apply IHmulti.
    clear H2 IHmulti H1. inversion H0. inversion H3. subst.
    destruct_exists_and. clear H0 H3.
    unfold is_assoc.
    destruct (assoc_on x0 x y p q l B H4 H5 H2 H1)
      as (G',(Hassoc_y,(Hstep,Hbal_y))).
    exists G'. split; [exact Hassoc_y|].
    split; [eapply regGtt_after_step; eassumption|exact Hbal_y].
Qed.

End ctx_liveness.
