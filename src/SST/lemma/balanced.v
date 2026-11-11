  From mathcomp Require Import ssreflect.seq all_ssreflect.
Require Import List String Coq.Arith.PeanoNat Coq.Arith.Arith Relations ZArith Datatypes Setoid Morphisms Coq.Logic.Decidable Coq.Program.Basics Coq.Init.Datatypes.
Import ListNotations. 
Open Scope list_scope.
From Paco Require Import paco.
Require Import SST def.session.
Require Import lemma.substitution.

(* Balancedness-oriented lemmas:
   connects path witnesses, participant reachability, and projectability
   properties needed by later liveness/soundness arguments. *)


(* Any path that reaches an interaction node mentioning `p1` witnesses that
   `p1` is a participant of the whole global tree. *)
Lemma word_to_participant : forall G w' p1 q1, gttmap G w' None (gnode_pq p1 q1) \/
     gttmap G w' None (gnode_pq q1 p1) -> isgPartsC p1 G.
Proof.
  intros G w'. revert G.
  induction w'; intros.
  - destruct H.
    inversion H. constructor.
    inversion H. constructor.
  - destruct H.
    - inversion H. subst.
      specialize(IHw' gk p1 q1).
      assert(isgPartsC p1 gk). apply IHw'; try easy. 
      left. easy.
      destruct (participant_dec p1 p).
      - subst. constructor.
      destruct (participant_dec p1 q).
      - subst. constructor.
      apply pac_sendr with a st gk; try easy.
    - inversion H. subst.
      specialize(IHw' gk p1 q1).
      assert(isgPartsC p1 gk). apply IHw'; try easy. 
      right. easy.
      destruct (participant_dec p1 p).
      - subst. constructor.
      destruct (participant_dec p1 q).
      - subst. constructor.
      apply pac_sendr with a st gk; try easy.
Qed.
      

(* Balancedness is inherited by every concrete continuation branch. *)
Lemma balanced_cont : forall p q f, balancedG (gtt_send p q f) -> (forall n, f n = None \/ (exists s g, f n = Some (s, g) /\ balancedG g)).
Proof.
  intros.
  specialize(always_exists (f n)); intros.
  destruct H0 as (x, H0). 
  destruct x.
  - right. destruct p0. exists s. exists g. 
    split; try easy.
    unfold balancedG in *.
    
    intros.
    specialize(H (n :: w) w' p0 q0).
    assert(gttmap (gtt_send p q f) ((n :: w) ++ w') None (gnode_pq p0 q0) \/
      gttmap (gtt_send p q f) ((n :: w) ++ w') None (gnode_pq q0 p0)).
    {
      destruct H1.
      - left.
        apply gmap_con with s g; try easy.
      - right.
        apply gmap_con with s g; try easy.
    }
    specialize(H H2). clear H1 H2.
    destruct H as (k, H). exists k.
    intros.
    specialize(H w'0).
    assert(gttmap (gtt_send p q f) ((n :: w) ++ w'0) None gnode_end \/
      length w'0 = k /\
      (exists tc : gnode, gttmap (gtt_send p q f) ((n :: w) ++ w'0) None tc)).
    {
      destruct H1.
      - left.
        apply gmap_con with s g; try easy.
      - right.
        destruct H1 as (Ha,(tc,Hb)).
        split. easy. exists tc.
        apply gmap_con with s g; try easy.
    }
    specialize(H H2). clear H2 H1.
    destruct H as (w2,(w0,(Ha,(r,Hb)))).
    exists w2. exists w0.
    split; try easy. exists r.
    destruct Hb.
    - left. inversion H. subst.
      rewrite H8 in H0. inversion H0. subst. easy.
    - right. inversion H. subst.
      rewrite H8 in H0. inversion H0. subst. easy.
  - left. easy.
Qed.


Definition projectableA `{good_merge} G := forall pt, exists T, projC G pt T.


(* Projectability is likewise inherited branch-wise. *)
Lemma projectableA_cont `{good_merge} : forall p q f, projectableA (gtt_send p q f) -> (forall n, f n = None \/ exists s g, f n = Some(s, g) /\ projectableA g).
Proof.
  intros.
  specialize(always_exists (f n)); intros.
  destruct H1 as (x,Ha). destruct x.
  - right. destruct p0.
    exists s. exists g. split. easy.
    unfold projectableA in *.
    intros.
    specialize(H0 pt).
    destruct H0 as (T,Hb).
    pinversion Hb; try easy.
    - subst.
      exists ltt_end. pfold. constructor.
      intro. apply H0.
      destruct (participant_dec pt p).
      - subst. constructor.
      destruct (participant_dec pt q).
      - subst. constructor.
        apply pac_sendr with n s g; try easy.
    - subst.
      specialize(H7 n). rewrite Ha in H7.
      destruct H7; try easy.
      destruct H0 as (s1,(g1,(t1,(Hc,(Hd,He))))).
      inversion Hc. subst. exists t1. pclearbot. easy.
    - subst.
      specialize(H7 n). rewrite Ha in H7.
      destruct H7; try easy.
      destruct H0 as (s1,(g1,(t1,(Hc,(Hd,He))))).
      inversion Hc. subst. exists t1. pclearbot. easy.
    - subst.
      specialize(H9 n). rewrite Ha in H9.
      destruct H9; try easy.
      destruct H0 as (s1,(g1,(t1,(Hc,(Hd,He))))).
      inversion Hc. subst. exists t1. pclearbot. easy.
    apply proj_mon.
  - left. easy.
Qed.

Lemma proj_cont_pq_step_shape `{good_merge} : forall G G' p q l, 
    balancedG G -> 
    gttstepC G G' p q l ->
    projectableA G ->
    forall T T', projC G p T -> projC G q T' -> exists f f', T = ltt_send q f /\ T' = ltt_recv p f'.
Proof.
  intros.
  specialize(step_to_htree G H0 G' p q l H1); intros.
  destruct H5 as (Gl,(Ha,Hb)). clear H0. revert H3 H4. revert T T'.
  revert Ha Hb H2 H1.
  revert G G'.
  induction Gl using gtth_ind_ref; intros.
  - inversion Ha.
    - subst. pinversion H1; try easy.
      apply step_mon.
    - subst. pinversion H1; try easy.
      subst.
      pinversion H3; try easy.
      - assert False.
        apply H0. constructor.
        easy.
      subst.
      pinversion H4; try easy.
      - subst. 
        assert False.
        apply H0. constructor.
        easy.
      subst.
      exists f'. exists f'0. easy.
      apply proj_mon.
      apply proj_mon.
      apply step_mon.
    - subst.
      pinversion H1; try easy.
      apply step_mon.
  - inversion Ha. subst. clear Ha.
    pinversion H1; try easy. subst.
    - assert False.
      apply Hb. constructor.
      easy.
    - subst.
      destruct H15 as (n,(pa,Hc)).
      specialize(H20 n). specialize(H21 n). specialize(H10 n). specialize(H0 n). 
      specialize(projectableA_cont p0 q0 ys H2); intros. specialize(H5 n).
      rewrite Hc in H20 H21 H10 H5.
      destruct H21; try easy.
      destruct H6 as (s1,(g1,(g2,(Hd,(He,Hf))))). inversion Hd. subst. clear Hd.
      destruct H10; try easy. destruct H6 as (s2,(g3,(g4,(Hg,(Hh,Hi))))). inversion Hh. subst. clear Hh.
      destruct H5; try easy. destruct H5 as (s3,(g5,(Hj,Hk))). inversion Hj. subst. clear Hj.
      rewrite Hg in H0.
      destruct H0; try easy.
      destruct H0 as (s4,(g6,(Hl,Hm))). inversion Hl. subst. clear Hl.
      specialize(Hm g5 g2).
     
      assert(forall T T' : ltt,
     projC g5 p T ->
     projC g5 q T' ->
     exists f f' : fin -> option (sort * ltt), T = ltt_send q f /\ T' = ltt_recv p f').
      {
        apply Hm; try easy.
        intro.
        apply Hb.
        apply ha_sendr with n s4 g6; try easy.
        destruct Hf; try easy.
      }
      clear Hm.
      
      destruct H20; try easy. destruct H5 as (s5,(g7,(Hn,(Ho,Hp)))). 
      inversion Hn. subst. clear Hn.
      pclearbot.
      
      pinversion H4; try easy.
      - subst.
        assert False. apply H5.
        apply pac_sendr with n s5 g7; try easy. 
        easy.
      subst.
      pinversion H3; try easy.
      - subst.
        assert False. apply H5.
        apply pac_sendr with n s5 g7; try easy.
        easy.
      subst.
      clear H23 H17.
      specialize(H26 n). specialize(H20 n). rewrite Hc in H20 H26.
      destruct H20; try easy. destruct H5 as (s1,(g1,(t1,(Hh,(Hj,Hl))))). inversion Hh. subst. clear Hh.
      destruct H26; try easy. destruct H5 as (s2,(g3,(t2,(Hm,(Hn,Hq))))). inversion Hm. subst. clear Hm.
      pclearbot.
      specialize(H0 t2 t1 Hq Hl).
      destruct H0 as (fa,(fb,(Hta,Htb))). subst.
      clear Hq Hl.
      specialize(isMerge_to_Into f'0 T' n (ltt_recv p fb) H21 Hj); intros.
      specialize(isMerge_to_Into f'1 T n (ltt_send q fa) H27 Hn); intros.
      specialize(MergeInto_to_subtypeC T (ltt_send q fa) H5); intros.
      specialize(MergeInto_to_subtypeC T' (ltt_recv p fb) H0); intros.
      pinversion H6. pinversion H7.
      exists xs0. exists xs1. easy.
      apply sub_mon.
      apply sub_mon.
      apply proj_mon.
      apply proj_mon.
      apply step_mon.
Qed.
  
 
Lemma proj_cont_pq_step_full `{good_merge} : forall G G' p q l,
    balancedG G -> 
    regGtt G ->
    gttstepC G G' p q l ->
    projectableA G -> 
    projectableA G'.
Proof.
  intros.
  specialize(proj_cont_pq_step_shape G G' p q l H0 H2 H3); intros.
  unfold projectableA in *. intro.
  pose proof H3 as Ht. pose proof Ht as Hr.
  specialize(H3 p). destruct H3 as (T,Ha). 
  specialize(Ht q). destruct Ht as (T',Hb).
  specialize(H4 T T' Ha Hb).
  destruct H4 as (f,(f',(Hc,Hd))). subst.
  specialize(typ_after_step_p G G' p q l f H0 H1 H2 Ha); intros.
  destruct H3 as (sa,(ta,(Hc,Hd))).
  specialize(typ_after_step_q G G' p q l f' H0 H1 H2 Hb); intros.
  destruct H3 as (sb,(tb,(He,Hf))).
  destruct (participant_dec pt p).
  - subst. eexists; eauto.
  destruct (participant_dec pt q).
  - subst. eexists; eauto.
  - specialize(Hr pt). destruct Hr as (T1,Hs).
    specialize(typ_after_step_r G G' p q pt l T1); intros.
    assert(exists T' : ltt, projC G' pt T' /\ subtypeC T1 T').
    apply H3; try easy.
    destruct H4 as (T',(Hta,Htb)).
    exists T'. easy.
Qed.

Definition balanced_with k pt G :=
    forall w'0 : seq.seq fin,
      gttmap G w'0 None gnode_end \/
      length w'0 = k /\ (exists tc : gnode, gttmap G w'0 None tc) ->
      exists w2 w0 : seq.seq fin,
        w'0 = w2 ++ w0 /\
        (exists r,
           gttmap G w2 None (gnode_pq pt r) \/
           gttmap G w2 None (gnode_pq r pt)).

Lemma part_with_balanced_k : forall pt G, isgPartsC pt G -> balancedG G -> exists k, balanced_with k pt G.
Proof.
  intros.
  unfold balancedG in *.
  specialize(isgPartsC_to_word pt G H); intros.
  destruct H1 as (w,(pr,Ha)).
  specialize(H0 nil w pt pr Ha). simpl in *. 
  unfold balanced_with. easy.
Qed.



Lemma split_word {A} : forall (w : list A) m, m <= (length w) -> exists w' w'', w = w' ++ w'' /\ length w' = m.
Proof.
  induction w; intros.
  - destruct m; try easy.
    exists nil. exists nil. easy.
  - destruct m; try easy.
    exists nil. exists (a :: w). easy.
    specialize(IHw m H). destruct IHw as (w1,(w2,(Ha,Hb))).
    exists (a :: w1). exists w2. subst. easy.
Qed.

Lemma balanced_with_more : forall k m pt G, balanced_with k pt G -> (k <= m) -> balanced_with m pt G.
Proof.
  intros.
  unfold balanced_with in *.
  intros.
  destruct H1.
  - specialize(H w'0).
    apply H. left. easy.
  - destruct H1 as (Ha,(tc,Hb)).
    subst.
    specialize(split_word w'0 k H0); intros. destruct H1 as (w1,(w2,(Hd,He))).
    subst.
    specialize(H w1).
    clear H0.
    assert(exists w2 w0 : seq.seq fin,
      w1 = w2 ++ w0 /\
      (exists r, gttmap G w2 None (gnode_pq pt r) \/ gttmap G w2 None (gnode_pq r pt))).
    {
      apply H.
      right. split. easy. clear H. revert Hb.
      revert G tc.
      induction w1; intros.
      - destruct G.
        - exists gnode_end. constructor.
        - exists (gnode_pq p p0). constructor.
      - inversion Hb. subst. 
        specialize(IHw1 gk tc H5). destruct IHw1.
        exists x. apply gmap_con with st gk; try easy.
    }
    destruct H0 as (wa,(wb,(Hc,Hd))).
    subst. exists wa. exists (wb ++ w2).
    split. apply esym. apply app_assoc.
    easy.
Qed.

Lemma balanced_with_nil : forall pt G, balanced_with 0 pt G -> (exists r ,
          gttmap G nil None (gnode_pq pt r) \/ gttmap G nil None (gnode_pq r pt)).
Proof.
  intros.
  unfold balanced_with in H.
  specialize(H nil).
  assert(exists w2 w0 : seq.seq fin,
      [] = w2 ++ w0 /\
      (exists r ,
         gttmap G w2 None (gnode_pq pt r) \/ gttmap G w2 None (gnode_pq r pt))).
  {
    apply H.
    right. split. easy.
    destruct G.
    - exists gnode_end. constructor.
    - exists (gnode_pq p p0). constructor.
  }
  destruct H0 as (w2,(w0,(Ha,Hb))). 
  destruct w2; try easy.
Qed.
  
Lemma balanced_with_0_l : forall pt r f', balanced_with 0 pt (gtt_send pt r f').
Proof.
  intros.
  unfold balanced_with. intros.
  destruct H.
  - exists nil. exists w'0. 
    split. easy.
    exists r. left. constructor.
  - destruct H as (Ha, (tc, Hb)).
    destruct w'0; try easy. exists nil. exists nil.
    split. easy. exists r. left. constructor.
Qed.

Lemma balanced_with_0_r : forall pt r f', balanced_with 0 pt (gtt_send r pt f').
Proof.
  intros.
  unfold balanced_with. intros.
  destruct H.
  - exists nil. exists w'0. 
    split. easy.
    exists r. right. constructor.
  - destruct H as (Ha, (tc, Hb)).
    destruct w'0; try easy. exists nil. exists nil.
    split. easy. exists r. right. constructor.
Qed.

Lemma balanced_with_Sk : forall k p G, balanced_with k.+1 p G -> G = gtt_end -> False.
Proof.
  intros.
  specialize(H nil). subst.
  assert(exists w2 w0 : seq.seq fin,
      [] = w2 ++ w0 /\
      (exists r ,
         gttmap gtt_end w2 None (gnode_pq p r) \/ gttmap gtt_end w2 None (gnode_pq r p))).
  apply H. left. constructor. clear H.
  destruct H0 as (w2,(w0,(Ha,(r,Hb)))).
  destruct w2; try easy. destruct w0; try easy.
  destruct Hb.
  - inversion H.
  - inversion H.
Qed.



Lemma balanced_k_up_s : forall f' k pt r s,
      (forall n : fin,
          f' n = None \/
          (exists (s : sort) (g' : gtt), f' n = Some (s, g') /\ balanced_with k pt g')) -> 
      balanced_with k.+1 pt (gtt_send r s f').
Proof.
  intros.
  unfold balanced_with in *.
  intros.
  destruct w'0.
  - destruct H0.
    - inversion H0.
    - destruct H0. easy.
  - specialize(H n).
    destruct H.
    - destruct H0.
      - inversion H0. subst. rewrite H in H8. easy.
      - destruct H0 as (Ha,(tc,Hb)).
        inversion Hb. subst. rewrite H in H7. easy.
    - destruct H as (s1,(g,(Ha,Hb))).
      specialize(Hb w'0).
      assert(exists w2 w0 : seq.seq fin,
       w'0 = w2 ++ w0 /\
       (exists r ,
          gttmap g w2 None (gnode_pq pt r) \/ gttmap g w2 None (gnode_pq r pt))).
      {
        apply Hb.
        destruct H0.
        - left. inversion H. subst.
          rewrite Ha in H7. inversion H7. subst. easy.
        - destruct H as (Hc,(tc,Hd)).
          right. inversion Hd. subst. 
          rewrite H6 in Ha. inversion Ha. subst. 
          split. inversion Hc. easy.
          exists tc. easy.
      }
      clear H0 Hb.
      destruct H as (w2,(w0,(Hb,(r1,Hc)))). subst.
      exists (n :: w2). exists w0. split. easy. exists r1.
      destruct Hc.
      - left. apply gmap_con with s1 g; try easy.
      - right. apply gmap_con with s1 g; try easy.
Qed.

Lemma balanced_k_cont : forall k pt p q f l s G',
        balanced_with k.+1 pt (gtt_send p q f) 
        -> pt <> p -> pt <> q 
        -> f l = Some (s, G') 
        -> balanced_with k pt G'.
Proof.
  intros.
  unfold balanced_with in *.
  intros.
  specialize(H (l :: w'0)).
  assert(exists w2 w0 : seq.seq fin,
      l :: w'0 = w2 ++ w0 /\
      (exists r ,
         gttmap (gtt_send p q f) w2 None (gnode_pq pt r) \/
         gttmap (gtt_send p q f) w2 None (gnode_pq r pt))).
  {
    apply H.
    destruct H3.
    - left. apply gmap_con with s G'; try easy.
    - destruct H3 as (Ha, (tc, Hb)).
      right. split. simpl.
      apply eq_S. easy.
      exists tc. apply gmap_con with s G'; try easy.
  }
  clear H3. rename H2 into Ht.
  destruct H4 as (w2,(w0,(Ha,(r,Hb)))).
  destruct w2; try easy.
  - destruct Hb. 
    inversion H2. subst. easy.
    inversion H2. subst. easy.
  - inversion Ha. subst.
    exists w2. exists w0. split. easy. exists r.
    destruct Hb.
    - left. inversion H2. subst. 
      rewrite H10 in Ht. inversion Ht. subst. easy.
    - right. inversion H2. subst.
      rewrite H10 in Ht. inversion Ht. subst. easy.    
Qed.

Lemma step_balanced_with : forall k G G' p q pt l, gttstepC G G' p q l -> balanced_with k pt G -> balanced_with k pt G' \/ pt = p \/ pt = q.
Proof.
  induction k; intros.
  - specialize(balanced_with_nil pt G H0); intros.
    destruct H1 as (r, Ha).
    destruct Ha.
    - inversion H1. subst.
      pinversion H; try easy.
      - subst. right. left. easy.
      - subst. left.
        apply balanced_with_0_l.
      apply step_mon.
    - inversion H1. subst.
      pinversion H; try easy.
      - subst. right. right. easy.
      - subst. left.
        apply balanced_with_0_r.
      apply step_mon.
  - pinversion H; try easy.
    - subst.
      specialize(participant_dec pt p); intros. destruct H3.
      - right. left. easy.
      specialize(participant_dec pt q); intros. destruct H3.
      - right. right. easy.
      rename H into Hta. rename H0 into Htb.
      left.
      specialize(balanced_with_more k k.+1 pt G'); intros.
      apply H; try easy.
      apply balanced_k_cont with p q f l s; try easy.
    - subst.
      specialize(participant_dec pt r); intros. destruct H10.
      - subst. left.
        apply balanced_with_more with 0; try easy. apply balanced_with_0_l.
      specialize(participant_dec pt s); intros. destruct H10.
      - subst. left.  
        apply balanced_with_more with 0; try easy. apply balanced_with_0_r.
      rename H8 into Hta. rename H9 into Htb.
      assert(pt = p \/ pt = q \/ (
        forall n : fin,
         f' n = None \/
         (exists (s : sort) (g' : gtt),
            f' n = Some (s, g') /\ balanced_with k pt g')
      )).
      {
        specialize(participant_dec pt p); intros. destruct H8. left. easy.
        specialize(participant_dec pt q); intros. destruct H8. right. left. easy.
        right. right.
        intro. clear H7 H.
        specialize(Htb n3). 
        destruct Htb.
        - left. easy.
        - destruct H as (s1, (g, (g', (Hc, (Hd, He))))).
        rewrite Hd. right. exists s1. exists g'. split. easy.
        specialize(IHk g g' p q pt l).
        assert(balanced_with k pt g' \/ pt = p \/ pt = q).
        {
          pclearbot.
          apply IHk; try easy.
          apply balanced_k_cont with r s f n3 s1; try easy.
        }
        destruct H; try easy. destruct H; try easy.
      }
      
      destruct H8. right. left. easy. 
      destruct H8. right. right. easy.
      clear Hta Htb H7. left.
      apply balanced_k_up_s; try easy.
    apply step_mon.
Qed.

Lemma balanced_k_up : forall n p q pt f, (forall n, f n = None \/ (exists s g, f n = Some(s, g) /\ exists k, balanced_with k pt g)) -> (forall m, n <= m -> f m = None) -> exists k, balanced_with k pt (gtt_send p q f).
Proof.
  induction n; intros.
  - exists 1.
    unfold balanced_with. intros.
    destruct H1.
    - inversion H1.
      subst. specialize(H0 n).
      assert(f n = None). apply H0; try easy.
      rewrite H2 in H8. easy.
    - destruct H1 as (Ha,(tc,Hb)).
      inversion Hb; subst; try easy.
      specialize(H0 n).
      assert(f n = None). apply H0; try easy.
      rewrite H1 in H7. easy.
  - specialize(IHn p q pt (fun n => f (S n))).
    assert(exists k : fin, balanced_with k pt (gtt_send p q (fun n : fin => f n.+1))).
    {
      apply IHn; try easy.
      intros. specialize(H0 (S m) H1). easy.
    }
    clear IHn.
    destruct H1 as (k,Ha). clear H0.
    specialize(H 0).
    destruct H.
    
    - exists (S k).
      unfold balanced_with.
      intros.
      destruct w'0.
      - destruct H0. inversion H0.
        destruct H0 as (Hb,(tc,Hc)). destruct k; try easy.
      destruct n0.
      - destruct H0.
        - inversion H0. subst. rewrite H in H8. easy.
        - destruct H0 as (Hb,(tc,Hc)).
          inversion Hc. subst. rewrite H in H7. easy.
      - specialize(balanced_with_more k (S k) pt (gtt_send p q (fun n : fin => f n.+1)) Ha); intros.
        assert(balanced_with k.+1 pt (gtt_send p q (fun n : fin => f n.+1))).
        apply H1; try easy. clear H1 Ha. unfold balanced_with in H2.
        specialize(H2 (n0 :: w'0)).
        assert(gttmap (gtt_send p q (fun n : fin => f n.+1)) (n0 :: w'0) None gnode_end \/
     length (n0 :: w'0) = k.+1 /\
     (exists tc : gnode, gttmap (gtt_send p q (fun n : fin => f n.+1)) (n0 :: w'0) None tc)).
        {
          destruct H0.
          - left. inversion H0. subst.
            apply gmap_con with st gk; try easy.
          - destruct H0 as (Hb,(tc,Hc)).
            right. split. easy.
            exists tc.
            inversion Hc. subst.
            apply gmap_con with st gk; try easy.
        }
        specialize(H2 H1). clear H1 H0.
        destruct H2 as (w1,(w2,(Ha,(r,Hb)))). 
        destruct w1.
        - exists nil. exists (n0.+1 :: w'0). split. easy.
          exists r.
          destruct Hb. 
          - inversion H0. subst. left. constructor.
          - inversion H0. subst. right. constructor.
        - inversion Ha. subst. 
          exists (n1.+1 :: w1). exists w2.
          split. simpl in *. easy.
          exists r.
          destruct Hb.
          - left. inversion H0. subst. apply gmap_con with st gk; try easy.
          - right. inversion H0. subst. apply gmap_con with st gk; try easy.
    - destruct H as (s1,(g1,(Hb,(k1,Hc)))).
    
      destruct k.
      - exists (S k1).
        specialize(balanced_with_more 0 k1.+1 pt (gtt_send p q (fun n : fin => f n.+1))); intros.
        assert(balanced_with k1.+1 pt (gtt_send p q (fun n : fin => f n.+1))).
        apply H; try easy. clear H Ha.
        unfold balanced_with in *.
        intros.
        destruct H.
        - destruct w'0; try easy.
          inversion H. subst. clear H.
          destruct n0. 
          - rewrite H8 in Hb. inversion Hb. subst. clear Hb.
            specialize(Hc w'0).
            assert(exists w2 w0 : seq.seq fin,
             w'0 = w2 ++ w0 /\
             (exists r , gttmap g1 w2 None (gnode_pq pt r) \/ gttmap g1 w2 None (gnode_pq r pt))).
            {
              apply Hc.
              left. easy.
            }
            destruct H as (w1,(w2,(Hd,(r,He)))). subst.
            exists (0 :: w1). exists w2.
            split. easy. exists r.
            destruct He.
            - left. apply gmap_con with s1 g1; try easy.
            - right. apply gmap_con with s1 g1; try easy.
          - specialize(H0 (n0 :: w'0)).
            assert(exists w2 w0 : seq.seq fin,
               n0 :: w'0 = w2 ++ w0 /\
               (exists r ,
                  gttmap (gtt_send p q (fun n : fin => f n.+1)) w2 None (gnode_pq pt r) \/
                  gttmap (gtt_send p q (fun n : fin => f n.+1)) w2 None (gnode_pq r pt))).
            {
              apply H0.
              left. apply gmap_con with st gk; try easy.
            }
            destruct H as (w1,(w2,(Hd,(r,He)))).
            destruct w1.
            - exists nil. exists (n0.+1 :: w'0).
              split. easy. exists r.
              destruct He.
              - left. inversion H. subst. constructor.
              - right. inversion H. subst. constructor.
            - inversion Hd. subst.
              exists (n1.+1 :: w1). exists w2.
              split. easy. exists r.
              destruct He.
              - left. inversion H. subst. apply gmap_con with st0 gk0; try easy.
              - right. inversion H. subst. apply gmap_con with st0 gk0; try easy.
        - destruct H as (Ha,(tc,Hd)). destruct w'0; try easy. simpl in *. inversion Ha. clear Ha.
          destruct n0.
          - specialize(Hc w'0).
            assert(exists w2 w0 : seq.seq fin,
             w'0 = w2 ++ w0 /\
             (exists r , gttmap g1 w2 None (gnode_pq pt r) \/ gttmap g1 w2 None (gnode_pq r pt))).
            {
              apply Hc. 
              right. split. easy.
              exists tc. inversion Hd. subst. rewrite Hb in H8. inversion H8. easy.
            } 
            destruct H as (w1,(w2,(He,(r,Hf)))). subst.
            exists (0 :: w1). exists w2. split. easy. exists r.
            destruct Hf.
            - left. apply gmap_con with s1 g1; try easy.
            - right. apply gmap_con with s1 g1; try easy.
          - specialize(H0 (n0 :: w'0)).
            assert(exists w2 w0 : seq.seq fin,
             n0 :: w'0 = w2 ++ w0 /\
             (exists r ,
                gttmap (gtt_send p q (fun n : fin => f n.+1)) w2 None (gnode_pq pt r) \/
                gttmap (gtt_send p q (fun n : fin => f n.+1)) w2 None (gnode_pq r pt))).
            {
              apply H0; try easy.
              right. split. simpl. rewrite H1. easy.
              exists tc. inversion Hd. subst.
              apply gmap_con with st gk; try easy.
            }
            destruct H as (w1,(w2,(He,(r,Hf)))). 
            destruct w1.
            - exists nil. exists (n0.+1 :: w'0).
              split. easy. exists r.
              destruct Hf.
              - left. inversion H. subst. constructor.
              - right. inversion H. subst. constructor.
            - inversion He. subst.
              exists (n1.+1 :: w1). exists w2.
              split. easy. exists r.
              destruct Hf.
              - inversion H. subst. left. apply gmap_con with st gk; try easy.
              - inversion H. subst. right. apply gmap_con with st gk; try easy.
      - exists (S (Nat.max k1 k)).
        specialize(balanced_with_more k1 (Nat.max k1 k) pt g1 Hc (max_l k1 k)); intros. clear Hc.
        specialize(balanced_with_more k.+1 (Nat.max k1 k).+1 pt (gtt_send p q (fun n : fin => f n.+1))); intros.
        assert(balanced_with (Nat.max k1 k).+1 pt (gtt_send p q (fun n : fin => f n.+1))).
        {
          apply H0; try easy.
          apply max_r.
        }
        clear H0 Ha.
        specialize(always_exists (Nat.max k1 k)); intros. destruct H0. rewrite H0.
        rewrite H0 in H1 H. clear H0. clear k k1. rename x into k1. rename H into Hc. rename H1 into H0.
         
        
        unfold balanced_with in *.
        intros.
        destruct H.
        - destruct w'0; try easy.
          inversion H. subst. clear H.
          destruct n0. 
          - rewrite H8 in Hb. inversion Hb. subst. clear Hb.
            specialize(Hc w'0).
            assert(exists w2 w0 : seq.seq fin,
             w'0 = w2 ++ w0 /\
             (exists r , gttmap g1 w2 None (gnode_pq pt r) \/ gttmap g1 w2 None (gnode_pq r pt))).
            {
              apply Hc.
              left. easy.
            }
            destruct H as (w1,(w2,(Hd,(r,He)))). subst.
            exists (0 :: w1). exists w2.
            split. easy. exists r.
            destruct He.
            - left. apply gmap_con with s1 g1; try easy.
            - right. apply gmap_con with s1 g1; try easy.
          - specialize(H0 (n0 :: w'0)).
            assert(exists w2 w0 : seq.seq fin,
               n0 :: w'0 = w2 ++ w0 /\
               (exists r ,
                  gttmap (gtt_send p q (fun n : fin => f n.+1)) w2 None (gnode_pq pt r) \/
                  gttmap (gtt_send p q (fun n : fin => f n.+1)) w2 None (gnode_pq r pt))).
            {
              apply H0.
              left. apply gmap_con with st gk; try easy.
            }
            destruct H as (w1,(w2,(Hd,(r,He)))).
            destruct w1.
            - exists nil. exists (n0.+1 :: w'0).
              split. easy. exists r.
              destruct He.
              - left. inversion H. subst. constructor.
              - right. inversion H. subst. constructor.
            - inversion Hd. subst.
              exists (n1.+1 :: w1). exists w2.
              split. easy. exists r.
              destruct He.
              - left. inversion H. subst. apply gmap_con with st0 gk0; try easy.
              - right. inversion H. subst. apply gmap_con with st0 gk0; try easy.
        - destruct H as (Ha,(tc,Hd)). destruct w'0; try easy. simpl in *. inversion Ha. clear Ha.
          destruct n0.
          - specialize(Hc w'0).
            assert(exists w2 w0 : seq.seq fin,
             w'0 = w2 ++ w0 /\
             (exists r , gttmap g1 w2 None (gnode_pq pt r) \/ gttmap g1 w2 None (gnode_pq r pt))).
            {
              apply Hc. 
              right. split. easy.
              exists tc. inversion Hd. subst. rewrite Hb in H8. inversion H8. easy.
            } 
            destruct H as (w1,(w2,(He,(r,Hf)))). subst.
            exists (0 :: w1). exists w2. split. easy. exists r.
            destruct Hf.
            - left. apply gmap_con with s1 g1; try easy.
            - right. apply gmap_con with s1 g1; try easy.
          - specialize(H0 (n0 :: w'0)).
            assert(exists w2 w0 : seq.seq fin,
             n0 :: w'0 = w2 ++ w0 /\
             (exists r ,
                gttmap (gtt_send p q (fun n : fin => f n.+1)) w2 None (gnode_pq pt r) \/
                gttmap (gtt_send p q (fun n : fin => f n.+1)) w2 None (gnode_pq r pt))).
            {
              apply H0; try easy.
              right. split. simpl. rewrite H1. easy.
              exists tc. inversion Hd. subst.
              apply gmap_con with st gk; try easy.
            }
            destruct H as (w1,(w2,(He,(r,Hf)))). 
            destruct w1.
            - exists nil. exists (n0.+1 :: w'0).
              split. easy. exists r.
              destruct Hf.
              - left. inversion H. subst. constructor.
              - right. inversion H. subst. constructor.
            - inversion He. subst.
              exists (n1.+1 :: w1). exists w2.
              split. easy. exists r.
              destruct Hf.
              - inversion H. subst. left. apply gmap_con with st gk; try easy.
              - inversion H. subst. right. apply gmap_con with st gk; try easy.
Qed.

Lemma balanced_step `{good_merge} : forall G G' p q l,
    balancedG G -> 
    regGtt G -> 
    gttstepC G G' p q l -> 
    projectableA G ->
    balancedG G'.
Proof.
  intros.
  specialize(step_to_htree G H0 G' p q l H2); intros.
  destruct H4 as (Gl,(Ha,Hb)). 
  revert H0 H1 H2 H3 Ha Hb. revert G G'.
  induction Gl using gtth_ind_ref; intros.
  - inversion Ha.
    - subst.
      pinversion H2; try easy.
      apply step_mon.
    - subst.
      pinversion H2; try easy. 
      subst.
      specialize(balanced_cont p q f H0); intros.
      specialize(H4 l). rewrite H12 in H4.
      destruct H4; try easy. destruct H4 as (s1,(g1,(Hc,Hd))). inversion Hc. subst. easy.
      apply step_mon.
    - subst.
      pinversion H2; try easy.
      apply step_mon.
  - inversion Ha. subst. clear Ha.
    specialize(proj_cont_pq_step_full (gtt_send p0 q0 ys) G' p q l H1 H2 H3 H4); intros.
    pinversion H3; try easy.
    - subst.
      assert False.
      apply Hb. constructor.
      easy.
    subst. clear H15.
    specialize(regGtt_cont p0 q0 ys H2); intros.
    specialize(balanced_cont p0 q0 ys H1); intros.
    specialize(projectableA_cont p0 q0 ys H4); intros. 
    clear H4 H16. rename H1 into Hta. rename H2 into Htb. rename H3 into Htc.
    assert(forall n, f' n = None \/ (exists s g, f' n = Some(s, g) /\ balancedG g)).
    {
      intros.
      specialize(H8 n). specialize(H7 n). specialize(H6 n). specialize(H22 n). 
      specialize(H10 n). specialize(H0 n).
      destruct H22.
      left. easy.
      destruct H1 as (s1,(g1,(g2,(He,(Hf,Hg))))). rewrite He in H6 H7 H8 H10.
      right. exists s1. exists g2. split. easy.
      destruct H6; try easy. destruct H1 as (s2,(g3,(Hh,Hi))). inversion Hh. subst.
      destruct H7; try easy. destruct H1 as (s3,(g4,(Hj,Hk))). inversion Hj. subst.
      destruct H8; try easy. destruct H1 as (s4,(g5,(Hl,Hm))). inversion Hl. subst.
      destruct H10; try easy. destruct H1 as (s5,(g6,(g7,(Ho,(Hp,Hq))))). inversion Hp. subst.
      rewrite Ho in H0.
      destruct H0; try easy.
      destruct H0 as (s6,(g8,(Hr,Hs))). inversion Hr. subst.
      specialize(Hs g7 g2).
      pclearbot. apply Hs; try easy.
      intro. apply Hb.
      apply ha_sendr with n s6 g8; try easy.
    }
    clear H8 H7 H6 H22 H10 H0.
    clear Hb.
    specialize(regGtt_after_step (gtt_send p0 q0 ys) Htb Hta (gtt_send p0 q0 f') p q l); intros.
    assert(regGtt (gtt_send p0 q0 f')). apply H0. pfold. easy. rename H2 into Htd.
    
    unfold balancedG.
    intros.
    destruct w.
    - simpl in *. 
      specialize(regGtt_fin_cont p0 q0 f' Htd); intros.
      destruct H3 as (n,H3).
      clear H0.
      assert(exists k, balanced_with k p1 (gtt_send p0 q0 f')).
      {
        clear Hta Htb Htc.
        clear H9 H11 H12 H13 H14.
        destruct (participant_dec p1 p0); intros.
        - subst.
          exists 0. unfold balanced_with.
          intros. exists nil. exists w'0. split. easy. exists q0. left. constructor.
         destruct (participant_dec p1 q0); intros.
        - subst.
          exists 0. unfold balanced_with.
          intros. exists nil. exists w'0. split. easy. exists p0. right. constructor.
        
        apply balanced_k_up with n; try easy.
        intro.
        specialize(H1 n2). destruct H1. left. easy.
        destruct H0 as (s1,(g1,(Ha,Hb))). right. rewrite Ha.
        exists s1. exists g1. split. easy.
        apply part_with_balanced_k; try easy.
        
        unfold projectableA in H5. specialize(H5 p1).
        destruct H5 as (T,Hta).
        
        specialize(word_to_participant (gtt_send p0 q0 f') w' p1 q1 H2); intros.
        clear H2 H3 Hb H21.
        clear p q l xs ys w' q1 n.
        
        pinversion Hta; subst; try easy.
        
        specialize(H10 n2). rewrite Ha in H10.
        destruct H10; try easy. destruct H1 as (s2,(g2,(t1,(Hb,(Hc,Hd))))). 
        inversion Hb. subst. clear Hb. 
        pclearbot.
        pinversion Hd; try easy. subst.
        specialize(Skip_merge_from_end f'0 n2 T H11 Hc); intros. subst.
        specialize(pmergeCR isMerge Skip_merge_cont_end (gtt_send p0 q0 f') p1); intros.
        assert False. apply H2; try easy. pfold. easy.
        easy.
        apply proj_mon.
        apply proj_mon.
      }
      easy.
    - specialize(H1 n).
      assert(exists p, f' n = Some p).
      {
        destruct H2. inversion H2. subst.
        exists (st, gk). easy.
        inversion H2. subst.
        exists (st, gk). easy.
      } 
      destruct H3 as (pa, H3). rewrite H3 in H1.
      destruct H1; try easy. destruct H1 as (s1,(g1,(He,Hf))).
      inversion He. subst. clear He.
      unfold balancedG in Hf.
      specialize(Hf w w' p1 q1).
      assert(gttmap g1 (w ++ w') None (gnode_pq p1 q1) \/ gttmap g1 (w ++ w') None (gnode_pq q1 p1)).
      {
        destruct H2.
        - left. inversion H1; subst; try easy. rewrite H16 in H3. inversion H3. subst. easy.
        - right. inversion H1; subst; try easy. rewrite H16 in H3. inversion H3. subst. easy.
      }
      specialize(Hf H1). clear H1 H0.
      destruct Hf as (k,Hf).
      exists k. intros.
      specialize(Hf w'0).
      assert(gttmap g1 (w ++ w'0) None gnode_end \/
       length w'0 = k /\ (exists tc : gnode, gttmap g1 (w ++ w'0) None tc)).
      {
        destruct H0.
        - left. inversion H0. subst. rewrite H16 in H3. inversion H3. subst. easy.
        - right. destruct H0 as (Hg,(tc,Hh)). inversion Hh. subst. rewrite H15 in H3.
          inversion H3. subst.
          split. easy. exists tc. easy.
      }
      specialize(Hf H1). clear H0 H1.
      destruct Hf as (w2,(w0,(Ha,(r,Hb)))).
      exists w2. exists w0. subst.
      split. easy. exists r.
      destruct Hb.
      - left. apply gmap_con with s1 g1; try easy.
      - right. apply gmap_con with s1 g1; try easy.
      apply step_mon.
Qed.


Lemma balanced_up : forall p q f,
        (forall n, f n = None \/ (exists s g, f n = Some(s, g) /\ balancedG g)) -> 
        regGtt (gtt_send p q f) -> 
        (forall pt, isgPartsC pt (gtt_send p q f) -> isgPartsCS pt (gtt_send p q f)) ->
        balancedG (gtt_send p q f).
Proof.
  intros.
  specialize(balanced_k_up); intros. 
  unfold balancedG.
  intros.
  destruct w.
  - simpl in *.
    destruct w'.
    - exists 0. intros.
      exists nil. exists w'. split. easy. exists q0. easy.
    - specialize(word_to_participant (gtt_send p q f) (n :: w') p0 q0 H3); intros.
      inversion H4; subst.
      - exists 0. intros.
        exists nil. exists w'0. split. easy. exists q. left. constructor.
      - exists 0. intros.
        exists nil. exists w'0. split. easy. exists p. right. constructor.
      subst.
      specialize(regGtt_fin_cont p q f); intros. fill_triv. destruct H5 as (n1,H5).
      apply H2 with n1; try easy.
      intros. specialize(H n2).
      destruct H; [left; easy | destruct_exists_and; right].
      rewrite H. eexists. eexists. split. easy.
      specialize(H1 p0). fill_triv. inversion H1; subst; try easy. clear H15 H16.
      specialize(H17 n2). rewrite H in H17. destruct H17; try easy. 
      destruct_exists_and. invert_all_some.
      apply part_with_balanced_k; try easy.
      specialize(regGtt_cont p q f); intros. fill_triv. 
      specialize(H7 n2). rewrite H in H7. destruct H7; try easy. destruct_exists_and.
      invert_all_some.
      apply isgPartsCS_back; try easy.
  - specialize(H n).
    assert(exists t, f n = Some t).
    {
      destruct H3 as [H3 | H3]; inversion H3; subst; try easy.
      rewrite H11. eexists. easy.
      rewrite H11. eexists. easy.
    }
    destruct H4. rewrite H4 in H. destruct H; try easy. destruct_exists_and.
    invert_all_some.
    clear H1 H2.
    assert(gttmap x1 (w ++ w') None (gnode_pq p0 q0) \/
           gttmap x1 (w ++ w') None (gnode_pq q0 p0)).
    {
      destruct H3 as [H3 | H3]; inversion H3; subst.
      - left. rewrite H10 in H4. invert_all_some. easy.
      - right. rewrite H10 in H4. invert_all_some. easy.
    }
    clear H3.
    unfold balancedG in H5.
    specialize(H5 w w' p0 q0). fill_triv. destruct H5 as (k, H5).
    exists k. intros.
    specialize(H5 w'0).
    assert_concl_of H5 as Ht.
    {
      apply H5; try easy.
      destruct H1.
      - left. inversion H1. subst. rewrite H11 in H4. invert_all_some. easy.
      - right. destruct_exists_and. split. easy. 
        inversion H2. subst. rewrite H12 in H4. invert_all_some. exists x. easy.
    }
    destruct_exists_and.
    exists x. exists x2. split. easy. subst.
    exists x3.
    destruct H3.
    - left. apply gmap_con with x0 x1; try easy.
    - right. apply gmap_con with x0 x1; try easy.
  Qed.

  
