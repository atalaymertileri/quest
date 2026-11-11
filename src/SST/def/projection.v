From mathcomp Require Import ssreflect.seq all_ssreflect.
Require Import List String Coq.Arith.PeanoNat Coq.Arith.Arith Relations ZArith Datatypes Setoid Morphisms Coq.Logic.Decidable Coq.Program.Basics Coq.Init.Datatypes.
Import ListNotations. 
Open Scope list_scope.
From Paco Require Import paco.
Require Import def.header def.tree  def.global def.local def.part.

(* Projection and reduction interface:
   - global communication steps (`gttstep`)
   - projection relation from global trees to local trees
   - preservation/connectivity lemmas between both views. *)



  
Lemma isgPartsC_to_word : forall pt G, isgPartsC pt G -> exists w pr, gttmap G w None (gnode_pq pt pr) \/ gttmap G w None (gnode_pq pr pt).
Proof.
  intros.
  induction H; intros.
  - exists nil.
    exists q. 
    left. constructor.
  - exists nil.
    exists p.
    right. constructor.
  - destruct IHisgPartsC as (w,(pr,Ha)).
    exists (n :: w). exists pr.
    destruct Ha.
    - left. apply gmap_con with (st := s) (gk := g); try easy.
    - right. apply gmap_con with (st := s) (gk := g); try easy.
Qed.

Section gprojstep.

Section step.

(* One communication step in a global tree:
   - `steq` consumes an interaction at the root.
   - `stneq` propagates the step through unrelated branches. *)
Variant gttstep (R: gtt -> gtt -> participant -> participant -> nat -> Prop): gtt -> gtt -> participant -> participant -> nat -> Prop :=
  | steq : forall p q f s gc n,
                  p <> q ->
                  f n = Some (s, gc) ->
                  gttstep R (gtt_send p q f) gc p q n
  | stneq: forall p q r s f f' l,
                  p <> q ->
                  r <> s ->
                  r <> p ->
                  r <> q ->
                  s <> p ->
                  s <> q ->
                  (exists n p, f n = Some p) ->
                  (forall n, f n = None \/ (exists s g, f n = Some(s, g) /\ isgPartsC p g /\ isgPartsC q g)) ->
                  (forall n, (f n = None /\ f' n = None) \/ (exists s g g', f n = Some(s, g) /\ f' n = Some(s, g') /\ R g g' p q l)) ->
                  gttstep R (gtt_send r s f) (gtt_send r s f') p q l.

Definition gttstepC g1 g2 p q n := paco5 gttstep bot5 g1 g2 p q n. 

Lemma step_mon : monotone5 gttstep.
Proof. 
      unfold monotone5.
      intros.
      induction IN; intros.
      - apply steq with (s := s). easy. easy.
      - constructor; try easy.
        intros.
        specialize(H6 n).
        specialize(H7 n).
        destruct H7.
        - left. easy.
        - destruct H7 as (s1,(g1,(g2,(Ha,(Hb,Hc))))).
          right.
          exists s1. exists g1. exists g2.
          split. easy. split. easy.
          apply LE; try easy.
Qed.

Hint Resolve step_mon : mon.


(* Basic structural properties of the step relation. *)
Section step_lemma.

  Variable G : gtt.
  
  Lemma step_to_pt : forall G' p q l, gttstepC G G' p q l -> isgPartsC p G.
  Proof.
    intros.
    pinversion H.
    - subst.
      constructor.
    - subst.
      destruct H6 as (n,(pr,Ha)).
      specialize(H7 n).
      destruct H7.
      - specialize(eq_trans (esym Ha) H6); intros.
        easy.
      - destruct H6 as (s1,(g1,(Hb,(Hc,Hd)))).
        apply pac_sendr with (n := n) (s := s1) (g := g1); try easy.
    - apply step_mon.
  Qed.
  
  Lemma step_to_pt_r : forall G' p q l, gttstepC G G' p q l -> isgPartsC q G.
  Proof.
    intros.
    pinversion H.
    - subst.
      constructor.
    - subst.
      destruct H6 as (n,(pr,Ha)).
      specialize(H7 n).
      destruct H7.
      - specialize(eq_trans (esym Ha) H6); intros.
        easy.
      - destruct H6 as (s1,(g1,(Hb,(Hc,Hd)))).
        apply pac_sendr with (n := n) (s := s1) (g := g1); try easy.
    - apply step_mon.
  Qed.
  
  (* Stepping cannot introduce a brand-new participant in the tree. *)
  Lemma pt_step_back : forall G' p q l pt, gttstepC G G' p q l -> isgPartsC pt G' -> isgPartsC pt G.
  Proof.
    intros. revert H. revert G.
    induction H0; intros.
    - pinversion H; try easy.
      - subst.
        destruct (participant_dec p0 p); subst; intros.
        - constructor.
        destruct (participant_dec p0 q); subst; intros.
        - constructor.
        - apply pac_sendr with l s (gtt_send p0 q0 l0); try easy.
          constructor.
      - subst. constructor.
      apply step_mon.
    - pinversion H; try easy.
      - subst.
        destruct (participant_dec q0 p); subst; intros.
        - constructor.
        destruct (participant_dec q0 q); subst; intros.
        - constructor.
        - apply pac_sendr with l s (gtt_send p0 q0 l0); try easy.
          constructor.
      - subst. constructor.
      apply step_mon.
    - pinversion H3.
      - subst.
        destruct (participant_dec r p); subst; intros.
        - constructor.
        destruct (participant_dec r q); subst; intros.
        - constructor.
        - apply pac_sendr with l s0 (gtt_send p0 q0 lis); try easy.
          apply pac_sendr with n s g; try easy.
      - subst.
        specialize(H19 n). clear H18.
        rewrite H1 in H19.
        destruct H19; try easy.
        destruct H4 as (s1,(g1,(g2,(Ha,(Hb,Hc))))). inversion Hb. subst.
        pclearbot.
        specialize(IHisgPartsC g1 Hc).
        destruct (participant_dec r p0); subst; intros.
        - constructor.
        destruct (participant_dec r q0); subst; intros.
        - constructor.
        - apply pac_sendr with n s1 g1; try easy.
      apply step_mon.
Qed.
  

(*   Lemma step_to_pt_b : forall G' p q l, gttstepC G G' p q l -> isgPartsC q G.
  Proof.
    intros.
    pinversion H.
    - subst.
      constructor.
    - subst.
      destruct H6 as (n,(pr,Ha)).
      specialize(H7 n).
      destruct H7.
      - specialize(eq_trans (esym Ha) H6); intros.
        easy.
      - destruct H6 as (s1,(g1,(Hb,(Hc,Hd)))).
        apply pac_sendr with (n := n) (s := s1) (g := g1); try easy.
    - apply step_mon.
  Qed. *)
    
  Hypothesis G_wf : regGtt G.
  Hypothesis G_bal : balancedG G.
  
  Lemma step_to_htree : forall G' p q l, gttstepC G G' p q l -> exists G' : gtth, typ_gtth p G' G /\ (ishParts p G' -> False).
  Proof.
    intros.
    specialize(step_to_pt G' p q l H); intros.
    specialize(isgPartsC_to_word p G H0); intros.
    destruct H1 as (w,(pr,Ha)).
    specialize(balanced_to_tree p pr w G G_bal Ha); intros.
    easy.
  Qed.
  
(*   Lemma step_to_htree_b : forall G' p q l, gttstepC G G' p q l -> exists G' : gtth, typ_gtth q G' G /\ (ishParts q G' -> False).
  Proof.
    intros.
    specialize(step_to_pt_b G' p q l H); intros.
    specialize(isgPartsC_to_word q G H0); intros.
    destruct H1 as (w,(pr,Ha)).
    specialize(balanced_to_tree q pr w G G_bal Ha); intros.
    easy.
  Qed. *)
  
  
  
  Lemma regGtt_after_step : forall G' p q l, gttstepC G G' p q l -> regGtt G'.
  Proof.
    intros.
    specialize(step_to_htree G' p q l H); intros.
    destruct H0 as (Gl,(Ha,Hb)).
    clear G_bal.
    revert Ha Hb H G_wf.
    revert G G' p q l.
    induction Gl using gtth_ind_ref; intros.
    - inversion Ha.
      - subst. pinversion H.
        apply step_mon.
      - subst. pinversion H; try easy.
        subst. clear H4.
        specialize(regGtt_cont p q f G_wf l); intros.
        rewrite H8 in H0.
        destruct H0; try easy.
        destruct H0 as (s1,(g1,(Hc,Hd))). inversion Hc. subst. easy.
        apply step_mon.
      - subst. pinversion H; try easy.
        apply step_mon.
    - inversion Ha. subst.
      pinversion H0; try easy.
      - subst. assert False.
        apply Hb. constructor.
        easy.
      - subst.
        rename p into s. rename q into s'. rename p0 into p. rename q0 into q.
        clear H11. clear Ha H0 H16.
        specialize(regGtt_cont s s' ys G_wf); intros.
        specialize(gttTC_inv_send s s' ys G_wf); intros. clear G_wf.
        destruct H1 as (xs0,(Hc,Hd)). clear Hc.
        clear H4 H5 H7 H8 H9 H10.
        assert(forall n, (onth n xs0 = None /\ f' n = None) \/ (exists s g g', onth n xs0 = Some(s, g) /\ f' n = Some(s, g') /\ regGtt g')).
        {
          intro.
          specialize(Hd n). specialize(H0 n). specialize(H17 n). specialize(H6 n). specialize(H n).
          destruct Hd.
          - destruct H1. rewrite H1. rewrite H2 in H17 H6.
            destruct H17. left. easy.
            destruct H3 as (s1,(g1,(g2,(Hc,(Hd,He))))). easy.
          - destruct H1 as (s1,(g1,(g2,(Hc,(Hd,He))))). 
            rewrite Hc. rewrite Hd in H17 H0 H6.
            right. exists s1. exists g1.
            destruct H6; try easy. destruct H1 as (s2,(g3,(Hf,(Hg,(Hh,Hi))))).
            inversion Hh. subst. clear Hh. rewrite Hg in H. 
            destruct H17; try easy. destruct H1 as (s3,(g4,(g5,(Hj,(Hk,Hl))))).
            inversion Hj. subst. clear Hj. rewrite Hk. exists g5.
            split. easy. split. easy.
            destruct H0; try easy. destruct H0 as (s4,(g6,(Hm,Hn))). 
            inversion Hm. subst. clear Hm.
            destruct H; try easy. destruct H as (s5,(g7,(Ho,Hp))). 
            inversion Ho. subst. clear Ho.
            specialize(Hp g6 g5 p q l). pclearbot.
            apply Hp; try easy.
            clear Hp Hi Hn Hl He Hk Hd Hc. intro.
            apply Hb.
            destruct (participant_dec p s); subst; intros.
            - constructor.
            destruct (participant_dec p s'); subst; intros.
            - constructor.
            - apply ha_sendr with n s5 g7; try easy.
        }
        clear Hd H0 H17 H6 Hb H. clear xs p q l ys.
        revert H1. revert f'.
        induction xs0; intros.
        - pose proof H1 as Ht.
          specialize(H1 0).
          destruct H1.
          - simpl in *. easy.
          - destruct H as (s1,(g1,(g2,(Ha,(Hb,Hc))))).
            inversion Ha. subst. clear Ha.
            destruct Hc.
            exists (g_send s s' (slist_x (s1, x))).
            pfold. constructor.
            intro.
            specialize(Ht n).
            destruct Ht.
            - destruct n; try easy. 
              left. easy.
            - destruct H0 as (s2,(g3,(g4,(Hc,(Hd,He))))).
              destruct n; try easy. rewrite Hb. rewrite Hb in Hd. inversion Hd. subst. clear Hd.
              right. simpl. exists s2. exists x. exists g4.
              split. easy. split. easy. left. easy.
        - pose proof H1 as Ht.
          specialize(H1 0).
          specialize(IHxs0 (fun n => f' (S n))).
          assert(regGtt (gtt_send s s' (fun n : fin => f' n.+1))).
          {
            clear H1.
            apply IHxs0. clear IHxs0.
            intro. specialize(Ht (S n)).
            destruct Ht.
            - left. easy.
            - destruct H as (s1,(g1,(g2,(Ha,(Hb,Hc))))).
              right. rewrite Hb. simpl in Ha. rewrite Ha.
              exists s1. exists g1. exists g2.
              easy.
          }
          clear IHxs0 Ht.
          specialize(gttTC_inv_send s s' (fun n : fin => f' n.+1) H); intros.
          destruct H0 as (xs,(Ha,Hb)). clear Ha.
          destruct H1.
          - destruct H0. destruct o; try easy.
            exists (g_send s s' (slist_xs None xs)).
            pfold. constructor.
            intro. destruct n. left. easy.
            simpl.
            specialize(Hb n).
            destruct Hb.
            - left. easy.
            - right. 
              destruct H2 as (s1,(g1,(g2,(Ha,(Hb,Hc))))).
              rewrite Ha. rewrite Hb. exists s1. exists g1. exists g2.
              split. easy. split. easy. left. easy.
          - destruct H0 as (s1,(g1,(g2,(Ha,(Hc,Hd))))).
            simpl in *. subst.
            destruct Hd.
            exists (g_send s s' (slist_xs (Some (s1, x)) xs)).
            pfold. constructor.
            intro.
            destruct n.
            - right. simpl. rewrite Hc.
              exists s1. exists x. exists g2. split. easy. split. easy. 
              left. easy.
            - specialize(Hb n).
              simpl in *.
              destruct Hb.
              - left. easy.
              - right. 
                destruct H1 as (s2,(g3,(g4,(Ha,(Hb,Hd))))).
                rewrite Ha. rewrite Hb. exists s2. exists g3. exists g4.
                split. easy. split. easy. left. easy.
        apply step_mon.
  Qed.



End step_lemma.

End step.

Variable isMerge : (fin -> option ltt) -> ltt -> Prop.


Section projection.


(* Coinductive projection from a global tree to one participant's local type.
   The `proj_cont` rule covers bystanders and relies on merge. *)
Variant projection (R: gtt -> participant -> ltt -> Prop): gtt -> participant -> ltt -> Prop :=
  | proj_end : forall g r, 
               (isgPartsC r g -> False) -> 
               projection R g r (ltt_end)
  | proj_in  : forall p r f f',
               p <> r ->
               (isgPartsC r (gtt_send p r f)) ->
               (forall n, (f n = None /\ f' n = None) \/ (exists s g t, f n = Some(s, g) /\ f' n = Some(s, t) /\ R g r t)) ->
               projection R (gtt_send p r f) r (ltt_recv p f')
  | proj_out : forall r q f f',
               r <> q ->
               (isgPartsC r (gtt_send r q f)) ->
               (forall n, (f n = None /\ f' n = None) \/ (exists s g t, f n = Some(s, g) /\ f' n = Some(s, t) /\ R g r t)) ->
               projection R (gtt_send r q f) r (ltt_send q f')
  | proj_cont: forall p q r f f' t,
               p <> q ->
               q <> r ->
               p <> r ->
               (isgPartsC r (gtt_send p q f)) ->
               (forall n, (f n = None /\ f' n = None) \/ (exists s g t, f n = Some(s, g) /\ f' n = Some t /\ R g r t)) ->
               isMerge f' t ->
               projection R (gtt_send p q f) r t.

Definition projectionC g r t := paco3 projection bot3 g r t.

Lemma proj_mon : monotone3 projection.
Proof.
  unfold monotone3; intros.
  induction IN.
  - constructor. easy.
  - constructor; try easy.
    intros.
    specialize(H1 n).
    destruct H1.
    - left. easy.
    - right.
      destruct H1 as (s1,(g1,(t1,(Ha,(Hb,Hc))))).
      exists s1. exists g1. exists t1.
      split. easy. split. easy.
      apply LE; try easy.
  - constructor; try easy.
    intros.
    specialize(H1 n).
    destruct H1.
    - left. easy.
    - right.
      destruct H1 as (s1,(g1,(t1,(Ha,(Hb,Hc))))).
      exists s1. exists g1. exists t1.
      split. easy. split. easy.
      apply LE; try easy.
  - apply proj_cont with f'; try easy.
    intros.
    specialize(H3 n).
    destruct H3. 
    - left. easy.
    - right.
      destruct H3 as (s1,(g1,(t1,(Ha,(Hb,Hc))))).
      exists s1. exists g1. exists t1.
      split. easy. split. easy.
      apply LE; try easy.
Qed.


Definition projectableA G := forall pt, exists T, projectionC G pt T.


End projection.


    


Section typ_after_step.

(* Main preservation layer: projection information survives global steps. *)
Section pmergeCR. 

Hypothesis merge_cont_end : forall f n t, isMerge f ltt_end -> f n = Some t -> t = ltt_end.
Hypothesis merge_from_end : forall f n t, isMerge f t -> f n = Some ltt_end -> t = ltt_end.

Lemma pmergeCR : forall G pt, regGtt G -> projectionC G pt ltt_end -> isgPartsC pt G -> False.
Proof.
  intros.
  specialize(dec_isgPartsC G pt H); intros.
  destruct H2; try easy. clear H1.
  clear H.
  revert H0.
  induction H2; intros.
  - pinversion H0; try easy.
    apply H. constructor.
    apply proj_mon.
  - pinversion H0; try easy.
    apply H. constructor.
    apply proj_mon.
  - pinversion H3; try easy.
    - subst.
      apply H4.
      apply pac_sendr with n s g; try easy.
    - subst.
      specialize(H13 n). rewrite H1 in H13.
      destruct H13; try easy.
      destruct H4 as (s1,(g1,(t1,(Ha,(Hb,Hc))))).
      inversion Ha. subst. 
      apply IHisgPartsC.
      specialize(merge_cont_end f' n t1 H14 Hb); intros. subst. 
      pclearbot. easy.
    apply proj_mon.
Qed.

Lemma pt_step_forward : forall G G' p q l r T, regGtt G -> gttstepC G G' p q l -> projectionC G r T -> p <> r -> q <> r -> isgPartsC r G -> isgPartsC r G'.
  Proof.
    intros.
    revert H H0 H1 H2 H3. revert G' T.
    induction H4; intros.
    - pinversion H0; try easy.
      - subst. easy.
      - subst. constructor.
      apply step_mon.
    - pinversion H0; try easy.
      - subst. easy.
      - subst. constructor.
      apply step_mon.
    - pinversion H3; try easy.
      - subst.
        pinversion H5; try easy.
        - subst.
          assert False. 
          apply H8.
          apply pac_sendr with n s g; try easy.
          easy.
        - subst.
          specialize(H19 l). rewrite H16 in H19.
          destruct H19; try easy.
          destruct H8 as (s1,(g1,(t1,(Ha,(Hb,Hc))))).
          inversion Ha. subst. clear Ha.
          pclearbot. pinversion Hc; try easy.
          subst.
          specialize(merge_from_end f' l T H20 Hb); intros. subst.
          specialize(pmergeCR (gtt_send p q lis) r H2); intros.
          assert False. apply H9; try easy. pfold. easy.
          easy.
        apply proj_mon.
        apply proj_mon.
      - subst.
        clear H22 H3.
        pinversion H5; try easy.
        - subst.
          assert False.
          apply H3.
          apply pac_sendr with n s g; try easy.
          easy.
        - subst.
          specialize(H24 n). specialize(H23 n).
          rewrite H1 in H23 H24.
          destruct H23; try easy. 
          destruct H3 as (s1,(g1,(g2,(Hd,(Hb,Hc))))). inversion Hd. subst. clear Hd.
          destruct H24; try easy.
          destruct H3 as (s2,(g3,(t1,(He,(Hf,Hg))))).
          inversion He. subst. clear He.
          specialize(regGtt_cont p0 q0 lis H2); intros.
          specialize(H3 n). rewrite H1 in H3.
          destruct H3; try easy. destruct H3 as (s3,(g4,(Hh,Hi))).
          inversion Hh. subst. clear Hh.
          specialize(IHisgPartsC g2 t1).
          assert(isgPartsC r g2).
          {
            pclearbot.
            apply IHisgPartsC; try easy.
          }
          apply pac_sendr with n s3 g2; try easy.
    apply proj_mon.
    apply step_mon.
Qed.
          
         
        

End pmergeCR.

Variable G : gtt.
Hypothesis G_bal : balancedG G.
Hypothesis G_wf : regGtt G.

Definition through_merge_s (g : fin -> option ltt) (l : fin) : fin -> option ltt :=
  (fun i => match g i with 
      | Some (ltt_send _ f) => match f l with
                                 | Some (_, t) => Some t 
                                 | None        => None 
                               end
      | _ => None
    end).

Definition through_merge_r (g : fin -> option ltt) (l : fin) : fin -> option ltt :=
  (fun i => match g i with 
      | Some (ltt_recv _ f) => match f l with
                                 | Some (_, t) => Some t 
                                 | None        => None 
                               end
      | _ => None
    end).
    

Hypothesis merge_from_end : forall f n t, isMerge f t -> f n = Some ltt_end -> t = ltt_end.


Section ltt_after_step_p.

Hypothesis merge_cont_send : forall g p f, isMerge g (ltt_send p f) -> forall n t, g n = Some t -> exists f', t = ltt_send p f'.

Hypothesis merge_label_send : forall g p f, isMerge g (ltt_send p f) -> forall n q f' l st, g n = Some (ltt_send q f') -> f' l = Some st -> exists st', f l = Some st'.

Hypothesis merge_into_send : forall g p f, isMerge g (ltt_send p f) -> forall n s t, f n = Some(s, t) -> isMerge (through_merge_s g n) t. 

(* Sender-side projection after a communication step:
   branch `l` is consumed and the continuation remains projectable. *)
Lemma ltt_after_step_p : forall p q l G' f, gttstepC G G' p q l -> projectionC G p (ltt_send q f) -> exists s t, f l = Some(s, t) /\ projectionC G' p t.
Proof.
  intros.
  specialize(step_to_htree G G_bal G' p q l H); intros.
  destruct H1 as (Gl,(Ha,Hb)).
  specialize(regGtt_after_step G G_wf G_bal G' p q l H); intros Ht.
  clear G_bal.
  revert H H0 Ha Hb G_wf Ht.
  revert G p q l G' f.
  induction Gl using gtth_ind_ref; intros.
  - inversion Ha.
    - subst.
      pinversion H0.
      apply proj_mon.
    - subst.
      pinversion H0.
      - subst.
        pinversion H; try easy.
        subst.
        clear H10 H7.
        specialize(H9 l).
        destruct H9.
        - rewrite H13 in H1. easy.
        - destruct H1 as (s1,(g1,(t1,(Hc,(Hd,He))))).
          rewrite H13 in Hc. inversion Hc. subst. clear Hc.
          exists s1. exists t1. split. easy.
          destruct He; try easy.
          apply step_mon.
      - subst. easy.
      apply proj_mon.
    - subst.
      pinversion H0.
      - subst. easy.
      - subst. easy.
      apply proj_mon.
  - inversion Ha. subst. clear Ha.
    pinversion H0; try easy.
    - subst.
      assert False.
      apply Hb. constructor.
      easy.
    - subst.
      rename p into s. rename q into s'. rename p0 into p. rename q0 into q.
      clear H0.
      pinversion H1; try easy.
      subst. clear H4 H13 H14 H15 H17 H1.
      assert(forall n, (ys n = None /\ f' n = None) \/ 
                       (exists s g g', ys n = Some (s, g) /\ f' n = Some(s, g') /\ gttstepC g g' p q l /\ 
                          exists f, projectionC g p (ltt_send q f) /\ f'0 n = Some (ltt_send q f) /\ exists s' t, f l = Some (s', t) /\ projectionC g' p t)).
      {
        intro.
        specialize(H18 n). specialize(H20 n). specialize(H n). specialize(H7 n).
        destruct H18. 
        - left. easy.
        - right. destruct H0 as (s1,(g1,(g2,(Hc,(Hd,He))))).
          rewrite Hc in H20 H7.
          destruct H20; try easy.
          destruct H0 as (s2,(g3,(t1,(Hf,(Hg,Hh))))). inversion Hf. subst. clear Hf.
          destruct H7; try easy.
          destruct H0 as (s3,(g4,(g5,(Hi,(Hj,Hk))))). inversion Hi. subst. clear Hi.
          inversion Hj. subst. clear Hj.
          rewrite H1 in H.
          destruct H; try easy.
          destruct H as (s4,(g6,(Hl,Hm))). inversion Hl. subst. clear Hl.
          pclearbot.
          specialize(Hm g5 p q l g2).
          exists s4. exists g5. exists g2.
          split. easy. split. easy. split. easy.
          specialize(merge_cont_send f'0 q f H21 n t1 Hg).
          destruct merge_cont_send as (f2,Hn). subst. clear merge_cont_send.
          exists f2.
          specialize(Hm f2 He Hh Hk).
          split. easy. split. easy.
          apply Hm.
          intro. apply Hb.
          apply ha_sendr with (n := n) (s := s4) (g := g6); try easy.
          specialize(regGtt_cont s s' ys G_wf n); intros.
          rewrite Hc in H.
          destruct H; try easy.
          destruct H as (s1,(g1,(Hn,Ho))). inversion Hn. subst. easy.
          specialize(regGtt_cont s s' f' Ht n); intros.
          rewrite Hd in H.
          destruct H; try easy.
          destruct H as (s1,(g1,(Hn,Ho))). inversion Hn. subst. easy.
      }
      clear H18 H H7 Hb.
      clear merge_cont_send.
      specialize(merge_into_send f'0 q f H21 l).
      specialize(merge_label_send f'0 q f H21); intros.
      assert(exists st' : sort * ltt, f l = Some st').
      {
        destruct H12 as (n,(stt,Ha)).
        specialize(H0 n). rewrite Ha in H0.
        destruct H0; try easy.
        destruct H as (s1,(g1,(g2,(Hb,(Hc,(Hd,(ff,(He,(Hf,(s2,(t1,(Hg,Hh)))))))))))).
        specialize(merge_label_send n q ff l (s2, t1) Hf Hg). easy.
      }
      destruct H as (st,Ha). destruct st. exists s0. exists l0. split. easy.
 
      clear merge_label_send.
      specialize(merge_into_send s0 l0 Ha).
      specialize(dec_isgPartsC (gtt_send s s' f') p Ht); intros Hta.
      destruct Hta as [Hta | Hta].
      
      - pfold. apply proj_cont with (through_merge_s f'0 l); try easy.
        clear H12 H5 H6 H8 H9 H10 H11.
        intros.
        specialize(H0 n). specialize(H20 n).
        destruct H0.
        - destruct H. rewrite H in H20.
          rewrite H0.
          destruct H20.
          destruct H1. 
          unfold through_merge_s at 1. rewrite H2.
          left. easy.
          destruct H1 as (s1,(g1,(t1,(Hb,(Hc,Hd))))). easy.
        - destruct H as (s1,(g1,(g2,(Hb,(Hc,(Hd,(ff,(He,(Hf,(s2,(t1,(Hg,Hh)))))))))))).
          right. rewrite Hb in H20.
          destruct H20; try easy.
          destruct H as (s3,(g3,(t2,(Hi,(Hj,Hk))))).
          rewrite Hj in Hf.
          inversion Hf. subst. clear Hf.
          inversion Hi. subst. clear Hi.
          rewrite Hc. 
          exists s3. exists g2.
          unfold through_merge_s. rewrite Hj. rewrite Hg. exists t1.
          split. easy. split. easy.
          left. easy.
      - clear H20.
        destruct H12 as (n,(pt,Hb)).
        specialize(H0 n). rewrite Hb in H0.
        destruct H0; try easy.
        destruct H as (s1,(g1,(g2,(Hc,(Hd,(He,(fn,(Hf,(Hg,(s2,(t1,(Hh,Hi)))))))))))).
        clear G_wf Hb Hc Hf He.
        clear Ha H21. clear f xs ys pt s0 g1.
        assert(isgPartsC p g2 -> False).
        {
          intro.
          apply Hta.
          apply pac_sendr with n s1 g2; try easy.
        }
        clear Hd.
        assert(t1 = ltt_end).
        {
          pinversion Hi; try easy. subst. easy. subst. easy. subst. easy.
          apply proj_mon.
        }
        subst. 
        assert(l0 = ltt_end).
        {
          clear H Hi Hta H11 H10 H9 H8 H6 H5.
          specialize(merge_from_end (through_merge_s f'0 l) n l0 merge_into_send).
          apply merge_from_end.
          unfold through_merge_s. rewrite Hg. rewrite Hh. easy.
        }
        subst.
        pfold. constructor; try easy. 
      apply proj_mon.
      apply step_mon.
Qed.

End ltt_after_step_p.

Section ltt_after_step_q.

Hypothesis merge_cont_recv : forall g p f, isMerge g (ltt_recv p f) -> forall n t, g n = Some t -> exists f', t = ltt_recv p f'.

Hypothesis merge_label_recv : forall g p f, isMerge g (ltt_recv p f) -> forall n q f' l st, g n = Some (ltt_recv q f') -> f' l = Some st -> exists st', f l = Some st'.

Hypothesis merge_into_recv : forall g p f, isMerge g (ltt_recv p f) -> forall n s t, f n = Some(s, t) -> isMerge (through_merge_r g n) t. 

(* Dual of `ltt_after_step_p` for the receiver side. *)
Lemma ltt_after_step_q : forall p q l G' f, gttstepC G G' p q l -> projectionC G q (ltt_recv p f) -> exists s t, f l = Some(s, t) /\ projectionC G' q t.
Proof.
  intros.
  specialize(step_to_htree G G_bal G' p q l H); intros.
  destruct H1 as (Gl,(Ha,Hb)).
  specialize(regGtt_after_step G G_wf G_bal G' p q l H); intros Ht.
  clear G_bal.
  revert H H0 Ha Hb G_wf Ht.
  revert G p q l G' f.
  induction Gl using gtth_ind_ref; intros.
  - inversion Ha.
    - subst.
      pinversion H0.
      apply proj_mon.
    - subst. pinversion H; try easy. subst.
      pinversion H0.
      - subst.
        clear H10 H7.
        specialize(H11 l). rewrite H9 in H11.
        destruct H11; try easy.
        - destruct H1 as (s1,(g1,(t1,(Hc,(Hd,He))))).
          inversion Hc. subst. clear Hc.
          exists s1. exists t1. split. easy.
          destruct He; try easy.
      - subst. easy.
      apply proj_mon.
      apply step_mon.
    - subst.
      pinversion H; try easy.
      apply step_mon.
  - inversion Ha. subst. clear Ha.
    pinversion H0; try easy.
    - subst.
      assert False.
      apply Hb. constructor.
      easy.
    - subst.
      rename p into s. rename q into s'. rename p0 into p. rename q0 into q.
      clear H0.
      pinversion H1; try easy.
      subst. clear H4 H13 H14 H15 H17 H1.
      assert(forall n, (ys n = None /\ f' n = None) \/ 
                       (exists s g g', ys n = Some (s, g) /\ f' n = Some(s, g') /\ gttstepC g g' p q l /\ 
                          exists f, projectionC g q (ltt_recv p f) /\ f'0 n = Some (ltt_recv p f) /\ exists s' t, f l = Some (s', t) /\ projectionC g' q t)).
      {
        intro.
        specialize(H18 n). specialize(H20 n). specialize(H n). specialize(H7 n).
        destruct H18. 
        - left. easy.
        - right. destruct H0 as (s1,(g1,(g2,(Hc,(Hd,He))))).
          rewrite Hc in H20 H7.
          destruct H20; try easy.
          destruct H0 as (s2,(g3,(t1,(Hf,(Hg,Hh))))). inversion Hf. subst. clear Hf.
          destruct H7; try easy.
          destruct H0 as (s3,(g4,(g5,(Hi,(Hj,Hk))))). inversion Hi. subst. clear Hi.
          inversion Hj. subst. clear Hj.
          rewrite H1 in H.
          destruct H; try easy.
          destruct H as (s4,(g6,(Hl,Hm))). inversion Hl. subst. clear Hl.
          pclearbot.
          specialize(Hm g5 p q l g2).
          exists s4. exists g5. exists g2.
          split. easy. split. easy. split. easy.
          specialize(merge_cont_recv f'0 p f H21 n t1 Hg).
          destruct merge_cont_recv as (f2,Hn). subst. clear merge_cont_recv.
          exists f2.
          specialize(Hm f2 He Hh Hk).
          split. easy. split. easy.
          apply Hm.
          intro. apply Hb.
          apply ha_sendr with (n := n) (s := s4) (g := g6); try easy.
          specialize(regGtt_cont s s' ys G_wf n); intros.
          rewrite Hc in H.
          destruct H; try easy.
          destruct H as (s1,(g1,(Hn,Ho))). inversion Hn. subst. easy.
          specialize(regGtt_cont s s' f' Ht n); intros.
          rewrite Hd in H.
          destruct H; try easy.
          destruct H as (s1,(g1,(Hn,Ho))). inversion Hn. subst. easy.
      }
      clear H18 H H7 Hb.
      clear merge_cont_recv.
      specialize(merge_into_recv f'0 p f H21 l).
      specialize(merge_label_recv f'0 p f H21); intros.
      assert(exists st' : sort * ltt, f l = Some st').
      {
        destruct H12 as (n,(stt,Ha)).
        specialize(H0 n). rewrite Ha in H0.
        destruct H0; try easy.
        destruct H as (s1,(g1,(g2,(Hb,(Hc,(Hd,(ff,(He,(Hf,(s2,(t1,(Hg,Hh)))))))))))).
        specialize(merge_label_recv n p ff l (s2, t1) Hf Hg). easy.
      }
      destruct H as (st,Ha). destruct st. exists s0. exists l0. split. easy.
 
      clear merge_label_recv.
      specialize(merge_into_recv s0 l0 Ha).
      specialize(dec_isgPartsC (gtt_send s s' f') q Ht); intros Hta.
      destruct Hta as [Hta | Hta].
      
      - pfold. apply proj_cont with (through_merge_r f'0 l); try easy.
        clear H12 H5 H6 H8 H9 H10 H11.
        intros.
        specialize(H0 n). specialize(H20 n).
        destruct H0.
        - destruct H. rewrite H in H20.
          rewrite H0.
          destruct H20.
          destruct H1. 
          unfold through_merge_r at 1. rewrite H2.
          left. easy.
          destruct H1 as (s1,(g1,(t1,(Hb,(Hc,Hd))))). easy.
        - destruct H as (s1,(g1,(g2,(Hb,(Hc,(Hd,(ff,(He,(Hf,(s2,(t1,(Hg,Hh)))))))))))).
          right. rewrite Hb in H20.
          destruct H20; try easy.
          destruct H as (s3,(g3,(t2,(Hi,(Hj,Hk))))).
          rewrite Hj in Hf.
          inversion Hf. subst. clear Hf.
          inversion Hi. subst. clear Hi.
          rewrite Hc. 
          exists s3. exists g2.
          unfold through_merge_r. rewrite Hj. rewrite Hg. exists t1.
          split. easy. split. easy.
          left. easy.
      - clear H20.
        destruct H12 as (n,(pt,Hb)).
        specialize(H0 n). rewrite Hb in H0.
        destruct H0; try easy.
        destruct H as (s1,(g1,(g2,(Hc,(Hd,(He,(fn,(Hf,(Hg,(s2,(t1,(Hh,Hi)))))))))))).
        clear G_wf Hb Hc Hf He.
        clear Ha H21. clear f xs ys pt s0 g1.
        assert(isgPartsC q g2 -> False).
        {
          intro.
          apply Hta.
          apply pac_sendr with n s1 g2; try easy.
        }
        clear Hd.
        assert(t1 = ltt_end).
        {
          pinversion Hi; try easy. subst. easy. subst. easy. subst. easy.
          apply proj_mon.
        }
        subst. 
        assert(l0 = ltt_end).
        {
          clear H Hi Hta H11 H10 H9 H8 H6 H5.
          specialize(merge_from_end (through_merge_r f'0 l) n l0 merge_into_recv).
          apply merge_from_end.
          unfold through_merge_r. rewrite Hg. rewrite Hh. easy.
        }
        subst.
        pfold. constructor; try easy. 
      apply proj_mon.
      apply step_mon.
Qed.

End ltt_after_step_q.


Section ltt_after_step_r.

  (* MergeInto T T' means: T' is a merged refinement of T. *)
  Variable MergeInto : ltt -> ltt -> Prop.
  
  Hypothesis MergeInto_end : MergeInto ltt_end ltt_end.
  Hypothesis MergeInto_end_r : forall t, MergeInto ltt_end t -> t = ltt_end.
  
  Hypothesis MergeInto_send : forall p fl fr, (forall n, (fl n = None /\ fr n = None) \/ (exists s t t', fl n = Some(s, t) /\ fr n = Some(s, t') /\ MergeInto t t')) -> MergeInto (ltt_send p fl) (ltt_send p fr).
  Hypothesis MergeInto_recv : forall p fl fr, (forall n, (fl n = None /\ fr n = None) \/ (exists s t t', fl n = Some(s, t) /\ fr n = Some(s, t') /\ MergeInto t t')) -> MergeInto (ltt_recv p fl) (ltt_recv p fr).
  Hypothesis isMerge_cont_Into : forall f f' T, isMerge f T -> (forall n, (f n = None /\ f' n = None) \/ (exists t t', f n = Some t /\ f' n = Some t' /\ MergeInto t t')) -> exists T', isMerge f' T' /\ MergeInto T T'.
  
  
  Hypothesis isMerge_to_Into : forall f T l T', isMerge f T -> f l = Some T' -> MergeInto T T'.
  
  Hypothesis merge_cont_end : forall f n t, isMerge f ltt_end -> f n = Some t -> t = ltt_end.
  
  (* Bystander projection after a step: type may change only via merge. *)
  Lemma ltt_after_step_r : forall p q r l G' T, gttstepC G G' p q l -> p <> r -> q <> r -> projectionC G r T -> exists T', projectionC G' r T' /\ MergeInto T T'.
  Proof.
    intros.
    specialize(step_to_htree G G_bal G' p q l H); intros.
    destruct H3 as (Gl,(Ha,Hb)).
    specialize(regGtt_after_step G G_wf G_bal G' p q l H); intros Ht.
    clear G_bal.
    revert H H0 H1 H2 Ha Hb G_wf Ht.
    revert G' T G.
    induction Gl using gtth_ind_ref; intros.
    - inversion Ha.
      - subst.
        pinversion H; try easy.
        apply step_mon.
      - subst.
        pinversion H; try easy. subst.
        clear H7.
        pinversion H2; try easy.
        - subst.
          assert(isgPartsC r G' -> False).
          {
            intro. apply H3.
            apply pac_sendr with l s G'; try easy.
          }
          exists ltt_end.
          split.
          - pfold.
            constructor; try easy.
          - easy.
        - subst.
          specialize(H14 l). rewrite H11 in H14.
          destruct H14; try easy. 
          destruct H3 as (s1,(g1,(t1,(Hd,(He,Hf))))).
          inversion Hd. subst. clear Hd.
          exists t1. pclearbot. split. easy.
          apply isMerge_to_Into with f' l; try easy.
        apply proj_mon.
        apply step_mon.
      - subst.
        pinversion H; try easy.
        apply step_mon.
    - inversion Ha. subst. clear Ha.
      pinversion H0; try easy.
      - subst.
        assert False.
        apply Hb. constructor.
        easy.
      - subst.
        rename p0 into s. rename q0 into s'. clear H14.
        assert(forall n, (ys n = None /\ f' n = None) \/ (exists s g g', ys n = Some(s, g) /\ f' n = Some(s, g') /\ gttstepC g g' p q l /\ (forall T, projectionC g r T -> exists T', projectionC g' r T' /\ MergeInto T T'))).
        {
          intro.
          specialize(H19 n). specialize(H20 n). specialize(H9 n). specialize(H n).
          destruct H20.
          left. easy.
          destruct_exists_and. rewrite H4 in H19 H9.
          destruct H19; try easy. destruct_exists_and.
          destruct H9; try easy. destruct_exists_and. invert_all_some.
          rewrite H9 in H. destruct H; try easy. destruct_exists_and. invert_all_some.
          right. rewrite H4 H5. exists x. exists x3. exists x1. pclearbot.
          - split. easy.
          - split. easy.
          - split. easy.
          - intros.
            specialize(H14 x1 T0 x3). fill_triv.
            apply H14; try easy.

            - intro.  
              apply Hb.
              apply ha_sendr with n x x0; try easy.
            - specialize(regGtt_cont s s' ys G_wf n); intros.
              rewrite H4 in H17. destruct H17; try easy. destruct_exists_and. invert_all_some. easy.
            - specialize(regGtt_cont s s' f' Ht n); intros.
              rewrite H5 in H17. destruct H17; try easy. destruct_exists_and. invert_all_some. easy.
        }
        clear Hb H H9 H19 H20. rename H0 into Htt.
        
        pinversion H3; rename H3 into Htk.
        - subst.
          exists ltt_end.
          split; try easy.
          pfold. constructor.
          intro. apply H.
          inversion H0.
          - constructor.
          - constructor.
          - subst.
            specialize(H4 n). rewrite H16 in H4.
            destruct H4; try easy. destruct_exists_and. invert_all_some.
            apply pac_sendr with n x x0; try easy.
            apply pt_step_back with x1 p q l; try easy.
        - subst.
          clear H6 H12 H13 H15.
          specialize(regGtt_fin_cont s r ys G_wf); intros.
          destruct H as (n,Ha).
          assert(exists f2, forall n, (f' n = None /\ f'0 n = None /\ f2 n = None) \/ (exists s g t t', f' n = Some(s, g) /\ f'0 n = Some (s, t) /\ f2 n = Some (s, t') /\ projectionC g r t' /\ MergeInto t t')).
          {
            revert Ha H16 H4. clear G_wf Ht Htt Htk.
            revert f' f'0 ys.
            induction n; intros.
            - exists (fun i => None).
              intro.
              specialize(Ha n). specialize(H16 n). specialize(H4 n).
              assert(ys n = None). apply Ha; try easy.
              rewrite H in H4 H16.
              destruct H4.
              - destruct H16. left. easy.
                destruct_exists_and; try easy.
              - destruct_exists_and. easy.
            - specialize(IHn (fun n => f' (S n)) (fun n => f'0 (S n)) (fun n => ys (S n))).
              assert(exists f2 : fin -> option (sort * ltt),
                forall n : fin,
                (fun n0 : fin => f' n0.+1) n = None /\
                (fun n0 : fin => f'0 n0.+1) n = None /\ f2 n = None \/
                (exists (s : sort) (g : gtt) (t t' : ltt),
                   (fun n0 : fin => f' n0.+1) n = Some (s, g) /\
                   (fun n0 : fin => f'0 n0.+1) n = Some (s, t) /\
                   f2 n = Some (s, t') /\ projectionC g r t' /\ MergeInto t t')).
              {
                apply IHn; try easy.
                intros.
                specialize(Ha (S m) H). easy.
              }
              clear IHn Ha.
              destruct H as (f2,Ha).
              specialize(H16 0). specialize(H4 0).
              - destruct H4.
                - destruct H. rewrite H in H16.
                  destruct H16. destruct H3.
                  exists (fun n => match n with 
                            | 0 => None 
                            | S m => f2 m end).
                  intro.
                  destruct n0.
                  - left. easy.
                  - specialize(Ha n0). easy.
                - destruct H3 as (s1,(g1,(t1,Hb))). easy.
              - destruct H as (s1,(g1,(g2,(Hb,(Hc,(Hd,He)))))).
                rewrite Hb in H16.
                destruct H16; try easy. 
                destruct H as (s2,(g3,(t1,(Hf,(Hg,Hh))))). 
                inversion Hf. subst. clear Hf.
                pclearbot.
                specialize(He t1 Hh). destruct He as (t,Hi).
                exists (fun n => match n with 
                          | 0 => Some (s2, t)
                          | S m => f2 m end).
                intro.
                destruct n0; try easy.
                right. rewrite Hc. rewrite Hg.
                exists s2. exists g2. exists t1. exists t.
                easy.
          }
          clear Ha H16 H4.
          destruct H as (fr,H). exists (ltt_recv s fr).
          split.
          - pfold. constructor; try easy.
            constructor.
            intro.
            specialize(H n0).
            destruct H.
            - left. easy.
            - right.
              destruct H as (s1,(g1,(t1,(t2,(Ha,(Hb,(Hc,(Hd,He)))))))).
              rewrite Ha. rewrite Hc.
              exists s1. exists g1. exists t2.
              split. easy. split. easy. left. easy.
          - apply MergeInto_recv. 
            intro.
            specialize(H n0).
            destruct H.
            - left. easy.
            - right.
              destruct H as (s1,(g1,(t1,(t2,(Ha,(Hb,(Hc,(Hd,He)))))))).
              rewrite Hb. rewrite Hc.
              exists s1. exists t1. exists t2. easy.
        - subst.
          clear H6 H15 H11 H10.
          specialize(regGtt_fin_cont r s' ys G_wf); intros.
          destruct H as (n,Ha).
          assert(exists f2, forall n, (f' n = None /\ f'0 n = None /\ f2 n = None) \/ (exists s g t t', f' n = Some(s, g) /\ f'0 n = Some (s, t) /\ f2 n = Some (s, t') /\ projectionC g r t' /\ MergeInto t t')).
          {
            revert Ha H16 H4. clear G_wf Ht Htt Htk.
            revert f' f'0 ys.
            induction n; intros.
            - exists (fun i => None).
              intro.
              specialize(Ha n). specialize(H16 n). specialize(H4 n).
              assert(ys n = None). apply Ha; try easy.
              rewrite H in H4 H16.
              destruct H4.
              - destruct H16. left. easy.
                destruct H3 as (s1,(g1,(t1,Hd))). easy.
              - destruct H0 as (s0,(g1,(g2,Hd))). easy.
            - specialize(IHn (fun n => f' (S n)) (fun n => f'0 (S n)) (fun n => ys (S n))).
              assert(exists f2 : fin -> option (sort * ltt),
                forall n : fin,
                (fun n0 : fin => f' n0.+1) n = None /\
                (fun n0 : fin => f'0 n0.+1) n = None /\ f2 n = None \/
                (exists (s : sort) (g : gtt) (t t' : ltt),
                   (fun n0 : fin => f' n0.+1) n = Some (s, g) /\
                   (fun n0 : fin => f'0 n0.+1) n = Some (s, t) /\
                   f2 n = Some (s, t') /\ projectionC g r t' /\ MergeInto t t')).
              {
                apply IHn; try easy.
                intros.
                specialize(Ha (S m) H). easy.
              }
              clear IHn Ha.
              destruct H as (f2,Ha).
              specialize(H16 0). specialize(H4 0).
              - destruct H4.
                - destruct H. rewrite H in H16.
                  destruct H16. destruct H3.
                  exists (fun n => match n with 
                            | 0 => None 
                            | S m => f2 m end).
                  intro.
                  destruct n0.
                  - left. easy.
                  - specialize(Ha n0). easy.
                - destruct H3 as (s1,(g1,(t1,Hb))). easy.
              - destruct H as (s1,(g1,(g2,(Hb,(Hc,(Hd,He)))))).
                rewrite Hb in H16.
                destruct H16; try easy. 
                destruct H as (s2,(g3,(t1,(Hf,(Hg,Hh))))). 
                inversion Hf. subst. clear Hf.
                pclearbot.
                specialize(He t1 Hh). destruct He as (t,Hi).
                exists (fun n => match n with 
                          | 0 => Some (s2, t)
                          | S m => f2 m end).
                intro.
                destruct n0; try easy.
                right. rewrite Hc. rewrite Hg.
                exists s2. exists g2. exists t1. exists t.
                easy.
          }
          clear Ha H16 H4.
          destruct H as (fr,H). exists (ltt_send s' fr).
          split.
          - pfold. constructor; try easy.
            constructor.
            intro.
            specialize(H n0).
            destruct H.
            - left. easy.
            - right.
              destruct H as (s1,(g1,(t1,(t2,(Ha,(Hb,(Hc,(Hd,He)))))))).
              rewrite Ha. rewrite Hc.
              exists s1. exists g1. exists t2.
              split. easy. split. easy. left. easy.
          - apply MergeInto_send. 
            intro.
            specialize(H n0).
            destruct H.
            - left. easy.
            - right.
              destruct H as (s1,(g1,(t1,(t2,(Ha,(Hb,(Hc,(Hd,He)))))))).
              rewrite Hb. rewrite Hc.
              exists s1. exists t1. exists t2. easy.
        - subst.
          assert(exists f2, (forall n, (f' n = None /\ f'0 n = None /\ f2 n = None) \/ (exists s g t t', f' n = Some(s, g) /\ f'0 n = Some t /\ f2 n = Some t' /\ projectionC g r t' /\ MergeInto t t'))).
          {
            specialize(regGtt_fin_cont s s' ys G_wf); intros.
            destruct H as (n,H).
            clear H6 Ht G_wf H15 H19 Htt Htk.
            revert H H18 H4. revert f' f'0 ys. 
            induction n; intros.
            - exists (fun n => None).
              intro.
              specialize(H18 n). specialize(H n). specialize(H4 n).
              assert(ys n = None). apply H; try easy. clear H.
              rewrite H0 in H18 H4.
              destruct H18.
              - destruct H4. left. easy.
                destruct H3 as (s1,(g1,(g2,Ha))). easy.
              - destruct H as (s1,(g1,(t1,Ha))). easy.
            - specialize(IHn (fun n => f' (S n)) (fun n => f'0 (S n)) (fun n => ys (S n))). 
              assert(exists f2 : fin -> option ltt,
                forall n : fin,
                (fun n0 : fin => f' n0.+1) n = None /\
                (fun n0 : fin => f'0 n0.+1) n = None /\ f2 n = None \/
                (exists (s : sort) (g : gtt) (t t' : ltt),
                   (fun n0 : fin => f' n0.+1) n = Some (s, g) /\
                   (fun n0 : fin => f'0 n0.+1) n = Some t /\
                   f2 n = Some t' /\ projectionC g r t' /\ MergeInto t t')).
              {
                apply IHn; try easy.
                intros.
                specialize(H (S m)). apply H; try easy.
              }
              clear IHn H.
              specialize(H18 0). specialize(H4 0).
              destruct H0 as (fn,Ha).
              - destruct H4.
                destruct H18.
                exists (fun n => match n with 
                          | 0 => None
                          | S m => fn m end).
                intro. destruct n0; try easy. left. easy.
                
                destruct H. rewrite H in H0.
                destruct H0 as (s1,(g1,(t1,Hb))). easy.
              - destruct H as (s1,(g1,(g2,(Hb,(Hc,(Hd,He)))))).
                rewrite Hb in H18.
                destruct H18; try easy.
                destruct H as (s2,(g3,(t1,(Hf,(Hg,Hh))))).
                inversion Hf. subst. clear Hf.
                pclearbot.
                specialize(He t1 Hh). destruct He as (t,(Hi,Hj)).
                exists (fun n => match n with 
                          | 0 => Some t
                          | S m => fn m end).
                intro. destruct n0; try easy.
                right. rewrite Hc. rewrite Hg.
                exists s2. exists g2. exists t1. exists t.
                easy.
          }
          clear H18 H4.
          destruct H as (fn,Ha).
          specialize(isMerge_cont_Into f'0 fn T H19).
          assert(exists T' : ltt, isMerge fn T' /\ MergeInto T T').
          {
            apply isMerge_cont_Into; try easy.
            intro.
            specialize(Ha n).
            destruct Ha.
            - left. easy.
            - destruct H as (s1,(g1,(t1,(t2,(Ha,(Hb,(Hc,(Hd,He)))))))).
              rewrite Hb. rewrite Hc.
              right. exists t1. exists t2. easy.
          }
          specialize(pt_step_forward merge_cont_end merge_from_end (gtt_send s s' ys) (gtt_send s s' f') p q l r T); intros.
          assert(isgPartsC r (gtt_send s s' f')).
          {
            apply H0; try easy.
            pfold. easy.
            pfold. easy.
          }
          clear H0.
          destruct H as (T',H).
          exists T'.
          split; try easy.
          pfold. apply proj_cont with fn; try easy.
          intro.
          specialize(Ha n).
          destruct Ha.
          - left. easy.
          - destruct H0 as (s1,(g1,(t1,(t2,(Ha,(Hb,(Hc,(Hd,He)))))))).
            right.
            rewrite Ha. rewrite Hc.
            exists s1. exists g1. exists t2. 
            split. easy. split. easy.
            left. easy.
        apply proj_mon.
      apply step_mon.
  Qed.


End ltt_after_step_r.



End typ_after_step.



Section step_with_proj.


(* Build an explicit global step from dual local projections. *)
CoFixpoint force_step (G : gtt) p q l := 
  match G with
    | gtt_send s s' f => if (participant_dec s p) && (participant_dec s' q) then 
                              match f l with 
                                | Some (_, g) => g 
                                | _            => gtt_end 
                              end 
                         else gtt_send s s' (fun n => match f n with
                                | Some (st, g) => Some (st, force_step g p q l)
                                | None         => None 
                              end)
    | _ => gtt_end
  end.


Hypothesis merge_cont_send : forall g p f, isMerge g (ltt_send p f) -> forall n t, g n = Some t -> exists f', t = ltt_send p f'.
  
Hypothesis merge_cont_recv : forall g p f, isMerge g (ltt_recv p f) -> forall n t, g n = Some t -> exists f', t = ltt_recv p f'.

Hypothesis merge_label_send_b : forall g p f, isMerge g (ltt_send p f) -> forall n q f' l st, g n = Some (ltt_send q f') -> f l = Some st -> exists st', f' l = Some st'.

Lemma step_with_proj_force : forall G p q l f f' st, 
                  balancedG G -> p <> q
               -> projectionC G p (ltt_send q f) -> projectionC G q (ltt_recv p f') 
               -> f l = Some st -> gttstepC G (force_step G p q l) p q l.
Proof.
  intros G p q l f f' st H Ht H0 H1 H2.
  assert(isgPartsC p G).
  {
    pinversion H0; try easy.
    apply proj_mon.
  }
  specialize(isgPartsC_to_word p G H3); intros.
  destruct H4 as (w,(pr,Ha)).
  specialize(balanced_to_tree p pr w G H Ha); intros.
  destruct H4 as (Gl,(Hb,Hc)). clear Ha H3 H. clear w pr.
  
  revert Hc Hb H2 H1 H0.
  revert G f f' st.
  induction Gl using gtth_ind_ref; intros.
  - inversion Hb.
    - subst.  
      pinversion H0; try easy.
      apply proj_mon.
    - subst.
      pinversion H0; try easy. subst.
      pinversion H1; try easy. subst. clear H1 H0.
      specialize(H13 l). specialize(H10 l).
      rewrite H2 in H10.
      destruct H10; try easy. destruct H as (s1,(g1,(t1,(Hd,(He,Hf))))).
      rewrite Hd in H13.
      destruct H13; try easy. destruct H as (s2,(g2,(t2,(Hg,(Hh,Hi))))).
      inversion He. subst. inversion Hg. subst. clear Hg He.
      rewrite (gtt_eq (force_step (gtt_send p q f0) p q l)). simpl.
      - destruct (participant_dec p p); try congruence; intros.
        destruct (participant_dec q q); try congruence; intros.
        rewrite Hd. simpl.
       
        assert(match g2 with
          | gtt_end => gtt_end
          | gtt_send p0 q0 l0 => gtt_send p0 q0 l0
          end = g2).
        {
          destruct g2; try easy.
        }
        rewrite H. clear H.
        pfold.
        apply steq with s2; try easy.
      apply proj_mon.
      apply proj_mon.
    - subst.
      pinversion H0; try easy.
      apply proj_mon.
  - inversion Hb. subst. clear Hb.
    pinversion H0; try easy.
    - subst.
      assert False.
      apply Hc. constructor.
      easy.
    - subst.
      rename p0 into s. rename q0 into s'.
      rewrite (gtt_eq (force_step (gtt_send s s' ys) p q l)).
      simpl.
      pinversion H1; try easy. clear H0 H1. subst.
      destruct (participant_dec s p); try congruence; intros; simpl.
      pfold. constructor; try easy.
      - inversion H16; subst; try easy.
        exists n0. exists (s0, g). easy.
      - intros.
        specialize(H13 n0). specialize(H19 n0).
        destruct H13.
        - left. easy.
        - right.
          destruct H0 as (s1,(g1,(t1,(Hd,(He,Hf))))).
          rewrite Hd. rewrite Hd in H19.
          destruct H19; try easy. destruct H0 as (s2,(g2,(t2,(Hg,(Hh,Hi))))).
          inversion Hg. subst. clear Hg.
          exists s2. exists g2.
          split. easy.
          specialize(merge_cont_send f'0 q f H14 n0 t1 He). 
          destruct merge_cont_send as (ft',Hta). subst.
          specialize(merge_cont_recv f'1 p f' H20 n0 t2 Hh).
          destruct merge_cont_recv as (fs',Htb). subst.
          pclearbot.
          split.
          - pinversion Hf; try easy.
            apply proj_mon.
          - pinversion Hi; try easy.
            apply proj_mon.
      - intros.
        specialize(H19 n0). specialize(H13 n0).
        destruct H13.
        - destruct H0. rewrite H0. left. easy.
        - destruct H0 as (s1,(g1,(t1,(Hd,(He,Hf))))).
          rewrite Hd. right.
          rewrite Hd in H19.
          destruct H19; try easy.
          destruct H0 as (s2,(g2,(t2,(Hg,(Hh,Hi))))).
          inversion Hg. subst. clear Hg.
          exists s2. exists g2. exists (force_step g2 p q l).
          split. easy. split. easy. left.
          specialize(H8 n0). rewrite Hd in H8.
          destruct H8; try easy.
          destruct H0 as (s3,(g3,(g4,(Hj,(Hk,Hl))))).
          inversion Hk. subst. clear Hk.
          specialize(H n0). rewrite Hj in H.
          destruct H; try easy.
          destruct H as (s4,(g5,(Hm,Hn))). inversion Hm. subst.
          specialize(merge_cont_send f'0 q f H14 n0 t1 He).
          destruct merge_cont_send as (fa,Hta). subst.
          specialize(merge_cont_recv f'1 p f' H20 n0 t2 Hh).
          destruct merge_cont_recv as (fb,Htb). subst.
          specialize(Hn g4 fa fb).
          specialize(merge_label_send_b f'0 q f H14 n0 q fa l st He H2).
          destruct merge_label_send_b as (st',Htc).
          specialize(Hn st'). pclearbot.
          apply Hn; try easy.
          intro.
          apply Hc.
          apply ha_sendr with n0 s4 g5; try easy.
        apply proj_mon.
        apply proj_mon.
Qed.
        
Lemma step_with_proj : forall G p q l f f' st, 
                  balancedG G -> p <> q
               -> projectionC G p (ltt_send q f) -> projectionC G q (ltt_recv p f') 
               -> f l = Some st -> exists G', gttstepC G G' p q l.
Proof.
  intros. 
  specialize(step_with_proj_force G p q l f f' st); intros.
  exists(force_step G p q l).
  apply H4; try easy.
Qed.




End step_with_proj.




Section sort_with_proj.

Hypothesis merge_cont_send : forall g p f, isMerge g (ltt_send p f) -> forall n t, g n = Some t -> exists f', t = ltt_send p f'.
  
Hypothesis merge_cont_recv : forall g p f, isMerge g (ltt_recv p f) -> forall n t, g n = Some t -> exists f', t = ltt_recv p f'.

Hypothesis merge_pres_sort : forall f'0 q f f'1 p f' n, isMerge f'0 (ltt_send q f) -> isMerge f'1 (ltt_recv p f') 
      -> (forall n : fin,
         f'0 n = None /\ f'1 n = None \/
         (exists fa fb : fin -> option (sort * ltt),
            f'0 n = Some (ltt_send q fa) /\
            f'1 n = Some (ltt_recv p fb) /\
            (forall m : fin,
             fa m = None /\ fb m = None \/
             (exists (s' : sort) (t t' : ltt), fa m = Some (s', t) /\ fb m = Some (s', t'))))) 
       -> f n = None /\ f' n = None \/ (exists (s : sort) (t t' : ltt), f n = Some (s, t) /\ f' n = Some (s, t')).

(* Sort compatibility extracted from dual projections. *)
Lemma sort_with_proj : forall G p q f f', balancedG G
                    -> projectionC G p (ltt_send q f) -> projectionC G q (ltt_recv p f') 
                    -> (forall n, (f n = None /\ f' n = None) \/ (exists s t t', f n = Some (s, t) /\ f' n = Some (s, t'))).
Proof.
  intros.
  assert(isgPartsC p G).
  {
    pinversion H0; try easy.
    apply proj_mon.
  }
  specialize(isgPartsC_to_word p G H2); intros.
  destruct H3 as (w,(pr,Ha)).
  specialize(balanced_to_tree p pr w G H Ha); intros.
  destruct H3 as (Gl,(Hb,Hc)). clear Ha H2 H. clear w pr.
  revert n.
  revert H0 H1 Hb Hc. revert G f f'.
  
  induction Gl using gtth_ind_ref; intros.
  - inversion Hb.
    - subst. 
      pinversion H0; try easy.
      apply proj_mon.
    - subst.
      pinversion H0; subst; try easy.
      subst. clear H0.
      pinversion H1; try easy. 
      subst. clear H1.
      specialize(H9 n). specialize(H11 n).
      destruct H11.
      - destruct H9.
        left. easy.
        destruct H. rewrite H in H0.
        destruct H0 as (s1,(g1,(t1,Ht))). easy.
      - destruct H as (s1,(g1,(t1,(Hd,(He,Hf))))).
        rewrite Hd in H9.
        destruct H9; try easy.
        destruct H as (s2,(g2,(t2,(Hg,(Hh,Hi))))).
        inversion Hg. subst.
        right. rewrite Hh. rewrite He.
        exists s2. exists t2. exists t1. easy.
      apply proj_mon. apply proj_mon.
    - subst.
      pinversion H0; try easy.
      apply proj_mon.
  - inversion Hb. subst. clear Hb.
    pinversion H0; try easy.
    - subst.
      assert False. 
      apply Hc. constructor.
      easy.
    - subst. clear H0.
      pinversion H1; try easy. subst.
      
      assert(forall n, (f'0 n = None /\ f'1 n = None) \/ (exists fa fb, f'0 n = Some(ltt_send q fa) /\ f'1 n = Some(ltt_recv p fb) /\ (forall m, (fa m = None /\ fb m = None) \/ (exists s' t t', fa m = Some(s', t) /\ fb m = Some(s', t'))))).
      {
        intros.
        specialize(H17 n0). specialize(H12 n0). specialize(H7 n0). specialize(H n0).
        destruct H17.
        - destruct H12. left. easy.
          destruct H0. rewrite H0 in H2.
          destruct H2 as (s1,(g1,(t1,Ht))). easy.
        - destruct H0 as (s1,(g1,(t1,(Hd,(He,Hf))))).
          rewrite Hd in H12.
          destruct H12; try easy.
          destruct H0 as (s2,(g2,(t2,(Hg,(Hh,Hi))))).
          inversion Hg. subst. clear Hg.
          rewrite Hh. rewrite He.
          right.
          specialize(merge_cont_send f'0 q f H13 n0 t2 Hh).
          destruct merge_cont_send as (fa,Ht). subst.
          specialize(merge_cont_recv f'1 p f' H18 n0 t1 He).
          destruct merge_cont_recv as (fb,Ht). subst.
          exists fa. exists fb.
          pclearbot. split. easy. split. easy.
          rewrite Hd in H7.
          destruct H7; try easy.
          destruct H0 as (s3,(g3,(g4,(Hj,(Hk,Hl))))). inversion Hk. subst. clear Hk.
          rewrite Hj in H.
          destruct H; try easy.
          destruct H as (s4,(g5,(Hm,Hn))).
          inversion Hm. subst. clear Hm.
          apply Hn with g4; try easy.
          intro.
          apply Hc.
          apply ha_sendr with n0 s4 g5; try easy.
      }
      clear H17 H12 H7 Hc H H1. clear merge_cont_send merge_cont_recv.
      clear H9 H14 H5 H6 H8 H4 H10 H11. clear p0 q0 xs ys.
      apply merge_pres_sort with f'0 q f'1 p; try easy.
    apply proj_mon.
    apply proj_mon.
Qed.

End sort_with_proj.











End gprojstep.

#[export] Hint Resolve proj_mon : mon.
#[export] Hint Resolve step_mon : mon.