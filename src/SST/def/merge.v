From mathcomp Require Import ssreflect.seq all_ssreflect.
Require Import List String Coq.Arith.PeanoNat Coq.Arith.Arith Relations ZArith Datatypes Setoid Morphisms Coq.Logic.Decidable Coq.Program.Basics Coq.Init.Datatypes.
Import ListNotations. 
Open Scope list_scope.
From Paco Require Import paco.
Require Import def.header def.tree  def.global def.part def.projection def.subtype.

(* Merge interface and assumptions.
   `good_merge` packages the algebraic properties required by
   projection soundness/completeness and typing preservation. *)


  Section good_merge.

  Class good_merge := {
    (* \Pi T_i = T *)
    isMerge : (fin -> option ltt) -> ltt -> Prop;
    
    merge_into_recv : forall g p f, isMerge g (ltt_recv p f) -> forall n s t, f n = Some(s, t) -> isMerge (through_merge_r g n) t;
    
    (* Label compatibility constraints for send merges. *)
    merge_label_send : forall g p f, isMerge g (ltt_send p f) -> forall n q f' l st, g n = Some (ltt_send q f') -> f' l = Some st -> exists st', f l = Some st';
    merge_into_send : forall g p f, isMerge g (ltt_send p f) -> forall n s t, f n = Some(s, t) -> isMerge (through_merge_s g n) t;
    merge_label_send_b : forall g p f, isMerge g (ltt_send p f) -> forall n q f' l st, g n = Some (ltt_send q f') -> f l = Some st -> exists st', f' l = Some st';
    
    (* `MergeInto T T'` means "T' is a merged refinement of T". *)
    MergeInto : ltt -> ltt -> Prop;
    
    (* Any selected merged branch refines the overall merged type. *)
    isMerge_to_Into : forall f T l T', isMerge f T -> f l = Some T' -> MergeInto T T';
    
    MergeInto_end : MergeInto ltt_end ltt_end;
    
    MergeInto_send : forall p fl fr, (forall n, (fl n = None /\ fr n = None) \/ (exists s t t', fl n = Some(s, t) /\ fr n = Some(s, t') /\ MergeInto t t')) -> MergeInto (ltt_send p fl) (ltt_send p fr);
    MergeInto_recv : forall p fl fr, (forall n, (fl n = None /\ fr n = None) \/ (exists s t t', fl n = Some(s, t) /\ fr n = Some(s, t') /\ MergeInto t t')) -> MergeInto (ltt_recv p fl) (ltt_recv p fr);
    isMerge_cont_Into : forall f f' T, isMerge f T -> (forall n, (f n = None /\ f' n = None) \/ (exists t t', f n = Some t /\ f' n = Some t' /\ MergeInto t t')) -> exists T', isMerge f' T' /\ MergeInto T T';
    
    MergeInto_to_subtypeC : forall T T', MergeInto T T' -> subtypeC T T';
    
    Merge_Sort : forall f'0 q f f'1 p f' n, isMerge f'0 (ltt_send q f) -> isMerge f'1 (ltt_recv p f') 
      -> (forall n : fin,
         f'0 n = None /\ f'1 n = None \/
         (exists fa fb : fin -> option (sort * ltt),
            f'0 n = Some (ltt_send q fa) /\
            f'1 n = Some (ltt_recv p fb) /\
            (forall m : fin,
             fa m = None /\ fb m = None \/
             (exists (s' : sort) (t t' : ltt), fa m = Some (s', t) /\ fb m = Some (s', t'))))) 
       -> f n = None /\ f' n = None \/ (exists (s : sort) (t t' : ltt), f n = Some (s, t) /\ f' n = Some (s, t'));
    
  (*   isMerge_bisim : forall f' f'0 T T' r,
      (forall n : fin,
       f' n = None /\ f'0 n = None \/
       (exists t t' : ltt, f' n = Some t /\ f'0 n = Some t' /\ r t t')) ->
      isMerge f' T ->
      isMerge f'0 T' -> 
      paco2 bisim r T T' *)
  
  }.
  
    
  
  Proposition Skip_merge_cont_end `{good_merge} : forall f n t, isMerge f ltt_end -> f n = Some t -> t = ltt_end.
  Proof.
    intros.
    specialize(isMerge_to_Into f ltt_end n t H0 H1); intros.
    specialize(MergeInto_to_subtypeC ltt_end t H2); intros.
    pinversion H3; try easy.
    apply sub_mon.
  Qed.
  
  Proposition Skip_merge_from_end `{good_merge} : forall f n t, isMerge f t -> f n = Some ltt_end -> t = ltt_end.
  Proof.
    intros.
    specialize(isMerge_to_Into f t n ltt_end H0 H1); intros.
    specialize(MergeInto_to_subtypeC t ltt_end H2); intros.
    pinversion H3; try easy.
    apply sub_mon.
  Qed.

  Proposition Skip_merge_cont_recv `{good_merge} : forall g p f, isMerge g (ltt_recv p f) -> forall n t, g n = Some t -> exists f', t = ltt_recv p f'.
  Proof.
    intros.
    specialize(isMerge_to_Into g (ltt_recv p f) n t H0 H1); intros.
    specialize(MergeInto_to_subtypeC (ltt_recv p f) t H2); intros.
    pinversion H3; try easy.
    - subst. exists ys. easy.
    - apply sub_mon.
  Qed.
  
  Proposition Skip_merge_label_recv `{good_merge} : forall g p f, isMerge g (ltt_recv p f) -> forall n q f' l st, g n = Some (ltt_recv q f') -> f' l = Some st -> exists st', f l = Some st'.
  Proof.
    intros.
    specialize(isMerge_to_Into g (ltt_recv p f) n (ltt_recv q f') H0 H1); intros.
    specialize(MergeInto_to_subtypeC (ltt_recv p f) (ltt_recv q f') H3); intros.
    pinversion H4.
    subst.
    specialize(H6 l). rewrite H2 in H6.
    destruct H6; try easy.
    destruct H5 as (s1,(t1,(t2,(Ha,(Hb,Hd))))).
    exists (s1,t1). easy.
    apply sub_mon.
  Qed.
  
  Proposition Skip_merge_cont_send `{good_merge} : forall g p f, isMerge g (ltt_send p f) -> forall n t, g n = Some t -> exists f', t = ltt_send p f'.
  Proof.
    intros.
    specialize(isMerge_to_Into g (ltt_send p f) n t H0 H1); intros.
    specialize(MergeInto_to_subtypeC (ltt_send p f) t H2); intros.
    pinversion H3; try easy.
    - subst. exists ys. easy.
    - apply sub_mon.
  Qed.
    
  
  Proposition Skip_MergeInto_end_r `{good_merge} : forall t, MergeInto ltt_end t -> t = ltt_end.
  Proof.
    intros.
    specialize(MergeInto_to_subtypeC ltt_end t H0); intros.
    pinversion H1; try easy.
    apply sub_mon.
  Qed.
  
  Hint Resolve Skip_merge_cont_end Skip_merge_from_end Skip_merge_cont_recv Skip_merge_cont_send Skip_merge_label_recv : Skip_GM.
  Ltac skgm := eauto with Skip_GM.
  
  Definition projC `{good_merge} := projectionC isMerge.
  
  Lemma typ_after_step_p `{good_merge} : forall G G' p q l f, balancedG G -> regGtt G -> gttstepC G G' p q l -> projC G p (ltt_send q f) -> exists s t, f l = Some(s, t) /\ projC G' p t.
  Proof.
    intros.
    apply ltt_after_step_p with G q; try easy; try skgm.
    - apply merge_label_send.
    - apply merge_into_send.
  Qed.
  
  Lemma typ_after_step_q `{good_merge} : forall G G' p q l f, balancedG G -> regGtt G -> gttstepC G G' p q l -> projC G q (ltt_recv p f) -> exists s t, f l = Some(s, t) /\ projC G' q t.
  Proof.
    intros.
    apply ltt_after_step_q with G p; try easy; try skgm.
    - apply merge_into_recv.
  Qed.
  
  Lemma typ_after_step_r `{good_merge} : forall G G' p q r l T, balancedG G -> regGtt G -> gttstepC G G' p q l -> p <> r -> q <> r -> projC G r T -> exists T', projC G' r T' /\ subtypeC T T'.
  Proof.
    intros.
    assert(exists T' : ltt, projC G' r T' /\ MergeInto T T').
    apply ltt_after_step_r with G p q l; try easy; try skgm.
    - apply MergeInto_end.
    - apply MergeInto_send.
    - apply MergeInto_recv.
    - apply isMerge_cont_Into.
    - apply isMerge_to_Into.
    destruct H6 as (T',Ha).
    exists T'. split. easy.
    apply MergeInto_to_subtypeC. easy.
  Qed.
  
  Lemma proj_to_step `{good_merge} : forall G p q l f f' st, 
                  balancedG G -> p <> q 
               -> projC G p (ltt_send q f) -> projC G q (ltt_recv p f') 
               -> f l = Some st -> exists G', gttstepC G G' p q l.
  Proof.
    apply step_with_proj; try easy; try skgm.
    - apply merge_label_send_b.
  Qed.
  
  Lemma proj_sort `{good_merge} : forall G p q f f', balancedG G
                      -> projC G p (ltt_send q f) -> projC G q (ltt_recv p f') 
                      -> (forall n, (f n = None /\ f' n = None) \/ (exists s t t', f n = Some (s, t) /\ f' n = Some (s, t'))).
  Proof.
    apply sort_with_proj; try easy; try skgm.
    apply Merge_Sort.
  Qed.
  

  Lemma proj_shape_p `{good_merge} : forall G G' p q l T,
        projC G p T -> 
        gttstepC G G' p q l -> 
        exists f, T = ltt_send q f.
  Proof.
    intros.
    specialize(step_to_pt G G' p q l); intros. fill_triv.
    revert H1 H0. revert T l q G'.
    induction H2; intros.
    - pinversion H0; try mon_easy; subst; try easy.
      - assert False.
        apply H2. constructor.
        easy.
      - pinversion H1; subst; try mon_easy; try easy.
        eexists. easy.
    - pinversion H0; try mon_easy; subst; try easy.
      - assert False.
        apply H2. constructor.
        easy.
      - pinversion H1; subst; try mon_easy; try easy.
    - pinversion H4; subst; try mon_easy; try easy.
      pinversion H5; subst; try mon_easy; try easy.
      - assert False.
        apply H6.
        apply pac_sendr with n s g; try easy. easy.
      - specialize(H20 n). specialize(H21 n). specialize(H24 n). rewrite H2 in H20 H21 H24.
        destruct H20; try easy. destruct H21; try easy. destruct H24; try easy. destruct_exists_and.
        invert_all_some. pclearbot.
        specialize(IHisgPartsC x1 l q0 x4).
        assert_concl_of IHisgPartsC as Ha. apply IHisgPartsC; try easy.
        - destruct H23; try easy.
        - destruct Ha. subst.
          specialize(isMerge_to_Into f'0 T n (ltt_send q0 x)); intros. fill_triv.
          specialize(MergeInto_to_subtypeC T (ltt_send q0 x)); intros. fill_triv.
          pinversion H7; try mon_easy. exists xs. easy.
  Qed.

  Lemma proj_shape_q `{good_merge} : forall G G' p q l T,
        projC G q T -> 
        gttstepC G G' p q l -> 
        exists f, T = ltt_recv p f.
  Proof.
    intros.
    specialize(step_to_pt_r G G' p q l); intros. fill_triv.
    revert H1 H0. revert T l p G'.
    induction H2; intros.
    - pinversion H0; try mon_easy; subst; try easy.
      - assert False.
        apply H2. constructor.
        easy.
      - pinversion H1; subst; try mon_easy; try easy.
    - pinversion H0; try mon_easy; subst; try easy.
      - assert False.
        apply H2. constructor.
        easy.
      - pinversion H1; subst; try mon_easy; try easy.
        eexists. easy.
    - pinversion H4; subst; try mon_easy; try easy.
      pinversion H5; subst; try mon_easy; try easy.
      - assert False.
        apply H6.
        apply pac_sendr with n s g; try easy. easy.
      - specialize(H20 n). specialize(H21 n). specialize(H24 n). rewrite H2 in H20 H21 H24.
        destruct H20; try easy. destruct H21; try easy. destruct H24; try easy. destruct_exists_and.
        invert_all_some. pclearbot.
        specialize(IHisgPartsC x1 l p0 x4).
        assert_concl_of IHisgPartsC as Ha. apply IHisgPartsC; try easy.
        - destruct H23; try easy.
        - destruct Ha. subst.
          specialize(isMerge_to_Into f'0 T n (ltt_recv p0 x)); intros. fill_triv.
          specialize(MergeInto_to_subtypeC T (ltt_recv p0 x)); intros. fill_triv.
          pinversion H7; try mon_easy. exists xs. easy.
  Qed.  
  
  
  Inductive slist_merge {R} : slist ltt -> ltt -> Prop :=
      | slm_x  : forall T, slist_merge (slist_x T) T
      | slm_nx : forall T xs, slist_merge xs T -> slist_merge (slist_xs None xs) T
      | slm_xs : forall T T' T'' xs, R T T' T'' -> slist_merge xs T'' -> slist_merge (slist_xs (Some T') xs) T.
  
  Section coind_fmer.
  
  
    Inductive coind_fmer_in (R : ltt -> ltt -> Prop) : ltt -> ltt -> Prop :=
      | fmer_in_end  : coind_fmer_in R ltt_end ltt_end 
      | fmer_in_send : forall p f f', (forall n, (f n = None /\ f' n = None) \/ (exists s t t', f n = Some(s, t) /\ f' n = Some(s, t') /\ R t t')) -> coind_fmer_in R (ltt_send p f) (ltt_send p f')
      | fmer_in_recv : forall p f f', (forall n, (f' n = None) \/ (exists s t t', f n = Some(s, t) /\ f' n = Some(s, t') /\ R t t')) -> coind_fmer_in R (ltt_recv p f) (ltt_recv p f').
    
    Lemma fmer_in_mon : monotone2 coind_fmer_in.
    Proof.
      unfold monotone2; intros.
      induction IN.
      - constructor.
      - constructor.
        intro.
        specialize(H n).
        destruct H.
        - left. easy.
        - right.
          destruct H as (s1,(t1,(t2,(Ha,(Hb,Hc))))).
          rewrite Ha. rewrite Hb.
          exists s1. exists t1. exists t2.
          split. easy. split. easy.
          apply LE; try easy.
      - constructor.
        intro.
        specialize(H n).
        destruct H.
        - left. easy.
        - right.
          destruct H as (s1,(t1,(t2,(Ha,(Hb,Hc))))).
          rewrite Ha. rewrite Hb.
          exists s1. exists t1. exists t2.
          split. easy. split. easy.
          apply LE; try easy.
    Qed.
    
    (* explicit MergeInto *)
    Definition full_merge_in T T' := paco2 coind_fmer_in bot2 T T'.
    
    Lemma MergeInto_end_f : full_merge_in ltt_end ltt_end.
    Proof.
      pfold. constructor.
    Qed.
    
    Lemma MergeInto_send_f : forall p fl fr, (forall n, (fl n = None /\ fr n = None) \/ (exists s t t', fl n = Some(s, t) /\ fr n = Some(s, t') /\ full_merge_in t t')) -> full_merge_in (ltt_send p fl) (ltt_send p fr).
    Proof.
      intros.
      pfold. constructor.
      intro.
      specialize(H n). 
      destruct H.
      - left. easy.
      - right.
        destruct H as (s1,(t1,(t2,(Ha,(Hb,Hc))))).
        rewrite Ha. rewrite Hb.
        exists s1. exists t1. exists t2.
        split. easy. split. easy. left. easy.
    Qed.
    
    Lemma MergeInto_recv_f : forall p fl fr, (forall n, (fl n = None /\ fr n = None) \/ (exists s t t', fl n = Some(s, t) /\ fr n = Some(s, t') /\ full_merge_in t t')) -> full_merge_in (ltt_recv p fl) (ltt_recv p fr).
    Proof.
      intros.
      pfold. constructor.
      intro.
      specialize(H n).
      destruct H.
      - left. easy.
      - right.
        destruct H as (s1,(t1,(t2,(Ha,(Hb,Hc))))).
        rewrite Ha. rewrite Hb.
        exists s1. exists t1. exists t2.
        split. easy. split. easy. left. easy.
    Qed.
    
    Lemma MergeInto_to_subtypeC_f : forall T T', full_merge_in T T' -> subtypeC T T'.
    Proof.
      pcofix CIH.
      intros.
      pinversion H0.
      - subst. pfold. constructor.
      - subst. pfold. constructor.
        intro.
        specialize(H n). 
        destruct H.
        - left. easy.
        - right.
          destruct H as (s1,(t1,(t2,(Ha,(Hb,Hc))))).
          rewrite Ha. rewrite Hb.
          exists s1. exists t1. exists t2.
          split. easy. split. easy.
          right. pclearbot.
          apply CIH; try easy.
      - subst. pfold. constructor.
        intro.
        specialize(H n). 
        destruct H.
        - left. easy.
        - right.
          destruct H as (s1,(t1,(t2,(Ha,(Hb,Hc))))).
          rewrite Ha. rewrite Hb.
          exists s1. exists t1. exists t2.
          split. easy. split. easy.
          right. pclearbot.
          apply CIH; try easy.
      - apply fmer_in_mon.
    Qed.
    
    
    
    
    
    Inductive coind_fmer_fun (R : ltt -> ltt -> ltt -> Prop) : ltt -> ltt -> ltt -> Prop :=
      | cfmer_end  : coind_fmer_fun R ltt_end ltt_end ltt_end 
      | cfmer_send : forall p f1 f2 f3, (forall n, (f1 n = None /\ f2 n = None /\ f3 n = None) \/
                                                   (exists s t1 t2 t3, f1 n = Some(s, t1) /\ f2 n = Some(s, t2) /\ f3 n = Some(s, t3) /\ R t1 t2 t3)) -> coind_fmer_fun R (ltt_send p f1) (ltt_send p f2) (ltt_send p f3)
      | cfmer_recv : forall p f1 f2 f3, (forall n, (f1 n = None /\ f2 n = None /\ f3 n = None) \/
                                                   (exists st, f1 n = Some st /\ f2 n = Some st /\ f3 n = None) \/
                                                   (exists st, f1 n = Some st /\ f2 n = None /\ f3 n = Some st) \/
                                                   (exists s t1 t2 t3, f1 n = Some(s, t1) /\ f2 n = Some(s, t2) /\ f3 n = Some(s, t3) /\ R t1 t2 t3)) -> coind_fmer_fun R (ltt_recv p f1) (ltt_recv p f2) (ltt_recv p f3).
    
    Lemma fmer_mon : monotone3 coind_fmer_fun.
    Proof.
      unfold monotone3; intros.
      induction IN; intros.
      - constructor.
      - constructor.
        intro.
        specialize(H n).
        destruct H.
        - left. easy.
        - right.
          destruct H as (s1,(t1,(t2,(t3,(Ha,(Hb,(Hc,Hd))))))).
          exists s1. exists t1. exists t2. exists t3.
          split. easy. split. easy. split. easy.
          apply LE; try easy.
      - constructor.
        intro.
        specialize(H n).
        destruct H.
        - left. easy.
        - destruct H. right. left. easy.
        - destruct H. right. right. left. easy.
        - right. right. right.
          destruct H as (s1,(t1,(t2,(t3,(Ha,(Hb,(Hc,Hd))))))).
          exists s1. exists t1. exists t2. exists t3.
          split. easy. split. easy. split. easy.
          apply LE; try easy.
    Qed.
    
    Definition full_merge2 T T' T'' := paco3 coind_fmer_fun bot3 T T' T''.
    
    
    Definition full_merge f T := exists zs, (forall n, onth n zs = f n) /\ @slist_merge full_merge2 zs T.
    
    Lemma merge_into_recv_s : forall g p f, full_merge g (ltt_recv p f) -> forall n s t, f n = Some(s, t) -> full_merge (through_merge_r g n) t.
    Proof.
      intros.
      destruct H as (zs, (Ha,Hb)).
      revert Ha Hb H0. revert n s t f g.
      induction zs; intros. 
      - inversion Hb. subst. clear Hb.
        unfold through_merge_r.
        exists (slist_x t).
        split.
        - intro.
          specialize(Ha n0). rewrite (esym Ha).
          destruct n0; try easy.
          simpl. rewrite H0. easy.
        - constructor.
      - inversion Hb.
        - subst.
          specialize(IHzs n s t f (fun n => g (S n))).
          assert(full_merge (through_merge_r (fun n : fin => g n.+1) n) t).
          {
            apply IHzs; try easy.
            intro. 
            specialize(Ha (S n0)); try easy.
          }
          inversion H. destruct H1.
          exists (slist_xs None x).
          split.
          - intro. 
            destruct n0.
            - specialize(Ha 0). unfold through_merge_r.
              rewrite (esym Ha). simpl in *. easy.
            - specialize(H1 n0); try easy.
          - constructor; try easy.
        - subst.
          pinversion H2; try easy. subst.
          specialize(H6 n). rewrite H0 in H6.
          destruct H6; try easy.
          destruct H.
          - destruct H as (st,(Hc,(Hd,He))).
            inversion Hc. subst. clear Hc. clear Hb H2.
            exists (slist_x t).
            split.
            - intro.
              unfold through_merge_r.
              destruct n0.
              - simpl in *.
                specialize(Ha 0). rewrite (esym Ha).
                simpl. rewrite Hd. easy.
              - simpl in *.
                specialize(Ha (S n0)).
                simpl in Ha. rewrite (esym Ha).
                clear Hd H0 Ha IHzs.
                clear f f2 s g t.
                revert He H4. revert n n0 f3.
                induction zs; intros.
                - inversion H4. subst.
                  destruct n0; try easy. simpl. rewrite He. easy.
                - inversion H4. subst.
                  - destruct n0; try easy.
                    specialize(IHzs n n0 f3 He H2). easy.
                  pinversion H1. subst.
                  specialize(H9 n). rewrite He in H9.
                  destruct H9.
                  - destruct H as (Ha,(Hb,Hc)). clear Ha.
                    destruct n0; try easy.
                    - simpl. rewrite Hb. easy.
                    - specialize(IHzs n n0 f0 Hc H3). easy.
                  - destruct H. destruct H; try easy.
                    destruct H. destruct H; try easy.
                    destruct H as (s1,(t1,(t2,(t3,Hb)))). easy.
                apply fmer_mon.
              - constructor.
          - destruct H.
            destruct H as (st,(Hc,(Hd,He))).
            inversion Hc. subst.
            specialize(IHzs n s t f3 (fun n => g (S n))).
            assert(full_merge (through_merge_r (fun n : fin => g n.+1) n) t).
            {
              apply IHzs; try easy.
              intro. specialize(Ha (S n0)). easy.
            }
            inversion H; try easy. destruct H1.
            exists (slist_xs None x); try easy.
            split.
            - intro. 
              destruct n0.
              - unfold through_merge_r. simpl in *.
                specialize(Ha 0). rewrite (esym Ha). simpl. rewrite Hd. easy.
              - specialize(H1 n0). easy.
            - constructor; try easy.
          - destruct H as (s1,(t1,(t2,(t3,(Hc,(Hd,(He,Hf))))))).
            inversion Hc. subst. clear Hc.
            specialize(IHzs n s1 t3 f3 (fun n => g (S n))).
            assert(full_merge (through_merge_r (fun n : fin => g n.+1) n) t3).
            {
              apply IHzs; try easy.
              intro.
              specialize(Ha (S n0)); try easy.
            }
            clear IHzs.
            inversion H.
            exists (slist_xs (Some t2) x). destruct H1.
            split.
            - intro.
              destruct n0.
              - unfold through_merge_r.
                simpl in *.
                specialize(Ha 0). rewrite (esym Ha). simpl.
                rewrite Hd. easy.
              - specialize(H1 n0). easy.
            - apply slm_xs with t3; try easy.
              destruct Hf; try easy.
          apply fmer_mon.
    Qed.
    
    Lemma merge_label_send_s : forall g p f, full_merge g (ltt_send p f) -> forall n q f' l st, g n = Some (ltt_send q f') -> f' l = Some st -> exists st', f l = Some st'.
    Proof.
      intros g p f H.
      destruct H as (zs,(Ha,Hb)).
      revert Ha Hb. revert g f.
      induction zs; intros.
      - inversion Hb. subst.
        assert (n = 0).
        {
          destruct n; try easy.
          specialize(Ha (S n)). simpl in *. rewrite H in Ha. easy.
        }
        subst.
        specialize(Ha 0). rewrite H in Ha. 
        inversion Ha. subst. exists st. easy.
      - inversion Hb.
        - subst.
          specialize(IHzs (fun n => g (S n)) f).
          assert(forall (n : fin) q  (f' : fin -> option (sort * ltt))
         (l : fin) (st : sort * ltt),
       (fun n0 : fin => g n0.+1) n = Some (ltt_send q f') ->
       f' l = Some st -> exists st' : sort * ltt, f l = Some st').
          {
            apply IHzs; try easy.
            intro.
            specialize(Ha (S n0)). easy.
          }
          clear IHzs.
          destruct n.
          - specialize(Ha 0). rewrite H in Ha. easy.
          - specialize(H1 n q f'). apply H1 with st; try easy.
        - subst. clear Hb.
          pinversion H3; try easy. subst.
          specialize(IHzs (fun n => g (S n)) f3).
          assert(forall (n : fin) q (f' : fin -> option (sort * ltt))
         (l : fin) (st : sort * ltt),
       (fun n0 : fin => g n0.+1) n = Some (ltt_send q f') ->
       f' l = Some st -> exists st' : sort * ltt, f3 l = Some st').
          {
            apply IHzs; try easy.
            intro.
            specialize(Ha (S n0)); try easy.
          }
          clear IHzs.
          destruct n.
          - specialize(Ha 0). rewrite H in Ha.
            inversion Ha. subst. clear Ha.
            specialize(H7 l). rewrite H0 in H7.
            destruct H7; try easy.
            destruct H2 as (s1,(t1,(t2,(t3,(Ha,(Hb,(Hc,Hd))))))).
            inversion Hb. subst. clear Hb.
            exists (s1, t1). easy.
          - specialize(H1 n q f' l st H H0).
            destruct H1 as (sta,Ht).
            specialize(H7 l). rewrite Ht in H7.
            destruct H7; try easy.
            destruct H1 as (s1,(t1,(t2,(t3,(Hb,(Hc,(Hd,He))))))).
            inversion Hd. subst. clear Hd. 
            exists (s1, t1). easy.
        apply fmer_mon.
    Qed.
    
    Lemma merge_label_send_b_s : forall g p f, full_merge g (ltt_send p f) -> forall n q f' l st, g n = Some (ltt_send q f') -> f l = Some st -> exists st', f' l = Some st'.
    Proof.
      intros g p f H.
      destruct H as (zs, (Ha,Hb)).
      revert Ha Hb. revert g f.
        
      induction zs; intros.
      - inversion Hb. subst.
        assert (n = 0).
        {
          destruct n; try easy.
          specialize(Ha (S n)). simpl in *. rewrite H in Ha. easy.
        }
        subst.
        specialize(Ha 0). rewrite H in Ha. 
        inversion Ha. subst. exists st. easy.
      - inversion Hb.
        - subst.
          specialize(IHzs (fun n => g (S n)) f).
          assert(forall (n : fin) q (f' : fin -> option (sort * ltt)) 
         (l : fin) (st : sort * ltt),
       (fun n0 : fin => g n0.+1) n = Some (ltt_send q f') ->
       f l = Some st -> exists st' : sort * ltt, f' l = Some st').
          {
            apply IHzs; try easy.
            intro.
            specialize(Ha (S n0)). easy.
          }
          clear IHzs.
          destruct n.
          - specialize(Ha 0). rewrite H in Ha. easy.
          - specialize(H1 n q f'). apply H1 with st; try easy.
        - subst. clear Hb.
          pinversion H3; try easy. subst.
          specialize(IHzs (fun n => g (S n)) f3).
          assert(forall (n : fin) q (f' : fin -> option (sort * ltt)) 
         (l : fin) (st : sort * ltt),
       (fun n0 : fin => g n0.+1) n = Some (ltt_send q f') ->
       f3 l = Some st -> exists st' : sort * ltt, f' l = Some st').
          {
            apply IHzs; try easy.
            intro.
            specialize(Ha (S n0)); try easy.
          }
          clear IHzs H3.
          destruct n.
          - specialize(Ha 0). rewrite H in Ha.
            inversion Ha. subst. clear Ha.
            specialize(H7 l). rewrite H0 in H7.
            destruct H7; try easy.
            destruct H2 as (s1,(t1,(t2,(t3,(Ha,(Hb,(Hc,Hd))))))).
            exists (s1, t2). easy.
          - specialize(H7 l). rewrite H0 in H7.
            destruct H7; try easy.
            destruct H2 as (s1,(t1,(t2,(t3,(Hb,(Hc,(Hd,He))))))).
            specialize(H1 n q f' l (s1, t3)).
            apply H1; try easy.
        apply fmer_mon.
    Qed.
    
    Lemma merge_into_send_s : forall g p f, full_merge g (ltt_send p f) -> forall n s t, f n = Some(s, t) -> full_merge (through_merge_s g n) t.
    Proof.
     intros.
      destruct H as (zs, (Ha,Hb)).
      revert Ha Hb H0. revert n s t f g.
      induction zs; intros. 
      - inversion Hb. subst. clear Hb.
        unfold through_merge_s.
        exists (slist_x t).
        split.
        - intro.
          specialize(Ha n0). rewrite (esym Ha).
          destruct n0; try easy.
          simpl. rewrite H0. easy.
        - constructor.
      - inversion Hb.
        - subst.
          specialize(IHzs n s t f (fun n => g (S n))).
          assert(full_merge (through_merge_s (fun n : fin => g n.+1) n) t).
          {
            apply IHzs; try easy.
            intro. 
            specialize(Ha (S n0)); try easy.
          }
          inversion H. destruct H1.
          exists (slist_xs None x).
          split.
          - intro. 
            destruct n0.
            - specialize(Ha 0). unfold through_merge_s.
              rewrite (esym Ha). simpl in *. easy.
            - specialize(H1 n0); try easy.
          - constructor; try easy.
        - subst.
          pinversion H2; try easy. subst.
          specialize(H6 n). rewrite H0 in H6.
          destruct H6; try easy.
          destruct H as (s1,(t1,(t2,(t3,(Hc,(Hd,(He,Hf))))))).
          - inversion Hc. subst. clear Hc. clear Hb H2.
   
            specialize(IHzs n s1 t3 f3 (fun n => g (S n))).
            assert(full_merge (through_merge_s (fun n : fin => g n.+1) n) t3).
            {
              apply IHzs; try easy.
              intro. specialize(Ha (S n0)). easy.
            }
            inversion H; try easy. destruct H1.
            exists (slist_xs (Some t2) x); try easy.
            split.
            - intro. 
              destruct n0.
              - unfold through_merge_s.
                simpl in *.
                specialize(Ha 0). rewrite (esym Ha). simpl.
                rewrite Hd. easy.
              - specialize(H1 n0). easy.
            - apply slm_xs with t3; try easy.
              destruct Hf; try easy.
          apply fmer_mon.
    Qed.
    
    Lemma full_merge_in_refl : forall T, full_merge_in T T.
    Proof.
      pcofix CIH; intros.
      destruct T.
      - pfold.
        constructor.
      - pfold.
        constructor.
        intros.
        destruct o.
        - right. destruct p0. exists s. exists l. exists l.
          split. easy. split. easy. right.
          apply CIH; try easy.
        - left. easy.
      - pfold.
        constructor.
        intros.
        destruct o.
        - right. destruct p0. exists s. exists l. exists l.
          split. easy. split. easy. right.
          apply CIH; try easy.
        - left. easy.
    Qed.
    
    Lemma fmer2_to_in_l : forall T T' T'', full_merge2 T T' T'' -> full_merge_in T T'.
    Proof.
      pcofix CIH; intros.
      pinversion H0.
      - subst. pfold. constructor.
      - subst. pfold. constructor.
        intros.
        specialize(H n).
        destruct H. left. easy.
        destruct H as (s1,(t1,(t2,(t3,(Ha,(Hb,(Hc,Hd))))))).
        right. exists s1. exists t1. exists t2.
        split. easy. split. easy.
        right. pclearbot. apply CIH with t3; try easy.
      - subst. pfold. constructor.
        intros.
        specialize(H n).
        destruct H.
        - left. easy.
        - destruct H.
          destruct H as (st,(Ha,(Hb,Hc))).
          right. rewrite Ha. rewrite Hb. destruct st.
          exists s. exists l. exists l.
          split. easy. split. easy.
          left. 
          specialize(full_merge_in_refl l); intros.
          specialize(paco2_mon). unfold monotone2. intros.
          apply H1 with (r := bot2); try easy.
        - destruct H.
          destruct H as (st,(Ha,(Hb,Hc))).
          left. easy.
        - destruct H as (s1,(t1,(t2,(t3,(Ha,(Hb,(Hc,Hd))))))).
          right. rewrite Ha. rewrite Hb.
          exists s1. exists t1. exists t2.
          split. easy. split. easy.
          pclearbot.
          right. apply CIH with t3; try easy.
      apply fmer_mon.
    Qed.
    
    Lemma fmer2_to_in_r : forall T T' T'', full_merge2 T T' T'' -> full_merge_in T T''.
    Proof.
      pcofix CIH; intros.
      pinversion H0.
      - subst. pfold. constructor.
      - subst. pfold. constructor.
        intros.
        specialize(H n).
        destruct H. left. easy.
        destruct H as (s1,(t1,(t2,(t3,(Ha,(Hb,(Hc,Hd))))))).
        right. exists s1. exists t1. exists t3.
        split. easy. split. easy.
        right. pclearbot. apply CIH with t2; try easy.
      - subst. pfold. constructor.
        intros.
        specialize(H n).
        destruct H.
        - left. easy.
        - destruct H.
          destruct H as (st,(Ha,(Hb,Hc))).
          left. easy.
        - destruct H.
          destruct H as (st,(Ha,(Hb,Hc))). 
          right. rewrite Ha. rewrite Hc. destruct st.
          exists s. exists l. exists l.
          split. easy. split. easy.
          left. 
          specialize(full_merge_in_refl l); intros.
          specialize(paco2_mon). unfold monotone2. intros.
          apply H1 with (r := bot2); try easy.
        - destruct H as (s1,(t1,(t2,(t3,(Ha,(Hb,(Hc,Hd))))))).
          right. rewrite Ha. rewrite Hc.
          exists s1. exists t1. exists t3.
          split. easy. split. easy.
          pclearbot.
          right. apply CIH with t2; try easy.
      apply fmer_mon.
    Qed.
    
    Lemma full_merge_in_trans : forall T T' T'', full_merge_in T T' -> full_merge_in T' T'' -> full_merge_in T T''.
    Proof.
      pcofix CIH; intros.
      pinversion H0.
      - subst.
        pinversion H1; try easy.
        pfold. constructor.
        apply fmer_in_mon.
      - subst.
        pinversion H1; try easy. subst.
        pfold. constructor.
        clear H0 H1.
        intro.
        specialize(H5 n). specialize(H n).
        destruct H.
        - destruct H5. left. easy.
          destruct H. destruct H0 as (s1,(t1,(t2,Ha))). rewrite H1 in Ha. easy.
        - destruct H as (s1,(t1,(t2,(Ha,(Hb,Hc))))).
          rewrite Hb in H5.
          destruct H5; try easy. destruct H as (s2,(t3,(t4,(Hd,(He,Hf))))).
          rewrite Ha. rewrite He.
          inversion Hd. subst.
          right. exists s2. exists t1. exists t4.
          split. easy. split. easy.
          pclearbot.
          right. apply CIH with t3; try easy.
        apply fmer_in_mon.
      - subst.
        pinversion H1; try easy. subst.
        pfold. constructor.
        clear H0 H1.
        intro.
        specialize(H5 n). specialize(H n).
        destruct H5.
        - left. easy.
        - destruct H0 as (s1,(t1,(t2,(Ha,(Hb,Hc))))).
          rewrite Ha in H.
          destruct H; try easy. destruct H as (s2,(t3,(t4,(Hd,(He,Hf))))).
          rewrite Hb. rewrite Hd.
          inversion He. subst.
          right. exists s2. exists t3. exists t2.
          split. easy. split. easy.
          pclearbot.
          right. apply CIH with t4; try easy.
        apply fmer_in_mon.
      apply fmer_in_mon.
    Qed.
        
    
    Lemma isMerge_to_Into_s : forall f T l T', full_merge f T -> f l = Some T' -> full_merge_in T T'.
    Proof.
      intros.
      destruct H as (ys,(Ha,Hb)).
      revert Ha Hb H0. revert T l T' f.
      induction ys; intros.
      - inversion Hb. subst.
        specialize(Ha l). rewrite H0 in Ha. destruct l; try easy.
        inversion Ha. subst.
        apply full_merge_in_refl; try easy.
      - inversion Hb.
        - subst. clear Hb.
          destruct l; try easy.
          - specialize(Ha 0). rewrite H0 in Ha. easy.
          - apply IHys with l (fun n => f (S n)); try easy.
            intro. specialize(Ha (S n)); try easy.
        - subst. clear Hb.
          destruct l.
          - specialize(Ha 0). rewrite H0 in Ha.
            inversion Ha. subst.
            apply fmer2_to_in_l with T''; try easy.
          - specialize(IHys T'' l T' (fun n => f (S n))).
            assert(full_merge_in T'' T').
            {
              apply IHys; try easy.
              intro.
              specialize(Ha (S n)); try easy.
            }
            clear IHys.
            clear Ha H0 H4.
            apply full_merge_in_trans with T''; try easy.
            apply fmer2_to_in_r with T'0; try easy.
    Qed.
  
    
    CoFixpoint force_fmer (T T' : ltt) : ltt := 
      match (T, T') with 
        | (ltt_send p f, ltt_send q f') => ltt_send p (fun n => match (f n, f' n) with 
                                                             | (Some (s1, t1), Some (s2, t2)) => Some (s1, force_fmer t1 t2)
                                                             | _                              => None
                                                       end)
        | (ltt_recv p f, ltt_recv q f') => ltt_recv p (fun n => match (f n, f' n) with 
                                                             | (Some (s1, t1), Some (s2, t2)) => Some (s1, force_fmer t1 t2)
                                                             | (Some (s1, t1), _)             => Some (s1, t1)
                                                             | (_            , Some (s2, t2)) => Some (s2, t2)
                                                             | _                              => None
                                                       end)
        | (_, _) => ltt_end
      end.
    
    Lemma onth_to_some {A} : forall (xs : slist A), exists n t, onth n xs = Some t.
    Proof.
      induction xs; intros.
      - exists 0. exists a. easy.
      - destruct IHxs as (n,(t,Ha)).
        exists (S n). exists t. easy.
    Qed.
    
    Lemma mergeTwo_can_merge : forall Tl Tl' Tr Tr' T, full_merge2 T Tl Tr -> full_merge_in Tl Tl' -> full_merge_in Tr Tr' -> exists T', full_merge2 T' Tl' Tr'.
    Proof.
      intros.
      exists (force_fmer Tl' Tr').
      revert H H0 H1. revert Tl Tl' Tr Tr' T.
      pcofix CIH; intros.
      
      pinversion H0.
      - subst.
        pinversion H1; try easy. subst.
        pinversion H2; try easy. subst. 
        rewrite (ltt_eq (force_fmer ltt_end ltt_end)). simpl.
        pfold. constructor.
        apply fmer_in_mon.
        apply fmer_in_mon.
      - subst.
        clear H0.
        pinversion H1; try easy. subst. clear H1.
        pinversion H2; try easy. subst. clear H2.
        pfold. rewrite(ltt_eq (force_fmer (ltt_send p f') (ltt_send p f'0))); simpl.
        apply cfmer_send; try easy.
        
        intro.
        specialize(H5 n). specialize(H4 n). specialize(H n).
        - destruct H5.
          destruct H0. rewrite H1. left.
          rewrite H0 in H. destruct H4.
          destruct H2. rewrite H3. easy.
          destruct H2 as (s1,(t1,(t2,(Ha,Hb)))). rewrite Ha in H.
          destruct H; try easy. destruct H as (s3,(t4,(t5,(t6,Hsa)))). easy.
        - destruct H0 as (s1,(t1,(t2,(Ha,(Hb,Hc))))).
          rewrite Ha in H.
          destruct H; try easy. destruct H as (s2,(t3,(t4,(t5,(Hd,(He,(Hf,Hg))))))).
          inversion He. subst. clear He.
          rewrite Hf in H4.
          destruct H4; try easy. destruct H as (s3,(t6,(t7,(Hh,(Hi,Hj))))).
          inversion Hh. subst. clear Hh.
          rewrite Hb. rewrite Hi.
          right. exists s3. exists (force_fmer t2 t7). exists t2. exists t7.
          split. easy. split. easy. split. easy.
          pclearbot.
          right.
          apply CIH with t4 t6 t3; try easy. 
        apply fmer_in_mon.
        apply fmer_in_mon.
      - subst. clear H0.
        pinversion H1; try easy. subst. clear H1.
        pinversion H2; try easy. subst. clear H2.
        rewrite (ltt_eq (force_fmer (ltt_recv p f') (ltt_recv p f'0))); simpl.
        pfold.
        constructor.
        intros.
        specialize(H4 n). specialize(H5 n). specialize(H n).
        
        destruct H5.
        - rewrite H0. 
          destruct H4.
          - rewrite H1. left. easy.
          - destruct H1 as (s1,(t1,(t2,(Ha,(Hb,Hc))))).
            rewrite Hb. right. right. left. exists (s1, t2). easy.
        - destruct H0 as (s1,(t1,(t2,(Ha,(Hb,Hc))))).
          rewrite Hb.
          destruct H4.
          - rewrite H0.
            right. left. exists (s1, t2). easy.
          - destruct H0 as (s2,(t3,(t4,(Hd,(He,Hf))))).
            rewrite He.
            right. right. right. 
            rewrite Ha in H. rewrite Hd in H.
            - destruct H. easy.
            - destruct H. destruct H as (st,H). easy.
            - destruct H. destruct H as (st,H). easy.
            - destruct H as (s3,(t5,(t6,(t7,(Hg,(Hh,(Hi,Hj))))))).
              inversion Hh. subst. inversion Hi. subst. clear Hh Hi.
              exists s3. exists (force_fmer t2 t4). exists t2. exists t4.
              split. easy. split. easy. split. easy.
              right.
              pclearbot.
              apply CIH with t6 t7 t5; try easy.
      apply fmer_in_mon.
      apply fmer_in_mon.
      apply fmer_mon.
    Qed.
    
    Lemma mergeTwo_to_Into : forall Tl Tl' Tr Tr' T T', full_merge2 T Tl Tr -> full_merge2 T' Tl' Tr' -> full_merge_in Tl Tl' -> full_merge_in Tr Tr' -> full_merge_in T T'.
    Proof.
      pcofix CIH; intros.
      pinversion H0.
      - subst.
        - pinversion H2; try easy. subst.
          pinversion H1; try easy. subst.
          pfold. constructor.
          apply fmer_mon.
          apply fmer_in_mon.
      - subst. clear H0.
        pinversion H2. subst. clear H2.
        pinversion H3. subst. clear H3.
        pinversion H1. subst. clear H1.
        pfold. constructor.
        intro.
        specialize(H3 n). specialize(H5 n). specialize(H6 n). specialize(H n).
        destruct H3.
        - destruct H0 as (Ha,(Hb,Hc)). 
          rewrite Ha.
          destruct H.
          - left. easy.
          - destruct H as (s1,(t1,(t2,(t3,(Hd,(He,(Hf,Hg))))))).
            rewrite He in H6. rewrite Hf in H5.
            destruct H6; try easy. rewrite Hb in H. 
            destruct H as (s2,(t4,(t5,H))). easy.
        - destruct H0 as (s1,(t1,(t2,(t3,(Ha,(Hb,(Hc,Hd))))))).
          rewrite Ha. right.
          rewrite Hb in H6. rewrite Hc in H5.
          destruct H6; try easy. destruct H0 as (s2,(t4,(t5,(He,(Hf,Hg))))).
          destruct H5; try easy. destruct H0 as (s3,(t6,(t7,(Hh,(Hi,Hj))))).
          inversion Hi. inversion Hf. subst. clear Hi Hf.
          rewrite Hh in H. rewrite He in H.
          destruct H; try easy.
          destruct H as (s4,(t8,(t9,(t10,(Hk,(Hl,(Hm,Hn))))))).
          inversion Hl. inversion Hm. subst. clear Hl Hm.
          rewrite Hk. exists s4. exists t8. exists t1.
          split. easy. split. easy.
          right. pclearbot.
          apply CIH with t9 t5 t10 t7; try easy.
        apply fmer_mon.
        apply fmer_in_mon.
        apply fmer_in_mon.
      - subst. clear H0.
        pinversion H2. subst. clear H2.
        pinversion H3. subst. clear H3.
        pinversion H1. subst. clear H1.
        pfold. constructor.
        intro.
        specialize(H3 n). specialize(H5 n). specialize(H6 n). specialize(H n).
        destruct H3.
        - destruct H0 as (Ha,(Hb,Hc)). 
          rewrite Ha. left. easy.
        - destruct H0.
          destruct H0 as (s1,(Ha,(Hb,Hc))).
          rewrite Ha. right. rewrite Hb in H6.
          destruct H6; try easy. 
          destruct H0 as (s2,(t1,(t2,(Hd,(He,Hf))))).
          inversion He. subst. clear He. rewrite Hd in H. rewrite Hc in H5.
          destruct H; try easy.
          - destruct H.
            destruct H as (st,(Hg,(Hh,Hi))).
            rewrite Hg. inversion Hh. subst.
            exists s2. exists t1. exists t2.
            split. easy. split. easy.
            specialize(paco2_mon). unfold monotone2. intros. pclearbot. left.
            apply H with (r := bot2); try easy.
          - destruct H.
            destruct H as (st,Ht). easy.
          - destruct H as (s3,(t3,(t4,(t5,(Hg,(Hh,(Hi,Hj))))))).
            inversion Hh. subst. clear Hh.
            rewrite Hg. exists s3. exists t3. exists t2. 
            split. easy. split. easy.
            left.
            assert(paco2 coind_fmer_in bot2 t3 t2).
            {
              pclearbot. destruct Hj; try easy.
              apply full_merge_in_trans with t4; try easy.
              apply fmer2_to_in_l with t5; try easy.
            }
            specialize(paco2_mon). unfold monotone2. intros. pclearbot.
            apply H0 with (r := bot2); try easy.
        - destruct H0.
          destruct H0 as (s1,(Ha,(Hb,Hc))).
          rewrite Ha. right. rewrite Hc in H5.
          destruct H5; try easy. 
          destruct H0 as (s2,(t1,(t2,(Hd,(He,Hf))))).
          inversion He. subst. clear He. rewrite Hd in H. 
          destruct H; try easy.
          - destruct H.
            destruct H as (st,Ht). easy.
          - destruct H.
            destruct H as (st,(Hg,(Hh,Hi))).
            rewrite Hg. inversion Hh. subst.
            exists s2. exists t1. exists t2.
            split. easy. split. easy.
            specialize(paco2_mon). unfold monotone2. intros. pclearbot. left.
            apply H with (r := bot2); try easy.
          - destruct H as (s3,(t3,(t4,(t5,(Hg,(Hh,(Hi,Hj))))))).
            inversion Hi. subst. clear Hi.
            rewrite Hg. exists s3. exists t3. exists t2. 
            split. easy. split. easy.
            left.
            assert(paco2 coind_fmer_in bot2 t3 t2).
            {
              pclearbot. destruct Hj; try easy.
              apply full_merge_in_trans with t5; try easy.
              apply fmer2_to_in_r with t4; try easy.
            }
            specialize(paco2_mon). unfold monotone2. intros. pclearbot.
            apply H0 with (r := bot2); try easy.
        - destruct H0 as (s1,(t1,(t2,(t3,(Ha,(Hb,(Hc,Hd))))))).
          rewrite Ha. right.
          rewrite Hb in H6. rewrite Hc in H5.
          destruct H6; try easy. destruct H0 as (s2,(t4,(t5,(He,(Hf,Hg))))).
          destruct H5; try easy. destruct H0 as (s3,(t6,(t7,(Hh,(Hi,Hj))))).
          inversion Hi. inversion Hf. subst. clear Hi Hf.
          rewrite Hh in H. rewrite He in H.
          - destruct H; try easy.
          - destruct H. destruct H; try easy.
          - destruct H. destruct H; try easy.
          destruct H as (s4,(t8,(t9,(t10,(Hk,(Hl,(Hm,Hn))))))).
          inversion Hl. inversion Hm. subst. clear Hl Hm.
          rewrite Hk. exists s4. exists t8. exists t1.
          split. easy. split. easy.
          right. pclearbot.
          apply CIH with t9 t5 t10 t7; try easy.
        apply fmer_mon.
        apply fmer_in_mon.
        apply fmer_in_mon.
      apply fmer_mon.
    Qed.
    
    
    Theorem isMerge_cont_Into_s : forall f f' T, full_merge f T -> (forall n, (f n = None /\ f' n = None) \/ (exists t t', f n = Some t /\ f' n = Some t' /\ full_merge_in t t')) -> exists T', full_merge f' T' /\ full_merge_in T T'.
    Proof.
      intros.
      destruct H as (ys,(Ha,Hb)).
      revert H0 Hb Ha. revert T f f'.
      induction ys; intros.
      - inversion Hb. subst.
        pose proof H0 as Hta. pose proof Ha as Htb.
        specialize(Ha 0). specialize(H0 0).
        rewrite (esym Ha) in H0.
        simpl in *.
        destruct H0; try easy.
        destruct H as (t1,(t2,(Hc,(Hd,He)))).
        inversion Hc. subst. clear Hc.
        exists t2. split; try easy.
        exists (slist_x t2).
        split.
        - intro.
          specialize(Htb n).
          specialize(Hta n).
          destruct n; try easy. 
          rewrite (esym Htb) in Hta. simpl in *.
          destruct Hta; try easy.  
          destruct H as (t3,(t4,Hf)). easy.
        - constructor.
      inversion Hb.
      - subst.
        specialize(IHys T (fun n => f (S n)) (fun n => f' (S n))).
        assert(exists T' : ltt,
         full_merge (fun n : fin => f' n.+1) T' /\ full_merge_in T T').
        {
          apply IHys; try easy.
          intro.
          specialize(Ha (S n)); try easy.
        }
        clear IHys.
        destruct H as (T',Hd).
        exists T'. split; try easy. destruct Hd.
        inversion H.
        exists (slist_xs None x). destruct H2.
        split.
        - intro.
          destruct n; try easy.
          - specialize(Ha 0).
            specialize(H0 0). rewrite (esym Ha) in H0. simpl in *.
            destruct H0; try easy.
            destruct H0 as (t1,(t2,Hc)). easy.
          - simpl.
            apply H2; try easy.
        - constructor; try easy.
      - subst. clear Hb.
        specialize(IHys T'' (fun n => f (S n)) (fun n => f' (S n))).
        assert(exists T' : ltt,
         full_merge (fun n : fin => f' n.+1) T' /\ full_merge_in T'' T').
        {
          apply IHys; try easy.
          intro.
          specialize(Ha (S n)); try easy.
        }
        clear IHys.
        
        destruct H as (Ta,(Hb,Hc)).
        assert(exists Tn, f' 0 = Some Tn).
        {
          specialize(Ha 0).
          specialize(H0 0). rewrite (esym Ha) in H0.
          destruct H0; try easy. destruct H as (t1,(t2,(Hf,(Hg,Hh)))). simpl in *.
          inversion Hf. subst.
          exists t2. easy.
        }
        destruct H as (Tn, H).
        assert(exists Tb, full_merge2 Tb Tn Ta).
        {
          specialize(mergeTwo_can_merge T' Tn T'' Ta T); intros.
          apply H1; try easy.
          specialize(Ha 0). simpl in *.
          specialize(H0 0). rewrite H in H0. rewrite (esym Ha) in H0.
          destruct H0; try easy.
          destruct H0 as (t1,(t2,(Hta,(Htb,Htc)))).
          inversion Hta. inversion Htb. easy.
        }
        destruct H1 as (Tb,H1).
        exists Tb.
        assert(full_merge f' Tb).
        {
          unfold full_merge. 
          inversion Hb. destruct H3.
          exists (slist_xs (Some Tn) x).
          split.
          - intro.
            destruct n; try easy.
            specialize(H3 n); try easy.
          - apply slm_xs with Ta; try easy.
        }
        split; try easy.
        clear H1 H Hc Hb.
        assert(full_merge f T).
        {
          exists (slist_xs (Some T') ys).
          split; try easy.
          apply slm_xs with T''; try easy.
        }
        clear H4 H2 Ha. clear T' Ta Tn. rename Tb into T'. clear T'' ys.
        
        inversion H as (xs,(Ha,Hb)). clear H. 
        inversion H3 as (ys,(Hc,Hd)). clear H3.
        assert(SForall2 full_merge_in xs ys).
        {
          clear Hd Hb. revert Ha Hc H0.
          revert f f'.
          revert ys.
          induction xs; intros.
          - destruct ys; try easy.
            - constructor.
              specialize(H0 0). specialize(Ha 0). specialize(Hc 0).
              simpl in *. rewrite (esym Ha) in H0. rewrite (esym Hc) in H0.
              destruct H0; try easy.
              destruct H as (t1,(t2,(Hd,(He,Hf)))).
              inversion Hd. subst. inversion He. subst. clear Hd He. easy.
            - specialize(onth_to_some ys); intros.
              destruct H as (n,(t,H)).
              specialize(Ha (S n)). specialize(Hc (S n)). specialize(H0 (S n)).
              rewrite (esym Ha) in H0. rewrite (esym Hc) in H0. clear Ha Hc. simpl in *.
              rewrite H in H0. destruct H0; try easy.
              destruct H0 as (t1,(t2,Ha)). easy.
          - destruct ys; try easy.
            - specialize(onth_to_some xs); intros.
              destruct H as (n,(t,H)).
              specialize(Ha (S n)). specialize(Hc (S n)). specialize(H0 (S n)).
              rewrite (esym Ha) in H0. rewrite (esym Hc) in H0. clear Ha Hc. simpl in *.
              rewrite H in H0. destruct H0; try easy.
              destruct H0 as (t1,(t2,Ha)). easy.
            - specialize(IHxs ys (fun n => f (S n)) (fun n => f' (S n))).
              assert(SForall2 full_merge_in xs ys).
              apply IHxs; try easy.
              intro. specialize(Ha (S n)); try easy.
              intro. specialize(Hc (S n)); try easy.
              
              specialize(Ha 0). specialize(Hc 0). specialize(H0 0).
              rewrite (esym Ha) in H0. rewrite (esym Hc) in H0. clear Ha Hc.
              simpl in *.
              destruct H0.
              - destruct H0. subst.
                constructor; try easy.
              - destruct H0 as (t1,(t2,(Ha,(Hb,Hc)))).
                subst.
                constructor; try easy.
              
        }
        clear Hc Ha H0. clear f f'.
        revert Hb Hd H. revert T T' ys.
        induction xs; intros.
        - destruct ys; try easy.
          inversion H. subst.
          inversion Hb. subst. inversion Hd. subst. easy.
        - destruct ys; try easy.
          inversion H. 
          - subst. clear H.
            inversion Hb. subst. clear Hb.
            inversion Hd. subst. clear Hd.
            specialize(IHxs T'' T''0 ys H4 H7 H5).
            clear H5 H4 H7. clear xs ys.
            
            specialize(mergeTwo_to_Into x y T'' T''0 T T'); intros.
            apply H; try easy.
            
          - subst. clear H.
            inversion Hb. subst. clear Hb.
            inversion Hd. subst. clear Hd.
            specialize(IHxs T T' ys H0 H2 H1). easy.

    Qed.
    
    Lemma Merge_Sort_s : forall f'0 q f f'1 p f' n, full_merge f'0 (ltt_send q f) -> full_merge f'1 (ltt_recv p f') 
      -> (forall n : fin,
         f'0 n = None /\ f'1 n = None \/
         (exists fa fb : fin -> option (sort * ltt),
            f'0 n = Some (ltt_send q fa) /\
            f'1 n = Some (ltt_recv p fb) /\
            (forall m : fin,
             fa m = None /\ fb m = None \/
             (exists (s' : sort) (t t' : ltt), fa m = Some (s', t) /\ fb m = Some (s', t'))))) 
       -> f n = None /\ f' n = None \/ (exists (s : sort) (t t' : ltt), f n = Some (s, t) /\ f' n = Some (s, t')).
    Proof.
      intros.
      destruct H as (zs,(Ha,Hb)).
      destruct H0 as (ys,(Hc,Hd)).
      revert H1 Hd Hc Hb Ha. revert f'0 q f f'1 p f' n ys.
      induction zs; intros.
      - inversion Hb. subst. clear Hb.
        inversion Hd.
        - subst. clear Hd.
          specialize(Hc 0). specialize(Ha 0). specialize(H1 0).
          simpl in *. rewrite (esym Ha) in H1. rewrite (esym Hc) in H1.
          destruct H1; try easy.
          destruct H as (fa,(fb,(Hd,(He,Hf)))).
          inversion Hd. subst. clear Hd.
          inversion He. subst. clear He.
          specialize(Hf n).
          easy.
        - subst. clear Hd.
          specialize(onth_to_some xs); intros.
          destruct H0 as (n1,(ta,Ht)).
          specialize(Hc (S n1)). specialize(Ha (S n1)). simpl in *. rewrite Ht in Hc.
          specialize(H1 (S n1)). rewrite (esym Ha) in H1. rewrite (esym Hc) in H1.
          destruct H1; try easy. destruct H0 as (fa,(fb,Hs)). easy.
        - subst. clear Hd.
          specialize(onth_to_some xs); intros.
          destruct H2 as (n1,(ta,Ht)).
          specialize(Hc (S n1)). specialize(Ha (S n1)). simpl in *. rewrite Ht in Hc.
          specialize(H1 (S n1)). rewrite (esym Ha) in H1. rewrite (esym Hc) in H1.
          destruct H1; try easy. destruct H1 as (fa,(fb,Hs)). easy.
      - inversion Hb.
        - subst. clear Hb.
          inversion Hd.
          - subst.
            specialize(onth_to_some zs); intros.
            destruct H as (n1,(ta,Ht)).
            specialize(Hc (S n1)). specialize(Ha (S n1)). simpl in *. rewrite Ht in Ha.
            specialize(H1 (S n1)). rewrite (esym Ha) in H1. rewrite (esym Hc) in H1.
            destruct H1; try easy. destruct H as (fa,(fb,Hs)). easy.
          - subst. clear Hd.
            specialize(IHzs (fun n => f'0 (S n)) q f (fun n => f'1 (S n)) p f' n xs).
            apply IHzs; try easy.
            - intro. specialize(Hc (S n0)). easy.
            - intro. specialize(Ha (S n0)). easy.
          - subst. 
            specialize(Hc 0). specialize(Ha 0).
            simpl in *.
            specialize(H1 0). rewrite (esym Ha) in H1. rewrite (esym Hc) in H1.
            destruct H1; try easy. destruct H1 as (fa,(fb,Ht)). easy.
        - subst. clear Hb.
          inversion Hd. 
          - subst.
            specialize(onth_to_some zs); intros.
            destruct H as (n1,(ta,Ht)).
            specialize(Hc (S n1)). specialize(Ha (S n1)). simpl in *. rewrite Ht in Ha.
            specialize(H1 (S n1)). rewrite (esym Ha) in H1. rewrite (esym Hc) in H1.
            destruct H1; try easy. destruct H as (fa,(fb,Hs)). easy.
          - subst.
            specialize(Hc 0). specialize(Ha 0).
            simpl in *.
            specialize(H1 0). rewrite (esym Ha) in H1. rewrite (esym Hc) in H1.
            destruct H1; try easy. destruct H0 as (fa,(fb,Ht)). easy.
          - subst.
            pinversion H2; try easy. subst. pinversion H; try easy. subst.
            clear H2 H.
            specialize(IHzs (fun n => f'0 (S n)) q f3 (fun n => f'1 (S n)) p f4 n xs).
            assert(f3 n = None /\ f4 n = None \/
              (exists (s : sort) (t t' : ltt), f3 n = Some (s, t) /\ f4 n = Some (s, t'))).
            {
              apply IHzs; try easy.
              - intro. specialize(Hc (S n0)); try easy.
              - intro. specialize(Ha (S n0)); try easy.
            }
            specialize(Hc 0). specialize(Ha 0). specialize(H1 0).
            simpl in *. rewrite (esym Ha) in H1. rewrite (esym Hc) in H1.
            destruct H1; try easy. 
            destruct H1 as (fa,(fb,(Hta,(Htb,Htc)))). inversion Hta. subst. inversion Htb. subst.
            clear IHzs Hc Hd Ha H4 H0 Hta Htb.
            specialize(H8 n). specialize(H9 n). specialize(Htc n).
            destruct H8.
            - destruct H9. left. easy.
              destruct H0 as (Ha,(Hb,Hc)). rewrite Hb in Htc. rewrite Hc in H.
              assert(fb n = None).
              {
                destruct Htc; try easy.
                destruct H0 as (s1,(t1,(t2,Ht))). easy.
              }
              assert(f4 n = None).
              {
                destruct H; try easy.
                destruct H as (s1,(t1,(t2,Ht))). easy.
              }
              rewrite H0 in H1. rewrite H2 in H1.
              
              - destruct H1. destruct H1; try easy.
              - destruct H1. destruct H1; try easy.
              - destruct H1 as (s1,(t1,(t2,(t3,Ht)))); try easy.
            - destruct H0 as (s1,(t1,(t2,(t3,(Ha,(Hb,(Hc,Hd))))))).
              rewrite Ha. rewrite Hb in Htc. rewrite Hc in H.
              right.
              destruct Htc; try easy. 
              destruct H0 as (s2,(t4,(t5,(He,Hf)))). inversion He. subst.
              destruct H; try easy.
              destruct H as (s3,(t6,(t7,(Hg,Hh)))). inversion Hg. subst.
              rewrite Hf in H9. rewrite Hh in H9.
              - destruct H9; try easy.
              - destruct H. destruct H; try easy.
              - destruct H. destruct H; try easy.
              - destruct H as (s4,(t8,(t9,(t10,(Hi,(Hj,(Hk,Hl))))))).
                inversion Hj. subst. inversion Hk. subst.
                rewrite Hi. exists s4. exists t1. exists t8. easy.
      apply fmer_mon.
      apply fmer_mon.
    Qed.
    
   (*  Lemma bisim_with_Merge : forall f' f'0 T T' r,
      (forall n : fin,
         f' n = None /\ f'0 n = None \/
         (exists t t' : ltt, f' n = Some t /\ f'0 n = Some t' /\ r t t')) ->
        full_merge f' T ->
        full_merge f'0 T' -> 
        paco2 bisim r T T'.
    Proof.
      intros.
      unfold full_merge in *.
      destruct H0 as (xs,(Ha,Hb)). destruct H1 as (ys,(Hc,Hd)).
      revert H Ha Hb Hc Hd. revert T T' f' f'0 r ys.
      induction xs; intros.
      - inversion Hb. subst.
        revert H Hb Ha Hc Hd. revert T T' f' f'0 r.
        induction ys; intros.
        - inversion Hd. subst.
          specialize(Ha 0). specialize(Hc 0). specialize(H 0).
          simpl in *. rewrite (esym Ha) in H. rewrite (esym Hc) in H.
      
      
       *)
       
    Instance coind_full_merge : good_merge := {
    
      isMerge := full_merge;
      
      merge_into_recv := merge_into_recv_s;
      merge_label_send := merge_label_send_s;
      merge_into_send := merge_into_send_s;
      merge_label_send_b := merge_label_send_b_s;
    
      MergeInto := full_merge_in;
      
      isMerge_to_Into := isMerge_to_Into_s;
      
      MergeInto_end := MergeInto_end_f;
      
      MergeInto_send := MergeInto_send_f;
      MergeInto_recv := MergeInto_recv_f;
      isMerge_cont_Into := isMerge_cont_Into_s;
      
      MergeInto_to_subtypeC := MergeInto_to_subtypeC_f;
      
      Merge_Sort := Merge_Sort_s
   
    }.
    
    (* coinductive full merge is a bisimular relation *)
    Lemma full_merge2_partial : forall T1 T2 T T', full_merge2 T1 T T' -> full_merge2 T2 T T' -> ltt_bisimC T1 T2.
    Proof.
      pcofix CIH; intros.
      pinversion H0; subst; try apply fmer_mon.
      - pinversion H1; try easy; subst; try apply fmer_mon.
        pfold.
        constructor.
      - pinversion H1; try easy; subst; try apply fmer_mon.
        pfold. constructor.
        intros.
        specialize(H n). specialize(H4 n). 
        destruct H.
        - destruct H as (Ha,(Hb,Hc)). rewrite Hb in H4.
          destruct H4 as [H4 | H4]; destruct_exists_and; try easy.
          left. easy.
        - destruct_exists_and. rewrite H2 H3 in H4.
          destruct H4; try easy. destruct_exists_and. invert_all_some.
          right. rewrite H H4. eexists. eexists. eexists.
          split. easy. split. easy. right. pclearbot.
          apply CIH with x5 x6; try easy.
      - pinversion H1; try easy; subst; try apply fmer_mon.
        pfold. constructor.
        intros.
        specialize(H n). specialize(H4 n). 
        destruct H as [H | [H | [H | H]]].
        - destruct H as (Ha,(Hb,Hc)). rewrite Hb Hc in H4.
          destruct H4 as [H4 | [H4 | [H4 | H4]]]; destruct_exists_and; try easy.
          left. easy.
        - destruct_exists_and. rewrite H2 H3 in H4.
          destruct H4 as [H4 | [H4 | [H4 | H4]]]; destruct_exists_and; try easy.
          invert_all_some. destruct x0.
          right. rewrite H H4. eexists. eexists. eexists. split. easy. split. easy.
          left.
          apply ltt_bisimC_refl.
        - destruct_exists_and. rewrite H2 H3 in H4.
          destruct H4 as [H4 | [H4 | [H4 | H4]]]; destruct_exists_and; try easy.
          invert_all_some. destruct x0.
          right. rewrite H H4. eexists. eexists. eexists. repeat(split; try easy).
          left. apply ltt_bisimC_refl.
        - destruct_exists_and. rewrite H2 H3 in H4.
          destruct H4 as [H4 | [H4 | [H4 | H4]]]; destruct_exists_and; try easy.
          invert_all_some. rewrite H H4.
          right. eexists. eexists. eexists. repeat(split; try easy).
          right. pclearbot.
          apply CIH with x5 x6; try easy.
    Qed.
          
  
  End coind_fmer.
  
  Section coind_pmer.
  
    Inductive coind_pmer_in (R : ltt -> ltt -> Prop) : ltt -> ltt -> Prop :=
      | pmer_in_end  : coind_pmer_in R ltt_end ltt_end 
      | pmer_in_send : forall p f f', (forall n, (f n = None /\ f' n = None) \/ (exists s t t', f n = Some(s, t) /\ f' n = Some(s, t') /\ R t t')) -> coind_pmer_in R (ltt_send p f) (ltt_send p f')
      | pmer_in_recv : forall p f f', (forall n, (f n = None /\ f' n = None) \/ (exists s t t', f n = Some(s, t) /\ f' n = Some(s, t') /\ R t t')) -> coind_pmer_in R (ltt_recv p f) (ltt_recv p f').
    
    Lemma pmer_in_mon : monotone2 coind_pmer_in.
    Proof.
      unfold monotone2; intros.
      induction IN.
      - constructor.
      - constructor.
        intro.
        specialize(H n).
        destruct H.
        - left. easy.
        - right.
          destruct H as (s1,(t1,(t2,(Ha,(Hb,Hc))))).
          rewrite Ha. rewrite Hb.
          exists s1. exists t1. exists t2.
          split. easy. split. easy.
          apply LE; try easy.
      - constructor.
        intro.
        specialize(H n).
        destruct H.
        - left. easy.
        - right.
          destruct H as (s1,(t1,(t2,(Ha,(Hb,Hc))))).
          rewrite Ha. rewrite Hb.
          exists s1. exists t1. exists t2.
          split. easy. split. easy.
          apply LE; try easy.
    Qed.
    
    (* explicit MergeInto *)
    Definition plain_merge_in T T' := paco2 coind_pmer_in bot2 T T'.
    
    Lemma MergeInto_end_p : plain_merge_in ltt_end ltt_end.
    Proof.
      pfold. constructor.
    Qed.
    
    Lemma MergeInto_send_p : forall p fl fr, (forall n, (fl n = None /\ fr n = None) \/ (exists s t t', fl n = Some(s, t) /\ fr n = Some(s, t') /\ plain_merge_in t t')) -> plain_merge_in (ltt_send p fl) (ltt_send p fr).
    Proof.
      intros.
      pfold. constructor.
      intro.
      specialize(H n). 
      destruct H.
      - left. easy.
      - right.
        destruct H as (s1,(t1,(t2,(Ha,(Hb,Hc))))).
        rewrite Ha. rewrite Hb.
        exists s1. exists t1. exists t2.
        split. easy. split. easy. left. easy.
    Qed.
    
    Lemma MergeInto_recv_p : forall p fl fr, (forall n, (fl n = None /\ fr n = None) \/ (exists s t t', fl n = Some(s, t) /\ fr n = Some(s, t') /\ plain_merge_in t t')) -> plain_merge_in (ltt_recv p fl) (ltt_recv p fr).
    Proof.
      intros.
      pfold. constructor.
      intro.
      specialize(H n).
      destruct H.
      - left. easy.
      - right.
        destruct H as (s1,(t1,(t2,(Ha,(Hb,Hc))))).
        rewrite Ha. rewrite Hb.
        exists s1. exists t1. exists t2.
        split. easy. split. easy. left. easy.
    Qed.
    
    Lemma MergeInto_to_subtypeC_p : forall T T', plain_merge_in T T' -> subtypeC T T'.
    Proof.
      pcofix CIH.
      intros.
      pinversion H0.
      - subst. pfold. constructor.
      - subst. pfold. constructor.
        intro.
        specialize(H n). 
        destruct H.
        - left. easy.
        - right.
          destruct H as (s1,(t1,(t2,(Ha,(Hb,Hc))))).
          rewrite Ha. rewrite Hb.
          exists s1.  exists t1. exists t2.
          split. easy. split. easy.
          right. pclearbot.
          apply CIH; try easy.
      - subst. pfold. constructor.
        intro.
        specialize(H n). 
        destruct H.
        - left. easy.
        - right.
          destruct H as (s1,(t1,(t2,(Ha,(Hb,Hc))))).
          rewrite Ha. rewrite Hb.
          exists s1. exists t1. exists t2.
          split. easy. split. easy.
          right. pclearbot.
          apply CIH; try easy.
      - apply pmer_in_mon.
    Qed.
    

    
    Inductive coind_pmer_fun (R : ltt -> ltt -> ltt -> Prop) : ltt -> ltt -> ltt -> Prop :=
      | cpmer_end  : coind_pmer_fun R ltt_end ltt_end ltt_end 
      | cpmer_send : forall p f1 f2 f3, (forall n, (f1 n = None /\ f2 n = None /\ f3 n = None) \/
                                                   (exists s t1 t2 t3, f1 n = Some(s, t1) /\ f2 n = Some(s, t2) /\ f3 n = Some(s, t3) /\ R t1 t2 t3)) -> coind_pmer_fun R (ltt_send p f1) (ltt_send p f2) (ltt_send p f3)
      | cpmer_recv : forall p f1 f2 f3, (forall n, (f1 n = None /\ f2 n = None /\ f3 n = None) \/
                                                   (exists s t1 t2 t3, f1 n = Some(s, t1) /\ f2 n = Some(s, t2) /\ f3 n = Some(s, t3) /\ R t1 t2 t3)) -> coind_pmer_fun R (ltt_recv p f1) (ltt_recv p f2) (ltt_recv p f3).
    
    Lemma pmer_mon : monotone3 coind_pmer_fun.
    Proof.
      unfold monotone3; intros.
      induction IN; intros.
      - constructor.
      - constructor.
        intro.
        specialize(H n).
        destruct H.
        - left. easy.
        - right.
          destruct H as (s1,(t1,(t2,(t3,(Ha,(Hb,(Hc,Hd))))))).
          exists s1. exists t1. exists t2. exists t3.
          split. easy. split. easy. split. easy.
          apply LE; try easy.
      - constructor.
        intro.
        specialize(H n).
        destruct H.
        - left. easy.
        - right.
          destruct H as (s1,(t1,(t2,(t3,(Ha,(Hb,(Hc,Hd))))))).
          exists s1. exists t1. exists t2. exists t3.
          split. easy. split. easy. split. easy.
          apply LE; try easy.
    Qed.
    
    Definition plain_merge2 T T' T'' := paco3 coind_pmer_fun bot3 T T' T''.
        
    Definition plain_merge f T := exists zs, (forall n, onth n zs = f n) /\ @slist_merge plain_merge2 zs T.
    
    Lemma pmerge_into_send_s : forall g p f, plain_merge g (ltt_send p f) -> forall n s t, f n = Some(s, t) -> plain_merge (through_merge_s g n) t.
    Proof.
     intros.
      destruct H as (zs, (Ha,Hb)).
      revert Ha Hb H0. revert n s t f g.
      induction zs; intros. 
      - inversion Hb. subst. clear Hb.
        unfold through_merge_s.
        exists (slist_x t).
        split.
        - intro.
          specialize(Ha n0). rewrite (esym Ha).
          destruct n0; try easy.
          simpl. rewrite H0. easy.
        - constructor.
      - inversion Hb.
        - subst.
          specialize(IHzs n s t f (fun n => g (S n))).
          assert(plain_merge (through_merge_s (fun n : fin => g n.+1) n) t).
          {
            apply IHzs; try easy.
            intro. 
            specialize(Ha (S n0)); try easy.
          }
          inversion H. destruct H1.
          exists (slist_xs None x).
          split.
          - intro. 
            destruct n0.
            - specialize(Ha 0). unfold through_merge_s.
              rewrite (esym Ha). simpl in *. easy.
            - specialize(H1 n0); try easy.
          - constructor; try easy.
        - subst.
          pinversion H2; try easy. subst.
          specialize(H6 n). rewrite H0 in H6.
          destruct H6; try easy.
          destruct H as (s1,(t1,(t2,(t3,(Hc,(Hd,(He,Hf))))))).
          - inversion Hc. subst. clear Hc. clear Hb H2.
   
            specialize(IHzs n s1 t3 f3 (fun n => g (S n))).
            assert(plain_merge (through_merge_s (fun n : fin => g n.+1) n) t3).
            {
              apply IHzs; try easy.
              intro. specialize(Ha (S n0)). easy.
            }
            inversion H; try easy. destruct H1.
            exists (slist_xs (Some t2) x); try easy.
            split.
            - intro. 
              destruct n0.
              - unfold through_merge_s.
                simpl in *.
                specialize(Ha 0). rewrite (esym Ha). simpl.
                rewrite Hd. easy.
              - specialize(H1 n0). easy.
            - apply slm_xs with t3; try easy.
              destruct Hf; try easy.
          apply pmer_mon.
    Qed.
    
    Lemma pmerge_into_recv_s : forall g p f, plain_merge g (ltt_recv p f) -> forall n s t, f n = Some(s, t) -> plain_merge (through_merge_r g n) t.
    Proof.
      intros.
      destruct H as (zs, (Ha,Hb)).
      revert Ha Hb H0. revert n s t f g.
      induction zs; intros. 
      - inversion Hb. subst. clear Hb.
        unfold through_merge_r.
        exists (slist_x t).
        split.
        - intro.
          specialize(Ha n0). rewrite (esym Ha).
          destruct n0; try easy.
          simpl. rewrite H0. easy.
        - constructor.
      - inversion Hb.
        - subst.
          specialize(IHzs n s t f (fun n => g (S n))).
          assert(plain_merge (through_merge_r (fun n : fin => g n.+1) n) t).
          {
            apply IHzs; try easy.
            intro. 
            specialize(Ha (S n0)); try easy.
          }
          inversion H. destruct H1.
          exists (slist_xs None x).
          split.
          - intro. 
            destruct n0.
            - specialize(Ha 0). unfold through_merge_r.
              rewrite (esym Ha). simpl in *. easy.
            - specialize(H1 n0); try easy.
          - constructor; try easy.
        - subst.
          pinversion H2; try easy. subst.
          specialize(H6 n). rewrite H0 in H6.
          destruct H6; try easy.
          destruct H as (s1,(t1,(t2,(t3,(Hc,(Hd,(He,Hf))))))).
          - inversion Hc. subst. clear Hc. clear Hb H2.
   
            specialize(IHzs n s1 t3 f3 (fun n => g (S n))).
            assert(plain_merge (through_merge_r (fun n : fin => g n.+1) n) t3).
            {
              apply IHzs; try easy.
              intro. specialize(Ha (S n0)). easy.
            }
            inversion H; try easy. destruct H1.
            exists (slist_xs (Some t2) x); try easy.
            split.
            - intro. 
              destruct n0.
              - unfold through_merge_r.
                simpl in *.
                specialize(Ha 0). rewrite (esym Ha). simpl.
                rewrite Hd. easy.
              - specialize(H1 n0). easy.
            - apply slm_xs with t3; try easy.
              destruct Hf; try easy.
          apply pmer_mon.
    Qed.
    
    Lemma pmerge_label_send_s : forall g p f, plain_merge g (ltt_send p f) -> forall n q f' l st, g n = Some (ltt_send q f') -> f' l = Some st -> exists st', f l = Some st'.
    Proof.
      intros g p f H.
      destruct H as (zs,(Ha,Hb)).
      revert Ha Hb. revert g f.
      induction zs; intros.
      - inversion Hb. subst.
        assert (n = 0).
        {
          destruct n; try easy.
          specialize(Ha (S n)). simpl in *. rewrite H in Ha. easy.
        }
        subst.
        specialize(Ha 0). rewrite H in Ha. 
        inversion Ha. subst. exists st. easy.
      - inversion Hb.
        - subst.
          specialize(IHzs (fun n => g (S n)) f).
          assert(forall (n : fin) q (f' : fin -> option (sort * ltt))
         (l : fin) (st : sort * ltt),
       (fun n0 : fin => g n0.+1) n = Some (ltt_send q f') ->
       f' l = Some st -> exists st' : sort * ltt, f l = Some st').
          {
            apply IHzs; try easy.
            intro.
            specialize(Ha (S n0)). easy.
          }
          clear IHzs.
          destruct n.
          - specialize(Ha 0). rewrite H in Ha. easy.
          - specialize(H1 n q f'). apply H1 with st; try easy.
        - subst. clear Hb.
          pinversion H3; try easy. subst.
          specialize(IHzs (fun n => g (S n)) f3).
          assert(forall (n : fin) q (f' : fin -> option (sort * ltt))
         (l : fin) (st : sort * ltt),
       (fun n0 : fin => g n0.+1) n = Some (ltt_send q f') ->
       f' l = Some st -> exists st' : sort * ltt, f3 l = Some st').
          {
            apply IHzs; try easy.
            intro.
            specialize(Ha (S n0)); try easy.
          }
          clear IHzs.
          destruct n.
          - specialize(Ha 0). rewrite H in Ha.
            inversion Ha. subst. clear Ha.
            specialize(H7 l). rewrite H0 in H7.
            destruct H7; try easy.
            destruct H2 as (s1,(t1,(t2,(t3,(Ha,(Hb,(Hc,Hd))))))).
            inversion Hb. subst. clear Hb.
            exists (s1, t1). easy.
          - specialize(H1 n q f' l st H H0).
            destruct H1 as (sta,Ht).
            specialize(H7 l). rewrite Ht in H7.
            destruct H7; try easy.
            destruct H1 as (s1,(t1,(t2,(t3,(Hb,(Hc,(Hd,He))))))).
            inversion Hd. subst. clear Hd. 
            exists (s1, t1). easy.
        apply pmer_mon.
    Qed.
    
    Lemma pmerge_label_send_b_s : forall g p f, plain_merge g (ltt_send p f) -> forall n q f' l st, g n = Some (ltt_send q f') -> f l = Some st -> exists st', f' l = Some st'.
    Proof.
      intros g p f H.
      destruct H as (zs, (Ha,Hb)).
      revert Ha Hb. revert g f.
        
      induction zs; intros.
      - inversion Hb. subst.
        assert (n = 0).
        {
          destruct n; try easy.
          specialize(Ha (S n)). simpl in *. rewrite H in Ha. easy.
        }
        subst.
        specialize(Ha 0). rewrite H in Ha. 
        inversion Ha. subst. exists st. easy.
      - inversion Hb.
        - subst.
          specialize(IHzs (fun n => g (S n)) f).
          assert(forall (n : fin) q (f' : fin -> option (sort * ltt)) 
         (l : fin) (st : sort * ltt),
       (fun n0 : fin => g n0.+1) n = Some (ltt_send q f') ->
       f l = Some st -> exists st' : sort * ltt, f' l = Some st').
          {
            apply IHzs; try easy.
            intro.
            specialize(Ha (S n0)). easy.
          }
          clear IHzs.
          destruct n.
          - specialize(Ha 0). rewrite H in Ha. easy.
          - specialize(H1 n q f'). apply H1 with st; try easy.
        - subst. clear Hb.
          pinversion H3; try easy. subst.
          specialize(IHzs (fun n => g (S n)) f3).
          assert(forall (n : fin) q (f' : fin -> option (sort * ltt)) 
         (l : fin) (st : sort * ltt),
       (fun n0 : fin => g n0.+1) n = Some (ltt_send q f') ->
       f3 l = Some st -> exists st' : sort * ltt, f' l = Some st').
          {
            apply IHzs; try easy.
            intro.
            specialize(Ha (S n0)); try easy.
          }
          clear IHzs H3.
          destruct n.
          - specialize(Ha 0). rewrite H in Ha.
            inversion Ha. subst. clear Ha.
            specialize(H7 l). rewrite H0 in H7.
            destruct H7; try easy.
            destruct H2 as (s1,(t1,(t2,(t3,(Ha,(Hb,(Hc,Hd))))))).
            exists (s1, t2). easy.
          - specialize(H7 l). rewrite H0 in H7.
            destruct H7; try easy.
            destruct H2 as (s1,(t1,(t2,(t3,(Hb,(Hc,(Hd,He))))))).
            specialize(H1 n q f' l (s1, t3)).
            apply H1; try easy.
        apply pmer_mon.
    Qed.
    
    
    
    Lemma plain_merge_in_refl : forall T, plain_merge_in T T.
    Proof.
      pcofix CIH; intros.
      destruct T.
      - pfold.
        constructor.
      - pfold.
        constructor.
        intros.
        destruct o.
        - right. destruct p0. exists s. exists l. exists l.
          split. easy. split. easy. right.
          apply CIH; try easy.
        - left. easy.
      - pfold.
        constructor.
        intros.
        destruct o.
        - right. destruct p0. exists s. exists l. exists l.
          split. easy. split. easy. right.
          apply CIH; try easy.
        - left. easy.
    Qed.
    
    Lemma pmer2_to_in_l : forall T T' T'', plain_merge2 T T' T'' -> plain_merge_in T T'.
    Proof.
      pcofix CIH; intros.
      pinversion H0.
      - subst. pfold. constructor.
      - subst. pfold. constructor.
        intros.
        specialize(H n).
        destruct H. left. easy.
        destruct H as (s1,(t1,(t2,(t3,(Ha,(Hb,(Hc,Hd))))))).
        right. exists s1. exists t1. exists t2.
        split. easy. split. easy.
        right. pclearbot. apply CIH with t3; try easy.
      - subst. pfold. constructor.
        intros.
        specialize(H n).
        destruct H. left. easy.
        destruct H as (s1,(t1,(t2,(t3,(Ha,(Hb,(Hc,Hd))))))).
        right. exists s1. exists t1. exists t2.
        split. easy. split. easy.
        right. pclearbot. apply CIH with t3; try easy.
      apply pmer_mon.
    Qed.
    
    Lemma pmer2_to_in_r : forall T T' T'', plain_merge2 T T' T'' -> plain_merge_in T T''.
    Proof.
      pcofix CIH; intros.
      pinversion H0.
      - subst. pfold. constructor.
      - subst. pfold. constructor.
        intros.
        specialize(H n).
        destruct H. left. easy.
        destruct H as (s1,(t1,(t2,(t3,(Ha,(Hb,(Hc,Hd))))))).
        right. exists s1. exists t1. exists t3.
        split. easy. split. easy.
        right. pclearbot. apply CIH with t2; try easy.
      - subst. pfold. constructor.
        intros.
        specialize(H n).
        destruct H. left. easy.
        destruct H as (s1,(t1,(t2,(t3,(Ha,(Hb,(Hc,Hd))))))).
        right. exists s1. exists t1. exists t3.
        split. easy. split. easy.
        right. pclearbot. apply CIH with t2; try easy.
      apply pmer_mon.
    Qed.
    
    Lemma plain_merge_in_trans : forall T T' T'', plain_merge_in T T' -> plain_merge_in T' T'' -> plain_merge_in T T''.
    Proof.
      pcofix CIH; intros.
      pinversion H0.
      - subst.
        pinversion H1; try easy.
        pfold. constructor.
        apply pmer_in_mon.
      - subst.
        pinversion H1; try easy. subst.
        pfold. constructor.
        clear H0 H1.
        intro.
        specialize(H5 n). specialize(H n).
        destruct H.
        - destruct H5. left. easy.
          destruct H. destruct H0 as (s1,(t1,(t2,Ha))). rewrite H1 in Ha. easy.
        - destruct H as (s1,(t1,(t2,(Ha,(Hb,Hc))))).
          rewrite Hb in H5.
          destruct H5; try easy. destruct H as (s2,(t3,(t4,(Hd,(He,Hf))))).
          rewrite Ha. rewrite He.
          inversion Hd. subst.
          right. exists s2. exists t1. exists t4.
          split. easy. split. easy.
          pclearbot.
          right. apply CIH with t3; try easy.
        apply pmer_in_mon.
      - subst.
        pinversion H1; try easy. subst.
        pfold. constructor.
        clear H0 H1.
        intro.
        specialize(H5 n). specialize(H n).
        destruct H.
        - destruct H5. left. easy.
          destruct H. destruct H0 as (s1,(t1,(t2,Ha))). rewrite H1 in Ha. easy.
        - destruct H as (s1,(t1,(t2,(Ha,(Hb,Hc))))).
          rewrite Hb in H5.
          destruct H5; try easy. destruct H as (s2,(t3,(t4,(Hd,(He,Hf))))).
          rewrite Ha. rewrite He.
          inversion Hd. subst.
          right. exists s2. exists t1. exists t4.
          split. easy. split. easy.
          pclearbot.
          right. apply CIH with t3; try easy.
        apply pmer_in_mon.
      apply pmer_in_mon.
    Qed.
        
    
    Lemma ispMerge_to_Into_s : forall f T l T', plain_merge f T -> f l = Some T' -> plain_merge_in T T'.
    Proof.
      intros.
      destruct H as (ys,(Ha,Hb)).
      revert Ha Hb H0. revert T l T' f.
      induction ys; intros.
      - inversion Hb. subst.
        specialize(Ha l). rewrite H0 in Ha. destruct l; try easy.
        inversion Ha. subst.
        apply plain_merge_in_refl; try easy.
      - inversion Hb.
        - subst. clear Hb.
          destruct l; try easy.
          - specialize(Ha 0). rewrite H0 in Ha. easy.
          - apply IHys with l (fun n => f (S n)); try easy.
            intro. specialize(Ha (S n)); try easy.
        - subst. clear Hb.
          destruct l.
          - specialize(Ha 0). rewrite H0 in Ha.
            inversion Ha. subst.
            apply pmer2_to_in_l with T''; try easy.
          - specialize(IHys T'' l T' (fun n => f (S n))).
            assert(plain_merge_in T'' T').
            {
              apply IHys; try easy.
              intro.
              specialize(Ha (S n)); try easy.
            }
            clear IHys.
            clear Ha H0 H4.
            apply plain_merge_in_trans with T''; try easy.
            apply pmer2_to_in_r with T'0; try easy.
    Qed.
  
    
    CoFixpoint force_pmer (T T' : ltt) : ltt := 
      match (T, T') with 
        | (ltt_send p f, ltt_send q f') => ltt_send p (fun n => match (f n, f' n) with 
                                                             | (Some (s1, t1), Some (s2, t2)) => Some (s1, force_pmer t1 t2)
                                                             | _                              => None
                                                       end)
        | (ltt_recv p f, ltt_recv q f') => ltt_recv p (fun n => match (f n, f' n) with 
                                                             | (Some (s1, t1), Some (s2, t2)) => Some (s1, force_pmer t1 t2)
                                                             | _                              => None
                                                       end)
        | (_, _) => ltt_end
      end.
    
    Lemma pmergeTwo_can_merge : forall Tl Tl' Tr Tr' T, plain_merge2 T Tl Tr -> plain_merge_in Tl Tl' -> plain_merge_in Tr Tr' -> exists T', plain_merge2 T' Tl' Tr'.
    Proof.
      intros.
      exists (force_pmer Tl' Tr').
      revert H H0 H1. revert Tl Tl' Tr Tr' T.
      pcofix CIH; intros.
      
      pinversion H0.
      - subst.
        pinversion H1; try easy. subst.
        pinversion H2; try easy. subst. 
        rewrite (ltt_eq (force_pmer ltt_end ltt_end)). simpl.
        pfold. constructor.
        apply pmer_in_mon.
        apply pmer_in_mon.
      - subst.
        clear H0.
        pinversion H1; try easy. subst. clear H1.
        pinversion H2; try easy. subst. clear H2.
        pfold. rewrite(ltt_eq (force_pmer (ltt_send p f') (ltt_send p f'0))); simpl.
        apply cpmer_send; try easy.
        
        intro.
        specialize(H5 n). specialize(H4 n). specialize(H n).
        - destruct H5.
          destruct H0. rewrite H1. left.
          rewrite H0 in H. destruct H4.
          destruct H2. rewrite H3. easy.
          destruct H2 as (s1,(t1,(t2,(Ha,Hb)))). rewrite Ha in H.
          destruct H; try easy. destruct H as (s3,(t4,(t5,(t6,Hsa)))). easy.
        - destruct H0 as (s1,(t1,(t2,(Ha,(Hb,Hc))))).
          rewrite Ha in H.
          destruct H; try easy. destruct H as (s2,(t3,(t4,(t5,(Hd,(He,(Hf,Hg))))))).
          inversion He. subst. clear He.
          rewrite Hf in H4.
          destruct H4; try easy. destruct H as (s3,(t6,(t7,(Hh,(Hi,Hj))))).
          inversion Hh. subst. clear Hh.
          rewrite Hb. rewrite Hi.
          right. exists s3. exists (force_pmer t2 t7). exists t2. exists t7.
          split. easy. split. easy. split. easy.
          pclearbot.
          right.
          apply CIH with t4 t6 t3; try easy. 
        apply pmer_in_mon.
        apply pmer_in_mon.
      - subst.
        clear H0.
        pinversion H1; try easy. subst. clear H1.
        pinversion H2; try easy. subst. clear H2.
        pfold. rewrite(ltt_eq (force_pmer (ltt_recv p f') (ltt_recv p f'0))); simpl.
        apply cpmer_recv; try easy.
        
        intro.
        specialize(H5 n). specialize(H4 n). specialize(H n).
        - destruct H5.
          destruct H0. rewrite H1. left.
          rewrite H0 in H. destruct H4.
          destruct H2. rewrite H3. easy.
          destruct H2 as (s1,(t1,(t2,(Ha,Hb)))). rewrite Ha in H.
          destruct H; try easy. destruct H as (s3,(t4,(t5,(t6,Hsa)))). easy.
        - destruct H0 as (s1,(t1,(t2,(Ha,(Hb,Hc))))).
          rewrite Ha in H.
          destruct H; try easy. destruct H as (s2,(t3,(t4,(t5,(Hd,(He,(Hf,Hg))))))).
          inversion He. subst. clear He.
          rewrite Hf in H4.
          destruct H4; try easy. destruct H as (s3,(t6,(t7,(Hh,(Hi,Hj))))).
          inversion Hh. subst. clear Hh.
          rewrite Hb. rewrite Hi.
          right. exists s3. exists (force_pmer t2 t7). exists t2. exists t7.
          split. easy. split. easy. split. easy.
          pclearbot.
          right.
          apply CIH with t4 t6 t3; try easy. 
        apply pmer_in_mon.
        apply pmer_in_mon.
      apply pmer_mon.
    Qed.
    
    Lemma pmergeTwo_to_Into : forall Tl Tl' Tr Tr' T T', plain_merge2 T Tl Tr -> plain_merge2 T' Tl' Tr' -> plain_merge_in Tl Tl' -> plain_merge_in Tr Tr' -> plain_merge_in T T'.
    Proof.
      pcofix CIH; intros.
      pinversion H0.
      - subst.
        - pinversion H2; try easy. subst.
          pinversion H1; try easy. subst.
          pfold. constructor.
          apply pmer_mon.
          apply pmer_in_mon.
      - subst. clear H0.
        pinversion H2. subst. clear H2.
        pinversion H3. subst. clear H3.
        pinversion H1. subst. clear H1.
        pfold. constructor.
        intro.
        specialize(H3 n). specialize(H5 n). specialize(H6 n). specialize(H n).
        destruct H3.
        - destruct H0 as (Ha,(Hb,Hc)). 
          rewrite Ha.
          destruct H.
          - left. easy.
          - destruct H as (s1,(t1,(t2,(t3,(Hd,(He,(Hf,Hg))))))).
            rewrite He in H6. rewrite Hf in H5.
            destruct H6; try easy. rewrite Hb in H. 
            destruct H as (s2,(t4,(t5,H))). easy.
        - destruct H0 as (s1,(t1,(t2,(t3,(Ha,(Hb,(Hc,Hd))))))).
          rewrite Ha. right.
          rewrite Hb in H6. rewrite Hc in H5.
          destruct H6; try easy. destruct H0 as (s2,(t4,(t5,(He,(Hf,Hg))))).
          destruct H5; try easy. destruct H0 as (s3,(t6,(t7,(Hh,(Hi,Hj))))).
          inversion Hi. inversion Hf. subst. clear Hi Hf.
          rewrite Hh in H. rewrite He in H.
          destruct H; try easy.
          destruct H as (s4,(t8,(t9,(t10,(Hk,(Hl,(Hm,Hn))))))).
          inversion Hl. inversion Hm. subst. clear Hl Hm.
          rewrite Hk. exists s4. exists t8. exists t1.
          split. easy. split. easy.
          right. pclearbot.
          apply CIH with t9 t5 t10 t7; try easy.
        apply pmer_mon.
        apply pmer_in_mon.
        apply pmer_in_mon.
      - subst. clear H0.
        pinversion H2. subst. clear H2.
        pinversion H3. subst. clear H3.
        pinversion H1. subst. clear H1.
        pfold. constructor.
        intro.
        specialize(H3 n). specialize(H5 n). specialize(H6 n). specialize(H n).
        destruct H3.
        - destruct H0 as (Ha,(Hb,Hc)). 
          rewrite Ha.
          destruct H.
          - left. easy.
          - destruct H as (s1,(t1,(t2,(t3,(Hd,(He,(Hf,Hg))))))).
            rewrite He in H6. rewrite Hf in H5.
            destruct H6; try easy. rewrite Hb in H. 
            destruct H as (s2,(t4,(t5,H))). easy.
        - destruct H0 as (s1,(t1,(t2,(t3,(Ha,(Hb,(Hc,Hd))))))).
          rewrite Ha. right.
          rewrite Hb in H6. rewrite Hc in H5.
          destruct H6; try easy. destruct H0 as (s2,(t4,(t5,(He,(Hf,Hg))))).
          destruct H5; try easy. destruct H0 as (s3,(t6,(t7,(Hh,(Hi,Hj))))).
          inversion Hi. inversion Hf. subst. clear Hi Hf.
          rewrite Hh in H. rewrite He in H.
          destruct H; try easy.
          destruct H as (s4,(t8,(t9,(t10,(Hk,(Hl,(Hm,Hn))))))).
          inversion Hl. inversion Hm. subst. clear Hl Hm.
          rewrite Hk. exists s4. exists t8. exists t1.
          split. easy. split. easy.
          right. pclearbot.
          apply CIH with t9 t5 t10 t7; try easy.
        apply pmer_mon.
        apply pmer_in_mon.
        apply pmer_in_mon.
      apply pmer_mon.
    Qed.
    
    
    Theorem ispMerge_cont_Into_s : forall f f' T, plain_merge f T -> (forall n, (f n = None /\ f' n = None) \/ (exists t t', f n = Some t /\ f' n = Some t' /\ plain_merge_in t t')) -> exists T', plain_merge f' T' /\ plain_merge_in T T'.
    Proof.
      intros.
      destruct H as (ys,(Ha,Hb)).
      revert H0 Hb Ha. revert T f f'.
      induction ys; intros.
      - inversion Hb. subst.
        pose proof H0 as Hta. pose proof Ha as Htb.
        specialize(Ha 0). specialize(H0 0).
        rewrite (esym Ha) in H0.
        simpl in *.
        destruct H0; try easy.
        destruct H as (t1,(t2,(Hc,(Hd,He)))).
        inversion Hc. subst. clear Hc.
        exists t2. split; try easy.
        exists (slist_x t2).
        split.
        - intro.
          specialize(Htb n).
          specialize(Hta n).
          destruct n; try easy. 
          rewrite (esym Htb) in Hta. simpl in *.
          destruct Hta; try easy.  
          destruct H as (t3,(t4,Hf)). easy.
        - constructor.
      inversion Hb.
      - subst.
        specialize(IHys T (fun n => f (S n)) (fun n => f' (S n))).
        assert(exists T' : ltt,
         plain_merge (fun n : fin => f' n.+1) T' /\ plain_merge_in T T').
        {
          apply IHys; try easy.
          intro.
          specialize(Ha (S n)); try easy.
        }
        clear IHys.
        destruct H as (T',Hd).
        exists T'. split; try easy. destruct Hd.
        inversion H.
        exists (slist_xs None x). destruct H2.
        split.
        - intro.
          destruct n; try easy.
          - specialize(Ha 0).
            specialize(H0 0). rewrite (esym Ha) in H0. simpl in *.
            destruct H0; try easy.
            destruct H0 as (t1,(t2,Hc)). easy.
          - simpl.
            apply H2; try easy.
        - constructor; try easy.
      - subst. clear Hb.
        specialize(IHys T'' (fun n => f (S n)) (fun n => f' (S n))).
        assert(exists T' : ltt,
         plain_merge (fun n : fin => f' n.+1) T' /\ plain_merge_in T'' T').
        {
          apply IHys; try easy.
          intro.
          specialize(Ha (S n)); try easy.
        }
        clear IHys.
        
        destruct H as (Ta,(Hb,Hc)).
        assert(exists Tn, f' 0 = Some Tn).
        {
          specialize(Ha 0).
          specialize(H0 0). rewrite (esym Ha) in H0.
          destruct H0; try easy. destruct H as (t1,(t2,(Hf,(Hg,Hh)))). simpl in *.
          inversion Hf. subst.
          exists t2. easy.
        }
        destruct H as (Tn, H).
        assert(exists Tb, plain_merge2 Tb Tn Ta).
        {
          specialize(pmergeTwo_can_merge T' Tn T'' Ta T); intros.
          apply H1; try easy.
          specialize(Ha 0). simpl in *.
          specialize(H0 0). rewrite H in H0. rewrite (esym Ha) in H0.
          destruct H0; try easy.
          destruct H0 as (t1,(t2,(Hta,(Htb,Htc)))).
          inversion Hta. inversion Htb. easy.
        }
        destruct H1 as (Tb,H1).
        exists Tb.
        assert(plain_merge f' Tb).
        {
          unfold plain_merge. 
          inversion Hb. destruct H3.
          exists (slist_xs (Some Tn) x).
          split.
          - intro.
            destruct n; try easy.
            specialize(H3 n); try easy.
          - apply slm_xs with Ta; try easy.
        }
        split; try easy.
        clear H1 H Hc Hb.
        assert(plain_merge f T).
        {
          exists (slist_xs (Some T') ys).
          split; try easy.
          apply slm_xs with T''; try easy.
        }
        clear H4 H2 Ha. clear T' Ta Tn. rename Tb into T'. clear T'' ys.
        
        inversion H as (xs,(Ha,Hb)). clear H. 
        inversion H3 as (ys,(Hc,Hd)). clear H3.
        assert(SForall2 plain_merge_in xs ys).
        {
          clear Hd Hb. revert Ha Hc H0.
          revert f f'.
          revert ys.
          induction xs; intros.
          - destruct ys; try easy.
            - constructor.
              specialize(H0 0). specialize(Ha 0). specialize(Hc 0).
              simpl in *. rewrite (esym Ha) in H0. rewrite (esym Hc) in H0.
              destruct H0; try easy.
              destruct H as (t1,(t2,(Hd,(He,Hf)))).
              inversion Hd. subst. inversion He. subst. clear Hd He. easy.
            - specialize(onth_to_some ys); intros.
              destruct H as (n,(t,H)).
              specialize(Ha (S n)). specialize(Hc (S n)). specialize(H0 (S n)).
              rewrite (esym Ha) in H0. rewrite (esym Hc) in H0. clear Ha Hc. simpl in *.
              rewrite H in H0. destruct H0; try easy.
              destruct H0 as (t1,(t2,Ha)). easy.
          - destruct ys; try easy.
            - specialize(onth_to_some xs); intros.
              destruct H as (n,(t,H)).
              specialize(Ha (S n)). specialize(Hc (S n)). specialize(H0 (S n)).
              rewrite (esym Ha) in H0. rewrite (esym Hc) in H0. clear Ha Hc. simpl in *.
              rewrite H in H0. destruct H0; try easy.
              destruct H0 as (t1,(t2,Ha)). easy.
            - specialize(IHxs ys (fun n => f (S n)) (fun n => f' (S n))).
              assert(SForall2 plain_merge_in xs ys).
              apply IHxs; try easy.
              intro. specialize(Ha (S n)); try easy.
              intro. specialize(Hc (S n)); try easy.
              
              specialize(Ha 0). specialize(Hc 0). specialize(H0 0).
              rewrite (esym Ha) in H0. rewrite (esym Hc) in H0. clear Ha Hc.
              simpl in *.
              destruct H0.
              - destruct H0. subst.
                constructor; try easy.
              - destruct H0 as (t1,(t2,(Ha,(Hb,Hc)))).
                subst.
                constructor; try easy.
              
        }
        clear Hc Ha H0. clear f f'.
        revert Hb Hd H. revert T T' ys.
        induction xs; intros.
        - destruct ys; try easy.
          inversion H. subst.
          inversion Hb. subst. inversion Hd. subst. easy.
        - destruct ys; try easy.
          inversion H. 
          - subst. clear H.
            inversion Hb. subst. clear Hb.
            inversion Hd. subst. clear Hd.
            specialize(IHxs T'' T''0 ys H4 H7 H5).
            clear H5 H4 H7. clear xs ys.
            
            specialize(pmergeTwo_to_Into x y T'' T''0 T T'); intros.
            apply H; try easy.
            
          - subst. clear H.
            inversion Hb. subst. clear Hb.
            inversion Hd. subst. clear Hd.
            specialize(IHxs T T' ys H0 H2 H1). easy.

    Qed.
    
    Lemma pMerge_Sort_s : forall f'0 q f f'1 p f' n, plain_merge f'0 (ltt_send q f) -> plain_merge f'1 (ltt_recv p f') 
      -> (forall n : fin,
         f'0 n = None /\ f'1 n = None \/
         (exists fa fb : fin -> option (sort * ltt),
            f'0 n = Some (ltt_send q fa) /\
            f'1 n = Some (ltt_recv p fb) /\
            (forall m : fin,
             fa m = None /\ fb m = None \/
             (exists (s' : sort) (t t' : ltt), fa m = Some (s', t) /\ fb m = Some (s', t'))))) 
       -> f n = None /\ f' n = None \/ (exists (s : sort) (t t' : ltt), f n = Some (s, t) /\ f' n = Some (s, t')).
    Proof.
      intros.
      destruct H as (zs,(Ha,Hb)).
      destruct H0 as (ys,(Hc,Hd)).
      revert H1 Hd Hc Hb Ha. revert f'0 q f f'1 p f' n ys.
      induction zs; intros.
      - inversion Hb. subst. clear Hb.
        inversion Hd.
        - subst. clear Hd.
          specialize(Hc 0). specialize(Ha 0). specialize(H1 0).
          simpl in *. rewrite (esym Ha) in H1. rewrite (esym Hc) in H1.
          destruct H1; try easy.
          destruct H as (fa,(fb,(Hd,(He,Hf)))).
          inversion Hd. subst. clear Hd.
          inversion He. subst. clear He.
          specialize(Hf n).
          easy.
        - subst. clear Hd.
          specialize(onth_to_some xs); intros.
          destruct H0 as (n1,(ta,Ht)).
          specialize(Hc (S n1)). specialize(Ha (S n1)). simpl in *. rewrite Ht in Hc.
          specialize(H1 (S n1)). rewrite (esym Ha) in H1. rewrite (esym Hc) in H1.
          destruct H1; try easy. destruct H0 as (fa,(fb,Hs)). easy.
        - subst. clear Hd.
          specialize(onth_to_some xs); intros.
          destruct H2 as (n1,(ta,Ht)).
          specialize(Hc (S n1)). specialize(Ha (S n1)). simpl in *. rewrite Ht in Hc.
          specialize(H1 (S n1)). rewrite (esym Ha) in H1. rewrite (esym Hc) in H1.
          destruct H1; try easy. destruct H1 as (fa,(fb,Hs)). easy.
      - inversion Hb.
        - subst. clear Hb.
          inversion Hd.
          - subst.
            specialize(onth_to_some zs); intros.
            destruct H as (n1,(ta,Ht)).
            specialize(Hc (S n1)). specialize(Ha (S n1)). simpl in *. rewrite Ht in Ha.
            specialize(H1 (S n1)). rewrite (esym Ha) in H1. rewrite (esym Hc) in H1.
            destruct H1; try easy. destruct H as (fa,(fb,Hs)). easy.
          - subst. clear Hd.
            specialize(IHzs (fun n => f'0 (S n)) q f (fun n => f'1 (S n)) p f' n xs).
            apply IHzs; try easy.
            - intro. specialize(Hc (S n0)). easy.
            - intro. specialize(Ha (S n0)). easy.
          - subst. 
            specialize(Hc 0). specialize(Ha 0).
            simpl in *.
            specialize(H1 0). rewrite (esym Ha) in H1. rewrite (esym Hc) in H1.
            destruct H1; try easy. destruct H1 as (fa,(fb,Ht)). easy.
        - subst. clear Hb.
          inversion Hd. 
          - subst.
            specialize(onth_to_some zs); intros.
            destruct H as (n1,(ta,Ht)).
            specialize(Hc (S n1)). specialize(Ha (S n1)). simpl in *. rewrite Ht in Ha.
            specialize(H1 (S n1)). rewrite (esym Ha) in H1. rewrite (esym Hc) in H1.
            destruct H1; try easy. destruct H as (fa,(fb,Hs)). easy.
          - subst.
            specialize(Hc 0). specialize(Ha 0).
            simpl in *.
            specialize(H1 0). rewrite (esym Ha) in H1. rewrite (esym Hc) in H1.
            destruct H1; try easy. destruct H0 as (fa,(fb,Ht)). easy.
          - subst.
            pinversion H2; try easy. subst. pinversion H; try easy. subst.
            clear H2 H.
            specialize(IHzs (fun n => f'0 (S n)) q f3 (fun n => f'1 (S n)) p f4 n xs).
            assert(f3 n = None /\ f4 n = None \/
              (exists (s : sort) (t t' : ltt), f3 n = Some (s, t) /\ f4 n = Some (s, t'))).
            {
              apply IHzs; try easy.
              - intro. specialize(Hc (S n0)); try easy.
              - intro. specialize(Ha (S n0)); try easy.
            }
            specialize(Hc 0). specialize(Ha 0). specialize(H1 0).
            simpl in *. rewrite (esym Ha) in H1. rewrite (esym Hc) in H1.
            destruct H1; try easy. 
            destruct H1 as (fa,(fb,(Hta,(Htb,Htc)))). inversion Hta. subst. inversion Htb. subst.
            clear IHzs Hc Hd Ha H4 H0 Hta Htb.
            specialize(H8 n). specialize(H9 n). specialize(Htc n).
            destruct H8.
            - destruct H9. left. easy.
              destruct H0 as (Ha,(Hb,Hc)). rewrite Hb in Htc. rewrite Hc in H.
              assert(fb n = None).
              {
                destruct Htc; try easy.
                destruct H0 as (s1,(t1,(t2,Ht))). easy.
              }
              assert(f4 n = None).
              {
                destruct H; try easy.
                destruct H as (s1,(t1,(t2,Ht))). easy.
              }
              rewrite H0 in H1. rewrite H2 in H1.
              destruct_exists_and. easy.
            - destruct H0 as (s1,(t1,(t2,(t3,(Ha,(Hb,(Hc,Hd))))))).
              rewrite Ha. rewrite Hb in Htc. rewrite Hc in H.
              right.
              destruct Htc; try easy. 
              destruct H0 as (s2,(t4,(t5,(He,Hf)))). inversion He. subst.
              destruct H; try easy.
              destruct H as (s3,(t6,(t7,(Hg,Hh)))). inversion Hg. subst.
              rewrite Hf in H9. rewrite Hh in H9.
              - destruct H9; try easy.
              - destruct_exists_and. 
                invert_all_some.
                exists x. exists t1. exists x0. easy.
      apply pmer_mon.
      apply pmer_mon.
    Qed.
      
       
    Instance coind_plain_merge : good_merge := {
    
      isMerge := plain_merge;
      
      merge_into_recv := pmerge_into_recv_s;
      merge_label_send := pmerge_label_send_s;
      merge_into_send := pmerge_into_send_s;
      merge_label_send_b := pmerge_label_send_b_s;
    
      MergeInto := plain_merge_in;
      
      isMerge_to_Into := ispMerge_to_Into_s;
      
      MergeInto_end := MergeInto_end_p;
      
      MergeInto_send := MergeInto_send_p;
      MergeInto_recv := MergeInto_recv_p;
      isMerge_cont_Into := ispMerge_cont_Into_s;
      
      MergeInto_to_subtypeC := MergeInto_to_subtypeC_p;
      
      Merge_Sort := pMerge_Sort_s;
    }.
  
  
  
  End coind_pmer.
  
  
Section coind_nmer.
  
    Inductive layer_merge_in : ltt -> ltt -> Prop :=
      | nmer_in_triv  : forall T T', plain_merge_in T T' -> layer_merge_in T T'
      | nmer_in_send : forall p f f', (forall n, (f n = None /\ f' n = None) \/ (exists s t t', f n = Some(s, t) /\ f' n = Some(s, t') /\ layer_merge_in t t')) -> layer_merge_in (ltt_send p f) (ltt_send p f')
      | nmer_in_recv : forall p f f', (forall n, (f' n = None) \/ (exists s t t', f n = Some(s, t) /\ f' n = Some(s, t') /\ layer_merge_in t t')) -> layer_merge_in (ltt_recv p f) (ltt_recv p f').
    
    Section layer_merge_ind_ref.
    Variable P : ltt -> ltt -> Prop.
    Hypothesis P_triv : forall T T', plain_merge_in T T' -> P T T'.
    Hypothesis P_send : forall p f f', (forall n, (f n = None /\ f' n = None) \/ (exists s t t', f n = Some(s, t) /\ f' n = Some(s, t') /\ layer_merge_in t t' /\ P t t')) -> P (ltt_send p f) (ltt_send p f').
    Hypothesis P_recv : forall p f f', (forall n, (f' n = None) \/ (exists s t t', f n = Some(s, t) /\ f' n = Some(s, t') /\ layer_merge_in t t' /\ P t t')) -> P (ltt_recv p f) (ltt_recv p f').
                                                   
  Fixpoint layer_merge_ind_ref (T T' : ltt) (a : layer_merge_in T T') {struct a} : P T T' .
  Proof.
    refine (match a with
      | nmer_in_triv t1 t2 Ha => P_triv t1 t2 Ha
      | nmer_in_send p f1 f2 Ha => P_send p f1 f2 _
      | nmer_in_recv p f1 f2 Ha => P_recv p f1 f2 _
    end); try easy.
    - intros. specialize(Ha n).
      destruct Ha.
      - left. easy.
      - right. destruct_exists_and. exists x. exists x0. exists x1.
        repeat(split; try easy).
        apply layer_merge_ind_ref. easy.
    - intros. specialize(Ha n).
      destruct Ha.
      - left. easy.
      - right. destruct_exists_and. exists x. exists x0. exists x1.
        repeat(split; try easy).
        apply layer_merge_ind_ref. easy.
  Qed.
  
  End layer_merge_ind_ref.
  
    Lemma layer_merge_inv_send : forall [p f T],
      layer_merge_in (ltt_send p f) T -> exists f', T = ltt_send p f' /\
      (forall n, (f n = None /\ f' n = None) \/ (exists s t t', f n = Some(s, t) /\ f' n = Some(s, t') /\ layer_merge_in t t')).
    Proof.
      intros. inversion H; subst.
      - pinversion H0; try apply pmer_in_mon. subst.  
        exists f'. split. easy.
        intros. specialize(H4 n). destruct H4. 
        - left. easy.
        - destruct_exists_and. rewrite H1 H2.
          right. 
          repeat(try eexists; try split; try easy).
          constructor. destruct H3; try easy.
      - exists f'. split. easy. easy.
    Qed.
    
    Lemma layer_merge_inv_recv : forall [p f T],
      layer_merge_in (ltt_recv p f) T -> exists f', T = ltt_recv p f' /\
      (forall n, (f' n = None) \/ (exists s t t', f n = Some(s, t) /\ f' n = Some(s, t') /\ layer_merge_in t t')).
    Proof.
      intros. inversion H; subst.
      - pinversion H0; try apply pmer_in_mon. subst.  
        exists f'. split. easy.
        intros. specialize(H4 n). destruct H4. 
        - left. easy.
        - destruct_exists_and. rewrite H1 H2.
          right. 
          repeat(try eexists; try split; try easy).
          constructor. destruct H3; try easy.
      - exists f'. split. easy. easy.
    Qed.
    
    Lemma layer_merge_inv_send_b : forall [p f' T'],
      layer_merge_in T' (ltt_send p f') -> exists f, T' = ltt_send p f /\
      (forall n, (f n = None /\ f' n = None) \/ (exists s t t', f n = Some(s, t) /\ f' n = Some(s, t') /\ layer_merge_in t t')).
    Proof.
      intros. inversion H; subst.
      - pinversion H0; try apply pmer_in_mon. subst.  
        exists f. split. easy.
        intros. specialize(H3 n). destruct H3. 
        - left. easy.
        - destruct_exists_and. rewrite H1 H2.
          right. 
          repeat(try eexists; try split; try easy).
          constructor. destruct H3; try easy.
      - exists f. split. easy. easy.
    Qed.
    
    Lemma layer_merge_inv_recv_b : forall [p f' T'],
      layer_merge_in T' (ltt_recv p f') -> exists f, T' = ltt_recv p f /\
      (forall n, (f' n = None) \/ (exists s t t', f n = Some(s, t) /\ f' n = Some(s, t') /\ layer_merge_in t t')).
    Proof.
      intros. inversion H; subst.
      - pinversion H0; try apply pmer_in_mon. subst.  
        exists f. split. easy.
        intros. specialize(H3 n). destruct H3. 
        - left. easy.
        - destruct_exists_and. rewrite H1 H2.
          right. 
          repeat(try eexists; try split; try easy).
          constructor. destruct H3; try easy.
      - exists f. split. easy. easy.
    Qed.
     
    
    Lemma MergeInto_end_n : layer_merge_in ltt_end ltt_end.
    Proof.
      constructor.
      apply MergeInto_end_p.
    Qed.
    
    Lemma MergeInto_send_n : forall p fl fr, (forall n, (fl n = None /\ fr n = None) \/ (exists s t t', fl n = Some(s, t) /\ fr n = Some(s, t') /\ layer_merge_in t t')) -> layer_merge_in (ltt_send p fl) (ltt_send p fr).
    Proof.
      intros. apply nmer_in_send.
      intro.
      specialize(H n). 
      destruct H.
      - left. easy.
      - right.
        destruct H as (s1,(t1,(t2,(Ha,(Hb,Hc))))).
        rewrite Ha. rewrite Hb.
        exists s1. exists t1. exists t2.
        split. easy. split. easy. easy.
    Qed.
    
    Lemma MergeInto_recv_n : forall p fl fr, (forall n, (fl n = None /\ fr n = None) \/ (exists s t t', fl n = Some(s, t) /\ fr n = Some(s, t') /\ layer_merge_in t t')) -> layer_merge_in (ltt_recv p fl) (ltt_recv p fr).
    Proof.
      intros. apply nmer_in_recv.
      intro.
      specialize(H n).
      destruct H.
      - left. easy.
      - right.
        destruct H as (s1,(t1,(t2,(Ha,(Hb,Hc))))).
        rewrite Ha. rewrite Hb.
        exists s1. exists t1. exists t2.
        split. easy. split. easy. easy. 
    Qed.
    
    Lemma MergeInto_to_subtypeC_n : forall T T', layer_merge_in T T' -> subtypeC T T'.
    Proof.
      pcofix CIH.
      intros. 
      inversion H0.
      - subst.
        specialize(MergeInto_to_subtypeC_p T T' H); intros.
        eapply paco2_mon; [ exact H1 | ].
        intros. inversion PR.
      - subst. pfold. constructor.
        intro.
        specialize(H n). 
        destruct H.
        - left. easy.
        - right.
          destruct H as (s1,(t1,(t2,(Ha,(Hb,Hc))))).
          rewrite Ha. rewrite Hb.
          exists s1.  exists t1. exists t2.
          split. easy. split. easy.
          right.
          apply CIH; try easy.
      - subst. pfold. constructor.
        intro.
        specialize(H n). 
        destruct H.
        - left. easy.
        - right.
          destruct H as (s1,(t1,(t2,(Ha,(Hb,Hc))))).
          rewrite Ha. rewrite Hb.
          exists s1. exists t1. exists t2.
          split. easy. split. easy.
          right. pclearbot.
          apply CIH; try easy.
    Qed.
        
    Inductive layer_merge2 : ltt -> ltt -> ltt -> Prop :=
      | nfmer_triv : forall T T' T'', plain_merge2 T T' T'' -> layer_merge2 T T' T''
      | nfmer_send : forall p f1 f2 f3, (forall n, (f1 n = None /\ f2 n = None /\ f3 n = None) \/
                                                   (exists s t1 t2 t3, f1 n = Some(s, t1) /\ f2 n = Some(s, t2) /\ f3 n = Some(s, t3) /\ layer_merge2 t1 t2 t3)) -> layer_merge2 (ltt_send p f1) (ltt_send p f2) (ltt_send p f3)
      | nfmer_recv : forall p f1 f2 f3, (forall n, (f1 n = None /\ f2 n = None /\ f3 n = None) \/
                                                   (exists st, f1 n = Some st /\ f2 n = Some st /\ f3 n = None) \/
                                                   (exists st, f1 n = Some st /\ f2 n = None /\ f3 n = Some st) \/
                                                   (exists s t1 t2 t3, f1 n = Some(s, t1) /\ f2 n = Some(s, t2) /\ f3 n = Some(s, t3) /\ layer_merge2 t1 t2 t3)) -> layer_merge2 (ltt_recv p f1) (ltt_recv p f2) (ltt_recv p f3).
   
    Section layer_merge2_ind_ref.
    Variable P : ltt -> ltt -> ltt -> Prop.
    Hypothesis P_triv : forall T T' T'', plain_merge2 T T' T'' -> P T T' T''.
    Hypothesis P_send : forall p f1 f2 f3, (forall n, (f1 n = None /\ f2 n = None /\ f3 n = None) \/
                                                   (exists s t1 t2 t3, f1 n = Some(s, t1) /\ f2 n = Some(s, t2) /\ f3 n = Some(s, t3) /\ layer_merge2 t1 t2 t3 /\ P t1 t2 t3)) -> P (ltt_send p f1) (ltt_send p f2) (ltt_send p f3).
    Hypothesis P_recv : forall p f1 f2 f3, (forall n, (f1 n = None /\ f2 n = None /\ f3 n = None) \/
                                                   (exists st, f1 n = Some st /\ f2 n = Some st /\ f3 n = None) \/
                                                   (exists st, f1 n = Some st /\ f2 n = None /\ f3 n = Some st) \/
                                                   (exists s t1 t2 t3, f1 n = Some(s, t1) /\ f2 n = Some(s, t2) /\ f3 n = Some(s, t3) /\ layer_merge2 t1 t2 t3 /\ P t1 t2 t3)) -> P (ltt_recv p f1) (ltt_recv p f2) (ltt_recv p f3).
                                                   
  Fixpoint layer_merge2_ind_ref (T T' T'' : ltt) (a : layer_merge2 T T' T'') {struct a} : P T T' T''.
  Proof.
    refine (match a with
      | nfmer_triv t1 t2 t3 Ha => P_triv t1 t2 t3 Ha
      | nfmer_send p f1 f2 f3 Ha => P_send p f1 f2 f3 _
      | nfmer_recv p f1 f2 f3 Ha => P_recv p f1 f2 f3 _
    end); try easy.
    - intros. specialize(Ha n).
      destruct Ha.
      - left. easy.
      - right. destruct_exists_and. exists x. exists x0. exists x1. exists x2.
        repeat(split; try easy).
        apply layer_merge2_ind_ref. easy.
    - intros. specialize(Ha n).
      destruct Ha.
      - left. easy.
      - right. 
        destruct H as [Ha | [Ha | Ha]].
        - left. easy.
        - right. left. easy.
        - right. right. destruct_exists_and. 
          exists x. exists x0. exists x1. exists x2.
          repeat(split; try easy).
          apply layer_merge2_ind_ref. easy.
  Qed.
  
  End layer_merge2_ind_ref.
    
    
    Definition layer_merge f T := exists zs, (forall n, onth n zs = f n) /\ @slist_merge layer_merge2 zs T.
    
    Lemma layer_merge2_inv_recv : forall [p f1 T' T''],
        layer_merge2 (ltt_recv p f1) T' T'' -> exists f2 f3, 
        T' = ltt_recv p f2 /\ T'' = ltt_recv p f3 /\
        ((forall n, (f1 n = None /\ f2 n = None /\ f3 n = None) \/
                                                   (exists st, f1 n = Some st /\ f2 n = Some st /\ f3 n = None) \/
                                                   (exists st, f1 n = Some st /\ f2 n = None /\ f3 n = Some st) \/
                                                   (exists s t1 t2 t3, f1 n = Some(s, t1) /\ f2 n = Some(s, t2) /\ f3 n = Some(s, t3) /\ layer_merge2 t1 t2 t3))).
    Proof.
      intros. inversion H; subst.
      - pinversion H0; try apply pmer_mon. subst.
        exists f2. exists f3. split. easy. split. easy.
        intro. specialize(H5 n).
        destruct H5. left. easy. right. right. right.
        destruct H1 as (s,(t1,(t2,(t3,(Ha,(Hb,(Hc,Hd))))))).
        exists s. exists t1. exists t2. exists t3.
        repeat(split; try easy). destruct Hd; try easy. constructor. easy.
      - exists f2. exists f3.
        repeat(split; try easy).
    Qed.
    
    Lemma layer_merge2_inv_recv_c : forall [p f2 T T''],
        layer_merge2 T (ltt_recv p f2) T'' -> exists f1 f3, 
        T = ltt_recv p f1 /\ T'' = ltt_recv p f3 /\
        ((forall n, (f1 n = None /\ f2 n = None /\ f3 n = None) \/
                                                   (exists st, f1 n = Some st /\ f2 n = Some st /\ f3 n = None) \/
                                                   (exists st, f1 n = Some st /\ f2 n = None /\ f3 n = Some st) \/
                                                   (exists s t1 t2 t3, f1 n = Some(s, t1) /\ f2 n = Some(s, t2) /\ f3 n = Some(s, t3) /\ layer_merge2 t1 t2 t3))).
    Proof.
      intros. inversion H; subst.
      - pinversion H0; try apply pmer_mon. subst.
        exists f1. exists f3. split. easy. split. easy.
        intro. specialize(H5 n).
        destruct H5. left. easy. right. right. right.
        destruct H1 as (s,(t1,(t2,(t3,(Ha,(Hb,(Hc,Hd))))))).
        exists s. exists t1. exists t2. exists t3.
        repeat(split; try easy). destruct Hd; try easy. constructor. easy.
      - exists f1. exists f3.
        repeat(split; try easy).
    Qed.
    
    Lemma layer_merge2_inv_send : forall [p f1 T' T''],
        layer_merge2 (ltt_send p f1) T' T'' -> exists f2 f3, 
        T' = ltt_send p f2 /\ T'' = ltt_send p f3 /\
        (forall n, (f1 n = None /\ f2 n = None /\ f3 n = None) \/
                                                   (exists s t1 t2 t3, f1 n = Some(s, t1) /\ f2 n = Some(s, t2) /\ f3 n = Some(s, t3) /\ layer_merge2 t1 t2 t3)).
    Proof.
      intros. inversion H; subst.
      - pinversion H0; try apply pmer_mon. subst.
        exists f2. exists f3. split. easy. split. easy.
        intro. specialize(H5 n).
        destruct H5. left. easy. right.
        destruct H1 as (s,(t1,(t2,(t3,(Ha,(Hb,(Hc,Hd))))))).
        exists s. exists t1. exists t2. exists t3.
        repeat(split; try easy). destruct Hd; try easy. constructor. easy.
      - exists f2. exists f3.
        repeat(split; try easy).
    Qed.
    
    Lemma layer_merge2_inv_send_c : forall [p f2 T T''],
        layer_merge2 T (ltt_send p f2) T'' -> exists f1 f3, 
        T = ltt_send p f1 /\ T'' = ltt_send p f3 /\
        (forall n, (f1 n = None /\ f2 n = None /\ f3 n = None) \/
                                                   (exists s t1 t2 t3, f1 n = Some(s, t1) /\ f2 n = Some(s, t2) /\ f3 n = Some(s, t3) /\ layer_merge2 t1 t2 t3)).
    Proof.
      intros. inversion H; subst.
      - pinversion H0; try apply pmer_mon. subst.
        exists f1. exists f3. split. easy. split. easy.
        intro. specialize(H5 n).
        destruct H5. left. easy. right.
        destruct H1 as (s,(t1,(t2,(t3,(Ha,(Hb,(Hc,Hd))))))).
        exists s. exists t1. exists t2. exists t3.
        repeat(split; try easy). destruct Hd; try easy. constructor. easy.
      - exists f1. exists f3.
        repeat(split; try easy).
    Qed.

    
    Lemma lmerge_into_recv_s : forall g p f, layer_merge g (ltt_recv p f) -> forall n s t, f n = Some(s, t) -> layer_merge (through_merge_r g n) t.
    Proof.
      intros.
      destruct H as (zs, (Ha,Hb)).
      revert Ha Hb H0. revert n s t f g.
      induction zs; intros. 
      - inversion Hb. subst. clear Hb.
        unfold through_merge_r.
        exists (slist_x t).
        split.
        - intro.
          specialize(Ha n0). rewrite (esym Ha).
          destruct n0; try easy.
          simpl. rewrite H0. easy.
        - constructor.
      - inversion Hb.
        - subst.
          specialize(IHzs n s t f (fun n => g (S n))).
          assert(layer_merge (through_merge_r (fun n : fin => g n.+1) n) t).
          {
            apply IHzs; try easy.
            intro. 
            specialize(Ha (S n0)); try easy.
          }
          inversion H. destruct H1.
          exists (slist_xs None x).
          split.
          - intro. 
            destruct n0.
            - specialize(Ha 0). unfold through_merge_r.
              rewrite (esym Ha). simpl in *. easy.
            - specialize(H1 n0); try easy.
          - constructor; try easy.
        - subst.
          specialize(layer_merge2_inv_recv H2); intros. destruct_exists_and. subst. 
          specialize(H3 n). rewrite H0 in H3.
          destruct H3; try easy. rename x into f2. rename x0 into f3.
          destruct H.
          - destruct H as (st,(Hc,(Hd,He))).
            inversion Hc. subst. clear Hc. clear Hb H2.
            exists (slist_x t).
            split.
            - intro.
              unfold through_merge_r.
              destruct n0.
              - simpl in *.
                specialize(Ha 0). rewrite (esym Ha).
                simpl. rewrite Hd. easy.
              - simpl in *.
                specialize(Ha (S n0)).
                simpl in Ha. rewrite (esym Ha).
                clear Hd H0 Ha IHzs.
                clear f s g t.
                revert He H4. revert n n0 f3. clear f2.
                induction zs; intros.
                - inversion H4. subst.
                  destruct n0; try easy. simpl. rewrite He. easy.
                - inversion H4. subst.
                  - destruct n0; try easy.
                    specialize(IHzs n n0 f3 He H2). easy.
                  subst.
                  specialize(layer_merge2_inv_recv H1); intros. destruct_exists_and. subst.
                  specialize(H2 n). rewrite He in H2.
                  destruct H2.
                  - destruct H as (Ha,(Hb,Hc)). clear Ha.
                    destruct n0; try easy.
                    - simpl. rewrite Hb. easy.
                    - specialize(IHzs n n0 x0 Hc H3). easy.
                  - destruct H. destruct H; try easy.
                    destruct H. destruct H; try easy.
                    destruct H as (s1,(t1,(t2,(t3,Hb)))). easy.
              - constructor.
          - destruct H.
            destruct H as (st,(Hc,(Hd,He))).
            inversion Hc. subst.
            specialize(IHzs n s t f3 (fun n => g (S n))).
            assert(layer_merge (through_merge_r (fun n : fin => g n.+1) n) t).
            {
              apply IHzs; try easy.
              intro. specialize(Ha (S n0)). easy.
            }
            inversion H; try easy. destruct H1.
            exists (slist_xs None x); try easy.
            split.
            - intro. 
              destruct n0.
              - unfold through_merge_r. simpl in *.
                specialize(Ha 0). rewrite (esym Ha). simpl. rewrite Hd. easy.
              - specialize(H1 n0). easy.
            - constructor; try easy.
          - destruct H as (s1,(t1,(t2,(t3,(Hc,(Hd,(He,Hf))))))).
            inversion Hc. subst. clear Hc.
            specialize(IHzs n s1 t3 f3 (fun n => g (S n))).
            assert(layer_merge (through_merge_r (fun n : fin => g n.+1) n) t3).
            {
              apply IHzs; try easy.
              intro.
              specialize(Ha (S n0)); try easy.
            }
            clear IHzs.
            inversion H.
            exists (slist_xs (Some t2) x). destruct H1.
            split.
            - intro.
              destruct n0.
              - unfold through_merge_r.
                simpl in *.
                specialize(Ha 0). rewrite (esym Ha). simpl.
                rewrite Hd. easy.
              - specialize(H1 n0). easy.
            - apply slm_xs with t3; try easy.
    Qed.
    
    Lemma lmerge_label_send_s : forall g p f, layer_merge g (ltt_send p f) -> forall n q f' l st, g n = Some (ltt_send q f') -> f' l = Some st -> exists st', f l = Some st'.
    Proof.
      intros g p f H.
      destruct H as (zs,(Ha,Hb)).
      revert Ha Hb. revert g f.
      induction zs; intros.
      - inversion Hb. subst.
        assert (n = 0).
        {
          destruct n; try easy.
          specialize(Ha (S n)). simpl in *. rewrite H in Ha. easy.
        }
        subst.
        specialize(Ha 0). rewrite H in Ha. 
        inversion Ha. subst. exists st. easy.
      - inversion Hb.
        - subst.
          specialize(IHzs (fun n => g (S n)) f).
          assert(forall (n : fin) q (f' : fin -> option (sort * ltt))
         (l : fin) (st : sort * ltt),
       (fun n0 : fin => g n0.+1) n = Some (ltt_send q f') ->
       f' l = Some st -> exists st' : sort * ltt, f l = Some st').
          {
            apply IHzs; try easy.
            intro.
            specialize(Ha (S n0)). easy.
          }
          clear IHzs.
          destruct n.
          - specialize(Ha 0). rewrite H in Ha. easy.
          - specialize(H1 n q f'). apply H1 with st; try easy.
        - subst. clear Hb.
          specialize(layer_merge2_inv_send H3); intros. destruct_exists_and.
          subst. rename x into f2. rename x0 into f3.
          specialize(IHzs (fun n => g (S n)) f3).
          assert(forall (n : fin) q (f' : fin -> option (sort * ltt))
         (l : fin) (st : sort * ltt),
       (fun n0 : fin => g n0.+1) n = Some (ltt_send q f') ->
       f' l = Some st -> exists st' : sort * ltt, f3 l = Some st').
          {
            apply IHzs; try easy.
            intro.
            specialize(Ha (S n0)); try easy.
          }
          clear IHzs.
          destruct n.
          - specialize(Ha 0). rewrite H in Ha.
            inversion Ha. subst. clear Ha.
            specialize(H4 l). rewrite H0 in H4.
            destruct H4; try easy.
            destruct H2 as (s1,(t1,(t2,(t3,(Ha,(Hb,(Hc,Hd))))))).
            inversion Hb. subst. clear Hb.
            exists (s1, t1). easy.
          - specialize(H1 n q f' l st H H0).
            destruct H1 as (sta,Ht).
            specialize(H4 l). rewrite Ht in H4.
            destruct H4; try easy.
            destruct H1 as (s1,(t1,(t2,(t3,(Hb,(Hc,(Hd,He))))))).
            inversion Hd. subst. clear Hd. 
            exists (s1, t1). easy.
    Qed.
    
    Lemma lmerge_label_send_b_s : forall g p f, layer_merge g (ltt_send p f) -> forall n q f' l st, g n = Some (ltt_send q f') -> f l = Some st -> exists st', f' l = Some st'.
    Proof.
      intros g p f H.
      destruct H as (zs, (Ha,Hb)).
      revert Ha Hb. revert g f.
        
      induction zs; intros.
      - inversion Hb. subst.
        assert (n = 0).
        {
          destruct n; try easy.
          specialize(Ha (S n)). simpl in *. rewrite H in Ha. easy.
        }
        subst.
        specialize(Ha 0). rewrite H in Ha. 
        inversion Ha. subst. exists st. easy.
      - inversion Hb.
        - subst.
          specialize(IHzs (fun n => g (S n)) f).
          assert(forall (n : fin) q (f' : fin -> option (sort * ltt)) 
         (l : fin) (st : sort * ltt),
       (fun n0 : fin => g n0.+1) n = Some (ltt_send q f') ->
       f l = Some st -> exists st' : sort * ltt, f' l = Some st').
          {
            apply IHzs; try easy.
            intro.
            specialize(Ha (S n0)). easy.
          }
          clear IHzs.
          destruct n.
          - specialize(Ha 0). rewrite H in Ha. easy.
          - specialize(H1 n q f'). apply H1 with st; try easy.
        - subst. clear Hb.
          specialize(layer_merge2_inv_send H3); intros. destruct_exists_and.
          subst. rename x into f2. rename x0 into f3.
          specialize(IHzs (fun n => g (S n)) f3).
          assert(forall (n : fin) q (f' : fin -> option (sort * ltt)) 
         (l : fin) (st : sort * ltt),
       (fun n0 : fin => g n0.+1) n = Some (ltt_send q f') ->
       f3 l = Some st -> exists st' : sort * ltt, f' l = Some st').
          {
            apply IHzs; try easy.
            intro.
            specialize(Ha (S n0)); try easy.
          }
          clear IHzs H3.
          destruct n.
          - specialize(Ha 0). rewrite H in Ha.
            inversion Ha. subst. clear Ha.
            specialize(H4 l). rewrite H0 in H4.
            destruct H4; try easy.
            destruct H2 as (s1,(t1,(t2,(t3,(Ha,(Hb,(Hc,Hd))))))).
            exists (s1, t2). easy.
          - specialize(H4 l). rewrite H0 in H4.
            destruct H4; try easy.
            destruct H2 as (s1,(t1,(t2,(t3,(Hb,(Hc,(Hd,He))))))).
            specialize(H1 n q f' l (s1, t3)).
            apply H1; try easy.
    Qed.
    
    Lemma lmerge_into_send_s : forall g p f, layer_merge g (ltt_send p f) -> forall n s t, f n = Some(s, t) -> layer_merge (through_merge_s g n) t.
    Proof.
     intros.
      destruct H as (zs, (Ha,Hb)).
      revert Ha Hb H0. revert n s t f g.
      induction zs; intros. 
      - inversion Hb. subst. clear Hb.
        unfold through_merge_s.
        exists (slist_x t).
        split.
        - intro.
          specialize(Ha n0). rewrite (esym Ha).
          destruct n0; try easy.
          simpl. rewrite H0. easy.
        - constructor.
      - inversion Hb.
        - subst.
          specialize(IHzs n s t f (fun n => g (S n))).
          assert(layer_merge (through_merge_s (fun n : fin => g n.+1) n) t).
          {
            apply IHzs; try easy.
            intro. 
            specialize(Ha (S n0)); try easy.
          }
          inversion H. destruct H1.
          exists (slist_xs None x).
          split.
          - intro. 
            destruct n0.
            - specialize(Ha 0). unfold through_merge_s.
              rewrite (esym Ha). simpl in *. easy.
            - specialize(H1 n0); try easy.
          - constructor; try easy.
        - subst.
          specialize(layer_merge2_inv_send H2); intros. destruct_exists_and. subst.
          rename x into f2. rename x0 into f3.
          specialize(H3 n). rewrite H0 in H3.
          destruct H3; try easy.
          destruct H as (s1,(t1,(t2,(t3,(Hc,(Hd,(He,Hf))))))).
          - inversion Hc. subst. clear Hc. clear Hb H2.
   
            specialize(IHzs n s1 t3 f3 (fun n => g (S n))).
            assert(layer_merge (through_merge_s (fun n : fin => g n.+1) n) t3).
            {
              apply IHzs; try easy.
              intro. specialize(Ha (S n0)). easy.
            }
            inversion H; try easy. destruct H1.
            exists (slist_xs (Some t2) x); try easy.
            split.
            - intro. 
              destruct n0.
              - unfold through_merge_s.
                simpl in *.
                specialize(Ha 0). rewrite (esym Ha). simpl.
                rewrite Hd. easy.
              - specialize(H1 n0). easy.
            - apply slm_xs with t3; try easy.
    Qed.
    
    Lemma layer_merge_in_refl : forall T, layer_merge_in T T.
    Proof.
      intros.
      constructor. apply plain_merge_in_refl.
    Qed.
    
    Lemma lmer2_to_in_l : forall T T' T'', layer_merge2 T T' T'' -> layer_merge_in T T'.
    Proof.
      apply layer_merge2_ind_ref; intros.
      - constructor. apply pmer2_to_in_l with T''; try easy.
      - apply nmer_in_send. 
        intros. specialize(H n).
        destruct H.
        - left. easy.
        - right. destruct_exists_and. rewrite H H0. 
          repeat(try eexists; try split; try easy).
      - apply nmer_in_recv.
        intros. specialize(H n).
        destruct H as [Ha | [Ha | [Ha | Ha]]].
        - left. easy.
        - destruct_exists_and. rewrite H H0. 
          right. destruct x. repeat(try eexists; try split; try easy).
          apply layer_merge_in_refl.
        - destruct_exists_and. rewrite H H0.  
          left. easy.
        - destruct_exists_and. rewrite H H0. 
          right. repeat(try eexists; try split; try easy).
    Qed.
    
    Lemma lmer2_to_in_r : forall T T' T'', layer_merge2 T T' T'' -> layer_merge_in T T''.
    Proof.
      apply layer_merge2_ind_ref; intros.
      - constructor.
        apply pmer2_to_in_r with T'. easy.
      - apply nmer_in_send. 
        intros. specialize(H n).
        destruct H.
        - left. easy.
        - right. destruct_exists_and. rewrite H H1. 
          repeat(try eexists; try split; try easy).
      - apply nmer_in_recv.
        intros. specialize(H n).
        destruct H as [Ha | [Ha | [Ha | Ha]]].
        - left. easy.
        - destruct_exists_and. rewrite H H1.  
          left. easy.
        - destruct_exists_and. rewrite H H1. 
          right. destruct x. repeat(try eexists; try split; try easy).
          apply layer_merge_in_refl.
        - destruct_exists_and. rewrite H H1. 
          right. repeat(try eexists; try split; try easy).
    Qed.
    
    Lemma layer_merge_in_trans : forall T T' T'', layer_merge_in T T' -> layer_merge_in T' T'' -> layer_merge_in T T''.
    Proof.
      intros. revert H0. revert T''.
       refine (
        layer_merge_ind_ref
        (fun A B => forall C, layer_merge_in B C -> layer_merge_in A C)
        _
        _ 
        _
        T T' H
      ); clear H; clear T T'.
      - intros.
        revert H. revert T.
        refine (
          layer_merge_ind_ref 
          (fun B C => forall A, plain_merge_in A B -> layer_merge_in A C)
          _ 
          _
          _
          T' C H0
        ); clear H0; clear T' C.
        - intros.
          constructor. apply plain_merge_in_trans with T; try easy.
        - intros.
          pinversion H0; try apply pmer_in_mon. subst.
          apply nmer_in_send.
          intros. specialize(H3 n). specialize(H n).
          destruct H.
          - destruct H3. left. easy.
            destruct_exists_and. rewrite H2 in H. easy.
          - destruct_exists_and. rewrite H in H3.
            destruct H3; try easy. destruct_exists_and. invert_all_some.
            rewrite H1 H3. right.
            repeat(try eexists; try split; try easy).
            apply H4. destruct H6; try easy.
        - intros.
          pinversion H0; try apply pmer_in_mon. subst.
          apply nmer_in_recv.
          intros. specialize(H3 n). specialize(H n).
          destruct H.
          - left. easy.
          - destruct_exists_and. rewrite H in H3. 
            destruct H3; try easy. destruct_exists_and. invert_all_some.
            rewrite H1 H3. right.
            repeat(try eexists; try split; try easy).
            apply H4. destruct H6; try easy.
      - intros.
        specialize(layer_merge_inv_send H0); intros. 
        destruct_exists_and. subst.
        apply nmer_in_send. intros.
        specialize(H n). specialize(H2 n).
        destruct H.
        - destruct H2. left. easy. 
          destruct_exists_and. rewrite H4 in H1. easy.
        - destruct_exists_and. rewrite H1 in H2.
          destruct H2; try easy. destruct_exists_and. invert_all_some.
          rewrite H H5. right.
          repeat(try eexists; try split; try easy). 
          apply H4. easy.
      - intros.
        specialize(layer_merge_inv_recv H0); intros. 
        destruct_exists_and. subst.
        apply nmer_in_recv. intros.
        specialize(H n). specialize(H2 n).
        destruct H2.
        - left. easy.
        - destruct_exists_and. rewrite H1 in H.
          destruct H; try easy. destruct_exists_and. invert_all_some.
          rewrite H2 H. right.
          repeat(try eexists; try split; try easy). 
          apply H6. easy.
    Qed.
        
    
    Lemma islMerge_to_Into_s : forall f T l T', layer_merge f T -> f l = Some T' -> layer_merge_in T T'.
    Proof.
      intros.
      destruct H as (ys,(Ha,Hb)).
      revert Ha Hb H0. revert T l T' f.
      induction ys; intros.
      - inversion Hb. subst.
        specialize(Ha l). rewrite H0 in Ha. destruct l; try easy.
        inversion Ha. subst.
        apply layer_merge_in_refl; try easy.
      - inversion Hb.
        - subst. clear Hb.
          destruct l; try easy.
          - specialize(Ha 0). rewrite H0 in Ha. easy.
          - apply IHys with l (fun n => f (S n)); try easy.
            intro. specialize(Ha (S n)); try easy.
        - subst. clear Hb.
          destruct l.
          - specialize(Ha 0). rewrite H0 in Ha.
            inversion Ha. subst.
            apply lmer2_to_in_l with T''; try easy.
          - specialize(IHys T'' l T' (fun n => f (S n))).
            assert(layer_merge_in T'' T').
            {
              apply IHys; try easy.
              intro.
              specialize(Ha (S n)); try easy.
            }
            clear IHys.
            clear Ha H0 H4.
            apply layer_merge_in_trans with T''; try easy.
            apply lmer2_to_in_r with T'0; try easy.
    Qed.
    
    Lemma force_fmer_on_p : forall Tl Tl' Tr Tr' T, 
      plain_merge2 T Tl Tr -> 
      plain_merge_in Tl Tl' -> 
      plain_merge_in Tr Tr' -> 
      plain_merge2 (force_fmer Tl' Tr') Tl' Tr'.
    Proof.
      pcofix CIH; intros.
      pinversion H0.
      - subst.
        pinversion H1; try easy. subst.
        pinversion H2; try easy. subst. 
        rewrite (ltt_eq (force_fmer ltt_end ltt_end)). simpl.
        pfold. constructor.
        apply pmer_in_mon.
        apply pmer_in_mon.
      - subst.
        clear H0.
        pinversion H1; try easy. subst. clear H1.
        pinversion H2; try easy. subst. clear H2.
        pfold. rewrite(ltt_eq (force_fmer (ltt_send p f') (ltt_send p f'0))); simpl.
        apply cpmer_send; try easy.
        
        intro.
        specialize(H5 n). specialize(H4 n). specialize(H n).
        - destruct H5.
          destruct H0. rewrite H1. left.
          rewrite H0 in H. destruct H4.
          destruct H2. rewrite H3. easy.
          destruct H2 as (s1,(t1,(t2,(Ha,Hb)))). rewrite Ha in H.
          destruct H; try easy. destruct H as (s3,(t4,(t5,(t6,Hsa)))). easy.
        - destruct H0 as (s1,(t1,(t2,(Ha,(Hb,Hc))))).
          rewrite Ha in H.
          destruct H; try easy. destruct H as (s2,(t3,(t4,(t5,(Hd,(He,(Hf,Hg))))))).
          inversion He. subst. clear He.
          rewrite Hf in H4.
          destruct H4; try easy. destruct H as (s3,(t6,(t7,(Hh,(Hi,Hj))))).
          inversion Hh. subst. clear Hh.
          rewrite Hb. rewrite Hi.
          right. exists s3. exists (force_fmer t2 t7). exists t2. exists t7.
          split. easy. split. easy. split. easy.
          pclearbot.
          right.
          apply CIH with t4 t6 t3; try easy. 
        apply pmer_in_mon.
        apply pmer_in_mon.
      - subst.
        clear H0.
        pinversion H1; try easy. subst. clear H1.
        pinversion H2; try easy. subst. clear H2.
        pfold. rewrite(ltt_eq (force_fmer (ltt_recv p f') (ltt_recv p f'0))); simpl.
        apply cpmer_recv; try easy.
        
        intro.
        specialize(H5 n). specialize(H4 n). specialize(H n).
        - destruct H5.
          destruct H0. rewrite H1. left.
          rewrite H0 in H. destruct H4.
          destruct H2. rewrite H3. easy.
          destruct H2 as (s1,(t1,(t2,(Ha,Hb)))). rewrite Ha in H.
          destruct H; try easy. destruct H as (s3,(t4,(t5,(t6,Hsa)))). easy.
        - destruct H0 as (s1,(t1,(t2,(Ha,(Hb,Hc))))).
          rewrite Ha in H.
          destruct H; try easy. destruct H as (s2,(t3,(t4,(t5,(Hd,(He,(Hf,Hg))))))).
          inversion He. subst. clear He.
          rewrite Hf in H4.
          destruct H4; try easy. destruct H as (s3,(t6,(t7,(Hh,(Hi,Hj))))).
          inversion Hh. subst. clear Hh.
          rewrite Hb. rewrite Hi.
          right. exists s3. exists (force_fmer t2 t7). exists t2. exists t7.
          split. easy. split. easy. split. easy.
          pclearbot.
          right.
          apply CIH with t4 t6 t3; try easy. 
        apply pmer_in_mon.
        apply pmer_in_mon.
      apply pmer_mon.
    Qed.
    
    Lemma lmergeTwo_can_merge : forall Tl Tl' Tr Tr' T, layer_merge2 T Tl Tr -> layer_merge_in Tl Tl' -> layer_merge_in Tr Tr' -> exists T', layer_merge2 T' Tl' Tr'.
    Proof.
      intros.
      exists (force_fmer Tl' Tr').
      revert H0 H1. revert Tl' Tr'.
      refine (
        layer_merge2_ind_ref
        (fun T Tl Tr => forall Tl' Tr', layer_merge_in Tl Tl' ->
            layer_merge_in Tr Tr' -> layer_merge2 (force_fmer Tl' Tr') Tl' Tr')
        _
        _ 
        _
        T Tl Tr H
      ); clear H; clear Tl Tr T.
      - intros.
        revert H H1. revert T T'' Tr'.
        refine (
          layer_merge_ind_ref 
          (fun T' Tl' => forall T T'' Tr' : ltt,
            plain_merge2 T T' T'' ->
            layer_merge_in T'' Tr' -> layer_merge2 (force_fmer Tl' Tr') Tl' Tr')
          _ _ _
          T' Tl' H0
        ); clear H0; clear T' Tl'.
        - intros.
          revert H H0. revert T T' T0.
          refine (
            layer_merge_ind_ref 
            (fun T'' Tr' => forall T T' T0 : ltt,
              plain_merge_in T T' -> 
              plain_merge2 T0 T T'' -> layer_merge2 (force_fmer T' Tr') T' Tr')
            _ _ _
            T'' Tr' H1
          ); clear H1; clear T'' Tr'.
          - intros. constructor.
            apply force_fmer_on_p with T0 T T1; try easy.
          - intros.
            pinversion H1; try apply pmer_mon; subst. clear H1.
            pinversion H0; try apply pmer_in_mon; subst. clear H0.
            rewrite (ltt_eq (force_fmer (ltt_send p f'0) (ltt_send p f'))); simpl.
            apply nfmer_send.
            intros. specialize(H4 n). specialize(H5 n). specialize(H n).
            destruct H4. 
            - destruct H0. rewrite H1. 
              - destruct H. left. easy.
              - destruct_exists_and. rewrite H in H5.
                destruct H5; try easy. destruct_exists_and. rewrite H0 in H6. easy.
            - destruct_exists_and. rewrite H0 in H5.
              destruct H5; try easy. destruct_exists_and.
              rewrite H5 in H. destruct H; try easy. destruct_exists_and.
              invert_all_some. rewrite H1. rewrite H7. right.
              repeat(try eexists; try split; try easy). pclearbot.
              apply H9 with x4 x3; try easy. 
          - intros.
            pinversion H1; try apply pmer_mon; subst. clear H1.
            pinversion H0; try apply pmer_in_mon; subst. clear H0.
            rewrite (ltt_eq (force_fmer (ltt_recv p f'0) (ltt_recv p f'))); simpl.
            apply nfmer_recv.
            intros. specialize(H4 n). specialize(H5 n). specialize(H n).
            destruct H4. 
            - destruct H0. rewrite H1. 
              - destruct H. left. rewrite H. easy.
              - destruct_exists_and. rewrite H in H5.
                destruct H5; try easy. destruct_exists_and. rewrite H0 in H6. easy.
            - destruct_exists_and. rewrite H0 in H5.
              destruct H5; try easy. destruct_exists_and.
              rewrite H5 in H. destruct H; try easy.
              - invert_all_some. rewrite H1. rewrite H. right. left.
                eexists. repeat(split; try easy).
              - destruct_exists_and. invert_all_some.
                rewrite H1. rewrite H7.
                right. right. right.
                repeat(try eexists; try split; try easy). pclearbot.
                apply H9 with x4 x3; try easy. 
        - intros.
          pinversion H0; try apply pmer_mon; subst. clear H0.
          specialize(layer_merge_inv_send H1); intros. destruct_exists_and. subst.
          rewrite (ltt_eq (force_fmer (ltt_send p f') (ltt_send p x))); simpl.
          apply nfmer_send.
          intros.
          specialize(H2 n). specialize(H6 n). specialize(H n).
          destruct H.
          - destruct H. rewrite H0. left.
            destruct H2; try easy. destruct_exists_and. 
            rewrite H2 in H6. destruct H6; try easy. destruct_exists_and.
            rewrite H6 in H. easy.
          - destruct_exists_and. rewrite H in H6. 
            destruct H6; try easy. destruct_exists_and. rewrite H7 in H2.
            destruct H2; try easy. destruct_exists_and. invert_all_some.
            rewrite H0. rewrite H9. right.
            repeat(try eexists; try split; try easy). pclearbot.
            apply H4 with x4 x8; try easy.
        - intros. 
          pinversion H0; try apply pmer_mon; subst. clear H0.
          specialize(layer_merge_inv_recv H1); intros. destruct_exists_and. subst.
          rewrite (ltt_eq (force_fmer (ltt_recv p f') (ltt_recv p x))); simpl.
          apply nfmer_recv.
          intros.
          specialize(H2 n). specialize(H6 n). specialize(H n).
          destruct H.
          - rewrite H.
            destruct H2.
            - rewrite H0. left. easy.
            - destruct_exists_and. rewrite H0 in H6.
              destruct H6; try easy. destruct_exists_and.
              rewrite H2. right. right. left.
              eexists. easy.
          - destruct_exists_and. rewrite H0.
            rewrite H in H6. destruct H6; try easy. 
            destruct_exists_and. destruct H2.
            - rewrite H2. right. left. eexists. easy.
            - destruct_exists_and. rewrite H7 in H2. invert_all_some.
              rewrite H9. right. right. right. 
              repeat(try eexists; try split; try easy). pclearbot.
              apply H4 with x4 x8; try easy.
      - intros.
        specialize(layer_merge_inv_send H0); intros; clear H0.
        specialize(layer_merge_inv_send H1); intros; clear H1.
        destruct_exists_and; subst.
        rewrite (ltt_eq (force_fmer (ltt_send p x0) (ltt_send p x))); simpl.
        apply nfmer_send. intros.
        specialize(H2 n). specialize(H3 n). specialize(H n).
        destruct H.
        - destruct H as (Ha,(Hb,Hc)). 
          destruct H3. destruct H2. destruct H0. destruct H. rewrite H2. left. easy. 
          rewrite Hc in H0. destruct_exists_and. easy.
          rewrite Hb in H. destruct_exists_and. easy.
        - destruct_exists_and. rewrite H0 in H3. destruct H3; try easy.
          destruct_exists_and. rewrite H6. rewrite H1 in H2. destruct H2; try easy.
          destruct_exists_and. rewrite H8. invert_all_some.
          right. repeat(try eexists; try split; try easy).
          apply H5; try easy.
      - intros.
        specialize(layer_merge_inv_recv H0); intros; clear H0.
        specialize(layer_merge_inv_recv H1); intros; clear H1.
        destruct_exists_and; subst.
        rewrite (ltt_eq (force_fmer (ltt_recv p x0) (ltt_recv p x))); simpl.
        apply nfmer_recv. intros.
        specialize(H2 n). specialize(H3 n). specialize(H n).
        destruct H3.
        - rewrite H0.
          destruct H2.
          - rewrite H1. left. easy.
          - destruct_exists_and. rewrite H1 in H.
            destruct H as [Ha | [Ha | [Ha | Ha]]]; destruct_exists_and; try easy.
            - rewrite H2. right. right. left. eexists. easy.
            - rewrite H2. right. right. left. eexists. easy.
        - destruct_exists_and.
          rewrite H1. destruct H2.
          - rewrite H2.
            right. left. eexists. easy.
          - destruct_exists_and. rewrite H4.
            rewrite H2 H0 in H.
            destruct H as [Ha | [Ha | [Ha | Ha]]]; destruct_exists_and; try easy.
            right. right. right. invert_all_some.
            repeat(try eexists; try split; try easy).
            apply H9; try easy.
    Qed.
    
    Lemma lmergeTwo_to_Into : forall Tl Tl' Tr Tr' T T', layer_merge2 T Tl Tr -> layer_merge2 T' Tl' Tr' -> layer_merge_in Tl Tl' -> layer_merge_in Tr Tr' -> layer_merge_in T T'.
    Proof.
      intros. revert H0 H1 H2. revert Tl' Tr' T'.
      refine (
        layer_merge2_ind_ref
        (fun T Tl Tr => forall Tl' Tr' T' : ltt,
          layer_merge2 T' Tl' Tr' ->
          layer_merge_in Tl Tl' -> layer_merge_in Tr Tr' -> layer_merge_in T T')
        _
        _ 
        _
        T Tl Tr H
      ); clear H; clear Tl Tr T.
      {
        intros. revert H H1 H2. revert T T' T''.
        refine (
          layer_merge2_ind_ref
          (fun T'0 Tl' Tr' => forall T T' T'' : ltt,
              plain_merge2 T T' T'' ->
              layer_merge_in T' Tl' -> layer_merge_in T'' Tr' -> layer_merge_in T T'0)
          _
          _ 
          _
          T'0 Tl' Tr' H0
        ); clear H0; clear Tl' Tr' T'0.
        {
          intros. revert H H0 H2. revert T T'' T0 T''0.
          refine (
            layer_merge_ind_ref 
            (fun T'0 T' => forall T T'' T0 T''0 : ltt,
              plain_merge2 T T' T'' ->
              plain_merge2 T0 T'0 T''0 -> layer_merge_in T''0 T'' -> layer_merge_in T0 T)
            _ _ _ 
            T'0 T' H1
          ); clear H1; clear T' T'0.
          {
            intros. revert H H0 H1. revert T T' T0 T1.
            refine (
              layer_merge_ind_ref
              (fun T''0 T'' => forall T T' T0 T1 : ltt,
                plain_merge_in T T' ->
                plain_merge2 T0 T' T'' -> plain_merge2 T1 T T''0 -> layer_merge_in T1 T0)
                _ _ _ 
                T''0 T'' H2
            ); clear H2; clear T'' T''0.
            {
              intros. constructor.
              apply pmergeTwo_to_Into with T0 T'0 T T'; try easy.
            }
            - intros.
              pinversion H1; try apply pmer_mon; subst; clear H1.
              pinversion H2; try apply pmer_mon; subst; clear H2.
              pinversion H0; try apply pmer_in_mon; subst; clear H0.
              apply nmer_in_send. intros.
              specialize(H n). specialize(H6 n). specialize(H5 n). specialize(H2 n).
              destruct H5.
              - destruct H6. left. easy.
                destruct_exists_and. rewrite H6 H4 in H.
                destruct H; try easy. destruct_exists_and. easy.
              - destruct_exists_and. rewrite H1 in H2. destruct H2; try easy.
                destruct_exists_and. rewrite H3 in H. destruct H; try easy.
                destruct_exists_and. rewrite H5 in H6. destruct H6; try easy.
                destruct_exists_and. rewrite H12 in H8. invert_all_some.
                right. rewrite H6 H0. 
                repeat(try eexists; try split; try easy). pclearbot.
                apply H10 with x4 x11; try easy. 
            - intros.
              pinversion H1; try apply pmer_mon; subst; clear H1.
              pinversion H2; try apply pmer_mon; subst; clear H2.
              pinversion H0; try apply pmer_in_mon; subst; clear H0.
              apply nmer_in_recv. intros.
              specialize(H n). specialize(H6 n). specialize(H5 n). specialize(H2 n).
              destruct H6.
              - left. easy.
              - destruct_exists_and. rewrite H3 in H. destruct H; try easy.
                destruct_exists_and. rewrite H1 in H2. destruct H2; try easy.
                destruct_exists_and. rewrite H2 H in H5. destruct H5; try easy.
                destruct_exists_and. invert_all_some.
                right. rewrite H5 H0.
                repeat(try eexists; try split; try easy). pclearbot.
                apply H8 with x11 x8; try easy. 
          }
          - intros.
            pinversion H0; try apply pmer_mon; subst.
            pinversion H1; try apply pmer_mon; subst. clear H1 H0.
            specialize(layer_merge_inv_send H2); intros. destruct_exists_and. inversion H0. subst. clear H0. 
            apply nmer_in_send. intros.
            specialize(H1 n). specialize(H8 n). specialize(H7 n). specialize(H n).
            destruct H8.
            - destruct H7. left. easy.
              destruct_exists_and. rewrite H6 H4 in H.
              destruct H; try easy. destruct_exists_and. easy.
            - destruct_exists_and. rewrite H4 in H1. destruct H1; try easy.
              destruct_exists_and. rewrite H3 in H. destruct H; try easy.
              destruct_exists_and. rewrite H9 in H7. destruct H7; try easy.
              destruct_exists_and. rewrite H13 in H6. invert_all_some.
              right. rewrite H7 H0. 
              repeat(try eexists; try split; try easy). pclearbot.
              apply H11 with x6 x5; try easy.
          - intros.
            pinversion H0; try apply pmer_mon; subst.
            pinversion H1; try apply pmer_mon; subst. clear H1 H0.
            specialize(layer_merge_inv_recv H2); intros. destruct_exists_and. inversion H0. subst. clear H0. 
            apply nmer_in_recv. intros.
            specialize(H1 n). specialize(H8 n). specialize(H7 n). specialize(H n).
            destruct H7.
            - left. easy.
            - destruct_exists_and. rewrite H3 in H. destruct H; try easy.
              destruct_exists_and. rewrite H4 in H1. destruct H1; try easy.
              destruct_exists_and. rewrite H1 H in H8. destruct H8; try easy.
              destruct_exists_and. invert_all_some.
              right. rewrite H8 H0.
              repeat(try eexists; try split; try easy). pclearbot.
              apply H9 with x9 x13; try easy.
        }
        - intros.
          specialize(layer_merge_inv_send_b H1); intros; clear H1.
          specialize(layer_merge_inv_send_b H2); intros; clear H2.
          destruct_exists_and. subst.
          pinversion H0; try apply pmer_mon; subst.
          apply nmer_in_send.
          intros. specialize(H5 n). specialize(H3 n). specialize(H4 n). specialize(H n).
          destruct H5. 
          - destruct H. left. easy.
            destruct_exists_and. rewrite H6 in H4. destruct H4; try easy.
            destruct_exists_and. rewrite H2 in H4. easy.
          - destruct_exists_and. rewrite H2 in H4. destruct H4; try easy.
            destruct_exists_and. rewrite H5 in H3. destruct H3; try easy.
            destruct_exists_and. invert_all_some.
            right. rewrite H7 H9 in H.
            destruct H; try easy. destruct_exists_and. invert_all_some.
            rewrite H1 H. 
            repeat(try eexists; try split; try easy). pclearbot.
            apply H12 with x6 x9; try easy. 
        - intros.
          specialize(layer_merge_inv_recv_b H1); intros; clear H1.
          specialize(layer_merge_inv_recv_b H2); intros; clear H2.
          destruct_exists_and. subst.
          pinversion H0; try apply pmer_mon; subst.
          apply nmer_in_recv.
          intros. specialize(H5 n). specialize(H3 n). specialize(H4 n). specialize(H n).
          destruct H.
          - left. easy.
          right. destruct H as [Ha | [Ha | Ha]]; destruct_exists_and; subst.
          - rewrite H1 in H4. destruct H4; try easy.
            destruct_exists_and. 
            rewrite H4 in H5. destruct H5; try easy. destruct_exists_and.
            invert_all_some. rewrite H5 H.
            repeat(try eexists; try split; try easy). pclearbot.
            apply layer_merge_in_trans with x7; try easy.
            apply lmer2_to_in_l with x8. constructor. easy.
          - rewrite H2 in H3. destruct H3; try easy. destruct_exists_and.
            rewrite H3 in H5. destruct H5; try easy. destruct_exists_and.
            rewrite H5 H. destruct x1. invert_all_some.
            repeat(try eexists; try split; try easy). pclearbot.
            apply layer_merge_in_trans with x8; try easy.
            apply lmer2_to_in_r with x7. constructor. easy.
          - rewrite H1 in H4. destruct H4; try easy. destruct_exists_and.
            rewrite H2 in H3. destruct H3; try easy. destruct_exists_and.
            rewrite H4 in H5. destruct H5; try easy. destruct_exists_and.
            invert_all_some.
            rewrite H5 H.
            repeat(try eexists; try split; try easy). pclearbot. rewrite H13 in H3. invert_all_some.
            apply H7 with x13 x9; try easy.
      }
      - intros.
        specialize(layer_merge_inv_send H1); intros; clear H1.
        specialize(layer_merge_inv_send H2); intros; clear H2.
        destruct_exists_and. subst.
        specialize(layer_merge2_inv_send_c H0); intros; clear H0.
        destruct_exists_and. inversion H1. subst. clear H1.
        apply nmer_in_send.
        intro.
        specialize(H2 n). specialize(H3 n). specialize(H4 n). specialize(H n).
        destruct H2.
        - destruct H. left. easy.
          destruct_exists_and. rewrite H5 H1 in H4. destruct H4; try easy. destruct_exists_and. easy.
        - destruct_exists_and. rewrite H1 in H4. destruct H4; try easy.
          destruct_exists_and. rewrite H2 in H3. destruct H3; try easy. 
          destruct_exists_and. rewrite H4 H3 in H.
          destruct H; try easy. destruct_exists_and. invert_all_some.
          right. rewrite H H0. repeat(try eexists; try split; try easy).
          apply H13 with x8 x11; try easy.
      - intros.
        specialize(layer_merge_inv_recv H1); intros; clear H1.
        specialize(layer_merge_inv_recv H2); intros; clear H2.
        destruct_exists_and. subst.
        specialize(layer_merge2_inv_recv_c H0); intros; clear H0.
        destruct_exists_and. inversion H1. subst. clear H1.
        apply nmer_in_recv.
        intro.
        specialize(H2 n). specialize(H3 n). specialize(H4 n). specialize(H n).
        destruct H2.
        - left. easy.
        right. destruct H0 as [H0 | [H0 | H0]]; destruct_exists_and.
        - rewrite H1 in H4. destruct H4; try easy.
          destruct_exists_and. rewrite H4 in H.
          destruct H as [Ha | [Ha | [Ha | Ha]]]; destruct_exists_and; try easy.
          - invert_all_some. rewrite H. rewrite H0.
            repeat(try eexists; try split; try easy).
          - invert_all_some. rewrite H. rewrite H0.
            repeat(try eexists; try split; try easy).
            apply layer_merge_in_trans with x8; try easy.
            apply lmer2_to_in_l with x9; try easy.
        - rewrite H2 in H3. destruct H3; try easy. destruct_exists_and.
          rewrite H3 in H.
          destruct H as [Ha | [Ha | [Ha | Ha]]]; destruct_exists_and; try easy.
          - invert_all_some. rewrite H H0.
            repeat(try eexists; try split; try easy).
          - invert_all_some. rewrite H H0.
            repeat(try eexists; try split; try easy).
            apply layer_merge_in_trans with x9; try easy.
            apply lmer2_to_in_r with x8; try easy.
        - rewrite H2 in H3. destruct H3; try easy. destruct_exists_and.
          rewrite H1 in H4. destruct H4; try easy. destruct_exists_and.
          rewrite H4 H3 in H.
          destruct H as [Ha | [Ha | [Ha | Ha]]]; destruct_exists_and; try easy.
          - invert_all_some. rewrite H H0.
            repeat(try eexists; try split; try easy).
            apply H13 with x11 x8; try easy.
    Qed.
    
    
    Theorem islMerge_cont_Into_s : forall f f' T, layer_merge f T -> (forall n, (f n = None /\ f' n = None) \/ (exists t t', f n = Some t /\ f' n = Some t' /\ layer_merge_in t t')) -> exists T', layer_merge f' T' /\ layer_merge_in T T'.
    Proof.
      intros.
      destruct H as (ys,(Ha,Hb)).
      revert H0 Hb Ha. revert T f f'.
      induction ys; intros.
      - inversion Hb. subst.
        pose proof H0 as Hta. pose proof Ha as Htb.
        specialize(Ha 0). specialize(H0 0).
        rewrite (esym Ha) in H0.
        simpl in *.
        destruct H0; try easy.
        destruct H as (t1,(t2,(Hc,(Hd,He)))).
        inversion Hc. subst. clear Hc.
        exists t2. split; try easy.
        exists (slist_x t2).
        split.
        - intro.
          specialize(Htb n).
          specialize(Hta n).
          destruct n; try easy. 
          rewrite (esym Htb) in Hta. simpl in *.
          destruct Hta; try easy.  
          destruct H as (t3,(t4,Hf)). easy.
        - constructor.
      inversion Hb.
      - subst.
        specialize(IHys T (fun n => f (S n)) (fun n => f' (S n))).
        assert(exists T' : ltt,
         layer_merge (fun n : fin => f' n.+1) T' /\ layer_merge_in T T').
        {
          apply IHys; try easy.
          intro.
          specialize(Ha (S n)); try easy.
        }
        clear IHys.
        destruct H as (T',Hd).
        exists T'. split; try easy. destruct Hd.
        inversion H.
        exists (slist_xs None x). destruct H2.
        split.
        - intro.
          destruct n; try easy.
          - specialize(Ha 0).
            specialize(H0 0). rewrite (esym Ha) in H0. simpl in *.
            destruct H0; try easy.
            destruct H0 as (t1,(t2,Hc)). easy.
          - simpl.
            apply H2; try easy.
        - constructor; try easy.
      - subst. clear Hb.
        specialize(IHys T'' (fun n => f (S n)) (fun n => f' (S n))).
        assert(exists T' : ltt,
         layer_merge (fun n : fin => f' n.+1) T' /\ layer_merge_in T'' T').
        {
          apply IHys; try easy.
          intro.
          specialize(Ha (S n)); try easy.
        }
        clear IHys.
        
        destruct H as (Ta,(Hb,Hc)).
        assert(exists Tn, f' 0 = Some Tn).
        {
          specialize(Ha 0).
          specialize(H0 0). rewrite (esym Ha) in H0.
          destruct H0; try easy. destruct H as (t1,(t2,(Hf,(Hg,Hh)))). simpl in *.
          inversion Hf. subst.
          exists t2. easy.
        }
        destruct H as (Tn, H).
        assert(exists Tb, layer_merge2 Tb Tn Ta).
        {
          specialize(lmergeTwo_can_merge T' Tn T'' Ta T); intros.
          apply H1; try easy.
          specialize(Ha 0). simpl in *.
          specialize(H0 0). rewrite H in H0. rewrite (esym Ha) in H0.
          destruct H0; try easy.
          destruct H0 as (t1,(t2,(Hta,(Htb,Htc)))).
          inversion Hta. inversion Htb. easy.
        }
        destruct H1 as (Tb,H1).
        exists Tb.
        assert(layer_merge f' Tb).
        {
          unfold layer_merge. 
          inversion Hb. destruct H3.
          exists (slist_xs (Some Tn) x).
          split.
          - intro.
            destruct n; try easy.
            specialize(H3 n); try easy.
          - apply slm_xs with Ta; try easy.
        }
        split; try easy.
        clear H1 H Hc Hb.
        assert(layer_merge f T).
        {
          exists (slist_xs (Some T') ys).
          split; try easy.
          apply slm_xs with T''; try easy.
        }
        clear H4 H2 Ha. clear T' Ta Tn. rename Tb into T'. clear T'' ys.
        
        inversion H as (xs,(Ha,Hb)). clear H. 
        inversion H3 as (ys,(Hc,Hd)). clear H3.
        assert(SForall2 layer_merge_in xs ys).
        {
          clear Hd Hb. revert Ha Hc H0.
          revert f f'.
          revert ys.
          induction xs; intros.
          - destruct ys; try easy.
            - constructor.
              specialize(H0 0). specialize(Ha 0). specialize(Hc 0).
              simpl in *. rewrite (esym Ha) in H0. rewrite (esym Hc) in H0.
              destruct H0; try easy.
              destruct H as (t1,(t2,(Hd,(He,Hf)))).
              inversion Hd. subst. inversion He. subst. clear Hd He. easy.
            - specialize(onth_to_some ys); intros.
              destruct H as (n,(t,H)).
              specialize(Ha (S n)). specialize(Hc (S n)). specialize(H0 (S n)).
              rewrite (esym Ha) in H0. rewrite (esym Hc) in H0. clear Ha Hc. simpl in *.
              rewrite H in H0. destruct H0; try easy.
              destruct H0 as (t1,(t2,Ha)). easy.
          - destruct ys; try easy.
            - specialize(onth_to_some xs); intros.
              destruct H as (n,(t,H)).
              specialize(Ha (S n)). specialize(Hc (S n)). specialize(H0 (S n)).
              rewrite (esym Ha) in H0. rewrite (esym Hc) in H0. clear Ha Hc. simpl in *.
              rewrite H in H0. destruct H0; try easy.
              destruct H0 as (t1,(t2,Ha)). easy.
            - specialize(IHxs ys (fun n => f (S n)) (fun n => f' (S n))).
              assert(SForall2 layer_merge_in xs ys).
              apply IHxs; try easy.
              intro. specialize(Ha (S n)); try easy.
              intro. specialize(Hc (S n)); try easy.
              
              specialize(Ha 0). specialize(Hc 0). specialize(H0 0).
              rewrite (esym Ha) in H0. rewrite (esym Hc) in H0. clear Ha Hc.
              simpl in *.
              destruct H0.
              - destruct H0. subst.
                constructor; try easy.
              - destruct H0 as (t1,(t2,(Ha,(Hb,Hc)))).
                subst.
                constructor; try easy.
              
        }
        clear Hc Ha H0. clear f f'.
        revert Hb Hd H. revert T T' ys.
        induction xs; intros.
        - destruct ys; try easy.
          inversion H. subst.
          inversion Hb. subst. inversion Hd. subst. easy.
        - destruct ys; try easy.
          inversion H. 
          - subst. clear H.
            inversion Hb. subst. clear Hb.
            inversion Hd. subst. clear Hd.
            specialize(IHxs T'' T''0 ys H4 H7 H5).
            clear H5 H4 H7. clear xs ys.
            
            specialize(lmergeTwo_to_Into x y T'' T''0 T T'); intros.
            apply H; try easy.
            
          - subst. clear H.
            inversion Hb. subst. clear Hb.
            inversion Hd. subst. clear Hd.
            specialize(IHxs T T' ys H0 H2 H1). easy.

    Qed.
    
    Lemma lMerge_Sort_s : forall f'0 q f f'1 p f' n, layer_merge f'0 (ltt_send q f) -> layer_merge f'1 (ltt_recv p f') 
      -> (forall n : fin,
         f'0 n = None /\ f'1 n = None \/
         (exists fa fb : fin -> option (sort * ltt),
            f'0 n = Some (ltt_send q fa) /\
            f'1 n = Some (ltt_recv p fb) /\
            (forall m : fin,
             fa m = None /\ fb m = None \/
             (exists (s' : sort) (t t' : ltt), fa m = Some (s', t) /\ fb m = Some (s', t'))))) 
       -> f n = None /\ f' n = None \/ (exists (s : sort) (t t' : ltt), f n = Some (s, t) /\ f' n = Some (s, t')).
    Proof.
      intros.
      destruct H as (zs,(Ha,Hb)).
      destruct H0 as (ys,(Hc,Hd)).
      revert H1 Hd Hc Hb Ha. revert f'0 q f f'1 p f' n ys.
      induction zs; intros.
      - inversion Hb. subst. clear Hb.
        inversion Hd.
        - subst. clear Hd.
          specialize(Hc 0). specialize(Ha 0). specialize(H1 0).
          simpl in *. rewrite (esym Ha) in H1. rewrite (esym Hc) in H1.
          destruct H1; try easy.
          destruct H as (fa,(fb,(Hd,(He,Hf)))).
          inversion Hd. subst. clear Hd.
          inversion He. subst. clear He.
          specialize(Hf n).
          easy.
        - subst. clear Hd.
          specialize(onth_to_some xs); intros.
          destruct H0 as (n1,(ta,Ht)).
          specialize(Hc (S n1)). specialize(Ha (S n1)). simpl in *. rewrite Ht in Hc.
          specialize(H1 (S n1)). rewrite (esym Ha) in H1. rewrite (esym Hc) in H1.
          destruct H1; try easy. destruct H0 as (fa,(fb,Hs)). easy.
        - subst. clear Hd.
          specialize(onth_to_some xs); intros.
          destruct H2 as (n1,(ta,Ht)).
          specialize(Hc (S n1)). specialize(Ha (S n1)). simpl in *. rewrite Ht in Hc.
          specialize(H1 (S n1)). rewrite (esym Ha) in H1. rewrite (esym Hc) in H1.
          destruct H1; try easy. destruct H1 as (fa,(fb,Hs)). easy.
      - inversion Hb.
        - subst. clear Hb.
          inversion Hd.
          - subst.
            specialize(onth_to_some zs); intros.
            destruct H as (n1,(ta,Ht)).
            specialize(Hc (S n1)). specialize(Ha (S n1)). simpl in *. rewrite Ht in Ha.
            specialize(H1 (S n1)). rewrite (esym Ha) in H1. rewrite (esym Hc) in H1.
            destruct H1; try easy. destruct H as (fa,(fb,Hs)). easy.
          - subst. clear Hd.
            specialize(IHzs (fun n => f'0 (S n)) q f (fun n => f'1 (S n)) p f' n xs).
            apply IHzs; try easy.
            - intro. specialize(Hc (S n0)). easy.
            - intro. specialize(Ha (S n0)). easy.
          - subst. 
            specialize(Hc 0). specialize(Ha 0).
            simpl in *.
            specialize(H1 0). rewrite (esym Ha) in H1. rewrite (esym Hc) in H1.
            destruct H1; try easy. destruct H1 as (fa,(fb,Ht)). easy.
        - subst. clear Hb.
          inversion Hd. 
          - subst.
            specialize(onth_to_some zs); intros.
            destruct H as (n1,(ta,Ht)).
            specialize(Hc (S n1)). specialize(Ha (S n1)). simpl in *. rewrite Ht in Ha.
            specialize(H1 (S n1)). rewrite (esym Ha) in H1. rewrite (esym Hc) in H1.
            destruct H1; try easy. destruct H as (fa,(fb,Hs)). easy.
          - subst.
            specialize(Hc 0). specialize(Ha 0).
            simpl in *.
            specialize(H1 0). rewrite (esym Ha) in H1. rewrite (esym Hc) in H1.
            destruct H1; try easy. destruct H0 as (fa,(fb,Ht)). easy.
          - subst.
            specialize(layer_merge2_inv_recv H); intros.
            specialize(layer_merge2_inv_send H2); intros. destruct_exists_and. subst. clear H H2. rename x1 into f2. rename x0 into f3. rename x2 into f4.
            specialize(IHzs (fun n => f'0 (S n)) q f3 (fun n => f'1 (S n)) p f4 n xs).
            assert(f3 n = None /\ f4 n = None \/
              (exists (s : sort) (t t' : ltt), f3 n = Some (s, t) /\ f4 n = Some (s, t'))).
            {
              apply IHzs; try easy.
              - intro. specialize(Hc (S n0)); try easy.
              - intro. specialize(Ha (S n0)); try easy.
            }
            specialize(Hc 0). specialize(Ha 0). specialize(H1 0).
            simpl in *. rewrite (esym Ha) in H1. rewrite (esym Hc) in H1.
            destruct H1; try easy. 
            destruct H1 as (fa,(fb,(Hta,(Htb,Htc)))). inversion Hta. subst. inversion Htb. subst.
            clear IHzs Hc Hd Ha H4 H0 Hta Htb.
            specialize(H7 n). specialize(H9 n). specialize(Htc n).
            destruct H7.
            - destruct H9. left. easy.
              destruct H0 as (Ha,(Hb,Hc)). rewrite Hb in Htc. rewrite Hc in H.
              assert(fb n = None).
              {
                destruct Htc; try easy.
                destruct H0 as (s1,(t1,(t2,Ht))). easy.
              }
              assert(f4 n = None).
              {
                destruct H; try easy.
                destruct H as (s1,(t1,(t2,Ht))). easy.
              }
              rewrite H0 in H1. rewrite H2 in H1.
              
              - destruct H1. destruct H1; try easy.
              - destruct H1. destruct H1; try easy.
              - destruct H1 as (s1,(t1,(t2,(t3,Ht)))); try easy.
            - destruct H0 as (s1,(t1,(t2,(t3,(Ha,(Hb,(Hc,Hd))))))).
              rewrite Ha. rewrite Hb in Htc. rewrite Hc in H.
              right.
              destruct Htc; try easy. 
              destruct H0 as (s2,(t4,(t5,(He,Hf)))). inversion He. subst.
              destruct H; try easy.
              destruct H as (s3,(t6,(t7,(Hg,Hh)))). inversion Hg. subst.
              rewrite Hf in H9. rewrite Hh in H9.
              - destruct H9; try easy.
              - destruct H. destruct H; try easy.
              - destruct H. destruct H; try easy.
              - destruct H as (s4,(t8,(t9,(t10,(Hi,(Hj,(Hk,Hl))))))).
                inversion Hj. subst. inversion Hk. subst.
                rewrite Hi. exists s4. exists t1. exists t8. easy.
    Qed.
       
    Instance coind_layer_merge : good_merge := {
    
      isMerge := layer_merge;
      
      merge_into_recv := lmerge_into_recv_s;
      merge_label_send := lmerge_label_send_s;
      merge_into_send := lmerge_into_send_s;
      merge_label_send_b := lmerge_label_send_b_s;
    
      MergeInto := layer_merge_in;
      
      isMerge_to_Into := islMerge_to_Into_s;
      
      MergeInto_end := MergeInto_end_n;
      
      MergeInto_send := MergeInto_send_n;
      MergeInto_recv := MergeInto_recv_n;
      isMerge_cont_Into := islMerge_cont_Into_s;
      
      MergeInto_to_subtypeC := MergeInto_to_subtypeC_n;
      
      Merge_Sort := lMerge_Sort_s
   
    }.
    
    (* coinductive layer merge is a bisimular relation *)
    Lemma layer_merge2_partial : forall T1 T2 T T', layer_merge2 T1 T T' -> layer_merge2 T2 T T' -> ltt_bisimC T1 T2.
    Proof.
      pcofix CIH; intros. destruct T1.
      - inversion H0. subst.
        pinversion H; try apply pmer_mon. subst.
        inversion H1. subst. 
        pinversion H2; try apply pmer_mon. subst. 
        pfold.
        constructor.
      - specialize(layer_merge2_inv_recv H0); intros.
        destruct_exists_and. subst.
        specialize(layer_merge2_inv_recv_c H1); intros.
        destruct_exists_and. subst. clear H0 H1. inversion H2; subst; clear H2.
        pfold. constructor.
        intros.
        specialize(H3 n). specialize(H4 n). 
        destruct H3.
        - destruct H as (Ha,(Hb,Hc)). rewrite Hb in H4.
          destruct H4 as [H4 | H4]; destruct_exists_and; try easy.
          left. easy.
          rewrite Hc in H4.
          destruct H4 as [He | [He | He]]; destruct_exists_and; subst; try easy.
        destruct H as [Hd | [Hd | Hd]]; destruct_exists_and; subst.
        - rewrite H1 H0 in H4.
          destruct H4 as [He | [He | [He | He]]]; destruct_exists_and; subst; try easy. invert_all_some. rewrite H H2.
          right. destruct x3. repeat(try eexists; try split; try easy).
          left. apply ltt_bisimC_refl.
        - rewrite H1 H0 in H4.
          destruct H4 as [He | [He | [He | He]]]; destruct_exists_and; subst; try easy. invert_all_some. rewrite H H2.
          right. destruct x3. repeat(try eexists; try split; try easy).
          left. apply ltt_bisimC_refl.
        - rewrite H1 H0 in H4.
          destruct H4 as [He | [He | [He | He]]]; destruct_exists_and; subst; try easy. invert_all_some. rewrite H H3.
          right. repeat(try eexists; try split; try easy).
          right. apply CIH with x8 x9; try easy.
      - specialize(layer_merge2_inv_send H0); intros.
        destruct_exists_and. subst.
        specialize(layer_merge2_inv_send_c H1); intros.
        destruct_exists_and. subst. clear H0 H1. inversion H2; subst; clear H2.
        pfold. constructor.
        intros.
        specialize(H3 n). specialize(H4 n). 
        destruct H3.
        - destruct H4. left. easy.
          destruct_exists_and. rewrite H2 in H5. easy.
        - destruct_exists_and. rewrite H0 H1 in H4.
          destruct H4; try easy. destruct_exists_and.
          invert_all_some. right. rewrite H H3.
          repeat(try eexists; try split; try easy).
          right. apply CIH with x8 x9; try easy.
    Qed.

End coind_nmer.

  
  
End good_merge.









