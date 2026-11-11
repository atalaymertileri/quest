Require Import String PeanoNat Arith Relations ZArith Datatypes Setoid Morphisms Decidable Program Datatypes Lia.
Require Import Automation ListUtils FMap Primitives Process.
Import ListNotations. 
Open Scope list_scope.
From Paco Require Import paco.
Require Import header. 

Section cguardP.
  
  (* --------------------------------------------------------------- *)
  (* Closedness/guardedness analyses                                  *)
  (*                                                                   *)
  (* `process_closedP`/`guardP` are "exact" formulations;                  *)
  (* `process_closedPS`/`guardPS` are closure-friendly variants with `*_sub`.  *)
  (* --------------------------------------------------------------- *)

  (* Boolean masks track which recursion variables are available. *)
  Inductive process_closedP : list bool -> process -> Prop :=
    | cp_var   : forall n lz, process_closedP (boollis n) (p_var n lz)
    | cp_end : forall lz, process_closedP nil (p_end lz)
    | cp_send  : forall xs pt l e P, process_closedP xs P -> process_closedP xs (p_send pt l e P)
    | cp_recv  : forall zs p ys, SForall2 process_closedP zs ys -> process_closedP (bmergelis zs) (p_recv p ys)
    | cp_ite   : forall xs ys e P Q, process_closedP xs P -> process_closedP ys Q -> process_closedP (bmerge xs ys) (p_ite e P Q)
    | cp_rec0  : forall P, process_closedP nil P -> process_closedP nil (p_rec P)
    | cp_rec1  : forall P x xs, process_closedP (x :: xs) P -> process_closedP xs (p_rec P)
    | cp_newq : forall xs P, process_closedP xs P -> process_closedP xs (p_newq P)
    | cp_unitary : forall xs n U lz P, process_closedP xs P -> process_closedP xs (p_unitary n U lz P)
    | cp_measure : forall xs z P, process_closedP xs P -> process_closedP xs (p_measure z P).
    
  Inductive process_closedPS : list bool -> process -> Prop :=
    | cps_var   : forall n lz, process_closedPS (boollis n) (p_var n lz)
    | cps_end : forall lz, process_closedPS nil (p_end lz)
    | cps_send  : forall xs pt l e P, process_closedPS xs P -> process_closedPS xs (p_send pt l e P)
    | cps_recv  : forall zs p ys, SForall (process_closedPS zs) ys -> process_closedPS zs (p_recv p ys)
    | cps_ite   : forall xs e P Q, process_closedPS xs P -> process_closedPS xs Q -> process_closedPS xs (p_ite e P Q)
    | cps_rec0  : forall P, process_closedPS nil P -> process_closedPS nil (p_rec P)
    | cps_rec1  : forall P x xs, process_closedPS (x :: xs) P -> process_closedPS xs (p_rec P)
    | cps_sub   : forall P xs ys, bmerge xs ys = ys -> process_closedPS xs P -> process_closedPS ys P
    | cps_newq : forall xs P, process_closedPS xs P -> process_closedPS xs (p_newq P)
    | cps_unitary : forall xs n U lz P, process_closedPS xs P -> process_closedPS xs (p_unitary n U lz P)
    | cps_measure : forall xs z P, process_closedPS xs P -> process_closedPS xs (p_measure z P).
  
  Lemma process_closedPS_inv_var : forall xs P n lz, process_closedPS xs P -> (P = p_var n lz) -> bmerge (boollis n) xs = xs.
  Proof.
    intros. revert H0. revert n lz.
    induction H; intros; try easy.
    - inversion H0. subst.
      clear H0.
      induction n0; try easy.
      simpl.
      rewrite IHn0. easy.
    - subst.
      specialize(IHprocess_closedPS n lz (eq_refl (p_var n lz))).
      clear H0.
      revert IHprocess_closedPS H.
      revert xs ys.
      induction n; intros; try easy.
      - destruct xs; try easy.
        destruct ys; try easy.
        inversion IHprocess_closedPS. subst. inversion H. subst. simpl.
        assert(exists zs, bmerge xs ys = zs). exists (bmerge xs ys). easy.
        destruct H0 as (zs, H0). rewrite H0. destruct zs; try easy.
      - destruct xs; try easy.  
        destruct ys; try easy.
        inversion IHprocess_closedPS. subst. inversion H. subst. simpl.
        specialize(IHn xs ys H1 H3).
        rewrite H3.
        rewrite IHn.
        easy.
  Qed.
        
  Lemma process_closedPS_inv_send : forall xs P pt l e P', process_closedPS xs P -> (P = p_send pt l e P') -> process_closedPS xs P'.
  Proof.
    intros.
    revert H0. revert pt l e P'.
    induction H; intros; try easy.
    - inversion H0. subst. easy.
    - subst.
      specialize(IHprocess_closedPS pt l e P').
      apply cps_sub with (xs := xs); try easy.
      apply IHprocess_closedPS; try easy.
  Qed.
  
  Lemma process_closedPS_inv_recv : forall xs P pt ys, process_closedPS xs P -> (P = p_recv pt ys) -> SForall (process_closedPS xs) ys.
  Proof.
    intros.
    revert H0. revert ys pt.
    induction H; intros; try easy.
    - inversion H0. subst. easy.
    - subst.
      specialize(IHprocess_closedPS ys0 pt).
      assert(SForall (process_closedPS xs) ys0). apply IHprocess_closedPS; try easy.
      revert H1.
      apply SForall_mono; intros.
      apply cps_sub with (xs := xs); try easy.
  Qed.
  
  Lemma process_closedPS_inv_ite : forall xs P e P1 P2, process_closedPS xs P -> (P = p_ite e P1 P2) -> process_closedPS xs P1 /\ process_closedPS xs P2.
  Proof.
    intros. revert H0. revert P1 P2 e.
    induction H; intros; try easy.
    - inversion H1. subst. easy.
    - subst.
      specialize(IHprocess_closedPS P1 P2 e).
      assert(process_closedPS xs P1 /\ process_closedPS xs P2). apply IHprocess_closedPS; try easy.
      destruct H1 as (Ha,Hb).
      split.
      - apply cps_sub with (xs := xs); try easy.
      - apply cps_sub with (xs := xs); try easy.
  Qed.

  Lemma process_closedPS_inv_newq : forall xs P, process_closedPS xs (p_newq P) ->  process_closedPS xs P.
  Proof.
    intros.
    dependent induction H; intros; try easy.
    subst.
      specialize(IHprocess_closedPS P eq_refl).
      apply cps_sub with (xs := xs); try easy.
  Qed.

  Lemma process_closedPS_inv_unitary : forall xs P n U lz, process_closedPS xs (p_unitary n U lz P) ->  process_closedPS xs P.
  Proof.
    intros.
    dependent induction H; intros; try easy.
    subst.
      specialize(IHprocess_closedPS P n U lz eq_refl).
      apply cps_sub with (xs := xs); try easy.
  Qed.

  Lemma process_closedPS_inv_measure : forall xs P z, process_closedPS xs (p_measure z P) ->  process_closedPS xs P.
  Proof.
    intros.
    dependent induction H; intros; try easy.
    subst.
      specialize(IHprocess_closedPS P z eq_refl).
      apply cps_sub with (xs := xs); try easy.
  Qed.
  
  Lemma process_closedPS_inv_rec : forall xs P P', process_closedPS xs P -> (P = p_rec P') -> exists x, process_closedPS (x :: xs) P'.
  Proof.
    intros. revert H0. revert P'.
    induction H; intros; try easy.
    - inversion H0. subst.
      exists true.
      apply cps_sub with (xs := nil); try easy.
    - inversion H0. subst.
      exists x; try easy.
    - subst.
      specialize(IHprocess_closedPS P').
      assert(exists x : bool, process_closedPS (x :: xs) P').
      apply IHprocess_closedPS; try easy.
      destruct H1 as (x, H1).
      exists x.
      apply cps_sub with (xs := x :: xs); try easy.
      simpl. rewrite H. 
      destruct x; try easy.
  Qed.

  Ltac invert_process_closedPS :=
    match goal with
    | [H: process_closedPS _ (p_newq _) |- _] =>
    apply process_closedPS_inv_newq in H
    | [H: process_closedPS _ (p_unitary _ _ _ _ ) |- _] =>
    apply process_closedPS_inv_unitary in H
    | [H: process_closedPS _ (p_measure _ _) |- _] =>
    apply process_closedPS_inv_measure in H
    end.
   
  Lemma process_closedPS_free : forall Q xl xr l m n, process_closedPS (xl ++ xr) Q -> process_closedPS (xl ++ (false_list m) ++ xr) (incr_free (length xl) l m n Q).
  Proof.
    induction Q using process_deep_ind; intros; try easy.
    - simpl.
      specialize(process_closedPS_inv_var (xl ++ xr) (p_var n lz) n lz); intros.
      assert(bmerge (boollis n) (xl ++ xr) = xl ++ xr). apply H0; try easy. clear H H0.
      case_eq (Nat.leb (length xl) n); intros.
      - revert H H1.
        revert n xr m.
        induction xl; intros; try easy.
        - simpl in *.
          apply cps_sub with (boollis (n + m)); try easy.
          - specialize(Nat.add_comm n m); intros. rewrite H0. clear H0.
            clear H.
            revert H1. revert xr n.
            induction m; intros; try easy.
            - simpl. 
            specialize(IHm xr n H1). rewrite IHm. easy.
          - constructor. 
        - destruct n; try easy.
          inversion H1.
          specialize(IHxl n xr m H H2).
          apply cps_sub with (boollis ((S n) + m)); try easy.
          - simpl.
            specialize(process_closedPS_inv_var (xl ++ false_list m ++ xr)
              (p_var (n + m) (map (incr_free_expression l n0) lz)) (n + m)
              (map (incr_free_expression l n0) lz)); intros.
            assert(bmerge (boollis (n + m)) (xl ++ false_list m ++ xr) =
     xl ++ false_list m ++ xr).
            apply H0; try easy.
            rewrite H3. easy.
          - constructor.
      - revert H1 H.
        revert n xr m.
        induction xl; intros; try easy.
        destruct n; try easy.
        - inversion H1. subst.
          apply cps_sub with (boollis 0); try easy.
          - simpl. destruct xl; try easy.
            destruct m; try easy. 
          - constructor.
        - inversion H1. subst.
          specialize(IHxl n xr m H2 H).
          specialize(process_closedPS_inv_var (xl ++ false_list m ++ xr)
            (p_var n (map (incr_free_expression l n0) lz)) n
            (map (incr_free_expression l n0) lz)); intros.
          assert(bmerge (boollis n) (xl ++ false_list m ++ xr) = xl ++ false_list m ++ xr).
          apply H0; try easy. clear H0 IHxl.
          apply cps_sub with (boollis (S n)); try easy.
          - simpl. rewrite H3. easy.
          - constructor.
    - apply cps_sub with nil; try easy.
      - destruct xl; try easy. destruct m; try easy. destruct xr; try easy.
      - constructor.
    - simpl. constructor.
      apply IHQ; try easy.
      specialize(process_closedPS_inv_send (xl ++ xr) (p_send pt lb ex Q) pt lb ex Q); intros.
      apply H0; try easy.
    - simpl. constructor.
      specialize(process_closedPS_inv_recv (xl ++ xr) (p_recv pt llp) pt llp); intros.
      assert(SForall (process_closedPS (xl ++ xr)) llp). apply H1; try easy. clear H1 H0.
      revert H2 H. clear pt. revert xl xr m n.
      induction llp; intros; try easy.
      - inversion H. subst. clear H.
        inversion H2. subst. clear H2.
        constructor. apply H1; try easy.
      inversion H.
      - subst. clear H.
        inversion H2. subst. clear H2.
        specialize(IHllp xl xr m n H5 H4). 
        constructor; try easy.
        apply H3; try easy.
      - subst. clear H.
        inversion H2. subst. clear H2.
        specialize(IHllp xl xr m n H0 H1). 
        constructor; try easy.
    - simpl. 
      specialize(process_closedPS_inv_ite (xl ++ xr) (p_ite e Q1 Q2) e Q1 Q2); intros.
      assert(process_closedPS (xl ++ xr) Q1 /\ process_closedPS (xl ++ xr) Q2). apply H0; try easy.
      clear H0 H.
      constructor.
      - apply IHQ1; try easy.
      - apply IHQ2; try easy.
    - simpl.
      specialize(process_closedPS_inv_rec (xl ++ xr) (p_rec Q) Q); intros.
      assert(exists x : bool, process_closedPS (x :: xl ++ xr) Q).
      apply H0; try easy. destruct H1 as (x, Ha). clear H H0.
      apply cps_rec1 with (x := x); try easy.
      specialize(IHQ (x :: xl) xr l m n). apply IHQ; try easy.
    - simpl. 
      specialize(process_closedPS_inv_newq (xl ++ xr) Q); intros.
      assert(process_closedPS (xl ++ xr) Q). apply H0; try easy.
      clear H0 H.
      constructor.
      apply IHQ; try easy.
    - simpl. 
      specialize(process_closedPS_inv_unitary (xl ++ xr) Q n U lz); intros.
      assert(process_closedPS (xl ++ xr) Q). apply H0; try easy.
      clear H0 H.
      constructor.
      apply IHQ; try easy.
    - simpl. 
      specialize(process_closedPS_inv_measure (xl ++ xr) Q z); intros.
      assert(process_closedPS (xl ++ xr) Q). apply H0; try easy.
      clear H0 H.
      constructor.
      apply IHQ; try easy.
  Qed.
  
  Lemma process_closedPS_remove_false : forall Q xs n, process_closedPS (xs ++ false_list n) Q -> process_closedPS xs Q.
  Proof.
    induction Q using process_deep_ind; intros; try easy.
    - specialize(process_closedPS_inv_var (xs ++ false_list n0) (p_var n lz) n lz); intros.
      assert(bmerge (boollis n) (xs ++ false_list n0) = xs ++ false_list n0).
      apply H0; try easy. clear H0 H.
      apply cps_sub with (xs := (boollis n)); try easy.
      - revert H1.
        revert xs.
        induction n; intros; try easy.
        simpl in H1.
        destruct xs; try easy.
        - destruct n0; try easy.
        - simpl in H1.
          inversion H1. subst.
          simpl. destruct xs; try easy.
      - destruct xs; try easy.
        - clear IHn.
          assert(exists m, S n = m). exists (S n). easy.
          destruct H as (m, H). rewrite H in H1. rewrite H. clear H. clear n.
          assert False.
          revert H1. rename m into n. revert n0.
          induction n; intros; try easy.
          - destruct n0; try easy.
          - destruct n0; try easy.
            inversion H1. 
            apply IHn with (n0 := n0); try easy.
          easy.
        - inversion H1. 
          simpl. specialize(IHn xs H0).
          rewrite IHn. easy.
        constructor.
    - apply cps_sub with nil; try easy.
      - destruct xs; try easy.
      - constructor.
    - constructor.
      apply IHQ with (n := n); try easy.
      specialize(process_closedPS_inv_send (xs ++ false_list n) (p_send pt lb ex Q) pt lb ex Q); intros.
      apply H0; try easy.
    - constructor.
      specialize(process_closedPS_inv_recv (xs ++ false_list n) (p_recv pt llp) pt llp); intros.
      assert(SForall (process_closedPS (xs ++ false_list n)) llp).
      apply H1; try easy. clear H1 H0.
      revert H H2.
      apply SForall_mono2; intros; try easy.
      apply H with (n := n); try easy.
    - specialize(process_closedPS_inv_ite (xs ++ false_list n) (p_ite e Q1 Q2) e Q1 Q2); intros.
      assert(process_closedPS (xs ++ false_list n) Q1 /\ process_closedPS (xs ++ false_list n) Q2).
      apply H0; try easy.
      constructor.
      - apply IHQ1 with (n := n); try easy.
      - apply IHQ2 with (n := n); try easy.
    - specialize(process_closedPS_inv_rec (xs ++ false_list n) (p_rec Q) Q); intros.
      assert(exists x : bool, process_closedPS (x :: xs ++ false_list n) Q).
      apply H0; try easy.
      destruct H1 as (x, Ha).
      apply cps_rec1 with (x := x); try easy.
      apply IHQ with (n := n); try easy.
    - simpl. 
      specialize(process_closedPS_inv_newq (xs ++ false_list n) Q); intros.
      assert(process_closedPS (xs ++ false_list n) Q). apply H0; try easy.
      clear H0 H.
      constructor.
      eapply IHQ; eauto.
    - simpl. 
      specialize(process_closedPS_inv_unitary (xs ++ false_list n0) Q n U lz); intros.
      assert(process_closedPS (xs ++ false_list n0) Q). apply H0; try easy.
      clear H0 H.
      constructor.
      eapply IHQ; eauto.
    - simpl. 
      specialize(process_closedPS_inv_measure (xs ++ false_list n) Q z); intros.
      assert(process_closedPS (xs ++ false_list n) Q). apply H0; try easy.
      clear H0 H.
      constructor.
      eapply IHQ; eauto.
  Qed.

  Lemma process_closedPS_freeS : forall Q m n, process_closedPS nil Q -> process_closedPS nil (incr_free 0 0 m n Q).
  Proof.
    intros.
    specialize(process_closedPS_free Q nil nil 0 m n H); intros.
    simpl in *.
    specialize(process_closedPS_remove_false (incr_free 0 0 m n Q) nil m); intros.
    apply H1; try easy.
    clear H1 H.
    simpl in *.
    specialize(app_nil_r (false_list m)); intros.
    rewrite <- H. easy.
  Qed.
  
  Lemma process_closedPS_subst : forall P Q xl xe xr m n, process_closedPS (xl ++ [xe] ++ xr) P -> process_closedPS nil Q -> process_closedPS (xl ++ xr) (substitutionP (length xl) m n Q P).
  Proof.
    induction P using process_deep_ind; intros; try easy.
    - specialize(process_closedPS_inv_var (xl ++ [xe] ++ xr) (p_var n lz) n lz); intros.
      assert(bmerge (boollis n) (xl ++ [xe] ++ xr) = xl ++ [xe] ++ xr).
      apply H1; try easy. clear H H1.
      simpl.
      - destruct_fresh (n <? length xl); intros.
        - clear H0. clear Q m n0.
          revert HD H2. revert xl xe xr. 
          induction n; intros; try easy.
          - destruct xl; try easy. 
            inversion H2. subst.
            apply cps_sub with (boollis 0); try easy.
            simpl. destruct xl; try easy. destruct xr; try easy.
            constructor.
          - destruct xl; try easy.
            inversion H2. 
            specialize(IHn xl xe xr HD H0).
            specialize(process_closedPS_inv_var (xl ++ xr) (p_var n lz) n lz); intros.
            assert(bmerge (boollis n) (xl ++ xr) = xl ++ xr). apply H; try easy.
            clear H H0 H2 HD IHn.
            apply cps_sub with (boollis (S n)); try easy.
            - simpl. rewrite H1. easy.
            - constructor.

        case_eq (n =? length xl); intros.
        - apply cps_sub with nil; try easy.
          - destruct xl; destruct xr; try easy.
          - clear HD H.
            apply process_closedPS_freeS; try easy.

        - clear H0.
          assert (exists m, n = S m).
          destruct n; simpl in *. 
          destruct xl; try easy.
          eexists; eauto.
          cleanup.
          simpl.
          rewrite Nat.sub_0_r.
          revert HD H H2. revert m0 xe xr. clear Q.
          induction xl; intros; try easy.
          - inversion H2. simpl in *.
            apply cps_sub with (xs := (boollis m0)); try easy.
            rewrite H1; eauto.
            econstructor.
      
          - simpl in *. inversion H2.
            destruct m0.
            simpl in *.
            apply cps_sub with (xs := nil); try easy.
            destruct xl; simpl in *; try easy.
            specialize(IHxl m0 xe xr HD H H1).
            clear HD H2 H H1.
            specialize(process_closedPS_inv_var (xl ++ xr) (p_var m0 lz) m0 lz); intros.
            assert(bmerge (boollis m0) (xl ++ xr) = xl ++ xr).
            apply H; try easy. clear H.
            apply cps_sub with (boollis (S m0)); try easy.
            - simpl. rewrite H0. easy.
            - constructor.
        
    - simpl.
      apply cps_sub with (xs := nil); try easy.
      destruct xl; try easy. destruct xr; try easy.
      constructor.
    - simpl. constructor.
      assert(process_closedPS (xl ++ [xe] ++ xr) P).
      {
        specialize(process_closedPS_inv_send (xl ++ [xe] ++ xr) (p_send pt lb ex P) pt lb ex P); intros.
        apply H1; try easy.
      }
      specialize(IHP Q xl xe xr m n H1 H0). easy.
    - simpl.
      constructor.
      specialize(process_closedPS_inv_recv (xl ++ [xe] ++ xr) (p_recv pt llp) pt llp); intros.
      assert(SForall (process_closedPS (xl ++ [xe] ++ xr)) llp).
      apply H2; try easy. clear H2 H0.
      revert H3 H.
      induction llp; intros; try easy.
      - inversion H. subst. clear H.
        inversion H3. subst. clear H3.
        constructor.
        apply H2 with (xe := xe); try easy.
      inversion H.
      - subst. clear H.
        inversion H3. subst. clear H3.
        specialize(IHllp H6 H5). clear H6 H5.
        constructor; try easy.
        apply H4 with (xe := xe); try easy.
      - subst. clear H.
        inversion H3. subst. clear H3.
        specialize(IHllp H0 H2). clear H0 H2.
        constructor; try easy.
    - simpl.
      specialize(process_closedPS_inv_ite (xl ++ [xe] ++ xr) (p_ite e P1 P2) e P1 P2); intros.
      assert(process_closedPS (xl ++ [xe] ++ xr) P1 /\ process_closedPS (xl ++ [xe] ++ xr) P2).
      apply H1; try easy. clear H1 H.
      destruct H2 as (Ha, Hb).
      constructor.
      - apply IHP1 with (xe := xe); try easy.
      - apply IHP2 with (xe := xe); try easy.
    - simpl.
      specialize(process_closedPS_inv_rec (xl ++ [xe] ++ xr) (p_rec P) P); intros.
      assert(exists x : bool, process_closedPS (x :: xl ++ [xe] ++ xr) P).
      apply H1; try easy. clear H1 H.
      destruct H2 as (x, Ha).
      apply cps_rec1 with (x := x); try easy.
      specialize(IHP Q (x :: xl) xe xr). apply IHP; try easy.
    - simpl. 
      specialize(process_closedPS_inv_newq (xl ++ [xe] ++ xr) P); intros.
      assert(process_closedPS (xl ++ [xe] ++ xr) P). apply H1; try easy. clear H1 H.
      constructor.
      eapply IHP with (xe := xe); try easy.
    - simpl. 
      specialize(process_closedPS_inv_unitary (xl ++ [xe] ++ xr) P n U lz); intros.
      assert(process_closedPS (xl ++ [xe] ++ xr) P). apply H1; try easy. clear H1 H.
      constructor.
      eapply IHP with (xe := xe); try easy.
    - simpl. 
      specialize(process_closedPS_inv_measure (xl ++ [xe] ++ xr) P z); intros.
      assert(process_closedPS (xl ++ [xe] ++ xr) P). apply H1; try easy. clear H1 H.
      constructor.
      eapply IHP with (xe := xe); try easy.
  Qed.
  
  Lemma process_closedP_to_PS : forall xs P, process_closedP xs P -> process_closedPS xs P.
  Proof.
    intros xs P. revert xs.
    induction P using process_deep_ind; intros; try easy.
    - inversion H.
      constructor.
    - inversion H.
      constructor.
    - inversion H.
      subst.
      constructor. 
      apply IHP; try easy.
    - inversion H0. subst.
      clear H0.
      revert H3 H.
      revert pt zs.
      induction llp; intros; try easy.
      - inversion H3. subst. clear H3.
        inversion H. subst. clear H.
        constructor. constructor; try easy.
        apply H1; try easy.
      inversion H3.
      - subst. clear H3.
        inversion H. subst. clear H.
        specialize(IHllp pt xs H5 H3). clear H3.
        specialize(H2 x H4). clear H4.
        constructor.
        constructor.
        - apply cps_sub with x; try easy. 
          simpl.
          specialize(bmerge_again_l x (bmergelis xs)); intros. easy.
        - clear H2.
          specialize(process_closedPS_inv_recv (bmergelis xs) (p_recv pt llp) pt llp); intros.
          assert(SForall (process_closedPS (bmergelis xs)) llp). apply H; try easy. clear H H5 IHllp.
          clear pt y.
          revert H0.
          apply SForall_mono; intros; try easy.
          apply cps_sub with (bmergelis xs); try easy.
          simpl.
          apply bmerge_again_r; try easy.
      - subst. clear H3.
        inversion H. subst. clear H.
        specialize(IHllp pt xs H2 H1).
        specialize(process_closedPS_inv_recv (bmergelis xs) (p_recv pt llp) pt llp); intros.
        assert(SForall (process_closedPS (bmergelis xs)) llp). apply H; try easy.
        clear H H1 H2.
        constructor.
        constructor; try easy.
    - inversion H. subst.
      constructor.
      - apply cps_sub with xs0; try easy.
        apply bmerge_again_l; try easy.
        apply IHP1; try easy.
      - apply cps_sub with ys; try easy.
        apply bmerge_again_r; try easy.
        apply IHP2; try easy.
    - inversion H. subst.
      - apply cps_rec0.
        apply IHP; try easy.
      - subst.
        apply cps_rec1 with (x := x).
        apply IHP; try easy.
    - inversion H. subst.
      constructor; eauto.
    - inversion H. subst.
      constructor; eauto.
    - inversion H. subst.
      constructor; eauto.
  Qed. 
        
  Lemma process_closedPS_to_P : forall xs P, process_closedPS xs P -> exists ys, bmerge ys xs = xs /\ process_closedP ys P.
  Proof.
    intros xs P. revert xs.
    induction P using process_deep_ind; intros; try easy.
    - specialize(process_closedPS_inv_var xs (p_var n lz) n lz); intros.
      assert(bmerge (boollis n) xs = xs). apply H0; try easy.
      clear H0.
      exists (boollis n).
      split. easy. constructor.
    - exists nil.
      split. destruct xs; try easy.
      constructor.
    - specialize(process_closedPS_inv_send xs (p_send pt lb ex P) pt lb ex P); intros.
      assert(process_closedPS xs P). apply H0; try easy. clear H0 H.
      specialize(IHP xs H1).
      destruct IHP as (ys,(Ha,Hb)).
      exists ys.
      - split. easy.
      - constructor; try easy.
    - specialize(process_closedPS_inv_recv xs (p_recv pt llp) pt llp); intros.
      assert(SForall (process_closedPS xs) llp). apply H1; try easy. clear H1 H0.
      revert H H2. 
      revert xs pt.
      induction llp; intros.
      - inversion H2. subst. clear H2.
        inversion H. subst. clear H.
        specialize(H2 xs H1).
        destruct H2 as (ys,(Ha,Hb)).
        exists ys.
        split.
        - easy.
        - replace ys with (bmergelis (slist_x ys)); try easy.
          constructor. constructor; try easy.
      inversion H2.
      - subst. clear H2.
        inversion H. subst. clear H.
        specialize(IHllp xs pt H5 H4). clear H5 H4.
        destruct IHllp as (ys,(Ha,Hb)).
        specialize(H2 xs H3).
        destruct H2 as (zs,(Hc,Hd)).
        exists (bmerge ys zs).
        split.
        - specialize(bmerge_again ys zs xs); intros.
          apply H; try easy.
          inversion Hb. subst.
          replace (bmerge (bmergelis zs0) zs) with (bmergelis (slist_xs (Some zs) zs0)); try easy.
          - constructor; try easy.
            constructor; try easy.
          - simpl.
            specialize(bmerge_comm zs (bmergelis zs0)).
            easy.
      - subst. clear H2.
        inversion H. subst. clear H.
        specialize(IHllp xs pt H2 H1). clear H2 H1.
        destruct IHllp as (ys,(Ha,Hb)).
        exists ys.
        split. easy.
        inversion Hb. subst.
        replace (bmergelis zs) with (bmergelis (slist_xs None zs)); try easy.
        constructor. constructor; try easy.
    - specialize(process_closedPS_inv_ite xs (p_ite e P1 P2) e P1 P2); intros.
      assert(process_closedPS xs P1 /\ process_closedPS xs P2). apply H0; try easy.
      clear H0 H.
      destruct H1.
      specialize(IHP1 xs H). destruct IHP1 as (ys,(Ha,Hb)).
      specialize(IHP2 xs H0). destruct IHP2 as (zs,(Hc,Hd)).
      exists (bmerge ys zs).
      split.
      - specialize(bmerge_again ys zs xs); intros.
        apply H1; try easy.
      - constructor; try easy.
    - specialize(process_closedPS_inv_rec xs (p_rec P) P); intros.
      assert(exists x : bool, process_closedPS (x :: xs) P).
      apply H0; try easy. clear H0.
      destruct H1 as (x, Ha).
      specialize(IHP (x :: xs) Ha).
      destruct IHP as (ys,(Hb,Hc)).
      destruct ys; try easy.
      - exists nil.
        split.
        - destruct xs; try easy.
        - constructor; try easy.
      - exists ys.
        inversion Hb. 
        split.
        rewrite H2. easy.
        apply cp_rec1 with (x := b); try easy.
    all: invert_process_closedPS;
      edestruct IHP; eauto; cleanup;
      eexists; split; eauto;
      constructor; eauto.
  Qed.
       
  (* Guardedness forbids immediate unguarded recursion-variable use. *)
  Inductive guardP : list bool -> process -> Prop :=
    | gp_var   : forall n lz, guardP (boollis n) (p_var n lz)
    | gp_end : forall lz, guardP nil (p_end lz)
    | gp_send  : forall A pt l e P, guardP A P -> guardP nil (p_send pt l e P)
    | gp_recv  : forall p ys zs, SForall2 guardP zs ys -> guardP nil (p_recv p ys)
    | gp_ite   : forall xs ys e P Q, guardP xs P -> guardP ys Q -> guardP (bmerge xs ys) (p_ite e P Q)
    | gp_rec0  : forall P, guardP nil P -> guardP nil (p_rec P)
    | gp_rec1  : forall P xs, guardP (false :: xs) P -> guardP xs (p_rec P)
    | gp_newq : forall xs P, guardP xs P -> guardP xs (p_newq P)
    | gp_unitary : forall xs n U lz P, guardP xs P -> guardP xs (p_unitary n U lz P)
    | gp_measure : forall xs z P, guardP xs P -> guardP xs (p_measure z P).
    
  (* Closure-friendly guardedness, mirroring `process_closedPS`. *)
  Inductive guardPS : list bool -> process -> Prop :=
    | gps_var   : forall n lz, guardPS (boollis n) (p_var n lz)
    | gps_end : forall lz, guardPS nil (p_end lz)
    | gps_send  : forall A pt l e P, guardPS A P -> guardPS nil (p_send pt l e P)
    | gps_recv  : forall p ys zs, SForall2 guardPS zs ys -> guardPS nil (p_recv p ys)
    | gps_ite   : forall xs e P Q, guardPS xs P -> guardPS xs Q -> guardPS xs (p_ite e P Q)
    | gps_rec0  : forall P, guardPS nil P -> guardPS nil (p_rec P)
    | gps_rec1  : forall P xs, guardPS (false :: xs) P -> guardPS xs (p_rec P)
    | gps_sub  : forall P xs ys, bmerge xs ys = ys -> guardPS xs P -> guardPS ys P
    | gps_newq : forall xs P, guardPS xs P -> guardPS xs (p_newq P)
    | gps_unitary : forall xs n U lz P, guardPS xs P -> guardPS xs (p_unitary n U lz P)
    | gps_measure : forall xs z P, guardPS xs P -> guardPS xs (p_measure z P).
    
  
  Lemma guardPS_inv_var : forall xs P n lz, P = p_var n lz -> guardPS xs P -> bmerge (boollis n) xs = xs.
  Proof.
    intros. revert H. revert n lz.
    induction H0; intros; try easy.
    - inversion H. subst. 
      clear H.
      induction n0; try easy.
      simpl. rewrite IHn0. easy.
    - subst.
      specialize(IHguardPS n lz (eq_refl (p_var n lz))).
      clear H0.
      revert IHguardPS H.
      revert xs ys.
      induction n; intros; try easy.
      - destruct xs; try easy.
        destruct ys; try easy.
        simpl. 
        inversion IHguardPS. subst.
        inversion H. subst.
        rewrite H3.
        destruct ys; try easy.
      - destruct xs; try easy.
        destruct ys; try easy.
        inversion IHguardPS.
        inversion H.
        specialize(IHn xs ys H1 H3).
        simpl. rewrite H3. rewrite IHn.
        easy.
  Qed.
  
  Lemma guardPS_inv_send : forall xs P pt l e P', (P = p_send pt l e P') -> guardPS xs P -> exists ys, guardPS ys P'.
  Proof.
    intros. revert H. revert pt l e P'.
    induction H0; intros; try easy.
    - inversion H. subst.
      exists A. easy.
    - subst.
      specialize(IHguardPS pt l e P').
      apply IHguardPS; try easy.
  Qed.
  
  Lemma guardPS_inv_recv : forall xs P pt llp, (P = p_recv pt llp) -> guardPS xs P -> exists ys, SForall2 guardPS ys llp.
  Proof.
    intros.
    revert H. revert pt llp.
    induction H0; intros; try easy.
    - inversion H0. subst.
      exists zs. easy.
    - subst.
      specialize(IHguardPS pt llp).
      apply IHguardPS; try easy.
  Qed.
  
  Lemma guardPS_inv_ite : forall xs P e P1 P2, (P = p_ite e P1 P2) -> guardPS xs P -> guardPS xs P1 /\ guardPS xs P2.
  Proof.
    intros. revert H. revert e P1 P2.
    induction H0; intros; try easy.
    - inversion H. subst. easy.
    - subst.
      specialize(IHguardPS e P1 P2 (eq_refl (p_ite e P1 P2))).
      destruct IHguardPS. clear H0.
      split.
      - apply gps_sub with xs; try easy.
      - apply gps_sub with xs; try easy.
  Qed.
  
  Lemma guardPS_inv_rec : forall xs P Q, (P = p_rec Q) -> guardPS xs P -> guardPS (false :: xs) Q.
  Proof.
    intros.
    revert H. revert Q.
    induction H0; intros; try easy.
    - inversion H. subst.
      apply gps_sub with nil; try easy.
    - inversion H. subst. easy.
    - subst.
      specialize(IHguardPS Q (eq_refl (p_rec Q))); intros.
      apply gps_sub with (false :: xs); try easy.
      simpl. rewrite H. easy.
  Qed.

  Lemma guardPS_inv_newq : forall xs P, guardPS xs (p_newq P) -> guardPS xs P.
  Proof.
    intros.
    dependent induction H; intros; eauto.
    econstructor; eauto.
  Qed.

  Lemma guardPS_inv_unitary : forall xs P n U lz, guardPS xs (p_unitary n U lz P) ->  guardPS xs P.
  Proof.
    intros.
    dependent induction H; intros; eauto.
    econstructor; eauto.
  Qed.

  Lemma guardPS_inv_measure : forall xs P z, guardPS xs (p_measure z P) ->  guardPS xs P.
  Proof.
    intros.
    dependent induction H; intros; eauto.
    econstructor; eauto.
  Qed.

  Ltac invert_guardPS :=
    match goal with
    | [H: guardPS _ (p_newq _) |- _] =>
    apply guardPS_inv_newq in H
    | [H: guardPS _ (p_unitary _ _ _ _ ) |- _] =>
    apply guardPS_inv_unitary in H
    | [H: guardPS _ (p_measure _ _) |- _] =>
    apply guardPS_inv_measure in H
    end.
  
  Lemma guardPS_bmergeR : forall P xs ys, guardPS xs P -> guardPS ys P -> guardPS (bmergeR xs ys) P.
  Proof.
    induction P using process_deep_ind; intros.
    - specialize(guardPS_inv_var xs (p_var n lz) n lz (eq_refl (p_var n lz)) H); intros.
      specialize(guardPS_inv_var ys (p_var n lz) n lz (eq_refl (p_var n lz)) H0); intros.
      clear H H0.
      apply gps_sub with (boollis n).
      - revert H1 H2. revert xs ys.
        induction n; intros; try easy.
        - destruct xs; try easy.
          destruct ys; try easy.
          simpl.
          inversion H1. subst. inversion H2. subst.
          destruct xs; try easy.
          - destruct ys; try easy.
          - destruct ys; try easy.
        - destruct xs; try easy.
          destruct ys; try easy.
          inversion H1. inversion H2.
          specialize(IHn xs ys H0 H3).
          simpl. rewrite H0. rewrite H3. rewrite IHn. easy.
      - constructor.
    - apply gps_sub with nil.
      - destruct xs; try easy.
        - destruct ys; try easy.
        - destruct ys; try easy.
      - constructor.
    - specialize(guardPS_inv_send xs (p_send pt lb ex P) pt lb ex P (eq_refl (p_send pt lb ex P)) H); intros.
      destruct H1 as (zs, Ha).
      apply gps_sub with nil; try easy.
      - destruct xs; try easy.
        - destruct ys; try easy.
        - destruct ys; try easy.
      - apply gps_send with zs; try easy.
    - specialize(guardPS_inv_recv xs (p_recv pt llp) pt llp); intros.
      assert(exists ys : slist (seq.seq bool), SForall2 guardPS ys llp).
      apply H2; try easy. clear H2. destruct H3 as (zs, H3).
      apply gps_sub with nil; try easy.
      - destruct xs; try easy.
        - destruct ys; try easy.
        - destruct ys; try easy.
      - apply gps_recv with zs; try easy.
    - specialize(guardPS_inv_ite xs (p_ite e P1 P2) e P1 P2); intros.
      assert(guardPS xs P1 /\ guardPS xs P2).
      apply H1; try easy. clear H1.
      specialize(guardPS_inv_ite ys (p_ite e P1 P2) e P1 P2); intros.
      assert(guardPS ys P1 /\ guardPS ys P2).
      apply H1; try easy. clear H1.
      destruct H2. destruct H3.
      specialize(IHP1 xs ys H1 H3).
      specialize(IHP2 xs ys H2 H4).
      constructor; try easy.
    - specialize(guardPS_inv_rec xs (p_rec P) P); intros.
      assert(guardPS (false :: xs) P). apply H1; try easy. clear H1.
      specialize(guardPS_inv_rec ys (p_rec P) P); intros.
      assert(guardPS (false :: ys) P). apply H1; try easy. clear H1.
      specialize(IHP (false :: xs) (false :: ys) H2 H3).
      apply gps_rec1; try easy.
    all: repeat invert_guardPS; cleanup; eauto;
       econstructor; eapply IHP; try easy.
  Qed.
  
  Lemma guardPS_any_length : forall P xs n, guardPS xs P -> exists xl xe xr, length xl = n /\ guardPS (xl ++ [xe] ++ xr) P.
  Proof.
    induction P using process_deep_ind; intros; try easy.
    - specialize(guardPS_inv_var xs (p_var n lz) n lz); intros.
      assert(bmerge (boollis n) xs = xs). apply H0; try easy. clear H0.
      clear H.
      revert H1. revert xs n.
      induction n0; intros.
      - exists nil.
        destruct n.
        - exists true. exists nil.
          split. easy.
          replace [true] with (boollis 0); try easy.
          specialize(app_nil_r (boollis 0)); intros.
          rewrite H. constructor.
        - exists false. exists (boollis n).
          split. easy.
          simpl.
          replace (false :: boollis n) with (boollis (S n)); try easy.
          constructor.
      - destruct n; try easy.
        - exists (true :: false_list n0). exists false. exists nil.
          clear IHn0 H1. clear xs.
          split.
          - simpl. induction n0; intros; try easy.
            simpl. rewrite IHn0. easy.
          - apply gps_sub with (boollis 0); try easy.
            simpl. destruct n0; try easy.
            constructor.
        - destruct xs; try easy.
          inversion H1.
          specialize(IHn0 xs n H0).
          destruct IHn0 as (xl,(xe,(xr,(Ha,Hb)))).
          exists (false :: xl). exists xe. exists xr.
          split. simpl. rewrite Ha. easy.
          specialize(guardPS_inv_var (xl ++ [xe] ++ xr) (p_var n lz) n lz); intros.
          assert(bmerge (boollis n) (xl ++ [xe] ++ xr) = xl ++ [xe] ++ xr).
          apply H; try easy. clear H.
          apply gps_sub with (boollis (S n)); try easy.
          - simpl. simpl in *. rewrite H2. easy.
          - constructor.
    - exists (false_list n). exists false. exists nil.
      clear H xs.
      split.
      - induction n; intros; try easy.
        simpl.
        rewrite IHn. easy.
      - apply gps_sub with nil; try easy.
        - destruct n; try easy.
        - constructor.
    - exists (false_list n). exists false. exists nil.
      specialize(guardPS_inv_send xs (p_send pt lb ex P) pt lb ex P); intros.
      assert(exists ys : seq.seq bool, guardPS ys P). apply H0; try easy.
      destruct H1 as (ys, Ha).
      split.
      - clear IHP H0 H Ha. clear pt lb ex P xs ys.
        induction n; intros; try easy.
        simpl. rewrite IHn. easy.
      - apply gps_sub with nil; try easy.
        - destruct n; try easy.
        - apply gps_send with ys; try easy.
    - clear H.
      exists (false_list n). exists false. exists nil.
      specialize(guardPS_inv_recv xs (p_recv pt llp) pt llp); intros.
      assert(exists ys : slist (seq.seq bool), SForall2 guardPS ys llp).
      apply H; try easy. clear H. destruct H1 as (ys, Ha).
      split.
      - clear Ha H0. clear pt llp xs ys.
        induction n; intros; try easy.
        simpl. rewrite IHn. easy.
      - apply gps_sub with nil; try easy.
        - destruct n; try easy.
        - apply gps_recv with ys; try easy.
    - specialize(guardPS_inv_ite xs (p_ite e P1 P2) e P1 P2); intros.
      assert(guardPS xs P1 /\ guardPS xs P2).
      apply H0; try easy. clear H0 H.
      destruct H1.
      specialize(IHP1 xs n H).
      specialize(IHP2 xs n H0).
      destruct IHP1 as (xla,(xea,(xra,(Ha,Hb)))).
      destruct IHP2 as (xlb,(xeb,(xrb,(Hc,Hd)))).
      exists (bmerge xla xlb). exists (orb xea xeb). exists (bmerge xra xrb).
      split.
      - clear H0 H Hd Hb. clear xs xrb xeb xra xea P1 P2 e.
        revert Ha Hc. revert xla xlb.
        induction n; intros; try easy.
        - destruct xla; try easy.
          destruct xlb; try easy.
        - destruct xla; try easy.
          destruct xlb; try easy.
          simpl in *.
          inversion Ha. inversion Hc.
          specialize(IHn xla xlb H0 H1).
          rewrite IHn. easy.
      - clear H0 H. clear xs. 
        constructor.
        - apply gps_sub with (xla ++ [xea] ++ xra); try easy.
          clear e P2 Hb Hd P1. revert Ha Hc.
          revert xea xra xlb xeb xrb n.
          induction xla; intros; try easy.
          - destruct n; try easy.
            destruct xlb; try easy.
            simpl.
            clear Ha Hc.
            specialize(bmerge_again_l xra xrb); intros.
            rewrite H. destruct xea; try easy.
          - destruct n; try easy.
            destruct xlb; try easy.
            inversion Ha. inversion Hc. clear Ha Hc.
            specialize(IHxla xea xra xlb xeb xrb n H0 H1).
            simpl in *. rewrite IHxla.
            destruct a; try easy.
        - apply gps_sub with (xlb ++ [xeb] ++ xrb); try easy.
          clear e P2 Hb Hd P1. revert Ha Hc.
          revert xea xra xla xeb xrb n.
          induction xlb; intros; try easy.
          - destruct n; try easy.
            destruct xla; try easy.
            simpl.
            clear Ha Hc.
            specialize(bmerge_again_r xra xrb); intros.
            rewrite H. destruct xeb; try easy. destruct xea; try easy.
          - destruct n; try easy.
            destruct xla; try easy.
            inversion Ha. inversion Hc. clear Ha Hc.
            specialize(IHxlb xea xra xla xeb xrb n H0 H1).
            simpl in *. rewrite IHxlb.
            destruct a; try easy. destruct b; try easy.
    - specialize(guardPS_inv_rec xs (p_rec P) P); intros.
      assert(guardPS (false :: xs) P). apply H0; try easy.
      clear H0 H.
      specialize(IHP (false :: xs) (S n) H1).
      destruct IHP as (xl,(xe,(xr,(Hb,Hc)))).
      destruct xl; try easy.
      exists xl. exists xe. exists xr.
      inversion Hb. split. easy.
      apply gps_rec1; try easy.
      specialize(guardPS_bmergeR P (false :: xs) ((b :: xl) ++ [xe] ++ xr) H1 Hc); intros.
      apply gps_sub with (bmergeR (false :: xs) ((b :: xl) ++ [xe] ++ xr)); try easy.
      clear H H0 H1 Hc Hb.
      simpl.
      specialize(bmergeR_back xs (xl ++ xe :: xr)); intros.
      rewrite H. easy.
    - invert_guardPS; edestruct IHP; eauto;     cleanup.
      do 3 eexists; split; eauto.
      apply gps_newq; eauto.
    - invert_guardPS; edestruct IHP; eauto;     cleanup.
      do 3 eexists; split; eauto.
      apply gps_unitary; eauto.
    - invert_guardPS; edestruct IHP; eauto;     cleanup.
      do 3 eexists; split; eauto.
      apply gps_measure; eauto.
  Qed.
  
  Lemma guardPS_free : forall Q xl xr l m n, guardPS (xl ++ xr) Q -> guardPS (xl ++ (false_list m) ++ xr) (incr_free (length xl) l m n Q).
  Proof.
    induction Q using process_deep_ind; intros; try easy.
    - simpl.
      specialize(guardPS_inv_var (xl ++ xr) (p_var n lz) n lz); intros.
      assert(bmerge (boollis n) (xl ++ xr) = xl ++ xr). apply H0; try easy. clear H H0.
      case_eq (Nat.leb (length xl) n); intros.
      - revert H H1.
        revert n xr m.
        induction xl; intros; try easy.
        - simpl in *.
          apply gps_sub with (boollis (n + m)); try easy.
          - specialize(Nat.add_comm n m); intros. rewrite H0. clear H0.
            clear H.
            revert H1. revert xr n.
            induction m; intros; try easy.
            - simpl. 
            specialize(IHm xr n H1). rewrite IHm. easy.
          - constructor. 
        - destruct n; try easy.
          inversion H1.
          specialize(IHxl n xr m H H2).
          apply gps_sub with (boollis (S n + m)); try easy.
          - simpl.
            specialize(guardPS_inv_var (xl ++ false_list m ++ xr)
              (p_var (n + m) (map (incr_free_expression l n0) lz)) (n + m)
              (map (incr_free_expression l n0) lz)); intros.
            assert(bmerge (boollis (n + m)) (xl ++ false_list m ++ xr) =
     xl ++ false_list m ++ xr).
            apply H0; try easy.
            rewrite H3. easy.
          - constructor.
      - revert H1 H.
        revert n xr m.
        induction xl; intros; try easy.
        destruct n; try easy.
        - inversion H1. subst.
          apply gps_sub with (boollis 0); try easy.
          - simpl. destruct xl; try easy.
            destruct m; try easy. 
          - constructor.
        - inversion H1. subst.
          specialize(IHxl n xr m H2 H).
          specialize(guardPS_inv_var (xl ++ false_list m ++ xr)
            (p_var n (map (incr_free_expression l n0) lz)) n
            (map (incr_free_expression l n0) lz)); intros.
          assert(bmerge (boollis n) (xl ++ false_list m ++ xr) = xl ++ false_list m ++ xr).
          apply H0; try easy. clear H0 IHxl.
          apply gps_sub with (boollis (S n)); try easy.
          - simpl. rewrite H3. easy.
          - constructor.
    - apply gps_sub with nil; try easy.
      - destruct xl; try easy. destruct m; try easy. destruct xr; try easy.
      - constructor.
    - simpl.
      specialize(guardPS_inv_send (xl ++ xr) (p_send pt lb ex Q) pt lb ex Q); intros.
      assert(exists ys : seq.seq bool, guardPS ys Q).
      apply H0; try easy. clear H0 H.
      destruct H1 as (ys, Ha).
      apply gps_sub with nil.
      - destruct xl; try easy.
        destruct m; try easy.
        destruct xr; try easy.
      - specialize(guardPS_any_length Q ys (length xl) Ha); intros.
        destruct H as (xl0,(xe,(xr0,(Hb,Hc)))).
        specialize(IHQ xl0 (xe :: xr0) l m n Hc).
        apply gps_send with (xl0 ++ false_list m ++ xe :: xr0); try easy.
        symmetry in Hb; rewrite Hb; try easy.
    - simpl.
      specialize(guardPS_inv_recv (xl ++ xr) (p_recv pt llp) pt llp); intros.
      assert(exists ys : slist (seq.seq bool), SForall2 guardPS ys llp).
      apply H1; try easy.
      destruct H2 as (ys, Ha).
      clear H1 H0.
      apply gps_sub with nil.
      - destruct xl; try easy. destruct m; try easy. destruct xr; try easy.
      revert Ha H. clear xr. 
      revert pt xl m n ys.
      induction llp; intros; try easy.
      - inversion Ha. subst. clear Ha.
        inversion H. subst. clear H.
        specialize(guardPS_any_length a x (length xl) H2); intros.
        destruct H as (xl0,(xe,(xr0,(Ha,Hb)))).
        specialize(H1 xl0 (xe :: xr0)).
        apply gps_recv with (zs := slist_x ((xl0 ++ false_list m ++ xe :: xr0))); try easy.
        constructor; try easy.
        symmetry in Ha; rewrite Ha.
        apply H1; try easy.
      inversion Ha.
      - subst. clear Ha.
        inversion H. subst. clear H.
        specialize(IHllp pt xl m n xs H4 H5).
        clear H5 H4.
        specialize(guardPS_inv_recv nil (p_recv pt (smap (incr_free (length xl) (S l) m n) llp)) pt (smap (incr_free (length xl) (S l) m n) llp)); intros.
        assert(exists ys : slist (seq.seq bool),
      SForall2 guardPS ys (smap (incr_free (length xl) (S l) m n) llp)).
        apply H; try easy.
        destruct H0 as (zs, Ha).
        clear H IHllp.
        specialize(guardPS_any_length y x (length xl) H3); intros.
        destruct H as (xl0,(xe,(xr,(Hb,Hc)))).
        specialize(H2 xl0 (xe :: xr) (S l) m n Hc).
        rewrite Hb in H2.
        apply gps_recv with (slist_xs (Some (xl0 ++ false_list m ++ xe :: xr)) zs).
        constructor; try easy.
      - subst. clear Ha.
        inversion H. subst. clear H.
        specialize(IHllp pt xl m n xs H2 H1).
        clear H2 H1.
        specialize(guardPS_inv_recv nil (p_recv pt (smap (incr_free (length xl) (S l) m n) llp)) pt (smap (incr_free (length xl) (S l) m n) llp)); intros.
        assert(exists ys : slist (seq.seq bool),
      SForall2 guardPS ys (smap (incr_free (length xl) (S l) m n) llp)).
        apply H; try easy.
        destruct H0 as (zs, Ha).
        clear H IHllp.
        apply gps_recv with (slist_xs None zs).
        constructor; try easy.
    - simpl.
      specialize(guardPS_inv_ite (xl ++ xr) (p_ite e Q1 Q2) e Q1 Q2); intros.
      assert(guardPS (xl ++ xr) Q1 /\ guardPS (xl ++ xr) Q2).
      apply H0; try easy. 
      clear H0 H.
      constructor.
      - apply IHQ1; try easy.
      - apply IHQ2; try easy.
    - simpl.
      specialize(guardPS_inv_rec (xl ++ xr) (p_rec Q) Q); intros.
      assert(guardPS (false :: xl ++ xr) Q).
      apply H0; try easy. clear H0.
      specialize(IHQ (false :: xl) xr l m n H1).
      apply gps_rec1; try easy.
    all: simpl;
      invert_guardPS; cleanup; 
      solve [econstructor; eauto].
  Qed.
  
  Lemma guardPS_remove_false : forall Q xs n, guardPS (xs ++ false_list n) Q -> guardPS xs Q.
  Proof.
    induction Q using process_deep_ind; intros; try easy.
    - specialize(guardPS_inv_var (xs ++ false_list n0) (p_var n lz) n lz); intros.
      assert(bmerge (boollis n) (xs ++ false_list n0) = xs ++ false_list n0).
      apply H0; try easy. clear H0 H.
      apply gps_sub with (xs := (boollis n)); try easy.
      - revert H1.
        revert xs.
        induction n; intros; try easy.
        simpl in H1.
        destruct xs; try easy.
        - destruct n0; try easy.
        - simpl in H1.
          inversion H1. subst.
          simpl. destruct xs; try easy.
      - destruct xs; try easy.
        - clear IHn.
          assert(exists m, S n = m). exists (S n). easy.
          destruct H as (m, H). rewrite H in H1. rewrite H. clear H. clear n.
          assert False.
          revert H1. rename m into n. revert n0.
          induction n; intros; try easy.
          - destruct n0; try easy.
          - destruct n0; try easy.
            inversion H1. 
            apply IHn with (n0 := n0); try easy.
          easy.
        - inversion H1. 
          simpl. specialize(IHn xs H0).
          rewrite IHn. easy.
        constructor.
    - apply gps_sub with nil; try easy.
      - destruct xs; try easy.
      - constructor.
    - specialize(guardPS_inv_send (xs ++ false_list n) (p_send pt lb ex Q) pt lb ex Q); intros.
      assert(exists ys : seq.seq bool, guardPS ys Q).
      apply H0; try easy. clear H0 H.
      destruct H1 as (ys, H1).
      apply gps_sub with nil; try easy.
      - destruct xs; try easy.
      - apply gps_send with ys; try easy.
    - specialize(guardPS_inv_recv (xs ++ false_list n) (p_recv pt llp) pt llp); intros.
      assert(exists ys : slist (seq.seq bool), SForall2 guardPS ys llp).
      apply H1; try easy. clear H1 H0.
      destruct H2 as (ys, H2).
      apply gps_sub with nil.
      - destruct xs; try easy.
      - apply gps_recv with ys; try easy.
    - specialize(guardPS_inv_ite (xs ++ false_list n) (p_ite e Q1 Q2) e Q1 Q2); intros.
      assert(guardPS (xs ++ false_list n) Q1 /\ guardPS (xs ++ false_list n) Q2).
      apply H0; try easy.
      constructor.
      - apply IHQ1 with (n := n); try easy.
      - apply IHQ2 with (n := n); try easy.
    - specialize(guardPS_inv_rec (xs ++ false_list n) (p_rec Q) Q); intros.
      assert(guardPS (false :: xs ++ false_list n) Q).
      apply H0; try easy.
      apply gps_rec1.
      apply IHQ with (n := n); try easy.
    all: simpl;
      invert_guardPS; cleanup; 
      solve [econstructor; eauto].
  Qed.
      
  Lemma guardPS_freeS : forall Q m n, guardPS nil Q -> guardPS nil (incr_free 0 0 m n Q).
  Proof.
    intros.
    specialize(guardPS_free Q nil nil 0 m n H); intros.
    simpl in *.
    specialize(guardPS_remove_false (incr_free 0 0 m n Q) nil m); intros.
    apply H1; try easy.
    clear H1 H.
    specialize(app_nil_r (false_list m)); intros.
    rewrite H in H0. easy.
  Qed.
  
  Lemma guardPS_subst : forall P Q xl xe xr m n, guardPS (xl ++ [xe] ++ xr) P -> guardPS nil Q -> guardPS (xl ++ xr) (substitutionP (length xl) m n Q P).
  Proof.
    induction P using process_deep_ind; intros; try easy.
    - specialize(guardPS_inv_var (xl ++ [xe] ++ xr) (p_var n lz) n lz); intros.
      assert(bmerge (boollis n) (xl ++ [xe] ++ xr) = xl ++ [xe] ++ xr).
      apply H1; try easy.
      clear H1 H.
      simpl.

    - destruct_fresh (n <? length xl); intros.
        - clear H0. clear Q m n0.
          revert HD H2. revert xl xe xr. 
          induction n; intros; try easy.
          - destruct xl; try easy. 
            inversion H2. subst.
            apply gps_sub with (boollis 0); try easy.
            simpl. destruct xl; try easy. destruct xr; try easy.
            constructor.
          - destruct xl; try easy.
            inversion H2. 
            specialize(IHn xl xe xr HD H0).
            specialize(guardPS_inv_var (xl ++ xr) (p_var n lz) n lz); intros.
            assert(bmerge (boollis n) (xl ++ xr) = xl ++ xr). apply H; try easy.
            clear H H0 H2 HD IHn.
            apply gps_sub with (boollis (S n)); try easy.
            - simpl. rewrite H1. easy.
            - constructor.

        case_eq (n =? length xl); intros.
        - apply gps_sub with nil; try easy.
          - destruct xl; destruct xr; try easy.
          - clear HD H.
            apply guardPS_freeS; try easy.

        - clear H0.
          assert (exists m, n = S m).
          destruct n; simpl in *. 
          destruct xl; try easy.
          eexists; eauto.
          cleanup.
          simpl;
          rewrite Nat.sub_0_r.
          revert HD H H2. revert m0 xe xr. clear Q.
          induction xl; intros; try easy.
          - inversion H2. simpl in *.
            apply gps_sub with (xs := (boollis m0)); try easy.
            rewrite H1; eauto.
            econstructor.
      
          - simpl in *. inversion H2.
            destruct m0.
            simpl in *.
            apply gps_sub with (xs := nil); try easy.
            destruct xl; simpl in *; try easy.
            specialize(IHxl m0 xe xr HD H H1).
            clear HD H2 H H1.
            specialize(guardPS_inv_var (xl ++ xr) (p_var m0 lz) m0 lz); intros.
            assert(bmerge (boollis m0) (xl ++ xr) = xl ++ xr).
            apply H; try easy. clear H.
            apply gps_sub with (boollis (S m0)); try easy.
            - simpl. rewrite H0. easy.
            - constructor.

    - apply gps_sub with nil; try easy.
      destruct xl; try easy. destruct xr; try easy.
      constructor.
    - apply gps_sub with nil; try easy.
      - destruct xl; try easy. destruct xr; try easy.
      - simpl. 
        specialize(guardPS_inv_send (xl ++ [xe] ++ xr) (p_send pt lb ex P) pt lb ex P); intros.
        assert(exists ys : seq.seq bool, guardPS ys P).
        apply H1; try easy. clear H1.
        destruct H2 as (ys, Ha).
        specialize(guardPS_any_length P ys (length xl) Ha); intros.
        destruct H1 as (xl0,(xe0,(xr0,(Hb,Hc)))).
        apply gps_send with (xl0 ++ xr0); try easy.
        symmetry in Hb; rewrite (Hb).
        apply IHP with (xe := xe0); try easy.
    - apply gps_sub with nil.
      - destruct xl; try easy. destruct xr; try easy.
      specialize(guardPS_inv_recv (xl ++ [xe] ++ xr) (p_recv pt llp) pt llp); intros.
      assert(exists ys : slist (seq.seq bool), SForall2 guardPS ys llp).
      apply H2; try easy. clear H2.
      destruct H3 as (ys, Ha). clear H0.
      revert H H1 Ha.
      revert Q xl m n ys. clear xe xr.
      induction llp; intros; try easy.
      - inversion Ha. subst. clear Ha.
        inversion H. subst. clear H.
        simpl.
        specialize(guardPS_any_length a x (length xl) H3); intros.
        destruct H as (xl0,(xe0,(xr0,(Ha,Hb)))).
        
        symmetry in Ha; rewrite (Ha).
        apply gps_recv with (slist_x (xl0 ++ xr0)); try easy.
        constructor; try easy.
        apply H2 with (xe := xe0); try easy.
      inversion Ha.
      - subst. clear Ha.
        inversion H. subst. clear H.
        simpl in *.
        specialize(IHllp Q xl m n xs H6 H1 H5).
        clear H6 H5.
        specialize(guardPS_inv_recv nil (p_recv pt (smap (substitutionP (length xl) m (S n) Q) llp)) pt (smap (substitutionP (length xl) m (S n) Q) llp)); intros.
        assert(exists ys : slist (seq.seq bool),
      SForall2 guardPS ys (smap (substitutionP (length xl) m (S n) Q) llp)).
        apply H; try easy. clear H.
        destruct H0 as (ys, Ha). clear IHllp.
        specialize(guardPS_any_length y x (length xl) H4); intros.
        destruct H as (xl0,(xe0,(xr0,(Hb,Hc)))).
        apply gps_recv with (slist_xs (Some (xl0 ++ xr0)) ys).
        constructor; try easy.
        symmetry in Hb; rewrite Hb. apply H3 with (xe := xe0); try easy.
      - subst. clear Ha.
        inversion H. subst. clear H.
        simpl in *.
        specialize(IHllp Q xl m n xs H2 H1 H3).
        simpl in *.
        specialize(guardPS_inv_recv nil (p_recv pt (smap (substitutionP (length xl) m (S n) Q) llp)) pt (smap (substitutionP (length xl) m (S n) Q) llp)); intros.
        assert(exists ys : slist (seq.seq bool),
      SForall2 guardPS ys (smap (substitutionP (length xl) m (S n) Q) llp)).
        apply H; try easy. clear H.
        destruct H0 as (ys, Ha). clear IHllp.
        apply gps_recv with (slist_xs None ys).
        constructor; try easy.
    - specialize(guardPS_inv_ite (xl ++ [xe] ++ xr) (p_ite e P1 P2) e P1 P2); intros.
      assert(guardPS (xl ++ [xe] ++ xr) P1 /\ guardPS (xl ++ [xe] ++ xr) P2).
      apply H1; try easy. clear H1 H.
      destruct H2.
      simpl.
      constructor.
      - apply IHP1 with (xe := xe); try easy.
      - apply IHP2 with (xe := xe); try easy.
    - specialize(guardPS_inv_rec (xl ++ [xe] ++ xr) (p_rec P) P); intros.
      assert (guardPS (false :: xl ++ [xe] ++ xr) P).
      apply H1; try easy. clear H1.
      simpl.
      apply gps_rec1.
      specialize(IHP Q (false :: xl) xe xr).
      apply IHP; try easy.
    all: simpl;
      invert_guardPS; cleanup; 
      solve [econstructor; eauto].
  Qed.
  
  Lemma guardP_to_PS : forall xs P, guardP xs P -> guardPS xs P.
  Proof.
    intros xs P. revert xs.
    induction P using process_deep_ind; intros; try easy.
    - inversion H.
      constructor.
    - inversion H.
      constructor.
    - inversion H.
      subst.
      specialize(IHP A H2).
      apply gps_send with A; try easy.
    - inversion H0. subst.
      clear H0.
      revert H3 H.
      revert pt zs.
      induction llp; intros; try easy.
      - inversion H3. subst. clear H3.
        inversion H. subst. clear H.
        specialize(H1 x H2).
        apply gps_recv with (slist_x x).
        constructor. easy.
      inversion H3.
      - subst. clear H3.
        inversion H. subst. clear H.
        specialize(H2 x H4). clear H4.
        apply gps_recv with (slist_xs (Some x) xs).
        constructor; try easy.
        revert H3 H5. clear IHllp H2. clear pt x y.
        revert xs.
        induction llp; intros.
        - inversion H5. subst. clear H5.
          inversion H3. subst. clear H3.
          constructor. apply H0; try easy.
        inversion H5.
        - subst. clear H5.
          inversion H3. subst. clear H3.
          specialize(IHllp xs0 H5 H4).
          constructor; try easy.
          apply H1; try easy.
        - subst. clear H5.
          inversion H3. subst. clear H3.
          specialize(IHllp xs0 H0 H1).
          constructor; try easy.
      - subst. clear H3.
        inversion H. subst. clear H.
        apply gps_recv with (slist_xs None xs); try easy.
        constructor; try easy.
        revert H1 H2. 
        clear IHllp. clear pt. revert xs.
        induction llp; intros; try easy.
        - inversion H2. subst. clear H2.
          inversion H1. subst. clear H1.
          constructor. apply H0; try easy.
        inversion H2.
        - subst. clear H2.
          inversion H1. subst. clear H1.
          specialize(IHllp xs0 H3 H5).
          constructor; try easy.
          apply H2; try easy.
        - subst. clear H2.
          inversion H1. subst. clear H1.
          specialize(IHllp xs0 H0 H3).
          constructor; try easy.
    - inversion H. subst.
      constructor.
      - apply gps_sub with xs0; try easy.
        apply bmerge_again_l; try easy.
        apply IHP1; try easy.
      - apply gps_sub with ys; try easy.
        apply bmerge_again_r; try easy.
        apply IHP2; try easy.
    - inversion H. subst.
      - apply gps_rec0.
        apply IHP; try easy.
      - subst.
        apply gps_rec1.
        apply IHP; try easy.
    all: inversion H;
      subst;
      specialize(IHP xs H2);
      solve [econstructor; eauto].
  Qed. 
        
  Lemma guardPS_to_P : forall xs P, guardPS xs P -> exists ys, bmerge ys xs = xs /\ guardP ys P.
  Proof.
    intros xs P. revert xs.
    induction P using process_deep_ind; intros; try easy.
    - specialize(guardPS_inv_var xs (p_var n lz) n lz); intros.
      assert(bmerge (boollis n) xs = xs). apply H0; try easy.
      clear H0.
      exists (boollis n).
      split. easy. constructor.
    - exists nil.
      split. destruct xs; try easy.
      constructor.
    - specialize(guardPS_inv_send xs (p_send pt lb ex P) pt lb ex P); intros.
      assert(exists ys : seq.seq bool, guardPS ys P). apply H0; try easy. clear H0 H.
      destruct H1 as (ys, H1).
      specialize(IHP ys H1).
      destruct IHP as (zs,(Ha,Hb)).
      exists nil.
      split.
      - destruct xs; try easy.
      - apply gp_send with zs; try easy.
    - specialize(guardPS_inv_recv xs (p_recv pt llp) pt llp); intros.
      assert(exists ys : slist (seq.seq bool), SForall2 guardPS ys llp). apply H1; try easy. clear H1 H0.
      destruct H2 as (ys, Ha).
      exists nil.
      split.
      - destruct xs; try easy.
      - revert Ha H. clear xs.
        revert ys.
        induction llp; intros; try easy.
        - inversion Ha. subst. clear Ha.
          inversion H. subst. clear H.
          specialize(H1 x H2).
          destruct H1 as (ys,(Ha,Hb)).
          apply gp_recv with (slist_x ys); try easy.
          constructor; try easy.
        inversion Ha.
        - subst. clear Ha.
          inversion H. subst. clear H.
          specialize(IHllp xs H4 H5).
          inversion IHllp. subst.
          clear H5 H4.
          specialize(H2 x H3). destruct H2 as (ys,(Ha,Hb)).
          apply gp_recv with (slist_xs (Some ys) zs).
          constructor; try easy.
        - subst. clear Ha.
          inversion H. subst. clear H.
          specialize(IHllp xs H2 H1).
          inversion IHllp. subst.
          clear H2 H1.
          apply gp_recv with (slist_xs None zs).
          constructor; try easy.
    - specialize(guardPS_inv_ite xs (p_ite e P1 P2) e P1 P2); intros.
      assert(guardPS xs P1 /\ guardPS xs P2). apply H0; try easy.
      clear H0 H.
      destruct H1.
      specialize(IHP1 xs H). destruct IHP1 as (ys,(Ha,Hb)).
      specialize(IHP2 xs H0). destruct IHP2 as (zs,(Hc,Hd)).
      exists (bmerge ys zs).
      split.
      - specialize(bmerge_again ys zs xs); intros.
        apply H1; try easy.
      - constructor; try easy.
    - specialize(guardPS_inv_rec xs (p_rec P) P); intros.
      assert(guardPS (false :: xs) P).
      apply H0; try easy. clear H0.
      specialize(IHP (false :: xs) H1).
      destruct IHP as (ys,(Hb,Hc)).
      destruct ys; try easy.
      - exists nil.
        split.
        - destruct xs; try easy.
        - constructor; try easy.
      - exists ys.
        inversion Hb. 
        split.
        rewrite H3. easy.
        apply gp_rec1; try easy.
        destruct b; try easy.
    all: invert_guardPS; cleanup;
      specialize(IHP xs H);
      cleanup; eexists; split; eauto;
      solve [econstructor; eauto].
  Qed.
  
  Lemma guard_less_process_closedP : forall P xs ys, guardP xs P -> process_closedP ys P -> bmerge xs ys = ys.
  Proof.
    induction P using process_deep_ind; intros; try easy.
    - inversion H. subst.
      inversion H0. subst.
      clear H H0.
      induction n; intros; try easy.
      - simpl. 
        replace (bmerge (boollis n) (boollis n)) with (boollis n) in *. easy.
    - inversion H. subst.
      inversion H0. subst. easy.
    - inversion H. subst.
      clear H H0 H3 IHP. clear pt lb ex P A.
      induction ys; intros; try easy.
    - inversion H0. subst.
      clear H H0 H1 H4. clear pt llp zs.
      induction ys; intros; try easy.
    - inversion H. subst.
      inversion H0. subst.
      specialize(IHP1 xs0 xs H4 H5).
      specialize(IHP2 ys0 ys1 H6 H8).
      clear H H0 H4 H6 H5 H8.
      clear P1 P2 e.
      revert IHP1 IHP2. revert xs0 ys0 ys1.
      induction xs; intros; try easy.
      - destruct xs0; try easy. 
        destruct ys0; try easy. destruct ys1; try easy.
        destruct ys1; try easy.
      - destruct ys1; try easy.
        - destruct ys0; try easy. simpl.
          destruct xs0; try easy.
        - destruct ys0; try easy. simpl.
          destruct xs0; try easy.
          inversion IHP1.
          simpl.
          replace (bmerge xs0 xs) with (xs).
          specialize(IHxs xs0 nil ys1).
          assert(bmerge (bmerge xs0 []) (bmerge xs ys1) =
       bmerge xs ys1).
          {
            apply IHxs; try easy.
            destruct ys1; try easy.
          }
          assert(bmerge xs0 nil = xs0).
          {
            destruct xs0; try easy.
          }
          replace (bmerge xs0 []) with xs0 in *.
          replace (bmerge xs0 (bmerge xs ys1)) with (bmerge xs ys1) in *.
          destruct b0; try easy.
        - destruct xs0; try easy.
          inversion IHP2. 
          replace (bmerge ys0 ys1) with ys1.
          simpl.
          specialize(IHxs nil ys0 ys1).
          assert(bmerge (bmerge [] ys0) (bmerge xs ys1) =
       bmerge xs ys1).
          {
            apply IHxs; try easy.
            destruct xs; try easy.
          }
          assert(bmerge nil ys0 = ys0).
          {
            destruct ys0; try easy.
          }
          replace (bmerge nil ys0) with ys0 in *.
          replace (bmerge ys0 (bmerge xs ys1)) with (bmerge xs ys1) in *.
          destruct b0; try easy.
          destruct a; try easy.
        - simpl.
          inversion IHP1. 
          inversion IHP2. 
          replace (bmerge xs0 xs) with xs.
          replace (bmerge ys0 ys1) with ys1.
          specialize(IHxs xs0 ys0 ys1).
          assert(bmerge (bmerge xs0 ys0) (bmerge xs ys1) =
       bmerge xs ys1).
          {
            apply IHxs; try easy.
          }
          replace (bmerge (bmerge xs0 ys0) (bmerge xs ys1)) with (bmerge xs ys1) in *.
          destruct b1; try easy. 
          destruct b0; try easy. destruct a; try easy.
    - inversion H.
      - subst.
        destruct ys; try easy.
      - subst.
        inversion H0. subst. 
        specialize(IHP (false :: xs) nil H3 H4).
        easy.
      - subst.
        specialize(IHP (false :: xs) (x :: ys) H3 H4).
        inversion IHP. 
        replace (bmerge xs ys) with ys. easy.
    all: inversionc H; inversionc H0; eauto. 
  Qed.
  
  (* Quantitative guardedness: bounds recursion unfolding depth (`n`)
     and interaction depth (`m`) used in normalization arguments. *)
  Inductive cguardP : fin -> fin -> process -> Prop :=  
    | cgp_nil : forall m G, cguardP 0 m G
    | cgp_end : forall n m lz, cguardP n m (p_end lz)
    | cgp_send : forall n m pt l e g, cguardP n m g -> cguardP (S n) (S m) (p_send pt l e g)
    | cgp_recv : forall n m p lis, SForall (cguardP n m) lis -> cguardP (S n) (S m) (p_recv p lis)
    | cgp_ite : forall n m P Q e, cguardP n m P -> cguardP n m Q -> cguardP n (S m) (p_ite e P Q)
    | cgp_rec : forall n m g, cguardP n m (substitutionP 0 0 0 (p_rec g) g) -> cguardP n (S m) (p_rec g)
    | cgp_newq : forall n m P, cguardP n m P -> cguardP (S n) (S m) (p_newq P)
    | cgp_unitary : forall n m n0 U lz P, cguardP n m P -> cguardP (S n) (S m) (p_unitary n0 U lz P)
    | cgp_measure : forall n m z P, cguardP n m P -> cguardP (S n) (S m) (p_measure z P).
    
  Lemma cguardP_more : forall m m' n P, m < m' -> cguardP n m P -> cguardP n m' P.
  Proof.
    induction m; intros; try easy.
    - inversion H0. subst. 
      constructor.
      subst. constructor.
    - inversion H0. subst.
      - constructor.
      - constructor.
      - subst. destruct m'; try easy.
        constructor. apply IHm; try easy.
        lia.
      - subst. destruct m'; try easy.
        constructor.
        clear H0.
        revert H3. apply SForall_mono; intros.
        apply IHm; try easy.
        lia.
    - subst.
      destruct m'; try easy. constructor.
      - apply IHm; try easy. lia.
      - apply IHm; try easy. lia.
    - subst.
      destruct m'; try easy.
      constructor.
      apply IHm; try easy. lia.
    - subst.
      destruct m'; try easy.
      constructor.
      apply IHm; try easy. lia.
    - subst.
      destruct m'; try easy.
      constructor.
      apply IHm; try easy. lia.
    - subst.
      destruct m'; try easy.
      constructor.
      apply IHm; try easy. lia.
  Qed.
  
  Lemma cguardP_more_s : forall m m' n P, m <= m' -> cguardP n m P -> cguardP n m' P.
  Proof.
    intros.
    apply Nat.le_lteq in H; split_ors; 
    subst; eauto.
    eapply cguardP_more; eauto.
  Qed.
  
  Inductive reachP : fin -> process -> Prop :=
    | rp_end : forall n lz, reachP n (p_end lz) 
    | rp_send  : forall n pt l e P, reachP n (p_send pt l e P)
    | rp_recv  : forall n pt xs, reachP n (p_recv pt xs)
    | rp_ite   : forall n m m' e P Q, m < n -> m' < n -> reachP m P -> reachP m' Q -> reachP n (p_ite e P Q)
    | rp_rec   : forall n P, reachP n P -> reachP (S n) (p_rec P)
    | rp_newq : forall n P, reachP n (p_newq P)
    | rp_unitary : forall n n0 U lz P, reachP n (p_unitary n0 U lz P)
    | rp_measure : forall n z P, reachP n (p_measure z P).
    
  Lemma reachP_subst : forall P n x m m' Q,
    reachP n P -> reachP n (substitutionP x m m' Q P).
  Proof.
    induction P using process_deep_ind; intros.
    - inversion H.
    - simpl. constructor.
    - simpl. constructor.
    - simpl. constructor.
    - inversion H. subst.
      simpl.
      specialize(IHP1 m0 x m m' Q H6).
      specialize(IHP2 m'0 x m m' Q H7).
      apply rp_ite with (m := m0) (m' := m'0); try easy.
    - inversion H. subst.
      constructor. apply IHP; try easy.
    all: simpl; constructor.
  Qed.
  
  Lemma guard_to_reach : forall P xs, allfalse xs -> guardP xs P -> exists n, reachP n P.
  Proof.
    induction P using process_deep_ind; intros; try easy.
    - inversion H0. subst.
      clear H0. assert False.
      induction n; try easy.
      - destruct H; try easy.
      - destruct H; try easy.
      easy.
    - exists 0. constructor.
    - exists 0. constructor.
    - exists 0. constructor.
    - inversion H0. subst.
      specialize(allfalse_bmerge_break xs0 ys H); intros. destruct H1.
      specialize(IHP1 xs0 H1 H4). destruct IHP1 as (n, IHP1).
      specialize(IHP2 ys H2 H6). destruct IHP2 as (m, IHP2).
      exists (S (Nat.max n m)). apply rp_ite with (m := n) (m' := m); try easy; lia.
    - inversion H0.
      - subst. 
        specialize(IHP nil H H3). destruct IHP as (n, IHP).
        exists (S n). constructor. easy. 
      - subst.
        specialize(IHP (false :: xs)).
        assert(exists n : fin, reachP n P).
        {
          apply IHP; try easy.
        }
        destruct H1 as (n, H1). exists (S n). constructor. easy.
    all: exists 0; constructor.
  Qed.
  
  Lemma process_closedP_subst : forall P, process_closedP nil (p_rec P) -> process_closedP nil (substitutionP 0 0 0 (p_rec P) P).
  Proof.
    intros.
    specialize(process_closedP_to_PS nil (p_rec P) H); intros. clear H.
    specialize(process_closedPS_inv_rec [] (p_rec P) P); intros.
    assert(exists x : bool, process_closedPS [x] P). apply H; try easy.
    destruct H1 as (x, Ha). clear H.
    specialize(process_closedPS_subst P (p_rec P) nil x nil 0 0); intros.
    assert(process_closedPS nil (substitutionP 0 0 0 (p_rec P) P)).
    apply H; try easy. clear H.
    specialize(process_closedPS_to_P nil (substitutionP 0 0 0 (p_rec P) P) H1); intros.
    destruct H as (ys,(Hb,Hc)).
    destruct ys; try easy.
  Qed.
  
  Lemma guardP_subst : forall P, guardP nil (p_rec P) -> guardP nil (substitutionP 0 0 0 (p_rec P) P).
  Proof.
    intros.
    specialize(guardP_to_PS nil (p_rec P) H); intros. clear H.
    specialize(guardPS_inv_rec [] (p_rec P) P); intros.
    assert(guardPS [false] P). apply H; try easy.
    clear H.
    specialize(guardPS_subst P (p_rec P) nil false nil 0 0); intros.
    assert(guardPS nil (substitutionP 0 0 0 (p_rec P) P)).
    apply H; try easy. clear H.
    specialize(guardPS_to_P nil (substitutionP 0 0 0 (p_rec P) P) H2); intros.
    destruct H as (ys,(Hb,Hc)).
    destruct ys; try easy.
  Qed.
  
  (* Core normalization theorem:
     closed + guarded processes have quantitative guardedness bounds. *)
  Theorem closed_guard_to_cguard : forall P, process_closedP nil P -> guardP nil P -> (forall n : fin, exists m : fin, cguardP n m P).
  Proof.
    intros.
    revert H H0. revert P.
    induction n; intros.
    - exists 0. constructor.
    - specialize(guard_to_reach P nil); intros.
      assert(exists n : fin, reachP n P).
      {
        apply H1; try easy.
      }
      clear H1.
      destruct H2 as (m, Ha).
      revert IHn H H0 Ha. revert n P.
      
      induction m using strong_ind; intros.
      - inversion Ha.
        - subst. exists 0. constructor.
        - subst.
          inversion H0. subst.
          inversion H1. subst.
          specialize(guard_less_process_closedP P0 A nil H5 H4); intros.
          assert(A = nil).
          {
            destruct A; try easy.
          }
          subst.
          specialize(IHn P0 H4 H5).
          destruct IHn as (k, Hb).
          exists (S k). constructor. easy.
        - subst.
          inversion H0. subst.
          inversion H1. subst.
          clear Ha H0 H1 H.
          assert(SForall (fun u => exists m, cguardP n m u) xs).
          {
            revert H6 H4 H2.
            revert zs zs0. clear pt m.
            induction xs; intros; try easy.
            - destruct zs0; try easy.
              destruct zs; try easy.
              constructor.
              simpl in *. subst.
              inversion H4. subst. 
              inversion H6. subst. clear H6 H4.
              specialize(guard_less_process_closedP a l nil H2 H1); intros.
              destruct l; try easy.
              apply IHn; try easy.
            - destruct zs0; try easy.
              destruct zs; try easy.
              simpl in *.
              inversion H4. subst. 
              - inversion H6. subst. clear H6 H4.
                specialize(bmerge_nil x (bmergelis zs) H2); intros.
                destruct H. subst. clear H2.
                specialize(IHxs zs zs0 H9 H7 H0).
                constructor; try easy.
                specialize(guard_less_process_closedP y x0 nil H5 H3); intros.
                destruct x0; try easy.
                apply IHn; try easy.
              - subst.
                inversion H6. subst.
                constructor.
                apply IHxs with (zs := zs) (zs0 := zs0); try easy.
          }
          clear H6 H2 H4 IHn. clear zs zs0 m.
          revert H.
          induction xs; intros.
          - inversion H. subst.
            destruct H1 as (m, Ha).
            exists (S m). 
            constructor. constructor. easy.
          - inversion H. subst.
            destruct H2 as (m, Ha). clear H.
            specialize(IHxs H3).
            destruct IHxs as (m', Hb). clear H3.
            destruct m'; try easy.
            exists (S (Nat.max m m')).
            constructor. constructor.
            - apply cguardP_more_s with (m := m); try easy; lia.
            - inversion Hb. subst.
              revert H2.
              apply SForall_mono; intros.
              apply cguardP_more_s with (m := m'); try easy; lia.
          - subst.
            specialize(IHxs H1).
            destruct IHxs as (m, Ha). clear H H1.
            exists m.
            destruct m; try easy.
            constructor.
            inversion Ha. subst.
            constructor. easy.
        - subst.
          inversionc H1; cleanup.
          inversionc H0; cleanup.
          apply bmerge_nil in H6, H1; cleanup.
          edestruct (H m0); try apply H4; eauto.
          apply coq_nat_to_nat_le; lia.
          edestruct (H m'); try apply H5; eauto.
          apply coq_nat_to_nat_le; lia.
          clear IHn Ha.
          exists (S (Nat.max x x0)).
          constructor.
          - apply cguardP_more_s with (m := x); try easy; lia.
          - apply cguardP_more_s with (m := x0); try easy; lia.
        - subst.
          assert(is_true (ssrnat.leq (S n0) (S n0))). eauto.
          specialize (H n0 H3 n (substitutionP 0 0 0 (p_rec P0) P0) IHn).
          assert(exists m : fin,
          cguardP (S n) m (substitutionP 0 0 0 (p_rec P0) P0)).
          {
            apply H; try easy.
            - apply process_closedP_subst; try easy.
            - apply guardP_subst; try easy.
            - apply reachP_subst; try easy.
          }
          destruct H4 as (m, Hb).
          exists (S m).
          constructor; try easy.
      - subst.
          inversion H0. subst.
          inversion H1. subst.
          specialize(IHn P0 H4 H5).
          destruct IHn as (k, Hb).
          exists (S k). constructor. easy.
      - subst.
          inversion H0. subst.
          inversion H1. subst.
          sigT_eq.
          specialize(IHn P0 H4 H6).
          destruct IHn as (k, Hb).
          exists (S k). constructor. easy.
      - subst.
          inversion H0. subst.
          inversion H1. subst.
          specialize(IHn P0 H4 H5).
          destruct IHn as (k, Hb).
          exists (S k). constructor. easy.
  Qed.
  
  (* Standard well-formedness condition used by typing/session layers. *)
  Definition cguardedP P := process_closedP nil P /\ guardP nil P.

  Fixpoint mu_heightP (P : process) : fin := 
    match P with
      | p_rec _P => S (mu_heightP _P)
      | _        => 0
    end.
    
  Fixpoint muite_heightP (P : process) : fin := 
    match P with 
      | p_rec _P => S (muite_heightP _P)
      | p_ite e P1 P2 => S (Nat.max (muite_heightP P1) (muite_heightP P2))
      | _ => 0
    end. 
    
  Lemma mu_heightP_after_subst : forall P P' ys x n m, guardPS ys P -> nth x ys false = false -> mu_heightP P = mu_heightP (substitutionP x n m P' P).
  Proof.
    induction P; intros; try easy.
    - simpl.
      specialize(guardPS_inv_rec ys (p_rec P) P); intros.
      assert(guardPS (false :: ys) P). apply H1; try easy. clear H1 H.
      specialize(IHP P' (false :: ys) (S x) (S n)).
      assert(mu_heightP P = mu_heightP (substitutionP (S x) (S n) m P' P)).
      apply IHP; eauto. simpl. rewrite H. easy.
    - simpl.
      specialize(guardPS_inv_var ys (p_var n lz) n lz); intros.
      assert(bmerge (boollis n) ys = ys). apply H1; try easy. clear H1 H.
      assert(n =? x = false).
      revert H0 H2. clear n0 P'.
      revert n x.
      induction ys; intros; try easy.
      - destruct n; try easy.
      - destruct x; try easy.
        - simpl in H0. subst.
          destruct n; try easy.
        - simpl in H0.
          destruct n; try easy.
          inversion H2.
          specialize(IHys n x H0 H1). easy.
      rewrite H.
      case_analysis; eauto.  
  Qed.
  
  Lemma muite_heightP_after_subst : forall P P' ys x n m, guardPS ys P -> nth x ys false = false -> muite_heightP P = muite_heightP (substitutionP x n m P' P).
  Proof.
    induction P; intros; eauto.
    - simpl.
      specialize(guardPS_inv_rec ys (p_rec P) P); intros.
      assert(guardPS (false :: ys) P). apply H1; try easy. clear H1 H.
      specialize(IHP P' (false :: ys) (S x) (S n)).
      assert(muite_heightP P = muite_heightP (substitutionP (S x) (S n) m P' P)).
      apply IHP; try easy. simpl. rewrite H. easy.
    - simpl.
      specialize(guardPS_inv_ite ys (p_ite e P1 P2) e P1 P2); intros.
      assert(guardPS ys P1 /\ guardPS ys P2). apply H1; try easy. clear H1 H.
      destruct H2 as (Ha, Hb).
      specialize(IHP1 P' ys x n m). specialize(IHP2 P' ys x n m). fill_triv.
      rewrite IHP1. rewrite IHP2. easy.
    
    - simpl.
      specialize(guardPS_inv_var ys (p_var n lz) n lz); intros.
      assert(bmerge (boollis n) ys = ys). apply H1; try easy. clear H1 H.
      assert(n =? x = false).
      revert H0 H2. clear n0 P'.
      revert n x.
      induction ys; intros; try easy.
      - destruct n; try easy.
      - destruct x; try easy.
        - simpl in H0. subst.
          destruct n; try easy.
        - simpl in H0.
          destruct n; try easy.
          inversion H2.
          specialize(IHys n x H0 H1). easy.
      rewrite H; case_analysis; eauto.    
  Qed.
   
  Lemma mu_heightP_after_subst_s : forall P, guardPS nil (p_rec P) -> mu_heightP P = mu_heightP (substitutionP 0 0 0 (p_rec P) P).
  Proof.
    intros.
    specialize(guardPS_inv_rec nil (p_rec P) P); intros.
    assert(guardPS [false] P). apply H0; try easy. clear H0.
    apply mu_heightP_after_subst with [false]; try easy.
  Qed.
   
  Lemma muite_heightP_after_subst_s : forall P, guardPS nil (p_rec P) -> muite_heightP P = muite_heightP (substitutionP 0 0 0 (p_rec P) P).
  Proof.
    intros.
    specialize(guardPS_inv_rec nil (p_rec P) P); intros.
    assert(guardPS [false] P). apply H0; try easy. clear H0.
    apply muite_heightP_after_subst with [false]; try easy.
  Qed. 
  
  Lemma cguardedP_mu_rec : forall P, cguardedP (p_rec P) -> mu_heightP P = mu_heightP (substitutionP 0 0 0 (p_rec P) P).
  Proof.
    intros. apply mu_heightP_after_subst_s.
    unfold cguardedP in H. destruct H.
    apply guardP_to_PS. easy.
  Qed.
 
  Lemma cguardedP_muite_rec : forall P, cguardedP (p_rec P) -> muite_heightP P = muite_heightP (substitutionP 0 0 0 (p_rec P) P).
  Proof.
    intros. apply muite_heightP_after_subst_s.
    unfold cguardedP in H. destruct H.
    apply guardP_to_PS. easy.
  Qed. 
 
  (* One unfolding step for top-level recursion. *)
  Definition unfold_recP (P : process) : process := 
    match P with 
      | p_rec P' => substitutionP 0 0 0 (p_rec P') P'
      | _        => P
    end.
  
  (* Strong unfolding also resolves top-level conditionals when possible. *)
  Definition strong_unfold_recP (P : process) : process := 
    match P with 
      | p_rec P' => substitutionP 0 0 0 (p_rec P') P'
      | p_ite e P1 P2 => 
        match evaluate_expression e with
          | Some (Primitives.Bool true) => P1 
          | Some (Primitives.Bool false) => P2
          | _ => P1
        end
      | _ => P
    end.
  
  (* Bounded unfolding by recursion-height measure. *)
  Definition unravelP (P : process) : process := 
    iter (mu_heightP P) unfold_recP P.
    
  (* Bounded unfolding + top-level conditional elimination. *)
  Definition full_unravelP (P : process) : process := 
    iter (muite_heightP P) strong_unfold_recP P.
 
  
  Lemma cguardedP_after_subst : forall P P', cguardedP P -> precongP P P' -> cguardedP P'.
  Proof.
    intros.
    revert H.
    induction H0; intros. easy.
    apply IHprecongP.
    unfold cguardedP in *. clear IHprecongP H0.
    destruct H.
    split.
    - apply process_closedP_subst. easy.
    - apply guardP_subst. easy.
    - apply IHprecongP2. apply IHprecongP1. easy.
  Qed.
    
  Lemma cguardedP_unfolds : forall P, cguardedP P -> cguardedP (unravelP P) /\ precongP P (unravelP P) /\ ((exists lz, unravelP P = p_end lz) \/ (exists e p q, unravelP P = p_ite e p q) \/ (exists p l e q, unravelP P = p_send p l e q) \/ (exists p lis, unravelP P = p_recv p lis) 
  \/ (exists P', unravelP P = p_newq P') 
  \/ (exists n U lz P', unravelP P = p_unitary n U lz P')
  \/ (exists z P', unravelP P = p_measure z P')).
  Proof.
    intros.
    specialize(always_exists (mu_heightP P)); intros.
    destruct H0 as (n, Ha). revert H Ha. revert P.
    induction n; intros.
    - unfold unravelP. rewrite Ha. simpl.
      split. easy. split. constructor.
      unfold cguardedP in H. destruct H.
      destruct P; try solve [intuition eauto].
      - simpl in Ha. easy. 
      - inversion H. destruct n0; try easy.
    - destruct P; try easy. 
      simpl in Ha.
      specialize(cguardedP_after_subst (p_rec P) (substitutionP 0 0 0 (p_rec P) P)); intros.
      assert(cguardedP (substitutionP 0 0 0 (p_rec P) P)).
      {
        apply H0; try easy.
        constructor. constructor.
      }
      clear H0.
      specialize(cguardedP_mu_rec P H); intros.
      rewrite H0 in Ha.
      specialize(IHn (substitutionP 0 0 0 (p_rec P) P) H1 (eq_add_S (mu_heightP (substitutionP 0 0 0 (p_rec P) P)) n Ha)). 
      destruct IHn as (Hb,(Hc,Hd)).
      split.
      - clear Hc Hd H Ha.
        unfold unravelP in *. simpl. rewrite H0. easy.
      split.
      - apply gttS; try easy. 
        unfold unravelP in *. simpl. rewrite H0. easy.
      - unfold unravelP in *. simpl. rewrite H0. easy.
  Qed.
  
  
  Lemma cguardedP_after_ite : forall e P Q, cguardedP (p_ite e P Q) -> cguardedP P /\ cguardedP Q.
  Proof.
    intros.
    unfold cguardedP in *.
    destruct H.
    inversion H. subst.
    specialize(bmerge_nil xs ys H1); intros.
    destruct H2. subst. simpl in *.
    inversion H0. subst.
    specialize(bmerge_nil xs ys H2); intros.
    destruct H3. subst.
    simpl in *.
    easy. 
  Qed.

  Lemma cguardedP_after_send :  forall p l e P, cguardedP (p_send p l e P) -> cguardedP P.
  Proof.
    intros.
    unfold cguardedP in *.
    destruct H.
    inversion H. subst. inversion H0. subst.
    clear H H0.
    specialize(guard_less_process_closedP P A nil H4 H3); intros.
    destruct A; try easy.
  Qed.

  Lemma cguardedP_after_recv : forall p xs l y, cguardedP (p_recv p xs) -> onth l xs = Some y -> cguardedP y.
  Proof.
    intros p xs l. revert p xs.
    induction l; intros.
    - destruct xs; try easy.
      - inversion H0. subst.
        unfold cguardedP in *.
        destruct H.
        - inversion H. subst. destruct zs; try easy. destruct l; try easy.
          inversion H1. subst. destruct zs; try easy. inversion H6. subst.
          inversion H4. subst.
          simpl in *.
          specialize(guard_less_process_closedP y l nil H7 H8); intros.
          destruct l; try easy.
      - destruct o; try easy.
        simpl in H0. inversion H0. subst. clear H0.
        unfold cguardedP in *.
        destruct H.
        - inversion H. subst. destruct zs; try easy.
          inversion H3. subst. clear H3.
          inversion H0. subst. inversion H4. subst. clear H4.
          simpl in *. rewrite H1.
          specialize(bmerge_nil x (bmergelis zs) H1); intros. destruct H2. subst.
          specialize(guard_less_process_closedP y x0 nil H7 H6); intros.
          destruct x0; try easy.
    - destruct xs; try easy.
      apply IHl with p xs; try easy.
      clear H0 IHl.
      unfold cguardedP in *.
      destruct H.
      - inversion H. subst.
        inversion H0. subst.
        clear H H0. rewrite H1.
        inversion H3. 
        - subst. 
          simpl in *.
          inversion H5. subst. clear H5 H3.
          specialize(bmerge_nil x (bmergelis xs0) H1); intros. destruct H. subst.
          assert(process_closedP [] (p_recv p xs)).
          {
            symmetry in H0; rewrite H0. constructor. easy.
          }
          split. easy.
          apply gp_recv with xs1; try easy.
        - subst.
          simpl in *.
          inversion H5. subst. clear H5 H3.
          assert(process_closedP [] (p_recv p xs)).
          {
            symmetry in H1; rewrite H1. constructor. easy.
          }
          split. easy.
          apply gp_recv with xs1; try easy.
  Qed.
  
  Lemma cguardedP_strong_unfold : forall P, 
      cguardedP P -> cguardedP (strong_unfold_recP P).
  Proof.
    intros. destruct P; try easy; simpl in *.
    - specialize(cguardedP_after_subst); intros.
      apply H0 with (p_rec P); try easy. constructor. constructor.
    - specialize(cguardedP_after_ite e P1 P2); intros. fill_triv.
      destruct (evaluate_expression e); try easy. destruct v; try easy.
      destruct b; try easy.
  Qed.
  
  
  Lemma cguardedP_var_false : forall n lz, cguardedP (p_var n lz) -> False.
  Proof.
    intros. destruct H. inversion H. subst. clear H H0.
    induction n; try easy.
  Qed.
  
  Lemma fully_unfold_further : forall n m P1,
        ((exists lz, iter n strong_unfold_recP P1 = p_end lz) \/
         (exists p l e q,
            iter n strong_unfold_recP P1 = p_send p l e q) \/
         (exists p lis,
            iter n strong_unfold_recP P1 = p_recv p lis) \/
         (exists P,
            iter n strong_unfold_recP P1 = p_newq P) \/
         (exists n0 U lz P,
            iter n strong_unfold_recP P1 = p_unitary n0 U lz P) \/
         (exists z P,
            iter n strong_unfold_recP P1 = p_measure z P)) ->
        n <= m -> 
        iter n strong_unfold_recP P1 = iter m strong_unfold_recP P1.
  Proof.
    induction n; intros; simpl in *.
    - destruct H as [H | [H | [H | [H | [H | H]]]]].
      all: try solve [destruct_exists_and; subst;
        clear H0; induction m; intros; try easy].
    - destruct m; try easy.
      specialize(IHn m (strong_unfold_recP P1)). fill_triv. simpl in *.
      apply IHn; lia.
  Qed. 
    
  (* After sufficiently many strong-unfold steps, a guarded process reaches
     an observable head constructor (inact/send/recv), preserving guardedness. *)
  Lemma cguardedP_fully_unfolds : forall P, cguardedP P -> cguardedP (full_unravelP P) /\ ((exists lz, full_unravelP P = p_end lz) \/ (exists p l e q, full_unravelP P = p_send p l e q) \/ (exists p lis, full_unravelP P = p_recv p lis)\/
  (exists P',
    full_unravelP P = p_newq P') \/
  (exists n0 U lz P',
    full_unravelP P = p_unitary n0 U lz P') \/
  (exists z P',
    full_unravelP P = p_measure z P')).
  Proof.
    intro P. unfold full_unravelP.
    remember (muite_heightP P) as n. revert Heqn. revert P.
    induction n using strong_ind; intros.
    destruct n; try easy.
    - simpl in *. split. easy.
      destruct P; try solve [intuition (eauto; try easy)].
      - specialize(cguardedP_var_false n lz H0). easy.
    - simpl in *.
      destruct P; simpl in *; try easy.
      - assert(is_true (ssrnat.leq (S n) (S n))) by eauto.
        specialize(H n). fill_triv. specialize(H (substitutionP 0 0 0 (p_rec P) P)).
        apply H.
        - specialize(cguardedP_muite_rec P H0); intros. symmetry in H2; rewrite H2.
          apply eq_add_S; try easy.
        - specialize(cguardedP_after_subst); intros.
          apply H2 with (p_rec P); try easy. constructor. constructor.
      - pose proof H as Ha.
        specialize(H (muite_heightP P1)). specialize(Ha (muite_heightP P2)).
        specialize(eq_add_S n (Nat.max (muite_heightP P1) (muite_heightP P2)) Heqn); intros. subst. clear Heqn.
        specialize(cguardedP_after_ite e P1 P2 H0); intros. destruct H1. clear H0.
        assert(is_true
(ssrnat.leq (S (muite_heightP P1))
(S (Nat.max (muite_heightP P1) (muite_heightP P2))))). apply max_l.
        assert(is_true
(ssrnat.leq (S (muite_heightP P2))
(S (Nat.max (muite_heightP P1) (muite_heightP P2))))). apply max_r.
        fill_triv.
        specialize(H P1 (eq_refl (muite_heightP P1))).
        specialize(Ha P2 (eq_refl (muite_heightP P2))).
        fill_triv.
        destruct H. destruct Ha.
        (* unfolding further does not change anything *)
        specialize(fully_unfold_further (muite_heightP P1) (Nat.max (muite_heightP P1) (muite_heightP P2)) P1); intros.
        specialize(fully_unfold_further (muite_heightP P2) (Nat.max (muite_heightP P1) (muite_heightP P2)) P2); intros.
        fill_triv.
        assert(iter (muite_heightP P1) strong_unfold_recP P1 =
               iter (Nat.max (muite_heightP P1) (muite_heightP P2)) strong_unfold_recP P1). apply H7; lia. clear H7.
        assert(iter (muite_heightP P2) strong_unfold_recP P2 =
               iter (Nat.max (muite_heightP P1) (muite_heightP P2)) strong_unfold_recP P2). apply H8; lia.
               clear H8 H0 H3.
        split; eauto.
        symmetry in H9; symmetry in H7.
        repeat case_analysis.
        symmetry in H9; symmetry in H7.
         repeat case_analysis; cleanup; eauto.
  Qed.
        
  
  Lemma full_unravel_with_more : forall P1 n,
            cguardedP P1 -> 
            muite_heightP P1 <= n ->
            full_unravelP P1 = iter n strong_unfold_recP P1.
  Proof.
    intros.
    specialize(cguardedP_fully_unfolds P1); intros. fill_triv.
    specialize(fully_unfold_further (muite_heightP P1) n P1); intros. 
    unfold full_unravelP in *. destruct H1. fill_triv. easy.
  Qed.
  
    
End cguardP.

Section peq_w. 
  
  Inductive peq_w : process -> process -> Prop := 
    | peq_var : forall n lz lz', peq_w (p_var n lz) (p_var n lz')
    | peq_end : forall lz lz', peq_w (p_end lz) (p_end lz')
    | peq_send : forall pt lb e e' p1 p2, peq_w p1 p2 -> peq_w (p_send pt lb e p1) (p_send pt lb e' p2)
    | peq_recv : forall pt xs ys, SForall2 peq_w xs ys -> peq_w (p_recv pt xs) (p_recv pt ys)
    | peq_ite  : forall e1 p1 q1 e2 p2 q2, peq_w p1 p2 -> peq_w q1 q2 -> peq_w (p_ite e1 p1 q1) (p_ite e2 p2 q2)
    | peq_rec : forall p1 p2, peq_w p1 p2 -> peq_w (p_rec p1) (p_rec p2)
    | peq_newq : forall p1 p2, peq_w p1 p2 -> peq_w (p_newq p1) (p_newq p2)
    | peq_unitary : forall n n' U U' lz lz' p1 p2, peq_w p1 p2 -> peq_w (p_unitary n U lz p1) (p_unitary n' U' lz' p2)
    | peq_measure : forall z z' p1 p2, peq_w p1 p2 -> peq_w (p_measure z p1) (p_measure z' p2).

  Lemma peq_w_refl : forall P, 
  peq_w P P.
  Proof.
    induction P using process_deep_ind; intros;
    try solve [repeat case_analysis; simpl in *; cleanup; constructor; eauto].
    constructor.
    clear pt.
    induction llp;
    inversion H; cleanup; constructor; eauto.
  Qed.

  Lemma peq_w_subst_expr : forall P e m n, 
  peq_w P (subst_expression_in_process m n e P).
  Proof.
    induction P using process_deep_ind; intros;
    try solve [unfold subst_expression; simpl in *; repeat case_analysis; simpl in *; cleanup; constructor].
    simpl.
    - repeat case_analysis; simpl in *; cleanup; constructor.
    eapply (IHP e); eauto.
    { 
      generalize dependent m.
      generalize dependent n.
      generalize dependent e.
      generalize dependent pt.
      induction llp; intros.
      {
        inversion H; cleanup.
        repeat case_analysis; simpl in *; cleanup; repeat constructor; eauto; simpl.
      }
      {
        inversion H; cleanup.
        specialize (IHllp H3 pt e n m); clear H3.
        simpl in *.
        repeat constructor; eauto; simpl.
        inversion IHllp; cleanup; eauto.

        specialize (IHllp H1 pt e n m); clear H1.
        simpl in *.
        repeat constructor; eauto; simpl.
        inversion IHllp; cleanup; eauto.
      }
    } 
    {
      specialize (IHP1 e0 m);
      specialize (IHP2 e0 m);
       repeat case_analysis; simpl in *; cleanup; repeat constructor; eauto; simpl.
    }
    all: try solve [specialize (IHP e m);
    repeat case_analysis; simpl in *; cleanup; repeat constructor; eauto; simpl].
    all: try solve [specialize (IHP e (S m) (S n));
    repeat case_analysis; simpl in *; cleanup; repeat constructor; eauto; simpl].
  Qed.


  Lemma close_guard_with_peq : forall xs ys P Q, process_closedP xs P -> guardP ys P -> peq_w P Q -> process_closedP xs Q /\ guardP ys Q.
  Proof.
    intros xs ys P. revert xs ys.
    induction P using process_deep_ind; intros.
    all: try solve [inversion H1; subst;
      inversion H; subst; inversion H0; subst; split; constructor]. 
    - inversion H1. subst. clear H1.
      inversion H. subst. clear H. inversion H0. subst. clear H0.
      specialize(IHP xs A p2 H3 H2 H7).
      destruct IHP.
      split. constructor. easy.
      apply gp_send with A; try easy.
    - inversion H2. subst. clear H2.
      inversion H1. subst. clear H1.
      inversion H0. subst. clear H0.
      assert(SForall2 guardP zs ys0 /\ SForall2 process_closedP zs0 ys0).
      {
        revert H3 H4 H6 H. revert zs ys0 zs0.
        induction llp; intros.
        - inversion H. subst. clear H.
          inversion H3. subst. clear H3. inversion H4. subst. clear H4. inversion H6. subst. clear H6.
          specialize(H1 x x0 y H2 H3 H0).
          split.
          - constructor. easy.
          - constructor. easy.
        inversion H.
        - subst. clear H.
          inversion H3. subst. clear H3. inversion H4. subst. clear H4. inversion H6. subst. clear H6.
          specialize(IHllp xs0 ys xs H8 H9 H10 H5).
          clear H10 H9 H8 H5.
          specialize(H2 x0 x1 y H7 H3 H1). clear H1 H3 H7.
          split.
          - constructor; try easy. 
          - constructor; try easy.
        - subst. clear H.
          inversion H3. subst. clear H3. inversion H4. subst. clear H4. inversion H6. subst. clear H6.
          specialize(IHllp xs0 ys xs H2 H3 H0 H1).
          split.
          - constructor; try easy. 
          - constructor; try easy.
      }
      clear H3 H4 H6 H.
      destruct H0.
      split.
      - constructor. easy.
      - apply gp_recv with zs; try easy.
    - inversion H1. subst. 
      inversion H. subst. inversion H0. subst.
      specialize(IHP1 xs0 xs p2 H5 H8 H6).
      specialize(IHP2 ys0 ys1 q2 H9 H11 H7).
      split. constructor; try easy. constructor; try easy.
    - inversion H1. subst. clear H1.
      inversion H. subst.
      - inversion H0. subst.
        specialize(IHP nil nil p2 H4 H5 H3).
        split. constructor. easy. constructor. easy.
      - subst.
        specialize(IHP nil (false :: ys) p2 H4 H5 H3).
        split. constructor. easy.
        apply gp_rec1. easy.
      - subst. inversion H0. subst.
        specialize(IHP (x :: xs) nil p2 H4 H5 H3).
        split. apply cp_rec1 with x. easy.
        constructor. easy.
      - subst. 
        specialize(IHP (x :: xs) (false :: ys) p2 H4 H5 H3).
        split.
        apply cp_rec1 with x; try easy.
        apply gp_rec1. easy.
      - inversionc H1. inversionc H. inversionc H0.
      specialize(IHP xs ys p2 H4 H2 H3).
      destruct IHP.
      split. constructor. easy.
      apply gp_newq; try easy.
      - inversion H1. subst. clear H1.
      inversion H. subst. clear H. inversion H0. subst. clear H0.
      sigT_eq.
      specialize(IHP xs ys p2 H3 H2 H7).
      destruct IHP.
      split. constructor. easy.
      apply gp_unitary; try easy.
      - inversion H1. subst. clear H1.
      inversion H. subst. clear H. inversion H0. subst. clear H0.
      specialize(IHP xs ys p2 H3 H2 H5).
      destruct IHP.
      split. constructor. easy.
      apply gp_measure; try easy.
  Qed.

  Lemma cguardedP_after_subst_expr : forall P e m n,
      cguardedP P -> 
      cguardedP (subst_expression_in_process m n e P).
  Proof.
    intros. destruct H.
    apply close_guard_with_peq with P; try easy.
    eapply peq_w_subst_expr; eauto.
  Qed.

End peq_w.
