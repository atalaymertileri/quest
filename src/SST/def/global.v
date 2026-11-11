From mathcomp Require Import ssreflect.seq all_ssreflect.
Require Import List String Coq.Arith.PeanoNat Coq.Arith.Arith Relations ZArith Datatypes Setoid Morphisms Coq.Logic.Decidable Coq.Program.Basics Coq.Init.Datatypes.
Import ListNotations. 
Open Scope list_scope.
From Paco Require Import paco.
Require Import def.header def.tree.

(* Global type syntax and its coinductive interpretation as `gtt`.
   This file also develops guardedness/closedness criteria used to
   justify unfolding and translation from recursive syntax to trees. *)


Section global.

(* Syntactic global types with recursion variables (`g_var`). *)
Inductive global  : Type :=
  | g_var : fin -> global 
  | g_end : global 
  | g_send : participant -> participant -> slist (sort * global) -> global 
  | g_rec : global -> global.
  
(* Strong induction principle over `global` using structured branch traversal. *)
(* Induction principle that descends through all listed continuations. *)
Section global_ind_ref.
  Variable P : global -> Prop.
  Hypothesis P_var : forall n, P (g_var n).
  Hypothesis P_end : P (g_end).
  Hypothesis P_send : forall p q lis, SForall (fun u => P (snd u)) lis -> P (g_send p q lis).
  Hypothesis P_rec : forall g, P g -> P (g_rec g).
  
  Fixpoint global_ind_ref p : P p.
  Proof.
    destruct p.
    - apply P_var.
    - apply P_end.
    - apply P_send.
      induction s; try easy.
      constructor; try easy.
      destruct o.
      - constructor; try easy.
      - constructor; try easy.
    - apply P_rec. easy.
  Qed.
End global_ind_ref.


(* De Bruijn shift for free recursion variables in global syntax. *)
Fixpoint incr_freeG (fv m : fin) (G : global) := 
  match G with 
    | g_var n        => g_var (if fv <= n then (n + m) else n)
    | g_end          => g_end 
    | g_send p q lis => g_send p q (smap (fun u => (fst u, incr_freeG fv m (snd u))) lis)
    | g_rec g        => g_rec (incr_freeG (S fv) m g)
  end.
  
(* Capture-avoiding substitution for recursion variables. *)
Fixpoint substitutionG (x m : fin) (P Q : global) : global :=
    match Q with 
      | g_var k => match k with 
        | 0   => if Nat.eqb x 0 then (incr_freeG 0 m P) else g_var 0 
        | S k => if Nat.eqb x (S k) then (incr_freeG 0 m P) else  
                 if Nat.leb x (S k) then g_var k
                                    else g_var (S k)
        end
      | g_end => g_end
      | g_send p q Q'    => g_send p q (smap (fun u => (fst u, substitutionG x m P (snd u))) Q')
      | g_rec Q'         => g_rec (substitutionG (S x) (S m) P Q')
    end.

Inductive betaG : relation global := 
  | gttR : forall G, betaG G G
  | gttS : forall G G', betaG (substitutionG 0 0 (g_rec G) G) G' -> betaG (g_rec G) G'.


(* One-step generator for the coinductive relation from syntax (`global`)
   to semantic trees (`gtt`). *)
Inductive gttT (R : global -> gtt -> Prop) : global -> gtt -> Prop := 
  | gttT_end  : gttT R g_end gtt_end
  | gttT_send : forall p q xs ys, (forall n, (onth n xs = None /\ ys n = None) \/ (exists s g g', onth n xs = Some(s, g) /\ ys n = Some(s, g') /\ R g g')) -> gttT R (g_send p q xs) (gtt_send p q ys)
  | gttT_rec  : forall G G', gttT R (substitutionG 0 0 (g_rec G) G) G' -> gttT R (g_rec G) G'.

Definition gttTC G G' := paco2 gttT bot2 G G'.

Lemma gttT_mon : monotone2 gttT.
Proof.
  unfold monotone2. intros.
  induction IN; intros; try easy.
  - apply gttT_end.
  - apply gttT_send; try easy.
    intros. specialize(H n).
    destruct H.
    - left. easy.
    - right.
      destruct H as (s1,(g1,(g2,(Ha,(Hb,Hc))))).
      exists s1. exists g1. exists g2. split. easy. split. easy.
      apply LE; try easy.
  - apply gttT_rec; try easy.
Qed.



Definition regGtt (G : gtt) := exists G', gttTC G' G.

Lemma gttTC_after_beta : forall G G' Gl r, betaG G G' -> paco2 gttT r G' Gl -> paco2 gttT r G Gl.
Proof. 
  intros. revert H0. revert Gl r.
  induction H; intros; try easy.
  pfold. apply gttT_rec.
  specialize(IHbetaG Gl r H0). 
  punfold IHbetaG; try easy.
  apply gttT_mon.
Qed.

(* Exact closedness judgment for recursion variables in global syntax. *)
Inductive closedG : list bool -> global -> Prop :=
    | cg_var   : forall n, closedG (boollis n) (g_var n)
    | cg_end : closedG nil g_end
    | cg_send  : forall zs p q lis, SForall2 (fun u v => closedG u (snd v)) zs lis -> closedG (bmergelis zs) (g_send p q lis)
    | cg_rec0  : forall P, closedG nil P -> closedG nil (g_rec P)
    | cg_rec1  : forall P x xs, closedG (x :: xs) P -> closedG xs (g_rec P).
    
  (* Closure-friendly closedness with weakening rule `cgs_sub`. *)
  Inductive closedGS : list bool -> global -> Prop :=
    | cgs_var   : forall n, closedGS (boollis n) (g_var n)
    | cgs_inact : closedGS nil g_end
    | cgs_recv  : forall zs p  q ys, SForall (fun u => (closedGS zs) (snd u)) ys -> closedGS zs (g_send p q ys)
    | cgs_rec0  : forall P, closedGS nil P -> closedGS nil (g_rec P)
    | cgs_rec1  : forall P x xs, closedGS (x :: xs) P -> closedGS xs (g_rec P)
    | cgs_sub   : forall P xs ys, bmerge xs ys = ys -> closedGS xs P -> closedGS ys P.
  
  Lemma closedGS_inv_var : forall xs P n, closedGS xs P -> (P = g_var n) -> bmerge (boollis n) xs = xs.
  Proof.
    intros. revert H0. revert n.
    induction H; intros; try easy.
    - inversion H0. subst.
      clear H0.
      induction n0; try easy.
      simpl.
      rewrite IHn0. easy.
    - subst.
      specialize(IHclosedGS n (erefl (g_var n))).
      clear H0.
      revert IHclosedGS H.
      revert xs ys.
      induction n; intros; try easy.
      - destruct xs; try easy.
        destruct ys; try easy.
        inversion IHclosedGS. subst. inversion H. subst. simpl.
        assert(exists zs, bmerge xs ys = zs). exists (bmerge xs ys). easy.
        destruct H0 as (zs, H0). rewrite H0. destruct zs; try easy.
      - destruct xs; try easy.  
        destruct ys; try easy.
        inversion IHclosedGS. subst. inversion H. subst. simpl.
        specialize(IHn xs ys H1 H3).
        rewrite H3.
        rewrite IHn.
        easy.
  Qed.
        

  Lemma closedGS_inv_send : forall xs P p q ys, closedGS xs P -> (P = g_send p q ys) -> SForall (fun u => closedGS xs (snd u)) ys.
  Proof.
    intros.
    revert H0. revert ys p q.
    induction H; intros; try easy.
    - inversion H0. subst. easy.
    - subst.
      specialize(IHclosedGS ys0 p q).
      assert(SForall (fun u : sort * global => closedGS xs u.2) ys0). apply IHclosedGS; try easy.
      revert H1.
      apply SForall_mono; intros.
      apply cgs_sub with (xs := xs); try easy.
  Qed.
  
  Lemma closedGS_inv_rec : forall xs P P', closedGS xs P -> (P = g_rec P') -> exists x, closedGS (x :: xs) P'.
  Proof.
    intros. revert H0. revert P'.
    induction H; intros; try easy.
    - inversion H0. subst.
      exists true.
      apply cgs_sub with (xs := nil); try easy.
    - inversion H0. subst.
      exists x; try easy.
    - subst.
      specialize(IHclosedGS P').
      assert(exists x : bool, closedGS (x :: xs) P').
      apply IHclosedGS; try easy.
      destruct H1 as (x, H1).
      exists x.
      apply cgs_sub with (xs := x :: xs); try easy.
      simpl. rewrite H. 
      destruct x; try easy.
  Qed.
   
  Lemma closedGS_free : forall Q xl xr m, closedGS (xl ++ xr) Q -> closedGS (xl ++ (false_list m) ++ xr) (incr_freeG (length xl) m Q).
  Proof.
    induction Q using global_ind_ref; intros; try easy.
    - simpl.
      specialize(closedGS_inv_var (xl ++ xr) (g_var n) n); intros.
      assert(bmerge (boollis n) (xl ++ xr) = xl ++ xr). apply H0; try easy. clear H H0.
      case_eq ((length xl) <= n); intros.
      - revert H H1. 
        revert n xr m.
        induction xl; intros; try easy.
        - simpl in *.
          apply cgs_sub with (boollis (n + m)%coq_nat); try easy.
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
          apply cgs_sub with (boollis (n.+1 + m)%coq_nat); try easy.
          - simpl.
            specialize(closedGS_inv_var (xl ++ false_list m ++ xr) (g_var (n + m)%coq_nat) (n + m)%coq_nat); intros.
            assert(bmerge (boollis (n + m)%coq_nat) (xl ++ false_list m ++ xr) =
     xl ++ false_list m ++ xr).
            apply H0; try easy.
            rewrite H3. easy.
          - constructor.
      - revert H1 H.
        revert n xr m.
        induction xl; intros; try easy.
        destruct n; try easy.
        - inversion H1. subst.
          apply cgs_sub with (boollis 0); try easy.
          - simpl. destruct xl; try easy.
            destruct m; try easy. 
          - constructor.
        - inversion H1. subst.
          specialize(IHxl n xr m H2 H).
          specialize(closedGS_inv_var (xl ++ false_list m ++ xr) (g_var n) n); intros.
          assert(bmerge (boollis n) (xl ++ false_list m ++ xr) = xl ++ false_list m ++ xr).
          apply H0; try easy. clear H0 IHxl.
          apply cgs_sub with (boollis (S n)); try easy.
          - simpl. rewrite H3. easy.
          - constructor.
    - apply cgs_sub with nil; try easy.
      - destruct xl; try easy. destruct m; try easy. destruct xr; try easy.
      - constructor.
    - simpl. constructor.
      specialize(closedGS_inv_send (xl ++ xr) (g_send p q lis) p q lis); intros.
      assert(SForall (fun u : sort * global => closedGS (xl ++ xr) u.2) lis). apply H1; try easy. clear H1 H0.
      revert H2 H. clear p q. revert xl xr m.
      induction lis; intros; try easy.
      - inversion H. subst. clear H.
        inversion H2. subst. clear H2.
        constructor. apply H1; try easy.
      inversion H.
      - subst. clear H.
        inversion H2. subst. clear H2.
        specialize(IHlis xl xr m H5 H4). 
        constructor; try easy.
        apply H3; try easy.
      - subst. clear H.
        inversion H2. subst. clear H2.
        specialize(IHlis xl xr m H0 H1). 
        constructor; try easy.
    - simpl.
      specialize(closedGS_inv_rec (xl ++ xr) (g_rec Q) Q); intros.
      assert(exists x : bool, closedGS (x :: xl ++ xr) Q).
      apply H0; try easy. destruct H1 as (x, Ha). clear H H0.
      apply cgs_rec1 with (x := x); try easy.
      specialize(IHQ (x :: xl) xr m). apply IHQ; try easy.
  Qed.
  
  Lemma closedGS_remove_false : forall Q xs n, closedGS (xs ++ false_list n) Q -> closedGS xs Q.
  Proof.
    induction Q using global_ind_ref; intros; try easy.
    - specialize(closedGS_inv_var (xs ++ false_list n0) (g_var n) n); intros.
      assert(bmerge (boollis n) (xs ++ false_list n0) = xs ++ false_list n0).
      apply H0; try easy. clear H0 H.
      apply cgs_sub with (xs := (boollis n)); try easy.
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
    - apply cgs_sub with nil; try easy.
      - destruct xs; try easy.
      - constructor.
    - constructor.
      specialize(closedGS_inv_send (xs ++ false_list n) (g_send p q lis) p q lis); intros.
      assert(SForall (fun u : sort * global => closedGS (xs ++ false_list n) u.2) lis).
      apply H1; try easy. clear H1 H0.
      revert H H2.
      apply SForall_mono2; intros; try easy.
      apply H with (n := n); try easy.
    - specialize(closedGS_inv_rec (xs ++ false_list n) (g_rec Q) Q); intros.
      assert(exists x : bool, closedGS (x :: xs ++ false_list n) Q).
      apply H0; try easy.
      destruct H1 as (x, Ha).
      apply cgs_rec1 with (x := x); try easy.
      apply IHQ with (n := n); try easy.
  Qed.

  Lemma closedGS_freeS : forall Q m, closedGS nil Q -> closedGS nil (incr_freeG 0 m Q).
  Proof.
    intros.
    specialize(closedGS_free Q nil nil m H); intros.
    simpl in *.
    specialize(closedGS_remove_false (incr_freeG 0 m Q) nil m); intros.
    apply H1; try easy.
    clear H1 H.
    specialize(app_nil_r (false_list m)); intros.
    rewrite H in H0. easy.
  Qed.
  
  Lemma closedGS_subst : forall P Q xl xe xr m, closedGS (xl ++ [xe] ++ xr) P -> closedGS nil Q -> closedGS (xl ++ xr) (substitutionG (length xl) m Q P).
  Proof.
    induction P using global_ind_ref; intros; try easy.
    - specialize(closedGS_inv_var (xl ++ [xe] ++ xr) (g_var n) n); intros.
      assert(bmerge (boollis n) (xl ++ [xe] ++ xr) = xl ++ [xe] ++ xr).
      apply H1; try easy. clear H H1.
      simpl.
      destruct n.
      - destruct xl; try easy. 
        - simpl.
          apply cgs_sub with nil; try easy. destruct xr; try easy.
          apply closedGS_freeS; try easy.
        - simpl.
          inversion H2. subst.
          apply cgs_sub with (boollis 0); try easy.
          - simpl. destruct xl; try easy. destruct xr; try easy.
          - constructor.
      - case_eq (Nat.eqb (length xl) (S n)); intros.
        - apply cgs_sub with nil; try easy.
          - destruct xl; try easy.
          - clear H2 H.
            apply closedGS_freeS; try easy.
        case_eq (Nat.leb (length xl) (S n)); intros.
        - clear H0.
          revert H1 H H2. revert n xe xr. clear Q m.
          induction xl; intros; try easy.
          - inversion H2. simpl in *.
            rewrite H3.
            apply cgs_sub with (xs := (boollis n)); try easy.
            constructor.
          - destruct n; try easy.
            - destruct xl; try easy.
            - inversion H2. 
              specialize(IHxl n xe xr H1 H H3).
              clear H3 H2 H H1.
              specialize(closedGS_inv_var (xl ++ xr) (g_var n) n); intros.
              assert(bmerge (boollis n) (xl ++ xr) = xl ++ xr).
              apply H; try easy. clear H.
              apply cgs_sub with (boollis (S n)); try easy.
              - simpl. rewrite H0. easy.
              - constructor.
        - clear H.
          clear H0. clear Q m.
          assert(exists m, S n = m). exists (S n). easy. destruct H as (m, H).
          rewrite H in H1 H2. rewrite H. clear H. clear n. rename m into n.
          revert H1 H2. revert xl xe xr. 
          induction n; intros; try easy.
          - destruct xl; try easy. 
            inversion H2. subst.
            apply cgs_sub with (boollis 0); try easy.
            simpl. destruct xl; try easy. destruct xr; try easy.
            constructor.
          - destruct xl; try easy.
            inversion H2. 
            specialize(IHn xl xe xr H1 H0).
            specialize(closedGS_inv_var (xl ++ xr) (g_var n) n); intros.
            assert(bmerge (boollis n) (xl ++ xr) = xl ++ xr). apply H; try easy.
            clear H H0 H2 H1 IHn.
            apply cgs_sub with (boollis (S n)); try easy.
            - simpl. rewrite H3. easy.
            - constructor.
    - simpl.
      apply cgs_sub with (xs := nil); try easy.
      destruct xl; try easy. destruct xr; try easy.
      constructor.
    - simpl.
      constructor.
      specialize(closedGS_inv_send (xl ++ [xe] ++ xr) (g_send p q lis) p q lis); intros. 
      assert(SForall (fun u : sort * global => closedGS (xl ++ [xe] ++ xr) u.2) lis).
      apply H2; try easy. clear H2 H0.
      revert H3 H.
      induction lis; intros; try easy.
      - inversion H. subst. clear H.
        inversion H3. subst. clear H3.
        constructor.
        apply H2 with (xe := xe); try easy.
      inversion H.
      - subst. clear H.
        inversion H3. subst. clear H3.
        specialize(IHlis H6 H5). clear H6 H5.
        constructor; try easy.
        apply H4 with (xe := xe); try easy.
      - subst. clear H.
        inversion H3. subst. clear H3.
        specialize(IHlis H0 H2). clear H0 H2.
        constructor; try easy.
    - simpl.
      specialize(closedGS_inv_rec (xl ++ [xe] ++ xr) (g_rec P) P); intros.
      assert(exists x : bool, closedGS (x :: xl ++ [xe] ++ xr) P).
      apply H1; try easy. clear H1 H.
      destruct H2 as (x, Ha).
      apply cgs_rec1 with (x := x); try easy.
      specialize(IHP Q (x :: xl) xe xr). apply IHP; try easy.
  Qed.
  
  Lemma closedG_to_GS : forall xs P, closedG xs P -> closedGS xs P.
  Proof.
    intros xs P. revert xs.
    induction P using global_ind_ref; intros; try easy.
    - inversion H.
      constructor.
    - inversion H.
      constructor.
    - inversion H0. subst.
      clear H0.
      revert H3 H.
      revert p q zs.
      induction lis; intros; try easy.
      - inversion H3. subst. clear H3.
        inversion H. subst. clear H.
        constructor. constructor; try easy.
        apply H1; try easy.
      inversion H3.
      - subst. clear H3.
        inversion H. subst. clear H.
        specialize(IHlis p q xs H5 H3). clear H3.
        specialize(H2 x H4). clear H4.
        constructor.
        constructor.
        - apply cgs_sub with x; try easy. 
          simpl.
          specialize(bmerge_again_l x (bmergelis xs)); intros. easy.
        - clear H2.
          specialize(closedGS_inv_send (bmergelis xs) (g_send p q lis) p q lis); intros.
          assert(SForall (fun u : sort * global => closedGS (bmergelis xs) u.2) lis). apply H; try easy. clear H H5 IHlis.
          clear p q y.
          revert H0.
          apply SForall_mono; intros; try easy.
          apply cgs_sub with (bmergelis xs); try easy.
          simpl.
          apply bmerge_again_r; try easy.
      - subst. clear H3.
        inversion H. subst. clear H.
        specialize(IHlis p q xs H2 H1).
        specialize(closedGS_inv_send (bmergelis xs) (g_send p q lis) p q lis); intros.
          assert(SForall (fun u : sort * global => closedGS (bmergelis xs) u.2) lis). apply H; try easy.
        clear H H1 H2.
        constructor.
        constructor; try easy.
    - inversion H. subst.
      - apply cgs_rec0.
        apply IHP; try easy.
      - subst.
        apply cgs_rec1 with (x := x).
        apply IHP; try easy.
  Qed. 
        
  Lemma closedGS_to_G : forall xs P, closedGS xs P -> exists ys, bmerge ys xs = xs /\ closedG ys P.
  Proof.
    intros xs P. revert xs.
    induction P using global_ind_ref; intros; try easy.
    - specialize(closedGS_inv_var xs (g_var n) n); intros.
      assert(bmerge (boollis n) xs = xs). apply H0; try easy.
      clear H0.
      exists (boollis n).
      split. easy. constructor.
    - exists nil.
      split. destruct xs; try easy.
      constructor.
    - specialize(closedGS_inv_send xs (g_send p q lis) p q lis); intros.
      assert(SForall (fun u : sort * global => closedGS xs u.2) lis). apply H1; try easy. clear H1 H0.
      revert H H2. 
      revert xs p q.
      induction lis; intros.
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
        specialize(IHlis xs p q H5 H4). clear H5 H4.
        destruct IHlis as (ys,(Ha,Hb)).
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
        specialize(IHlis xs p q H2 H1). clear H2 H1.
        destruct IHlis as (ys,(Ha,Hb)).
        exists ys.
        split. easy.
        inversion Hb. subst.
        replace (bmergelis zs) with (bmergelis (slist_xs None zs)); try easy.
        constructor. constructor; try easy.
    - specialize(closedGS_inv_rec xs (g_rec P) P); intros.
      assert(exists x : bool, closedGS (x :: xs) P).
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
        apply cg_rec1 with (x := b); try easy.
  Qed.

  Lemma closedG_subst : forall P, closedG nil (g_rec P) -> closedG nil (substitutionG 0 0 (g_rec P) P).
  Proof.
    intros.
    specialize(closedG_to_GS nil (g_rec P) H); intros. clear H.
    specialize(closedGS_inv_rec [] (g_rec P) P); intros.
    assert(exists x : bool, closedGS [x] P). apply H; try easy.
    destruct H1 as (x, Ha). clear H.
    specialize(closedGS_subst P (g_rec P) nil x nil 0); intros.
    assert(closedGS nil (substitutionG 0 0 (g_rec P) P)).
    apply H; try easy. clear H.
    specialize(closedGS_to_G nil (substitutionG 0 0 (g_rec P) P) H1); intros.
    destruct H as (ys,(Hb,Hc)).
    destruct ys; try easy.
  Qed.
       
  (* Exact guardedness judgment: recursion variables must be guarded by
     communication constructors before use. *)
  Inductive guardG : list bool -> global -> Prop :=
    | gg_var   : forall n, guardG (boollis n) (g_var n)
    | gg_end : guardG nil g_end
    | gg_send  : forall p q ys zs, SForall2 (fun u v => guardG u (snd v)) zs ys -> guardG nil (g_send p q ys)
    | gg_rec0  : forall P, guardG nil P -> guardG nil (g_rec P)
    | gg_rec1  : forall P xs, guardG (false :: xs) P -> guardG xs (g_rec P).
  
  (* Witness form of "non-guardedness" used for contradiction arguments. *)
  Inductive nguardG : list (option fin) -> global -> Prop :=
    | ngg_init : forall P xs, guardG (true :: xs) P -> nguardG nil (g_rec P)
    | ngg_send : forall p q ys n s g w, onth n ys = Some(s, g) -> nguardG w g -> nguardG (Some n :: w) (g_send p q ys)
    | ngg_rec  : forall P w, nguardG w P -> nguardG (None :: w) (g_rec P).
    
  (* Closure-friendly guardedness with weakening rule `ggs_sub`. *)
  Inductive guardGS : list bool -> global -> Prop :=
    | ggs_var   : forall n, guardGS (boollis n) (g_var n)
    | ggs_inact : guardGS nil g_end
    | ggs_send  : forall p q ys zs, SForall2 (fun u v => guardGS u (snd v)) zs ys -> guardGS nil (g_send p q ys)
    | ggs_rec0  : forall P, guardGS nil P -> guardGS nil (g_rec P)
    | ggs_rec1  : forall P xs, guardGS (false :: xs) P -> guardGS xs (g_rec P)
    | ggs_sub   : forall P xs ys, bmerge xs ys = ys -> guardGS xs P -> guardGS ys P.
    
  
  Lemma guardGS_inv_var : forall xs P n, P = g_var n -> guardGS xs P -> bmerge (boollis n) xs = xs.
  Proof.
    intros. revert H. revert n.
    induction H0; intros; try easy.
    - inversion H. subst. 
      clear H.
      induction n0; try easy.
      simpl. rewrite IHn0. easy.
    - subst.
      specialize(IHguardGS n (erefl (g_var n))).
      clear H0.
      revert IHguardGS H.
      revert xs ys.
      induction n; intros; try easy.
      - destruct xs; try easy.
        destruct ys; try easy.
        simpl. 
        inversion IHguardGS. subst.
        inversion H. subst.
        rewrite H3.
        destruct ys; try easy.
      - destruct xs; try easy.
        destruct ys; try easy.
        inversion IHguardGS.
        inversion H.
        specialize(IHn xs ys H1 H3).
        simpl. rewrite H3. rewrite IHn.
        easy.
  Qed.
  
  Lemma guardGS_inv_send : forall xs P p q lis, (P = g_send p q lis) -> guardGS xs P -> exists ys, SForall2 (fun u v => guardGS u (snd v)) ys lis.
  Proof.
    intros.
    revert H. revert p q lis.
    induction H0; intros; try easy.
    - inversion H0. subst.
      exists zs. easy.
    - subst.
      specialize(IHguardGS p q lis).
      apply IHguardGS; try easy.
  Qed.
  
  Lemma guardGS_inv_rec : forall xs P Q, (P = g_rec Q) -> guardGS xs P -> guardGS (false :: xs) Q.
  Proof.
    intros.
    revert H. revert Q.
    induction H0; intros; try easy.
    - inversion H. subst.
      apply ggs_sub with nil; try easy.
    - inversion H. subst. easy.
    - subst.
      specialize(IHguardGS Q (erefl (g_rec Q))); intros.
      apply ggs_sub with (false :: xs); try easy.
      simpl. rewrite H. easy.
  Qed.
  
  Lemma guardGS_bmergeR : forall P xs ys, guardGS xs P -> guardGS ys P -> guardGS (bmergeR xs ys) P.
  Proof.
    induction P using global_ind_ref; intros.
    - specialize(guardGS_inv_var xs (g_var n) n (erefl (g_var n)) H); intros.
      specialize(guardGS_inv_var ys (g_var n) n (erefl (g_var n)) H0); intros.
      clear H H0.
      apply ggs_sub with (boollis n).
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
    - apply ggs_sub with nil.
      - destruct xs; try easy.
        - destruct ys; try easy.
        - destruct ys; try easy.
      - constructor.
    - specialize(guardGS_inv_send xs (g_send p q lis) p q lis); intros.
      assert(exists ys : slist (seq.seq bool),
       SForall2 (fun (u : seq.seq bool) (v : sort * global) => guardGS u v.2) ys lis).
      apply H2; try easy. clear H2. destruct H3 as (zs, H3).
      apply ggs_sub with nil; try easy.
      - destruct xs; try easy.
        - destruct ys; try easy.
        - destruct ys; try easy.
      - apply ggs_send with zs; try easy.
    - specialize(guardGS_inv_rec xs (g_rec P) P); intros.
      assert(guardGS (false :: xs) P). apply H1; try easy. clear H1.
      specialize(guardGS_inv_rec ys (g_rec P) P); intros.
      assert(guardGS (false :: ys) P). apply H1; try easy. clear H1.
      specialize(IHP (false :: xs) (false :: ys) H2 H3).
      apply ggs_rec1; try easy.
  Qed.
  
  Lemma guardGS_any_length : forall P xs n, guardGS xs P -> exists xl xe xr, length xl = n /\ guardGS (xl ++ [xe] ++ xr) P.
  Proof.
    induction P using global_ind_ref; intros; try easy.
    - specialize(guardGS_inv_var xs (g_var n) n); intros.
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
          - apply ggs_sub with (boollis 0); try easy.
            simpl. destruct n0; try easy.
            constructor.
        - destruct xs; try easy.
          inversion H1.
          specialize(IHn0 xs n H0).
          destruct IHn0 as (xl,(xe,(xr,(Ha,Hb)))).
          exists (false :: xl). exists xe. exists xr.
          split. simpl. rewrite Ha. easy.
          specialize(guardGS_inv_var (xl ++ [xe] ++ xr) (g_var n) n); intros.
          assert(bmerge (boollis n) (xl ++ [xe] ++ xr) = xl ++ [xe] ++ xr).
          apply H; try easy. clear H.
          apply ggs_sub with (boollis (S n)); try easy.
          - simpl. rewrite H2. easy.
          - constructor.
    - exists (false_list n). exists false. exists nil.
      clear H xs.
      split.
      - induction n; intros; try easy.
        simpl.
        rewrite IHn. easy.
      - apply ggs_sub with nil; try easy.
        - destruct n; try easy.
        - constructor.
    - clear H.
      exists (false_list n). exists false. exists nil.
      specialize(guardGS_inv_send xs (g_send p q lis) p q lis); intros.
      assert(exists ys : slist (seq.seq bool),
      SForall2 (fun (u : seq.seq bool) (v : sort * global) => guardGS u v.2) ys lis).
      apply H; try easy. clear H. destruct H1 as (ys, Ha).
      split.
      - clear Ha H0. clear p q lis xs ys.
        induction n; intros; try easy.
        simpl. rewrite IHn. easy.
      - apply ggs_sub with nil; try easy.
        - destruct n; try easy.
        - apply ggs_send with ys; try easy.
    - specialize(guardGS_inv_rec xs (g_rec P) P); intros.
      assert(guardGS (false :: xs) P). apply H0; try easy.
      clear H0 H.
      specialize(IHP (false :: xs) (S n) H1).
      destruct IHP as (xl,(xe,(xr,(Hb,Hc)))).
      destruct xl; try easy.
      exists xl. exists xe. exists xr.
      inversion Hb. split. easy.
      apply ggs_rec1; try easy.
      specialize(guardGS_bmergeR P (false :: xs) ((b :: xl) ++ [xe] ++ xr) H1 Hc); intros.
      apply ggs_sub with (bmergeR (false :: xs) ((b :: xl) ++ [xe] ++ xr)); try easy.
      clear H H0 H1 Hc Hb.
      simpl.
      specialize(bmergeR_back xs (xl ++ xe :: xr)); intros.
      rewrite H. easy.
  Qed.
  
  Lemma guardGS_free : forall Q xl xr m, guardGS (xl ++ xr) Q -> guardGS (xl ++ (false_list m) ++ xr) (incr_freeG (length xl) m Q).
  Proof.
    induction Q using global_ind_ref; intros; try easy.
    - simpl.
      specialize(guardGS_inv_var (xl ++ xr) (g_var n) n); intros.
      assert(bmerge (boollis n) (xl ++ xr) = xl ++ xr). apply H0; try easy. clear H H0.
      case_eq ((length xl) <= n); intros.
      - revert H H1. 
        revert n xr m.
        induction xl; intros; try easy.
        - simpl in *.
          apply ggs_sub with (boollis (n + m)%coq_nat); try easy.
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
          apply ggs_sub with (boollis (n.+1 + m)%coq_nat); try easy.
          - simpl.
            specialize(guardGS_inv_var (xl ++ false_list m ++ xr) (g_var (n + m)%coq_nat) (n + m)%coq_nat); intros.
            assert(bmerge (boollis (n + m)%coq_nat) (xl ++ false_list m ++ xr) =
     xl ++ false_list m ++ xr).
            apply H0; try easy.
            rewrite H3. easy.
          - constructor.
      - revert H1 H.
        revert n xr m.
        induction xl; intros; try easy.
        destruct n; try easy.
        - inversion H1. subst.
          apply ggs_sub with (boollis 0); try easy.
          - simpl. destruct xl; try easy.
            destruct m; try easy. 
          - constructor.
        - inversion H1. subst.
          specialize(IHxl n xr m H2 H).
          specialize(guardGS_inv_var (xl ++ false_list m ++ xr) (g_var n) n); intros.
          assert(bmerge (boollis n) (xl ++ false_list m ++ xr) = xl ++ false_list m ++ xr).
          apply H0; try easy. clear H0 IHxl.
          apply ggs_sub with (boollis (S n)); try easy.
          - simpl. rewrite H3. easy.
          - constructor.
    - apply ggs_sub with nil; try easy.
      - destruct xl; try easy. destruct m; try easy. destruct xr; try easy.
      - constructor.
    - simpl.
      specialize(guardGS_inv_send (xl ++ xr) (g_send p q lis) p q lis); intros.
      assert(exists ys : slist (seq.seq bool),
       SForall2 (fun (u : seq.seq bool) (v : sort * global) => guardGS u v.2) ys lis).
      apply H1; try easy.
      destruct H2 as (ys, Ha).
      clear H1 H0.
      apply ggs_sub with nil.
      - destruct xl; try easy. destruct m; try easy. destruct xr; try easy.
      revert Ha H. clear xr. 
      revert p q xl m ys.
      induction lis; intros; try easy.
      - inversion Ha. subst. clear Ha.
        inversion H. subst. clear H.
        specialize(guardGS_any_length a.2 x (length xl) H2); intros.
        destruct H as (xl0,(xe,(xr0,(Ha,Hb)))).
        specialize(H1 xl0 (xe :: xr0)).
        apply ggs_send with (zs := slist_x ((xl0 ++ false_list m ++ xe :: xr0))); try easy.
        constructor; try easy.
        rewrite (esym Ha).
        apply H1; try easy.
      inversion Ha.
      - subst. clear Ha.
        inversion H. subst. clear H.
        specialize(IHlis p q xl m xs H4 H5).
        clear H5 H4.
        specialize(guardGS_inv_send nil (g_send p q (smap (fun u : sort * global => (u.1, incr_freeG (length xl) m u.2)) lis)) p q (smap (fun u : sort * global => (u.1, incr_freeG (length xl) m u.2)) lis)); intros.
        assert(exists ys : slist (seq.seq bool),
      SForall2 (fun (u : seq.seq bool) (v : sort * global) => guardGS u v.2) ys
        (smap (fun u : sort * global => (u.1, incr_freeG (length xl) m u.2)) lis)).
        apply H; try easy.
        destruct H0 as (zs, Ha).
        clear H IHlis.
        specialize(guardGS_any_length y.2 x (length xl) H3); intros.
        destruct H as (xl0,(xe,(xr,(Hb,Hc)))).
        specialize(H2 xl0 (xe :: xr) m Hc).
        rewrite Hb in H2.
        apply ggs_send with (slist_xs (Some (xl0 ++ false_list m ++ xe :: xr)) zs).
        constructor; try easy.
      - subst. clear Ha.
        inversion H. subst. clear H.
        specialize(IHlis p q xl m xs H2 H1).
        clear H2 H1.
        specialize(guardGS_inv_send nil (g_send p q (smap (fun u : sort * global => (u.1, incr_freeG (length xl) m u.2)) lis)) p q (smap (fun u : sort * global => (u.1, incr_freeG (length xl) m u.2)) lis)); intros.
        assert(exists ys : slist (seq.seq bool),
      SForall2 (fun (u : seq.seq bool) (v : sort * global) => guardGS u v.2) ys
        (smap (fun u : sort * global => (u.1, incr_freeG (length xl) m u.2)) lis)).
        apply H; try easy.
        destruct H0 as (zs, Ha).
        clear H IHlis.
        apply ggs_send with (slist_xs None zs).
        constructor; try easy.
    - simpl.
      specialize(guardGS_inv_rec (xl ++ xr) (g_rec Q) Q); intros.
      assert(guardGS (false :: xl ++ xr) Q).
      apply H0; try easy. clear H0.
      specialize(IHQ (false :: xl) xr m H1).
      apply ggs_rec1; try easy.
  Qed.
  
  Lemma guardGS_remove_false : forall Q xs n, guardGS (xs ++ false_list n) Q -> guardGS xs Q.
  Proof.
    induction Q using global_ind_ref; intros; try easy.
    - specialize(guardGS_inv_var (xs ++ false_list n0) (g_var n) n); intros.
      assert(bmerge (boollis n) (xs ++ false_list n0) = xs ++ false_list n0).
      apply H0; try easy. clear H0 H.
      apply ggs_sub with (xs := (boollis n)); try easy.
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
    - apply ggs_sub with nil; try easy.
      - destruct xs; try easy.
      - constructor.
    - specialize(guardGS_inv_send (xs ++ false_list n) (g_send p q lis) p q lis); intros.
      assert(exists ys : slist (seq.seq bool),
       SForall2 (fun (u : seq.seq bool) (v : sort * global) => guardGS u v.2) ys lis).
      apply H1; try easy. clear H1 H0.
      destruct H2 as (ys, H2).
      apply ggs_sub with nil.
      - destruct xs; try easy.
      - apply ggs_send with ys; try easy.
    - specialize(guardGS_inv_rec (xs ++ false_list n) (g_rec Q) Q); intros.
      assert(guardGS (false :: xs ++ false_list n) Q).
      apply H0; try easy.
      apply ggs_rec1.
      apply IHQ with (n := n); try easy.
  Qed.
      
  Lemma guardGS_freeS : forall Q m, guardGS nil Q -> guardGS nil (incr_freeG 0 m Q).
  Proof.
    intros.
    specialize(guardGS_free Q nil nil m H); intros.
    simpl in *.
    specialize(guardGS_remove_false (incr_freeG 0 m Q) nil m); intros.
    apply H1; try easy.
    clear H1 H.
    specialize(app_nil_r (false_list m)); intros.
    rewrite H in H0. easy.
  Qed.
  
  Lemma guardGS_subst : forall P Q xl xe xr m, guardGS (xl ++ [xe] ++ xr) P -> guardGS nil Q -> guardGS (xl ++ xr) (substitutionG (length xl) m Q P).
  Proof.
    induction P using global_ind_ref; intros; try easy.
    - specialize(guardGS_inv_var (xl ++ [xe] ++ xr) (g_var n) n); intros.
      assert(bmerge (boollis n) (xl ++ [xe] ++ xr) = xl ++ [xe] ++ xr).
      apply H1; try easy.
      clear H1 H.
      simpl.
      destruct n.
      - destruct xl; try easy.
        - simpl.
          apply ggs_sub with nil; try easy.
          destruct xr; try easy.
          apply guardGS_freeS; try easy.
        - simpl.
          inversion H2.
          apply ggs_sub with (boollis 0).
          - simpl. destruct xl; try easy.
            destruct xr; try easy.
          - constructor.
      - case_eq (Nat.eqb (length xl) (S n)); intros.
        - apply ggs_sub with nil; try easy.
          - destruct xl; try easy.
          - apply guardGS_freeS; try easy.
        clear H0. clear m Q.
        case_eq (Nat.leb (length xl) (S n)); intros.
        - revert H0 H H2. revert xe xr n.
          induction xl; intros; try easy. 
          - inversion H2. 
            rewrite H3.
            apply ggs_sub with (boollis n); try easy.
            constructor.
          - destruct n; try easy.
            destruct xl; try easy.
            inversion H2.
            specialize(IHxl xe xr n H0 H H3).
            specialize(guardGS_inv_var (xl ++ xr) (g_var n) n); intros.
            assert(bmerge (boollis n) (xl ++ xr) = xl ++ xr).
            apply H1; try easy. clear H1 IHxl.
            apply ggs_sub with (boollis (S n)); try easy.
            - simpl. rewrite H4. easy.
            - constructor.
        - clear H.
          assert(exists m, S n = m).
          exists (S n). easy.
          destruct H as (m, Ha). rewrite Ha in H2 H0. rewrite Ha.
          clear Ha. clear n. rename m into n.
          revert H2 H0. revert n xe xr.
          induction xl; intros; try easy.
          destruct n; try easy.
          - inversion H2.
            apply ggs_sub with (boollis 0); try easy.
            - destruct xl; try easy. 
              destruct xr; try easy.
            - constructor.
          - inversion H2. 
            specialize(IHxl n xe xr H1 H0).
            specialize(guardGS_inv_var (xl ++ xr) (g_var n) n); intros.
            assert(bmerge (boollis n) (xl ++ xr) = xl ++ xr).
            apply H; try easy. clear H IHxl.
            apply ggs_sub with (boollis (S n)).
            - simpl. rewrite H3. easy.
            - constructor.
    - apply ggs_sub with nil; try easy.
      destruct xl; try easy. destruct xr; try easy.
      constructor.
    - apply ggs_sub with nil.
      - destruct xl; try easy. destruct xr; try easy.
      specialize(guardGS_inv_send (xl ++ [xe] ++ xr) (g_send p q lis) p q lis); intros.
      assert(exists ys : slist (seq.seq bool),
       SForall2 (fun (u : seq.seq bool) (v : sort * global) => guardGS u v.2) ys lis).
      apply H2; try easy. clear H2.
      destruct H3 as (ys, Ha). clear H0.
      revert H H1 Ha.
      revert Q xl m ys. clear xe xr.
      induction lis; intros; try easy.
      - inversion Ha. subst. clear Ha.
        inversion H. subst. clear H.
        simpl.
        specialize(guardGS_any_length a.2 x (length xl) H3); intros.
        destruct H as (xl0,(xe0,(xr0,(Ha,Hb)))).
        rewrite (esym Ha).
        apply ggs_send with (slist_x (xl0 ++ xr0)); try easy.
        constructor; try easy.
        apply H2 with (xe := xe0); try easy.
      inversion Ha.
      - subst. clear Ha.
        inversion H. subst. clear H.
        simpl in *.
        specialize(IHlis Q xl m xs H6 H1 H5).
        clear H6 H5.
        specialize(guardGS_inv_send nil (g_send p q (smap (fun u : sort * global => (u.1, substitutionG (length xl) m Q u.2)) lis)) p q (smap (fun u : sort * global => (u.1, substitutionG (length xl) m Q u.2)) lis)); intros.
        assert(exists ys : slist (seq.seq bool),
      SForall2 (fun (u : seq.seq bool) (v : sort * global) => guardGS u v.2) ys
        (smap (fun u : sort * global => (u.1, substitutionG (length xl) m Q u.2)) lis)).
        apply H; try easy. clear H.
        destruct H0 as (ys, Ha). clear IHlis.
        specialize(guardGS_any_length y.2 x (length xl) H4); intros.
        destruct H as (xl0,(xe0,(xr0,(Hb,Hc)))).
        apply ggs_send with (slist_xs (Some (xl0 ++ xr0)) ys).
        constructor; try easy.
        rewrite (esym Hb). apply H3 with (xe := xe0); try easy.
      - subst. clear Ha.
        inversion H. subst. clear H.
        simpl in *.
        specialize(IHlis Q xl m xs H2 H1 H3).
        simpl in *.
        specialize(guardGS_inv_send nil (g_send p q (smap (fun u : sort * global => (u.1, substitutionG (length xl) m Q u.2)) lis)) p q (smap (fun u : sort * global => (u.1, substitutionG (length xl) m Q u.2)) lis)); intros.
        assert(exists ys : slist (seq.seq bool),
      SForall2 (fun (u : seq.seq bool) (v : sort * global) => guardGS u v.2) ys
        (smap (fun u : sort * global => (u.1, substitutionG (length xl) m Q u.2)) lis)).
        apply H; try easy. clear H.
        destruct H0 as (ys, Ha). clear IHlis.
        apply ggs_send with (slist_xs None ys).
        constructor; try easy.
    - specialize(guardGS_inv_rec (xl ++ [xe] ++ xr) (g_rec P) P); intros.
      assert (guardGS (false :: xl ++ [xe] ++ xr) P).
      apply H1; try easy. clear H1.
      simpl.
      apply ggs_rec1.
      specialize(IHP Q (false :: xl) xe xr).
      apply IHP; try easy.
  Qed.
  
  Lemma guardG_to_GS : forall xs P, guardG xs P -> guardGS xs P.
  Proof.
    intros xs P. revert xs.
    induction P using global_ind_ref; intros; try easy.
    - inversion H.
      constructor.
    - inversion H.
      constructor.
    - inversion H0. subst.
      clear H0.
      revert H3 H.
      revert p q zs.
      induction lis; intros; try easy.
      - inversion H3. subst. clear H3.
        inversion H. subst. clear H.
        specialize(H1 x H2).
        apply ggs_send with (slist_x x).
        constructor. easy.
      inversion H3.
      - subst. clear H3.
        inversion H. subst. clear H.
        specialize(H2 x H4). clear H4.
        apply ggs_send with (slist_xs (Some x) xs).
        constructor; try easy.
        revert H3 H5. clear IHlis H2. clear p q x y.
        revert xs.
        induction lis; intros.
        - inversion H5. subst. clear H5.
          inversion H3. subst. clear H3.
          constructor. apply H0; try easy.
        inversion H5.
        - subst. clear H5.
          inversion H3. subst. clear H3.
          specialize(IHlis xs0 H5 H4).
          constructor; try easy.
          apply H1; try easy.
        - subst. clear H5.
          inversion H3. subst. clear H3.
          specialize(IHlis xs0 H0 H1).
          constructor; try easy.
      - subst. clear H3.
        inversion H. subst. clear H.
        apply ggs_send with (slist_xs None xs); try easy.
        constructor; try easy.
        revert H1 H2. 
        clear IHlis. clear p q. revert xs.
        induction lis; intros; try easy.
        - inversion H2. subst. clear H2.
          inversion H1. subst. clear H1.
          constructor. apply H0; try easy.
        inversion H2.
        - subst. clear H2.
          inversion H1. subst. clear H1.
          specialize(IHlis xs0 H3 H5).
          constructor; try easy.
          apply H2; try easy.
        - subst. clear H2.
          inversion H1. subst. clear H1.
          specialize(IHlis xs0 H0 H3).
          constructor; try easy.
    - inversion H. subst.
      - apply ggs_rec0.
        apply IHP; try easy.
      - subst.
        apply ggs_rec1.
        apply IHP; try easy.
  Qed. 
        
  Lemma guardGS_to_G : forall xs P, guardGS xs P -> exists ys, bmerge ys xs = xs /\ guardG ys P.
  Proof.
    intros xs P. revert xs.
    induction P using global_ind_ref; intros; try easy.
    - specialize(guardGS_inv_var xs (g_var n) n); intros.
      assert(bmerge (boollis n) xs = xs). apply H0; try easy.
      clear H0.
      exists (boollis n).
      split. easy. constructor.
    - exists nil.
      split. destruct xs; try easy.
      constructor.
    - specialize(guardGS_inv_send xs (g_send p q lis) p q lis); intros.
      assert(exists ys : slist (seq.seq bool),
       SForall2 (fun (u : seq.seq bool) (v : sort * global) => guardGS u v.2) ys lis). apply H1; try easy. clear H1 H0.
      destruct H2 as (ys, Ha).
      exists nil.
      split.
      - destruct xs; try easy.
      - revert Ha H. clear xs.
        revert ys.
        induction lis; intros; try easy.
        - inversion Ha. subst. clear Ha.
          inversion H. subst. clear H.
          specialize(H1 x H2).
          destruct H1 as (ys,(Ha,Hb)).
          apply gg_send with (slist_x ys); try easy.
          constructor; try easy.
        inversion Ha.
        - subst. clear Ha.
          inversion H. subst. clear H.
          specialize(IHlis xs H4 H5).
          inversion IHlis. subst.
          clear H5 H4.
          specialize(H2 x H3). destruct H2 as (ys,(Ha,Hb)).
          apply gg_send with (slist_xs (Some ys) zs).
          constructor; try easy.
        - subst. clear Ha.
          inversion H. subst. clear H.
          specialize(IHlis xs H2 H1).
          inversion IHlis. subst.
          clear H2 H1.
          apply gg_send with (slist_xs None zs).
          constructor; try easy.
    - specialize(guardGS_inv_rec xs (g_rec P) P); intros.
      assert(guardGS (false :: xs) P).
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
        apply gg_rec1; try easy.
        destruct b; try easy.
  Qed.
  
  Lemma guardG_subst : forall P, guardG nil (g_rec P) -> guardG nil (substitutionG 0 0 (g_rec P) P).
  Proof.
    intros.
    specialize(guardG_to_GS nil (g_rec P) H); intros. clear H.
    specialize(guardGS_inv_rec [] (g_rec P) P); intros.
    assert(guardGS [false] P). apply H; try easy.
    clear H.
    specialize(guardGS_subst P (g_rec P) nil false nil 0); intros.
    assert(guardGS nil (substitutionG 0 0 (g_rec P) P)).
    apply H; try easy. clear H.
    specialize(guardGS_to_G nil (substitutionG 0 0 (g_rec P) P) H2); intros.
    destruct H as (ys,(Hb,Hc)).
    destruct ys; try easy.
  Qed.
  
  Lemma guard_less_closedG : forall P xs ys, guardG xs P -> closedG ys P -> bmerge xs ys = ys.
  Proof.
    induction P using global_ind_ref; intros; try easy.
    - inversion H. subst.
      inversion H0. subst.
      clear H H0.
      induction n; intros; try easy.
      - simpl. 
        replace (bmerge (boollis n) (boollis n)) with (boollis n) in *. easy.
    - inversion H. subst.
      inversion H0. subst. easy.
    - inversion H0. subst.
      clear H H0 H1 H4. clear p q lis zs.
      induction ys; intros; try easy.
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
  Qed.

(* Canonical well-formedness condition for global syntax. *)
Definition cguardedG P := closedG nil P /\ guardG nil P.


  Lemma cguardedG_rec : forall G, cguardedG (g_rec G) -> cguardedG (substitutionG 0 0 (g_rec G) G).
  Proof.
    intros.
    unfold cguardedG in *. destruct H.
    split.
    apply closedG_subst. easy.
    apply guardG_subst. easy.
  Qed.

  Lemma cguardedG_cont : forall p q lis, cguardedG (g_send p q lis) -> SForall (fun u => cguardedG (snd u)) lis.
  Proof.  
    intros.
    unfold cguardedG in *.
    destruct H.
    inversion H. subst.
    inversion H0. subst.
    clear H H0. clear p q.
    revert H5 H1 H3. revert zs zs0.
    induction lis; intros.
    - destruct zs; try easy.
      destruct zs0; try easy.
      inversion H3. subst. clear H3.
      inversion H5. subst. clear H5.
      destruct l; try easy.
      specialize(guard_less_closedG a.2 l0 nil H3 H2); intros.
      destruct l0; try easy.
      constructor. simpl. easy.
    - destruct zs; try easy.
      destruct zs0; try easy.
      inversion H3.
      - subst. clear H3.
        inversion H5. subst. clear H5.
        simpl in H1. 
        specialize(bmerge_nil x (bmergelis zs) H1); intros. destruct H. subst.
        specialize(IHlis zs zs0 H8 H0 H7).
        simpl. rewrite H0. rewrite H0 in IHlis.
        - constructor; try easy.
          clear IHlis H8 H7 H1 H0. 
          specialize(guard_less_closedG y.2 x0 nil H3 H4); intros.
          destruct x0; try easy.
      - subst.
        clear H3.
        inversion H5. subst. clear H5.
        simpl in H1. 
        specialize(IHlis zs zs0 H2 H1 H0).
        simpl.
        constructor; try easy.
  Qed.

  
  Fixpoint mu_height (G : global) : fin := 
    match G with
      | g_rec _G => S (mu_height _G)
      | _        => 0
    end.
    
  Lemma mu_height_after_subst : forall G G' ys x n, guardGS ys G -> nth x ys false = false -> mu_height G = mu_height (substitutionG x n G' G).
  Proof.
    induction G; intros.
    - simpl.
      specialize(guardGS_inv_var ys (g_var n) n); intros. 
      assert(bmerge (boollis n) ys = ys). apply H1; try easy. clear H1 H.
      assert(x =? n = false).
      revert H0 H2. clear n0 G'.
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
      destruct n; try easy.
      - rewrite H. easy.
      - rewrite H. 
        case_eq (Nat.leb x (S n)); intros; try easy.
    - easy.
    - easy.
    - simpl.
      specialize(guardGS_inv_rec ys (g_rec G) G); intros.
      assert(guardGS (false :: ys) G). apply H1; try easy. clear H1 H.
      specialize(IHG G' (false :: ys) x.+1 n.+1).
      assert(mu_height G = mu_height (substitutionG x.+1 n.+1 G' G)).
      apply IHG; try easy. simpl. rewrite H. easy.
  Qed.
  
  Lemma mu_height_after_subst_s : forall G, guardGS nil (g_rec G) -> mu_height G = mu_height (substitutionG 0 0 (g_rec G) G).
  Proof.
    intros.
    specialize(guardGS_inv_rec nil (g_rec G) G); intros.
    assert(guardGS [false] G). apply H0; try easy. clear H0.
    apply mu_height_after_subst with [false]; try easy.
  Qed.
  
  Lemma cguardedG_mu_rec : forall G, cguardedG (g_rec G) -> mu_height G = mu_height (substitutionG 0 0 (g_rec G) G).
  Proof.
    intros. apply mu_height_after_subst_s.
    unfold cguardedG in H. destruct H.
    apply guardG_to_GS. easy.
  Qed.
 
  Definition unfold_recG (G : global) : global := 
    match G with 
      | g_rec G' => substitutionG 0 0 (g_rec G') G'
      | _        => G
    end.
    
  Definition unravelG (G : global) : global := 
    iter (mu_height G) unfold_recG G.
  
  (* Convert a guarded recursive syntax tree into a coinductive tree by
     bounded syntactic unfolding followed by coinductive reconstruction. *)
  CoFixpoint global_to_gtt (G : global) : gtt :=
    match unravelG G with 
      | g_send p q xs => gtt_send p q (fun n => match onth n xs with 
                                        | Some (s, g) => Some (s, global_to_gtt g)
                                        | None        => None
                                      end)
      | _     => gtt_end
    end.
    
  (* Finite unfolding preserves guardedness and yields either end or send form. *)
  Lemma cguardedG_unfolds : forall G, cguardedG G -> cguardedG (unravelG G) /\ betaG G (unravelG G) /\ (unravelG G = g_end \/ exists p q lis, unravelG G = g_send p q lis).
  Proof.
    intros.
    specialize(always_exists (mu_height G)); intros.
    destruct H0 as (n, Ha). revert H Ha. revert G.
    induction n; intros.
    - unfold unravelG. rewrite Ha. simpl.
      split. easy. split. constructor.
      unfold cguardedG in H. destruct H.
      destruct G.
      - inversion H. destruct n0; try easy.
      - left. easy.
      - right. exists p. exists p0. exists s. easy.
      - easy.
    - destruct G; try easy. 
      simpl in Ha.
      specialize(cguardedG_rec G H); intros.
      specialize(cguardedG_mu_rec G H); intros.
      rewrite H1 in Ha.
      specialize(IHn (substitutionG 0 0 (g_rec G) G) H0 (eq_add_S (mu_height (substitutionG 0 0 (g_rec G) G)) n Ha)).
      destruct IHn as (Hb,(Hc,Hd)).
      split.
      - clear Hc Hd H H0 Ha.
        unfold unravelG in *. simpl. rewrite H1. easy.
      split.
      - apply gttS; try easy.
        unfold unravelG in *. simpl. rewrite H1. easy.
      - unfold unravelG in *. simpl. rewrite H1. easy.
  Qed.
    
  (* Main soundness direction: guarded syntax has a coinductive tree
     interpretation related by `gttTC`. *)
  Theorem cguardedG_to_gtt : forall G, cguardedG G -> gttTC G (global_to_gtt G).
  Proof.
    pcofix CIH.
    induction G using global_ind_ref; intros.
    - unfold cguardedG in H0. destruct H0.
      inversion H0. destruct n0; try easy.
    - pfold. 
      rewrite (gtt_eq (global_to_gtt g_end)).
      unfold global_to_gtt. simpl. constructor.
    - pfold.
      rewrite (gtt_eq (global_to_gtt (g_send p q lis))).
      unfold global_to_gtt. simpl. constructor.
      intros.
      specialize(always_exists (onth n lis)); intros.
      destruct H1 as (b, Ha). rewrite Ha.
      destruct b.
      - right. destruct p0. exists s. exists g.
        exists ((cofix global_to_gtt (G : global) : gtt :=
        match unravelG G with
        | g_send p0 q0 xs =>
            gtt_send p0 q0
              (fun n0 : fin =>
               match onth n0 xs with
               | Some (s0, g0) => Some (s0, global_to_gtt g0)
               | None => None
               end)
        | _ => gtt_end
        end) g).
        split. easy. split. easy.
        specialize(cguardedG_cont p q lis H0); intros. clear H0.
        
        revert H1 H Ha. revert s g lis. clear p q.
        induction n; intros.
        - destruct lis; try easy.
          - inversion H1. subst. clear H1.
            inversion H. subst. clear H.
            simpl in Ha. destruct p. inversion Ha. subst. clear Ha.
            simpl in H1. 
            left. apply H1; try easy.
          inversion H1.
          - subst. clear H1.
            inversion H. subst. clear H.
            simpl in Ha. inversion Ha. subst. clear Ha.
            left. apply H2; try easy.
          - subst. simpl in Ha. inversion Ha.
        - destruct lis; try easy. simpl in Ha.
          specialize(IHn s g lis). 
          apply IHn; try easy.
          - inversion H1; try easy.
          - inversion H; try easy.
      - left. easy.
    - pfold.
      rewrite (gtt_eq (global_to_gtt (g_rec G))).
      clear IHG.
      simpl.
      
      specialize(cguardedG_unfolds (g_rec G) H0); intros.
      destruct H as (Ha,(Hb,Hc)).
      destruct Hc.
      - rewrite H. rewrite H in Ha Hb.
        
        specialize(gttTC_after_beta (g_rec G) g_end gtt_end r); intros.
        assert(paco2 gttT r (g_rec G) gtt_end).
        {
          apply H1; try easy.
          pfold. constructor.
        }
        punfold H2.
        apply gttT_mon.
      - destruct H as (p,(q,(lis,Hc))).
        rewrite Hc.
        rewrite Hc in Ha Hb.
        
        specialize(gttTC_after_beta (g_rec G) (g_send p q lis) (gtt_send p q
     (fun n : fin =>
      match onth n lis with
      | Some (s, g) => Some (s, global_to_gtt g)
      | None => None
      end)) r); intros.
        assert(paco2 gttT r (g_rec G)
      (gtt_send p q
         (fun n : fin =>
          match onth n lis with
          | Some (s, g) => Some (s, global_to_gtt g)
          | None => None
          end))).
        {
          apply H; try easy.
          clear H.
          pfold. constructor.
          specialize(cguardedG_cont p q lis Ha); intros. 
          clear Hc Ha Hb H0.
          specialize(always_exists (onth n lis)); intros.
          destruct H0 as (b,Ha). rewrite Ha.
          destruct b.
          - right. destruct p0.
            exists s. exists g. exists (global_to_gtt g).
            split. easy. split. easy.
            right. apply CIH.
            clear CIH p q G. clear r.
            revert Ha H. revert s g lis.
            induction n; intros.
            - destruct lis; try easy.
              - inversion Ha. subst.
                inversion H. subst. easy.
              inversion H.
              - subst. clear H.
                inversion Ha. subst.
                easy.
              - subst. clear H.
                inversion Ha.
            - destruct lis; try easy.
              specialize(IHn s g lis). apply IHn; try easy.
              inversion H; try easy.
          - left. easy.
        }
        punfold H1. 
        apply gttT_mon.
  Qed.
  
  
  Lemma dec_guard_nguardG : forall G, (exists xs, guardG xs G) \/ (exists w, nguardG w G).
  Proof.
    induction G using global_ind_ref; intros.
    - left. exists (boollis n). constructor.
    - left. exists nil. constructor.
    - induction lis; intros.
      - inversion H. subst.
        destruct H1.
        - left. exists nil.
          destruct H0 as (xs, Ha).
          apply gg_send with (zs := slist_x xs).
          constructor; try easy.
        - right.
          destruct H0 as (w, Ha). 
          destruct a.
          exists (Some 0 :: w).
          apply ngg_send with (n := 0) (s := s) (g := g); try easy.
      inversion H.
      - subst. clear H.
        specialize(IHlis H3). clear H3.
        destruct IHlis.
        - destruct H as (ys, Hb).
          destruct H2.
          - destruct H as (xs, Ha). destruct x.
            left.
            inversion Hb. subst. exists nil.
            apply gg_send with (slist_xs (Some xs) zs). 
            constructor; try easy.
          - destruct x.
            destruct H as (w, Ha). 
            right.
            exists (Some 0 :: w).
            apply ngg_send with (n := 0) (s := s) (g := g); try easy.
        - inversion H.
          - inversion H0.
          - subst.
            right.
            exists (Some (S n) :: w). 
            apply ngg_send with (n := S n) (s := s) (g := g); try easy.
      - subst. clear H.
        specialize(IHlis H1). clear H1.
        destruct IHlis.
        - destruct H as (xs, Ha).
          left. exists nil.
          inversion Ha. subst.
          apply gg_send with (slist_xs None zs).
          constructor; try easy.
        - right.
          inversion H. 
          - inversion H0.
          - subst.
            exists (Some (S n) :: w).
            apply ngg_send with (n := S n) (s := s) (g := g); try easy.
  - destruct IHG.
    - destruct H.
      destruct x.
      - left. exists nil. constructor. easy.
      destruct b.
      - right. exists nil. apply ngg_init with x; try easy. 
      - left. exists x. constructor. easy.
    - right. destruct H as (w, Ha). exists (None :: w). constructor. easy.
Qed.


Lemma dec_closedG : forall G, exists xs, closedG xs G.
Proof.
  induction G using global_ind_ref; intros.
  - exists (boollis n).
    constructor.
  - exists nil.
    constructor.
  - revert H.
    induction lis; intros.
    - inversion H. subst. clear H.
      destruct a. destruct H1 as (xs, Ha).
      exists xs.
      replace xs with (bmergelis (slist_x xs)); try easy.
      constructor. constructor; try easy.
    inversion H.
    - subst. clear H.
      specialize(IHlis H3). clear H3.
      destruct H2 as (xs, Ha).
      destruct IHlis as (ys, Hb). destruct x.
      inversion Hb. subst.
      exists (bmergelis (slist_xs (Some xs) zs)).
      constructor.
      constructor; try easy.
    - subst. clear H. 
      specialize(IHlis H1). clear H1.
      destruct IHlis as (ys, Hb). 
      inversion Hb. subst.
      exists (bmergelis (slist_xs None zs)).
      constructor.
      constructor; try easy.
  - destruct IHG.
    destruct x.
    - exists nil. constructor; try easy.
    - exists x. apply cg_rec1 with b; try easy.
Qed.
    

(* Path witness through global syntax with current recursion depth index. *)
Inductive global_path_c : list (option fin) -> fin -> global -> Prop :=
  | gpathc_init : forall n m, m <= n -> global_path_c nil m (g_var n)
  | gpathc_send : forall p q xs n s g w m, onth n xs = Some(s, g) -> global_path_c w m g -> global_path_c (Some n :: w) m (g_send p q xs)
  | gpathc_mu   : forall w m g, global_path_c w (S m) g -> global_path_c (None :: w) m (g_rec g).

Lemma bmerge_split_app : forall xs ys xl xr, bmerge xs ys = xl ++ xr -> exists xl0 xr0, length xl0 = length xl /\ length xr0 = length xr /\ (xs = xl0 ++ xr0 \/ ys = xl0 ++ xr0).
Proof.
  induction xs; intros.
  - exists xl. exists xr.
    split. easy. split. easy.
    right. destruct ys; try easy.
  - destruct ys.
    - exists xl. exists xr.
      split. easy. split. easy.
      left.
      easy.
    - destruct xl.
      - exists nil.
        destruct xr; try easy.
        inversion H. subst. 
        specialize(IHxs ys nil (bmerge xs ys) (erefl (bmerge xs ys))).
        destruct IHxs as (xa,(xb,(Ha,(Hb,Hc)))).
        destruct xa; try easy.
        destruct Hc.
        - subst.
          exists (a :: xb).
          split. easy. split. simpl. rewrite Hb. easy.
          left. easy.
        - subst.
          simpl in *.
          exists (b :: xb).
          split. easy.
          split. simpl. rewrite Hb. easy.
          right. easy.
      - inversion H. subst.
        specialize(IHxs ys xl xr H2).
        destruct IHxs as (xa,(xb,(Ha,(Hb,Hc)))).
        destruct Hc.
        simpl in *.
        - subst.
          exists (a :: xa). exists xb.
          split. simpl. rewrite Ha. easy.
          split. easy.
          left. easy.
        - subst.
          exists (b :: xa). exists xb.
          split. simpl. rewrite Ha. easy.
          split. easy.
          right. easy.
Qed.

Lemma closedG_to_path : forall G xl xr, xr <> nil -> closedG (xl ++ xr) G -> exists w, global_path_c w (length xl) G.
Proof.
  induction G using global_ind_ref; intros.
  - inversion H0. subst. clear H0.
    exists nil. constructor. revert H2. revert n.
    induction xl; intros.
    - easy.
    - destruct n; try easy.
      - destruct xl; try easy. destruct xr; try easy.
      - inversion H2. subst.
        specialize(IHxl n H3). easy.
  - inversion H0.
    destruct xl; try easy. destruct xr; try easy.
  - inversion H1. subst. clear H1.
    revert H H0 H4 H2. revert xl xr zs.
    induction lis; intros.
    - inversion H4. subst. clear H4.
      inversion H. subst. clear H.
      simpl in H2. subst.
      specialize(H3 xl xr H0 H5).
      destruct H3 as (w,Ha).
      exists (Some 0 :: w).
      destruct a.
      apply gpathc_send with (s := s) (g := g); try easy.
    inversion H4.
    - subst. clear H4. 
      inversion H. subst. clear H.
      simpl in H2.
      specialize(bmerge_split_app x (bmergelis xs) xl xr H2); intros.
      destruct H as (xa,(xb,(Ha,(Hb,Hc)))).
      destruct Hc.
      - subst.
        specialize(H4 xa xb).
        assert(exists w : seq.seq (option fin), global_path_c w (length xa) y.2).
        {
          apply H4; try easy.
          destruct xb; try easy. destruct xr; try easy.
        }
        destruct H as (w,Hd).
        exists (Some 0 :: w). destruct y.
        apply gpathc_send with (s := s) (g := g); try easy.
        rewrite Ha in Hd. easy.
      - clear H2 H6 H4.
        specialize(IHlis xa xb xs).
        assert(exists w : seq.seq (option fin), global_path_c w (length xa) (g_send p q lis)).
        {
          apply IHlis; try easy.
          destruct xb; try easy. destruct xr; try easy.
        }
        destruct H1 as (w,Hd).
        inversion Hd. subst.
        exists (Some (S n) :: w0).
        apply gpathc_send with (s := s) (g := g); try easy.
        rewrite Ha in H9. easy.
    - subst. clear H4.
      inversion H. subst. clear H.
      simpl in H2.
      specialize(IHlis xl xr xs H3 H0 H5 H2).
      destruct IHlis as (w,Ha). clear H2 H5 H3.
      inversion Ha. subst. clear Ha.
      exists (Some (S n) :: w0).
      apply gpathc_send with (s := s) (g := g); try easy.
  - inversion H0.
    - subst. 
      destruct xl; try easy. destruct xr; try easy.
    - subst.
      specialize(IHG (x :: xl) xr H H3).
      destruct IHG as (w, Ha).
      exists (None :: w).
      constructor. easy.
Qed.

Lemma global_path_c_after_subst : forall G w c x G' m, x <= c -> global_path_c w (S c) G -> global_path_c w c (substitutionG x m G' G).
Proof.
  induction G using global_ind_ref; intros.
  - inversion H0. subst.
    simpl.
    specialize(leq_ltn_trans H H4); intros.
    destruct n.
    - destruct x; try easy.
    - case_eq (Nat.eqb x (S n)); intros.
      - specialize(Nat.eqb_eq x (S n)); intros.
        rewrite H3 in H2. subst.
        specialize(ltnn n.+1); intros. rewrite H1 in H2. easy.
      case_eq (Nat.leb x (S n)); intros.
      - constructor. easy.
      - constructor.
        apply ltnW. easy.
  - inversion H0.
  - inversion H1. subst.
    specialize(SForall_onth n lis (fun u : sort * global =>
       forall (w : seq.seq (option fin)) (c x : fin) (G' : global) (m : fin),
       x <= c -> global_path_c w c.+1 u.2 -> global_path_c w c (substitutionG x m G' u.2)) (s, g) H H6); intros. simpl in H2.
    specialize(H2 w0 c x G' m).
    apply gpathc_send with (n := n) (s := s) (g := (substitutionG x m G' g)); try easy.
    - clear H2 H8 H1 H0 H.
      revert H6. revert lis.
      induction n; intros.
      - destruct lis; try easy.
        - inversion H6. subst.
          simpl. easy.
        - simpl in H6. subst. simpl. easy.
      - destruct lis; try easy.
        specialize(IHn lis H6). 
        rewrite (esym IHn). destruct o; try easy.
    - apply H2; try easy.
  - inversion H0. subst.
    simpl. constructor.
    apply IHG; try easy.
Qed.
      
Lemma gttT_closed_nil : forall G G' xs, gttTC G G' -> closedG xs G -> xs = nil.
Proof.
  intros.
  destruct xs; try easy.
  specialize(closedG_to_path G nil (b ::xs)); intros.
  assert(exists w : seq.seq (option fin), global_path_c w 0 G).
  apply H1; try easy. clear H1 H0.
  destruct H2 as (w,Ha). 
  specialize(always_exists 0); intros. destruct H0 as (c, Hb).
  rewrite Hb in Ha. clear Hb.
  assert False.
  {
    revert Ha H. revert c G G'. clear b xs.
    induction w; intros.
    - inversion Ha. subst.
      pinversion H.
      apply gttT_mon.
    - inversion Ha.
      - subst.
        pinversion H. subst. clear H.
        specialize(H6 n). rewrite H2 in H6.
        destruct H6; try easy. destruct H as (s1,(g1,(g2,(Hb,(Hc,Hd))))).
        inversion Hb. subst. clear Hb. pclearbot. 
        specialize(IHw c g1 g2). apply IHw; try easy.
        apply gttT_mon.
      - subst.
        pinversion H. subst.
        specialize(IHw c (substitutionG 0 0 (g_rec g) g) G').
        apply IHw; try easy.
        apply global_path_c_after_subst; try easy.
        pfold. easy.
        apply gttT_mon.
  }
  easy.
Qed.


(* Lemma gttTC_first : forall G n, gttTC (g_rec (g_var n)) G -> False.
Proof.
  intros.
  pinversion H. subst. simpl in *.
  clear H1.
  remember (g_rec (g_var n)) as one eqn:Hone. revert Hone. revert n.  
  induction H; intros; try easy.
  inversion Hone. subst. simpl in IHgttT.
  destruct n.
  - specialize(IHgttT 0). apply IHgttT. easy.
  - simpl in H. inversion H.
  apply gttT_mon.
 *)


Lemma guardG_only_boollis : forall G xs, xs <> nil -> guardG xs G -> exists n, xs = boollis n.
Proof.
  intros. revert H.
  induction H0; intros; try easy.
  - exists n. easy.
  - assert(exists n : fin, false :: xs = boollis n).
    apply IHguardG; try easy. destruct H1 as (n,Ha).
    destruct n; try easy.
    exists n. inversion Ha. easy.
Qed.


Lemma nguardG_canon : forall G, nguardG nil G -> exists G', G = g_rec G' /\ guardG [true] G'.
Proof.  
  intros. inversion H. subst. clear H.
  specialize(guardG_only_boollis P (true :: xs)); intros.
  assert(exists n : fin, true :: xs = boollis n).
  apply H; try easy.
  destruct H1 as (n, Ha). clear H.
  destruct n; try easy. destruct xs; try easy. clear Ha.
  exists P. easy.
Qed.

(* Shape predicate: term consists only of nested recursion over a variable. *)
Inductive only_rec : global -> Prop := 
  | rec_nil : forall n, only_rec (g_rec (g_var n))
  | rec_app : forall G, only_rec G -> only_rec (g_rec G).

Lemma guardG_nonempty_to_rec : forall G xs, xs <> nil -> guardG xs G -> only_rec (g_rec G).
Proof.
  intros. revert H.
  induction H0; intros; try easy.
  - constructor.
  - constructor. apply IHguardG. easy.
Qed.

Lemma nguardG_only_rec : forall G, nguardG nil G -> only_rec G.
Proof.
  intros.
  specialize(nguardG_canon G H); intros.
  destruct H0 as (Gl,(Ha,Hb)). subst.
  specialize(guardG_nonempty_to_rec Gl [true]); intros.
  apply H0; try easy.
Qed.

Lemma only_rec_closed_less_guard : forall G xs ys, only_rec G -> closedG xs G -> guardG ys G -> bmerge xs ys = ys.
Proof. 
  induction G using global_ind_ref; intros; try easy.
  inversion H.
  - subst.  
    inversion H0. subst.
    - destruct ys; try easy.
    - subst. clear H0.
      inversion H1; try easy.
      - subst. inversion H3. destruct n0; try easy.
      - subst. inversion H4. subst.
        inversion H3. subst. clear H4 H3 IHG H1 H.
        destruct n; try easy. inversion H2. subst.
        inversion H5. subst. clear H2 H5.
        induction n; intros; try easy.
        simpl. rewrite IHn. easy.
  - subst.
    inversion H0. subst.
    - destruct ys; try easy.
    - subst. clear H0.  
      inversion H1; try easy.
      - subst.
        specialize(IHG (x :: xs) nil H3 H5 H4).
        inversion IHG.
      - subst.
        specialize(IHG (x :: xs) (false :: ys) H3 H5 H4).
        inversion IHG. rewrite H6. easy.
Qed.

Lemma nguardG_closed : forall G, nguardG nil G -> closedG nil G.
Proof.
  intros.
  specialize(nguardG_only_rec G H); intros.
  specialize(nguardG_canon G H); intros.
  destruct H1 as (Gl,(Ha,Hb)). subst. clear H.
  specialize(dec_closedG Gl); intros. destruct H as (xs,Ha).
  inversion H0.
  - subst.
    inversion Hb. destruct n0; try easy. subst.
    inversion Ha. subst.
    apply cg_rec1 with true.
    rewrite (esym H1). constructor.
  - subst.
    specialize(only_rec_closed_less_guard Gl xs [true] H1 Ha Hb); intros.
    destruct xs; try easy.
    - constructor; try easy.
    - apply cg_rec1 with b. destruct xs; try easy.
Qed.

Lemma nguardG_subst_same_helper : forall G xs x m G', closedG xs G -> only_rec G -> length xs <= x -> G = substitutionG x m G' G.
Proof.
  induction G using global_ind_ref; intros.
  - inversion H0.
  - inversion H0.
  - inversion H1.
  - simpl.
    inversion H0.
    - subst.
      inversion H.
      - subst.
        inversion H4. destruct n0; try easy.
      - subst.
        inversion H4. subst.
        simpl. destruct n; try easy.
        clear IHG H0 H.
        inversion H3. subst.
        assert(length (boollis n) = S n).
        {
          clear H4 H3 H1.
          induction n; intros; try easy.
          simpl. rewrite IHn. easy.
        }
        rewrite H in H1.
        case_eq (Nat.eqb x n); intros.
        - specialize(Nat.eqb_eq x n); intros.
          rewrite H2 in H0. subst. clear H2 H3 H H4. 
          assert False.
          induction n; intros; try easy. easy.
        case_eq (Nat.leb x n); intros; try easy.
        - clear H4 H3 H H0. assert False. 
          revert H1 H2. revert x.
          induction n; intros; try easy.
          - destruct x; try easy.
          - destruct x; try easy.
            apply IHn with x; try easy.
          easy.
    - subst.
      assert(G = (substitutionG x.+1 m.+1 G' G)).
      clear H0.
      inversion H.
      - subst.
        specialize(IHG nil x.+1 m.+1 G' H4 H3).
        apply IHG; try easy.
      - subst.
        apply IHG with (x0 :: xs); try easy.
      rewrite (esym H2). easy.
Qed.

Lemma nguardG_subst_same : forall G x m G', nguardG nil G -> G = substitutionG x m G' G.
Proof.
  intros.
  specialize(nguardG_only_rec G H); intros.
  specialize(nguardG_closed G H); intros. 
  clear H.
  apply nguardG_subst_same_helper with nil; try easy.
Qed.


Lemma only_rec_incr_freeG : forall G m n, only_rec G -> only_rec (incr_freeG m n G).
Proof.
  induction G using global_ind_ref; intros; try easy.
  inversion H.
  - subst. simpl. constructor.
  - subst. simpl. constructor. apply IHG; try easy.
Qed.

Lemma only_rec_subst : forall G G' x m, only_rec G -> only_rec G' -> only_rec (substitutionG x m G' G).
Proof.
  induction G using global_ind_ref; intros; try easy.
  simpl.
  inversion H.
  - subst.
    clear IHG H. simpl.
    destruct n.
    - constructor.
    - case_eq (Nat.eqb x n); intros. constructor.
      apply only_rec_incr_freeG; try easy.
      case_eq (Nat.leb x n); intros; try easy.
      constructor. constructor.
  - subst. constructor.
    apply IHG; try easy.
Qed.

Lemma only_rec_gttT_false : forall G G', only_rec G -> gttTC G G' -> False.
Proof.
  intros.
  punfold H0.
  revert H.
  induction H0; intros.
  - inversion H.
  - inversion H0.
    inversion H.
    - subst.
      simpl in *.
      destruct n.
      - apply IHgttT; try easy.
      - inversion H0.
    - subst.
      apply IHgttT.
      clear H0 IHgttT.
      specialize(only_rec_subst G (g_rec G) 0 0); intros.
      apply H0; try easy.
  apply gttT_mon.
Qed.

Lemma nguardG_gttT_false : forall G Gl, nguardG nil G -> gttTC G Gl -> False.
Proof.
  intros.
  apply only_rec_gttT_false with G Gl; try easy.
  apply nguardG_only_rec; try easy.
Qed.


Lemma nguardG_subst : forall w G x m G', nguardG w G -> nguardG w (substitutionG x m G' G).
Proof.
  induction w; intros.
  - specialize(nguardG_subst_same G x m G' H); intros. rewrite (esym H0). easy.
  - inversion H. 
    - subst. simpl.
      apply ngg_send with (s := s) (g := substitutionG x m G' g); try easy.
      clear H4 H IHw. 
      revert H2. revert ys.
      induction n; intros.
      - destruct ys.
        - inversion H2. subst. easy.
        - simpl in H2. subst. easy.
      - destruct ys; try easy.
        specialize(IHn ys H2).
        destruct o; try easy.
      apply IHw; try easy.
  - subst. simpl.
    constructor.
    apply IHw; try easy.
Qed.


Lemma gtt_nguardG_false : forall w G G', nguardG w G -> gttTC G G' -> False.
Proof.
  induction w; intros.
  - specialize(nguardG_gttT_false G G' H H0); intros. easy.
  - inversion H.
    - subst.
      pinversion H0. subst.
      specialize(H7 n). rewrite H3 in H7.
      destruct H7; try easy.
      destruct H1 as (s1,(g1,(g2,(Ha,(Hb,Hc))))). inversion Ha. subst. clear Ha.
      pclearbot.
      specialize(IHw g1 g2 H5 Hc). easy.
      apply gttT_mon.
  - subst.
    specialize(nguardG_subst w P 0 0 (g_rec P) H4); intros.
    pinversion H0.
    subst.
    specialize(IHw (substitutionG 0 0 (g_rec P) P) G'). apply IHw; try easy.
    pfold. easy.
    apply gttT_mon.
Qed.



(* Converse direction: any syntax related to a coinductive tree is guarded. *)
Theorem gtt_to_cguardedG : forall G G', gttTC G G' -> cguardedG G.
Proof. 
  unfold cguardedG.
  intros.
  specialize(dec_closedG G); intros. destruct H0 as (xs, H0).
  specialize(gttT_closed_nil G G' xs H H0); intros. subst.
  split. easy.
  specialize(dec_guard_nguardG G); intros.
  destruct H1.
  - destruct H1 as (xs, Ha).
    specialize(guard_less_closedG G xs nil Ha H0); intros.
    destruct xs; try easy.
  - destruct H1 as (w, Ha).
    specialize(gtt_nguardG_false w G G' Ha H); intros. easy.
Qed.

 
Lemma gttTC_forward : forall G1 G, gttTC G1 G -> gttTC (unravelG G1) G.
Proof.
  intros.
  unfold unravelG.
  specialize(always_exists (mu_height G1)); intros.
  destruct H0 as (x,Ha). rewrite Ha. clear Ha.
  revert H. revert G G1.
  induction x; intros.
  - simpl. easy.
  - pinversion H; intros.
    - subst. simpl. apply IHx; try easy. pfold. easy.
    - subst. simpl. apply IHx; try easy. pfold. easy.
    - subst.
      simpl.
      apply IHx; try easy.
      pfold. easy.
  apply gttT_mon.
Qed.

     
Lemma unravelG_notmu : forall G, cguardedG G -> unravelG G = g_end \/ (exists p q lis, unravelG G = g_send p q lis).
Proof.
  intros.
  unfold unravelG.
  specialize(always_exists (mu_height G)); intros.
  destruct H0 as (x, Ha). rewrite Ha. revert Ha H. revert G.
  induction x; intros; try easy.
  - simpl in *.
    destruct G; try easy.
    - destruct H. inversion H. destruct n0; try easy.
    - left. easy.
    - right. exists p. exists p0. exists s. easy.
  - simpl in *.
    destruct G; try easy.
    inversion Ha.
    specialize(mu_height_after_subst_s G); intros.
    assert(mu_height G = mu_height (substitutionG 0 0 (g_rec G) G)).
    {
      apply H0.
      destruct H.
      specialize(guardG_to_GS); intros.
      apply H3; try easy.
    }
    specialize(IHx (substitutionG 0 0 (g_rec G) G)).
    clear H0. rewrite (esym H2) in IHx.
    rewrite H1 in IHx. rewrite H1.
    apply IHx; try easy.
    clear IHx H2 H1 Ha.
    destruct H. split.
    apply closedG_subst; try easy.
    apply guardG_subst; try easy.
Qed.
 
Lemma regGtt_cont : forall p q ys, regGtt (gtt_send p q ys) -> (forall n, ys n = None \/ (exists s g, ys n = Some(s, g) /\ regGtt g)).
Proof.
  intros.
  destruct H.
  specialize(gttTC_forward x (gtt_send p q ys) H); intros.
  specialize(gtt_to_cguardedG x (gtt_send p q ys) H); intros. 
  specialize(unravelG_notmu x H1); intros.
  destruct H2.
  - rewrite H2 in H0.
    pinversion H0.
    apply gttT_mon.
  - destruct H2 as (p1,(q1,(lis1,Ha))).
    rewrite Ha in H0.
    pinversion H0.
    subst.
    specialize(H3 n).
    destruct H3.
    - left. easy.
    - destruct H2 as (s1,(g1,(g2,(Hb,(Hc,Hd))))).
      rewrite Hc. right. exists s1. exists g2.
      split. easy.
      exists g1. pclearbot. easy.
      apply gttT_mon.
Qed. 


Lemma gttTC_inv_send : forall p q ys, regGtt (gtt_send p q ys) -> exists xs, gttTC (g_send p q xs) (gtt_send p q ys) /\ (forall n, (onth n xs = None /\ ys n = None) \/ (exists s g g', onth n xs = Some(s, g) /\ ys n = Some(s, g') /\ gttTC g g')). 
Proof.
  intros. destruct H as (G,H).
  specialize(gttTC_forward G (gtt_send p q ys) H); intros. 
  specialize(gtt_to_cguardedG G (gtt_send p q ys) H); intros.
  specialize(unravelG_notmu G H1); intros.
  destruct H2.
  - rewrite H2 in H0.
    pinversion H0.
    apply gttT_mon.
  - destruct H2 as (p1,(q1,(lis1,Ha))).
    rewrite Ha in H0. pinversion H0; try easy.
    subst. exists lis1.
    split.
    - pfold. easy.
    - intro.
      specialize(H3 n).
        destruct H3.
        - left. easy.
        - right. 
          destruct H2 as (s1,(g1,(g2,(Hb,(Hc,Hd))))).
          exists s1. exists g1. exists g2.
          pclearbot. easy.
    apply gttT_mon.
Qed.

Lemma regGtt_fin_cont : forall p q xs, regGtt (gtt_send p q xs) -> exists n, forall m, n <= m -> xs m = None.
Proof.
  intros.
  specialize(gttTC_inv_send p q xs H); intros.
  destruct H0 as (xs0,(Ha,Hb)). clear Ha.
  clear H. revert Hb. revert xs.
  induction xs0; intros.
  - exists 1; intros.
    specialize(Hb m).
    destruct m; try easy.
    simpl in *.
    destruct Hb; try easy. destruct H0 as (s1,(g1,(g2,(Ha,(Hb,Hc))))). easy.
  - specialize(IHxs0 (fun i => xs (S i))).
    assert(exists n : fin, forall m : fin, n <= m -> (fun i : fin => xs i.+1) m = None).
    {
      apply IHxs0; try easy.
      intros. specialize(Hb (S n)).
      simpl in *. easy.
    }
    clear IHxs0 Hb.
    destruct H as (n, H).
    exists (S n).
    intros. 
    destruct m; try easy.
    specialize(H m). 
    apply H; try easy.
Qed.



Lemma regGtt_some_cont : forall p q xs,
    regGtt (gtt_send p q xs) -> exists l sg, xs l = Some sg.
Proof.
  intros.
  specialize(gttTC_inv_send p q xs H); intros.
  destruct H0 as (xs0,(Ha,Hb)).
  clear Ha H. revert Hb. revert xs.
  induction xs0; intros.
  - specialize(Hb 0).
    destruct Hb; try easy.
    destruct H as (s1,(g1,(g2,(Ha,(Hb,Hc))))).
    exists 0. exists (s1, g2). easy.
  - specialize(IHxs0 (fun n => xs n.+1)).
    assert (exists (l : fin) (sg : sort * gtt), (fun n : fin => xs n.+1) l = Some sg).
    {
      apply IHxs0; try easy.
      intro.
      specialize(Hb (S n)). easy.
    }
    destruct H as (l,(sg,Ha)).
    exists l.+1. exists sg. easy.
Qed.


End global.


#[export] Hint Resolve gttT_mon : mon.















Definition unfoldG (G : global) : option global :=
  match unravelG G with
  | g_end => Some g_end
  | g_send p q xs => Some (g_send p q xs)
  | _ => None
  end.

CoInductive optionalG : global -> gtt -> Prop :=
| optionalG_end : forall G,
    unfoldG G = Some g_end ->
    optionalG G gtt_end
| optionalG_send : forall G p q xs ys,
    unfoldG G = Some (g_send p q xs) ->
    (forall n,
      (onth n xs = None /\ ys n = None) \/
      exists s g t,
        onth n xs = Some (s, g) /\
        ys n = Some (s, t) /\ optionalG g t) ->
    optionalG G (gtt_send p q ys).

Lemma unfoldG_some : forall G H,
  unfoldG G = Some H -> unravelG G = H.
Proof.
  intros G H E.
  unfold unfoldG in E.
  destruct (unravelG G); inversion E; reflexivity.
Qed.

Lemma betaG_iter : forall n G,
  betaG G (header.iter n unfold_recG G).
Proof.
  induction n as [|n IH]; intro G; simpl.
  - constructor.
  - destruct G; simpl; try apply IH.
    apply gttS. apply IH.
Qed.

Lemma betaG_unravel : forall G, betaG G (unravelG G).
Proof.
  intro G. unfold unravelG. apply betaG_iter.
Qed.

Theorem optionalG_to_gttTC : forall G H,
  optionalG G H -> gttTC G H.
Proof.
  unfold gttTC.
  pcofix CIH.
  intros G H HG.
  destruct HG as [G E | G p q xs ys E HB].
  - apply unfoldG_some in E.
    eapply gttTC_after_beta.
    + apply betaG_unravel.
    + rewrite E. pfold. constructor.
  - apply unfoldG_some in E.
    eapply gttTC_after_beta.
    + apply betaG_unravel.
    + rewrite E. pfold. apply gttT_send.
      intro n. destruct (HB n) as [HN | [s [g [t [HX [HY HT]]]]]].
      * left. exact HN.
      * right. exists s, g, t.
        split; [exact HX|]. split; [exact HY|].
        right. apply CIH. exact HT.
Qed.

Theorem gttTC_to_optionalG : forall G H,
  gttTC G H -> optionalG G H.
Proof.
  cofix CIH.
  intros G H HG.
  pose proof (gttTC_forward G H HG) as HH.
  pose proof (gtt_to_cguardedG G H HG) as HW.
  destruct (unravelG_notmu G HW) as [E | [p [q [xs E]]]].
  - rewrite E in HH.
    apply (@paco2_unfold _ _ _ gttT_mon) in HH.
    inversion HH; subst.
    apply optionalG_end.
    unfold unfoldG. rewrite E. reflexivity.
  - rewrite E in HH.
    apply (@paco2_unfold _ _ _ gttT_mon) in HH.
    inversion HH as [|p' q' xs' ys HB|U V HR]; subst.
    eapply optionalG_send.
    + unfold unfoldG. rewrite E. reflexivity.
    + intro n.
      destruct (HB n) as [HN | [s [g [t [HX [HY HT]]]]]].
      * left. exact HN.
      * right. exists s, g, t.
        split; [exact HX|]. split; [exact HY|].
        apply CIH. destruct HT as [HT | HT].
        -- exact HT.
        -- contradiction.
Qed.

Theorem optionalG_equiv : forall G H,
  optionalG G H <-> gttTC G H.
Proof.
  intros G H. split;
    [apply optionalG_to_gttTC | apply gttTC_to_optionalG].
Qed.

Theorem optionalG_well_formed_iff : forall G,
  cguardedG G <-> exists H, optionalG G H.
Proof.
  intro G. split.
  - intro HW. exists (global_to_gtt G).
    apply gttTC_to_optionalG. apply cguardedG_to_gtt. exact HW.
  - intros [H HG].
    apply (gtt_to_cguardedG G H).
    apply optionalG_to_gttTC. exact HG.
Qed.

Corollary optionalG_regularity_iff : forall H,
  (exists G, optionalG G H) <-> global.regGtt H.
Proof.
  intro H. split; intros [G HG]; exists G.
  - apply optionalG_to_gttTC. exact HG.
  - apply gttTC_to_optionalG. exact HG.
Qed.

Definition headG (G : global) : Prop :=
  match G with
  | g_end | g_send _ _ _ => True
  | _ => False
  end.

Fixpoint spineG (G : global) : bool :=
  match G with
  | g_var _ => false
  | g_rec B => spineG B
  | _ => true
  end.

Lemma spineG_incr : forall G x m,
  spineG (incr_freeG x m G) = spineG G.
Proof.
  induction G; intros x m; simpl; try reflexivity.
  apply IHG.
Qed.

Lemma spineG_subst_true : forall G P x m,
  spineG G = true ->
  spineG (substitutionG x m P G) = true /\
  global.mu_height (substitutionG x m P G) = global.mu_height G.
Proof.
  induction G; intros P x m HS; simpl in *; try discriminate;
    try (split; reflexivity).
  destruct (IHG P (S x) (S m) HS) as [HA HB].
  split; [exact HA|]. f_equal. exact HB.
Qed.

Lemma spineG_subst_false : forall G P x m,
  spineG G = false -> spineG P = false ->
  spineG (substitutionG x m P G) = false.
Proof.
  induction G; intros P x m HS HP; cbn [spineG] in HS; try discriminate.
  - destruct n; cbn [substitutionG];
      repeat match goal with
      | |- context [if ?b then _ else _] => destruct b
      end;
      try reflexivity;
      rewrite spineG_incr; exact HP.
  - cbn [substitutionG spineG]. apply IHG; assumption.
Qed.

Lemma spineG_step : forall G, spineG (unfold_recG G) = spineG G.
Proof.
  intro G. destruct G; try reflexivity.
  change (spineG (substitutionG 0 0 (g_rec G) G) = spineG G).
  destruct (spineG G) eqn:HS.
  - exact (proj1 (spineG_subst_true G (g_rec G) 0 0 HS)).
  - apply spineG_subst_false; exact HS.
Qed.

Lemma spineG_iter : forall n G,
  spineG (header.iter n unfold_recG G) = spineG G.
Proof.
  induction n as [|n IH]; intro G; simpl; [reflexivity|].
  rewrite IH. apply spineG_step.
Qed.

Lemma headG_spine_height : forall G,
  headG G -> spineG G = true /\ global.mu_height G = 0.
Proof.
  intro G. destruct G; cbn [headG spineG global.mu_height];
    intro H; try contradiction; split; reflexivity.
Qed.

Inductive muStepsG : nat -> global -> global -> Prop :=
| muStepsG_zero : forall G, muStepsG 0 G G
| muStepsG_mu : forall n B H,
    muStepsG n (substitutionG 0 0 (g_rec B) B) H ->
    muStepsG (S n) (g_rec B) H.

Lemma muStepsG_iter : forall n G H,
  muStepsG n G H -> header.iter n unfold_recG G = H.
Proof.
  intros n G H HS. induction HS; simpl; assumption || reflexivity.
Qed.

Lemma muStepsG_spine : forall n G H,
  muStepsG n G H -> spineG G = spineG H.
Proof.
  intros n G H HS. induction HS; [reflexivity|].
  pose proof (spineG_step (g_rec B)) as E.
  cbn [unfold_recG] in E. rewrite <- E. exact IHHS.
Qed.

Theorem muStepsG_head_exact_height : forall n G H,
  muStepsG n G H -> headG H -> n = global.mu_height G.
Proof.
  intros n G H HS. induction HS; intro HH.
  - symmetry. exact (proj2 (headG_spine_height G HH)).
  - pose proof (muStepsG_spine n (substitutionG 0 0 (g_rec B) B) H HS) as E.
    pose proof (proj1 (headG_spine_height H HH)) as HSH.
    assert (HSB : spineG B = true).
    {
      pose proof (spineG_step (g_rec B)) as ES.
      cbn [unfold_recG spineG] in ES.
      rewrite <- ES, E. exact HSH.
    }
    destruct (spineG_subst_true B (g_rec B) 0 0 HSB) as [_ HE].
    cbn [global.mu_height]. f_equal.
    rewrite (IHHS HH). exact HE.
Qed.

Lemma spineG_complete : forall n G,
  global.mu_height G = n -> spineG G = true ->
  muStepsG n G (header.iter n unfold_recG G) /\
  headG (header.iter n unfold_recG G).
Proof.
  induction n as [|n IH]; intros G HE HS.
  - split; [constructor|].
    destruct G; cbn [global.mu_height] in HE;
      cbn [spineG] in HS; try discriminate; exact I.
  - destruct G; cbn [global.mu_height] in HE; try discriminate.
    injection HE as HE.
    cbn [spineG] in HS.
    destruct (spineG_subst_true G (g_rec G) 0 0 HS) as [HP HM].
    assert (HN : global.mu_height (substitutionG 0 0 (g_rec G) G) = n).
    { rewrite HM. exact HE. }
    destruct (IH (substitutionG 0 0 (g_rec G) G) HN HP) as [HA HB].
    cbn [header.iter unfold_recG].
    split; [constructor; exact HA|exact HB].
Qed.

Definition rawUnfoldG (G H : global) : Prop :=
  exists n, muStepsG n G H /\ headG H.

Corollary rawUnfoldG_at_height : forall G H,
  rawUnfoldG G H -> muStepsG (global.mu_height G) G H.
Proof.
  intros G H [n [HS HH]].
  pose proof (muStepsG_head_exact_height n G H HS HH) as E.
  rewrite <- E. exact HS.
Qed.

Lemma unfoldG_some_head : forall G H,
  unfoldG G = Some H -> headG H.
Proof.
  intros G H E. unfold unfoldG in E.
  destruct (unravelG G); inversion E; exact I.
Qed.

Theorem rawUnfoldG_iff_optional : forall G H,
  rawUnfoldG G H <-> unfoldG G = Some H.
Proof.
  intros G H. split.
  - intros [n [HS HH]].
    pose proof (muStepsG_head_exact_height n G H HS HH) as HN.
    pose proof (muStepsG_iter n G H HS) as HE.
    unfold unfoldG, unravelG. rewrite <- HN, HE.
    destruct H; cbn [headG] in HH; try contradiction; reflexivity.
  - intro E.
    pose proof (unfoldG_some G H E) as EH.
    pose proof (unfoldG_some_head G H E) as HH.
    assert (HS : spineG G = true).
    {
      rewrite <- (spineG_iter (global.mu_height G) G).
      change (spineG (unravelG G) = true).
      rewrite EH. exact (proj1 (headG_spine_height H HH)).
    }
    destruct (spineG_complete (global.mu_height G) G Logic.eq_refl HS) as [HA HB].
    exists (global.mu_height G). split; [|exact HH].
    change (muStepsG (global.mu_height G) G (unravelG G)) in HA.
    rewrite EH in HA. exact HA.
Qed.

Corollary unfoldG_none_iff_no_raw_head : forall G,
  unfoldG G = None <-> ~ exists H, rawUnfoldG G H.
Proof.
  intro G. split.
  - intros E [H HR]. apply rawUnfoldG_iff_optional in HR.
    rewrite E in HR. discriminate.
  - intro HN. destruct (unfoldG G) as [H|] eqn:E; [|reflexivity].
    exfalso. apply HN. exists H.
    apply rawUnfoldG_iff_optional. exact E.
Qed.
