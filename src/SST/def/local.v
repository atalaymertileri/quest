From mathcomp Require Import ssreflect.seq all_ssreflect.
Require Import List String Coq.Arith.PeanoNat Coq.Arith.Arith Relations ZArith Datatypes Setoid Morphisms Coq.Logic.Decidable Coq.Program.Basics Coq.Init.Datatypes.
Import ListNotations. 
Open Scope list_scope.
From Paco Require Import paco.
Require Import def.header def.tree .

(* Local type syntax and translation to coinductive local trees (`ltt`).
   Mirrors the global development, but from one participant's viewpoint. *)
 

Section local.

(* Syntactic local types with de Bruijn recursion variables. *)
Inductive local  : Type :=
  | l_var : fin -> local
  | l_end : local
  | l_send : participant -> slist (sort * local) -> local
  | l_recv : participant -> slist (sort * local) -> local
  | l_rec : local -> local.
  
(* Strong induction principle over local syntax. *)
(* Induction principle that traverses all branch continuations in `slist`. *)
Section local_ind_ref.
  Variable P : local -> Prop.
  Hypothesis P_var : forall n, P (l_var n).
  Hypothesis P_end : P (l_end).
  Hypothesis P_send : forall p lis, SForall (fun u => P (snd u)) lis -> P (l_send p lis).
  Hypothesis P_recv : forall p lis, SForall (fun u => P (snd u)) lis -> P (l_recv p lis).
  Hypothesis P_rec : forall g, P g -> P (l_rec g).
  
  Fixpoint local_ind_ref p : P p.
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
    - apply P_recv.
      induction s; try easy.
      constructor; try easy.
      destruct o.
      - constructor; try easy.
      - constructor; try easy.
    - apply P_rec. easy.
  Qed.
End local_ind_ref.


(* De Bruijn shift for local recursion variables. *)
Fixpoint incr_freeL (fv m : fin) (G : local) := 
  match G with 
    | l_var n        => l_var (if fv <= n then (n + m) else n)
    | l_end          => l_end 
    | l_send p lis   => l_send p (smap (fun u => (fst u, incr_freeL fv m (snd u))) lis)
    | l_recv p lis   => l_recv p (smap (fun u => (fst u, incr_freeL fv m (snd u))) lis)
    | l_rec g        => l_rec (incr_freeL (S fv) m g)
  end.
  
(* Capture-avoiding substitution for local recursion variables. *)
Fixpoint substitutionL (x m : fin) (P Q : local) : local :=
    match Q with 
      | l_var k => match k with 
        | 0   => if Nat.eqb x 0 then (incr_freeL 0 m P) else l_var 0 
        | S k => if Nat.eqb x (S k) then (incr_freeL 0 m P) else  
                 if Nat.leb x (S k) then l_var k
                                    else l_var (S k)
        end
      | l_end => l_end
      | l_send p Q'    => l_send p (smap (fun u => (fst u, substitutionL x m P (snd u))) Q')
      | l_recv p Q'    => l_recv p (smap (fun u => (fst u, substitutionL x m P (snd u))) Q')
      | l_rec Q'         => l_rec (substitutionL (S x) (S m) P Q')
    end.

Inductive betaL : relation local := 
  | lttR : forall G, betaL G G
  | lttS : forall G G', betaL (substitutionL 0 0 (l_rec G) G) G' -> betaL (l_rec G) G'.


(* Generator for the coinductive relation from local syntax to `ltt`. *)
Inductive lttT (R : local -> ltt -> Prop) : local -> ltt -> Prop := 
  | lttT_end  : lttT R l_end ltt_end
  | lttT_send : forall p xs ys, (forall n, (onth n xs = None /\ ys n = None) \/ (exists s g g', onth n xs = Some(s, g) /\ ys n = Some(s, g') /\ R g g')) -> lttT R (l_send p xs) (ltt_send p ys)
  | lttT_recv : forall p xs ys, (forall n, (onth n xs = None /\ ys n = None) \/ (exists s g g', onth n xs = Some(s, g) /\ ys n = Some(s, g') /\ R g g')) -> lttT R (l_recv p xs) (ltt_recv p ys)
  | lttT_rec  : forall G G', lttT R (substitutionL 0 0 (l_rec G) G) G' -> lttT R (l_rec G) G'.

Definition lttTC G G' := paco2 lttT bot2 G G'.

Lemma lttT_mon : monotone2 lttT.
Proof.
  unfold monotone2. intros.
  induction IN; intros; try easy.
  - apply lttT_end.
  - apply lttT_send; try easy.
    intros. specialize(H n).
    destruct H.
    - left. easy.
    - right.
      destruct H as (s1,(g1,(g2,(Ha,(Hb,Hc))))).
      exists s1. exists g1. exists g2. split. easy. split. easy.
      apply LE; try easy.
  - apply lttT_recv; try easy.
    intros. specialize(H n).
    destruct H.
    - left. easy.
    - right.
      destruct H as (s1,(g1,(g2,(Ha,(Hb,Hc))))).
      exists s1. exists g1. exists g2. split. easy. split. easy.
      apply LE; try easy.
  - apply lttT_rec; try easy.
Qed.



Definition regLtt (G : ltt) := exists G', lttTC G' G.


Lemma lttTC_after_beta : forall G G' Gl r, betaL G G' -> paco2 lttT r G' Gl -> paco2 lttT r G Gl.
Proof. 
  intros. revert H0. revert Gl r.
  induction H; intros; try easy.
  pfold. apply lttT_rec.
  specialize(IHbetaL Gl r H0). 
  punfold IHbetaL; try easy.
  apply lttT_mon.
Qed.

(* Exact closedness for local recursion variables. *)
Inductive closedL : list bool -> local -> Prop :=
    | cl_var   : forall n, closedL (boollis n) (l_var n)
    | cl_end : closedL nil l_end
    | cl_send  : forall zs p lis, SForall2 (fun u v => closedL u (snd v)) zs lis -> closedL (bmergelis zs) (l_send p lis)
    | cl_recv  : forall zs p lis, SForall2 (fun u v => closedL u (snd v)) zs lis -> closedL (bmergelis zs) (l_recv p lis)
    | cl_rec0  : forall P, closedL nil P -> closedL nil (l_rec P)
    | cl_rec1  : forall P x xs, closedL (x :: xs) P -> closedL xs (l_rec P).
    
  (* Closure-friendly closedness with weakening rule `cls_sub`. *)
  Inductive closedLS : list bool -> local -> Prop :=
    | cls_var   : forall n, closedLS (boollis n) (l_var n)
    | cls_inact : closedLS nil l_end
    | cls_send  : forall zs p ys, SForall (fun u => (closedLS zs) (snd u)) ys -> closedLS zs (l_send p ys)
    | cls_recv  : forall zs p ys, SForall (fun u => (closedLS zs) (snd u)) ys -> closedLS zs (l_recv p ys)
    | cls_rec0  : forall P, closedLS nil P -> closedLS nil (l_rec P)
    | cls_rec1  : forall P x xs, closedLS (x :: xs) P -> closedLS xs (l_rec P)
    | cls_sub   : forall P xs ys, bmerge xs ys = ys -> closedLS xs P -> closedLS ys P.
  
  Lemma closedLS_inv_var : forall xs P n, closedLS xs P -> (P = l_var n) -> bmerge (boollis n) xs = xs.
  Proof.
    intros. revert H0. revert n.
    induction H; intros; try easy.
    - inversion H0. subst.
      clear H0.
      induction n0; try easy.
      simpl.
      rewrite IHn0. easy.
    - subst.
      specialize(IHclosedLS n (erefl (l_var n))).
      clear H0.
      revert IHclosedLS H.
      revert xs ys.
      induction n; intros; try easy.
      - destruct xs; try easy.
        destruct ys; try easy.
        inversion IHclosedLS. subst. inversion H. subst. simpl.
        assert(exists zs, bmerge xs ys = zs). exists (bmerge xs ys). easy.
        destruct H0 as (zs, H0). rewrite H0. destruct zs; try easy.
      - destruct xs; try easy.  
        destruct ys; try easy.
        inversion IHclosedLS. subst. inversion H. subst. simpl.
        specialize(IHn xs ys H1 H3).
        rewrite H3.
        rewrite IHn.
        easy.
  Qed.
        

  Lemma closedLS_inv_send : forall xs P p ys, closedLS xs P -> (P = l_send p ys) -> SForall (fun u => closedLS xs (snd u)) ys.
  Proof.
    intros.
    revert H0. revert ys p.
    induction H; intros; try easy.
    - inversion H0. subst. easy.
    - subst.
      specialize(IHclosedLS ys0 p).
      assert(SForall (fun u : sort * local => closedLS xs u.2) ys0). apply IHclosedLS; try easy.
      revert H1.
      apply SForall_mono; intros.
      apply cls_sub with (xs := xs); try easy.
  Qed.
  
  Lemma closedLS_inv_recv : forall xs P p ys, closedLS xs P -> (P = l_recv p ys) -> SForall (fun u => closedLS xs (snd u)) ys.
  Proof.
    intros.
    revert H0. revert ys p.
    induction H; intros; try easy.
    - inversion H0. subst. easy.
    - subst.
      specialize(IHclosedLS ys0 p).
      assert(SForall (fun u : sort * local => closedLS xs u.2) ys0). apply IHclosedLS; try easy.
      revert H1.
      apply SForall_mono; intros.
      apply cls_sub with (xs := xs); try easy.
  Qed.
  
  Lemma closedLS_inv_rec : forall xs P P', closedLS xs P -> (P = l_rec P') -> exists x, closedLS (x :: xs) P'.
  Proof.
    intros. revert H0. revert P'.
    induction H; intros; try easy.
    - inversion H0. subst.
      exists true.
      apply cls_sub with (xs := nil); try easy.
    - inversion H0. subst.
      exists x; try easy.
    - subst.
      specialize(IHclosedLS P').
      assert(exists x : bool, closedLS (x :: xs) P').
      apply IHclosedLS; try easy.
      destruct H1 as (x, H1).
      exists x.
      apply cls_sub with (xs := x :: xs); try easy.
      simpl. rewrite H. 
      destruct x; try easy.
  Qed.
   
  Lemma closedLS_free : forall Q xl xr m, closedLS (xl ++ xr) Q -> closedLS (xl ++ (false_list m) ++ xr) (incr_freeL (length xl) m Q).
  Proof.
    induction Q using local_ind_ref; intros; try easy.
    - simpl.
      specialize(closedLS_inv_var (xl ++ xr) (l_var n) n); intros.
      assert(bmerge (boollis n) (xl ++ xr) = xl ++ xr). apply H0; try easy. clear H H0.
      case_eq ((length xl) <= n); intros.
      - revert H H1. 
        revert n xr m.
        induction xl; intros; try easy.
        - simpl in *.
          apply cls_sub with (boollis (n + m)%coq_nat); try easy.
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
          apply cls_sub with (boollis (n.+1 + m)%coq_nat); try easy.
          - simpl.
            specialize(closedLS_inv_var (xl ++ false_list m ++ xr) (l_var (n + m)%coq_nat) (n + m)%coq_nat); intros.
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
          apply cls_sub with (boollis 0); try easy.
          - simpl. destruct xl; try easy.
            destruct m; try easy. 
          - constructor.
        - inversion H1. subst.
          specialize(IHxl n xr m H2 H).
          specialize(closedLS_inv_var (xl ++ false_list m ++ xr) (l_var n) n); intros.
          assert(bmerge (boollis n) (xl ++ false_list m ++ xr) = xl ++ false_list m ++ xr).
          apply H0; try easy. clear H0 IHxl.
          apply cls_sub with (boollis (S n)); try easy.
          - simpl. rewrite H3. easy.
          - constructor.
    - apply cls_sub with nil; try easy.
      - destruct xl; try easy. destruct m; try easy. destruct xr; try easy.
      - constructor.
    - simpl. constructor.
      specialize(closedLS_inv_send (xl ++ xr) (l_send p lis) p lis); intros.
      assert(SForall (fun u : sort * local => closedLS (xl ++ xr) u.2) lis). apply H1; try easy. clear H1 H0.
      revert H2 H. clear p. revert xl xr m.
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
    - simpl. constructor.
      specialize(closedLS_inv_recv (xl ++ xr) (l_recv p lis) p lis); intros.
      assert(SForall (fun u : sort * local => closedLS (xl ++ xr) u.2) lis). apply H1; try easy. clear H1 H0.
      revert H2 H. clear p. revert xl xr m.
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
      specialize(closedLS_inv_rec (xl ++ xr) (l_rec Q) Q); intros.
      assert(exists x : bool, closedLS (x :: xl ++ xr) Q).
      apply H0; try easy. destruct H1 as (x, Ha). clear H H0.
      apply cls_rec1 with (x := x); try easy.
      specialize(IHQ (x :: xl) xr m). apply IHQ; try easy.
  Qed.
  
  Lemma closedLS_remove_false : forall Q xs n, closedLS (xs ++ false_list n) Q -> closedLS xs Q.
  Proof.
    induction Q using local_ind_ref; intros; try easy.
    - specialize(closedLS_inv_var (xs ++ false_list n0) (l_var n) n); intros.
      assert(bmerge (boollis n) (xs ++ false_list n0) = xs ++ false_list n0).
      apply H0; try easy. clear H0 H.
      apply cls_sub with (xs := (boollis n)); try easy.
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
    - apply cls_sub with nil; try easy.
      - destruct xs; try easy.
      - constructor.
    - constructor.
      specialize(closedLS_inv_send (xs ++ false_list n) (l_send p lis) p lis); intros.
      assert(SForall (fun u : sort * local => closedLS (xs ++ false_list n) u.2) lis).
      apply H1; try easy. clear H1 H0.
      revert H H2.
      apply SForall_mono2; intros; try easy.
      apply H with (n := n); try easy.
    - constructor.
      specialize(closedLS_inv_recv (xs ++ false_list n) (l_recv p lis) p lis); intros.
      assert(SForall (fun u : sort * local => closedLS (xs ++ false_list n) u.2) lis).
      apply H1; try easy. clear H1 H0.
      revert H H2.
      apply SForall_mono2; intros; try easy.
      apply H with (n := n); try easy.
    - specialize(closedLS_inv_rec (xs ++ false_list n) (l_rec Q) Q); intros.
      assert(exists x : bool, closedLS (x :: xs ++ false_list n) Q).
      apply H0; try easy.
      destruct H1 as (x, Ha).
      apply cls_rec1 with (x := x); try easy.
      apply IHQ with (n := n); try easy.
  Qed.

  Lemma closedLS_freeS : forall Q m, closedLS nil Q -> closedLS nil (incr_freeL 0 m Q).
  Proof.
    intros.
    specialize(closedLS_free Q nil nil m H); intros.
    simpl in *.
    specialize(closedLS_remove_false (incr_freeL 0 m Q) nil m); intros.
    apply H1; try easy.
    clear H1 H.
    specialize(app_nil_r (false_list m)); intros.
    rewrite H in H0. easy.
  Qed.
  
  Lemma closedLS_subst : forall P Q xl xe xr m, closedLS (xl ++ [xe] ++ xr) P -> closedLS nil Q -> closedLS (xl ++ xr) (substitutionL (length xl) m Q P).
  Proof.
    induction P using local_ind_ref; intros; try easy.
    - specialize(closedLS_inv_var (xl ++ [xe] ++ xr) (l_var n) n); intros.
      assert(bmerge (boollis n) (xl ++ [xe] ++ xr) = xl ++ [xe] ++ xr).
      apply H1; try easy. clear H H1.
      simpl.
      destruct n.
      - destruct xl; try easy. 
        - simpl.
          apply cls_sub with nil; try easy. destruct xr; try easy.
          apply closedLS_freeS; try easy.
        - simpl.
          inversion H2. subst.
          apply cls_sub with (boollis 0); try easy.
          - simpl. destruct xl; try easy. destruct xr; try easy.
          - constructor.
      - case_eq (Nat.eqb (length xl) (S n)); intros.
        - apply cls_sub with nil; try easy.
          - destruct xl; try easy.
          - clear H2 H.
            apply closedLS_freeS; try easy.
        case_eq (Nat.leb (length xl) (S n)); intros.
        - clear H0.
          revert H1 H H2. revert n xe xr. clear Q m.
          induction xl; intros; try easy.
          - inversion H2. simpl in *.
            rewrite H3.
            apply cls_sub with (xs := (boollis n)); try easy.
            constructor.
          - destruct n; try easy.
            - destruct xl; try easy.
            - inversion H2. 
              specialize(IHxl n xe xr H1 H H3).
              clear H3 H2 H H1.
              specialize(closedLS_inv_var (xl ++ xr) (l_var n) n); intros.
              assert(bmerge (boollis n) (xl ++ xr) = xl ++ xr).
              apply H; try easy. clear H.
              apply cls_sub with (boollis (S n)); try easy.
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
            apply cls_sub with (boollis 0); try easy.
            simpl. destruct xl; try easy. destruct xr; try easy.
            constructor.
          - destruct xl; try easy.
            inversion H2. 
            specialize(IHn xl xe xr H1 H0).
            specialize(closedLS_inv_var (xl ++ xr) (l_var n) n); intros.
            assert(bmerge (boollis n) (xl ++ xr) = xl ++ xr). apply H; try easy.
            clear H H0 H2 H1 IHn.
            apply cls_sub with (boollis (S n)); try easy.
            - simpl. rewrite H3. easy.
            - constructor.
    - simpl.
      apply cls_sub with (xs := nil); try easy.
      destruct xl; try easy. destruct xr; try easy.
      constructor.
    - simpl.
      constructor.
      specialize(closedLS_inv_send (xl ++ [xe] ++ xr) (l_send p lis) p lis); intros. 
      assert(SForall (fun u : sort * local => closedLS (xl ++ [xe] ++ xr) u.2) lis).
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
      constructor.
      specialize(closedLS_inv_recv (xl ++ [xe] ++ xr) (l_recv p lis) p lis); intros. 
      assert(SForall (fun u : sort * local => closedLS (xl ++ [xe] ++ xr) u.2) lis).
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
      specialize(closedLS_inv_rec (xl ++ [xe] ++ xr) (l_rec P) P); intros.
      assert(exists x : bool, closedLS (x :: xl ++ [xe] ++ xr) P).
      apply H1; try easy. clear H1 H.
      destruct H2 as (x, Ha).
      apply cls_rec1 with (x := x); try easy.
      specialize(IHP Q (x :: xl) xe xr). apply IHP; try easy.
  Qed.
  
  Lemma closedL_to_GS : forall xs P, closedL xs P -> closedLS xs P.
  Proof.
    intros xs P. revert xs.
    induction P using local_ind_ref; intros; try easy.
    - inversion H.
      constructor.
    - inversion H.
      constructor.
    - inversion H0. subst.
      clear H0.
      revert H3 H.
      revert p zs.
      induction lis; intros; try easy.
      - inversion H3. subst. clear H3.
        inversion H. subst. clear H.
        constructor. constructor; try easy.
        apply H1; try easy.
      inversion H3.
      - subst. clear H3.
        inversion H. subst. clear H.
        specialize(IHlis p xs H5 H3). clear H3.
        specialize(H2 x H4). clear H4.
        constructor.
        constructor.
        - apply cls_sub with x; try easy. 
          simpl.
          specialize(bmerge_again_l x (bmergelis xs)); intros. easy.
        - clear H2.
          specialize(closedLS_inv_send (bmergelis xs) (l_send p lis) p lis); intros.
          assert(SForall (fun u : sort * local => closedLS (bmergelis xs) u.2) lis). apply H; try easy. clear H H5 IHlis.
          clear p y.
          revert H0.
          apply SForall_mono; intros; try easy.
          apply cls_sub with (bmergelis xs); try easy.
          simpl.
          apply bmerge_again_r; try easy.
      - subst. clear H3.
        inversion H. subst. clear H.
        specialize(IHlis p xs H2 H1).
        specialize(closedLS_inv_send (bmergelis xs) (l_send p lis) p lis); intros.
          assert(SForall (fun u : sort * local => closedLS (bmergelis xs) u.2) lis). apply H; try easy.
        clear H H1 H2.
        constructor.
        constructor; try easy.
    - inversion H0. subst.
      clear H0.
      revert H3 H.
      revert p zs.
      induction lis; intros; try easy.
      - inversion H3. subst. clear H3.
        inversion H. subst. clear H.
        constructor. constructor; try easy.
        apply H1; try easy.
      inversion H3.
      - subst. clear H3.
        inversion H. subst. clear H.
        specialize(IHlis p xs H5 H3). clear H3.
        specialize(H2 x H4). clear H4.
        constructor.
        constructor.
        - apply cls_sub with x; try easy. 
          simpl.
          specialize(bmerge_again_l x (bmergelis xs)); intros. easy.
        - clear H2.
          specialize(closedLS_inv_recv (bmergelis xs) (l_recv p lis) p lis); intros.
          assert(SForall (fun u : sort * local => closedLS (bmergelis xs) u.2) lis). apply H; try easy. clear H H5 IHlis.
          clear p y.
          revert H0.
          apply SForall_mono; intros; try easy.
          apply cls_sub with (bmergelis xs); try easy.
          simpl.
          apply bmerge_again_r; try easy.
      - subst. clear H3.
        inversion H. subst. clear H.
        specialize(IHlis p xs H2 H1).
        specialize(closedLS_inv_recv (bmergelis xs) (l_recv p lis) p lis); intros.
          assert(SForall (fun u : sort * local => closedLS (bmergelis xs) u.2) lis). apply H; try easy.
        clear H H1 H2.
        constructor.
        constructor; try easy.
    - inversion H. subst.
      - apply cls_rec0.
        apply IHP; try easy.
      - subst.
        apply cls_rec1 with (x := x).
        apply IHP; try easy.
  Qed. 
        
  Lemma closedLS_to_G : forall xs P, closedLS xs P -> exists ys, bmerge ys xs = xs /\ closedL ys P.
  Proof.
    intros xs P. revert xs.
    induction P using local_ind_ref; intros; try easy.
    - specialize(closedLS_inv_var xs (l_var n) n); intros.
      assert(bmerge (boollis n) xs = xs). apply H0; try easy.
      clear H0.
      exists (boollis n).
      split. easy. constructor.
    - exists nil.
      split. destruct xs; try easy.
      constructor.
    - specialize(closedLS_inv_send xs (l_send p lis) p lis); intros.
      assert(SForall (fun u : sort * local => closedLS xs u.2) lis). apply H1; try easy. clear H1 H0.
      revert H H2. 
      revert xs p.
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
        specialize(IHlis xs p H5 H4). clear H5 H4.
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
        specialize(IHlis xs p H2 H1). clear H2 H1.
        destruct IHlis as (ys,(Ha,Hb)).
        exists ys.
        split. easy.
        inversion Hb. subst.
        replace (bmergelis zs) with (bmergelis (slist_xs None zs)); try easy.
        constructor. constructor; try easy.
    - specialize(closedLS_inv_recv xs (l_recv p lis) p lis); intros.
      assert(SForall (fun u : sort * local => closedLS xs u.2) lis). apply H1; try easy. clear H1 H0.
      revert H H2. 
      revert xs p.
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
        specialize(IHlis xs p H5 H4). clear H5 H4.
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
        specialize(IHlis xs p H2 H1). clear H2 H1.
        destruct IHlis as (ys,(Ha,Hb)).
        exists ys.
        split. easy.
        inversion Hb. subst.
        replace (bmergelis zs) with (bmergelis (slist_xs None zs)); try easy.
        constructor. constructor; try easy.
    - specialize(closedLS_inv_rec xs (l_rec P) P); intros.
      assert(exists x : bool, closedLS (x :: xs) P).
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
        apply cl_rec1 with (x := b); try easy.
  Qed.

  Lemma closedL_subst : forall P, closedL nil (l_rec P) -> closedL nil (substitutionL 0 0 (l_rec P) P).
  Proof.
    intros.
    specialize(closedL_to_GS nil (l_rec P) H); intros. clear H.
    specialize(closedLS_inv_rec [] (l_rec P) P); intros.
    assert(exists x : bool, closedLS [x] P). apply H; try easy.
    destruct H1 as (x, Ha). clear H.
    specialize(closedLS_subst P (l_rec P) nil x nil 0); intros.
    assert(closedLS nil (substitutionL 0 0 (l_rec P) P)).
    apply H; try easy. clear H.
    specialize(closedLS_to_G nil (substitutionL 0 0 (l_rec P) P) H1); intros.
    destruct H as (ys,(Hb,Hc)).
    destruct ys; try easy.
  Qed.
       
  (* Exact guardedness: recursion variables must appear under IO nodes. *)
  Inductive guardL : list bool -> local -> Prop :=
    | gl_var   : forall n, guardL (boollis n) (l_var n)
    | gl_end : guardL nil l_end
    | gl_send  : forall p ys zs, SForall2 (fun u v => guardL u (snd v)) zs ys -> guardL nil (l_send p ys)
    | gl_recv  : forall p ys zs, SForall2 (fun u v => guardL u (snd v)) zs ys -> guardL nil (l_recv p ys)
    | gl_rec0  : forall P, guardL nil P -> guardL nil (l_rec P)
    | gl_rec1  : forall P xs, guardL (false :: xs) P -> guardL xs (l_rec P).
  
  (* Witness form of non-guardedness for contradiction proofs. *)
  Inductive nguardL : list (option fin) -> local -> Prop :=
    | ngl_init : forall P xs, guardL (true :: xs) P -> nguardL nil (l_rec P)
    | ngl_send : forall p ys n s g w, onth n ys = Some(s, g) -> nguardL w g -> nguardL (Some n :: w) (l_send p ys)
    | ngl_recv : forall p ys n s g w, onth n ys = Some(s, g) -> nguardL w g -> nguardL (Some n :: w) (l_recv p ys)
    | ngl_rec  : forall P w, nguardL w P -> nguardL (None :: w) (l_rec P).
    
  (* Closure-friendly guardedness with weakening rule `gls_sub`. *)
  Inductive guardLS : list bool -> local -> Prop :=
    | gls_var   : forall n, guardLS (boollis n) (l_var n)
    | gls_inact : guardLS nil l_end
    | gls_send  : forall p ys zs, SForall2 (fun u v => guardLS u (snd v)) zs ys -> guardLS nil (l_send p ys)
    | gls_recv  : forall p ys zs, SForall2 (fun u v => guardLS u (snd v)) zs ys -> guardLS nil (l_recv p ys)
    | gls_rec0  : forall P, guardLS nil P -> guardLS nil (l_rec P)
    | gls_rec1  : forall P xs, guardLS (false :: xs) P -> guardLS xs (l_rec P)
    | gls_sub   : forall P xs ys, bmerge xs ys = ys -> guardLS xs P -> guardLS ys P.
    
  
  Lemma guardLS_inv_var : forall xs P n, P = l_var n -> guardLS xs P -> bmerge (boollis n) xs = xs.
  Proof.
    intros. revert H. revert n.
    induction H0; intros; try easy.
    - inversion H. subst. 
      clear H.
      induction n0; try easy.
      simpl. rewrite IHn0. easy.
    - subst.
      specialize(IHguardLS n (erefl (l_var n))).
      clear H0.
      revert IHguardLS H.
      revert xs ys.
      induction n; intros; try easy.
      - destruct xs; try easy.
        destruct ys; try easy.
        simpl. 
        inversion IHguardLS. subst.
        inversion H. subst.
        rewrite H3.
        destruct ys; try easy.
      - destruct xs; try easy.
        destruct ys; try easy.
        inversion IHguardLS.
        inversion H.
        specialize(IHn xs ys H1 H3).
        simpl. rewrite H3. rewrite IHn.
        easy.
  Qed.
  
  Lemma guardLS_inv_send : forall xs P p lis, (P = l_send p lis) -> guardLS xs P -> exists ys, SForall2 (fun u v => guardLS u (snd v)) ys lis.
  Proof.
    intros.
    revert H. revert p lis.
    induction H0; intros; try easy.
    - inversion H0. subst.
      exists zs. easy.
    - subst.
      specialize(IHguardLS p lis).
      apply IHguardLS; try easy.
  Qed.
  
  Lemma guardLS_inv_recv : forall xs P p lis, (P = l_recv p lis) -> guardLS xs P -> exists ys, SForall2 (fun u v => guardLS u (snd v)) ys lis.
  Proof.
    intros.
    revert H. revert p lis.
    induction H0; intros; try easy.
    - inversion H0. subst.
      exists zs. easy.
    - subst.
      specialize(IHguardLS p lis).
      apply IHguardLS; try easy.
  Qed.
  
  Lemma guardLS_inv_rec : forall xs P Q, (P = l_rec Q) -> guardLS xs P -> guardLS (false :: xs) Q.
  Proof.
    intros.
    revert H. revert Q.
    induction H0; intros; try easy.
    - inversion H. subst.
      apply gls_sub with nil; try easy.
    - inversion H. subst. easy.
    - subst.
      specialize(IHguardLS Q (erefl (l_rec Q))); intros.
      apply gls_sub with (false :: xs); try easy.
      simpl. rewrite H. easy.
  Qed.
  
  Lemma guardLS_bmergeR : forall P xs ys, guardLS xs P -> guardLS ys P -> guardLS (bmergeR xs ys) P.
  Proof.
    induction P using local_ind_ref; intros.
    - specialize(guardLS_inv_var xs (l_var n) n (erefl (l_var n)) H); intros.
      specialize(guardLS_inv_var ys (l_var n) n (erefl (l_var n)) H0); intros.
      clear H H0.
      apply gls_sub with (boollis n).
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
    - apply gls_sub with nil.
      - destruct xs; try easy.
        - destruct ys; try easy.
        - destruct ys; try easy.
      - constructor.
    - specialize(guardLS_inv_send xs (l_send p lis) p lis); intros.
      assert(exists ys : slist (seq.seq bool),
       SForall2 (fun (u : seq.seq bool) (v : sort * local) => guardLS u v.2) ys lis).
      apply H2; try easy. clear H2. destruct H3 as (zs, H3).
      apply gls_sub with nil; try easy.
      - destruct xs; try easy.
        - destruct ys; try easy.
        - destruct ys; try easy.
      - apply gls_send with zs; try easy.
    - specialize(guardLS_inv_recv xs (l_recv p lis) p lis); intros.
      assert(exists ys : slist (seq.seq bool),
       SForall2 (fun (u : seq.seq bool) (v : sort * local) => guardLS u v.2) ys lis).
      apply H2; try easy. clear H2. destruct H3 as (zs, H3).
      apply gls_sub with nil; try easy.
      - destruct xs; try easy.
        - destruct ys; try easy.
        - destruct ys; try easy.
      - apply gls_recv with zs; try easy.
    - specialize(guardLS_inv_rec xs (l_rec P) P); intros.
      assert(guardLS (false :: xs) P). apply H1; try easy. clear H1.
      specialize(guardLS_inv_rec ys (l_rec P) P); intros.
      assert(guardLS (false :: ys) P). apply H1; try easy. clear H1.
      specialize(IHP (false :: xs) (false :: ys) H2 H3).
      apply gls_rec1; try easy.
  Qed.
  
  Lemma guardLS_any_length : forall P xs n, guardLS xs P -> exists xl xe xr, length xl = n /\ guardLS (xl ++ [xe] ++ xr) P.
  Proof.
    induction P using local_ind_ref; intros; try easy.
    - specialize(guardLS_inv_var xs (l_var n) n); intros.
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
          - apply gls_sub with (boollis 0); try easy.
            simpl. destruct n0; try easy.
            constructor.
        - destruct xs; try easy.
          inversion H1.
          specialize(IHn0 xs n H0).
          destruct IHn0 as (xl,(xe,(xr,(Ha,Hb)))).
          exists (false :: xl). exists xe. exists xr.
          split. simpl. rewrite Ha. easy.
          specialize(guardLS_inv_var (xl ++ [xe] ++ xr) (l_var n) n); intros.
          assert(bmerge (boollis n) (xl ++ [xe] ++ xr) = xl ++ [xe] ++ xr).
          apply H; try easy. clear H.
          apply gls_sub with (boollis (S n)); try easy.
          - simpl. rewrite H2. easy.
          - constructor.
    - exists (false_list n). exists false. exists nil.
      clear H xs.
      split.
      - induction n; intros; try easy.
        simpl.
        rewrite IHn. easy.
      - apply gls_sub with nil; try easy.
        - destruct n; try easy.
        - constructor.
    - clear H.
      exists (false_list n). exists false. exists nil.
      specialize(guardLS_inv_send xs (l_send p lis) p lis); intros.
      assert(exists ys : slist (seq.seq bool),
      SForall2 (fun (u : seq.seq bool) (v : sort * local) => guardLS u v.2) ys lis).
      apply H; try easy. clear H. destruct H1 as (ys, Ha).
      split.
      - clear Ha H0. clear p lis xs ys.
        induction n; intros; try easy.
        simpl. rewrite IHn. easy.
      - apply gls_sub with nil; try easy.
        - destruct n; try easy.
        - apply gls_send with ys; try easy.
    - clear H.
      exists (false_list n). exists false. exists nil.
      specialize(guardLS_inv_recv xs (l_recv p lis) p lis); intros.
      assert(exists ys : slist (seq.seq bool),
      SForall2 (fun (u : seq.seq bool) (v : sort * local) => guardLS u v.2) ys lis).
      apply H; try easy. clear H. destruct H1 as (ys, Ha).
      split.
      - clear Ha H0. clear p lis xs ys.
        induction n; intros; try easy.
        simpl. rewrite IHn. easy.
      - apply gls_sub with nil; try easy.
        - destruct n; try easy.
        - apply gls_recv with ys; try easy.
    - specialize(guardLS_inv_rec xs (l_rec P) P); intros.
      assert(guardLS (false :: xs) P). apply H0; try easy.
      clear H0 H.
      specialize(IHP (false :: xs) (S n) H1).
      destruct IHP as (xl,(xe,(xr,(Hb,Hc)))).
      destruct xl; try easy.
      exists xl. exists xe. exists xr.
      inversion Hb. split. easy.
      apply gls_rec1; try easy.
      specialize(guardLS_bmergeR P (false :: xs) ((b :: xl) ++ [xe] ++ xr) H1 Hc); intros.
      apply gls_sub with (bmergeR (false :: xs) ((b :: xl) ++ [xe] ++ xr)); try easy.
      clear H H0 H1 Hc Hb.
      simpl.
      specialize(bmergeR_back xs (xl ++ xe :: xr)); intros.
      rewrite H. easy.
  Qed.
  
  Lemma guardLS_free : forall Q xl xr m, guardLS (xl ++ xr) Q -> guardLS (xl ++ (false_list m) ++ xr) (incr_freeL (length xl) m Q).
  Proof.
    induction Q using local_ind_ref; intros; try easy.
    - simpl.
      specialize(guardLS_inv_var (xl ++ xr) (l_var n) n); intros.
      assert(bmerge (boollis n) (xl ++ xr) = xl ++ xr). apply H0; try easy. clear H H0.
      case_eq ((length xl) <= n); intros.
      - revert H H1. 
        revert n xr m.
        induction xl; intros; try easy.
        - simpl in *.
          apply gls_sub with (boollis (n + m)%coq_nat); try easy.
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
          apply gls_sub with (boollis (n.+1 + m)%coq_nat); try easy.
          - simpl.
            specialize(guardLS_inv_var (xl ++ false_list m ++ xr) (l_var (n + m)%coq_nat) (n + m)%coq_nat); intros.
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
          apply gls_sub with (boollis 0); try easy.
          - simpl. destruct xl; try easy.
            destruct m; try easy. 
          - constructor.
        - inversion H1. subst.
          specialize(IHxl n xr m H2 H).
          specialize(guardLS_inv_var (xl ++ false_list m ++ xr) (l_var n) n); intros.
          assert(bmerge (boollis n) (xl ++ false_list m ++ xr) = xl ++ false_list m ++ xr).
          apply H0; try easy. clear H0 IHxl.
          apply gls_sub with (boollis (S n)); try easy.
          - simpl. rewrite H3. easy.
          - constructor.
    - apply gls_sub with nil; try easy.
      - destruct xl; try easy. destruct m; try easy. destruct xr; try easy.
      - constructor.
    - simpl.
      specialize(guardLS_inv_send (xl ++ xr) (l_send p lis) p lis); intros.
      assert(exists ys : slist (seq.seq bool),
       SForall2 (fun (u : seq.seq bool) (v : sort * local) => guardLS u v.2) ys lis).
      apply H1; try easy.
      destruct H2 as (ys, Ha).
      clear H1 H0.
      apply gls_sub with nil.
      - destruct xl; try easy. destruct m; try easy. destruct xr; try easy.
      revert Ha H. clear xr. 
      revert p xl m ys.
      induction lis; intros; try easy.
      - inversion Ha. subst. clear Ha.
        inversion H. subst. clear H.
        specialize(guardLS_any_length a.2 x (length xl) H2); intros.
        destruct H as (xl0,(xe,(xr0,(Ha,Hb)))).
        specialize(H1 xl0 (xe :: xr0)).
        apply gls_send with (zs := slist_x ((xl0 ++ false_list m ++ xe :: xr0))); try easy.
        constructor; try easy.
        rewrite (esym Ha).
        apply H1; try easy.
      inversion Ha.
      - subst. clear Ha.
        inversion H. subst. clear H.
        specialize(IHlis p xl m xs H4 H5).
        clear H5 H4.
        specialize(guardLS_inv_send nil (l_send p (smap (fun u : sort * local => (u.1, incr_freeL (length xl) m u.2)) lis)) p (smap (fun u : sort * local => (u.1, incr_freeL (length xl) m u.2)) lis)); intros.
        assert(exists ys : slist (seq.seq bool),
      SForall2 (fun (u : seq.seq bool) (v : sort * local) => guardLS u v.2) ys
        (smap (fun u : sort * local => (u.1, incr_freeL (length xl) m u.2)) lis)).
        apply H; try easy.
        destruct H0 as (zs, Ha).
        clear H IHlis.
        specialize(guardLS_any_length y.2 x (length xl) H3); intros.
        destruct H as (xl0,(xe,(xr,(Hb,Hc)))).
        specialize(H2 xl0 (xe :: xr) m Hc).
        rewrite Hb in H2.
        apply gls_send with (slist_xs (Some (xl0 ++ false_list m ++ xe :: xr)) zs).
        constructor; try easy.
      - subst. clear Ha.
        inversion H. subst. clear H.
        specialize(IHlis p xl m xs H2 H1).
        clear H2 H1.
        specialize(guardLS_inv_send nil (l_send p (smap (fun u : sort * local => (u.1, incr_freeL (length xl) m u.2)) lis)) p (smap (fun u : sort * local => (u.1, incr_freeL (length xl) m u.2)) lis)); intros.
        assert(exists ys : slist (seq.seq bool),
      SForall2 (fun (u : seq.seq bool) (v : sort * local) => guardLS u v.2) ys
        (smap (fun u : sort * local => (u.1, incr_freeL (length xl) m u.2)) lis)).
        apply H; try easy.
        destruct H0 as (zs, Ha).
        clear H IHlis.
        apply gls_send with (slist_xs None zs).
        constructor; try easy.
    - simpl.
      specialize(guardLS_inv_recv (xl ++ xr) (l_recv p lis) p lis); intros.
      assert(exists ys : slist (seq.seq bool),
       SForall2 (fun (u : seq.seq bool) (v : sort * local) => guardLS u v.2) ys lis).
      apply H1; try easy.
      destruct H2 as (ys, Ha).
      clear H1 H0.
      apply gls_sub with nil.
      - destruct xl; try easy. destruct m; try easy. destruct xr; try easy.
      revert Ha H. clear xr. 
      revert p xl m ys.
      induction lis; intros; try easy.
      - inversion Ha. subst. clear Ha.
        inversion H. subst. clear H.
        specialize(guardLS_any_length a.2 x (length xl) H2); intros.
        destruct H as (xl0,(xe,(xr0,(Ha,Hb)))).
        specialize(H1 xl0 (xe :: xr0)).
        apply gls_recv with (zs := slist_x ((xl0 ++ false_list m ++ xe :: xr0))); try easy.
        constructor; try easy.
        rewrite (esym Ha).
        apply H1; try easy.
      inversion Ha.
      - subst. clear Ha.
        inversion H. subst. clear H.
        specialize(IHlis p xl m xs H4 H5).
        clear H5 H4.
        specialize(guardLS_inv_recv nil (l_recv p (smap (fun u : sort * local => (u.1, incr_freeL (length xl) m u.2)) lis)) p (smap (fun u : sort * local => (u.1, incr_freeL (length xl) m u.2)) lis)); intros.
        assert(exists ys : slist (seq.seq bool),
      SForall2 (fun (u : seq.seq bool) (v : sort * local) => guardLS u v.2) ys
        (smap (fun u : sort * local => (u.1, incr_freeL (length xl) m u.2)) lis)).
        apply H; try easy.
        destruct H0 as (zs, Ha).
        clear H IHlis.
        specialize(guardLS_any_length y.2 x (length xl) H3); intros.
        destruct H as (xl0,(xe,(xr,(Hb,Hc)))).
        specialize(H2 xl0 (xe :: xr) m Hc).
        rewrite Hb in H2.
        apply gls_recv with (slist_xs (Some (xl0 ++ false_list m ++ xe :: xr)) zs).
        constructor; try easy.
      - subst. clear Ha.
        inversion H. subst. clear H.
        specialize(IHlis p xl m xs H2 H1).
        clear H2 H1.
        specialize(guardLS_inv_recv nil (l_recv p (smap (fun u : sort * local => (u.1, incr_freeL (length xl) m u.2)) lis)) p (smap (fun u : sort * local => (u.1, incr_freeL (length xl) m u.2)) lis)); intros.
        assert(exists ys : slist (seq.seq bool),
      SForall2 (fun (u : seq.seq bool) (v : sort * local) => guardLS u v.2) ys
        (smap (fun u : sort * local => (u.1, incr_freeL (length xl) m u.2)) lis)).
        apply H; try easy.
        destruct H0 as (zs, Ha).
        clear H IHlis.
        apply gls_recv with (slist_xs None zs).
        constructor; try easy.
    - simpl.
      specialize(guardLS_inv_rec (xl ++ xr) (l_rec Q) Q); intros.
      assert(guardLS (false :: xl ++ xr) Q).
      apply H0; try easy. clear H0.
      specialize(IHQ (false :: xl) xr m H1).
      apply gls_rec1; try easy.
  Qed.
  
  Lemma guardLS_remove_false : forall Q xs n, guardLS (xs ++ false_list n) Q -> guardLS xs Q.
  Proof.
    induction Q using local_ind_ref; intros; try easy.
    - specialize(guardLS_inv_var (xs ++ false_list n0) (l_var n) n); intros.
      assert(bmerge (boollis n) (xs ++ false_list n0) = xs ++ false_list n0).
      apply H0; try easy. clear H0 H.
      apply gls_sub with (xs := (boollis n)); try easy.
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
    - apply gls_sub with nil; try easy.
      - destruct xs; try easy.
      - constructor.
    - specialize(guardLS_inv_send (xs ++ false_list n) (l_send p lis) p lis); intros.
      assert(exists ys : slist (seq.seq bool),
       SForall2 (fun (u : seq.seq bool) (v : sort * local) => guardLS u v.2) ys lis).
      apply H1; try easy. clear H1 H0.
      destruct H2 as (ys, H2).
      apply gls_sub with nil.
      - destruct xs; try easy.
      - apply gls_send with ys; try easy.
    - specialize(guardLS_inv_recv (xs ++ false_list n) (l_recv p lis) p lis); intros.
      assert(exists ys : slist (seq.seq bool),
       SForall2 (fun (u : seq.seq bool) (v : sort * local) => guardLS u v.2) ys lis).
      apply H1; try easy. clear H1 H0.
      destruct H2 as (ys, H2).
      apply gls_sub with nil.
      - destruct xs; try easy.
      - apply gls_recv with ys; try easy.
    - specialize(guardLS_inv_rec (xs ++ false_list n) (l_rec Q) Q); intros.
      assert(guardLS (false :: xs ++ false_list n) Q).
      apply H0; try easy.
      apply gls_rec1.
      apply IHQ with (n := n); try easy.
  Qed.
      
  Lemma guardLS_freeS : forall Q m, guardLS nil Q -> guardLS nil (incr_freeL 0 m Q).
  Proof.
    intros.
    specialize(guardLS_free Q nil nil m H); intros.
    simpl in *.
    specialize(guardLS_remove_false (incr_freeL 0 m Q) nil m); intros.
    apply H1; try easy.
    clear H1 H.
    specialize(app_nil_r (false_list m)); intros.
    rewrite H in H0. easy.
  Qed.
  
  Lemma guardLS_subst : forall P Q xl xe xr m, guardLS (xl ++ [xe] ++ xr) P -> guardLS nil Q -> guardLS (xl ++ xr) (substitutionL (length xl) m Q P).
  Proof.
    induction P using local_ind_ref; intros; try easy.
    - specialize(guardLS_inv_var (xl ++ [xe] ++ xr) (l_var n) n); intros.
      assert(bmerge (boollis n) (xl ++ [xe] ++ xr) = xl ++ [xe] ++ xr).
      apply H1; try easy.
      clear H1 H.
      simpl.
      destruct n.
      - destruct xl; try easy.
        - simpl.
          apply gls_sub with nil; try easy.
          destruct xr; try easy.
          apply guardLS_freeS; try easy.
        - simpl.
          inversion H2.
          apply gls_sub with (boollis 0).
          - simpl. destruct xl; try easy.
            destruct xr; try easy.
          - constructor.
      - case_eq (Nat.eqb (length xl) (S n)); intros.
        - apply gls_sub with nil; try easy.
          - destruct xl; try easy.
          - apply guardLS_freeS; try easy.
        clear H0. clear m Q.
        case_eq (Nat.leb (length xl) (S n)); intros.
        - revert H0 H H2. revert xe xr n.
          induction xl; intros; try easy. 
          - inversion H2. 
            rewrite H3.
            apply gls_sub with (boollis n); try easy.
            constructor.
          - destruct n; try easy.
            destruct xl; try easy.
            inversion H2.
            specialize(IHxl xe xr n H0 H H3).
            specialize(guardLS_inv_var (xl ++ xr) (l_var n) n); intros.
            assert(bmerge (boollis n) (xl ++ xr) = xl ++ xr).
            apply H1; try easy. clear H1 IHxl.
            apply gls_sub with (boollis (S n)); try easy.
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
            apply gls_sub with (boollis 0); try easy.
            - destruct xl; try easy. 
              destruct xr; try easy.
            - constructor.
          - inversion H2. 
            specialize(IHxl n xe xr H1 H0).
            specialize(guardLS_inv_var (xl ++ xr) (l_var n) n); intros.
            assert(bmerge (boollis n) (xl ++ xr) = xl ++ xr).
            apply H; try easy. clear H IHxl.
            apply gls_sub with (boollis (S n)).
            - simpl. rewrite H3. easy.
            - constructor.
    - apply gls_sub with nil; try easy.
      destruct xl; try easy. destruct xr; try easy.
      constructor.
    - apply gls_sub with nil.
      - destruct xl; try easy. destruct xr; try easy.
      specialize(guardLS_inv_send (xl ++ [xe] ++ xr) (l_send p lis) p lis); intros.
      assert(exists ys : slist (seq.seq bool),
       SForall2 (fun (u : seq.seq bool) (v : sort * local) => guardLS u v.2) ys lis).
      apply H2; try easy. clear H2.
      destruct H3 as (ys, Ha). clear H0.
      revert H H1 Ha.
      revert Q xl m ys. clear xe xr.
      induction lis; intros; try easy.
      - inversion Ha. subst. clear Ha.
        inversion H. subst. clear H.
        simpl.
        specialize(guardLS_any_length a.2 x (length xl) H3); intros.
        destruct H as (xl0,(xe0,(xr0,(Ha,Hb)))).
        rewrite (esym Ha).
        apply gls_send with (slist_x (xl0 ++ xr0)); try easy.
        constructor; try easy.
        apply H2 with (xe := xe0); try easy.
      inversion Ha.
      - subst. clear Ha.
        inversion H. subst. clear H.
        simpl in *.
        specialize(IHlis Q xl m xs H6 H1 H5).
        clear H6 H5.
        specialize(guardLS_inv_send nil (l_send p (smap (fun u : sort * local => (u.1, substitutionL (length xl) m Q u.2)) lis)) p (smap (fun u : sort * local => (u.1, substitutionL (length xl) m Q u.2)) lis)); intros.
        assert(exists ys : slist (seq.seq bool),
      SForall2 (fun (u : seq.seq bool) (v : sort * local) => guardLS u v.2) ys
        (smap (fun u : sort * local => (u.1, substitutionL (length xl) m Q u.2)) lis)).
        apply H; try easy. clear H.
        destruct H0 as (ys, Ha). clear IHlis.
        specialize(guardLS_any_length y.2 x (length xl) H4); intros.
        destruct H as (xl0,(xe0,(xr0,(Hb,Hc)))).
        apply gls_send with (slist_xs (Some (xl0 ++ xr0)) ys).
        constructor; try easy.
        rewrite (esym Hb). apply H3 with (xe := xe0); try easy.
      - subst. clear Ha.
        inversion H. subst. clear H.
        simpl in *.
        specialize(IHlis Q xl m xs H2 H1 H3).
        simpl in *.
        specialize(guardLS_inv_send nil (l_send p (smap (fun u : sort * local => (u.1, substitutionL (length xl) m Q u.2)) lis)) p (smap (fun u : sort * local => (u.1, substitutionL (length xl) m Q u.2)) lis)); intros.
        assert(exists ys : slist (seq.seq bool),
      SForall2 (fun (u : seq.seq bool) (v : sort * local) => guardLS u v.2) ys
        (smap (fun u : sort * local => (u.1, substitutionL (length xl) m Q u.2)) lis)).
        apply H; try easy. clear H.
        destruct H0 as (ys, Ha). clear IHlis.
        apply gls_send with (slist_xs None ys).
        constructor; try easy.
    - apply gls_sub with nil.
      - destruct xl; try easy. destruct xr; try easy.
      specialize(guardLS_inv_recv (xl ++ [xe] ++ xr) (l_recv p lis) p lis); intros.
      assert(exists ys : slist (seq.seq bool),
       SForall2 (fun (u : seq.seq bool) (v : sort * local) => guardLS u v.2) ys lis).
      apply H2; try easy. clear H2.
      destruct H3 as (ys, Ha). clear H0.
      revert H H1 Ha.
      revert Q xl m ys. clear xe xr.
      induction lis; intros; try easy.
      - inversion Ha. subst. clear Ha.
        inversion H. subst. clear H.
        simpl.
        specialize(guardLS_any_length a.2 x (length xl) H3); intros.
        destruct H as (xl0,(xe0,(xr0,(Ha,Hb)))).
        rewrite (esym Ha).
        apply gls_recv with (slist_x (xl0 ++ xr0)); try easy.
        constructor; try easy.
        apply H2 with (xe := xe0); try easy.
      inversion Ha.
      - subst. clear Ha.
        inversion H. subst. clear H.
        simpl in *.
        specialize(IHlis Q xl m xs H6 H1 H5).
        clear H6 H5.
        specialize(guardLS_inv_recv nil (l_recv p (smap (fun u : sort * local => (u.1, substitutionL (length xl) m Q u.2)) lis)) p (smap (fun u : sort * local => (u.1, substitutionL (length xl) m Q u.2)) lis)); intros.
        assert(exists ys : slist (seq.seq bool),
      SForall2 (fun (u : seq.seq bool) (v : sort * local) => guardLS u v.2) ys
        (smap (fun u : sort * local => (u.1, substitutionL (length xl) m Q u.2)) lis)).
        apply H; try easy. clear H.
        destruct H0 as (ys, Ha). clear IHlis.
        specialize(guardLS_any_length y.2 x (length xl) H4); intros.
        destruct H as (xl0,(xe0,(xr0,(Hb,Hc)))).
        apply gls_recv with (slist_xs (Some (xl0 ++ xr0)) ys).
        constructor; try easy.
        rewrite (esym Hb). apply H3 with (xe := xe0); try easy.
      - subst. clear Ha.
        inversion H. subst. clear H.
        simpl in *.
        specialize(IHlis Q xl m xs H2 H1 H3).
        simpl in *.
        specialize(guardLS_inv_recv nil (l_recv p (smap (fun u : sort * local => (u.1, substitutionL (length xl) m Q u.2)) lis)) p (smap (fun u : sort * local => (u.1, substitutionL (length xl) m Q u.2)) lis)); intros.
        assert(exists ys : slist (seq.seq bool),
      SForall2 (fun (u : seq.seq bool) (v : sort * local) => guardLS u v.2) ys
        (smap (fun u : sort * local => (u.1, substitutionL (length xl) m Q u.2)) lis)).
        apply H; try easy. clear H.
        destruct H0 as (ys, Ha). clear IHlis.
        apply gls_recv with (slist_xs None ys).
        constructor; try easy.
    - specialize(guardLS_inv_rec (xl ++ [xe] ++ xr) (l_rec P) P); intros.
      assert (guardLS (false :: xl ++ [xe] ++ xr) P).
      apply H1; try easy. clear H1.
      simpl.
      apply gls_rec1.
      specialize(IHP Q (false :: xl) xe xr).
      apply IHP; try easy.
  Qed.
  
  Lemma guardL_to_GS : forall xs P, guardL xs P -> guardLS xs P.
  Proof.
    intros xs P. revert xs.
    induction P using local_ind_ref; intros; try easy.
    - inversion H.
      constructor.
    - inversion H.
      constructor.
    - inversion H0. subst.
      clear H0.
      revert H3 H.
      revert p zs.
      induction lis; intros; try easy.
      - inversion H3. subst. clear H3.
        inversion H. subst. clear H.
        specialize(H1 x H2).
        apply gls_send with (slist_x x).
        constructor. easy.
      inversion H3.
      - subst. clear H3.
        inversion H. subst. clear H.
        specialize(H2 x H4). clear H4.
        apply gls_send with (slist_xs (Some x) xs).
        constructor; try easy.
        revert H3 H5. clear IHlis H2. clear p x y.
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
        apply gls_send with (slist_xs None xs); try easy.
        constructor; try easy.
        revert H1 H2. 
        clear IHlis. clear p. revert xs.
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
    - inversion H0. subst.
      clear H0.
      revert H3 H.
      revert p zs.
      induction lis; intros; try easy.
      - inversion H3. subst. clear H3.
        inversion H. subst. clear H.
        specialize(H1 x H2).
        apply gls_recv with (slist_x x).
        constructor. easy.
      inversion H3.
      - subst. clear H3.
        inversion H. subst. clear H.
        specialize(H2 x H4). clear H4.
        apply gls_recv with (slist_xs (Some x) xs).
        constructor; try easy.
        revert H3 H5. clear IHlis H2. clear p x y.
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
        apply gls_recv with (slist_xs None xs); try easy.
        constructor; try easy.
        revert H1 H2. 
        clear IHlis. clear p. revert xs.
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
      - apply gls_rec0.
        apply IHP; try easy.
      - subst.
        apply gls_rec1.
        apply IHP; try easy.
  Qed. 
        
  Lemma guardLS_to_G : forall xs P, guardLS xs P -> exists ys, bmerge ys xs = xs /\ guardL ys P.
  Proof.
    intros xs P. revert xs.
    induction P using local_ind_ref; intros; try easy.
    - specialize(guardLS_inv_var xs (l_var n) n); intros.
      assert(bmerge (boollis n) xs = xs). apply H0; try easy.
      clear H0.
      exists (boollis n).
      split. easy. constructor.
    - exists nil.
      split. destruct xs; try easy.
      constructor.
    - specialize(guardLS_inv_send xs (l_send p lis) p lis); intros.
      assert(exists ys : slist (seq.seq bool),
       SForall2 (fun (u : seq.seq bool) (v : sort * local) => guardLS u v.2) ys lis). apply H1; try easy. clear H1 H0.
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
          apply gl_send with (slist_x ys); try easy.
          constructor; try easy.
        inversion Ha.
        - subst. clear Ha.
          inversion H. subst. clear H.
          specialize(IHlis xs H4 H5).
          inversion IHlis. subst.
          clear H5 H4.
          specialize(H2 x H3). destruct H2 as (ys,(Ha,Hb)).
          apply gl_send with (slist_xs (Some ys) zs).
          constructor; try easy.
        - subst. clear Ha.
          inversion H. subst. clear H.
          specialize(IHlis xs H2 H1).
          inversion IHlis. subst.
          clear H2 H1.
          apply gl_send with (slist_xs None zs).
          constructor; try easy.
    - specialize(guardLS_inv_recv xs (l_recv p lis) p lis); intros.
      assert(exists ys : slist (seq.seq bool),
       SForall2 (fun (u : seq.seq bool) (v : sort * local) => guardLS u v.2) ys lis). apply H1; try easy. clear H1 H0.
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
          apply gl_recv with (slist_x ys); try easy.
          constructor; try easy.
        inversion Ha.
        - subst. clear Ha.
          inversion H. subst. clear H.
          specialize(IHlis xs H4 H5).
          inversion IHlis. subst.
          clear H5 H4.
          specialize(H2 x H3). destruct H2 as (ys,(Ha,Hb)).
          apply gl_recv with (slist_xs (Some ys) zs).
          constructor; try easy.
        - subst. clear Ha.
          inversion H. subst. clear H.
          specialize(IHlis xs H2 H1).
          inversion IHlis. subst.
          clear H2 H1.
          apply gl_recv with (slist_xs None zs).
          constructor; try easy.
    - specialize(guardLS_inv_rec xs (l_rec P) P); intros.
      assert(guardLS (false :: xs) P).
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
        apply gl_rec1; try easy.
        destruct b; try easy.
  Qed.
  
  Lemma guardL_subst : forall P, guardL nil (l_rec P) -> guardL nil (substitutionL 0 0 (l_rec P) P).
  Proof.
    intros.
    specialize(guardL_to_GS nil (l_rec P) H); intros. clear H.
    specialize(guardLS_inv_rec [] (l_rec P) P); intros.
    assert(guardLS [false] P). apply H; try easy.
    clear H.
    specialize(guardLS_subst P (l_rec P) nil false nil 0); intros.
    assert(guardLS nil (substitutionL 0 0 (l_rec P) P)).
    apply H; try easy. clear H.
    specialize(guardLS_to_G nil (substitutionL 0 0 (l_rec P) P) H2); intros.
    destruct H as (ys,(Hb,Hc)).
    destruct ys; try easy.
  Qed.
  
  Lemma guard_less_closedL : forall P xs ys, guardL xs P -> closedL ys P -> bmerge xs ys = ys.
  Proof.
    induction P using local_ind_ref; intros; try easy.
    - inversion H. subst.
      inversion H0. subst.
      clear H H0.
      induction n; intros; try easy.
      - simpl. 
        replace (bmerge (boollis n) (boollis n)) with (boollis n) in *. easy.
    - inversion H. subst.
      inversion H0. subst. easy.
    - inversion H0. subst.
      clear H H0 H1 H4. clear p lis zs.
      induction ys; intros; try easy.
    - inversion H0. subst.
      clear H H0 H1 H4. clear p lis zs.
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

  Definition cguardedL P := closedL nil P /\ guardL nil P.


  Lemma cguardedL_rec : forall G, cguardedL (l_rec G) -> cguardedL (substitutionL 0 0 (l_rec G) G).
  Proof.
    intros.
    unfold cguardedL in *. destruct H.
    split.
    apply closedL_subst. easy.
    apply guardL_subst. easy.
  Qed.

  Lemma cguardedL_cont_send : forall p lis, cguardedL (l_send p lis) -> SForall (fun u => cguardedL (snd u)) lis.
  Proof.  
    intros.
    unfold cguardedL in *.
    destruct H.
    inversion H. subst.
    inversion H0. subst.
    clear H H0. clear p.
    revert H5 H1 H3. revert zs zs0.
    induction lis; intros.
    - destruct zs; try easy.
      destruct zs0; try easy.
      inversion H3. subst. clear H3.
      inversion H5. subst. clear H5.
      destruct l; try easy.
      specialize(guard_less_closedL a.2 l0 nil H3 H2); intros.
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
          specialize(guard_less_closedL y.2 x0 nil H3 H4); intros.
          destruct x0; try easy.
      - subst.
        clear H3.
        inversion H5. subst. clear H5.
        simpl in H1. 
        specialize(IHlis zs zs0 H2 H1 H0).
        simpl.
        constructor; try easy.
  Qed.
  
  Lemma cguardedL_cont_recv : forall p lis, cguardedL (l_recv p lis) -> SForall (fun u => cguardedL (snd u)) lis.
  Proof.  
    intros.
    unfold cguardedL in *.
    destruct H.
    inversion H. subst.
    inversion H0. subst.
    clear H H0. clear p.
    revert H5 H1 H3. revert zs zs0.
    induction lis; intros.
    - destruct zs; try easy.
      destruct zs0; try easy.
      inversion H3. subst. clear H3.
      inversion H5. subst. clear H5.
      destruct l; try easy.
      specialize(guard_less_closedL a.2 l0 nil H3 H2); intros.
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
          specialize(guard_less_closedL y.2 x0 nil H3 H4); intros.
          destruct x0; try easy.
      - subst.
        clear H3.
        inversion H5. subst. clear H5.
        simpl in H1. 
        specialize(IHlis zs zs0 H2 H1 H0).
        simpl.
        constructor; try easy.
  Qed.

  
  Fixpoint mu_height (G : local) : fin := 
    match G with
      | l_rec _G => S (mu_height _G)
      | _        => 0
    end.
    
  Lemma mu_height_after_subst : forall G G' ys x n, guardLS ys G -> nth x ys false = false -> mu_height G = mu_height (substitutionL x n G' G).
  Proof.
    induction G; intros.
    - simpl.
      specialize(guardLS_inv_var ys (l_var n) n); intros. 
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
    - easy.
    - simpl.
      specialize(guardLS_inv_rec ys (l_rec G) G); intros.
      assert(guardLS (false :: ys) G). apply H1; try easy. clear H1 H.
      specialize(IHG G' (false :: ys) x.+1 n.+1).
      assert(mu_height G = mu_height (substitutionL x.+1 n.+1 G' G)).
      apply IHG; try easy. simpl. rewrite H. easy.
  Qed.
  
  Lemma mu_height_after_subst_s : forall G, guardLS nil (l_rec G) -> mu_height G = mu_height (substitutionL 0 0 (l_rec G) G).
  Proof.
    intros.
    specialize(guardLS_inv_rec nil (l_rec G) G); intros.
    assert(guardLS [false] G). apply H0; try easy. clear H0.
    apply mu_height_after_subst with [false]; try easy.
  Qed.
  
  Lemma cguardedL_mu_rec : forall G, cguardedL (l_rec G) -> mu_height G = mu_height (substitutionL 0 0 (l_rec G) G).
  Proof.
    intros. apply mu_height_after_subst_s.
    unfold cguardedL in H. destruct H.
    apply guardL_to_GS. easy.
  Qed.
 
  Definition unfold_recL (G : local) : local := 
    match G with 
      | l_rec G' => substitutionL 0 0 (l_rec G') G'
      | _        => G
    end.
    
  Definition unravelL (G : local) : local := 
    iter (mu_height G) unfold_recL G.
  
  CoFixpoint local_to_ltt (G : local) : ltt :=
    match unravelL G with 
      | l_send p xs => ltt_send p (fun n => match onth n xs with 
                                        | Some (s, g) => Some (s, local_to_ltt g)
                                        | None        => None
                                      end)
      | l_recv p xs => ltt_recv p (fun n => match onth n xs with 
                                        | Some (s, g) => Some (s, local_to_ltt g)
                                        | None        => None
                                      end)
      | _     => ltt_end
    end.
    
  Lemma cguardedL_unfolds : forall G, cguardedL G -> cguardedL (unravelL G) /\ betaL G (unravelL G) /\ (unravelL G = l_end \/ exists p lis, unravelL G = l_send p lis \/ unravelL G = l_recv p lis).
  Proof.
    intros.
    specialize(always_exists (mu_height G)); intros.
    destruct H0 as (n, Ha). revert H Ha. revert G.
    induction n; intros.
    - unfold unravelL. rewrite Ha. simpl.
      split. easy. split. constructor.
      unfold cguardedL in H. destruct H.
      destruct G.
      - inversion H. destruct n0; try easy.
      - left. easy.
      - right. exists p. exists s. left. easy.
      - right. exists p. exists s. right. easy.
      - easy.
    - destruct G; try easy. 
      simpl in Ha.
      specialize(cguardedL_rec G H); intros.
      specialize(cguardedL_mu_rec G H); intros.
      rewrite H1 in Ha.
      specialize(IHn (substitutionL 0 0 (l_rec G) G) H0 (eq_add_S (mu_height (substitutionL 0 0 (l_rec G) G)) n Ha)).
      destruct IHn as (Hb,(Hc,Hd)).
      split.
      - clear Hc Hd H H0 Ha.
        unfold unravelL in *. simpl. rewrite H1. easy.
      split.
      - apply lttS; try easy.
        unfold unravelL in *. simpl. rewrite H1. easy.
      - unfold unravelL in *. simpl. rewrite H1. easy.
  Qed.
    
  Theorem cguardedL_to_ltt : forall G, cguardedL G -> lttTC G (local_to_ltt G).
  Proof.
    pcofix CIH.
    induction G using local_ind_ref; intros.
    - unfold cguardedL in H0. destruct H0.
      inversion H0. destruct n0; try easy.
    - pfold. 
      rewrite (ltt_eq (local_to_ltt l_end)).
      unfold local_to_ltt. simpl. constructor.
    - pfold.
      rewrite (ltt_eq (local_to_ltt (l_send p lis))).
      unfold local_to_ltt. simpl. constructor.
      intros.
      specialize(always_exists (onth n lis)); intros.
      destruct H1 as (b, Ha). rewrite Ha.
      destruct b.
      - right. destruct p0. exists s. exists l.
        exists ((cofix local_to_ltt (G : local) : ltt :=
        match unravelL G with
        | l_send p0 xs =>
            ltt_send p0 
              (fun n0 : fin =>
               match onth n0 xs with
               | Some (s0, g0) => Some (s0, local_to_ltt g0)
               | None => None
               end)
        | l_recv p0 xs =>
            ltt_recv p0 
              (fun n0 : fin =>
               match onth n0 xs with
               | Some (s0, g0) => Some (s0, local_to_ltt g0)
               | None => None
               end)
        | _ => ltt_end
        end) l).
        split. easy. split. easy.
        specialize(cguardedL_cont_send p lis H0); intros. clear H0.
        
        revert H1 H Ha. revert s l lis. clear p.
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
          specialize(IHn s l lis). 
          apply IHn; try easy.
          - inversion H1; try easy.
          - inversion H; try easy.
      - left. easy.
    - pfold.
      rewrite (ltt_eq (local_to_ltt (l_recv p lis))).
      unfold local_to_ltt. simpl. constructor.
      intros.
      specialize(always_exists (onth n lis)); intros.
      destruct H1 as (b, Ha). rewrite Ha.
      destruct b.
      - right. destruct p0. exists s. exists l.
        exists ((cofix local_to_ltt (G : local) : ltt :=
        match unravelL G with
        | l_send p0 xs =>
            ltt_send p0 
              (fun n0 : fin =>
               match onth n0 xs with
               | Some (s0, g0) => Some (s0, local_to_ltt g0)
               | None => None
               end)
        | l_recv p0 xs =>
            ltt_recv p0 
              (fun n0 : fin =>
               match onth n0 xs with
               | Some (s0, g0) => Some (s0, local_to_ltt g0)
               | None => None
               end)
        | _ => ltt_end
        end) l).
        split. easy. split. easy.
        specialize(cguardedL_cont_recv p lis H0); intros. clear H0.
        
        revert H1 H Ha. revert s l lis. clear p.
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
          specialize(IHn s l lis). 
          apply IHn; try easy.
          - inversion H1; try easy.
          - inversion H; try easy.
      - left. easy.
    - pfold.
      rewrite (ltt_eq (local_to_ltt (l_rec G))).
      clear IHG.
      simpl.
      
      specialize(cguardedL_unfolds (l_rec G) H0); intros.
      destruct H as (Ha,(Hb,Hc)).
      destruct Hc.
      - rewrite H. rewrite H in Ha Hb.
        
        specialize(lttTC_after_beta (l_rec G) l_end ltt_end r); intros.
        assert(paco2 lttT r (l_rec G) ltt_end).
        {
          apply H1; try easy.
          pfold. constructor.
        }
        punfold H2.
        apply lttT_mon.
      - destruct H as (p,(lis,Hc)).
        destruct Hc as [Hc | Hc].
        - rewrite Hc.
          rewrite Hc in Ha Hb.
          
          specialize(lttTC_after_beta (l_rec G) (l_send p lis) (ltt_send p
       (fun n : fin =>
        match onth n lis with
        | Some (s, g) => Some (s, local_to_ltt g)
        | None => None
        end)) r); intros.
          assert(paco2 lttT r (l_rec G)
        (ltt_send p
           (fun n : fin =>
            match onth n lis with
            | Some (s, g) => Some (s, local_to_ltt g)
            | None => None
            end))).
          {
            apply H; try easy.
            clear H.
            pfold. constructor.
            specialize(cguardedL_cont_send p lis Ha); intros. 
            clear Hc Ha Hb H0.
            specialize(always_exists (onth n lis)); intros.
            destruct H0 as (b,Ha). rewrite Ha.
            destruct b.
            - right. destruct p0.
              exists s. exists l. exists (local_to_ltt l).
              split. easy. split. easy.
              right. apply CIH.
              clear CIH p G. clear r.
              revert Ha H. revert s l lis.
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
                specialize(IHn s l lis). apply IHn; try easy.
                inversion H; try easy.
            - left. easy.
          }
          punfold H1. 
          apply lttT_mon.
        - rewrite Hc.
          rewrite Hc in Ha Hb.
          
          specialize(lttTC_after_beta (l_rec G) (l_recv p lis) (ltt_recv p
       (fun n : fin =>
        match onth n lis with
        | Some (s, g) => Some (s, local_to_ltt g)
        | None => None
        end)) r); intros.
          assert(paco2 lttT r (l_rec G)
        (ltt_recv p
           (fun n : fin =>
            match onth n lis with
            | Some (s, g) => Some (s, local_to_ltt g)
            | None => None
            end))).
          {
            apply H; try easy.
            clear H.
            pfold. constructor.
            specialize(cguardedL_cont_recv p lis Ha); intros. 
            clear Hc Ha Hb H0.
            specialize(always_exists (onth n lis)); intros.
            destruct H0 as (b,Ha). rewrite Ha.
            destruct b.
            - right. destruct p0.
              exists s. exists l. exists (local_to_ltt l).
              split. easy. split. easy.
              right. apply CIH.
              clear CIH p G. clear r.
              revert Ha H. revert s l lis.
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
                specialize(IHn s l lis). apply IHn; try easy.
                inversion H; try easy.
            - left. easy.
          }
          punfold H1. 
          apply lttT_mon.
  Qed.
  
  
  Lemma dec_guard_nguardL : forall G, (exists xs, guardL xs G) \/ (exists w, nguardL w G).
  Proof.
    induction G using local_ind_ref; intros.
    - left. exists (boollis n). constructor.
    - left. exists nil. constructor.
    - induction lis; intros.
      - inversion H. subst.
        destruct H1.
        - left. exists nil.
          destruct H0 as (xs, Ha).
          apply gl_send with (zs := slist_x xs).
          constructor; try easy.
        - right.
          destruct H0 as (w, Ha). 
          destruct a.
          exists (Some 0 :: w).
          apply ngl_send with (n := 0) (s := s) (g := l); try easy.
      inversion H.
      - subst. clear H.
        specialize(IHlis H3). clear H3.
        destruct IHlis.
        - destruct H as (ys, Hb).
          destruct H2.
          - destruct H as (xs, Ha). destruct x.
            left.
            inversion Hb. subst. exists nil.
            apply gl_send with (slist_xs (Some xs) zs). 
            constructor; try easy.
          - destruct x.
            destruct H as (w, Ha). 
            right.
            exists (Some 0 :: w).
            apply ngl_send with (n := 0) (s := s) (g := l); try easy.
        - inversion H.
          - inversion H0.
          - subst.
            right.
            exists (Some (S n) :: w). 
            apply ngl_send with (n := S n) (s := s) (g := g); try easy.
      - subst. clear H.
        specialize(IHlis H1). clear H1.
        destruct IHlis.
        - destruct H as (xs, Ha).
          left. exists nil.
          inversion Ha. subst.
          apply gl_send with (slist_xs None zs).
          constructor; try easy.
        - right.
          inversion H. 
          - inversion H0.
          - subst.
            exists (Some (S n) :: w).
            apply ngl_send with (n := S n) (s := s) (g := g); try easy.
    - induction lis; intros.
      - inversion H. subst.
        destruct H1.
        - left. exists nil.
          destruct H0 as (xs, Ha).
          apply gl_recv with (zs := slist_x xs).
          constructor; try easy.
        - right.
          destruct H0 as (w, Ha). 
          destruct a.
          exists (Some 0 :: w).
          apply ngl_recv with (n := 0) (s := s) (g := l); try easy.
      inversion H.
      - subst. clear H.
        specialize(IHlis H3). clear H3.
        destruct IHlis.
        - destruct H as (ys, Hb).
          destruct H2.
          - destruct H as (xs, Ha). destruct x.
            left.
            inversion Hb. subst. exists nil.
            apply gl_recv with (slist_xs (Some xs) zs). 
            constructor; try easy.
          - destruct x.
            destruct H as (w, Ha). 
            right.
            exists (Some 0 :: w).
            apply ngl_recv with (n := 0) (s := s) (g := l); try easy.
        - inversion H.
          - inversion H0.
          - subst.
            right.
            exists (Some (S n) :: w). 
            apply ngl_recv with (n := S n) (s := s) (g := g); try easy.
      - subst. clear H.
        specialize(IHlis H1). clear H1.
        destruct IHlis.
        - destruct H as (xs, Ha).
          left. exists nil.
          inversion Ha. subst.
          apply gl_recv with (slist_xs None zs).
          constructor; try easy.
        - right.
          inversion H. 
          - inversion H0.
          - subst.
            exists (Some (S n) :: w).
            apply ngl_recv with (n := S n) (s := s) (g := g); try easy.
  - destruct IHG.
    - destruct H.
      destruct x.
      - left. exists nil. constructor. easy.
      destruct b.
      - right. exists nil. apply ngl_init with x; try easy. 
      - left. exists x. constructor. easy.
    - right. destruct H as (w, Ha). exists (None :: w). constructor. easy.
Qed.


Lemma dec_closedL : forall G, exists xs, closedL xs G.
Proof.
  induction G using local_ind_ref; intros.
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
    - exists x. apply cl_rec1 with b; try easy.
Qed.
    

(* Path witness through local syntax with recursion-depth index. *)
Inductive local_path_c : list (option fin) -> fin -> local -> Prop :=
  | gpathc_init : forall n m, m <= n -> local_path_c nil m (l_var n)
  | gpathc_send : forall p xs n s g w m, onth n xs = Some(s, g) -> local_path_c w m g -> local_path_c (Some n :: w) m (l_send p xs)
  | gpathc_recv : forall p xs n s g w m, onth n xs = Some(s, g) -> local_path_c w m g -> local_path_c (Some n :: w) m (l_recv p xs)
  | gpathc_mu   : forall w m g, local_path_c w (S m) g -> local_path_c (None :: w) m (l_rec g).

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

Lemma closedL_to_path : forall G xl xr, xr <> nil -> closedL (xl ++ xr) G -> exists w, local_path_c w (length xl) G.
Proof.
  induction G using local_ind_ref; intros.
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
      apply gpathc_send with (s := s) (g := l); try easy.
    inversion H4.
    - subst. clear H4. 
      inversion H. subst. clear H.
      simpl in H2.
      specialize(bmerge_split_app x (bmergelis xs) xl xr H2); intros.
      destruct H as (xa,(xb,(Ha,(Hb,Hc)))).
      destruct Hc.
      - subst.
        specialize(H4 xa xb).
        assert(exists w : seq.seq (option fin), local_path_c w (length xa) y.2).
        {
          apply H4; try easy.
          destruct xb; try easy. destruct xr; try easy.
        }
        destruct H as (w,Hd).
        exists (Some 0 :: w). destruct y.
        apply gpathc_send with (s := s) (g := l); try easy.
        rewrite Ha in Hd. easy.
      - clear H2 H6 H4.
        specialize(IHlis xa xb xs).
        assert(exists w : seq.seq (option fin), local_path_c w (length xa) (l_send p lis)).
        {
          apply IHlis; try easy.
          destruct xb; try easy. destruct xr; try easy.
        }
        destruct H1 as (w,Hd).
        inversion Hd. subst.
        exists (Some (S n) :: w0).
        apply gpathc_send with (s := s) (g := g); try easy.
        rewrite Ha in H8. easy.
    - subst. clear H4.
      inversion H. subst. clear H.
      simpl in H2.
      specialize(IHlis xl xr xs H3 H0 H5 H2).
      destruct IHlis as (w,Ha). clear H2 H5 H3.
      inversion Ha. subst. clear Ha.
      exists (Some (S n) :: w0).
      apply gpathc_send with (s := s) (g := g); try easy.
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
      apply gpathc_recv with (s := s) (g := l); try easy.
    inversion H4.
    - subst. clear H4. 
      inversion H. subst. clear H.
      simpl in H2.
      specialize(bmerge_split_app x (bmergelis xs) xl xr H2); intros.
      destruct H as (xa,(xb,(Ha,(Hb,Hc)))).
      destruct Hc.
      - subst.
        specialize(H4 xa xb).
        assert(exists w : seq.seq (option fin), local_path_c w (length xa) y.2).
        {
          apply H4; try easy.
          destruct xb; try easy. destruct xr; try easy.
        }
        destruct H as (w,Hd).
        exists (Some 0 :: w). destruct y.
        apply gpathc_recv with (s := s) (g := l); try easy.
        rewrite Ha in Hd. easy.
      - clear H2 H6 H4.
        specialize(IHlis xa xb xs).
        assert(exists w : seq.seq (option fin), local_path_c w (length xa) (l_recv p lis)).
        {
          apply IHlis; try easy.
          destruct xb; try easy. destruct xr; try easy.
        }
        destruct H1 as (w,Hd).
        inversion Hd. subst.
        exists (Some (S n) :: w0).
        apply gpathc_recv with (s := s) (g := g); try easy.
        rewrite Ha in H8. easy.
    - subst. clear H4.
      inversion H. subst. clear H.
      simpl in H2.
      specialize(IHlis xl xr xs H3 H0 H5 H2).
      destruct IHlis as (w,Ha). clear H2 H5 H3.
      inversion Ha. subst. clear Ha.
      exists (Some (S n) :: w0).
      apply gpathc_recv with (s := s) (g := g); try easy.
  - inversion H0.
    - subst. 
      destruct xl; try easy. destruct xr; try easy.
    - subst.
      specialize(IHG (x :: xl) xr H H3).
      destruct IHG as (w, Ha).
      exists (None :: w).
      constructor. easy.
Qed.

Lemma local_path_c_after_subst : forall G w c x G' m, x <= c -> local_path_c w (S c) G -> local_path_c w c (substitutionL x m G' G).
Proof.
  induction G using local_ind_ref; intros.
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
    specialize(SForall_onth n lis (fun u : sort * local =>
       forall (w : seq.seq (option fin)) (c x : fin) (G' : local) (m : fin),
       x <= c -> local_path_c w c.+1 u.2 -> local_path_c w c (substitutionL x m G' u.2)) (s, g) H H6); intros. simpl in H2.
    specialize(H2 w0 c x G' m).
    apply gpathc_send with (n := n) (s := s) (g := (substitutionL x m G' g)); try easy.
    - clear H2 H7 H1 H0 H.
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
  - inversion H1. subst.
    specialize(SForall_onth n lis (fun u : sort * local =>
       forall (w : seq.seq (option fin)) (c x : fin) (G' : local) (m : fin),
       x <= c -> local_path_c w c.+1 u.2 -> local_path_c w c (substitutionL x m G' u.2)) (s, g) H H6); intros. simpl in H2.
    specialize(H2 w0 c x G' m).
    apply gpathc_recv with (n := n) (s := s) (g := (substitutionL x m G' g)); try easy.
    - clear H2 H7 H1 H0 H.
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
      
Lemma lttT_closed_nil : forall G G' xs, lttTC G G' -> closedL xs G -> xs = nil.
Proof.
  intros.
  destruct xs; try easy.
  specialize(closedL_to_path G nil (b ::xs)); intros.
  assert(exists w : seq.seq (option fin), local_path_c w 0 G).
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
      apply lttT_mon.
    - inversion Ha.
      - subst.
        pinversion H. subst. clear H.
        specialize(H4 n). rewrite H2 in H4.
        destruct H4; try easy. destruct H as (s1,(g1,(g2,(Hb,(Hc,Hd))))).
        inversion Hb. subst. clear Hb. pclearbot. 
        specialize(IHw c g1 g2). apply IHw; try easy.
        apply lttT_mon.
      - subst.
        pinversion H. subst. clear H.
        specialize(H4 n). rewrite H2 in H4.
        destruct H4; try easy. destruct H as (s1,(g1,(g2,(Hb,(Hc,Hd))))).
        inversion Hb. subst. clear Hb. pclearbot. 
        specialize(IHw c g1 g2). apply IHw; try easy.
        apply lttT_mon.
      - subst.
        pinversion H. subst.
        specialize(IHw c (substitutionL 0 0 (l_rec g) g) G').
        apply IHw; try easy.
        apply local_path_c_after_subst; try easy.
        pfold. easy.
        apply lttT_mon.
  }
  easy.
Qed.


(* Lemma lttTC_first : forall G n, lttTC (l_rec (l_var n)) G -> False.
Proof.
  intros.
  pinversion H. subst. simpl in *.
  clear H1.
  remember (l_rec (l_var n)) as one eqn:Hone. revert Hone. revert n.  
  induction H; intros; try easy.
  inversion Hone. subst. simpl in IHlttT.
  destruct n.
  - specialize(IHlttT 0). apply IHlttT. easy.
  - simpl in H. inversion H.
  apply lttT_mon.
 *)


Lemma guardL_only_boollis : forall G xs, xs <> nil -> guardL xs G -> exists n, xs = boollis n.
Proof.
  intros. revert H.
  induction H0; intros; try easy.
  - exists n. easy.
  - assert(exists n : fin, false :: xs = boollis n).
    apply IHguardL; try easy. destruct H1 as (n,Ha).
    destruct n; try easy.
    exists n. inversion Ha. easy.
Qed.


Lemma nguardL_canon : forall G, nguardL nil G -> exists G', G = l_rec G' /\ guardL [true] G'.
Proof.  
  intros. inversion H. subst. clear H.
  specialize(guardL_only_boollis P (true :: xs)); intros.
  assert(exists n : fin, true :: xs = boollis n).
  apply H; try easy.
  destruct H1 as (n, Ha). clear H.
  destruct n; try easy. destruct xs; try easy. clear Ha.
  exists P. easy.
Qed.

Inductive only_rec : local -> Prop := 
  | rec_nil : forall n, only_rec (l_rec (l_var n))
  | rec_app : forall G, only_rec G -> only_rec (l_rec G).

Lemma guardL_nonempty_to_rec : forall G xs, xs <> nil -> guardL xs G -> only_rec (l_rec G).
Proof.
  intros. revert H.
  induction H0; intros; try easy.
  - constructor.
  - constructor. apply IHguardL. easy.
Qed.

Lemma nguardL_only_rec : forall G, nguardL nil G -> only_rec G.
Proof.
  intros.
  specialize(nguardL_canon G H); intros.
  destruct H0 as (Gl,(Ha,Hb)). subst.
  specialize(guardL_nonempty_to_rec Gl [true]); intros.
  apply H0; try easy.
Qed.

Lemma only_rec_closed_less_guard : forall G xs ys, only_rec G -> closedL xs G -> guardL ys G -> bmerge xs ys = ys.
Proof. 
  induction G using local_ind_ref; intros; try easy.
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

Lemma nguardL_closed : forall G, nguardL nil G -> closedL nil G.
Proof.
  intros.
  specialize(nguardL_only_rec G H); intros.
  specialize(nguardL_canon G H); intros.
  destruct H1 as (Gl,(Ha,Hb)). subst. clear H.
  specialize(dec_closedL Gl); intros. destruct H as (xs,Ha).
  inversion H0.
  - subst.
    inversion Hb. destruct n0; try easy. subst.
    inversion Ha. subst.
    apply cl_rec1 with true.
    rewrite (esym H1). constructor.
  - subst.
    specialize(only_rec_closed_less_guard Gl xs [true] H1 Ha Hb); intros.
    destruct xs; try easy.
    - constructor; try easy.
    - apply cl_rec1 with b. destruct xs; try easy.
Qed.

Lemma nguardL_subst_same_helper : forall G xs x m G', closedL xs G -> only_rec G -> length xs <= x -> G = substitutionL x m G' G.
Proof.
  induction G using local_ind_ref; intros.
  - inversion H0.
  - inversion H0.
  - inversion H1.
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
      assert(G = (substitutionL x.+1 m.+1 G' G)).
      clear H0.
      inversion H.
      - subst.
        specialize(IHG nil x.+1 m.+1 G' H4 H3).
        apply IHG; try easy.
      - subst.
        apply IHG with (x0 :: xs); try easy.
      rewrite (esym H2). easy.
Qed.

Lemma nguardL_subst_same : forall G x m G', nguardL nil G -> G = substitutionL x m G' G.
Proof.
  intros.
  specialize(nguardL_only_rec G H); intros.
  specialize(nguardL_closed G H); intros. 
  clear H.
  apply nguardL_subst_same_helper with nil; try easy.
Qed.


Lemma only_rec_incr_freeL : forall G m n, only_rec G -> only_rec (incr_freeL m n G).
Proof.
  induction G using local_ind_ref; intros; try easy.
  inversion H.
  - subst. simpl. constructor.
  - subst. simpl. constructor. apply IHG; try easy.
Qed.

Lemma only_rec_subst : forall G G' x m, only_rec G -> only_rec G' -> only_rec (substitutionL x m G' G).
Proof.
  induction G using local_ind_ref; intros; try easy.
  simpl.
  inversion H.
  - subst.
    clear IHG H. simpl.
    destruct n.
    - constructor.
    - case_eq (Nat.eqb x n); intros. constructor.
      apply only_rec_incr_freeL; try easy.
      case_eq (Nat.leb x n); intros; try easy.
      constructor. constructor.
  - subst. constructor.
    apply IHG; try easy.
Qed.

Lemma only_rec_lttT_false : forall G G', only_rec G -> lttTC G G' -> False.
Proof.
  intros.
  punfold H0.
  revert H.
  induction H0; intros.
  - inversion H.
  - inversion H0.
  - inversion H0.
  - inversion H.
    - subst.
      simpl in *.
      destruct n.
      - apply IHlttT; try easy.
      - inversion H0.
    - subst.
      apply IHlttT.
      clear H0 IHlttT.
      specialize(only_rec_subst G (l_rec G) 0 0); intros.
      apply H0; try easy.
  apply lttT_mon.
Qed.

Lemma nguardL_lttT_false : forall G Gl, nguardL nil G -> lttTC G Gl -> False.
Proof.
  intros.
  apply only_rec_lttT_false with G Gl; try easy.
  apply nguardL_only_rec; try easy.
Qed.


Lemma nguardL_subst : forall w G x m G', nguardL w G -> nguardL w (substitutionL x m G' G).
Proof.
  induction w; intros.
  - specialize(nguardL_subst_same G x m G' H); intros. rewrite (esym H0). easy.
  - inversion H. 
    - subst. simpl.
      apply ngl_send with (s := s) (g := substitutionL x m G' g); try easy.
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
      apply ngl_recv with (s := s) (g := substitutionL x m G' g); try easy.
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


Lemma ltt_nguardL_false : forall w G G', nguardL w G -> lttTC G G' -> False.
Proof.
  induction w; intros.
  - specialize(nguardL_lttT_false G G' H H0); intros. easy.
  - inversion H.
    - subst.
      pinversion H0. subst.
      specialize(H6 n). rewrite H3 in H6.
      destruct H6; try easy.
      destruct H1 as (s1,(g1,(g2,(Ha,(Hb,Hc))))). inversion Ha. subst. clear Ha.
      pclearbot.
      specialize(IHw g1 g2 H5 Hc). easy.
      apply lttT_mon.
    - subst.
      pinversion H0. subst.
      specialize(H6 n). rewrite H3 in H6.
      destruct H6; try easy.
      destruct H1 as (s1,(g1,(g2,(Ha,(Hb,Hc))))). inversion Ha. subst. clear Ha.
      pclearbot.
      specialize(IHw g1 g2 H5 Hc). easy.
      apply lttT_mon.
  - subst.
    specialize(nguardL_subst w P 0 0 (l_rec P) H4); intros.
    pinversion H0.
    subst.
    specialize(IHw (substitutionL 0 0 (l_rec P) P) G'). apply IHw; try easy.
    pfold. easy.
    apply lttT_mon.
Qed.



Theorem ltt_to_cguardedL : forall G G', lttTC G G' -> cguardedL G.
Proof. 
  unfold cguardedL.
  intros.
  specialize(dec_closedL G); intros. destruct H0 as (xs, H0).
  specialize(lttT_closed_nil G G' xs H H0); intros. subst.
  split. easy.
  specialize(dec_guard_nguardL G); intros.
  destruct H1.
  - destruct H1 as (xs, Ha).
    specialize(guard_less_closedL G xs nil Ha H0); intros.
    destruct xs; try easy.
  - destruct H1 as (w, Ha).
    specialize(ltt_nguardL_false w G G' Ha H); intros. easy.
Qed.

 
Lemma lttTC_forward : forall G1 G, lttTC G1 G -> lttTC (unravelL G1) G.
Proof.
  intros.
  unfold unravelL.
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
    - subst.
      simpl.
      apply IHx; try easy.
      pfold. easy.
  apply lttT_mon.
Qed.

     
Lemma unravelL_notmu : forall G, cguardedL G -> unravelL G = l_end \/ (exists p lis, unravelL G = l_send p lis \/ unravelL G = l_recv p lis).
Proof.
  intros.
  unfold unravelL.
  specialize(always_exists (mu_height G)); intros.
  destruct H0 as (x, Ha). rewrite Ha. revert Ha H. revert G.
  induction x; intros; try easy.
  - simpl in *.
    destruct G; try easy.
    - destruct H. inversion H. destruct n0; try easy.
    - left. easy.
    - right. exists p. exists s. left. easy.
    - right. exists p. exists s. right. easy. 
  - simpl in *.
    destruct G; try easy.
    inversion Ha.
    specialize(mu_height_after_subst_s G); intros.
    assert(mu_height G = mu_height (substitutionL 0 0 (l_rec G) G)).
    {
      apply H0.
      destruct H.
      specialize(guardL_to_GS); intros.
      apply H3; try easy.
    }
    specialize(IHx (substitutionL 0 0 (l_rec G) G)).
    clear H0. rewrite (esym H2) in IHx.
    rewrite H1 in IHx. rewrite H1.
    apply IHx; try easy.
    clear IHx H2 H1 Ha.
    destruct H. split.
    apply closedL_subst; try easy.
    apply guardL_subst; try easy.
Qed.
 
Lemma regLtt_cont : forall p ys, regLtt (ltt_send p ys) -> (forall n, ys n = None \/ (exists s g, ys n = Some(s, g) /\ regLtt g)).
Proof.
  intros.
  destruct H.
  specialize(lttTC_forward x (ltt_send p ys) H); intros.
  specialize(ltt_to_cguardedL x (ltt_send p ys) H); intros. 
  specialize(unravelL_notmu x H1); intros.
  destruct H2.
  - rewrite H2 in H0.
    pinversion H0.
    apply lttT_mon.
  - destruct H2 as (p1,(lis1,Ha)).
    destruct Ha as [Ha | Ha].
    - rewrite Ha in H0.
      pinversion H0.
      subst.
      specialize(H3 n).
      destruct H3.
      - left. easy.
      - destruct H2 as (s1,(g1,(g2,(Hb,(Hc,Hd))))).
        rewrite Hc. right. exists s1. exists g2.
        split. easy.
        exists g1. pclearbot. easy.
        apply lttT_mon.
    - rewrite Ha in H0.
      pinversion H0.
      apply lttT_mon.
Qed. 

Lemma regLtt_cont_r : forall p ys, regLtt (ltt_recv p ys) -> (forall n, ys n = None \/ (exists s g, ys n = Some(s, g) /\ regLtt g)).
Proof.
  intros.
  destruct H.
  specialize(lttTC_forward x (ltt_recv p ys) H); intros.
  specialize(ltt_to_cguardedL x (ltt_recv p ys) H); intros. 
  specialize(unravelL_notmu x H1); intros.
  destruct H2.
  - rewrite H2 in H0.
    pinversion H0.
    apply lttT_mon.
  - destruct H2 as (p1,(lis1,Ha)).
    destruct Ha as [Ha | Ha].
    - rewrite Ha in H0.
      pinversion H0.
      apply lttT_mon.
    - rewrite Ha in H0.
      pinversion H0.
      subst.
      specialize(H3 n).
      destruct H3.
      - left. easy.
      - destruct H2 as (s1,(g1,(g2,(Hb,(Hc,Hd))))).
        rewrite Hc. right. exists s1. exists g2.
        split. easy.
        exists g1. pclearbot. easy.
        apply lttT_mon.
Qed. 


Lemma lttTC_inv_send : forall p ys, regLtt (ltt_send p ys) -> exists xs, lttTC (l_send p xs) (ltt_send p ys) /\ (forall n, (onth n xs = None /\ ys n = None) \/ (exists s g g', onth n xs = Some(s, g) /\ ys n = Some(s, g') /\ lttTC g g')).
Proof.
  intros. destruct H as (G,H).
  specialize(lttTC_forward G (ltt_send p ys) H); intros. 
  specialize(ltt_to_cguardedL G (ltt_send p ys) H); intros.
  specialize(unravelL_notmu G H1); intros.
  destruct H2.
  - rewrite H2 in H0.
    pinversion H0.
    apply lttT_mon.
  - destruct H2 as (p1,(lis1,Ha)).
    destruct Ha as [Ha | Ha].
    - rewrite Ha in H0. pinversion H0; try easy.
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
      apply lttT_mon.
    - rewrite Ha in H0. pinversion H0; try easy.
      apply lttT_mon.
Qed.


Lemma regLtt_some_cont_send : forall p xs,
    regLtt (ltt_send p xs) -> exists l sg, xs l = Some sg.
Proof.
  intros.
  specialize(lttTC_inv_send p xs H); intros.
  destruct H0 as (xs0,(Ha,Hb)).
  clear Ha H. revert Hb. revert xs.
  induction xs0; intros.
  - specialize(Hb 0).
    destruct Hb; try easy.
    destruct H as (s1,(g1,(g2,(Ha,(Hb,Hc))))).
    exists 0. exists (s1, g2). easy.
  - specialize(IHxs0 (fun n => xs n.+1)).
    assert (exists (l : fin) (sg : sort * ltt), (fun n : fin => xs n.+1) l = Some sg).
    {
      apply IHxs0; try easy.
      intro.
      specialize(Hb (S n)). easy.
    }
    destruct H as (l,(sg,Ha)).
    exists l.+1. exists sg. easy.
Qed.


Lemma lttTC_inv_recv : forall p ys, regLtt (ltt_recv p ys) -> exists xs, lttTC (l_recv p xs) (ltt_recv p ys) /\ (forall n, (onth n xs = None /\ ys n = None) \/ (exists s g g', onth n xs = Some(s, g) /\ ys n = Some(s, g') /\ lttTC g g')).
Proof.
  intros. destruct H as (G,H).
  specialize(lttTC_forward G (ltt_recv p ys) H); intros. 
  specialize(ltt_to_cguardedL G (ltt_recv p ys) H); intros.
  specialize(unravelL_notmu G H1); intros.
  destruct H2.
  - rewrite H2 in H0.
    pinversion H0.
    apply lttT_mon.
  - destruct H2 as (p1,(lis1,Ha)).
    destruct Ha as [Ha | Ha].
    - rewrite Ha in H0. pinversion H0; try easy.
      apply lttT_mon.
    - rewrite Ha in H0. pinversion H0; try easy.
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
      apply lttT_mon.
   
Qed.


Lemma regLtt_some_cont_recv : forall p xs,
    regLtt (ltt_recv p xs) -> exists l sg, xs l = Some sg.
Proof.
  intros.
  specialize(lttTC_inv_recv p xs H); intros.
  destruct H0 as (xs0,(Ha,Hb)).
  clear Ha H. revert Hb. revert xs.
  induction xs0; intros.
  - specialize(Hb 0).
    destruct Hb; try easy.
    destruct H as (s1,(g1,(g2,(Ha,(Hb,Hc))))).
    exists 0. exists (s1, g2). easy.
  - specialize(IHxs0 (fun n => xs n.+1)).
    assert (exists (l : fin) (sg : sort * ltt), (fun n : fin => xs n.+1) l = Some sg).
    {
      apply IHxs0; try easy.
      intro.
      specialize(Hb (S n)). easy.
    }
    destruct H as (l,(sg,Ha)).
    exists l.+1. exists sg. easy.
Qed.
End local.



#[export] Hint Resolve lttT_mon : mon.













Definition unfoldL (L : local) : option local :=
  match unravelL L with
  | l_end => Some l_end
  | l_send p xs => Some (l_send p xs)
  | l_recv p xs => Some (l_recv p xs)
  | _ => None
  end.

CoInductive optionalL : local -> ltt -> Prop :=
| optionalL_end : forall L,
    unfoldL L = Some l_end ->
    optionalL L ltt_end
| optionalL_send : forall L p xs ys,
    unfoldL L = Some (l_send p xs) ->
    (forall n,
      (onth n xs = None /\ ys n = None) \/
      exists s l t,
        onth n xs = Some (s, l) /\
        ys n = Some (s, t) /\ optionalL l t) ->
    optionalL L (ltt_send p ys)
| optionalL_recv : forall L p xs ys,
    unfoldL L = Some (l_recv p xs) ->
    (forall n,
      (onth n xs = None /\ ys n = None) \/
      exists s l t,
        onth n xs = Some (s, l) /\
        ys n = Some (s, t) /\ optionalL l t) ->
    optionalL L (ltt_recv p ys).

Lemma unfoldL_some : forall L H,
  unfoldL L = Some H -> unravelL L = H.
Proof.
  intros L H E.
  unfold unfoldL in E.
  destruct (unravelL L); inversion E; reflexivity.
Qed.

Lemma betaL_iter : forall n L,
  betaL L (header.iter n unfold_recL L).
Proof.
  induction n as [|n IH]; intro L; simpl.
  - constructor.
  - destruct L; simpl; try apply IH.
    apply lttS. apply IH.
Qed.

Lemma betaL_unravel : forall L, betaL L (unravelL L).
Proof.
  intro L. unfold unravelL. apply betaL_iter.
Qed.

Theorem optionalL_to_lttTC : forall L H,
  optionalL L H -> lttTC L H.
Proof.
  unfold lttTC.
  pcofix CIH.
  intros L H HL.
  destruct HL as [L E | L p xs ys E HB | L p xs ys E HB].
  - apply unfoldL_some in E.
    eapply lttTC_after_beta.
    + apply betaL_unravel.
    + rewrite E. pfold. constructor.
  - apply unfoldL_some in E.
    eapply lttTC_after_beta.
    + apply betaL_unravel.
    + rewrite E. pfold. apply lttT_send.
      intro n. destruct (HB n) as [HN | [s [l [t [HX [HY HT]]]]]].
      * left. exact HN.
      * right. exists s, l, t.
        split; [exact HX|]. split; [exact HY|].
        right. apply CIH. exact HT.
  - apply unfoldL_some in E.
    eapply lttTC_after_beta.
    + apply betaL_unravel.
    + rewrite E. pfold. apply lttT_recv.
      intro n. destruct (HB n) as [HN | [s [l [t [HX [HY HT]]]]]].
      * left. exact HN.
      * right. exists s, l, t.
        split; [exact HX|]. split; [exact HY|].
        right. apply CIH. exact HT.
Qed.

Theorem lttTC_to_optionalL : forall L H,
  lttTC L H -> optionalL L H.
Proof.
  cofix CIH.
  intros L H HL.
  pose proof (lttTC_forward L H HL) as HH.
  pose proof (ltt_to_cguardedL L H HL) as HW.
  destruct (unravelL_notmu L HW) as [E | [p [xs [E | E]]]].
  - rewrite E in HH.
    apply (@paco2_unfold _ _ _ lttT_mon) in HH.
    inversion HH; subst.
    apply optionalL_end.
    unfold unfoldL. rewrite E. reflexivity.
  - rewrite E in HH.
    apply (@paco2_unfold _ _ _ lttT_mon) in HH.
    inversion HH as [|p' xs' ys HB|p' xs' ys HB|U V HR]; subst.
    eapply optionalL_send.
    + unfold unfoldL. rewrite E. reflexivity.
    + intro n.
      destruct (HB n) as [HN | [s [l [t [HX [HY HT]]]]]].
      * left. exact HN.
      * right. exists s, l, t.
        split; [exact HX|]. split; [exact HY|].
        apply CIH. destruct HT as [HT | HT].
        -- exact HT.
        -- contradiction.
  - rewrite E in HH.
    apply (@paco2_unfold _ _ _ lttT_mon) in HH.
    inversion HH as [|p' xs' ys HB|p' xs' ys HB|U V HR]; subst.
    eapply optionalL_recv.
    + unfold unfoldL. rewrite E. reflexivity.
    + intro n.
      destruct (HB n) as [HN | [s [l [t [HX [HY HT]]]]]].
      * left. exact HN.
      * right. exists s, l, t.
        split; [exact HX|]. split; [exact HY|].
        apply CIH. destruct HT as [HT | HT].
        -- exact HT.
        -- contradiction.
Qed.

Theorem optionalL_equiv : forall L H,
  optionalL L H <-> lttTC L H.
Proof.
  intros L H. split;
    [apply optionalL_to_lttTC | apply lttTC_to_optionalL].
Qed.

Theorem optionalL_well_formed_iff : forall L,
  cguardedL L <-> exists H, optionalL L H.
Proof.
  intro L. split.
  - intro HW. exists (local_to_ltt L).
    apply lttTC_to_optionalL. apply cguardedL_to_ltt. exact HW.
  - intros [H HL].
    apply (ltt_to_cguardedL L H).
    apply optionalL_to_lttTC. exact HL.
Qed.

Corollary optionalL_regularity_iff : forall H,
  (exists L, optionalL L H) <-> local.regLtt H.
Proof.
  intro H. split; intros [L HL]; exists L.
  - apply optionalL_to_lttTC. exact HL.
  - apply lttTC_to_optionalL. exact HL.
Qed.

Definition headL (G : local) : Prop :=
  match G with
  | l_end | l_send _ _ | l_recv _ _ => True
  | _ => False
  end.

Fixpoint spineL (G : local) : bool :=
  match G with
  | l_var _ => false
  | l_rec B => spineL B
  | _ => true
  end.

Lemma spineL_incr : forall G x m,
  spineL (incr_freeL x m G) = spineL G.
Proof.
  induction G; intros x m; simpl; try reflexivity.
  apply IHG.
Qed.

Lemma spineL_subst_true : forall G P x m,
  spineL G = true ->
  spineL (substitutionL x m P G) = true /\
  local.mu_height (substitutionL x m P G) = local.mu_height G.
Proof.
  induction G; intros P x m HS; simpl in *; try discriminate;
    try (split; reflexivity).
  destruct (IHG P (S x) (S m) HS) as [HA HB].
  split; [exact HA|]. f_equal. exact HB.
Qed.

Lemma spineL_subst_false : forall G P x m,
  spineL G = false -> spineL P = false ->
  spineL (substitutionL x m P G) = false.
Proof.
  induction G; intros P x m HS HP; cbn [spineL] in HS; try discriminate.
  - destruct n; cbn [substitutionL];
      repeat match goal with
      | |- context [if ?b then _ else _] => destruct b
      end;
      try reflexivity;
      rewrite spineL_incr; exact HP.
  - cbn [substitutionL spineL]. apply IHG; assumption.
Qed.

Lemma spineL_step : forall G, spineL (unfold_recL G) = spineL G.
Proof.
  intro G. destruct G; try reflexivity.
  change (spineL (substitutionL 0 0 (l_rec G) G) = spineL G).
  destruct (spineL G) eqn:HS.
  - exact (proj1 (spineL_subst_true G (l_rec G) 0 0 HS)).
  - apply spineL_subst_false; exact HS.
Qed.

Lemma spineL_iter : forall n G,
  spineL (header.iter n unfold_recL G) = spineL G.
Proof.
  induction n as [|n IH]; intro G; simpl; [reflexivity|].
  rewrite IH. apply spineL_step.
Qed.

Lemma headL_spine_height : forall G,
  headL G -> spineL G = true /\ local.mu_height G = 0.
Proof.
  intro G. destruct G; cbn [headL spineL local.mu_height];
    intro H; try contradiction; split; reflexivity.
Qed.

Inductive muStepsL : nat -> local -> local -> Prop :=
| muStepsL_zero : forall G, muStepsL 0 G G
| muStepsL_mu : forall n B H,
    muStepsL n (substitutionL 0 0 (l_rec B) B) H ->
    muStepsL (S n) (l_rec B) H.

Lemma muStepsL_iter : forall n G H,
  muStepsL n G H -> header.iter n unfold_recL G = H.
Proof.
  intros n G H HS. induction HS; simpl; assumption || reflexivity.
Qed.

Lemma muStepsL_spine : forall n G H,
  muStepsL n G H -> spineL G = spineL H.
Proof.
  intros n G H HS. induction HS; [reflexivity|].
  pose proof (spineL_step (l_rec B)) as E.
  cbn [unfold_recL] in E. rewrite <- E. exact IHHS.
Qed.

Theorem muStepsL_head_exact_height : forall n G H,
  muStepsL n G H -> headL H -> n = local.mu_height G.
Proof.
  intros n G H HS. induction HS; intro HH.
  - symmetry. exact (proj2 (headL_spine_height G HH)).
  - pose proof (muStepsL_spine n (substitutionL 0 0 (l_rec B) B) H HS) as E.
    pose proof (proj1 (headL_spine_height H HH)) as HSH.
    assert (HSB : spineL B = true).
    {
      pose proof (spineL_step (l_rec B)) as ES.
      cbn [unfold_recL spineL] in ES.
      rewrite <- ES, E. exact HSH.
    }
    destruct (spineL_subst_true B (l_rec B) 0 0 HSB) as [_ HE].
    cbn [local.mu_height]. f_equal.
    rewrite (IHHS HH). exact HE.
Qed.

Lemma spineL_complete : forall n G,
  local.mu_height G = n -> spineL G = true ->
  muStepsL n G (header.iter n unfold_recL G) /\
  headL (header.iter n unfold_recL G).
Proof.
  induction n as [|n IH]; intros G HE HS.
  - split; [constructor|].
    destruct G; cbn [local.mu_height] in HE;
      cbn [spineL] in HS; try discriminate; exact I.
  - destruct G; cbn [local.mu_height] in HE; try discriminate.
    injection HE as HE.
    cbn [spineL] in HS.
    destruct (spineL_subst_true G (l_rec G) 0 0 HS) as [HP HM].
    assert (HN : local.mu_height (substitutionL 0 0 (l_rec G) G) = n).
    { rewrite HM. exact HE. }
    destruct (IH (substitutionL 0 0 (l_rec G) G) HN HP) as [HA HB].
    cbn [header.iter unfold_recL].
    split; [constructor; exact HA|exact HB].
Qed.

Definition rawUnfoldL (G H : local) : Prop :=
  exists n, muStepsL n G H /\ headL H.

Corollary rawUnfoldL_at_height : forall G H,
  rawUnfoldL G H -> muStepsL (local.mu_height G) G H.
Proof.
  intros G H [n [HS HH]].
  pose proof (muStepsL_head_exact_height n G H HS HH) as E.
  rewrite <- E. exact HS.
Qed.

Lemma unfoldL_some_head : forall G H,
  unfoldL G = Some H -> headL H.
Proof.
  intros G H E. unfold unfoldL in E.
  destruct (unravelL G); inversion E; exact I.
Qed.

Theorem rawUnfoldL_iff_optional : forall G H,
  rawUnfoldL G H <-> unfoldL G = Some H.
Proof.
  intros G H. split.
  - intros [n [HS HH]].
    pose proof (muStepsL_head_exact_height n G H HS HH) as HN.
    pose proof (muStepsL_iter n G H HS) as HE.
    unfold unfoldL, unravelL. rewrite <- HN, HE.
    destruct H; cbn [headL] in HH; try contradiction; reflexivity.
  - intro E.
    pose proof (unfoldL_some G H E) as EH.
    pose proof (unfoldL_some_head G H E) as HH.
    assert (HS : spineL G = true).
    {
      rewrite <- (spineL_iter (local.mu_height G) G).
      change (spineL (unravelL G) = true).
      rewrite EH. exact (proj1 (headL_spine_height H HH)).
    }
    destruct (spineL_complete (local.mu_height G) G Logic.eq_refl HS) as [HA HB].
    exists (local.mu_height G). split; [|exact HH].
    change (muStepsL (local.mu_height G) G (unravelL G)) in HA.
    rewrite EH in HA. exact HA.
Qed.

Corollary unfoldL_none_iff_no_raw_head : forall G,
  unfoldL G = None <-> ~ exists H, rawUnfoldL G H.
Proof.
  intro G. split.
  - intros E [H HR]. apply rawUnfoldL_iff_optional in HR.
    rewrite E in HR. discriminate.
  - intro HN. destruct (unfoldL G) as [H|] eqn:E; [|reflexivity].
    exfalso. apply HN. exists H.
    apply rawUnfoldL_iff_optional. exact E.
Qed.
