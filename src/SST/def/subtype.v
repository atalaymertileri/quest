From mathcomp Require Import ssreflect.seq all_ssreflect.
Require Import List String Coq.Arith.PeanoNat Coq.Arith.Arith Relations ZArith Datatypes Setoid Morphisms Coq.Logic.Decidable Coq.Program.Basics Coq.Init.Datatypes.
Import ListNotations. 
Open Scope list_scope.
From Paco Require Import paco.
Require Import def.header def.tree.

(* Coinductive local-type subtyping and bisimulation relations. *)

Section subtype.


(* One-step generator for the greatest fixed-point subtype relation. *)
Inductive subtype (R: ltt -> ltt -> Prop): ltt -> ltt -> Prop :=
  | sub_end: subtype R ltt_end ltt_end
  | sub_in : forall p xs ys,
                    (forall n, (ys n = None) \/ (exists s t t', xs n = Some(s, t) /\ ys n = Some(s, t') /\  R t t')) ->
                    subtype R (ltt_recv p xs) (ltt_recv p ys)
  | sub_out : forall p xs ys,
                     (forall n, (xs n = None) \/ (exists s t t', xs n = Some(s, t) /\ ys n = Some(s, t') /\ R t t')) ->
                     subtype R (ltt_send p xs) (ltt_send p ys).

Definition subtypeC l1 l2 := paco2 subtype bot2 l1 l2.

Lemma sub_mon : monotone2 subtype.
Proof.
  unfold monotone2.
  intros.
  induction IN; intros.
  - constructor.
  - constructor.
    intro.
    specialize(H n).
    destruct H.
    - left. easy.
    - destruct H as (s1,(t1,(t2,(Ha,(Hb,Hc))))).
      rewrite Ha. rewrite Hb.
      right. exists s1. exists t1. exists t2.
      split. easy. split. easy.
      apply LE; try easy.
  - constructor.
    intro.
    specialize(H n).
    destruct H.
    - left. easy.
    - destruct H as (s1,(t1,(t2,(Ha,(Hb,Hc))))).
      rewrite Ha. rewrite Hb.
      right. exists s1. exists t1. exists t2.
      split. easy. split. easy. 
      apply LE; try easy.
Qed.


Lemma stRefl: forall l, subtypeC l l.
Proof. 
      pcofix CIH.
      intros.
      pfold.
      case_eq l; intros.
      - constructor.
      - subst.
        constructor.
        intro.
        destruct o.
        - right. destruct p0.
          exists s. exists l. exists l.
          split. easy. split. easy.
          right. apply CIH.
        - left. easy.
      - subst.
        constructor.
        intro.
        destruct o.
        - right. destruct p0.
          exists s. exists l. exists l.
          split. easy. split. easy.
          right. apply CIH.
        - left. easy.
Qed.


Lemma stTrans: forall l1 l2 l3, subtypeC l1 l2 -> subtypeC l2 l3 -> subtypeC l1 l3.
Proof.
    pcofix CIH. intros.
    pfold. case_eq l1; intros.
    - subst. pinversion H0. subst. pinversion H1. subst. constructor. 
      apply sub_mon. apply sub_mon.

    - (* Receive case: labels are contravariant in sorts, so we compose
         branch witnesses by pulling a branch from the right premise and
         then matching it against the left premise. *)
      subst. pinversion H0. subst. pinversion H1. subst.
      constructor.
      intro.
      specialize(H4 n). specialize(H5 n).
      destruct H5. left. easy.
      - destruct H as (s1,(t1,(t2,(Ha,(Hb,Hd))))).
        rewrite Hb. right. rewrite Ha in H4.
        destruct H4; try easy.
        destruct H as (s3,(t3,(t4,(He,(Hf,Hh))))).
        inversion Hf. subst. clear Hf. rewrite He.
        exists s3. exists t3. exists t2.
        split. easy. split. easy.
        - right. pclearbot.
          apply CIH with t4; try easy.
      apply sub_mon. apply sub_mon.

    - (* Send case: labels are covariant in sorts, composition is dual
         to the receive case. *)
      subst. pinversion H0. subst. pinversion H1. subst.
      constructor.
      intro.
      specialize(H4 n). specialize(H5 n).
      destruct H4. left. easy.
      - destruct H as (s1,(t1,(t2,(Ha,(Hb,Hd))))).
        rewrite Ha. right. rewrite Hb in H5.
        destruct H5; try easy.
        destruct H as (s3,(t3,(t4,(He,(Hf,Hh))))).
        inversion He. subst. clear He. rewrite Hf.
        exists s3. exists t1. exists t4.
        split. easy. split. easy.
        - right. pclearbot.
          apply CIH with t3; try easy.
      apply sub_mon. apply sub_mon.
Qed.


(* Bisimulation-style companion relation; same shape as subtype but requires
   branch presence on both sides. *)
Inductive bisim (R: ltt -> ltt -> Prop): ltt -> ltt -> Prop :=
  | bisim_end: bisim R ltt_end ltt_end
  | bisim_in : forall p xs ys,
                    (forall n, (xs n = None /\ ys n = None) \/ (exists s t t', xs n = Some(s, t) /\ ys n = Some(s, t') /\ R t t')) ->
                    bisim R (ltt_recv p xs) (ltt_recv p ys)
  | bisim_out : forall p xs ys,
                     (forall n, (xs n = None /\ ys n = None) \/ (exists s t t', xs n = Some(s, t) /\ ys n = Some(s, t') /\  R t t')) ->
                     bisim R (ltt_send p xs) (ltt_send p ys).

Definition bisimC l1 l2 := paco2 bisim bot2 l1 l2.



End subtype.

#[export] Hint Resolve sub_mon : mon.
