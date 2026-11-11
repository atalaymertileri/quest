From mathcomp Require Import ssreflect.seq all_ssreflect.
Require Import List String Coq.Arith.PeanoNat Coq.Arith.Arith Relations ZArith Datatypes Setoid Morphisms Coq.Logic.Decidable Coq.Program.Basics Coq.Init.Datatypes.
Import ListNotations. 
Open Scope list_scope.
From Paco Require Import paco.
Require Import def.header.

(* Core tree syntax:
   - global communication trees (`gtt`)
   - local communication trees (`ltt`)
   - helper tree-with-hole syntax (`gtth`) for projection proofs. *)

Section gtt.

(* Coinductive global tree type. *)
CoInductive gtt: Type :=
  | gtt_end    : gtt
  | gtt_send   : participant -> participant -> (fin -> option (sort * gtt)) -> gtt.

Definition gtt_id (s: gtt): gtt :=
  match s with
    | gtt_end        => gtt_end
    | gtt_send p q l => gtt_send p q l
  end.

Lemma gtt_eq: forall s, s = gtt_id s.
Proof. intro s; destruct s; easy. Defined.

(* Node view used by path-based predicates (`gttmap`, `balancedG`). *)
Inductive gnode : Type := 
  | gnode_end : gnode
  | gnode_pq : participant -> participant -> gnode
  | gnode_s  : sort -> gnode.

(* Path observer:
   `gttmap G w s n` means that following word `w` in `G` reaches node `n`,
   optionally exposing a selected label `s` at the end. *)
Inductive gttmap : gtt -> list fin -> option fin -> gnode -> Prop := 
  | gmap_end : gttmap gtt_end nil None gnode_end
  | gmap_pq  : forall p q xs, gttmap (gtt_send p q xs) nil None (gnode_pq p q)
  | gmap_con : forall n lis xs p q st gk s gn, xs n = Some (st, gk) -> gttmap gk lis s gn -> gttmap (gtt_send p q xs) (n :: lis) s gn
  | gmap_st  : forall n xs p q st gk, xs n = Some (st, gk) -> gttmap (gtt_send p q xs) nil (Some n) (gnode_s st). 

(* Global balancedness condition used to guarantee dual interactions along
   all reachable continuations. *)
Definition balancedG (G : gtt) := forall w w' p q,
                        (gttmap G (w ++ w') None (gnode_pq p q) \/ gttmap G (w ++ w') None (gnode_pq q p)) -> 
  (exists k, forall w', (gttmap G (w ++ w') None (gnode_end) \/ (List.length w' = k /\ exists tc, gttmap G (w ++ w') None tc)) -> 
                        exists w2 w0, w' = w2 ++ w0 /\ exists r, 
                        gttmap G (w ++ w2) None (gnode_pq p r) \/ gttmap G (w ++ w2) None (gnode_pq r p)).

End gtt.

Section ltt.

CoInductive ltt: Type :=
  | ltt_end : ltt
  | ltt_recv: participant -> (fin -> (option(sort*ltt))) -> ltt
  | ltt_send: participant -> (fin -> (option(sort*ltt))) -> ltt.

Definition ltt_id (s: ltt): ltt :=
  match s with
    | ltt_end      => ltt_end
    | ltt_recv p l => ltt_recv p l 
    | ltt_send p l => ltt_send p l
  end.
  
Lemma ltt_eq: forall s, s = ltt_id s.
Proof. intro s; destruct s; easy. Defined.

End ltt.



Section gtth.

(* Global trees with an explicit hole constructor for context reasoning. *)
Inductive gtth: Type :=
  | gtth_hol    : gtth
  | gtth_send   : participant -> participant -> (fin -> option (sort * gtth)) -> gtth.

Section gtth_ind_ref.
  Variable P : gtth -> Prop.
  Hypothesis P_hol : P (gtth_hol).
  Hypothesis P_send : forall p q xs, (forall n, xs n = None \/ exists s g, xs n = Some (s,g) /\ P g) -> P (gtth_send p q xs).
  
  Fixpoint gtth_ind_ref p : P p.
  Proof.
    destruct p.
    - apply P_hol.
    - apply P_send.
      intros.
      assert(exists sg, o n = sg). exists (o n). easy.
      destruct H as (sg, Ha).
      destruct sg.
      - right. destruct p1.
        exists s. exists g.
        split. easy.
        apply gtth_ind_ref; try easy.
      - left. easy.
  Qed.

End gtth_ind_ref.


Inductive typ_gtth : participant -> gtth -> gtt -> Prop := 
  | gt_holend : forall pp, typ_gtth pp (gtth_hol) gtt_end
  | gt_holps  : forall pp pq f, typ_gtth pp (gtth_hol) (gtt_send pp pq f)
  | gt_holpr  : forall pp pq f, typ_gtth pp (gtth_hol) (gtt_send pq pp f)
  | gt_send : forall ctx p q xs ys, (forall n, (xs n = None /\ ys n = None) \/ exists s g g', (xs n = Some(s,g) /\ ys n = Some(s,g') /\ typ_gtth ctx g g'))-> 
                                                typ_gtth ctx (gtth_send p q xs) (gtt_send p q ys).

Section typ_gtth_ind_ref.
  Variable P : participant -> gtth -> gtt -> Prop.
  Hypothesis P_holend : forall pp, P pp (gtth_hol) gtt_end.
  Hypothesis P_holps  : forall pp pq f, P pp (gtth_hol) (gtt_send pp pq f).
  Hypothesis P_holpr  : forall pp pq f, P pp (gtth_hol) (gtt_send pq pp f).
  Hypothesis P_send : forall ctx p q xs ys, (forall n, (xs n = None /\ ys n = None) \/ exists s g g', (xs n = Some(s,g) /\ ys n = Some(s,g') /\ P ctx g g'))->
                                                 P ctx (gtth_send p q xs) (gtt_send p q ys).
  
  Fixpoint typ_gtth_ind_ref ctx G G' (a : typ_gtth ctx G G') {struct a} : P ctx G G'.
  Proof.
    revert a. revert G'.
    induction G using gtth_ind_ref; intros.
    - inversion a. subst.
      apply P_holend; try easy.
    - subst.
      apply P_holps; try easy.
    - subst.
      apply P_holpr; try easy.
    - inversion a.
      subst. clear a.
      apply P_send; try easy.
      clear P_holend P_holps P_holpr P_send typ_gtth_ind_ref.
      intro.
      specialize(H5 n). specialize(H n).
      destruct H5.
      - left. easy.
      - destruct H0 as (s,(g,(g1,(Ha,(Hb,Hc))))).
        destruct H; try easy.
        - specialize(eq_trans (esym H) Ha); intros. 
          easy.
        - destruct H as (s1,(g2,(Hd,He))).
          specialize(eq_trans (esym Hd) Ha); intros.
          inversion H. subst. clear H.
          right. exists s. exists g. exists g1.
          split. easy. split. easy.
          apply He; try easy.
  Qed.

End typ_gtth_ind_ref.

Inductive ishParts : participant -> gtth -> Prop := 
  | ha_sendp : forall p q l, ishParts p (gtth_send p q l)
  | ha_sendq : forall p q l, ishParts q (gtth_send p q l)
  | ha_sendr : forall p q r n s g lis, p <> r -> q <> r -> lis n = Some (s, g) -> ishParts r g -> ishParts r (gtth_send p q lis).

End gtth.

Fixpoint explicit_btt (n : fin) (pt : participant) (G : gtt) : gtth :=
  match n with 
    | 0 => gtth_hol 
    | S m => match G with
      | gtt_send pr ps f => if participant_dec pr pt then gtth_hol else
                            if participant_dec ps pt then gtth_hol else 
                            gtth_send pr ps (fun i => match f i with 
                                                | None => None 
                                                | Some (s, g) => Some (s, explicit_btt m pt g)
                                              end)
      | _ => gtth_hol
    end
  end.

Lemma balanced_to_tree : forall pt pr w G, balancedG G -> (gttmap G w None (gnode_pq pt pr) \/ gttmap G w None (gnode_pq pr pt)) -> 
      exists G', 
       typ_gtth pt G' G /\ (ishParts pt G' -> False).
Proof.
  intros.
  unfold balancedG in H.
  specialize(H nil w pt pr).
  specialize(H H0). 
  destruct H as (k, H).
  clear H0.
  simpl in *.
  exists (explicit_btt k pt G).
  revert H. revert pt G. clear pr w.
  
  induction k; intros; try easy.
  - specialize(H nil).
    assert(exists w2 w0 : seq.seq fin,
      [] = w2 ++ w0 /\
      (exists r,
         gttmap G ([] ++ w2) None (gnode_pq pt r) \/ gttmap G ([] ++ w2) None (gnode_pq r pt))).
    {
      apply H; try easy. clear H.
      destruct G.
      - left. constructor.
      - right.
        split. easy.
        exists (gnode_pq p p0). constructor.
    }
    clear H.
    destruct H0 as (w,(w',(Ha,(r,Hb)))).
    destruct w; try easy. destruct w'; try easy.
    clear Ha.
    simpl in *.
    destruct Hb.
    - inversion H. subst.
      split.
      - constructor.
      - intros. inversion H0.
    - inversion H. subst.
      split.
      - constructor.
      - intros. inversion H0.
  - destruct G.
    - split. constructor. 
      intros. inversion H0.
    - simpl in *; destruct (participant_dec p  pt);   subst; intros; simpl.
      - split.
        - constructor.
        - intros. 
          inversion H0.
      simpl in *; destruct (participant_dec p0 pt); subst; simpl in *; intros.
      - split.
        constructor.
        - intros.
          inversion H0.
      - simpl.
        specialize(IHk pt).
        split.
        - constructor.
          intros.
          assert(exists z, o n1 = z). exists (o n1). easy.
          destruct H0 as (z, Ha).
          rewrite Ha. destruct z.
          - destruct p1.
            right. exists s. exists (explicit_btt k pt g). exists g.
            split. easy. split. easy.
            specialize(IHk g).
            assert(typ_gtth pt (explicit_btt k pt g) g /\ (ishParts pt (explicit_btt k pt g) -> False)).
            {
              apply IHk; try easy. clear IHk.
              intros.
              specialize(H (n1 :: w')). 
              assert(gttmap (gtt_send p p0 o) (n1 :: w') None gnode_end \/
    length (n1 :: w') = k.+1 /\
    (exists tc : gnode, gttmap (gtt_send p p0 o) (n1 :: w') None tc)).
              {
                destruct H0.
                - left.
                  apply gmap_con with (st := s) (gk := g); try easy.
                - destruct H0.
                  right.
                  split. simpl. rewrite H0. easy.
                  destruct H1 as (tc,Hb).
                  exists tc.
                  apply gmap_con with (st := s) (gk := g); try easy.
              }
              specialize(H H1). clear H1 H0.
              destruct H as (w2,(w0,(Hb,(r,Hc)))).
              destruct w2.
              - destruct Hc.
                - inversion H. subst.
                  congruence. 
                - inversion H. subst.
                  congruence. 
              - inversion Hb. subst.
                exists w2. exists w0.
                split. easy.
                exists r.
                destruct Hc.
                - inversion H. subst.
                  specialize(eq_trans (esym Ha) H7); intros.
                  inversion H0. subst.
                  left.
                  easy.
                - inversion H. subst.
                  specialize(eq_trans (esym Ha) H7); intros.
                  inversion H0. subst.
                  right.
                  easy.
            }
            easy.
          - left. easy.
        - intros.
          inversion H0.
          - subst.
            congruence.
          - subst.
            congruence.
          - subst.
            clear H0.
            assert(exists z, o n1 = z). exists (o n1). easy.
            destruct H0 as (z, Ha). rewrite Ha in H7.
            destruct z; try easy. destruct p1.
            inversion H7. subst. clear H7. 
            specialize(IHk g0). rename g0 into g.
            assert(typ_gtth pt (explicit_btt k pt g) g /\ (ishParts pt (explicit_btt k pt g) -> False)).
            {
              apply IHk; try easy. clear IHk.
              intros.
              specialize(H (n1 :: w')). 
              assert(gttmap (gtt_send p p0 o) (n1 :: w') None gnode_end \/
    length (n1 :: w') = k.+1 /\
    (exists tc : gnode, gttmap (gtt_send p p0 o) (n1 :: w') None tc)).
              {
                destruct H0.
                - left.
                  apply gmap_con with (st := s) (gk := g); try easy.
                - destruct H0.
                  right.
                  split. simpl. rewrite H0. easy.
                  destruct H1 as (tc,Hb).
                  exists tc.
                  apply gmap_con with (st := s) (gk := g); try easy.
              }
              specialize(H H1). clear H1 H0.
              destruct H as (w2,(w0,(Hb,(r,Hc)))).
              destruct w2.
              - destruct Hc.
                - inversion H. subst. easy.
                - inversion H. subst. easy.
              - inversion Hb. subst.
                exists w2. exists w0.
                split. easy.
                exists r.
                destruct Hc.
                - inversion H. subst.
                  specialize(eq_trans (esym Ha) H10); intros.
                  inversion H0. subst.
                  left.
                  easy.
                - inversion H. subst.
                  specialize(eq_trans (esym Ha) H10); intros.
                  inversion H0. subst.
                  right.
                  easy.
            }
            destruct H0.
            apply H1. easy.
Qed.



Inductive ltt_bisim (R : ltt -> ltt -> Prop) : ltt -> ltt -> Prop := 
  | ltt_bisim_end : ltt_bisim R ltt_end ltt_end 
  | ltt_bisim_send : forall p f1 f2, (forall n, (f1 n = None /\ f2 n = None) \/ (exists s t1 t2, f1 n = Some(s, t1) /\ f2 n = Some(s, t2) /\ R t1 t2)) -> ltt_bisim R (ltt_send p f1) (ltt_send p f2)
  | ltt_bisim_recv : forall p f1 f2, (forall n, (f1 n = None /\ f2 n = None) \/ (exists s t1 t2, f1 n = Some(s, t1) /\ f2 n = Some(s, t2) /\ R t1 t2)) -> ltt_bisim R (ltt_recv p f1) (ltt_recv p f2).
  
Lemma ltt_bisim_mon : monotone2 ltt_bisim.
Proof.
  unfold monotone2; intros.
  induction IN; intros.
  - constructor.
  - constructor.
    intros. 
    specialize(H n).
    destruct H.
    - left. easy.
    - destruct_exists_and. right. exists x. exists x0. exists x1.
      repeat(split; try easy).
      apply LE; try easy.
  - constructor.
    intros. 
    specialize(H n).
    destruct H.
    - left. easy.
    - destruct_exists_and. right. exists x. exists x0. exists x1.
      repeat(split; try easy).
      apply LE; try easy.
Qed.


Definition ltt_bisimC := paco2 ltt_bisim bot2.

Lemma ltt_bisimC_refl : forall r l, paco2 ltt_bisim r l l.
Proof.
  pcofix CIH; intros.
  destruct l.
  - pfold. constructor.
  - pfold. constructor.
    intros. destruct (o n).
    - right. destruct p0. eexists. eexists. eexists.
      repeat(split; try easy).
      right. apply CIH.
    - left. easy.
  - pfold. constructor.
    intros. destruct (o n).
    - right. destruct p0. eexists. eexists. eexists.
      repeat(split; try easy).
      right. apply CIH.
    - left. easy.
Qed.





#[export] Hint Resolve ltt_bisim_mon : mon.
