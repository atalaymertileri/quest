From mathcomp Require Import ssreflect.seq all_ssreflect.
Require Import List String Coq.Arith.PeanoNat Coq.Arith.Arith Relations ZArith Datatypes Setoid Morphisms Coq.Logic.Decidable Coq.Program.Basics Coq.Init.Datatypes.
Import ListNotations. 
Open Scope list_scope.
From Paco Require Import paco.
Require Import def.header def.tree def.global.

(* Participant-occurrence predicates and their key properties:
   decidability, depth-indexed variants, and preservation across
   unfolding/substitution/translations between global forms. *)


Section global_part.

(* Participant occurrence predicates over recursive global syntax. *)
Inductive isgParts : participant -> global -> Prop := 
  | pa_sendp : forall p q l, isgParts p (g_send p q l)
  | pa_sendq : forall p q l, isgParts q (g_send p q l)
  | pa_sendr : forall p q r n s g lis, p <> r -> q <> r -> onth n lis = Some (s, g) -> isgParts r g -> isgParts r (g_send p q lis)
  | pa_mu    : forall p g, isgParts p g -> isgParts p (g_rec g).

(* Depth-indexed version used for induction arguments through recursion. *)
Inductive isgParts_depth : fin -> participant -> global -> Prop := 
  | dpth_p : forall p q lis, isgParts_depth 0 p (g_send p q lis)
  | dpth_q : forall p q lis, isgParts_depth 0 q (g_send p q lis)
  | dpth_mu : forall n pt g, isgParts_depth n pt g -> isgParts_depth (S n) pt (g_rec g)
  | dpth_c : forall p q pt s g lis n k, p <> pt -> q <> pt -> onth k lis = Some(s, g) -> isgParts_depth n pt g -> isgParts_depth (S n) pt (g_send p q lis).


Lemma isgParts_depth_exists : forall r Gl,
    isgParts r Gl -> exists n, isgParts_depth n r Gl.
Proof.
  induction Gl using global_ind_ref; intros; try easy.
  inversion H0.
  - subst. exists 0. constructor.
  - subst. exists 0. constructor.
  - subst. 
    specialize(SForall_onth n lis (fun u : sort * global => isgParts r u.2 -> exists n : fin, isgParts_depth n r u.2) (s, g) H H7); intros.
    simpl in H1.
    specialize(H1 H8).
    destruct H1 as (n0, Ha).
    exists (S n0). apply dpth_c with (n := n0) (s := s) (g := g) (k := n); try easy.
  - inversion H. subst. specialize(IHGl H2). destruct IHGl. exists (S x). constructor. easy.
Qed.

Lemma isgParts_depth_back : forall G n r,
      isgParts_depth n r G -> isgParts r G.
Proof.
  induction G using global_ind_ref; intros; try easy.
  inversion H0. 
  - subst. constructor.
  - subst. constructor.
  - subst.
    specialize(SForall_onth k lis (fun u : sort * global =>
       forall (n : fin) r, isgParts_depth n r u.2 -> isgParts r u.2) (s, g) H H8); intros.
    simpl in H1.
    specialize(H1 n0 r H9).
    apply pa_sendr with (n := k) (s := s) (g := g); try easy.
  - inversion H. subst. specialize(IHG n0 r H3). constructor. easy.
Qed.

Lemma subst_parts_depth : forall m n k r g g',
      isgParts_depth k r g' -> 
      isgParts_depth k r (substitutionG m n g g').
Proof.
  intros. revert H. revert m n r g g'.
  induction k; intros.
  - inversion H.
    - subst. simpl. constructor.
    - subst. simpl. constructor.
  - inversion H.
    - subst.
      simpl. constructor.
      apply IHk; try easy.
    - subst.
      simpl.
      apply dpth_c with (s := s) (g := (substitutionG m n g g0)) (k := k0); try easy.
      - clear H4 H2 H1 H IHk.
        revert H3. revert g0 s lis g m n. clear k r p q.
        induction k0; intros.
        - inversion H3.
          destruct lis.
          - inversion H0. subst. 
            simpl. easy.
          - subst.
            simpl. easy.
        - destruct lis; try easy.
          specialize(IHk0 g0 s lis g m n). simpl. destruct o. 
          - apply IHk0; try easy.
          - apply IHk0; try easy.
      - apply IHk; try easy.
Qed.

Lemma dec_isgParts : forall pt G, (isgParts pt G) \/ (isgParts pt G -> False).
Proof.
  intros pt G.
  induction G using global_ind_ref; intros; try easy.
  - right.
    intros. inversion H.
  - right. 
    intros. inversion H.
  - destruct (participant_dec pt p); subst; intros.
    - left.
      constructor.
    destruct (participant_dec pt q); subst; intros.
    - left.
      constructor.
    revert H.
    induction lis; intros.
    - inversion H. subst.
      destruct H1.
      - left. 
        destruct a.
        apply pa_sendr with (n := 0) (s := s) (g := g); try easy.
      - right.
        intro.
        inversion H1; try easy.
        subst.
        destruct n1; try easy. inversion H8. subst.
        apply H0; try easy.
    inversion H.
    - subst. clear H. destruct x.
      destruct H2.
      - left. apply pa_sendr with (n := 0) (s := s) (g := g); try easy.
      - specialize(IHlis H3). 
        destruct IHlis.
        - inversion H0; try easy. subst.
          left.
          apply pa_sendr with (n := S n1) (s := s0) (g := g0); try easy.
        - right. intro.
          inversion H1; try easy. subst.
          destruct n1.
          - inversion H9. subst.
            apply H; try easy.
          - simpl in H9.
            apply H0.
            apply pa_sendr with (n := n1) (s := s0) (g := g0); try easy.
    - subst. clear H.
      specialize(IHlis H1). clear H1.
      destruct IHlis.
      - left. 
        inversion H; try easy.
        subst.
        apply pa_sendr with (n := S n1) (s := s) (g := g); try easy.
      - right. intros. apply H.
        clear H.
        inversion H0; try easy.
        subst.
        destruct n1; try easy.
        apply pa_sendr with (n := n1) (s := s) (g := g); try easy.
  - destruct IHG.
    - left. constructor. easy.
    - right. intro. apply H.
      inversion H0. easy.
Qed.


Lemma subst_after_incrG_b : forall G m n pt,
    isgParts pt (incr_freeG m n G) -> isgParts pt G.
Proof.
  induction G using global_ind_ref; intros; try easy.
  - subst. 
    simpl in *.
    inversion H0. 
    - subst. constructor.
    - subst. constructor.
    - subst.
      specialize(onth_move_out n0 (fun u : sort * global => (u.1, incr_freeG m n u.2)) lis (s, g) H7); intros.
      destruct H1 as (t,(Ha,Hb)). destruct t. 
      inversion Hb. subst. clear Hb.
      specialize(SForall_onth n0 lis (fun u : sort * global =>
       forall (m n : fin) pt,
       isgParts pt (incr_freeG m n u.2) -> isgParts pt u.2) (s, g0) H Ha); intros.
      simpl in H1.
      specialize(H1 m n pt H8). 
      apply pa_sendr with (n := n0) (s := s) (g := g0); try easy.
  - simpl.
    constructor. 
    simpl in H.
    inversion H. subst.
    specialize(IHG m.+1 n pt H2). easy.
Qed.

Lemma subst_part_b : forall m n G G1 pt,
    isgParts pt (substitutionG m n G G1) -> 
    (isgParts pt G \/ isgParts pt G1).
Proof.
  intros. revert H. revert pt m n G.
  induction G1 using global_ind_ref; intros; try easy.
  - simpl in *.
    destruct n.
    - case_eq (Nat.eqb m 0); intros.
      - rewrite H0 in H.
        left.
        apply subst_after_incrG_b with 0 n0. easy.
      - rewrite H0 in H.
        inversion H.
    - case_eq (Nat.eqb m n.+1); intros.
      - rewrite H0 in H.
        left.
        apply subst_after_incrG_b with 0 n0. easy.
      rewrite H0 in H.
      case_eq (Nat.leb m n.+1); intros.
      - rewrite H1 in H.
        inversion H.
      - rewrite H1 in H.
        inversion H.
  - simpl in *.
    inversion H0.
    - subst. right. constructor.
    - subst. right. constructor.
    - subst. clear H0.
      specialize(onth_move_out n0 (fun u : sort * global => (u.1, substitutionG m n G u.2)) lis (s, g) H7); intros.
      destruct H0 as (t,(Ha,Hb)).
      inversion Hb. subst. clear Hb.
      specialize(SForall_onth n0 lis (fun u : sort * global =>
       forall pt (m n : fin) (G : global),
       isgParts pt (substitutionG m n G u.2) -> isgParts pt G \/ isgParts pt u.2) t H Ha); intros.
      simpl in H0.
      destruct t.
      specialize(H0 pt m n G H8).
      destruct H0.
      - left. easy.
      - right.
        apply pa_sendr with n0 s g; try easy.
  - simpl in *.
    inversion H. subst. clear H.
    specialize(IHG1 pt m.+1 n.+1 G H2).
    destruct IHG1.
    - left. easy.
    - right. 
      constructor. easy.
Qed.


End global_part.


Section gtt_part.



(* Participant occurrence over coinductive global trees (`gtt`). *)
Inductive isgPartsC : participant -> gtt -> Prop := 
  | pac_sendp : forall p q l, isgPartsC p (gtt_send p q l)
  | pac_sendq : forall p q l, isgPartsC q (gtt_send p q l)
  | pac_sendr : forall p q r n s g lis, p <> r -> q <> r -> lis n = Some (s, g) -> isgPartsC r g -> isgPartsC r (gtt_send p q lis).




Lemma part_global_to_gtt : forall pt G' G, gttTC G' G -> isgParts pt G' -> isgPartsC pt G.
Proof.
  intros.
  specialize(isgParts_depth_exists pt G' H0); intros. clear H0.
  destruct H1 as (n, H0). revert H H0. revert G' G.
  induction n; intros.
  - inversion H0.
    - subst. 
      pinversion H. subst. constructor.
      apply gttT_mon.
    - subst.
      pinversion H. subst. constructor.
      apply gttT_mon.
  - inversion H0. subst.
    specialize(subst_parts_depth 0 0 n pt (g_rec g) g H2); intros. clear H2.
    specialize(IHn (substitutionG 0 0 (g_rec g) g) G).
    apply IHn; try easy.
    pinversion H; try easy. subst. pfold. easy.
    apply gttT_mon.
  - subst.
    pinversion H.
    subst.
    specialize(H9 k). rewrite H4 in H9.
    destruct H9; try easy.
    destruct H1 as (s1,(g1,(g2,(Ha,(Hb,Hc))))). inversion Ha. subst. clear Ha.
    pclearbot.
    specialize(IHn g1 g2 Hc H5).
    apply pac_sendr with (n := k) (s := s1) (g := g2); try easy.
    apply gttT_mon.
Qed.


Lemma part_forward : forall G pt, isgParts pt G -> isgParts pt (unravelG G).
Proof.
  unfold unravelG.
  intro G.
  specialize(always_exists (mu_height G)); intros.
  destruct H as (x,Ha).
  rewrite Ha. clear Ha.
  revert H0. revert G.
  induction x; intros.
  - simpl. easy.
  - simpl.
    apply IHx; try easy.
    specialize(isgParts_depth_exists pt G H0); intros.
    destruct H as (n, Ha).
    destruct G; try easy.
    simpl.
    inversion Ha; try easy. subst.
    specialize(subst_parts_depth 0 0 n0 pt (g_rec G) G H3); intros.
    apply isgParts_depth_back with n0; try easy.
Qed.

Lemma part_backward : forall G pt, isgParts pt (unravelG G) -> isgParts pt G.
Proof.
  unfold unravelG in *.
  intro G.
  specialize(always_exists (mu_height G)); intros.
  destruct H as (x,H).
  rewrite H in H0. clear H.
  revert H0. revert G.
  induction x; intros.
  - simpl in H0. easy.
  - simpl in *.
    assert(isgParts pt (unfold_recG G)).
    {
      apply IHx; try easy.
    }
    clear IHx H0.
    unfold unfold_recG in *.
    destruct G; try easy.
    specialize(subst_part_b 0 0 (g_rec G) G pt H); intros.
    destruct H0; try easy.
    constructor. easy.
Qed.



Lemma part_gtt_to_global : forall pt G G', gttTC G' G -> isgPartsC pt G -> isgParts pt G'.
Proof.
  intros.
  revert H. revert G'.
  induction H0; intros.
  - apply part_backward.
    specialize(gttTC_forward G' (gtt_send p q l) H); intros.
    specialize(gtt_to_cguardedG G' (gtt_send p q l) H); intros.
    specialize(unravelG_notmu G' H1); intros.
    destruct H2.
    - rewrite H2 in H0.
      pinversion H0; try easy.
      apply gttT_mon.
    - destruct H2 as (p1,(q1,(lis,Ha))).
      rewrite Ha in H0. rewrite Ha.
      pinversion H0.
      constructor.
      apply gttT_mon.
  - apply part_backward.
    specialize(gttTC_forward G' (gtt_send p q l) H); intros.
    specialize(gtt_to_cguardedG G' (gtt_send p q l) H); intros.
    specialize(unravelG_notmu G' H1); intros.
    destruct H2.
    - rewrite H2 in H0.
      pinversion H0; try easy.
      apply gttT_mon.
    - destruct H2 as (p1,(q1,(lis,Ha))).
      rewrite Ha in H0. rewrite Ha.
      pinversion H0.
      constructor.
      apply gttT_mon.
  - apply part_backward.
    specialize(gttTC_forward G' (gtt_send p q lis) H3); intros.
    specialize(gtt_to_cguardedG G' (gtt_send p q lis) H3); intros.
    specialize(unravelG_notmu G' H5); intros.
    destruct H6.
    - rewrite H6 in H4.
      pinversion H4.
      apply gttT_mon.
    - destruct H6 as (p1,(q1,(lis1,Ha))).
      rewrite Ha in H4.
      pinversion H4.
      subst.
      specialize(H7 n). rewrite H1 in H7.
      destruct H7; try easy.
      destruct H6 as (s1,(g1,(g2,(Hb,(Hc,Hd))))). inversion Hc. subst. clear Hc.
      rewrite Ha.
      pclearbot.
      apply pa_sendr with n s1 g1; try easy.
      apply IHisgPartsC; try easy.
      apply gttT_mon.
Qed.


Lemma dec_isgPartsC : forall G pt, regGtt G -> (isgPartsC pt G \/ (isgPartsC pt G -> False)).
Proof.
  intros.
  destruct H as (G',H).
  specialize(dec_isgParts pt G'); intros.
  destruct H0.
  - left.
    apply part_global_to_gtt with G'; try easy.
  - right. intro.
    apply H0.
    apply part_gtt_to_global with G; try easy.
Qed.

  
End gtt_part.


Section sgtt_part.


Inductive isgPartsCS : participant -> gtt -> Prop := 
  | pacs_sendp : forall p q l, isgPartsCS p (gtt_send p q l)
  | pacs_sendq : forall p q l, isgPartsCS q (gtt_send p q l)
  | pacs_sendr : forall p q r lis, p <> r -> q <> r -> 
                (forall pt, lis pt = None \/ (exists s g, lis pt = Some (s, g) /\ isgPartsCS r g)) -> 
                isgPartsCS r (gtt_send p q lis).

Section isgPartsCS_ind_ref.
   Variable P : participant -> gtt -> Prop.
   Hypothesis P_sendp : forall p q l, P p (gtt_send p q l).
   Hypothesis P_sendq : forall p q l, P q (gtt_send p q l).
   Hypothesis P_sendr : forall p q r lis,
            p <> r -> q <> r -> 
                (forall pt, lis pt = None \/ (exists s g, lis pt = Some (s, g) /\ isgPartsCS r g /\ P r g)) -> P r (gtt_send p q lis).
                
   Fixpoint isgPartsCS_ind_ref (pt : participant) (G : gtt) (a : isgPartsCS pt G) {struct a} : P pt G.
   Proof.
      refine (match a with 
        | pacs_sendp p q l => P_sendp p q l 
        | pacs_sendq p q l => P_sendq p q l 
        | pacs_sendr p q l lis Ha Hb Hc => P_sendr p q l lis Ha Hb _
      end); try easy.
      intros.
      specialize(Hc pt0). destruct Hc as [Hc | Hc]; [left; easy | destruct_exists_and; subst; right].
      rewrite H. eexists. eexists. split. easy.
      split. easy.
      apply isgPartsCS_ind_ref; try easy.
   Qed.
End isgPartsCS_ind_ref.

Lemma isgPartsCS_back : forall p0 x0,
      isgPartsCS p0 x0 -> 
      regGtt x0 -> 
      isgPartsC p0 x0.
Proof.
  intros. revert H0.
  refine (
     isgPartsCS_ind_ref 
     (fun p0 x0 => regGtt x0 -> isgPartsC p0 x0)
     _ _ _ 
     p0 x0 H
  ); clear H; clear p0 x0.
  intros; try constructor.
  intros; try constructor.
  intros.
  specialize(regGtt_some_cont p q lis); intros. fill_triv.
  destruct_exists_and.
  specialize(H1 x). rewrite H3 in H1. destruct H1; try easy.
  destruct_exists_and. invert_all_some.
  specialize(regGtt_cont p q lis); intros. fill_triv.
  specialize(H1 x). rewrite H3 in H1. destruct H1; try easy. 
  destruct_exists_and. invert_all_some.
  fill_triv.
  apply pac_sendr with x x0 x3; try easy.
Qed.

End sgtt_part.




