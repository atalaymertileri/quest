From mathcomp Require Import ssreflect.seq all_ssreflect.
Require Import List String Coq.Arith.PeanoNat Coq.Arith.Arith Relations ZArith Datatypes Setoid Morphisms Coq.Logic.Decidable Coq.Program.Basics Coq.Init.Datatypes.
Import ListNotations. 
Open Scope list_scope.
From Paco Require Import paco.
Require Import def.header def.tree def.global def.local def.part def.projection def.subtype def.merge.
Require Import Permutation ListUtils FMap Automation.
Require Import Primitives Process ProcessGuarding Typechecking.

(* Session-level operational semantics and typing:
   this file lifts process/global-local machinery to session maps,
   then defines safety/liveness-oriented context notions. *)

(* notation that forgets participants and labels when G takes a step, equivalent to saying that G -(p,q)l-> G' <-> G -> G' *)
Inductive multiC : relation gtt := 
  | multiC_refl : forall G, multiC G G
  | multiC_step : forall G1 G2 G3 p q n, gttstepC G1 G2 p q n -> multiC G2 G3 -> multiC G1 G3.


(* M \Rrightarrow \prod_{i \in I} p : 0 *)
Definition is_inact (M: session) := (exists M', unfoldM M M' /\ (forall pt, M' pt = None \/ (exists lz, M' pt = Some (p_end lz)))). 

(* M is not a complete session but cannot also make a step *)
Definition stuck (M : session) := (is_inact M -> False) /\ ((exists qs a S' r, step (qs, M) a S' r) -> False).

(* M is stuckM if it can reach a stuck state *)
Definition stuckM (M : session) := exists qs la S' r, multistep (qs, M) la S' r /\ stuck (snd S').
  
(* typing contexts are partial functions from participants to local type trees *)
Definition typ_ctx := finite_map participant ltt.

(* corresponds to \Delta -(p : q \oplus l(s)t)-> *)
Inductive ctx_step_s : typ_ctx -> participant -> participant -> Prop :=
  | step_s : forall (G: typ_ctx) p q xs l st, 
             G p = Some (ltt_send q xs) -> 
             xs l = Some st -> 
             ctx_step_s G p q.
(* explict label *)
Inductive ctx_step_sl : typ_ctx -> participant -> participant -> label -> sort -> Prop :=
  | step_sl : forall (G: typ_ctx) p q xs l B T, 
             G p = Some (ltt_send q xs) -> 
             xs l = Some (B, T) -> 
             ctx_step_sl G p q l B.
             
(* corresponds to \Delta -(p : q & l(s)t)-> *) 
Inductive ctx_step_r : typ_ctx -> participant -> participant -> Prop :=
  | step_r : forall (G: typ_ctx) p q xs l st, 
             G p = Some (ltt_recv q xs) -> 
             xs l = Some st -> 
             ctx_step_r G p q.

(* corresponds to \Delta -(pq)l-> \Delta' *)
Inductive ctx_step_f : typ_ctx -> participant -> participant -> label -> sort -> typ_ctx -> Prop :=
  | step_sr : forall (G G': typ_ctx) p q l xs ys T T' B, 
              p <> q -> 
              G p = Some (ltt_send q xs) -> 
              G q = Some (ltt_recv p ys) -> 
              xs l = Some(B, T) -> 
              ys l = Some(B, T') -> 
              (forall pt, if participant_dec pt p then G' pt = Some T else if participant_dec pt q then G' pt = Some T' else G pt = G' pt) -> 
              ctx_step_f G p q l B G'.

(* syntactic sugar where we don't care about the specific participants involved *)
Inductive typ_ctx_red : typ_ctx -> typ_ctx -> Prop := 
  | step_on_f : forall G G' p q l B, ctx_step_f G p q l B G' -> typ_ctx_red G G'.


(* safe typing context *)
Definition safe_ctx (gtx : typ_ctx) := forall gtx',
  multi typ_ctx_red gtx gtx' ->
  (forall p q l B,
        ctx_step_sl gtx' p q l B -> 
        ctx_step_r gtx' q p ->
        exists gtx'', ctx_step_f gtx' p q l B gtx'').
   
(* completed typing context *)
Definition is_end (gtx : typ_ctx) := forall pt, gtx pt = None \/ gtx pt = Some ltt_end.

(* deadlock free typing context *)
Definition df_ctx (gtx : typ_ctx) := forall gtx', 
      multi typ_ctx_red gtx gtx' ->
      (forall gtx'', typ_ctx_red gtx' gtx'' -> False) -> 
      is_end gtx'.

(* live *)
Definition live_ctx (gtx : typ_ctx) := forall gtx',
      multi typ_ctx_red gtx gtx' ->  
      (forall p q l B, ctx_step_sl gtx' p q l B -> 
       exists gtx1 gtx2, multi typ_ctx_red gtx' gtx1 /\
                     ctx_step_f gtx1 p q l B gtx2) /\
      (forall p q,   ctx_step_r  gtx' q p   ->
       exists gtx1 gtx2 l B, multi typ_ctx_red gtx' gtx1 /\
                     ctx_step_f gtx1 p q l B gtx2).
  



(* a context path is a possibly infinite sequence of typing contexts *)
Notation ctx_path := (stream typ_ctx).

(* context paths are well defined if every step corresponds to an actual reduction step *)
Definition wdef gxs := (forall n G1 G2, 
                       stnth n gxs = Some G1 -> 
                       stnth (S n) gxs = Some G2 -> 
                       exists p q l B, ctx_step_f G1 p q l B G2) /\ 
                       (forall n G1 pt T, 
                       stnth n gxs = Some G1 -> 
                       G1 pt = Some T -> 
                       regLtt T).

(* fair path : communication that can happen actually eventually happens *)
Definition fair_path gxs := forall n Gl Gl' p q l B, 
                            stnth n gxs = Some Gl -> 
                            ctx_step_f Gl p q l B Gl' -> 
                            exists k l' B' G1 G2, n <= k /\ 
                            stnth k gxs = Some G1 /\ 
                            stnth (S k) gxs = Some G2 /\ 
                            ctx_step_f G1 p q l' B' G2.

(* live path : participant that wants to communicate will eventually communicate *)
Definition live_path gxs := 
           (forall n Gl p q, 
              stnth n gxs = Some Gl -> 
              ctx_step_s Gl p q -> 
              exists k l G1 G2 B, n <= k /\ 
              stnth k gxs = Some G1 /\ 
              stnth (S k) gxs = Some G2 /\ 
              ctx_step_f G1 p q l B G2) /\ 
           (forall n Gl p q, 
              stnth n gxs = Some Gl -> 
              ctx_step_r Gl q p -> 
              exists k l G1 G2 B, n <= k /\ 
              stnth k gxs = Some G1 /\ 
              stnth (S k) gxs = Some G2 /\ 
              ctx_step_f G1 p q l B G2).

(* means : the current ctx has a fair path which is live+ *)
Definition live_ctx_0 gxs := wdef gxs -> fair_path gxs -> live_path gxs.

(* context association with global types, assuming a good merge *)
Definition assoc_gctx `{good_merge} gtx G := 
  (forall pt, isgPartsC pt G -> exists T, gtx pt = Some T) /\ 
  (forall pt T, gtx pt = Some T -> exists T', projC G pt T' /\ subtypeC T T').

(* proj_G(\Delta) *)
Definition full_proj_assoc `{good_merge} gtx G := 
  (forall pt, isgPartsC pt G -> exists T, gtx pt = Some T) /\ 
  (forall pt T, gtx pt = Some T ->projC G pt T).

(* full projection is associated *)
Lemma full_proj_is_assoc `{good_merge} : forall gtx G, full_proj_assoc gtx G -> assoc_gctx gtx G.
Proof.
  intros.
  inversion H0; clear H0.
  constructor; try easy.
  intros. specialize(H2 pt T). fill_triv. exists T.
  split. easy.
  (* just transitivity of <=, instantiated by T *)
  apply stRefl.
Qed.

(* \Delta is associated, if it has some global type tree G that is regular and balanced that it is associated to *)
Definition is_assoc gtx `{good_merge} := exists G, assoc_gctx gtx G /\ regGtt G /\ balancedG G.


 
(* ------------------------------------------------------------------------- *)
(* Explicit local-type map variant of session typing.                         *)
(* ------------------------------------------------------------------------- *)


Definition typecheck_session `{good_merge} (qcontext: qubit_context) (s: session) (delta: typ_ctx) (Gtt: gtt):=
exists lqc,
regGtt Gtt /\
balancedG Gtt /\
assoc_gctx delta Gtt /\
partition _ _ qcontext lqc /\
length lqc = length delta.(elems _ _) /\
Permutation (map fst delta.(elems _ _)) (session_participants s) /\ (*This also ensures there are no sessions with duplicated participants.*)
forall p T qc, 
In (p, T, qc) (combine delta.(elems _ _) lqc) ->
exists P, s p = Some P /\
typecheck_process (nil, nil, qc) P T.

Lemma unfoldM_preserves_session_participants :
    forall M0 M1,
    unfoldM M0 M1 ->
    Permutation (session_participants M0) (session_participants M1).
Proof.
    intros M0 M1 Hunfold.
    unfold unfoldM in Hunfold.
    unfold session_participants.
    apply Permutation.NoDup_Permutation.
    - apply specs.
    - apply specs.
    - intros pt; split; intro Hin.
      + apply in_map_iff in Hin.
        destruct Hin as [[pt0 P0] [Hpt Hin]].
        simpl in Hpt; subst pt0.
        apply specs in Hin.
        destruct (Hunfold pt) as [[Hnone0 Hnone1]
            |[Psrc [Pdst [Hsome0 [Hsome1 Hpre]]]]].
        * rewrite Hnone0 in Hin; discriminate.
        * rewrite Hsome0 in Hin; inversion Hin; subst P0.
          apply in_map_iff.
          exists (pt, Pdst); split; [reflexivity|].
          apply specs; exact Hsome1.
      + apply in_map_iff in Hin.
        destruct Hin as [[pt0 P1] [Hpt Hin]].
        simpl in Hpt; subst pt0.
        apply specs in Hin.
        destruct (Hunfold pt) as [[Hnone0 Hnone1]
            |[Psrc [Pdst [Hsome0 [Hsome1 Hpre]]]]].
        * rewrite Hnone1 in Hin; discriminate.
        * rewrite Hsome1 in Hin; inversion Hin; subst P1.
          apply in_map_iff.
          exists (pt, Psrc); split; [reflexivity|].
          apply specs; exact Hsome0.
Qed.

(* version of typing rules where there is an explicit map into the local type 
Inductive typ_sess_with_Tx `{good_merge} : session -> gtt -> (participant -> option ltt) -> Prop :=
  | twx_sess : 
    forall M G Tx, balancedG G -> regGtt G ->
    (forall pt, isgPartsC pt G -> InS pt M) ->
    (forall pt P, M pt = Some P -> exists T T', Tx pt = Some T /\ cguardedP P /\ projC G pt T' /\ typ_proc nil nil P T /\ subtypeC T T') ->
    (forall pt, InS pt M <-> InS pt Tx) ->
    typ_sess_with_Tx M G Tx.


(* typ_sess_with_Tx is typ_sess with an explicit Tx *) 
Lemma typ_sess_with_Tx_forget `{good_merge} : forall M G gtx, 
  typ_sess_with_Tx M G gtx -> typ_sess M G.
Proof.
  intros.
  inversion H0. subst. unfold finiteF in *. unfold InS in *. rename H6 into Hk. constructor; try easy.
  intros.
  specialize(H4 pt P). fill_triv. destruct_exists_and. 
  split. easy. exists x1. split. easy. apply tc_sub with x0; try easy.
Qed.


(* on the other hand, we can also construct an explicit Tx by feeding back the exact projections *)
Lemma typ_sess_create `{good_merge} : forall M G,
  typ_sess M G -> exists Tx, typ_sess_with_Tx M G Tx.
Proof.
  intros.
  inversion H0; clear H0; subst.
  assert(exists Tx, 
          (forall pt P, M pt = Some P -> exists T T', Tx pt = Some T /\ cguardedP P /\ projC G pt T' /\ typ_proc nil nil P T /\ subtypeC T T') /\
          (forall pt, InS pt M <-> InS pt Tx)).
  {
    clear H1 H2 H3. unfold finiteF in H5. destruct H5 as (Mpt,(Ha,Hb)).
    revert Hb Ha H4. revert M.
    induction Mpt; intros.
    - exists (fun pt => None).
      split; intros.
      - specialize(Hb pt). destruct Hb. simpl in H2. assert False.
        apply H2. exists P. easy.
        easy.
      - split; intros.
        - specialize(Hb pt). destruct Hb; fill_triv. easy.
        - destruct H0. easy.
    - inversion Ha. subst. clear Ha.
      specialize(IHMpt (fun pt => if eqb pt a then None else M pt)).
      assert_concl_of IHMpt as Ha.
      {
        apply IHMpt; try easy; clear IHMpt.
        - intros.
          specialize(Hb pt). destruct Hb.
          split.
          - intro.
            specialize(string_dec pt a); intros. destruct H6; subst; try easy.
            assert(InS pt M). apply H0. right. easy.
            destruct H6. exists x.
            specialize(eqb_neq pt a); intros. destruct H7; fill_triv. rewrite H8.
            easy.
          - intro.
            destruct H5. case_eq (eqb pt a); intros.
            - rewrite H6 in H5. easy.
            - rewrite H6 in H5.
              assert(In pt (a :: Mpt)). apply H1. exists x. easy.
              specialize(eqb_neq pt a); intros. destruct H8; fill_triv.
              destruct H7; subst; try easy.
        - intros.
          case_eq (eqb pt a); intros.
          - rewrite H1 in H0. easy.
          - rewrite H1 in H0. specialize(H4 pt P). apply H4; try easy.
      }
      clear IHMpt. destruct Ha as (Tx,(Ha,Hc)).
      specialize(Hb a). assert(InS a M). apply Hb. left. easy.
      destruct H0 as (P,H0). specialize(H4 a P). fill_triv. destruct_exists_and.
      exists (fun pt => if eqb pt a then Some x else Tx pt). clear Hb.
      split.
      - intros.
        specialize(Ha pt P0). specialize(Hc pt).
        case_eq (eqb pt a); intros Hd; rewrite Hd in Ha Hc.
        - eexists. exists x. split. easy.
          specialize(eqb_eq pt a); intros. rewrite H7 in Hd. subst.
          rewrite H6 in H0. invert_all_some. split. easy. split. easy.
          split. easy. apply stRefl.
        - fill_triv. destruct_exists_and. exists x0. exists x1. easy.
      - intros.
        unfold InS in *.
        case_eq (eqb pt a); intros.
        - specialize(eqb_eq pt a); intros. rewrite H7 in H6. subst. rewrite H0.
          split; try eexists; try easy.
        - split; intros; fill_triv.
          - destruct H7. specialize(Ha pt x0). rewrite H6 in Ha. fill_triv. 
            destruct_exists_and. exists x1. easy.
          - specialize(Hc pt). destruct Hc; fill_triv. rewrite H6 in H9. easy.
  }
  destruct H0 as (Tx,(Ha, Hb)). exists Tx. constructor; try easy.
Qed.
  

(* typ_sess_with_Tx gives association (assuming Tx has the correct form) *)
Lemma typ_sess_is_assoc `{good_merge} : forall M G Tx,
  typ_sess_with_Tx M G Tx ->  
  assoc_gctx Tx G.  
Proof.
  intros. 
  inversion H0. subst. constructor; try easy.
  - intros.
    specialize(H6 pt). apply H6. apply H3. easy.
  - intros.
    specialize(H6 pt).
    assert(exists P, M pt = Some P). apply H6. exists T. easy.
    destruct H8 as (P,Ha).
    specialize(H4 pt P). fill_triv. destruct_exists_and. rewrite H7 in H4.
    invert_all_some. 
    exists x0. easy.
Qed.
*)










  
