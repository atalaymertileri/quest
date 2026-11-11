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
Definition assoc_gctx `{good_merge} (gtx:typ_ctx) G := 
  (forall pt, isgPartsC pt G -> exists T, gtx pt = Some T) /\ 
  (forall pt T, gtx pt = Some T -> exists T', projC G pt T' /\ subtypeC T T').

(* proj_G(\Delta) *)
Definition full_proj_assoc `{good_merge} (gtx:typ_ctx) G := 
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
