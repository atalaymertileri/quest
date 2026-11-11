From SQIR Require Import SQIR UnitaryOps.
From QuantumLib Require Import Matrix CauchySchwarz.
Require Import Lia Permutation Reals List.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import SST session substitution balanced.
Require Import QUEST.
From Paco Require Import paco.


Lemma variable_not_in_context_not_appears:
forall e y B context,
typecheck_expression context e B ->
~ (exists B', in_variable_context context y B') ->
appears_in_expression e y = false.
Proof.
  intros e y B context Htyped.
  induction Htyped; intro Habsent; simpl; eauto.
  - destruct (Nat.eqb y x) eqn:Heq; eauto.
    apply PeanoNat.Nat.eqb_eq in Heq; subst x.
    exfalso; apply Habsent.
    exists B; exact H.
  all: repeat match goal with
       | IH : _ -> appears_in_expression _ _ = false |- _ =>
           rewrite IH by exact Habsent
       end;
       reflexivity.
Qed.

Inductive value_has_sort : value -> sort -> Prop :=
| value_has_sort_nat : forall n, value_has_sort (Primitives.Nat n) header.Nat
| value_has_sort_bool : forall b, value_has_sort (Primitives.Bool b) header.Bool
| value_has_sort_qubit : forall q, value_has_sort (Primitives.QVal q) header.Qubit.

Lemma closed_expression_evaluates : forall context e B,
  typecheck_expression context e B ->
  closed_expression_at 0 e ->
  exists v, evaluate_expression e = Some v /\ value_has_sort v B.
Proof.
  intros context e B Htyped.
  induction Htyped; intro Hclosed; simpl in *.
  - exists (Primitives.Nat n); split; [reflexivity | constructor].
  - exists (Primitives.Bool b); split; [reflexivity | constructor].
  - exists (Primitives.QVal q); split; [reflexivity | constructor].
  - inversion Hclosed; subst; lia.
  - inversion Hclosed; subst.
    match goal with
    | Hargs : Forall _ (_ :: _ :: nil) |- _ =>
        let Ha := fresh "Ha" in
        let Hb := fresh "Hb" in
        pose proof (Forall_inv Hargs) as Ha;
        pose proof (Forall_inv (Forall_inv_tail Hargs)) as Hb
    end.
    destruct (IHHtyped1 Ha) as [va [Hva Hsorta]].
    destruct (IHHtyped2 Hb) as [vb [Hvb Hsortb]].
    inversion Hsorta; subst va. inversion Hsortb; subst vb.
    exists (Primitives.Nat (n + n0)); split;
      [simpl; rewrite Hva, Hvb; reflexivity | constructor].
  - inversion Hclosed; subst.
    match goal with
    | Hargs : Forall _ (_ :: _ :: nil) |- _ =>
        let Ha := fresh "Ha" in
        let Hb := fresh "Hb" in
        pose proof (Forall_inv Hargs) as Ha;
        pose proof (Forall_inv (Forall_inv_tail Hargs)) as Hb
    end.
    destruct (IHHtyped1 Ha) as [va [Hva Hsorta]].
    destruct (IHHtyped2 Hb) as [vb [Hvb Hsortb]].
    inversion Hsorta; subst va. inversion Hsortb; subst vb.
    exists (Primitives.Nat (n - n0)); split;
      [simpl; rewrite Hva, Hvb; reflexivity | constructor].
  - inversion Hclosed; subst.
    match goal with
    | Hargs : Forall _ (_ :: _ :: nil) |- _ =>
        let Ha := fresh "Ha" in
        let Hb := fresh "Hb" in
        pose proof (Forall_inv Hargs) as Ha;
        pose proof (Forall_inv (Forall_inv_tail Hargs)) as Hb
    end.
    destruct (IHHtyped1 Ha) as [va [Hva Hsorta]].
    destruct (IHHtyped2 Hb) as [vb [Hvb Hsortb]].
    inversion Hsorta; subst va. inversion Hsortb; subst vb.
    exists (Primitives.Bool (n <=? n0)); split;
      [simpl; rewrite Hva, Hvb; reflexivity | constructor].
  - inversion Hclosed; subst.
    match goal with
    | Hargs : Forall _ (_ :: _ :: nil) |- _ =>
        let Ha := fresh "Ha" in
        let Hb := fresh "Hb" in
        pose proof (Forall_inv Hargs) as Ha;
        pose proof (Forall_inv (Forall_inv_tail Hargs)) as Hb
    end.
    destruct (IHHtyped1 Ha) as [va [Hva Hsorta]].
    destruct (IHHtyped2 Hb) as [vb [Hvb Hsortb]].
    inversion Hsorta; subst va. inversion Hsortb; subst vb.
    exists (Primitives.Bool (andb b0 b1)); split;
      [simpl; rewrite Hva, Hvb; reflexivity | constructor].
  - inversion Hclosed; subst.
    match goal with
    | Hargs : Forall _ (_ :: _ :: nil) |- _ =>
        let Ha := fresh "Ha" in
        let Hb := fresh "Hb" in
        pose proof (Forall_inv Hargs) as Ha;
        pose proof (Forall_inv (Forall_inv_tail Hargs)) as Hb
    end.
    destruct (IHHtyped1 Ha) as [va [Hva Hsorta]].
    destruct (IHHtyped2 Hb) as [vb [Hvb Hsortb]].
    inversion Hsorta; subst va. inversion Hsortb; subst vb.
    exists (Primitives.Bool (orb b0 b1)); split;
      [simpl; rewrite Hva, Hvb; reflexivity | constructor].
  - inversion Hclosed; subst.
    match goal with
    | Hargs : Forall _ (_ :: _ :: nil) |- _ =>
        let Ha := fresh "Ha" in
        let Hb := fresh "Hb" in
        pose proof (Forall_inv Hargs) as Ha;
        pose proof (Forall_inv (Forall_inv_tail Hargs)) as Hb
    end.
    destruct (IHHtyped1 Ha) as [va [Hva Hsorta]].
    destruct (IHHtyped2 Hb) as [vb [Hvb Hsortb]].
    inversion Hsorta; subst va. inversion Hsortb; subst vb.
    exists (Primitives.Bool (Bool.eqb b0 b1)); split;
      [simpl; rewrite Hva, Hvb; reflexivity | constructor].
  - inversion Hclosed; subst.
    match goal with
    | Hargs : Forall _ (_ :: nil) |- _ =>
        let Ha := fresh "Ha" in pose proof (Forall_inv Hargs) as Ha
    end.
    destruct (IHHtyped Ha) as [va [Hva Hsorta]].
    inversion Hsorta; subst va.
    exists (Primitives.Bool (negb b)); split;
      [simpl; rewrite Hva; reflexivity | constructor].
Qed.

Lemma closed_qubit_expression_literal : forall context e,
  typecheck_expression context e Qubit ->
  closed_expression_at 0 e ->
  exists q, e = Val (Primitives.QVal q).
Proof.
  intros context e Htyped Hclosed.
  destruct e as [v | x | op args].
  - inversion Htyped; subst; eexists; reflexivity.
  - inversion Hclosed; subst; lia.
  - inversion Htyped.
Qed.

Lemma evaluate_closed_qubit_list : forall context lz,
  Forall (fun z => typecheck_expression context z Qubit) lz ->
  Forall (closed_expression_at 0) lz ->
  NoDup lz ->
  exists qs,
    Forall2 (fun z q => evaluate_expression z = Some (Primitives.QVal q)) lz qs /\
    map (fun q => Val (Primitives.QVal q)) qs = lz /\ NoDup qs.
Proof.
  intros context lz.
  induction lz as [|z zs IH]; intros Htyped Hclosed Hnd.
  - inversion Htyped; inversion Hclosed; inversion Hnd.
    exists nil; repeat split; constructor.
  - inversion Htyped as [|z0 zs0 Hz Hzt]; subst.
    inversion Hclosed as [|z0 zs0 Hc Hct]; subst.
    inversion Hnd as [|z0 zs0 Hnot Hndt]; subst.
    destruct (closed_qubit_expression_literal context z Hz Hc) as [q Hq].
    subst z.
    destruct (IH Hzt Hct Hndt) as [qs [Hevals [Hmap Hqs]]].
    exists (q :: qs); split.
    + constructor; [reflexivity | exact Hevals].
    + split.
      * simpl; f_equal; exact Hmap.
      * constructor.
        -- intro Hin.
           apply Hnot.
           pose proof (in_map (fun q0 => Val (Primitives.QVal q0)) qs q Hin) as Hmapped.
           rewrite Hmap in Hmapped; exact Hmapped.
        -- exact Hqs.
Qed.

Inductive process_head_view : Type :=
| ph_end (lz : list expression)
| ph_send (q : participant) (l : label) (e : expression)
| ph_recv (p : participant)
| ph_newq
| ph_unitary (n : nat) (U : base_Unitary n) (lz : list expression)
| ph_measure (z : expression)
| ph_ite (e : expression)
| ph_var (n : nat).

Definition recv_shape (cont : slist process) (branches : slist (sort * ltt)) :=
  forall l, onth l cont = None <-> onth l branches = None.

Inductive process_head_type : process -> process_head_view -> ltt -> Prop :=
| pht_end : forall lz,
    process_head_type (p_end lz) (ph_end lz) ltt_end
| pht_rec : forall P h T,
    process_head_type P h T ->
    process_head_type (p_rec P) h T
| pht_send : forall context p l e P B T,
    typecheck_expression context e B ->
    process_head_type (p_send p l e P) (ph_send p l e)
      (ltt_send p (fun n => if Nat.eqb n l then Some (B, T) else None))
| pht_recv : forall p cont branches,
    recv_shape cont branches ->
    process_head_type (p_recv p cont) (ph_recv p)
      (ltt_recv p (fun n => onth n branches))
| pht_newq : forall P T,
    process_head_type (p_newq P) ph_newq T
| pht_unitary : forall context n U lz P T,
    Datatypes.length lz = n ->
    Forall (fun z => typecheck_expression context z Qubit) lz ->
    NoDup lz ->
    process_head_type (p_unitary n U lz P) (ph_unitary n U lz) T
| pht_measure : forall context z P T,
    typecheck_expression context z Qubit ->
    process_head_type (p_measure z P) (ph_measure z) T
| pht_ite : forall context e P1 P0 T,
    typecheck_expression context e header.Bool ->
    process_head_type (p_ite e P1 P0) (ph_ite e) T
| pht_var : forall n lz T,
    process_head_type (p_var n lz) (ph_var n) T
| pht_sub : forall P h T T',
    process_head_type P h T ->
    subtypeC T T' ->
    process_head_type P h T'.

Definition process_head_view_closed (h : process_head_view) : Prop :=
  match h with
  | ph_end lz => Forall (closed_expression_at 0) lz
  | ph_send _ _ e => closed_expression_at 0 e
  | ph_recv _ => True
  | ph_newq => True
  | ph_unitary _ _ lz => Forall (closed_expression_at 0) lz
  | ph_measure z => closed_expression_at 0 z
  | ph_ite e => closed_expression_at 0 e
  | ph_var _ => True
  end.

Lemma process_head_type_closed_view : forall P h T,
  process_head_type P h T ->
  variable_closed_process_at 0 P ->
  process_head_view_closed h.
Proof.
  intros P h T Hhead.
  induction Hhead; intro Hclosed.
  - inversion Hclosed; subst; assumption.
  - inversion Hclosed; subst; eapply IHHhead; eauto.
  - inversion Hclosed; subst; assumption.
  - constructor.
  - constructor.
  - inversion Hclosed; subst; assumption.
  - inversion Hclosed; subst; assumption.
  - inversion Hclosed; subst; assumption.
  - constructor.
  - eapply IHHhead; exact Hclosed.
Qed.

Lemma typecheck_process_has_head : forall context P T,
  typecheck_process context P T -> exists h, process_head_type P h T.
Proof.
  intros context P T Htyped.
  induction Htyped.
  - exists ph_newq; exact (@pht_newq P T).
  - exists (ph_measure z); eapply pht_measure with (T := T); eassumption.
  - exists (ph_unitary n U lz); eapply pht_unitary with (T := T); eauto.
  - exists (ph_end lz); constructor.
  - exists (ph_send p l e); eapply pht_send with (T := T); eassumption.
  - exists (ph_recv p); apply pht_recv.
    pose proof (proj2 (SForall2_forall _ _ _ lP lBT) H) as Hshape.
    exact (proj1 (proj2 Hshape)).
  - exists (ph_ite e); eapply pht_ite with (T := T); eassumption.
  - destruct IHHtyped as [h Hh].
    exists h; constructor; assumption.
  - exists (ph_var X); constructor.
  - destruct IHHtyped as [h Hh].
    exists h; eapply pht_sub; eauto.
Qed.

Lemma boollis_not_all_false : forall n,
  ~ Forall (fun b => b = false) (boollis n).
Proof.
  induction n; simpl; intros H; inversion H; subst; try discriminate.
  apply IHn; assumption.
Qed.

Lemma guardP_var_not_all_false : forall xs n lz,
  Forall (fun b => b = false) xs -> guardP xs (p_var n lz) -> False.
Proof.
  intros xs n lz Hfalse Hguard.
  inversion Hguard; subst.
  eapply boollis_not_all_false; eauto.
Qed.

Lemma process_head_type_guarded_not_var : forall P h T xs,
  process_head_type P h T ->
  guardP xs P ->
  Forall (fun b => b = false) xs ->
  forall n, h <> ph_var n.
Proof.
  intros P h T xs Hhead.
  revert xs.
  induction Hhead as
    [lz
    | P h T Hrec IHrec
    | context p l e P B T Hexpr
    | p cont branches Hshape
    | P T
    | context n U lz P T Hlen Hforall Hnodup
    | context z P T Hz
    | context e P1 P0 T He
    | n lz T
    | P h T T' Hsub IHsub Hrel].
  - intros xs Hguard Hfalse n0 Heq; discriminate.
  - intros xs Hguard Hfalse n0 Heq.
    inversion Hguard; subst.
    + eapply IHrec with (xs := nil); eauto; constructor.
    + eapply IHrec with (xs := false :: xs); eauto.
  - intros xs Hguard Hfalse n0 Heq; discriminate.
  - intros xs Hguard Hfalse n0 Heq; discriminate.
  - intros xs Hguard Hfalse n0 Heq; discriminate.
  - intros xs Hguard Hfalse n0 Heq; discriminate.
  - intros xs Hguard Hfalse n0 Heq; discriminate.
  - intros xs Hguard Hfalse n0 Heq; discriminate.
  - intros xs Hguard Hfalse n0 Heq.
    inversion Heq; subst.
    eapply guardP_var_not_all_false; eauto.
  - intros xs Hguard Hfalse n0 Heq.
    eapply IHsub; eauto.
Qed.

Lemma onth_smap_none : forall A B (f : A -> B) n (xs : slist A),
  onth n (smap f xs) = None <-> onth n xs = None.
Proof.
  intros A B f n.
  induction n.
  - intros [x | o xs]; simpl.
    + split; intro H; discriminate.
    + destruct o; simpl.
      * split; intro H; discriminate.
      * split; intros; reflexivity.
  - intros [x | o xs]; simpl.
    + split; intros; reflexivity.
    + destruct o; simpl; apply IHn.
Qed.

Lemma recv_shape_smap : forall f cont branches,
  recv_shape cont branches -> recv_shape (smap f cont) branches.
Proof.
  intros f cont branches Hshape l.
  rewrite onth_smap_none.
  apply Hshape.
Qed.

Lemma process_head_type_subst : forall P h T x m n Q,
  process_head_type P h T ->
  (forall k, h <> ph_var k) ->
  process_head_type (substitutionP x m n Q P) h T.
Proof.
  intros P h T sx sm sd Q Hhead.
  revert sx sm sd Q.
  induction Hhead; intros sx sm sd Q Hnonvar; simpl.
  - constructor.
  - constructor; eapply IHHhead; eauto.
  - eapply pht_send; eauto.
  - eapply pht_recv; apply recv_shape_smap; assumption.
  - constructor.
  - eapply pht_unitary; eauto.
  - eapply pht_measure; eauto.
  - eapply pht_ite; eauto.
  - exfalso; apply (Hnonvar n); reflexivity.
  - eapply pht_sub; [eapply IHHhead |]; eauto.
Qed.

Definition process_root_view (P : process) : option process_head_view :=
  match P with
  | p_end lz => Some (ph_end lz)
  | p_rec _ => None
  | p_send p l e _ => Some (ph_send p l e)
  | p_recv p _ => Some (ph_recv p)
  | p_newq _ => Some ph_newq
  | p_unitary n U lz _ => Some (ph_unitary n U lz)
  | p_measure z _ => Some (ph_measure z)
  | p_ite e _ _ => Some (ph_ite e)
  | p_var n _ => None
  end.

Lemma process_head_type_pvar : forall k lz h T,
  process_head_type (p_var k lz) h T -> h = ph_var k.
Proof.
  intros k lz h T Hhead.
  remember (p_var k lz) as P eqn:HP in Hhead.
  induction Hhead; inversion HP; subst; try reflexivity; eauto.
Qed.

Lemma process_root_view_subst : forall P h T x m n Q,
  process_head_type P h T ->
  (forall k, h <> ph_var k) ->
  process_root_view (substitutionP x m n Q P) = process_root_view P.
Proof.
  intros P h T x m n Q Hhead Hnonvar.
  destruct P as [lz | P0 | p l e P0 | p cont | P0 | dim U lz P0
    | z P0 | e P1 P0 | k lz]; simpl; try reflexivity.
  pose proof (process_head_type_pvar k lz h T Hhead) as Hview.
  subst h.
  exfalso; exact (Hnonvar k eq_refl).
Qed.

Lemma process_head_type_rec_inv : forall P h T,
  process_head_type (p_rec P) h T ->
  exists T0, process_head_type P h T0 /\ subtypeC T0 T.
Proof.
  intros P h T Hhead.
  dependent induction Hhead.
  - exists T; split; [assumption | apply stRefl].
  - destruct (IHHhead P eq_refl) as [T0 [Hbody0 Hsub0]].
    exists T0; split; [exact Hbody0 | eapply stTrans; eauto].
Qed.

Lemma process_head_type_unfold_rec : forall P h T,
  process_head_type (p_rec P) h T ->
  (forall k, h <> ph_var k) ->
  process_head_type (substitutionP 0 0 0 (p_rec P) P) h T.
Proof.
  intros P h T Hhead Hnonvar.
  destruct (process_head_type_rec_inv _ _ _ Hhead) as [T0 [Hbody Hsub]].
  eapply pht_sub.
  - eapply process_head_type_subst; eauto.
  - exact Hsub.
Qed.

Lemma process_head_type_unravel : forall P h T,
  process_head_type P h T ->
  cguardedP P ->
  (forall k, h <> ph_var k) ->
  process_head_type (unravelP P) h T.
Proof.
  intros P h T Hhead Hguard Hnonvar.
  assert (Hiter : forall n P,
    mu_heightP P = n ->
    process_head_type P h T ->
    cguardedP P ->
    process_head_type (iter n unfold_recP P) h T).
  {
    induction n as [|n IH]; intros Q Hheight Htyped Hclosedguard.
    - destruct Q; simpl in Hheight; try discriminate; simpl; exact Htyped.
    - destruct Q; simpl in Hheight; try discriminate.
      inversion Hheight; subst.
      set (U := substitutionP 0 0 0 (p_rec Q) Q).
      assert (HtypedU : process_head_type U h T).
      { unfold U; eapply process_head_type_unfold_rec; [exact Htyped | exact Hnonvar]. }
      assert (HguardU : cguardedP U).
      {
        unfold U.
        eapply cguardedP_after_subst; [exact Hclosedguard |].
        constructor; constructor.
      }
      assert (HheightU : mu_heightP U = mu_heightP Q).
      { unfold U; symmetry; apply cguardedP_mu_rec; exact Hclosedguard. }
      change (process_head_type (iter (mu_heightP Q) unfold_recP U) h T).
      eapply IH; eauto.
  }
  unfold unravelP.
  eapply Hiter; eauto.
Qed.

Lemma process_head_type_nonrec_view : forall P h T,
  process_head_type P h T ->
  (forall Q, P <> p_rec Q) ->
  (forall k lz, P <> p_var k lz) ->
  process_root_view P = Some h.
Proof.
  intros P h T Hhead.
  induction Hhead; intros Hnrec Hnvar; simpl; try reflexivity.
  - exfalso; apply (Hnrec P); reflexivity.
  - exfalso; apply (Hnvar n lz); reflexivity.
  - eapply IHHhead; eauto.
Qed.

Lemma cguardedP_unravel_nonrec : forall P,
  cguardedP P ->
  (forall Q, unravelP P <> p_rec Q) /\
  (forall k lz, unravelP P <> p_var k lz).
Proof.
  intros P Hguard.
  destruct (cguardedP_unfolds P Hguard) as [_ [_ Hshape]].
  destruct Hshape as
    [Hend | [Hite | [Hsend | [Hrecv | [Hnew | [Hunit | Hmeasure]]]]]].
  - destruct Hend as [lz Heq].
    split.
    + intros x Hbad; rewrite Heq in Hbad; discriminate.
    + intros k lz0 Hbad; rewrite Heq in Hbad; discriminate.
  - destruct Hite as [e [P1 [P0 Heq]]].
    split.
    + intros x Hbad; rewrite Heq in Hbad; discriminate.
    + intros k lz Hbad; rewrite Heq in Hbad; discriminate.
  - destruct Hsend as [p [l [e [Q Heq]]]].
    split.
    + intros x Hbad; rewrite Heq in Hbad; discriminate.
    + intros k lz Hbad; rewrite Heq in Hbad; discriminate.
  - destruct Hrecv as [p [cont Heq]].
    split.
    + intros x Hbad; rewrite Heq in Hbad; discriminate.
    + intros k lz Hbad; rewrite Heq in Hbad; discriminate.
  - destruct Hnew as [Q Heq].
    split.
    + intros x Hbad; rewrite Heq in Hbad; discriminate.
    + intros k lz Hbad; rewrite Heq in Hbad; discriminate.
  - destruct Hunit as [n [U [lz [Q Heq]]]].
    split.
    + intros x Hbad; rewrite Heq in Hbad; discriminate.
    + intros k lz0 Hbad; rewrite Heq in Hbad; discriminate.
  - destruct Hmeasure as [z [Q Heq]].
    split.
    + intros x Hbad; rewrite Heq in Hbad; discriminate.
    + intros k lz Hbad; rewrite Heq in Hbad; discriminate.
Qed.

Lemma process_head_type_unravel_view : forall P h T,
  process_head_type P h T ->
  cguardedP P ->
  process_root_view (unravelP P) = Some h.
Proof.
  intros P h T Hhead Hguard.
  assert (Hnonvar : forall k, h <> ph_var k).
  {
    exact (process_head_type_guarded_not_var P h T nil Hhead
      (proj2 Hguard) (Forall_nil _)).
  }
  pose proof (process_head_type_unravel P h T Hhead Hguard Hnonvar) as HheadU.
  destruct (cguardedP_unravel_nonrec P Hguard) as [Hnrec Hnvar].
  eapply process_head_type_nonrec_view; eauto.
Qed.

Lemma wf_basis_vector_matrix : forall dim,
  0 < dim ->
  @WF_Matrix dim 1 (fun i j =>
    if (Nat.eqb i 0 && Nat.eqb j 0)%bool then Complex.C1 else Complex.C0).
Proof.
  intros dim Hdim i j Hout.
  unfold WF_Matrix.
  destruct (Nat.eqb i 0) eqn:Hi; simpl.
  - apply Nat.eqb_eq in Hi; subst i.
    destruct (Nat.eqb j 0) eqn:Hj; simpl.
    + apply Nat.eqb_eq in Hj; subst j.
      destruct Hout as [Hout | Hout]; simpl in *; lia.
    + reflexivity.
  - destruct (Nat.eqb j 0) eqn:Hj; simpl; reflexivity.
Qed.

Definition empty_quantum_state : quantum_state.
Proof.
  assert (Hmap : quantum_map_wf (@empty_fmap qubit_reference (participant * fin))).
  { unfold quantum_map_wf; simpl; split; constructor. }
  refine (existT _ (exist _ (@empty_fmap qubit_reference (participant * fin)) Hmap)
    (exist _ (fun i j =>
      if (Nat.eqb i 0 && Nat.eqb j 0)%bool then Complex.C1 else Complex.C0) _)).
  unfold state_vector_wf; simpl.
  assert (Hpow : 0 < 2 ^ Datatypes.length
    (elems qubit_reference (participant * fin) empty_fmap)).
  { induction (Datatypes.length
      (elems qubit_reference (participant * fin) empty_fmap)); simpl; lia. }
  split.
  - eapply wf_basis_vector_matrix; exact Hpow.
  - split.
    + right; split; [reflexivity | reflexivity].
    + intros n Hn; lia.
Defined.



Definition quantum_map_of (qs : quantum_state) : finite_map qubit_reference (participant * fin) :=
  proj1_sig (projT1 qs).

Lemma in_rev_elim : forall A (x : A) xs,
  In x (rev xs) -> In x xs.
Proof.
  intros A x xs; induction xs as [|y ys IH]; simpl; intros Hin.
  - contradiction.
  - rewrite in_app_iff in Hin.
    destruct Hin as [Hin | Hin].
    + right; apply IH; exact Hin.
    + simpl in Hin; destruct Hin as [Hin | Hin].
      * left; exact Hin.
      * contradiction.
Qed.

Lemma rev_cons_progress : forall A (x : A) xs,
  rev (x :: xs) = rev xs ++ [x].
Proof.
  intros A x xs.
  assert (Hrev_inj : forall ys zs : list A, rev ys = rev zs -> ys = zs).
  {
    intros ys zs Hrev.
    apply (f_equal (@rev A)) in Hrev.
    rewrite !rev_involutive in Hrev.
    exact Hrev.
  }
  apply Hrev_inj.
  rewrite rev_involutive.
  rewrite rev_app_distr.
  simpl.
  rewrite rev_involutive.
  reflexivity.
Qed.

Lemma in_rev_intro : forall A (x : A) xs,
  In x xs -> In x (rev xs).
Proof.
  intros A x xs Hin.
  apply in_rev_elim with (xs := rev xs).
  rewrite rev_involutive.
  exact Hin.
Qed.

Definition add_new_qubit_for_progress (st : quantum_state) (p : participant)
    (q : qubit_reference)
    (Hfresh : ~ In q (map fst (elems qubit_reference (participant * fin) (quantum_map_of st)))) :=
  add_new_qubit st p q Hfresh.

Lemma add_new_qubit_keys_append : forall st p q Hfresh,
  map fst (elems qubit_reference (participant * fin)
    (quantum_map_of (add_new_qubit_for_progress st p q Hfresh))) =
  map fst (elems qubit_reference (participant * fin) (quantum_map_of st)) ++ [q].
Proof.
  intros st p q Hfresh.
  unfold add_new_qubit_for_progress, add_new_qubit, quantum_map_of; simpl.
  rewrite replace_or_add_fresh_append by exact Hfresh.
  rewrite map_app; simpl; reflexivity.
Qed.

Lemma add_new_qubit_lookup : forall st p q Hfresh,
  quantum_map_of (add_new_qubit_for_progress st p q Hfresh) q =
  Some (p, Datatypes.length
    (elems qubit_reference (participant * fin) (quantum_map_of st))).
Proof.
  intros st p q Hfresh.
  unfold add_new_qubit_for_progress, add_new_qubit, quantum_map_of.
  cbn [proj1_sig projT1].
  rewrite insert_eq; reflexivity.
Qed.

Lemma add_new_qubit_preserves_lookup : forall st p x Hfresh q v,
  q <> x -> quantum_map_of st q = Some v ->
  quantum_map_of (add_new_qubit_for_progress st p x Hfresh) q = Some v.
Proof.
  intros st p x Hfresh q v Hneq Hlookup.
  unfold add_new_qubit_for_progress, add_new_qubit, quantum_map_of.
  cbn [proj1_sig projT1].
  rewrite insert_neq by (symmetry; exact Hneq).
  exact Hlookup.
Qed.
Opaque add_new_qubit_for_progress.

Fixpoint zero_state_for_qubits (p : participant) (qs : list qubit_reference)
    (Hnd : NoDup qs) {struct qs} :
    {st : quantum_state |
      map fst (elems qubit_reference (participant * fin) (quantum_map_of st)) = rev qs}.
Proof.
  destruct qs as [|q tl].
  - exists empty_quantum_state; reflexivity.
  - pose proof (proj1 (NoDup_cons_iff q tl) Hnd) as Hnd_parts.
    pose proof (proj1 Hnd_parts) as Hnot.
    pose proof (proj2 Hnd_parts) as Htail.
    pose (tail := zero_state_for_qubits p tl Htail).
    assert (Hfresh : ~ In q (map fst (elems qubit_reference
      (participant * fin) (quantum_map_of (proj1_sig tail))))).
    {
      intro Hin.
      apply Hnot.
      apply in_rev_elim.
      rewrite <- (proj2_sig tail).
      exact Hin.
    }
    exists (add_new_qubit_for_progress (proj1_sig tail) p q Hfresh).
    rewrite add_new_qubit_keys_append.
    rewrite (proj2_sig tail).
    apply rev_cons_progress.
Defined.

Lemma qubit_key_lookup : forall (qm : finite_map qubit_reference (participant * fin))
    (q : qubit_reference),
  In q (map fst (elems qubit_reference (participant * fin) qm)) ->
  exists v, qm q = Some v.
Proof.
  intros qm q Hin.
  apply in_map_iff in Hin.
  destruct Hin as [[q' v] [Hq Hin]].
  simpl in Hq; subst q'.
  exists v.
  apply (proj1 (proj2 (specs _ _ qm) q v)); exact Hin.
Qed.

Lemma zero_state_for_qubits_length : forall p qs Hnd,
  Datatypes.length (elems qubit_reference (participant * fin)
    (quantum_map_of (proj1_sig (zero_state_for_qubits p qs Hnd)))) =
  Datatypes.length qs.
Proof.
  intros p qs Hnd.
  pose proof (f_equal (@Datatypes.length qubit_reference)
    (proj2_sig (zero_state_for_qubits p qs Hnd))) as Hlen.
  rewrite length_map, length_rev in Hlen.
  exact Hlen.
Qed.

Lemma zero_state_for_qubits_lookup : forall p qs Hnd q,
  In q qs ->
  exists v, quantum_map_of (proj1_sig (zero_state_for_qubits p qs Hnd)) q = Some v.
Proof.
  intros p qs Hnd q Hin.
  apply qubit_key_lookup.
  rewrite (proj2_sig (zero_state_for_qubits p qs Hnd)).
  apply in_rev_intro; exact Hin.
Qed.

Lemma zero_state_for_qubits_owner_lookup : forall p qs Hnd q,
  In q qs ->
  exists n, quantum_map_of (proj1_sig (zero_state_for_qubits p qs Hnd)) q =
    Some (p, n).
Proof.
  intros p qs.
  induction qs as [|x xs IH]; intros Hnd q Hin.
  - contradiction.
  - inversion Hnd as [|x0 xs0 Hnot Hndtail]; subst.
    simpl in Hin; destruct Hin as [Heq | Hin].
    + subst q.
      cbn [zero_state_for_qubits].
      cbn [proj1_sig].
      rewrite add_new_qubit_lookup.
      eexists; reflexivity.
    + destruct (IH Hndtail q Hin) as [n Hlookup].
      assert (Hndtail_eq : Hndtail =
        proj2 (proj1 (NoDup_cons_iff x xs) Hnd)).
      { apply proof_irrelevance. }
      rewrite Hndtail_eq in Hlookup.
      cbn [zero_state_for_qubits].
      cbn [proj1_sig].
      rewrite add_new_qubit_preserves_lookup with (v := (p, n)); try assumption.
      * eexists; reflexivity.
      * intro Heq; subst x; apply Hnot; exact Hin.
Qed.

Lemma get_all_some_of_lookups : forall
  (qm : finite_map qubit_reference (participant * fin))
  (qs : list qubit_reference),
  (forall q, In q qs -> exists v, qm q = Some v) ->
  exists vs, get_all_values qm qs = Some vs.
Proof.
  intros qm qs Hlook.
  eapply get_all_values_some_of_lookups; exact Hlook.
Qed.

Lemma nodup_append_singleton_fresh : forall (A : Type) (xs : list A) x,
  NoDup xs -> ~ In x xs -> NoDup (xs ++ [x]).
Proof.
  intros A xs; induction xs as [|y ys IH]; intros x Hnd Hfresh; simpl.
  - constructor; [simpl; tauto | constructor].
  - inversion Hnd as [|y0 ys0 Hnot Htail]; subst.
    constructor.
    + intro Hin. apply in_app_iff in Hin.
      destruct Hin as [Hin | Hin].
      * apply Hnot. exact Hin.
      * simpl in Hin. destruct Hin as [Heq | Hin]; [subst; apply Hfresh; now left | contradiction].
    + apply IH.
      * exact Htail.
      * intro Hin. apply Hfresh. now right.
Qed.

Lemma base_Unitary_dim_positive : forall dim (U : base_Unitary dim), dim > 0.
Proof. intros dim U; destruct U; lia. Qed.

Lemma apply_unitary_non_none_of_lookups : forall
  (qm : finite_map qubit_reference (participant * fin))
  (Hqm : quantum_map_wf qm)
  (sv : state_vector (Datatypes.length (elems qubit_reference (participant * fin) qm)))
  (Hsv : state_vector_wf sv) (dim : nat) (U : base_Unitary dim)
  (qs : list qubit_reference) (Hlen : Datatypes.length qs = dim)
  (Hdim : dim > 0),
  NoDup qs ->
  0 < Datatypes.length (elems qubit_reference (participant * fin) qm) ->
  dim <= Datatypes.length (elems qubit_reference (participant * fin) qm) ->
  (forall q, In q qs -> exists v, qm q = Some v) ->
  apply_unitary qm Hqm sv Hsv U qs Hlen Hdim <> None.
Proof.
  intros qm Hqm sv Hsv dim U qs Hlen Hdim Hnd Hpositive Hbound Hlook.
  destruct (get_all_values_some_of_lookups qubit_reference (participant * fin)
    qm qs Hlook) as [lpn Hget].
  assert (Hcertified : get_all_values_certified qm qs <> None).
  {
    unfold get_all_values_certified.
    rewrite Hget; discriminate.
  }
  unfold apply_unitary.
  destruct (lt_dec 0 (Datatypes.length (elems qubit_reference (participant * fin) qm)))
    as [Hpositive' | Hempty]; [|lia].
  destruct (le_dec dim (Datatypes.length (elems qubit_reference (participant * fin) qm)))
    as [Hbound' | Htoo_large]; [|lia].
  destruct (NoDup_dec (TEQ := qr_dec) qs) as [Hnd' | Hbad].
  - destruct (get_all_values_certified qm qs) as [certified|] eqn:Hgetcert.
    + discriminate.
    + exfalso; apply Hcertified; reflexivity.
  - exfalso; apply Hbad; exact Hnd.
Qed.

Lemma apply_unitary_some_of_lookups : forall
  (qm : finite_map qubit_reference (participant * fin))
  (Hqm : quantum_map_wf qm)
  (sv : state_vector (Datatypes.length (elems qubit_reference (participant * fin) qm)))
  (Hsv : state_vector_wf sv) (dim : nat) (U : base_Unitary dim)
  (qs : list qubit_reference) (Hlen : Datatypes.length qs = dim)
  (Hdim : dim > 0),
  NoDup qs ->
  0 < Datatypes.length (elems qubit_reference (participant * fin) qm) ->
  dim <= Datatypes.length (elems qubit_reference (participant * fin) qm) ->
  (forall q, In q qs -> exists v, qm q = Some v) ->
  exists qs', apply_unitary qm Hqm sv Hsv U qs Hlen Hdim = Some qs'.
Proof.
  intros qm Hqm sv Hsv dim U qs Hlen Hdim Hnd Hpositive Hbound Hlook.
  pose proof (apply_unitary_non_none_of_lookups qm Hqm sv Hsv dim U qs Hlen Hdim
    Hnd Hpositive Hbound Hlook) as Hnonempty.
  destruct (apply_unitary qm Hqm sv Hsv U qs Hlen Hdim) as [qs'|] eqn:Happly.
  - exists qs'; reflexivity.
  - exfalso; apply Hnonempty; reflexivity.
Qed.

Lemma measurement_outcome_nonzero_of_wf : forall
  (qm : finite_map qubit_reference (participant * nat))
  (sv : state_vector (Datatypes.length (elems qubit_reference (participant * nat) qm)))
  (Hsv : state_vector_wf sv) index,
  index < Datatypes.length (elems qubit_reference (participant * nat) qm) ->
  exists result,
    norm (proj index (Datatypes.length (elems qubit_reference (participant * nat) qm))
      result × sv) <> 0%R.
Proof.
  intros qm sv Hsv index Hindex.
  pose proof Hsv as Hsv_copy.
  destruct Hsv_copy as [_ [_ Houtcomes]].
  destruct (Houtcomes index Hindex) as [result [Hnonzero _]].
  exists result.
  exact Hnonzero.
Qed.



Lemma quantum_map_lookup_index_lt : forall
  (qm : finite_map qubit_reference (participant * fin)) q p n,
  quantum_map_wf qm ->
  qm q = Some (p, n) ->
  n < Datatypes.length (elems qubit_reference (participant * fin) qm).
Proof.
  intros qm q p n Hwf Hlookup.
  unfold quantum_map_wf in Hwf.
  destruct Hwf as [_ Hbounds].
  assert (Hin : In (q, (p, n)) (elems qubit_reference (participant * fin) qm)).
  { apply (proj2 (specs _ _ qm) q (p, n)); exact Hlookup. }
  rewrite Forall_forall in Hbounds.
  apply Hbounds.
  apply in_map_iff.
  exists (q, (p, n)); split; [reflexivity | exact Hin].
Qed.

Lemma typecheck_session_has_component `{good_merge} : forall context M delta G p,
  typecheck_session context M delta G ->
  isgPartsC p G ->
  exists P T qc,
    M p = Some P /\ delta p = Some T /\
    typecheck_process (nil, nil, qc) P T.
Proof.
  intros context M delta G p Hsession Hpart.
  unfold typecheck_session in Hsession.
  destruct Hsession as [lqc [Hreg [Hbalanced [Hassoc [Hpartition
    [Hlength [Hperm Htyped]]]]]]].
  destruct Hassoc as [Hparts Htypes].
  destruct (Hparts p Hpart) as [T HT].
  assert (HinDelta : In (p, T) (elems participant ltt delta)).
  { apply (proj2 (specs _ _ delta) p T); exact HT. }
  assert (HinM : In p (session_participants M)).
  {
    unfold session_participants.
    eapply Permutation_in; [exact Hperm |].
    apply in_map_iff; exists (p, T); split; [reflexivity | exact HinDelta].
  }
  apply in_map_iff in HinM.
  destruct HinM as [[p' P] [Hp' HMIn]].
  simpl in Hp'; subst p'.
  assert (HM : M p = Some P).
  { apply (proj2 (specs _ _ M) p P); exact HMIn. }
  assert (Hlength_le : Datatypes.length (elems participant ltt delta) <= Datatypes.length lqc).
  { rewrite <- Hlength; lia. }
  destruct (in_combine_ex_r (elems participant ltt delta) lqc
    Hlength_le (p, T) HinDelta) as [qc Htriple].
  destruct (Htyped p T qc Htriple) as [P' [HM' Hproc]].
  rewrite HM in HM'; inversion HM'; subst P'.
  exists P, T, qc; repeat split; assumption.
Qed.

Lemma typecheck_session_has_component_projection `{good_merge} : forall context M delta G p,
  typecheck_session context M delta G ->
  isgPartsC p G ->
  exists P T qc Tproj,
    M p = Some P /\ delta p = Some T /\
    typecheck_process (nil, nil, qc) P T /\
    projC G p Tproj /\ subtypeC T Tproj.
Proof.
  intros context M delta G p Hsession Hpart.
  destruct (typecheck_session_has_component context M delta G p Hsession Hpart)
    as [P [T [qc [HM [Hdelta Htyped]]]]].
  unfold typecheck_session in Hsession.
  destruct Hsession as [lqc [_ [_ [Hassoc _]]]].
  destruct Hassoc as [_ Hassoc].
  destruct (Hassoc p T Hdelta) as [Tproj [Hproj Hsub]].
  exists P, T, qc, Tproj.
  split; [exact HM |].
  split; [exact Hdelta |].
  split; [exact Htyped |].
  split; assumption.
Qed.

Lemma subtypeC_right_send_inv : forall T p f,
  subtypeC T (ltt_send p f) -> exists g, T = ltt_send p g.
Proof.
  intros T p f Hsub.
  destruct T as [|r g|r g].
  - exfalso; pinversion Hsub; try apply sub_mon; discriminate.
  - exfalso; pinversion Hsub; try apply sub_mon; discriminate.
  - pinversion Hsub; try apply sub_mon; subst; eexists; reflexivity.
Qed.

Lemma subtypeC_right_recv_inv : forall T p f,
  subtypeC T (ltt_recv p f) -> exists g, T = ltt_recv p g.
Proof.
  intros T p f Hsub.
  destruct T as [|r g|r g].
  - exfalso; pinversion Hsub; try apply sub_mon; discriminate.
  - pinversion Hsub; try apply sub_mon; subst; eexists; reflexivity.
  - exfalso; pinversion Hsub; try apply sub_mon; discriminate.
Qed.

Lemma subtypeC_send_inv : forall p f T,
  subtypeC (ltt_send p f) T -> exists g, T = ltt_send p g.
Proof.
  intros p f T Hsub.
  destruct T as [|r g|r g].
  - exfalso. pinversion Hsub; try apply sub_mon; discriminate.
  - exfalso. pinversion Hsub; try apply sub_mon; discriminate.
  - pinversion Hsub; try apply sub_mon; subst; eexists; reflexivity.
Qed.

Lemma subtypeC_recv_inv : forall p f T,
  subtypeC (ltt_recv p f) T -> exists g, T = ltt_recv p g.
Proof.
  intros p f T Hsub.
  destruct T as [|r g|r g].
  - exfalso. pinversion Hsub; try apply sub_mon; discriminate.
  - pinversion Hsub; try apply sub_mon; subst; eexists; reflexivity.
  - exfalso. pinversion Hsub; try apply sub_mon; discriminate.
Qed.

Lemma subtypeC_send_branch : forall p f g n s t,
  subtypeC (ltt_send p f) (ltt_send p g) ->
  f n = Some (s, t) ->
  exists t', g n = Some (s, t') /\ subtypeC t t'.
Proof.
  intros p f g n s t Hsub Hbranch.
  pinversion Hsub.
  match goal with
  | Hbranches : forall k, _ |- _ =>
      specialize (Hbranches n); rewrite Hbranch in Hbranches;
      destruct Hbranches as [Hnone | Hsome]; [discriminate |]
  end.
  destruct Hsome as [s' [t0 [t' [Hf [Hg Hsub']]]]].
  inversion Hf; subst s' t0.
  exists t'; split.
  - exact Hg.
  - pclearbot; exact Hsub'.
  apply sub_mon.
Qed.

Lemma subtypeC_recv_branch : forall p f g n s t',
  subtypeC (ltt_recv p f) (ltt_recv p g) ->
  g n = Some (s, t') ->
  exists t, f n = Some (s, t) /\ subtypeC t t'.
Proof.
  intros p f g n s t' Hsub Hbranch.
  pinversion Hsub.
  match goal with
  | Hbranches : forall k, _ |- _ =>
      specialize (Hbranches n); rewrite Hbranch in Hbranches;
      destruct Hbranches as [Hnone | Hsome]; [discriminate |]
  end.
  destruct Hsome as [s' [t [t0 [Hf [Hg Hsub']]]]].
  inversion Hg; subst s' t0.
  exists t; split.
  - exact Hf.
  - pclearbot; exact Hsub'.
  apply sub_mon.
Qed.

Lemma projC_send_root_branch `{good_merge} : forall p q f g n s t,
  projC (gtt_send p q f) p (ltt_send q g) ->
  g n = Some (s, t) ->
  p <> q /\ exists G', f n = Some (s, G').
Proof.
  intros p q f g n s t Hproj Hbranch.
  unfold projC, projectionC in Hproj.
  pinversion Hproj; try apply proj_mon.
  - match goal with
    | Hneq : _ <> _, Hrel : forall k, _ |- _ =>
        split; [exact Hneq |]; specialize (Hrel n);
        destruct Hrel as [[Hfnone Hgnone] | [s' [G' [t' [Hf [Hg _]]]]]];
        [rewrite Hbranch in Hgnone; discriminate |];
        rewrite Hbranch in Hg; inversion Hg; subst; exists G'; exact Hf
    end.
  - exfalso; congruence.
Qed.

Lemma projC_recv_root_branch `{good_merge} : forall p q f g n s t,
  projC (gtt_send p q f) q (ltt_recv p (fun k => g k)) ->
  g n = Some (s, t) ->
  p <> q /\ exists G', f n = Some (s, G').
Proof.
  intros p q f g n s t Hproj Hbranch.
  unfold projC, projectionC in Hproj.
  pinversion Hproj; try apply proj_mon.
  - match goal with
    | Hneq : _ <> _, Hrel : forall k, _ |- _ =>
        split; [exact Hneq |]; specialize (Hrel n);
        destruct Hrel as [[Hfnone Hgnone] | [s' [G' [t' [Hf [Hg _]]]]]];
        [rewrite Hbranch in Hgnone; discriminate |];
        rewrite Hbranch in Hg; inversion Hg; subst; exists G'; exact Hf
    end.
  - exfalso; congruence.
Qed.

Lemma projC_send_root_shape `{good_merge} : forall p q f T,
  projC (gtt_send p q f) p T -> exists g, T = ltt_send q g.
Proof.
  intros p q f T Hproj.
  unfold projC, projectionC in Hproj.
  pinversion Hproj; try apply proj_mon.
  - exfalso; match goal with
    | Hnot : isgPartsC p (gtt_send p q f) -> False |- _ => apply Hnot; constructor
    end.
  - exfalso; congruence.
  - match goal with
    | Htype : ltt_send q ?branches = T |- _ => subst T; exists branches; reflexivity
    end.
  - exfalso; congruence.
Qed.

Lemma projC_recv_root_shape `{good_merge} : forall p q f T,
  projC (gtt_send p q f) q T -> exists g, T = ltt_recv p g.
Proof.
  intros p q f T Hproj.
  unfold projC, projectionC in Hproj.
  pinversion Hproj; try apply proj_mon.
  - exfalso; match goal with
    | Hnot : isgPartsC q (gtt_send p q f) -> False |- _ => apply Hnot; constructor
    end.
  - match goal with
    | Htype : ltt_recv p ?branches = T |- _ => subst T; exists branches; reflexivity
    end.
  - exfalso; congruence.
  - exfalso; congruence.
Qed.

Lemma projC_send_root_local_branch `{good_merge} : forall p q f g n s G',
  projC (gtt_send p q f) p (ltt_send q g) ->
  f n = Some (s, G') -> exists T, g n = Some (s, T).
Proof.
  intros p q f g n s G' Hproj Hglobal.
  unfold projC, projectionC in Hproj.
  pinversion Hproj; try apply proj_mon.
  - match goal with
    | Hrel : forall k, _ |- _ =>
        specialize (Hrel n);
        destruct Hrel as [[Hfnone HgNone] | [s' [G0 [T [Hf [Hg _]]]]]];
        [rewrite Hglobal in Hfnone; discriminate |];
        rewrite Hglobal in Hf; inversion Hf; subst; exists T; exact Hg
    end.
  - exfalso; congruence.
Qed.

Lemma projC_recv_root_local_branch `{good_merge} : forall p q f g n s G',
  projC (gtt_send p q f) q (ltt_recv p g) ->
  f n = Some (s, G') -> exists T, g n = Some (s, T).
Proof.
  intros p q f g n s G' Hproj Hglobal.
  unfold projC, projectionC in Hproj.
  pinversion Hproj; try apply proj_mon.
  - match goal with
    | Hin : forall k, _ |- _ =>
        specialize (Hin n);
        destruct Hin as [[Hfnone HgNone] | [s' [G0 [T [Hf [Hg _]]]]]];
        [rewrite Hglobal in Hfnone; discriminate |];
        rewrite Hglobal in Hf; inversion Hf; subst; exists T; exact Hg
    end.
  - exfalso; congruence.
Qed.

Lemma process_head_type_send_info : forall p l e P T,
  process_head_type (p_send p l e P) (ph_send p l e) T ->
  exists context B f T0,
    typecheck_expression context e B /\
    T = ltt_send p f /\ f l = Some (B, T0).
Proof.
  intros p l e P T Hhead.
  dependent induction Hhead.
  - exists context, B, (fun n => if Nat.eqb n l then Some (B, T) else None), T.
    split; [assumption |]. split; [reflexivity |].
    rewrite Nat.eqb_refl; reflexivity.
  - destruct (IHHhead p l e P eq_refl eq_refl)
      as [context0 [B0 [f0 [T0 [Hexpr [HT0 Hbranch]]]]]].
    rewrite HT0 in H.
    destruct (subtypeC_send_inv p f0 T' H) as [g Hg].
    rewrite Hg in H.
    destruct (subtypeC_send_branch p f0 g l B0 T0 H Hbranch)
      as [T1 [Hbranch1 _]].
    exists context0, B0, g, T1.
    split; [exact Hexpr |]. split; [exact Hg | exact Hbranch1].
Qed.

Lemma process_head_type_recv_info : forall p cont T,
  process_head_type (p_recv p cont) (ph_recv p) T ->
  exists f, T = ltt_recv p f /\
    forall n s T0, f n = Some (s, T0) -> onth n cont <> None.
Proof.
  intros p cont T Hhead.
  dependent induction Hhead.
  - exists (fun n => onth n branches); split; [reflexivity |].
    intros n s T0 Hsome.
    intro Hnone.
    apply (proj1 (H n)) in Hnone.
    rewrite Hnone in Hsome; discriminate.
  - destruct (IHHhead p cont eq_refl eq_refl) as [f0 [HT0 Hcovered]].
    rewrite HT0 in H.
    destruct (subtypeC_recv_inv p f0 T' H) as [g Hg].
    rewrite Hg in H.
    exists g; split; [exact Hg |].
    intros n s T0 Hsome.
    destruct (subtypeC_recv_branch p f0 g n s T0 H Hsome)
      as [T1 [Hsource _]].
    eapply Hcovered; exact Hsource.
Qed.

Lemma subtypeC_end_inv : forall T,
  subtypeC ltt_end T -> T = ltt_end.
Proof.
  intros T Hsub.
  destruct T as [|p f|p f]; [reflexivity | |].
  - exfalso; pinversion Hsub; try apply sub_mon.
  - exfalso; pinversion Hsub; try apply sub_mon.
Qed.

Lemma process_head_type_end_info : forall lz T,
  process_head_type (p_end lz) (ph_end lz) T -> T = ltt_end.
Proof.
  intros lz T Hhead.
  dependent induction Hhead.
  - reflexivity.
  - pose proof (IHHhead lz eq_refl eq_refl) as Hbody.
    rewrite Hbody in H.
    eapply subtypeC_end_inv; exact H.
Qed.

Lemma process_head_type_ite_expr : forall e P1 P0 T,
  process_head_type (p_ite e P1 P0) (ph_ite e) T ->
  exists context, typecheck_expression context e header.Bool.
Proof.
  intros e P1 P0 T Hhead.
  dependent induction Hhead.
  - exists context; exact H.
  - destruct (IHHhead e P1 P0 eq_refl eq_refl) as [context0 Hexpr].
    exists context0; exact Hexpr.
Qed.

Lemma process_head_type_measure_expr : forall z P T,
  process_head_type (p_measure z P) (ph_measure z) T ->
  exists context, typecheck_expression context z Qubit.
Proof.
  intros z P T Hhead.
  dependent induction Hhead.
  - exists context; exact H.
  - destruct (IHHhead z P eq_refl eq_refl) as [context0 Hexpr].
    exists context0; exact Hexpr.
Qed.

Lemma process_head_type_unitary_info : forall n U lz P T,
  process_head_type (p_unitary n U lz P) (ph_unitary n U lz) T ->
  exists context,
    Datatypes.length lz = n /\
    Forall (fun z => typecheck_expression context z Qubit) lz /\ NoDup lz.
Proof.
  intros n U lz P T Hhead.
  dependent induction Hhead.
  - exists context; repeat split; assumption.
  - destruct (IHHhead n U lz P eq_refl eq_refl)
      as [context0 [Hlen [Htyped Hnd]]].
    exists context0; repeat split; assumption.
Qed.

Lemma unfoldM_refl : forall M, unfoldM M M.
Proof.
  intros M p.
  destruct (M p) as [P|] eqn:Hp.
  - right; exists P, P; repeat split; try assumption; constructor.
  - left; auto.
Qed.

Lemma unfoldM_trans : forall M1 M2 M3,
  unfoldM M1 M2 -> unfoldM M2 M3 -> unfoldM M1 M3.
Proof.
  intros M1 M2 M3 H12 H23 p.
  destruct (H12 p) as [[H10 H20] | [P1 [P2 [H10 [H20 Hpre12]]]]];
  destruct (H23 p) as [[H20' H30] | [P2' [P3 [H20' [H30 Hpre23]]]]].
  - left; split; congruence.
  - rewrite H20 in H20'; discriminate.
  - rewrite H20 in H20'; discriminate.
  - rewrite H20 in H20'; inversion H20'; subst P2'.
    right; exists P1, P3; repeat split; try assumption.
    eapply gttT; [exact Hpre12 | exact Hpre23].
Qed.

Lemma unfoldM_insert_one : forall (M : session) (p : participant) P P',
  M p = Some P -> precongP P P' ->
  unfoldM M (insert (KEQ:=participant_dec) M p P').
Proof.
  intros M p P P' Hp Hpre r.
  destruct (participant_dec r p) as [Heq | Hneq].
  - subst r.
    right; exists P, P'; repeat split; try assumption.
    rewrite insert_eq; reflexivity.
  - destruct (M r) as [Q|] eqn:Hr.
    + right; exists Q, Q; split; [reflexivity |].
      split; [rewrite insert_neq by (symmetry; exact Hneq); exact Hr | constructor].
    + left; split; [reflexivity |].
      rewrite insert_neq by (symmetry; exact Hneq); exact Hr.
Qed.

Lemma unfoldM_insert_two : forall (M : session) (p q : participant) P Q P' Q',
  p <> q -> M p = Some P -> M q = Some Q ->
  precongP P P' -> precongP Q Q' ->
  unfoldM M (insert (KEQ:=participant_dec)
    (insert (KEQ:=participant_dec) M q Q') p P').
Proof.
  intros M p q P Q P' Q' Hneq Hp Hq Hp' Hq'.
  eapply unfoldM_trans with
    (M2 := insert (KEQ:=participant_dec) M q Q').
  - eapply unfoldM_insert_one; eauto.
  - eapply unfoldM_insert_one with (P := P) (P' := P'); eauto.
    rewrite insert_neq by (symmetry; exact Hneq); exact Hp.
Qed.

Lemma step_after_unfold_one : forall (M : session) (p : participant) P Pu Pu'
  (qs1 qs2 : quantum_state) (a : action) (pi : R),
  M p = Some P -> precongP P Pu ->
  step (qs1, insert (KEQ:=participant_dec) M p Pu) a
    (qs2, insert (KEQ:=participant_dec) (insert (KEQ:=participant_dec) M p Pu) p Pu') pi ->
  step (qs1, M) a
    (qs2, insert (KEQ:=participant_dec) (insert (KEQ:=participant_dec) M p Pu) p Pu') pi.
Proof.
  intros M p P Pu Pu' qs1 qs2 a pi Hp Hpre Hstep.
  eapply Congr with
    (M1' := insert (KEQ:=participant_dec) M p Pu).
  - eapply unfoldM_insert_one; eauto.
  - exact Hstep.
Qed.

Lemma step_after_unfold_two : forall (M : session) (p q : participant) P Q Pu Qu P' Q'
  (qs1 qs2 : quantum_state) (a : action) (pi : R),
  p <> q -> M p = Some P -> M q = Some Q ->
  precongP P Pu -> precongP Q Qu ->
  step (qs1, insert (KEQ:=participant_dec) (insert (KEQ:=participant_dec) M q Qu) p Pu) a
    (qs2, insert (KEQ:=participant_dec)
      (insert (KEQ:=participant_dec)
        (insert (KEQ:=participant_dec) (insert (KEQ:=participant_dec) M q Qu) p Pu) q Q') p P') pi ->
  step (qs1, M) a
    (qs2, insert (KEQ:=participant_dec)
      (insert (KEQ:=participant_dec)
        (insert (KEQ:=participant_dec) (insert (KEQ:=participant_dec) M q Qu) p Pu) q Q') p P') pi.
Proof.
  intros M p q P Q Pu Qu P' Q' qs1 qs2 a pi Hneq Hp Hq HpreP HpreQ Hstep.
  eapply Congr with
    (M1' := insert (KEQ:=participant_dec) (insert (KEQ:=participant_dec) M q Qu) p Pu).
  - eapply unfoldM_insert_two; eauto.
  - exact Hstep.
Qed.

Definition is_internal_head_view (h : process_head_view) : Prop :=
  match h with
  | ph_newq | ph_unitary _ _ _ | ph_measure _ | ph_ite _ => True
  | _ => False
  end.

Lemma internal_head_step : forall (M : session) p P Pu h T,
  M p = Some P ->
  variable_closed_process_at 0 P ->
  process_head_type Pu h T ->
  process_head_view_closed h ->
  process_root_view Pu = Some h ->
  is_internal_head_view h ->
  exists qs1 qs2 Pu' pi,
    step (qs1, insert (KEQ:=participant_dec) M p Pu) (Tau p)
      (qs2, insert (KEQ:=participant_dec)
        (insert (KEQ:=participant_dec) M p Pu) p Pu') pi.
Proof.
  intros M p P Pu h T HM Hclosed Hhead Hview Hroot Hinternal.
  destruct h as [lz|q l e|q| |dim U lz|z|e|k]; simpl in Hinternal;
    try contradiction.
  - destruct Pu as [lz0|P0|sp sl e0 P0|sp cont|P0|dim0 U0 lz0 P0
      |z0 P0|e0 P1 P0|k0]; simpl in Hroot; try discriminate.
    inversion Hroot; subst.
    pose (freshq := fresh_qubit_reference
      (map fst (elems qubit_reference (participant * fin)
        (quantum_map_of empty_quantum_state)))).
    pose (qnew := proj1_sig freshq).
    pose (Hfresh := proj2_sig freshq).
    exists empty_quantum_state,
      (add_new_qubit empty_quantum_state p qnew Hfresh),
      (subst_expression_in_process 0 0 (Val (Primitives.QVal qnew)) P0), 1%R.
    eapply New with (q := qnew) (Hfresh := Hfresh).
    rewrite insert_eq; reflexivity.
  - destruct Pu as [lz0|P0|sp sl e0 P0|sp cont|P0|dim0 U0 lz0 P0
      |z0 P0|e0 P1 P0|k0]; simpl in Hroot; try discriminate.
    inversion Hroot; subst.
    dependent destruction H1.
    destruct (process_head_type_unitary_info dim U lz P0 T Hhead)
      as [context [Hlen [Htyped Hndexpr]]].
    destruct (evaluate_closed_qubit_list context lz Htyped Hview Hndexpr)
      as [qs [Hevals [Hmap Hndqs]]].
    pose (freshq := fresh_qubit_reference qs).
    pose (dummy := proj1_sig freshq).
    pose proof (nodup_append_singleton_fresh qubit_reference qs dummy
      Hndqs (proj2_sig freshq)) as Hndall.
    pose (zst := zero_state_for_qubits p (qs ++ [dummy]) Hndall).
    pose (qs1 := proj1_sig zst).
    pose proof (zero_state_for_qubits_length p (qs ++ [dummy]) Hndall) as HstateLen.
    rewrite length_app in HstateLen; simpl in HstateLen.
    change (Datatypes.length (elems qubit_reference (participant * fin)
      (quantum_map_of qs1)) = Datatypes.length qs + 1) in HstateLen.
    pose proof (f_equal (@Datatypes.length expression) Hmap) as Hmaplen.
    rewrite length_map in Hmaplen.
    assert (Hqslen : Datatypes.length qs = dim) by lia.
    pose proof (base_Unitary_dim_positive dim U) as Hdim.
    assert (Hstatepos : 0 < Datatypes.length
      (elems qubit_reference (participant * fin) (quantum_map_of qs1))) by lia.
    assert (Hstatebound : dim <= Datatypes.length
      (elems qubit_reference (participant * fin) (quantum_map_of qs1))) by lia.
    assert (Hlook : forall q0, In q0 qs -> exists v,
      (quantum_map_of qs1) q0 = Some v).
    {
      intros q0 Hin.
      destruct (zero_state_for_qubits_owner_lookup p (qs ++ [dummy]) Hndall q0)
        as [n Howner].
      - apply in_app_iff; left; exact Hin.
      - exists (p, n); exact Howner.
    }
    destruct (apply_unitary_some_of_lookups
      (quantum_map_of qs1) (proj2_sig (projT1 qs1))
      (proj1_sig (projT2 qs1)) (proj2_sig (projT2 qs1))
      dim U qs Hqslen Hdim Hndqs Hstatepos Hstatebound Hlook)
      as [qs2 Happly].
    exists qs1, qs2, P0, 1%R.
    eapply Unitary with (Hlen := Hqslen) (Hdim := Hdim).
    + rewrite insert_eq; rewrite Hmap; reflexivity.
    + exact Happly.
    + exact Hndqs.
    + apply Forall_forall; intros q0 Hin.
      destruct (zero_state_for_qubits_owner_lookup p (qs ++ [dummy]) Hndall q0)
        as [n Howner].
      * apply in_app_iff; left; exact Hin.
      * exists n; exact Howner.
  - destruct Pu as [lz0|P0|sp sl e0 P0|sp cont|P0|dim0 U0 lz0 P0
      |z0 P0|e0 P1 P0|k0]; simpl in Hroot; try discriminate.
    inversion Hroot; subst.
    destruct (process_head_type_measure_expr z P0 T Hhead)
      as [context Htyped].
    destruct (closed_qubit_expression_literal context z Htyped Hview)
      as [q Hq]; subst z.
    assert (Hndq : NoDup [q]) by (constructor; [simpl; tauto | constructor]).
    pose (zst := zero_state_for_qubits p [q] Hndq).
    pose (qs1 := proj1_sig zst).
    destruct (zero_state_for_qubits_owner_lookup p [q] Hndq q
      (or_introl eq_refl)) as [n Hlookup].
    assert (Hindex : n < Datatypes.length
      (elems qubit_reference (participant * fin) (quantum_map_of qs1))).
    {
      eapply quantum_map_lookup_index_lt; [apply proj2_sig | exact Hlookup].
    }
    assert (Hstatepos : 0 < Datatypes.length
      (elems qubit_reference (participant * fin) (quantum_map_of qs1))) by lia.
    destruct (measurement_outcome_nonzero_of_wf
      (quantum_map_of qs1) (proj1_sig (projT2 qs1))
      (proj2_sig (projT2 qs1)) n Hindex) as [r Hnonzero].
    destruct (measure_qubit_from_nonzero
      (quantum_map_of qs1) (proj2_sig (projT1 qs1))
      (proj1_sig (projT2 qs1)) (proj2_sig (projT2 qs1))
      q p n r Hlookup Hstatepos Hnonzero) as [pi qs2] eqn:Hmeasure.
    exists qs1, qs2, (subst_expression_in_process 0 0 (Val (Primitives.Bool r)) P0), pi!.
    eapply Meas with (n := n) (r := r) (pi := pi)
      (q_state2 := qs2) (Hlookup := Hlookup)
      (Hlen := Hstatepos) (Hnonzero := Hnonzero).
    + rewrite insert_eq; reflexivity.
    + symmetry; exact Hmeasure.
  - destruct Pu as [lz0|P0|sp sl e0 P0|sp cont|P0|dim0 U0 lz0 P0
      |z0 P0|e0 P1 P0|k0]; simpl in Hroot; try discriminate.
    inversion Hroot; subst.
    destruct (process_head_type_ite_expr e P1 P0 T Hhead)
      as [context Htyped].
    destruct (closed_expression_evaluates context e header.Bool Htyped Hview)
      as [v [Heval Hsort]].
    destruct v as [n|b|q].
    + inversion Hsort.
    + inversion Hsort; subst.
      destruct b.
      * exists empty_quantum_state, empty_quantum_state, P1, 1%R.
        eapply If_1.
        -- rewrite insert_eq; reflexivity.
        -- exact Heval.
      * exists empty_quantum_state, empty_quantum_state, P0, 1%R.
        eapply If_0.
        -- rewrite insert_eq; reflexivity.
        -- exact Heval.
    + inversion Hsort.
Qed.

Lemma progress_internal_transition : forall (M : session) p P h T,
  M p = Some P ->
  cguardedP P ->
  variable_closed_process_at 0 P ->
  process_head_type (unravelP P) h T ->
  process_head_view_closed h ->
  process_root_view (unravelP P) = Some h ->
  is_internal_head_view h ->
  exists qs1 qs2 M' pi,
    step (qs1, M) (Tau p) (qs2, M') pi.
Proof.
  intros M p P h T HM Hguard Hclosed Hhead Hview Hroot Hinternal.
  destruct (cguardedP_unfolds P Hguard) as [_ [Hpre _]].
  destruct (internal_head_step M p P (unravelP P) h T
    HM Hclosed Hhead Hview Hroot Hinternal)
    as [qs1 [qs2 [Pu' [pi Hstep]]]].
  exists qs1, qs2,
    (insert (KEQ:=participant_dec)
      (insert (KEQ:=participant_dec) M p (unravelP P)) p Pu'), pi.
  eapply step_after_unfold_one; eauto.
Qed.


Theorem progress `{good_merge}: 
forall G delta q_context M,
typecheck_session q_context M delta G ->
variable_closed_session M ->
(forall p P,  M p = Some P -> cguardedP P) ->
G = gtt_end \/ exists qs1 qs2 a M' pi, step (qs1, M) a (qs2, M') pi.
Proof.
  intros G delta q_context M Htyped Hclosed Hguard.
  destruct G as [|p q branches].
  - left; reflexivity.
  - right.
    destruct (typecheck_session_has_component_projection q_context M delta
      (gtt_send p q branches) p Htyped (pac_sendp p q branches))
      as [P [Tp [qcp [Tp_proj [Hp [HdeltaP [HtypeP [HprojP HsubP]]]]]]]].
    destruct (typecheck_session_has_component_projection q_context M delta
      (gtt_send p q branches) q Htyped (pac_sendq p q branches))
      as [Q [Tq [qcq [Tq_proj [Hq [HdeltaQ [HtypeQ [HprojQ HsubQ]]]]]]]].
    pose proof (Hguard p P Hp) as HguardP.
    pose proof (Hguard q Q Hq) as HguardQ.
    pose proof (Hclosed p P Hp) as HclosedP.
    pose proof (Hclosed q Q Hq) as HclosedQ.
    destruct (cguardedP_unfolds P HguardP)
      as [HguardPu [HpreP HshapeP]].
    destruct (cguardedP_unfolds Q HguardQ)
      as [HguardQu [HpreQ HshapeQ]].
    destruct (typecheck_process_has_head (nil, nil, qcp) P Tp HtypeP)
      as [hP HheadP].
    destruct (typecheck_process_has_head (nil, nil, qcq) Q Tq HtypeQ)
      as [hQ HheadQ].
    assert (HnotvarP : forall k, hP <> ph_var k).
    {
      exact (process_head_type_guarded_not_var P hP Tp nil HheadP
        (proj2 HguardP) (Forall_nil _)).
    }
    assert (HnotvarQ : forall k, hQ <> ph_var k).
    {
      exact (process_head_type_guarded_not_var Q hQ Tq nil HheadQ
        (proj2 HguardQ) (Forall_nil _)).
    }
    assert (HheadPu : process_head_type (unravelP P) hP Tp).
    { eapply process_head_type_unravel; eauto. }
    assert (HheadQu : process_head_type (unravelP Q) hQ Tq).
    { eapply process_head_type_unravel; eauto. }
    pose proof (process_head_type_unravel_view P hP Tp HheadP HguardP)
      as HrootP.
    pose proof (process_head_type_unravel_view Q hQ Tq HheadQ HguardQ)
      as HrootQ.
    pose proof (process_head_type_closed_view P hP Tp HheadP HclosedP)
      as HviewP.
    pose proof (process_head_type_closed_view Q hQ Tq HheadQ HclosedQ)
      as HviewQ.
    destruct (projC_send_root_shape p q branches Tp_proj HprojP)
      as [fp HprojTypeP].
    rewrite HprojTypeP in HsubP.
    destruct (subtypeC_right_send_inv Tp q fp HsubP)
      as [fP HTp].
    subst Tp.
    destruct (projC_recv_root_shape p q branches Tq_proj HprojQ)
      as [fq HprojTypeQ].
    rewrite HprojTypeQ in HsubQ.
    destruct (subtypeC_right_recv_inv Tq p fq HsubQ)
      as [fQ HTq].
    subst Tq.
    (* Continue by the exposed root of the sender; the receiver either steps
       internally or accepts the selected communication branch. *)
    destruct HshapeP as [HendP | [HiteP | [HsendP | [HrecvP
      | [HnewP | [HunitP | HmeasureP]]]]]].
    + destruct HendP as [lz HrootEnd].
      pose proof HrootP as HrootP'.
      rewrite HrootEnd in HrootP'; simpl in HrootP'; inversion HrootP'; subst hP.
      rewrite HrootEnd in HheadPu.
      pose proof (process_head_type_end_info lz (ltt_send q fP) HheadPu) as Hbad.
      discriminate.
    + destruct HiteP as [e [P1 [P0 HrootIte]]].
      pose proof HrootP as HrootP'.
      rewrite HrootIte in HrootP'; simpl in HrootP'; inversion HrootP'; subst hP.
      destruct (progress_internal_transition M p P (ph_ite e)
        (ltt_send q fP) Hp HguardP HclosedP HheadPu HviewP HrootP
        ltac:(simpl; constructor))
        as [qs1 [qs2 [M' [pi Hstep]]]].
      exists qs1, qs2, (Tau p), M', pi; exact Hstep.
    + destruct HsendP as [sp [l [e [P' HrootSend]]]].
      pose proof HrootP as HrootP'.
      rewrite HrootSend in HrootP'; simpl in HrootP'; inversion HrootP'; subst hP.
      rewrite HrootSend in HheadPu.
      destruct (process_head_type_send_info sp l e P'
        (ltt_send q fP) HheadPu)
        as [expr_context [B [fsend [Tcont [Hexpression [HsendType HsendBranch]]]]]].
      inversion HsendType; subst fsend sp.
      rewrite HprojTypeP in HprojP.
      destruct (subtypeC_send_branch q fP fp l B Tcont HsubP HsendBranch)
        as [TprojCont [HprojectedBranch HsubCont]].
      destruct (projC_send_root_branch p q branches fp l B TprojCont
        HprojP HprojectedBranch) as [Hpq [Gcont HglobalBranch]].
      rewrite HprojTypeQ in HprojQ.
      destruct HshapeQ as [HendQ | [HiteQ | [HsendQ | [HrecvQ
        | [HnewQ | [HunitQ | HmeasureQ]]]]]].
      * destruct HendQ as [lz HrootEndQ].
        pose proof HrootQ as HrootQ'.
        rewrite HrootEndQ in HrootQ'; simpl in HrootQ'; inversion HrootQ'; subst hQ.
        rewrite HrootEndQ in HheadQu.
        pose proof (process_head_type_end_info lz (ltt_recv p fQ) HheadQu) as Hbad.
        discriminate.
      * destruct HiteQ as [e0 [Q1 [Q0 HrootIteQ]]].
        pose proof HrootQ as HrootQ'.
        rewrite HrootIteQ in HrootQ'; simpl in HrootQ'; inversion HrootQ'; subst hQ.
        destruct (progress_internal_transition M q Q (ph_ite e0)
          (ltt_recv p fQ) Hq HguardQ HclosedQ HheadQu HviewQ HrootQ
          ltac:(simpl; constructor)) as [qs1 [qs2 [M' [pi Hstep]]]].
        exists qs1, qs2, (Tau q), M', pi; exact Hstep.
      * destruct HsendQ as [spQ [lQ [eQ [Q' HrootSendQ]]]].
        pose proof HrootQ as HrootQ'.
        rewrite HrootSendQ in HrootQ'; simpl in HrootQ'; inversion HrootQ'; subst hQ.
        rewrite HrootSendQ in HheadQu.
        destruct (process_head_type_send_info spQ lQ eQ Q'
          (ltt_recv p fQ) HheadQu)
          as [ctxQ [BQ [fsendQ [TcontQ [HexprQ [HsendTypeQ HbranchQ]]]]]].
        inversion HsendTypeQ.
      * destruct HrecvQ as [spQ [lQ HrootRecvQ]].
        pose proof HrootQ as HrootQ'.
        rewrite HrootRecvQ in HrootQ'; simpl in HrootQ'; inversion HrootQ'; subst hQ.
        rewrite HrootRecvQ in HheadQu.
        destruct (process_head_type_recv_info spQ lQ (ltt_recv p fQ) HheadQu)
          as [frecv [HrecvType HrecvCovered]].
        inversion HrecvType; subst frecv spQ.
        destruct (projC_recv_root_local_branch p q branches fq l B Gcont
          HprojQ HglobalBranch) as [TrecvProj HrecvProjBranch].
        destruct (subtypeC_recv_branch p fQ fq l B TrecvProj HsubQ
          HrecvProjBranch) as [Trecv [HrecvBranch HsubRecv]].
        destruct (onth l lQ) as [Qbranch|] eqn:HbranchProcess.
        -- assert (Hcovered : onth l lQ <> None).
           { eapply HrecvCovered; exact HrecvBranch. }
           assert (Hsendpre : precongP P (p_send q l e P')).
           { rewrite <- HrootSend; exact HpreP. }
           assert (Hrecvpre : precongP Q (p_recv p lQ)).
           { rewrite <- HrootRecvQ; exact HpreQ. }
           destruct (closed_expression_evaluates expr_context e B
             Hexpression HviewP) as [v [Hevaluate Hsort]].
           destruct B as [| |].
           ++ destruct v as [n|b|qv].
              ** inversion Hsort; subst.
                 set (Qafter := subst_expression_in_process 0 0
                   (Val (Primitives.Nat n)) Qbranch).
                 set (Sbase := insert (KEQ:=participant_dec)
                   (insert (KEQ:=participant_dec) M q (p_recv p lQ)) p
                   (p_send q l e P')).
                 set (Safter := insert (KEQ:=participant_dec)
                   (insert (KEQ:=participant_dec) Sbase q Qafter) p P').
                 assert (Hinner : step (empty_quantum_state, Sbase)
                   (Transmit p q l (Primitives.Nat n))
                   (empty_quantum_state, Safter) 1%R).
                 {
                   unfold Sbase, Safter, Qafter.
                   eapply Comm_C with (p := p) (q := q) (l := l)
                     (e := e) (P := P') (lQ := lQ) (Q := Qbranch)
                     (v := Primitives.Nat n) (s1 := Sbase)
                     (q_state := empty_quantum_state).
                   - exact l.
                   - unfold Sbase; rewrite insert_eq; reflexivity.
                   - unfold Sbase; rewrite insert_neq by congruence.
                     rewrite insert_eq; reflexivity.
                   all: try (intros; discriminate).
                   all: eauto.
                 }
                 exists empty_quantum_state, empty_quantum_state,
                   (Transmit p q l (Primitives.Nat n)), Safter, 1%R.
                 exact (step_after_unfold_two M p q P Q
                   (p_send q l e P') (p_recv p lQ) P' Qafter
                   empty_quantum_state empty_quantum_state
                   (Transmit p q l (Primitives.Nat n)) 1%R
                   Hpq Hp Hq Hsendpre Hrecvpre Hinner).
              ** inversion Hsort.
              ** inversion Hsort.
           ++ destruct v as [n|b|qv].
              ** inversion Hsort.
              ** inversion Hsort; subst.
                 set (Qafter := subst_expression_in_process 0 0
                   (Val (Primitives.Bool b)) Qbranch).
                 set (Sbase := insert (KEQ:=participant_dec)
                   (insert (KEQ:=participant_dec) M q (p_recv p lQ)) p
                   (p_send q l e P')).
                 set (Safter := insert (KEQ:=participant_dec)
                   (insert (KEQ:=participant_dec) Sbase q Qafter) p P').
                 assert (Hinner : step (empty_quantum_state, Sbase)
                   (Transmit p q l (Primitives.Bool b))
                   (empty_quantum_state, Safter) 1%R).
                 {
                   unfold Sbase, Safter, Qafter.
                   eapply Comm_C with (p := p) (q := q) (l := l)
                     (e := e) (P := P') (lQ := lQ) (Q := Qbranch)
                     (v := Primitives.Bool b) (s1 := Sbase)
                     (q_state := empty_quantum_state).
                   - exact l.
                   - unfold Sbase; rewrite insert_eq; reflexivity.
                   - unfold Sbase; rewrite insert_neq by congruence.
                     rewrite insert_eq; reflexivity.
                   all: try (intros; discriminate).
                   all: eauto.
                 }
                 exists empty_quantum_state, empty_quantum_state,
                   (Transmit p q l (Primitives.Bool b)), Safter, 1%R.
                 exact (step_after_unfold_two M p q P Q
                   (p_send q l e P') (p_recv p lQ) P' Qafter
                   empty_quantum_state empty_quantum_state
                   (Transmit p q l (Primitives.Bool b)) 1%R
                   Hpq Hp Hq Hsendpre Hrecvpre Hinner).
              ** inversion Hsort.
           ++ destruct v as [n|b|qv].
              ** inversion Hsort.
              ** inversion Hsort.
              ** inversion Hsort; subst.
                 assert (Hnd : NoDup [qv]).
                 { constructor; [simpl; tauto | constructor]. }
                 pose (zst := zero_state_for_qubits p [qv] Hnd).
                 pose (qs1 := proj1_sig zst).
                 destruct (zero_state_for_qubits_owner_lookup p [qv] Hnd qv
                   (or_introl eq_refl)) as [n Hlookup].
                 set (qs2 := transfer_qubit_from_lookup
                   (quantum_map_of qs1) (proj2_sig (projT1 qs1))
                   (proj1_sig (projT2 qs1)) (proj2_sig (projT2 qs1))
                   q qv p n Hlookup).
                 set (Qafter := subst_expression_in_process 0 0
                   (Val (Primitives.QVal qv)) Qbranch).
                 set (Sbase := insert (KEQ:=participant_dec)
                   (insert (KEQ:=participant_dec) M q (p_recv p lQ)) p
                   (p_send q l e P')).
                 set (Safter := insert (KEQ:=participant_dec)
                   (insert (KEQ:=participant_dec) Sbase q Qafter) p P').
                 assert (Hinner : step (qs1, Sbase)
                   (Transmit p q l (Primitives.QVal qv))
                   (qs2, Safter) 1%R).
                 {
                   unfold Sbase, Safter, Qafter, qs2.
                   eapply Comm_Q with (p := p) (q := q) (l := l)
                     (e := e) (P := P') (lQ := lQ) (Q := Qbranch)
                     (v := qv) (s1 := Sbase) (q_state := qs1)
                     (q_state' := transfer_qubit_from_lookup
                       (quantum_map_of qs1) (proj2_sig (projT1 qs1))
                       (proj1_sig (projT2 qs1)) (proj2_sig (projT2 qs1))
                       q qv p n Hlookup)
                     (n := n) (Hlookup := Hlookup).
                   - exact l.
                   - unfold Sbase; rewrite insert_eq; reflexivity.
                   - unfold Sbase; rewrite insert_neq by congruence.
                     rewrite insert_eq; reflexivity.
                   all: eauto.
                 }
                 exists qs1, qs2, (Transmit p q l (Primitives.QVal qv)),
                   Safter, 1%R.
                 exact (step_after_unfold_two M p q P Q
                   (p_send q l e P') (p_recv p lQ) P' Qafter
                   qs1 qs2 (Transmit p q l (Primitives.QVal qv)) 1%R
                   Hpq Hp Hq Hsendpre Hrecvpre Hinner).
        -- exfalso.
           apply (HrecvCovered l B Trecv HrecvBranch).
           exact HbranchProcess.
      * destruct HnewQ as [Q' HrootNewQ].
        pose proof HrootQ as HrootQ'.
        rewrite HrootNewQ in HrootQ'; simpl in HrootQ'; inversion HrootQ'; subst hQ.
        destruct (progress_internal_transition M q Q ph_newq
          (ltt_recv p fQ) Hq HguardQ HclosedQ HheadQu HviewQ HrootQ
          ltac:(simpl; constructor)) as [qs1 [qs2 [M' [pi Hstep]]]].
        exists qs1, qs2, (Tau q), M', pi; exact Hstep.
      * destruct HunitQ as [n [U [lz [Q' HrootUnitQ]]]].
        pose proof HrootQ as HrootQ'.
        rewrite HrootUnitQ in HrootQ'; simpl in HrootQ'; inversion HrootQ'; subst hQ.
        destruct (progress_internal_transition M q Q (ph_unitary n U lz)
          (ltt_recv p fQ) Hq HguardQ HclosedQ HheadQu HviewQ HrootQ
          ltac:(simpl; constructor)) as [qs1 [qs2 [M' [pi Hstep]]]].
        exists qs1, qs2, (Tau q), M', pi; exact Hstep.
      * destruct HmeasureQ as [z [Q' HrootMeasureQ]].
        pose proof HrootQ as HrootQ'.
        rewrite HrootMeasureQ in HrootQ'; simpl in HrootQ'; inversion HrootQ'; subst hQ.
        destruct (progress_internal_transition M q Q (ph_measure z)
          (ltt_recv p fQ) Hq HguardQ HclosedQ HheadQu HviewQ HrootQ
          ltac:(simpl; constructor)) as [qs1 [qs2 [M' [pi Hstep]]]].
        exists qs1, qs2, (Tau q), M', pi; exact Hstep.
    + destruct HrecvP as [sp [cont HrootRecv]].
      pose proof HrootP as HrootP'.
      rewrite HrootRecv in HrootP'; simpl in HrootP'; inversion HrootP'; subst hP.
      rewrite HrootRecv in HheadPu.
      destruct (process_head_type_recv_info sp cont (ltt_send q fP) HheadPu)
        as [f0 [HrecvType _]].
      discriminate.
    + destruct HnewP as [P' HrootNew].
      pose proof HrootP as HrootP'.
      rewrite HrootNew in HrootP'; simpl in HrootP'; inversion HrootP'; subst hP.
      destruct (progress_internal_transition M p P ph_newq
        (ltt_send q fP) Hp HguardP HclosedP HheadPu HviewP HrootP
        ltac:(simpl; constructor))
        as [qs1 [qs2 [M' [pi Hstep]]]].
      exists qs1, qs2, (Tau p), M', pi; exact Hstep.
    + destruct HunitP as [n [U [lz [P' HrootUnit]]]].
      pose proof HrootP as HrootP'.
      rewrite HrootUnit in HrootP'; simpl in HrootP'; inversion HrootP'; subst hP.
      destruct (progress_internal_transition M p P (ph_unitary n U lz)
        (ltt_send q fP) Hp HguardP HclosedP HheadPu HviewP HrootP
        ltac:(simpl; constructor))
        as [qs1 [qs2 [M' [pi Hstep]]]].
      exists qs1, qs2, (Tau p), M', pi; exact Hstep.
    + destruct HmeasureP as [z [P' HrootMeasure]].
      pose proof HrootP as HrootP'.
      rewrite HrootMeasure in HrootP'; simpl in HrootP'; inversion HrootP'; subst hP.
      destruct (progress_internal_transition M p P (ph_measure z)
        (ltt_send q fP) Hp HguardP HclosedP HheadPu HviewP HrootP
        ltac:(simpl; constructor))
        as [qs1 [qs2 [M' [pi Hstep]]]].
      exists qs1, qs2, (Tau p), M', pi; exact Hstep.
Qed.

Lemma subtypeC_to_end_inv : forall T,
  subtypeC T ltt_end -> T = ltt_end.
Proof.
  intros T Hsub.
  destruct T as [|p f|p f]; [reflexivity| |].
  - exfalso; pinversion Hsub; try apply sub_mon.
  - exfalso; pinversion Hsub; try apply sub_mon.
Qed.

Lemma projectionC_end_inv `{good_merge} : forall p T,
  projC gtt_end p T -> T = ltt_end.
Proof.
  intros p T Hproj.
  unfold projectionC in Hproj.
  pinversion Hproj; try apply proj_mon.
  reflexivity.
Qed.

Lemma typecheck_session_component_lookup `{good_merge} :
  forall context M delta G p P,
    typecheck_session context M delta G ->
    M p = Some P ->
    exists T qc,
      delta p = Some T /\ typecheck_process (nil, nil, qc) P T.
Proof.
  intros context M delta G p P Hsession HM.
  unfold typecheck_session in Hsession.
  destruct Hsession as [lqc [Hreg [Hbalanced [Hassoc [Hpartition
    [Hlength [Hperm Htyped]]]]]]].
  assert (HinM : In p (session_participants M)).
  {
    unfold session_participants.
    apply in_map_iff.
    exists (p, P); split; [reflexivity|].
    apply (proj2 (specs _ _ M) p P); exact HM.
  }
  assert (HinDeltaParts : In p (map fst (elems participant ltt delta))).
  {
    eapply Permutation_in; [apply Permutation_sym; exact Hperm|exact HinM].
  }
  apply in_map_iff in HinDeltaParts.
  destruct HinDeltaParts as [[p' T] [Hp HinDelta]].
  simpl in Hp; subst p'.
  assert (Hdelta : delta p = Some T).
  { apply (proj2 (specs _ _ delta) p T); exact HinDelta. }
  assert (Hlength_le : Datatypes.length (elems participant ltt delta) <= Datatypes.length lqc).
  { rewrite <- Hlength; lia. }
  destruct (in_combine_ex_r (elems participant ltt delta) lqc
    Hlength_le (p, T) HinDelta) as [qc Htriple].
  destruct (Htyped p T qc Htriple) as [P' [HM' Hproc]].
  rewrite HM in HM'; inversion HM'; subst P'.
  exists T, qc; split; assumption.
Qed.

Lemma ended_component_progress : forall (M : session) (p : participant)
  (P : process) (context : process_context * variable_context)
  (qc : qubit_context) (T : ltt),
  M p = Some P ->
  typecheck_process (context, qc) P T ->
  subtypeC T ltt_end ->
  cguardedP P ->
  variable_closed_process_at 0 P ->
  (exists lz, precongP P (p_end lz)) \/
  exists qs1 qs2 M' pi, step (qs1, M) (Tau p) (qs2, M') pi.
Proof.
  intros M p P context qc T HM Htyped Hsub Hguard Hclosed.
  destruct (typecheck_process_has_head (context, qc) P T Htyped)
    as [h Hhead].
  assert (Hnonvar : forall k, h <> ph_var k).
  {
    exact (process_head_type_guarded_not_var P h T nil Hhead
      (proj2 Hguard) (Forall_nil _)).
  }
  assert (HheadU : process_head_type (unravelP P) h T).
  { eapply process_head_type_unravel; eauto. }
  assert (Hroot : process_root_view (unravelP P) = Some h).
  { eapply process_head_type_unravel_view; eauto. }
  pose proof (process_head_type_closed_view P h T Hhead Hclosed) as Hview.
  destruct (cguardedP_unfolds P Hguard) as [_ [Hpre Hshape]].
  destruct Hshape as
    [Hend | [Hite | [Hsend | [Hrecv | [Hnew | [Hunit | Hmeasure]]]]]].
  - destruct Hend as [lz Hend].
    rewrite Hend in Hroot; simpl in Hroot; inversion Hroot; subst h.
    left; exists lz; rewrite Hend in Hpre; exact Hpre.
  - destruct Hite as [e [P1 [P0 Hite]]].
    rewrite Hite in Hroot; simpl in Hroot; inversion Hroot; subst h.
    assert (HrootU : process_root_view (unravelP P) = Some (ph_ite e)).
    { rewrite Hite; reflexivity. }
    destruct (progress_internal_transition M p P (ph_ite e) T HM Hguard
      Hclosed HheadU Hview HrootU ltac:(simpl; constructor))
      as [qs1 [qs2 [M' [pi Hstep]]]].
    right; exists qs1, qs2, M', pi; exact Hstep.
  - destruct Hsend as [q [l [e [Q Hsend]]]].
    rewrite Hsend in Hroot; simpl in Hroot; inversion Hroot; subst h.
    rewrite Hsend in HheadU; simpl in HheadU.
    destruct (process_head_type_send_info q l e Q T HheadU)
      as [expr_context [B [f [Tcont [_ [HT _]]]]]].
    pose proof (subtypeC_to_end_inv T Hsub) as HendT.
    rewrite HT in HendT; discriminate.
  - destruct Hrecv as [q [cont Hrecv]].
    rewrite Hrecv in Hroot; simpl in Hroot; inversion Hroot; subst h.
    rewrite Hrecv in HheadU; simpl in HheadU.
    destruct (process_head_type_recv_info q cont T HheadU)
      as [f [HT _]].
    pose proof (subtypeC_to_end_inv T Hsub) as HendT.
    rewrite HT in HendT; discriminate.
  - destruct Hnew as [Q Hnew].
    rewrite Hnew in Hroot; simpl in Hroot; inversion Hroot; subst h.
    assert (HrootU : process_root_view (unravelP P) = Some ph_newq).
    { rewrite Hnew; reflexivity. }
    destruct (progress_internal_transition M p P ph_newq T HM Hguard
      Hclosed HheadU Hview HrootU ltac:(simpl; constructor))
      as [qs1 [qs2 [M' [pi Hstep]]]].
    right; exists qs1, qs2, M', pi; exact Hstep.
  - destruct Hunit as [n [U [lz [Q Hunit]]]].
    rewrite Hunit in Hroot; simpl in Hroot; inversion Hroot; subst h.
    assert (HrootU : process_root_view (unravelP P) =
      Some (ph_unitary n U lz)).
    { rewrite Hunit; reflexivity. }
    destruct (progress_internal_transition M p P (ph_unitary n U lz) T
      HM Hguard Hclosed HheadU Hview HrootU ltac:(simpl; constructor))
      as [qs1 [qs2 [M' [pi Hstep]]]].
    right; exists qs1, qs2, M', pi; exact Hstep.
  - destruct Hmeasure as [z [Q Hmeasure]].
    rewrite Hmeasure in Hroot; simpl in Hroot; inversion Hroot; subst h.
    assert (HrootU : process_root_view (unravelP P) =
      Some (ph_measure z)).
    { rewrite Hmeasure; reflexivity. }
    destruct (progress_internal_transition M p P (ph_measure z) T HM Hguard
      Hclosed HheadU Hview HrootU ltac:(simpl; constructor))
      as [qs1 [qs2 [M' [pi Hstep]]]].
    right; exists qs1, qs2, M', pi; exact Hstep.
Qed.

Lemma ended_session_component_progress `{good_merge} :
  forall context M delta p P,
    typecheck_session context M delta gtt_end ->
    variable_closed_session M ->
    (forall p P, M p = Some P -> cguardedP P) ->
    M p = Some P ->
    (exists lz, precongP P (p_end lz)) \/
    exists qs1 qs2 a M' pi, step (qs1, M) a (qs2, M') pi.
Proof.
  intros context M delta p P Htyped Hclosed Hguard HM.
  destruct (typecheck_session_component_lookup context M delta gtt_end
    p P Htyped HM) as [T [qc [Hdelta Hproc]]].
  unfold typecheck_session in Htyped.
  destruct Htyped as [lqc [_ [_ [Hassoc _]]]].
  destruct Hassoc as [_ HassocTypes].
  destruct (HassocTypes p T Hdelta) as [Tproj [Hproj Hsub]].
  pose proof (projectionC_end_inv p Tproj Hproj) as HTproj.
  rewrite HTproj in Hsub.
  destruct (ended_component_progress M p P (nil, nil) qc T HM Hproc
    Hsub (Hguard p P HM) (Hclosed p P HM)) as [HfinishedP | HstepP].
  - left; exact HfinishedP.
  - destruct HstepP as [qs1 [qs2 [M' [pi HstepP]]]].
    right; exists qs1, qs2, (Tau p), M', pi; exact HstepP.
Qed.

Lemma collect_ended_component_progress : forall (M : session) ps,
  (forall p, In p ps -> forall P, M p = Some P ->
    (exists lz, precongP P (p_end lz)) \/
    exists qs1 qs2 a M' pi, step (qs1, M) a (qs2, M') pi) ->
  Forall (fun p => forall P, M p = Some P ->
    exists lz, precongP P (p_end lz)) ps \/
  exists qs1 qs2 a M' pi, step (qs1, M) a (qs2, M') pi.
Proof.
  intros M ps Hlocal.
  revert Hlocal.
  induction ps as [|p ps IH]; intros Hlocal.
  - left; constructor.
  - destruct (M p) as [P|] eqn:HM.
    + destruct (Hlocal p (or_introl eq_refl) P HM)
        as [HfinishedP | HstepP].
      * assert (HlocalTail : forall p, In p ps -> forall P,
          M p = Some P ->
          (exists lz, precongP P (p_end lz)) \/
          exists qs1 qs2 a M' pi, step (qs1, M) a (qs2, M') pi).
        { intros p' Hin P' HM'; exact (Hlocal p' (or_intror Hin) P' HM'). }
        destruct (IH HlocalTail) as [Hall | HstepTail].
        -- left; apply Forall_cons.
           ++ intros P' HM'; rewrite HM in HM'; inversion HM'; subst P'; exact HfinishedP.
           ++ exact Hall.
        -- right; exact HstepTail.
      * right; exact HstepP.
    + assert (HlocalTail : forall p, In p ps -> forall P,
        M p = Some P ->
        (exists lz, precongP P (p_end lz)) \/
        exists qs1 qs2 a M' pi, step (qs1, M) a (qs2, M') pi).
      { intros p' Hin P' HM'; exact (Hlocal p' (or_intror Hin) P' HM'). }
      destruct (IH HlocalTail) as [Hall | HstepTail].
      * left; apply Forall_cons.
        -- intros P' HM'; rewrite HM in HM'; discriminate.
        -- exact Hall.
      * right; exact HstepTail.
Qed.

Theorem type_safety `{good_merge}:
forall G delta q_context M,
typecheck_session q_context M delta G ->
variable_closed_session M ->
(forall p P,  M p = Some P -> cguardedP P) ->
finished M \/ exists qs1 qs2 a M' pi, step (qs1, M) a (qs2, M') pi.
Proof.
  intros G delta q_context M Htyped Hclosed Hguard.
  destruct (progress G delta q_context M Htyped Hclosed Hguard)
    as [Hend | Hstep].
  - subst G.
    assert (Hlocal : forall p, In p (session_participants M) ->
      forall P, M p = Some P ->
      (exists lz, precongP P (p_end lz)) \/
      exists qs1 qs2 a M' pi, step (qs1, M) a (qs2, M') pi).
    {
      intros p Hin P HM.
      eapply ended_session_component_progress; eauto.
    }
    destruct (collect_ended_component_progress M (session_participants M)
      Hlocal) as [Hdone | HstepList].
    + left; unfold finished; intros p P HM.
      assert (Hin : In p (session_participants M)).
      {
        unfold session_participants; apply in_map_iff.
        exists (p, P); split; [reflexivity|].
        apply (proj2 (specs _ _ M) p P); exact HM.
      }
      rewrite Forall_forall in Hdone.
      exact (Hdone p Hin P HM).
    + right; exact HstepList.
  - right; exact Hstep.
Qed.
