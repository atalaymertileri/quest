Require Import Coq.Program.Equality.
Require Import SST.
Require Import Lia Permutation.
Require Import ListUtils Automation FMap Primitives.
Require Import Process.
From Paco Require Import paco.

Definition variable_context := list (option sort).

Definition qubit_context := finite_map qubit_reference unit.

Definition process_context := list (option (ltt * qubit_context)).

Definition typechecking_context := (process_context * variable_context * qubit_context)%type.

Definition empty_context : typechecking_context := (nil, nil, empty_fmap).

Definition in_process_context (context: typechecking_context) (X: nat) T : Prop := nth X context.1.1 None = Some T.

Definition insert_into_process_context (context: typechecking_context) (TD:ltt * qubit_context):typechecking_context := (Some TD::context.1.1, context.1.2, context.2).

Definition in_variable_context (context: typechecking_context) (x: variable) (s: sort) : Prop := nth x context.1.2 None = Some s.

Definition insert_into_variable_context (context: typechecking_context) (s: sort) : typechecking_context := (context.1.1, Some s :: context.1.2, context.2).

Definition remove_from_variable_context (context: typechecking_context) (n: fin) : typechecking_context := (context.1.1, updn context.1.2 n None, context.2).

Definition in_qubit_context (context: typechecking_context) (y: qubit_reference) : Prop := context.2 y = Some tt.

Definition insert_into_qubit_context (context: typechecking_context) (y: qubit_reference): typechecking_context := (context.1, insert (KEQ:= qr_dec) context.2 y tt).

Definition remove_from_qubit_context (context: typechecking_context) (y: qubit_reference): typechecking_context := 
(context.1, delete (KEQ:= qr_dec) context.2 y).

Definition remove_measured_expression_from_context
    (context : typechecking_context) (e : expression) : typechecking_context :=
  match e with
  | Val (QVal q) => remove_from_qubit_context context q
  | Var x => remove_from_variable_context context x
  | _ => context
  end.

Inductive typecheck_expression : typechecking_context -> expression -> sort -> Prop :=
| TE_ValN: forall context n, 
typecheck_expression context (Val (Primitives.Nat n)) header.Nat

| TE_ValB: forall context b, 
typecheck_expression context (Val (Primitives.Bool b)) header.Bool

| TE_ValQ: forall context q, 
in_qubit_context context q ->
typecheck_expression context (Val (Primitives.QVal q)) header.Qubit

| TE_Var:  forall context x B, 
in_variable_context context x B ->
typecheck_expression context (Var x) B

(*Below is fine because nothing should have qubits in it*)
| TE_Op_Plus: forall context a b,
typecheck_expression context a header.Nat ->
typecheck_expression context b header.Nat ->
typecheck_expression context (Op Plus (a::b::nil)) header.Nat

| TE_Op_Minus: forall context a b,
typecheck_expression context a header.Nat ->
typecheck_expression context b header.Nat ->
typecheck_expression context (Op Minus (a::b::nil)) header.Nat

| TE_Op_Leq: forall context a b,
typecheck_expression context a header.Nat ->
typecheck_expression context b header.Nat ->
typecheck_expression context (Op Leq (a::b::nil)) header.Bool

| TE_Op_And: forall context a b,
typecheck_expression context a header.Bool ->
typecheck_expression context b header.Bool ->
typecheck_expression context (Op And (a:: b::nil)) header.Bool

| TE_Op_Or: forall context a b,
typecheck_expression context a header.Bool ->
typecheck_expression context b header.Bool ->
typecheck_expression context (Op Or (a:: b::nil)) header.Bool

| TE_Op_Beq: forall context a b,
typecheck_expression context a header.Bool ->
typecheck_expression context b header.Bool ->
typecheck_expression context (Op Beq (a:: b::nil)) header.Bool

| TE_Op_Not: forall context a,
typecheck_expression context a header.Bool ->
typecheck_expression context (Op Not (a::nil)) header.Bool.


Definition only_qubit_references_in_context (context: typechecking_context) :=
Forall (fun s => s <> Some Qubit) context.1.2.

Inductive typecheck_process : typechecking_context -> process -> ltt -> Prop :=
|T_qbit : forall context P T, 
typecheck_process (insert_into_variable_context context Qubit) P T -> 
typecheck_process context (p_newq P) T

|T_meas : forall context z P T, 
typecheck_expression context z Qubit->
typecheck_process
  (insert_into_variable_context
    (remove_measured_expression_from_context context z) header.Bool) P T ->
typecheck_process context (p_measure z P) T

|T_U : forall context n U lz P T, 
Datatypes.length lz = n ->
Forall (fun z => typecheck_expression context z Qubit) lz ->
NoDup lz ->
typecheck_process context P T ->
typecheck_process context (p_unitary n U lz P) T

|T_end : forall context lz,
(forall z, In z lz <-> typecheck_expression context z Qubit) ->
NoDup lz ->
typecheck_process context (p_end lz) ltt_end

|T_send : forall context p e P l B T,
typecheck_expression context e B ->
typecheck_process 
    (match B with
    | Qubit => 
        match e with
        | Var x => remove_from_variable_context context x
        | Val (QVal q) => remove_from_qubit_context context q 
        | _ => context
        end
    | _ => context
    end) P T -> 
typecheck_process context (p_send p l e P) (ltt_send p (fun n => if Nat.eqb n l then (Some (B,T)) else None))

|T_recv : forall context p lP lBT,
  SForall2 (fun P BT => typecheck_process (insert_into_variable_context context BT.1) P BT.2) lP lBT ->
  typecheck_process context (p_recv p lP) (ltt_recv p (fun n => onth n lBT))

|T_if : forall context e P1 P0 T,
typecheck_expression context e header.Bool ->
typecheck_process context P1 T -> 
typecheck_process context P0 T -> 
typecheck_process context (p_ite e P1 P0) T

|T_rec : forall context P T,
typecheck_process (insert_into_process_context context (T, context.2)) P T ->
only_qubit_references_in_context context ->
typecheck_process context (p_rec P) T

|T_var: forall context qcontext X T lz,
in_process_context context X (T, qcontext) ->
only_qubit_references_in_context context ->
equivalent qcontext context.2 ->
(forall z, In z lz <-> typecheck_expression context z Qubit) ->
NoDup lz ->
typecheck_process context (p_var X lz) T
 
|T_sub: forall context P T T',
typecheck_process context P T ->
subtypeC T T' ->
typecheck_process context P T'.


Program Definition typecheck_process_deep_ind := 
fun (P : typechecking_context -> process -> ltt -> Prop)
(f : forall (context : typechecking_context) (P0 : process) (T : ltt),
typecheck_process (insert_into_variable_context context Qubit) P0 T ->
P (insert_into_variable_context context Qubit) P0 T -> P context (p_newq P0) T)
(f0 : forall (context : typechecking_context) (z : expression) (P0 : process) (T : ltt),
typecheck_expression context z Qubit ->
typecheck_process
  (insert_into_variable_context
    (remove_measured_expression_from_context context z) header.Bool) P0 T ->
P (insert_into_variable_context
  (remove_measured_expression_from_context context z) header.Bool) P0 T ->
P context (p_measure z P0) T)
(f1 : forall (context : typechecking_context) (n : fin) (U : SQIR.base_Unitary n) (lz : list expression) (P0 : process)
(T : ltt),
Datatypes.length lz = n ->
Forall (fun z : expression => typecheck_expression context z Qubit) lz ->
NoDup lz -> typecheck_process context P0 T -> P context P0 T -> P context (p_unitary n U lz P0) T)
(f2 : forall (context : typechecking_context) (lz : list expression),
(forall z : expression, In z lz <-> typecheck_expression context z Qubit) -> NoDup lz ->
P context (p_end lz) ltt_end)
(f3 : forall (context : typechecking_context) (p : participant) (e : expression) (P0 : process) (l : fin) (B : sort)
(T : ltt),
typecheck_expression context e B ->
typecheck_process
match B with
| Qubit =>
match e with
| Val (QVal q) => remove_from_qubit_context context q
| Var x => remove_from_variable_context context x
| _ => context
end
| _ => context
end P0 T ->
P
match B with
| Qubit =>
match e with
| Val (QVal q) => remove_from_qubit_context context q
| Var x => remove_from_variable_context context x
| _ => context
end
| _ => context
end P0 T -> P context (p_send p l e P0) (ltt_send p (fun n : fin => if Nat.eqb n l then Some (B, T) else None)))
(f4 : forall (context : typechecking_context) (p : participant) (lP : slist process) (lBT : slist (sort * ltt)),
SForall2 (fun (P0 : process) (BT : sort * ltt) =>
typecheck_process (insert_into_variable_context context BT.1) P0 BT.2) lP lBT ->
SForall2 (fun (P0 : process) (BT : sort * ltt) =>
P (insert_into_variable_context context BT.1) P0 BT.2) lP lBT ->
P context (p_recv p lP) (ltt_recv p (fun n : fin => onth n lBT)))
(f5 : forall (context : typechecking_context) (e : expression) (P1 P0 : process) (T : ltt),
typecheck_expression context e header.Bool ->
typecheck_process context P1 T ->
P context P1 T -> typecheck_process context P0 T -> P context P0 T -> P context (p_ite e P1 P0) T)
(f6 : forall (context : typechecking_context) (P0 : process) (T : ltt),
typecheck_process (insert_into_process_context context (T, context.2)) P0 T ->
P (insert_into_process_context context (T, context.2)) P0 T ->
only_qubit_references_in_context context -> P context (p_rec P0) T)
(f7 : forall (context : typechecking_context) (qcontext : qubit_context) (X : fin) lz (T : ltt),
in_process_context context X (T, qcontext) ->
only_qubit_references_in_context context -> equivalent qcontext context.2 ->
(forall z, In z lz <-> typecheck_expression context z Qubit) ->
NoDup lz -> P context (p_var X lz) T)
(f8 : forall (context : typechecking_context) (P0 : process) (T T' : ltt),
typecheck_process context P0 T -> P context P0 T -> subtypeC T T' -> P context P0 T') =>
fix F (t : typechecking_context) (p : process) (l : ltt) (t0 : typecheck_process t p l) {struct t0} : P t p l :=
match t0 in (typecheck_process t1 p0 l0) return (P t1 p0 l0) with
| T_qbit context P0 T t1 => f context P0 T t1 (F (insert_into_variable_context context Qubit) P0 T t1)
| T_meas context z P0 T t1 t2 =>
    f0 context z P0 T t1 t2
      (F (insert_into_variable_context
        (remove_measured_expression_from_context context z) header.Bool) P0 T t2)
| T_U context n U lz P0 T Hlen f9 n0 t1 => f1 context n U lz P0 T Hlen f9 n0 t1 (F context P0 T t1)
| T_end context lz i n => f2 context lz i n
| T_send context p0 e P0 l0 B T t1 t2 =>
f3 context p0 e P0 l0 B T t1 t2
(F
match B with
| Qubit =>
match e with
| Val (QVal q) => remove_from_qubit_context context q
| Var x => remove_from_variable_context context x
| _ => context
end
| _ => context
end P0 T t2)
| T_recv context p0 lP lBT s => f4 context p0 lP lBT s _
| T_if context e P1 P0 T t1 t2 t3 => f5 context e P1 P0 T t1 t2 (F context P1 T t2) t3 (F context P0 T t3)
| T_rec context P0 T t1 o => f6 context P0 T t1 (F (insert_into_process_context context (T, context.2)) P0 T t1) o
| T_var context qcontext X T lz i o i0 i1 i2 => f7 context qcontext X lz T i o i0 i1 i2
| T_sub context P0 T T' t1 s => f8 context P0 T T' t1 (F context P0 T t1) s
end.
Next Obligation.
intuition congruence.
Defined.
Next Obligation.
intuition congruence.
Defined.
Next Obligation.
intuition congruence.
Defined.
Next Obligation.
intuition congruence.
Defined.
Next Obligation.
intuition congruence.
Defined.
Next Obligation.
intuition congruence.
Defined.
Next Obligation.
repeat case_analysis.
Defined.
Next Obligation.
repeat case_analysis.
Defined.
Next Obligation.
revert s.
apply SForall2_mono.
intros; eauto.
Defined.


Definition state_only_contains_qubits_in_context (qcontext: qubit_context) (qstate: quantum_state) :=
forall q, qcontext q = Some tt <-> (proj1_sig (projT1 qstate)) q <> None.


Lemma typecheck_process_p_end_post:
    forall T context lz,
    typecheck_process context (p_end lz) T ->
    subtypeC ltt_end T /\
    (forall z, In z lz <-> typecheck_expression context z Qubit) /\ NoDup lz.
Proof.
    intros.
    dependent induction H; eauto.
    split; eauto.
    apply stRefl.
    edestruct IHtypecheck_process; eauto.
    split; eauto.
    eapply stTrans; eauto.
Qed.

 Lemma typecheck_process_p_send_post:
    forall T p l e P context,
    typecheck_process context (p_send p l e P) T ->
    exists B T',
    subtypeC (ltt_send p (fun n => if Nat.eqb n l then Some (B, T') else None)) T /\
    typecheck_expression context e B /\
    typecheck_process
        match B with
        | Qubit =>
            match e with
            | Val (QVal q) => remove_from_qubit_context context q
            | Var x => remove_from_variable_context context x
            | _ => context
            end
        | _ => context
        end P T'.
Proof.
    intros.
    dependent induction H; eauto.
    do 2 eexists; split; eauto.
    apply stRefl.

    edestruct IHtypecheck_process; eauto.
    cleanup.
    do 2 eexists; split; eauto.
    eapply stTrans; eauto.
Qed.

Lemma typecheck_process_p_recv_post:
forall T context p lxP,
typecheck_process context (p_recv p lxP) T ->
exists lBT, 
subtypeC (ltt_recv p (fun n => onth n lBT)) T /\
SForall2 (fun P BT => typecheck_process (insert_into_variable_context context BT.1) P BT.2) lxP lBT.
Proof.
    intros.
    dependent induction H; eauto.
    eexists; split; eauto.
    apply stRefl.
    simpl.

    edestruct IHtypecheck_process; eauto.
    cleanup.
    eexists; split; eauto.
    eapply stTrans; eauto.
Qed.

Lemma typecheck_process_p_measure_post:
forall T context P z,
typecheck_process context (p_measure z P) T ->
typecheck_expression context z Qubit /\ 
typecheck_process
  (insert_into_variable_context
    (remove_measured_expression_from_context context z) header.Bool) P T.
Proof.
    intros.
    dependent induction H; eauto.
    edestruct IHtypecheck_process; eauto.
    split; eauto.
    econstructor; eauto.
Qed.

Lemma typecheck_process_p_newq_post:
forall T context P,
typecheck_process context (p_newq P) T ->
typecheck_process (insert_into_variable_context context Qubit) P T.
Proof.
    intros.
    dependent induction H; eauto.
    econstructor; eauto.
Qed.

Lemma typecheck_process_p_unitary_post:
forall T context P n U lz,
typecheck_process context (p_unitary n U lz P)  T ->
Datatypes.length lz = n /\
Forall (fun z => typecheck_expression context z Qubit) lz /\ NoDup lz /\ typecheck_process context P T.
Proof.
    intros.
    dependent induction H; eauto.
    edestruct IHtypecheck_process; eauto.
    cleanup.
    repeat split; eauto.
    econstructor; eauto.
Qed.

Lemma typecheck_process_p_ite_post:
forall T context P1 P0 e,
typecheck_process context (p_ite e P1 P0) T ->
typecheck_expression context e header.Bool /\ 
typecheck_process context P1 T /\ 
typecheck_process context P0 T.
Proof.
    intros.
    dependent induction H; eauto.
    edestruct IHtypecheck_process; eauto.
    split; eauto.
    cleanup;
    split;
    econstructor; eauto.
Qed.

Lemma typecheck_process_p_var_post:
forall T context X lz,
typecheck_process context (p_var X lz) T ->
exists T' qcontext,
in_process_context context X (T', qcontext) /\
only_qubit_references_in_context context /\
equivalent qcontext context.2 /\
(forall z, In z lz <-> typecheck_expression context z Qubit) /\
NoDup lz /\
subtypeC T' T.
Proof.
    intros.
    dependent induction H; eauto.
    do 2 eexists; split; eauto.
    split; eauto.
    split; eauto.
    split; eauto.
    split; eauto.
    apply stRefl.

    edestruct IHtypecheck_process; eauto.
    cleanup.
    do 2 eexists.
    split; eauto.
    split; eauto.
    split; eauto.
    split; eauto.
    split; eauto.
    eapply stTrans; eauto.
Qed.

Lemma typecheck_process_p_rec_post:
forall T context P,
typecheck_process context (p_rec P) T ->
exists T',
typecheck_process (insert_into_process_context context (T', context.2)) P T' /\ 
only_qubit_references_in_context context /\
subtypeC T' T.
Proof.
    intros.
    dependent induction H; eauto.
    eexists; split; eauto.
    split; eauto.
    apply stRefl.

    edestruct IHtypecheck_process; eauto.
    cleanup.
    eexists.
    split; eauto.
    split; eauto.
    eapply stTrans; eauto.
Qed.

Ltac invert_typecheck:= match goal with
| H: typecheck_process _ (p_end _) _ |- _ => 
eapply_fresh typecheck_process_p_end_post in H
| H: typecheck_process _ (p_send _ _ _ _) _ |- _ => 
eapply_fresh typecheck_process_p_send_post in H
| H: typecheck_process _ (p_recv _ _) _ |- _ => 
eapply_fresh typecheck_process_p_recv_post in H
| H: typecheck_process _ (p_unitary _ _ _ _) _ |- _ => 
eapply_fresh typecheck_process_p_unitary_post in H
| H: typecheck_process _ (p_measure _ _) _ |- _ => 
eapply_fresh typecheck_process_p_measure_post in H
| H: typecheck_process _ (p_newq _) _ |- _ => 
eapply_fresh typecheck_process_p_newq_post in H
| H: typecheck_process _ (p_ite _ _ _) _ |- _ => 
eapply_fresh typecheck_process_p_ite_post in H
| H: typecheck_process _ (p_rec _) _ |- _ => 
eapply_fresh typecheck_process_p_rec_post in H
| H: typecheck_process _ (p_var _ _) _ |- _ =>
eapply_fresh typecheck_process_p_var_post in H
end.


Lemma typecheck_expression_equivalent:
    forall e B theta1 theta2, 
    typecheck_expression theta1 e B
    ->
    theta1.1.2 = theta2.1.2 ->
    equivalent theta1.2 theta2.2 ->
    typecheck_expression theta2 e B.
Proof. 
    induction e using expression_deep_ind; simpl; intros; eauto;
    cleanup; eauto.
    inversion H; cleanup; try solve [econstructor; eauto].
    econstructor; apply H1; eauto.

    inversion H; cleanup;
    econstructor; eauto.
    unfold in_variable_context in *; cleanup; eauto.

    inversion H0; cleanup; try solve [econstructor; eauto].
Qed.

Lemma typecheck_process_equivalent:
    forall P T theta1 theta2, 
    typecheck_process theta1 P T
    ->
    theta1.1.2 = theta2.1.2 ->
    Forall2 (fun Tq1 Tq2 => (Tq1 = None /\ Tq2 = None) \/ (exists T' T'' qc1 qc2, Tq1 = Some (T', qc1) /\ Tq2 = Some (T'', qc2) /\ equivalent qc2 qc1 /\ subtypeC T'' T')) theta1.1.1 theta2.1.1 ->
    equivalent theta1.2 theta2.2 ->
    typecheck_process theta2 P T.
Proof. 
    induction P using process_deep_ind; simpl; intros; cleanup.
    {(*p_var*)
        invert_typecheck; cleanup; eauto.
        simpl in *; cleanup.
        eapply T_sub; eauto.

        unfold in_process_context in *; simpl in *; eauto.

        assert_fresh (n < length theta1.1.1). {
            destruct_fresh (Nat.ltb n (length theta1.1.1));
            clean_natb; eauto.
            rewrite <- nth_seln_eq, seln_oob in H3.
            congruence.
            lia.
        }
        eapply_fresh nth_error_nth' in HA.
        eapply_fresh Forall2_length in H1.
        setoid_rewrite Hx0 in HA.
        eapply_fresh nth_error_nth' in HA; eauto.
        eapply nth_error_combine_merge in Hx1; try apply Hx; eauto.
        apply nth_error_In in Hx1.
        eapply forall2_forall, Forall_forall in H1; eauto.
        simpl in *.
        rewrite H3 in H1.
        split_ors; cleanup; try congruence.
        eapply T_sub; eauto.

        econstructor.
        unfold in_process_context in *; simpl in *; eauto.

        unfold only_qubit_references_in_context in *; simpl in *; intros; eauto.
        setoid_rewrite <- H0; eauto.

        unfold equivalent, included in *; simpl in *;
        intuition; eauto.
        all: try assumption.
        all: match goal with
        | Hiff : forall z, In z ?lz <-> typecheck_expression ?ctx1 z Qubit
          |- forall z, In z ?lz <-> typecheck_expression ?ctx2 z Qubit =>
            intros z; split; intros Hz;
            [apply (proj1 (Hiff z)) in Hz | apply (proj2 (Hiff z))];
            eapply typecheck_expression_equivalent; eauto using equivalent_sym
        end.
    }
    {
        invert_typecheck; cleanup.
        econstructor; eauto.
        econstructor; eauto.
        
        unfold in_qubit_context in *; simpl in *; split; intros; intuition eauto.
        eapply H4 in H6; cleanup; eauto.
        eapply typecheck_expression_equivalent; eauto.
        eapply H4; cleanup; eauto.
        eapply typecheck_expression_equivalent; eauto.
        apply equivalent_sym; eauto.
    }
    {
        invert_typecheck; cleanup; eauto.
        econstructor; eauto.
        econstructor; eauto.
        eapply typecheck_expression_equivalent; eauto.
        unfold equivalent, included in *; cleanup; eauto.

        unfold
        remove_from_qubit_context,
        remove_from_variable_context in *; 
        repeat case_analysis;
        eapply IHP; eauto.
        simpl in *; cleanup; eauto.

        simpl; intros; intuition;
        repeat (case_analysis; 
        simpl in *; cleanup; eauto; try congruence).
        simpl; cleanup; eauto.
    }
    {
        invert_typecheck; cleanup; eauto.
        simpl in *; cleanup.
        econstructor; eauto.

        econstructor; eauto.
        eapply SForall2_forall in H5; cleanup.
        eapply (SForall2_forall _ _ _ llp).
        repeat split; eauto; intros.
        eapply_fresh H5 in H9; eauto; clear H5.

        eapply SForall_onth in H; eauto; cleanup.
        {
            unfold insert_into_variable_context,
            insert_into_variable_context,
            insert_into_qubit_context in *; repeat case_analysis; simpl in *;
            eapply H; clear H; eauto; simpl.
            cleanup; eauto.
        }
        eapply H6; eauto.
        eapply H6; eauto.
    }
    {
        invert_typecheck; cleanup.
        simpl in *; cleanup.
        econstructor; eauto.
        eapply typecheck_expression_equivalent; eauto.
    }
    {
        invert_typecheck; cleanup.
        simpl in *; cleanup.
        eapply T_sub; eauto.
        econstructor; eauto.

        eapply IHP; eauto.
        simpl in *.
        econstructor; eauto.
        right.
        do 4 eexists; 
        do 3 (split; eauto).
        apply equivalent_sym; exact H2.
        eapply stRefl.

        unfold only_qubit_references_in_context in *; eauto.
        cleanup; eauto.
    }
    {
        invert_typecheck; cleanup.
        simpl in *; cleanup.
        econstructor; eauto.

        unfold insert_into_variable_context in *; simpl in *; cleanup.

        eapply IHP; eauto; simpl.
    }
    {
        invert_typecheck; cleanup.
        simpl in *; cleanup.
        econstructor; eauto.
        
        eapply Forall_impl; eauto.
        simpl; eauto.
        intros; eapply typecheck_expression_equivalent; eauto. 
    }
    {
        invert_typecheck; cleanup.
        assert (Hvar :
          (insert_into_variable_context
            (remove_measured_expression_from_context theta1 z) header.Bool).1.2 =
          (insert_into_variable_context
            (remove_measured_expression_from_context theta2 z) header.Bool).1.2).
        {
          destruct z as [v|x|op args]; simpl in *.
          - destruct v; simpl in *; try (inversion H3).
            inversion H3; subst; simpl; rewrite H0; reflexivity.
          - inversion H3; subst; simpl.
            rewrite H0; reflexivity.
          - inversion H3.
        }
        assert (Hqc : equivalent
          (remove_measured_expression_from_context theta1 z).2
          (remove_measured_expression_from_context theta2 z).2).
        {
          destruct z as [v|x|op args]; simpl in *.
          - destruct v; simpl in *; try (inversion H3).
            inversion H3; subst.
            unfold equivalent, included in *.
            destruct H2 as [H21 H22].
            split; intros k value Hlookup.
            + destruct (qr_dec q k) as [Heq|Hneq].
              * subst k. rewrite delete_eq in Hlookup. discriminate.
              * rewrite delete_neq in Hlookup by exact Hneq.
                rewrite delete_neq by congruence. eauto.
            + destruct (qr_dec q k) as [Heq|Hneq].
              * subst k. rewrite delete_eq in Hlookup. discriminate.
              * rewrite delete_neq in Hlookup by exact Hneq.
                rewrite delete_neq by congruence. eauto.
          - exact H2.
          - inversion H3.
        }
        econstructor.
        - eapply typecheck_expression_equivalent; eauto.
        - eapply IHP.
          + exact H4.
          + exact Hvar.
          + destruct z as [v|x|op args]; simpl.
            * destruct v; simpl; exact H1.
            * exact H1.
            * exact H1.
          + exact Hqc.
    }
Qed.
