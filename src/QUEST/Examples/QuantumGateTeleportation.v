From SQIR Require Import SQIR.
Require Import SST session.
Require Import Permutation Reals List String.
Require Import Automation FMap Primitives Process Typechecking  ExamplesHelpers.
From Paco Require Import paco.
Require Import balanced Lia.


Definition l_A_in := 0.
Definition l_a_in := 0.
Definition l_B_in := 0.
Definition l_b_in := 0.
Definition l_xa := 0.
Definition l_xb := 0.
Definition l_A_out := 0.
Definition l_B_out := 0.


(*control: x; target: y*)
Definition do_CZ (x y : expression) (cont: process) : process := 
U_H [.y::nil.]; 
(U_CNOT[.x::y::nil.]; 
(U_H [.y::nil.]; cont)).

Definition U_S := U_R 0 0 (PI/2).
Definition U_Sdag := U_R 0 0 (-PI/2).

Definition P_A : process :=
Env .& l_A_in .; 
(Source .& l_a_in .; 
(do_CZ (Var 1) (Var 0) (*CZ[qA, qa]*)
(U_H [.Var 0::nil.]; (*H[qa]*) 
(U_X [.Var 0::nil.]; (*X[qa]*) 
(p_measure (Var 0) (*xa = measure qa*)
(Bob .+ l_xa<.(Var 0).>; (*send xa*)
(Bob .& l_xb .; 
(IF (Op Beq (Var 0::Var 1::nil)) THEN (*xa == xb*)
  (U_Sdag [.Var 3::nil.]; (Env .+ l_A_out<.(Var 3).>; (p_end (nil))))
ELSE
  (U_S [.Var 3::nil.]; (Env .+ l_A_out<.(Var 3).>; (p_end (nil))))
)))))))).

Definition P_B : process :=
Env .& l_B_in .;
(Source .& l_b_in .;
(do_CZ (Var 1) (Var 0)
(U_Sdag [.Var 0::nil.];
(U_H [.Var 0::nil.];
(p_measure (Var 0)
(Alice .& l_xa .;
(Alice .+ l_xb<.Var 1.>; (
IF (Op Beq (Var 0::Var 1::nil)) THEN
  (U_S [.Var 3::nil.]; (Env .+ l_B_out<.Var 3.>; (p_end (nil))))
ELSE
  (U_Sdag [.Var 3::nil.]; (Env .+ l_B_out<.Var 3.>; (p_end (nil))))
)))))))).

Definition P_S : process :=
p_newq
(p_newq
(U_H [.Var 1::nil.];
(U_CNOT [.Var 1::Var 0::nil.];
(U_X [.Var 0::nil.];
(Alice .+ l_a_in<.Var 1.>;
(Bob .+ l_b_in<.Var 0.>;
(p_end nil))))))).


Definition P_E (qA qB: qubit_reference): process :=
Alice .+ l_A_in<.(Val (QVal qA)).>;
(Bob .+ l_B_in<.(Val (QVal qB)).>;
(Alice .& l_A_out .;
(Bob .& l_B_out .;
(p_end (Var 1::Var 0::nil))))).

Definition gate_teleportation qA qB :=
insert (insert (insert (insert empty_fmap Source P_S) Env (P_E qA qB)) Bob P_B) Alice P_A.


Definition gate_teleportation_global : global :=
Env --> Alice $ l_A_in(.Qubit.);
(Env --> Bob $ l_B_in(.Qubit.);
(Source --> Alice $ l_a_in(.Qubit.);
(Source --> Bob $ l_b_in(.Qubit.);
(Alice --> Bob $ l_xa(.header.Bool.);
(Bob --> Alice $ l_xb(.header.Bool.);
(Alice --> Env $ l_A_out(.Qubit.); 
(Bob --> Env $ l_B_out(.Qubit.); g_end))))))).


Definition gate_teleportation_global_coind : gtt :=
Env -c-> Alice $ l_A_in(.Qubit.);
(Env -c-> Bob $ l_B_in(.Qubit.);
(Source -c-> Alice $ l_a_in(.Qubit.);
(Source -c-> Bob $ l_b_in(.Qubit.);
(Alice -c-> Bob $ l_xa(.header.Bool.);
(Bob -c-> Alice $ l_xb(.header.Bool.);
(Alice -c-> Env $ l_A_out(.Qubit.); 
(Bob -c-> Env $ l_B_out(.Qubit.); gtt_end))))))).


Definition L_A : ltt := 
Env .&. l_A_in(.Qubit.);
(Source .&. l_a_in(.Qubit.);
(Bob .+. l_xa(.header.Bool.);
(Bob .&. l_xb(.header.Bool.); 
(Env .+. l_A_out(.Qubit.);ltt_end)))).

Definition L_B : ltt := 
Env .&. l_B_in(.Qubit.);
(Source .&. l_b_in(.Qubit.);
(Alice .&. l_xa(.header.Bool.); 
(Alice .+. l_xb(.header.Bool.);
(Env .+. l_B_out(.Qubit.);ltt_end)))).

Definition L_S : ltt := 
Alice .+. l_a_in(.Qubit.);
(Bob .+. l_b_in(.Qubit.);ltt_end).

Definition L_E : ltt := 
Alice .+. l_A_in(.Qubit.);
(Bob .+. l_B_in(.Qubit.);
(Alice .&. l_A_out(.Qubit.);
(Bob .&. l_B_out(.Qubit.);ltt_end))).

(* The global protocol has one branch at each communication. *)
Local Ltac gate_regular :=
  let rec syntax G :=
    lazymatch G with
    | gtt_end => constr:(g_end)
    | gtt_send ?p ?q ?f =>
        let branch := eval cbn in (f 0) in
        lazymatch branch with
        | Some (?B, ?G') =>
            let tail := syntax G' in
            constr:(g_send p q (extendSlis 0 (B, tail)))
        end
    end in
  match goal with
  | |- regGtt ?G => let witness := syntax G in exists witness; repeat gttTC_step
  end.

Local Ltac gate_parts :=
  let Hr := fresh "Hpart" in
  intro Hr; inversion Hr; clear Hr; subst; try solve [constructor];
  match goal with
  | H : (if Nat.eqb ?n 0 then _ else _) = Some _ |- _ =>
      destruct n; cbn in H; [inversion H; subst|discriminate];
      apply pacs_sendr; try assumption;
      intros [|n]; cbn; [right; do 2 eexists; split; [reflexivity|]
                        |left; reflexivity];
      match goal with H : isgPartsC _ _ |- _ => revert H; gate_parts end
  end.

Local Ltac gate_balanced :=
  match goal with
  | |- balancedG gtt_end =>
      unfold balancedG; intros w w' p q [Hw|Hw]; inversion Hw
  | |- balancedG (gtt_send _ _ _) =>
      apply balanced_up;
      [intros [|n]; cbn;
       [right; do 2 eexists; split; [reflexivity|gate_balanced]|left; reflexivity]
      |gate_regular
      |intro r; gate_parts]
  end.

Local Ltac gate_occurs :=
  first [apply pac_sendp | apply pac_sendq
        |eapply pac_sendr with (n := 0);
         [discriminate|discriminate|reflexivity|gate_occurs]].

Local Ltac gate_absent :=
  let Hr := fresh "Habsent" in intro Hr; inversion Hr; clear Hr; subst; try discriminate;
  match goal with
  | H : (if Nat.eqb ?n 0 then _ else _) = Some _ |- _ =>
      destruct n; cbn in H; [inversion H; subst;
       match goal with Hpart : isgPartsC _ _ |- _ => revert Hpart; gate_absent end|discriminate]
  end.

Local Ltac gate_projection :=
  let branch := ltac:(
    intros [|n]; cbn; [right|left; auto];
    do 3 eexists; repeat split; try reflexivity; left; gate_projection) in
  pfold;
  first [apply proj_out; [discriminate|constructor|branch]
        |apply proj_in; [discriminate|constructor|branch]
        |match goal with
         | |- projection _ _ _ ?r ?T =>
             eapply proj_cont with
               (f' := fun n => if Nat.eqb n 0 then Some T else None);
             [discriminate|discriminate|discriminate|gate_occurs|branch|
              match goal with H : forall T0, _ |- _ => eapply H end]
         end
        |apply proj_end; gate_absent].
    
Lemma gate_teleportation_global_coind_balanced :
balancedG gate_teleportation_global_coind.
Proof.
  unfold gate_teleportation_global_coind, l_A_in, l_B_in, l_a_in,
    l_b_in, l_xa, l_xb, l_A_out, l_B_out.
  gate_balanced.
Qed.

Lemma projection_exists_gate_teleportation_global_coind:
forall (pt : participant) (T : ltt),
insert
(insert (insert (insert empty_fmap Alice L_A) Bob L_B)
Source L_S) Env L_E pt = Some T->
exists T' : ltt,
@projC coind_full_merge gate_teleportation_global_coind pt T' /\
subtypeC T T'.
Proof.
  intros pt T Hlookup.
  assert (Hsingle : forall T0,
      @isMerge coind_full_merge
        (fun n => if Nat.eqb n 0 then Some T0 else None) T0).
  {
    intros T0.
    change (full_merge (fun n => if Nat.eqb n 0 then Some T0 else None) T0).
    unfold full_merge.
    exists (slist_x T0).
    split.
    - intros [|n]; reflexivity.
    - constructor.
  }
  destruct (participant_dec pt Env) as [Heq|Hne].
  - subst pt. rewrite insert_eq in Hlookup. inversion Hlookup; subst T.
    exists L_E. split.
    + unfold projC, projectionC.
      unfold gate_teleportation_global_coind, L_E,
        l_A_in, l_B_in, l_a_in, l_b_in, l_xa, l_xb, l_A_out, l_B_out.
      gate_projection.
    + apply stRefl.
  - rewrite insert_neq in Hlookup by congruence.
    destruct (participant_dec pt Source) as [Heq|HneSource].
    + subst pt. rewrite insert_eq in Hlookup. inversion Hlookup; subst T.
      exists L_S. split.
      * unfold projC, projectionC.
        unfold gate_teleportation_global_coind, L_S,
          l_A_in, l_B_in, l_a_in, l_b_in, l_xa, l_xb, l_A_out, l_B_out.
        gate_projection.
      * apply stRefl.
    + rewrite insert_neq in Hlookup by congruence.
      destruct (participant_dec pt Bob) as [Heq|HneBob].
      * subst pt. rewrite insert_eq in Hlookup. inversion Hlookup; subst T.
        exists L_B. split.
        -- unfold projC, projectionC.
           unfold gate_teleportation_global_coind, L_B,
             l_A_in, l_B_in, l_a_in, l_b_in, l_xa, l_xb, l_A_out, l_B_out.
           gate_projection.
        -- apply stRefl.
      * rewrite insert_neq in Hlookup by congruence.
        destruct (participant_dec pt Alice) as [Heq|HneAlice].
        -- subst pt. rewrite insert_eq in Hlookup. inversion Hlookup; subst T.
           exists L_A. split.
           ++ unfold projC, projectionC.
              unfold gate_teleportation_global_coind, L_A,
                l_A_in, l_B_in, l_a_in, l_b_in, l_xa, l_xb, l_A_out, l_B_out.
              gate_projection.
           ++ apply stRefl.
        -- rewrite insert_neq in Hlookup by congruence.
           simpl in Hlookup. discriminate.
Qed.


(* A singleton merge is needed for projections through unrelated actions.
   This existence property is not included in [good_merge]. *)
Lemma gate_teleportation_typechecks:
  forall qA qB, qA <> qB ->
  typecheck_session (H:= coind_full_merge) 
    (insert (KEQ := qr_dec)
      (insert (KEQ := qr_dec) empty_fmap qA tt) qB tt)
    (gate_teleportation qA qB)
    (insert (insert (insert (insert empty_fmap Alice L_A) Bob L_B)
      Source L_S) Env L_E)
    gate_teleportation_global_coind.
Proof.
    intros; unfold typecheck_session, gate_teleportation_global_coind.
    exists  (empty_fmap :: empty_fmap ::empty_fmap ::(insert (KEQ := qr_dec)
      (insert (KEQ := qr_dec) empty_fmap qA tt) qB tt)::nil).
    split.
    {
        exists gate_teleportation_global.
        repeat gttTC_step.
    }
    split.
    {
        apply gate_teleportation_global_coind_balanced.
    }
    split.
    {
        split.
        { 
        intros; inversionc H0;
        repeat (case_analysis; clean_natb; cleanup;
        match goal with
        | [H: context [isgPartsC]|- _] =>
        inversionc H
        end);
        try solve [eexists; 
        repeat (try apply insert_eq;rewrite insert_neq; try congruence); intros Hnot; inversion Hnot].
        }
        apply projection_exists_gate_teleportation_global_coind.
    }
    split.
    {
        unfold partition; simpl. split.
        - unfold covers. intros k v. split.
          + intro Hq. exists (insert (KEQ := qr_dec)
              (insert (KEQ := qr_dec) empty_fmap qA tt) qB tt).
            split; [simpl; right; right; right; left; reflexivity|exact Hq].
          + intros [m [Hin Hm]]. simpl in Hin.
            destruct Hin as [Hin|[Hin|[Hin|[Hin|Hin]]]].
            * subst m. unfold empty_fmap in Hm. simpl in Hm. discriminate.
            * subst m. unfold empty_fmap in Hm. simpl in Hm. discriminate.
            * subst m. unfold empty_fmap in Hm. simpl in Hm. discriminate.
            * subst m. exact Hm.
            * contradiction.
        - unfold pairwise_disjoint.
          intros i j m m' Hneq Hi Hj k.
          destruct i as [|[|[|[|i]]]].
          + simpl in Hi. inversion Hi; subst m.
            unfold empty_fmap; simpl. split.
            * intros Hnonempty. exfalso. apply Hnonempty. reflexivity.
            * intros _. reflexivity.
          + simpl in Hi. inversion Hi; subst m.
            unfold empty_fmap; simpl. split.
            * intros Hnonempty. exfalso. apply Hnonempty. reflexivity.
            * intros _. reflexivity.
          + simpl in Hi. inversion Hi; subst m.
            unfold empty_fmap; simpl. split.
            * intros Hnonempty. exfalso. apply Hnonempty. reflexivity.
            * intros _. reflexivity.
          + simpl in Hi. inversion Hi; subst m.
            destruct j as [|[|[|[|j]]]].
            * simpl in Hj. inversion Hj; subst m'.
              unfold empty_fmap; simpl. split.
              -- intros _. reflexivity.
              -- intros Hnonempty. exfalso. apply Hnonempty. reflexivity.
            * simpl in Hj. inversion Hj; subst m'.
              unfold empty_fmap; simpl. split.
              -- intros _. reflexivity.
              -- intros Hnonempty. exfalso. apply Hnonempty. reflexivity.
            * simpl in Hj. inversion Hj; subst m'.
              unfold empty_fmap; simpl. split.
              -- intros _. reflexivity.
              -- intros Hnonempty. exfalso. apply Hnonempty. reflexivity.
            * simpl in Hj. inversion Hj; subst m'. exfalso. apply Hneq. reflexivity.
            * simpl in Hj. rewrite nth_error_nil in Hj. discriminate.
          + simpl in Hi. rewrite nth_error_nil in Hi. discriminate.
    }
    repeat split.
    {
        cbv.
        eapply Permutation_cons_app
          with (l1 := Pt "Source" :: Pt "Env" :: Pt "Bob" :: nil)
               (l2 := nil).
        eapply Permutation_cons_app
          with (l1 := Pt "Source" :: Pt "Env" :: nil)
               (l2 := nil).
        apply Permutation_refl.
    }
    Opaque gate_teleportation.
    simpl; intros.
    repeat split_ors; cleanup.
    {
        exists P_A.
        eexists; repeat split.
  
        repeat (intros; match goal with
                | [H:context [in_variable_context] |- _ ] => 
                idtac
                | [|- _] =>
                constructor
                end); 
        unfold in_variable_context in *; simpl in *;
        repeat case_analysis; cleanup; eauto;
        try solve [intros HNot; inversion HNot; congruence] ; eauto;
        intros; repeat split_ors; cleanup;

        inversionc H0; 
        cbv in H1; cleanup;
        repeat case_analysis; cleanup.
    }
    {
        exists P_B.
        eexists; repeat split.

        repeat (intros; match goal with
                | [H:context [in_variable_context] |- _ ] => 
                idtac
                | [|- _] =>
                constructor
                end); 
        unfold in_variable_context in *; simpl in *;
        repeat case_analysis; cleanup; eauto;
        try solve [intros HNot; inversion HNot; congruence];
        eauto;
        intros; repeat split_ors; cleanup;

        inversionc H0; 
        cbv in H1; cleanup;
        repeat case_analysis; cleanup.
    }
    {
        exists P_S.
        eexists; repeat split.

        repeat (intros; match goal with
                | [H:context [in_variable_context] |- _ ] => 
                idtac
                | [|- _] =>
                constructor
                end); 
        unfold in_variable_context in *; simpl in *;
        repeat case_analysis; cleanup; eauto;
        try solve [intros HNot; inversion HNot; congruence]; eauto;
        intros; repeat split_ors; cleanup.

        inversionc H0; 
        cbv in H1; cleanup;
        repeat case_analysis; cleanup.
    }
    {
        exists (P_E qA qB).
        eexists; repeat split.

        repeat (intros; match goal with
                | [H:context [in_variable_context] |- _ ] => 
                idtac
                | [|- context [typecheck_process]] =>
                constructor
                | [|- context [typecheck_expression]] =>
                constructor
                end); 
        unfold in_variable_context in *; simpl in *;
        repeat case_analysis; cleanup; eauto;
        try solve [intros HNot; inversion HNot; congruence] ; eauto;
        intros; repeat split_ors; cleanup;

        cbv; repeat case_analysis; eauto;
        try solve [constructor; cbv; eauto].
        inversionc H0; 
        cbv in H1; cleanup;
        repeat case_analysis; cleanup; eauto.
        repeat constructor; cleanup; eauto.
        simpl;
        try solve [intros HNot; inversion HNot; congruence].
    }
Unshelve.
all: try solve [repeat constructor].
Qed.
