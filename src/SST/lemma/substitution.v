Require Import List String Coq.Arith.PeanoNat Coq.Arith.Arith Relations ZArith Datatypes Setoid Morphisms Coq.Logic.Decidable Coq.Program.Basics Coq.Init.Datatypes Lia.
Import ListNotations. 
Open Scope list_scope.
From Paco Require Import paco.
Require Import SST session.
Require Import QUEST Typechecking.

(* Substitution/weakening support lemmas for expression/process typing.
   These are technical tools reused throughout typing and reduction proofs. *)

Lemma slideTp : forall Q X tm Gtl Gtr T cvc qvc m k,
typecheck_process (Gtl ++ Gtr, cvc, qvc) (incr_free (length Gtl) k X m Q) T  -> 
typecheck_process (Gtl ++ [tm] ++ Gtr, cvc, qvc) (incr_free (length Gtl) k (S X) m Q) T.
Proof.
  induction Q using process_deep_ind; intros; try easy; 
  simpl in *; 
    invert_typecheck; cleanup; intros;
    try solve [
    econstructor; eauto;
    econstructor; eauto].
  - (* Variable case: inserting one binder in the middle context shifts
       indices to the right of the insertion point by one. *)
    destruct_fresh (Nat.leb (length Gtl) n); cleanup; intros.
    - assert (Hlist : forall z,
          In z (map (incr_free_expression k m) lz) <->
          typecheck_expression (Gtl ++ [tm] ++ Gtr, cvc, qvc) z Qubit).
      {
        intros z; specialize (H3 z); split; intros Hz.
        - apply H3 in Hz.
          eapply typecheck_expression_equivalent; [exact Hz|reflexivity|apply equivalent_refl].
        - apply H3.
          eapply typecheck_expression_equivalent with
            (theta1 := (Gtl ++ [tm] ++ Gtr, cvc, qvc))
            (theta2 := (Gtl ++ Gtr, cvc, qvc)); [exact Hz|reflexivity|apply equivalent_refl].
      }
      apply T_sub with (T := T'); [|exact H5].
      eapply T_var with (qcontext := qcontext).
      + unfold in_process_context in *; simpl in *.
        apply Nat.leb_le in HD.
        rewrite app_nth2; [|lia].
        rewrite app_nth2 in H0 by lia.
        replace (n + S X - length Gtl) with (S (n + X - length Gtl)) by lia.
        simpl; exact H0.
      + exact H1.
      + exact H2.
      + exact Hlist.
      + exact H4.

    - assert (Hlist : forall z,
          In z (map (incr_free_expression k m) lz) <->
          typecheck_expression (Gtl ++ [tm] ++ Gtr, cvc, qvc) z Qubit).
      {
        intros z; specialize (H3 z); split; intros Hz.
        - apply H3 in Hz.
          eapply typecheck_expression_equivalent; [exact Hz|reflexivity|apply equivalent_refl].
        - apply H3.
          eapply typecheck_expression_equivalent with
            (theta1 := (Gtl ++ [tm] ++ Gtr, cvc, qvc))
            (theta2 := (Gtl ++ Gtr, cvc, qvc)); [exact Hz|reflexivity|apply equivalent_refl].
      }
      apply T_sub with (T := T'); [|exact H5].
      eapply T_var with (qcontext := qcontext).
      + unfold in_process_context in *; simpl in *.
        apply Nat.leb_nle in HD.
        rewrite app_nth1; [|lia].
        rewrite app_nth1 in H0 by lia.
        exact H0.
      + exact H1.
      + exact H2.
      + exact Hlist.
      + exact H4.
  -(*end case*)
    econstructor; eauto.
    econstructor; eauto.
    intros.
    specialize (H1 z); simpl in *.
    split; intros.
    apply H1 in H3.
    eapply typecheck_expression_equivalent; eauto;
    simpl; eauto.
    apply equivalent_refl.
    apply H1.
    eapply typecheck_expression_equivalent; eauto;
    simpl; eauto.
    apply equivalent_refl.
  
  - (*send case*)
    econstructor; eauto.
    econstructor; eauto.
    eapply typecheck_expression_equivalent; eauto;
    simpl; eauto.
    apply equivalent_refl.
    
    unfold remove_from_qubit_context,
    remove_from_variable_context in *; simpl in *.
    repeat case_analysis; eauto.
  - (* Receive case: recurse under each branch with an extended sort context. *)
    simpl in *.
    econstructor; eauto.
    econstructor; eauto.
    clear H0 H1 T. 
    
    revert H2 H. revert X tm cvc qvc m k Gtl Gtr lBT.
    induction llp; intros.
    - inversionc H2. 
      inversionc H.
      constructor; try easy.
      unfold insert_into_variable_context,
      insert_into_variable_context,
      insert_into_qubit_context; simpl.
      destruct y.1; eauto.
    - inversion H; cleanup.
      - simpl in *. inversionc H2.
        specialize(IHllp X tm cvc qvc m k Gtl Gtr ys H7 H4).
        constructor; try easy.
        unfold insert_into_variable_context,
        insert_into_variable_context,
        insert_into_qubit_context; simpl.
        destruct y.1; eauto.
      - subst.
        simpl in *. inversionc H2.
        specialize(IHllp X tm cvc qvc m k Gtl Gtr ys H3 H1).
        constructor; try easy.
  - econstructor; eauto.
    eapply typecheck_expression_equivalent; eauto;
    simpl; eauto.
    apply equivalent_refl.

  - simpl in *. 
    specialize(IHQ X tm (Some (T', qvc) :: Gtl) Gtr T' cvc qvc m k); intros.
    simpl in *.
    apply T_sub with T'; try easy. constructor.
    apply IHQ; try easy.
    simpl in *; eauto.

  - simpl in *.
    econstructor; eauto.
    unfold insert_into_variable_context in *; simpl in *; eauto.

  - simpl in *.
    econstructor; eauto.
    unfold insert_into_variable_context in *; simpl in *; eauto.
    eapply Forall_impl; eauto.
    simpl; intros.
    eapply typecheck_expression_equivalent; eauto;
    simpl; eauto.
    apply equivalent_refl.

  - simpl in *.
    econstructor; eauto.
    eapply typecheck_expression_equivalent; eauto;
    simpl; eauto.
    apply equivalent_refl.
    destruct (incr_free_expression k m z) as [v|x|op args] eqn:Hz;
      simpl in *.
    + destruct v; simpl in *; try solve [inversion H0].
      inversion H0; subst.
      eapply IHQ with (Gtl := Gtl) (Gtr := Gtr)
        (cvc := Some header.Bool :: cvc)
        (qvc := delete (KEQ := qr_dec) qvc q).
      exact H1.
    + eapply IHQ with (Gtl := Gtl) (Gtr := Gtr)
        (cvc := Some header.Bool :: updn cvc x None) (qvc := qvc).
      exact H1.
    + inversion H0.
Qed.

(* Head-insertion specialization of `slideTp`. *)
Lemma slideT : forall Q X tm Gt cvc qvc T m,
typecheck_process (Gt, cvc, qvc) (incr_free 0 0 X m Q) T -> 
typecheck_process (tm::Gt, cvc, qvc) (incr_free 0 0 (S X) m Q) T.
Proof.
  intros.
  specialize(slideTp Q X tm [] Gt T cvc qvc m 0 H); intros. simpl in H0.
  apply H0; try easy.
Qed.

Lemma slideSp_e : forall e Gsl Gsr tm pvc qc B m,
  typecheck_expression (pvc, Gsl ++ Gsr, qc) (incr_free_expression (length Gsl) m e) B ->
  typecheck_expression (pvc, Gsl ++ tm :: Gsr, qc) (incr_free_expression (length Gsl) (S m) e) B.
Proof.
  induction e using expression_deep_ind;
  simpl; intros; eauto.
  inversionc H; try solve [econstructor; eauto].
  {  
    repeat case_analysis; clean_natb; eauto; try lia.
    inversionc H; econstructor; eauto.
    unfold in_variable_context in *; simpl in *.

    rewrite app_nth2; try lia.
    rewrite app_nth2 in H2; try lia.
    replace (x + S m - length Gsl)  with (S (x + m - length Gsl)) by lia; eauto.

    inversionc H; econstructor; eauto.
    unfold in_variable_context in *; simpl in *.
    rewrite app_nth1; try lia.
    rewrite app_nth1 in H2; try lia.
    eauto.
  }
  
  inversionc H0;
  repeat (destruct args; simpl in *; try congruence; cleanup);
  econstructor; eauto.
Qed.


Lemma incr_free_expression_succ : forall fv m e,
  incr_free_expression fv 1 (incr_free_expression fv m e) =
  incr_free_expression fv (S m) e.
Proof.
  induction e using expression_deep_ind; intros; simpl.
  - reflexivity.
  - destruct (Nat.leb fv x) eqn:Hcut.
    + apply Nat.leb_le in Hcut.
      assert (Hcut' : Nat.leb fv (x + m) = true) by (apply Nat.leb_le; lia).
      rewrite Hcut'.
      f_equal; lia.
    + apply Nat.leb_gt in Hcut.
      assert (Hcut' : Nat.leb fv x = false) by (apply Nat.leb_gt; lia).
      rewrite Hcut'.
      reflexivity.
  - f_equal.
    rewrite map_map.
    apply map_ext_in.
    intros e Hin.
    apply Forall_forall with (x := e) in H; [exact H|exact Hin].
Qed.

Lemma incr_free_expression_zero : forall fv e,
  incr_free_expression fv 0 e = e.
Proof.
  induction e using expression_deep_ind; intros; simpl.
  - reflexivity.
  - destruct (Nat.leb fv x); simpl; f_equal; lia.
  - f_equal.
    rewrite <- map_id.
    apply map_ext_in.
    intros e Hin.
    apply Forall_forall with (x := e) in H; [exact H|exact Hin].
Qed.

Lemma map_injective_from_forall : forall A B (f : A -> B) xs ys,
  Forall (fun x => forall y, f x = f y -> x = y) xs ->
  map f xs = map f ys -> xs = ys.
Proof.
  intros A B f xs.
  induction xs as [|x xs IH]; intros ys Hforall Hmap.
  - destruct ys; simpl in Hmap; [reflexivity|discriminate].
  - destruct ys as [|y ys]; simpl in Hmap; [discriminate|].
    inversion Hforall; subst.
    inversion Hmap; subst.
    f_equal.
    + apply H1; assumption.
    + eapply IH; eassumption.
Qed.

Lemma incr_free_expression_injective : forall fv m e e',
  incr_free_expression fv m e = incr_free_expression fv m e' -> e = e'.
Proof.
  intros fv m e.
  induction e using expression_deep_ind; intros e' Heq.
  - destruct e'; simpl in Heq; try discriminate.
    inversion Heq; reflexivity.
  - destruct e'; simpl in Heq; try discriminate.
    destruct (Nat.leb fv x) eqn:Hx;
      destruct (Nat.leb fv x0) eqn:Hx0; inversion Heq; f_equal;
      apply Nat.leb_le in Hx || apply Nat.leb_gt in Hx;
      apply Nat.leb_le in Hx0 || apply Nat.leb_gt in Hx0; lia.
  - destruct e' as [| |op' args']; simpl in Heq; try discriminate.
    inversion Heq; subst.
    f_equal.
    eapply map_injective_from_forall; eauto.
Qed.

Lemma NoDup_map_injective : forall A B (f : A -> B) xs,
  (forall x y, f x = f y -> x = y) ->
  NoDup xs -> NoDup (map f xs).
Proof.
  intros A B f xs Hf Hnd.
  induction Hnd; simpl; constructor.
  - intro Hin.
    apply in_map_iff in Hin as [y [Heq Hin]].
    apply Hf in Heq; subst y.
    contradiction.
  - exact IHHnd.
Qed.

Lemma slideSp_qubit_forward : forall e Gsl Gsr tm pvc qc,
  tm <> Some Qubit ->
  typecheck_expression (pvc, Gsl ++ Gsr, qc) e Qubit ->
  typecheck_expression (pvc, Gsl ++ tm :: Gsr, qc)
    (incr_free_expression (length Gsl) 1 e) Qubit.
Proof.
  intros e Gsl Gsr tm pvc qc Htm Htyped.
  rewrite <- (incr_free_expression_zero (length Gsl) e) in Htyped.
  pose proof (slideSp_e e Gsl Gsr tm pvc qc Qubit 0 Htyped) as Hshift.
  exact Hshift.
Qed.

Lemma slideSp_qubit_backward : forall e Gsl Gsr tm pvc qc,
  tm <> Some Qubit ->
  typecheck_expression (pvc, Gsl ++ tm :: Gsr, qc) e Qubit ->
  exists e', e = incr_free_expression (length Gsl) 1 e' /\
    typecheck_expression (pvc, Gsl ++ Gsr, qc) e' Qubit.
Proof.
  intros e Gsl Gsr tm pvc qc Htm Htyped.
  induction e using expression_deep_ind.
  - inversion Htyped; subst.
    exists (Val (Primitives.QVal q)); split; [reflexivity|].
    eapply TE_ValQ; exact H1.
  - inversion Htyped; subst.
    assert (Hlookup : in_variable_context
      (pvc, Gsl ++ tm :: Gsr, qc) x Qubit) by assumption.
    unfold in_variable_context in Hlookup.
    simpl in Hlookup.
    destruct (Nat.lt_ge_cases x (length Gsl)) as [Hlt|Hge].
    + exists (Var x); split.
      * assert (Hcut : Nat.leb (length Gsl) x = false) by
          (apply Nat.leb_gt; exact Hlt).
        simpl; rewrite Hcut; reflexivity.
      * eapply TE_Var. unfold in_variable_context; simpl.
        rewrite app_nth1 in Hlookup by lia.
        rewrite app_nth1 by lia.
        exact Hlookup.
    + destruct (Nat.eq_dec x (length Gsl)) as [Heq|Hne].
      * subst x.
        rewrite app_nth2 in Hlookup by lia.
        replace (length Gsl - length Gsl) with 0 in Hlookup by lia.
        simpl in Hlookup.
        exfalso; apply Htm; exact Hlookup.
      * assert (Hgt : length Gsl < x) by lia.
        exists (Var (x - 1)); split.
        -- assert (Hcut : Nat.leb (length Gsl) (x - 1) = true) by
             (apply Nat.leb_le; lia).
           simpl; rewrite Hcut; f_equal; lia.
        -- eapply TE_Var. unfold in_variable_context; simpl.
           rewrite app_nth2 by lia.
           rewrite app_nth2 in Hlookup by lia.
           replace (x - length Gsl) with (S (x - S (length Gsl))) in Hlookup by lia.
           simpl in Hlookup.
           replace (x - 1 - length Gsl) with (x - S (length Gsl)) by lia.
           exact Hlookup.
  - inversion Htyped.
  all: try congruence.
Qed.

Lemma slideSp_var_list : forall lz m Gsl Gsr tm pvc qc,
  tm <> Some Qubit ->
  (forall z, In z (map (incr_free_expression (length Gsl) m) lz) <->
    typecheck_expression (pvc, Gsl ++ Gsr, qc) z Qubit) ->
  NoDup (map (incr_free_expression (length Gsl) m) lz) ->
  (forall z, In z (map (incr_free_expression (length Gsl) (S m)) lz) <->
    typecheck_expression (pvc, Gsl ++ tm :: Gsr, qc) z Qubit) /\
  NoDup (map (incr_free_expression (length Gsl) (S m)) lz).
Proof.
  intros lz m Gsl Gsr tm pvc qc Htm Htyped Hnd.
  assert (Hmap : map (incr_free_expression (length Gsl) (S m)) lz =
      map (incr_free_expression (length Gsl) 1)
        (map (incr_free_expression (length Gsl) m) lz)).
  {
    rewrite map_map.
    apply map_ext.
    intros e.
    symmetry; apply incr_free_expression_succ.
  }
  split.
  - intros z; rewrite Hmap; split; intros Hz.
    + apply in_map_iff in Hz as [x [Hz Hx]].
      subst z.
      apply Htyped in Hx.
      eapply slideSp_qubit_forward; eauto.
    + destruct (slideSp_qubit_backward z Gsl Gsr tm pvc qc Htm Hz)
        as [x [Heqx Hx]].
      apply Htyped in Hx.
      apply in_map_iff.
      exists x; split; [symmetry; exact Heqx|exact Hx].
  - rewrite Hmap.
    eapply NoDup_map_injective.
    + intros x y Heq.
      eapply incr_free_expression_injective; exact Heq.
    + exact Hnd.
Qed.

Lemma slideSp : forall Q X m l T Gsl Gsr pvc qc tm,
typecheck_process (pvc, Gsl ++ Gsr, qc) (incr_free l (length Gsl) X m Q) T -> 
tm <> Some Qubit ->
typecheck_process (pvc, Gsl ++ tm :: Gsr, qc) (incr_free l (length Gsl) X (S m) Q) T.
Proof.
  intros Q X m l T Gsl Gsr pvc qc tm Htyped Htm_not_qubit.
  revert X m l T Gsl Gsr pvc qc tm Htyped Htm_not_qubit.
  induction Q using process_deep_ind; simpl; intros; 
  try invert_typecheck; cleanup; eauto.
  {(*p_var*)
    destruct (slideSp_var_list lz m Gsl Gsr tm pvc qc
      Htm_not_qubit H2 H3) as [Hlist Hnd].
    assert (Honly : only_qubit_references_in_context
      (pvc, Gsl ++ tm :: Gsr, qc)).
    {
      unfold only_qubit_references_in_context in *; simpl in *.
      apply List.Forall_app in H0 as [Hsl Hsr].
      apply List.Forall_app; split; [exact Hsl|].
      constructor; [exact Htm_not_qubit|exact Hsr].
    }
    case_analysis.
    all: eapply T_sub with (T := T');
      [ eapply T_var with (qcontext := qcontext)
          (lz := map (incr_free_expression (length Gsl) (S m)) lz);
        [exact H|exact Honly|exact H1|exact Hlist|exact Hnd]
      |exact H4].
  }
  {(*p_end*) 
    simpl in *. 
    eapply T_sub; eauto. 
    eapply T_end; simpl; eauto.
    {
      intros.
      destruct z; simpl; eauto.
      {
        specialize (H0 (Val v)); simpl in *.
        split; intros.

        apply in_map_iff in H2; simpl in *; cleanup.
        cleanup; destruct x; simpl in *; try congruence.
        inversionc H2.
        assert_fresh (In (Val v) (map (incr_free_expression (length Gsl) m) lz)).
        eapply in_map_iff; eexists; split; eauto.
        simpl; eauto.
        apply H0 in HA.
        inversionc HA; econstructor; eauto.
        
        assert_fresh (In (Val v) (map (incr_free_expression (length Gsl) m) lz)).
        apply H0; inversionc H2; econstructor; eauto.


        apply in_map_iff in HA; simpl in *.
        cleanup; destruct x; simpl in *; try congruence.
        inversionc H3.
        eapply in_map_iff; eexists; split; eauto.
        simpl; eauto.
      }
      {
          split; intros.
          apply in_map_iff in H2; simpl in *.
          cleanup; destruct x0; simpl in *; try congruence.
          case_analysis; clean_natb;
          inversionc H2.
          
          assert_fresh (In (Var (x0 + m)) (map (incr_free_expression (length Gsl) m) lz)).
          eapply in_map_iff; eexists; split; eauto.
          simpl; cleanup; eauto.
          case_analysis; clean_natb; eauto; lia.
          apply H0 in HA.
          inversionc HA; econstructor; eauto.
          unfold in_variable_context in *; simpl in *.
          rewrite app_nth2; try lia.
          rewrite app_nth2 in H5; try lia.
          replace (x0 + S m - length Gsl)  with (S (x0 + m - length Gsl)) by lia; eauto.

          assert_fresh (In (Var x) (map (incr_free_expression (length Gsl) m) lz)).
          eapply in_map_iff; eexists; split; eauto.
          simpl; cleanup; eauto.
          case_analysis; clean_natb; eauto; lia.
          apply H0 in HA.
          inversionc HA; econstructor; eauto.
          unfold in_variable_context in *; simpl in *.
          rewrite app_nth1; try lia.
          rewrite app_nth1 in H5; try lia.
          eauto.
        
          inversionc H2.
          unfold in_variable_context in *; simpl in *.
          destruct (lt_dec x (length Gsl)) as [Hlt | Hnlt].
          {
            assert_fresh (typecheck_expression
              (pvc, Gsl ++ Gsr, qc) (Var x) Qubit). {
              econstructor.
              unfold in_variable_context; simpl.
              rewrite app_nth1; eauto.
              rewrite app_nth1 in H5; eauto.
            }
            apply H0 in HA.
            apply in_map_iff in HA; cleanup.
            eapply in_map_iff; eexists; split; eauto.
            destruct x0; simpl in *; try congruence.
            repeat case_analysis; clean_natb; inversionc H2; try lia.
          }
          destruct (Nat.eq_dec x (length Gsl)) as [Heq | Hneq].
          {
            subst x.
            rewrite nth_middle in H5.
            congruence.
          }
          assert (length Gsl < x) by lia.
          assert_fresh (typecheck_expression
            (pvc, Gsl ++ Gsr, qc) (Var (x - 1)) Qubit). {
            econstructor.
            unfold in_variable_context; simpl.
            rewrite app_nth2 by lia.
            rewrite app_nth2 in H5 by lia.
            replace (x - length Gsl) with
              (S (x - S (length Gsl))) in H5 by lia.
            simpl in H5.
            replace (x - 1 - length Gsl) with
              (x - S (length Gsl)) by lia.
            exact H5.
          }
          apply H0 in HA.
          apply in_map_iff in HA.
          destruct HA as [a [Heq Hin]].
          eapply in_map_iff; exists a; split; [|exact Hin].
          destruct a; simpl in *; try congruence.
          destruct (Nat.leb (length Gsl) x0) eqn:Hle.
          - apply Nat.leb_le in Hle.
            inversion Heq; f_equal; lia.
          - apply Nat.leb_gt in Hle.
            inversion Heq; lia.
      }
      split; intros.
      {
        apply in_map_iff in H2; cleanup.
        assert_fresh (typecheck_expression
          (pvc, Gsl ++ Gsr, qc)
          (incr_free_expression (length Gsl) m x) Qubit). {
          apply H0.
          apply in_map_iff; eexists; split; eauto.
        }
        destruct x; simpl in *; try congruence;
        inversion HA.
      }
      inversion H2.
    }
    {
      revert H1.
      clear.
      induction lz; simpl; eauto.
      intros; cleanup.
      econstructor; eauto.
      intros Hnot; apply H2.
      eapply in_map_iff in Hnot; cleanup.
      assert (x = a). {
        revert H.
        generalize x a (length Gsl) (S m).
        clear.
        induction x using expression_deep_ind; 
        simpl; destruct a; simpl; intros; try congruence.
        repeat case_analysis; clean_natb; inversionc H; try lia.
        assert (x = x0) by lia; subst; eauto.
        inversionc H0.
        assert (args = args0). {
          revert H3 H.
          clear.
          generalize dependent args0.
          induction args; simpl; intros; 
          destruct args0; simpl in *; try congruence.
          cleanup.
          apply H2 in H0; subst.
          erewrite IHargs; eauto.
        }
        subst; eauto.
      }
      subst; eauto.
      eapply in_map_iff; eexists; split; eauto.
    }
  }
  {(*p_send*)
    simpl in *. 
    eapply T_sub; eauto.
    econstructor; eauto.
    eapply slideSp_e; eauto.
    unfold remove_from_qubit_context, remove_from_variable_context in *; simpl in *.
    case_analysis; eauto.
    destruct ex; simpl in *; eauto.
    case_analysis; eauto.
    case_analysis; clean_natb.
    rewrite updn_app2 in H1 by lia.
    rewrite updn_app2 by lia.
    replace (x + S m - length Gsl)  with (S (x + m - length Gsl)) by lia; eauto.

    rewrite updn_app1 in H1 by lia.
    rewrite updn_app1 by lia.
    erewrite <- updn_length.
    erewrite <- updn_length in H1;
    eauto.
  }
  {(*p_recv*)
    simpl in *. 
    eapply T_sub; eauto.
    econstructor; eauto.
    eapply (SForall2_forall _ _ _ _ lBT).
    split; intros.
    eapply onth_move_out in H2; cleanup.
    eapply SForall_onth in H; eauto.
    eapply SForall2_onth_r in H3; eauto.
    cleanup.
    eapply onth_move_out in H3; cleanup.
    unfold insert_into_variable_context in *; simpl in *.
    specialize (H X m l b.2 ( Some b.1 :: Gsl)); simpl in *.
    eapply H in H4; eauto.
    split; intros.
    {
      split; intros.
      destruct_fresh (onth n lBT); eauto.
      eapply SForall2_onth_r in H1; eauto.
      cleanup.
      apply onth_move_out in H1; cleanup.
      eapply onth_move_in in H1.
      rewrite H1 in H2; discriminate.

      destruct_fresh (onth n (smap (incr_free l (S (length Gsl)) X (S m)) llp)); eauto.
      apply onth_move_out in HD; cleanup.
      eapply onth_move_in in H3.
      eapply SForall2_onth_l in H1; eauto.
      cleanup.
    }
    eapply SForall2_forall in H1; cleanup.
    rewrite <- H3.
    clear.
    induction llp; simpl; eauto.
    case_analysis; simpl; cleanup; eauto.
  }
  {(*p_ite*)
    simpl in *. 
    econstructor; eauto.
    eapply slideSp_e; eauto.
  }
  {(*p_rec*)
    simpl in *. 
    eapply T_sub; eauto.
    econstructor; eauto.
    unfold insert_into_process_context in *; simpl in *; eauto.
    unfold only_qubit_references_in_context in *; simpl in *.
    apply List.Forall_app in H0; cleanup.
    apply List.Forall_app; split; eauto.
  }
  {(*p_newq*)
    simpl in *. 
    econstructor; eauto.
    unfold insert_into_variable_context in *; simpl in *; eauto.
    specialize (IHQ X m l T ( Some Qubit :: Gsl)); simpl in *; eauto.
  }
  {(*p_unitary*)
    simpl in *. 
    econstructor; eauto.
    rewrite !length_map. reflexivity.
    eapply Forall_forall; intros z Hz.
    apply in_map_iff in Hz; cleanup.
    eapply slideSp_e; eauto.
    eapply Forall_forall in H0; eauto.
    apply in_map_iff; eexists; split; eauto.
    revert H1.
    clear.
    induction lz; simpl; eauto.
    intros; cleanup.
    econstructor; eauto.
    intros Hnot; apply H2.
    eapply in_map_iff in Hnot; cleanup.
    assert (x = a). {
      revert H.
      generalize x a (length Gsl) (S m).
      clear.
      induction x using expression_deep_ind; 
      simpl; destruct a; simpl; intros; try congruence.
      repeat case_analysis; clean_natb; inversionc H; try lia.
      assert (x = x0) by lia; subst; eauto.
      inversionc H0.
      assert (args = args0). {
        revert H3 H.
        clear.
        generalize dependent args0.
        induction args; simpl; intros; 
        destruct args0; simpl in *; try congruence.
        cleanup.
        apply H2 in H0; subst.
        erewrite IHargs; eauto.
      }
      subst; eauto.
    }
    subst; eauto.
    eapply in_map_iff; eexists; split; eauto.
  }
  {(*p_measure*)
    simpl in *. 
    econstructor; eauto.
    eapply slideSp_e; eauto.
    unfold insert_into_variable_context in *; simpl in *; eauto.
    destruct z as [v|x|op args]; simpl in *.
    + destruct v; simpl in *; try solve [inversion H].
      inversion H; subst.
      simpl in H0 |- *.
      eapply IHQ with (Gsl := Some header.Bool :: Gsl)
        (Gsr := Gsr) (pvc := pvc)
        (qc := delete (KEQ := qr_dec) qc q) (tm := tm); eauto.
    + destruct (Nat.leb (length Gsl) x) eqn:Hleb; simpl in *.
      * apply Nat.leb_le in Hleb.
        unfold remove_from_variable_context in H0 |- *; simpl in *.
        rewrite updn_app2 in H0 by lia.
        rewrite updn_app2 by lia.
        replace (x + S m - length Gsl)
          with (S (x + m - length Gsl)) by lia.
        simpl.
        eapply IHQ with (Gsl := Some header.Bool :: Gsl)
          (Gsr := updn Gsr (x + m - length Gsl) None)
          (pvc := pvc) (qc := qc) (tm := tm); eauto.
      * apply Nat.leb_gt in Hleb.
        unfold remove_from_variable_context in H0 |- *; simpl in *.
        rewrite updn_app1 in H0 by lia.
        rewrite updn_app1 by lia.
        assert (Hprefix_len :
          length (Some header.Bool :: updn Gsl x None) = S (length Gsl)).
        { simpl. rewrite updn_length. reflexivity. }
        rewrite <- Hprefix_len in H0 |- *.
        eapply IHQ with (Gsl := Some header.Bool :: updn Gsl x None)
          (Gsr := Gsr) (pvc := pvc) (qc := qc) (tm := tm); eauto.
    + inversion H.
  }
Qed.

Lemma slideS : forall Q X m tm Gs T pvc qc,
typecheck_process (pvc, Gs, qc) (incr_free 0 0 X m Q) T -> 
tm <> Some Qubit ->
typecheck_process (pvc, tm :: Gs, qc) (incr_free 0 0 X (S m) Q) T.
Proof.
  intros.
  specialize(slideSp Q X m 0 T [] Gs pvc qc tm H); intros. simpl in H1.
  apply H1; try easy.
Qed.

Lemma trivial_incr_expression : forall n e, (incr_free_expression n 0 e) = e.
Proof.
    induction e using expression_deep_ind;
    simpl; intros; eauto.
    repeat case_analysis; clean_natb; eauto; try lia.
    rewrite Nat.add_0_r; eauto.
    assert (map (incr_free_expression n 0) args = args).
    induction args; simpl; eauto.
    inversionc H; cleanup.
    inversionc H2.
    rewrite IHargs; eauto.
    rewrite H0; eauto.
Qed.

Lemma trivial_incr_expression_list : forall n lz,
  map (incr_free_expression n 0) lz = lz.
Proof.
  intros n lz; induction lz; simpl; [reflexivity|].
  rewrite trivial_incr_expression.
  f_equal; exact IHlz.
Qed.

Lemma smap_id_forall : forall A (P : A -> Prop) (f : A -> A) xs,
  (forall x, P x -> f x = x) ->
  SForall P xs ->
  smap f xs = xs.
Proof.
  intros A P f xs Hpoint Hforall.
  induction xs as [x|o xs IH].
  - simpl. f_equal. apply Hpoint. inversion Hforall; assumption.
  - destruct o as [x|].
    + simpl. inversion Hforall; subst. f_equal.
      * f_equal. apply Hpoint; assumption.
      * apply IH; assumption.
    + simpl. inversion Hforall; subst. f_equal. apply IH; assumption.
Qed.


Lemma trivial_incr : forall Q m n, (incr_free m n 0 0 Q) = Q.
Proof.
  induction Q using process_deep_ind; intros process_offset expr_offset; simpl.
  - destruct (Nat.leb process_offset n); simpl; rewrite ?Nat.add_0_r; f_equal;
      try reflexivity; apply trivial_incr_expression_list.
  - f_equal. apply trivial_incr_expression_list.
  - rewrite trivial_incr_expression, (IHQ process_offset expr_offset); reflexivity.
  - f_equal.
    eapply smap_id_forall with
      (P := fun p => forall m n, incr_free m n 0 0 p = p).
    + intros p Hp. exact (Hp process_offset (S expr_offset)).
    + exact H.
  - rewrite trivial_incr_expression, (IHQ1 process_offset expr_offset),
      (IHQ2 process_offset expr_offset); reflexivity.
  - rewrite (IHQ (S process_offset) expr_offset); reflexivity.
  - rewrite (IHQ process_offset (S expr_offset)); reflexivity.
  - rewrite trivial_incr_expression_list, (IHQ process_offset expr_offset); reflexivity.
  - rewrite trivial_incr_expression, (IHQ process_offset (S expr_offset)); reflexivity.
Qed.


Lemma expr_subst : forall ex v d Gsl Gsr B B' pvc qc,
  typecheck_expression (pvc, Gsl ++ Gsr, qc) (incr_free_expression 0 d v) B ->
  typecheck_expression (pvc, Gsl ++ Some B :: Gsr, qc) ex B' ->
  typecheck_expression (pvc, Gsl ++ Gsr, qc) (subst_expression (length Gsl) d v ex) B'.
Proof.
  induction ex using expression_deep_ind; intros. 
  inversionc H0; simpl in *; try solve [econstructor; simpl; eauto].
  {
    inversionc H0; simpl in *; try solve [econstructor; simpl; eauto].
    repeat case_analysis; clean_natb; eauto.
    { 
      econstructor; eauto.
      unfold in_variable_context in *; simpl in *.
      rewrite app_nth1 by lia.
      rewrite app_nth1 in H3 by lia.
      eauto.
    }
    { 
      unfold in_variable_context in *; simpl in *;
      cleanup.
      rewrite nth_middle in H3; cleanup; eauto. 
    }
    { 
      econstructor; eauto.
      unfold in_variable_context in *; simpl in *.
      rewrite app_nth2 by lia.
      rewrite app_nth2 in H3 by lia.
      replace (x - 1 - length Gsl) with (x - length Gsl - 1) by lia.
      simpl in *; case_analysis; try lia; simpl; eauto.
      rewrite Nat.sub_0_r; eauto.
    }
  }
  {
    inversionc H1; simpl in *; try solve [econstructor; simpl; eauto].
  }
Qed.

Lemma slideE : forall v Gs d B B' pvc qc,
  typecheck_expression (pvc, Gs, qc) (incr_free_expression 0 d v) B ->
  typecheck_expression (pvc, Some B'::Gs, qc)(incr_free_expression 0 (S d) v) B.
Proof.
  induction v using expression_deep_ind; intros. 
  inversionc H; simpl in *; try solve [econstructor; simpl; eauto].
  inversionc H; simpl in *; try solve [econstructor; simpl; eauto].
  econstructor; eauto.
  replace (x + S d) with (S (x + d)) by lia.
  unfold in_variable_context in *; simpl in *; eauto.

  inversionc H0; simpl in *; 
  repeat (destruct args; simpl in *; try congruence; cleanup);
  econstructor; eauto.
Qed.

Lemma expr_subst_quantum_fresh :
  forall ex q d Gsl Gsr B pvc (qc : qubit_context),
    qc q = None ->
    typecheck_expression
      (pvc, Gsl ++ Some Qubit :: Gsr, qc) ex B ->
    typecheck_expression
      (pvc, Gsl ++ Gsr, insert (KEQ := qr_dec) qc q tt)
      (subst_expression (length Gsl) d (Val (QVal q)) ex) B.
Proof.
  induction ex using expression_deep_ind; intros.
  - inversionc H0; simpl in *; try solve [econstructor; eauto].
    econstructor.
    unfold in_qubit_context in *; simpl in *.
    unfold insert; simpl.
    case_analysis; cleanup; eauto.
  - inversionc H0; simpl in *; repeat case_analysis; clean_natb; cleanup.
    + econstructor.
      unfold in_variable_context in *; simpl in *.
      rewrite app_nth1 by lia.
      rewrite app_nth1 in H3 by lia; exact H3.
    + unfold in_variable_context in H3; simpl in H3.
      rewrite nth_middle in H3; inversion H3; subst B.
      econstructor.
      unfold in_qubit_context; simpl.
      apply insert_eq.
    + econstructor.
      unfold in_variable_context in *; simpl in *.
      rewrite app_nth2 by lia.
      rewrite app_nth2 in H3 by lia.
      replace (x - 1 - length Gsl) with (x - length Gsl - 1) by lia.
      simpl in *; case_analysis; try lia; simpl; eauto.
      rewrite Nat.sub_0_r; eauto.
  - inversionc H1; simpl in *;
      repeat (destruct args; simpl in *; try congruence; cleanup);
      econstructor; eauto.
Qed.

Lemma subst_expression_quantum_fresh_injective :
  forall a b q d Gsl Gsr pvc (qc : qubit_context),
    qc q = None ->
    typecheck_expression (pvc, Gsl ++ Some Qubit :: Gsr, qc) a Qubit ->
    typecheck_expression (pvc, Gsl ++ Some Qubit :: Gsr, qc) b Qubit ->
    subst_expression (length Gsl) d (Val (QVal q)) a =
    subst_expression (length Gsl) d (Val (QVal q)) b ->
    a = b.
Proof.
  intros a b q d Gsl Gsr pvc qc Hfresh Ha Hb Heq.
  inversionc Ha; inversionc Hb; simpl in Heq;
    repeat case_analysis; clean_natb; cleanup; try congruence; try lia;
    unfold in_qubit_context, in_variable_context in *; simpl in *;
    cleanup; try congruence; try lia.
  all: inversion Heq; subst; f_equal; lia.
Qed.

Lemma subst_expression_quantum_fresh_NoDup :
  forall l q d Gsl Gsr pvc (qc : qubit_context),
    qc q = None ->
    Forall
      (fun z => typecheck_expression
        (pvc, Gsl ++ Some Qubit :: Gsr, qc) z Qubit) l ->
    NoDup l ->
    NoDup (map (subst_expression (length Gsl) d (Val (QVal q))) l).
Proof.
  intros l q d Gsl Gsr pvc qc Hfresh Htyped Hnodup.
  revert Htyped.
  induction Hnodup; intros Htyped; inversionc Htyped; simpl; constructor.
  - intro Hin.
    apply in_map_iff in Hin; cleanup.
    assert (Hx0 : typecheck_expression
      (pvc, Gsl ++ Some Qubit :: Gsr, qc) x0 Qubit).
    { eapply Forall_forall in H3; eauto. }
    apply H.
    replace x with x0; [assumption |].
    symmetry; eapply subst_expression_quantum_fresh_injective; eauto.
  - apply IHHnodup; assumption.
Qed.

(* A variable slot already marked unavailable can be contracted: no typed
   expression can mention that slot, and substitution simply closes the
   resulting index gap.  The send case uses this when its argument consumes
   the distinguished qubit variable. *)
Lemma expr_subst_unavailable_quantum_slot :
  forall ex q d B Gsl Gsr pvc qc,
    typecheck_expression (pvc, Gsl ++ None :: Gsr, qc) ex B ->
    typecheck_expression (pvc, Gsl ++ Gsr, qc)
      (subst_expression (length Gsl) d (Val (QVal q)) ex) B.
Proof.
  intros ex.
  induction ex using expression_deep_ind; intros.
  - match goal with Hty : typecheck_expression _ (Val _) _ |- _ => inversionc Hty end;
      simpl in *; try solve [econstructor; eauto].
  - match goal with Hty : typecheck_expression _ (Var _) _ |- _ => inversionc Hty end;
      simpl in *; repeat case_analysis; clean_natb; cleanup.
    + econstructor.
      unfold in_variable_context in *; simpl in *.
      rewrite app_nth1 by lia.
      rewrite app_nth1 in * by lia; eauto.
    + unfold in_variable_context in *; simpl in *.
      rewrite nth_middle in *; discriminate.
    + econstructor.
      unfold in_variable_context in *; simpl in *.
      rewrite app_nth2 in * by lia.
      replace (x - 1 - length Gsl) with (x - length Gsl - 1) by lia.
      replace (x - length Gsl) with (S (x - length Gsl - 1)) in * by lia.
      simpl in *; eauto.
      rewrite Nat.sub_0_r; eauto.
  - match goal with Hty : typecheck_expression _ (Op _ _) _ |- _ => inversionc Hty end;
      simpl in *;
      repeat (destruct args; simpl in *; try congruence; cleanup);
      econstructor; eauto.
Qed.

Fixpoint lift_unavailable_expression (n : nat) (ex : expression) : expression :=
  match ex with
  | Val _ => ex
  | Var x => Var (if Nat.leb n x then S x else x)
  | Op op args => Op op (map (lift_unavailable_expression n) args)
  end.

Lemma subst_lift_unavailable_expression :
  forall ex n q d,
    subst_expression n d (Val (QVal q))
      (lift_unavailable_expression n ex) = ex.
Proof.
  induction ex using expression_deep_ind; intros; simpl.
  - reflexivity.
  - destruct (Nat.leb n x) eqn:Hnx; simpl.
    + apply Nat.leb_le in Hnx.
      assert (Hlt : (S x <? n) = false) by (apply Nat.ltb_ge; lia).
      rewrite Hlt. destruct n; simpl; [replace (x - 0) with x by lia; reflexivity|].
      assert (Heq : (x =? n) = false) by (apply Nat.eqb_neq; lia).
      rewrite Heq. simpl. f_equal; lia.
    + apply Nat.leb_gt in Hnx.
      assert (Hlt : (x <? n) = true) by (apply Nat.ltb_lt; lia).
      rewrite Hlt. reflexivity.
  - simpl. f_equal. rewrite map_map.
    induction args as [|a args IHargs]; simpl; [reflexivity|].
    inversion H; subst. f_equal; [eauto|]. apply IHargs; assumption.
Qed.

Lemma lift_unavailable_expression_typed :
  forall ex B (Gsl Gsr : variable_context) (pvc : process_context)
    (qc : qubit_context),
    typecheck_expression (pvc, Gsl ++ Gsr, qc) ex B ->
    typecheck_expression (pvc, Gsl ++ None :: Gsr, qc)
      (lift_unavailable_expression (length Gsl) ex) B.
Proof.
  intros ex.
  induction ex using expression_deep_ind; intros B Gsl Gsr pvc qc Htyped.
  - inversionc Htyped; simpl; econstructor; eauto.
  - inversionc Htyped; simpl in *.
    econstructor. unfold in_variable_context in *; simpl in *.
    destruct (Nat.leb (length Gsl) x) eqn:Hnx.
    + apply Nat.leb_le in Hnx.
      rewrite app_nth2 in * by lia.
      replace (S x - length Gsl) with (S (x - length Gsl)) by lia.
      simpl in *. exact H1.
    + apply Nat.leb_gt in Hnx.
      rewrite app_nth1 in * by lia. exact H1.
  - inversionc Htyped; simpl in *;
      repeat (destruct args; simpl in *; try congruence; cleanup);
      econstructor; eauto.
Qed.

Lemma subst_lift_unavailable_typed :
  forall ex q B Gsl Gsr pvc (qc : qubit_context) d,
    typecheck_expression (pvc, Gsl ++ None :: Gsr, qc) ex B ->
    lift_unavailable_expression (length Gsl)
      (subst_expression (length Gsl) d (Val (QVal q)) ex) = ex.
Proof.
  intros ex.
  induction ex using expression_deep_ind; intros q B Gsl Gsr pvc qc d Htyped.
  - inversionc Htyped; reflexivity.
  - inversionc Htyped; simpl in *.
    unfold in_variable_context in H1; simpl in H1.
    destruct (Nat.ltb x (length Gsl)) eqn:Hlt.
    + apply Nat.ltb_lt in Hlt. simpl.
      assert (Hle : Nat.leb (length Gsl) x = false).
      { apply Nat.leb_gt. lia. }
      rewrite Hle. reflexivity.
    + destruct (Nat.eqb x (length Gsl)) eqn:Heq.
      * apply Nat.eqb_eq in Heq. subst x.
        rewrite nth_middle in H1. discriminate.
      * apply Nat.ltb_ge in Hlt. apply Nat.eqb_neq in Heq.
        simpl. assert (Hle : Nat.leb (length Gsl) (x - 1) = true).
        { apply Nat.leb_le. lia. }
        rewrite Hle. f_equal; lia.
  - inversionc Htyped; simpl in *.
    all: f_equal; simpl; repeat f_equal; eauto.
Qed.

Lemma subst_unavailable_quantum_list_complete :
  forall lz q d Gsl Gsr pvc (qc : qubit_context),
    (forall z, In z lz <->
      typecheck_expression (pvc, Gsl ++ None :: Gsr, qc) z Qubit) ->
    forall z,
      In z (map (subst_expression (length Gsl) d (Val (QVal q))) lz) <->
      typecheck_expression (pvc, Gsl ++ Gsr, qc) z Qubit.
Proof.
  intros lz q d Gsl Gsr pvc qc Hcomplete z.
  split.
  - intros Hin. apply in_map_iff in Hin. destruct Hin as [z0 [Hmap Hin]].
    apply Hcomplete in Hin. rewrite <- Hmap.
    eapply expr_subst_unavailable_quantum_slot; eauto.
  - intros Htyped.
    pose proof (lift_unavailable_expression_typed z Qubit Gsl Gsr pvc qc
      Htyped) as Hlift.
    apply Hcomplete in Hlift.
    apply in_map_iff. exists (lift_unavailable_expression (length Gsl) z).
    split; [apply subst_lift_unavailable_expression|exact Hlift].
Qed.

Lemma subst_unavailable_quantum_NoDup :
  forall lz q d Gsl Gsr pvc (qc : qubit_context),
    Forall (fun z =>
      typecheck_expression (pvc, Gsl ++ None :: Gsr, qc) z Qubit) lz ->
    NoDup lz ->
    NoDup (map (subst_expression (length Gsl) d (Val (QVal q))) lz).
Proof.
  intros lz q d Gsl Gsr pvc qc Htyped Hnodup.
  revert Htyped.
  induction Hnodup as [|a lz Hnot Hnodup IH]; intros Htyped.
  - inversion Htyped. constructor.
  - inversion Htyped as [|? ? Htypea Htypel]; subst.
    simpl. constructor.
    + intro Hin. apply in_map_iff in Hin.
      destruct Hin as [z [Hmap Hzin]].
      assert (Heq : z = a).
      { assert (Hztyped : typecheck_expression
          (pvc, Gsl ++ None :: Gsr, qc) z Qubit).
        { apply (proj1 (Forall_forall
            (fun z => typecheck_expression
              (pvc, Gsl ++ None :: Gsr, qc) z Qubit) lz)); assumption. }
        pose proof (f_equal (lift_unavailable_expression (length Gsl)) Hmap) as Hlift.
        pose proof (subst_lift_unavailable_typed z q Qubit Gsl Gsr pvc qc d Hztyped) as Hz.
        pose proof (subst_lift_unavailable_typed a q Qubit Gsl Gsr pvc qc d Htypea) as Ha.
        rewrite Hz, Ha in Hlift. exact Hlift. }
      apply Hnot. rewrite <- Heq. exact Hzin.
    + apply IH. assumption.
Qed.

Lemma subst_p_end_unavailable_quantum_slot :
  forall lz q d Gsl Gsr pvc (qc : qubit_context),
    (forall z, In z lz <->
      typecheck_expression (pvc, Gsl ++ None :: Gsr, qc) z Qubit) ->
    NoDup lz ->
    typecheck_process (pvc, Gsl ++ Gsr, qc)
      (p_end (map (subst_expression (length Gsl) d (Val (QVal q))) lz))
      ltt_end.
Proof.
  intros lz q d Gsl Gsr pvc qc Hcomplete Hnodup.
  assert (Hfor : Forall
    (fun z => typecheck_expression
      (pvc, Gsl ++ None :: Gsr, qc) z Qubit) lz).
  { apply Forall_forall. intros z Hin. apply Hcomplete. exact Hin. }
  assert (Hlisted : forall z,
    In z (map (subst_expression (length Gsl) d (Val (QVal q))) lz) <->
    typecheck_expression (pvc, Gsl ++ Gsr, qc) z Qubit).
  { apply subst_unavailable_quantum_list_complete. exact Hcomplete. }
  assert (Hnd : NoDup
    (map (subst_expression (length Gsl) d (Val (QVal q))) lz)).
  { eapply subst_unavailable_quantum_NoDup; eauto. }
  econstructor; eauto.
Qed.

Lemma subst_unavailable_recv_branches :
  forall llp lBT q d Gsl Gsr pvc (qc : qubit_context),
    SForall (fun P => forall q' d' T' Gsl' Gsr' pvc' (qc' : qubit_context),
      typecheck_process (pvc', Gsl' ++ None :: Gsr', qc') P T' ->
      typecheck_process (pvc', Gsl' ++ Gsr', qc')
        (subst_expression_in_process (length Gsl') d' (Val (QVal q')) P) T') llp ->
    SForall2
      (fun P BT => typecheck_process
        (insert_into_variable_context
          (pvc, Gsl ++ None :: Gsr, qc) BT.1) P BT.2) llp lBT ->
    SForall2
      (fun P BT => typecheck_process
        (insert_into_variable_context
          (pvc, Gsl ++ Gsr, qc) BT.1) P BT.2)
      (smap (subst_expression_in_process (S (length Gsl)) (S d) (Val (QVal q))) llp)
      lBT.
Proof.
  intros llp lBT q d Gsl Gsr pvc qc Hih Hbranches.
  revert Hih.
  induction Hbranches; intros Hih.
  - inversion Hih; subst; cleanup. simpl. constructor.
    apply (H1 q (S d) y.2 (Some y.1 :: Gsl) Gsr pvc qc).
    simpl in H. exact H.
  - inversion Hih; subst; cleanup. simpl. econstructor.
    + apply (H2 q (S d) y.2 (Some y.1 :: Gsl) Gsr pvc qc).
      simpl in H. exact H.
    + exact (IHHbranches H3).
  - inversion Hih; subst; cleanup. simpl. constructor.
    eapply IHHbranches; eauto.
Qed.

Lemma subst_fresh_recv_branches :
  forall llp lBT q d Gsl Gsr pvc (qc : qubit_context),
    SForall (fun P => forall q' d' T' Gsl' Gsr' pvc' (qc' : qubit_context),
      qc' q' = None ->
      typecheck_process (pvc', Gsl' ++ Some Qubit :: Gsr', qc') P T' ->
      typecheck_process (pvc', Gsl' ++ Gsr',
        insert (KEQ := qr_dec) qc' q' tt)
        (subst_expression_in_process (length Gsl') d' (Val (QVal q')) P) T') llp ->
    SForall2
      (fun P BT => typecheck_process
        (insert_into_variable_context
          (pvc, Gsl ++ Some Qubit :: Gsr, qc) BT.1) P BT.2) llp lBT ->
    qc q = None ->
    SForall2
      (fun P BT => typecheck_process
        (insert_into_variable_context
          (pvc, Gsl ++ Gsr, insert (KEQ := qr_dec) qc q tt) BT.1) P BT.2)
      (smap (subst_expression_in_process (S (length Gsl)) (S d) (Val (QVal q))) llp)
      lBT.
Proof.
  intros llp lBT q d Gsl Gsr pvc qc Hih Hbranches Hfresh.
  revert Hih.
  induction Hbranches; intros Hih.
  - inversion Hih; subst; cleanup. simpl. constructor.
    apply (H1 q (S d) y.2 (Some y.1 :: Gsl) Gsr pvc qc Hfresh).
    simpl in H. exact H.
  - inversion Hih; subst; cleanup. simpl. econstructor.
    + apply (H2 q (S d) y.2 (Some y.1 :: Gsl) Gsr pvc qc Hfresh).
      simpl in H. exact H.
    + exact (IHHbranches H3).
  - inversion Hih; subst; cleanup. simpl. constructor.
    eapply IHHbranches; eauto.
Qed.

Lemma variable_qubit_slot_not_only_refs :
  forall Gsl Gsr pvc (qc : qubit_context),
    ~ only_qubit_references_in_context
      (pvc, Gsl ++ Some Qubit :: Gsr, qc).
Proof.
  intros Gsl Gsr pvc qc Honly.
  unfold only_qubit_references_in_context in Honly; simpl in Honly.
  assert (Hin : In (Some Qubit) (Gsl ++ Some Qubit :: Gsr)).
  { apply in_or_app. right. simpl. auto. }
  apply Forall_forall with (x := Some Qubit) in Honly.
  - contradiction.
  - exact Hin.
Qed.

Lemma only_qubit_refs_contract_none :
  forall Gsl Gsr pvc (qc : qubit_context),
    only_qubit_references_in_context
      (pvc, Gsl ++ None :: Gsr, qc) ->
    only_qubit_references_in_context (pvc, Gsl ++ Gsr, qc).
Proof.
  intros Gsl Gsr pvc qc Honly.
  unfold only_qubit_references_in_context in *; simpl in *.
  rewrite Forall_forall in Honly |- *.
  intros s Hin.
  apply Honly.
  apply in_app_or in Hin as [Hin | Hin].
  - apply in_or_app. left. exact Hin.
  - apply in_or_app. right. simpl. right. exact Hin.
Qed.

(* Reconstruct the expression before substitution from one typed in the
   contracted variable context.  A reference to the newly inserted quantum
   is represented by the variable slot being substituted away. *)
Fixpoint lift_fresh_quantum_expression (n : nat) (q : qubit_reference)
    (ex : expression) : expression :=
  match ex with
  | Val (QVal q') => if qr_dec q' q then Var n else ex
  | Val _ => ex
  | Var x => Var (if Nat.leb n x then S x else x)
  | Op op args => Op op (map (lift_fresh_quantum_expression n q) args)
  end.

Lemma subst_lift_fresh_quantum_expression :
  forall ex n q d,
    subst_expression n d (Val (QVal q))
      (lift_fresh_quantum_expression n q ex) = ex.
Proof.
  induction ex using expression_deep_ind; intros; simpl.
  - destruct v; simpl; try reflexivity.
    destruct (qr_dec q0 q) as [-> | Hneq].
    + simpl. rewrite Nat.ltb_irrefl, Nat.eqb_refl. reflexivity.
    + simpl. reflexivity.
  - destruct (Nat.leb n x) eqn:Hnx; simpl.
    + apply Nat.leb_le in Hnx.
      assert (Hlt : (S x <? n) = false) by (apply Nat.ltb_ge; lia).
      rewrite Hlt. destruct n; simpl; [replace (x - 0) with x by lia; reflexivity|].
      assert (Heq : (x =? n) = false) by (apply Nat.eqb_neq; lia).
      rewrite Heq. simpl. f_equal; lia.
    + apply Nat.leb_gt in Hnx.
      assert (Hlt : (x <? n) = true) by (apply Nat.ltb_lt; lia).
      rewrite Hlt. reflexivity.
  - simpl. f_equal. rewrite map_map.
    induction args as [|a args IH]; simpl; [reflexivity|].
    inversion H; subst. f_equal; [eauto|]. apply IH; assumption.
Qed.

Lemma lift_fresh_quantum_expression_typed :
  forall ex q B (Gsl Gsr : variable_context) (pvc : process_context)
    (qc : qubit_context),
    qc q = None ->
    typecheck_expression
      (pvc, Gsl ++ Gsr, insert (KEQ := qr_dec) qc q tt) ex B ->
    typecheck_expression (pvc, Gsl ++ Some Qubit :: Gsr, qc)
      (lift_fresh_quantum_expression (length Gsl) q ex) B.
Proof.
  intros ex.
  induction ex using expression_deep_ind; intros q B Gsl Gsr pvc qc Hfresh Htyped.
  - inversionc Htyped; simpl.
    + econstructor.
    + econstructor.
    + simpl in *.
      destruct (qr_dec q0 q) as [-> | Hneq].
      * econstructor. unfold in_variable_context; simpl.
        rewrite nth_middle. reflexivity.
      * econstructor. unfold in_qubit_context in *; simpl in *.
        destruct (qr_dec q q0); [congruence|]. simpl in H1. exact H1.
  - inversionc Htyped; simpl in *.
    econstructor. unfold in_variable_context in *; simpl in *.
    destruct (Nat.leb (length Gsl) x) eqn:Hnx.
    + apply Nat.leb_le in Hnx.
      rewrite app_nth2 in * by lia.
      replace (S x - length Gsl) with (S (x - length Gsl)) by lia.
      simpl in *. exact H1.
    + apply Nat.leb_gt in Hnx.
      rewrite app_nth1 in * by lia. exact H1.
  - inversionc Htyped; simpl in *;
      repeat (destruct args; simpl in *; try congruence; cleanup);
      econstructor; eauto.
Qed.

Lemma subst_fresh_quantum_list_complete :
  forall lz q d Gsl Gsr pvc (qc : qubit_context),
    qc q = None ->
    (forall z, In z lz <->
      typecheck_expression (pvc, Gsl ++ Some Qubit :: Gsr, qc) z Qubit) ->
    forall z,
      In z (map (subst_expression (length Gsl) d (Val (QVal q))) lz) <->
      typecheck_expression
        (pvc, Gsl ++ Gsr, insert (KEQ := qr_dec) qc q tt) z Qubit.
Proof.
  intros lz q d Gsl Gsr pvc qc Hfresh Hcomplete z.
  split.
  - intros Hin. apply in_map_iff in Hin. destruct Hin as [z0 [Hmap Hin]].
    apply Hcomplete in Hin. rewrite <- Hmap.
    eapply expr_subst_quantum_fresh; eauto.
  - intros Htyped.
    pose proof (lift_fresh_quantum_expression_typed z q Qubit Gsl Gsr pvc qc
      Hfresh Htyped) as Hlift.
    apply Hcomplete in Hlift.
    apply in_map_iff. exists (lift_fresh_quantum_expression (length Gsl) q z).
    split; [apply subst_lift_fresh_quantum_expression|exact Hlift].
Qed.

Lemma subst_p_end_fresh_quantum :
  forall lz q d Gsl Gsr pvc (qc : qubit_context),
    qc q = None ->
    (forall z, In z lz <->
      typecheck_expression (pvc, Gsl ++ Some Qubit :: Gsr, qc) z Qubit) ->
    NoDup lz ->
    typecheck_process
      (pvc, Gsl ++ Gsr, insert (KEQ := qr_dec) qc q tt)
      (p_end (map (subst_expression (length Gsl) d (Val (QVal q))) lz))
      ltt_end.
Proof.
  intros lz q d Gsl Gsr pvc qc Hfresh Hcomplete Hnodup.
  assert (Hfor : Forall
      (fun z => typecheck_expression
        (pvc, Gsl ++ Some Qubit :: Gsr, qc) z Qubit) lz).
  { apply Forall_forall. intros z Hin. apply Hcomplete. exact Hin. }
  assert (Hlisted : forall z,
    In z (map (subst_expression (length Gsl) d (Val (QVal q))) lz) <->
    typecheck_expression
      (pvc, Gsl ++ Gsr, insert (KEQ := qr_dec) qc q tt) z Qubit).
  { apply subst_fresh_quantum_list_complete; assumption. }
  assert (Hnd : NoDup
    (map (subst_expression (length Gsl) d (Val (QVal q))) lz)).
  { eapply subst_expression_quantum_fresh_NoDup; eauto. }
  econstructor; eauto.
Qed.

Lemma process_context_equivalent_refl :
  forall pvc,
    Forall2
      (fun Tq1 Tq2 => (Tq1 = None /\ Tq2 = None) \/
        (exists T' T'' (qc1 qc2 : qubit_context),
          Tq1 = Some (T', qc1) /\ Tq2 = Some (T'', qc2) /\
          equivalent qc2 qc1 /\ subtypeC T'' T')) pvc pvc.
Proof.
  induction pvc as [|entry pvc IH]; simpl; constructor.
  destruct entry as [[T0 qc0]|].
  - right. exists T0, T0, qc0, qc0.
    split; [reflexivity|].
    split; [reflexivity|].
    split; [apply equivalent_refl|apply stRefl].
  - left; split; reflexivity.
  - exact IH.
Qed.

Lemma typecheck_process_delete_insert_comm :
  forall P T Gsl Gsr pvc (qc : qubit_context) q r,
    r <> q ->
    typecheck_process
      (pvc, Gsl ++ Gsr, insert (KEQ := qr_dec) (delete (KEQ := qr_dec) qc r) q tt) P T ->
    typecheck_process
      (pvc, Gsl ++ Gsr, delete (KEQ := qr_dec) (insert (KEQ := qr_dec) qc q tt) r) P T.
Proof.
  intros P T Gsl Gsr pvc qc q r Hneq Htyped.
  eapply typecheck_process_equivalent with
    (theta1 := (pvc, Gsl ++ Gsr,
      insert (KEQ := qr_dec) (delete (KEQ := qr_dec) qc r) q tt))
    (theta2 := (pvc, Gsl ++ Gsr,
      delete (KEQ := qr_dec) (insert (KEQ := qr_dec) qc q tt) r)).
  - exact Htyped.
  - reflexivity.
  - apply process_context_equivalent_refl.
  - apply insert_delete_comm. exact Hneq.
Qed.

Lemma typecheck_process_delete_insert_same :
  forall P T Gsl Gsr pvc (qc : qubit_context) q,
    qc q = None ->
    typecheck_process (pvc, Gsl ++ Gsr, qc) P T ->
    typecheck_process
      (pvc, Gsl ++ Gsr, delete (KEQ := qr_dec) (insert (KEQ := qr_dec) qc q tt) q)
      P T.
Proof.
  intros P T Gsl Gsr pvc qc q Hfresh Htyped.
  eapply typecheck_process_equivalent with
    (theta1 := (pvc, Gsl ++ Gsr, qc))
    (theta2 := (pvc, Gsl ++ Gsr,
      delete (KEQ := qr_dec) (insert (KEQ := qr_dec) qc q tt) q)).
  - exact Htyped.
  - reflexivity.
  - apply process_context_equivalent_refl.
  - apply equivalent_sym, delete_insert_noop. exact Hfresh.
Qed.

Lemma typecheck_send_fresh_qubit_value :
  forall P pt lb q0 q T' T Gsl Gsr pvc (qc : qubit_context),
    qc q = None ->
    qc q0 = Some tt ->
    subtypeC
      (ltt_send pt (fun n => if Nat.eqb n lb then Some (Qubit, T') else None)) T ->
    typecheck_process
      (pvc, Gsl ++ Gsr,
        insert (KEQ := qr_dec) (delete (KEQ := qr_dec) qc q0) q tt) P T' ->
    typecheck_process (pvc, Gsl ++ Gsr, insert (KEQ := qr_dec) qc q tt)
      (p_send pt lb (Val (QVal q0)) P) T.
Proof.
  intros P pt lb q0 q T' T Gsl Gsr pvc qc Hfresh Hq0 Hsub Hcont.
  assert (Hneq : q0 <> q) by (intro Heq; subst; congruence).
  eapply T_sub with
    (T := ltt_send pt (fun n => if Nat.eqb n lb then Some (Qubit, T') else None)).
  - eapply T_send with (B := Qubit) (T := T').
    + econstructor. unfold in_qubit_context; simpl.
      destruct (qr_dec q q0); [congruence|exact Hq0].
    + eapply typecheck_process_delete_insert_comm; eauto.
  - exact Hsub.
Qed.

Lemma subst_expression_in_process_unavailable_quantum_slot :
  forall P q d T Gsl Gsr pvc (qc : qubit_context),
    typecheck_process (pvc, Gsl ++ None :: Gsr, qc) P T ->
    typecheck_process (pvc, Gsl ++ Gsr, qc)
      (subst_expression_in_process (length Gsl) d (Val (QVal q)) P) T.
Proof.
  induction P using process_deep_ind; simpl; intros; invert_typecheck; cleanup; simpl in *; eauto.
  1: assert (Hlist : forall z,
       In z (map (subst_expression (length Gsl) d (Val (QVal q))) lz) <->
       typecheck_expression (pvc, Gsl ++ Gsr, qc) z Qubit).
     { eapply subst_unavailable_quantum_list_complete; exact H3. }
     assert (Hfor : Forall
       (fun z => typecheck_expression (pvc, Gsl ++ None :: Gsr, qc) z Qubit) lz).
     { apply Forall_forall. intros z Hz. apply H3. exact Hz. }
     assert (Hnd : NoDup
       (map (subst_expression (length Gsl) d (Val (QVal q))) lz)).
     { eapply subst_unavailable_quantum_NoDup; eauto. }
     eapply T_sub with (T := T').
     - eapply T_var with (qcontext := qcontext)
         (lz := map (subst_expression (length Gsl) d (Val (QVal q))) lz).
       + exact H0.
       + eapply only_qubit_refs_contract_none; exact H1.
       + exact H2.
       + exact Hlist.
       + exact Hnd.
     - exact H5.
  1: eapply T_sub with (T := ltt_end); [eapply subst_p_end_unavailable_quantum_slot; eauto | exact H0].
  all: try solve [repeat case_analysis; cleanup; simpl in *; eauto using expr_subst_unavailable_quantum_slot].
  1: destruct B.
     - simpl in H2.
       eapply T_sub with (T := ltt_send pt (fun n => if Nat.eqb n lb then Some (header.Nat,T') else None)).
       + eapply T_send with (B := header.Nat) (T := T').
         * eapply expr_subst_unavailable_quantum_slot; eauto.
         * exact (IHP q d T' Gsl Gsr pvc qc H2).
       + exact H0.
     - simpl in H2.
       eapply T_sub with (T := ltt_send pt (fun n => if Nat.eqb n lb then Some (header.Bool,T') else None)).
       + eapply T_send with (B := header.Bool) (T := T').
         * eapply expr_subst_unavailable_quantum_slot; eauto.
         * exact (IHP q d T' Gsl Gsr pvc qc H2).
       + exact H0.
     - destruct ex; simpl in *; try solve [inversion H1].
       + inversion H1; subst.
         unfold remove_from_qubit_context in H2; simpl in H2.
         eapply T_sub with (T := ltt_send pt (fun n => if Nat.eqb n lb then Some (Qubit,T') else None)).
         * eapply T_send with (B := Qubit) (T := T').
           -- econstructor; exact H5.
           -- exact (IHP q d T' Gsl Gsr pvc (delete (KEQ := qr_dec) qc q0) H2).
         * exact H0.
       + inversion H1; subst.
         destruct (Nat.ltb x (length Gsl)) eqn:Hx.
         * pose proof (proj1 (Nat.ltb_lt x (length Gsl)) Hx) as Hxlt.
           unfold remove_from_variable_context in H2; simpl in H2.
           rewrite updn_app1 in H2 by lia.
           eapply T_sub with (T := ltt_send pt (fun n => if Nat.eqb n lb then Some (Qubit,T') else None)).
           -- eapply T_send with (B := Qubit) (T := T').
              ++ econstructor; unfold in_variable_context in *; simpl in *; rewrite app_nth1 in * by lia; eauto.
              ++ unfold remove_from_variable_context; simpl; rewrite updn_app1 by lia.
                 pose proof (IHP q d T' (updn Gsl x None) Gsr pvc qc H2) as Hcont.
                 rewrite updn_length in Hcont. exact Hcont.
           -- exact H0.
         * destruct (Nat.eqb x (length Gsl)) eqn:Heq.
           -- apply Nat.eqb_eq in Heq; subst x.
              unfold in_variable_context in *; simpl in *.
              repeat rewrite nth_middle in *; discriminate.
           -- pose proof (proj1 (Nat.ltb_ge x (length Gsl)) Hx) as Hxge.
              pose proof (proj1 (Nat.eqb_neq x (length Gsl)) Heq) as Hneq.
              unfold remove_from_variable_context in H2; simpl in H2.
              rewrite updn_app2 in H2 by lia.
              replace (x - length Gsl) with (S (x - length Gsl - 1)) in H2 by lia.
              simpl in H2.
              eapply T_sub with (T := ltt_send pt (fun n => if Nat.eqb n lb then Some (Qubit,T') else None)).
              ++ eapply T_send with (B := Qubit) (T := T').
                 ** econstructor; unfold in_variable_context in *; simpl in *.
                    rewrite app_nth2 by lia.
                    rewrite app_nth2 in H5 by lia.
                    replace (x - 1 - length Gsl) with (x - length Gsl - 1) by lia.
                    replace (x - length Gsl) with (S (x - length Gsl - 1)) in H5 by lia.
                    simpl in H5. exact H5.
                 ** unfold remove_from_variable_context; simpl; rewrite updn_app2 by lia.
                    replace (x - 1 - length Gsl) with (x - length Gsl - 1) by lia.
                    exact (IHP q d T' Gsl (updn Gsr (x - length Gsl - 1) None) pvc qc H2).
              ++ exact H0.
  1: eapply T_sub with (T := ltt_recv pt (fun n => onth n lBT)).
     - eapply T_recv. eapply subst_unavailable_recv_branches; eauto.
     - exact H1.
  1: eapply T_if.
     - eapply expr_subst_unavailable_quantum_slot; eauto.
     - exact (IHP1 q d T Gsl Gsr pvc qc H1).
     - exact (IHP2 q d T Gsl Gsr pvc qc H2).
  1: eapply T_sub with (T := T').
     - eapply T_rec.
       + exact (IHP q d T' Gsl Gsr (Some (T', qc) :: pvc) qc H0).
       + eapply only_qubit_refs_contract_none; exact H1.
     - exact H2.
  1: eapply T_qbit.
     exact (IHP q (S d) T (Some Qubit :: Gsl) Gsr pvc qc Hx).
  1: eapply T_U.
     - simpl. rewrite length_map. reflexivity.
     - apply Forall_forall. intros z Hz.
       apply in_map_iff in Hz. destruct Hz as [z0 [Hz Hz0]].
       rewrite <- Hz.
       eapply expr_subst_unavailable_quantum_slot.
       apply Forall_forall with (x := z0) in H1; assumption.
     - eapply subst_unavailable_quantum_NoDup; eauto.
     - exact (IHP q d T Gsl Gsr pvc qc H3).
  1: eapply T_meas.
     - eapply expr_subst_unavailable_quantum_slot; eauto.
     - destruct z as [v|x|op args]; simpl in *.
       + destruct v; simpl in *; try solve [inversion H0].
         inversion H0; subst.
         unfold remove_from_qubit_context in H1; simpl in H1.
         exact (IHP q (S d) T (Some header.Bool :: Gsl) Gsr pvc
           (delete (KEQ := qr_dec) qc q0) H1).
       + assert (Hxneq : x <> length Gsl).
         {
           intro Heq; subst x.
           inversion H0; subst.
           unfold in_variable_context in *; simpl in *.
           repeat rewrite nth_middle in *; discriminate.
         }
         destruct (Nat.ltb x (length Gsl)) eqn:Hx.
         * apply Nat.ltb_lt in Hx.
           unfold remove_from_variable_context in H1; simpl in H1.
           rewrite updn_app1 in H1 by lia.
           pose proof (IHP q (S d) T
             (Some header.Bool :: updn Gsl x None) Gsr pvc qc H1) as Hcont.
           simpl in Hcont |- *.
           rewrite updn_length in Hcont.
           unfold remove_measured_expression_from_context,
             remove_from_variable_context in *; simpl in *.
           rewrite updn_app1 by lia.
           exact Hcont.
         * apply Nat.ltb_ge in Hx.
           assert (Hgt : length Gsl < x) by lia.
           destruct (Nat.eqb x (length Gsl)) eqn:Heq.
           { apply Nat.eqb_eq in Heq; contradiction. }
           apply Nat.eqb_neq in Heq.
           unfold remove_from_variable_context in H1; simpl in H1.
           rewrite updn_app2 in H1 by lia.
           replace (x - length Gsl) with (S (x - length Gsl - 1)) in H1 by lia.
           simpl in H1.
           pose proof (IHP q (S d) T (Some header.Bool :: Gsl)
             (updn Gsr (x - length Gsl - 1) None) pvc qc H1) as Hcont.
           unfold remove_measured_expression_from_context,
             remove_from_variable_context in *; simpl in *.
           rewrite updn_app2 by lia.
           replace (x - 1 - length Gsl) with
             (x - length Gsl - 1) by lia.
           exact Hcont.
       + inversion H0.
Qed.

Lemma subst_expression_in_process_helper_quantum :
  forall P q d T Gsl Gsr pvc (qc: qubit_context),
    qc q = None ->
    typecheck_process
      (pvc, Gsl ++ Some Qubit :: Gsr, qc) P T ->
    typecheck_process
      (pvc, Gsl ++ Gsr, insert (KEQ := qr_dec) qc q tt)
      (subst_expression_in_process
         (length Gsl) d (Val (QVal q)) P) T.
Proof.
  induction P using process_deep_ind; simpl; intros;
    invert_typecheck; cleanup; simpl in *; eauto.
  1: exfalso. eapply variable_qubit_slot_not_only_refs; eauto.
  1: eapply T_sub with (T := ltt_end).
     - eapply subst_p_end_fresh_quantum; eauto.
     - exact H1.
  1: destruct B.
     - eapply T_sub with (T := ltt_send pt (fun n => if Nat.eqb n lb then Some (header.Nat,T') else None)).
       + eapply T_send with (B := header.Nat) (T := T').
         * eapply expr_subst_quantum_fresh; eauto.
         * exact (IHP q d T' Gsl Gsr pvc qc H H3).
       + exact H1.
     - eapply T_sub with (T := ltt_send pt (fun n => if Nat.eqb n lb then Some (header.Bool,T') else None)).
       + eapply T_send with (B := header.Bool) (T := T').
         * eapply expr_subst_quantum_fresh; eauto.
         * exact (IHP q d T' Gsl Gsr pvc qc H H3).
       + exact H1.
     - destruct ex as [v|x|op args]; simpl in *.
       + inversion H2; subst.
         unfold in_qubit_context in H6; simpl in H6.
         assert (Hneq : q0 <> q).
         { intro Heq; subst q0. rewrite H in H6. discriminate. }
         assert (Hfresh' : delete (KEQ := qr_dec) qc q0 q = None).
         { rewrite delete_neq; [exact H|exact Hneq]. }
         pose proof (IHP q d T' Gsl Gsr pvc (delete (KEQ := qr_dec) qc q0) Hfresh' H3) as Hcont.
         eapply typecheck_send_fresh_qubit_value; eauto.
       + inversion H2; subst.
         destruct (Nat.ltb x (length Gsl)) eqn:Hx.
         * apply Nat.ltb_lt in Hx.
           simpl.
           unfold remove_from_variable_context in H3; simpl in H3.
           rewrite updn_app1 in H3 by lia.
           eapply T_sub with (T := ltt_send pt (fun n => if Nat.eqb n lb then Some (Qubit,T') else None)).
           -- eapply T_send with (B := Qubit) (T := T').
              ++ econstructor. unfold in_variable_context in *; simpl in *.
                 rewrite app_nth1 in * by lia. eauto.
              ++ unfold remove_from_variable_context; simpl; rewrite updn_app1 by lia.
                 pose proof (IHP q d T' (updn Gsl x None) Gsr pvc qc H H3) as Hcont.
                 rewrite updn_length in Hcont. exact Hcont.
           -- exact H1.
         * destruct (Nat.eqb x (length Gsl)) eqn:Heq.
           -- apply Nat.eqb_eq in Heq; subst x.
              simpl.
              unfold remove_from_variable_context in H3; simpl in H3.
              rewrite updn_app2 in H3 by lia.
              replace (length Gsl - length Gsl) with 0 in H3 by lia.
              simpl in H3.
              eapply T_sub with (T := ltt_send pt (fun n => if Nat.eqb n lb then Some (Qubit,T') else None)).
              ++ eapply T_send with (B := Qubit) (T := T').
                 ** econstructor. unfold in_qubit_context; simpl.
                    unfold insert; simpl. destruct (qr_dec q q); [reflexivity|contradiction].
                 ** eapply typecheck_process_delete_insert_same with (qc := qc) (q := q).
                    --- exact H.
                    --- eapply subst_expression_in_process_unavailable_quantum_slot; exact H3.
              ++ exact H1.
           -- apply Nat.ltb_ge in Hx. apply Nat.eqb_neq in Heq.
              assert (Hgt : length Gsl < x) by lia.
              simpl.
              unfold remove_from_variable_context in H3; simpl in H3.
              rewrite updn_app2 in H3 by lia.
              replace (x - length Gsl) with (S (x - length Gsl - 1)) in H3 by lia.
              simpl in H3.
              eapply T_sub with (T := ltt_send pt (fun n => if Nat.eqb n lb then Some (Qubit,T') else None)).
              ++ eapply T_send with (B := Qubit) (T := T').
                 ** econstructor. unfold in_variable_context in *; simpl in *.
                    rewrite app_nth2 by lia.
                    rewrite app_nth2 in H6 by lia.
                    replace (x - 1 - length Gsl) with (x - length Gsl - 1) by lia.
                    replace (x - length Gsl) with (S (x - length Gsl - 1)) in H6 by lia.
                    simpl in H6. exact H6.
                 ** unfold remove_from_variable_context; simpl; rewrite updn_app2 by lia.
                    replace (x - 1 - length Gsl) with (x - length Gsl - 1) by lia.
                    exact (IHP q d T' Gsl (updn Gsr (x - length Gsl - 1) None) pvc qc H H3).
              ++ exact H1.
       + inversion H2.
  1: eapply T_sub with (T := ltt_recv pt (fun n => onth n lBT)).
     - eapply T_recv. eapply subst_fresh_recv_branches; eauto.
     - exact H2.
  1: eapply T_if.
     - eapply expr_subst_quantum_fresh; eauto.
     - eapply IHP1; eauto.
     - eapply IHP2; eauto.
  1: exfalso. eapply variable_qubit_slot_not_only_refs; eauto.
  1: eapply T_qbit.
     exact (IHP q (S d) T (Some Qubit :: Gsl) Gsr pvc qc H Hx).
  1: eapply T_U.
     - simpl. rewrite length_map. reflexivity.
     - apply Forall_forall. intros z Hz.
       apply in_map_iff in Hz. destruct Hz as [z0 [Hzmap Hzin]].
       subst z.
       assert (Htyped : typecheck_expression
         (pvc, Gsl ++ Some Qubit :: Gsr, qc) z0 Qubit).
       { apply (proj1 (Forall_forall
           (fun z => typecheck_expression
             (pvc, Gsl ++ Some Qubit :: Gsr, qc) z Qubit) lz) H2 z0).
         exact Hzin. }
       eapply expr_subst_quantum_fresh; eauto.
     - eapply subst_expression_quantum_fresh_NoDup; eauto.
     - exact (IHP q d T Gsl Gsr pvc qc H H4).
  1: eapply T_meas.
     - eapply expr_subst_quantum_fresh; eauto.
     - destruct z as [v|x|op args]; simpl in *.
       + destruct v; simpl in *; try solve [inversion H1].
         inversion H1; subst.
         unfold remove_from_qubit_context in H2; simpl in H2.
         unfold in_qubit_context in H5; simpl in H5.
         assert (Hneq : q0 <> q).
         { intro Heq; subst q0. rewrite H in H5. discriminate. }
         assert (Hfresh' : delete (KEQ := qr_dec) qc q0 q = None).
         { rewrite delete_neq; [exact H|exact Hneq]. }
         pose proof (IHP q (S d) T (Some header.Bool :: Gsl) Gsr pvc
           (delete (KEQ := qr_dec) qc q0) Hfresh' H2) as Hcont.
         eapply typecheck_process_delete_insert_comm with
           (qc := qc) (q := q) (r := q0)
           (Gsl := Some header.Bool :: Gsl) (Gsr := Gsr); eauto.
       + inversion H1; subst.
         destruct (Nat.ltb x (length Gsl)) eqn:Hx.
         * apply Nat.ltb_lt in Hx.
           unfold remove_from_variable_context in H2; simpl in H2.
           rewrite updn_app1 in H2 by lia.
           pose proof (IHP q (S d) T
             (Some header.Bool :: updn Gsl x None) Gsr pvc qc H H2) as Hcont.
           simpl in Hcont |- *.
           rewrite updn_length in Hcont.
           unfold remove_measured_expression_from_context,
             remove_from_variable_context in *; simpl in *.
           rewrite updn_app1 by lia.
           exact Hcont.
         * apply Nat.ltb_ge in Hx.
           destruct (Nat.eqb x (length Gsl)) eqn:Heq.
           -- apply Nat.eqb_eq in Heq; subst x.
              unfold remove_from_variable_context in H2; simpl in H2.
              rewrite updn_app2 in H2 by lia.
              replace (length Gsl - length Gsl) with 0 in H2 by lia.
              simpl in H2.
              eapply typecheck_process_delete_insert_same with
                (qc := qc) (q := q) (Gsl := Some header.Bool :: Gsl)
                (Gsr := Gsr).
              ++ exact H.
              ++ eapply subst_expression_in_process_unavailable_quantum_slot.
                 exact H2.
           -- apply Nat.eqb_neq in Heq.
              assert (Hgt : length Gsl < x) by lia.
              unfold remove_from_variable_context in H2; simpl in H2.
              rewrite updn_app2 in H2 by lia.
              replace (x - length Gsl) with
                (S (x - length Gsl - 1)) in H2 by lia.
              simpl in H2.
              pose proof (IHP q (S d) T (Some header.Bool :: Gsl)
                (updn Gsr (x - length Gsl - 1) None) pvc qc H H2) as Hcont.
              unfold remove_measured_expression_from_context,
                remove_from_variable_context in *; simpl in *.
              rewrite updn_app2 by lia.
              replace (x - 1 - length Gsl) with
                (x - length Gsl - 1) by lia.
              exact Hcont.
       + inversion H1.
Qed.


Lemma nth_updn_neq_local : forall A (l : list A) i j (v d : A),
  i <> j -> nth i (updn l j v) d = nth i l d.
Proof.
  induction l as [|a l IH]; intros i j v d Hneq;
    destruct i as [|i], j as [|j]; simpl in *; try reflexivity; try congruence.
  apply IH. lia.
Qed.

Lemma typecheck_expression_classical_qcontext_irrel :
  forall context ex B (qc2 : qubit_context),
    typecheck_expression context ex B ->
    B <> Qubit ->
    typecheck_expression (context.1, qc2) ex B.
Proof.
  intros context ex B qc2 Hty Hneq.
  revert qc2 Hneq.
  induction Hty; intros qc2 Hneq; simpl in *; try contradiction;
    econstructor; eauto.
  all: try solve [eapply IHHty1; discriminate |
    eapply IHHty2; discriminate | eapply IHHty; discriminate].
Qed.

Lemma nth_updn_qubit_other_local :
  forall (vc : variable_context) x y B,
    nth y vc None = Some B ->
    nth x vc None = Some Qubit ->
    B <> Qubit ->
    nth y (updn vc x None) None = Some B.
Proof.
  intros vc x y B Hvar Hq Hneq.
  destruct (Nat.eq_dec x y) as [-> | Hxy].
  - rewrite Hq in Hvar. inversion Hvar; congruence.
  - rewrite nth_updn_neq_local by congruence. exact Hvar.
Qed.

Lemma typecheck_expression_classical_remove_variable :
  forall context ex B removed,
    typecheck_expression context ex B ->
    B <> Qubit ->
    in_variable_context context removed Qubit ->
    typecheck_expression
      (context.1.1, updn context.1.2 removed None, context.2) ex B.
Proof.
  intros context ex B removed Hty Hneq Hslot.
  revert removed Hneq Hslot.
  assert (Hnat : header.Nat <> Qubit) by discriminate.
  assert (Hbool : header.Bool <> Qubit) by discriminate.
  induction Hty; intros removed Hneq Hslot; simpl in *; try contradiction.
  all: try solve [econstructor; eauto using nth_updn_qubit_other_local].
  all: try solve [econstructor; unfold in_variable_context in *; simpl in *;
    eapply nth_updn_qubit_other_local; eauto].
Qed.

Lemma only_qubit_refs_contract_classical :
  forall Gsl Gsr pvc (qc : qubit_context) B,
    only_qubit_references_in_context (pvc, Gsl ++ Some B :: Gsr, qc) ->
    only_qubit_references_in_context (pvc, Gsl ++ Gsr, qc).
Proof.
  intros Gsl Gsr pvc qc B Honly.
  unfold only_qubit_references_in_context in *; simpl in *.
  rewrite Forall_forall in Honly |- *.
  intros s Hin.
  apply Honly.
  apply in_app_or in Hin as [Hin | Hin].
  - apply in_or_app. left. exact Hin.
  - apply in_or_app. right. simpl. right. exact Hin.
Qed.

Lemma subst_expression_classical_qubit_preimage :
  forall z e d B Gsl Gsr pvc (qc : qubit_context),
    B <> Qubit ->
    typecheck_expression (pvc, Gsl ++ Gsr, qc) z Qubit ->
    exists z0,
      typecheck_expression (pvc, Gsl ++ Some B :: Gsr, qc) z0 Qubit /\
      subst_expression (length Gsl) d e z0 = z.
Proof.
  intros z e d B Gsl Gsr pvc qc Hneq Hty.
  destruct z as [v | x | op args].
  - destruct v; inversion Hty; subst.
    exists (Val (Primitives.QVal q)). split; [constructor; assumption|reflexivity].
  - inversion Hty; subst.
    unfold in_variable_context in *; simpl in *.
    destruct (Nat.ltb x (length Gsl)) eqn:Hx.
    + exists (Var x). split.
      * apply Nat.ltb_lt in Hx.
        econstructor. unfold in_variable_context; simpl.
        rewrite app_nth1 in * by lia. assumption.
      * simpl. rewrite Hx. reflexivity.
    + apply Nat.ltb_ge in Hx.
      exists (Var (S x)). split.
      * econstructor. unfold in_variable_context; simpl.
        rewrite app_nth2 by lia.
        rewrite app_nth2 in * by lia.
        replace (S x - length Gsl) with (S (x - length Gsl)) in * by lia.
        simpl in *. assumption.
      * simpl.
        assert (Hlt : Nat.ltb (S x) (length Gsl) = false) by (apply Nat.ltb_ge; lia).
        destruct (length Gsl) as [|m] eqn:Hlen.
        -- simpl. rewrite Nat.sub_0_r. reflexivity.
        -- simpl in *.
           assert (Heq' : Nat.eqb x m = false) by (apply Nat.eqb_neq; lia).
           rewrite Hlt, Heq'. simpl. rewrite Nat.sub_0_r. reflexivity.
  - inversion Hty.
Qed.

Lemma classical_slot_not_qubit_var :
  forall x B Gsl Gsr pvc (qc : qubit_context),
    B <> Qubit ->
    typecheck_expression (pvc, Gsl ++ Some B :: Gsr, qc) (Var x) Qubit ->
    x <> length Gsl.
Proof.
  intros x B Gsl Gsr pvc qc Hneq Hty Heq.
  subst x. inversion Hty; subst.
  unfold in_variable_context in *; simpl in *.
  match goal with
  | Hvar : nth (length Gsl) (Gsl ++ Some B :: Gsr) None = Some Qubit |- _ =>
      rewrite nth_middle in Hvar; inversion Hvar; contradiction
  end.
Qed.

Lemma subst_expression_classical_qubit_injective :
  forall a b e d B Gsl Gsr pvc (qc : qubit_context),
    B <> Qubit ->
    typecheck_expression (pvc, Gsl ++ Some B :: Gsr, qc) a Qubit ->
    typecheck_expression (pvc, Gsl ++ Some B :: Gsr, qc) b Qubit ->
    subst_expression (length Gsl) d e a =
      subst_expression (length Gsl) d e b -> a = b.
Proof.
  intros a b e d B Gsl Gsr pvc qc Hneq Hta Htb Hmap.
  destruct a as [va | x | opa argsa], b as [vb | y | opb argsb].
  - inversion Hta; subst. inversion Htb; subst. simpl in Hmap. inversion Hmap. reflexivity.
  - inversion Hta; subst.
    pose proof (classical_slot_not_qubit_var y B Gsl Gsr pvc qc Hneq Htb) as Hy.
    unfold subst_expression in Hmap; simpl in Hmap.
    assert (Hyeq : Nat.eqb y (length Gsl) = false) by (apply Nat.eqb_neq; exact Hy).
    rewrite Hyeq in Hmap. destruct (Nat.ltb y (length Gsl)); discriminate.
  - inversion Htb.
  - inversion Hta; subst.
    pose proof (classical_slot_not_qubit_var x B Gsl Gsr pvc qc Hneq Hta) as Hx.
    unfold subst_expression in Hmap; simpl in Hmap.
    assert (Hxeq : Nat.eqb x (length Gsl) = false) by (apply Nat.eqb_neq; exact Hx).
    rewrite Hxeq in Hmap. destruct (Nat.ltb x (length Gsl)); discriminate.
  - pose proof (classical_slot_not_qubit_var x B Gsl Gsr pvc qc Hneq Hta) as Hx.
    pose proof (classical_slot_not_qubit_var y B Gsl Gsr pvc qc Hneq Htb) as Hy.
    inversion Hta; subst. inversion Htb; subst.
    unfold subst_expression in Hmap; simpl in Hmap.
    assert (Hxeq : Nat.eqb x (length Gsl) = false) by (apply Nat.eqb_neq; exact Hx).
    assert (Hyeq : Nat.eqb y (length Gsl) = false) by (apply Nat.eqb_neq; exact Hy).
    rewrite Hxeq, Hyeq in Hmap.
    destruct (Nat.ltb x (length Gsl)) eqn:Hxlt;
      destruct (Nat.ltb y (length Gsl)) eqn:Hylt;
      simpl in Hmap; inversion Hmap; f_equal;
      apply Nat.ltb_lt in Hxlt || apply Nat.ltb_ge in Hxlt;
      apply Nat.ltb_lt in Hylt || apply Nat.ltb_ge in Hylt; lia.
  - inversion Htb.
  - inversion Hta.
  - inversion Hta.
  - inversion Hta.
Qed.

Lemma subst_expression_classical_qubit_NoDup :
  forall lz e d B Gsl Gsr pvc (qc : qubit_context),
    B <> Qubit ->
    Forall (fun z => typecheck_expression
      (pvc, Gsl ++ Some B :: Gsr, qc) z Qubit) lz ->
    NoDup lz ->
    NoDup (map (subst_expression (length Gsl) d e) lz).
Proof.
  intros lz e d B Gsl Gsr pvc qc Hneq Htyped Hnd.
  induction Hnd as [|a lz Hnot Hnd IH]; inversion Htyped; subst; simpl.
  - constructor.
  - constructor.
    + intro Hin. apply in_map_iff in Hin. destruct Hin as [b [Heq Hin]].
      assert (Hba : a = b).
      { eapply subst_expression_classical_qubit_injective with
          (a := a) (b := b) (e := e) (d := d) (B := B)
          (Gsl := Gsl) (Gsr := Gsr) (pvc := pvc) (qc := qc).
        - exact Hneq.
        - exact H1.
        - apply Forall_forall with (x := b) in H2; assumption.
        - symmetry. exact Heq. }
      apply Hnot. subst b. exact Hin.
    + apply IH. assumption.
Qed.

Lemma Slength_smap_local :
  forall A C (f : A -> C) (xs : slist A),
    Slength (smap f xs) = Slength xs.
Proof.
  intros A C f xs. induction xs; simpl; auto.
  destruct o; simpl; auto.
Qed.

Lemma subst_expression_in_process_helper_classical : forall P e d B T Gsl Gsr pvc qc,
  typecheck_process (pvc, Gsl ++ Some B :: Gsr, qc)  P T ->
  typecheck_expression (pvc, Gsl ++ Gsr, qc)  (incr_free_expression 0 d e) B ->
  B <> Qubit ->
  typecheck_process (pvc, Gsl ++ Gsr, qc) (subst_expression_in_process (length Gsl) d e P) T.
Proof.
  induction P using process_deep_ind; simpl; intros;
    revert H1; invert_typecheck; cleanup; intros Hlinear; simpl in *; eauto.
  1: assert (Hlist : forall z,
       In z (map (subst_expression (length Gsl) d e) lz) <->
       typecheck_expression (pvc, Gsl ++ Gsr, qc) z Qubit).
     { intros z; split.
       - intro Hin. apply in_map_iff in Hin. destruct Hin as [z0 [Hz Hzin]].
         apply H4 in Hzin. rewrite <- Hz. eapply expr_subst; eauto.
       - intro Hzt.
         destruct (subst_expression_classical_qubit_preimage z e d B Gsl Gsr pvc qc
           Hlinear Hzt) as [z0 [Hz0 Hz]].
         apply in_map_iff. exists z0. split; [exact Hz|apply H4; exact Hz0]. }
     assert (Htyped_lz : Forall
       (fun z => typecheck_expression (pvc, Gsl ++ Some B :: Gsr, qc) z Qubit) lz).
     { apply Forall_forall. intros z Hz. apply H4. exact Hz. }
     assert (Hnd : NoDup (map (subst_expression (length Gsl) d e) lz)).
     { eapply subst_expression_classical_qubit_NoDup; eauto. }
     eapply T_sub with (T := T').
     - eapply T_var with (qcontext := qcontext)
         (lz := map (subst_expression (length Gsl) d e) lz).
       + exact H1.
       + eapply only_qubit_refs_contract_classical; exact H2.
       + exact H3.
       + exact Hlist.
       + exact Hnd.
     - exact H6.
  1: eapply T_sub with (T := ltt_end).
     - eapply T_end.
       + intros z; split.
         * intro Hin. apply in_map_iff in Hin. destruct Hin as [z0 [Hz Hzin]].
           apply H2 in Hzin.
           rewrite <- Hz. eapply expr_subst; eauto.
         * intro Hzt.
           destruct (subst_expression_classical_qubit_preimage z e d B Gsl Gsr pvc qc Hlinear Hzt)
             as [z0 [Hz0 Hz]].
           apply in_map_iff. exists z0. split; [exact Hz|]. apply H2. exact Hz0.
       + assert (Htyped : Forall (fun z0 =>
           typecheck_expression (pvc, Gsl ++ Some B :: Gsr, qc) z0 Qubit) lz).
         { apply Forall_forall. intros z0 Hzin. apply H2. exact Hzin. }
         eapply subst_expression_classical_qubit_NoDup with
           (e := e) (d := d) (B := B) (Gsl := Gsl) (Gsr := Gsr)
           (pvc := pvc) (qc := qc); eauto.
     - exact H1.
  1: eapply T_sub with (T := ltt_send pt
       (fun n => if Nat.eqb n lb then Some (B0, T') else None)).
     - eapply T_send with (B := B0) (T := T').
       + eapply expr_subst; eauto.
       + destruct B0; simpl in *.
         * eapply IHP; eauto.
         * eapply IHP; eauto.
         * destruct ex as [v | x | op args]; simpl in *.
           -- destruct v; simpl in *; try solve [inversion H2].
              inversion H2; subst.
              assert (H0qc : typecheck_expression
                (pvc, Gsl ++ Gsr, delete (KEQ := qr_dec) qc q)
                (incr_free_expression 0 d e) B).
              { eapply typecheck_expression_classical_qcontext_irrel
                  with (context := (pvc, Gsl ++ Gsr, qc)) (qc2 := delete (KEQ := qr_dec) qc q).
                - exact H0.
                - exact Hlinear. }
              change (typecheck_process
                (pvc, Gsl ++ Some B :: Gsr, delete (KEQ := qr_dec) qc q) P T') in H3.
              eapply IHP with (e := e) (d := d) (B := B) (T := T')
                (Gsl := Gsl) (Gsr := Gsr) (pvc := pvc)
                (qc := delete (KEQ := qr_dec) qc q).
              ** exact H3.
              ** exact H0qc.
              ** exact Hlinear.
           -- assert (Hvar : in_variable_context
                (pvc, Gsl ++ Some B :: Gsr, qc) x Qubit).
              { inversion H2; assumption. }
              pose proof (classical_slot_not_qubit_var x B Gsl Gsr pvc qc Hlinear H2) as Hxneq.
              destruct (Nat.ltb x (length Gsl)) eqn:Hx.
              ++ apply Nat.ltb_lt in Hx.
                 assert (Hslot : in_variable_context (pvc, Gsl ++ Gsr, qc) x Qubit).
                 { unfold in_variable_context. simpl.
                   unfold in_variable_context in Hvar. simpl in Hvar.
                   rewrite app_nth1 in Hvar by lia.
                   rewrite app_nth1 by lia. exact Hvar. }
                 assert (H0rem : typecheck_expression
                   (pvc, updn (Gsl ++ Gsr) x None, qc)
                   (incr_free_expression 0 d e) B).
                 { eapply typecheck_expression_classical_remove_variable
                     with (context := (pvc, Gsl ++ Gsr, qc)) (removed := x).
                   - exact H0.
                   - exact Hlinear.
                   - exact Hslot. }
                 unfold remove_from_variable_context; simpl.
                 rewrite updn_app1 by lia.
                 unfold remove_from_variable_context in H3; simpl in H3.
                 rewrite updn_app1 in H3 by lia.
                 rewrite updn_app1 in H0rem by lia.
                 rewrite <- (updn_length Gsl x None).
                 eapply IHP with (e := e) (d := d) (B := B) (T := T')
                   (Gsl := updn Gsl x None) (Gsr := Gsr) (pvc := pvc) (qc := qc).
                 ** exact H3.
                 ** exact H0rem.
                 ** exact Hlinear.
              ++ apply Nat.ltb_ge in Hx.
                 assert (Hgt : length Gsl < x) by lia.
                 assert (Hslot : in_variable_context (pvc, Gsl ++ Gsr, qc) (x - 1) Qubit).
                 { unfold in_variable_context. simpl.
                   unfold in_variable_context in Hvar. simpl in Hvar.
                   rewrite app_nth2 in Hvar by lia.
                   rewrite app_nth2 by lia.
                   replace (x - length Gsl) with (S (x - length Gsl - 1)) in Hvar by lia.
                   simpl in Hvar.
                   replace (x - 1 - length Gsl) with (x - length Gsl - 1) by lia.
                   exact Hvar. }
                 assert (H0rem : typecheck_expression
                   (pvc, updn (Gsl ++ Gsr) (x - 1) None, qc)
                   (incr_free_expression 0 d e) B).
                 { eapply typecheck_expression_classical_remove_variable
                     with (context := (pvc, Gsl ++ Gsr, qc)) (removed := x - 1).
                   - exact H0.
                   - exact Hlinear.
                   - exact Hslot. }
                 unfold subst_expression; simpl.
                 assert (Heqx : Nat.eqb x (length Gsl) = false) by (apply Nat.eqb_neq; lia).
                 rewrite Heqx. simpl.
                 unfold remove_from_variable_context; simpl.
                 rewrite updn_app2 by lia.
                 replace (x - 1 - length Gsl) with (x - length Gsl - 1) by lia.
                 replace (x - length Gsl) with (S (x - length Gsl - 1)) by lia.
                 simpl.
                 replace (x - length Gsl - 1 - 0) with (x - length Gsl - 1) by lia.
                 unfold remove_from_variable_context in H3; simpl in H3.
                 rewrite updn_app2 in H3 by lia.
                 replace (x - length Gsl) with (S (x - length Gsl - 1)) in H3 by lia.
                 simpl in H3.
                 rewrite updn_app2 in H0rem by lia.
                 replace (x - 1 - length Gsl) with (x - length Gsl - 1) in H0rem by lia.
                 eapply IHP with (e := e) (d := d) (B := B) (T := T')
                   (Gsl := Gsl) (Gsr := updn Gsr (x - length Gsl - 1) None)
                   (pvc := pvc) (qc := qc).
                 ** exact H3.
                 ** exact H0rem.
                 ** exact Hlinear.
           -- inversion H2.
     - exact H1.
  1: eapply T_sub with (T := ltt_recv pt (fun n => onth n lBT)).
     - eapply T_recv.
       pose proof (proj2 (SForall_forall _ _ llp) H) as Hih.
       pose proof (proj2 (SForall2_forall _ _ _ llp lBT) H3) as Hshape.
       destruct Hshape as [Hpair [Hnone Hlen]].
       set (f := subst_expression_in_process (S (length Gsl)) (S d) e).
       apply (proj1 (SForall2_forall _ _ _ (smap f llp) lBT)).
       split.
       + intros n P0 BT Hpn HBn.
         destruct (onth_move_out n f llp P0 Hpn) as [P1 [HP1 Hf]].
         subst P0.
         destruct BT as [B0 T0]; simpl in *.
         specialize (Hih n P1 HP1).
         specialize (Hpair n P1 (B0, T0) HP1 HBn) as Horig.
         eapply Hih with (e := e) (d := S d) (B := B) (T := T0)
           (Gsl := Some B0 :: Gsl) (Gsr := Gsr) (pvc := pvc) (qc := qc).
         * exact Horig.
         * simpl. apply slideE. exact Hlinear.
         * exact H2.
       + split.
         * intros n. split; intro Hnone'.
           -- assert (Hsrc : onth n llp = None).
              { destruct (onth n llp) as [P0|] eqn:Hsrc; [|reflexivity].
                exfalso. pose proof (onth_move_in process process f llp n P0 Hsrc). cleanup. }
              apply (proj1 (Hnone n)). exact Hsrc.
           -- apply (proj2 (Hnone n)) in Hnone'.
              destruct (onth n (smap f llp)) as [P0|] eqn:Hdest; [|reflexivity].
              exfalso. destruct (onth_move_out n f llp P0 Hdest) as [P1 [HP1 _]].
              congruence.
         * rewrite Slength_smap_local. exact Hlen.
     - exact H1.
  1: eapply T_if.
     - eapply expr_subst; eauto.
     - eapply IHP1; eauto.
     - eapply IHP2; eauto.
  1: eapply T_sub with (T := T').
     - eapply T_rec.
       + assert (H0rec : typecheck_expression
           (Some (T', qc) :: pvc, Gsl ++ Gsr, qc)
           (incr_free_expression 0 d e) B).
         { eapply typecheck_expression_equivalent.
           - exact H0.
           - reflexivity.
           - apply equivalent_refl. }
         change (typecheck_process
           (Some (T', qc) :: pvc, Gsl ++ Some B :: Gsr, qc) P T') in H1.
         eapply IHP with (e := e) (d := d) (B := B) (T := T')
           (Gsl := Gsl) (Gsr := Gsr) (pvc := Some (T', qc) :: pvc) (qc := qc).
         * exact H1.
         * exact H0rec.
         * exact Hlinear.
       + eapply only_qubit_refs_contract_classical; exact H2.
     - exact H3.
  1: eapply T_qbit.
     assert (Hshift : typecheck_expression
       (pvc, Some Qubit :: Gsl ++ Gsr, qc)
       (incr_free_expression 0 (S d) e) B).
     { apply slideE. exact H0. }
     eapply IHP with (e := e) (d := S d) (B := B) (T := T)
       (Gsl := Some Qubit :: Gsl) (Gsr := Gsr) (pvc := pvc) (qc := qc);
       simpl in *; eauto.
  1: eapply T_U.
     - simpl. rewrite length_map. reflexivity.
     - apply Forall_forall. intros z Hz.
       apply in_map_iff in Hz. destruct Hz as [z0 [Hz Hzin]].
       rewrite <- Hz. apply Forall_forall with (x := z0) in H2.
       + eapply expr_subst; eauto.
       + exact Hzin.
     - eapply subst_expression_classical_qubit_NoDup; eauto.
     - eapply IHP; eauto.
  1: eapply T_meas.
     - eapply expr_subst; eauto.
     - assert (Hshift : typecheck_expression
         (pvc, Some header.Bool :: Gsl ++ Gsr, qc)
         (incr_free_expression 0 (S d) e) B).
       { apply slideE. exact H0. }
       destruct z as [v|x|op args]; simpl in *.
       + destruct v; simpl in *; try solve [inversion H1].
         inversion H1; subst.
         assert (H0qc : typecheck_expression
           (pvc, Some header.Bool :: Gsl ++ Gsr,
             delete (KEQ := qr_dec) qc q)
           (incr_free_expression 0 (S d) e) B).
         { eapply typecheck_expression_classical_qcontext_irrel
             with (context := (pvc, Some header.Bool :: Gsl ++ Gsr, qc))
                  (qc2 := delete (KEQ := qr_dec) qc q).
           - exact Hshift.
           - exact Hlinear. }
         unfold remove_from_qubit_context in H2; simpl in H2.
         change (typecheck_process
           (pvc, Some header.Bool :: Gsl ++ Some B :: Gsr,
             delete (KEQ := qr_dec) qc q) P T) in H2.
         eapply IHP with (e := e) (d := S d) (B := B) (T := T)
           (Gsl := Some header.Bool :: Gsl) (Gsr := Gsr)
           (pvc := pvc) (qc := delete (KEQ := qr_dec) qc q).
         * exact H2.
         * exact H0qc.
         * exact Hlinear.
       + assert (Hvar : in_variable_context
           (pvc, Gsl ++ Some B :: Gsr, qc) x Qubit).
         { inversion H1; assumption. }
         pose proof (classical_slot_not_qubit_var x B Gsl Gsr pvc qc
           Hlinear H1) as Hxneq.
         destruct (Nat.ltb x (length Gsl)) eqn:Hx.
         * apply Nat.ltb_lt in Hx.
           assert (Hslot : in_variable_context
             (pvc, Some header.Bool :: Gsl ++ Gsr, qc) (S x) Qubit).
           { unfold in_variable_context in *; simpl in *.
             rewrite app_nth1 in Hvar by lia.
             simpl. rewrite app_nth1 by lia. exact Hvar. }
           assert (H0rem : typecheck_expression
             (pvc, updn (Some header.Bool :: Gsl ++ Gsr) (S x) None, qc)
             (incr_free_expression 0 (S d) e) B).
           { eapply typecheck_expression_classical_remove_variable
               with (context := (pvc, Some header.Bool :: Gsl ++ Gsr, qc))
                    (removed := S x).
             - exact Hshift.
             - exact Hlinear.
             - exact Hslot. }
           unfold remove_from_variable_context in H2; simpl in H2.
           rewrite updn_app1 in H2 by lia.
           simpl in H0rem.
           rewrite updn_app1 in H0rem by lia.
           pose proof (IHP e (S d) B T
             (Some header.Bool :: updn Gsl x None) Gsr pvc qc
             H2 H0rem Hlinear) as Hcont.
           simpl in Hcont |- *.
           rewrite updn_length in Hcont.
           unfold remove_measured_expression_from_context,
             remove_from_variable_context in *; simpl in *.
           rewrite updn_app1 by lia.
           exact Hcont.
         * apply Nat.ltb_ge in Hx.
           assert (Hxgt : length Gsl < x) by lia.
           assert (Hslot : in_variable_context
             (pvc, Some header.Bool :: Gsl ++ Gsr, qc) (S (x - 1)) Qubit).
           { unfold in_variable_context in *; simpl in *.
             rewrite app_nth2 in Hvar by lia.
             replace (x - length Gsl) with
               (S (x - length Gsl - 1)) in Hvar by lia.
             simpl in Hvar.
             rewrite app_nth2 by lia.
             replace (x - 1 - length Gsl) with
               (x - length Gsl - 1) by lia.
             exact Hvar. }
           assert (H0rem : typecheck_expression
             (pvc, updn (Some header.Bool :: Gsl ++ Gsr) (S (x - 1)) None, qc)
             (incr_free_expression 0 (S d) e) B).
           { eapply typecheck_expression_classical_remove_variable
               with (context := (pvc, Some header.Bool :: Gsl ++ Gsr, qc))
                    (removed := S (x - 1)).
             - exact Hshift.
             - exact Hlinear.
             - exact Hslot. }
           unfold remove_from_variable_context in H2; simpl in H2.
           rewrite updn_app2 in H2 by lia.
           replace (x - length Gsl) with
             (S (x - length Gsl - 1)) in H2 by lia.
           simpl in H2.
           simpl in H0rem.
           rewrite updn_app2 in H0rem by lia.
           replace (x - 1 - length Gsl) with
             (x - length Gsl - 1) in H0rem by lia.
           replace (S (x - 1) - S (length Gsl)) with
             (x - length Gsl - 1) in H0rem by lia.
           pose proof (IHP e (S d) B T (Some header.Bool :: Gsl)
             (updn Gsr (x - length Gsl - 1) None) pvc qc
             H2 H0rem Hlinear) as Hcont.
           assert (Hltb : Nat.ltb x (length Gsl) = false)
             by (apply Nat.ltb_ge; lia).
           assert (Heqx : Nat.eqb x (length Gsl) = false)
             by (apply Nat.eqb_neq; exact Hxneq).
           try rewrite Hltb in *.
           try rewrite Heqx in *.
           simpl in *.
           unfold remove_measured_expression_from_context,
             remove_from_variable_context in *; simpl in *.
           rewrite updn_app2 by lia.
           replace (x - 1 - length Gsl) with
             (x - length Gsl - 1) by lia.
           exact Hcont.
       + inversion H1.
Qed.

Lemma subst_expression_in_process_classical : forall P e d B T Gsr pvc qc,
  typecheck_process (pvc, Some B :: Gsr, qc)  P T ->
  typecheck_expression (pvc, Gsr, qc)  (incr_free_expression 0 d e) B ->
  B <> Qubit ->
  typecheck_process (pvc, Gsr, qc) (subst_expression_in_process 0 d e P) T.
Proof.
  intros; eapply(subst_expression_in_process_helper_classical _ _ _ _ _ nil); simpl; eauto.
Qed.

Lemma subst_expression_in_process_quantum :
  forall P q d T Gsr pvc (qc: qubit_context),
    qc q = None ->
    typecheck_process
      (pvc, Some Qubit :: Gsr, qc) P T ->
    typecheck_process
      (pvc, Gsr, insert (KEQ := qr_dec) qc q tt)
      (subst_expression_in_process
        0 d (Val (QVal q)) P) T.
Proof.
  intros; eapply(subst_expression_in_process_helper_quantum _ _ _ _ nil); simpl; eauto.
Qed.



Lemma nth_not_qubit_of_forall : forall vc,
    Forall (fun s : option sort => s <> Some Qubit) vc ->
    forall n, nth n vc None <> Some Qubit.
Proof.
    intros vc Hvc.
    induction Hvc as [|s vc Hs Hvc IH]; intros [|n]; simpl.
    - discriminate.
    - discriminate.
    - exact Hs.
    - apply IH.
Qed.

Lemma recursion_typechecking_context_lift :
    forall P T qc pc vc,
    typecheck_process (pc, vc, qc) (p_rec P) T ->
    Forall (fun s : option sort => s <> Some Qubit) vc ->
    forall pc' vc',
    Forall (fun s : option sort => s <> Some Qubit) vc' ->
    typecheck_process (pc' ++ pc, vc' ++ vc, qc)
        (incr_free 0 0 (length pc') (length vc') (p_rec P)) T.
Proof.
    intros P T qc pc vc Hrec Hvc pc' vc' Hvc'.
    assert (Hclass : forall vc',
      Forall (fun s : option sort => s <> Some Qubit) vc' ->
      typecheck_process (pc, vc' ++ vc, qc)
        (incr_free 0 0 0 (length vc') (p_rec P)) T).
    {
      intros vcExtra HvcExtra.
      induction vcExtra as [|s vcExtra IH].
      - simpl.
        rewrite (trivial_incr P 1 0).
        exact Hrec.
      - inversion HvcExtra; subst.
        eapply slideSp with (Q:=p_rec P) (X:=0)
            (m:=length vcExtra) (l:=0) (Gsl:=nil) (Gsr:=vcExtra ++ vc)
            (pvc:=pc) (qc:=qc) (tm:=s).
        + apply IH; assumption.
        + assumption.
    }
    induction pc' as [|entry pc' IH].
    - simpl. apply Hclass; assumption.
    - simpl.
      eapply slideT with (Q:=p_rec P) (X:=length pc')
          (tm:=entry) (Gt:=pc' ++ pc) (cvc:=vc' ++ vc)
          (qvc:=qc) (T:=T) (m:=length vc').
      apply IH; assumption.
Qed.

Lemma typecheck_rec_substitution_induction :
    forall P T qc pc vc,
    (Forall (fun s : option sort => s <> Some Qubit) vc) ->
    (forall Gpre cpre,
      Forall (fun s : option sort => s <> Some Qubit) cpre ->
      typecheck_process (Gpre ++ pc, cpre ++ vc, qc)
        (incr_free 0 0 (length Gpre) (length cpre) (p_rec P)) T) ->
    forall ctx Q T',
    typecheck_process ctx Q T' ->
    forall Gpre cpre qc',
    ctx = (Gpre ++ (Some (T, qc) :: pc), cpre ++ vc, qc') ->
    included qc' qc ->
    typecheck_process (Gpre ++ pc, cpre ++ vc, qc')
      (substitutionP (length Gpre) (length Gpre) (length cpre) (p_rec P) Q) T'.
Proof.
    intros P T qc pc vc Hvc Hlift.
    intros ctx Q T' Htyped.
    apply (typecheck_process_deep_ind
        (fun ctx Q T' => forall Gpre cpre qc',
          ctx = (Gpre ++ (Some (T, qc) :: pc), cpre ++ vc, qc') ->
          included qc' qc ->
          typecheck_process (Gpre ++ pc, cpre ++ vc, qc')
            (substitutionP (length Gpre) (length Gpre) (length cpre)
              (p_rec P) Q) T')).
    - intros cxt Q0 T0 Hq IH Gpre cpre qc' Hctx Hinc.
      subst cxt; simpl in *.
      eapply T_qbit.
      eapply IH with (Gpre:=Gpre) (cpre:=Some Qubit :: cpre) (qc':=qc').
      + reflexivity.
      + exact Hinc.
    - intros cxt z Q0 T0 Hz Hq IH Gpre cpre qc' Hctx Hinc.
      subst cxt; simpl in *.
      eapply T_meas.
      + eapply typecheck_expression_equivalent with
            (theta1:=(Gpre ++ (Some (T, qc) :: pc), cpre ++ vc, qc'))
            (theta2:=(Gpre ++ pc, cpre ++ vc, qc')).
        * exact Hz.
        * reflexivity.
        * apply equivalent_refl.
      +
      destruct z as [v|x|op args]; simpl in *.
      + destruct v; simpl in *; try solve [inversion Hz].
        inversion Hz; subst.
        eapply IH with (Gpre:=Gpre) (cpre:=Some header.Bool :: cpre)
          (qc':=delete (KEQ:=qr_dec) qc' q).
        * reflexivity.
        * unfold included in *; intros k value Hlookup.
          destruct (qr_dec q k) as [Heq|Hneq].
          -- subst k. rewrite delete_eq in Hlookup. discriminate.
          -- rewrite delete_neq in Hlookup by exact Hneq.
             eapply Hinc; eauto.
      + assert (Hslot : nth x (cpre ++ vc) None = Some Qubit).
        { inversion Hz; assumption. }
        inversion Hz; subst.
        assert (Hxpre : x < length cpre).
        {
          destruct (Nat.lt_ge_cases x (length cpre)); [assumption|].
          rewrite app_nth2 in Hslot by lia.
          exfalso.
          eapply (nth_not_qubit_of_forall vc Hvc (x - length cpre)).
          exact Hslot.
        }
        unfold remove_measured_expression_from_context,
          remove_from_variable_context in *; simpl in *.
        rewrite updn_app1 by exact Hxpre.
        rewrite updn_app1 in IH by exact Hxpre.
        replace (S (length cpre)) with
          (length (Some header.Bool :: updn cpre x None))
          by (simpl; rewrite updn_length; reflexivity).
        eapply IH with (Gpre:=Gpre)
          (cpre:=Some header.Bool :: updn cpre x None)
          (qc':=qc').
        * reflexivity.
        * exact Hinc.
      + inversion Hz.
    - intros cxt dim U lz Q0 T0 Hlen Hl Hnd Hq IH Gpre cpre qc' Hctx Hinc.
      subst cxt; simpl in *.
      eapply T_U.
      + exact Hlen.
      + apply Forall_forall; intros z Hz.
        apply Forall_forall with (x:=z) in Hl; [|exact Hz].
        eapply typecheck_expression_equivalent with
            (theta1:=(Gpre ++ (Some (T, qc) :: pc), cpre ++ vc, qc'))
            (theta2:=(Gpre ++ pc, cpre ++ vc, qc')).
        * exact Hl.
        * reflexivity.
        * apply equivalent_refl.
      + exact Hnd.
      +
      eapply IH with (Gpre:=Gpre) (cpre:=cpre)
        (qc':=qc').
      + reflexivity.
      + exact Hinc.
    - intros cxt lz Htyped_end Hnd Gpre cpre qc' Hctx Hinc.
      subst cxt; simpl in *.
      eapply T_end.
      + intros z; split; intro Hz.
        * apply Htyped_end in Hz.
          eapply typecheck_expression_equivalent with
              (theta1:=(Gpre ++ (Some (T, qc) :: pc), cpre ++ vc, qc'))
              (theta2:=(Gpre ++ pc, cpre ++ vc, qc')).
          -- exact Hz.
          -- reflexivity.
          -- apply equivalent_refl.
        * apply Htyped_end.
          eapply typecheck_expression_equivalent with
              (theta1:=(Gpre ++ pc, cpre ++ vc, qc'))
              (theta2:=(Gpre ++ (Some (T, qc) :: pc), cpre ++ vc, qc')).
          -- exact Hz.
          -- reflexivity.
          -- apply equivalent_refl.
      + exact Hnd.
    - intros cxt pt e Q0 lb B T1 He Hq IH Gpre cpre qc' Hctx Hinc.
      subst cxt; simpl in *.
      eapply T_send with (B:=B) (T:=T1).
      + eapply typecheck_expression_equivalent with
            (theta1:=(Gpre ++ (Some (T, qc) :: pc), cpre ++ vc, qc'))
            (theta2:=(Gpre ++ pc, cpre ++ vc, qc')).
        * exact He.
        * reflexivity.
        * apply equivalent_refl.
      + destruct B; simpl in *; try (eapply IH; [reflexivity|exact Hinc]).
        destruct e as [v|x|op args]; simpl in *.
        * destruct v; simpl in *; try solve [inversion He].
          eapply IH with (Gpre:=Gpre) (cpre:=cpre)
              (qc':=delete qc' q).
          -- reflexivity.
          -- unfold included in *; intros q0 v0 Hdel.
             apply Hinc.
             destruct (qr_dec q q0); subst.
             ++ rewrite delete_eq in Hdel; discriminate.
             ++ rewrite delete_neq in Hdel by assumption; exact Hdel.
        * assert (Hslot : nth x (cpre ++ vc) None = Some Qubit).
          { inversion He; assumption. }
          assert (Hxpre : x < length cpre).
          {
            destruct (Nat.lt_ge_cases x (length cpre)); [assumption|].
            rewrite app_nth2 in Hslot by lia.
            exfalso.
            eapply (nth_not_qubit_of_forall vc Hvc (x - length cpre)).
            exact Hslot.
          }
          unfold remove_from_variable_context; simpl.
          rewrite updn_app1 by exact Hxpre.
          rewrite <- (updn_length cpre x None).
          eapply IH with (Gpre:=Gpre)
            (cpre:=updn cpre x None) (qc':=qc').
          -- unfold remove_from_variable_context; simpl.
             rewrite updn_app1 by exact Hxpre. reflexivity.
          -- exact Hinc.
        * inversion He.
    - intros cxt pt lP lBT Hshape Hih Gpre cpre qc' Hctx Hinc.
      subst cxt; simpl in *.
      pose proof (proj2 (SForall2_forall _ _ _ lP lBT) Hshape)
          as [Hpair [Hnone Hlen]].
      pose proof (proj2 (SForall2_forall _ _ _ lP lBT) Hih)
          as [Hihpair [Hihnone Hihlen]].
      set (f := substitutionP (length Gpre) (length Gpre)
          (S (length cpre)) (p_rec P)).
      eapply T_recv.
      apply (proj1 (SForall2_forall _ _ _ (smap f lP) lBT)).
      split.
      + intros n P0 BT Hpn Hbtn.
        destruct (onth_move_out n f lP P0 Hpn) as [P1 [HP1 Hf]].
        destruct BT as [B0 T0]; simpl in *.
        specialize (Hpair n P1 (B0, T0) HP1 Hbtn) as Htyped_branch.
        specialize (Hihpair n P1 (B0, T0) HP1 Hbtn) as Hih_branch.
        assert (Hctx_branch :
            insert_into_variable_context
              (Gpre ++ (Some (T, qc) :: pc), cpre ++ vc, qc') B0 =
            (Gpre ++ (Some (T, qc) :: pc), Some B0 :: cpre ++ vc, qc')).
        { reflexivity. }
        specialize (Hih_branch Gpre (Some B0 :: cpre) qc'
            Hctx_branch Hinc).
        subst P0.
        exact Hih_branch.
      + split.
        * intros n; split; intro Hnone'.
          -- destruct (onth n lP) as [P0|] eqn:Hsrc.
             ++
             exfalso.
             pose proof (onth_move_in process process f lP n P0 Hsrc) as Hdest.
             rewrite Hdest in Hnone'; discriminate.
             ++ apply (proj1 (Hnone n)); exact Hsrc.
          -- destruct (onth n (smap f lP)) as [P0|] eqn:Hdest; [|reflexivity].
             exfalso.
             destruct (onth_move_out n f lP P0 Hdest) as [P1 [Hsrc _]].
             apply (proj2 (Hnone n)) in Hnone'.
             congruence.
        * rewrite Slength_smap_local; exact Hlen.
    - intros cxt e P1 P0 T0 He Hbranch1 IH1 Hbranch2 IH2 Gpre cpre qc' Hctx Hinc.
      subst cxt; simpl in *.
      eapply T_if.
      + eapply typecheck_expression_equivalent with
            (theta1:=(Gpre ++ (Some (T, qc) :: pc), cpre ++ vc, qc'))
            (theta2:=(Gpre ++ pc, cpre ++ vc, qc')).
        * exact He.
        * reflexivity.
        * apply equivalent_refl.
      + eapply IH1 with (Gpre:=Gpre) (cpre:=cpre)
          (qc':=qc').
        * reflexivity.
        * exact Hinc.
      + eapply IH2 with (Gpre:=Gpre) (cpre:=cpre)
          (qc':=qc').
        * reflexivity.
        * exact Hinc.
    - intros cxt Q0 T0 Hq IH Honly Gpre cpre qc' Hctx Hinc.
      subst cxt; simpl in *.
      eapply T_rec.
      + eapply IH with (Gpre:=Some (T0, qc') :: Gpre)
            (cpre:=cpre) (qc':=qc').
        * simpl; reflexivity.
        * exact Hinc.
      + exact Honly.
    - intros cxt qctx X lz T0 Hvar_ctx Honly Hvarinc Hlist Hnd
        Gpre cpre qc' Hctx Hinc.
      subst cxt; simpl in *.
      unfold in_process_context in Hvar_ctx; simpl in Hvar_ctx.
      unfold only_qubit_references_in_context in Honly; simpl in Honly.
      destruct (lt_dec X (length Gpre)) as [Hlt|Hge].
      + assert (Hfound : nth X Gpre None = Some (T0, qctx)).
        { rewrite app_nth1 in Hvar_ctx by exact Hlt; exact Hvar_ctx. }
        assert (Hlist' : forall z,
          In z lz <->
            typecheck_expression (Gpre ++ pc, cpre ++ vc, qc') z Qubit).
        {
          intros z; split; intros Hz.
          - apply Hlist in Hz.
            eapply typecheck_expression_equivalent; [exact Hz|reflexivity|apply equivalent_refl].
          - apply Hlist.
            eapply typecheck_expression_equivalent with
              (theta1 := (Gpre ++ pc, cpre ++ vc, qc'))
              (theta2 := (Gpre ++ (Some (T, qc) :: pc), cpre ++ vc, qc'));
              [exact Hz|reflexivity|apply equivalent_refl].
        }
        assert (Hltb : Nat.ltb X (length Gpre) = true).
        { apply Nat.ltb_lt; exact Hlt. }
        simpl [substitutionP]; rewrite Hltb.
        eapply T_var with (qcontext := qctx) (lz := lz).
        * unfold in_process_context; simpl.
          rewrite app_nth1 by exact Hlt.
          exact Hfound.
        * exact Honly.
        * exact Hvarinc.
        * exact Hlist'.
        * exact Hnd.
      + destruct (Nat.eq_dec X (length Gpre)) as [Heq|Hneq].
        * rewrite Heq in Hvar_ctx.
          rewrite app_nth2 in Hvar_ctx by lia.
          replace (length Gpre - length Gpre) with 0 in Hvar_ctx by lia.
          simpl in Hvar_ctx; inversion Hvar_ctx; subst T0 qctx.
          assert (Hltb : Nat.ltb X (length Gpre) = false)
              by (apply Nat.ltb_ge; lia).
          assert (Heqb : Nat.eqb X (length Gpre) = true)
              by (apply Nat.eqb_eq; exact Heq).
          simpl [substitutionP]; rewrite Hltb, Heqb.
          assert (Hcpre : Forall
              (fun s : option sort => s <> Some Qubit) cpre).
          { apply List.Forall_app in Honly as [Hcpre HvcLocal]; exact Hcpre. }
          eapply typecheck_process_equivalent with
              (theta1:=(Gpre ++ pc, cpre ++ vc, qc))
              (theta2:=(Gpre ++ pc, cpre ++ vc, qc')).
          -- apply Hlift; exact Hcpre.
          -- reflexivity.
          -- apply process_context_equivalent_refl.
          -- exact Hvarinc.
        * assert (Hgt : length Gpre < X) by lia.
          rewrite app_nth2 in Hvar_ctx by lia.
          replace (X - length Gpre) with
            (S (X - length Gpre - 1)) in Hvar_ctx by lia.
          simpl in Hvar_ctx.
          assert (Hfound_tail :
            nth (X - length Gpre - 1) pc None = Some (T0, qctx)).
          { exact Hvar_ctx. }
          assert (Hlist' : forall z,
            In z lz <->
              typecheck_expression (Gpre ++ pc, cpre ++ vc, qc') z Qubit).
          {
            intros z; split; intros Hz.
            - apply Hlist in Hz.
              eapply typecheck_expression_equivalent; [exact Hz|reflexivity|apply equivalent_refl].
            - apply Hlist.
              eapply typecheck_expression_equivalent with
                (theta1 := (Gpre ++ pc, cpre ++ vc, qc'))
                (theta2 := (Gpre ++ (Some (T, qc) :: pc), cpre ++ vc, qc'));
                [exact Hz|reflexivity|apply equivalent_refl].
          }
          assert (Hltb : Nat.ltb X (length Gpre) = false)
            by (apply Nat.ltb_ge; lia).
          assert (Heqb : Nat.eqb X (length Gpre) = false)
            by (apply Nat.eqb_neq; exact Hneq).
          simpl [substitutionP]; rewrite Hltb, Heqb.
          eapply T_var with (qcontext := qctx) (lz := lz).
          -- unfold in_process_context; simpl.
             rewrite app_nth2 by lia.
             replace (X - 1 - length Gpre) with
               (X - length Gpre - 1) by lia.
             exact Hfound_tail.
          -- exact Honly.
          -- exact Hvarinc.
          -- exact Hlist'.
          -- exact Hnd.
    - intros cxt Q0 T0 T1 Hq IH Hsub Gpre cpre qc' Hctx Hinc.
      subst cxt; simpl in *.
      eapply T_sub.
      + eapply IH with (Gpre:=Gpre) (cpre:=cpre)
          (qc':=qc').
        * reflexivity.
        * exact Hinc.
      + exact Hsub.
    - exact Htyped.
Qed.

Lemma recursion_substitution_preserves_typing :
    forall P T qc pc vc,
    typecheck_process (Some (T, qc) :: pc, vc, qc) P T ->
    typecheck_process (pc, vc, qc) (p_rec P) T ->
    typecheck_process (pc, vc, qc)
        (substitutionP 0 0 0 (p_rec P) P) T.
Proof.
    intros P T qc pc vc Hbody Hrec.
    pose proof (typecheck_process_p_rec_post T (pc, vc, qc) P Hrec) as Hrec_post.
    destruct Hrec_post as [Trec [Hrec_body [Honly Hrec_sub]]].
    unfold only_qubit_references_in_context in Honly; simpl in Honly.
    assert (Hlift : forall Gpre cpre,
      Forall (fun s : option sort => s <> Some Qubit) cpre ->
      typecheck_process (Gpre ++ pc, cpre ++ vc, qc)
        (incr_free 0 0 (length Gpre) (length cpre) (p_rec P)) T).
    { intros Gpre cpre Hcpre.
      eapply recursion_typechecking_context_lift; eauto. }
    eapply (@typecheck_rec_substitution_induction P T qc pc vc Honly Hlift
        (Some (T, qc) :: pc, vc, qc) P T Hbody nil nil qc eq_refl).
    unfold included; simpl; auto.
Qed.

Lemma typecheck_process_precongruence :
    forall qc P0 P1 T0,
    precongP P0 P1 ->
    typecheck_process (nil, nil, qc) P0 T0 ->
    typecheck_process (nil, nil, qc) P1 T0.
Proof.
    intros qc0 P0 P1 T0 Hunfold.
    induction Hunfold; intros Htyped0.
    - exact Htyped0.
    - apply typecheck_process_p_rec_post in Htyped0.
      destruct Htyped0 as [Trec [Hbody0 [Honly0 Hsub0]]].
      eapply IHHunfold.
      eapply T_sub.
      + eapply recursion_substitution_preserves_typing.
        * exact Hbody0.
        * eapply T_rec; eauto.
      + exact Hsub0.
    - eapply IHHunfold2; eapply IHHunfold1; exact Htyped0.
Qed.
