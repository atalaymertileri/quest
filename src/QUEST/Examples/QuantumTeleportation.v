From SQIR Require Import SQIR.
Require Import SST.
Require Import Permutation Reals List String.
Require Import SST QUEST session substitution balanced ExamplesHelpers.
From Paco Require Import paco.

Definition l_Env_A := 0.
Definition l_Env_B := 0.
Definition l_Source_A := 0.
Definition l_Source_B := 0.
Definition l_r1 := 0.
Definition l_r2 := 0.

Definition P_A : process :=
Source .& l_Source_A .; 
(Env .& l_Env_A .; 
(U_CNOT [. Var 0::Var 1::nil .]; (*CNOT (w,x)*)
(U_H [. Var 0::nil .]; (*H(w)*)
(p_measure (Var 0) (*r1 = measure w ; r1 :0, x:2 (w is destroyed)*)
(p_measure (Var 2) (*r2 = measure x*)
(Bob .+ l_r1 <. (Var 1) .>;
(Bob .+ l_r2 <. (Var 0) .>; 
(p_end (nil))))))))).

Definition U_I := U_R 0 0 0.

(*e1, e2 - Alice's signal to Bob. q: qubit to apply to*)
Definition apply_pauli e1 e2 q P : process :=
IF e1 THEN 
    (IF e2 THEN 
        (U_X [.q::nil.]; (U_Z [.q::nil.];P))
    ELSE
        (U_Z [.q::nil.]; P))
ELSE
    (IF e2 THEN 
        (U_X [.q::nil.]; P)
    ELSE
        (U_I [.q::nil.]; P)).


Definition P_B : process :=
Source .& l_Source_B.;
(Alice .& l_r1.;
(Alice .& l_r2.;
(apply_pauli (Var 1) (Var 0) (Var 2) 
(Env .+ l_Env_B<.(Var 2).>;
(p_end nil))))).

Definition P_S : process :=
p_newq (*xs*)
(p_newq (*ys*)
(U_H [.Var 1::nil.]; (*H[xs]*)
(U_CNOT [.Var 1::Var 0::nil.]; (*CNOT[xs,ys]*)
(Alice .+ l_Source_A <.(Var 1).>; 
(Bob .+ l_Source_B<.(Var 0).>;
(p_end nil)))))).

Definition P_E (q: qubit_reference): process :=
Alice .+ l_Env_A <.(Val (QVal q)).>;
(Bob .& l_Env_B.; 
(p_end (Var 0::nil))).

Definition quantum_teleportation q :=
insert (insert (insert (insert empty_fmap Source P_S) Env (P_E q)) Bob P_B) Alice P_A.

Definition quantum_teleportation_global : global :=
Source --> Alice $ l_Source_A(.Qubit.);
(Source --> Bob $ l_Source_B(.Qubit.);
(Env --> Alice $ l_Env_A(.Qubit.);
(Alice --> Bob $ l_r1(.header.Bool.);
(Alice --> Bob $ l_r2(.header.Bool.);
(Bob --> Env $ l_Env_B(.Qubit.); g_end))))).

Definition quantum_teleportation_global_coind : gtt :=
Source -c-> Alice $ l_Source_A(.Qubit.);
(Source -c-> Bob $ l_Source_B(.Qubit.);
(Env -c-> Alice $ l_Env_A(.Qubit.);
(Alice -c-> Bob $ l_r1(.header.Bool.);
(Alice -c-> Bob $ l_r2(.header.Bool.);
(Bob -c-> Env $ l_Env_B(.Qubit.); gtt_end))))).

(*LOCAL TYPES*)

Definition L_A : ltt := 
Source .&. l_Source_A(.Qubit.);
(Env .&. l_Env_A(.Qubit.);
(Bob .+. l_r1(.header.Bool.);
(Bob .+. l_r2(.header.Bool.); ltt_end))).

Definition L_B : ltt := 
Source .&. l_Source_B(.Qubit.);
(Alice .&. l_r1(.header.Bool.);
(Alice .&. l_r2(.header.Bool.);
(Env .+. l_Env_B(.Qubit.);ltt_end
))).

Definition L_S : ltt := 
Alice .+. l_Source_A(.Qubit.);
(Bob .+. l_Source_B(.Qubit.);ltt_end).

Definition L_E : ltt := 
Alice .+. l_Env_A(.Qubit.);
(Bob .&. l_Env_B(.Qubit.);ltt_end).

Lemma  quantum_teleportation_global_coind_balanced :
balancedG quantum_teleportation_global_coind.
Proof.
  pose (G5 := (Bob -c-> Env $ l_Env_B(.Qubit.); gtt_end)).
  pose (G4 := (Alice -c-> Bob $ l_r2(.header.Bool.); G5)).
  pose (G3 := (Alice -c-> Bob $ l_r1(.header.Bool.); G4)).
  pose (G2 := (Env -c-> Alice $ l_Env_A(.Qubit.); G3)).
  pose (G1 := (Source -c-> Bob $ l_Source_B(.Qubit.); G2)).
  pose (G0 := (Source -c-> Alice $ l_Source_A(.Qubit.); G1)).
  change (balancedG G0).

  assert (Hreg0 : regGtt G0).
  {
    unfold regGtt. exists quantum_teleportation_global.
    unfold quantum_teleportation_global, G0, G1, G2, G3, G4, G5.
    repeat gttTC_step.
  }
  assert (regGtt_branch : forall p q f n s g,
      regGtt (gtt_send p q f) -> f n = Some (s, g) -> regGtt g).
  {
    intros p q f n s g Hr Hf.
    pose proof (regGtt_cont p q f Hr n) as Hcont.
    destruct Hcont as [Hnone | (s' & g' & Heq & Hr')].
    - rewrite Hf in Hnone. discriminate.
    - rewrite Hf in Heq. inversion Heq. assumption.
  }
  assert (Hreg1 : regGtt G1).
  { eapply regGtt_branch with (n := 0) (s := Qubit) (g := G1).
    - exact Hreg0.
    - unfold G0, l_Source_A; simpl; reflexivity. }
  assert (Hreg2 : regGtt G2).
  { eapply regGtt_branch with (n := 0) (s := Qubit) (g := G2).
    - exact Hreg1.
    - unfold G1, l_Source_B; simpl; reflexivity. }
  assert (Hreg3 : regGtt G3).
  { eapply regGtt_branch with (n := 0) (s := Qubit) (g := G3).
    - exact Hreg2.
    - unfold G2, l_Env_A; simpl; reflexivity. }
  assert (Hreg4 : regGtt G4).
  { eapply regGtt_branch with (n := 0) (s := header.Bool) (g := G4).
    - exact Hreg3.
    - unfold G3, l_r1; simpl; reflexivity. }
  assert (Hreg5 : regGtt G5).
  { eapply regGtt_branch with (n := 0) (s := header.Bool) (g := G5).
    - exact Hreg4.
    - unfold G4, l_r2; simpl; reflexivity. }

  assert (partsCS_send0 : forall p q f s g,
      f 0 = Some (s, g) -> (forall n, f (S n) = None) ->
      (forall pt, isgPartsC pt g -> isgPartsCS pt g) ->
      forall pt, isgPartsC pt (gtt_send p q f) -> isgPartsCS pt (gtt_send p q f)).
  {
    intros p q f s g Hzero Hsucc Hchild pt Hparts.
    inversion Hparts; subst.
    - apply pacs_sendp.
    - apply pacs_sendq.
    - apply pacs_sendr; try assumption.
      intros m.
      destruct m as [|m].
      + right. exists s, g. split; [exact Hzero|].
        apply Hchild.
        destruct n as [|n].
        * simpl in H5. rewrite Hzero in H5. inversion H5. subst. exact H6.
        * rewrite Hsucc in H5. discriminate.
      + rewrite Hsucc. left. reflexivity.
  }
  assert (Hparts_end : forall pt,
      isgPartsC pt gtt_end -> isgPartsCS pt gtt_end).
  { intros pt Hparts. inversion Hparts. }
  assert (Hparts5 : forall pt, isgPartsC pt G5 -> isgPartsCS pt G5).
  {
    unfold G5, l_Env_B.
    apply partsCS_send0 with (s := Qubit) (g := gtt_end).
    - reflexivity.
    - intros n. reflexivity.
    - exact Hparts_end.
  }
  assert (Hparts4 : forall pt, isgPartsC pt G4 -> isgPartsCS pt G4).
  {
    unfold G4, l_r2.
    apply partsCS_send0 with (s := header.Bool) (g := G5).
    - reflexivity.
    - intros n. reflexivity.
    - exact Hparts5.
  }
  assert (Hparts3 : forall pt, isgPartsC pt G3 -> isgPartsCS pt G3).
  {
    unfold G3, l_r1.
    apply partsCS_send0 with (s := header.Bool) (g := G4).
    - reflexivity.
    - intros n. reflexivity.
    - exact Hparts4.
  }
  assert (Hparts2 : forall pt, isgPartsC pt G2 -> isgPartsCS pt G2).
  {
    unfold G2, l_Env_A.
    apply partsCS_send0 with (s := Qubit) (g := G3).
    - reflexivity.
    - intros n. reflexivity.
    - exact Hparts3.
  }
  assert (Hparts1 : forall pt, isgPartsC pt G1 -> isgPartsCS pt G1).
  {
    unfold G1, l_Source_B.
    apply partsCS_send0 with (s := Qubit) (g := G2).
    - reflexivity.
    - intros n. reflexivity.
    - exact Hparts2.
  }
  assert (Hparts0 : forall pt, isgPartsC pt G0 -> isgPartsCS pt G0).
  {
    unfold G0, l_Source_A.
    apply partsCS_send0 with (s := Qubit) (g := G1).
    - reflexivity.
    - intros n. reflexivity.
    - exact Hparts1.
  }

  assert (Hbal_end : balancedG gtt_end).
  { unfold balancedG. intros w w' p q Hmap.
    destruct Hmap as [Hleft|Hright]; inversion Hleft || inversion Hright. }
  assert (Hbal5 : balancedG G5).
  {
    unfold G5, l_Env_B. eapply balanced_up.
    - intros n. destruct n; simpl.
      + right. exists Qubit, gtt_end. split; [reflexivity|exact Hbal_end].
      + left. reflexivity.
    - exact Hreg5.
    - exact Hparts5.
  }
  assert (Hbal4 : balancedG G4).
  {
    unfold G4, l_r2. eapply balanced_up.
    - intros n. destruct n; simpl.
      + right. exists header.Bool, G5. split; [reflexivity|exact Hbal5].
      + left. reflexivity.
    - exact Hreg4.
    - exact Hparts4.
  }
  assert (Hbal3 : balancedG G3).
  {
    unfold G3, l_r1. eapply balanced_up.
    - intros n. destruct n; simpl.
      + right. exists header.Bool, G4. split; [reflexivity|exact Hbal4].
      + left. reflexivity.
    - exact Hreg3.
    - exact Hparts3.
  }
  assert (Hbal2 : balancedG G2).
  {
    unfold G2, l_Env_A. eapply balanced_up.
    - intros n. destruct n; simpl.
      + right. exists Qubit, G3. split; [reflexivity|exact Hbal3].
      + left. reflexivity.
    - exact Hreg2.
    - exact Hparts2.
  }
  assert (Hbal1 : balancedG G1).
  {
    unfold G1, l_Source_B. eapply balanced_up.
    - intros n. destruct n; simpl.
      + right. exists Qubit, G2. split; [reflexivity|exact Hbal2].
      + left. reflexivity.
    - exact Hreg1.
    - exact Hparts1.
  }
  unfold G0, l_Source_A. eapply balanced_up.
  - intros n. destruct n; simpl.
    + right. exists Qubit, G1. split; [reflexivity|exact Hbal1].
    + left. reflexivity.
  - exact Hreg0.
  - exact Hparts0.
Qed.

Lemma projection_exists_quantum_teleportation_global_coind:
forall (pt : participant) (T : ltt),
insert
(insert
(insert (insert empty_fmap Alice
L_A) Bob L_B) Source
L_S) Env L_E pt = Some T ->
exists T' : ltt,
@projC coind_full_merge quantum_teleportation_global_coind pt T' /\
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

  assert (Hparts_of_proj : forall g r T0,
      T0 <> ltt_end -> @projC coind_full_merge g r T0 -> isgPartsC r g).
  {
    intros g r T0 Hnonend Hproj.
    unfold projC, projectionC in Hproj. punfold Hproj.
    inversion Hproj; subst; try contradiction.
    - assumption.
    - assumption.
    - assumption.
    - apply proj_mon.
  }
  assert (Hskip : forall p q r f s g T0,
      f 0 = Some (s, g) -> (forall n, f (S n) = None) ->
      p <> q -> p <> r -> q <> r -> T0 <> ltt_end ->
      @projC coind_full_merge g r T0 ->
      @projC coind_full_merge (gtt_send p q f) r T0).
  {
    intros p q r f s g T0 Hzero Hsucc Hpq Hpr Hqr Hnonend Hproj.
    unfold projC, projectionC. pfold.
    assert (Hparts : isgPartsC r g).
    { eapply Hparts_of_proj; eauto. }
    apply proj_cont with
      (f' := fun n => if Nat.eqb n 0 then Some T0 else None).
    - exact Hpq.
    - exact Hqr.
    - exact Hpr.
    - eapply pac_sendr with (n := 0) (s := s) (g := g); eauto.
    - intros [|n]; simpl.
      + right. exists s, g, T0. split; [exact Hzero|].
        split; [reflexivity|left; exact Hproj].
      + left. split; [apply Hsucc|reflexivity].
    - apply Hsingle.
  }

  pose (G5 := (Bob -c-> Env $ l_Env_B(.Qubit.); gtt_end)).
  pose (G4 := (Alice -c-> Bob $ l_r2(.header.Bool.); G5)).
  pose (G3 := (Alice -c-> Bob $ l_r1(.header.Bool.); G4)).
  pose (G2 := (Env -c-> Alice $ l_Env_A(.Qubit.); G3)).
  pose (G1 := (Source -c-> Bob $ l_Source_B(.Qubit.); G2)).
  pose (G0 := (Source -c-> Alice $ l_Source_A(.Qubit.); G1)).
  pose (A1 := (Env .&. l_Env_A(.Qubit.); (Bob .+. l_r1(.header.Bool.); (Bob .+. l_r2(.header.Bool.); ltt_end)))).
  pose (A2 := (Bob .+. l_r1(.header.Bool.); (Bob .+. l_r2(.header.Bool.); ltt_end))).
  pose (A3 := (Bob .+. l_r2(.header.Bool.); ltt_end)).
  pose (B1 := (Alice .&. l_r1(.header.Bool.); (Alice .&. l_r2(.header.Bool.); (Env .+. l_Env_B(.Qubit.); ltt_end)))).
  pose (B2 := (Alice .&. l_r2(.header.Bool.); (Env .+. l_Env_B(.Qubit.); ltt_end))).
  pose (B3 := (Env .+. l_Env_B(.Qubit.); ltt_end)).
  pose (S1 := (Bob .+. l_Source_B(.Qubit.); ltt_end)).
  pose (E1 := (Bob .&. l_Env_B(.Qubit.); ltt_end)).

  assert (Hproj_end_source : @projC coind_full_merge G2 Source ltt_end).
  {
    unfold projC, projectionC. pfold. apply proj_end.
    unfold G2, G3, G4, G5, l_Env_A, l_r1, l_r2, l_Env_B, Source.
    intro Hpart.
    repeat match goal with
    | H : isgPartsC (Pt "Source") (gtt_send _ _ _) |- _ =>
        inversion H; subst; try congruence; clear H;
        match goal with
        | E : (if Nat.eqb ?n 0 then Some _ else None) = Some _ |- _ =>
            destruct n; simpl in E; [inversion E; subst; clear E | discriminate]
        end
    end;
    match goal with
    | H : isgPartsC (Pt "Source") gtt_end |- _ => inversion H
    end; congruence.
  }
  assert (Hproj_end_alice : @projC coind_full_merge G5 Alice ltt_end).
  {
    unfold projC, projectionC. pfold. apply proj_end.
    unfold G5, l_Env_B, Alice, Bob, Env.
    intro Hpart.
    repeat match goal with
    | H : isgPartsC (Pt "Alice") (gtt_send _ _ _) |- _ =>
        inversion H; subst; try discriminate; clear H;
        match goal with
        | E : (if Nat.eqb ?n 0 then Some _ else None) = Some _ |- _ =>
            destruct n; simpl in E; [inversion E; subst; clear E | discriminate]
        end
    end;
    match goal with H : isgPartsC (Pt "Alice") gtt_end |- _ => inversion H end;
    discriminate.
  }
  assert (Hproj_end_bob : @projC coind_full_merge gtt_end Bob ltt_end).
  {
    unfold projC, projectionC. pfold. apply proj_end.
    intro Hpart. inversion Hpart.
  }
  assert (Hproj_end_env : @projC coind_full_merge gtt_end Env ltt_end).
  {
    unfold projC, projectionC. pfold. apply proj_end.
    intro Hpart. inversion Hpart.
  }

  assert (Hproj_A4 : @projC coind_full_merge G4 Alice A3).
  {
    unfold projC, projectionC. pfold. unfold G4, l_r2, A3.
    apply proj_out with (f' := fun n => if Nat.eqb n l_r2 then Some (header.Bool, ltt_end) else None).
    - unfold Alice, Bob; discriminate.
    - apply pac_sendp.
    - intros [|n]; simpl.
      + right. exists header.Bool, G5, ltt_end. repeat split; try reflexivity.
        left. exact Hproj_end_alice.
      + left. split; reflexivity.
  }
  assert (Hproj_A3 : @projC coind_full_merge G3 Alice A2).
  {
    unfold projC, projectionC. pfold. unfold G3, l_r1, A2.
    apply proj_out with (f' := fun n => if Nat.eqb n l_r1 then Some (header.Bool, A3) else None).
    - unfold Alice, Bob; discriminate.
    - apply pac_sendp.
    - intros [|n]; simpl.
      + right. exists header.Bool, G4, A3. repeat split; try reflexivity.
        left. exact Hproj_A4.
      + left. split; reflexivity.
  }
  assert (Hproj_A2 : @projC coind_full_merge G2 Alice A1).
  {
    unfold projC, projectionC. pfold. unfold G2, l_Env_A, A1.
    apply proj_in with (f' := fun n => onth n (extendSlis l_Env_A (Qubit, A2))).
    - unfold Env, Alice; discriminate.
    - apply pac_sendq.
    - intros [|n]; simpl.
      + right. exists Qubit, G3, A2. repeat split; try reflexivity.
        left. exact Hproj_A3.
      + left. split; reflexivity.
  }
  assert (Hproj_A1 : @projC coind_full_merge G1 Alice A1).
  {
    unfold G1, l_Source_B.
    eapply Hskip; try (unfold Source, Bob, Alice; discriminate).
    - simpl; reflexivity.
    - intros n. reflexivity.
    - exact Hproj_A2.
  }
  assert (Hproj_A0 : @projC coind_full_merge G0 Alice L_A).
  {
    unfold projC, projectionC. pfold. unfold G0, l_Source_A, L_A.
    apply proj_in with (f' := fun n => onth n (extendSlis l_Source_A (Qubit, A1))).
    - unfold Source, Alice; discriminate.
    - apply pac_sendq.
    - intros [|n]; simpl.
      + right. exists Qubit, G1, A1. repeat split; try reflexivity.
        left. exact Hproj_A1.
      + left. split; reflexivity.
  }

  assert (Hproj_B5 : @projC coind_full_merge G5 Bob B3).
  {
    unfold projC, projectionC. pfold. unfold G5, l_Env_B, B3.
    apply proj_out with (f' := fun n => if Nat.eqb n l_Env_B then Some (Qubit, ltt_end) else None).
    - unfold Bob, Env; discriminate.
    - apply pac_sendp.
    - intros [|n]; simpl.
      + right. exists Qubit, gtt_end, ltt_end. repeat split; try reflexivity.
        left. exact Hproj_end_bob.
      + left. split; reflexivity.
  }
  assert (Hproj_B4 : @projC coind_full_merge G4 Bob B2).
  {
    unfold projC, projectionC. pfold. unfold G4, l_r2, B2.
    apply proj_in with (f' := fun n => onth n (extendSlis l_r2 (header.Bool, B3))).
    - unfold Alice, Bob; discriminate.
    - apply pac_sendq.
    - intros [|n]; simpl.
      + right. exists header.Bool, G5, B3. repeat split; try reflexivity.
        left. exact Hproj_B5.
      + left. split; reflexivity.
  }
  assert (Hproj_B3 : @projC coind_full_merge G3 Bob B1).
  {
    unfold projC, projectionC. pfold. unfold G3, l_r1, B1.
    apply proj_in with (f' := fun n => onth n (extendSlis l_r1 (header.Bool, B2))).
    - unfold Alice, Bob; discriminate.
    - apply pac_sendq.
    - intros [|n]; simpl.
      + right. exists header.Bool, G4, B2. repeat split; try reflexivity.
        left. exact Hproj_B4.
      + left. split; reflexivity.
  }
  assert (Hproj_B2 : @projC coind_full_merge G2 Bob B1).
  {
    unfold G2, l_Env_A.
    eapply Hskip; try (unfold Env, Alice, Bob; discriminate).
    - simpl; reflexivity.
    - intros n. reflexivity.
    - exact Hproj_B3.
  }
  assert (Hproj_B1 : @projC coind_full_merge G1 Bob L_B).
  {
    unfold projC, projectionC. pfold. unfold G1, l_Source_B, L_B.
    apply proj_in with (f' := fun n => onth n (extendSlis l_Source_B (Qubit, B1))).
    - unfold Source, Bob; discriminate.
    - apply pac_sendq.
    - intros [|n]; simpl.
      + right. exists Qubit, G2, B1. repeat split; try reflexivity.
        left. exact Hproj_B2.
      + left. split; reflexivity.
  }
  assert (Hproj_B0 : @projC coind_full_merge G0 Bob L_B).
  {
    unfold G0, l_Source_A.
    eapply Hskip; try (unfold Source, Alice, Bob; discriminate).
    - simpl; reflexivity.
    - intros n. reflexivity.
    - exact Hproj_B1.
  }

  assert (Hproj_S1 : @projC coind_full_merge G1 Source S1).
  {
    unfold projC, projectionC. pfold. unfold G1, l_Source_B, S1.
    apply proj_out with (f' := fun n => if Nat.eqb n l_Source_B then Some (Qubit, ltt_end) else None).
    - unfold Source, Bob; discriminate.
    - apply pac_sendp.
    - intros [|n]; simpl.
      + right. exists Qubit, G2, ltt_end.
        split; [reflexivity|].
        split; [reflexivity|].
        left. exact Hproj_end_source.
      + left. split; reflexivity.
  }
  assert (Hproj_S0 : @projC coind_full_merge G0 Source L_S).
  {
    unfold projC, projectionC. pfold. unfold G0, l_Source_A, L_S.
    apply proj_out with (f' := fun n => if Nat.eqb n l_Source_A then Some (Qubit, S1) else None).
    - unfold Source, Alice; discriminate.
    - apply pac_sendp.
    - intros [|n]; simpl.
      + right. exists Qubit, G1, S1. repeat split; try reflexivity.
        left. exact Hproj_S1.
      + left. split; reflexivity.
  }

  assert (Hpart_env4 : isgPartsC Env G4).
  {
    unfold G4, l_r2.
    eapply pac_sendr with (n := 0) (s := header.Bool) (g := G5).
    - unfold Alice, Env; discriminate.
    - unfold Bob, Env; discriminate.
    - simpl; reflexivity.
    - apply pac_sendq.
  }
  assert (Hproj_E5 : @projC coind_full_merge G5 Env E1).
  {
    unfold projC, projectionC. pfold. unfold G5, l_Env_B, E1.
    apply proj_in with (f' := fun n => onth n (extendSlis l_Env_B (Qubit, ltt_end))).
    - unfold Bob, Env; discriminate.
    - apply pac_sendq.
    - intros [|n]; simpl.
      + right. exists Qubit, gtt_end, ltt_end. repeat split; try reflexivity.
        left. exact Hproj_end_env.
      + left. split; reflexivity.
  }
  assert (Hproj_E4 : @projC coind_full_merge G4 Env E1).
  {
    unfold projC, projectionC. pfold. unfold G4, l_r2.
    apply proj_cont with (f' := fun n => if Nat.eqb n 0 then Some E1 else None).
    - unfold Alice, Bob; discriminate.
    - unfold Bob, Env; discriminate.
    - unfold Alice, Env; discriminate.
    - exact Hpart_env4.
    - intros [|n]; simpl.
      + right. exists header.Bool, G5, E1. repeat split; try reflexivity.
        left. exact Hproj_E5.
      + left. split; reflexivity.
    - apply Hsingle.
  }
  assert (Hpart_env3 : isgPartsC Env G3).
  {
    unfold G3, l_r1.
    eapply pac_sendr with (n := 0) (s := header.Bool) (g := G4).
    - unfold Alice, Env; discriminate.
    - unfold Bob, Env; discriminate.
    - simpl; reflexivity.
    - exact Hpart_env4.
  }
  assert (Hproj_E3 : @projC coind_full_merge G3 Env E1).
  {
    unfold projC, projectionC. pfold. unfold G3, l_r1.
    apply proj_cont with (f' := fun n => if Nat.eqb n 0 then Some E1 else None).
    - unfold Alice, Bob; discriminate.
    - unfold Bob, Env; discriminate.
    - unfold Alice, Env; discriminate.
    - exact Hpart_env3.
    - intros [|n]; simpl.
      + right. exists header.Bool, G4, E1. repeat split; try reflexivity.
        left. exact Hproj_E4.
      + left. split; reflexivity.
    - apply Hsingle.
  }
  assert (Hproj_E2 : @projC coind_full_merge G2 Env L_E).
  {
    unfold projC, projectionC. pfold. unfold G2, l_Env_A, L_E.
    apply proj_out with (f' := fun n => if Nat.eqb n l_Env_A then Some (Qubit, E1) else None).
    - unfold Env, Alice; discriminate.
    - apply pac_sendp.
    - intros [|n]; simpl.
      + right. exists Qubit, G3, E1. repeat split; try reflexivity.
        left. exact Hproj_E3.
      + left. split; reflexivity.
  }
  assert (Hproj_E1 : @projC coind_full_merge G1 Env L_E).
  {
    unfold G1, l_Source_B.
    eapply Hskip; try (unfold Source, Bob, Env; discriminate).
    - simpl; reflexivity.
    - intros n. reflexivity.
    - exact Hproj_E2.
  }
  assert (Hproj_E0 : @projC coind_full_merge G0 Env L_E).
  {
    unfold G0, l_Source_A.
    eapply Hskip; try (unfold Source, Alice, Env; discriminate).
    - simpl; reflexivity.
    - intros n. reflexivity.
    - exact Hproj_E1.
  }

  destruct (participant_dec pt Env) as [Heq|Hne].
  - subst pt. rewrite insert_eq in Hlookup. inversion Hlookup; subst T.
    exists L_E. split; [exact Hproj_E0|apply stRefl].
  - rewrite insert_neq in Hlookup by congruence.
    destruct (participant_dec pt Source) as [Heq|HneSource].
    + subst pt. rewrite insert_eq in Hlookup. inversion Hlookup; subst T.
      exists L_S. split; [exact Hproj_S0|apply stRefl].
    + rewrite insert_neq in Hlookup by congruence.
      destruct (participant_dec pt Bob) as [Heq|HneBob].
      * subst pt. rewrite insert_eq in Hlookup. inversion Hlookup; subst T.
        exists L_B. split; [exact Hproj_B0|apply stRefl].
      * rewrite insert_neq in Hlookup by congruence.
        destruct (participant_dec pt Alice) as [Heq|HneAlice].
        -- subst pt. rewrite insert_eq in Hlookup. inversion Hlookup; subst T.
           exists L_A. split; [exact Hproj_A0|apply stRefl].
        -- rewrite insert_neq in Hlookup by congruence.
           simpl in Hlookup. discriminate.
Qed.
 
    
(*(Alice , L_A) :: (Bob , L_B)  :: (Source , L_S):: (Env , L_E) :: nil*)
Lemma quantum_teleportation_typechecks:
forall q, typecheck_session (H := coind_full_merge) (insert (KEQ:= qr_dec) empty_fmap  q tt) (quantum_teleportation q) (insert (insert (insert (insert empty_fmap Alice L_A) Bob L_B) Source L_S) Env L_E) quantum_teleportation_global_coind.
Proof.
    intros; unfold typecheck_session, quantum_teleportation_global_coind.
    exists  (empty_fmap :: empty_fmap ::empty_fmap ::(insert (KEQ:= qr_dec) empty_fmap q tt)::nil).
    split.
    {
        exists quantum_teleportation_global.
        repeat gttTC_step.
    }
    split.
    {
        apply quantum_teleportation_global_coind_balanced.
    }
    split.
    {
        split.
        { 
        intros; inversionc H;
        repeat (case_analysis; clean_natb; cleanup;
        match goal with
        | [H: context [isgPartsC]|- _] =>
        inversionc H
        end);
        try solve [eexists; 
        repeat (try apply insert_eq;rewrite insert_neq; try congruence); intros Hnot; inversion Hnot].
        }
        apply projection_exists_quantum_teleportation_global_coind.
    }
    split.
    {
        unfold partition; simpl.
        repeat split.   
        cbv. intros.
        repeat case_analysis; cleanup; eauto.
        eexists; split.
        do 3 right; left; eauto.
        simpl; case_analysis; eauto.

        intros; cleanup.
        simpl in *; repeat split_ors; cleanup;
        simpl in *; cleanup; eauto.

        {   
        intros; cleanup. 
        assert (i = 3). {
        destruct i. rewrite nth_error_cons_0 in H0. inversion H0. subst. simpl in H2. contradiction.
        destruct i. rewrite nth_error_S in H0. simpl in H0. inversion H0. subst. simpl in H2. contradiction.
        destruct i. rewrite nth_error_S in H0. simpl in H0. inversion H0. subst. simpl in H2. contradiction.
        destruct i. auto.
        rewrite nth_error_S in H0. simpl in H0. rewrite nth_error_nil in H0. discriminate.
        }
        subst. rewrite nth_error_S in H0; simpl in H0. inversion H0. subst.
        destruct j. rewrite nth_error_cons_0 in H1. inversion H1. eauto.
        destruct j. rewrite nth_error_S in H1. simpl in H1. inversion H1. eauto.
        destruct j. rewrite nth_error_S in H1. simpl in H1. inversion H1. eauto.
        destruct j. contradiction.
        simpl in H1. rewrite nth_error_nil in H1. discriminate.
    }
    {
        intros; cleanup.
        assert (j = 3). {
        destruct j. rewrite nth_error_cons_0 in H1. inversion H1. subst. simpl in H2. contradiction.
        destruct j. rewrite nth_error_S in H1. simpl in H1. inversion H1. subst. simpl in H2. contradiction.
        destruct j. rewrite nth_error_S in H1. simpl in H1. inversion H1. subst. simpl in H2. contradiction.
        destruct j. auto.
        rewrite nth_error_S in H1. simpl in H1. rewrite nth_error_nil in H1. discriminate.
        }
        subst. rewrite nth_error_S in H1; simpl in H1. inversion H1. subst.
        destruct i. rewrite nth_error_cons_0 in H0. inversion H0. eauto.
        destruct i. rewrite nth_error_S in H0. simpl in H0. inversion H0. eauto.
        destruct i. rewrite nth_error_S in H0. simpl in H0. inversion H0. eauto.
        destruct i. contradiction.
        simpl in H0. rewrite nth_error_nil in H0. discriminate.
    }
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
    Opaque quantum_teleportation.
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
        intros; repeat split_ors; cleanup.

        inversionc H; 
        cbv in H0; cleanup.
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

        inversionc H; 
        cbv in H0; cleanup;
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

        inversionc H; 
        cbv in H0; cleanup;
        repeat case_analysis; cleanup.
    }
    {
        exists (P_E q).
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
        intros; repeat split_ors; cleanup.

        cbv; case_analysis; eauto.
        econstructor; cbv; eauto.
        inversionc H; 
        cbv in H0; cleanup;
        repeat case_analysis; cleanup.
    }
Unshelve.
all: try solve [repeat constructor].
Qed.
