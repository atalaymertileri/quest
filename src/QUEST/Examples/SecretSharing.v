From SQIR Require Import SQIR.
Require Import Permutation Reals List String.
Require Import SST session balanced.
Require Import Automation FMap Primitives Process Typechecking ExamplesHelpers.
From Paco Require Import paco.

Definition l_Env_A := 0.
Definition l_GHZ := 0.
Definition l_m := 0.
Definition l_n := 0.
Definition l_o := 0.
Definition l_c := 0.


Definition P_A : process :=
Env .& l_Env_A.;  (*x*)
(Source .& l_GHZ.;  (*a*)
(U_CNOT [.Var 1::Var 0::nil.]; (*CNOT[x,a]*) 
(U_H [.Var 1::nil.]; (*H[x]*)
(p_measure (Var 1) (*m := meas x; m:0, a:1*)
(p_measure (Var 1) (*n := meas a; n:0, m:1*)
(Charlie .+ l_m <.(Var 1).>; 
(Charlie .+ l_n <.(Var 0).>;
(p_end nil)))))))).

Definition P_B : process :=
Source .& l_GHZ.; (*b*)
(U_H [.Var 0::nil.]; (*H[b]*)
(p_measure (Var 0) (*o := meas b; o:0*)
(Charlie .+ l_o<.(Var 0).>;
(p_end nil)))).


Definition p_it e P Q := IF e THEN (P Q) ELSE Q.

Definition P_C : process := 
Source .& l_GHZ.; (*c*)
(Alice .& l_m.; (*m*)
(Alice .& l_n.; (*n*)
(Bob .& l_o.; (*o*)
(p_it (Var 0) (U_Z [.Var 3 :: nil.]; )
(p_it (Var 2) (U_Z [.Var 3 :: nil.]; )
(p_it (Var 1) (U_X [.Var 3 :: nil.]; )
(Env .+ l_c <.(Var 3).>; 
(p_end nil)))))))).

Definition P_S : process := 
p_newq (*a*)
(p_newq (*b*)
(p_newq (*c*)
(U_H [.Var 2 :: nil.]; (*H[a]*)
(U_CNOT [.Var 2 :: Var 1 :: nil.]; (*CNOT[a,b]*)
(U_CNOT [.Var 1 :: Var 0 :: nil.]; (*CNOT[b,c]*)
(Alice .+ l_GHZ<.(Var 2).>; 
(Bob .+ l_GHZ<.(Var 1).>; 
(Charlie .+ l_GHZ<.(Var 0).>; 
(p_end nil))))))))).

Definition P_E (q : qubit_reference) : process := 
Alice .+ l_Env_A<.(Val (QVal q)).>;
(Charlie .& l_c.;
(p_end (Var 0 :: nil))).

Definition secret_sharing q :=
insert (insert (insert (insert (insert empty_fmap Source P_S) Env (P_E q)) Charlie P_C ) Bob P_B) Alice P_A .

Definition secret_sharing_global : global :=
Env --> Alice $ l_Env_A(.Qubit.);
(Source --> Alice $ l_GHZ(.Qubit.);
(Source --> Bob $ l_GHZ(.Qubit.);
(Source --> Charlie $ l_GHZ(.Qubit.);
(Alice --> Charlie $ l_m(.header.Bool.);
(Alice --> Charlie $ l_n(.header.Bool.);
(Bob --> Charlie $ l_o(.header.Bool.);
(Charlie --> Env $ l_c(.Qubit.); g_end))))))).

Definition secret_sharing_global_coind : gtt :=
Env -c-> Alice $ l_Env_A(.Qubit.);
(Source -c-> Alice $ l_GHZ(.Qubit.);
(Source -c-> Bob $ l_GHZ(.Qubit.);
(Source -c-> Charlie $ l_GHZ(.Qubit.);
(Alice -c-> Charlie $ l_m(.header.Bool.);
(Alice -c-> Charlie $ l_n(.header.Bool.);
(Bob -c-> Charlie $ l_o(.header.Bool.);
(Charlie -c-> Env $ l_c(.Qubit.); gtt_end))))))).


(*LOCAL TYPES*)

Definition L_A : ltt := 
Env .&. l_Env_A(.Qubit.);
(Source .&. l_GHZ(.Qubit.);
(Charlie .+. l_m(.header.Bool.);
(Charlie .+. l_n(.header.Bool.); ltt_end
))).
Definition L_B : ltt := 
Source .&. l_GHZ(.Qubit.);
(Charlie .+. l_o(.header.Bool.);ltt_end).

Definition L_C : ltt := 
Source .&. l_GHZ(.Qubit.);
(Alice .&. l_m(.header.Bool.);
(Alice .&. l_n(.header.Bool.);
(Bob .&. l_o(.header.Bool.);
(Env .+. l_c(.Qubit.);ltt_end)))).

Definition L_S : ltt := 
Alice .+. l_GHZ(.Qubit.);
(Bob .+. l_GHZ(.Qubit.);
(Charlie .+. l_GHZ(.Qubit.);
ltt_end)).

Definition L_E : ltt := 
Alice .+. l_Env_A(.Qubit.);
(Charlie .&. l_c(.Qubit.);ltt_end).

Lemma  secret_sharing_global_coind_balanced :
balancedG secret_sharing_global_coind.
Proof.
  pose (G7 := (Charlie -c-> Env $ l_c(.Qubit.); gtt_end)).
  pose (G6 := (Bob -c-> Charlie $ l_o(.header.Bool.); G7)).
  pose (G5 := (Alice -c-> Charlie $ l_n(.header.Bool.); G6)).
  pose (G4 := (Alice -c-> Charlie $ l_m(.header.Bool.); G5)).
  pose (G3 := (Source -c-> Charlie $ l_GHZ(.Qubit.); G4)).
  pose (G2 := (Source -c-> Bob $ l_GHZ(.Qubit.); G3)).
  pose (G1 := (Source -c-> Alice $ l_GHZ(.Qubit.); G2)).
  pose (G0 := (Env -c-> Alice $ l_Env_A(.Qubit.); G1)).
  change (balancedG G0).

  assert (Hreg0 : regGtt G0).
  {
    unfold regGtt. exists secret_sharing_global.
    unfold secret_sharing_global, G0, G1, G2, G3, G4, G5, G6, G7.
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
    - unfold G0, l_Env_A; simpl; reflexivity. }
  assert (Hreg2 : regGtt G2).
  { eapply regGtt_branch with (n := 0) (s := Qubit) (g := G2).
    - exact Hreg1.
    - unfold G1, l_GHZ; simpl; reflexivity. }
  assert (Hreg3 : regGtt G3).
  { eapply regGtt_branch with (n := 0) (s := Qubit) (g := G3).
    - exact Hreg2.
    - unfold G2, l_GHZ; simpl; reflexivity. }
  assert (Hreg4 : regGtt G4).
  { eapply regGtt_branch with (n := 0) (s := Qubit) (g := G4).
    - exact Hreg3.
    - unfold G3, l_GHZ; simpl; reflexivity. }
  assert (Hreg5 : regGtt G5).
  { eapply regGtt_branch with (n := 0) (s := header.Bool) (g := G5).
    - exact Hreg4.
    - unfold G4, l_m; simpl; reflexivity. }
  assert (Hreg6 : regGtt G6).
  { eapply regGtt_branch with (n := 0) (s := header.Bool) (g := G6).
    - exact Hreg5.
    - unfold G5, l_n; simpl; reflexivity. }
  assert (Hreg7 : regGtt G7).
  { eapply regGtt_branch with (n := 0) (s := header.Bool) (g := G7).
    - exact Hreg6.
    - unfold G6, l_o; simpl; reflexivity. }

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
  assert (Hparts7 : forall pt, isgPartsC pt G7 -> isgPartsCS pt G7).
  {
    unfold G7, l_c.
    apply partsCS_send0 with (s := Qubit) (g := gtt_end).
    - reflexivity.
    - intros n. reflexivity.
    - exact Hparts_end.
  }
  assert (Hparts6 : forall pt, isgPartsC pt G6 -> isgPartsCS pt G6).
  {
    unfold G6, l_o.
    apply partsCS_send0 with (s := header.Bool) (g := G7).
    - reflexivity.
    - intros n. reflexivity.
    - exact Hparts7.
  }
  assert (Hparts5 : forall pt, isgPartsC pt G5 -> isgPartsCS pt G5).
  {
    unfold G5, l_n.
    apply partsCS_send0 with (s := header.Bool) (g := G6).
    - reflexivity.
    - intros n. reflexivity.
    - exact Hparts6.
  }
  assert (Hparts4 : forall pt, isgPartsC pt G4 -> isgPartsCS pt G4).
  {
    unfold G4, l_m.
    apply partsCS_send0 with (s := header.Bool) (g := G5).
    - reflexivity.
    - intros n. reflexivity.
    - exact Hparts5.
  }
  assert (Hparts3 : forall pt, isgPartsC pt G3 -> isgPartsCS pt G3).
  {
    unfold G3, l_GHZ.
    apply partsCS_send0 with (s := Qubit) (g := G4).
    - reflexivity.
    - intros n. reflexivity.
    - exact Hparts4.
  }
  assert (Hparts2 : forall pt, isgPartsC pt G2 -> isgPartsCS pt G2).
  {
    unfold G2, l_GHZ.
    apply partsCS_send0 with (s := Qubit) (g := G3).
    - reflexivity.
    - intros n. reflexivity.
    - exact Hparts3.
  }
  assert (Hparts1 : forall pt, isgPartsC pt G1 -> isgPartsCS pt G1).
  {
    unfold G1, l_GHZ.
    apply partsCS_send0 with (s := Qubit) (g := G2).
    - reflexivity.
    - intros n. reflexivity.
    - exact Hparts2.
  }
  assert (Hparts0 : forall pt, isgPartsC pt G0 -> isgPartsCS pt G0).
  {
    unfold G0, l_Env_A.
    apply partsCS_send0 with (s := Qubit) (g := G1).
    - reflexivity.
    - intros n. reflexivity.
    - exact Hparts1.
  }

  assert (Hbal_end : balancedG gtt_end).
  { unfold balancedG. intros w w' p q Hmap.
    destruct Hmap as [Hleft|Hright]; inversion Hleft || inversion Hright. }
  assert (Hbal7 : balancedG G7).
  {
    unfold G7, l_c. eapply balanced_up.
    - intros n. destruct n; simpl.
      + right. exists Qubit, gtt_end. split; [reflexivity|exact Hbal_end].
      + left. reflexivity.
    - exact Hreg7.
    - exact Hparts7.
  }
  assert (Hbal6 : balancedG G6).
  {
    unfold G6, l_o. eapply balanced_up.
    - intros n. destruct n; simpl.
      + right. exists header.Bool, G7. split; [reflexivity|exact Hbal7].
      + left. reflexivity.
    - exact Hreg6.
    - exact Hparts6.
  }
  assert (Hbal5 : balancedG G5).
  {
    unfold G5, l_n. eapply balanced_up.
    - intros n. destruct n; simpl.
      + right. exists header.Bool, G6. split; [reflexivity|exact Hbal6].
      + left. reflexivity.
    - exact Hreg5.
    - exact Hparts5.
  }
  assert (Hbal4 : balancedG G4).
  {
    unfold G4, l_m. eapply balanced_up.
    - intros n. destruct n; simpl.
      + right. exists header.Bool, G5. split; [reflexivity|exact Hbal5].
      + left. reflexivity.
    - exact Hreg4.
    - exact Hparts4.
  }
  assert (Hbal3 : balancedG G3).
  {
    unfold G3, l_GHZ. eapply balanced_up.
    - intros n. destruct n; simpl.
      + right. exists Qubit, G4. split; [reflexivity|exact Hbal4].
      + left. reflexivity.
    - exact Hreg3.
    - exact Hparts3.
  }
  assert (Hbal2 : balancedG G2).
  {
    unfold G2, l_GHZ. eapply balanced_up.
    - intros n. destruct n; simpl.
      + right. exists Qubit, G3. split; [reflexivity|exact Hbal3].
      + left. reflexivity.
    - exact Hreg2.
    - exact Hparts2.
  }
  assert (Hbal1 : balancedG G1).
  {
    unfold G1, l_GHZ. eapply balanced_up.
    - intros n. destruct n; simpl.
      + right. exists Qubit, G2. split; [reflexivity|exact Hbal2].
      + left. reflexivity.
    - exact Hreg1.
    - exact Hparts1.
  }
  unfold G0, l_Env_A. eapply balanced_up.
  - intros n. destruct n; simpl.
    + right. exists Qubit, G1. split; [reflexivity|exact Hbal1].
    + left. reflexivity.
  - exact Hreg0.
  - exact Hparts0.
Qed.

Lemma projection_exists_quantum_teleportation_global_coind:
forall (pt : participant) (T : ltt),
insert (insert (insert (insert (insert empty_fmap Alice L_A) Bob L_B) Charlie L_C) Source L_S) Env
L_E pt = Some T ->
exists T' : ltt,
@projC coind_full_merge secret_sharing_global_coind pt T' /\ subtypeC T T'.
Proof.
  intros pt T Hlookup.
  assert (Hsingle : forall T0,
      @isMerge coind_full_merge
        (fun n => if Nat.eqb n 0 then Some T0 else None) T0).
  {
    intros T0.
    change (full_merge (fun n => if Nat.eqb n 0 then Some T0 else None) T0).
    unfold full_merge. exists (slist_x T0). split.
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
  assert (Hout : forall p q f s g T0,
      f 0 = Some (s, g) -> (forall n, f (S n) = None) -> p <> q ->
      @projC coind_full_merge g p T0 ->
      @projC coind_full_merge (gtt_send p q f) p
        (ltt_send q (fun n => if Nat.eqb n 0 then Some (s, T0) else None))).
  {
    intros p q f s g T0 Hzero Hsucc Hneq Hproj.
    unfold projC, projectionC. pfold.
    apply proj_out with
      (f' := fun n => if Nat.eqb n 0 then Some (s, T0) else None).
    - exact Hneq.
    - apply pac_sendp.
    - intros [|n]; simpl.
      + right. exists s, g, T0. split; [exact Hzero|].
        split; [reflexivity|left; exact Hproj].
      + left. split; [apply Hsucc|reflexivity].
  }
  assert (Hin : forall p q f s g T0,
      f 0 = Some (s, g) -> (forall n, f (S n) = None) -> p <> q ->
      @projC coind_full_merge g q T0 ->
      @projC coind_full_merge (gtt_send p q f) q
        (ltt_recv p (fun n => onth n (extendSlis 0 (s, T0))))).
  {
    intros p q f s g T0 Hzero Hsucc Hneq Hproj.
    unfold projC, projectionC. pfold.
    apply proj_in with
      (f' := fun n => onth n (extendSlis 0 (s, T0))).
    - exact Hneq.
    - apply pac_sendq.
    - intros [|n]; simpl.
      + right. exists s, g, T0. split; [exact Hzero|].
        split; [reflexivity|left; exact Hproj].
      + left. split; [apply Hsucc|reflexivity].
  }

  pose (G7 := (Charlie -c-> Env $ l_c(.Qubit.); gtt_end)).
  pose (G6 := (Bob -c-> Charlie $ l_o(.header.Bool.); G7)).
  pose (G5 := (Alice -c-> Charlie $ l_n(.header.Bool.); G6)).
  pose (G4 := (Alice -c-> Charlie $ l_m(.header.Bool.); G5)).
  pose (G3 := (Source -c-> Charlie $ l_GHZ(.Qubit.); G4)).
  pose (G2 := (Source -c-> Bob $ l_GHZ(.Qubit.); G3)).
  pose (G1 := (Source -c-> Alice $ l_GHZ(.Qubit.); G2)).
  pose (G0 := (Env -c-> Alice $ l_Env_A(.Qubit.); G1)).

  pose (A1 := (Source .&. l_GHZ(.Qubit.);
      (Charlie .+. l_m(.header.Bool.);
       (Charlie .+. l_n(.header.Bool.); ltt_end)))).
  pose (A2 := (Charlie .+. l_m(.header.Bool.);
      (Charlie .+. l_n(.header.Bool.); ltt_end))).
  pose (A3 := (Charlie .+. l_n(.header.Bool.); ltt_end)).
  pose (B1 := (Charlie .+. l_o(.header.Bool.); ltt_end)).
  pose (C1 := (Alice .&. l_m(.header.Bool.);
      (Alice .&. l_n(.header.Bool.);
       (Bob .&. l_o(.header.Bool.);
        (Env .+. l_c(.Qubit.); ltt_end))))).
  pose (C2 := Alice .&. l_n(.header.Bool.);
      (Bob .&. l_o(.header.Bool.);
       (Env .+. l_c(.Qubit.); ltt_end))).
  pose (C3 := Bob .&. l_o(.header.Bool.);
      (Env .+. l_c(.Qubit.); ltt_end)).
  pose (C4 := (Env .+. l_c(.Qubit.); ltt_end)).
  pose (E1 := Charlie .&. l_c(.Qubit.); ltt_end).

  assert (Hproj_end_source : @projC coind_full_merge G4 Source ltt_end).
  {
    unfold projC, projectionC. pfold. apply proj_end.
    unfold G4, G5, G6, G7, l_m, l_n, l_o, l_c, Source.
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
  assert (Hproj_end_alice : @projC coind_full_merge G6 Alice ltt_end).
  {
    unfold projC, projectionC. pfold. apply proj_end.
    unfold G6, G7, l_o, l_c, Alice, Bob, Charlie, Env.
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
  assert (Hproj_end_bob : @projC coind_full_merge G7 Bob ltt_end).
  {
    unfold projC, projectionC. pfold. apply proj_end.
    unfold G7, l_c, Bob, Charlie, Env.
    intro Hpart.
    repeat match goal with
    | H : isgPartsC (Pt "Bob") (gtt_send _ _ _) |- _ =>
        inversion H; subst; try discriminate; clear H;
        match goal with
        | E : (if Nat.eqb ?n 0 then Some _ else None) = Some _ |- _ =>
            destruct n; simpl in E; [inversion E; subst; clear E | discriminate]
        end
    end;
    match goal with H : isgPartsC (Pt "Bob") gtt_end |- _ => inversion H end;
    discriminate.
  }
  assert (Hproj_end_env : @projC coind_full_merge gtt_end Env ltt_end).
  {
    unfold projC, projectionC. pfold. apply proj_end.
    intro Hpart. inversion Hpart.
  }
  assert (Hproj_end_charlie : @projC coind_full_merge gtt_end Charlie ltt_end).
  {
    unfold projC, projectionC. pfold. apply proj_end.
    intro Hpart. inversion Hpart.
  }

  assert (Hproj_A3 : @projC coind_full_merge G5 Alice A3).
  {
    unfold G5, l_n, A3.
    eapply Hout; try (unfold Alice, Charlie; discriminate).
    - simpl; reflexivity.
    - intros n. reflexivity.
    - exact Hproj_end_alice.
  }
  assert (Hproj_A2 : @projC coind_full_merge G4 Alice A2).
  {
    unfold G4, l_m, A2.
    eapply Hout; try (unfold Alice, Charlie; discriminate).
    - simpl; reflexivity.
    - intros n. reflexivity.
    - exact Hproj_A3.
  }
  assert (Hproj_A2_skip3 : @projC coind_full_merge G3 Alice A2).
  {
    unfold G3, l_GHZ.
    eapply Hskip; try (unfold Source, Charlie, Alice; discriminate).
    - simpl; reflexivity.
    - intros n. reflexivity.
    - exact Hproj_A2.
  }
  assert (Hproj_A2_skip2 : @projC coind_full_merge G2 Alice A2).
  {
    unfold G2, l_GHZ.
    eapply Hskip; try (unfold Source, Bob, Alice; discriminate).
    - simpl; reflexivity.
    - intros n. reflexivity.
    - exact Hproj_A2_skip3.
  }
  assert (Hproj_A1 : @projC coind_full_merge G1 Alice A1).
  {
    unfold G1, l_GHZ, A1.
    eapply Hin; try (unfold Source, Alice; discriminate).
    - simpl; reflexivity.
    - intros n. reflexivity.
    - exact Hproj_A2_skip2.
  }
  assert (Hproj_A0 : @projC coind_full_merge G0 Alice L_A).
  {
    unfold G0, l_Env_A, L_A.
    eapply Hin; try (unfold Env, Alice; discriminate).
    - simpl; reflexivity.
    - intros n. reflexivity.
    - exact Hproj_A1.
  }

  assert (Hproj_B6 : @projC coind_full_merge G6 Bob B1).
  {
    unfold G6, l_o, B1.
    eapply Hout; try (unfold Bob, Charlie; discriminate).
    - simpl; reflexivity.
    - intros n. reflexivity.
    - exact Hproj_end_bob.
  }
  assert (Hproj_B5 : @projC coind_full_merge G5 Bob B1).
  {
    unfold G5, l_n.
    eapply Hskip; try (unfold Alice, Charlie, Bob; discriminate).
    - simpl; reflexivity.
    - intros n. reflexivity.
    - exact Hproj_B6.
  }
  assert (Hproj_B4 : @projC coind_full_merge G4 Bob B1).
  {
    unfold G4, l_m.
    eapply Hskip; try (unfold Alice, Charlie, Bob; discriminate).
    - simpl; reflexivity.
    - intros n. reflexivity.
    - exact Hproj_B5.
  }
  assert (Hproj_B3 : @projC coind_full_merge G3 Bob B1).
  {
    unfold G3, l_GHZ.
    eapply Hskip; try (unfold Source, Charlie, Bob; discriminate).
    - simpl; reflexivity.
    - intros n. reflexivity.
    - exact Hproj_B4.
  }
  assert (Hproj_B2 : @projC coind_full_merge G2 Bob L_B).
  {
    unfold G2, l_GHZ, L_B.
    eapply Hin; try (unfold Source, Bob; discriminate).
    - simpl; reflexivity.
    - intros n. reflexivity.
    - exact Hproj_B3.
  }
  assert (Hproj_B1 : @projC coind_full_merge G1 Bob L_B).
  {
    unfold G1, l_GHZ.
    eapply Hskip; try (unfold Source, Alice, Bob; discriminate).
    - simpl; reflexivity.
    - intros n. reflexivity.
    - exact Hproj_B2.
  }
  assert (Hproj_B0 : @projC coind_full_merge G0 Bob L_B).
  {
    unfold G0, l_Env_A.
    eapply Hskip; try (unfold Env, Alice, Bob; discriminate).
    - simpl; reflexivity.
    - intros n. reflexivity.
    - exact Hproj_B1.
  }

  assert (Hproj_S3 : @projC coind_full_merge G3 Source
      (Charlie .+. l_GHZ(.Qubit.); ltt_end)).
  {
    unfold G3, l_GHZ.
    eapply Hout; try (unfold Source, Charlie; discriminate).
    - simpl; reflexivity.
    - intros n. reflexivity.
    - exact Hproj_end_source.
  }
  assert (Hproj_S2 : @projC coind_full_merge G2 Source
      (Bob .+. l_GHZ(.Qubit.);
       (Charlie .+. l_GHZ(.Qubit.); ltt_end))).
  {
    unfold G2, l_GHZ.
    eapply Hout; try (unfold Source, Bob; discriminate).
    - simpl; reflexivity.
    - intros n. reflexivity.
    - exact Hproj_S3.
  }
  assert (Hproj_S1 : @projC coind_full_merge G1 Source L_S).
  {
    unfold G1, l_GHZ, L_S.
    eapply Hout; try (unfold Source, Alice; discriminate).
    - simpl; reflexivity.
    - intros n. reflexivity.
    - exact Hproj_S2.
  }
  assert (Hproj_S0 : @projC coind_full_merge G0 Source L_S).
  {
    unfold G0, l_Env_A.
    eapply Hskip; try (unfold Env, Alice, Source; discriminate).
    - simpl; reflexivity.
    - intros n. reflexivity.
    - exact Hproj_S1.
  }

  assert (Hproj_C7 : @projC coind_full_merge G7 Charlie C4).
  {
    unfold G7, l_c, C4.
    eapply Hout; try (unfold Charlie, Env; discriminate).
    - simpl; reflexivity.
    - intros n. reflexivity.
    - exact Hproj_end_charlie.
  }
  assert (Hproj_C6 : @projC coind_full_merge G6 Charlie C3).
  {
    unfold G6, l_o, C3.
    eapply Hin; try (unfold Bob, Charlie; discriminate).
    - simpl; reflexivity.
    - intros n. reflexivity.
    - exact Hproj_C7.
  }
  assert (Hproj_C5 : @projC coind_full_merge G5 Charlie C2).
  {
    unfold G5, l_n, C2.
    eapply Hin; try (unfold Alice, Charlie; discriminate).
    - simpl; reflexivity.
    - intros n. reflexivity.
    - exact Hproj_C6.
  }
  assert (Hproj_C4 : @projC coind_full_merge G4 Charlie C1).
  {
    unfold G4, l_m, C1.
    eapply Hin; try (unfold Alice, Charlie; discriminate).
    - simpl; reflexivity.
    - intros n. reflexivity.
    - exact Hproj_C5.
  }
  assert (Hproj_C3 : @projC coind_full_merge G3 Charlie L_C).
  {
    unfold G3, l_GHZ, L_C.
    eapply Hin; try (unfold Source, Charlie; discriminate).
    - simpl; reflexivity.
    - intros n. reflexivity.
    - exact Hproj_C4.
  }
  assert (Hproj_C2 : @projC coind_full_merge G2 Charlie L_C).
  {
    unfold G2, l_GHZ.
    eapply Hskip; try (unfold Source, Bob, Charlie; discriminate).
    - simpl; reflexivity.
    - intros n. reflexivity.
    - exact Hproj_C3.
  }
  assert (Hproj_C1 : @projC coind_full_merge G1 Charlie L_C).
  {
    unfold G1, l_GHZ.
    eapply Hskip; try (unfold Source, Alice, Charlie; discriminate).
    - simpl; reflexivity.
    - intros n. reflexivity.
    - exact Hproj_C2.
  }
  assert (Hproj_C0 : @projC coind_full_merge G0 Charlie L_C).
  {
    unfold G0, l_Env_A.
    eapply Hskip; try (unfold Env, Alice, Charlie; discriminate).
    - simpl; reflexivity.
    - intros n. reflexivity.
    - exact Hproj_C1.
  }

  assert (Hproj_E7 : @projC coind_full_merge G7 Env E1).
  {
    unfold G7, l_c, E1.
    eapply Hin; try (unfold Charlie, Env; discriminate).
    - simpl; reflexivity.
    - intros n. reflexivity.
    - exact Hproj_end_env.
  }
  assert (Hproj_E6 : @projC coind_full_merge G6 Env E1).
  {
    unfold G6, l_o.
    eapply Hskip; try (unfold Bob, Charlie, Env; discriminate).
    - simpl; reflexivity.
    - intros n. reflexivity.
    - exact Hproj_E7.
  }
  assert (Hproj_E5 : @projC coind_full_merge G5 Env E1).
  {
    unfold G5, l_n.
    eapply Hskip; try (unfold Alice, Charlie, Env; discriminate).
    - simpl; reflexivity.
    - intros n. reflexivity.
    - exact Hproj_E6.
  }
  assert (Hproj_E4 : @projC coind_full_merge G4 Env E1).
  {
    unfold G4, l_m.
    eapply Hskip; try (unfold Alice, Charlie, Env; discriminate).
    - simpl; reflexivity.
    - intros n. reflexivity.
    - exact Hproj_E5.
  }
  assert (Hproj_E3 : @projC coind_full_merge G3 Env E1).
  {
    unfold G3, l_GHZ.
    eapply Hskip; try (unfold Source, Charlie, Env; discriminate).
    - simpl; reflexivity.
    - intros n. reflexivity.
    - exact Hproj_E4.
  }
  assert (Hproj_E2 : @projC coind_full_merge G2 Env E1).
  {
    unfold G2, l_GHZ.
    eapply Hskip; try (unfold Source, Bob, Env; discriminate).
    - simpl; reflexivity.
    - intros n. reflexivity.
    - exact Hproj_E3.
  }
  assert (Hproj_E1 : @projC coind_full_merge G1 Env E1).
  {
    unfold G1, l_GHZ.
    eapply Hskip; try (unfold Source, Alice, Env; discriminate).
    - simpl; reflexivity.
    - intros n. reflexivity.
    - exact Hproj_E2.
  }
  assert (Hproj_E0 : @projC coind_full_merge G0 Env L_E).
  {
    unfold G0, l_Env_A, L_E.
    eapply Hout; try (unfold Env, Alice; discriminate).
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
      destruct (participant_dec pt Charlie) as [Heq|HneCharlie].
      * subst pt. rewrite insert_eq in Hlookup. inversion Hlookup; subst T.
        exists L_C. split; [exact Hproj_C0|apply stRefl].
      * rewrite insert_neq in Hlookup by congruence.
        destruct (participant_dec pt Bob) as [Heq|HneBob].
        -- subst pt. rewrite insert_eq in Hlookup. inversion Hlookup; subst T.
           exists L_B. split; [exact Hproj_B0|apply stRefl].
        -- rewrite insert_neq in Hlookup by congruence.
           destruct (participant_dec pt Alice) as [Heq|HneAlice].
           ++ subst pt. rewrite insert_eq in Hlookup. inversion Hlookup; subst T.
              exists L_A. split; [exact Hproj_A0|apply stRefl].
           ++ rewrite insert_neq in Hlookup by congruence.
              simpl in Hlookup. discriminate.
Qed.

Lemma secret_sharing_typechecks:
forall q, typecheck_session (H:=coind_full_merge)(insert (KEQ:= qr_dec) empty_fmap q tt) (secret_sharing q) (insert (insert ( insert (insert (insert empty_fmap Alice L_A) Bob L_B) Charlie L_C )Source L_S) Env L_E) secret_sharing_global_coind.
Proof.
    intros; unfold typecheck_session, secret_sharing_global_coind.
    exists (empty_fmap :: empty_fmap ::empty_fmap ::empty_fmap ::(insert (KEQ:= qr_dec) empty_fmap  q tt)::nil).
    split.
    {
        exists secret_sharing_global; unfold secret_sharing_global.
        repeat gttTC_step.
    }
    split.
    {
        apply secret_sharing_global_coind_balanced.
    }
    repeat split.
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
    {
        apply projection_exists_quantum_teleportation_global_coind.
    }
    {
        simpl. repeat case_analysis.
        intros H. inversion H;subst; clear H. 
        exists (insert (KEQ := qr_dec) empty_fmap k tt).
        split. right. right. right. right. left. reflexivity. cbv. destruct (qr_dec k k). auto. contradiction.
    }
    {
        simpl. repeat case_analysis.
        intros H. inversion H. repeat (destruct H0); simpl in *; try( discriminate).
        case_analysis.
        intros. exfalso.
        inversion H. repeat destruct H0;simpl in *; try(discriminate).
        case_analysis. 
    }
    
    {   
        simpl.
        intros; cleanup. 
        assert (i = 4). {
        destruct i. rewrite nth_error_cons_0 in H0. inversion H0. subst. simpl in H2. contradiction.
        destruct i. rewrite nth_error_S in H0. simpl in H0. inversion H0. subst. simpl in H2. contradiction.
        destruct i. rewrite nth_error_S in H0. simpl in H0. inversion H0. subst. simpl in H2. contradiction.
        destruct i. rewrite nth_error_S in H0. simpl in H0. inversion H0. subst. simpl in H2. contradiction.
        destruct i. auto.
        rewrite nth_error_S in H0. simpl in H0. rewrite nth_error_nil in H0. discriminate.
        }
        subst. rewrite nth_error_S in H0; simpl in H0. inversion H0. subst.
        destruct j. rewrite nth_error_cons_0 in H1. inversion H1. eauto.
        destruct j. rewrite nth_error_S in H1. simpl in H1. inversion H1. eauto.
        destruct j. rewrite nth_error_S in H1. simpl in H1. inversion H1. eauto.
        destruct j. rewrite nth_error_S in H1. simpl in H1. inversion H1. eauto.
        destruct j. contradiction.
        simpl in H1. rewrite nth_error_nil in H1. discriminate.
    }
    {
        intros; cleanup.
        assert (j = 4). {
        destruct j. rewrite nth_error_cons_0 in H1. inversion H1. subst. simpl in H2. contradiction.
        destruct j. rewrite nth_error_S in H1. simpl in H1. inversion H1. subst. simpl in H2. contradiction.
        destruct j. rewrite nth_error_S in H1. simpl in H1. inversion H1. subst. simpl in H2. contradiction.
        destruct j. rewrite nth_error_S in H1. simpl in H1. inversion H1. subst. simpl in H2. contradiction.
        destruct j. auto.
        rewrite nth_error_S in H1. simpl in H1. rewrite nth_error_nil in H1. discriminate.
        }
        subst. rewrite nth_error_S in H1; simpl in H1. inversion H1. subst.
        destruct i. rewrite nth_error_cons_0 in H0. inversion H0. eauto.
        destruct i. rewrite nth_error_S in H0. simpl in H0. inversion H0. eauto.
        destruct i. rewrite nth_error_S in H0. simpl in H0. inversion H0. eauto.
        destruct i. rewrite nth_error_S in H0. simpl in H0. inversion H0. eauto.
        destruct i. contradiction.
        simpl in H0. rewrite nth_error_nil in H0. discriminate.
    }
    {
      cbv. eapply Permutation_trans with
        (l' := Env :: Source :: Charlie :: Bob :: Alice :: nil).
      - apply Permutation_rev.
      - simpl. apply perm_swap.
    }
    Opaque secret_sharing.
    cbv;intros. repeat split_ors;cleanup.
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
        exists P_C.
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
