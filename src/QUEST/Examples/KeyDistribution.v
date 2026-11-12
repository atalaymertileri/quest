From Paco Require Import paco.
From SQIR Require Import SQIR.
Require Import Permutation Reals List String Lia.
Require Import SST session balanced.
Require Import Automation FMap Primitives Process Typechecking ExamplesHelpers.

Definition Seller := Pt "Seller".
Definition Buyer := Pt "Buyer".
Definition Verif := Pt "Verif".

(* Labels are numeric; abort and ok occupy the two choice branches. *)
Definition l_abort := 0.
Definition l_ok := 1.
Definition l_ok1 := 0.
Definition l_PKey_B01 := 0.
Definition l_PKey_B02 := 0.
Definition l_PKey_B11 := 0.
Definition l_PKey_B12 := 0.
Definition l_PKey_V03 := 0.
Definition l_PKey_V04 := 0.
Definition l_PKey_V13 := 0.
Definition l_PKey_V14 := 0.

(* Abstract quantum one-way function. Its continuation binds the output at
   index 0, just as p_newq does in the other examples. *)
Parameter qow : list bool -> process -> process.
Parameter qow_typecheck : forall k cont T context,
  typecheck_process (insert_into_variable_context context Qubit) cont T ->
  typecheck_process context (qow k cont) T.

Definition U_T : base_Unitary 1 := U_R 0 0 (PI / 4).
Definition U_TDAG : base_Unitary 1 := U_R 0 0 (-(PI / 4)).

Definition do_Toffoli (a b c : expression) (P : process) : process :=
U_H [.c :: nil.];
(U_CNOT [.b :: c :: nil.];
(U_TDAG [.c :: nil.];
(U_CNOT [.a :: c :: nil.];
(U_T [.c :: nil.];
(U_CNOT [.b :: c :: nil.];
(U_TDAG [.c :: nil.];
(U_CNOT [.a :: c :: nil.];
(U_CNOT [.a :: b :: nil.];
(U_TDAG [.b :: nil.];
(U_CNOT [.a :: b :: nil.];
(U_T [.a :: nil.];
(U_T [.b :: nil.];
(U_T [.c :: nil.];
(U_H [.c :: nil.]; P)))))))))))))).

Definition do_CSWAP (a b c : expression) (P : process) : process :=
U_CNOT [.c :: b :: nil.];
(do_Toffoli a b c (U_CNOT [.c :: b :: nil.]; P)).

   
Definition QS (q q' : expression) (P : process) : process :=
p_newq
(U_H [.Var 0 :: nil.];
(do_CSWAP (Var 0) (incr_free_expression 0 1 q)
  (incr_free_expression 0 1 q')
(U_H [.Var 0 :: nil.];
(p_measure (Var 0) P)))).

(* Indices include consumed variables: receiving, allocation, and measurement
   each introduce a binder; sending only clears its context entry. *)
Definition P_S (k0 k1 : list bool) : process :=
(qow k0
(Buyer .+ l_PKey_B01 <.Var 0.>;
(qow k0
(Buyer .+ l_PKey_B02 <.Var 0.>;
(qow k1
(Buyer .+ l_PKey_B11 <.Var 0.>;
(qow k1
(Buyer .+ l_PKey_B12 <.Var 0.>;
(qow k0
(Verif .+ l_PKey_V03 <.Var 0.>;
(qow k0
(Verif .+ l_PKey_V04 <.Var 0.>;
(qow k1
(Verif .+ l_PKey_V13 <.Var 0.>;
(qow k1
(Verif .+ l_PKey_V14 <.Var 0.>;
(p_end (nil)))))))))))))))))).

Definition P_B : process :=
(Seller .& l_PKey_B01 .;
(Seller .& l_PKey_B02 .;
(Seller .& l_PKey_B11 .; 
(Seller .& l_PKey_B12 .; (*qk12:0 ; qk11:1 ; qk02:2 ; qk01:3*)
(QS (Var 3) (Var 2) (*r0 = QS(qk01,qk02);    r0:0; None; qk12:2 ; qk11:3 ; qk02:4 ; qk01:5*)
(QS (Var 3) (Var 2) (*r1 = QS(qk11,qk12);    r1: 0; None ; r0:2 ; None; qk12:4 ; qk11:5 ; qk02:6 ; qk01:7*)
(IF (Op Or (Var 2 :: Var 0 :: nil)) (*r0 \/ r1*)
THEN (Verif .+ l_abort <.UNIT.>;
(p_end ((Var 7) :: (Var 6) :: (Var 5) :: (Var 4) :: nil)))
ELSE (Verif .+ l_ok <.(Var 7).>; (**)
(Verif .+ l_ok1 <.(Var 5).>; 
(Verif .& {(*qk0v*)
  0 => (p_end ((Var 7) :: (Var 5) :: nil)) (*end with qk02, qk12*)
| 1 => (Verif .& l_ok1 .; (*qk1v:0; qk0v:1; r1: 2; None ; r0:4 ; None; qk12:6 ; qk11:7 ; qk02:8 ; qk01:9*)
(QS (Var 1) (Var 8) (*r0f = QS(qk0v, qk02) ;    r0f:0; None; qk1v:2; qk0v:3; r1: 4; None ; r0:6 ; None; qk12:8 ; qk11:9 ; qk02:10 ; qk01:11*)
(QS (Var 2) (Var 8) (*r1f = QS(qk1v, qk12)  r1f:0; None; r0f:0; None; qk1v:4; qk0v:5; r1: 6; None ; r0:8 ; None; qk12:10 ; qk11:11 ; qk02:12 ; qk01:13*)
(IF (Op Or (Var 2 :: Var 0 :: nil)) (*r0f and r1f*)
THEN (Verif .+ l_abort <.UNIT.>; 
(p_end ((Var 12) :: (Var 10) :: (Var 5) :: (Var 4) :: nil)))
ELSE (Verif .+ l_ok <.UNIT.>;
(p_end ((Var 12) :: (Var 10) :: (Var 5) :: (Var 4) :: nil)))))))
})))))))))).

Definition P_V : process :=
(Seller .& l_PKey_V03 .;
(Seller .& l_PKey_V04 .;
(Seller .& l_PKey_V13 .;
(Seller .& l_PKey_V14 .;
(QS (Var 3) (Var 2)
(QS (Var 3) (Var 2)
(Buyer .& { (*qk0b*)
  0 => (Env .+ l_abort <.UNIT.>;
(p_end ((Var 8) :: (Var 7) :: (Var 6) :: (Var 5) :: nil)))
| 1 => (Buyer .& l_ok1 .; (*qk1b*)  (*qk1b, qk0b,r1, None, r0, None, qk14, qk13,qk04, qk03 *)
(IF (Op Or (Var 4 :: Var 2 :: nil)) (*r0 r1*)
THEN (Buyer .+ l_abort <.UNIT.>;
(Env .+ l_abort <.UNIT.>;
(p_end ((Var 9) :: (Var 8) :: (Var 7) :: (Var 6) :: (Var 1) :: (Var 0) :: nil))))
ELSE (Buyer .+ l_ok <.(Var 9).>;
(Buyer .+ l_ok1 <.(Var 7).>;
(Buyer .& { (*received unit*) (*UNIT, qk1b, qk0b,r1, None, r0, None, qk14, qk13,qk04, qk03 *)
  0 => (Env .+ l_abort <.UNIT.>;
(p_end ((Var 9) :: (Var 7) :: (Var 2) :: (Var 1) :: nil)))
| 1 => (QS (Var 2) (Var 9) (*r0g = QS(qk0b, qk04)*)
(QS (Var 3) (Var 9) (*r1g = QS(qk1b, qk14)*)(*r1g, None, r0g, None, UNIT, qk1b, qk0b,r1, None, r0, None, qk14, qk13,qk04, qk03 *) 
(IF (Op Or (Var 2 :: Var 0 :: nil))
THEN (Env .+ l_abort <.UNIT.>;
(p_end ((Var 13) :: (Var 11) :: (Var 6) :: (Var 5) :: nil)))
ELSE (Env .+ l_ok <.UNIT.>;
(p_end ((Var 13) :: (Var 11) :: (Var 6) :: (Var 5) :: nil))))))
})))))
}))))))).

Definition P_E : process :=
(Verif .& {
  0 => (p_end (nil))
| 1 => (p_end (nil))
}).

Definition key_distribution k0 k1 : session :=
insert (insert (insert (insert empty_fmap Seller (P_S k0 k1))
  Buyer P_B) Verif P_V) Env P_E.

Definition key_distribution_global : global :=
Seller --> Buyer $ l_PKey_B01(.Qubit.);
(Seller --> Buyer $ l_PKey_B02(.Qubit.);
(Seller --> Buyer $ l_PKey_B11(.Qubit.);
(Seller --> Buyer $ l_PKey_B12(.Qubit.);
(Seller --> Verif $ l_PKey_V03(.Qubit.);
(Seller --> Verif $ l_PKey_V04(.Qubit.);
(Seller --> Verif $ l_PKey_V13(.Qubit.);
(Seller --> Verif $ l_PKey_V14(.Qubit.);
(Buyer --> Verif $ {
  0 (.header.Bool.);
    Verif --> Env $ l_abort(.header.Bool.); g_end
| 1 (.Qubit.);
    Buyer --> Verif $ l_ok1(.Qubit.);
    (Verif --> Buyer $ {
      0 (.header.Bool.);
        Verif --> Env $ l_abort(.header.Bool.); g_end
    | 1 (.Qubit.);
        Verif --> Buyer $ l_ok1(.Qubit.);
        (Buyer --> Verif $ {
          0 (.header.Bool.);
            Verif --> Env $ l_abort(.header.Bool.); g_end
        | 1 (.header.Bool.);
            Verif --> Env $ {
              0 (.header.Bool.); g_end
            | 1 (.header.Bool.); g_end
            }
        })
    })
})))))))).

(* Named suffixes keep the coinductive global readable and let the proofs
   follow one protocol phase at a time. *)
Definition KD_G_abort : gtt :=
  gtt_send Verif Env
    (fun n => if Nat.eqb n l_abort then Some (header.Bool, gtt_end) else None).

Definition KD_G_final_env : gtt :=
  gtt_send Verif Env
    (fun n => match n with
      | 0 => Some (header.Bool, gtt_end)
      | 1 => Some (header.Bool, gtt_end)
      | _ => None
    end).

Definition KD_G_buyer_final_choice : gtt :=
  gtt_send Buyer Verif
    (fun n => match n with
      | 0 => Some (header.Bool, KD_G_abort)
      | 1 => Some (header.Bool, KD_G_final_env)
      | _ => None
    end).

Definition KD_G_verif_final_qubit : gtt :=
  gtt_send Verif Buyer
    (fun n => if Nat.eqb n l_ok1 then Some (Qubit, KD_G_buyer_final_choice) else None).

Definition KD_G_verif_choice : gtt :=
  gtt_send Verif Buyer
    (fun n => match n with
      | 0 => Some (header.Bool, KD_G_abort)
      | 1 => Some (Qubit, KD_G_verif_final_qubit)
      | _ => None
    end).

Definition KD_G_buyer_second_qubit : gtt :=
  gtt_send Buyer Verif
    (fun n => if Nat.eqb n l_ok1 then Some (Qubit, KD_G_verif_choice) else None).

Definition KD_G_buyer_choice : gtt :=
  gtt_send Buyer Verif
    (fun n => match n with
      | 0 => Some (header.Bool, KD_G_abort)
      | 1 => Some (Qubit, KD_G_buyer_second_qubit)
      | _ => None
    end).

Definition key_distribution_global_coind : gtt :=
  Seller -c-> Buyer $ l_PKey_B01(.Qubit.);
  (Seller -c-> Buyer $ l_PKey_B02(.Qubit.);
  (Seller -c-> Buyer $ l_PKey_B11(.Qubit.);
  (Seller -c-> Buyer $ l_PKey_B12(.Qubit.);
  (Seller -c-> Verif $ l_PKey_V03(.Qubit.);
  (Seller -c-> Verif $ l_PKey_V04(.Qubit.);
  (Seller -c-> Verif $ l_PKey_V13(.Qubit.);
  (Seller -c-> Verif $ l_PKey_V14(.Qubit.); KD_G_buyer_choice))))))).

(* Finite global witnesses used to show that the coinductive global is
   regular.  The communication structure mirrors the suffixes above. *)
Definition KD_S_abort : global :=
  g_send Verif Env (extendSlis l_abort (header.Bool, g_end)).

Definition KD_S_final_env : global :=
  g_send Verif Env
    (slist_xs (Some (header.Bool, g_end)) (slist_x (header.Bool, g_end))).

Definition KD_S_buyer_final_choice : global :=
  g_send Buyer Verif
    (slist_xs (Some (header.Bool, KD_S_abort))
      (slist_x (header.Bool, KD_S_final_env))).

Definition KD_S_verif_choice : global :=
  g_send Verif Buyer
    (slist_xs (Some (header.Bool, KD_S_abort))
      (slist_x (Qubit, (g_send Verif Buyer (extendSlis l_ok1 (Qubit, KD_S_buyer_final_choice)))))).

Definition KD_S_buyer_choice : global :=
  g_send Buyer Verif
    (slist_xs (Some (header.Bool, KD_S_abort))
      (slist_x (Qubit, (g_send Buyer Verif (extendSlis l_ok1 (Qubit, KD_S_verif_choice)))))).

Lemma kd_gtt_end : gttTC g_end gtt_end.
Proof. unfold gttTC. pfold. constructor. Qed.

Lemma kd_gttTC_send : forall p q xs ys,
  (forall n,
    (onth n xs = None /\ ys n = None) \/
    exists s g g', onth n xs = Some (s, g) /\ ys n = Some (s, g') /\ gttTC g g') ->
  gttTC (g_send p q xs) (gtt_send p q ys).
Proof.
  intros p q xs ys H. unfold gttTC. pfold. apply gttT_send. intros n.
  destruct (H n) as [[Hxs Hys] | (s & g & g' & Hxs & Hys & Hrel)].
  - left. split; assumption.
  - right. exists s, g, g'. split; [exact Hxs|]. split; [exact Hys|].
    left. exact Hrel.
Qed.

Lemma kd_tc_abort : gttTC KD_S_abort KD_G_abort.
Proof.
  unfold KD_S_abort, KD_G_abort, l_abort. apply kd_gttTC_send.
  intros [|n]; simpl.
  - right. exists header.Bool, g_end, gtt_end.
    split; [reflexivity|]. split; [reflexivity|exact kd_gtt_end].
  - left. split; reflexivity.
Qed.

Lemma kd_tc_final_env : gttTC KD_S_final_env KD_G_final_env.
Proof.
  unfold KD_S_final_env, KD_G_final_env. apply kd_gttTC_send.
  intros [|[|n]]; simpl.
  - right. exists header.Bool, g_end, gtt_end.
    split; [reflexivity|]. split; [reflexivity|exact kd_gtt_end].
  - right. exists header.Bool, g_end, gtt_end.
    split; [reflexivity|]. split; [reflexivity|exact kd_gtt_end].
  - left. split; reflexivity.
Qed.

Lemma kd_tc_buyer_final_choice :
  gttTC KD_S_buyer_final_choice KD_G_buyer_final_choice.
Proof.
  unfold KD_S_buyer_final_choice, KD_G_buyer_final_choice.
  apply kd_gttTC_send. intros [|[|n]]; simpl.
  - right. exists header.Bool, KD_S_abort, KD_G_abort.
    split; [reflexivity|]. split; [reflexivity|exact kd_tc_abort].
  - right. exists header.Bool, KD_S_final_env, KD_G_final_env.
    split; [reflexivity|]. split; [reflexivity|exact kd_tc_final_env].
  - left. split; reflexivity.
Qed.

Lemma kd_tc_verif_final_qubit :
  gttTC (g_send Verif Buyer (extendSlis l_ok1 (Qubit, KD_S_buyer_final_choice))) KD_G_verif_final_qubit.
Proof.
  unfold KD_G_verif_final_qubit, l_ok1.
  apply kd_gttTC_send. intros [|n]; simpl.
  - right. exists Qubit, KD_S_buyer_final_choice, KD_G_buyer_final_choice.
    split; [reflexivity|]. split; [reflexivity|exact kd_tc_buyer_final_choice].
  - left. split; reflexivity.
Qed.

Lemma kd_tc_verif_choice : gttTC KD_S_verif_choice KD_G_verif_choice.
Proof.
  unfold KD_S_verif_choice, KD_G_verif_choice. apply kd_gttTC_send.
  intros [|[|n]]; simpl.
  - right. exists header.Bool, KD_S_abort, KD_G_abort.
    split; [reflexivity|]. split; [reflexivity|exact kd_tc_abort].
  - right. exists Qubit, (g_send Verif Buyer (extendSlis l_ok1 (Qubit, KD_S_buyer_final_choice))), KD_G_verif_final_qubit.
    split; [reflexivity|]. split; [reflexivity|exact kd_tc_verif_final_qubit].
  - left. split; reflexivity.
Qed.

Lemma kd_tc_buyer_second_qubit :
  gttTC (g_send Buyer Verif (extendSlis l_ok1 (Qubit, KD_S_verif_choice))) KD_G_buyer_second_qubit.
Proof.
  unfold KD_G_buyer_second_qubit, l_ok1.
  apply kd_gttTC_send. intros [|n]; simpl.
  - right. exists Qubit, KD_S_verif_choice, KD_G_verif_choice.
    split; [reflexivity|]. split; [reflexivity|exact kd_tc_verif_choice].
  - left. split; reflexivity.
Qed.

Lemma kd_tc_buyer_choice : gttTC KD_S_buyer_choice KD_G_buyer_choice.
Proof.
  unfold KD_S_buyer_choice, KD_G_buyer_choice. apply kd_gttTC_send.
  intros [|[|n]]; simpl.
  - right. exists header.Bool, KD_S_abort, KD_G_abort.
    split; [reflexivity|]. split; [reflexivity|exact kd_tc_abort].
  - right. exists Qubit, (g_send Buyer Verif (extendSlis l_ok1 (Qubit, KD_S_verif_choice))), KD_G_buyer_second_qubit.
    split; [reflexivity|]. split; [reflexivity|exact kd_tc_buyer_second_qubit].
  - left. split; reflexivity.
Qed.

Lemma key_distribution_global_coind_regular :
  regGtt key_distribution_global_coind.
Proof.
  unfold regGtt. unfold key_distribution_global_coind.
  exists key_distribution_global.
  unfold key_distribution_global, KD_G_buyer_choice, KD_G_buyer_second_qubit,
    KD_G_verif_choice, KD_G_verif_final_qubit, KD_G_buyer_final_choice,
    KD_G_abort, KD_G_final_env.
  unfold l_abort, l_ok, l_ok1, l_PKey_B01, l_PKey_B02, l_PKey_B11,
    l_PKey_B12, l_PKey_V03, l_PKey_V04, l_PKey_V13, l_PKey_V14.
  repeat gttTC_step.
  change (gttTC KD_S_buyer_choice KD_G_buyer_choice).
  exact kd_tc_buyer_choice.
Qed.

Lemma kd_parts_range_send : forall p q f,
  (p = Buyer \/ p = Verif \/ p = Env) ->
  (q = Buyer \/ q = Verif \/ q = Env) ->
  (forall n s g, f n = Some (s,g) ->
     forall pt, isgPartsC pt g -> pt = Buyer \/ pt = Verif \/ pt = Env) ->
  forall pt, isgPartsC pt (gtt_send p q f) ->
    pt = Buyer \/ pt = Verif \/ pt = Env.
Proof.
  intros p q f Hp Hq Hchild pt Hpart.
  inversion Hpart; subst; try tauto.
  eapply Hchild; eauto.
Qed.

Lemma kd_range_abort : forall pt, isgPartsC pt KD_G_abort ->
  pt = Buyer \/ pt = Verif \/ pt = Env.
Proof.
  intros pt H. unfold KD_G_abort, l_abort in *.
  eapply kd_parts_range_send with (p:=Verif) (q:=Env)
    (f:=fun n => if Nat.eqb n 0 then Some (header.Bool, gtt_end) else None).
  - right; left; reflexivity.
  - right; right; reflexivity.
  - intros n s g Hg pt' Hpt. destruct n as [|n]; simpl in Hg; try discriminate.
    inversion Hg; subst. inversion Hpt.
  - exact H.
Qed.

Lemma kd_range_final_env : forall pt, isgPartsC pt KD_G_final_env ->
  pt = Buyer \/ pt = Verif \/ pt = Env.
Proof.
  intros pt H. unfold KD_G_final_env in *.
  eapply kd_parts_range_send with (p:=Verif) (q:=Env)
    (f:=fun n => match n with 0 => Some (header.Bool, gtt_end) | 1 => Some (header.Bool, gtt_end) | _ => None end).
  - right; left; reflexivity.
  - right; right; reflexivity.
  - intros n s g Hg pt' Hpt. destruct n as [|[|n]]; simpl in Hg; try discriminate;
      inversion Hg; subst; inversion Hpt.
  - exact H.
Qed.

Lemma kd_range_buyer_final_choice : forall pt,
  isgPartsC pt KD_G_buyer_final_choice ->
  pt = Buyer \/ pt = Verif \/ pt = Env.
Proof.
  intros pt H. unfold KD_G_buyer_final_choice in *.
  eapply kd_parts_range_send with (p:=Buyer) (q:=Verif)
    (f:=fun n => match n with 0 => Some (header.Bool, KD_G_abort) | 1 => Some (header.Bool, KD_G_final_env) | _ => None end).
  - left; reflexivity.
  - right; left; reflexivity.
  - intros n s g Hg pt' Hpt.
    destruct n as [|[|n]]; simpl in Hg; try discriminate; inversion Hg; subst.
    + eapply kd_range_abort; exact Hpt.
    + eapply kd_range_final_env; exact Hpt.
  - exact H.
Qed.

Lemma kd_range_verif_final_qubit : forall pt,
  isgPartsC pt KD_G_verif_final_qubit ->
  pt = Buyer \/ pt = Verif \/ pt = Env.
Proof.
  intros pt H. unfold KD_G_verif_final_qubit, l_ok1 in *.
  eapply kd_parts_range_send with (p:=Verif) (q:=Buyer)
    (f:=fun n => if Nat.eqb n 0 then Some (Qubit, KD_G_buyer_final_choice) else None).
  - right; left; reflexivity.
  - left; reflexivity.
  - intros n s g Hg pt' Hpt. destruct n as [|n]; simpl in Hg; try discriminate.
    inversion Hg; subst. eapply kd_range_buyer_final_choice; exact Hpt.
  - exact H.
Qed.

Lemma kd_range_verif_choice : forall pt,
  isgPartsC pt KD_G_verif_choice ->
  pt = Buyer \/ pt = Verif \/ pt = Env.
Proof.
  intros pt H. unfold KD_G_verif_choice in *.
  eapply kd_parts_range_send with (p:=Verif) (q:=Buyer)
    (f:=fun n => match n with 0 => Some (header.Bool, KD_G_abort) | 1 => Some (Qubit, KD_G_verif_final_qubit) | _ => None end).
  - right; left; reflexivity.
  - left; reflexivity.
  - intros n s g Hg pt' Hpt.
    destruct n as [|[|n]]; simpl in Hg; try discriminate; inversion Hg; subst.
    + eapply kd_range_abort; exact Hpt.
    + eapply kd_range_verif_final_qubit; exact Hpt.
  - exact H.
Qed.

Lemma kd_range_buyer_second_qubit : forall pt,
  isgPartsC pt KD_G_buyer_second_qubit ->
  pt = Buyer \/ pt = Verif \/ pt = Env.
Proof.
  intros pt H. unfold KD_G_buyer_second_qubit, l_ok1 in *.
  eapply kd_parts_range_send with (p:=Buyer) (q:=Verif)
    (f:=fun n => if Nat.eqb n 0 then Some (Qubit, KD_G_verif_choice) else None).
  - left; reflexivity.
  - right; left; reflexivity.
  - intros n s g Hg pt' Hpt. destruct n as [|n]; simpl in Hg; try discriminate.
    inversion Hg; subst. eapply kd_range_verif_choice; exact Hpt.
  - exact H.
Qed.

Lemma kd_range_buyer_choice : forall pt,
  isgPartsC pt KD_G_buyer_choice ->
  pt = Buyer \/ pt = Verif \/ pt = Env.
Proof.
  intros pt H. unfold KD_G_buyer_choice in *.
  eapply kd_parts_range_send with (p:=Buyer) (q:=Verif)
    (f:=fun n => match n with 0 => Some (header.Bool, KD_G_abort) | 1 => Some (Qubit, KD_G_buyer_second_qubit) | _ => None end).
  - left; reflexivity.
  - right; left; reflexivity.
  - intros n s g Hg pt' Hpt.
    destruct n as [|[|n]]; simpl in Hg; try discriminate; inversion Hg; subst.
    + eapply kd_range_abort; exact Hpt.
    + eapply kd_range_buyer_second_qubit; exact Hpt.
  - exact H.
Qed.

Lemma kd_parts_range_end : forall p q f,
  (forall n s g, f n = Some (s,g) -> forall pt, isgPartsC pt g -> False) ->
  forall pt, isgPartsC pt (gtt_send p q f) -> pt = p \/ pt = q.
Proof.
  intros p q f Hchild pt Hpart.
  inversion Hpart; subst; try tauto.
  exfalso. eapply Hchild; eauto.
Qed.

Lemma kd_range_abort_end : forall pt, isgPartsC pt KD_G_abort ->
  pt = Verif \/ pt = Env.
Proof.
  intros pt H. unfold KD_G_abort, l_abort in *.
  eapply kd_parts_range_end with (p:=Verif) (q:=Env)
    (f:=fun n => if Nat.eqb n 0 then Some (header.Bool, gtt_end) else None).
  - intros n s g Hg pt' Hpt. destruct n; simpl in Hg; try discriminate.
    inversion Hg; subst. inversion Hpt.
  - exact H.
Qed.

Lemma kd_range_final_env_end : forall pt, isgPartsC pt KD_G_final_env ->
  pt = Verif \/ pt = Env.
Proof.
  intros pt H. unfold KD_G_final_env in *.
  eapply kd_parts_range_end with (p:=Verif) (q:=Env)
    (f:=fun n => match n with 0 => Some (header.Bool, gtt_end) | 1 => Some (header.Bool, gtt_end) | _ => None end).
  - intros n s g Hg pt' Hpt. destruct n as [|[|n]]; simpl in Hg; try discriminate;
      inversion Hg; subst; inversion Hpt.
  - exact H.
Qed.

Lemma kd_env_in_abort : isgPartsC Env KD_G_abort.
Proof. unfold KD_G_abort, l_abort. apply pac_sendq. Qed.
Lemma kd_env_in_final_env : isgPartsC Env KD_G_final_env.
Proof. unfold KD_G_final_env. apply pac_sendq. Qed.
Lemma kd_env_in_buyer_final_choice : isgPartsC Env KD_G_buyer_final_choice.
Proof.
  unfold Buyer, Verif, Env. unfold KD_G_buyer_final_choice. eapply pac_sendr with (n:=0) (s:=header.Bool) (g:=KD_G_abort).
  - discriminate.
  - discriminate.
  - reflexivity.
  - exact kd_env_in_abort.
Qed.
Lemma kd_env_in_verif_final_qubit : isgPartsC Env KD_G_verif_final_qubit.
Proof.
  unfold Buyer, Verif, Env. unfold KD_G_verif_final_qubit, l_ok1. eapply pac_sendr with (n:=0) (s:=Qubit) (g:=KD_G_buyer_final_choice).
  - discriminate.
  - discriminate.
  - reflexivity.
  - exact kd_env_in_buyer_final_choice.
Qed.
Lemma kd_env_in_verif_choice : isgPartsC Env KD_G_verif_choice.
Proof.
  unfold Buyer, Verif, Env. unfold KD_G_verif_choice. eapply pac_sendr with (n:=0) (s:=header.Bool) (g:=KD_G_abort).
  - discriminate.
  - discriminate.
  - reflexivity.
  - exact kd_env_in_abort.
Qed.
Lemma kd_env_in_buyer_second_qubit : isgPartsC Env KD_G_buyer_second_qubit.
Proof.
  unfold Buyer, Verif, Env. unfold KD_G_buyer_second_qubit, l_ok1. eapply pac_sendr with (n:=0) (s:=Qubit) (g:=KD_G_verif_choice).
  - discriminate.
  - discriminate.
  - reflexivity.
  - exact kd_env_in_verif_choice.
Qed.
Lemma kd_env_in_buyer_choice : isgPartsC Env KD_G_buyer_choice.
Proof.
  unfold Buyer, Verif, Env. unfold KD_G_buyer_choice. eapply pac_sendr with (n:=0) (s:=header.Bool) (g:=KD_G_abort).
  - discriminate.
  - discriminate.
  - reflexivity.
  - exact kd_env_in_abort.
Qed.

Lemma kd_partsCS_send0 : forall p q f s g,
    f 0 = Some (s, g) -> (forall n, f (S n) = None) ->
    (forall pt, isgPartsC pt g -> isgPartsCS pt g) ->
    forall pt, isgPartsC pt (gtt_send p q f) -> isgPartsCS pt (gtt_send p q f).
Proof.
  intros p q f s g Hzero Hsucc Hchild pt Hparts.
  inversion Hparts; subst.
  - apply pacs_sendp.
  - apply pacs_sendq.
  - apply pacs_sendr; try assumption.
    intros m. destruct m as [|m].
    + right. exists s, g. split; [exact Hzero|].
      apply Hchild.
      destruct n as [|n].
      * simpl in H5. rewrite Hzero in H5. inversion H5. subst. exact H6.
      * rewrite Hsucc in H5. discriminate.
    + rewrite Hsucc. left. reflexivity.
Qed.

Lemma kd_parts_abort : forall pt, isgPartsC pt KD_G_abort -> isgPartsCS pt KD_G_abort.
Proof.
  intros pt H. unfold KD_G_abort, l_abort.
  apply kd_partsCS_send0 with (s:=header.Bool) (g:=gtt_end).
  - reflexivity.
  - intros n. reflexivity.
  - intros pt' Hpt. inversion Hpt.
  - exact H.
Qed.

Lemma kd_parts_final_env : forall pt, isgPartsC pt KD_G_final_env -> isgPartsCS pt KD_G_final_env.
Proof.
  intros pt H. destruct (kd_range_final_env_end pt H) as [Hpt|Hpt]; subst;
    [apply pacs_sendp|apply pacs_sendq].
Qed.

Lemma kd_parts_buyer_final_choice : forall pt,
  isgPartsC pt KD_G_buyer_final_choice -> isgPartsCS pt KD_G_buyer_final_choice.
Proof.
  intros pt Hroot.
  destruct (participant_dec pt Buyer) as [->|HnotBuyer].
  - apply pacs_sendp.
  - destruct (participant_dec pt Verif) as [->|HnotVerif].
    + apply pacs_sendq.
    + assert (HptEnv : pt = Env).
      { destruct (kd_range_buyer_final_choice pt Hroot) as [Heq|[Heq|Heq]];
          subst; congruence. }
      subst pt. unfold Buyer, Verif, Env. unfold KD_G_buyer_final_choice.
      apply pacs_sendr.
      * discriminate.
      * discriminate.
      * intros [|[|n]]; simpl.
      * right. exists header.Bool, KD_G_abort. split; [reflexivity|].
        apply kd_parts_abort. exact kd_env_in_abort.
      * right. exists header.Bool, KD_G_final_env. split; [reflexivity|].
        apply kd_parts_final_env. exact kd_env_in_final_env.
      * left. reflexivity.
Qed.

Lemma kd_parts_verif_final_qubit : forall pt,
  isgPartsC pt KD_G_verif_final_qubit -> isgPartsCS pt KD_G_verif_final_qubit.
Proof.
  intros pt Hroot.
  destruct (participant_dec pt Verif) as [->|HnotVerif].
  - apply pacs_sendp.
  - destruct (participant_dec pt Buyer) as [->|HnotBuyer].
    + apply pacs_sendq.
    + assert (HptEnv : pt = Env).
      { destruct (kd_range_verif_final_qubit pt Hroot) as [Heq|[Heq|Heq]];
          subst; congruence. }
      subst pt. unfold Buyer, Verif, Env. unfold KD_G_verif_final_qubit, l_ok1.
      apply pacs_sendr.
      * discriminate.
      * discriminate.
      * intros [|n]; simpl.
      * right. exists Qubit, KD_G_buyer_final_choice. split; [reflexivity|].
        apply kd_parts_buyer_final_choice. exact kd_env_in_buyer_final_choice.
      * left. reflexivity.
Qed.

Lemma kd_parts_verif_choice : forall pt,
  isgPartsC pt KD_G_verif_choice -> isgPartsCS pt KD_G_verif_choice.
Proof.
  intros pt Hroot.
  destruct (participant_dec pt Verif) as [->|HnotVerif].
  - apply pacs_sendp.
  - destruct (participant_dec pt Buyer) as [->|HnotBuyer].
    + apply pacs_sendq.
    + assert (HptEnv : pt = Env).
      { destruct (kd_range_verif_choice pt Hroot) as [Heq|[Heq|Heq]];
          subst; congruence. }
      subst pt. unfold Buyer, Verif, Env. unfold KD_G_verif_choice.
      apply pacs_sendr.
      * discriminate.
      * discriminate.
      * intros [|[|n]]; simpl.
      * right. exists header.Bool, KD_G_abort. split; [reflexivity|].
        apply kd_parts_abort. exact kd_env_in_abort.
      * right. exists Qubit, KD_G_verif_final_qubit. split; [reflexivity|].
        apply kd_parts_verif_final_qubit. exact kd_env_in_verif_final_qubit.
      * left. reflexivity.
Qed.

Lemma kd_parts_buyer_second_qubit : forall pt,
  isgPartsC pt KD_G_buyer_second_qubit -> isgPartsCS pt KD_G_buyer_second_qubit.
Proof.
  intros pt Hroot.
  destruct (participant_dec pt Buyer) as [->|HnotBuyer].
  - apply pacs_sendp.
  - destruct (participant_dec pt Verif) as [->|HnotVerif].
    + apply pacs_sendq.
    + assert (HptEnv : pt = Env).
      { destruct (kd_range_buyer_second_qubit pt Hroot) as [Heq|[Heq|Heq]];
          subst; congruence. }
      subst pt. unfold Buyer, Verif, Env. unfold KD_G_buyer_second_qubit, l_ok1.
      apply pacs_sendr.
      * discriminate.
      * discriminate.
      * intros [|n]; simpl.
      * right. exists Qubit, KD_G_verif_choice. split; [reflexivity|].
        apply kd_parts_verif_choice. exact kd_env_in_verif_choice.
      * left. reflexivity.
Qed.

Lemma kd_parts_buyer_choice : forall pt,
  isgPartsC pt KD_G_buyer_choice -> isgPartsCS pt KD_G_buyer_choice.
Proof.
  intros pt Hroot.
  destruct (participant_dec pt Buyer) as [->|HnotBuyer].
  - apply pacs_sendp.
  - destruct (participant_dec pt Verif) as [->|HnotVerif].
    + apply pacs_sendq.
    + assert (HptEnv : pt = Env).
      { destruct (kd_range_buyer_choice pt Hroot) as [Heq|[Heq|Heq]];
          subst; congruence. }
      subst pt. unfold Buyer, Verif, Env. unfold KD_G_buyer_choice.
      apply pacs_sendr.
      * discriminate.
      * discriminate.
      * intros [|[|n]]; simpl.
      * right. exists header.Bool, KD_G_abort. split; [reflexivity|].
        apply kd_parts_abort. exact kd_env_in_abort.
      * right. exists Qubit, KD_G_buyer_second_qubit. split; [reflexivity|].
        apply kd_parts_buyer_second_qubit. exact kd_env_in_buyer_second_qubit.
      * left. reflexivity.
Qed.

(* Regularity passes to every live continuation. *)
Lemma kd_regular_branch : forall p q f n s g,
  regGtt (gtt_send p q f) -> f n = Some (s, g) -> regGtt g.
Proof.
  intros p q f n s g Hr Hf.
  destruct (regGtt_cont p q f Hr n) as [Hnone | (s' & g' & Heq & Hrg)].
  - rewrite Hf in Hnone. discriminate.
  - rewrite Hf in Heq. inversion Heq. exact Hrg.
Qed.

(* Adding a singleton communication preserves these two suffix properties. *)
Lemma kd_balanced_send0 : forall p q s g,
  regGtt (gtt_send p q (fun n => if Nat.eqb n 0 then Some (s, g) else None)) ->
  (forall pt, isgPartsC pt g -> isgPartsCS pt g) ->
  balancedG g ->
  balancedG (gtt_send p q (fun n => if Nat.eqb n 0 then Some (s, g) else None)).
Proof.
  intros p q s g Hreg Hparts Hbal.
  apply balanced_up.
  - intros [|n]; simpl.
    + right. exists s, g. split; [reflexivity|exact Hbal].
    + left. reflexivity.
  - exact Hreg.
  - eapply kd_partsCS_send0; [reflexivity|intros n; reflexivity|exact Hparts].
Qed.

Lemma key_distribution_global_coind_balanced : balancedG key_distribution_global_coind.
Proof.
  (* Prove the branching suffixes once, working backwards from termination. *)
  assert (Hbal_end : balancedG gtt_end).
  { unfold balancedG. intros w w' p q [Hmap|Hmap]; inversion Hmap. }

  Local Ltac kd_balance_suffix syntax typing parts :=
    apply balanced_up;
    [intros [|[|n]]; simpl;
     first [left; reflexivity
           |right; do 2 eexists; split; [reflexivity|assumption]]
    |exists syntax; exact typing
    |exact parts].

  assert (Hbal_abort : balancedG KD_G_abort).
  { unfold KD_G_abort, l_abort.
    kd_balance_suffix KD_S_abort kd_tc_abort kd_parts_abort. }
  assert (Hbal_final_env : balancedG KD_G_final_env).
  { unfold KD_G_final_env.
    kd_balance_suffix KD_S_final_env kd_tc_final_env kd_parts_final_env. }
  assert (Hbal_buyer_final_choice : balancedG KD_G_buyer_final_choice).
  { unfold KD_G_buyer_final_choice.
    kd_balance_suffix KD_S_buyer_final_choice kd_tc_buyer_final_choice kd_parts_buyer_final_choice. }
  assert (Hbal_verif_final_qubit : balancedG KD_G_verif_final_qubit).
  { unfold KD_G_verif_final_qubit, l_ok1.
    kd_balance_suffix (g_send Verif Buyer (extendSlis l_ok1 (Qubit, KD_S_buyer_final_choice))) kd_tc_verif_final_qubit kd_parts_verif_final_qubit. }
  assert (Hbal_verif_choice : balancedG KD_G_verif_choice).
  { unfold KD_G_verif_choice.
    kd_balance_suffix KD_S_verif_choice kd_tc_verif_choice kd_parts_verif_choice. }
  assert (Hbal_buyer_second_qubit : balancedG KD_G_buyer_second_qubit).
  { unfold KD_G_buyer_second_qubit, l_ok1.
    kd_balance_suffix (g_send Buyer Verif (extendSlis l_ok1 (Qubit, KD_S_verif_choice))) kd_tc_buyer_second_qubit kd_parts_buyer_second_qubit. }
  assert (Hbal_buyer_choice : balancedG KD_G_buyer_choice).
  { unfold KD_G_buyer_choice.
    kd_balance_suffix KD_S_buyer_choice kd_tc_buyer_choice kd_parts_buyer_choice. }

  (* Carry regularity forward and balance backwards through the eight sends. *)
  pose proof key_distribution_global_coind_regular as Hreg.
  unfold key_distribution_global_coind in *.
  revert Hreg.
  do 8 (
    intro Hreg;
    pose proof (kd_regular_branch _ _ _ 0 _ _ Hreg eq_refl) as Hchild;
    apply kd_balanced_send0;
    [exact Hreg
    |repeat (eapply kd_partsCS_send0;
       [reflexivity|intros n; reflexivity|]); exact kd_parts_buyer_choice
    |clear Hreg; revert Hchild]).
  intro Hreg. exact Hbal_buyer_choice.
Qed.

Definition L_S : ltt :=
(ltt_send Buyer (fun n => onth n (extendSlis l_PKey_B01 (Qubit, (ltt_send Buyer (fun n => onth n (extendSlis l_PKey_B02 (Qubit, (ltt_send Buyer (fun n => onth n (extendSlis l_PKey_B11 (Qubit, (ltt_send Buyer (fun n => onth n (extendSlis l_PKey_B12 (Qubit, (ltt_send Verif (fun n => onth n (extendSlis l_PKey_V03 (Qubit, (ltt_send Verif (fun n => onth n (extendSlis l_PKey_V04 (Qubit, (ltt_send Verif (fun n => onth n (extendSlis l_PKey_V13 (Qubit, (ltt_send Verif (fun n => onth n (extendSlis l_PKey_V14 (Qubit, ltt_end)))))))))))))))))))))))))))))))).

Definition L_B : ltt :=
(ltt_recv Seller (fun n => onth n (extendSlis l_PKey_B01 (Qubit, (ltt_recv Seller (fun n => onth n (extendSlis l_PKey_B02 (Qubit, (ltt_recv Seller (fun n => onth n (extendSlis l_PKey_B11 (Qubit, (ltt_recv Seller (fun n => onth n (extendSlis l_PKey_B12 (Qubit, (ltt_send Verif (fun n => onth n (slist_xs (Some (header.Bool, ltt_end)) (slist_x (Qubit, (ltt_send Verif (fun n => onth n (extendSlis l_ok1 (Qubit, (ltt_recv Verif (fun n => onth n (slist_xs (Some (header.Bool, ltt_end)) (slist_x (Qubit, (ltt_recv Verif (fun n => onth n (extendSlis l_ok1 (Qubit, (ltt_send Verif (fun n => onth n (slist_xs (Some (header.Bool, ltt_end)) (slist_x (header.Bool, ltt_end))))))))))))))))))))))))))))))))))))))).

Definition L_V : ltt :=
(ltt_recv Seller (fun n => onth n (extendSlis l_PKey_V03 (Qubit, (ltt_recv Seller (fun n => onth n (extendSlis l_PKey_V04 (Qubit, (ltt_recv Seller (fun n => onth n (extendSlis l_PKey_V13 (Qubit, (ltt_recv Seller (fun n => onth n (extendSlis l_PKey_V14 (Qubit, (ltt_recv Buyer (fun n => onth n (slist_xs (Some (header.Bool, (ltt_send Env (fun n => onth n (extendSlis l_abort (header.Bool, ltt_end)))))) (slist_x (Qubit, (ltt_recv Buyer (fun n => onth n (extendSlis l_ok1 (Qubit, (ltt_send Buyer (fun n => onth n (slist_xs (Some (header.Bool, (ltt_send Env (fun n => onth n (extendSlis l_abort (header.Bool, ltt_end)))))) (slist_x (Qubit, (ltt_send Buyer (fun n => onth n (extendSlis l_ok1 (Qubit, (ltt_recv Buyer (fun n => onth n (slist_xs (Some (header.Bool, (ltt_send Env (fun n => onth n (extendSlis l_abort (header.Bool, ltt_end)))))) (slist_x (header.Bool, (ltt_send Env (fun n => onth n (slist_xs (Some (header.Bool, ltt_end)) (slist_x (header.Bool, ltt_end)))))))))))))))))))))))))))))))))))))))))))).

Definition L_E : ltt :=
(ltt_recv Verif (fun n => onth n (slist_xs (Some (header.Bool, ltt_end)) (slist_x (header.Bool, ltt_end))))).

Definition L_E_abort : ltt :=
  ltt_recv Verif (fun n => if Nat.eqb n l_abort then Some (header.Bool, ltt_end) else None).

(* Process typing proofs are split at protocol phases so that each proof
   handles only the local operation and context change at that point. *)
Lemma P_E_typecheck :
  typecheck_process empty_context P_E L_E.
Proof.
  unfold P_E, L_E.
  apply T_recv.
  apply SForall2_sxs.
  - apply T_end.
    + intros z. split; [contradiction|].
      intros Hexpr. inversion Hexpr; subst.
      all: unfold in_variable_context, in_qubit_context,
        insert_into_variable_context, empty_context in *;
        simpl in *; try destruct x as [|x]; simpl in *;
        try destruct x as [|x]; simpl in *; try congruence.
    + apply NoDup_nil.
  - apply SForall2_x.
    + apply T_end.
      * intros z. split; [contradiction|].
        intros Hexpr. inversion Hexpr; subst.
        all: unfold in_variable_context, in_qubit_context,
          insert_into_variable_context, empty_context in *;
          simpl in *; try destruct x as [|x]; simpl in *;
          try destruct x as [|x]; simpl in *; try congruence.
      * apply NoDup_nil.
Qed.

Lemma send0_slist_x_subtype :
  forall p B T,
    subtypeC
      (ltt_send p (fun n => if Nat.eqb n 0 then Some (B, T) else None))
      (ltt_send p (fun n => onth n (slist_x (B, T)))).
Proof.
  intros p B T. unfold subtypeC. pfold. apply sub_out.
  intros [|n]; simpl.
  - right. exists B, T, T. repeat split; try reflexivity.
    left. apply stRefl.
  - left. reflexivity.
Qed.

Lemma send_branch0_subtype :
  forall p B0 T0 B1 T1,
    subtypeC
      (ltt_send p (fun n => if Nat.eqb n 0 then Some (B0, T0) else None))
      (ltt_send p
        (fun n => onth n (slist_xs (Some (B0, T0)) (slist_x (B1, T1))))).
Proof.
  intros p B0 T0 B1 T1.
  unfold subtypeC. pfold. apply sub_out.
  intros [|[|n]]; simpl.
  - right. exists B0, T0, T0. repeat split; try reflexivity.
    left. apply stRefl.
  - left. reflexivity.
  - left. reflexivity.
Qed.

Lemma send_branch1_subtype :
  forall p B0 T0 B1 T1,
    subtypeC
      (ltt_send p (fun n => if Nat.eqb n 1 then Some (B1, T1) else None))
      (ltt_send p
        (fun n => onth n (slist_xs (Some (B0, T0)) (slist_x (B1, T1))))).
Proof.
  intros p B0 T0 B1 T1.
  unfold subtypeC. pfold. apply sub_out.
  intros [|[|n]]; simpl.
  - left. reflexivity.
  - right. exists B1, T1, T1. repeat split; try reflexivity.
    left. apply stRefl.
  - left. reflexivity.
Qed.

Lemma send0_extend_typecheck :
  forall (context : typechecking_context) (p : participant) (e : expression)
         (P : process) (B : sort) (T : ltt),
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
    typecheck_process context (p_send p 0 e P)
      (ltt_send p (fun n => onth n (extendSlis 0 (B, T)))).
Proof.
  intros context p e P B T He Hproc.
  eapply T_sub with
    (T := ltt_send p (fun n => if Nat.eqb n 0 then Some (B, T) else None)).
  - eapply T_send; eauto.
  - unfold subtypeC. pfold. apply sub_out.
    intros [|n]; simpl.
    + right. exists B, T, T. repeat split; try reflexivity.
      left. apply stRefl.
    + left. reflexivity.
Qed.

Lemma p_end_verif_initial_abort_typecheck :
  typecheck_process
    (nil,
     Some header.Bool :: Some header.Bool :: None :: Some header.Bool :: None ::
       Some Qubit :: Some Qubit :: Some Qubit :: Some Qubit :: nil,
     empty_fmap)
    (p_end (Var 8 :: Var 7 :: Var 6 :: Var 5 :: nil)) ltt_end.
Proof.
  apply T_end.
  - intros z. split.
    + simpl. intros [Hz | [Hz | [Hz | [Hz | Hz]]]]; try contradiction;
        subst z; apply TE_Var; unfold in_variable_context; simpl; reflexivity.
    + intros Hexpr. inversion Hexpr; subst.
      * unfold in_qubit_context in H. simpl in H. discriminate.
      * unfold in_variable_context in H. simpl in H.
        destruct x as [|[|[|[|[|[|[|[|[|[|x]]]]]]]]]];
          simpl in H; try discriminate; simpl; intuition.
  - repeat constructor; simpl; intuition discriminate.
Qed.

Lemma p_end_verif_measure_abort_typecheck :
  typecheck_process
    (nil,
     Some Qubit :: Some Qubit :: Some header.Bool :: None :: Some header.Bool :: None ::
       Some Qubit :: Some Qubit :: Some Qubit :: Some Qubit :: nil,
     empty_fmap)
    (p_end (Var 9 :: Var 8 :: Var 7 :: Var 6 :: Var 1 :: Var 0 :: nil)) ltt_end.
Proof.
  apply T_end.
  - intros z. split.
    + simpl. intros [Hz | [Hz | [Hz | [Hz | [Hz | [Hz | Hz]]]]]];
        try contradiction; subst z; apply TE_Var;
        unfold in_variable_context; simpl; reflexivity.
    + intros Hexpr. inversion Hexpr; subst.
      * unfold in_qubit_context in H. simpl in H. discriminate.
      * unfold in_variable_context in H. simpl in H.
        destruct x as [|[|[|[|[|[|[|[|[|[|[|x]]]]]]]]]]];
          simpl in H; try discriminate; simpl; intuition.
  - repeat constructor; simpl; intuition discriminate.
Qed.

Lemma p_end_verif_postselection_abort_typecheck :
  typecheck_process
    (nil,
     Some header.Bool :: Some Qubit :: Some Qubit :: Some header.Bool :: None ::
       Some header.Bool :: None :: Some Qubit :: None :: Some Qubit :: None :: nil,
     empty_fmap)
    (p_end (Var 9 :: Var 7 :: Var 2 :: Var 1 :: nil)) ltt_end.
Proof.
  apply T_end.
  - intros z. split.
    + simpl. intros [Hz | [Hz | [Hz | [Hz | Hz]]]]; try contradiction;
        subst z; apply TE_Var; unfold in_variable_context; simpl; reflexivity.
    + intros Hexpr. inversion Hexpr; subst.
      * unfold in_qubit_context in H. simpl in H. discriminate.
      * unfold in_variable_context in H. simpl in H.
        destruct x as [|[|[|[|[|[|[|[|[|[|[|x]]]]]]]]]]];
          simpl in H; try discriminate; simpl; intuition.
        all: try solve [destruct x; simpl in H; discriminate].
  - repeat constructor.
    all: simpl; intros Hin; repeat split_ors; try contradiction;
      try (injection Hin; lia).
    all: try match goal with
      | [H : Var _ = Var _ |- _] => injection H; lia
      end.
Qed.

Lemma p_end_verif_success_typecheck :
  typecheck_process
    (nil,
     Some header.Bool :: None :: Some header.Bool :: None :: Some header.Bool ::
       Some Qubit :: Some Qubit :: Some header.Bool :: None :: Some header.Bool :: None ::
       Some Qubit :: None :: Some Qubit :: None :: nil,
     empty_fmap)
    (p_end (Var 13 :: Var 11 :: Var 6 :: Var 5 :: nil)) ltt_end.
Proof.
  apply T_end.
  - intros z. split.
    + simpl. intros [Hz | [Hz | [Hz | [Hz | Hz]]]]; try contradiction;
        subst z; apply TE_Var; unfold in_variable_context; simpl; reflexivity.
    + intros Hexpr. inversion Hexpr; subst.
      * unfold in_qubit_context in H. simpl in H. discriminate.
      * unfold in_variable_context in H. simpl in H.
        destruct x as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|x]]]]]]]]]]]]]]];
          simpl in H; try discriminate; simpl; intuition.
        all: try solve [destruct x; simpl in H; discriminate].
  - repeat constructor.
    all: simpl; intros Hin; repeat split_ors; try contradiction.
    all: try match goal with
      | [H : Var _ = Var _ |- _] => injection H; lia
      end.
Qed.

Definition L_V_final_env_send : ltt :=
  ltt_send Env
    (fun n => onth n
      (slist_xs (Some (header.Bool, ltt_end))
        (slist_x (header.Bool, ltt_end)))).

Definition L_V_postselect_abort_send : ltt :=
  ltt_send Env (fun n => onth n (slist_x (header.Bool, ltt_end))).

Definition L_V_postselect_receive : ltt :=
  ltt_recv Buyer
    (fun n => onth n
      (slist_xs (Some (header.Bool, L_V_postselect_abort_send))
        (slist_x (header.Bool, L_V_final_env_send)))).

Definition L_V_postselect_second_send : ltt :=
  ltt_send Buyer
    (fun n => onth n (slist_x (Qubit, L_V_postselect_receive))).

Definition P_V_buyer_choice : process :=
  (Buyer .& {
    0 => (Env .+ l_abort <.UNIT.>;
      (p_end ((Var 8) :: (Var 7) :: (Var 6) :: (Var 5) :: nil)))
  | 1 => (Buyer .& l_ok1 .;
      (IF (Op Or (Var 4 :: Var 2 :: nil))
        THEN (Buyer .+ l_abort <.UNIT.>;
          (Env .+ l_abort <.UNIT.>;
            (p_end ((Var 9) :: (Var 8) :: (Var 7) :: (Var 6) ::
              (Var 1) :: (Var 0) :: nil))))
        ELSE (Buyer .+ l_ok <.(Var 9).>;
          (Buyer .+ l_ok1 <.(Var 7).>;
            (Buyer .& {
              0 => (Env .+ l_abort <.UNIT.>;
                (p_end ((Var 9) :: (Var 7) :: (Var 2) :: (Var 1) :: nil)))
            | 1 => (QS (Var 2) (Var 9)
                (QS (Var 3) (Var 9)
                  (IF (Op Or (Var 2 :: Var 0 :: nil))
                    THEN (Env .+ l_abort <.UNIT.>;
                      (p_end ((Var 13) :: (Var 11) :: (Var 6) :: (Var 5) :: nil)))
                    ELSE (Env .+ l_ok <.UNIT.>;
                      (p_end ((Var 13) :: (Var 11) :: (Var 6) :: (Var 5) :: nil))))))
            })))))
  }).

Definition L_V_buyer_if_send : ltt :=
  ltt_send Buyer (fun n => onth n
    (slist_xs (Some (header.Bool, L_V_postselect_abort_send))
      (slist_x (Qubit, L_V_postselect_second_send)))).

Definition L_V_buyer_choice : ltt :=
  ltt_recv Buyer (fun n => onth n
    (slist_xs (Some (header.Bool, L_V_postselect_abort_send))
      (slist_x (Qubit, (Buyer .&. l_ok1(.Qubit.); L_V_buyer_if_send))))).

Lemma P_V_final_env_send0_typecheck :
  typecheck_process
    (nil,
     Some header.Bool :: None :: Some header.Bool :: None :: Some header.Bool ::
       Some Qubit :: Some Qubit :: Some header.Bool :: None :: Some header.Bool :: None ::
       Some Qubit :: None :: Some Qubit :: None :: nil,
     empty_fmap)
    (p_send Env 0 UNIT (p_end (Var 13 :: Var 11 :: Var 6 :: Var 5 :: nil)))
    L_V_final_env_send.
Proof.
  eapply T_sub with
    (T := ltt_send Env
      (fun n => if Nat.eqb n 0 then Some (header.Bool, ltt_end) else None)).
  - eapply typecheck_process_send_unit_step.
    exact p_end_verif_success_typecheck.
  - apply send_branch0_subtype.
Qed.

Lemma P_V_final_env_send1_typecheck :
  typecheck_process
    (nil,
     Some header.Bool :: None :: Some header.Bool :: None :: Some header.Bool ::
       Some Qubit :: Some Qubit :: Some header.Bool :: None :: Some header.Bool :: None ::
       Some Qubit :: None :: Some Qubit :: None :: nil,
     empty_fmap)
    (p_send Env 1 UNIT (p_end (Var 13 :: Var 11 :: Var 6 :: Var 5 :: nil)))
    L_V_final_env_send.
Proof.
  eapply T_sub with
    (T := ltt_send Env
      (fun n => if Nat.eqb n 1 then Some (header.Bool, ltt_end) else None)).
  - eapply typecheck_process_send_unit_step.
    exact p_end_verif_success_typecheck.
  - apply send_branch1_subtype.
Qed.

Lemma P_V_final_measurement_typecheck :
  typecheck_process
    (nil,
     Some header.Bool :: Some Qubit :: Some Qubit :: Some header.Bool :: None ::
       Some header.Bool :: None :: Some Qubit :: None :: Some Qubit :: None :: nil,
     empty_fmap)
    (QS (Var 2) (Var 9)
      (QS (Var 3) (Var 9)
        (IF (Op Or (Var 2 :: Var 0 :: nil))
          THEN (Env .+ 0 <. UNIT .>; (p_end (Var 13 :: Var 11 :: Var 6 :: Var 5 :: nil)))
          ELSE (Env .+ 1 <. UNIT .>; (p_end (Var 13 :: Var 11 :: Var 6 :: Var 5 :: nil))))))
    L_V_final_env_send.
Proof.
  unfold QS, do_CSWAP, do_Toffoli.
  repeat (intros; match goal with
  | [|- typecheck_process _
       (p_send Env 0 UNIT (p_end (Var 13 :: Var 11 :: Var 6 :: Var 5 :: nil))) _] =>
      cbv [insert_into_variable_context remove_from_variable_context empty_context];
      exact P_V_final_env_send0_typecheck
  | [|- typecheck_process _
       (p_send Env 1 UNIT (p_end (Var 13 :: Var 11 :: Var 6 :: Var 5 :: nil))) _] =>
      cbv [insert_into_variable_context remove_from_variable_context empty_context];
      exact P_V_final_env_send1_typecheck
  | [|- typecheck_process _ (p_end _) _] => idtac
  | [H : context [in_variable_context] |- _] => idtac
  | [|- _] => constructor
  end);
  unfold in_variable_context, in_qubit_context in *;
  simpl in *;
  repeat case_analysis; cleanup; eauto;
  try solve [intros HNot; inversion HNot; congruence];
  eauto;
  intros; repeat split_ors; cleanup;
  try (inversion H; subst; cbv in *; cleanup; repeat case_analysis; cleanup).
Qed.

Lemma P_V_buyer_choice_typecheck :
  typecheck_process
    (nil,
     Some header.Bool :: None :: Some header.Bool :: None ::
       Some Qubit :: Some Qubit :: Some Qubit :: Some Qubit :: nil,
     empty_fmap)
    P_V_buyer_choice L_V_buyer_choice.
Proof.
  unfold P_V_buyer_choice, L_V_buyer_choice.
  unfold l_abort, l_ok, l_ok1.
  apply T_recv. apply SForall2_sxs.
  - eapply T_sub with
      (T := ltt_send Env
        (fun n => if Nat.eqb n 0 then Some (header.Bool, ltt_end) else None)).
    + eapply typecheck_process_send_unit_step.
      cbv [insert_into_variable_context empty_context].
      exact p_end_verif_initial_abort_typecheck.
    + apply send0_slist_x_subtype.
  - apply SForall2_x.
    apply T_recv. apply SForall2_x.
    apply T_if.
    + apply TE_Op_Or; apply TE_Var;
        unfold in_variable_context; simpl; reflexivity.
    + eapply T_sub with
        (T := ltt_send Buyer
          (fun n => if Nat.eqb n 0 then
            Some (header.Bool, L_V_postselect_abort_send) else None)).
      * eapply typecheck_process_send_unit_step.
        eapply T_sub with
          (T := ltt_send Env
            (fun n => if Nat.eqb n 0 then Some (header.Bool, ltt_end) else None)).
        -- eapply typecheck_process_send_unit_step.
           exact p_end_verif_measure_abort_typecheck.
        -- apply send0_slist_x_subtype.
      * apply send_branch0_subtype.
    + eapply T_sub with
        (T := ltt_send Buyer
          (fun n => if Nat.eqb n 1 then
            Some (Qubit, L_V_postselect_second_send) else None)).
      * eapply T_send with (B := Qubit).
        -- apply TE_Var. unfold in_variable_context. simpl.
           repeat case_analysis; reflexivity.
        -- eapply send0_extend_typecheck with (B := Qubit)
             (T := L_V_postselect_receive).
           ++ apply TE_Var. unfold in_variable_context. simpl.
              repeat case_analysis; reflexivity.
           ++ apply T_recv. apply SForall2_sxs.
              ** eapply T_sub with
                   (T := ltt_send Env
                     (fun n => if Nat.eqb n 0 then Some (header.Bool, ltt_end) else None)).
                 --- eapply typecheck_process_send_unit_step.
                     cbv [insert_into_variable_context remove_from_variable_context empty_context].
                     exact p_end_verif_postselection_abort_typecheck.
                 --- apply send0_slist_x_subtype.
              ** apply SForall2_x.
                 exact P_V_final_measurement_typecheck.
      * apply send_branch1_subtype.
Qed.

Lemma P_V_initial_measurements_typecheck :
  typecheck_process
    (nil, Some Qubit :: Some Qubit :: Some Qubit :: Some Qubit :: nil, empty_fmap)
    (QS (Var 3) (Var 2)
      (QS (Var 3) (Var 2) P_V_buyer_choice))
    L_V_buyer_choice.
Proof.
  unfold QS, do_CSWAP, do_Toffoli.
  repeat (intros; match goal with
  | [|- typecheck_process _ P_V_buyer_choice _] =>
      cbv [insert_into_variable_context remove_from_variable_context empty_context];
      exact P_V_buyer_choice_typecheck
  | [|- typecheck_process _ (p_end _) _] => idtac
  | [|- _] => constructor
  end);
  unfold in_variable_context, in_qubit_context in *;
  simpl in *;
  repeat case_analysis; cleanup; eauto;
  try solve [intros HNot; inversion HNot; congruence];
  eauto;
  intros; repeat split_ors; cleanup;
  try (inversion H; subst; cbv in *; cleanup; repeat case_analysis; cleanup).
Qed.

Lemma P_V_typecheck :
  typecheck_process empty_context P_V L_V.
Proof.
  unfold P_V, L_V.
  unfold l_PKey_V03, l_PKey_V04, l_PKey_V13, l_PKey_V14.
  fold P_V_buyer_choice L_V_buyer_choice.
  apply T_recv. apply SForall2_x.
  apply T_recv. apply SForall2_x.
  apply T_recv. apply SForall2_x.
  apply T_recv. apply SForall2_x.
  exact P_V_initial_measurements_typecheck.
Qed.

Definition after_qow_send (context : typechecking_context) : typechecking_context :=
  remove_from_variable_context (insert_into_variable_context context Qubit) 0.

Lemma qow_send_typecheck :
  forall (k : list bool) (context : typechecking_context) (p : participant)
         (T : ltt) (cont : process),
    typecheck_process (after_qow_send context) cont T ->
    typecheck_process context
      (qow k (p_send p 0 (Var 0) cont))
      (ltt_send p (fun n => onth n (extendSlis 0 (Qubit, T)))).
Proof.
  intros k context p T cont Hcont.
  eapply T_sub with
    (T := ltt_send p
      (fun n => if Nat.eqb n 0 then Some (Qubit, T) else None)).
  - apply qow_typecheck.
    eapply T_send with (B := Qubit) (T := T).
    + apply TE_Var.
      unfold in_variable_context, insert_into_variable_context.
      simpl. reflexivity.
    + exact Hcont.
  - unfold subtypeC. pfold. apply sub_out.
    intros [|n]; simpl.
    + right. exists Qubit, T, T. repeat split; try reflexivity.
      left. apply stRefl.
    + left. reflexivity.
Qed.

Lemma after_qow_send_preserves_no_qubit_vars :
  forall context,
    (forall x, ~ in_variable_context context x Qubit) ->
    forall x, ~ in_variable_context (after_qow_send context) x Qubit.
Proof.
  intros context Hfresh [|x] Hlookup.
  - unfold in_variable_context, after_qow_send,
      remove_from_variable_context, insert_into_variable_context in Hlookup.
    simpl in Hlookup. discriminate.
  - unfold in_variable_context, after_qow_send,
      remove_from_variable_context, insert_into_variable_context in Hlookup.
    simpl in Hlookup. eapply Hfresh. exact Hlookup.
Qed.

Lemma p_end_nil_typecheck_qubit_free :
  forall context,
    (forall x, ~ in_variable_context context x Qubit) ->
    (forall q, ~ in_qubit_context context q) ->
    typecheck_process context (p_end nil) ltt_end.
Proof.
  intros context Hvar Hqubit.
  apply T_end.
  - intros z. split.
    + simpl. contradiction.
    + intros Hexpr. inversion Hexpr; subst.
      * exfalso. eapply Hqubit. eassumption.
      * exfalso. eapply Hvar. eassumption.
  - apply NoDup_nil.
Qed.

Lemma P_S_typecheck :
  forall k0 k1,
    typecheck_process empty_context (P_S k0 k1) L_S.
Proof.
  intros k0 k1.
  unfold P_S, L_S.
  unfold l_PKey_B01, l_PKey_B02, l_PKey_B11, l_PKey_B12,
    l_PKey_V03, l_PKey_V04, l_PKey_V13, l_PKey_V14.
  cbn [extendSlis onth].
  repeat eapply qow_send_typecheck.
  eapply p_end_nil_typecheck_qubit_free.
  - repeat apply after_qow_send_preserves_no_qubit_vars.
    intros x Hlookup.
    unfold in_variable_context, empty_context in Hlookup.
    destruct x; simpl in Hlookup; discriminate.
  - intros q Hlookup.
    unfold in_qubit_context, empty_context in Hlookup.
    simpl in Hlookup. discriminate.
Qed.

Lemma p_end_four_received_qubits_typecheck :
  typecheck_process
    (nil,
     Some header.Bool :: None :: Some header.Bool :: None ::
       Some Qubit :: Some Qubit :: Some Qubit :: Some Qubit :: nil,
     empty_fmap)
    (p_end (Var 7 :: Var 6 :: Var 5 :: Var 4 :: nil)) ltt_end.
Proof.
  apply T_end.
  - intros z. split.
    + simpl. intros [Hz | [Hz | [Hz | [Hz | Hz]]]];
        try contradiction; subst z; apply TE_Var;
        unfold in_variable_context; simpl; reflexivity.
    + intros Hexpr. inversion Hexpr; subst.
      * unfold in_qubit_context in H. simpl in H. discriminate.
      * unfold in_variable_context in H. simpl in H.
        destruct x as [|[|[|[|[|[|[|[|[|x]]]]]]]]];
          simpl in H; try discriminate; simpl; intuition.
  - repeat constructor; simpl; intuition discriminate.
Qed.

Lemma p_end_buyer_verified_keys_typecheck :
  typecheck_process
    (nil,
     Some header.Bool :: None :: Some header.Bool :: None ::
       Some Qubit :: Some Qubit :: Some header.Bool :: None ::
       Some header.Bool :: None :: Some Qubit :: None :: Some Qubit :: None :: nil,
     empty_fmap)
    (p_end (Var 12 :: Var 10 :: Var 5 :: Var 4 :: nil)) ltt_end.
Proof.
  apply T_end.
  - intros z. split.
    + simpl. intros [Hz | [Hz | [Hz | [Hz | Hz]]]];
        try contradiction; subst z; apply TE_Var;
        unfold in_variable_context; simpl; reflexivity.
    + intros Hexpr. inversion Hexpr; subst.
      * unfold in_qubit_context in H. simpl in H. discriminate.
      * unfold in_variable_context in H. simpl in H.
        destruct x as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|x]]]]]]]]]]]]]]];
          simpl in H; try discriminate; simpl; intuition.
  - repeat constructor; simpl; intuition discriminate.
Qed.

Lemma p_end_buyer_unverified_keys_typecheck :
  typecheck_process
    (nil,
     Some header.Bool :: Some header.Bool :: None :: Some header.Bool :: None ::
       Some Qubit :: None :: Some Qubit :: None :: nil,
     empty_fmap)
    (p_end (Var 7 :: Var 5 :: nil)) ltt_end.
Proof.
  apply T_end.
  - intros z. split.
    + simpl. intros [Hz | [Hz | Hz]]; try contradiction; subst z; apply TE_Var;
        unfold in_variable_context; simpl; reflexivity.
    + intros Hexpr. inversion Hexpr; subst.
      * unfold in_qubit_context in H. simpl in H. discriminate.
      * unfold in_variable_context in H. simpl in H.
        destruct x as [|[|[|[|[|[|[|[|[|x]]]]]]]]];
          simpl in H; try discriminate; simpl; intuition.
        all: try solve [destruct x; simpl in H; discriminate].
  - constructor.
    + simpl. intros [Heq | []]. injection Heq; lia.
    + constructor.
      * simpl. tauto.
      * constructor.
Qed.

Definition L_B_final_status_send : ltt :=
  ltt_send Verif (fun n => onth n
    (slist_xs (Some (header.Bool, ltt_end))
      (slist_x (header.Bool, ltt_end)))).

Definition L_B_after_second_send : ltt :=
  ltt_recv Verif (fun n => onth n
    (slist_xs (Some (header.Bool, ltt_end))
      (slist_x (Qubit, (Verif .&. l_ok1(.Qubit.); L_B_final_status_send))))).

Definition L_B_after_first_send : ltt :=
  ltt_send Verif (fun n => onth n
    (extendSlis l_ok1 (Qubit, L_B_after_second_send))).

Definition L_B_after_initial_measurements : ltt :=
  ltt_send Verif (fun n => onth n
    (slist_xs (Some (header.Bool, ltt_end))
      (slist_x (Qubit, L_B_after_first_send)))).

Definition P_B_final_measurement : process :=
  (QS (Var 1) (Var 8)
    (QS (Var 2) (Var 8)
      (IF (Op Or (Var 2 :: Var 0 :: nil))
        THEN (Verif .+ l_abort <.UNIT.>;
          (p_end ((Var 12) :: (Var 10) :: (Var 5) :: (Var 4) :: nil)))
        ELSE (Verif .+ l_ok <.UNIT.>;
          (p_end ((Var 12) :: (Var 10) :: (Var 5) :: (Var 4) :: nil)))))).

Definition P_B_after_initial_measurements : process :=
  (IF (Op Or (Var 2 :: Var 0 :: nil))
    THEN (Verif .+ l_abort <.UNIT.>;
      (p_end ((Var 7) :: (Var 6) :: (Var 5) :: (Var 4) :: nil)))
    ELSE (Verif .+ l_ok <.(Var 7).>;
      (Verif .+ l_ok1 <.(Var 5).>;
        (Verif .& {
          0 => (p_end ((Var 7) :: (Var 5) :: nil))
        | 1 => (Verif .& l_ok1 .; P_B_final_measurement)
        })))).

Lemma P_B_final_status_send0_typecheck :
  typecheck_process
    (nil,
     Some header.Bool :: None :: Some header.Bool :: None ::
       Some Qubit :: Some Qubit :: Some header.Bool :: None ::
       Some header.Bool :: None :: Some Qubit :: None :: Some Qubit :: None :: nil,
     empty_fmap)
    (p_send Verif 0 UNIT
      (p_end (Var 12 :: Var 10 :: Var 5 :: Var 4 :: nil)))
    L_B_final_status_send.
Proof.
  eapply T_sub with
    (T := ltt_send Verif
      (fun n => if Nat.eqb n 0 then Some (header.Bool, ltt_end) else None)).
  - eapply typecheck_process_send_unit_step.
    exact p_end_buyer_verified_keys_typecheck.
  - apply send_branch0_subtype.
Qed.

Lemma P_B_final_status_send1_typecheck :
  typecheck_process
    (nil,
     Some header.Bool :: None :: Some header.Bool :: None ::
       Some Qubit :: Some Qubit :: Some header.Bool :: None ::
       Some header.Bool :: None :: Some Qubit :: None :: Some Qubit :: None :: nil,
     empty_fmap)
    (p_send Verif 1 UNIT
      (p_end (Var 12 :: Var 10 :: Var 5 :: Var 4 :: nil)))
    L_B_final_status_send.
Proof.
  eapply T_sub with
    (T := ltt_send Verif
      (fun n => if Nat.eqb n 1 then Some (header.Bool, ltt_end) else None)).
  - eapply typecheck_process_send_unit_step.
    exact p_end_buyer_verified_keys_typecheck.
  - apply send_branch1_subtype.
Qed.

Lemma P_B_final_measurement_typecheck :
  typecheck_process
    (nil,
     Some Qubit :: Some Qubit :: Some header.Bool :: None :: Some header.Bool :: None ::
       Some Qubit :: None :: Some Qubit :: None :: nil,
     empty_fmap)
    P_B_final_measurement L_B_final_status_send.
Proof.
  unfold P_B_final_measurement, l_abort, l_ok, QS, do_CSWAP, do_Toffoli.
  repeat (intros; match goal with
  | [|- typecheck_process _
       (p_send Verif 0 UNIT
         (p_end (Var 12 :: Var 10 :: Var 5 :: Var 4 :: nil))) _] =>
      cbv [insert_into_variable_context remove_from_variable_context empty_context];
      exact P_B_final_status_send0_typecheck
  | [|- typecheck_process _
       (p_send Verif 1 UNIT
         (p_end (Var 12 :: Var 10 :: Var 5 :: Var 4 :: nil))) _] =>
      cbv [insert_into_variable_context remove_from_variable_context empty_context];
      exact P_B_final_status_send1_typecheck
  | [|- typecheck_process _ (p_end _) _] => idtac
  | [|- _] => constructor
  end);
  unfold in_variable_context, in_qubit_context in *;
  simpl in *;
  repeat case_analysis; cleanup; eauto;
  try solve [intros HNot; inversion HNot; congruence];
  eauto;
  intros; repeat split_ors; cleanup;
  try (inversion H; subst; cbv in *; cleanup; repeat case_analysis; cleanup).
Qed.

Lemma P_B_after_initial_measurements_typecheck :
  typecheck_process
    (nil,
     Some header.Bool :: None :: Some header.Bool :: None ::
       Some Qubit :: Some Qubit :: Some Qubit :: Some Qubit :: nil,
     empty_fmap)
    P_B_after_initial_measurements L_B_after_initial_measurements.
Proof.
  unfold P_B_after_initial_measurements, L_B_after_initial_measurements.
  unfold l_abort, l_ok, l_ok1.
  apply T_if.
  - apply TE_Op_Or; apply TE_Var;
      unfold in_variable_context; simpl; reflexivity.
  - eapply T_sub with
      (T := ltt_send Verif
        (fun n => if Nat.eqb n 0 then Some (header.Bool, ltt_end) else None)).
    + eapply typecheck_process_send_unit_step.
      exact p_end_four_received_qubits_typecheck.
    + apply send_branch0_subtype.
  - eapply T_sub with
      (T := ltt_send Verif
        (fun n => if Nat.eqb n 1 then Some (Qubit, L_B_after_first_send) else None)).
    + eapply T_send with (B := Qubit).
      * apply TE_Var. unfold in_variable_context. simpl. reflexivity.
      * eapply send0_extend_typecheck with (B := Qubit)
          (T := L_B_after_second_send).
        -- apply TE_Var. unfold in_variable_context. simpl. reflexivity.
        -- apply T_recv. apply SForall2_sxs.
           ++ change (typecheck_process
                (nil,
                 Some header.Bool :: Some header.Bool :: None :: Some header.Bool :: None ::
                   Some Qubit :: None :: Some Qubit :: None :: nil,
                 empty_fmap)
                (p_end (Var 7 :: Var 5 :: nil)) ltt_end).
              exact p_end_buyer_unverified_keys_typecheck.
           ++ apply SForall2_x. apply T_recv. apply SForall2_x.
              exact P_B_final_measurement_typecheck.
    + apply send_branch1_subtype.
Qed.

Lemma P_B_initial_measurements_typecheck :
  typecheck_process
    (nil, Some Qubit :: Some Qubit :: Some Qubit :: Some Qubit :: nil, empty_fmap)
    (QS (Var 3) (Var 2)
      (QS (Var 3) (Var 2) P_B_after_initial_measurements))
    L_B_after_initial_measurements.
Proof.
  unfold QS, do_CSWAP, do_Toffoli.
  repeat (intros; match goal with
  | [|- typecheck_process _ P_B_after_initial_measurements _] =>
      cbv [insert_into_variable_context remove_from_variable_context empty_context];
      exact P_B_after_initial_measurements_typecheck
  | [|- typecheck_process _ (p_end _) _] => idtac
  | [|- _] => constructor
  end);
  unfold in_variable_context, in_qubit_context in *;
  simpl in *;
  repeat case_analysis; cleanup; eauto;
  try solve [intros HNot; inversion HNot; congruence];
  eauto;
  intros; repeat split_ors; cleanup;
  try (inversion H; subst; cbv in *; cleanup; repeat case_analysis; cleanup).
Qed.

Lemma P_B_typecheck :
  typecheck_process empty_context P_B L_B.
Proof.
  unfold P_B, L_B.
  unfold l_abort, l_ok, l_ok1,
    l_PKey_B01, l_PKey_B02, l_PKey_B11, l_PKey_B12.
  fold P_B_after_initial_measurements L_B_after_initial_measurements.
  apply T_recv. apply SForall2_x.
  apply T_recv. apply SForall2_x.
  apply T_recv. apply SForall2_x.
  apply T_recv. apply SForall2_x.
  exact P_B_initial_measurements_typecheck.
Qed.

(* Show that each participant's declared local type is a subtype of its
   projection.  The Env projection merges the abort and success branches. *)
Lemma projection_exists_key_distribution_global_coind :
  forall (pt : participant) (Tlocal : ltt),
  insert (insert (insert (insert empty_fmap Seller L_S) Buyer L_B) Verif L_V) Env L_E pt = Some Tlocal ->
  exists T', @projC coind_full_merge key_distribution_global_coind pt T' /\ subtypeC Tlocal T'.
Proof.
  intros pt Tlocal Hlookup.
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
  assert (Hmerge_end3 : full_merge2 ltt_end ltt_end ltt_end).
  { unfold full_merge2. pfold. constructor. }
  assert (Hmerge_abort_env :
    @isMerge coind_full_merge
      (fun n => match n with 0 => Some L_E_abort | 1 => Some L_E | _ => None end) L_E).
  {
    change (full_merge
      (fun n => match n with 0 => Some L_E_abort | 1 => Some L_E | _ => None end)
      L_E).
    unfold full_merge. exists (slist_xs (Some L_E_abort) (slist_x L_E)). split.
    - intros [|[|n]]; reflexivity.
    - eapply slm_xs with (T':=L_E_abort) (T'':=L_E).
      + unfold full_merge2. pfold. apply cfmer_recv. intros [|[|n]]; simpl.
        * right. right. right. exists header.Bool, ltt_end, ltt_end, ltt_end.
          split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
          left. exact Hmerge_end3.
        * right. right. left. exists (header.Bool,ltt_end).
          split; [reflexivity|]. split; [reflexivity|reflexivity].
        * left. repeat split; reflexivity.
      + constructor.
  }
  assert (Hproj_end : forall p, @projC coind_full_merge gtt_end p ltt_end).
  {
    intros p. unfold projC, projectionC. pfold.
    apply proj_end. intros H. inversion H.
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
  assert (Hout_any : forall p q f f',
      p <> q -> isgPartsC p (gtt_send p q f) ->
      (forall n, (f n = None /\ f' n = None) \/
        exists s g T, f n = Some (s,g) /\ f' n = Some (s,T) /\
          @projC coind_full_merge g p T) ->
      @projC coind_full_merge (gtt_send p q f) p (ltt_send q f')).
  {
    intros p q f f' Hneq Hpart Hbranches.
    unfold projC, projectionC. pfold.
    apply proj_out with (f':=f'); try assumption.
    intros n. destruct (Hbranches n) as [Hnone | (s & g & T & Hf & Hf' & Hproj)].
    - left. exact Hnone.
    - right. exists s,g,T. split; [exact Hf|]. split; [exact Hf'|].
      left. exact Hproj.
  }
  (* A branch table in this protocol has at most two live labels.  The
     projection facts for those labels are proved before each use. *)
  Ltac kd_branch :=
    first [left; split; reflexivity
          |right; do 3 eexists;
           split; [reflexivity|]; split; [reflexivity|]; first [assumption|eauto]].
  Ltac kd_branch_table :=
    let i := fresh "i" in
    let i1 := fresh "i" in
    let i2 := fresh "i" in
    intro i; destruct i as [|i1]; simpl;
    [kd_branch|destruct i1 as [|i2]; simpl; [kd_branch|kd_branch]].

  assert (Hproj_abort_V :
      @projC coind_full_merge KD_G_abort Verif L_V_postselect_abort_send).
  {
    unfold L_V_postselect_abort_send, KD_G_abort, l_abort.
    eapply Hout_any with (f':=fun n => onth n (slist_x (header.Bool,ltt_end))).
    - discriminate.
    - apply pac_sendp.
    - kd_branch_table.
  }
  assert (Hproj_abort_E :
      @projC coind_full_merge KD_G_abort Env L_E_abort).
  {
    unfold L_E_abort, KD_G_abort, l_abort.
    unfold projC, projectionC. pfold.
    apply proj_in with (f':=fun n => if Nat.eqb n 0 then Some (header.Bool,ltt_end) else None).
    - discriminate.
    - apply pac_sendq.
    - intros [|n]; simpl.
      + right. exists header.Bool,gtt_end,ltt_end. repeat split; try reflexivity.
        left. apply Hproj_end.
      + left. split; reflexivity.
  }
  assert (Hproj_final_V :
      @projC coind_full_merge KD_G_final_env Verif L_V_final_env_send).
  {
    unfold L_V_final_env_send, KD_G_final_env.
    eapply Hout_any with
      (f':=fun n => onth n (slist_xs (Some (header.Bool,ltt_end)) (slist_x (header.Bool,ltt_end)))).
    - discriminate.
    - apply pac_sendp.
    - kd_branch_table.
  }
  assert (Hproj_final_E :
      @projC coind_full_merge KD_G_final_env Env L_E).
  {
    unfold L_E, KD_G_final_env.
    unfold projC, projectionC. pfold.
    apply proj_in with
      (f':=fun n => onth n (slist_xs (Some (header.Bool,ltt_end)) (slist_x (header.Bool,ltt_end)))).
    - discriminate.
    - apply pac_sendq.
    - intros [|[|n]]; simpl.
      + right. exists header.Bool,gtt_end,ltt_end. repeat split; try reflexivity.
        left. apply Hproj_end.
      + right. exists header.Bool,gtt_end,ltt_end. repeat split; try reflexivity.
        left. apply Hproj_end.
      + left. split; reflexivity.
  }

  assert (Hout_zero : forall p q f s g T,
      f 0 = Some (s,g) -> (forall n, f (S n)=None) -> p <> q ->
      @projC coind_full_merge g p T ->
      @projC coind_full_merge (gtt_send p q f) p
        (ltt_send q (fun n => onth n (extendSlis 0 (s,T))))).
  {
    intros p q f s g T Hzero Hsucc Hneq Hproj.
    eapply Hout_any with (f':=fun n => onth n (extendSlis 0 (s,T))).
    - exact Hneq.
    - apply pac_sendp.
    - intros [|n]; simpl.
      + right. exists s,g,T. split; [exact Hzero|]. split; [reflexivity|exact Hproj].
      + left. split; [apply Hsucc|reflexivity].
  }
  assert (Hend : forall g r,
      (isgPartsC r g -> False) -> @projC coind_full_merge g r ltt_end).
  {
    intros g r Hnone. unfold projC, projectionC. pfold.
    apply proj_end. exact Hnone.
  }
  assert (Hin_any : forall p r f f',
      p <> r -> isgPartsC r (gtt_send p r f) ->
      (forall n, (f n = None /\ f' n = None) \/
        exists s g T, f n = Some (s,g) /\ f' n = Some (s,T) /\
          @projC coind_full_merge g r T) ->
      @projC coind_full_merge (gtt_send p r f) r (ltt_recv p f')).
  {
    intros p r f f' Hneq Hpart Hbranches.
    unfold projC, projectionC. pfold.
    apply proj_in with (f':=f'); try assumption.
    intros n. destruct (Hbranches n) as [Hnone | (s & g & T & Hf & Hf' & Hproj)].
    - left. exact Hnone.
    - right. exists s,g,T. split; [exact Hf|]. split; [exact Hf'|].
      left. exact Hproj.
  }
  assert (Hskip_any : forall p q r f f' T0,
      p <> q -> q <> r -> p <> r ->
      isgPartsC r (gtt_send p q f) ->
      (forall n, (f n = None /\ f' n = None) \/
        exists s g T, f n = Some (s,g) /\ f' n = Some T /\
          @projC coind_full_merge g r T) ->
      @isMerge coind_full_merge f' T0 ->
      @projC coind_full_merge (gtt_send p q f) r T0).
  {
    intros p q r f f' T0 Hpq Hqr Hpr Hpart Hbranches Hmerge.
    unfold projC, projectionC. pfold.
    apply proj_cont with (f':=f') (t:=T0); try assumption.
    intros n. destruct (Hbranches n) as [Hnone | (s & g & T & Hf & Hf' & Hproj)].
    - left. exact Hnone.
    - right. exists s,g,T. split; [exact Hf|]. split; [exact Hf'|].
      left. exact Hproj.
  }
  assert (Hskip_zero : forall p q r f s g T0,
      f 0 = Some (s,g) -> (forall n, f (S n) = None) ->
      p <> q -> p <> r -> q <> r -> T0 <> ltt_end ->
      @projC coind_full_merge g r T0 ->
      @projC coind_full_merge (gtt_send p q f) r T0).
  {
    intros p q r f s g T0 Hzero Hsucc Hpq Hpr Hqr Hnonend Hproj.
    assert (Hpart_tail : isgPartsC r g).
    { eapply Hparts_of_proj; eauto. }
    assert (Hpart : isgPartsC r (gtt_send p q f)).
    { eapply pac_sendr with (n:=0) (s:=s) (g:=g); eauto. }
    eapply Hskip_any with
      (f':=fun n => if Nat.eqb n 0 then Some T0 else None).
    - exact Hpq.
    - exact Hqr.
    - exact Hpr.
    - exact Hpart.
    - intros [|n]; simpl.
      + right. exists s,g,T0. split; [exact Hzero|]. split; [reflexivity|exact Hproj].
      + left. split; [apply Hsucc|reflexivity].
    - exact (Hsingle T0).
  }
  assert (Hin_zero : forall p q f s g T,
      f 0 = Some (s,g) -> (forall n, f (S n)=None) -> p <> q ->
      @projC coind_full_merge g q T ->
      @projC coind_full_merge (gtt_send p q f) q
        (ltt_recv p (fun n => onth n (extendSlis 0 (s,T))))).
  {
    intros p q f s g T Hzero Hsucc Hneq Hproj.
    eapply Hin_any with (f':=fun n => onth n (extendSlis 0 (s,T))).
    - exact Hneq.
    - apply pac_sendq.
    - intros [|n]; simpl.
      + right. exists s,g,T. split; [exact Hzero|]. split; [reflexivity|exact Hproj].
      + left. split; [apply Hsucc|reflexivity].
  }
  assert (Hproj_abort_B : @projC coind_full_merge KD_G_abort Buyer ltt_end).
  { apply Hend. intros H. destruct (kd_range_abort_end Buyer H) as [Hbad|Hbad]; unfold Buyer, Verif, Env in *; discriminate. }
  assert (Hproj_final_B : @projC coind_full_merge KD_G_final_env Buyer ltt_end).
  { apply Hend. intros H. destruct (kd_range_final_env_end Buyer H) as [Hbad|Hbad]; unfold Buyer, Verif, Env in *; discriminate. }
  assert (Hproj_buyer_final_B :
      @projC coind_full_merge KD_G_buyer_final_choice Buyer L_B_final_status_send).
  {
    unfold L_B_final_status_send, KD_G_buyer_final_choice.
    eapply Hout_any with
      (f':=fun n => onth n (slist_xs (Some (header.Bool,ltt_end)) (slist_x (header.Bool,ltt_end)))).
    - discriminate.
    - apply pac_sendp.
    - kd_branch_table.
  }
  assert (Hproj_buyer_final_V :
      @projC coind_full_merge KD_G_buyer_final_choice Verif L_V_postselect_receive).
  {
    unfold L_V_postselect_receive, KD_G_buyer_final_choice.
    eapply Hin_any with
      (f':=fun n => onth n (slist_xs (Some (header.Bool,L_V_postselect_abort_send))
        (slist_x (header.Bool,L_V_final_env_send)))).
    - discriminate.
    - apply pac_sendq.
    - kd_branch_table.
  }
  assert (Hproj_buyer_final_E :
      @projC coind_full_merge KD_G_buyer_final_choice Env L_E).
  {
    eapply Hskip_any with
      (f':=fun n => match n with 0 => Some L_E_abort | 1 => Some L_E | _ => None end).
    - discriminate.
    - discriminate.
    - discriminate.
    - apply kd_env_in_buyer_final_choice.
    - kd_branch_table.
    - exact Hmerge_abort_env.
  }
  assert (Hnone_buyer_final_S : isgPartsC Seller KD_G_buyer_final_choice -> False).
  { intros H. destruct (kd_range_buyer_final_choice Seller H) as [Hbad|[Hbad|Hbad]]; unfold Seller, Buyer, Verif, Env in *; discriminate. }
  assert (Hproj_buyer_final_S :
      @projC coind_full_merge KD_G_buyer_final_choice Seller ltt_end).
  { apply Hend. exact Hnone_buyer_final_S. }

  assert (Hnone_verif_final_qubit_S : isgPartsC Seller KD_G_verif_final_qubit -> False).
  { intros H. destruct (kd_range_verif_final_qubit Seller H) as [Hbad|[Hbad|Hbad]]; unfold Seller, Buyer, Verif, Env in *; discriminate. }
  assert (Hproj_vfq_V : @projC coind_full_merge KD_G_verif_final_qubit Verif L_V_postselect_second_send).
  {
    unfold L_V_postselect_second_send, KD_G_verif_final_qubit, l_ok1.
    eapply Hout_any with (f':=fun n => onth n (slist_x (Qubit,L_V_postselect_receive))).
    - discriminate.
    - apply pac_sendp.
    - kd_branch_table.
  }
  assert (Hproj_vfq_B : @projC coind_full_merge KD_G_verif_final_qubit Buyer (Verif .&. l_ok1(.Qubit.); L_B_final_status_send)).
  {
    unfold L_B_final_status_send, KD_G_verif_final_qubit, l_ok1.
    eapply Hin_any with (f':=fun n => onth n (extendSlis 0 (Qubit,L_B_final_status_send))).
    - discriminate.
    - apply pac_sendq.
    - kd_branch_table.
  }
  assert (Hproj_vfq_E : @projC coind_full_merge KD_G_verif_final_qubit Env L_E).
  {
    unfold KD_G_verif_final_qubit, l_ok1.
    eapply Hskip_zero with (s:=Qubit) (g:=KD_G_buyer_final_choice).
    - reflexivity.
    - intros n. reflexivity.
    - discriminate.
    - discriminate.
    - discriminate.
    - discriminate.
    - exact Hproj_buyer_final_E.
  }
  assert (Hproj_vfq_S : @projC coind_full_merge KD_G_verif_final_qubit Seller ltt_end).
  { apply Hend. exact Hnone_verif_final_qubit_S. }

  assert (Hnone_verif_choice_S : isgPartsC Seller KD_G_verif_choice -> False).
  { intros H. destruct (kd_range_verif_choice Seller H) as [Hbad|[Hbad|Hbad]]; unfold Seller, Buyer, Verif, Env in *; discriminate. }
  assert (Hproj_vchoice_V : @projC coind_full_merge KD_G_verif_choice Verif L_V_buyer_if_send).
  {
    unfold L_V_buyer_if_send, KD_G_verif_choice.
    eapply Hout_any with
      (f':=fun n => onth n (slist_xs (Some (header.Bool,L_V_postselect_abort_send))
        (slist_x (Qubit,L_V_postselect_second_send)))).
    - discriminate.
    - apply pac_sendp.
    - kd_branch_table.
  }
  assert (Hproj_vchoice_B : @projC coind_full_merge KD_G_verif_choice Buyer L_B_after_second_send).
  {
    unfold L_B_after_second_send, L_B_final_status_send, KD_G_verif_choice.
    eapply Hin_any with
      (f':=fun n => onth n (slist_xs (Some (header.Bool,ltt_end))
        (slist_x (Qubit,(Verif .&. l_ok1(.Qubit.); L_B_final_status_send))))).
    - discriminate.
    - apply pac_sendq.
    - kd_branch_table.
  }
  assert (Hproj_vchoice_E : @projC coind_full_merge KD_G_verif_choice Env L_E).
  {
    eapply Hskip_any with
      (f':=fun n => match n with 0 => Some L_E_abort | 1 => Some L_E | _ => None end).
    - discriminate.
    - discriminate.
    - discriminate.
    - apply kd_env_in_verif_choice.
    - kd_branch_table.
    - exact Hmerge_abort_env.
  }
  assert (Hproj_vchoice_S : @projC coind_full_merge KD_G_verif_choice Seller ltt_end).
  { apply Hend. exact Hnone_verif_choice_S. }

  assert (Hnone_buyer_second_S : isgPartsC Seller KD_G_buyer_second_qubit -> False).
  { intros H. destruct (kd_range_buyer_second_qubit Seller H) as [Hbad|[Hbad|Hbad]]; unfold Seller, Buyer, Verif, Env in *; discriminate. }
  assert (Hproj_bsecond_B : @projC coind_full_merge KD_G_buyer_second_qubit Buyer L_B_after_first_send).
  {
    unfold L_B_after_first_send, L_B_after_second_send, KD_G_buyer_second_qubit, l_ok1.
    eapply Hout_any with (f':=fun n => onth n (extendSlis 0 (Qubit,L_B_after_second_send))).
    - discriminate.
    - apply pac_sendp.
    - kd_branch_table.
  }
  assert (Hproj_bsecond_V : @projC coind_full_merge KD_G_buyer_second_qubit Verif (Buyer .&. l_ok1(.Qubit.); L_V_buyer_if_send)).
  {
    unfold L_V_buyer_if_send, KD_G_buyer_second_qubit, l_ok1.
    eapply Hin_any with (f':=fun n => onth n (extendSlis 0 (Qubit,L_V_buyer_if_send))).
    - discriminate.
    - apply pac_sendq.
    - kd_branch_table.
  }
  assert (Hproj_bsecond_E : @projC coind_full_merge KD_G_buyer_second_qubit Env L_E).
  {
    unfold KD_G_buyer_second_qubit, l_ok1.
    eapply Hskip_zero with (s:=Qubit) (g:=KD_G_verif_choice).
    - reflexivity.
    - intros n. reflexivity.
    - discriminate.
    - discriminate.
    - discriminate.
    - discriminate.
    - exact Hproj_vchoice_E.
  }
  assert (Hproj_bsecond_S : @projC coind_full_merge KD_G_buyer_second_qubit Seller ltt_end).
  { apply Hend. exact Hnone_buyer_second_S. }

  assert (Hnone_buyer_choice_S : isgPartsC Seller KD_G_buyer_choice -> False).
  { intros H. destruct (kd_range_buyer_choice Seller H) as [Hbad|[Hbad|Hbad]]; unfold Seller, Buyer, Verif, Env in *; discriminate. }
  assert (Hproj_bchoice_B : @projC coind_full_merge KD_G_buyer_choice Buyer L_B_after_initial_measurements).
  {
    unfold L_B_after_initial_measurements, L_B_after_first_send, KD_G_buyer_choice.
    eapply Hout_any with
      (f':=fun n => onth n (slist_xs (Some (header.Bool,ltt_end))
        (slist_x (Qubit,L_B_after_first_send)))).
    - discriminate.
    - apply pac_sendp.
    - kd_branch_table.
  }
  assert (Hproj_bchoice_V : @projC coind_full_merge KD_G_buyer_choice Verif L_V_buyer_choice).
  {
    unfold L_V_buyer_choice, KD_G_buyer_choice.
    eapply Hin_any with
      (f':=fun n => onth n (slist_xs (Some (header.Bool,L_V_postselect_abort_send))
        (slist_x (Qubit,(Buyer .&. l_ok1(.Qubit.); L_V_buyer_if_send))))).
    - discriminate.
    - apply pac_sendq.
    - kd_branch_table.
  }
  assert (Hproj_bchoice_E : @projC coind_full_merge KD_G_buyer_choice Env L_E).
  {
    eapply Hskip_any with
      (f':=fun n => match n with 0 => Some L_E_abort | 1 => Some L_E | _ => None end).
    - discriminate.
    - discriminate.
    - discriminate.
    - apply kd_env_in_buyer_choice.
    - kd_branch_table.
    - exact Hmerge_abort_env.
  }
  assert (Hproj_bchoice_S : @projC coind_full_merge KD_G_buyer_choice Seller ltt_end).
  { apply Hend. exact Hnone_buyer_choice_S. }

  (* Traverse the singleton seller prefix directly. Each participant either
     sends, receives, or skips a communication before the branching suffix. *)
  Local Ltac kd_project_send rule :=
    eapply rule; [reflexivity|intros n; reflexivity|discriminate|].
  Local Ltac kd_project_receive rule :=
    eapply rule; [reflexivity|intros n; reflexivity|discriminate|].
  Local Ltac kd_project_skip rule :=
    eapply rule;
    [reflexivity|intros n; reflexivity
    |discriminate|discriminate|discriminate|discriminate|].

  assert (Hproj_seller_root : @projC coind_full_merge key_distribution_global_coind Seller L_S).
  {
    unfold key_distribution_global_coind, L_S.
    do 8 (kd_project_send Hout_zero).
    exact Hproj_bchoice_S.
  }
  assert (Hproj_buyer_root : @projC coind_full_merge key_distribution_global_coind Buyer L_B).
  {
    unfold key_distribution_global_coind, L_B.
    do 4 (kd_project_receive Hin_zero).
    do 4 (kd_project_skip Hskip_zero).
    exact Hproj_bchoice_B.
  }
  assert (Hproj_verif_root : @projC coind_full_merge key_distribution_global_coind Verif L_V).
  {
    unfold key_distribution_global_coind, L_V.
    do 4 (kd_project_skip Hskip_zero).
    do 4 (kd_project_receive Hin_zero).
    exact Hproj_bchoice_V.
  }
  assert (Hproj_env_root : @projC coind_full_merge key_distribution_global_coind Env L_E).
  {
    unfold key_distribution_global_coind.
    do 8 (kd_project_skip Hskip_zero).
    exact Hproj_bchoice_E.
  }
  destruct (participant_dec pt Env) as [Heq|Hne].
  - subst pt. rewrite insert_eq in Hlookup. inversion Hlookup; subst Tlocal.
    exists L_E. split; [exact Hproj_env_root|apply stRefl].
  - rewrite insert_neq in Hlookup by congruence.
    destruct (participant_dec pt Verif) as [Heq|HneV].
    + subst pt. rewrite insert_eq in Hlookup. inversion Hlookup; subst Tlocal.
      exists L_V. split; [exact Hproj_verif_root|apply stRefl].
    + rewrite insert_neq in Hlookup by congruence.
      destruct (participant_dec pt Buyer) as [Heq|HneB].
      * subst pt. rewrite insert_eq in Hlookup. inversion Hlookup; subst Tlocal.
        exists L_B. split; [exact Hproj_buyer_root|apply stRefl].
      * rewrite insert_neq in Hlookup by congruence.
        destruct (participant_dec pt Seller) as [Heq|HneS].
        -- subst pt. rewrite insert_eq in Hlookup. inversion Hlookup; subst Tlocal.
           exists L_S. split; [exact Hproj_seller_root|apply stRefl].
        -- rewrite insert_neq in Hlookup by congruence. cbv delta [empty_fmap] in Hlookup. discriminate.
Qed.

Lemma key_distribution_typechecks :
  forall (k0 k1 : list bool),
  typecheck_session (H:=coind_full_merge) empty_fmap
    (key_distribution k0 k1)
    (insert (insert (insert (insert empty_fmap Seller L_S) Buyer L_B) Verif L_V) Env L_E)
    key_distribution_global_coind.
Proof.
  intros k0 k1. unfold typecheck_session.
  exists (empty_fmap :: empty_fmap :: empty_fmap :: empty_fmap :: nil).
  (* Session obligations: regularity, balance, participant associations,
     partitioning, context shape, and each participant's process typing. *)
  split.
  - apply key_distribution_global_coind_regular.
  - split.
    + apply key_distribution_global_coind_balanced.
    + split.
      * split.
        -- assert (Hrange_send4 : forall p q f,
             (p = Seller \/ p = Buyer \/ p = Verif \/ p = Env) ->
             (q = Seller \/ q = Buyer \/ q = Verif \/ q = Env) ->
             (forall n s g, f n = Some (s,g) -> forall pt, isgPartsC pt g ->
               pt = Seller \/ pt = Buyer \/ pt = Verif \/ pt = Env) ->
             forall pt, isgPartsC pt (gtt_send p q f) ->
               pt = Seller \/ pt = Buyer \/ pt = Verif \/ pt = Env).
           {
             intros p q f Hp Hq Hchild pt Hpart.
             inversion Hpart; subst; try tauto.
             eapply Hchild; eauto.
           }
           (* Lift the suffix's participant range through a singleton send. *)
           assert (Hrange_send0 : forall p q g,
             (p = Seller \/ p = Buyer \/ p = Verif \/ p = Env) ->
             (q = Seller \/ q = Buyer \/ q = Verif \/ q = Env) ->
             (forall pt, isgPartsC pt g ->
               pt = Seller \/ pt = Buyer \/ pt = Verif \/ pt = Env) ->
             forall pt, isgPartsC pt
               (gtt_send p q (fun n => if Nat.eqb n 0 then Some (Qubit,g) else None)) ->
               pt = Seller \/ pt = Buyer \/ pt = Verif \/ pt = Env).
           {
             intros p q g Hp Hq Hchild pt Hpart.
             eapply Hrange_send4; [exact Hp|exact Hq| |exact Hpart].
             intros [|n] s g' Hbranch pt' Hchildpart; simpl in Hbranch;
               try discriminate.
             inversion Hbranch; subst. apply Hchild. exact Hchildpart.
           }
           assert (Hrange_root : forall pt,
             isgPartsC pt key_distribution_global_coind ->
             pt = Seller \/ pt = Buyer \/ pt = Verif \/ pt = Env).
           {
             unfold key_distribution_global_coind.
             do 8 (apply Hrange_send0;
               [first [left; reflexivity | right; left; reflexivity
                      | right; right; left; reflexivity | right; right; right; reflexivity]
               |first [left; reflexivity | right; left; reflexivity
                      | right; right; left; reflexivity | right; right; right; reflexivity]
               |]).
             intros pt Hpart. right. exact (kd_range_buyer_choice pt Hpart).
           }
           intros pt Hpart.
           destruct (Hrange_root pt Hpart) as [Hp|[Hp|[Hp|Hp]]]; subst pt.
           ++ exists L_S. rewrite insert_neq by discriminate.
              rewrite insert_neq by discriminate. rewrite insert_neq by discriminate.
              rewrite insert_eq. reflexivity.
           ++ exists L_B. rewrite insert_neq by discriminate.
              rewrite insert_neq by discriminate. rewrite insert_eq. reflexivity.
           ++ exists L_V. rewrite insert_neq by discriminate. rewrite insert_eq. reflexivity.
           ++ exists L_E. rewrite insert_eq. reflexivity.
        -- apply projection_exists_key_distribution_global_coind.
      * split.
        -- unfold partition, covers, pairwise_disjoint.
           split.
           ++ intros k v. split.
              ** unfold empty_fmap. simpl. discriminate.
              ** intros [m [Hin Hm]].
                 destruct Hin as [Heq|[Heq|[Heq|[Heq|[]]]]]; subst m;
                   unfold empty_fmap in Hm; simpl in Hm; discriminate.
           ++ intros i j m m' Hneq Hi Hj k.
              destruct i as [|[|[|[|i]]]]; simpl in Hi;
              try (rewrite nth_error_nil in Hi; discriminate);
              inversion Hi; subst;
              destruct j as [|[|[|[|j]]]]; simpl in Hj;
              try (rewrite nth_error_nil in Hj; discriminate);
              inversion Hj; subst;
              unfold empty_fmap; simpl; split; intros; reflexivity.
        -- split.
           ++ cbv. reflexivity.
           ++ split.
              ** cbv. apply Permutation_refl.
              ** intros p T qc Hin.
                 assert (Hqc : qc = empty_fmap).
                 {
                   apply in_map with (f:=snd) in Hin.
                   cbv in Hin. destruct Hin as [Hin|[Hin|[Hin|[Hin|Hin]]]];
                     inversion Hin; reflexivity.
                 }
                 subst qc. cbv in Hin. repeat split_ors; cleanup.
                 +++ exists (P_S k0 k1). split.
                     *** cbv delta [key_distribution]. simpl. reflexivity.
                     *** apply P_S_typecheck.
                 +++ exists P_B. split.
                     *** cbv delta [key_distribution]. simpl. reflexivity.
                     *** apply P_B_typecheck.
                 +++ exists P_V. split.
                     *** cbv delta [key_distribution]. simpl. reflexivity.
                     *** apply P_V_typecheck.
                 +++ exists P_E. split.
                     *** cbv delta [key_distribution]. simpl. reflexivity.
                     *** apply P_E_typecheck.
Qed.
