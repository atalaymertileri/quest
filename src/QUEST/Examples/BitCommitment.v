From SQIR Require Import SQIR.
From Paco Require Import paco.
Require Import List String Bool Arith Lia PeanoNat Permutation.
Require Import SST session balanced.
Require Import Automation FMap Primitives Process Typechecking ExamplesHelpers.

(* The labels for the two phases are reused by different participants. *)
Definition lb := 0.
Definition stop := 0.
Definition data := 1.
Definition verified := 0.
Definition notVerified := 1.

Fixpoint send_all (p : participant) (xs : list expression) (P : process) : process :=
  match xs with
  | nil => P
  | x :: xs' => p .+ lb <.x.>; (send_all p xs' P)
  end.

Fixpoint receive_all (p : participant) (n : nat) (P : process) : process :=
  match n with
  | 0 => P
  | S n' => p .& lb => receive_all p n' P
  end.

(* Alice prepares each bit in the committed basis and sends the qubit.
   The bit and basis are revealed after Bob announces his guess. *)
Fixpoint P_A_rec (x : bool) (xs ys : list bool) : process :=
  match xs with
  | nil =>
      Bob .+ stop <.UNIT.>;
      (Bob .& lb .; (*UNIT;g*)
       (Bob .+ lb <.(Val (Primitives.Bool x)).>; (*send x*)
        (send_all Bob (map (fun b => Val (Primitives.Bool b)) ys) (p_end nil))))
  | x' :: xs' =>
      p_newq
        (let send_cont := Bob .+ data <.(Var 0).>; (P_A_rec x xs' ys) in
         let basis_cont := if x then U_H [.Var 0 :: nil.]; send_cont else send_cont in
         if x' then U_X [.Var 0 :: nil.]; basis_cont else basis_cont)
  end.

Definition P_A (x : bool) (xs : list bool) : process := P_A_rec x xs xs.


(* At the end of the exchange, the latest revealed bit is Var 0, Alice's
   basis is Var m, and each measured round occupies three binder slots:
   measurement result, consumed qubit, and Bob's basis bit. *)
Definition check_pair (m j : nat) : expression :=
  Op Or
    (Op Not (((Var (m + 4 + 3 * j)) .=. (Var m)) :: nil) ::
     ((Var (m + 2 + 3 * j)) .=. (Var j)) :: nil).

Fixpoint verification_expression (m n : nat) : expression :=
  match n with
  | 0 => Val (Primitives.Bool true)
  | S j => (check_pair m j) .&&. (verification_expression m j)
  end.

Definition P_B_v (m : nat) : process :=
  IF verification_expression m m THEN
    (Env .+ verified <.UNIT.>; (p_end nil))
  ELSE
    (Env .+ notVerified <.UNIT.>; (p_end nil)).

Fixpoint P_B_data (n m : nat) (g : bool) : process :=
  match n with
  | 0 => (*L: zn-1, xn-1, yn-1, .... z0, x0, y0*)
      Alice .& stop .; (*UNIT, L*)
      (Alice .+ lb <.(Val (Primitives.Bool g)).>; 
       (Alice .& lb .;(*a, UNIT,L*)
        (receive_all Alice m (P_B_v m)))) (*after receive_all: v_n-1.. v_0, a, UNIT, L*) 
  | S n' =>
      Rnd .& lb .; (*y*)
      (Alice .& data .; (*x, y*)
       (let next := p_measure (Var 0) (P_B_data n' m g) in (*z := measure x;   z x y*)
        IF ((Var 1) .=. (Val (Primitives.Bool true))) THEN
          (U_H [.Var 0 :: nil.]; next) 
        ELSE next))
  end.

Definition P_B (n : nat) (g : bool) : process := P_B_data n n g.

Fixpoint P_R (n : nat) : process :=
  match n with
  | 0 => p_end nil
  | S n' =>
      p_newq (*xq*)
        (U_H [.Var 0 :: nil.];
         (p_measure (Var 0) (*r, xq*)
           (Bob .+ lb <.(Var 0).>; (P_R n'))))
  end.

Definition P_E : process :=
  Bob .& { 0 => p_end nil | 1 => p_end nil }.

Definition bit_commitment (x : bool) (xs : list bool) (g : bool) : session :=
  insert (insert (insert (insert empty_fmap Alice (P_A x xs))
    Bob (P_B (List.length xs) g)) Rnd (P_R (List.length xs))) Env P_E.

Fixpoint transfer_all (p q : participant) (ss : list sort) (G : global) : global :=
  match ss with
  | nil => G
  | B :: ss' => p --> q $ lb(.B.); (transfer_all p q ss' G)
  end.

Fixpoint bit_commitment_global (n m : nat) : global :=
  match n with
  | 0 =>
      Alice --> Bob $ stop(.header.Bool.);
      (Bob --> Alice $ lb(.header.Bool.);
       (Alice --> Bob $ lb(.header.Bool.);
        (transfer_all Alice Bob (repeat header.Bool m)
          (Bob --> Env $ { 0 (. header.Bool .); g_end
                         | 1 (. header.Bool .); g_end }))))
  | S n' =>
      Rnd --> Bob $ lb(.header.Bool.);
      (Alice --> Bob $ data(.Qubit.); (bit_commitment_global n' m))
  end.

Fixpoint transfer_all_coind (p q : participant) (ss : list sort) (G : gtt) : gtt :=
  match ss with
  | nil => G
  | B :: ss' => p -c-> q $ lb(.B.); (transfer_all_coind p q ss' G)
  end.

Fixpoint bit_commitment_global_coind (n m : nat) : gtt :=
  match n with
  | 0 =>
      Alice -c-> Bob $ stop(.header.Bool.);
      (Bob -c-> Alice $ lb(.header.Bool.);
       (Alice -c-> Bob $ lb(.header.Bool.);
        (transfer_all_coind Alice Bob (repeat header.Bool m)
          (Bob -c-> Env $ { 0 (. header.Bool .); gtt_end
                           | 1 (. header.Bool .); gtt_end }))))
  | S n' =>
      Rnd -c-> Bob $ lb(.header.Bool.);
      (Alice -c-> Bob $ data(.Qubit.); (bit_commitment_global_coind n' m))
  end.

Fixpoint send_all_local (p : participant) (ss : list sort) (T : ltt) : ltt :=
  match ss with
  | nil => T
  | B :: ss' => p .+. lb(.B.); (send_all_local p ss' T)
  end.

Fixpoint receive_all_local (p : participant) (ss : list sort) (T : ltt) : ltt :=
  match ss with
  | nil => T
  | B :: ss' => p .&. lb(.B.); (receive_all_local p ss' T)
  end.

Fixpoint L_A (n m : nat) : ltt :=
  match n with
  | 0 =>
      Bob .+. stop(.header.Bool.);
      (Bob .&. lb(.header.Bool.);
       (Bob .+. lb(.header.Bool.);
        (send_all_local Bob (repeat header.Bool m) ltt_end)))
  | S n' => Bob .+. data(.Qubit.); (L_A n' m)
  end.

Definition L_B_v : ltt :=
  Env .+. { 0 (. header.Bool .); ltt_end
           | 1 (. header.Bool .); ltt_end }.

Fixpoint L_B (n m : nat) : ltt :=
  match n with
  | 0 =>
      Alice .&. stop(.header.Bool.);
      (Alice .+. lb(.header.Bool.);
       (Alice .&. lb(.header.Bool.);
        (receive_all_local Alice (repeat header.Bool m) L_B_v)))
  | S n' =>
      Rnd .&. lb(.header.Bool.);
      (Alice .&. data(.Qubit.); (L_B n' m))
  end.

Definition L_R (n : nat) : ltt :=
  send_all_local Bob (repeat header.Bool n) ltt_end.

Definition L_E : ltt :=
  Bob .&. { 0 (. header.Bool .); ltt_end
           | 1 (. header.Bool .); ltt_end }.

Definition bit_commitment_delta (xs : list bool) : typing_context :=
  insert (insert (insert (insert empty_fmap
    Alice (L_A (List.length xs) (List.length xs)))
    Bob (L_B (List.length xs) (List.length xs)))
    Rnd (L_R (List.length xs)))
    Env L_E.

Lemma transfer_all_tc : forall p q ss G H,
  gttTC G H ->
  gttTC (transfer_all p q ss G) (transfer_all_coind p q ss H).
Proof.
  intros p q ss.
  induction ss as [| B ss IH]; intros G H HG; simpl.
  - exact HG.
  - pfold. constructor. intro k. destruct k; simpl.
    + right. exists B, (transfer_all p q ss G),
        (transfer_all_coind p q ss H).
      repeat split; try reflexivity. left. apply IH. exact HG.
    + left. split; reflexivity.
Qed.

Lemma onth_extend : forall (A : Type) (l k : nat) (x : A),
  onth k (extendSlis l x) = if Nat.eqb k l then Some x else None.
Proof.
  intros A l. induction l as [|l IH]; intros k x; destruct k; simpl; try reflexivity.
  apply IH.
Qed.

Lemma send_tc : forall p q l B G H,
  gttTC G H ->
  gttTC (g_send p q (extendSlis l (B,G)))
        (gtt_send p q (fun t => if Nat.eqb t l then Some (B,H) else None)).
Proof.
  intros p q l B G H HG. pfold. constructor. intro k.
  rewrite onth_extend. destruct (Nat.eqb k l) eqn:E.
  - right. exists B,G,H. repeat split; try reflexivity. left. exact HG.
  - left. split; reflexivity.
Qed.

Lemma status_tc :
  gttTC
    (Bob --> Env $ { 0 (.header.Bool.); g_end | 1 (.header.Bool.); g_end })
    (Bob -c-> Env $ { 0 (.header.Bool.); gtt_end | 1 (.header.Bool.); gtt_end }).
Proof.
  pfold. constructor. intro k. destruct k as [|[|k]]; simpl.
  - right. exists header.Bool, g_end, gtt_end. repeat split; try reflexivity. left. pfold. constructor.
  - right. exists header.Bool, g_end, gtt_end. repeat split; try reflexivity. left. pfold. constructor.
  - left. split; reflexivity.
Qed.

Lemma bit_global_tc : forall n m,
  gttTC (bit_commitment_global n m) (bit_commitment_global_coind n m).
Proof.
  induction n as [| n IH]; intros m; simpl.
  - apply (send_tc Alice Bob stop header.Bool).
    apply (send_tc Bob Alice lb header.Bool).
    apply (send_tc Alice Bob lb header.Bool).
    apply transfer_all_tc. apply status_tc.
  - apply (send_tc Rnd Bob lb header.Bool).
    apply (send_tc Alice Bob data Qubit). apply IH.
Qed.

Lemma reg_single : forall p q l B G,
  regGtt G -> regGtt (gtt_send p q (fun t => if Nat.eqb t l then Some (B,G) else None)).
Proof.
  intros p q l B G [g Hg]. exists (g_send p q (extendSlis l (B,g))).
  apply send_tc. exact Hg.
Qed.

Lemma parts_single : forall p q l B G,
  (forall pt, isgPartsC pt G -> isgPartsCS pt G) ->
  forall pt,
  isgPartsC pt (gtt_send p q (fun t => if Nat.eqb t l then Some (B,G) else None)) ->
  isgPartsCS pt (gtt_send p q (fun t => if Nat.eqb t l then Some (B,G) else None)).
Proof.
  intros p q l B G Hchild pt Hparts.
  inversion Hparts; subst.
  - apply pacs_sendp.
  - apply pacs_sendq.
  - eapply pacs_sendr; eauto.
    intros k. destruct (Nat.eqb k l) eqn:E.
    + right. exists B,G. split; [reflexivity|].
      apply Hchild.
      destruct (Nat.eqb n l) eqn:En; simpl in H5; try discriminate.
      inversion H5; subst. exact H6.
    + left. reflexivity.
Qed.

Lemma balanced_single : forall p q l B G,
  regGtt G -> balancedG G ->
  (forall pt, isgPartsC pt G -> isgPartsCS pt G) ->
  balancedG (gtt_send p q (fun t => if Nat.eqb t l then Some (B,G) else None)).
Proof.
  intros p q l B G Hr Hb Hp.
  eapply balanced_up.
  - intros k. destruct (Nat.eqb k l) eqn:E.
    + right. exists B,G. split; [reflexivity|exact Hb].
    + left. reflexivity.
  - apply reg_single. exact Hr.
  - apply parts_single. exact Hp.
Qed.

Lemma status_parts : forall pt,
  isgPartsC pt (Bob -c-> Env $ { 0 (.header.Bool.); gtt_end | 1 (.header.Bool.); gtt_end }) ->
  isgPartsCS pt (Bob -c-> Env $ { 0 (.header.Bool.); gtt_end | 1 (.header.Bool.); gtt_end }).
Proof.
  intros pt Hparts. inversion Hparts; subst.
  - apply pacs_sendp.
  - apply pacs_sendq.
  - destruct n as [|[|n]]; simpl in H5; try discriminate; inversion H5; subst; inversion H6.
Qed.

Lemma status_balanced :
  balancedG (Bob -c-> Env $ { 0 (.header.Bool.); gtt_end | 1 (.header.Bool.); gtt_end }).
Proof.
  eapply balanced_up.
  - intros [|[|k]]; simpl.
    + right. exists header.Bool,gtt_end. split; [reflexivity|].
      unfold balancedG. intros w w' p q [H|H]; inversion H.
    + right. exists header.Bool,gtt_end. split; [reflexivity|].
      unfold balancedG. intros w w' p q [H|H]; inversion H.
    + left. reflexivity.
  - exists (Bob --> Env $ { 0 (.header.Bool.); g_end | 1 (.header.Bool.); g_end }).
    exact status_tc.
  - exact status_parts.
Qed.

Lemma good_single : forall p q l B G,
  (regGtt G /\ balancedG G /\
   (forall pt, isgPartsC pt G -> isgPartsCS pt G)) ->
  regGtt (gtt_send p q (fun t => if Nat.eqb t l then Some (B,G) else None)) /\
  balancedG (gtt_send p q (fun t => if Nat.eqb t l then Some (B,G) else None)) /\
  (forall pt,
    isgPartsC pt (gtt_send p q (fun t => if Nat.eqb t l then Some (B,G) else None)) ->
    isgPartsCS pt (gtt_send p q (fun t => if Nat.eqb t l then Some (B,G) else None))).
Proof.
  intros p q l B G [Hr [Hb Hp]].
  repeat split.
  - apply reg_single. exact Hr.
  - apply balanced_single; assumption.
  - apply parts_single. exact Hp.
Qed.

Lemma good_transfer : forall p q ss G,
  (regGtt G /\ balancedG G /\
   (forall pt, isgPartsC pt G -> isgPartsCS pt G)) ->
  regGtt (transfer_all_coind p q ss G) /\
  balancedG (transfer_all_coind p q ss G) /\
  (forall pt, isgPartsC pt (transfer_all_coind p q ss G) ->
              isgPartsCS pt (transfer_all_coind p q ss G)).
Proof.
  intros p q ss. induction ss as [|B ss IH]; intros G HG; simpl.
  - exact HG.
  - apply good_single. apply IH. exact HG.
Qed.

Lemma bit_global_good : forall n m,
  regGtt (bit_commitment_global_coind n m) /\
  balancedG (bit_commitment_global_coind n m) /\
  (forall pt, isgPartsC pt (bit_commitment_global_coind n m) ->
              isgPartsCS pt (bit_commitment_global_coind n m)).
Proof.
  induction n as [|n IH]; intros m; simpl.
  - apply (good_single Alice Bob stop header.Bool).
    apply (good_single Bob Alice lb header.Bool).
    apply (good_single Alice Bob lb header.Bool).
    apply good_transfer.
    repeat split.
    + exists (Bob --> Env $ { 0 (.header.Bool.); g_end | 1 (.header.Bool.); g_end }). exact status_tc.
    + exact status_balanced.
    + exact status_parts.
  - apply (good_single Rnd Bob lb header.Bool).
    apply (good_single Alice Bob data Qubit).
    apply IH.
Qed.

Lemma singleton_merge : forall l T,
  @isMerge coind_full_merge
    (fun n => if Nat.eqb n l then Some T else None) T.
Proof.
  intros l T. change (full_merge (fun n => if Nat.eqb n l then Some T else None) T).
  unfold full_merge. exists (extendSlis l T). split.
  - intros n. apply onth_extend.
  - induction l; simpl; constructor; assumption.
Qed.

Lemma proj_skip_single : forall p q r l B G T,
  p <> q -> q <> r -> p <> r ->
  isgPartsC r G ->
  @projC coind_full_merge G r T ->
  @projC coind_full_merge
    (gtt_send p q (fun k => if Nat.eqb k l then Some (B,G) else None)) r T.
Proof.
  intros p q r l B G T Hpq Hqr Hpr Hpart Hproj.
  pfold.
  eapply (@proj_cont _ _ p q r _ (fun k => if Nat.eqb k l then Some T else None) T).
  - exact Hpq.
  - exact Hqr.
  - exact Hpr.
  - eapply pac_sendr with (n := l) (s := B) (g := G); eauto.
    simpl. rewrite Nat.eqb_refl. reflexivity.
  - intros k. destruct (Nat.eqb k l) eqn:E; simpl.
    + right. exists B,G,T. repeat split; try reflexivity. left. exact Hproj.
    + left. split; reflexivity.
  - apply singleton_merge.
Qed.

Lemma proj_emit_single : forall p q l B G T,
  p <> q -> @projC coind_full_merge G p T ->
  @projC coind_full_merge
    (gtt_send p q (fun k => if Nat.eqb k l then Some (B,G) else None))
    p (ltt_send q (fun k => if Nat.eqb k l then Some (B,T) else None)).
Proof.
  intros p q l B G T Hneq Hproj. pfold. apply proj_out.
  - exact Hneq.
  - apply pac_sendp.
  - intros k. destruct (Nat.eqb k l); simpl.
    + right. exists B,G,T. repeat split; try reflexivity. left. exact Hproj.
    + left. split; reflexivity.
Qed.

Lemma proj_receive_single : forall p q l B G T,
  p <> q -> @projC coind_full_merge G q T ->
  @projC coind_full_merge
    (gtt_send p q (fun k => if Nat.eqb k l then Some (B,G) else None))
    q (ltt_recv p (fun k => if Nat.eqb k l then Some (B,T) else None)).
Proof.
  intros p q l B G T Hneq Hproj. pfold. apply proj_in.
  - exact Hneq.
  - apply pac_sendq.
  - intros k. destruct (Nat.eqb k l); simpl.
    + right. exists B,G,T. repeat split; try reflexivity. left. exact Hproj.
    + left. split; reflexivity.
Qed.

Lemma proj_status_alice :
  @projC coind_full_merge
    (Bob -c-> Env $ { 0 (.header.Bool.); gtt_end | 1 (.header.Bool.); gtt_end })
    Alice ltt_end.
Proof.
  pfold. apply proj_end. intro Hpart.
  inversion Hpart; subst; try discriminate.
  destruct n as [|[|n]]; simpl in H5; try discriminate;
    inversion H5; subst; inversion H6.
Qed.

Lemma proj_transfer_alice : forall ss G T,
  @projC coind_full_merge G Alice T ->
  @projC coind_full_merge (transfer_all_coind Alice Bob ss G) Alice
    (send_all_local Bob ss T).
Proof.
  induction ss as [|B ss IH]; intros G T Hproj; simpl.
  - exact Hproj.
  - apply (proj_emit_single Alice Bob lb B); [discriminate|].
    apply IH. exact Hproj.
Qed.

Lemma proj_receive_sparse : forall p q l B G T,
  p <> q -> @projC coind_full_merge G q T ->
  @projC coind_full_merge
    (gtt_send p q (fun k => if Nat.eqb k l then Some (B,G) else None))
    q (ltt_recv p (fun k => onth k (extendSlis l (B,T)))).
Proof.
  intros p q l B G T Hneq Hproj. pfold. apply proj_in.
  - exact Hneq.
  - apply pac_sendq.
  - intros k. rewrite onth_extend.
    destruct (Nat.eqb k l); simpl.
    + right. exists B,G,T. repeat split; try reflexivity. left. exact Hproj.
    + left. split; reflexivity.
Qed.

Lemma proj_alice : forall n m,
  @projC coind_full_merge (bit_commitment_global_coind n m) Alice (L_A n m).
Proof.
  induction n as [|n IH]; intros m; simpl.
  - apply (proj_emit_single Alice Bob stop header.Bool); [discriminate|].
    apply (proj_receive_sparse Bob Alice lb header.Bool); [discriminate|].
    apply (proj_emit_single Alice Bob lb header.Bool); [discriminate|].
    apply proj_transfer_alice. exact proj_status_alice.
  - apply (proj_skip_single Rnd Bob Alice lb header.Bool); try discriminate.
    + apply pac_sendp.
    + apply (proj_emit_single Alice Bob data Qubit); [discriminate|].
      apply IH.
Qed.

Lemma proj_status_bob :
  @projC coind_full_merge
    (Bob -c-> Env $ { 0 (.header.Bool.); gtt_end | 1 (.header.Bool.); gtt_end })
    Bob L_B_v.
Proof.
  unfold L_B_v. pfold. apply proj_out.
  - discriminate.
  - apply pac_sendp.
  - intros [|[|k]]; simpl.
    + right. exists header.Bool, gtt_end, ltt_end.
      repeat split; try reflexivity. left. pfold. apply proj_end. intro H; inversion H.
    + right. exists header.Bool, gtt_end, ltt_end.
      repeat split; try reflexivity. left. pfold. apply proj_end. intro H; inversion H.
    + left. split; reflexivity.
Qed.

Lemma proj_transfer_bob : forall ss G T,
  @projC coind_full_merge G Bob T ->
  @projC coind_full_merge (transfer_all_coind Alice Bob ss G) Bob
    (receive_all_local Alice ss T).
Proof.
  induction ss as [|B ss IH]; intros G T Hproj; simpl.
  - exact Hproj.
  - apply (proj_receive_sparse Alice Bob lb B); [discriminate|].
    apply IH. exact Hproj.
Qed.

Lemma proj_bob : forall n m,
  @projC coind_full_merge (bit_commitment_global_coind n m) Bob (L_B n m).
Proof.
  induction n as [|n IH]; intros m; simpl.
  - apply (proj_receive_sparse Alice Bob stop header.Bool); [discriminate|].
    apply (proj_emit_single Bob Alice lb header.Bool); [discriminate|].
    apply (proj_receive_sparse Alice Bob lb header.Bool); [discriminate|].
    apply proj_transfer_bob. exact proj_status_bob.
  - apply (proj_receive_sparse Rnd Bob lb header.Bool); [discriminate|].
    apply (proj_receive_sparse Alice Bob data Qubit); [discriminate|].
    apply IH.
Qed.

Lemma absent_single : forall p q r l B G,
  p <> r -> q <> r -> (isgPartsC r G -> False) ->
  isgPartsC r (gtt_send p q (fun k => if Nat.eqb k l then Some (B,G) else None)) -> False.
Proof.
  intros p q r l B G Hpr Hqr Habs Hpart.
  inversion Hpart; subst; try contradiction.
  destruct (Nat.eqb n l) eqn:E; simpl in H5; try discriminate.
  inversion H5; subst. apply Habs. exact H6.
Qed.

Lemma absent_transfer : forall p q r ss G,
  p <> r -> q <> r -> (isgPartsC r G -> False) ->
  isgPartsC r (transfer_all_coind p q ss G) -> False.
Proof.
  intros p q r ss. induction ss as [|B ss IH]; intros G Hpr Hqr Habs; simpl.
  - exact Habs.
  - apply absent_single; try assumption. apply IH; assumption.
Qed.

Lemma absent_status_rnd :
  isgPartsC Rnd
    (Bob -c-> Env $ { 0 (.header.Bool.); gtt_end | 1 (.header.Bool.); gtt_end }) -> False.
Proof.
  intro Hpart. inversion Hpart; subst; try discriminate.
  destruct n as [|[|n]]; simpl in H5; try discriminate;
    inversion H5; subst; inversion H6.
Qed.

Lemma absent_base_rnd : forall m,
  isgPartsC Rnd (bit_commitment_global_coind 0 m) -> False.
Proof.
  intro m. simpl.
  apply (absent_single Alice Bob Rnd stop header.Bool); try discriminate.
  apply (absent_single Bob Alice Rnd lb header.Bool); try discriminate.
  apply (absent_single Alice Bob Rnd lb header.Bool); try discriminate.
  apply absent_transfer; try discriminate.
  exact absent_status_rnd.
Qed.

Lemma proj_rnd : forall n m,
  @projC coind_full_merge (bit_commitment_global_coind n m) Rnd (L_R n).
Proof.
  induction n as [|n IH]; intros m; simpl.
  - pfold. apply proj_end. apply absent_base_rnd.
  - apply (proj_emit_single Rnd Bob lb header.Bool); [discriminate|].
    destruct n as [|n].
    + pfold. apply proj_end.
      apply (absent_single Alice Bob Rnd data Qubit); try discriminate.
      apply absent_base_rnd.
    + apply (proj_skip_single Alice Bob Rnd data Qubit); try discriminate.
      * apply pac_sendp.
      * apply IH.
Qed.

Lemma part_single : forall p q r l B G,
  p <> r -> q <> r -> isgPartsC r G ->
  isgPartsC r (gtt_send p q (fun k => if Nat.eqb k l then Some (B,G) else None)).
Proof.
  intros p q r l B G Hpr Hqr Hpart.
  eapply pac_sendr with (n := l) (s := B) (g := G); eauto.
  rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma part_transfer : forall p q r ss G,
  p <> r -> q <> r -> isgPartsC r G ->
  isgPartsC r (transfer_all_coind p q ss G).
Proof.
  intros p q r ss. induction ss as [|B ss IH]; intros G Hpr Hqr Hpart; simpl.
  - exact Hpart.
  - apply part_single; try assumption. apply IH; assumption.
Qed.

Lemma env_part : forall n m,
  isgPartsC Env (bit_commitment_global_coind n m).
Proof.
  induction n as [|n IH]; intros m; simpl.
  - apply (part_single Alice Bob Env stop header.Bool); try discriminate.
    apply (part_single Bob Alice Env lb header.Bool); try discriminate.
    apply (part_single Alice Bob Env lb header.Bool); try discriminate.
    apply part_transfer; try discriminate. apply pac_sendq.
  - apply (part_single Rnd Bob Env lb header.Bool); try discriminate.
    apply (part_single Alice Bob Env data Qubit); try discriminate.
    apply IH.
Qed.

Lemma proj_status_env :
  @projC coind_full_merge
    (Bob -c-> Env $ { 0 (.header.Bool.); gtt_end | 1 (.header.Bool.); gtt_end })
    Env L_E.
Proof.
  unfold L_E. pfold. apply proj_in.
  - discriminate.
  - apply pac_sendq.
  - intros [|[|k]]; simpl.
    + right. exists header.Bool, gtt_end, ltt_end.
      repeat split; try reflexivity. left. pfold. apply proj_end. intro H; inversion H.
    + right. exists header.Bool, gtt_end, ltt_end.
      repeat split; try reflexivity. left. pfold. apply proj_end. intro H; inversion H.
    + left. split; reflexivity.
Qed.

Lemma proj_skip_transfer_env : forall ss G,
  isgPartsC Env G ->
  @projC coind_full_merge G Env L_E ->
  @projC coind_full_merge (transfer_all_coind Alice Bob ss G) Env L_E.
Proof.
  induction ss as [|B ss IH]; intros G Hpart Hproj; simpl.
  - exact Hproj.
  - apply (proj_skip_single Alice Bob Env lb B); try discriminate.
    + apply part_transfer; try discriminate. exact Hpart.
    + apply IH; assumption.
Qed.

Lemma proj_env : forall n m,
  @projC coind_full_merge (bit_commitment_global_coind n m) Env L_E.
Proof.
  induction n as [|n IH]; intros m; simpl.
  - apply (proj_skip_single Alice Bob Env stop header.Bool); try discriminate.
    + apply (part_single Bob Alice Env lb header.Bool); try discriminate.
      apply (part_single Alice Bob Env lb header.Bool); try discriminate.
      apply part_transfer; try discriminate. apply pac_sendq.
    + apply (proj_skip_single Bob Alice Env lb header.Bool); try discriminate.
      * apply (part_single Alice Bob Env lb header.Bool); try discriminate.
        apply part_transfer; try discriminate. apply pac_sendq.
      * apply (proj_skip_single Alice Bob Env lb header.Bool); try discriminate.
        -- apply part_transfer; try discriminate. apply pac_sendq.
        -- apply proj_skip_transfer_env.
           ++ apply pac_sendq.
           ++ exact proj_status_env.
  - apply (proj_skip_single Rnd Bob Env lb header.Bool); try discriminate.
    + apply (part_single Alice Bob Env data Qubit); try discriminate. apply env_part.
    + apply (proj_skip_single Alice Bob Env data Qubit); try discriminate.
      * apply env_part.
      * apply IH.
Qed.

Lemma P_E_typecheck :
  typecheck_process (nil, nil, empty_fmap) P_E L_E.
Proof.
  unfold P_E, L_E.
  apply T_recv. apply SForall2_sxs.
  - apply T_end.
    + intros z. split; intro H; [inversion H|].
      inversion H; subst; unfold in_variable_context, in_qubit_context in *; simpl in *; try discriminate.
      destruct x as [|[|x]]; simpl in H0; discriminate H0.
    + constructor.
  - apply SForall2_x. apply T_end.
    + intros z. split; intro H; [inversion H|].
      inversion H; subst; unfold in_variable_context, in_qubit_context in *; simpl in *; try discriminate.
      destruct x as [|[|x]]; simpl in H0; discriminate H0.
    + constructor.
Qed.

Lemma no_qubit_nth : forall lc x,
  Forall (fun s => s <> Some Qubit) lc ->
  nth x lc None <> Some Qubit.
Proof.
  induction lc as [|a lc IH]; intros [|x] H; simpl; try discriminate.
  - inversion H; subst; assumption.
  - inversion H; subst; apply IH; assumption.
Qed.

Lemma no_qubit_end : forall lc,
  Forall (fun s => s <> Some Qubit) lc ->
  typecheck_process (nil, lc, empty_fmap) (p_end nil) ltt_end.
Proof.
  intros lc Hlc. apply T_end.
  - intros z; split; intro H; [inversion H|].
    inversion H; subst.
    + unfold in_qubit_context in H0; simpl in H0; discriminate.
    + unfold in_variable_context in H0; simpl in H0.
      exact (no_qubit_nth lc x Hlc H0).
  - constructor.
Qed.

Lemma rnd_ctx_no_qubit : forall k,
  Forall (fun s => s <> Some Qubit)
    (List.concat (repeat (Some header.Bool :: None :: nil) k)).
Proof.
  induction k; simpl; [constructor|].
  repeat constructor; try discriminate; assumption.
Qed.

Lemma P_R_typecheck_acc : forall n k,
  typecheck_process
    (nil, List.concat (repeat (Some header.Bool :: None :: nil) k), empty_fmap)
    (P_R n) (L_R n).
Proof.
  induction n as [|n IH]; intro k; simpl.
  - apply no_qubit_end. apply rnd_ctx_no_qubit.
  - apply T_qbit. apply T_U; simpl.
    + reflexivity.
    + constructor; [apply TE_Var; reflexivity|constructor].
    + constructor; [intro H; inversion H|constructor].
    + apply T_meas.
      * apply TE_Var. reflexivity.
      * apply T_send with (B := header.Bool).
        -- apply TE_Var. reflexivity.
        -- change (typecheck_process
             (nil, List.concat (repeat (Some header.Bool :: None :: nil) (S k)), empty_fmap)
             (P_R n) (L_R n)). apply IH.
Qed.

Lemma alice_ctx_no_qubit : forall k,
  Forall (fun s => s <> Some Qubit) (repeat None k).
Proof. induction k; simpl; constructor; try discriminate; assumption. Qed.

Lemma send_all_bool_typecheck : forall ys k,
  typecheck_process
    (nil, Some header.Bool :: repeat None k, empty_fmap)
    (send_all Bob (map (fun b => Val (Primitives.Bool b)) ys) (p_end nil))
    (send_all_local Bob (repeat header.Bool (List.length ys)) ltt_end).
Proof.
  induction ys as [|y ys IH]; intro k; simpl.
  - apply no_qubit_end. constructor; [discriminate|apply alice_ctx_no_qubit].
  - apply T_send with (B := header.Bool).
    + apply TE_ValB.
    + exact (IH k).
Qed.

Lemma P_A_rec_typecheck_acc : forall xs k x ys,
  typecheck_process
    (nil, repeat None k, empty_fmap)
    (P_A_rec x xs ys) (L_A (List.length xs) (List.length ys)).
Proof.
  induction xs as [|b xs IH]; intros k x ys; simpl.
  - apply T_send with (B := header.Bool).
    + apply TE_ValB.
    + apply T_recv. apply SForall2_x.
      apply T_send with (B := header.Bool).
      * apply TE_ValB.
      * apply send_all_bool_typecheck.
  - apply T_qbit.
    destruct b, x; simpl.
    + apply T_U; simpl; [reflexivity| | |].
      * constructor; [apply TE_Var; reflexivity|constructor].
      * constructor; [intro H; inversion H|constructor].
      * apply T_U; simpl; [reflexivity| | |].
        -- constructor; [apply TE_Var; reflexivity|constructor].
        -- constructor; [intro H; inversion H|constructor].
        -- apply T_send with (B := Qubit).
           ++ apply TE_Var. reflexivity.
           ++ change (typecheck_process
                (nil, repeat None (S k), empty_fmap)
                (P_A_rec true xs ys) (L_A (List.length xs) (List.length ys))).
              apply IH.
    + apply T_U; simpl; [reflexivity| | |].
      * constructor; [apply TE_Var; reflexivity|constructor].
      * constructor; [intro H; inversion H|constructor].
      * apply T_send with (B := Qubit).
        -- apply TE_Var. reflexivity.
        -- change (typecheck_process
             (nil, repeat None (S k), empty_fmap)
             (P_A_rec false xs ys) (L_A (List.length xs) (List.length ys))).
           apply IH.
    + apply T_U; simpl; [reflexivity| | |].
      * constructor; [apply TE_Var; reflexivity|constructor].
      * constructor; [intro H; inversion H|constructor].
      * apply T_send with (B := Qubit).
        -- apply TE_Var. reflexivity.
        -- change (typecheck_process
             (nil, repeat None (S k), empty_fmap)
             (P_A_rec true xs ys) (L_A (List.length xs) (List.length ys))).
           apply IH.
    + apply T_send with (B := Qubit).
      * apply TE_Var. reflexivity.
      * change (typecheck_process
           (nil, repeat None (S k), empty_fmap)
           (P_A_rec false xs ys) (L_A (List.length xs) (List.length ys))).
        apply IH.
Qed.

Lemma bob_round_nth : forall k j,
  j < k ->
  nth (3*j) (List.concat (repeat (Some header.Bool :: None :: Some header.Bool :: nil) k)) None = Some header.Bool /\
  nth (2+3*j) (List.concat (repeat (Some header.Bool :: None :: Some header.Bool :: nil) k)) None = Some header.Bool.
Proof.
  induction k as [|k IH]; intros j Hj; [lia|].
  destruct j as [|j]; cbn [List.repeat List.concat].
  - split; reflexivity.
  - replace (3 * S j) with (3 + 3*j) by lia.
    replace (2 + 3 * S j) with (3 + (2+3*j)) by lia.
    cbn [nth]. apply IH. lia.
Qed.

Lemma bob_round_no_qubit : forall k,
  Forall (fun s => s <> Some Qubit)
    (List.concat (repeat (Some header.Bool :: None :: Some header.Bool :: nil) k)).
Proof.
  induction k; simpl; [constructor|].
  repeat constructor; try discriminate; assumption.
Qed.

Lemma bob_round_length : forall k,
  List.length (List.concat (repeat (Some header.Bool :: None :: Some header.Bool :: nil) k)) = 3*k.
Proof. induction k; simpl; lia. Qed.

Lemma bob_final_nth : forall m j,
  j < m ->
  nth j
    (repeat (Some header.Bool) m ++ Some header.Bool :: Some header.Bool ::
      List.concat (repeat (Some header.Bool :: None :: Some header.Bool :: nil) m)) None = Some header.Bool /\
  nth m
    (repeat (Some header.Bool) m ++ Some header.Bool :: Some header.Bool ::
      List.concat (repeat (Some header.Bool :: None :: Some header.Bool :: nil) m)) None = Some header.Bool /\
  nth (m+2+3*j)
    (repeat (Some header.Bool) m ++ Some header.Bool :: Some header.Bool ::
      List.concat (repeat (Some header.Bool :: None :: Some header.Bool :: nil) m)) None = Some header.Bool /\
  nth (m+4+3*j)
    (repeat (Some header.Bool) m ++ Some header.Bool :: Some header.Bool ::
      List.concat (repeat (Some header.Bool :: None :: Some header.Bool :: nil) m)) None = Some header.Bool.
Proof.
  intros m j Hj.
  repeat split.
  - apply nth_error_nth. rewrite nth_error_app1 by (rewrite repeat_length; lia).
    apply nth_error_repeat. exact Hj.
  - apply nth_error_nth. rewrite nth_error_app2 by (rewrite repeat_length; lia).
    rewrite repeat_length. replace (m-m) with 0 by lia. reflexivity.
  - apply nth_error_nth. rewrite nth_error_app2 by (rewrite repeat_length; lia).
    rewrite repeat_length. replace (m+2+3*j-m) with (2+3*j) by lia.
    replace (2+3*j) with (S (S (3*j))) by lia. cbn [nth_error].
    rewrite nth_error_nth' with (d := None).

    + replace (j+(j+(j+0))) with (3*j) by lia. rewrite (proj1 (bob_round_nth m j Hj)). reflexivity.
    + rewrite bob_round_length. lia.
  - apply nth_error_nth. rewrite nth_error_app2 by (rewrite repeat_length; lia).
    rewrite repeat_length. replace (m+4+3*j-m) with (4+3*j) by lia.
    replace (4+3*j) with (S (S (2+3*j))) by lia. cbn [nth_error].
    rewrite nth_error_nth' with (d := None).
    + replace (j+(j+(j+0))) with (3*j) by lia. rewrite (proj2 (bob_round_nth m j Hj)). reflexivity.
    + rewrite bob_round_length. lia.
Qed.

Lemma check_pair_typecheck : forall m j,
  j < m ->
  typecheck_expression
    (nil, repeat (Some header.Bool) m ++ Some header.Bool :: Some header.Bool ::
      List.concat (repeat (Some header.Bool :: None :: Some header.Bool :: nil) m), empty_fmap)
    (check_pair m j) header.Bool.
Proof.
  intros m j Hj. unfold check_pair.
  apply TE_Op_Or.
  - apply TE_Op_Not. apply TE_Op_Beq.
    + apply TE_Var. unfold in_variable_context; simpl.
      exact (proj2 (proj2 (proj2 (bob_final_nth m j Hj)))).
    + apply TE_Var. unfold in_variable_context; simpl.
      exact (proj1 (proj2 (bob_final_nth m j Hj))).
  - apply TE_Op_Beq.
    + apply TE_Var. unfold in_variable_context; simpl.
      exact (proj1 (proj2 (proj2 (bob_final_nth m j Hj)))).
    + apply TE_Var. unfold in_variable_context; simpl.
      exact (proj1 (bob_final_nth m j Hj)).
Qed.

Lemma verification_expression_typecheck : forall m n,
  n <= m ->
  typecheck_expression
    (nil, repeat (Some header.Bool) m ++ Some header.Bool :: Some header.Bool ::
      List.concat (repeat (Some header.Bool :: None :: Some header.Bool :: nil) m), empty_fmap)
    (verification_expression m n) header.Bool.
Proof.
  intros m n. induction n as [|n IH]; intro Hn; simpl.
  - apply TE_ValB.
  - apply TE_Op_And.
    + apply check_pair_typecheck. lia.
    + apply IH. lia.
Qed.

Lemma bob_final_no_qubit : forall m,
  Forall (fun s => s <> Some Qubit)
    (repeat (Some header.Bool) m ++ Some header.Bool :: Some header.Bool ::
      List.concat (repeat (Some header.Bool :: None :: Some header.Bool :: nil) m)).
Proof.
  intro m. apply Forall_app. split.
  - induction m; simpl; constructor; try discriminate; assumption.
  - repeat constructor; try discriminate; apply bob_round_no_qubit.
Qed.

Lemma P_B_v_typecheck : forall m,
  typecheck_process
    (nil, repeat (Some header.Bool) m ++ Some header.Bool :: Some header.Bool ::
      List.concat (repeat (Some header.Bool :: None :: Some header.Bool :: nil) m), empty_fmap)
    (P_B_v m) L_B_v.
Proof.
  intro m. unfold P_B_v. apply T_if.
  - apply verification_expression_typecheck. lia.
  - eapply T_sub.
    + apply T_send with (B := header.Bool).
      * apply TE_ValB.
      * apply no_qubit_end. apply bob_final_no_qubit.
    + unfold subtypeC. pfold. apply sub_out.
      intros [|[|n]]; simpl.
      * right. exists header.Bool, ltt_end, ltt_end.
        repeat split; try reflexivity. left. apply stRefl.
      * left. reflexivity.
      * left. reflexivity.
  - eapply T_sub.
    + apply T_send with (B := header.Bool).
      * apply TE_ValB.
      * apply no_qubit_end. apply bob_final_no_qubit.
    + unfold subtypeC. pfold. apply sub_out.
      intros [|[|n]]; simpl.
      * left. reflexivity.
      * right. exists header.Bool, ltt_end, ltt_end.
        repeat split; try reflexivity. left. apply stRefl.
      * left. reflexivity.
Qed.

Lemma receive_all_bool_typecheck : forall n m i,
  m = i + n ->
  typecheck_process
    (nil, repeat (Some header.Bool) i ++ Some header.Bool :: Some header.Bool ::
      List.concat (repeat (Some header.Bool :: None :: Some header.Bool :: nil) m), empty_fmap)
    (receive_all Alice n (P_B_v m))
    (receive_all_local Alice (repeat header.Bool n) L_B_v).
Proof.
  induction n as [|n IH]; intros m i Hm; simpl.
  - subst m. rewrite Nat.add_0_r. apply P_B_v_typecheck.
  - apply T_recv. apply SForall2_x.
    change (typecheck_process
      (nil, repeat (Some header.Bool) (S i) ++ Some header.Bool :: Some header.Bool ::
        List.concat (repeat (Some header.Bool :: None :: Some header.Bool :: nil) m), empty_fmap)
      (receive_all Alice n (P_B_v m))
      (receive_all_local Alice (repeat header.Bool n) L_B_v)).
    apply IH. lia.
Qed.

Lemma P_B_data_typecheck_acc : forall n k m g,
  m = n + k ->
  typecheck_process
    (nil, List.concat (repeat (Some header.Bool :: None :: Some header.Bool :: nil) k), empty_fmap)
    (P_B_data n m g) (L_B n m).
Proof.
  induction n as [|n IH]; intros k m g Hm; simpl.
  - subst m. apply T_recv. apply SForall2_x.
    apply T_send with (B := header.Bool).
    + apply TE_ValB.
    + apply T_recv. apply SForall2_x.
      simpl.
      exact (receive_all_bool_typecheck k k 0 (eq_refl k)).
  - apply T_recv. apply SForall2_x.
    apply T_recv. apply SForall2_nxs. apply SForall2_x.
    apply T_if.
    + apply TE_Op_Beq.
      * apply TE_Var. reflexivity.
      * apply TE_ValB.
    + apply T_U; simpl.
      * reflexivity.
      * constructor; [apply TE_Var; reflexivity|constructor].
      * constructor; [intro H; inversion H|constructor].
      * apply T_meas.
        -- apply TE_Var. reflexivity.
        -- change (typecheck_process
             (nil, List.concat (repeat (Some header.Bool :: None :: Some header.Bool :: nil) (S k)), empty_fmap)
             (P_B_data n m g) (L_B n m)).
           apply IH. lia.
    + apply T_meas.
      * apply TE_Var. reflexivity.
      * change (typecheck_process
           (nil, List.concat (repeat (Some header.Bool :: None :: Some header.Bool :: nil) (S k)), empty_fmap)
           (P_B_data n m g) (L_B n m)).
        apply IH. lia.
Qed.

Lemma bit_part_range_single : forall p q l B G,
  (p = Alice \/ p = Bob \/ p = Rnd \/ p = Env) ->
  (q = Alice \/ q = Bob \/ q = Rnd \/ q = Env) ->
  (forall pt, isgPartsC pt G -> pt = Alice \/ pt = Bob \/ pt = Rnd \/ pt = Env) ->
  forall pt,
  isgPartsC pt (gtt_send p q (fun t => if Nat.eqb t l then Some (B,G) else None)) ->
  pt = Alice \/ pt = Bob \/ pt = Rnd \/ pt = Env.
Proof.
  intros p q l B G Hp Hq HG pt Hpart.
  inversion Hpart; subst; try assumption.
  apply HG. destruct (Nat.eqb n l) eqn:E; simpl in H5; try discriminate.
  inversion H5; subst; assumption.
Qed.

Lemma bit_part_range_status : forall pt,
  isgPartsC pt
    (Bob -c-> Env $ { 0 (.header.Bool.); gtt_end | 1 (.header.Bool.); gtt_end }) ->
  pt = Bob \/ pt = Env.
Proof.
  intros pt Hpart. inversion Hpart; subst; try tauto.
  destruct n as [|[|n]]; simpl in H5; try discriminate;
    inversion H5; subst; inversion H6.
Qed.

Lemma bit_part_range_transfer : forall p q ss G,
  (p = Alice \/ p = Bob \/ p = Rnd \/ p = Env) ->
  (q = Alice \/ q = Bob \/ q = Rnd \/ q = Env) ->
  (forall pt, isgPartsC pt G -> pt = Alice \/ pt = Bob \/ pt = Rnd \/ pt = Env) ->
  forall pt, isgPartsC pt (transfer_all_coind p q ss G) ->
  pt = Alice \/ pt = Bob \/ pt = Rnd \/ pt = Env.
Proof.
  intros p q ss. induction ss as [|B ss IH]; intros G Hp Hq HG pt Hpart; simpl in *.
  - apply HG. exact Hpart.
  - apply (bit_part_range_single p q lb B (transfer_all_coind p q ss G)); try assumption.
    intros pt' H. eapply IH; eauto.
Qed.

Lemma bit_part_range_global : forall n m pt,
  isgPartsC pt (bit_commitment_global_coind n m) ->
  pt = Alice \/ pt = Bob \/ pt = Rnd \/ pt = Env.
Proof.
  induction n as [|n IH]; intros m pt Hpart; simpl in Hpart.
  - eapply (bit_part_range_single Alice Bob stop header.Bool); [tauto|tauto| |exact Hpart].
    intros pt1 H1.
    eapply (bit_part_range_single Bob Alice lb header.Bool); [tauto|tauto| |exact H1].
    intros pt2 H2.
    eapply (bit_part_range_single Alice Bob lb header.Bool); [tauto|tauto| |exact H2].
    intros pt3 H3.
    eapply (bit_part_range_transfer Alice Bob (repeat header.Bool m)); [tauto|tauto| |exact H3].
    intros pt4 H4. destruct (bit_part_range_status pt4 H4); tauto.
  - eapply (bit_part_range_single Rnd Bob lb header.Bool); [tauto|tauto| |exact Hpart].
    intros pt1 H1.
    eapply (bit_part_range_single Alice Bob data Qubit); [tauto|tauto| |exact H1].
    intros pt2 H2. apply IH with (m:=m). exact H2.
Qed.

Lemma bit_full_proj_assoc : forall xs,
  @full_proj_assoc coind_full_merge (bit_commitment_delta xs)
    (bit_commitment_global_coind (List.length xs) (List.length xs)).
Proof.
  intro xs. set (n := List.length xs). unfold full_proj_assoc, bit_commitment_delta.
  split.
  - intros pt Hpart.
    destruct (bit_part_range_global n n pt Hpart) as [Heq|[Heq|[Heq|Heq]]]; subst pt.
    + exists (L_A n n). rewrite insert_neq by discriminate.
      rewrite insert_neq by discriminate. rewrite insert_neq by discriminate.
      apply insert_eq.
    + exists (L_B n n). rewrite insert_neq by discriminate.
      rewrite insert_neq by discriminate. apply insert_eq.
    + exists (L_R n). rewrite insert_neq by discriminate. apply insert_eq.
    + exists L_E. apply insert_eq.
  - intros pt T Hlookup.
    destruct (participant_dec pt Env) as [->|Henv].
    + rewrite insert_eq in Hlookup. inversion Hlookup; subst. apply proj_env.
    + rewrite insert_neq in Hlookup by congruence.
      destruct (participant_dec pt Rnd) as [->|Hrnd].
      * rewrite insert_eq in Hlookup. inversion Hlookup; subst. apply proj_rnd.
      * rewrite insert_neq in Hlookup by congruence.
        destruct (participant_dec pt Bob) as [->|Hbob].
        -- rewrite insert_eq in Hlookup. inversion Hlookup; subst. apply proj_bob.
        -- rewrite insert_neq in Hlookup by congruence.
           destruct (participant_dec pt Alice) as [->|Halice].
           ++ rewrite insert_eq in Hlookup. inversion Hlookup; subst. apply proj_alice.
           ++ rewrite insert_neq in Hlookup by congruence.
              unfold empty_fmap in Hlookup. discriminate.
Qed.

Lemma P_A_typecheck : forall x xs,
  typecheck_process (nil,nil,empty_fmap) (P_A x xs)
    (L_A (List.length xs) (List.length xs)).
Proof. intros x xs. unfold P_A. exact (P_A_rec_typecheck_acc xs 0 x xs). Qed.

Lemma P_B_typecheck : forall (xs : list bool) g,
  typecheck_process (nil,nil,empty_fmap) (P_B (List.length xs) g)
    (L_B (List.length xs) (List.length xs)).
Proof.
  intros xs g. unfold P_B. eapply P_B_data_typecheck_acc with (k:=0).
  lia.
Qed.

Lemma P_R_typecheck : forall n,
  typecheck_process (nil,nil,empty_fmap) (P_R n) (L_R n).
Proof. intro n. exact (P_R_typecheck_acc n 0). Qed.

Lemma bit_empty_partition : forall n,
  FMap.partition _ _ (empty_fmap : qubit_context)
    (repeat (empty_fmap : qubit_context) n).
Proof.
  intro n. unfold FMap.partition, covers, pairwise_disjoint. split.
  - intros k v. split; intro H.
    + unfold empty_fmap in H. discriminate.
    + destruct H as [m [Hin Hm]].
      apply repeat_spec in Hin. subst m.
      unfold empty_fmap in Hm. discriminate.
  - intros i j m m' Hneq Hi Hj k.
    apply nth_error_In in Hi. apply nth_error_In in Hj.
    apply repeat_spec in Hi. apply repeat_spec in Hj. subst.
    unfold empty_fmap. split; intro H; contradiction H; reflexivity.
Qed.


Lemma bit_commitment_typechecks :
  forall x xs g,
    xs <> nil ->
    typecheck_session (H := coind_full_merge)
      empty_fmap
      (bit_commitment x xs g)
      (bit_commitment_delta xs)
      (bit_commitment_global_coind (List.length xs) (List.length xs)).
Proof.
  intros x xs g Hxs. unfold typecheck_session.
  exists (empty_fmap :: empty_fmap :: empty_fmap :: empty_fmap :: nil).
  split.
  - exact (proj1 (bit_global_good (List.length xs) (List.length xs))).
  - split.
    + exact (proj1 (proj2 (bit_global_good (List.length xs) (List.length xs)))).
    + split.
      * apply full_proj_is_assoc. apply bit_full_proj_assoc.
      * split.
        -- change (FMap.partition _ _ (empty_fmap : qubit_context)
             (empty_fmap :: empty_fmap :: empty_fmap :: empty_fmap :: nil)).
           exact (bit_empty_partition 4).
        -- split.
           ++ cbv. reflexivity.
           ++ split.
              ** cbv. apply Permutation_refl.
              ** intros p T qc Hin.
                 cbv delta [bit_commitment_delta] in Hin.
                 simpl in Hin.
                 destruct Hin as [Hin|[Hin|[Hin|[Hin|[]]]]];
                   inversion Hin; subst; clear Hin; simpl.
                 --- exists (P_A x xs). split.
                     +++ cbv delta [bit_commitment]. simpl. reflexivity.
                     +++ apply P_A_typecheck.
                 --- exists (P_B (List.length xs) g). split.
                     +++ cbv delta [bit_commitment]. simpl. reflexivity.
                     +++ apply P_B_typecheck.
                 --- exists (P_R (List.length xs)). split.
                     +++ cbv delta [bit_commitment]. simpl. reflexivity.
                     +++ apply P_R_typecheck.
                 --- exists P_E. split.
                     +++ cbv delta [bit_commitment]. simpl. reflexivity.
                     +++ apply P_E_typecheck.
Qed.
