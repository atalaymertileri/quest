From mathcomp Require ssreflect.seq ssreflect.ssrnat.
From SQIR Require Import SQIR UnitaryOps.
Require Import Reals Nat Lia List Bool String Relations.
Require Import header. 
Require Import Automation ListUtils FMap Primitives.

Open Scope nat_scope.

Arguments Forall_cons _ _ _ _ : clear implicits.
Section Process.

Inductive action :=
| Tau (p: participant)
| Transmit (p q: participant) (l: label) (v: value).

Inductive expression :=
| Val (v: value)
| Var (x: variable)
| Op (op: operation) (args: list expression).


Program Definition expression_deep_ind := fun (P : expression -> Prop)
(f : forall v : value, P (Val v))
(f0 : forall x : variable, P (Var x))
(f1 : forall (op : operation)
(args : list expression),
Forall P args -> P (Op op args))  =>
fix F (c: expression) : P c := 
match c as c0 return  (P c0) with
| Val v => f v
| Var x => f0 x
| Op op args => f1 op args (list_deep_ind (Forall P) (Forall_nil _) (Forall_cons _ P) _)
end.
Next Obligation.
induction args. constructor.
simpl in *; 
constructor; auto.
Defined.


Fixpoint evaluate_expression (e: expression): option value :=
match e with
| Val v => Some v
| Var _ => None
| Op op args =>
    match strip_option (map evaluate_expression args) with
    | None => None
    | Some l => eval_op op l
    end
end.

Inductive process :=
| p_end (lz: list expression)
| p_rec (P: process) (*New process variable is implicit by De Bruijn*)
| p_send (p: participant) (l: label) (e: expression) (P: process)
| p_recv (p: participant) (cont: slist process) (*New variable is implicit by De Bruijn*)
| p_newq (P: process) (*New quantum variable is implicit by De Bruijn*)
| p_unitary (n: nat) (U: base_Unitary n) (lz: list expression) (P: process)
| p_measure (z: expression) (P: process) (*New classic variable is implicit by De Bruijn*)
| p_ite (e: expression) (P1 P0: process)
| p_var (n: nat) (lz: list expression).


Program Definition process_deep_ind :=
fun (P : process -> Prop) (f7 : forall (n : nat) (lz : list expression), P (p_var n lz))
(f : forall lz : list expression, P (p_end lz))
(f1 : forall (pt : participant) (lb : label) (ex : expression) (pr : process),
P pr -> P (p_send pt lb ex pr))
(f2 : forall (pt : participant) (llp : slist process),
SForall P llp -> P (p_recv pt llp))
(f6 : forall (e : expression) (P1 P2 : process),
P P1 -> P P2 -> P (p_ite e P1 P2))
(f0 : forall (pr : process), P pr -> P (p_rec pr))
(f3 : forall (pr : process), P pr -> P (p_newq pr))
(f4 : forall (n : nat) (U : base_Unitary n) (lz : list expression)
(pr : process), P pr -> P (p_unitary n U lz pr))
(f5 : forall (z : expression) (pr : process),
P pr -> P (p_measure z pr)) =>
fix F (p : process) : P p :=
match p as p0 return (P p0) with
| p_var n lz => f7 n lz
| p_end lz => f lz
| p_send pt lb ex pr => f1 pt lb ex pr (F pr)
| p_recv pt llp => f2 pt llp _
| p_ite e P1 P2 => f6 e P1 P2 (F P1) (F P2)
| p_rec pr => f0 pr (F pr) 
| p_newq pr => f3 pr (F pr)
| p_unitary n U lz pr => f4 n U lz pr (F pr)
| p_measure z pr => f5 z pr (F pr)
end.
Next Obligation.
induction llp; try constructor; auto.
destruct o; constructor; eauto.
Defined.

Definition session := finite_map participant process.

Definition session_participants (s: session) := map fst (elems _ _ s).

(** Semantics **)

(* De Bruijn index shifting for expression variables. Shift each variable >= fv by m *)
Fixpoint incr_free_expression (fv m : fin) (e : expression) :=
match e with
| Val v => Val v
| Var (n) => Var ((if Nat.leb fv n then (n + m) else n))
| Op op args => Op op (map (incr_free_expression fv m) args)
end.


(* De Bruijn index shifting for process and expression variables. 
Shift each process variable n >= fvP to n + m
Shift each expression variable n >= fvE to n + k *)
Fixpoint incr_free (fvP fvE m k : fin) (P : process) : process :=
match P with 
| p_var n lz         => p_var (if Nat.leb fvP n then ((n + m)) else n) (map (incr_free_expression fvE k) lz)
| p_end lz         => p_end (map (incr_free_expression fvE k) lz)
| p_send p l e P'  => p_send p l (incr_free_expression fvE k e) (incr_free fvP fvE m k P')
| p_recv p llp     => p_recv p (smap (incr_free fvP (S fvE) m k) llp)
| p_ite e P1 P2    => p_ite (incr_free_expression fvE k e) (incr_free fvP fvE m k P1) (incr_free fvP fvE m k P2)
| p_rec P'         => p_rec (incr_free (S fvP) fvE m k P')
| p_newq P'     => p_newq (incr_free fvP (S fvE) m k P')
| p_unitary n U lz P' => p_unitary n U (map (incr_free_expression fvE k) lz) (incr_free fvP fvE m k P')
| p_measure z P' =>  p_measure (incr_free_expression fvE k z) (incr_free fvP (S fvE) m k P')
end.

Lemma p_var_subst_eq :
forall k x P,
match k with 
| 0   => if Nat.eqb x 0 then P else p_var 0 
| S k => if Nat.eqb x (S k) then P else  
        if Nat.leb x (S k) then p_var k
                            else p_var (S k)
end = if Nat.ltb k x then 
      p_var k
    else if Nat.eqb k x then 
      P
    else
        p_var (k-1).
Proof.
    intros; repeat case_analysis; clean_natb; try lia; simpl; eauto;
    rewrite Nat.sub_0_r; eauto.
Qed.

(* Process substitution Q[x/P] while shifting process variables in P by m and expression variables in P by n. *)
Fixpoint substitutionP (x m n : fin) (P Q : process) : process :=
match Q with 
| p_var k lz =>
    if Nat.ltb k x then 
      p_var k lz
    else if Nat.eqb k x then 
      (incr_free 0 0 m n P) 
    else
        p_var (k-1) lz
| p_end lz => p_end lz
| p_send pt l e Q' => p_send pt l e (substitutionP x m n P Q')
| p_recv pt xs     => p_recv pt (smap (substitutionP x m (S n) P) xs)
| p_ite e Q1 Q2    => p_ite e (substitutionP x m n P Q1) (substitutionP x m n P Q2)
| p_rec Q'         => p_rec (substitutionP (S x) (S m) n P Q')
| p_newq P'         => p_newq (substitutionP x m (S n) P P')
| p_unitary n' U lz P' => p_unitary n' U lz (substitutionP x m n P P')
| p_measure z P'    =>  p_measure z (substitutionP x m (S n) P P')
end.

(* Pre-congruence generated by one-step recursive unfolding plus
    reflexive/transitive closure.  Used to compare sessions modulo unfold. *)
Inductive precongP : relation process := 
| gttR : forall P, precongP P P
| gttS : forall P P', precongP (substitutionP 0 0 0 (p_rec P) P) P' -> precongP (p_rec P) P'
| gttT : forall P P' P'', precongP P P' -> precongP P' P'' -> precongP P P''.


(* Expression substitution e1[n/e] while shifting expression variables in e by d *)
Fixpoint subst_expression (n d : fin) (e e1 : expression) : expression :=
match e1 with 
| Val v => Val v
| Var m => 
    if Nat.ltb m n then 
        Var m
    else if Nat.eqb m n then 
        (incr_free_expression 0 d e) 
    else 
        Var (m-1)
| Op op args => Op op (map (subst_expression n d e) args)
end.

(* Substitute nth variable with e' in P by shifting variables in e' by d.*)
Fixpoint subst_expression_in_process (n d : fin) (e' : expression) (P : process): process :=
match P with 
| p_var k lz => p_var k (map (subst_expression n d e') lz)
| p_end lz => p_end (map (subst_expression n d e') lz)
| p_send pt l e Q' => p_send pt l (subst_expression n d e' e) (subst_expression_in_process n d e' Q')
| p_recv pt xs => p_recv pt (smap (subst_expression_in_process (S n) (S d) e') xs)
| p_ite e Q1 Q2    => 
    p_ite (subst_expression n d e' e)
        (subst_expression_in_process n d e' Q1) (subst_expression_in_process n d e' Q2)
| p_rec Q'         => p_rec (subst_expression_in_process n d e' Q')
| p_newq P'         => p_newq (subst_expression_in_process (S n) (S d) e' P')
| p_unitary n' U lz P' => 
    p_unitary n' U (map (subst_expression n d e') lz) (subst_expression_in_process n d e' P')
| p_measure z P' =>  
    p_measure (subst_expression n d e' z) 
        (subst_expression_in_process (S n) (S d) e' P')
end.


Local Open Scope nat_scope.
Definition state := (quantum_state * session)%type.

(* unrolling of sessions *)
Definition unfoldM (M M' : session) := forall pt, (M pt = None /\ M' pt = None) \/ (exists P P', M pt = Some P /\ M' pt = Some P' /\ precongP P P').

Lemma equivalent_unfoldM : forall M M',
    equivalent M M' -> unfoldM M M'.
Proof.
  intros M M' [HMM' HM'M] pt.
  unfold unfoldM.
  destruct (M pt) as [P|] eqn:HM.
  - right. exists P, P. split; [exact eq_refl|]. split.
    + exact (HMM' pt P HM).
    + apply gttR.
  - destruct (M' pt) as [P'|] eqn:HM'.
    + exfalso. pose proof (HM'M pt P' HM') as Hcontr.
      rewrite HM in Hcontr. discriminate.
    + left. split; reflexivity.
Qed.


Inductive step : state -> action -> state -> R -> Prop :=
| Comm_C: 
    forall p q (l: label) e P lQ l Q v (s1: finite_map participant process) q_state,
    s1 p = Some (p_send q l e P) ->
    s1 q = Some (p_recv p lQ) ->
    p <> q ->
    header.onth l lQ = Some Q ->
    evaluate_expression e = Some v ->
    (forall q, v <> QVal q) ->
    let Q' := subst_expression_in_process 0 0 (Val v) Q in
    let s2 := (insert (insert s1 q Q') p P) in
    step (q_state, s1) (Transmit p q l v) (q_state, s2) 1%R
| Comm_Q: 
    forall p q (l: label) e P lQ l Q v (s1: finite_map participant process)
      (q_state q_state' : quantum_state) (n : nat)
      (Hlookup : (proj1_sig (projT1 q_state)) v = Some (p, n)),
    s1 p = Some (p_send q l e P) ->
    s1 q = Some (p_recv p lQ) ->
    p <> q ->
    header.onth l lQ = Some Q ->
    evaluate_expression e = Some (QVal v) ->
    q_state' = transfer_qubit_from_lookup
      (proj1_sig (projT1 q_state)) (proj2_sig (projT1 q_state))
      (proj1_sig (projT2 q_state)) (proj2_sig (projT2 q_state)) q v p n Hlookup ->
    let Q' := subst_expression_in_process 0 0 (Val (QVal v)) Q in
    let s2 := (insert (insert s1 q Q') p P) in
    step (q_state, s1) (Transmit p q l (QVal v)) (q_state', s2) 1%R
| New: 
    forall p P (s1: finite_map participant process) q_state1 q Hfresh,
    s1 p = Some (p_newq P) ->
    let q_state2 := add_new_qubit q_state1 p q Hfresh in
    let s2 := (insert s1 p (subst_expression_in_process 0 0 (Val (QVal q)) P)) in
    step (q_state1, s1) (Tau p) (q_state2, s2) 1%R
| If_0:
    forall p e P1 P0 (s1: finite_map participant process) q_state,
    s1 p = Some (p_ite e P1 P0) ->
    evaluate_expression e = Some (Bool false) ->
    let s2 := (insert s1 p P0) in
    step (q_state, s1) (Tau p) (q_state, s2) 1%R
| If_1:
    forall p e P1 P0 (s1: finite_map participant process) q_state,
    s1 p = Some (p_ite e P1 P0) ->
    evaluate_expression e = Some (Bool true) ->
    let s2 := (insert s1 p P1) in
    step (q_state, s1) (Tau p) (q_state, s2) 1%R
| Meas: 
    forall p q P (s1: finite_map participant process) (q_state1 q_state2: quantum_state)
      n r (pi : {prob : R | (prob > 0)%R})
      (Hlookup : (projT1 q_state1)! q = Some (p, n))
      (Hlen : 0 < Datatypes.length
        (elems qubit_reference (participant * nat) (proj1_sig (projT1 q_state1))))
      (Hnonzero : norm
        (proj n (Datatypes.length
          (elems qubit_reference (participant * nat) (proj1_sig (projT1 q_state1))))
          r × (proj1_sig (projT2 q_state1))) <> 0%R),
    s1 p = Some (p_measure (Val (QVal q)) P) ->
    (pi, q_state2) = measure_qubit_from_nonzero
      (proj1_sig (projT1 q_state1)) (proj2_sig (projT1 q_state1))
      (proj1_sig (projT2 q_state1)) (proj2_sig (projT2 q_state1))
      q p n r Hlookup Hlen Hnonzero ->
    let s2 := (insert s1 p (subst_expression_in_process 0 0 (Val (Bool r)) P)) in
    step (q_state1, s1) (Tau p) (q_state2, s2) pi!
| Unitary:
    forall dim p U lq P (s1: finite_map participant process) q_state1 q_state2 Hlen Hdim,
    s1 p = Some (p_unitary dim U (map (fun z => Val (QVal z)) lq) P) ->
    apply_unitary (proj1_sig (projT1 q_state1)) (proj2_sig (projT1 q_state1)) (proj1_sig (projT2 q_state1)) (proj2_sig (projT2 q_state1)) U lq Hlen Hdim = Some q_state2 ->
    NoDup lq ->
    Forall (fun q => exists n, (proj1_sig (projT1 q_state1)) q = Some (p, n)) lq ->
    let s2 := (insert s1 p P) in
    step (q_state1, s1) (Tau p) (q_state2, s2) 1%R
| Congr : forall M1 M1' M2 q_state1 q_state2 a r,
    unfoldM M1 M1' -> 
    step (q_state1, M1') a (q_state2, M2) r ->
    step (q_state1, M1) a (q_state2, M2) r.


Lemma unfoldM_refl : forall M, unfoldM M M.
Proof.
  intros M p.
  destruct (M p) as [P|] eqn:HM.
  - right. exists P, P. repeat split; try assumption. apply gttR.
  - left. split; reflexivity.
Qed.

Lemma unfoldM_trans : forall M M' M'',
    unfoldM M M' -> unfoldM M' M'' -> unfoldM M M''.
Proof.
  intros M M' M'' HMM' HM'M'' p.
  specialize (HMM' p). specialize (HM'M'' p).
  destruct HMM' as [[Hnone Hnone']|[P [P' [HM [HM' HP]]]]].
  - destruct HM'M'' as [[Hnone_mid Hnone_end]|[Pmid [Pend [Hmid [Hend Hpre]]]]].
    + left. split; [exact Hnone|exact Hnone_end].
    + congruence.
  - destruct HM'M'' as [[Hnone_mid Hnone_end]|[Pmid [Pend [Hmid [Hend Hpre]]]]].
    + congruence.
    + right. exists P, Pend. split; [exact HM|]. split; [exact Hend|].
      assert (P' = Pmid) by congruence. subst Pmid.
      eapply gttT; eassumption.
Qed.

Lemma precongP_nonrec : forall P P', precongP P P' ->
    (forall R, P <> p_rec R) -> P' = P.
Proof.
  intros P P' Hpre.
  induction Hpre; intros Hnonrec.
  - reflexivity.
  - exfalso. apply (Hnonrec P). reflexivity.
  - transitivity P'.
    + apply IHHpre2. intros R Heq. apply (Hnonrec R).
      rewrite <- (IHHpre1 Hnonrec). exact Heq.
    + apply IHHpre1. exact Hnonrec.
Qed.

Lemma unfoldM_insert : forall M M' p P,
    unfoldM M M' ->
    unfoldM (insert M p P) (insert M' p P).
Proof.
  intros M M' p P Hunfold pt.
  destruct (participant_dec pt p) as [->|Hneq].
  - rewrite !insert_eq. right. exists P, P. repeat split; try reflexivity.
    apply gttR.
  - rewrite !insert_neq by congruence. apply Hunfold.
Qed.

Lemma unfoldM_insert_two : forall M M' p P q Q,
    unfoldM M M' ->
    unfoldM (insert (insert M q Q) p P)
      (insert (insert M' q Q) p P).
Proof.
  intros. apply unfoldM_insert. apply unfoldM_insert. assumption.
Qed.

Lemma unfoldM_lookup_nonrec : forall M M' p P,
    unfoldM M M' -> M p = Some P ->
    (forall R, P <> p_rec R) -> M' p = Some P.
Proof.
  intros M M' p P Hunfold Hlookup Hnonrec.
  destruct (Hunfold p) as [[Hnone _]|[P0 [P' [H0 [H' Hpre]]]]].
  - rewrite Hlookup in Hnone. discriminate.
  - rewrite Hlookup in H0. inversion H0; subst P0.
    pose proof (precongP_nonrec _ _ Hpre Hnonrec) as Heq.
    subst P'. exact H'.
Qed.


Lemma step_inv_Comm_C : forall (q_state : quantum_state)
    (s1 : session) p q l v (q_state' : quantum_state) (s2 : session) r e P lQ,
    (forall q0, v <> QVal q0) ->
    step (q_state, s1) (Transmit p q l v) (q_state', s2) r ->
    s1 p = Some (p_send q l e P) ->
    s1 q = Some (p_recv p lQ) ->
    exists Q,
       p <> q /\
      header.onth l lQ = Some Q /\ evaluate_expression e = Some v /\
      unfoldM (insert (insert s1 q
        (subst_expression_in_process 0 0 (Val v) Q)) p P) s2 /\
      q_state' = q_state /\ r = 1%R.
Proof.
  intros q_state s1 p q l v q_state' s2 r e P lQ Hnotq Hstep.
  remember (Transmit p q l v) as a eqn:Ha.
  remember (q_state, s1) as src eqn:Hsrc.
  remember (q_state', s2) as dst eqn:Hdst.
  revert q_state s1 q_state' s2 Ha Hsrc Hdst.
  induction Hstep; intros qs ss qs' ss' Ha Hsrc Hdst Hp Hq;
    try discriminate.
  - inversion Ha; inversion Hsrc; inversion Hdst; subst.
    inversion Hp; inversion Hq; subst.
    assert (e0 = e) by congruence. subst e0.
    assert (P0 = P) by congruence. subst P0.
    assert (lQ0 = lQ) by congruence. subst lQ0.
    exists Q. split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
    split; [apply unfoldM_refl|]. split; reflexivity.
  - inversion Ha; subst. exfalso. apply (Hnotq v0). reflexivity.
  - inversion Hsrc; inversion Hdst; subst.
    pose proof (unfoldM_lookup_nonrec ss M1' p
      (p_send q l e P) H Hp
      ltac:(intros R Hneq; discriminate Hneq)) as Hp'.
    pose proof (unfoldM_lookup_nonrec ss M1' q
      (p_recv p lQ) H Hq
      ltac:(intros R Hneq; discriminate Hneq)) as Hq'.
    destruct (IHHstep qs M1' qs' ss' eq_refl eq_refl eq_refl Hp' Hq')
      as [Q [Hneq [Hnth [Heval [Hmid [Hqs Hr]]]]]].
    exists Q. split; [exact Hneq|]. split; [exact Hnth|].
    split; [exact Heval|].
    split.
    + eapply unfoldM_trans.
      * apply unfoldM_insert_two. exact H.
      * exact Hmid.
    + split; assumption.
Qed.

Lemma step_inv_Comm_Q : forall (q_state : quantum_state)
    (s1 : session) p q l v (q_state' : quantum_state) (s2 : session) r e P lQ,
    step (q_state, s1) (Transmit p q l (QVal v)) (q_state', s2) r ->
    s1 p = Some (p_send q l e P) ->
    s1 q = Some (p_recv p lQ) ->
    exists  Q old n
      (Hlookup : (proj1_sig (projT1 q_state)) v = Some (old, n)),
       p <> q /\
      header.onth l lQ = Some Q /\
      evaluate_expression e = Some (QVal v) /\
      q_state' = transfer_qubit_from_lookup
        (proj1_sig (projT1 q_state)) (proj2_sig (projT1 q_state))
        (proj1_sig (projT2 q_state)) (proj2_sig (projT2 q_state))
        q v old n Hlookup /\
      unfoldM (insert (insert s1 q
        (subst_expression_in_process 0 0 (Val (QVal v)) Q)) p P) s2 /\
      r = 1%R.
Proof.
  intros q_state s1 p q l v q_state' s2 r e P lQ Hstep.
  remember (Transmit p q l (QVal v)) as a eqn:Ha.
  remember (q_state, s1) as src eqn:Hsrc.
  remember (q_state', s2) as dst eqn:Hdst.
  revert q_state s1 q_state' s2 Ha Hsrc Hdst.
  induction Hstep; intros qs ss qs' ss' Ha Hsrc Hdst Hp Hq;
    try discriminate.
  - inversion Ha; subst. exfalso. apply (H4 v). reflexivity.
  - inversion Ha; inversion Hsrc; inversion Hdst; subst.
    inversion Hp; inversion Hq; subst.
    assert (e0 = e) by congruence. subst e0.
    assert (P0 = P) by congruence. subst P0.
    assert (lQ0 = lQ) by congruence. subst lQ0.
    exists Q, p, n, Hlookup.
    split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
    split; [reflexivity|]. split; [apply unfoldM_refl|reflexivity].
  - inversion Hsrc; inversion Hdst; subst.
    pose proof (unfoldM_lookup_nonrec ss M1' p
      (p_send q l e P) H Hp
      ltac:(intros R Hneq; discriminate Hneq)) as Hp'.
    pose proof (unfoldM_lookup_nonrec ss M1' q
      (p_recv p lQ) H Hq
      ltac:(intros R Hneq; discriminate Hneq)) as Hq'.
    destruct (IHHstep qs M1' qs' ss' eq_refl eq_refl eq_refl Hp' Hq')
      as [Q [old [n [Hlookup [Hneq [Hnth [Heval [Hqs [Hmid Hr]]]]]]]]].
    exists Q, old, n, Hlookup. split; [exact Hneq|].
    split; [exact Hnth|]. split; [exact Heval|]. split; [exact Hqs|].
    split.
    + eapply unfoldM_trans.
      * apply unfoldM_insert_two. exact H.
      * exact Hmid.
    + exact Hr.
Qed.

Lemma step_inv_Comm:
forall (s1 : session) p q l v (q_state q_state' : quantum_state) (s2 : session) r e P lQ,
    step (q_state, s1) (Transmit p q l v) (q_state', s2) r ->
    s1 p = Some (p_send q l e P) ->
    s1 q = Some (p_recv p lQ) ->
    ((forall q0, v <> QVal q0) /\
      exists Q,
      p <> q /\
      header.onth l lQ = Some Q /\ evaluate_expression e = Some v /\
      unfoldM (insert (insert s1 q
        (subst_expression_in_process 0 0 (Val v) Q)) p P) s2 /\
      q_state' = q_state /\ r = 1%R) \/
      (exists v' Q old n
      (Hlookup : (proj1_sig (projT1 q_state)) v' = Some (old, n)),
      v = (QVal v') /\
       p <> q /\
      header.onth l lQ = Some Q /\
      evaluate_expression e = Some (QVal v') /\
      q_state' = transfer_qubit_from_lookup
        (proj1_sig (projT1 q_state)) (proj2_sig (projT1 q_state))
        (proj1_sig (projT2 q_state)) (proj2_sig (projT2 q_state))
        q v' old n Hlookup /\
      unfoldM (insert (insert s1 q
        (subst_expression_in_process 0 0 (Val (QVal v')) Q)) p P) s2 /\
      r = 1%R).
Proof.
  intros.
  destruct v.
  left; split; intros.
  congruence.
  eapply step_inv_Comm_C; eauto.
  congruence.
  left; split; intros.
  congruence.
  eapply step_inv_Comm_C; eauto.
  congruence.
  eapply step_inv_Comm_Q in H; eauto; cleanup.
  right; repeat (eexists; eauto).
Qed.

Lemma step_inv_New : forall (q_state : quantum_state)
    (s1 : session) p P (q_state' : quantum_state) (s2 : session) r,
    s1 p = Some (p_newq P) ->
    step (q_state, s1) (Tau p) (q_state', s2) r ->
    exists q (Hfresh : ~ In q
      (map fst (elems qubit_reference (participant * nat)
        (proj1_sig (projT1 q_state))))),
      q_state' = add_new_qubit q_state p q Hfresh /\
      unfoldM (insert s1 p
        (subst_expression_in_process 0 0 (Val (QVal q)) P)) s2 /\ r = 1%R.
Proof.
  intros q_state s1 p P q_state' s2 r Hproc Hstep.
  remember (Tau p) as a eqn:Ha.
  remember (q_state, s1) as src eqn:Hsrc.
  remember (q_state', s2) as dst eqn:Hdst.
  revert q_state s1 q_state' s2 Ha Hsrc Hdst Hproc.
  induction Hstep; intros qs ss qs' ss' Ha Hsrc Hdst Hproc;
    try discriminate.
  - inversion Ha; inversion Hsrc; inversion Hdst; subst.
    inversion Hproc; subst.
    assert (P = P0) by congruence. subst P0.
    exists q, Hfresh. split; [reflexivity|].
    split; [apply unfoldM_refl|reflexivity].
  - congruence.
  - congruence.
  - congruence.
  - congruence.
  - inversion Hsrc; inversion Hdst; subst.
    pose proof (unfoldM_lookup_nonrec ss M1' p (p_newq P) H Hproc
      ltac:(intros R Hneq; discriminate Hneq)) as Hproc'.
    destruct (IHHstep qs M1' qs' ss' eq_refl eq_refl eq_refl Hproc')
      as [q0 [Hfresh [Hstate [Hmid Hr]]]].
    exists q0, Hfresh. split; [exact Hstate|].
    split.
    + eapply unfoldM_trans.
      * apply unfoldM_insert. exact H.
      * exact Hmid.
    + exact Hr.
Qed.

Lemma step_inv_If : forall (q_state : quantum_state)
    (s1 : session) p e P1 P0 (q_state' : quantum_state) (s2 : session) r,
    s1 p = Some (p_ite e P1 P0) ->
    step (q_state, s1) (Tau p) (q_state', s2) r ->
    ((evaluate_expression e = Some (Bool false) /\ unfoldM (insert s1 p P0) s2) \/ (evaluate_expression e = Some (Bool true) /\ unfoldM (insert s1 p P1) s2)) /\
    q_state' = q_state /\ r = 1%R.
Proof.
  intros q_state s1 p e P1 P0 q_state' s2 r Hproc Hstep.
  remember (Tau p) as a eqn:Ha.
  remember (q_state, s1) as src eqn:Hsrc.
  remember (q_state', s2) as dst eqn:Hdst.
  revert q_state s1 q_state' s2 Ha Hsrc Hdst Hproc.
  induction Hstep; intros qs ss qs' ss' Ha Hsrc Hdst Hproc;
    try discriminate.
  - congruence.
  - inversion Ha; inversion Hsrc; inversion Hdst; subst.
    assert (e0 = e) by congruence. subst e0.
    assert (P3 = P0) by congruence. subst P3.
    split; [left; split; [exact H0|apply unfoldM_refl]|].
    split; reflexivity.
  - inversion Ha; inversion Hsrc; inversion Hdst; subst.
    assert (e0 = e) by congruence. subst e0.
    assert (P2 = P1) by congruence. subst P2.
    split; [right; split; [exact H0|apply unfoldM_refl]|].
    split; reflexivity.
  - congruence.
  - congruence.
  - inversion Hsrc; inversion Hdst; subst.
    pose proof (unfoldM_lookup_nonrec ss M1' p (p_ite e P1 P0) H Hproc
      ltac:(intros R Hneq; discriminate Hneq)) as Hproc'.
    destruct (IHHstep qs M1' qs' ss' eq_refl eq_refl eq_refl Hproc')
      as [Hbranch [Hqs Hr]].
    split.
    + destruct Hbranch as [[Heval Hmid]|[Heval Hmid]].
      * left; split; [exact Heval|].
        eapply unfoldM_trans.
        -- apply unfoldM_insert. exact H.
        -- exact Hmid.
      * right; split; [exact Heval|].
        eapply unfoldM_trans.
        -- apply unfoldM_insert. exact H.
        -- exact Hmid.
    + split; assumption.
Qed.

Lemma step_inv_Meas : forall (q_state : quantum_state)
    (s1 : session) p e P (q_state' : quantum_state) (s2 : session) pi,
    s1 p = Some (p_measure e P) ->
    step (q_state, s1) (Tau p) (q_state', s2) pi ->
    exists q n r (Hprob : {prob : R | (prob > 0)%R})
      (Hlookup : (projT1 q_state)! q = Some (p, n))
      (Hlen : 0 < Datatypes.length
        (elems qubit_reference (participant * nat)
          (proj1_sig (projT1 q_state))))
      (Hnonzero : norm
        (proj n (Datatypes.length
          (elems qubit_reference (participant * nat)
            (proj1_sig (projT1 q_state))))
          r × (proj1_sig (projT2 q_state))) <> 0%R),
      e = (Val (QVal q)) /\
      (Hprob, q_state') = measure_qubit_from_nonzero
        (proj1_sig (projT1 q_state)) (proj2_sig (projT1 q_state))
        (proj1_sig (projT2 q_state)) (proj2_sig (projT2 q_state))
        q p n r Hlookup Hlen Hnonzero /\
      unfoldM (insert s1 p
        (subst_expression_in_process 0 0 (Val (Bool r)) P)) s2.
Proof.
  intros q_state s1 p e P q_state' s2 pi Hproc Hstep.
  remember (Tau p) as a eqn:Ha.
  remember (q_state, s1) as src eqn:Hsrc.
  remember (q_state', s2) as dst eqn:Hdst.
  revert q_state s1 q_state' s2 Ha Hsrc Hdst Hproc.
  induction Hstep; intros qs ss qs' ss' Ha Hsrc Hdst Hproc;
    try discriminate.
  - congruence.
  - congruence.
  - congruence.
  - inversion Ha; inversion Hsrc; inversion Hdst; subst.
    assert (e = Val (QVal q)) by congruence.
    assert (P = P0) by congruence. subst P0.
    exists q, n, r, pi, Hlookup, Hlen, Hnonzero.
    split; [assumption|]. split; [exact H0|apply unfoldM_refl].
  - congruence.
  - inversion Hsrc; inversion Hdst; subst.
    pose proof (unfoldM_lookup_nonrec ss M1' p (p_measure e P) H Hproc
      ltac:(intros R Hneq; discriminate Hneq)) as Hproc'.
    destruct (IHHstep qs M1' qs' ss' eq_refl eq_refl eq_refl Hproc')
      as [q [n [r0 [Hprob [Hlookup [Hlen [Hnonzero [He [Hmeasure Hmid]]]]]]]]].
    exists q, n, r0, Hprob, Hlookup, Hlen, Hnonzero.
    split; [exact He|]. split; [exact Hmeasure|].
    eapply unfoldM_trans.
    + apply unfoldM_insert. exact H.
    + exact Hmid.
Qed.

Lemma step_inv_Unitary : forall (q_state : quantum_state)
    (s1 : session) p dim U le P (q_state' : quantum_state) (s2 : session) r,
    s1 p = Some (p_unitary dim U le P) ->
    step (q_state, s1) (Tau p) (q_state', s2) r ->
    exists lq Hlen Hdim,
      le = (map (fun z => Val (QVal z)) lq) /\
      apply_unitary (proj1_sig (projT1 q_state))
        (proj2_sig (projT1 q_state)) (proj1_sig (projT2 q_state))
        (proj2_sig (projT2 q_state)) U lq Hlen Hdim = Some q_state' /\
      NoDup lq /\
      Forall (fun q => exists n,
        (proj1_sig (projT1 q_state)) q = Some (p, n)) lq /\
      unfoldM (insert s1 p P) s2 /\ r = 1%R.
Proof.
  intros q_state s1 p dim U le P q_state' s2 r Hproc Hstep.
  remember (Tau p) as a eqn:Ha.
  remember (q_state, s1) as src eqn:Hsrc.
  remember (q_state', s2) as dst eqn:Hdst.
  revert q_state s1 q_state' s2 Ha Hsrc Hdst Hproc.
  induction Hstep; intros qs ss qs' ss' Ha Hsrc Hdst Hproc;
    try discriminate.
  - congruence.
  - congruence.
  - congruence.
  - congruence.
  - inversion Ha; inversion Hsrc; inversion Hdst; subst.
    rewrite H in Hproc. injection Hproc as Hshape.
    inversion Hshape; subst.
    sigT_eq.
    exists lq, eq_refl, Hdim.
    split; [reflexivity|]. split; [exact H0|].
    split; [exact H1|]. split; [exact H2|].
    split; [apply unfoldM_refl|reflexivity].
  - inversion Hsrc; inversion Hdst; subst.
    pose proof (unfoldM_lookup_nonrec ss M1' p
      (p_unitary dim U le P) H Hproc
      ltac:(intros R Hneq; discriminate Hneq)) as Hproc'.
    destruct (IHHstep qs M1' qs' ss' eq_refl eq_refl eq_refl Hproc')
      as [lq [Hlen [Hdim [Hle [Happly [Hnodup [Howned [Hmid Hr]]]]]]]].
    exists lq, Hlen, Hdim. split; [exact Hle|].
    split; [exact Happly|]. split; [exact Hnodup|].
    split; [exact Howned|]. split.
    + eapply unfoldM_trans.
      * apply unfoldM_insert. exact H.
      * exact Hmid.
    + exact Hr.
Qed.

Inductive multistep : state -> list action -> state -> R -> Prop :=
| ms_refl : forall qstate s s', 
    equivalent s s' -> (*Allows reordering of processes *)
    multistep (qstate, s) nil (qstate, s') 1%R
| ms_step: forall s1 s2 s3 r1 r2 a la, 
    step s1 a s2 r1 ->
    multistep s2 la s3 r2 ->
    multistep s1 (a::la) s3 (r1 * r2).

Lemma multistep_equivalent_source : forall qstate M M' la S r,
    equivalent M M' ->
    multistep (qstate, M') la S r ->
    multistep (qstate, M) la S r.
Proof.
  intros qstate M M' la S r HMM' Hmulti.
  dependent induction Hmulti.
  - apply ms_refl.
    eapply equivalent_trans; eauto.
  - destruct s2 as [q2 M2].
    eapply ms_step.
    + eapply Congr with (M1' := M').
      * apply equivalent_unfoldM. exact HMM'.
      * exact H.
    + assumption.
Qed.


Definition finished (M: session) :=
forall p Q, M p = Some Q -> exists lz, precongP Q (p_end lz).


Fixpoint size (P: process) :=
match P with
| p_end lz => 1
| p_rec P' => S(size P')
| p_send p l e P' => S(size P')
| p_recv p cont => S (fold_right add 0 (to_list (smap size cont)))
| p_newq P' => S(size P')
| p_unitary n U lz P' => S(size P')
| p_measure z P' =>  S(size P')
| p_ite e P1 P0 => S(size P1 + size P0)
| p_var X lz => 1
end.


Fixpoint appears_in_expression (e: expression) (x: variable) : bool :=
match e with
| Val _ => false
| Var x' => Nat.eqb x x'
| Op _ args => fold_right (fun e => orb (appears_in_expression e x)) false args
end.

Fixpoint free_process_var_in_process (bound: fin) (P: process) (x: fin) : bool :=
    match P with
    | p_end lz => false
    
    | p_rec P' => 
    free_process_var_in_process (S bound) P' x
    
    | p_send p l e P' => (free_process_var_in_process bound P' x)

    | p_recv p cont => 
    fold_right orb false (to_list (smap  (fun P => free_process_var_in_process bound P x) cont))

    | p_newq P' => 
    free_process_var_in_process bound P' x


    | p_unitary n U lz P' => 
     (free_process_var_in_process bound P' x)

    | p_measure z P' =>  
    (free_process_var_in_process (bound) P' x)

    | p_ite e P1 P0 => 
     (orb (free_process_var_in_process bound P1 x) (free_process_var_in_process bound P0 x))

    | p_var X lz => Nat.eqb X (x + bound)
end.

(* Expressions use de Bruijn indices.  The depth records the number of
   expression binders crossed on the way from the root of a process. *)
Inductive closed_expression_at : nat -> expression -> Prop :=
| closed_val_at : forall depth v,
    closed_expression_at depth (Val v)
| closed_bound_var_at : forall depth x,
    x < depth ->
    closed_expression_at depth (Var x)
| closed_op_at : forall depth op args,
    Forall (closed_expression_at depth) args ->
    closed_expression_at depth (Op op args).

Inductive variable_closed_process_at : nat -> process -> Prop :=
| closed_end_at : forall depth lz,
    Forall (closed_expression_at depth) lz ->
    variable_closed_process_at depth (p_end lz)
| closed_rec_at : forall depth P,
    variable_closed_process_at depth P ->
    variable_closed_process_at depth (p_rec P)
| closed_send_at : forall depth p l e P,
    closed_expression_at depth e ->
    variable_closed_process_at depth P ->
    variable_closed_process_at depth (p_send p l e P)
| closed_recv_at : forall depth p cont,
    SForall (variable_closed_process_at (S depth)) cont ->
    variable_closed_process_at depth (p_recv p cont)
| closed_newq_at : forall depth P,
    variable_closed_process_at (S depth) P ->
    variable_closed_process_at depth (p_newq P)
| closed_unitary_at : forall depth n U lz P,
    Forall (closed_expression_at depth) lz ->
    variable_closed_process_at depth P ->
    variable_closed_process_at depth (p_unitary n U lz P)
| closed_measure_at : forall depth z P,
    closed_expression_at depth z ->
    variable_closed_process_at (S depth) P ->
    variable_closed_process_at depth (p_measure z P)
| closed_ite_at : forall depth e P1 P0,
    closed_expression_at depth e ->
    variable_closed_process_at depth P1 ->
    variable_closed_process_at depth P0 ->
    variable_closed_process_at depth (p_ite e P1 P0)
| closed_var_at : forall depth n lz,
    Forall (closed_expression_at depth) lz ->
    variable_closed_process_at depth (p_var n lz).

(* Every session expression is closed at the session boundary.  Expression
   binders in receive, measurement, and allocation continuations are tracked
   by [variable_closed_process_at]. *)
Definition variable_closed_session (s : session) :=
  forall p Q, s p = Some Q -> variable_closed_process_at 0 Q.

Lemma Forall_impl_In:
forall [A : Type] [P : A -> Prop] (Q : A -> Prop) (l : list A),
(forall a : A, In a l -> P a -> Q a) ->
 Forall P l -> Forall Q l.
Proof.
    induction l; simpl; intros; eauto.
    cleanup; constructor; eauto.
Qed.

Fixpoint get_qubits_expression (e: expression) : list qubit_reference :=
match e with
| Val (QVal q) => q::nil
| Op _ args => flat_map get_qubits_expression args
| _ => nil
end.

Definition get_qubits (l: list expression) :=
flat_map get_qubits_expression l.

Fixpoint free_qubits (P: process): list qubit_reference :=
match P with
| p_end lz =>
    get_qubits lz

| p_rec P' => 
    free_qubits P'

| p_send p l e P' => 
    get_qubits (e::nil) ++ free_qubits P'

| p_recv p cont => 
    fold_right (@app qubit_reference) nil (to_list (smap free_qubits cont))

| p_newq P' => 
    free_qubits P'

| p_unitary n U lz P' => 
    get_qubits lz ++ free_qubits P'

| p_measure z P' =>  
    get_qubits (z::nil) ++ free_qubits P'

| p_ite e P1 P0 => 
    get_qubits (e::nil) ++ free_qubits P1 ++ free_qubits P0

| p_var X lz => get_qubits lz
end. 

Lemma multistep_app:
forall l1 l2 S S' S'' pi pi',
multistep S l1 S' pi ->
multistep S' l2 S'' pi' ->
multistep S (l1++l2) S'' (pi * pi').
Proof.
  intros l1 l2 S S' S'' pi pi' H1 H2.
  revert l2 S'' pi' H2.
  induction H1; intros l2 S'' pi' H2.
  - simpl. replace (1 * pi')%R with pi' by ring.
    eapply multistep_equivalent_source; eauto.
  - simpl.
    replace ((r1 * r2) * pi')%R with (r1 * (r2 * pi'))%R by ring.
    eapply ms_step.
    + exact H.
    + exact (IHmultistep l2 S'' pi' H2).
Qed.

Lemma multistep_app_rev:
forall l1 l2 S S'' pi,
multistep S (l1++l2) S'' pi ->
exists S' pi' pi'',
multistep S l1 S' pi' /\
multistep S' l2 S'' pi'' /\
pi = (pi' * pi'')%R.
Proof.
  intros l1.
  induction l1 as [|a l1 IH]; intros l2 S S'' pi H.
  - simpl in H.
    exists S, 1%R, pi.
    split.
    + destruct S as [qstate M]. simpl. apply ms_refl. apply equivalent_refl.
    + split; [exact H|].
      rewrite Rmult_1_l. reflexivity.
  - simpl in H.
    inversion H as [|s1 s2 s3 r1 r2 a' la Hstep Htail]; subst.
    destruct (IH l2 s2 S'' r2 Htail)
      as [S' [pi' [pi'' [Hleft [Hright Hprob]]]]].
    exists S', (r1 * pi')%R, pi''.
    split.
    + eapply ms_step; eauto.
    + split; [exact Hright|].
      rewrite Hprob.
      rewrite Rmult_assoc. reflexivity.
Qed.

End Process.
