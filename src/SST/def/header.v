From mathcomp Require Import ssreflect.seq all_ssreflect.
Require Import List String PeanoNat Arith Relations ZArith Datatypes Setoid Morphisms Coq.Logic.Decidable Coq.Program.Basics Coq.Init.Datatypes ListUtils Bool Lia.
From QUEST Require Import Automation.
Import ListNotations. 
Open Scope list_scope.
From Paco Require Import paco.

(* ------------------------------------------------------------------------- *)
(* Shared foundations used across the development.                           *)
(*                                                                           *)
(* This file defines common aliases, helper lemmas, list/stream utilities,   *)
(* and Ltac helpers that are reused in both definition and proof files.      *)
(* ------------------------------------------------------------------------- *)

Notation fin := nat.
Notation label := nat (only parsing).
Notation "p '.1'" := (fst p).
Notation "p '.2'" := (snd p).

Inductive participant := | Pt (name: string).
Instance participant_dec : EqDec participant.
unfold EqDec. repeat decide equality.
Defined.

Instance bool_eqdec : EqDec bool := bool_dec.

Definition variable := fin.
Instance v_dec : EqDec variable.
unfold EqDec. repeat decide equality.
Defined.

Inductive sort :=
| Nat
| Bool
| Qubit.

Instance sort_eqdec: EqDec sort.
unfold EqDec; repeat decide equality.
Defined.



Section helper.

  (* Basic arithmetic/list helper lemmas used globally. *)
  Lemma max_l : forall m m1, m <= Nat.max m m1.
  Proof.
    induction m; intros; try easy.
    revert IHm. revert m. induction m1; intros; try easy.
    apply IHm; try easy.
  Qed.

  Lemma max_r : forall m m1, m1 <= Nat.max m m1.
  Proof.
    induction m; intros; try easy.
    revert IHm. revert m. induction m1; intros; try easy.
    apply IHm; try easy.
  Qed.

  Fixpoint iter {A} (n : fin) (f : A -> A) (e : A) : A := 
    match n with 
      | S m => (iter m f (f e))
      | _   => e
    end.


  Lemma always_exists {A} (a : A) : exists b, a = b.
  Proof.
    exists a. easy.
  Qed.


  Lemma leq_to_eq_le : forall n m, n <= m -> n = m \/ n < m.
  Proof.
    induction n; intros.
    - destruct m; try easy.
      - left. easy.
      - right. easy.
    - destruct m; try easy.
      specialize(IHn m H).
      destruct IHn. 
      - left. subst. easy.
      - right. easy.
  Qed.
    
  Lemma triad_le : forall n m, (Nat.eqb n m) \/ (Nat.ltb n m) \/ (Nat.ltb m n).
  Proof.
    induction n; intros.
    - destruct m.
      - left. easy.
      - right. left. easy.
    - destruct m; try easy.
      - right. right. easy.
      - specialize(IHn m).
        easy.
  Qed.


  Lemma strong_ind (P : fin -> Prop) :
    (forall m, (forall k : nat, k < m -> P k) -> P m) ->
      forall n, P n.
  Proof.
    intros H n; enough (H0: forall p, p <= n -> P p).
      - apply H0. easy. 
      - induction n.
        + intros. destruct p; try easy. apply H. intros. inversion H1.
        + intros. apply H. intros. apply IHn. 
          destruct p; try easy.
          clear H IHn. clear P.
          revert H1 H0.
          revert n p.
          induction k; intros; try easy.
          destruct p; try easy. destruct n; try easy.
          apply IHk with (p := p); try easy.
  Qed.

  Lemma coq_nat_to_nat_le : forall a b,
    (a <= b)%coq_nat -> 
    a <= b.
  Proof.
    induction a; intros.
    - destruct b; try easy.
    - destruct b; try easy.
      specialize(le_S_n a b H); intros.
      specialize(IHa b H0). clear H H0.
      revert IHa. revert b.
      induction a; intros.
      - destruct b; try easy.
      - destruct b; try easy.
  Qed.
End helper.

Section slist.

  (* Sparse lists:
     - `slist_x` is the final mandatory element
     - `slist_xs` prefixes optional positions. *)
  Variable A : Type.

  Inductive slist : Type :=
  | slist_x : A -> slist 
  | slist_xs : option A -> slist -> slist.

  Fixpoint to_list (l: slist) : list A :=
  match l with
  | slist_x a => a::nil
  | slist_xs oa la => 
    match oa with
    | Some a => a::to_list la
    | None => to_list la
    end
  end.
End slist.

Arguments slist_x {A}.
Arguments slist_xs {A}.
Arguments to_list {A}.

Section slist_extend.

  Variable A : Type.
  Variable B : Type.
  Variable P : A -> Prop.
  Variable R : A -> B -> Prop.
  
  Section map.
    (* Map over sparse lists while preserving shape. *)
    Variable f : A -> B.
    Fixpoint smap (xs : slist A) : slist B :=
      match xs with 
        | slist_x y => slist_x (f y)
        | slist_xs None ys => slist_xs None (smap ys)
        | slist_xs (Some y) ys => slist_xs (Some (f y)) (smap ys)
      end.
  End map.

  Section slist_Forall.
    Inductive SForall : slist A -> Prop :=
      | SForall_x   : forall x, P x -> SForall (slist_x x)
      | SForall_sxs : forall x xs, P x -> SForall xs -> SForall (slist_xs (Some x) xs)
      | SForall_nxs : forall xs, SForall xs -> SForall (slist_xs (None) xs).
      
    Inductive SForall2 : slist A -> slist B -> Prop :=
      | SForall2_x   : forall x y, R x y -> SForall2 (slist_x x) (slist_x y)
      | SForall2_sxs : forall x y xs ys, R x y -> SForall2 xs ys -> SForall2 (slist_xs (Some x) xs) (slist_xs (Some y) ys)
      | SForall2_nxs : forall xs ys, SForall2 xs ys -> SForall2 (slist_xs None xs) (slist_xs None ys).
  End slist_Forall.
  
  Section extend_extract.
    (* Access and finite-extension operations for sparse lists. *)
    Fixpoint onth (n : fin) (xs : slist A) : option A :=
      match n with 
        | S m => 
          match xs with 
            | slist_xs _ ys => onth m ys
            | _             => None
          end
        | 0 =>
          match xs with 
            | slist_xs y _ => y
            | slist_x y    => Some y
          end
      end.
    
    Fixpoint extendSlis (n : fin) (x : A) : slist A :=
      match n with 
        | S m => slist_xs None (extendSlis m x)
        | 0   => slist_x x
      end.
  
  End extend_extract.

End slist_extend.

Arguments smap {A} {B}.
Arguments onth {A}.
Arguments extendSlis {A}.
Arguments SForall {A}.
Arguments SForall2 {A} {B}.

Section slist_lemma.
  Variable A : Type.
  Variable B : Type.
  
  Lemma SForall_mono : forall xs (P Q : A -> Prop),  (forall x, P x -> Q x) -> SForall P xs -> SForall Q xs.
  Proof.
    induction xs; intros; try easy.
    - constructor. 
      inversion H0. subst. apply H; try easy.
    - inversion H0. subst.
      - constructor. apply H; try easy.
        eapply IHxs with (P := P); try easy.
      - subst. 
        constructor. 
        apply IHxs with (P := P); try easy.
  Qed.
  
  Lemma SForall_mono2 : forall xs (P Q R : A -> Prop), (forall x, P x -> Q x -> R x) -> SForall P xs -> SForall Q xs -> SForall R xs.
  Proof.
    induction xs; intros; try easy.
    - constructor. 
      inversion H0. subst. inversion H1. subst. apply H; try easy.
    - inversion H0. subst. inversion H1. subst.
      - constructor. apply H; try easy.
        apply IHxs with (P := P) (Q := Q); try easy.
      - subst. inversion H1. subst.
        constructor. 
        apply IHxs with (P := P) (Q := Q); try easy.
  Qed.
  
  Definition SForall2_mono {R T : A -> B -> Prop} (HRT : forall x y, R x y -> T x y) :
      forall l m, SForall2 R l m -> SForall2 T l m :=
  fix loop l m h {struct h} :=
    match h with
    | SForall2_x Ha Hb Hc => SForall2_x A B T Ha Hb (HRT Ha Hb Hc)
    | SForall2_sxs Ha Hb _ _ He Hf => SForall2_sxs A B T Ha Hb _ _ (HRT Ha Hb He) (loop _ _ Hf)
    | SForall2_nxs _ _ Hc => SForall2_nxs A B T _ _ (loop _ _ Hc)
    end.
  
  Lemma SForall_onth : forall n (xs : slist A) P t, SForall P xs -> onth n xs = Some t -> P t.
  Proof. 
    induction n; intros.
    - destruct xs; try easy.
      - inversion H0. subst.
        inversion H. easy.
      inversion H.
      - subst. clear H.
        inversion H0. subst. easy.
      - subst. inversion H0.
    - destruct xs; try easy.
      specialize(IHn xs P t).
      apply IHn; try easy.
      inversion H. 
      - easy.
      - easy.
  Qed.
  
  Lemma SForall2_onth_l : forall n (xs : slist A) (ys : slist B) P t, SForall2 P xs ys -> onth n xs = Some t -> exists t', onth n ys = Some t' /\ P t t'.
  Proof.
    induction n; intros.
    - destruct xs; try easy.
      inversion H0. subst. destruct ys; try easy.
      inversion H. subst. exists b. easy.
      simpl in H0. subst.
      inversion H. subst. exists y. easy.
    - destruct xs; try easy.
      destruct ys; try easy.
      apply IHn with xs; try easy.
      inversion H; try easy.
  Qed.
  
  Lemma SForall2_onth_r : forall n (xs : slist A) (ys : slist B) P t', SForall2 P xs ys -> onth n ys = Some t' -> exists t, onth n xs = Some t /\ P t t'.
  Proof.
    induction n; intros.
    - destruct ys; try easy.
      inversion H0. subst. destruct xs; try easy.
      inversion H. subst. exists a. easy.
      simpl in H0. subst.
      inversion H. subst. exists x. easy.
    - destruct ys; try easy.
      destruct xs; try easy.
      apply IHn with ys; try easy.
      inversion H; try easy.
  Qed.
  
  Lemma onth_move_out : forall n (f : A -> B) (lis : slist A) x, onth n (smap f lis) = Some x -> exists t, onth n lis = Some t /\ f t = x.
  Proof.
    induction n; intros.
    - destruct lis; try easy.
      - inversion H. subst. simpl.
        exists a. easy.
      - simpl in H. destruct o; try easy.
        exists a. inversion H. subst. easy.
    - destruct lis; try easy.
      apply IHn. destruct o; try easy.
  Qed.

  Definition slist_to_func (lis : slist A) : fin -> option A := (fun i => onth i lis).
  
  Lemma onth_to_some : forall (xs : slist A), exists n t, onth n xs = Some t.
    Proof.
      induction xs; intros.
      - exists 0. exists a. easy.
      - destruct IHxs as (n,(t,Ha)).
        exists (S n). exists t. easy.
    Qed.

Lemma SForall_forall:
forall A (P: A -> Prop) l,
(forall n a, onth n l = Some a -> P a) <->
SForall P l.
Proof.
    induction l; simpl in *; intros.
    econstructor; intros.
    econstructor.
    eapply (H 0); eauto.
    inversionc H.
    destruct n; simpl in *; cleanup; try congruence; eauto.
    
    destruct o; econstructor; eauto; intros.
    econstructor.
    eapply (H 0); eauto.
    eapply IHl; intros.
    eapply (H (S n)); eauto.

    inversionc H.
    destruct n; simpl in *; cleanup; eauto.
    eapply IHl in H4; eauto.

    econstructor.
    eapply IHl; eauto.
    intros.
    eapply (H (S n)); simpl; eauto.

    inversionc H.
    destruct n; simpl in *; cleanup; eauto.
    eapply IHl in H2; eauto.
Qed.

Fixpoint Slength {A} (l: slist A) : nat :=
match l with
| slist_x a => 1 
| slist_xs o la => S (Slength la)
end.

Lemma SForall2_forall:
forall A B (P: A -> B -> Prop) la lb,
((forall n a b, onth n la = Some a -> onth n lb = Some b ->  P a b) /\
(forall n, onth n la = None <-> onth n lb = None) /\
(Slength la = Slength lb)) <->
SForall2 P la lb.
Proof.
    induction la; simpl in *; intros;
    destruct lb; simpl in *.
    
    split; intros; cleanup.
    econstructor.
    eapply (H 0); eauto.
    inversionc H; cleanup.
    repeat split; intros.
    destruct n; simpl in *; cleanup; try congruence; eauto.
    destruct n; simpl in *; cleanup; try congruence; eauto.
    destruct n; simpl in *; cleanup; try congruence; eauto.

    destruct lb; simpl in *;
    split; intros; cleanup; try lia.
    inversion H.
    inversion H.

    destruct la; simpl in *;
    split; intros; cleanup; try lia.
    inversion H.
    inversion H.

    destruct o, o0; split; intros; cleanup.

    econstructor.
    eapply (H 0); eauto.
    eapply IHla; intros.
    repeat split; intros.
    eapply (H (S n)); eauto.
    eapply (H0 (S n)); simpl; eauto.
    eapply (H0 (S n)); simpl; eauto.
    lia.

    inversionc H.
    apply IHla in H5; cleanup.
    repeat split; intros.
    destruct n; simpl in *; cleanup; try congruence; eauto.
    destruct n; simpl in *; cleanup; try congruence; eauto.
    apply H0; eauto.
    destruct n; simpl in *; cleanup; try congruence; eauto.
    apply H0; eauto.
    specialize (H0 0); simpl in *; eauto.
    intuition congruence.

    inversion H.
    specialize (H0 0); simpl in *; eauto.
    intuition congruence.

    inversion H.
    econstructor.
    eapply IHla; intros.
    repeat split; intros.
    eapply (H (S n)); eauto.
    eapply (H0 (S n)); simpl; eauto.
    eapply (H0 (S n)); simpl; eauto.
    lia.

    inversionc H.
    apply IHla in H2; cleanup.
    repeat split; intros.
    destruct n; simpl in *; cleanup; try congruence; eauto.
    destruct n; simpl in *; cleanup; try congruence; eauto.
    apply H0; eauto.
    destruct n; simpl in *; cleanup; try congruence; eauto.
    apply H0; eauto.
Qed.

Lemma In_to_list_onth:
forall A l (a: A),
In a (to_list l) ->
exists n, onth n l = Some a.
Proof.
  induction l; simpl; eauto.
  intros; split_ors; cleanup.
  exists 0; simpl; eauto.
  
  intros; case_analysis; cleanup.
  simpl in H; intros; split_ors; cleanup.
  exists 0; simpl; eauto.
  edestruct IHl; eauto.
  exists (S x); simpl; eauto.
  edestruct IHl; eauto.
  exists (S x); simpl; eauto.
Qed.

Lemma onth_to_list_In:
forall A l n (a: A),
onth n l = Some a -> 
In a (to_list l). 
Proof.
  induction l; simpl; eauto;
  intros; destruct n; simpl in *; cleanup; 
  simpl; eauto.
  case_analysis; simpl; eauto.
Qed. 

Lemma onth_move_in : forall A B (f : A -> B) (lis : slist A) n x, onth n lis = Some x ->
onth n (smap f lis) = Some (f x).
Proof.
  induction lis; simpl; intros;
  destruct n; simpl in *;
  cleanup; eauto.

  repeat case_analysis; cleanup;
  inversionc HD; eauto.
Qed.

Lemma onth_move_out_inj : forall A B (f : A -> B) (lis : slist A) n x, onth n (smap f lis) = Some (f x) -> 
(forall a b, f a = f b -> a = b) ->
onth n lis = Some x.
Proof.
  induction lis; simpl; intros;
  destruct n; simpl in *;
  cleanup; eauto.

  erewrite (H0 a x); eauto.
  repeat case_analysis; cleanup.
  inversionc HD.
  erewrite (H0 a x); eauto.

  repeat case_analysis; cleanup;
  inversionc HD; eauto.
Qed.

End slist_lemma.

Arguments SForall_mono {A}.
Arguments SForall_mono2 {A}.
Arguments SForall2_mono {A} {B}.
Arguments SForall_onth {A}.
Arguments SForall2_onth_l {A} {B}.
Arguments SForall2_onth_r {A} {B}.
Arguments onth_move_out {A B}.
Arguments slist_to_func {A}.
Arguments onth_to_some {A}.

Section bmerge.

  (* Boolean-mask merge operators used by guard/closed analyses. *)
  Fixpoint bmerge (xs ys : list bool) : list bool :=
      match (xs, ys) with 
        | (xs, nil) => xs
        | (nil, ys) => ys
        | (x::xs, y::ys) => (x || y) :: bmerge xs ys
      end.
    
  Fixpoint bmergelis (xs : slist (list bool)) : list bool :=
    match xs with 
      | slist_x y => y
      | slist_xs None ys => bmergelis ys
      | slist_xs (Some y) ys => bmerge y (bmergelis ys)
    end.
    
  Lemma bmerge_nil : forall xs ys, bmerge xs ys = nil -> xs = nil /\ ys = nil.
  Proof.  
    induction xs; intros; try easy.
    - destruct ys; try easy.
    - destruct ys; try easy.
  Qed.

  Lemma bmerge_self : forall xs, bmerge xs xs = xs.
  Proof.
    induction xs; intros; try easy.
    simpl. rewrite IHxs. destruct a; try easy.
  Qed.

  Lemma bmerge_again_l : forall xs ys, bmerge xs (bmerge xs ys) = bmerge xs ys.
  Proof.
    induction xs; intros; try easy.
    - destruct ys; try easy.
    - destruct ys; try easy.
      - simpl.
        specialize(bmerge_self xs); intros.
        rewrite H. destruct a; try easy.
      - specialize(IHxs ys).
        simpl. rewrite IHxs.
        destruct a; try easy.
  Qed.

  Lemma bmerge_again_r : forall xs ys, bmerge ys (bmerge xs ys) = bmerge xs ys.
  Proof.
    intros xs ys. revert xs.
    induction ys; intros; try easy.
    - destruct xs; try easy.
    - destruct xs; try easy.
      - simpl.
        specialize(bmerge_self ys); intros.
        rewrite H. destruct a; try easy.
      - specialize(IHys xs).
        simpl. rewrite IHys.
        destruct a; try easy.
        simpl. destruct b; try easy.
  Qed.

  Fixpoint bmergeR (xs ys : list bool) : list bool :=
    match (xs, ys) with 
      | (_xs, nil) => nil
      | (nil, _ys) => nil 
      | (x::_xs, y::_ys) => (x && y) :: bmergeR _xs _ys
    end.

  Lemma bmerge_comm : forall xs ys, bmerge xs ys = bmerge ys xs.
  Proof.
    induction xs; intros; try easy.
    - destruct ys; try easy.
    - destruct ys; try easy.
      specialize(IHxs ys).
      simpl. rewrite IHxs.
      destruct a; try easy.
      - destruct b; try easy.
      - destruct b; try easy.
  Qed.

  Lemma bmerge_again : forall xs ys zs, bmerge xs zs = zs -> bmerge ys zs = zs -> bmerge (bmerge xs ys) zs = zs.
  Proof.
    intros xs ys zs. revert xs ys.
    induction zs; intros; try easy.
    - destruct xs; try easy.
      destruct ys; try easy.
    - destruct xs; try easy.
      - destruct ys; try easy.
      - destruct ys; try easy.
        inversion H. inversion H0.
        specialize(IHzs xs ys H3 H5).
        clear H H0.
        simpl. 
        rewrite H5. rewrite H3.
        rewrite IHzs.
        destruct b; try easy.
        destruct b0; try easy.
  Qed.


  Lemma bmergeR_back : forall xs ys, bmerge (bmergeR xs ys) ys = ys.
  Proof.
    induction xs; intros; try easy.
    - simpl.
      induction ys; intros; try easy.
    - destruct ys; try easy.
      simpl.
      specialize(IHxs ys). rewrite IHxs.
      destruct a; try easy.
      destruct b; try easy.
  Qed.
  
  Fixpoint boollis (n : fin) : list bool := 
    match n with 
      | S m => false :: boollis m
      | 0   => [true]
    end.
  
  Fixpoint allfalse (xs : list bool) : Prop :=
    match xs with 
      | nil => True 
      | y::ys => y = false /\ allfalse ys
    end.
  
  Fixpoint false_list (n : fin) : list bool :=
    match n with 
      | 0 => nil
      | S m => false :: false_list m
    end.
  
  Lemma allfalse_bmerge_break : forall xs ys, allfalse (bmerge xs ys) -> allfalse xs /\ allfalse ys.
  Proof.
    induction xs; intros.
    - destruct ys; try easy.
    - destruct ys; try easy.
      inversion H.
      specialize(IHxs ys H1).
      simpl. destruct a; try easy. 
  Qed.

End bmerge.
  
Section list_nth.

  Lemma nth_extract {A} : forall xl (xe : option A) xr, nth (length xl) (xl ++ [xe] ++ xr) None = xe.
  Proof.
    induction xl; intros.
    - easy.
    - simpl in *.
      specialize(IHxl xe xr). rewrite IHxl. easy.
  Qed.

  Lemma nth_morec {A} : forall Gtl Gtr n X x (tm : option A),
        (length Gtl <= n) = true ->
        nth (n + X) (Gtl ++ Gtr) None = Some x ->
        Some x = nth (n + X.+1) (Gtl ++ tm :: Gtr) None.
  Proof.
    induction Gtl; intros; try easy.
    - simpl in *. 
      specialize(addnS n X); intros. rewrite H1. easy.
    - destruct n. easy. simpl in *.
      apply IHGtl; try easy.
  Qed.

  Lemma nth_lessc {A} : forall Gtl Gtr n x (tm : option A),
        (length Gtl <= n) = false ->
        nth n (Gtl ++ Gtr) None = Some x ->
        Some x = nth n (Gtl ++ tm :: Gtr) None.
  Proof.
    induction Gtl; intros; try easy.
    destruct n; try easy.
    simpl in *.
    apply IHGtl; try easy.
  Qed.

  Lemma nth_sless {X} : forall n (Gsl Gsr : list (option X)) x0 S,
        n < length Gsl ->
        nth n (Gsl ++ Some S :: Gsr) None = Some x0 ->
        nth n (Gsl ++ Gsr) None = Some x0.
  Proof.
    intro n. induction n; intros; try easy.
    - destruct Gsl; try easy.
    - destruct Gsl; try easy. apply IHn with (S := S); try easy.
  Qed.

  Lemma nth_smore {X} : forall n (Gsl Gsr : list (option X)) x0 o S,
        n <> length Gsl ->
        length Gsl <= n ->
        Some x0 = nth n (Gsl ++ Some S :: Gsr) None ->
        Some x0 = nth n (o :: Gsl ++ Gsr) None.
  Proof.
    intro n. induction n; intros; try easy.
    destruct Gsl; try easy.
    simpl in *. destruct Gsl; try easy.
    apply IHn with (S := S); try easy. simpl in *.
    specialize(Nat.succ_inj_wd_neg n (length Gsl)); intros. destruct H2. specialize(H2 H). easy.
  Qed.

  Lemma coq_nat_to_nat_lt : forall a b, (a < b)%coq_nat -> a < b.
  Proof.
    induction a; intros.
    - destruct b; try easy.
    - destruct b; try easy.
      specialize(PeanoNat.lt_S_n a b H); intros.
      specialize(IHa b H0). clear H H0.
      revert IHa. revert b.
      induction a; intros.
      - destruct b; try easy.
      - destruct b; try easy.
  Qed.

End list_nth.


Section multi.

  (* Reflexive-transitive closures (`multi`, `multi1`). *)
  Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x 
  | multi_step : forall (x y z : X), R x y -> multi R y z -> multi R x z.
  
  Lemma multi_trans {x : Type} : forall (R : relation x) X Y Z, multi R X Y -> multi R Y Z -> multi R X Z.
  Proof.
    intros. revert H0. revert Z.
    induction H; intros; try easy. 
    specialize(IHmulti Z H1). apply multi_step with y; try easy.
  Qed.
  
  Inductive multi1 {X : Type} (R : relation X) : relation X :=
  | multi1_just : forall (x y : X), R x y -> multi1 R x y 
  | multi1_step : forall (x y z : X), R x y -> multi1 R y z -> multi1 R x z.
  
  Lemma multi1_trans {x : Type} : forall (R : relation x) X Y Z, multi1 R X Y -> multi1 R Y Z -> multi1 R X Z.
  Proof.
    intros. revert H0. revert Z.
    induction H; intros; try easy.
    - apply multi1_step with y; try easy. 
    - specialize(IHmulti1 Z H1). apply multi1_step with y; try easy.
  Qed.
  
  Lemma multi1_multi {x : Type} : forall (R : relation x) X Y, multi1 R X Y -> multi R X Y.
  Proof.
    intros. induction H; intros.
    - apply multi_step with y; try easy. constructor.
    - apply multi_step with y; try easy.
  Qed.
  
  Inductive multif {A B : Type} (R : relation (A -> B)) : relation (A -> B) := 
    | multif_refl : forall (f g : A -> B), (forall x, f x = g x) -> multif R f g
    | multif_step : forall (f g h : A -> B), R f g -> multif R g h -> multif R f h.
    
  Lemma multif_trans {A B : Type} : 
      forall (R : relation (A -> B))
             (R_closed_l : forall (f g h : A -> B),
                  (forall x, f x = g x) -> R g h -> R f h)
             X Y Z, 
      multif R X Y -> multif R Y Z -> multif R X Z.
  Proof.
    intros R R_closed_l X Y Z HXY HYZ.
    assert (Hlift :
      forall (f g z : A -> B),
        (forall x, f x = g x) -> multif R g z -> multif R f z).
    {
      intros f g z Heq Hgz.
      revert f Heq.
      induction Hgz; intros f0 Heq.
      - apply multif_refl.
        intro x.
        rewrite Heq.
        apply H.
      - eapply multif_step.
        + eapply R_closed_l; eauto.
        + exact Hgz.
    }
    induction HXY.
    - eapply Hlift; eauto.
    - eapply multif_step.
      + exact H.
      + eauto.
  Qed.

End multi.
   

Section stream.

  (* Finite-or-infinite stream skeleton used for path semantics. *)
  Variable A : Type.
  
  CoInductive stream : Type :=
    | st_end : stream
    | st_cons : A -> stream -> stream.
    
  Fixpoint stnth (n : fin) (gxs : stream) : option A := 
    match gxs with
      | st_end => None
      | st_cons x xs =>
        match n with 
          | 0 => Some x 
          | S m => stnth m xs
        end
    end.

End stream.

Arguments st_end {A}.
Arguments st_cons {A}.
Arguments stnth {A}.

Create HintDb mon.
Ltac mon_easy :=
  auto with mon.

Ltac destruct_exists_and :=
  repeat match goal with
    | H : exists _, _ |- _ => destruct H
    | H : _ /\ _      |- _ => destruct H
    end.
      
Ltac invert_all_some :=
  repeat match goal with
    | H : Some _ = Some _ |- _ => inversion H; subst; clear H
  end.

Ltac fill_triv :=
  repeat match goal with
        | H : ?A -> ?B |- _ =>
          match goal with
          | HA : A |- _ => specialize (H HA)
          end
        end.
      
Ltac concl_of_type T :=
  lazymatch T with
  | forall x : ?A, ?B =>
      (* If x occurs in B, this is a dependent forall: keep it. *)
      lazymatch B with
      | context[x] =>
          let C := concl_of_type B in
          constr:(forall x : A, C)
      | _ =>
          (* Otherwise it's just an arrow (non-dependent): drop it. *)
          concl_of_type B
      end
  | ?C => C
  end.

Tactic Notation "assert_concl_of" ident(Hyp) "as" ident(H) :=
  let T := type of Hyp in
  let C := concl_of_type T in
  assert (C) as H.

  
  