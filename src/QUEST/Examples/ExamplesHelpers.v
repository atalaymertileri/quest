From Paco Require Import paco.
From SQIR Require Import SQIR.
Require Import Permutation Reals List String Lia.
Require Import Automation FMap Primitives Process SST Typechecking.

Notation "'UNIT'" := (Val (Primitives.Bool false)).

Lemma insert_equiv_lemma : 
forall A B KEQ (map map': finite_map A B) k v,
equivalent map map' -> 
equivalent (insert (KEQ := KEQ) map k v) (insert (KEQ := KEQ) map' k v) .
Proof.
  intros. destruct H; unfold included in *.
  split.
  unfold included.
  intros. inversion H1.
  destruct (KEQ k k0) eqn: E. 
  subst. inversion H3; subst; clear H3. apply insert_eq.
  specialize (H k0 v0 H3). rewrite H3. rewrite <- H.  apply insert_neq. auto. 
  unfold included. intros.
  intros. inversion H1.
  destruct (KEQ k k0) eqn: E. 
  subst. inversion H3; subst; clear H3. apply insert_eq.
  specialize (H0 k0 v0 H3). rewrite H3. rewrite <- H0.  apply insert_neq. auto.
Qed. 

Lemma delete_equiv_lemma : 
forall A B KEQ (map map': finite_map A B) k ,
equivalent map map' -> 
equivalent (delete (KEQ := KEQ) map k ) (delete (KEQ := KEQ) map' k ) .
Proof.
  intros.
  destruct H; unfold included in *.
  split; unfold included; intros.
  inversion H1. destruct (KEQ k k0).
  discriminate. specialize (H _ _ H3). rewrite H3. rewrite <- H.
  apply delete_neq. auto.
  inversion H1.
  destruct (KEQ k k0). subst. rewrite delete_eq in H1. discriminate. 
  specialize (H0 _ _ H3). rewrite H3. rewrite <- H0.
  apply delete_neq. auto.
Qed. 



Lemma typecheck_process_send_unit_step :
forall p_context c_context q_context p (l : label) (P: process) (Q: ltt),
typecheck_process (p_context, c_context, q_context)
P Q -> 
typecheck_process (p_context, c_context, q_context)
(p_send p l UNIT P)
(ltt_send p (fun n => if Nat.eqb n l then Some (Bool, Q) else None)).
Proof. 
  intros.
  econstructor; simpl; eauto.
  econstructor; eauto.
Qed.

Lemma SForall2_extendSlis:
forall A B P n (a: A) (b: B),
P a b ->
SForall2 P (extendSlis n a) (extendSlis n b).
Proof.
  induction n; simpl; intros;
  econstructor; eauto.
Qed.


Lemma append_length :
forall s1 s2,
length (s1 ++ s2)%string = (length s1 + length s2).
Proof.
    induction s1; simpl; eauto.
Qed.

Lemma string_append_l:
forall s1 s2 s,
(s1 ++ s)%string = (s2 ++ s)%string -> s1 = s2.
Proof.
    induction s1; destruct s2; simpl in *; eauto;
    intros;
    inversion H.

    assert_fresh (length s = length (String a (s2 ++ s))). {
        rewrite H at 1; eauto.
    }
    simpl in *.
    rewrite append_length in HA.
    lia.
    assert_fresh (length s = length (String a (s1 ++ s))). {
        rewrite H at 1; eauto.
    }
    simpl in *.
    rewrite append_length in HA.
    lia.
    erewrite IHs1; eauto.
Qed.

Definition Alice := (Pt "Alice").
Definition Bob := (Pt "Bob").
Definition Charlie := (Pt "Charlie").
Definition Env := (Pt "Env").
Definition Source := (Pt "Source").
Definition Rnd := (Pt "Rnd").

Notation "a .=. b" := (Op Beq (a :: b :: nil))
  (at level 20, b at next level).
Notation ".~. a" := (Op Not (a :: nil))
  (at level 21, a at next level).
Notation "a .\\/. b" := (Op Or (a :: b :: nil))
  (at level 20, b at next level).
Notation "a .&&. b" := (Op And (a :: b :: nil))
  (at level 20, b at next level).

Notation "p .+ l <. v .>;" := (p_send p l v)(at level 0).

Notation "p .& l .; P" := (p_recv p (extendSlis l P))(at level 0, P at next level).

(* Allow a full continuation, including applications and nested receives. *)
Notation "p .& l => P" := (p_recv p (extendSlis l P))
  (at level 0, P at level 200).

(* Two receive branches at labels 0 and 1. Each continuation binds the
   received value at index 0, just like a singleton receive. *)
Notation "p .& { 0 => P | 1 => Q }" := (p_recv p (slist_xs (Some P) (slist_x Q))) (at level 0, P at level 200, Q at level 200).

Notation "U [. l .];" := (p_unitary _ U l)(at level 0).
Notation "'IF' e 'THEN' P 'ELSE' Q" := (p_ite e P Q)(at level 0, P at next level).
 
Notation "p --> q $ l (. B .); G" := (g_send p q (extendSlis l (B, G)))(at level 0, G at next level).

Notation "p --> q $ { 0 (. B0 .); G0 | 1 (. B1 .); G1 }" :=
  (g_send p q (slist_xs (Some (B0, G0)) (slist_x (B1, G1))))
  (at level 0, G0 at level 200, G1 at level 200).

Notation "p -c-> q $ l (. B .); G" := (gtt_send p q (fun t => if Nat.eqb t l then Some (B, G) else None))(at level 0, G at next level).

Notation "p -c-> q $ { 0 (. B0 .); G0 | 1 (. B1 .); G1 }" :=
  (gtt_send p q (fun t => onth t
    (slist_xs (Some (B0, G0)) (slist_x (B1, G1)))))
  (at level 0, G0 at level 200, G1 at level 200).

Notation "p .&. l (. B .); T" := (ltt_recv p (fun t => onth t (extendSlis l (B, T))))(at level 0, T at next level).

Notation "p .+. l (. B .); T" := (ltt_send p (fun t => if Nat.eqb t l then Some (B, T) else None))(at level 0, T at next level).

Notation "p .&. { 0 (. B0 .); T0 | 1 (. B1 .); T1 }" := (ltt_recv p (fun t => onth t (slist_xs (Some (B0, T0)) (slist_x (B1, T1)))))
  (at level 0, T0 at level 200, T1 at level 200).

Notation "p .+. { 0 (. B0 .); T0 | 1 (. B1 .); T1 }" := (ltt_send p (fun t => onth t (slist_xs (Some (B0, T0)) (slist_x (B1, T1)))))
  (at level 0, T0 at level 200, T1 at level 200).


Ltac gttTC_step:= 
pfold; econstructor; simpl;
intros; 
match goal with 
| [|- context [onth ?n]] =>
destruct n
end; simpl; eauto;
right; do 3 eexists; repeat split; eauto;
left.
