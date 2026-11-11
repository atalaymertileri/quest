Require Import PeanoNat.
Require Import ListUtils.
Require Import Eqdep.
Import ListNotations.

Tactic Notation "eapply_fresh" uconstr(thm) "in" hyp(H) :=
  let Hx := fresh "Hx" in eapply thm in H as Hx.


Tactic Notation "eapply_fresh" uconstr(thm) "with"
       "(" ident(name) ":=" ident(assig) ")" "in" hyp(H) :=
  let Hx := fresh "Hx" in eapply thm with
    (name := assig) in H as Hx.

Tactic Notation "eapply_fresh" uconstr(thm) "with"
       "(" ident(name) ":=" ident(assignee) ")"
       "(" ident(name2) ":=" ident(assignee2) ")" "in" hyp(H) :=
  let Hx := fresh "Hx" in eapply thm with
    (name := assignee)
    (name2 := assignee2) in H as Hx.

Tactic Notation "eapply_fresh" uconstr(thm) "with"
       "(" ident(name) ":=" ident(assignee) ")"
       "(" ident(name2) ":=" ident(assignee2) ")"
       "(" ident(name3) ":=" ident(assignee3) ")" "in" hyp(H) :=
  let Hx := fresh "Hx" in eapply thm with
    (name := assignee)
    (name2 := assignee2)
    (name3 := assignee3) in H as Hx.

Tactic Notation "eapply_fresh" uconstr(thm) "with"
       "(" ident(name) ":=" ident(assignee) ")"
       "(" ident(name2) ":=" ident(assignee2) ")"
       "(" ident(name3) ":=" ident(assignee3) ")"
       "(" ident(name4) ":=" ident(assignee4) ")" "in" hyp(H) :=
  let Hx := fresh "Hx" in eapply thm with
    (name := assignee)
    (name2 := assignee2)
    (name3 := assignee3)
    (name4 := assignee4) in H as Hx.



Tactic Notation "destruct_fresh" constr(term) :=
  let D := fresh "HD" in destruct term eqn:D.

Tactic Notation "assert_fresh" constr(ass) :=
  let A := fresh "HA" in assert ass as A.

  Tactic Notation "assert_fresh" constr(ass) "by" ltac(tac) :=
  let A := fresh "HA" in assert ass as A by tac.

Tactic Notation "assume" "(" ident(label) ":" constr(type) ")" :=
  assert (label: type); [shelve|].

Tactic Notation "assume_fresh" constr(ass) :=
  let A := fresh "HA" in assume (A: ass).

Ltac clean_natb:=
repeat match goal with
|[H: (Nat.leb _ _) = true |- _] =>
apply Nat.leb_le in H
|[H: (Nat.leb _ _) = false |- _] =>
apply Nat.leb_nle in H
|[H: (Nat.ltb _ _) = true |- _] =>
apply Nat.ltb_lt in H
|[H: (Nat.ltb _ _) = false |- _] =>
apply Nat.ltb_nlt in H
|[H: (Nat.eqb _ _) = true |- _] =>
apply Nat.eqb_eq in H
|[H: (Nat.eqb _ _) = false |- _] =>
apply Nat.eqb_neq in H
end.

Ltac sigT_eq :=
  repeat match goal with
  | [ H: existT ?P ?a _ = existT ?P ?a _ |- _ ] =>
    apply Eqdep.EqdepTheory.inj_pair2 in H; subst
  end.

Ltac logic_clean:=
  repeat match goal with
  | [H: exists (name:_), _  |- _] => 
    let name' := fresh name in
    destruct H as [name' H]
  | [H: _ /\ _ |- _] => destruct H
  end.

Ltac invert_const :=
  repeat match goal with
  | [H: Some _ = Some _ |- _ ] =>
    inversion H; subst; clear H
  | [H: Some _ = None |- _ ] =>
    inversion H; subst; clear H
  | [H: None = Some _ |- _ ] =>
    inversion H; subst; clear H
  | [H: (_, _) = (_, _) |- _ ] =>
    inversion H; subst; clear H
  | [H: Forall _ (_::_) |- _ ] =>
    inversion H; subst; clear H
  | [H: Forall2 _ (_::_) (_::_) |- _ ] =>
    inversion H; subst; clear H
  | [H: NoDup (_::_) |- _ ] =>
    inversion H; subst; clear H
  | [H: Forall _ (_ ++ _::_) |- _ ] =>
    eapply_fresh Forall_elt in H;
    eapply_fresh Forall_cons_app in H;
    clear H
  | [H: true = false |- _ ] =>
    congruence
  | [H: false = true |- _ ] =>
    congruence
  | [H: False |- _ ] =>
    inversion H
  | [H: ?P -> False, H0: ?P |- _ ] =>
    exfalso; apply H; eauto
  | [H: ~ ?P, H0: ?P |- _ ] =>
    exfalso; apply H; eauto
  | [H: Forall _ nil |- _ ] =>
    clear H
  | [H: Forall2 _ nil nil |- _ ] =>
    clear H
  end.

Ltac clear_dup:=
  repeat match goal with
  | [H: ?x = ?x |- _] => clear H
  | [H: ?x, H0: ?x |- _] => clear H0
  end.

Ltac rewriteall :=
  repeat match goal with
  | [H := _ |- _] =>
    subst H
  | [H: ?x = _, H0: context [?x] |- _ ] =>
    setoid_rewrite H in H0
  | [H: ?x = _ |-  context [?x] ] =>
    setoid_rewrite H
  end.

Ltac rewriteall_normal :=
  repeat match goal with
  | [H := _ |- _] =>
    subst H
  | [H: ?x = _, H0: context [?x] |- _ ] =>
    rewrite H in H0
  | [H: ?x = _ |-  context [?x] ] =>
    rewrite H
  end.

Ltac list_append_clear:=
  match goal with
  | [H: _++?tr = _++?tr |- _] =>
    apply app_inv_tail in H
  | [H: ?tr++_ = ?tr++_ |- _] =>
    apply app_inv_head in H
  | [H: ?tr = _++?tr |- _] =>
    rewrite <- app_nil_l in H at 1
  | [H: _::?tr = _++?tr |- _] =>
    apply cons_app_inv_tail in H
  | [H: _::_++?tr = _++?tr |- _] =>
    rewrite app_comm_cons in H
  | [H: _++_++?tr = _++?tr |- _] =>
    rewrite app_assoc in H
  | [H: _++?tr = _++_++?tr |- _] =>
    rewrite app_assoc in H
  end.

Ltac clear_lists:=
  repeat match goal with
  | [H: _::_ = _::_ |- _] =>
    inversion H; clear H
  | [H: length _ = 0 |- _] =>
    apply length_zero_iff_nil in H
  | [H: 0 = length _  |- _] =>
    symmetry in H
  | [H: context[ firstn _ [] ] |- _] =>
    rewrite firstn_nil in H
  | [|- context[ firstn _ [] ] ] =>
    rewrite firstn_nil
  | [H: context[ skipn _ [] ] |- _] =>
    rewrite skipn_nil in H
  | [|- context[ skipn _ [] ] ] =>
    rewrite skipn_nil
  | [H: _++ _ = nil |- _] =>
    apply app_eq_nil in H; destruct H
  | [H: nil = _++ _ |- _] =>
    symmetry in H; apply app_eq_nil in H; destruct H
  | _ =>
    list_append_clear
  end.

Ltac cleanup_left_right :=
  repeat match goal with
  |[H: _ = left _  |- _] =>
    clear H
  |[H: _ = right _  |- _] =>
    clear H
  end.

Ltac case_analysis_if:=
  match goal with
  |[H: context [if ?x then _ else _ ] |- _] =>
      destruct_fresh x
  |[|- context [if ?x then _ else _ ] ] =>
      destruct_fresh x
  end; try cleanup_left_right.

Ltac case_analysis_match:=
  match goal with
  |[H: context [if ?x then _ else _ ] |- _] =>
      destruct_fresh x
  |[|- context [if ?x then _ else _ ] ] =>
      destruct_fresh x
  |[H: context [match ?x with | _ => _ end] |- _] =>
      destruct_fresh x
  |[|- context [match ?x with | _ => _ end] ] =>
      destruct_fresh x
  end; try cleanup_left_right.

Ltac case_analysis:=
  (case_analysis_if || case_analysis_match); try cleanup_left_right; try congruence.

Ltac destruct_dependents :=
  repeat match goal with
  |[H: {_ | _} |- _] =>
     destruct H
  end.

Ltac cleanup_setoid:= 
  try logic_clean;
  subst; try rewriteall;
  try clear_dup; try invert_const;
  try clear_lists; try sigT_eq;
  subst; try rewriteall;
  try cleanup_left_right.

Ltac cleanup := 
  try logic_clean;
  subst; try rewriteall_normal;
  try clear_dup; try invert_const;
  try clear_lists; try sigT_eq;
  subst; try rewriteall_normal;
  try cleanup_left_right.

Ltac split_ors:=
  match goal with
  | [H: _ \/ _ |- _ ] => destruct H
  end.

Ltac cleanup_pairs :=
  match goal with
  | [H: context [fst ?x] |- _] =>
    destruct_fresh x
  | [H: context [snd ?x] |- _] =>
    destruct_fresh x
  end; simpl in *; cleanup.

Lemma existsb_false_forallb:
  forall A f (l: list A),
  existsb f l = false <->
  forallb (fun b => negb (f b)) l = true.
  Proof.
      induction l; simpl; intuition eauto.
      apply Bool.orb_false_iff in H1; cleanup.
      apply Bool.andb_true_iff; simpl; eauto.
      apply Bool.andb_true_iff in H1; cleanup.
      apply Bool.orb_false_iff; simpl; eauto.
      destruct (f a); simpl in *; cleanup; eauto.
  Qed.

  Ltac clean_bool_basic :=
    match goal with
    | [H: (_ && _)%bool = true |- _] =>
        apply Bool.andb_true_iff in H; logic_clean
    | [H: (_ && _)%bool = false |- _] =>
        apply Bool.andb_false_iff in H; split_ors
    | [H: negb _ = true |- _] =>
        apply Bool.negb_true_iff in H
    | [H: negb _ = false |- _] =>
        apply Bool.negb_false_iff in H
    | [H: (_ || _)%bool = true |- _] =>
        apply Bool.orb_true_iff in H; split_ors
    | [H: (_ || _)%bool = false |- _] =>
        apply Bool.orb_false_iff in H; logic_clean
    end ; repeat clean_bool_basic.

Ltac clean_bool_exists :=
      (clean_bool_basic || 
      match goal with
      | [H: existsb _ _ = true |- _] =>
          eapply existsb_exists in H; logic_clean
      | [H: existsb _ _ = false |- _] =>
          eapply existsb_false_forallb in H
      end); repeat clean_bool_exists.

Ltac clean_bool :=
    (clean_bool_exists ||
    match goal with
    | [H: forallb _ _ = true |- _] =>
        eapply forallb_forall in H; eauto
    end); repeat clean_bool.

Ltac inversionc H := inversion H; clear H; cleanup.