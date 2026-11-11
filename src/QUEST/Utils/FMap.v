Require Import ListUtils Automation Program.Wf.

Section FMap.
    Variable key: Type.
    Context {KEQ: EqDec key}.
    Variable value : Type.

Record finite_map := {
    m :> key -> option value;
    elems : list (key * value);
    specs : NoDup (map fst elems) /\ (forall k v, In (k, v) elems <-> m k = Some v)   
}.

Fixpoint replace_or_add {A B} {AEQ: EqDec A} (l: list (A * B)) (ab: A * B) :=
match l with
| nil => ab::nil
| h::tl => 
    if AEQ (fst h) (fst ab) then
     ab::tl
    else
        h:: replace_or_add tl ab
end.

Fixpoint remove_fst {A B} {AEQ: EqDec A} (l: list (A * B)) (a: A) :=
match l with
| nil => nil
| h::tl => 
    if AEQ (fst h) a then
     tl
    else
        h:: remove_fst tl a
end.

Program Fixpoint get_all (m: finite_map) (lk: list key) {measure (length lk)}: {ol: option (list value) | forall l, ol = Some l -> (length l = length lk /\ forall kl, In kl (combine lk l) -> m (fst kl) = Some (snd kl)) } :=
match lk with
| nil => Some nil
| k::tl => 
    match m k, get_all m tl with
    | Some v, Some l => exist _ (Some (v::l)) _
    | _, _ => None
    end
end.
Next Obligation.
simpl; split; intros; eauto.
tauto.
Qed.
Next Obligation.
edestruct get_all; simpl in *.
edestruct a; eauto.
simpl in *; split; intros; eauto.
intuition eauto.
inversion H2; subst; eauto.
Qed.

Lemma replace_or_add_not_In : forall A B (AEQ: EqDec A) (l: list (A * B)) ab a,
~In a (map fst l) -> a <> fst ab -> ~In a (map fst (replace_or_add l ab)).
Proof.
    induction l; unfold not; simpl; intros; cleanup.
    split_ors; cleanup; eauto.
    case_analysis; cleanup; simpl in *.
    repeat split_ors; cleanup; eauto.
    eapply IHl; eauto.
Qed.

Lemma replace_or_add_NoDup : forall A B (AEQ: EqDec A) (l: list (A * B)) ab,
NoDup (map fst l) -> NoDup (map fst (replace_or_add l ab)).
Proof.
    induction l; simpl; intros; cleanup.
    econstructor; eauto.
    case_analysis; cleanup; simpl;
    econstructor; eauto.
    eapply replace_or_add_not_In; eauto.
Qed.

Lemma In_fst_map: forall A B (l: list (A * B)) ab,
In ab l -> In (fst ab) (map fst l).
Proof.
    induction l; simpl; intros; cleanup; eauto.
    split_ors; cleanup; eauto.
Qed.

Lemma replace_or_add_In_snd_eq : forall A B (AEQ: EqDec A) (l: list (A * B)) ab ab',
NoDup (map fst l) -> 
In ab (replace_or_add l ab') -> 
fst ab = fst ab' -> snd ab = snd ab'.
Proof.
    induction l; unfold not; simpl; intros; cleanup.
    split_ors; cleanup; eauto.
    case_analysis; cleanup; simpl in *;
    repeat split_ors; cleanup; eauto.
    apply In_fst_map in H; simpl in *.
    cleanup; tauto.
    simpl in *; tauto.
Qed.

Lemma replace_or_add_In_eq : forall A B (AEQ: EqDec A) (l: list (A * B)) ab,
In ab (replace_or_add l ab).
Proof.
    induction l; unfold not; simpl; intros; cleanup; eauto.
    case_analysis; cleanup; simpl in *;
    repeat split_ors; cleanup; eauto.
Qed.

Lemma replace_or_add_In_neq : forall A B (AEQ: EqDec A) (l: list (A * B)) ab ab',
fst ab <> fst ab' ->  
In ab (replace_or_add l ab') <-> In ab l.
Proof.
    induction l; unfold not; simpl; intros; cleanup; eauto.
    split; intros; cleanup.
    split_ors; cleanup; eauto.
    
    case_analysis; cleanup; simpl in *;
    repeat split_ors; cleanup; eauto.

    split; intros; cleanup;
    split_ors; cleanup; eauto;
    exfalso; eauto.

    split; intros; cleanup;
    split_ors; cleanup; eauto.
    apply IHl in H0;
    edestruct IHl; eauto.
    edestruct IHl.
    2: right; apply H2; eauto.
    eauto.
Qed.

Lemma replace_or_add_In_length : forall A B (AEQ: EqDec A) (l: list (A * B)) a,
(exists b,  In (a,b) l) -> 
forall b, length (replace_or_add l (a, b)) = length l.
Proof.
    induction l; simpl; intros; cleanup.
    split_ors; cleanup; eauto.
    case_analysis; cleanup; simpl in *;
    repeat split_ors; cleanup; eauto.
    congruence.
    case_analysis; cleanup; simpl in *;
    repeat split_ors; cleanup; eauto.
Qed.

Lemma replace_or_add_not_In_length : forall A B (AEQ: EqDec A) (l: list (A * B)) a,
(forall b,  ~In (a,b) l) -> 
forall b, length (replace_or_add l (a, b)) = S(length l).
Proof.
    induction l; simpl; intros; cleanup; eauto.
    case_analysis; cleanup; simpl in *;
    repeat split_ors; cleanup; eauto.
    destruct a; simpl in *.
    exfalso; eapply H; eauto.
    erewrite IHl; eauto.
    unfold not; intros;
    destruct a; simpl in *.
    eapply H; eauto.
Qed.

Lemma replace_or_add_not_In_map_snd_NoDup : 
forall A B (AEQ: EqDec A)
(l: list (A * B)) a b,
NoDup (map fst l) ->
NoDup (map snd l) ->
~ In b (map snd l) ->
NoDup (map snd (replace_or_add l (a, b))).
Proof.
    induction l; simpl; intros; cleanup.
    repeat constructor; eauto.
    
    case_analysis; cleanup; simpl in *;
    repeat split_ors; cleanup; eauto.
    constructor; eauto.
    constructor; eauto.
    intros Hnot.
    apply in_map_iff in Hnot; cleanup.
    destruct (AEQ (fst x) a0).
    destruct x; simpl in *; cleanup.
    eapply replace_or_add_In_snd_eq in H0; eauto.
    eapply (replace_or_add_In_neq _ _ _ l) in H0.
    destruct x; simpl in *; cleanup.
    eapply (in_map snd) in H0.
    simpl in *; eauto.
    simpl; eauto.
Qed.

Lemma remove_fst_In:
forall A (AEQ: EqDec A) B (l: list (A * B)) ab a,
In ab (remove_fst l a) ->
In ab l.
Proof.
    induction l; simpl; eauto.
    intros; cleanup.
    case_analysis; cleanup; eauto.
    simpl in *; intuition eauto.
Qed.

Lemma remove_fst_map_fst_NoDup:
  forall A (AEQ: EqDec A) B (l: list (A * B)) a,
  NoDup (map fst l) ->
  NoDup (map fst (remove_fst l a)).
Proof.
    induction l; simpl; eauto.
    intros; cleanup.
    case_analysis; cleanup; eauto.
    simpl; econstructor; intuition eauto.
    apply in_map_iff in H; cleanup.
    apply remove_fst_In in H0.
    eapply (in_map fst) in H0; cleanup;
    intuition eauto.
Qed.

Lemma remove_fst_map_snd_NoDup : 
forall A B (AEQ: EqDec A)
(l: list (A * B)) a,
NoDup (map snd l) ->
NoDup (map snd (remove_fst l a)).
Proof.
    induction l; simpl; intros; cleanup; eauto.
    case_analysis; cleanup; simpl in *;
    repeat split_ors; cleanup; eauto.
    constructor; eauto.
    intuition eauto.
    apply in_map_iff in H; cleanup.
    apply remove_fst_In in H0.
    eapply (in_map snd) in H0; cleanup;
    intuition eauto.
Qed.

Lemma remove_fst_NoDup_not_In:
forall A (AEQ: EqDec A) B (l: list (A * B)) a b,
In (a, b) l ->
NoDup (map fst l) ->
NoDup (map snd l) ->
~In b (map snd (remove_fst l a)).
Proof. 
    induction l; simpl; intros; cleanup; eauto.
    case_analysis; cleanup; simpl in *.
    destruct a; simpl in *.
    split_ors; cleanup; eauto.
    exfalso; apply H3; apply in_map_iff;
    eexists; split; eauto.
    simpl; eauto.

    destruct a; simpl in *.
    split_ors; cleanup; eauto.
    eapply_fresh IHl in H; eauto.
    intuition eauto; cleanup.
    apply H4; apply in_map_iff;
    eexists; split; eauto.
    simpl; eauto.
Qed.

Lemma remove_fst_length_In:
forall A (AEQ: EqDec A) B (l: list (A * B)) a b,
In (a, b) l ->
S (Datatypes.length (remove_fst l a)) = length l. 
Proof.
    induction l; simpl; intros; cleanup; eauto.
    case_analysis; cleanup; simpl in *.
    destruct a; simpl in *.
    split_ors; cleanup; eauto.
    congruence.
Qed.

Lemma replace_or_add_map_NoDup : 
forall A B C (AEQ: EqDec A)
(l: list (A * (B * C))) a b b',
In (a, b) l ->
snd b = snd b' ->
NoDup (map fst l) ->
NoDup (map (fun s => snd (snd s)) l) ->
NoDup (map (fun s => snd (snd s)) (replace_or_add l (a, b'))).
Proof.
    induction l; simpl; intros; cleanup.
    split_ors; cleanup; simpl in *; eauto.
    case_analysis; cleanup; simpl in *;
    repeat split_ors; cleanup; eauto.
    constructor; eauto.
    case_analysis; cleanup; simpl in *;
    repeat split_ors; cleanup; eauto.
    constructor; eauto.
    exfalso; apply H4.
    apply in_map_iff.
    eexists; split; [|eauto]; eauto.
    
    constructor; eauto.
    unfold not; intros Hn; apply H5.
    apply in_map_iff in Hn; cleanup.
    apply in_map_iff. 
    destruct x, a; simpl in *; cleanup.
    destruct (AEQ a0 a1); subst.
    apply replace_or_add_In_snd_eq in H2; eauto.
    simpl in *; subst.
    eexists; split; [|eauto]; simpl; eauto.
    cleanup; eauto.
    apply replace_or_add_In_neq in H2; eauto.
    eexists; split; [|eauto]; simpl; eauto.
Qed.

Lemma replace_or_add_None_map_NoDup : 
forall A B C (AEQ: EqDec A)
(l: list (A * (B * C))) a b,
NoDup (map fst l) ->
NoDup (map (fun s => snd (snd s)) l) ->
Forall (fun b' => snd b <> b') (map (fun s => snd (snd s)) l) ->
NoDup (map (fun s => snd (snd s)) (replace_or_add l (a, b))).
Proof.
    induction l; simpl; intros; cleanup.
    econstructor; eauto.
    case_analysis; cleanup; simpl in *;
    repeat split_ors; cleanup; eauto.
    constructor; eauto.
    unfold not; intros Hn.
    eapply Forall_forall in H5;[| apply Hn].
    congruence.
    econstructor; eauto.
    unfold not; intros Hn.
    apply in_map_iff in Hn; cleanup.
    destruct x, a; simpl in *; cleanup.
    destruct (AEQ a0 a1); subst.
    apply replace_or_add_In_snd_eq in H0; eauto.
    simpl in *; subst; congruence.
    apply H3.
    apply replace_or_add_In_neq in H0; eauto.
    apply in_map_iff; eauto.
    eexists; split; [|eauto]; simpl; eauto.
Qed.

Program Definition insert (m: finite_map) k v : finite_map :=
{| m:= (fun k' => if KEQ k k' then Some v else m k'); 
    elems:= (replace_or_add m.(elems) (k, v));
    specs := _ |}.
Next Obligation.
    destruct m0.(specs).
    split.
    apply replace_or_add_NoDup; eauto.
    intros.
    case_analysis; cleanup; eauto.
    split; intros; cleanup; eauto.
    apply replace_or_add_In_snd_eq in H1; 
    simpl in *; subst; eauto.
    apply replace_or_add_In_eq.
    split; intros.
    apply replace_or_add_In_neq in H1; simpl; eauto.
    apply H0; eauto.
    apply replace_or_add_In_neq; simpl; eauto.
    apply H0; eauto.
Qed.

Lemma remove_not_In : forall A B (AEQ: EqDec A) (l: list (A * B)) ab a,
~In a (map fst l) -> ~In a (map fst (remove_fst l ab)).
Proof.
    induction l; unfold not; simpl; intros; cleanup.
    case_analysis; cleanup; simpl in *.
    repeat split_ors; cleanup; eauto.
    repeat split_ors; cleanup; eauto.
    eapply IHl; eauto.
Qed.


Lemma remove_not_In_2 : forall A B (AEQ: EqDec A) (l: list (A * B)) a,
NoDup (map fst l) -> ~In a (map fst (remove_fst l a)).
Proof.
    induction l; unfold not; simpl; intros; cleanup.
    case_analysis; cleanup; simpl in *.
    repeat split_ors; cleanup; eauto.
    eapply IHl; eauto.
Qed.

Lemma remove_NoDup : forall A B (AEQ: EqDec A) (l: list (A * B)) a,
NoDup (map fst l) -> NoDup (map fst (remove_fst l a)).
Proof.
    induction l; simpl; intros; cleanup.
    econstructor; eauto.
    case_analysis; cleanup; simpl; eauto;
    econstructor; eauto.
    eapply remove_not_In; eauto.
Qed.


Lemma remove_In_neq : forall A B (AEQ: EqDec A) (l: list (A * B)) ab a,
fst ab <> a ->  
In ab (remove_fst l a) <-> In ab l.
Proof.
    induction l; unfold not; simpl; intros; cleanup; eauto.
    split; intros; cleanup.
    
    case_analysis; cleanup; simpl in *;
    repeat split_ors; cleanup; eauto.

    split; intros; cleanup; eauto;
    split_ors; cleanup; eauto;
    exfalso; eauto.

    split; intros; cleanup;
    split_ors; cleanup; eauto.
    apply IHl in H0;
    edestruct IHl; eauto.
    edestruct IHl.
    2: right; apply H2; eauto.
    eauto.
Qed.

Program Definition delete (m: finite_map) k : finite_map :=
{| m:= (fun k' => if KEQ k k' then None else m k'); 
    elems:= (remove_fst m.(elems) k);
    specs := _ |}.
Next Obligation.
    destruct m0.(specs).
    split.
    apply remove_NoDup; eauto.
    intros.
    case_analysis; cleanup; eauto.
    split; intros; cleanup; eauto.
    exfalso; eapply remove_not_In_2; eauto.
    apply in_map_iff; exists (k0,v); intuition eauto.
    split; intros.
    apply remove_In_neq in H1; simpl; eauto.
    apply H0; eauto.
    apply remove_In_neq; simpl; eauto.
    apply H0; eauto.
Qed.

Program Definition empty_fmap : finite_map :=
{| m:= (fun _ => None);
    elems:= nil;
    specs := _ |}.
Next Obligation.
    intuition eauto.
    econstructor.
    inversion H.
Qed.

Definition disjoint (m m': finite_map) : Prop :=
(forall k, (m k <> None -> m' k = None) /\ (m' k <> None -> m k = None)).

Program Definition merge (m1 m2: finite_map) : finite_map :=
{| m:= (fun k => match m1 k with | Some v => Some v | None => m2 k end); 
    elems:= (nodup_by_fst KEQ (m2.(elems)++m1.(elems)));
    specs := _ |}.
Next Obligation.
    destruct m1.(specs).
    destruct m2.(specs).
    split.
    eapply NoDup_map_fst_nodup_by_fst.
    intros.
    split; intros.
    {
        case_analysis.
        apply H0 in HD.
        eapply_fresh nodup_by_fst_In_r in HD; eauto.
        eapply NoDup_In_inj in HD; eauto; cleanup; eauto.

        eapply nodup_by_fst_In_app in H3.
        split_ors; eauto.
        apply H2; eauto.
        apply H0 in H3; congruence.
    }
    {
        case_analysis; cleanup; eauto.
        apply H0 in HD.
        eapply_fresh In_NoDup_nodup_by_fst_r in HD; eauto.
        apply H2 in H3.
        eapply_fresh In_NoDup_nodup_by_fst_l in H3; eauto.
        simpl; intros Hnot.
        apply in_map_iff in Hnot; cleanup; eauto.
        destruct x; apply H0 in H5; simpl in *; congruence.
    }
Qed.

Program Definition map_f (f: key -> value -> value) (m1: finite_map) : finite_map :=
{| m:= (fun k => match m1 k with | Some v => Some (f k v) | None => None end); 
    elems:= map (fun kv => (fst kv, f (fst kv) (snd kv))) m1.(elems);
    specs := _ |}.
Next Obligation.
    destruct m1.(specs).
    split.
    rewrite map_map; simpl; eauto.
    intros.
    split; intros.
    {
        apply in_map_iff in H1; cleanup.
        destruct x; apply H0 in H2; simpl in *; cleanup; eauto.
    }
    {
        case_analysis; cleanup.
        apply H0 in HD.
        apply in_map_iff; eexists; split; eauto.
        simpl; eauto.
    }
Qed.
 
Definition pairwise_disjoint (lm: list finite_map) : Prop :=
forall i j m m', i <> j ->
nth_error lm i  = Some m -> 
nth_error lm j = Some m' -> 
(forall k, (m k <> None -> m' k = None) /\ (m' k <> None -> m k = None)).

Definition covers (m: finite_map) (lm: list finite_map): Prop :=
forall k v, m k = Some v <-> (exists m', In m' lm /\ m' k = Some v).

Definition partition (m: finite_map) (lm: list finite_map): Prop :=
covers m lm /\ pairwise_disjoint lm.

Definition included (m1 m2: finite_map) : Prop :=
forall k v, m1 k = Some v -> m2 k = Some v.

Definition equivalent (m1 m2: finite_map) :=
included m1 m2 /\ included m2 m1.

Lemma equivalent_refl :
    forall (m: finite_map),
    equivalent m m.
Proof.
    unfold equivalent, included; simpl;
    intuition; repeat case_analysis; eauto.
Qed.

Lemma equivalent_sym :
    forall (m1 m2: finite_map),
    equivalent m1 m2 ->
    equivalent m2 m1.
Proof.
    unfold equivalent, included; simpl;
    intuition; repeat case_analysis; eauto.
Qed.

Lemma equivalent_trans :
    forall (m1 m2 m3: finite_map),
    equivalent m1 m2 ->
    equivalent m2 m3 -> 
    equivalent m1 m3.
Proof.
    unfold equivalent, included; simpl;
    intuition; repeat case_analysis; eauto.
Qed.

Lemma insert_delete_comm :
    forall m k1 k2 v,
    k1 <> k2 ->
    equivalent (insert (delete m k1) k2 v) (delete (insert m k2 v) k1).
Proof.
    unfold equivalent, included; simpl;
    intuition; repeat case_analysis; eauto.
Qed.

Lemma insert_insert_comm :
    forall m k1 k2 v1 v2,
    k1 <> k2 ->
    equivalent (insert (insert m k1 v1) k2 v2) (insert (insert m k2 v2) k1 v1).
Proof.
    unfold equivalent, included; simpl;
    intuition; repeat case_analysis; eauto.
Qed.

Lemma delete_insert_noop :
    forall (m: finite_map) k v,
    m k = None ->
    equivalent (delete (insert m k v) k) m.
Proof.
    unfold equivalent, included; simpl;
    intuition; repeat case_analysis; try cleanup; try congruence; eauto.
Qed.

Lemma insert_insert_noop :
    forall (m: finite_map) k v v',
    equivalent (insert (insert m k v') k v) (insert m k v).
Proof.
    unfold equivalent, included; simpl;
    intuition; repeat case_analysis; try cleanup; try congruence; eauto.
Qed.

Lemma equivalent_Permutation:
forall (m1 m2: finite_map),
equivalent m1 m2 ->
Permutation.Permutation (elems m1) (elems m2).
Proof. 
    intros.
    apply Permutation.NoDup_Permutation.
    eapply NoDup_map_inv, specs.
    eapply NoDup_map_inv, specs.
    unfold equivalent, included in *.
    intuition; eapply specs; eapply specs in H;
    eauto.
Qed.


Lemma insert_eq :
forall (m: finite_map) k v,
insert m k v k = Some v.
Proof.
    simpl; intros; case_analysis.
Qed.

Lemma insert_neq :
forall (m: finite_map) k k' v,
k <> k' ->
insert m k v k' = m k'.
Proof. 
    simpl; intros; case_analysis.
Qed.


Lemma delete_eq:
forall (m: finite_map) k,
delete m k k = None.
Proof.
    simpl; intros; case_analysis.
Qed.

Lemma delete_neq:
forall (m: finite_map) k k',
k <> k' ->
delete m k k' = m k'.
Proof.
    simpl; intros; case_analysis.
Qed.

Lemma delete_Some:
forall (m: finite_map) k k' v,
delete m k k' = Some v ->
k <> k' /\ m k' = Some v.
Proof.
    simpl; intros; case_analysis; eauto.
Qed.

Lemma delete_None:
forall (m: finite_map) k k',
delete m k k' = None ->
k = k' \/ (k <> k' /\ m k' = None).
Proof.
    simpl; intros; case_analysis; eauto.
Qed.

Lemma insert_Some:
forall (m: finite_map) k k' v' v,
insert m k v k' = Some v' ->
(k = k' /\ v = v') \/ (k <> k' /\ m k' = Some v').
Proof.
    simpl; intros; case_analysis; eauto.
    inversion H; subst; eauto.
Qed.

Lemma insert_None:
forall (m: finite_map) k k' v,
insert m k v k' = None ->
k <> k' /\ m k' = None.
Proof.
    simpl; intros; case_analysis; eauto.
Qed.

Lemma insert_insert_noop_2: 
forall (m : finite_map) k k1 v v' v1,
equivalent (insert (insert (insert m k v') k1 v1) k v)
(insert (insert m k1 v1) k v).
Proof.
    intros; unfold equivalent, FMap.included.
    intuition eauto; simpl in *; repeat case_analysis;
    cleanup; eauto.
Qed.

Lemma insert_insert_noop_3:
forall (m : finite_map) k k1 k2 v v' v1 v2,
equivalent (insert (insert (insert (insert m k v') k2 v2) k1 v1) k v)
(insert (insert (insert m k2 v2) k1 v1) k v).
Proof.
    intros; unfold equivalent, FMap.included.
    intuition eauto; simpl in *; repeat case_analysis;
    cleanup; eauto.
Qed.

Lemma insert_insert_noop_4:
forall (m : finite_map) k k1 k2 k3 v v' v1 v2 v3,
equivalent (insert (insert (insert (insert (insert m k v') k3 v3) k2 v2) k1 v1) k v)
(insert (insert (insert (insert m k3 v3) k2 v2) k1 v1) k v).
Proof.
    intros; unfold equivalent, FMap.included.
    intuition eauto; simpl in *; repeat case_analysis;
    cleanup; eauto.
Qed.

Lemma insert_insert_noop_5:
forall (m : finite_map) k k1 k2 k3 k4 v v' v1 v2 v3 v4,
equivalent (insert (insert (insert (insert (insert (insert m k v') k4 v4) k3 v3) k2 v2) k1 v1) k v)
(insert (insert (insert (insert (insert m k4 v4) k3 v3) k2 v2) k1 v1) k v).
Proof.
    intros; unfold equivalent, FMap.included.
    intuition eauto; simpl in *; repeat case_analysis;
    cleanup; eauto.
Qed.

Lemma delete_delete_comm :
    forall (m: finite_map) k k1 k2,
    (delete (delete m k1) k2) k = (delete (delete m k2) k1) k.
Proof.
  intros. unfold delete. simpl.
  repeat case_analysis; eauto.
Qed.

End FMap.

Arguments insert {key KEQ value}%_type_scope.
Arguments delete {key KEQ value}%_type_scope.
Arguments merge {key KEQ value}%_type_scope.
Arguments map_f {key value}%_type_scope.
Arguments included {key value}%_type_scope.
Arguments disjoint {key value}%_type_scope.
Arguments empty_fmap {key value}%_type_scope.
Arguments equivalent {key value}%_type_scope.


