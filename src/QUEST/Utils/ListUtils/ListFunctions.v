Require Import Lia PeanoNat ZArith SetoidList Permutation List.
Import ListNotations.
Import Permutation.

Set Implicit Arguments.
Set Maximal Implicit Insertion.

Class EqDec (T : Type) := eq_dec : forall (a b : T), {a = b} + {a <> b}.

Fixpoint bimap {A B C} (f: A -> B -> C) (la: list A) (lb: list B): list C :=
  match la, lb with
  | a::la, b::lb => (f a b)::(bimap f la lb)
  | _, _ => nil
  end.

Fixpoint repeat_map {A B} (f: A -> list B -> list B) (la: list A) (lb: list B): list B :=
  match la with
  | a::la => (repeat_map f la (f a lb))
  | _ => lb
  end.

Fixpoint seln (V : Type) (vs : list V) (n : nat) (default : V) : V :=
  match vs with
    | nil => default
    | v :: vs' =>
      match n with
        | O => v
        | S n' => seln vs' n' default
      end
  end.

Fixpoint updn T (vs : list T) (n : nat) (v : T) : list T :=
  match vs with
    | nil => nil
    | v' :: vs' =>
      match n with
        | O => v :: vs'
        | S n' => v' :: updn vs' n' v
      end
  end.

 Fixpoint indexed_map_shifted {A B} n (f: nat -> A -> B) (l: list A) :=
   match l with
   | nil => nil
   | a :: l' =>
     f n a :: indexed_map_shifted (S n) f l'
   end.

(** prevent eauto from unifying length ?a = length ?b *)
Definition eqlen A B (a : list A) (b : list B) := length a = length b.

Definition removen {V} (l : list V) i :=
   (firstn i l) ++ (skipn (S i) l).


Fixpoint nodup_by_list {A B} AEQ (la: list A) (lb: list B) :=
  match la, lb with
  | a :: la' , b :: lb' =>
    if In_dec AEQ a la' then
      nodup_by_list AEQ la' lb'
    else
      b :: nodup_by_list AEQ la' lb'
  | _, _ => nil
  end.

Fixpoint nodup_by_fst {A B} AEQ (l: list (A * B)) :=
  match l with
  | ab :: l' =>
    if In_dec AEQ (fst ab) (map fst l') then
      nodup_by_fst AEQ l'
    else
      ab :: nodup_by_fst AEQ l'
  | nil => nil
  end.

Definition setlen A l n (def : A) :=
  firstn n l ++ (repeat def (n - length l)).

Definition cuttail A n (l : list A) := firstn (length l - n) l.

Definition upd_range' T l start len (v : T) :=
  firstn start l ++ repeat v len ++ skipn (start + len) l.

Definition enumerate A (l : list A) := combine (seq 0 (length l)) l.

Definition part {T} (l : list T) (k : nat) :=
  map (fun i => firstn k (skipn (i * k) l)) (seq 0 (length l / k)).

Definition seln_each {T} (l : list (list T)) n (def : T) : list T :=
  map (fun l => seln l n def) l.

Definition inb {T} {E: EqDec T} (l : list T) (x : T) :=
if in_dec E x l then true else false.

Definition NoDup_dec {T} {TEQ: EqDec T}: forall (l: list T), {NoDup l}+{~NoDup l}.
  induction l; simpl; intuition.
  left; constructor.
  destruct (in_dec TEQ a l).
  right; intuition eauto.
  inversion H; eauto.
  left; constructor; eauto.
  right; intuition eauto.
  inversion H; eauto.
Defined.

Fixpoint upd_range {T} l start len (v : T) :=
  match len with
  | 0 => l
  | S len' => updn (upd_range l (S start) len' v) start v
  end.

Fixpoint upd_range_fast {T} vs start len (v : T) :=
  match vs with
  | nil => nil
  | v' :: vs' =>
    match start with
    | S start' => v' :: upd_range_fast vs' start' len v
    | O =>
      match len with
      | O => v' :: vs'
      | S len' => v :: upd_range_fast vs' O len' v
      end
    end
  end.

Fixpoint select U (P: U -> bool) (X: list U) : option U * list U :=
  match X with
  | nil => (None, X)
  | h::t =>
      if P h then
          (Some h, t)
      else
          let (r, Y) := select P t in (r, h::Y)
  end.
  
Fixpoint find_pair {U V} (P: U -> V -> bool) (X: list U) (Y: list V): option (U * V) :=
  match X with
  | nil => None
  | x::t =>
      match find (P x) Y with
      | Some y  => Some (x, y)
      | None => find_pair P t Y
      end
  end.

Fixpoint countb U (P: U -> bool) (X: list U) : nat :=
  match X with
  | nil => 0
  | h::t =>
      if P h then
          S (countb P t)
      else
          countb P t
  end.

Fixpoint countb_pair {U V} (P: U -> V -> bool) (X: list U) (Y: list V): nat :=
match X with
| nil => 0
| x::t =>
    countb (P x) Y + countb_pair P t Y
end.

Fixpoint strip_option {A} (l: list (option A)) : option (list A) :=
match l with
| nil => Some nil
| a::tl =>
  match a, strip_option tl with
  | Some b, Some l' => Some (b::l')
  | _, _ => None
  end
end.

Definition list_deep_ind :=
fun (A : Type) (P : list A -> Prop) (Q: A -> Prop) (f : P [])
(f0 : forall (a : A) (l : list A), Q a -> P l -> P (a :: l)) =>
fix F (l : list A) : Forall Q l -> P l :=
match l as l0 return Forall Q l0 -> (P l0) with
| [] => fun _ => f
| y :: l0 => fun G => f0 y l0 (Forall_inv G) (F l0 (Forall_inv_tail G))
end.    

(* Removes the first element that satisfies b *)
Fixpoint removeb {A} (cond: A -> bool) (l: list A) : list A :=
match l with
|nil => nil
|a::tl => if cond a then tl else
    a::(removeb cond tl)
end.

Definition transpose {A} (lla: list (list A)) : option (list (list A)) :=
match hd_error lla with
| Some la =>
  let n_selectors := map (fun n => (fun l => nth_error l n)) (seq 0 (length la)) in
  strip_option (map (fun f => strip_option (map f lla)) n_selectors)
| None => None
end.