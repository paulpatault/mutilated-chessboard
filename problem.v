(* Require Import PeanoNat. Require Arith_base. *)

Require Import Arith Nat Bool.

(* Inductive vect (A : Set) : nat -> Set :=
  | vnil : vect A 0
  | vcons : forall n : nat, A -> vect A n -> vect A (n+1). *)

(* Definition matrix (A : Set) (n m : nat) : Set := vect (vect A n) m. *)

(* Definition mplateau := matrix couleur 8 8. *)

Record coord := mkCoord { x : nat; y : nat }.

Inductive couleur := Blanc | Noir | Vide.

Inductive domino :=
  | Hauteur : coord -> domino
  | Largeur : coord -> domino.

Definition droite  (c : coord) := {| x := c.(x) + 1; y := c.(y) |}.
Definition gauche  (c : coord) := {| x := c.(x) - 1; y := c.(y) |}.
Definition dessus  (c : coord) := {| x := c.(x)    ; y := c.(y) - 1 |}.
Definition dessous (c : coord) := {| x := c.(x)    ; y := c.(y) + 1 |}.

Definition case_prise : domino -> coord := fun d =>
  match d with
  | Hauteur c => dessous c
  | Largeur c => droite c
  end.

Definition case_blanche (c : coord) : Prop := Nat.Even (c.(x) + c.(y)).
Definition case_noire   (c : coord) : Prop := Nat.Odd  (c.(x) + c.(y)).

Definition inf8 := forall n m : nat, n < 8 /\ m < 8.

Require Import List.
Import ListNotations.

Require Import Lists.ListSet.

Definition mset := set coord.

Print ListSet.

Definition eq_coord (c1 c2 : coord) := (c1.(x) =? c2.(x)) && (c1.(y) =? c2.(y)).

Infix "==" := eq_coord (at level 39, no associativity).

(**
   ll n m = [ { 1; m } .. { n; m } ]
 *)
Fixpoint mk_line (n m:nat) : list coord :=
  match n with
  | 0 => []
  | S n => {| x := n; y := m |} :: (mk_line n m)
  end.

(**
   plateau n := { {1; 1} ; ... ; {1; n} ; ... ; {n; 1} ; { n; n } }
 *)

Fixpoint plateau (n:nat) :=
  match n with
  | 0 => []
  | S n =>
      (mk_line 8 n) ++ (plateau n)
  end.

Definition plateau8 : list coord := plateau 8.

Eval compute in plateau 8.

Check List.filter.

Print Bool.

Definition neq07 (e:coord) : bool :=
    e == {| x := 0; y := 0 |} ||
    e == {| x := 7; y := 7 |}.

Definition plateau_sc :=
  List.filter (fun e => negb (neq07 e)) plateau8.

Fixpoint mem {A : Set} (eq : A -> A -> bool) (e : A) (l : list A) : bool :=
  match l with
  | [] => false
  | h::t => if eq h e then true else mem eq e t
  end.

(*
   Eval compute in mem eq_coord {| x := 0; y := 0 |} plateau8.   (* true *)
   Eval compute in mem eq_coord {| x := 0; y := 0 |} plateau_sc. (* false *)
 *)


