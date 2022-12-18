(* Require Import PeanoNat. Require Arith_base. *)

Require Import Arith Nat.

Inductive vect (A : Set) : nat -> Set :=
  | vnil : vect A 0
  | vcons : forall n : nat, A -> vect A n -> vect A (n+1).

Definition matrix (A : Set) (n m : nat) : Set := vect (vect A n) m.

Record coord := mkCoord { x : nat; y : nat }.

Inductive couleur := Blanc | Noir | Vide.

Definition plateau := matrix couleur 8 8.

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
