(* Require Import PeanoNat. Require Arith_base. *)

Require Import Arith Nat.

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

Definition eq_dec (c1 c2 : coord) := c1.(x) = c2.(x) /\ c1.(y) = c2.(y).

Lemma eq_decl : forall n m : coord, {n = m} + {n <> m}.
Admitted.

Print eq_dec.

(**
   ll n m = { { 1; m } .. { n; m } }
 *)
Fixpoint ll (n m:nat) : mset :=
  match n with
  | 0 => empty_set coord
  | S n => set_add eq_decl {| x := n; y := m |} (ll n m)
  end.

(**
   plateau n := { {1; 1} ; ... ; {1; n} ; ... ; {n; 1} ; { n; n } }
 *)

Fixpoint plateau (n:nat) :=
  match n with
  | 0 => empty_set coord
  | S n =>
      set_union eq_decl (ll 8 n) (plateau n)
  end.

Definition plateau8 := plateau 8.

Definition plateau_sc :=
  let m00 := set_remove eq_decl ({| x := 0; y := 0 |}) plateau8 in
  set_remove eq_decl ({| x := 7; y := 7 |}) m00.

Eval compute in set_mem eq_decl ({| x := 0; y := 0 |}) plateau8.

(* TODO : changer la def de plateau : set -> matrix (= vect vect) ? *)
