Require Import Arith Nat Bool.
Require Import List.
Import ListNotations.

Record coord := mkCoord { x : nat; y : nat }.
Definition eq_coord (c1 c2 : coord) := (c1.(x) =? c2.(x)) && (c1.(y) =? c2.(y)).

Infix "==" := eq_coord (at level 39, no associativity).


(* Lemma eq_dec : forall y:A, x = y \/ x <> y. *)

Definition plateau := list coord.

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

Lemma eq_coord_eq (c1 c2 : coord) : c1 == c2 = true -> c1 = c2.
Admitted.
(* Proof.
  induction c1.
  induction c2.
  unfold "==".
  intro.
   *)

(* Lemma eqeq_refl (c1 c2 : coord) : c1 == c2 -> c2 == c1. *)
Lemma ncolor_neq (c1 c2 : coord) : case_noire c1 -> case_blanche c2 -> c1 == c2 = false.
Proof.
  intros.
  unfold "==".
Admitted.


Lemma eq_coord_color (c1 c2 : coord) :
  c1 == c2 = true ->
  (case_blanche c1 <-> case_blanche c2) /\ (case_noire c1 <-> case_noire c2).
Proof.
  intro.
  apply (eq_coord_eq c1 c2) in H.
  rewrite H.
  split; split; trivial.
Qed.

Fixpoint card_bl (p : plateau) :=
  match p with
  | [] => 0
  | c :: t =>
      if even (c.(x) + c.(y))
      then 1 + card_bl t
      else card_bl t
  end.

Fixpoint card_no (p : plateau) :=
  match p with
  | [] => 0
  | c :: t =>
      if odd (c.(x) + c.(y))
      then 1 + card_no t
      else card_no t
  end.

Lemma bl_or_no : forall c: coord, case_blanche c \/ case_noire c.
Proof.
  intro.
  eapply Nat.Even_or_Odd.
Qed.

Lemma bl_no : forall c: coord, case_blanche c -> ~ (case_noire c).
Proof.
  intros c H1 H2.
  unfold case_blanche in H1.
  unfold case_noire in H2.
  apply (Nat.Even_Odd_False (x c + y c)); assumption.
Qed.

(* Lemma bl_or_no2 (c : coord): case_blanche c \/ case_noire c. Proof. eapply Nat.Even_or_Odd. Qed. *)

Lemma even_xor_odd (n : nat) : Nat.Even n -> ~ (Nat.Odd n).
Proof.
  intros H H1.
  apply Nat.Even_Odd_False with n; assumption.
Qed.

Lemma even_to_not_odd (n:nat) : Nat.even n = true -> Nat.odd n = false.
Proof.
  rewrite <- Nat.negb_odd.
  intro.
  rewrite negb_true_iff in H.
  assumption.
Qed.

Lemma odd_to_not_even (n:nat) : Nat.odd n = true <-> Nat.even n = false.
Proof.
  split.
  - rewrite <- Nat.negb_odd.
    intro.
    rewrite negb_false_iff.
    assumption.
  - intro.
    unfold Nat.odd .
    rewrite negb_true_iff.
    assumption.
Qed.

Lemma sum_card_bl_no : forall p : plateau, card_bl p + card_no p = List.length p.
Proof.
  induction p.
  { simpl. reflexivity. }
  { simpl.
    destruct (bl_or_no a).
    + unfold case_blanche in H.
      rewrite <- Nat.even_spec in H.
      rewrite H.
      apply even_to_not_odd in H.
      rewrite H.
      simpl.
      apply Nat.succ_inj_wd.
      assumption.
    + unfold case_noire in H.
      rewrite <- Nat.odd_spec in H.
      rewrite H.
      apply odd_to_not_even in H.
      rewrite H.
      rewrite Nat.add_comm.
      simpl.
      apply Nat.succ_inj_wd.
      rewrite Nat.add_comm.
      assumption.
  }
Qed.

(* Definition inf8 := forall n m : nat, n < 8 /\ m < 8. *)

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

Fixpoint mk_plateau (n:nat) :=
  match n with
  | 0 => []
  | S n =>
      (mk_line 8 n) ++ (mk_plateau n)
  end.


Definition plateau8 : plateau := mk_plateau 8.

Eval compute in mk_plateau 8.

Check List.filter.

Print Bool.

Definition neq07 (e:coord) : bool :=
    e == {| x := 0; y := 0 |} ||
    e == {| x := 7; y := 7 |}.

Fixpoint mem {A : Set} (eq : A -> A -> bool) (e : A) (l : list A) : bool :=
  match l with
  | [] => false
  | h::t => if eq h e then true else mem eq e t
  end.

Fixpoint retire (p:plateau) (e:coord) :=
  match p with
  | [] => []
  | h::t => if eq_coord h e then t else h :: retire t e
  end.

Infix "\" := retire (at level 31, left associativity).

(* Definition plateau_sc :=
  List.filter (fun e => negb (neq07 e)) plateau8. *)
Definition plateau_sc := plateau8 \ {| x := 7; y := 7|} \ {| x := 0; y := 0|}.

Eval compute in plateau_sc.

  (* List.filter (fun e => negb (neq07 e)) plateau8. *)
(*
   Eval compute in mem eq_coord {| x := 0; y := 0 |} plateau8.   (* true *)
   Eval compute in mem eq_coord {| x := 0; y := 0 |} plateau_sc. (* false *)
 *)

Definition pose_domino (d:domino) (p:plateau) : plateau :=
  match d with
  | Hauteur c =>
      p \ c \ (case_prise d)
  | Largeur c =>
      p \ c \ (case_prise d)
  end.

Definition mk_domino_H (x y : nat) := Hauteur {| x := x ; y := y |}.
Definition mk_domino_L (x y : nat) := Largeur {| x := x ; y := y |}.

Eval compute in plateau_sc.
Eval compute in pose_domino (mk_domino_H 4 4) plateau_sc.


Lemma desous_bn (c : coord) : case_blanche c -> case_noire (dessous c).
Admitted.
Lemma droite_bn (c : coord) : case_blanche c -> case_noire (droite c).
Admitted.

Lemma desous_nb (c : coord) : case_noire c -> case_blanche (dessous c).
Admitted.
Lemma droite_nb (c : coord) : case_noire c -> case_blanche (droite c).
Admitted.


Ltac casse_if h :=
  unfold case_blanche in h;
  rewrite <- Nat.even_spec in h;
  rewrite h.

Lemma rew_cons_card (a : coord) (p: plateau) :
  case_blanche a ->
  card_bl (a :: p) = S (card_bl p).
Proof.
  induction p; simpl; intro; casse_if H; trivial.
Qed.

Lemma remove_bad_color (a : coord) (p: plateau) :
  case_noire a ->
  card_bl (a :: p) = card_bl p.
Proof.
Admitted.

Lemma rew_remove_card (a : coord) (p: plateau) :
  case_blanche a ->
  card_bl (p \ a) = card_bl p - 1.
Proof.
  induction p.
  - simpl. trivial.
  - intro.
Admitted.

Lemma rw_util (a c : coord) (p : plateau) : (a == c) = false -> card_bl (a :: (p \ c)) = card_bl ((a :: p) \ c).
Proof.
Admitted.
(* Proof.
  intro.
  unfold card_bl. *)

Require Import Lia.
Lemma aux_pred_succ (n : nat) : n > 0 -> n - 1 + 1 = n.
Proof.
  lia.
Qed.

Lemma retire_case_bl (p:plateau) (c:coord) : case_blanche c -> 0 < card_bl p -> card_bl (p \ c) + 1 = card_bl p.
Proof.
  induction p.
  { intros. simpl in *. apply Nat.lt_neq in H0. contradiction. }
  { intros.
    destruct (bl_or_no a); simpl in *.
    + unfold case_blanche in H1.
      rewrite <- Nat.even_spec in H1.
      rewrite H1.
      rewrite Nat.add_1_r.
      apply Nat.succ_inj_wd.
      assert ((a == c) = true \/ (a == c) = false).
      - left.
      - destruct H2; rewrite H2.
        * reflexivity.
        * rewrite Nat.even_spec in H1.
          rewrite (rw_util a c p H2).
          rewrite (rew_remove_card c (a::p) H).
          rewrite (rew_cons_card a p H1).
          simpl.
          apply Nat.sub_0_r.
    + unfold case_noire in H1.
      rewrite <- Nat.odd_spec in H1.
      apply odd_to_not_even in H1.
      rewrite H1.
      assert ((a == c) = false).
      - eapply ncolor_neq.
        * unfold case_noire.
          rewrite <- Nat.odd_spec.
          apply odd_to_not_even.
          assumption.
        * assumption.
      - rewrite H2.
        rewrite (rw_util a c p H2).
        rewrite (rew_remove_card c (a::p) H).
        apply odd_to_not_even in H1.
        rewrite (remove_bad_color a p).
        ++ apply aux_pred_succ.
           apply odd_to_not_even in H1.
           rewrite H1 in H0.
           assumption.
        ++ unfold case_noire.
          rewrite <- Nat.odd_spec.
          assumption.
  }
Qed.

Lemma invariant : forall p p': plateau, forall d: domino,
  p' = pose_domino d p ->
  card_bl p = card_bl p' + 1 /\
  card_no p = card_no p' + 1.
Proof.
  intros.
  split.
  {
    destruct d; simpl in *.
    {
      destruct (bl_or_no c).
      + rewrite H.

      (* si c blanc alors dessous c = noir *)

  }

  }
