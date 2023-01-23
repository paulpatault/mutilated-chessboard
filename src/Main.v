Require Import Domino Disjoint Resoluble WF Lemmas.
Require Import Arith Nat List Lia.
Import ListNotations.

(*****************************************************************************************)
(********************************* { Classical board } ***********************************)
(*****************************************************************************************)

(** On remarque ici que le plateau non amputé a une solution *)

(** fonctions de liste *)
Fixpoint init_aux {A : Type} (i len : nat) (f : nat -> A) : list A :=
  match len with
  | 0 => []
  | S len =>
      (f i) :: init_aux (i+1) len f
  end.

Definition init {A : Type} (n : nat) (f : nat -> A) : list A :=
  init_aux 0 n f.

(** définition de la solution pour l'échiquier non mutilé *)
Definition sol_base :=
  List.concat
  (init 8 (fun j =>
  init 4 (fun i => mk_domino_H j (i*2)))).

(** la solution fonctionne bien
    → pas mal de calcul ici (8 secondes sur ma machine) *)
Theorem classic_board_resoluble : resoluble plateau_base.
Proof.
  unfold resoluble.
  split.
  { simpl.
    intuition. }
  { exists sol_base.
    split.
    - unfold solution.
      simpl.
      unfold pose_domino.
      simpl.
      trivial.
    - simpl. intuition; discriminate H. }
Qed.

(*****************************************************************************************)
(********************************* { Mutilated Board  } **********************************)
(*****************************************************************************************)

(** combinaison des deux lemmes importants que l'on vient de définir *)
Lemma invariant_extended_to_dominolist :
  forall p p' dl,
  well_formed p ->
  disjoints_dominos_lo dl ->
  pose_dominos dl p = p' ->
  card Blanc p = card Blanc p' + (List.length dl) /\
  card Noir p = card Noir p' + (List.length dl).
Proof.
  intros p p' dl wfp disj.
  destruct dl; intro H; symmetry in H.
  { rewrite H. simpl. lia. }
  {
    destruct d as [c|c];
    split;
    case (bl_or_no c);
    intro col;
    rewrite H;
    try (apply (rm_add_b p Blanc (Hauteur c :: dl)));
    try (apply (rm_add_b p Noir  (Hauteur c :: dl)));
    try (apply (rm_add_b p Blanc (Largeur c :: dl)));
    try (apply (rm_add_b p Noir  (Largeur c :: dl)));
    assumption.
  }
Qed.

(** si on peut résourde [p],
    alors [p] contient autant de cases noires de que cases blanches *)
Theorem resoluble_invariant : forall p, resoluble p -> card Noir p = card Blanc p.
Proof.
  intros p H.
  destruct H as (wf, (sol, H)).
  assert (H' := H).
  destruct H.
  unfold solution in H.
  induction sol; simpl in *.
  { rewrite H. simpl. reflexivity. }
  { apply invariant_extended_to_dominolist  in H.
    simpl in H.
    destruct H.
    rewrite <- H in H1.
    apply (pose_domino_dont_change_card a).
    assumption.
    assumption.
    apply simp_disjlo1 in H0.
    - apply (wf_minus_d p wf a).
    - destruct H0. assumption.
  }
Qed.

(** Le plateau amputé n'a pas de solution ! *)
Corollary mutilated_board : ~ resoluble plateau_coupe.
Proof.
  intro.
  apply resoluble_invariant in H.
  rewrite card_coupe in H.
  lia.
Qed.
