Require Import Domino List.
Import ListNotations.

Definition disjoints_dominos (d1 d2:domino) :=
  match d1, d2 with
  | Hauteur c1, Hauteur c2 =>
              c1 <> c2 /\
      dessous c1 <> c2 /\
              c1 <> dessous c2 /\
      dessous c1 <> dessous c2
  | Largeur c1, Largeur c2 =>
              c1 <> c2 /\
       droite c1 <> c2 /\
              c1 <> droite c2 /\
       droite c1 <> droite c2
  | Hauteur c1, Largeur c2
  | Largeur c2, Hauteur c1 =>
              c1 <> c2 /\
              c1 <> droite c2 /\
      dessous c1 <> c2 /\
      dessous c1 <> droite c2
  end.

Infix "#" := (fun a b => disjoints_dominos a b) (at level 32, left associativity).

(** déduction de la commutativité de [pose_domino] *)
Fixpoint disjoints_dominos_l (d : domino) (dl : list domino) :=
  match dl with
  | [] => True
  | h :: t => disjoints_dominos d h /\ disjoints_dominos_l d t
  end.

Infix "##" := (fun a b => disjoints_dominos_l a b) (at level 33, left associativity).

Fixpoint disjoints_dominos_lo_aux (d : domino) (dl : list domino) :=
  match dl with
  | [] => True
  | h::t => (d # h /\ disjoints_dominos_lo_aux d t)
  end.

Fixpoint disjoints_dominos_lo (dl : list domino) :=
  match dl with
  | [] => True
  | h::t => disjoints_dominos_lo_aux h t /\ disjoints_dominos_lo t
  end.

(*****************************************************************************************)
(****************************** { Lemmes sur "disjoints" } *******************************)
(*****************************************************************************************)

Lemma simp_disjlo0 : disjoints_dominos_lo [].
Proof.
  unfold disjoints_dominos_lo.
  simpl.
  auto.
Qed.

Hint Resolve simp_disjlo0.

Lemma simp_disjlo0b : forall d, disjoints_dominos_l d [].
Proof.
  simpl.
  auto.
Qed.

Hint Resolve simp_disjlo0b.

Lemma rw_util_disj : forall a d, disjoints_dominos_l d [a] <-> disjoints_dominos d a.
Proof.
  split.
  - intros H.
    case d, a;
    unfold disjoints_dominos_l, disjoints_dominos in *;
    split;
    try (destruct H;
      destruct H;
      assumption).
  - intros H.
    case d, a;
    unfold disjoints_dominos_l, disjoints_dominos in *;
    split; try assumption; trivial.
Qed.

Hint Resolve simp_disjlo0b.

Lemma simp_disjlo1 :
  forall d dl,
  disjoints_dominos_lo (d :: dl) ->
  disjoints_dominos_lo dl.
Proof.
  intros d dl.
  revert d.
  induction dl.
  - intros. apply simp_disjlo0.
  - intros d H.
    unfold disjoints_dominos_lo in H.
    unfold disjoints_dominos_lo.
    destruct H.
    destruct H0.
    split.
    + assumption.
    + assumption.
Qed.

Hint Resolve simp_disjlo1.

Lemma simp_disjlo2 :
  forall d dl,
  disjoints_dominos_lo (d :: dl) ->
  disjoints_dominos_l d dl.
Proof.
  intros d dl H.
  destruct dl.
  { auto. }
  { destruct H.
    split;
    unfold disjoints_dominos_lo_aux in H;
    destruct H;
    assumption. }
Qed.

Hint Resolve simp_disjlo2.
