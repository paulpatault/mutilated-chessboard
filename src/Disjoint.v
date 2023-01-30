Require Import Domino List.
Import ListNotations.

Create HintDb disjoints_hints.

(** des dominos sont « disjoints » s'ils ne recouvrent pas de case en commun *)
Definition disjoints2_dominos (d1 d2:domino) :=
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

Infix "#" := (fun a b => disjoints2_dominos a b) (at level 32, left associativity).

(** déduction de la commutativité de [pose_domino] *)
Fixpoint disjoints_dominos_l (d : domino) (dl : list domino) :=
  match dl with
  | [] => True
  | h :: t => disjoints2_dominos d h /\ disjoints_dominos_l d t
  end.

Infix "##" := (fun a b => disjoints_dominos_l a b) (at level 33, left associativity).

Fixpoint disjoints_dominos_lo_aux (d : domino) (dl : list domino) :=
  match dl with
  | [] => True
  | h::t => (d # h /\ disjoints_dominos_lo_aux d t)
  end.

Fixpoint disjoints_dominos (dl : list domino) :=
  match dl with
  | [] => True
  | h::t => disjoints_dominos_lo_aux h t /\ disjoints_dominos t
  end.

(*****************************************************************************************)
(****************************** { Lemmes sur "disjoints" } *******************************)
(*****************************************************************************************)

Lemma simp_disjlo0 : disjoints_dominos [].
Proof.
  unfold disjoints_dominos.
  simpl.
  auto.
Qed.

#[local]
Hint Resolve simp_disjlo0 : disjoints_hints.

Lemma simp_disjlo0b : forall d, d ## [].
Proof.
  simpl.
  auto.
Qed.

#[local]
Hint Resolve simp_disjlo0b : disjoints_hints.

Lemma rw_util_disj : forall a d, d ## [a] <-> d # a.
Proof.
  split.
  - intros H.
    case d, a;
    split;
    try
     (destruct H;
      destruct H;
      assumption).
  - intros H.
    case d, a;
    cbv;
    auto.
Qed.

#[local]
Hint Resolve simp_disjlo0b : disjoints_hints.

Lemma simp_disjlo1 :
  forall d dl,
  disjoints_dominos (d :: dl) ->
  disjoints_dominos dl.
Proof.
  intros d dl.
  revert d.
  induction dl.
  - intros. apply simp_disjlo0.
  - intros d H.
    unfold disjoints_dominos in H.
    unfold disjoints_dominos.
    destruct H.
    destruct H0.
    split; assumption.
Qed.

#[local]
Hint Resolve simp_disjlo1 : disjoints_hints.

Lemma simp_disjlo2 :
  forall d dl,
  disjoints_dominos (d :: dl) ->
  d ## dl.
Proof.
  intros d dl H.
  destruct dl.
  { auto with disjoints_hints. }
  { destruct H.
    split;
    unfold disjoints_dominos_lo_aux in H;
    destruct H;
    assumption. }
Qed.

#[local]
Hint Resolve simp_disjlo2 : disjoints_hints.
