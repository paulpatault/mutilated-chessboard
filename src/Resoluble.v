Require Import Domino Disjoint WF.
Require Import Arith Nat List Lia.
Import ListNotations.

(*****************************************************************************************)
(***************************** { Critère de résolubilité  } ******************************)
(*****************************************************************************************)

(** une liste de dominos « résout » un plateau si une fois que l'on les a tous posé,
    la liste représentant le plateau est vide *)
Definition solution (p : plateau) (dl : list domino) :=
  pose_dominos dl p = [].

(** un définition possible de la résolubilité d'un plateau
    un plateau est résoluble s'il existe un liste de domino
    telle que lorsque les domino seront posés le plateau sera vide *)
Definition resoluble (p : plateau) :=
  well_formed p /\
  exists dl : list domino, solution p dl /\ disjoints_dominos dl.
