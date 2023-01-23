Require Import Nat Arith List.
Import ListNotations.

(*****************************************************************************************)
(******************************** { Définitions de base } ********************************)
(*****************************************************************************************)

(** une case du plateau *)
Record coord := mkCoord { x : nat; y : nat }.

(** liste de cases *)
Definition plateau := list coord.

(** une case est soit blanche soit noire *)
Inductive couleur := Blanc | Noir.

(** négatif *)
Definition neg_couleur c :=
  match c with
  | Blanc => Noir
  | Noir => Blanc
  end.

(**
  un domino se pose peut être identifié par :
  - une case
  - le sens dans lequel il est posé
  exemple : Hauteur {0;0} occupe les cases {0;0} et {0;1}
 *)
Inductive domino :=
  | Hauteur : coord -> domino
  | Largeur : coord -> domino.

(** case a droite de [c] *)
Definition droite  (c : coord) := {| x := c.(x) + 1; y := c.(y) |}.

(** case en dessous de [c] *)
Definition dessous (c : coord) := {| x := c.(x)    ; y := c.(y) + 1 |}.

(** pair des cases occupées par un domino *)
Definition case_prise (d:domino) : coord * coord :=
  match d with
  | Hauteur c => (c, dessous c)
  | Largeur c => (c, droite c)
  end.

(** une case est blanche si la somme de ses coordonnées est paire *)
Definition case_blanche (c : coord) : Prop := Nat.Even (c.(x) + c.(y)).

(** une case est noire si la somme de ses coordonnées est paire *)
Definition case_noire (c : coord) : Prop := Nat.Odd (c.(x) + c.(y)).

(** condiction pour que la case [c] soit de couleur [cc] *)
Definition couleur_case (cc : couleur) (c : coord) : Prop :=
  match cc with
  | Blanc => Nat.Even (c.(x) + c.(y))
  | Noir  => Nat.Odd  (c.(x) + c.(y))
  end.

(** calcul le nombre de case de couleur [Blanc] sur un plateau [p] *)
Fixpoint card_bl (p : plateau) :=
  match p with
  | [] => 0
  | c :: t =>
      if even (c.(x) + c.(y))
      then 1 + card_bl t
      else card_bl t
  end.

(** calcul le nombre de case de couleur [Noir] sur un plateau [p] *)
Fixpoint card_no (p : plateau) :=
  match p with
  | [] => 0
  | c :: t =>
      if odd (c.(x) + c.(y))
      then 1 + card_no t
      else card_no t
  end.

(** calcul le nombre de case de couleur [c] sur un plateau [p] *)
Definition card (c : couleur) (p : plateau) :=
  match c with
  | Blanc => card_bl p
  | Noir  => card_no p
  end.

(** Fabrique une ligne d'un plateau
    exemple : mk_line n m = [ { 1; m } .. { n; m } ] *)
Fixpoint mk_line (n m:nat) : list coord :=
  match n with
  | 0 => []
  | S n => {| x := n; y := m |} :: (mk_line n m)
  end.

(** construction d'un plateau « classique »
    forme de carré [n] * [n]
    exemple :
     mk_plateau n := { {1; 1} ; ... ; {1; n} ; ... ; {n; 1} ; { n; n } } *)
Fixpoint mk_plateau (n:nat) :=
  match n with
  | 0 => []
  | S n =>
      (mk_line 8 n) ++ (mk_plateau n)
  end.


(** Plateau du problème original est un plateau d'échecs donc : 8x8 *)
Definition plateau_base : plateau := mk_plateau 8.

(* Eval compute in mk_plateau 8. *)

(** l'égalité entre coordonnées est décidable *)
Lemma eq_coord : forall a b : coord, {a = b} + {a <> b}.
Proof.
  decide equality; decide equality.
Defined.

Lemma eq_rw {P}:
  forall a (x y : P), (if eq_coord a a then x else y) = x.
Proof.
  intros.
  case (eq_coord a a).
  intros.
  trivial.
  contradiction.
Qed.

Lemma eq_rw2 {P}:
  forall a b (x y : P), a <> b -> (if eq_coord a b then x else y) = y.
Proof.
  intros.
  case (eq_coord a b).
  - contradiction.
  - intro. trivial.
Qed.

(** l'égalité entre dominos est décidable *)
Lemma eq_domino : forall a b : domino, {a = b} + {a <> b}.
Proof.
  intros.
  destruct a, b.
  - case (eq_coord c c0); intro e.
    + rewrite e. left. trivial.
    + decide equality; apply eq_coord.
  - right. intro. discriminate.
  - right. intro. discriminate.
  - case (eq_coord c c0); intro e.
    + rewrite e. left. trivial.
    + decide equality; apply eq_coord.
Defined.

(** notation à la \setminus *)
Infix "\" := (fun a b => List.remove eq_coord b a) (at level 31, left associativity).

(** Plateau du problème : échiquier classique sans 1 pair de coins opposés *)
Definition plateau_coupe := plateau_base \ {| x := 7; y := 7|} \ {| x := 0; y := 0|}.

(* Eval compute in plateau_coupe. *)

(** poser un domino [d] :
      retirer les deux cases prisent par [d] dans la liste des cases du plateau *)
Definition pose_domino (d : domino) (p : plateau) : plateau :=
  p \ fst (case_prise d) \ snd (case_prise d).

(** itérations consécutives de la fonction précédante *)
Definition pose_dominos (dl : list domino) (p_init : plateau) : plateau :=
  fold_left (fun (p : plateau) (d : domino) => pose_domino d p) dl p_init.

(** hyp : si l'on a un [p'] tq [p' = pose_domino d p]
          alors c'est que les cases prisent par le domino
          étaient présentes dans [p] *)

Hypothesis rm_iff_mem : forall p p' d, p' = pose_domino d p ->
  (In (fst (case_prise d)) p /\ In (snd (case_prise d)) p).

Hypothesis rm_iff_mem2 : forall p p' c, p' = p \ c -> In c p.
(* Proof.
  intros p p' d.
  destruct d; unfold pose_domino; simpl; intro.
  revert p p'.
  -
  simpl.
  intros. *)


Definition mk_domino_H (x y : nat) := Hauteur {| x := x ; y := y |}.
Definition mk_domino_L (x y : nat) := Largeur {| x := x ; y := y |}.

(* Eval compute in pose_domino (mk_domino_H 4 4) plateau_coupe. *)
