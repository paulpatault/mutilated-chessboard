Require Import Arith Nat List Lia.
Import ListNotations.

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
 * un domino se pose peut être identifié par :
 * - une case
 * - le sens dans lequel il est posé
 * exemple : Hauteur {0;0} occupe les cases {0;0} et {0;1}
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
Definition est_blanche  (c : coord) : bool := even     (c.(x) + c.(y)).

(** une case est noire si la somme de ses coordonnées est paire *)
Definition case_noire (c : coord) : Prop := Nat.Odd (c.(x) + c.(y)).
Definition est_noire  (c : coord) : bool := odd     (c.(x) + c.(y)).

(** condiction pour que la case [c] soit de couleur [cc] *)
Definition couleur_case (cc : couleur) (c : coord) : Prop :=
  match cc with
  | Blanc => Nat.Even (c.(x) + c.(y))
  | Noir  => Nat.Odd  (c.(x) + c.(y))
  end.

(** étant donnée la case [c], celle en dessous de [c] a la couleur opposée *)
Lemma dessous_inv_col col c : couleur_case col c <-> couleur_case (neg_couleur col) (dessous c).
Proof.
  split.
  { case col; unfold couleur_case; intro; simpl; rewrite Nat.add_assoc; rewrite Nat.add_1_r.
    - apply Nat.odd_spec.
      rewrite Nat.odd_succ.
      apply Nat.even_spec.
      assumption.
    - apply Nat.even_spec.
      rewrite Nat.even_succ.
      apply Nat.odd_spec.
      assumption.
  }
  { case col; unfold couleur_case; intro; simpl in *; rewrite Nat.add_assoc in H; rewrite Nat.add_1_r in H.
    - apply Nat.odd_spec in H.
      rewrite Nat.odd_succ in H.
      apply Nat.even_spec.
      assumption.
    - apply Nat.even_spec in H.
      rewrite Nat.even_succ in H.
      apply Nat.odd_spec.
      assumption.
  }
Qed.

(** étant donnée la case [c], celle à droite de [c] a la couleur opposée *)
Lemma droite_inv_col col c : couleur_case col c -> couleur_case (neg_couleur col) (droite c).
Proof.
  case col; unfold couleur_case; intro; simpl.
  - rewrite <- Nat.add_assoc.
    rewrite Nat.add_comm.
    rewrite <- Nat.add_assoc.
    rewrite Nat.add_comm.
    apply Nat.odd_spec.
    rewrite Nat.add_1_r.
    rewrite Nat.odd_succ.
    apply Nat.even_spec.
    rewrite Nat.add_comm.
    assumption.
  - rewrite <- Nat.add_assoc.
    rewrite Nat.add_comm.
    rewrite <- Nat.add_assoc.
    rewrite Nat.add_comm.
    apply Nat.even_spec.
    rewrite Nat.add_1_r.
    rewrite Nat.even_succ.
    apply Nat.odd_spec.
    rewrite Nat.add_comm.
    assumption.
Qed.

(** les cases prisent par un domino sont exactement une case blanche et une case noire *)
Lemma domino_bicolor (d : domino) :
  (case_blanche (fst (case_prise d)) -> case_noire   (snd (case_prise d))) /\
  (case_noire   (fst (case_prise d)) -> case_blanche (snd (case_prise d))).
Proof.
  split; destruct d; unfold case_prise; simpl; intro. 
  - eapply (dessous_inv_col Blanc).
    unfold couleur_case.
    unfold case_blanche in H.
    assumption.
  - eapply (droite_inv_col Blanc).
    unfold couleur_case.
    unfold case_blanche in H.
    assumption.
  - eapply (dessous_inv_col Noir).
    unfold couleur_case.
    unfold case_noire in H.
    assumption.
  - eapply (droite_inv_col Noir).
    unfold couleur_case.
    unfold case_noire in H.
    assumption.
Qed.

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

(** la couleur d'une case est [Blanc] ou [Noir] *)
Lemma bl_or_no : forall c: coord, couleur_case Blanc c \/ couleur_case Noir c.
Proof.
  intro.
  eapply Nat.Even_or_Odd.
Qed.

(** une case [c] ne peut pas être de plusieurs couleurs *)
Lemma bl_no_false_g : forall c col, couleur_case col c -> couleur_case (neg_couleur col) c -> False.
Proof.
  intros c col H2 H3.
  destruct col;
   simpl in *;
    apply (Nat.Even_Odd_False (x c + y c)); assumption.
Qed.

(** si [c] est une case blanche alors [c] n'est pas une case noire *)
Lemma bl_no_false : forall c: coord, case_blanche c -> ~ (case_noire c).
Proof.
  intros c H1 H2.
  apply (Nat.Even_Odd_False (x c + y c)); assumption.
Qed.

(** si [n] est pair, alors [n] n'est pas impair (dans Prop) *)
Lemma even_xor_odd (n : nat) : Nat.Even n -> ~ (Nat.Odd n).
Proof.
  intros H H1.
  apply Nat.Even_Odd_False with n; assumption.
Qed.

(** si [n] est pair, alors [n] n'est pas impair (dans Bool) *)
Lemma even_to_not_odd (n:nat) : Nat.even n = true -> Nat.odd n = false.
Proof.
  rewrite <- Nat.negb_odd.
  intro.
  rewrite Bool.negb_true_iff in H.
  assumption.
Qed.

(** [n] est impair est équivalent à [n] n'est pas pair (dans Bool) *)
Lemma odd_to_not_even (n:nat) : Nat.odd n = true <-> Nat.even n = false.
Proof.
  split.
  - rewrite <- Nat.negb_odd.
    intro.
    rewrite Bool.negb_false_iff.
    assumption.
  - intro.
    unfold Nat.odd .
    rewrite Bool.negb_true_iff.
    assumption.
Qed.

(** factorisation de preuves *)
Ltac casse_if col h :=
  unfold card;
  match col with
  | Blanc =>
    unfold card_bl;
    unfold couleur_case in h;
    unfold case_blanche in h;
    try rewrite <- Nat.even_spec in h;
    try rewrite h;
    trivial
  | Noir =>
    unfold card_no;
    unfold couleur_case in h;
    unfold case_noire in h;
    try rewrite <- Nat.odd_spec in h;
    try rewrite h;
    trivial
  end.

(** la taille du plateau est égale
 *  à la somme du nombre de ses cases blanches
 *  et du nombre de ses cases noires *)
Lemma sum_card_bl_no : forall p : plateau, card_bl p + card_no p = List.length p.
Proof.
  induction p.
  { simpl. reflexivity. }
  { simpl.
    destruct (bl_or_no a).
    + casse_if Blanc H.
      apply even_to_not_odd in H.
      rewrite H.
      simpl.
      apply Nat.succ_inj_wd.
      assumption.
    + casse_if Noir H.
      apply odd_to_not_even in H.
      rewrite H.
      rewrite Nat.add_comm.
      simpl.
      apply Nat.succ_inj_wd.
      rewrite Nat.add_comm.
      assumption.
  }
Qed.

(**
 *  Fabrique une ligne d'un plateau
 *  exemple :
 *    mk_line n m = [ { 1; m } .. { n; m } ]
 *)
Fixpoint mk_line (n m:nat) : list coord :=
  match n with
  | 0 => []
  | S n => {| x := n; y := m |} :: (mk_line n m)
  end.

(**
 *  construction d'un plateau « classique »
 *  forme de carré [n] * [n]
 *  exemple :
 *    mk_plateau n := { {1; 1} ; ... ; {1; n} ; ... ; {n; 1} ; { n; n } }
 *)
Fixpoint mk_plateau (n:nat) :=
  match n with
  | 0 => []
  | S n =>
      (mk_line 8 n) ++ (mk_plateau n)
  end.


(** Plateau du problème original est un plateau d'échecs donc : 8x8 *)
Definition plateau_base : plateau := mk_plateau 8.

Eval compute in mk_plateau 8.

Lemma eq_coord : forall a b : coord, {a = b} + {a <> b}.
Proof.
  decide equality; decide equality.
Defined.

Infix "\" := (fun a b => List.remove eq_coord b a) (at level 31, left associativity).

(** Plateau du problème : échiquier classique sans 1 pair de coins opposés *)
Definition plateau_coupe := plateau_base \ {| x := 7; y := 7|} \ {| x := 0; y := 0|}.

Eval compute in plateau_coupe.

(*
   Eval compute in mem eq_coord {| x := 0; y := 0 |} plateau_base.   (* true *)
   Eval compute in mem eq_coord {| x := 0; y := 0 |} plateau_coupe. (* false *)
 *)

(** poser un domino [d] :
 *  retirer les deux cases prisent par [d] dans la liste des cases du plateau
 *)
Definition pose_domino (d : domino) (p : plateau) : plateau :=
  p \ fst (case_prise d) \ snd (case_prise d).

(** itérations consécutives de la fonction précédante *)
Definition pose_dominos (dl : list domino) (p_init : plateau) : plateau :=
  fold_left (fun (p : plateau) (d : domino) => pose_domino d p) dl p_init.

(** hyp : lorsque l'on écrit [pose_domino d p] on suppose toujours que [p] contient [case_prises d] *)
Hypothesis rm_iff_mem : forall p p' d, p' = pose_domino d p ->
  (In (fst (case_prise d)) p /\ In (snd (case_prise d)) p) .

Definition mk_domino_H (x y : nat) := Hauteur {| x := x ; y := y |}.
Definition mk_domino_L (x y : nat) := Largeur {| x := x ; y := y |}.

Eval compute in plateau_coupe.
Eval compute in pose_domino (mk_domino_H 4 4) plateau_coupe.

(** si on a deux cases différentes, les opérations [ajoute] et [retire] commutent *)
Lemma rw_util col (a c : coord) (p : plateau) : a <> c -> card col (a :: (p \ c)) = card col ((a :: p) \ c).
Proof.
  intro.
  induction p.
  (* HR *)
  { case col; simpl; case (bl_or_no a).
    - intro.
      casse_if Blanc H0.
      case (eq_coord c a).
      + intro. symmetry in e. contradiction.
      + intro. simpl. rewrite H0. trivial.
    - intro.
      casse_if Noir H0.
      apply odd_to_not_even in H0.
      rewrite H0.
      case (eq_coord c a).
      + intro. symmetry in e. contradiction.
      + intro. simpl. casse_if Noir H0.
    - intro.
      casse_if Blanc H0.
      apply even_to_not_odd in H0.
      rewrite H0.
      case (eq_coord c a); intro; trivial.
      + simpl. rewrite H0. trivial.
    - intro.
      casse_if Noir H0.
      case (eq_coord c a); intro; trivial.
      + symmetry in e. contradiction.
      + simpl. rewrite H0. trivial.
  }
  (* Heredite *)
  {
    case col; simpl; case (bl_or_no a).
    - intro.
      casse_if Blanc H0.
      case (eq_coord c a).
      + intro. symmetry in e. contradiction.
      + intro. simpl. rewrite H0. trivial.
    - intro.
      casse_if Noir H0.
      apply odd_to_not_even in H0.
      rewrite H0.
      case (eq_coord c a0);
      intro;
        case (eq_coord c a);
          intro; trivial; simpl;
          casse_if Noir H0.
    - intro.
      casse_if Blanc H0.
      apply even_to_not_odd in H0.
      rewrite H0.
      case (eq_coord c a); intro; trivial.
      + simpl. rewrite H0. trivial.
    - intro.
      casse_if Noir H0.
      apply odd_to_not_even in H0.
      simpl.
      case (eq_coord c a0); intro; simpl.
      + case (eq_coord c a); intro; simpl.
        * symmetry in e0. contradiction.
        * apply odd_to_not_even in H0.
          rewrite H0.
          trivial.
      + case (eq_coord c a); intro; simpl.
        * symmetry in e. contradiction.
        * apply odd_to_not_even in H0. rewrite H0. trivial.
  }
Qed.

(** symmétrie de la différence *)
Lemma diff_sym (a c : coord) : a <> c -> c <> a.
Proof.
  intros H H1.
  rewrite H1 in H.
  contradiction.
Qed.

(** Les listes sont un "modèle" pour un ensemble, on peut supposer le lemme suivant : *)
Hypothesis remove_hd : forall c, forall p, (c :: p) \ c = p.

(** Si on a une case blanche et qu'on l'ajoute à un plateau
 *  alors le nombre de cases blanches du plateau augmente de 1 *)
Lemma cons_card col a p : couleur_case col a -> card col (a :: p) = card col p + 1.
Proof.
  intro.
  destruct col.
  - casse_if Blanc H.
    rewrite Nat.add_1_r.
    trivial.
  - casse_if Noir H.
    rewrite Nat.add_1_r.
    trivial.
Qed.

Lemma cons_card_neq col a p : couleur_case col a -> card (neg_couleur col) (a :: p) = card (neg_couleur col) p.
Proof.
  intro.
  destruct col; simpl; unfold couleur_case in H;
  [ rewrite <- Nat.even_spec in H; apply even_to_not_odd in H
  | rewrite <- Nat.odd_spec  in H; apply odd_to_not_even in H ];
    rewrite H;
    trivial.
Qed.

(** [Blanc] et l'inverse de [Noir] *)
Lemma chg_color1 : Blanc = neg_couleur Noir.
Proof.
  simpl.
  reflexivity.
Qed.

(** [Noir] et l'inverse de [Blanc] *)
Lemma chg_color2 : Noir = neg_couleur Blanc.
Proof.
  simpl.
  reflexivity.
Qed.


Lemma card_eq_hdS col a p p' : card col p + 1 = card col p' -> card col (a :: p) + 1 = card col (a :: p').
Proof.
  intro.
  destruct col; case (bl_or_no a); intro.
    + rewrite (cons_card Blanc a p H0).
      rewrite (cons_card Blanc a p' H0).
      congruence.
    + rewrite chg_color1.
      rewrite (cons_card_neq Noir a p H0).
      rewrite (cons_card_neq Noir a p' H0).
      simpl in *.
      assumption.
    + rewrite chg_color2.
      rewrite (cons_card_neq Blanc a p H0).
      rewrite (cons_card_neq Blanc a p' H0).
      simpl in *.
      assumption.
    + rewrite (cons_card Noir a p H0).
      rewrite (cons_card Noir a p' H0).
      congruence.
Qed.

Lemma retire_case (col : couleur) (a : coord) (p: plateau) :
  couleur_case col a -> List.In a p -> card col (p \ a) + 1 = card col p.
Proof.
  case col;
  induction p; intros Bc Hin; try contradiction.
  {
    case (eq_coord a a0); intro H.
    + rewrite H.
      rewrite remove_hd.
      rewrite H in Bc.
      rewrite (cons_card Blanc a0 p Bc).
      trivial.
    + case (eq_coord a a0). intro. contradiction.
      intro. apply diff_sym in H.
      case (bl_or_no a0); intro.
      - rewrite (cons_card Blanc a0 p H0).
        rewrite <- IHp; trivial.
        * rewrite Nat.add_1_r, Nat.add_1_r.
          apply Nat.succ_inj_wd.
          rewrite <- (rw_util Blanc a0 a p H).
          apply cons_card.
          assumption.
        * eapply List.in_inv in Hin.
          destruct Hin.
          -- rewrite H1 in H. contradiction.
          -- assumption.
      - rewrite <- (rw_util Blanc a0 a p H).
        rewrite (card_eq_hdS Blanc a0 (remove eq_coord a p) p).
        * reflexivity.
        * apply IHp; trivial.
          eapply List.in_inv in Hin.
          destruct Hin.
          -- rewrite H1 in H. contradiction.
          -- assumption.
  }
  {
    case (eq_coord a a0); intro H.
    + rewrite H.
      rewrite remove_hd.
      rewrite H in Bc.
      rewrite (cons_card Noir a0 p Bc).
      trivial.
    + case (eq_coord a a0). intro. contradiction.
      intro. apply diff_sym in H.
      case (bl_or_no a0); intro.
      - rewrite <- (rw_util Noir a0 a p H).
        rewrite (card_eq_hdS Noir a0 (remove eq_coord a p) p).
        * reflexivity.
        * apply IHp; trivial.
          eapply List.in_inv in Hin.
          destruct Hin.
          -- rewrite H1 in H. contradiction.
          -- assumption.
      - rewrite (cons_card Noir a0 p H0).
        rewrite <- IHp; trivial.
        * rewrite Nat.add_1_r, Nat.add_1_r.
          apply Nat.succ_inj_wd.
          rewrite <- (rw_util Noir a0 a p H).
          apply cons_card.
          assumption.
        * eapply List.in_inv in Hin.
          destruct Hin.
          -- rewrite H1 in H. contradiction.
          -- assumption.
  }
Qed.

Lemma retire_case_neg1 (a : coord) (p : plateau) :
  case_noire a -> card_bl (p \ a) = card_bl p.
Proof.
  induction p.
  { auto. }
  { intro H.
    simpl.
    case (eq_coord a a0); intro.
    - rewrite IHp; trivial.
      rewrite e in H.
      unfold case_noire in H.
      apply Nat.odd_spec in H.
      rewrite odd_to_not_even in H.
      rewrite H.
      trivial.
    - simpl.
      case (even (x a0 + y a0)).
      + apply Nat.succ_inj_wd.
        apply IHp.
        assumption.
      + apply IHp.
        assumption.
  }
Qed.

Lemma retire_case_neg2 (a : coord) (p : plateau) :
  case_blanche a -> card_no (p \ a) = card_no p.
Proof.
  induction p.
  { auto. }
  { intro H.
    simpl.
    case (eq_coord a a0); intro.
    - rewrite IHp; trivial.
      rewrite e in H.
      unfold case_blanche in H.
      apply Nat.even_spec in H.
      apply even_to_not_odd in H.
      rewrite H.
      trivial.
    - simpl.
      case (odd (x a0 + y a0)).
      + apply Nat.succ_inj_wd.
        apply IHp.
        assumption.
      + apply IHp.
        assumption.
  }
Qed.

(** l'opération [remove] est commutative *)
Lemma remove_assoc (p : plateau) (a b : coord) : p \ a \ b = p \ b \ a.
Proof.
  case (eq_coord a b).
  { intro. rewrite e. reflexivity. }
  { intro.
    induction p; trivial.
    case (eq_coord a a0).
    { intro.
      rewrite e.
      simpl.
      case (eq_coord a0 a0).
      - intro. 
        case (eq_coord b a0).
        + intro. rewrite e1. reflexivity.
        + intro. rewrite <- e, IHp.
          simpl. case (eq_coord a a).
          * trivial.
          * intro. contradiction.
      - intro. contradiction. }
    { intro. simpl.
      case (eq_coord a a0).
      - intro. contradiction.
      - intro.
        case (eq_coord b a0).
        + intro. rewrite e. simpl.
          case (eq_coord a0 a0).
          * intro. rewrite <- e. trivial.
          * intro. contradiction.
        + intro. simpl.
          case (eq_coord b a0).
          ++ intro. contradiction.
          ++ intro. case (eq_coord a a0).
            * intro. contradiction.
            * intro. rewrite IHp. trivial. } }
Qed.

(** raccourci *)
Ltac apply_lemmas cp h f :=
  assert (H2_cpy : cp); trivial;
  apply h in H2_cpy;
  unfold pose_domino;
  simpl;
  symmetry; rewrite f.

(** Lemme important :
 *  si [p'] est le plateau [p] sur lequel on a posé le domino [d], alors
 *  [p] a exactement une case blanche de plus que [p']
 *)
Lemma invariant_blanc : forall p p': plateau, forall d: domino,
  p' = pose_domino d p ->
  card Blanc p = card Blanc p' + 1.
Proof.
  intros p p' d H.
  case (domino_bicolor d).
  intros H0 H1.
  destruct d; simpl in *; destruct (bl_or_no c);
    unfold case_blanche in H0;
    unfold case_noire in H1;
    unfold couleur_case in H2;
    rewrite H.
  { apply_lemmas (Nat.Even (x c + y c)) H0 (retire_case_neg1 (dessous c) (remove eq_coord c p)).
    apply (retire_case Blanc c p).
    - trivial.
    - destruct (rm_iff_mem p p' (Hauteur c)); trivial.
    - assumption. }
  { clear H0.
    assert (H2_cpy : Nat.Odd (x c + y c)); trivial.
    apply H1 in H2_cpy.
    unfold pose_domino.
    simpl.
    rewrite remove_assoc.
    rewrite (retire_case_neg1 c (remove eq_coord (dessous c) p)); trivial.
    symmetry.
    apply (retire_case Blanc (dessous c) p); simpl; trivial.
    destruct (rm_iff_mem p p' (Hauteur c)); trivial. }
  { apply_lemmas (Nat.Even (x c + y c)) H0 (retire_case_neg1 (droite c) (remove eq_coord c p)).
    apply (retire_case Blanc c p); simpl; trivial.
    apply (rm_iff_mem p p' (Largeur c)); trivial. trivial. }
  { clear H0.
    assert (H2_cpy : Nat.Odd (x c + y c)); trivial.
    apply H1 in H2_cpy.
    unfold pose_domino.
    simpl.
    rewrite remove_assoc.
    rewrite (retire_case_neg1 c (remove eq_coord (droite c) p)); trivial.
    symmetry.
    apply (retire_case Blanc (droite c) p); simpl; trivial.
    apply (rm_iff_mem p p' (Largeur c)).
    trivial. }
Qed.

(** une case ne peut pas être égale à la case en dessous d'elle même *)
Lemma case_diff_dessous : forall c, c <> dessous c.
Proof.
  intros c H.
  case (bl_or_no c).
  + intro.
    assert (Hcp : couleur_case Blanc c); trivial.
    apply dessous_inv_col in H0.
    rewrite <- H in H0.
    eapply bl_no_false_g with c Blanc; assumption.
  + intro.
    assert (H0cp : couleur_case Noir c); trivial.
    apply dessous_inv_col in H0.
    rewrite <- H in H0.
    eapply bl_no_false_g with c Noir; assumption.
Qed.

(** une case ne peut pas être égale à la case à sa droite *)
Lemma case_diff_droite : forall c, c <> droite c.
Proof.
  intros c H.
  case (bl_or_no c).
  + intro.
    assert (Hcp : couleur_case Blanc c); trivial.
    apply droite_inv_col in H0.
    rewrite <- H in H0.
    eapply bl_no_false_g with c Blanc; assumption.
  + intro.
    assert (H0cp : couleur_case Noir c); trivial.
    apply droite_inv_col in H0.
    rewrite <- H in H0.
    eapply bl_no_false_g with c Noir; assumption.
Qed.

(** comme [c] <> [droite c],
    si [c] est dans [p] alors [c] est dans [p \ (droite c)]*)
Lemma in_simp2_droite c p : In c p -> In c (remove eq_coord (droite c) p).
Proof.
  intro.
  apply List.in_in_remove.
  - intro.
    eapply case_diff_droite with c. 
    assumption.
  - assumption.
Qed.

(** comme [c] <> [dessous c],
    si [c] est dans [p] alors [c] est dans [p \ (dessous c)]*)
Lemma in_simp2 c p : In c p -> In c (remove eq_coord (dessous c) p).
Proof.
  intro.
  apply List.in_in_remove.
  - intro.
    eapply case_diff_dessous with c. 
    assumption.
  - assumption.
Qed.

(** comme [c] <> [droite c],
    si [droite c] est dans [p] alors [droite c] est dans [p \ c]*)
Lemma in_simp_droite c p : In (droite c) p -> In (droite c) (remove eq_coord c p).
Proof.
  intro.
  apply List.in_in_remove.
  - intro.
    eapply case_diff_droite with c. 
    symmetry.
    assumption.
  - assumption.
Qed.

(** comme [c] <> [dessous c],
    si [dessous c] est dans [p] alors [dessous c] est dans [p \ c]*)
Lemma in_simp c p : In (dessous c) p -> In (dessous c) (remove eq_coord c p).
Proof.
  intro.
  apply List.in_in_remove.
  - intro.
    eapply case_diff_dessous with c. 
    symmetry.
    assumption.
  - assumption.
Qed.

(** raccourci, voir usage *)
Ltac apply_lemmas_l cp h f :=
  assert (H2_cpy : cp); trivial;
  apply h in H2_cpy;
  unfold pose_domino;
  simpl;
  symmetry;
  rewrite <- f.

(** Lemme important :
 *  si [p'] est le plateau [p] sur lequel on a posé le domino [d], alors
 *  [p] a exactement une case noire de plus que [p']
 *)
Lemma invariant_noir : forall p p': plateau, forall d: domino,
  p' = pose_domino d p ->
  card Noir p  = card Noir  p' + 1.
Proof.
  intros p p' d H.
  case (domino_bicolor d).
  intros H0 H1.
  destruct d; simpl in *; destruct (bl_or_no c);
    unfold couleur_case in H2;
    unfold case_blanche in H0;
    unfold case_noire in H1;
    rewrite H.
  { apply_lemmas_l (Nat.Even (x c + y c)) H0 (retire_case_neg2 c p).
    apply (retire_case Noir (dessous c) (remove eq_coord c p)); simpl; trivial.
    - apply in_simp.
      apply (rm_iff_mem p p' (Hauteur c)).
      trivial.
    - unfold case_blanche. assumption. }
  { apply_lemmas_l (Nat.Odd (x c + y c)) H1 (retire_case_neg2 (dessous c) p).
    rewrite remove_assoc.
    apply (retire_case Noir c (remove eq_coord (dessous c) p)); simpl; trivial.
    - apply in_simp2.
      apply (rm_iff_mem p p' (Hauteur c)).
      trivial.
    - unfold case_blanche. assumption. }
  { apply_lemmas_l (Nat.Even (x c + y c)) H0 (retire_case_neg2 c p).
    apply (retire_case Noir (droite c) (remove eq_coord c p)); simpl; trivial.
    - apply in_simp_droite.
      apply (rm_iff_mem p p' (Largeur c)).
      trivial.
    - unfold case_blanche. assumption. }
  { apply_lemmas_l (Nat.Odd (x c + y c)) H1 (retire_case_neg2 (droite c) p).
    rewrite remove_assoc.
    apply (retire_case Noir c (remove eq_coord (droite c) p)); simpl; trivial.
    - apply in_simp2_droite.
      apply (rm_iff_mem p p' (Largeur c)).
      trivial.
    - unfold case_blanche. assumption. }
Qed.

(** combinaison des deux lemmes importants que l'on vient de définir *)
Lemma invariant : forall p p': plateau, forall d: domino,
  p' = pose_domino d p ->
  card Blanc p = card Blanc p' + 1 /\
  card Noir p  = card Noir  p' + 1.
Proof.
  intros p p' d H.
  split.
  - apply (invariant_blanc p p' d); assumption.
  - apply (invariant_noir p p' d);  assumption.
Qed.

Lemma rw_util3 : forall d a p, pose_dominos d (pose_domino a p) = pose_dominos (a::d) p.
Proof.
  simpl.
  reflexivity.
Qed.

(** le plateau initial mutilé contient deux cases blanches de moins que son nombre de cases noires *)
Lemma card_coupe : card Noir plateau_coupe = card Blanc plateau_coupe + 2.
Proof.
  simpl.
  reflexivity.
Qed.

(*********************** { Critère de résolubilité  } ************************)

(** une liste de dominos « résout » un plateau si une fois que l'on les a tous posé,
    la liste représentant le plateau est vide *)
Definition solution (p : plateau) (dl : list domino) :=
  pose_dominos dl p = [].

(** un définition possible de la résolubilité d'un plateau
 *  un plateau est résoluble s'il existe un liste de domino
 *  telle que lorsque les domino seront posés le plateau sera vide *)
Definition resoluble (p : plateau) :=
  exists dl : list domino, solution p dl.

(**************************** { Classical board } ****************************)

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

(* Eval compute in sol_base. *)

(** la solution fonctionne bien *)
Corollary classic_board_resoluble : resoluble plateau_base.
Proof.
  unfold resoluble.
  exists sol_base.
  simpl.
  unfold pose_domino.
  simpl.
  reflexivity.
Qed.

(**************************** { Mutilated Board  } ***************************)

Lemma pose_domino_dont_change_card : forall d p,
  card_no (pose_domino d p) = card_bl (pose_domino d p) ->
  card_no p = card_bl p.
Proof.
  intros d p.
  set (p' := pose_domino d p).
  assert (p' = pose_domino d p). auto.
  set (H1 := invariant p p' d H).
  destruct H1.
  simpl in H0, H1.
  rewrite H0, H1.
  auto.
Qed.

(* Goal forall d p, card_bl (pose_domino d p) + 1 = card_bl p. *)
(* Lemma cons_card col a p : couleur_case col a -> card col (a :: p) = card col p + 1. *)


(** combinaison des deux lemmes importants que l'on vient de définir *)
Lemma invariant_extended_to_dominolist : forall p p': plateau, forall dl: list domino,
  pose_dominos dl p = p' ->
  card Blanc p = card Blanc p' + (List.length dl) /\
  card Noir p = card Noir p' + (List.length dl).
Proof.
  intros p p' dl.
  destruct dl; intro H.
  { rewrite <- H. simpl. lia. }
  {
    destruct d;
    (* simpl in *; *)
    split;
    case (bl_or_no c);
    intro col.
    - 
    (* rewrite rw_util3 in H; *)
    (* rewrite <- H. *)
    (* unfold pose_dominos. *)

Admitted.


Theorem resoluble_invariant : forall p, resoluble p -> card Noir p = card Blanc p.
Proof.
  intros p H.
  destruct H.
  unfold solution in H.
  induction x0; simpl in *.
  { rewrite H. simpl. reflexivity. }
  { apply invariant_extended_to_dominolist  in H.
    simpl in H.
    destruct H.
    rewrite <- H in H0.
    apply (pose_domino_dont_change_card a).
    assumption. }
Qed.

Corollary mutilated_board : ~ resoluble plateau_coupe.
Proof.
  intro.
  apply resoluble_invariant in H.
  rewrite card_coupe in H.
  lia.
Qed.
