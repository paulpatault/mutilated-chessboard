Require Import Arith Nat Bool List Lia.
Import ListNotations.


Record coord := mkCoord { x : nat; y : nat }.

Definition plateau := list coord.

Inductive couleur := Blanc | Noir.

Definition neg_couleur c :=
  match c with
  | Blanc => Noir
  | Noir => Blanc
  end.

Inductive domino :=
  | Hauteur : coord -> domino
  | Largeur : coord -> domino.

Definition droite  (c : coord) := {| x := c.(x) + 1; y := c.(y) |}.
(* Definition gauche  (c : coord) := {| x := c.(x) - 1; y := c.(y) |}. *)
(* Definition dessus  (c : coord) := {| x := c.(x)    ; y := c.(y) - 1 |}. *)
Definition dessous (c : coord) := {| x := c.(x)    ; y := c.(y) + 1 |}.

Definition case_prise : domino -> coord * coord := fun d =>
  match d with
  | Hauteur c => (c, dessous c)
  | Largeur c => (c, droite c)
  end.

Definition case_blanche (c : coord) : Prop := Nat.Even (c.(x) + c.(y)).
Definition case_noire   (c : coord) : Prop := Nat.Odd  (c.(x) + c.(y)).

Definition couleur_case (cc : couleur) (c : coord) : Prop :=
  match cc with
  | Blanc => Nat.Even (c.(x) + c.(y))
  | Noir  => Nat.Odd  (c.(x) + c.(y))
  end.

Definition est_blanche (c : coord) : bool := even (c.(x) + c.(y)).
Definition est_noire   (c : coord) : bool := odd (c.(x) + c.(y)).

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

Definition card (c : couleur) (p : plateau) :=
  match c with
  | Blanc => card_bl p
  | Noir  => card_no p
  end.


Lemma bl_or_no : forall c: coord, couleur_case Blanc c \/ couleur_case Noir c.
Proof.
  intro.
  eapply Nat.Even_or_Odd.
Qed.

Lemma bl_no_false : forall c: coord, case_blanche c -> ~ (case_noire c).
Proof.
  intros c H1 H2.
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

Ltac casse_if col h :=
  unfold card;
  match col with
  | Blanc =>
    unfold card_bl;
    unfold couleur_case in h;
    unfold case_blanche in h;
    rewrite <- Nat.even_spec in h;
    rewrite h
  | Noir =>
    unfold card_no;
    unfold couleur_case in h;
    unfold case_noire in h;
    rewrite <- Nat.odd_spec in h;
    rewrite h
  end.

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

Lemma eq_coord : forall a b : coord, {a = b} + {a <> b}.
Proof.
  decide equality; decide equality.
Defined.

Infix "\" := (fun a b => List.remove eq_coord b a) (at level 31, left associativity).

Definition plateau_sc := plateau8 \ {| x := 7; y := 7|} \ {| x := 0; y := 0|}.

Eval compute in plateau_sc.

  (* List.filter (fun e => negb (neq07 e)) plateau8. *)
(*
   Eval compute in mem eq_coord {| x := 0; y := 0 |} plateau8.   (* true *)
   Eval compute in mem eq_coord {| x := 0; y := 0 |} plateau_sc. (* false *)
 *)

Definition pose_domino (d:domino) (p:plateau) : plateau :=
  p \ fst (case_prise d) \ snd (case_prise d).

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

Hypothesis unique : forall a : coord, forall p : plateau, (List.In a (a :: p) -> ~List.In a p).

Lemma rw_util col (a c : coord) (p : plateau) : a <> c -> card col (a :: (p \ c)) = card col ((a :: p) \ c).
Proof.
  intro. induction p; simpl in *.
  { case (bl_or_no a).
    + intro.
      casse_if Blanc H0.
      simpl.
      case (eq_coord c a).
      admit.
      (* assert ((eq_coord c a) -> False). *)

  (* } *)
Admitted.

Require Import Lia.

Lemma diff_sym (a c : coord) : a <> c -> c <> a.
Proof.
  intros H H1.
  rewrite H1 in H.
  contradiction.
Qed.


Hypothesis remove_hd : forall c, forall p, (c :: p) \ c = p.


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

Lemma chg_color1 : Blanc = neg_couleur Noir.
Proof.
  simpl.
  reflexivity.
Qed.

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
        rewrite <- IHp; try assumption.
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
        * apply IHp; try assumption.
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
        * apply IHp; try assumption.
          eapply List.in_inv in Hin.
          destruct Hin.
          -- rewrite H1 in H. contradiction.
          -- assumption.
      - rewrite (cons_card Noir a0 p H0).
        rewrite <- IHp; try assumption.
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
  { intros.
    simpl.
    case (eq_coord a a0); intro.
    - rewrite IHp; try assumption.
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

Lemma retire_case_neg2 (a : coord) (p : plateau) : case_blanche a -> card_no (p \ a) = card_no p.
Proof.
  induction p.
  { auto. }
  { intros.
    simpl.
    case (eq_coord a a0); intro.
    - rewrite IHp; try assumption.
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

Lemma remove_assoc (p : plateau) (a b : coord) : p \ a \ b = p \ b \ a.
Proof.
  induction p; auto.
  simpl.
Admitted.

Lemma invariant : forall p p': plateau, forall d: domino,
  p' = pose_domino d p ->
  card Blanc p = card Blanc p' + 1 /\
  card Noir p  = card Noir  p' + 1.
Proof.
  intros.
  case (domino_bicolor d).
  split.
  {
    destruct d; simpl in *.
    + destruct (bl_or_no c).
      - clear H1; unfold couleur_case in H2; unfold case_blanche in H0.
        assert (H2_cpy : Nat.Even (x c + y c)); try assumption.
        apply H0 in H2_cpy.
        rewrite H.
        unfold pose_domino.
        simpl.
        apply (retire_case_neg1 (dessous c) (remove eq_coord c p)).
        * symmetry.
          apply (retire_case Blanc c p).
          ** simpl.
             assumption.
          ** admit.
        * assumption.
      - clear H0; unfold couleur_case in H2; unfold case_noire in H1.
        assert (H2_cpy : Nat.Odd (x c + y c)); try assumption.
        apply H1 in H2_cpy.
        rewrite H.
        unfold pose_domino.
        simpl.
        rewrite remove_assoc.
        rewrite (retire_case_neg1 c (remove eq_coord (dessous c) p)).
        * admit.
        * assumption.

    + destruct (bl_or_no c).
      - clear H1; unfold couleur_case in H2; unfold case_blanche in H0.
        assert (H2_cpy : Nat.Even (x c + y c)); try assumption.
        apply H0 in H2_cpy.
        rewrite H.
        unfold pose_domino.
        simpl.
        rewrite (retire_case_neg (droite c) (remove eq_coord c p)).
        * symmetry.
          apply (retire_case Blanc c p).
          ** simpl.
             assumption.
          ** admit.
        * assumption.
      - clear H0; unfold couleur_case in H2; unfold case_noire in H1.
        assert (H2_cpy : Nat.Odd (x c + y c)); try assumption.
        apply H1 in H2_cpy.
        rewrite H.
        unfold pose_domino.
        simpl.
        rewrite remove_assoc.
        rewrite (retire_case_neg c (remove eq_coord (droite c) p)).
        * admit.
        * assumption.
  }
  {
    destruct d; simpl in *.
    + destruct (bl_or_no c).
      - clear H1; unfold couleur_case in H2; unfold case_blanche in H0.
        assert (H2_cpy : Nat.Even (x c + y c)); try assumption.
        apply H0 in H2_cpy.
        rewrite H.
        unfold pose_domino.
        simpl.
        rewrite <- (retire_case_neg (dessous c) (remove eq_coord c p)).
        * symmetry.
          apply (retire_case Blanc c p).
          ** simpl.
             assumption.
          ** admit.
        * assumption.
      - clear H0; unfold couleur_case in H2; unfold case_noire in H1.
        assert (H2_cpy : Nat.Odd (x c + y c)); try assumption.
        apply H1 in H2_cpy.
        rewrite H.
        unfold pose_domino.
        simpl.
        rewrite remove_assoc.
        rewrite (retire_case_neg c (remove eq_coord (dessous c) p)).
        * admit.
        * assumption.

    + destruct (bl_or_no c).
      - clear H1; unfold couleur_case in H2; unfold case_blanche in H0.
        assert (H2_cpy : Nat.Even (x c + y c)); try assumption.
        apply H0 in H2_cpy.
        rewrite H.
        unfold pose_domino.
        simpl.
        rewrite (retire_case_neg (droite c) (remove eq_coord c p)).
        * symmetry.
          apply (retire_case Blanc c p).
          ** simpl.
             assumption.
          ** admit.
        * assumption.
      - clear H0; unfold couleur_case in H2; unfold case_noire in H1.
        assert (H2_cpy : Nat.Odd (x c + y c)); try assumption.
        apply H1 in H2_cpy.
        rewrite H.
        unfold pose_domino.
        simpl.
        rewrite remove_assoc.
        rewrite (retire_case_neg c (remove eq_coord (droite c) p)).
        * admit.
        * assumption.
  }
  }

Lemma retire_case (col : couleur) (a : coord) (p: plateau) :
  couleur_case col a -> List.In a p -> card col (p \ a) + 1 = card col p.

Lemma domino_bicolor (d : domino) :
  (case_blanche (fst (case_prise d)) -> case_noire   (snd (case_prise d))) /\
  (case_noire   (fst (case_prise d)) -> case_blanche (snd (case_prise d))).

