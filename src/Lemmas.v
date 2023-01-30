Require Import Domino Disjoint Resoluble WF.
Require Import Arith Nat List Lia.
Import ListNotations.

Create HintDb lemmas_hints.

(*****************************************************************************************)
(************************************ { Lemmes}  *****************************************)
(*****************************************************************************************)

(** étant donnée la case [c], celle en dessous de [c] a la couleur opposée *)
Lemma dessous_inv_col col c :
  couleur_case col c <-> couleur_case (neg_couleur col) (dessous c).
Proof.
  split.
  { case col;
    unfold couleur_case;
    intro;
    simpl;
    rewrite Nat.add_assoc;
    rewrite Nat.add_1_r.
    - apply Nat.odd_spec.
      rewrite Nat.odd_succ.
      apply Nat.even_spec.
      assumption.
    - apply Nat.even_spec.
      rewrite Nat.even_succ.
      apply Nat.odd_spec.
      assumption.
  }
  { case col;
    unfold couleur_case;
    intro;
    simpl in *;
    rewrite Nat.add_assoc in H;
    rewrite Nat.add_1_r in H.
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
Lemma droite_inv_col col c :
  couleur_case col c -> couleur_case (neg_couleur col) (droite c).
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

(** les cases prisent par un domino sont exactement
    une case blanche et une case noire *)
Lemma domino_bicolor (d : domino) :
  (case_blanche (fst (case_prise d)) -> case_noire   (snd (case_prise d))) /\
  (case_noire   (fst (case_prise d)) -> case_blanche (snd (case_prise d))).
Proof.
  split; destruct d; unfold case_prise; simpl; intro H.
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

(** la couleur d'une case est [Blanc] ou [Noir] *)
Lemma bl_or_no : forall c: coord, couleur_case Blanc c \/ couleur_case Noir c.
Proof.
  intro c.
  eapply Nat.Even_or_Odd.
Qed.

(** une case [c] ne peut pas être de plusieurs couleurs *)
Lemma bl_no_false_g :
  forall c col, couleur_case col c ->
                couleur_case (neg_couleur col) c ->
                False.
Proof.
  intros c col H2 H3.
  destruct col;
   simpl in *;
    apply (Nat.Even_Odd_False (x c + y c)); assumption.
Qed.

(** si [n] est pair, alors [n] n'est pas impair (dans Bool) *)
Lemma even_to_not_odd (n:nat) : Nat.even n = true -> Nat.odd n = false.
Proof.
  rewrite <- Nat.negb_odd.
  intro H.
  rewrite Bool.negb_true_iff in H.
  assumption.
Qed.

(** [n] est impair est équivalent à [n] n'est pas pair (dans Bool) *)
Lemma odd_to_not_even (n:nat) : Nat.odd n = true <-> Nat.even n = false.
Proof.
  split.
  - rewrite <- Nat.negb_odd.
    intro H.
    rewrite Bool.negb_false_iff.
    assumption.
  - intro H.
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

(** si on a deux cases différentes, les opérations [ajoute] et [retire] commutent *)
Lemma rw_util col (a c : coord) (p : plateau) :
  a <> c -> card col (a :: (p \ c)) = card col ((a :: p) \ c).
Proof.
  intro H.
  induction p.
  (* HR *)
  { case col; simpl; case (bl_or_no a); intro H0.
    - casse_if Blanc H0.
      case (eq_coord c a).
      + intro e. symmetry in e. contradiction.
      + intro e. simpl. rewrite H0. trivial.
    - casse_if Noir H0.
      apply odd_to_not_even in H0.
      rewrite H0.
      case (eq_coord c a).
      + intro e. symmetry in e. contradiction.
      + intro e. simpl. casse_if Noir H0.
    - casse_if Blanc H0.
      apply even_to_not_odd in H0.
      rewrite H0.
      case (eq_coord c a); intro; trivial.
      + simpl. rewrite H0. trivial.
    - casse_if Noir H0.
      case (eq_coord c a); intro; trivial.
      + symmetry in e. contradiction.
      + simpl. rewrite H0. trivial.
  }
  (* Heredite *)
  {
    case col; simpl; case (bl_or_no a); intro H0.
    - casse_if Blanc H0.
      case (eq_coord c a).
      + intro e. symmetry in e. contradiction.
      + intro e. simpl. rewrite H0. trivial.
    - casse_if Noir H0.
      apply odd_to_not_even in H0.
      rewrite H0.
      case (eq_coord c a0);
      intro;
        case (eq_coord c a);
          intro; trivial; simpl;
          casse_if Noir H0.
    - casse_if Blanc H0.
      apply even_to_not_odd in H0.
      rewrite H0.
      case (eq_coord c a); intro; trivial.
      + simpl. rewrite H0. trivial.
    - casse_if Noir H0.
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

(** Si on a une case blanche et qu'on l'ajoute à un plateau
    alors le nombre de cases blanches du plateau augmente de 1 *)
Lemma cons_card col a p : couleur_case col a -> card col (a :: p) = card col p + 1.
Proof.
  intro H.
  destruct col.
  - casse_if Blanc H.
    rewrite Nat.add_1_r.
    trivial.
  - casse_if Noir H.
    rewrite Nat.add_1_r.
    trivial.
Qed.

(** si [a] est une case de couleur [col],
    alors [a] ne pèse pas dans le compte des cases de couleurs [neg col] *)
Lemma cons_card_neq col a p :
  couleur_case col a ->
  card (neg_couleur col) (a :: p) = card (neg_couleur col) p.
Proof.
  intro H.
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

(** ajouter la même case à deux plateau ne change rien
    à l'égalité entre les comptes de couleurs *)
Lemma card_eq_hdS col a p p' :
  card col p + 1 = card col p' ->
  card col (a :: p) + 1 = card col (a :: p').
Proof.
  intro H.
  destruct col; case (bl_or_no a); intro H0.
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

(** si on retire une case de la couleur que l'on compte, alors on en a une de moins *)
Lemma retire_case (col : couleur) (a : coord) (p: plateau) :
  well_formed p ->
  couleur_case col a ->
  List.In a p ->
  card col (p \ a) + 1 = card col p.
Proof.
  case col;
  induction p; intros wfp Bc Hin; try contradiction.
  {
    case (eq_coord a a0); intro H.
    + rewrite H.
      simpl.
      rewrite eq_rw.
      rewrite (rw_wf_in p a0 wfp).
      rewrite H in Bc.
      simpl in Bc.
      apply Nat.even_spec in Bc.
      rewrite Bc.
      lia.
    + case (eq_coord a a0). intro e. contradiction.
      intro n. apply diff_sym in H.
      case (bl_or_no a0); intro H0.
      - rewrite (cons_card Blanc a0 p H0).
        rewrite <- IHp; trivial.
        * rewrite Nat.add_1_r, Nat.add_1_r.
          apply Nat.succ_inj_wd.
          rewrite <- (rw_util Blanc a0 a p H).
          apply cons_card.
          assumption.
        * apply (wf_minus_hd p a0); assumption.
        * eapply List.in_inv in Hin.
          destruct Hin.
          -- rewrite H1 in H. contradiction.
          -- assumption.
      - rewrite <- (rw_util Blanc a0 a p H).
        rewrite (card_eq_hdS Blanc a0 (remove eq_coord a p) p).
        * reflexivity.
        * apply IHp; trivial.
          ++ apply (wf_minus_hd p a0); assumption.
          ++ eapply List.in_inv in Hin.
             destruct Hin.
             -- rewrite H1 in H. contradiction.
             -- assumption.
  }
  {
    case (eq_coord a a0); intro H.
    + rewrite H.
      simpl.
      rewrite eq_rw.
      rewrite (rw_wf_in p a0 wfp).
      rewrite H in Bc.
      simpl in Bc.
      apply Nat.odd_spec in Bc.
      rewrite Bc.
      lia.
    + case (eq_coord a a0). intro e. contradiction.
      intro n. apply diff_sym in H.
      case (bl_or_no a0); intro H0.
      - rewrite <- (rw_util Noir a0 a p H).
        rewrite (card_eq_hdS Noir a0 (remove eq_coord a p) p).
        * reflexivity.
        * apply IHp; trivial.
          ++ apply (wf_minus_hd p a0); assumption.
          ++ eapply List.in_inv in Hin.
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
        * apply (wf_minus_hd p a0); assumption.

        * eapply List.in_inv in Hin.
          destruct Hin.
          -- rewrite H1 in H. contradiction.
          -- assumption.
  }
Qed.

#[global]
Hint Resolve retire_case : lemmas_hints.

(** si on retire une case de la couleur que l'on ne compte pas
    alors le compte n'a pas changé *)
Lemma retire_case_neg1 (a : coord) (p : plateau) :
  case_noire a -> card_bl (p \ a) = card_bl p.
Proof.
  induction p.
  { auto. }
  { intro H.
    simpl.
    case (eq_coord a a0); intro e.
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

#[global]
Hint Resolve retire_case_neg1 : lemmas_hints.

(** si on retire une case de la couleur que l'on ne compte pas
    alors le compte n'a pas changé *)
Lemma retire_case_neg2 (a : coord) (p : plateau) :
  case_blanche a -> card_no (p \ a) = card_no p.
Proof.
  induction p.
  { auto. }
  { intro H.
    simpl.
    case (eq_coord a a0); intro e.
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

#[global]
Hint Resolve retire_case_neg2 : lemmas_hints.

(** l'opération [remove] est commutative *)
Lemma remove_comm (p : plateau) (a b : coord) : p \ a \ b = p \ b \ a.
Proof.
  case (eq_coord a b).
  { intro e. rewrite e. reflexivity. }
  { intro n.
    induction p; trivial.
    case (eq_coord a a0).
    { intro e.
      rewrite e.
      simpl.
      case (eq_coord a0 a0).
      - intro e0.
        case (eq_coord b a0).
        + intro e1. rewrite e1. reflexivity.
        + intro e1. rewrite <- e, IHp.
          simpl. case (eq_coord a a).
          * trivial.
          * now contradiction.
      - now contradiction. }
    { intro n0. simpl.
      case (eq_coord a a0).
      - now contradiction.
      - intro n1.
        case (eq_coord b a0).
        + intro e. rewrite e. simpl.
          case (eq_coord a0 a0).
          * intro e0. rewrite <- e. trivial.
          * now contradiction.
        + intro n2. simpl.
          case (eq_coord b a0).
          * now contradiction.
          * intro n3. case (eq_coord a a0).
             now contradiction.
             now rewrite IHp. }
  }
Qed.

(** raccourci *)
Ltac apply_lemmas cp h f :=
  assert (H2_cpy : cp); trivial;
  apply h in H2_cpy;
  unfold pose_domino;
  simpl;
  symmetry; rewrite f.

(** Lemme important :
    si [p'] est le plateau [p] sur lequel on a posé le domino [d], alors
    [p] a exactement une case blanche de plus que [p']
 *)
Lemma invariant_blanc : forall p p': plateau, forall d: domino,
  well_formed p ->
  p' = pose_domino d p ->
  card Blanc p = card Blanc p' + 1.
Proof.
  intros p p' d wfp H.
  case (domino_bicolor d).
  intros H0 H1.
  destruct d; simpl in *; destruct (bl_or_no c);
    unfold case_blanche in H0;
    unfold case_noire in H1;
    unfold couleur_case in H2;
    rewrite H.
  { assert (H2_cpy := H2 ); trivial.
    apply H0 in H2_cpy.
    unfold pose_domino.
    simpl.
    symmetry.
    rewrite  (retire_case_neg1 (dessous c) (p\c)).
    apply (retire_case Blanc c p wfp).
    - trivial.
    - destruct (Domino.rm_iff_mem p p' (Hauteur c)); trivial.
    - assumption. }
  { clear H0.
    assert (H2_cpy : Nat.Odd (x c + y c)); trivial.
    apply H1 in H2_cpy.
    unfold pose_domino.
    simpl.
    rewrite remove_comm.
    rewrite (retire_case_neg1 c (p \ dessous c)); trivial.
    symmetry.
    apply (retire_case Blanc (dessous c) p wfp); simpl; trivial.
    destruct (Domino.rm_iff_mem p p' (Hauteur c)); trivial. }
  { assert (H2_cpy := H2); trivial;
    apply H0 in H2_cpy;
    unfold pose_domino;
    simpl;
    symmetry; rewrite (retire_case_neg1 (droite c) (p\c)).
    apply (retire_case Blanc c p wfp); simpl; trivial.
    apply (Domino.rm_iff_mem p p' (Largeur c)); trivial. trivial. }
  { clear H0.
    assert (H2_cpy : Nat.Odd (x c + y c)); trivial.
    apply H1 in H2_cpy.
    unfold pose_domino.
    simpl.
    rewrite remove_comm.
    rewrite (retire_case_neg1 c (p \ droite c)); trivial.
    symmetry.
    apply (retire_case Blanc (droite c) p wfp); simpl; trivial.
    apply (Domino.rm_iff_mem p p' (Largeur c)).
    trivial. }
Qed.

(** une case ne peut pas être égale à la case en dessous d'elle même *)
Lemma case_diff_dessous : forall c, c <> dessous c.
Proof.
  intros c H.
  case (bl_or_no c); intro H0.
  + assert (Hcp : couleur_case Blanc c); trivial.
    apply dessous_inv_col in H0.
    rewrite <- H in H0.
    eapply bl_no_false_g with c Blanc; assumption.
  + assert (H0cp : couleur_case Noir c); trivial.
    apply dessous_inv_col in H0.
    rewrite <- H in H0.
    eapply bl_no_false_g with c Noir; assumption.
Qed.

(** une case ne peut pas être égale à la case à sa droite *)
Lemma case_diff_droite : forall c, c <> droite c.
Proof.
  intros c H.
  case (bl_or_no c); intro H0.
  + assert (Hcp : couleur_case Blanc c); trivial.
    apply droite_inv_col in H0.
    rewrite <- H in H0.
    eapply bl_no_false_g with c Blanc; assumption.
  + assert (H0cp : couleur_case Noir c); trivial.
    apply droite_inv_col in H0.
    rewrite <- H in H0.
    eapply bl_no_false_g with c Noir; assumption.
Qed.

(** comme [c] <> [droite c],
    si [c] est dans [p] alors [c] est dans [p \ (droite c)]*)
Lemma in_simp2_droite c p : In c p -> In c (p \ droite c).
Proof.
  intro H.
  apply List.in_in_remove.
  - intro H1.
    eapply case_diff_droite with c.
    assumption.
  - assumption.
Qed.

(** comme [c] <> [dessous c],
    si [c] est dans [p] alors [c] est dans [p \ (dessous c)]*)
Lemma in_simp2 c p : In c p -> In c (p \ dessous c).
Proof.
  intro H.
  apply List.in_in_remove.
  - intro H1.
    eapply case_diff_dessous with c.
    assumption.
  - assumption.
Qed.

(** comme [c] <> [droite c],
    si [droite c] est dans [p] alors [droite c] est dans [p \ c]*)
Lemma in_simp_droite c p : In (droite c) p -> In (droite c) (p \ c).
Proof.
  intro H.
  apply List.in_in_remove.
  - intro H1.
    eapply case_diff_droite with c.
    symmetry.
    assumption.
  - assumption.
Qed.

(** comme [c] <> [dessous c],
    si [dessous c] est dans [p] alors [dessous c] est dans [p \ c]*)
Lemma in_simp c p : In (dessous c) p -> In (dessous c) (p \ c).
Proof.
  intro H.
  apply List.in_in_remove.
  - intro H1.
    eapply case_diff_dessous with c.
    symmetry.
    assumption.
  - assumption.
Qed.

#[global]
Hint Resolve in_simp : lemmas_hints.
#[global]
Hint Resolve in_simp2 : lemmas_hints.
#[global]
Hint Resolve in_simp_droite : lemmas_hints.
#[global]
Hint Resolve in_simp2_droite : lemmas_hints.

(** raccourci, voir usage *)
Ltac apply_lemmas_l cp h f :=
  assert (H2_cpy : cp); trivial;
  apply h in H2_cpy;
  unfold pose_domino;
  simpl;
  symmetry;
  rewrite <- f.

(** Lemme important :
    si [p'] est le plateau [p] sur lequel on a posé le domino [d], alors
    [p] a exactement une case noire de plus que [p']
 *)
Lemma invariant_noir : forall p p': plateau, forall d: domino,
  well_formed p ->
  p' = pose_domino d p ->
  card Noir p  = card Noir  p' + 1.
Proof.
  intros p p' d wfp H.
  case (domino_bicolor d).
  intros H0 H1.
  destruct d; simpl in *; destruct (bl_or_no c);
    unfold couleur_case in H2;
    unfold case_blanche in H0;
    unfold case_noire in H1;
    rewrite H.
  { apply_lemmas_l (Nat.Even (x c + y c)) H0 (retire_case_neg2 c p).
    set (t := wf_minus p wfp c).
    apply (retire_case Noir (dessous c) (p\c) t); simpl; trivial.
    - apply in_simp.
      apply (Domino.rm_iff_mem p p' (Hauteur c)).
      trivial.
    - unfold case_blanche. assumption. }
  { apply_lemmas_l (Nat.Odd (x c + y c)) H1 (retire_case_neg2 (dessous c) p).
    rewrite remove_comm.
    apply (retire_case Noir c (p\dessous c)); simpl; trivial.
    - apply (wf_minus p wfp (dessous c)).
    - apply in_simp2.
      apply (Domino.rm_iff_mem p p' (Hauteur c)).
      trivial.
    - unfold case_blanche. assumption. }
  { apply_lemmas_l (Nat.Even (x c + y c)) H0 (retire_case_neg2 c p).
    apply (retire_case Noir (droite c) (p\c)); simpl; trivial.
    - apply (wf_minus p wfp c).
    - apply in_simp_droite.
      apply (Domino.rm_iff_mem p p' (Largeur c)).
      trivial.
    - unfold case_blanche. assumption. }
  { apply_lemmas_l (Nat.Odd (x c + y c)) H1 (retire_case_neg2 (droite c) p).
    rewrite remove_comm.
    apply (retire_case Noir c (p\droite c)); simpl; trivial.
    - apply (wf_minus p wfp (droite c)).
    - apply in_simp2_droite.
      apply (Domino.rm_iff_mem p p' (Largeur c)).
      trivial.
    - unfold case_blanche. assumption. }
Qed.

(** combinaison des deux lemmes importants que l'on vient de définir *)
Lemma invariant : forall p p': plateau, forall d: domino,
  well_formed p ->
  p' = pose_domino d p ->
  card Blanc p = card Blanc p' + 1 /\
  card Noir p  = card Noir  p' + 1.
Proof.
  intros p p' d wfp H.
  split.
  - apply (invariant_blanc p p' d); assumption.
  - apply (invariant_noir p p' d);  assumption.
Qed.

Lemma rw_util3 : forall d a p, pose_dominos d (pose_domino a p) = pose_dominos (a::d) p.
Proof.
  simpl.
  reflexivity.
Qed.

(** le plateau initial mutilé contient deux cases blanches
    de moins que son nombre de cases noires *)
Lemma card_coupe : card Noir plateau_coupe = card Blanc plateau_coupe + 2.
Proof.
  simpl.
  reflexivity.
Qed.

Lemma pose_domino_dont_change_card : forall d p,
  well_formed p ->
  card_no (pose_domino d p) = card_bl (pose_domino d p) ->
  card_no p = card_bl p.
Proof.
  intros d p wfp.
  set (p' := pose_domino d p).
  assert (p' = pose_domino d p). auto.
  set (H1 := invariant p p' d wfp H).
  destruct H1.
  simpl in H0, H1.
  rewrite H0, H1.
  auto.
Qed.


Lemma write : forall d1 d2, d1 # d2 ->
  match d1, d2 with
  | Largeur c1, Largeur c2 => c1 <> c2 /\ droite c1 <> droite c2
  | Hauteur c1, Hauteur c2 => c1 <> c2 /\ dessous c1 <> dessous c2
  | Largeur c1, Hauteur c2
  | Hauteur c2, Largeur c1 =>
             c1 <> c2 /\
      droite c1 <> c2 /\
             c1 <> dessous c2 /\
      droite c1 <> dessous c2
  end.
Proof.
  intros d1 d2 H.
  case d1, d2;
  unfold disjoints2_dominos in H;
  destruct H;
  destruct H0;
  destruct H1;
  auto.
Qed.

#[global]
Hint Resolve remove_comm : lemmas_hints.

(** l'opération pose_domino est commutative *)
Lemma pose_domino_comm :
  forall p d1 d2,
  d1 # d2 ->
  pose_domino d1 (pose_domino d2 p) = pose_domino d2 (pose_domino d1 p).
Proof.
  intros p d1 d2.
  revert p.
  case (eq_domino d1 d2).
  - intro eqH. rewrite eqH. auto.
  - intro neqH.
    intros p H.
    destruct d1, d2;
    unfold pose_domino;
    simpl;
    unfold disjoints2_dominos in H;
    induction p;
    try (simpl; reflexivity).
    * rewrite <- (remove_comm ((a :: p)\c) c0 (dessous c)).
      rewrite <- (remove_comm ((a :: p)\c\c0) (dessous c0) (dessous c)).
      rewrite <- (remove_comm (a :: p) c0 c).
      rewrite <- (remove_comm ((a :: p)\c0) (dessous c0) c).
      reflexivity.
    * rewrite <- (remove_comm ((a :: p)\c) c0 (dessous c)).
      rewrite <- (remove_comm ((a :: p)) c0 c).
      rewrite <- (remove_comm ((a :: p)\c0\c) (droite c0) (dessous c)).
      rewrite <- (remove_comm ((a :: p)\c0) c (droite c0)).
      reflexivity.
    * rewrite <- (remove_comm ((a :: p)\c) c0 (droite c)).
      rewrite <- (remove_comm ((a :: p)) c0 c).
      rewrite <- (remove_comm ((a :: p)\c0\c) (dessous c0) (droite c)).
      rewrite <- (remove_comm ((a :: p)\c0) (dessous c0) c).
      reflexivity.
    * rewrite <- (remove_comm ((a :: p)\c) c0 (droite c)).
      rewrite <- (remove_comm ((a :: p)\c\c0) (droite c0) (droite c)).
      rewrite <- (remove_comm (a :: p) c0 c).
      rewrite <- (remove_comm ((a :: p)\c0) (droite c0) c).
      reflexivity.
Qed.

Lemma disj_lemma1 : forall d a a0 dl, d ## (a :: a0 :: dl) ->
   d # a /\ d ## dl.
Proof.
  induction dl;
  intros; simpl; split;
  unfold disjoints_dominos_l in H; destruct H; auto.
  destruct H0.
  auto.
Qed.


Lemma disj_lemma2  :
  forall d a a0 dl,
    d ## (a :: a0 :: dl) ->
    d ## (a0 :: a0 :: dl).
Proof.
  induction dl;
  intros; simpl; split;
  unfold disjoints_dominos_l in H;
  destruct H; auto;
  destruct H0;
  assumption.
Qed.

Lemma disj_lemma3 : forall d1 d2, d1 # d2 -> d2 # d1.
Proof.
  intros d1 d2 H.
  destruct d1, d2;
  unfold disjoints2_dominos in *;
  intuition.
Qed.

Lemma rw_util4_for4 : forall p dl d,
  d ## dl ->
  pose_dominos (d::dl) p = (pose_dominos (dl++[d]) p).
Proof.
  intros p dl d H.
  revert p.
  induction dl.
  { auto. }
  {
    intro p.
    simpl.
    rewrite pose_domino_comm.
    set (pa := pose_domino a p).
    apply IHdl.
    -
      (* induction dl; simpl; auto. *)
      induction dl. simpl; auto.
      eapply disj_lemma1 with a0.
      eapply disj_lemma2 with a.
      assumption.
    - induction dl.
      + unfold disjoints_dominos_l in H.
        destruct H.
        apply disj_lemma3.
        assumption.
      + apply disj_lemma1 in H.
        destruct H.
        apply disj_lemma3.
        assumption.
  }
Qed.

(** poser un domino [d] puis la liste [dl]
    est équivalent à poser [dl] puis [d]    *)
Lemma rw_util4 :
  forall p dl d, d ## dl -> pose_dominos (d::dl) p = pose_domino d (pose_dominos dl p).
Proof.
  intros p dl d H.
  rewrite (rw_util4_for4 p dl d).
  revert p.
  induction dl.
  { auto. }
  { simpl.
    intro p.
    apply IHdl.
    induction dl.
    - simpl. auto.
    - simpl.
      try (unfold disjoints_dominos_l in H;
        destruct H;
        destruct H0;
        auto).
      }
  { assumption. }
Qed.

(** [Lemma retire_domino] : poser un domino sur un plateau
                            retire une case de chaque couleur
    remarque : les preuves des 8 sous cas sont très proches
               mais je n'ai pas réussi à les factoriser *)
Lemma retire_domino : forall p d col,
  well_formed p ->
  card col p = S (card col (pose_domino d p)).
Proof.
  intros p d col wfp.
  pose (H := Domino.rm_iff_mem p (pose_domino d p) d eq_refl).
  destruct H as (H1 & H2).
  case_eq d;
      intros c rw_d;
      rewrite rw_d in H1, H2;
      unfold pose_domino;
      case col;
      simpl in *;
      case (bl_or_no c);
      intro col_c.
  {
    pose (H := dessous_inv_col Blanc c).
    destruct H as (H & HH). clear HH.
    pose (col_d_c := H col_c).
    assert (couleur_case Noir (dessous c)); auto.
    clear col_d_c.
    rewrite retire_case_neg1; auto.
    rewrite <- Nat.add_1_r.
    symmetry.
    auto using (retire_case Blanc).
  }
  {
    rewrite <- Nat.add_1_r.
    rewrite (retire_case Blanc); auto with lemmas_hints.
    + simpl.
      rewrite (retire_case_neg1 c);
      auto.
    + apply (wf_minus p wfp c).
    +
      apply dessous_inv_col in col_c.
      auto.
  }
  {
    pose (H := dessous_inv_col Blanc c).
    destruct H as (H & HH). clear HH.
    pose (col_d_c := H col_c).
    assert (couleur_case Noir (dessous c)); auto with lemmas_hints.
    clear col_d_c.
    rewrite <- Nat.add_1_r.
    symmetry.
    rewrite (retire_case Noir); auto with lemmas_hints.
    apply (wf_minus p wfp c).
  }
  {
    rewrite <- Nat.add_1_r.
    rewrite (retire_case_neg2).
    assert (col_d_c := col_c).
    apply dessous_inv_col in col_d_c.
    rewrite (retire_case Noir); auto.
    apply dessous_inv_col in col_c.
    auto.
  }
  {
    pose (H := droite_inv_col Blanc c).
    pose (col_d_c := H col_c).
    assert (couleur_case Noir (droite c)); auto.
    clear col_d_c.
    rewrite retire_case_neg1; auto.
    rewrite <- Nat.add_1_r.
    symmetry.
    auto using (retire_case Blanc).
  }
  {
    rewrite <- Nat.add_1_r.
    rewrite (retire_case Blanc); auto with lemmas_hints.
    + simpl.
      rewrite (retire_case_neg1 c);
      auto.
    + apply (wf_minus p wfp c).
    + apply droite_inv_col in col_c.
      auto.
  }
  {
    pose (H := droite_inv_col Blanc c).
    pose (col_d_c := H col_c).
    assert (couleur_case Noir (droite c)); auto.
    clear col_d_c.
    rewrite <- Nat.add_1_r.
    symmetry.
    rewrite (retire_case Noir); auto with lemmas_hints.
    apply (wf_minus p wfp c).
  }
  {
    rewrite <- Nat.add_1_r.
    rewrite (retire_case_neg2).
    assert (col_d_c := col_c).
    apply droite_inv_col in col_d_c.
    rewrite (retire_case Noir); auto.
    apply droite_inv_col in col_c.
    auto.
  }
Qed.

(** retirer [N] dominos = retirer [N] cases [blanches|noires] *)
Lemma rm_add_b :
  forall p col dl,
  well_formed p ->
  (disjoints_dominos dl) ->
  card col p = card col (pose_dominos dl p) + length dl.
Proof.
  induction dl.
  { simpl. trivial. }
  { intros wfp disj.
    simpl.
    rewrite rw_util3.
    rewrite rw_util4.
    set (p' := (pose_dominos dl p)).
    rewrite IHdl.
    cut (forall a b c, a = c + 1 -> a + b = c + S b).
    + intro min_b_both_sides.
      apply min_b_both_sides.
      rewrite Nat.add_1_r.
      rewrite (retire_domino p' a).
      reflexivity.
      apply (wf_minus_dl p wfp).
    + lia.
    + assumption.
    + now apply (simp_disjlo1 a).
    + now apply (simp_disjlo2 a).
  }
Qed.
