Require Import Arith Nat List Lia.
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

Eval compute in mk_plateau 8.

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

(** Les listes sont un "modèle" pour un ensemble, on peut supposer le lemme suivant : *)
Hypothesis remove_hd : forall c p, (c :: p) \ c = p.

(** Plateau du problème : échiquier classique sans 1 pair de coins opposés *)
Definition plateau_coupe := plateau_base \ {| x := 7; y := 7|} \ {| x := 0; y := 0|}.

Eval compute in plateau_coupe.

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
  (In (fst (case_prise d)) p /\ In (snd (case_prise d)) p) .

Definition mk_domino_H (x y : nat) := Hauteur {| x := x ; y := y |}.
Definition mk_domino_L (x y : nat) := Largeur {| x := x ; y := y |}.

Eval compute in pose_domino (mk_domino_H 4 4) plateau_coupe.

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


(* Definition disjoints_dominos_lo (dl : list domino) :=
  forall d, In d dl -> d ## (List.remove eq_domino d dl). *)

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

(*****************************************************************************************)
(***************************** { Critère de résolubilité  } ******************************)
(*****************************************************************************************)

(** une liste de dominos « résout » un plateau si une fois que l'on les a tous posé,
    la liste représentant le plateau est vide *)
Definition solution (p : plateau) (dl : list domino) :=
  pose_dominos dl p = [].

(* Print List. *)
Fixpoint well_formed (p : plateau) :=
  match p with
  | [] => True
  | hd::tl => List.count_occ eq_coord p hd = 1 /\ well_formed tl
  end.

(** un définition possible de la résolubilité d'un plateau
    un plateau est résoluble s'il existe un liste de domino
    telle que lorsque les domino seront posés le plateau sera vide *)
Definition resoluble (p : plateau) :=
  well_formed p /\
  exists dl : list domino, solution p dl /\ disjoints_dominos_lo dl.


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
(********************************** { Lemmes (WF) } **************************************)
(*****************************************************************************************)


Lemma arith : forall a, a = 0 <-> S a = 1. Proof. lia. Qed.

Lemma easy_occ :
  forall p a, well_formed (a::p) -> count_occ eq_coord (a :: p) a = 1 -> count_occ eq_coord p a = 0.
Proof.
  induction p.
  trivial.
  intros a0 wf H.
  case (eq_coord a a0).
  - intro e.
    rewrite e in H.
    simpl in H.
    case (eq_coord a0 a0); intro e2.
    -- rewrite eq_rw in H.
       rewrite eq_rw in H.
       apply arith in H.
       discriminate.
    -- contradiction.
  - intro e.
    unfold well_formed in wf.
    destruct wf.
    apply count_occ_not_In.
    simpl in H0.
    rewrite eq_rw in H0.
    apply arith in H0.
    rewrite eq_rw2 in H0; try assumption.
    apply count_occ_not_In in H0.
    apply not_in_cons.
    auto.
Qed.

Lemma list_aux2 :
  forall (a a0 : coord) p, a <> a0 -> In a0 (a :: p) -> In a0 p.
Proof.
  intros a a0 p.
  revert a a0.
  induction p; intros; simpl.
  - elim H.
    unfold In in H0.
    destruct H0.
    assumption.
    exfalso.
    assumption.
  - unfold In in H0.
    destruct H0.
    + contradiction.
    + destruct H0.
      * left. assumption.
      * right. assumption.
Qed.

Lemma list_aux3 :
  forall (a a0 : coord) p, In a0 p -> a <> a0 -> In a0 (a :: p).
Proof.
  intros a a0 p.
  revert a a0.
  induction p; intros; simpl.
  - destruct H.
  - right.
    destruct H.
    + left. assumption.
    + right. assumption.
Qed.

Lemma list_aux : forall p a c, ~ In a p -> ~ In a (p\c).
Proof.
  induction p; simpl; trivial.
  intros a0 c H1 H2.
  elim H1.
  case (eq_coord a a0).
  - intro. left. trivial.
  - intro. right.
    case (eq_coord c a); intro.
    + rewrite e in H2. rewrite eq_rw in H2.
      set (pp := List.in_remove eq_coord p a0 a).
      destruct pp; assumption.
    + rewrite eq_rw2 in H2.
      apply (list_aux2 a a0 p); try assumption.
      * apply list_aux2 in H2.
        ** apply in_remove in H2.
           destruct H2.
           apply list_aux3; assumption.
        ** assumption.
      * assumption.
Qed.

Lemma occ_arith: forall p a c,
   c <> a -> count_occ eq_coord p a = 0 -> S (count_occ eq_coord (p\c) a) = 1.
Proof.
  intros p a c H1 H2.
  apply arith.
  apply count_occ_not_In in H2.
  apply count_occ_not_In.
  apply list_aux.
  assumption.
Qed.

Lemma wf_minus :
  forall p, well_formed p -> forall c, well_formed (p \ c).
Proof.
  induction p.
  { simpl. trivial. }
  { intros wf c.
    case (eq_coord a c); intro eq.
    + rewrite eq.
      simpl.
      case (eq_coord c c); intro eq2.
      * apply IHp.
        unfold well_formed.
        unfold well_formed in wf.
        destruct wf.
        assumption.
      * contradiction.
    + simpl.
      case (eq_coord c a); intro eq2.
      - congruence.
      - unfold well_formed.
         split.
         ++ simpl.
            case (eq_coord a a); intro eq3.
            ** assert (wfcp := wf).
               unfold well_formed in wf.
               destruct wf.
               eapply easy_occ in H.
               apply occ_arith; assumption.
               assumption.
            ** contradiction.
         ++ apply IHp.
          unfold well_formed in wf.
          destruct wf.
          assumption. }
Qed.

Lemma wf_minus_hd :
  forall p a, well_formed (a :: p) -> well_formed p.
Proof.
  induction p.
  + simpl.
    split.
  + intros a0 wf.
    unfold well_formed.
    unfold well_formed in wf.
    destruct wf as (h1, (h2, h3)).
    split; assumption.
Qed.

(* Lemma wf_minus_hd2 :
  forall p a, ~ In a p -> well_formed (a :: (p\a)) -> well_formed p.
Proof.
  induction p.
  + simpl.
    split.
  + intros a0 nin wf.
    unfold well_formed.
    unfold well_formed in wf.
    destruct wf.
    split.
Qed. *)

Lemma rw10 : forall x p, (x :: p) \ x = p \ x.
Proof.
  intros x p.
  revert x.
  induction p; intro x0; simpl;
  rewrite eq_rw; reflexivity.
Qed.

Lemma rw11 : forall x y p, x <> y -> (y :: p) \ x = y :: (p \ x).
Proof.
  intros x y p neq.
  revert x y neq.
  induction p; intros x0 y0 neq; simpl;
  case (eq_coord x0 y0); trivial; congruence.
Qed.

Print List.

Fixpoint sublist (pp p : plateau) :=
  match pp with
  | [] => True
  | h::t => In h p /\ sublist t (p\h)
  end.

Lemma wf_minus_ll :
  forall p pp, well_formed p -> sublist pp p -> well_formed pp.
Proof.
  intros p pp.
  revert p.
  induction pp.
  - intros. auto.
  - intros.
    unfold sublist in H0.
    destruct H0 as (H01, H02).
    set (HH := IHpp (p\a) (wf_minus p H a) H02).
  Admitted.

Lemma sub_refl : forall a, well_formed a -> sublist a a.
Proof.
  induction a.
  - simpl. trivial.
  - simpl.
    split.
    + left; reflexivity.
    + rewrite eq_rw.
      rewrite eq_rw in H.
      destruct H.
      apply arith in H.
      apply count_occ_not_In in H.
      rewrite notin_remove.
      apply IHa.
      assumption.
      assumption.
Qed.

Lemma sub_rm : forall p p' a, sublist p p' -> sublist (p\a) (p'\a).
Proof.
  (* induction p.
  - simpl. trivial.
  - intros. *)
Admitted.


Lemma sub_trans : forall a b c, well_formed a -> sublist a b -> sublist b c -> sublist a c.
Proof.
  induction a.
  { intros. trivial. }
  { intros b c wf H H0.
    simpl.
    split.
    cut (sublist (a :: a0) b -> In a b).
    - intro.
      cut (In a b -> sublist b c -> In a c).
      -- intros. apply H2. apply H1. assumption. assumption.
      -- intros. admit.
    - intros. admit.
    - apply (IHa (b\a) (c\a)).
      + apply (wf_minus_hd a0 a wf).
      + admit.
      + apply sub_rm. assumption.
  }
Admitted.

Lemma rw_wf_in : forall p a, well_formed (a :: p) -> p \ a = p.
Proof.
  induction p.
  - simpl; trivial.
  - intros a0 wf.
    destruct wf.
    rewrite count_occ_cons_eq in H; trivial.
    apply arith in H.
    apply count_occ_not_In in H.
    apply notin_remove.
    assumption.
Qed.

Lemma sub_cor : forall p d, well_formed p -> sublist (p \ d) p /\ sublist p (d::p).
Proof.
  induction p.
  - simpl. intro. split; trivial.
  - intros.
    destruct (IHp a) as (IH1, IH2).
    apply (wf_minus_hd p a H).
    split.
    * case (eq_coord d a); intro eq.
      + rewrite eq.
        simpl.
        rewrite eq_rw.
        apply (sub_trans (p\a) p (a::p)); try assumption.
        apply (wf_minus p (wf_minus_hd p a H) a).
      + simpl.
        rewrite eq_rw2; try assumption.
        unfold sublist.
        split.
        -- apply in_eq.
        -- simpl. rewrite eq_rw.
           rewrite (rw_wf_in p a); try assumption.
           destruct (IHp d); try apply (wf_minus_hd p a H).
           assumption.
    * unfold sublist.
      split.
      + simpl; right; left; trivial.
      + simpl.
        case (eq_coord d a); intro eq; rewrite eq_rw.
        -- rewrite eq. rewrite eq_rw.
           rewrite rw_wf_in.
           simpl.
           apply sub_refl.
           --- apply (wf_minus_hd p a H).
           --- assumption.
        -- rewrite eq_rw2.
           ++ rewrite rw_wf_in; try assumption.
              set (H3 := IHp d (wf_minus_hd p a H)).
              destruct H3.
              assumption.
           ++ intro. apply eq. symmetry. assumption.
Qed.

Lemma sublemma : forall d p, well_formed p -> sublist (pose_domino d p) p.
Proof.
  destruct d; intros; unfold pose_domino; simpl.
  - set (H1 := sub_cor p c).
    destruct H1; try assumption.
    set (H2 := sub_cor (p\c) (dessous c)).
    destruct H2.
    apply (wf_minus p H c).
    set (wfp_c_dc := wf_minus (p\c) (wf_minus p H c) (dessous c)).
    apply (sub_trans (p\c\dessous c) (p\c) p wfp_c_dc H2 H0).
  - set (H1 := sub_cor p c).
    destruct H1; try assumption.
    set (H2 := sub_cor (p\c) (droite c)).
    destruct H2.
    apply (wf_minus p H c).
    set (wfp_c_dc := wf_minus (p\c) (wf_minus p H c) (droite c)).
    apply (sub_trans (p\c\droite c) (p\c) p wfp_c_dc H2 H0).
Qed.

Lemma wf_minus_d :
  forall p, well_formed p -> forall d, well_formed (pose_domino d p).
Proof.
  intros.
  cut (sublist (pose_domino d p) p).
  + apply wf_minus_ll. assumption.
  + apply sublemma. assumption.
Qed.

Lemma rw12 : forall dl a p,
  (fold_left (fun (p0 : plateau) (d : domino) => pose_domino d p0) dl
     (pose_domino a p)) = pose_dominos dl (pose_domino a p).
Proof.
  reflexivity.
Qed.

Lemma wf_minus_dl :
  forall p, well_formed p -> forall dl, well_formed (pose_dominos dl p).
Proof.
  unfold pose_dominos.
  intros p wfp dl.
  revert p wfp.
  induction dl; trivial.
  intros p wfp.
  set (wfpdl := IHdl p wfp).
  unfold well_formed.
  simpl.
  rewrite rw12.
  apply (IHdl (pose_domino a p)).
  eapply wf_minus_d.
  assumption.
Qed.

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

(** la couleur d'une case est [Blanc] ou [Noir] *)
Lemma bl_or_no : forall c: coord, couleur_case Blanc c \/ couleur_case Noir c.
Proof.
  intro.
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

(** si on a deux cases différentes, les opérations [ajoute] et [retire] commutent *)
Lemma rw_util col (a c : coord) (p : plateau) :
  a <> c -> card col (a :: (p \ c)) = card col ((a :: p) \ c).
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

(** Si on a une case blanche et qu'on l'ajoute à un plateau
    alors le nombre de cases blanches du plateau augmente de 1 *)
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

(** si [a] est une case de couleur [col],
    alors [a] ne pèse pas dans le compte des cases de couleurs [neg col] *)
Lemma cons_card_neq col a p :
  couleur_case col a ->
  card (neg_couleur col) (a :: p) = card (neg_couleur col) p.
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

(** ajouter la même case à deux plateau ne change rien
    à l'égalité entre les comptes de couleurs *)
Lemma card_eq_hdS col a p p' :
  card col p + 1 = card col p' ->
  card col (a :: p) + 1 = card col (a :: p').
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

Hint Resolve retire_case.

(** si on retire une case de la couleur que l'on ne compte pas
    alors le compte n'a pas changé *)
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

Hint Resolve retire_case_neg1.

(** si on retire une case de la couleur que l'on ne compte pas
    alors le compte n'a pas changé *)
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

Hint Resolve retire_case_neg2.

(** l'opération [remove] est commutative *)
Lemma remove_comm (p : plateau) (a b : coord) : p \ a \ b = p \ b \ a.
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
  { apply_lemmas (Nat.Even (x c + y c)) H0 (retire_case_neg1 (dessous c) (p\c)).
    apply (retire_case Blanc c p wfp).
    - trivial.
    - destruct (rm_iff_mem p p' (Hauteur c)); trivial.
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
    destruct (rm_iff_mem p p' (Hauteur c)); trivial. }
  { apply_lemmas (Nat.Even (x c + y c)) H0 (retire_case_neg1 (droite c) (p\c)).
    apply (retire_case Blanc c p wfp); simpl; trivial.
    apply (rm_iff_mem p p' (Largeur c)); trivial. trivial. }
  { clear H0.
    assert (H2_cpy : Nat.Odd (x c + y c)); trivial.
    apply H1 in H2_cpy.
    unfold pose_domino.
    simpl.
    rewrite remove_comm.
    rewrite (retire_case_neg1 c (p \ droite c)); trivial.
    symmetry.
    apply (retire_case Blanc (droite c) p wfp); simpl; trivial.
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
Lemma in_simp2_droite c p : In c p -> In c (p \ droite c).
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
Lemma in_simp2 c p : In c p -> In c (p \ dessous c).
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
Lemma in_simp_droite c p : In (droite c) p -> In (droite c) (p \ c).
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
Lemma in_simp c p : In (dessous c) p -> In (dessous c) (p \ c).
Proof.
  intro.
  apply List.in_in_remove.
  - intro.
    eapply case_diff_dessous with c.
    symmetry.
    assumption.
  - assumption.
Qed.

Hint Resolve in_simp.
Hint Resolve in_simp2.
Hint Resolve in_simp_droite.
Hint Resolve in_simp2_droite.

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
      apply (rm_iff_mem p p' (Hauteur c)).
      trivial.
    - unfold case_blanche. assumption. }
  { apply_lemmas_l (Nat.Odd (x c + y c)) H1 (retire_case_neg2 (dessous c) p).
    rewrite remove_comm.
    apply (retire_case Noir c (p\dessous c)); simpl; trivial.
    - apply (wf_minus p wfp (dessous c)).
    - apply in_simp2.
      apply (rm_iff_mem p p' (Hauteur c)).
      trivial.
    - unfold case_blanche. assumption. }
  { apply_lemmas_l (Nat.Even (x c + y c)) H0 (retire_case_neg2 c p).
    apply (retire_case Noir (droite c) (p\c)); simpl; trivial.
    - apply (wf_minus p wfp c).
    - apply in_simp_droite.
      apply (rm_iff_mem p p' (Largeur c)).
      trivial.
    - unfold case_blanche. assumption. }
  { apply_lemmas_l (Nat.Odd (x c + y c)) H1 (retire_case_neg2 (droite c) p).
    rewrite remove_comm.
    apply (retire_case Noir c (p\droite c)); simpl; trivial.
    - apply (wf_minus p wfp (droite c)).
    - apply in_simp2_droite.
      apply (rm_iff_mem p p' (Largeur c)).
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
  intros.
  case d1, d2;
  unfold disjoints_dominos in H;
  destruct H;
  destruct H0;
  destruct H1;
  auto.
Qed.

Hint Resolve remove_comm.

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
    intros.
    destruct d1, d2;
    unfold pose_domino;
    simpl;
    unfold disjoints_dominos in H;
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
  intros.
  destruct d1, d2;
  unfold disjoints_dominos in *;
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
  pose (H := rm_iff_mem p (pose_domino d p) d eq_refl).
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
    rewrite (retire_case Blanc); auto.
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
    assert (couleur_case Noir (dessous c)); auto.
    clear col_d_c.
    rewrite <- Nat.add_1_r.
    symmetry.
    rewrite (retire_case Noir); auto.
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
    rewrite (retire_case Blanc); auto.
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
    rewrite (retire_case Noir); auto.
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
  (disjoints_dominos_lo dl) ->
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
    + apply (simp_disjlo1 a). assumption.
    + apply (simp_disjlo2 a). assumption.
  }
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
