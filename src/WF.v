Require Import Domino Disjoint.
Require Import Arith_aux.
Require Import List.
Import ListNotations.

(** l'occurence de chaque case est égale à 1
    <-> éléments de [p] sont uniques *)
Fixpoint well_formed (p : plateau) :=
  match p with
  | [] => True
  | hd::tl => List.count_occ eq_coord p hd = 1 /\ well_formed tl
  end.

(*****************************************************************************************)
(********************************** { Lemmes (WF) } **************************************)
(*****************************************************************************************)

Lemma easy_occ :
  forall p a, well_formed (a::p) -> count_occ eq_coord p a = 0.
Proof.
  induction p.
  trivial.
  intros a0 H.
  case (eq_coord a a0).
  { intro e.
    rewrite e in H.
    simpl in H.
    case (eq_coord a0 a0); intro e2.
    - rewrite eq_rw in H.
      rewrite eq_rw in H.
      destruct H.
      apply arith in H.
      discriminate.
    - contradiction. }
  { intro e.
    apply count_occ_not_In.
    destruct H.
    rewrite count_occ_cons_eq in H.
    apply arith in H.
    apply count_occ_not_In in H.
    - assumption.
    - auto. }
Qed.

Lemma list_aux2 :
  forall (a a0 : coord) p, a <> a0 -> In a0 (a :: p) -> In a0 p.
Proof.
  intros a a0 p.
  revert a a0.
  induction p; intros; simpl.
  { elim H.
    unfold In in H0.
    destruct H0.
    assumption.
    exfalso.
    assumption. }
  { unfold In in H0.
    destruct H0.
    + contradiction.
    + destruct H0; auto. }
Qed.

Lemma list_aux3 :
  forall (a a0 : coord) p, In a0 p -> a <> a0 -> In a0 (a :: p).
Proof.
  intros a a0 p.
  revert a a0.
  induction p; intros; simpl.
  { destruct H. }
  { right.
    destruct H; auto. }
Qed.

Lemma list_aux : forall p a c, ~ In a p -> ~ In a (p\c).
Proof.
  induction p; simpl; trivial.
  intros a0 c H1 H2.
  elim H1.
  case (eq_coord a a0).
  { intro e. left. trivial. }
  { intro ne. right.
    case (eq_coord c a); intro e.
    + rewrite e in H2. rewrite eq_rw in H2.
      set (pp := List.in_remove eq_coord p a0 a).
      destruct pp; assumption.
    + rewrite eq_rw2 in H2.
      apply (list_aux2 a a0 p); try assumption.
      * apply list_aux2 in H2.
        - apply in_remove in H2.
          destruct H2.
          apply list_aux3; assumption.
        - assumption.
      * assumption. }
Qed.

Lemma occ_arith : forall p a c,
   c <> a ->
   count_occ eq_coord p a = 0 ->
   S (count_occ eq_coord (p\c) a) = 1.
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
      case (eq_coord c c); intro eq2; try contradiction.
      apply IHp.
      unfold well_formed.
      unfold well_formed in wf.
      destruct wf.
      assumption.
    + simpl.
      case (eq_coord c a); intro eq2.
      - congruence.
      - unfold well_formed.
        split.
        ++ simpl.
           case (eq_coord a a); intro eq3; try contradiction.
           assert (wfcp := wf).
           unfold well_formed in wf.
           destruct wf.
           set (xx := easy_occ p a wfcp).
           apply occ_arith; assumption.
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
    auto.
Qed.

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

Fixpoint sublist (pp p : plateau) :=
  match pp with
  | [] => True
  | h::t => In h p /\ sublist t (p\h)
  end.

Lemma sub_empty : forall b, sublist b [] -> b = [].
Proof.
  induction b.
  - trivial.
  - intro H.
    destruct H.
    destruct H.
Qed.

Lemma sub_in_trans: forall a b c, In a b -> sublist b c -> In a c.
Admitted.

Lemma sub_notin_contra : forall pp p a, sublist pp p -> ~ In a p -> ~ In a pp.
Proof.
  intros pp p a H1 H2 H3.
  apply H2.
  apply (sub_in_trans a pp p); assumption.
Qed.

Lemma wf_minus_ll :
  forall p pp, well_formed p -> sublist pp p -> well_formed pp.
Proof.
  intros p pp.
  revert p.
  induction pp.
  - auto.
  - intros p H H0.
    destruct H0 as (H01, H02).
    set (HH := IHpp (p\a) (wf_minus p H a) H02).
    cut (~ In a pp).
    + intro H2.
      split.
      * rewrite count_occ_cons_eq.
        -- apply arith.
           apply count_occ_not_In.
           assumption.
        -- reflexivity.
      * assumption.
    + apply (sub_notin_contra pp (p\a) a H02).
      apply remove_In.
Qed.

Lemma sub_refl : forall a, well_formed a -> sublist a a.
Proof.
  induction a.
  - auto.
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

(** un des deux lemmes dont je n'ai pas terminé la preuve *)
Lemma sub_trans : forall a b c, well_formed a -> sublist a b -> sublist b c -> sublist a c.
Admitted.

Lemma rw_wf_in : forall p a, well_formed (a :: p) -> p \ a = p.
Proof.
  induction p.
  - auto.
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
  { auto. }
  { intros d H.
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
        - apply in_eq.
        - simpl. rewrite eq_rw.
          rewrite (rw_wf_in p a); try assumption.
          destruct (IHp d); try apply (wf_minus_hd p a H).
          assumption.
    * unfold sublist.
      split.
      + simpl; right; left; trivial.
      + simpl.
        case (eq_coord d a); intro eq; rewrite eq_rw.
        - rewrite eq. rewrite eq_rw.
           rewrite rw_wf_in.
           simpl.
           apply sub_refl.
           ++ apply (wf_minus_hd p a H).
           ++ assumption.
        - rewrite eq_rw2.
           ++ rewrite rw_wf_in; try assumption.
              set (H3 := IHp d (wf_minus_hd p a H)).
              destruct H3.
              assumption.
           ++ auto. }
Qed.

Lemma sublemma : forall d p, well_formed p -> sublist (d // p) p.
Proof.
  destruct d; intros; unfold pose_domino; simpl.
  { set (H1 := sub_cor p c).
    destruct H1; try assumption.
    set (H2 := sub_cor (p\c) (dessous c)).
    destruct H2.
    apply (wf_minus p H c).
    set (wfp_c_dc := wf_minus (p\c) (wf_minus p H c) (dessous c)).
    apply (sub_trans (p\c\dessous c) (p\c) p wfp_c_dc H2 H0). }
  { set (H1 := sub_cor p c).
    destruct H1; try assumption.
    set (H2 := sub_cor (p\c) (droite c)).
    destruct H2.
    apply (wf_minus p H c).
    set (wfp_c_dc := wf_minus (p\c) (wf_minus p H c) (droite c)).
    apply (sub_trans (p\c\droite c) (p\c) p wfp_c_dc H2 H0). }
Qed.

Lemma wf_minus_d :
  forall p, well_formed p -> forall d, well_formed (d // p).
Proof.
  intros p H d.
  cut (sublist (d // p) p).
  + now apply wf_minus_ll.
  + now apply sublemma.
Qed.

Lemma rw12 : forall dl a p,
  (fold_left (fun (p0 : plateau) (d : domino) => d // p0) dl (a // p)) = pose_dominos dl (a // p).
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
  apply (IHdl (a // p)).
  eapply wf_minus_d.
  assumption.
Qed.
