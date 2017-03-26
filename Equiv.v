Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.

Import ListNotations.

Require Import SfLib.
Require Import Maps.
Require Import Imp.

Definition aequiv  (a1 a2: aexp) : Prop :=
  forall st,
    aeval st a1 = aeval st a2.
Definition bequiv (b1 b2: bexp) : Prop :=
  forall st,
    beval st b1 = beval st b2.

Definition cequiv (c1 c2:com) : Prop :=
  forall st st',
    c1 / st \\ st' <-> c2 / st \\ st'.

Example aequiv_example:
  aequiv (AMinus (AId X) (AId X)) (ANum 0).

unfold aequiv. intros. simpl. omega.
Qed.

Theorem skip_left :
  forall c,
    cequiv (SKIP;;c)
           c.
  intro. unfold cequiv. split.
  intros. inversion H. inversion H2. auto.
  intros. eapply E_Seq. apply E_Skip. auto.
Qed.


Theorem skip_right:
  forall c,
    cequiv (c;;SKIP)
           c.
  unfold cequiv. split.
  intros. inversion H. inversion H5. rewrite H8 in H2. auto.
  intros. eapply E_Seq. apply H. apply E_Skip.
Qed.


Theorem IFB_true_simple :
  forall c1 c2,
    cequiv (IFB BTrue THEN c1 ELSE c2 FI)
           c1.
  unfold cequiv. split.
  intros. inversion H; auto. simpl in H5. discriminate.
  intros. apply E_IfTrue. auto. apply H.
Qed.


Theorem IFB_true :
  forall b c1 c2,
    bequiv b BTrue ->
    cequiv (IFB b THEN c1 ELSE c2 FI)
           c1.

  split. intros.
  inversion H0; auto. unfold bequiv in H. pose (H st). rewrite H6 in e. simpl in e. discriminate.
  intros. apply E_IfTrue. pose (H st). simpl in e; auto.
  auto.
Qed.

Theorem swap_if_branches:
  forall b e1 e2,
    cequiv (IFB b THEN e1 ELSE e2 FI)
           (IFB BNot b THEN e2 ELSE e1 FI).
  unfold cequiv.
  intros until st.
  destruct (beval st b) eqn: b1.
  split. intros. inversion H. apply E_IfFalse. simpl. rewrite H5. auto. auto.
  apply E_IfTrue. simpl. rewrite H5. auto. auto.
  intros. inversion H. simpl in H5. rewrite b1 in H5. simpl in H5. discriminate.
  apply E_IfTrue. auto. auto.
  split. intros. apply E_IfTrue. simpl; rewrite b1; auto. inversion H. rewrite b1 in H5; discriminate.
  auto.
  intros. apply E_IfFalse. auto. inversion H; auto. simpl in H5; rewrite b1 in H5; simpl in H5; discriminate.
Qed.


Theorem WHILE_false :
  forall b c,
    bequiv b BFalse ->
    cequiv (WHILE b DO c END)
           SKIP.

  intros. split. intros. pose (H st). simpl in e. inversion H0. rewrite e in H3; discriminate.
  apply E_Skip.
  intros. inversion H0. apply E_WhileEnd. pose (H st). simpl in e; subst st'; auto.
Qed.


Lemma WHILE_true_nonterm :
  forall b c st st',
    bequiv b BTrue ->
    ~( (WHILE b DO c END) / st \\ st').
  unfold not. intros. remember (WHILE b DO c END) as h. generalize Heqh.
  elim H0; try (simpl; intros; discriminate).
  intros. auto.
  intros. inversion Heqh0; subst b0.
  pose (H st0). simpl in e. rewrite e in H1. discriminate.
Qed.

Theorem WHILE_true :
  forall b c,
    bequiv b BTrue ->
    cequiv (WHILE b DO c END)
           (WHILE BTrue DO SKIP END).
  split. intros. pose (WHILE_true_nonterm b c st st'). elim (n H H0).
  intros. pose (WHILE_true_nonterm BTrue SKIP st st'). unfold bequiv in n.
  assert (False). apply n. intros; auto. auto. elim H1.
Qed.

Theorem seq_assoc :
  forall c1 c2 c3,
    cequiv ((c1 ;; c2) ;; c3)
           (c1 ;; (c2 ;; c3)).

  split. intros. inversion H. inversion H2. eapply E_Seq. apply H8. eapply E_Seq. apply H11. auto.
  intros. inversion H. inversion H5. eapply E_Seq. eapply E_Seq. apply H2. apply H8. apply H11.
Qed.

Theorem identity_assignment :
  forall (X:id),
    cequiv (X ::= AId X)
           SKIP.

  split. intros. inversion H.
  assert (st = t_update st X n).
  apply functional_extensionality.
  intro. unfold t_update.
  case (eq_id_dec X x0). intros. simpl in H4. subst x0. auto.
  auto. pattern st at 1. rewrite H5. apply E_Skip.
  intros. inversion H.
  assert (st' = t_update st' X (aeval st' (AId X))).
  apply functional_extensionality.
  intro; unfold t_update.
  case (eq_id_dec X x). simpl. intros; subst x; auto.
  auto.
  pattern st' at 2. rewrite H0. eapply E_Ass. auto.
Qed.




Theorem symm_cequiv:
  forall a b,
    cequiv a b <-> cequiv b a.
  unfold cequiv.
  intros. split; intros. split; apply (H st st').
  split; apply (H st st').
Qed.

Theorem assign_aequiv:
  forall X e,
    aequiv (AId X) e ->
    cequiv SKIP (X ::= e).
  intros. split; intros.
  pose (identity_assignment X).
  unfold cequiv in c. pose (c st st'). destruct i.
  pose (H2 H0). inversion c0. pose (H st). rewrite e0 in H7. rewrite <- H7.
  apply E_Ass. auto.
  apply (identity_assignment X). pose (H st).
  inversion H0. apply E_Ass. subst n; auto.
Qed.

Lemma refl_aequiv :
  forall a,
    aequiv a a.
  split.
Qed.


Lemma sym_aequiv:
  forall a1 a2,
    aequiv a1 a2 <-> aequiv a2 a1.
  split; intros;unfold aequiv; intros st; pose (H st); auto.
Qed.

Lemma trans_aequiv:
  forall a1 a2 a3,
    aequiv a1 a2 ->
    aequiv a2 a3 ->
    aequiv a1 a3.
  intros. unfold aequiv. intro. pose (H st); pose (H0 st). rewrite e; rewrite e0; auto.
Qed.


Lemma refl_bequiv:
  forall b,
    bequiv b b.
  split.
Qed.

Lemma symm_bequiv:
  forall b1 b2,
    bequiv b1 b2 -> bequiv b2 b2.
  unfold bequiv. intros. symmetry in H. auto.
Qed.


Lemma tran_bequiv:
  forall b1 b2 b3,
    bequiv b1 b2 ->
    bequiv b2 b3 ->
    bequiv b1 b3.
  unfold bequiv.
  intros.
  rewrite H; rewrite H0; auto.
Qed.


Lemma refl_cequiv:
  forall c,
    cequiv c c.
  split; auto.
Qed.


Lemma trans_cequiv :
  forall c1 c2 c3,
    cequiv c1 c2 ->
    cequiv c2 c3 ->
    cequiv c1 c3.

  unfold cequiv.
  split; intros.
  apply H0. apply H; auto.
  apply H. apply H0 ;auto.
Qed.


Theorem CAss_congruence :
  forall i a1 a1',
    aequiv a1 a1' ->
    cequiv (CAss i a1) (CAss i a1').
  split; intros.
  inversion H0. apply E_Ass. pose (H st). rewrite <- e. auto.
  inversion H0. apply E_Ass. pose (H st). rewrite e. auto.
Qed.

Theorem CWhile_congruence:
  forall b1 b1' c1 c1',
         bequiv b1 b1' ->
         cequiv c1 c1' ->
         cequiv (WHILE b1 DO c1 END)
                (WHILE b1' DO c1' END).

  split; intros. generalize dependent b1'. generalize dependent c1'.
  remember (WHILE b1 DO c1 END) as h1. generalize dependent Heqh1.
  elim H1; try (simpl; intros; discriminate).
  intros. pose (H4 Heqh1 c1' H5 b1' H6).
  eapply E_WhileLoop. inversion Heqh1. pose (H6 st0). rewrite <- e. rewrite <- H8. auto.
  inversion Heqh1. apply H5. rewrite <- H9. apply H0. apply c0.
  intros. pose (H2 st0). inversion Heqh1. subst b1. rewrite H in e. apply E_WhileEnd. auto.
  generalize dependent b1. generalize dependent c1.
  remember (WHILE b1' DO c1' END) as h1.
  generalize Heqh1. elim H1; try (simpl; intros; discriminate).
  intros. inversion Heqh0. pose (H4 Heqh0 c1 H5 b1 H6).
  eapply E_WhileLoop. rewrite H6. rewrite <- H8. auto.
  apply H5. rewrite <- H9. apply H0. auto.
  intros. apply E_WhileEnd. rewrite H2. inversion Heqh0. subst b1'. auto.
Qed.

Theorem CSeq_congruence :
  forall c1 c1' c2 c2',
    cequiv c1 c1' ->
    cequiv c2 c2' ->
    cequiv (c1;;c2) (c1';;c2).
  split.
  intros. inversion H1. eapply E_Seq. apply H. apply H4. apply H7.
  intros. inversion H1. eapply E_Seq. apply H. apply H4. apply H7.
Qed.


Theorem CIf_congruence:
  forall b b' c1 c1' c2 c2',
    bequiv b b' ->
    cequiv c1 c1' ->
    cequiv c2 c2' ->
    cequiv (IFB b THEN c1 ELSE c2 FI)
           (IFB b' THEN c1' ELSE c2' FI).
  split; intros.
  inversion H2. apply E_IfTrue. pose (H st). rewrite <- e. auto.
  apply H0. auto.
  apply E_IfFalse. rewrite <- H. auto.
  apply H1. auto.
  inversion H2. apply E_IfTrue. rewrite H. auto. apply H0. auto.
  apply E_IfFalse. rewrite H. auto. apply H1. auto.
Qed.

Definition atrans_sound (atrans: aexp -> aexp) : Prop :=
  forall (a:aexp),
    aequiv a (atrans a).

Definition btrans_sound (btrans: bexp -> bexp) : Prop :=
  forall (b:bexp),
    bequiv b (btrans b).

Definition ctrans_sound (ctrans : com -> com) : Prop :=
  forall (c : com),
    cequiv c (ctrans c).

Fixpoint fold_constants_aexp (a:aexp) : aexp :=
  match a with
    | ANum n => ANum n
    | AId i => AId i
    | APlus a1 a2 =>
      match (fold_constants_aexp a1, fold_constants_aexp a2)
      with
        | (ANum n1, ANum n2) => ANum (n1 + n2)
        | (a1' , a2') => APlus a1' a2'
      end
    | AMinus a1 a2 =>
      match (fold_constants_aexp a1, fold_constants_aexp a2) with
        | (ANum n1, ANum n2) => ANum (n1 - n2)
        | (a1', a2') => AMinus a1' a2'
      end
    | AMult a1 a2 =>
      match (fold_constants_aexp a1, fold_constants_aexp a2) with
        | (ANum n1, ANum n2) => ANum (n1 * n2)
        | (a1', a2') => AMult a1' a2'
      end
  end.

Example fold_aexp_ex1 :
  fold_constants_aexp (AMult (APlus (ANum 1) (ANum 2)) (AId X))
  = AMult (ANum 3) (AId X).
simpl; auto.
Qed.

Print eq_nat_dec.
SearchPattern ({_}+{_}).

Fixpoint fold_constants_bexp (b:bexp) : bexp :=
  match b with
    | BTrue => BTrue
    | BFalse => BFalse
    | BEq a1 a2 =>
      match (fold_constants_aexp a1, fold_constants_aexp a2) with
        | (ANum n1, ANum n2) =>
          if (eq_nat_dec n1 n2) then BTrue else BFalse
        | (a1', a2') => BEq a1' a2'
      end
    | BLe a1 a2 =>
      match (fold_constants_aexp a1, fold_constants_aexp a2) with
        | (ANum n1, ANum n2) =>
          if (le_dec n1 n2) then BTrue else BFalse
        | (a1' ,a2') => BLe a1' a2'
      end
    | BNot b1 =>
      match (fold_constants_bexp b1) with
        | BTrue => BFalse
        | BFalse => BTrue
        | b1' => BNot b1'
      end
    | BAnd b1 b2 =>
      match (fold_constants_bexp b1, fold_constants_bexp b2) with
        | (BTrue, BFalse) => BFalse
        | (BTrue, BTrue) => BTrue
        | (BFalse, BTrue) => BFalse
        | (BFalse, BFalse) => BFalse
        | (b1', b2') => BAnd b1' b2'
      end
  end.

Fixpoint fold_constants_com (c:com) : com :=
  match c with
    | SKIP => SKIP
    | i ::= a => CAss i (fold_constants_aexp a)
    | c1 ;; c2 => (fold_constants_com c1);;(fold_constants_com c2)
    | IFB b THEN c1 ELSE c2 FI =>
      match fold_constants_bexp b with
        | BTrue => fold_constants_com c1
        | BFalse => fold_constants_com c2
        | b' => IFB b' THEN (fold_constants_com c1) ELSE (fold_constants_com c2) FI
      end
    | WHILE b DO c END =>
      match fold_constants_bexp b with
        | BTrue => WHILE BTrue DO SKIP END
        | BFalse => SKIP
        | b' => WHILE b' DO (fold_constants_com c) END
      end
  end.




Lemma fca_plus:
  forall a1 a2 st,
    aeval st (fold_constants_aexp (APlus a1 a2)) =
    aeval st (APlus (fold_constants_aexp a1) (fold_constants_aexp a2)).
  simpl. intros a1 a2. destruct (fold_constants_aexp a1) eqn: h1; destruct (fold_constants_aexp a2); try(simpl; auto; fail).
Qed.



Lemma fca_minus:
  forall a1 a2 st,
    aeval st (fold_constants_aexp (AMinus a1 a2)) =
    aeval st (AMinus (fold_constants_aexp a1) (fold_constants_aexp a2)).
  simpl. intros a1 a2. destruct (fold_constants_aexp a1) eqn: h1; destruct (fold_constants_aexp a2); try(simpl; auto; fail).
Qed.

Lemma fca_mult:
  forall a1 a2 st,
    aeval st (fold_constants_aexp (AMult a1 a2)) =
    aeval st (AMult (fold_constants_aexp a1) (fold_constants_aexp a2)).
  simpl. intros a1 a2. destruct (fold_constants_aexp a1) eqn: h1; destruct (fold_constants_aexp a2); try(simpl; auto; fail).
Qed.




Lemma aexp_plus_aplus:
  forall a1 a2 st,
    aeval st (APlus a1 a2) = aeval st a1 + aeval st a2.
  auto.
Qed.

Lemma aexp_minus_aminus:
  forall a1 a2 st,
    aeval st (AMinus a1 a2) = aeval st a1 - aeval st a2.
  auto.
Qed.

Lemma aexp_mult_amult:
  forall a1 a2 st,
    aeval st (AMult a1 a2) = aeval st a1 * aeval st a2.
  auto.
Qed.

Hint Rewrite aexp_plus_aplus aexp_minus_aminus aexp_mult_amult fca_plus fca_mult fca_minus : fca_rwbase.

Theorem fold_constants_aexp_sound :
  atrans_sound fold_constants_aexp.
  unfold atrans_sound.
  unfold aequiv.
  intro. elim a; try (auto); try (intros; autorewrite with fca_rwbase);rewrite H; rewrite H0; autorewrite with fca_rwbase; auto.
Qed.



Theorem fold_constants_bexp_sound :
  btrans_sound fold_constants_bexp.
  unfold btrans_sound. unfold bequiv.
  intro. elim b; try (simpl; auto; fail);
         try (intros; simpl; rewrite (fold_constants_aexp_sound a); rewrite (fold_constants_aexp_sound a0); destruct (fold_constants_aexp a); destruct (fold_constants_aexp a0); try (simpl; auto; fail));
         try (intros; simpl; try (rewrite H); try (rewrite H0); try (rewrite H1); destruct (fold_constants_bexp b0); try (destruct (fold_constants_bexp b1)); try (simpl; auto; fail); fail).
  unfold beq_nat_bydec; intros; simpl; case (eq_nat_dec n n0); simpl; auto.
  unfold leb_bydec; intros; simpl; case (le_dec n n0); simpl; auto.
Qed.



Theorem fold_constants_com_sound:
  ctrans_sound fold_constants_com.

  unfold ctrans_sound. unfold cequiv.
  intro. split; generalize dependent st; generalize dependent st'.
  elim c; try (simpl; auto; fail); intros.
  simpl. inversion H. rewrite (fold_constants_aexp_sound a) in H4. rewrite <- H4.
  apply E_Ass; auto.
  simpl. inversion H1. pose (H _ _ H4). pose (H0 _ _ H7). eapply E_Seq. apply c4. apply c5.
  inversion H1. pose (H _ _ H8). pose (fold_constants_bexp_sound b st).
  rewrite H7 in e; symmetry in e.
  simpl; destruct (fold_constants_bexp b) eqn:hh ; try (simpl; auto; fail);
  try (rewrite H7 in hh; discriminate); try (rewrite e; simpl; auto); try (simpl in e; discriminate); try (apply E_IfTrue; auto).
  pose (H0 _ _ H8). pose (fold_constants_bexp_sound b st).
  rewrite H7 in e; symmetry in e.
 simpl; destruct (fold_constants_bexp b) eqn:hh ; try (simpl; auto; fail);
 try (rewrite H7 in hh; discriminate); try (rewrite e; simpl; auto); try (simpl in e; discriminate); try (apply E_IfFalse; auto).
 clear c. remember (WHILE b DO c0 END) as h. generalize dependent Heqh. elim H0; try (simpl; intros; discriminate).
 intros. inversion Heqh; subst b0; subst c0.
 destruct (fold_constants_bexp b) eqn: hh;
   pose (H5 eq_refl) as h2;
   simpl; simpl in h2; rewrite hh in h2; rewrite hh; pose (E_WhileLoop b c st0 st'0 st'' H1 H2 H4) as h0; (try auto).
 apply (WHILE_true b c). pose (fold_constants_bexp_sound b). rewrite hh in b0. auto.
 auto. pose (fold_constants_bexp_sound b st0) as h'; rewrite H1 in h'; rewrite hh in h'; simpl in h'; discriminate.
 eapply E_WhileLoop. rewrite <- hh. rewrite <- fold_constants_bexp_sound. auto. apply H. apply H2; auto. auto.
 eapply E_WhileLoop. rewrite <- hh. rewrite <- fold_constants_bexp_sound. auto. apply H. apply H2; auto. auto.
 eapply E_WhileLoop. rewrite <- hh. rewrite <- fold_constants_bexp_sound. auto. apply H. apply H2; auto. auto. 
 eapply E_WhileLoop. rewrite <- hh. rewrite <- fold_constants_bexp_sound. auto. apply H. apply H2; auto. auto.
 intros. inversion Heqh; subst b0; subst c0.
 simpl; destruct (fold_constants_bexp b) eqn:hh; pose (fold_constants_bexp_sound b st0) as h1; rewrite H1 in h1; rewrite hh in h1; simpl in h1; (try discriminate); try ( apply E_WhileEnd; simpl; rewrite h1; auto).
 apply E_Skip.
 elim c; try auto.
 intros. pose (CAss_congruence i a (fold_constants_aexp a) (fold_constants_aexp_sound a) st st').
 destruct i0. auto.
 intros. inversion H1. Print E_Seq. apply (E_Seq _ _ st st'0); auto.
 intros. simpl in H1; destruct (fold_constants_bexp b) eqn:hh;
         try( apply E_IfTrue; pose (fold_constants_bexp_sound b st) as e; rewrite hh in e; try( rewrite e; auto); auto; fail);
         try( apply E_IfFalse; pose (fold_constants_bexp_sound b st) as e; rewrite hh in e; try( rewrite e; auto); auto; fail).
 inversion H1; [apply E_IfTrue | apply E_IfFalse]; pose (fold_constants_bexp_sound b st) as h3; rewrite hh in  h3; try( try rewrite h3; auto; apply H; auto; fail); try ( try rewrite h3; auto; apply H0; auto; fail).
 inversion H1; [apply E_IfTrue | apply E_IfFalse]; pose (fold_constants_bexp_sound b st) as h3; rewrite hh in  h3; try( try rewrite h3; auto; apply H; auto; fail); try ( try rewrite h3; auto; apply H0; auto; fail).
 inversion H1; [apply E_IfTrue | apply E_IfFalse]; pose (fold_constants_bexp_sound b st) as h3; rewrite hh in  h3; try( try rewrite h3; auto; apply H; auto; fail); try ( try rewrite h3; auto; apply H0; auto; fail).
 inversion H1; [apply E_IfTrue | apply E_IfFalse]; pose (fold_constants_bexp_sound b st) as h3; rewrite hh in  h3; try( try rewrite h3; auto; apply H; auto; fail); try ( try rewrite h3; auto; apply H0; auto; fail).
 intros. simpl in H0. destruct (fold_constants_bexp b) eqn:hh.
 apply (WHILE_true b c0). pose (fold_constants_bexp_sound b). rewrite hh in b0; auto. auto.
 inversion H0. apply E_WhileEnd. pose (fold_constants_bexp_sound b st'). rewrite hh in e; rewrite e; auto.
 rewrite <- hh in H0.
 remember (WHILE fold_constants_bexp b DO fold_constants_com c0 END) as h. generalize dependent Heqh. elim H0; try(simpl; intros; discriminate).
 intros. inversion Heqh; subst b0; subst c1. pose (H st'0 st0 H2). pose (H5 eq_refl). eapply E_WhileLoop. rewrite fold_constants_bexp_sound. auto. apply c1. apply c2.
 intros. inversion Heqh; subst b0 ; subst c1. apply E_WhileEnd. rewrite fold_constants_bexp_sound. auto.
 rewrite <- hh in H0.
 remember (WHILE fold_constants_bexp b DO fold_constants_com c0 END) as h. generalize dependent Heqh. elim H0; try(simpl; intros; discriminate).
 intros. inversion Heqh; subst b0; subst c1. pose (H st'0 st0 H2). pose (H5 eq_refl). eapply E_WhileLoop. rewrite fold_constants_bexp_sound. auto. apply c1. apply c2.
 intros. inversion Heqh; subst b0 ; subst c1. apply E_WhileEnd. rewrite fold_constants_bexp_sound. auto.
 rewrite <- hh in H0.
 remember (WHILE fold_constants_bexp b DO fold_constants_com c0 END) as h. generalize dependent Heqh. elim H0; try(simpl; intros; discriminate).
 intros. inversion Heqh; subst b1; subst c1. pose (H st'0 st0 H2). pose (H5 eq_refl). eapply E_WhileLoop. rewrite fold_constants_bexp_sound. auto. apply c1. apply c2.
 intros. inversion Heqh; subst b1 ; subst c1. apply E_WhileEnd. rewrite fold_constants_bexp_sound. auto.
 rewrite <- hh in H0.
 remember (WHILE fold_constants_bexp b DO fold_constants_com c0 END) as h. generalize dependent Heqh. elim H0; try(simpl; intros; discriminate).
 intros. inversion Heqh; subst b0; subst c1. pose (H st'0 st0 H2). pose (H5 eq_refl). eapply E_WhileLoop. rewrite fold_constants_bexp_sound. auto. apply c1. apply c2.
 intros. inversion Heqh; subst b0 ; subst c1. apply E_WhileEnd. rewrite fold_constants_bexp_sound. auto.
Qed.

Theorem inequiv_exercise:
  ~ cequiv (WHILE BTrue DO SKIP END)
    SKIP.

  unfold not; unfold cequiv. intros.
  pose (E_Skip (t_empty 0)).
  pose (H (t_empty 0) (t_empty 0)).
  destruct i. pose (H1 c).
  SearchPattern ( _ / _ \\ _).
  pose loop_never_stops.
  pose (n loop (t_empty 0) (t_empty 0) eq_refl). unfold loop in n0.
  unfold not in n0. auto.
Qed.

Module HIMP.

  Inductive com : Type :=
| CSkip : com
| CAss : id -> aexp -> com
| CSeq : com -> com -> com
| CIf : bexp -> com -> com -> com
| CWhile : bexp -> com -> com
| CHavoc : id -> com.

  Notation "'SKIP'" :=
    CSkip.

  Notation "X '::=' a":=
    (CAss X a) (at level 60).

  Notation "c1 ;; c2" :=
    (CSeq c1 c2) (at level 80, right associativity).

  Notation "'WHILE' b 'DO' c 'END'" :=
    (CWhile b c) (at level 80, right associativity).

  Notation "'IFB' b 'THEN' c1 'ELSE' c2 'END'" :=
    (CIf b c1 c2) (at level 80, right associativity).

  Notation "'HAVOC' l" := (CHavoc l) (at level 60).

  Reserved Notation "c1 '/' st '\\' st'"
           (at level 40, st at level 39).


End HIMP.


