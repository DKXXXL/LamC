Require Import Coq.omega.Omega.
Require Import Coq.Arith.Arith.
Require Import SfLib.
Require Import Imp.
Require Import Maps.

Fixpoint ceval_step3 (st:state) (c: com) (i:nat)
:option state :=
  match i with
    | O => None
    | S i' =>
      match c with
        | SKIP =>
          Some st
        | l ::= a1 =>
          Some (t_update st l (aeval st a1))
        | c1 ;; c2 =>
          match (ceval_step3 st c1 i') with
            | Some st' => ceval_step3 st' c2 i'
            | None => None
          end
        | IFB b THEN c1 ELSE c2 FI =>
          if (beval st b)
          then ceval_step3 st c1 i'
          else ceval_step3 st c2 i'
        | WHILE b1 DO c1 END =>
          if (beval st b1)
          then match (ceval_step3 st c1 i') with
                 | Some st' => ceval_step3 st' c i'
                 | None => None
               end
          else Some st
      end
  end.

Notation "'LETOPT' x <== e1 'IN' e2" :=
  (match e1 with
     | Some x => e2
     | None => None
   end)
    (right associativity, at level 60).

Fixpoint ceval_step (st : state) (c:com) (i:nat) : option state :=
  match i with
    | O => None
    | S i' =>
      match c with
        | SKIP => Some st
        | l ::= a1 =>
          Some (t_update st l (aeval st a1))
        | c1 ;; c2 =>
          LETOPT st' <== ceval_step st c1 i' IN
                 ceval_step st' c2 i'
        | IFB b THEN c1 ELSE c2 FI =>
          if (beval st b)
          then ceval_step st c1 i'
          else ceval_step st c2 i'
        | WHILE b1 DO c1 END =>
          if (beval st b1)
          then LETOPT st' <== ceval_step st c1 i' IN
                      ceval_step st' c i'
          else Some st
      end
  end.

Definition test_ceval (st:state) (c:com) :=
  match ceval_step st c 500 with
    | None => None
    | Some st => Some (st X, st Y, st Z)
  end.

Definition pup_to_n : com :=
  X ::= ANum 1 ;; Y ::= ANum 0 ;;
    WHILE BLe (AId X) (ANum 50) DO
    Y ::= APlus (AId Y) (AId X) ;;
    X ::= APlus (AId X) (ANum 1)
    END.

Theorem ceval_step__ceval :
  forall c st st',
    (exists i, ceval_step st c i = Some st') ->
    c / st \\ st'.
  intro.
  elim c;    try( intros;inversion H; generalize H0; clear H0; case x; try (simpl; intros; discriminate); simpl; intros).
  inversion H0; subst st; apply E_Skip.
  inversion H0; subst st'; apply E_Ass.
  trivial.
  intros. inversion H1. generalize H2. clear H2. case x; try (simpl; intros; discriminate).
  simpl. intros. remember (ceval_step st c0 n) as c01. generalize Heqc01 H2. clear Heqc01 H2. case c01. intro. remember (ceval_step s c1 n) as c11. generalize Heqc11. clear Heqc11. case c11. intros.
  symmetry in Heqc11; symmetry in Heqc01. Print ex. assert (exists i, ceval_step s c1 i = Some s0). exists n. auto. assert (exists i, ceval_step st c0 i = Some s). exists n. auto.
  pose (H0 s s0 H3). pose (H st s H4). inversion H2; subst s0. eapply E_Seq. apply c3. auto.
  intros; discriminate. intros; discriminate.
  intros. inversion H1. generalize H2. clear H2. case x; try(intros; discriminate).
  simpl. remember (beval st b) as b'. generalize Heqb'; clear Heqb'.
  case b'. intros. pose (ex_intro (fun x => ceval_step st c0 x = Some st') n H2).
  pose (H st st' e). apply E_IfTrue; auto.
  intros. pose (ex_intro (fun x => ceval_step st c1 x = Some st') n H2). pose (H0 st st' e). apply E_IfFalse; auto.
  intros. inversion H0. generalize H1. clear H1. elim x; try (simpl; intros; discriminate).
  Restart.
  intros. inversion H. generalize dependent c. generalize dependent st. generalize dependent st'.
  elim x; try( simpl; intros; discriminate).
  intros until c. case c. simpl. intros. inversion H1. apply E_Skip.
  simpl. intros. inversion H1. apply E_Ass. trivial.
  simpl. intros c0 c1. remember (ceval_step st c0 n) as c01.
  generalize Heqc01.   case c01; try (simpl; intros; discriminate).
  intros. symmetry in Heqc00. pose (ex_intro (fun x => ceval_step st c0 x = Some s) n Heqc00).
  pose (ex_intro (fun x => ceval_step s c1 x = Some st') n H1).
  pose (H s st c0 e Heqc00).
  pose (H st' s c1 e0 H1).
  eapply E_Seq. apply c2. apply c3.
  intros until b. simpl. remember (beval st b) as b'. generalize Heqb'; clear Heqb'. case b'.
  intros. pose (ex_intro (fun i => ceval_step st c0 i = Some st') n H1).
  pose (H st' st c0 e H1). apply E_IfTrue; auto.
  intros. pose (ex_intro (fun i=> ceval_step st c1 i = Some st') n H1).
  pose (H st' st c1 e H1). apply E_IfFalse; auto.
  simpl. intros until c0. remember (beval st b) as b'. generalize Heqb'.
  case b'. remember (ceval_step st c0 n) as c01. generalize Heqc01. case c01; try(simpl; intros; discriminate).
  intros. eapply E_WhileLoop. auto. symmetry in Heqc00. pose (ex_intro (fun i => ceval_step st c0 i = Some s) n Heqc00). pose (H _ _ _ e Heqc00). apply c1.
  pose (ex_intro (fun i => ceval_step s (WHILE b DO c0 END) i = Some st') n H1). pose (H _ _ _ e H1). apply c1.
  intros. inversion H1. subst st. apply E_WhileEnd; auto.
Qed.

Theorem ceval_step_more :
  forall i1 i2 st st' c,
    i1 <= i2 ->
    ceval_step st c i1 = Some st' ->
    ceval_step st c i2 = Some st'.
  intros until i2. generalize i1. clear i1.
  elim i2.
  intros i1 st st' c h. inversion h. simpl;intros; discriminate.
  intros until c. case c; simpl; case i1; try(simpl; intros; discriminate).
  simpl; auto.
  simpl; auto.
  simpl. intros until c1. destruct (ceval_step st c0 n0) eqn: H1. intros.
  assert (n0 <= n); try omega.
  pose (H _ _ _ _ H3 H1).
  pose (H _ _ _ _ H3 H2).
  rewrite e. auto. intros; discriminate.
  intros until b. simpl. destruct (beval st b) eqn: H1;intros; apply (H n0 _ _ _); try (auto; omega).
  intros until b. simpl. destruct (beval st b) eqn: H1.
  intro. destruct (ceval_step st c0 n0) eqn:H2; try(simpl; intros; discriminate).
  intro; assert( n0 <= n); try omega.
  pose (H n0 _ _ _ H3 H2). rewrite e.
  intros. apply (H n0 _ _ _); try(auto; omega).
  intros; auto.
Qed.


Theorem ceval__ceval_step :
  forall c st st',
    c / st \\ st' ->
    exists i, ceval_step st c i = Some st'.

  intros. elim H.
  intros. exists 1. simpl; auto.
  intros. exists 1. simpl. subst n. auto.
  intros. inversion H1. inversion H3. exists (S(x+x0)). simpl.
  assert (ceval_step st0 c1 (x+x0) = Some st'0).
  apply (ceval_step_more x); try (auto; omega).
  rewrite H6.
  apply (ceval_step_more x0); try (auto; omega).
  intros. inversion H2. exists (S x). simpl. rewrite H0. auto.
  intros. inversion H2. exists (S x). simpl. rewrite H0; auto.
  intros. inversion H4. inversion H2. exists (S (x+x0)). simpl. rewrite H0.
  assert (ceval_step st0 c0 (x + x0) = Some st'0). apply (ceval_step_more x0); try(auto; omega).
  rewrite H7. apply (ceval_step_more x); try (auto; omega).
  intros. exists 1. simpl. rewrite H0. auto.
Qed.

Theorem ceval_determinstic' :
  forall c st st1 st2,
    c / st \\ st1 ->
    c / st \\ st2 ->
    st1 = st2.

  intros. pose (ceval__ceval_step _ _ _ H).
  pose (ceval__ceval_step _ _ _ H0).
  inversion e. inversion e0.
  assert (ceval_step st c (x+x0) = Some st1). apply (ceval_step_more x); try (auto;omega).
  assert (ceval_step st c (x+x0) = Some st2). apply (ceval_step_more x0); try (auto; omega).
  rewrite H3 in H4. inversion H4; auto.
Qed.

