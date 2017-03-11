Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Maps.
Require Import SfLib.

Module AExp.
  Inductive aexp : Type :=
| ANum : nat -> aexp
| APlus : aexp -> aexp -> aexp
| AMinus : aexp -> aexp -> aexp
| AMult : aexp -> aexp -> aexp.

  Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | Ble : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.


  Fixpoint aeval (a:aexp) : nat :=
    match a with
      | ANum n => n
      | APlus a1 a2 => (aeval a1) + (aeval a2)
      | AMinus a1 a2 => (aeval a1) - (aeval a2)
      | AMult a1 a2 => (aeval a1) * (aeval a2)
    end.

Print beq_nat.
Print eq_nat_dec.

Definition beq_nat_bydec (a b :nat) : bool :=
  match (eq_nat_dec a b) with
    | left _ => true
    | right _ => false
  end.

Print le_dec.

Definition leb_bydec (a b :nat) : bool :=
  match le_dec a b with
    | left _ => true
    | right _ => false
  end.

  Fixpoint beval (b:bexp): bool :=
    match b with
      | BTrue => true
      | BFalse => false
      | BEq a1 a2 => beq_nat_bydec (aeval a1) (aeval a2)
      | Ble a1 a2 => leb_bydec (aeval a1) (aeval a2)
      | BNot b => negb (beval b)
      | BAnd b1 b2 => andb (beval b1) (beval b2)
    end.

  Fixpoint optimize_0plus (a:aexp) :aexp :=
    match a with
      | ANum n => ANum n
      | APlus (ANum 0) e2 => optimize_0plus e2
      | APlus e1 e2 => APlus (optimize_0plus e1) (optimize_0plus e2)
      | AMinus e1 e2 => AMinus (optimize_0plus e1) (optimize_0plus e2)
      | AMult e1 e2 => AMult (optimize_0plus e1) (optimize_0plus e2)
    end.

  Theorem optimize_0plus_sound:
    forall a,
      aeval a = aeval (optimize_0plus a).
  Abort.

  Module AEVALR_FIRST_TRY.

    Reserved Notation "e '\\' n" (at level 50, left associativity).
    Inductive aevalR : aexp -> nat -> Prop :=
    | E_ANum :
        forall n:nat, (ANum n) \\ n
    | E_APlus : forall (e1 e2:aexp) (n1 n2:nat),
                  (e1 \\ n1) -> (e2 \\ n2) -> (APlus e1 e2) \\ (n1 + n2)
    | E_AMinus : forall (e1 e2:aexp) (n1 n2:nat),
                   (e1 \\ n1) -> (e2 \\ n2) -> (AMinus e1 e2) \\ (n1 - n2)
    | E_AMult : forall (e1 e2:aexp) (n1 n2:nat),
                  (e1 \\ n1) -> (e2 \\ n2) -> (AMult e1 e2) \\ (n1 * n2)
    where "e '\\' n" := (aevalR e n): type_scope.


    Theorem aeval_iff_aevalR :
      forall a n,
        (a \\ n) <-> aeval a = n.
      split. intros.
      elim H; try auto; simpl;
      repeat (intros; rewrite H1; rewrite H3; auto).
      generalize n. clear n.
      elim a; simpl; try auto.
      intros. rewrite H; apply E_ANum.
      intros. rewrite <- H1. apply E_APlus; auto.
      intros. rewrite <- H1; apply E_AMinus; auto.
      intros. rewrite <- H1; apply E_AMult; auto.
    Qed.


    End AEVALR_FIRST_TRY.

End AExp.

Require Export Maps.

Definition state := total_map nat.

Definition empty_state : state :=
  t_empty 0.

Inductive aexp: Type :=
| ANum : nat -> aexp
| AId : id -> aexp
| APlus : aexp -> aexp -> aexp
| AMinus : aexp -> aexp -> aexp
| AMult : aexp -> aexp -> aexp.


Definition X:id := Id 0.
Definition Y:id := Id 1.
Definition Z:id := Id 2.



Inductive bexp: Type :=
| BTrue : bexp
| BFalse : bexp
| BEq : aexp -> aexp -> bexp
| BLe : aexp -> aexp -> bexp
| BNot : bexp -> bexp
| BAnd : bexp -> bexp -> bexp.


Definition beq_nat_bydec (a b :nat) : bool :=
  match (eq_nat_dec a b) with
    | left _ => true
    | right _ => false
  end.

Print le_dec.

Definition leb_bydec (a b :nat) : bool :=
  match le_dec a b with
    | left _ => true
    | right _ => false
  end.



Fixpoint aeval (st:state) (a:aexp) : nat :=
  match a with
    | ANum n => n
    | AId x => st x
    | APlus a1 a2 => (aeval st a1) + (aeval st a2)
    | AMinus a1 a2 => (aeval st a1) - (aeval st a2)
    | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st:state) (b:bexp) : bool :=
  match b with
    | BTrue => true
    | BFalse => false
    | BEq a1 a2 => beq_nat_bydec (aeval st a1) (aeval st a2)
    | BLe a1 a2 => leb_bydec (aeval st a1) (aeval st a2)
    | BNot b1 => negb (beval st b1)
    | BAnd b1 b2 => andb (beval st b1) (beval st b2)
  end.

Inductive com: Type :=
| CSkip : com
| CAss : id -> aexp -> com
| CSeq : com -> com -> com
| CIf : bexp -> com -> com -> com
| CWhile : bexp -> com -> com.

Notation "'SKIP'" := CSkip.
Notation "x '::=' c" := (CAss x c) (at level 60).
Notation "c1 ;; c2" := (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" := (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" := (CIf c1 c2 c3)(at level 80, right associativity).

Fixpoint ceval_fun_no_while(st: state) (c:com) :state :=
  match c with
    | SKIP =>
      st
    | x ::= a1 =>
      t_update st x (aeval st a1)
    | c1 ;; c2 =>
      let st' := ceval_fun_no_while st c1 in
      ceval_fun_no_while st' c2
    | IFB b THEN c1 ELSE c2 FI =>
      if (beval st b)
      then  ceval_fun_no_while st c1
      else ceval_fun_no_while st c2
    | WHILE b DO c END =>
      st
  end.


Reserved Notation "c1 '/' st '\\' st'"
         (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
| E_Skip : forall st,
             SKIP / st \\ st
| E_Ass : forall st a1 n x,
            aeval st a1 = n ->
            (x ::= a1) / st \\ (t_update st x n)
| E_Seq : forall c1 c2 st st' st'',
            c1 / st \\ st' ->
            c2 / st' \\ st'' ->
            (c1 ;; c2) / st \\ st''
| E_IfTrue : forall b c1 c2 st st',
               (beval st b = true) ->
               c1 / st \\ st' ->
               (IFB b THEN c1 ELSE c2 FI) / st \\ st'
| E_IfFalse :
    forall b c1 c2 st st',
      (beval st b = false) ->
      c2 / st \\ st' ->
      (IFB b THEN c1 ELSE c2 FI) / st \\ st'
| E_WhileLoop :
    forall b c st st' st'',
      (beval st b = true) ->
      c / st \\ st' ->
      (WHILE b DO c END) / st' \\ st'' -> 
      (WHILE b DO c END) / st \\ st''
| E_WhileEnd :
    forall b c st,
      (beval st b = false) ->
      (WHILE b DO c END) / st \\ st
where "c1 '/' st '\\' st'" := (ceval c1 st st').

Hint Resolve E_WhileLoop E_WhileEnd E_IfFalse E_IfTrue E_Seq E_Ass E_Skip : ceval_base.

Example ceval_example1:
  (X ::= ANum 2;;
     IFB BLe (AId X) (ANum 1)
     THEN Y ::= ANum 3
     ELSE Z ::= ANum 4
     FI) / empty_state \\ (t_update (t_update empty_state X 2) Z 4).
Proof.
  eapply E_Seq. eapply E_Ass. simpl; trivial.
  simpl. eapply E_IfFalse; simpl. unfold t_update. rewrite eq_id_dec_id.
  compute. trivial.
  eapply E_Ass. simpl. trivial.
Qed.

Theorem ceval_determinstic:
  forall c st st1 st2,
    c / st \\ st1 ->
    c / st \\ st2 ->
    st1 = st2.
  intros. generalize st2 H0. clear H0 st2.
  elim H;  try (eauto with ceval_base).
  intros. inversion H0; trivial.
  intros. inversion H1. rewrite H0 in H6. rewrite H6; trivial.
  intros. inversion H4. pose(H1 st'0 H7). apply H3. rewrite e. auto.
  intros. inversion H3.  exact(H2 st2 H10). rewrite H9 in H0. inversion H0.
  intros. inversion H3.  rewrite H9 in H0. inversion H0.
  apply H2. auto.
  intros. inversion H5. pose (H2 _ H9). rewrite <- e in H12. apply H4. auto.
  rewrite H9 in H0. rewrite H10 in H0. inversion H0.
  intros. inversion H1. rewrite H4 in H0; inversion H0. trivial.
Qed.

(*
Theorem plus2_spec :
  forall st n st',
    st X = n ->
    plus2 / st \\ st' ->
    st' X = n + 2.*)

Definition plus2 : com :=
  X ::= (APlus (AId X) (ANum 2)).

Definition XtimesYinZ : com :=
  Z ::= (AMult (AId X) (AId Y)).

Definition subtract_slowly_body : com :=
  Z ::= AMinus (AId Z) (ANum 1) ;;
    X ::= AMinus (AId X) (ANum 1).

Definition subtract_slowly : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
        subtract_slowly_body
        END.

Definition subtract_3_from_5_slowly : com :=
  X ::= ANum 3 ;;
    Z ::= ANum 5 ;;
    subtract_slowly.

Definition loop : com :=
  WHILE BTrue DO
        SKIP
        END.

Theorem plus2_spec :
  forall st n st',
    st X = n ->
    plus2 / st \\ st' ->
    st' X = n + 2.
  intros. unfold plus2 in H0. inversion H0. rewrite <- H5.
  simpl. rewrite H. unfold t_update. apply eq_id_dec_id.
Qed.


Theorem XtimesYinZ_spec :
  forall st n m st',
    st X = n ->
    st Y = m ->
    XtimesYinZ / st \\ st' ->
    st' Z = m * n.
  unfold XtimesYinZ. intros.
  inversion H1. rewrite <- H6 in H5. unfold t_update. rewrite eq_id_dec_id.
  rewrite <- H6. simpl. rewrite H; rewrite H0. rewrite mult_comm. trivial.
Qed.


Theorem loop_never_stops:
  forall c st st',
    c=loop -> ~(loop / st \\ st').
  unfold loop. unfold not. intros.
  generalize H. elim H0; rewrite H; intros; try discriminate.
  auto. inversion H2. rewrite <- H4 in H1. simpl in H1; discriminate.
Qed.


Fixpoint no_whiles (c:com) : bool :=
  match c with
    | SKIP =>
      true
    | _ ::= _ =>
      true
    | c1 ;; c2 =>
      andb (no_whiles c1) (no_whiles c2)
    | IFB _ THEN c1 ELSE c2 FI =>
      andb (no_whiles c1) (no_whiles c2)
    | WHILE _ DO _ END  =>
      false
  end.

Inductive no_whilesR : com -> Prop :=
| skip_nw : no_whilesR SKIP
| ass_nw : forall a b, no_whilesR (a ::= b)
| seq_nw : forall c1 c2, no_whilesR c1 -> no_whilesR c2 -> no_whilesR (c1 ;; c2)
| if_nw : forall b c1 c2, no_whilesR c1 -> no_whilesR c2 -> no_whilesR (IFB b THEN c1 ELSE c2 FI).

Theorem no_whiles_eqv :
  forall c, no_whiles c = true <-> no_whilesR c.
  split.
  elim c; intros; try discriminate.
  apply skip_nw. apply ass_nw. simpl in H1.
  remember (no_whiles c0) as h1; remember (no_whiles c1) as h2.
  generalize Heqh1 Heqh2; clear Heqh1 Heqh2.
  case (no_whiles c0); case (no_whiles c1); intros hh hhh; try (rewrite hh in H1; rewrite hhh in H1; simpl in H1; inversion H1).
  apply seq_nw; auto.
  simpl in H1. remember (no_whiles c0) as h1; remember (no_whiles c1) as h2.
  generalize Heqh1 Heqh2; clear Heqh1 Heqh2.
  case (no_whiles c0); case (no_whiles c1); intros hh hhh; try (rewrite hh in H1; rewrite hhh in H1; simpl in H1; inversion H1).
  apply if_nw; auto.
  intros. elim H; intros; simpl; try auto.
  rewrite H1; rewrite H3; try auto.
  rewrite H1; rewrite H3; try auto.
Qed.

Print ex.

Theorem no_whiles_terminating:
  forall k, no_whilesR k -> forall st, exists st', k / st \\ st'.
  intros k h.
  elim h; intros.
  exists st; apply E_Skip.
  exists (t_update st a (aeval st b)). apply E_Ass. trivial.
  pose (H0 st). inversion e. pose (H2 x). inversion e0.
  exists x0. eapply E_Seq; eauto.
  pose (H0 st). inversion e. pose (H2 st). inversion e0.
  remember (beval st b) as c. generalize Heqc. clear Heqc.
  case c; intros; [exists x; eapply E_IfTrue| exists x0; eapply E_IfFalse]; eauto.
Qed.

Inductive sinstr : Type :=
| SPush : nat -> sinstr
| SLoad : id -> sinstr
| SPlus : sinstr
| SMinus : sinstr
| SMult : sinstr.


Fixpoint s_execute (st : state)
         (stack : list nat)
         (prog : list sinstr) {struct prog} : list nat :=
  match prog with
    | nil => stack
    | SPush x :: fol => s_execute st (x :: stack) fol
    | SLoad a :: fol => s_execute st ((st a) :: stack) fol
    | SPlus :: fol =>
      match stack with
        | x1::x2::newstack => s_execute st ((x1 + x2)::newstack) fol
        | _ => s_execute st stack fol
      end
    | SMinus :: fol =>
      match stack with
        | x1::x2::newstack => s_execute st ((x2-x1)::newstack) fol
        | _ => s_execute st stack fol
      end
    | SMult :: fol =>
      match stack with
        | x1 :: x2 :: newstack => s_execute st ((x1*x2)::newstack) fol
        | _ => s_execute st stack fol
      end
  end.

Example s_execute1:
  s_execute empty_state []
            [SPush 5; SPush 3; SPush 1; SMinus]
  = [2;5]. auto.
Qed.


Example s_execute2:
  s_execute (t_update empty_state X 3) [3;4]
            [SPush 4; SLoad X; SMult; SPlus]
  = [15;4].
simpl. unfold t_update. rewrite eq_id_dec_id. auto.
Qed.



Fixpoint s_compile (e:aexp) : list sinstr :=
  match e with
    | ANum x => SPush x :: nil
    | AId i => SLoad i :: nil
    | APlus a b => (s_compile a) ++ (s_compile b) ++  SPlus :: nil
    | AMinus a b => (s_compile a) ++ (s_compile b) ++ SMinus :: nil
    | AMult a b => (s_compile a) ++ (s_compile b) ++ SMult :: nil
  end.

Lemma s_execute_append :
  forall a b c st,
    s_execute st (c) (a ++ b) = s_execute st (s_execute st (c) a) b. 
  intro. elim a; auto.
  intros. elim a0; intros; auto. simpl. apply H.
  simpl. apply H.
  case c. simpl. apply H.
  intros. case l0. simpl. apply H.
  simpl. intros; apply H.
  case c. simpl. apply H.
  intros. case l0. simpl. apply H.
  simpl. intros; apply H.
  case c. simpl. apply H.
  intros. case l0. simpl. apply H.
  simpl.  intros; apply H.
Qed.

  Theorem s_compile_correct :
    forall st e c,
      s_execute st c (s_compile e) =  [aeval st e] ++ c.
    intros st e. elim e; intros; auto.
    simpl. rewrite s_execute_append. rewrite H. rewrite s_execute_append. rewrite H0. simpl. rewrite plus_comm. trivial.
    simpl. rewrite s_execute_append. rewrite H. rewrite s_execute_append. rewrite H0. simpl. trivial.
    simpl. rewrite s_execute_append. rewrite H. rewrite s_execute_append. rewrite H0. simpl. rewrite mult_comm. trivial.
  Qed.


  Module BREAKIMP.
    Inductive com : Type :=
  | CSkip : com
  | CBreak : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.

    Notation "'SKIP'" :=
      CSkip.

    Notation "'BREAK'" :=
      CBreak.

    Notation "x '::=' a" :=
      (CAss x a) (at level 60).

    Notation "c1 ;; c2" :=
      (CSeq c1 c2) (at level 80, right associativity).

    Notation "'WHILE' b 'DO' c 'END'" :=
      (CWhile b c) (at level 80, right associativity).

    Notation "'IFB' b 'THEN' c1 'ELSE' c2 'FI' " :=
      (CIf b c1 c2) (at level 80, right associativity).

    Inductive status : Type :=
    | SContinue : status
    | SBreak : status.

    Reserved Notation "c1 '/' st '\\' s '/' st'"
             (at level 40, st, s at level 39).

    Inductive ceval : com -> state -> status -> state -> Prop :=
    | E_Skip : forall st,
                 SKIP / st \\ SContinue / st
    | E_Ass : forall st a b,
                (a ::= b) / st \\ SContinue / (t_update st a (aeval st b))
    | E_Break : forall st,
                  BREAK / st \\ SBreak / st
    | E_IfTrue : forall st st' c1 c2 signal,
                   c1 / st \\ signal / st' ->
                   (IFB BTrue THEN c1 ELSE c2 FI) / st \\ signal / st'
    | E_IfFalse : forall st st' c1 c2 signal,
                    c2 / st \\ signal / st' ->
                    (IFB BFalse THEN c1 ELSE c2 FI) / st \\ signal / st'
    | E_SeqBreak : forall st st' c1 c2,
                     c1 / st \\ SBreak / st' ->
                     (c1 ;; c2) / st \\ SBreak / st'
    | E_SeqCont : forall st st' st'' c1 c2 signal,
                    c1 / st \\ SContinue / st' ->
                    c2 / st' \\ signal / st'' ->
                    (c1 ;; c2) / st \\ signal / st''
    | E_WhileFalse : forall st b c,
                       beval st b = false ->
                       WHILE b DO c END / st \\ SContinue / st
    | E_WhileBreak : forall st st' b c,
                       c / st \\ SBreak / st' ->
                       beval st b = true ->
                       (WHILE b DO c END) / st \\ SContinue / st'
    | E_WhileTrue : forall st st' st'' b c,
                      beval st b = true ->
                      c / st \\ SContinue / st' ->
                      (WHILE b DO c END) / st' \\ SContinue / st'' ->
                      (WHILE b DO c END) / st \\ SContinue / st''
    where "c1 '/' st '\\' signal '/' st'" := (ceval c1 st signal st').

    Theorem break_ignore : forall c st st' s,
                             (BREAK;;c) / st \\ s / st' ->
                             st = st'.
      intros. inversion H.  inversion H5. trivial. inversion H2.
    Qed.

    Theorem while_continue : forall b c st st' s,
                               (WHILE b DO c END) / st \\ s / st' ->
                               s = SContinue.
      intros.
      inversion H; auto.
    Qed.

    Theorem while_stops_on_break :
      forall b c st st',
        beval st b = true ->
        c / st \\ SBreak / st' ->
        (WHILE b DO c END) / st \\ SContinue / st'.

      intros. apply E_WhileBreak; auto.
    Qed.
  End BREAKIMP.
  
    