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
Notation "'IFB' c1 'THEN' c2 'ELSE' c3" := (CIf c1 c2 c3)(at level 80, right associativity).

