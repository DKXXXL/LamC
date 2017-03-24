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


