Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.

Import ListNotations.
Require Import SfLib.
Require Import Maps.
Require Import Imp.


Inductive tm : Type :=
| C:nat -> tm
| P : tm -> tm -> tm.

Fixpoint evalF (t:tm) : nat :=
  match t with
    | C n => n
    | P a1 a2 => evalF a1 + evalF a2
  end.

Reserved Notation "t '\\' n" (at level 50, left associativity).
Inductive eval : tm -> nat -> Prop :=
| E_Const : forall n,
              C n \\ n
| E_Plus : forall t1 t2 n1 n2,
             t1 \\ n1 ->
             t2 \\ n2 ->
             P t1 t2 \\ (n1 + n2)
where "t '\\' n" := (eval t n).

Module SIMPLEARITH1.

  Reserved Notation "t '==>' t'" (at level 40).
  Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst :
      forall n1 n2,
        P (C n1) (C n2) ==> C (n1 + n2)
  | ST_Plus1 :
      forall t1 t1' t2,
        t1 ==> t1' ->
        P t1 t2 ==> P t1' t2
  | ST_Plus2 :
      forall n1 t2 t2',
        t2 ==> t2' ->
        P (C n1) t2 ==> P (C n1) t2'
  where "t '==>' t'" := (step t t').

  Example test_step_1 :
    P
      (P (C 0) (C 3))
      (P (C 2) (C 4))
      ==>

      P (C (0+3))
      (P (C 2) (C 4)).
  apply ST_Plus1. apply ST_PlusConstConst.
  Qed.

  Example test_step_2:
    P (C 0)
      (P
         (C 2)
         (P (C 0) (C 3)))
      ==>
      P (C 0)
      (P
         (C 2)
         (C (0+3))).
  apply ST_Plus2. apply ST_Plus2. apply ST_PlusConstConst.
  Qed.

  End SIMPLEARITH1.

Definition relation (X:Type) := X -> X -> Prop.

Definition determinstic {X:Type} (R:relation X) :=
  forall x y1 y2, R x y1 -> R x y2 -> y1 = y2.


Module SIMPLEARITH2.

  Import SIMPLEARITH1.
  Theorem step_deterministic:
    deterministic step.

    unfold deterministic.
    intros x y1 y2 h. generalize dependent y2.
    elim h. intros. inversion H. auto.
    inversion H3. inversion H3.
    intros. inversion H1. rewrite <- H3 in H. inversion H.
    pose (H0 t1'0 H5). rewrite e. auto.
    subst t1. inversion H.
    intros. inversion H1. subst t2. inversion H.
    subst t1. inversion H5. pose (H0 t2'0 H5). rewrite e. auto.
  Qed.

  
End SIMPLEARITH2.

Inductive value : tm -> Prop :=
  v_const : forall n, value (C n).

Reserved Notation "t '==>' t'" (at level 40).
Inductive step : tm -> tm -> Prop :=
| ST_PlusConstConst :
    forall n1 n2,
      P (C n1) (C n2) ==> C (n1 + n2)
| ST_Plus1 :
    forall t1 t1' t2,
      t1 ==> t1' ->
      P t1 t2 ==> P t1' t2
| ST_Plus2 :
    forall t1 t2 t2',
      value t1 ->
      t2 ==> t2' ->
      P t1 t2 ==> P t1 t2'
where "t '==>' t'" := (step t t').

Theorem step_determinstic:
  determinstic step.
  unfold determinstic.
  intros x y1 y2 h. generalize dependent y2.
  elim h. intros. inversion H. auto. inversion H3. inversion H4.
  intros. inversion H1. subst t1. subst t2. inversion H. pose (H0 t1'0 H5). rewrite e; auto.
  subst t1. subst t2. inversion H4. subst t0. inversion H.
  intros. inversion H2. subst t1. subst t2. inversion H0. subst t1. inversion H. subst t0. inversion H6. pose (H1 t2'0 H7). rewrite e; auto.
Qed.

Theorem strong_progress :
  forall (t:tm),
    (value t) \/ exists t', t ==> t'.

  intro.
  elim t. intro. left. apply v_const.
  intros. right. destruct H;destruct H0.
  inversion H. inversion H0. exists (C (n + n0)). apply ST_PlusConstConst.
  inversion H0. exists (P t0 x). apply ST_Plus2; auto.
  inversion H. exists (P x t1). apply ST_Plus1; auto.
  inversion H. exists (P x t1). apply ST_Plus1; auto.
Qed.


Definition normal_form {X:Type} (R:relation X) (t : X) : Prop :=
  ~ (exists t', R t t').

Lemma value_is_nf:
  forall c,
    value c -> normal_form step c.
  intros. inversion H. unfold normal_form. intro. inversion H1. inversion H2.
Qed.

Lemma nf_is_value:
  forall c,
    normal_form  step c -> value c.

  intro. unfold normal_form.
  destruct c. intros; apply v_const.
  intros. pose (strong_progress (P c1 c2)).
  assert (forall c1 c2, ~(value (P c1 c2))).
  intros. intro. inversion H0.
  destruct o. elim (H0 c1 c2 H1).
  elim (H H1).
Qed.


Corollary nf_eq_value:
  forall t,
    normal_form step t <-> value t.
  split; try (apply value_is_nf); try (apply nf_is_value).
Qed.


Module TEMP1.

  Inductive value: tm -> Prop :=
| v_const : forall n, value (C n)
| v_funny : forall t1 n2,
              value (P t1 (C n2)).

  Lemma value_not_same_as_normal_form :
    exists v, value v /\ ~ normal_form step v.

    exists (P (C 0) (C 1)); split.
    apply v_funny.
    unfold normal_form. intro. assert (exists t: tm, P(C 0) (C 1) ==> t). exists (C (0+1)). apply ST_PlusConstConst. auto.
  Qed.


  End TEMP1.


Module TEMP3.
  Reserved Notation "t '==>' t'" (at level 40).
Inductive step : tm -> tm -> Prop :=
| ST_PlusConstConst :
    forall n1 n2,
      P (C n1) (C n2) ==> C (n1 + n2)
| ST_Plus1 :
    forall t1 t1' t2,
      t1 ==> t1' ->
      P t1 t2 ==> P t1' t2
where "t '==>' t'" := (step t t').

Lemma value_not_nf:
  exists t, ~(value t) /\ (normal_form step t).

  exists (P (C 0) (P (C 0) (C 1))); split.
  intro. inversion H.
  unfold normal_form. intro. inversion H. inversion H0. inversion H4.
Qed.


End TEMP3.


Module TEMP4.
  Inductive tm:Type :=
| ttrue : tm
| tfalse : tm
| tif : tm -> tm -> tm -> tm.

  Inductive value : tm -> Prop :=
  | v_true : value ttrue
  | v_false : value tfalse.

  Reserved Notation "t '==>' t'" (at level 40).

  Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
                  tif ttrue t1 t2 ==> t1
  | ST_IfFalse : forall t1 t2,
                   tif tfalse t1 t2 ==> t2
  | ST_If : forall t1 t2 t t',
              t ==> t' ->
              tif t t1 t2 ==> tif t' t1 t2
  where "t '==>' t'" := (step t t').

  Definition bool_step_prop1:
    ~(tfalse ==> tfalse).
    intro. inversion H.
  Qed.


  Definition bool_step_prop2:
    ~(tif ttrue
        (tif ttrue ttrue ttrue)
        (tif tfalse tfalse tfalse)
        ==>
        ttrue).
    intro. inversion H.
  Qed.

  Definition bool_step_prop3:
    tif
      (tif ttrue ttrue ttrue)
      (tif ttrue ttrue ttrue)
      tfalse
      ==>
      tif
      ttrue
      (tif ttrue ttrue ttrue)
      tfalse.

    eapply ST_If. apply ST_IfTrue.
  Qed.

  Theorem strong_progress :
    forall t,
      value t \/ (exists t', t ==> t').
    intro. elim t.
    left; apply v_true.
    left; apply v_false.
    intros. right. destruct H.
    inversion H. exists t1; apply ST_IfTrue.
    exists t2; apply ST_IfFalse.
    inversion H. exists (tif x t1 t2). apply ST_If; auto.
  Qed.


  Theorem determinstic_if:
    forall x y z,
      x ==> y ->
      x ==> z ->
      y = z.

    intros x y z h1. generalize dependent z.
    elim h1. intros. inversion H. auto.
    inversion H4.
    intros. inversion H. auto. inversion H4.
    intros. inversion H1. subst t. subst t1. subst t2. subst t0. inversion H. subst t. inversion H.
    pose (H0 t'0 H6). rewrite e. auto.
  Qed.

End TEMP4.

(* Too boring, Module 5 *)
(* If short circuit then it is not determinstic, but still strong progression
   And to cancel strong progress, just remove the ST_If constructor *)


Inductive multi {X:Type} (R:relation X) : relation X :=
| multi_refl : forall (x:X), multi R x x
| multi_step : forall (x y z:X),
                R x y ->
                multi R y z ->
                multi R x z.

Notation "t '==>*' t'" := (multi step t t') (at level 40).

Theorem multi_R : forall {X:Type} (R:relation X) (x y :X),
                    R x y -> (multi R) x y.
  intros. eapply multi_step. eauto. apply multi_refl.
Qed.


Theorem multi_trans :
  forall {X:Type} (R:relation X) (x y z:X),
    multi R x y ->
    multi R y z ->
    multi R x z.

  intros X R x y z h1. generalize dependent z.
  elim h1; auto.
  intros. eapply multi_step; eauto.
Qed.


Hint Resolve ST_PlusConstConst ST_Plus1 ST_Plus2 v_const: smallstep_def.

Ltac calculate_smallstep :=
  match goal with
      | [|- ?X ==>* ?X] => eapply multi_refl
      | _ => (eapply multi_step; [auto with smallstep_def;fail | calculate_smallstep])
  end.
Lemma test_multistep_1:
  P
    (P (C 0) (C 3))
    (P (C 2) (C 4))
    ==>*
    C ((0+3) + (2+4)).
  calculate_smallstep.
Qed.


Lemma test_multistep_2:
  (C 3) ==>* (C 3).

  calculate_smallstep.
Qed.

Lemma test_multistep_3:
  (P (C 0) (C 3))
    ==>*
    (P (C 0) (C 3)).

  calculate_smallstep.

Qed.

Lemma test_multistep_4:
  P
    (C 0)
    (P
       (C 2)
       (P (C 0) (C 3)))
    ==>*
    P
    (C 0)
    (C (2 + (0 + 3))).

  calculate_smallstep.
Qed.


Definition step_normal_form := normal_form step.

Definition normal_form_of (t t' : tm) :=
  (t ==>* t' /\ step_normal_form t').

Theorem normal_form_unique:
  forall t t1 t2,
    normal_form_of t t1 ->
    normal_form_of t t2 ->
    t1 = t2.
  unfold normal_form_of. unfold step_normal_form. unfold normal_form.
  intros t t1 t2 h1. generalize dependent t2.
  destruct h1. remember t1 as t1'. rewrite Heqt1' in H.
  generalize dependent Heqt1'. elim H. intros. subst t1'. destruct H1.
  inversion H1. auto. assert (exists t, x ==> t); eauto. elim (H0 H7).
  intros. pose (H3 Heqt1'). destruct H4. inversion H4. subst x0. subst x. assert (exists t, t2 ==> t); eauto. elim (H5 H6).
  assert (y = y0). eapply step_determinstic. apply H1. apply H6. subst y0.
  pose (e t2). tauto.
Qed.

Definition normalizing {X:Type} (R:relation X) :=
  forall t, exists t',
    (multi R) t t' /\ normal_form R t'.

Lemma multistep_congr_1 :
  forall t1 t1' t2,
    t1 ==>* t1' ->
    P t1 t2 ==>* P t1' t2.

  intros. generalize dependent t2.
  elim H. intros; calculate_smallstep.
  intros. assert (P x t2 ==> P y t2). apply ST_Plus1. auto. eapply multi_step; eauto.
Qed.

Lemma multistep_congr_2 :
  forall t1 t2 t2',
    value t1 ->
    t2 ==>* t2' ->
    P t1 t2 ==>* P t1 t2'.

  intros. generalize dependent t1.
  elim H0. intros; apply multi_refl.
  intros. Check ST_Plus2.
  pose (ST_Plus2 _ _ _ H3 H). eapply multi_step; eauto.
Qed.


Theorem step_normalizing:
  normalizing step.

  unfold normalizing. intro.
  elim t.
  intro. exists (C n). split; [apply multi_refl |]. unfold normal_form. intro. inversion H. inversion H0.
  unfold normal_form. intros. destruct H. destruct H0. destruct H. destruct H0.
  Check strong_progress.
  pose (strong_progress x); pose (strong_progress x0).
  destruct o; destruct o0.
  inversion H3; inversion H4.
  subst x; subst x0. exists (C (n + n0)). split.  eapply multi_trans. eapply multistep_congr_1. apply H. eapply multi_trans. eapply multistep_congr_2. auto. apply H0. calculate_smallstep. intro. inversion H5. inversion H6.
  elim (H2 H4). elim (H1 H3). elim (H1 H3).
Qed.


Theorem eval__multistep :
  forall t n,
    t \\ n -> t ==>* C n.
  intros. elim H. intros; apply multi_refl.
  intros. eapply multi_trans. eapply multistep_congr_1; eauto.
  eapply multi_trans. eapply multistep_congr_2. apply v_const. eauto.
  eapply multi_step. apply ST_PlusConstConst. calculate_smallstep.
Qed.


Lemma step__eval :
  forall t t' n,
    t ==> t' ->
    t' \\ n ->
    t \\ n.

  intros. generalize dependent n.
  elim H. intros. inversion H0. apply E_Plus. apply E_Const. apply E_Const.
  intros. inversion H2. apply E_Plus. apply H1. auto. auto.
  intros. inversion H3. apply E_Plus. auto. apply H2; auto.
Qed.


Theorem multistep__eval :
  forall t t',
    normal_form_of t t' ->
    exists n, t' = C n /\ t \\ n.

  unfold normal_form_of. unfold step_normal_form. unfold normal_form.
  intros. destruct H. generalize dependent H0.
  elim H. intros.
  pose (strong_progress x). destruct o. inversion H1. exists n. split; [auto| apply E_Const].
  elim (H0 H1).
  intros. pose (H2 H3). destruct e. destruct H4. exists x0. split; auto.
  eapply step__eval; eauto.
Qed.


Theorem evalF__eval:
  forall t n,
    evalF t = n <->
    t \\ n.

  split. generalize dependent n.
  elim t; simpl; intros. subst n0; apply E_Const.
  subst n. apply E_Plus. apply H; auto.
  apply H0; auto.
  intro. elim H. simpl; auto.
  intros. simpl. auto.
Qed.

Module COMBINED.

  Inductive tm:Type :=
| C : nat -> tm
| P : tm -> tm -> tm
| ttrue : tm
| tfalse : tm
| tif : tm -> tm -> tm -> tm.
  Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n)
  | v_true : value (ttrue)
  | v_false : value (tfalse).

  Reserved Notation "t '==>' t'" (at level 40).

  Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst :
      forall n1 n2,
        P (C n1) (C n2) ==> C (n1 + n2)
  | ST_Plus1 :
      forall t1 t1' t2,
        t1 ==> t1' ->
        P t1 t2 ==> P t1' t2
  | ST_Plus2 :
      forall v1 t2 t2',
        value v1 ->
        t2 ==> t2' ->
        P v1 t2 ==> P v1 t2'
  | ST_IfTrue:
      forall t1 t2,
        tif ttrue t1 t2 ==> t1
  | ST_IfFalse :
      forall t1 t2,
        tif tfalse t1 t2 ==> t2
  | ST_If:
      forall t t' t1 t2,
        t ==> t' ->
        tif t t1 t2 ==> tif t' t1 t2

  where "t '==>' t'" := (step t t').

  Theorem cstep_deterministic:
    determinstic step.

    unfold determinstic.
    intros x y1 y2 h1. generalize dependent y2.
    elim h1. intros. inversion H. auto. inversion H3. inversion H4.
    intros. inversion H1. subst t1. inversion H. pose (H0 t1'0 H5). rewrite e; auto.
    subst t2. subst v1. inversion H4; subst t1; inversion H.
    intros. inversion H2. subst v1. subst t2. inversion H0. subst v1. inversion H; subst t1; inversion H6. rewrite (H1 t2'0 H7); auto.
    intros. inversion H. auto. inversion H4.
    intros. inversion H. auto. inversion H4.
    intros. inversion H1. subst t. inversion H. subst t. inversion H. rewrite (H0 t'0 H6). auto.
  Qed.

  Theorem not_strong_progress:
    exists c,
      ~ (value c) /\ ~(exists t, c ==> t).

    exists (tif (C 0) (C 0) (C 0)).

    split; intro. inversion H. inversion H. inversion H0. inversion H5.
  Qed.

  End COMBINED.

Inductive aval : aexp -> Prop :=
  av_num : forall n, aval (ANum n).

Reserved Notation "t '/' st '==>a' t'" (at level 40, st at level 39).

Inductive astep : state -> aexp -> aexp -> Prop :=
| AS_Id :
    forall st i,
      AId i / st ==>a ANum (st i)
| AS_Plus1 :
    forall st n1 n2,
      APlus (ANum n1) (ANum n2) / st ==>a ANum (n1 + n2)
| AS_Plus2 :
    forall st a1 a1' a2,
      a1 / st ==>a a1' ->
      APlus a1 a2 / st ==>a APlus a1' a2
| AS_Plus3 :
    forall st a1 a2 a2',
      aval a1 ->
      a2 / st ==>a a2' ->
      APlus a1 a2 / st ==>a APlus a1 a2'
| AS_Minus1 :
    forall st n1 n2,
      AMinus (ANum n1) (ANum n2) / st ==>a (ANum (minus n1 n2))
| AS_Minus2 :
    forall st v1 v1' v2,
      v1 / st ==>a v1' ->
      APlus v1 v2 / st ==>a APlus v1' v2
| AS_Minus3 :
    forall st v1 v2 v2',
      aval v1 ->
      v2 / st ==>a v2' ->
      APlus v1 v2 / st ==>a APlus v1 v2'
| AS_Mult1 :
    forall st n1 n2,
      AMult (ANum n1) (ANum n2) / st ==>a ANum ( n1 * n2)
| AS_Mult2 :
    forall st v1 v1' v2,
      v1 / st ==>a v1' ->
      AMult v1 v2 / st ==>a AMult v1' v2
| AS_Mult3 :
    forall st v1 v2 v2',
      aval v1 ->
      v2 / st ==>a v2' ->
      AMult v1 v2 / st ==>a AMult v1 v2'

where "t '/' st '==>a' t'" := (astep st t t').

Reserved Notation "t '/' st '==>b' t'" (at level 40, st at level 39).






Inductive bstep : state -> bexp -> bexp -> Prop :=
| BS_Eq :
    forall st n1 n2,
      (BEq (ANum n1) (ANum n2)) / st ==>b (if (eq_nat_dec n1 n2) then BTrue else BFalse)
| BS_Eq1 :
    forall st a1 a1' a2,
      a1 / st ==>a a1' ->
      BEq a1 a2 / st ==>b BEq a1' a2
| BS_Eq2 :
    forall st a1 a2 a2',
      aval a1 ->
      a2 / st ==>a a2' ->
      BEq a1 a2 /st ==>b BEq a1 a2'
| BS_LtEq1 :
    forall st n1 n2,
      BLe (ANum n1) (ANum n2) / st ==>b
          (if le_dec n1 n2 then BTrue else BFalse)
| BS_LtEq2 :
    forall st a1 a1' a2,
      a1 / st ==>a a1' ->
      BLe a1 a2 / st ==>b BLe a1' a2
| BS_LtEq3 :
    forall st a1 a2 a2',
      aval a1 ->
      a2 / st ==>a a2' ->
      BLe a1 a2 / st ==>b BLe a1 a2'
| BS_NotTrue :
    forall st,
      (BNot BTrue) / st ==>b BFalse
| BS_NotFalse :
    forall st,
      (BNot BFalse) / st ==>b BTrue
| BS_NotStep :
    forall st b1 b1',
      b1 / st ==>b b1' ->
      (BNot b1) / st ==>b (BNot b1')
| BS_AndTrueTrue:
    forall st,
      BAnd BTrue BTrue / st ==>b BTrue
| BS_AndTrueFalse:
    forall st,
      BAnd BTrue BFalse / st ==>b BFalse
| BS_AndFalse :
    forall st b2,
      BAnd BFalse b2 / st ==>b BFalse
| BS_AndTrueStep :
    forall st b2 b2',
      b2 / st ==>b b2' ->
      BAnd BTrue b2 / st ==>b BAnd BTrue b2'
| BS_AndStep :
    forall st b1 b1' b2,
      b1 / st ==>b   b1' ->
      BAnd b1 b2 / st ==>b BAnd b1' b2

where "t '/' st ==>b t'" := (bstep st t t').


Reserved Notation "t '/' st '==>' t' '/' st'"
         (at level 40, st at level 39, t' at level 39).

Inductive cstep : (com * state) -> (com * state) -> Prop :=
| CS_AssStep :
    forall st i x x',
      x / st ==>a x' ->
      (i ::= x) / st ==> (i ::= x') / st
| CS_Ass :
    forall st i n,
      (i ::= (ANum n)) / st ==> SKIP / (t_update st i n)
| CS_SeqStep1 :
    forall st post,
      (SKIP;; post) / st ==> post / st
| CS_SeqStep2 :
   forall st st' pre pre' post,
     pre / st ==> pre' / st' ->
     (pre;;post) / st ==> (pre' ;; post) / st'
| CS_IfTrue :
    forall c1 c2 st,
      (IFB BTrue THEN c1 ELSE c2 FI) / st ==> c1 / st
| CS_IfFalse :
    forall c1 c2 st,
      (IFB BFalse THEN c1 ELSE c2 FI) / st ==> c2 / st
| CS_IfStep :
    forall b b' c1 c2 st,
      b / st ==>b b' ->
      (IFB b THEN c1 ELSE c2 FI) / st ==> (IFB b' THEN c1 ELSE c2 FI) / st
| CS_IfWhile :
    forall b c st,
      (WHILE b DO c END) / st ==> (IFB b THEN (c ;; (WHILE b DO c END)) ELSE SKIP FI) / st

where "t '/' st '==>' t' '/' st'" := (cstep (t, st) (t', st')).

Module CImp.

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  (* New: *)
  | CPar : com -> com -> com.

Tactic Notation "com_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SKIP" | Case_aux c "::=" | Case_aux c ";"
  | Case_aux c "IFB" | Case_aux c "WHILE" | Case_aux c "PAR" ].

Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' b 'THEN' c1 'ELSE' c2 'FI'" :=
  (CIf b c1 c2) (at level 80, right associativity).
Notation "'PAR' c1 'WITH' c2 'END'" :=
  (CPar c1 c2) (at level 80, right associativity).

Inductive cstep : (com * state)  -> (com * state) -> Prop :=
    (* Old part *)
  | CS_AssStep : forall st i a a',
      a / st ==>a a' ->
      (i ::= a) / st ==> (i ::= a') / st
  | CS_Ass : forall st i n,
      (i ::= (ANum n)) / st ==> SKIP / (t_update st i n)
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st ==> c1' / st' ->
      (c1 ;; c2) / st ==> (c1' ;; c2) / st'
  | CS_SeqFinish : forall st c2,
      (SKIP ;; c2) / st ==> c2 / st
  | CS_IfTrue : forall st c1 c2,
      (IFB BTrue THEN c1 ELSE c2 FI) / st ==> c1 / st
  | CS_IfFalse : forall st c1 c2,
      (IFB BFalse THEN c1 ELSE c2 FI) / st ==> c2 / st
  | CS_IfStep : forall st b b' c1 c2,
      b /st ==>b b' ->
      (IFB b THEN c1 ELSE c2 FI) / st ==> (IFB b' THEN c1 ELSE c2 FI) / st
  | CS_While : forall st b c1,
      (WHILE b DO c1 END) / st ==>
               (IFB b THEN (c1;; (WHILE b DO c1 END)) ELSE SKIP FI) / st
    (* New part: *)
  | CS_Par1 : forall st c1 c1' c2 st',
      c1 / st ==> c1' / st' ->
      (PAR c1 WITH c2 END) / st ==> (PAR c1' WITH c2 END) / st'
  | CS_Par2 : forall st c1 c2 c2' st',
      c2 / st ==> c2' / st' ->
      (PAR c1 WITH c2 END) / st ==> (PAR c1 WITH c2' END) / st'
  | CS_ParDone : forall st,
      (PAR SKIP WITH SKIP END) / st ==> SKIP / st
  where " t '/' st '==>' t' '/' st' " := (cstep (t,st) (t',st')).


Definition cmultistep := multi cstep.

Notation " t '/' st '==>*' t' '/' st' " :=
   (multi cstep  (t,st) (t',st'))
   (at level 40, st at level 39, t' at level 39).


Definition par_loop : com :=
  PAR
    Y ::= ANum 1
    WITH
    WHILE (BEq (AId Y) (ANum 0))
    DO
    X ::= APlus (AId X) (ANum 1)
    END
    END.


Hint Constructors cstep astep bstep: cstep_def.

Ltac calculate_smallsteps base :=
  match goal with
      | [|- ?X ==>* ?X] => eapply multi_refl
      | _ => (eapply multi_step; [auto with base;fail | calculate_smallsteps base])
      | _ => idtac
  end.

  

Example par_loop_example_0 :
  exists st',
    par_loop / empty_state ==>* SKIP / st'
    /\ st' X = 0.
Proof.
  unfold par_loop.
  exists (t_update empty_state Y 1).
  split. eapply multi_step. apply CS_Par1. auto with cstep_def.
  eapply multi_step. apply CS_Par2. auto with cstep_def.
  eapply multi_step. apply CS_Par2. auto with cstep_def. unfold t_update. rewrite eq_id_dec_id.
  eapply multi_step. apply CS_Par2. eapply CS_IfStep. eapply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. eapply CS_IfFalse.
  eapply multi_step. auto with cstep_def.  apply multi_refl.
  unfold t_update. destruct (eq_id_dec Y X). inversion e. auto.
Qed.


Ltac expand x X :=
  match X with
    | 0 => x
    | ?y => (fun g => expand x;X g) 
  end.


Ltac cal_par_ k x X :=
  match goal with
    | [ |- ?Y ==>* ?Y] => apply multi_refl
    | _ => 
        match X with
          | 0 => k;eapply multi_step;eapply x;eauto with cstep_def;fail
          | 0 => k;eapply multi_step;eauto with cstep_def;fail
          | 0 => k;idtac
          | ?y => cal_par_ ltac:(k;eapply multi_step;[eapply x; eauto with cstep_def; fail | idtac]) y
          | ?y => cal_par_ ltac:(k;eapply multi_step;[eauto with cstep_def; fail | idtac]) y
          | _ => idtac
        end
  end.

Ltac cal_par x X := cal_par_ idtac.


Example par_loop_example_2 :
  exists st,
    par_loop / empty_state ==>* SKIP / st
    /\ st X = 2.

exists (t_update (t_update (t_update empty_state X 1) X 2) Y 1). split.
unfold par_loop.
cal_par CS_Par2 CS_Par2 CS_Par2 CS_Par2 CS_Par2 CS_Par2 CS_Par2 CS_Par2 CS_Par2 CS_Par2 CS_Par2 CS_Par2 CS_Par2 CS_Par2 0. unfold empty_state; unfold t_empty; simpl. unfold t_update.
destruct (eq_id_dec X Y). inversion e. destruct (eq_nat_dec 0 0).
eapply multi_step. eapply CS_Par2. eapply CS_IfTrue.
cal_par CS_Par2 CS_Par2 CS_Par2 0.
Abort.


Definition stack := list nat.
Definition prog := list sinstr.

Inductive stack_step : state -> prog * stack -> prog * stack -> Prop :=
  | SS_Push : forall st stk n p',
    stack_step st (SPush n :: p', stk)      (p', n :: stk)
  | SS_Load : forall st stk i p',
    stack_step st (SLoad i :: p', stk)      (p', st i :: stk)
  | SS_Plus : forall st stk n m p',
    stack_step st (SPlus :: p', n::m::stk)  (p', (m+n)::stk)
  | SS_Minus : forall st stk n m p',
    stack_step st (SMinus :: p', n::m::stk) (p', (m-n)::stk)
  | SS_Mult : forall st stk n m p',
    stack_step st (SMult :: p', n::m::stk)  (p', (m*n)::stk).

Theorem stack_step_deterministic :
  forall st,
    deterministic (stack_step st).
  unfold deterministic. intros st x y1 y2 h1.
  generalize dependent y2.
  elim h1. intros. inversion H. auto.
  intros. inversion H. auto.
  intros. inversion H. auto.
  intros. inversion H. auto.
  intros. inversion H. auto.
Qed.

Check s_compile.

Check aeval.

Definition stack_process (st : state) :=
  multi (stack_step st).

Definition compile_correctly :=
  forall a st l l',
    stack_process st ((s_compile a) ++ l', l) (l', aeval st a :: l).

Theorem compile_is_correct : compile_correctly.
  unfold compile_correctly.
  unfold stack_process.
  intro. elim a.
  simpl. intros. eapply multi_step. apply SS_Push. apply multi_refl.
  simpl. intros. eapply multi_step. apply SS_Load. apply multi_refl.
  intros. simpl. eapply multi_trans. SearchPattern (_ ++ _ ++ _ = _).
  rewrite <- app_assoc. apply H. rewrite <- app_assoc. eapply multi_trans. apply H0.
  simpl. eapply multi_step. apply SS_Plus. apply multi_refl.
  intros. simpl. eapply multi_trans. SearchPattern (_ ++ _ ++ _ = _).
  rewrite <- app_assoc. apply H. rewrite <- app_assoc. eapply multi_trans. apply H0.
  simpl. eapply multi_step. apply SS_Minus. apply multi_refl.
intros. simpl. eapply multi_trans. SearchPattern (_ ++ _ ++ _ = _).
  rewrite <- app_assoc. apply H. rewrite <- app_assoc. eapply multi_trans. apply H0.
  simpl. eapply multi_step. apply SS_Mult. apply multi_refl.

Qed.



