Require Import Coq.Arith.Arith.
Require Import SfLib.
Require Import Maps.
Require Import Imp.
Require Import Smallstep.

Hint Constructors multi.

Inductive tm:Type :=
| ttrue : tm
| tfalse : tm
| tif : tm -> tm -> tm -> tm
| tzero : tm
| tsucc : tm -> tm
| tpred : tm -> tm
| tiszero : tm -> tm.

Inductive bvalue : tm -> Prop :=
| bv_true : bvalue ttrue
| bv_false : bvalue tfalse.

Inductive nvalue : tm -> Prop :=
| nv_zero : nvalue tzero
| nv_succ : forall t, nvalue t -> nvalue (tsucc t).

Definition value (t: tm) := bvalue t \/ nvalue t.

Hint Constructors bvalue nvalue.
Hint Unfold value.
Hint Unfold update.

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      (tif ttrue t1 t2) ==> t1
  | ST_IfFalse : forall t1 t2,
      (tif tfalse t1 t2) ==> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      (tif t1 t2 t3) ==> (tif t1' t2 t3)
  | ST_Succ : forall t1 t1',
      t1 ==> t1' ->
      (tsucc t1) ==> (tsucc t1')
  | ST_PredZero :
      (tpred tzero) ==> tzero
  | ST_PredSucc : forall t1,
      nvalue t1 ->
      (tpred (tsucc t1)) ==> t1
  | ST_Pred : forall t1 t1',
      t1 ==> t1' ->
      (tpred t1) ==> (tpred t1')
  | ST_IszeroZero :
      (tiszero tzero) ==> ttrue
  | ST_IszeroSucc : forall t1,
       nvalue t1 ->
      (tiszero (tsucc t1)) ==> tfalse
  | ST_Iszero : forall t1 t1',
      t1 ==> t1' ->
      (tiszero t1) ==> (tiszero t1')

where "t1 '==>' t2" := (step t1 t2).

Hint Constructors step.

Check normal_form.

Notation step_normal_form:= (normal_form step).

Definition stuck (t:tm) : Prop :=
  step_normal_form t /\ ~(value t).

Hint Unfold stuck.

Example some_term_is_stuck :
  exists t, stuck t.
exists (tsucc ttrue).
unfold stuck. split. unfold normal_form. intro. inversion H. inversion H0. inversion H2.
intro. inversion H. inversion H0. inversion H0. inversion H2.
Qed.

Lemma value_is_nf:
  forall t,
    value t -> step_normal_form t.
  intros. unfold normal_form. elim H; intros.
  intro. inversion H0. inversion H1. subst t. inversion H3.
  inversion H1. subst t. inversion H3.
  elim H0. intro. inversion H1. inversion H2.
  intros. intro. inversion H3. inversion H4. eauto.
Qed.



Ltac deterministic_try_contra :=
  (match goal with
     | [H1 : ttrue = ?X1 |- _] => subst X1
     | [H1 : ?X1 = ttrue |- _] => subst X1
     | [H1 : tfalse = ?X1 |- _] => subst X1
     | [H1 : ?X1 = tfalse |- _] => subst X1
     | [H1 : tzero = ?X1 |- _] => subst X1
     | [H1 : ?X1 = tzero |- _] => subst X1
     | [H1 : tsucc ?X2 = ?X1 |- _] => subst X1
     | [H1 : ?X1 = tsucc ?X2 |- _] => subst X1
     | [H : ttrue ==> ?X |- _] => inversion H
     | [H : tfalse ==> ?X |- _] => inversion H
     | [H : tzero ==> ?X |- _] => inversion H
     | _ => fail
   end); deterministic_try_contra.


Ltac is_nvalue_contra what proof :=
  match goal with
    | [H : what ==> ?X |- _] =>
      assert (exists x, what ==> x) as CONTRA; eauto;
      elim ((value_is_nf _ (or_intror _ proof)) CONTRA)
  end.

Theorem step_deterministic :
  deterministic step.

  unfold deterministic. intros x y1 y2 h1.
  generalize dependent y2.
  elim h1. intros. inversion H. auto. deterministic_try_contra.
  intros. inversion H; try auto; try deterministic_try_contra.
  intros. inversion H1; try eauto; try deterministic_try_contra. rewrite (H0 t1'0 H6). auto.
  intros. inversion H1; try eauto; try deterministic_try_contra.  rewrite (H0 t1'0 H3); auto.
  intros. inversion H; try eauto; try deterministic_try_contra.
  intros. inversion H0. auto. is_nvalue_contra (tsucc t1) (nv_succ _ H).
  intros. inversion H1; try eauto; try deterministic_try_contra. subst t1. subst t0. is_nvalue_contra (tsucc y2) (nv_succ _ H3). subst. rewrite (H0 _ H3); auto.
  intros. inversion H; try eauto; try deterministic_try_contra.
  intros. inversion H0;try eauto; try deterministic_try_contra. subst. is_nvalue_contra (tsucc t1) (nv_succ _ H).
  intros. inversion H1; try eauto; try deterministic_try_contra. subst. is_nvalue_contra (tsucc t0) (nv_succ _ H3). rewrite (H0 _ H3); auto.
Qed.

Inductive ty : Type :=
| TBool : ty
| TNat : ty.

Reserved Notation "'|-' t '\in' T" (at level 40).

Inductive has_type : tm -> ty -> Prop :=
| T_True :
  |- ttrue \in TBool
| T_False :
  |- tfalse \in TBool
| T_If :
    forall t1 t2 t3 T,
      |- t1 \in TBool ->
      |- t2 \in T ->
      |- t3 \in T ->
      |- (tif t1 t2 t3) \in T
| T_Zero :
  |- tzero \in TNat
| T_Succ :
    forall x,
      |- x \in TNat ->
               |- (tsucc x) \in TNat
| T_Pred :
    forall x,
      |- x \in TNat ->
               |- tpred x \in TNat
| T_IsZero:
    forall x,
      |- x \in TNat ->
               |- tiszero x \in TBool

where "'|-' t '\in' T" := (has_type t T).

Hint Constructors has_type.

Example has_type_1:
|- tif tfalse tzero (tsucc tzero) \in TNat.

eauto.
Qed.


Example has_type_2 :
  ~ (|- tif tfalse tzero ttrue \in TBool).

intro. inversion H. inversion H5.
Qed.

Lemma succ_type_injective :
  forall n,
    |- tsucc n \in TNat ->
                   |- n \in TNat.
  intros. inversion H. auto.
Qed.

Lemma bool_canonical :
  forall t,
    |- t \in TBool -> value t -> bvalue t.

  unfold value.
  intros. destruct H0. auto. inversion H0. subst. inversion H. subst t. inversion H.
Qed.

Lemma nat_canonical :
  forall t,
    |- t \in TNat ->
             value t -> nvalue t.

  unfold value.
  intros. destruct H0; auto. inversion H0; subst t; inversion H.
Qed.


Ltac it_is_nf :=
  try subst; (match goal with
                | [H : ttrue ==> ?X |- _] => inversion H
                | [H : tfalse ==> ?X |- _] => inversion H
                | [H : tzero ==> ?X |- _] => inversion H
                | _ => fail
              end); deterministic_try_contra.



Theorem progress:
  forall t T,
    |- t \in T ->
             value t \/ exists t', t ==> t'.

  intros. elim H. left; auto. left; auto.
  intros. destruct H1. inversion H0. right. exists t2; auto.
  right. exists t3; auto. subst. inversion H1; inversion H9. subst. inversion H1. inversion H7. inversion H7. inversion H1. right. exists (tif x t2 t3). auto.
  left; auto.
  intros. destruct H1. left. inversion H1. inversion H2. subst x. inversion H0. subst. inversion H0. auto. right. inversion H1. exists (tsucc x0); auto.
  intros. destruct H1. destruct H1. inversion H1; subst; inversion H0. destruct H1. right. exists tzero; auto. right. exists t0; auto. inversion H1. right. exists (tpred x0); auto.
  intros. destruct H1. destruct H1. inversion H1; subst; inversion H0.
  destruct H1. right. exists ttrue. auto. right. exists tfalse. auto.
  right. inversion H1. exists (tiszero x0); auto.
Qed.


Theorem preservation :
  forall t t' T,
    |- t \in T ->
             t ==> t' ->
             |- t' \in T.

  intros t t' T h1. generalize dependent t'.
  elim h1. intros; it_is_nf. intros; it_is_nf.
  intros. inversion H5; subst; auto.
  intros; it_is_nf.
  intros. inversion H1; subst; auto.
  intros. inversion H1; subst; auto. eapply succ_type_injective. auto.
  intros. inversion H1; subst; auto.
Qed.

Definition multistep := (multi step).

Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

Lemma preservation' :
  forall t t' T,
    |- t \in T ->
             t ==>* t' ->
             |- t' \in T.
  unfold multistep.
  intros. generalize dependent T.
  elim H0. auto.
  intros. apply H2. eapply preservation; eauto.
Qed.


Corollary soundness :
  forall t t' T,
    |- t \in T ->
             t ==>* t' ->
             ~(stuck t').
  intros. pose (preservation' _ _ _ H H0).
  pose (progress _ _ h).
  unfold stuck. unfold normal_form.
  intro. destruct H1.
  tauto.
Qed.

Tactic Notation "print_goal" := match goal with [|- ?x] => idtac x end.

Tactic Notation "normalize" :=
  repeat (print_goal ; eapply multi_step ;
          [ (eauto 10; fail) | (instantiate; simpl)]);
  apply multi_refl.

(* SUbject Expansion can be easily proved by contradiction*)
(* WHile it is intuitive logic, so... By induction !*)

Theorem subject_expansion_false:
  ~(forall t t' T,
      t ==> t' ->
      |- t' \in T ->
                |- t \in T).

  intro.
  pose (ST_IfTrue tzero ttrue).
  pose (H _ _ _ s T_Zero).
  inversion h. inversion H6.
Qed.

(*
Definition progress_bigstep :=
  forall t t' T,
    |- t \in T ->
    t \\ t' ->
     value t'

Definition preservation_bigstep :=
forall t t' T,
|- t \in T ->
t \\ t' ->
|- t' \in T.

*)