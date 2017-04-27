Require Import Maps.
Require Import Smallstep.
Require Import Types.

Module STLC.

  Inductive ty:Type :=
| TBool : ty
| TArrow : ty -> ty -> ty.

  Inductive tm: Type :=
  | tvar : id -> tm
  | tapp : tm -> tm -> tm
  | tabs : id -> ty -> tm -> tm
  | ttrue : tm
  | tfalse : tm
  | tif : tm -> tm -> tm -> tm.

  Definition x:= (Id 0).
  Definition y:= (Id 1).
  Definition z:= (Id 2).

  Hint Unfold x.
  Hint Unfold y.
  Hint Unfold z.

  (** [idB = \x:Bool. x] *)

Notation idB :=
  (tabs x TBool (tvar x)).

(** [idBB = \x:Bool->Bool. x] *)

Notation idBB :=
  (tabs x (TArrow TBool TBool) (tvar x)).

(** [idBBBB = \x:(Bool->Bool) -> (Bool->Bool). x] *)

Notation idBBBB :=
  (tabs x (TArrow (TArrow TBool TBool)
                      (TArrow TBool TBool))
    (tvar x)).

(** [k = \x:Bool. \y:Bool. x] *)

Notation k := (tabs x TBool (tabs y TBool (tvar x))).

(** [notB = \x:Bool. if x then false else true] *)

Notation notB := (tabs x TBool (tif (tvar x) tfalse ttrue)).

Inductive value : tm -> Prop :=
| v_true : value ttrue
| v_false : value tfalse
| v_abs : forall x T y, value (tabs x T y).

Hint Constructors value.

Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Fixpoint subst (x:id) (s:tm) (t:tm) : tm :=
  match t with
    | tvar x' => if (eq_id_dec x x') then s else t
    | tapp abs arg => tapp ([x := s] abs) ([x:=s] arg)
    | tabs x' T t' => if (eq_id_dec x x') then t else ([x := s] t')
    | ttrue => ttrue
    | tfalse => tfalse
    | tif a b c => tif ([x:=s]a) ([x:=s] b) ([x:=s]c)
  end
where "'[' x ':=' s ']' t" := (subst x s t).

Reserved Notation "t '==>' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
| ST_AppAbs :
    forall abs abs' arg,
      abs ==> abs' ->
      tapp abs arg ==> tapp abs' arg
| ST_AppArg :
    forall abs arg arg',
      value abs ->
      arg ==> arg' ->
      tapp abs arg ==> tapp abs arg'
| ST_Apply :
    forall arg x T t',
      value arg ->
      tapp (tabs x T t') arg ==> [x := arg] t' 
| ST_IfTrue :
    forall t1 t2,
      tif ttrue t1 t2 ==> t1
| ST_IfFalse :
    forall t1 t2,
      tif tfalse t1 t2 ==> t2
| ST_If :
    forall t t' t1 t2,
      t ==> t' ->
      tif t t1 t2 ==> tif t' t1 t2
where "t '==>' t'" := (step t t').

Hint Constructors step.

Notation multistep := (multi step).

Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

Hint Constructors multi.


Ltac stlc_step_cal :=
  match goal with
    | [ |- ?X ==>* ?X ] => eapply multi_refl
    | [ |- ?X ==>* ?Y ] => idtac "multi_step"; (try (simpl; rewrite eq_id_dec_id; auto)); eapply multi_step; [ eauto ; fail | stlc_step_cal]
    | [ |- _] => idtac "Try rewrite"; simpl; rewrite eq_id_dec_id; auto; stlc_step_cal
  end.

Lemma step_example1:
  (tapp idBB idB) ==>* idB.

  stlc_step_cal.
Qed.

  Lemma step_example2:
  (tapp idBB (tapp idBB idB)) ==>* idB.

    stlc_step_cal.
Qed.    



  Lemma step_example3:
  tapp (tapp idBB notB) ttrue ==>* tfalse.

    stlc_step_cal.
  Qed.

  Lemma step_example4:
    tapp idBB (tapp notB ttrue) ==>* tfalse.

    stlc_step_cal.
  Qed.

  Lemma step_example1' :
    (tapp idBB idB) ==>* idB.

    stlc_step_cal.
  Qed.

  Lemma step_example5:
    (tapp (tapp idBBBB idBB) idB) ==>* idB.

    stlc_step_cal.
  Qed.

  Definition context := partial_map ty.

  Reserved Notation "Gamma '|-' t '\in' T" (at level 40).

  Print partial_map.
  Print total_map.
  
  Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
              Gamma x = Some T ->
              Gamma |- tvar x \in T
  | T_Abs : forall Gamma x T11 T12 t12,
              (update Gamma x T11) |- t12 \in T12 ->
              Gamma |- (tabs x T11 t12) \in (TArrow T11 T12)
  | T_App : forall Gamma t1 t2 G T,
              Gamma |- t1 \in TArrow G T ->
              Gamma |- t2 \in G ->
              Gamma |- (tapp t1 t2) \in T
  | T_True : forall Gamma,
      Gamma |- ttrue \in TBool
  | T_False : forall Gamma,
      Gamma |- tfalse \in TBool
  | T_If : forall Gamma t t1 t2 T,
             Gamma |- t \in TBool ->
             Gamma |- t1 \in T -> Gamma |- t2 \in T ->
             Gamma |- (tif t t1 t2) \in T
  where "Gamma '|-' t '\in' T " := (has_type Gamma t T).


  Hint Constructors has_type.

  Hint Unfold update.
  Hint Unfold empty.
  Hint Unfold t_update.
  
  Ltac stlc_type_cal_ :=
    eauto using eq_id_dec_id; unfold update; unfold t_update; unfold empty; eauto using eq_id_dec_id.

  Ltac stlc_type_cal :=
    match goal with
      | [ |- ( ?x |- tvar _ \in _)] => eapply T_Var ;stlc_type_cal_; stlc_type_cal
      | [ |- ( _ |- (tabs _ _ _ ) \in _)] => eapply T_Abs ;stlc_type_cal_; stlc_type_cal
      | [ |- ( _ |- (tapp _ _ ) \in _)] => eapply T_App;stlc_type_cal_; stlc_type_cal
      | [ |- ( _ |- (tif _ _ _ ) \in _)] => eapply T_If ;stlc_type_cal_; stlc_type_cal
      | [ |- ( _ |- _ \in _)] => stlc_type_cal_; stlc_type_cal
      | _ => eauto
    end.
      
  Example typing_example_1:
    empty |- tabs x TBool (tvar x) \in TArrow TBool TBool.
  stlc_type_cal.
  Qed.

  Example typing_example_2:
    empty |- (tabs x TBool (tabs y (TArrow TBool TBool)
                                 (tapp (tvar y) (tapp (tvar y) (tvar x))))) \in
      (TArrow TBool (TArrow (TArrow TBool TBool) TBool)).

  Proof with stlc_type_cal.
    stlc_type_cal.
    rewrite eq_id_dec_id.
    destruct (eq_id_dec y x); eauto.
    inversion e.
Qed.

    Example typing_example_2_full :
    empty |-
  (tabs x TBool (tabs y (TArrow TBool TBool)
        (tapp (tvar y) (tapp (tvar y) (tvar x))))) \in
      (TArrow TBool (TArrow (TArrow TBool TBool) TBool)).

  repeat stlc_type_cal.
  rewrite eq_id_dec_id.
  destruct (eq_id_dec y x); eauto. inversion e.
  Qed.

  Example typing_example_3:
    exists T,
      empty |-
      (tabs x (TArrow TBool TBool)
            (tabs y (TArrow TBool TBool)
                  (tabs z TBool
                        (tapp (tvar y) (tapp (tvar x) (tvar z)))))) \in
        T.
  exists (TArrow (TArrow TBool TBool) (TArrow (TArrow TBool TBool) (TArrow TBool TBool))).
  stlc_type_cal.
  rewrite eq_id_dec_id.
  destruct (eq_id_dec z y); eauto. inversion e.
  rewrite eq_id_dec_id. destruct (eq_id_dec z x); eauto. inversion e.
  destruct (eq_id_dec y x); eauto.
  Qed.

  Example typing_nonexample_1:
    ~(exists T,
        empty |-
        (tabs x TBool)
          (tabs y TBool
                (tapp (tvar x) (tvar y))) \in
          T).

  intro.
  inversion H.  inversion H0;subst. inversion H6;subst. inversion H0; subst. inversion H3;subst.
  generalize H4; clear.
  unfold update; unfold t_update.
  intro. inversion H4; subst. clear H5. inversion H2; subst. rewrite eq_id_dec_id in H1.
  destruct (eq_id_dec y x); eauto; inversion H1.
  Qed.


  
Lemma cant_typed:
    forall G X,
      ~(TArrow G X = G). 

    intro. elim G.
    intros. intro. inversion H.
    intros. intro. inversion H1. subst X. elim (H _ H3).
  Qed.

  
  

  
  Example typing_nonexample_3:
    ~(exists S, exists T,
                  empty |-
                  (tabs x S
                        (tapp (tvar x) (tvar x))) \in
                    T).

  intro. inversion H. inversion H0. generalize H1; clear.
  intro. inversion H1; subst. unfold update in H5; unfold t_update in H5.
  inversion H5;subst. inversion H3; subst. inversion H6; subst. rewrite eq_id_dec_id in *. inversion H2; inversion H4; subst. elim (cant_typed _ _ H7).
  Qed.

End STLC.
