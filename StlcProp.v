Require Import SfLib.
Require Import Maps.
Require Import Types.
Require Import Stlc.
Require Import Smallstep.

Module STLCPROP.
  Import STLC.

  Lemma canonical_forms_bool :
    forall t,
      empty |-
      t \in TBool ->
            value t ->
            (t = ttrue) \/ (t = tfalse).
    intros. inversion H0; subst; eauto.
    inversion H.
  Qed.

  Lemma canonical_forms_fun :
    forall t T1 T2,
      empty |-
      t \in (TArrow T1 T2) ->
            value t ->
            exists x u, t = tabs x T1 u.

    intros. inversion H0; subst; eauto. inversion H. inversion H.
    exists x0; exists y0.
    inversion H; subst; auto.
  Qed.

  Theorem progress :
    forall t T,
      empty
      |- t \in T ->
               value t \/ (exists t', t ==> t').
    intro. elim t; eauto.
    intros. inversion H; subst. unfold empty in H2. unfold t_empty in H2. inversion H2.
    intros. right. inversion H1; eauto; subst. destruct (H _ H5); destruct (H0 _ H7). inversion H2; subst. inversion H5. inversion H5. exists ([x0 := t1] y0); eauto.
    inversion H3; subst. exists (tapp t0 x0); eauto.
    inversion H2; subst. exists (tapp x0 t1); eauto.
    inversion H2; subst. exists (tapp x0 t1); eauto.
    intros. right. inversion H2; subst. destruct (H _ H7). inversion H3; subst; (try inversion H7). exists t1; eauto. exists t2; eauto. inversion H3. exists (tif x0 t1 t2); eauto.
  Qed.

  (* The elim/induction tactic will delete some important information
so we have to use remember to record these information
but it's a working around, which shouldn't exists at all
While induction on term, the information would not be deleted
*)

  

  Inductive appears_free_in : id -> tm -> Prop :=
  | afi_var : forall x,
                appears_free_in x (tvar x)
  | afi_abs : forall x y T t,
                x <> y ->
                appears_free_in x t ->
                appears_free_in x (tabs y T t)
  | afi_app1 : forall x abs arg,
                appears_free_in x abs ->
                appears_free_in x (tapp abs arg)
  | afi_app2 : forall x abs arg,
                 appears_free_in x arg ->
                 appears_free_in x (tapp abs arg)
  | afi_if1 : forall x t t1 t2,
                appears_free_in x t ->
                appears_free_in x (tif t t1 t2)
  | afi_if2 : forall x t t1 t2,
                appears_free_in x t1 ->
                appears_free_in x (tif t t1 t2)
  | afi_if3 : forall x t t1 t2,
                appears_free_in x t2 ->
                appears_free_in x (tif t t1 t2).

  Hint Constructors appears_free_in.

  Definition closed (t:tm) :=
    forall x, ~(appears_free_in x t).

  Lemma free_in_context :
    forall x t T Gamma,
      appears_free_in x t ->
      Gamma
      |- t \in T ->
               exists T', Gamma x = Some T'.
    intros x0 t T Gamma h. generalize dependent T. generalize dependent Gamma.
    elim h; eauto.
    intros. inversion H; subst. exists T; eauto.
    intros. inversion H2; subst. destruct (H1 _ _ H8). unfold update in *. unfold t_update in *.
    destruct (eq_id_dec y0 x1); subst. elim (H eq_refl). exists x2; auto.
    intros. inversion H1; subst.  eauto.
    intros. inversion H1; subst. eauto.
    intros. inversion H1; subst. eauto.
    intros. inversion H1;subst. eauto.
    intros. inversion H1;subst;eauto.
  Qed.

  Corollary typable_empty__closed:
    forall t T,
      empty |-
      t \in T ->
            closed t.

    intros. unfold closed. intros x0 h.
    destruct (free_in_context _ _ _ _ h H). unfold empty in *. unfold t_empty in *.
    inversion H0.
  Qed.

  Lemma context_invariance :
    forall G G' t T,
      G
      |- t \in T ->
               (forall x, appears_free_in x t -> G x = G' x) ->
               G'
               |- t \in T.

    intros G G' t T h.
    generalize dependent G'.
    elim h; eauto.
    intros. eapply T_Var. rewrite <- H. symmetry. eauto.
    intros.  eapply T_Abs. eapply H0. intros. unfold update;unfold t_update.
    destruct (eq_id_dec x0 x1); subst; auto.
    intros. eapply T_App. eauto. eapply H2. intros. eauto.
    intros. eapply T_If; eauto.
  Qed.

  Ltac general_val_ X u v :=
    match v with
      | 0 => X;(generalize dependent u)
      | _ => general_val_ ltac:(X; generalize dependent u) v
    end.

  Ltac glize := general_val_ idtac.
  
  Lemma substitution_preserves_typing :
    forall G x U t v T,
      update G x U
      |- t \in T ->
               empty
               |- v \in U ->
                        G |- [x:=v]t \in T.
    intros G x U t.
    glize G x U 0.
    elim t. simpl. intros. destruct (eq_id_dec x0 i). inversion H;subst. unfold update in *; unfold t_update in *; rewrite eq_id_dec_id in *. inversion H3; subst. eapply context_invariance. eauto. intros. pose (typable_empty__closed _ _ H0). unfold closed in *. elim (c _ H1).
    eapply context_invariance. apply H. unfold update; unfold t_update. intro. destruct (eq_id_dec x0 x1); subst. intros. inversion H1; subst. elim (n eq_refl). auto.
    intros. simpl. inversion H1; subst. pose (H _ _ _ _ _ H6 H2). pose (H0 _ _ _ _ _ H8 H2). eauto.
    intros. simpl. destruct (eq_id_dec x0 i). inversion H0; subst. eapply T_Abs. eapply context_invariance. eauto. unfold update; unfold t_update. intro. destruct (eq_id_dec i x0). auto. auto.
    inversion H0; subst. Print T_Abs. cut (update G i t0 |- [x0 := v]t1 \in T12). eauto.
    eapply H. cut (update (update G i t0) x0 U |- t1 \in T12). eauto.
    assert (update (update G x0 U) i t0 = update (update G i t0) x0 U). SearchPattern (update _ _ _ = _). apply update_permute. auto. rewrite <- H2. auto. auto.
    intros. simpl. inversion H; subst. eauto.
    intros. simpl. inversion H; subst. eauto.
    intros. simpl. inversion H2; subst. eauto.
  Qed.


  
  Theorem preservation :
    forall t t' T,
      empty
      |- t \in T ->
               t ==> t' ->
               empty
               |- t' \in T.

    intro. elim t; intros. inversion H0.
    inversion H1; subst. inversion H2; subst. pose (H _ _ H6 H7). Check T_App. apply (T_App _ _ _ _ _ h H8).
    pose (H0 _ _ H8 H9). Check T_App. apply (T_App _ _ _ _ _ H6 h). eapply substitution_preserves_typing. inversion H6; subst. eauto. eauto.
    inversion H1. inversion H0. inversion H0. inversion H3; subst; inversion H2; subst; eauto.
  Qed.

  Print has_type.

  Theorem preservation_not_expandable:
    ~ (forall t t' T,
         empty
         |- t' \in T ->
                   t ==> t' ->
                   empty
                   |- t \in T).
    intro.
    Print tm.
    pose (H (tif ttrue ttrue (tabs y TBool (tvar y)))
            ttrue
            TBool).
    Print has_type.
    pose (h (T_True _ )).
    assert (tif ttrue ttrue (tabs y TBool (tvar y)) ==> ttrue).
    eauto.
    pose (h0 H0). inversion h1; subst. inversion H8.
  Qed.


  Definition stuck (t:tm) : Prop :=
    (normal_form step) t /\ ~(value t).

  Corollary preservation' :
    forall t t' T,
      empty
      |- t \in T ->
               t ==>* t' ->
               empty
               |- t' \in T.

    intros.  induction H0. auto.
    apply IHmulti. eapply preservation; eauto.
  Qed.


  Corollary soundness:
    forall t t' T,
      empty |- t \in T ->
                     t ==>* t' ->
                     ~(stuck t').

    intros.
    pose (progress _ _ (preservation' _ _ _ H H0)).
    unfold stuck; unfold normal_form. intro.
    destruct H1. destruct o; eauto.
  Qed.

  Theorem types_uniqueness :
    forall t G T1 T2,
      G |- t \in T1 ->
                 G |- t \in T2 ->
                            T1 = T2.

    intros t.
    elim t. intros. inversion H; subst. inversion H0; subst. rewrite H3 in H4. inversion H4; auto.
    intros. inversion H1; inversion H2;subst. pose (H _ _ _ H6 H12). inversion e. auto.
    intros. inversion H0; inversion H1; subst. rewrite (H _ _ _ H7 H13). auto.
    intros. inversion H; inversion H0; eauto.
    intros. inversion H; inversion H0; eauto.
    intros. inversion H2; inversion H3; subst. eauto.
  Qed.


(* Very first Verified Intepreter in my LIFE.
STLC with Arithmetic 
It is the very prototype. 

I will make it compiled.
*)
  
  Module STLCARITH.
    Inductive ty : Type :=
  | TArrow : ty -> ty -> ty
  | TNat : ty.

    Inductive tm:Type :=
    | tvar : id -> tm
    | tapp : tm -> tm -> tm
    | tabs : id -> ty -> tm -> tm
    | tnat : nat -> tm
    | tsucc : tm -> tm
    | tpred : tm -> tm
    | tmult : tm -> tm -> tm
    | tif0 : tm -> tm -> tm -> tm.



    