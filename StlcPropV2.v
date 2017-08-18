Require Import SfLib.
Require Import Maps.
Require Import Types.
Require Import Stlc.
Require Import Smallstep.

Module STLCPROP.
Import STLC.

Lemma canonical_forms_bool :
forall t,
    empty |- t \in TBool ->
    value t ->
    (t = ttrue) \/ (t = tfalse).

    intros.
    destruct t; inversion H0; try tauto.
    inversion H.
Qed.


Lemma canonical_forms_fun :
forall t T1 T2,
    empty |- t \in (TArrow T1 T2) ->
    value t ->
    exists x u, t = tabs x T1 u.

    intros. 
    destruct t; inversion H0; try tauto; try (inversion H; fail).
    exists i; exists t0. inversion H; auto.

Qed.


Theorem progress :
forall t T,
    empty |- t \in T ->
    value t \/ exists t', t ==> t'.

    intro. elim t; intros.
    inversion H. inversion H2.
    inversion H1. 
    destruct (H (TArrow G T) H5);
    destruct (H0 G H7); subst t0; subst t1; subst T.
    inversion H8; inversion H9; subst t2; subst t3; try (try (inversion H5); try (inversion H1); fail).
    inversion H7; subst G.   
    right.  exists ([x0 := ttrue] y0 ). auto.
    right; exists ([x0 := tfalse] y0); auto.
    right; exists( [x0 := tabs x1 T1 y1] y0); auto.
    destruct H9. right; exists (tapp t2 x0); auto.
    destruct H8. right; exists (tapp x0 t3); auto.
    destruct H8. right; exists (tapp x0 t3); auto.
    left; auto.
    left; auto. left ;auto.
    right. inversion H2; subst t0; subst t1; subst t2; subst T.
    destruct (H TBool H7).
    inversion H3; try (subst t3; inversion H7).
    exists t4; auto. exists t5; auto.
    destruct H3. exists (tif x0 t4 t5); auto.
Qed.




Theorem preservation :
forall t t' T,
    empty |- t \in T ->
    t ==> t' ->
    empty |- t' \in T.

    intro.
    elim t.
    intros. inversion H0. intros. inversion H2. subst abs; subst arg.
    inversion H1. subst t0; subst t1; subst T0. pose(H abs' (TArrow G T) H8 H6).
    eauto.
    subst t1; subst t0; subst t'.
    inversion H5; subst abs. inversion H1; inversion H8.
    inversion H1; inversion H8.
    inversion H1. subst t1;subst t2; subst T1. 
    pose (H0 _ _ H10 H7). eauto.
Abort.

Lemma app_preserv:
forall t g x G T,
    empty |- tabs x G t \in TArrow G T ->
    empty |- g \in G ->
    empty |- [x := g] t \in T.

    intro. elim t.
    intros. inversion H; subst; unfold subst in *; unfold update in *; unfold t_update in *.
    destruct (eq_id_dec); subst. inversion H; subst. unfold update in *; unfold t_update in *.
    inversion H4; subst. rewrite eq_id_dec_id in H5. inversion H5; subst; auto.
    inversion H3; subst.  destruct eq_id_dec ; subst; try contradict. destruct (n eq_refl).
    auto.

    intros. change (empty |- tapp ([x0 := g] t0) ([x0 := g] t1) \in T).
    inversion H1; subst. inversion H5; subst. pose (T_Abs _ _ _ _ _ H7).
    pose (H _ _ _ _ h H2). 
    pose (T_Abs _ _ _ _ _ H9).
    pose (H0 _ _ _ _ h1 H2). eauto.

    intros. remember T. generalize Heqt2.
    elim T; intros; subst. inversion H0.
    Abort.







