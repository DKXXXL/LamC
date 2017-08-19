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




Lemma app_preserv_snd:
    forall t g x G T C,
        C |- tabs x G t \in TArrow G T ->
        empty |- g \in G ->
        C |- [x := g] t \in T.

    intro. elim t; intros. unfold subst in *.
    destruct (eq_id_dec); subst. inversion H; subst.
    unfold update in *; unfold t_update in *. inversion H3; subst.
    rewrite eq_id_dec_id in H4. inversion H4; subst; auto.

    Abort.

Lemma context_empty:
    forall g T,
    empty |- g \in T -> 
    (forall C,
        C |- g \in T).
    
    intro. elim g; intros; unfold empty in *; unfold t_empty in *.

    inversion H; subst. inversion H2.
    inversion H1; subst. 
    pose (H _ H5); pose (H0 _ H7).
    eauto.

    inversion H0; subst. unfold update in *; unfold t_update in *.    
Abort.

Inductive occurs_free: id -> tm -> Prop :=
    | occurs_free_var : 
        forall i,
            occurs_free i (tvar i)
    | occurs_free_app_1 :
        forall i lamb arg,
            occurs_free i lamb ->
            occurs_free i (tapp lamb arg)
    | occurs_free_app_2 :
        forall i lamb arg,
            occurs_free i arg ->
            occurs_free i (tapp lamb arg)
    | occurs_free_abs :
        forall i x T t,
            occurs_free i t ->
            i <> x ->
            occurs_free i (tabs x T t)
    | occurs_free_if0 :
        forall i t t1 t2,
            occurs_free i t ->
            occurs_free i (tif t t1 t2)
    | occurs_free_if1 :
        forall i t t1 t2,
            occurs_free i t1 ->
            occurs_free i (tif t t1 t2)
    | occurs_free_if2 :
        forall i t t1 t2,
            occurs_free i t2 ->
            occurs_free i (tif t t1 t2).

Hint Constructors occurs_free.


Theorem occurs_dec:
    forall x i,
    {occurs_free i x} + {~ (occurs_free i x)}.

    intro. elim x0; intros.
    destruct (eq_id_dec i i0); subst.
    left; auto. right; intro.
    inversion H; subst. destruct (n eq_refl).
    
    destruct (H i). left; auto.
    destruct (H0 i). left; auto.
    right. intro. inversion H1; subst; tauto.

    destruct (H i0). destruct (eq_id_dec i0 i); subst.
    right; intro. inversion H0; subst. destruct (H6 eq_refl).
    left; try auto. right; intro. inversion H0; subst. destruct (n H4).

    right; intro. inversion H.
    right; intro. inversion H.

    destruct (H i). left; auto.
    destruct (H0 i). left; auto.
    destruct (H1 i). left; auto.
    right; intro. inversion H2; subst. 
    destruct (n H5). destruct (n0 H5). destruct (n1 H5).

Qed.

Lemma 



    










