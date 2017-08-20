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


Lemma non_occur_context_rm:
    forall v x i T U,
        update U i x |- v \in T ->
        ~occurs_free i v ->
        U |- v \in T.
    
    intro. elim v; intros.

    inversion H; subst; unfold update in *; unfold t_update in *; subst.
    destruct eq_id_dec; subst. destruct (H0 (occurs_free_var i)).
    auto.

    inversion H1; subst. 
    pose (contrapositive _ _ (occurs_dec _ _) (occurs_free_app_1 i t t0)).
    pose (contrapositive _ _ (occurs_dec _ _) (occurs_free_app_2 i t t0)).  
    pose (n H2) as h1; pose (n0 H2) as h2. eauto.
    
    inversion H0; subst. 
    destruct (eq_id_dec i0 i); subst.
    rewrite update_shadow in H7. eauto.
    rewrite update_permute in H7. 
    destruct (occurs_dec  t0 i0). 
    pose (occurs_free_abs i0 i t _ o n). destruct (H1 o0).
    pose (H _ _ _ _ H7 n0).
    eapply T_Abs; eauto. auto.

    inversion H; subst. auto.
    inversion H; subst. auto.

    inversion H2; subst.
    pose (contrapositive _ _ (occurs_dec _ _) (occurs_free_if0 i t t0 t1)).
    pose (contrapositive _ _ (occurs_dec _ _) (occurs_free_if1 i t t0 t1)).
    pose (contrapositive _ _ (occurs_dec _ _) (occurs_free_if2 i t t0 t1)).
    pose (H _ _ _ _ H8 (n H3)).
    pose (H0 _ _ _ _ H10 (n0 H3)).
    pose (H1 _ _ _ _ H11 (n1 H3)).
    eauto.
Qed.

(*
Lemma app_preserv_snd:
forall t g x G T,
    empty |- tabs x G t \in TArrow G T ->
    empty |- g \in G ->
    empty |- [x := g] t \in T.

intro. elim t; intros. unfold subst in *.
destruct (eq_id_dec); subst. inversion H; subst.
unfold update in *; unfold t_update in *. inversion H3; subst.
rewrite eq_id_dec_id in H4. inversion H4; subst; auto.

inversion H; subst. 
destruct (occurs_dec (tvar i) x0). inversion o; subst.
destruct (n eq_refl). eapply non_occur_context_rm; eauto.

change (empty |- tapp ([x0 := g] t0) ([x0 := g] t1) \in T ).
inversion H1; subst. inversion H5;subst. eapply  T_App.
eapply H. eauto. eauto. eauto.

inversion H0; subst. inversion H4; subst.
change (empty |- (if (eq_id_dec x0 i) then tabs i t0 t1 else tabs i t0 ([x0 := g] t1)) \in TArrow t0 T12).
destruct (eq_id_dec x0 i); subst. rewrite update_shadow in H8. eauto.
rewrite update_permute in H8; auto.
pose (T_Abs _ _ _ _ _ H8).
destruct (occurs_dec (tabs x0 G t1) i); subst.
inversion o; subst. 
Abort.
*)

(*
    inversion H0; subst. 
    inversion H4; subst.
    change (U |- (if (eq_id_dec x0 i) then tabs i t0 t1 else tabs i t0 ([x0 := g] t1)) \in TArrow t0 T12).
    destruct (eq_id_dec x0 i); subst. 
    rewrite update_shadow in H8. eauto.
    rewrite update_permute in H8; auto.
    pose (T_Abs _ _ _ _ _ H8).
    pose (H _ _ _ _ _ h H1). eauto.

*)

Lemma app_preserv_snd:
forall t g x G T U,
    U |- tabs x G t \in TArrow G T ->
    empty |- g \in G ->
    U |- [x := g] t \in T.

intro. elim t; intros.

    Focus 3.
    inversion H0; subst. 
    inversion H4; subst.
    change (U |- (if (eq_id_dec x0 i) then tabs i t0 t1 else tabs i t0 ([x0 := g] t1)) \in TArrow t0 T12).
    destruct (eq_id_dec x0 i); subst. 
    rewrite update_shadow in H8. eauto.
    rewrite update_permute in H8; auto.
    pose (T_Abs _ _ _ _ _ H8).
    pose (H _ _ _ _ _ h H1). eauto.
Abort.



Lemma occurs_free_non_empty_ctx:
forall i x T G,
    occurs_free i x ->
    G |- x \in T ->
    (exists V, G i = Some V).

intros i x T G h. intros.

generalize dependent T; generalize dependent G.
elim h; subst; intros.
inversion H; subst. exists T; auto.

inversion H1; subst. eauto.

inversion H1; subst. eauto.

inversion H2; subst. destruct (H0 _ _ H8); subst.
unfold update in *; unfold t_update in *. destruct (eq_id_dec x0 i0); try contradict; try auto.
symmetry in e. destruct (H1 e). exists x1; auto.

inversion H1; subst. eauto.
inversion H1; subst. eauto.
inversion H1; subst. eauto.

Qed.


Definition closed (t:tm) := 
forall x, ~ occurs_free x t .



Lemma empty_closed:
    forall x T,
        empty |- x \in T ->
        closed x.
    
    unfold closed.

    intros x T h i h1.
    generalize dependent T.
    elim h1; intros; subst.
    
    inversion h; subst. inversion H1.

    inversion h; subst. eauto.
    inversion h; subst. eauto.

    inversion h; subst. 
    destruct (occurs_free_non_empty_ctx _ _ _ _ H H7).
    unfold update in *; unfold t_update in *.
    destruct (eq_id_dec x0 i0). symmetry in e. destruct (H1 e).
    inversion H2.

    inversion h; subst. eauto.
    inversion h; subst. eauto.
    inversion h; subst. eauto.

Qed.

Lemma closed_infective_app:
    forall x y,
    closed (tapp x y) ->
    closed x /\ closed y.

    unfold closed; split; intros; intro.
    pose (occurs_free_app_1 x1 x0 y0 H0).
    destruct (H x1 o).
    pose (occurs_free_app_2 x1 x0 y0 H0).
    destruct (H x1 o).
Qed.


Inductive Ctx_len: context -> nat -> Prop :=
    |  Ctx_empty : Ctx_len empty 0
    |  Ctx_update :
        forall i x n U,
            Ctx_len U n ->
            Ctx_len (update U i x) (S n).


Lemma non_occur_context_add:
    forall v x i T U,
        U |- v \in T ->
        ~occurs_free i v ->
        update U i x |- v \in T.

    intro v; elim v; intros.
    eapply T_Var. unfold update; unfold t_update.
    destruct (eq_id_dec i0 i); subst. 
    destruct (H0 (occurs_free_var _)).
    inversion H; subst. auto.

    inversion H1; subst.
    pose (contrapositive _ _ (occurs_dec _ _) (occurs_free_app_1 i t t0)).
    pose (contrapositive _ _ (occurs_dec _ _) (occurs_free_app_2 i t t0)).
    eapply T_App; eauto.

    inversion H0; subst.
    eapply T_Abs.
    
    destruct (eq_id_dec i0 i); subst.
    rewrite update_shadow. auto.
    destruct (occurs_dec t0 i0).
    
    pose (occurs_free_abs _ i t _ o n).
    destruct (H1 o0). pose (H x0 i0 _ _ H7 n0).
    rewrite update_permute. auto. auto.

    inversion H; subst. eauto.
    inversion H; subst. eauto.
    pose (contrapositive _ _ (occurs_dec _ _) (occurs_free_if0 i t t0 t1)).
    pose (contrapositive _ _ (occurs_dec _ _) (occurs_free_if1 i t t0 t1)).
    pose (contrapositive _ _ (occurs_dec _ _) (occurs_free_if2 i t t0 t1)).
    pose (n H3); pose (n0 H3); pose (n1 H3).
    inversion H2; subst. eauto.

Qed.

Theorem context_invariance:
    forall x (G G' : context) T,
        G |- x \in T ->
        (forall i, occurs_free i x -> G i = G' i) ->
        G' |- x \in T.
    
    intro x.
    induction x; intros. inversion H; subst.
    pose (occurs_free_var i).
    eapply T_Var. pose (H0 _ o).
    rewrite <- e; auto.

    inversion H; subst. 
    assert (forall i: id, occurs_free i x1 -> G i = G' i).
    intros. pose (occurs_free_app_1 i x1 x2 H1).
    auto.
    assert (forall i: id, occurs_free i x2 -> G i = G' i).
    intros. pose (occurs_free_app_2 i x1 x2 H2).
    auto.
    eauto.

    inversion H; subst.
    eapply T_Abs. 
    assert (forall i0:id, occurs_free i0 x0 -> (update G i t) i0 = (update G' i t)i0 ).
    intros. unfold update; unfold t_update.
    destruct (eq_id_dec i i0); subst. auto.
    assert (i0 <> i). intro. symmetry in H2; tauto.
    pose (occurs_free_abs _ _ t _ H1 H2).
    auto. pose (IHx _ _ _ H6 H1). auto.

    inversion H; subst; eauto.
    inversion H; subst; eauto.
    inversion H; subst; eauto.
    assert (forall i: id, occurs_free i x1 -> G i = G' i). eauto.
    assert (forall i: id, occurs_free i x2 -> G i = G' i). eauto.
    assert (forall i: id, occurs_free i x3 -> G i = G' i). eauto.
    eauto.
Qed.

Theorem empty_is_strong:
    forall x G T,
        empty |- x \in T ->
        G |- x \in T.
    
    intros x G T h.
    assert  (forall i, occurs_free i x -> empty i = G i).
    Focus 1.
    Print empty_closed.
    intros. pose (empty_closed _ _ h).
    unfold closed in *.
    destruct (c _ H).
    eapply context_invariance; eauto.
Qed.


Lemma app_preserv:
forall t g x G T U,
    U |- tabs x G t \in TArrow G T ->
    empty |- g \in G ->
    U |- [x := g] t \in T.

intro. elim t; intros.
    inversion H; subst.
    unfold subst. inversion H3; subst.
    unfold update in *; unfold t_update in *.
    destruct (eq_id_dec x0 i); subst. inversion H4; subst. 
    eapply empty_is_strong. auto.
    eapply T_Var. auto.
    
    inversion H1; subst. inversion H5; subst.
    pose (T_Abs _ _ _ _ _ H7).
    pose (T_Abs _ _ _ _ _ H9).
    pose (H _ _ _ _ _ h H2).
    pose (H0 _ _ _ _ _ h0 H2).
    change (U |- tapp ([x0 := g] t0) ([x0 := g] t1) \in T ).
    eauto.

    inversion H0; subst. inversion H4; subst.
    change (U |- (if (eq_id_dec x0 i) then tabs i t0 t1 else tabs i t0 ([x0 := g] t1)) \in TArrow t0 T12).
    destruct (eq_id_dec x0 i); subst. rewrite update_shadow in H8. eauto.
    rewrite update_permute in H8; eauto.

    inversion H; subst. inversion H3; subst. unfold subst; auto.
    inversion H; subst. inversion H3; subst. unfold subst; auto.

    inversion H2; subst.  inversion H6; subst.
    pose (T_Abs _ _ _ _ _ H9).
    pose (T_Abs _ _ _ _ _ H11).
    pose (T_Abs _ _ _ _ _ H12).
    change (U |- tif ([x0 := g] t0) ([x0 := g] t1) ([x0 := g] t2) \in T).
    eauto.
Qed.


Theorem preservation :
forall t t' T,
    empty |- t \in T ->
    t ==> t' ->
    empty |- t' \in T.

    intro.
    elim t; intros.
    inversion H; subst. inversion H3.

    inversion H1; subst; inversion H2; subst; eauto.
    inversion H6; subst. eapply app_preserv; eauto.

    inversion H0; subst; inversion H1; subst; eauto.
    
    inversion H0. inversion H0. 
    inversion H2; subst; inversion H3; subst; eauto.
Qed.



    




    




    
    
    

    
    
    

    
    

    

    
    

     






    

    







    




    
    



    


    
    
    

    
    

    
    



    



    



    
    


    










