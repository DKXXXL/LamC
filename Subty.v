Require Import SfLib.

Require Import Types.
Require Import STLCWA.

Require Import LibTactics.


Module Subtype.

Inductive ty : Type :=
    | TTop : ty
    | TBool : ty 
    | TBase : id -> ty
    | TArrow : ty -> ty -> ty
    | TUnit : ty.

    Hint Constructors ty.
Inductive tm : Type :=
    | tvar : id -> tm 
    | tapp : tm -> tm -> tm
    | tabs : id -> ty -> tm -> tm
    | ttrue : tm
    | tfalse : tm 
    | tif : tm -> tm -> tm -> tm 
    | tunit : tm.
    
    Hint Constructors tm.


    Reserved Notation "x '<:' y" (at level 40).
    Inductive subtype_of : ty -> ty -> Prop :=
        | sub_top :
            forall x,
                x <: TTop
        | sub_arrow:
            forall x x' y y',
                x' <: x ->
                y <: y' ->
                TArrow x y <: TArrow x' y'
        | refl_sub :
            forall x,
                x <: x
        | trans_sub :  
            forall x y z,
                x <: y ->
                y <: z ->
                x <: z
        where "x '<:' y" := (subtype_of x y).


    Hint Constructors subtype_of.

    Fixpoint subst (i : id) (x org : tm) : tm :=
        match org with
            | tvar v => if (eq_id_dec i v) then x else org
            | tapp a b => tapp (subst i x a) (subst i x b)
            | tabs u T v => tabs u T (if (eq_id_dec i u) then v else (subst i x v))
            | tif a b c => 
                tif (subst i x a) (subst i x b) (subst i x c)
            | _ => org
        end.
    
    Notation "[ x ':=' s ] a" := (subst x s a) (at level 40).

    Print tm.
    Inductive has_type : Context -> tm -> ty -> Prop :=
        | tyVar :
            forall (i: id) G (T:ty),
                byContext G i = Some T ->
                has_type G (tvar i) T
        | tyAbs :
            forall i G x U T,
                has_type (update i T G) x U ->
                has_type G (tabs i T x) (TArrow T U)
        | tyApp :
            forall G abs arg U T,
                has_type G abs (TArrow U T) ->
                has_type G arg U ->
                has_type G (tapp abs arg) T 
        | tyTrue :
            forall G,
                has_type G ttrue TBool
        | tyFalse :
            forall G,
                has_type G tfalse TBool
        | tyUnit :
            forall G,
                has_type G tunit TUnit
        | tyIf :
            forall G x t0 t1 T,
                has_type G t0 T ->
                has_type G t1 T ->
                has_type G x TBool ->
                has_type G (tif x t0 t1) T
        | tySub :
            forall G x U V,
                has_type G x U ->
                U <: V ->
                has_type G x V.

    Notation "G '|=' x '\in' T" :=
        (has_type G x T) (at level 40).

    Hint Constructors has_type.

    Inductive value : tm -> Prop :=
        | vAbs : forall x T v, value (tabs x T v)
        | vTrue : value ttrue
        | vFalse : value tfalse
        | vunit : value tunit.

    Hint Constructors value.

    Inductive step : tm -> tm -> Prop :=
        | stApp0 :
            forall a a' b,
                step a a' ->
                step (tapp a b) (tapp a' b)
        | stApp1 :
            forall a b b',
                value a ->
                step b b' ->
                step (tapp a b) (tapp a b')
        | stApp2 :
            forall x T v b,
                value b ->
                step (tapp (tabs x T v) b) ([x := b] v)
        | stIf0 :
            forall x x' t0 t1,
                step x x' ->
                step (tif x t0 t1) (tif x' t0 t1)
        | stIfTrue :
            forall t0 t1,
                step (tif ttrue t0 t1) t0
        | stIfFalse :
            forall t0 t1,
                step (tif tfalse t0 t1) t1.
    
    Notation "a '==>' b" := (step a b) (at level 40).

    Hint Constructors step.

    Module EXAMPLES.
        Notation x := (Id 0).
        Notation y := (Id 1).
        Notation z := (Id 2).

        Notation A := (TBase (Id 6)).
        Notation B := (TBase (Id 7)).
        Notation C := (TBase (Id 8)).

        Notation String := (TBase (Id 9)).
        Notation Float := (TBase (Id 10)).
        Notation Integer := (TBase (Id 11)).

        Example subtyping_ex0: 
            (TArrow C TBool) <: (TArrow C TTop).

            eauto.
        Qed.

    End EXAMPLES.

    Hint Extern 2 (has_type _ (tapp _ _) _) =>
        eapply tyApp; auto.

    Hint Extern 2 (_ = _) =>
        compute; reflexivity.

    Module EXAMPLES2.
    Import EXAMPLES.
    End EXAMPLES2.

Lemma sub_inversion_Bool :
        forall U,
            U <: TBool ->
            U = TBool.

        intros U h. 
        remember TBool as t.
        induction h; subst. inversion Heqt.
        inversion Heqt. auto. 
        pose (IHh2 eq_refl).
        pose (IHh1 e). rewrite e0; rewrite e. auto.
        
Qed.

Lemma sub_inversion_arrow :
    forall U V1 V2,
        (U <: (TArrow V1 V2)) ->
        exists U1 U2,
            (U = TArrow U1 U2) /\
            (V1 <: U1) /\
            (U2 <: V2).

    intros u v1 v2 h.
    remember (TArrow v1 v2) as v.
    generalize dependent v1; generalize dependent v2.
    induction h; subst; intros; try discriminate.
    inversion Heqv; subst.
    exists x; exists y; tauto.
    exists v1; exists v2; repeat (split; eauto).
    destruct (IHh2 _ _ Heqv) as (u1 & u2 & H1 & H2 & H3); subst.
    destruct (IHh1 u2 u1 eq_refl) as (a1 & a2 & a3 & a4 &a5).
    exists a1; exists a2; try tauto.
    repeat (split; eauto).
Qed. 

Lemma canonical_form_of_arrow_ty :
    forall Gamma s T1 T2,
        Gamma |= s \in (TArrow T1 T2) ->
        value s ->
        exists x S1 s2,
            s = tabs x S1 s2.
        
    intros G s T1 T2 h1.
    remember (TArrow T1 T2) as Ar.
    gen T1 T2.
    induction h1; eauto;
    try (intros T1 T2 h0 hh; inversion hh; fail);
    try (intros T1 T2 h0; inversion h0; fail).
    
    intros; subst.
    destruct (sub_inversion_arrow _ _ _ H) as (u1 & u2 & hh1 & hh2 & hh3).
    eauto.
Qed.

Lemma canonical_form_of_bool_ty :
    forall G s,
        G |= s \in TBool ->
        value s ->
        s = ttrue \/ s = tfalse.

    intros G s h. remember TBool as t.
    gen Heqt.
    induction h; eauto;
    try (intros hh1 hh2; inversion hh2; fail);
    try (intros hh1; inversion hh1; fail).

    intros; subst. 
    pose (sub_inversion_Bool _ H).
    eauto.
Qed.


Ltac go_far :=
    match goal with
        | [x: ?pre -> _ |- _] => 
                    (assert (pre) as GO_FAR_H; 
                    [eauto; fail | eauto];
                    pose (x GO_FAR_H) as GO_FAR_HH; 
                        generalize GO_FAR_HH; 
                        try (clear GO_FAR_HH); 
                        try (clear GO_FAR_H);
                        clear x; intro x; go_far
                            )
        | _ => idtac 
    end.


Theorem progress:
    forall x T,
        empty |= x \in T ->
        value x \/ exists x', x ==> x'.

    intros x T h.
    remember empty as eg.
    gen Heqeg. 
    induction h; try (intros; subst; eauto).
    inversion H.
    destruct (IHh1 eq_refl). destruct (IHh2 eq_refl).
    destruct (canonical_form_of_arrow_ty _ _ _ _ h1 H) as (x & S1 &s2 & hh); subst.
    right; exists ([x := arg] s2); eauto.
    destruct H0 as (arg' & hh);
    right; exists (tapp abs arg'); eauto.
    destruct H as (abs' & hh); right ;exists (tapp abs' arg); eauto.
    go_far.
    destruct IHh3. 
    destruct (canonical_form_of_bool_ty _ _ h3 H); subst.
    right; exists t0; eauto.
    right; exists t1; eauto.
    destruct H as (x'0 & H); subst;
    right; exists (tif x'0 t0 t1); eauto.

Qed.

Lemma typing_inversion_abs :
    forall G x S1 t2 T,
        G |= tabs x S1 t2 \in T ->
        (exists S2, (TArrow S1 S2) <: T /\
            (update x S1 G) |= t2 \in S2).

    intros G x S1 t2 T h.
    remember (tabs x S1 t2) as v.
    gen x S1 t2.
    induction h; intros x0 S1 t2 h0; subst; eauto;
    try (inversion h0; subst; eauto; fail).

    destruct (IHh x0 S1 t2) as (S3 & hh & hhh); eauto.
Qed.

Lemma typing_inversion_var :
    forall G x T ,
        G |= tvar x \in T ->
        exists S,
            byContext G x = Some S /\
            S <: T.

    intros G x T h.
    remember (tvar x) as v.
    gen x.

    induction h; try (intros; subst; eauto; fail);
    try (intros a h' ; subst; inversion h'; fail);
    intros a h'; subst.
    inversion h'; subst; eauto.
    destruct (IHh a eq_refl ) as (S & h0 & h1); eauto.
Qed.

Lemma typing_inversion_app0 :
    forall G t1 t2 T,
        G |= (tapp t1 t2) \in T ->
        (exists S1 S2, G |= t1 \in TArrow S1 S2 /\
        G |= t2 \in S1 /\
        S2 <: T).

        intros G t1 t2 T2 h1.
        remember (tapp t1 t2) as v.
        gen t1 t2.

        induction h1; try (intros; subst; eauto;fail);
        try (intros t1 t2 h0; subst; inversion h0; fail);
        intros a1 a2 h0; subst.

        inversion h0; subst. eauto.
        inversion h0; subst.
        destruct (IHh1 a1 a2 eq_refl) as (S1 & S2 & H0 & H1 & H2).
        exists S1; exists S2; eauto.
Qed.

Lemma typing_inversion_app :
    forall G t1 t2 T2,
        G |= (tapp t1 t2) \in T2 ->
        (exists T1, 
            G |= t1 \in TArrow T1 T2 /\
            G |= t2 \in T1).
    
    intros G t1 t2 T2 h;
    remember (tapp t1 t2) as v;
    gen t1 t2;
    induction h; try (intros; subst; eauto ;fail );
    try (intros t1 t2 hh; subst; inversion hh; subst ;fail).

    intros. inversion Heqv; subst. eauto.
    intros t2 t3 hh; inversion hh.
    intros. destruct (IHh _ _ Heqv) as (T1 & h1 & h2); eauto.
Qed.

Lemma typing_inversion_true :
    forall G T,
        G |= ttrue \in T ->
        TBool <: T.

    intros G T h; 
    remember ttrue as v;
    gen Heqv.
    induction h; try (intros h; subst; inversion h; eauto; fail).
    intros. inversion Heqv. eauto.
Qed.

Lemma typing_inversion_if :
    forall G t1 t2 t3 T,
        G |= tif t1 t2 t3 \in T ->
        G |= t1 \in TBool /\
        (exists S, G |= t2 \in S /\
                    G |= t3 \in S /\
                        S <: T).

    intros G t1 t2 t3 T h;
    remember (tif t1 t2 t3) as v;
    gen t1 t2 t3.
    induction h; try (intros t1 t2 t3 hh; inversion hh; subst; eauto).

    intros t2 t3 t4 hh. inversion hh; subst. eauto.
    destruct (IHh t1 t2 t3 eq_refl) as (S & h0 & h1 & h2 & h3); eauto.
    split; eauto.
Qed.   

Lemma typing_inversion_false :
    forall G T,
        G |= tfalse \in T ->
        TBool <: T.

        intros G T h; 
        remember tfalse as v;
        gen Heqv.
        induction h; try (intros h; subst; inversion h; eauto; fail).
        intros. inversion Heqv. eauto.
Qed.


Lemma typing_inversion_unit:
    forall G T,
         G |= tunit \in T ->
         TUnit <: T.

         intros G T h; 
         remember tunit as v;
         gen Heqv.
         induction h; try (intros h; subst; inversion h; eauto; fail).
         intros. inversion Heqv. eauto.
Qed.


Lemma abs_arrow :
    forall x S1 s2 T1 T2,
        empty |= tabs x S1 s2 \in (TArrow T1 T2) ->
        T1 <: S1 /\
        (update x S1 empty) |= s2 \in T2.

    intros x S1 s2 T1 T2 h1.
    destruct (typing_inversion_abs _ _ _ _ _ h1) as 
        (S2 & hh & hhh).
    destruct (sub_inversion_arrow _ _ _ hh) as 
            (u1 & u2 & hh1 & hh2 & hh3).
    inversion hh1; subst; eauto.
Qed.

Print tm.

Inductive occurs_free : id -> tm -> Prop :=
    | of_var : forall i,
                occurs_free i (tvar i)
    | of_app1 : forall i x y,
                occurs_free i x ->
                occurs_free i (tapp x y)
    | of_app2 : forall i x y,
                occurs_free i y ->
                occurs_free i (tapp x y)
    | of_abs : forall i x T v,
                i <> x ->
                occurs_free i v ->
                occurs_free i (tabs x T v)
    | of_if0 : forall i t t0 t1,
                occurs_free i t ->
                occurs_free i (tif t t0 t1)
    | of_if1 : forall i t t0 t1,
                occurs_free i t0 ->
                occurs_free i (tif t t0 t1)
    | of_if2 : forall i t t0 t1,
                occurs_free i t1 ->
                occurs_free i (tif t t0 t1).

    Hint Constructors occurs_free.

Hint Resolve typing_inversion_abs typing_inversion_var
            typing_inversion_app typing_inversion_true
            typing_inversion_false typing_inversion_if
            typing_inversion_unit abs_arrow : inv_ty_db.

Ltac typing_inversion_auto :=
    match goal with
        | [x : _ |= tvar _ \in _  |- _] => destruct (typing_inversion_var _ _ _ x) as (ss0 & hh0 & hh1)
        | [x : _ |= tapp _ _ \in _ |- _] => destruct (typing_inversion_app _ _ _ _ x) as (ss0 & hh0 & hh1)
        | [x : _ |= tabs _ _ _ \in TArrow _ _ |- _] => destruct (abs_arrow _ _ _ _ _ x) as ( hh0 & hh1)  
        | [x : _ |= tabs _ _ _ \in _ |- _] => destruct (typing_inversion_abs _ _ _ _ _ x) as (ss0 & hh0 & hh1)
        | [x : _ |= ttrue \in _ |- _] => pose (typing_inversion_true _ _ x) as hh0
        | [x : _ |= tfalse \in _ |- _] => pose (typing_inversion_false _ _ x) as hh0
        | [x : _ |= tunit \in _ |- _] => pose (typing_inversion_unit _ _ x) as hh0
        | [x : _ |= tif _ _ _ \in _ |- _] => destruct (typing_inversion_if _ _ _ _ _ x) as (ss0 & hh0 & hh1 & hh2 & hh3)
        | _ => idtac
    end; eauto.
Lemma occurs_free_in_ctx :
    forall G i t T,
        occurs_free i t ->
        G |= t \in T ->
        (exists S, byContext G i = Some S).
    
    intros G i t T h.
    gen G T.
    induction h; try (subst; intros; typing_inversion_auto; eauto with inv_ty_db).
    destruct (IHh _ _ hh1) as (S & h0). cbn in *.
    destruct (eq_id_dec i x); subst; eauto.
    destruct (H eq_refl).
Qed.


Lemma context_invariance :
    forall G G' t S,
        G |= t \in S ->
        (forall x, occurs_free x t -> byContext G x = byContext G' x) ->
        G' |= t \in S.

    intros G G' t S h.
    gen G'.
    induction h; intros; typing_inversion_auto.

    intros. eapply tyVar.
    rewrite <- H0; eauto.
    
    intros; eauto. eapply tyAbs.
    assert (forall x0, occurs_free x0 x -> byContext (update i T G) x0 = byContext (update i T G') x0).
    cbn. intros. destruct (eq_id_dec x0 i); subst; eauto.
    eauto.

    eapply tyIf; eauto.
Qed.




Lemma empty_is_closed :
    forall x T,
        empty |= x \in T ->
        (forall i, ~occurs_free i x).

    intros x T h1 i h2.
    gen T h1.
    induction h2; subst; intros; typing_inversion_auto.

    inversion hh0. 
    assert (occurs_free i (tabs x T v)); eauto.
    destruct  (occurs_free_in_ctx _ _ _ _ H0 h1) as (S & hh);
    inversion hh.
Qed.

Lemma empty_is_strong :
    forall x G T,
        empty |= x \in T ->
        G |= x \in T.

    intros. eapply context_invariance; eauto.
    intros x0 hh. destruct (empty_is_closed _ _ H x0 hh).
Qed.


Theorem ctx_swap :
    forall U V t T,
        U |= t \in T ->
        U =-= V ->
        V |= t \in T.
    intros U V t; gen U V.
    induction t;
    try (unfold context_equivalence; intros; typing_inversion_auto; fail); try (intros; typing_inversion_auto).

    intros; unfold context_equivalence in *; typing_inversion_auto; eapply tySub; try eapply hh1. eapply tyVar. rewrite <- H0; eauto.
    eapply tySub; try eapply hh0. eapply tyAbs.  eapply IHt. eapply hh1.
    eapply update_inc; eapply H0.
    eapply tyIf; eauto.
Qed.

Lemma subst_preserve_typing:
forall G x U g t S,
    (update x U G) |= t \in S ->
    empty |= g \in U ->
    G |= [x := g] t \in S.

intros G x U g t.
gen G x U g.
induction t; cbn in *; intros; typing_inversion_auto; cbn in *.
destruct (eq_id_dec x i); subst; eauto. rewrite eq_id_dec_id in *. inversion hh0; subst.
eapply empty_is_strong. eauto.
destruct (eq_id_dec i x); subst; eauto. destruct (n eq_refl).
destruct (eq_id_dec x i); subst; eauto. 
eapply tySub; try eapply hh0. eapply tyAbs; eauto. 
eapply ctx_swap; try eapply hh1. eapply update_shadow. eapply refl_ctxeq.
eapply tySub; try eapply hh0. eapply tyAbs; eauto. eapply IHt; eauto.
eapply ctx_swap; try eapply hh1; try eapply update_permute; eauto.
eapply refl_ctxeq.
eapply tyIf; eauto.
Qed.


Theorem preservation:
    forall t t' T,
        empty |= t \in T ->
        t ==> t' ->
        empty |= t' \in T.

    intro t; induction t;
     try (intros t' T h1 h2; inversion h2; subst; typing_inversion_auto).

    typing_inversion_auto.

    destruct (abs_arrow _ _ _ _ _ hh0).
    eapply subst_preserve_typing; eauto.
Qed.

(* Corollary  Soundness is omitted. *)

End Subtype.









    








    








    

    
        
        

                    
    