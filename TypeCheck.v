Require Import Coq.Bool.Bool.
Require Import SfLib.
Require Import Maps.
Require Import Stlc.
Require Import LibTactics.

Module STLCCHECKER.

Import STLC.

Fixpoint beq_ty (T1 T2: ty) : bool :=
    match T1, T2 with
        | TBool, TBool => true
        | TArrow t1 t2, TArrow t3 t4 => andb (beq_ty t1 t3) (beq_ty t2 t4)
        | _, _ => false
    end.

Lemma beq_ty_refl : forall t,
    beq_ty t t = true.
    induction t;cbn; eauto.
    rewrite IHt1; rewrite IHt2; eauto.
Qed.

Lemma beq_ty__eq :
    forall t1 t2,
        beq_ty t1 t2 = true -> t1 = t2.
    
    intro t1. induction t1; intros t2; induction t2; 
    try (eauto; fail);
    try (intros h1; inversion h1; fail).
    intros. inversion H. 
    destruct (beq_ty t1_1 t2_1) eqn: hh1; destruct (beq_ty t1_2 t2_2) eqn:hh2; subst; inversion H1.
    pose (IHt1_1 _ hh1); pose (IHt1_2 _ hh2). rewrite e in *; rewrite e0 in *.
    auto.
Qed.

Print tm.

Fixpoint type_check (G : context) (t : tm) : option ty :=
    match t with
        | tvar x => G x
        | tabs x T v => match (type_check (update G x T) v) with
                            | Some U => Some (TArrow T U)
                            | None => None
                        end
        | tapp abs arg =>
            match (type_check G abs) with
                | Some (TArrow U V) => match (type_check G arg) with
                                        | Some Q => if(beq_ty U Q) then Some V else None
                                        | _ => None 
                                        end
                | _ => None 
                end
        | ttrue => Some TBool 
        | tfalse => Some TBool
        | tif t t0 t1 =>
            match type_check G t with
                | Some TBool =>
            match type_check G t0, type_check G t1 with
                | Some a, Some b => if(beq_ty a b) then Some a else None 
                | _, _ => None 
            end 
                | _ => None 
            end 
    end.

Theorem type_check_sound : 
    forall G t T,
        type_check G t = Some T ->
        has_type G t T.

    intros G t; gen G.
    induction t; cbn in *.
    intros. eapply T_Var; eauto.
    intros.
    destruct (type_check G t1) eqn:h1.
    destruct t eqn:h2;
    destruct (type_check G t2) eqn:h3; eauto; try discriminate.
    destruct (beq_ty t0_1 t0) eqn:h4; eauto; try discriminate.
    eapply T_App; eauto. eapply IHt1; eauto. inversion H; subst.
    pose (beq_ty__eq _ _ h4); rewrite h1. rewrite e. auto.
    inversion H.

    intros. destruct (type_check (update G i t) t0) eqn:h1; try eauto; try discriminate.
    inversion H; subst; eauto. 
    intros G T h1; inversion h1; subst; eauto.
    intros G T h1; inversion h1; subst; eauto.
    intros G T h;
    destruct (type_check G t1) eqn:h1;
    destruct (type_check G t2) eqn:h2;
    destruct (type_check G t3) eqn:h3;
    eauto; try discriminate.

    destruct t eqn:h4; try discriminate; eauto.
    destruct (beq_ty t0 t4) eqn: h5; try discriminate; eauto.
    generalize (beq_ty__eq _ _ h5); intro;
    inversion h; subst. eapply T_If; eauto.
    destruct t eqn:h5; try discriminate; eauto.
    destruct t eqn:h5; try discriminate; eauto.
    destruct t eqn:h5; try discriminate; eauto.
Qed.

End STLCCHECKER.