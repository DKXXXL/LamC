Require Import SfLib.
Require Import Maps.
Require Import Types.
Require Import STLCWA.


Module Subtype.

Inductive ty : Type :=
    | TTop : ty
    | TBool : ty 
    | TBase : id -> ty
    | TArrow : ty -> ty -> ty
    | TUnit : ty.

Inductive tm : Type :=
    | tvar : id -> tm 
    | tapp : tm -> tm -> tm
    | tabs : id -> ty -> tm -> tm
    | ttrue : tm
    | tfalse : tm 
    | tif : tm -> tm -> tm -> tm 
    | tunit : tm.


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

    
    Reserved Notation "G '|=' x '\in' T" (at level 40).

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

    Inductive has_type : 

    
        
        

                    
    