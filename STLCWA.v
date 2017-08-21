Module STLCARITH.

Inductive ty : Type :=
    | TArrow : ty -> ty -> ty
    | TNat : ty.

Inductive tm : Type :=
    | tvar : id -> tm 
    | tapp : tm -> tm -> tm
    | tabs : id -> ty -> tm -> tm 
    | tnat : nat -> tm 
    | tsucc : tm -> tm 
    | tpred : tm -> tm 
    | tmult : tm -> tm -> tm 
    | tif0 : tm -> tm -> tm -> tm.

(*Weak Typing. 0 as False, others are true.*)

In