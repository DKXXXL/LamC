Require Import Maps.


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

(* Weak Typing. 0 as False, others are true. *)

Inductive TyContext : Type :=
    | empty : TyContext 
    | update : id -> ty -> TyContext -> TyContext.
    
Fixpoint byContext (ctx : TyContext) (i : id) : option ty :=
    match ctx with 
        | empty => None
        | update x Ty ctx' =>
            if (eq_id_dec i x) then Some Ty else byContext ctx' i
            end.

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).            

Inductive has_type : TyContext -> tm -> ty -> Type :=
    | tyVar : 
        forall G i T,
            byContext G i = Some T ->
            G |- tvar i \in T
    | tyApp :
        forall Gamma a b G T,
        Gamma |- a \in TArrow G T ->
        Gamma |- b \in G ->
        Gamma |- tapp a b \in T
    | tyAbs :
        forall Gamma i x G T,
        update i G Gamma |- x \in T ->
        Gamma |- tabs i T x \in TArrow G T
    | tyNat :
        forall i Gamma,
        Gamma |- tnat i \in TNat
    | tySucc :
        forall x Gamma,
        Gamma |- x \in TNat ->
        Gamma |- tsucc x \in TNat
    | tyPred :
        forall x Gamma,
        Gamma |- x \in TNat ->
        Gamma |- tpred x \in TNat
    | tyMult :
        forall x y Gamma,
        Gamma |- x \in TNat ->
        Gamma |- y \in TNat ->
        Gamma |- tmult x y \in TNat
    | tyIf :
        forall t t0 t1 Gamma T,
        Gamma |- t0 \in T ->
        Gamma |- t1 \in T ->
        Gamma |- t \in TNat ->
        Gamma |- tif0 t t0 t1 \in T
    where "Gamma '|-' t '\in' T " := (has_type Gamma t T).
        