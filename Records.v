Require Import SfLib.
(* Require Import Maps.*)
Require Import STLCWA.
Require Import Imp.
Require Import Smallstep.
Require Import Stlc.

Module STLCEXTENDEDRECORDS.

Module FIRSTTRY.
    Definition alist (X: Type) := list (id * X).

    Inductive ty : Type :=
        | TBase : id -> ty
        | TArrow : ty -> ty -> ty
        | TRcd : (alist ty) -> ty.

    (* It's not good, just look at the induction rule *)
End FIRSTTRY.

