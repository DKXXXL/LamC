Require Import SfLib.
Require Import Maps.
Require Import Types.
Require Import STLCWA.

Module SubTest.

Inductive ty : Type :=
    | TNat : ty
    | TTop : ty 
    | TProd : ty -> ty -> ty
    | TArrow : ty -> ty -> ty.

Reserved Notation "x '<:' y" (at level 40).

Inductive subtype_of : ty -> ty -> Prop :=
    | refl_sub : forall x, x <: x
    | trans_sub : forall x y z,
                        x <: y ->
                        y <: z ->
                        x <: z
    | prod_sub : forall x x' y y',
                    x <: x' ->
                    y <: y' ->
                    (TProd x y) <: (TProd x' y')
    | arrow_sub : forall x x' y y',
                    x' <: x ->
                    y <: y' ->
                    (TArrow x y) <: (TArrow x' y')
    | sub_top : forall x,
                    x <: TTop
    where "x '<:' y " := (subtype_of x y).

Hint Constructors subtype_of.

Parameter (S T U V A B C: ty).

Parameter (Rule1 : S <: T) (Rule2 : U <: V).

Hint Resolve Rule1 Rule2 : example_database1.

Example
    ex1_1:
        TArrow S T <: TArrow S T.
    eauto.

Qed.

Example ex1_2 :
        TArrow TTop U <: TArrow S TTop.

    eauto.
Qed.

Example ex1_3 :
        TArrow (TArrow C C) (TProd A B) <: TArrow (TArrow C C) (TProd TTop B).
        eauto.
Qed.

Example ex1_4 :
        TArrow T (TArrow T U) <: TArrow S (TArrow S V).
        eauto with example_database1.
Qed.

Theorem subtype_dec :
    forall A B,
        {A <: B} + {~ A <: B}.

    intro A; induction A; intro B; induction B; eauto.
    destruct IHB1; destruct IHB2.
    right; intro. inversion H; subst. inversion H0; subst.
Abort.

(* I think this definition has some problem. Because it's not decidable. *)

Example ex1_5:
    ~TArrow (TArrow T T) U <: TArrow (TArrow S S) V.

    Abort.

Example ex1_6:
    TArrow (TArrow (TArrow T S) T) U <:
    TArrow (TArrow (TArrow S T) S) V.
    eauto with example_database1.
Qed.

Example ex1_7:
    ~TProd S V <: TProd T U.
    Abort.

Parameter (Student Person : ty).
Parameter (Rule3 : Student <: Person).

Hint Resolve Rule3 : example1_database.
Example ex2:
        (TArrow TTop Student) <:
        (TArrow Person Student) /\
        (TArrow Person Student) <:
        (TArrow Student Person) /\
        (TArrow Student Person) <:
        (TArrow Student TTop) /\
        (TArrow Student TTop) <:
        TTop.
        repeat (split; eauto with example1_database).
Qed.

Example ex3:
    ~(forall S T,
        S <: T ->
        (TArrow S S) <: (TArrow T T)).
Admitted. 

Example ex3_2:
    ~(forall S,
        S <: (TArrow A A) ->
        exists T,
            S = TArrow T T /\ T <: A).
Admitted.


Example ex3_3:
    forall S T1 T2,
        (S <: TArrow T1 T2) ->
        exists S1 S2,
            S = TArrow S1 S2 /\
            T1 <: S1 /\
            S2 <: T2.

    intros S T1 T2 h.
    remember S as s.
    remember (TArrow T1 T2) as q.
    generalize Heqs. induction h; subst.
    eauto.

    intros.
    Abort.

Example ex3_4:
    ~(exists S,
        S <: (TArrow S S)).
Admitted.


Example ex3_5:
    exists S,
        (TArrow S S) <: S.
    exists TTop; eauto.
Qed.

Example ex3_6:
    forall S T1 T2,
        S <: (TProd T1 T2) ->
        exists S1 S2,
            S = (TProd S1 S2) /\
            S1 <: T1 /\
            S2 <: T2.
Admitted.

(** **** Exercise: 2 stars (small_large_4)  *)
(**
   - What is the _smallest_ type [T] that makes the following
     assertion true?
       exists S,
         empty |- (\p:(A*T). (p.snd) (p.fst)) : S
   ?????
   - What is the _largest_ type [T] that makes the same
     assertion true?
   ?????
[] *)

(** **** Exercise: 2 stars (smallest_1)  *)
(** What is the _smallest_ type [T] that makes the following
    assertion true?
      exists S, exists t,
        empty |- (\x:T. x x) t : S
    ?????
]]
[] *)

(** **** Exercise: 3 stars, optional (count_supertypes)  *)
(** How many supertypes does the record type [{x:A, y:C->C}] have?  That is,
    how many different types [T] are there such that [{x:A, y:C->C} <:
    T]?  (We consider two types to be different if they are written
    differently, even if each is a subtype of the other.  For example,
    [{x:A,y:B}] and [{y:B,x:A}] are different.) *)


End SubTest.
