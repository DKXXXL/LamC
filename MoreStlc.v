Require Import SfLib.

Require Import Types.
Require Import Smallstep.
Require Import Stlc.
Require Import STLCWA.


Module STLCEXTENDED.

Inductive ty : Type :=
    | TNat : ty 
    | TArrow : ty -> ty -> ty
    | TProd : ty -> ty -> ty
    | TSum : ty -> ty -> ty
    | TUnit : ty 
    | TList : ty -> ty.

    Hint Constructors ty.

Inductive tm : Type :=
    | tvar : id -> tm
    | tabs : id -> ty -> tm -> tm 
    | tapp : tm -> tm -> tm
    | tnat : nat -> tm
    | tsucc : tm -> tm
    | tpred : tm -> tm 
    | tmult : tm -> tm -> tm
    | tif0 : tm -> tm -> tm -> tm
    | tlet : id -> tm -> tm -> tm 
    | tpair : tm -> tm -> tm 
    | inl : ty -> tm -> tm 
    | inr : ty -> tm -> tm
    | scase : tm -> id -> tm -> id -> tm -> tm
    | unit : tm 
    | tnil : ty -> tm 
    | tcons : tm -> tm -> tm
    | lcase : tm -> tm -> id -> id -> tm -> tm
    | tfix : tm -> tm.

    Hint Constructors tm.

Print update.

    Reserved Notation "Gamma '|=' t '\in' T" (at level 40).            



Inductive has_type : Context -> tm -> ty -> Prop :=
    | tyVar :
        forall i T G,
            byContext G i = Some T ->
            G |= tvar i \in T
    | tyAbs :
        forall i x T G Gamma,
            update i T Gamma |= x \in G ->
            Gamma |= tabs i T x \in TArrow T G 
    | tyApp :
        forall abs arg U V G,
            G |= abs \in TArrow U V ->
            G |= arg \in U ->
            G |= tapp abs arg \in V
    | tyNat :
        forall n G,
            G |= tnat n \in TNat
    | tySucc :
        forall x G,
            G |= x \in TNat ->
            G |= tsucc x \in TNat
    | tyPred :
        forall x G,
            G |= x \in TNat ->
            G |= tpred x \in TNat
    | tyMult :
        forall x y G,
            G |= x \in TNat ->
            G |= y \in TNat ->
            G |= tmult x y \in TNat
    | tyIf :
        forall t t0 t1 G T,
            G |= t0 \in T ->
            G |= t1 \in T ->
            G |= t \in TNat ->
            G |= tif0 t t0 t1 \in T
    | tyLet :
        forall i x g G T U,
            update i U G |= x \in T ->
            G |= g \in U ->
            G |= tlet i g x \in T
    | tyPair :
        forall x y U V G,
            G |= x \in U ->
            G |= y \in V ->
            G |= tpair x y \in TProd U V
    | tySum0 :
        forall x U V G,
            G |= x \in U ->
            G |= inl V x \in TSum U V
    | tySum1 :
        forall y U V G,
            G |= y \in V ->
            G |= inr U y \in TSum U V
    | tySCase :
        forall i j matched U V lft rgt G T,
            update i U G |= lft \in T ->
            update j V G |= rgt \in T ->
            G |= matched \in TSum U V ->
            G |= scase matched i lft j rgt \in T 
    | tyUnit :
        forall G,
            G |= unit \in TUnit
    | tyNil :
        forall G T,
            G |= tnil T \in TList T
    | tyCons :
        forall x y G T,
            G |= x \in T ->
            G |= y \in TList T ->
            G |= tcons x y \in TList T
    | tyLCase :
        forall casenil caselist matched i j T U  G,
            G |= casenil \in U ->
            i <> j ->
            update i T
                (update j (TList T) G) |= caselist \in U ->
            G |= matched \in TList T ->
            G |= lcase matched casenil i j caselist \in U
    | tyFix :
        forall x G T,
            G |= x \in TArrow T T ->
            G |= tfix x \in T 
    where "Gamma '|=' t '\in' T " := (has_type Gamma t T).
            

    Hint Constructors has_type.


Inductive value : tm -> Prop :=
    | vnat : forall i,
        value (tnat i)
    | vabs : forall x T v,
        value (tabs x T v)
    | vprod : forall x y,
        value x ->
        value y ->
        value (tpair x y)
    | vsum0 : forall x T,
        value x ->
        value (inl T x)
    | vsum1 : forall x T,
        value x ->
        value (inr T x)
    | vunit :
        value unit
    | vnil :
        forall T,
        value (tnil T)
    | vcons :
        forall x y,
        value x ->
        value y ->
        value (tcons x y)
    | vfix :
        forall x,
            value x ->
            value (tfix x).

    Hint Constructors value.

    Print tm.
    
Reserved Notation "'[' x ':=' s ']' t" (at level 20).
Fixpoint subst (x : id) (s : tm) (org : tm) : tm :=
    match org with
        | tvar i => if (eq_id_dec x i) then s else org
        | tabs t T v => tabs t T (if(eq_id_dec t x) then v else ([x := s] v))
        | tapp a b => tapp ([x := s] a) ([x := s] b)
        | tsucc n => tsucc ([x := s] n)
        | tpred n => tpred ([x := s] n)
        | tmult a b => tmult ([x := s] a) ([x := s] b)
        | tif0 t t0 t1 => tif0 ([x := s] t) ([x := s] t0) ([x := s] t1)
        | tlet t u v => if(eq_id_dec t x) then org else tlet t u ([x := s] v)
        | tpair a b => tpair ([ x:= s] a) ([x := s] b)
        | inl T v => inl T ([x := s] v)
        | inr T v => inr T ([x := s] v)
        | scase m ia lft ib rgt => 
            scase ([x := s] m) ia (if (eq_id_dec ia x) then lft else [x := s] lft)
                               ib (if (eq_id_dec ib x) then rgt else [x := s] rgt)
        | tcons a b => tcons ([x := s] a) ([x := s] b)
        | lcase m cn ihead itail cl =>
            lcase ([x := s] m) ([ x:= s] cn) ihead itail
                (if eq_id_dec ihead x then cl else 
                    if eq_id_dec itail x then cl else [x:= s] cl)
        | tfix v => tfix ([x := s] v)
        | _ => org
        end
        where "'[' x ':=' s ']' t" := (subst x s t).


        
        




