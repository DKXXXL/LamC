Require Import SfLib.
Require Import LibTactics.
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
    | tfst : tm -> tm
    | tsnd : tm -> tm
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
    | tyFst :
        forall x G U V,
            G |= x \in TProd U V ->
            G |= tfst x \in U
    | tySnd :
            forall x G U V,
                G |= x \in TProd U V ->
                G |= tsnd x \in V
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
        value (tcons x y).

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
        | tlet t u v => if(eq_id_dec t x) then tlet t ([x := s] u) v else tlet t ([x := s] u) ([x := s] v)
        | tpair a b => tpair ([ x:= s] a) ([x := s] b)
        | tfst t => tfst ([x := s] t)
        | tsnd t => tsnd ([x := s] t)
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

        Hint Constructors value.

Print tm.

Reserved Notation "t '==>' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
    | stApp1 : 
        forall x y x',
            x ==> x' ->
            tapp x y ==> tapp x' y
    | stApp2 :
        forall x y y',
            value x ->
            y ==> y' ->
            tapp x y ==> tapp x y'
    | stApp :
        forall i x y T,
            value y ->
            tapp (tabs i T x) y ==> ([i := y] x)
    | stSucc0 :
        forall x x',
            x ==> x' ->
            tsucc x ==> tsucc x'
    | stSucc1 :
        forall x,
            tsucc (tnat x) ==> tnat (S x)
    | stPred0 :
        forall x x',
            x ==> x' ->
            tpred x ==> tpred x'
    | stPred1 :
        forall x,
            tpred (tnat x) ==> tnat (pred x)
    | stMult0 :
        forall x x' y,
            x ==> x' ->
            tmult x y ==> tmult x' y
    | stMult1 :
        forall x y y',
            value x ->
            y ==> y' ->
            tmult x y ==> tmult x y'
    | stMult2 :
        forall a b,
            tmult (tnat a) (tnat b) ==> tnat (a * b)
    | stIf:
        forall t t' t1 t2,
            t ==> t' ->
            tif0 t t1 t2 ==> tif0 t' t1 t2
    | stIf0 :
        forall t1 t2,
            tif0 (tnat 0) t1 t2 ==> t1
    | stIf1 :
        forall i t1 t2,
            i <> 0 ->
            tif0 (tnat i) t1 t2 ==> t2
    | stlet0 :
        forall i t t' v,
            t ==> t' ->
            tlet i t v ==> tlet i t' v
    | stlet1 :
        forall i t v,
            value t ->
            tlet i t v ==> [i := t] v
    | stpair0 :
        forall a a' b,
            a ==> a' ->
            tpair a b ==> tpair a' b
    | stpair1 :
        forall a b b',
            value a ->
            b ==> b' ->
            tpair a b ==> tpair a b'
    | stFst0 :
        forall x x',
            x ==> x' ->
            tfst x ==> tfst x'
    | stFst1 :
        forall x y,
            value (tpair x y) ->
            tfst (tpair x y) ==> x
    | stSnd0 :
        forall x x',
            x ==> x' ->
            tsnd x ==> tsnd x'
    | stSnd1 :
        forall x y,
            value (tpair x y) ->
            tsnd (tpair x y) ==> y
    | stinl :
        forall v v' T,
            v ==> v' ->
            inl T v ==> inl T v'
    | stinr :
        forall v v' T,
            v ==> v' ->
            inr T v ==> inr T v'
    | stscase0 :
        forall x x' i lft j rgt,
            x ==> x' ->
            scase x i lft j rgt ==> scase x' i lft j rgt
    | stscasel :
        forall i j v lft rgt T,
            value (inl T v) ->
            scase (inl T v) i lft j rgt ==> [i := v] lft
    | stscaser :
        forall i j v lft rgt T,
            value (inr T v) ->
            scase (inr T v) i lft j rgt ==> [j := v] rgt
    | stcons0 :
        forall x y x',
            x ==> x'->
            tcons x y ==> tcons x' y
    | stcons1 :
        forall x y y',
            value x ->
            y ==> y' ->
            tcons x y ==> tcons x y'    
    
    | stlcase0 :
        forall x x' casenil head tail caselist,
            x ==> x' ->
            lcase x casenil head tail caselist ==> 
                lcase x' casenil head tail caselist
    | stlcasen :
        forall head tail casenil caselist T,
            lcase (tnil T) casenil head tail caselist ==>
                casenil
    | stlcasel :
        forall head tail casenil caselist h t,
            value h ->
            value t ->
            lcase (tcons h t) casenil head tail caselist ==>
                ([head := h] ([tail := t] caselist))
    | stlfix0 :
        forall x x',
            x ==> x' ->
            tfix x ==> tfix x'
    | stlfix1 :
        forall x T v,
            tfix (tabs x T v) ==> [x := tfix (tabs x T v)] v 
    where "t '==>' t'" := (step t t').
            
    Hint Constructors step.      
    

Lemma value_cant_step :
    forall u v,
        value u ->
        u ==> v ->
        False.
    intros u v h.
    generalize dependent v.
    induction h; intros; try inversion H; subst; eauto.

Qed.

Ltac value_stepping_false :=
    match goal with
        | [H1: ?X1 ==> ?X2 |- _] 
            => assert (value X1) as HHH; eauto;
                destruct (value_cant_step _ _ HHH H1); fail
        end.
Ltac clear_value_stepping :=
    repeat value_stepping_false.







Theorem stlcex_deterministic:
    deterministic step.
    
    unfold deterministic.
    intros x; induction x; 
    try (intros y1 y2 h1 h2;
    inversion h1; inversion h2; subst;
    match goal with
    | [H1 : ?X ==> ?Y, H2 : ?X ==> ?Z |- _] =>
        assert (Y = Z); eauto; subst; eauto
        end);
    try value_stepping_false;
    try (inversion H3; subst; eauto; fail);
    try (inversion H2; subst; eauto; fail).

    inversion H4; subst; eauto.
    inversion H3; inversion H4; subst; eauto.
    inversion H; subst; destruct (H7 eq_refl).
    inversion H5; subst; destruct (H3 eq_refl).
    inversion H6; subst; eauto.
    inversion  H6. inversion H6.
    inversion H6; subst; eauto.
    inversion H. inversion H8. 
    inversion H7; subst; eauto.
Qed.
    
Lemma canonical_form_bools:
    forall t,
        empty |= t \in TNat ->
        value t ->
        exists n, t = tnat n.

    intros t h1 h2; inversion h2; subst; inversion h1; subst; eauto.
Qed.

Lemma canonical_form_fun:
    forall t T U,
        empty |= t \in TArrow T U ->
        value t ->
        exists x v, t = tabs x T v.
    
    intros t T U h1 h2; inversion h2; subst; inversion h1; subst; eauto.
Qed.

Print value.
Lemma canonical_form_pair:
    forall t U V,
        empty |= t \in TProd U V ->
        value t ->
        exists a b,
            value a /\ value b /\ t = tpair a b.
        
            intros t U V h1 h2; inversion h2; subst; inversion h1; subst; eauto; tauto.
Qed.

Lemma canonical_form_sum:
    forall t U V,
        empty |= t \in TSum U V ->
        value t ->
        exists x,
            value x /\ (t = inr U x \/ t = inl V x).

        intros t U V h1 h2; inversion h2; subst; inversion h1; subst; eauto; tauto.
Qed.

Lemma canonical_form_unit:
    forall t,
        empty |= t \in TUnit ->
        value t ->
        t = unit.

        intros t h1 h2; inversion h2; subst; inversion h1; subst; eauto.
Qed.

Lemma canonical_form_list:
    forall t T,
        empty |= t \in TList T ->
        value t ->
        t = tnil T \/ (exists head tail,
                        value head /\ value tail /\ t = tcons head tail).

    intros t T h1 h2; inversion h2; subst; inversion h1; subst;  try tauto.
    right; eauto; tauto.

Qed.

Theorem progress:
    forall t T,
        empty |= t \in T ->
        value t \/ (exists t', t ==> t').

    intros t; induction t; intros;
    inversion H; subst; eauto;
    try (repeat match goal with
    | [H1 : _ -> _ -> value ?X \/ ?H |- _]
        => assert (value X \/ H) as HHH; eauto;
            destruct HHH; generalize H1; clear H1
    end ; intros); try
    (match goal with 
        | [ |- value (?X) \/ _ ]
            => assert (value X); eauto; try (tauto; eauto); fail
            end); right;
    
    repeat (match goal with 
        | [H1 : value ?T, H2 : _ |= ?T \in TNat |- _] =>
            inversion H1; subst;inversion H2; subst;
            generalize H1; generalize H2; clear H1; clear H2
        | [H1 : value ?T, H2 : _ |= ?T \in TArrow _ _ |- _] =>
        inversion H1; subst;inversion H2; subst;
        generalize H1; generalize H2; clear H1; clear H2 
        | [H1 : value ?T, H2 : _ |= ?T \in TProd _ _ |- _] =>
        inversion H1; subst;inversion H2; subst;
        generalize H1; generalize H2; clear H1; clear H2 
        | [H1 : value ?T, H2 : _ |= ?T \in TSum _ _ |- _] =>
        inversion H1; subst;inversion H2; subst;
        generalize H1; generalize H2; clear H1; clear H2     
            end); intros; try (esplit; eauto; fail)
    ;
    try (
    repeat (match goal with
    | [ H1 : exists _, _ |- _] => destruct H1
    end); esplit; eauto; fail
    ).

    inversion H; subst. inversion H2.
    destruct i; subst. exists t2; eauto.
    assert (S i <> 0); eauto.
    destruct i; subst. exists t2; eauto.
    assert (S i <> 0); eauto.
    destruct i; subst. exists t2; eauto.
    assert (S i <> 0); eauto.
    destruct i; subst. exists t2; eauto.
    assert (S i <> 0); eauto.

    inversion H1; subst; inversion H10; subst; eauto.
    inversion H1; subst; inversion H10; subst; eauto.
Qed.


(* We need the 'occurs_free' tool again. *)
Print tm.

Inductive occurs_free : id -> tm -> Prop :=
    | occurs_free_var :
        forall i,
            occurs_free i (tvar i)
    | occurs_free_abs :
        forall i j v T,
            i <> j ->
            occurs_free i v ->
            occurs_free i (tabs j T v)
    | occurs_free_app0 :
        forall i a b,
            occurs_free i a ->
            occurs_free i (tapp a b) 
    | occurs_free_app1 :
            forall i a b,
                occurs_free i b ->
                occurs_free i (tapp a b) 
    | occurs_free_succ :
        forall i x,
            occurs_free i x ->
            occurs_free i (tsucc x)
    | occurs_free_pred :
        forall i x,
            occurs_free i x ->
            occurs_free i (tpred x)
    | occurs_free_mult0:
        forall i a b,
            occurs_free i a ->
            occurs_free i (tmult a b)
    | occurs_free_mult1:
            forall i a b,
                occurs_free i b ->
                occurs_free i (tmult a b)     
    | occurs_free_if0 :
        forall i t t0 t1,
            occurs_free i t ->
            occurs_free i (tif0 t t0 t1)
    | occurs_free_if1 :
            forall i t t0 t1,
                occurs_free i t0 ->
                occurs_free i (tif0 t t0 t1)
    | occurs_free_if2 :
            forall i t t0 t1,
                occurs_free i t1 ->
                occurs_free i (tif0 t t0 t1)
    | occurs_free_let0 :
        forall i j x v,
            occurs_free i v ->
            i <> j ->
            occurs_free i (tlet j x v)
    | occurs_free_let1 :
        forall i j x v,
            occurs_free i x ->
            occurs_free i (tlet j x v)
    | occurs_free_pair0:
        forall i a b,
            occurs_free i a ->
            occurs_free i (tpair a b)
    | occurs_free_pair1:
            forall i a b,
                occurs_free i b ->
                occurs_free i (tpair a b)
    | occurs_free_fst:
        forall i x,
            occurs_free i x ->
            occurs_free i (tfst x)
    | occurs_free_snd :
        forall i x,
            occurs_free i x ->
            occurs_free i (tsnd x)
    | occurs_free_inl :
        forall i x T,
            occurs_free i x ->
            occurs_free i (inl T x)
    | occurs_free_inr :
        forall i x T,
            occurs_free i x ->
            occurs_free i (inr T x)
    | occurs_free_scase:
        forall i x u v lft rgt,
            occurs_free i x ->
            occurs_free i (scase x u lft v rgt)
    | occurs_free_scase0:
        forall i x u v lft rgt,
            i <> u ->
            occurs_free i lft ->
            occurs_free i (scase x u lft v rgt)
    | occurs_free_scase1:
        forall i x u v lft rgt,
            i <> v ->
            occurs_free i rgt ->
            occurs_free i (scase x u lft v rgt)
    | occurs_free_cons0:
        forall i h t,
            occurs_free i h ->
            occurs_free i (tcons h t)
    | occurs_free_cons1:
        forall i h t,
            occurs_free i t ->
            occurs_free i (tcons h t)
    | occurs_free_lcase:
        forall i l h t casenil casel,
            occurs_free i l ->
            occurs_free i (lcase l casenil h t casel)
    | occurs_free_lcase0:
        forall i l h t casenil casel,
            occurs_free i casenil ->
            occurs_free i (lcase l casenil h t casel)
    | occurs_free_lcase1:
            forall i l h t casenil casel,
                i <> h ->
                i <> t ->
                occurs_free i casel ->
                occurs_free i (lcase l casenil h t casel)
    | occurs_free_fix:
        forall i x,
            occurs_free i x ->
            occurs_free i (tfix x).

    Hint Constructors occurs_free.
Theorem occurs_dec :
    forall i x,
        {occurs_free i x} + {~occurs_free i x}.

    intros i x; generalize dependent i.
    induction x;
    intro ii;
    repeat (match goal with
        | [Hx : _ -> {_} + {_} |- _] =>
            destruct (Hx ii); generalize Hx; clear Hx
        end);
    intros;
    match goal with
    | [|- {?H} + {~?H}] =>
        try (assert H as HH; eauto; fail);
        try (assert (~H) as HH; eauto; intro HHH; inversion HHH; subst; eauto; fail)
    end.

    intros. destruct (eq_id_dec ii i); subst. left; eauto.
    right; intro h; inversion h; subst; destruct (n eq_refl).

    destruct (eq_id_dec ii i); subst. right; intro HH; inversion HH; subst. destruct (H2 eq_refl).
    left; eauto.
    destruct (eq_id_dec ii i); subst. right; intro HH; inversion HH; subst. destruct (H4 eq_refl).
    eauto.
    left; eauto.

    destruct (eq_id_dec ii i); destruct (eq_id_dec ii i0); subst; eauto. right; intro HH; inversion HH; subst; eauto.
    destruct (eq_id_dec ii i); destruct (eq_id_dec ii i0); subst; eauto. right; intro HH; inversion HH; subst; eauto. right ; intro HH; inversion HH; subst; eauto.
    destruct (eq_id_dec ii i); destruct (eq_id_dec ii i0); subst; eauto. right; intro HH; inversion HH; subst; eauto. right ; intro HH; inversion HH; subst; eauto.
    destruct (eq_id_dec ii i); destruct (eq_id_dec ii i0); subst; eauto;
    try (right; intro HH; inversion HH; subst; eauto; fail);
    try (left; eauto).
Qed. 

Definition closed (t : tm) :=
    forall i, ~occurs_free i t.

Lemma occurs_free_in_ctx:
    forall x i G T,
        G |= x \in T ->
        occurs_free i x ->
        exists U, byContext G i = Some U.
    intro x; induction x; 
    try (intros i G T h1 h2; inversion h1; inversion h2; subst; eauto; fail
    );
    try (
        intros i0 G T h1 h2; inversion h1; inversion h2; subst;
        repeat (match goal with 
            | [H1 : _ -> _ -> _ -> _ |= ?x \in  _ -> occurs_free _ ?x -> _ ,
                H2: _ |= ?x \in _, 
                H3 : occurs_free _ ?x |- _ ] => 
                destruct (H1 _ _ _ H2 H3); generalize H1 H2 H3; clear H1 H2 H3
        end) ;intros; cbn in *; 
        destruct (eq_id_dec i0 i); subst;
        try (
            match goal with
                | [H1 : ?x <> ?x |- _] => destruct (H1 eq_refl)
            end
        );
        eauto).

    intros. inversion H0 ; inversion H; subst. eauto.
    intros. inversion H0; inversion H; subst; eauto.
    destruct (IHx2 _ _ _ H16 H8). cbn in  *.
    destruct (eq_id_dec i1 i); subst; eauto. destruct (H4 eq_refl).
    intros. 
    destruct (IHx3 _ _ _ H17 H8). cbn in  *.
    destruct (eq_id_dec i1 i0); subst; eauto. 
    destruct (H4 eq_refl).
    intros. inversion H; inversion H0; subst; eauto.
    destruct (IHx3 _ _ _ H10 H20). cbn in *.
    destruct (eq_id_dec i1 i); destruct (eq_id_dec i1 i0); subst;
    try (match goal with
        | [H1 : ?x <> ?x |- _] => destruct (H1 eq_refl)
    end); eauto.

Qed.

Theorem empty_is_closed:
    forall x T,
        empty |= x \in T ->
        closed x.

    unfold closed; unfold not.
    intro x; induction x;
    try (intros T h1 k h2; inversion h1; inversion h2; subst; eauto; fail);
    try (    intros;
    pose occurs_free_in_ctx as e;
    destruct (e _ _ _ _ H H0); inversion H1).
Qed.


Theorem ctx_swap:
    forall x T U V ,
        U |= x \in T ->
        U =-= V ->
        V |= x \in T.
    
    intros x T U V h.
    generalize dependent V.
    induction h; try (unfold context_equivalence ; eauto; fail).

    intros. eapply tyVar; eauto. rewrite <- H0; auto.
    intros. eapply tyAbs; eauto.
    assert (update i T Gamma =-= update i T V); eauto.
    eapply update_inc. auto.
    
    intros. eapply tyLet. eapply IHh1. eapply update_inc. auto.
    eapply IHh2; eauto.

    intros. Print has_type. eapply tySCase; [eapply IHh1 | eapply IHh2 | eapply IHh3].
    eapply update_inc; eauto.
    eapply update_inc; eauto.
    auto.

    intros. eapply tyLCase; eauto. eapply IHh2.
    repeat eapply update_inc; auto.
Qed.

Hint Resolve  occurs_dec contrapositive  : occurs_free_db.

Hint Resolve refl_ctxeq trans_ctxeq ctx_swap update_permute update_shadow : ctx_db.


Lemma non_occurs_free_ctx_add:
forall x i T U G,
    G |= x \in T ->
    ~occurs_free i x ->
    update i U G |= x \in T.

intro x; induction x;
try (intros i T U G hh; inversion hh; subst;  eauto 10 with occurs_free_db
; fail).

intros. eapply tyVar. cbn.
inversion H; subst. destruct (eq_id_dec i i0); subst; eauto.
destruct (H0 (occurs_free_var _)).

intros. inversion H; subst. 
destruct (occurs_dec i0 x); destruct (eq_id_dec i0 i); subst;
eapply tyAbs. eapply ctx_swap. eauto. eapply symm_ctxeq. eapply update_shadow.
apply refl_ctxeq. assert (occurs_free i0 (tabs i t x)); eauto. destruct (H0 H1).
eapply ctx_swap. eauto. eapply symm_ctxeq. eapply update_shadow.
apply refl_ctxeq. eapply ctx_swap. eapply (IHx _ _ _ _ H6 n).
eapply update_permute; eauto. apply refl_ctxeq.
intros i T U G h1 h2; inversion h1; subst;
assert (~occurs_free i x1) as hh1; eauto with occurs_free_db;
assert (~occurs_free i x2) as hh2; eauto with occurs_free_db;
assert (~occurs_free i x3) as hh3; eauto with occurs_free_db;
eauto with occurs_free_db.

intros i0 T U G h1 h2; inversion h1; subst; eauto with occurs_free_db; eauto with ctx_db; eauto with occurs_free_db.
assert (~occurs_free i0 x1) as hh1; eauto with occurs_free_db.
destruct (eq_id_dec i0 i); subst; eapply tyLet; eauto with ctx_db.
eapply ctx_swap. apply H4. eapply symm_ctxeq. eapply update_shadow.
eapply refl_ctxeq. eauto.
assert (~occurs_free i0 x2); eauto 10 with occurs_free_db.
forwards : IHx2; eauto 5 with ctx_db. eapply ctx_swap; eauto with ctx_db.
eapply update_permute; eauto. eapply refl_ctxeq.

intros. assert (~occurs_free i1 x1); eauto with occurs_free_db.
inversion H; subst. 
Print has_type.
eapply tySCase; eauto with occurs_free_db.
destruct (eq_id_dec i1 i); subst; eauto with ctx_db.
Print symm_ctxeq.
eapply ctx_swap;  eauto 10 using symm_ctxeq with ctx_db. eapply symm_ctxeq; eauto with ctx_db.
eapply update_shadow. eapply refl_ctxeq.
assert (~occurs_free i1 x2); eauto with occurs_free_db.
eapply ctx_swap; try eapply update_permute; eauto.
eapply refl_ctxeq.
destruct (eq_id_dec i0 i1); subst.
eapply ctx_swap; eauto using update_shadow.
eapply symm_ctxeq; eapply update_shadow; eapply refl_ctxeq.
eapply ctx_swap; try eapply update_permute. 
eapply IHx3; eauto with occurs_free_db. eauto. eapply refl_ctxeq.

intros. inversion H; subst. eapply tyLCase; eauto with occurs_free_db.
destruct (eq_id_dec i i1); subst.
eapply ctx_swap; try eapply update_permute. 
eapply ctx_swap; try eapply update_inc. eapply ctx_swap ; try eapply update_permute; eauto.
eapply refl_ctxeq. eapply symm_ctxeq; eapply update_shadow.
eapply refl_ctxeq. eauto. eapply refl_ctxeq.
destruct (eq_id_dec i1 i0); subst.
eapply ctx_swap; try eapply update_inc; eauto.
eapply symm_ctxeq; eapply update_shadow. eapply refl_ctxeq.
assert (~occurs_free i1 x3); eauto with occurs_free_db.
pose (IHx3 _ _ U _ H10 H1).
assert (update i T0 (update i1 U (update i0 (TList T0) G)) |= x3 \in T).
eapply ctx_swap; try eapply update_permute; eauto.
eapply refl_ctxeq.
eapply ctx_swap; try eapply update_inc; eauto.
eapply update_permute. eauto. eapply refl_ctxeq.

Qed.


Theorem empty_is_strong :
    forall G t T,
        empty |= t \in T ->
        G |= t \in T.

    intro G; induction G; eauto.
    intros. pose (empty_is_closed _ _ H).
    unfold closed in *.
    pose (c i).
    eapply non_occurs_free_ctx_add; eauto.
Qed.

Lemma app_preserv:
    forall t x y T G U,
        U |= tabs x T t \in TArrow T G ->
        empty |= y \in T ->
        U |= [x := y] t \in G.

    intro t; induction t; eauto;
    cbn; intros x y T G U h1 h2;
    try (inversion h1; subst;
    try match goal with
        | [H1: update _ _ _ |= _ \in _ |- _] =>
    inversion H1;subst; eauto 10
    end; fail).

    intros. inversion h1; subst. 
    unfold subst. inversion H1; subst.
    cbn in *. 
    destruct (eq_id_dec i x); destruct (eq_id_dec x i); subst;
    try match goal with
        | [H1 : ?x <> ?x |- _] => destruct (H1 eq_refl)
        end.
    inversion H2; subst;eauto. eapply empty_is_strong; eauto.
    eauto.

    cbn; intros. inversion h1; subst. inversion H1; subst.
    destruct (eq_id_dec i x); subst. eapply tyAbs. eapply ctx_swap; try eapply update_shadow.
    eauto. eapply refl_ctxeq. eapply tyAbs. eapply IHt; eauto.
    eapply tyAbs; eapply ctx_swap ; try eapply update_permute; eauto.
    eapply refl_ctxeq.

    inversion h1; subst. inversion H1; subst.
    destruct (eq_id_dec i x); subst; eauto 10;
    eapply tyLet. eapply ctx_swap; try eapply update_shadow; eauto.
    eapply refl_ctxeq. 
    eauto. eapply IHt2. eapply tyAbs. eapply ctx_swap; try eapply update_permute; eauto.
    eapply refl_ctxeq. eapply empty_is_strong; eauto.
    eapply IHt1; eauto.

    inversion h1; subst. inversion H1; subst; eauto.
    eapply tySCase; eauto. destruct (eq_id_dec i x); subst.
    eapply ctx_swap; try eapply update_shadow; eauto. eapply refl_ctxeq.
    eapply IHt2. eapply tyAbs; eauto. eapply ctx_swap; try eapply update_permute;eauto.
    eapply refl_ctxeq; eauto. eauto.
    destruct (eq_id_dec i0 x); subst; eauto. 
    eapply ctx_swap; try eapply update_shadow; eauto. eapply refl_ctxeq.
    eapply IHt3; eauto. eapply tyAbs; eauto. eapply ctx_swap; try eapply update_permute; eauto 10.
    eapply refl_ctxeq.

    inversion h1; subst. inversion H1; subst; eapply tyLCase; destruct (eq_id_dec i x); subst; eauto.
    eapply ctx_swap; try (eapply symm_ctxeq; eapply update_shadow); eauto.
    eapply trans_ctxeq. eapply update_inc. eapply update_permute; eauto.
    eapply refl_ctxeq. eapply update_shadow. eapply refl_ctxeq.
    destruct (eq_id_dec i0 x); subst. eapply ctx_swap; try eapply update_inc. eapply H9.
    eapply update_shadow. eapply refl_ctxeq. eapply IHt3. eapply tyAbs.
    eapply ctx_swap; try eapply H9. eapply trans_ctxeq; try (eapply update_inc; eapply update_permute); eauto.
    eapply refl_ctxeq. eapply update_permute; eauto. eapply refl_ctxeq. eauto.
Qed.

Theorem preservation :
    forall t t' T,
        empty |= t \in T ->
        step t t' ->
        empty |= t' \in T.

    intro t; induction t;
    try (intros t' T h1 h2; try value_stepping_false; fail);
    try (intros t' T h1 h2; inversion h1; inversion h2; subst; eauto; fail).

    intros t' T h1 h2; inversion h1; subst; inversion h2; subst; eauto.
    eapply app_preserv; eauto. inversion H2; subst; eauto.

    intros t' T h1 h2; inversion h1; inversion h2; subst; eauto.
    eapply app_preserv; eauto.

    intros t' T h1 h2; inversion h1; inversion h2; subst; eauto.
    inversion H1; subst; eauto.
    intros t' T h1 h2; inversion h1; inversion h2; subst; eauto.
    inversion H1; subst; eauto.
    intros t' T h1 h2; inversion h1; inversion h2; subst; eauto.
    eapply app_preserv; eauto. inversion H8; eauto.
    eapply app_preserv; eauto. inversion H8; eauto.

    intros t' T h1 h2; inversion h1; inversion h2; subst; eauto.
    inversion H9;subst; eauto.
    eapply app_preserv; eauto. eapply tyAbs. eapply app_preserv; eauto.
    eapply tyAbs; eauto. eapply ctx_swap; try eapply update_permute; eauto.
    eapply refl_ctxeq.
    
    intros t' T h1 h2; inversion h1; inversion h2; subst; eauto.
    inversion h1; subst; inversion H1; subst; eauto.
    eapply app_preserv; eauto.
Qed.


Definition stuck (t: tm) : Prop :=
(normal_form step) t /\ ~ value t.

Notation "t '==>*' t'" := (multi step t t') (at level 40).

Corollary soundness :
    forall t t' T,
        empty |= t \in T ->
        t ==>* t' ->
        ~(stuck t').


        unfold stuck; unfold not; unfold normal_form; unfold not.
        intros t t' T h1 h.
        generalize dependent T.
        induction h; eauto; try tauto.
        intros T h1 h2. destruct h2. 
        destruct (progress _ _ h1); eauto.
        intros T h1 h2; destruct h2.
        pose (preservation _ _ _ h1 H).
        eauto.
Qed.


        


    







    
    