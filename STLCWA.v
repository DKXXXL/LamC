
Require Import SfLib.


Module STLCARITH.

Inductive ty : Type :=
    | TArrow : ty -> ty -> ty
    | TNat : ty.

    Hint Constructors ty.
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

    Hint Constructors tm.

Inductive Context {type : Type} : Type :=
    | empty : Context
    | update : id -> type -> Context -> Context.
    
    Hint Constructors Context.
Fixpoint byContext (ctx : Context) (i : id) : option ty :=
    match ctx with 
        | empty => None
        | update x Ty ctx' =>
            if (eq_id_dec i x) then Some Ty else byContext ctx' i
            end.

Reserved Notation "Gamma '|=' t '\in' T" (at level 40).            

Inductive has_type : Context -> tm -> ty -> Type :=
    | tyVar : 
        forall G i T,
            byContext G i = Some T ->
            G |= tvar i \in T
    | tyApp :
        forall Gamma a b G T,
        Gamma |= a \in TArrow G T ->
        Gamma |= b \in G ->
        Gamma |= tapp a b \in T
    | tyAbs :
        forall Gamma i x G T,
        update i G Gamma |= x \in T ->
        Gamma |= tabs i G x \in TArrow G T
    | tyNat :
        forall i Gamma,
        Gamma |= tnat i \in TNat
    | tySucc :
        forall x Gamma,
        Gamma |= x \in TNat ->
        Gamma |= tsucc x \in TNat
    | tyPred :
        forall x Gamma,
        Gamma |= x \in TNat ->
        Gamma |= tpred x \in TNat
    | tyMult :
        forall x y Gamma,
        Gamma |= x \in TNat ->
        Gamma |= y \in TNat ->
        Gamma |= tmult x y \in TNat
    | tyIf :
        forall t t0 t1 Gamma T,
        Gamma |= t0 \in T ->
        Gamma |= t1 \in T ->
        Gamma |= t \in TNat ->
        Gamma |= tif0 t t0 t1 \in T
    where "Gamma '|=' t '\in' T " := (has_type Gamma t T).

    Hint Constructors has_type.
    Reserved Notation "'[' x ':=' s ']' t" (at level 20).
    
    

Fixpoint subst (i : id) (t org : tm) : tm :=
    match org with
        | tvar j => if(eq_id_dec i j) then t else org
        | tapp a b => tapp ([i := t] a) ([i := t] b)
        | tabs x T y => tabs x T (if (eq_id_dec i x) then y else ([i := t] y))
        | tsucc x => tsucc ([i := t] x)
        | tpred y => tpred ([i := t] y)
        | tmult x y => tmult ([i := t] x) ([i := t] y)
        | tif0 x t0 t1 => tif0 ([i := t] x) ([i := t] t0) ([i := t] t1)
        | _ => org
        end
        where "'[' x ':=' s ']' t" := (subst x s t).


Inductive value : tm -> Prop :=
    | vnat : 
        forall n,
            value (tnat n)
    | vabs :
        forall x T y,
            value (tabs x T y).

Reserved Notation "t '==>' t'" (at level 40).
        
    Hint Constructors value.
Inductive step : tm -> tm -> Prop :=
    | ST_AppAbs :
        forall abs abs' arg,
        abs ==> abs' ->
        tapp abs arg ==> tapp abs' arg
    | ST_AppArg :
        forall abs arg arg',
        value abs ->
        arg ==> arg' ->
        tapp abs arg ==> tapp abs arg'
    | ST_App :
        forall x T y arg,
        value arg ->
        tapp (tabs x T y) arg ==> [x := arg] y
    | ST_Succ0 :
        forall n n',
        n ==> n' ->
        tsucc n ==> tsucc n'
    | ST_Succ1 :
        forall n,
        tsucc (tnat n) ==> tnat (S n)
    | ST_Pred0 :
        forall n n',
        n ==> n' ->
        tpred n ==> tpred n'
    | ST_Pred1 :
        forall n,
        tpred (tnat n) ==> tnat (pred n)
    | ST_Mult0 :
        forall n0 n0' n1,
        n0 ==> n0' ->
        tmult n0 n1 ==> tmult n0' n1
    | ST_Mult1 :
        forall n0 n1 n1',
        value n0 ->
        n1 ==> n1' ->
        tmult n0 n1 ==> tmult n0 n1'
    | ST_Mult2 :
        forall n0 n1,
        tmult (tnat n0) (tnat n1) ==> tnat (n0 * n1)
    | ST_If0 :
        forall t t' t0 t1,
        t ==> t' ->
        tif0 t t0 t1 ==> tif0 t' t0 t1
    | ST_IfFalse :
        forall t0 t1,
        tif0 (tnat 0) t0 t1 ==> t1
    | ST_IfTrue :
        forall t t0 t1,
        t <> 0 ->
        tif0 (tnat t) t0 t1 ==> t0
    where "t '==>' t'" := (step t t').

    Hint Constructors step.

    Theorem deterministic_step :
        deterministic step.
    
    unfold deterministic.
    intros x y1 y2 h.
    generalize dependent y2.
    elim h; intros.

    inversion H1; subst. pose (H0 _ H5). rewrite e; auto.
    inversion H4; subst. inversion H.

    Abort.

    Lemma value_cant_step:
        forall n n',
        value n ->
        n ==> n' ->
        False.
    intros n n' h.
    generalize dependent n'.
    elim h; subst; intros.
    inversion H. inversion H.
Qed.



Ltac value_no_stepping_ :=
    match goal with
     | [ H1 : tabs ?X ?T ?Y ==> ?Z |- _ ] => inversion H1
     | [ H1 : tnat ?N ==> ?Z |- _ ] => inversion H1
     | [ H1 : value ?X, H2 : ?X ==> ?Z |- _ ] => destruct (value_cant_step _ _ H1 H2)
     end.

Ltac value_no_stepping := repeat value_no_stepping_.

Theorem deterministic_step :
     deterministic step.
     
     unfold deterministic.
     intros x y1 y2 h.
     generalize dependent y2.
     elim h; intros until y2; intro HH;
     inversion HH; subst; try value_no_stepping; auto.

     pose (H0 _ H4). rewrite e; auto.

     pose (H1 _ H6). rewrite e; auto.

     rewrite (H0 _ H2); auto.

     rewrite (H0 _ H2); auto.

     rewrite (H0 _ H4); auto.

     rewrite (H1 _ H6); auto.

     rewrite (H0 _ H5); auto.

     destruct (H3 eq_refl).
     destruct (H eq_refl).

Qed.

Lemma canonical_forms_bool :
    forall t,
    empty |= t \in TNat ->
    value t ->
    (exists i, t = tnat i).

    intros. inversion H0; subst. 
    exists n; auto.
    inversion H; subst.
Qed.

Lemma canonical_forms_fun :
    forall t G T,
        empty |= t \in TArrow G T ->
        value t ->
        (exists x v, t = tabs x G v).

    intros. inversion H0; subst.
    inversion H.
    exists x. exists y. inversion H; subst. auto.

Qed.

Hint Unfold byContext.

Theorem progress :
    forall t T,
        empty |= t \in T ->
        value t \/ (exists t', t ==> t').

    intro. elim t; intros.
    inversion H; subst.  inversion H2.

    inversion H1; subst. 
    right.
    destruct (H _ H5). 
    destruct (H0 _ H7). 
    inversion H2; subst. inversion H5.
    exists ([x := t1] y). eauto.

    destruct H3. exists (tapp t0 x). eauto.
    destruct H2. exists (tapp x t1). eauto.
    
    left; eauto.
    left; eauto.

    right. inversion H0; subst. 
    destruct (H _ H3). 
    inversion H1; subst.
    exists (tnat (S n)). eauto.
    inversion H3.
    destruct H1.
    exists (tsucc x). eauto.

    right. inversion H0; subst.
    destruct (H _ H3). inversion H1; subst.
    exists (tnat (pred n)); eauto.
    inversion H3.

    destruct H1.
    exists (tpred x). eauto.

    right. inversion H1; subst.
    destruct  (H _ H5). destruct (H0 _ H7).
    inversion H2; inversion H3; subst.
    exists (tnat (n * n0)); eauto.

    inversion H7. inversion H5. inversion H5.

    destruct H3.
    exists (tmult t0 x). eauto.

    destruct H2.
    exists (tmult x t1). eauto.

    right. inversion H2; subst. 
    destruct (H _ H10). inversion H3; subst.
    destruct n. exists t2; eauto.
    assert (S n <> 0); eauto.
    inversion H10. 
    destruct H3.
    exists (tif0 x t1 t2); eauto.
Qed.







    



     
     















        