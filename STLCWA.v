
Require Import SfLib.

Require Import Smallstep.

Require Import Coq.Relations.Relation_Definitions.


Inductive Context {type : Type} : Type :=
| empty : Context
| update : id -> type -> Context -> Context.

Hint Constructors Context.

Fixpoint byContext {type : Type} (ctx : Context) (i : id) : option type :=
match ctx with 
    | empty => None
    | update x Ty ctx' =>
        if (eq_id_dec i x) then Some Ty else byContext ctx' i
        end.


Definition context_equivalence {type : Type}  : relation Context :=
        fun (x y : Context (type := type)) => forall i, byContext x i = byContext y i.
    
    Notation "x '=-=' y" := (context_equivalence x y) (at level 40).
    
    
    Print reflexive.
    Print equiv.

    
    Theorem refl_ctxeq {x : Type}:
        reflexive _ (context_equivalence (type := x )).
        unfold reflexive; unfold context_equivalence. auto.
    Qed.
    
    Hint Unfold reflexive.

    Theorem symm_ctxeq {x : Type}:
        symmetric _ (context_equivalence (type := x)).
        unfold symmetric; unfold context_equivalence. auto.
    Qed.

    Hint Unfold symmetric.
    Theorem trans_ctxeq {x : Type}:
    transitive _ (context_equivalence (type :=x)).

    unfold transitive.
    
    unfold context_equivalence.
    intros. rewrite H; auto.
Qed.

Hint Unfold transitive.

Theorem equiv_ctxeq {x : Type}:
    equiv _ (context_equivalence (type := x)).

    unfold equiv.
    pose (refl_ctxeq (x := x)). pose (symm_ctxeq (x := x)). pose (trans_ctxeq (x:= x)).
    tauto.
Qed.
    
    Theorem update_shadow {z : Type}:
        forall i (x y : z) (U V : Context (type := z)),
            U =-= V ->
            update i x (update i y U) =-= update i x V.
            
        unfold context_equivalence. intros.
        cbn. destruct (eq_id_dec i0 i); auto.
    
    Qed.
    
    Theorem update_permute {z : Type}:
        forall i j (x y : z) U V,
            i <> j ->
            U =-= V ->
            update i x (update j y U) =-= update j y (update i x U).
    
        unfold context_equivalence. 
        intros. cbn. destruct (eq_id_dec i0 i); destruct (eq_id_dec i0 j); auto; subst.
        destruct (H eq_refl).
    Qed.
    
    Theorem update_inc {z : Type}:
        forall i (x: z) U V,
            U =-= V ->
            update i x U =-= update i x V.
    
        unfold context_equivalence.
        intros. cbn. destruct (eq_id_dec i0 i); subst; auto.
    Qed.




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

Reserved Notation "Gamma '|=' t '\in' T" (at level 40).            

Inductive has_type : Context -> tm -> ty -> Prop :=
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
        | tabs x T y => tabs x T (if (eq_id_dec x i) then y else ([i := t] y))
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

Theorem preservation :
    forall t t' T,
        empty |= t \in T ->
        step t t' ->
        empty |= t' \in T.

    intro. elim t; intros.
    inversion H0.
    
    inversion H1; inversion H2; subst; eauto.

    Abort.

Lemma app_preserv:
    forall t x y T G U,
        U |= tabs x T t \in TArrow T G ->
        empty |= y \in T ->
        U |= [x := y] t \in G.
    intro t. elim t; intros.
    inversion H; subst. unfold subst.
    inversion H3; subst. unfold byContext in *. 
    destruct (eq_id_dec i x); subst. inversion H4; subst.
    rewrite eq_id_dec_id.

    Abort.


(*
Theorem update_shadow:
    forall U i x y,
    update i x (update i y U) =-= update i x U.

    unfold context_equivalence.
    intro. induction U; intros.
    unfold byContext in *.
    destruct (eq_id_dec i0 i); subst; auto.

    unfold byContext in *.
    destruct (eq_id_dec i1 i0); subst; auto.

Qed.

Theorem update_permute:
    forall U i j x y,
    i <> j ->
    update i x (update j y U) =-= update j y (update i x U).

    intro. 
    
    induction U; intros.
    unfold context_equivalence. intros.
    unfold byContext in *. destruct (eq_id_dec i0 i); destruct (eq_id_dec i0 j); subst; eauto.
    destruct (H eq_refl).

    destruct (eq_id_dec i j); subst.
    Abort.

Print relation.
Print equiv.

Theorem equiv_ctx_eq:
    equiv context_equivalence.
*)



Inductive occurs_free : id -> tm -> Prop :=
    | occurs_free_var :
        forall i,
            occurs_free i (tvar i)
    | occurs_free_abs :
        forall i j x T,
            occurs_free i x ->
            i <> j ->
            occurs_free i (tabs j T x)
    | occurs_free_app1 :
        forall i x y,
            occurs_free i x ->
            occurs_free i (tapp x y)
    | occurs_free_app2 :
        forall i x y,
            occurs_free i y ->
            occurs_free i (tapp x y)
    | occurs_free_succ :
        forall i x,
            occurs_free i x ->
            occurs_free i (tsucc x)
    | occurs_free_pred :
        forall i x,
            occurs_free i x ->
            occurs_free i (tpred x)
    | occurs_free_mult1 :
        forall i x y,
            occurs_free i x ->
            occurs_free i (tmult x y)
    | occurs_free_mult2 :
        forall i x y,
            occurs_free i y ->
            occurs_free i (tmult x y)
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
            occurs_free i (tif0 t t0 t1).

    Hint Constructors occurs_free.
Theorem occurs_dec:
    forall i x,
    {occurs_free i x} + {~occurs_free i x}.

    intros i x. generalize dependent i.
    induction x; eauto.
    intros. 
    destruct (eq_id_dec i0 i); subst. 
    left; eauto.
    right; intros H; inversion H; subst. destruct (n eq_refl).

    intros. destruct (IHx1 i). left; eauto.
    destruct (IHx2 i). left; eauto.
    right; intro. inversion H; subst; eauto.

    intro. destruct (IHx i0). destruct (eq_id_dec i0 i); subst.
    right; intro HH; inversion HH; subst. destruct (H4 eq_refl).
    left; eauto.

    right; intro HH; inversion HH; subst; eauto.

    intros; right; intro HH; inversion HH.

    intros i; destruct (IHx i). left; eauto. right; intro HH; inversion HH; subst; eauto.

    intros i; destruct (IHx i). left; eauto. right; intro HH; inversion HH; subst; eauto.
    
    intros i; destruct (IHx1 i).
    left; eauto. destruct (IHx2 i). left; eauto.
    right; intro HH; inversion HH; subst; eauto.

    intros i; destruct (IHx1 i).
    left; eauto. destruct (IHx2 i). left; eauto.
    destruct (IHx3 i). left; eauto.
    right; intro HH; inversion HH; subst; eauto.
Qed.

Definition closed (x : tm) :=
    forall i, ~ occurs_free i x.

Theorem ctx_swap:
    forall x U V T ,
        U |= x \in T ->
        U =-= V ->
        V |= x \in T.

    intros x U V T h.
    generalize dependent V.
    induction h; unfold context_equivalence; intros; eauto.
    eapply tyVar. rewrite <- H0. auto.

    eapply tyAbs. 
    pose (update_inc (z := ty)).
    pose (update_inc i G _ _ H).
    eauto.
Qed.

Theorem non_occurs_free_ctx_rm:
    forall v i x U T,
    update i x U |= v \in T ->
    (~occurs_free i v) ->
    U |= v \in T.

    intros v i x U T h.
    remember (update i x U) as u.
    generalize Hequ.
    induction h; subst; eauto.
    intros. cbn in H. 
    destruct (eq_id_dec i0 i); subst. destruct (H0 (occurs_free_var i)).
    eauto.

    intros. 
    pose (contrapositive _ _ (occurs_dec _ _) (occurs_free_app1 i a b)).
    pose (contrapositive _ _ (occurs_dec _ _) (occurs_free_app2 i a b)).

    pose (IHh2 eq_refl eq_refl).
    pose (IHh1 eq_refl eq_refl).
    eapply tyApp; eauto.

    intros. destruct (occurs_dec i x0). 
    destruct (eq_id_dec i i0); subst.
    
    pose (update_shadow i0 G x U U (refl_ctxeq _ )).
    pose (ctx_swap _ _ _ _ h c).
    eauto.

    assert (occurs_free i (tabs i0 G x0)) as HH; eauto.
    destruct (H HH).

    eauto.
    Abort.


Theorem non_occurs_free_ctx_rm:
    forall v i x U T,
    update i x U |= v \in T ->
    (~occurs_free i v) ->
    U |= v \in T.

    intro v; induction v; eauto.
    intros. inversion H; subst.
    cbn in H3. destruct (eq_id_dec i i0); subst.
    destruct (H0 (occurs_free_var i0)).
    eauto.

    intros. 
    pose (contrapositive _ _ (occurs_dec _ _) (occurs_free_app1 i v1 v2)).
    pose (contrapositive _ _ (occurs_dec _ _) (occurs_free_app2 i v1 v2)).
    inversion H; subst. eapply tyApp; eauto.

    intros. inversion H; subst.
    destruct (occurs_dec i0 v);
    destruct (eq_id_dec i0 i); subst. inversion H; subst.
    
    pose (update_shadow i t x U U (refl_ctxeq _ )).
    pose (ctx_swap _ _ _ _ H6 c).
    eauto.

    assert (occurs_free i0 (tabs i t v)) as HH; eauto.
    destruct (H0 HH).

    inversion H; subst. 
    pose (update_shadow i t x U U (refl_ctxeq _ )).
    pose (ctx_swap _ _ _ _ H6 c).
    eauto.
    pose (update_permute i0 i x t U U n0 (refl_ctxeq _)).
    Print symm_ctxeq.
    pose (symm_ctxeq _ _ c).
    pose (ctx_swap _ _ _ _ H6 c0).
    eauto.

    intros. inversion H; subst. eauto.

    intros. inversion H; subst.
    Print occurs_free_succ. 
    pose (contrapositive _ _ (occurs_dec _ _) (occurs_free_succ i v)).
    eauto.

    intros. inversion H; subst.
    pose (contrapositive _ _ (occurs_dec _ _) (occurs_free_pred i v)).
    eauto.

    intros. inversion H; subst.
    pose (contrapositive _ _ (occurs_dec _ _) (occurs_free_mult1 i v1 v2)).
    pose (contrapositive _ _ (occurs_dec _ _) (occurs_free_mult2 i v1 v2)).
    eapply tyMult; eauto.

    intros.
     inversion H; subst.
     pose (contrapositive _ _ (occurs_dec _ _) (occurs_free_if0 i v1 v2 v3)).
     pose (contrapositive _ _ (occurs_dec _ _) (occurs_free_if1 i v1 v2 v3)).
     pose (contrapositive _ _ (occurs_dec _ _) (occurs_free_if2 i v1 v2 v3)).
     eapply tyIf; eauto.

Qed.

   
Lemma occurs_free_is_in_ctx:
forall i x U T,
    U |= x \in T ->
    occurs_free i x ->
    (exists K, byContext U i = Some K).

intros i x U T h0 h.
generalize dependent U.
generalize dependent T.
induction h; intros; eauto; try (inversion h0; subst; eauto).

inversion h0; subst. 
destruct (IHh _ _ H5).
cbn in H0. destruct (eq_id_dec i j); subst; eauto.
destruct (H eq_refl).
Qed.



Theorem empty_means_closed:
    forall t T,
        empty |= t \in T ->
        closed t.

    unfold closed.
    intros t.
    induction t; intros; intro.
    inversion H; subst. inversion H3.

    inversion H; subst. inversion H0; subst. 
    destruct ((IHt1 _ H4 i) H3).
    destruct ((IHt2 _ H6 i) H3).

 

    inversion H; subst; inversion H0; subst.
    destruct (occurs_free_is_in_ctx _ _ _ _ H H0).
    inversion H1.

    inversion H0. 

    inversion H; inversion H0; subst; eauto.
    eapply IHt. apply H3. apply H7.

    inversion H; inversion H0; subst; eapply IHt. apply H3. apply H7.
    inversion H; inversion H0; subst. eapply IHt1; eauto. eapply IHt2; eauto.
    inversion H; inversion H0; subst. eapply IHt1; eauto. eapply IHt2; eauto. eapply IHt3; eauto.

Qed.


Theorem empty_is_strong:
    forall x T U,
        empty |= x \in T ->
        U |= x \in T.

    intros x T U. 
    generalize dependent x;
    generalize dependent T.
    induction U; intros; auto.
    pose (empty_means_closed x T H).
    unfold closed in c.
    pose (c i).
    Print non_occurs_free_ctx_rm.
    Abort.

Theorem occurs_free_ctx_add :
    forall i j x T U,
    U |= x \in T ->
    ~(occurs_free i x) ->
    update i j U |= x \in T.

    intros i j x.
    generalize dependent i;
    generalize dependent j.

    induction x; eauto.
    intros. inversion H; subst.
    eapply tyVar. cbn.
    destruct (eq_id_dec i i0); subst.
    destruct (H0 (occurs_free_var i0)).
    auto.

    intros. inversion H; subst. eapply tyApp; eauto.

    intros. inversion H; subst. 
    destruct (occurs_dec i0 x); subst.
    destruct (eq_id_dec i0 i); subst.
    eapply tyAbs. 
    eapply ctx_swap. eapply H6. eapply symm_ctxeq.
    eapply update_shadow. eapply refl_ctxeq.
    assert (occurs_free i0 (tabs i t x)). eauto.
    destruct (H0 H1).
    destruct (eq_id_dec i0 i); subst.
    eapply tyAbs. eapply ctx_swap. eapply H6.
    eapply symm_ctxeq. eapply update_shadow. eapply refl_ctxeq.
    eapply tyAbs. eapply ctx_swap. eapply IHx. eapply H6. eauto.
    eapply update_permute; eauto. eapply refl_ctxeq.

    intros. inversion H; subst; eauto.

    intros. inversion H; subst; eauto. eapply tySucc; eauto.

    intros. inversion H; subst;eauto. eapply tyPred; eauto.

    intros. inversion H; subst; eauto. eapply tyMult; eauto.

    intros. inversion H; subst; eauto. eapply tyIf; eauto.
Qed.

Theorem empty_is_strong:
forall x T U,
    empty |= x \in T ->
    U |= x \in T.

intros x T U. 
generalize dependent x;
generalize dependent T.
induction U; intros; auto.
pose (empty_means_closed x T H).
unfold closed in c.
pose (c i).
eapply occurs_free_ctx_add; eauto.
Qed.


Lemma app_preserv:
forall t x y T G U,
    U |= tabs x T t \in TArrow T G ->
    empty |= y \in T ->
    U |= [x := y] t \in G.
intro t. elim t; intros.
inversion H; subst. unfold subst.
inversion H3; subst. cbn in H4.
destruct (eq_id_dec i x); subst. inversion H4; subst.
rewrite eq_id_dec_id. eapply empty_is_strong; eauto.
destruct (eq_id_dec x i); subst. destruct (n eq_refl).
eapply tyVar; auto.

inversion H1; subst.
change (U |= tapp ([x := y] t0) ([x := y] t1) \in G).
inversion H5; subst. 
eapply tyApp; eauto.

change (U |= tabs i t0 (if eq_id_dec i x then t1 else [x := y] t1) \in G).
inversion H0; subst. inversion H4; subst.
destruct (eq_id_dec i x); subst.
eapply tyAbs. eapply ctx_swap. apply H8. eapply update_shadow. eapply refl_ctxeq.
eapply tyAbs. eapply H. eapply tyAbs. eapply ctx_swap. eapply H8. eapply update_permute; eauto. eapply refl_ctxeq. auto.

inversion H; subst. inversion H3; subst. unfold subst. eauto.

inversion H0; subst. inversion H4; subst. 
change (U |= tsucc ([x := y] t0) \in TNat).
eapply tySucc. eapply H; eauto.

inversion H0; subst. inversion H4; subst.
change (U |= tpred ([x := y] t0) \in TNat).
eauto.

inversion H1; subst. inversion H5; subst.
change (U |= tmult ([ x:= y] t0) ([x := y] t1) \in TNat).
eapply tyMult; eauto.

inversion H2; subst. inversion H6; subst.
change (U |= tif0 ([x := y] t0) ([x := y] t1) ([x := y] t2) \in G).
eapply tyIf; eauto.

Qed.


Theorem preservation :
forall t t' T,
    empty |= t \in T ->
    step t t' ->
    empty |= t' \in T.

intro. elim t; intros.
inversion H0.

inversion H1; inversion H2; subst; eauto. inversion H6; subst.
eapply app_preserv; eauto.

inversion H1.

inversion H0.

inversion H1; subst. inversion H0; subst. eauto.

inversion H0; subst. eauto.

inversion H1; subst; inversion H0; subst; eauto.

inversion H1; subst; inversion H2; subst; eauto.

inversion H2; subst; inversion H3; subst; eauto.
Qed.

Definition stuck (t: tm) : Prop :=
(normal_form step) t /\ ~ value t.

Notation "t '==>*' t'" := (multi step t t') (at level 40).


Corollary soundness : 
    forall t t' T,
        empty |= t \in T ->
        t ==>* t' ->
        ~(stuck t').

    intros t t' T h0 h. generalize dependent T.
    unfold stuck. unfold normal_form.
    induction h; intros; auto; intro.
    destruct H.
    Print progress.
    destruct (progress _ _ h0); eauto.
    Print preservation.
    pose (preservation _ _ _ h0 H). 
    destruct ((IHh _ h1) H0).
Qed.

Theorem types_unique:
    forall x T G U,
    U |= x \in T ->
    U |= x \in G ->
    T = G.
    intro x; induction x; eauto; intros; (try (inversion H; inversion H0; subst; eauto)).
    inversion H; inversion H0; subst. rewrite H7 in H3. inversion H3; subst. auto.

    inversion H; inversion H0; subst; eauto.
    pose (IHx1 _ _ _ H4 H10). inversion e; subst; auto.

    inversion H; inversion H0; subst. rewrite (IHx _ _ _ H6 H12); eauto.

Qed.
    
End STLCARITH.





















        