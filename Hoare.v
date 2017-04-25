Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import SfLib.
Require Import Imp.
Require Import Maps.

Definition Assertion := state -> Prop.

Definition assert_implies (P Q:Assertion) : Prop :=
  forall st, P st -> Q st.

Notation "P ->> Q" :=
  (assert_implies P Q)
    (at level 80):hoare_spec_scope.
Open Scope hoare_spec_scope.

Notation "P <<->> Q" :=
  ((P ->> Q) /\ (Q ->> P)) (at level 80) : hoare_spec_scope.

Definition hoare_triple (P : Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st',
    c / st \\ st' ->
    P st ->
    Q st'.

Notation "{{ P }} c {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level) : hoare_spec_scope.

Theorem hoare_post_true :
  forall (P Q : Assertion) c,
    (forall st, Q st) ->
    {{P}} c {{Q}}.
  unfold hoare_triple. auto.
Qed.


Theorem hoare_pre_false :
  forall (P Q:Assertion) c,
    (forall st, ~ (P st)) ->
    {{ P}} c{{Q}}.
  unfold hoare_triple.
  intros. elim (H st H1).
Qed.

Definition assn_sub X a P : Assertion :=
  fun (st : state) =>
    P (t_update st X (aeval st a)).

Notation "P [ X |-> a ]" := (assn_sub X a P) (at level 10).

Theorem hoare_asgn :
  forall Q X a,
    {{ Q [ X |-> a]}} (X ::= a) {{Q}}.
  unfold hoare_triple. unfold assn_sub.
  intros. inversion H. subst n; auto.
Qed.

Example assn_sub_example:
  {{(fun st => st X = 3) [X |-> ANum 3]}}
    (X ::= (ANum 3))
    {{ fun st => st X = 3}}.
apply hoare_asgn.
Qed.


Example hoare_asgn_wrong:
  forall X a,
    {{fun x =>True}} (X ::= a) {{fun x=> aeval x (AId X) = aeval x a}}.

assert (forall X a,
          {{ (fun x=> aeval x (AId X) = aeval x a) [X |-> a] }}
            (X ::= a) {{fun x=> aeval x (AId X) = aeval x a}}).
intros; apply hoare_asgn.
unfold assn_sub in H. simpl in H. unfold t_update in H. intros.
destruct (eq_id_dec X X) eqn: h1.
pose (H X a). rewrite h1 in h. destruct a eqn:ha; unfold hoare_triple in h; unfold hoare_triple; simpl in h.
simpl in h. simpl. unfold hoare_triple. unfold hoare_triple in h. intros. apply (h st st' H0 eq_refl).
simpl in h. destruct (eq_id_dec X i). intros. pose (h st st' H0 eq_refl).
simpl. auto.
simpl. intros. apply (h st st' H0 eq_refl).
Abort.


Theorem hoare_asgn_fwd:
  (forall {X Y:Type} {f g: X -> Y},
     (forall (x:X), f x = g x) -> f = g) ->
     forall m a P X,
       {{fun st => P st /\ st X = m}}
         (X ::= a)
         {{fun st => P (t_update st X m)
                     /\ st X = aeval (t_update st X m) a}}.
  intros. unfold hoare_triple.
  intros. inversion H0.
  assert (st = t_update (t_update st X n) X m).
  apply H. unfold t_update. intro; case (eq_id_dec X x0); simpl; auto.
  intros; subst x0; auto. inversion H1; auto.
  rewrite <- H7. rewrite H6. unfold t_update. rewrite eq_id_dec_id.
  tauto.
Qed.


Theorem hoare_asgn_fwd_exists:
  (forall {X Y: Type} {f g:X -> Y},
     (forall x:X, f x = g x) -> f = g) ->
  forall a P,
    {{fun st => P st}}
      X ::= a
      {{fun st => exists m, P(t_update st X m) /\
                            st X = aeval (t_update st X m) a }}.

  unfold hoare_triple. intros.
  pose (eq_refl (st X)).
  pose (conj H1 e).
  pose (hoare_asgn_fwd H (st X) a P).
  unfold hoare_triple in h.
  pose (h X st st' H0 a0).
  exists (st X). auto.
Qed.

Theorem hoare_consequence_pre :
  forall (P P' Q : Assertion) c,
    {{P'}} c {{Q}} ->
    P ->> P' ->
    {{P}} c {{Q}}.
  unfold hoare_triple.
  unfold assert_implies.
  intros. apply (H st st'); auto.
Qed.

Theorem hoare_consequence_post :
  forall (P Q Q' : Assertion) c,
    {{P}} c {{Q'}} ->
    Q' ->> Q ->
    {{P}} c {{Q}}.

  unfold hoare_triple; unfold assert_implies.
  intros. apply (H0 st'). apply (H st st'); auto.
Qed.

Example hoare_asgn_example1:
  {{fun st => True}} (X::=(ANum 1)) {{fun st => st X = 1}}.
apply hoare_consequence_pre with (P' := (fun st => st X = 1)[ X |-> ANum 1]).
apply hoare_asgn.
unfold assn_sub. unfold t_update. intro. intro. rewrite eq_id_dec_id. simpl. auto.
Qed.


Theorem hoare_consequence:
  forall (P P' Q Q' :Assertion) c,
    {{P'}} c {{Q'}} ->
    P ->> P' ->
    Q' ->> Q ->
    {{P}} c {{Q}}.
  unfold hoare_triple; unfold assert_implies.
  intros. apply H1. apply (H st st'); auto.
Qed.

Theorem hoare_skip :
  forall P,
    {{P}} SKIP {{P}}.
  unfold hoare_triple.
  intros. inversion H. subst st'. auto.
Qed.

Theorem hoare_seq:
  forall P Q R c1 c2,
    {{P}} c1 {{Q}} ->
    {{Q}} c2 {{R}} ->
    {{P}} c1 ;; c2 {{R}}.

  unfold hoare_triple; intros.
  inversion H1. subst st''. subst st0.
  apply (H0 st'0 st'); auto. apply(H st st'0);auto.
Qed.

Example hoare_asgn_example3:
  forall a n,
    {{fun st => aeval st a = n}}
      (X ::= a ;; SKIP)
      {{fun st => st X = n}}.
intros. eapply hoare_seq.
eapply (hoare_consequence_pre).
apply (hoare_asgn (fun st:state => st X = n) _ _).
unfold assert_implies. unfold assn_sub. unfold t_update. intro. rewrite eq_id_dec_id. auto.
apply hoare_skip.
Qed.



Definition swap_program : com :=
  Z::= AId X;;
   X::= AId Y;;
   Y::= AId Z.

Theorem swap_exercise:
  {{fun st => st X <= st Y}}
    swap_program
    {{ fun st => st Y <= st X}}.
  unfold swap_program.
  eapply hoare_seq.
  eapply hoare_consequence_pre.
  apply (hoare_asgn (fun st:state => st Z <= st Y) Z _).
  unfold assn_sub. unfold t_update. simpl. unfold assert_implies. intros; rewrite eq_id_dec_id.
  case (eq_id_dec Z Y). intro; discriminate. auto.
  eapply hoare_seq. eapply hoare_consequence_pre. apply (hoare_asgn (fun st:state => st Z <= st X) X _).
  unfold assn_sub; unfold assert_implies; unfold t_update. simpl. intros; rewrite eq_id_dec_id.
  case (eq_id_dec X Z); intros; try discriminate; auto.
  eapply hoare_consequence_pre.
  apply (hoare_asgn (fun st:state => st Y <= st X) Y (AId Z)).
  unfold assn_sub; unfold t_update; simpl; unfold assert_implies. intros; rewrite eq_id_dec_id.
  case (eq_id_dec Y X); intros; try discriminate; auto.
Qed.

Definition bassn b:Assertion :=
  fun st => (beval st b = true).

Lemma bexp_eval_true:
  forall b st,
    beval st b = true -> (bassn b) st.
  unfold bassn. auto.
Qed.

Lemma bexp_eval_false :
  forall b st,
    beval st b = false -> ~ ((bassn b) st).

  unfold bassn. unfold not. intros. rewrite H0 in H; discriminate.
Qed.

Theorem hoare_if :
  forall P Q b c1 c2,
    {{fun st => P st /\ bassn b st}} c1 {{Q}} ->
    {{fun st => P st /\ ~(bassn b st)}} c2 {{Q}} ->
    {{P}} (IFB b THEN c1 ELSE c2 FI) {{Q}}.
  unfold hoare_triple. intros. inversion H1. subst st'0. subst st0. subst c0. subst c3.
  pose (H st st' H9). unfold bassn in q. apply q; auto.
  subst st'0; subst st0; subst c3; subst c0.
  pose (H0 st st' H9). unfold bassn in q. rewrite H8 in q.
  apply q; auto.
Qed.


Theorem if_minus_plus:
  {{fun st => True}}
    IFB (BLe (AId X) (AId Y))
    THEN (Z::= AMinus (AId Y) (AId X))
    ELSE (Y::= APlus (AId X) (AId Z))
    FI
    {{fun st => st Y = st X + st Z}}.

  apply hoare_if. unfold bassn. eapply hoare_consequence_pre.
  apply (hoare_asgn (fun st => st Y = st X + st Z) _ _).
  unfold assert_implies. unfold assn_sub. simpl. unfold t_update. intro. rewrite eq_id_dec_id.
  case (eq_id_dec Z X); case (eq_id_dec Z Y); intros; try discriminate; auto.
  unfold leb_bydec in H. inversion H. SearchRewrite ( _ - _). generalize H1; case (le_dec (st X) (st Y)); intros; try discriminate; auto. omega.
  unfold bassn. eapply hoare_consequence_pre. apply (hoare_asgn _ _ _).
  unfold assert_implies. unfold assn_sub. unfold t_update. intro. rewrite eq_id_dec_id.
  case (eq_id_dec Y Z); case (eq_id_dec Y X); intros; try discriminate; auto.
Qed.

Module IF1.
  Inductive com: Type :=
| CSkip : com
| CAss : id -> aexp -> com
| CSeq : com -> com -> com
| CIf : bexp -> com -> com -> com
| CWhile : bexp -> com -> com
| CIf1 : bexp -> com -> com.

  
  Notation "'SKIP'" :=
    CSkip.

  Notation "c1 ;; c2" :=
    (CSeq c1 c2) (at level 80, right associativity).

  Notation "X '::=' a" :=
    (CAss X a) (at level 60).

  Notation "'WHILE' b 'DO' c 'END'" :=
    (CWhile b c) (at level 80, right associativity).

  Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
    (CIf e1 e2 e3) (at level 80, right associativity).

  

  Notation "'IF11' b 'THEN' c 'FI'" :=
    (CIf1 b c) (at level 80, right associativity).

  Reserved Notation "c1 '/' st '\\' st'" (at level 40, st at level 39).
  
  Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st:state, SKIP / st \\ st
  | E_Ass : forall (st:state) (a1:aexp) (n:nat) (X:id),
              aeval st a1 = n -> (X ::= a1) / st \\ (t_update st X n)
  | E_Seq : forall (c1 c2: com) (st st' st'' : state),
              c1 / st \\ st' -> c2 / st' \\ st'' -> (c1 ;; c2) / st \\ st''
  | E_IfTrue : forall (st st' : state) (b1 : bexp) (c1 c2: com),
                 beval st b1 = false ->
                 c2 / st \\ st' -> (IFB b1 THEN c1 ELSE c2 FI) / st \\ st'
  | E_WhileEnd : forall (b1: bexp) (st:state) (c1:com),
                   beval st b1 = false -> (WHILE b1 DO c1 END) / st \\ st
  | E_WhileLoop: forall (st st' st'' : state) (b1: bexp) (c1:com),
                   beval st b1 = true ->
                   c1 / st \\ st' ->
                   (WHILE b1 DO c1 END) / st' \\ st'' ->
                   (WHILE b1 DO c1 END) / st \\ st''
  | E_If1True : forall st st' b c,
                  beval st b = true ->
                  c / st \\ st' ->
                  (IF11 b THEN c FI) / st \\ st'
  | E_If1False : forall st b c,
                   beval st b = false ->
                   (IF11 b THEN c FI) / st \\ st
  where "c1 '/' st '\\' st'" := (ceval c1 st st').

  
  
  Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
    forall st st',
      c / st \\ st' ->
      P st ->
      Q st'.


  Notation "{{ P }} c {{ Q }}" := (hoare_triple P c Q)
                                (at level 90, c at next level)
                                  : hoare_spec_scope.

  
  
  Lemma hoare_if1_good :
    {{fun st => st X + st Y = st Z}}
      IF11 BNot (BEq (AId Y) (ANum 0)) THEN
      X ::= APlus (AId X) (AId Y)
      FI
      {{fun st => st X = st Z}}.
Proof.
    unfold hoare_triple. intros.
    inversion H. subst st0; subst st'0. inversion H6. unfold t_update. rewrite eq_id_dec_id.
    case (eq_id_dec Imp.X Z); auto. intros. simpl in H9. rewrite <- H9. auto.
    inversion H5. unfold beq_nat_bydec in H7. generalize H7. subst st'.
    case (eq_nat_dec (st Y) 0). intros; omega. simpl; intros; discriminate.
Qed.

  End IF1.








Lemma hoare_while :
    forall P b c,
      {{fun st => P st /\ bassn b st}} c {{P }} ->
      {{P}} WHILE b DO c END {{fun st => P st /\ ~(bassn b st)}}.

    unfold hoare_triple. unfold bassn.
    intros. generalize dependent H1.
    remember (WHILE b DO c END) as h. generalize dependent Heqh.
    elim H0; try (intros; discriminate).
    intros. inversion Heqh. subst c0. subst b0. pose (H st0 st'0 H2 (conj H6 H1)). auto.
    intros. inversion Heqh. subst b0; rewrite H1. auto.
Qed.



    
  Theorem always_loop_hoare :
    forall P Q,
      {{P}} WHILE BTrue DO SKIP END {{Q}}.

    unfold hoare_triple.
    intros. remember (WHILE BTrue DO SKIP END) as c.
    generalize dependent Heqc.
    elim H; try (intros; discriminate).
    intros. auto.
    intros. inversion Heqc. subst b. simpl H1; discriminate.
  Qed.

  Module REPEATEXERCISE.

    Inductive com : Type :=
  |  CSkip : com
  |  CAsgn : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CRepeat : com -> bexp -> com.

    Notation "'SKIP'" :=
      CSkip.

    Notation "c1 ;; c2" :=
      (CSeq c1 c2) (at level 80, right associativity).

    Notation " X '::=' a" :=
      (CAsgn X a) (at level 60).

    Notation "'WHILE' b 'DO' c 'END'" :=
      (CWhile b c) (at level 80, right associativity).

    Notation "'IFB' b 'THEN' c1 'ELSE' c2 'FI'" :=
      (CIf b c1 c2) (at level 80, right associativity).

    Notation "'REPEAT' e1 'UNTIL' b2 'END'" :=
      (CRepeat e1 b2) (at level 80, right associativity).

    Inductive ceval : state -> com -> state -> Prop :=
    | E_Skip : forall st,
                 ceval st SKIP st
    | E_Ass : forall st a1 n X,
                aeval st a1 = n ->
                ceval st (X ::= a1) (t_update st X n)
    | E_Seq : forall c1 c2 st st' st'',
                ceval st c1 st' ->
                ceval st' c2 st'' ->
                ceval st (c1 ;; c2) st''
    | E_IfTrue : forall st st' b1 (c1 c2:com),
                   beval st b1 = true ->
                   ceval st c1 st' ->
                   ceval st (IFB b1 THEN c1 ELSE c2 FI) st'
    | E_IfFalse : forall st st' b1 (c1 c2:com),
                    beval st b1 = false ->
                    ceval st c2 st' ->
                    ceval st (IFB b1 THEN c1 ELSE c2 FI) st'
    | E_WhileEnd : forall b1 st st' c1 c2,
                     beval st b1 = false ->
                     ceval st c2 st' ->
                     ceval st (IFB b1 THEN c1 ELSE c2 FI) st'
    | E_WhileLoop : forall b1 st st'' st' c1,
                      beval st b1 = true ->
                      ceval st c1 st' ->
                      ceval st' (WHILE b1 DO c1 END) st'' ->
                      ceval st (WHILE b1 DO c1 END) st''
    | E_RepeatEnd : forall st st'' c b1 ,
                   ceval st c st'' ->
                   beval st'' b1 = true ->
                   ceval st (REPEAT c UNTIL b1 END) st''
    | E_RepeatR : forall st st' st'' c b,
                    ceval st c st' ->
                    beval st' b = false ->
                    ceval st' (REPEAT c UNTIL b END) st'' ->
                    ceval st (REPEAT c UNTIL b END) st''.

    Notation "c1 '/' st '\\' st'" :=
      (ceval st c1 st')
        (at level 40, st at level 39).

    Definition hoare_triple (P :Assertion) (c : com) (Q: Assertion) : Prop :=
      forall st st',
        (c / st \\ st') -> P st -> P st'.

    
    Definition ex1_repeat :=
      REPEAT
        X::= ANum 1;;
        Y::= APlus (AId Y) (ANum 1)
        UNTIL (BEq (AId X) (ANum 1)) END.

    Theorem ex1_repeat_works :
      ex1_repeat / empty_state
                 \\ t_update (t_update empty_state X 1) Y 1.
      unfold ex1_repeat. apply E_RepeatEnd.
      apply (E_Seq _ _ empty_state (t_update empty_state X (aeval empty_state (ANum 1))) _).
      apply E_Ass. auto.
      simpl. apply E_Ass. simpl. unfold t_update. case (eq_id_dec X Y); try (intros; discriminate).
      simpl. auto.
      simpl. unfold t_update. rewrite eq_id_dec_id. case (eq_id_dec Y X); auto.
    Qed.

    Notation "{{ P }} c {{ Q }}" :=
      (hoare_triple P c Q) (at level 90, c at next level).
    
    Theorem hoare_repeat:
      forall P c b,
        {{P}} c {{P}} ->
        {{P}} REPEAT c UNTIL b END {{ fun st => P st /\ (bassn b st)}}.

      unfold hoare_triple.
      intros. remember (REPEAT c UNTIL b END) as d.
      generalize dependent H1. generalize dependent Heqd.
      elim H0; try (intros; discriminate).
      intros. inversion Heqd; subst c0; subst b1. apply (H st0 st'' H1 H4).
      intros. inversion Heqd; subst c0; subst b0. pose (H st0 st'0 H1 H6).
      auto.
    Qed.

    End REPEATEXERCISE.


  Module HIMP.
    Inductive com : Type :=
  | CSkip : com
  | CAsgn : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CHavoc : id -> com.

    Notation "'SKIP'" :=
      CSkip.

    Notation "X '::=' a" :=
      (CAsgn X a) (at level 60).

    Notation "c1 ;; c2" :=
      (CSeq c1 c2) (at level 80, right associativity).

    Notation "'WHILE' b 'DO' c 'END'" :=
      (CWhile b c) (at level 80, right associativity).

    Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
      (CIf e1 e2 e3) (at level 80, right associativity).

    Notation "'HAVOC' X" := (CHavoc X) (at level 60).

    Reserved Notation "c1 '/' st '\\' st'" (at level 40, st at level 39).
    
    Inductive ceval : com -> state -> state -> Prop :=
    | E_Skip : forall st, SKIP / st \\ st
    | E_Ass : forall st (a1: aexp) (n:nat) X,
                aeval st a1 = n -> (X::= a1) / st \\ t_update st X n
    | E_Seq : forall c1 c2 st st' st'',
                c1 / st \\ st' -> c2 / st' \\ st'' -> (c1;;c2) / st \\ st''
    | E_IfTrue :
        forall (st st': state) (b1:bexp) (c1 c2:com),
          beval st b1 = true ->
          c1 / st \\ st' ->
          (IFB b1 THEN c1 ELSE c2 FI) / st \\ st'
    | E_IfFalse:
        forall (st st': state) (b1:bexp) (c1 c2:com),
          beval st b1 = true ->
          c2 / st \\ st' ->
          (IFB b1 THEN c1 ELSE c2 FI) / st \\ st'
    | E_WhileEnd :
        forall (b1: bexp) (st:state) (c1:com),
          beval st b1 = false ->
          (WHILE b1 DO c1 END) / st \\ st
    | E_WhileLoop :
        forall (st st' st'' : state) (b1:bexp) (c1:com),
          beval st b1 = true ->
          c1 / st \\ st' ->
          (WHILE b1 DO c1 END) / st' \\ st'' ->
          (WHILE b1 DO c1 END) / st \\ st''
    | E_Havoc :
        forall (st:state) (X:id) (n:nat),
          (HAVOC X) / st \\ t_update st X n
    where "c1 '/' st '\\' st'" := (ceval c1 st st').

    
    Definition hoare_triple (P :Assertion) (c : com) (Q: Assertion) : Prop :=
      forall st st',
        (c / st \\ st') -> P st -> P st'.
    Notation "{{ P }} c {{ Q }}" :=
      (hoare_triple P c Q) (at level 90, c at next level).

    Definition havoc_pre (X:id) (Q:Assertion) : Assertion :=
      fun st => forall (n:nat), Q (t_update st X n).

Require Import Coq.Logic.FunctionalExtensionality.
    
    Theorem hoare_havoc :
      forall (Q:Assertion) (X:id),
        {{ havoc_pre X Q}} HAVOC X {{Q}}.

      unfold hoare_triple. unfold havoc_pre.
      intros. inversion H. subst X0; subst st0.
      assert (t_update (t_update st X n0) X n = t_update st X n).
      apply functional_extensionality. unfold t_update.
      intro. case (eq_id_dec X x); auto.
      rewrite H1. apply H0.
    Qed.
End HIMP.

    
    