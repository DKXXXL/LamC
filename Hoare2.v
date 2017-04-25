Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import SfLib.
Require Import Maps.
Require Import Imp.
Require Import Hoare.

Definition reduce_to_zero' : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
        X ::= AMinus (AId X) (ANum 1)
        END.
Theorem reduce_to_zero_correct' :
  {{fun st => True}}
    reduce_to_zero'
    {{ fun st => st X = 0}}.
  unfold reduce_to_zero'.
  SearchPattern ({{ _ }} _ {{ _ }}).
  eapply hoare_consequence_post.
  apply hoare_while. apply hoare_post_true; auto.
  unfold bassn. simpl. unfold beq_nat_bydec. intro. case (eq_nat_dec (st X) 0); intros; tauto.
Qed.

Fixpoint parity x :=
  match x with
    | 0 => 0
    | 1 => 1
    | S (S x') => parity x'
  end.


Lemma parity_ge_2 :
  forall x,
    2 <= x ->
    parity (x - 2) = parity x.

  intros.
  cut (parity (x - 2) = parity x /\ parity (S x - 2) = parity (S x)); try tauto.
  elim H; try tauto.
  intros. split. destruct m. try tauto. try tauto.
  simpl. assert (m - 0 = m); try omega. rewrite H2. auto.
Restart.

intro. elim x; try omega.
intro. intro. elim n. try omega.
intros. simpl. assert (n0 - 0 = n0); try omega. rewrite H2; auto.
Qed.


Lemma parity_lt_2:
  forall x,
    ~ (2 <= x) ->
    parity x = x.
  intro. destruct x; try auto.
  destruct x; try auto.
  destruct x; try omega.
Qed.

Theorem parity_correct :
  forall m,
    {{ fun st => st X = m}}
      WHILE BLe (ANum 2) (AId X) DO
      X ::= AMinus (AId X) (ANum 2)
      END
      {{ fun st => st X = parity m}}.

  SearchPattern ({{ _ }} _ {{ _ }}).
  intro. eapply hoare_consequence_pre.
  eapply hoare_consequence_post.
  SearchPattern ({{_}}_{{_}}).
  apply (hoare_while (fun st => parity (st X) = parity m)).
  eapply hoare_consequence_pre.
  apply (hoare_asgn). unfold assn_sub. simpl. intro. intros. unfold t_update. rewrite eq_id_dec_id.
  inversion H. unfold bassn in H1. simpl in H1. unfold leb_bydec in H1. generalize dependent H1.
  case (le_dec 2 (st X)). intros. cut (parity (st X) = parity (st X - 2)). intros. rewrite <- H2. auto. symmetry. apply parity_ge_2. auto. intros; discriminate.
  unfold bassn. simpl. unfold leb_bydec. intro. case (le_dec 2 (st X)). intro; tauto.
  intros. symmetry. inversion H. rewrite <- H0. apply parity_lt_2. auto.
  intro. intros; subst m; auto.
Qed.



Definition is_wp P c Q :=
  {{P}} c {{Q}} /\
  forall P', {{P'}} c {{Q}} -> (P' ->> P).

Theorem is_wp_example :
  is_wp (fun st => st Y <= 4)
        (X ::= APlus (AId Y) (ANum 1)) (fun st => st X <= 5).

  unfold is_wp.
  split. eapply hoare_consequence_pre.
  apply hoare_asgn. unfold assn_sub. unfold t_update.
  intro. rewrite eq_id_dec_id. simpl. omega.
  unfold assert_implies.
  unfold hoare_triple. intros.
  pose (t_update st X (st Y + 1)).
  Print E_Ass.
  pose (E_Ass st (APlus (AId Y) (ANum 1)) (st Y + 1) X eq_refl).
  pose (H st t c H0).
  unfold t in l.
  unfold t_update in l. rewrite eq_id_dec_id in l. omega.
Qed.

Theorem hoare_asgn_weakest :
  forall Q X a,
    is_wp (Q [ X |-> a]) (X ::= a) Q.

  unfold is_wp. split. apply hoare_asgn.
  unfold hoare_triple. unfold assert_implies. unfold assn_sub.
  intros.
  Print E_Ass.
  pose (E_Ass st a (aeval st a) X eq_refl).
  apply (H st _ c H0).
Qed.


Inductive dcom : Type :=
| DCSkip : Assertion -> dcom
| DCSeq : dcom -> dcom -> dcom
| DCAsgn : id -> aexp -> Assertion -> dcom
| DCIf : bexp -> Assertion -> dcom -> Assertion -> dcom -> Assertion -> dcom
| DCWhile : bexp -> Assertion -> dcom -> Assertion -> dcom
| DCPre : Assertion -> dcom -> dcom
| DCPost : dcom -> Assertion -> dcom.


Notation "'Skip' {{ P }}" := (DCSkip P)
                               (at level 10) : dcom_scope.




Notation "l '::=' a {{ P }}" :=
  (DCAsgn l a P)
    (at level 60, a at next level) : dcom_scope.

Notation "'WHILE' b 'DO' {{ Pbody }} d 'END' {{ Ppost }}"
  := (DCWhile b Pbody d Ppost)
       (at level 80, right associativity) : dcom_scope.

Notation "'IFB' b 'THEN' {{ P }} d 'ELSE' {{ P' }} d' 'FI' {{ Q }}"
  := (DCIf b P d P' d' Q)
       (at level 80, right associativity) : dcom_scope.

Notation "'->>' {{ P }} d"
  := (DCPre P d)
       (at level 90, right associativity) : dcom_scope.




Notation "{{ P }} d"
  := (DCPre P d)
       (at level 90) : dcom_scope.


Notation "d '->>' {{ P }}"
  := (DCPost d P)
       (at level 80, right associativity) : dcom_scope.

Notation "d ;; d'"
  := (DCSeq d d')
       (at level 80, right associativity) : dcom_scope.


Delimit Scope dcom_scope with dcom.

Example dec_while : dcom :=
  ({{fun st => True}}
     WHILE (BNot (BEq (AId X) (ANum 0)))
     DO
     {{ fun st => True /\ st X <> 0}}
     X ::= (AMinus (AId X) (ANum 1))
     {{ fun st => True}}
     END
     {{fun st => True /\ st X = 0}} ->>
     {{fun st => st X = 0}}
  )%dcom.


Fixpoint extract (d:dcom) : com :=
  match d with
    | DCSkip _ => SKIP
    | DCSeq d1 d2 => (extract d1) ;; (extract d2)
    | DCAsgn X a _ => X ::= a
    | DCIf b _ d1 _ d2 _ => IFB b THEN extract d1 ELSE extract d2 FI
    | DCWhile b _ d _ => WHILE b DO extract d END
    | DCPre _ d => extract d
    | DCPost d _ => extract d
  end.

Fixpoint post (d:dcom) : Assertion :=
  match d with
    | DCSkip P => P
    | DCSeq d1 d2 => post d2
    | DCAsgn X a Q => Q
    | DCIf _ _ d1 _ d2 Q => Q
    | DCWhile b Pbody c Ppost => Ppost
    | DCPre _ d => post d
    | DCPost c Q => Q
  end.

Fixpoint pre (d:dcom) : Assertion :=
  match d with
    | DCSkip P => (fun st => True)
    | DCSeq c1 c2 => pre c1
    | DCAsgn X a Q => fun st => True
    | DCIf _ _ t _ e _ => fun st => True
    | DCWhile b Pbody c Ppost => fun st => True
    | DCPre P c => P
    | DCPost c Q => pre c
  end.

Definition dec_correct (d:dcom) :=
  {{pre d}} (extract d) {{post d}}.

Fixpoint verification_conditions (P:Assertion) (d:dcom) : Prop :=
  match d with
    | DCSkip Q =>
      P ->> Q
    | DCSeq d1 d2 =>
      verification_conditions P d1 /\
      verification_conditions (post d1) d2
    | DCAsgn X a Q =>
      P ->> Q [ X |-> a]
    | DCIf b P1 d1 P2 d2 Q =>
      (( fun st => P st /\ bassn b st ) ->> P1)
      /\ ((fun st => P st /\ ~(bassn b st)) ->> P2)
      /\ (Q <<->> post d1)
      /\ (Q <<->> post d2)
      /\ verification_conditions P1 d1
      /\ verification_conditions P2 d2
    | DCWhile b Pbody d Ppost =>
      (P ->> post d)
      /\ (Pbody <<->> (fun st => post d st /\ bassn b st))
      /\ (Ppost <<->> (fun st => post d st /\ ~(bassn b st)))
      /\ (verification_conditions Pbody d)
    | DCPre P' d =>
      (P ->> P') /\ verification_conditions P' d
    | DCPost d Q =>
      verification_conditions P d /\ (post d ->> Q)
  end.




Lemma assert_implies_trans:
  forall A B C,
    (A ->> B) -> (B ->> C) -> (A ->> C).
  unfold assert_implies. auto.
Qed.


Lemma vc_pre:
  forall P Q d,
    verification_conditions P d ->
    Q ->> P ->
    verification_conditions Q d.
  intros P Q d.
  elim d; simpl.
  unfold assert_implies. auto.
  intros. tauto.
  intros i a a0. unfold assert_implies. auto.
  unfold assert_implies.
  intros. inversion H1. inversion H4. inversion H6. inversion H8.
  clear H1 H4 H6 H8.
  inversion H7; inversion H9; inversion H10. clear H7 H9 H10.
  split; intros. inversion H7. apply (H3 _ (conj (H2 _ H9) H10)).
  split; intros. inversion H7. apply (H5 _ (conj (H2 _ H9) H10)).
  split; intros. try tauto. try tauto.
  split; intros. inversion H0. eapply assert_implies_trans. apply H1. apply H2.
  tauto. split. inversion H0. eapply assert_implies_trans. apply H1. auto.
  tauto.
  split; intros. tauto. tauto.
Qed.

  
Theorem verification_correct :
  forall d P,
    verification_conditions P d -> {{P}} (extract d) {{post d}}.
  intro. elim d; simpl.
  intros; eapply hoare_consequence_pre. apply hoare_skip. auto.
  intros. inversion H1. pose (H _ H2). pose (H0 _ H3).
  eapply hoare_seq. apply h. auto.
  intros. eapply hoare_consequence_pre. apply hoare_asgn. auto.
  intros. inversion H1; inversion H3; inversion H5; inversion H7.
  clear H1 H3 H5 H7.
  eapply hoare_if. eapply hoare_consequence_pre. inversion H9; clear H9.
  inversion H6; clear H6. inversion H8; clear H8.
  eapply hoare_consequence_post. apply (H a H1). auto. auto.
  eapply hoare_consequence_pre. eapply hoare_consequence_post. inversion H9; clear H9.
  apply (H0 a0 H3). inversion H8; auto. auto.
  intros. inversion H0; inversion H2. inversion H4. clear H0 H2 H4.
  eapply hoare_consequence_pre. eapply hoare_consequence_post. eapply hoare_while. eapply hoare_consequence_pre. apply (H a H6). tauto. tauto. auto.
  intros.  inversion H0. apply (H P). eapply vc_pre. apply H2. auto.
  intros. inversion H0. eapply hoare_consequence_post. apply (H P). auto. auto.
Qed.


  Print beq_nat_true_iff.
  Lemma beq_nat_bydec_true_iff:
    forall x y, beq_nat_bydec x y = true <-> x = y.
    unfold beq_nat_bydec. intros x y.
    case (eq_nat_dec x y); split; intros; try auto; try discriminate.
  Qed.

  Lemma beq_nat_bydec_false_iff:
    forall x y, beq_nat_bydec x y = false <-> x <> y.
    unfold beq_nat_bydec. intros x y.
    case (eq_nat_dec x y); split; intros; try discriminate; try auto. elim (H e).
  Qed.

Print leb_iff.

Lemma leb_bydec_iff:
  forall m n, leb_bydec m n = true <-> m <= n.
  unfold leb_bydec. intros m n. case (le_dec m n); try (intros;discriminate); try auto.
  tauto.
  split; intros; try discriminate.
  elim (n0 H).
Qed.
Print leb_iff_conv.
Lemma leb_bydec_iff_conv :
  forall m n, leb_bydec m n = false <-> m > n.
  unfold leb_bydec. intros m n. case (le_dec m n); split; try (intros; discriminate); try omega.
  auto.
Qed.




  Tactic Notation "verify" :=
  apply verification_correct;
  repeat split;
  simpl; unfold assert_implies;
  unfold bassn in *; unfold beval in *; unfold aeval in *;
  unfold assn_sub; intros;
  repeat rewrite t_update_eq;
  repeat (rewrite t_update_neq; [|( intro X; inversion X)]);
  simpl in *;
  repeat match goal with [ H : _ /\ _ |- _] => destruct H end;
  repeat rewrite not_true_iff_false in *;
  repeat rewrite not_false_iff_true in *;
  repeat rewrite negb_true_iff in *;
  repeat rewrite negb_false_iff in *;
  repeat rewrite beq_nat_true_iff in *;
  repeat rewrite beq_nat_false_iff in *;
  repeat rewrite beq_nat_bydec_true_iff in *;
  repeat rewrite beq_nat_bydec_false_iff in *;
  repeat rewrite leb_iff in *;
  repeat rewrite leb_bydec_iff in *;
  repeat rewrite leb_bydec_iff_conv in *;
  repeat rewrite leb_iff_conv in *;
  try subst;
  repeat
    match goal with
        [st : state |- _] =>
        match goal with
            [ H:st _ = _ |- _] => rewrite -> H in *; clear H
          | [H: _ = st _ |- _] => rewrite <- H in * ; clear H
        end
    end;
  try eauto; try omega.


  Theorem dec_while_correct:
    dec_correct dec_while.

    verify.
  Qed.


  Example subtract_slowly_dec (m p:nat) : dcom :=
    ( {{ fun st => st X = m /\ st Z = p }}
        ->> {{ fun st => st Z - st X = p - m }}
        WHILE BNot (BEq (AId X) (ANum 0))
        DO {{ fun st => st Z - st X = p - m /\ st X <> 0}} ->>
        {{ fun st => (st Z - 1) - (st X - 1) = p - m }}
        Z::= AMinus (AId Z) (ANum 1)
        {{ fun st => st Z - (st X - 1) = p - m}} ;;
        X ::= AMinus (AId X) (ANum 1)
        {{fun st => st Z - st X = p - m }}
        END
        {{ fun st => st Z - st X = p - m /\ st X = 0 }} ->>
        {{fun st => st Z = p - m}})%dcom.

  Theorem subtract_slowly_dec_correct :
    forall m p,
      dec_correct (subtract_slowly_dec m p).

    intros m p. verify.
    Qed.


  Example slow_assignment_dec (m:nat) : dcom :=
    ({{ fun st => st X = m }}
       Y ::= (ANum 0) 
       {{ fun st => st Y = 0 /\ st X = m}} ->>
       {{ fun st => st Y + st X = m }};;
       WHILE (BNot (BEq (AId X) (ANum 0)))
       DO {{ fun st => st Y + st X = m /\ st X <> 0 }} ->>
       {{ fun st => (st Y + 1) + (st X - 1) = m /\ st X <> 0}}
       X ::= AMinus (AId X) (ANum 1)
       {{ fun st => (st Y + 1) + st X = m}};;
       Y ::= APlus (AId Y) (ANum 1)
       {{ fun st => st Y + st X = m}}
       END
       {{fun st => st Y + st X = m /\ st X = 0}} ->>
       {{ fun st => st Y = m}})%dcom.
  Theorem slow_assignment_dec_correct :
    forall m, dec_correct (slow_assignment_dec m).

    intro.
    verify.                    
    Qed.


  Fixpoint real_fact (n:nat) : nat :=
    match n with
      | 0 => 1
      | S n' => n * (real_fact n')
    end.

  Require Import Arith.

  Locate divmod.
  Require Import Coq.Numbers.Natural.Peano.NPeano.

  
  
  Definition factorial_dec (n:nat) : dcom :=
    ({{ fun st => st X = n }}
       Y ::= ANum 1
       {{ fun st => st Y = 1 /\ st X = n}};; ->>
       {{ fun st => st Y * (real_fact (st X)) = (real_fact n)}} 
       WHILE (BNot (BEq (AId X) (ANum 0)))
       DO {{ fun st => st Y * (real_fact (st X)) = (real_fact n) 
                       /\  st X <> 0}} ->>
       {{ fun st => st Y * (st X) * (real_fact (st X - 1)) = (real_fact n)
                    /\ st X <> 0 }}
       Y ::= AMult (AId Y) (AId X)
       {{ fun st => st Y * (real_fact (st X - 1)) = (real_fact n) 
                    /\ st X <> 0}};;
       X ::= AMinus (AId X) (ANum 1)
       {{ fun st => st Y * (real_fact (st X)) = (real_fact n) }}
       END
       {{fun st => st Y * (real_fact (st X)) = (real_fact n) 
                   /\ st X = 0}} ->>
       {{fun st => st Y = (real_fact n)}})%dcom.

  
  Lemma factorial_is_not_zero:
    forall m,
      real_fact m > 0.
    intro. elim m; try (intros; simpl; auto; omega).
    intros. simpl. remember (n*real_fact n) as c. omega.
  Qed.

  Lemma bigger_iff_neq_0:
    forall m,
      m <> 0 <-> m > 0.

    intro; omega.
  Qed.

  
  Locate div_same.
  Theorem factorial_dec_correct :
    forall m,
      dec_correct (factorial_dec m).
    intro. verify.
    assert ( st X * (real_fact (st X - 1)) = real_fact (st X)).
    destruct (st X) eqn: h; try (auto;omega;discriminate).
    simpl. assert (n-0 = n); try omega. rewrite H1. omega.
    rewrite <- H. rewrite <- H1.
    remember (st Y) as a. remember (st X) as b. remember (real_fact (b -1)) as c.
    rewrite mult_assoc. auto. simpl in H; omega.
  Qed.

  Definition swap : com :=
    X ::= APlus (AId X) (AId Y) ;;
      Y ::= AMinus (AId X) (AId Y) ;;
      X ::= AMinus (AId X) (AId Y).
  Definition swap_dec m n : dcom :=
    ({{ fun st => st X = m /\ st Y = n}}
       ->> {{ fun st => (st X + st Y) - ((st X + st Y) - st Y) = n
                        /\ (st X + st Y) - st Y = m}}
       X ::= APlus (AId X) (AId Y)
       {{ fun st => st X - (st X - st Y) = n
                    /\ st X - st Y = m}};;
       Y ::= AMinus (AId X) (AId Y)
       {{ fun st => st X - st Y = n /\ st Y = m}} ;;
       X ::= AMinus (AId X) (AId Y)
       {{ fun st => st X = n
                    /\ st Y = m}})%dcom.

  Theorem swap_correct :
    forall m n,
      dec_correct (swap_dec m n).
    intros. verify.
  Qed.

  Definition if_minus_plus_com :=
    IFB (BLe (AId X) (AId Y))
        THEN (Z ::= AMinus (AId Y) (AId X))
        ELSE (Y ::= APlus (AId X) (AId Z))
        FI.

  Definition if_minus_plus_dec :dcom :=
    ({{fun st => True}}
       IFB (BLe (AId X) (AId Y))
       THEN {{fun st => st X <= st Y}}
       Z::= AMinus (AId Y) (AId X)
       {{fun st => st Z = st Y - st X
        /\ st X <= st Y}}
       ELSE {{fun st => st X > st Y}}
       Y ::= APlus (AId Z) (AId X)
       {{fun st => st Y = st Z + st X}}
       FI
       {{fun st => st Y = st Z + st X}})%dcom.

  Theorem if_minus_plus_dec_correct:
    dec_correct (if_minus_plus_dec).
    verify.
  Qed.

  Definition abs_value :=
    IFB (BLe (AId X) (AId Y))
        THEN Z ::= AMinus (AId Y) (AId X)
        ELSE Z ::= AMinus (AId X) (AId Y)
        FI.

  Definition abs_value_dec :dcom :=
    ({{fun st =>True}}
       IFB (BLe (AId X) (AId Y))
       THEN {{ fun st => st X <= st Y }}
       Z ::= AMinus (AId Y) (AId X)
       {{fun st => st Z + st X = st Y
                   /\ st X <= st Y}} ->>
       {{fun st => st Z + st X = st Y
                   \/ st Z + st Y = st X}}
       ELSE {{fun st => st X > st Y}}
       Z ::= AMinus (AId X) (AId Y)
       {{fun st => st Z + st Y = st X
                   /\ st X > st Y}} ->>
       {{fun st => st Z + st X = st Y
                   \/ st Z + st Y = st X}}
       FI
       {{fun st => st Z + st Y = st X
                   \/ st Z + st X = st Y}})%dcom.

  Theorem abs_value_dec_correct:
    dec_correct (abs_value_dec).
    verify; try tauto.
  Qed.

  Definition div_mod (a b :nat) : com :=
    X ::= ANum a;;
      Y ::= ANum 0;;
      WHILE (BNot (BLe (AId X) (ANum b)))
      DO
      X ::= AMinus (AId X) (ANum b);;
      Y ::= APlus (AId Y) (ANum 1)
      END.


  Definition div_mod_dec (a b:nat) : dcom :=
    ({{fun st => True}}
       X ::= (ANum a)
       {{ fun st => st X = a}};;
       Y ::= ANum 0
       {{ fun st => st Y = 0 /\ st X = a}};; ->>
       {{ fun st => (st Y) * b + st X = a}}
       WHILE ((BLe (ANum b) (AId X)))
       DO {{fun st => (st Y)* b + st X = a
                      /\ st X >= b}} ->>
       {{fun st => (st Y + 1) * b + (st X - b) = a
                   /\ st X >= b}}
       X ::= AMinus (AId X) (ANum b)
       {{fun st => (st Y + 1) * b + st X = a}};;
       Y ::= APlus (AId Y) (ANum 1)
       {{fun st => (st Y) * b + st X = a}}
       END
       {{fun st => (st Y) * b + st X = a
                   /\ st X < b}})%dcom.

  Theorem div_mod_dec_correct:
    forall m n,
      dec_correct (div_mod_dec m n).
    intros m n.
    verify. remember (st Y) as a. remember (st X) as b.
    SearchPattern ( (_+_)*_ = _).
    rewrite mult_plus_distr_r.
    simpl. SearchPattern (_+0=_).
    rewrite plus_0_r. rewrite <- plus_assoc.
    SearchPattern  (_ + (_ - _) = _).
    rewrite le_plus_minus_r. auto. auto.
  Qed.

  Definition find_parity : com :=
    WHILE (BLe (ANum 2) (AId X)) DO
          X ::= AMinus (AId X) (ANum 2)
          END.

  Definition find_parity_dec (m:nat) : dcom :=
    ({{fun st => st X = m}}
       ->> {{fun st => parity (st X) = parity m}}
       WHILE (BLe (ANum 2) (AId X))
       DO {{ fun st => parity (st X) = parity m
                       /\ 2 <= st X}} ->>
       {{fun st => parity (st X - 2) = parity m}}
       X ::= AMinus (AId X) (ANum 2)
       {{fun st => parity (st X) = parity m}}
       END
       {{fun st => parity (st X) = parity m
                   /\ st X < 2}} ->>
       {{fun st => st X = parity m}})%dcom.

  Theorem find_parity_dec_correct:
    forall m, dec_correct (find_parity_dec m).
    intro. verify. SearchPattern ( parity _ = _).
    pose (parity_ge_2 (st X) H0).
    rewrite e. auto.
    assert (~ (2 <= st X)). omega.
    pose (parity_lt_2 (st X) H1). rewrite e in H; auto.
  Qed.

  Definition square_root : com :=
      Y ::= (ANum 0);;
      WHILE (BLe (AMult (APlus (AId Y) (ANum 1)) (APlus (AId Y) (ANum 1))) (AId X))
      DO Y ::= APlus (AId Y) (ANum 1)
      END.

  Definition sqrt_dec : dcom :=
    ({{ fun st => True}}
       Y ::= (ANum 0)
       {{fun st => st Y = 0}};; ->>
       {{fun st => (st Y) * (st Y) <= (st X)}}
       WHILE (BLe (AMult (APlus (AId Y) (ANum 1)) (APlus (AId Y) (ANum 1))) (AId X))
       DO {{fun st => (st Y) * (st Y) <= (st X)
                      /\ (st Y + 1)* (st Y + 1) <= st X}}
       Y ::= APlus (AId Y) (ANum 1)
       {{fun st => (st Y) * (st Y) <= st X}}
       END
       {{fun st => (st Y) * (st Y) <= st X
                   /\ (st Y + 1)* (st Y + 1) > st X}})%dcom.
  Theorem sqrt_dec_correct :
    dec_correct sqrt_dec.
    verify.
  Qed.


  Definition square_dec (m:nat): dcom :=
    ({{fun st => st X = m}}
      X ::= AMult (AId X) (AId X)
      {{fun st => st X = m * m}})%dcom.

  Theorem square_dec_correct :
    forall m,
      dec_correct (square_dec m).
    intro. verify.
  Qed.


  Definition dpow2 (m:nat) : com :=
    X ::= ANum 0;;
      Y ::= ANum 0;;
      Z ::= ANum 1;;
      WHILE (BNot (BEq (AId Y) (ANum m)))
      DO
      X ::= APlus (AId X) (AId Z);;
      Z ::= AMult (AId Z) (ANum 2);;
      Y ::= APlus (AId Y) (ANum 1)
      END.

  Fixpoint pow2 (m:nat) :=
    match m with
      | O => 1
      | S n => 2 * (pow2 n)
    end.
  
  Definition dpow_dec (m:nat) : dcom :=
    ({{fun st => True}}
       X ::= (ANum 0)
       {{ fun st => st X = 0}};;
       Y ::= (ANum 0)
       {{ fun st => st Y = 0 /\ st X = 0}};;
       Z ::= (ANum 1)
       {{ fun st => st Z = 1 /\
                    st Y = 0 /\ st X = 0}};; ->>
       {{ fun st => st X = (pow2 (st Y)) - 1 /\
                    st Z = pow2 (st Y) /\
                    st Y = 0
        }}
       WHILE (BNot (BEq (AId Y) (APlus (ANum m) (ANum 1))))
       DO {{fun st => st X = (pow2 (st Y)) - 1 /\
                      st Y <> m + 1 /\
                      st Z = pow2 (st Y)}}
       X ::= APlus (AId X) (AId Z)
       {{fun st => st X = pow2 (st Y + 1) - 1 /\
                   st Y <> m + 1 /\
                   2 * st Z = (pow2 (st Y + 1))}};;
       Z ::= AMult (AId Z) (ANum 2)
       {{ fun st => st X = pow2 (st Y + 1) - 1/\
                    st Y <> m + 1 /\
                    st Z = pow2 (st Y + 1)}};;
       Y ::= APlus (AId Y) (ANum 1)
       {{fun st => st X = pow2 (st Y) - 1 /\
                   st Z = pow2 (st Y)}}
       END
       {{fun st => st X = pow2 (st Y) - 1 /\
                   st Y = m + 1 /\
                   st Z = pow2 (st Y)}} ->>
       {{fun st => st X = pow2 (S m) - 1}})%dcom.



  
  
  Lemma pow2_gt_0:
    forall n, pow2 n > 0.
    intro. elim n; simpl; intros; try auto; try omega.
  Qed.

  Theorem dpow_dec_correct:
    forall m,
      dec_correct (dpow_dec m).
    intro; verify.
    rewrite plus_comm. pattern (st Y + 1). rewrite plus_comm. simpl.
    pose (pow2_gt_0 (st Y)).
    omega.
    pattern (st Y + 1); rewrite plus_comm.
    simpl; auto.
    pattern (m+1); rewrite plus_comm.
    simpl; auto.
  Qed.
  

  