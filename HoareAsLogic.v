Require Import Imp.
Require Import Hoare.

Inductive hoare_proof : Assertion -> com -> Assertion -> Type :=
| H_Skip : forall P,
             hoare_proof P (SKIP) P
| H_Asgn : forall Q V a,
             hoare_proof (assn_sub V a Q) (V::= a) Q
| H_Seq : forall P c Q d R,
            hoare_proof P c Q ->
            hoare_proof Q d R ->
            hoare_proof P (c;;d) R
| H_If : forall P Q b c1 c2,
           hoare_proof (fun st => P st /\ bassn b st) c1 Q ->
           hoare_proof (fun st => P st /\ ~(bassn b st)) c2 Q ->
           hoare_proof P (IFB b THEN c1 ELSE c2 FI) Q
| H_While: forall P b c,
             hoare_proof (fun st => P st /\ bassn b st) c P ->
             hoare_proof P (WHILE b DO c END) (fun st => P st /\ ~(bassn b st))
| H_Consequence : forall (P Q P' Q' :Assertion) c,
                    hoare_proof P' c Q' ->
                    (forall st, P st -> P' st) ->
                    (forall st, Q' st -> Q st) ->
                    hoare_proof P c Q.

Lemma H_Consequence_pre :
  forall (P P' Q:Assertion) c,
    hoare_proof P' c Q ->
    (forall st, P st -> P' st) ->
    hoare_proof P c Q.
  intros. eapply H_Consequence. apply X. auto. auto.
Qed.

Lemma H_Consequence_post :
  forall (P Q Q':Assertion) c,
    hoare_proof P c Q' ->
    (forall st, Q' st -> Q st) ->
    hoare_proof P c Q.

  intros; eapply H_Consequence; eauto.
Qed.

Example same_proof:
  hoare_proof
    (assn_sub X (APlus (AId X) (ANum 1))
              (assn_sub X (APlus (AId X) (ANum 2))
                        (fun st => st X = 3)))
    (X ::= APlus (AId X) (ANum 1);; (X::= APlus (AId X) (ANum 2)))
    (fun st => st X = 3).
Proof.
  eapply H_Consequence_pre.
  eapply H_Seq.
  apply H_Asgn.
  apply H_Asgn. auto.
Qed.

Theorem hoare_proof_sound :
  forall P c Q,
    hoare_proof P c Q -> {{P}} c {{Q}}.

  intros.
  elim X.
  apply hoare_skip. apply hoare_asgn.
  intros. eapply hoare_seq; eauto.
  intros. eapply hoare_if; eauto.
  intros. eapply hoare_while; eauto.
  intros. eapply hoare_consequence; eauto.
Qed.


Theorem H_Post_True_deriv :
  forall c P,
    hoare_proof P c (fun _ => True).

  intro. elim c; intros.
  eapply H_Consequence_post. eapply H_Skip. auto.
  eapply H_Consequence_pre. eapply H_Asgn. unfold assn_sub. auto.
  eapply H_Seq; eauto.
  eapply H_If; eauto.
  eapply H_Consequence. apply (H_While (fun st=> True)). apply X. simpl. auto. auto.
Qed.

Theorem H_Pre_False_deriv:
  forall c P,
    hoare_proof (fun st => False) c P.
  intro. elim c.
  intros. eapply H_Consequence_pre. apply H_Skip. intros. elim H.
  intros. eapply H_Consequence_pre. apply H_Asgn. intros. elim H.
  intros. eapply H_Seq. eapply H_Consequence_pre. apply X. intros. elim H. auto.
  intros. eapply H_If. eapply H_Consequence_pre; eauto. intros. inversion H. elim H0.
  eapply H_Consequence_pre; eauto. intros. elim H. auto.
  intros. eapply H_Consequence. apply (H_While (fun st=>False)). eapply H_Consequence_pre. apply X.
  intros. inversion H. elim H0. intros ? x; elim x. simpl. intros ? x; inversion x. elim H.
Qed.

Definition wp (c:com) (Q:Assertion) :Assertion :=
  fun st => (forall st' , c/ st \\ st' -> Q st').


Lemma wp_is_precondition :
  forall c Q,
    {{wp c Q}} c {{Q}}.

  unfold wp. unfold hoare_triple. intros. auto.
Qed.

Lemma wp_is_weakest:
  forall c Q P',
    {{P'}} c {{Q}} -> forall st, P' st -> wp c Q st.
  unfold wp. unfold hoare_triple.
  intros. eauto.
Qed.

Theorem hoare_proof_complete :
  forall P c Q,
    {{P}} c {{Q}} -> hoare_proof P c Q.

  
  intros P c. generalize dependent P. unfold hoare_triple.
  elim c; intros. eapply H_Consequence_pre. apply H_Skip. intro. apply (H st st (E_Skip _)).
  eapply H_Consequence_pre. apply H_Asgn. unfold assn_sub. intro. apply (H st (t_update st i (aeval st a)) (E_Ass st a (aeval st a) i eq_refl)).
  eapply H_Consequence_pre.  pose (X0 (wp c1 Q) Q (wp_is_precondition _ _)).
  pose (X (wp c0 (wp c1 Q)) (wp c1 Q) (wp_is_precondition _ _)).
  pose (wp_is_weakest _ _ _ H). eapply H_Seq. apply h0. auto.
  pose (wp_is_weakest _ _ _ H).
  assert (forall st, wp (c0;;c1) Q st -> wp c0 (wp c1 Q) st).
  unfold wp. intros. apply H0. eapply (E_Seq); eauto. auto.
  pose (wp (IFB b THEN c0 ELSE c1 FI) Q) as p.
  cut (hoare_proof p (IFB b THEN c0 ELSE c1 FI) Q).
  intro. eapply H_Consequence_pre. apply X1. unfold p. intro. apply wp_is_weakest. auto.
  assert (forall st, p st -> ((beval st b = true) -> wp c0 Q st) /\ ((beval st b = false) -> wp c1 Q st)).
  split; intros. unfold wp in p. unfold p in H0. unfold wp. intros. apply H0. apply E_IfTrue; auto.
  unfold wp in p. unfold p in H0. unfold wp. intros. apply H0. apply E_IfFalse; auto.
  eapply H_If; pose wp_is_precondition as h; unfold hoare_triple in h. apply X. unfold bassn. intros. destruct H2. eapply h; eauto. destruct (H0 st H2). auto.
  apply X0. unfold bassn. intros. destruct H2. eapply h; eauto. destruct (H0 st H2). destruct (beval st b). elim (H3 eq_refl). auto.
  apply (H_Consequence _ _ (wp (WHILE b DO c0 END) Q) (fun st => (wp (WHILE b DO c0 END) Q) st /\ ~(bassn b st))).  apply H_While. apply X. unfold wp; unfold bassn. intros. destruct H1. apply H1. eapply E_WhileLoop; eauto.
  eapply wp_is_weakest. unfold hoare_triple. auto. unfold wp; unfold bassn. intros. destruct H0. apply H0. apply E_WhileEnd. destruct (beval st b). elim (H1 eq_refl). auto.
Qed.











