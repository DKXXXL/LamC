Require Export Basics.

(* Some trivial exercises *)

Theorem plus_n_0_:
  forall n,
    n = 0 + n.

Proof. intro n.
induction n; auto. Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_is_idem_plus:
forall n, double n = n + n.

Proof. intro n; induction n; auto.
assert (forall n m, n + S m = S(n + m)).
intro k; induction k; auto.
rewrite H; simpl; auto.
Qed.

