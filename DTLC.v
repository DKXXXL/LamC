Require Import Maps.
Require Import ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.



Inductive _Exp : Set :=
| _Const : id -> _Exp
| _Var : id -> _Exp
| _Lamb : id  -> _Exp -> _Exp
| _Add : _Exp -> _Exp -> _Exp
| _Minus : _Exp -> _Exp -> _Exp
| _Mult : _Exp -> _Exp -> _Exp
| _Apply : _Exp -> _Exp -> _Exp.


Inductive _obj : Set :=
| _int :  Z -> _obj
| _str : string -> _obj
| _list : list _obj -> _obj
| _quote : string -> _obj
| _quoteq : _obj -> _obj
| _func : id -> _Exp -> _obj
| _undef : _obj.

Definition _State := total_map _obj.

(*
Fixpoint eval_ (st: _State) (exp : _Exp) {struct exp} : _obj :=
  match exp with
    | _Const x => st x
    | _Var i => st i
    | _Lamb i exp' => _func i exp'
    | _Apply expFunc expArg =>
      let func := eval_ st expFunc in
      let arg := eval_ st expArg in
      match func with
        | _func i exp' => eval_ (t_update st i arg) exp'
        | _ => _undef
      end
    | _Add x y =>
      let x' := eval_ st x in
      let y' := eval_ st y in
      match x' with
        | _int x'' => match y' with _int y'' => _int (x'' + y'') | _ => _undef end
        | _ => _undef
      end
    | _Minus x y =>
      let x' := eval_ st x in
      let y' := eval_ st y in
      match x' with
        | _int x'' => match y' with _int y'' => _int (x'' - y'') | _ => _undef end
        | _ => _undef
      end
    | _Mult x y =>
      let x' := eval_ st x in
      let y' := eval_ st y in
      match x' with
        | _int x'' => match y' with _int y'' => _int (x'' * y'') | _ => _undef end
        | _ => _undef
      end
  end.*)

Reserved Notation "exp '/' st1 '\\' st2 '/' val"
         (at level 40, st1, st2 at level 39).

Inductive SevalR : _Exp -> _State -> _State -> _obj -> Prop :=
| e_const : forall v x st, st x = v ->  (_Const x) / st \\ st / v
| e_var : forall v x st, st x = v -> (_Var x) / st \\ st / v
| e_Lam : forall i st exp, (_Lamb i exp) / st \\ st / _func i exp
| e_App : forall i st v argExp funExp bodyexp v' , 
            (argExp / st \\ st / v) ->
            (funExp / st \\ st / (_func i bodyexp)) ->
            (bodyexp / (t_update st i v) \\ (t_update st i v) / v') ->
            (_Apply funExp argExp) / st \\ st / v'
where "exp '/' st1 '\\' st2 '/' val" := (SevalR exp st1 st2 val).


Print id.

Definition part_unhalting:=
  _Lamb (Id 1) (_Apply (_Var (Id 1)) (_Var (Id 1))).

Definition unhalting := _Apply part_unhalting part_unhalting.



Theorem DTLC_determin:
  forall exp st st1 st2 v1 v2,
    exp / st \\ st1 / v1 -> exp / st \\ st2 / v2 -> st1 = st2 /\ v1 = v2.
  intros exp st st1 st2 v1 v2 h1.
  generalize st2 v2. clear st2 v2.
  elim h1; split. inversion H0; auto. inversion H0. rewrite H4 in H. rewrite H in H2; auto.
  inversion H0; auto. inversion H0. rewrite H4 in H; rewrite H in H2; auto.
  inversion H; auto. inversion H; auto.
  inversion H5; auto. inversion H5. rewrite <- H11 in H8. pose (H0 _ _ H8).
  rewrite <- H11 in H9. pose (H2 _ _ H9).
  inversion a0. inversion H15. rewrite <- H18 in H13. inversion a. rewrite H19 in H4. rewrite H17 in H4. rewrite H11 in H4. pose(H4 (t_update st2 i0 v0) v2 H13). tauto.
Qed.



Lemma classic_unhalting:
  forall st1 st2 v, ~ (unhalting / st1 \\ st2 / v).
  unfold not. remember unhalting as c. unfold unhalting.
  intros. remember part_unhalting as d. rewrite Heqc in H.
  generalize Heqc. 
  elim H; try (rewrite Heqc; discriminate).
  rewrite Heqc.
  intros. unfold unhalting in Heqc0. inversion Heqc0.
  rewrite <- H8 in H0. unfold part_unhalting in H0. inversion H0.
  rewrite <- H12 in H4. rewrite <- H7 in H2. unfold part_unhalting in H2. inversion H2.
  rewrite H19 in H12. rewrite <- H18 in H4. rewrite <- H19 in H4. inversion H4.
  inversion H21; inversion H22. unfold t_update in H31; unfold t_update in H27.
  generalize H31 H27; clear H31 H27. case (eq_id_dec (Id 1) (Id 1)); try (intros; discriminate).
  intros. inversion H31. rewrite H19 in H36. rewrite <- H36 in H24. symmetry in H19.
  inversion H24; try (intros; subst bodyexp; discriminate).
Abort.

(* Failed : Inductive Definition not right *)

(* A Testing on Proof by Vscode.*)
