Require Import Maps.
Require Import ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.



Inductive _obj : Set :=
| _int :  Z -> _obj
| _str : string -> _obj
| _list : list _obj -> _obj
| _quote : string -> _obj
| _quoteq : _obj -> _obj
| _undef : _obj -> _obj.


Inductive _Exp : Set :=
| _Const : _obj -> _Exp
| _Var : id -> _Exp
| _Lamb : id  -> _Exp -> _Exp
| _Apply : _Exp -> _Exp -> _Exp.

(* EXTOp is prepared for extension. Like side effects(IO), and many other stuff *)



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



Definition substt (var :_Exp) : _Exp -> _Exp -> {s| var = _Var s} -> _Exp.
  refine (fix substt bdd exp h :=
          match exp with
            | _Const i => _Const i
            | _Var i => match h with exist s P =>
                                     match eq_id_dec i s with
                                       | left h1 => bdd
                                       | right h2 => _Var i
                                     end
                        end
            | _Lamb i exp' => match h with exist s P =>
                                           match eq_id_dec i s with
                                             | left h1 => _Lamb i exp'
                                             | right h2 => _Lamb i (substt bdd exp' h)
                                           end
                              end
            | _Apply func arg => _Apply (substt bdd func h) (substt bdd arg h)
          end).
Defined.


Reserved Notation "exp '\\' val"
         (at level 40).

Inductive SevalR : _Exp -> _Exp -> Prop :=
| e_const : forall x, (_Const x) \\ (_Const x)
| e_Lam : forall exp i, (_Lamb i exp) \\  (_Lamb i exp)
| e_App : forall argExp funExp bodyExp i v1 v2 , 
            (argExp  \\ v1) ->
            (funExp \\ (_Lamb i bodyExp)) ->
            (substt (_Var i) v1 bodyExp (exist _ i eq_refl) \\ v2) ->
            (_Apply funExp argExp) \\ v2
where "exp '\\' val" := (SevalR exp val).

Theorem DTLC_determine:
  forall exp v1 v2,
    exp \\ v1 -> exp \\ v2 -> v1 = v2.
  intros exp v1 v2 h1; generalize v2; clear v2.
  elim h1; try(intros; inversion H; auto).
  subst v0. subst argExp. inversion H5. pose (H0 _ H8). rewrite <- e in H11. pose (H2 _ H9).
  inversion e0. subst bodyExp0. subst i. auto. inversion H5. pose (H0 _ H10). pose (H2 _ H11).
  inversion e0. subst bodyExp0. symmetry in e. subst v4. subst i1. auto.
  inversion H5. pose(H0 _ H13). pose (H2 _ H14). inversion e0. symmetry in e. subst v6; subst bodyExp1. subst i1. auto.
Qed.



Definition part_unhalting:=
  _Lamb (Id 1) (_Apply (_Var (Id 1)) (_Var (Id 1))).

Definition unhalting := _Apply part_unhalting part_unhalting.



Example classic_unhalting:
  forall v, ~ (unhalting \\ v).
  unfold not. intros.
  remember unhalting as c.
  generalize Heqc. elim H; try (intros; subst c; discriminate).
  intros. unfold unhalting in Heqc0. inversion Heqc0.
  subst funExp. unfold part_unhalting in H2. inversion H2. rewrite H10 in H11.
  subst bodyExp. inversion Heqc0. subst argExp. inversion H0. fold part_unhalting in H6.
  simpl in H5. simpl in H4. rewrite eq_id_dec_id in H5. subst v1. fold unhalting in H5. auto.
Qed.



Inductive _EExp : Set :=
| e_ext : forall cont: _Exp, {i : id & { exp | cont = _Lamb i exp}} -> nat -> _EExp.

(* With side effect. *)