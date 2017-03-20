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


Fixpoint substt (exp : _Exp) (var : _Exp) (bdd : _Exp) : _Exp :=
  match exp with
    | 

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
