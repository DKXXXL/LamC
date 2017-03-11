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

Inductive SevalR : _Exp -> _State -> _State -> _obj -> Set :=.