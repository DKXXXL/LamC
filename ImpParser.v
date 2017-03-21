Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.Lists.List.

Import ListNotations.

Require Import Maps.
Require Import Imp.

Definition isWhite (c:ascii) : bool :=
  let n := nat_of_ascii c in
  orb (orb (beq_nat n 32)
           (beq_nat n 9))
      (orb (beq_nat n 10)
           (beq_nat n 13)).

Notation "x '<=?' y" := (leb x y)
                          (at level 70, no associativity) : nat_scope.

Definition isLowAlpha (c:ascii) : bool :=
  let n := nat_of_ascii c in
  andb (97 <=? n) (n <=? 122).

Definition isAlpha (c:ascii) : bool :=
  let n:= nat_of_ascii c in
  orb (andb (65 <=? n) (n <=? 90))
      (andb (97 <=? n) (n <=? 122)).

Definition isDigit (c:ascii) : bool :=
  let n:= nat_of_ascii c in
  andb (48 <=? n) (n <=? 57).

Inductive chartype := white | alpha | digit | other.

Definition classifyChar (c: ascii) : chartype :=
  if isWhite c then
    white
  else if isAlpha c then
         alpha
       else if isDigit c then
              digit
            else
              other.

Fixpoint list_of_string (s:string) : list ascii :=
  match s with
    | EmptyString => []
    | String c s => c :: (list_of_string s)
  end.

Fixpoint string_of_list (xs:list ascii) : string :=
  fold_right String EmptyString xs.

Definition token := string.

Fixpoint tokenize_helper (cls:chartype) (acc xs : list ascii)
: list (list ascii) :=
  let tk:= match acc with [] => [] | _ :: _ => [rev acc] end in
  match xs with
    | [] => tk
    | (x :: xs') =>
      match cls, classifyChar x, x with
        | _, _, "(" =>
          tk ++ ["("] :: (tokenize_helper other [] xs')
        | _, _, ")" =>
          tk ++ [")"] :: (tokenize_helper other [] xs')
        | _, white, _ =>
          tk ++ (tokenize_helper white [] xs')
        | alpha, alpha, x =>
          tokenize_helper alpha (x :: acc) xs'
        | digit, digit, 