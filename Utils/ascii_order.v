Require Import List.
Import ListNotations.
Require Import Ascii.

From Verbatim Require Import Utils.order.

Definition ascii2list (a : ascii) : list bool :=
  match a with
  | Ascii b b0 b1 b2 b3 b4 b5 b6 =>
    [b; b0; b1; b2; b3; b4; b5; b6]
  end.

Definition bool_order (b1 b2 : bool) : order :=
  match b1, b2 with
  | false, false => EQUAL
  | false, true => LESSER
  | true, false => GREATER
  | true, true => EQUAL
  end.
  
Fixpoint bool_list_order (bs bs' : list bool) : order :=
  match bs, bs' with
  | [], [] => EQUAL
  | [], _ => LESSER
  | _, [] => GREATER
  | h :: t, h' :: t' =>
    match bool_order h h' with
    | EQUAL => bool_list_order t t'
    | o => o
    end
  end.

Definition ascii_order (a1 a2 : ascii) : order :=
  bool_list_order (ascii2list a1) (ascii2list a2).
