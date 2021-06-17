Require Import List.
Import ListNotations.

From Verbatim Require Import state.
From Verbatim Require Import lexer.correct.
From Verbatim Require Import lexer.impl.
From Verbatim Require Import ltac.

Module Type FIXBIN.

  Parameter min_bits : nat.

End FIXBIN.

Module FixBinDefsFn (FB : FIXBIN).

  Import FB.

  Inductive ubin : Type :=
  | Z
  | D0 (u : ubin)
  | D1 (u : ubin).

  Definition ubin0 := D0 Z.
  Definition ubin1 := D1 Z.
  Definition ubin2 := D0 (D1 Z).
  Definition ubin3 := D1 (D1 Z).
  Definition ubin4 := D0 (D0 (D1 Z)).

  Inductive bin : Type :=
  | N (u : ubin)
  | P (u : ubin).

  Fixpoint incr_u (u : ubin) : ubin :=
    match u with
    | Z => Z
    | D0 u' => D1 u'
    | D1 Z => D0 (D1 Z)
    | D1 u' => D0 (incr_u u')
    end.

  Lemma incr_u_test :
    incr_u (ubin0) = ubin1
    /\ incr_u (ubin1) = ubin2
    /\ incr_u (ubin2) = ubin3
    /\ incr_u (ubin3) = ubin4.
  Proof. auto. Qed.

  Fixpoint decr_u' (u : ubin) : ubin :=
    match u with
    | Z => Z
    | D0 u' => D1 (decr_u' u')
    | D1 Z => Z
    | D1 u' => D0 u'
    end.

  Definition decr_u (u : ubin) : ubin :=
    match u with
    | D1 Z => D0 Z
    | _ => decr_u' u
    end.

  Lemma decr_u_test :
    decr_u (ubin1) = ubin0
    /\ decr_u (ubin2) = ubin1
    /\ decr_u (ubin3) = ubin2
    /\ decr_u (ubin4) = ubin3.
  Proof. auto. Qed.

  Lemma inv_u_test :
    decr_u (incr_u ubin1) = ubin1
    /\ decr_u (incr_u ubin2) = ubin2
    /\ decr_u (incr_u ubin3) = ubin3
    /\ decr_u (incr_u ubin4) = ubin4.
  Proof. auto. Qed.

  Fixpoint init_ubin (n : nat) :=
    match n with
    | 0 => D0 Z
    | S m => incr_u (init_ubin m)
    end.


End FixBinDefsFn.

Module Type DefsT (FB : FIXBIN).
  Include FixBinDefsFn FB.
End DefsT.

Module Type T.
  Declare Module FB : FIXBIN.
  Declare Module Defs : DefsT FB.
  Export FB.
  Export Defs.
End T.
