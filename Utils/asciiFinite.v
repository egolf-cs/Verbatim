Require Import List.
Import ListNotations.
Require Import Ascii.


Fixpoint asciiEnumFn (n : nat) : list ascii :=
        match n with
        | 0 => []
        | S m => (ascii_of_nat m) :: asciiEnumFn m
        end.

Definition asciiEnum : list ascii := asciiEnumFn 256.

Lemma ascii_finite : forall a : ascii, In a asciiEnum.
Proof.
  intros. destruct a.
  destruct b; destruct b0; destruct b1; destruct b2;
    destruct b3; destruct b4; destruct b5; destruct b6;
  repeat(try(left; reflexivity); right).
Qed.
