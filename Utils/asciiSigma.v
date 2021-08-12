Require Import List.
Import ListNotations.

From Verbatim Require Import regex.
From Verbatim Require Import Utils.asciiFinite.
From Verbatim Require Import Utils.ascii_order.
Require Import Ascii.

Module Export ALPHABET <: SIGMA.
  
  Definition Sigma : Type := ascii.
  Definition SigmaEnum : list Sigma := asciiEnum.
  Definition compareT := ascii_order.
  Definition compareT_eq := ascii_order_eq.
  Definition compareT_trans := ascii_order_trans.

  Lemma Sigma_finite : forall a : Sigma, In a SigmaEnum.
  Proof. apply ascii_finite. Qed.

  Lemma Sigma_dec : forall a a' : Sigma, {a = a'} + {a <> a'}.
  Proof. apply ascii_dec.  Qed.

  Definition ascii2Sigma (a : ascii) : Sigma := a.
  
End ALPHABET.
