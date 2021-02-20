Require Import Nat.
Require Import PeanoNat.

Ltac inv H := inversion H; subst; clear H.
(* destruct a match in a hypothesis *)
Ltac dmh := match goal with | H : context[match ?x with | _ => _ end] |- _ => destruct x eqn:?E end.
(* destruct a match in the goal *)
Ltac dmg := match goal with | |- context[match ?x with | _ => _ end] => destruct x eqn:?E end.
Ltac dm := (first [dmh | dmg]); auto.

Lemma false_not_true : forall(b : bool),
    b = false <-> not(b = true).
Proof.
  intros b. split.
  - intros H. destruct b.
    + discriminate.
    + unfold not. intros C. discriminate.
  - intros H. destruct b.
    + contradiction.
    + reflexivity.
Qed.

Ltac inj_all :=
  match goal with
  | H:context [ (_, _) = (_, _) ] |- _
    => injection H; intros; subst; clear H
  | H:context [ Some _ = Some _ ] |- _
    => injection H; intros; subst; clear H
  end.

Ltac eqb_eq_all :=
  match goal with
  | H:context [ (_ =? _) = _ ] |- _ => try(rewrite false_not_true in H); rewrite Nat.eqb_eq in H
  end.

Ltac ltb_lt_all :=
  match goal with
  | H:context [ (_ <? _) = _ ] |- _ => try(rewrite false_not_true in H); rewrite Nat.ltb_lt in H
  end.
