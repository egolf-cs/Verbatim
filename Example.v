Require Import List.
Import ListNotations.

From Verbatim Require Import regex.
From Verbatim Require Import state.
From Verbatim Require Import matcher.

Module Ty <: SIGMA.
  
  Inductive Sigma' := A | B.
  Definition Sigma := Sigma'.
  
  Definition SigmaEnum := [A ; B].
  
  Lemma Sigma_finite : forall a : Sigma, In a SigmaEnum.
  Proof.
    intros. destruct a; simpl; auto.
  Qed.
  
  Lemma Sigma_dec : forall a a' : Sigma, {a = a'} + {a <> a'}.
  Proof. decide equality. Qed.
    
End Ty.

Module R <: regex.T.
  
  Module Ty : SIGMA := Ty.
  Module Defs := regex.DefsFn Ty.

End R.


Module NaiveState (R' : regex.T) <: STATE R'.

  Include MatcherFn R'.
  Include R'.
  
  Definition State := regex.
  Definition defState := EmptySet.
  
  Definition transition (a : Defs.Sigma) (e : State) : State := derivative a e.
  Definition accepts := exp_matchb.
  Definition accepting := nullable.

  Lemma accepts_nil: forall(fsm : State), accepting fsm = accepts [] fsm.
  Proof. intros fsm. reflexivity. Qed.

  Lemma accepts_transition : forall cand a fsm,
      accepts cand (transition a fsm) = accepts (a :: cand) fsm.
  Proof. auto. Qed.

  Definition init_state (r : regex) : State := r.
  Definition init_state_inv (r : State) : regex := r.
  
  Lemma invert_init_correct : forall r s,
      exp_match s (init_state_inv (init_state r)) <-> exp_match s r.
  Proof. intros. split; auto. Qed.
  
  Lemma accepts_matches : forall(s : String) (fsm : State),
      true = accepts s fsm <-> exp_match s (init_state_inv fsm).
  Proof. intros. split; intros; apply match_iff_matchb; auto. Qed.

End NaiveState.

Module ST <: state.T.

  Module R : regex.T := R.
  Module Ty := NaiveState R.
  Module Defs := state.DefsFn R Ty.

End ST.
