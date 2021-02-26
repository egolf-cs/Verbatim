Require Import List.
Import ListNotations.

From Verbatim Require Import ltac.

From Verbatim Require Import regex.

Module ImplFn (Import R : regex.T).

  Fixpoint exp_matchb (s : String) (r : regex) :=
    match s, r with
    | [], _ => nullable r
    | x::xs, _ => exp_matchb xs (derivative x r)
    end.

End ImplFn.

Module LemmasFn (Import R : regex.T).
  
  Include ImplFn R.
  Import R.Ty.
  
  { (**)

    Theorem der_matchb : forall(a : Sigma) (s : String) (r : regex),
        true = exp_matchb (a::s) r <-> true = exp_matchb s (derivative a r).
    Proof.
      intros a s r.
      split; generalize dependent r; induction s; intros r H; simpl; simpl in H; apply H.
    Qed.
    
  }
End LemmasFn.

Module CorrectFn (Import R : regex.T).

  Include LemmasFn R.
  Import R.Ty.

  { (**)

    Theorem der_matchb' : forall(a : Sigma) (s : String) (r : regex),
      exp_matchb (a::s) r = exp_matchb s (derivative a r).
    Proof.
      intros. destruct (exp_matchb (a :: s) r) eqn:E.
      - symmetry in E. rewrite der_matchb in E. auto.
      - symmetry. rewrite false_not_true in *.
        intros C. destruct E.
        symmetry in C. rewrite <- der_matchb in C. auto.
    Qed.

    Theorem match_iff_matchb : forall(s : String) (r : regex),
        true = exp_matchb s r <-> exp_match s r.
    Proof.
      intros s r. split.
      {
        generalize dependent r. induction s; intros r H.
        - simpl in H. apply nullable_bridge. apply H.
        - apply der_match. apply der_matchb in H. apply IHs. apply H.
      }
      {
        generalize dependent r. induction s; intros r H.
        - simpl. apply nullable_bridge. apply H.
        - apply der_match in H. apply der_matchb. apply IHs in H. apply H.
      }
    Qed.

  }
  
End CorrectFn.

Module MatcherFn (Import R : regex.T).
  Include CorrectFn R.
End MatcherFn.
