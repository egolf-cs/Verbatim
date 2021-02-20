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
  
  { (**)
    
    Theorem nullable_bridge : forall(r : regex),
      true = nullable r <-> exp_match [] r.
    Proof.
      intros r. split; intros H.
      - induction r; try(simpl in H; discriminate).
        + apply MEmpty.
        + simpl in H. destruct (nullable r1); destruct (nullable r2); try(simpl in H; discriminate).
          rewrite <- nil_left with (s := []). apply MApp.
          * apply IHr1. reflexivity.
          * apply IHr2. reflexivity.
        + simpl in H.  destruct (nullable r1); destruct (nullable r2).
          * apply MUnionL. apply IHr1. reflexivity.
          * apply MUnionL. apply IHr1. reflexivity.
          * apply MUnionR. apply IHr2. reflexivity.
          * simpl in H. discriminate.
        + apply MStar0.
      - induction r.
        + inversion H.
        + simpl. reflexivity.
        + inversion H.
        + simpl. inversion H. apply empty_app in H1. destruct H1.
          rewrite H1 in H3. rewrite H5 in H4.
          apply IHr1 in H3. apply IHr2 in H4.
          rewrite <- H3. rewrite <- H4. simpl. reflexivity.
        + simpl. inversion H.
          * apply IHr1 in H2. rewrite <- H2. destruct (nullable r2); simpl; reflexivity.
          * apply IHr2 in H1. rewrite <- H1. destruct (nullable r1); simpl; reflexivity.
        + simpl. reflexivity.
    Qed.

    Theorem nullable_bridge' : forall(r : regex),
        nullable r = true <-> exp_match [] r.
    Proof.
      split; intros.
      - symmetry in H. apply nullable_bridge; auto.
      - symmetry. apply nullable_bridge; auto.
    Qed.

    (* star_concat upto concat_star necessary for hard star case of der_match *)
    Lemma star_concat :
      forall s r',
        exp_match s (Star r')
        -> (exists xss : list (list Sigma),
               s = concat xss
               /\ (forall xs,
                      In xs xss
                      -> exp_match xs r')).
    Proof.
      intros s r' hm.
      remember (Star r') as r. generalize dependent r'.
      induction hm; intros r' heq; inv heq.
      - exists []; split; auto.
        intros xs hi; inv hi.
      - destruct (IHhm2 r') as (xss' & heq & hall); subst; auto.
        exists (s1 :: xss'); split; auto.
        intros xs hi.
        destruct hi as [hh| ht]; subst; auto.
    Qed.

    Lemma star_concat_no_empt : forall(s : String) (r' : regex),
        s <> []
        -> exp_match s (Star r')
        -> (exists xss : list (list Sigma),
               s = concat xss
               /\ (forall xs,
                      In xs xss
                      -> exp_match xs r' /\ xs <> [])).
    Proof.
      intros s r' Hempty Hstar. apply star_concat in Hstar.
      destruct Hstar as (yss & heq & hall).
      exists(rm_empty yss). split.
      - rewrite rm_empty_mute. apply heq.
      - intros xs H. split.
        + apply hall.  apply filtered_subset in H. apply H.
        + apply rm_empty_no_empty in H. apply H.
    Qed.

    Lemma concat_star : forall(xss : list String) (r : regex),
        (forall xs : list Sigma, In xs xss -> exp_match xs r) -> exp_match (concat xss) (Star r).
    Proof.
      intros xss r H. induction xss.
      - simpl. apply MStar0.
      - replace (concat (a :: xss)) with (a ++ (concat xss)).
        + apply MStarApp.
          * apply H. simpl. left. reflexivity.
          * apply IHxss. intros xs H1. apply H. simpl. right. apply H1.
        + simpl. reflexivity.
    Qed.

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
    
    Theorem der_match : forall(a : Sigma) (s : String) (r : regex),
        exp_match (a::s) r <-> exp_match s (derivative a r).
    Proof.
      intros a s r.
      split.
      {
        generalize dependent s. induction r; intros s H.
        - inv H.
        - inv H.
        - destruct s.
          + simpl. destruct (R.Ty.Sigma_dec t a).
            * apply MEmpty.
            * inv H. contradiction.
          + inv H.
        - simpl. destruct(nullable r1) eqn:E.
          + inv H. destruct s1.
            * apply MUnionR. apply IHr2. rewrite <- H1. simpl. apply H4.
            * apply MUnionL. simpl in H1. injection H1. intros Happ Hchar.
              rewrite <- Happ. rewrite Hchar in H3. apply IHr1 in H3.
              apply MApp.
              -- apply H3.
              -- apply H4.
          + inv H. destruct s1.
            * apply nullable_bridge in H3. rewrite E in H3. discriminate.
            * simpl in H1. injection H1. intros Happ Hchar.
              rewrite <- Happ. rewrite Hchar in H3. apply IHr1 in H3.
              apply MApp.
              -- apply H3.
              -- apply H4.
        - simpl. inv H.
          + apply IHr1 in H2. apply MUnionL. apply H2.
          + apply IHr2 in H1. apply MUnionR. apply H1.
        (* hard_star: This case was the hard one *)
        - apply star_concat_no_empt in H. destruct H as (xss & heq & hall).
          + assert (H : exists(s1 : String) (yss : list String),
                       ((a :: s1) :: yss) = xss).
            {
              destruct xss.
              - simpl in heq. discriminate.
              - simpl in heq. destruct l eqn:E.
                + apply hall in E.
                  * contradiction.
                  * rewrite E. simpl. left. reflexivity.
                + exists(l0). exists(xss). simpl in heq.
                  injection heq. intros I1 I2. rewrite I2. reflexivity.
            }
            destruct H as [s1]. destruct H as [yss].
            rewrite <- H in hall.
            assert (A : In (a :: s1) ((a :: s1) :: yss)).
            { simpl. left. reflexivity. }
            simpl. replace s with (s1 ++ (concat yss)).
            * apply MApp.
              -- apply IHr. apply hall in A. destruct A. apply H0.
              -- rewrite H in hall.
                 assert (A1 : forall xs : list Sigma, In xs xss -> exp_match xs r).
                 { intros xs. intros HA1. apply hall in HA1. destruct HA1. apply H0. }
                 apply concat_star. intros xs H1. apply A1.
                 rewrite <- H. simpl. right. apply H1.
            * assert (A1 : concat ((a :: s1) :: yss) = concat xss).
              { rewrite H. reflexivity. }
              assert (A2 : concat ((a :: s1) :: yss) = a :: (s1 ++ (concat yss))).
              { simpl. reflexivity. }
              rewrite <- A1 in heq. rewrite A2 in heq. injection heq.
              intros I. symmetry. apply I.
          + unfold not. intros C. discriminate.
      }
      {
        generalize dependent s. induction r; intros s H.
        - inv H.
        - inv H.
        - simpl in H. destruct (R.Ty.Sigma_dec t a); inv H. apply MChar.
        - simpl in H. destruct (nullable r1) eqn:E.
          + inv H.
            * inv H2. replace (a :: s1 ++ s2) with ((a :: s1) ++ s2).
              apply MApp.
              -- apply IHr1. apply H3.
              -- apply H4.
              -- reflexivity.
            * symmetry in E. apply nullable_bridge in E. rewrite <- nil_left with (s := (a :: s)).
              apply MApp.
              -- apply E.
              -- apply IHr2. apply H1.
          + inv H.
            * replace (a :: s1 ++ s2) with ((a :: s1) ++ s2).
              apply MApp.
              -- apply IHr1. apply H3.
              -- apply H4.
              -- reflexivity.
        - inv H.
          + apply MUnionL. apply IHr1. apply H2.
          + apply MUnionR. apply IHr2. apply H1.
        - simpl in H. inv H. replace (a :: s1 ++ s2) with ((a :: s1) ++ s2).
          + apply MStarApp.
            * apply IHr. apply H3.
            * apply H4.
          + reflexivity.
      }
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
