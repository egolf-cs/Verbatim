Require Import List.
Import ListNotations.
Require Import Nat.
Require Import Coq.Program.Wf.
Require Import Coq.omega.Omega.

From Verbatim Require Import ltac.
From Verbatim Require Import order.

Module Type SIGMA.
  Parameter Sigma : Type.
  Parameter SigmaEnum : list Sigma.
  Parameter Sigma_order : Sigma -> Sigma -> order.
  Parameter Sigma_finite : forall a, In a SigmaEnum.
  Parameter Sigma_dec : forall(a a' : Sigma), {a = a'} + {a <> a'}.
End SIGMA.

Module DefsFn (Ty : SIGMA).

  Import Ty.

  Module Export Strings.

    Hint Resolve Sigma_dec.
    
    Definition String : Type := list Sigma.

    Lemma String_dec : forall s s' : String, {s = s'} + {s <> s'}.
    Proof. decide equality. Qed.

    (** * *Should deprecate/move String lemmas *)
    Lemma nil_right : forall(s : String), s ++ [] = s.
    Proof.
      induction s.
      - simpl. reflexivity.
      - simpl. rewrite IHs. reflexivity.
    Qed.

    Lemma nil_left : forall(s : String), [] ++ s = s.
    Proof.
      intros s. simpl. reflexivity.
    Qed.

    Lemma empty_app : forall(s1 s2 : String), s1 ++ s2 = [] -> s1 = [] /\ s2 = [].
    Proof.
      intros s1 s2 H. destruct s1; destruct s2; try(simpl in H; discriminate).
      - split; reflexivity.
    Qed.

    Definition rm_empty (yss : list String) :=
      filter (fun l => match l with | [] => false | _ => true end) yss.

    Lemma rm_empty_mute : forall(yss : list String),
        concat (rm_empty yss) = concat yss.
    Proof.
      intros yss. induction yss.
      - simpl. reflexivity.
      - simpl. destruct a.
        + simpl. apply IHyss.
        + simpl. rewrite IHyss. reflexivity.
    Qed.

    Lemma rm_empty_no_empty : forall(ys : String) (yss : list String),
        In ys (rm_empty yss) -> ys <> [].
    Proof.
      intros ys yss H. unfold not. intros C. rewrite C in H.
      unfold rm_empty in H. induction yss.
      - simpl in H. contradiction.
      - simpl in H. destruct a.
        + apply IHyss in H. contradiction.
        + simpl in H. destruct H.
          * discriminate.
          * apply IHyss in H. contradiction.
    Qed.

    Lemma filtered_subset : forall(xs : String) (yss : list String),
        In xs (rm_empty yss) -> In xs yss.
    Proof.
      intros xs yss. generalize dependent xs. induction yss; intros xs H.
      - simpl in H. contradiction.
      - simpl. destruct a.
        + simpl in H. right. apply IHyss. apply H.
        + simpl in H. destruct H.
          * left. apply H.
          * right. apply IHyss. apply H.
    Qed.

    End Strings.

    Module Export Regexes.

      Inductive regex : Type :=
      | EmptySet
      | EmptyStr
      | Char (t : Sigma)
      | App (r1 r2 : regex)
      | Union (r1 r2 : regex)
      | Star (r : regex).

      Lemma regex_dec : forall r r' : regex, {r = r'} + {r <> r'}.
      Proof. decide equality. Qed.

      (** * *Should rename to re_equal *)
      Fixpoint regex_eq (r1 r2 : regex) : bool :=
        match r1, r2 with
        | EmptyStr, EmptyStr => true
        | EmptySet, EmptySet => true
        | Char a, Char b => if (Ty.Sigma_dec a b) then true else false
        | App x1 y1, App x2 y2 => andb (regex_eq x1 x2) (regex_eq y1 y2)
        | Union x1 y1, Union x2 y2 => andb (regex_eq x1 x2) (regex_eq y1 y2)
        | Star a, Star b => regex_eq a b
        | _, _ => false
        end.

      Lemma regex_eq_correct : forall r1 r2,
          r1 = r2 <-> regex_eq r1 r2 = true.
      Proof.
        induction r1; intros r2; split; intros H; subst; try(auto);
          try(unfold regex_eq in H; repeat dmh; subst; auto; discriminate).
        - simpl. dmg; [reflexivity | contradiction].
        - assert(A1 : regex_eq r1_1 r1_1 = true). apply IHr1_1; reflexivity.
          assert(A2 : regex_eq r1_2 r1_2 = true). apply IHr1_2; reflexivity.
          simpl. rewrite A1. rewrite A2. auto.
        - destruct r2; simpl in H; try(discriminate).
          destruct (regex_eq r1_1 r2_1) eqn:E1; destruct (regex_eq r1_2 r2_2) eqn:E2; try(discriminate).
          apply IHr1_1 in E1. apply IHr1_2 in E2. subst. reflexivity.
        - assert(A1 : regex_eq r1_1 r1_1 = true). apply IHr1_1; reflexivity.
          assert(A2 : regex_eq r1_2 r1_2 = true). apply IHr1_2; reflexivity.
          simpl. rewrite A1. rewrite A2. auto.
        - destruct r2; simpl in H; try(discriminate).
          destruct (regex_eq r1_1 r2_1) eqn:E1; destruct (regex_eq r1_2 r2_2) eqn:E2; try(discriminate).
          apply IHr1_1 in E1. apply IHr1_2 in E2. subst. reflexivity.
        - assert(A : regex_eq r1 r1 = true). apply IHr1; reflexivity.
          simpl. apply A.
        - destruct r2; simpl in H; try(discriminate). apply IHr1 in H. subst; reflexivity.
      Qed.

      Lemma regex_eq_refl : forall e, regex_eq e e = true.
        intros. induction e; auto.
        - simpl. dm.
        - simpl. apply Bool.andb_true_iff. split; auto.
        - simpl. apply Bool.andb_true_iff. split; auto.
      Qed.







      Fixpoint nullable' (r : regex) : bool:=
        match r with
        | EmptySet => false
        | EmptyStr => true
        | Char _ => false
        | App r1 r2 => andb (nullable' r1) (nullable' r2)
        | Union r1 r2 => orb (nullable' r1) (nullable' r2)
        | Star _ => true
        end.

      Fixpoint nullable (r : regex) : bool:=
        match r with
        | EmptySet => false
        | EmptyStr => true
        | Char _ => false
        | App r1 r2 => if negb (nullable r2) (* short circuit and *)
                      then false
                      else (nullable r1)
        | Union r1 r2 => if (nullable r2)    (* short circuit or *)
                        then true
                        else (nullable r1)
        | Star _ => true
        end.
      
      Fixpoint derivative (a : Sigma) (r : regex) :=
        match r with
        | EmptySet => EmptySet
        | EmptyStr => EmptySet
        | Char x => if Ty.Sigma_dec x a then EmptyStr else EmptySet
        | App r1 r2 => if (nullable r1) then Union (App (derivative a r1) r2) (derivative a r2)
                      else (App (derivative a r1) r2)
        | Union r1 r2 => Union (derivative a r1) (derivative a r2)
        | Star r => App (derivative a r) (Star r)
        end.

      Fixpoint derivative_list (bs : list Sigma) (e : regex) :=
        match bs with
        | [] => e
        | c :: cs => derivative_list cs (derivative c e)
        end.
      
    End Regexes.

    Module Export MatchSpec.

      Inductive exp_match : String -> regex -> Prop :=
      | MEmpty : exp_match [] EmptyStr
      | MChar x : exp_match [x] (Char x)
      | MApp s1 re1 s2 re2
             (H1 : exp_match s1 re1)
             (H2 : exp_match s2 re2) :
          exp_match (s1 ++ s2) (App re1 re2)
      | MUnionL s1 re1 re2
                (H1 : exp_match s1 re1) :
          exp_match s1 (Union re1 re2)
      | MUnionR re1 s2 re2
                (H2 : exp_match s2 re2) :
          exp_match s2 (Union re1 re2)
      | MStar0 re : exp_match [] (Star re)
      | MStarApp s1 s2 re
                 (H1 : exp_match s1 re)
                 (H2 : exp_match s2 (Star re)) :
          exp_match (s1 ++ s2) (Star re).

      Definition re_equiv (e1 e2 : regex) : Prop :=
        forall z, exp_match z e1 <-> exp_match z e2.

    End MatchSpec.

    Module Export MatchSpecLemmas.
      
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
            + simpl. destruct (Sigma_dec t a).
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
          - simpl in H. destruct (Sigma_dec t a); inv H. apply MChar.
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

      Lemma derivative_list_cons : forall bs b e,
          derivative_list (b :: bs) e = derivative_list bs (derivative b e).
      Proof.
        auto.
      Qed.

      Lemma derivative_list_str : forall bs e,
          exp_match [] (derivative_list bs e) <-> exp_match bs e.
      Proof.
        induction bs; intros; auto.
        - simpl. split; auto.
        - simpl. rewrite IHbs. split; apply der_match.
      Qed.
      
    End MatchSpecLemmas.

    Module Notations.
      
      Notation "e1 = e2 " := (regex_eq e1 e2) (at level 70).
      Notation "a ∂ r" := (derivative a r) (at level 75, right associativity).
      Notation ε := EmptyStr.
      Notation "e1 @ e2" := (App e1 e2) (at level 75).
      Notation "e1 # e2" := (Union e1 e2) (at level 75).

    End Notations.

    Module Helpers.
      
      Definition Plus (r : regex) : regex := App r (Star r).

      Fixpoint IterUnion (rs : list regex) :=
        match rs with
        | [] => EmptySet
        | [e] => e
        | h::t => Union h (IterUnion t)
        end.

      Fixpoint IterApp (rs : list regex) :=
        match rs with
        | [] => EmptyStr
        | [e] => e
        | h::t => App h (IterApp t)
        end.

      (* r? *)
      Definition Optional (r : regex) := Union EmptyStr r.

      Definition REString (z : String) := IterApp (map Char z).

    End Helpers.

    (*
    Module Export Similarity.

      Module Export Spec.

        Inductive re_sim_prop : regex -> regex ->  Prop
          :=
            u_self1 (r : regex) : re_sim_prop (Union r r) r
          | u_self2 (r : regex) : re_sim_prop r (Union r r)
          | u_comm1 (r s : regex) : re_sim_prop (Union r s) (Union s r)
          | u_comm2 (r s : regex) : re_sim_prop (Union s r) (Union r s)
          | u_assoc1 (r s t : regex) :
              re_sim_prop (Union (Union r s) t) (Union r (Union s t))
          | u_assoc2 (r s t : regex) :
              re_sim_prop (Union r (Union s t)) (Union (Union r s) t)
          | a_assoc1 (r s t : regex) :
              re_sim_prop (App (App r s) t) (App r (App s t))
          | a_assoc2 (r s t : regex) :
              re_sim_prop (App r (App s t)) (App (App r s) t)
          | sim_refl (r : regex) : re_sim_prop r r.

      End Spec.

      Module Export Impl.

        Import Notations.

        Definition re_sim (e1 e2 : regex) : bool :=
          (e1 = e2)                                       (* sim refl *)
          || match e1, e2 with
            | (r1 # s1) # (t1 # u1), (r2 # s2) # (t2 # u2) =>
              (  (e1 = (r2 # s2)) && (e1 = (t2 # u2))  ) (* self union *)
              || (  (e2 = (r1 # s1)) && (e2 = (t1 # u1))  ) (* self union *)
              || (  ((r1 # s1) = (t2 # u2)) && ((t1 # u1) = (r2 # s2))  ) (* union commutes *)
              (** treat (r1 # s1) as r1 and (t2 # u2) as t2, as in case 2 **)
              || (  ((r1 # s1) = r2) && (t1 = s2) && (u1 = (t2 # u2))  ) (* union assoc *)
              (** treat (r2 # s2) as r2 and (t1 # u1) as t1, as in case 3 **)
              || (  (r1 = (r2 # s2)) && (s1 = t2) && ((t1 # u1) = u2)  ) (* union assoc *)
            (* * case 2 * *)
            | r1 # (s1 # t1), (r2 # s2) # t2 =>
              (  (e1 = (r2 # s2)) && (e1 = t2)  )          (* self union *)
              || (  (e2 = r1) && (e2 = (s1 # t1))  )        (* self union *)
              || (  (r1 = t2) && ((s1 # t1) = (r2 # s2))  ) (* union commutes *)
              || (  (r1 = r2) && (s1 = s2) && (t1 = t2)  )  (* union assoc *)
            (* * case 3 * *)
            | (r1 # s1) # t1, r2 # (s2 # t2) =>
              (  (e1 = r2) && (e1 = (s2 # t2))  )          (* self union *)
              || (  (e2 = (r1 # s1)) && (e2 = t1)  )        (* self union *)
              || (  ((r1 # s1) = (s2 # t2)) && (t1 = r2)  ) (* union commutes *)
              || (  (r1 = r2) && (s1 = s2) && (t1 = t2)  )  (* union assoc *)
            | r1 # s1, s2 # r2 =>
              (  (e1 = r2) && (e1 = s2)  )                 (* self union *)
              || (  (e2 = r1) && (e2 = s1)  )                (* self union *)
              || (  (r1 = r2) && (s1 = s2)  )                (* union commutes *)
            | r0 # r1, _ =>
              (  (e2 = r0) && (e2 = r1)  )                  (* self union *)
            | _, r0 # r1 =>
              (  (e1 = r0) && (e1 = r1)  )                  (* self union *)
            | (r1 @ s1) @ (t1 @ u1), (r2 @ s2) @ (t2 @ u2) =>
              (  ((r1 @ s1) = r2) && (t1 = s2) && (u1 = (t2 @ u2))  )
              || (  (r1 = (r2 @ s2)) && (s1 = t2) && ((t1 @ u1) = u2)  )
            | r1 @ (s1 @ t1), (r2 @ s2) @ t2 =>
              (  (r1 = r2) && (s1 = s2) && (t1 = t2)  )     (* assoc commutes *)                           
            | (r1 @ s1) @ t1, r2 @ (s2 @ t2) => 
              (  (r1 = r2) && (s1 = s2) && (t1 = t2)  )     (* assoc commutes *)   
            | _, _ => false
            end.

      End Impl.

      Module Lemmas.

        Theorem re_sim_correctF : forall e1 e2,
          re_sim e1 e2 = true -> re_sim_prop e1 e2.
        Proof.
          intros.
          unfold re_sim in H.
          repeat dm; try(discriminate);
            repeat(first [rewrite Bool.orb_true_iff in *; destruct H
                         | rewrite Bool.andb_true_iff in *; destruct H]);
            try(discriminate);
            try(rewrite <- regex_eq_correct in *; discriminate);
            try(rewrite <- regex_eq_correct in *; subst; constructor);
            try(rewrite <- regex_eq_correct in *; rewrite H; constructor);
            try(rewrite <- regex_eq_correct in *; rewrite H0; constructor);
            try(rewrite <- regex_eq_correct in *; rewrite H; rewrite H0; constructor);
            try(rewrite <- regex_eq_correct in *; rewrite <- H; rewrite <- H0; constructor).
        Qed.
  
        Theorem re_sim_correctB : forall e1 e2,
            re_sim_prop e1 e2 -> re_sim e1 e2 = true.
        Proof.
          intros.
                  inv H; try(eapply re_sim_correctB_trans; eauto; reflexivity);
            unfold re_sim;
            try(rewrite Bool.orb_true_iff; left; rewrite <- regex_eq_correct; reflexivity);
            repeat dm; try(discriminate);
              repeat(first [rewrite Bool.orb_true_iff | rewrite Bool.andb_true_iff]);
              repeat(rewrite <- regex_eq_correct); repeat rewrite regex_eq_refl;
                try(right; right; right; right; right; split; reflexivity);
                try(right; left; right; right; right; split; reflexivity);
                try(left; right; right; right; right; split; reflexivity);
                try(left; left; right; right; right; split; reflexivity);
                try(right; right; right; right; left; split; reflexivity);
                try(right; left; right; right; left; split; reflexivity);
                try(left; right; right; right; left; split; reflexivity);
                try(left; left; right; right; left; split; reflexivity);
                try(right; right; right; left; right; split; reflexivity);
                try(right; left; right; left; right; split; reflexivity);
                try(left; right; right; left; right; split; reflexivity);
                try(left; left; right; left; right; split; reflexivity);
                try(right; right; right; left; left; split; reflexivity);
                try(right; left; right; left; left; split; reflexivity);
                try(left; right; right; left; left; split; reflexivity);
                try(left; left; right; left; left; split; reflexivity);
                try(right; right; left; right; right; split; reflexivity);
                try(right; left; left; right; right; split; reflexivity);
                try(left; right; left; right; right; split; reflexivity);
                try(left; left; left; right; right; split; reflexivity);
                try(right; right; left; right; left; split; reflexivity);
                try(right; left; left; right; left; split; reflexivity);
                try(left; right; left; right; left; split; reflexivity);
                try(left; left; left; right; left; split; reflexivity);
                try(right; right; left; left; right; split; reflexivity);
                try(right; left; left; left; right; split; reflexivity);
                try(left; right; left; left; right; split; reflexivity);
                try(left; left; left; left; right; split; reflexivity);
                try(right; right; left; left; left; split; reflexivity);
                try(right; left; left; left; left; split; reflexivity);
                try(left; right; left; left; left; split; reflexivity);
                try(left; left; left; left; left; split; reflexivity);
                try(right; left; left; left; right; split; reflexivity);
                try(right; right; right; right; split; reflexivity);
                try(right; right; right; left; split; reflexivity);
                try(right; right; left; right; split; reflexivity);
                try(right; right; left; left; split; reflexivity);
                try(right; left; right; right; split; reflexivity);
                try(right; left; right; left; split; reflexivity);
                try(right; left; left; right; split; reflexivity);
                try(right; left; left; left; split; reflexivity);
                try(left; right; right; right; split; reflexivity);
                try(left; right; right; left; split; reflexivity);
                try(left; right; left; right; split; reflexivity);
                try(left; right; left; left; split; reflexivity);
                try(left; left; right; right; split; reflexivity);
                try(left; left; right; left; split; reflexivity);
                try(left; left; left; right; split; reflexivity);
                try(left; left; left; left; split; reflexivity);
                try(right; right; right; split; reflexivity);
                try(right; right; left; split; reflexivity);
                try(right; left; right; split; auto; reflexivity);
                try(right; left; left; split; reflexivity);
                try(left; right; right; split; reflexivity);
                try(left; right; left; split; reflexivity);
                try(left; left; right; split; reflexivity);
                try(left; left; left; split; reflexivity);
                try(right; right; split; reflexivity);
                try(right; right; split; auto; reflexivity);
                try(right; left; split; auto; reflexivity);
                try(left; right; split; reflexivity);
                try(left; left; split; reflexivity);
                try(left; split; reflexivity);
                try(right; split; auto; reflexivity).
        Qed.

      End Lemmas.

      Module Export Correct.

        Import Lemmas.

        Theorem re_sim_correct : forall e1 e2,
            re_sim e1 e2 = true <-> re_sim_prop e1 e2.
        Proof.
          intros; split; [apply re_sim_correctF | apply re_sim_correctB].
        Qed.

        Lemma re_sim_refl : forall e, re_sim e e = true.
        Proof.
          intros. rewrite re_sim_correct. constructor.
        Qed.

        Theorem re_sim_symm : forall e1 e2, re_sim e1 e2 = re_sim e2 e1.
        Proof.
          intros. destruct (re_sim e1 e2) eqn:E; symmetry.
          - rewrite re_sim_correct in *. inv E; constructor.
          - rewrite false_not_true in *. intros C. destruct E.
            rewrite re_sim_correct in *. inv C; constructor.
        Qed.
        
        Theorem re_sim_equiv : forall e1 e2,
            re_sim e1 e2 = true -> re_equiv e1 e2.
        Proof.
          intros. apply re_sim_correct in H.
          inv H;
            try(unfold re_equiv; intros; split; intros;
                inv H; auto; repeat(constructor); auto; reflexivity);
            unfold re_equiv; intros; split; intros.
          - inv H.
            + inv H2.
              * apply MUnionL. auto.
              * apply MUnionR. apply MUnionL. auto.
            + apply MUnionR. apply MUnionR. auto.
          - inv H.
            + apply MUnionL. apply MUnionL. auto.
            + inv H1.
              * apply MUnionL. apply MUnionR. auto.
              * apply MUnionR. auto.
          - inv H.
            + apply MUnionL. apply MUnionL. auto.
            + inv H1.
              * apply MUnionL. apply MUnionR. auto.
              * apply MUnionR. auto.
          - inv H.
            + inv H2.
              * apply MUnionL. auto.
              * apply MUnionR. apply MUnionL. auto.
            + apply MUnionR. apply MUnionR. auto.
          - inv H. inv H3. rewrite <- app_assoc. repeat(constructor); auto.
          - inv H. inv H4. rewrite app_assoc. repeat(constructor); auto.
          - inv H. inv H4. rewrite app_assoc. repeat(constructor); auto.
          - inv H. inv H3. rewrite <- app_assoc. repeat(constructor); auto.
        Qed.

      End Correct.

    End Similarity.
    *)

End DefsFn.


Module Type DefsT (Ty : SIGMA).
  Include DefsFn Ty.
End DefsT.

Module Type T.
  Declare Module Ty : SIGMA.
  Declare Module Defs  : DefsT Ty.
  Export Defs.
End T.
