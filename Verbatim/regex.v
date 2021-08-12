Require Import List.
Import ListNotations.
Require Import Nat.
Require Import Coq.Program.Wf.
Require Import Coq.omega.Omega.
Require Import FSets FSets.FMapAVL FSets.FMapFacts.
Require Import Ascii.

From Verbatim Require Import ltac.
From Verbatim Require Import Orders.

Module Type SIGMA.
  Parameter Sigma : Type.
  Parameter SigmaEnum : list Sigma.
  Parameter Sigma_finite : forall a, In a SigmaEnum.
  Parameter Sigma_dec : forall(a a' : Sigma), {a = a'} + {a <> a'}.
  
  Parameter compareT : Sigma -> Sigma -> comparison.
  Parameter compareT_eq : forall x y : Sigma,
      compareT x y = Eq <-> x = y.

  Parameter compareT_trans : forall c x y z,
      compareT x y = c -> compareT y z = c -> compareT x z = c.

  (* This is a bit superfluous and probably needs some validation unless its identity *)
  Parameter ascii2Sigma : ascii -> Sigma.

End SIGMA.

Module DefsFn (Ty : SIGMA).

  Import Ty.

  Module T_as_UCT <: UsualComparableType.
    Definition t             := Sigma.
    Definition compare       := compareT.
    Definition compare_eq    := compareT_eq.
    Definition compare_trans := compareT_trans.
  End T_as_UCT.

  Module T_as_UOT <: UsualOrderedType := UOT_from_UCT T_as_UCT.

  Module SigFS := FSetAVL.Make T_as_UOT.
  Module SigFSF := FSetFacts.Facts SigFS.

  Module SigFM := FMapAVL.Make T_as_UOT.
  Module SigFMF := FMapFacts.Facts SigFM.
  

  Module Export Strings.

    Set Warnings "-implicit-core-hint-db,-deprecated".
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

    Fixpoint re_compare (e1 e2 : regex) : comparison :=
      match e1, e2 with
      | EmptyStr, EmptyStr => Eq
      | EmptyStr, _ => Lt
      | _, EmptyStr => Gt
      | EmptySet, EmptySet => Eq
      | EmptySet, _ => Lt
      | _, EmptySet => Gt
      | Char a, Char b => compareT a b
      | Char _, _ => Lt
      | _, Char _ => Gt
      | App e1 e2, App e3 e4 =>
        match re_compare e1 e3 with
        | Eq => re_compare e2 e4
        | comp => comp
        end
      | App _ _, _ => Lt
      | _, App _ _ => Gt
      | Star e1, Star e2 => re_compare e1 e2
      | Star _, _ => Lt
      | _, Star _ => Gt
      | Union e1 e2, Union e3 e4 =>
        match re_compare e1 e3 with
        | Eq => re_compare e2 e4
        | comp => comp
        end
      end.

    Lemma re_compare_eq : forall x y : regex, re_compare x y = Eq <-> x = y.
    Proof.
      induction x; destruct y; split;
        try(reflexivity);
        try(simpl; intros; discriminate).
      - simpl. intros. apply compareT_eq in H. subst. auto.
      - simpl. intros. injection H; intros; subst. apply compareT_eq. auto.
      - intros. specialize (IHx1 y1). specialize (IHx2 y2). simpl in H.
        destruct (re_compare x1 y1) eqn:E; try(discriminate).
        destruct IHx1. destruct H0. auto. destruct (re_compare x2 y2); try(discriminate).
        destruct IHx2. destruct H0; auto.
      - intros. injection H. intros; subst. simpl.
        destruct (regex_eq y1 y1) eqn:E.
        + apply regex_eq_correct in E. apply IHx1 in E. rewrite E.
          destruct (regex_eq y2 y2) eqn:E1.
          * apply regex_eq_correct in E1. apply IHx2 in E1. auto.
          * apply false_not_true in E1. destruct E1. apply regex_eq_correct. auto.
        + apply false_not_true in E. destruct E. apply regex_eq_correct. auto.
      - intros. specialize (IHx1 y1). specialize (IHx2 y2). simpl in H.
        destruct (re_compare x1 y1) eqn:E; try(discriminate).
        destruct IHx1. destruct H0. auto. destruct (re_compare x2 y2); try(discriminate).
        destruct IHx2. destruct H0; auto.
      - intros. injection H. intros; subst. simpl.
        destruct (regex_eq y1 y1) eqn:E.
        + apply regex_eq_correct in E. apply IHx1 in E. rewrite E.
          destruct (regex_eq y2 y2) eqn:E1.
          * apply regex_eq_correct in E1. apply IHx2 in E1. auto.
          * apply false_not_true in E1. destruct E1. apply regex_eq_correct. auto.
        + apply false_not_true in E. destruct E. apply regex_eq_correct. auto.
      - intros. specialize (IHx y). simpl in H. apply IHx in H. subst. auto.
      - intros. injection H. intros. subst. simpl. apply IHx. auto.
    Qed.

    Lemma re_compare_eq' : forall x,
        re_compare x x = Eq.
    Proof.
      intros. apply re_compare_eq. auto.
    Qed.

    Lemma re_compare_trans : forall c x y z,
        re_compare x y = c -> re_compare y z = c -> re_compare x z = c.
    Proof.
      induction x; destruct y; destruct z; intros; auto;
        try(simpl in *; subst; discriminate).
      - simpl in *. eapply compareT_trans; eauto.
      - simpl in *.
        destruct(re_compare x1 y1) eqn:E; destruct(re_compare x2 y2) eqn:E0;
          destruct(re_compare y1 z1) eqn:E1; destruct(re_compare y2 z2) eqn:E2;
            try(rewrite re_compare_eq in *; subst; repeat rewrite re_compare_eq' in *; auto);
            try(discriminate);
            try(specialize (IHx2 y2 z2); apply IHx2; auto);
            try(rewrite E0; rewrite E1; auto);
            try(rewrite E1; auto);
            try(rewrite E; auto);
            try(specialize (IHx1 y1 z1); rewrite IHx1; [reflexivity|auto|auto]);
            try(subst; specialize (IHx1 y1 z1); specialize (IHx2 y2 z2);
                rewrite IHx1; [reflexivity|auto|auto]); try(discriminate).
      - simpl in *.
        destruct(re_compare x1 y1) eqn:E; destruct(re_compare x2 y2) eqn:E0;
          destruct(re_compare y1 z1) eqn:E1; destruct(re_compare y2 z2) eqn:E2;
            try(rewrite re_compare_eq in *; subst; repeat rewrite re_compare_eq' in *; auto);
            try(discriminate);
            try(specialize (IHx2 y2 z2); apply IHx2; auto);
            try(rewrite E0; rewrite E1; auto);
            try(rewrite E1; auto);
            try(rewrite E; auto);
            try(specialize (IHx1 y1 z1); rewrite IHx1; [reflexivity|auto|auto]);
            try(subst; specialize (IHx1 y1 z1); specialize (IHx2 y2 z2);
                rewrite IHx1; [reflexivity|auto|auto]); try(discriminate).
      - simpl in *. eapply IHx; eauto.
    Qed.
    
  End Regexes.

  Module regex_as_UCT <: UsualComparableType.
    Definition t := regex.
    Definition compare := re_compare.
    Definition compare_eq := re_compare_eq.
    Definition compare_trans := re_compare_trans.
  End regex_as_UCT.
  

  Module regex_as_UOT <: UsualOrderedType := UOT_from_UCT regex_as_UCT.

  Module reFS := FSetAVL.Make regex_as_UOT.
  Module reFSF := FSetFacts.Facts reFS.

  Module reFM := FMapAVL.Make regex_as_UOT.
  Module reFMF := FMapFacts.Facts reFM.

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
  
End DefsFn.


Module Type DefsT (Ty : SIGMA).
  Include DefsFn Ty.
End DefsT.

Module Type T.
  Declare Module Ty : SIGMA.
  Declare Module Defs  : DefsT Ty.
  Export Defs.
End T.

Module regexTFn (Ty' : SIGMA) <: T.

  Module Export Ty := Ty'.
  Module Export Defs := DefsFn Ty.

End regexTFn.
