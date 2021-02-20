Require Import List.
Import ListNotations.
Require Import Nat.
Require Import Coq.Program.Wf.
Require Import Coq.omega.Omega.

From Verbatim Require Import ltac.

Module Type SIGMA.
  Parameter Sigma : Type.
  Parameter SigmaEnum : list Sigma.
  Hypothesis Sigma_finite : forall a, In a SigmaEnum.
  Hypothesis Sigma_dec : forall(a a' : Sigma), {a = a'} + {a <> a'}.
End SIGMA.

Module DefsFn (Ty : SIGMA).

  Include Ty.

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


End DefsFn.


Module Type DefsT (Ty : SIGMA).
  Include DefsFn Ty.
End DefsT.

Module Type T.
  Declare Module Ty : SIGMA.
  Declare Module Defs  : DefsT Ty.
  Export Ty.
  Export Defs.
End T.
