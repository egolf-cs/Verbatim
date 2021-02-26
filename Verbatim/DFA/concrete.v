Require Import List.
Import ListNotations.

From Verbatim Require Import ltac.
From Verbatim Require Import regex.
From Verbatim Require Import Table.

Module naiveTable (R : regex.T) <: TABLE R.

  Import R.
  Import R.Ty.

  Definition SigmaMap : Type := list (Sigma * regex).


  Fixpoint setSigmaMap (M : SigmaMap) (a : Sigma) (e : regex) : SigmaMap :=
    match M with
    | [] => [(a,e)]
    | (a', e') :: t =>
      if (Sigma_dec a a')
      then (a, e) :: t
      else (a',e') :: (setSigmaMap t a e)
    end.

  Fixpoint getSigmaMap (M : SigmaMap) (a : Sigma) : option regex :=
    match M with
    | [] => None
    | (a', e') :: t =>
      if (Sigma_dec a a')
      then Some e'
      else getSigmaMap t a
    end.                                

  Lemma SMget_of_set : forall M e a,
      getSigmaMap (setSigmaMap M a e) a = Some (e).
  Proof.
    induction M; intros; auto.
    - simpl. dm. contradiction.
    - simpl. repeat dm.
      + simpl. dm. contradiction.
      + simpl. destruct (Sigma_dec a0 s) eqn:E1.
        * contradiction.
        * auto.
  Qed.

  Lemma SMmoot_set : forall M a b r,
      a <> b
      -> getSigmaMap (setSigmaMap M b r) a = getSigmaMap M a.
  Proof.
    induction M; intros.
    - simpl. dm. contradiction.
    - simpl. repeat dm; subst; try(contradiction).
      + simpl. dm. contradiction.
      + simpl. dm. contradiction.
      + simpl. dm. contradiction.
  Qed.



  Definition RegexMap : Type := list (regex * SigmaMap).

  Fixpoint setRegexMap (M : RegexMap) (e : regex) (SM : SigmaMap) :=
    match M with
    | [] => [(e,SM)]
    | (e', SM') :: t =>
      if (regex_dec e e')
      then (e, SM) :: t
      else (e', SM') :: (setRegexMap t e SM)
    end.

  Fixpoint getRegexMap (M : RegexMap) (e : regex) : option SigmaMap :=
    match M with
    | [] => None
    | (e', SM') :: t =>
      if (regex_dec e e')
      then Some SM'
      else getRegexMap t e
    end.    

  Lemma RMget_of_set : forall RM e SM,
      getRegexMap (setRegexMap RM e SM) e = Some (SM).
  Proof.
    induction RM; intros.
    - simpl. dm. contradiction.
    - simpl. repeat (dm; simpl); try(contradiction).
  Qed.

  Lemma RMset_moot : forall RM e e' SM,
      e' <> e
      ->  getRegexMap (setRegexMap RM e SM) e' = getRegexMap RM e'.
  Proof.
    induction RM; intros.
    - simpl. dm. contradiction.
    - simpl. repeat (dm; simpl); try(contradiction).
      clear E1. rewrite e1 in n. rewrite e0 in n. contradiction.
  Qed.


  Definition Table : Type := (RegexMap * list regex).
  Definition emptyTable : Table := ([],[]).

  Fixpoint set_Table (T : Table) (e : regex) (a : Sigma) (e' : regex) : Table :=
    match getRegexMap (fst T) e with
    | None => (setRegexMap (fst T) e (setSigmaMap [] a e'), snd T)
    | Some SM => (setRegexMap (fst T) e (setSigmaMap SM a e'), snd T)
    end.

  Fixpoint get_Table (T : Table) (e : regex) (a : Sigma) : option regex :=
    match getRegexMap (fst T) e with
    | None => None
    | Some SM => getSigmaMap SM a
    end.


  Lemma foo : forall T e a r,
      set_Table T e a r
      = match getRegexMap (fst T) e with
        | None => (setRegexMap (fst T) e (setSigmaMap [] a r), snd T)
        | Some SM => (setRegexMap (fst T) e (setSigmaMap SM a r), snd T)
        end.
  Proof.
    intros. destruct T; auto.
  Qed.

  Lemma bar : forall T e a,
      get_Table T e a
      = match getRegexMap (fst T) e with
        | None => None
        | Some SM => getSigmaMap SM a
        end.
  Proof.
    intros. destruct T; auto.
  Qed.

  Lemma correct_Table : forall T e a r, get_Table (set_Table T e a r) e a = Some (r).
  Proof.
    intros. rewrite bar. rewrite foo. destruct (getRegexMap (fst T) e) eqn:E.
    - dm.
      + simpl in E0. rewrite RMget_of_set in E0. injection E0; intros; subst.
        rewrite SMget_of_set. auto.
      + simpl in E0. rewrite RMget_of_set in *. discriminate.
    - dm.
      + simpl in E0. rewrite RMget_of_set in *.
        assert(s = setSigmaMap [] a r).
        { injection E0; intros; subst; auto. }
        rewrite H.
        rewrite SMget_of_set. auto.
      + simpl in E0. rewrite RMget_of_set in *. discriminate.
  Qed.

  Lemma moot_setTable : forall T e0 e a b r,
      a <> b
      \/ e <> e0
      -> get_Table (set_Table T e b r) e0 a = get_Table T e0 a.
  Proof.
    intros. rewrite bar. rewrite foo. destruct (getRegexMap (fst T) e) eqn:E.
  Admitted.

  Lemma correct_emptyTable : forall e a, get_Table emptyTable e a = None.
  Proof.
    auto.
  Qed.

  Definition add_state (T : Table) (e : regex) : Table :=
    match T with
    | (T', sts) => (T', e :: sts)
    end.

  Definition get_states (T : Table) := snd T.

  Lemma empty_states : get_states emptyTable = [].
  Proof. auto. Qed.

  Lemma correct_states : forall T r, In r (get_states (add_state T r)).
  Proof.
    intros. destruct T. simpl. auto.
  Qed.

  Lemma moot_add_state : forall T e a r,
      get_Table T e a = get_Table (add_state T r) e a.
  Proof.
    intros. destruct T. auto.
  Qed.

End naiveTable.
