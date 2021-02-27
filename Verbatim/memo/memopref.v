Require Import List.
Import ListNotations.
Require Import PeanoNat.
Require Import Coq.omega.Omega.

From VLG Require Import ltac.
From VLG Require Import coredefs.
From VLG Require Import spec.
From VLG Require Import prefixer.
From VLG Require Import lexer.
From VLG Require Import memocore.
From VLG Require Import memospec.

Fixpoint zip {A B : Type} (a: list A) (b: list B) : list (A * B) :=
  match a, b with
  | ha :: ta, hb :: tb => (ha,hb) :: (zip ta tb)
  | _, _ => []
  end.

Fixpoint unzip {A B : Type} (ab : list (A * B)) : (list A) * (list B) :=
  match ab with
  | [] => ([], [])
  | (ha, hb) :: t =>
    match unzip t with
    | (ta, tb) => (ha :: ta, hb :: tb)
    end
  end.
                

(** Single-rule Prefixer **)
Fixpoint max_pref_fn__M (M : Memo) (s : String) (state : State)
  : Memo * option (Prefix * Suffix) :=
  match s with
  (* in a regex approach, accepting := nullable *)
  | [] => if accepting state then (M, Some ([],[])) else (M, None)
  | a :: s' =>
    let
      (* in a regex approach, transition := derivative *)
      state' := transition a state in
    let
      lookup := get_Memo M state' s' in
    let
      mpxs :=
      match lookup with
      | None => max_pref_fn__M M s' state'
      | Some o => (M, o)
      end
    in

    match mpxs with
    | (M', None) => if (accepting state') then (M', Some ([a], s')) else
                     if (accepting state) then (M', Some ([], s)) else
                       (M', None)
    | (M', Some (p, q)) => (M', Some (a :: p, q))
    end
  end.

(** Multi-rule Prefixer **)
Definition extract_fsm_for_max__M (code : String) (sru : Memo * (Label * State))
  : Memo * (Label * option (Prefix * Suffix)) :=
  match sru with
    (M, (a, fsm)) =>
    match max_pref_fn__M M code fsm with
      (M', o) => (M', (a, o))
    end
  end.


Definition max_prefs__M (Ms : list Memo) (code : String) (erules : list (Label * State))
  : (list Memo) * list (Label * option (Prefix * Suffix))
  :=
    let
      zipped := zip Ms erules
    in
    let
      mapped := map (extract_fsm_for_max__M code) zipped
    in
    unzip mapped.

Fixpoint max_of_prefs__M (mprefs : list Memo
                                 * list (Label * (option (Prefix * Suffix))))
  : list Memo * Label * option (Prefix * Suffix) :=
  match mprefs with
    (Ms, prefs) =>
    match max_of_prefs prefs with
      (l, o) => (Ms, l, o)
    end
  end.

Theorem mpref_memo_eq : forall z stt o,
  (exists M, max_pref_fn__M emptyMemo z stt = (M, o))
  <-> max_pref_fn z stt = o.
Proof.
  induction z; split.
  - intros. destruct H. simpl in *. destruct (accepting stt); inv H; auto.
  - intros. exists emptyMemo. simpl in *. destruct (accepting stt); inv H; auto.
  - intros. destruct H. simpl in *.
    repeat dm; repeat inj_all; subst; 
      try(rewrite memocore.correct_emptyMemo in *; discriminate);
      try(apply IHz in E3; destruct E3; rewrite E in H; repeat inj_all; subst; auto; discriminate);
      try(apply IHz in E4; destruct E4; rewrite E in H; repeat inj_all; subst; auto; discriminate).
  - intros. simpl in *.
    repeat dm; repeat inj_all; subst; 
      try(rewrite memocore.correct_emptyMemo in *; discriminate);
      try(apply IHz in E; destruct E; rewrite H in E1;
          repeat inj_all; subst; exists m; auto; discriminate);
      try(eexists; eauto; reflexivity);
      try(apply IHz in E; destruct E; rewrite H in E2; repeat inj_all; subst; discriminate).
Qed.

Lemma lexy_correct : forall M stt z o,
    lexy M
    -> get_Memo M stt z = Some (o)
    -> max_pref_fn z stt = o.
Proof.
  intros. unfold lexy in H. apply H in H0. auto.
Qed.

Theorem mpref_memo_eq_lexy_F : forall z stt o M M',
    lexy M
    -> max_pref_fn__M M z stt = (M', o)
    -> max_pref_fn z stt = o.
Proof.
  induction z; intros.
  - simpl in *. repeat dm; repeat inj_all; auto.
  - simpl in *.
    repeat dm; repeat inj_all; auto;
      try(eapply lexy_correct in H; eauto; rewrite E3 in H);
      try(eapply IHz in H; eauto; rewrite E3 in H);
      try(injection H; intros; subst; auto);
      try(apply lexy_correct in E3; auto; rewrite E3 in E4; auto);
      try(eapply IHz in H; eauto; rewrite E4 in H);
      try(discriminate).
Qed.

Lemma cons_mprefs : forall lst z a rules p,
  max_prefs z (a :: rules) = p :: lst
  -> max_prefs z rules = lst.
Proof.
  intros. simpl in H. injection H. auto.
Qed.

Lemma nil_mprefs__M : forall z,
  max_prefs__M [] z [] = ([], []).
Proof.
  intros. unfold max_prefs__M in *. simpl in *. auto.
Qed.

Lemma cons_mprefs__M : forall m Ms z a rules m' Ms' p lst,
  max_prefs__M (m :: Ms) z (a :: rules) = (m' :: Ms', p :: lst)
  -> max_prefs__M [m] z [a] = ([m'], [p]) /\ max_prefs__M Ms z rules = (Ms', lst).
Proof.
  intros. unfold max_prefs__M in *. simpl in *. repeat dm; repeat inj_all; subst. auto.
Qed.

Theorem mprefs_memo_F : forall z rules Ms Ms' lst,
    lexy_list Ms
    -> length Ms = length rules
    -> max_prefs__M Ms z rules = (Ms', lst)
    -> max_prefs z rules = lst.
Proof.
  induction rules; intros.
  - destruct Ms;
      unfold max_prefs__M in H1; simpl in H1; repeat inj_all; subst; auto; discriminate.
  - destruct Ms; try(discriminate).
    assert(A0 : lexy_list Ms).
    { unfold lexy_list in *. intros. apply H. simpl. right. auto. }
    assert(A1 : length Ms = length rules).
    { simpl in H0. inv H0. auto. }
    destruct lst.
    + unfold max_prefs__M in H1. simpl in H1. repeat dm. discriminate.
    + destruct Ms'.
      * unfold max_prefs__M in H1. simpl in H1. repeat dm. discriminate.
      * simpl. unfold extract_fsm_for_max. dm. subst.
        apply cons_mprefs__M in H1. eapply IHrules in A0; destruct H1; eauto.
        unfold max_prefs__M in e. simpl in e. repeat dm. repeat inj_all; subst.
        assert(A2 : lexy m).
        { unfold lexy_list in *. apply H. simpl. left. auto. }
        eapply mpref_memo_eq_lexy_F in A2; eauto. subst. auto.
Qed.

Theorem all_mprefs_memo_F : forall z rules Ms Ms' l o,
    lexy_list Ms
    -> length Ms = length rules
    -> max_of_prefs__M (max_prefs__M Ms z rules) = (Ms', l, o)
    -> max_of_prefs (max_prefs z rules) = (l, o).
Proof.
  intros. destruct (max_prefs__M Ms z rules) eqn:E.
  apply mprefs_memo_F with (z := z) (rules := rules) (Ms' := Ms') (lst := l1) in H; auto.
  - rewrite H in *. unfold max_of_prefs__M in H1. repeat dm; repeat inj_all; auto.
  - unfold max_of_prefs__M in H1. repeat dm; repeat inj_all; auto.
Qed.
