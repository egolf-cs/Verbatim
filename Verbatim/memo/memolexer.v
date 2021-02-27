Require Import List.
Import ListNotations.
Require Import PeanoNat.
Require Import Coq.omega.Omega.

From VLG Require Import ltac.
From VLG Require Import coredefs.
From VLG Require Import spec.
From VLG Require Import prefixer.
From VLG Require Import lexer.
From VLG Require Import lemmas.
From VLG Require Import memocore.
From VLG Require Import memopref.
From VLG Require Import memospec.

(* Lexer *)


Lemma memo_len_const : forall n Ms rules code Ms' l0,
    n = length Ms'
    -> length Ms = length rules
    -> max_prefs__M Ms code rules = (Ms', l0)
    -> length Ms' = length Ms.
Proof.
  induction n; intros; destruct rules; destruct Ms; destruct Ms'; destruct l0;
      try(simpl in *; auto; discriminate);
      try(unfold max_prefs__M in *; simpl in *; repeat dm; repeat inj_all; subst; discriminate).
  + simpl in *. injection H; intros; clear H. injection H0; intros; clear H0.
    apply cons_mprefs__M in H1. destruct H1. eapply IHn in H2; eauto.
Qed.

Lemma labeled_len_const : forall n Ms rules code Ms' l0,
    n = length Ms'
    -> length Ms = length rules
    -> max_prefs__M Ms code rules = (Ms', l0)
    -> length Ms' = length l0.
Proof.
  induction n; intros; destruct rules; destruct Ms; destruct Ms'; destruct l0;
      try(simpl in *; auto; discriminate);
      try(unfold max_prefs__M in *; simpl in *; repeat dm; repeat inj_all; subst; discriminate).
  + simpl in *. injection H; intros; clear H. injection H0; intros; clear H0.
    apply cons_mprefs__M in H1. destruct H1. eapply IHn in H2; eauto.
Qed.

Lemma all_lens_const' : forall n Ms rules code Ms' l0,
    n = length Ms'
    -> length Ms = length rules
    -> max_prefs__M Ms code rules = (Ms', l0)
    -> length Ms' = length Ms /\ length Ms' = length l0.
Proof.
  intros. split.
  - eapply memo_len_const; eauto.
  - eapply labeled_len_const; eauto.
Qed.

Lemma all_lens_const : forall Ms rules code Ms' l0,
    length Ms = length rules
    -> max_prefs__M Ms code rules = (Ms', l0)
    -> length Ms' = length Ms /\ length Ms' = length l0.
Proof.
  intros. eapply all_lens_const'; eauto.
Qed.

Lemma mprefs__M_associates :
  forall n rules Ms Ms' code (l0 : list (Label * option (Prefix * Suffix))) M M' o label ru,
  length Ms = length rules
  -> max_prefs__M Ms code rules = (Ms', l0)
  -> n < length Ms'
  -> nth n Ms emptyMemo = M
  -> nth n Ms' emptyMemo = M'
  -> nth n l0 ([], None) = (label, o)
  -> nth n rules ([], defState) = (label, ru)
  -> max_pref_fn__M M code ru = (M', o).
Proof.
  induction n; intros; destruct Ms; destruct Ms'; destruct l0; destruct rules;
      try(simpl in *; omega);
      try(rewrite nil_mprefs__M in *; repeat inj_all; discriminate);
      try(simpl in *; repeat inj_all; unfold max_prefs__M in *; simpl in *;
          repeat dm; repeat inj_all; discriminate).
    + simpl in *. subst. unfold max_prefs__M in *. simpl in *.
      repeat dm. repeat inj_all. auto.
    + simpl in *. injection H; intros; clear H.
      apply lt_S_n in H1. eapply IHn; eauto. eapply cons_mprefs__M; eauto.
Qed.


Lemma nth_labels_match'' : forall m n rules Ms code Ms' l0 o ru label label',
    m = length rules
    -> length Ms = length rules
    -> length rules = length l0
    -> length Ms' = length Ms
    -> n < length Ms'
    -> max_prefs__M Ms code rules = (Ms', l0)
    -> nth n l0 ([], None) = (label, o)
    -> nth n rules ([], defState) = (label', ru)
    -> label = label'.
Proof.
  induction m; intros; destruct Ms; destruct rules; destruct Ms'; destruct l0; destruct n;
    try(simpl in *; omega).
  - apply cons_mprefs__M in H4. destruct H4. clear H7. simpl in *.
    unfold max_prefs__M in H4. simpl in *. repeat dm; repeat inj_all. auto.
  - simpl in *.
    apply Nat.succ_inj in H.  apply Nat.succ_inj in H0.
    apply Nat.succ_inj in H1. apply Nat.succ_inj in H2.
    apply lt_S_n in H3.
    apply cons_mprefs__M in H4. destruct H4.
    eapply IHm; eauto.
Qed.

Lemma nth_labels_match' : forall m n rules Ms code Ms' l0 o ru label label',
    m = length rules
    -> length Ms = length rules
    -> n < length Ms'
    -> max_prefs__M Ms code rules = (Ms', l0)
    -> nth n l0 ([], None) = (label, o)
    -> nth n rules ([], defState) = (label', ru)
    -> label = label'.
Proof.
  intros.
  assert(L := all_lens_const Ms rules code Ms' l0 H0 H2). destruct L.
  eapply nth_labels_match''; eauto. omega.
Qed.

Lemma nth_labels_match : forall n rules Ms code Ms' l0 o ru label label',
    max_prefs__M Ms code rules = (Ms', l0)
    -> length Ms = length rules
    -> n < length Ms'
    -> nth n l0 ([], None) = (label, o)
    -> nth n rules ([], defState) = (label', ru)
    -> label = label'.
Proof.
  intros. eapply nth_labels_match'; eauto.
Qed.

Lemma lexy_closure : 
  forall code rules M o M',
  lexy M
  -> max_pref_fn__M M code rules = (M', o)
  -> lexy M'.
Proof.
  induction code; intros.
  - simpl in H0. repeat dm; repeat inj_all; auto; discriminate.
  - simpl in H0. repeat dm; repeat inj_all; auto;
                   try(eapply IHcode; eauto).
Qed.

Lemma lexy_list_closure : 
  forall code rules Ms l0 Ms',
  lexy_list Ms
  -> length Ms = length rules
  -> max_prefs__M Ms code rules = (Ms', l0)
  -> lexy_list Ms'.
Proof.
  intros. unfold lexy_list in *. intros M' H2.
  apply In_nth with (d := emptyMemo) in H2. destruct H2 as [n]. destruct H2.
  assert(L := all_lens_const Ms rules code Ms' l0 H0 H1). destruct L.
  assert(exists M, nth n Ms emptyMemo = M).
  { eexists; eauto. }
  destruct H6 as [M].
  assert(exists label o, nth n l0 ([], None) = (label, o)).
  { destruct (nth n l0 ([], None)). eexists; eauto. }
  destruct H7 as [label]. destruct H7 as [o].
  assert(exists label' ru, nth n rules ([], defState) = (label', ru)).
  { destruct (nth n rules ([], defState)). eexists; eauto. }
  destruct H8 as [label']. destruct H8 as [ru].
  assert(label = label').
  { eapply nth_labels_match; eauto. }
  rewrite H9 in *. clear H9.
  eapply mprefs__M_associates in H0; eauto.

  assert(Hlen : length Ms = length Ms').
  { omega. }
  
  rewrite <- Hlen in H2.
  apply nth_In with (d:=emptyMemo) in H2. rewrite H6 in H2. apply H in H2.
  eapply lexy_closure; eauto.
Qed.

Lemma len_recursive_call :
  forall code rules label s l suffix Ms Ms',
    length Ms = length rules
    -> max_of_prefs__M (max_prefs__M Ms code rules) = (Ms', label, Some (s :: l, suffix))
    -> length Ms' = length rules.
Proof.
  intros. destruct (max_prefs__M Ms code rules) eqn:E.
  assert(l0 = Ms').
  {
    simpl in H0. repeat dm. injection H0; auto.
  }
  subst. clear H0.
  assert(L := all_lens_const Ms rules code Ms' l1 H E). destruct L. omega.
Qed.
  

Lemma lexy_recursive_call_gen :
  forall code rules Ms label o Ms',
  lexy_list Ms
  -> length Ms = length rules
  -> max_of_prefs__M (max_prefs__M Ms code rules) = (Ms', label, o)
  -> lexy_list Ms'.
Proof.
  intros. destruct (max_prefs__M Ms code rules) eqn:E.
  assert(l = Ms').
  {
    simpl in H1. repeat dm. injection H1; auto.
  }
  subst. clear H1.
  eapply lexy_list_closure in H; eauto.
Qed.


Lemma lexy_recursive_call :
  forall code rules Ms label s l suffix Ms',
  lexy_list Ms
  -> length Ms = length rules
  -> max_of_prefs__M (max_prefs__M Ms code rules) = (Ms', label, Some (s :: l, suffix))
  -> lexy_list Ms'.
Proof.
  intros. eapply lexy_recursive_call_gen in H; eauto.
Qed.
  
Lemma acc_helper__M : forall Ms code rules Ms' label o,
    lexy_list Ms
    -> length Ms = length rules
    -> max_of_prefs__M (max_prefs__M Ms code rules) = (Ms', label, o)
    -> max_of_prefs (max_prefs code rules) = (label, o).
Proof.
  intros. destruct (max_prefs code rules) eqn:E; destruct (max_prefs__M Ms code rules) eqn:E1.
  - simpl in *. repeat dm; repeat inj_all; subst. eapply mprefs_memo_F in H; eauto.
    + rewrite E in H. subst. simpl in E0. auto.
  - simpl in *. repeat dm; repeat inj_all; subst. eapply mprefs_memo_F in H; eauto.
    rewrite E in H. subst. simpl in E0. auto.
Qed.

Lemma acc_recursive_call__M :
  forall code rules label s l suffix Ms Ms',
    Acc lt (length code)
    -> lexy_list Ms
    -> length Ms = length rules
    -> max_of_prefs__M (max_prefs__M Ms code rules) = (Ms', label, Some (s :: l, suffix))
    -> Acc lt (length suffix).
Proof.
  intros. eapply acc_helper__M in H0; eauto; eapply acc_recursive_call; eauto.
Defined.

Fixpoint lex'__M
         (Ms : list Memo)
         (rules : list (sRule))
         (code : String)
         (Ha : Acc lt (length code))
         (Hlexy : lexy_list Ms)
         (Hlen : length Ms = length rules)
         {struct Ha} : (list Memo) * (list Token) * String :=
  match max_of_prefs__M (max_prefs__M Ms code rules) as mpref'
        return max_of_prefs__M (max_prefs__M Ms code rules) = mpref' -> _
  with
  | (Ms', _, None) => fun _ => (Ms', [], code) (* Code cannot be processed further *)
  | (Ms', _, Some ([], _)) => fun _ => (Ms', [], code) (* Code cannot be processed further *)
  | (Ms', label, Some (ph :: pt, suffix)) =>
    fun Heq =>
      match (lex'__M Ms' rules suffix
                   (acc_recursive_call__M _ _ _ _ _ _ _ _ Ha Hlexy Hlen Heq)
                   (lexy_recursive_call _ _ _ _ _ _ _ _ Hlexy Hlen Heq)
                   (len_recursive_call _ _ _ _ _ _ _ _ Hlen Heq)
            )
      with
      | (Ms'', lexemes, rest) => (Ms'', ((label, ph :: pt) :: lexemes), rest)
      end
  end eq_refl.
