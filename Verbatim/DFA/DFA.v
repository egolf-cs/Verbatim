Require Import List.
Import ListNotations.
Require Import PeanoNat.
Require Import Coq.omega.Omega.

From Verbatim Require Import ltac.
From Verbatim Require Import regex.
From Verbatim Require Import matcher.
From Verbatim Require Import Table.

Module DFAFn (TabT : Table.T).

  Import TabT.
  Import TabT.Defs.

  Module Export CoreDefs.

    Fixpoint char_set (e : regex) : list Sigma :=
      SigmaEnum.
    (*
      match e with
      | EmptySet | EmptyStr => []
      | Char a => [a]
      | Union e1 e2 | App e1 e2 => nodup Sigma_dec ((char_set e1) ++ (char_set e2))
      | Star e1 => char_set e1
      end.
     *)
     

    Fixpoint regex_depth (e : regex) : nat := 
      match e with
      | EmptySet
      | EmptyStr
      | Char _ => 0
      | App e1 e2
      | Union e1 e2 =>
        let
          d1 := regex_depth e1 in
        let
          d2 := regex_depth e2 in
        if leb d2 d1 then d1 + 1 else d2 + 1
      | Star e0 => (regex_depth e0) + 1
      end.
    
    Definition fin_states (es : reFS.t) :=
      reFS.filter nullable es.
      (*
      match es with
      | [] => []
      | h :: t =>
        let t' := fin_states t in
        if nullable h
        then h :: t'
        else t'
      end.
      *)

    Definition DFA : Type := regex * Table * reFS.t.
    Definition defDFA : DFA := (EmptySet, emptyTable, reFS.empty).

    Definition DFAtransition (a : Sigma) (dfa : DFA) : DFA :=
      match dfa with
        (e, T, fins)
        => match get_Table T e a with
          | Some e' => (e', T, fins)
          | None => (derivative a e, T, fins)
          end
      end.

    Fixpoint DFAtransition_list (bs : list Sigma) (dfa : DFA) : DFA :=
      match bs with
      | [] => dfa
      | c :: cs => DFAtransition_list cs (DFAtransition c dfa)
      end.

    Definition DFAaccepting (dfa : DFA) : bool :=
      match dfa with
        (e, T, fins)
        => if reFS.mem e (get_states T)
          then reFS.mem e fins else nullable e
      end.

    Fixpoint DFAaccepts (z : String) (dfa : DFA) : bool :=
      match z with
      | [] => DFAaccepting dfa
      | x :: xs => DFAaccepts xs (DFAtransition x dfa)
      end.

    Definition regex2dfa (e : regex) : DFA :=
      let
        T := fill_Table_all emptyTable (canon e) (char_set e) 20000
      in
      let
        es := get_states T
      in
      (canon e, T, fin_states es).
    
    Definition dfa2regex (dfa : DFA) : regex :=
      match dfa with (e, _, _) => e end.

  End CoreDefs.

  
  Module Export Correct.

    Module Import Mat := MatcherFn TabT.R.

    (* unused? 
    Lemma In_fin_nullable : forall es x,
      reFS.In x (fin_states es)
      -> nullable x = true.
    Admitted.
    Proof.
      induction es; intros.
      - contradiction.
      - simpl in H. destruct (nullable a) eqn:E.
        + simpl in H. destruct H.
          * subst; auto.
          * auto.
        + auto.
    Qed. *)

    Lemma compat_bool_nullable :
      SetoidList.compat_bool eq nullable.
    Proof.
      unfold SetoidList.compat_bool. unfold Morphisms.Proper. unfold Morphisms.respectful.
      intros. rewrite H. auto.
    Qed.

    Theorem DFAaccepting_nullable : forall T e,
        DFAaccepting (e, T, fin_states (get_states T)) = nullable e.
    Proof.
      intros. unfold DFAaccepting. dm.
      unfold fin_states. destruct (reFS.mem e (reFS.filter nullable (get_states T))) eqn:E1.
      - rewrite reFSF.filter_b in E1.
        + symmetry in E1. apply Bool.andb_true_eq in E1. destruct E1. auto.
        + apply compat_bool_nullable.
      - rewrite reFSF.filter_b in E1.
        + inv E1. rewrite E. auto.
        + apply compat_bool_nullable.
    Qed.

    Theorem transition_Table_correct : forall e e' T es,
        regex2dfa e = (e', T, es)
        -> derived T /\ (es = fin_states (get_states T)) /\ canon e = e'.
    Proof.
      intros. 
      unfold regex2dfa in *. injection H; intros.
      repeat(split).
      - apply derived_get_some in H3.
        + apply H3.
        + eapply derived_closure_all; eauto. apply emptyTable_derived.
      - apply derived_get_some in H3.
        + apply H3.
        + eapply derived_closure_all; eauto. apply emptyTable_derived.
      - inv H. auto.
      - auto.
    Qed.

    Theorem transition_deriv : forall es es' e e' T T' a,
        derived T
        -> DFAtransition a (e, T, es) = (e', T', es')
        -> re_equiv (derivative a e) e'
          /\ T = T' /\ es = es'.
    Proof.
      intros. unfold derived in *. unfold DFAtransition in *. dm.
      - injection H0; intros; subst. clear H0.
        apply H in E. split; [|split]; auto.
        unfold re_equiv in *. intros. symmetry. auto.
      - injection H0; intros; subst. inv H0.
        split; [| split]; auto. unfold re_equiv. reflexivity.
    Qed.

    Lemma accepts_cons : forall z a dfa,
        DFAaccepts (a :: z) dfa
        = DFAaccepts z (DFAtransition a dfa).
    Proof.
      auto.
    Qed.

    Lemma unfold_transition_list : forall bs a dfa,
        DFAtransition_list bs (DFAtransition a dfa)
        = DFAtransition_list (a :: bs) dfa.
    Proof.
      auto.
    Qed.
    
    Lemma accepts_str_lst : forall z dfa,
        DFAaccepts z dfa = DFAaccepting (DFAtransition_list z dfa).
    Proof.
      induction z; intros; auto.
      rewrite accepts_cons. rewrite <- unfold_transition_list.
      apply IHz.
    Qed.
    
    Theorem accepts_deriv : forall z T e a,
        (forall (T : Table) (e : regex),
            derived T -> DFAaccepts z (e, T, fin_states (get_states T)) = exp_matchb z e)
        -> derived T
        -> DFAaccepts (a :: z) (e, T, fin_states (get_states T))
          = DFAaccepts z (derivative a e, T, fin_states (get_states T)).
    Proof.
      intros. rewrite accepts_cons. do 2 rewrite accepts_str_lst.
      unfold DFAtransition. repeat dm.
      do 2 rewrite <- accepts_str_lst.
      rewrite H; auto. rewrite H; auto.
      apply derived_get_some in E; auto.
      unfold re_equiv in E.
      destruct (exp_matchb z r) eqn:E1.
      - symmetry in E1. rewrite match_iff_matchb in *. apply E. auto.
      - symmetry. rewrite false_not_true in *. intros C. destruct E1.
        symmetry. symmetry in C. rewrite match_iff_matchb in *. apply E. auto.
    Qed.

    Theorem accepts_matchb : forall z T e,
        derived T
        -> DFAaccepts z (e, T, fin_states (get_states T))
          = exp_matchb z e.
    Proof.
      induction z; intros.
      - rewrite DFAaccepting_nullable. destruct (nullable e) eqn:E.
        + apply nullable_bridge' in E. apply match_iff_matchb. auto.
        + symmetry. rewrite <- Bool.not_true_iff_false in *. intros C. destruct E.
          apply nullable_bridge'. symmetry in C. apply match_iff_matchb in C. auto.
      - rewrite accepts_deriv; auto.
        rewrite der_matchb'; auto.
    Qed.

    Theorem accepts_match : forall z T e,
        derived T ->
        (DFAaccepts z (e, T, fin_states (get_states T)) = true <-> exp_match z e).
    Proof.
      intros. rewrite accepts_matchb; auto.
      rewrite <- match_iff_matchb. split; symmetry; auto.
    Qed.

    Theorem r2d_accepts_match : forall z e,
        DFAaccepts z (regex2dfa e) = true <-> exp_match z e.
    Proof.
      intros. destruct regex2dfa eqn:H0. destruct p. apply transition_Table_correct in H0.
      do 2 destruct H0. subst.
      rewrite accepts_match; auto.
      apply canon_equiv.
    Qed.

    Lemma DFAaccepts_dt : forall bs a e,
        DFAaccepts bs (regex2dfa (derivative a e))
        = DFAaccepts bs (DFAtransition a (regex2dfa e)).
    Proof.
      intros. rewrite <- accepts_cons.
      destruct (DFAaccepts bs (regex2dfa (derivative a e))) eqn:E.
      - symmetry. rewrite r2d_accepts_match in *. apply der_match. auto.
      - symmetry. rewrite false_not_true in *. intros C. destruct E.
        rewrite r2d_accepts_match in *. apply der_match. auto.
    Qed.

    Lemma exact_table_moot : forall bs e T,
        derived T
        -> 
        DFAaccepts bs (e, T, fin_states (get_states T)) =
        DFAaccepts bs (regex2dfa e).
    Proof.
      induction bs; intros; auto.
      - unfold regex2dfa. repeat rewrite DFAaccepting_nullable.
        clear. destruct (nullable e) eqn:E.
          + symmetry in E. rewrite nullable_bridge in *.
            assert(L := canon_equiv e []). rewrite L. auto.
          + symmetry. rewrite false_not_true in *. intros C. destruct E.
            symmetry. symmetry in C. rewrite nullable_bridge in *.
            assert(L := canon_equiv e []). rewrite L in *. auto.
      - rewrite accepts_deriv; auto. 2: { intros. apply accepts_matchb. auto. }
        rewrite IHbs; auto. rewrite accepts_cons.
        apply DFAaccepts_dt.
    Qed.

      
    Theorem DFAaccepting_dt_list : forall bs e,
        DFAaccepting (DFAtransition_list bs (regex2dfa e))
        = DFAaccepting (regex2dfa (derivative_list bs e)).
    Proof.
      intros. rewrite <- accepts_str_lst.
      generalize dependent e.
      induction bs; intros; auto.
      - destruct (regex2dfa e) eqn:E. destruct p.
        apply transition_Table_correct in E. destruct E. destruct H0. subst.
        subst.
        rewrite accepts_deriv; auto. 2: { intros. apply accepts_matchb. auto. }
        assert(
          DFAaccepts bs (derivative a (canon e), t0, fin_states (get_states t0)) =
          DFAaccepts bs (regex2dfa (derivative a (canon e)))).
        { apply exact_table_moot. auto. }
        rewrite H0. clear H0 H t0.
        rewrite IHbs. 
        assert(
            DFAaccepting (regex2dfa (derivative_list bs (derivative a (canon e)))) =
            DFAaccepting (regex2dfa (derivative_list (a :: bs) (canon e)))).
        { auto. }
        rewrite H. clear H. unfold regex2dfa. repeat rewrite DFAaccepting_nullable.
        clear. destruct (nullable (canon (derivative_list (a :: bs) (canon e)))) eqn:E.
        + symmetry in E. rewrite nullable_bridge in *.
          assert(L := canon_equiv (derivative_list bs (derivative a (canon e))) []).
          rewrite L in *. clear L.
          assert(L := canon_equiv (derivative_list bs (derivative a e)) []).
          apply L. clear L.
          rewrite <- derivative_list_cons in *. rewrite derivative_list_str in *.
          apply canon_equiv. auto.
        + symmetry. rewrite false_not_true in *. intros C. destruct E. rename C into E.
          symmetry. symmetry in E.
          rewrite nullable_bridge in *.
          assert(L := canon_equiv (derivative_list bs (derivative a (canon e))) []).
          rewrite L in *. clear L.
          assert(L := canon_equiv (derivative_list bs (derivative a e)) []).
          rewrite L in *. clear L.
          rewrite <- derivative_list_cons in *. rewrite derivative_list_str in *.
          apply canon_equiv. auto.
    Qed.

  End Correct.

End DFAFn.
