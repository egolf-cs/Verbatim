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
      match e with
      | EmptySet | EmptyStr => []
      | Char a => [a]
      | Union e1 e2 | App e1 e2 => nodup Sigma_dec ((char_set e1) ++ (char_set e2))
      | Star e1 => char_set e1
      end.

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
    
    Fixpoint fin_states (es : list regex) :=
      match es with
      | [] => []
      | h :: t =>
        let t' := fin_states t in
        if nullable h
        then h :: t'
        else t'
      end.

    Definition DFA : Type := regex * Table * list regex.
    Definition defDFA : DFA := (EmptySet, emptyTable, []).

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
        => match find (fun x => regex_eq e x) fins with
          | None => nullable e
          | Some _ => true
          end
      end.

    Fixpoint DFAaccepts (z : String) (dfa : DFA) : bool :=
      match z with
      | [] => DFAaccepting dfa
      | x :: xs => DFAaccepts xs (DFAtransition x dfa)
      end.

    Definition regex2dfa (e : regex) : DFA :=
      let
        T := fill_Table_all emptyTable e (char_set e) ((regex_depth e)^2)
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

    (*
    Lemma re_sim_nullable : forall e e',
      re_sim e e' = true
      -> nullable e = nullable e'.
    Proof.
      intros. apply re_sim_equiv in H.
      unfold re_equiv in H. specialize (H []).
      do 2 rewrite <- nullable_bridge in H.
      apply Bool.eq_true_iff_eq. split; intros; symmetry; apply H; symmetry; auto.
    Qed.*)

    Lemma In_fin_nullable : forall es x,
      In x (fin_states es)
      -> nullable x = true.
    Proof.
      induction es; intros.
      - contradiction.
      - simpl in H. destruct (nullable a) eqn:E.
        + simpl in H. destruct H.
          * subst; auto.
          * auto.
        + auto.
    Qed.

    Theorem DFAaccepting_nullable : forall es T e,
      DFAaccepting (e, T, fin_states es) = nullable e.
    Proof.
      intros. unfold DFAaccepting. dm.
      apply find_some in E. destruct E.
      apply In_fin_nullable in H.
      apply regex_eq_correct in H0.
      symmetry in H. rewrite H0 in *; auto.
    Qed.

    Theorem transition_Table_correct : forall e e' T es,
        regex2dfa e = (e', T, es)
        -> derived T /\ (exists es', es = fin_states es') /\ canon e = e'.
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
      - eexists; eauto.
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
    
    Theorem accepts_deriv : forall z es T e a,
        (forall (es : list regex) (T : Table) (e : regex),
            derived T -> DFAaccepts z (e, T, fin_states es) = exp_matchb z e)
        -> derived T
        -> DFAaccepts (a :: z) (e, T, fin_states es)
          = DFAaccepts z (derivative a e, T, fin_states es).
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

    Theorem accepts_matchb : forall z es T e,
        derived T
        -> DFAaccepts z (e, T, fin_states es)
          = exp_matchb z e.
    Proof.
      induction z; intros.
      - simpl. dm. apply find_some in E; destruct E.
        apply In_fin_nullable in H0.
        apply regex_eq_correct in H1. rewrite H1. auto.
      - rewrite accepts_deriv; auto.
        rewrite der_matchb'; auto.
    Qed.

    Theorem accepts_match : forall z es T e,
        derived T ->
        (DFAaccepts z (e, T, fin_states es) = true <-> exp_match z e).
    Proof.
      intros. rewrite accepts_matchb; auto.
      rewrite <- match_iff_matchb. split; symmetry; auto.
    Qed.

    Theorem r2d_accepts_match : forall z e,
        DFAaccepts z (regex2dfa e) = true <-> exp_match z e.
    Proof.
      intros. destruct regex2dfa eqn:H0. destruct p. apply transition_Table_correct in H0.
      do 3 destruct H0. subst.
      rewrite accepts_match; auto.
      apply canon_equiv.
    Qed.

    (*  exp_match s (dfa2regex (regex2dfa r)) <-> exp_match s r *)

    (* true = accepts s fsm <-> exp_match s (dfa2regex fsm) *)
    (*
    Lemma foo : forall z dfa,
        DFAaccepts z dfa = DFAaccepts z (regex2dfa (dfa2regex dfa)).
    Proof.
      intros. destruct dfa. destruct p. simpl.
    Qed.*)

    (*
    Theorem d2r_accepts_match : forall z dfa,
        DFAaccepts z dfa = true <-> exp_match z (dfa2regex dfa).
    Proof.
      intros.*)

    

    Lemma DFAaccepts_dt : forall bs a e,
        DFAaccepts bs (regex2dfa (derivative a e)) = DFAaccepts bs (DFAtransition a (regex2dfa e)).
    Proof.
      intros. rewrite <- accepts_cons. destruct (DFAaccepts bs (regex2dfa (derivative a e))) eqn:E.
      - symmetry. rewrite r2d_accepts_match in *. apply der_match. auto.
      - symmetry. rewrite false_not_true in *. intros C. destruct E.
        rewrite r2d_accepts_match in *. apply der_match. auto.
    Qed.

    Lemma exact_table_moot : forall bs e T es,
        derived T
        -> 
        DFAaccepts bs (e, T, fin_states es) =
        DFAaccepts bs (regex2dfa e).
    Proof.
      induction bs; intros; auto.
      - simpl. repeat dm.
        + apply find_some in E. destruct E. apply In_fin_nullable in H0.
          apply regex_eq_correct in H1. rewrite H1 in *. clear H1.
          symmetry in H0. rewrite nullable_bridge in *.
          assert(L := canon_equiv r []). rewrite L. auto.
        + apply find_some in E0. destruct E0. apply In_fin_nullable in H0.
          apply regex_eq_correct in H1. rewrite <- H1 in *. clear H1.
          symmetry. symmetry in H0. rewrite nullable_bridge in *.
          assert(L := canon_equiv e []). rewrite <- L. auto.
        + clear E E0.
          destruct (nullable e) eqn:E.
          * symmetry in E. rewrite nullable_bridge in *.
            assert(L := canon_equiv e []). rewrite L. auto.
          * symmetry. rewrite false_not_true in *. intros C. destruct E.
            symmetry. symmetry in C. rewrite nullable_bridge in *.
            assert(L := canon_equiv e []). rewrite <- L. auto.
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
        apply transition_Table_correct in E. destruct E. destruct H0. destruct H0. subst.
        rewrite accepts_deriv; auto. 2: { intros. apply accepts_matchb. auto. }
        assert(
          DFAaccepts bs (derivative a (canon e), t, fin_states x) =
          DFAaccepts bs (regex2dfa (derivative a (canon e)))).
        { apply exact_table_moot. auto. }
        rewrite H0. clear H0 H x t.
        rewrite IHbs. 
        assert(
            DFAaccepting (regex2dfa (derivative_list bs (derivative a (canon e)))) =
            DFAaccepting (regex2dfa (derivative_list (a :: bs) (canon e)))).
        { auto. }
        rewrite H. clear H. simpl. repeat dm.
        + clear E0. apply find_some in E. destruct E.
          apply In_fin_nullable in H. apply regex_eq_correct in H0.
          rewrite <- H0 in H. clear H0 IHbs.
          symmetry in H. rewrite nullable_bridge in *.
          assert(L := canon_equiv (derivative_list bs (derivative a (canon e))) []).
          apply L in H. clear L.
          assert(L := canon_equiv (derivative_list bs (derivative a e)) []).
          apply L. clear L.
          rewrite <- derivative_list_cons in *. rewrite derivative_list_str in *.
          apply canon_equiv. auto.
        + clear E. apply find_some in E0. destruct E0.
          apply In_fin_nullable in H. apply regex_eq_correct in H0.
          rewrite <- H0 in H. clear H0.
          symmetry. symmetry in H. rewrite nullable_bridge in *.
          assert(L := canon_equiv (derivative_list bs (derivative a (canon e))) []).
          apply L. clear L.
          assert(L := canon_equiv (derivative_list bs (derivative a e)) []).
          apply L in H. clear L.
          rewrite <- derivative_list_cons in *. rewrite derivative_list_str in *.
          apply canon_equiv. auto.
        + clear E E0 IHbs.
          destruct (nullable (canon (derivative_list bs (derivative a e)))) eqn:E.
          * symmetry. symmetry in E. rewrite nullable_bridge in *.
            assert(L := canon_equiv (derivative_list bs (derivative a (canon e))) []).
            apply L. clear L.
            assert(L := canon_equiv (derivative_list bs (derivative a e)) []).
            apply L in E. clear L.
            rewrite <- derivative_list_cons in *. rewrite derivative_list_str in *.
            apply canon_equiv. auto.
          * rewrite false_not_true in *. intros C. destruct E.
            symmetry. symmetry in C. rewrite nullable_bridge in *.
            assert(L := canon_equiv (derivative_list bs (derivative a (canon e))) []).
            apply L in C. clear L.
            assert(L := canon_equiv (derivative_list bs (derivative a e)) []).
            apply L. clear L.
            rewrite <- derivative_list_cons in *. rewrite derivative_list_str in *.
            apply canon_equiv. auto.
    Qed.

  End Correct.

End DFAFn.
