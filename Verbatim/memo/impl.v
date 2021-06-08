Require Import List.
Import ListNotations.
Require Import PeanoNat.
Require Import Coq.omega.Omega.
Require Import Coq.Numbers.NatInt.NZOrder.

From Verbatim Require Import ltac.
From Verbatim Require Import memo.
From Verbatim Require Import lexer.impl.

Module ImplFn (Import MEM : memo.T).

  Module Import MEMO := MEM.MemTy.
  Module Import Defs := MEM.Defs.
  Import Defs.NaiveLexer.
  Import Defs.NaiveLexer.MPref.
  Import MEM.STT.Defs.
  Import MEM.STT.Ty.

  Module Export Utils.

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

  End Utils.
    
  Module Export MPref.
         
    (** Single-rule Prefixer **)
    Fixpoint max_pref_fn__M (M : Memo) (s : String) (state : State) (d : Delta)
    : Memo * option (String * String) :=
      match s with
      (* in a regex approach, accepting := nullable *)
      | [] => if accepting state d then (M, Some ([],[])) else (M, None)
      | a :: s' =>
        let
          (* in a regex approach, transition := derivative *)
          state' := transition a state d in
        let
          lookup := get_Memo M state' s' in
        let
          mpxs :=
          match lookup with
          | None => max_pref_fn__M M s' state' d
          | Some o => (M, o)
          end
        in

        match mpxs with
        | (M', None) => if (accepting state' d) then (M' , Some ([a], s')) else
                         if (accepting state d) then (M', Some ([], s)) else
                           ((set_Memo M' state s None), None)
        | (M', Some (p, q)) => (M', Some (a :: p, q))
        end
      end.

    (** Multi-rule Prefixer **)
    Definition extract_fsm_for_max__M (code : String) (sru : Memo * (Label * State * Delta))
      : Memo * (Label * option (Prefix * Suffix)) :=
      match sru with
        (M, (a, fsm, d)) =>
        match max_pref_fn__M M code fsm d with
          (M', o) => (M', (a, o))
        end
      end.


    Definition max_prefs__M (Ms : list Memo) (code : String) (erules : list (Label * State * Delta))
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

  End MPref.

  Module Export TypeCheckLemmas.

    Module Export MemoEq.

      Lemma lexy_correct : forall M stt z o d,
        lexy M d
        -> get_Memo M stt z = Some (o)
        -> max_pref_fn z stt d = o.
      Proof.
        intros. unfold lexy in H. apply H in H0. auto.
      Qed.

      Theorem mpref_memo_eq_lexy_F : forall z stt o M M' d,
          lexy M d
          -> max_pref_fn__M M z stt d = (M', o)
          -> max_pref_fn z stt d = o.
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
          + unfold lexy in H. apply H in E3. rewrite E3 in E4. discriminate.
          + unfold lexy in H. apply H in E3. rewrite E3 in E4. discriminate.
      Qed.

      Lemma cons_mprefs__M : forall m Ms z a rules m' Ms' p lst,
          max_prefs__M (m :: Ms) z (a :: rules) = (m' :: Ms', p :: lst)
          -> max_prefs__M [m] z [a] = ([m'], [p]) /\ max_prefs__M Ms z rules = (Ms', lst).
      Proof.
        intros. unfold max_prefs__M in *. simpl in *. repeat dm; repeat inj_all; subst. auto.
      Qed.

      Theorem mprefs_memo_F : forall z (rules : list sdRule) Ms Ms' lst,
          lexy_list (zip Ms (map snd rules))
          -> length Ms = length rules
          -> max_prefs__M Ms z rules = (Ms', lst)
          -> max_prefs z rules = lst.
      Proof.
        induction rules; intros.
        - destruct Ms;
            unfold max_prefs__M in H1; simpl in H1; repeat inj_all; subst; auto; discriminate.
        - destruct Ms; try(discriminate).
          assert(A0 : lexy_list (zip Ms (map snd rules))).
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
              assert(A2 : lexy m d).
              { unfold lexy_list in *. apply H. simpl. left. auto. }
              eapply mpref_memo_eq_lexy_F in A2; eauto. subst. auto.
      Qed.

    End MemoEq.

    Module Export Accessible.
      
      Lemma acc_helper__M : forall Ms code rules Ms' label o,
        lexy_list (zip Ms (map snd rules))
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
          -> lexy_list (zip Ms (map snd rules))
          -> length Ms = length rules
          -> max_of_prefs__M (max_prefs__M Ms code rules) = (Ms', label, Some (s :: l, suffix))
          -> Acc lt (length suffix).
      Proof.
        intros. eapply acc_helper__M in H0; eauto; eapply acc_recursive_call; eauto.
      Defined.
      

    End Accessible.

    Module Export Lengths.

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
      
    End Lengths.

    Module Export LexyClosure.

      Lemma nth_labels_match'' : forall m n rules Ms code Ms' l0 o ru label d label',
        m = length rules
        -> length Ms = length rules
        -> length rules = length l0
        -> length Ms' = length Ms
        -> n < length Ms'
        -> max_prefs__M Ms code rules = (Ms', l0)
        -> nth n l0 ([], None) = (label, o)
        -> nth n rules ([], defState, defDelta) = (label', ru, d)
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

      Lemma nth_labels_match' : forall m n rules Ms code Ms' l0 o ru label d label',
          m = length rules
          -> length Ms = length rules
          -> n < length Ms'
          -> max_prefs__M Ms code rules = (Ms', l0)
          -> nth n l0 ([], None) = (label, o)
          -> nth n rules ([], defState, defDelta) = (label', ru, d)
          -> label = label'.
      Proof.
        intros.
        assert(L := all_lens_const Ms rules code Ms' l0 H0 H2). destruct L.
        eapply nth_labels_match''; eauto. omega.
      Qed.

      Lemma nth_labels_match : forall n rules Ms code Ms' l0 o ru label d label',
          max_prefs__M Ms code rules = (Ms', l0)
          -> length Ms = length rules
          -> n < length Ms'
          -> nth n l0 ([], None) = (label, o)
          -> nth n rules ([], defState, defDelta) = (label', ru, d)
          -> label = label'.
      Proof.
        intros. eapply nth_labels_match'; eauto.
      Qed.

      Lemma mprefs__M_associates :
        forall n rules Ms Ms' code (l0 : list (Label * option (Prefix * Suffix))) M M' o label ru d,
          length Ms = length rules
          -> max_prefs__M Ms code rules = (Ms', l0)
          -> n < length Ms'
          -> nth n Ms emptyMemo = M
          -> nth n Ms' emptyMemo = M'
          -> nth n l0 ([], None) = (label, o)
          -> nth n rules ([], defState, defDelta) = (label, ru, d)
          -> max_pref_fn__M M code ru d = (M', o).
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

      Lemma set_Memo_lexy : forall stt0 z0 o o' z stt m d,
          max_pref_fn z stt d = o'
          -> lexy m d
          -> get_Memo (set_Memo m stt z o') stt0 z0 = Some o
          -> max_pref_fn z0 stt0 d = o.
      Proof.
        intros. destruct (String_dec z z0).
        (* originally tried to find an ordering on State *)
        (* realized that was too much, tried to find decidable equality *)
        (* seems like even that is too much, considering that 
           the Table and final states doesn't change, only the state-pointer *)
        - subst. destruct (stt_compare stt stt0) eqn:E.
          + apply stt_compare_eq in E. subst. rewrite correct_Memo in H1. inv H1. auto.
          + assert(stt <> stt0).
            { intros C. apply stt_compare_eq in C. rewrite C in *. discriminate. }
            clear E.
            assert(stt0 <> stt \/ z0 <> z0); auto.
            eapply correct_Memo_moot in H2; eauto. rewrite H2 in H1.
            eapply lexy_correct; eauto.
          + assert(stt <> stt0).
            { intros C. apply stt_compare_eq in C. rewrite C in *. discriminate. }
            clear E.
            assert(stt0 <> stt \/ z0 <> z0); auto.
            eapply correct_Memo_moot in H2; eauto. rewrite H2 in H1.
            eapply lexy_correct; eauto.
        - assert(stt0 <> stt \/ z0 <> z); auto.
          clear n. eapply correct_Memo_moot in H2; eauto. rewrite H2 in H1.
          eapply lexy_correct; eauto.
      Qed.

      Lemma lexy_closure : 
        forall code stt M o M' d,
          lexy M d
          -> max_pref_fn__M M code stt d = (M', o)
          -> lexy M' d.
      Proof.
        induction code; intros.
        {
          simpl in H0. dm; inv H0; auto.
        }
        {
          simpl in H0. repeat dm.
          - repeat inj_all. auto.
          - repeat inj_all. eapply IHcode; eauto.
          - repeat inj_all. auto.
          - repeat inj_all. eapply IHcode; eauto.
          - repeat inj_all. auto.
          - repeat inj_all. eapply IHcode; eauto.
          - repeat inj_all.
            assert(max_pref_fn code (transition a stt d) d = None).
            {
              unfold lexy in H. apply H in E3. auto.
            }
            assert(max_pref_fn (a :: code) stt d = None).
            {
              simpl. repeat dm; try discriminate.
            }
            unfold lexy. intros. clear IHcode E3 E1 E2 H0.
            eapply set_Memo_lexy; eauto.
          - repeat inj_all.
            assert(max_pref_fn code (transition a stt d) d = None).
            {
              apply mpref_memo_eq_lexy_F in E; auto.
            }
            assert(max_pref_fn (a :: code) stt d = None).
            {
              simpl. repeat dm; try discriminate.
            }
            apply IHcode in E; auto. clear H H0 E3 E1 E2 M IHcode.
            unfold lexy. intros.
            eapply set_Memo_lexy; eauto.
        }
      Qed.

      Lemma length_zip_eq : forall (A B : Type) (aas : list A) (bs : list B),
          length aas = length bs
          -> length (zip aas bs) = length aas
            /\ length (zip aas bs)= length bs.
      Proof.
        induction aas; intros; split; intros; auto.
        - destruct bs; sis; try discriminate.
          inv H. apply f_equal. apply IHaas. auto.
        - destruct bs; sis; try discriminate.
          inv H. apply f_equal. apply IHaas. auto.
      Qed.

      Lemma nth_zip : forall {A B : Type} (aas : list A) (bs : list B) n a b,
        length aas = length bs
        -> n < length aas
        -> nth n (zip aas bs) (a, b) = (nth n aas a, nth n bs b).
      Admitted.

      Lemma lexy_list_closure : 
        forall code rules Ms l0 Ms',
           lexy_list (zip Ms (map snd rules))
          -> length Ms = length rules
          -> max_prefs__M Ms code rules = (Ms', l0)
          ->  lexy_list (zip Ms' (map snd rules)).
      Proof.
        intros. unfold lexy_list in *. intros M' d H2.
        apply In_nth with (d := (emptyMemo, defDelta)) in H2. destruct H2 as [n]. destruct H2.
        assert(L := all_lens_const Ms rules code Ms' l0 H0 H1). destruct L.
        assert(exists M, nth n Ms emptyMemo = M).
        { eexists; eauto. }
        destruct H6 as [M].
        assert(exists label o, nth n l0 ([], None) = (label, o)).
        { destruct (nth n l0 ([], None)). eexists; eauto. }
        destruct H7 as [label]. destruct H7 as [o].
        assert(exists label' ru d, nth n rules ([], defState, defDelta) = (label', ru, d)).
        { destruct (nth n rules ([], defState, defDelta)). destruct p.
          repeat eexists. }
        destruct H8 as [label']. destruct H8 as [ru]. destruct H8 as [d0].
        assert(label = label').
        {
          eapply nth_labels_match; eauto.
          rewrite <- H4 in H0.
          rewrite <- map_length with (f := snd) in H0. apply length_zip_eq in H0.
          destruct H0. rewrite H0 in H2. auto.
        }
        rewrite H9 in *. clear H9.
        assert (H0' := H0).
        eapply mprefs__M_associates in H0; eauto.
        - assert (H2' := H2).
          apply nth_In with (d := (emptyMemo, defDelta)) in H2. rewrite H3 in H2.
          assert (d0 = d).
          {
            rewrite nth_zip in H3; auto.
            - inv H3.
              assert (forall (xs : Label), snd (xs, defState, defDelta) = defDelta).
              { intros. auto. }
              specialize (H3 []). rewrite <- H3.
              rewrite map_nth.
              try rewrite H8. (* why didn't that work? *)
              admit.
            - rewrite H4. rewrite map_length. auto.
            - rewrite <- H4 in H0'. symmetry in H0'.
              erewrite <- map_length in H0'. symmetry in H0'.  apply length_zip_eq in H0'.
              destruct H0'. rewrite <- H9. eauto.
          }
          assert (nth n Ms' emptyMemo = M').
          { 
            rewrite nth_zip in H3.
            - inv H3. auto.
            - rewrite H4. rewrite map_length. auto.
            - rewrite <- H4 in H0'. symmetry in H0'.
              erewrite <- map_length in H0'. symmetry in H0'.  apply length_zip_eq in H0'.
              destruct H0'. rewrite <- H10. eauto.
          }
          rewrite H10 in *. rewrite H9 in *. clear H9 H10.
          (* H8 /\ H6 -> nth n (zip Ms (map snd rules)) _ = (M, d) -> In (M, d) _ -> lexy M d *)
          assert(In (M', d) (zip Ms (map snd rules))).
          { admit. }
          apply H. auto.
        - rewrite <- H4 in H0.
          rewrite <- map_length with (f := snd) in H0. apply length_zip_eq in H0.
          destruct H0. rewrite H0 in H2. auto.
      Admitted.

      Lemma lexy_recursive_call_gen :
        forall code rules Ms label o Ms',
          lexy_list (zip Ms (map snd rules))
          -> length Ms = length rules
          -> max_of_prefs__M (max_prefs__M Ms code rules) = (Ms', label, o)
          -> lexy_list (zip Ms' (map snd rules)).
      Proof.
        intros. destruct (max_prefs__M Ms code rules) eqn:E.
        assert(l = Ms').
        {
          simpl in H1. repeat dm. injection H1; auto.
        }
        subst. clear H1.
        eapply lexy_list_closure; eauto.
      Qed.

      Lemma lexy_recursive_call :
        forall code rules Ms label s l suffix Ms',
          lexy_list (zip Ms (map snd rules))
          -> length Ms = length rules
          -> max_of_prefs__M (max_prefs__M Ms code rules) = (Ms', label, Some (s :: l, suffix))
          -> lexy_list (zip Ms' (map snd rules)).
        intros. eapply lexy_recursive_call_gen in H; eauto.
      Qed.

    End LexyClosure.
    
  End TypeCheckLemmas.

  Module Export Lex.

    Fixpoint lex'__M
             (Ms : list Memo)
             (rules : list (sdRule))
             (code : String)
             (Ha : Acc lt (length code))
             (Hlexy : lexy_list (zip Ms (map snd rules)))
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

    Definition init_sdrule (rule : Rule) : sdRule :=
      match rule with
      | (label, re) => (label, init_state re, init_delta re)
      end.

    Definition init_Memos (sdrules : list sdRule) : list Memo :=
      (map (fun x => emptyMemo) sdrules).

    Lemma lexy_list_cons : forall M Mds d,
        lexy M d -> lexy_list Mds -> lexy_list ((M,d) :: Mds).
    Proof.
      intros. unfold lexy_list in *. intros. sis. destruct H1.
      - inv H1. auto.
      - apply H0; auto.
    Qed.

    Lemma init_Memos_lexy : forall sdrules,
        lexy_list (zip (init_Memos sdrules) (map snd sdrules)).
    Proof.
      intros. induction sdrules.
      - simpl. unfold lexy_list. intros. contradiction.
      - simpl. apply lexy_list_cons; auto. unfold lexy. intros.
        rewrite correct_emptyMemo in H. discriminate.
    Qed.        

    Lemma init_Memos_parallel : forall srules,
        length (init_Memos srules) = length srules.
    Proof.
      intros. induction srules; auto. sis. omega.
    Qed.

    Definition lex__M (rules : list Rule) (code : String) : list Token * String :=
      let
        srules := map init_sdrule rules
      in
      match
        lex'__M (init_Memos srules) srules code
              (lt_wf _) (init_Memos_lexy _) (init_Memos_parallel _)
       with
       | (_, ts, rest) => (ts, rest)
       end.

  End Lex.

End ImplFn.
