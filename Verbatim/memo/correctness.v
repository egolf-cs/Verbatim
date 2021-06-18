Require Import List.
Import ListNotations.
Require Import PeanoNat.
Require Import Coq.omega.Omega.
Require Import Coq.Numbers.NatInt.NZOrder.

From Verbatim Require Import ltac.
From Verbatim Require Import memo.
From Verbatim Require Import memo.impl.

Module CorrectFn (Import MEM : memo.T).

  Import MEM.STT.Defs.
  Import MEM.Defs.
  Import MEM.Defs.Invariants.
  Module Import IMPL := ImplFn MEM.
  Import MEM.Defs.NaiveLexerF.LEM.IMPL.Lex.
  Import MEM.Defs.NaiveLexerF.LEM.
  Import MEM.Defs.NaiveLexerF.LEM.Lemmas.
  Import MEM.Defs.NaiveLexerF.
  Import MEM.Defs.NaiveLexer.MPref.
  Import IMPL.
  Import MEMO.

  Module Export CaseLemmas.

    Lemma lex'_eq_body__M :
      forall (orig : String)
        (Ms : list Memo)
        (rules : list (sRule))
        (code : String)
        (i : index)
        (Hindex : ith_suffix orig code i)
        (Ha : Acc lt (length code))
        (Hlexy : lexy_list orig (zip Ms (map ssnd rules)))
        (Hlen : length Ms = length rules),
        (lex'__M orig Ms rules code i Hindex Ha Hlexy Hlen =
         (match max_of_prefs__M (max_prefs__M Ms code i rules) as mpref'
                return max_of_prefs__M (max_prefs__M Ms code i rules) = mpref' -> _
          with
          | (Ms', _, None) => fun _ => (Ms', [], code) (* Code cannot be processed further *)
          | (Ms', _, Some ([], _, _)) => fun _ => (Ms', [], code) 
          | (Ms', label, Some (ph :: pt, suffix, i')) =>
            fun Heq =>
              let Hindex' := (index_rec_call__M _ _ _ _ _ _ _ _ _ _ _ Hlexy Hlen Heq Hindex) in
              match (lex'__M orig Ms' rules suffix i'
                       Hindex'
                       (acc_recursive_call__M _ _ _ _ _ _ _ _ _ _ _ Ha Hlexy Hlen Heq Hindex Hindex')
                       (lexy_recursive_call _ _ _ _ _ _ _ _ _ _ _ Hlexy Hlen Heq Hindex Hindex')
                       (len_recursive_call _ _ _ _ _ _ _ _ _ _ Hlen Heq)
                    )
              with
              | (Ms'', lexemes, rest) => (Ms'', ((label, ph :: pt) :: lexemes), rest)
              end
          end eq_refl)).
    Proof. 
      intros orig Ms rules code i Hindex Ha Hlexy Hlen.
      destruct Ha. auto.
    Qed.

    Lemma lex'_cases_backward__M :
      forall (orig : String)
        (Ms : list Memo)
        (rules : list (sRule))
        (code : String)
        (i : index)
        (Hindex : ith_suffix orig code i)
        (Ha : Acc lt (length code))
        (Hlexy : lexy_list orig (zip Ms (map ssnd rules)))
        (Hlen : length Ms = length rules)
        (pr : list Memo * Label * option (Prefix * Suffix * index))
        (res : list Memo * list Token * String)
        (Heq : max_of_prefs__M (max_prefs__M Ms code i rules) = pr),
        match pr as mpref' return max_of_prefs__M (max_prefs__M Ms code i rules) = mpref' -> _ with
        | (Ms', _, None) => fun _ => (Ms', [], code) (* Code cannot be processed further *)
        | (Ms', _, Some ([], _, _)) => fun _ => (Ms', [], code)
        | (Ms', label, Some (h :: t, suffix, i')) =>
          fun Heq =>
            let Hindex' := (index_rec_call__M _ _ _ _ _ _ _ _ _ _ _ Hlexy Hlen Heq Hindex) in
            match (lex'__M orig Ms' rules suffix i'
                         Hindex'
                         (acc_recursive_call__M _ _ _ _ _ _ _ _ _ _ _
                                              Ha Hlexy Hlen Heq Hindex Hindex')
                         (lexy_recursive_call _ _ _ _ _ _ _ _ _ _ _ Hlexy Hlen Heq Hindex Hindex')
                         (len_recursive_call _ _ _ _ _ _ _ _ _ _ Hlen Heq)
                  )
            with
            | (Ms'', lexemes, rest) => (Ms'', ((label, h :: t) :: lexemes), rest)
            end
        end Heq = res
        -> match res with
          | (_, [], code') =>
            code' = code
            /\ (snd (max_of_prefs__M (max_prefs__M Ms code i rules)) = None
               \/ exists suf, snd (max_of_prefs__M (max_prefs__M Ms code i rules))
                        = Some ([], suf, init_index (length suf)))
          | (_, (label, prefix) :: lexemes, rest) =>
            exists Ms'' Ms' h t suffix i' Hindex'
              (Heq' : max_of_prefs__M (max_prefs__M Ms code i rules)
                      = (Ms', label, Some (h :: t, suffix, i'))),
            lex'__M orig Ms' rules suffix i'
                  Hindex'
                  (acc_recursive_call__M _ _ _ _ _ _ _ _ _ _ _
                                       Ha Hlexy Hlen Heq' Hindex Hindex')
                  (lexy_recursive_call _ _ _ _ _ _ _ _ _ _ _ Hlexy Hlen Heq' Hindex Hindex')
                  (len_recursive_call _ _ _ _ _ _ _ _ _ _ Hlen Heq')
            = (Ms'', lexemes, rest)
            /\ h :: t = prefix
          end.
    Proof.
      intros.
      repeat dm; intros; subst; simpl in *; try congruence.
      - split; inv H; eauto. right. exists s.
        assert(i0 = init_index (length s)).
        {
          eapply index_rec_call__M_gen in Heq; eauto. inv Heq. auto.
        } 
        rewrite H in *.
        apply f_equal with (f := snd) in Heq. auto.
      - repeat dm. inv H.
      - repeat dm. inv H. exists l1. exists l. exists s0. exists p3. exists s. exists i0.
        exists (index_rec_call__M code rules Ms l4 s0 p3 s l i i0 orig Hlexy Hlen Heq Hindex).
        exists Heq. split; auto.
      - split; inv H; eauto. left. apply f_equal with (f := snd) in Heq. auto.
    Qed.

    Lemma lex'_cases__M :
      forall Ms rules code orig  i Hindex Ha Hlexy Hlen res,
        lex'__M orig Ms rules code i Hindex Ha Hlexy Hlen = res
        -> match res with
          | (_, [], code') =>
            code' = code
            /\ (snd (max_of_prefs__M (max_prefs__M Ms code i rules)) = None
               \/ exists suf, snd (max_of_prefs__M (max_prefs__M Ms code i rules))
                        = Some ([], suf, init_index (length suf)))
          | (_, (label, prefix) :: lexemes, rest) =>
            exists Ms'' Ms' h t suffix i' Hindex'
              (Heq' : max_of_prefs__M (max_prefs__M Ms code i rules)
                      = (Ms', label, Some (h :: t, suffix, i'))),
            lex'__M orig Ms' rules suffix i'
                  Hindex'
                  (acc_recursive_call__M _ _ _ _ _ _ _ _ _ _ _
                                       Ha Hlexy Hlen Heq' Hindex Hindex')
                  (lexy_recursive_call _ _ _ _ _ _ _ _ _ _ _ Hlexy Hlen Heq' Hindex Hindex')
                  (len_recursive_call _ _ _ _ _ _ _ _ _ _ Hlen Heq')
            = (Ms'', lexemes, rest)
            /\ h :: t = prefix
          end.
    Proof.
      intros; subst.
      rewrite lex'_eq_body__M.
      eapply lex'_cases_backward__M; eauto.
    Qed.

  End CaseLemmas.

  Lemma momprefs_memo_F : forall code rus l o Ms Ms' l' o' orig i,
      max_of_prefs (max_prefs code i rus) = (l, o)
      -> max_of_prefs__M (max_prefs__M Ms code i rus) = (Ms', l', o')
      -> lexy_list orig (zip Ms (map ssnd rus))
      -> length Ms = length rus
      -> ith_suffix orig code i
      -> (l, o) = (l', o').
  Proof.
    intros. destruct (max_prefs__M Ms code i rus) eqn:E.
    eapply mprefs_memo_F in E; eauto.
    assert(A : max_prefs code i rus = l1).
    {
      auto.
    }
    rewrite <- A in H0.
    sis.
    assert (A0 : Defs.NaiveLexer.MPref.max_of_prefs (max_prefs code i rus)
            = max_of_prefs (max_prefs code i rus)).
    {
      auto.
    }
    rewrite A in *. clear A.
    destruct (max_of_prefs (max_prefs code i rus)).
    destruct (Defs.NaiveLexer.MPref.max_of_prefs l1).
    inv H0. rewrite H in *. auto.
  Qed.

  Lemma lex'_memo_eq_ts : forall ts ts' code orig i Hindex Hindex'
                           (Ha Ha' : Acc lt (length code))
                           rus rest rest' iMs Ms Hlexy Hlen,
    lex' rus code i Hindex Ha = (ts, rest)
    -> lex'__M orig iMs rus code i Hindex'
            Ha' Hlexy Hlen = (Ms, ts', rest')
    -> ts = ts'.
  Proof.
    induction ts; destruct ts'; auto;
    intros; apply lex'_cases in H; apply lex'_cases__M in H0.
    - exfalso. destruct t. destruct H0 as (Ms'' & Ms' & h & y & suffix & i' & Hindex0 & Heq' & H0).
      destruct H. destruct H1.
      + clear H0.
        destruct (max_of_prefs (max_prefs code i rus)) eqn:E. simpl in H1.
        rewrite H1 in *.
        eapply momprefs_memo_F with (l := l0) (o := None) in Heq'; eauto.
        discriminate.
      + clear H0.
        destruct (max_of_prefs (max_prefs code i rus)) eqn:E. simpl in H1.
        destruct H1. destruct H0.
        eapply momprefs_memo_F in Heq'; eauto.
        rewrite H0 in *. discriminate.
    - exfalso. destruct a. destruct H as (h & t & suffix & i' & Heq' & H).
      destruct H. destruct H0. destruct H2.
      + destruct (max_of_prefs__M (max_prefs__M iMs code i rus)) eqn:E.
        simpl in H2. rewrite H2 in *. clear H2.
        destruct p0.
        eapply momprefs_memo_F in E; eauto.
        discriminate.
      + destruct (max_of_prefs__M (max_prefs__M iMs code i rus)) eqn:E.
        destruct H2.
        simpl in H2. rewrite H2 in *. clear H2.
        destruct p0.
        eapply momprefs_memo_F in E; eauto.
        discriminate.
    - destruct a. destruct t.
      destruct H as (h & t & suffix & i' & Heq & Hlex' & Hp).
      destruct H0 as (Ms'' & Ms' & h0 & t0 & suffix0 & i0 & Hindex'0 & Heq0 & Hlex'0 & Hp0).
      subst.
      assert (suffix = suffix0 -> ts = ts').
      {
        assert(i' = i0).
        { clear Hlex'. eapply momprefs_memo_F in Heq; eauto. repeat inj_all. auto. }
        intros. subst. eapply IHts; eauto.
      } 
      clear Hlex'0.
      eapply momprefs_memo_F in Heq0; eauto.
      inv Heq0. intros. subst. destruct H; reflexivity.
  Qed.

  Lemma lex'_memo_splits : forall ts' ts code orig i Hindex Hindex__M (Ha Ha' : Acc lt (length code))
                           rus rest rest' iMs Ms Hlexy Hlen,
    lex' (map init_srule rus) code i Hindex Ha = (ts, rest)
    -> lex'__M orig iMs (map init_srule rus) code i Hindex__M
         Ha' Hlexy Hlen = (Ms, ts', rest')
    -> code = (concat (map snd ts')) ++ rest'.
  Proof.
    induction ts'; destruct ts; intros.
    {
      simpl. apply lex'_cases__M in H0. destruct H0. auto.
    }
    {
      eapply lex'_memo_eq_ts in H; eauto. discriminate.
    }
    {
      eapply lex'_memo_eq_ts in H; eauto. discriminate.
    } 
    {
      apply lex'_cases__M in H0. destruct a.
      destruct H0 as (Ms'' & Ms' & h0 & t0 & suffix0 & i' & Hindex' & Heq0 & Hlex'0 & Hp0).
      apply lex'_cases in H. destruct t.
      destruct H as (h & t & suffix & i0 & Heq & Hlex' & Hp).
      assert(suffix = suffix0 -> code = concat (map snd ((l, p) :: ts')) ++ rest').
      {
        assert(i0 = i').
        { clear Hlex'. eapply momprefs_memo_F in Heq; eauto. repeat inj_all. auto. }
        subst i0.
        intros. subst. eapply IHts' in Hlex'0; eauto.
        simpl. rewrite <- app_assoc. rewrite <- Hlex'0.
        eapply momprefs_memo_F in Heq0; eauto. clear Hlex'0. inv Heq0.
        clear Hlex'. apply exists_rus_of_mpref in Heq. destruct Heq. destruct H.
        symmetry in H0. apply max_pref_fn_splits in H0. auto.
      }
      apply H. clear Hlex' Hlex'0 H. eapply momprefs_memo_F in Heq; eauto.
      inv Heq. auto.
    }
    Qed.
      
      
  
  Lemma lex'_memo_eq_rest : forall code orig i Hindex Hindex' (Ha Ha' : Acc lt (length code))
                           ts rus rest ts' rest' iMs Ms Hlexy Hlen,
    lex' (map init_srule rus) code i Hindex Ha = (ts, rest)
    -> lex'__M orig iMs (map init_srule rus) code i Hindex'
         Ha' Hlexy Hlen = (Ms, ts', rest')
    -> rest = rest'.
  Proof.
    intros.
    assert (ts = ts').
    {
      eapply lex'_memo_eq_ts; eauto.
    }
    subst.
    eapply lex'_memo_splits in H0; eauto. apply lex'_splits in H.
    rewrite H in *. apply app_inv_head in H0. auto.
  Qed.

  Theorem lex'_memo_eq : forall code orig i Hindex Hindex' (Ha : Acc lt (length code))
                           ts rus rest ts' rest' Ms Hlexy Hlen,
    lex' (map init_srule rus) code i Hindex Ha = (ts, rest)
    -> lex'__M orig (init_Memos (map init_srule rus)) (map init_srule rus) code i Hindex'
         Ha Hlexy Hlen = (Ms, ts', rest')
    -> (ts, rest) = (ts', rest').
  Proof.
    intros.
    assert(ts = ts').
    { eapply lex'_memo_eq_ts with (ts := ts) (rest := rest) in H0; eauto. }
    assert(rest = rest').
    { eapply lex'_memo_eq_rest with (ts := ts) (rest := rest) in H0; eauto. }
    subst. auto.
  Qed.
    

  Theorem lex_memo_eq : forall rus code,
      lex__M rus code = lex rus code.
  Proof.
    intros. destruct (lex rus code) eqn:E.
    unfold lex__M. unfold lex in E.
    repeat dm.
    destruct p.
    eapply lex'_memo_eq in E0; eauto.
  Qed.

  Theorem lex_sound__M : forall ts code rest rus,
      lex__M rus code = (ts, rest)
      -> rules_is_function rus
      -> tokenized rus code ts rest.
  Proof.
    intros. rewrite lex_memo_eq in *. apply lex_sound; auto.
  Qed.

  Theorem lex_complete__M : forall ts code rest rus,
      tokenized rus code ts rest
      -> rules_is_function rus
      -> lex__M rus code = (ts, rest).
  Proof.
    intros. rewrite lex_memo_eq in *. apply lex_complete; auto.
  Qed.
  
End CorrectFn.
