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
  Module Import IMPL := ImplFn MEM.
  Import MEM.Defs.NaiveLexerF.LEM.IMPL.Lex.
  Import MEM.Defs.NaiveLexerF.LEM.
  Import MEM.Defs.NaiveLexerF.
  Import MEM.Defs.NaiveLexer.MPref.
  Import IMPL.
  Import MEMO.

  Module Export CaseLemmas.

    Lemma lex'_eq_body__M :
      forall rules code Ms
        (Ha : Acc lt (length code))
        (Hlexy : lexy_list (zip Ms (map ssnd rules)))
        (Hlen : length Ms = length rules),
        (lex'__M Ms rules code Ha Hlexy Hlen =
         (match max_of_prefs__M (max_prefs__M Ms code rules) as mpref'
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
          end eq_refl)).
    Proof. 
      intros rules code Ha Hlexy Hlen.
      destruct Ha; destruct Hlexy; auto.
    Qed.

    Lemma lex'_cases_backward__M :
      forall (Ms : list Memo)
        (rules : list sRule)
        (code : String)
        (Ha : Acc lt (length code))
        (Hlexy : lexy_list (zip Ms (map ssnd rules)))
        (Hlen : length Ms = length rules)
        (pr : list Memo * Label * option (Prefix * Suffix))
        (res : list Memo * list Token * String)
        (Heq : max_of_prefs__M (max_prefs__M Ms code rules) = pr),
        match pr as mpref' return max_of_prefs__M (max_prefs__M Ms code rules) = mpref' -> _ with
        | (Ms', _, None) => fun _ => (Ms', [], code) (* Code cannot be processed further *)
        | (Ms', _, Some ([], _)) => fun _ => (Ms', [], code) (* Code cannot be processed further *)
        | (Ms', label, Some (h :: t, suffix)) =>
          fun Heq =>
            match (lex'__M Ms' rules suffix
                         (acc_recursive_call__M _ _ _ _ _ _ _ _ Ha Hlexy Hlen Heq)
                         (lexy_recursive_call _ _ _ _ _ _ _ _ Hlexy Hlen Heq)
                         (len_recursive_call _ _ _ _ _ _ _ _ Hlen Heq)
                  )
            with
            | (Ms'', lexemes, rest) => (Ms'', ((label, h :: t) :: lexemes), rest)
            end
        end Heq = res
        -> match res with
          | (_, [], code') =>
            code' = code
            /\ (snd (max_of_prefs__M (max_prefs__M Ms code rules)) = None
               \/ exists suf, snd (max_of_prefs__M (max_prefs__M Ms code rules)) = Some ([], suf))
          | (_, (label, prefix) :: lexemes, rest) =>
            exists Ms'' Ms' h t suffix (Heq' : max_of_prefs__M (max_prefs__M Ms code rules)
                                 = (Ms', label, Some (h :: t, suffix))),
            lex'__M Ms' rules suffix
                         (acc_recursive_call__M _ _ _ _ _ _ _ _ Ha Hlexy Hlen Heq')
                         (lexy_recursive_call _ _ _ _ _ _ _ _ Hlexy Hlen Heq')
                         (len_recursive_call _ _ _ _ _ _ _ _ Hlen Heq')
            = (Ms'', lexemes, rest)
            /\ h :: t = prefix
          end.
    Proof.
      intros.
      repeat dm; intros; subst; simpl in *; try congruence.
      - split; inv H; eauto. right. exists s. apply f_equal with (f := snd) in Heq. auto.
      - inv H. exists l3. exists l. exists s0. exists p2. exists s. exists Heq. split; auto.
      - split; inv H; eauto. left. apply f_equal with (f := snd) in Heq. auto.
    Qed.

    Lemma lex'_cases__M :
      forall Ms rules code Ha Hlexy Hlen res,
        lex'__M Ms rules code Ha Hlexy Hlen = res
        -> match res with
          | (_, [], code') =>
            code' = code
            /\ (snd (max_of_prefs__M (max_prefs__M Ms code rules)) = None
               \/ exists suf, snd (max_of_prefs__M (max_prefs__M Ms code rules)) = Some ([], suf))
          | (_, (label, prefix) :: lexemes, rest) =>
            exists Ms'' Ms' h t suffix (Heq' : max_of_prefs__M (max_prefs__M Ms code rules)
                                 = (Ms', label, Some (h :: t, suffix))),
            lex'__M Ms' rules suffix
                         (acc_recursive_call__M _ _ _ _ _ _ _ _ Ha Hlexy Hlen Heq')
                         (lexy_recursive_call _ _ _ _ _ _ _ _ Hlexy Hlen Heq')
                         (len_recursive_call _ _ _ _ _ _ _ _ Hlen Heq')
            = (Ms'', lexemes, rest)
            /\ h :: t = prefix
          end.
    Proof.
      intros; subst.
      rewrite lex'_eq_body__M.
      eapply lex'_cases_backward__M; eauto.
    Qed.

  End CaseLemmas.

  Lemma momprefs_memo_F : forall code rus l o Ms Ms' l' o',
      max_of_prefs (max_prefs code rus) = (l, o)
      -> max_of_prefs__M (max_prefs__M Ms code rus) = (Ms', l', o')
      -> lexy_list (zip Ms (map ssnd rus))
      -> length Ms = length rus
      -> (l, o) = (l', o').
  Proof.
    intros. destruct (max_prefs__M Ms code rus) eqn:E.
    apply mprefs_memo_F in E; auto.
    assert(max_prefs code rus = l1).
    {
      rewrite E. auto.
    }
    rewrite <- H3 in H0.
    sis.
    assert (Defs.NaiveLexer.MPref.max_of_prefs (max_prefs code rus)
            = max_of_prefs (max_prefs code rus)).
    {
      auto.
    }
    rewrite H3 in *. clear H3.
    destruct (max_of_prefs (max_prefs code rus)).
    destruct (Defs.NaiveLexer.MPref.max_of_prefs l1).
    inv H0. auto.
  Qed.

  Lemma lex'_memo_eq_ts : forall ts ts' code
                           (Ha Ha' : Acc lt (length code))
                           rus rest rest' iMs Ms Hlexy Hlen,
    lex' rus code Ha = (ts, rest)
    -> lex'__M iMs rus code
            Ha' Hlexy Hlen = (Ms, ts', rest')
    -> ts = ts'.
  Proof.
    induction ts; destruct ts'; auto;
    intros; apply lex'_cases in H; apply lex'_cases__M in H0.
    - exfalso. destruct t. destruct H0 as (Ms'' & Ms' & h & y & suffix & Heq' & H0).
      destruct H. destruct H1.
      + clear H0.
        destruct (max_of_prefs (max_prefs code rus)) eqn:E. simpl in H1.
        assert(MPref.max_of_prefs (MPref.max_prefs code rus)
               = max_of_prefs (max_prefs code rus)).
        { auto. }
        rewrite H0 in H1. clear H0.
        rewrite E in H1. simpl in H1. rewrite H1 in *. clear H1.
        apply momprefs_memo_F with (l := l0) (o := None) in Heq'; auto.
        discriminate.
      + clear H0.
        destruct (max_of_prefs (max_prefs code rus)) eqn:E. simpl in H1.
        destruct H1.
        assert(MPref.max_of_prefs (MPref.max_prefs code rus)
               = max_of_prefs (max_prefs code rus)).
        { auto. }
        rewrite H1 in H0. clear H1. rewrite E in H0.
        simpl in H0. rewrite H0 in *. clear H0.
        apply momprefs_memo_F with (l := l0) (o := Some ([], x)) in Heq'; auto.
        discriminate.
    - exfalso. destruct a. destruct H as (h & t & suffix & Heq' & H).
      destruct H. destruct H0. destruct H2.
      + destruct (max_of_prefs__M (max_prefs__M iMs code rus)) eqn:E.
        simpl in H2. rewrite H2 in *. clear H2.
        destruct p0.
        apply momprefs_memo_F with (l := l) (o := Some (h :: t, suffix)) in E; auto.
        discriminate.
      + destruct (max_of_prefs__M (max_prefs__M iMs code rus)) eqn:E.
        destruct H2.
        simpl in H2. rewrite H2 in *. clear H2.
        destruct p0.
        apply momprefs_memo_F with (l := l) (o := Some (h :: t, suffix)) in E; auto.
        discriminate.
    - destruct a. destruct t.
      destruct H as (h & t & suffix & Heq & Hlex' & Hp).
      destruct H0 as (Ms'' & Ms' & h0 & t0 & suffix0 & Heq0 & Hlex'0 & Hp0).
      subst.
      assert (suffix = suffix0 -> ts = ts').
      {
        intros. subst. eapply IHts; eauto.
      } 
      clear Hlex'0.
      apply momprefs_memo_F with (l := l) (o := Some (h :: t, suffix)) in Heq0; auto.
      inv Heq0. intros. subst. destruct H; reflexivity.
  Qed.

  Lemma lex'_memo_splits : forall ts' ts code (Ha Ha' : Acc lt (length code))
                           rus rest rest' iMs Ms Hlexy Hlen,
    lex' (map init_srule rus) code Ha = (ts, rest)
    -> lex'__M iMs (map init_srule rus) code
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
      destruct H0 as (Ms'' & Ms' & h0 & t0 & suffix0 & Heq0 & Hlex'0 & Hp0).
      apply lex'_cases in H. destruct t.
      destruct H as (h & t & suffix & Heq & Hlex' & Hp).
      assert(suffix = suffix0 -> code = concat (map snd ((l, p) :: ts')) ++ rest').
      {
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
      
      
  
  Lemma lex'_memo_eq_rest : forall code (Ha Ha' : Acc lt (length code))
                           ts rus rest ts' rest' iMs Ms Hlexy Hlen,
    lex' (map init_srule rus) code Ha = (ts, rest)
    -> lex'__M iMs (map init_srule rus) code
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

  Theorem lex'_memo_eq : forall code (Ha : Acc lt (length code))
                           ts rus rest ts' rest' Ms Hlexy Hlen,
    lex' (map init_srule rus) code Ha = (ts, rest)
    -> lex'__M (init_Memos (map init_srule rus)) (map init_srule rus) code
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
    destruct (lex'__M (init_Memos (map CorrectFn.IMPL.Lex.init_srule rus))
       (map CorrectFn.IMPL.Lex.init_srule rus) code (lt_wf (length code))
       (init_Memos_lexy (map CorrectFn.IMPL.Lex.init_srule rus))
       (init_Memos_parallel (map CorrectFn.IMPL.Lex.init_srule rus))) eqn:E1.
    destruct p.
    apply lex'_memo_eq with (ts := l) (rest := s) in E1; auto.
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
