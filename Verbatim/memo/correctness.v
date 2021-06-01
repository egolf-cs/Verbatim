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
  Import MEM.Defs.NaiveLexerF.
  Import LEM.IMPL.Lex.
  Import LEM.
  Import IMPL.
  Import MEMO.

  Module Export CaseLemmas.

    Lemma lex'_eq_body__M :
      forall rules code Ms
        (Ha : Acc lt (length code))
        (Hlexy : lexy_list Ms)
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
      intros rules code Ha Hlexy Hlen. unfold lex'.
      destruct Ha; destruct Hlexy; auto.
    Qed.

    (*
    Lemma lex'_cases_backward__M :
      forall (Ms : list Memo)
        (rules : list sRule)
        (code : String)
        (Ha : Acc lt (length code))
        (Hlexy : lexy_list Ms)
        (Hlen : length Ms = length rules)
        (pr : list Memo * Label * option (Prefix * Suffix))
        (res : list Memo * list Token * String)
        (Heq : max_of_prefs__M (max_prefs__M Ms code rules) = pr),
        match pr as mpref' return max_of_prefs__M (max_prefs__M Ms code rules) = mpref' -> _ with
        | (Ms', _, None) => fun _ => ([], code) (* Code cannot be processed further *)
        | (Ms', _, Some ([], _)) => fun _ => ([], code) (* Code cannot be processed further *)
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
        end Heq = res.
                        (*
        -> match res with
          | ([], code') =>
            code' = code
            /\ (snd pr = None
               \/ exists suf, snd pr = Some ([], suf))
          | ((label, prefix) :: lexemes, rest) =>
            exists h t suffix (Heq' : max_of_prefs (max_prefs code rules) = (label, Some (h :: t, suffix))),
            lex' rules suffix (acc_recursive_call _ _ _ _ _ _ Ha Heq') = (lexemes, rest)
            /\ h :: t = prefix
          end
          end*).
    Proof.
      intros rules code Ha pr res Heq.
      repeat dm; intros; subst; simpl in *; try congruence.
      - split; inv H; eauto.
      - inv H. exists s0. exists p1. exists s. exists Heq. split. apply E3. reflexivity.
      - split; inv H; eauto.
    Qed.*)

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
    (*
    Proof.
      intros rules code Ha res Heq; subst.
      rewrite lex'_eq_body.
      eapply lex'_cases_backward; eauto.
    Qed.*)
    Admitted.

  End CaseLemmas.

  Lemma momprefs_memo_F : forall code rus l o Ms' l' o',
      max_of_prefs (max_prefs code rus) = (l, o)
      -> max_of_prefs__M (max_prefs__M (init_Memos rus) code rus) = (Ms', l', o')
      -> (l, o) = (l', o').
  Admitted.

  Lemma lex'_memo_eq_ts : forall code (Ha : Acc lt (length code))
                           ts rus rest ts' rest' Ms Hlexy Hlen,
    lex' rus code Ha = (ts, rest)
    -> lex'__M (init_Memos rus) rus code
         Ha Hlexy Hlen = (Ms, ts', rest')
    -> ts = ts'.
  Proof.
    intros. apply lex'_cases in H. apply lex'_cases__M in H0.
    destruct ts; destruct ts'; auto.
    - exfalso. destruct t. destruct H0 as (Ms'' & Ms' & h & y & suffix & Heq' & H0).
      destruct H. destruct H1.
      + clear H0.
        destruct (max_of_prefs (max_prefs code rus)) eqn:E. simpl in H1. rewrite H1 in *. clear H1.
        apply momprefs_memo_F with (l := l0) (o := None) in Heq'; auto.
        discriminate.
      + clear H0.
        destruct (max_of_prefs (max_prefs code rus)) eqn:E. simpl in H1.
        destruct H1. rewrite H0 in *. clear H0.
        apply momprefs_memo_F with (l := l0) (o := Some ([], x)) in Heq'; auto.
        discriminate.
    - exfalso. destruct t. destruct H as (h & t & suffix & Heq' & H).
      destruct H. destruct H0. destruct H2.
      + destruct (max_of_prefs__M (max_prefs__M (init_Memos rus) code rus)) eqn:E.
        simpl in H2. rewrite H2 in *. clear H2.
        destruct p0.
        apply momprefs_memo_F with (l := l) (o := Some (h :: t, suffix)) in E; auto.
        discriminate.
      + destruct (max_of_prefs__M (max_prefs__M (init_Memos rus) code rus)) eqn:E.
        destruct H2.
        simpl in H2. rewrite H2 in *. clear H2.
        destruct p0.
        apply momprefs_memo_F with (l := l) (o := Some (h :: t, suffix)) in E; auto.
        discriminate.
    - destruct t. destruct t0.
      destruct H as (h & t & suffix & Heq & Hlex' & Hp).
      destruct H0 as (Ms'' & Ms' & h0 & t0 & suffix0 & Heq0 & Hlex'0 & Hp0).
      subst.
      clear Hlex'0. (** <--- watch out for this **)
      apply momprefs_memo_F with (l := l) (o := Some (h :: t, suffix)) in Heq0; auto.
      injection Heq0. intros. subst.
      (** either need induction or need Hlex'0; pretty close though  **)
      admit.
  Admitted.
  
  Lemma lex'_memo_eq_rest : forall code (Ha : Acc lt (length code))
                           ts rus rest ts' rest' Ms Hlexy Hlen,
    lex' rus code Ha = (ts, rest)
    -> lex'__M (init_Memos rus) rus code
         Ha Hlexy Hlen = (Ms, ts', rest')
    -> rest = rest'.
    (** this will probably be similar to eq_ts above **)
  Admitted.

  Theorem lex'_memo_eq : forall code (Ha : Acc lt (length code))
                           ts rus rest ts' rest' Ms Hlexy Hlen,
    lex' rus code Ha = (ts, rest)
    -> lex'__M (init_Memos rus) rus code
         Ha Hlexy Hlen = (Ms, ts', rest')
    -> (ts, rest) = (ts', rest').
  Proof.
    intros.
    assert(ts = ts').
    { apply lex'_memo_eq_ts with (ts := ts) (rest := rest) in H0; auto. }
    assert(rest = rest').
    { apply lex'_memo_eq_rest with (ts := ts) (rest := rest) in H0; auto. }
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
