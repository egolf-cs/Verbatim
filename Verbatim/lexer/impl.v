Require Import List.
Import ListNotations.
Require Import PeanoNat.
Require Import Coq.omega.Omega.
Require Import Coq.Numbers.NatInt.NZOrder.

From Verbatim Require Import ltac.
From Verbatim Require Import state.

Module ImplFn (Import ST : state.T).

  Import ST.Ty.
  Import ST.Defs.
  
  Module Import MPref.
    
    Fixpoint max_pref_fn (s : String) (state : State) (d : Delta)
    : option (Prefix * Suffix):=
      match s with
      (* in a regex approach, accepting := nullable *)
      | [] => if accepting state d then Some ([],[]) else None
      | a :: s' =>
        let
          (* in a regex approach, transition := derivative *)
          state' := transition a state d in
        let
          mpxs := max_pref_fn s' state' d in

        match mpxs with
        | None => if (accepting state' d) then Some ([a], s') else
                   if (accepting state d) then Some ([], s) else
                     None
        | Some (p, q) => Some (a :: p, q)
        end
      end.

    Definition extract_fsm_for_max (code : String)
               (sru : (Label * State * Delta)) :=
      match sru with
        (a, fsm, d) => (a, max_pref_fn code fsm d)
      end.

    Definition max_prefs (code : String)
               (erules : list (Label * State * Delta))
      :=
      map (extract_fsm_for_max code) erules.

    (* prefixes closest to the head are preferred *)
    Definition longer_pref (apref1 apref2 : Label * (option (Prefix * Suffix)))
      : Label * (option (Prefix * Suffix)) :=
      match apref1, apref2 with
      | (_, None), (_, _) => apref2
      | (_, _), (_, None) => apref1
      (* This is finding the min right now... *)
      | (_, Some (x, _)), (_, Some (y, _)) => if (length x) =? (length y)
                                             then apref1 else
                                               if (length x) <? (length y)
                                               then apref2 else apref1
      end.

    
    Fixpoint max_of_prefs (mprefs : list (Label * (option (Prefix * Suffix))))
      : Label * option (Prefix * Suffix) :=
      match mprefs with
      | [] => ([], @None (String * String))
      | p :: ps => longer_pref p (max_of_prefs ps)
      end.

  End MPref.

  Module Export TypeCheckLemmas.
    
    Lemma max_pref_fn_splits : forall code prefix suffix (fsm : State) d,
      Some (prefix, suffix) = max_pref_fn code fsm d -> code = prefix ++ suffix.
    Proof.
      induction code as [| a s']; intros; simpl in H;
        repeat dm; repeat inj_all; auto; try(discriminate).
      symmetry in E. apply IHs' in E. rewrite E. auto.
    Qed.

    Lemma proper_suffix_shorter : forall code prefix suffix (fsm : State) d,
        prefix <> []
        -> Some (prefix, suffix) = max_pref_fn code fsm d
        -> length suffix < length code.
    Proof.
      intros code prefix suffix fsm d. intros Hneq Heq.
      apply max_pref_fn_splits in Heq. rewrite Heq.
      replace (length (prefix ++ suffix)) with ((length prefix) + (length suffix)).
      - apply Nat.lt_add_pos_l. destruct prefix.
        + contradiction.
        + simpl. omega.
      - symmetry. apply app_length.
    Qed.

    Lemma max_first_or_rest : forall ys x y,
        x = max_of_prefs (y :: ys) -> x = y \/ x = max_of_prefs ys.
    Proof.
      intros. simpl in H. unfold longer_pref in H. repeat dm.
    Qed.
    
  End TypeCheckLemmas.

  
  Module Export Lex.
    
    Lemma acc_recursive_call :
      forall code rules label s l suffix,
        Acc lt (length code)
        -> max_of_prefs (max_prefs code rules) = (label, Some (s :: l, suffix))
        -> Acc lt (length suffix).
    Proof.
      intros code rules label s l suffix Ha Heq.
      apply Acc_inv with (x := length code).
      - apply Ha.
      - assert(A2 : exists(fsm : State) d, Some (s :: l, suffix)
                                    = max_pref_fn code fsm d).
        {
          induction rules.
          - simpl in Heq. discriminate.
          - symmetry in Heq. apply max_first_or_rest in Heq. destruct Heq.
            + destruct a. simpl in H.
              destruct p. do 2 eexists. injection H; intros; subst. apply H0.
            + apply IHrules. destruct rules.
              * simpl in H. discriminate.
              * rewrite H. reflexivity.
        }
        assert(A3 : s :: l <> []).
        { intros C. discriminate. }
        destruct A2 as (fsm & d & A2).
        eapply proper_suffix_shorter with (suffix := suffix) (code := code)
                                         (fsm := fsm) in A3; eauto.
    Defined.

    Fixpoint lex'
             (rules : list sdRule)
             (code : String)
             (Ha : Acc lt (length code))
             {struct Ha} : (list Token) * String :=
      match max_of_prefs (max_prefs code rules) as mpref'
            return max_of_prefs (max_prefs code rules) = mpref' -> _
      with
      | (_, None) => fun _ => ([], code) (* Code cannot be processed further *)
      | (_, Some ([], _)) => fun _ => ([], code) (* Code cannot be processed further *)
      | (label, Some (ph :: pt, suffix)) =>
        fun Heq =>
          match (lex' rules suffix
                      (acc_recursive_call _ _ _ _ _ _ Ha Heq)) with
          | (lexemes, rest) => (((label, ph :: pt) :: lexemes), rest)
          end
      end eq_refl.
    (**)

    Definition init_sdrule (rule : Rule) : sdRule :=
      match rule with
      | (label, re) => (label, init_state re, init_delta re)
      end.

    Definition lex (rules : list Rule) (code : String) :=
      let
        srules := map init_sdrule rules
      in
      lex' srules code (lt_wf _).
    
  End Lex.

End ImplFn.
