Require Import List.
Import ListNotations.
Require Import PeanoNat.
Require Import Coq.omega.Omega.
Require Import Coq.Numbers.NatInt.NZOrder.

From Verbatim Require Import ltac.
From Verbatim Require Import state.
From Verbatim Require Import lemmas_pref.
From Verbatim Require Import impl_pref.

Module ImplFn (Import ST : state.T).

  Import ST.Ty.
  Import ST.Defs.
  Module LEM := lemmas_pref.LemmasFn ST.
  Import LEM.
  Import LEM.IMPL.
  

  Module Export Lex.
    
    Lemma acc_recursive_call :
      forall code rules label s l suffix i i',
        Acc lt (length code)
        -> max_of_prefs (max_prefs code i rules) = (label, Some (s :: l, suffix, i'))
        -> Acc lt (length suffix).
    Proof.
      intros code rules label s l suffix i i' Ha Heq.
      apply Acc_inv with (x := length code).
      - apply Ha.
      - assert(A2 : exists(fsm : State), Some (s :: l, suffix, i')
                                    = max_pref_fn code i fsm).
        {
          induction rules.
          - simpl in Heq. discriminate.
          - symmetry in Heq. apply max_first_or_rest in Heq. destruct Heq.
            + destruct a. simpl in H. exists s0. injection H; intros; subst. apply H0.
            + apply IHrules. destruct rules.
              * simpl in H. discriminate.
              * rewrite H. reflexivity.
        }
        assert(A3 : s :: l <> []).
        { intros C. discriminate. }
        destruct A2 as (fsm & A2).
        eapply proper_suffix_shorter with (suffix := suffix) (code := code)
                                         (fsm := fsm) in A3; eauto.
    Defined.


    Lemma index_rec_call_gen : forall code rules i suffix i' z label,
        i = init_index (length code)
        -> max_of_prefs (max_prefs code i rules) = (label, Some (z, suffix, i'))
        -> i' = init_index (length suffix).
    Proof.
      intros.
      rewrite H in *. apply exists_rus_of_mpref_gen in H0. destruct H0 as (r & Hin & E2).
      symmetry in E2. apply index_closure_gen in E2. auto.
    Qed.


    Lemma index_rec_call : forall rules code i suffix i' ph pt label,
        i = init_index (length code)
        -> max_of_prefs (max_prefs code i rules) = (label, Some (ph :: pt, suffix, i'))
        -> i' = init_index (length suffix).
    Proof.
      intros. eapply index_rec_call_gen; eauto.
    Defined.

    Fixpoint lex'
             (rules : list sRule)
             (code : String)
             (i : index)
             (Hindex : i = init_index (length code))
             (Ha : Acc lt (length code))
             {struct Ha} : (list Token) * String :=
      match max_of_prefs (max_prefs code i rules) as mpref'
            return max_of_prefs (max_prefs code i rules) = mpref' -> _
      with
      | (_, None) => fun _ => ([], code) (* Code cannot be processed further *)
      | (_, Some ([], _, _)) => fun _ => ([], code) (* Code cannot be processed further *)
      | (label, Some (ph :: pt, suffix, i')) =>
        fun Heq =>
          match (lex' rules suffix i'
                      (index_rec_call _ _ _ _ _ _ _ _ Hindex Heq)
                      (acc_recursive_call _ _ _ _ _ _ _ _ Ha Heq)) with
          | (lexemes, rest) => (((label, ph :: pt) :: lexemes), rest)
          end
      end eq_refl.
    (**)

    Definition lex (rules : list Rule) (code : String) :=
      let
        srules := map init_srule rules
      in
      lex' srules code (init_index (length code)) eq_refl (lt_wf _).

  End Lex.

End ImplFn.
