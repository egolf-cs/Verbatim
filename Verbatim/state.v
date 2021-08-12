Require Import List.
Import ListNotations.

Require Import FSets FSets.FMapAVL FSets.FMapFacts.
Require Import Coq.ZArith.BinInt.

From Verbatim Require Import ltac.
From Verbatim Require Import regex.
From Verbatim Require Import Orders.


Module Type LABEL.

  Parameter Label : Type.
  Parameter defLabel : Label.
  Parameter Label_eq_dec : forall (l l' : Label), {l = l'} + {l <> l'}.

End LABEL.

Module Type STATE (Import R : regex.T).

  Import R.Ty.

  (*** Core ***)

  (* The labels for lexical rules; this should probably be defined somewhere else *)
  Parameter Label : Type.
  Parameter Label_eq_dec : forall (l l' : Label), {l = l'} + {l <> l'}.
  Parameter defLabel : Label.

  (* Pointers are like state-labels for state machines *)
  Parameter Pointer : Type.
  Parameter defPointer : Pointer.
  Parameter pointer_compare : Pointer -> Pointer -> comparison.
  Parameter pointer_compare_eq : forall x y,
      pointer_compare x y = Eq <-> x = y.
  Parameter pointer_compare_trans : forall c x y z,
      pointer_compare x y = c -> pointer_compare y z = c -> pointer_compare x z = c.

  (* Delta is some mechanism for transitioning, like a transition table *)
  Parameter Delta : Type.
  Parameter defDelta : Delta.

  (* A State tells you where you are in the machine and how to transition *)
  Definition State : Type := prod Pointer Delta.
  Definition defState : State := (defPointer, defDelta).
  

  
  (*** Index ***)
  Parameter index : Type.
  Parameter index0 : index.
  Parameter index_eq_dec : forall (i ii : index), {i = ii} + {i <> ii}.
  Parameter incr : index -> index.
  Parameter decr : index -> index.
  Parameter init_index : nat -> index.
  
  Parameter index2list : index -> list bool.
  Parameter list2index : list bool -> index.
  Parameter list_inv : forall (x : index), list2index (index2list x) = x.

  (* for index correctness *)
  Parameter decr_inv_incr : forall i, decr (incr i) = i.
  Parameter incr_inv_decr : forall i, incr (decr i) = i.
  Parameter decr_inv_S : forall n, decr (init_index (S n)) = init_index n.
  Parameter incr_is_S : forall n, init_index (S n) = incr (init_index n).
  Parameter n_det_index : forall n1 n2, init_index n1 = init_index n2 -> n1 = n2.
                                                                   

  (*** State Machine ***)
  Parameter transition : Sigma -> State -> State.
  Parameter transition_list : list Sigma -> State -> State.
  Parameter transition_list_nil : forall fsm,
      transition_list [] fsm = fsm.
  Parameter transition_list_cons : forall bs a fsm,
      transition_list (a :: bs) fsm = transition_list bs (transition a fsm).
  Parameter transition_Delta : forall a p p' d d',
      transition a (p, d) = (p', d') -> d = d'.
  
  Parameter accepts : String -> State -> bool.
  Parameter accepting : State -> bool.

  Parameter accepts_nil: forall fsm, accepting fsm = accepts [] fsm.
  Parameter accepts_transition : forall cand a fsm,
      accepts cand (transition a fsm) = accepts (a :: cand) fsm.

  Parameter init_state : regex -> State.
  Parameter init_state_inv : State -> regex.
  
  Parameter invert_init_correct : forall r s,
      exp_match s (init_state_inv (init_state r)) <-> exp_match s r.

  Parameter accepting_dt_list : forall bs e,
      accepting (transition_list bs (init_state e))
      = accepting (init_state (derivative_list bs e)).
  
  Parameter accepts_matches : forall(s : String) (e : regex),
      true = accepts s (init_state e) <-> exp_match s e.
  
End STATE.


Module DefsFn (R : regex.T) (Ty : STATE R).

  Import Ty.
  Import R.Defs.
  Import R.Ty.

  Module Pointer_as_UCT <: UsualComparableType.
    Definition t := Pointer.
    Definition compare := pointer_compare.
    Definition compare_eq := pointer_compare_eq.
    Definition compare_trans := pointer_compare_trans.

    Lemma Pointer_eq_dec : forall (x y : Pointer), {x = y} + {x <> y}.
    Proof.
      intros. destruct (pointer_compare x y) eqn:E.
      - apply pointer_compare_eq in E. auto.
      - right. intros C. apply pointer_compare_eq in C. rewrite C in *. discriminate.
      - right. intros C. apply pointer_compare_eq in C. rewrite C in *. discriminate.
    Qed.
    
  End Pointer_as_UCT.
  
  Module Export Coredefs.
    
    Definition Prefix : Type := String.
    Definition Suffix : Type := String.
    Definition Token : Type := Label * Prefix.
    Definition Rule : Type := Label * regex.

    Definition sRule : Type := Label * State.

    Inductive eq_models : State -> regex -> Prop :=
    | SReq (fsm : State) (r : regex)
           (H1 : forall(s : String), true = accepts s fsm <-> exp_match s r) :
        eq_models fsm r.
    
  End Coredefs.

  Module Export MaxMunchSpec.
    
    Inductive is_prefix : String -> String -> Prop :=
    | pref_def p s
               (H1 : exists q, p ++ q = s) :
        is_prefix p s.

    Notation "p ++_= s" := (is_prefix p s) (at level 80).

    Inductive re_no_max_pref : String -> regex -> Prop :=
    | re_MP0 (s : String) (r : regex)
             (H1 : forall cand, cand ++_= s -> ~(exp_match cand r)) :
        re_no_max_pref s r.

    Inductive re_max_pref : String -> regex -> String -> Prop :=
    | re_MP1 (s p : String) (r : regex)
             (H1 : p ++_= s)
             (H2 : exp_match p r)
             (H3 : forall(cand : String),
                 cand ++_= s
                 -> ((length cand) <= (length p)) \/ ~(exp_match cand r)) :
        re_max_pref s r p.

    Inductive no_max_pref : String -> State -> Prop :=
    | MP0 (s : String) (fsm : State)
          (H1 : exists(r : regex), eq_models fsm r /\ re_no_max_pref s r) :
        no_max_pref s fsm.

    Inductive max_pref : String -> State -> String -> Prop :=
    | MP1 (s p : String) (fsm : State)
          (H1 : exists(r : regex), eq_models fsm r /\ re_max_pref s r p) :
        max_pref s fsm p.

    (* a rule is at index 0 if it's the first element of the list.
   Otherwise a rule is at index n + 1 if it's at index n of the tail of the list *)
    Inductive at_index : Rule -> nat -> list Rule -> Prop :=
    | AI0 (ru h: Rule) (tl : list Rule)
          (Heq : ru = h) :
        at_index ru 0 (h :: tl)
    | AI1 (ru h: Rule) (n : nat) (tl : list Rule)
          (IH : at_index ru n tl) :
        at_index ru (S n) (h :: tl).

    (* n is the first index of a rule if no smaller index maps to that rule *)
    Inductive least_index : Rule -> nat -> list Rule -> Prop :=
    | LI1 (ru : Rule) (n : nat) (rus : list Rule)
          (Hat : at_index ru n rus)
          (Hnot : forall(n' : nat), n' < n -> ~(at_index ru n' rus)) :
        least_index ru n rus.

    (* A rule is "earlier" than another if its first occurrence comes before
   the first occurence of the other rule *)
    Inductive earlier_rule : Rule -> Rule -> list Rule -> Prop :=
    | ERu1 (ru1 ru2 : Rule) (rus : list Rule)
           (H : forall(n1 n2 : nat),
               least_index ru1 n1 rus
               -> least_index ru2 n2 rus
               -> n1 < n2) :
        earlier_rule ru1 ru2 rus.

    Inductive first_token : String -> (list Rule) -> Token -> Prop :=
    (* l is Token.label, p is Token.value *)
    | FT1 (code : String) (p : Prefix) (l : Label) (r : regex) (rus : list Rule)
          (Hnempt : p <> [])
          (Hex : In (l, r) rus)
          (Hmpref : re_max_pref code r p)
          (* We can't produce longer prefixes from other rules *)
          (Hout : forall(l' : Label) (r' : regex) (p' : String),
              length p' > length p
              -> re_max_pref code r' p'
              -> ~(In (l',r') rus)
          )
          (* If we can produce the prefix in some other way,
           the rule used to do so most come later in the list *)
          (Hlater : forall(r' : regex) (l' : Label),
              earlier_rule (l',r') (l, r) rus
              -> In (l', r') rus
              -> ~(re_max_pref code r' p)
          ) :
        first_token code rus (l, p).

    (* This definition accounts for inputs that could not be entirely tokenized.
   The list of tokens must match some prefix and the unprocessed suffix
   must match s1 *)
    Inductive tokenized (rus : list Rule) : String -> list Token -> String -> Prop :=
    | Tkd0 (code : String)
           (H : forall(t : Token), first_token code rus t -> snd t = []) :
        (* If no tokens can be produced from the input,
       then the input is tokenized by the empty list
       of tokens and itself *)
        tokenized rus code [] code
    | Tkd1 (p : Prefix) (s0 s1 : Suffix) (ts : list Token) (l : Label)
           (* the first token matches the input *)
           (H0 : first_token (p ++ s0 ++ s1) rus (l,p))
           (* The rest of the tokens match the rest of the input *)
           (IH : tokenized rus (s0 ++ s1) ts s1) :
        tokenized rus (p ++ s0 ++ s1) ((l, p) :: ts) s1.

    Definition rules_is_function (rus : list Rule) :=
      forall l r r', In (l, r) rus
                -> In (l, r') rus
                -> r = r'.
  End MaxMunchSpec.

  

  Module Export Corollaries.

    Lemma ru_dec : forall (ru1 ru2 : Rule), {ru1 = ru2} + {ru1 <> ru2}.
    Proof.
      intros. destruct ru1. destruct ru2.
      destruct (Label_eq_dec l l0); destruct (regex_dec r r0); subst; auto;
        right; intros C; destruct n; inv C; auto.
    Qed.

    Lemma accepting_nilmatch : forall e,
        true = accepting (init_state e)
        <-> exp_match [] e.
    Proof.
      intros. split; intros.
      - rewrite accepts_nil in H. rewrite accepts_matches in H. auto.
      - rewrite accepts_nil. rewrite accepts_matches. auto.
    Qed.

    Lemma inv_eq_model : forall(e : regex),
        eq_models (init_state e) e.
    Proof.
      intros fsm. apply SReq. intros s. rewrite accepts_matches. split; auto.
    Qed.

    (*
    Lemma inv_transition : forall cand a e,
        exp_match cand (init_state_inv (transition a (init_state e)))
        <-> exp_match (a :: cand) (init_state_inv (init_state e)).
    Proof.
      intros. repeat rewrite <- accepts_matches.
      repeat rewrite accepts_matches.
      rewrite invert_init_correct.
      rewrite accepts_transition.
      split; auto.
    Qed.*)

    Lemma invert_init_correct_max : forall r p code,
        re_max_pref code (init_state_inv (init_state r)) p
        <-> re_max_pref code r p.
    Proof.
      split; intros; inv H.
      - rewrite invert_init_correct in H2. apply re_MP1; auto.
        intros. apply H3 in H. destruct H; auto.
        right. intros C. destruct H. rewrite invert_init_correct. auto.
      - apply re_MP1; auto.
        + rewrite invert_init_correct. auto.
        + intros. apply H3 in H. destruct H; auto.
          right. intros C. destruct H. rewrite invert_init_correct in *. auto.
    Qed.

    Lemma invert_init_correct_nomax : forall r code,
        re_no_max_pref code (init_state_inv (init_state r))
        <-> re_no_max_pref code r.
    Proof.
      split; intros;
        inv H; apply re_MP0; intros; apply H1 in H;
          intros C; destruct H; apply invert_init_correct; auto.
    Qed.

  End Corollaries.
  
  
End DefsFn.


Module Type DefsT (R : regex.T) (Ty : STATE R).
  Include DefsFn R Ty.
End DefsT.

Module Type T.
  Declare Module R : regex.T.
  Declare Module Ty : STATE R.
  Declare Module Defs : DefsT R Ty.
  Export R.
  Export R.Ty.
  Export R.Defs.
  Export Ty.
  Export Defs.
End T.

