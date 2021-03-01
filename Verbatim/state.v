Require Import List.
Import ListNotations.

From Verbatim Require Import ltac.
From Verbatim Require Import regex.


Module Type STATE (Import R : regex.T).

  Import R.Ty.

  Parameter State : Type.
  Parameter defState : State.
  
  Parameter transition : Sigma -> State -> State.
  
  Fixpoint transition_list (bs : list Sigma) (fsm : State) : State :=
    match bs with
    | [] => fsm
    | c :: cs => transition_list cs (transition c fsm)
    end.
  
  Parameter accepts : String -> State -> bool.
  Parameter accepting : State -> bool.

  Parameter accepts_nil: forall(fsm : State), accepting fsm = accepts [] fsm.
  Parameter accepts_transition : forall cand a fsm,
      accepts cand (transition a fsm) = accepts (a :: cand) fsm.

  Parameter init_state : regex -> State.
  Parameter init_state_inv : State -> regex.
  
  Parameter invert_init_correct : forall r s,
      exp_match s (init_state_inv (init_state r)) <-> exp_match s r.

  Parameter accepting_dt_list : forall bs e,
      accepting (transition_list bs (init_state e)) = accepting (init_state (derivative_list bs e)).
  
  Parameter accepts_matches : forall(s : String) (e : regex),
    true = accepts s (init_state e) <-> exp_match s e.

End STATE.

Module DefsFn (R : regex.T) (Ty : STATE R).

  Import Ty.
  Import R.Defs.
  Import R.Ty.
  
  Module Export Coredefs.
    
    Definition Label : Type := String.
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
          (Hout : forall(l' : String) (r' : regex) (p' : String),
              length p' > length p
              -> re_max_pref code r' p'
              -> ~(In (l',r') rus)
          )
          (* If we can produce the prefix in some other way,
           the rule used to do so most come later in the list *)
          (Hlater : forall(r' : regex) (l' : String),
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
      destruct (String_dec l l0); destruct (regex_dec r r0); subst; auto;
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

