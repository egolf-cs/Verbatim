From Verbatim Require Import state.
Require Import List.
Import ListNotations.

From Verbatim Require Import ltac.



Module Type LEXER (STT : state.T).

  Export STT.Defs.
  Export STT.R.Defs.
  Export STT.Ty.

  Parameter lex : list Rule -> String -> list Token * String.
  
  Parameter lex_sound :  forall ts code rest rus,
      lex rus code = (ts, rest)
      -> rules_is_function rus
      -> tokenized rus code ts rest.
  
  Parameter lex_complete : forall ts code rest rus,
      tokenized rus code ts rest
      -> rules_is_function rus
      -> lex rus code = (ts, rest).

End LEXER.

Module Type SEM_USER (Import STT : state.T).

  Import STT.R.Defs.
  Import STT.R.
  Import STT.Defs.
  Import STT.Ty.
  
  Parameter sem_ty : Label -> Type.
  Parameter apply_sem : (Label * String) -> option {l : Label & sem_ty l}.
  Parameter label_carries : forall l l' s t,
      apply_sem (l, s) = Some (existT _ l' t)
      -> l = l'.

End SEM_USER.

Module SemLexerFn (STT : state.T) (Export LXR : LEXER STT) (Import USER : SEM_USER STT).

  
  Module Import Core.
    
    Definition sem_token := {l : Label & sem_ty l}.

  End Core. 

  Module Import Spec.
      
    Inductive tokenized_sem' (rus : list Rule) : String -> (list (option sem_token))
                                                -> String -> Prop :=
    | Tkd_sem'_Nil (code : String)
               (H : tokenized rus code [] code)
      : tokenized_sem' rus code [] code
    | Tkd_sem'_Cons (t : option sem_token) (ts : list (option sem_token))
               (l : Label) (p : Prefix) (s0 s1 : Suffix)
               (Hsem : apply_sem (l, p) = t)
               (* the first token matches the input *)
               (H0 : first_token (p ++ s0 ++ s1) rus (l,p))
               (* The rest of the tokens match the rest of the input *)
               (IH : tokenized_sem' rus (s0 ++ s1) ts s1) :
        tokenized_sem' rus (p ++ s0 ++ s1) (t :: ts) s1.

    Inductive tokenized_sem (rus : list Rule) : String -> (option (list sem_token))
                                                -> String -> Prop :=
      (* The Some case really needs some work, probably another predicate *)
    | Tkd_sem_Some (code rest : String) (ts : list Token) (sts : list sem_token)
                   (n : nat) (st st' : sem_token) (t : Token)
                   (H0 : tokenized rus code ts rest)
                   (H3 : (nth_error ts n = Some t
                         /\ nth_error sts n = Some st)
                         -> (apply_sem t = Some st' /\ st = st'))
                   (H6 : length ts = length sts)
      : tokenized_sem rus code (Some sts) rest
    | Tkd_sem_None (code rest : String) (t : Token) (ts : list Token)
        (H : tokenized rus code ts rest)
        (Hin : In t ts)
        (Hsem : apply_sem t = None)
      : tokenized_sem rus code None rest.
    
  End Spec.

  Module Import Impl.

    Definition lex_sem' (rus : list Rule) (code : String) : (list (option sem_token)) * String :=
      match lex rus code with
      | (ts, rest) => ((map apply_sem ts), rest)
      end.

    Fixpoint lo2ol {A : Type} (xs : list (option A)) : option (list A) :=
      match xs with
      | [] => Some []
      | None :: ys => None
      | Some x :: ys =>
        match lo2ol ys with
        | None => None
        | Some zs => Some (x :: zs)
        end
      end.

    Definition lex_sem (rus : list Rule) (code : String) : (option (list sem_token)) * String :=
      match lex_sem' rus code with
      | (ts, rest) => (lo2ol ts, rest)
      end.

  End Impl.

  Module Correct.

    Theorem lex_sem_sound : forall o code rest rus,
      lex_sem rus code = (o, rest)
      -> rules_is_function rus
      -> tokenized_sem rus code o rest.
    Proof.
      intros. destruct o.
      {
        unfold lex_sem in *. unfold lex_sem' in *. repeat dm. repeat inj_all.
        eapply Tkd_sem_Some; eauto.
        - eapply lex_sound; eauto.
        - Abort.

  End Correct.

End SemLexerFn.
  
