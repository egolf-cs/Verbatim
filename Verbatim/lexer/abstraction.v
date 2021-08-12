From Verbatim Require Import state.

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
