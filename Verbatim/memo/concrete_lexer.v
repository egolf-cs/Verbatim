From Verbatim Require Import regex.
From Verbatim Require Import state.
From Verbatim Require Import concrete_state.
From Verbatim Require Import memo.
From Verbatim Require Import memo.impl.
From Verbatim Require Import memo.correctness.
From Verbatim Require Import concrete_memo.
From Verbatim Require Import lexer.abstraction.

Module LexerFn (ALPHABET : SIGMA) (LABELS : LABEL).

  Module Import R <: regex.T := regexTFn ALPHABET.
  Module Import STT <: state.T := stateTFn R LABELS.
  Module Import MEM <: memo.T := memoTFn STT.

  Module Import Correctness := memo.correctness.CorrectFn MEM.

  Module Export LitLexer <: LEXER STT.

    Import IMPL.
    Definition lex := lex_M.
    Definition lex_sound := lex_sound__M.
    Definition lex_complete := lex_complete__M.

  End LitLexer.

  Export STT.
  Export R.Defs.
  Export STT.Defs.
  Export STT.R.Defs.
  

End LexerFn.

  
