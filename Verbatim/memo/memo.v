Require Import List.
Import ListNotations.

From Verbatim Require Import state.
From Verbatim Require Import lexer.correct.
From Verbatim Require Import lexer.impl.

Module Type MEMO (Import STT : state.T).

  Import STT.
  Import STT.Ty.

  Parameter Memo : Type.
  Parameter emptyMemo : Memo.
  Parameter set_Memo : Memo -> State -> String -> option(String * String) -> Memo.
  Parameter get_Memo : Memo -> State -> String -> option (option (String * String)).

  Parameter correct_Memo : forall M stt z o, get_Memo (set_Memo M stt z o) stt z = Some (o).
  Parameter correct_Memo_moot : forall M stt stt' z z' o,
      (stt <> stt' \/ z <> z')
      -> 
      get_Memo (set_Memo M stt' z' o) stt z = get_Memo M stt z.
  Parameter correct_emptyMemo : forall stt z, get_Memo emptyMemo stt z = None.

End MEMO.

Module MemoDefsFn (STT : state.T) (MEM : MEMO STT).

  Import MEM.
  Module Import NaiveLexer := lexer.impl.ImplFn STT.
  Module Import NaiveLexerF := lexer.correct.CorrectFn STT.
  Import NaiveLexer.MPref.
  

  
  Definition lexy (M : Memo) : Prop :=
    forall stt z o,
      (get_Memo M stt z = Some o
       -> max_pref_fn z stt = o)
      (*/\ (max_pref_fn z stt = o
         -> (get_Memo M stt z = Some o \/ get_Memo M stt z = None))*).

  Definition lexy_list (Ms : list Memo) : Prop :=
    forall M, In M Ms -> lexy M.


End MemoDefsFn.

Module Type DefsT (STT : state.T) (Ty : MEMO STT).
  Include MemoDefsFn STT Ty.
End DefsT.

Module Type T.
  Declare Module STT : state.T.
  Declare Module MemTy : MEMO STT.
  Declare Module Defs : DefsT STT MemTy.
  Export STT.
  Export STT.Ty.
  Export MemTy.
End T.
