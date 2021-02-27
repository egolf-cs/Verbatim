Require Import List.
Import ListNotations.

From Verbatim Require Import state.

Module Type MEMO (Import STT : state.T).

  Import STT.
  Import STT.Ty.

  Parameter Memo : Type.
  Parameter emptyMemo : Memo.
  Parameter set_Memo : Memo -> State -> String -> option(String * String) -> Memo.
  Parameter get_Memo : Memo -> State -> String -> option (option (String * String)).

  Parameter correct_Memo : forall M stt z o, get_Memo (set_Memo M stt z o) stt z = Some (o).
  Parameter correct_emptyMemo : forall stt z, get_Memo emptyMemo stt z = None.

End MEMO.

(*Module MemoDefsFn (STT : state.T) (MEM : MEMO STT).*)

Module Type T.
  Declare Module STT : state.T.
  Declare Module Ty : MEMO STT.
  Export STT.
  Export STT.Ty.
  Export Ty.
End T.
