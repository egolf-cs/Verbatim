Require Import List.
Import ListNotations.
Require Import PeanoNat.
Require Import Coq.omega.Omega.

From VLG Require Import ltac.
From VLG Require Import coredefs.

Parameter Memo : Type.
Parameter emptyMemo : Memo.
Parameter set_Memo : Memo -> State -> String -> option(Prefix * Suffix) -> Memo.
Parameter get_Memo : Memo -> State -> String -> option (option (Prefix * Suffix)).

Hypothesis correct_Memo : forall M stt z o, get_Memo (set_Memo M stt z o) stt z = Some (o).
Hypothesis correct_emptyMemo : forall stt z, get_Memo emptyMemo stt z = None.
