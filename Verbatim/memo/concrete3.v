Require Import List.
Import ListNotations.

Require Import FSets FSets.FMapAVL FSets.FMapFacts.

From Verbatim Require Import state.
From Verbatim Require Import memo.
From Verbatim Require Import Orders.
From Verbatim Require Import ltac.


Module FMemo (STT : state.T) <: MEMO STT.

  Import STT.Ty.
  Import STT.Defs.
  Import STT.R.Defs.

  Module Pointer_as_UOT <: UsualOrderedType := UOT_from_UCT Pointer_as_UCT.
  Module Suffix_as_UOT <: UsualOrderedType := List_as_UOT T_as_UOT.
  Module pair_as_UOT <: UsualOrderedType := Pair_as_UOT Pointer_as_UOT Suffix_as_UOT.

  Module FM := FMapAVL.Make pair_as_UOT.
  Module FMF := FMapFacts.Facts FM.

  Definition Memo : Type := FM.t (option (String * String)).
  Definition emptyMemo : Memo := FM.empty (option (String * String)).

  Definition set_Memo (M : Memo) (pnt : Pointer) (sx : String) (o : (option (String * String))) :=
    FM.add (pnt, sx) o M.

  Definition get_Memo (M : Memo) (pnt : Pointer) (sx : String)
    : option (option (String * String)) :=
    FM.find (pnt, sx) M.


  Lemma correct_Memo : forall M stt z o, get_Memo (set_Memo M stt z o) stt z = Some (o).
  Proof.
    intros. unfold get_Memo. unfold set_Memo. apply FMF.add_eq_o. auto.
  Qed.
  
  Lemma correct_Memo_moot : forall M stt stt' z z' o,
      (stt <> stt' \/ z <> z')
      -> 
      get_Memo (set_Memo M stt' z' o) stt z = get_Memo M stt z.
  Proof.
    intros. unfold get_Memo. unfold set_Memo. apply FMF.add_neq_o.
    intros C. inv C. destruct H; contradiction.
  Qed.
    
  Lemma correct_emptyMemo : forall stt z, get_Memo emptyMemo stt z = None.
  Proof.
    intros. unfold get_Memo. unfold emptyMemo. apply FMF.empty_o.
  Qed.
  

End FMemo.
