Require Import List.
Import ListNotations.

Require Import FSets FSets.FMapAVL FSets.FMapFacts.

From Verbatim Require Import state.
From Verbatim Require Import memo.
From Verbatim Require Import ltac.
From Verbatim Require Import Orders.
From Verbatim Require Import tape.



Module FMemo (STT : state.T) <: MEMO STT.

  Import STT.Ty.
  Import STT.Defs.
  Import STT.R.Defs.

  Module Pointer_as_UOT <: UsualOrderedType := UOT_from_UCT Pointer_as_UCT.
  Module FM := FMapAVL.Make Pointer_as_UOT.
  Module FMF := FMapFacts.Facts FM.

  Definition Memo : Type := @Tape (FM.t (option (String * String * index))).
  Definition emptyMemo : Memo := ([],[]).
  
  Definition get_Memo (M : Memo) (pnt : Pointer) (i : index)
    : option (option (String * String * index)) :=
    match get_Tape (index2nat i) M with
    | None => None
    | Some MP => FM.find pnt MP
    end.
  
  Definition set_Memo (M : Memo) (pnt : Pointer) (i : index)
             (o : (option (String * String * index))) : Memo :=
    match get_Tape (index2nat i) M with
    | None => set_Tape (FM.add pnt o (@FM.empty (option (String * String * index))))
                      (index2nat i)
                      M
    | Some MP => set_Tape (FM.add pnt o (MP)) (index2nat i) M
    end.

  Lemma correct_Memo : forall M ptr i o, get_Memo (set_Memo M ptr i o) ptr i = Some o.
  Proof.
    intros. unfold get_Memo. unfold set_Memo. repeat dm.
    - rewrite get_of_set_eq in E; repeat inj_all. apply FMF.add_eq_o; auto.
    - rewrite get_of_set_eq in E; repeat inj_all. apply FMF.add_eq_o; auto.
    - rewrite get_of_set_eq in E; discriminate.
    - rewrite get_of_set_eq in E; discriminate.
  Qed.

  Lemma bar : forall i i', i <> i' -> index2nat i <> index2nat i'.
  Admitted.
  
  Lemma correct_Memo_moot : forall M ptr ptr' i i' o,
      (ptr <> ptr' \/ i <> i')
      -> 
      get_Memo (set_Memo M ptr' i' o) ptr i = get_Memo M ptr i.
  Proof.
    intros. unfold get_Memo. unfold set_Memo.
    destruct (Pointer_as_UOT.eq_dec ptr ptr') eqn:E;
      destruct (index_eq_dec i i'); destruct H;
        repeat dm; try contradiction.
  Admitted.
    
  Lemma correct_emptyMemo : forall stt z, get_Memo emptyMemo stt z = None.
  Proof.
    intros. unfold get_Memo. unfold emptyMemo. unfold get_Tape. repeat dm.
    sis.
  Admitted.

End FMemo.


Module memoTFn (STT' : state.T) <: memo.T.
  Module STT := STT'.
  Module MemTy <: MEMO STT := FMemo STT.
  Module Defs := memo.MemoDefsFn STT MemTy.
End memoTFn.
