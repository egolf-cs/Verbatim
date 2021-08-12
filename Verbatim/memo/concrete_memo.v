Require Import List.
Import ListNotations.

Require Import FSets FSets.FMapAVL FSets.FMapFacts.

From Verbatim Require Import state.
From Verbatim Require Import memo.
From Verbatim Require Import ltac.
From Verbatim Require Import Orders.
From Verbatim Require Import hashtrie.


Module FMemo (STT : state.T) <: MEMO STT.

  Import STT.Ty.
  Import STT.Defs.
  Import STT.R.Defs.
  Import Trie.

  Module Pointer_as_UOT <: UsualOrderedType := UOT_from_UCT Pointer_as_UCT.
  Module FM := FMapAVL.Make Pointer_as_UOT.
  Module FMF := FMapFacts.Facts FM.

  Definition Memo : Type := FM.t (@Trie (option (String * String * index))).
  Definition emptyMemo : Memo := FM.empty (@Trie (option (String * String * index))).
  
  Definition get_Memo (M : Memo) (pnt : Pointer) (i : index)
    : option (option (String * String * index)) :=
    match FM.find pnt M with
    | None => None
    | Some T => get_Trie T (index2list i)
    end.
  
  Definition set_Memo (M : Memo) (pnt : Pointer) (i : index)
             (o : (option (String * String * index))) : Memo :=
    match FM.find pnt M with
    | None => FM.add pnt (set_Trie Leaf (index2list i) o) M
    | Some T => FM.add pnt (set_Trie T (index2list i) o) M 
    end.

  Lemma correct_Memo : forall M ptr i o, get_Memo (set_Memo M ptr i o) ptr i = Some o.
  Proof.
    intros. unfold get_Memo. unfold set_Memo. repeat dm.
    - rewrite FMF.add_eq_o in E; auto. repeat inj_all. apply get_set.
    - rewrite FMF.add_eq_o in E; auto. repeat inj_all. apply get_set.
    - rewrite FMF.add_eq_o in E; auto. discriminate.
    - rewrite FMF.add_eq_o in E; auto. discriminate.
  Qed.

  
  Lemma correct_Memo_moot : forall M ptr ptr' i i' o,
      (ptr <> ptr' \/ i <> i')
      -> 
      get_Memo (set_Memo M ptr' i' o) ptr i = get_Memo M ptr i.
  Proof.
    intros. unfold get_Memo. unfold set_Memo.
    destruct (Pointer_as_UOT.eq_dec ptr ptr') eqn:E;
      destruct (index_eq_dec i i'); destruct H;
      repeat dm;
      try(rewrite FMF.add_neq_o in *; auto; rewrite E in *; repeat inj_all; auto; discriminate);
      try(rewrite FMF.add_eq_o in *; auto;
          repeat inj_all; rewrite E1 in *; repeat inj_all; rewrite get_set_moot; auto;
          intros C; destruct H; apply f_equal with (f := list2index) in C;
          repeat rewrite list_inv in C; auto; discriminate);
      try(try subst i; rewrite FMF.add_neq_o in *; auto; rewrite E0 in *;
          repeat inj_all; auto; discriminate);
      try(subst ptr; rewrite E1 in *; discriminate).
    - rewrite FMF.add_eq_o in *; auto; discriminate.
  Qed.
    
  Lemma correct_emptyMemo : forall stt z, get_Memo emptyMemo stt z = None.
  Proof.
    intros. unfold get_Memo. unfold emptyMemo. repeat dm.
    rewrite FMF.empty_o in E. discriminate.
  Qed.
  

End FMemo.


Module memoTFn (STT' : state.T) <: memo.T.
  Module STT := STT'.
  Module MemTy <: MEMO STT := FMemo STT.
  Module Defs := memo.MemoDefsFn STT MemTy.
End memoTFn.
