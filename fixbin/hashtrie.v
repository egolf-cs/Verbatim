Require Import List.
Import ListNotations.

From Verbatim Require Import ltac.


Module Trie.

  Inductive Trie {Target : Type} : Type :=
  | Leaf
  | Branch (t : option Target) (t0 t1 : Trie).

  Fixpoint set_Trie {Target : Type} (T : Trie) (key : list bool) (value : Target) : Trie :=
    match key with
    | [] =>
      match T with
      | Leaf => Branch (Some value) Leaf Leaf
      | Branch _ t0 t1 => Branch (Some value) t0 t1
      end
    | b :: bs =>
      match T with
      | Leaf =>
        if b then Branch None (set_Trie Leaf bs value) Leaf
        else Branch None Leaf (set_Trie Leaf bs value)
      | Branch t t0 t1 =>
        if b then Branch t (set_Trie t0 bs value) t1
        else Branch t t0 (set_Trie t1 bs value)
      end
    end.

  Fixpoint get_Trie {Target : Type} (T : Trie) (key : list bool) : option Target :=
    match T with
    | Leaf => None
    | Branch t t0 t1 =>
      match key with
      | [] => t
      | b :: bs =>
        if b then get_Trie t0 bs
        else get_Trie t1 bs
      end
    end.

  Lemma get_set : forall {Target : Type} key T (value : Target),
      get_Trie (set_Trie T key value) key = Some value.
  Proof.
    induction key; intros.
    - sis. repeat dm.
    - sis. repeat dm; sis; apply IHkey.
  Qed.

  Lemma get_set_moot : forall {Target : Type} k0 k1 (v : Target) T,
      k0 <> k1
      -> get_Trie (set_Trie T k0 v) k1 = get_Trie T k1.
  Proof.
    induction k0; destruct k1; intros.
    - contradiction.
    - clear H. sis. repeat dm. sis. repeat dm.
    - clear H. sis. repeat dm.
    - sis. repeat dm; sis; repeat dm; apply IHk0; intros C; destruct H; rewrite C; auto.
  Qed.

End Trie.
  
