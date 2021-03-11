Require Import List.
Import ListNotations.

From Verbatim Require Import ltac.
From Verbatim Require Import regex.
From Verbatim Require Import Table.
From Verbatim Require Import Orders.

Module FTable (R : regex.T) <: TABLE R.  

  Import R.
  Import R.Ty.
  Module DS := R.Defs.
  Module Sigma_as_UOT := R.Defs.T_as_UOT.
  Module regex_as_UOT := R.Defs.regex_as_UOT.
  Module pair_as_UOT := Pair_as_UOT regex_as_UOT Sigma_as_UOT.

  Module FM := FMapAVL.Make pair_as_UOT.
  Module FMF := FMapFacts.Facts FM.
  Module reFS := R.Defs.reFS.
      

  Definition Table : Type := (FM.t regex) * reFS.t.
  Definition emptyTable : Table := (FM.empty regex, reFS.empty).
  
  Definition set_Table (T : Table) (e : regex) (a : Sigma) (r : regex) : Table :=
    match T with
    | (fm, fs) => (FM.add (e, a) r fm, fs)
    end.
  Definition get_Table (T : Table) (e : regex) (a : Sigma) : option regex :=
    FM.find (e, a) (fst T).

  Lemma correct_Table : forall T e a r, get_Table (set_Table T e a r) e a = Some (r).
  Proof.
    intros. unfold get_Table. unfold set_Table. destruct T.
    apply FMF.add_eq_o. auto.
  Qed.

  Lemma moot_setTable : forall T e0 e a b r,
      a <> b
      \/ e <> e0
      -> get_Table (set_Table T e b r) e0 a = get_Table T e0 a.
  Proof.
    intros. unfold get_Table. unfold set_Table. destruct T.
    apply FMF.add_neq_o. destruct H; intros C; destruct H; injection C; intros; subst; auto.
  Qed.

  Lemma correct_emptyTable : forall e a, get_Table emptyTable e a = None.
  Proof.
    intros. unfold get_Table. unfold emptyTable. simpl. apply FMF.empty_o.
  Qed.

  Definition add_state (T : Table) (e : regex) : Table :=
    match T with
    | (fm, fs) => (fm, reFS.add e fs)
    end.

  Definition get_states (T : Table) : reFS.t := snd T.

  Lemma empty_states : get_states emptyTable = reFS.empty.
  Proof. auto. Qed.

  Lemma correct_states : forall T r, reFS.In r (get_states (add_state T r)).
  Proof.
    intros. unfold add_state. unfold get_states. destruct T. simpl. apply reFS.add_1. auto.
  Qed.
  
  Lemma moot_add_state : forall T e a r,
      get_Table T e a = get_Table (add_state T r) e a.
  Proof.
    intros. unfold get_Table. unfold add_state. destruct T. simpl. auto.
  Qed.

  Definition get_eq (T : Table) (e : regex) : option regex :=
    if reFS.mem e (snd T) then Some e else None.

  Lemma get_eq_correct : forall T e e',
      get_eq T e = Some e' -> reFS.In e' (get_states T) /\ regex_eq e e' = true.
  Proof.
    intros. unfold get_eq in H. destruct (reFS.mem e (snd T)) eqn:E; [|discriminate].
    injection H. intros. subst. split.
    - unfold get_states. apply reFS.mem_2. auto.
    - apply regex_eq_correct. auto.
  Qed.

End FTable.
