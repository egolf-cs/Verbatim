Require Import List.
Import ListNotations.
Require Import PeanoNat.
Require Import Coq.omega.Omega.

From VLG Require Import ltac.
From VLG Require Import coredefs.
From VLG Require Import prefixer.
From VLG Require Import memocore.

(*
Inductive lexy_entry (M : Memo) (stt : State) (z : String) : Prop :=
| LexyE0 (H : get_Memo M stt z = None)
  :
    lexy_entry M stt z
| LexyE1 (o : option (Prefix * Suffix))
         (H0 : max_pref_fn z stt = o)
         (H1 : get_Memo M stt z = Some o)
  :
    lexy_entry M stt z. *)

Definition lexy (M : Memo) : Prop :=
  forall stt z o,
    (get_Memo M stt z = Some o
     -> max_pref_fn z stt = o)
    /\ (max_pref_fn z stt = o
       -> (get_Memo M stt z = Some o \/ get_Memo M stt z = None)).

Definition lexy_list (Ms : list Memo) : Prop :=
  forall M, In M Ms -> lexy M. 
