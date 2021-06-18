Require Import List.
Import ListNotations.
Require Import PeanoNat.
Require Import Coq.omega.Omega.
Require Import Coq.Numbers.NatInt.NZOrder.

From Verbatim Require Import ltac.
From Verbatim Require Import state.

Module ImplFn (Import ST : state.T).

  Import ST.Ty.
  Import ST.Defs.

  (* Invariant: index == length s *)
  Fixpoint max_pref_fn (s : String) (i : index) (state : State)
    : option (Prefix * Suffix * index):=
    match s with
    (* in a regex approach, accepting := nullable *)
    | [] => if accepting state then Some ([],[],i) else None
    | a :: s' =>
      let
        (* in a regex approach, transition := derivative *)
        state' := transition a state in
      let
        mpxs := max_pref_fn s' (decr i) state' in

      match mpxs with
      | None => if (accepting state') then Some ([a], s', (decr i)) else
                 if (accepting state) then Some ([], s, i) else
                   None
      | Some (p, q, qi) => Some (a :: p, q, qi)
      end
    end.

  Definition extract_fsm_for_max (code : String) (i : index)
             (sru : (Label * State)) :=
    match sru with
      (a, fsm) => (a, max_pref_fn code i fsm)
    end.

  Definition max_prefs (code : String) (i : index)
             (erules : list (Label * State))
    :=
      map (extract_fsm_for_max code i) erules.

  (* prefixes closest to the head are preferred *)
  Definition longer_pref (apref1 apref2 : Label * (option (Prefix * Suffix * index)))
    : Label * (option (Prefix * Suffix * index)) :=
    match apref1, apref2 with
    | (_, None), (_, _) => apref2
    | (_, _), (_, None) => apref1
    (* This is finding the min right now... *)
    | (_, Some (x, _, _)), (_, Some (y, _, _)) => if (length x) =? (length y)
                                                 then apref1 else
                                                   if (length x) <? (length y)
                                                   then apref2 else apref1
    end.


  Fixpoint max_of_prefs (mprefs : list (Label * (option (Prefix * Suffix * index))))
    : Label * option (Prefix * Suffix * index) :=
    match mprefs with
    | [] => ([], @None (String * String * index))
    | p :: ps => longer_pref p (max_of_prefs ps)
    end.

  
  Definition init_srule (rule : Rule) : sRule :=
    match rule with
    | (label, re) => (label, init_state re)
    end.


End ImplFn.
