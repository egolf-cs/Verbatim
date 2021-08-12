Require Import List.
Import ListNotations.

Require Import Ascii.
Require Import String.
Open Scope string_scope.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

(** < Core imports **)
From Verbatim Require Import state. (* LABEL lives here, maybe it shouldn't. *)
From Verbatim Require Import Utils.asciiSigma.
From Verbatim Require Import concrete_lexer.
From Verbatim Require Import _Utils.Lexer.
(** /> **)

Module Export LABELS <: LABEL.
  
  Inductive Label' : Type :=
  | INT
  | PNT
  | DEC
  | EXP.

  Definition Label := Label'.
  Definition defLabel : Label := INT.
  Lemma Label_eq_dec : forall (l l' : Label), {l = l'} + {l <> l'}.
  Proof. decide equality. Qed.
  
End LABELS.

Module Export LXR := LexerFn ALPHABET LABELS.
Module Import PBR := prebuilt_regexes R.

(** Build Rules **)
Definition ru_int := (INT, int_re).
Definition ru_dec_point := (PNT, stringApp ".").
Definition ru_dec := (DEC, nat_lz_re).
Definition ru_Ee_delim :=
  (EXP, IterUnion [(stringApp "e");(stringApp "E");(stringApp "e+");(stringApp "E+")]).


Definition rules : list Rule := [ru_int;ru_dec_point;ru_dec;ru_Ee_delim].

Module Splitter.
  
  Definition Split_float_str (z : String) : option (String * String * String) :=
    match lex rules z with
    | ([(INT,i)], []) => Some (i, [], [])
    | ([(INT,i);(PNT,_);(DEC,d)], []) => Some (i, d, [])
    | ([(INT,i);(EXP,_);(INT,e)], []) => Some (i, [], e)
    | ([(INT,i);(PNT,_);(DEC,d);(EXP,_);(INT,e)], []) => Some (i, d, e)
    | _ => None
    end.

End Splitter.

