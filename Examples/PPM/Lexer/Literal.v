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

(** Label type defined here **)
Module Export LABELS <: LABEL.

  Inductive Label' : Type :=
  | P3
  | NAT
  | WS.

  Definition Label : Type := Label'.
  Definition defLabel : Label := WS.
  Lemma Label_eq_dec : forall (l l' : Label), {l = l'} + {l <> l'}.
  Proof. decide equality. Qed.

End LABELS.

(** Here is where the lexer is compiled **)
(* ALPHABET is the SIGMA object from asciiSigma *)
Module Export LXR := LexerFn ALPHABET LABELS.
(* Loads in regex library from _Utils.Lexer; Object R comes from LXR *)
Module Import PBR := prebuilt_regexes R.

(** keywords **)
Definition ru_p3 := (P3, stringApp "P3").

(** Numbers **)
Definition ru_nat := (NAT, nat_re).

(** White Space **)
(* [ \t\n\r] *)
(* ws_carr_re includes \r; ws_re does not *)
Definition ru_ws : Rule := (WS, ws_carr_re).

(** Compile rules and extract **)
Definition rus : list Rule :=
  [ru_p3 ; ru_nat; ru_ws]. 

Set Warnings "-extraction-opaque-accessed,-extraction".
Compute (extract_path "PPM" Literal).
Extraction "Examples/PPM/Evaluation/Literal/instance.ml" lex rus.
