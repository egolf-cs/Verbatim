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
Module Export NEWICK_LABELS <: LABEL.

  Inductive Label' : Type :=
  | NAT
  | COLON
  | COMMA
  | DECIMAL_POINT
  | L_PAREN
  | R_PAREN
  | SEMICOLON
  | WS.

  Definition Label : Type := Label'.
  Definition defLabel : Label := WS.
  Lemma Label_eq_dec : forall (l l' : Label), {l = l'} + {l <> l'}.
  Proof. decide equality. Qed.

End NEWICK_LABELS.

(** Here is where the lexer is compiled **)
(* ALPHABET is the SIGMA object from asciiSigma *)
Module Export LXR := LexerFn ALPHABET NEWICK_LABELS.
(* Loads in regex library from _Utils.Lexer; Object R comes from LXR *)
Module Import PBR := prebuilt_regexes R.

Definition ru_nat := (NAT, App digit_re (Star digit_re)).
Definition ru_colon := (COLON, stringApp ":").
Definition ru_comma := (COMMA, stringApp ",").
Definition ru_decimal := (DECIMAL_POINT, stringApp ".").
Definition ru_lparen := (L_PAREN, stringApp "(").
Definition ru_rparen := (R_PAREN, stringApp ")").
Definition ru_semi := (SEMICOLON, stringApp ";").
Definition ru_ws : Rule := (WS, ws_carr_re).

(** Compile rules and extract **)
Definition rus : list Rule :=
  [ ru_nat ; ru_colon ; ru_comma ; ru_decimal ; ru_lparen ; ru_rparen ; ru_semi ; ru_ws ].

Set Warnings "-extraction-opaque-accessed,-extraction".
Compute (extract_path "Newick" Literal).
Extraction "Examples/Newick/Evaluation/Literal/instance.ml" lex rus.
