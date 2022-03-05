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
  | INT
  | FLOAT
  | STRING
  | TRUE
  | FALSE
  | NULL
  | COLON
  | COMMA
  | LEFT_BRACKET
  | RIGHT_BRACKET
  | LEFT_BRACE
  | RIGHT_BRACE
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


(** White Space **)
(* [ \t\n\r] *)
(* ws_carr_re includes \r; ws_re does not *)
Definition ru_ws : Rule := (WS, ws_carr_re).


(** Numbers **)
Definition exp_part_re := IterApp [(stringUnion "Ee"); (Optional (stringUnion "+-")); nat_re].
Definition float_re := App dec_re (Optional exp_part_re).

Definition ru_float := (FLOAT, float_re).
Definition ru_int := (INT, int_re).


(** STRING **)
Definition unicode_digit_re := stringUnion "0123456789aAbBcCdDeEfF".
Definition four_unicode_digits_re := IterApp [unicode_digit_re ; unicode_digit_re ; unicode_digit_re ; unicode_digit_re].
Definition unicode_codepoint_re := App (stringApp "\u") four_unicode_digits_re.
Definition json_char_re := IterUnion [ unicode_codepoint_re ; AZ_re; az_re; digit_re; ws_re; punc_re; esc_quote_re; esc_bslash_re ].
Definition json_string_re := IterApp [quote_re; Star json_char_re; quote_re].
Definition ru_string := (STRING, json_string_re).

(** keywords **)
Definition ru_true := (TRUE, stringApp "true").
Definition ru_false := (FALSE, stringApp "false").
Definition ru_null := (NULL, stringApp "null").


(** brack, brace, colon, comma **)
Definition ru_colon := (COLON, stringApp ":").
Definition ru_comma := (COMMA, stringApp ",").
Definition ru_lbrack := (LEFT_BRACKET, stringApp "[").
Definition ru_rbrack := (RIGHT_BRACKET, stringApp "]").
Definition ru_lbrace := (LEFT_BRACE, stringApp "{").
Definition ru_rbrace := (RIGHT_BRACE, stringApp "}").


(** Compile rules and extract **)
Definition rus : list Rule :=
  [ru_ws;ru_int;ru_float;ru_string;ru_true;ru_false;ru_null;
  ru_colon;ru_comma;ru_lbrack;ru_rbrack;ru_lbrace;ru_rbrace].

Set Warnings "-extraction-opaque-accessed,-extraction".
Compute (extract_path "JSON" Literal).
Extraction "Examples/JSON/Evaluation/Literal/instance.ml" lex rus.
