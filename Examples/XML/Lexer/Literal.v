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
  | OPEN
  | XMLDeclOpen
  | CLOSE
  | SPECIAL_CLOSE
  | SLASH_CLOSE
  | SLASH
  | EQUALS
  | STRING
  | NAME
  | SEA_WS.

  Definition Label : Type := Label'.
  Definition defLabel : Label := SEA_WS.
  Lemma Label_eq_dec : forall (l l' : Label), {l = l'} + {l <> l'}.
  Proof. decide equality. Qed.

End LABELS.

(** Here is where the lexer is compiled **)
(* ALPHABET is the SIGMA object from asciiSigma *)
Module Export LXR := LexerFn ALPHABET LABELS.
(* Loads in regex library from _Utils.Lexer; Object R comes from LXR *)
Module Import PBR := prebuilt_regexes R.

Definition S_re := asciiUnion ws_carr_chars.
Definition SEA_WS_re := Plus S_re.
Definition SEA_WS_ru := (SEA_WS, SEA_WS_re).

Definition OPEN_re := stringApp "<".
Definition OPEN_ru := (OPEN, OPEN_re).

Definition XMLDeclOpen_re := App (stringApp "<?xml") S_re.
Definition XMLDeclOpen_ru := (XMLDeclOpen, XMLDeclOpen_re).

Definition CLOSE_re := stringApp ">".
Definition CLOSE_ru := (CLOSE, CLOSE_re).

Definition SPECIAL_CLOSE_re := stringApp "?>".
Definition SPECIAL_CLOSE_ru := (SPECIAL_CLOSE, SPECIAL_CLOSE_re). 

Definition SLASH_CLOSE_re := stringApp "/>".
Definition SLASH_CLOSE_ru := (SLASH_CLOSE, SLASH_CLOSE_re).

Definition SLASH_re := stringApp "/".
Definition SLASH_ru := (SLASH, SLASH_re). 

Definition EQUALS_re := stringApp "=".
Definition EQUALS_ru := (EQUALS, EQUALS_re).

(* No double quotation mark or opening angle bracket *)
Definition DoubleQuotedStringCharPunc_re := stringUnion "!#$%&()*+,-.\/:;=>?@[]^_`{¦}~'".
Definition DoubleQuotedStringChar_re := IterUnion [AZ_re; az_re; digit_re; ws_re; DoubleQuotedStringCharPunc_re].
Definition DoubleQuotedString_re := IterApp [quote_re ; Star DoubleQuotedStringChar_re ; quote_re].

(* No double quotation mark, single quotation mark, or opening angle bracket *)
Definition SingleQuotedStringCharPunc_re := stringUnion "!#$%&()*+,-.\/:;=>?@[]^_`{¦}~".
Definition SingleQuotedStringChar_re := IterUnion [AZ_re; az_re; digit_re; ws_re; SingleQuotedStringCharPunc_re].
Definition SingleQuotedString_re := IterApp [stringApp "\'" ; Star SingleQuotedStringChar_re ; stringApp "\'"].

Definition STRING_re := Union DoubleQuotedString_re SingleQuotedString_re.
Definition STRING_ru := (STRING, STRING_re).

Definition NameStartChar_re := IterUnion [stringApp ":" ; az_re ; AZ_re ].
Definition NameChar_re := IterUnion [ NameStartChar_re ; stringApp "-" ; stringApp "_" ; stringApp "." ; digit_re ].

Definition NAME_re := App NameStartChar_re (Star NameChar_re).
Definition NAME_ru := (NAME, NAME_re).

(** Compile rules and extract **)
Definition rus : list Rule :=
  [ OPEN_ru ; XMLDeclOpen_ru ; CLOSE_ru ; SPECIAL_CLOSE_ru ; SLASH_CLOSE_ru ; SLASH_ru ; EQUALS_ru ; STRING_ru ; NAME_ru ; SEA_WS_ru ].

Definition show_label (l : Label) : string :=
  match l with
  | OPEN => "OPEN"
  | XMLDeclOpen => "XMLDeclOpen"
  | CLOSE => "CLOSE"
  | SPECIAL_CLOSE => "SPECIAL_CLOSE"
  | SLASH_CLOSE => "SLASH_CLOSE"
  | SLASH => "SLASH"
  | EQUALS => "EQUALS"
  | STRING => "STRING"
  | NAME => "NAME"
  | SEA_WS => "SEA_WS"
  end.

Definition show_token (t : Token) : string :=
  match t with
  | (l, s) => show_label l ++ " | " ++ string_of_list_ascii s
  end.
              
Set Warnings "-extraction-opaque-accessed,-extraction".
Compute (extract_path "XML" Literal).
Extraction "Examples/XML/Evaluation/Literal/instance.ml" lex rus show_token.
