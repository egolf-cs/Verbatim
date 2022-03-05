Require Import List.
Import ListNotations.

Require Import String.
Open Scope string_scope.
Require Import Ascii.

Require Import BinInt.
Require Import DecimalString.
Import NilEmpty.

From Verbatim Require Import ltac.

(** < Core imports **)
From Verbatim Require Import lexer.abstraction.
From Verbatim Require Import XML.Lexer.Literal.
From Verbatim Require Import actions.impl.
From Verbatim Require Import _Utils.Lexer.
(** /> **)

(** This is where the user defines
   1) sem_ty -- which maps labels to types
   2) apply_sem -- which tries to map tokens to semantic tokens
   3) defLiteral -- of type sem_ty defLabel -- which is the "default" value of that type
   4) label_carries -- a proof that apply_sem does not change the label of the token
 **)
Module USER <: SEM_USER STT.

  Definition sem_ty (l : Label) : Type :=
    match l with
    | STRING => string
    | NAME => string
    | _ => unit
    end.

  (* Need to define a default value for nth *)
  (* defLabel was defined in Literal.v *)
  Definition defLiteral : sem_ty defLabel := tt.

  Definition apply_sem (pr : Label * String) : option {l : Label & sem_ty l} :=
    match pr with
    | (STRING, s) => Some (existT _ STRING (string_of_list_ascii s))
    | (NAME, s)   => Some (existT _ NAME (string_of_list_ascii s))
    | (l, s)      => Some (existT _ l tt)
    end.

  Lemma label_carries : forall l l' s t,
      apply_sem (l, s) = Some (existT sem_ty l' t)
      -> l = l'.
  Proof.
    intros. destruct l; destruct l'; auto; sis; repeat dm; repeat inj_all; discriminate.
  Qed.

End USER.

(* Here we use the literal lexer and the user parameters to create the semantic lexer *)
Module Import SemLexer := SemLexerFn STT LitLexer USER.
Import SemLexer.Impl.

(* And extract; extract_path returns the default path for extraction *)
Set Warnings "-extraction-opaque-accessed,-extraction".
Compute (extract_path "XML" Semantic).
Extraction "Examples/XML/Evaluation/Semantic/instance.ml" lex_sem rus.
