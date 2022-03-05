Require Import List.
Import ListNotations.

Require Import String.
Open Scope string_scope.
Require Import Ascii.

Require Import BinInt BinNat.
Require Import DecimalString.
Import NilEmpty.
(** < Float stuff; doesn't extract **)
(*Require Import PrimFloat.
Require Import Int63.

Require Extraction.
Require ExtrOCamlInt63.
Require ExtrOCamlFloats.

From Verbatim Require FloatLexer.
Import FloatLexer.Splitter.
 *)
(**/> **)

From Verbatim Require Import ltac.

(** < Core imports **)
From Verbatim Require Import lexer.abstraction.
From Verbatim Require Import Newick.Lexer.Literal.
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
    | NAT => N
    | _ => unit
    end.

  (* Need to define a default value for nth *)
  (* defLabel was defined in Literal.v *)
  Definition defLiteral : sem_ty defLabel := tt.

  Definition N_of_String (s : String) : option N :=
    match uint_of_string (string_of_list_ascii s) with
    | Some ui => Some (N.of_uint ui)
    | None => None
    end.
  
  Definition apply_sem (pr : Label * String) : option {l : Label & sem_ty l} :=
    match pr with
    | (NAT, s) =>
      match N_of_String s with
      | Some n => Some (existT _ NAT n)
      | None => None
      end
    | (l, _) => Some (existT _ l tt)
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
Compute (extract_path "Newick" Semantic).
Extraction "Examples/Newick/Evaluation/Semantic/instance.ml" lex_sem rus.
