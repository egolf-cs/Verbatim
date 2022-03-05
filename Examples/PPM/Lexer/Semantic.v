Require Import List.
Import ListNotations.

Require Import String.
Open Scope string_scope.
Require Import Ascii.

Require Import BinInt NArith.
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
From Verbatim Require Import PPM.Lexer.Literal.
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
    | P3 => unit
    | NAT => N
    | WS => unit
    end.

  (* Need to define a default value for nth *)
  (* defLabel was defined in Literal.v *)
  Definition defLiteral : sem_ty defLabel := tt.

(*  (* Doesn't check for leading 0 or -0 *)
  Definition String2uint' (z : String) : option Z :=
    match z with
    | [] => None
    | _ =>
      match uint_of_string (string_of_list_ascii z) with
      | None => None
      | Some x => Some (Z.of_uint x)
      end
    end.

  (* Doesn't check for leading 0 or -0 *)
  Definition String2int' (z : String) : option Z :=
    match z with
    | [] => None
    | _ =>
      match int_of_string (string_of_list_ascii z) with
      | None => None
      | Some x => Some (Z.of_int x)
      end
    end.

  (* Checks for 0 and -0 *)
  Definition String2int (z : String) : option Z :=
    match z with
    (* Just a 0 *)
    | [Ascii false false false false true true false false] => Some 0%Z
    (* Just a -0 *)
    | [Ascii true false true true false true false false ;
      Ascii false false false false true true false false] => Some 0%Z
    (* Leading 0 *)
    | Ascii false false false false true true false false :: _ => None
    (* Only a - *)
    | [Ascii true false true true false true false false] => None
    (* Leading -0 *)
    | Ascii true false true true false true false false ::
            Ascii false false false false true true false false :: _ => None
    | _ => String2int' z
    end.
 *)
  
  (** Float stuff, could not extract **)
  (*
  Fixpoint float_exp_pos (f : float) (n : nat) : float :=
    match n with
    | 0 => 1%float
    | S m => f * (float_exp_pos f m)
    end.

  Definition float_exp (f : float) (i : Z) : float :=
    match i with
    | Z0 => 1%float
    | Zpos n => float_exp_pos f (Pos.to_nat n)
    | Zneg n => 1%float / float_exp_pos f (Pos.to_nat n)
    end.

  Definition String2float' (o : option (String * String * String)) : option float :=
    match o with
    | Some (i, [], []) =>
      match String2int i with
      | Some i' => Some (of_int63 (Int63.of_Z i'))
      | None => None
      end
    | Some (i, d, []) =>
      match String2int i with
      | Some i' =>
        match String2uint' d with
        | Some d' =>
          let
            dec_factor := float_exp 10%float (Zneg (Pos.of_nat (List.length d)))
          in
          let
            dec_part :=  ((of_int63 (Int63.of_Z d')) * dec_factor)%float
          in
          Some ((of_int63 (Int63.of_Z i')) + dec_part)%float
        | None => None
        end
      | None => None
      end
    | Some (i, [], e) =>
      match String2int i with
      | Some i' =>
        match String2int e with
        | Some e' =>
          let
            exp_factor := float_exp 10%float e'
          in
          Some ((of_int63 (Int63.of_Z i')) * exp_factor)%float
        | None => None
        end
      | None => None
      end
    | Some (i, d, e) =>
      match String2int i with
      | Some i' =>
        match String2uint' d with
        | Some d' =>
          let
            dec_factor := float_exp 10%float (Zneg (Pos.of_nat (List.length d)))
          in
          let
            dec_part :=  ((of_int63 (Int63.of_Z d')) * dec_factor)%float
          in
          match String2int e with
          | Some e' =>
            let
              exp_factor := float_exp 10%float e'
            in
            Some ((of_int63 (Int63.of_Z i') + dec_part) * exp_factor)%float
          | None => None
          end
        | None => None
        end
      | None => None
      end
    | _ => None
    end.

  Definition String2float (z : String) : option float :=
    String2float' (Split_float_str z).

  Definition toS (z : string) : String := list_ascii_of_string z.
  Compute (String2float' (Some (toS "0", toS "3", toS "1"))).
   *)
  (** End float stuff **)

  Definition nat_of_String (s : String) : option nat :=
    match uint_of_string (string_of_list_ascii s) with
    | Some ui => Some (Nat.of_uint ui)
    | None => None
    end.

  Definition apply_sem (pr : Label * String) : option {l : Label & sem_ty l} :=
    match pr with
    | (P3, _) =>
      Some (existT sem_ty P3 tt)
    | (NAT, s) =>
      match nat_of_String s with
      | Some n => Some (existT sem_ty NAT (N.of_nat n))
      | None => None
      end
    | (WS, _) =>
      Some (existT sem_ty WS tt)
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
Compute (extract_path "PPM" Semantic).
Extraction "Examples/PPM/Evaluation/Semantic/instance.ml" lex_sem rus.
