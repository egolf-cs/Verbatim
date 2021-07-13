Require Import List.
Import ListNotations.

Require Import String.
Open Scope string_scope.
Require Import Ascii.

Require Import BinInt.

(*Require Import PrimFloat.
Require Import Int63.

Require Extraction.
Require ExtrOCamlInt63.
Require ExtrOCamlFloats.*)

Require Import DecimalString.
Import NilEmpty.

From Verbatim Require Import ExampleLexer.
Import ExampleLexer.MEM.STT.R.Defs.
(*From Verbatim Require FloatLexer.
Import FloatLexer.Splitter.*)
From Verbatim Require Import actions.impl.

From Verbatim Require Import ltac.


Module Import STT <: state.T := ExampleLexer.MEM.STT.

Module Import LXR <: LEXER STT.

  Definition lex := ExampleLexer.C.IMPL.Lex.lex_M.
  Definition lex_sound := ExampleLexer.C.lex_sound__M.
  Definition lex_complete := ExampleLexer.C.lex_complete__M.

End LXR.

Module USER <: SEM_USER STT.

  Definition sem_ty (l : Label) : Type :=
    match l with
    | INT => Z
    | FLOAT => Z
    | STRING => string
    | TRUE => unit
    | FALSE => unit
    | NULL => unit
    | COLON => unit
    | COMMA => unit
    | LEFT_BRACKET => unit
    | RIGHT_BRACKET => unit
    | LEFT_BRACE => unit
    | RIGHT_BRACE => unit
    | WS => unit
    end.


  Set Printing All.
  Compute "0".
  Compute "-".
  Unset Printing All.

  (* Doesn't check for leading 0 or -0 *)
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

  (* This is probably not super safe *)
  Definition String2float (z : String) : option float :=
    String2float' (Split_float_str z).

  Definition toS (z : string) : String := list_ascii_of_string z.
  Compute (String2float' (Some (toS "0", toS "3", toS "1"))).
   *)

  
  Definition apply_sem (pr : Label * String) : option {l : Label & sem_ty l} :=
    match pr with
    | (INT, z) =>
      match (String2int z) with
      | Some i => Some (existT sem_ty INT i)
      | None => None
      end
    | (FLOAT, z) => 
      match (String2int z) with
      | Some i => Some (existT sem_ty FLOAT i)
      | None => None
      end
    | (STRING, z) => Some (existT _ STRING (string_of_list_ascii z)) 
    | (L, _)      => Some (existT _ L tt)
    end.


  Lemma label_carries : forall l l' s t,
      apply_sem (l, s) = Some (existT sem_ty l' t)
      -> l = l'.
  Proof.
    intros. destruct l; destruct l'; auto; sis; repeat dm; repeat inj_all; discriminate.
  Qed.
    
End USER.

Module Import SemLexer := SemLexerFn STT LXR USER.
Import SemLexer.Impl.


Set Warnings "-extraction-opaque-accessed,-extraction".
Extraction "../../Evaluation/semantic/instance.ml" lex_sem rus.
