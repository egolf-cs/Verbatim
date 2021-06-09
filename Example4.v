Require Import List.
Import ListNotations.

Require Import Ascii.
Require Import String.
Open Scope string_scope.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

From Verbatim Require Import regex.
From Verbatim Require Import state.
From Verbatim Require Import Table.
From Verbatim Require Import DFA.
From Verbatim Require Import lexer.impl.
From Verbatim Require Import Utils.ltac.
From Verbatim Require Import Utils.asciiFinite.
From Verbatim Require Import Utils.ascii_order.
From Verbatim Require Import concrete1.

From Verbatim Require Import memo.memo.
From Verbatim Require Import memo.impl.
From Verbatim Require Import concrete3.

Module Export MEM <: memo.T.
  
  Module Export STT <: state.T.
    
    Module TabT <: Table.T.
      
      Module Export R <: regex.T.
        
        Module Export Ty <: SIGMA.
          
          Definition Sigma : Type := ascii.
          Definition SigmaEnum : list Sigma := asciiEnum.
          Definition compareT := ascii_order.
          Definition compareT_eq := ascii_order_eq.
          Definition compareT_trans := ascii_order_trans.

          Lemma Sigma_finite : forall a : Sigma, In a SigmaEnum.
          Proof. apply ascii_finite. Qed.

          Lemma Sigma_dec : forall a a' : Sigma, {a = a'} + {a <> a'}.
          Proof. apply ascii_dec.  Qed.
          
        End Ty.
        
        Module Export Defs := regex.DefsFn Ty.
        
      End R.

      Module TabTy <: TABLE R := FTable R.

      Module Export Defs := DefsFn R TabTy.

    End TabT.

    Module Export R := TabT.R.
    Import R.Ty.
    Export R.Defs.Helpers.
    
    Module Export Ty <: STATE R.

      Module Export D := DFAFn TabT. 

      Definition Pointer : Type := regex.
      Definition defPointer : Pointer := EmptySet.
      Definition Delta : Type := TabT.TabTy.Table * TabT.R.Defs.reFS.t.
      Definition defDelta := (TabT.TabTy.emptyTable, TabT.TabTy.reFS.empty).
      Definition State := prod Pointer Delta.
      Definition defState := (defPointer, defDelta).
      
      Definition transition (a : Sigma) (e : State) : State :=
        match e with
          (x, (y, z)) =>
          match DFAtransition a (x,y,z) with
            (x',y',z') => (x',(y',z'))
          end
        end.
      Definition transition_list (bs : list Sigma) (e : State) : State :=
        match e with
          (x, (y, z)) =>
          match DFAtransition_list bs (x,y,z) with
            (x',y',z') => (x',(y',z'))
          end
        end.
      Lemma transition_list_nil : forall fsm,
          transition_list [] fsm = fsm.
      Admitted.
      Lemma transition_list_cons : forall bs a fsm,
          transition_list (a :: bs) fsm = transition_list bs (transition a fsm).
      Admitted.
      
      Definition accepts (s : String) (e : State) : bool :=
        match e with
          (x, (y, z)) => DFAaccepts s (x, y, z)
        end.
      Definition accepting (e : State) :=
        match e with
          (x, (y, z)) => DFAaccepting (x, y, z)
        end.

      Lemma accepts_nil: forall(fsm : State), accepting fsm = accepts [] fsm.
      Proof. intros fsm. reflexivity. Qed.

      Lemma accepts_transition : forall cand a fsm,
          accepts cand (transition a fsm) = accepts (a :: cand) fsm.
      Proof. Admitted.

      Definition init_state (r : regex) : State :=
        match regex2dfa r with
          (x, y, z) => (x, (y, z))
        end.
      Definition init_state_inv (r : State) : regex :=
        match r with
          (x, (y, z)) => dfa2regex (x, y, z)
        end.
      
      Lemma invert_init_correct : forall r s,
          exp_match s (init_state_inv (init_state r)) <-> exp_match s r.
      Proof. intros. simpl. apply TabT.Defs.FillTable.canon_equiv. Qed.
      
      Lemma accepts_matches : forall(s : String) (e : regex),
          true = accepts s (init_state e) <-> exp_match s e.
      Proof.
        split; intros.
        - symmetry in H. apply r2d_accepts_match. auto.
        - symmetry. apply r2d_accepts_match. auto.
      Qed.

      Definition accepting_dt_list : forall bs e,
          accepting (transition_list bs (init_state e))
          = accepting (init_state (derivative_list bs e)).
      Proof. Admitted.

      (*Lemma stt_dec : forall (s1 s2 : State), {s1 = s2} + {s1 <> s2}.
      Proof.
        intros. decide equality; clear s1 s2.
        - clear a0 a p. try apply reFS.eq_dec. admit.
        - clear b t. decide equality.
          + clear a1 a0 r a p. decide equality.
            * clear a a0 t0 t b. try apply reFS.eq_dec. admit.
            * clear b t b0 t1. admit.
          + clear a p b t. decide equality.
      Admitted.*)

      Definition pointer_compare (s1 s2 : Pointer) : comparison :=
        re_compare s1 s2.

      Lemma pointer_compare_eq : forall x y,
          pointer_compare x y = Eq <-> x = y.
      Proof. apply re_compare_eq. Qed.

      Lemma pointer_compare_trans : forall c x y z,
          pointer_compare x y = c -> pointer_compare y z = c -> pointer_compare x z = c.
      Proof. apply re_compare_trans. Qed.
      
    End Ty.
    
    Module Export Defs := state.DefsFn R Ty.

  End STT.

  Module Export MemTy <: MEMO STT := FMemo STT.

  Module Export Defs := memo.MemoDefsFn STT MemTy.

End MEM.

Import MEM.STT.
Module L := memo.impl.ImplFn MEM.
Import L.

Definition toS (z : string) : String := list_ascii_of_string z.
Definition Sig_of_N (n : nat) : Sigma := ascii_of_nat 65.
Fixpoint range' (n : nat) : (list nat) :=
  match n with
  | 0 => []
  | S n' => (range' n') ++ [n']
  end.

Fixpoint range (n1 n2 : nat) : (list nat) := map (plus n1) (range' (n2 - n1 + 1)).

(*** White Space ***)
(* [ \t\n\r] *)
Definition chars_ws := map Char (map ascii_of_nat [9;10;13;32]).
Definition ru_ws : Rule := (toS "WS", Plus (IterUnion chars_ws)).
(**)

(*** Numbers ***)
(* [0-9] *)
Definition ascii_digit := range 48 57.
Definition chars_digit := map Char (map ascii_of_nat ascii_digit).
Definition regex_digit := IterUnion chars_digit.

(* [1-9], nz = non-zero *)
Definition ascii_nz_digit := range 49 57.
Definition chars_nz_digit := map Char (map ascii_of_nat ascii_nz_digit).
Definition regex_nz_digit := IterUnion chars_nz_digit.

(* "fragment INT" *)
Definition regex_zero := Char (ascii_of_nat 48).
Definition regex_nzero := App regex_nz_digit (Star regex_digit).
Definition regex_int := Union regex_zero regex_nzero.

(* '-'? *)
Definition regex_sign := Char (ascii_of_nat 45).
Definition regex_sign_option := Optional regex_sign.
(* ('.' [0-9] +)? *)
Definition regex_dec_point := Char (ascii_of_nat 46).
Definition regex_dec := App regex_dec_point (Plus regex_digit).
Definition regex_dec_option := Optional regex_dec.
(* fragment EXP : [Ee] [+\-]? INT *)
Definition regex_Ee := Union (Char (ascii_of_nat 69)) (Char (ascii_of_nat 101)).
Definition regex_pm := Union (Char (ascii_of_nat 43)) (Char (ascii_of_nat 45)).
Definition regex_pm_option := Optional regex_pm.
Definition regex_exp := IterApp [regex_Ee;regex_pm_option;regex_int].
Definition regex_exp_option := Optional regex_exp.

(* NUMBER : '-'? INT ('.' [0-9] +)? EXP? *)
Definition regex_number := IterApp [regex_sign_option;regex_int;regex_dec_option;regex_exp_option].
Definition ru_number := (toS "NUMBER", regex_number).
(**)

(*** STRING ***)
Definition ascii_lower := range 97 122.
Definition chars_lower := map Char (map ascii_of_nat ascii_lower).
Definition regex_lower := IterUnion chars_lower.
Definition ascii_upper := range 65 90.
Definition chars_upper := map Char (map ascii_of_nat ascii_upper).
Definition regex_upper := IterUnion chars_upper.
(* not sure what to include for punctuation, but here's almost all of it. *)
(* Maybe too much, and no consideration for escaping characters. *)
(* In theory this is meant to support unicode... *)
Definition ascii_punc : (list nat) := [32;33] ++ (range 35 47) ++ (range 58 64) ++ (range 91 96) ++ (range 123 126).
Definition chars_punc := map Char (map ascii_of_nat ascii_punc).
Definition regex_punc := IterUnion chars_punc.
Definition regex_char := IterUnion [regex_lower;regex_upper;regex_digit;regex_punc].
Definition regex_par := Char (ascii_of_nat 34).
(* ru_string *)
Definition regex_string := IterApp [regex_par;(Star regex_char);regex_par].
Definition ru_string := (toS "STRING", regex_string).
(**)

(*** keywords ***)
Definition regex_true := IterApp (map Char (toS "true")).
Definition ru_true := (toS "TRUE", regex_true).
Definition regex_false := IterApp (map Char (toS "false")).
Definition ru_false := (toS "FALSE", regex_false).
Definition regex_null := IterApp (map Char (toS "null")).
Definition ru_null := (toS "NULL", regex_null).

(*** brack, brace, colon, comma ***)
Definition regex_colon := IterApp (map Char (toS ":")).
Definition ru_colon := (toS "COLON", regex_colon).
Definition regex_comma := IterApp (map Char (toS ",")).
Definition ru_comma := (toS "COMMA", regex_comma).
Definition regex_lbrack := IterApp (map Char (toS "[")).
Definition ru_lbrack := (toS "LEFT_BRACKET", regex_lbrack).
Definition regex_rbrack := IterApp (map Char (toS "]")).
Definition ru_rbrack := (toS "RIGHT_BRACKET", regex_rbrack).
Definition regex_lbrace := IterApp (map Char (toS "{")).
Definition ru_lbrace := (toS "LEFT_BRACE", regex_lbrace).
Definition regex_rbrace := IterApp (map Char (toS "}")).
Definition ru_rbrace := (toS "RIGHT_BRACE", regex_rbrace).


(*** Compile rules and export ***)
Definition rus : list Rule := [ru_ws;ru_number;ru_string;ru_true;ru_false;ru_null;ru_colon;ru_comma;ru_lbrack;ru_rbrack;ru_lbrace;ru_rbrace].

Definition lex := lex__M.
Definition lex' := lex'__M.

Extraction "Evaluation/Example/instance.ml" lex rus.


