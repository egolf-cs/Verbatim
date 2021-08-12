Require Import List.
Import ListNotations.

Require Import String.
Open Scope string_scope.
Require Import Ascii.

From Verbatim Require Import Utils.asciiSigma.

Module Export extract_helpers.
       
  Inductive extract_opt : Type :=
  | Literal
  | Semantic.

  Definition extract_path (lang : string) (opt : extract_opt) : string :=
    let opt' := match opt with
                | Literal => "Literal"
                | Semantic => "Semantic"
                end
    in
    concat "/" ["Examples";lang;"Evaluation";opt';"instance.ml"].

End extract_helpers.

Module regex_builders (Import R : regex.T).

  Import Ty.
  Export Helpers.

  Definition Char_of_nat (n : nat) : regex :=
    Char (ascii2Sigma (ascii_of_nat n)).

  Definition asciiUnion (bs : list ascii) : regex :=
    IterUnion (map (fun x => Char (ascii2Sigma x)) bs).
  
  Definition stringUnion (bs : string) : regex :=
    asciiUnion (list_ascii_of_string bs).

  Definition asciiApp (bs : list ascii) : regex :=
    IterApp (map (fun x => Char (ascii2Sigma x)) bs).

  Definition stringApp (bs : string) : regex :=
    asciiApp (list_ascii_of_string bs).


End regex_builders.

Module prebuilt_regexes (Import R : regex.T).

  Module Export builders := regex_builders R.

  (*** Whitespace ***)
  Module Export whitespace.

    Definition tab_ascii : ascii := ascii_of_nat 9.              (* \t *)
    Definition linebreak_ascii : ascii := ascii_of_nat 10.       (* \n *)
    Definition carriage_return_ascii : ascii := ascii_of_nat 13. (* \r *)
    Definition space_ascii : ascii := ascii_of_nat 32.

    (* Includes tab \t, newline \n, and space *)
    Definition ws_chars : list ascii :=
      [tab_ascii; linebreak_ascii; space_ascii].
    Definition ws_re : regex := Plus (asciiUnion ws_chars).
                
    (* Includes tab \t, newline \n, carriage return \r, and space *)
    Definition ws_carr_chars : list ascii :=
      [tab_ascii; linebreak_ascii; carriage_return_ascii; space_ascii].
    Definition ws_carr_re : regex := Plus (asciiUnion ws_carr_chars).

  End whitespace.

  
  (*** Numbers ***)
  Module Export numbers.
    
    Definition digit_re := stringUnion "0123456789".
    Definition nz_digit_re := stringUnion "123456789".
    Definition zero_re := stringApp "0".

    (** * * Leading zeros denoted by lz * **)

    
    (** Positives exclude 0 **)
    Definition pos_lz_re := IterApp [(Star digit_re); nz_digit_re; (Star digit_re)].
    Definition pos_re := App nz_digit_re (Star digit_re).

    
    (** Naturals include 0 **)
    Definition nat_lz_re := Plus digit_re.
    Definition nat_re := Union zero_re pos_re.

    
    (** Integers; Be sure to handle -0 appropriately for your language **)
    Definition int_lz_re := App (Optional (stringApp "-")) nat_lz_re.
    Definition int_re := App (Optional (stringApp "-")) nat_re.
    Definition int_no_neg0_lz_re := Union zero_re (App (Optional (stringApp "-")) pos_lz_re).
    Definition int_no_neg0_re := Union zero_re (App (Optional (stringApp "-")) pos_re).

    
    (** Decimal numbers; 
        Note: One or both of the integer/decimal part may be optional
        for your language **)
    Definition dec_part_re := App (stringApp ".") nat_lz_re.
    
    (* Optional decimal part *)
    Definition dec_lz_re := App int_lz_re (Optional dec_part_re).
    Definition dec_re := App int_re (Optional dec_part_re).
    Definition dec_no_neg0_lz_re := App int_no_neg0_lz_re (Optional dec_part_re).
    Definition dec_no_neg0_re := App int_no_neg0_re (Optional dec_part_re).
    
    (* Required decimal part *)
    Definition proper_dec_lz_re := App int_lz_re dec_part_re.
    Definition proper_dec_re := App int_re dec_part_re.
    Definition proper_dec_no_neg0_lz_re := App int_no_neg0_lz_re dec_part_re.
    Definition proper_dec_no_neg0_re := App int_no_neg0_re dec_part_re.
    
    (* Optional integer part, required decimal part *)
    (** * * For later * **)
  End numbers.


  (*** Strings ***)

  Module Export Strings_regex.
    
    Definition AZ_re := stringUnion "ABCDEFGHIJKLMNOPQRSTUVWXYZ".
    Definition az_re := stringUnion "abcdefghijklmnopqrstuvwxyz".
    (* Does not include white space, double quote, backslash, or ascii 0-31 *)
    Definition punc_re := stringUnion "!#$%&()*+,-./:;<=>?@[]^_`{¦}~'".
    Definition quote_re := Char_of_nat 34.
    Definition esc_quote_re := App (stringApp "\") quote_re.
    Definition esc_bslash_re := stringApp "\\".
    (** * * Your language may vary in what is a character, *)
    (** *   what is escaped and how, and what delimits a string. * *)
    Definition char_re :=
      IterUnion [AZ_re; az_re; digit_re; ws_re; punc_re; esc_quote_re; esc_bslash_re].
    Definition string_re := IterApp [quote_re; (Star char_re); quote_re].

  End Strings_regex.

End prebuilt_regexes.
    
