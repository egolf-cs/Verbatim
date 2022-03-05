open Instance
open LXR.LitLexer
open Common

let tokens_len_str ts = List.length ts

type coq_string = char list
let str_of_coqstr (c : coq_string) : string = String.concat "" (List.map Char.escaped c)


let rec print_evaluation results =
match results with
| fname, code_len, ts, rest_len, tokens ->
  let () = List.iter (fun t -> print_endline (str_of_coqstr (show_token t))) tokens in
  let oc = open_out ("results/"^fname) in
  let tokens_len = tokens_len_str tokens in
  let ts' = times_to_string ts in
  Printf.fprintf oc "{\n\"fname\":\"%s\",\n \"input_len\":%d,\n \"times\":%s,\n \"rest_len\":%d,\n \"tokens_len\":%d\n}" fname code_len ts' rest_len tokens_len;
  (* Printf.fprintf oc "{\n\"fname\":\"%s\",\n \"input_len\":%d,\n \"times\":%s,\n \"rest_len\":%d\n}" fname code_len ts' rest_len; *)
  close_out oc


(* let srus = map init_srule rus *)
(*let lex_pre orig = lex'__M orig (init_Memos srus) srus
let lex_pre = lex' srus *)
(* let () = Printf.printf "%.5f\n" (time (map init_srule) rus) *)



let xs = Array.to_list (Sys.readdir "data")
let ps = map (fun x -> (print_evaluation (evaluate x lex 1 rus))) xs
