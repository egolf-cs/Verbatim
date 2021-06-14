open Instance2
open L.Lex

let to_string chars =
  let buf = Buffer.create 16 in
  List.iter (Buffer.add_char buf) chars;
  Buffer.contents buf

let to_chars s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) []

let read_whole_file filename =
    let ch = open_in filename in
    let s = really_input_string ch (in_channel_length ch) in
    close_in ch;
    s

let token_to_string token =
match token with
| label, pref -> "(" ^ (to_string label) ^ ", " ^ (to_string pref) ^ ")"

let rec tokens_to_string tokens =
match tokens with
| [] -> ""
| t::[] -> (token_to_string t)
| t::ts -> (token_to_string t) ^ ",\n" ^ (tokens_to_string ts)

let print_results rs =
match rs with
| ts, rest -> (*Printf.printf "Tokens: %s\n" (tokens_to_string ts) ;*) Printf.printf "Rest: %s\n" (to_string rest)

let float_to_string f = Printf.sprintf "%.5f" f

let rec times_to_string' times =
match times with
| [] -> ""
| t::[] -> (float_to_string t)
| t::ts -> (float_to_string t) ^ "," ^ (times_to_string' ts)

let times_to_string times = Printf.sprintf "[%s]" (times_to_string' times)

let rec print_evaluation results =
match results with
| fname, code_len, ts, rest_len ->
  let oc = open_out ("results/"^fname) in
  let ts' = times_to_string ts in
  Printf.fprintf oc "{\n\"fname\":\"%s\",\n \"input_len\":%d,\n \"times\":%s,\n \"rest_len\":%d\n}" fname code_len ts' rest_len;
  close_out oc

let time f x =
    let t = Sys.time() in
    let fx = f x in
    (Sys.time() -. t, fx)

let rec n_copies n x =
match n with
| 0 -> []
| _ -> x :: (n_copies (n-1) x)

let srus = map init_srule rus
let () = Printf.printf "%.5f\n" (fst (time (map init_srule) rus))


let evaluate fname =
  let code = to_chars (read_whole_file ("data/"^fname)) in
  let codes = n_copies 2 code in
  let oc = open_out ("trace/build/"^fname) in
  let () = Printf.fprintf oc "\nBuilding Memo... " in
  let ((ms, _), _) = lex__Ms' oc rus code in
  let oc = open_out ("trace/use/"^fname) in
  let () = Printf.fprintf oc "Memo Built\nRunning Benchmark\n" in
  let trs = map (time (lex__Ms oc ms rus)) codes in
  let ts = map fst trs in
  let rest =
  match trs with
  | [] -> to_string []
  | (t, r) :: trs' -> (to_string (snd r))
  in
  let rest_len = (String.length rest) in
  (fname, List.length code, ts, rest_len)

let xs = Array.to_list (Sys.readdir "data")
let ps = map (fun x -> (print_evaluation (evaluate x))) xs
