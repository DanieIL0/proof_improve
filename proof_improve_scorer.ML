open Proof_Improve_Config_Manager

signature PROOF_IMPROVE_SCORER =
sig
  val score :  Proof.state -> Command_Span.span list -> real * string
end;

fun get_content spans : string =
  let
    val tokens = List.concat (List.map Command_Span.content spans)
    val non_comment_tokens = List.filter (fn tok => not (Token.is_comment tok)) tokens
        fun concat_tokens (toks, acc) =
      case toks of
          [] => acc
        | tok::rest =>
            let
              val token_str = Token.content_of tok
              val updated_acc =
                if acc = "" orelse String.isSuffix " " acc orelse String.isPrefix " " token_str then
                  acc ^ token_str
                else
                  acc ^ " " ^ token_str
            in
              concat_tokens (rest, updated_acc)
            end

  in
     concat_tokens (non_comment_tokens, "")
  end;

fun count_lemmas (st: Proof.state) : int =
  let
    val {goal, ...} = Proof.simple_goal st
    val lemma_count = length (Thm.prems_of goal)
  in
    lemma_count
  end;

fun calculate_length_score sp : int =
  let
    val content_str = get_content sp
  in
    String.size content_str
  end;

val empty_dict = Symtab.empty: (int Symtab.table)

fun count_freqs [] dict = dict
  | count_freqs (x::xs) dict =
    let
      val count = case Symtab.lookup dict (Int.toString x) of
                    NONE => 0
                  | SOME n => n
      val updated_dict = Symtab.update (Int.toString x, count + 1) dict
    in
      count_freqs xs updated_dict
    end

fun build_mapping dict =
  let
    val items = Symtab.dest dict
    val sorted_items = sort (fn ((_, a: int), (_, b)) => Int.compare(a, b)) items
    val mapping = map_index (fn (i, (x, _)) => (x, Int.toString i)) sorted_items
  in
    Symtab.make mapping
  end

fun compress_list mapping lst =
  map (fn x => the (Symtab.lookup mapping (Int.toString x)) |> Int.fromString |> the) lst

fun compress_ints (ints: int list) : int list =
  let
    val freq_dict = count_freqs ints empty_dict
    val mapping = build_mapping freq_dict
    val compressed = compress_list mapping ints
  in
    compressed
  end

fun calculate_entropy_score sp : real =
  let
    val content_str = get_content sp
    val total_chars = size content_str

    fun count_char c = List.foldl (fn (ch, acc) => if ch = c then acc + 1 else acc) 0 (String.explode content_str)
    fun freq c = (Real.fromInt (count_char c)) / (Real.fromInt total_chars)
    fun entropy c = let val p = freq c in p * Math.ln p / Math.ln 2.0 end

    fun dedup_sorted_list xs =
      case xs of
          [] => []
        | [x] => [x]
        | x::y::ys => if x = y then dedup_sorted_list (y::ys) else x :: dedup_sorted_list (y::ys)

    val chars_list = String.explode content_str
                      |> sort Char.compare
                      |> dedup_sorted_list

  in
    if total_chars = 0 then 0.0
    else ~1.0 * (List.foldl (fn (c, acc) => acc + entropy c) 0.0 chars_list)
  end;

fun calculate_symbol_to_text_ratio sp : real =
  let
    val content_str = get_content sp
    val total_chars = size content_str
    val symbols_count = List.foldl (fn (ch, acc) =>
                      if Char.isAlpha ch then acc else acc + 1) 0 (String.explode content_str)
  in
    if total_chars = 0 then 0.0
    else (Real.fromInt symbols_count / Real.fromInt total_chars) * 100.0
  end;

fun calculate_depth (spans: Command_Span.span list): int =
  let
    val tokens = List.concat (List.map Command_Span.content spans)
    fun depth_aux (toks, current_depth) =
      case toks of
          [] => current_depth
        | tok::rest =>
            if Token.is_command tok then
              (case Token.content_of tok of
                 "proof" => depth_aux (rest, current_depth + 1)
               | "qed" => depth_aux (rest, current_depth - 1)
               | "done" => depth_aux (rest, current_depth - 1)
               | _ => depth_aux (rest, current_depth))
            else
              depth_aux (rest, current_depth)
  in
    (depth_aux (tokens, 0))
  end;

fun count_applys (spans: Command_Span.span list) : int =
  let
    val tokens = List.concat (List.map Command_Span.content spans)
    val apply_count = List.foldl (fn (tok, acc) =>
                      if Token.is_command tok andalso Token.content_of tok = "apply"
                      then acc + 1 else acc) 0 tokens
  in
   apply_count
  end;


fun log_normalize (value: real, max_value: real) : real =
  if value <= 0.0 then 0.0
  else
    let
      val log_value = Math.ln (value + 1.0)
      val log_max_value = Math.ln (max_value + 1.0)
      val result = 100.0 * (log_value / log_max_value)
    in
      if result > 100.0 then 100.0 else result
    end

fun linear_normalize (value: real, max_value: real) : real =
  if value <= 0.0 then 0.0
  else if max_value <= 0.0 then 0.0
  else
    let
      val result = 100.0 * (value /  max_value)
    in
      if result > 100.0 then 100.0 else result
    end;

fun normalize_score_real (mode: string, value: real, max_value: real) : real =
  case mode of
      "log" => log_normalize (value, max_value)
    | "linear" => linear_normalize (value, max_value)
    | _ => (tracing ("Error: Invalid normalization mode: " ^ mode); 0.0);

fun normalize_score_int (mode: string, value: int, max_value: int) : real =
  case mode of
      "log" => log_normalize (Real.fromInt value, Real.fromInt max_value)
    | "linear" => linear_normalize (Real.fromInt value, Real.fromInt max_value)
    | _ => (tracing ("Error: Invalid normalization mode: " ^ mode); 0.0);

structure Proof_Improve_Scorer : PROOF_IMPROVE_SCORER =
struct
fun score st sp =
  let
    val normalize_mode = get_normalize_mode ()

    val weight_length = get_weight_length ()
    val weight_lemma = get_weight_lemma ()
    val weight_entropy = get_weight_entropy ()
    val weight_symbol_to_text_ratio = get_weight_symbol_to_text_ratio ()
    val weight_depth = get_weight_depth ()
    val weight_apply = get_weight_apply ()

    val max_length = get_max_length ()
    val max_lemma = get_max_lemma ()
    val max_entropy = get_max_entropy ()
    val max_depth  = get_max_depth ()
    val max_apply = get_max_apply ()

    val length_score = normalize_score_int (normalize_mode, calculate_length_score sp, max_length)
    val length_report = "Length score: " ^ Real.toString length_score ^ "\n"

    val lemma_score = normalize_score_int (normalize_mode, count_lemmas st, max_lemma)
    val lemma_report = "Lemma score: " ^ Real.toString lemma_score ^ "\n"

    val entropy_score = normalize_score_real (normalize_mode, calculate_entropy_score sp, max_entropy)
    val entropy_report = "Entropy score: " ^ Real.toString entropy_score ^ "\n"

    val symbol_to_text_ratio_score = calculate_symbol_to_text_ratio sp
    val symbol_to_text_ratio_report = "Symbol to text ratio score: " ^ Real.toString symbol_to_text_ratio_score ^ "\n"

    val depth_score = normalize_score_int (normalize_mode, calculate_depth sp, max_depth)
    val depth_report = "Proof depth score: " ^ Real.toString depth_score ^ "\n"

    val apply_score = normalize_score_int (normalize_mode, count_applys sp, max_apply)
    val apply_report = "Apply score: " ^ Real.toString apply_score ^ "\n"

    val weighted_sum = (length_score * weight_length) + (lemma_score * weight_lemma) +
                         (entropy_score * weight_entropy) + (depth_score * weight_depth) +
                         (symbol_to_text_ratio_score * weight_symbol_to_text_ratio) +
                         (apply_score * weight_apply)

      val total_weight = weight_length + weight_lemma + weight_entropy +
                         weight_symbol_to_text_ratio + weight_depth + weight_apply

    val normalized_score = weighted_sum / total_weight

    val full_report = length_report ^ lemma_report ^ entropy_report ^
                      symbol_to_text_ratio_report ^ depth_report ^ apply_report
                      ^ "Span: " ^ (get_content sp) ^ "\n"
  in
    (normalized_score, full_report)
  end;
end