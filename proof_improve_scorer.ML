open Proof_Improve_Config_Manager

signature PROOF_IMPROVE_SCORER =
sig
  val score :  Proof.state -> Command_Span.span -> real
end;

fun get_content (sp: Command_Span.span) : string =
  let
    val tokens = Command_Span.content sp
    val non_comment_tokens = List.filter (fn tok => not (Token.is_comment tok)) tokens

    fun traverse (toks, current_depth, acc) =
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
              val new_depth =
                if Token.is_command tok andalso token_str = "proof" then
                  current_depth + 1
                else if Token.is_command tok andalso token_str = "qed" then
                  current_depth - 1
                else
                  current_depth
            in
              if new_depth = 0 then updated_acc
              else traverse (rest, new_depth, updated_acc)
            end

  in
    traverse (non_comment_tokens, 0, "")
  end;

fun count_lemmas (st: Proof.state) : real =
  let
    val {goal, ...} = Proof.simple_goal st
    val lemma_count = length (Thm.prems_of goal)
  in
    Real.fromInt lemma_count
  end;

fun calculate_length_score (sp: Command_Span.span) : real =
  let
    val content_str = get_content sp
  in
    Real.fromInt (String.size content_str)
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

fun calculate_entropy_score (sp: Command_Span.span) : real =
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

fun calculate_symbol_to_text_ratio (sp: Command_Span.span) : real =
  let
    val content_str = get_content sp
    val total_chars = size content_str
    val symbols_count = List.foldl (fn (ch, acc) =>
                      if Char.isAlpha ch then acc else acc + 1) 0 (String.explode content_str)
  in
    if total_chars = 0 then 0.0
    else (Real.fromInt symbols_count / Real.fromInt total_chars) * 100.0
  end;

fun calculate_depth (sp: Command_Span.span) : real =
  let
    val tokens = Command_Span.content sp

    fun depth_aux (toks, current_depth, max_depth) =
      case toks of
          [] => max_depth
        | tok::rest =>
            if Token.is_command tok andalso Token.content_of tok = "proof" then
              depth_aux (rest, current_depth + 1, Int.max (current_depth + 1, max_depth))
            else if Token.is_command tok andalso Token.content_of tok = "qed" then
              depth_aux (rest, current_depth - 1, max_depth)
            else
              depth_aux (rest, current_depth, max_depth)
  in
   Real.fromInt (depth_aux (tokens, 0, 0))
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

fun normalize_score (mode: string, value: real, max_value: real) : real =
  case mode of
      "log" => log_normalize (value, max_value)
    | "linear" => linear_normalize (value, max_value)
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

    val max_length = get_max_length ()
    val max_lemma = get_max_lemma ()
    val max_entropy = get_max_entropy ()
    val max_depth  = get_max_depth ()

    val length_score = normalize_score (normalize_mode, calculate_length_score sp, max_length)
    val _ = tracing ("Length score: " ^ Real.toString length_score)

    val lemma_score = normalize_score (normalize_mode, count_lemmas st, max_lemma)
    val _ = tracing ("Lemma score: " ^ Real.toString lemma_score)

    val entropy_score = normalize_score (normalize_mode, calculate_entropy_score sp, max_entropy)
    val _ = tracing ("Entropy score: " ^ Real.toString entropy_score)

    val symbol_to_text_ratio_score = calculate_symbol_to_text_ratio sp
    val _ = tracing ("Symbol to text ratio score: " ^ Real.toString symbol_to_text_ratio_score)

    val depth_score = normalize_score (normalize_mode, calculate_depth sp, max_depth)
    val _ = tracing ("Proof depth score: " ^ Real.toString depth_score)

    val weighted_sum = (length_score * weight_length) + (lemma_score * weight_lemma) +
                       (entropy_score * weight_entropy) + (depth_score * weight_depth) +
                       (symbol_to_text_ratio_score * weight_symbol_to_text_ratio)

    val total_weight = weight_length + weight_lemma + weight_entropy +
    weight_symbol_to_text_ratio + weight_depth

    val normalized_score = weighted_sum  / total_weight
  in
    normalized_score
  end;
end;