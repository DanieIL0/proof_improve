open Term
open Thm
open Proof_Improve_Config_Manager
open Command_Span
open Token

signature PROOF_IMPROVE_SCORER =
sig
  val score :  Proof.state -> span -> real
end;


fun count_lemmas (st: Proof.state) : int =
  let
    val {goal, ...} = Proof.simple_goal st
    val lemma_count = length (Thm.prems_of goal)
  in
    lemma_count
  end;

fun calculate_length_score (sp: Command_Span.span) : int =
  let
    val tokens = Command_Span.content sp
    val non_comment_tokens = List.filter (fn tok => not (Token.is_comment tok)) tokens
    val is_end_keyword = Token.keyword_with (fn s => s = "by" orelse s = "done" orelse s = "qed")

    fun count_length (tok, acc) =
      if is_end_keyword tok then
        acc
      else
        acc + String.size (Token.content_of tok)

  in
    List.foldl count_length 0 non_comment_tokens
  end

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

fun calculate_entropy_score (sp: Command_Span.span) : int =
  let
    val tokens = Command_Span.content sp
    val non_comment_tokens = List.filter (fn tok => not (Token.is_comment tok)) tokens
    val is_end_keyword = Token.keyword_with (fn s => s = "by" orelse s = "done" orelse s = "qed")

    fun count_freqs [] dict = dict
      | count_freqs (token::toks) dict =
        if is_end_keyword token then
          dict
        else
          let
            val key = Token.content_of token
            val count = case Symtab.lookup dict key of
                          NONE => 0
                        | SOME n => n
            val updated_dict = Symtab.update (key, count + 1) dict
          in
            count_freqs toks updated_dict
          end

    val freq_dict = count_freqs non_comment_tokens Symtab.empty
    val total_tokens = fold (fn (_, cnt) => fn acc => acc + cnt) (Symtab.dest freq_dict) 0
    val entropy_score =
      fold (fn (_, cnt) => fn acc =>
        let
          val probability = Real.fromInt cnt / Real.fromInt total_tokens
        in
          acc - (probability * Math.ln probability)
        end) (Symtab.dest freq_dict) 0.0
  in
    Real.round entropy_score
  end

fun calculate_symbol_to_text_ratio (sp: Command_Span.span) : real =
  let
    val tokens = Command_Span.content sp
    val non_comment_tokens = List.filter (fn tok => not (Token.is_comment tok)) tokens

    val total_chars =
      List.foldl (fn (tok, acc) => acc + String.size (Token.content_of tok)) 0 non_comment_tokens

    fun count_symbols str =
      let
        fun aux (i, len, acc) =
          if i = len then acc
          else
            let
              val ch = String.sub (str, i)
            in
              aux (i + 1, len, if Char.isAlphaNum ch then acc else acc + 1)
            end
      in
        aux (0, String.size str, 0)
      end

    val symbol_count =
      List.foldl (fn (tok, acc) => acc + count_symbols (Token.content_of tok)) 0 non_comment_tokens

    val text_count = total_chars - symbol_count
  in
    if text_count = 0 then 0.0 else Real.fromInt symbol_count / Real.fromInt text_count
  end


fun calculate_depth (sp: Command_Span.span) : int =
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
    depth_aux (tokens, 0, 0)
  end;

fun log_normalize (value: int, max_value: int) : real =
  if value <= 0 then 0.0
  else
    let
      val log_value = Math.ln (real (value + 1))
      val log_max_value = Math.ln (real (max_value + 1))
      val result = 100.0 * (log_value / log_max_value)
    in
      if result > 100.0 then 100.0 else result
    end

fun linear_normalize (value: int, max_value: int) : real =
  if value <= 0 then 0.0
  else if max_value <= 0 then 0.0
  else
    let
      val result = 100.0 * (real value / real max_value)
    in
      if result > 100.0 then 100.0 else result
    end;

fun normalize_score (mode: string, value: int, max_value: int) : real =
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