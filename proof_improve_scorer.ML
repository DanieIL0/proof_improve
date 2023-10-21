open Term
open Thm
open Proof_Improve_Config_Manager

fun count_lemmas (st: Proof.state) : int =
  let
    val {goal, ...} = Proof.simple_goal st
    val lemma_count = length (Thm.prems_of goal)
  in
    lemma_count
  end;

fun calculate_length_score (st: Proof.state) : int =
  let
    val {context, goal, ...} = Proof.simple_goal st
    val goal_term = Thm.prop_of goal
    val goal_str = Syntax.string_of_term_global (Proof.theory_of st) goal_term

    val keywords = Thy_Header.get_keywords' context
    val tokens = Token.explode keywords Position.start goal_str
    val logical_tokens = List.filter (fn tok => not (Token.is_space tok) andalso not (Token.is_comment tok)) tokens
    val length_of_proof = List.length logical_tokens
  in
    length_of_proof
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

fun calculate_entropy_score (st: Proof.state) : int =
  let
    val {context, goal, ...} = Proof.simple_goal st
    val goal_term = Thm.prop_of goal
    val proof_str = Syntax.string_of_term_global (Proof.theory_of st) goal_term

    val keywords = Thy_Header.get_keywords' context
    val tokens = Token.explode keywords Position.start proof_str

    fun count_freqs [] dict = dict
      | count_freqs (token::toks) dict =
        let
          val key = Token.content_of token
          val count = case Symtab.lookup dict key of
                        NONE => 0
                      | SOME n => n
          val updated_dict = Symtab.update (key, count + 1) dict
        in
          count_freqs toks updated_dict
        end

    val freq_dict = count_freqs tokens empty_dict
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
  end;


fun calculate_symbol_to_text_ratio (st: Proof.state) : real =
  let
    val {goal, ...} = Proof.simple_goal st
    val goal_term = Thm.prop_of goal
    val proof_str = Syntax.string_of_term_global (Proof.theory_of st) goal_term
    val total_chars = String.size proof_str
    fun count_symbols (str, acc) =
      if String.size str = 0 then acc
      else
        let
          val ch = String.sub (str, 0)
        in
          count_symbols (String.extract (str, 1, NONE), if Char.isAlphaNum ch then acc else acc + 1)
        end
    val symbol_count = count_symbols (proof_str, 0)
    val text_count = total_chars - symbol_count
  in
    if text_count = 0 then 0.0 else real (symbol_count * 100 div text_count)
  end;


fun calculate_branching_factor (st: Proof.state) : int =
  let
    val {goal, ...} = Proof.simple_goal st
    val branches = map Thm.prems_of [goal]
    val flat_branches = List.concat branches
  in
    length flat_branches
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

signature PROOF_IMPROVE_SCORER =
sig
  val score : Proof.state -> real
end;



(*
val calcLengthScore = @{scala_function "Prooftextextractor.calculateLengthScore"}
val calcEntropyScore = @{scala_function "Prooftextextractor.calculateEntropyScore"}
val lengthScore = @{scala "Prooftextextractor.calculateLengthScore"} proofText
val entropyScore = @{scala "Prooftextextractor.calculateEntropyScore"} proofText
 does not work? - check antiquotation*)

structure Proof_Improve_Scorer : PROOF_IMPROVE_SCORER =
struct
fun score st =
  let
    val normalize_mode = get_normalize_mode ()

    val weight_length = get_weight_length ()
    val weight_lemma = get_weight_lemma ()
    val weight_entropy = get_weight_entropy ()
    val weight_dependency = get_weight_dependency ()
    val weight_symbol_to_text_ratio = get_weight_symbol_to_text_ratio ()
    val weight_branching_factor = get_weight_branching_factor ()

    val max_length = get_max_length ()
    val max_lemma = get_max_lemma ()
    val max_entropy = get_max_entropy ()
    val max_dependency = get_max_dependency ()
    val max_branching_factor = get_max_branching_factor ()

    val length_score = normalize_score (normalize_mode, calculate_length_score st, max_length)
    val _ = tracing ("Length score: " ^ Real.toString length_score)

    val lemma_score = normalize_score (normalize_mode, count_lemmas st, max_lemma)
    val _ = tracing ("Lemma score: " ^ Real.toString lemma_score)

    val entropy_score = normalize_score (normalize_mode, calculate_entropy_score st, max_entropy)
    val _ = tracing ("Entropy score: " ^ Real.toString entropy_score)

    val symbol_to_text_ratio_score = calculate_symbol_to_text_ratio st
    val _ = tracing ("Symbol to text ratio score: " ^ Real.toString symbol_to_text_ratio_score)

    val branching_factor_score = normalize_score (normalize_mode, calculate_branching_factor st, max_branching_factor)
    val _ = tracing ("Branching factor score: " ^ Real.toString branching_factor_score)

    val weighted_sum = (length_score * weight_length) + (lemma_score * weight_lemma) +
                       (entropy_score * weight_entropy) +
                       (symbol_to_text_ratio_score * weight_symbol_to_text_ratio) +
                       (branching_factor_score * weight_branching_factor)

    val total_weight = weight_length + weight_lemma + weight_entropy + weight_dependency +
                        weight_symbol_to_text_ratio + weight_branching_factor

    val normalized_score = weighted_sum  / total_weight
  in
    normalized_score
  end;
end;