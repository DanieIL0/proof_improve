open Term
open Thm
open ProofImproveConfigManager

fun calculate_dependency_score (st: Proof.state) : int =
  let
    val ctxt = Proof.context_of st
    val thms = Proof.the_facts st
    fun is_external_thm thm =
      (case try (Proof_Context.get_fact ctxt) (Facts.named (Thm.get_name_hint thm)) of
         NONE => true
       | SOME _ => false)
    val external_thms_count = length (filter is_external_thm thms)
    val facts_count = length thms
  in
    external_thms_count + facts_count
  end;

fun count_lemmas (st: Proof.state) : int =
  let
    val {goal, ...} = Proof.simple_goal st
    val lemma_count = length (Thm.prems_of goal)
  in
    lemma_count
  end;

fun calculate_length_score (st: Proof.state) : int =
  let
    val {goal, ...} = Proof.simple_goal st
    val goal_term = Thm.prop_of goal
    val goal_str = Syntax.string_of_term_global (Proof.theory_of st) goal_term
    val length_of_proof = String.size goal_str
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
    val {goal, ...} = Proof.simple_goal st
    val goal_term = Thm.prop_of goal
    val proof_str = Syntax.string_of_term_global (Proof.theory_of st) goal_term
    val ints = map Char.ord (String.explode proof_str)
    val compressed_ints = compress_ints ints
    val entropy_score = length compressed_ints
  in
    entropy_score
  end;

fun calculate_symbol_to_text_ratio (st: Proof.state) : int =
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
    if text_count = 0 then 0 else symbol_count * 100 div text_count
  end;

fun calculate_branching_factor (st: Proof.state) : int =
  let
    val {goal, ...} = Proof.simple_goal st
    val branches = map Thm.prems_of [goal]  (* Wrapping goal in list as we have a single goal *)
    val flat_branches = List.concat branches
  in
    length flat_branches
  end;

fun ln_taylor_series (x: real) (n: int) =
  if n = 0 then x
  else
    let
      val term = if n mod 2 = 0 then ~ (Math.pow (x, 2.0 * real n - 1.0)) else Math.pow (x, 2.0 * real n - 1.0)
    in
      term / (real (2 * n - 1)) + ln_taylor_series x (n - 1)
    end

fun log_normalize (value: int, max_value: int) : int =
  if value <= 0 then 0
  else
    let
      val log_value = ln_taylor_series (real (value + 1)) 10
      val log_max_value = ln_taylor_series (real (max_value + 1)) 10
    in
      Real.round (100.0 * (log_value / log_max_value))
    end

signature PROOF_IMPROVE_SCORER =
sig
  val score : Proof.state -> int
end;

structure ProofImproveScorer : PROOF_IMPROVE_SCORER =
struct
fun score st =
  let
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

    val length_score = real (log_normalize (calculate_length_score st, max_length))
    val lemma_score = real (log_normalize (count_lemmas st, max_lemma))
    val entropy_score = real (log_normalize (calculate_entropy_score st, max_entropy))
    val dependency_score = real (log_normalize (calculate_dependency_score st, max_dependency))
    val symbol_to_text_ratio_score = real (calculate_symbol_to_text_ratio st)
    val branching_factor_score = real (log_normalize (calculate_branching_factor st, max_branching_factor))

    val weighted_sum = (length_score * weight_length) + (lemma_score * weight_lemma) +
                       (entropy_score * weight_entropy) + (dependency_score * weight_dependency) +
                       (symbol_to_text_ratio_score * weight_symbol_to_text_ratio) +
                       (branching_factor_score * weight_branching_factor)

    val total_weight = weight_length + weight_lemma + weight_entropy + weight_dependency +
                        weight_symbol_to_text_ratio + weight_branching_factor

    val normalized_score = weighted_sum * 100.0 / total_weight
  in
    Real.round normalized_score
  end;
end;