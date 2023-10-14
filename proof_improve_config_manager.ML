signature PROOF_IMPROVE_CONFIG_MANAGER =
sig
  type config
  val default_config : config
  val get_weight_length : unit -> real
  val get_weight_lemma : unit -> real
  val get_weight_entropy : unit -> real
  val get_weight_dependency : unit -> real
  val get_weight_symbol_to_text_ratio : unit -> real
  val get_weight_branching_factor : unit -> real
  val get_max_length : unit -> int
  val get_max_lemma : unit -> int
  val get_max_entropy : unit -> int
  val get_max_dependency : unit -> int
  val get_max_branching_factor : unit -> int
  val get_normalize_mode : unit -> string
end;

structure Proof_Improve_Config_Manager : PROOF_IMPROVE_CONFIG_MANAGER =
struct
  datatype config = Config of {
    weight_length : real,
    weight_lemma : real,
    weight_entropy : real,
    weight_dependency : real,
    weight_symbol_to_text_ratio : real,
    weight_branching_factor : real,
    max_length : int,
    max_lemma : int,
    max_entropy : int,
    max_dependency : int,
    max_branching_factor : int,
    normalize_mode : string
  }

  val default_config = Config {
    weight_length = 0.25,
    weight_lemma = 0.4,
    weight_entropy = 0.05,
    weight_dependency = 0.15,
    weight_symbol_to_text_ratio = 0.05,
    weight_branching_factor = 0.1,

    max_length = 150000,
    max_lemma = 10,
    max_entropy = 130000,
    max_dependency = 25,
    max_branching_factor = 4,
    normalize_mode = "linear" (*can be log/linear*)
  }

  fun get_weight_length () = let val Config cfg = default_config in #weight_length cfg end
  fun get_weight_lemma () = let val Config cfg = default_config in #weight_lemma cfg end
  fun get_weight_entropy () = let val Config cfg = default_config in #weight_entropy cfg end
  fun get_weight_dependency () = let val Config cfg = default_config in #weight_dependency cfg end
  fun get_weight_symbol_to_text_ratio () = let val Config cfg = default_config in #weight_symbol_to_text_ratio cfg end
  fun get_weight_branching_factor () = let val Config cfg = default_config in #weight_branching_factor cfg end
  fun get_max_length () = let val Config cfg = default_config in #max_length cfg end
  fun get_max_lemma () = let val Config cfg = default_config in #max_lemma cfg end
  fun get_max_entropy () = let val Config cfg = default_config in #max_entropy cfg end
  fun get_max_dependency () = let val Config cfg = default_config in #max_dependency cfg end
  fun get_max_branching_factor () = let val Config cfg = default_config in #max_branching_factor cfg end
  fun get_normalize_mode () = let val Config cfg = default_config in #normalize_mode cfg end

end;