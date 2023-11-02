signature PROOF_IMPROVE_CONFIG_MANAGER =
sig
  type config
  val default_config : config
  val get_weight_length : unit -> real
  val get_weight_lemma : unit -> real
  val get_weight_entropy : unit -> real
  val get_weight_depth : unit -> real
  val get_weight_symbol_to_text_ratio : unit -> real
  val get_max_length : unit -> real
  val get_max_lemma : unit -> real
  val get_max_entropy : unit -> real
  val get_max_depth : unit -> real
  val get_normalize_mode : unit -> string
end;

structure Proof_Improve_Config_Manager : PROOF_IMPROVE_CONFIG_MANAGER =
struct
  datatype config = Config of {
    weight_length : real,
    weight_lemma : real,
    weight_entropy : real,
    weight_symbol_to_text_ratio : real,
    weight_depth : real,
    max_length : real,
    max_lemma : real,
    max_entropy : real,
    max_depth : real,
    normalize_mode : string
  }

  val default_config = Config {
    weight_length = 0.35,
    weight_lemma = 0.3,
    weight_entropy = 0.2,
    weight_symbol_to_text_ratio = 0.05,
    weight_depth = 0.1,

    max_length = 100000.0,
    max_lemma = 10.0,
    max_entropy = 8.0,
    max_depth = 5.0,
    normalize_mode = "linear" (*can be log/linear*)
  }

  fun get_weight_length () = let val Config cfg = default_config in #weight_length cfg end
  fun get_weight_lemma () = let val Config cfg = default_config in #weight_lemma cfg end
  fun get_weight_entropy () = let val Config cfg = default_config in #weight_entropy cfg end
  fun get_weight_symbol_to_text_ratio () = let val Config cfg = default_config in #weight_symbol_to_text_ratio cfg end
  fun get_weight_depth () = let val Config cfg = default_config in #weight_depth cfg end
  fun get_max_length () = let val Config cfg = default_config in #max_length cfg end
  fun get_max_lemma () = let val Config cfg = default_config in #max_lemma cfg end
  fun get_max_entropy () = let val Config cfg = default_config in #max_entropy cfg end
  fun get_max_depth () = let val Config cfg = default_config in #max_depth cfg end
  fun get_normalize_mode () = let val Config cfg = default_config in #normalize_mode cfg end

end;