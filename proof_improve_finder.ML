signature PROOF_IMPROVE_FINDER =
sig
  val find: Proof.state -> Proof.state option
end;

structure Proof_Improve_Finder: PROOF_IMPROVE_FINDER =
struct
  open Sledgehammer
  open Sledgehammer_Prover

  fun find (st: Proof.state) =
    let
      val params = {
        abduce = NONE,
        compress = NONE,
        debug = false,
        expect = "",
        fact_filter = NONE,
        fact_thresholds = (0.0, 0.0),
        falsify = NONE,
        induction_rules = NONE,
        isar_proofs = NONE,
        lam_trans = NONE,
        learn = false,
        max_facts = NONE,
        max_mono_iters = NONE,
        max_new_mono_instances = NONE,
        max_proofs = 1,
        minimize = true,
        overlord = false,
        preplay_timeout = Time.fromSeconds 30,
        provers = ["e"],
        slices = 1,
        smt_proofs = false,
        spy = false,
        strict = false,
        timeout = Time.fromSeconds 30,
        try0 = false,
        type_enc = NONE,
        uncurried_aliases = NONE,
        verbose = false
      }

    val mode = Normal
    val fact_override = {add = [], del = [], only = false}
    val (_, (outcome, _)) = Sledgehammer.run_sledgehammer params mode NONE 30 fact_override st
    fun analyze_preplay_results (preplay_results: preplay_result list) =

      let
        val unfolded_results = map (fn (method, (play_outcome, stature_list)) =>
          let
        val (scope, status) = case stature_list of
        (s, stat)::_ => (s, stat)
          in
            { method = method,
              play_outcome = play_outcome,
              scope = scope,
              status = status }
          end
        ) preplay_results

        val best_method = st
      in
        best_method
      end

    fun generate_rewritten_proof (best_method) = SOME st

  in
    case outcome of
      SH_Some (prover_result, preplay_results) =>
        (case prover_result of
          Success =>
            let
              val best_method = analyze_preplay_results preplay_results
              val rewritten_proof = generate_rewritten_proof best_method
            in
               rewritten_proof
            end
        | _ => SOME st)
    | _ => SOME st
  end
end