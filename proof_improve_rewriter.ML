signature PROOF_IMPROVE_REWRITER =
sig
  val rewrite: Proof.state -> Proof.state option
end;

structure ProofImproveRewriter: PROOF_IMPROVE_REWRITER =
struct
  open Sledgehammer
  open Sledgehammer_Prover
  
  fun rewrite (st: Proof.state) =
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
        preplay_timeout = Time.zeroTime,
        provers = ["e"],
        slices = 1,
        smt_proofs = false,
        spy = false,
        strict = false,
        timeout = Time.zeroTime,
        try0 = false,
        type_enc = NONE,
        uncurried_aliases = NONE,
        verbose = false
      }
      
      val mode = Normal
      val fact_override = {add = [], del = [], only = false}
      val (_, (outcome, _)) = Sledgehammer.run_sledgehammer params mode NONE 30 fact_override st
    in
      case outcome of
          SH_Some _ => SOME st
        | _ => NONE
    end
end;
