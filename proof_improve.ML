(*  Title:      HOL/Tools/proof_improve.ML
    Author:     Daniel Lipkin, TU Muenchen

This module provides utilities for improving Isabelle proofs.
*)

signature PROOF_IMPROVE =
sig
  datatype outcome = Rewrite_Succeeded of Proof.state option
              | TimeOut
              | ResourcesOut
              | Unknown
              | None

  val string_of_outcome : outcome -> string
  val proof_improve : Time.time option -> Proof.state ->  outcome
end;

structure Proof_Improve : PROOF_IMPROVE =
struct
  open ProofImproveScorer
  open ProofImproveRewriter
  open ProofImproveVerifier

  datatype outcome = Rewrite_Succeeded of Proof.state option
              | TimeOut
              | ResourcesOut
              | Unknown
              | None

  val default_timeout = seconds 20.0;

  fun string_of_outcome (Rewrite_Succeeded _) = "rewrite_succeeded"
    | string_of_outcome TimeOut = "timeout"
    | string_of_outcome ResourcesOut = "resources_out"
    | string_of_outcome Unknown = "unknown"
    | string_of_outcome None = "none"

  fun proof_improve timeout_opt st =
    let
      val internal_score = score st
      val _ = tracing ("Scorer result: " ^ Int.toString internal_score)
      val rewrite_result = rewrite st
    in
      case (internal_score, rewrite_result) of
        (0, NONE) => None
      | _ =>
        if verify st (the rewrite_result)
        then Rewrite_Succeeded rewrite_result
        else Unknown
    end;
end;