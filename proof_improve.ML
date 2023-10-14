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
              | ScoreNotLowered

  val string_of_outcome : outcome -> string
  val proof_improve : Time.time option -> Proof.state -> outcome
end;

structure Proof_Improve : PROOF_IMPROVE =
struct
  open Proof_Improve_Scorer
  open Proof_Improve_Finder

  datatype outcome = Rewrite_Succeeded of Proof.state option
              | TimeOut
              | ResourcesOut
              | Unknown
              | None
              | ScoreNotLowered

  val default_timeout = seconds 20.0;

  fun string_of_outcome (Rewrite_Succeeded _) = "rewrite_succeeded"
    | string_of_outcome TimeOut = "timeout"
    | string_of_outcome ResourcesOut = "resources_out"
    | string_of_outcome Unknown = "unknown"
    | string_of_outcome None = "none"
    | string_of_outcome ScoreNotLowered = "score_not_lowered"

  fun proof_improve timeout_opt st =
    let
      val original_score = score st
      val _ = tracing ("Scorer result (original): " ^ Real.toString original_score)
      val potential_rewrite = find st
    in
      case potential_rewrite of
        NONE =>
          (tracing "No potential rewrite found"; None)
      | SOME potential_rewrite_st =>
        let
          val rewritten_score = score potential_rewrite_st
          val _ = tracing ("Scorer result (rewritten): " ^ Real.toString rewritten_score)
        in
          if rewritten_score < original_score
          then (tracing "Outcome: Rewrite_Succeeded"; Rewrite_Succeeded (SOME potential_rewrite_st))
          else if rewritten_score >= original_score
          then (tracing "Outcome: ScoreNotLowered"; ScoreNotLowered)
          else (tracing "Outcome: Unknown"; Unknown)
        end
    end;
end;