(*  Title:      HOL/Tools/proof_improve.ML
    Author:     Daniel Lipkin, TU Muenchen

This module provides utilities for improving Isabelle proofs.
*)
signature PROOF_IMPROVE =
sig
  datatype outcome = Rewrite_Succeeded of string * Proof.state option
              | TimeOut of string
              | ResourcesOut of string
              | Unknown of string
              | None of string
              | ScoreNotLowered of string

  val proof_improve : Proof.state -> Command_Span.span list -> outcome
end;

structure Proof_Improve : PROOF_IMPROVE =
struct
  open Proof_Improve_Scorer
  open Proof_Improve_Finder

   datatype outcome = Rewrite_Succeeded of string * Proof.state option
              | TimeOut of string
              | ResourcesOut of string
              | Unknown of string
              | None of string
              | ScoreNotLowered of string


fun proof_improve  st sp =
  let
    val (original_score, original_log) = score st sp
    val original_score_msg = "Scorer result (original): " ^ Real.toString original_score
    val potential_rewrite = find st
    val initial_log = original_log ^ "\n" ^ original_score_msg
  in
    case potential_rewrite of
      NONE =>
        let
          val log_msg = initial_log ^ "\nNo potential rewrite found."
        in
          None log_msg
        end
    | SOME potential_rewrite_st =>
      let
        val (rewritten_score, rewritten_log) = score potential_rewrite_st sp
        val rewritten_score_msg = "Scorer result (rewritten): " ^ Real.toString rewritten_score
        val combined_log = initial_log ^ "\n" ^ rewritten_log ^ "\n" ^ rewritten_score_msg
      in
        if rewritten_score < original_score
        then
          let
            val outcome_msg = "Outcome: Rewrite_Succeeded"
          in
            Rewrite_Succeeded (combined_log ^ "\n" ^ outcome_msg, SOME potential_rewrite_st)
          end
        else if rewritten_score >= original_score
        then
          let
            val outcome_msg = "Outcome: ScoreNotLowered"
          in
            ScoreNotLowered (combined_log ^ "\n" ^ outcome_msg)
          end
        else
          let
            val outcome_msg = "Outcome: Unknown"
          in
            Unknown (combined_log ^ "\n" ^ outcome_msg)
          end
      end
  end;
end