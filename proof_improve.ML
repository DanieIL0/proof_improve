(*  Title:      HOL/Tools/proof_improve.ML
    Author:     Daniel Lipkin, TU Muenchen

This module provides utilities for improving Isabelle proofs.
*)
signature PROOF_IMPROVE =
sig
  datatype outcome = Rewrite_Succeeded of string
              | TimeOut of string
              | ResourcesOut of string
              | Unknown of string
              | None of string
              | ScoreNotLowered of string

  val proof_improve : Proof.state -> string -> outcome
end;

structure Proof_Improve : PROOF_IMPROVE =
struct
  open Proof_Improve_Scorer
  open Proof_Improve_Finder

   datatype outcome = Rewrite_Succeeded of string
              | TimeOut of string
              | ResourcesOut of string
              | Unknown of string
              | None of string
              | ScoreNotLowered of string

fun proof_improve st proof_text =
  let
    val (original_score, original_log) = score (List.length (Proof.the_fact_or_facts st)) proof_text
    val original_score_msg = "Scorer result (original): " ^ Real.toString original_score
    val find_result = find st
    val initial_log = original_log  ^ original_score_msg
  in
    case find_result of
      NONE =>
        let
          val log_msg = initial_log ^ "\nNo potential rewrite found."
        in
          ScoreNotLowered log_msg
        end
    | SOME (found_facts, found_proof_text, log) =>
      let
        val (found_score, found_log) = score found_facts found_proof_text
        val found_score_msg = "Scorer result (found): " ^ Real.toString found_score
        val combined_log = initial_log ^ "\n" ^ log ^ "\n" ^ found_log ^  found_score_msg
      in
        if found_score < original_score
        then
          let
            val outcome_msg = "Outcome: Rewrite_Succeeded\n"
          in
            Rewrite_Succeeded (combined_log ^ "\n" ^ outcome_msg)
          end
        else if found_score >= original_score
        then
          let
            val outcome_msg = "Outcome: ScoreNotLowered\n"
          in
            ScoreNotLowered (combined_log ^ "\n" ^ outcome_msg)
          end
        else
          let
            val outcome_msg = "Outcome: Unknown\n"
          in
            Unknown (combined_log ^ "\n" ^ outcome_msg)
          end
      end
  end;
end