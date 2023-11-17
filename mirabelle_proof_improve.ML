(*  Title:      HOL/Tools/Mirabelle/mirabelle_proof_improve.ML
    Author:     Daniel Lipkin, TU Muenchen

    Mirabelle action: "proof_improve".
*)

structure Mirabelle_Proof_Improve: MIRABELLE_ACTION =
struct
  open Proof_Improve
  open Mirabelle


  val data = Synchronized.var "Mirabelle_Proof_Improve_data" ""

  fun make_action ({timeout, ...} : action_context) =
    let
      val generous_timeout = Time.scale 100.0 timeout

      fun run ({pre, spans, ...} : command) : string =
        let
          val outcome = Timeout.apply generous_timeout (proof_improve (SOME timeout)) pre spans
          val outcome_message = case outcome of
              Rewrite_Succeeded (log, _) => "Rewrite Succeeded: " ^ log
            | TimeOut log => "TimeOut: " ^ log
            | ResourcesOut log => "ResourcesOut: " ^ log
            | Unknown log => "Unknown: " ^ log
            | None log => "None: " ^ log
            | ScoreNotLowered log => "ScoreNotLowered: " ^ log
          val () = Synchronized.change data (fn old_str => old_str ^ outcome_message ^ "\n")
        in
          outcome_message
        end

      fun finalize () : string = ""
    in

      ("", {run = run, finalize = finalize})
    end

  val () = register_action "proof_improve" make_action
end;