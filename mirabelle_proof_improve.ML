(*  Title:      HOL/Tools/Mirabelle/mirabelle_proof_improve.ML
    Author:     Daniel Lipkin, TU Muenchen

Mirabelle action: "proof_improve".
*)

structure Mirabelle_Proof_Improve: MIRABELLE_ACTION =
struct
  open Proof_Improve
  open Mirabelle

  fun make_action ({timeout, ...} : action_context) =
    let
      val generous_timeout = Time.scale 100.0 timeout

      fun run ({pre, span, ...} : command) =
        case Timeout.apply generous_timeout (proof_improve (SOME timeout)) pre span of
          Rewrite_Succeeded _ => "succeeded"
        | _ => ""
    in
      ("", {run = run, finalize = K ""})
    end

  val () = register_action "proof_improve" make_action
end;