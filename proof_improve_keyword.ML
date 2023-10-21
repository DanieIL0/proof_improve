signature PROOF_IMPROVE_COMMANDS =
sig
  val proof_improve_cmd: Toplevel.state -> unit
end;

structure Proof_Improve_Commands : PROOF_IMPROVE_COMMANDS =
struct

open Proof_Improve

fun proof_improve_cmd state =
  let
    val proof_state = Toplevel.proof_of state
    val outcome = Proof_Improve.proof_improve NONE proof_state
    val _ = case outcome of
              Proof_Improve.Rewrite_Succeeded _ => writeln "Proof improvement succeeded."
            | _ => writeln ("Proof improvement failed: " ^ Proof_Improve.string_of_outcome outcome)
  in
    ()
  end

val _ =
  Outer_Syntax.command \<^command_keyword>‹proof_improve› "Improve the current proof"
    (Scan.succeed (Toplevel.keep_proof proof_improve_cmd))

end;