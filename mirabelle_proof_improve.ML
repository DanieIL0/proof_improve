(*  Title:      HOL/Tools/Mirabelle/mirabelle_proof_improve.ML
    Author:     Daniel Lipkin, TU Muenchen

Mirabelle action: "proof_improve".
*)

structure Mirabelle_Proof_Improve: MIRABELLE_ACTION =
struct
  open Proof_Improve

fun get_content spans : string =
  let
    val tokens = List.concat (List.map Command_Span.content spans)
    val non_comment_tokens = List.filter (fn tok => not (Token.is_comment tok)) tokens
        fun concat_tokens (toks, acc) =
      case toks of
          [] => acc
        | tok::rest =>
            let
              val token_str = Token.content_of tok
              val updated_acc =
                if acc = "" orelse String.isSuffix " " acc orelse String.isPrefix " " token_str then
                  acc ^ token_str
                else
                  acc ^ " " ^ token_str
            in
              concat_tokens (rest, updated_acc)
            end

  in
     concat_tokens (non_comment_tokens, "")
  end;

  fun make_action ({timeout, ...} : Mirabelle.action_context) =
    let
      val generous_timeout = Time.scale 200.0 timeout

      fun run ({pre, spans, ...} : Mirabelle.command) : string =
        let
          val outcome = Timeout.apply generous_timeout (proof_improve) pre (get_content spans)
        in
          string_of_outcome outcome ^ "\n"
        end

      fun finalize () : string = "End of Proof Improve Call"
    in

      ("", {run = run, finalize = finalize})
    end

  val () = Mirabelle.register_action "proof_improve" make_action
end;