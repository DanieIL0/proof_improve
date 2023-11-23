(*  Title:      HOL/Tools/Proof_Improve/proof_improve_finder.ML
    Author:     Daniel Lipkin, TU Muenchen

Finding proof alternatives using sledgehammer.
*)

signature PROOF_IMPROVE_FINDER =
sig
  val find: Proof.state -> (int * string * string) option
end;

structure Proof_Improve_Finder: PROOF_IMPROVE_FINDER =
struct

fun parse_sledgehammer_result (result: string) : string =
  let
    val prefix = "Try this: "
    val prefix_len = size prefix

    val result_without_prefix =
      if String.isPrefix prefix result then
        String.extract (result, prefix_len, NONE)
      else
        result

    fun rindex_from (s, c, i) =
      if i < 0 then NONE
      else if String.sub (s, i) = c then SOME i
      else rindex_from (s, c, i - 1)

    val result_without_timing =
      case rindex_from (result_without_prefix, #"(", size result_without_prefix - 1) of
        NONE => result_without_prefix
      | SOME i => String.extract (result_without_prefix, 0, SOME i)

    val result_trimmed =
      if size result_without_timing > 0 andalso String.sub (result_without_timing, size result_without_timing - 1) = #" " then
        String.extract (result_without_timing, 0, SOME (size result_without_timing - 1))
      else
        result_without_timing
  in
    result_trimmed
  end;


fun find (st: Proof.state) =
  let
    val params = Sledgehammer_Commands.default_params \<^theory> []
    val fact_override = {add = [], del = [], only = false}
    val (_, (outcome, try_this)) = Sledgehammer.run_sledgehammer params Sledgehammer_Prover.Normal NONE 1 fact_override st
  in
    case outcome of
      Sledgehammer.SH_Some (prover_result, _) =>
        (case #outcome prover_result of
           NONE =>
           let
             val facts = #used_facts prover_result
             val result = parse_sledgehammer_result try_this
           in
             if String.isSubstring "failed" result then
               NONE
             else
               SOME (List.length facts, parse_sledgehammer_result try_this, "Found Proof:")
           end
         | SOME _ => NONE)
    | _ => NONE
  end

end