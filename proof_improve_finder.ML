signature PROOF_IMPROVE_FINDER =
sig
  val find: Proof.state -> (int * string * string) option
end;

structure Proof_Improve_Finder: PROOF_IMPROVE_FINDER =
struct
  open Sledgehammer
  open Sledgehammer_Prover
  open Sledgehammer_Proof_Methods
  open Sledgehammer_Isar_Proof
  open Sledgehammer_Util

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
  in
    result_without_timing
  end;

fun prove ctxt goal meth facts chained subproofs =
let
      val assmsp =
      Sledgehammer_Isar_Preplay.resolve_fact_names ctxt facts
      |>> append (map (Sledgehammer_Isar_Preplay.thm_of_proof ctxt) subproofs)
      |>> append chained
in

      Goal.prove_common ctxt NONE [] [] [goal] (fn {context = ctxt, ...} =>
        HEADGOAL (tac_of_proof_method ctxt assmsp meth))
      handle ERROR msg => error ("Preplay error: " ^ msg)

end



fun find (st: Proof.state) =
  let
    val params = Sledgehammer_Commands.default_params \<^theory> []
    val fact_override = {add = [], del = [], only = false}
    val (_, (outcome, try_this)) = run_sledgehammer params Normal NONE 1 fact_override st
  in
    case outcome of
      SH_Some (prover_result, _) =>
        (case #outcome prover_result of
           NONE =>

           let
        val facts = #used_facts prover_result

        in
            SOME (List.length facts, parse_sledgehammer_result try_this, "sledgehammer result: " ^ try_this)
            end

         | SOME _ => NONE)
    | _ => NONE
  end

end