signature PROOF_IMPROVE_FINDER =
sig
  val find: Proof.state -> Proof.state option
end;

structure Proof_Improve_Finder: PROOF_IMPROVE_FINDER =
struct
  open Sledgehammer
  open Sledgehammer_Prover
  open Sledgehammer_Proof_Methods

fun apply_prover_result (res : prover_result) (st : Proof.state) : Proof.state option =
  case #outcome res of
    NONE =>
      let
        val facts = #used_facts res
        val (preferred_method, _) = #preferred_methss res

       fun apply_fact_to_state (fact: string * stature) (preferred_method: proof_method) (current_state: Proof.state) : Proof.state =
          let
          val _ = case preferred_method of
          Metis_Method (opt1, opt2) => ()
          | Meson_Method => ()
          | SMT_Method backend => ()
          | SATx_Method => ()
          | Blast_Method => ()
          | Simp_Method => ()
          | Auto_Method => ()
          | Fastforce_Method => ()
          | Force_Method => ()
          | Moura_Method => ()
          | Linarith_Method => ()
          | Presburger_Method => ()
          | Algebra_Method => ()
  in
    current_state
    end

      val modified_st = fold (fn fact => apply_fact_to_state fact preferred_method) facts st
      in
        SOME modified_st
      end
  | SOME _ => NONE


fun apply_sh_outcome (sh : sledgehammer_outcome) (st: Proof.state) : Proof.state option =
  case sh of
    SH_Some (prover_result, _) =>
      apply_prover_result prover_result st
  | _ => NONE


  fun find (st: Proof.state) =
    let
      val params = Sledgehammer_Commands.default_params \<^theory> []
      val fact_override = {add = [], del = [], only = false}
      val (_, (outcome, _)) = run_sledgehammer params Normal NONE 30 fact_override st
    in
      apply_sh_outcome outcome st
end

end