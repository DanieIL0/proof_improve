# proof_improve

HOL/Tools/Mirabelle/mirabelle_proof_improve.ML
```ML
(*  Title:      HOL/Tools/Mirabelle/mirabelle_proof_improve.ML
    Author:     Daniel Lipkin, TU Muenchen

Mirabelle action: "proof_improve".
*)

structure Mirabelle_Proof_Improve: MIRABELLE_ACTION =
struct
  open Proof_Improve
  fun make_action ({timeout, ...} : Mirabelle.action_context) =
    let
      val generous_timeout = Time.scale 20.0 timeout

      fun run ({pre, ...} : Mirabelle.command) =
        case Timeout.apply generous_timeout (proof_improve (SOME timeout)) pre of
          Rewrite_Succeeded _ => "succeeded"
        | _ => ""
    in
      ("", {run = run, finalize = K ""})
    end

  val () = Mirabelle.register_action "proof_improve" make_action
end;
```
HOL/Mirabelle.thy **(HAS TO BE READONLY) - ELSE HOL WILL NOT BUILD**

```isabelle
(*  Title:      HOL/Mirabelle.thy
    Author:     Jasmin Blanchette, TU Munich
    Author:     Sascha Boehme, TU Munich
    Author:     Makarius
    Author:     Martin Desharnais, UniBw Munich, MPI-INF Saarbrücken
*)

theory Mirabelle
  imports Sledgehammer Predicate_Compile Presburger Proof_Improve
begin

ML_file ‹Tools/Mirabelle/mirabelle_util.ML›
ML_file ‹Tools/Mirabelle/mirabelle.ML›

ML ‹
signature MIRABELLE_ACTION = sig
  val make_action : Mirabelle.action_context -> string * Mirabelle.action
end
›

ML_file ‹Tools/Mirabelle/mirabelle_arith.ML›
ML_file ‹Tools/Mirabelle/mirabelle_metis.ML›
ML_file ‹Tools/Mirabelle/mirabelle_presburger.ML›
ML_file ‹Tools/Mirabelle/mirabelle_quickcheck.ML›
ML_file ‹Tools/Mirabelle/mirabelle_sledgehammer_filter.ML›
ML_file ‹Tools/Mirabelle/mirabelle_sledgehammer.ML›
ML_file ‹Tools/Mirabelle/mirabelle_try0.ML›
ML_file ‹Tools/Mirabelle/mirabelle_proof_improve.ML›
end
```

HOL/Proof_Improve.thy
```isabelle
(*  Title:      HOL/Proof_Improve.thy
    Author:     Daniel Lipkin, TU Muenchen
*)

section ‹Proof Improve: Automatic Proof Improvement›

theory Proof_Improve
  imports Sledgehammer
begin

ML_file ‹Tools/Proof_Improve/proof_improve_config_manager.ML›
ML_file ‹Tools/Proof_Improve/proof_improve_scorer.ML›
ML_file ‹Tools/Proof_Improve/proof_improve_finder.ML›
ML_file ‹Tools/Proof_Improve/proof_improve.ML›

end
```
