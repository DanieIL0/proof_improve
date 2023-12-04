# proof_improve

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
ML_file ‹Tools/Mirabelle/mirabelle_proof_improve.ML›
ML_file ‹Tools/Mirabelle/mirabelle_quickcheck.ML›
ML_file ‹Tools/Mirabelle/mirabelle_sledgehammer_filter.ML›
ML_file ‹Tools/Mirabelle/mirabelle_sledgehammer.ML›
ML_file ‹Tools/Mirabelle/mirabelle_try0.ML›

end
```

Proof.ML

```ML
val the_fact_or_facts: state -> thm list

fun the_fact_or_facts state =
  (case get_facts state of
    SOME (facts, proper) => (if proper then () else report_improper state; facts)
  | NONE => []);
```
