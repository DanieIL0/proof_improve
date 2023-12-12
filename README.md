# proof_improve
Semi-Automatic Proof Improvement

## Warning
If mirabelle.ML is changed, the other registered Actions that use mirabelle will be noticeably slower.
Logging will also be missing the finalize prefix.

## Setup
1. Place the Proof_Improve directory and its contents in ~~/src/HOL/Tools and add the Proof_Improve.thy file to ~~/src/HOL
2. Place the contents of the Mirabelle directory in ~~/src/HOL/Tools/Mirabelle and update the mirabelle.ML file inside
3. Add proof_improve to ~~/src/HOL/Mirabelle.thy as shown below:

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

4. Add the following function to the signature and structure in ~~/src/Pure/Isar/Proof.ML

```ML
val the_fact_or_facts: state -> thm list

fun the_fact_or_facts state =
  (case get_facts state of
    SOME (facts, proper) => (if proper then () else report_improper state; facts)
  | NONE => []);
```

## Tutorial
```Bash
 isabelle mirabelle -D your_directory -A "proof_improve"
```
 
or optionally when proof_improve should only run on one file:
```Bash
  isabelle mirabelle -D your_directory -T your_file -A "proof_improve"
```