(*  Title:      HOL/Proof_Improve.thy
    Author:     Daniel Lipkin, TU Muenchen
*)

section ‹Proof Improve: Semi-Automatic Proof Improvement›

theory Proof_Improve
  imports Sledgehammer
begin


ML_file ‹Tools/Proof_Improve/proof_improve_changes.ML›
ML_file ‹Tools/Proof_Improve/proof_improve_config_manager.ML›
ML_file ‹Tools/Proof_Improve/proof_improve_finder.ML›
ML_file ‹Tools/Proof_Improve/proof_improve_scorer.ML›
ML_file ‹Tools/Proof_Improve/proof_improve.ML›

end