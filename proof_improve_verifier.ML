signature PROOF_IMPROVE_VERIFIER =
sig
  val verify : Proof.state -> Proof.state -> bool
end;

structure ProofImproveVerifier : PROOF_IMPROVE_VERIFIER =
struct
  fun verify (original_st: Proof.state) (rewritten_st: Proof.state) : bool =
    let
      val {goal = original_goal, ...} = Proof.simple_goal original_st
      val {goal = rewritten_goal, ...} = Proof.simple_goal rewritten_st
    in
      Term.could_unify (Thm.prop_of original_goal, Thm.prop_of rewritten_goal)
    end
end;
