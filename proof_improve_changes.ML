(*  Title:      HOL/Tools/Proof_Improve/proof_improve_changes.ML
    Author:     Daniel Lipkin, TU Muenchen

Datatype to track changes by proof_improve
*)

signature PROOF_IMPROVE_CHANGES =
sig
  type proof_changes
  val create : unit -> proof_changes
  val add_change : string * string * Position.T -> proof_changes -> proof_changes
  val add_unsuccessful_call : proof_changes -> proof_changes
  val tostring : proof_changes -> string
end;

structure Proof_Improve_Changes : PROOF_IMPROVE_CHANGES =
struct
  datatype proof_change = ProofChange of { prev_proof: string, changed_proof: string, position: Position.T }
  datatype proof_changes = ProofChanges of { changes: proof_change list, total_proofs: int, successful_changes: int }

  fun create () = ProofChanges { changes = [], total_proofs = 0, successful_changes = 0 }

  fun add_change (prev_proof, changed_proof, position) (ProofChanges {changes, total_proofs, successful_changes}) =
    let
      val new_change = ProofChange {prev_proof = prev_proof, changed_proof = changed_proof, position = position}
    in
      ProofChanges { changes = new_change :: changes, total_proofs = total_proofs + 1, successful_changes = successful_changes + 1}
    end;

  fun add_unsuccessful_call (ProofChanges {changes, total_proofs, successful_changes}) =
      ProofChanges { changes = changes, total_proofs = total_proofs + 1, successful_changes = successful_changes }

  fun proof_change_compare (ProofChange {position = pos1, ...}) (ProofChange {position = pos2, ...}) =
    case (Position.line_of pos1, Position.line_of pos2) of
      (SOME l1, SOME l2) => Int.compare (l1, l2)
    | (SOME _, NONE) => GREATER
    | (NONE, SOME _) => LESS
    | (NONE, NONE) => EQUAL

  fun insert_sorted (x, []) = [x]
    | insert_sorted (x, y::ys) =
        if proof_change_compare x y = LESS then
          x :: y :: ys
        else
          y :: insert_sorted (x, ys)

  fun sort_proof_changes changes = List.foldl (fn (x, acc) => insert_sorted (x, acc)) [] changes

  fun proof_change_tostring (ProofChange {prev_proof, changed_proof, position}) =
    let
      val line_str = case Position.line_of position of
                       NONE => "Unknown Line"
                     | SOME line => "Line " ^ Int.toString line
    in
      "(Prev: " ^ prev_proof ^ "\nChanged: " ^ changed_proof ^ "\n " ^ line_str ^ ")\n"
    end;

  fun tostring (ProofChanges {changes, total_proofs, successful_changes}) =
    let
      val sorted_changes = sort_proof_changes changes
      val changes_str = map proof_change_tostring sorted_changes
      val stats = "Total Proofs: " ^ Int.toString total_proofs ^ ", Successful Changes: " ^ Int.toString successful_changes
    in
      String.concatWith "\n" changes_str ^ "\n" ^ stats
    end;

end;