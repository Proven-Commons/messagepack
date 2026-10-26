/-
  Axiom check for the claims this package makes. Run with:

    lake env lean MessagePack/Verify.lean

  Every claim should list only the standard axioms (propext,
  Classical.choice, Quot.sound). A line naming sorryAx would mean
  a proof rests on an admitted gap, and the claim is not proved.
-/

import Proofs
import Proofs.Examples

open MessagePack.Proofs MessagePack.Examples

#print axioms parse_print
#print axioms parseGo_print
#print axioms parse_nil
#print axioms parse_never_used
#print axioms parse_uint64_of_one
#print axioms parse_int64_min
#print axioms parse_nested
