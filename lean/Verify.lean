import MinBox

/-!
Run `lake env lean Verify.lean` after `lake build`.
It prints the statements of the main theorems and the axioms they depend on.
The expected axioms are the three standard ones: `propext`, `Classical.choice`, `Quot.sound`
(no `sorryAx`).
-/

#check @MinBox.three_contacts
#check @MinBox.three_edge_face_contacts
#check @MinBox.exists_minimal_box_with_three_contacts

#print axioms MinBox.three_contacts
#print axioms MinBox.three_edge_face_contacts
#print axioms MinBox.exists_minimal_box_with_three_contacts
