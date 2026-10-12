import Howroyd.Main

/-!
This module prints the semantic target and all critical transitive axiom lists.
Run with `lake env lean -j 2 -s 131072 Howroyd/Audit.lean`.
No declaration below is an assumption used by the main proof.
-/

#print Howroyd.Vec
#print Howroyd.Vec.degree
#print Howroyd.vertices
#print Howroyd.l1Distance
#print Howroyd.Independent
#print Howroyd.MaximumIndependent
#print Howroyd.maximumIndependentSets
#print Howroyd.Howroyd27

#check Howroyd.maximum_independent_sets_card
#print Howroyd.howroyd_27

#print axioms Howroyd.mem_vertices
#print axioms Howroyd.triVertices_clique
#print axioms Howroyd.triVertices_injective_of_valid
#print axioms Howroyd.triangles_filter_eq_incident
#print axioms Howroyd.sum_incidentTriangles
#print axioms Howroyd.cover_base
#print axioms Howroyd.covered_all
#print axioms Howroyd.legal_key_defined
#print axioms Howroyd.exact_cover_of_not_dvd
#print axioms Howroyd.maximum_saturates
#print axioms Howroyd.weight_zero_iff
#print axioms Howroyd.maximum_body_color_constancy
#print axioms Howroyd.maximum_one_color_on_body
#print axioms Howroyd.Corner.isMaximum_iff_table
#print axioms Howroyd.independent_of_localCompatible
#print axioms Howroyd.maximum_eq_assembly
#print axioms Howroyd.assembled_maximum
#print axioms Howroyd.assembleChoice_injective
#print axioms Howroyd.maximumIndependentSets_eq_candidates
#print axioms Howroyd.maximum_independent_sets_card
#print axioms Howroyd.howroyd_27
