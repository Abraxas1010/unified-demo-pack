import HeytingLean.LoF.CryptoSheaf.Quantum.EmpiricalModel

open HeytingLean.LoF.CryptoSheaf.Quantum

-- Sanity: ensure all six compatibility cases are well-typed and available
#check (triCompatible (ab_in_cover) (bc_in_cover))
#check (triCompatible (ab_in_cover) (ac_in_cover))
#check (triCompatible (bc_in_cover) (ab_in_cover))
#check (triCompatible (bc_in_cover) (ac_in_cover))
#check (triCompatible (ac_in_cover) (ab_in_cover))
#check (triCompatible (ac_in_cover) (bc_in_cover))

