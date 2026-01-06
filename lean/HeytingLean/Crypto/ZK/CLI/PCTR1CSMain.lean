import HeytingLean.Crypto.ZK.CLI.PCTR1CS

-- Thin executable wrapper: provide a top-level main for the pct_r1cs target
open HeytingLean.Crypto.ZK.CLI.PCTR1CS in
def main (args : List String) : IO UInt32 :=
  HeytingLean.Crypto.ZK.CLI.PCTR1CS.main args

