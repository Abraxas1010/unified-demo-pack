.PHONY: all bootstrap build run-quick run-full test-valuation check

all: run-quick

bootstrap:
	bash scripts/bootstrap.sh

build:
	cd lean && lake build --wfail

run-quick:
	bash scripts/demo_quick_all.sh

run-quick-robust:
	# run with a minimal environment to catch accidental env dependencies
	if [ -x lean/.lake/build/bin/unified_demo ]; then \
	  (cd lean && env -i PATH="/usr/bin:/bin" .lake/build/bin/unified_demo --quick); \
	else \
	  (cd lean && env -i PATH="/usr/bin:/bin" lake env lean --run HeytingLean/CLI/UnifiedDemo.lean -- --quick); \
	fi

run-full:
	bash scripts/demo_full_all.sh

test-valuation:
	cd lean && lake build --wfail HeytingLean.LoF.CryptoSheaf.Quantum.Entropy.ValuationSizeTests

check:
	bash scripts/guard_no_sorry.sh
	cd lean && lake build --wfail UnifiedPack.ContextualityAC HeytingLean.CLI.UnifiedDemo
