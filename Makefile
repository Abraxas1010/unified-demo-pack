.PHONY: all bootstrap build run-quick run-full test-valuation check diagrams

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
	  (cd lean && env -i PATH="/usr/bin:/bin" LANG=C HOME=/nonexistent .lake/build/bin/unified_demo --quick); \
	else \
	  (cd lean && env -i PATH="/usr/bin:/bin" LANG=C HOME=/nonexistent lake env lean --run HeytingLean/CLI/UnifiedDemo.lean -- --quick); \
	fi

run-full:
	bash scripts/demo_full_all.sh

test-valuation:
	cd lean && lake build --wfail HeytingLean.LoF.CryptoSheaf.Quantum.Entropy.ValuationSizeTests

check:
	bash scripts/guard_no_sorry.sh
	cd lean && lake build --wfail UnifiedPack.ContextualityAC HeytingLean.CLI.UnifiedDemo

diagrams:
	# Generate proof graph UMAP diagrams (requires python packages: umap-learn, numpy, matplotlib, plotly)
	cd lean && ./.lake/build/bin/proof_graph_dump > ../docs/proof_graph.json || (echo "proof_graph_dump not available" && exit 1)
	python3 ../scripts/generate_umap.py --graph ../docs/proof_graph.json --out2d ../docs/umap2d.png --out3d ../docs/umap3d.html
