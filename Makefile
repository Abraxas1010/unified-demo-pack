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
	# Try to generate proof graph; if empty, build module graph
	cd lean && ./.lake/build/bin/proof_graph_dump > ../docs/proof_graph.json || true
	python3 scripts/generate_module_graph.py --root lean --out docs/module_graph.json
	# Select a non-empty graph json (prefer proof_graph)
	python3 -c "import json,sys,pathlib; p='docs/proof_graph.json'; print(p if (pathlib.Path(p).exists() and len(json.load(open(p)).get('nodes',[]))>0) else 'docs/module_graph.json')" > docs/_graph.pick
	GRAPH_JSON=$$(cat docs/_graph.pick); \
	python3 scripts/generate_umap.py --graph $$GRAPH_JSON --out2d docs/umap2d.png --out3d-png docs/umap3d.png
