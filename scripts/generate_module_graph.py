#!/usr/bin/env python3
import os, sys, json, argparse

def fs_to_module(root, path):
    """Map a filesystem path to a Lean module name.

    Handles:
      - local sources under `HeytingLean/**` (prefix preserved)
      - local sources under any other top-level (e.g. `UnifiedPack/**`)
      - vendored deps under `.lake/packages/<Pkg>/**` mapped to `<Pkg>/**`
        and also normalizes the common duplication where the next segment
        repeats the package name (e.g. `.../Mathlib/Mathlib/Topology/Basic.lean`).
    """
    if not path.endswith('.lean'):
        return None
    rel = os.path.relpath(path, root)
    parts = rel[:-5].split(os.sep)  # drop .lean
    if not parts:
        return None
    # Direct project modules
    if parts[0] == 'HeytingLean':
        return '.'.join(parts)
    if parts[0] == 'UnifiedPack':
        return '.'.join(parts)
    # Lake vendored packages: .lake/packages/<Pkg>/[<Pkg>]/...
    if len(parts) >= 3 and parts[0] == '.lake' and parts[1] == 'packages':
        pkg = parts[2]
        rest = parts[3:]
        prefix = None
        if rest:
            # Drop duplicated segment if it matches the package name ignoring case
            if rest[0].lower() == pkg.lower():
                prefix = rest[0]  # preserve original casing for module root
                rest = rest[1:]
            else:
                # Some packages place sources under a capitalized module root (e.g., Mathlib)
                prefix = rest[0] if rest[0][:1].isupper() else pkg
        if not rest:
            return None
        return '.'.join(([prefix] if prefix else [pkg]) + rest)
    # Fallback: join as-is (e.g., lakefile)
    return '.'.join(parts)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--root', default='lean')
    ap.add_argument('--out', default='docs/module_graph.json')
    args = ap.parse_args()

    modules = {}
    for dirpath, _, filenames in os.walk(args.root):
        # Skip vendored dependencies - only include project modules
        if '.lake' in dirpath:
            continue
        for fn in filenames:
            if fn.endswith('.lean'):
                full = os.path.join(dirpath, fn)
                mod = fs_to_module(args.root, full)
                if mod:
                    modules[mod]=full

    edges = []
    nodes = []
    for mod, path in modules.items():
        nodes.append({'id': mod, 'name': mod})
        try:
            with open(path,'r') as f:
                for line in f:
                    line=line.strip()
                    if line.startswith('import '):
                        imp = line.split('import',1)[1].strip()
                        # normalize spaces
                        imp = imp.split('--')[0].strip()
                        if not imp:
                            continue
                        # Split on spaces; handle multiple imports per line
                        for maybe in imp.split():
                            t = maybe.strip()
                            # Normalize relative/aliased whitespace
                            if not t:
                                continue
                            if t in modules:
                                edges.append({'source': t, 'target': mod})
        except Exception:
            pass
    graph={'nodes':nodes,'edges':edges}
    os.makedirs(os.path.dirname(args.out), exist_ok=True)
    with open(args.out,'w') as f:
        json.dump(graph,f)
    print(f'wrote {args.out} with {len(nodes)} nodes, {len(edges)} edges')

if __name__=='__main__':
    main()
