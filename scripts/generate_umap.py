#!/usr/bin/env python3
import argparse, json, sys

try:
    import numpy as np
except ImportError:
    print("numpy not installed; install and retry", file=sys.stderr); sys.exit(2)
try:
    import umap
except ImportError:
    print("umap-learn not installed; pip install umap-learn", file=sys.stderr); sys.exit(2)
try:
    import matplotlib.pyplot as plt
except ImportError:
    plt = None
try:
    import plotly.express as px
except ImportError:
    px = None

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--graph', required=True)
    ap.add_argument('--out2d', required=False)
    ap.add_argument('--out3d', required=False)
    args = ap.parse_args()

    with open(args.graph) as f:
        g = json.load(f)
    # Expecting nodes as a list; build a trivial feature vector per node (degree, label length)
    nodes = g.get('nodes', [])
    edges = g.get('edges', [])
    deg = {}
    for e in edges:
        u = e.get('source') or e.get('u'); v = e.get('target') or e.get('v')
        if u is not None: deg[u]=deg.get(u,0)+1
        if v is not None: deg[v]=deg.get(v,0)+1
    X = []
    labels = []
    for i,n in enumerate(nodes):
        name = n.get('name') or n.get('id') or str(i)
        d = deg.get(name, 0)
        labels.append(name)
        X.append([d, len(name)])
    X = np.asarray(X, dtype=float)
    if len(X) == 0:
        print("graph has no nodes", file=sys.stderr); sys.exit(1)

    reducer2 = umap.UMAP(n_components=2, random_state=42)
    Y2 = reducer2.fit_transform(X)
    if args.out2d and plt is not None:
        plt.figure(figsize=(6,6))
        plt.scatter(Y2[:,0], Y2[:,1], s=6)
        plt.tight_layout(); plt.savefig(args.out2d, dpi=200)
        print(f"wrote {args.out2d}")
    if args.out3d and px is not None:
        reducer3 = umap.UMAP(n_components=3, random_state=42)
        Y3 = reducer3.fit_transform(X)
        fig = px.scatter_3d(x=Y3[:,0], y=Y3[:,1], z=Y3[:,2], width=700, height=600)
        fig.write_html(args.out3d)
        print(f"wrote {args.out3d}")

if __name__ == '__main__':
    main()
