#!/usr/bin/env python3
import argparse, json, sys

try:
    import numpy as np
except ImportError:
    print("numpy not installed; install and retry", file=sys.stderr); sys.exit(2)
try:
    import umap
    HAVE_UMAP = True
except ImportError:
    HAVE_UMAP = False
try:
    import matplotlib.pyplot as plt
    HAVE_MPL = True
except ImportError:
    HAVE_MPL = False
try:
    import plotly.express as px
except ImportError:
    px = None

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--graph', required=True, help='JSON with nodes/edges; each node should have a name/id')
    ap.add_argument('--out2d', required=False)
    ap.add_argument('--out3d', required=False, help='write interactive HTML if plotly is available')
    ap.add_argument('--out3d-png', required=False, help='write static 3D PNG (matplotlib fallback)')
    ap.add_argument('--max-edge-lines', type=int, default=15000, help='limit of edges to draw as lines')
    ap.add_argument('--label-top', type=int, default=30, help='number of hub labels to annotate')
    args = ap.parse_args()

    with open(args.graph) as f:
        g = json.load(f)
    # Expecting nodes/edges; build informative, stable features per node
    nodes = g.get('nodes', [])
    edges = g.get('edges', [])
    # degrees
    deg_in, deg_out, deg = {}, {}, {}
    # fast name-index map
    raw_names = [(n.get('name') or n.get('id') or str(i)) for i,n in enumerate(nodes)]
    name_to_idx = {nm:i for i,nm in enumerate(raw_names)}
    for e in edges:
        u = e.get('source') or e.get('u')
        v = e.get('target') or e.get('v')
        if u is None or v is None:
            continue
        deg_out[u] = deg_out.get(u, 0) + 1
        deg_in[v] = deg_in.get(v, 0) + 1
        deg[u] = deg.get(u, 0) + 1
        deg[v] = deg.get(v, 0) + 1
    # groups by top-level namespace
    top = []
    for nm in raw_names:
        seg = nm.split('.')[0]
        top.append(seg)
    # choose top-k groups for one-hot features
    from collections import Counter
    group_counts = Counter(top)
    top_groups = [g for g,_ in group_counts.most_common(16)]
    group_index = {g:i for i,g in enumerate(top_groups)}
    # assemble features
    X = []
    labels = []
    for i,nm in enumerate(raw_names):
        di = deg_in.get(nm, 0)
        do = deg_out.get(nm, 0)
        d = di + do
        depth = nm.count('.') + 1
        name_len = len(nm)
        gfeat = [0.0]*len(top_groups)
        gi = group_index.get(nm.split('.')[0])
        if gi is not None:
            gfeat[gi] = 1.0
        # feature vector: [deg_in, deg_out, deg_total, depth, name_len, one-hot(groups...)]
        X.append([di, do, d, depth, name_len] + gfeat)
        labels.append(nm)
    X = np.asarray(X, dtype=float)
    if len(X) == 0:
        if args.out2d and plt is not None:
            plt.figure(figsize=(6,6))
            plt.text(0.5, 0.5, 'No nodes', ha='center', va='center')
            plt.axis('off')
            plt.tight_layout(); plt.savefig(args.out2d, dpi=200)
            print(f"wrote {args.out2d} (empty)")
        if args.out3d and px is not None:
            import plotly.graph_objs as go
            fig = go.Figure()
            fig.add_annotation(text='No nodes', x=0.5, y=0.5, showarrow=False)
            fig.write_html(args.out3d)
            print(f"wrote {args.out3d} (empty)")
        sys.exit(0)

    if HAVE_UMAP:
        reducer2 = umap.UMAP(n_components=2, random_state=42, n_neighbors=15, min_dist=0.15)
        Y2 = reducer2.fit_transform(X)
    else:
        # PCA fallback using SVD
        Xc = X - X.mean(axis=0)
        U,S,Vt = np.linalg.svd(Xc, full_matrices=False)
        Y2 = Xc @ Vt.T[:, :2]
    if args.out2d and HAVE_MPL:
        # Group-aware coloring by top-level namespace; add edges and labels
        groups = top
        import random
        random.seed(42)
        # deterministic color per group
        cmap = {}
        def color_for(gname):
            if gname not in cmap:
                random.seed(hash(gname) & 0xFFFFFFFF)
                cmap[gname] = (random.random()*0.8, random.random()*0.8, random.random()*0.8, 0.8)
            return cmap[gname]
        import matplotlib.pyplot as plt
        import numpy as _np
        fig, ax = plt.subplots(figsize=(8,8))
        Y2 = _np.asarray(Y2)
        # jitter to avoid total overlap of identical features
        if Y2.size > 0:
            scale = (Y2.std(axis=0)+1e-6) * 0.01
            Y2 = Y2 + _np.random.default_rng(42).normal(0, scale, Y2.shape)
        # draw sampled edges
        if edges:
            import random as _r
            _r.seed(42)
            m = min(len(edges), max(0, int(args.max_edge_lines)))
            sample = edges if len(edges) <= m else _r.sample(edges, m)
            for e in sample:
                u = e.get('source') or e.get('u')
                v = e.get('target') or e.get('v')
                iu = name_to_idx.get(u); iv = name_to_idx.get(v)
                if iu is None or iv is None:
                    continue
                x1,y1 = Y2[iu,0], Y2[iu,1]
                x2,y2 = Y2[iv,0], Y2[iv,1]
                ax.plot([x1,x2],[y1,y2], color=(0,0,0,0.06), linewidth=0.3)
        # plot points by group
        from collections import defaultdict
        bucket = defaultdict(list)
        for i,gname in enumerate(groups):
            bucket[gname].append(i)
        # Show legend only for top 12 groups by size
        gc_sorted = sorted(bucket.items(), key=lambda kv: -len(kv[1]))
        show_legend_groups = set([g for g,_ in gc_sorted[:12]])
        for gname, idxs in gc_sorted:
            arrx = [Y2[j,0] for j in idxs]
            arry = [Y2[j,1] for j in idxs]
            ax.scatter(arrx, arry, s=4, label=gname if gname in show_legend_groups else None,
                       c=[color_for(gname)], edgecolors='none')
        # annotate hubs
        if args.label_top > 0:
            # pick top hubs by total degree
            d_scores = [(deg.get(nm,0), i, nm) for nm,i in name_to_idx.items()]
            d_scores.sort(reverse=True)
            for _, i, nm in d_scores[:args.label_top]:
                ax.text(Y2[i,0], Y2[i,1], nm.split('.')[-1], fontsize=6, color=(0,0,0,0.6),
                        clip_on=True)
        if len(show_legend_groups) > 0:
            ax.legend(fontsize=7, markerscale=3, loc='best', frameon=False)
        ax.set_xticks([]); ax.set_yticks([])
        ax.set_xlabel(''); ax.set_ylabel('')
        fig.tight_layout(); fig.savefig(args.out2d, dpi=250)
        print(f"wrote {args.out2d}")
    if args.out3d and px is not None:
        if HAVE_UMAP:
            reducer3 = umap.UMAP(n_components=3, random_state=42, n_neighbors=15, min_dist=0.15)
            Y3 = reducer3.fit_transform(X)
        else:
            # PCA fallback to min(3, rank)
            Xc = X - X.mean(axis=0)
            U,S,Vt = np.linalg.svd(Xc, full_matrices=False)
            k = 3 if Vt.shape[0] >= 3 else Vt.shape[0]
            Y3 = Xc @ Vt.T[:, :k]
            import numpy as _np
            if k < 3:
                pad = _np.zeros((Y3.shape[0], 3 - k))
                Y3 = _np.hstack([Y3, pad])
        fig = px.scatter_3d(x=Y3[:,0], y=Y3[:,1], z=Y3[:,2], width=900, height=700)
        fig.write_html(args.out3d)
        print(f"wrote {args.out3d}")
    elif args.out3d_png and HAVE_MPL:
        # Static 3D using matplotlib
        from mpl_toolkits.mplot3d import Axes3D  # noqa: F401
        if HAVE_UMAP:
            reducer3 = umap.UMAP(n_components=3, random_state=42, n_neighbors=15, min_dist=0.15)
            Y3 = reducer3.fit_transform(X)
        else:
            Xc = X - X.mean(axis=0)
            U,S,Vt = np.linalg.svd(Xc, full_matrices=False)
            Y3 = Xc @ Vt.T[:, :3]
        fig = plt.figure(figsize=(8,8))
        ax = fig.add_subplot(111, projection='3d')
        # Ensure Y3 has 3 columns
        import numpy as _np
        if Y3.shape[1] < 3:
            pad = _np.zeros((Y3.shape[0], 3 - Y3.shape[1]))
            Y3 = _np.hstack([Y3, pad])
        # edges (sampled)
        if edges:
            import random as _r
            _r.seed(42)
            m = min(len(edges), max(0, int(args.max_edge_lines//3)))
            sample = edges if len(edges) <= m else _r.sample(edges, m)
            for e in sample:
                u = e.get('source') or e.get('u')
                v = e.get('target') or e.get('v')
                iu = name_to_idx.get(u); iv = name_to_idx.get(v)
                if iu is None or iv is None:
                    continue
                x1,y1,z1 = Y3[iu,0], Y3[iu,1], Y3[iu,2]
                x2,y2,z2 = Y3[iv,0], Y3[iv,1], Y3[iv,2]
                ax.plot([x1,x2],[y1,y2],[z1,z2], color=(0,0,0,0.05), linewidth=0.3)
        ax.scatter(Y3[:,0], Y3[:,1], Y3[:,2], s=4, c=(0.2,0.4,0.8,0.8))
        ax.set_xticks([]); ax.set_yticks([]); ax.set_zticks([])
        plt.tight_layout(); plt.savefig(args.out3d_png, dpi=250)
        print(f"wrote {args.out3d_png}")

if __name__ == '__main__':
    main()
