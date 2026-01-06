#!/usr/bin/env python3
"""
UMAP Visualization Generator for Lean Module Graphs

Generates 2D and 3D UMAP embeddings with:
- Namespace-based color coding
- kNN-style edge rendering
- Hub labeling for high-degree nodes
- Interactive Plotly 3D with hover details

Designed to match the causal-confluence-wolfram-lean visualization standard.
"""
import argparse, json, sys
from collections import Counter, defaultdict

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
    from matplotlib.colors import to_hex
    HAVE_MPL = True
except ImportError:
    HAVE_MPL = False
try:
    import plotly.graph_objects as go
    import plotly.express as px
    HAVE_PLOTLY = True
except ImportError:
    HAVE_PLOTLY = False
    px = None
    go = None


# Family-specific color palette (consistent across all visualizations)
FAMILY_COLORS = {
    'CLI': (0.263, 0.627, 0.278),       # #43a047 green
    'Crypto': (0.118, 0.533, 0.898),    # #1e88e5 blue
    'FHE': (0.557, 0.141, 0.667),       # #8e24aa purple
    'ZK': (0.612, 0.153, 0.690),        # #9c27b0 violet
    'Lattice': (0.984, 0.549, 0.000),   # #fb8c00 orange
    'LoF': (0.898, 0.224, 0.208),       # #e53935 red
    'CryptoSheaf': (0.000, 0.675, 0.757),  # #00acc1 cyan
    'Quantum': (0.000, 0.537, 0.482),   # #00897b teal
    'UnifiedPack': (0.486, 0.702, 0.259),  # #7cb342 light green
    'Contextuality': (0.847, 0.106, 0.376),  # #d81b60 pink
    'HeytingLean': (0.098, 0.463, 0.824),  # #1976d2 darker blue
    'Other': (0.376, 0.490, 0.545)      # #607d8b gray
}


def get_family(name: str) -> str:
    """Determine module family from namespace for consistent coloring."""
    if 'CLI' in name:
        return 'CLI'
    if 'UnifiedPack' in name:
        return 'UnifiedPack'
    if 'CryptoSheaf' in name or 'Contextuality' in name:
        return 'CryptoSheaf'
    if 'Quantum' in name or 'Entropy' in name:
        return 'Quantum'
    if 'FHE' in name:
        return 'FHE'
    if 'ZK' in name:
        return 'ZK'
    if 'Lattice' in name:
        return 'Lattice'
    if 'LoF' in name:
        return 'LoF'
    if 'Crypto' in name:
        return 'Crypto'
    if 'HeytingLean' in name:
        return 'HeytingLean'
    return 'Other'


def deterministic_color(name: str, saturation: float = 0.7, value: float = 0.85):
    """Get color for a namespace/family name."""
    family = get_family(name)
    if family in FAMILY_COLORS:
        return FAMILY_COLORS[family]
    # Fallback to HSV hash for unknown families
    import colorsys
    h = (hash(name) & 0xFFFFFFFF) / 0xFFFFFFFF
    r, g, b = colorsys.hsv_to_rgb(h, saturation, value)
    return (r, g, b)


def deterministic_color_hex(name: str) -> str:
    """Return hex color for Plotly."""
    r, g, b = deterministic_color(name)
    return f'rgb({int(r*255)},{int(g*255)},{int(b*255)})'


def main():
    ap = argparse.ArgumentParser(description="Generate UMAP visualizations for module graphs")
    ap.add_argument('--graph', required=True, help='JSON with nodes/edges; each node should have a name/id')
    ap.add_argument('--out2d', required=False, help='Output path for 2D PNG')
    ap.add_argument('--out3d', required=False, help='Output path for interactive 3D HTML (Plotly)')
    ap.add_argument('--out3d-png', required=False, help='Output path for static 3D PNG (matplotlib)')
    ap.add_argument('--max-edge-lines', type=int, default=15000, help='Max edges to draw as lines')
    ap.add_argument('--label-top', type=int, default=30, help='Number of hub labels to annotate')
    ap.add_argument('--title', default='Module Dependency Graph', help='Title for visualizations')
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
    # groups by semantic family (using get_family for consistent coloring)
    top = []
    for nm in raw_names:
        top.append(get_family(nm))
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
        if args.out3d and HAVE_PLOTLY:
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
        # Group-aware coloring by semantic family; add edges and labels
        groups = top

        # Use family color palette
        def color_for(gname):
            rgb = FAMILY_COLORS.get(gname, FAMILY_COLORS['Other'])
            return (*rgb, 0.85)
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
        fig.tight_layout(); fig.savefig(args.out2d, dpi=300, facecolor='white', bbox_inches='tight')
        print(f"wrote {args.out2d}")
    if args.out3d and HAVE_PLOTLY:
        if HAVE_UMAP:
            reducer3 = umap.UMAP(n_components=3, random_state=42, n_neighbors=15, min_dist=0.15)
            Y3 = reducer3.fit_transform(X)
        else:
            # PCA fallback to min(3, rank)
            Xc = X - X.mean(axis=0)
            U,S,Vt = np.linalg.svd(Xc, full_matrices=False)
            k = 3 if Vt.shape[0] >= 3 else Vt.shape[0]
            Y3 = Xc @ Vt.T[:, :k]
            if k < 3:
                pad = np.zeros((Y3.shape[0], 3 - k))
                Y3 = np.hstack([Y3, pad])

        # Apply jitter to avoid collapsed points
        if Y3.size > 0:
            scale = (Y3.std(axis=0) + 1e-6) * 0.01
            Y3 = Y3 + np.random.default_rng(42).normal(0, scale, Y3.shape)

        # Build color list per point based on namespace
        point_colors = [deterministic_color_hex(g) for g in groups]

        # Build hover text with module details
        hover_texts = []
        for i, nm in enumerate(labels):
            di = deg_in.get(nm, 0)
            do = deg_out.get(nm, 0)
            hover_texts.append(
                f"<b>{nm}</b><br>"
                f"Namespace: {groups[i]}<br>"
                f"In-degree: {di}<br>"
                f"Out-degree: {do}<br>"
                f"Total: {di + do}"
            )

        # Create figure with edges first (as lines)
        fig = go.Figure()

        # Draw sampled edges as thin lines
        if edges:
            import random as _r
            _r.seed(42)
            m = min(len(edges), max(0, int(args.max_edge_lines)))
            sample = edges if len(edges) <= m else _r.sample(edges, m)

            edge_x, edge_y, edge_z = [], [], []
            for e in sample:
                u = e.get('source') or e.get('u')
                v = e.get('target') or e.get('v')
                iu = name_to_idx.get(u)
                iv = name_to_idx.get(v)
                if iu is None or iv is None:
                    continue
                edge_x.extend([Y3[iu, 0], Y3[iv, 0], None])
                edge_y.extend([Y3[iu, 1], Y3[iv, 1], None])
                edge_z.extend([Y3[iu, 2], Y3[iv, 2], None])

            fig.add_trace(go.Scatter3d(
                x=edge_x, y=edge_y, z=edge_z,
                mode='lines',
                line=dict(color='rgba(100,100,100,0.15)', width=0.5),
                hoverinfo='skip',
                name='Dependencies'
            ))

        # Add points grouped by namespace for legend
        gc_sorted = sorted(bucket.items(), key=lambda kv: -len(kv[1]))
        show_legend_groups = set([g for g, _ in gc_sorted[:12]])

        for gname, idxs in gc_sorted:
            fig.add_trace(go.Scatter3d(
                x=[Y3[j, 0] for j in idxs],
                y=[Y3[j, 1] for j in idxs],
                z=[Y3[j, 2] for j in idxs],
                mode='markers',
                marker=dict(
                    size=4,
                    color=deterministic_color_hex(gname),
                    opacity=0.85,
                    line=dict(width=0)
                ),
                text=[hover_texts[j] for j in idxs],
                hoverinfo='text',
                name=gname,
                showlegend=(gname in show_legend_groups)
            ))

        # Add hub labels as annotations
        if args.label_top > 0:
            d_scores = [(deg.get(nm, 0), i, nm) for nm, i in name_to_idx.items()]
            d_scores.sort(reverse=True)
            for _, i, nm in d_scores[:args.label_top]:
                short_name = nm.split('.')[-1]
                fig.add_trace(go.Scatter3d(
                    x=[Y3[i, 0]], y=[Y3[i, 1]], z=[Y3[i, 2]],
                    mode='text',
                    text=[short_name],
                    textfont=dict(size=9, color='rgba(0,0,0,0.7)'),
                    hoverinfo='skip',
                    showlegend=False
                ))

        # Layout configuration for clean visualization
        fig.update_layout(
            title=dict(text=args.title, x=0.5, font=dict(size=16)),
            scene=dict(
                xaxis=dict(showgrid=False, showticklabels=False, title='', showbackground=False),
                yaxis=dict(showgrid=False, showticklabels=False, title='', showbackground=False),
                zaxis=dict(showgrid=False, showticklabels=False, title='', showbackground=False),
                bgcolor='rgba(250,250,250,1)'
            ),
            width=1000,
            height=800,
            legend=dict(
                yanchor="top", y=0.99,
                xanchor="left", x=0.01,
                bgcolor='rgba(255,255,255,0.8)',
                font=dict(size=10)
            ),
            margin=dict(l=0, r=0, t=40, b=0)
        )

        fig.write_html(args.out3d)
        print(f"wrote {args.out3d}")

    # Also generate PNG if requested (can be in addition to HTML)
    if args.out3d_png and HAVE_MPL:
        # Static 3D using matplotlib with full group coloring and labels
        from mpl_toolkits.mplot3d import Axes3D  # noqa: F401
        if HAVE_UMAP:
            reducer3 = umap.UMAP(n_components=3, random_state=42, n_neighbors=15, min_dist=0.15)
            Y3 = reducer3.fit_transform(X)
        else:
            Xc = X - X.mean(axis=0)
            U, S, Vt = np.linalg.svd(Xc, full_matrices=False)
            k = min(3, Vt.shape[0])
            Y3 = Xc @ Vt.T[:, :k]

        # Ensure Y3 has 3 columns
        if Y3.shape[1] < 3:
            pad = np.zeros((Y3.shape[0], 3 - Y3.shape[1]))
            Y3 = np.hstack([Y3, pad])

        # Apply jitter to avoid collapsed points
        if Y3.size > 0:
            scale = (Y3.std(axis=0) + 1e-6) * 0.01
            Y3 = Y3 + np.random.default_rng(42).normal(0, scale, Y3.shape)

        fig = plt.figure(figsize=(10, 10))
        ax = fig.add_subplot(111, projection='3d')

        # Draw sampled edges
        if edges:
            import random as _r
            _r.seed(42)
            m = min(len(edges), max(0, int(args.max_edge_lines // 3)))
            sample = edges if len(edges) <= m else _r.sample(edges, m)
            for e in sample:
                u = e.get('source') or e.get('u')
                v = e.get('target') or e.get('v')
                iu = name_to_idx.get(u)
                iv = name_to_idx.get(v)
                if iu is None or iv is None:
                    continue
                x1, y1, z1 = Y3[iu, 0], Y3[iu, 1], Y3[iu, 2]
                x2, y2, z2 = Y3[iv, 0], Y3[iv, 1], Y3[iv, 2]
                ax.plot([x1, x2], [y1, y2], [z1, z2], color=(0.4, 0.4, 0.4, 0.08), linewidth=0.3)

        # Plot points by group with proper coloring
        gc_sorted = sorted(bucket.items(), key=lambda kv: -len(kv[1]))
        show_legend_groups = set([g for g, _ in gc_sorted[:12]])

        for gname, idxs in gc_sorted:
            color = deterministic_color(gname)
            color_with_alpha = (*color, 0.85)
            arrx = [Y3[j, 0] for j in idxs]
            arry = [Y3[j, 1] for j in idxs]
            arrz = [Y3[j, 2] for j in idxs]
            ax.scatter(arrx, arry, arrz, s=6,
                       label=gname if gname in show_legend_groups else None,
                       c=[color_with_alpha], edgecolors='none', depthshade=True)

        # Add hub labels
        if args.label_top > 0:
            d_scores = [(deg.get(nm, 0), i, nm) for nm, i in name_to_idx.items()]
            d_scores.sort(reverse=True)
            for _, i, nm in d_scores[:min(args.label_top, 20)]:  # Limit labels in 3D
                short_name = nm.split('.')[-1]
                ax.text(Y3[i, 0], Y3[i, 1], Y3[i, 2], short_name,
                        fontsize=7, color=(0, 0, 0, 0.7))

        # Clean up axes
        ax.set_xticks([])
        ax.set_yticks([])
        ax.set_zticks([])
        ax.xaxis.pane.fill = False
        ax.yaxis.pane.fill = False
        ax.zaxis.pane.fill = False
        ax.xaxis.pane.set_edgecolor('none')
        ax.yaxis.pane.set_edgecolor('none')
        ax.zaxis.pane.set_edgecolor('none')
        ax.grid(False)

        # Legend
        if len(show_legend_groups) > 0:
            ax.legend(fontsize=7, markerscale=2, loc='upper left', frameon=True,
                      facecolor='white', framealpha=0.8)

        ax.set_title(args.title, fontsize=12, pad=10)
        plt.tight_layout()
        plt.savefig(args.out3d_png, dpi=250, facecolor='white', bbox_inches='tight')
        print(f"wrote {args.out3d_png}")

if __name__ == '__main__':
    main()
