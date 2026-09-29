#!/usr/bin/env python3
"""
CNNA symmetric-birth / temporal-DtN derivation test
===================================================

Purpose
-------
This is an exact-rational Python surrogate for the proposed CNNA insertion path.

The construction deliberately separates:

1. RECORD / PROVENANCE
   - rooted finite b-ary birth tree
   - immutable parent relation and birth time
   - every primitive birth edge is reciprocal with the same normalized
     conductance C_* = 1
   - no primitive sibling edges
   - no primitive ancestor shortcut edges
   - no directed conductance parameters

2. LIVE STATIC RESPONSE
   - at every growth stage, construct the ordinary symmetric weighted
     graph Laplacian L_t from the currently born Record edges
   - compute exact Dirichlet-to-Neumann (DtN) / Schur responses Lambda
     on a canonical birth-local boundary

3. TEMPORAL RESPONSE
   - pre-birth boundary B^- consists of the causal ancestor chain
     root -> ... -> parent plus already-born older siblings
   - post-birth boundary B^+ = B^- union {newborn}
   - embed Lambda^- into the enlarged post-birth carrier by adding
     a zero newborn row/column: hat(Lambda^-)
   - define the ordered two-stage response:
         R_fwd = (1/C_*) Lambda^+ hat(Lambda^-)
         R_rev = (1/C_*) hat(Lambda^-) Lambda^+
   - define the temporal skew response:
         Omega = 1/2 (R_fwd - R_rev)
               = 1/(2 C_*) [Lambda^+, hat(Lambda^-)]

No Omega term is fed back as a primitive conductance.
Thus any skew part measured here is derived from:
    symmetric Record birth
    + exact DtN response
    + canonical birth order.

Important physical/control distinction
--------------------------------------
If the newborn is added as a passive leaf and then immediately Schur-eliminated,
the old-boundary response is unchanged. The script verifies this exactly:
    Lambda_after_on_old_boundary == Lambda_before.

The nonzero temporal skew arises only when the newborn becomes a new response
port and the pre/post responses are compared in their canonical time order.

For a unit boundary spike at parent p, the script also verifies the exact
closed-form identities:
    Lambda^+ =
      [[Lambda^- + C_* e_p e_p^T,  -C_* e_p],
       [        -C_* e_p^T,          C_* ]]

and
    [Lambda^+, hat(Lambda^-)] =
      [[C_*(e_p v^T - v e_p^T), C_* v],
       [               -C_* v^T,    0 ]],
where
    v = Lambda^- e_p
is the old DtN response column of the parent.

Hence the newborn temporal-response coupling to old port q is determined by
the already-existing parent response Lambda^-_{q,p}; its support is not chosen
by a sibling/ancestor broadcast rule.

This is a diagnostic/formalization prototype, not yet a Lean theorem or a
physical interpretation theorem.
"""

from __future__ import annotations

import argparse
import csv
from dataclasses import dataclass, field
from pathlib import Path
from collections import defaultdict
from typing import Dict, List, Tuple

import sympy as sp

Address = Tuple[int, ...]
CSTAR = sp.Rational(1)


@dataclass(frozen=True)
class BirthEvent:
    time: int
    parent: Address
    child: Address
    child_slot: int


@dataclass
class RecordState:
    branching: int
    root: Address = ()
    born: List[Address] = field(default_factory=lambda: [()])
    birth_time: Dict[Address, int] = field(default_factory=lambda: {(): 0})
    parent: Dict[Address, Address] = field(default_factory=dict)
    children: Dict[Address, List[Address]] = field(
        default_factory=lambda: defaultdict(list)
    )

    def add_birth(self, ev: BirthEvent) -> None:
        assert ev.child not in self.birth_time
        self.parent[ev.child] = ev.parent
        self.children[ev.parent].append(ev.child)
        self.birth_time[ev.child] = ev.time
        self.born.append(ev.child)


def bfs_schedule(branching: int, depth: int) -> List[BirthEvent]:
    """
    Canonical breadth-first schedule on Sigma_b^*.
    Root is (). Child slot k of parent p is p + (k,).
    """
    events: List[BirthEvent] = []
    frontier: List[Address] = [()]
    time = 0

    for _level in range(depth):
        next_frontier: List[Address] = []
        for p in frontier:
            for k in range(branching):
                time += 1
                c = p + (k,)
                events.append(BirthEvent(time, p, c, k))
                next_frontier.append(c)
        frontier = next_frontier

    return events


def ancestor_chain_root_to(parent: Address) -> List[Address]:
    """Canonical causal chain [root, ..., parent]."""
    return [parent[:k] for k in range(len(parent) + 1)]


def canonical_unique(xs: List[Address]) -> List[Address]:
    out: List[Address] = []
    seen = set()
    for x in xs:
        if x not in seen:
            out.append(x)
            seen.add(x)
    return out


def birth_boundary_pre(record: RecordState, parent: Address) -> List[Address]:
    """
    CNNA birth-local pre-boundary:
      causal predecessor chain + older siblings already born at this parent.

    This is the exact structural analogue used in the test. It contains no
    newborn and no future child.
    """
    return canonical_unique(
        ancestor_chain_root_to(parent) + list(record.children[parent])
    )


def symmetric_record_laplacian(
    record: RecordState,
    index: Dict[Address, int],
    ambient_size: int,
) -> sp.Matrix:
    """
    Ordinary reciprocal graph Laplacian of the currently born Record tree.
    Every primitive parent-child edge has C_* = 1 in both directions.
    """
    L = sp.zeros(ambient_size)

    for child, parent in record.parent.items():
        i = index[parent]
        j = index[child]
        c = CSTAR

        L[i, i] += c
        L[j, j] += c
        L[i, j] -= c
        L[j, i] -= c

    return L


def active_submatrix(
    L_ambient: sp.Matrix,
    born: List[Address],
    index: Dict[Address, int],
) -> Tuple[sp.Matrix, Dict[Address, int]]:
    ids = [index[a] for a in born]
    L = L_ambient.extract(ids, ids)
    local_index = {a: i for i, a in enumerate(born)}
    return L, local_index


def dtn_response(L: sp.Matrix, boundary: List[int]) -> sp.Matrix:
    """
    Exact Dirichlet-to-Neumann response:
        Lambda = L_BB - L_BI L_II^{-1} L_IB.

    For a connected resistor tree with nonempty boundary, the Dirichlet
    interior block is invertible. All arithmetic is exact SymPy Rational.
    """
    B = list(boundary)
    I = [i for i in range(L.rows) if i not in set(B)]

    if not I:
        return sp.Matrix(L.extract(B, B))

    L_BB = L.extract(B, B)
    L_BI = L.extract(B, I)
    L_IB = L.extract(I, B)
    L_II = L.extract(I, I)

    return sp.simplify(L_BB - L_BI * L_II.inv() * L_IB)


def embed_pre_response(Lambda_pre: sp.Matrix) -> sp.Matrix:
    """
    Canonical inclusion B^- -> B^+ = B^- union {newborn}.
    The unborn/newborn slot carries zero pre-birth response.
    """
    n = Lambda_pre.rows
    H = sp.zeros(n + 1)
    H[:n, :n] = Lambda_pre
    return H


def basis_vector(n: int, i: int) -> sp.Matrix:
    e = sp.zeros(n, 1)
    e[i, 0] = 1
    return e


def boundary_spike_prediction(
    Lambda_pre: sp.Matrix,
    parent_pos: int,
) -> sp.Matrix:
    """
    Exact post-birth DtN predicted for a reciprocal unit boundary spike.
    """
    m = Lambda_pre.rows
    e = basis_vector(m, parent_pos)

    out = sp.zeros(m + 1)
    out[:m, :m] = Lambda_pre + CSTAR * (e * e.T)
    out[:m, m] = -CSTAR * e
    out[m, :m] = (-CSTAR * e.T)
    out[m, m] = CSTAR
    return sp.simplify(out)


def temporal_commutator_prediction(
    Lambda_pre: sp.Matrix,
    parent_pos: int,
) -> sp.Matrix:
    """
    Closed form for:
        [Lambda_plus, hat(Lambda_pre)].

    v = Lambda_pre e_p is the old parent-response column.
    """
    m = Lambda_pre.rows
    e = basis_vector(m, parent_pos)
    v = Lambda_pre * e

    out = sp.zeros(m + 1)
    out[:m, :m] = CSTAR * (e * v.T - v * e.T)
    out[:m, m] = CSTAR * v
    out[m, :m] = -CSTAR * v.T
    return sp.simplify(out)


def temporal_response(
    Lambda_pre: sp.Matrix,
    Lambda_post: sp.Matrix,
) -> Tuple[sp.Matrix, sp.Matrix, sp.Matrix]:
    """
    Ordered response and its skew part:
        R_fwd = Lambda_post hat(Lambda_pre) / C_*
        R_rev = hat(Lambda_pre) Lambda_post / C_*
        Omega = (R_fwd - R_rev)/2
    """
    H = embed_pre_response(Lambda_pre)
    R_fwd = sp.simplify(Lambda_post * H / CSTAR)
    R_rev = sp.simplify(H * Lambda_post / CSTAR)
    Omega = sp.simplify((R_fwd - R_rev) / 2)
    return R_fwd, R_rev, Omega


def zero_sum_projector(b: int) -> sp.Matrix:
    return sp.eye(b) - sp.ones(b, b) / sp.Rational(b)


def zero_sum_basis(b: int) -> sp.Matrix:
    """
    Fixed basis q_i = e_i - e_(b-1) for F^perp.
    Used only for rank/span diagnostics.
    """
    Q = sp.zeros(b, b - 1)
    for i in range(b - 1):
        Q[i, i] = 1
        Q[b - 1, i] = -1
    return Q


def block_child_temporal_skew(
    Omega: sp.Matrix,
    boundary_post: List[Address],
    parent: Address,
    branching: int,
) -> sp.Matrix:
    """
    Pull Omega back to the canonical b child slots of parent, zero-pad unborn
    slots, then project onto F^perp.
    """
    pos = {a: i for i, a in enumerate(boundary_post)}
    M = sp.zeros(branching)

    for i in range(branching):
        ai = parent + (i,)
        if ai not in pos:
            continue
        for j in range(branching):
            aj = parent + (j,)
            if aj in pos:
                M[i, j] = Omega[pos[ai], pos[aj]]

    P = zero_sum_projector(branching)
    return sp.simplify(P * M * P)


def skew_coordinates(A: sp.Matrix, branching: int) -> sp.Matrix:
    """
    Coordinates of projected skew operator on a fixed basis of F^perp.
    """
    if branching <= 2:
        return sp.zeros(0, 1)

    Q = zero_sum_basis(branching)
    Aq = sp.simplify(Q.T * A * Q)

    return sp.Matrix([
        Aq[i, j]
        for i in range(branching - 1)
        for j in range(i + 1, branching - 1)
    ])


def nonzero_pairs(M: sp.Matrix, labels: List[Address]) -> List[str]:
    out = []
    for i in range(M.rows):
        for j in range(i + 1, M.cols):
            if M[i, j] != 0 or M[j, i] != 0:
                out.append(
                    f"{labels[i]} <-> {labels[j]} : "
                    f"{sp.simplify(M[i,j])} / {sp.simplify(M[j,i])}"
                )
    return out


def exact_zero(M: sp.Matrix) -> bool:
    return M == sp.zeros(M.rows, M.cols)


def frobenius_sq(M: sp.Matrix) -> sp.Expr:
    return sp.simplify(sum(x * x for x in M))


def run_case(branching: int, depth: int):
    events = bfs_schedule(branching, depth)

    # Fixed ambient address set for indexing only.
    all_addresses: List[Address] = [()]
    for ev in events:
        all_addresses.append(ev.child)
    index = {a: i for i, a in enumerate(all_addresses)}

    record = RecordState(branching=branching)
    ambient_L = sp.zeros(len(all_addresses))

    event_rows = []
    parent_skew_vectors: Dict[Address, List[sp.Matrix]] = defaultdict(list)
    selected_support_examples = []

    for ev in events:
        # ---------- PRE-BIRTH ----------
        boundary_pre = birth_boundary_pre(record, ev.parent)

        L_pre, local_pre = active_submatrix(ambient_L, record.born, index)
        Bpre_idx = [local_pre[a] for a in boundary_pre]
        Lambda_pre = dtn_response(L_pre, Bpre_idx)

        static_pre_skew = sp.simplify(Lambda_pre - Lambda_pre.T)

        # Parent position in the PRE boundary.
        parent_pos = boundary_pre.index(ev.parent)

        # ---------- BIRTH: only one symmetric C*=1 parent-child edge ----------
        record.add_birth(ev)
        ambient_L = symmetric_record_laplacian(
            record, index=index, ambient_size=len(all_addresses)
        )

        # ---------- POST-BIRTH ----------
        boundary_post = boundary_pre + [ev.child]

        L_post, local_post = active_submatrix(ambient_L, record.born, index)
        Bpost_idx = [local_post[a] for a in boundary_post]
        Lambda_post = dtn_response(L_post, Bpost_idx)

        static_post_skew = sp.simplify(Lambda_post - Lambda_post.T)

        # Control: if the newborn is not retained as a boundary port, a passive
        # dangling unit spike must not change the old-port DtN response.
        Lambda_after_old_boundary = dtn_response(
            L_post, [local_post[a] for a in boundary_pre]
        )
        old_boundary_defect = sp.simplify(
            Lambda_after_old_boundary - Lambda_pre
        )

        # Exact boundary-spike identity.
        Lambda_post_pred = boundary_spike_prediction(
            Lambda_pre, parent_pos
        )
        spike_formula_defect = sp.simplify(
            Lambda_post - Lambda_post_pred
        )

        # ---------- TEMPORAL RESPONSE ----------
        R_fwd, R_rev, Omega = temporal_response(
            Lambda_pre, Lambda_post
        )
        commutator = sp.simplify(2 * CSTAR * Omega)

        # Exact closed form from the old parent-response column.
        commutator_pred = temporal_commutator_prediction(
            Lambda_pre, parent_pos
        )
        commutator_formula_defect = sp.simplify(
            commutator - commutator_pred
        )

        reversal_defect = sp.simplify(R_fwd.T - R_rev)
        omega_skew_defect = sp.simplify(Omega + Omega.T)

        # ---------- LOCAL TRANSVERSE CHILD SECTOR ----------
        A_perp_time = block_child_temporal_skew(
            Omega,
            boundary_post,
            ev.parent,
            branching,
        )
        coords = skew_coordinates(A_perp_time, branching)
        parent_skew_vectors[ev.parent].append(coords)

        parent_col = Lambda_pre[:, parent_pos]
        parent_col_support = sum(1 for x in parent_col if x != 0)

        support = nonzero_pairs(Omega, boundary_post)

        event_rows.append({
            "b": branching,
            "depth": depth,
            "time": ev.time,
            "parent": repr(ev.parent),
            "child": repr(ev.child),
            "child_slot": ev.child_slot,
            "pre_boundary": repr(boundary_pre),
            "post_boundary": repr(boundary_post),
            "pre_boundary_size": len(boundary_pre),
            "post_boundary_size": len(boundary_post),
            "static_pre_skew_rank": static_pre_skew.rank(),
            "static_post_skew_rank": static_post_skew.rank(),
            "old_boundary_invariance_exact": exact_zero(old_boundary_defect),
            "boundary_spike_formula_exact": exact_zero(spike_formula_defect),
            "temporal_formula_exact": exact_zero(commutator_formula_defect),
            "time_reversal_transpose_exact": exact_zero(reversal_defect),
            "omega_skew_exact": exact_zero(omega_skew_defect),
            "parent_response_column_nonzero_entries": parent_col_support,
            "temporal_omega_rank": Omega.rank(),
            "temporal_omega_frobenius_sq": str(frobenius_sq(Omega)),
            "transverse_time_skew_rank": A_perp_time.rank(),
            "transverse_time_skew_frobenius_sq": str(
                frobenius_sq(A_perp_time)
            ),
            "temporal_support_pairs": " ; ".join(support),
        })

        # Representative support examples.
        if branching == 4 and ev.child in [
            (1,),
            (0, 0),
            (0, 1),
            (0, 2),
        ]:
            selected_support_examples.append({
                "time": ev.time,
                "parent": ev.parent,
                "child": ev.child,
                "boundary_pre": boundary_pre,
                "Lambda_pre": Lambda_pre,
                "Lambda_post": Lambda_post,
                "Omega": Omega,
                "support": support,
            })

    # Historical span per block parent.
    parent_spans: Dict[Address, int] = {}
    for p, vectors in parent_skew_vectors.items():
        if not vectors or vectors[0].rows == 0:
            parent_spans[p] = 0
        else:
            parent_spans[p] = sp.Matrix.hstack(*vectors).rank()

    for row in event_rows:
        # parse parent safely from the corresponding event index instead
        ev = events[row["time"] - 1]
        row["parent_historical_transverse_span_rank"] = parent_spans[
            ev.parent
        ]

    return event_rows, parent_spans, selected_support_examples


def write_csv(path: Path, rows: List[dict]) -> None:
    if not rows:
        return
    with path.open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--min-b", type=int, default=2)
    ap.add_argument("--max-b", type=int, default=6)
    ap.add_argument("--depth", type=int, default=2)
    ap.add_argument(
        "--outdir",
        type=Path,
        default=Path("cnna_symmetric_birth_temporal_dtn_out"),
    )
    args = ap.parse_args()
    args.outdir.mkdir(parents=True, exist_ok=True)

    all_rows = []
    summaries = []
    b4_examples = []

    for b in range(args.min_b, args.max_b + 1):
        rows, spans, examples = run_case(b, args.depth)
        all_rows.extend(rows)

        root_rows = [r for r in rows if r["parent"] == repr(())]
        root_span = spans.get((), 0)

        summaries.append({
            "b": b,
            "events": len(rows),
            "all_static_responses_symmetric": all(
                r["static_pre_skew_rank"] == 0
                and r["static_post_skew_rank"] == 0
                for r in rows
            ),
            "all_old_boundary_invariance_exact": all(
                r["old_boundary_invariance_exact"] for r in rows
            ),
            "all_boundary_spike_identities_exact": all(
                r["boundary_spike_formula_exact"] for r in rows
            ),
            "all_temporal_closed_forms_exact": all(
                r["temporal_formula_exact"] for r in rows
            ),
            "all_time_reversal_transpose_exact": all(
                r["time_reversal_transpose_exact"] for r in rows
            ),
            "all_omega_skew_exact": all(
                r["omega_skew_exact"] for r in rows
            ),
            "root_transverse_ranks": repr(
                [r["transverse_time_skew_rank"] for r in root_rows]
            ),
            "root_historical_transverse_span_rank": root_span,
        })

        if b == 4:
            b4_examples = examples

    write_csv(args.outdir / "events.csv", all_rows)
    write_csv(args.outdir / "summary.csv", summaries)

    lines = []
    lines.append("CNNA symmetric-birth / temporal-DtN exact test")
    lines.append(f"C_* = {CSTAR}; depth = {args.depth}")
    lines.append("")
    for s in summaries:
        lines.append(
            f"b={s['b']}: "
            f"static symmetric={s['all_static_responses_symmetric']}; "
            f"old-boundary invariant={s['all_old_boundary_invariance_exact']}; "
            f"spike identity={s['all_boundary_spike_identities_exact']}; "
            f"temporal closed form={s['all_temporal_closed_forms_exact']}; "
            f"Omega skew={s['all_omega_skew_exact']}; "
            f"root transverse ranks={s['root_transverse_ranks']}; "
            f"root historical span={s['root_historical_transverse_span_rank']}"
        )

    lines.append("")
    lines.append("Representative b=4 exact support examples:")
    for ex in b4_examples:
        lines.append(
            f"time={ex['time']} parent={ex['parent']} child={ex['child']}"
        )
        lines.append(f"  B^- = {ex['boundary_pre']}")
        lines.append(f"  Lambda^- = {ex['Lambda_pre'].tolist()}")
        lines.append(f"  Lambda^+ = {ex['Lambda_post'].tolist()}")
        lines.append(f"  Omega = {ex['Omega'].tolist()}")
        for pair in ex["support"]:
            lines.append(f"    {pair}")

    summary_text = "\n".join(lines)
    (args.outdir / "SUMMARY.txt").write_text(
        summary_text, encoding="utf-8"
    )
    print(summary_text)


if __name__ == "__main__":
    main()
