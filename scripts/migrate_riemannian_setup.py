#!/usr/bin/env python3
"""Migrate flat manifold variable blocks to the bundled setup classes.

Two-layer bundling:
  * files whose variable block has a Riemannian metric  -> `[RiemannianSetup I M]`
  * metric-free files (CompleteSpace+FiniteDimensional+IsLocallyConstant, no
    metric, no inner product)                            -> `[SmoothManifoldSetup I M]`
  * anything else (e.g. single-atom / finite-smoothness HessianLie) -> skipped

Scope: ONLY `variable` blocks and `omit` statements (multi-line aware); never
per-lemma signatures. Inserts the matching import.

Usage:
  python3 scripts/migrate_riemannian_setup.py --dry-run
  python3 scripts/migrate_riemannian_setup.py
"""
import re, sys, subprocess, difflib

RIEM_IMPORT   = "import OpenGALib.Riemannian.Metric.Util.RiemannianSetup"
SMOOTH_IMPORT = "import OpenGALib.Riemannian.TangentBundle.Util.SmoothManifoldSetup"

HASMETRIC = r"\[(?:[\w]+\s*:\s*)?(?:Riemannian\.)?HasMetric I M\]"
A_IPS   = r"\[InnerProductSpace ℝ E\]"
A_CPL   = r"\[CompleteSpace E\]"
A_FIN   = r"\[FiniteDimensional ℝ E\]"
A_NEZ   = r"\[NeZero \(Module\.finrank ℝ E\)\]"
A_BND   = r"\[I\.Boundaryless\]|\[ModelWithCorners\.Boundaryless I\]"
A_T2    = r"\[T2Space M\]"
A_LCC   = r"\[IsLocallyConstantChartedSpace H M\]"

RIEM_RE   = re.compile("|".join([A_IPS, A_CPL, A_FIN, A_NEZ, A_BND, A_T2, A_LCC, HASMETRIC]))
SMOOTH_RE = re.compile("|".join([A_CPL, A_FIN, A_LCC]))
# atoms strippable from omit statements (+ bare `hm` binder handled separately)
OMIT_RE   = re.compile("|".join([A_IPS, A_CPL, A_FIN, A_NEZ, A_BND, A_T2, A_LCC, HASMETRIC]))

def target_files():
    out = subprocess.run(
        ["grep", "-rl", "IsLocallyConstantChartedSpace H M", "OpenGALib", "--include=*.lean"],
        capture_output=True, text=True).stdout.split()
    skip = ("TangentBundle/LocallyConstant.lean", "Metric/Util/RiemannianSetup.lean",
            "TangentBundle/Util/SmoothManifoldSetup.lean", "Curvature/SectionalCurvature.lean")
    return [f for f in out if not any(s in f for s in skip)]

def classify(text):
    if re.search(HASMETRIC, text):
        return "riem"
    if re.search(A_CPL, text) and re.search(A_FIN, text) and re.search(A_LCC, text):
        return "smooth"
    return None

def is_block_cont(line):
    return line[:1] in (" ", "\t") and any(c in line for c in "[{(")

def ensure_normedspace(lines):
    """A file may rely on `InnerProductSpace ℝ E` to supply `NormedSpace ℝ E`;
    once IPS is bundled away, re-add the explicit `[NormedSpace ℝ E]`."""
    if any("[NormedSpace ℝ E]" in l for l in lines):
        return lines
    for k, l in enumerate(lines):
        if "[NormedAddCommGroup E]" in l:
            lines[k] = l.replace("[NormedAddCommGroup E]",
                                 "[NormedAddCommGroup E] [NormedSpace ℝ E]")
            return lines
    return lines

def insert_bundle(lines, inject):
    """Insert the bundle right after the `[IsManifold I ∞ M]` skeleton line, so
    instances that depend on the bundled ones (e.g. IsRiemannianManifold) see it."""
    for k, l in enumerate(lines):
        if "[IsManifold I ∞ M]" in l:
            lines.insert(k + 1, inject)
            return lines
    lines.append(inject)
    return lines

def tidy(blocktext):
    out = []
    for k, bl in enumerate(blocktext.split("\n")):
        m = re.match(r"^(\s*)(.*)$", bl)
        indent, rest = m.group(1), m.group(2)
        rest = re.sub(r"  +", " ", rest)
        rest = re.sub(r"\(\s+", "(", rest)
        bl = (indent + rest).rstrip()
        if k > 0 and bl.strip() == "":
            continue
        out.append(bl)
    return out

def migrate(text, kind):
    atom_re = RIEM_RE if kind == "riem" else SMOOTH_RE
    inject  = "  [RiemannianSetup I M]" if kind == "riem" else "  [SmoothManifoldSetup I M]"
    imp     = RIEM_IMPORT if kind == "riem" else SMOOTH_IMPORT
    lines = text.splitlines()
    out, i, n = [], 0, len(lines)
    while i < n:
        line = lines[i]
        # ---- variable block ----
        if re.match(r"^variable\b", line):
            block = [line]; j = i + 1
            while j < n and is_block_cont(lines[j]):
                block.append(lines[j]); j += 1
            bt = "\n".join(block)
            if atom_re.search(bt):
                bt = atom_re.sub("", bt)
                tl = ensure_normedspace(tidy(bt))
                tl = insert_bundle(tl, inject)
                out.extend(tl)
            else:
                out.extend(block)
            i = j; continue
        # ---- omit statement (possibly multi-line, until `in` or non-cont) ----
        if re.match(r"^\s*omit\b", line):
            stmt = [line]; j = i + 1
            if "in" not in re.sub(r"\[[^\]]*\]", "", line):     # no bare `in` yet
                while j < n and is_block_cont(lines[j]):
                    stmt.append(lines[j])
                    if re.search(r"\bin\b", re.sub(r"\[[^\]]*\]", "", lines[j])):
                        j += 1; break
                    j += 1
            st = "\n".join(stmt)
            st2 = OMIT_RE.sub("", st)
            st2 = re.sub(r"\bhm\b", "", st2)
            body = re.sub(r"\bomit\b|\bin\b|\s+", " ", st2).strip()
            if body == "":
                i = j; continue                                  # drop whole omit
            st2 = re.sub(r"  +", " ", st2)
            st2 = "\n".join(l.rstrip() for l in st2.split("\n") if l.strip())
            out.append(st2); i = j; continue
        out.append(line); i += 1
    res = "\n".join(out) + ("\n" if text.endswith("\n") else "")
    if imp not in res:
        rl = res.splitlines(keepends=True)
        last = max((idx for idx, l in enumerate(rl) if l.startswith("import ")), default=-1)
        if last >= 0:
            rl.insert(last + 1, imp + "\n"); res = "".join(rl)
    return res

def main():
    dry = "--dry-run" in sys.argv
    files = target_files()
    counts = {"riem": 0, "smooth": 0, "skip": 0}
    for f in files:
        with open(f, encoding="utf-8") as fh:
            orig = fh.read()
        kind = classify(orig)
        if kind is None:
            counts["skip"] += 1
            print(f"  SKIP (no full setup): {f}")
            continue
        new = migrate(orig, kind)
        if new != orig:
            counts[kind] += 1
            if dry:
                print("\n".join(difflib.unified_diff(
                    orig.splitlines(), new.splitlines(), fromfile=f, tofile=f, lineterm="")))
                print()
            else:
                with open(f, "w", encoding="utf-8") as fh:
                    fh.write(new)
    print(f"{'[dry-run] ' if dry else ''}riem={counts['riem']} smooth={counts['smooth']} skipped={counts['skip']}")

if __name__ == "__main__":
    main()
