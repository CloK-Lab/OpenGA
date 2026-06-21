#!/usr/bin/env python3
"""Second pass: fix `omit` lines after RiemannianSetup migration.

`omit [X] in` requires X to be a direct section variable. Once the eight atoms
are bundled into `[RiemannianSetup I M]`, omitting them individually is invalid.
This strips the bundled atoms (and the bare `hm` binder name) from every `omit`
line in the given files, dropping the line entirely if nothing else remains.
Non-bundled omits (e.g. `[IsManifold I ∞ M]`) are preserved.

Usage: python3 scripts/fix_omit_after_setup.py FILE [FILE ...]
"""
import re, sys

BUNDLED = [
    r"\[InnerProductSpace ℝ E\]",
    r"\[CompleteSpace E\]",
    r"\[FiniteDimensional ℝ E\]",
    r"\[NeZero \(Module\.finrank ℝ E\)\]",
    r"\[I\.Boundaryless\]",
    r"\[ModelWithCorners\.Boundaryless I\]",
    r"\[T2Space M\]",
    r"\[IsLocallyConstantChartedSpace H M\]",
    r"\[hm : HasMetric I M\]",
    r"\[HasMetric I M\]",
]
BUNDLED_RE = re.compile("|".join(BUNDLED))

def fix_line(line):
    m = re.match(r"^(\s*omit\b)(.*?)(\bin\b\s*)?$", line)
    if not m:
        return line
    head, body, tail = m.group(1), m.group(2), m.group(3) or ""
    body = BUNDLED_RE.sub("", body)
    body = re.sub(r"\bhm\b", "", body)          # bare named HasMetric binder
    body = re.sub(r"  +", " ", body).strip()
    if body == "":
        return None                              # nothing left to omit → drop line
    return f"{head} {body}" + (" in" if tail.strip() else "")

def main():
    for f in sys.argv[1:]:
        with open(f, encoding="utf-8") as fh:
            lines = fh.read().splitlines(keepends=False)
        out, changed = [], False
        for line in lines:
            if re.match(r"^\s*omit\b", line):
                fixed = fix_line(line)
                if fixed != line:
                    changed = True
                if fixed is not None:
                    out.append(fixed)
            else:
                out.append(line)
        if changed:
            with open(f, "w", encoding="utf-8") as fh:
                fh.write("\n".join(out) + "\n")
            print(f"fixed omit in {f}")

if __name__ == "__main__":
    main()
