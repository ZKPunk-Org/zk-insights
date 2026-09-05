#!/usr/bin/env python3
from __future__ import annotations

import argparse
from pathlib import Path


def replace_all(path: Path, old: str, new: str, *, expected: int | None = None) -> None:
    text = path.read_text(encoding="utf-8")
    count = text.count(old)
    if count == 0:
        raise RuntimeError(f"{path}: missing expected text: {old!r}")
    if expected is not None and count != expected:
        raise RuntimeError(f"{path}: expected {expected} occurrences of {old!r}, found {count}")
    path.write_text(text.replace(old, new), encoding="utf-8")
    print(f"patched {path}: {count} × {old!r}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("root", type=Path)
    args = parser.parse_args()
    sub = args.root / "ProximityPrize" / "SubmissionLower"

    p = sub / "ContactAlignmentParameters.lean"
    replacements = [
        ("def agreements : ℕ := 185354", "def agreements : ℕ := 185055"),
        ("def alignmentBudget : ℕ := 100000000000000000",
         "def alignmentBudget : ℕ := 137232143318053042"),
        ("def multiplicity : ℕ := 13", "def multiplicity : ℕ := 14"),
        ("def seedTotalCap : ℕ := 169", "def seedTotalCap : ℕ := 194"),
        ("def slopeCap : ℕ := 3", "def slopeCap : ℕ := 4"),
        ("weightedCap = 2409602 ∧ yCap = 18 ∧ gap = 54283 ∧\n"
         "    errors = 76790 ∧ algebraicCap = 845",
         "weightedCap = 2590770 ∧ yCap = 19 ∧ gap = 53984 ∧\n"
         "    errors = 77089 ∧ algebraicCap = 1358"),
        ("coefficientCount = 13096794720", "coefficientCount = 20819496100"),
        ("localContactRank = 49960", "localContactRank = 79420"),
        ("totalNumerator = 228788847483348849235588882",
         "totalNumerator = 399878559201234662384898048"),
        ("gap ^ 2 = 2946644089", "gap ^ 2 = 2914272256"),
        ("totalNumerator = 77643868948215160 * gap ^ 2 + 921399642 ∧\n"
         "    921399642 < gap ^ 2",
         "totalNumerator = 137213864757471260 * gap ^ 2 + 649535488 ∧\n"
         "    649535488 < gap ^ 2"),
    ]
    for old, new in replacements:
        replace_all(p, old, new, expected=1)

    p = sub / "ContactImplicitLiftParameters.lean"
    replacements = [
        ("implicitWeightedCap = 12048010 ∧ implicitYCap = 91 ∧\n"
         "    liftedLastTail = ⟨2192737821, 12048010, 20361136900⟩ ∧\n"
         "    liftedAgreement = ⟨23854923, 131071, 221509991⟩",
         "implicitWeightedCap = 18135390 ∧ implicitYCap = 138 ∧\n"
         "    liftedLastTail = ⟨5005367641, 18135390, 49255719240⟩ ∧\n"
         "    liftedAgreement = ⟨36175597, 131071, 355988837⟩"),
        ("mixed liftedSurface implicitCut unitY = 845 ∧\n"
         "    mixed liftedSurface implicitCut unitR = 153790 ∧\n"
         "    mixed liftedSurface implicitCut unitZ = 91",
         "mixed liftedSurface implicitCut unitY = 1358 ∧\n"
         "    mixed liftedSurface implicitCut unitR = 374808 ∧\n"
         "    mixed liftedSurface implicitCut unitZ = 138"),
        ("liftedSingularNumerator = 317589849985539807",
         "liftedSingularNumerator = 1139469983092841216"),
        ("liftedTotalNumerator = 228802875770776585458064808",
         "liftedTotalNumerator = 399931827903217763501092864"),
        ("liftedTotalNumerator = 77648629715720168 * gap ^ 2 + 2042777856 ∧\n"
         "    2042777856 < gap ^ 2",
         "liftedTotalNumerator = 137232143318053041 * gap ^ 2 + 2178362368 ∧\n"
         "    2178362368 < gap ^ 2"),
    ]
    for old, new in replacements:
        replace_all(p, old, new, expected=1)

    p = sub / "ContactInterpolation.lean"
    replacements = [
        ("CoefficientIndex 2409602 131071 169 3",
         "CoefficientIndex 2590770 131071 194 4"),
        ("IRSProfile.Field 2409602 131071 169 3",
         "IRSProfile.Field 2590770 131071 194 4"),
        ("(r : Fin 13)", "(r : Fin 14)"),
        ("(13 - r.val)", "(14 - r.val)"),
        ("IRSProfile.Field 2590770 131071 194 4 13",
         "IRSProfile.Field 2590770 131071 194 4 14"),
    ]
    for old, new in replacements:
        replace_all(p, old, new)

    p = sub / "ContactTranslation.lean"
    replacements = [
        ("IRSProfile.Field 2409602 131071 169 3",
         "IRSProfile.Field 2590770 131071 194 4"),
        ("^ (13 - r)", "^ (14 - r)"),
        ("IRSProfile.Field 2590770 131071 194 4 13",
         "IRSProfile.Field 2590770 131071 194 4 14"),
        ("P.natDegree ≤ 131071 → 185354 ≤ support.card",
         "P.natDegree ≤ 131071 → 185055 ≤ support.card"),
        ("support 13", "support 14"),
        ("2590770 ≤ 13 * support.card", "2590770 ≤ 14 * support.card"),
    ]
    for old, new in replacements:
        replace_all(p, old, new)

    p = sub / "ContactGlobalSelectedFamilies.lean"
    replacements = [
        ("(∑ F : RegularIndex Q, (regularVector Q F).y) ≤ 18 ∧\n"
         "      (∑ F : RegularIndex Q, (regularVector Q F).r) ≤ 3 ∧\n"
         "      (∑ F : RegularIndex Q, (regularVector Q F).z) ≤ 169",
         "(∑ F : RegularIndex Q, (regularVector Q F).y) ≤ 19 ∧\n"
         "      (∑ F : RegularIndex Q, (regularVector Q F).r) ≤ 4 ∧\n"
         "      (∑ F : RegularIndex Q, (regularVector Q F).z) ≤ 194"),
        ("(∑ F ∈ positiveRFactors Q, F.degreeOf (1 : Fin 4)) ≤ 18",
         "(∑ F ∈ positiveRFactors Q, F.degreeOf (1 : Fin 4)) ≤ 19"),
    ]
    for old, new in replacements:
        replace_all(p, old, new, expected=1)

    p = sub / "ContactCountingLedger.lean"
    replacements = [
        ("(hy : (∑ i, (v i).y) ≤ 18) (hr : (∑ i, (v i).r) ≤ 3)\n"
         "    (hz : (∑ i, (v i).z) ≤ 169)",
         "(hy : (∑ i, (v i).y) ≤ 19) (hr : (∑ i, (v i).r) ≤ 4)\n"
         "    (hz : (∑ i, (v i).z) ≤ 194)"),
        ("(hregularY : (∑ i, (v i).y) ≤ 18) (hregularR : (∑ i, (v i).r) ≤ 3)\n"
         "    (hregularZ : (∑ i, (v i).z) ≤ 169)",
         "(hregularY : (∑ i, (v i).y) ≤ 19) (hregularR : (∑ i, (v i).r) ≤ 4)\n"
         "    (hregularZ : (∑ i, (v i).z) ≤ 194)"),
    ]
    for old, new in replacements:
        replace_all(p, old, new, expected=1)

    p = sub / "ContactFrozenAlignment6401.lean"
    replace_all(p, "76790", "77089")
    replace_all(p, "100000000000000000", "137232143318053042")

    p = sub / "ContactAlignment6401.lean"
    replace_all(p, "76790", "77089")
    replace_all(p, "100000000000000000", "137232143318053042")

    checks = {
        "ContactAlignmentParameters.lean": [
            "def agreements : ℕ := 185055",
            "def alignmentBudget : ℕ := 137232143318053042",
            "def multiplicity : ℕ := 14",
            "def seedTotalCap : ℕ := 194",
            "def slopeCap : ℕ := 4",
        ],
        "ContactTranslation.lean": [
            "globalCoefficientBox IRSProfile.Field 2590770 131071 194 4",
            "185055 ≤ support.card",
            "support 14",
        ],
        "ContactAlignment6401.lean": [
            "AffineLineAlignmentBound IRSProfile.baseCode 77089 137232143318053042",
        ],
    }
    for name, needles in checks.items():
        text = (sub / name).read_text(encoding="utf-8")
        for needle in needles:
            if needle not in text:
                raise RuntimeError(f"{name}: post-patch check failed: {needle!r}")

    print("K14 proof-source patch completed successfully.")


if __name__ == "__main__":
    main()
