#!/usr/bin/env python3
"""Fail-closed gate for the two mandatory whole-repository verification jobs.

Only same-run, same-commit phases with complete matching physical source snapshots
may produce final.json. Partial phases are not standalone verification success.
Artifacts must be restored to their original RUNNER_TEMP paths; mismatches fail.
The large exported proof is checked in the proof job and need not be uploaded.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import verify

PHASE_STAGES = {
    "proof": ["build", "inventory", "selection", "export", "coverage", "nanoda"],
    "replay": ["build", "inventory", "selection", "replay"],
}


def phase_evidence(directory, phase, root, commit, run_id):
    directory = directory.resolve()
    final = verify.read_json(directory / "phase-final.json")
    verify.require(final.get("phase") == phase and final.get("phasePassed") is True
                   and final.get("passed") is False and final.get("exitCode") == 0
                   and final.get("status") == "finished", "Incomplete phase: " + phase)
    verify.require(final.get("workflowRun") == run_id, "Workflow run mismatch")
    inputs_path = directory / "inputs.json"
    verify.require(verify.digest(inputs_path) == final["inputsSha256"], "Inputs receipt changed")
    inputs = verify.read_json(inputs_path)
    verify.require(inputs.get("repositoryCommit") == commit, "Source commit mismatch")
    verify.require("version 4.35.0," in inputs["leanVersion"]
                   and verify.LEAN_COMMIT in inputs["leanVersion"], "Lean pin mismatch")
    for tool, pin in (("exporter", verify.EXPORT_COMMIT), ("nanoda", verify.NANODA_COMMIT)):
        verify.require(inputs[tool]["commit"] == pin and inputs[tool]["clean"] is True,
                       "Checker pin mismatch")
    # Re-audit physical source coverage and bind every maintained source/config.
    manifest = inputs["moduleManifest"]
    config = verify.generate_manifest.load_json(root / ".github/verification/manifest-config.json")
    verify.require(config.get("enforceSourcePolicy") is True, "Source policy disabled")
    current, report = verify.generate_manifest.analyze(root, config)
    verify.require(report["staticPassed"] and report["allPhysicalSourcesMapped"]
                   and current == manifest, "Physical source manifest mismatch")
    expected_paths = {root / row["path"] for row in manifest["moduleRows"].values()}
    expected_paths |= {root / name for name in ("lean-toolchain", "lake-manifest.json")}
    expected_paths |= {p for p in (root / "lakefile.toml", root / "lakefile.lean") if p.is_file()}
    expected_paths |= {p for p in (root / ".github/verification").rglob("*")
                       if p.is_file() and "__pycache__" not in p.parts}
    expected_paths.add(root / ".github/workflows/lean.yml")
    for path in expected_paths:
        verify.require(inputs["fileSha256"].get(str(path)) == verify.digest(path),
                       "Audited source/config changed: " + str(path))
    stages = final["stages"]
    verify.require([s["stage"] for s in stages] == PHASE_STAGES[phase], "Incomplete stage set")
    for stage in stages:
        path = directory / (stage["stage"] + ".json")
        verify.require(stage["passed"] is True and stage["receipt"] == str(path)
                       and stage["sha256"] == verify.digest(path), "Stage receipt changed")
        receipt = verify.read_json(path)
        verify.require(receipt["stage"] == stage["stage"] and receipt["passed"] is True
                       and receipt["status"] == "finished" and receipt["exitCode"] == 0,
                       "Unsuccessful stage")
        baseline = hashlib.sha256(json.dumps(inputs["fileSha256"], sort_keys=True).encode()).hexdigest()
        verify.require(receipt.get("inputsBeforeSha256") == baseline
                       and receipt.get("inputsAfterSha256") == baseline, "Input guard mismatch")
        for artifact, sha in receipt["artifactSha256"].items():
            artifact = Path(artifact).resolve()
            verify.require(artifact.is_relative_to(directory), "Artifact outside phase directory")
            # This was checked and hashed by the successful proof job; avoid multi-GB upload.
            if phase == "proof" and artifact == directory / "selected.ndjson":
                continue
            verify.require(artifact.is_file() and verify.digest(artifact) == sha,
                           "Stage artifact changed: " + str(artifact))
    return final, inputs


def combine(proof, replay, root, commit, run_id):
    verify.require(run_id and commit, "Missing workflow identity")
    root, proof, replay = root.resolve(), proof.resolve(), replay.resolve()
    verify.require(proof != replay, "Distinct phase directories required")
    verify.require(not (proof / "final.json").exists(), "Aggregate receipt already exists")
    pf, pi = phase_evidence(proof, "proof", root, commit, run_id)
    rf, ri = phase_evidence(replay, "replay", root, commit, run_id)
    verify.require(pi["moduleManifest"] == ri["moduleManifest"], "Phase scope differs")
    verify.require(pf["safeSelectedDeclarations"] == rf["safeSelectedDeclarations"],
                   "Phase selection counts differ")
    for name in ("safe-union.txt", "declarations.jsonl"):
        verify.require(verify.digest(proof / name) == verify.digest(replay / name),
                       "Phase declaration inventories differ")
    final = {
        "passed": True, "exitCode": 0, "status": "finished", "phase": "combined",
        "completedUtc": verify.utc(), "repositoryCommit": commit, "workflowRun": run_id,
        "safeSelectedDeclarations": pf["safeSelectedDeclarations"],
        "stages": pf["stages"] + [rf["stages"][-1]],
        "phaseEvidenceSha256": {str(d / "phase-final.json"): verify.digest(d / "phase-final.json")
                                for d in (proof, replay)},
    }
    verify.write_json(proof / "final.json", final)
    return final


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for arg in ("proof", "replay", "package-root"):
        parser.add_argument("--" + arg, required=True, type=Path)
    args = parser.parse_args()
    commit = subprocess.check_output(["git", "-C", str(args.package_root), "rev-parse", "HEAD"], text=True).strip()
    combine(args.proof, args.replay, args.package_root, commit, os.environ.get("GITHUB_RUN_ID"))
    print("PASS: both mandatory whole-repository verification phases completed")


if __name__ == "__main__":
    main()
