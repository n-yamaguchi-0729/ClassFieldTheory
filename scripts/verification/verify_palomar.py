#!/usr/bin/env python3
"""Validate the local Kronecker–Weber candidate; never submit or register it."""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

from verify import (EXPORT_COMMIT, NANODA_COMMIT, LEAN, digest, git_identity,
                    read_json, require, utc, write_json)

HERE = Path(__file__).resolve().parent
PINS = {
    "comparator": ("https://github.com/leanprover/comparator", "575674928e239f5bc452aab72d1dd7b0f1326494"),
    "landrun": ("https://github.com/zouuup/landrun", "811cfff51ceaf3d9843708aa6d22e9b84ccac8b4"),
    "hostedVerifier": ("https://github.com/PalomarRegistry/PalomarSubmission", "c605f23466450a52999fcfb3c6d68ed8febc56bf"),
    "metadataSchema": ("https://github.com/mathlib-initiative/formalization.yaml", "99c678e569c7c4c0772db297c5ddd5e4c9b6322e"),
}
COMPARATOR_TOOLCHAIN = "leanprover/lean4:v4.34.0-rc1"
NESTED = Path("submissions/kronecker-weber")
TARGET = "KroneckerWeber.exists_cyclotomicEmbedding"


def check_config(config):
    require(set(config) == {"challenge_module", "solution_module", "theorem_names",
                           "definition_names", "permitted_axioms", "enable_nanoda"},
            "Unexpected Comparator configuration keys")
    require(config["challenge_module"] == "Challenge" and config["solution_module"] == "Solution",
            "Challenge/Solution modules changed")
    require(config["theorem_names"] == [TARGET] and config["definition_names"] == [],
            "Designated theorem/definition contract changed")
    axioms = config["permitted_axioms"]
    require(isinstance(axioms, list) and len(axioms) == 3 and
            set(axioms) == {"propext", "Quot.sound", "Classical.choice"}, "Wrong axiom policy")
    require(config["enable_nanoda"] is True, "NanoDa must be enabled")


def check_completion(log):
    lines = log.splitlines()
    for marker in ("nanoda kernel accepts the solution", "Lean default kernel accepts the solution",
                   "Your solution is okay!"):
        require(lines.count(marker) == 1, "Missing exact Comparator completion: " + marker)


def comparator_command(project, binary, config, environment, *, uid, gid):
    """Official Comparator CLI behind the README's required AF_UNIX restriction."""
    require(uid != 0, "Comparator must run as an unprivileged user")
    systemd = shutil.which("systemd-run")
    require(systemd is not None, "systemd-run is required; no unconfined fallback")
    sudo = shutil.which("sudo")
    command = ([sudo, "-n", systemd, f"--uid={uid}", f"--gid={gid}"] if sudo else
               [systemd, "--user"])
    command += ["--quiet", "--collect", "--wait", "--pipe",
                "--property=RestrictAddressFamilies=~AF_UNIX",
                "--property=NoNewPrivileges=yes", "--property=RestrictSUIDSGID=yes",
                "--property=LimitNOFILE=524288", f"--working-directory={project}"]
    for key in ("PATH", "HOME", "LEAN_PATH", "LEAN_NUM_THREADS", "COMPARATOR_LANDRUN",
                "COMPARATOR_LEAN4EXPORT", "COMPARATOR_NANODA"):
        value = environment[key]
        require(not any(c in value for c in "\0\n\r"), "Invalid execution environment")
        command.append(f"--setenv={key}={value}")
    return command + ["--", "lake", "env", str(binary), str(config)]


class CandidateCheck:
    def __init__(self, args):
        self.root, self.out = args.package_root.resolve(), args.output.resolve()
        self.checks, self.tools = args.verification.resolve(), args.tools.resolve()
        self.project = self.root / NESTED
        self.baseline, self.receipts, self.checkouts = {}, [], {}
        self.environment = dict(os.environ, LEAN_NUM_THREADS="1", PYTHONDONTWRITEBYTECODE="1")
        for key in ("LEAN_PATH", "LEAN_SYSROOT", "ELAN_TOOLCHAIN"):
            self.environment.pop(key, None)

    def bind(self, paths):
        for path in paths:
            path = path.resolve(strict=True)
            require(path.is_file(), "Missing input artifact: " + str(path))
            self.baseline[str(path)] = digest(path)

    def guard(self):
        require(all(Path(p).is_file() and digest(Path(p)) == sha
                    for p, sha in self.baseline.items()), "Bound source/config/tool artifact changed")
        for name, checkout in self.checkouts.items():
            git_identity(checkout, PINS[name][1])
        git_identity(self.tools / "lean4export", EXPORT_COMMIT)
        git_identity(self.tools / "nanoda_lib", NANODA_COMMIT)

    def stage(self, name, command, *, cwd=None, env=None, validate=None):
        started = time.monotonic()
        path, log = self.out / (name + ".json"), self.out / (name + ".log")
        row = {"stage": name, "passed": False, "startedUtc": utc(), "exitCode": None,
               "command": command, "cwd": str(cwd or self.root)}
        write_json(path, row)
        try:
            self.guard()
            with log.open("wb") as stream:
                proc = subprocess.run(command, cwd=cwd or self.root,
                                      env=env or self.environment, stdout=stream, stderr=subprocess.STDOUT)
            row["exitCode"] = proc.returncode
            require(proc.returncode == 0, name + " failed")
            if validate:
                validate(log)
            self.guard()
            row["passed"] = True
        except Exception as error:
            row["error"] = str(error)
            raise
        finally:
            row.update(completedUtc=utc(), elapsedSeconds=round(time.monotonic() - started, 3),
                       logSha256=digest(log) if log.is_file() else None)
            write_json(path, row)
            self.receipts.append({"stage": name, "passed": row["passed"],
                                  "path": str(path), "sha256": digest(path)})
            self.bind([path] + ([log] if log.is_file() else []))

    def checkout(self, name):
        url, commit = PINS[name]
        dest = self.tools / ("palomar-" + name)
        require(not dest.exists(), "Fresh checker checkout required: " + str(dest))
        self.stage(name + "-init", ["git", "init", str(dest)])
        self.stage(name + "-remote", ["git", "-C", str(dest), "remote", "add", "origin", url])
        self.stage(name + "-fetch", ["git", "-C", str(dest), "fetch", "--depth=1", "origin", commit])
        self.stage(name + "-checkout", ["git", "-C", str(dest), "checkout", "--detach", commit])
        git_identity(dest, commit)
        self.checkouts[name] = dest
        return dest

    def inputs(self):
        final = read_json(self.checks / "final.json")
        require(final.get("passed") is True and final.get("exitCode") == 0,
                "Complete parent verification must pass first")
        inputs_path = self.checks / "inputs.json"
        require(digest(inputs_path) == final["inputsSha256"], "Parent input receipt changed")
        parent = read_json(inputs_path)
        self.baseline.update(parent["fileSha256"])
        for row in final["stages"]:
            path = Path(row["receipt"])
            require(row["passed"] and digest(path) == row["sha256"], "Parent stage receipt changed")
            self.bind([path])
        self.bind([inputs_path, self.checks / "final.json"])
        require(self.project.is_dir(), "Missing nested submission package")
        self.bind(p for p in self.project.iterdir() if p.is_file())
        self.bind([Path(__file__), HERE / "palomar_metadata.py", HERE / "palomar-requirements.txt"])
        require((self.project / "lean-toolchain").read_text().strip() == LEAN,
                "Nested toolchain differs from the parent/exporter")
        check_config(read_json(self.project / "comparator.json"))
        pins = read_json(self.project / "verification-pins.json")
        for key, (url, commit) in PINS.items():
            require(pins[key]["commit"] == commit and pins[key]["repository"].removesuffix(".git") == url,
                    "Submission checker pin mismatch: " + key)
        require(pins["lean4export"]["commit"] == EXPORT_COMMIT and
                pins["nanoda"]["commit"] == NANODA_COMMIT, "Submission export/kernel pin mismatch")
        self.source_commit = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=self.root,
                                                      env=self.environment, text=True).strip()
        self.guard()

    def execute(self):
        require(not self.out.exists(), "Use a fresh candidate-check output directory")
        self.out.mkdir(parents=True)
        started = time.monotonic()
        final = {"passed": False, "startedUtc": utc(), "submitted": False, "registered": False}
        write_json(self.out / "final.json", final)
        code = 1
        try:
            self.inputs()
            pipeline = self.checkout("hostedVerifier")
            schema = self.checkout("metadataSchema") / "schema/v0.4.schema.json"
            venv = self.tools / "palomar-python"
            require(not venv.exists(), "Fresh Python environment required")
            self.stage("python-environment", [sys.executable, "-m", "venv", str(venv)])
            python = venv / "bin/python"
            self.stage("metadata-dependencies", [str(python), "-m", "pip", "install", "--require-hashes",
                       "--no-deps", "--only-binary=:all:", "-r", str(HERE / "palomar-requirements.txt")])
            self.bind([schema, python])
            metadata_report = self.out / "metadata-result.json"
            self.stage("metadata", [str(python), str(HERE / "palomar_metadata.py"),
                       "--pipeline", str(pipeline), "--schema", str(schema),
                       "--metadata", str(self.project / "formalization.yaml"), "--output", str(metadata_report)],
                       validate=lambda _: require(read_json(metadata_report).get("passed") is True,
                                                  "Metadata validator did not pass"))
            self.bind([metadata_report])
            comparator = self.checkout("comparator")
            require((comparator / "lean-toolchain").read_text().strip() == COMPARATOR_TOOLCHAIN,
                    "Comparator's own pinned toolchain changed")
            self.stage("comparator-build", ["lake", "--no-ansi", "build", "comparator"], cwd=comparator)
            landrun = self.checkout("landrun")
            landrun_bin = self.tools / "palomar-bin/landrun"
            landrun_bin.parent.mkdir()
            go_env = dict(self.environment, CGO_ENABLED="0", GOFLAGS="-mod=readonly", GOTOOLCHAIN="go1.24.0")
            self.stage("go-version", ["go", "version"], env=go_env,
                       validate=lambda log: require("go1.24.0" in log.read_text(), "Wrong Go toolchain"))
            self.stage("landrun-build", ["go", "build", "-trimpath", "-o", str(landrun_bin), "./cmd/landrun"],
                       cwd=landrun, env=go_env)
            # The build output is deliberately outside tracked sources; keep checkout identity clean.
            exporter = self.tools / "lean4export"
            self.stage("exporter-binary", ["lake", "--no-ansi", "build", "lean4export"], cwd=exporter)
            binaries = [comparator / ".lake/build/bin/comparator", landrun_bin,
                        exporter / ".lake/build/bin/lean4export", self.tools / "nanoda_lib/target/release/nanoda_bin"]
            self.bind(binaries + [comparator / "lean-toolchain", landrun / "go.mod", landrun / "go.sum"])
            self.stage("challenge-build", ["lake", "--no-ansi", "build", "Challenge"], cwd=self.project)
            self.stage("solution-build", ["lake", "--no-ansi", "--wfail", "build", "Solution"], cwd=self.project)
            nested_manifest = self.project / "lake-manifest.json"
            require(nested_manifest.is_file(), "Nested dependency manifest was not produced")
            self.bind([nested_manifest])
            shutil.copyfile(nested_manifest, self.out / "nested-lake-manifest.json")
            lean_path = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"],
                        cwd=self.project, env=self.environment, text=True).strip()
            environment = dict(self.environment, LEAN_PATH=lean_path,
                    COMPARATOR_LANDRUN=str(binaries[1]), COMPARATOR_LEAN4EXPORT=str(binaries[2]),
                    COMPARATOR_NANODA=str(binaries[3]))
            command = comparator_command(self.project, binaries[0], self.project / "comparator.json",
                                         environment, uid=os.getuid(), gid=os.getgid())
            self.stage("comparator", command, cwd=self.project, env=environment,
                       validate=lambda log: check_completion(log.read_text()))
            self.guard()
            require(all(row["passed"] for row in self.receipts), "A required candidate stage failed")
            final.update(passed=True, pins=PINS, comparatorToolchain=COMPARATOR_TOOLCHAIN,
                         targetToolchain=LEAN, boundSha256=self.baseline)
            code = 0
        except Exception as error:
            final["error"] = str(error)
        finally:
            final.update(completedUtc=utc(), elapsedSeconds=round(time.monotonic() - started, 3),
                         exitCode=code, stages=self.receipts, boundSha256=self.baseline,
                         sourceCommit=getattr(self, "source_commit", None),
                         scope="Local candidate schema/profile and exact theorem comparison with both kernels; not a hosted Palomar provenance audit or acceptance.")
            write_json(self.out / "final.json", final)
        return code


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("package-root", "verification", "tools", "output"):
        parser.add_argument("--" + name, type=Path, required=True)
    args = parser.parse_args()
    try:
        return CandidateCheck(args).execute()
    except Exception as error:
        print(str(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
