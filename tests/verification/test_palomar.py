"""Small Python-only candidate checks; never run a compiler, sandbox, or kernel."""
import argparse
import importlib.util
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

SOURCE = Path(__file__).resolve().parents[2] / "scripts/verification/verify_palomar.py"
sys.path.insert(0, str(SOURCE.parent))
SPEC = importlib.util.spec_from_file_location("candidate_check", SOURCE)
P = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(P)


class PalomarTests(unittest.TestCase):
    def config(self):
        return {"challenge_module": "Challenge", "solution_module": "Solution",
                "theorem_names": [P.TARGET], "definition_names": [], "enable_nanoda": True,
                "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]}

    def test_config_cannot_disable_kernel_or_change_selected_statement(self):
        P.check_config(self.config())
        for update in ({"enable_nanoda": False}, {"theorem_names": []},
                       {"solution_module": "Challenge"}, {"definition_names": ["replacement"]},
                       {"permitted_axioms": ["propext", "Classical.choice", "sorryAx"]}):
            with self.subTest(update=update), self.assertRaises(RuntimeError):
                P.check_config(dict(self.config(), **update))

    def test_success_requires_exact_both_kernel_completions(self):
        lines = ["nanoda kernel accepts the solution", "Lean default kernel accepts the solution",
                 "Your solution is okay!"]
        P.check_completion("\n".join(lines))
        for wrong in (lines[1:], lines + lines, ["prefix " + line for line in lines]):
            with self.subTest(wrong=wrong), self.assertRaises(RuntimeError):
                P.check_completion("\n".join(wrong))

    def test_systemd_forwards_tools_and_forbids_root(self):
        env = {key: "/fixture/" + key for key in ("PATH", "HOME", "LEAN_PATH", "LEAN_NUM_THREADS",
               "COMPARATOR_LANDRUN", "COMPARATOR_LEAN4EXPORT", "COMPARATOR_NANODA")}
        with patch.object(P.shutil, "which", side_effect=lambda name: "/bin/" + name):
            command = P.comparator_command(Path("/project"), Path("/comparator"), Path("/config"),
                                           env, uid=1000, gid=1000)
            self.assertIn("--property=RestrictAddressFamilies=~AF_UNIX", command)
            self.assertIn("--uid=1000", command)
            for key, value in env.items():
                self.assertIn("--setenv=" + key + "=" + value, command)
            self.assertEqual(command[-5:], ["--", "lake", "env", "/comparator", "/config"])
            with self.assertRaises(RuntimeError):
                P.comparator_command(Path("/project"), Path("/comparator"), Path("/config"),
                                     env, uid=0, gid=0)

    def test_missing_parent_receipt_fails_without_process(self):
        with tempfile.TemporaryDirectory() as temp:
            base = Path(temp)
            args = argparse.Namespace(package_root=base, output=base / "result",
                                      verification=base / "missing", tools=base / "tools")
            runner = P.CandidateCheck(args)
            with patch.object(P.subprocess, "run", side_effect=AssertionError("No process")):
                self.assertEqual(runner.execute(), 1)
            final = P.read_json(runner.out / "final.json")
            self.assertFalse(final["passed"])
            self.assertFalse(final["submitted"])
            self.assertEqual(final["stages"], [])

    def test_failed_process_records_nonzero_and_cannot_pass(self):
        with tempfile.TemporaryDirectory() as temp:
            base = Path(temp)
            args = argparse.Namespace(package_root=base, output=base / "result",
                                      verification=base / "checks", tools=base / "tools")
            runner = P.CandidateCheck(args)
            runner.out.mkdir()
            with patch.object(runner, "guard"), patch.object(P.subprocess, "run",
                    return_value=subprocess.CompletedProcess([], 9)):
                with self.assertRaises(RuntimeError):
                    runner.stage("fixture", ["unexecuted"])
            row = P.read_json(runner.out / "fixture.json")
            self.assertFalse(row["passed"])
            self.assertEqual(row["exitCode"], 9)


if __name__ == "__main__":
    unittest.main()
