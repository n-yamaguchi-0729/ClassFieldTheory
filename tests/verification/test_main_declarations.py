import importlib.util
from pathlib import Path
import unittest

SPEC = importlib.util.spec_from_file_location("main_check", Path(__file__).with_name("check_main_declarations.py"))
M = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(M)

class MainDeclarationTests(unittest.TestCase):
    def test_presence_is_not_satisfied_by_wrong_kind_or_missing_theorem(self):
        contract = {"declarations": [{"name": "Main.result", "kind": "theorem"}]}
        row = {"name": "Main.result", "kind": "theorem", "primaryOwner": "ClassFieldTheory",
               "isSafeKernelRoot": True, "nonstandardAxioms": [], "hasTransitiveSorry": False}
        self.assertEqual(M.check(contract, [row]), 1)
        with self.assertRaisesRegex(ValueError, "Missing"):
            M.check(contract, [])
        with self.assertRaisesRegex(ValueError, "kind/owner"):
            M.check(contract, [dict(row, kind="definition")])

    def test_nonstandard_axiom_cannot_pass_presence(self):
        row = {"name": "Main.result", "kind": "theorem", "primaryOwner": "ClassFieldTheory",
               "isSafeKernelRoot": True, "nonstandardAxioms": ["sorryAx"], "hasTransitiveSorry": False}
        with self.assertRaisesRegex(ValueError, "proof policy"):
            M.check({"declarations": [{"name": "Main.result", "kind": "theorem"}]}, [row])

if __name__ == "__main__":
    unittest.main()
