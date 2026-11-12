"""Live diagnostics must not alter checker output or fail-closed receipts."""
from argparse import Namespace
from contextlib import redirect_stdout
from io import StringIO
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import verify


class ProgressTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        root = Path(self.temp.name)
        self.pipeline = verify.Pipeline(Namespace(
            package_root=root, manifest=root / 'modules.json', output=root,
            exporter_checkout=root, nanoda_checkout=root, nanoda_binary=root / 'nanoda'))
        self.guard = patch.object(self.pipeline, 'guard', return_value='unchanged')
        self.guard.start()
        self.addCleanup(self.guard.stop)

    def run_stage(self, command, **kwargs):
        output = StringIO()
        with redirect_stdout(output), patch.object(verify, 'HEARTBEAT_SECONDS', 0.01):
            try:
                self.pipeline.stage('checker', [sys.executable, '-c', command], **kwargs)
            except verify.VerificationError:
                pass
        receipt = json.loads((self.pipeline.out / 'checker.json').read_text())
        self.assertIn('START checker', output.getvalue())
        self.assertIn('END checker', output.getvalue())
        self.assertEqual(self.pipeline.stages[0]['passed'], receipt['passed'])
        self.assertEqual(self.pipeline.stages[0]['sha256'],
                         verify.digest(self.pipeline.out / 'checker.json'))
        return receipt, output.getvalue()

    def test_heartbeat_and_exact_separate_export_output(self):
        exported = self.pipeline.out / 'selected.ndjson'
        receipt, live = self.run_stage(
            'import time; time.sleep(0.1); print("export payload")', output=exported)
        self.assertTrue(receipt['passed'])
        self.assertEqual(receipt['exitCode'], 0)
        self.assertIn('RUNNING checker', live)
        self.assertEqual(exported.read_text(), 'export payload\n')
        self.assertEqual((self.pipeline.out / 'checker.log').read_text(), '')
        self.assertEqual(receipt['artifactSha256'][str(exported)], verify.digest(exported))

    def test_process_failure_remains_failure(self):
        receipt, live = self.run_stage('print("checker rejected proof"); raise SystemExit(7)')
        self.assertFalse(receipt['passed'])
        self.assertEqual(receipt['exitCode'], 7)
        self.assertIn('ERROR checker: checker process failed', live)
        self.assertEqual((self.pipeline.out / 'checker.log').read_text(), 'checker rejected proof\n')

    def test_validator_failure_remains_failure(self):
        def reject():
            raise verify.VerificationError('missing declarations')
        receipt, live = self.run_stage('print("process finished")', validate=reject)
        self.assertFalse(receipt['passed'])
        self.assertEqual(receipt['exitCode'], 0)
        self.assertIn('missing declarations', live)

    def test_missing_artifact_remains_failure(self):
        receipt, live = self.run_stage('pass', artifacts=[self.pipeline.out / 'absent'])
        self.assertFalse(receipt['passed'])
        self.assertIn('Missing stage output', live)

    def test_guard_failure_remains_failure(self):
        with patch.object(self.pipeline, 'guard', side_effect=verify.VerificationError('changed input')):
            receipt, live = self.run_stage('raise SystemExit("must not run")')
        self.assertFalse(receipt['passed'])
        self.assertEqual(receipt['exitCode'], 1)
        self.assertIn('changed input', live)
        self.assertFalse((self.pipeline.out / 'checker.log').exists())


if __name__ == '__main__':
    unittest.main()
