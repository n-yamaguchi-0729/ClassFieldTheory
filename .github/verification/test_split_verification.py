#!/usr/bin/env python3
"""Synthetic negative tests for the split gate; these do not replace Lean checking."""
import copy
import hashlib
import json
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch
import combine_verification as gate
import verify

class GateTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.proof, self.replay = self.root / 'proof', self.root / 'replay'
        for directory in (self.proof, self.replay):
            directory.mkdir()
        for name in ('lean-toolchain', 'lake-manifest.json', '.github/workflows/lean.yml',
                     '.github/verification/manifest-config.json', 'Demo.lean'):
            p = self.root / name
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text('{"enforceSourcePolicy": true}' if name.endswith('manifest-config.json') else 'fixture')
        self.manifest = {'moduleRows': {'Demo': {'path': 'Demo.lean'}}}
        self.addCleanup(patch.stopall)
        patch.object(verify.generate_manifest, 'analyze',
                     return_value=(self.manifest, {'staticPassed': True, 'allPhysicalSourcesMapped': True})).start()
        paths = [p for p in self.root.rglob('*') if p.is_file()]
        self.inputs = {'repositoryCommit': 'commit', 'moduleManifest': self.manifest,
                       'fileSha256': {str(p): verify.digest(p) for p in paths},
                       'leanVersion': 'version 4.35.0, ' + verify.LEAN_COMMIT,
                       'exporter': {'commit': verify.EXPORT_COMMIT, 'clean': True},
                       'nanoda': {'commit': verify.NANODA_COMMIT, 'clean': True}}
        self.baseline = hashlib.sha256(json.dumps(self.inputs['fileSha256'], sort_keys=True).encode()).hexdigest()
        for phase, directory in [('proof', self.proof), ('replay', self.replay)]:
            verify.write_json(directory / 'inputs.json', self.inputs)
            for name in ('safe-union.txt', 'declarations.jsonl'):
                (directory / name).write_text('identical fixture')
            stages = []
            for name in gate.PHASE_STAGES[phase]:
                path = directory / (name + '.json')
                log = directory / (name + '.log')
                log.write_text('checked')
                receipt = {'stage': name, 'passed': True, 'exitCode': 0, 'status': 'finished',
                           'inputsBeforeSha256': self.baseline, 'inputsAfterSha256': self.baseline,
                           'artifactSha256': {str(log): verify.digest(log)}}
                verify.write_json(path, receipt)
                stages.append({'stage': name, 'passed': True, 'receipt': str(path), 'sha256': verify.digest(path)})
            verify.write_json(directory / 'phase-final.json',
                              {'phase': phase, 'phasePassed': True, 'passed': False, 'exitCode': 0,
                               'status': 'finished', 'workflowRun': 'run', 'inputsSha256': verify.digest(directory / 'inputs.json'),
                               'safeSelectedDeclarations': 1, 'stages': stages})

    def run_gate(self):
        return gate.combine(self.proof, self.replay, self.root, 'commit', 'run')

    def mutate_final(self, **values):
        path = self.replay / 'phase-final.json'
        row = verify.read_json(path); row.update(values); verify.write_json(path, row)

    def test_complete_phases(self):
        self.assertTrue(self.run_gate()['passed'])

    def test_missing_replay(self):
        (self.replay / 'replay.json').unlink()
        with self.assertRaises((FileNotFoundError, RuntimeError)):
            self.run_gate()

    def test_invalid_final(self):
        for values in ({'phasePassed': False}, {'passed': True}, {'exitCode': 1},
                       {'workflowRun': 'foreign'}, {'phase': 'proof'}, {'status': 'started'}):
            with self.subTest(values=values):
                original = (self.replay / 'phase-final.json').read_bytes()
                self.mutate_final(**values)
                with self.assertRaises(RuntimeError): self.run_gate()
                (self.replay / 'phase-final.json').write_bytes(original)

    def test_missing_or_duplicate_stages(self):
        stages = verify.read_json(self.replay / 'phase-final.json')['stages']
        for replacement in (stages[:-1], stages + [stages[-1]], stages[::-1]):
            self.mutate_final(stages=replacement)
            with self.assertRaises(RuntimeError): self.run_gate()

    def test_changed_source(self):
        (self.root / 'Demo.lean').write_text('changed')
        with self.assertRaises(RuntimeError): self.run_gate()

    def test_changed_inventory(self):
        (self.replay / 'declarations.jsonl').write_text('different')
        with self.assertRaises(RuntimeError): self.run_gate()

    def test_foreign_commit(self):
        with self.assertRaises(RuntimeError):
            gate.combine(self.proof, self.replay, self.root, 'foreign', 'run')

    def test_receipt_tampered(self):
        (self.replay / 'replay.json').write_text('{}')
        with self.assertRaises(RuntimeError): self.run_gate()

    def test_artifact_tampered(self):
        (self.replay / 'replay.log').write_text('changed')
        with self.assertRaises(RuntimeError): self.run_gate()

    def test_foreign_artifact_path(self):
        path = self.replay / 'replay.json'
        row = verify.read_json(path)
        row['artifactSha256'] = {str(self.replay / '..' / 'Demo.lean'): verify.digest(self.root / 'Demo.lean')}
        verify.write_json(path, row)
        final = verify.read_json(self.replay / 'phase-final.json')
        final['stages'][-1]['sha256'] = verify.digest(path)
        verify.write_json(self.replay / 'phase-final.json', final)
        with self.assertRaises(RuntimeError): self.run_gate()

    def test_changed_input_guard(self):
        path = self.replay / 'replay.json'
        row = verify.read_json(path); row['inputsAfterSha256'] = 'wrong'
        verify.write_json(path, row)
        final = verify.read_json(self.replay / 'phase-final.json')
        final['stages'][-1]['sha256'] = verify.digest(path)
        verify.write_json(self.replay / 'phase-final.json', final)
        with self.assertRaises(RuntimeError): self.run_gate()


class ProofOnlyTests(unittest.TestCase):
    setUp = GateTests.setUp

    def run_gate(self):
        return gate.finalize_proof(self.proof, self.root, 'commit', 'run')

    def test_complete_proof_without_replay(self):
        import shutil
        shutil.rmtree(self.replay)
        final = self.run_gate()
        self.assertTrue(final['passed'])
        self.assertEqual(final['officialKernelReplay'], 'not-run')
        self.assertEqual(final['phase'], 'proof-only')
        self.assertEqual([s['stage'] for s in final['stages']], gate.PHASE_STAGES['proof'])

    def test_missing_nanoda(self):
        (self.proof / 'nanoda.json').unlink()
        with self.assertRaises((FileNotFoundError, RuntimeError)): self.run_gate()

    def test_invalid_proof_identity_and_stage_set(self):
        path = self.proof / 'phase-final.json'
        original = path.read_bytes()
        for change in ({'phasePassed': False}, {'passed': True}, {'exitCode': 1},
                       {'workflowRun': 'foreign'}, {'phase': 'replay'}, {'status': 'started'},
                       {'stages': []}):
            row = json.loads(original); row.update(change); verify.write_json(path, row)
            with self.subTest(change=change), self.assertRaises(RuntimeError): self.run_gate()
            path.write_bytes(original)

    def test_source_and_artifact_tampering(self):
        for path in (self.root / 'Demo.lean', self.proof / 'nanoda.log',
                     self.proof / 'inventory.json', self.proof / 'inputs.json'):
            original = path.read_bytes(); path.write_text('{}')
            with self.subTest(path=path), self.assertRaises(RuntimeError): self.run_gate()
            path.write_bytes(original)

    def test_foreign_commit(self):
        with self.assertRaises(RuntimeError):
            gate.finalize_proof(self.proof, self.root, 'foreign', 'run')

    def test_missing_identity(self):
        with self.assertRaises(RuntimeError):
            gate.finalize_proof(self.proof, self.root, 'commit', '')

    def test_no_overwrite(self):
        self.run_gate()
        with self.assertRaises(RuntimeError): self.run_gate()


class PhaseTests(unittest.TestCase):
    def test_mandatory_sequences_and_partial_not_success(self):
        for phase in ("all", "proof", "replay"):
            with self.subTest(phase=phase), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                args = SimpleNamespace(phase=phase, package_root=root, manifest=root / "manifest",
                                       output=root / "output", exporter_checkout=root,
                                       nanoda_checkout=root, nanoda_binary=root / "nanoda")
                pipeline = verify.Pipeline(args)
                def inputs():
                    pipeline.manifest = {"roots": ["Nyll"]}
                    pipeline.lean = root / "lean"
                    pipeline.leanc = root / "leanc"
                    pipeline.export_core_dir = root
                    pipeline.selector_path = pipeline.out / "safe-union.txt"
                    pipeline.selectors = ["one"]
                    verify.write_json(pipeline.out / "inputs.json", {})
                commands = {}
                def stage(name, command=None, **kwargs):
                    commands[name] = command
                    pipeline.stages.append({"stage": name, "passed": True})
                with patch.object(pipeline, "inputs", inputs), patch.object(pipeline, "stage", stage), \
                     patch.object(pipeline, "guard"), patch.object(pipeline, "check_physical_snapshot"), \
                     patch.object(pipeline, "capture", return_value="lean-path"):
                    self.assertEqual(pipeline.execute(), 0)
                expected = (gate.PHASE_STAGES["proof"] + ["replay-compile", "replay-link", "replay"]) if phase == "all" else gate.PHASE_STAGES[phase]
                self.assertEqual(list(commands), expected)
                final = verify.read_json(pipeline.out / ("final.json" if phase == "all" else "phase-final.json"))
                self.assertEqual(final["passed"], phase == "all")
                self.assertTrue(final["phasePassed"])
                if phase != "all":
                    self.assertFalse((pipeline.out / "final.json").exists())
                if "replay" in commands:
                    self.assertEqual(commands["replay"][-1], "Nyll")
                    self.assertNotIn("--run", commands["replay"])
                    self.assertEqual(commands["replay"][2], str(pipeline.out / "ReplayKernel"))
                    self.assertEqual(commands["replay-compile"][-1], str(verify.HERE / "ReplayKernel.lean"))
                    self.assertEqual(commands["replay-link"][0], str(pipeline.leanc))

if __name__ == '__main__':
    unittest.main()
