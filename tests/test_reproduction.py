"""Regression tests for the release workflow; no Magma or network access needed."""
import contextlib
import importlib.util
import io
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import unittest
from unittest.mock import patch
from urllib.parse import parse_qs, urlparse

ROOT = Path(__file__).resolve().parents[1]


class RunnerTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        shutil.copy2(ROOT / 'verify_all.sh', self.root)
        self.bin = self.root / 'bin'
        self.bin.mkdir()
        self.env = dict(os.environ, PATH=str(self.bin) + os.pathsep + os.environ['PATH'])

    def jobs(self, *rows):
        (self.root / 'jobs.txt').write_text('\n'.join('\t'.join(row) for row in rows) + '\n')

    def run_jobs(self, *args):
        return subprocess.run(['bash', './verify_all.sh', *args], cwd=self.root, env=self.env,
                              capture_output=True, text=True, timeout=15)

    def fake_magma(self):
        for name in ('mdmagma/v2/mdmagma.spec', 'mdmagma/Magma/magma.spec',
                     'gl2/magma.spec', 'fast_hecke.m'):
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.touch()
        fake = self.bin / 'magma'
        fake.write_text('''#!/usr/bin/env python3
import json, os, pathlib, sys
with open('magma_calls.jsonl', 'a') as f:
    f.write(json.dumps(sys.argv[1:]) + '\\n')
if pathlib.Path(sys.argv[-1]).name == 'init.m':
    print(os.environ.get('INIT_OUTPUT', 'PACKAGE_READY'))
    sys.exit(int(os.environ.get('INIT_EXIT', '0')))
print('DONE')
''')
        fake.chmod(0o755)

    def test_serial_and_parallel_success(self):
        self.jobs(('logs/a.log', "printf 'RESULT survivors=0\\nDONE\\n\\n'", 'DONE',
                   '^RESULT survivors=0$'), ('logs/b.log', "printf 'DONE details\\n'", 'DONE'))
        for args in ((), ('-j', '2')):
            with self.subTest(args=args):
                result = self.run_jobs(*args)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertIn('all 2 jobs completed', result.stdout)

    def test_failed_commands_incomplete_logs_and_wrong_results_fail(self):
        failures = [
            ("bash -c 'echo DONE; exit 7'", 'DONE'),
            ("false | printf 'DONE\\n'", 'DONE'),
            ("exit 0", 'DONE'),
            ("printf 'Magma: Internal error\\n'", 'DONE'),
            ("printf 'DONE_WRONG\\n'", 'DONE'),
            ("printf 'RESULT survivors=3\\nDONE\\n'", 'DONE', '^RESULT survivors=0$'),
        ]
        for failure in failures:
            for args in ((), ('-j', '2')):
                with self.subTest(failure=failure, args=args):
                    self.jobs(('logs/failed.log', *failure),
                              ('logs/good.log', "printf 'DONE\\n'", 'DONE'))
                    result = self.run_jobs(*args)
                    self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
                    self.assertIn('1 of 2 jobs failed', result.stdout)

    def test_job_failure_count(self):
        self.jobs(('logs/a.log', 'false', 'DONE'), ('logs/b.log', 'false', 'DONE'))
        self.assertEqual(self.run_jobs('-j', '2').returncode, 2)

    def test_invalid_invocations_do_not_overwrite_logs(self):
        self.jobs(('logs/a.log', "printf 'DONE\\n'", 'DONE'))
        (self.root / 'logs').mkdir()
        (self.root / 'logs/a.log').write_text('reference\n')
        for args in (('-j', '0'), ('-j', '-2'), ('-j', 'bad'), ('-j',),
                     ('missing',), ('-j', '2', 'missing'), ('a', 'b')):
            with self.subTest(args=args):
                self.assertNotEqual(self.run_jobs(*args).returncode, 0)
                self.assertEqual((self.root / 'logs/a.log').read_text(), 'reference\n')

    def test_missing_empty_and_malformed_manifests_fail(self):
        self.assertNotEqual(self.run_jobs().returncode, 0)
        for content in ('# no jobs\n', 'logs/a.log\ttrue\n',
                        'logs/a.log\ttrue\tDONE\t[\n',
                        'logs/a.log\ttrue\tDONE\nlogs/a.log\ttrue\tDONE\n'):
            with self.subTest(content=content):
                (self.root / 'jobs.txt').write_text(content)
                self.assertNotEqual(self.run_jobs().returncode, 0)

    def test_scheduler_cannot_silently_skip_jobs(self):
        self.jobs(('logs/a.log', "printf 'DONE\\n'", 'DONE'))
        fake = self.bin / 'xargs'
        for status in (0, 7):
            with self.subTest(status=status):
                fake.write_text('#!/bin/sh\nexit %d\n' % status)
                fake.chmod(0o755)
                self.assertNotEqual(self.run_jobs('-j', '2').returncode, 0)

    def test_package_initialisation_checks_status_and_exact_marker(self):
        self.fake_magma()
        self.jobs(('logs/a.log', 'magma -n -b proof.m', 'DONE'))
        for output, status in [('PACKAGE_READY', '7'),
                               ('> print "PACKAGE_READY";\nMagma: Internal error', '0'),
                               ('PACKAGE_READY_BROKEN', '0')]:
            with self.subTest(output=output, status=status):
                self.env.update(INIT_OUTPUT=output, INIT_EXIT=status)
                self.assertNotEqual(self.run_jobs('-j', '2').returncode, 0)
                self.assertFalse((self.root / 'logs/a.log').exists())

    def test_packages_initialised_sequentially_before_jobs(self):
        self.fake_magma()
        self.jobs(('logs/a.log', 'magma -n -b proof.m', 'DONE'))
        result = self.run_jobs('-j', '2')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        calls = [json.loads(line) for line in (self.root / 'magma_calls.jsonl').read_text().splitlines()]
        self.assertEqual(len(calls), 3)
        self.assertTrue(all(call[:2] == ['-n', '-b'] for call in calls))
        self.assertTrue(all(Path(call[-1]).name == 'init.m' for call in calls[:2]))
        self.assertEqual(calls[-1][-1], 'proof.m')


class ArchiveTests(unittest.TestCase):
    def test_manifest_covers_logs_and_matches_reference_results(self):
        paths = []
        for line in (ROOT / 'jobs.txt').read_text().splitlines():
            if not line.strip() or line.lstrip().startswith('#'):
                continue
            fields = line.split('\t')
            self.assertIn(len(fields), (3, 4))
            path, command, marker = fields[:3]
            paths.append(path)
            log = (ROOT / path).read_text()
            last = [line for line in log.splitlines() if line.strip()][-1]
            self.assertTrue(last == marker or last.startswith(marker + ' '), path)
            if len(fields) == 4:
                self.assertEqual(subprocess.run(['grep', '-Eq', '--', fields[3]], input=log,
                                               text=True).returncode, 0, path)
            if path == 'logs/torsion_over_Fq.log':
                levels = list(dict.fromkeys(re.findall(r'^TORSION n=(\d+)', log, re.M)))
                self.assertIn('Ns:=' + ','.join(levels), command.split())
        self.assertEqual(len(paths), len(set(paths)))
        self.assertEqual(set(paths), {str(path.relative_to(ROOT))
                                     for path in (ROOT / 'logs').rglob('*.log')})


class RankTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        spec = importlib.util.spec_from_file_location('lmfdb_ranks', ROOT / 'lmfdb_ranks.py')
        cls.ranks = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(cls.ranks)

    def test_pagination_fetches_records_after_first_hundred(self):
        records = [{'label': str(i)} for i in range(125)]
        offsets = []

        def page(url):
            offset = int(parse_qs(urlparse(url).query)['_offset'][0])
            offsets.append(offset)
            return {'data': records[offset:offset + 100]}

        with patch.object(self.ranks, 'get', side_effect=page), patch.object(self.ranks.time, 'sleep'):
            self.assertEqual(self.ranks.fetch_level(1), records)
        self.assertEqual(offsets, [0, 100])

    def test_failed_refetch_preserves_archived_files(self):
        with tempfile.TemporaryDirectory() as temp:
            paths = {name: str(Path(temp) / name) for name in ('CACHE', 'RANKS', 'SUMMARY')}
            for path in paths.values():
                Path(path).write_text('reference\n')
            cache = json.loads((ROOT / 'data/lmfdb_newforms_cache.json').read_text())
            cache['26'].pop()
            with patch.multiple(self.ranks, **paths), patch.object(self.ranks, 'fetch', return_value=cache):
                with contextlib.redirect_stdout(io.StringIO()):
                    self.assertEqual(self.ranks.main(['--fetch']), 1)
            for path in paths.values():
                self.assertEqual(Path(path).read_text(), 'reference\n')


if __name__ == '__main__':
    unittest.main()
