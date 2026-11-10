import json
import os
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from check_submission import check, claim, score_literal
from verify import (MAX_CPUS, VerifyError, freeze_submission,
                    limited_lake_command, linux_command, prepare_project, trusted_axioms,
                    clone_project_cache, REBUILT_NAMESPACES, comparator_spool_directory,
                    validate_spool_directory, linux_filesystem_type)


class PolicyTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        (self.root / "InitECandidate").mkdir()
        (self.root / "Solution.lean").write_text("import InitECandidate.Program\n")
        (self.root / "InitECandidate" / "Program.lean").write_text("import InitE.Challenge\n")
        (self.root / "claim.json").write_text('{"K":"infinity"}')

    def tearDown(self):
        self.temp.cleanup()

    def test_infinity_and_finite(self):
        self.assertTrue(check(self.root)["ok"])
        self.assertEqual(score_literal(claim(self.root / "claim.json")), ".infinity")
        (self.root / "claim.json").write_text('{"K":123}')
        self.assertTrue(check(self.root)["ok"])
        self.assertEqual(score_literal(claim(self.root / "claim.json")), ".finite 123")

    def test_noncanonical_claims_rejected(self):
        for value in ['{"K":true}', '{"K":-1}', '{"K":1.5}', '{"K":"123"}',
                      '{"K":"Infinity"}', '{"K":1,"K":2}', '{"K":0,"extra":0}']:
            with self.subTest(value=value):
                (self.root / "claim.json").write_text(value)
                self.assertFalse(check(self.root)["ok"])

    def test_large_finite_claim(self):
        (self.root / "claim.json").write_text('{"K":%d}\n' % (10**295 - 1))
        self.assertTrue(check(self.root)["ok"])
        (self.root / "claim.json").write_text('{"K":%d}\n' % 10**295)
        self.assertFalse(check(self.root)["ok"])

    def test_cross_prefix_import_rejected(self):
        (self.root / "InitECandidate" / "Program.lean").write_text("import InitECandidateX.Program\n")
        self.assertFalse(check(self.root)["ok"])

    def test_nested_comments_and_frozen_namespace(self):
        (self.root / "Solution.lean").write_text("/- outer /- nested -/ -/\nimport InitEBaselineCandidate.Program\n")
        self.assertFalse(check(self.root)["ok"])
        (self.root / "Solution.lean").write_text("/- outer /- nested -/ -/\nimport InitE.Challenge\n")
        self.assertTrue(check(self.root)["ok"])

    def test_extra_files_symlinks_and_module_headers_rejected(self):
        (self.root / "InitECandidate" / "Bad.lean").symlink_to("Program.lean")
        (self.root / "notes.zip").write_bytes(b"x")
        self.assertFalse(check(self.root)["ok"])
        (self.root / "InitECandidate" / "Bad.lean").unlink()
        (self.root / "notes.zip").unlink()
        (self.root / "Solution.lean").write_text("prelude\n")
        self.assertFalse(check(self.root)["ok"])


class FreezeTests(unittest.TestCase):
    def test_refuses_links_and_special_files(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            source = root / "source"
            source.mkdir()
            (source / "linked").symlink_to("/etc/passwd")
            with self.assertRaises(VerifyError):
                freeze_submission(source, root / "frozen1")
            (source / "linked").unlink()
            os.mkfifo(source / "fifo")
            with self.assertRaises(VerifyError):
                freeze_submission(source, root / "frozen2")

    def test_limits_copy_and_preserves_bytes(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            source = root / "source"
            source.mkdir()
            (source / "Solution.lean").write_bytes(b"0123456789")
            with patch("verify.MAX_FILE_BYTES", 8):
                with self.assertRaises(VerifyError):
                    freeze_submission(source, root / "small")
            freeze_submission(source, root / "frozen")
            self.assertEqual((root / "frozen" / "Solution.lean").read_bytes(), b"0123456789")

    def test_challenge_is_frozen_independently_of_submissions(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            trusted, source = root / "trusted", root / "source"
            for directory in [trusted / "Guest", trusted / "InitE", trusted / "verifier",
                              trusted / "submission" / "InitECandidate", trusted / "tools", source / "InitECandidate"]:
                directory.mkdir(parents=True, exist_ok=True)
            for name in ["lean-toolchain", "lakefile.toml", "lake-manifest.json", "Guest.lean"]:
                (trusted / name).write_text("trusted")
            for name in ("lean-process-limit.c", "limited-lake.py"):
                (trusted / "tools" / name).write_text("trusted limiter " + name)
            (trusted / "Guest" / "guest.pp.pnk").write_text("fixed original source")
            (trusted / "InitE" / "Challenge.lean").write_text("def challenge := True\n")
            (trusted / "InitE.lean").write_text("import InitE.Challenge\n")
            (trusted / "submission" / "InitECandidate" / "Program.lean").write_text("namespace InitECandidate\ndef code := [1,2]\n")
            (trusted / "verifier" / "TrustedAxioms.lean").write_text("audit")
            (trusted / "verifier" / "trusted-axioms.json").write_text("[]")
            (trusted / "verifier" / "comparator.json").write_text("{}")
            (trusted / "verifier" / "Challenge.lean.in").write_text("score := {{SCORE}}")
            (source / "Solution.lean").write_text("candidate proof")
            (source / "InitECandidate" / "Program.lean").write_text("namespace InitECandidate\ndef code := [9]\n")
            def clone(src, dst):
                cache = dst / "build" / "lib" / "lean" / "InitE"
                cache.mkdir(parents=True)
                (cache / "Stale.olean").write_bytes(b"old")
            with patch("verify.clone_project_cache", clone):
                digest = prepare_project(trusted, source, root / "project", {"K":"infinity"})
            project = root / "project"
            self.assertEqual(len(digest), 64)
            for name in ("lean-process-limit.c", "limited-lake.py"):
                self.assertEqual((project / "tools" / name).read_bytes(),
                                 (trusted / "tools" / name).read_bytes())
            # Neither the checked-in initial submission nor submitted proof is trusted.
            (trusted / "submission" / "InitECandidate" / "Program.lean").write_text("changed baseline")
            (source / "InitECandidate" / "Program.lean").write_text("changed candidate")
            with patch("verify.clone_project_cache", clone):
                unchanged = prepare_project(trusted, source, root / "candidate-change", {"K":"infinity"})
            self.assertEqual(digest, unchanged)
            self.assertEqual((root / "candidate-change" / "submission" / "InitECandidate" / "Program.lean").read_text(), "changed candidate")
            (trusted / "InitE" / "Challenge.lean").write_text("changed challenge")
            with patch("verify.clone_project_cache", clone):
                changed_challenge = prepare_project(trusted, source, root / "challenge-change", {"K":"infinity"})
            self.assertNotEqual(digest, changed_challenge)
            (trusted / "tools" / "limited-lake.py").write_text("changed trusted limiter")
            with patch("verify.clone_project_cache", clone):
                changed = prepare_project(trusted, source, root / "project2", {"K":"infinity"})
            self.assertNotEqual(digest, changed)
            (trusted / "tools" / "lean-process-limit.c").unlink()
            with self.assertRaisesRegex(VerifyError, "trusted Lean limiter source missing"):
                prepare_project(trusted, source, root / "project3", {"K":"infinity"})
            self.assertEqual((project / "verifier" / "trusted-axioms.json").read_text(), "[]")
            self.assertFalse((project / "baseline").exists())
            self.assertNotIn("InitEBaselineCandidate", (project / "lakefile.toml").read_text())
            self.assertEqual((project / "InitE.lean").read_text(), "import InitE.Challenge\n")
            self.assertEqual((project / "InitE" / "Challenge.lean").read_text(), "def challenge := True\n")
            self.assertIn("[9]", (project / "submission" / "InitECandidate" / "Program.lean").read_text())
            self.assertEqual((project / "Guest" / "guest.pp.pnk").read_text(), "fixed original source")
            self.assertFalse((project / ".lake" / "build" / "lib" / "lean" / "InitE").exists())


class CacheCopyTests(unittest.TestCase):
    def test_skips_only_rebuilt_workspace_artifacts_and_copies_independently(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source, target = root / "source", root / "target"
            for launcher in ("lean-limit", "metadata-limit"):
                binary = source / launcher / "launcher"
                binary.parent.mkdir(parents=True)
                binary.write_text("host-generated launcher")
                (binary.parent / "lean").symlink_to(binary)
            kept = [
                "packages/upstream/.lake/build/lib/lean/InitE/Dependency.olean",
                "build/lib/lean/Tools/Helper.olean", "build/lib/lean/InitEExtra/Kept.olean",
                "build/lib/lean/InitEExtra.olean", "build/ir/Tools/Helper.c",
                "build/bin/tool", "config/lean-limit.json",
            ]
            skipped = []
            for folder in ("build/lib/lean", "build/ir"):
                for name in REBUILT_NAMESPACES:
                    skipped.extend([f"{folder}/{name}/Stale.olean", f"{folder}/{name}.olean.private"])
            for relative in kept + skipped:
                path = source / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(relative.encode())
            clone_project_cache(source, target)
            for launcher in ("lean-limit", "metadata-limit"):
                self.assertFalse((target / launcher).exists())
                self.assertTrue((source / launcher / "lean").is_symlink())
            for relative in kept:
                original, copied = source / relative, target / relative
                self.assertEqual(copied.read_bytes(), original.read_bytes())
                self.assertNotEqual(copied.stat().st_ino, original.stat().st_ino)
            for relative in skipped:
                self.assertFalse((target / relative).exists(), relative)
            (target / kept[1]).write_bytes(b"independent update")
            self.assertEqual((source / kept[1]).read_bytes(), kept[1].encode())


class AxiomTests(unittest.TestCase):
    def setUp(self):
        self.pinned = json.loads((Path(__file__).resolve().parents[1] / "trusted-axioms.json").read_text())

    def test_only_standard_axioms_permitted(self):
        names = trusted_axioms("INIT_E_TRUSTED_AXIOMS " + json.dumps(self.pinned))
        self.assertEqual(set(names), {"propext", "Quot.sound", "Classical.choice"})

    def test_manifest_cannot_extend_standard_axioms(self):
        with tempfile.TemporaryDirectory() as temporary:
            manifest = Path(temporary) / "axioms.json"
            extended = self.pinned + ["InitE.native_check._native.native_decide.ax_1_1"]
            manifest.write_text(json.dumps(extended))
            with self.assertRaises(VerifyError):
                trusted_axioms("INIT_E_TRUSTED_AXIOMS " + json.dumps(extended), manifest)

    def test_missing_duplicate_and_unexpected_axioms_rejected(self):
        outputs = ["", "INIT_E_TRUSTED_AXIOMS []\nINIT_E_TRUSTED_AXIOMS []",
                   "INIT_E_TRUSTED_AXIOMS []"]
        for extra in ["sorryAx", "Candidate.assumption",
                      "Candidate.fake._native.native_decide.ax_1_1",
                      "Candidate.fake._native.bv_decide.ax_1_5",
                      "_private.Candidate.0.fake._native.native_decide.ax_1_1",
                      self.pinned[0]]:
            outputs.append("INIT_E_TRUSTED_AXIOMS " + json.dumps(self.pinned + [extra]))
        for output in outputs:
            with self.subTest(output=output), self.assertRaises(VerifyError):
                trusted_axioms(output)


if __name__ == "__main__":
    unittest.main()


class ResourceLimitTests(unittest.TestCase):
    def test_verifier_cpu_affinity_and_extended_limits(self):
        env = {"COMPARATOR_LANDRUN": "/usr/bin/true",
               "COMPARATOR_LEAN4EXPORT": "/usr/bin/true"}
        for available in (set(range(32)), {2, 5, 8}):
            with self.subTest(available=available), patch("verify.os.sched_getaffinity", return_value=available):
                command, _ = linux_command(["lake", "build"], Path("/tmp/project"), env, [])
                cpus = " ".join(map(str, sorted(available)[:MAX_CPUS]))
                self.assertIn(f"CPUAffinity={cpus}", command)
                self.assertIn("RuntimeMaxSec=infinity", command)
                self.assertIn(f"MemoryMax={112 * 1024**3}", command)
                self.assertIn("MemorySwapMax=0", command)
                self.assertIn("TasksMax=16384", command)
                self.assertIn("LAKE_ARTIFACT_CACHE=false", command)
        self.assertEqual(MAX_CPUS, 30)

    def test_audit_and_comparator_use_project_local_limiter(self):
        project = Path("/tmp/frozen-project")
        for inner in (["lake", "build", "TrustedAxioms"],
                      ["lake", "env", "/trusted/comparator", "/tmp/comparator.json"]):
            with self.subTest(inner=inner):
                command = limited_lake_command(project, inner)
                self.assertEqual(command, [
                    sys.executable, str(project / "tools" / "limited-lake.py"),
                    "--work-dir", str(project / ".lake" / "lean-limit"),
                    "--slots", "30", "--", *inner])


class ComparatorSpoolTests(unittest.TestCase):
    def test_ram_backed_spools_rejected_and_cleaned(self):
        with tempfile.TemporaryDirectory() as temporary:
            work = Path(temporary)
            for kind in (0x01021994, 0x858458F6):
                with self.subTest(kind=kind), patch("verify.linux_filesystem_type", return_value=kind):
                    with self.assertRaisesRegex(VerifyError, "disk-backed"):
                        with comparator_spool_directory(work, work / "project"):
                            self.fail("RAM-backed spool reached comparator")
                self.assertEqual(list(work.iterdir()), [])

    def test_private_disk_spool_command_and_exception_cleanup(self):
        with tempfile.TemporaryDirectory() as temporary:
            work = Path(temporary)
            project = work / "project"
            env = {"COMPARATOR_LANDRUN": "/usr/bin/true",
                   "COMPARATOR_LEAN4EXPORT": "/usr/bin/true"}
            with patch("verify.linux_filesystem_type", return_value=0xEF53):
                with self.assertRaisesRegex(RuntimeError, "comparator failure"):
                    with comparator_spool_directory(work, project) as spool:
                        self.assertEqual(spool.stat().st_mode & 0o777, 0o700)
                        self.assertEqual(spool.parent, work)
                        self.assertFalse(spool.is_relative_to(project))
                        command, _ = linux_command(["comparator"], project, env, [], spool_dir=spool)
                        writable = [arg for arg in command if arg.startswith("ReadWritePaths=")]
                        self.assertEqual(writable, [f"ReadWritePaths={project / '.lake'}", f"ReadWritePaths={spool}"])
                        self.assertIn(f"TMPDIR={spool}", command)
                        self.assertNotIn(f"ReadWritePaths={work}", command)
                        for property in ("PrivateTmp=yes", "PrivatePIDs=yes", "PrivateUsers=yes",
                                         "ProtectSystem=strict", "ReadOnlyPaths=/home"):
                            self.assertIn(property, command)
                        (spool / "unfinished-export").write_bytes(b"partial")
                        raise RuntimeError("comparator failure")
                self.assertFalse(spool.exists())

    def test_spool_cannot_be_candidate_writable_or_public(self):
        with tempfile.TemporaryDirectory() as temporary:
            work = Path(temporary)
            project = work / "project"
            nested = project / ".lake" / "spool"
            nested.mkdir(parents=True, mode=0o700)
            with self.assertRaisesRegex(VerifyError, "outside"):
                validate_spool_directory(nested, project)
            public = work / "public"
            public.mkdir(mode=0o755)
            with self.assertRaisesRegex(VerifyError, "0700"):
                validate_spool_directory(public, project)
            link = work / "linked"
            link.symlink_to(public)
            with self.assertRaisesRegex(VerifyError, "ordinary"):
                validate_spool_directory(link, project)

    def test_audit_command_does_not_get_spool_access(self):
        env = {"COMPARATOR_LANDRUN": "/usr/bin/true",
               "COMPARATOR_LEAN4EXPORT": "/usr/bin/true"}
        command, _ = linux_command(["lake", "build", "TrustedAxioms"], Path("/frozen/project"), env, [])
        self.assertFalse(any(arg.startswith("TMPDIR=") for arg in command))
        self.assertEqual([arg for arg in command if arg.startswith("ReadWritePaths=")],
                         ["ReadWritePaths=/frozen/project/.lake"])

    def test_statfs_failure_fails_closed(self):
        with self.assertRaises(OSError):
            linux_filesystem_type(Path("/this-verifier-spool-does-not-exist"))


class ProofBoundaryTests(unittest.TestCase):
    def test_fixed_contract_cannot_import_submission_proofs(self):
        from check_submission import contract_modules, imports
        root = Path(__file__).resolve().parents[2]
        modules = contract_modules(root)
        self.assertNotIn("InitECandidate.Proofs.FullBaseline", modules)
        for module in sorted(modules):
            path = root / (module.replace(".", "/") + ".lean")
            for dependency in imports(path.read_text()):
                self.assertFalse(dependency.startswith("InitECandidate"),
                                 f"{module} imports {dependency}")
        for name in ("TrustedAxioms.lean", "Challenge.lean.in"):
            source = (root / "verifier" / name).read_text()
            self.assertTrue(all(not dep.startswith("InitECandidate")
                                for dep in imports(source)), name)

    def test_approved_layout_is_present(self):
        root = Path(__file__).resolve().parents[2]
        layout = json.loads((root / "tools" / "submission-proof-layout.json").read_text())
        for name in layout["challenge_roots"]:
            self.assertTrue((root / "InitE" / (name + ".lean")).is_file(), name)
        for name in layout["moved_roots"]:
            target = root / layout["destination"] / name
            self.assertTrue(target.is_dir() or target.with_suffix(".lean").is_file(), name)
            self.assertFalse((root / "InitE" / name).exists(), name)
            self.assertFalse((root / "InitE" / (name + ".lean")).exists(), name)
