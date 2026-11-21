#!/usr/bin/env python3
import argparse
import base64
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
from tempfile import TemporaryDirectory
from urllib.error import URLError
from urllib.request import Request, urlopen

HERE = Path(__file__).resolve().parent
MEOW_REPO = "meowmath-ai/MeowLean"
MEOW = "954254a1a399147fcf5128ba125cfd666afcf2e7"
MATHLIB = "fc4f59e577feb1a4956671bc04ac18aaaf8cd842"
TERMINAL_SHA256 = "a292da92bae3a043c5d5e0a0157e44781db7386334b117b1134eec4fc3dbd09c"
EXTERNAL_LOCK_SHA256 = "e74138a2ed7d67c64e8d78e44953cb8ad01475e6aa6263fa5fc790ffac716d5f"
PLBY_REPO = "plby/lean-proofs"
PLBY = "8822f7ddef30fadbd92e1c6ab4ed897af356af5e"
VENDORS = "supplements/JSP-000933/"
MODULE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")
IMPORT = re.compile(r"(?:(?:public|private|meta)\s+)*import\s+([A-Za-z0-9_.'\t ]+)")
CORE = ("Mathlib", "Lean", "Init", "Std")
CLEAN = frozenset(("propext", "Classical.choice", "Quot.sound"))
INCOMPLETE = re.compile(r"\bsorryAx\b|uses\s+['‘\u2019]sorry['’\u2019]")

TARGETS = {
    "syntax": ("AuditJSP000930Syntax",),
    "literal-eval": ("AuditJSP000930LiteralEval",),
    "positive": ("AuditJSP000930Positive",),
    "negative-construction": (
        "JSP000930ActualWetzelAllStagesCCC",
        "JSP000930NegativeActualNamedPaletteSchedule",
    ),
    "all": ("AuditJSP000930",),
}
AUDIT_SHA256 = {
    "AuditJSP000930Syntax": "0bb6391bb96a3ff4c4c817afc756291e39e21e826ffe6557ce7f0c35030e5d7d",
    "AuditJSP000930LiteralEval": "5c5f6afc1aff2a0575fc3d2b9d0def13030f61e900ce8430db72903e09a5dce3",
    "AuditJSP000930": "cd5739e4efce1d677d3805e987f867659779638636d6678d6c3568085ef27315",
    "AuditJSP000930Positive": "51c333fc1d458991a6af4bffad679337fc4ae875e48718c7af1edb6c4feafb19",
}
REQUIRED_AXIOM_REPORTS = {
    "AuditJSP000930LiteralEval": (
        "JSP000930.AnalyticSyntax.forces_evalAt_iff_taylorLimit",
        "JSP000930.AnalyticSyntax.literalTaylorEvalCorrespondence",
    ),
    "AuditJSP000930Positive": (
        "JSP000930.Positive.Cohen.wetzelCohen_forces_haymanAtAlephTwo",
        "JSP000930.Consistency.wetzelCohen_consistent_ZFC_plus_alephTwo_plus_haymanBound",
    ),
    "AuditJSP000930": (
        "JSP000930.Positive.Cohen.wetzelCohen_forces_haymanAtAlephTwo",
        "JSP000930.Consistency.wetzelCohen_consistent_ZFC_plus_alephTwo_plus_haymanBound",
        "JSP000930.Consistency.actualWetzel_forces_negative_atAlephTwo",
        "JSP000930.Consistency.hayman_1119_literal_independence_and_same_continuum",
        "JSP000930.Consistency.hayman_1119_relative_independence",
    ),
}


def git(repo, *args):
    return subprocess.check_output(["git", "-C", str(repo), *args])


def source_path(name):
    if not MODULE.fullmatch(name):
        raise ValueError(f"Invalid Lean module name: {name!r}")
    return "/".join(name.split(".")) + ".lean"


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def verified(data, expected, label):
    if sha256(data) != expected:
        raise ValueError(f"Unexpected SHA-256 for {label}")
    return data


def git_blob(repo, path):
    spec = f"{MEOW}:{path}"
    oid = git(repo, "rev-parse", "--verify", spec).decode("ascii").strip()
    data = git(repo, "cat-file", "blob", spec)
    hashed = hashlib.sha1(f"blob {len(data)}\0".encode("ascii") + data).hexdigest()
    if hashed != oid:
        raise ValueError(f"Git object hash mismatch at {path}")
    return data


def lean_imports(data):
    """Read the initial command region, discounting all nested comments."""
    depth = 0
    imports = []
    for raw in data.decode("utf-8-sig").splitlines():
        clean = []
        i = 0
        while i < len(raw):
            pair = raw[i:i+2]
            if pair == "/-":
                depth += 1
                i += 2
            elif pair == "-/" and depth:
                depth -= 1
                i += 2
            elif pair == "--" and not depth:
                break
            elif depth:
                i += 1
            else:
                clean.append(raw[i])
                i += 1
        line = "".join(clean).strip()
        if not line or line in ("module", "prelude"):
            continue
        match = IMPORT.fullmatch(line)
        if match is None:
            break
        names = match[1].split()
        for name in names:
            source_path(name)
        imports.extend(names)
    return imports


def fetch(url):
    req = Request(url, headers={"User-Agent": "JSP-000930-replay"})
    with urlopen(req, timeout=20) as response:
        return response.read()


def plby_source(relative, expected, plby_dir):
    if plby_dir is not None:
        data = (plby_dir / relative).read_bytes()
    else:
        path = "src/latest/" + relative
        try:
            data = fetch(f"https://raw.githubusercontent.com/{PLBY_REPO}/{PLBY}/{path}")
        except (TimeoutError, URLError):
            r = json.loads(fetch(
                f"https://api.github.com/repos/{PLBY_REPO}/contents/{path}?ref={PLBY}"
            ))
            data = base64.b64decode("".join(r["content"].split()), validate=True)
    return verified(data, expected, relative)


def project_checkout(repo):
    git(repo, "merge-base", "--is-ancestor", MEOW, "HEAD")
    git(repo, "diff", "--exit-code", MEOW, "--", "lean-toolchain",
        "lakefile.lean", "lakefile.toml", "lake-manifest.json")
    toolchain = git_blob(repo, "lean-toolchain").decode("ascii").strip()
    if toolchain != "leanprover/lean4:v4.36.0":
        raise ValueError(f"Unexpected pinned toolchain: {toolchain}")
    lock = json.loads(git_blob(repo, "lake-manifest.json"))
    mathlib = [r for r in lock["packages"] if r["name"] == "mathlib"]
    if len(mathlib) != 1 or mathlib[0]["rev"] != MATHLIB:
        raise ValueError("Unexpected pinned Mathlib in Lake manifest.")
    installed = repo / lock["packagesDir"] / "mathlib"
    if git(installed, "rev-parse", "HEAD").decode("ascii").strip() != MATHLIB:
        raise ValueError("Installed Mathlib differs from the pinned commit.")
    v = subprocess.check_output(["lean", "--version"], text=True)
    if "version 4.36.0," not in v:
        raise ValueError(f"Expected Lean 4.36.0, got {v.strip()}")
    print(v.strip(), flush=True)


def lock_rows(repo):
    project = json.loads((HERE / "SOURCE-MANIFEST.json").read_text(encoding="utf-8"))
    for field, value in (
        ("target", "JSP000930RelativeIndependence"),
        ("mathlib", MATHLIB), ("meowlean", MEOW),
    ):
        if project[field] != value:
            raise ValueError(f"Unexpected project manifest {field}: {project[field]}")
    loc = {}
    for row in project["sourceOrder"]:
        path = row["path"]
        name = Path(path).stem
        if path != "src/" + source_path(name) or not name.startswith("JSP000930") or name in loc:
            raise ValueError(f"Unexpected or duplicate local path: {path!r}")
        loc[name] = row
    if (project["terminalSHA256"] != TERMINAL_SHA256 or
            loc[project["target"]]["sha256"] != TERMINAL_SHA256):
        raise ValueError("Unexpected exact 000930 endpoint hash.")
    if len(loc) != 478 or project["sourceCount"] != 478:
        raise ValueError("Expected exactly 478 project modules in this manifest.")
    manifest = json.loads(verified((HERE / "EXTERNAL-SOURCE-LOCK.json").read_bytes(),
                                   EXTERNAL_LOCK_SHA256, "EXTERNAL-SOURCE-LOCK.json"))
    original = json.loads(git_blob(repo, VENDORS + "dependencies.json"))
    if (original["repository"], original["commit"], original["directory"]) != (PLBY_REPO, PLBY, "src/latest"):
        raise ValueError("Unexpected original plby lock provenance.")
    allowed_plby = original["sha256"]
    seen_plby = set()
    ext = {}
    for row in manifest["modules"]:
        name = row["module"]
        path = source_path(name)
        if name in ext or name in loc:
            raise ValueError(f"Duplicate external module: {name}")
        if name.startswith(("JSP000933", "Flypitch4.")):
            if (row["repo"], row["commit"], row["path"]) != (MEOW_REPO, MEOW, VENDORS + "src/" + path):
                raise ValueError(f"Unexpected MeowLean dependency path: {row}")
        elif name.startswith("ErdosProblems."):
            if (row["repo"], row["commit"], row["path"]) != (PLBY_REPO, PLBY, "src/latest/" + path):
                raise ValueError(f"Unexpected plby dependency path: {row}")
            if row["sha256"] != allowed_plby.get(path):
                raise ValueError(f"Unexpected plby dependency hash: {row}")
            seen_plby.add(path)
        else:
            raise ValueError(f"Unexpected external module: {name}")
        ext[name] = row
    if len(ext) != 285 or seen_plby != set(allowed_plby) or len(seen_plby) != 17:
        raise ValueError("External source lock is incomplete or has extras.")
    return loc, ext


def checked_reports(name, diagnostics):
    for theorem in REQUIRED_AXIOM_REPORTS.get(name, ()):
        pattern = (
            r"['‘\u2019]?" + re.escape(theorem) +
            r"['’\u2019]?\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
        )
        report = re.search(pattern, diagnostics)
        if report is None:
            raise ValueError(f"Missing printed axiom report for {theorem}")
        found = {part.strip() for part in (report[1] or "").split(",") if part.strip()}
        if not found <= CLEAN:
            raise ValueError(f"Unexpected axioms for {theorem}: {sorted(found - CLEAN)}")


def check(repo, plby_dir, stages):
    if Path.cwd().resolve() != repo:
        raise RuntimeError("Run lake env from the root of the pinned MeowLean checkout.")
    inherited = os.environ.get("LEAN_PATH")
    if not inherited:
        raise RuntimeError("Run this script from the pinned checkout via 'lake env python'.")
    project_checkout(repo)
    local, external = lock_rows(repo)
    seen = set()
    active = set()
    ordered = []
    with TemporaryDirectory(prefix="jsp-000930-") as temp:
        root = Path(temp).resolve()

        def visit(name):
            if name in active:
                raise ValueError(f"Import cycle at {name}")
            if name in seen:
                return
            if any(name == p or name.startswith(p + ".") for p in CORE):
                return
            path = source_path(name)
            if name in local:
                row = local[name]
                data = verified((HERE / row["path"]).read_bytes(), row["sha256"], name)
                if len(data) != row["bytes"]:
                    raise ValueError(f"Unexpected local source length: {name}")
            elif name in external:
                row = external[name]
                if name.startswith("ErdosProblems."):
                    data = plby_source(path, row["sha256"], plby_dir)
                else:
                    data = git_blob(repo, row["path"])
            elif name in AUDIT_SHA256:
                row = {}
                data = verified((HERE / "src" / path).read_bytes(), AUDIT_SHA256[name], name)
            else:
                raise ValueError(f"Missing declared source: {name}")
            imports = lean_imports(data)
            if "imports" in row and imports != row["imports"]:
                raise ValueError(f"Source imports disagree with lock for {name}: {imports!r}")
            active.add(name)
            for dep in imports:
                visit(dep)
            active.remove(name)
            seen.add(name)
            dest = root / path
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(data)
            ordered.append((name, dest))

        for stage in stages:
            for module in TARGETS[stage]:
                visit(module)
        env = dict(os.environ, LEAN_PATH=os.pathsep.join(
            [str(root), *(str(Path(p).resolve()) for p in inherited.split(os.pathsep) if p)]
        ))
        for i, (name, path) in enumerate(ordered, 1):
            print(f"[{i}/{len(ordered)}] {name}", flush=True)
            opts = []
            if name.startswith("Flypitch4."):
                opts = ["-Dbackward.isDefEq.respectTransparency=false",
                        "-Dbackward.isDefEq.respectTransparency.types=false"]
            command = ["lean", "-j", "1", "-M", "8192", *opts, f"--root={root}",
                       "-o", str(path.with_suffix(".olean")), str(path)]
            result = subprocess.run(command, cwd=root, env=env, text=True, encoding="utf-8",
                                    errors="replace", stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            diagnostics = result.stdout
            if diagnostics:
                print(diagnostics, end="" if diagnostics.endswith("\n") else "\n", flush=True)
            if result.returncode:
                raise subprocess.CalledProcessError(result.returncode, command)
            if INCOMPLETE.search(diagnostics):
                raise ValueError(f"Incomplete proof reported by Lean in {name}")
            checked_reports(name, diagnostics)
        print(f"Passed stages: {', '.join(stages)}", flush=True)


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo", type=Path, default=Path.cwd(),
                    help="MeowLean checkout (default: current directory)")
    ap.add_argument("--plby-src", type=Path,
                    help="optional local plby src/latest directory; hashes are still verified")
    ap.add_argument("--stage", action="append", choices=tuple(TARGETS),
                    help="repeat to replay a union of stages; default: all audits")
    args = ap.parse_args()
    check(args.repo.resolve(), args.plby_src, args.stage or ["syntax", "literal-eval", "positive", "all"])
