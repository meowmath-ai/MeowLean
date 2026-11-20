import base64
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
from tempfile import TemporaryDirectory
from urllib.error import URLError
from urllib.request import Request, urlopen


HERE = Path(__file__).resolve().parent
IMPORT = re.compile(r"^\s*(?:(?:public|private|meta)\s+)*import\s+([\w.]+)", re.M)
PREFIXES = ("JSP000933", "AuditJSP000933", "Flypitch4.", "ErdosProblems.")


def fetch(request_url):
    request = Request(request_url, headers={"User-Agent": "MeowLean-replay"})
    with urlopen(request, timeout=15) as response:
        return response.read()


def download_sources(root):
    lock = json.loads((HERE / "dependencies.json").read_text(encoding="utf-8"))
    repository, commit = lock["repository"], lock["commit"]
    for relative_path, expected_hash in lock["sha256"].items():
        upstream_path = f'{lock["directory"]}/{relative_path}'
        raw_url = f"https://raw.githubusercontent.com/{repository}/{commit}/{upstream_path}"
        try:
            source = fetch(raw_url)
        except (TimeoutError, URLError):
            api_url = f"https://api.github.com/repos/{repository}/contents/{upstream_path}?ref={commit}"
            reply = json.loads(fetch(api_url))
            source = base64.b64decode(reply["content"])
        if hashlib.sha256(source).hexdigest() != expected_hash:
            raise ValueError(f"Unexpected source hash for {relative_path}")
        destination = root / relative_path
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(source)


def ordered_sources(root):
    visited = set()
    active = set()
    ordered = []

    def visit(module):
        if module in visited:
            return
        if module in active:
            raise ValueError(f"Import cycle at {module}")
        active.add(module)
        path = root.joinpath(*module.split(".")).with_suffix(".lean")
        for name in IMPORT.findall(path.read_text(encoding="utf-8-sig")):
            if name.startswith(PREFIXES):
                visit(name)
        active.remove(module)
        visited.add(module)
        ordered.append((module, path))

    for target in ("AuditJSP000933Vendors", "AuditJSP000933"):
        visit(target)
    return ordered


def check():
    lean_path = os.environ.get("LEAN_PATH")
    if not lean_path:
        raise RuntimeError("Run this script through lake env.")
    version = subprocess.check_output(["lean", "--version"], text=True)
    if "version 4.36.0," not in version:
        raise RuntimeError(f"Expected Lean 4.36.0. Found {version.strip()}")
    with TemporaryDirectory(prefix="jsp-000933-") as directory:
        root = Path(directory).resolve()
        shutil.copytree(HERE / "src", root, dirs_exist_ok=True)
        download_sources(root)
        local_paths = [str(Path(path).resolve()) for path in lean_path.split(os.pathsep) if path]
        env = dict(os.environ, LEAN_PATH=os.pathsep.join([str(root), *local_paths]))
        ordered = ordered_sources(root)
        for index, (module, path) in enumerate(ordered, start=1):
            print(f"[{index}/{len(ordered)}] {module}", flush=True)
            options = []
            if module.startswith("Flypitch4."):
                options = [
                    "-Dbackward.isDefEq.respectTransparency=false",
                    "-Dbackward.isDefEq.respectTransparency.types=false",
                ]
            result = subprocess.run(
                ["lean", "-j", "1", "-M", "8192", *options, f"--root={root}",
                 "-o", str(path.with_suffix(".olean")), str(path)],
                cwd=root, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                encoding="utf-8", errors="replace",
            )
            diagnostics = result.stdout
            if module.startswith("AuditJSP000933") or result.returncode:
                print(diagnostics, end="")
            if result.returncode:
                raise subprocess.CalledProcessError(result.returncode, result.args)
            if re.search(r"uses .sorry.|\bsorryAx\b", diagnostics):
                raise RuntimeError(f"Incomplete proof in {module}")


if __name__ == "__main__":
    check()
