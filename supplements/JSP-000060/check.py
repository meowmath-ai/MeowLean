import hashlib
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

PIN = '8822f7ddef30fadbd92e1c6ab4ed897af356af5e'
BASE = f'https://raw.githubusercontent.com/plby/lean-proofs/{PIN}/src/latest/'
MODULES = {
    "UnitFractions/ForMathlib/IntegralRPow.lean": "884ed8b4343eb10c4e5fa123069c9ac584d74123aea3173974bf3afdb6c48134",
    "UnitFractions/ForMathlib/Misc.lean": "99e31b4fcb5ff24d26b0c9261ca280f4d96aea91e9f1cde7b8ae59a43361f3dd",
    "UnitFractions/ForMathlib/BasicEstimates.lean": "1475f84517f02f43f91563e7852b147d677d661d57e7cac6b4b3120570613775",
    "ErdosProblems/Erdos277.lean": "141c43ae0e8cc4de9a88dc8731c2565414d17b61ccfaa52792d543a8ba285989",
    "ErdosProblems/Erdos281.lean": "2d6af01e6bbb0d6d18158975fb81c39cae23f6b6436eb3f70ac8bf3705afa1ec",
    "ErdosProblems/Erdos27.lean": "f62e2a0ebf8c227d15a14513d2d2dc624a293cf90d8193079af72b0dd2d415c3"
}


def check(root: Path) -> None:
    project = Path(__file__).resolve().parent
    for module, digest in MODULES.items():
        path = root / module
        path.parent.mkdir(parents=True, exist_ok=True)
        if os.name == 'nt':
            shell = shutil.which('pwsh') or 'powershell.exe'
            env = dict(os.environ, JSP060_SOURCE_URL=BASE + module, JSP060_SOURCE_PATH=str(path))
            subprocess.run(
                [shell, '-NoProfile', '-NonInteractive', '-Command',
                 'Invoke-WebRequest -UseBasicParsing -TimeoutSec 60 -ErrorAction Stop '
                 '$env:JSP060_SOURCE_URL -OutFile $env:JSP060_SOURCE_PATH'],
                env=env,
                check=True,
            )
        else:
            subprocess.run(
                ['curl', '-fLsS', '--retry', '2', '--max-time', '60',
                 '-o', str(path), BASE + module],
                check=True,
            )
        source = path.read_bytes()
        if hashlib.sha256(source).hexdigest() != digest:
            raise ValueError(f'Unexpected source hash for {module}')
        path.write_bytes(source.replace(b'\r\n', b'\n'))

    subprocess.run(
        ['git', 'apply', '--unidiff-zero', str(project / 'mathlib-4.36.patch')],
        cwd=root,
        check=True,
    )
    source = root / 'JSP000060.lean'
    source.write_bytes((project / source.name).read_bytes())
    env = os.environ.copy()
    lean_path = env.get('LEAN_PATH')
    if not lean_path:
        raise RuntimeError('Run this script using lake env')
    env['LEAN_PATH'] = str(root) + os.pathsep + lean_path

    for module in (*MODULES, source.name):
        path = root / module
        print(f'Checking {module}', flush=True)
        subprocess.run(
            ['lean', '-j', '1', '-M', '4096', f'--root={root}',
             '-o', str(path.with_suffix('.olean')), str(path)],
            env=env,
            check=True,
        )


if __name__ == '__main__':
    with tempfile.TemporaryDirectory(prefix='jsp-000060-') as directory:
        check(Path(directory))
