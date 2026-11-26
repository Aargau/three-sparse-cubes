"""Replay a single-declaration Lean export with the independent Nanoda kernel.

From lean/, create the export with:
  lake env leanexport MODULE -- DECLARATION > proof.ndjson
Run this checker with the export path and the fully qualified DECLARATION.
"""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time


ROOT = Path(__file__).resolve().parents[1]
AXIOMS = ["propext", "Classical.choice", "Quot.sound"]


def check_export(path, declaration):
    # A single-declaration export writes the requested theorem after its dependencies.
    # Most lines contain expressions. Only names and the last record are needed here.
    names = {0: ""}
    digest = sha256()
    with path.open("rb") as stream:
        last = None
        for line in stream:
            digest.update(line)
            if not line.strip():
                continue
            last = line
            if b'"in":' in line and (b'"str":' in line or b'"num":' in line):
                obj = json.loads(line)
                if "in" in obj:
                    kind = "str" if "str" in obj else "num"
                    node = obj[kind]
                    parent = names[node["pre"]]
                    part = str(node["i" if kind == "num" else "str"])
                    names[obj["in"]] = parent + "." + part if parent else part
        if last is None:
            raise ValueError("Empty export")
        theorem = json.loads(last).get("thm", {})
        if names.get(theorem.get("name")) != declaration:
            raise ValueError("The last declaration in this export is not the requested theorem")
    return digest.hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("export", type=Path)
    parser.add_argument("declaration")
    parser.add_argument("--nanoda", type=Path, help="Default to the pinned Lean toolchain's binary")
    args = parser.parse_args()
    sys.stdout.reconfigure(encoding="utf8")
    path = args.export.resolve(strict=True)
    export_digest = check_export(path, args.declaration)
    if args.nanoda is None:
        prefix = subprocess.check_output(["lean", "--print-prefix"], cwd=ROOT / "lean", text=True).strip()
        binary = Path(prefix) / "bin" / "nanoda_bin"
        if not binary.is_file():
            binary = binary.with_suffix(".exe")
    else:
        binary = args.nanoda.resolve(strict=True)
    version = subprocess.check_output([binary, "--help"], text=True, encoding="utf8").splitlines()[0]
    print(f"Declaration {args.declaration}\nExport SHA256 {export_digest}", flush=True)
    print(f"Checker {version}\nChecker SHA256 {sha256(binary.read_bytes()).hexdigest()}", flush=True)
    config = {"export_file_path": str(path), "permitted_axioms": AXIOMS,
              "unpermitted_axiom_hard_error": True, "nat_extension": True,
              "string_extension": True, "pp_to_stdout": True, "print_success_message": True}
    with tempfile.TemporaryDirectory(prefix="sparse-cube-nanoda-") as folder:
        file = Path(folder).resolve(strict=True) / "check.json"
        with file.open("x", encoding="utf8") as stream:
            json.dump(config, stream)
        start = time.monotonic()
        check = subprocess.run([binary, file], text=True, capture_output=True, encoding="utf8")
        print(check.stdout, end="")
        print(check.stderr, end="")
        check.check_returncode()
        if not re.search(r"Checked [0-9]+ declarations with no errors", check.stdout):
            raise ValueError("The checker did not report a clean verdict")
        print(f"Replay seconds {time.monotonic()-start:.2f}")


if __name__ == "__main__":
    main()
