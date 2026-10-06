#!/usr/bin/env python3
"""Check the tracked snapshot's structural Palomar requirements before building.

The pinned full Palomar workflow remains the authoritative mechanical check.
This fast check needs only Python's standard library and Git.
"""

import json
import re
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
COMPILED_SUFFIXES = {
    ".olean", ".ilean", ".a", ".bc", ".dll", ".dylib", ".o", ".obj", ".so", ".trace"
}
LICENSE_NAMES = {
    base + suffix
    for base in ("license", "licence", "copying", "unlicense", "ofl")
    for suffix in ("", ".md", ".markdown", ".txt")
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def starts_with_module(source):
    """Skip whitespace and ordinary, possibly nested, Lean comments."""
    pos = 0
    while pos < len(source):
        if source[pos] in " \r\n":
            pos += 1
        elif source.startswith("--", pos):
            end = source.find("\n", pos)
            pos = len(source) if end < 0 else end + 1
        elif source.startswith(("/-!", "/--"), pos):
            return False
        elif source.startswith("/-", pos):
            pos += 2
            depth = 1
            while depth and pos < len(source):
                if source.startswith("/-", pos):
                    depth += 1
                    pos += 2
                elif source.startswith("-/", pos):
                    depth -= 1
                    pos += 2
                else:
                    pos += 1
            require(depth == 0, "Unterminated leading Lean comment")
        else:
            return re.match(r"module(?=\s|--|/-|$)", source[pos:]) is not None
    return False


def check():
    listing = subprocess.check_output(["git", "ls-files", "-z", "--stage"], cwd=ROOT)
    paths = []
    for entry in listing.split(b"\0"):
        if not entry:
            continue
        record, filename = entry.split(b"\t", 1)
        require(not record.startswith(b"160000 "), "Git submodules are not permitted")
        paths.append(filename.decode("utf-8"))

    lean_count = 0
    total_bytes = 0
    for name in paths:
        path = ROOT / name
        if ".git" in path.parts or ".lake" in path.parts:
            continue
        require(path.suffix not in COMPILED_SUFFIXES, f"Compiled artifact committed: {name}")
        if path.is_symlink():
            require(path.suffix != ".lean", f"Lean symlink is not permitted: {name}")
            continue
        data = path.read_bytes()
        total_bytes += len(data)
        require(not data.startswith(b"version https://git-lfs.github.com/spec/v1\n"),
                f"Git LFS pointer is not permitted: {name}")
        if path.suffix != ".lean":
            continue
        lean_count += 1
        line_count = data.count(b"\n") + int(bool(data) and not data.endswith(b"\n"))
        require(line_count <= 10000, f"Lean file exceeds 10,000 lines: {name}")
        if path.name != "lakefile.lean":
            require(starts_with_module(data.decode("utf-8")), f"Missing module header: {name}")

    require(total_bytes <= 500 * 1024 * 1024, "Tracked repository exceeds 500 MiB")
    configs = [ROOT / name for name in ("lakefile.toml", "lakefile.lean")]
    require(sum(path.is_file() for path in configs) == 1, "Provide exactly one Lakefile")
    for name in ("lean-toolchain", "lake-manifest.json", "formalization.yaml", "comparator.json"):
        path = ROOT / name
        require(path.is_file() and not path.is_symlink(), f"Missing regular file: {name}")
    toolchain = (ROOT / "lean-toolchain").read_text().strip()
    require(re.fullmatch(r"leanprover/lean4:v\d+\.\d+\.\d+(?:-rc\d+)?", toolchain),
            "Pin a Lean release or release candidate")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    for package in manifest["packages"]:
        require(package["type"] == "git", "This project expects only pinned Git dependencies")
        require(re.fullmatch(r"[0-9a-f]{40}", package["rev"]),
                f"Dependency is not pinned: {package['name']}")
        require(re.fullmatch(r"https://github\.com/[\w.-]+/[\w.-]+(?:\.git)?", package["url"]),
                f"Dependency URL is not public GitHub HTTPS: {package['name']}")

    config = json.loads((ROOT / "comparator.json").read_text())
    required = {"challenge_module", "solution_module", "theorem_names", "permitted_axioms"}
    require(required <= config.keys(), "Comparator configuration lacks a required field")
    require(config.keys() <= required | {"definition_names", "enable_nanoda"},
            "Comparator configuration has unsupported fields")
    require(config["challenge_module"] != config["solution_module"],
            "Challenge and Solution must be distinct")
    require(isinstance(config["theorem_names"], list) and bool(config["theorem_names"]),
            "Select at least one theorem")
    for key in ("theorem_names", "definition_names"):
        require(all(isinstance(name, str) and name.strip() for name in config.get(key, [])),
                f"Invalid Comparator {key}")
    require(set(config["permitted_axioms"]) <= AXIOMS, "Additional axioms are not permitted")
    for key in ("challenge_module", "solution_module"):
        module = config[key]
        require(isinstance(module, str) and re.fullmatch(r"[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*", module),
                f"Invalid module name: {module}")
        path = ROOT.joinpath(*module.split(".")).with_suffix(".lean")
        require(path.is_file() and not path.is_symlink(), f"Missing module source: {module}")
        if key == "challenge_module":
            data = path.read_bytes()
            lines = data.count(b"\n") + int(bool(data) and not data.endswith(b"\n"))
            require(len(data) <= 100 * 1024 and lines <= 1000, "Challenge exceeds its size cap")

    licenses = [name for name in paths if "/" not in name and name.lower() in LICENSE_NAMES]
    require(len(licenses) == 1, "Provide exactly one root license file")
    require((ROOT / licenses[0]).is_file() and not (ROOT / licenses[0]).is_symlink(),
            "License must be a regular file")
    print(f"Structural checks passed: {lean_count} tracked Lean files; "
          f"{total_bytes / 1024 / 1024:.2f} MiB of tracked source.")
    print("Run the pinned full Palomar workflow for proof, metadata, and resource verification.")


if __name__ == "__main__":
    try:
        check()
    except (ValueError, OSError, KeyError, TypeError, subprocess.CalledProcessError) as error:
        print(f"Submission check failed: {error}", file=sys.stderr)
        sys.exit(1)
