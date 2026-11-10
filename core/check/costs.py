"""Fill in E and B for every network in a model's zoo manifest.

    python -m core.check.costs models/<name>
"""

from __future__ import annotations

import argparse

from ..model_folder import load_model_folder
from ..zoo import read_manifest, write_manifest
from .checker import extraction_and_brute_force_costs
from .cost import VERSION


def fill_costs(folder, log=print) -> dict:
    manifest = read_manifest(folder)
    for entry in manifest["networks"]:
        E, B = extraction_and_brute_force_costs(folder, entry["id"])
        entry["E"], entry["B"], entry["cost_model"] = E, B, VERSION
        log(f"{entry['id']}: E={E:,} B={B:,}")
    write_manifest(folder, manifest)
    return manifest


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("model_folder")
    args = ap.parse_args(argv)
    fill_costs(load_model_folder(args.model_folder))


if __name__ == "__main__":
    main()
