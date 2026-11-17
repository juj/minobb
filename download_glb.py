"""Download random GLB files from Objaverse-XL into ./test/glb.

Uses the Sketchfab source, whose objects are all native GLB files. Objects
that are already in ./test/glb are not picked again, so every run adds new
files.

Usage: python download_glb.py [count] [seed]
"""

import os
import sys

import objaverse.xl as oxl
from objaverse.xl.sketchfab import SketchfabDownloader

ANNOTATIONS_DIR = "./.objaverse"
DOWNLOAD_DIR = "./test/glb"
N_OBJECTS = int(sys.argv[1]) if len(sys.argv) > 1 else 10
SEED = int(sys.argv[2]) if len(sys.argv) > 2 else 44


def handle_found_object(local_path, file_identifier, sha256, metadata):
    print(f"Found: {local_path}")


def handle_missing_object(file_identifier, sha256, metadata):
    print(f"Missing: {file_identifier}")


def main():
    # Load only the sketchfab annotations (796k rows, all GLB),
    # instead of all sources (~9.7M rows).
    annotations = SketchfabDownloader.get_annotations(
        download_dir=ANNOTATIONS_DIR
    )

    # Leave out the objects that have been downloaded before: the files are
    # named <uid>.glb, and the uid is the last part of the file identifier.
    have = {
        os.path.splitext(name)[0]
        for _dirpath, _dirnames, names in os.walk(DOWNLOAD_DIR)
        for name in names
        if name.endswith(".glb")
    }
    uids = annotations["fileIdentifier"].str.rsplit("/", n=1).str[-1]
    samples = annotations[~uids.isin(have)].sample(n=N_OBJECTS, random_state=SEED)

    downloaded = SketchfabDownloader.download_objects(
        samples,
        download_dir=DOWNLOAD_DIR,
        processes=4,
        handle_found_object=handle_found_object,
        handle_missing_object=handle_missing_object,
    )

    print(f"\nDownloaded {len(downloaded)}/{N_OBJECTS} objects into {DOWNLOAD_DIR}:")
    for file_identifier, path in downloaded.items():
        print(f"  {path}")


if __name__ == "__main__":
    main()
