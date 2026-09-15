"""Download 10 random GLB files from Objaverse-XL into ./test/glb.

Uses the Sketchfab source, whose objects are all native GLB files.
"""

import objaverse.xl as oxl
from objaverse.xl.sketchfab import SketchfabDownloader

ANNOTATIONS_DIR = "./.objaverse"
DOWNLOAD_DIR = "./test/glb"
N_OBJECTS = 10


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

    samples = annotations.sample(n=N_OBJECTS, random_state=43)

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
