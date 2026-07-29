#!/usr/bin/env python3
"""Average already-captured cargo bench output files."""

import argparse
from pathlib import Path

from divan_fmt import average_fields, parse_divan_output, render_divan_table


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Average already-captured `cargo bench` output files."
    )
    parser.add_argument(
        "files",
        nargs="+",
        type=Path,
        help="captured cargo bench output files",
    )
    parser.add_argument(
        "-o",
        "--output",
        type=Path,
        help="write the averaged table to this file instead of stdout",
    )
    args = parser.parse_args()

    data_sets = [parse_divan_output(path.read_text()) for path in args.files]
    if not data_sets or not data_sets[0]:
        parser.error("no benchmark rows were found in the input files")

    averaged = render_divan_table(average_fields(data_sets)) + "\n"

    if args.output:
        args.output.write_text(averaged)
    else:
        print(averaged, end="")


if __name__ == "__main__":
    main()
