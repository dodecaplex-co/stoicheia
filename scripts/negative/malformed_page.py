"""A `page` stamp not of its form is refused: I.1's record given `page = "sha256:"` and
three letters in its [review] table, and `check_fidelity.py` must fail, saying that `page`
is 64 lowercase hex digits, and must not stop with a traceback.
"""

import negative_tests as nt
import review_stamp

BUILDS = False


def plant() -> None:
    path = nt.heath.review_path("I", 1)
    saved = path.read_text()
    try:
        path.write_text(review_stamp.set_stamp(saved, "review", "page", "sha256:xyz"))
        nt.expect_failure("a `page` stamp not of its form", nt.fidelity(),
                          "review/I/01.toml: [review]: `page` is 64 lowercase hex digits",
                          unwanted=("Traceback",))
    finally:
        path.write_text(saved)
