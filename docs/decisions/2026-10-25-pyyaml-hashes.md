- **PyYAML pinned by hash as well as by version, for every install of the parser the
  landing tool's tests read the workflows with (tooling,
  [#430](https://github.com/jackChallis/stoicheia/issues/430), from
  [#346](https://github.com/jackChallis/stoicheia/issues/346)).**
  `scripts/requirements-test_safe_push.txt` held `PyYAML==6.0.3` and nothing more. Five
  steps install it: in CI, the `check` job, the `queue-integrity` job on a pull request or
  main, and the `queue-gaps` job on a merge group, from the group's base; on the cadence,
  the `safe-push-shards` and `safe-push-tests` jobs. A pin by version trusts the index to
  serve the same file each time; a pin by hash does not, for the file pip installs, and
  the review of #346 asked for one (card #430). The file now gives the requirement one
  `--hash=sha256:` for each of the 73 files PyPI holds for 6.0.3, the sdist and its 72
  wheels, so that the file pip picks is listed wherever it installs, on CI's Linux runners
  or on a contributor's macOS or Linux, and a machine with no wheel of its own builds from
  the sdist. That build installs PyYAML's build requirements, setuptools and Cython, which
  its `pyproject.toml` does not pin, with no hash check, since pip passes no hashes to the
  install of build requirements. An index can send any machine there, CI's runners
  included, by listing a wheel under a digest this file does not hold: pip passes over
  that wheel for the listed sdist. Ruling the sdist out in CI, with `--only-binary :all:`
  on its five installs, is a change to the workflows and to the tests that pin their
  commands, proposed to the coordinator; this train does not make it. A `--hash` turns on
  pip's hash-checking mode for every install of the file, with no flag, and pip then
  installs no PyYAML file whose SHA-256 digest is not listed. So no workflow step,
  command, permission or test changes, and the train is of class R3, by `scripts/risk.py`.
  The merge group's install reads the file at the group's base, so it checks the digests
  once this change is on main.

  The digests are the `urls[].digests.sha256` of PyPI's page for the release,
  <https://pypi.org/pypi/PyYAML/6.0.3/json>, sorted; PyPI's Simple index, which pip
  reads, gives the same 73. Three files were downloaded and hashed by hand, and each
  matched its listed digest: the wheel CI installs, CPython 3.12's for manylinux x86_64
  (its digest begins `ba1cc08a7ccd`), the wheel a Mac with Apple silicon installs under
  CPython 3.14 (`34d5fcd24b84`), and the sdist (`d76623373421`). The comment at the head
  of the file says where the digests come from, and gives the command that prints the
  requirement again from that page, so that a refresh, for this version or the next, is
  that command's output put in place of the requirement; after it, the wheel CI installs
  and one's own are hashed by hand, as these were.

  In a fresh virtual environment, `python3 -I -m pip install -r` the file installed PyYAML
  6.0.3 from the Mac's wheel. In a scratch copy with that wheel's digest altered in its
  last digit, pip did not refuse: its finder passes over a file whose digest the index
  gives and the requirement does not list, and it built 6.0.3 from the sdist, whose digest
  was still listed. With wheels alone allowed (`--only-binary :all:`), the altered wheel
  was the one candidate, and pip refused it with its hash error, "THESE PACKAGES DO NOT
  MATCH THE HASHES FROM THE REQUIREMENTS FILE". The case the hashes are for, an index
  serving other bytes under a listed file's name, with a digest of their own or none, was
  planted too: a copy of that wheel with one byte added, offered by a folder in place of
  the index (`--no-index --find-links`), which gives no digest, was refused under the file
  as written, and installed under main's file. `pip download` for CI's platform fetched
  the wheel CI installs, and checked its digest. WORKFLOW, section 8, now says that the
  parser is pinned by version and hash.

  This entry approves the change to `scripts/requirements-test_safe_push.txt`, which pins
  PyYAML 6.0.3 by the SHA-256 digest of each of its 73 files on PyPI as well as by its
  version, under a comment saying where the digests come from, what they do not cover and
  how to refresh them.
