- **A check refuses a stale address of the repository in the pages and the documents
  outside the exempt folders (checks,
  [#626](https://github.com/dodecaplex-co/stoicheia/issues/626)).** After the move to the
  organization dodecaplex-co on 27 October 2026, the pages and the documents outside
  `docs/decisions/`, `docs/briefs/` and `docs/reports/` name the new address, and the card
  asks that a check keep it so, with those folders exempt. The decision entries, the
  decisions page and the reports are dated records, kept as written; `docs/briefs/` is
  exempt as a whole, the current book briefs among them (`book-I.md`, `book-II.md`,
  `0004-book-III.md`, `0012-book-IV.md`), which keep their links until their briefs are
  next revised. The check does not judge the exempt folders, so it does not refuse an old
  address added there; it says how many addresses they hold, so that a run shows the
  exemption at work. It refuses any address of a repository named `stoicheia` on GitHub
  whose owner is not `dodecaplex-co`, in each form WORKFLOW section 4 lists (the API's
  `api.github.com/repos/`, `codeload.` and the wiki's `stoicheia.wiki` among them), as a
  bare `<owner>/stoicheia` that no path runs into, no `@` stands just before and no other
  site's address holds after its `?` or `#`, and as the bare `repos/<owner>/stoicheia`
  of `gh api`, rather than the old address alone, so that the check need not name the
  old one; each refusal says what to write for the form found. It reads
  every Markdown file and the root's `CITATION.cff`, `LICENSE` and `NOTICE`, code inside
  Markdown included; code and configuration files are outside its scope. A file in scope,
  or a file named outside the exempt folders, that cannot be read or decoded as UTF-8 is
  refused, and an argument beginning `--` other than `--self-test` stops the run with a
  usage line. Its self-test's cases include addresses it must pass over (another host,
  another repository's name, a local path), the advice for each form, the options and
  files that cannot be read; and a plant puts a stand-in owner's address in a generated
  page, in `CITATION.cff` and, bare, in `NOTICE`, and then a byte that is not UTF-8 in
  `NOTICE`, each refused. WORKFLOW, section 4, "The repository's address", says why the
  exempt folders keep their words.

  This entry approves the new file [`scripts/check_address.py`](../../scripts/check_address.py),
  the check.
  It approves the new file [`checks/27-check-address.toml`](../../checks/27-check-address.toml),
  which runs the check, with its self-test, at order 185 of CI's `check` job, after the
  links.
  It approves the new file [`scripts/negative/stale_address.py`](../../scripts/negative/stale_address.py),
  the check's plant.
  It approves the change to [`tests/test_concurrent_checks.py`](../../tests/test_concurrent_checks.py):
  the check's self-test joins the commands that test's registry expects to run alone,
  since it writes files in the tree while it runs (#608).
