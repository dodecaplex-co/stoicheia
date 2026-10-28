- **A check refuses a stale address of the repository in the pages and current documents
  (tooling, [#626](https://github.com/dodecaplex-co/stoicheia/issues/626)).** After the
  move to the organization dodecaplex-co on 27 October 2026, the pages and the current
  documents name the new address, and the card asks that a check keep it so, with the
  dated records exempt. The check refuses any address of a repository named `stoicheia`
  on GitHub whose owner is not `dodecaplex-co`, in the four forms GitHub serves, rather
  than the old address alone, so that no file names the old one; it reads every Markdown
  file and `CITATION.cff` outside `docs/decisions/`, `docs/briefs/` and `docs/reports/`,
  code included, and says how many addresses those records hold, so that a run shows
  the exemption at work. Its self-test reads 26 cases, and a plant puts a stand-in
  owner's address in a generated page and in `CITATION.cff`, each refused. WORKFLOW,
  section 4, "The repository's address", says why the dated records keep their words.

  This entry approves the new file [`scripts/check_address.py`](../../scripts/check_address.py),
  the check.
  It approves the new file [`checks/27-check-address.toml`](../../checks/27-check-address.toml),
  which runs the check, with its self-test, at order 185 of CI's `check` job, after the
  links.
  It approves the new file [`scripts/negative/stale_address.py`](../../scripts/negative/stale_address.py),
  the check's plant.
