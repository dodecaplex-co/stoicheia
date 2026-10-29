- **The pages and the documents name the repository's new home, the dated records and
  the briefs aside (tooling,
  [#626](https://github.com/dodecaplex-co/stoicheia/issues/626)).** The repository moved
  from a personal account to the organization dodecaplex-co on 27 October 2026. GitHub
  redirects the old address, but it is stale, and it put a personal handle in the
  reader's path on every page. So the one constant from which every page's links to a
  commit and a release are written now names `https://github.com/dodecaplex-co/stoicheia`,
  and the pages are regenerated from it; the documents outside `docs/decisions/`,
  `docs/briefs/` and `docs/reports/` name the new address in their links. The decision
  entries, the decisions page and the reports are dated records, kept as written; the
  briefs are left as they are, the current book briefs among them (`book-I.md`,
  `book-II.md`, `0004-book-III.md`, `0012-book-IV.md`), which keep their links until
  their briefs are next revised. Nothing else changes: each link keeps its issue, pull
  request or release, and its words.

  This entry approves the change to [`scripts/render.py`](../../scripts/render.py), whose
  `REPO` is that constant.
  It approves the change to [`scripts/audit/jev.py`](../../scripts/audit/jev.py), whose
  user agent names the repository's address.
  It approves the change to [`Certificate/FIELDS.md`](../../Certificate/FIELDS.md), whose
  four links to issues name the new address.
  It approves the change to [`tests/model/MODEL.md`](../../tests/model/MODEL.md), whose
  three links to issues name the new address.
  It approves the change to [`review/SCHEMA.md`](../../review/SCHEMA.md), whose one link
  to an issue names the new address.
