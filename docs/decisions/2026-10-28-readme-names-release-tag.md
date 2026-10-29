- **README names the release tag a Lean project pins (#38).** On 28 October 2026 the owner
  chose, of the options the coordinator put to them on whether README should name a release
  tag, "README names a release tag"; the coordinator relayed that choice to ship RT, and the
  release it concerns is #38. The tag's name, `v1.0`, is the one the coordinator's orders
  give. README's "Use it" now pins `rev = "v1.0"`, in both the `lakefile.toml` and the
  `lakefile.lean` forms, and says that the owner makes the tag when the release of Books I
  to III is published; until then `git ls-remote` shows no such tag, and a project pins a
  commit of main instead. `book-III`, of 17 October 2026, which README pinned before, is
  named as an older tag, kept as history. Nothing here creates, moves or deletes a tag.
