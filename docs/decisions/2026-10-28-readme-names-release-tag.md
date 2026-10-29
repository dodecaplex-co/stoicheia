- **README names the release tag a Lean project pins (README, #38).** On 28 October 2026
  the owner chose, of the options the coordinator put to them on whether README should name
  a release tag, "README names a release tag"; the coordinator relayed that choice to ship
  RT, and the release it concerns is #38. The tag's name, `v1.0`, is the one the
  coordinator's orders give. README's "Use it" now uses `rev = "v1.0"` in the
  `lakefile.toml` form and `@ "v1.0"` in the `lakefile.lean` form, and says that the tag is
  made when the release of Books I to III is published (the owner makes it then); until
  then `git ls-remote` shows no such tag, and a project pins a commit of main instead.
  `book-III`, of 17 October 2026, which README pinned before, is named as an older tag,
  kept as history. Nothing here creates, moves or deletes a tag.
