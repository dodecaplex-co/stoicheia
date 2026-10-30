- **The queue's judge refuses an entry whose author, or whose body's last editor, lacks
  write access to the repository, before the queue is turned on (tooling,
  [#617](https://github.com/dodecaplex-co/stoicheia/issues/617)).**
  Until #574's signatures replace it, write access to the pull request vouches for the
  pre-flight block in its body
  ([28 October 2026](2026-10-28-queue-write-access.md)): the judge checks the block for
  consistency with the repository, not as proof that a pre-flight ran. That entry found
  the trust wider than writers. GitHub lets a pull request's author edit its body, even
  after a writer has queued it; and in a public repository of an organization, GitHub
  lets a member of the organization without write access open a pull request between
  the repository's branches. So an author without write access could put a block
  consistent with the repository in place of the real one after the entry was queued,
  and the judge would pass it.

  On 28 October 2026 the owner chose, of the options the coordinator put to them, "Yes,
  before queue goes on (Recommended)" (the coordinator's record: #617): the judge closes
  this before the queue is turned on, as a prerequisite beside the queue's trial
  ([#606](https://github.com/dodecaplex-co/stoicheia/issues/606)).

  So `scripts/check_queue.py` now reads, for each open entry but the automatic revert,
  the repository permission of the pull request's author and of its body's last editor,
  when anyone has edited the body, which the queue's own answer names (GitHub's REST
  "Get repository permissions for a user",
  [GitHub's documentation](https://docs.github.com/en/rest/collaborators/collaborators#get-repository-permissions-for-a-user)).
  It refuses the entry unless each reads `admin` or `write`, the permission GitHub
  reports for the admin, maintain and write roles. A read that fails, an answer for
  another account or one giving a permission GitHub does not give, a login not of
  GitHub's shape, or a last editor whose GraphQL type is neither `User` nor `Bot`, is
  unreadable, and refuses; a bot's authorship or edit is refused, as before. No editor
  between the author and the last is read: the two of them vouch for the whole body.
  The automatic revert is judged as before: its author must be the revert App, and its
  body is read only for lines the judge checks against GitHub's own record.

  The queue's trial (#606) gains the case: a group whose entry's body was last edited by
  an account without write access is refused, after edits through the web page and
  through the API, one of them after a writer's edit, with the queue answer's `editor`
  recorded after each edit, so that the trial shows GitHub naming the last editor as the
  judge reads it (the refusal itself may name the author).

  This entry approves the change to `scripts/check_queue.py`, which reads the
  permissions and refuses as above, and whose docstring says so.

  This entry approves the change to `tests/test_check_queue.py`, whose planted cases
  refuse a body last edited by a member of the organization without write access, a body
  last edited by an outside account, and an author without write access, refuse a
  permission read that fails, and pass the owner's account; its fixtures give their
  accounts write access, and no existing assertion changes.

  This entry approves the change to `docs/WORKFLOW.md`, whose section 10 now says the
  judge holds the trust in the body to writers alone, and that the trial shows it.
