- **CI's Lean install survives an outage of releases.lean-lang.org: a cache, three tries
  and GitHub's copy (CI, [#594](https://github.com/dodecaplex-co/stoicheia/issues/594)).**
  On 27 October 2026, from about 22:10 to 23:10 US Pacific time, GitHub's runners could not
  open a TLS connection to `releases.lean-lang.org`, and three CI jobs failed to download
  Lean 4.35.0 (`[35] SSL connect error`); two of them cost landings, #592 and #593, each
  after a passing pre-flight. The host was answering other networks at the time, and it
  redirects every download to the same file among the release assets of
  `leanprover/lean4` on GitHub. That night too, #593's `negative` job waited 75 minutes on a
  toolchain download that connected and never finished.

  Six jobs install Lean: CI's `check`, `negative`, `formal-model` and `acceptance`, and the
  cadence's `negative-tests` and `formal-model-kernel`. Each piped elan's installer, unpinned,
  from its `master` branch, and then let elan download the toolchain at first use, with no
  cache and no second try. Each now has two steps in place of its one. The first,
  `actions/cache@v5`, as the formal model's Mathlib is cached already, restores
  `~/.elan/toolchains` under a key made of the runner's system and the hash of
  `lean-toolchain` and `model/lean-toolchain`, and saves it after a job that passes. The
  second runs one script, `scripts/install_lean.sh`, the same in every job. It installs
  elan v4.2.4, checked against the SHA-256 of its release, with no default toolchain; then
  the toolchain `lean-toolchain` names, and `model/lean-toolchain`'s too if that ever names
  another. A toolchain the cache restored is used as it is, and nothing is downloaded for
  it. One it did not is installed by elan, in three tries at most, 15 and then 30 seconds
  apart; and if none succeeds, it is downloaded from GitHub's copy of the same file, the
  one `releases.lean-lang.org` redirects to, and unpacked where elan keeps it, with what a
  stopped try left beside it removed: elan takes a lock beside that place, unpacks beside
  it and renames the whole into it, so a stopped try may leave its lock there, and its
  partial unpack too, which the cache would otherwise save with the toolchain. Whatever
  the route, the script ends by asking `lean --version`, in the checkout and in `model/`,
  and fails unless each says the version its file names. It refuses any system but Linux on
  x86_64, which is what `ubuntu-latest` is, and any toolchain that is not a release of
  `leanprover/lean4`, for which it would know no copy to fall back on. elan checks no
  digest of a toolchain it downloads, and neither does the script: GitHub's copy is the
  file elan's own download ends at, fetched from the same place, and the version check
  holds what it is.

  Every download has a time limit, so that a stall fails fast. The toolchain is a file of
  about 594 MB, and on a healthy connection the whole install took 22 seconds. Each of
  elan's tries is stopped after 90 seconds, four times that, so that a stalled host costs at
  most about five minutes before GitHub's copy, not a job's whole time. elan v4.2.4 itself
  gives up on the toolchain's download when it moves under 10 bytes a second for 30
  seconds, but not on a slow trickle, and it sets no limit at all on the two reads before
  it: a check for a newer elan, from GitHub, and the index of releases, from a second
  host, `release.lean-lang.org`. The 90 seconds bound all three. The script's own
  downloads, of elan and of GitHub's copy, give up on a connection not made in
  20 seconds, on a transfer slower than 100 kB a second for 20 seconds, and on any try
  longer than 5 minutes (2 MB a second, for the toolchain), and start no new try after 10
  minutes.

  We owe the pieces to TS, with warm thanks. TS's train of 25 October that pins CI's
  installs (#430) first pinned elan v4.2.4 by that digest, and gave the form in which the
  test of the `negative` job's commands now passes over the install, by its lines; and TS's
  benchmark of the pre-flight (#574, never merged) pinned it too and cached the toolchain,
  and its cache was saved on a real runner on the night of the outage.

  The planted cases, run on a Mac in an x86_64 Ubuntu 24.04 container, with zstd added
  as `ubuntu-latest` has it, each with the script as committed unless said otherwise:
  - with `releases.lean-lang.org` answering plain HTTP on port 443, so that elan's
    downloads fail with the night's error, `[35] SSL connect error`, three times, the
    install took GitHub's copy, and `lean --version` said 4.35.0, in 71 seconds;
  - with the host sent to 127.0.0.1, so that its connections are refused, the same, in 66;
  - the same outage, with the script's fall-back to GitHub's copy taken out: elan's three
    tries failed, `lean --version` failed with them, and so did the install, as it should;
  - the toolchain left in place by the first case, as the cache restores it, with the host
    sent to 127.0.0.1: nothing downloaded for the toolchain, and `lean --version` right, in
    2 seconds;
  - with nothing blocked: elan's first try, in 22 seconds.

  These numbers are from the script before its time limits; run again with them, the five
  cases came out the same, in 73, 71, 50 (failing), 3 and 24 seconds. Then the stalls, each
  with `releases.lean-lang.org` sent to a planted host:
  - a host that accepts the connection and sends nothing: each of elan's tries failed when
    its own connection limit, 30 seconds, ran out, and the install took GitHub's copy and
    ended with the right `lean --version`, in 259 seconds;
  - a host that completes TLS with a certificate the container was made to trust, sends
    the reply's headers and 1 kB, then nothing, even to a resumed request: elan's own limit
    ended each try in about 66 seconds, and the install took GitHub's copy, in 275 seconds;
  - the same host, sending 100 bytes a second after the first kilobyte: the 90-second limit
    stopped each of elan's three tries, and the install took GitHub's copy, in 345 seconds;
  - the script's own download, its line exactly as committed, against a reply that sends its
    headers and then nothing: six tries, each ended after 20 seconds as too slow, and the
    download failed, as it should, in 152 seconds;
  - a stopped try's leftovers, a partial unpack and a lock, planted beside where elan keeps
    the toolchain, with the host sent to 127.0.0.1: the install took GitHub's copy, and the
    toolchain alone was left, in 68 seconds. Each of elan's tries failed, and was not
    stopped, so each took the planted lock and removed it as it ended: the case shows the
    script removing the partial unpack, not the lock.

  On GitHub's runners, a trial on a branch of its own, never landed, ran the script before
  its time limits (run 40652212492, on 28 October 2026): with `releases.lean-lang.org` sent
  to 127.0.0.1, elan's three tries failed and the install took GitHub's copy and passed, in
  69 seconds; the same with the fall-back taken out failed, as it should; and a job that
  saved the toolchains to the cache was followed by one that restored them ("Cache restored
  from key"), in which the script said the toolchain was "restored from the cache; nothing
  downloaded for it".

  The test of the `check` job's setup now holds the cache, its path and key exactly, after
  the checkout and Python and before the install, and the install's one line in place of
  the old two; it compares each action's inputs by value and type, where it compared them
  by identity, which holds for `false` but not for a string; and it plants six changes of
  the cache (none, after the install, another path, a path as a list, another key, and
  `restore-keys`), each of which it refuses. The test of the `negative` job's commands
  passes over the install's line, where it passed over any line naming elan. No check,
  job or step is skipped, loosened or renamed.

  This entry approves the change to `.github/workflows/ci.yml`, whose `check`, `negative`,
  `formal-model` and `acceptance` jobs restore the toolchains from the cache and run
  `scripts/install_lean.sh` in place of the unpinned installer.

  This entry approves the cadence's two installs, in
  `.github/workflows/safe-push-tests.yml`: its `negative-tests` and `formal-model-kernel`
  jobs do as CI's four do.

  This entry approves the new file `scripts/install_lean.sh`, which installs elan v4.2.4 by
  its digest and the toolchains from the cache, elan or GitHub's copy, and checks the
  version each file names, with a time limit on every download.

  This entry approves the cache and the install in the test model of the `check` job's
  setup, `scripts/test_safe_push.py`, with each input compared by value and type and six
  changes of the cache refused, and its test of the `negative` job's commands, which
  passes over the install.
