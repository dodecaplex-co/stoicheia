- **A pre-flight proof: the yard VM runs step 4, and the Mac pushes on its proof (landing,
  [#678](https://github.com/dodecaplex-co/stoicheia/issues/678)).** On 29 October 2026 the
  owner was asked how work should ship from the yard VM, `stoicheia-yard-1`, a machine of
  48 cores that holds no credentials. Three options were put: (A) the VM runs the heavy
  work, the pre-flight included, and the Mac only signs off, pushes and merges with its
  existing login; (B) short-lived tokens from a GitHub App for each landing, with approval
  by phone for security holds; (C) a long-lived token on the VM. The owner said: "A is
  fine." Asked then whether the pre-flight itself could run on the VM, the owner said:
  "Can we run the preflight on the VM?" Card #678 is the coordinator's record of both.

  Why. The yard already runs the landing tool's whole dry run on the VM as its last step,
  but a landing on the Mac then runs the same pre-flight again, step 4 included: the full
  local checks and the negative tests, the long part of every landing of R3 to R5. A proof
  lets the VM's run count once, and only for exactly what it checked.

  What changes. A dry run given `--emit-proof FILE` writes, when it passes with step 4 run
  in full, a proof: the pre-flight's record (the commit, origin/main's tip that it was
  judged against, the harness's blob, and each step's verdict and time), the blob of
  every check input as origin/main holds it, which takes in the harness's own modules,
  the machine's name, the time it was made, and a SHA-256 digest of all of these. A
  failed run writes none, and removes a file left at that path. `--land` given
  `--preflight-proof FILE` reads the file after the preconditions and the class, before
  any of the commit's code runs on the Mac, and lets it stand in for step 4 only when
  every one of these holds: it can be read, and is of the expected shape; its digest
  matches; it is of the commit being pushed; origin/main has not moved since it was made;
  it was made by the harness running now, with the check inputs origin/main holds now;
  it is no more than 12 hours old, and dated no more than five minutes ahead of the Mac's
  clock; it holds no note for the security review; and `checks_record` accepts its record
  as it accepts one kept in memory, every step passed and step 4 run in full. When any of
  them fails, a step line says which, and the full pre-flight runs on the Mac, as it does
  today. Nothing is ever accepted silently, and nothing is checked less than once.

  What still runs on the Mac. The preconditions, the secret scan and the invariant guards,
  the train check among them, run there every time, before the push; the merge that
  `--land` goes on to runs the scan and the guards again, and takes its step 4 from the
  record the push made, as it does without a proof. Its step 3 says when that record's
  step 4 came from a proof, and from which machine. The machine is named only on the
  terminal: the line the record keeps, which goes into the pull request's body, gives the
  time the proof was made and not the machine, since a machine's name can be a person's.

  The trust, stated plainly. The proof is a file, and the run that made it ran the head's
  own code. The entry for `--land`, of 26 October, gives that as the reason a separate
  `--merge` never lets a record from a file stand in for a head that changes the checks
  or a protected path. The proof is let stand in for such heads all the same, since nearly
  every landing that runs step 4 in full changes a check input or a protected path (each of
  the 31 heavy merges #557 counted did), and a proof refused for them would spare the Mac
  almost nothing. Its digest catches an edit by hand or damage in
  transit, not a forgery: what binds it is the commit, origin/main's tip, the harness and
  the check inputs, the age limit, and the owner's decision above that the VM runs the
  pre-flight. Code a head leaves running on the VM could write a proof for that head, as
  code left running on the Mac could already change a check's verdict there (the routes
  #218 lists). The checks CI runs on every pull request, and main's rules, still gate
  every merge.

  This entry approves the change to `scripts/safe_push.py` that brings the options
  `--emit-proof` and `--preflight-proof` with their rules in the parser; the constants
  that set the proof's format, its age limit, the clock's allowance and the largest file
  read; the functions that list the check inputs' blobs, make and write the proof, and
  judge it; the step lines that report it, in the pre-flight's first and fourth steps, in
  the fifth step of the dry run that writes it, and in the merge's third; the record's field that names the proof; and the docstring and
  help that describe them.

  Approved here as well is the change to `scripts/test_safe_push.py` that adds the class
  `PreflightProof` and its tests: a proof accepted for a head that changes the checks, and
  each case the card plants falling back to the full pre-flight on the Mac.
