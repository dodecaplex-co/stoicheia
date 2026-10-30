# Merge audit: #415, axiom wave two

*30 October 2026. For #485. The history was read with Git at main 32eebe4ba, and every file and line cited below was read again at main 05640d4c7; none of the files cited changed between the two. The audit changed no file but this one.*

The merge that landed #415, axiom wave two (b77b645f, 24 October 2026, 216 files), put back an older version of README's row for the formal model, and so lost #375's account of the model's replay. This audit asked whether main's text was lost anywhere else in the same way. That row is the only loss, and 5e33da16a (#489) has put it back; in 29 other places a merge left out lines from main's side, 24 of them because the axiom retirement rewrote main's words on purpose and 5 where main has since replaced the text.

## Method

**The merge.** b77b645f has two parents: main at 69850d21b, and the branch's tip at 65db996e5. Two facts settle where to look:

- `git diff --quiet b77b645f 65db996e5` exits 0, so the merge's tree is the branch's tree, file for file.
- `git merge-base 69850d21b 65db996e5` gives 69850d21b, so all of main was already in the branch, and main's side brought nothing the branch had not merged.

So b77b645f resolved nothing by hand, and all 216 files it changed came from the branch as it stood.

**Where a loss must be.** The branch merged main 64 times between 19 and 24 October 2026. `git rev-list --merges 69850d21b..65db996e5` lists those merges, beside 70 ordinary commits. In b77b645f main is the first parent, and in these merges it is the second. If one of these merges resolved a conflict by taking the branch's side, it dropped main's text there. Every later merge then carried the drop without a conflict, because its merge base already held main's text and the branch had changed it. b77b645f brought the result to main. So the search reads those 64 merges, in these passes:

1. **The line scan.** For each merge, and each file both parents had changed since their merge base, the scan lists the lines one side added that the merge's result lacks. It keeps those whose side lies on main's line of first parents. It leaves out the generated edition (book/, facts.json, CERTIFICATE.md, GRAPH.md). It found 30 file-merges, in 8 merges, all on main's side.
2. **Each entry read.** Each of the 30 was read as a word-by-word diff of the merge against main's side, with the commits on each side that touched the file, and followed to the file on main today.
3. **Where each line came from.** A lost line counts as main's when the main that the merge's side carried held it and the merge base did not. This pass ran over the losses of every merge, on either side, to find text of main's that came in through a sub-branch.
4. **Each merge redone.** `git merge-tree` redid each of the 64 merges. The pass listed each file whose recorded result differs from the automatic one, whichever side had changed it.
5. **Copies counted.** The line scan again, counting the copies of each line instead of asking only whether it is there.
6. **Text put back.** Lines that main's side had deleted, a merge kept, and #415 then brought back to main.
7. **Stale copies.** The 70 ordinary commits, searched for lines main once had and had since removed, which a commit adds back.
8. **Deleted and moved files.** The files a merge deleted, and the files either side moved.

## The one loss

**Lost.** 106c74fed (23 October 2026) merged main at 6152394a5, which carried #375 (0a19e2c13, 22 October). #375 had added an account of the replay to README's row for the formal model. That account says that leanchecker replays every compiled declaration of the model's Model and Check libraries, then replays Check's whole environment from nothing, and it says what the replay leaves out. For the retirement, the branch had changed the same row from 80 axioms to 49. README conflicted, and the merge took the branch's row: the count was right, but the account of the replay was gone. #375's other sentence, in the row for the negative tests, came through.

**Carried.** Two later merges of main, 918efd90b (23 October) and 518e67597 (24 October), brought further changes to README from main. Each kept the branch's row without a conflict. Their merge bases, c9411ece6 and dd27962c2, held the account of the replay and the branch's side did not, so the three-way merge read its absence as the branch's own change. b77b645f brought the row to main on 24 October.

**Restored.** 5e33da16a, landed by cf1591f14 (#489) on 25 October, put the account back. It stands on main today at `README.md:91`, with the count at 48 since Circle 1 was retired (80e7ee2d7).

## The 30 entries

The entries are in the order Git lists the merges, newest first. The lines are those of main's side that the merge's result lacks, as the scan counted them. "Intended" means the retirement rewrote main's words on purpose. "Superseded" means the text was generated, stamped or moved, and main has replaced it since.

| # | Merge | File | Lines | Class | Reason and evidence |
|---|---|---|---|---|---|
| 1 | 1df5d14ba | tests/model/hyperbolic.py | 40 | Intended | Main's 5f065a039 edited the numerical checks of laws the branch retired, Pasch 4 and Triple incidence 1 and 2 among them. Their code left with the 31 laws in 22252498c, and none of them is in `Certificate/axioms.lock` today. |
| 2 | 1df5d14ba | tests/model/search.py | 12 | Intended | The same: helpers of the retired laws. |
| 3 | 3d61e0f79 | docs/briefs/0002-decisions.md | 1 | Intended | Main's sentence kept, with the caveat of #160 inserted (`docs/briefs/0002-decisions.md:5825`). |
| 4 | 3d61e0f79 | tests/model/MODEL.md | 3 | Intended | Once the 31 were retired, "eight for retired axioms and 31 prepared" became "the 39 numerical predicates of the retired rules". Since replaced by 80e7ee2d7 and 089badbd8 (`tests/model/MODEL.md:72`). |
| 5 | 0328bcb61 | Audit/Superposition.lean | 17 | Intended | The pinned axiom lists made again: retired names leave, and the axioms of the proved rules enter. One line of prose extended (`Audit/Superposition.lean:29`). `lake build` checks the pins. |
| 6 | 0328bcb61 | Elements/Figure/Superposition.lean | 1 | Intended | A docstring reflowed round one added sentence, all of main's words kept (`Elements/Figure/Superposition.lean:27`). |
| 7 | 0328bcb61 | Elements/Foundations/Superposition/Syntax.lean | 5 | Intended | A paragraph rewritten for the retirement, main's sentences inside it (`Elements/Foundations/Superposition/Syntax.lean:194`). |
| 8 | 0328bcb61 | docs/briefs/0009-superposition.md | 5 | Intended | The retirement made "at this revision it lists none" false, and it became "before the second retirement it listed none" (`docs/briefs/0009-superposition.md:442`). |
| 9 | 918efd90b | Audit/Crossing.lean | 2 | Intended | Main's sentence of #131 kept, rewrapped. Since replaced by 87a29a212 (#547) (`Audit/Crossing.lean:140`–`142`). |
| 10 | 918efd90b | README.md | 1 | Superseded | Book III's row between the scope:III markers, which render.py writes, and has written again since (`README.md:33`). |
| 11 | 918efd90b | docs/reports/overlaps.md | 1 | Intended | Only the counts changed, 51 to 38 and 56 to 39, for the retirement. The row has been recounted since (`docs/reports/overlaps.md:203`). |
| 12 | 106c74fed | README.md | 1 | Restored | The formal model's row: 80 became 49 as intended, but #375's account of the replay was dropped. Restored by 5e33da16a (#489) (`README.md:91`). |
| 13 | 64852bd48 | Audit/Crossing.lean | 6 | Intended | The paragraph of entry 9: main's text kept, with a clause on the retirement added (`Audit/Crossing.lean:133`–`142`). |
| 14 | 64852bd48 | Audit/screen.py | 10 | Intended | The counts and the list of circle rules cut to the 49 axioms, and "what the next run will show" replaced by the run of 21 October 2026 (`Audit/screen.py:23`). |
| 15 | 64852bd48 | README.md | 1 | Superseded | The generated scope:III row, as in entry 10. |
| 16 | 64852bd48 | docs/briefs/book-I.md | 2 | Intended | The retirement made "without construction rules" false, and the sentence was rewritten (`docs/briefs/book-I.md:120`–`122`). |
| 17 | 64852bd48 | docs/reports/overlaps.md | 11 | Intended | Main's paragraph on I.13's rule kept and extended (`docs/reports/overlaps.md:317`–`321`). The paragraph on the screen's 80 axioms and its next run rewritten for the 49 and the run of 21 October 2026 (now `:837`–`841`). |
| 18 | 64852bd48 | mishnah/I/04.md | 1 | Intended | Main's paragraph kept, with sentences on the retirement added (`mishnah/I/04.md:7`). |
| 19 | 64852bd48 | mishnah/I/08.md | 1 | Intended | The same (`mishnah/I/08.md:5`). |
| 20 | 64852bd48 | review/I/22.toml | 2 | Intended | "a rule we assume" became "now proved", for rules the retirement proved (`review/I/22.toml:20`, `:26`). |
| 21 | 64852bd48 | review/I/31.toml | 1 | Intended | The same, for `Tacit.exists_point_between` (`review/I/31.toml:16`). |
| 22 | 64852bd48 | review/II/14.toml | 1 | Intended | The same, for `Tacit.on_circle_of_len_eq` (`review/II/14.toml:38`). |
| 23 | 64852bd48 | tests/certificate_expectations.json | 4 | Intended | The counts of III.1 Por. and III.1, 51 and 56, became 38 and 39, and the caveat on `Tacit.centre_unique` was kept. They are 37 and 38 now (`tests/certificate_expectations.json:52`, `:60`). |
| 24 | 5c93de52b | docs/reports/overlaps.md | 1 | Intended | Main's "give 20, 19 and 61." kept, reflowed, with the rerun of 22 October after it. Main itself replaced the sentence in c3a0c0963 (#331) before #415 landed (now `docs/reports/overlaps.md:314`). |
| 25 | 890032fd6 | Audit/Overlaps.lean | 1 | Intended | Axiom wave one made `Tacit.adjacent_eq_of_right` a theorem, so it left the pinned axioms (`Audit/Overlaps.lean:315`–`319`). |
| 26 | 890032fd6 | Elements/Figure/OnCircles.lean | 3 | Intended | Wave one: "System E, Circle 2" became "Circle 2, proved from Circle 3", and Generalities 2 became `Tacit.centre_unique`, proved (`Elements/Figure/OnCircles.lean:81`). The passage on Circle 2 has since left with the retirement of 24 October (`:22`–`23`). |
| 27 | 890032fd6 | docs/briefs/book-I.md | 1 | Intended | Wave one retired I.7's row for Circle 4, so "four propositions" became three. The paragraph has been replaced since (`docs/briefs/book-I.md:190`). |
| 28 | 890032fd6 | review/III/01.toml | 1 | Superseded | The merge kept the branch's stamp, 2c3686e, which matched its rewritten notes, over main's 39e9dbb. Stamped again since, at d06d39e33 (`review/III/01.toml:80`). |
| 29 | 890032fd6 | review/III/02.toml | 1 | Superseded | The same. Stamped again since, at 3b0757e4a (`review/III/02.toml:56`). |
| 30 | 890032fd6 | scripts/negative_tests.py | 3 | Superseded | Two wordings of one assertion, and the merge kept the branch's. 2a39c2b77 (#205) moved the plant to a file of its own, where main's wording stands (`scripts/negative/planted_assumptions.py:27`–`28`, `:87`). |

## What the scan cannot see

The line scan compares sets of lines, at each file's path, in files both sides changed. Each limit has a pass that covers it:

- **A lost line that stands elsewhere in the file is missed.** The count pass looked for these. It found only more of the retired laws' code, and one wrapped line ending "rule.", which is part of a rewrite.
- **A rewrapped paragraph counts as lost,** though its words are kept. Entries 6, 9 and 24 are of this kind, and each was read word by word.
- **A line's place on main today is found by its old path and its exact words.** That overstates: entry 30's lines and the rewrapped prose look absent, though they stand. Each entry's place on main was therefore found by reading, and the table gives it.
- **Only files both sides changed are read.** The merge-tree pass redid all 64 merges. It found seven files that only main's side had changed and that a merge edited: Audit/Centre.lean in 64852bd48; Audit/Crossing.lean in 22252498c; Elements/Figure/Superposition.lean, Elements/Foundations/Superposition/Syntax.lean and review/I/04.toml in 58018a31d; and Audit/Superposition.lean and tests/test_check_style.py in f564f82da. Each edit is the retirement's rewrite.
- **Text of main's that came through a sub-branch is missed,** because the scan keeps only losses on a side that lies on main's line of first parents. Three sub-branches of the retirement had merged main themselves, and each had landed on main through its own pull request (#413, #265 and #406) before 69850d21b. The pass that asks where each line came from found further losses of main's text in 22252498c, f564f82da, 251129ba2, abe56d0fb, and in eight earlier merges that repeat 0328bcb61's rewrite of the superposition files. All are intended:
  - the counts changed, 80 axioms to 49 and 74 tacit rules to 43;
  - "assumed" became "proved";
  - the claim in mishnah/intro/I.md about I.5 and Postulate 2 was rewritten (cbd0e8cac).

  The derivations of Intersection 2 and of the converse of angle addition, which model/README.md dropped in 251129ba2, stand in FORMALIZATION's table "Rules now proved" (`docs/FORMALIZATION.md:793`, `:795`).
- **Deleted and moved files are skipped,** since a deleted file has no result to compare, and a moved file has a different name on each side. Merges deleted 11 files under Staging/. Main's side had already deleted every one of them when staging was retired, so nothing of main's was lost. Main's side moved one file, Staging/Stage3/Placement/OnLine.lean to Elements/BookIII/Placement/OnLine.lean, and the merge only added the branch's two lines to it. Entry 30 is a move of the same kind: main's text stands in a file with another name.
- **Text main deleted that a merge put back** is not a loss, and the scan does not look for it. The pass for it found nine lines. Each is a copy of a line that stands elsewhere in the same file, and none is main's deleted text come back.
- **Ordinary commits are not merges,** so a commit that copies back a stale version of a file is outside the scan. The pass over the 70 ordinary commits found none.
- **Scope.** The sub-branches' own merges of main landed through their own pull requests. So they lie outside 69850d21b..65db996e5, and outside #485.

Nothing is left to restore: the one loss, README's account of the replay, is back on main, and every other place where a merge dropped main's text is recorded here as intended or superseded.
