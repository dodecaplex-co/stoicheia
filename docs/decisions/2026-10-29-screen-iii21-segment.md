<!-- entry: id=screen-iii21-segment cards=663 line="The screen's account of what its lemmas leave out states III.21 with its restriction to the points on the other side of the straight line joining the circumference's ends." -->
- **The screen states III.21 with its restriction (checks,
  [#663](https://github.com/dodecaplex-co/stoicheia/issues/663)).** The coordinator's
  orders of 29 October 2026, 12:33, assign card #663 to ship TL; this entry claims no
  decision of the owner's.

  `Audit/screen.py`'s docstring says what the lemmas on Lean's chosen magnitudes leave
  unsearched. For `circumference` and `standing` it said that every point of the circle
  gives the same angle, and credited III.21 with it. III.21 says less: "In a circle the
  angles in the same segment are equal to one another", so the points are those on the
  other side of the straight line joining the circumference's ends, as
  [the catalogue of overlaps](../reports/overlaps.md) now puts it. The sentence now says
  so. The screen's behaviour, its output and its tests are unchanged: the docstring's
  first line alone is printed, by `--help`, and no test quotes the sentence.

  This entry approves the change to `Audit/screen.py`, in its docstring.
