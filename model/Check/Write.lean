import Elements.Foundations.CommonNotions
import Elements.Foundations.Definitions
import Elements.Foundations.DefinitionsII
import Elements.Foundations.DefinitionsIII
import Elements.Foundations.Magnitudes
import Elements.Foundations.Phrases
import Elements.Foundations.Postulates
import Elements.Foundations.Tacit.Constructions
import Elements.Foundations.Tacit.Diagram
import Elements.Foundations.Tacit.Magnitudes
import Elements.Foundations.Tacit.Metric
import Elements.Foundations.Tacit.Superposition
import Elements.Foundations.Tacit.Transfer
import Elements.Foundations.Words
import Elements.Foundations.Superposition.Restriction
import Model.Signature
import Check.Generator

/-!
# Writing the generated files

Run, in `model/`,

```sh
lake lean Check/Write.lean
```

to write `Model/Laws.lean`, `Check/Laws.lean` and `Model/Assembly.lean` from the library's
declarations (`lake lean` builds this file's imports first). Do it after a change to the
lock's axioms or to a word they reach, and after a theorem in the plane proves a law, then run
`lake build`, which checks the files against the generator (`Check/Generated.lean`) and each
law against the library (`Check/RoundTrip.lean`, `Check/Laws.lean`).

This file is not part of the `Check` library, and `lake build` never runs it. Its imports are
exactly those of `Check/Generated.lean`, so that the two print alike. Like
`Certificate/Facts.lean`, it writes its files whenever Lean elaborates it, an editor's
included.
-/

run_cmd Check.Generator.writeFiles
