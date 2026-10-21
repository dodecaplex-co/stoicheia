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
# The generated files are what the generator writes

At every build, the generator (`Check/Generator.lean`) runs again here, on the library's
declarations, and the build fails unless:

* `model/lock.sha256` holds the sha256 of `Certificate/axioms.lock`;
* every file of `Elements/Foundations/` is imported above, so that no axiom is missed;
* the axioms declared there are exactly the lock's `[axioms]`, each with the statement the
  lock prints, and every word they reach is in the lock's `[vocabulary]` as Lean prints it;
* every constant of the project that the laws reach has a translation; and
* `Model/Laws.lean`, `Check/Laws.lean` and `Model/Assembly.lean` are, line for line, what
  the generator writes now.

Its imports are exactly those of `Check/Write.lean`, which writes the files, so that the two
print alike. It imports neither `Model/Laws.lean` nor anything that does: the generator adds
the words it translates to its own environment as it prints them.
-/

run_cmd Check.Generator.checkFiles
