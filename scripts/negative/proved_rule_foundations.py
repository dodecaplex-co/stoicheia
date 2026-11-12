"""Exercise the certificate producer on three actual proofs in an isolated package.

The plant expects [] of the pure rule, ["Classical.choice"] of the choice proof
and ["sorryAx"] of the sorry proof in proved_rule_foundations. A literal verifier
in this file checks the emitted certificate. Two independent copies lose one
required name each. The verifier must refuse them with exactly:
  proved_rule_foundations: Tacit.foundations_choice missing Classical.choice
  proved_rule_foundations: Tacit.foundations_sorry missing sorryAx
The suite records each verified refusal and fails if the control fails, a loss
passes, or its diagnostic differs. These two losses
are judged here. All fixture inputs and outputs
belong to the temporary package, cleaned in finally; the edition is read only.
"""

import copy
import json
import os
import subprocess
import tempfile
from pathlib import Path

import negative_tests as nt

BUILDS = True

TABLE = "proved_rule_foundations"
FIXTURE = 'import Lean\n\nuniverse u\nnamespace Elements\n\ndef companions : List (Lean.Name × String) := []\n\ntheorem CommonNotion1 : True := True.intro\ntheorem CommonNotion2 : True := True.intro\ntheorem CommonNotion3 : True := True.intro\ntheorem CommonNotion4 : True := True.intro\ntheorem CommonNotion4.angle : True := True.intro\ntheorem CommonNotion4.triangle : True := True.intro\ntheorem CommonNotion5 : True := True.intro\n\ntheorem Tacit.foundations_pure : True := True.intro\ntheorem Tacit.foundations_choice (α : Sort u) (h : Nonempty α) : Nonempty α :=\n  ⟨Classical.choice h⟩\ntheorem Tacit.foundations_sorry : False := by sorry\n\nend Elements\n'
EXPECTED = {
    "Tacit.foundations_choice": ["Classical.choice"],
    "Tacit.foundations_pure": [],
    "Tacit.foundations_sorry": ["sorryAx"],
}


def object_pairs(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"{TABLE}: duplicate key {key}")
        result[key] = value
    return result


def nonfinite(value):
    raise ValueError(f"{TABLE}: nonfinite constant {value}")


def verify(path):
    """Read the real output or a loss copy with the same independent literal oracle."""
    facts = json.loads(path.read_text(encoding="utf-8"),
                       object_pairs_hook=object_pairs, parse_constant=nonfinite)
    if not isinstance(facts, dict):
        raise ValueError(f"{TABLE}: certificate is not an object")
    table = facts.get(TABLE)
    if not isinstance(table, dict) or set(table) != set(EXPECTED):
        raise ValueError(f"{TABLE}: table or rule keys differ")
    for rule, expected in EXPECTED.items():
        value = table[rule]
        if (not isinstance(value, list) or any(not isinstance(v, str) for v in value)
                or value != sorted(set(value))):
            raise ValueError(f"{TABLE}: {rule} is not a sorted list of distinct names")
        for name in expected:
            if name not in value:
                raise ValueError(f"{TABLE}: {rule} missing {name}")
        if value != expected:
            raise ValueError(f"{TABLE}: {rule} differs from the literal oracle")
    for field in ("proved_rules", "proved_rule_cites"):
        if facts.get(field) != {rule: [] for rule in EXPECTED}:
            raise ValueError(f"{TABLE}: {field} differs from the literal oracle")
    for field, empty in (("propositions", []), ("axiom_modules", {}),
                         ("axiom_types", {}), ("vocabulary", {})):
        if facts.get(field) != empty:
            raise ValueError(f"{TABLE}: {field} is not empty")
    return facts


def plant() -> None:
    temporary = tempfile.TemporaryDirectory(prefix="stoicheia-rule-foundations-")
    try:
        work = Path(temporary.name).resolve()
        if work.is_relative_to(nt.ROOT.resolve()):
            raise ValueError("the producer test package must be outside the edition")
        (work / "lakefile.toml").write_text(
            'name = "rule_foundations_fixture"\n'
            'defaultTargets = ["Elements"]\n\n[[lean_lib]]\nname = "Elements"\n',
            encoding="utf-8")
        (work / "lean-toolchain").write_bytes((nt.ROOT / "lean-toolchain").read_bytes())
        (work / "Elements.lean").write_text(FIXTURE, encoding="utf-8")
        # Copy the candidate producer whole; no collector is substituted for it.
        (work / "Facts.lean").write_bytes((nt.ROOT / "Certificate/Facts.lean").read_bytes())
        env = {key: value for key, value in os.environ.items()
               if key != "LEAN_PATH" and not key.startswith("LAKE")}
        env["LEAN_PATH"] = str(work / ".lake/build/lib/lean")
        # The package has no dependencies; the running toolchain supplies Lean.
        for command in (("lake", "build", "Elements"),
                        ("lake", "env", "lean", "Facts.lean")):
            result = subprocess.run(command, cwd=work, env=env,
                                    capture_output=True, text=True)
            if not nt.expect_success(f"{TABLE}: {' '.join(command)}", result):
                return
        emitted = verify(work / "facts.json")
        print(f"{TABLE}: control []; Classical.choice and sorryAx emitted")
        for rule, name, filename in (
                ("Tacit.foundations_choice", "Classical.choice", "choice-loss.json"),
                ("Tacit.foundations_sorry", "sorryAx", "sorry-loss.json")):
            loss = copy.deepcopy(emitted)
            loss[TABLE][rule].remove(name)
            path = work / filename
            path.write_text(json.dumps(loss) + "\n", encoding="utf-8")
            expected = f"{TABLE}: {rule} missing {name}"
            try:
                verify(path)
            except ValueError as error:
                if str(error) != expected:
                    raise ValueError(f"{TABLE}: wrong loss diagnostic: {error}") from error
                print(str(error))
                nt.refused(f"{TABLE}: {name} loss caught")
            else:
                raise ValueError(f"{TABLE}: {name} loss passed")
    except (OSError, ValueError) as error:
        message = f"{TABLE}: {error}"
        nt.failures.append(message)
        print(f"✗ {message}")
    finally:
        temporary.cleanup()
