"""`pipeline.sync_rumoca`: rumoca's shared Lean modules against dynacert's `Rumoca/`."""

import pytest

from dynacert.pipeline import CertError, sync_rumoca

PRELUDE = "namespace Rumoca\nend Rumoca\n"
LOG = "noncomputable def LieGroups.SO3.Quat.log_map (q : Fin 4 → ℝ) : Fin 3 → ℝ := 0\n"


def tree(base, files):
    for rel, text in files.items():
        p = base / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text)
    return base


def test_adds_new_function_modules(tmp_path):
    out = tree(tmp_path / "out", {"Rumoca/Prelude.lean": PRELUDE,
                                  "Rumoca/Fn/LieGroups/SO3/Quat/log_map.lean": LOG})
    root = tree(tmp_path / "root", {"Rumoca/Prelude.lean": PRELUDE})
    added = sync_rumoca(out, root)
    dst = root / "Rumoca/Fn/LieGroups/SO3/Quat/log_map.lean"
    assert added == [dst] and dst.read_text() == LOG
    assert sync_rumoca(out, root) == []  # identical text: nothing to do


def test_changed_function_module_is_an_error(tmp_path):
    out = tree(tmp_path / "out", {"Rumoca/Prelude.lean": PRELUDE,
                                  "Rumoca/Fn/LieGroups/SO3/Quat/log_map.lean": LOG})
    root = tree(tmp_path / "root", {"Rumoca/Prelude.lean": PRELUDE,
                                    "Rumoca/Fn/LieGroups/SO3/Quat/log_map.lean": LOG + "-- old\n"})
    with pytest.raises(CertError, match="log_map.lean"):
        sync_rumoca(out, root)
    assert (root / "Rumoca/Fn/LieGroups/SO3/Quat/log_map.lean").read_text().endswith("-- old\n")


def test_changed_prelude_is_an_error(tmp_path):
    out = tree(tmp_path / "out", {"Rumoca/Prelude.lean": PRELUDE + "-- new\n"})
    root = tree(tmp_path / "root", {"Rumoca/Prelude.lean": PRELUDE})
    with pytest.raises(CertError, match="Prelude"):
        sync_rumoca(out, root)


def test_model_without_functions(tmp_path):
    out = tree(tmp_path / "out", {"Rumoca/Prelude.lean": PRELUDE})
    root = tree(tmp_path / "root", {"Rumoca/Prelude.lean": PRELUDE})
    assert sync_rumoca(out, root) == []
