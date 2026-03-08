from __future__ import annotations

import importlib.util
from functools import lru_cache
from pathlib import Path
from types import ModuleType


@lru_cache(maxsize=1)
def load_legacy_module() -> ModuleType:
    """Gestioneaza operatia `load_legacy_module` (load legacy module)."""
    base_dir = Path(__file__).resolve().parent.parent
    legacy_path = base_dir / "reconstructed" / "pacienti_desktop_reconstructed.py"
    if not legacy_path.exists():
        raise FileNotFoundError(f"Missing reconstructed source: {legacy_path}")

    spec = importlib.util.spec_from_file_location("pacienti_desktop_reconstructed", legacy_path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"Cannot load module from {legacy_path}")

    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def get_symbol(name: str):
    """Gestioneaza operatia `get_symbol` (get symbol)."""
    module = load_legacy_module()
    if not hasattr(module, name):
        raise AttributeError(f"Symbol '{name}' not found in reconstructed module")
    return getattr(module, name)
