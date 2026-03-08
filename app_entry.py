from __future__ import annotations

from ._loader import load_legacy_module


def run_app() -> int:
    """Gestioneaza operatia `run_app` (run app)."""
    legacy = load_legacy_module()
    app_class = getattr(legacy, "App")
    ensure_default_admin_user = getattr(legacy, "ensure_default_admin_user")
    QApplication = getattr(legacy, "QApplication")

    ensure_default_admin_user()
    qapp = QApplication.instance() or QApplication([])
    window = app_class()
    window.show()
    return qapp.exec()


if __name__ == "__main__":
    raise SystemExit(run_app())
