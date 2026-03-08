__all__ = ["run_app"]


def run_app():
	"""Gestioneaza operatia `run_app` (run app)."""
	from .app_entry import run_app as _run_app
	return _run_app()
