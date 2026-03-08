from __future__ import annotations

from ._loader import get_symbol


_SYMBOLS = {
	"get_conn": "get_conn",
	"init_db": "init_db",
	"check_db_integrity": "check_db_integrity",
	"get_master": "get_master",
	"find_master_by_cnp": "find_master_by_cnp",
	"find_master_by_exact_name": "find_master_by_exact_name",
	"find_patients_by_name": "find_patients_by_name",
	"insert_master": "insert_master",
	"update_master": "update_master",
	"delete_master": "delete_master",
	"insert_consult": "insert_consult",
	"update_consult": "update_consult",
	"delete_consult": "delete_consult",
	"get_consults": "get_consults",
	"get_latest_consult": "get_latest_consult",
	"master_list_with_latest_consult": "master_list_with_latest_consult",
}

__all__ = list(_SYMBOLS.keys())


def __getattr__(name: str):
	"""Gestioneaza operatia `__getattr__` (getattr)."""
	target = _SYMBOLS.get(name)
	if target is None:
		raise AttributeError(name)
	fn = get_symbol(target)
	globals()[name] = fn
	return fn
