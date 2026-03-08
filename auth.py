from __future__ import annotations

from typing import Any, Dict, Optional

from ._loader import get_symbol


_SYMBOLS = {
    "hash_password": "_hash_password",
    "upsert_user": "upsert_user",
    "get_user": "get_user",
    "validate_login": "validate_login",
    "ensure_default_admin_user": "ensure_default_admin_user",
    "list_users": "list_users",
    "get_current_user": "get_current_user",
    "get_current_role": "get_current_role",
    "set_current_user_role": "set_current_user_role",
}

__all__ = [*list(_SYMBOLS.keys()), "authenticate"]


def __getattr__(name: str):
    """Gestioneaza operatia `__getattr__` (getattr)."""
    target = _SYMBOLS.get(name)
    if target is None:
        raise AttributeError(name)
    fn = get_symbol(target)
    globals()[name] = fn
    return fn


def authenticate(username: str, password: str) -> Optional[Dict[str, Any]]:
    """Gestioneaza operatia `authenticate` (authenticate)."""
    validate_login = __getattr__("validate_login")
    return validate_login(username, password)
