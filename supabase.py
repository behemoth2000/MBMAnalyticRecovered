from __future__ import annotations

from ._loader import get_symbol


_SYMBOLS = {
	"supabase_headers": "supabase_headers",
	"supabase_request": "supabase_request",
	"supabase_auth_login": "supabase_auth_login",
	"supabase_auth_refresh": "supabase_auth_refresh",
	"supabase_auth_logout": "supabase_auth_logout",
	"supabase_upsert": "supabase_upsert",
	"supabase_fetch_updated": "supabase_fetch_updated",
	"supabase_storage_upload": "supabase_storage_upload",
	"supabase_call_function": "supabase_call_function",
	"get_supabase_access_token": "get_supabase_access_token",
	"set_supabase_tokens": "set_supabase_tokens",
	"clear_supabase_tokens": "clear_supabase_tokens",
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
