# Reconstructed Modular Layout

Acest pachet modularizează aplicația reconstruită fără a modifica logica originală.

## Structură
- `_loader.py` — încarcă dinamic fișierul `reconstructed/pacienti_desktop_reconstructed.py`
- `auth.py` — funcții de autentificare/utilizatori
- `db.py` — funcții de acces date SQLite
- `supabase.py` — funcții API Supabase
- `app_entry.py` — entrypoint UI

## Rulare
Din rădăcina proiectului:

```powershell
python -m recovered_mbm.reconstructed_modular.app_entry
```

## Instalare dependențe

```powershell
pip install -r recovered_mbm/reconstructed_modular/requirements_recovered.txt
```

## Rulare rapidă (PowerShell)

Din rădăcina proiectului:

```powershell
.\run_recovered.ps1
```

Opțiuni utile:

```powershell
.\run_recovered.ps1 -SkipInstall
.\run_recovered.ps1 -ForceVenv
.\run_recovered.ps1 -CheckOnly
```

## Notă
Este un refactor sigur de tip *facade/wrapper*: simbolurile sunt expuse modular, dar execuția rămâne compatibilă cu sursa reconstruită.

Importurile din `auth.py`, `db.py`, `supabase.py` sunt **lazy** (nu încarcă imediat modulul mare).

## Dependențe runtime
Pentru rulare UI completă sunt necesare aceleași dependențe ca în aplicația originală (ex: `pandas`, `PyQt6`, `reportlab`).
