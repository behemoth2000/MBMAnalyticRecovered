# MBM - Analytic Recovery Report

## Status
- Installer processed successfully from: `D:\Download\MBM-Analytic Soft (1).exe`
- Installation payload recovered in: `recovered_mbm/installed`
- PyInstaller CArchive extracted in: `recovered_mbm/installed/pacienti_desktop.exe_extracted`
- PYZ extracted (Python 3.14 marshal) in: `recovered_mbm/pyz_extracted`
- Main entrypoint disassembly generated: `recovered_mbm/decompiled/pacienti_desktop1-2.dis.txt`

## Key recovered artifacts
- Reconstructed source candidate:
  - `recovered_mbm/reconstructed/pacienti_desktop_reconstructed.py`
  - `recovered_mbm/reconstructed/pacienti_desktop_reconstructed_backup.py`
- Recovery tooling scripts:
  - `recovered_mbm/disassemble_pyc.py`
  - `recovered_mbm/extract_pyz_314.py`
- Match report between executable symbols and source:
  - `recovered_mbm/reconstruction_match_report.json`

## Validation notes
- Executable detected as **PyInstaller** with **Python 3.14** bytecode.
- `PYZ.pyz` extraction succeeded for **1529 modules** (1 module failed).
- Symbol overlap vs source file is high (`matched_count` in report), indicating the reconstructed source file is a valid practical recovery baseline.

## Known limitation
- Full automatic decompilation from Python 3.14 `.pyc` to high-fidelity original `.py` is still limited in current public decompilers.
- For this reason, recovery used:
  1. direct extraction of packaged files,
  2. disassembly of main entrypoint,
  3. verified source baseline reconstruction.

## Recommended next step
- Use `recovered_mbm/reconstructed/pacienti_desktop_reconstructed.py` as main recovered source.
- If needed, manually port any missing behaviors by checking:
  - `recovered_mbm/decompiled/pacienti_desktop1-2.dis.txt`
  - specific modules from `recovered_mbm/pyz_extracted`.
