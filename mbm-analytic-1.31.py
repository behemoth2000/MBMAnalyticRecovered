import sys
import os
import subprocess
import sqlite3
import shutil
import csv
import threading
import json
import time
import hashlib
import base64
import uuid
import urllib.request
import urllib.parse
import urllib.error
from pathlib import Path
from typing import Optional, Tuple, List, Dict, Any
from datetime import datetime, date, timedelta, timezone
import mimetypes
import io
import zipfile
import gzip

import pandas as pd
import re
import unicodedata
import textwrap
import traceback
import warnings
import importlib
import ctypes
import inspect
from ctypes import wintypes

from PyQt6.QtCore import (
    Qt, QDate, QTimer, pyqtSignal, QObject, QThread, QRect, QUrl, QSize, QPointF, QStringListModel, QEvent
)
from PyQt6.QtGui import QColor, QBrush, QFont, QPixmap, QPainter, QIcon, QDesktopServices, QImage, QPen, QTextCharFormat, QAction, QShortcut, QKeySequence
from PyQt6.QtWidgets import (
    QApplication, QWidget, QVBoxLayout, QHBoxLayout, QFormLayout,
    QLineEdit, QTextEdit, QPushButton, QTableWidget, QTableWidgetItem,
    QMessageBox, QLabel, QFileDialog, QDialog, QCalendarWidget,
    QDialogButtonBox, QToolButton, QSplitter, QHeaderView, QScrollArea, QStyledItemDelegate, QStyleOptionViewItem,
    QCompleter, QGridLayout,
    QAbstractItemView, QComboBox, QSpinBox, QAbstractSpinBox, QProgressDialog, QGroupBox, QSizePolicy, QCheckBox,
    QProgressBar, QSplashScreen, QStyle, QInputDialog, QTabWidget, QFrame, QMenu
)

# PDF reporting
from reportlab.lib.pagesizes import A4
from reportlab.pdfgen import canvas
from reportlab.lib.units import cm

# ============================================================
# CONFIG
# ============================================================
APP_DIR = Path.home() / "PacientiApp"
APP_DIR.mkdir(parents=True, exist_ok=True)
DB_PATH = APP_DIR / "pacienti.db"
ICD10_CSV_PATH = APP_DIR / "icd10.csv"
ICD10_READONLY_LOCAL = True
ICD10_SUPABASE_ENABLED = True
ICD10_SUPABASE_SYNC_DAYS = 7
ICD10_BUNDLE_COPIED = False
ICD10_BUNDLE_PATHS = []
_meipass = getattr(sys, "_MEIPASS", None)
if _meipass:
    ICD10_BUNDLE_PATHS.append(Path(_meipass) / "icd10.csv")
ICD10_BUNDLE_PATHS.extend([
    Path(__file__).resolve().parent / "icd10.csv",
    Path.cwd() / "icd10.csv",
])

RO_LOCALITIES_BUNDLE_PATHS: List[Path] = []
if _meipass:
    RO_LOCALITIES_BUNDLE_PATHS.append(Path(_meipass) / "ro_localities.csv.gz")
    RO_LOCALITIES_BUNDLE_PATHS.append(Path(_meipass) / "ro_localities.csv")
RO_LOCALITIES_BUNDLE_PATHS.extend([
    Path(__file__).resolve().parent / "ro_localities.csv.gz",
    Path(__file__).resolve().parent / "ro_localities.csv",
    Path.cwd() / "ro_localities.csv.gz",
    Path.cwd() / "ro_localities.csv",
])

# App version + auto-update (Supabase Storage)
APP_VERSION = "1.31.14"
APP_VERSION_LABEL = f"v{APP_VERSION}"
UPDATE_BUCKET = "updates"
UPDATE_MANIFEST_NAME = "latest.json"
UPDATE_MANIFEST_URL = ""  # optional override
# Ed25519 public key (base64) used to verify update manifest
UPDATE_PUBLIC_KEY_B64 = "RRWu69IeuJ9Lnv7wYNkQMNObJTjSC7Wg4jaJbkRuPEk="
UI_TRIANGLE_COLLAPSED = "\u25B8"
UI_TRIANGLE_EXPANDED = "\u25BE"

# Autosave / backup (VARIANTA 2)
AUTOSAVE_EVERY_SECONDS = 5 * 60      # 5 minute
AUTOSAVE_DEBOUNCE_SECONDS = 30       # backup la 30 sec dupÄ ultima modificare

AUTOBACKUP_DIR = APP_DIR / "autobackups"
AUTOBACKUP_DIR.mkdir(parents=True, exist_ok=True)
DAILY_DIR = AUTOBACKUP_DIR / "daily"
DAILY_DIR.mkdir(parents=True, exist_ok=True)

REPORTS_DIR = APP_DIR / "rapoarte"
REPORTS_DIR.mkdir(parents=True, exist_ok=True)

LOG_DIR = APP_DIR / "logs"
LOG_DIR.mkdir(parents=True, exist_ok=True)
ERROR_LOG_PATH = LOG_DIR / "app_errors.log"
SYNC_LOG_DIR = LOG_DIR / "sync"
SYNC_LOG_DIR.mkdir(parents=True, exist_ok=True)
SYNC_LOG_RETENTION_DAYS = 30

# Alertele includ toČ›i pacienČ›ii cu data_revenire_control Ă®n urmÄtoarele 7 zile
ALERT_ONLY_PROGRAMAT = False

REMINDER_RULE_DAY_BEFORE = "day_before"
REMINDER_RULE_2H_BEFORE = "two_hours_before"
REMINDER_RULE_SAME_DAY = "same_day_at_time"
REMINDER_RULE_CHOICES: List[Tuple[str, str]] = [
    (REMINDER_RULE_DAY_BEFORE, "Cu 24h inainte"),
    (REMINDER_RULE_2H_BEFORE, "Cu 2 ore inainte"),
    (REMINDER_RULE_SAME_DAY, "In ziua programarii (la/dupa ora)"),
]
REMINDER_LAST_SLOT_KEY = "reminder_last_run_slot"
REMINDER_LAST_RUN_AT_KEY = "reminder_last_run_at"
REMINDER_INTERVAL_MIN_KEY = "reminder_run_interval_min"
REMINDER_INTERVAL_MIN_DEFAULT = 5
REMINDER_TEMPLATE_DEFAULT = (
    "Buna {nume_prenume}, va reamintim programarea din {date} la {time} "
    "cu {medic} la {location}. {contact}"
)
REMINDER_TEMPLATE_CONFIRM = (
    "Programarea dvs este confirmata: {date} la {time}, medic {medic}, {location}. {contact}"
)
REMINDER_TEMPLATE_CANCEL = (
    "Programarea din {date} la {time} a fost anulata. Pentru reprogramare contactati clinica: {contact}"
)
REMINDER_TEMPLATE_ORTOPEDIE = (
    "Buna {nume_prenume}, va reamintim consultul de ortopedie din {date} la {time} "
    "cu {medic}, {location}. {contact}"
)
REMINDER_TEMPLATE_FIZIOTERAPIE = (
    "Buna {nume_prenume}, va reamintim sedinta de fizioterapie din {date} la {time} "
    "cu {medic}, {location}. {contact}"
)
SESSION_SENSITIVE_TIMEOUT_MIN_KEY = "session_sensitive_timeout_min"
SESSION_SENSITIVE_TIMEOUT_MIN_DEFAULT = 20

# Reguli duplicate:
# - CNP identic -> acelaČ™i pacient + consult nou dacÄ data consult diferÄ
# - Nume identic (case-insensitive, trimmed) -> Ă®ntreabÄ user dacÄ e acelaČ™i pacient
# - Nume similar (fuzzy simplu) -> oferÄ opČ›iune "nu sunt duplicate"
FUZZY_THRESHOLD = 0.93
FUZZY_LIMIT = 180
FUZZY_MAX_PAIRS = 30
CATEGORY_NAME_MATCH_THRESHOLD = 0.88

# App icon (initialized in main)
APP_ICON: Optional[QIcon] = None

# Roles
DEFAULT_USER = "operator"
DEFAULT_ROLE = "admin"
ROLE_CHOICES = ["admin", "medic", "asistenta", "receptie"]

FEATURE_PERMISSION_ITEMS: List[Tuple[str, str]] = [
    ("main.save_consult", "Salveaza consult"),
    ("main.update_pacient", "Update pacient"),
    ("main.delete_pacient", "Sterge pacient"),
    ("main.import_excel", "Import Excel/CSV"),
    ("main.export_csv", "Export CSV"),
    ("main.backup_db", "Backup DB"),
    ("main.open_tools", "Deschide Instrumente"),
    ("main.search_advanced", "Cautare avansata"),
    ("main.check_duplicates", "Verificare duplicate"),
    ("main.recalc_ages", "Recalculeaza varste"),

    ("tools.periodic", "Raport periodic"),
    ("tools.adv_search", "Cautare avansata"),
    ("tools.stats", "Statistici avansate"),
    ("tools.kpi", "KPI"),
    ("tools.followup", "Modul follow-up"),
    ("tools.import_map", "Import mapare"),
    ("tools.view_import_profile_current", "Vezi maparea curenta"),
    ("tools.export_import_profile_current", "Export mapare curenta"),
    ("tools.reset_import_profile_current", "Reset mapare curenta"),
    ("tools.reset_import_profiles", "Reset mapari import"),
    ("tools.restore", "Restore DB"),
    ("tools.log", "Log activitate"),
    ("tools.error_log", "Log erori"),
    ("tools.interop", "Interoperabilitate"),
    ("tools.inventory", "Stocuri"),
    ("tools.role", "Rol/Permisiuni"),
    ("tools.backup_secure", "Backup securizat"),
    ("tools.sync_cloud", "Sync cloud"),
    ("tools.sync_status", "Status sync"),
    ("tools.test_supabase", "Test conexiune Supabase"),
    ("tools.reminders", "Remindere automate"),
    ("tools.clinic", "Setari clinica"),
    ("tools.locations", "Sedii"),
    ("tools.nomenclatoare", "Nomenclatoare"),
    ("tools.appt", "Programari"),
    ("tools.wait", "Lista asteptare"),
    ("tools.tasks", "Taskuri interne"),
    ("tools.claims", "Decontari"),
    ("tools.lab_import", "Import laborator"),
    ("tools.dashboard", "Dashboard"),
    ("tools.labels", "Etichete"),
    ("tools.icd10", "Import ICD-10"),
    ("tools.update_app", "Update aplicatie"),
    ("tools.db_cleanup", "Curata baza de date"),
    ("tools.recycle_bin", "Recycle Bin"),
]

FEATURE_PERMISSION_DEFAULTS = {k for k, _ in FEATURE_PERMISSION_ITEMS}
SETTINGS_SECRET_PREFIX = "enc:dpapi:"
SETTINGS_SECRET_KEYS = {
    "reminder_smsmobileapi_api_key",
    "reminder_android_gateway_token",
    "supabase_access_token",
    "supabase_refresh_token",
}

MAIN_FEATURE_BUTTONS: List[Tuple[str, str]] = [
    ("main.save_consult", "btn_save"),
    ("main.update_pacient", "btn_update_master"),
    ("main.delete_pacient", "btn_delete"),
    ("main.import_excel", "btn_import_excel"),
    ("main.export_csv", "btn_export_csv"),
    ("main.backup_db", "btn_backup"),
    ("main.open_tools", "btn_tools"),
    ("main.search_advanced", "btn_search_adv"),
    ("main.check_duplicates", "btn_check_dups"),
    ("main.recalc_ages", "btn_recalc_ages"),
]

TOOLS_FEATURE_BUTTONS: List[Tuple[str, str]] = [
    ("tools.periodic", "btn_periodic"),
    ("tools.adv_search", "btn_adv_search"),
    ("tools.stats", "btn_stats"),
    ("tools.kpi", "btn_kpi"),
    ("tools.followup", "btn_followup"),
    ("tools.import_map", "btn_import_map"),
    ("tools.view_import_profile_current", "btn_view_import_profile_current"),
    ("tools.export_import_profile_current", "btn_export_import_profile_current"),
    ("tools.reset_import_profile_current", "btn_reset_import_profile_current"),
    ("tools.reset_import_profiles", "btn_reset_import_profiles"),
    ("tools.restore", "btn_restore"),
    ("tools.log", "btn_log"),
    ("tools.error_log", "btn_error_log"),
    ("tools.interop", "btn_interop"),
    ("tools.inventory", "btn_inventory"),
    ("tools.role", "btn_role"),
    ("tools.backup_secure", "btn_backup_secure"),
    ("tools.sync_cloud", "btn_sync_cloud"),
    ("tools.sync_status", "btn_sync_status"),
    ("tools.test_supabase", "btn_test_supabase"),
    ("tools.reminders", "btn_reminders"),
    ("tools.clinic", "btn_clinic"),
    ("tools.locations", "btn_locations"),
    ("tools.nomenclatoare", "btn_nomenclatoare"),
    ("tools.appt", "btn_appt"),
    ("tools.wait", "btn_wait"),
    ("tools.tasks", "btn_tasks"),
    ("tools.claims", "btn_claims"),
    ("tools.lab_import", "btn_lab_import"),
    ("tools.dashboard", "btn_dashboard"),
    ("tools.labels", "btn_labels"),
    ("tools.icd10", "btn_icd10"),
    ("tools.update_app", "btn_update_app"),
    ("tools.db_cleanup", "btn_db_cleanup"),
    ("tools.recycle_bin", "btn_recycle_bin"),
]

# Templates
PRESCRIPTION_TEMPLATES = [
    {
        "name": "Reteta simpla",
        "body": (
            "RETETA\n"
            "Pacient: {nume_prenume}\n"
            "CNP: {cnp}\n"
            "Data nasterii: {data_nasterii}\n"
            "Telefon: {telefon}\n"
            "Data: {data}\n"
            "Medic: {medic}\n"
            "\n"
            "Medicamente:\n"
            "- \n"
            "\n"
            "Diagnostic: {diagnostic}\n"
            "Observatii: {observatii}\n"
        ),
    },
    {
        "name": "Reteta cronica",
        "body": (
            "RETETA CRONICA\n"
            "Pacient: {nume_prenume}\n"
            "CNP: {cnp}\n"
            "Data: {data}\n"
            "Medic: {medic}\n"
            "\n"
            "Medicamente cronice:\n"
            "- \n"
            "\n"
            "Observatii: {observatii}\n"
        ),
    },
]

NOMENCLATOR_DEFAULTS: Dict[str, List[Tuple[str, Optional[int], int]]] = {}

# Supabase sync (online/offline)
SUPABASE_URL = "https://bidwmnutexfuvznmiclp.supabase.co"
SUPABASE_ANON_KEY = "eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJpc3MiOiJzdXBhYmFzZSIsInJlZiI6ImJpZHdtbnV0ZXhmdXZ6bm1pY2xwIiwicm9sZSI6ImFub24iLCJpYXQiOjE3NzA0OTgwMDEsImV4cCI6MjA4NjA3NDAwMX0.qz8V3XPXLdOqVV-rle2wJsfhMzqViorNW2GQjdQROQE"
SUPABASE_AUTH_ENABLED = False
SUPABASE_AUTH_REQUIRED = False
SUPABASE_STORAGE_ENABLED = True
SUPABASE_STORAGE_BUCKET = "documents"
SUPABASE_STORAGE_PUBLIC = True
SYNC_INTERVAL_MIN = 10
AUTO_MAINTENANCE_INTERVAL_MIN = 180
# Query strategy for main list: avoid expensive full-window scans on large consult tables.
MAIN_LIST_QUERY_MODE = "latest_join"

SYNC_TABLES = [
    # parent tables
    {"table": "users", "fk": {}},
    {"table": "locations", "fk": {}},
    {"table": "pacienti_master", "fk": {}},
    {"table": "inventory_items", "fk": {}},
    {"table": "invoices", "fk": {"pacient_id": ("pacienti_master", "pacient_sync_id")}},
    # child tables
    {"table": "consulturi", "fk": {"pacient_id": ("pacienti_master", "pacient_sync_id")}},
    {"table": "patient_flow", "fk": {"pacient_id": ("pacienti_master", "pacient_sync_id")}},
    {"table": "medical_history", "fk": {"pacient_id": ("pacienti_master", "pacient_sync_id")}},
    {"table": "treatment_plans", "fk": {"pacient_id": ("pacienti_master", "pacient_sync_id")}},
    {"table": "prescriptions", "fk": {"pacient_id": ("pacienti_master", "pacient_sync_id")}},
    {"table": "medical_letters", "fk": {"pacient_id": ("pacienti_master", "pacient_sync_id")}},
    {"table": "documents", "fk": {"pacient_id": ("pacienti_master", "pacient_sync_id")}},
    {"table": "clinical_alerts", "fk": {"pacient_id": ("pacienti_master", "pacient_sync_id")}},
    {"table": "vaccinations", "fk": {"pacient_id": ("pacienti_master", "pacient_sync_id")}},
    {"table": "lab_orders", "fk": {"pacient_id": ("pacienti_master", "pacient_sync_id")}},
    {"table": "insurance_claims", "fk": {"pacient_id": ("pacienti_master", "pacient_sync_id"), "invoice_id": ("invoices", "invoice_sync_id")}},
    {"table": "inventory_lots", "fk": {"item_id": ("inventory_items", "item_sync_id")}},
    {"table": "inventory_movements", "fk": {"item_id": ("inventory_items", "item_sync_id"), "pacient_id": ("pacienti_master", "pacient_sync_id")}},
    {"table": "appointments", "fk": {"pacient_id": ("pacienti_master", "pacient_sync_id"), "location_id": ("locations", "location_sync_id")}},
    {"table": "waiting_list", "fk": {"pacient_id": ("pacienti_master", "pacient_sync_id"), "location_id": ("locations", "location_sync_id")}},
    {"table": "tasks", "fk": {}},
    {"table": "not_duplicates", "fk": {"a": ("pacienti_master", "a_sync_id"), "b": ("pacienti_master", "b_sync_id")}},
    {"table": "activity_log", "fk": {}},
]

DB_CLEANUP_SEGMENTS: List[Tuple[str, str, List[str]]] = [
    (
        "patients",
        "Date pacienti + consulturi",
        [
            "not_duplicates",
            "consulturi",
            "patient_flow",
            "medical_history",
            "treatment_plans",
            "prescriptions",
            "medical_letters",
            "documents",
            "clinical_alerts",
            "vaccinations",
            "lab_orders",
            "pacienti_master",
        ],
    ),
    (
        "financial",
        "Facturi si decontari",
        ["insurance_claims", "invoices"],
    ),
    (
        "scheduling",
        "Programari, asteptare, taskuri",
        ["appointments", "waiting_list", "tasks"],
    ),
    (
        "inventory",
        "Stocuri si miscari",
        ["inventory_movements", "inventory_lots", "inventory_items"],
    ),
    (
        "locations",
        "Sedii",
        ["locations"],
    ),
    (
        "logs",
        "Log activitate",
        ["activity_log"],
    ),
    (
        "icd10",
        "Catalog ICD-10 local",
        ["icd10_codes"],
    ),
]

RECYCLE_BIN_SNAPSHOTS_TABLE = "recycle_bin_snapshots"
RECYCLE_BIN_ITEMS_TABLE = "recycle_bin_items"
DB_SCHEMA_META_TABLE = "schema_meta"
DB_SCHEMA_VERSION_KEY = "schema_version"
DB_SCHEMA_VERSION_CURRENT = 7
DB_SCHEMA_MIGRATION_BACKUP_DIR = AUTOBACKUP_DIR / "migrations"
DB_SCHEMA_MIGRATION_BACKUP_DIR.mkdir(parents=True, exist_ok=True)
ENTITY_AUDIT_TABLE = "entity_audit_log"
_ENTITY_AUDIT_SCHEMA_READY = False
CONSULT_DRAFT_KEY_PREFIX = "consult_draft::"
CONSULT_DRAFT_AUTOSAVE_MS = 1200
SYNC_OUTBOX_TABLE = "sync_outbox"
SYNC_CONFLICT_RULE_KEY = "sync_conflict_rule"
SYNC_CONFLICT_RULE_DEFAULT = "latest_updated_at_wins"
AUTOBACKUP_RETENTION_DAYS = 30
SMS_BULK_CONFIRM_THRESHOLD_KEY = "sms_bulk_confirm_threshold"
SMS_BULK_CONFIRM_THRESHOLD_DEFAULT = 20
SMS_IMMEDIATE_RETRY_MAX_KEY = "sms_immediate_retry_max"
SMS_IMMEDIATE_RETRY_MAX_DEFAULT = 2
SMS_IMMEDIATE_RETRY_BASE_MS_KEY = "sms_immediate_retry_base_ms"
SMS_IMMEDIATE_RETRY_BASE_MS_DEFAULT = 700

LETTER_TEMPLATES = [
    {
        "name": "Scrisoare medicala",
        "body": (
            "SCRISOARE MEDICALA\n"
            "Pacient: {nume_prenume}\n"
            "CNP: {cnp}\n"
            "Data nasterii: {data_nasterii}\n"
            "Domiciliu: {domiciliu}\n"
            "Data: {data}\n"
            "Medic: {medic}\n"
            "\n"
            "Diagnostic: {diagnostic}\n"
            "Observatii: {observatii}\n"
        ),
    },
    {
        "name": "Adeverinta medicala",
        "body": (
            "ADEVERINTA MEDICALA\n"
            "Se adevereste ca {nume_prenume} (CNP {cnp})\n"
            "a fost consultat in data de {data}.\n"
            "\n"
            "Diagnostic: {diagnostic}\n"
            "Observatii: {observatii}\n"
            "\n"
            "Medic: {medic}\n"
        ),
    },
    {
        "name": "Bilet externare",
        "body": (
            "BILET DE EXTERNARE\n"
            "Pacient: {nume_prenume}\n"
            "CNP: {cnp}\n"
            "Data: {data}\n"
            "Medic: {medic}\n"
            "\n"
            "Diagnostic: {diagnostic}\n"
            "Observatii: {observatii}\n"
        ),
    },
]

# UI styles (CNP)
CNP_INVALID_STYLE = "QLineEdit { border: 2px solid #d32f2f; border-radius: 4px; }"
CNP_OK_STYLE = ""


# ============================================================
# FIELDS (Consult)
# ============================================================
# ĂŽn UI formularul din stĂ˘nga este "consult" curent pentru pacient.
CONSULT_FIELDS = [
    ("Data consultului (YYYY-MM-DD)", "data_consultului"),
    ("Medic", "medic"),
    ("Diagnostic principal (ICD-10)", "diagnostic_principal"),
    ("Diagnostice secundare (ICD-10)", "diagnostic_secundar"),
    ("Diagnostic liber", "diagnostic_liber"),
    ("Observatii", "observatii"),
    ("Status follow-up", "status_follow_up"),
    ("Data revenire control (YYYY-MM-DD HH:MM)", "data_revenire_control"),
    ("Interval (luni)", "interval_luni_revenire"),
    ("Recomandare fizio-kinetoterapie", "recomandare_fizio_kineto"),
    ("Status fizioterapie", "a_inceput_fizio"),
]

MASTER_FIELDS = [
    ("Nume si prenume*", "nume_prenume"),
    ("Domiciliu", "domiciliu"),
    ("CNP", "cnp"),
    ("Data nasterii (YYYY-MM-DD)", "data_nasterii"),
    ("Telefon", "telefon"),
    ("Email", "email"),
    ("SMS", "sms_opt_out"),
    ("Sex", "sex"),
    ("Varsta (ani)", "varsta"),
]

TEXTAREA_KEYS = {"observatii"}
DATE_KEYS = {"data_nasterii", "data_consultului", "data_revenire_control"}
INT_KEYS = {"interval_luni_revenire"}
CONSULT_BOOL_KEYS = {"recomandare_fizio_kineto", "a_inceput_fizio"}
CONSULT_NOMENCLATOR_TABLES = {}
CONSULT_NOMENCLATOR_KEYS = set(CONSULT_NOMENCLATOR_TABLES.keys())
CONSULT_COMBO_KEYS = {"status_follow_up"} | CONSULT_BOOL_KEYS | CONSULT_NOMENCLATOR_KEYS

# Tabelul principal afiČ™eazÄ MASTER + "ultimul consult" (denormalizat la query)
TABLE_COLS = [
    "alerta",
    "id",
    "nume_prenume",
    "cnp",
    "sex",
    "telefon",
    "email",
    "data_nasterii",
    "varsta",
    "domiciliu",
    "ultimul_consult",
    "ultim_diagnostic",
    "data_revenire_control",
    "status_follow_up",
]


# ============================================================
# Helpers (date / normalize / CNP)
# ============================================================
def validate_ymd_or_empty(s: Optional[str]) -> bool:
    """Valideaza data in format YYYY-MM-DD sau accepta valoare goala."""
    if not s:
        return True
    try:
        datetime.strptime(str(s).strip(), "%Y-%m-%d")
        return True
    except Exception:
        return False


def validate_ymd_hhmm_or_empty(s: Optional[str]) -> bool:
    """Valideaza YYYY-MM-DD sau YYYY-MM-DD HH:MM si accepta valoare goala."""
    if not s:
        return True
    t = str(s).strip()
    if not t:
        return True
    if validate_ymd_or_empty(t):
        return True
    if _parse_dt_any(t) is not None:
        return True
    m = re.match(r"^(\d{4}-\d{2}-\d{2})[ T]+(\d{1,2}):(\d{2})$", t)
    if not m:
        return False
    try:
        hh = int(m.group(2))
        mm = int(m.group(3))
    except Exception:
        return False
    return 0 <= hh <= 23 and 0 <= mm <= 59


def _validate_date_for_key(key: str, value: Optional[str]) -> bool:
    """Valideaza campurile de data in functie de cheie."""
    if key == "data_revenire_control":
        return validate_ymd_hhmm_or_empty(value)
    return validate_ymd_or_empty(value)


def validate_hhmm(s: Optional[str]) -> bool:
    """Valideaza ora in format HH:MM."""
    if not s:
        return False
    s = str(s).strip()
    return bool(re.match(r"^([01]\d|2[0-3]):([0-5]\d)$", s))


def parse_hhmm_list(s: Optional[str]) -> List[str]:
    """Parseaza lista de ore HH:MM separata prin virgula."""
    if not s:
        return []
    parts = [p.strip() for p in str(s).split(",")]
    out = []
    seen = set()
    for p in parts:
        if not p:
            continue
        if not validate_hhmm(p):
            return []
        if p not in seen:
            seen.add(p)
            out.append(p)
    return out


def _safe_parse_ymd(s: Optional[str]) -> Optional[date]:
    """Parseaza sigur o data (YYYY-MM-DD sau YYYY-MM-DD HH:MM) si returneaza None la valori invalide."""
    if not s:
        return None
    s = str(s).strip()
    if not s:
        return None
    try:
        return datetime.strptime(s, "%Y-%m-%d").date()
    except Exception:
        pass
    m = re.match(r"^(\d{4}-\d{2}-\d{2})", s)
    if m:
        try:
            return datetime.strptime(m.group(1), "%Y-%m-%d").date()
        except Exception:
            pass
    dt = _parse_dt_any(s)
    if dt is not None:
        return dt.date()
    return None


def _split_ymd_hhmm(value: Optional[str]) -> Tuple[str, str]:
    """Intoarce perechea (data YYYY-MM-DD, ora HH:MM) dintr-un text date-time."""
    raw = str(value or "").strip()
    if not raw:
        return "", ""
    dt = _parse_dt_any(raw)
    if dt is not None:
        return dt.strftime("%Y-%m-%d"), dt.strftime("%H:%M")
    m = re.match(r"^(\d{4}-\d{2}-\d{2})[ T]+(\d{1,2}):(\d{2})$", raw)
    if m:
        try:
            hh = int(m.group(2))
            mm = int(m.group(3))
            if 0 <= hh <= 23 and 0 <= mm <= 59:
                return m.group(1), f"{hh:02d}:{mm:02d}"
        except Exception:
            pass
    if validate_ymd_or_empty(raw):
        return raw, ""
    m = re.match(r"^(\d{4}-\d{2}-\d{2})", raw)
    if m:
        return m.group(1), ""
    return "", ""


def _consult_confirmation_slot(consult_payload: Optional[Dict[str, Any]]) -> Optional[Tuple[str, str]]:
    """Extrage data+ora pentru SMS confirmare consult; fara data_revenire_control nu trimitem SMS."""
    cp = dict(consult_payload or {})
    control_date, control_time = _split_ymd_hhmm(cp.get("data_revenire_control"))
    if not control_date:
        return None
    if not control_time:
        fallback_time = (cp.get("time") or cp.get("ora") or "").strip()
        if validate_hhmm(fallback_time):
            control_time = fallback_time
    if not validate_hhmm(control_time):
        control_time = "--:--"
    return control_date, control_time


def calc_age_ani(dob_ymd: Optional[str], ref: Optional[date] = None) -> Optional[int]:
    """Calculeaza varsta in ani pe baza datei de nastere."""
    d = _safe_parse_ymd(dob_ymd)
    if d is None:
        return None
    refd = ref or date.today()
    age = refd.year - d.year
    if (refd.month, refd.day) < (d.month, d.day):
        age -= 1
    if age < 0 or age > 130:
        return None
    return age


def _parse_dt_any(s: Optional[str]) -> Optional[datetime]:
    """Parseaza o valoare text in data/ora folosind mai multe formate acceptate."""
    if not s:
        return None
    s = str(s).strip()
    if not s:
        return None
    for fmt in ("%Y-%m-%d %H:%M", "%Y-%m-%d %H:%M:%S", "%Y-%m-%dT%H:%M", "%Y-%m-%dT%H:%M:%S"):
        try:
            return datetime.strptime(s, fmt)
        except Exception:
            continue
    return None


class _SafeDict(dict):
    def __missing__(self, key):
        """Returneaza placeholder gol cand lipseste o cheie din template."""
        return ""


def render_template_text(template_body: str, data: Dict[str, Any]) -> str:
    """Renderizeaza template text."""
    try:
        return (template_body or "").format_map(_SafeDict(data))
    except Exception:
        return template_body or ""


def append_shortcut_hint(widget: Optional[QWidget], hint: str):
    """Adauga shortcut hint."""
    if widget is None:
        return
    txt = (hint or "").strip()
    if not txt:
        return
    try:
        base = (widget.toolTip() or "").strip()
        suffix = f"Shortcut: {txt}"
        if suffix.lower() in base.lower():
            return
        widget.setToolTip(f"{base}\n{suffix}" if base else suffix)
    except Exception:
        pass


def _gen_code(n: int = 8) -> str:
    """Genereaza un cod alfanumeric aleator pentru identificatori temporari."""
    import random
    import string
    return "".join(random.choice(string.ascii_uppercase + string.digits) for _ in range(n))


def ensure_default_location():
    """Asigura default location."""
    conn = get_conn()
    cur = conn.cursor()
    cur.execute("SELECT id FROM locations ORDER BY id LIMIT 1")
    row = cur.fetchone()
    if not row:
        cur.execute("INSERT INTO locations(name, address, active) VALUES (?,?,?)", ("Sediu principal", "", 1))
        conn.commit()
        loc_id = cur.lastrowid
    else:
        loc_id = row[0]
    conn.close()
    if get_current_location_id() is None:
        set_current_location_id(int(loc_id))


def generate_qr_pixmap(text: str, size: int = 200) -> QPixmap:
    """Gestioneaza QR pixmap."""
    try:
        import qrcode
        from PIL.ImageQt import ImageQt
        img = qrcode.make(text or "")
        img = img.resize((size, size))
        qimg = ImageQt(img.convert("RGB"))
        return QPixmap.fromImage(qimg)
    except Exception:
        pix = QPixmap(size, size)
        pix.fill(QColor("#f5f5f5"))
        p = QPainter(pix)
        p.setPen(QColor("#333333"))
        p.drawRect(0, 0, size - 1, size - 1)
        p.drawText(QRect(10, 10, size - 20, size - 20), Qt.AlignmentFlag.AlignCenter, text or "")
        p.end()
        return pix


def encrypt_bytes(data: bytes, password: str) -> bytes:
    """Cripteaza un bloc de date binare folosind parola primita."""
    try:
        from cryptography.fernet import Fernet
        import base64
        import hashlib
        key = base64.urlsafe_b64encode(hashlib.sha256(password.encode("utf-8")).digest())
        return Fernet(key).encrypt(data)
    except Exception as e:
        raise RuntimeError("Cryptography not available") from e


def normalize_cnp_digits(cnp: Optional[str]) -> str:
    """Normalizeaza CNP digits."""
    return re.sub(r"\D+", "", str(cnp or ""))


def cnp_checksum_valid(digits: Optional[str]) -> bool:
    """Gestioneaza checksum valid."""
    if not digits or not re.fullmatch(r"\d{13}", str(digits)):
        return False
    s = str(digits)
    weights = "279146358279"
    total = 0
    for i in range(12):
        total += int(s[i]) * int(weights[i])
    chk = total % 11
    if chk == 10:
        chk = 1
    return chk == int(s[12])


def cnp_is_valid_13(cnp: Optional[str]) -> bool:
    """Gestioneaza is valid 13."""
    digits = normalize_cnp_digits(cnp)
    return cnp_checksum_valid(digits)


def cnp_extract_birthdate_and_sex(cnp: Optional[str]) -> Tuple[Optional[str], Optional[str]]:
    """
    Din CNP:
      - data nasterii -> YYYY-MM-DD
      - sex -> Masculin / Feminin

    Reguli sex (prima cifra):
      Masculin: 1,5,7
      Feminin: 2,6,8

    Secol:
      1-2 => 1900-1999
      5-6 => 2000-2099
      7-8 => rezidenti straini (folosim 1900-1999 ca fallback, dar e variabil; pastram doar sexul, iar data se calculeaza tot cu 19xx/20xx in functie de practica)
    """
    if not cnp:
        return None, None
    s = normalize_cnp_digits(cnp)
    if len(s) != 13:
        return None, None

    first = s[0]
    yy = s[1:3]
    mm = s[3:5]
    dd = s[5:7]

    sex = None
    if first in {"1", "5", "7"}:
        sex = "Masculin"
    elif first in {"2", "6", "8"}:
        sex = "Feminin"

    century = None
    if first in {"1", "2", "7", "8"}:
        century = 1900
    elif first in {"5", "6"}:
        century = 2000

    dob = None
    try:
        if century is not None:
            y = century + int(yy)
            m = int(mm)
            d = int(dd)
            dob = date(y, m, d).strftime("%Y-%m-%d")
    except Exception:
        dob = None

    return dob, sex


def sex_from_cnp(cnp: Optional[str]) -> Optional[str]:
    """Gestioneaza from CNP."""
    digits = normalize_cnp_digits(cnp)
    if not cnp_checksum_valid(digits):
        return None
    _, sex = cnp_extract_birthdate_and_sex(digits)
    return sex


def birthdate_from_cnp(cnp: Optional[str]) -> Optional[str]:
    """Gestioneaza from CNP."""
    digits = normalize_cnp_digits(cnp)
    if not cnp_checksum_valid(digits):
        return None
    dob, _ = cnp_extract_birthdate_and_sex(digits)
    return dob


def normalize_ro_mobile_phone(phone: Optional[str]) -> Optional[str]:
    """
    Pentru numere de mobil RO: daca lipseste 0 la inceput, il adauga.
    Exemple:
      - 7xxxxxxxx  -> 07xxxxxxxx
      - +407xxxxxx -> 07xxxxxxxx
      - 00407xxxxx -> 07xxxxxxxx
    """
    if phone is None:
        return None
    raw = (phone or "").strip()
    if not raw:
        return None
    digits = re.sub(r"\D+", "", raw)
    if not digits:
        return raw
    if digits.startswith("0040"):
        digits = digits[4:]
    elif digits.startswith("40"):
        digits = digits[2:]
    if len(digits) == 9 and digits.startswith("7"):
        return "0" + digits
    return raw


def is_valid_ro_mobile_phone(phone: Optional[str]) -> bool:
    """Verifica daca valid ro mobile phone."""
    normalized = normalize_ro_mobile_phone(phone)
    if not normalized:
        return False
    digits = re.sub(r"\D+", "", str(normalized))
    return bool(re.fullmatch(r"07\d{8}", digits))


_RO_DIACRITICS_MAP = {
    ord("\u0103"): "a",  # a cu breva (ă)
    ord("\u00E2"): "a",  # a circumflex (â)
    ord("\u00EE"): "i",  # i circumflex (î)
    ord("\u0219"): "s",  # s cu virgula (ș)
    ord("\u015F"): "s",  # s cu sedila (ş, forma veche)
    ord("\u021B"): "t",  # t cu virgula (ț)
    ord("\u0163"): "t",  # t cu sedila (ţ, forma veche)
    ord("\u0102"): "A",
    ord("\u00C2"): "A",
    ord("\u00CE"): "I",
    ord("\u0218"): "S",
    ord("\u015E"): "S",
    ord("\u021A"): "T",
    ord("\u0162"): "T",
}


def strip_ro_diacritics(s: Optional[str]) -> Optional[str]:
    """Gestioneaza ro diacritics."""
    if s is None:
        return None
    return str(s).translate(_RO_DIACRITICS_MAP)


def _repair_common_mojibake(s: str) -> str:
    """Gestioneaza common mojibake."""
    txt = str(s or "")
    if not txt:
        return txt
    if not any(ch in txt for ch in ("Ă", "Ă‚", "Ă…", "Ă„", "Ă‹", "Ă˘", "ďż˝")):
        return txt

    current = txt
    for _ in range(2):
        repaired = current
        for enc in ("latin-1", "cp1252"):
            try:
                cand = current.encode(enc).decode("utf-8")
            except Exception:
                continue
            bad_old = sum(current.count(m) for m in ("Ă", "Ă‚", "Ă…", "Ă„", "Ă‹", "Ă˘", "ďż˝"))
            bad_new = sum(cand.count(m) for m in ("Ă", "Ă‚", "Ă…", "Ă„", "Ă‹", "Ă˘", "ďż˝"))
            if bad_new < bad_old:
                repaired = cand
                break
        if repaired == current:
            break
        current = repaired
    return current


def to_ascii_text(s: Optional[str]) -> Optional[str]:
    """Converteaza ascii text."""
    if s is None:
        return None
    txt = _repair_common_mojibake(str(s))
    txt = txt.translate(_RO_DIACRITICS_MAP)
    txt = unicodedata.normalize("NFKD", txt)
    txt = "".join(ch for ch in txt if not unicodedata.combining(ch))
    txt = txt.encode("ascii", "ignore").decode("ascii")
    return txt


def force_ascii_ui_texts(root_widget: Optional[QWidget]) -> None:
    """Gestioneaza ascii interfata texts."""
    if root_widget is None:
        return
    widgets: List[QWidget] = [root_widget]
    try:
        widgets.extend(root_widget.findChildren(QWidget))
    except Exception:
        pass

    def _fix(getter_name: str, setter_name: str, obj):
        """Ajusteaza textul pentru afisare coerenta in UI (helper intern pentru `force_ascii_ui_texts`)."""
        getter = getattr(obj, getter_name, None)
        setter = getattr(obj, setter_name, None)
        if not callable(getter) or not callable(setter):
            return
        try:
            value = getter()
            if isinstance(value, str) and value:
                fixed = to_ascii_text(value) or ""
                if fixed != value:
                    setter(fixed)
        except Exception:
            return

    for w in widgets:
        _fix("windowTitle", "setWindowTitle", w)
        _fix("toolTip", "setToolTip", w)
        _fix("statusTip", "setStatusTip", w)
        _fix("whatsThis", "setWhatsThis", w)
        _fix("placeholderText", "setPlaceholderText", w)
        _fix("text", "setText", w)

        if isinstance(w, QComboBox):
            try:
                for i in range(w.count()):
                    t = w.itemText(i)
                    f = to_ascii_text(t) or ""
                    if f != t:
                        w.setItemText(i, f)
            except Exception:
                pass


def _default_icon_for_button_text(text: str):
    """Gestioneaza icon for button text."""
    t = _norm(to_ascii_text(text) or text or "")
    if not t:
        return None
    if any(k in t for k in ["sterge", "delete", "remove", "trash"]):
        return QStyle.StandardPixmap.SP_TrashIcon
    if any(k in t for k in ["salveaza", "save", "export"]):
        return QStyle.StandardPixmap.SP_DialogSaveButton
    if any(k in t for k in ["import", "deschide", "open", "alege", "browse", "restore"]):
        return QStyle.StandardPixmap.SP_DialogOpenButton
    if any(k in t for k in ["adauga", "create", "nou", "new"]):
        return QStyle.StandardPixmap.SP_FileDialogNewFolder
    if any(k in t for k in ["editeaza", "update", "aplica", "filtreaza", "genereaza", "seteaza"]):
        return QStyle.StandardPixmap.SP_DialogApplyButton
    if any(k in t for k in ["refresh", "actualizeaza", "reload", "sync", "recalculeaza"]):
        return QStyle.StandardPixmap.SP_BrowserReload
    if any(k in t for k in ["reset", "reseteaza", "curata", "clear"]):
        return QStyle.StandardPixmap.SP_DialogResetButton
    if any(k in t for k in ["inchide", "renunta", "cancel", "deconectare", "logout"]):
        return QStyle.StandardPixmap.SP_DialogCancelButton
    if any(k in t for k in ["cauta", "search", "avansat"]):
        return QStyle.StandardPixmap.SP_FileDialogContentsView
    if any(k in t for k in ["inapoi", "anterioara", "prev"]):
        return QStyle.StandardPixmap.SP_ArrowBack
    if any(k in t for k in ["urmatoare", "next", "inainte"]):
        return QStyle.StandardPixmap.SP_ArrowForward
    return None


def apply_default_button_icons(root_widget: Optional[QWidget]) -> None:
    """Aplica default button icons."""
    if root_widget is None:
        return
    widgets: List[QWidget] = [root_widget]
    try:
        widgets.extend(root_widget.findChildren(QWidget))
    except Exception:
        pass
    for w in widgets:
        if not isinstance(w, QPushButton):
            continue
        try:
            if not w.icon().isNull():
                continue
            sp = _default_icon_for_button_text(w.text() or "")
            if sp is not None:
                apply_std_icon(w, sp)
        except Exception:
            pass


def _combo_first_item_empty(cb: QComboBox) -> bool:
    """Gestioneaza first item empty."""
    try:
        if cb.count() <= 0:
            return False
        return not (cb.itemText(0) or "").strip()
    except Exception:
        return False


def _set_combo_empty_visual_state(cb: QComboBox) -> None:
    """Seteaza combo empty visual state."""
    try:
        idx = cb.currentIndex()
        txt = (cb.currentText() or "").strip()
        is_empty = (idx < 0) or (_combo_first_item_empty(cb) and idx == 0) or (not txt)
        cb.setProperty("empty", bool(is_empty))
        style = cb.style()
        if style is not None:
            style.unpolish(cb)
            style.polish(cb)
    except Exception:
        pass


def style_dropdown_combobox(cb: QComboBox) -> None:
    """Gestioneaza dropdown combobox."""
    try:
        if not bool(cb.property("_dropdown_patched")):
            cb.setProperty("_dropdown_patched", True)
            if _combo_first_item_empty(cb):
                try:
                    cb.setPlaceholderText("Selecteaza")
                except Exception:
                    pass
                if cb.currentIndex() == 0:
                    cb.setCurrentIndex(-1)

            def _on_index_changed(_idx: int, combo_ref=cb):
                """Gestioneaza evenimentul index changed ca helper intern in `style_dropdown_combobox`."""
                try:
                    if _combo_first_item_empty(combo_ref) and combo_ref.currentIndex() == 0:
                        combo_ref.blockSignals(True)
                        combo_ref.setCurrentIndex(-1)
                        combo_ref.blockSignals(False)
                except Exception:
                    pass
                _set_combo_empty_visual_state(combo_ref)

            cb.currentIndexChanged.connect(_on_index_changed)

        _set_combo_empty_visual_state(cb)
    except Exception:
        pass


def apply_global_dropdown_style(root_widget: Optional[QWidget]) -> None:
    """Aplica global dropdown style."""
    if root_widget is None:
        return
    widgets: List[QWidget] = [root_widget]
    try:
        widgets.extend(root_widget.findChildren(QWidget))
    except Exception:
        pass
    for w in widgets:
        if isinstance(w, QComboBox):
            style_dropdown_combobox(w)


def _handle_combobox_wheel_scroll(cb: QComboBox, event: QEvent) -> bool:
    """Gestioneaza combobox wheel scroll."""
    try:
        if cb is None or event is None:
            return False
        if not cb.isEnabled() or cb.count() <= 0:
            return False
        view = cb.view()
        if view is not None and view.isVisible():
            return False
        delta_y = int(event.angleDelta().y())
        if delta_y == 0:
            return False

        step = -1 if delta_y > 0 else 1
        idx = int(cb.currentIndex())
        if idx < 0:
            target = 0
        else:
            target = idx + step
        target = max(0, min(cb.count() - 1, target))
        if target != idx:
            cb.setCurrentIndex(target)
        event.accept()
        return True
    except Exception:
        return False


def _fit_messagebox_title(box: QMessageBox) -> None:
    """Gestioneaza messagebox title."""
    if bool(box.property("_title_fit_done")):
        return
    try:
        title = (box.windowTitle() or "").strip()
        text = (box.text() or "").splitlines()[0].strip() if (box.text() or "") else ""
        fm = box.fontMetrics()
        title_px = fm.horizontalAdvance(title) if title else 0
        text_px = fm.horizontalAdvance(text[:120]) if text else 0
        target_w = max(520, title_px + 220, text_px + 180)
        target_w = min(780, target_w)
        box.setMinimumWidth(target_w)
        if box.width() < target_w:
            box.resize(target_w, box.height())
        box.setProperty("_title_fit_done", True)
    except Exception:
        pass


class _UiPolishEventFilter(QObject):
    def eventFilter(self, obj, event):
        """Intercepteaza evenimente UI pentru ajustari vizuale globale."""
        try:
            if isinstance(obj, QComboBox) and event.type() == QEvent.Type.Wheel:
                if _handle_combobox_wheel_scroll(obj, event):
                    return True
            if isinstance(obj, QMessageBox) and event.type() in (QEvent.Type.Show, QEvent.Type.Polish):
                _fit_messagebox_title(obj)
            if isinstance(obj, QWidget) and event.type() in (QEvent.Type.Show, QEvent.Type.Polish):
                apply_default_button_icons(obj)
                apply_global_dropdown_style(obj)
        except Exception:
            pass
        return False

        if isinstance(w, QTableWidget):
            try:
                for i in range(w.columnCount()):
                    it = w.horizontalHeaderItem(i)
                    if it:
                        t = it.text() or ""
                        f = to_ascii_text(t) or ""
                        if f != t:
                            it.setText(f)
                for i in range(w.rowCount()):
                    it = w.verticalHeaderItem(i)
                    if it:
                        t = it.text() or ""
                        f = to_ascii_text(t) or ""
                        if f != t:
                            it.setText(f)
            except Exception:
                pass


def _sqlite_text_to_ascii(raw: bytes) -> str:
    """Gestioneaza text to ascii."""
    try:
        return to_ascii_text(raw.decode("utf-8")) or ""
    except Exception:
        try:
            return to_ascii_text(raw.decode("cp1250")) or ""
        except Exception:
            return to_ascii_text(raw.decode("latin-1", errors="ignore")) or ""


def normalize_payload_ascii(payload: Optional[dict]) -> dict:
    """Normalizeaza payload ascii."""
    out: Dict[str, Any] = {}
    for k, v in (payload or {}).items():
        if isinstance(v, str):
            out[k] = to_ascii_text(v)
        else:
            out[k] = v
    return out


def _update_row(cur, table: str, id_col: str, id_val, updates: dict):
    """Actualizeaza row."""
    if not updates:
        return
    cols = list(updates.keys())
    sets = ", ".join([f"{c}=?" for c in cols])
    values = [updates[c] for c in cols] + [id_val]
    cur.execute(f"UPDATE {table} SET {sets} WHERE {id_col}=?", values)


def remove_diacritics_in_db():
    """Elimina diacritics in baza de date."""
    conn = get_conn()
    cur = conn.cursor()

    def _existing_cols(table: str) -> set:
        """Gestioneaza cols ca helper intern in `remove_diacritics_in_db`."""
        cur.execute(f"PRAGMA table_info({table})")
        return {row[1] for row in cur.fetchall()}

    master_cols = ["nume_prenume", "domiciliu", "sex"]
    master_cols = [c for c in master_cols if c in _existing_cols("pacienti_master")]
    if master_cols:
        cur.execute(f"SELECT id, {', '.join(master_cols)} FROM pacienti_master")
        for r in cur.fetchall():
            updates = {}
            for c in master_cols:
                v = r[c]
                if v is None:
                    continue
                nv = strip_ro_diacritics(v)
                if nv != v:
                    updates[c] = nv
            _update_row(cur, "pacienti_master", "id", r["id"], updates)

    consult_cols = [
        "medic", "diagnostic_principal", "diagnostic_secundar", "diagnostic_liber", "observatii",
        "status_follow_up",
        "recomandare_fizio_kineto", "a_inceput_fizio",
    ]
    consult_cols = [c for c in consult_cols if c in _existing_cols("consulturi")]
    if consult_cols:
        cur.execute(f"SELECT id, {', '.join(consult_cols)} FROM consulturi")
        for r in cur.fetchall():
            updates = {}
            for c in consult_cols:
                v = r[c]
                if v is None:
                    continue
                nv = strip_ro_diacritics(v)
                if nv != v:
                    updates[c] = nv
            _update_row(cur, "consulturi", "id", r["id"], updates)

    conn.commit()
    conn.close()


def normalize_master_from_cnp(payload: dict) -> dict:
    """
    Daca CNP e valid (13 cifre), completeaza automat:
      - data_nasterii (daca lipseste sau e invalida)
      - sex (daca lipseste)
      - varsta (calculata din data_nasterii)
    """
    p = dict(payload or {})
    cnp = (p.get("cnp") or "").strip()
    digits = normalize_cnp_digits(cnp)
    if len(digits) == 13 and cnp_checksum_valid(digits):
        p["cnp"] = digits
        cnp = digits
    elif not cnp:
        p["cnp"] = None
    if cnp_is_valid_13(cnp):
        dob, sex = cnp_extract_birthdate_and_sex(cnp)
        if dob and (not p.get("data_nasterii") or not validate_ymd_or_empty(p.get("data_nasterii"))):
            p["data_nasterii"] = dob
        if sex and not p.get("sex"):
            p["sex"] = sex

    # calculeazÄ vĂ˘rsta din data naČ™terii
    age = calc_age_ani(p.get("data_nasterii"))
    p["varsta"] = age
    p["telefon"] = normalize_ro_mobile_phone(p.get("telefon"))
    p["sms_opt_out"] = _to_int_flag(p.get("sms_opt_out"))
    return normalize_payload_ascii(p)


def _pdf_wrap_lines(text: str, max_chars: int = 95) -> List[str]:
    """Gestioneaza wrap lines."""
    t = (text or "").strip()
    if not t:
        return []
    out: List[str] = []
    for para in t.splitlines():
        para = para.rstrip()
        if not para.strip():
            out.append("")
            continue
        out.extend(textwrap.wrap(para, width=max_chars, break_long_words=False, break_on_hyphens=False))
    return out


def control_status(date_str: Optional[str], days_ahead: int = 7) -> str:
    """
    Returneaza:
      - "today" daca e azi
      - "soon" daca e in urmatoarele N zile (excluzand azi)
      - "" altfel
    """
    d = _safe_parse_ymd(date_str)
    if d is None:
        return ""
    today = date.today()
    end = today + timedelta(days=days_ahead)
    if d == today:
        return "today"
    if today < d <= end:
        return "soon"
    return ""


def _norm(s: str) -> str:
    """Normalizeaza textul pentru comparatii fara diferente de formatare."""
    s = str(s).strip().lower()
    s = unicodedata.normalize("NFKD", s)
    s = "".join(ch for ch in s if not unicodedata.combining(ch))
    s = re.sub(r"[^a-z0-9]+", " ", s)
    s = re.sub(r"\s+", " ", s).strip()
    return s


def log_error(message: str, exc: Optional[BaseException] = None, tb=None):
    """Inregistreaza eroarea in jurnalul aplicatiei, inclusiv traceback cand este disponibil."""
    try:
        ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        lines = [f"[{ts}] {message}"]
        if exc is not None:
            lines.append(f"Exception: {repr(exc)}")
        if tb is not None:
            lines.append("Traceback:")
            lines.extend(traceback.format_tb(tb))
        elif exc is not None:
            lines.extend(traceback.format_exception(type(exc), exc, exc.__traceback__))
        lines.append("")
        ERROR_LOG_PATH.parent.mkdir(parents=True, exist_ok=True)
        with open(ERROR_LOG_PATH, "a", encoding="utf-8") as f:
            f.write("".join(lines))
    except Exception:
        pass


def _install_error_logging():
    """Gestioneaza error logging."""
    def _sys_hook(exc_type, exc, tb):
        """Gestioneaza hook ca helper intern in `_install_error_logging`."""
        log_error("Unhandled exception", exc, tb)
        try:
            sys.__excepthook__(exc_type, exc, tb)
        except Exception:
            pass

    sys.excepthook = _sys_hook

    def _thread_hook(args):
        """Gestioneaza hook ca helper intern in `_install_error_logging`."""
        log_error(f"Thread exception in {getattr(args, 'thread', None)}", args.exc_value, args.exc_traceback)

    try:
        threading.excepthook = _thread_hook  # type: ignore
    except Exception:
        pass


_ICD10_CACHE: List[str] = []
_ICD10_CACHE_TS: float = 0.0
_ICD10_SEARCH_CACHE: List[Tuple[str, str]] = []
_ICD10_SEARCH_CACHE_TS: float = 0.0

RO_LOCALITIES_ADMIN1_URL = "https://download.geonames.org/export/dump/admin1CodesASCII.txt"
RO_LOCALITIES_ZIP_URL = "https://download.geonames.org/export/dump/RO.zip"
RO_LOCALITIES_TABLE = "ro_localities"
RO_LOCALITIES_MIN_ROWS = 12000

RO_LOCALITIES_FALLBACK: Dict[str, List[str]] = {
    "Alba": ["Alba Iulia"],
    "Arad": ["Arad"],
    "Arges": ["Pitesti"],
    "Bacau": ["Bacau"],
    "Bihor": ["Oradea"],
    "Bistrita-Nasaud": ["Bistrita"],
    "Botosani": ["Botosani"],
    "Braila": ["Braila"],
    "Brasov": ["Brasov"],
    "Bucuresti": ["Bucuresti"],
    "Buzau": ["Buzau"],
    "Calarasi": ["Calarasi"],
    "Caras-Severin": ["Resita"],
    "Cluj": ["Cluj-Napoca"],
    "Constanta": ["Constanta"],
    "Covasna": ["Sfantu Gheorghe"],
    "Dambovita": ["Targoviste"],
    "Dolj": ["Craiova"],
    "Galati": ["Galati"],
    "Giurgiu": ["Giurgiu"],
    "Gorj": ["Targu Jiu"],
    "Harghita": ["Miercurea Ciuc"],
    "Hunedoara": ["Deva"],
    "Ialomita": ["Slobozia"],
    "Iasi": ["Iasi"],
    "Ilfov": ["Buftea"],
    "Maramures": ["Baia Mare"],
    "Mehedinti": ["Drobeta-Turnu Severin"],
    "Mures": ["Targu Mures"],
    "Neamt": ["Piatra Neamt"],
    "Olt": ["Slatina"],
    "Prahova": ["Ploiesti"],
    "Salaj": ["Zalau"],
    "Satu Mare": ["Satu Mare"],
    "Sibiu": ["Sibiu"],
    "Suceava": ["Suceava"],
    "Teleorman": ["Alexandria"],
    "Timis": ["Timisoara"],
    "Tulcea": ["Tulcea"],
    "Valcea": ["Ramnicu Valcea"],
    "Vaslui": ["Vaslui"],
    "Vrancea": ["Focsani"],
}

RO_COUNTY_SEATS: Dict[str, str] = {
    (to_ascii_text(k) or k).strip(): (to_ascii_text(v[0]) or v[0]).strip()
    for k, v in RO_LOCALITIES_FALLBACK.items()
    if v and (to_ascii_text(v[0]) or v[0]).strip()
}


def _clean_county_name(county: Optional[str]) -> str:
    """Gestioneaza county name."""
    txt = (to_ascii_text(county) or county or "").strip()
    if not txt:
        return ""
    txt = re.sub(r"\s+county\s*$", "", txt, flags=re.IGNORECASE).strip()
    txt = re.sub(r"\s+", " ", txt).strip()
    return txt


def get_ro_county_seat(county: str) -> str:
    """Returneaza ro county seat."""
    c = _clean_county_name(county)
    if not c:
        return ""
    return (RO_COUNTY_SEATS.get(c) or "").strip()


def _ensure_ro_localities_table() -> None:
    """Asigura ro localities table."""
    conn = get_conn()
    cur = conn.cursor()
    cur.execute(
        f"""
        CREATE TABLE IF NOT EXISTS {RO_LOCALITIES_TABLE} (
            county TEXT NOT NULL,
            locality TEXT NOT NULL,
            search TEXT NOT NULL,
            PRIMARY KEY (county, locality)
        )
        """
    )
    cur.execute(f"CREATE INDEX IF NOT EXISTS idx_{RO_LOCALITIES_TABLE}_county ON {RO_LOCALITIES_TABLE}(county)")
    cur.execute(f"CREATE INDEX IF NOT EXISTS idx_{RO_LOCALITIES_TABLE}_search ON {RO_LOCALITIES_TABLE}(search)")
    conn.commit()
    conn.close()


def _seed_ro_localities_fallback() -> int:
    """Gestioneaza ro localities fallback."""
    _ensure_ro_localities_table()
    conn = get_conn()
    cur = conn.cursor()
    cur.execute(f"SELECT COUNT(*) FROM {RO_LOCALITIES_TABLE}")
    existing = int(cur.fetchone()[0] or 0)
    if existing > 0:
        conn.close()
        return existing
    rows: List[Tuple[str, str, str]] = []
    for county, localities in sorted(RO_LOCALITIES_FALLBACK.items()):
        county_txt = (to_ascii_text(county) or county).strip()
        for loc in localities:
            locality_txt = (to_ascii_text(loc) or loc).strip()
            if not county_txt or not locality_txt:
                continue
            rows.append((county_txt, locality_txt, _norm(locality_txt)))
    if rows:
        cur.executemany(
            f"INSERT OR REPLACE INTO {RO_LOCALITIES_TABLE}(county, locality, search) VALUES (?,?,?)",
            rows,
        )
    conn.commit()
    conn.close()
    return len(rows)


def _import_ro_localities_from_bundle(progress_cb=None, cancelled_cb=None) -> int:
    """Importa ro localities from bundle."""
    def pg(p: int, m: str = ""):
        """Actualizeaza progresul operatiei in curs (helper intern pentru `_import_ro_localities_from_bundle`)."""
        if progress_cb:
            try:
                progress_cb(int(max(0, min(100, p))), m)
            except Exception:
                pass

    def is_cancelled() -> bool:
        """Verifica daca cancelled ca helper intern in `_import_ro_localities_from_bundle`."""
        return bool(cancelled_cb and cancelled_cb())

    bundle = next((p for p in RO_LOCALITIES_BUNDLE_PATHS if p.exists() and p.is_file()), None)
    if bundle is None:
        raise RuntimeError("Fisierul local de localitati nu exista in pachet.")

    pg(10, "Incarc localitatile offline...")
    opener = gzip.open if bundle.suffix.lower() == ".gz" else open
    rows: List[Tuple[str, str, str]] = []
    with opener(bundle, "rt", encoding="utf-8", newline="") as fh:
        reader = csv.reader(fh)
        header_checked = False
        for idx, rec in enumerate(reader, start=1):
            if is_cancelled():
                raise RuntimeError("Import localitati anulat.")
            if not rec:
                continue
            if not header_checked:
                header_checked = True
                h0 = _norm(rec[0]) if len(rec) > 0 else ""
                h1 = _norm(rec[1]) if len(rec) > 1 else ""
                if h0 == "county" and h1 == "locality":
                    continue
            county = _clean_county_name(rec[0] if len(rec) > 0 else "")
            locality = (to_ascii_text(rec[1]) or (rec[1] if len(rec) > 1 else "") or "").strip()
            if not county or not locality:
                continue
            rows.append((county, locality, _norm(locality)))
            if idx % 5000 == 0:
                pg(10 + min(75, int(idx / 1200)), f"Incarc localitati offline... {idx}")

    if len(rows) < RO_LOCALITIES_MIN_ROWS:
        raise RuntimeError(f"Fisier offline incomplet: {len(rows)} localitati.")

    pg(90, "Salvez localitatile offline in baza locala...")
    _ensure_ro_localities_table()
    conn = get_conn()
    cur = conn.cursor()
    cur.execute(f"DELETE FROM {RO_LOCALITIES_TABLE}")
    cur.executemany(
        f"INSERT OR REPLACE INTO {RO_LOCALITIES_TABLE}(county, locality, search) VALUES (?,?,?)",
        rows,
    )
    conn.commit()
    conn.close()
    pg(100, f"Localitati offline actualizate: {len(rows)}")
    return len(rows)


def _download_url_bytes(url: str, timeout: int = 45) -> bytes:
    """Gestioneaza url bytes."""
    req = urllib.request.Request(url, method="GET")
    req.add_header("User-Agent", "PacientiApp/1.3")
    with urllib.request.urlopen(req, timeout=max(10, int(timeout))) as resp:
        return resp.read()


def _parse_ro_admin1_map(raw_text: str) -> Dict[str, str]:
    """Parseaza ro admin1 map."""
    out: Dict[str, str] = {}
    for ln in (raw_text or "").splitlines():
        line = ln.strip()
        if not line or line.startswith("#"):
            continue
        parts = line.split("\t")
        if len(parts) < 2:
            continue
        code = (parts[0] or "").strip()
        name = (parts[1] or "").strip()
        if not code.startswith("RO."):
            continue
        admin1 = code.split(".", 1)[1].strip()
        county = _clean_county_name(name)
        if admin1 and county:
            out[admin1] = county
    return out


def _import_ro_localities_from_geonames(progress_cb=None, cancelled_cb=None) -> int:
    """Importa ro localities from geonames."""
    def pg(p: int, m: str = ""):
        """Actualizeaza progresul operatiei in curs (helper intern pentru `_import_ro_localities_from_geonames`)."""
        if progress_cb:
            try:
                progress_cb(int(max(0, min(100, p))), m)
            except Exception:
                pass

    def is_cancelled() -> bool:
        """Verifica daca cancelled ca helper intern in `_import_ro_localities_from_geonames`."""
        return bool(cancelled_cb and cancelled_cb())

    pg(5, "Descarc judetele...")
    admin_raw = _download_url_bytes(RO_LOCALITIES_ADMIN1_URL, timeout=45)
    admin_map = _parse_ro_admin1_map(admin_raw.decode("utf-8", errors="ignore"))
    if not admin_map:
        raise RuntimeError("Nu am putut citi judetele din GeoNames.")
    if is_cancelled():
        raise RuntimeError("Import localitati anulat.")

    pg(20, "Descarc localitatile din Romania...")
    ro_zip = _download_url_bytes(RO_LOCALITIES_ZIP_URL, timeout=90)
    if is_cancelled():
        raise RuntimeError("Import localitati anulat.")

    county_to_localities: Dict[str, set] = {}
    pg(35, "Procesez fisierul de localitati...")
    with zipfile.ZipFile(io.BytesIO(ro_zip)) as zf:
        members = [n for n in zf.namelist() if n.lower().endswith(".txt")]
        if not members:
            raise RuntimeError("Arhiva GeoNames nu contine fisierul de localitati.")
        member_name = ""
        for n in members:
            if n.lower().endswith("ro.txt"):
                member_name = n
                break
        if not member_name:
            candidate = [n for n in members if "readme" not in n.lower()]
            member_name = candidate[0] if candidate else members[0]
        with zf.open(member_name, "r") as fh:
            for idx, raw_line in enumerate(fh, start=1):
                if is_cancelled():
                    raise RuntimeError("Import localitati anulat.")
                try:
                    line = raw_line.decode("utf-8", errors="ignore").rstrip("\n\r")
                except Exception:
                    continue
                if not line:
                    continue
                cols = line.split("\t")
                if len(cols) < 11:
                    continue
                if (cols[6] or "").strip() != "P":
                    continue
                loc_name = (to_ascii_text(cols[1]) or cols[1] or "").strip()
                admin1 = (cols[10] or "").strip()
                county_name = (to_ascii_text(admin_map.get(admin1, "")) or "").strip()
                if not loc_name or not county_name:
                    continue
                county_to_localities.setdefault(county_name, set()).add(loc_name)
                if idx % 25000 == 0:
                    pg(35 + min(50, int(idx / 25000)), f"Procesez localitati... {idx}")

    rows: List[Tuple[str, str, str]] = []
    for county_name, loc_set in county_to_localities.items():
        for loc_name in sorted(loc_set):
            rows.append((county_name, loc_name, _norm(loc_name)))
    if not rows:
        raise RuntimeError("Nu au fost gasite localitati valide in import.")

    pg(90, "Salvez localitatile in baza locala...")
    _ensure_ro_localities_table()
    conn = get_conn()
    cur = conn.cursor()
    cur.execute(f"DELETE FROM {RO_LOCALITIES_TABLE}")
    cur.executemany(
        f"INSERT OR REPLACE INTO {RO_LOCALITIES_TABLE}(county, locality, search) VALUES (?,?,?)",
        rows,
    )
    conn.commit()
    conn.close()
    pg(100, f"Localitati actualizate: {len(rows)}")
    return len(rows)


def ensure_ro_localities_dataset(
    progress_cb=None,
    cancelled_cb=None,
    force_refresh: bool = False,
    allow_fallback: bool = True,
) -> int:
    """Asigura ro localities dataset."""
    _ensure_ro_localities_table()
    conn = get_conn()
    cur = conn.cursor()
    cur.execute(f"SELECT COUNT(*) FROM {RO_LOCALITIES_TABLE}")
    count = int(cur.fetchone()[0] or 0)
    conn.close()
    if (not force_refresh) and count >= RO_LOCALITIES_MIN_ROWS:
        return count

    if not force_refresh:
        try:
            return _import_ro_localities_from_bundle(progress_cb=progress_cb, cancelled_cb=cancelled_cb)
        except Exception:
            pass

    try:
        return _import_ro_localities_from_geonames(progress_cb=progress_cb, cancelled_cb=cancelled_cb)
    except Exception:
        if allow_fallback:
            return _seed_ro_localities_fallback()
        raise


def get_ro_counties() -> List[str]:
    """Returneaza ro counties."""
    _ensure_ro_localities_table()
    conn = get_conn()
    cur = conn.cursor()
    cur.execute(f"SELECT DISTINCT county FROM {RO_LOCALITIES_TABLE} ORDER BY county COLLATE NOCASE")
    rows = [_clean_county_name(str(r[0] or "").strip()) for r in cur.fetchall()]
    conn.close()
    uniq = sorted({r for r in rows if r}, key=lambda x: x.lower())
    return uniq


def get_ro_localities_by_county(county: str) -> List[str]:
    """Returneaza ro localities by county."""
    county_txt = _clean_county_name(county)
    if not county_txt:
        return []
    _ensure_ro_localities_table()
    conn = get_conn()
    cur = conn.cursor()
    cur.execute(
        f"SELECT locality FROM {RO_LOCALITIES_TABLE} WHERE county=? OR county=? ORDER BY locality COLLATE NOCASE",
        (county_txt, f"{county_txt} County"),
    )
    rows = [str(r[0] or "").strip() for r in cur.fetchall()]
    conn.close()
    return [r for r in rows if r]


def get_domiciliu_suggestions(limit: int = 60000) -> List[str]:
    """Returneaza domiciliu suggestions."""
    try:
        _ensure_ro_localities_table()
        conn = get_conn()
        cur = conn.cursor()

        cur.execute(f"SELECT COUNT(*) FROM {RO_LOCALITIES_TABLE}")
        cnt = int(cur.fetchone()[0] or 0)
        if cnt <= 0:
            conn.close()
            _seed_ro_localities_fallback()
            conn = get_conn()
            cur = conn.cursor()

        values: List[str] = []
        seen = set()

        cur.execute(
            f"SELECT locality, county FROM {RO_LOCALITIES_TABLE} ORDER BY locality COLLATE NOCASE LIMIT ?",
            (max(1000, int(limit)),),
        )
        for loc, county in cur.fetchall():
            loc_txt = (loc or "").strip()
            county_txt = (county or "").strip()
            if not loc_txt:
                continue
            val = f"{loc_txt}, {county_txt}" if county_txt else loc_txt
            if val not in seen:
                seen.add(val)
                values.append(val)

        cur.execute(
            "SELECT DISTINCT domiciliu FROM pacienti_master WHERE domiciliu IS NOT NULL AND TRIM(domiciliu)<>'' ORDER BY domiciliu COLLATE NOCASE LIMIT 3000"
        )
        for row in cur.fetchall():
            txt = str(row[0] or "").strip()
            if txt and txt not in seen:
                seen.add(txt)
                values.append(txt)

        conn.close()
        return values
    except Exception:
        return []


_ICD10_COMMA_SPLIT_RE = re.compile(
    r",\s*(?=[A-TV-Z]\d{2}(?:\.\d{1,4})?\b)",
    flags=re.IGNORECASE,
)


def _split_icd10_tokens(s: Optional[str]) -> List[str]:
    """Imparte diagnosticele ICD-10 in token-uri, evitand split pe virgula din descriere."""
    raw = (s or "").strip()
    if not raw:
        return []
    out: List[str] = []
    # Delimitatori principali: ';' si newline. Virgula e delimitator doar daca
    # dupa ea incepe explicit un nou cod ICD-10 (ex: "M54.5, M75.9").
    major_parts = re.split(r"[;\n]+", raw)
    for part in major_parts:
        chunk = (part or "").strip()
        if not chunk:
            continue
        for sub in _ICD10_COMMA_SPLIT_RE.split(chunk):
            t = (sub or "").strip().strip(",")
            if t:
                out.append(t)
    return out


def _icd10_current_token(s: str) -> str:
    """Gestioneaza current token."""
    if not s:
        return ""
    major_parts = re.split(r"[;\n]+", s)
    if not major_parts:
        return ""
    last_chunk = (major_parts[-1] or "").strip()
    if not last_chunk:
        return ""
    parts = _ICD10_COMMA_SPLIT_RE.split(last_chunk)
    if not parts:
        return ""
    return (parts[-1] or "").strip()


def normalize_icd10_single(s: Optional[str]) -> Tuple[Optional[str], bool]:
    """Normalizeaza ICD10 single."""
    toks = _split_icd10_tokens(s)
    if not toks:
        return None, False
    return toks[0], len(toks) > 1


def normalize_icd10_multi(s: Optional[str]) -> Optional[str]:
    """Normalizeaza ICD10 multi."""
    toks = _split_icd10_tokens(s)
    if not toks:
        return None
    out = []
    seen = set()
    for t in toks:
        k = t.lower()
        if k in seen:
            continue
        seen.add(k)
        out.append(t)
    return "; ".join(out) if out else None


def normalize_consult_diagnoses(payload: dict, parent: Optional[QWidget] = None) -> dict:
    """Normalizeaza consult diagnoses."""
    p = dict(payload or {})
    d1, multi = normalize_icd10_single(p.get("diagnostic_principal"))
    d2 = normalize_icd10_multi(p.get("diagnostic_secundar"))
    dlib = str(p.get("diagnostic_liber") or "").strip()
    p["diagnostic_principal"] = d1 or None
    p["diagnostic_secundar"] = d2 or None
    p["diagnostic_liber"] = dlib or None
    if multi and parent is not None:
        QMessageBox.warning(
            parent,
            "Diagnostic principal",
            "La diagnostic principal este permis un singur diagnostic.\nAm pastrat primul."
        )
    return p


def _icd10_row_to_label(code: str, title: str) -> str:
    """Gestioneaza row to label."""
    code = (code or "").strip()
    title = (title or "").strip()
    if code and title:
        return f"{code} - {title}"
    return code or title


def ensure_icd10_table():
    """Asigura ICD10 table."""
    conn = get_conn()
    cur = conn.cursor()
    cur.execute("""
        CREATE TABLE IF NOT EXISTS icd10_codes (
            code TEXT PRIMARY KEY,
            title TEXT,
            search TEXT
        )
    """)
    conn.commit()
    conn.close()


def ensure_icd10_bundle() -> bool:
    """Asigura ICD10 bundle."""
    if ICD10_CSV_PATH.exists():
        return True
    for p in ICD10_BUNDLE_PATHS:
        try:
            if p and p.exists():
                ICD10_CSV_PATH.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(p, ICD10_CSV_PATH)
                global ICD10_BUNDLE_COPIED
                ICD10_BUNDLE_COPIED = True
                return True
        except Exception:
            continue
    return False


def load_icd10_cache(force: bool = False) -> List[str]:
    """Incarca ICD10 cache."""
    global _ICD10_CACHE, _ICD10_CACHE_TS
    if _ICD10_CACHE and not force:
        return _ICD10_CACHE
    if ICD10_READONLY_LOCAL:
        ensure_icd10_bundle()
        rows = _load_icd10_from_sqlite()
        if not rows:
            rows = _load_icd10_from_csv()
        _ICD10_CACHE = rows
        _ICD10_CACHE_TS = time.time()
        return _ICD10_CACHE
    ensure_icd10_table()
    conn = get_conn()
    cur = conn.cursor()
    cur.execute("SELECT code, title FROM icd10_codes ORDER BY code")
    rows = cur.fetchall()
    conn.close()
    _ICD10_CACHE = [_icd10_row_to_label(r[0], r[1]) for r in rows]
    _ICD10_CACHE_TS = time.time()
    return _ICD10_CACHE


def _load_icd10_search_cache(force: bool = False) -> List[Tuple[str, str]]:
    """Incarca ICD10 search cache."""
    global _ICD10_SEARCH_CACHE, _ICD10_SEARCH_CACHE_TS
    if _ICD10_SEARCH_CACHE and not force:
        return _ICD10_SEARCH_CACHE
    ensure_icd10_bundle()
    rows: List[Tuple[str, str]] = []
    # prefer local sqlite mirror if available
    try:
        ensure_icd10_table()
        conn = get_conn()
        cur = conn.cursor()
        cur.execute("SELECT code, title, search FROM icd10_codes ORDER BY code")
        db_rows = cur.fetchall()
        conn.close()
        for r in db_rows:
            code = r[0] or ""
            title = r[1] or ""
            label = _icd10_row_to_label(code, title)
            search = r[2] or _norm(label)
            rows.append((label, search))
    except Exception:
        rows = []
    if not rows:
        # fallback to CSV
        if ICD10_CSV_PATH.exists():
            try:
                with open(ICD10_CSV_PATH, "r", encoding="utf-8-sig", newline="") as f:
                    reader = csv.DictReader(f)
                    for r in reader:
                        code = (r.get("code") or "").strip()
                        title = (r.get("title") or "").strip()
                        if not code and not title:
                            continue
                        if not code:
                            code = title.split(" ", 1)[0].strip()
                        label = _icd10_row_to_label(code, title)
                        rows.append((label, _norm(label)))
            except Exception:
                rows = []
    _ICD10_SEARCH_CACHE = rows
    _ICD10_SEARCH_CACHE_TS = time.time()
    return _ICD10_SEARCH_CACHE


def import_icd10_csv(path: str) -> int:
    """Importa ICD10 CSV."""
    if ICD10_READONLY_LOCAL:
        raise RuntimeError("ICD-10 este read-only local. Actualizarea se face doar din Supabase.")
    ensure_icd10_table()
    rows: List[Tuple[str, str, str]] = []
    with open(path, "r", encoding="utf-8-sig", newline="") as f:
        sample = f.read(4096)
        f.seek(0)
        has_header = False
        first = sample.splitlines()[0] if sample else ""
        if "code" in first.lower() or "diagnosis" in first.lower() or "title" in first.lower() or "descr" in first.lower():
            has_header = True
        if has_header:
            reader = csv.DictReader(f)
            for r in reader:
                code = (r.get("code") or r.get("icd_code") or r.get("icd10") or r.get("diagnosis_code") or "").strip()
                title = (r.get("title") or r.get("diagnosis") or r.get("description") or r.get("name") or "").strip()
                if not code and not title:
                    continue
                if not code:
                    code = title.split(" ", 1)[0].strip()
                label = _icd10_row_to_label(code, title)
                rows.append((code, title, _norm(label)))
        else:
            reader = csv.reader(f)
            for r in reader:
                if not r:
                    continue
                code = (r[0] or "").strip()
                title = (r[1] if len(r) > 1 else "").strip()
                if not code and not title:
                    continue
                label = _icd10_row_to_label(code, title)
                rows.append((code, title, _norm(label)))

    if not rows:
        return 0

    conn = get_conn()
    cur = conn.cursor()
    cur.executemany(
        "INSERT OR REPLACE INTO icd10_codes(code, title, search) VALUES (?,?,?)",
        rows,
    )
    conn.commit()
    conn.close()
    load_icd10_cache(force=True)
    return len(rows)


def ensure_icd10_loaded():
    """Asigura ICD10 loaded."""
    try:
        if ICD10_READONLY_LOCAL:
            ensure_icd10_bundle()
            # populate local sqlite from csv if missing
            if ICD10_CSV_PATH.exists():
                try:
                    ensure_icd10_table()
                    conn = get_conn()
                    cur = conn.cursor()
                    cur.execute("SELECT COUNT(*) FROM icd10_codes")
                    cnt = int(cur.fetchone()[0] or 0)
                    if cnt == 0:
                        rows = []
                        with open(ICD10_CSV_PATH, "r", encoding="utf-8-sig", newline="") as f:
                            reader = csv.DictReader(f)
                            for r in reader:
                                code = (r.get("code") or "").strip()
                                title = (r.get("title") or "").strip()
                                if not code and not title:
                                    continue
                                if not code:
                                    code = title.split(" ", 1)[0].strip()
                                label = _icd10_row_to_label(code, title)
                                rows.append((code, title, _norm(label)))
                        if rows:
                            cur.executemany(
                                "INSERT OR REPLACE INTO icd10_codes(code, title, search) VALUES (?,?,?)",
                                rows,
                            )
                            conn.commit()
                    conn.close()
                except Exception:
                    pass
            if not ICD10_CSV_PATH.exists() and ICD10_SUPABASE_ENABLED:
                try:
                    sync_icd10_from_supabase(force=True)
                except Exception:
                    pass
            return
        ensure_icd10_table()
        conn = get_conn()
        cur = conn.cursor()
        cur.execute("SELECT COUNT(*) FROM icd10_codes")
        cnt = int(cur.fetchone()[0] or 0)
        conn.close()
        if cnt == 0 and ICD10_CSV_PATH.exists():
            import_icd10_csv(str(ICD10_CSV_PATH))
    except Exception:
        pass


def apply_icd10_completer(edit: QLineEdit, multi: bool = False):
    """Aplica ICD10 completer."""
    try:
        ensure_icd10_loaded()
        _load_icd10_search_cache()
        model = QStringListModel([], edit)
        comp = QCompleter(model, edit)
        comp.setCaseSensitivity(Qt.CaseSensitivity.CaseInsensitive)
        comp.setFilterMode(Qt.MatchFlag.MatchContains)
        comp.setCompletionMode(QCompleter.CompletionMode.PopupCompletion)
        try:
            comp.setMaxVisibleItems(20)
        except Exception:
            pass
        edit.setCompleter(comp)
        if multi:
            edit.setPlaceholderText("ICD-10: scrie cod/diagnostic si separa cu ;")
        else:
            edit.setPlaceholderText("ICD-10: scrie cod sau diagnostic...")
        edit._icd10_model = model  # prevent GC
        edit._icd10_completer = comp
        edit._icd10_timer = QTimer(edit)
        edit._icd10_timer.setSingleShot(True)
        edit._icd10_timer.setInterval(180)
        edit._icd10_last_text = ""
        cache: Dict[str, List[str]] = {}
        last_qn = ""
        last_matches: List[Tuple[str, str]] = []

        def _filter_list(query: str) -> List[str]:
            """Filtreaza list ca helper intern in `apply_icd10_completer`."""
            nonlocal last_qn, last_matches
            qn = _norm(query or "")
            if len(qn) < 2:
                return []
            if qn in cache:
                return cache[qn]
            source = last_matches if last_qn and qn.startswith(last_qn) and last_matches else _ICD10_SEARCH_CACHE
            out: List[str] = []
            matches: List[Tuple[str, str]] = []
            for label, search in source:
                if qn in search:
                    if len(out) < 40:
                        out.append(label)
                    if len(matches) < 400:
                        matches.append((label, search))
                    if len(out) >= 40 and len(matches) >= 400:
                        break
            last_qn = qn
            last_matches = matches
            cache[qn] = out
            return out

        def _update_model():
            """Actualizeaza model ca helper intern in `apply_icd10_completer`."""
            base = edit._icd10_last_text if hasattr(edit, "_icd10_last_text") else (edit.text() or "")
            query = _icd10_current_token(base) if multi else (base or "").strip()
            items = _filter_list(query)
            model.setStringList(items)
            try:
                comp.setCompletionPrefix(query or "")
            except Exception:
                pass
            try:
                if items and len((query or "").strip()) >= 2 and edit.hasFocus():
                    comp.complete()
                else:
                    popup = comp.popup()
                    if popup is not None:
                        popup.hide()
            except Exception:
                pass

        def _queue_update(txt: str):
            """Gestioneaza update ca helper intern in `apply_icd10_completer`."""
            edit._icd10_last_text = txt
            try:
                edit._icd10_timer.stop()
                edit._icd10_timer.timeout.disconnect()
            except Exception:
                pass
            edit._icd10_timer.timeout.connect(_update_model)
            edit._icd10_timer.start()

        try:
            edit.textEdited.connect(_queue_update)
        except Exception:
            pass

        if multi:
            def _apply_selected(text: str):
                """Aplica selected ca helper intern in `apply_icd10_completer`."""
                base = getattr(edit, "_icd10_last_text", edit.text() or "")
                trailing = base.strip().endswith((",", ";"))
                tokens = _split_icd10_tokens(base)
                if trailing or not tokens:
                    if text not in tokens:
                        tokens.append(text)
                else:
                    tokens[-1] = text
                edit.setText("; ".join(tokens))

            try:
                comp.activated.connect(_apply_selected)
            except Exception:
                pass
    except Exception:
        pass


def _load_icd10_from_csv() -> List[str]:
    """Incarca ICD10 from CSV."""
    if not ICD10_CSV_PATH.exists():
        return []
    rows = []
    try:
        with open(ICD10_CSV_PATH, "r", encoding="utf-8-sig", newline="") as f:
            reader = csv.DictReader(f)
            for r in reader:
                code = (r.get("code") or "").strip()
                title = (r.get("title") or "").strip()
                if not code and not title:
                    continue
                if not code:
                    code = title.split(" ", 1)[0].strip()
                rows.append(_icd10_row_to_label(code, title))
    except Exception:
        return []
    return rows


def _load_icd10_from_sqlite() -> List[str]:
    """Incarca ICD10 from sqlite."""
    try:
        ensure_icd10_table()
        conn = get_conn()
        cur = conn.cursor()
        cur.execute("SELECT code, title FROM icd10_codes ORDER BY code")
        rows = cur.fetchall()
        conn.close()
        if not rows:
            return []
        return [_icd10_row_to_label(r[0], r[1]) for r in rows]
    except Exception:
        return []


def supabase_fetch_icd10(progress_cb=None, cancelled_cb=None) -> List[Dict[str, Any]]:
    """Gestioneaza fetch ICD10."""
    if not SUPABASE_URL or not SUPABASE_ANON_KEY:
        raise RuntimeError("Supabase not configured")
    out: List[Dict[str, Any]] = []
    limit = 1000
    offset = 0
    page_no = 0
    if progress_cb:
        try:
            progress_cb(5, "Pornesc descarcarea ICD-10 din Supabase...")
        except Exception:
            pass
    while True:
        if cancelled_cb and cancelled_cb():
            raise RuntimeError("Sincronizare ICD-10 anulata.")
        params = {"select": "code,title", "order": "code.asc", "limit": limit, "offset": offset}
        data = supabase_request("GET", "/rest/v1/icd10_codes", params=params)
        if not data:
            break
        out.extend(data)
        page_no += 1
        if progress_cb:
            try:
                approx = min(85, 5 + page_no * 10)
                progress_cb(approx, f"Descarc ICD-10... {len(out)} coduri")
            except Exception:
                pass
        if len(data) < limit:
            break
        offset += limit
    return out


def _icd10_rows_fingerprint(rows: List[Dict[str, Any]]) -> str:
    """Gestioneaza rows fingerprint."""
    parts: List[str] = []
    for r in rows:
        code = to_ascii_text((r.get("code") or "").strip())
        title = to_ascii_text((r.get("title") or "").strip())
        parts.append(f"{code}\t{title}")
    payload = "\n".join(parts).encode("utf-8", errors="ignore")
    return hashlib.sha256(payload).hexdigest()


def _icd10_remote_fingerprint() -> str:
    # Lightweight remote signature to detect changes without downloading full table.
    """Gestioneaza remote fingerprint."""
    latest_marker = ""
    try:
        latest = supabase_request(
            "GET",
            "/rest/v1/icd10_codes",
            params={"select": "updated_at", "order": "updated_at.desc.nullslast", "limit": 1},
        )
        if isinstance(latest, list) and latest:
            latest_marker = to_ascii_text((latest[0] or {}).get("updated_at") or "")
    except Exception:
        latest_marker = ""

    first = supabase_request(
        "GET",
        "/rest/v1/icd10_codes",
        params={"select": "code,title", "order": "code.asc", "limit": 1},
    )
    last = supabase_request(
        "GET",
        "/rest/v1/icd10_codes",
        params={"select": "code,title", "order": "code.desc", "limit": 1},
    )

    first_row = (first[0] if isinstance(first, list) and first else {}) or {}
    last_row = (last[0] if isinstance(last, list) and last else {}) or {}

    raw = "|".join([
        latest_marker,
        to_ascii_text(first_row.get("code") or ""),
        to_ascii_text(first_row.get("title") or ""),
        to_ascii_text(last_row.get("code") or ""),
        to_ascii_text(last_row.get("title") or ""),
    ])
    if not raw.strip("|"):
        return ""
    return hashlib.sha256(raw.encode("utf-8", errors="ignore")).hexdigest()


def sync_icd10_from_supabase(force: bool = False, progress_cb=None, cancelled_cb=None) -> int:
    """Sincronizeaza ICD10 from Supabase."""
    if not ICD10_SUPABASE_ENABLED:
        return 0
    if progress_cb:
        try:
            progress_cb(1, "Verific daca ICD-10 necesita actualizare...")
        except Exception:
            pass
    if not force:
        local_fp = get_setting("icd10_remote_fingerprint", "") or ""
        remote_fp = ""
        try:
            remote_fp = _icd10_remote_fingerprint()
        except Exception:
            remote_fp = ""

        if remote_fp and local_fp and remote_fp == local_fp and ICD10_CSV_PATH.exists():
            set_setting("icd10_sync_at", now_ts())
            if progress_cb:
                try:
                    progress_cb(100, "ICD-10 este deja actualizat.")
                except Exception:
                    pass
            return 0

        if not remote_fp:
            last = get_setting("icd10_sync_at", "") or ""
            if last and ICD10_CSV_PATH.exists():
                try:
                    last_dt = _parse_dt_any(last)
                    if last_dt and (datetime.now() - last_dt) < timedelta(days=ICD10_SUPABASE_SYNC_DAYS):
                        if progress_cb:
                            try:
                                progress_cb(100, "ICD-10 este deja actualizat.")
                            except Exception:
                                pass
                        return 0
                except Exception:
                    pass
    rows = supabase_fetch_icd10(progress_cb=progress_cb, cancelled_cb=cancelled_cb)
    if not rows:
        if progress_cb:
            try:
                progress_cb(100, "Nu exista coduri ICD-10 de sincronizat.")
            except Exception:
                pass
        return 0
    if progress_cb:
        try:
            progress_cb(88, "Salvez ICD-10 local...")
        except Exception:
            pass
    ICD10_CSV_PATH.parent.mkdir(parents=True, exist_ok=True)
    with open(ICD10_CSV_PATH, "w", encoding="utf-8", newline="") as f:
        w = csv.writer(f)
        w.writerow(["code", "title"])
        for r in rows:
            w.writerow([r.get("code") or "", r.get("title") or ""])
    try:
        ensure_icd10_table()
        conn = get_conn()
        cur = conn.cursor()
        payload = []
        for r in rows:
            code = r.get("code") or ""
            title = r.get("title") or ""
            label = _icd10_row_to_label(code, title)
            payload.append((code, title, _norm(label)))
        if payload:
            cur.executemany(
                "INSERT OR REPLACE INTO icd10_codes(code, title, search) VALUES (?,?,?)",
                payload,
            )
            conn.commit()
        conn.close()
    except Exception:
        pass
    # refresh cache
    global _ICD10_CACHE, _ICD10_CACHE_TS
    _ICD10_CACHE = [_icd10_row_to_label(r.get("code") or "", r.get("title") or "") for r in rows]
    _ICD10_CACHE_TS = time.time()
    try:
        set_setting("icd10_remote_fingerprint", _icd10_rows_fingerprint(rows))
    except Exception:
        pass
    set_setting("icd10_sync_at", now_ts())
    if progress_cb:
        try:
            progress_cb(100, f"ICD-10 actualizat: {len(rows)} coduri")
        except Exception:
            pass
    return len(rows)


def _norm_name(s: str) -> str:
    """Normalizeaza numele pentru comparare si cautare robusta."""
    return _norm(s)


def _to_str_safe(x):
    """Converteaza str safe."""
    if pd.isna(x):
        return None
    s = str(x).strip()
    return s if s != "" else None


def _to_date_str_ymd(x):
    """Converteaza date str YYYY-MM-DD."""
    if pd.isna(x):
        return None
    try:
        raw = str(x).strip()
        d = pd.to_datetime(x, errors="coerce")
        if pd.isna(d):
            return raw if validate_ymd_or_empty(raw) and raw else None

        # For ambiguous 2-digit years (e.g. 24.06.66), prefer past dates.
        # If parsed year lands in the future relative to current year,
        # shift the century back by 100 years.
        try:
            if re.match(r"^\s*\d{1,2}[./-]\d{1,2}[./-]\d{2}\s*$", raw):
                cur_year = datetime.now().year
                if int(d.year) > cur_year:
                    d = d.replace(year=int(d.year) - 100)
        except Exception:
            pass

        return str(d.date())
    except Exception:
        s = str(x).strip()
        return s if validate_ymd_or_empty(s) and s else None


def _to_int_safe(x):
    """Converteaza int safe."""
    if pd.isna(x):
        return None
    try:
        return int(float(x))
    except Exception:
        try:
            return int(str(x).strip())
        except Exception:
            return None


def _sniff_csv_read_options(path: Path, encoding: str) -> Dict[str, Any]:
    """Gestioneaza CSV read options."""
    try:
        with path.open("r", encoding=encoding, newline="") as fh:
            sample = fh.read(128 * 1024)
        if not sample or not sample.strip():
            return {}

        sniffer = csv.Sniffer()
        dialect = sniffer.sniff(sample, delimiters=",;\t|")
        opts: Dict[str, Any] = {
            "sep": dialect.delimiter,
            "quotechar": dialect.quotechar or '"',
            "doublequote": bool(getattr(dialect, "doublequote", True)),
            "skipinitialspace": bool(getattr(dialect, "skipinitialspace", False)),
            "engine": "python",
        }
        esc = getattr(dialect, "escapechar", None)
        if esc:
            opts["escapechar"] = esc
        return opts
    except Exception:
        return {}


def _maybe_expand_single_column_dataframe(df: "pd.DataFrame") -> "pd.DataFrame":
    """Decide daca ruleaza expand single column dataframe."""
    if df is None or df.empty:
        return df
    try:
        if len(df.columns) != 1:
            return df

        only_col = str(df.columns[0] or "")
        raw_vals = [str(v) for v in df.iloc[:, 0].tolist() if str(v or "").strip()]
        if not raw_vals:
            return df

        sample_vals = [str(only_col or "")] + raw_vals[:120]
        delim_candidates = [";", "\t", "|", ","]
        best_delim = None
        best_width = 1
        best_hits = 0
        best_total = 0

        for delim in delim_candidates:
            counts: List[int] = []
            for txt in sample_vals:
                try:
                    parts = next(csv.reader([txt], delimiter=delim, quotechar='"'))
                    counts.append(len(parts))
                except Exception:
                    counts.append(1)

            hits = sum(1 for c in counts if c >= 2)
            if hits <= 0:
                continue

            width_freq: Dict[int, int] = {}
            for c in counts:
                if c >= 2:
                    width_freq[c] = int(width_freq.get(c, 0)) + 1
            if not width_freq:
                continue

            width = max(width_freq.items(), key=lambda kv: (kv[1], kv[0]))[0]
            total_cells = sum(c for c in counts if c >= 2)
            if (
                (hits > best_hits)
                or (hits == best_hits and total_cells > best_total)
                or (hits == best_hits and total_cells == best_total and width > best_width)
            ):
                best_delim = delim
                best_width = width
                best_hits = hits
                best_total = total_cells

        min_hits = max(1, int(len(sample_vals) * 0.20))
        if not best_delim or best_width < 2 or best_hits < min_hits:
            return df

        parsed_rows: List[List[str]] = []
        for txt in [str(v or "") for v in df.iloc[:, 0].tolist()]:
            try:
                parts = next(csv.reader([txt], delimiter=best_delim, quotechar='"'))
            except Exception:
                parts = [txt]
            if len(parts) < best_width:
                parts = parts + [""] * (best_width - len(parts))
            elif len(parts) > best_width:
                parts = parts[: best_width - 1] + [best_delim.join(parts[best_width - 1 :])]
            parsed_rows.append(parts)

        out = pd.DataFrame(parsed_rows)

        try:
            hparts = next(csv.reader([only_col], delimiter=best_delim, quotechar='"'))
            if len(hparts) == best_width and any(str(x).strip() for x in hparts):
                out.columns = _dedupe_header_names([str(x).strip() for x in hparts])
            else:
                out.columns = [f"col_{i+1}" for i in range(best_width)]
        except Exception:
            out.columns = [f"col_{i+1}" for i in range(best_width)]

        return out
    except Exception:
        return df


def _parse_csv_raw_fallback(path: Path, encoding: str) -> Optional["pd.DataFrame"]:
    """Parseaza CSV raw fallback."""
    try:
        with path.open("r", encoding=encoding, newline="") as fh:
            lines = [ln for ln in fh.read().splitlines() if str(ln or "").strip()]
        if not lines:
            return None

        candidates = [";", "\t", "|", ","]
        best_delim = None
        best_hits = 0
        best_width = 1

        probe = lines[:200]
        for delim in candidates:
            widths: List[int] = []
            for ln in probe:
                try:
                    parts = next(csv.reader([ln], delimiter=delim, quotechar='"'))
                    widths.append(len(parts))
                except Exception:
                    widths.append(1)
            hits = sum(1 for w in widths if w >= 2)
            if hits <= 0:
                continue
            mode = {}
            for w in widths:
                if w >= 2:
                    mode[w] = int(mode.get(w, 0)) + 1
            if not mode:
                continue
            width = max(mode.items(), key=lambda kv: (kv[1], kv[0]))[0]
            if (hits > best_hits) or (hits == best_hits and width > best_width):
                best_delim = delim
                best_hits = hits
                best_width = width

        if not best_delim or best_width < 2:
            return None

        rows: List[List[str]] = []
        for ln in lines:
            try:
                parts = next(csv.reader([ln], delimiter=best_delim, quotechar='"'))
            except Exception:
                parts = [ln]
            if len(parts) < best_width:
                parts = parts + [""] * (best_width - len(parts))
            elif len(parts) > best_width:
                parts = parts[: best_width - 1] + [best_delim.join(parts[best_width - 1 :])]
            rows.append([str(x or "").strip() for x in parts])

        if not rows:
            return None

        header = _dedupe_header_names(rows[0])
        data_rows = rows[1:] if len(rows) > 1 else []
        return pd.DataFrame(data_rows, columns=header)
    except Exception:
        return None


def _read_tabular_dataframe(path: str) -> "pd.DataFrame":
    """
    Read tabular input for imports (Excel/CSV/TSV) with robust CSV fallback.
    CSV is read as strings to preserve leading zeroes (CNP/telefon).
    """
    p = Path(path or "")
    if not p.exists():
        raise RuntimeError("Fisierul nu exista.")

    ext = p.suffix.lower()
    if ext in {".xlsx", ".xls", ".xlsm", ".xlsb"}:
        return pd.read_excel(str(p), sheet_name=0)

    if ext in {".csv", ".tsv", ".txt"}:
        encodings = ["utf-8-sig", "utf-8", "cp1250", "latin-1"]
        if ext == ".tsv":
            separators = ["\t"]
        else:
            separators = [None, ";", ",", "\t", "|"]

        candidate = None
        last_err = None
        for enc in encodings:
            base_kwargs = {
                "encoding": enc,
                "dtype": str,
                "keep_default_na": False,
                "na_filter": False,
                "skip_blank_lines": True,
            }

            # 1) CSV dialect parsing (delimiter + quote/escape) according to file rules.
            if ext in {".csv", ".txt"}:
                sniff_opts = _sniff_csv_read_options(p, enc)
                if sniff_opts:
                    try:
                        kwargs = dict(base_kwargs)
                        kwargs.update(sniff_opts)
                        df = pd.read_csv(str(p), **kwargs)
                        df = _maybe_expand_single_column_dataframe(df)
                        if candidate is None:
                            candidate = df
                        if len(df.columns) > 1:
                            return df
                    except Exception as e:
                        last_err = e

            # 2) Fallbacks for unusual files.
            for sep in separators:
                try:
                    kwargs = dict(base_kwargs)
                    if sep is None:
                        kwargs["sep"] = None
                        kwargs["engine"] = "python"
                    else:
                        kwargs["sep"] = sep
                    df = pd.read_csv(str(p), **kwargs)
                    df = _maybe_expand_single_column_dataframe(df)
                    if candidate is None:
                        candidate = df
                    # Prefer a parse with >=2 columns for delimited files.
                    if len(df.columns) > 1 or ext == ".tsv":
                        return df
                except Exception as e:
                    last_err = e
                    continue
        if candidate is not None:
            if len(candidate.columns) <= 1:
                for enc in encodings:
                    raw_df = _parse_csv_raw_fallback(p, enc)
                    if raw_df is not None and len(raw_df.columns) > 1:
                        return raw_df
            return candidate
        raise RuntimeError(f"Eroare la citire CSV/TSV: {last_err}")

    raise RuntimeError("Format neacceptat. Foloseste: .xlsx, .xls, .csv sau .tsv")


def last_backup_path() -> Path:
    """Gestioneaza backup path."""
    return AUTOBACKUP_DIR / "last.db"


def daily_backup_path(d: date) -> Path:
    """Gestioneaza backup path."""
    return DAILY_DIR / f"pacienti_{d.strftime('%Y-%m-%d')}.db"


def _sqlite_backup_quick_check(path: Path) -> bool:
    """Gestioneaza backup quick check."""
    try:
        if (not path.exists()) or path.stat().st_size < 4096:
            return False
    except Exception:
        return False

    conn = None
    try:
        conn = sqlite3.connect(str(path))
        cur = conn.cursor()
        cur.execute("PRAGMA quick_check;")
        row = cur.fetchone()
        return bool(row and str(row[0]).strip().lower() == "ok")
    except Exception:
        return False
    finally:
        if conn is not None:
            try:
                conn.close()
            except Exception:
                pass


def _parse_daily_backup_date_from_name(path: Path) -> Optional[date]:
    """Parseaza daily backup date from name."""
    m = re.match(r"^pacienti_(\d{4}-\d{2}-\d{2})$", path.stem)
    if not m:
        return None
    try:
        return datetime.strptime(m.group(1), "%Y-%m-%d").date()
    except Exception:
        return None


def prune_autobackups(retention_days: int = AUTOBACKUP_RETENTION_DAYS) -> Dict[str, int]:
    """Sterge backup-urile vechi conform perioadei de retentie configurate."""
    keep_days = max(1, int(retention_days))
    cutoff_day = date.today() - timedelta(days=keep_days)
    cutoff_ts = time.time() - (keep_days * 24 * 60 * 60)

    removed_daily = 0
    removed_migrations = 0
    errors = 0

    try:
        for p in DAILY_DIR.glob("pacienti_*.db"):
            try:
                d = _parse_daily_backup_date_from_name(p)
                if d is None:
                    continue
                if d < cutoff_day:
                    p.unlink(missing_ok=True)
                    removed_daily += 1
            except Exception:
                errors += 1
    except Exception:
        errors += 1

    try:
        for p in DB_SCHEMA_MIGRATION_BACKUP_DIR.glob("schema_backup_*.db"):
            try:
                if p.stat().st_mtime < cutoff_ts:
                    p.unlink(missing_ok=True)
                    removed_migrations += 1
            except Exception:
                errors += 1
    except Exception:
        errors += 1

    return {
        "removed_daily": int(removed_daily),
        "removed_migrations": int(removed_migrations),
        "errors": int(errors),
    }


# ============================================================
# UI helpers
# ============================================================
def apply_std_icon(btn, std_icon):
    """Aplica std icon."""
    app = QApplication.instance()
    if app:
        btn.setIcon(app.style().standardIcon(std_icon))
        btn.setIconSize(QSize(22, 22))


def apply_global_button_style(app: QApplication):
    # Professional, clean UI theme
    """Aplica global button style."""
    app.setStyleSheet(
        (app.styleSheet() or "")
        + """
        QWidget {
            font-family: "Segoe UI";
            font-size: 11pt;
            color: #1f2937;
            background-color: #f8fafc;
        }
        QDialog, QMainWindow, QWidget#centralwidget {
            background-color: #f8fafc;
        }
        QGroupBox {
            border: 1px solid #d7dce3;
            border-radius: 8px;
            margin-top: 12px;
            padding: 10px;
            background: #ffffff;
        }
        QGroupBox::title {
            subcontrol-origin: margin;
            left: 12px;
            padding: 0 6px;
            color: #2b3645;
            font-weight: 600;
            background: #f8fafc;
        }
        QPushButton, QToolButton {
            border: none;
            border-radius: 6px;
            background: #ffffff;
            background-color: #ffffff;
            background-image: none;
            padding: 8px 14px;
            min-height: 30px;
            outline: none;
        }
        QPushButton:hover, QToolButton:hover {
            background: #f1f5f9;
            background-color: #f1f5f9;
            background-image: none;
        }
        QPushButton#primary {
            background: #2b70dd;
            color: #ffffff;
            border: none;
        }
        QPushButton:pressed, QToolButton:pressed {
            background: #e6edf7;
            background-color: #e6edf7;
            background-image: none;
        }
        QPushButton#primary:hover {
            background: #255fc3;
        }
        QPushButton:disabled, QToolButton:disabled {
            color: #8b95a7;
            background: #f1f5f9;
            border: none;
        }
        QLineEdit, QTextEdit, QPlainTextEdit, QComboBox, QSpinBox, QDateEdit, QTimeEdit {
            border: 1px solid #c7d1dc;
            border-radius: 6px;
            padding: 8px 10px;
            background: #ffffff;
            selection-background-color: #dbeafe;
            selection-color: #000000;
        }
        QLineEdit:focus, QTextEdit:focus, QPlainTextEdit:focus, QComboBox:focus, QSpinBox:focus, QDateEdit:focus, QTimeEdit:focus {
            border: 1px solid #2b70dd;
        }
        QComboBox {
            border: 1px solid #d6dbe3;
            border-radius: 6px;
            background: #eef1f5;
            color: #2f343b;
            font-weight: 500;
            font-size: 11pt;
            min-height: 24px;
            padding: 10px 34px 10px 12px;
        }
        QComboBox[empty="true"] {
            color: rgba(47, 52, 59, 135);
            font-weight: 400;
        }
        QComboBox:hover {
            border-color: #c8d0dc;
            background: #f2f4f7;
        }
        QComboBox:on {
            border-color: #bcc6d4;
            background: #edf1f6;
        }
        QComboBox::drop-down {
            border: none;
            border-left: 1px solid #d3d9e2;
            width: 28px;
            subcontrol-origin: padding;
            subcontrol-position: top right;
            background: transparent;
        }
        QComboBox::down-arrow {
            image: url(:/qt-project.org/styles/commonstyle/images/arrow-down-16.png);
            width: 10px;
            height: 10px;
            margin-right: 8px;
        }
        QComboBox:disabled {
            color: #8b95a7;
            background: #f3f5f8;
            border-color: #dde3ea;
        }
        QComboBox:disabled::down-arrow {
            border-top: 7px solid #9aa6b8;
        }
        QComboBox QAbstractItemView {
            border: 1px solid #d7dde6;
            border-radius: 8px;
            background: #ffffff;
            padding: 4px;
            outline: none;
            selection-background-color: #e7ebf1;
            selection-color: #2f343b;
            font-size: 11pt;
        }
        QComboBox QAbstractItemView::item {
            min-height: 30px;
            padding: 7px 12px;
            border-radius: 6px;
            margin: 1px 2px;
            color: #2f343b;
        }
        QComboBox QAbstractItemView::item:hover {
            background: #f1f4f8;
            color: #2f343b;
        }
        QComboBox QAbstractItemView::item:selected {
            background: #e7ebf1;
            color: #2f343b;
            font-weight: 500;
        }
        QCheckBox::indicator {
            width: 16px;
            height: 16px;
            border: 1px solid #8a96a8;
            border-radius: 3px;
            background: #ffffff;
        }
        QCheckBox::indicator:hover {
            border: 1px solid #5f728b;
            background: #f8fbff;
        }
        QCheckBox::indicator:checked {
            border: 1px solid #1f5fd0;
            background: #2b70dd;
        }
        QCheckBox::indicator:unchecked:disabled,
        QCheckBox::indicator:checked:disabled {
            border: 1px solid #c3cad5;
            background: #e7ecf3;
        }
        QTableView {
            background: #ffffff;
            alternate-background-color: #f6f9fc;
            gridline-color: #dfe3e8;
            border: 1px solid #e2e6ec;
            border-radius: 6px;
        }
        QTableView::item {
            padding: 4px 6px;
        }
        QTableView::item:hover {
            background: #eef6ff;
        }
        QHeaderView::section {
            background: #e9eff7;
            color: #2b3645;
            font-weight: 600;
            border: 1px solid #e1e5eb;
            padding: 8px 10px;
        }
        QAbstractItemView::item:selected {
            background: #dbeafe;
            color: #000000;
            font-weight: 600;
        }
        QAbstractItemView::item:selected:active {
            background: #dbeafe;
            color: #000000;
            font-weight: 600;
        }
        QLineEdit::selection, QTextEdit::selection, QPlainTextEdit::selection {
            background: #dbeafe;
            color: #000000;
            font-weight: 600;
        }
        QTabWidget::pane {
            border: 1px solid #e1e5eb;
            border-radius: 6px;
            background: #ffffff;
        }
        QTabBar::tab {
            background: #e9eff7;
            border: 1px solid #e1e5eb;
            border-bottom: none;
            padding: 8px 14px;
            border-top-left-radius: 6px;
            border-top-right-radius: 6px;
            margin-right: 4px;
        }
        QTabBar::tab:selected {
            background: #ffffff;
            color: #1f2937;
            font-weight: 600;
        }
        QFrame#headerBar {
            background: #ffffff;
            border: 1px solid #e2e6ec;
            border-radius: 10px;
        }
        QLabel#appTitle {
            font-size: 16pt;
            font-weight: 700;
            color: #0f172a;
        }
        QLabel#appSubtitle, QLabel#muted {
            color: #64748b;
            font-size: 10pt;
        }
        QPushButton#secondary, QToolButton#secondary {
            background: #f8fafc;
            border: none;
            color: #1f2937;
        }
        QPushButton#secondary:hover, QToolButton#secondary:hover {
            background: #eef2f7;
        }
        QPushButton#danger, QToolButton#danger {
            background: #ef4444;
            border: none;
            color: #ffffff;
        }
        QPushButton#danger:hover, QToolButton#danger:hover {
            background: #dc2626;
        }
        QScrollBar:vertical {
            width: 10px;
            background: transparent;
            margin: 2px;
        }
        QScrollBar::handle:vertical {
            background: #c0cad6;
            border-radius: 5px;
        }
        QScrollBar::handle:vertical:hover {
            background: #b2bdcc;
        }
        """
    )


def matplotlib_missing_message() -> str:
    """Gestioneaza missing message."""
    exe = sys.executable or "python"
    return (
        "Pentru grafice este necesar pachetul matplotlib.\n"
        f"Instaleaza cu: \"{exe}\" -m pip install matplotlib"
    )


def _icon_from_theme(name: str) -> QIcon:
    """Gestioneaza from theme."""
    ico = QIcon.fromTheme(name)
    return ico


def get_user_icon(size: int = 16) -> QIcon:
    """Returneaza user icon."""
    ico = _icon_from_theme("user")
    if ico.isNull():
        app = QApplication.instance()
        if app:
            ico = app.style().standardIcon(QStyle.StandardPixmap.SP_ComputerIcon)
    return ico


def get_lock_icon(size: int = 16) -> QIcon:
    """Returneaza lock icon."""
    ico = _icon_from_theme("dialog-password")
    if ico.isNull():
        ico = _icon_from_theme("lock")
    if ico.isNull():
        pix = QPixmap(size, size)
        pix.fill(Qt.GlobalColor.transparent)
        p = QPainter(pix)
        p.setRenderHint(QPainter.RenderHint.Antialiasing, True)
        p.setPen(QColor("#444444"))
        p.setBrush(QColor("#cfd4da"))
        p.drawRoundedRect(3, 7, size - 6, size - 6, 2, 2)
        p.setBrush(Qt.GlobalColor.transparent)
        p.drawArc(4, 1, size - 8, 10, 0 * 16, 180 * 16)
        p.end()
        ico = QIcon(pix)
    return ico


def get_role_icon(role: str, active: int = 1) -> QIcon:
    """Returneaza role icon."""
    app = QApplication.instance()
    if not app:
        return QIcon()
    style = app.style()
    if active == 0:
        return style.standardIcon(QStyle.StandardPixmap.SP_DialogCancelButton)
    if role == "admin":
        return style.standardIcon(QStyle.StandardPixmap.SP_DialogYesButton)
    if role == "medic":
        return style.standardIcon(QStyle.StandardPixmap.SP_FileDialogInfoView)
    if role == "asistenta":
        return style.standardIcon(QStyle.StandardPixmap.SP_MessageBoxInformation)
    if role == "receptie":
        return style.standardIcon(QStyle.StandardPixmap.SP_DirHomeIcon)
    return style.standardIcon(QStyle.StandardPixmap.SP_FileIcon)


class RowOutlineDelegate(QStyledItemDelegate):
    def __init__(self, table: QTableWidget):
        """Initializeaza clasa `RowOutlineDelegate` si starea initiala necesara."""
        super().__init__(table)
        self._table = table

    def _first_visible_col(self) -> int:
        """Gestioneaza visible col in `RowOutlineDelegate`."""
        try:
            for c in range(self._table.columnCount()):
                if not self._table.isColumnHidden(c):
                    return c
        except Exception:
            pass
        return 0

    def paint(self, painter, option, index):
        """Deseneaza randul tabelului cu stilul custom de contur si selectie."""
        opt = QStyleOptionViewItem(option)
        opt.state = opt.state & ~QStyle.StateFlag.State_HasFocus
        super().paint(painter, opt, index)
        if not (option.state & QStyle.StateFlag.State_Selected):
            return
        if index.column() != self._first_visible_col():
            return
        rect = option.rect
        rect.setLeft(0)
        rect.setRight(self._table.viewport().width() - 1)
        painter.save()
        painter.setClipRect(self._table.viewport().rect())
        pen = QPen(QColor("#4a76a8"))
        pen.setWidth(1)
        painter.setPen(pen)
        painter.setBrush(Qt.BrushStyle.NoBrush)
        painter.drawRect(rect.adjusted(0, 0, -1, -1))
        painter.restore()


def _create_calendar_icon(size: int = 32) -> QIcon:
    """Creeaza calendar icon."""
    pix = QPixmap(size, size)
    pix.fill(Qt.GlobalColor.transparent)

    p = QPainter(pix)
    p.setRenderHint(QPainter.RenderHint.Antialiasing, True)

    # body
    p.setPen(QColor("#2f3b52"))
    p.setBrush(QColor("#ffffff"))
    p.drawRoundedRect(1, 2, size - 2, size - 3, 3, 3)

    # header
    p.setBrush(QColor("#4e79a7"))
    p.setPen(QColor("#4e79a7"))
    p.drawRoundedRect(1, 2, size - 2, int(size * 0.28), 3, 3)

    # rings
    p.setPen(QColor("#ffffff"))
    p.setBrush(QColor("#ffffff"))
    r = max(2, size // 10)
    p.drawEllipse(int(size * 0.25) - r, 1, r * 2, r * 2)
    p.drawEllipse(int(size * 0.75) - r, 1, r * 2, r * 2)

    # grid dots
    p.setPen(QColor("#c7ccd2"))
    dot = max(1, size // 12)
    y0 = int(size * 0.42)
    for row in range(3):
        for col in range(3):
            x = int(size * 0.2) + col * int(size * 0.25)
            y = y0 + row * int(size * 0.18)
            p.drawEllipse(x, y, dot, dot)

    p.end()
    return QIcon(pix)


def get_calendar_icon(size: int = 32) -> QIcon:
    """Returneaza calendar icon."""
    icon = QIcon.fromTheme("x-office-calendar")
    if icon.isNull():
        icon = _create_calendar_icon(size)
    return icon


def _create_printer_icon(size: int = 24) -> QIcon:
    """Creeaza printer icon."""
    pix = QPixmap(size, size)
    pix.fill(Qt.GlobalColor.transparent)
    p = QPainter(pix)
    p.setRenderHint(QPainter.RenderHint.Antialiasing, True)

    body = QColor("#4b5563")
    panel = QColor("#9ca3af")
    paper = QColor("#ffffff")
    outline = QColor("#2f3b52")

    w = size
    h = size

    # printer body
    p.setPen(outline)
    p.setBrush(body)
    p.drawRoundedRect(int(w * 0.1), int(h * 0.35), int(w * 0.8), int(h * 0.4), 3, 3)

    # top panel
    p.setBrush(panel)
    p.drawRoundedRect(int(w * 0.18), int(h * 0.25), int(w * 0.64), int(h * 0.18), 2, 2)

    # paper
    p.setBrush(paper)
    p.drawRoundedRect(int(w * 0.22), int(h * 0.05), int(w * 0.56), int(h * 0.3), 2, 2)
    p.drawRoundedRect(int(w * 0.22), int(h * 0.62), int(w * 0.56), int(h * 0.3), 2, 2)

    # paper lines
    p.setPen(QColor("#c7ccd2"))
    for i in range(3):
        y = int(h * 0.68) + i * int(h * 0.06)
        p.drawLine(int(w * 0.28), y, int(w * 0.72), y)

    p.end()
    return QIcon(pix)


def get_printer_icon(size: int = 24) -> QIcon:
    """Returneaza printer icon."""
    icon = QIcon.fromTheme("printer")
    if icon.isNull():
        icon = QIcon.fromTheme("document-print")
    if icon.isNull():
        icon = _create_printer_icon(size)
    return icon


# ============================================================
# DATE PICKER (search + calendar + optional "Azi")
# ============================================================
def _parse_date_or_month(s: str):
    """Parseaza date or month."""
    if not s:
        return None, None

    t = s.strip().lower()
    if t in {"today", "azi"}:
        return "date", date.today()

    m = re.fullmatch(r"(\d{4})-(\d{2})", t)
    if m:
        y, mo = int(m.group(1)), int(m.group(2))
        if 1 <= mo <= 12:
            return "month", (y, mo)

    m = re.fullmatch(r"(\d{2})/(\d{4})", t)
    if m:
        mo, y = int(m.group(1)), int(m.group(2))
        if 1 <= mo <= 12:
            return "month", (y, mo)

    fmts = ["%Y-%m-%d", "%d.%m.%Y", "%d/%m/%Y", "%Y/%m/%d"]
    for f in fmts:
        try:
            d = datetime.strptime(t, f).date()
            return "date", d
        except Exception:
            pass

    return None, None


class DatePicker(QWidget):
    def __init__(self, placeholder="YYYY-MM-DD", show_today: bool = False):
        """Initializeaza clasa `DatePicker` si starea initiala necesara."""
        super().__init__()
        self.show_today = show_today

        lay = QHBoxLayout(self)
        lay.setContentsMargins(0, 0, 0, 0)
        lay.setSpacing(6)

        self.edit = QLineEdit()
        self.edit.setPlaceholderText(placeholder)

        self.btn = QPushButton("Alege")
        self.btn.setObjectName("secondary")
        self.btn.setToolTip("Deschide calendar (cu cautare)")
        # calendar icon (theme if available, fallback to standard)
        self.btn.setIcon(get_calendar_icon(20))
        self.btn.setMinimumHeight(30)
        self.btn.setMinimumWidth(84)
        self.btn.setIconSize(QSize(18, 18))
        self.btn.clicked.connect(self.open_dialog)

        lay.addWidget(self.edit, 1)
        lay.addWidget(self.btn, 0)

    def text(self) -> str:
        """Returneaza data selectata sub forma de text."""
        return self.edit.text().strip()

    def setText(self, s: str):
        """Seteaza data afisata in controlul DatePicker."""
        self.edit.setText("" if s is None else str(s))

    def clear(self):
        """Reseteaza controlul DatePicker la valoare vida."""
        self.edit.clear()

    def open_dialog(self):
        """Deschide dialog in `DatePicker`."""
        dlg = QDialog(self)
        dlg.setWindowTitle("Selecteaza data")
        dlg.setModal(True)

        v = QVBoxLayout(dlg)
        info = QLabel("Cauta: 2026-02-10 | 10.02.2026 | 02/2026 | today")
        info.setStyleSheet("color: gray;")
        v.addWidget(info)

        top_line = QHBoxLayout()
        search = QLineEdit()
        search.setPlaceholderText("Scrie o data/luna si apasa Enterâ€¦")
        top_line.addWidget(search, 1)

        if self.show_today:
            btn_today = QPushButton("Azi")
            btn_today.setToolTip("Seteaza data curenta")
            btn_today.setIcon(get_calendar_icon(32))
            btn_today.setIconSize(QSize(18, 18))
            btn_today.setObjectName("secondary")
            top_line.addWidget(btn_today, 0)
        else:
            btn_today = None

        v.addLayout(top_line)

        cal = QCalendarWidget()
        cal.setGridVisible(True)
        v.addWidget(cal)

        buttons = QDialogButtonBox(
            QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel
        )
        try:
            ok_btn = buttons.button(QDialogButtonBox.StandardButton.Ok)
            if ok_btn:
                apply_std_icon(ok_btn, QStyle.StandardPixmap.SP_DialogOkButton)
            cancel_btn = buttons.button(QDialogButtonBox.StandardButton.Cancel)
            if cancel_btn:
                apply_std_icon(cancel_btn, QStyle.StandardPixmap.SP_DialogCancelButton)
        except Exception:
            pass
        v.addWidget(buttons)

        # iniČ›ializare dupÄ valoarea existentÄ
        cur_txt = self.text()
        kind, val = _parse_date_or_month(cur_txt)
        if kind == "date":
            qd = QDate(val.year, val.month, val.day)
            cal.setSelectedDate(qd)
            cal.setCurrentPage(val.year, val.month)
        elif kind == "month":
            y, mo = val
            cal.setCurrentPage(y, mo)

        def do_search():
            """Gestioneaza search in `DatePicker`, ca helper intern in `open_dialog`."""
            kind2, val2 = _parse_date_or_month(search.text())
            if kind2 == "date":
                qd2 = QDate(val2.year, val2.month, val2.day)
                cal.setSelectedDate(qd2)
                cal.setCurrentPage(val2.year, val2.month)
            elif kind2 == "month":
                y2, mo2 = val2
                cal.setCurrentPage(y2, mo2)
            else:
                QMessageBox.warning(
                    dlg, "Format invalid",
                    "Exemple valide:\n"
                    "- 2026-02-10\n"
                    "- 10.02.2026\n"
                    "- 02/2026\n"
                    "- today"
                )

        search.returnPressed.connect(do_search)

        def accept_ok():
            """Gestioneaza ok in `DatePicker`, ca helper intern in `open_dialog`."""
            qd = cal.selectedDate()
            self.setText(qd.toString("yyyy-MM-dd"))
            dlg.accept()

        buttons.accepted.connect(accept_ok)
        buttons.rejected.connect(dlg.reject)

        if btn_today is not None:
            def set_today():
                """Seteaza today in `DatePicker`, ca helper intern in `open_dialog`."""
                qd = QDate.currentDate()
                self.setText(qd.toString("yyyy-MM-dd"))
                dlg.accept()
            btn_today.clicked.connect(set_today)

        dlg.resize(420, 380)
        dlg.exec()


class DateTimePicker(QWidget):
    def __init__(self, date_placeholder: str = "YYYY-MM-DD", show_today: bool = False):
        """Selector compus de data+ora; serializeaza in format YYYY-MM-DD HH:MM."""
        super().__init__()
        lay = QHBoxLayout(self)
        lay.setContentsMargins(0, 0, 0, 0)
        lay.setSpacing(6)

        self.date_picker = DatePicker(date_placeholder, show_today=show_today)
        self.time_edit = QLineEdit()
        self.time_edit.setPlaceholderText("HH:MM")
        self.time_edit.setMaximumWidth(82)
        self.time_edit.setToolTip("Ora in format HH:MM (optional)")
        self.time_edit.editingFinished.connect(self._normalize_time)

        lbl = QLabel("Ora:")
        lbl.setObjectName("muted")

        lay.addWidget(self.date_picker, 1)
        lay.addWidget(lbl, 0)
        lay.addWidget(self.time_edit, 0)

    @property
    def edit(self):
        """Expune QLineEdit-ul de data pentru compatibilitate cu DatePicker."""
        return self.date_picker.edit

    @property
    def btn(self):
        """Expune butonul calendar pentru compatibilitate cu DatePicker."""
        return self.date_picker.btn

    def _normalize_time(self):
        """Normalizeaza ora introdusa manual la HH:MM."""
        _, t = _split_ymd_hhmm(f"2000-01-01 {self.time_edit.text()}")
        self.time_edit.setText(t)

    def text(self) -> str:
        """Returneaza valoarea compusa (YYYY-MM-DD sau YYYY-MM-DD HH:MM)."""
        d = (self.date_picker.text() or "").strip()
        _, t = _split_ymd_hhmm(f"2000-01-01 {self.time_edit.text()}")
        if not d:
            return ""
        return f"{d} {t}" if t else d

    def setText(self, value: Optional[str]):
        """Seteaza data+ora dintr-un text compatibil."""
        d, t = _split_ymd_hhmm(value)
        self.date_picker.setText(d)
        self.time_edit.setText(t)

    def clear(self):
        """Curata data si ora."""
        self.date_picker.clear()
        self.time_edit.clear()


def wrap_selector_widget(widget: QWidget, parent: Optional[QWidget] = None, button_text: str = "Alege") -> QWidget:
    """Infasoara selector widget."""
    row = QWidget(parent)
    lay = QHBoxLayout(row)
    lay.setContentsMargins(0, 0, 0, 0)
    lay.setSpacing(6)
    lay.addWidget(widget, 1)

    # Pentru dropdown (QComboBox) nu mai afisam buton auxiliar.
    if isinstance(widget, QComboBox):
        return row

    btn = QPushButton(button_text)
    btn.setObjectName("secondary")
    btn.setMinimumWidth(84)
    apply_std_icon(btn, QStyle.StandardPixmap.SP_DialogOpenButton)
    lay.addWidget(btn, 0)

    if isinstance(widget, QSpinBox):
        try:
            widget.setButtonSymbols(QAbstractSpinBox.ButtonSymbols.NoButtons)
        except Exception:
            pass

    def _pick():
        """Deschide selectorul auxiliar si aplica valoarea aleasa (helper intern pentru `wrap_selector_widget`)."""
        try:
            if isinstance(widget, QComboBox):
                widget.setFocus()
                widget.showPopup()
                return
            if isinstance(widget, QSpinBox):
                current = int(widget.value())
                minimum = int(widget.minimum())
                maximum = int(widget.maximum())
                value, ok = QInputDialog.getInt(
                    row,
                    "Alege valoare",
                    "Valoare:",
                    current,
                    minimum,
                    maximum,
                    1,
                )
                if ok:
                    widget.setValue(value)
                return
            widget.setFocus()
        except Exception:
            pass

    btn.clicked.connect(_pick)
    return row


# ============================================================
# Thread Worker (cancel real)
# ============================================================
class Worker(QObject):
    progress = pyqtSignal(int, str)   # percent, message
    finished = pyqtSignal(object)     # result
    error = pyqtSignal(str)
    cancelled = pyqtSignal()

    def __init__(self, fn, *args, **kwargs):
        """Initializeaza clasa `Worker` si starea initiala necesara."""
        super().__init__()
        self.fn = fn
        self.args = args
        self.kwargs = kwargs
        self._cancel_event = threading.Event()

    def cancel(self):
        """Marcheaza worker-ul ca anulat, pentru oprire cooperativa."""
        self._cancel_event.set()

    def is_cancelled(self) -> bool:
        """Verifica daca cancelled in `Worker`."""
        return self._cancel_event.is_set()

    def run(self):
        """Executa functia worker-ului pe thread separat si emite semnalele de rezultat."""
        try:
            call_kwargs = dict(self.kwargs)

            # Injectam callback-uri doar daca functia tinta le accepta.
            accepts_progress = False
            accepts_cancelled = False
            try:
                sig = inspect.signature(self.fn)
                params = sig.parameters
                accepts_any_kwargs = any(p.kind == inspect.Parameter.VAR_KEYWORD for p in params.values())
                accepts_progress = accepts_any_kwargs or ("progress_cb" in params)
                accepts_cancelled = accepts_any_kwargs or ("cancelled_cb" in params)
            except Exception:
                accepts_progress = "progress_cb" in call_kwargs
                accepts_cancelled = "cancelled_cb" in call_kwargs

            if "progress_cb" not in call_kwargs and accepts_progress:
                call_kwargs["progress_cb"] = lambda p, m="": self.progress.emit(int(p), str(m))
            if "cancelled_cb" not in call_kwargs and accepts_cancelled:
                call_kwargs["cancelled_cb"] = self.is_cancelled

            try:
                res = self.fn(*self.args, **call_kwargs)
            except TypeError as e:
                # Fallback defensiv pentru functii care resping keyword-uri injectate.
                msg = str(e)
                if "unexpected keyword argument" in msg and ("'progress_cb'" in msg or "'cancelled_cb'" in msg):
                    call_kwargs.pop("progress_cb", None)
                    call_kwargs.pop("cancelled_cb", None)
                    res = self.fn(*self.args, **call_kwargs)
                else:
                    raise

            if self.is_cancelled():
                self.cancelled.emit()
                return

            self.finished.emit(res)
        except Exception as e:
            self.error.emit(str(e))
# ============================================================
# DB
# ============================================================
def get_conn():
    """Deschide si returneaza conexiunea SQLite catre baza locala a aplicatiei."""
    conn = sqlite3.connect(DB_PATH, timeout=10)
    conn.row_factory = sqlite3.Row
    conn.text_factory = _sqlite_text_to_ascii
    conn.execute("PRAGMA journal_mode=WAL;")
    conn.execute("PRAGMA synchronous=NORMAL;")
    conn.execute("PRAGMA busy_timeout=10000;")
    conn.execute("PRAGMA foreign_keys=ON;")
    conn.execute("PRAGMA temp_store=MEMORY;")
    conn.execute("PRAGMA cache_size=-20000;")  # ~20MB
    return conn


def _is_secret_setting_key(key: str) -> bool:
    """Verifica daca secret setting key."""
    k = (key or "").strip().lower()
    if not k:
        return False
    if k in SETTINGS_SECRET_KEYS:
        return True
    if k.startswith("secret::"):
        return True
    return False


if os.name == "nt":
    class _DpapiBlob(ctypes.Structure):
        _fields_ = [
            ("cbData", wintypes.DWORD),
            ("pbData", ctypes.POINTER(ctypes.c_ubyte)),
        ]


    _CRYPT32 = ctypes.WinDLL("Crypt32.dll")
    _KERNEL32 = ctypes.WinDLL("Kernel32.dll")
    _CRYPTPROTECT_UI_FORBIDDEN = 0x01
    _CRYPT32.CryptProtectData.argtypes = [
        ctypes.POINTER(_DpapiBlob),
        wintypes.LPCWSTR,
        ctypes.POINTER(_DpapiBlob),
        ctypes.c_void_p,
        ctypes.c_void_p,
        wintypes.DWORD,
        ctypes.POINTER(_DpapiBlob),
    ]
    _CRYPT32.CryptProtectData.restype = wintypes.BOOL
    _CRYPT32.CryptUnprotectData.argtypes = [
        ctypes.POINTER(_DpapiBlob),
        ctypes.POINTER(wintypes.LPWSTR),
        ctypes.POINTER(_DpapiBlob),
        ctypes.c_void_p,
        ctypes.c_void_p,
        wintypes.DWORD,
        ctypes.POINTER(_DpapiBlob),
    ]
    _CRYPT32.CryptUnprotectData.restype = wintypes.BOOL
    _KERNEL32.LocalFree.argtypes = [ctypes.c_void_p]
    _KERNEL32.LocalFree.restype = ctypes.c_void_p


def _dpapi_encrypt(raw: bytes) -> bytes:
    """Cripteaza date sensibile local folosind DPAPI pe Windows."""
    if os.name != "nt":
        return raw
    if raw is None:
        return b""
    if not raw:
        return b""
    in_buf = ctypes.create_string_buffer(raw, len(raw))
    in_blob = _DpapiBlob(
        cbData=len(raw),
        pbData=ctypes.cast(in_buf, ctypes.POINTER(ctypes.c_ubyte)),
    )
    out_blob = _DpapiBlob()
    ok = _CRYPT32.CryptProtectData(
        ctypes.byref(in_blob),
        None,
        None,
        None,
        None,
        _CRYPTPROTECT_UI_FORBIDDEN,
        ctypes.byref(out_blob),
    )
    if not ok:
        raise ctypes.WinError()
    try:
        return ctypes.string_at(out_blob.pbData, out_blob.cbData)
    finally:
        if out_blob.pbData:
            _KERNEL32.LocalFree(out_blob.pbData)


def _dpapi_decrypt(raw: bytes) -> bytes:
    """Decripteaza date stocate local prin DPAPI pe Windows."""
    if os.name != "nt":
        return raw
    if raw is None:
        return b""
    if not raw:
        return b""
    in_buf = ctypes.create_string_buffer(raw, len(raw))
    in_blob = _DpapiBlob(
        cbData=len(raw),
        pbData=ctypes.cast(in_buf, ctypes.POINTER(ctypes.c_ubyte)),
    )
    out_blob = _DpapiBlob()
    ok = _CRYPT32.CryptUnprotectData(
        ctypes.byref(in_blob),
        None,
        None,
        None,
        None,
        _CRYPTPROTECT_UI_FORBIDDEN,
        ctypes.byref(out_blob),
    )
    if not ok:
        raise ctypes.WinError()
    try:
        return ctypes.string_at(out_blob.pbData, out_blob.cbData)
    finally:
        if out_blob.pbData:
            _KERNEL32.LocalFree(out_blob.pbData)


def _encode_setting_for_storage(key: str, value: Optional[str]) -> Optional[str]:
    """Gestioneaza setting for storage."""
    if value is None:
        return None
    raw = to_ascii_text(value) or ""
    if not raw:
        return raw
    if not _is_secret_setting_key(key):
        return raw
    if raw.startswith(SETTINGS_SECRET_PREFIX):
        return raw
    if os.name != "nt":
        return raw
    try:
        enc = _dpapi_encrypt(raw.encode("utf-8"))
        return SETTINGS_SECRET_PREFIX + base64.urlsafe_b64encode(enc).decode("ascii")
    except Exception:
        # Fallback safely to plain text if DPAPI is not available.
        return raw


def _decode_setting_from_storage(key: str, value: Optional[str], default: Optional[str] = None) -> Optional[str]:
    """Gestioneaza setting from storage."""
    if value is None:
        return default
    raw = str(value)
    if raw.startswith(SETTINGS_SECRET_PREFIX):
        enc = raw[len(SETTINGS_SECRET_PREFIX):]
        if not enc:
            return ""
        try:
            blob = base64.urlsafe_b64decode(enc.encode("ascii"))
            dec = _dpapi_decrypt(blob)
            return dec.decode("utf-8", errors="ignore")
        except Exception:
            return default
    return raw


def get_setting(key: str, default: Optional[str] = None) -> Optional[str]:
    """Citeste o setare aplicatie din tabela de configurare."""
    try:
        # Path rapid de citire: nu folosim get_conn() aici ca sa evitam
        # PRAGMA-uri grele pe fiecare apel si blocari UI in caz de lock.
        conn = sqlite3.connect(DB_PATH, timeout=0.4)
        conn.row_factory = sqlite3.Row
        conn.text_factory = _sqlite_text_to_ascii
        cur = conn.cursor()
        try:
            cur.execute("SELECT value FROM app_settings WHERE key=?", (key,))
        except sqlite3.OperationalError as e:
            # La prima rulare tabela poate sa nu existe inca.
            if "no such table" in str(e).lower():
                conn.close()
                return default
            raise
        row = cur.fetchone()
        conn.close()
        if row is None:
            return default
        stored = row["value"]
        value = _decode_setting_from_storage(key, stored, default)
        # Auto-migrate legacy plain secret values to DPAPI format on Windows.
        if (
            os.name == "nt"
            and _is_secret_setting_key(key)
            and isinstance(stored, str)
            and stored
            and not stored.startswith(SETTINGS_SECRET_PREFIX)
            and value not in (None, "")
        ):
            try:
                set_setting(key, value)
            except Exception:
                pass
        return value
    except Exception:
        return default


def set_setting(key: str, value: Optional[str]):
    """Salveaza sau actualizeaza o setare aplicatie in baza locala."""
    try:
        key = to_ascii_text(key) or ""
        value = _encode_setting_for_storage(key, value)
        conn = get_conn()
        cur = conn.cursor()
        cur.execute("CREATE TABLE IF NOT EXISTS app_settings (key TEXT PRIMARY KEY, value TEXT)")
        cur.execute("INSERT OR REPLACE INTO app_settings(key, value) VALUES (?,?)", (key, value))
        conn.commit()
        conn.close()
    except Exception:
        pass


def delete_settings_by_prefix(prefix: str) -> int:
    """Sterge settings by prefix."""
    try:
        conn = get_conn()
        cur = conn.cursor()
        cur.execute("CREATE TABLE IF NOT EXISTS app_settings (key TEXT PRIMARY KEY, value TEXT)")
        cur.execute("DELETE FROM app_settings WHERE key LIKE ?", (f"{prefix}%",))
        removed = int(cur.rowcount or 0)
        conn.commit()
        conn.close()
        return removed
    except Exception:
        return 0


def delete_setting(key: str) -> bool:
    """Sterge o setare aplicatie dupa cheia furnizata."""
    try:
        conn = get_conn()
        cur = conn.cursor()
        cur.execute("CREATE TABLE IF NOT EXISTS app_settings (key TEXT PRIMARY KEY, value TEXT)")
        cur.execute("DELETE FROM app_settings WHERE key=?", (key,))
        removed = int(cur.rowcount or 0)
        conn.commit()
        conn.close()
        return removed > 0
    except Exception:
        return False


_CURRENT_USER_CACHE: Optional[str] = None
_CURRENT_ROLE_CACHE: Optional[str] = None
_CURRENT_USER_FULL_NAME_CACHE: Optional[str] = None


def get_current_user() -> str:
    """Returneaza current user."""
    global _CURRENT_USER_CACHE
    cached = (_CURRENT_USER_CACHE or "").strip()
    if cached:
        return cached
    user = (get_setting("current_user", DEFAULT_USER) or DEFAULT_USER).strip() or DEFAULT_USER
    _CURRENT_USER_CACHE = user
    return user


def get_current_user_full_name() -> str:
    """Returneaza current user full name."""
    global _CURRENT_USER_FULL_NAME_CACHE
    cached_mem = (_CURRENT_USER_FULL_NAME_CACHE or "").strip()
    if cached_mem:
        return cached_mem
    cached = (get_setting("current_user_full_name", "") or "").strip()
    if cached:
        _CURRENT_USER_FULL_NAME_CACHE = cached
        return cached
    try:
        row = get_user(get_current_user())
        full_name = ((row or {}).get("full_name") or "").strip() if row else ""
        if full_name:
            set_setting("current_user_full_name", full_name)
            _CURRENT_USER_FULL_NAME_CACHE = full_name
            return full_name
    except Exception:
        pass
    fallback = get_current_user()
    _CURRENT_USER_FULL_NAME_CACHE = fallback
    return fallback


def get_current_role() -> str:
    """Returneaza current role."""
    global _CURRENT_ROLE_CACHE
    cached = (_CURRENT_ROLE_CACHE or "").strip()
    if cached in ROLE_CHOICES:
        return cached
    role = (get_setting("current_role", DEFAULT_ROLE) or DEFAULT_ROLE).strip() or DEFAULT_ROLE
    if role not in ROLE_CHOICES:
        role = DEFAULT_ROLE
    _CURRENT_ROLE_CACHE = role
    return role


def set_current_user_role(user: str, role: str, full_name: Optional[str] = None):
    """Seteaza current user role."""
    global _CURRENT_USER_CACHE, _CURRENT_ROLE_CACHE, _CURRENT_USER_FULL_NAME_CACHE
    user_txt = (user or DEFAULT_USER).strip() or DEFAULT_USER
    role_txt = (role or DEFAULT_ROLE).strip() or DEFAULT_ROLE
    if role_txt not in ROLE_CHOICES:
        role_txt = DEFAULT_ROLE
    set_setting("current_user", user_txt)
    set_setting("current_role", role_txt)
    display_name = (full_name or "").strip()
    if not display_name:
        try:
            row = get_user(user)
            display_name = ((row or {}).get("full_name") or "").strip() if row else ""
        except Exception:
            display_name = ""
    display_name = display_name or user_txt
    set_setting("current_user_full_name", display_name)
    _CURRENT_USER_CACHE = user_txt
    _CURRENT_ROLE_CACHE = role_txt
    _CURRENT_USER_FULL_NAME_CACHE = display_name


def _hash_password(username: str, password: str) -> str:
    """Calculeaza hash-ul parolei folosind username-ul ca parte din salt."""
    u = (username or "").strip().lower()
    p = (password or "").strip()
    return hashlib.sha256(f"{u}:{p}".encode("utf-8")).hexdigest()


def upsert_user(username: str, password: Optional[str], role: str, active: int = 1, full_name: Optional[str] = None):
    """Insereaza sau actualizeaza un utilizator in tabela `users`."""
    if not username:
        return
    full_name = (full_name or "").strip()
    has_sync = table_has_column("users", "sync_id")
    has_updated = table_has_column("users", "updated_at")
    has_deleted = table_has_column("users", "deleted")
    has_device = table_has_column("users", "device_id")
    has_full_name = table_has_column("users", "full_name")
    conn = get_conn()
    cur = conn.cursor()
    if has_sync:
        cur.execute("SELECT id, password_hash, sync_id FROM users WHERE username=?", (username,))
    else:
        cur.execute("SELECT id, password_hash FROM users WHERE username=?", (username,))
    row = cur.fetchone()
    pwd_hash = _hash_password(username, password) if password else None
    updated_at = now_ts()
    device_id = get_device_id()
    if row:
        sync_id = row[2] if has_sync else None
        if has_sync and not sync_id:
            sync_id = uuid.uuid4().hex
        sets = []
        vals = []
        if pwd_hash:
            sets.append("password_hash=?")
            vals.append(pwd_hash)
        sets.append("role=?")
        vals.append(role)
        sets.append("active=?")
        vals.append(active)
        if has_full_name:
            sets.append("full_name=?")
            vals.append(full_name or username)
        if has_updated:
            sets.append("updated_at=?")
            vals.append(updated_at)
        if has_device:
            sets.append("device_id=?")
            vals.append(device_id)
        if has_deleted:
            sets.append("deleted=0")
        if has_sync:
            sets.append("sync_id=?")
            vals.append(sync_id)
        vals.append(username)
        cur.execute(f"UPDATE users SET {', '.join(sets)} WHERE username=?", vals)
    else:
        cols = ["username", "password_hash", "role", "active"]
        vals = [username, pwd_hash or "", role, active]
        if has_full_name:
            cols.append("full_name")
            vals.append(full_name or username)
        if has_sync:
            cols.append("sync_id")
            vals.append(uuid.uuid4().hex)
        if has_updated:
            cols.append("updated_at")
            vals.append(updated_at)
        if has_deleted:
            cols.append("deleted")
            vals.append(0)
        if has_device:
            cols.append("device_id")
            vals.append(device_id)
        cur.execute(
            f"INSERT INTO users({', '.join(cols)}) VALUES ({', '.join(['?']*len(cols))})",
            vals,
        )
    conn.commit()
    conn.close()


def get_user(username: str) -> Optional[Dict[str, Any]]:
    """Returneaza datele unui utilizator dupa username."""
    if not username:
        return None
    conn = get_conn()
    cur = conn.cursor()
    if table_has_column("users", "deleted"):
        cur.execute("SELECT * FROM users WHERE username=? AND COALESCE(deleted,0)=0", (username,))
    else:
        cur.execute("SELECT * FROM users WHERE username=?", (username,))
    row = cur.fetchone()
    conn.close()
    return dict(row) if row else None


def validate_login(username: str, password: str) -> Optional[Dict[str, Any]]:
    """Valideaza credentialele si returneaza utilizatorul activ la autentificare reusita."""
    u = (username or "").strip()
    if not u:
        return None
    row = get_user(u)
    if not row:
        return None
    if row.get("active", 1) != 1:
        return None
    if _hash_password(u, password) != (row.get("password_hash") or ""):
        return None
    return row


def ensure_default_admin_user():
    """Asigura default admin user."""
    if not get_user("behemoth2000"):
        upsert_user("behemoth2000", "8Cdd5735", "admin", 1, "Administrator")


def list_users() -> List[Dict[str, Any]]:
    """Returneaza lista de utilizatori disponibili pentru administrare."""
    conn = get_conn()
    cur = conn.cursor()
    has_deleted = table_has_column("users", "deleted")
    has_full_name = table_has_column("users", "full_name")
    if has_deleted and has_full_name:
        cur.execute("SELECT username, full_name, role, active FROM users WHERE COALESCE(deleted,0)=0 ORDER BY username COLLATE NOCASE ASC")
    elif has_deleted and not has_full_name:
        cur.execute("SELECT username, '' AS full_name, role, active FROM users WHERE COALESCE(deleted,0)=0 ORDER BY username COLLATE NOCASE ASC")
    elif (not has_deleted) and has_full_name:
        cur.execute("SELECT username, full_name, role, active FROM users ORDER BY username COLLATE NOCASE ASC")
    else:
        cur.execute("SELECT username, '' AS full_name, role, active FROM users ORDER BY username COLLATE NOCASE ASC")
    rows = [dict(r) for r in cur.fetchall()]
    conn.close()
    return rows


def _user_permissions_setting_key(username: str) -> str:
    """Gestioneaza permissions setting key."""
    return f"user_permissions::{(username or '').strip().lower()}"


def get_user_allowed_features(username: str) -> set:
    """Returneaza user allowed features."""
    uname = (username or "").strip()
    if not uname:
        return set(FEATURE_PERMISSION_DEFAULTS)
    raw = (get_setting(_user_permissions_setting_key(uname), "") or "").strip()
    if not raw:
        return set(FEATURE_PERMISSION_DEFAULTS)
    try:
        payload = json.loads(raw)
        if isinstance(payload, list):
            allowed = {
                str(item).strip()
                for item in payload
                if isinstance(item, str) and str(item).strip() in FEATURE_PERMISSION_DEFAULTS
            }
            if allowed:
                return allowed
    except Exception:
        pass
    return set(FEATURE_PERMISSION_DEFAULTS)


def set_user_allowed_features(username: str, allowed_features: set):
    """Seteaza user allowed features."""
    uname = (username or "").strip()
    if not uname:
        return
    clean = sorted(
        [k for k in (allowed_features or set()) if k in FEATURE_PERMISSION_DEFAULTS],
        key=lambda x: x.lower(),
    )
    set_setting(_user_permissions_setting_key(uname), json.dumps(clean, ensure_ascii=False))


def is_feature_allowed(username: str, feature_key: str) -> bool:
    """Verifica daca feature allowed."""
    key = (feature_key or "").strip()
    if not key:
        return True
    row = get_user(username)
    role = ((row or {}).get("role") or "").strip().lower()
    if role == "admin":
        return True
    allowed = get_user_allowed_features(username)
    return key in allowed


def is_feature_allowed_for_current_user(feature_key: str) -> bool:
    """Verifica daca feature allowed for current user."""
    return is_feature_allowed(get_current_user(), feature_key)


def get_medic_dropdown_values() -> List[str]:
    """Returneaza medic dropdown values."""
    seen: Dict[str, str] = {}
    for row in list_users():
        role = (row.get("role") or "").strip().lower()
        if role != "medic":
            continue
        try:
            if int(row.get("active", 1) or 0) != 1:
                continue
        except Exception:
            continue
        display_name = ((row.get("full_name") or "").strip() or (row.get("username") or "").strip())
        if not display_name:
            continue
        seen.setdefault(display_name.casefold(), display_name)
    return sorted(seen.values(), key=lambda value: value.casefold())


def get_clinic_settings() -> Dict[str, str]:
    """Returneaza clinic settings."""
    return {
        "clinic_name": get_setting("clinic_name", "Clinica"),
        "clinic_address": get_setting("clinic_address", ""),
        "clinic_phone": get_setting("clinic_phone", ""),
        "clinic_logo": get_setting("clinic_logo", ""),
        "category_name_match_threshold": get_setting("category_name_match_threshold", f"{CATEGORY_NAME_MATCH_THRESHOLD:.2f}"),
    }


def set_clinic_settings(data: Dict[str, str]):
    """Seteaza clinic settings."""
    set_setting("clinic_name", data.get("clinic_name") or "")
    set_setting("clinic_address", data.get("clinic_address") or "")
    set_setting("clinic_phone", data.get("clinic_phone") or "")
    set_setting("clinic_logo", data.get("clinic_logo") or "")
    thr = (data.get("category_name_match_threshold") or "").strip()
    if not thr:
        thr = f"{CATEGORY_NAME_MATCH_THRESHOLD:.2f}"
    try:
        fv = float(thr)
        fv = max(0.5, min(1.0, fv))
        set_setting("category_name_match_threshold", f"{fv:.2f}")
    except Exception:
        set_setting("category_name_match_threshold", f"{CATEGORY_NAME_MATCH_THRESHOLD:.2f}")


def get_category_name_match_threshold() -> float:
    """Returneaza category name match threshold."""
    raw = (get_setting("category_name_match_threshold", f"{CATEGORY_NAME_MATCH_THRESHOLD:.2f}") or "").strip()
    try:
        val = float(raw)
    except Exception:
        val = CATEGORY_NAME_MATCH_THRESHOLD
    return max(0.5, min(1.0, val))


def get_current_location_id() -> Optional[int]:
    """Returneaza current location ID."""
    v = get_setting("current_location_id", "")
    if not v:
        return None
    try:
        return int(v)
    except Exception:
        return None


def set_current_location_id(loc_id: Optional[int]):
    """Seteaza current location ID."""
    if loc_id is None:
        set_setting("current_location_id", "")
    else:
        set_setting("current_location_id", str(int(loc_id)))


def now_ts() -> str:
    """Returneaza timestamp-ul curent in format compatibil cu baza de date."""
    return datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S")


def get_device_id() -> str:
    """Returneaza device ID."""
    did = get_setting("device_id", "")
    if did:
        return did
    did = uuid.uuid4().hex
    set_setting("device_id", did)
    return did


_TABLE_COL_CACHE: Dict[str, List[str]] = {}


def get_table_columns(table: str) -> List[str]:
    """Returneaza table columns."""
    if table in _TABLE_COL_CACHE:
        return _TABLE_COL_CACHE[table]
    conn = get_conn()
    cur = conn.cursor()
    cur.execute(f"PRAGMA table_info({table})")
    cols = [row[1] for row in cur.fetchall()]
    conn.close()
    _TABLE_COL_CACHE[table] = cols
    return cols


def table_has_column(table: str, col: str) -> bool:
    """Gestioneaza has column."""
    return col in get_table_columns(table)


def table_exists(table: str) -> bool:
    """Verifica daca tabela exista in baza de date locala."""
    try:
        conn = get_conn()
        cur = conn.cursor()
        cur.execute("SELECT 1 FROM sqlite_master WHERE type='table' AND name=?", (table,))
        ok = cur.fetchone() is not None
        conn.close()
        return ok
    except Exception:
        return False


def ensure_recycle_bin_tables(conn: Optional[sqlite3.Connection] = None):
    """Asigura recycle bin tables."""
    own_conn = conn is None
    c = conn or get_conn()
    cur = c.cursor()
    cur.execute(
        f"""
        CREATE TABLE IF NOT EXISTS {RECYCLE_BIN_SNAPSHOTS_TABLE} (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            created_at TEXT,
            action TEXT,
            segment_keys TEXT,
            include_system INTEGER,
            source_user TEXT,
            source_role TEXT,
            total_rows INTEGER,
            restored_at TEXT,
            restored_by TEXT,
            details TEXT
        )
        """
    )
    cur.execute(
        f"""
        CREATE TABLE IF NOT EXISTS {RECYCLE_BIN_ITEMS_TABLE} (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            snapshot_id INTEGER NOT NULL,
            table_name TEXT NOT NULL,
            row_json TEXT,
            FOREIGN KEY(snapshot_id) REFERENCES {RECYCLE_BIN_SNAPSHOTS_TABLE}(id) ON DELETE CASCADE
        )
        """
    )
    cur.execute(
        f"CREATE INDEX IF NOT EXISTS idx_recycle_items_snapshot ON {RECYCLE_BIN_ITEMS_TABLE}(snapshot_id)"
    )
    cur.execute(
        f"CREATE INDEX IF NOT EXISTS idx_recycle_items_table ON {RECYCLE_BIN_ITEMS_TABLE}(table_name)"
    )
    if own_conn:
        c.commit()
        c.close()


def list_recycle_snapshots(limit: int = 200) -> List[Dict[str, Any]]:
    """Listeaza recycle snapshots."""
    ensure_recycle_bin_tables()
    conn = get_conn()
    cur = conn.cursor()
    cur.execute(
        f"""
        SELECT
            s.id,
            s.created_at,
            s.action,
            s.segment_keys,
            s.include_system,
            s.source_user,
            s.source_role,
            s.total_rows,
            s.restored_at,
            s.restored_by,
            s.details,
            COUNT(i.id) AS item_count
        FROM {RECYCLE_BIN_SNAPSHOTS_TABLE} s
        LEFT JOIN {RECYCLE_BIN_ITEMS_TABLE} i ON i.snapshot_id = s.id
        GROUP BY s.id
        ORDER BY s.id DESC
        LIMIT ?
        """,
        (int(limit),),
    )
    rows = [dict(r) for r in cur.fetchall()]
    conn.close()
    return rows


def get_recycle_snapshot_table_counts(snapshot_id: int) -> Dict[str, int]:
    """Returneaza recycle snapshot table counts."""
    ensure_recycle_bin_tables()
    conn = get_conn()
    cur = conn.cursor()
    cur.execute(
        f"""
        SELECT table_name, COUNT(*)
        FROM {RECYCLE_BIN_ITEMS_TABLE}
        WHERE snapshot_id=?
        GROUP BY table_name
        ORDER BY table_name
        """,
        (int(snapshot_id),),
    )
    out = {str(r[0]): int(r[1]) for r in cur.fetchall()}
    conn.close()
    return out


def delete_recycle_snapshots(snapshot_ids: List[int]) -> Dict[str, int]:
    """Sterge recycle snapshots."""
    ensure_recycle_bin_tables()
    ids = []
    for sid in (snapshot_ids or []):
        try:
            v = int(sid)
            if v > 0:
                ids.append(v)
        except Exception:
            pass
    ids = sorted(set(ids))
    if not ids:
        return {"snapshots": 0, "items": 0}

    conn = get_conn()
    cur = conn.cursor()
    deleted_items = 0
    deleted_snapshots = 0
    try:
        for sid in ids:
            cur.execute(f"SELECT COUNT(*) FROM {RECYCLE_BIN_ITEMS_TABLE} WHERE snapshot_id=?", (sid,))
            row = cur.fetchone()
            deleted_items += int(row[0] if row and row[0] is not None else 0)

            cur.execute(f"DELETE FROM {RECYCLE_BIN_ITEMS_TABLE} WHERE snapshot_id=?", (sid,))
            cur.execute(f"DELETE FROM {RECYCLE_BIN_SNAPSHOTS_TABLE} WHERE id=?", (sid,))
            if int(cur.rowcount or 0) > 0:
                deleted_snapshots += 1

        conn.commit()
    finally:
        conn.close()

    return {"snapshots": int(deleted_snapshots), "items": int(deleted_items)}


def get_cleanup_tables_for_segments(segment_keys: List[str], include_system: bool = False) -> List[str]:
    """Returneaza cleanup tables for segments."""
    seg_map = {k: tables for k, _label, tables in DB_CLEANUP_SEGMENTS}
    ordered: List[str] = []
    seen = set()

    if "all" in segment_keys:
        keys = [k for k, _label, _tables in DB_CLEANUP_SEGMENTS]
    else:
        keys = list(segment_keys or [])

    for k in keys:
        for t in seg_map.get(k, []):
            if t not in seen:
                ordered.append(t)
                seen.add(t)

    if include_system:
        for t in ["users", "app_settings"]:
            if t not in seen:
                ordered.append(t)
                seen.add(t)

    return ordered


def cleanup_local_database_segments(
    segment_keys: List[str],
    include_system: bool = False,
    action: str = "cleanup_database",
) -> Tuple[Dict[str, int], Optional[int]]:
    """Gestioneaza local database segments."""
    tables = get_cleanup_tables_for_segments(segment_keys, include_system=include_system)
    counts: Dict[str, int] = {}
    if not tables:
        return counts, None

    conn = get_conn()
    cur = conn.cursor()
    snapshot_id: Optional[int] = None
    try:
        ensure_recycle_bin_tables(conn)
        cur.execute(
            f"""
            INSERT INTO {RECYCLE_BIN_SNAPSHOTS_TABLE}
                (created_at, action, segment_keys, include_system, source_user, source_role, total_rows, details)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?)
            """,
            (
                now_ts(),
                action,
                json.dumps(list(segment_keys or []), ensure_ascii=False),
                1 if include_system else 0,
                get_current_user(),
                get_current_role(),
                0,
                "",
            ),
        )
        snapshot_id = int(cur.lastrowid)

        total_rows = 0
        for table in tables:
            cur.execute("SELECT 1 FROM sqlite_master WHERE type='table' AND name=?", (table,))
            if cur.fetchone() is None:
                continue
            try:
                cur.execute(f"SELECT * FROM {table}")
                rows = cur.fetchall()
                col_names = [d[0] for d in (cur.description or [])]
                counts[table] = int(len(rows))
                total_rows += counts[table]

                if snapshot_id is not None and rows and col_names:
                    for r in rows:
                        row_obj = {col_names[idx]: r[idx] for idx in range(len(col_names))}
                        cur.execute(
                            f"INSERT INTO {RECYCLE_BIN_ITEMS_TABLE}(snapshot_id, table_name, row_json) VALUES (?,?,?)",
                            (snapshot_id, table, json.dumps(row_obj, ensure_ascii=False, default=str)),
                        )
            except Exception:
                counts[table] = 0
            cur.execute(f"DELETE FROM {table}")

        if snapshot_id is not None:
            cur.execute(
                f"UPDATE {RECYCLE_BIN_SNAPSHOTS_TABLE} SET total_rows=? WHERE id=?",
                (int(total_rows), int(snapshot_id)),
            )
        conn.commit()
    finally:
        conn.close()

    try:
        conn2 = get_conn()
        conn2.execute("VACUUM")
        conn2.close()
    except Exception:
        pass

    return counts, snapshot_id


def restore_recycle_snapshot(snapshot_id: int) -> Dict[str, int]:
    """Restaureaza recycle snapshot."""
    ensure_recycle_bin_tables()
    conn = get_conn()
    cur = conn.cursor()
    restored: Dict[str, int] = {}
    table_cols: Dict[str, List[str]] = {}
    try:
        cur.execute(f"SELECT id FROM {RECYCLE_BIN_SNAPSHOTS_TABLE} WHERE id=?", (int(snapshot_id),))
        if cur.fetchone() is None:
            return restored

        cur.execute(
            f"SELECT table_name, row_json FROM {RECYCLE_BIN_ITEMS_TABLE} WHERE snapshot_id=? ORDER BY id ASC",
            (int(snapshot_id),),
        )
        items = cur.fetchall()

        for row in items:
            table_name = str(row[0] or "").strip()
            payload = row[1]
            if not table_name or payload is None:
                continue
            cur.execute("SELECT 1 FROM sqlite_master WHERE type='table' AND name=?", (table_name,))
            if cur.fetchone() is None:
                continue

            if table_name not in table_cols:
                cur.execute(f"PRAGMA table_info({table_name})")
                table_cols[table_name] = [c[1] for c in cur.fetchall()]
            valid_cols = table_cols.get(table_name, [])
            if not valid_cols:
                continue

            try:
                obj = json.loads(payload)
            except Exception:
                continue
            if not isinstance(obj, dict):
                continue

            cols = [c for c in valid_cols if c in obj]
            if not cols:
                continue
            placeholders = ", ".join(["?"] * len(cols))
            values = [obj.get(c) for c in cols]
            cur.execute(
                f"INSERT OR REPLACE INTO {table_name} ({', '.join(cols)}) VALUES ({placeholders})",
                values,
            )
            restored[table_name] = int(restored.get(table_name, 0)) + 1

        cur.execute(
            f"UPDATE {RECYCLE_BIN_SNAPSHOTS_TABLE} SET restored_at=?, restored_by=? WHERE id=?",
            (now_ts(), get_current_user(), int(snapshot_id)),
        )
        conn.commit()
    finally:
        conn.close()

    try:
        conn2 = get_conn()
        conn2.execute("VACUUM")
        conn2.close()
    except Exception:
        pass

    return restored


def ensure_sync_columns(table: str):
    """Asigura sync columns."""
    conn = get_conn()
    cur = conn.cursor()
    cur.execute(f"PRAGMA table_info({table})")
    cols = {row[1] for row in cur.fetchall()}

    def add_col(name: str, sql_type: str):
        """Adauga col ca helper intern in `ensure_sync_columns`."""
        if name not in cols:
            cur.execute(f"ALTER TABLE {table} ADD COLUMN {name} {sql_type}")
            cols.add(name)

    add_col("sync_id", "TEXT")
    add_col("updated_at", "TEXT")
    add_col("deleted", "INTEGER")
    add_col("device_id", "TEXT")

    # fill missing values
    try:
        cur.execute(f"SELECT rowid, sync_id, updated_at, deleted, device_id FROM {table}")
        rows = cur.fetchall()
        for r in rows:
            rowid = r[0]
            sync_id = r[1]
            updated_at = r[2]
            deleted = r[3]
            device_id = r[4]
            updates = []
            vals = []
            if not sync_id:
                updates.append("sync_id=?")
                vals.append(uuid.uuid4().hex)
            if not updated_at:
                updates.append("updated_at=?")
                vals.append(now_ts())
            if deleted is None:
                updates.append("deleted=?")
                vals.append(0)
            if not device_id:
                updates.append("device_id=?")
                vals.append(get_device_id())
            if updates:
                vals.append(rowid)
                cur.execute(f"UPDATE {table} SET {', '.join(updates)} WHERE rowid=?", vals)
    except Exception:
        pass

    conn.commit()
    conn.close()
    _TABLE_COL_CACHE.pop(table, None)


def init_sync_schema():
    """Initializeaza sync schema."""
    for cfg in SYNC_TABLES:
        try:
            ensure_sync_columns(cfg["table"])
        except Exception:
            pass


def get_supabase_access_token() -> str:
    """Returneaza Supabase access token."""
    try:
        tok = get_setting("supabase_access_token", "") or ""
        exp = int(get_setting("supabase_token_expires_at", "0") or 0)
        if tok and exp and int(time.time()) > exp:
            rt = get_setting("supabase_refresh_token", "") or ""
            if rt:
                try:
                    supabase_auth_refresh(rt)
                    tok = get_setting("supabase_access_token", "") or tok
                except Exception:
                    pass
        return tok
    except Exception:
        return ""


def set_supabase_tokens(access: str, refresh: str, email: str = "", expires_in: int = 3600):
    """Seteaza Supabase tokens."""
    set_setting("supabase_access_token", access or "")
    set_setting("supabase_refresh_token", refresh or "")
    set_setting("supabase_user_email", email or "")
    try:
        exp = int(time.time()) + max(60, int(expires_in) - 30)
        set_setting("supabase_token_expires_at", str(exp))
    except Exception:
        pass


def clear_supabase_tokens():
    """Curata Supabase tokens."""
    set_setting("supabase_access_token", "")
    set_setting("supabase_refresh_token", "")
    set_setting("supabase_user_email", "")
    set_setting("supabase_token_expires_at", "")


def supabase_headers(token: Optional[str] = None) -> Dict[str, str]:
    """Construieste headerele HTTP standard folosite la apelurile Supabase."""
    tok = token if token is not None else (get_supabase_access_token() or SUPABASE_ANON_KEY)
    return {
        "apikey": SUPABASE_ANON_KEY,
        "Authorization": f"Bearer {tok}",
        "Content-Type": "application/json",
    }


def test_supabase_connectivity(
    timeout_sec: int = 5,
    progress_cb=None,
    cancelled_cb=None,
) -> Tuple[bool, str]:
    """Verifica conectivitatea Supabase cu test de auth si endpoint API."""
    if not SUPABASE_URL:
        return False, "SUPABASE_URL lipseste."
    if not SUPABASE_ANON_KEY:
        return False, "SUPABASE_ANON_KEY lipseste."

    try:
        if progress_cb:
            progress_cb(10, "Initializez testul Supabase...")
    except Exception:
        pass

    base = SUPABASE_URL.rstrip("/")
    candidates = [
        (base + "/rest/v1/", "REST API"),
        (base + "/auth/v1/health", "Auth health"),
    ]
    reachable_http = {200, 204, 400, 401, 403, 404, 406}
    headers = {
        "apikey": SUPABASE_ANON_KEY,
        "Authorization": f"Bearer {SUPABASE_ANON_KEY}",
    }

    last_err = ""
    total = max(1, len(candidates))
    for idx, (url, label) in enumerate(candidates):
        try:
            if cancelled_cb and cancelled_cb():
                return False, "Test anulat."
            if progress_cb:
                progress_cb(min(95, int((idx + 1) * 100 / total)), f"Testez {label}...")
        except Exception:
            pass
        req = urllib.request.Request(url, method="GET")
        for hk, hv in headers.items():
            req.add_header(hk, hv)
        try:
            with urllib.request.urlopen(req, timeout=max(2, int(timeout_sec))) as resp:
                code = int(getattr(resp, "status", 200) or 200)
                try:
                    if progress_cb:
                        progress_cb(100, "Conexiune confirmata.")
                except Exception:
                    pass
                return True, f"Conectat: {label} (HTTP {code})"
        except urllib.error.HTTPError as e:
            code = int(getattr(e, "code", 0) or 0)
            if code in reachable_http:
                try:
                    if progress_cb:
                        progress_cb(100, "Conexiune confirmata.")
                except Exception:
                    pass
                return True, f"Conectat: {label} (HTTP {code})"
            last_err = f"{label}: HTTP {code}"
        except urllib.error.URLError as e:
            last_err = f"{label}: {e.reason}"
        except Exception as e:
            last_err = f"{label}: {e}"

    return False, (last_err or "Nu s-a putut contacta Supabase.")


def supabase_request(method: str, path: str, params: Optional[Dict[str, str]] = None, data: Optional[Any] = None, token: Optional[str] = None) -> Any:
    """Executa o cerere HTTP catre Supabase cu tratare uniforma de erori."""
    if not SUPABASE_URL or not SUPABASE_ANON_KEY:
        raise RuntimeError("Supabase not configured")
    url = SUPABASE_URL.rstrip("/") + path
    if params:
        url += "?" + urllib.parse.urlencode(params, safe=",:>=")
    body = None
    if data is not None:
        body = json.dumps(data).encode("utf-8")
    req = urllib.request.Request(url, data=body, method=method.upper())
    for k, v in supabase_headers(token).items():
        req.add_header(k, v)
    try:
        with urllib.request.urlopen(req, timeout=30) as resp:
            raw = resp.read().decode("utf-8")
            return json.loads(raw) if raw else None
    except urllib.error.HTTPError as e:
        msg = e.read().decode("utf-8")
        raise RuntimeError(f"Supabase HTTP {e.code}: {msg}")


def supabase_auth_login(email: str, password: str):
    """Gestioneaza auth login."""
    if not email or not password:
        raise RuntimeError("Email/parola lipsa.")
    data = {"email": email, "password": password}
    resp = supabase_request(
        "POST",
        "/auth/v1/token",
        params={"grant_type": "password"},
        data=data,
        token=SUPABASE_ANON_KEY,
    )
    if not resp:
        raise RuntimeError("Login Supabase esuat.")
    set_supabase_tokens(
        resp.get("access_token", ""),
        resp.get("refresh_token", ""),
        resp.get("user", {}).get("email", "") if isinstance(resp.get("user"), dict) else "",
        int(resp.get("expires_in") or 3600),
    )


def supabase_auth_refresh(refresh_token: str):
    """Gestioneaza auth refresh."""
    if not refresh_token:
        raise RuntimeError("Refresh token lipsa.")
    data = {"refresh_token": refresh_token}
    resp = supabase_request(
        "POST",
        "/auth/v1/token",
        params={"grant_type": "refresh_token"},
        data=data,
        token=SUPABASE_ANON_KEY,
    )
    if not resp:
        raise RuntimeError("Refresh token esuat.")
    set_supabase_tokens(
        resp.get("access_token", ""),
        resp.get("refresh_token", refresh_token),
        resp.get("user", {}).get("email", "") if isinstance(resp.get("user"), dict) else "",
        int(resp.get("expires_in") or 3600),
    )


def supabase_auth_logout():
    """Gestioneaza auth logout."""
    clear_supabase_tokens()


def supabase_upsert(table: str, rows: List[Dict[str, Any]]):
    """Face upsert in tabela Supabase pentru lotul de randuri sincronizate."""
    if not rows:
        return
    params = {"on_conflict": "sync_id"}
    headers = supabase_headers()
    url = SUPABASE_URL.rstrip("/") + f"/rest/v1/{table}?" + urllib.parse.urlencode(params)
    body = json.dumps(rows).encode("utf-8")
    req = urllib.request.Request(url, data=body, method="POST")
    for k, v in headers.items():
        req.add_header(k, v)
    req.add_header("Prefer", "resolution=merge-duplicates")
    try:
        with urllib.request.urlopen(req, timeout=30) as resp:
            resp.read()
    except urllib.error.HTTPError as e:
        msg = e.read().decode("utf-8")
        raise RuntimeError(f"Supabase upsert {table} HTTP {e.code}: {msg}")


def supabase_fetch_updated(table: str, since_ts: Optional[str]) -> List[Dict[str, Any]]:
    """Descarca randurile modificate dupa un timestamp pentru sincronizare incrementala."""
    params = {"select": "*"}
    if since_ts:
        params["updated_at"] = f"gt.{since_ts}"
    data = supabase_request("GET", f"/rest/v1/{table}", params=params)
    return data or []


def is_http_url(v: str) -> bool:
    """Verifica daca http url."""
    return isinstance(v, str) and (v.startswith("http://") or v.startswith("https://"))


def supabase_storage_upload(
    local_path: str,
    bucket: str = SUPABASE_STORAGE_BUCKET,
    dest_name: Optional[str] = None,
    progress_cb=None,
    cancelled_cb=None,
) -> str:
    """Gestioneaza storage upload."""
    if not SUPABASE_URL or not SUPABASE_ANON_KEY:
        raise RuntimeError("Supabase not configured")
    if not local_path:
        raise RuntimeError("Fisier lipsa.")
    p = Path(local_path)
    if not p.exists():
        raise RuntimeError("Fisierul local nu exista.")

    def pg(percent: int, msg: str = ""):
        """Actualizeaza progresul operatiei in curs (helper intern pentru `supabase_storage_upload`)."""
        if progress_cb:
            try:
                progress_cb(int(max(0, min(100, percent))), msg)
            except Exception:
                pass

    pg(1, "Pregatesc upload Supabase...")
    dest = dest_name or f"{uuid.uuid4().hex}_{p.name}"
    q = urllib.parse.quote(dest)
    url = SUPABASE_URL.rstrip("/") + f"/storage/v1/object/{bucket}/{q}?upsert=true"
    total_size = int(p.stat().st_size or 0)
    read = 0
    chunks: List[bytes] = []
    with p.open("rb") as fh:
        while True:
            if cancelled_cb and cancelled_cb():
                raise RuntimeError("Upload anulat.")
            chunk = fh.read(1024 * 128)
            if not chunk:
                break
            chunks.append(chunk)
            read += len(chunk)
            if total_size > 0:
                pg(5 + int((read * 35) / total_size), f"Pregatesc fisierul... {read // 1024} KB")
    data = b"".join(chunks)

    ctype = mimetypes.guess_type(p.name)[0] or "application/octet-stream"
    req = urllib.request.Request(url, data=data, method="POST")
    req.add_header("apikey", SUPABASE_ANON_KEY)
    req.add_header("Authorization", f"Bearer {get_supabase_access_token() or SUPABASE_ANON_KEY}")
    req.add_header("Content-Type", ctype)
    try:
        pg(50, "Upload in curs...")
        with urllib.request.urlopen(req, timeout=60) as resp:
            resp.read()
        pg(100, "Upload finalizat.")
    except urllib.error.HTTPError as e:
        msg = e.read().decode("utf-8")
        raise RuntimeError(f"Supabase storage HTTP {e.code}: {msg}")
    if SUPABASE_STORAGE_PUBLIC:
        return SUPABASE_URL.rstrip("/") + f"/storage/v1/object/public/{bucket}/{dest}"
    return SUPABASE_URL.rstrip("/") + f"/storage/v1/object/{bucket}/{dest}"


def supabase_call_function(fn_name: str, payload: Optional[Dict[str, Any]] = None, token: Optional[str] = None) -> Any:
    """Gestioneaza call function."""
    if not fn_name:
        raise RuntimeError("Function name missing")
    return supabase_request(
        "POST",
        f"/functions/v1/{fn_name}",
        data=payload or {},
        token=token or SUPABASE_ANON_KEY,
    )


def send_reminders_job(progress_cb=None, cancelled_cb=None) -> Any:
    """Ruleaza trimiterea de remindere prin Supabase Edge Function folosind configuratia curenta."""
    if progress_cb:
        try:
            progress_cb(10, "Pregatesc trimiterea reminderelor...")
        except Exception:
            pass
    if cancelled_cb and cancelled_cb():
        raise RuntimeError("Trimiterea reminderelor a fost anulata.")

    # Ensure upcoming control visits exist as appointments with reminder contact fields.
    try:
        added = auto_create_appointments_from_controls()
    except Exception:
        added = 0

    if progress_cb:
        try:
            progress_cb(30, f"Programari pregatite din controale: {int(added or 0)}")
        except Exception:
            pass

    # Push fresh local appointment changes before calling cloud reminder function.
    if added:
        if progress_cb:
            try:
                progress_cb(45, "Sincronizez cloud inainte de remindere...")
            except Exception:
                pass
        sync_all(progress_cb=None, cancelled_cb=cancelled_cb)

    if progress_cb:
        try:
            progress_cb(55, "Trimit remindere prin Supabase...")
        except Exception:
            pass
    res = supabase_call_function("send-reminders", {})
    if progress_cb:
        try:
            progress_cb(100, "Remindere trimise.")
        except Exception:
            pass
    return res


def build_sms_gateway_runtime_config() -> Dict[str, Any]:
    """Construieste configuratia efectiva a gateway-ului SMS din setarile aplicatiei."""
    provider = "SMSMOBILEAPI"
    gateway_url = (get_setting("reminder_android_gateway_url", "") or "").strip()
    gateway_token = (get_setting("reminder_android_gateway_token", "") or "").strip()
    smsmobileapi_url = (get_setting("reminder_smsmobileapi_url", "") or "").strip()
    smsmobileapi_key = (get_setting("reminder_smsmobileapi_api_key", "") or "").strip()
    smsmobileapi_from = (get_setting("reminder_smsmobileapi_from", "") or "").strip()
    payload: Dict[str, Any] = {}
    payload["sms_provider"] = provider
    if gateway_url:
        payload["android_sms_gateway_url"] = gateway_url
    if gateway_token:
        payload["android_sms_gateway_token"] = gateway_token
    if gateway_url and not smsmobileapi_url:
        smsmobileapi_url = gateway_url
    if gateway_token and not smsmobileapi_key:
        smsmobileapi_key = gateway_token
    if smsmobileapi_url:
        payload["smsmobileapi_url"] = smsmobileapi_url
    if smsmobileapi_key:
        payload["smsmobileapi_api_key"] = smsmobileapi_key
    if smsmobileapi_from:
        payload["smsmobileapi_from"] = smsmobileapi_from
    return payload


def build_reminder_dispatch_mode() -> str:
    """Determina modul de dispatch pentru remindere automate (local sau cloud)."""
    return "local"


def is_valid_test_phone(phone: str) -> bool:
    """Valideaza formatul unui numar folosit pentru test SMS manual."""
    s = re.sub(r"\s+", "", str(phone or "").strip())
    if not s:
        return False
    if s.startswith("+"):
        return bool(re.fullmatch(r"\+\d{10,15}", s))
    if s.startswith("00"):
        return bool(re.fullmatch(r"00\d{10,15}", s))
    return bool(re.fullmatch(r"0\d{9}", s))


def _send_sms_via_android_gateway(to_number: str, message: str, sms_config: Optional[Dict[str, Any]] = None) -> Dict[str, Any]:
    """Trimite un SMS prin webhook-ul Android Gateway si returneaza rezultatul providerului."""
    cfg = dict(sms_config or build_sms_gateway_runtime_config())
    provider = (cfg.get("sms_provider") or "").strip().upper()
    gateway_url = (cfg.get("android_sms_gateway_url") or "").strip()
    gateway_token = (cfg.get("android_sms_gateway_token") or "").strip()

    if provider and provider != "ANDROID_GATEWAY":
        raise RuntimeError("Modul local suporta doar provider ANDROID_GATEWAY.")
    if not gateway_url:
        raise RuntimeError("Android gateway URL lipsa. Configureaza-l in Remindere automate.")

    phone = normalize_ro_mobile_phone(to_number) or (to_number or "").strip()
    if not phone:
        raise RuntimeError("Numar destinatar invalid.")

    body = json.dumps({"to": phone, "message": message}, ensure_ascii=False).encode("utf-8")
    req = urllib.request.Request(gateway_url, data=body, method="POST")
    req.add_header("Content-Type", "application/json")
    req.add_header("User-Agent", "PacientiApp/1.0")
    if gateway_token:
        req.add_header("Authorization", f"Bearer {gateway_token}")

    try:
        with urllib.request.urlopen(req, timeout=12) as resp:
            code = int(getattr(resp, "status", 200) or 200)
            raw = (resp.read() or b"").decode("utf-8", errors="ignore").strip()
            return {"ok": True, "http": code, "response": raw}
    except urllib.error.HTTPError as e:
        raw = (e.read() or b"").decode("utf-8", errors="ignore").strip()
        raise RuntimeError(f"Gateway HTTP {int(e.code)}: {raw}")
    except urllib.error.URLError as e:
        raise RuntimeError(f"Gateway indisponibil: {e.reason}")


def _is_http_url(value: str) -> bool:
    """Verifica daca textul primit este URL HTTP/HTTPS valid."""
    txt = (value or "").strip()
    if not txt:
        return False
    try:
        parsed = urllib.parse.urlparse(txt)
    except Exception:
        return False
    return parsed.scheme in ("http", "https") and bool(parsed.netloc)


def _smsmobileapi_response_error(parsed: Any) -> Optional[str]:
    """Extrage eroarea business din raspunsul SMSMobileAPI (chiar daca HTTP=200)."""
    node = parsed
    if isinstance(parsed, dict) and isinstance(parsed.get("result"), dict):
        node = parsed.get("result")
    if not isinstance(node, dict):
        return None

    err = node.get("error")
    if err is not None:
        serr = str(err).strip().lower()
        if serr not in ("", "0", "ok", "success", "true"):
            return f"error={err}"

    sent = node.get("sent")
    if sent is not None:
        ssent = str(sent).strip().lower()
        if ssent in ("", "0", "false", "failed", "error", "api_error", "not_sent", "ko", "no"):
            return f"sent={sent}"

    status = node.get("status")
    if status is not None:
        sstatus = str(status).strip().lower()
        if sstatus in ("error", "failed", "ko", "false", "0"):
            return f"status={status}"

    return None


def _send_sms_via_smsmobileapi(to_number: str, message: str, sms_config: Optional[Dict[str, Any]] = None) -> Dict[str, Any]:
    """Trimite un SMS prin SMSMobile API si normalizeaza raspunsul pentru audit intern."""
    cfg = dict(sms_config or build_sms_gateway_runtime_config())
    api_url = (cfg.get("smsmobileapi_url") or "").strip()
    api_key = (cfg.get("smsmobileapi_api_key") or "").strip()
    sender = (cfg.get("smsmobileapi_from") or "").strip() or "python"

    if api_url and not _is_http_url(api_url):
        if not api_key and re.fullmatch(r"[A-Za-z0-9._:-]{12,}", api_url):
            # Migrare toleranta: utilizatorul a pus cheia in campul URL.
            api_key = api_url
            api_url = ""
        else:
            raise RuntimeError("SMSMobileAPI URL invalid. Exemplu corect: https://api.smsmobileapi.com/sendsms")
    if not api_url:
        api_url = "https://api.smsmobileapi.com/sendsms"
    if not _is_http_url(api_url):
        raise RuntimeError("SMSMobileAPI URL invalid. Exemplu corect: https://api.smsmobileapi.com/sendsms")
    if not api_key:
        raise RuntimeError("SMSMobileAPI API Key lipsa. Configureaza-l in Remindere automate.")

    phone = normalize_ro_mobile_phone(to_number) or (to_number or "").strip()
    if not phone:
        raise RuntimeError("Numar destinatar invalid.")

    params = {
        "apikey": api_key,
        "recipients": phone,
        "message": message,
        "from": sender,
        "sendwa": 0,
        "sendsms": 1,
    }
    url = f"{api_url}?{urllib.parse.urlencode(params, doseq=False)}"
    req = urllib.request.Request(url, method="GET")
    req.add_header("User-Agent", "PacientiApp/1.0")

    try:
        with urllib.request.urlopen(req, timeout=12) as resp:
            code = int(getattr(resp, "status", 200) or 200)
            raw = (resp.read() or b"").decode("utf-8", errors="ignore").strip()
            parsed: Any = raw
            try:
                parsed = json.loads(raw) if raw else {}
            except Exception:
                pass
            api_err = _smsmobileapi_response_error(parsed)
            if api_err:
                raise RuntimeError(f"SMSMobileAPI raspuns negativ: {api_err}")
            return {"ok": True, "http": code, "response": parsed}
    except urllib.error.HTTPError as e:
        raw = (e.read() or b"").decode("utf-8", errors="ignore").strip()
        raise RuntimeError(f"SMSMobileAPI HTTP {int(e.code)}: {raw}")
    except urllib.error.URLError as e:
        raise RuntimeError(f"SMSMobileAPI indisponibil: {e.reason}")


def _send_sms_via_selected_provider(to_number: str, message: str, sms_config: Optional[Dict[str, Any]] = None) -> Dict[str, Any]:
    """Ruteaza trimiterea SMS catre providerul selectat in setari."""
    cfg = dict(sms_config or build_sms_gateway_runtime_config())
    provider = (cfg.get("sms_provider") or "SMSMOBILEAPI").strip().upper()
    if provider == "ANDROID_GATEWAY":
        return _send_sms_via_android_gateway(to_number, message, sms_config=cfg)

    # Compatibilitate cu configuratii vechi ce indicau webhook local pe /send.
    api_url = (cfg.get("smsmobileapi_url") or "").strip()
    if _is_http_url(api_url):
        p = urllib.parse.urlparse(api_url)
        host = (p.netloc or "").lower()
        path = (p.path or "").lower().rstrip("/")
        if path.endswith("/send") and "api.smsmobileapi.com" not in host:
            legacy_cfg = dict(cfg)
            legacy_cfg["sms_provider"] = "ANDROID_GATEWAY"
            legacy_cfg["android_sms_gateway_url"] = legacy_cfg.get("android_sms_gateway_url") or api_url
            legacy_cfg["android_sms_gateway_token"] = legacy_cfg.get("android_sms_gateway_token") or legacy_cfg.get("smsmobileapi_api_key")
            return _send_sms_via_android_gateway(to_number, message, sms_config=legacy_cfg)

    return _send_sms_via_smsmobileapi(to_number, message, sms_config=cfg)


def _ensure_reminder_runtime_tables(conn: sqlite3.Connection) -> None:
    """Creeaza tabelele runtime necesare pentru statusul si auditul reminderelor automate."""
    cur = conn.cursor()
    cur.execute(
        """
        CREATE TABLE IF NOT EXISTS appointment_reminder_state (
            appointment_id INTEGER PRIMARY KEY,
            status TEXT,
            attempts INTEGER DEFAULT 0,
            last_attempt_at TEXT,
            sent_at TEXT,
            next_retry_at TEXT,
            last_error TEXT,
            last_message TEXT,
            updated_at TEXT
        )
        """
    )
    cur.execute(
        """
        CREATE TABLE IF NOT EXISTS reminder_dispatch_log (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            appointment_id INTEGER,
            trigger_at TEXT,
            attempted_at TEXT,
            status TEXT,
            phone TEXT,
            message TEXT,
            response TEXT,
            error TEXT,
            attempts INTEGER,
            dispatch_rule TEXT,
            source_user TEXT,
            source_role TEXT,
            source_action TEXT
        )
        """
    )
    cur.execute("CREATE INDEX IF NOT EXISTS idx_reminder_state_status ON appointment_reminder_state(status)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_reminder_state_next_retry ON appointment_reminder_state(next_retry_at)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_reminder_log_appt ON reminder_dispatch_log(appointment_id)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_reminder_log_ts ON reminder_dispatch_log(attempted_at)")
    cols = _db_table_columns_cur(cur, "reminder_dispatch_log")
    if "source_user" in cols and "attempted_at" in cols:
        cur.execute("CREATE INDEX IF NOT EXISTS idx_reminder_log_user_ts ON reminder_dispatch_log(source_user, attempted_at)")


def _ensure_appointment_sms_template_state_table(conn: sqlite3.Connection) -> None:
    """Asigura tabela care memoreaza ce template SMS a fost trimis per programare."""
    cur = conn.cursor()
    cur.execute(
        """
        CREATE TABLE IF NOT EXISTS appointment_sms_template_state (
            appointment_id INTEGER PRIMARY KEY,
            confirm_sent_at TEXT,
            cancel_sent_at TEXT,
            last_template_key TEXT,
            last_status TEXT,
            last_error TEXT,
            updated_at TEXT
        )
        """
    )
    cur.execute("CREATE INDEX IF NOT EXISTS idx_appt_sms_tmpl_confirm ON appointment_sms_template_state(confirm_sent_at)")


def _is_safe_sql_table_name(table_name: str) -> bool:
    """Verifica daca safe SQL table name."""
    return bool(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", str(table_name or "").strip()))


def _ensure_entity_audit_table(conn: sqlite3.Connection) -> None:
    """Asigura entity audit table."""
    global _ENTITY_AUDIT_SCHEMA_READY
    cur = conn.cursor()
    cur.execute(
        f"""
        CREATE TABLE IF NOT EXISTS {ENTITY_AUDIT_TABLE} (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            ts TEXT,
            table_name TEXT,
            row_id INTEGER,
            action TEXT,
            before_json TEXT,
            after_json TEXT,
            source_user TEXT,
            source_role TEXT,
            source_action TEXT
        )
        """
    )
    cur.execute(f"CREATE INDEX IF NOT EXISTS idx_entity_audit_table_row ON {ENTITY_AUDIT_TABLE}(table_name, row_id, id)")
    cur.execute(f"CREATE INDEX IF NOT EXISTS idx_entity_audit_ts ON {ENTITY_AUDIT_TABLE}(ts)")
    _ENTITY_AUDIT_SCHEMA_READY = True


def _safe_json_dump_obj(value: Optional[Dict[str, Any]]) -> str:
    """Gestioneaza JSON dump obj."""
    if not value:
        return ""
    try:
        return json.dumps(value, ensure_ascii=False, sort_keys=True)
    except Exception:
        return ""


def _safe_json_load_obj(raw: Any) -> Dict[str, Any]:
    """Gestioneaza JSON load obj."""
    txt = (raw or "").strip() if isinstance(raw, str) else raw
    if not txt:
        return {}
    try:
        payload = json.loads(txt)
        if isinstance(payload, dict):
            return payload
    except Exception:
        pass
    return {}


def _fetch_row_dict_cur(cur: sqlite3.Cursor, table_name: str, row_id: int) -> Optional[Dict[str, Any]]:
    """Gestioneaza row dict cursor."""
    table = (table_name or "").strip()
    if not _is_safe_sql_table_name(table):
        return None
    cols = _db_table_columns_cur(cur, table)
    if "id" not in cols:
        return None
    try:
        cur.execute(f"SELECT * FROM {table} WHERE id=?", (int(row_id),))
        row = cur.fetchone()
        return dict(row) if row is not None else None
    except Exception:
        return None


def _insert_entity_audit_cur(
    cur: sqlite3.Cursor,
    table_name: str,
    row_id: int,
    action: str,
    before_row: Optional[Dict[str, Any]],
    after_row: Optional[Dict[str, Any]],
    source_action: str = "",
) -> None:
    """Insereaza entity audit cursor."""
    global _ENTITY_AUDIT_SCHEMA_READY
    table = (table_name or "").strip()
    if not _is_safe_sql_table_name(table):
        return
    if not _ENTITY_AUDIT_SCHEMA_READY:
        _ensure_entity_audit_table(cur.connection)
    cur.execute(
        f"""
        INSERT INTO {ENTITY_AUDIT_TABLE}(
            ts, table_name, row_id, action, before_json, after_json, source_user, source_role, source_action
        ) VALUES (?,?,?,?,?,?,?,?,?)
        """,
        (
            datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
            table,
            int(row_id),
            (action or "").strip(),
            _safe_json_dump_obj(before_row),
            _safe_json_dump_obj(after_row),
            get_current_user(),
            get_current_role(),
            (source_action or "").strip(),
        ),
    )


def get_entity_audit_rows(
    limit: int = 500,
    table_name: str = "",
    row_id: Optional[int] = None,
) -> List[Dict[str, Any]]:
    """Returneaza entity audit rows."""
    lim = max(20, min(5000, int(limit or 500)))
    table = (table_name or "").strip()
    if table and not _is_safe_sql_table_name(table):
        table = ""

    conn = get_conn()
    _ensure_entity_audit_table(conn)
    cur = conn.cursor()
    where: List[str] = []
    args: List[Any] = []
    if table:
        where.append("table_name=?")
        args.append(table)
    if row_id is not None:
        where.append("row_id=?")
        args.append(int(row_id))
    where_sql = f"WHERE {' AND '.join(where)}" if where else ""
    cur.execute(
        f"""
        SELECT
            id, ts, table_name, row_id, action, before_json, after_json, source_user, source_role, source_action
        FROM {ENTITY_AUDIT_TABLE}
        {where_sql}
        ORDER BY id DESC
        LIMIT ?
        """,
        tuple(args + [lim]),
    )
    rows = [dict(r) for r in cur.fetchall()]
    conn.close()
    return rows


def _apply_row_snapshot_cur(cur: sqlite3.Cursor, table_name: str, snapshot: Dict[str, Any]) -> int:
    """Aplica row snapshot cursor."""
    table = (table_name or "").strip()
    if not _is_safe_sql_table_name(table):
        raise RuntimeError("Tabel invalid pentru revert.")
    if not isinstance(snapshot, dict) or "id" not in snapshot:
        raise RuntimeError("Snapshot invalid pentru revert.")

    cols = _db_table_columns_cur(cur, table)
    if "id" not in cols:
        raise RuntimeError("Tabelul nu are coloana id.")

    rid = int(snapshot.get("id") or 0)
    if rid <= 0:
        raise RuntimeError("ID snapshot invalid.")

    payload: Dict[str, Any] = {}
    for k, v in snapshot.items():
        if k in cols:
            payload[k] = v
    payload["id"] = rid

    cur.execute(f"SELECT 1 FROM {table} WHERE id=?", (rid,))
    exists = cur.fetchone() is not None
    if exists:
        up_cols = [c for c in payload.keys() if c != "id"]
        if up_cols:
            sets = ", ".join([f"{c}=?" for c in up_cols])
            vals = [payload.get(c) for c in up_cols] + [rid]
            cur.execute(f"UPDATE {table} SET {sets} WHERE id=?", tuple(vals))
    else:
        ins_cols = list(payload.keys())
        placeholders = ", ".join(["?"] * len(ins_cols))
        cur.execute(
            f"INSERT INTO {table}({', '.join(ins_cols)}) VALUES ({placeholders})",
            tuple([payload.get(c) for c in ins_cols]),
        )
    return rid


def revert_entity_audit_entry(audit_id: int) -> Dict[str, Any]:
    """Gestioneaza entity audit entry."""
    conn = get_conn()
    _ensure_entity_audit_table(conn)
    cur = conn.cursor()
    try:
        cur.execute(f"SELECT * FROM {ENTITY_AUDIT_TABLE} WHERE id=?", (int(audit_id),))
        row = cur.fetchone()
        if row is None:
            raise RuntimeError("Intrarea de audit nu exista.")

        table = (row["table_name"] or "").strip()
        if table not in {"pacienti_master", "consulturi", "appointments"}:
            raise RuntimeError("Revert permis doar pentru pacienti, consulturi sau programari.")

        rid = int(row["row_id"] or 0)
        if rid <= 0:
            raise RuntimeError("Intrare audit invalida (row_id).")

        before_snapshot = _safe_json_load_obj(row["before_json"])
        after_snapshot = _safe_json_load_obj(row["after_json"])
        current_before = _fetch_row_dict_cur(cur, table, rid)

        if before_snapshot:
            _apply_row_snapshot_cur(cur, table, before_snapshot)
            revert_action = f"revert_to_before#{int(audit_id)}"
        elif after_snapshot:
            cols = _db_table_columns_cur(cur, table)
            if "deleted" in cols:
                sets = ["deleted=1"]
                vals: List[Any] = []
                if "updated_at" in cols:
                    sets.append("updated_at=?")
                    vals.append(now_ts())
                if "device_id" in cols:
                    sets.append("device_id=?")
                    vals.append(get_device_id())
                vals.append(rid)
                cur.execute(f"UPDATE {table} SET {', '.join(sets)} WHERE id=?", tuple(vals))
            else:
                cur.execute(f"DELETE FROM {table} WHERE id=?", (rid,))
            revert_action = f"revert_insert#{int(audit_id)}"
        else:
            raise RuntimeError("Intrarea audit nu are snapshot pentru revert.")

        current_after = _fetch_row_dict_cur(cur, table, rid)
        _insert_entity_audit_cur(
            cur,
            table,
            rid,
            revert_action,
            current_before,
            current_after,
            source_action="manual_revert",
        )
        conn.commit()
        return {
            "ok": True,
            "table_name": table,
            "row_id": rid,
            "revert_action": revert_action,
        }
    except Exception:
        conn.rollback()
        raise
    finally:
        conn.close()


def _get_appointment_confirm_sent_ids(conn: sqlite3.Connection) -> set:
    """Returneaza setul de programari care au deja SMS de confirmare trimis."""
    _ensure_appointment_sms_template_state_table(conn)
    cur = conn.cursor()
    cur.execute(
        """
        SELECT appointment_id
        FROM appointment_sms_template_state
        WHERE confirm_sent_at IS NOT NULL AND TRIM(confirm_sent_at) <> ''
        """
    )
    out = set()
    for r in cur.fetchall():
        try:
            out.add(int(r[0]))
        except Exception:
            continue
    return out


def _upsert_appointment_sms_template_state(
    cur: sqlite3.Cursor,
    appointment_id: int,
    template_key: str,
    status: str,
    error: str = "",
    sent_at: str = "",
) -> None:
    """Insereaza sau actualizeaza starea de trimitere SMS per template si programare."""
    key = _normalize_forced_template_key(template_key) or "default"
    confirm_sent_at = sent_at if (key == "confirm" and status == "sent") else ""
    cancel_sent_at = sent_at if (key == "cancel" and status == "sent") else ""
    cur.execute(
        """
        INSERT INTO appointment_sms_template_state (
            appointment_id, confirm_sent_at, cancel_sent_at, last_template_key, last_status, last_error, updated_at
        ) VALUES (?,?,?,?,?,?,?)
        ON CONFLICT(appointment_id) DO UPDATE SET
            confirm_sent_at=CASE
                WHEN excluded.confirm_sent_at IS NOT NULL AND TRIM(excluded.confirm_sent_at) <> '' THEN excluded.confirm_sent_at
                ELSE appointment_sms_template_state.confirm_sent_at
            END,
            cancel_sent_at=CASE
                WHEN excluded.cancel_sent_at IS NOT NULL AND TRIM(excluded.cancel_sent_at) <> '' THEN excluded.cancel_sent_at
                ELSE appointment_sms_template_state.cancel_sent_at
            END,
            last_template_key=excluded.last_template_key,
            last_status=excluded.last_status,
            last_error=excluded.last_error,
            updated_at=excluded.updated_at
        """,
        (
            int(appointment_id),
            confirm_sent_at or None,
            cancel_sent_at or None,
            key,
            (status or "").strip() or None,
            (error or "").strip() or None,
            now_ts(),
        ),
    )


def _setting_int(key: str, default: int, min_val: int, max_val: int) -> int:
    """Citeste o setare numerica intreaga si o limiteaza in intervalul permis."""
    raw = (get_setting(key, str(default)) or str(default)).strip()
    try:
        val = int(raw)
    except Exception:
        val = int(default)
    return max(min_val, min(max_val, val))


def _setting_float(key: str, default: float, min_val: float, max_val: float) -> float:
    """Citeste o setare numerica zecimala si o limiteaza in intervalul permis."""
    raw = (get_setting(key, str(default)) or str(default)).strip()
    try:
        val = float(raw)
    except Exception:
        val = float(default)
    return max(float(min_val), min(float(max_val), val))


def _to_int_flag(value: Any) -> int:
    """Converteaza int flag."""
    if isinstance(value, bool):
        return 1 if value else 0
    if value is None:
        return 0
    txt = str(value).strip().lower()
    if txt in {"1", "true", "da", "yes", "y"}:
        return 1
    return 0


def _safe_sleep_with_cancel(total_sec: float, cancelled_cb=None) -> bool:
    """Gestioneaza sleep with cancel."""
    remaining = max(0.0, float(total_sec))
    while remaining > 0:
        if cancelled_cb and cancelled_cb():
            return False
        chunk = min(0.2, remaining)
        time.sleep(chunk)
        remaining -= chunk
    return True


def _is_retryable_sms_error(exc: Exception) -> bool:
    """Verifica daca retryable SMS error."""
    msg = (str(exc) or "").lower()
    transient = [
        "timeout",
        "temporar",
        "temporarily",
        "unavailable",
        "gateway",
        "429",
        "502",
        "503",
        "504",
        "connection",
        "network",
        "econn",
        "reset",
    ]
    return any(k in msg for k in transient)


def _send_sms_with_retry(
    phone: str,
    message: str,
    sms_config: Optional[Dict[str, Any]] = None,
    cancelled_cb=None,
) -> Dict[str, Any]:
    """Trimite SMS cu retry controlat pentru erori tranzitorii si respecta anularea jobului."""
    attempts_max = _setting_int(SMS_IMMEDIATE_RETRY_MAX_KEY, SMS_IMMEDIATE_RETRY_MAX_DEFAULT, 1, 6)
    base_ms = _setting_int(SMS_IMMEDIATE_RETRY_BASE_MS_KEY, SMS_IMMEDIATE_RETRY_BASE_MS_DEFAULT, 100, 5000)
    last_exc: Optional[Exception] = None
    for attempt in range(1, attempts_max + 1):
        if cancelled_cb and cancelled_cb():
            raise RuntimeError("Trimiterea SMS a fost anulata.")
        try:
            res = _send_sms_via_selected_provider(phone, message, sms_config=sms_config)
            if isinstance(res, dict):
                res.setdefault("attempt", attempt)
                res.setdefault("attempts_max", attempts_max)
            return res
        except Exception as e:
            last_exc = e
            if attempt >= attempts_max or not _is_retryable_sms_error(e):
                break
            wait_sec = (base_ms / 1000.0) * (2 ** (attempt - 1))
            if not _safe_sleep_with_cancel(wait_sec, cancelled_cb=cancelled_cb):
                raise RuntimeError("Trimiterea SMS a fost anulata.")
    if last_exc is not None:
        raise last_exc
    raise RuntimeError("Eroare necunoscuta la trimiterea SMS.")


def _get_reminder_run_interval_min() -> int:
    """Citeste intervalul de rulare al schedulerului de remindere in minute."""
    return _setting_int(REMINDER_INTERVAL_MIN_KEY, REMINDER_INTERVAL_MIN_DEFAULT, 5, 1440)


def _set_reminder_last_run_at(dt: datetime) -> None:
    """Seteaza reminder last run at."""
    set_setting(REMINDER_LAST_RUN_AT_KEY, dt.strftime("%Y-%m-%d %H:%M:%S"))


def _reminder_interval_status(now_local: datetime, force: bool = False) -> Tuple[bool, int]:
    """Calculeaza daca jobul de remindere poate rula acum conform intervalului configurat."""
    if force:
        return True, 0
    interval_min = _get_reminder_run_interval_min()
    last_run = _parse_dt_any(get_setting(REMINDER_LAST_RUN_AT_KEY, "") or "")
    if last_run is None:
        return True, 0
    elapsed_sec = (now_local - last_run).total_seconds()
    if elapsed_sec < 0:
        return True, 0
    required_sec = int(interval_min) * 60
    if elapsed_sec >= required_sec:
        return True, 0
    remaining_min = int((required_sec - elapsed_sec + 59) // 60)
    return False, max(1, remaining_min)


def _parse_slot_dt(value: str) -> Optional[datetime]:
    """Parseaza slot data/ora."""
    s = (value or "").strip()
    if not s:
        return None
    try:
        return datetime.strptime(s, "%Y-%m-%d %H:%M")
    except Exception:
        return None


def _fmt_slot_dt(dt: datetime) -> str:
    """Formateaza slot data/ora."""
    return dt.strftime("%Y-%m-%d %H:%M")


def _appointment_dt(date_value: Optional[str], time_value: Optional[str], fallback_hhmm: str = "09:00") -> Optional[datetime]:
    """Gestioneaza data/ora."""
    d = _safe_parse_ymd(date_value)
    if d is None:
        return None
    hhmm = (time_value or "").strip()
    if not validate_hhmm(hhmm):
        hhmm = fallback_hhmm
    hh, mm = [int(x) for x in hhmm.split(":")]
    return datetime(d.year, d.month, d.day, hh, mm)


def _get_reminder_rule() -> str:
    """Citeste regula activa de eligibilitate pentru remindere automate."""
    rule = (get_setting("reminder_send_rule", REMINDER_RULE_DAY_BEFORE) or REMINDER_RULE_DAY_BEFORE).strip()
    valid = {REMINDER_RULE_DAY_BEFORE, REMINDER_RULE_2H_BEFORE, REMINDER_RULE_SAME_DAY}
    return rule if rule in valid else REMINDER_RULE_DAY_BEFORE


def _get_reminder_templates() -> Dict[str, str]:
    """Incarca template-urile SMS folosite de remindere automate."""
    default_tpl = (get_setting("reminder_template_default", REMINDER_TEMPLATE_DEFAULT) or REMINDER_TEMPLATE_DEFAULT).strip()
    confirm_tpl = (get_setting("reminder_template_confirm", REMINDER_TEMPLATE_CONFIRM) or REMINDER_TEMPLATE_CONFIRM).strip()
    cancel_tpl = (get_setting("reminder_template_cancel", REMINDER_TEMPLATE_CANCEL) or REMINDER_TEMPLATE_CANCEL).strip()
    ortopedie_tpl = (get_setting("reminder_template_ortopedie", REMINDER_TEMPLATE_ORTOPEDIE) or REMINDER_TEMPLATE_ORTOPEDIE).strip()
    fizioterapie_tpl = (get_setting("reminder_template_fizioterapie", REMINDER_TEMPLATE_FIZIOTERAPIE) or REMINDER_TEMPLATE_FIZIOTERAPIE).strip()
    return {
        "default": default_tpl or REMINDER_TEMPLATE_DEFAULT,
        "confirm": confirm_tpl or REMINDER_TEMPLATE_CONFIRM,
        "cancel": cancel_tpl or REMINDER_TEMPLATE_CANCEL,
        "ortopedie": ortopedie_tpl or REMINDER_TEMPLATE_ORTOPEDIE,
        "fizioterapie": fizioterapie_tpl or REMINDER_TEMPLATE_FIZIOTERAPIE,
    }


def _select_reminder_template(appt_status: str, templates: Dict[str, str]) -> str:
    """Alege template-ul SMS potrivit pe baza statusului programarii."""
    st = _norm(appt_status or "")
    if "anulat" in st or "cancel" in st:
        return templates.get("cancel") or REMINDER_TEMPLATE_CANCEL
    if "confirm" in st:
        return templates.get("confirm") or REMINDER_TEMPLATE_CONFIRM
    return templates.get("default") or REMINDER_TEMPLATE_DEFAULT


def _normalize_forced_template_key(value: Optional[str]) -> Optional[str]:
    """Normalizeaza forced template key."""
    key = str(value or "").strip().lower()
    aliases = {
        "default": "default",
        "standard": "default",
        "confirm": "confirm",
        "confirmare": "confirm",
        "cancel": "cancel",
        "anulare": "cancel",
        "ortopedie": "ortopedie",
        "ortho": "ortopedie",
        "fizioterapie": "fizioterapie",
        "physio": "fizioterapie",
        "fizio": "fizioterapie",
    }
    return aliases.get(key)


def _is_due_for_rule(appt_date: date, appt_dt: datetime, trigger_dt: datetime, rule: str) -> bool:
    """Verifica daca due for rule."""
    if rule == REMINDER_RULE_2H_BEFORE:
        # Window includes short catch-up for missed runs.
        return (trigger_dt - timedelta(hours=2)) <= appt_dt <= (trigger_dt + timedelta(hours=2))
    if rule == REMINDER_RULE_SAME_DAY:
        return appt_date == trigger_dt.date() and appt_dt <= trigger_dt
    # Default: day-before + late same-day catch-up (up to 2h after appointment time).
    if appt_date == (trigger_dt.date() + timedelta(days=1)):
        return True
    if appt_date == trigger_dt.date() and appt_dt >= (trigger_dt - timedelta(hours=2)):
        return True
    return False


def _build_reminder_message(
    row: sqlite3.Row,
    trigger_dt: datetime,
    templates: Dict[str, str],
    forced_template_key: Optional[str] = None,
) -> str:
    """Renderizeaza mesajul reminderului cu datele pacientului si ale programarii."""
    clinic = get_clinic_settings()
    phone = (clinic.get("clinic_phone") or "").strip()
    name = (clinic.get("clinic_name") or "Clinica").strip() or "Clinica"
    contact = phone or name

    appt_dt = _appointment_dt(row["date"], row["time"]) if "date" in row.keys() else None
    if appt_dt is None:
        appt_dt = trigger_dt
    ctx = {
        "nume_prenume": (row["nume_prenume"] or "").strip(),
        "date": appt_dt.strftime("%Y-%m-%d"),
        "time": appt_dt.strftime("%H:%M"),
        "medic": (row["medic"] or "").strip() or "medic",
        "location": (row["location_name"] or "").strip() or name,
        "status": (row["status"] or "").strip(),
        "contact": contact,
    }
    forced_key = _normalize_forced_template_key(forced_template_key)
    if forced_key:
        template = templates.get(forced_key) or templates.get("default") or REMINDER_TEMPLATE_DEFAULT
    else:
        template = _select_reminder_template((row["status"] or "").strip(), templates)
    msg = render_template_text(template, ctx)
    msg = re.sub(r"\s+", " ", (msg or "").strip())
    return msg or f"Reminder programare: {ctx['date']} {ctx['time']}."


def get_sms_opt_out_patient_ids(patient_ids: List[int]) -> set:
    """Returneaza pacientii care au opt-out SMS si trebuie exclusi din trimitere."""
    ids = sorted(set([int(x) for x in (patient_ids or []) if int(x) > 0]))
    if not ids:
        return set()
    if not table_has_column("pacienti_master", "sms_opt_out"):
        return set()
    conn = get_conn()
    cur = conn.cursor()
    ph = ", ".join(["?"] * len(ids))
    cur.execute(
        f"""
        SELECT id
        FROM pacienti_master
        WHERE id IN ({ph}) AND COALESCE(sms_opt_out,0)=1
        """,
        tuple(ids),
    )
    out = set()
    for r in cur.fetchall():
        try:
            out.add(int(r[0]))
        except Exception:
            continue
    conn.close()
    return out


def _update_reminder_state(
    cur: sqlite3.Cursor,
    appointment_id: int,
    status: str,
    attempts: int,
    last_attempt_at: str,
    sent_at: str,
    next_retry_at: str,
    last_error: str,
    last_message: str,
) -> None:
    """Actualizeaza runtime state dupa incercarea de trimitere reminder."""
    cur.execute(
        """
        INSERT INTO appointment_reminder_state (
            appointment_id, status, attempts, last_attempt_at, sent_at, next_retry_at, last_error, last_message, updated_at
        ) VALUES (?,?,?,?,?,?,?,?,?)
        ON CONFLICT(appointment_id) DO UPDATE SET
            status=excluded.status,
            attempts=excluded.attempts,
            last_attempt_at=excluded.last_attempt_at,
            sent_at=excluded.sent_at,
            next_retry_at=excluded.next_retry_at,
            last_error=excluded.last_error,
            last_message=excluded.last_message,
            updated_at=excluded.updated_at
        """,
        (
            int(appointment_id),
            status,
            int(attempts),
            last_attempt_at or None,
            sent_at or None,
            next_retry_at or None,
            last_error or None,
            last_message or None,
            now_ts(),
        ),
    )


def _insert_reminder_log(
    cur: sqlite3.Cursor,
    appointment_id: int,
    trigger_at: str,
    attempted_at: str,
    status: str,
    phone: str,
    message: str,
    response: str,
    error: str,
    attempts: int,
    dispatch_rule: str,
    source_user: str = "",
    source_role: str = "",
    source_action: str = "",
) -> None:
    """Scrie in jurnal rezultatul unei trimiteri de reminder pentru audit si monitorizare."""
    cols = _db_table_columns_cur(cur, "reminder_dispatch_log")
    insert_cols = [
        "appointment_id",
        "trigger_at",
        "attempted_at",
        "status",
        "phone",
        "message",
        "response",
        "error",
        "attempts",
        "dispatch_rule",
    ]
    vals: List[Any] = [
        int(appointment_id),
        trigger_at or None,
        attempted_at or None,
        status,
        phone or None,
        message or None,
        response or None,
        error or None,
        int(attempts),
        dispatch_rule or REMINDER_RULE_DAY_BEFORE,
    ]
    if "source_user" in cols:
        insert_cols.append("source_user")
        vals.append((source_user or get_current_user() or DEFAULT_USER).strip() or DEFAULT_USER)
    if "source_role" in cols:
        insert_cols.append("source_role")
        vals.append((source_role or get_current_role() or DEFAULT_ROLE).strip() or DEFAULT_ROLE)
    if "source_action" in cols:
        insert_cols.append("source_action")
        vals.append((source_action or dispatch_rule or "sms_dispatch").strip())

    cur.execute(
        f"INSERT INTO reminder_dispatch_log ({', '.join(insert_cols)}) VALUES ({', '.join(['?'] * len(vals))})",
        tuple(vals),
    )


def send_reminders_job_local(
    sms_config: Optional[Dict[str, Any]] = None,
    progress_cb=None,
    cancelled_cb=None,
    trigger_dt: Optional[datetime] = None,
    dispatch_rule: Optional[str] = None,
    force_template_key: Optional[str] = None,
) -> Dict[str, Any]:
    """Ruleaza local tot pipeline-ul de remindere automate cu filtrare, template si audit."""
    if progress_cb:
        try:
            progress_cb(10, "Pregatesc remindere locale...")
        except Exception:
            pass
    if cancelled_cb and cancelled_cb():
        raise RuntimeError("Trimiterea reminderelor a fost anulata.")

    try:
        added = auto_create_appointments_from_controls()
    except Exception:
        added = 0

    if progress_cb:
        try:
            progress_cb(25, f"Programari pregatite din controale: {int(added or 0)}")
        except Exception:
            pass

    run_dt = trigger_dt or datetime.now()
    rule = (dispatch_rule or _get_reminder_rule()).strip()
    if rule not in {REMINDER_RULE_DAY_BEFORE, REMINDER_RULE_2H_BEFORE, REMINDER_RULE_SAME_DAY}:
        rule = REMINDER_RULE_DAY_BEFORE

    templates = _get_reminder_templates()
    retry_max = _setting_int("reminder_retry_max_attempts", 3, 1, 20)
    retry_delay_min = _setting_int("reminder_retry_delay_min", 20, 1, 1440)

    has_deleted = table_has_column("appointments", "deleted")
    has_reminder_sent = table_has_column("appointments", "reminder_sent_at")
    has_updated_at = table_has_column("appointments", "updated_at")
    has_location_fk = table_has_column("appointments", "location_id")
    has_status_col = table_has_column("appointments", "status")

    where = ["a.reminder_sms IS NOT NULL", "TRIM(a.reminder_sms)<>''", "a.date IS NOT NULL", "TRIM(a.date)<>''"]
    args: List[Any] = []
    if has_deleted:
        where.append("COALESCE(a.deleted,0)=0")

    conn = get_conn()
    _ensure_reminder_runtime_tables(conn)
    cur = conn.cursor()
    status_select = "a.status" if has_status_col else "'' AS status"
    location_join = "LEFT JOIN locations l ON l.id=a.location_id" if has_location_fk else ""
    location_select = "COALESCE(l.name,'')" if has_location_fk else "''"
    cur.execute(
        f"""
        SELECT
            a.id,
            a.pacient_id,
            a.date,
            a.time,
            a.medic,
            {status_select},
            a.reminder_sms,
            COALESCE(m.nume_prenume,'') AS nume_prenume,
            COALESCE(m.sms_opt_out,0) AS sms_opt_out,
            {location_select} AS location_name,
            COALESCE(s.status,'') AS reminder_state_status,
            COALESCE(s.attempts,0) AS reminder_state_attempts,
            COALESCE(s.next_retry_at,'') AS reminder_next_retry_at,
            COALESCE(s.sent_at,'') AS reminder_sent_state_at
        FROM appointments a
        LEFT JOIN pacienti_master m ON m.id=a.pacient_id
        {location_join}
        LEFT JOIN appointment_reminder_state s ON s.appointment_id=a.id
        WHERE {' AND '.join(where)}
        """,
        args,
    )
    rows = cur.fetchall()

    candidates: List[sqlite3.Row] = []
    for r in rows:
        d = _safe_parse_ymd(r["date"])
        appt_dt = _appointment_dt(r["date"], r["time"])
        if d is None or appt_dt is None:
            continue
        if not _is_due_for_rule(d, appt_dt, run_dt, rule):
            continue
        sent_state = (r["reminder_sent_state_at"] or "").strip()
        if sent_state:
            continue
        if has_reminder_sent:
            try:
                cur.execute("SELECT reminder_sent_at FROM appointments WHERE id=?", (int(r["id"]),))
                rr = cur.fetchone()
                if rr and (rr[0] or "").strip():
                    continue
            except Exception:
                pass
        attempts = int(r["reminder_state_attempts"] or 0)
        st = (r["reminder_state_status"] or "").strip().lower()
        if attempts >= retry_max and st in ("failed_final", "failed"):
            continue
        next_retry_raw = (r["reminder_next_retry_at"] or "").strip()
        if next_retry_raw:
            next_retry_dt = _parse_dt_any(next_retry_raw)
            if next_retry_dt is not None and next_retry_dt > run_dt:
                continue
        candidates.append(r)

    total = len(candidates)
    sent = 0
    errors = 0
    skipped_no_phone = 0
    skipped_opt_out = 0
    trigger_txt = run_dt.strftime("%Y-%m-%d %H:%M")

    for idx, r in enumerate(candidates, start=1):
        if cancelled_cb and cancelled_cb():
            conn.close()
            raise RuntimeError("Trimiterea reminderelor a fost anulata.")

        appt_id = int(r["id"])
        attempts = int(r["reminder_state_attempts"] or 0)
        attempted_at = now_ts()
        phone = normalize_ro_mobile_phone(r["reminder_sms"]) or (r["reminder_sms"] or "").strip()
        msg = _build_reminder_message(r, run_dt, templates, forced_template_key=force_template_key)
        if _to_int_flag(r["sms_opt_out"]) == 1:
            skipped_opt_out += 1
            _update_reminder_state(
                cur,
                appt_id,
                status="skipped_opt_out",
                attempts=attempts,
                last_attempt_at=attempted_at,
                sent_at="",
                next_retry_at="",
                last_error="SMS dezactivat pentru pacient.",
                last_message=msg,
            )
            _insert_reminder_log(
                cur,
                appt_id,
                trigger_at=trigger_txt,
                attempted_at=attempted_at,
                status="skipped_opt_out",
                phone="",
                message=msg,
                response="",
                error="sms_opt_out",
                attempts=attempts,
                dispatch_rule=rule,
            )
            conn.commit()
            continue
        if not phone:
            skipped_no_phone += 1
            _update_reminder_state(
                cur,
                appt_id,
                status="skipped_no_phone",
                attempts=attempts,
                last_attempt_at=attempted_at,
                sent_at="",
                next_retry_at="",
                last_error="Numar de telefon invalid sau lipsa",
                last_message=msg,
            )
            _insert_reminder_log(
                cur,
                appt_id,
                trigger_at=trigger_txt,
                attempted_at=attempted_at,
                status="skipped_no_phone",
                phone="",
                message=msg,
                response="",
                error="Numar de telefon invalid sau lipsa",
                attempts=attempts,
                dispatch_rule=rule,
            )
            conn.commit()
            continue

        try:
            res = _send_sms_with_retry(
                phone,
                msg,
                sms_config=sms_config,
                cancelled_cb=cancelled_cb,
            )
            sent += 1
            used_attempts = int(res.get("attempt", 1)) if isinstance(res, dict) else 1
            attempts_new = attempts + max(1, used_attempts)
            _update_reminder_state(
                cur,
                appt_id,
                status="sent",
                attempts=attempts_new,
                last_attempt_at=attempted_at,
                sent_at=attempted_at,
                next_retry_at="",
                last_error="",
                last_message=msg,
            )
            pretty_res = ""
            try:
                pretty_res = json.dumps(res, ensure_ascii=False)
            except Exception:
                pretty_res = str(res)
            _insert_reminder_log(
                cur,
                appt_id,
                trigger_at=trigger_txt,
                attempted_at=attempted_at,
                status="sent",
                phone=phone,
                message=msg,
                response=pretty_res,
                error="",
                attempts=attempts_new,
                dispatch_rule=rule,
            )
            if has_reminder_sent:
                if has_updated_at:
                    cur.execute("UPDATE appointments SET reminder_sent_at=?, updated_at=? WHERE id=?", (attempted_at, now_ts(), appt_id))
                else:
                    cur.execute("UPDATE appointments SET reminder_sent_at=? WHERE id=?", (attempted_at, appt_id))
            conn.commit()
        except Exception as e:
            errors += 1
            attempts_new = attempts + 1
            final_failed = attempts_new >= retry_max
            next_retry = ""
            if not final_failed:
                next_retry = (datetime.now(timezone.utc) + timedelta(minutes=retry_delay_min)).strftime("%Y-%m-%d %H:%M:%S")
            err = str(e)
            _update_reminder_state(
                cur,
                appt_id,
                status="failed_final" if final_failed else "retry_wait",
                attempts=attempts_new,
                last_attempt_at=attempted_at,
                sent_at="",
                next_retry_at=next_retry,
                last_error=err,
                last_message=msg,
            )
            _insert_reminder_log(
                cur,
                appt_id,
                trigger_at=trigger_txt,
                attempted_at=attempted_at,
                status="failed_final" if final_failed else "retry_wait",
                phone=phone,
                message=msg,
                response="",
                error=err,
                attempts=attempts_new,
                dispatch_rule=rule,
            )
            conn.commit()

        if progress_cb:
            try:
                p = 30 + int((idx * 70) / max(1, total))
                progress_cb(min(100, p), f"Trimit SMS local {idx}/{total}")
            except Exception:
                pass

    conn.close()
    return {
        "ok": True,
        "mode": "local",
        "dispatch_rule": rule,
        "trigger_at": trigger_txt,
        "total": total,
        "sent_sms": sent,
        "errors": errors,
        "skipped_no_phone": skipped_no_phone,
        "skipped_opt_out": skipped_opt_out,
        "retry_max": retry_max,
        "retry_delay_min": retry_delay_min,
    }


def get_reminder_monitor_snapshot(limit: int = 40) -> Dict[str, Any]:
    """Construieste sumarul monitorizarii reminderelor pentru ecranul de dashboard."""
    conn = get_conn()
    _ensure_reminder_runtime_tables(conn)
    cur = conn.cursor()
    cur.execute(
        """
        SELECT
            COUNT(*) AS total,
            SUM(CASE WHEN status='sent' THEN 1 ELSE 0 END) AS sent,
            SUM(CASE WHEN status='retry_wait' THEN 1 ELSE 0 END) AS retry_wait,
            SUM(CASE WHEN status='failed_final' THEN 1 ELSE 0 END) AS failed_final,
            SUM(CASE WHEN status='skipped_no_phone' THEN 1 ELSE 0 END) AS skipped_no_phone,
            SUM(CASE WHEN status='skipped_opt_out' THEN 1 ELSE 0 END) AS skipped_opt_out
        FROM appointment_reminder_state
        """
    )
    row = cur.fetchone() or {}
    cur.execute(
        """
        SELECT appointment_id, trigger_at, attempted_at, status, phone, error, attempts, dispatch_rule
        FROM reminder_dispatch_log
        ORDER BY id DESC
        LIMIT ?
        """,
        (max(5, int(limit)),),
    )
    logs = [dict(r) for r in cur.fetchall()]
    conn.close()
    return {
        "total_state": int(row["total"] or 0),
        "sent": int(row["sent"] or 0),
        "retry_wait": int(row["retry_wait"] or 0),
        "failed_final": int(row["failed_final"] or 0),
        "skipped_no_phone": int(row["skipped_no_phone"] or 0),
        "skipped_opt_out": int(row["skipped_opt_out"] or 0),
        "recent_logs": logs,
    }


def get_manual_sms_dashboard_snapshot(day_ymd: Optional[str] = None) -> Dict[str, int]:
    """Calculeaza KPI zilnici pentru SMS manual trimise din interfata."""
    day = (day_ymd or date.today().strftime("%Y-%m-%d")).strip()
    conn = get_conn()
    _ensure_reminder_runtime_tables(conn)
    cur = conn.cursor()
    cur.execute(
        """
        SELECT
            SUM(CASE WHEN status LIKE 'manual\\_%\\_sent' ESCAPE '\\' THEN 1 ELSE 0 END) AS sent,
            SUM(CASE WHEN status LIKE 'manual\\_%\\_failed' ESCAPE '\\' THEN 1 ELSE 0 END) AS failed,
            SUM(CASE WHEN status LIKE 'manual\\_%\\_skipped\\_no\\_phone' ESCAPE '\\' THEN 1 ELSE 0 END) AS no_phone,
            SUM(CASE WHEN status LIKE 'manual\\_%\\_skipped\\_opt\\_out' ESCAPE '\\' THEN 1 ELSE 0 END) AS opt_out,
            SUM(CASE WHEN status='manual_confirm_blocked' THEN 1 ELSE 0 END) AS blocked_confirm
        FROM reminder_dispatch_log
        WHERE dispatch_rule LIKE 'manual_%'
          AND attempted_at IS NOT NULL
          AND SUBSTR(attempted_at, 1, 10)=?
        """,
        (day,),
    )
    row = cur.fetchone()
    conn.close()
    return {
        "sent": int((row["sent"] if row is not None and "sent" in row.keys() else 0) or 0),
        "failed": int((row["failed"] if row is not None and "failed" in row.keys() else 0) or 0),
        "no_phone": int((row["no_phone"] if row is not None and "no_phone" in row.keys() else 0) or 0),
        "opt_out": int((row["opt_out"] if row is not None and "opt_out" in row.keys() else 0) or 0),
        "blocked_confirm": int((row["blocked_confirm"] if row is not None and "blocked_confirm" in row.keys() else 0) or 0),
    }


def get_manual_sms_audit_rows(limit: int = 200, day_ymd: Optional[str] = None) -> List[Dict[str, Any]]:
    """Returneaza istoricul audit al SMS manual pentru vizualizare in UI."""
    lim = max(10, min(2000, int(limit or 200)))
    day = (day_ymd or "").strip()
    conn = get_conn()
    _ensure_reminder_runtime_tables(conn)
    cur = conn.cursor()
    cols = set(get_table_columns("reminder_dispatch_log"))
    src_user_sel = "COALESCE(l.source_user, '') AS source_user" if "source_user" in cols else "'' AS source_user"
    src_role_sel = "COALESCE(l.source_role, '') AS source_role" if "source_role" in cols else "'' AS source_role"
    src_action_sel = "COALESCE(l.source_action, '') AS source_action" if "source_action" in cols else "'' AS source_action"

    where_parts = ["l.dispatch_rule LIKE 'manual_%'"]
    args: List[Any] = []
    if day:
        where_parts.append("l.attempted_at IS NOT NULL")
        where_parts.append("SUBSTR(l.attempted_at, 1, 10)=?")
        args.append(day)
    args.append(lim)
    cur.execute(
        f"""
        SELECT
            l.id,
            l.appointment_id,
            l.attempted_at,
            l.status,
            l.phone,
            l.message,
            l.error,
            l.dispatch_rule,
            {src_user_sel},
            {src_role_sel},
            {src_action_sel},
            a.pacient_id,
            COALESCE(m.nume_prenume, '') AS patient_name
        FROM reminder_dispatch_log l
        LEFT JOIN appointments a ON a.id=l.appointment_id
        LEFT JOIN pacienti_master m ON m.id=a.pacient_id
        WHERE {' AND '.join(where_parts)}
        ORDER BY l.id DESC
        LIMIT ?
        """,
        tuple(args),
    )
    rows = [dict(r) for r in cur.fetchall()]
    conn.close()
    return rows


def run_reminders_scheduler_once(
    now_dt: Optional[datetime] = None,
    sms_config: Optional[Dict[str, Any]] = None,
    force: bool = False,
) -> Dict[str, Any]:
    """Executa o iteratie de scheduler pentru remindere, respectand configuratia activa."""
    now_local = now_dt or datetime.now()
    if not force and get_setting("reminder_auto_enabled", "0") != "1":
        return {"ok": True, "skipped": "disabled"}

    scheduler_mode = (get_setting("reminder_scheduler_mode", "continuous") or "continuous").strip().lower()
    if scheduler_mode not in ("continuous", "fixed_times"):
        scheduler_mode = "continuous"

    if scheduler_mode == "fixed_times":
        times = parse_hhmm_list(get_setting("reminder_times", "08:00,12:00") or "08:00,12:00")
        if not times:
            return {"ok": True, "skipped": "no_times"}
        lookback_h = _setting_int("reminder_catchup_hours", 36, 1, 168)
        max_slots = _setting_int("reminder_catchup_max_slots", 8, 1, 64)
        last_slot = _parse_slot_dt(get_setting(REMINDER_LAST_SLOT_KEY, "") or "")
        start_dt = (last_slot + timedelta(minutes=1)) if last_slot else (now_local - timedelta(hours=lookback_h))
        slots: List[datetime] = []
        day_cur = start_dt.date()
        while day_cur <= now_local.date():
            for hhmm in times:
                hh, mm = [int(x) for x in hhmm.split(":")]
                slot = datetime(day_cur.year, day_cur.month, day_cur.day, hh, mm)
                if start_dt <= slot <= now_local:
                    slots.append(slot)
            day_cur += timedelta(days=1)
        slots.sort()
        slots = slots[:max_slots]
        if not slots:
            return {"ok": True, "skipped": "no_due_slots", "mode": scheduler_mode}

        aggregate = {"ok": True, "mode": scheduler_mode, "slots": len(slots), "runs": []}
        cfg = dict(sms_config or build_sms_gateway_runtime_config())
        for slot in slots:
            res = send_reminders_job_local(cfg, trigger_dt=slot, dispatch_rule=_get_reminder_rule())
            aggregate["runs"].append(res)
            set_setting(REMINDER_LAST_SLOT_KEY, _fmt_slot_dt(slot))
            _set_reminder_last_run_at(slot)
        return aggregate

    # continuous
    due, wait_min = _reminder_interval_status(now_local, force=force)
    if not due:
        return {
            "ok": True,
            "mode": scheduler_mode,
            "skipped": "interval_wait",
            "interval_min": _get_reminder_run_interval_min(),
            "wait_min": wait_min,
        }
    res = send_reminders_job_local(
        dict(sms_config or build_sms_gateway_runtime_config()),
        trigger_dt=now_local,
        dispatch_rule=_get_reminder_rule(),
    )
    set_setting(REMINDER_LAST_SLOT_KEY, _fmt_slot_dt(now_local))
    _set_reminder_last_run_at(now_local)
    return {"ok": True, "mode": scheduler_mode, "runs": [res]}


def send_reminders_job_with_config(sms_config: Optional[Dict[str, Any]] = None, progress_cb=None, cancelled_cb=None) -> Any:
    """Ruleaza jobul de remindere folosind explicit configuratia SMS primita."""
    if progress_cb:
        try:
            progress_cb(10, "Pregatesc trimiterea reminderelor...")
        except Exception:
            pass
    if cancelled_cb and cancelled_cb():
        raise RuntimeError("Trimiterea reminderelor a fost anulata.")

    try:
        added = auto_create_appointments_from_controls()
    except Exception:
        added = 0

    if progress_cb:
        try:
            progress_cb(30, f"Programari pregatite din controale: {int(added or 0)}")
        except Exception:
            pass

    if added:
        if progress_cb:
            try:
                progress_cb(45, "Sincronizez cloud inainte de remindere...")
            except Exception:
                pass
        sync_all(progress_cb=None, cancelled_cb=cancelled_cb)

    if progress_cb:
        try:
            progress_cb(55, "Trimit remindere prin Supabase...")
        except Exception:
            pass

    payload = dict(sms_config or {})
    res = supabase_call_function("send-reminders", payload)

    if progress_cb:
        try:
            progress_cb(100, "Remindere trimise.")
        except Exception:
            pass
    return res


# ============================================================
# Auto-update (Supabase Storage + signed manifest)
# ============================================================
def _get_update_manifest_url() -> str:
    """Returneaza update manifest url."""
    if UPDATE_MANIFEST_URL:
        return UPDATE_MANIFEST_URL.strip()
    if not SUPABASE_URL:
        return ""
    return SUPABASE_URL.rstrip("/") + f"/storage/v1/object/public/{UPDATE_BUCKET}/{UPDATE_MANIFEST_NAME}"


def _canonical_manifest_payload(manifest: Dict[str, Any]) -> bytes:
    """Gestioneaza manifest payload."""
    data = {k: manifest[k] for k in manifest.keys() if k != "signature"}
    return json.dumps(data, sort_keys=True, separators=(",", ":")).encode("utf-8")


def _verify_update_manifest(manifest: Dict[str, Any]) -> None:
    """Gestioneaza update manifest."""
    if not UPDATE_PUBLIC_KEY_B64:
        raise RuntimeError("Cheie publica lipsa pentru update.")
    sig_b64 = (manifest.get("signature") or "").strip()
    if not sig_b64:
        raise RuntimeError("Semnatura lipsa in manifest.")
    try:
        from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PublicKey
    except Exception as e:
        raise RuntimeError(f"Lipseste cryptography pentru verificare semnatura: {e}")
    try:
        pub_bytes = base64.b64decode(UPDATE_PUBLIC_KEY_B64)
        sig = base64.b64decode(sig_b64)
        payload = _canonical_manifest_payload(manifest)
        pub = Ed25519PublicKey.from_public_bytes(pub_bytes)
        pub.verify(sig, payload)
    except Exception:
        raise RuntimeError("Semnatura update invalida.")


def _version_tuple(v: str) -> Tuple[int, ...]:
    """Converteste un string de versiune intr-un tuplu comparabil."""
    parts = []
    for p in re.split(r"[\\.-]", v or ""):
        if p.isdigit():
            parts.append(int(p))
    if not parts:
        parts = [0]
    while len(parts) < 3:
        parts.append(0)
    return tuple(parts[:3])


def _is_newer_version(current: str, newv: str) -> bool:
    """Verifica daca newer version."""
    return _version_tuple(newv) > _version_tuple(current)


def fetch_update_manifest(progress_cb=None, cancelled_cb=None) -> Optional[Dict[str, Any]]:
    """Gestioneaza update manifest."""
    url = _get_update_manifest_url()
    if not url:
        return None
    if progress_cb:
        try:
            progress_cb(10, "Conectez la serverul de update...")
        except Exception:
            pass
    if cancelled_cb and cancelled_cb():
        raise RuntimeError("Verificarea update a fost anulata.")
    req = urllib.request.Request(url, method="GET")
    with urllib.request.urlopen(req, timeout=30) as resp:
        if cancelled_cb and cancelled_cb():
            raise RuntimeError("Verificarea update a fost anulata.")
        raw = resp.read().decode("utf-8")
        if not raw:
            return None
        if progress_cb:
            try:
                progress_cb(70, "Procesez manifestul de update...")
            except Exception:
                pass
        manifest = json.loads(raw)
    if cancelled_cb and cancelled_cb():
        raise RuntimeError("Verificarea update a fost anulata.")
    _verify_update_manifest(manifest)
    if progress_cb:
        try:
            progress_cb(100, "Verificare update finalizata.")
        except Exception:
            pass
    return manifest


def download_update_file(url: str, dest: str, progress_cb=None, cancelled_cb=None) -> str:
    """Gestioneaza update file."""
    if not url:
        raise RuntimeError("URL update lipsa.")
    req = urllib.request.Request(url, method="GET")
    with urllib.request.urlopen(req, timeout=60) as resp:
        total = int(resp.headers.get("Content-Length", "0") or 0)
        read = 0
        with open(dest, "wb") as f:
            while True:
                if cancelled_cb and cancelled_cb():
                    raise RuntimeError("Download anulat.")
                chunk = resp.read(1024 * 128)
                if not chunk:
                    break
                f.write(chunk)
                read += len(chunk)
                if progress_cb and total > 0:
                    progress = int(read * 100 / total)
                    progress_cb(progress, f"Descarc... {read // 1024} KB")
    return dest


def sha256_file(path: str) -> str:
    """Calculeaza hash SHA-256 pentru fisierul indicat."""
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _get_sync_conflict_rule() -> str:
    """Returneaza sync conflict rule."""
    rule = (get_setting(SYNC_CONFLICT_RULE_KEY, SYNC_CONFLICT_RULE_DEFAULT) or SYNC_CONFLICT_RULE_DEFAULT).strip().lower()
    if rule not in {"latest_updated_at_wins", "local_wins", "remote_wins"}:
        return SYNC_CONFLICT_RULE_DEFAULT
    return rule


def _ensure_sync_outbox_table(conn: sqlite3.Connection) -> None:
    """Creeaza tabela outbox pentru operatii locale care trebuie retrimise in cloud."""
    cur = conn.cursor()
    cur.execute(
        f"""
        CREATE TABLE IF NOT EXISTS {SYNC_OUTBOX_TABLE} (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            created_at TEXT,
            table_name TEXT,
            payload_json TEXT,
            attempts INTEGER DEFAULT 0,
            next_retry_at TEXT,
            last_error TEXT,
            updated_at TEXT
        )
        """
    )
    cur.execute(f"CREATE INDEX IF NOT EXISTS idx_sync_outbox_next_retry ON {SYNC_OUTBOX_TABLE}(next_retry_at)")
    cur.execute(f"CREATE INDEX IF NOT EXISTS idx_sync_outbox_table ON {SYNC_OUTBOX_TABLE}(table_name)")


def _enqueue_sync_outbox(
    conn: sqlite3.Connection,
    table_name: str,
    payload_rows: List[Dict[str, Any]],
    error_text: str,
) -> int:
    """Adauga in outbox o operatiune de sync esuata pentru retry ulterior."""
    if not payload_rows:
        return 0
    _ensure_sync_outbox_table(conn)
    cur = conn.cursor()
    try:
        payload_json = json.dumps(payload_rows, ensure_ascii=False)
    except Exception:
        payload_json = "[]"
    now_txt = now_ts()
    cur.execute(
        f"""
        INSERT INTO {SYNC_OUTBOX_TABLE}(created_at, table_name, payload_json, attempts, next_retry_at, last_error, updated_at)
        VALUES (?,?,?,?,?,?,?)
        """,
        (
            now_txt,
            (table_name or "").strip(),
            payload_json,
            0,
            now_txt,
            (error_text or "").strip(),
            now_txt,
        ),
    )
    return int(cur.lastrowid or 0)


def _retry_sync_outbox(progress_cb=None, cancelled_cb=None, max_items: int = 25) -> Dict[str, Any]:
    """Reproceseaza elementele din outbox si curata operatiile retrimise cu succes."""
    conn = get_conn()
    _ensure_sync_outbox_table(conn)
    cur = conn.cursor()
    now_txt = now_ts()
    cur.execute(
        f"""
        SELECT id, table_name, payload_json, attempts
        FROM {SYNC_OUTBOX_TABLE}
        WHERE next_retry_at IS NULL OR TRIM(next_retry_at)='' OR next_retry_at<=?
        ORDER BY id ASC
        LIMIT ?
        """,
        (now_txt, max(1, int(max_items))),
    )
    items = cur.fetchall()
    retried = 0
    sent = 0
    failed = 0
    for it in items:
        if cancelled_cb and cancelled_cb():
            break
        row_id = int(it["id"])
        table = (it["table_name"] or "").strip()
        attempts = int(it["attempts"] or 0)
        raw = (it["payload_json"] or "").strip()
        try:
            payload = json.loads(raw) if raw else []
        except Exception:
            payload = []
        if not table or not isinstance(payload, list) or not payload:
            cur.execute(f"DELETE FROM {SYNC_OUTBOX_TABLE} WHERE id=?", (row_id,))
            continue
        retried += 1
        try:
            supabase_upsert(table, payload)
            sent += len(payload)
            cur.execute(f"DELETE FROM {SYNC_OUTBOX_TABLE} WHERE id=?", (row_id,))
        except Exception as e:
            failed += 1
            attempts_new = attempts + 1
            delay_min = min(120, max(1, 2 ** min(8, attempts_new - 1)))
            next_retry = (datetime.now() + timedelta(minutes=delay_min)).strftime("%Y-%m-%d %H:%M:%S")
            cur.execute(
                f"""
                UPDATE {SYNC_OUTBOX_TABLE}
                SET attempts=?, next_retry_at=?, last_error=?, updated_at=?
                WHERE id=?
                """,
                (attempts_new, next_retry, str(e), now_ts(), row_id),
            )
        if progress_cb:
            try:
                progress_cb(0, f"Retry outbox: {retried}/{len(items)}")
            except Exception:
                pass

    cur.execute(f"SELECT COUNT(1) FROM {SYNC_OUTBOX_TABLE}")
    _pending_row = cur.fetchone()
    pending = int((_pending_row[0] if _pending_row is not None else 0) or 0)
    conn.commit()
    conn.close()
    return {"retried": retried, "sent_rows": sent, "failed_items": failed, "pending": pending}


def get_sync_outbox_health(limit: int = 30) -> Dict[str, Any]:
    """Returneaza starea outbox-ului de sincronizare pentru monitorizare."""
    conn = get_conn()
    _ensure_sync_outbox_table(conn)
    cur = conn.cursor()
    cur.execute(f"SELECT COUNT(1) AS cnt FROM {SYNC_OUTBOX_TABLE}")
    _row_total = cur.fetchone()
    total = int((_row_total["cnt"] if _row_total is not None else 0) or 0)
    cur.execute(
        f"""
        SELECT table_name, COUNT(1) AS cnt
        FROM {SYNC_OUTBOX_TABLE}
        GROUP BY table_name
        ORDER BY cnt DESC, table_name ASC
        """
    )
    by_table = {str(r["table_name"] or ""): int(r["cnt"] or 0) for r in cur.fetchall()}
    cur.execute(
        f"""
        SELECT id, created_at, table_name, attempts, next_retry_at, last_error
        FROM {SYNC_OUTBOX_TABLE}
        ORDER BY id DESC
        LIMIT ?
        """,
        (max(1, int(limit)),),
    )
    items = [dict(r) for r in cur.fetchall()]
    conn.close()
    return {"total": total, "by_table": by_table, "items": items}


def get_sync_id_by_local_id(
    table: str,
    local_id: Optional[int],
    conn: Optional[sqlite3.Connection] = None,
    cache: Optional[Dict[Tuple[str, int], Optional[str]]] = None,
) -> Optional[str]:
    """Mapeaza ID local la sync_id pentru relatii locale-cloud."""
    if local_id is None:
        return None
    try:
        local_key = int(local_id)
    except Exception:
        return None
    cache_key = (str(table), int(local_key))
    if cache is not None and cache_key in cache:
        return cache.get(cache_key)

    own_conn = conn is None
    c = conn or get_conn()
    cur = c.cursor()
    cur.execute(f"SELECT sync_id FROM {table} WHERE id=?", (local_id,))
    row = cur.fetchone()
    if own_conn:
        c.close()
    out = row[0] if row else None
    if cache is not None:
        cache[cache_key] = out
    return out


def get_local_id_by_sync_id(
    table: str,
    sync_id: Optional[str],
    conn: Optional[sqlite3.Connection] = None,
    cache: Optional[Dict[Tuple[str, str], Optional[int]]] = None,
) -> Optional[int]:
    """Mapeaza sync_id la ID local pentru rezolvare de referinte."""
    if not sync_id:
        return None
    sync_txt = str(sync_id).strip()
    if not sync_txt:
        return None
    cache_key = (str(table), sync_txt)
    if cache is not None and cache_key in cache:
        return cache.get(cache_key)

    own_conn = conn is None
    c = conn or get_conn()
    cur = c.cursor()
    cur.execute(f"SELECT id FROM {table} WHERE sync_id=?", (sync_id,))
    row = cur.fetchone()
    if own_conn:
        c.close()
    out = int(row[0]) if row else None
    if cache is not None:
        cache[cache_key] = out
    return out


def local_row_to_remote(
    table: str,
    row: sqlite3.Row,
    fk_map: Dict[str, Tuple[str, str]],
    conn: Optional[sqlite3.Connection] = None,
    sync_id_cache: Optional[Dict[Tuple[str, int], Optional[str]]] = None,
) -> Dict[str, Any]:
    """Converteste un rand local in payload remote cu mapare de chei externe."""
    rd = dict(row)
    out: Dict[str, Any] = {}
    for k, v in rd.items():
        if k == "id":
            continue
        if k == "sms_opt_out":
            # Optional local-only safety flag; skip until cloud schema explicitly enables it.
            continue
        if k in fk_map:
            ref_table, remote_col = fk_map[k]
            out[remote_col] = get_sync_id_by_local_id(ref_table, v, conn=conn, cache=sync_id_cache)
            continue
        out[k] = v
    return out


def _find_existing_id_by_category_and_name(
    conn: sqlite3.Connection,
    table: str,
    cols: List[str],
    data: Dict[str, Any],
    threshold: Optional[float] = None,
) -> Optional[int]:
    """Cauta existing ID by category and name."""
    if "id" not in cols or "category" not in cols:
        return None

    category = (data.get("category") or "").strip()
    if not category:
        return None

    name_col = None
    for candidate in ("item", "name", "title", "test_name"):
        if candidate in cols and (data.get(candidate) or "").strip():
            name_col = candidate
            break
    if not name_col:
        return None

    incoming_name = (data.get(name_col) or "").strip()
    if not incoming_name:
        return None

    if threshold is None:
        threshold = get_category_name_match_threshold()

    sql = f"SELECT id, {name_col} FROM {table} WHERE LOWER(TRIM(category)) = LOWER(TRIM(?))"
    params: List[Any] = [category]

    if "pacient_id" in cols and data.get("pacient_id") is not None:
        sql += " AND pacient_id = ?"
        params.append(data.get("pacient_id"))

    if "deleted" in cols:
        sql += " AND COALESCE(deleted,0)=0"

    sql += f" AND TRIM(COALESCE({name_col},'')) <> ''"
    sql += " LIMIT 300"

    cur = conn.cursor()
    cur.execute(sql, tuple(params))
    rows = cur.fetchall()
    if not rows:
        return None

    incoming_norm = _norm_name(incoming_name)
    best_id = None
    best_score = 0.0
    for row in rows:
        local_name = (row[name_col] or "").strip() if name_col in row.keys() else ""
        if not local_name:
            continue

        if _norm_name(local_name) == incoming_norm:
            return int(row["id"])

        score = _ratio(local_name, incoming_name)
        if score > best_score:
            best_score = score
            best_id = int(row["id"])

    if best_id is not None and best_score >= threshold:
        return best_id
    return None


def upsert_local_from_remote(
    table: str,
    remote_row: Dict[str, Any],
    fk_map: Dict[str, Tuple[str, str]],
    conn: Optional[sqlite3.Connection] = None,
    local_id_cache: Optional[Dict[Tuple[str, str], Optional[int]]] = None,
):
    """Aplica in baza locala un rand primit din cloud cu reguli de conflict."""
    cols = get_table_columns(table)
    has_id = "id" in cols
    sync_id = remote_row.get("sync_id")
    if not sync_id:
        return

    # map fk_sync_id -> local id
    data: Dict[str, Any] = {}
    for k in cols:
        if k == "id":
            continue
        if k in fk_map:
            ref_table, remote_col = fk_map[k]
            fk_sync_id = remote_row.get(remote_col)
            data[k] = get_local_id_by_sync_id(ref_table, fk_sync_id, conn=conn, cache=local_id_cache)
        else:
            if k in remote_row:
                data[k] = remote_row.get(k)

    own_conn = conn is None
    c = conn or get_conn()
    cur = c.cursor()
    if has_id:
        cur.execute(f"SELECT id, updated_at FROM {table} WHERE sync_id=?", (sync_id,))
    else:
        cur.execute(f"SELECT updated_at FROM {table} WHERE sync_id=?", (sync_id,))
    row = cur.fetchone()
    conflict_rule = _get_sync_conflict_rule()
    if row:
        if conflict_rule == "local_wins":
            if own_conn:
                c.close()
            return
        local_updated = row[1] if has_id else row[0]
        local_updated = local_updated or ""
        remote_updated = remote_row.get("updated_at") or ""
        if (
            conflict_rule == "latest_updated_at_wins"
            and local_updated
            and remote_updated
            and local_updated >= remote_updated
        ):
            if own_conn:
                c.close()
            return
        sets = ", ".join([f"{k}=?" for k in data.keys()])
        vals = list(data.values()) + [sync_id]
        cur.execute(f"UPDATE {table} SET {sets} WHERE sync_id=?", vals)
    else:
        matched_id = _find_existing_id_by_category_and_name(c, table, cols, data)
        if matched_id is not None and data:
            sets = ", ".join([f"{k}=?" for k in data.keys()])
            vals = list(data.values()) + [matched_id]
            cur.execute(f"UPDATE {table} SET {sets} WHERE id=?", vals)
        elif table == "users" and (data.get("username") or "").strip():
            username = (data.get("username") or "").strip()
            cur.execute(
                "SELECT id, updated_at FROM users WHERE LOWER(TRIM(username)) = LOWER(TRIM(?))",
                (username,),
            )
            user_row = cur.fetchone()
            if user_row and data:
                local_updated = (user_row[1] or "") if len(user_row.keys()) > 1 else ""
                remote_updated = remote_row.get("updated_at") or ""
                if local_updated and remote_updated and local_updated >= remote_updated:
                    if own_conn:
                        c.close()
                    return
                sets = ", ".join([f"{k}=?" for k in data.keys()])
                vals = list(data.values()) + [int(user_row[0])]
                cur.execute("UPDATE users SET " + sets + " WHERE id=?", vals)
            else:
                cols_ins = list(data.keys())
                vals = [data[k] for k in cols_ins]
                cur.execute(
                    f"INSERT INTO {table} ({', '.join(cols_ins)}) VALUES ({', '.join(['?']*len(cols_ins))})",
                    vals,
                )
        else:
            cols_ins = list(data.keys())
            vals = [data[k] for k in cols_ins]
            cur.execute(
                f"INSERT INTO {table} ({', '.join(cols_ins)}) VALUES ({', '.join(['?']*len(cols_ins))})",
                vals,
            )
    if own_conn:
        c.commit()
        c.close()


def _persist_sync_summary(summary: Dict[str, Any]) -> None:
    """Persista sumarul ultimei rulari de sincronizare pentru diagnostic."""
    try:
        stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        json_path = SYNC_LOG_DIR / f"sync_{stamp}.json"
        csv_path = SYNC_LOG_DIR / f"sync_{stamp}.csv"

        json_path.write_text(json.dumps(summary, ensure_ascii=False, indent=2), encoding="utf-8")
        tables = summary.get("tables") if isinstance(summary.get("tables"), list) else []
        upload = summary.get("upload") if isinstance(summary.get("upload"), dict) else {}
        download = summary.get("download") if isinstance(summary.get("download"), dict) else {}
        if not tables:
            tables = sorted(set(list(upload.keys()) + list(download.keys())))

        with open(csv_path, "w", encoding="utf-8", newline="") as f:
            writer = csv.writer(f)
            writer.writerow(["metric", "value"])
            writer.writerow(["started_at", summary.get("started_at") or ""])
            writer.writerow(["finished_at", summary.get("finished_at") or ""])
            writer.writerow(["duration_sec", summary.get("duration_sec") or ""])
            writer.writerow(["upload_total", int(summary.get("upload_total") or 0)])
            writer.writerow(["download_total", int(summary.get("download_total") or 0)])
            writer.writerow([])
            writer.writerow(["table", "upload", "download"])
            for table in tables:
                writer.writerow([table, int(upload.get(table) or 0), int(download.get(table) or 0)])

        # retention: keep sync logs only for recent N days
        try:
            keep_days = max(1, int(SYNC_LOG_RETENTION_DAYS))
            cutoff_ts = time.time() - (keep_days * 24 * 60 * 60)
            files = [p for p in SYNC_LOG_DIR.glob("sync_*") if p.is_file()]
            for old in files:
                try:
                    if old.stat().st_mtime < cutoff_ts:
                        old.unlink()
                except Exception:
                    pass
        except Exception:
            pass
    except Exception:
        pass


def sync_all(progress_cb=None, cancelled_cb=None):
    """Ruleaza sincronizarea bidirectionala standard intre baza locala si Supabase."""
    def is_cancelled():
        """Verifica daca cancelled ca helper intern in `sync_all`."""
        return bool(cancelled_cb and cancelled_cb())

    started_at = now_ts()
    started_perf = time.time()
    total_steps = max(1, len(SYNC_TABLES) * 4)
    step = 0
    upload_counts: Dict[str, int] = {}
    download_counts: Dict[str, int] = {}
    upload_errors: Dict[str, str] = {}
    download_errors: Dict[str, str] = {}
    outbox_retry: Dict[str, Any] = {"retried": 0, "sent_rows": 0, "failed_items": 0, "pending": 0}
    fk_sync_id_cache: Dict[Tuple[str, int], Optional[str]] = {}
    fk_local_id_cache: Dict[Tuple[str, str], Optional[int]] = {}

    def tick(msg: str):
        """Actualizeaza progresul incremental al rularii curente (helper intern pentru `sync_all`)."""
        nonlocal step
        step += 1
        if progress_cb:
            progress_cb(int(step * 100 / total_steps), msg)

    last_sync = get_setting("sync_last_at", "")
    last_sync = last_sync or None

    if progress_cb:
        progress_cb(1, "Pregatesc sincronizarea Supabase...")

    try:
        outbox_retry = _retry_sync_outbox(progress_cb=None, cancelled_cb=cancelled_cb, max_items=40)
    except Exception:
        outbox_retry = {"retried": 0, "sent_rows": 0, "failed_items": 0, "pending": 0}

    total_tables = max(1, len(SYNC_TABLES))

    for idx, cfg in enumerate(SYNC_TABLES, start=1):
        if is_cancelled():
            return {"cancelled": True}
        table = cfg["table"]
        fk_map = cfg.get("fk", {})
        tick(f"Upload {table} ({idx}/{total_tables}) - colectare")
        conn = get_conn()
        cur = conn.cursor()
        if last_sync:
            cur.execute(f"SELECT * FROM {table} WHERE updated_at > ?", (last_sync,))
        else:
            cur.execute(f"SELECT * FROM {table}")
        rows = cur.fetchall()
        payload = [local_row_to_remote(table, r, fk_map, conn=conn, sync_id_cache=fk_sync_id_cache) for r in rows]
        conn.close()
        upload_counts[table] = int(len(payload))
        tick(f"Upload {table} ({idx}/{total_tables}) - trimit {len(payload)} randuri")
        if payload:
            try:
                supabase_upsert(table, payload)
            except Exception as e:
                upload_errors[table] = str(e)
                try:
                    conn2 = get_conn()
                    _enqueue_sync_outbox(conn2, table, payload, str(e))
                    conn2.commit()
                    conn2.close()
                except Exception:
                    pass

    for idx, cfg in enumerate(SYNC_TABLES, start=1):
        if is_cancelled():
            return {"cancelled": True}
        table = cfg["table"]
        fk_map = cfg.get("fk", {})
        tick(f"Download {table} ({idx}/{total_tables}) - solicit")
        try:
            remote_rows = supabase_fetch_updated(table, last_sync)
        except Exception as e:
            download_errors[table] = str(e)
            remote_rows = []
        download_counts[table] = int(len(remote_rows))
        conn_local = get_conn()
        applied = 0
        commit_every = 200
        try:
            for r in remote_rows:
                try:
                    upsert_local_from_remote(
                        table,
                        r,
                        fk_map,
                        conn=conn_local,
                        local_id_cache=fk_local_id_cache,
                    )
                    applied += 1
                    if applied % commit_every == 0:
                        conn_local.commit()
                except Exception as e:
                    download_errors[table] = str(e)
            conn_local.commit()
        finally:
            try:
                conn_local.close()
            except Exception:
                pass
        tick(f"Download {table} ({idx}/{total_tables}) - primit {len(remote_rows)} randuri")

    finished_at = now_ts()
    duration_sec = max(0.0, float(time.time() - started_perf))
    summary = {
        "started_at": started_at,
        "finished_at": finished_at,
        "duration_sec": round(duration_sec, 2),
        "tables": [cfg.get("table") for cfg in SYNC_TABLES],
        "upload": upload_counts,
        "download": download_counts,
        "upload_errors": upload_errors,
        "download_errors": download_errors,
        "upload_total": int(sum(upload_counts.values())),
        "download_total": int(sum(download_counts.values())),
        "outbox_retry": outbox_retry,
    }

    try:
        summary["outbox_health"] = get_sync_outbox_health(limit=15)
    except Exception:
        summary["outbox_health"] = {"total": 0, "by_table": {}, "items": []}

    _persist_sync_summary(summary)

    set_setting("sync_last_summary_json", json.dumps(summary, ensure_ascii=False))
    set_setting("sync_last_at", finished_at)
    if progress_cb:
        progress_cb(100, "Sync Supabase finalizat.")
    return {"ok": True, "summary": summary}


def sync_download_all_from_cloud(progress_cb=None, cancelled_cb=None):
    """Ruleaza full download din cloud pentru repopulare completa locala."""
    def is_cancelled() -> bool:
        """Verifica daca cancelled ca helper intern in `sync_download_all_from_cloud`."""
        return bool(cancelled_cb and cancelled_cb())

    started_at = now_ts()
    started_perf = time.time()
    download_counts: Dict[str, int] = {}
    upload_counts: Dict[str, int] = {cfg.get("table"): 0 for cfg in SYNC_TABLES}
    fk_local_id_cache: Dict[Tuple[str, str], Optional[int]] = {}
    total_tables = max(1, len(SYNC_TABLES))

    if progress_cb:
        progress_cb(1, "Pornesc re-sincronizarea completa din cloud...")

    for idx, cfg in enumerate(SYNC_TABLES, start=1):
        if is_cancelled():
            return {"cancelled": True}
        table = cfg["table"]
        fk_map = cfg.get("fk", {})
        if progress_cb:
            progress_cb(
                min(95, int(((idx - 1) * 100) / total_tables)),
                f"Download {table} ({idx}/{total_tables}) - solicit",
            )
        remote_rows = supabase_fetch_updated(table, None)
        download_counts[table] = int(len(remote_rows))
        total_rows = max(1, len(remote_rows))
        conn_local = get_conn()
        try:
            for row_idx, r in enumerate(remote_rows, start=1):
                if is_cancelled():
                    return {"cancelled": True}
                upsert_local_from_remote(
                    table,
                    r,
                    fk_map,
                    conn=conn_local,
                    local_id_cache=fk_local_id_cache,
                )
                if row_idx % 200 == 0:
                    conn_local.commit()
                if progress_cb and (row_idx == total_rows or row_idx % 200 == 0):
                    base = (idx - 1) / total_tables
                    frac = row_idx / total_rows
                    pct = int(min(98, (base + (frac / total_tables)) * 100))
                    progress_cb(pct, f"Download {table}: {row_idx}/{total_rows}")
            conn_local.commit()
        finally:
            try:
                conn_local.close()
            except Exception:
                pass

    finished_at = now_ts()
    duration_sec = max(0.0, float(time.time() - started_perf))
    summary = {
        "started_at": started_at,
        "finished_at": finished_at,
        "duration_sec": round(duration_sec, 2),
        "tables": [cfg.get("table") for cfg in SYNC_TABLES],
        "upload": upload_counts,
        "download": download_counts,
        "upload_total": 0,
        "download_total": int(sum(download_counts.values())),
        "mode": "download_only_full_resync",
    }
    _persist_sync_summary(summary)
    set_setting("sync_last_summary_json", json.dumps(summary, ensure_ascii=False))
    set_setting("sync_last_at", finished_at)
    if progress_cb:
        progress_cb(100, "Re-sincronizare completa din cloud finalizata.")
    return {"ok": True, "summary": summary, "mode": "download_only_full_resync"}


def get_sync_pending_upload_counts(last_sync: Optional[str]) -> Dict[str, Any]:
    """Calculeaza cate modificari locale sunt in asteptare de upload."""
    conn = get_conn()
    cur = conn.cursor()
    counts: Dict[str, int] = {}
    total = 0
    for cfg in SYNC_TABLES:
        table = (cfg.get("table") or "").strip()
        if not table or not _is_safe_sql_table_name(table):
            continue
        if not _db_table_exists_cur(cur, table):
            continue
        cols = _db_table_columns_cur(cur, table)
        if "updated_at" not in cols:
            continue
        where_parts: List[str] = []
        args: List[Any] = []
        if last_sync:
            where_parts.append("updated_at > ?")
            args.append(last_sync)
        where_sql = f"WHERE {' AND '.join(where_parts)}" if where_parts else ""
        try:
            cur.execute(f"SELECT COUNT(1) FROM {table} {where_sql}", tuple(args))
            row = cur.fetchone()
            cnt = int(row[0] or 0) if row is not None else 0
        except Exception:
            cnt = 0
        counts[table] = cnt
        total += cnt
    conn.close()
    return {
        "total": int(total),
        "tables": counts,
    }


def log_action(action: str, details: str = ""):
    """Inregistreaza actiunea curenta in jurnalul de activitate al aplicatiei."""
    try:
        conn = get_conn()
        cols = ["ts", "action", "details", "user", "role"]
        vals = [
            datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
            action,
            details,
            get_current_user(),
            get_current_role(),
        ]
        if table_has_column("activity_log", "sync_id"):
            cols.extend(["sync_id", "updated_at", "deleted", "device_id"])
            vals.extend([uuid.uuid4().hex, now_ts(), 0, get_device_id()])
        conn.execute(
            f"INSERT INTO activity_log({', '.join(cols)}) VALUES ({', '.join(['?']*len(cols))})",
            vals,
        )
        conn.commit()
        conn.close()
    except Exception:
        pass


def get_activity_log(limit: int = 200) -> List[Dict[str, Any]]:
    """Returneaza activity log."""
    conn = get_conn()
    cur = conn.cursor()
    if table_has_column("activity_log", "deleted"):
        cur.execute(
            "SELECT id, ts, action, details, user, role FROM activity_log WHERE COALESCE(deleted,0)=0 ORDER BY id DESC LIMIT ?",
            (limit,),
        )
    else:
        cur.execute(
            "SELECT id, ts, action, details, user, role FROM activity_log ORDER BY id DESC LIMIT ?",
            (limit,),
        )
    rows = [dict(r) for r in cur.fetchall()]
    conn.close()
    return rows


def get_nomenclator_values(table_name: str, include_inactive: bool = False) -> List[str]:
    """Returneaza nomenclator values."""
    allowed = set(CONSULT_NOMENCLATOR_TABLES.values())
    if table_name not in allowed:
        return []
    conn = get_conn()
    cur = conn.cursor()
    where_parts = []
    if table_has_column(table_name, "deleted"):
        where_parts.append("COALESCE(deleted,0)=0")
    if table_has_column(table_name, "valid") and not include_inactive:
        where_parts.append("COALESCE(valid,1)=1")
    where_sql = f"WHERE {' AND '.join(where_parts)}" if where_parts else ""
    order_sql = "ORDER BY COALESCE(cod_drg, 999999) ASC, denumire COLLATE NOCASE ASC"
    cur.execute(f"SELECT denumire FROM {table_name} {where_sql} {order_sql}")
    out = []
    seen = set()
    for row in cur.fetchall():
        val = (row[0] or "").strip()
        if val and val not in seen:
            seen.add(val)
            out.append(val)
    conn.close()
    return out


def get_nomenclator_values_by_key(field_key: str, include_inactive: bool = False) -> List[str]:
    """Returneaza nomenclator values by key."""
    table_name = CONSULT_NOMENCLATOR_TABLES.get(field_key)
    if not table_name:
        return []
    return get_nomenclator_values(table_name, include_inactive=include_inactive)


def _seed_nomenclator_table(
    cur: sqlite3.Cursor,
    table_name: str,
    rows: List[Tuple[str, Optional[int], int]],
):
    """Gestioneaza nomenclator table."""
    ts = now_ts()
    for denumire, cod_drg, valid in rows:
        den = (denumire or "").strip()
        if not den:
            continue
        cur.execute(
            f"SELECT id FROM {table_name} WHERE LOWER(TRIM(denumire)) = LOWER(TRIM(?)) LIMIT 1",
            (den,),
        )
        existing = cur.fetchone()
        if existing is None:
            cur.execute(
                f"""
                INSERT INTO {table_name}(denumire, cod_drg, valid, sync_id, updated_at, deleted, device_id)
                VALUES (?,?,?,?,?,?,?)
                """,
                (den, cod_drg, int(valid), uuid.uuid4().hex, ts, 0, None),
            )
        else:
            cur.execute(
                f"""
                UPDATE {table_name}
                SET cod_drg=?, valid=?, deleted=0, updated_at=?
                WHERE id=?
                """,
                (cod_drg, int(valid), ts, int(existing[0])),
            )


def seed_nomenclatoare_defaults(cur: sqlite3.Cursor):
    """Gestioneaza nomenclatoare defaults."""
    for table_name, rows in NOMENCLATOR_DEFAULTS.items():
        _seed_nomenclator_table(cur, table_name, rows)


def _db_table_exists_cur(cur: sqlite3.Cursor, table_name: str) -> bool:
    """Gestioneaza table exists cursor."""
    cur.execute("SELECT 1 FROM sqlite_master WHERE type='table' AND name=?", (table_name,))
    return cur.fetchone() is not None


def _db_table_columns_cur(cur: sqlite3.Cursor, table_name: str) -> set:
    """Gestioneaza table columns cursor."""
    if not _db_table_exists_cur(cur, table_name):
        return set()
    cur.execute(f"PRAGMA table_info({table_name})")
    return {str(r[1]) for r in cur.fetchall()}


def _schema_meta_ensure_table(cur: sqlite3.Cursor) -> None:
    """Asigura tabela schema_meta folosita pentru versionarea migrarilor locale."""
    cur.execute(
        f"""
        CREATE TABLE IF NOT EXISTS {DB_SCHEMA_META_TABLE} (
            key TEXT PRIMARY KEY,
            value TEXT,
            updated_at TEXT
        )
        """
    )


def _schema_meta_get_version(cur: sqlite3.Cursor) -> int:
    """Citeste versiunea curenta de schema din schema_meta."""
    _schema_meta_ensure_table(cur)
    cur.execute(f"SELECT value FROM {DB_SCHEMA_META_TABLE} WHERE key=?", (DB_SCHEMA_VERSION_KEY,))
    row = cur.fetchone()
    if not row:
        return 0
    try:
        return max(0, int(str(row[0]).strip()))
    except Exception:
        return 0


def _schema_meta_set_version(cur: sqlite3.Cursor, version: int) -> None:
    """Actualizeaza versiunea de schema dupa o migrare reusita."""
    _schema_meta_ensure_table(cur)
    cur.execute(
        f"""
        INSERT INTO {DB_SCHEMA_META_TABLE}(key, value, updated_at)
        VALUES (?,?,?)
        ON CONFLICT(key) DO UPDATE SET
            value=excluded.value,
            updated_at=excluded.updated_at
        """,
        (DB_SCHEMA_VERSION_KEY, str(int(version)), now_ts()),
    )


def _invalidate_table_col_cache(*tables: str) -> None:
    """Gestioneaza table col cache."""
    for table in tables:
        _TABLE_COL_CACHE.pop(table, None)


def _ensure_table_column(cur: sqlite3.Cursor, table_name: str, column_name: str, sql_type: str) -> None:
    """Asigura table column."""
    cols = _db_table_columns_cur(cur, table_name)
    if column_name not in cols:
        cur.execute(f"ALTER TABLE {table_name} ADD COLUMN {column_name} {sql_type}")
        _invalidate_table_col_cache(table_name)


def _migration_v1_core_columns(conn: sqlite3.Connection, cur: sqlite3.Cursor) -> None:
    # pacienti_master: varsta/email
    """Gestioneaza V1 core columns."""
    cols = _db_table_columns_cur(cur, "pacienti_master")
    if "varsta" not in cols:
        cur.execute("ALTER TABLE pacienti_master ADD COLUMN varsta INTEGER")
        if "varsta_cache" in cols:
            cur.execute("UPDATE pacienti_master SET varsta = varsta_cache WHERE varsta IS NULL")
        _invalidate_table_col_cache("pacienti_master")
    if "email" not in cols:
        cur.execute("ALTER TABLE pacienti_master ADD COLUMN email TEXT")
        _invalidate_table_col_cache("pacienti_master")

    # activity_log: user/role
    cols = _db_table_columns_cur(cur, "activity_log")
    if "user" not in cols:
        cur.execute("ALTER TABLE activity_log ADD COLUMN user TEXT")
        _invalidate_table_col_cache("activity_log")
    if "role" not in cols:
        cur.execute("ALTER TABLE activity_log ADD COLUMN role TEXT")
        _invalidate_table_col_cache("activity_log")

    # users: full_name
    cols = _db_table_columns_cur(cur, "users")
    if "full_name" not in cols:
        cur.execute("ALTER TABLE users ADD COLUMN full_name TEXT")
        _invalidate_table_col_cache("users")
    cur.execute("UPDATE users SET full_name=COALESCE(NULLIF(TRIM(full_name),''), username)")

    # prescriptions: signature fields
    cols = _db_table_columns_cur(cur, "prescriptions")
    if "signed_by" not in cols:
        cur.execute("ALTER TABLE prescriptions ADD COLUMN signed_by TEXT")
        _invalidate_table_col_cache("prescriptions")
    if "signature_path" not in cols:
        cur.execute("ALTER TABLE prescriptions ADD COLUMN signature_path TEXT")
        _invalidate_table_col_cache("prescriptions")
    if "signed_at" not in cols:
        cur.execute("ALTER TABLE prescriptions ADD COLUMN signed_at TEXT")
        _invalidate_table_col_cache("prescriptions")

    # medical_letters: signature fields
    cols = _db_table_columns_cur(cur, "medical_letters")
    if "signed_by" not in cols:
        cur.execute("ALTER TABLE medical_letters ADD COLUMN signed_by TEXT")
        _invalidate_table_col_cache("medical_letters")
    if "signature_path" not in cols:
        cur.execute("ALTER TABLE medical_letters ADD COLUMN signature_path TEXT")
        _invalidate_table_col_cache("medical_letters")
    if "signed_at" not in cols:
        cur.execute("ALTER TABLE medical_letters ADD COLUMN signed_at TEXT")
        _invalidate_table_col_cache("medical_letters")


def _migration_v2_consulturi_cleanup(conn: sqlite3.Connection, cur: sqlite3.Cursor) -> None:
    """Gestioneaza V2 consulturi cleanup."""
    cols = _db_table_columns_cur(cur, "consulturi")
    legacy_cols = [
        "tip_internare",
        "tip_externare",
        "stare_externare",
        "situatie_speciala",
        "tip_asigurare_cnas",
        "tip_finantare_sectie",
        "ocupatie",
        "specialitate",
        "statut_asigurare",
        "categorie_asigurat",
        "nivel_instruire",
        "accident",
        "criteriu_internare",
        "tip_serviciu",
        "cas_asigurari",
    ]
    for legacy_col in legacy_cols:
        if legacy_col in cols:
            # Best effort: physically remove legacy columns where supported.
            try:
                cur.execute(f"ALTER TABLE consulturi DROP COLUMN {legacy_col}")
                cols.remove(legacy_col)
                _invalidate_table_col_cache("consulturi")
            except Exception:
                pass
    if "diagnostic_secundar" not in cols:
        cur.execute("ALTER TABLE consulturi ADD COLUMN diagnostic_secundar TEXT")
        _invalidate_table_col_cache("consulturi")
    cols = _db_table_columns_cur(cur, "consulturi")
    if "diagnostic_liber" not in cols:
        cur.execute("ALTER TABLE consulturi ADD COLUMN diagnostic_liber TEXT")
        _invalidate_table_col_cache("consulturi")


def _migration_v3_runtime_tables(conn: sqlite3.Connection, cur: sqlite3.Cursor) -> None:
    """Gestioneaza V3 runtime tables."""
    ensure_recycle_bin_tables(conn)
    _ensure_reminder_runtime_tables(conn)
    _ensure_appointment_sms_template_state_table(conn)

    _ensure_table_column(cur, "reminder_dispatch_log", "dispatch_rule", "TEXT")
    _ensure_table_column(cur, "reminder_dispatch_log", "attempted_at", "TEXT")
    _ensure_table_column(cur, "appointment_sms_template_state", "confirm_sent_at", "TEXT")
    _ensure_table_column(cur, "appointment_sms_template_state", "cancel_sent_at", "TEXT")
    _ensure_table_column(cur, "appointment_sms_template_state", "last_template_key", "TEXT")
    _ensure_table_column(cur, "appointment_sms_template_state", "last_status", "TEXT")
    _ensure_table_column(cur, "appointment_sms_template_state", "last_error", "TEXT")
    _ensure_table_column(cur, "appointment_sms_template_state", "updated_at", "TEXT")
    cur.execute(
        "CREATE INDEX IF NOT EXISTS idx_reminder_log_rule_date ON reminder_dispatch_log(dispatch_rule, attempted_at)"
    )


def _migration_v4_reminder_audit(conn: sqlite3.Connection, cur: sqlite3.Cursor) -> None:
    """Gestioneaza V4 reminder audit."""
    _ensure_reminder_runtime_tables(conn)
    _ensure_table_column(cur, "reminder_dispatch_log", "source_user", "TEXT")
    _ensure_table_column(cur, "reminder_dispatch_log", "source_role", "TEXT")
    _ensure_table_column(cur, "reminder_dispatch_log", "source_action", "TEXT")
    cur.execute(
        "CREATE INDEX IF NOT EXISTS idx_reminder_log_user_ts ON reminder_dispatch_log(source_user, attempted_at)"
    )


def _migration_v5_diagnostic_liber(conn: sqlite3.Connection, cur: sqlite3.Cursor) -> None:
    """Gestioneaza V5 diagnostic liber."""
    _ensure_table_column(cur, "consulturi", "diagnostic_liber", "TEXT")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_cons_diag_liber ON consulturi(diagnostic_liber)")


def _migration_v6_entity_audit(conn: sqlite3.Connection, cur: sqlite3.Cursor) -> None:
    """Gestioneaza V6 entity audit."""
    _ensure_entity_audit_table(conn)


def _migration_v7_sms_optout_sync_outbox(conn: sqlite3.Connection, cur: sqlite3.Cursor) -> None:
    """Gestioneaza V7 SMS optout sync outbox."""
    _ensure_table_column(cur, "pacienti_master", "sms_opt_out", "INTEGER DEFAULT 0")
    cur.execute("UPDATE pacienti_master SET sms_opt_out=COALESCE(sms_opt_out,0)")
    _ensure_sync_outbox_table(conn)
    cur.execute("CREATE INDEX IF NOT EXISTS idx_master_sms_opt_out ON pacienti_master(sms_opt_out)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_master_email ON pacienti_master(email)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_master_name_phone ON pacienti_master(nume_prenume, telefon)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_cons_diag_principal ON consulturi(diagnostic_principal)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_cons_diag_secundar ON consulturi(diagnostic_secundar)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_cons_status_date ON consulturi(status_follow_up, data_consultului)")


def _create_schema_migration_backup(conn: sqlite3.Connection, from_version: int, to_version: int) -> str:
    """Creeaza schema migration backup."""
    stamp = datetime.now().strftime("%Y-%m-%d_%H%M%S")
    backup_path = DB_SCHEMA_MIGRATION_BACKUP_DIR / (
        f"pacienti_before_schema_v{int(from_version)}_to_v{int(to_version)}_{stamp}.db"
    )
    dst = sqlite3.connect(str(backup_path))
    try:
        conn.backup(dst)
    finally:
        dst.close()
    return str(backup_path)


def _run_db_schema_migrations(conn: sqlite3.Connection, cur: sqlite3.Cursor) -> Dict[str, Any]:
    """Ruleaza migrari incrementale de schema si returneaza raportul executiei."""
    migrations = [
        (1, "Core compatibility columns", _migration_v1_core_columns),
        (2, "Consulturi legacy cleanup", _migration_v2_consulturi_cleanup),
        (3, "Reminder/runtime schema", _migration_v3_runtime_tables),
        (4, "Reminder audit metadata", _migration_v4_reminder_audit),
        (5, "Diagnostic liber support", _migration_v5_diagnostic_liber),
        (6, "Entity audit trail", _migration_v6_entity_audit),
        (7, "SMS opt-out + sync outbox + performance indexes", _migration_v7_sms_optout_sync_outbox),
    ]
    target_version = int(DB_SCHEMA_VERSION_CURRENT)
    current_version = int(_schema_meta_get_version(cur))
    report: Dict[str, Any] = {
        "schema_version_before": current_version,
        "schema_version_after": current_version,
        "schema_version_target": target_version,
        "applied_migrations": [],
        "migration_backup_path": "",
        "issues": [],
    }

    if current_version > target_version:
        report["issues"].append(
            f"Schema DB v{current_version} este mai noua decat build-ul curent (v{target_version})."
        )
        return report

    pending = [m for m in migrations if int(m[0]) > current_version and int(m[0]) <= target_version]
    if pending:
        report["migration_backup_path"] = _create_schema_migration_backup(
            conn,
            current_version,
            target_version,
        )

    for version, name, func in pending:
        func(conn, cur)
        _schema_meta_set_version(cur, int(version))
        report["schema_version_after"] = int(version)
        report["applied_migrations"].append(f"v{int(version)} - {name}")

    if not pending and current_version < target_version:
        # fallback for edge cases where migration list was altered
        _schema_meta_set_version(cur, target_version)
        report["schema_version_after"] = target_version

    # Self-heal for partially applied versions (for example, schema_meta bumped but some columns missing).
    if int(target_version) >= 4:
        try:
            _migration_v4_reminder_audit(conn, cur)
        except Exception as e:
            report["issues"].append(f"Self-heal migrare v4 esuat: {e}")
    if int(target_version) >= 5:
        try:
            _migration_v5_diagnostic_liber(conn, cur)
        except Exception as e:
            report["issues"].append(f"Self-heal migrare v5 esuat: {e}")
    if int(target_version) >= 6:
        try:
            _migration_v6_entity_audit(conn, cur)
        except Exception as e:
            report["issues"].append(f"Self-heal migrare v6 esuat: {e}")
    if int(target_version) >= 7:
        try:
            _migration_v7_sms_optout_sync_outbox(conn, cur)
        except Exception as e:
            report["issues"].append(f"Self-heal migrare v7 esuat: {e}")

    return report


def _collect_schema_diagnostics(cur: sqlite3.Cursor, schema_version: Optional[int] = None) -> List[str]:
    """Colecteaza inconsistente de schema pentru afisare la startup."""
    required_map: Dict[str, List[str]] = {
        "app_settings": ["key", "value"],
        "users": ["id", "username", "password_hash", "full_name", "role", "active"],
        "activity_log": ["id", "ts", "action", "details", "user", "role"],
        "pacienti_master": ["id", "nume_prenume", "cnp", "varsta", "telefon", "email", "sms_opt_out"],
        "consulturi": ["id", "pacient_id", "data_consultului", "diagnostic_principal", "diagnostic_secundar", "diagnostic_liber"],
        "appointments": ["id", "pacient_id", "date", "time", "status", "reminder_sms"],
        "reminder_dispatch_log": [
            "id",
            "appointment_id",
            "trigger_at",
            "attempted_at",
            "status",
            "phone",
            "message",
            "response",
            "error",
            "attempts",
            "dispatch_rule",
            "source_user",
            "source_role",
            "source_action",
        ],
        "appointment_reminder_state": [
            "appointment_id",
            "status",
            "attempts",
            "last_attempt_at",
            "sent_at",
            "next_retry_at",
            "last_error",
            "last_message",
            "updated_at",
        ],
        "appointment_sms_template_state": [
            "appointment_id",
            "confirm_sent_at",
            "cancel_sent_at",
            "last_template_key",
            "last_status",
            "last_error",
            "updated_at",
        ],
        ENTITY_AUDIT_TABLE: [
            "id",
            "ts",
            "table_name",
            "row_id",
            "action",
            "before_json",
            "after_json",
            "source_user",
            "source_role",
            "source_action",
        ],
        SYNC_OUTBOX_TABLE: [
            "id",
            "created_at",
            "table_name",
            "payload_json",
            "attempts",
            "next_retry_at",
            "last_error",
            "updated_at",
        ],
        DB_SCHEMA_META_TABLE: ["key", "value", "updated_at"],
    }

    issues: List[str] = []
    for table_name, required_cols in required_map.items():
        if not _db_table_exists_cur(cur, table_name):
            issues.append(f"Lipseste tabelul critic: {table_name}")
            continue
        cols = _db_table_columns_cur(cur, table_name)
        missing = [c for c in required_cols if c not in cols]
        if missing:
            issues.append(f"{table_name}: coloane lipsa -> {', '.join(missing)}")

    ver = int(schema_version if schema_version is not None else _schema_meta_get_version(cur))
    if ver < int(DB_SCHEMA_VERSION_CURRENT):
        issues.append(f"Schema incompleta: versiune DB v{ver}, necesar v{int(DB_SCHEMA_VERSION_CURRENT)}.")
    elif ver > int(DB_SCHEMA_VERSION_CURRENT):
        issues.append(f"Schema DB v{ver} este mai noua decat build-ul curent v{int(DB_SCHEMA_VERSION_CURRENT)}.")

    return issues


def _format_schema_diagnostic_text(report: Dict[str, Any]) -> str:
    """Formateaza schema diagnostic text."""
    before = int(report.get("schema_version_before") or 0)
    after = int(report.get("schema_version_after") or 0)
    target = int(report.get("schema_version_target") or int(DB_SCHEMA_VERSION_CURRENT))
    lines = [
        "Diagnostic schema baza de date",
        "",
        f"Versiune schema: v{before} -> v{after} (target v{target})",
    ]

    backup_path = (report.get("migration_backup_path") or "").strip()
    if backup_path:
        lines.append(f"Backup pre-migrare: {backup_path}")

    applied = report.get("applied_migrations") or []
    if applied:
        lines.append("")
        lines.append("Migrari aplicate:")
        for item in applied:
            lines.append(f"- {item}")

    issues = report.get("issues") or []
    if issues:
        lines.append("")
        lines.append("Probleme detectate:")
        for item in issues:
            lines.append(f"- {item}")
    else:
        lines.append("")
        lines.append("Nu au fost detectate inconsistente de schema.")

    return "\n".join(lines)


def init_db():
    """Initializeaza baza locala, ruleaza migrari si asigura toate tabelele necesare aplicatiei."""
    conn = get_conn()
    cur = conn.cursor()

    # Master pacient
    cur.execute("""
        CREATE TABLE IF NOT EXISTS pacienti_master (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            nume_prenume TEXT NOT NULL,
            domiciliu TEXT,
            cnp TEXT,
            data_nasterii TEXT,
            sex TEXT,
            varsta INTEGER,
            telefon TEXT,
            email TEXT,
            sms_opt_out INTEGER DEFAULT 0
        )
    """)
    _ensure_table_column(cur, "pacienti_master", "sms_opt_out", "INTEGER DEFAULT 0")

    # Consulturi
    cur.execute("""
        CREATE TABLE IF NOT EXISTS consulturi (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            pacient_id INTEGER NOT NULL,
            data_consultului TEXT,
            medic TEXT,
            diagnostic_principal TEXT,
            diagnostic_secundar TEXT,
            diagnostic_liber TEXT,
            observatii TEXT,
            status_follow_up TEXT,
            data_revenire_control TEXT,
            interval_luni_revenire INTEGER,
            recomandare_fizio_kineto TEXT,
            a_inceput_fizio TEXT,
            created_at TEXT,
            FOREIGN KEY(pacient_id) REFERENCES pacienti_master(id) ON DELETE CASCADE
        )
    """)
    _ensure_table_column(cur, "consulturi", "diagnostic_liber", "TEXT")

    # Perechi marcate ca NU duplicate
    cur.execute("""
        CREATE TABLE IF NOT EXISTS not_duplicates (
            a INTEGER NOT NULL,
            b INTEGER NOT NULL,
            created_at TEXT,
            PRIMARY KEY (a, b)
        )
    """)

    # Self-heal sync metadata columns required by CRUD paths even before init_sync_schema().
    for table_name in ("pacienti_master", "consulturi", "not_duplicates"):
        _ensure_table_column(cur, table_name, "sync_id", "TEXT")
        _ensure_table_column(cur, table_name, "updated_at", "TEXT")
        _ensure_table_column(cur, table_name, "deleted", "INTEGER")
        _ensure_table_column(cur, table_name, "device_id", "TEXT")

    # Log activitate
    cur.execute("""
        CREATE TABLE IF NOT EXISTS activity_log (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            ts TEXT,
            action TEXT,
            details TEXT,
            user TEXT,
            role TEXT
        )
    """)

    # Setari aplicatie
    cur.execute("""
        CREATE TABLE IF NOT EXISTS app_settings (
            key TEXT PRIMARY KEY,
            value TEXT
        )
    """)
    _ensure_sync_outbox_table(conn)

    # Utilizatori
    cur.execute("""
        CREATE TABLE IF NOT EXISTS users (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            username TEXT UNIQUE,
            password_hash TEXT,
            full_name TEXT,
            role TEXT,
            active INTEGER
        )
    """)

    # Traseu pacient
    cur.execute("""
        CREATE TABLE IF NOT EXISTS patient_flow (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            pacient_id INTEGER NOT NULL,
            status TEXT,
            checkin_time TEXT,
            triage_time TEXT,
            consult_start TEXT,
            consult_end TEXT,
            discharge_time TEXT,
            notes TEXT,
            created_at TEXT,
            FOREIGN KEY(pacient_id) REFERENCES pacienti_master(id) ON DELETE CASCADE
        )
    """)

    # Istoric medical structurat
    cur.execute("""
        CREATE TABLE IF NOT EXISTS medical_history (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            pacient_id INTEGER NOT NULL,
            category TEXT,
            item TEXT,
            start_date TEXT,
            end_date TEXT,
            notes TEXT,
            FOREIGN KEY(pacient_id) REFERENCES pacienti_master(id) ON DELETE CASCADE
        )
    """)

    # Planuri tratament
    cur.execute("""
        CREATE TABLE IF NOT EXISTS treatment_plans (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            pacient_id INTEGER NOT NULL,
            name TEXT,
            protocol TEXT,
            start_date TEXT,
            end_date TEXT,
            status TEXT,
            notes TEXT,
            FOREIGN KEY(pacient_id) REFERENCES pacienti_master(id) ON DELETE CASCADE
        )
    """)

    # Retete
    cur.execute("""
        CREATE TABLE IF NOT EXISTS prescriptions (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            pacient_id INTEGER NOT NULL,
            date TEXT,
            doctor TEXT,
            template_name TEXT,
            content TEXT,
            file_path TEXT,
            signed_by TEXT,
            signature_path TEXT,
            signed_at TEXT,
            FOREIGN KEY(pacient_id) REFERENCES pacienti_master(id) ON DELETE CASCADE
        )
    """)

    # Scrisori medicale
    cur.execute("""
        CREATE TABLE IF NOT EXISTS medical_letters (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            pacient_id INTEGER NOT NULL,
            date TEXT,
            doctor TEXT,
            letter_type TEXT,
            template_name TEXT,
            content TEXT,
            file_path TEXT,
            signed_by TEXT,
            signature_path TEXT,
            signed_at TEXT,
            FOREIGN KEY(pacient_id) REFERENCES pacienti_master(id) ON DELETE CASCADE
        )
    """)

    # Documente atasate
    cur.execute("""
        CREATE TABLE IF NOT EXISTS documents (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            pacient_id INTEGER NOT NULL,
            category TEXT,
            title TEXT,
            file_path TEXT,
            date TEXT,
            notes TEXT,
            FOREIGN KEY(pacient_id) REFERENCES pacienti_master(id) ON DELETE CASCADE
        )
    """)

    # Programari
    cur.execute("""
        CREATE TABLE IF NOT EXISTS appointments (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            pacient_id INTEGER,
            date TEXT,
            time TEXT,
            duration_min INTEGER,
            medic TEXT,
            status TEXT,
            reminder_email TEXT,
            reminder_sms TEXT,
            checkin_code TEXT,
            location_id INTEGER,
            notes TEXT
        )
    """)

    # Lista asteptare
    cur.execute("""
        CREATE TABLE IF NOT EXISTS waiting_list (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            pacient_id INTEGER,
            priority INTEGER,
            reason TEXT,
            status TEXT,
            created_at TEXT,
            location_id INTEGER,
            notes TEXT
        )
    """)

    # Taskuri interne
    cur.execute("""
        CREATE TABLE IF NOT EXISTS tasks (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            title TEXT,
            assigned_to TEXT,
            due_date TEXT,
            status TEXT,
            notes TEXT,
            created_at TEXT
        )
    """)

    # Decontari / Asigurari
    cur.execute("""
        CREATE TABLE IF NOT EXISTS insurance_claims (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            pacient_id INTEGER,
            insurer TEXT,
            policy_no TEXT,
            amount REAL,
            status TEXT,
            invoice_id INTEGER,
            notes TEXT,
            created_at TEXT
        )
    """)

    # Sedii
    cur.execute("""
        CREATE TABLE IF NOT EXISTS locations (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            name TEXT,
            address TEXT,
            active INTEGER
        )
    """)

    # Loturi stoc
    cur.execute("""
        CREATE TABLE IF NOT EXISTS inventory_lots (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            item_id INTEGER NOT NULL,
            lot TEXT,
            expiry_date TEXT,
            qty REAL,
            notes TEXT,
            FOREIGN KEY(item_id) REFERENCES inventory_items(id) ON DELETE CASCADE
        )
    """)

    # Alerte clinice
    cur.execute("""
        CREATE TABLE IF NOT EXISTS clinical_alerts (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            pacient_id INTEGER NOT NULL,
            alert_type TEXT,
            message TEXT,
            active INTEGER,
            due_date TEXT,
            created_at TEXT,
            FOREIGN KEY(pacient_id) REFERENCES pacienti_master(id) ON DELETE CASCADE
        )
    """)

    # ICD-10 codes
    cur.execute("""
        CREATE TABLE IF NOT EXISTS icd10_codes (
            code TEXT PRIMARY KEY,
            title TEXT,
            search TEXT
        )
    """)

    # Localitati RO (judet + localitate)
    cur.execute(f"""
        CREATE TABLE IF NOT EXISTS {RO_LOCALITIES_TABLE} (
            county TEXT NOT NULL,
            locality TEXT NOT NULL,
            search TEXT NOT NULL,
            PRIMARY KEY (county, locality)
        )
    """)
    cur.execute(f"CREATE INDEX IF NOT EXISTS idx_{RO_LOCALITIES_TABLE}_county ON {RO_LOCALITIES_TABLE}(county)")
    cur.execute(f"CREATE INDEX IF NOT EXISTS idx_{RO_LOCALITIES_TABLE}_search ON {RO_LOCALITIES_TABLE}(search)")

    # Vaccinari
    cur.execute("""
        CREATE TABLE IF NOT EXISTS vaccinations (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            pacient_id INTEGER NOT NULL,
            vaccine TEXT,
            dose TEXT,
            date TEXT,
            due_date TEXT,
            status TEXT,
            notes TEXT,
            FOREIGN KEY(pacient_id) REFERENCES pacienti_master(id) ON DELETE CASCADE
        )
    """)

    # Laborator (cereri + rezultate)
    cur.execute("""
        CREATE TABLE IF NOT EXISTS lab_orders (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            pacient_id INTEGER NOT NULL,
            date TEXT,
            test_name TEXT,
            status TEXT,
            lab TEXT,
            result_text TEXT,
            result_file TEXT,
            notes TEXT,
            FOREIGN KEY(pacient_id) REFERENCES pacienti_master(id) ON DELETE CASCADE
        )
    """)

    # Facturare
    cur.execute("""
        CREATE TABLE IF NOT EXISTS invoices (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            pacient_id INTEGER NOT NULL,
            date TEXT,
            total REAL,
            method TEXT,
            status TEXT,
            notes TEXT,
            FOREIGN KEY(pacient_id) REFERENCES pacienti_master(id) ON DELETE CASCADE
        )
    """)

    # Stocuri
    cur.execute("""
        CREATE TABLE IF NOT EXISTS inventory_items (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            name TEXT,
            unit TEXT,
            qty REAL,
            min_qty REAL,
            location TEXT,
            vendor TEXT,
            notes TEXT
        )
    """)
    cur.execute("""
        CREATE TABLE IF NOT EXISTS inventory_movements (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            item_id INTEGER NOT NULL,
            ts TEXT,
            qty REAL,
            move_type TEXT,
            reason TEXT,
            pacient_id INTEGER,
            FOREIGN KEY(item_id) REFERENCES inventory_items(id) ON DELETE CASCADE
        )
    """)

    # Indexuri
    cur.execute("CREATE INDEX IF NOT EXISTS idx_master_nume ON pacienti_master(nume_prenume)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_master_cnp ON pacienti_master(cnp)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_master_tel ON pacienti_master(telefon)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_master_email ON pacienti_master(email)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_master_sms_opt_out ON pacienti_master(sms_opt_out)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_master_name_phone ON pacienti_master(nume_prenume, telefon)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_cons_pacient ON consulturi(pacient_id)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_cons_data ON consulturi(data_consultului)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_cons_control ON consulturi(data_revenire_control)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_cons_latest ON consulturi(pacient_id, data_consultului, id)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_cons_diag_liber ON consulturi(diagnostic_liber)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_cons_diag_principal ON consulturi(diagnostic_principal)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_cons_diag_secundar ON consulturi(diagnostic_secundar)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_cons_status_date ON consulturi(status_follow_up, data_consultului)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_flow_pacient ON patient_flow(pacient_id)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_hist_pacient ON medical_history(pacient_id)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_treat_pacient ON treatment_plans(pacient_id)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_presc_pacient ON prescriptions(pacient_id)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_letter_pacient ON medical_letters(pacient_id)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_docs_pacient ON documents(pacient_id)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_alert_pacient ON clinical_alerts(pacient_id)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_vacc_pacient ON vaccinations(pacient_id)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_lab_pacient ON lab_orders(pacient_id)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_inv_pacient ON invoices(pacient_id)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_app_pacient ON appointments(pacient_id)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_app_date ON appointments(date)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_app_status ON appointments(status)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_app_medic ON appointments(medic)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_app_date_status ON appointments(date, status)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_app_date_medic ON appointments(date, medic)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_app_sms_phone ON appointments(reminder_sms)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_app_email ON appointments(reminder_email)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_cons_status ON consulturi(status_follow_up)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_cons_medic_date ON consulturi(medic, data_consultului)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_log_user_ts ON activity_log(user, ts)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_wait_pacient ON waiting_list(pacient_id)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_claim_pacient ON insurance_claims(pacient_id)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_sync_outbox_next_retry ON sync_outbox(next_retry_at)")

    # Cleanup legacy nomenclator removed from app
    try:
        cur.execute("DROP TABLE IF EXISTS nom_tip_internare")
    except Exception:
        pass
    try:
        cur.execute("DROP TABLE IF EXISTS nom_tip_externare")
    except Exception:
        pass
    try:
        cur.execute("DROP TABLE IF EXISTS nom_stare_externare")
    except Exception:
        pass
    try:
        cur.execute("DROP TABLE IF EXISTS nom_situatie_speciala")
    except Exception:
        pass
    try:
        cur.execute("DROP TABLE IF EXISTS nom_tip_asigurare_cnas")
    except Exception:
        pass
    try:
        cur.execute("DROP TABLE IF EXISTS nom_tip_finantare_sectie")
    except Exception:
        pass
    try:
        cur.execute("DROP TABLE IF EXISTS nom_ocupatie")
    except Exception:
        pass
    try:
        cur.execute("DROP TABLE IF EXISTS nom_specialitate")
    except Exception:
        pass
    try:
        cur.execute("DROP TABLE IF EXISTS nom_statut_asigurare")
    except Exception:
        pass
    try:
        cur.execute("DROP TABLE IF EXISTS nom_categorie_asigurat")
    except Exception:
        pass
    try:
        cur.execute("DROP TABLE IF EXISTS nom_nivel_instruire")
    except Exception:
        pass
    try:
        cur.execute("DROP TABLE IF EXISTS nom_accident")
    except Exception:
        pass
    try:
        cur.execute("DROP TABLE IF EXISTS nom_criteriu_internare")
    except Exception:
        pass
    try:
        cur.execute("DROP TABLE IF EXISTS nom_tip_serviciu")
    except Exception:
        pass
    try:
        cur.execute("DROP TABLE IF EXISTS nom_cas")
    except Exception:
        pass

    migration_report: Dict[str, Any] = {
        "schema_version_before": 0,
        "schema_version_after": 0,
        "schema_version_target": int(DB_SCHEMA_VERSION_CURRENT),
        "applied_migrations": [],
        "migration_backup_path": "",
        "issues": [],
    }
    try:
        migration_report = _run_db_schema_migrations(conn, cur)

        # Defensive keep: schema runtime helpers remain idempotent.
        ensure_recycle_bin_tables(conn)
        _ensure_reminder_runtime_tables(conn)
        _ensure_appointment_sms_template_state_table(conn)
        _ensure_entity_audit_table(conn)
        seed_nomenclatoare_defaults(cur)

        issues = list(migration_report.get("issues") or [])
        issues.extend(_collect_schema_diagnostics(cur, migration_report.get("schema_version_after")))
        migration_report["issues"] = sorted(set([str(it) for it in issues if str(it).strip()]))

        conn.commit()
    except Exception as e:
        try:
            conn.rollback()
        except Exception:
            pass
        issue_list = [f"Eroare la migrarea schemei: {e}"]
        try:
            issue_list.extend(_collect_schema_diagnostics(cur))
        except Exception:
            pass
        migration_report["issues"] = sorted(set([str(it) for it in issue_list if str(it).strip()]))
    finally:
        conn.close()

    if table_exists("users"):
        try:
            ensure_default_admin_user()
        except Exception:
            pass

    return migration_report


def export_db_copy_atomic(dest_path: str):
    """Exporta baza de date copy atomic."""
    dest = Path(dest_path)
    tmp = dest.with_suffix(dest.suffix + ".tmp")
    dest.parent.mkdir(parents=True, exist_ok=True)

    src_conn = sqlite3.connect(str(DB_PATH), timeout=10)
    try:
        dst_conn = sqlite3.connect(str(tmp), timeout=10)
        try:
            # Use SQLite backup API for a consistent snapshot under WAL/concurrency.
            src_conn.backup(dst_conn)
        finally:
            dst_conn.close()
    finally:
        src_conn.close()
    tmp.replace(dest)


# ============================================================
# DB Helpers
# ============================================================
def get_master(pid: int) -> Optional[sqlite3.Row]:
    """Returneaza randul pacientului din `pacienti_master` dupa ID."""
    conn = get_conn()
    cur = conn.cursor()
    cur.execute("SELECT * FROM pacienti_master WHERE id=? AND COALESCE(deleted,0)=0", (pid,))
    r = cur.fetchone()
    conn.close()
    return r


def find_master_by_cnp(cnp: str) -> Optional[sqlite3.Row]:
    """Cauta master by CNP."""
    c = normalize_cnp_digits(cnp)
    if not c:
        return None
    conn = get_conn()
    cur = conn.cursor()
    cur.execute(
        """
        SELECT *
        FROM pacienti_master
        WHERE COALESCE(deleted,0)=0
          AND REPLACE(REPLACE(REPLACE(REPLACE(TRIM(COALESCE(cnp,'')), ' ', ''), '-', ''), '.', ''), '/', '')=?
        LIMIT 1
        """,
        (c,),
    )
    r = cur.fetchone()
    conn.close()
    return r


def find_master_by_exact_name(name: str) -> List[sqlite3.Row]:
    """Cauta master by exact name."""
    n = (name or "").strip()
    if not n:
        return []
    conn = get_conn()
    cur = conn.cursor()
    cur.execute(
        "SELECT * FROM pacienti_master WHERE TRIM(nume_prenume) = ? COLLATE NOCASE AND COALESCE(deleted,0)=0",
        (n,),
    )
    rows = cur.fetchall()
    conn.close()
    return rows


def find_patients_by_name(name: str, limit: int = 20) -> List[Tuple[int, str]]:
    """Cauta patients by name."""
    name = (name or "").strip()
    if not name:
        return []
    name_low = name.lower()
    name_norm = strip_ro_diacritics(name_low) or name_low
    like1 = f"%{name_low}%"
    like2 = f"%{name_norm}%"
    conn = get_conn()
    cur = conn.cursor()
    cur.execute("""
        SELECT id, nume_prenume
        FROM pacienti_master
        WHERE COALESCE(deleted,0)=0
          AND (LOWER(nume_prenume)=? OR LOWER(nume_prenume) LIKE ?)
        ORDER BY nume_prenume COLLATE NOCASE ASC
        LIMIT ?
    """, (name_low, like1, limit))
    rows = cur.fetchall()
    if not rows and name_norm != name_low:
        cur.execute("""
            SELECT id, nume_prenume
            FROM pacienti_master
            WHERE COALESCE(deleted,0)=0
              AND LOWER(nume_prenume) LIKE ?
            ORDER BY nume_prenume COLLATE NOCASE ASC
            LIMIT ?
        """, (like2, limit))
        rows = cur.fetchall()
    conn.close()
    return [(int(r[0]), r[1] or "") for r in rows]


def resolve_pacient_id_input(val: Any, parent: Optional[QWidget] = None) -> Optional[int]:
    """Rezolva pacient ID input."""
    if val is None:
        return None
    s = str(val).strip()
    if not s:
        return None
    if s.isdigit():
        return int(s)
    rows = find_patients_by_name(s, limit=50)
    if not rows:
        QMessageBox.warning(parent, "Pacient negasit", "Nu exista pacient cu acest nume.")
        return None
    if len(rows) == 1:
        return int(rows[0][0])
    options = [f"{rid} - {nm}" for rid, nm in rows]
    choice, ok = QInputDialog.getItem(
        parent,
        "Selecteaza pacient",
        "Mai multi pacienti gasiti. Alege pacientul:",
        options,
        0,
        False,
    )
    if not ok or not choice:
        return None
    try:
        pid_str = choice.split(" - ", 1)[0].strip()
        if pid_str.isdigit():
            return int(pid_str)
    except Exception:
        return None
    return None


def _normalize_pair_ids(a: int, b: int) -> Tuple[int, int]:
    """Normalizeaza pair ID-uri."""
    a = int(a)
    b = int(b)
    if a == b:
        return a, b
    return (a, b) if a < b else (b, a)


def mark_not_duplicate(a: int, b: int):
    """Marcheaza not duplicate."""
    if a is None or b is None:
        return
    if a == b:
        return
    aa, bb = _normalize_pair_ids(a, b)
    conn = get_conn()
    cur = conn.cursor()
    cur.execute(
        "INSERT OR IGNORE INTO not_duplicates(a, b, created_at, sync_id, updated_at, deleted, device_id) VALUES (?,?,?,?,?,?,?)",
        (
            aa,
            bb,
            datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
            uuid.uuid4().hex,
            now_ts(),
            0,
            get_device_id(),
        ),
    )
    conn.commit()
    conn.close()


def is_marked_not_duplicate(a: int, b: int) -> bool:
    """Verifica daca marked not duplicate."""
    if a is None or b is None:
        return False
    if a == b:
        return True
    aa, bb = _normalize_pair_ids(a, b)
    conn = get_conn()
    cur = conn.cursor()
    cur.execute("SELECT 1 FROM not_duplicates WHERE a=? AND b=? LIMIT 1", (aa, bb))
    row = cur.fetchone()
    conn.close()
    return bool(row)


def insert_master(payload: dict) -> int:
    """Insereaza un pacient nou in pacienti_master dupa normalizarea payload-ului."""
    payload = normalize_payload_ascii(normalize_master_from_cnp(payload))

    conn = get_conn()
    cur = conn.cursor()
    cur.execute("""
        INSERT INTO pacienti_master(
            nume_prenume, domiciliu, cnp, data_nasterii, sex, varsta, telefon, email, sms_opt_out,
            sync_id, updated_at, deleted, device_id
        ) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?)
    """, (
        payload.get("nume_prenume"),
        payload.get("domiciliu"),
        payload.get("cnp"),
        payload.get("data_nasterii"),
        payload.get("sex"),
        payload.get("varsta"),
        payload.get("telefon"),
        payload.get("email"),
        _to_int_flag(payload.get("sms_opt_out")),
        uuid.uuid4().hex,
        now_ts(),
        0,
        get_device_id(),
    ))
    _ensure_entity_audit_table(conn)
    pid = int(cur.lastrowid)
    after_row = _fetch_row_dict_cur(cur, "pacienti_master", pid)
    _insert_entity_audit_cur(
        cur,
        "pacienti_master",
        pid,
        "insert",
        None,
        after_row,
        source_action="insert_master",
    )
    conn.commit()
    conn.close()
    return pid


def update_master(pid: int, payload: dict):
    """Actualizeaza datele pacientului si mentine campurile derivate consistente."""
    payload = normalize_payload_ascii(normalize_master_from_cnp(payload))

    conn = get_conn()
    cur = conn.cursor()
    _ensure_entity_audit_table(conn)
    before_row = _fetch_row_dict_cur(cur, "pacienti_master", int(pid))
    cur.execute("""
        UPDATE pacienti_master SET
            nume_prenume=?,
            domiciliu=?,
            cnp=?,
            data_nasterii=?,
            sex=?,
            varsta=?,
            telefon=?,
            email=?,
            sms_opt_out=?,
            updated_at=?,
            device_id=?,
            deleted=0
        WHERE id=?
    """, (
        payload.get("nume_prenume"),
        payload.get("domiciliu"),
        payload.get("cnp"),
        payload.get("data_nasterii"),
        payload.get("sex"),
        payload.get("varsta"),
        payload.get("telefon"),
        payload.get("email"),
        _to_int_flag(payload.get("sms_opt_out")),
        now_ts(),
        get_device_id(),
        pid
    ))
    after_row = _fetch_row_dict_cur(cur, "pacienti_master", int(pid))
    _insert_entity_audit_cur(
        cur,
        "pacienti_master",
        int(pid),
        "update",
        before_row,
        after_row,
        source_action="update_master",
    )
    conn.commit()
    conn.close()


def delete_master(pid: int):
    """Sterge logic pacientul si inregistreaza snapshot pentru recover/recycle bin."""
    conn = get_conn()
    cur = conn.cursor()
    _ensure_entity_audit_table(conn)
    before_master = _fetch_row_dict_cur(cur, "pacienti_master", int(pid))
    before_consults: Dict[int, Dict[str, Any]] = {}
    try:
        cur.execute("SELECT * FROM consulturi WHERE pacient_id=?", (int(pid),))
        for rr in cur.fetchall():
            try:
                before_consults[int(rr["id"])] = dict(rr)
            except Exception:
                continue
    except Exception:
        before_consults = {}
    if table_has_column("pacienti_master", "deleted"):
        cur.execute(
            "UPDATE pacienti_master SET deleted=1, updated_at=?, device_id=? WHERE id=?",
            (now_ts(), get_device_id(), pid),
        )
        if table_has_column("consulturi", "deleted"):
            cur.execute(
                "UPDATE consulturi SET deleted=1, updated_at=?, device_id=? WHERE pacient_id=?",
                (now_ts(), get_device_id(), pid),
            )
    else:
        cur.execute("DELETE FROM pacienti_master WHERE id=?", (pid,))

    after_master = _fetch_row_dict_cur(cur, "pacienti_master", int(pid))
    _insert_entity_audit_cur(
        cur,
        "pacienti_master",
        int(pid),
        "soft_delete" if table_has_column("pacienti_master", "deleted") else "delete",
        before_master,
        after_master,
        source_action="delete_master",
    )
    for cid, c_before in before_consults.items():
        c_after = _fetch_row_dict_cur(cur, "consulturi", int(cid))
        _insert_entity_audit_cur(
            cur,
            "consulturi",
            int(cid),
            "soft_delete" if table_has_column("consulturi", "deleted") else "delete",
            c_before,
            c_after,
            source_action="delete_master",
        )
    conn.commit()
    conn.close()


def insert_consult(pacient_id: int, payload: dict) -> int:
    """Insereaza consult nou pentru pacient si sincronizeaza metadatele asociate."""
    payload = normalize_payload_ascii(payload)
    conn = get_conn()
    cur = conn.cursor()
    cur.execute("""
        INSERT INTO consulturi(
            pacient_id, data_consultului, medic, diagnostic_principal, diagnostic_secundar, diagnostic_liber, observatii,
            status_follow_up,
            data_revenire_control, interval_luni_revenire,
            recomandare_fizio_kineto, a_inceput_fizio, created_at,
            sync_id, updated_at, deleted, device_id
        ) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)
    """, (
        pacient_id,
        payload.get("data_consultului"),
        payload.get("medic"),
        payload.get("diagnostic_principal"),
        payload.get("diagnostic_secundar"),
        payload.get("diagnostic_liber"),
        payload.get("observatii"),
        payload.get("status_follow_up"),
        payload.get("data_revenire_control"),
        payload.get("interval_luni_revenire"),
        payload.get("recomandare_fizio_kineto"),
        payload.get("a_inceput_fizio"),
        datetime.now().isoformat(timespec="seconds"),
        uuid.uuid4().hex,
        now_ts(),
        0,
        get_device_id(),
    ))
    _ensure_entity_audit_table(conn)
    cid = int(cur.lastrowid)
    after_row = _fetch_row_dict_cur(cur, "consulturi", cid)
    _insert_entity_audit_cur(
        cur,
        "consulturi",
        cid,
        "insert",
        None,
        after_row,
        source_action="insert_consult",
    )
    conn.commit()
    conn.close()
    return cid


def _insert_master_and_consult_cur(
    cur: sqlite3.Cursor,
    master_payload: dict,
    consult_payload: dict,
    source_action: str = "insert_master_and_consult",
) -> int:
    """Insereaza pacient + consult folosind cursorul existent (fara commit local)."""
    master_payload = normalize_payload_ascii(normalize_master_from_cnp(master_payload))
    consult_payload = normalize_payload_ascii(consult_payload)

    cur.execute("""
        INSERT INTO pacienti_master(
            nume_prenume, domiciliu, cnp, data_nasterii, sex, varsta, telefon, email, sms_opt_out,
            sync_id, updated_at, deleted, device_id
        ) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?)
    """, (
        master_payload.get("nume_prenume"),
        master_payload.get("domiciliu"),
        master_payload.get("cnp"),
        master_payload.get("data_nasterii"),
        master_payload.get("sex"),
        master_payload.get("varsta"),
        master_payload.get("telefon"),
        master_payload.get("email"),
        _to_int_flag(master_payload.get("sms_opt_out")),
        uuid.uuid4().hex,
        now_ts(),
        0,
        get_device_id(),
    ))
    pid = int(cur.lastrowid)
    after_master = _fetch_row_dict_cur(cur, "pacienti_master", pid)
    _insert_entity_audit_cur(
        cur,
        "pacienti_master",
        pid,
        "insert",
        None,
        after_master,
        source_action=source_action,
    )

    cur.execute("""
        INSERT INTO consulturi(
            pacient_id, data_consultului, medic, diagnostic_principal, diagnostic_secundar, diagnostic_liber, observatii,
            status_follow_up,
            data_revenire_control, interval_luni_revenire,
            recomandare_fizio_kineto, a_inceput_fizio, created_at,
            sync_id, updated_at, deleted, device_id
        ) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)
    """, (
        pid,
        consult_payload.get("data_consultului"),
        consult_payload.get("medic"),
        consult_payload.get("diagnostic_principal"),
        consult_payload.get("diagnostic_secundar"),
        consult_payload.get("diagnostic_liber"),
        consult_payload.get("observatii"),
        consult_payload.get("status_follow_up"),
        consult_payload.get("data_revenire_control"),
        consult_payload.get("interval_luni_revenire"),
        consult_payload.get("recomandare_fizio_kineto"),
        consult_payload.get("a_inceput_fizio"),
        datetime.now().isoformat(timespec="seconds"),
        uuid.uuid4().hex,
        now_ts(),
        0,
        get_device_id(),
    ))
    cid = int(cur.lastrowid)
    after_consult = _fetch_row_dict_cur(cur, "consulturi", cid)
    _insert_entity_audit_cur(
        cur,
        "consulturi",
        cid,
        "insert",
        None,
        after_consult,
        source_action=source_action,
    )
    return pid


def insert_master_and_consult(master_payload: dict, consult_payload: dict) -> int:
    """Creeaza pacient nou impreuna cu consult initial intr-o singura tranzactie."""
    conn = get_conn()
    try:
        cur = conn.cursor()
        _ensure_entity_audit_table(conn)
        pid = _insert_master_and_consult_cur(
            cur,
            master_payload,
            consult_payload,
            source_action="insert_master_and_consult",
        )
        conn.commit()
        return pid
    except Exception:
        conn.rollback()
        raise
    finally:
        conn.close()


def _update_master_and_insert_consult_cur(
    cur: sqlite3.Cursor,
    pid: int,
    master_payload: dict,
    consult_payload: dict,
    source_action: str = "update_master_and_insert_consult",
):
    """Actualizeaza pacient + adauga consult folosind cursorul existent (fara commit local)."""
    master_payload = normalize_payload_ascii(normalize_master_from_cnp(master_payload))
    consult_payload = normalize_payload_ascii(consult_payload)

    before_master = _fetch_row_dict_cur(cur, "pacienti_master", int(pid))
    cur.execute("""
        UPDATE pacienti_master SET
            nume_prenume=?,
            domiciliu=?,
            cnp=?,
            data_nasterii=?,
            sex=?,
            varsta=?,
            telefon=?,
            email=?,
            sms_opt_out=?,
            updated_at=?,
            device_id=?,
            deleted=0
        WHERE id=?
    """, (
        master_payload.get("nume_prenume"),
        master_payload.get("domiciliu"),
        master_payload.get("cnp"),
        master_payload.get("data_nasterii"),
        master_payload.get("sex"),
        master_payload.get("varsta"),
        master_payload.get("telefon"),
        master_payload.get("email"),
        _to_int_flag(master_payload.get("sms_opt_out")),
        now_ts(),
        get_device_id(),
        pid
    ))
    after_master = _fetch_row_dict_cur(cur, "pacienti_master", int(pid))
    _insert_entity_audit_cur(
        cur,
        "pacienti_master",
        int(pid),
        "update",
        before_master,
        after_master,
        source_action=source_action,
    )

    cur.execute("""
        INSERT INTO consulturi(
            pacient_id, data_consultului, medic, diagnostic_principal, diagnostic_secundar, diagnostic_liber, observatii,
            status_follow_up,
            data_revenire_control, interval_luni_revenire,
            recomandare_fizio_kineto, a_inceput_fizio, created_at,
            sync_id, updated_at, deleted, device_id
        ) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)
    """, (
        pid,
        consult_payload.get("data_consultului"),
        consult_payload.get("medic"),
        consult_payload.get("diagnostic_principal"),
        consult_payload.get("diagnostic_secundar"),
        consult_payload.get("diagnostic_liber"),
        consult_payload.get("observatii"),
        consult_payload.get("status_follow_up"),
        consult_payload.get("data_revenire_control"),
        consult_payload.get("interval_luni_revenire"),
        consult_payload.get("recomandare_fizio_kineto"),
        consult_payload.get("a_inceput_fizio"),
        datetime.now().isoformat(timespec="seconds"),
        uuid.uuid4().hex,
        now_ts(),
        0,
        get_device_id(),
    ))
    cid = int(cur.lastrowid)
    after_consult = _fetch_row_dict_cur(cur, "consulturi", cid)
    _insert_entity_audit_cur(
        cur,
        "consulturi",
        cid,
        "insert",
        None,
        after_consult,
        source_action=source_action,
    )


def update_master_and_insert_consult(pid: int, master_payload: dict, consult_payload: dict):
    """Actualizeaza pacient existent si adauga consult nou in aceeasi tranzactie."""
    conn = get_conn()
    try:
        cur = conn.cursor()
        _ensure_entity_audit_table(conn)
        _update_master_and_insert_consult_cur(
            cur,
            int(pid),
            master_payload,
            consult_payload,
            source_action="update_master_and_insert_consult",
        )
        conn.commit()
    except Exception:
        conn.rollback()
        raise
    finally:
        conn.close()


def update_consult(consult_id: int, payload: dict):
    """Actualizeaza datele unui consult existent cu validare si audit."""
    payload = normalize_payload_ascii(payload)
    conn = get_conn()
    cur = conn.cursor()
    _ensure_entity_audit_table(conn)
    before_row = _fetch_row_dict_cur(cur, "consulturi", int(consult_id))
    cur.execute("""
        UPDATE consulturi SET
            data_consultului=?,
            medic=?,
            diagnostic_principal=?,
            diagnostic_secundar=?,
            diagnostic_liber=?,
            observatii=?,
            status_follow_up=?,
            data_revenire_control=?,
            interval_luni_revenire=?,
            recomandare_fizio_kineto=?,
            a_inceput_fizio=?,
            updated_at=?,
            device_id=?,
            deleted=0
        WHERE id=?
    """, (
        payload.get("data_consultului"),
        payload.get("medic"),
        payload.get("diagnostic_principal"),
        payload.get("diagnostic_secundar"),
        payload.get("diagnostic_liber"),
        payload.get("observatii"),
        payload.get("status_follow_up"),
        payload.get("data_revenire_control"),
        payload.get("interval_luni_revenire"),
        payload.get("recomandare_fizio_kineto"),
        payload.get("a_inceput_fizio"),
        now_ts(),
        get_device_id(),
        consult_id
    ))
    after_row = _fetch_row_dict_cur(cur, "consulturi", int(consult_id))
    _insert_entity_audit_cur(
        cur,
        "consulturi",
        int(consult_id),
        "update",
        before_row,
        after_row,
        source_action="update_consult",
    )
    conn.commit()
    conn.close()


def delete_consult(consult_id: int):
    """Sterge logic un consult si actualizeaza starea derivata a pacientului."""
    conn = get_conn()
    cur = conn.cursor()
    _ensure_entity_audit_table(conn)
    before_row = _fetch_row_dict_cur(cur, "consulturi", int(consult_id))
    if table_has_column("consulturi", "deleted"):
        cur.execute(
            "UPDATE consulturi SET deleted=1, updated_at=?, device_id=? WHERE id=?",
            (now_ts(), get_device_id(), consult_id),
        )
    else:
        cur.execute("DELETE FROM consulturi WHERE id=?", (consult_id,))
    after_row = _fetch_row_dict_cur(cur, "consulturi", int(consult_id))
    _insert_entity_audit_cur(
        cur,
        "consulturi",
        int(consult_id),
        "soft_delete" if table_has_column("consulturi", "deleted") else "delete",
        before_row,
        after_row,
        source_action="delete_consult",
    )
    conn.commit()
    conn.close()


def get_consults(pacient_id: int) -> List[sqlite3.Row]:
    """Returneaza lista consulturilor pentru pacientul selectat."""
    conn = get_conn()
    cur = conn.cursor()
    cur.execute("""
        SELECT * FROM consulturi
        WHERE pacient_id=? AND COALESCE(deleted,0)=0
        ORDER BY COALESCE(data_consultului,'') DESC, id DESC
    """, (pacient_id,))
    rows = cur.fetchall()
    conn.close()
    return rows


def get_consult_by_id(consult_id: int) -> Optional[sqlite3.Row]:
    """Returneaza consult by ID."""
    conn = get_conn()
    cur = conn.cursor()
    cur.execute("SELECT * FROM consulturi WHERE id=? AND COALESCE(deleted,0)=0", (consult_id,))
    r = cur.fetchone()
    conn.close()
    return r


def get_latest_consult(pacient_id: int) -> Optional[sqlite3.Row]:
    """Returneaza latest consult."""
    conn = get_conn()
    cur = conn.cursor()
    cur.execute("""
        SELECT * FROM consulturi
        WHERE pacient_id=? AND COALESCE(deleted,0)=0
        ORDER BY COALESCE(data_consultului,'') DESC, id DESC
        LIMIT 1
    """, (pacient_id,))
    r = cur.fetchone()
    conn.close()
    return r

def _master_list_with_latest_base_sql(search_q: str, use_window: bool) -> Tuple[str, Tuple[Any, ...]]:
    """Gestioneaza list with latest base SQL."""
    q = (search_q or "").strip()
    args: List[Any] = []
    if use_window:
        sql = """
            WITH latest AS (
                SELECT
                    c.*,
                    ROW_NUMBER() OVER (PARTITION BY pacient_id
                        ORDER BY COALESCE(data_consultului,'') DESC, id DESC) AS rn
                FROM consulturi c
                WHERE COALESCE(c.deleted,0)=0
            )
            SELECT
              m.id,
              m.nume_prenume,
              m.cnp,
              m.sex,
              m.telefon,
              m.email,
              m.data_nasterii,
              m.varsta,
              m.domiciliu,
              l.data_consultului AS ultimul_consult,
              COALESCE(NULLIF(l.diagnostic_liber,''), l.diagnostic_principal) AS ultim_diagnostic,
              l.diagnostic_secundar AS diagnostic_secundar,
              l.diagnostic_liber AS diagnostic_liber,
              l.data_revenire_control AS data_revenire_control,
              l.status_follow_up AS status_follow_up
            FROM pacienti_master m
            LEFT JOIN latest l ON l.pacient_id=m.id AND l.rn=1
            WHERE COALESCE(m.deleted,0)=0
        """
    else:
        sql = """
            SELECT
              m.id,
              m.nume_prenume,
              m.cnp,
              m.sex,
              m.telefon,
              m.email,
              m.data_nasterii,
              m.varsta,
              m.domiciliu,
              l.data_consultului AS ultimul_consult,
              COALESCE(NULLIF(l.diagnostic_liber,''), l.diagnostic_principal) AS ultim_diagnostic,
              l.diagnostic_secundar AS diagnostic_secundar,
              l.diagnostic_liber AS diagnostic_liber,
              l.data_revenire_control AS data_revenire_control,
              l.status_follow_up AS status_follow_up
            FROM pacienti_master m
            LEFT JOIN consulturi l ON l.id = (
                SELECT c.id
                FROM consulturi c
                WHERE c.pacient_id=m.id AND COALESCE(c.deleted,0)=0
                ORDER BY COALESCE(c.data_consultului,'') DESC, c.id DESC
                LIMIT 1
            )
            WHERE COALESCE(m.deleted,0)=0
        """
    if q:
        like = f"%{q}%"
        sql += """
          AND (m.nume_prenume LIKE ?
               OR m.cnp LIKE ?
               OR m.telefon LIKE ?
               OR COALESCE(l.diagnostic_principal,'') LIKE ?
               OR COALESCE(l.diagnostic_secundar,'') LIKE ?
               OR COALESCE(l.diagnostic_liber,'') LIKE ?)
        """
        args.extend([like, like, like, like, like, like])
    return sql, tuple(args)


def master_list_with_latest_consult_page(
    search_q: str = "",
    limit: Optional[int] = 250,
    offset: int = 0,
    include_total: bool = True,
) -> Tuple[List[sqlite3.Row], int]:
    """Intoarce pagina curenta de pacienti cu ultimul consult pentru tabelul principal."""
    conn = get_conn()
    cur = conn.cursor()
    mode = (MAIN_LIST_QUERY_MODE or "").strip().lower()
    use_window = bool(mode == "window" and tuple(int(x) for x in sqlite3.sqlite_version.split(".")) >= (3, 25, 0))
    base_sql, base_args = _master_list_with_latest_base_sql(search_q, use_window=use_window)

    total = 0
    if include_total:
        if not (search_q or "").strip():
            cur.execute("SELECT COUNT(1) FROM pacienti_master WHERE COALESCE(deleted,0)=0")
            rr = cur.fetchone()
            try:
                total = int(rr[0]) if rr is not None else 0
            except Exception:
                total = 0
        else:
            cur.execute(f"SELECT COUNT(1) FROM ({base_sql}) src", base_args)
            rr = cur.fetchone()
            try:
                total = int(rr[0]) if rr is not None else 0
            except Exception:
                total = 0

    data_sql = base_sql + " ORDER BY nume_prenume COLLATE NOCASE ASC"
    data_args: List[Any] = list(base_args)
    if limit is not None:
        try:
            lim = max(1, int(limit))
        except Exception:
            lim = 250
        try:
            off = max(0, int(offset))
        except Exception:
            off = 0
        data_sql += " LIMIT ? OFFSET ?"
        data_args.extend([lim, off])

    cur.execute(data_sql, tuple(data_args))
    rows = cur.fetchall()
    conn.close()

    if not include_total:
        total = len(rows)
    return rows, max(0, int(total))


def master_list_with_latest_consult(search_q: str = "") -> List[sqlite3.Row]:
    """Intoarce lista pacientilor cu datele ultimului consult pentru cautare simpla."""
    rows, _ = master_list_with_latest_consult_page(
        search_q=search_q,
        limit=None,
        offset=0,
        include_total=False,
    )
    return rows


def avg_age_by_category(category_key: str) -> List[Tuple[str, float, int]]:
    """Gestioneaza age by category."""
    rows = master_list_with_latest_consult("")
    sums: Dict[str, float] = {}
    counts: Dict[str, int] = {}

    for r in rows:
        rd = dict(r)
        age = rd.get("varsta")
        if age in ("", None):
            age = calc_age_ani(rd.get("data_nasterii"))
        try:
            age_val = float(age)
        except Exception:
            continue
        if age_val < 0 or age_val > 130:
            continue

        key = rd.get(category_key)
        key = (key or "").strip() or "Necunoscut"

        sums[key] = sums.get(key, 0.0) + age_val
        counts[key] = counts.get(key, 0) + 1

    out = []
    for k in sorted(sums.keys()):
        cnt = counts.get(k, 0)
        if cnt > 0:
            out.append((k, sums[k] / cnt, cnt))
    return out

def get_upcoming_controls(
    days_ahead: int = 7,
    status_follow_up: str = "",
) -> List[Dict[str, Any]]:
    """Returneaza upcoming controls."""
    today = date.today()
    end = today + timedelta(days=days_ahead)
    conn = get_conn()
    cur = conn.cursor()

    sql = """
        SELECT
            m.id,
            m.nume_prenume,
            m.telefon,
            COALESCE(NULLIF(c.diagnostic_liber,''), c.diagnostic_principal) AS diagnostic_principal,
            c.diagnostic_liber,
            c.data_revenire_control,
            c.status_follow_up
    """
    sql += """
        FROM pacienti_master m
        JOIN consulturi c ON c.pacient_id=m.id
        WHERE c.data_revenire_control IS NOT NULL
          AND TRIM(c.data_revenire_control) <> ''
          AND COALESCE(m.deleted,0)=0
          AND COALESCE(c.deleted,0)=0
    """

    args: List[Any] = []
    status_filter = (status_follow_up or "").strip()
    if ALERT_ONLY_PROGRAMAT and not status_filter:
        status_filter = "Programat"
    if status_filter:
        sql += " AND COALESCE(c.status_follow_up,'') = ?"
        args.append(status_filter)

    cur.execute(sql, tuple(args))

    rows = cur.fetchall()
    conn.close()

    out = []
    for r in rows:
        d = _safe_parse_ymd(r["data_revenire_control"])
        if d is None:
            continue
        if today <= d <= end:
            out.append({
                "id": r["id"],
                "nume_prenume": r["nume_prenume"] or "",
                "telefon": r["telefon"] or "",
                "diagnostic_principal": r["diagnostic_principal"] or "",
                "diagnostic_liber": r["diagnostic_liber"] or "",
                "data_revenire_control": r["data_revenire_control"] or "",
                "status_follow_up": r["status_follow_up"] or "",
            })

    out.sort(key=lambda x: (x["data_revenire_control"], x["nume_prenume"].lower()))
    return out


def filter_master_rows_advanced(criteria: dict) -> List[Dict[str, Any]]:
    """Aplica filtrarea avansata pe pacienti folosind criteriile definite in UI."""
    rows = master_list_with_latest_consult("")
    out: List[Dict[str, Any]] = []
    name = (criteria.get("name") or "").lower()
    cnp = (criteria.get("cnp") or "").lower()
    tel = (criteria.get("telefon") or "").lower()
    email = (criteria.get("email") or "").lower()
    sex = (criteria.get("sex") or "").lower()
    diag = (criteria.get("diag") or "").lower()
    diag2 = (criteria.get("diag2") or "").lower()
    diag_liber = (criteria.get("diag_liber") or "").lower()
    age_min = criteria.get("age_min")
    age_max = criteria.get("age_max")
    last_from = (criteria.get("last_from") or "").strip()
    last_to = (criteria.get("last_to") or "").strip()

    for r in rows:
        rd = dict(r)
        if name and name not in (rd.get("nume_prenume") or "").lower():
            continue
        if cnp and cnp not in (rd.get("cnp") or "").lower():
            continue
        if tel and tel not in (rd.get("telefon") or "").lower():
            continue
        if email and email not in (rd.get("email") or "").lower():
            continue
        if sex and sex != (rd.get("sex") or "").lower():
            continue
        diag_blob = " ".join(
            [
                str(rd.get("ultim_diagnostic") or ""),
                str(rd.get("diagnostic_liber") or ""),
            ]
        ).lower()
        if diag and diag not in diag_blob:
            continue
        if diag2 and diag2 not in (rd.get("diagnostic_secundar") or "").lower():
            continue
        if diag_liber and diag_liber not in (rd.get("diagnostic_liber") or "").lower():
            continue

        v_cache = rd.get("varsta")
        v_calc = None
        if v_cache in ("", None):
            v_calc = calc_age_ani(rd.get("data_nasterii"))
        else:
            try:
                v_calc = int(v_cache)
            except Exception:
                v_calc = calc_age_ani(rd.get("data_nasterii"))

        if age_min is not None and (v_calc is None or v_calc < age_min):
            continue
        if age_max is not None and (v_calc is None or v_calc > age_max):
            continue

        if last_from or last_to:
            dval = (rd.get("ultimul_consult") or "").strip()
            if not dval:
                continue
            if last_from and dval < last_from:
                continue
            if last_to and dval > last_to:
                continue

        out.append(rd)
    return out


def auto_create_appointments_from_controls() -> int:
    """Genereaza programari automate din controale scadente."""
    conn = get_conn()
    cur = conn.cursor()
    added = 0

    has_deleted_appt = table_has_column("appointments", "deleted")
    if has_deleted_appt:
        cur.execute("""
            SELECT pacient_id, date
            FROM appointments
            WHERE COALESCE(deleted,0)=0
              AND date IS NOT NULL
              AND TRIM(date) <> ''
        """)
    else:
        cur.execute("""
            SELECT pacient_id, date
            FROM appointments
            WHERE date IS NOT NULL
              AND TRIM(date) <> ''
        """)
    existing = {(int(r[0]), str(r[1]).strip()) for r in cur.fetchall() if r[0] is not None and r[1]}

    has_deleted_cons = table_has_column("consulturi", "deleted")
    has_deleted_master = table_has_column("pacienti_master", "deleted")
    has_medic = table_has_column("consulturi", "medic")
    cons_where = []
    if has_deleted_cons:
        cons_where.append("COALESCE(c.deleted,0)=0")
    cons_where.append("c.data_revenire_control IS NOT NULL")
    cons_where.append("TRIM(c.data_revenire_control) <> ''")
    if ALERT_ONLY_PROGRAMAT:
        cons_where.append("c.status_follow_up='Programat'")
    cons_where_sql = " AND ".join(cons_where) if cons_where else "1=1"
    master_where = "COALESCE(m.deleted,0)=0" if has_deleted_master else "1=1"

    use_window = tuple(int(x) for x in sqlite3.sqlite_version.split(".")) >= (3, 25, 0)
    if use_window:
        medic_select = "l.medic" if has_medic else "NULL AS medic"
        cur.execute(f"""
            WITH latest AS (
                SELECT
                    c.*,
                    ROW_NUMBER() OVER (PARTITION BY pacient_id
                        ORDER BY COALESCE(data_consultului,'') DESC, id DESC) AS rn
                FROM consulturi c
                WHERE {cons_where_sql}
            )
            SELECT
                l.pacient_id,
                l.data_revenire_control,
                {medic_select},
                m.telefon,
                m.email
            FROM latest l
            JOIN pacienti_master m ON m.id=l.pacient_id
            WHERE l.rn=1 AND {master_where}
        """)
        rows = cur.fetchall()
    else:
        medic_sub = f"""
                    SELECT c.medic
                    FROM consulturi c
                    WHERE c.pacient_id=m.id AND {cons_where_sql}
                    ORDER BY COALESCE(c.data_consultului,'') DESC, c.id DESC
                    LIMIT 1
                """ if has_medic else "SELECT NULL"
        cur.execute(f"""
            SELECT
                m.id AS pacient_id,
                m.telefon,
                m.email,
                (
                    SELECT c.data_revenire_control
                    FROM consulturi c
                    WHERE c.pacient_id=m.id AND {cons_where_sql}
                    ORDER BY COALESCE(c.data_consultului,'') DESC, c.id DESC
                    LIMIT 1
                ) AS data_revenire_control,
                ({medic_sub}) AS medic
            FROM pacienti_master m
            WHERE {master_where}
        """)
        rows = cur.fetchall()

    today = date.today()
    for r in rows:
        try:
            pid = int(r["pacient_id"])
        except Exception:
            continue
        dctrl = (r["data_revenire_control"] or "").strip()
        if not dctrl:
            continue
        d = _safe_parse_ymd(dctrl)
        if d is None or d < today:
            continue
        key = (pid, dctrl)
        if key in existing:
            continue

        phone = normalize_ro_mobile_phone(r["telefon"]) if "telefon" in r.keys() else None
        email = (r["email"] if "email" in r.keys() else None) or None
        cols = ["pacient_id", "date", "medic", "status", "reminder_email", "reminder_sms", "checkin_code", "location_id", "notes"]
        vals = [
            pid,
            dctrl,
            r["medic"] if "medic" in r.keys() else "",
            "Programat",
            email,
            phone,
            _gen_code(),
            get_current_location_id(),
            "Auto din control",
        ]
        if table_has_column("appointments", "sync_id"):
            cols.append("sync_id")
            vals.append(uuid.uuid4().hex)
        if table_has_column("appointments", "updated_at"):
            cols.append("updated_at")
            vals.append(now_ts())
        if table_has_column("appointments", "deleted"):
            cols.append("deleted")
            vals.append(0)
        if table_has_column("appointments", "device_id"):
            cols.append("device_id")
            vals.append(get_device_id())

        cur.execute(
            f"INSERT INTO appointments ({', '.join(cols)}) VALUES ({', '.join(['?']*len(cols))})",
            vals,
        )
        added += 1
        existing.add(key)

    conn.commit()
    conn.close()
    return added


# ============================================================
# Duplicate scan helpers
# ============================================================
def find_duplicate_cnp_groups() -> List[List[Dict[str, Any]]]:
    """Cauta duplicate CNP groups."""
    conn = get_conn()
    cur = conn.cursor()
    cur.execute("""
        SELECT cnp, COUNT(*) as cnt
        FROM pacienti_master
        WHERE cnp IS NOT NULL AND TRIM(cnp)<>'' 
          AND COALESCE(deleted,0)=0
        GROUP BY cnp
        HAVING cnt >= 2
    """)
    cnps = [row[0] for row in cur.fetchall()]

    groups = []
    for cnp in cnps:
        cur.execute("""
            SELECT id, nume_prenume, cnp, telefon, data_nasterii, sex
            FROM pacienti_master
            WHERE cnp=? AND COALESCE(deleted,0)=0
            ORDER BY id DESC
        """, (cnp,))
        rows = cur.fetchall()
        groups.append([dict(r) for r in rows])

    conn.close()
    return groups


def find_exact_name_groups() -> List[List[Dict[str, Any]]]:
    """Cauta exact name groups."""
    conn = get_conn()
    cur = conn.cursor()
    cur.execute("""
        SELECT LOWER(TRIM(nume_prenume)) as nm, COUNT(*) as cnt
        FROM pacienti_master
        WHERE nume_prenume IS NOT NULL AND TRIM(nume_prenume)<>'' 
          AND COALESCE(deleted,0)=0
        GROUP BY nm
        HAVING cnt >= 2
    """)
    names = [row[0] for row in cur.fetchall()]

    groups = []
    for nm in names:
        cur.execute("""
            SELECT id, nume_prenume, cnp, telefon, data_nasterii, sex
            FROM pacienti_master
            WHERE LOWER(TRIM(nume_prenume))=? AND COALESCE(deleted,0)=0
            ORDER BY id DESC
        """, (nm,))
        rows = cur.fetchall()
        groups.append([dict(r) for r in rows])

    conn.close()
    return groups


def _ratio(a: str, b: str) -> float:
    # Similaritate simplÄ fÄrÄ libs externe:
    # - normalizeazÄ
    # - calculeazÄ overlap token + prefix
    """Calculeaza scorul de similaritate intre doua siruri de caractere."""
    na = _norm_name(a)
    nb = _norm_name(b)
    if not na or not nb:
        return 0.0
    if na == nb:
        return 1.0
    ta = na.split()
    tb = nb.split()
    set_a = set(ta)
    set_b = set(tb)
    j = len(set_a & set_b) / max(1, len(set_a | set_b))
    # bonus dacÄ prefix comun mare
    pref = 0
    for i in range(min(len(na), len(nb))):
        if na[i] == nb[i]:
            pref += 1
        else:
            break
    pscore = pref / max(len(na), len(nb))
    return 0.75 * j + 0.25 * pscore


def find_similar_name_pairs(threshold: float = 0.93, limit: int = 180) -> List[Tuple[Dict[str, Any], Dict[str, Any], float]]:
    """Cauta similar name pairs."""
    conn = get_conn()
    cur = conn.cursor()
    cur.execute("""
        SELECT id, nume_prenume, cnp, telefon, data_nasterii, sex
        FROM pacienti_master
        WHERE TRIM(nume_prenume) <> ''
          AND COALESCE(deleted,0)=0
        ORDER BY id DESC
        LIMIT ?
    """, (limit,))
    rows = [dict(r) for r in cur.fetchall()]
    conn.close()

    pairs = []
    # blocking: bucket dupÄ prima literÄ Č™i lungime aprox
    buckets: Dict[str, List[Dict[str, Any]]] = {}
    for r in rows:
        nm = _norm_name(r.get("nume_prenume", ""))
        if not nm:
            continue
        key = (nm[:1] + "_" + str(len(nm) // 3)).strip("_")
        buckets.setdefault(key, []).append(r)

    for key, items in buckets.items():
        n = len(items)
        for i in range(n):
            for j in range(i + 1, n):
                a = items[i]
                b = items[j]
                pid_a = int(a["id"])
                pid_b = int(b["id"])
                if is_marked_not_duplicate(pid_a, pid_b):
                    continue
                s = _ratio(a.get("nume_prenume", ""), b.get("nume_prenume", ""))
                if s >= threshold:
                    pairs.append((a, b, float(s)))

    pairs.sort(key=lambda x: x[2], reverse=True)
    return pairs


# ============================================================
# Jobs: Recalc ages/sex for all
# ============================================================
def job_recalc_ages(progress_cb=None, cancelled_cb=None) -> Dict[str, int]:
    """Executa jobul pentru recalc ages."""
    def pg(p, m=""):
        """Actualizeaza progresul operatiei in curs (helper intern pentru `job_recalc_ages`)."""
        if progress_cb:
            progress_cb(int(p), str(m))

    def is_cancelled():
        """Verifica daca cancelled ca helper intern in `job_recalc_ages`."""
        return bool(cancelled_cb and cancelled_cb())

    conn = get_conn()
    cur = conn.cursor()
    has_updated_at = table_has_column("pacienti_master", "updated_at")
    has_device_id = table_has_column("pacienti_master", "device_id")
    has_deleted = table_has_column("pacienti_master", "deleted")
    sets = ["data_nasterii=?", "varsta=?", "sex=?"]
    if has_updated_at:
        sets.append("updated_at=?")
    if has_device_id:
        sets.append("device_id=?")
    if has_deleted:
        sets.append("deleted=0")
    sql_update = f"UPDATE pacienti_master SET {', '.join(sets)} WHERE id=?"
    cur.execute("SELECT COUNT(*) FROM pacienti_master WHERE COALESCE(deleted,0)=0")
    total = int(cur.fetchone()[0] or 0)

    cur.execute("SELECT id, cnp, data_nasterii, sex FROM pacienti_master WHERE COALESCE(deleted,0)=0")
    rows = cur.fetchall()

    updated = 0
    derived_dn = 0
    derived_sex = 0
    invalid = 0

    batch = []
    for idx, r in enumerate(rows):
        if idx % 50 == 0:
            if total > 0:
                pg(int(idx * 100 / total), f"Recalcâ€¦ {idx}/{total}")
            if is_cancelled():
                pg(100, "Anulat.")
                conn.close()
                return {"updated": updated, "derived_dn": derived_dn, "derived_sex": derived_sex, "invalid": invalid}

        pid = int(r["id"])
        cnp = (r["cnp"] or "").strip()
        dn_old = (r["data_nasterii"] or "").strip() or None
        sx_old = (r["sex"] or "").strip() or None

        dn_new = dn_old
        sx_new = sx_old

        if cnp_is_valid_13(cnp):
            cnp_ok = normalize_cnp_digits(cnp)
            sx2 = sex_from_cnp(cnp_ok)
            if sx2 and sx2 != sx_new:
                sx_new = sx2
                derived_sex += 1

            if not dn_new:
                dn2 = birthdate_from_cnp(cnp_ok)
                if dn2:
                    dn_new = dn2
                    derived_dn += 1

        age = calc_age_ani(dn_new)
        if dn_new is None and age is None:
            invalid += 1

        vals: List[Any] = [dn_new, age, sx_new]
        if has_updated_at:
            vals.append(now_ts())
        if has_device_id:
            vals.append(get_device_id())
        vals.append(pid)
        batch.append(tuple(vals))

        if len(batch) >= 200:
            conn.executemany(sql_update, batch)
            conn.commit()
            updated += len(batch)
            batch.clear()

    if batch:
        conn.executemany(sql_update, batch)
        conn.commit()
        updated += len(batch)

    conn.close()
    pg(100, "Gata.")
    return {"updated": updated, "derived_dn": derived_dn, "derived_sex": derived_sex, "invalid": invalid}

# ============================================================
# Tabular import (MASTER + CONSULT) strict template
# ============================================================
HEADER_TO_DB = {
    _norm("Nume si prenume"): "nume_prenume",
    _norm("Domiciliu"): "domiciliu",
    _norm("CNP"): "cnp",
    _norm("Data Nasterii"): "data_nasterii",
    _norm("Medic"): "medic",
    _norm("Diagnostic Principal"): "diagnostic_principal",
    _norm("Diagnostic liber"): "diagnostic_liber",
    _norm("Data Consultului"): "data_consultului",
    _norm("Ultimul consult"): "data_consultului",
    _norm("Observatii"): "observatii",
    _norm("Status Follow Up"): "status_follow_up",
    _norm("Data Revenirii la Control"): "data_revenire_control",
    _norm("Interval (luni) revenire"): "interval_luni_revenire",
    _norm("Recomandare Fizio-Kineto"): "recomandare_fizio_kineto",
    _norm("Recomandare Fizio-Kinetoterapie"): "recomandare_fizio_kineto",
    _norm("A inceput fizio?"): "a_inceput_fizio",
    _norm("A inceput fizioT"): "a_inceput_fizio",
    _norm("Status fizioterapie"): "a_inceput_fizio",
    _norm("Telefon"): "telefon",
}
OPTIONAL_TEMPLATE_HEADERS = {"diagnostic_liber"}
REQUIRED_HEADERS = {v for v in set(HEADER_TO_DB.values()) if v not in OPTIONAL_TEMPLATE_HEADERS}

AUTO_IMPORT_FIELD_ALIASES = {
    "nume_prenume": [
        "nume si prenume", "nume prenume", "pacient", "patient", "name", "nume", "nume pacient",
        "nume complet", "full name", "patient name"
    ],
    "domiciliu": [
        "domiciliu", "adresa", "address", "localitate", "oras", "city", "judet", "county", "resedinta"
    ],
    "cnp": [
        "cnp", "cod numeric personal", "personal numeric code", "idnp", "pid", "cod pacient"
    ],
    "data_nasterii": [
        "data nasterii", "nastere", "birth date", "dob", "date of birth", "dn", "data nastere"
    ],
    "telefon": [
        "telefon", "telefon mobil", "mobil", "phone", "phone number", "tel", "nr telefon", "numar telefon"
    ],
    "email": ["email", "e-mail", "mail", "adresa email", "email pacient"],
    "sex": ["sex", "gen", "gender", "m/f", "mf"],
    "varsta": ["varsta", "varsta ani", "age", "ani", "age years"],
    "data_consultului": [
        "data consultului", "consult", "consult date", "visit date", "data vizitei", "data prezentarii",
        "ultimul consult", "ultim consult", "ultima consultatie", "last consult", "last consultation",
        "data ultimului consult", "last visit date"
    ],
    "medic": ["medic", "doctor", "doctor name", "nume medic", "medic curant", "physician"],
    "diagnostic_principal": [
        "diagnostic principal", "diagnostic", "icd10", "icd-10", "primary diagnosis", "diag principal",
        "diagnostic initial"
    ],
    "diagnostic_secundar": [
        "diagnostic secundar", "secondary diagnosis", "diag secundar", "diagnostic secundar 1", "diag 2"
    ],
    "diagnostic_liber": [
        "diagnostic liber", "diag liber", "free diagnosis", "free text diagnosis", "diagnostic text"
    ],
    "observatii": [
        "observatii", "observatii consult", "note", "notes", "comentarii", "comments", "mentiuni", "remarks"
    ],
    "status_follow_up": [
        "status follow up", "status follow-up", "follow up", "follow-up", "status control", "status",
        "followup status"
    ],
    "data_revenire_control": [
        "data revenire control", "control", "data control", "next control", "next visit", "recontrol",
        "data urmatorului control", "data follow up"
    ],
    "interval_luni_revenire": [
        "interval luni revenire", "interval luni", "luni revenire", "months interval", "interval", "interval control"
    ],
    "recomandare_fizio_kineto": [
        "recomandare fizio kineto", "fizio kineto", "recomandare fizioterapie", "reco fizio", "kineto"
    ],
    "a_inceput_fizio": [
        "a inceput fizio", "inceput fizio", "started physio", "a inceput fizioterapia", "fizio inceput", "kineto inceput"
    ],
}
AUTO_IMPORT_REQUIRED_KEYS = {"nume_prenume"}


def _is_blank_tabular_cell(v: Any) -> bool:
    """Verifica daca blank tabular cell."""
    if v is None:
        return True
    try:
        if pd.isna(v):
            return True
    except Exception:
        pass
    s = str(v).strip()
    if not s:
        return True
    return s.lower() in {"nan", "none", "null"}
def _dedupe_header_names(names: List[str]) -> List[str]:
    """Gestioneaza header names."""
    out = []
    seen = {}
    for i, raw in enumerate(names):
        base = (str(raw or "").strip() or f"col_{i+1}")
        cnt = seen.get(base, 0) + 1
        seen[base] = cnt
        out.append(base if cnt == 1 else f"{base}_{cnt}")
    return out


def _prepare_tabular_df_for_import(df: "pd.DataFrame") -> "pd.DataFrame":
    """Gestioneaza tabular df for import."""
    if df is None:
        return df

    work = df.copy()
    if work.empty:
        return work

    known_terms = set(HEADER_TO_DB.keys())
    for aliases in AUTO_IMPORT_FIELD_ALIASES.values():
        for a in aliases:
            known_terms.add(_norm(a))

    col_names = [str(c).strip() for c in work.columns]
    placeholder_cols = 0
    for c in col_names:
        nc = _norm(c)
        if (not c) or c.lower().startswith("unnamed") or nc in {"", "nan", "none"}:
            placeholder_cols += 1

    need_header_promote = placeholder_cols >= max(1, int(len(col_names) * 0.6))

    if need_header_promote:
        best_idx = -1
        best_score = -1.0
        scan_limit = min(len(work), 20)

        for ridx in range(scan_limit):
            row = work.iloc[ridx]
            non_empty = 0
            score = 0.0
            for v in row.tolist():
                if _is_blank_tabular_cell(v):
                    continue
                non_empty += 1
                txt = str(v).strip()
                n = _norm(txt)
                if n in known_terms:
                    score += 3.0
                else:
                    best_alias_sc = 0.0
                    for kt in known_terms:
                        sc = _column_alias_score(n, kt)
                        if sc > best_alias_sc:
                            best_alias_sc = sc
                    if best_alias_sc >= 0.88:
                        score += 2.0
                    elif best_alias_sc >= 0.75:
                        score += 1.0
                    else:
                        score += 0.1

            if non_empty >= 4 and score > best_score:
                best_score = score
                best_idx = ridx

        if best_idx >= 0:
            header_vals = [str(v).strip() for v in work.iloc[best_idx].tolist()]
            new_cols = _dedupe_header_names(header_vals)
            work = work.iloc[best_idx + 1 :].copy()
            if len(new_cols) == len(work.columns):
                work.columns = new_cols

    # Drop fully empty rows
    keep_rows = []
    for _, row in work.iterrows():
        has_val = any(not _is_blank_tabular_cell(v) for v in row.tolist())
        keep_rows.append(bool(has_val))
    if keep_rows:
        work = work.loc[keep_rows].copy()

    # Drop columns that are empty by both name and values
    drop_cols = []
    for col in work.columns:
        c = str(col).strip()
        nc = _norm(c)
        name_empty = (not c) or c.lower().startswith("unnamed") or nc in {"", "nan", "none"}
        if not name_empty:
            continue
        series = work[col].tolist()
        if all(_is_blank_tabular_cell(v) for v in series):
            drop_cols.append(col)
    if drop_cols:
        work = work.drop(columns=drop_cols, errors="ignore")

    # Normalize final column names
    work.columns = [str(c).strip() for c in work.columns]
    work = work.reset_index(drop=True)
    return work


def _import_profile_signature(columns: List[str]) -> str:
    """Importa profile signature."""
    parts = [_norm(str(c or "")) for c in (columns or [])]
    payload = "|".join(parts)
    return hashlib.sha1(payload.encode("utf-8", errors="ignore")).hexdigest()


def _import_profile_key(columns: List[str]) -> str:
    """Importa profile key."""
    return f"import_mapping_profile::{_import_profile_signature(columns)}::{len(columns or [])}"


def _parse_import_profile_key(profile_key: str) -> Tuple[str, int]:
    """Parseaza import profile key."""
    try:
        parts = str(profile_key or "").split("::")
        if len(parts) != 3 or parts[0] != "import_mapping_profile":
            return "", 0
        sig = parts[1].strip()
        cnt = int(parts[2])
        return sig, cnt
    except Exception:
        return "", 0


def save_import_mapping_profile(columns: List[str], mapping: Dict[str, str]):
    """Salveaza import mapping profile."""
    try:
        key = _import_profile_key(columns)
        clean = {}
        cols_set = {str(c) for c in (columns or [])}
        for mk, mv in (mapping or {}).items():
            if not mk or not mv:
                continue
            if str(mv) in cols_set:
                clean[str(mk)] = str(mv)
        set_setting(key, json.dumps(clean, ensure_ascii=False))
    except Exception:
        pass


def load_import_mapping_profile(columns: List[str]) -> Dict[str, str]:
    """Incarca import mapping profile."""
    try:
        key = _import_profile_key(columns)
        raw = get_setting(key, "") or ""
        if not raw:
            return {}
        obj = json.loads(raw)
        if not isinstance(obj, dict):
            return {}
        cols_set = {str(c) for c in (columns or [])}
        out = {}
        for mk, mv in obj.items():
            if str(mv) in cols_set:
                out[str(mk)] = str(mv)
        return out
    except Exception:
        return {}


def _norm_tokens(s: str) -> List[str]:
    """Normalizeaza textul in tokeni pentru mapare si potrivire de coloane."""
    return [t for t in re.split(r"[^a-z0-9]+", _norm(s or "")) if t]


def _column_alias_score(col_name: str, alias: str) -> float:
    """Gestioneaza alias score."""
    cn = _norm(col_name or "")
    an = _norm(alias or "")
    if not cn or not an:
        return 0.0
    if cn == an:
        return 1.0

    ct = _norm_tokens(cn)
    at = _norm_tokens(an)
    if ct and at:
        set_c = set(ct)
        set_a = set(at)
        if set_c == set_a:
            return 0.97
        if set_a.issubset(set_c):
            return 0.94
        inter = len(set_c & set_a)
        if inter >= 2:
            return 0.88
        if inter == 1:
            return 0.80

    if an in cn or cn in an:
        return 0.90
    return _ratio(cn, an)


def auto_map_tabular_columns(columns: List[str]) -> Tuple[Dict[str, str], Dict[str, float]]:
    """Automatizeaza map tabular columns."""
    col_list = [str(c) for c in (columns or [])]
    mapping: Dict[str, str] = {}
    scores: Dict[str, float] = {}
    used_cols = set()

    field_order = [k for _, k in MASTER_FIELDS] + [k for _, k in CONSULT_FIELDS]
    proposals = []

    for key in field_order:
        aliases = [key]
        for label, lk in MASTER_FIELDS + CONSULT_FIELDS:
            if lk == key:
                aliases.append(label)
        aliases.extend(AUTO_IMPORT_FIELD_ALIASES.get(key, []))

        best_col = ""
        best_score = 0.0
        for col in col_list:
            local_best = 0.0
            for alias in aliases:
                sc = _column_alias_score(col, alias)
                if sc > local_best:
                    local_best = sc
            if local_best > best_score:
                best_score = local_best
                best_col = col

        if best_col:
            proposals.append((key, best_col, float(best_score)))

    proposals.sort(key=lambda x: x[2], reverse=True)

    for key, col, sc in proposals:
        if key in mapping or col in used_cols:
            continue
        min_score = 0.62 if key in AUTO_IMPORT_REQUIRED_KEYS else 0.75
        if sc < min_score:
            continue
        mapping[key] = col
        scores[key] = sc
        used_cols.add(col)

    return mapping, scores


IMPORT_DB_COMMIT_BATCH = 200


def import_from_excel_strict(path: str, progress_cb=None, cancelled_cb=None) -> Tuple[int, int]:
    """Importa from excel strict."""
    def pg(p, m=""):
        """Actualizeaza progresul operatiei in curs (helper intern pentru `import_from_excel_strict`)."""
        if progress_cb:
            progress_cb(int(p), str(m))

    def is_cancelled():
        """Verifica daca cancelled ca helper intern in `import_from_excel_strict`."""
        return bool(cancelled_cb and cancelled_cb())

    df = _prepare_tabular_df_for_import(_read_tabular_dataframe(path))

    mapped = {}
    for col in df.columns:
        n = _norm(col)
        if n in HEADER_TO_DB:
            mapped[HEADER_TO_DB[n]] = col

    missing = [h for h in REQUIRED_HEADERS if h not in mapped]
    extra = [str(col) for col in df.columns if _norm(col) not in HEADER_TO_DB]

    if missing or extra:
        msg = "Fisierul tabelar NU respecta strict template-ul (eticheta pe primul rand).\n\n"
        if missing:
            msg += "Lipsesc coloanele:\n- " + "\n- ".join(sorted(missing)) + "\n\n"
        if extra:
            msg += "Exista coloane in plus (nepermise):\n- " + "\n- ".join(sorted(extra)) + "\n\n"
        msg += "Sfat: foloseste exact aceleasi denumiri de coloane ca in fisierul model."
        raise ValueError(msg)

    inserted_consults = 0
    skipped = 0
    total = max(1, len(df))
    pending_commit_rows = 0

    col_idx = {str(col): i for i, col in enumerate(df.columns)}
    row_iter = df.itertuples(index=False, name=None)

    conn = get_conn()
    try:
        cur = conn.cursor()
        _ensure_entity_audit_table(conn)
        cache_by_id, cache_by_cnp, cache_by_name = _build_import_master_cache(cur)

        for idx, row_vals in enumerate(row_iter):
            if idx % 25 == 0:
                pg(int(idx * 100 / total), f"Import... {idx}/{total}")
                if is_cancelled():
                    if pending_commit_rows > 0:
                        conn.commit()
                    pg(100, "Import anulat.")
                    return inserted_consults, skipped

            master_payload = {k: None for _, k in MASTER_FIELDS}
            consult_payload = {k: None for _, k in CONSULT_FIELDS}

            for db_key, excel_col in mapped.items():
                pos = col_idx.get(str(excel_col))
                if pos is None or pos >= len(row_vals):
                    val = None
                else:
                    val = row_vals[pos]

                if db_key in DATE_KEYS:
                    v = _to_date_str_ymd(val)
                elif db_key in INT_KEYS:
                    v = _to_int_safe(val)
                else:
                    if db_key in ("cnp", "telefon") and not pd.isna(val):
                        try:
                            if isinstance(val, float):
                                v = str(int(val))
                            else:
                                v = str(val).strip()
                        except Exception:
                            v = _to_str_safe(val)
                    else:
                        v = _to_str_safe(val)

                if db_key in master_payload:
                    master_payload[db_key] = v
                else:
                    consult_payload[db_key] = v

            if _nonempty_payload_count(master_payload, consult_payload) <= 2:
                _rescue_from_full_row_values(row_vals, master_payload, consult_payload)

            _rescue_flat_row_payload(master_payload, consult_payload)

            if not master_payload.get("nume_prenume"):
                skipped += 1
                continue
            if _is_probable_import_header_row(master_payload, consult_payload):
                skipped += 1
                continue

            for dk in DATE_KEYS:
                if master_payload.get(dk) and not _validate_date_for_key(dk, master_payload[dk]):
                    master_payload[dk] = None
                if consult_payload.get(dk) and not _validate_date_for_key(dk, consult_payload[dk]):
                    consult_payload[dk] = None

            cnp_txt = (master_payload.get("cnp") or "").strip()
            if cnp_txt:
                digits = normalize_cnp_digits(cnp_txt)
                if not cnp_checksum_valid(digits):
                    master_payload["cnp"] = None
                else:
                    master_payload["cnp"] = digits

            existing = _resolve_existing_master_from_cache(
                master_payload,
                cache_by_id,
                cache_by_cnp,
                cache_by_name,
            )

            master_payload = normalize_master_from_cnp(master_payload)
            if existing is None:
                pid = _insert_master_and_consult_cur(
                    cur,
                    master_payload,
                    consult_payload,
                    source_action="import_from_excel_strict",
                )
                cache_row = _cache_master_payload_row(pid, master_payload)
            else:
                pid = int(existing["id"])
                merged = dict(existing)
                for _, k in MASTER_FIELDS:
                    nv = master_payload.get(k)
                    if nv and (not merged.get(k)):
                        merged[k] = nv
                merged = normalize_master_from_cnp(merged)
                _update_master_and_insert_consult_cur(
                    cur,
                    pid,
                    merged,
                    consult_payload,
                    source_action="import_from_excel_strict",
                )
                cache_row = _cache_master_payload_row(pid, merged)

            _update_import_master_cache(
                pid,
                cache_row,
                cache_by_id,
                cache_by_cnp,
                cache_by_name,
            )
            inserted_consults += 1
            pending_commit_rows += 1

            if pending_commit_rows >= IMPORT_DB_COMMIT_BATCH:
                conn.commit()
                pending_commit_rows = 0

        if pending_commit_rows > 0:
            conn.commit()
    except Exception:
        try:
            conn.rollback()
        except Exception:
            pass
        raise
    finally:
        conn.close()

    pg(100, "Gata importul.")
    return inserted_consults, skipped


def _excel_to_str(val):
    """Gestioneaza to str."""
    try:
        if pd.isna(val):
            return None
    except Exception:
        pass
    try:
        if isinstance(val, (datetime, date)):
            return val.strftime("%Y-%m-%d")
    except Exception:
        pass
    try:
        if hasattr(val, "to_pydatetime"):
            return val.to_pydatetime().strftime("%Y-%m-%d")
    except Exception:
        pass
    try:
        if isinstance(val, float):
            if val.is_integer():
                return str(int(val))
    except Exception:
        pass
    return str(val).strip()


def _split_flat_csv_record(text: str) -> List[str]:
    """Gestioneaza flat CSV record."""
    src = str(text or "").strip()
    if not src:
        return []
    candidates = [",", ";", "\t", "|"]
    best: List[str] = [src]
    best_score = 1
    for delim in candidates:
        parsed_variants: List[List[str]] = []
        try:
            parsed_variants.append(next(csv.reader([src], delimiter=delim, quotechar='"')))
        except Exception:
            pass
        try:
            parsed_variants.append(src.split(delim))
        except Exception:
            pass

        for parts in parsed_variants:
            parts = [str(p or "").strip() for p in parts]
            score = len(parts)
            if score > best_score:
                best = parts
                best_score = score
    return best


def _rescue_flat_row_payload(master_payload: Dict[str, Any], consult_payload: Dict[str, Any]) -> None:
    """Gestioneaza flat row payload."""
    try:
        filled = 0
        for k, v in (master_payload or {}).items():
            if k in {"sex", "varsta"}:
                continue
            if str(v or "").strip():
                filled += 1
        for _k, v in (consult_payload or {}).items():
            if str(v or "").strip():
                filled += 1

        source = str(master_payload.get("nume_prenume") or "").strip()
        if not source:
            return
        if not any(d in source for d in [",", ";", "\t", "|"]):
            return

        # Accept rescue not only for mostly-empty rows, but also when the current
        # name field clearly looks like a concatenated CSV payload.
        comma_cnt = source.count(",")
        semi_cnt = source.count(";")
        pipe_cnt = source.count("|")
        tab_cnt = source.count("\t")
        has_many_delims = (comma_cnt + semi_cnt + pipe_cnt + tab_cnt) >= 2
        has_digits_inside = bool(re.search(r"\d", source))
        looks_concatenated = has_many_delims and has_digits_inside

        if filled > 2 and not looks_concatenated:
            return

        parts = _split_flat_csv_record(source)
        if len(parts) < 2:
            return

        # If first token is empty, use first non-empty token as name.
        for token in parts:
            t = str(token or "").strip()
            if t:
                master_payload["nume_prenume"] = t
                break

        rest_tokens = [str(x or "").strip() for x in parts[1:] if str(x or "").strip()]
        date_candidates: List[str] = []
        text_candidates: List[str] = []
        yes_no_tokens: List[str] = []

        for tok in rest_tokens:
            tok_l = _norm(tok)
            digits = normalize_cnp_digits(tok)

            if not master_payload.get("cnp") and cnp_checksum_valid(digits):
                master_payload["cnp"] = digits
                continue

            if not master_payload.get("email") and "@" in tok and "." in tok:
                master_payload["email"] = tok
                continue

            if not master_payload.get("telefon"):
                tel = normalize_ro_mobile_phone(tok)
                tel_digits = re.sub(r"\D+", "", str(tel or ""))
                if tel and len(tel_digits) >= 9 and len(tel_digits) <= 12:
                    master_payload["telefon"] = tel
                    continue

            dt = _to_date_str_ymd(tok)
            if dt:
                date_candidates.append(dt)
                continue

            if tok_l in {"programat", "neprogramat"} and not consult_payload.get("status_follow_up"):
                consult_payload["status_follow_up"] = tok.capitalize()
                continue

            if tok_l in {"da", "nu", "yes", "no"}:
                yes_no_tokens.append(tok.upper())
                continue

            text_candidates.append(tok)

        if yes_no_tokens:
            if not consult_payload.get("recomandare_fizio_kineto"):
                consult_payload["recomandare_fizio_kineto"] = yes_no_tokens[0]
            if len(yes_no_tokens) > 1 and not consult_payload.get("a_inceput_fizio"):
                consult_payload["a_inceput_fizio"] = yes_no_tokens[1]

        if date_candidates:
            uniq_dates = sorted(set(date_candidates))
            birth_known = _to_date_str_ymd(master_payload.get("data_nasterii"))
            if not birth_known:
                birth_known = birthdate_from_cnp(master_payload.get("cnp"))
            if len(uniq_dates) == 1:
                only_d = uniq_dates[0]
                # Avoid using DOB (often derived from CNP) as "data consultului".
                if birth_known and only_d == birth_known:
                    if not master_payload.get("data_nasterii"):
                        master_payload["data_nasterii"] = only_d
                elif not consult_payload.get("data_consultului"):
                    consult_payload["data_consultului"] = only_d
            else:
                first_d = uniq_dates[0]
                last_d = uniq_dates[-1]
                if not master_payload.get("data_nasterii"):
                    # prefer plausible birth date if old enough
                    try:
                        y = int(first_d.split("-")[0])
                        cur_y = datetime.now().year
                        if y <= cur_y - 8:
                            master_payload["data_nasterii"] = first_d
                    except Exception:
                        pass
                if not consult_payload.get("data_consultului"):
                    consult_payload["data_consultului"] = last_d
                if len(uniq_dates) >= 3 and not consult_payload.get("data_revenire_control"):
                    consult_payload["data_revenire_control"] = uniq_dates[1]

        if text_candidates:
            if not master_payload.get("domiciliu"):
                master_payload["domiciliu"] = text_candidates[0]

            medic_idx = -1
            for i, txt in enumerate(text_candidates):
                if re.search(r"\d", txt):
                    continue
                words = [w for w in re.split(r"\s+", txt.strip()) if w]
                if len(words) >= 2 and len(words) <= 5:
                    medic_idx = i
                    break

            if medic_idx >= 0 and not consult_payload.get("medic"):
                consult_payload["medic"] = text_candidates[medic_idx]

            remaining = [
                txt for i, txt in enumerate(text_candidates)
                if i != 0 and i != medic_idx
            ]
            if remaining:
                best_diag = max(remaining, key=lambda s: len(str(s or "")))
                if not consult_payload.get("diagnostic_principal"):
                    consult_payload["diagnostic_principal"] = best_diag
                elif not consult_payload.get("diagnostic_liber"):
                    consult_payload["diagnostic_liber"] = best_diag
            if len(remaining) >= 2 and not consult_payload.get("observatii"):
                consult_payload["observatii"] = remaining[0]

        # Final safeguard: keep only first segment in name if still concatenated.
        final_name = str(master_payload.get("nume_prenume") or "").strip()
        if final_name and any(d in final_name for d in [",", ";", "\t", "|"]):
            p2 = _split_flat_csv_record(final_name)
            if p2:
                first_non_empty = next((str(x).strip() for x in p2 if str(x).strip()), "")
                if first_non_empty:
                    master_payload["nume_prenume"] = first_non_empty

        # Normalize recovered values
        for dk in DATE_KEYS:
            if dk in master_payload and master_payload.get(dk):
                master_payload[dk] = _to_date_str_ymd(master_payload.get(dk))
            if dk in consult_payload and consult_payload.get(dk):
                consult_payload[dk] = _to_date_str_ymd(consult_payload.get(dk))
        if consult_payload.get("interval_luni_revenire"):
            consult_payload["interval_luni_revenire"] = _to_int_safe(consult_payload.get("interval_luni_revenire"))
    except Exception:
        return


def _is_probable_import_header_row(master_payload: Dict[str, Any], consult_payload: Dict[str, Any]) -> bool:
    """Verifica daca probable import header row."""
    try:
        name_val = _norm(str(master_payload.get("nume_prenume") or ""))
        if not name_val:
            return False
        name_aliases = {
            _norm("nume"),
            _norm("nume prenume"),
            _norm("nume si prenume"),
            _norm("nume si prenume"),
            _norm("pacient"),
        }
        if name_val not in name_aliases:
            return False

        other_vals = [
            _norm(str(master_payload.get("cnp") or "")),
            _norm(str(master_payload.get("data_nasterii") or "")),
            _norm(str(master_payload.get("telefon") or "")),
            _norm(str(master_payload.get("email") or "")),
            _norm(str(consult_payload.get("medic") or "")),
            _norm(str(consult_payload.get("diagnostic_principal") or "")),
            _norm(str(consult_payload.get("diagnostic_liber") or "")),
            _norm(str(consult_payload.get("data_consultului") or "")),
        ]
        header_terms = {
            _norm("cnp"),
            _norm("data nasterii"),
            _norm("telefon"),
            _norm("email"),
            _norm("medic"),
            _norm("diagnostic"),
            _norm("diagnostic liber"),
            _norm("data consultului"),
        }
        return any(v in header_terms for v in other_vals if v)
    except Exception:
        return False


def _nonempty_payload_count(master_payload: Dict[str, Any], consult_payload: Dict[str, Any]) -> int:
    """Gestioneaza payload count."""
    n = 0
    for k, v in (master_payload or {}).items():
        if k in {"sex", "varsta"}:
            continue
        if str(v or "").strip():
            n += 1
    for _k, v in (consult_payload or {}).items():
        if str(v or "").strip():
            n += 1
    return n


def _rescue_from_full_row_values(row_obj: Any, master_payload: Dict[str, Any], consult_payload: Dict[str, Any]) -> None:
    """Gestioneaza from full row values."""
    try:
        if row_obj is None:
            return
        if hasattr(row_obj, "tolist"):
            vals = row_obj.tolist()
        elif isinstance(row_obj, (list, tuple)):
            vals = list(row_obj)
        elif isinstance(row_obj, dict):
            vals = list(row_obj.values())
        else:
            vals = []
        tokens: List[str] = []
        for v in vals:
            s = _excel_to_str(v)
            if s is None:
                continue
            s = str(s).strip()
            if s:
                tokens.append(s)
        if len(tokens) < 2:
            return

        master_payload["nume_prenume"] = ",".join(tokens)
        _rescue_flat_row_payload(master_payload, consult_payload)
    except Exception:
        return


def _import_name_key(name: Optional[str]) -> str:
    """Normalizeaza cheia de nume folosita de cache-ul de import."""
    return (str(name or "").strip().lower())


def _build_import_master_cache(cur: sqlite3.Cursor) -> Tuple[Dict[int, Dict[str, Any]], Dict[str, int], Dict[str, List[int]]]:
    """Construieste cache local de pacienti existenti pentru import rapid."""
    cur.execute("""
        SELECT id, nume_prenume, domiciliu, cnp, data_nasterii, sex, varsta, telefon, email, sms_opt_out
        FROM pacienti_master
        WHERE COALESCE(deleted,0)=0
        ORDER BY id ASC
    """)
    rows = cur.fetchall()
    by_id: Dict[int, Dict[str, Any]] = {}
    by_cnp: Dict[str, int] = {}
    by_name: Dict[str, List[int]] = {}

    for r in rows:
        d = dict(r)
        pid = int(d.get("id"))
        by_id[pid] = d

        cnp = str(d.get("cnp") or "").strip()
        if cnp and cnp not in by_cnp:
            by_cnp[cnp] = pid

        nk = _import_name_key(d.get("nume_prenume"))
        if nk:
            by_name.setdefault(nk, []).append(pid)

    return by_id, by_cnp, by_name


def _resolve_existing_master_from_cache(
    master_payload: Dict[str, Any],
    by_id: Dict[int, Dict[str, Any]],
    by_cnp: Dict[str, int],
    by_name: Dict[str, List[int]],
) -> Optional[Dict[str, Any]]:
    """Rezolva pacient existent din cache-ul de import (CNP prioritar, apoi nume unic)."""
    cnp = str(master_payload.get("cnp") or "").strip()
    if cnp:
        pid = by_cnp.get(cnp)
        if pid is not None:
            return by_id.get(int(pid))

    nk = _import_name_key(master_payload.get("nume_prenume"))
    if nk:
        ids = by_name.get(nk) or []
        if len(ids) == 1:
            return by_id.get(int(ids[0]))
    return None


def _cache_master_payload_row(pid: int, master_payload: Dict[str, Any]) -> Dict[str, Any]:
    """Construieste randul cache pentru pacient dupa insert/update in import."""
    row: Dict[str, Any] = {"id": int(pid)}
    for _, k in MASTER_FIELDS:
        row[k] = master_payload.get(k)
    row["sms_opt_out"] = _to_int_flag(row.get("sms_opt_out"))
    return row


def _update_import_master_cache(
    pid: int,
    new_row: Dict[str, Any],
    by_id: Dict[int, Dict[str, Any]],
    by_cnp: Dict[str, int],
    by_name: Dict[str, List[int]],
) -> None:
    """Actualizeaza indexurile cache-ului de import dupa insert/update pacient."""
    pid = int(pid)
    old_row = by_id.get(pid)
    if old_row:
        old_cnp = str(old_row.get("cnp") or "").strip()
        if old_cnp and by_cnp.get(old_cnp) == pid:
            by_cnp.pop(old_cnp, None)

        old_nk = _import_name_key(old_row.get("nume_prenume"))
        if old_nk and old_nk in by_name:
            by_name[old_nk] = [x for x in by_name[old_nk] if int(x) != pid]
            if not by_name[old_nk]:
                by_name.pop(old_nk, None)

    by_id[pid] = dict(new_row)

    new_cnp = str(new_row.get("cnp") or "").strip()
    if new_cnp:
        existing_pid = by_cnp.get(new_cnp)
        if existing_pid is None or int(existing_pid) == pid:
            by_cnp[new_cnp] = pid

    new_nk = _import_name_key(new_row.get("nume_prenume"))
    if new_nk:
        ids = by_name.setdefault(new_nk, [])
        if pid not in ids:
            ids.append(pid)


def import_from_excel_mapping(path: str, mapping: dict, progress_cb=None, cancelled_cb=None) -> Tuple[int, int]:
    """Importa from excel mapping."""
    def pg(p, m=""):
        """Actualizeaza progresul operatiei in curs (helper intern pentru `import_from_excel_mapping`)."""
        if progress_cb:
            progress_cb(int(p), str(m))

    def is_cancelled():
        """Verifica daca cancelled ca helper intern in `import_from_excel_mapping`."""
        return bool(cancelled_cb and cancelled_cb())

    try:
        df = _prepare_tabular_df_for_import(_read_tabular_dataframe(path))
    except Exception as e:
        raise RuntimeError(f"Eroare la citire fisier tabelar: {e}")

    total = len(df)
    inserted_consults = 0
    skipped = 0
    pending_commit_rows = 0

    col_idx = {str(col): i for i, col in enumerate(df.columns)}
    mapped_indexes: List[Tuple[str, int]] = []
    for key, col in (mapping or {}).items():
        if not col:
            continue
        pos = col_idx.get(str(col))
        if pos is None:
            continue
        mapped_indexes.append((str(key), int(pos)))

    row_iter = df.itertuples(index=False, name=None)

    conn = get_conn()
    try:
        cur = conn.cursor()
        _ensure_entity_audit_table(conn)
        cache_by_id, cache_by_cnp, cache_by_name = _build_import_master_cache(cur)

        for i, row_vals in enumerate(row_iter):
            if is_cancelled():
                if pending_commit_rows > 0:
                    conn.commit()
                pg(100, "Anulat.")
                return inserted_consults, skipped

            master_payload = {k: None for _, k in MASTER_FIELDS}
            consult_payload = {k: None for _, k in CONSULT_FIELDS}

            for key, pos in mapped_indexes:
                if pos >= len(row_vals):
                    val = None
                else:
                    val = row_vals[pos]
                v = _excel_to_str(val)
                if v is None or v == "":
                    continue
                if key in master_payload:
                    master_payload[key] = v
                elif key in consult_payload:
                    consult_payload[key] = v

            if _nonempty_payload_count(master_payload, consult_payload) <= 2:
                _rescue_from_full_row_values(row_vals, master_payload, consult_payload)

            _rescue_flat_row_payload(master_payload, consult_payload)

            if not master_payload.get("nume_prenume"):
                skipped += 1
                continue
            if _is_probable_import_header_row(master_payload, consult_payload):
                skipped += 1
                continue

            for dk in DATE_KEYS:
                if master_payload.get(dk) and not _validate_date_for_key(dk, master_payload[dk]):
                    master_payload[dk] = None
                if consult_payload.get(dk) and not _validate_date_for_key(dk, consult_payload[dk]):
                    consult_payload[dk] = None

            cnp_txt = (master_payload.get("cnp") or "").strip()
            if cnp_txt:
                digits = normalize_cnp_digits(cnp_txt)
                if not cnp_checksum_valid(digits):
                    master_payload["cnp"] = None
                else:
                    master_payload["cnp"] = digits

            existing = _resolve_existing_master_from_cache(
                master_payload,
                cache_by_id,
                cache_by_cnp,
                cache_by_name,
            )

            master_payload = normalize_master_from_cnp(master_payload)

            if existing is None:
                pid = _insert_master_and_consult_cur(
                    cur,
                    master_payload,
                    consult_payload,
                    source_action="import_from_excel_mapping",
                )
                cache_row = _cache_master_payload_row(pid, master_payload)
            else:
                pid = int(existing["id"])
                merged = dict(existing)
                for _, k in MASTER_FIELDS:
                    nv = master_payload.get(k)
                    if nv and (not merged.get(k)):
                        merged[k] = nv
                merged = normalize_master_from_cnp(merged)
                _update_master_and_insert_consult_cur(
                    cur,
                    pid,
                    merged,
                    consult_payload,
                    source_action="import_from_excel_mapping",
                )
                cache_row = _cache_master_payload_row(pid, merged)

            _update_import_master_cache(
                pid,
                cache_row,
                cache_by_id,
                cache_by_cnp,
                cache_by_name,
            )
            inserted_consults += 1
            pending_commit_rows += 1

            if pending_commit_rows >= IMPORT_DB_COMMIT_BATCH:
                conn.commit()
                pending_commit_rows = 0

            if total > 0 and (i % 50 == 0):
                pg(int(i * 100 / total), f"Import... {i}/{total}")

        if pending_commit_rows > 0:
            conn.commit()
    except Exception:
        try:
            conn.rollback()
        except Exception:
            pass
        raise
    finally:
        conn.close()

    pg(100, "Gata importul.")
    return inserted_consults, skipped


def export_csv_incremental(dest_path: str, progress_cb=None, cancelled_cb=None, chunk_size: int = 1000):
    """Exporta CSV incremental."""
    def pg(p, m=""):
        """Actualizeaza progresul operatiei in curs (helper intern pentru `export_csv_incremental`)."""
        if progress_cb:
            progress_cb(int(p), str(m))

    def is_cancelled():
        """Verifica daca cancelled ca helper intern in `export_csv_incremental`."""
        return bool(cancelled_cb and cancelled_cb())

    conn = get_conn()
    cur = conn.cursor()
    has_deleted_master = table_has_column("pacienti_master", "deleted")
    has_deleted_cons = table_has_column("consulturi", "deleted")
    m_where = "COALESCE(m.deleted,0)=0" if has_deleted_master else "1=1"
    c_deleted_clause = " AND COALESCE(c.deleted,0)=0" if has_deleted_cons else ""
    cur.execute(f"SELECT COUNT(*) FROM pacienti_master m WHERE {m_where}")
    total = int(cur.fetchone()[0] or 0)

    cur.execute(f"""
        SELECT
          m.id, m.nume_prenume, m.domiciliu, m.cnp, m.data_nasterii, m.sex, m.varsta, m.telefon,
          (
            SELECT c.data_consultului
            FROM consulturi c
            WHERE c.pacient_id=m.id
              {c_deleted_clause}
            ORDER BY COALESCE(c.data_consultului,'') DESC, c.id DESC
            LIMIT 1
          ) AS ultimul_consult,
          (
            SELECT COALESCE(NULLIF(c.diagnostic_liber,''), c.diagnostic_principal)
            FROM consulturi c
            WHERE c.pacient_id=m.id
              {c_deleted_clause}
            ORDER BY COALESCE(c.data_consultului,'') DESC, c.id DESC
            LIMIT 1
          ) AS ultim_diagnostic,
          (
            SELECT c.data_revenire_control
            FROM consulturi c
            WHERE c.pacient_id=m.id
              {c_deleted_clause}
            ORDER BY COALESCE(c.data_consultului,'') DESC, c.id DESC
            LIMIT 1
          ) AS data_revenire_control,
          (
            SELECT c.status_follow_up
            FROM consulturi c
            WHERE c.pacient_id=m.id
              {c_deleted_clause}
            ORDER BY COALESCE(c.data_consultului,'') DESC, c.id DESC
            LIMIT 1
          ) AS status_follow_up
        FROM pacienti_master m
        WHERE {m_where}
        ORDER BY m.nume_prenume COLLATE NOCASE ASC
    """)

    headers = [
        "id", "nume_prenume", "domiciliu", "cnp", "data_nasterii", "sex", "varsta", "telefon",
        "ultimul_consult", "ultim_diagnostic", "data_revenire_control", "status_follow_up"
    ]

    written = 0
    pg(0, "Pregatesc exportâ€¦")

    try:
        with open(dest_path, "w", newline="", encoding="utf-8-sig") as f:
            w = csv.writer(f)
            w.writerow(headers)

            while True:
                if is_cancelled():
                    pg(100, "Export anulat.")
                    return True

                rows = cur.fetchmany(chunk_size)
                if not rows:
                    break

                for r in rows:
                    w.writerow([("" if v is None else v) for v in r])

                written += len(rows)

                if total > 0:
                    p = min(99, int(written * 100 / total))
                    pg(p, f"Exportâ€¦ {written}/{total}")
                else:
                    pg(50, f"Exportâ€¦ {written}")

        pg(100, "Gata CSV.")
        return True
    finally:
        conn.close()


# ============================================================
# Jobs for threaded operations
# ============================================================
def job_export_csv(dest: str, progress_cb=None, cancelled_cb=None):
    """Executa jobul pentru export CSV."""
    return export_csv_incremental(dest, progress_cb=progress_cb, cancelled_cb=cancelled_cb, chunk_size=1000)


def job_backup_db(dest: str, progress_cb=None, cancelled_cb=None):
    """Executa jobul pentru backup baza de date."""
    def pg(p, m=""):
        """Actualizeaza progresul operatiei in curs (helper intern pentru `job_backup_db`)."""
        if progress_cb:
            progress_cb(int(p), str(m))

    def is_cancelled():
        """Verifica daca cancelled ca helper intern in `job_backup_db`."""
        return bool(cancelled_cb and cancelled_cb())

    pg(5, "Pregatesc backupâ€¦")

    try:
        pg(15, "Checkpoint WAL (PASSIVE)â€¦")
        conn = get_conn()
        conn.execute("PRAGMA wal_checkpoint(PASSIVE);")
        conn.close()
    except Exception:
        pass

    if is_cancelled():
        pg(100, "Backup anulat.")
        return True

    pg(45, "Copiez baza de dateâ€¦")
    export_db_copy_atomic(dest)
    if not _sqlite_backup_quick_check(Path(dest)):
        raise RuntimeError("Backup invalid: PRAGMA quick_check a esuat pentru fisierul exportat.")

    if is_cancelled():
        pg(100, "Backup anulat.")
        return True

    pg(100, "Gata backup.")
    return True

# ============================================================
# Dialog: Alerts
# ============================================================
class ControlAlertDialog(QDialog):
    def __init__(self, items, parent=None):
        """Initializeaza dialogul `ControlAlertDialog` si configureaza controalele interfetei."""
        super().__init__(parent)
        self.setWindowTitle("Alerte control")
        self.setModal(True)
        self.resize(900, 460)

        v = QVBoxLayout(self)

        lbl = QLabel("Acesti pacienti sunt programati pentru control")
        lbl.setStyleSheet("font-weight: 600; font-size: 14px;")
        v.addWidget(lbl)

        table = QTableWidget(0, 4)
        table.setHorizontalHeaderLabels(["Nume si prenume", "Telefon", "Diagnostic", "Data control"])
        table.setEditTriggers(QAbstractItemView.EditTrigger.NoEditTriggers)
        table.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
        table.setSelectionMode(QAbstractItemView.SelectionMode.SingleSelection)

        table.setRowCount(len(items))
        for i, it in enumerate(items):
            table.setItem(i, 0, QTableWidgetItem(it.get("nume_prenume", "")))
            table.setItem(i, 1, QTableWidgetItem(it.get("telefon", "") or ""))
            table.setItem(i, 2, QTableWidgetItem(it.get("diagnostic_principal", "") or ""))
            table.setItem(i, 3, QTableWidgetItem(it.get("data_revenire_control", "") or ""))

        h = table.horizontalHeader()
        h.setSectionResizeMode(QHeaderView.ResizeMode.ResizeToContents)
        v.addWidget(table, 1)

        btns = QDialogButtonBox(QDialogButtonBox.StandardButton.Ok)
        try:
            ok_btn = btns.button(QDialogButtonBox.StandardButton.Ok)
            if ok_btn:
                apply_std_icon(ok_btn, QStyle.StandardPixmap.SP_DialogOkButton)
        except Exception:
            pass
        btns.accepted.connect(self.accept)
        v.addWidget(btns)


# ============================================================
# Dialog: Patient Page (master + consult history)
# ============================================================
class PatientPageDialog(QDialog):
    """
    "Fisa pacientului": master info + consulturi (istoric).
    Permite editare master (inclusiv CNP) si vizualizare consulturi.
    """
    patientDataChanged = pyqtSignal(int)

    def __init__(self, pacient_id: int, parent=None):
        """Initializeaza fisa pacientului si controalele de filtrare/istoric consulturi."""
        super().__init__(parent)
        self.pacient_id = pacient_id
        self.setWindowTitle("Fisa pacientului")
        self.setModal(False)
        self.resize(1100, 700)

        root = QVBoxLayout(self)
        main_row = QHBoxLayout()
        main_row.setSpacing(12)
        root.addLayout(main_row, 1)

        left_panel = QWidget()
        left_root = QVBoxLayout(left_panel)
        left_root.setContentsMargins(0, 0, 0, 0)
        left_root.setSpacing(8)
        left_panel.setMaximumWidth(430)

        # Master box
        gb = QGroupBox("Date pacient")
        gb_l = QFormLayout(gb)
        self.inp_master = {}

        for label, key in MASTER_FIELDS:
            row_widget: QWidget
            if key in DATE_KEYS:
                w = DatePicker("YYYY-MM-DD", show_today=False)
                row_widget = w
            elif key == "sms_opt_out":
                cb_sms = QComboBox()
                cb_sms.addItem("DA", 0)
                cb_sms.addItem("NU", 1)
                w = cb_sms
                row_widget = wrap_selector_widget(cb_sms, self)
            else:
                w = QLineEdit()
                if key in ("sex", "varsta"):
                    w.setReadOnly(True)
                    w.setPlaceholderText("Auto din CNP / data nasterii")
                row_widget = w
            self.inp_master[key] = w
            gb_l.addRow(label, row_widget)

        btn_row = QHBoxLayout()
        self.btn_save_master = QPushButton("Salveaza date pacient")
        apply_std_icon(self.btn_save_master, QStyle.StandardPixmap.SP_DialogSaveButton)
        btn_row.addWidget(self.btn_save_master)
        btn_row.addStretch(1)
        gb_l.addRow(btn_row)

        self.btn_save_master.clicked.connect(self.save_master)

        left_root.addWidget(gb, 0)
        left_root.addStretch(1)
        main_row.addWidget(left_panel, 0)

        right_panel = QWidget()
        right_root = QVBoxLayout(right_panel)
        right_root.setContentsMargins(0, 0, 0, 0)
        right_root.setSpacing(8)
        main_row.addWidget(right_panel, 1)

        # Consults table
        right_root.addWidget(QLabel("Istoric consulturi (dublu click pe rand pentru editare):"))

        filter_row_dates = QHBoxLayout()
        self.flt_from = DatePicker("YYYY-MM-DD", show_today=False)
        self.flt_to = DatePicker("YYYY-MM-DD", show_today=False)
        self.flt_medic = QComboBox()
        self.flt_medic.addItem("Toti medicii", "")
        for medic_name in get_medic_dropdown_values():
            self.flt_medic.addItem(medic_name, medic_name)
        self.flt_medic.setToolTip("Filtreaza dupa medic")
        self.flt_diag = QLineEdit()
        self.flt_diag.setPlaceholderText("Diagnostic (principal/secundar/liber) contine")
        self.flt_diag.setMinimumWidth(230)
        self.flt_status = QComboBox()
        self.flt_status.addItem("Toate statusurile", "")
        self.flt_status.addItem("Programat", "Programat")
        self.flt_status.addItem("Neprogramat", "Neprogramat")
        self.btn_flt_apply = QPushButton("Filtreaza")
        self.btn_flt_reset = QPushButton("Reset")
        apply_std_icon(self.btn_flt_apply, QStyle.StandardPixmap.SP_DialogApplyButton)
        apply_std_icon(self.btn_flt_reset, QStyle.StandardPixmap.SP_DialogResetButton)
        filter_row_dates.addWidget(QLabel("De la:"))
        filter_row_dates.addWidget(self.flt_from)
        filter_row_dates.addWidget(QLabel("Pana la:"))
        filter_row_dates.addWidget(self.flt_to)
        filter_row_dates.addStretch(1)
        right_root.addLayout(filter_row_dates)

        filter_row_medic = QHBoxLayout()
        filter_row_medic.addWidget(QLabel("Medic:"))
        filter_row_medic.addWidget(wrap_selector_widget(self.flt_medic, self), 1)
        filter_row_medic.addStretch(1)
        right_root.addLayout(filter_row_medic)

        filter_row_diag = QHBoxLayout()
        filter_row_diag.addWidget(QLabel("Diagnostic:"))
        filter_row_diag.addWidget(self.flt_diag, 1)
        filter_row_diag.addStretch(1)
        right_root.addLayout(filter_row_diag)

        filter_row_status = QHBoxLayout()
        filter_row_status.addWidget(QLabel("Status:"))
        filter_row_status.addWidget(wrap_selector_widget(self.flt_status, self), 1)
        filter_row_status.addStretch(1)
        right_root.addLayout(filter_row_status)

        filter_row_nom = QHBoxLayout()
        filter_row_nom.addStretch(1)
        filter_row_nom.addWidget(self.btn_flt_apply)
        filter_row_nom.addWidget(self.btn_flt_reset)
        right_root.addLayout(filter_row_nom)

        self.tbl = QTableWidget(0, 9)
        self.tbl.setHorizontalHeaderLabels([
            "ID",
            "Data consult",
            "Medic",
            "Diagnostic",
            "Diag secundar",
            "Diag liber",
            "Control",
            "Status",
            "Ultimul",
        ])
        self.tbl.setEditTriggers(QAbstractItemView.EditTrigger.NoEditTriggers)
        self.tbl.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
        self.tbl.setSelectionMode(QAbstractItemView.SelectionMode.SingleSelection)
        self.tbl.cellDoubleClicked.connect(self.edit_selected_consult)
        self.tbl.setColumnHidden(0, True)
        self.tbl.setAlternatingRowColors(True)
        self.tbl.verticalHeader().setDefaultSectionSize(24)

        h = self.tbl.horizontalHeader()
        h.setSectionResizeMode(QHeaderView.ResizeMode.ResizeToContents)
        h.setSortIndicatorShown(True)
        h.setSortIndicator(1, Qt.SortOrder.DescendingOrder)
        self.tbl.setSortingEnabled(True)

        right_root.addWidget(self.tbl, 1)

        bottom = QHBoxLayout()
        self.btn_add_consult = QPushButton("Adauga consult nou")
        self.btn_delete_consult = QPushButton("Sterge consult selectat")
        self.btn_report = QPushButton("Genereaza raport (PDF)")
        self.btn_modules = QPushButton("Module pacient")
        apply_std_icon(self.btn_add_consult, QStyle.StandardPixmap.SP_FileDialogNewFolder)
        apply_std_icon(self.btn_delete_consult, QStyle.StandardPixmap.SP_TrashIcon)
        apply_std_icon(self.btn_report, QStyle.StandardPixmap.SP_DialogSaveButton)
        apply_std_icon(self.btn_modules, QStyle.StandardPixmap.SP_DirIcon)
        self.btn_report.setToolTip("Creeaza raport PDF pentru consultul selectat (sau ultimul daca nu e selectat)")
        bottom.addWidget(self.btn_add_consult)
        bottom.addWidget(self.btn_delete_consult)
        bottom.addWidget(self.btn_report)
        bottom.addWidget(self.btn_modules)
        bottom.addStretch(1)
        right_root.addLayout(bottom)

        self.btn_add_consult.clicked.connect(self.add_consult)
        self.btn_delete_consult.clicked.connect(self.delete_consult)
        self.btn_report.clicked.connect(self.generate_report)
        self.btn_modules.clicked.connect(self.open_patient_modules)
        self.btn_flt_apply.clicked.connect(self.apply_consult_filters)
        self.btn_flt_reset.clicked.connect(self.reset_consult_filters)
        self.flt_diag.returnPressed.connect(self.apply_consult_filters)
        self.flt_medic.currentIndexChanged.connect(self.apply_consult_filters)
        self.flt_status.currentIndexChanged.connect(self.apply_consult_filters)

        self._role_can_edit = True
        self._role_can_delete = True
        self.apply_role_permissions()

        self.reload()

    def _notify_patient_changed(self):
        """Gestioneaza patient changed in `PatientPageDialog`."""
        try:
            self.patientDataChanged.emit(int(self.pacient_id))
        except Exception:
            pass

    def reload(self):
        """Reincarca datele pacientului si istoricul consulturilor din baza de date."""
        m = get_master(self.pacient_id)
        if m is None:
            QMessageBox.warning(self, "Info", "Pacientul nu mai exista.")
            self.reject()
            return

        for _, k in MASTER_FIELDS:
            v = m[k] if k in m.keys() else None
            w = self.inp_master[k]
            if k in DATE_KEYS:
                w.setText("" if v is None else str(v))
            elif k == "sms_opt_out":
                try:
                    idx_sms = w.findData(_to_int_flag(v))
                    w.setCurrentIndex(idx_sms if idx_sms >= 0 else 0)
                except Exception:
                    pass
            else:
                w.setText("" if v is None else str(v))

        self._all_consults = [dict(r) for r in get_consults(self.pacient_id)]
        self._render_consults(self._all_consults)

    def _render_consults(self, rows: List[Dict[str, Any]]):
        """Afiseaza lista consulturilor in tabelul din fisa pacientului."""
        sorting_was = self.tbl.isSortingEnabled()
        sort_col = self.tbl.horizontalHeader().sortIndicatorSection()
        sort_order = self.tbl.horizontalHeader().sortIndicatorOrder()
        self.tbl.setSortingEnabled(False)
        self.tbl.setRowCount(len(rows))
        for i, rd in enumerate(rows):
            self.tbl.setItem(i, 0, QTableWidgetItem(str(rd.get("id", ""))))
            self.tbl.setItem(i, 1, QTableWidgetItem(rd.get("data_consultului") or ""))
            self.tbl.setItem(i, 2, QTableWidgetItem(rd.get("medic") or ""))
            self.tbl.setItem(i, 3, QTableWidgetItem(rd.get("diagnostic_principal") or ""))
            self.tbl.setItem(i, 4, QTableWidgetItem(rd.get("diagnostic_secundar") or ""))
            self.tbl.setItem(i, 5, QTableWidgetItem(rd.get("diagnostic_liber") or ""))
            self.tbl.setItem(i, 6, QTableWidgetItem(rd.get("data_revenire_control") or ""))
            self.tbl.setItem(i, 7, QTableWidgetItem(rd.get("status_follow_up") or ""))
            badge = QTableWidgetItem("ULTIM" if i == 0 else "")
            if i == 0:
                badge.setForeground(QBrush(QColor("#ffffff")))
                badge.setBackground(QBrush(QColor("#2f6fed")))
                badge.setTextAlignment(Qt.AlignmentFlag.AlignCenter)
            self.tbl.setItem(i, 8, badge)
        self.tbl.setSortingEnabled(sorting_was)
        if sorting_was and sort_col >= 0:
            self.tbl.sortItems(sort_col, sort_order)

    def apply_consult_filters(self):
        """Filtreaza consulturile din fisa dupa interval, medic, diagnostic si status."""
        rows = list(self._all_consults or [])
        q_medic = (self.flt_medic.currentData() or self.flt_medic.currentText() or "").strip()
        q_diag = (self.flt_diag.text() or "").strip()
        q_status = (self.flt_status.currentData() or self.flt_status.currentText() or "").strip()
        d_from = (self.flt_from.text() or "").strip()
        d_to = (self.flt_to.text() or "").strip()
        q_medic_n = _norm(q_medic)
        q_diag_tokens = [tok for tok in _norm(q_diag).split(" ") if tok]

        def _in_range(dval: str) -> bool:
            """Gestioneaza range in `PatientPageDialog`, ca helper intern in `apply_consult_filters`."""
            if not dval:
                return False
            if d_from and dval < d_from:
                return False
            if d_to and dval > d_to:
                return False
            return True

        out = []
        for r in rows:
            if q_medic_n and q_medic_n not in _norm(r.get("medic") or ""):
                continue
            if q_diag_tokens:
                diag_blob = (
                    f"{r.get('diagnostic_principal') or ''} "
                    f"{r.get('diagnostic_secundar') or ''} "
                    f"{r.get('diagnostic_liber') or ''}"
                )
                diag_norm = _norm(diag_blob)
                if not all(tok in diag_norm for tok in q_diag_tokens):
                    continue
            if q_status and (r.get("status_follow_up") or "") != q_status:
                continue
            if d_from or d_to:
                dval = (r.get("data_consultului") or "").strip()
                if not dval or not _in_range(dval):
                    continue
            out.append(r)
        self._render_consults(out)

    def reset_consult_filters(self):
        """Reseteaza filtrele din fisa pacientului la starea implicita."""
        self.flt_from.setText("")
        self.flt_to.setText("")
        self.flt_medic.setCurrentIndex(0)
        self.flt_diag.setText("")
        self.flt_status.setCurrentIndex(0)
        self._render_consults(self._all_consults or [])
    def save_master(self):
        """Salveaza modificarile facute pe datele de identificare ale pacientului."""
        payload = {}
        for _, k in MASTER_FIELDS:
            w = self.inp_master[k]
            if k in DATE_KEYS:
                txt = w.text().strip()
                payload[k] = txt if txt else None
            elif k == "sms_opt_out":
                try:
                    payload[k] = int(w.currentData() or 0)
                except Exception:
                    payload[k] = 0
            else:
                payload[k] = w.text().strip() or None

        if not payload.get("nume_prenume"):
            QMessageBox.warning(self, "Date invalide", "Nume si prenume este obligatoriu.")
            return
        if payload.get("data_nasterii") and not validate_ymd_or_empty(payload["data_nasterii"]):
            QMessageBox.warning(self, "Date invalide", "Data nasterii trebuie sa fie YYYY-MM-DD.")
            return
        phone_txt = (payload.get("telefon") or "").strip()
        if phone_txt:
            if not is_valid_ro_mobile_phone(phone_txt):
                btn_phone = QMessageBox.question(
                    self,
                    "Telefon invalid",
                    "Telefonul nu este valid pentru mobil RO.\nContinui salvarea fara telefon?",
                    QMessageBox.StandardButton.Ok | QMessageBox.StandardButton.Cancel,
                    QMessageBox.StandardButton.Cancel,
                )
                if btn_phone != QMessageBox.StandardButton.Ok:
                    return
                payload["telefon"] = None
            else:
                payload["telefon"] = normalize_ro_mobile_phone(phone_txt)

        # CNP strict (13 cifre + checksum) cu opČ›iune salvare fÄrÄ CNP
        cnp_txt = (payload.get("cnp") or "").strip()
        if cnp_txt:
            digits = normalize_cnp_digits(cnp_txt)
            if len(digits) != 13:
                btn = QMessageBox.question(
                    self, "CNP invalid",
                    f"CNP invalid: {len(digits)} cifre (trebuie 13).\n\nSalvez fara CNPT",
                    QMessageBox.StandardButton.Ok | QMessageBox.StandardButton.Cancel,
                    QMessageBox.StandardButton.Cancel
                )
                if btn != QMessageBox.StandardButton.Ok:
                    return
                payload["cnp"] = None
                payload["sex"] = None
            elif not cnp_checksum_valid(digits):
                btn = QMessageBox.question(
                    self, "CNP invalid",
                    "CNP invalid: checksum gresit.\n\nSalvez fara CNPT",
                    QMessageBox.StandardButton.Ok | QMessageBox.StandardButton.Cancel,
                    QMessageBox.StandardButton.Cancel
                )
                if btn != QMessageBox.StandardButton.Ok:
                    return
                payload["cnp"] = None
                payload["sex"] = None
            else:
                payload["cnp"] = digits
                sx = sex_from_cnp(digits)
                sx_cur = (payload.get("sex") or "").strip()
                if sx and sx_cur and _norm(sx_cur) != _norm(sx):
                    btn_sex = QMessageBox.question(
                        self,
                        "Incoerenta CNP/Sex",
                        f"Sex introdus: {sx_cur}\nSex din CNP: {sx}\n\nCorectez la sexul din CNP?",
                        QMessageBox.StandardButton.Ok | QMessageBox.StandardButton.Cancel,
                        QMessageBox.StandardButton.Ok,
                    )
                    if btn_sex != QMessageBox.StandardButton.Ok:
                        return
                if sx:
                    payload["sex"] = sx

        # normalize (sex/dn/varsta)
        payload = normalize_master_from_cnp(payload)

        try:
            update_master(self.pacient_id, payload)
            QMessageBox.information(self, "OK", "Date pacient salvate.")
            self.reload()
            self._notify_patient_changed()
            log_action("update_master", f"pid={self.pacient_id}")
        except Exception as e:
            QMessageBox.critical(self, "Eroare", str(e))

    def _selected_consult_id(self) -> Optional[int]:
        """Gestioneaza consult ID in `PatientPageDialog`."""
        row = self.tbl.currentRow()
        if row < 0:
            return None
        it = self.tbl.item(row, 0)
        if not it:
            return None
        try:
            return int(it.text())
        except Exception:
            return None

    def add_consult(self):
        """Adauga consult nou din fisa pacientului si reincarca istoricul."""
        d = ConsultEditDialog(parent=self, title="Consult nou")
        if d.exec() == QDialog.DialogCode.Accepted:
            payload = d.get_payload()
            try:
                insert_consult(self.pacient_id, payload)
                self._auto_send_consult_confirmation_sms(payload)
                self.reload()
                self._notify_patient_changed()
            except Exception as e:
                QMessageBox.critical(self, "Eroare", str(e))

    def edit_selected_consult(self, *_):
        """Editeaza consultul selectat din istoricul pacientului."""
        if not self._role_can_edit:
            return
        cid = self._selected_consult_id()
        if cid is None:
            return
        r = get_consult_by_id(cid)
        if r is None:
            return

        d = ConsultEditDialog(parent=self, title=f"Editare consult ID={cid}")
        d.set_payload(dict(r))
        if d.exec() == QDialog.DialogCode.Accepted:
            payload = d.get_payload()
            try:
                update_consult(cid, payload)
                self.reload()
                self._notify_patient_changed()
            except Exception as e:
                QMessageBox.critical(self, "Eroare", str(e))

    def delete_consult(self):
        """Sterge consultul selectat din fisa pacientului cu confirmare."""
        if not self._role_can_delete:
            return
        cid = self._selected_consult_id()
        if cid is None:
            return
        if QMessageBox.question(
            self,
            "Confirmare",
            "Stergi consultul selectat?",
            QMessageBox.StandardButton.Ok | QMessageBox.StandardButton.Cancel,
            QMessageBox.StandardButton.Cancel,
        ) != QMessageBox.StandardButton.Ok:
            return
        try:
            delete_consult(cid)
            self.reload()
            self._notify_patient_changed()
        except Exception as e:
            QMessageBox.critical(self, "Eroare", str(e))

    def generate_report(self):
        # consult selectat (din istoric)
        """Genereaza raport medical pentru consultul selectat."""
        cid = self._selected_consult_id()
        if cid is None:
            QMessageBox.warning(self, "Info", "Selecteaza un consult din lista inainte de generarea raportului.")
            return
        consult = get_consult_by_id(cid)
        master = get_master(self.pacient_id)
        if master is None:
            QMessageBox.warning(self, "Info", "Pacientul nu mai exista.")
            return
        if consult is None:
            QMessageBox.warning(self, "Info", "Consultul selectat nu mai exista.")
            return

        try:
            out_path = generate_medical_report_pdf(dict(master), dict(consult))
            rtf_path = generate_medical_report_rtf(dict(master), dict(consult))
            d = ReportPreviewDialog(out_path, rtf_path=rtf_path, parent=self)
            d.exec()
            log_action("report_pdf", f"pid={self.pacient_id}; consult_id={cid}")
        except Exception as e:
            QMessageBox.critical(self, "Eroare", str(e))

    def open_patient_modules(self):
        """Deschide modulele extinse asociate pacientului curent."""
        d = PatientModulesDialog(self.pacient_id, parent=self)
        d.exec()

    def _auto_send_consult_confirmation_sms(self, consult_payload: Optional[Dict[str, Any]] = None):
        """Trimite automat SMS de confirmare dupa adaugarea unui consult nou."""
        patient_id = int(self.pacient_id or 0)
        if patient_id <= 0:
            return

        try:
            m = get_master(patient_id)
        except Exception:
            m = None
        if m is None:
            return

        if _to_int_flag(m["sms_opt_out"] if "sms_opt_out" in m.keys() else 0) == 1:
            try:
                log_action("auto_consult_sms_skipped", f"pid={patient_id}; source=patient_page; reason=sms_disabled")
            except Exception:
                pass
            return

        phone_raw = (m["telefon"] if "telefon" in m.keys() else "") or ""
        phone = normalize_ro_mobile_phone(phone_raw) or str(phone_raw).strip()
        if not phone:
            try:
                log_action("auto_consult_sms_skipped", f"pid={patient_id}; source=patient_page; reason=missing_phone")
            except Exception:
                pass
            return

        cp = dict(consult_payload or {})
        slot = _consult_confirmation_slot(cp)
        if not slot:
            try:
                log_action("auto_consult_sms_skipped", f"pid={patient_id}; source=patient_page; reason=missing_control_date")
            except Exception:
                pass
            return
        consult_date, consult_time = slot
        medic_name = (cp.get("medic") or "").strip() or "medic"

        clinic = get_clinic_settings()
        clinic_name = (clinic.get("clinic_name") or "Clinica").strip() or "Clinica"
        contact = (clinic.get("clinic_phone") or "").strip() or clinic_name
        templates = _get_reminder_templates()
        template = templates.get("confirm") or REMINDER_TEMPLATE_CONFIRM

        ctx = {
            "nume_prenume": (m["nume_prenume"] if "nume_prenume" in m.keys() else "") or "",
            "date": consult_date,
            "time": consult_time,
            "medic": medic_name,
            "location": clinic_name,
            "status": "Confirmat",
            "contact": contact,
        }
        msg = render_template_text(template, ctx)
        msg = re.sub(r"\s+", " ", (msg or "").strip())
        if not msg:
            msg = f"Programarea dvs este confirmata: {consult_date}, medic {medic_name}. {contact}"

        sms_cfg = build_sms_gateway_runtime_config()

        def _run_send():
            """Ruleaza send in `PatientPageDialog`, ca helper intern in `_auto_send_consult_confirmation_sms`."""
            try:
                res = _send_sms_with_retry(
                    phone,
                    msg,
                    sms_config=sms_cfg,
                    cancelled_cb=None,
                )
                attempts = 1
                if isinstance(res, dict):
                    try:
                        attempts = int(res.get("attempt", 1) or 1)
                    except Exception:
                        attempts = 1
                try:
                    log_action(
                        "auto_consult_sms_sent",
                        f"pid={patient_id}; source=patient_page; phone={phone}; date={consult_date}; medic={medic_name}; attempts={attempts}",
                    )
                except Exception:
                    pass
            except Exception as e:
                try:
                    log_action(
                        "auto_consult_sms_failed",
                        f"pid={patient_id}; source=patient_page; phone={phone}; err={str(e)}",
                    )
                except Exception:
                    pass

        try:
            threading.Thread(target=_run_send, daemon=True).start()
        except Exception:
            pass

    def apply_role_permissions(self):
        """Aplica role permissions in `PatientPageDialog`."""
        role = get_current_role()
        can_edit = role in ("admin", "medic", "asistenta")
        can_delete = role in ("admin", "medic")
        self._role_can_edit = can_edit
        self._role_can_delete = can_delete

        try:
            self.btn_save_master.setEnabled(can_edit)
            self.btn_add_consult.setEnabled(can_edit)
            self.btn_delete_consult.setEnabled(can_delete)
            for _, k in MASTER_FIELDS:
                w = self.inp_master.get(k)
                if not w:
                    continue
                if isinstance(w, DatePicker):
                    w.edit.setReadOnly(not can_edit)
                    try:
                        w.btn.setEnabled(can_edit)
                    except Exception:
                        pass
                elif k in ("sex", "varsta") and isinstance(w, QLineEdit):
                    w.setReadOnly(True)
                elif k == "sms_opt_out" and isinstance(w, QComboBox):
                    w.setEnabled(can_edit)
                elif isinstance(w, QLineEdit):
                    w.setReadOnly(not can_edit)
        except Exception:
            pass


_patient_page_windows: Dict[str, QDialog] = {}


def open_patient_page_window(
    pacient_id: int,
    owner: Optional[QWidget] = None,
    on_close=None,
    on_change=None,
) -> Optional[QDialog]:
    """Deschide patient page window."""
    try:
        pid = int(pacient_id)
    except Exception:
        return None
    key = f"patient_page::{pid}"

    def _find_modeless_host(start: Optional[QWidget]) -> Optional[QWidget]:
        """Cauta modeless host ca helper intern in `open_patient_page_window`."""
        cur = start
        seen = set()
        while cur is not None and id(cur) not in seen:
            seen.add(id(cur))
            opener = getattr(cur, "_open_modeless_page", None)
            if callable(opener):
                return cur
            try:
                cur = cur.parentWidget()
            except Exception:
                cur = None
        app = QApplication.instance()
        if app is None:
            return None
        try:
            aw = app.activeWindow()
            opener = getattr(aw, "_open_modeless_page", None)
            if aw is not None and callable(opener):
                return aw
        except Exception:
            pass
        try:
            for top in app.topLevelWidgets():
                opener = getattr(top, "_open_modeless_page", None)
                if callable(opener):
                    return top
        except Exception:
            pass
        return None

    host = _find_modeless_host(owner)
    if host is not None:
        def _factory():
            """Construieste instanta de dialog/pagina folosita de deschiderea modeless (helper intern pentru `open_patient_page_window`)."""
            dlg = PatientPageDialog(pid, parent=None)
            if callable(on_change):
                try:
                    dlg.patientDataChanged.connect(on_change)
                except Exception:
                    pass
            return dlg
        try:
            return host._open_modeless_page(
                key,
                _factory,
                on_close=on_close,
            )
        except Exception:
            pass

    existing = _patient_page_windows.get(key)
    if existing is not None:
        try:
            if existing.isVisible():
                if existing.isMinimized():
                    existing.showNormal()
                existing.raise_()
                existing.activateWindow()
                return existing
        except Exception:
            pass
        _patient_page_windows.pop(key, None)

    try:
        dlg = PatientPageDialog(pid, parent=None)
    except Exception:
        return None
    if callable(on_change):
        try:
            dlg.patientDataChanged.connect(on_change)
        except Exception:
            pass

    try:
        dlg.setWindowModality(Qt.WindowModality.NonModal)
        dlg.setWindowFlag(Qt.WindowType.Window, True)
        dlg.setWindowFlag(Qt.WindowType.WindowContextHelpButtonHint, False)
        dlg.setAttribute(Qt.WidgetAttribute.WA_DeleteOnClose, True)
        if APP_ICON is not None:
            dlg.setWindowIcon(APP_ICON)
    except Exception:
        pass

    def _on_destroyed(_obj=None):
        """Gestioneaza evenimentul destroyed ca helper intern in `open_patient_page_window`."""
        _patient_page_windows.pop(key, None)
        if callable(on_close):
            try:
                on_close()
            except Exception:
                pass

    try:
        dlg.destroyed.connect(_on_destroyed)
    except Exception:
        pass
    _patient_page_windows[key] = dlg
    try:
        dlg.show()
        dlg.raise_()
        dlg.activateWindow()
    except Exception:
        try:
            dlg.show()
        except Exception:
            pass
    return dlg


# ============================================================
# Dialog: Consult edit
# ============================================================
class ConsultEditDialog(QDialog):
    def __init__(self, parent=None, title="Consult"):
        """Initializeaza dialogul `ConsultEditDialog` si configureaza controalele interfetei."""
        super().__init__(parent)
        self.setWindowTitle(title)
        self.setModal(True)
        self.resize(700, 520)

        root = QVBoxLayout(self)
        form = QFormLayout()
        self.inputs = {}

        for label, key in CONSULT_FIELDS:
            row_widget: QWidget
            if key == "data_revenire_control":
                w = DateTimePicker("YYYY-MM-DD", show_today=False)
                row_widget = w
            elif key in DATE_KEYS:
                w = DatePicker("YYYY-MM-DD", show_today=(key == "data_consultului"))
                row_widget = w
            elif key == "medic":
                w = QComboBox()
                w.addItem("")
                for medic_name in get_medic_dropdown_values():
                    w.addItem(medic_name)
                row_widget = wrap_selector_widget(w, self)
            elif key == "status_follow_up":
                w = QComboBox()
                w.addItems(["", "Programat", "Neprogramat"])
                row_widget = wrap_selector_widget(w, self)
            elif key in CONSULT_NOMENCLATOR_KEYS:
                w = QComboBox()
                w.addItem("")
                for val in get_nomenclator_values_by_key(key):
                    w.addItem(val)
                row_widget = wrap_selector_widget(w, self)
            elif key in CONSULT_BOOL_KEYS:
                w = QComboBox()
                w.addItems(["", "DA", "NU"])
                row_widget = wrap_selector_widget(w, self)
            elif key == "interval_luni_revenire":
                w = QSpinBox()
                w.setRange(0, 120)
                w.setSpecialValueText("")
                row_widget = wrap_selector_widget(w, self)
            elif key in TEXTAREA_KEYS:
                w = QTextEdit()
                w.setFixedHeight(90)
                row_widget = w
            else:
                w = QLineEdit()
                if key == "diagnostic_principal":
                    apply_icd10_completer(w, multi=False)
                elif key == "diagnostic_secundar":
                    apply_icd10_completer(w, multi=True)
                row_widget = w
            self.inputs[key] = w
            form.addRow(label, row_widget)

        root.addLayout(form)

        btns = QDialogButtonBox(QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel)
        try:
            ok_btn = btns.button(QDialogButtonBox.StandardButton.Ok)
            if ok_btn:
                apply_std_icon(ok_btn, QStyle.StandardPixmap.SP_DialogOkButton)
            cancel_btn = btns.button(QDialogButtonBox.StandardButton.Cancel)
            if cancel_btn:
                apply_std_icon(cancel_btn, QStyle.StandardPixmap.SP_DialogCancelButton)
        except Exception:
            pass
        btns.accepted.connect(self.accept)
        btns.rejected.connect(self.reject)
        root.addWidget(btns)

    def set_payload(self, p: dict):
        """Seteaza payload in `ConsultEditDialog`."""
        for _, key in CONSULT_FIELDS:
            w = self.inputs[key]
            v = p.get(key)

            if key in DATE_KEYS:
                w.setText("" if not v else str(v))

            elif key in CONSULT_COMBO_KEYS or key == "medic":
                if v:
                    idx = w.findText(str(v))
                    if idx < 0 and key == "medic":
                        w.addItem(str(v))
                        idx = w.findText(str(v))
                    w.setCurrentIndex(idx if idx >= 0 else 0)
                else:
                    w.setCurrentIndex(0)

            elif key == "interval_luni_revenire":
                w.setValue(int(v) if v not in (None, "") else 0)

            elif key in TEXTAREA_KEYS:
                w.setPlainText("" if v is None else str(v))

            else:
                w.setText("" if v is None else str(v))

    def get_payload(self) -> dict:
        """Returneaza payload in `ConsultEditDialog`."""
        payload = {}
        for _, key in CONSULT_FIELDS:
            w = self.inputs[key]

            if key in DATE_KEYS:
                txt = w.text().strip()
                payload[key] = txt if txt else None

            elif key in CONSULT_COMBO_KEYS or key == "medic":
                val = w.currentText().strip()
                payload[key] = val if val else None

            elif key == "interval_luni_revenire":
                v = int(w.value())
                payload[key] = None if v == 0 else v

            elif key in TEXTAREA_KEYS:
                payload[key] = w.toPlainText().strip() or None

            else:
                payload[key] = w.text().strip() or None

        # validate date formats
        for k in ("data_consultului", "data_revenire_control"):
            if payload.get(k) and not _validate_date_for_key(k, payload[k]):
                payload[k] = None
        d_cons = _safe_parse_ymd(payload.get("data_consultului"))
        d_ctrl = _safe_parse_ymd(payload.get("data_revenire_control"))
        if d_cons is not None and d_ctrl is not None and d_ctrl < d_cons:
            payload["data_revenire_control"] = None
        payload = normalize_consult_diagnoses(payload, parent=self)
        return payload


# ============================================================
# Dialog: Duplicate resolution (name match)
# ============================================================
class DuplicateNameResolutionDialog(QDialog):
    """
    Cand nume identic:
    - alegi un pacient existent ca target
    - poti edita CNP/Nume pentru target inainte de salvare (corectie)
    - apoi consultul se adauga in istoric (target)
    - sau poti crea pacient nou (master nou) + consult
    """
    def __init__(self, incoming_master: dict, incoming_consult: dict, candidates: List[sqlite3.Row], parent=None):
        """Initializeaza dialogul `DuplicateNameResolutionDialog` si configureaza controalele interfetei."""
        super().__init__(parent)
        self.incoming_master = incoming_master
        self.incoming_consult = incoming_consult
        self.candidates = [dict(r) for r in candidates]
        self.result_action = None  # "merge" / "new"
        self.selected_target_id: Optional[int] = None
        self.corrected_master_payload: Optional[dict] = None

        self.setWindowTitle("Nume identic â€“ verificare duplicat")
        self.setModal(True)
        self.resize(980, 520)

        root = QVBoxLayout(self)
        root.addWidget(QLabel("Exista pacienti cu acelasi nume. Sunt duplicateT"))

        self.tbl = QTableWidget(0, 6)
        self.tbl.setHorizontalHeaderLabels(["ID", "Nume", "CNP", "Sex", "Telefon", "Data nasterii"])
        self.tbl.setEditTriggers(QAbstractItemView.EditTrigger.NoEditTriggers)
        self.tbl.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
        self.tbl.setSelectionMode(QAbstractItemView.SelectionMode.SingleSelection)
        self.tbl.verticalHeader().setDefaultSectionSize(26)
        h = self.tbl.horizontalHeader()
        h.setSectionResizeMode(QHeaderView.ResizeMode.ResizeToContents)

        self.tbl.setRowCount(len(self.candidates))
        for i, r in enumerate(self.candidates):
            self.tbl.setItem(i, 0, QTableWidgetItem(str(r.get("id", ""))))
            self.tbl.setItem(i, 1, QTableWidgetItem(r.get("nume_prenume") or ""))
            self.tbl.setItem(i, 2, QTableWidgetItem(r.get("cnp") or ""))
            self.tbl.setItem(i, 3, QTableWidgetItem(r.get("sex") or ""))
            self.tbl.setItem(i, 4, QTableWidgetItem(r.get("telefon") or ""))
            self.tbl.setItem(i, 5, QTableWidgetItem(r.get("data_nasterii") or ""))

        root.addWidget(self.tbl, 1)

        gb = QGroupBox("Corectie date (pentru pacientul selectat) â€“ optional")
        gb_l = QFormLayout(gb)
        self.ed_name = QLineEdit()
        self.ed_cnp = QLineEdit()
        self.ed_tel = QLineEdit()
        self.ed_dn = DatePicker("YYYY-MM-DD")
        self.ed_sex = QLineEdit()
        self.ed_sex.setReadOnly(True)
        self.ed_sex.setPlaceholderText("Auto din CNP")

        gb_l.addRow("Nume corect:", self.ed_name)
        gb_l.addRow("CNP corect:", self.ed_cnp)
        gb_l.addRow("Sex:", self.ed_sex)
        gb_l.addRow("Telefon corect:", self.ed_tel)
        gb_l.addRow("Data nasterii corect:", self.ed_dn)
        root.addWidget(gb)

        btns = QHBoxLayout()
        self.btn_merge = QPushButton("Da, este acelasi pacient â†’ adaug consult la selectat")
        self.btn_new = QPushButton("Nu, NU e duplicat â†’ creeaza pacient nou")
        self.btn_cancel = QPushButton("Renunta")
        apply_std_icon(self.btn_merge, QStyle.StandardPixmap.SP_DialogApplyButton)
        apply_std_icon(self.btn_new, QStyle.StandardPixmap.SP_FileDialogNewFolder)
        apply_std_icon(self.btn_cancel, QStyle.StandardPixmap.SP_DialogCancelButton)
        btns.addWidget(self.btn_merge)
        btns.addWidget(self.btn_new)
        btns.addStretch(1)
        btns.addWidget(self.btn_cancel)
        root.addLayout(btns)

        self.btn_merge.clicked.connect(self.do_merge)
        self.btn_new.clicked.connect(self.do_new)
        self.btn_cancel.clicked.connect(self.reject)

        if self.candidates:
            self.tbl.selectRow(0)
            self._prefill_from_selected()

        self.tbl.itemSelectionChanged.connect(self._prefill_from_selected)
        self.ed_cnp.textChanged.connect(self._cnp_live)

    def _cnp_live(self):
        """Gestioneaza live in `DuplicateNameResolutionDialog`."""
        digits = normalize_cnp_digits(self.ed_cnp.text())
        if cnp_checksum_valid(digits):
            self.ed_sex.setText(sex_from_cnp(digits) or "")
        else:
            self.ed_sex.setText("")

    def _prefill_from_selected(self):
        """Gestioneaza from selected in `DuplicateNameResolutionDialog`."""
        row = self.tbl.currentRow()
        if row < 0:
            return
        pid = int(self.tbl.item(row, 0).text())
        m = get_master(pid)
        if m is None:
            return
        self.ed_name.setText(m["nume_prenume"] or "")
        self.ed_cnp.setText(m["cnp"] or "")
        self.ed_tel.setText(m["telefon"] or "")
        self.ed_dn.setText(m["data_nasterii"] or "")
        self.ed_sex.setText(m["sex"] or "")

    def _selected_pid(self) -> Optional[int]:
        """Gestioneaza pid in `DuplicateNameResolutionDialog`."""
        row = self.tbl.currentRow()
        if row < 0:
            return None
        it = self.tbl.item(row, 0)
        if not it:
            return None
        try:
            return int(it.text())
        except Exception:
            return None

    def do_merge(self):
        """Gestioneaza merge in `DuplicateNameResolutionDialog`."""
        pid = self._selected_pid()
        if pid is None:
            QMessageBox.warning(self, "Selectare", "Selecteaza un pacient din lista.")
            return

        cnp_txt = (self.ed_cnp.text() or "").strip()
        if cnp_txt:
            digits = normalize_cnp_digits(cnp_txt)
            if len(digits) != 13:
                btn = QMessageBox.question(
                    self, "CNP invalid",
                    f"CNP invalid: {len(digits)} cifre (trebuie 13).\n\nSalvez fara CNPT",
                    QMessageBox.StandardButton.Ok | QMessageBox.StandardButton.Cancel,
                    QMessageBox.StandardButton.Cancel
                )
                if btn != QMessageBox.StandardButton.Ok:
                    return
                self.ed_cnp.setText("")
            elif not cnp_checksum_valid(digits):
                btn = QMessageBox.question(
                    self, "CNP invalid",
                    "CNP invalid: checksum gresit.\n\nSalvez fara CNPT",
                    QMessageBox.StandardButton.Ok | QMessageBox.StandardButton.Cancel,
                    QMessageBox.StandardButton.Cancel
                )
                if btn != QMessageBox.StandardButton.Ok:
                    return
                self.ed_cnp.setText("")
            else:
                self.ed_cnp.setText(digits)

        payload = {
            "nume_prenume": self.ed_name.text().strip() or None,
            "cnp": self.ed_cnp.text().strip() or None,
            "telefon": self.ed_tel.text().strip() or None,
            "data_nasterii": self.ed_dn.text().strip() or None,
            "sex": None,  # se va impune din CNP
            "domiciliu": None,
        }
        if not payload.get("nume_prenume"):
            QMessageBox.warning(self, "Date invalide", "Nume este obligatoriu.")
            return
        if payload.get("data_nasterii") and not validate_ymd_or_empty(payload["data_nasterii"]):
            QMessageBox.warning(self, "Date invalide", "Data nasterii trebuie sa fie YYYY-MM-DD.")
            return

        self.result_action = "merge"
        self.selected_target_id = pid
        self.corrected_master_payload = payload
        self.accept()

    def do_new(self):
        """Gestioneaza new in `DuplicateNameResolutionDialog`."""
        self.result_action = "new"
        self.accept()
# ============================================================
# Raport medical (PDF) â€“ ReportLab
# ============================================================
def _safe_filename(s: str) -> str:
    """Sanitizeaza numele de fisier pentru a evita caractere invalide."""
    s = (s or "").strip()
    s = re.sub(r"[^\w\-\. ]+", "_", s, flags=re.UNICODE)
    s = re.sub(r"\s+", " ", s).strip()
    return s[:120] if len(s) > 120 else s


def generate_medical_report_pdf(master: Dict[str, Any], consult: Dict[str, Any]) -> str:
    """
    Creeaza un PDF in APP_DIR/reports cu:
      - date pacient
      - date consult
      - diagnostic + observatii
    """
    from reportlab.lib.pagesizes import A4
    from reportlab.pdfgen import canvas
    from reportlab.lib.units import cm

    reports_dir = APP_DIR / "reports"
    reports_dir.mkdir(parents=True, exist_ok=True)

    nume = master.get("nume_prenume") or "Pacient"
    dcons = (consult.get("data_consultului") or "").strip() or datetime.now().strftime("%Y-%m-%d")
    base = _safe_filename(f"Raport_{nume}_{dcons}.pdf")
    out_path = str(reports_dir / base)

    c = canvas.Canvas(out_path, pagesize=A4)
    w, h = A4

    def draw_line(y, text, size=11, bold=False):
        """Gestioneaza line ca helper intern in `generate_medical_report_pdf`."""
        c.setFont("Helvetica-Bold" if bold else "Helvetica", size)
        c.drawString(2.0 * cm, y, text)

    y = h - 2.2 * cm
    draw_line(y, "RAPORT MEDICAL", size=16, bold=True)
    y -= 0.7 * cm
    draw_line(y, f"Data raport: {datetime.now().strftime('%Y-%m-%d %H:%M')}", size=10)
    y -= 0.9 * cm

    # ---- Patient master ----
    draw_line(y, "Date pacient", size=13, bold=True)
    y -= 0.55 * cm

    def kv(k, v):
        """Formateaza un rand cheie-valoare pentru raport (helper intern pentru `generate_medical_report_pdf`)."""
        nonlocal y
        v = "" if v is None else str(v)
        draw_line(y, f"{k}: {v}", size=11)
        y -= 0.45 * cm

    kv("Nume si prenume", master.get("nume_prenume"))
    kv("CNP", master.get("cnp"))
    kv("Sex", master.get("sex"))
    kv("Data nasterii", master.get("data_nasterii"))
    kv("Varsta", master.get("varsta"))
    kv("Telefon", master.get("telefon"))
    kv("Domiciliu", master.get("domiciliu"))

    y -= 0.25 * cm
    c.line(2.0 * cm, y, w - 2.0 * cm, y)
    y -= 0.6 * cm

    # ---- Consult ----
    draw_line(y, "Consult", size=13, bold=True)
    y -= 0.55 * cm

    kv("Data consultului", consult.get("data_consultului"))
    kv("Medic", consult.get("medic"))
    kv("Status follow-up", consult.get("status_follow_up"))
    kv("Data revenire control", consult.get("data_revenire_control"))
    kv("Interval (luni)", consult.get("interval_luni_revenire"))
    kv("Recomandare fizio-kinetoterapie", consult.get("recomandare_fizio_kineto"))
    kv("Status fizioterapie", consult.get("a_inceput_fizio"))

    y -= 0.2 * cm
    c.line(2.0 * cm, y, w - 2.0 * cm, y)
    y -= 0.6 * cm

    # text wrap helper
    def draw_paragraph(title: str, text: str):
        """Gestioneaza paragraph ca helper intern in `generate_medical_report_pdf`."""
        nonlocal y
        draw_line(y, title, size=12, bold=True)
        y -= 0.55 * cm

        text = (text or "").strip()
        if not text:
            draw_line(y, "(gol)", size=11)
            y -= 0.55 * cm
            return

        c.setFont("Helvetica", 11)
        max_width = w - 4.0 * cm
        words = text.split()
        line = ""
        for wd in words:
            test = (line + " " + wd).strip()
            if c.stringWidth(test, "Helvetica", 11) <= max_width:
                line = test
            else:
                c.drawString(2.0 * cm, y, line)
                y -= 0.45 * cm
                line = wd
                if y < 2.0 * cm:
                    c.showPage()
                    y = h - 2.2 * cm
                    c.setFont("Helvetica", 11)
        if line:
            c.drawString(2.0 * cm, y, line)
            y -= 0.55 * cm

    draw_paragraph(
        "Diagnostic principal",
        (consult.get("diagnostic_principal") or consult.get("diagnostic_liber") or ""),
    )
    if (consult.get("diagnostic_secundar") or "").strip():
        draw_paragraph("Diagnostic secundar", consult.get("diagnostic_secundar") or "")
    if (consult.get("diagnostic_liber") or "").strip():
        draw_paragraph("Diagnostic liber", consult.get("diagnostic_liber") or "")
    draw_paragraph("Observatii", consult.get("observatii") or "")

    y -= 0.2 * cm
    draw_line(y, "Semnatura medic: ____________________", size=11)
    y -= 0.6 * cm

    c.showPage()
    c.save()
    return out_path


def _rtf_escape(s: str) -> str:
    """Escape pentru caractere speciale folosite in continut RTF."""
    s = (s or "")
    s = s.replace("\\", "\\\\").replace("{", "\\{").replace("}", "\\}")
    s = s.replace("\r\n", "\n").replace("\r", "\n")
    s = s.replace("\n", "\\par\n")
    return s


def generate_medical_report_rtf(master: Dict[str, Any], consult: Dict[str, Any]) -> str:
    """Gestioneaza medical report RTF."""
    reports_dir = APP_DIR / "reports"
    reports_dir.mkdir(parents=True, exist_ok=True)
    nume = master.get("nume_prenume") or "Pacient"
    dcons = (consult.get("data_consultului") or "").strip() or datetime.now().strftime("%Y-%m-%d")
    base = _safe_filename(f"Raport_{nume}_{dcons}.rtf")
    out_path = str(reports_dir / base)

    lines = []
    lines.append("\\b RAPORT MEDICAL \\b0\\par")
    lines.append(f"Data raport: {_rtf_escape(datetime.now().strftime('%Y-%m-%d %H:%M'))}\\par")
    lines.append("\\par")
    lines.append("\\b Date pacient \\b0\\par")
    lines.append(f"Nume si prenume: {_rtf_escape(master.get('nume_prenume') or '')}\\par")
    lines.append(f"CNP: {_rtf_escape(master.get('cnp') or '')}\\par")
    lines.append(f"Sex: {_rtf_escape(master.get('sex') or '')}\\par")
    lines.append(f"Data nasterii: {_rtf_escape(master.get('data_nasterii') or '')}\\par")
    lines.append(f"Varsta: {_rtf_escape(str(master.get('varsta') or ''))}\\par")
    lines.append(f"Telefon: {_rtf_escape(master.get('telefon') or '')}\\par")
    lines.append(f"Domiciliu: {_rtf_escape(master.get('domiciliu') or '')}\\par")
    lines.append("\\par")
    lines.append("\\b Consult \\b0\\par")
    lines.append(f"Data consultului: {_rtf_escape(consult.get('data_consultului') or '')}\\par")
    lines.append(f"Medic: {_rtf_escape(consult.get('medic') or '')}\\par")
    lines.append(f"Status follow-up: {_rtf_escape(consult.get('status_follow_up') or '')}\\par")
    lines.append(f"Data revenire control: {_rtf_escape(consult.get('data_revenire_control') or '')}\\par")
    lines.append(f"Interval (luni): {_rtf_escape(str(consult.get('interval_luni_revenire') or ''))}\\par")
    lines.append(f"Recomandare fizio-kinetoterapie: {_rtf_escape(consult.get('recomandare_fizio_kineto') or '')}\\par")
    lines.append(f"Status fizioterapie: {_rtf_escape(consult.get('a_inceput_fizio') or '')}\\par")
    lines.append("\\par")
    lines.append("\\b Diagnostic principal \\b0\\par")
    lines.append(_rtf_escape(consult.get("diagnostic_principal") or consult.get("diagnostic_liber") or ""))
    if (consult.get("diagnostic_secundar") or "").strip():
        lines.append("\\par")
        lines.append("\\b Diagnostic secundar \\b0\\par")
        lines.append(_rtf_escape(consult.get("diagnostic_secundar") or ""))
    if (consult.get("diagnostic_liber") or "").strip():
        lines.append("\\par")
        lines.append("\\b Diagnostic liber \\b0\\par")
        lines.append(_rtf_escape(consult.get("diagnostic_liber") or ""))
    lines.append("\\par\\par")
    lines.append("\\b Observatii \\b0\\par")
    lines.append(_rtf_escape(consult.get("observatii") or ""))
    lines.append("\\par\\par")
    lines.append("Semnatura medic: ____________________\\par")

    rtf = "{\\rtf1\\ansi\\deff0 " + "\n".join(lines) + "}"
    Path(out_path).write_text(rtf, encoding="utf-8")
    return out_path


def generate_text_report_pdf(
    title: str,
    content: str,
    meta: Dict[str, Any],
    prefix: str = "doc",
    signature_path: Optional[str] = None,
    signed_by: Optional[str] = None,
) -> str:
    """Gestioneaza text report PDF."""
    reports_dir = APP_DIR / "reports"
    reports_dir.mkdir(parents=True, exist_ok=True)
    nume = meta.get("nume_prenume") or "Pacient"
    stamp = datetime.now().strftime("%Y-%m-%d_%H-%M")
    base = _safe_filename(f"{prefix}_{nume}_{stamp}.pdf")
    out_path = str(reports_dir / base)

    c = canvas.Canvas(out_path, pagesize=A4)
    w, h = A4
    y = h - 2.0 * cm

    clinic = get_clinic_settings()
    logo_path = clinic.get("clinic_logo") or ""
    if logo_path and Path(logo_path).exists():
        try:
            c.drawImage(logo_path, 2.0 * cm, y - 1.2 * cm, width=2.2 * cm, height=2.2 * cm, preserveAspectRatio=True, mask='auto')
        except Exception:
            pass
        left_x = 4.6 * cm
    else:
        left_x = 2.0 * cm
    c.setFont("Helvetica-Bold", 13)
    c.drawString(left_x, y, clinic.get("clinic_name") or "")
    c.setFont("Helvetica", 9)
    y -= 0.45 * cm
    if clinic.get("clinic_address"):
        c.drawString(left_x, y, clinic.get("clinic_address") or "")
        y -= 0.4 * cm
    if clinic.get("clinic_phone"):
        c.drawString(left_x, y, f"Tel: {clinic.get('clinic_phone')}")
        y -= 0.4 * cm
    y -= 0.4 * cm
    clinic = get_clinic_settings()
    logo_path = clinic.get("clinic_logo") or ""

    # header with logo + clinic info
    if logo_path and Path(logo_path).exists():
        try:
            c.drawImage(logo_path, 2.0 * cm, y - 1.2 * cm, width=2.2 * cm, height=2.2 * cm, preserveAspectRatio=True, mask='auto')
        except Exception:
            pass
        left_x = 4.6 * cm
    else:
        left_x = 2.0 * cm

    c.setFont("Helvetica-Bold", 13)
    c.drawString(left_x, y, clinic.get("clinic_name") or "")
    c.setFont("Helvetica", 9)
    y -= 0.45 * cm
    if clinic.get("clinic_address"):
        c.drawString(left_x, y, clinic.get("clinic_address") or "")
        y -= 0.4 * cm
    if clinic.get("clinic_phone"):
        c.drawString(left_x, y, f"Tel: {clinic.get('clinic_phone')}")
        y -= 0.4 * cm

    y -= 0.4 * cm
    c.setFont("Helvetica-Bold", 14)
    c.drawString(2.0 * cm, y, title or "Document")
    y -= 0.7 * cm

    c.setFont("Helvetica", 10)
    meta_lines = [
        f"Pacient: {meta.get('nume_prenume') or ''}",
        f"CNP: {meta.get('cnp') or ''}",
        f"Data: {meta.get('data') or ''}",
        f"Medic: {meta.get('medic') or ''}",
    ]
    for line in meta_lines:
        if not line.strip():
            continue
        c.drawString(2.0 * cm, y, line)
        y -= 0.45 * cm

    y -= 0.3 * cm
    c.setFont("Helvetica", 11)
    text = (content or "").strip()
    if not text:
        text = "-"
    for para in text.split("\n"):
        words = para.split()
        if not words:
            y -= 0.45 * cm
            continue
        line = ""
        for wd in words:
            test = (line + " " + wd).strip()
            if c.stringWidth(test, "Helvetica", 11) <= (w - 4.0 * cm):
                line = test
            else:
                c.drawString(2.0 * cm, y, line)
                y -= 0.45 * cm
                line = wd
                if y < 2.0 * cm:
                    c.showPage()
                    y = h - 2.0 * cm
                    c.setFont("Helvetica", 11)
        if line:
            c.drawString(2.0 * cm, y, line)
            y -= 0.45 * cm
            if y < 2.0 * cm:
                c.showPage()
                y = h - 2.0 * cm
                c.setFont("Helvetica", 11)

    # signature
    y -= 0.5 * cm
    if signed_by:
        c.setFont("Helvetica", 10)
        c.drawString(2.0 * cm, y, f"Semnat de: {signed_by}")
        y -= 0.5 * cm
    if signature_path and Path(signature_path).exists():
        try:
            c.drawImage(signature_path, 2.0 * cm, y - 1.2 * cm, width=4.0 * cm, height=1.6 * cm, preserveAspectRatio=True, mask='auto')
            y -= 1.6 * cm
        except Exception:
            pass

    c.showPage()
    c.save()
    return out_path


def generate_text_report_rtf(
    title: str,
    content: str,
    meta: Dict[str, Any],
    prefix: str = "doc",
    signed_by: Optional[str] = None,
) -> str:
    """Gestioneaza text report RTF."""
    reports_dir = APP_DIR / "reports"
    reports_dir.mkdir(parents=True, exist_ok=True)
    nume = meta.get("nume_prenume") or "Pacient"
    stamp = datetime.now().strftime("%Y-%m-%d_%H-%M")
    base = _safe_filename(f"{prefix}_{nume}_{stamp}.rtf")
    out_path = str(reports_dir / base)

    clinic = get_clinic_settings()
    lines = []
    if clinic.get("clinic_name"):
        lines.append(f"\\b {_rtf_escape(clinic.get('clinic_name'))} \\b0\\par")
    if clinic.get("clinic_address"):
        lines.append(f"{_rtf_escape(clinic.get('clinic_address'))}\\par")
    if clinic.get("clinic_phone"):
        lines.append(f"Tel: {_rtf_escape(clinic.get('clinic_phone'))}\\par")
    lines.append("\\par")
    lines.append(f"\\b { _rtf_escape(title or 'Document') } \\b0\\par")
    lines.append(f"Pacient: {_rtf_escape(meta.get('nume_prenume') or '')}\\par")
    lines.append(f"CNP: {_rtf_escape(meta.get('cnp') or '')}\\par")
    lines.append(f"Data: {_rtf_escape(meta.get('data') or '')}\\par")
    lines.append(f"Medic: {_rtf_escape(meta.get('medic') or '')}\\par")
    lines.append("\\par")
    lines.append(_rtf_escape(content or ""))
    if signed_by:
        lines.append("\\par")
        lines.append(f"Semnat de: {_rtf_escape(signed_by)}\\par")

    rtf = "{\\rtf1\\ansi\\deff0 " + "\n".join(lines) + "}"
    Path(out_path).write_text(rtf, encoding="utf-8")
    return out_path


# ============================================================
# UI: Splash (loading)
# ============================================================
def create_splash():
    """Creeaza splash."""
    w, h = 420, 260
    pix = QPixmap(w, h)
    pix.fill(QColor("#f2f3f5"))

    p = QPainter(pix)
    p.setRenderHint(QPainter.RenderHint.Antialiasing, True)

    # card
    p.setPen(QColor("#d0d4da"))
    p.setBrush(QColor("#ffffff"))
    p.drawRoundedRect(10, 10, w - 20, h - 20, 12, 12)

    # simple logo mark
    p.setBrush(QColor("#2f3b52"))
    p.setPen(QColor("#2f3b52"))
    p.drawEllipse(170, 45, 80, 80)
    p.setPen(QColor("#ffffff"))
    f = QFont("Segoe UI", 18, QFont.Weight.Bold)
    p.setFont(f)
    p.drawText(QRect(170, 45, 80, 80), Qt.AlignmentFlag.AlignCenter, "MBM")

    # title
    p.setPen(QColor("#1f2937"))
    f2 = QFont("Segoe UI", 16, QFont.Weight.DemiBold)
    p.setFont(f2)
    p.drawText(QRect(0, 135, w, 30), Qt.AlignmentFlag.AlignCenter, "MBM - Analytic")

    # subtitle
    p.setPen(QColor("#6b7280"))
    f3 = QFont("Segoe UI", 10)
    p.setFont(f3)
    p.drawText(QRect(0, 160, w, 20), Qt.AlignmentFlag.AlignCenter, "Se incarca aplicatia...")

    p.end()

    splash = QSplashScreen(pix)
    splash.setWindowFlag(Qt.WindowType.WindowStaysOnTopHint, True)

    bar = QProgressBar(splash)
    bar.setGeometry(30, 205, w - 60, 14)
    bar.setRange(0, 100)
    bar.setValue(0)
    bar.setTextVisible(False)
    bar.setStyleSheet(
        "QProgressBar {"
        "  border: 1px solid #d1d5db;"
        "  border-radius: 7px;"
        "  background: #f3f4f6;"
        "}"
        "QProgressBar::chunk {"
        "  border-radius: 7px;"
        "  background: #4e79a7;"
        "}"
    )

    return splash, bar


def show_schema_diagnostic_dialog(report: Dict[str, Any], parent=None) -> bool:
    """Afiseaza raportul de diagnostic schema si permite continuare controlata."""
    dlg = QDialog(parent)
    dlg.setWindowTitle("Diagnostic schema DB")
    dlg.resize(860, 560)

    root = QVBoxLayout(dlg)
    lbl = QLabel(
        "S-au detectat inconsistente in schema bazei de date.\n"
        "Revizuieste diagnosticul de mai jos inainte sa continui."
    )
    lbl.setWordWrap(True)
    root.addWidget(lbl)

    txt = QTextEdit()
    txt.setReadOnly(True)
    txt.setLineWrapMode(QTextEdit.LineWrapMode.NoWrap)
    txt.setPlainText(_format_schema_diagnostic_text(report))
    root.addWidget(txt, 1)

    buttons = QDialogButtonBox(
        QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel
    )
    btn_ok = buttons.button(QDialogButtonBox.StandardButton.Ok)
    btn_cancel = buttons.button(QDialogButtonBox.StandardButton.Cancel)
    if btn_ok:
        btn_ok.setText("Continua")
    if btn_cancel:
        btn_cancel.setText("Inchide aplicatia")
    buttons.accepted.connect(dlg.accept)
    buttons.rejected.connect(dlg.reject)
    root.addWidget(buttons)

    return dlg.exec() == QDialog.DialogCode.Accepted


def create_app_icon() -> QIcon:
    # Prefer clinic logo if configured
    """Creeaza app icon."""
    try:
        logo_path = get_setting("clinic_logo", "") or ""
        if logo_path and Path(logo_path).exists():
            src = QPixmap(logo_path)
            if not src.isNull():
                size = 256
                canvas = QPixmap(size, size)
                canvas.fill(Qt.GlobalColor.transparent)
                scaled = src.scaled(
                    size,
                    size,
                    Qt.AspectRatioMode.KeepAspectRatio,
                    Qt.TransformationMode.SmoothTransformation,
                )
                p = QPainter(canvas)
                p.setRenderHint(QPainter.RenderHint.Antialiasing, True)
                x = (size - scaled.width()) // 2
                y = (size - scaled.height()) // 2
                p.drawPixmap(x, y, scaled)
                p.end()
                return QIcon(canvas)
    except Exception:
        pass

    size = 256
    pix = QPixmap(size, size)
    pix.fill(QColor("#f2f3f5"))

    p = QPainter(pix)
    p.setRenderHint(QPainter.RenderHint.Antialiasing, True)

    p.setPen(QColor("#d0d4da"))
    p.setBrush(QColor("#ffffff"))
    p.drawRoundedRect(12, 12, size - 24, size - 24, 24, 24)

    p.setBrush(QColor("#2f3b52"))
    p.setPen(QColor("#2f3b52"))
    r = int(size * 0.5)
    p.drawEllipse((size - r) // 2, int(size * 0.2), r, r)

    p.setPen(QColor("#ffffff"))
    f = QFont("Segoe UI", 32, QFont.Weight.Bold)
    p.setFont(f)
    p.drawText(QRect((size - r) // 2, int(size * 0.2), r, r), Qt.AlignmentFlag.AlignCenter, "MBM")

    p.setPen(QColor("#1f2937"))
    f2 = QFont("Segoe UI", 20, QFont.Weight.DemiBold)
    p.setFont(f2)
    p.drawText(QRect(0, int(size * 0.72), size, 28), Qt.AlignmentFlag.AlignCenter, "Analytic")

    p.end()
    return QIcon(pix)


# ============================================================
# UI: Chart dialog (avg age by category)
# ============================================================
class AvgAgeByCategoryDialog(QDialog):
    def __init__(self, parent=None):
        """Initializeaza dialogul `AvgAgeByCategoryDialog` si configureaza controalele interfetei."""
        super().__init__(parent)
        self.setWindowTitle("Media varstei pe categorie")
        self.resize(800, 520)

        root = QVBoxLayout(self)
        top = QHBoxLayout()
        top.addWidget(QLabel("Categorie:"))

        self.combo = QComboBox()
        self.combo.addItem("Sex", "sex")
        self.combo.addItem("Status follow-up (ultimul consult)", "status_follow_up")
        top.addWidget(self.combo, 1)
        root.addLayout(top)

        self._no_chart_label = QLabel("")
        self._no_chart_label.setWordWrap(True)
        root.addWidget(self._no_chart_label)

        try:
            from matplotlib.backends.backend_qtagg import FigureCanvasQTAgg as FigureCanvas
            from matplotlib.figure import Figure
        except Exception:
            self._no_chart_label.setText(matplotlib_missing_message())
            return

        self.figure = Figure(figsize=(6, 4))
        self.canvas = FigureCanvas(self.figure)
        self.ax = self.figure.add_subplot(111)
        root.addWidget(self.canvas, 1)

        self.combo.currentIndexChanged.connect(self._render_chart)
        self._render_chart()

    def _render_chart(self):
        """Renderizeaza chart in `AvgAgeByCategoryDialog`."""
        key = self.combo.currentData()
        stats = avg_age_by_category(key)

        self.ax.clear()
        if not stats:
            self._no_chart_label.setText("Nu exista date suficiente pentru acest grafic.")
            self.canvas.draw()
            return
        self._no_chart_label.setText("")

        labels = [s[0] for s in stats]
        values = [s[1] for s in stats]
        counts = [s[2] for s in stats]

        bars = self.ax.bar(range(len(labels)), values, color="#4e79a7")
        self.ax.set_ylabel("Varsta medie (ani)")
        self.ax.set_title("Media varstei pe categorie")
        self.ax.set_xticks(range(len(labels)))
        self.ax.set_xticklabels(labels, rotation=20, ha="right")

        max_val = max(values) if values else 0
        self.ax.set_ylim(0, max(10, max_val * 1.2))

        for i, b in enumerate(bars):
            self.ax.text(
                b.get_x() + b.get_width() / 2,
                b.get_height(),
                f"{values[i]:.1f} ({counts[i]})",
                ha="center",
                va="bottom",
                fontsize=9,
            )

        try:
            with warnings.catch_warnings():
                warnings.simplefilter("ignore", UserWarning)
                self.figure.tight_layout()
        except Exception:
            pass
        self.canvas.draw()


# ============================================================
# UI: Report preview dialog (PDF + print/export)
# ============================================================
class ReportPreviewDialog(QDialog):
    def __init__(self, pdf_path: str, rtf_path: Optional[str] = None, parent=None):
        """Initializeaza dialogul `ReportPreviewDialog` si configureaza controalele interfetei."""
        super().__init__(parent)
        self.pdf_path = pdf_path
        self.rtf_path = rtf_path
        self.setWindowTitle("Raport PDF")
        if APP_ICON is not None:
            self.setWindowIcon(APP_ICON)
        self.resize(980, 720)

        root = QVBoxLayout(self)

        self.info = QLabel("")
        self.info.setWordWrap(True)
        root.addWidget(self.info)

        self._pdf_doc = None
        self._pdf_view = None
        self._has_viewer = False
        self._pdf_fitz = None
        self._fitz = None
        self._render_page_idx = 0
        self._page_count = 0
        self._render_scale = 2.0
        self._img_label = None
        self._page_label = None
        self._btn_prev = None
        self._btn_next = None

        try:
            from PyQt6.QtPdf import QPdfDocument
            from PyQt6.QtPdfWidgets import QPdfView

            self._pdf_doc = QPdfDocument(self)
            status = self._pdf_doc.load(self.pdf_path)
            if status == QPdfDocument.Status.Ready:
                self._pdf_view = QPdfView(self)
                self._pdf_view.setDocument(self._pdf_doc)
                self._pdf_view.setZoomMode(QPdfView.ZoomMode.FitInView)
                root.addWidget(self._pdf_view, 1)
                self._has_viewer = True
            else:
                self.info.setText("Nu pot afisa PDF-ul in aplicatie. Se va deschide extern la nevoie.")
        except Exception:
            self.info.setText(
                "Pentru afisarea PDF-ului in aplicatie este necesar modulul PyQt6-QtPdf "
                "sau PyMuPDF.\n"
                "Poti instala cu: pip install PyQt6-QtPdf   sau   pip install PyMuPDF"
            )

        if not self._has_viewer:
            try:
                fitz_module_name = "fi" + "tz"
                fitz = importlib.import_module(fitz_module_name)  # PyMuPDF

                self._fitz = fitz
                self._pdf_fitz = fitz.open(self.pdf_path)
                self._page_count = int(self._pdf_fitz.page_count)

                nav = QHBoxLayout()
                self._btn_prev = QPushButton("Pagina anterioara")
                self._btn_next = QPushButton("Pagina urmatoare")
                apply_std_icon(self._btn_prev, QStyle.StandardPixmap.SP_ArrowBack)
                apply_std_icon(self._btn_next, QStyle.StandardPixmap.SP_ArrowForward)
                self._page_label = QLabel("")
                self._page_label.setStyleSheet("color: gray;")
                self._btn_prev.clicked.connect(self._prev_page)
                self._btn_next.clicked.connect(self._next_page)
                nav.addWidget(self._btn_prev)
                nav.addWidget(self._btn_next)
                nav.addStretch(1)
                nav.addWidget(self._page_label)
                root.addLayout(nav)

                self._img_label = QLabel()
                self._img_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
                scroll = QScrollArea()
                scroll.setWidgetResizable(True)
                scroll.setWidget(self._img_label)
                root.addWidget(scroll, 1)

                self.info.setText("")
                self._render_page(0)
                self._has_viewer = True
            except Exception:
                pass

        btns = QHBoxLayout()
        self.btn_print = QPushButton("Printare")
        self.btn_export = QPushButton("Exporta")
        self.btn_export_word = QPushButton("Exporta Word")
        self.btn_close = QPushButton("Inchide")
        self.btn_print.setIcon(get_printer_icon(24))
        self.btn_print.setIconSize(QSize(22, 22))
        apply_std_icon(self.btn_export, QStyle.StandardPixmap.SP_DialogSaveButton)
        apply_std_icon(self.btn_export_word, QStyle.StandardPixmap.SP_DialogSaveButton)
        apply_std_icon(self.btn_close, QStyle.StandardPixmap.SP_DialogCloseButton)
        btns.addWidget(self.btn_print)
        btns.addWidget(self.btn_export)
        btns.addWidget(self.btn_export_word)
        btns.addStretch(1)
        btns.addWidget(self.btn_close)
        root.addLayout(btns)

        self.btn_print.clicked.connect(self.print_report)
        self.btn_export.clicked.connect(self.export_report)
        self.btn_export_word.clicked.connect(self.export_report_word)
        self.btn_close.clicked.connect(self.accept)

    def _render_page(self, idx: int):
        """Renderizeaza page in `ReportPreviewDialog`."""
        if not self._pdf_fitz or not self._fitz or not self._img_label:
            return
        if self._page_count <= 0:
            return
        idx = max(0, min(idx, self._page_count - 1))
        page = self._pdf_fitz.load_page(idx)
        mat = self._fitz.Matrix(self._render_scale, self._render_scale)
        pix = page.get_pixmap(matrix=mat, alpha=False)
        img = QImage(pix.samples, pix.width, pix.height, pix.stride, QImage.Format.Format_RGB888).copy()
        self._img_label.setPixmap(QPixmap.fromImage(img))
        self._render_page_idx = idx
        if self._page_label:
            self._page_label.setText(f"Pagina {idx + 1} / {self._page_count}")
        if self._btn_prev:
            self._btn_prev.setEnabled(idx > 0)
        if self._btn_next:
            self._btn_next.setEnabled(idx < self._page_count - 1)

    def _prev_page(self):
        """Gestioneaza page in `ReportPreviewDialog`."""
        self._render_page(self._render_page_idx - 1)

    def _next_page(self):
        """Gestioneaza page in `ReportPreviewDialog`."""
        self._render_page(self._render_page_idx + 1)

    def closeEvent(self, event):
        """Gestioneaza evenimentul Qt `closeEvent` pentru componenta curenta."""
        try:
            if self._pdf_fitz:
                self._pdf_fitz.close()
        except Exception:
            pass
        super().closeEvent(event)

    def print_report(self):
        """Gestioneaza report in `ReportPreviewDialog`."""
        try:
            if os.name == "nt":
                os.startfile(self.pdf_path, "print")
            else:
                QDesktopServices.openUrl(QUrl.fromLocalFile(self.pdf_path))
        except Exception as e:
            QMessageBox.warning(self, "Printare", f"Nu pot trimite la imprimanta.\n{e}")

    def export_report(self):
        """Exporta report in `ReportPreviewDialog`."""
        dest, _ = QFileDialog.getSaveFileName(
            self, "Exporta raport", str(Path(self.pdf_path).name), "PDF (*.pdf)"
        )
        if not dest:
            return
        try:
            shutil.copy2(self.pdf_path, dest)
            # Deschide fiČ™ierul Č™i locaČ›ia pentru trimitere prin mail/aplicaČ›ii
            try:
                QDesktopServices.openUrl(QUrl.fromLocalFile(dest))
            except Exception:
                pass
            try:
                if os.name == "nt":
                    subprocess.Popen(["explorer", "/select,", dest])
            except Exception:
                pass
            # Deschide Share UI (Windows) pentru trimitere prin mail/alte aplicaČ›ii
            try:
                if os.name == "nt":
                    ps_path = dest.replace("'", "''")
                    cmd = (
                        "$p = '{p}';"
                        "$sh = New-Object -ComObject Shell.Application;"
                        "$folder = $sh.Namespace((Split-Path $p));"
                        "$item = $folder.ParseName((Split-Path $p -Leaf));"
                        "if ($item -ne $null) {{ $item.InvokeVerb('Share') }}"
                    ).format(p=ps_path)
                    subprocess.Popen(["powershell", "-NoProfile", "-Command", cmd])
            except Exception:
                pass
        except Exception as e:
            QMessageBox.critical(self, "Exporta", f"Eroare la export:\n{e}")

    def export_report_word(self):
        """Exporta report word in `ReportPreviewDialog`."""
        if not self.rtf_path or not Path(self.rtf_path).exists():
            QMessageBox.warning(self, "Export Word", "Raportul Word nu este disponibil.")
            return
        dest, _ = QFileDialog.getSaveFileName(
            self, "Exporta Word", str(Path(self.rtf_path).name), "RTF (*.rtf)"
        )
        if not dest:
            return
        try:
            shutil.copy2(self.rtf_path, dest)
            try:
                QDesktopServices.openUrl(QUrl.fromLocalFile(dest))
            except Exception:
                pass
        except Exception as e:
            QMessageBox.critical(self, "Export Word", f"Eroare la export:\n{e}")


# ============================================================
# UI: Periodic report (upcoming controls)
# ============================================================
class PeriodicReportDialog(QDialog):
    def __init__(self, parent=None):
        """Initializeaza dialogul `PeriodicReportDialog` si configureaza controalele interfetei."""
        super().__init__(parent)
        self.setWindowTitle("Raport periodic")
        if APP_ICON is not None:
            self.setWindowIcon(APP_ICON)
        self.resize(900, 520)

        root = QVBoxLayout(self)

        top = QHBoxLayout()
        top.addWidget(QLabel("Zile inainte:"))
        self.spin_days = QSpinBox()
        self.spin_days.setRange(1, 365)
        self.spin_days.setValue(7)
        self.btn_refresh = QPushButton("Refresh")
        self.btn_export = QPushButton("Export CSV")
        apply_std_icon(self.btn_refresh, QStyle.StandardPixmap.SP_BrowserReload)
        apply_std_icon(self.btn_export, QStyle.StandardPixmap.SP_DialogSaveButton)
        top.addWidget(self.spin_days)
        top.addWidget(self.btn_refresh)
        top.addWidget(self.btn_export)

        top.addStretch(1)
        root.addLayout(top)

        self.tbl = QTableWidget(0, 6)
        self.tbl.setHorizontalHeaderLabels([
            "ID", "Nume", "Telefon", "Diagnostic",
            "Data control", "Status"
        ])
        self.tbl.setEditTriggers(QAbstractItemView.EditTrigger.NoEditTriggers)
        self.tbl.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
        self.tbl.setSelectionMode(QAbstractItemView.SelectionMode.SingleSelection)
        self.tbl.verticalHeader().setDefaultSectionSize(26)
        h = self.tbl.horizontalHeader()
        h.setSectionResizeMode(QHeaderView.ResizeMode.ResizeToContents)
        self.tbl.setColumnHidden(0, True)
        root.addWidget(self.tbl, 1)

        self.btn_refresh.clicked.connect(self.reload)
        self.btn_export.clicked.connect(self.export_csv)
        self.tbl.cellDoubleClicked.connect(self._open_patient_from_row)
        self.spin_days.valueChanged.connect(lambda _v: self.reload())

        self.reload()

    def reload(self):
        """Reincarca datele afisate in `PeriodicReportDialog`."""
        days = int(self.spin_days.value())
        rows = get_upcoming_controls(
            days_ahead=days,
        )
        self.tbl.setRowCount(len(rows))
        for i, r in enumerate(rows):
            self.tbl.setItem(i, 0, QTableWidgetItem(str(r.get("id", ""))))
            self.tbl.setItem(i, 1, QTableWidgetItem(r.get("nume_prenume") or ""))
            self.tbl.setItem(i, 2, QTableWidgetItem(r.get("telefon") or ""))
            self.tbl.setItem(i, 3, QTableWidgetItem(r.get("diagnostic_principal") or ""))
            self.tbl.setItem(i, 4, QTableWidgetItem(r.get("data_revenire_control") or ""))
            self.tbl.setItem(i, 5, QTableWidgetItem(r.get("status_follow_up") or ""))

    def export_csv(self):
        """Exporta CSV in `PeriodicReportDialog`."""
        dest, _ = QFileDialog.getSaveFileName(self, "Export CSV", "raport_periodic.csv", "CSV (*.csv)")
        if not dest:
            return
        try:
            with open(dest, "w", newline="", encoding="utf-8-sig") as f:
                w = csv.writer(f)
                w.writerow([
                    "Nume", "Telefon", "Diagnostic",
                    "Data control", "Status"
                ])
                for i in range(self.tbl.rowCount()):
                    w.writerow([
                        self.tbl.item(i, 1).text() if self.tbl.item(i, 1) else "",
                        self.tbl.item(i, 2).text() if self.tbl.item(i, 2) else "",
                        self.tbl.item(i, 3).text() if self.tbl.item(i, 3) else "",
                        self.tbl.item(i, 4).text() if self.tbl.item(i, 4) else "",
                        self.tbl.item(i, 5).text() if self.tbl.item(i, 5) else "",
                    ])
            log_action("export_csv", f"raport_periodic={dest}")
        except Exception as e:
            QMessageBox.critical(self, "Export CSV", f"Eroare:\n{e}")

    def _open_patient_from_row(self, row, _col):
        """Deschide patient from row in `PeriodicReportDialog`."""
        it = self.tbl.item(row, 0)
        if it and it.text().strip().isdigit():
            pid = int(it.text())
            open_patient_page_window(pid, owner=self)


# ============================================================
# UI: Advanced search
# ============================================================
class AdvancedSearchDialog(QDialog):
    def __init__(self, parent=None):
        """Initializeaza dialogul `AdvancedSearchDialog` si configureaza controalele interfetei."""
        super().__init__(parent)
        self.setWindowTitle("Cautare avansata")
        self.resize(980, 520)
        self.criteria = None

        root = QHBoxLayout(self)
        form = QFormLayout()

        self.ed_name = QLineEdit()
        self.ed_cnp = QLineEdit()
        self.ed_tel = QLineEdit()
        self.ed_email = QLineEdit()
        self.cmb_sex = QComboBox()
        self.cmb_sex.addItems(["", "Masculin", "Feminin"])
        self.sp_age_min = QSpinBox()
        self.sp_age_min.setRange(0, 120)
        self.sp_age_min.setSpecialValueText("")
        self.sp_age_max = QSpinBox()
        self.sp_age_max.setRange(0, 120)
        self.sp_age_max.setSpecialValueText("")
        self.ed_diag = QLineEdit()
        self.ed_diag2 = QLineEdit()
        self.ed_diag_liber = QLineEdit()
        self.dt_last_from = DatePicker("YYYY-MM-DD", show_today=False)
        self.dt_last_to = DatePicker("YYYY-MM-DD", show_today=False)

        form.addRow("Nume contine:", self.ed_name)
        form.addRow("CNP:", self.ed_cnp)
        form.addRow("Telefon:", self.ed_tel)
        form.addRow("Email:", self.ed_email)
        form.addRow("Sex:", wrap_selector_widget(self.cmb_sex, self))
        form.addRow("Varsta min:", wrap_selector_widget(self.sp_age_min, self))
        form.addRow("Varsta max:", wrap_selector_widget(self.sp_age_max, self))
        form.addRow("Diagnostic contine:", self.ed_diag)
        form.addRow("Diagnostic secundar contine:", self.ed_diag2)
        form.addRow("Diagnostic liber contine:", self.ed_diag_liber)
        form.addRow("Ultimul consult de la:", self.dt_last_from)
        form.addRow("Ultimul consult pana la:", self.dt_last_to)
        left = QVBoxLayout()
        left.addLayout(form)

        btn_row = QHBoxLayout()
        self.btn_search = QPushButton("Cauta")
        self.btn_search.setObjectName("primary")
        apply_std_icon(self.btn_search, QStyle.StandardPixmap.SP_DialogOkButton)
        self.btn_clear = QPushButton("Reseteaza")
        apply_std_icon(self.btn_clear, QStyle.StandardPixmap.SP_DialogResetButton)
        self.btn_close = QPushButton("Inchide")
        apply_std_icon(self.btn_close, QStyle.StandardPixmap.SP_DialogCancelButton)
        btn_row.addWidget(self.btn_search)
        btn_row.addWidget(self.btn_clear)
        btn_row.addStretch(1)
        btn_row.addWidget(self.btn_close)
        left.addLayout(btn_row)

        right = QVBoxLayout()
        self.lbl_results = QLabel("Rezultate: 0")
        right.addWidget(self.lbl_results)
        self.tbl_results = QTableWidget(0, 9)
        self.tbl_results.setHorizontalHeaderLabels(
            [
                "ID", "Nume", "CNP", "Telefon", "Email",
                "Diagnostic", "Diag secundar",
                "Diag liber",
                "Data control",
            ]
        )
        self.tbl_results.setEditTriggers(QAbstractItemView.EditTrigger.NoEditTriggers)
        self.tbl_results.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
        self.tbl_results.setSelectionMode(QAbstractItemView.SelectionMode.SingleSelection)
        self.tbl_results.setAlternatingRowColors(True)
        self.tbl_results.verticalHeader().setDefaultSectionSize(24)
        h = self.tbl_results.horizontalHeader()
        h.setSectionResizeMode(QHeaderView.ResizeMode.ResizeToContents)
        h.setStretchLastSection(True)
        self.tbl_results.setColumnHidden(0, True)
        right.addWidget(self.tbl_results, 1)

        root.addLayout(left, 0)
        root.addLayout(right, 1)

        self.btn_search.clicked.connect(self.run_search)
        self.btn_clear.clicked.connect(self.reset_form)
        self.btn_close.clicked.connect(self.reject)
        self.tbl_results.cellDoubleClicked.connect(self._open_patient_from_row)
        for ed in (self.ed_name, self.ed_cnp, self.ed_tel, self.ed_email, self.ed_diag, self.ed_diag2, self.ed_diag_liber):
            ed.returnPressed.connect(self.run_search)
        try:
            self.dt_last_from.edit.returnPressed.connect(self.run_search)
            self.dt_last_to.edit.returnPressed.connect(self.run_search)
        except Exception:
            pass
        apply_icd10_completer(self.ed_diag, multi=False)
        apply_icd10_completer(self.ed_diag2, multi=False)
        self.ed_diag_liber.setPlaceholderText("Text liber diagnostic")

    def _accept(self):
        """Valideaza datele introduse si confirma dialogul curent."""
        self.criteria = {
            "name": (self.ed_name.text() or "").strip(),
            "cnp": (self.ed_cnp.text() or "").strip(),
            "telefon": (self.ed_tel.text() or "").strip(),
            "email": (self.ed_email.text() or "").strip(),
            "sex": (self.cmb_sex.currentText() or "").strip(),
            "age_min": int(self.sp_age_min.value()) if self.sp_age_min.value() > 0 else None,
            "age_max": int(self.sp_age_max.value()) if self.sp_age_max.value() > 0 else None,
            "diag": (self.ed_diag.text() or "").strip(),
            "diag2": (self.ed_diag2.text() or "").strip(),
            "diag_liber": (self.ed_diag_liber.text() or "").strip(),
            "last_from": (self.dt_last_from.text() or "").strip(),
            "last_to": (self.dt_last_to.text() or "").strip(),
        }
        return self.criteria

    def reset_form(self):
        """Gestioneaza form in `AdvancedSearchDialog`."""
        self.ed_name.clear()
        self.ed_cnp.clear()
        self.ed_tel.clear()
        self.ed_email.clear()
        self.cmb_sex.setCurrentIndex(0)
        self.sp_age_min.setValue(0)
        self.sp_age_max.setValue(0)
        self.ed_diag.clear()
        self.ed_diag2.clear()
        self.ed_diag_liber.clear()
        self.dt_last_from.setText("")
        self.dt_last_to.setText("")
        self.tbl_results.setRowCount(0)
        self.lbl_results.setText("Rezultate: 0")

    def run_search(self):
        """Ruleaza search in `AdvancedSearchDialog`."""
        crit = self._accept()
        self.criteria = crit
        rows = filter_master_rows_advanced(crit)
        self.tbl_results.setRowCount(len(rows))
        hl = QBrush(QColor("#fff3cd"))
        name_q = (crit.get("name") or "").lower()
        cnp_q = (crit.get("cnp") or "").lower()
        tel_q = (crit.get("telefon") or "").lower()
        email_q = (crit.get("email") or "").lower()
        diag_q = (crit.get("diag") or "").lower()
        diag2_q = (crit.get("diag2") or "").lower()
        diag_liber_q = (crit.get("diag_liber") or "").lower()
        has_date_filter = bool((crit.get("last_from") or "").strip() or (crit.get("last_to") or "").strip())
        for i, r in enumerate(rows):
            it_id = QTableWidgetItem(str(r.get("id", "")))
            it_name = QTableWidgetItem(r.get("nume_prenume") or "")
            it_cnp = QTableWidgetItem(r.get("cnp") or "")
            it_tel = QTableWidgetItem(r.get("telefon") or "")
            it_email = QTableWidgetItem(r.get("email") or "")
            it_diag = QTableWidgetItem(r.get("ultim_diagnostic") or "")
            it_diag2 = QTableWidgetItem(r.get("diagnostic_secundar") or "")
            it_diag_liber = QTableWidgetItem(r.get("diagnostic_liber") or "")
            it_ctrl = QTableWidgetItem(r.get("data_revenire_control") or "")

            if name_q and name_q in (it_name.text() or "").lower():
                it_name.setBackground(hl)
            if cnp_q and cnp_q in (it_cnp.text() or "").lower():
                it_cnp.setBackground(hl)
            if tel_q and tel_q in (it_tel.text() or "").lower():
                it_tel.setBackground(hl)
            if email_q and email_q in (it_email.text() or "").lower():
                it_email.setBackground(hl)
            if diag_q and (
                diag_q in (it_diag.text() or "").lower()
                or diag_q in (it_diag_liber.text() or "").lower()
            ):
                it_diag.setBackground(hl)
                it_diag_liber.setBackground(hl)
            if diag2_q and diag2_q in (it_diag2.text() or "").lower():
                it_diag2.setBackground(hl)
            if diag_liber_q and diag_liber_q in (it_diag_liber.text() or "").lower():
                it_diag_liber.setBackground(hl)
            if has_date_filter:
                it_ctrl.setBackground(hl)

            self.tbl_results.setItem(i, 0, it_id)
            self.tbl_results.setItem(i, 1, it_name)
            self.tbl_results.setItem(i, 2, it_cnp)
            self.tbl_results.setItem(i, 3, it_tel)
            self.tbl_results.setItem(i, 4, it_email)
            self.tbl_results.setItem(i, 5, it_diag)
            self.tbl_results.setItem(i, 6, it_diag2)
            self.tbl_results.setItem(i, 7, it_diag_liber)
            self.tbl_results.setItem(i, 8, it_ctrl)
        self.lbl_results.setText(f"Rezultate: {len(rows)}")

    def _open_patient_from_row(self, row, _col):
        """Deschide patient from row in `AdvancedSearchDialog`."""
        it = self.tbl_results.item(row, 0)
        if it and it.text().strip().isdigit():
            pid = int(it.text())
            open_patient_page_window(pid, owner=self)


# ============================================================
# UI: Statistics
# ============================================================
class StatsDialog(QDialog):
    def __init__(self, parent=None):
        """Initializeaza dialogul `StatsDialog` si configureaza controalele interfetei."""
        super().__init__(parent)
        self.setWindowTitle("Statistici avansate")
        self.resize(980, 700)
        root = QVBoxLayout(self)

        self.lbl_summary = QLabel("")
        root.addWidget(self.lbl_summary)

        # chart controls
        chart_row = QHBoxLayout()
        chart_row.addWidget(QLabel("Grafic:"))
        self.cmb_chart = QComboBox()
        self.cmb_chart.addItems(["Top diagnostice", "Top diagnostice secundare", "Consulturi pe luni", "Sex"])
        self.btn_chart = QPushButton("Genereaza grafic")
        self.btn_export_chart = QPushButton("Exporta grafic")
        apply_std_icon(self.btn_chart, QStyle.StandardPixmap.SP_DialogApplyButton)
        apply_std_icon(self.btn_export_chart, QStyle.StandardPixmap.SP_DialogSaveButton)
        chart_row.addWidget(self.cmb_chart)
        chart_row.addWidget(self.btn_chart)
        chart_row.addWidget(self.btn_export_chart)
        chart_row.addStretch(1)
        root.addLayout(chart_row)

        # chart area
        self._chart_canvas = None
        self._chart_figure = None
        try:
            from matplotlib.backends.backend_qtagg import FigureCanvasQTAgg as FigureCanvas
            from matplotlib.figure import Figure
            self._chart_figure = Figure(figsize=(6, 3.2))
            self._chart_canvas = FigureCanvas(self._chart_figure)
            root.addWidget(self._chart_canvas, 1)
        except Exception:
            lbl = QLabel(matplotlib_missing_message())
            lbl.setStyleSheet("color: gray;")
            root.addWidget(lbl)

        self.tbl_diag = QTableWidget(0, 2)
        self.tbl_diag.setHorizontalHeaderLabels(["Diagnostic", "Count"])
        self.tbl_diag.setEditTriggers(QAbstractItemView.EditTrigger.NoEditTriggers)
        self.tbl_diag.verticalHeader().setDefaultSectionSize(26)
        h1 = self.tbl_diag.horizontalHeader()
        h1.setSectionResizeMode(QHeaderView.ResizeMode.ResizeToContents)

        self.tbl_diag2 = QTableWidget(0, 2)
        self.tbl_diag2.setHorizontalHeaderLabels(["Diagnostic secundar", "Count"])
        self.tbl_diag2.setEditTriggers(QAbstractItemView.EditTrigger.NoEditTriggers)
        self.tbl_diag2.verticalHeader().setDefaultSectionSize(26)
        h12 = self.tbl_diag2.horizontalHeader()
        h12.setSectionResizeMode(QHeaderView.ResizeMode.ResizeToContents)

        self.tbl_month = QTableWidget(0, 2)
        self.tbl_month.setHorizontalHeaderLabels(["Luna", "Consulturi"])
        self.tbl_month.setEditTriggers(QAbstractItemView.EditTrigger.NoEditTriggers)
        self.tbl_month.verticalHeader().setDefaultSectionSize(26)
        h2 = self.tbl_month.horizontalHeader()
        h2.setSectionResizeMode(QHeaderView.ResizeMode.ResizeToContents)

        root.addWidget(QLabel("Top diagnostice"))
        root.addWidget(self.tbl_diag, 1)
        root.addWidget(QLabel("Top diagnostice secundare"))
        root.addWidget(self.tbl_diag2, 1)
        root.addWidget(QLabel("Consulturi pe luni"))
        root.addWidget(self.tbl_month, 1)

        self.btn_chart.clicked.connect(self._draw_chart_selected)
        self.btn_export_chart.clicked.connect(self._export_chart)
        self.cmb_chart.currentIndexChanged.connect(lambda _i: self._draw_chart_selected())

        self.reload()

    def reload(self):
        """Reincarca datele afisate in `StatsDialog`."""
        conn = get_conn()
        cur = conn.cursor()
        cur.execute("SELECT COUNT(*) FROM pacienti_master")
        total_pat = cur.fetchone()[0]
        cur.execute("SELECT COUNT(*) FROM consulturi")
        total_cons = cur.fetchone()[0]
        cur.execute("SELECT AVG(varsta) FROM pacienti_master WHERE varsta IS NOT NULL")
        avg_age = cur.fetchone()[0] or 0
        cur.execute("SELECT sex, COUNT(*) FROM pacienti_master GROUP BY sex")
        sex_rows = cur.fetchall()

        cur.execute("""
            SELECT COALESCE(NULLIF(diagnostic_liber,''), diagnostic_principal) AS diagnostic_principal, COUNT(*) as cnt
            FROM consulturi
            WHERE COALESCE(NULLIF(diagnostic_liber,''), diagnostic_principal) IS NOT NULL
              AND TRIM(COALESCE(NULLIF(diagnostic_liber,''), diagnostic_principal)) <> ''
            GROUP BY COALESCE(NULLIF(diagnostic_liber,''), diagnostic_principal)
            ORDER BY cnt DESC
            LIMIT 10
        """)
        diag_rows = cur.fetchall()

        cur.execute("""
            SELECT diagnostic_secundar
            FROM consulturi
            WHERE diagnostic_secundar IS NOT NULL AND TRIM(diagnostic_secundar) <> ''
        """)
        diag2_raw = cur.fetchall()

        cur.execute("""
            SELECT substr(data_consultului,1,7) as ym, COUNT(*) as cnt
            FROM consulturi
            WHERE data_consultului IS NOT NULL AND LENGTH(data_consultului) >= 7
            GROUP BY ym
            ORDER BY ym DESC
            LIMIT 12
        """)
        month_rows = cur.fetchall()
        conn.close()

        sex_info = ", ".join([f"{r[0] or 'N/A'}: {r[1]}" for r in sex_rows]) or "N/A"
        self.lbl_summary.setText(
            f"Total pacienti: {total_pat}   |   Total consulturi: {total_cons}   |   Varsta medie: {avg_age:.1f}   |   Sex: {sex_info}"
        )

        self._stats_sex_rows = sex_rows
        self._stats_diag_rows = diag_rows
        diag2_counts: Dict[str, int] = {}
        for r in diag2_raw:
            txt = r[0] if isinstance(r, (list, tuple)) else None
            for tok in _split_icd10_tokens(txt):
                diag2_counts[tok] = diag2_counts.get(tok, 0) + 1
        diag2_rows = sorted(diag2_counts.items(), key=lambda x: (-x[1], x[0]))[:10]
        self._stats_diag2_rows = diag2_rows
        self._stats_month_rows = month_rows

        self.tbl_diag.setRowCount(len(diag_rows))
        for i, r in enumerate(diag_rows):
            self.tbl_diag.setItem(i, 0, QTableWidgetItem(r[0] or ""))
            self.tbl_diag.setItem(i, 1, QTableWidgetItem(str(r[1])))

        self.tbl_diag2.setRowCount(len(diag2_rows))
        for i, r in enumerate(diag2_rows):
            self.tbl_diag2.setItem(i, 0, QTableWidgetItem(r[0] or ""))
            self.tbl_diag2.setItem(i, 1, QTableWidgetItem(str(r[1])))

        self.tbl_month.setRowCount(len(month_rows))
        for i, r in enumerate(month_rows):
            self.tbl_month.setItem(i, 0, QTableWidgetItem(r[0] or ""))
            self.tbl_month.setItem(i, 1, QTableWidgetItem(str(r[1])))

        self._draw_chart_selected()

    def _draw_chart_selected(self):
        """Gestioneaza chart selected in `StatsDialog`."""
        if not self._chart_canvas or not self._chart_figure:
            return
        self._chart_figure.clear()
        ax = self._chart_figure.add_subplot(111)

        key = self.cmb_chart.currentText()
        if key == "Top diagnostice":
            labels = [r[0] or "" for r in (self._stats_diag_rows or [])]
            values = [r[1] for r in (self._stats_diag_rows or [])]
            ax.barh(labels, values)
            ax.set_title("Top diagnostice")
        elif key == "Top diagnostice secundare":
            labels = [r[0] or "" for r in (self._stats_diag2_rows or [])]
            values = [r[1] for r in (self._stats_diag2_rows or [])]
            ax.barh(labels, values)
            ax.set_title("Top diagnostice secundare")
        elif key == "Consulturi pe luni":
            labels = [r[0] or "" for r in (self._stats_month_rows or [])][::-1]
            values = [r[1] for r in (self._stats_month_rows or [])][::-1]
            ax.plot(labels, values, marker="o")
            ax.set_title("Consulturi pe luni")
            ax.tick_params(axis='x', rotation=45)
        else:
            labels = [r[0] or "N/A" for r in (self._stats_sex_rows or [])]
            values = [r[1] for r in (self._stats_sex_rows or [])]
            ax.pie(values, labels=labels, autopct="%1.0f%%")
            ax.set_title("Sex")

        try:
            with warnings.catch_warnings():
                warnings.simplefilter("ignore", UserWarning)
                self._chart_figure.tight_layout()
        except Exception:
            pass
        self._chart_canvas.draw()

    def _export_chart(self):
        """Exporta chart in `StatsDialog`."""
        if not self._chart_figure:
            return
        path, _ = QFileDialog.getSaveFileName(self, "Exporta grafic", str(APP_DIR / "statistica.png"), "PNG (*.png)")
        if not path:
            return
        try:
            self._chart_figure.savefig(path)
            QMessageBox.information(self, "OK", "Grafic exportat.")
        except Exception as e:
            QMessageBox.critical(self, "Eroare", str(e))


# ============================================================
# UI: Follow-up module
# ============================================================
class FollowUpDialog(QDialog):
    def __init__(self, parent=None):
        """Initializeaza dialogul `FollowUpDialog` si configureaza controalele interfetei."""
        super().__init__(parent)
        self.setWindowTitle("Modul follow-up")
        self.resize(900, 520)
        root = QVBoxLayout(self)

        top = QHBoxLayout()
        top.addWidget(QLabel("Status:"))
        self.cmb_status = QComboBox()
        self.cmb_status.addItems(["", "Programat", "Neprogramat"])
        top.addWidget(wrap_selector_widget(self.cmb_status, self))
        top.addWidget(QLabel("Zile inainte (0=toate):"))
        self.spin_days = QSpinBox()
        self.spin_days.setRange(0, 365)
        self.spin_days.setValue(0)
        top.addWidget(wrap_selector_widget(self.spin_days, self))
        self.btn_refresh = QPushButton("Refresh")
        apply_std_icon(self.btn_refresh, QStyle.StandardPixmap.SP_BrowserReload)
        top.addWidget(self.btn_refresh)
        top.addStretch(1)
        root.addLayout(top)

        self.tbl = QTableWidget(0, 6)
        self.tbl.setHorizontalHeaderLabels(["ID", "Nume", "Telefon", "Diagnostic", "Data control", "Status"])
        self.tbl.setEditTriggers(QAbstractItemView.EditTrigger.NoEditTriggers)
        self.tbl.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
        self.tbl.setSelectionMode(QAbstractItemView.SelectionMode.SingleSelection)
        self.tbl.verticalHeader().setDefaultSectionSize(26)
        h = self.tbl.horizontalHeader()
        h.setSectionResizeMode(QHeaderView.ResizeMode.ResizeToContents)
        self.tbl.setColumnHidden(0, True)
        root.addWidget(self.tbl, 1)

        self.btn_refresh.clicked.connect(self.reload)
        self.tbl.cellDoubleClicked.connect(self._open_patient_from_row)

        self.reload()

    def reload(self):
        """Reincarca datele afisate in `FollowUpDialog`."""
        status = (self.cmb_status.currentText() or "").strip()
        days = int(self.spin_days.value())
        rows = master_list_with_latest_consult("")

        out = []
        today = date.today()
        for r in rows:
            rd = dict(r)
            st = (rd.get("status_follow_up") or "").strip()
            if status and st != status:
                continue
            if days > 0:
                dctrl = (rd.get("data_revenire_control") or "").strip()
                if not dctrl:
                    continue
                try:
                    dval = datetime.strptime(dctrl, "%Y-%m-%d").date()
                except Exception:
                    continue
                if dval < today or dval > (today + timedelta(days=days)):
                    continue
            out.append(rd)

        self.tbl.setRowCount(len(out))
        for i, r in enumerate(out):
            self.tbl.setItem(i, 0, QTableWidgetItem(str(r.get("id", ""))))
            self.tbl.setItem(i, 1, QTableWidgetItem(r.get("nume_prenume") or ""))
            self.tbl.setItem(i, 2, QTableWidgetItem(r.get("telefon") or ""))
            self.tbl.setItem(i, 3, QTableWidgetItem(r.get("ultim_diagnostic") or ""))
            self.tbl.setItem(i, 4, QTableWidgetItem(r.get("data_revenire_control") or ""))
            self.tbl.setItem(i, 5, QTableWidgetItem(r.get("status_follow_up") or ""))

    def _open_patient_from_row(self, row, _col):
        """Deschide patient from row in `FollowUpDialog`."""
        it = self.tbl.item(row, 0)
        if it and it.text().strip().isdigit():
            pid = int(it.text())
            open_patient_page_window(pid, owner=self)


# ============================================================
# UI: Activity log
# ============================================================
class ActivityLogDialog(QDialog):
    def __init__(self, parent=None):
        """Initializeaza dialogul `ActivityLogDialog` si configureaza controalele interfetei."""
        super().__init__(parent)
        self.setWindowTitle("Log activitate")
        self.resize(980, 620)
        root = QVBoxLayout(self)
        tabs = QTabWidget(self)
        root.addWidget(tabs, 1)

        # Activity tab
        tab_activity = QWidget(self)
        tab_activity_root = QVBoxLayout(tab_activity)
        self.btn_refresh = QPushButton("Refresh")
        apply_std_icon(self.btn_refresh, QStyle.StandardPixmap.SP_BrowserReload)
        tab_activity_root.addWidget(self.btn_refresh)

        self.tbl = QTableWidget(0, 5)
        self.tbl.setHorizontalHeaderLabels(["Data", "Actiune", "Detalii", "User", "Rol"])
        self.tbl.setEditTriggers(QAbstractItemView.EditTrigger.NoEditTriggers)
        self.tbl.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
        self.tbl.setSelectionMode(QAbstractItemView.SelectionMode.SingleSelection)
        self.tbl.verticalHeader().setDefaultSectionSize(26)
        h = self.tbl.horizontalHeader()
        h.setSectionResizeMode(QHeaderView.ResizeMode.ResizeToContents)
        h.setSectionResizeMode(2, QHeaderView.ResizeMode.Stretch)
        tab_activity_root.addWidget(self.tbl, 1)
        tabs.addTab(tab_activity, "Activitate")

        # Entity audit tab
        tab_audit = QWidget(self)
        tab_audit_root = QVBoxLayout(tab_audit)

        flt_row = QHBoxLayout()
        self.cb_audit_table = QComboBox()
        self.cb_audit_table.addItem("Toate tabelele", "")
        self.cb_audit_table.addItem("Pacienti", "pacienti_master")
        self.cb_audit_table.addItem("Consulturi", "consulturi")
        self.cb_audit_table.addItem("Programari", "appointments")
        self.ed_audit_row_id = QLineEdit()
        self.ed_audit_row_id.setPlaceholderText("Filtru row_id (optional)")
        self.btn_refresh_audit = QPushButton("Refresh audit")
        self.btn_revert_audit = QPushButton("Revert selectie")
        apply_std_icon(self.btn_refresh_audit, QStyle.StandardPixmap.SP_BrowserReload)
        apply_std_icon(self.btn_revert_audit, QStyle.StandardPixmap.SP_BrowserReload)
        flt_row.addWidget(QLabel("Tabel:"))
        flt_row.addWidget(wrap_selector_widget(self.cb_audit_table, self))
        flt_row.addWidget(self.ed_audit_row_id)
        flt_row.addWidget(self.btn_refresh_audit)
        flt_row.addWidget(self.btn_revert_audit)
        flt_row.addStretch(1)
        tab_audit_root.addLayout(flt_row)

        self.tbl_audit = QTableWidget(0, 8)
        self.tbl_audit.setHorizontalHeaderLabels(["Audit ID", "Data", "Tabel", "Row ID", "Actiune", "User", "Rol", "Sursa"])
        self.tbl_audit.setEditTriggers(QAbstractItemView.EditTrigger.NoEditTriggers)
        self.tbl_audit.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
        self.tbl_audit.setSelectionMode(QAbstractItemView.SelectionMode.SingleSelection)
        self.tbl_audit.verticalHeader().setDefaultSectionSize(26)
        hh = self.tbl_audit.horizontalHeader()
        hh.setSectionResizeMode(QHeaderView.ResizeMode.ResizeToContents)
        hh.setSectionResizeMode(7, QHeaderView.ResizeMode.Stretch)
        tab_audit_root.addWidget(self.tbl_audit, 1)

        self.txt_audit_details = QTextEdit(self)
        self.txt_audit_details.setReadOnly(True)
        self.txt_audit_details.setPlaceholderText("Detalii before/after pentru intrarea selectata.")
        self.txt_audit_details.setMinimumHeight(170)
        tab_audit_root.addWidget(self.txt_audit_details)
        tabs.addTab(tab_audit, "Audit detaliat")

        self._audit_rows_cache: List[Dict[str, Any]] = []
        self.btn_refresh.clicked.connect(self.reload_activity)
        self.btn_refresh_audit.clicked.connect(self.reload_audit)
        self.btn_revert_audit.clicked.connect(self.revert_selected_audit)
        self.cb_audit_table.currentIndexChanged.connect(self.reload_audit)
        self.ed_audit_row_id.returnPressed.connect(self.reload_audit)
        self.tbl_audit.itemSelectionChanged.connect(self._on_audit_selection_changed)

        self.reload_activity()
        self.reload_audit()

    def reload_activity(self):
        """Reincarca activity in `ActivityLogDialog`."""
        rows = get_activity_log(limit=500)
        self.tbl.setRowCount(len(rows))
        for i, r in enumerate(rows):
            self.tbl.setItem(i, 0, QTableWidgetItem(r.get("ts") or ""))
            self.tbl.setItem(i, 1, QTableWidgetItem(r.get("action") or ""))
            self.tbl.setItem(i, 2, QTableWidgetItem(r.get("details") or ""))
            self.tbl.setItem(i, 3, QTableWidgetItem(r.get("user") or ""))
            self.tbl.setItem(i, 4, QTableWidgetItem(r.get("role") or ""))

    def _audit_selected_id(self) -> Optional[int]:
        """Gestioneaza selected ID in `ActivityLogDialog`."""
        row = self.tbl_audit.currentRow()
        if row < 0:
            return None
        it = self.tbl_audit.item(row, 0)
        if not it:
            return None
        txt = (it.text() or "").strip()
        if not txt.isdigit():
            return None
        return int(txt)

    def _on_audit_selection_changed(self):
        """Gestioneaza evenimentul audit selection changed in `ActivityLogDialog`."""
        aid = self._audit_selected_id()
        if aid is None:
            self.txt_audit_details.clear()
            return
        rr = None
        for r in self._audit_rows_cache:
            if int(r.get("id") or 0) == aid:
                rr = r
                break
        if rr is None:
            self.txt_audit_details.clear()
            return

        before_payload = _safe_json_load_obj(rr.get("before_json"))
        after_payload = _safe_json_load_obj(rr.get("after_json"))
        lines: List[str] = []
        lines.append(f"Audit ID: {aid}")
        lines.append(f"Actiune: {rr.get('action') or '-'}")
        lines.append(f"Tabel: {rr.get('table_name') or '-'} | Row ID: {rr.get('row_id') or '-'}")
        lines.append("")
        lines.append("Before:")
        lines.append(json.dumps(before_payload, ensure_ascii=False, indent=2) if before_payload else "(gol)")
        lines.append("")
        lines.append("After:")
        lines.append(json.dumps(after_payload, ensure_ascii=False, indent=2) if after_payload else "(gol)")
        self.txt_audit_details.setPlainText("\n".join(lines))

    def reload_audit(self):
        """Reincarca audit in `ActivityLogDialog`."""
        table_name = (self.cb_audit_table.currentData() or "").strip()
        row_id_txt = (self.ed_audit_row_id.text() or "").strip()
        row_id: Optional[int] = None
        if row_id_txt:
            if not row_id_txt.isdigit():
                QMessageBox.warning(self, "Audit", "Filtrul row_id trebuie sa fie numeric.")
                return
            row_id = int(row_id_txt)
        rows = get_entity_audit_rows(limit=1000, table_name=table_name, row_id=row_id)
        self._audit_rows_cache = rows
        self.tbl_audit.setRowCount(len(rows))
        for i, r in enumerate(rows):
            self.tbl_audit.setItem(i, 0, QTableWidgetItem(str(r.get("id") or "")))
            self.tbl_audit.setItem(i, 1, QTableWidgetItem(str(r.get("ts") or "")))
            self.tbl_audit.setItem(i, 2, QTableWidgetItem(str(r.get("table_name") or "")))
            self.tbl_audit.setItem(i, 3, QTableWidgetItem(str(r.get("row_id") or "")))
            self.tbl_audit.setItem(i, 4, QTableWidgetItem(str(r.get("action") or "")))
            self.tbl_audit.setItem(i, 5, QTableWidgetItem(str(r.get("source_user") or "")))
            self.tbl_audit.setItem(i, 6, QTableWidgetItem(str(r.get("source_role") or "")))
            self.tbl_audit.setItem(i, 7, QTableWidgetItem(str(r.get("source_action") or "")))
        if len(rows) > 0:
            self.tbl_audit.selectRow(0)
            self._on_audit_selection_changed()
        else:
            self.txt_audit_details.clear()

    def revert_selected_audit(self):
        """Gestioneaza selected audit in `ActivityLogDialog`."""
        aid = self._audit_selected_id()
        if aid is None:
            QMessageBox.information(self, "Audit", "Selecteaza o intrare audit pentru revert.")
            return
        if QMessageBox.question(
            self,
            "Confirmare revert",
            "Aplic revert pe intrarea audit selectata?",
            QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
            QMessageBox.StandardButton.No,
        ) != QMessageBox.StandardButton.Yes:
            return
        try:
            res = revert_entity_audit_entry(int(aid))
            QMessageBox.information(
                self,
                "Audit",
                f"Revert aplicat.\nTabel: {res.get('table_name')}\nRow ID: {res.get('row_id')}",
            )
            try:
                log_action(
                    "audit_revert",
                    json.dumps(
                        {
                            "audit_id": int(aid),
                            "table": res.get("table_name"),
                            "row_id": res.get("row_id"),
                            "revert_action": res.get("revert_action"),
                        },
                        ensure_ascii=False,
                    ),
                )
            except Exception:
                pass
            self.reload_activity()
            self.reload_audit()
        except Exception as e:
            QMessageBox.critical(self, "Audit", f"Revert esuat:\n{e}")


# ============================================================
# UI: Import table mapping
# ============================================================
class ImportMapDialog(QDialog):
    def __init__(self, columns: List[str], parent=None):
        """Initializeaza dialogul `ImportMapDialog` si configureaza controalele interfetei."""
        super().__init__(parent)
        self.setWindowTitle("Import tabel - mapare coloane")
        self.resize(740, 640)
        self.mapping = None

        root = QVBoxLayout(self)
        form = QFormLayout()

        self._combos = {}
        def add_row(label, key):
            """Adauga row in `ImportMapDialog`, ca helper intern in `__init__`."""
            cb = QComboBox()
            cb.addItem("", "")
            for c in columns:
                cb.addItem(str(c), str(c))
            self._combos[key] = cb
            form.addRow(label, wrap_selector_widget(cb, self))

        # Master fields
        add_row("Nume si prenume", "nume_prenume")
        add_row("CNP", "cnp")
        add_row("Telefon", "telefon")
        add_row("Domiciliu", "domiciliu")
        add_row("Data nasterii", "data_nasterii")
        add_row("Sex", "sex")
        add_row("Varsta", "varsta")

        # Consult fields
        add_row("Data consultului", "data_consultului")
        add_row("Medic", "medic")
        add_row("Diagnostic principal", "diagnostic_principal")
        add_row("Diagnostic secundar", "diagnostic_secundar")
        add_row("Diagnostic liber", "diagnostic_liber")
        add_row("Observatii", "observatii")
        add_row("Status follow-up", "status_follow_up")
        add_row("Data revenire control", "data_revenire_control")
        add_row("Interval luni revenire", "interval_luni_revenire")
        add_row("Recomandare fizio-kinetoterapie", "recomandare_fizio_kineto")
        add_row("Status fizioterapie", "a_inceput_fizio")

        root.addLayout(form)

        btns = QDialogButtonBox(QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel)
        try:
            ok_btn = btns.button(QDialogButtonBox.StandardButton.Ok)
            if ok_btn:
                ok_btn.setText("Importa")
                apply_std_icon(ok_btn, QStyle.StandardPixmap.SP_DialogOkButton)
            cancel_btn = btns.button(QDialogButtonBox.StandardButton.Cancel)
            if cancel_btn:
                apply_std_icon(cancel_btn, QStyle.StandardPixmap.SP_DialogCancelButton)
        except Exception:
            pass
        btns.accepted.connect(self._accept)
        btns.rejected.connect(self.reject)
        root.addWidget(btns)

    def _accept(self):
        """Valideaza datele introduse si confirma dialogul curent."""
        self.mapping = {k: (cb.currentData() or "") for k, cb in self._combos.items()}
        self.accept()


class DatabaseCleanupDialog(QDialog):
    def __init__(self, parent=None):
        """Initializeaza dialogul `DatabaseCleanupDialog` si configureaza controalele interfetei."""
        super().__init__(parent)
        self.setWindowTitle("Curatare baza de date")
        self.resize(620, 520)
        self.selected_segments: List[str] = []
        self.include_system = False

        root = QVBoxLayout(self)

        info = QLabel(
            "Alege ce date vrei sa stergi.\n"
            "Datele se muta in Recycle Bin si pot fi restaurate ulterior (se face si backup automat inainte)."
        )
        info.setWordWrap(True)
        root.addWidget(info)

        self.cb_all = QCheckBox("Golire completa a datelor (toate segmentele)")
        root.addWidget(self.cb_all)

        self._segment_checks: Dict[str, QCheckBox] = {}
        for seg_key, seg_label, _tables in DB_CLEANUP_SEGMENTS:
            cb = QCheckBox(seg_label)
            self._segment_checks[seg_key] = cb
            root.addWidget(cb)

        self.cb_include_system = QCheckBox("Include utilizatori + setari aplicatie (reset aproape complet)")
        root.addWidget(self.cb_include_system)

        self.cb_all.toggled.connect(self._on_all_toggled)

        btns = QDialogButtonBox(QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel)
        try:
            ok_btn = btns.button(QDialogButtonBox.StandardButton.Ok)
            if ok_btn:
                ok_btn.setText("Sterge")
                apply_std_icon(ok_btn, QStyle.StandardPixmap.SP_TrashIcon)
            cancel_btn = btns.button(QDialogButtonBox.StandardButton.Cancel)
            if cancel_btn:
                apply_std_icon(cancel_btn, QStyle.StandardPixmap.SP_DialogCancelButton)
        except Exception:
            pass
        btns.accepted.connect(self._accept)
        btns.rejected.connect(self.reject)
        root.addWidget(btns)

    def _on_all_toggled(self, checked: bool):
        """Gestioneaza evenimentul all toggled in `DatabaseCleanupDialog`."""
        for cb in self._segment_checks.values():
            cb.setEnabled(not checked)
            if checked:
                cb.setChecked(False)

    def _accept(self):
        """Valideaza datele introduse si confirma dialogul curent."""
        selected = []
        if self.cb_all.isChecked():
            selected.append("all")
        else:
            for seg_key, cb in self._segment_checks.items():
                if cb.isChecked():
                    selected.append(seg_key)

        if not selected and not self.cb_include_system.isChecked():
            QMessageBox.warning(self, "Curatare", "Selecteaza cel putin un segment.")
            return

        self.selected_segments = selected
        self.include_system = bool(self.cb_include_system.isChecked())
        self.accept()


class RecycleBinDialog(QDialog):
    def __init__(self, parent=None):
        """Initializeaza dialogul `RecycleBinDialog` si configureaza controalele interfetei."""
        super().__init__(parent)
        self.setWindowTitle("Recycle Bin - restaurare date")
        self.resize(900, 560)
        self.selected_snapshot_id: Optional[int] = None

        root = QVBoxLayout(self)
        info = QLabel(
            "Aici gasesti snapshot-urile create automat inainte de curatarea bazei de date. "
            "Selecteaza unul si apasa Restaurare sau selecteaza mai multe pentru stergere definitiva."
        )
        info.setWordWrap(True)
        root.addWidget(info)

        self.table = QTableWidget(0, 6)
        self.table.setHorizontalHeaderLabels(["ID", "Data", "Actiune", "Randuri", "Segmente", "Status"])
        self.table.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
        self.table.setSelectionMode(QAbstractItemView.SelectionMode.ExtendedSelection)
        self.table.setEditTriggers(QAbstractItemView.EditTrigger.NoEditTriggers)
        self.table.setAlternatingRowColors(True)
        self.table.verticalHeader().setVisible(False)
        self.table.horizontalHeader().setStretchLastSection(True)
        self.table.horizontalHeader().setSectionResizeMode(QHeaderView.ResizeMode.Interactive)
        self.table.horizontalHeader().setSectionResizeMode(1, QHeaderView.ResizeMode.ResizeToContents)
        self.table.horizontalHeader().setSectionResizeMode(3, QHeaderView.ResizeMode.ResizeToContents)
        root.addWidget(self.table, 1)

        btn_row = QHBoxLayout()
        self.btn_refresh = QPushButton("Refresh")
        self.btn_restore = QPushButton("Restaurare snapshot selectat")
        self.btn_delete = QPushButton("Sterge definitiv din Recycle Bin")
        self.btn_close = QPushButton("Inchide")
        apply_std_icon(self.btn_refresh, QStyle.StandardPixmap.SP_BrowserReload)
        apply_std_icon(self.btn_restore, QStyle.StandardPixmap.SP_DialogApplyButton)
        apply_std_icon(self.btn_delete, QStyle.StandardPixmap.SP_TrashIcon)
        apply_std_icon(self.btn_close, QStyle.StandardPixmap.SP_DialogCloseButton)
        btn_row.addWidget(self.btn_refresh)
        btn_row.addStretch(1)
        btn_row.addWidget(self.btn_restore)
        btn_row.addWidget(self.btn_delete)
        btn_row.addWidget(self.btn_close)
        root.addLayout(btn_row)

        self.btn_refresh.clicked.connect(self.reload_data)
        self.btn_restore.clicked.connect(self._accept_restore)
        self.btn_delete.clicked.connect(self._delete_selected)
        self.btn_close.clicked.connect(self.reject)
        self.reload_data()

    def _segments_text(self, raw: Any) -> str:
        """Gestioneaza text in `RecycleBinDialog`."""
        try:
            val = json.loads(raw) if isinstance(raw, str) else raw
            if isinstance(val, list):
                if not val:
                    return "-"
                if "all" in val:
                    return "all"
                return ", ".join(str(x) for x in val)
        except Exception:
            pass
        return str(raw or "-")

    def reload_data(self):
        """Reincarca data in `RecycleBinDialog`."""
        rows = list_recycle_snapshots(500)
        self.table.setRowCount(0)
        for r in rows:
            row_idx = self.table.rowCount()
            self.table.insertRow(row_idx)
            status = "Restaurat" if r.get("restored_at") else "Disponibil"
            values = [
                str(r.get("id") or ""),
                str(r.get("created_at") or ""),
                str(r.get("action") or "cleanup"),
                str(r.get("total_rows") if r.get("total_rows") is not None else r.get("item_count") or 0),
                self._segments_text(r.get("segment_keys")),
                status,
            ]
            for col_idx, val in enumerate(values):
                self.table.setItem(row_idx, col_idx, QTableWidgetItem(val))
        if self.table.rowCount() > 0:
            self.table.selectRow(0)

    def _selected_snapshot_id(self) -> Optional[int]:
        """Gestioneaza snapshot ID in `RecycleBinDialog`."""
        ids = self._selected_snapshot_ids()
        if not ids:
            return None
        return int(ids[0])

    def _selected_snapshot_ids(self) -> List[int]:
        """Gestioneaza snapshot ID-uri in `RecycleBinDialog`."""
        rows = sorted(set(i.row() for i in self.table.selectedIndexes()))
        out: List[int] = []
        for row in rows:
            it = self.table.item(row, 0)
            if not it:
                continue
            txt = (it.text() or "").strip()
            if txt.isdigit():
                out.append(int(txt))
        return out

    def _accept_restore(self):
        """Gestioneaza restore in `RecycleBinDialog`."""
        sid = self._selected_snapshot_id()
        if not sid:
            QMessageBox.warning(self, "Recycle Bin", "Selecteaza un snapshot pentru restaurare.")
            return
        self.selected_snapshot_id = int(sid)
        self.accept()

    def _delete_selected(self):
        """Sterge selected in `RecycleBinDialog`."""
        ids = self._selected_snapshot_ids()
        if not ids:
            QMessageBox.warning(self, "Recycle Bin", "Selecteaza cel putin un snapshot pentru stergere definitiva.")
            return

        total_rows = 0
        for sid in ids:
            try:
                total_rows += int(sum(get_recycle_snapshot_table_counts(int(sid)).values()))
            except Exception:
                pass

        msg = (
            f"Urmeaza sa stergi definitiv {len(ids)} snapshot(uri) din Recycle Bin.\n"
            f"Randuri arhivate afectate (estimare): {total_rows}\n\n"
            "Aceasta actiune este ireversibila. Continui?"
        )
        if QMessageBox.question(
            self,
            "Confirmare stergere definitiva",
            msg,
            QMessageBox.StandardButton.Ok | QMessageBox.StandardButton.Cancel,
            QMessageBox.StandardButton.Cancel,
        ) != QMessageBox.StandardButton.Ok:
            return

        try:
            result = delete_recycle_snapshots(ids)
            try:
                log_action(
                    "recycle_bin_delete_permanent",
                    json.dumps(
                        {
                            "snapshot_ids": ids,
                            "deleted_snapshots": int(result.get("snapshots", 0)),
                            "deleted_items": int(result.get("items", 0)),
                        },
                        ensure_ascii=False,
                    ),
                )
            except Exception:
                pass
            self.reload_data()
            QMessageBox.information(
                self,
                "Recycle Bin",
                f"Stergere definitiva finalizata.\nSnapshot-uri sterse: {int(result.get('snapshots', 0))}\n"
                f"Randuri arhivate sterse: {int(result.get('items', 0))}",
            )
        except Exception as e:
            QMessageBox.critical(self, "Recycle Bin", f"Eroare la stergerea definitiva:\n{e}")


# ============================================================
# UI: Generic CRUD
# ============================================================
class RecordEditDialog(QDialog):
    def __init__(self, title: str, fields: List[Dict[str, Any]], data: Optional[Dict[str, Any]] = None, parent=None):
        """Initializeaza dialogul `RecordEditDialog` si configureaza controalele interfetei."""
        super().__init__(parent)
        self.setWindowTitle(title)
        self.setModal(True)
        self.resize(620, 420)
        self._fields = fields
        self._widgets: Dict[str, QWidget] = {}
        self._auto_signed_by_doctor = ""

        root = QVBoxLayout(self)
        form = QFormLayout()

        for f in self._fields:
            key = f["key"]
            label = f.get("label", key)
            ftype = f.get("type", "text")
            row_widget: QWidget

            if ftype == "date":
                w = DatePicker("YYYY-MM-DD", show_today=False)
                self._widgets[key] = w
                row_widget = w
                form.addRow(label, row_widget)

            elif ftype == "choice":
                w = QComboBox()
                w.addItem("")
                for c in f.get("choices", []):
                    w.addItem(str(c))
                self._widgets[key] = w
                if key in {"recomandare_fizio_kineto", "a_inceput_fizio"}:
                    row_widget = w
                else:
                    row_widget = wrap_selector_widget(w, self)
                form.addRow(label, row_widget)

            elif ftype == "bool":
                w = QComboBox()
                w.addItems(["", "Da", "Nu"])
                self._widgets[key] = w
                if key in {"recomandare_fizio_kineto", "a_inceput_fizio"}:
                    row_widget = w
                else:
                    row_widget = wrap_selector_widget(w, self)
                form.addRow(label, row_widget)

            elif ftype == "multiline":
                w = QTextEdit()
                w.setFixedHeight(90)
                self._widgets[key] = w
                row_widget = w
                form.addRow(label, row_widget)

            elif ftype == "file":
                row = QWidget()
                row_l = QHBoxLayout(row)
                row_l.setContentsMargins(0, 0, 0, 0)
                row_l.setSpacing(8)
                le = QLineEdit()
                btn = QPushButton("Alege")
                btn.setObjectName("secondary")
                btn.setMinimumWidth(84)
                apply_std_icon(btn, QStyle.StandardPixmap.SP_DialogOpenButton)
                row_l.addWidget(le, 1)
                row_l.addWidget(btn)

                def _browse(le_ref=le):
                    """Gestioneaza operatia `_browse` in `RecordEditDialog`."""
                    path, _ = QFileDialog.getOpenFileName(self, "Alege fisier")
                    if path:
                        le_ref.setText(path)

                btn.clicked.connect(_browse)
                self._widgets[key] = le
                form.addRow(label, row)

            else:
                w = QLineEdit()
                self._widgets[key] = w
                row_widget = w
                form.addRow(label, row_widget)

        root.addLayout(form)

        btns = QDialogButtonBox(QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel)
        try:
            ok_btn = btns.button(QDialogButtonBox.StandardButton.Ok)
            if ok_btn:
                apply_std_icon(ok_btn, QStyle.StandardPixmap.SP_DialogOkButton)
            cancel_btn = btns.button(QDialogButtonBox.StandardButton.Cancel)
            if cancel_btn:
                apply_std_icon(cancel_btn, QStyle.StandardPixmap.SP_DialogCancelButton)
        except Exception:
            pass
        btns.accepted.connect(self.accept)
        btns.rejected.connect(self.reject)
        root.addWidget(btns)

        self._connect_doctor_signed_by_sync()

        if data:
            self.set_data(data)
        self._sync_signed_by_from_doctor(force=True)

    def _get_widget_text(self, key: str) -> str:
        """Returneaza widget text in `RecordEditDialog`."""
        w = self._widgets.get(key)
        if isinstance(w, QComboBox):
            return (w.currentText() or "").strip()
        if isinstance(w, QLineEdit):
            return (w.text() or "").strip()
        return ""

    def _set_widget_text(self, key: str, value: str):
        """Seteaza widget text in `RecordEditDialog`."""
        w = self._widgets.get(key)
        val = (value or "").strip()
        if isinstance(w, QComboBox):
            if not val:
                w.setCurrentIndex(0)
                return
            idx = w.findText(val)
            if idx < 0:
                w.addItem(val)
                idx = w.findText(val)
            if idx >= 0:
                w.setCurrentIndex(idx)
            return
        if isinstance(w, QLineEdit):
            w.setText(val)

    def _connect_doctor_signed_by_sync(self):
        """Gestioneaza doctor signed by sync in `RecordEditDialog`."""
        w_doctor = self._widgets.get("doctor")
        if isinstance(w_doctor, QComboBox) and "signed_by" in self._widgets:
            try:
                w_doctor.currentTextChanged.connect(self._sync_signed_by_from_doctor)
            except Exception:
                pass

    def _sync_signed_by_from_doctor(self, _=None, force: bool = False):
        """Sincronizeaza signed by from doctor in `RecordEditDialog`."""
        if "doctor" not in self._widgets or "signed_by" not in self._widgets:
            return
        doctor_name = self._get_widget_text("doctor")
        current_signed = self._get_widget_text("signed_by")
        if force or (not current_signed) or (current_signed == self._auto_signed_by_doctor):
            self._set_widget_text("signed_by", doctor_name)
            self._auto_signed_by_doctor = doctor_name

    def set_data(self, data: Dict[str, Any]):
        """Seteaza data in `RecordEditDialog`."""
        for f in self._fields:
            key = f["key"]
            ftype = f.get("type", "text")
            w = self._widgets.get(key)
            v = data.get(key)
            if w is None:
                continue
            if ftype == "multiline":
                w.setPlainText("" if v is None else str(v))
            elif ftype == "choice":
                if v:
                    idx = w.findText(str(v))
                    if idx < 0:
                        w.addItem(str(v))
                        idx = w.findText(str(v))
                    w.setCurrentIndex(idx if idx >= 0 else 0)
                else:
                    w.setCurrentIndex(0)
            elif ftype == "bool":
                if v in (1, "1", True, "Da", "DA", "da"):
                    w.setCurrentIndex(1)
                elif v in (0, "0", False, "Nu", "NU", "nu"):
                    w.setCurrentIndex(2)
                else:
                    w.setCurrentIndex(0)
            elif ftype == "date":
                w.setText("" if v is None else str(v))
            else:
                w.setText("" if v is None else str(v))

    def get_payload(self) -> Optional[Dict[str, Any]]:
        """Returneaza payload in `RecordEditDialog`."""
        payload: Dict[str, Any] = {}
        for f in self._fields:
            key = f["key"]
            ftype = f.get("type", "text")
            w = self._widgets.get(key)
            if w is None:
                continue
            if ftype == "multiline":
                val = w.toPlainText().strip()
            elif ftype == "choice":
                val = w.currentText().strip()
            elif ftype == "bool":
                t = w.currentText().strip()
                if t == "Da":
                    val = 1
                elif t == "Nu":
                    val = 0
                else:
                    val = None
            elif ftype == "date":
                val = w.text().strip()
                if val and not _validate_date_for_key(key, val):
                    QMessageBox.warning(self, "Data invalida", f"Data invalida pentru {f.get('label', key)}")
                    return None
            else:
                val = w.text().strip()

            if val == "":
                val = None
            if ftype == "int" and val is not None:
                try:
                    val = int(val)
                except Exception:
                    QMessageBox.warning(self, "Valoare invalida", f"Numar invalid pentru {f.get('label', key)}")
                    return None
            if ftype == "float" and val is not None:
                try:
                    val = float(val)
                except Exception:
                    QMessageBox.warning(self, "Valoare invalida", f"Numar invalid pentru {f.get('label', key)}")
                    return None

            payload[key] = val
        return payload


# ============================================================
# UI: Template dialog
# ============================================================
class TemplateDialog(QDialog):
    def __init__(
        self,
        title: str,
        templates: List[Dict[str, Any]],
        master: Dict[str, Any],
        last_consult: Optional[Dict[str, Any]] = None,
        include_letter_type: bool = False,
        parent=None,
    ):
        """Initializeaza dialogul `TemplateDialog` si configureaza controalele interfetei."""
        super().__init__(parent)
        self.setWindowTitle(title)
        self.setModal(True)
        self.resize(720, 600)

        self.templates = templates or []
        self.master = master or {}
        self.last_consult = last_consult or {}
        self._auto_signed_by_medic = ""

        root = QVBoxLayout(self)
        form = QFormLayout()

        self.cb_tpl = QComboBox()
        for t in self.templates:
            self.cb_tpl.addItem(t.get("name", "Template"))
        form.addRow("Sablon:", self.cb_tpl)

        self.ed_date = DatePicker("YYYY-MM-DD", show_today=True)
        self.ed_medic = QComboBox()
        self.ed_medic.addItem("")
        for medic_name in get_medic_dropdown_values():
            self.ed_medic.addItem(medic_name)
        form.addRow("Data:", self.ed_date)
        form.addRow("Medic:", wrap_selector_widget(self.ed_medic, self))

        self.ed_diag = QLineEdit()
        self.ed_diag.setPlaceholderText("Diagnostic (optional)")
        apply_icd10_completer(self.ed_diag)
        form.addRow("Diagnostic:", self.ed_diag)

        self.ed_obs = QTextEdit()
        self.ed_obs.setFixedHeight(80)
        form.addRow("Observatii:", self.ed_obs)

        self.ed_signed_by = QLineEdit()
        self.ed_signature_path = QLineEdit()
        btn_sig = QPushButton("Alege")
        btn_sig.setObjectName("secondary")
        btn_sig.setMinimumWidth(84)
        apply_std_icon(btn_sig, QStyle.StandardPixmap.SP_DialogOpenButton)
        sig_row = QWidget()
        sig_l = QHBoxLayout(sig_row)
        sig_l.setContentsMargins(0, 0, 0, 0)
        sig_l.setSpacing(8)
        sig_l.addWidget(self.ed_signature_path, 1)
        sig_l.addWidget(btn_sig)
        form.addRow("Semnat de:", self.ed_signed_by)
        form.addRow("Semnatura (fisier):", sig_row)

        def _browse_sig():
            """Gestioneaza sig in `TemplateDialog`, ca helper intern in `__init__`."""
            path, _ = QFileDialog.getOpenFileName(self, "Alege fisier semnatura")
            if path:
                self.ed_signature_path.setText(path)

        btn_sig.clicked.connect(_browse_sig)

        self.cb_letter_type = None
        if include_letter_type:
            self.cb_letter_type = QComboBox()
            self.cb_letter_type.addItems(["Scrisoare medicala", "Adeverinta", "Bilet externare"])
            form.addRow("Tip scrisoare:", self.cb_letter_type)

        root.addLayout(form)

        self.txt_content = QTextEdit()
        self.txt_content.setPlaceholderText("Continut generat din sablon...")
        root.addWidget(self.txt_content, 1)

        btn_row = QHBoxLayout()
        self.btn_gen = QPushButton("Genereaza din sablon")
        apply_std_icon(self.btn_gen, QStyle.StandardPixmap.SP_DialogApplyButton)
        btn_row.addWidget(self.btn_gen)
        btn_row.addStretch(1)
        root.addLayout(btn_row)

        btns = QDialogButtonBox(QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel)
        btns.accepted.connect(self.accept)
        btns.rejected.connect(self.reject)
        root.addWidget(btns)

        # defaults
        self.ed_date.setText(datetime.now().strftime("%Y-%m-%d"))
        if self.last_consult:
            diag_default = (
                (self.last_consult.get("diagnostic_liber") or "").strip()
                or (self.last_consult.get("diagnostic_principal") or "").strip()
            )
            self.ed_diag.setText(diag_default)
            if not self._get_medic_value():
                self._set_medic_value(self.last_consult.get("medic") or "")
        self._sync_signed_by_from_medic(force=True)

        self.cb_tpl.currentIndexChanged.connect(self.generate)
        self.btn_gen.clicked.connect(self.generate)
        self.ed_medic.currentTextChanged.connect(self._sync_signed_by_from_medic)
        self.generate()

    def _build_data(self) -> Dict[str, Any]:
        """Construieste data in `TemplateDialog`."""
        data = dict(self.master or {})
        data.update({
            "data": self.ed_date.text().strip(),
            "medic": self._get_medic_value(),
            "diagnostic": self.ed_diag.text().strip(),
            "observatii": self.ed_obs.toPlainText().strip(),
        })
        return data

    def _get_medic_value(self) -> str:
        """Returneaza medic value in `TemplateDialog`."""
        return (self.ed_medic.currentText() or "").strip()

    def _set_medic_value(self, value: str):
        """Seteaza medic value in `TemplateDialog`."""
        val = (value or "").strip()
        if not val:
            self.ed_medic.setCurrentIndex(0)
            return
        idx = self.ed_medic.findText(val)
        if idx < 0:
            self.ed_medic.addItem(val)
            idx = self.ed_medic.findText(val)
        if idx >= 0:
            self.ed_medic.setCurrentIndex(idx)

    def _sync_signed_by_from_medic(self, _=None, force: bool = False):
        """Sincronizeaza signed by from medic in `TemplateDialog`."""
        medic_name = self._get_medic_value()
        current_signed_by = (self.ed_signed_by.text() or "").strip()
        if force or (not current_signed_by) or (current_signed_by == self._auto_signed_by_medic):
            self.ed_signed_by.setText(medic_name)
            self._auto_signed_by_medic = medic_name

    def generate(self):
        """Gestioneaza operatia `generate` in `TemplateDialog`."""
        idx = self.cb_tpl.currentIndex()
        tpl = self.templates[idx] if 0 <= idx < len(self.templates) else {}
        body = tpl.get("body", "")
        content = render_template_text(body, self._build_data())
        self.txt_content.setPlainText(content)

    def get_payload(self) -> Dict[str, Any]:
        """Returneaza payload in `TemplateDialog`."""
        template_name = self.cb_tpl.currentText().strip()
        payload = {
            "template_name": template_name,
            "content": self.txt_content.toPlainText().strip(),
            "doctor": self._get_medic_value(),
            "date": self.ed_date.text().strip(),
            "signed_by": self.ed_signed_by.text().strip(),
            "signature_path": self.ed_signature_path.text().strip(),
            "signed_at": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
        }
        if self.cb_letter_type:
            payload["letter_type"] = self.cb_letter_type.currentText().strip()
        return payload


class SimpleCrudWidget(QWidget):
    def __init__(
        self,
        title: str,
        table_name: str,
        display_cols: List[Tuple[str, str]],
        fields: List[Dict[str, Any]],
        patient_id: Optional[int] = None,
        order_by: str = "id DESC",
        file_col_key: Optional[str] = None,
        insert_defaults: Optional[Dict[str, Any]] = None,
        template_provider: Optional[Dict[str, Any]] = None,
        can_add_roles: Optional[Tuple[str, ...]] = None,
        can_edit_roles: Optional[Tuple[str, ...]] = None,
        can_delete_roles: Optional[Tuple[str, ...]] = None,
        filter_sql: Optional[str] = None,
        filter_args: Optional[Tuple[Any, ...]] = None,
        on_mutation=None,
        parent=None,
    ):
        """Initializeaza componenta `SimpleCrudWidget` si legaturile UI aferente."""
        super().__init__(parent)
        self.table_name = table_name
        self.display_cols = display_cols
        self.fields = fields
        self.patient_id = patient_id
        self.order_by = order_by
        self.file_col_key = file_col_key
        self.insert_defaults = insert_defaults or {}
        self.template_provider = template_provider
        self.can_add_roles = can_add_roles
        self.can_edit_roles = can_edit_roles
        self.can_delete_roles = can_delete_roles
        self.filter_sql = filter_sql
        self.filter_args = filter_args or tuple()
        self.on_mutation = on_mutation
        self._page_size_options = [100, 250, 500, 1000]
        try:
            saved_page_size = int(get_setting(f"crud_page_size::{self.table_name}", "250") or 250)
        except Exception:
            saved_page_size = 250
        if saved_page_size <= 0:
            saved_page_size = 250
        if saved_page_size not in self._page_size_options:
            self._page_size_options.append(saved_page_size)
            self._page_size_options = sorted(set(self._page_size_options))
        self._page_size = int(saved_page_size)
        self._page_index = 0
        self._total_rows = 0
        self._total_pages = 1
        self._last_query_signature = None

        root = QVBoxLayout(self)
        if title:
            root.addWidget(QLabel(title))

        self.tbl = QTableWidget(0, len(self.display_cols) + 1)
        self.tbl.setHorizontalHeaderLabels(["ID"] + [c[0] for c in self.display_cols])
        self.tbl.setEditTriggers(QAbstractItemView.EditTrigger.NoEditTriggers)
        self.tbl.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
        self.tbl.setSelectionMode(QAbstractItemView.SelectionMode.SingleSelection)
        self.tbl.verticalHeader().setDefaultSectionSize(24)
        h = self.tbl.horizontalHeader()
        h.setSectionResizeMode(QHeaderView.ResizeMode.ResizeToContents)
        self.tbl.setColumnHidden(0, True)
        root.addWidget(self.tbl, 1)

        pager = QHBoxLayout()
        pager.setSpacing(8)
        self.btn_prev_page = QPushButton("Pagina anterioara")
        self.btn_next_page = QPushButton("Pagina urmatoare")
        self.cb_page_size = QComboBox()
        for page_size in self._page_size_options:
            self.cb_page_size.addItem(f"{page_size}/pagina", int(page_size))
        idx_page = self.cb_page_size.findData(int(self._page_size))
        self.cb_page_size.setCurrentIndex(idx_page if idx_page >= 0 else 0)
        self.lbl_page_info = QLabel("")
        self.lbl_page_info.setObjectName("muted")
        apply_std_icon(self.btn_prev_page, QStyle.StandardPixmap.SP_ArrowBack)
        apply_std_icon(self.btn_next_page, QStyle.StandardPixmap.SP_ArrowForward)
        pager.addWidget(self.btn_prev_page)
        pager.addWidget(self.btn_next_page)
        pager.addWidget(QLabel("Randuri/pagina:"))
        pager.addWidget(wrap_selector_widget(self.cb_page_size, self), 0)
        pager.addStretch(1)
        pager.addWidget(self.lbl_page_info, 0, Qt.AlignmentFlag.AlignRight)
        root.addLayout(pager)

        btns = QHBoxLayout()
        self.btn_add = QPushButton("Adauga")
        self.btn_edit = QPushButton("Editeaza")
        self.btn_delete = QPushButton("Sterge")
        self.btn_refresh = QPushButton("Refresh")
        apply_std_icon(self.btn_add, QStyle.StandardPixmap.SP_FileDialogNewFolder)
        apply_std_icon(self.btn_edit, QStyle.StandardPixmap.SP_DialogApplyButton)
        apply_std_icon(self.btn_delete, QStyle.StandardPixmap.SP_TrashIcon)
        apply_std_icon(self.btn_refresh, QStyle.StandardPixmap.SP_BrowserReload)
        btns.addWidget(self.btn_add)
        btns.addWidget(self.btn_edit)
        btns.addWidget(self.btn_delete)
        btns.addWidget(self.btn_refresh)
        if self.template_provider:
            self.btn_template = QPushButton("Sablon")
            self.btn_export_doc = QPushButton("Export PDF/RTF")
            apply_std_icon(self.btn_template, QStyle.StandardPixmap.SP_FileDialogDetailedView)
            apply_std_icon(self.btn_export_doc, QStyle.StandardPixmap.SP_DialogSaveButton)
            btns.addWidget(self.btn_template)
            btns.addWidget(self.btn_export_doc)
        if self.file_col_key:
            self.btn_open_file = QPushButton("Deschide fisier")
            apply_std_icon(self.btn_open_file, QStyle.StandardPixmap.SP_DialogOpenButton)
            btns.addWidget(self.btn_open_file)
            self.btn_open_file.clicked.connect(self.open_file_from_row)
        btns.addStretch(1)
        root.addLayout(btns)

        self.btn_add.clicked.connect(self.add_record)
        self.btn_edit.clicked.connect(self.edit_record)
        self.btn_delete.clicked.connect(self.delete_record)
        self.btn_refresh.clicked.connect(self.load_rows)
        self.btn_prev_page.clicked.connect(self._go_prev_page)
        self.btn_next_page.clicked.connect(self._go_next_page)
        self.cb_page_size.currentIndexChanged.connect(self._on_page_size_changed)
        if self.template_provider:
            self.btn_template.clicked.connect(self.add_from_template)
            self.btn_export_doc.clicked.connect(self.export_selected_doc)

        self.load_rows()
        self.apply_role_permissions()

    def _selected_id(self) -> Optional[int]:
        """Gestioneaza ID in `SimpleCrudWidget`."""
        row = self.tbl.currentRow()
        if row < 0:
            return None
        it = self.tbl.item(row, 0)
        if not it:
            return None
        try:
            return int(it.text())
        except Exception:
            return None

    def _fetch_row_dict(self, cur: sqlite3.Cursor, rec_id: int) -> Optional[Dict[str, Any]]:
        """Gestioneaza row dict in `SimpleCrudWidget`."""
        try:
            cur.execute(f"SELECT * FROM {self.table_name} WHERE id=?", (int(rec_id),))
            rr = cur.fetchone()
            return dict(rr) if rr is not None else None
        except Exception:
            return None

    def _emit_mutation(
        self,
        action: str,
        row_id: int,
        before_row: Optional[Dict[str, Any]],
        after_row: Optional[Dict[str, Any]],
        payload: Optional[Dict[str, Any]] = None,
    ) -> None:
        """Gestioneaza mutation in `SimpleCrudWidget`."""
        cb = getattr(self, "on_mutation", None)
        if not callable(cb):
            return
        try:
            cb(
                (action or "").strip(),
                {
                    "table_name": self.table_name,
                    "row_id": int(row_id),
                    "before_row": dict(before_row) if isinstance(before_row, dict) else None,
                    "after_row": dict(after_row) if isinstance(after_row, dict) else None,
                    "payload": dict(payload) if isinstance(payload, dict) else {},
                },
            )
        except Exception:
            pass

    def _role_allows(self, allowed: Optional[Tuple[str, ...]]) -> bool:
        """Gestioneaza allows in `SimpleCrudWidget`."""
        if allowed is None:
            return True
        return get_current_role() in allowed

    def apply_role_permissions(self):
        """Aplica role permissions in `SimpleCrudWidget`."""
        can_add = self._role_allows(self.can_add_roles)
        can_edit = self._role_allows(self.can_edit_roles)
        can_delete = self._role_allows(self.can_delete_roles)
        self.btn_add.setEnabled(can_add)
        self.btn_edit.setEnabled(can_edit)
        self.btn_delete.setEnabled(can_delete)
        if self.template_provider:
            self.btn_template.setEnabled(can_add)
            self.btn_export_doc.setEnabled(True)

    def _build_where_clause(self, deleted_clause: str) -> Tuple[str, Tuple[Any, ...]]:
        """Construieste where clause in `SimpleCrudWidget`."""
        where_sql = ""
        args: Tuple[Any, ...] = tuple()
        if self.filter_sql:
            where_sql = self.filter_sql
            if deleted_clause:
                where_sql = f"({where_sql}) AND {deleted_clause}"
            args = tuple(self.filter_args)
        elif self.patient_id is None:
            if deleted_clause:
                where_sql = deleted_clause
        else:
            where_sql = "pacient_id=?"
            args = (self.patient_id,)
            if deleted_clause:
                where_sql = f"{where_sql} AND {deleted_clause}"

        if where_sql.strip():
            return f" WHERE {where_sql}", args
        return "", args

    def _update_pager_ui(self, rows_on_page: int):
        """Actualizeaza pager interfata in `SimpleCrudWidget`."""
        if self._total_rows <= 0:
            self.lbl_page_info.setText("Pagina 1/1 | 0 rezultate")
        else:
            start_idx = self._page_index * self._page_size + 1
            end_idx = min(self._total_rows, start_idx + max(0, rows_on_page) - 1)
            self.lbl_page_info.setText(
                f"Pagina {self._page_index + 1}/{self._total_pages} | {start_idx}-{end_idx} din {self._total_rows}"
            )
        self.btn_prev_page.setEnabled(self._total_rows > 0 and self._page_index > 0)
        self.btn_next_page.setEnabled(self._total_rows > 0 and (self._page_index + 1) < self._total_pages)

    def _go_prev_page(self):
        """Gestioneaza prev page in `SimpleCrudWidget`."""
        if self._page_index <= 0:
            return
        self._page_index -= 1
        self.load_rows()

    def _go_next_page(self):
        """Gestioneaza next page in `SimpleCrudWidget`."""
        if (self._page_index + 1) >= self._total_pages:
            return
        self._page_index += 1
        self.load_rows()

    def _on_page_size_changed(self):
        """Gestioneaza evenimentul page size changed in `SimpleCrudWidget`."""
        try:
            new_size = int(self.cb_page_size.currentData() or 0)
        except Exception:
            return
        if new_size <= 0:
            return
        if new_size == self._page_size:
            self._update_pager_ui(self.tbl.rowCount())
            return
        self._page_size = int(new_size)
        self._page_index = 0
        try:
            set_setting(f"crud_page_size::{self.table_name}", str(int(new_size)))
        except Exception:
            pass
        self.load_rows()

    def load_rows(self):
        """Incarca rows in `SimpleCrudWidget`."""
        conn = get_conn()
        cur = conn.cursor()
        cols = [c[1] for c in self.display_cols]
        has_deleted = table_has_column(self.table_name, "deleted")
        deleted_clause = "COALESCE(deleted,0)=0" if has_deleted else ""
        where_sql, where_args = self._build_where_clause(deleted_clause)
        query_signature = (self.table_name, self.order_by, where_sql, tuple(where_args))
        if query_signature != self._last_query_signature:
            self._page_index = 0
            self._last_query_signature = query_signature

        cur.execute(f"SELECT COUNT(1) FROM {self.table_name}{where_sql}", where_args)
        cnt_row = cur.fetchone()
        try:
            self._total_rows = int(cnt_row[0]) if cnt_row is not None else 0
        except Exception:
            self._total_rows = 0
        self._total_rows = max(0, int(self._total_rows))
        self._total_pages = max(1, (self._total_rows + self._page_size - 1) // self._page_size)
        if self._page_index >= self._total_pages:
            self._page_index = self._total_pages - 1
        if self._page_index < 0:
            self._page_index = 0
        offset = self._page_index * self._page_size
        cur.execute(
            (
                f"SELECT id, {', '.join(cols)} "
                f"FROM {self.table_name}{where_sql} "
                f"ORDER BY {self.order_by} "
                f"LIMIT ? OFFSET ?"
            ),
            tuple(where_args) + (int(self._page_size), int(offset)),
        )
        rows = cur.fetchall()
        conn.close()

        self.tbl.setRowCount(len(rows))
        for i, r in enumerate(rows):
            self.tbl.setItem(i, 0, QTableWidgetItem(str(r[0])))
            for j, col in enumerate(cols, start=1):
                self.tbl.setItem(i, j, QTableWidgetItem("" if r[j] is None else str(r[j])))
        self._update_pager_ui(len(rows))

    def add_record(self):
        """Adauga record in `SimpleCrudWidget`."""
        d = RecordEditDialog("Adauga", self.fields, parent=self)
        if d.exec() != QDialog.DialogCode.Accepted:
            return
        payload = d.get_payload()
        if payload is None:
            return
        if "pacient_id" in payload and payload.get("pacient_id") is not None:
            resolved = resolve_pacient_id_input(payload.get("pacient_id"), parent=d)
            if resolved is None:
                return
            payload["pacient_id"] = resolved
            if self.table_name == "appointments" and not (payload.get("reminder_email") or "").strip():
                try:
                    m = get_master(resolved)
                    if m is not None:
                        payload["reminder_email"] = (m.get("email") or "").strip() or None
                except Exception:
                    pass
        if self.file_col_key and SUPABASE_STORAGE_ENABLED:
            path = payload.get(self.file_col_key)
            if path and not is_http_url(str(path)):
                try:
                    up_dlg = QProgressDialog("Upload Supabase...", "Anuleaza", 0, 100, self)
                    up_dlg.setWindowTitle("Supabase Upload")
                    up_dlg.setWindowModality(Qt.WindowModality.WindowModal)
                    up_dlg.setAutoClose(False)
                    up_dlg.setAutoReset(False)
                    up_dlg.show()

                    def up_pg(p, m=""):
                        """Gestioneaza pg in `SimpleCrudWidget`, ca helper intern in `add_record`."""
                        percent = int(max(0, min(100, p)))
                        up_dlg.setValue(percent)
                        base = str(m).strip() if m else "Upload Supabase..."
                        up_dlg.setLabelText(f"{base}\n{percent}%")
                        QApplication.processEvents()

                    payload[self.file_col_key] = supabase_storage_upload(
                        str(path),
                        progress_cb=up_pg,
                        cancelled_cb=lambda: up_dlg.wasCanceled(),
                    )
                    up_dlg.close()
                except Exception as e:
                    try:
                        up_dlg.close()
                    except Exception:
                        pass
                    QMessageBox.warning(self, "Storage", f"Upload cloud esuat:\n{e}\nPastrez fisierul local.")
        for k, v in self.insert_defaults.items():
            if payload.get(k) is None:
                payload[k] = v() if callable(v) else v

        cols = [f["key"] for f in self.fields]
        vals = [payload.get(k) for k in cols]
        for k, v in self.insert_defaults.items():
            if k not in cols:
                cols.append(k)
                vals.append(payload.get(k))
        if self.patient_id is not None:
            cols = ["pacient_id"] + cols
            vals = [self.patient_id] + vals
        if table_has_column(self.table_name, "sync_id") and "sync_id" not in cols:
            cols.append("sync_id")
            vals.append(uuid.uuid4().hex)
        if table_has_column(self.table_name, "updated_at") and "updated_at" not in cols:
            cols.append("updated_at")
            vals.append(now_ts())
        if table_has_column(self.table_name, "deleted") and "deleted" not in cols:
            cols.append("deleted")
            vals.append(0)
        if table_has_column(self.table_name, "device_id") and "device_id" not in cols:
            cols.append("device_id")
            vals.append(get_device_id())

        conn = get_conn()
        cur = conn.cursor()
        cur.execute(
            f"INSERT INTO {self.table_name} ({', '.join(cols)}) VALUES ({', '.join(['?']*len(cols))})",
            vals,
        )
        new_id = cur.lastrowid
        after_row = self._fetch_row_dict(cur, int(new_id)) if new_id else None
        conn.commit()
        conn.close()
        try:
            log_action("crud_add", f"{self.table_name}: id={new_id}")
        except Exception:
            pass
        try:
            self._emit_mutation("add", int(new_id), None, after_row, payload)
        except Exception:
            pass
        self._page_index = 0
        self.load_rows()

    def edit_record(self):
        """Gestioneaza record in `SimpleCrudWidget`."""
        rec_id = self._selected_id()
        if rec_id is None:
            return
        conn = get_conn()
        cur = conn.cursor()
        cols = [f["key"] for f in self.fields]
        cur.execute(
            f"SELECT {', '.join(cols)} FROM {self.table_name} WHERE id=?",
            (rec_id,),
        )
        row = cur.fetchone()
        conn.close()
        if row is None:
            return
        data = {cols[i]: row[i] for i in range(len(cols))}
        d = RecordEditDialog("Editeaza", self.fields, data=data, parent=self)
        if d.exec() != QDialog.DialogCode.Accepted:
            return
        payload = d.get_payload()
        if payload is None:
            return
        if "pacient_id" in payload and payload.get("pacient_id") is not None:
            resolved = resolve_pacient_id_input(payload.get("pacient_id"), parent=d)
            if resolved is None:
                return
            payload["pacient_id"] = resolved
        if self.file_col_key and SUPABASE_STORAGE_ENABLED:
            path = payload.get(self.file_col_key)
            if path and not is_http_url(str(path)):
                try:
                    up_dlg = QProgressDialog("Upload Supabase...", "Anuleaza", 0, 100, self)
                    up_dlg.setWindowTitle("Supabase Upload")
                    up_dlg.setWindowModality(Qt.WindowModality.WindowModal)
                    up_dlg.setAutoClose(False)
                    up_dlg.setAutoReset(False)
                    up_dlg.show()

                    def up_pg(p, m=""):
                        """Gestioneaza pg in `SimpleCrudWidget`, ca helper intern in `edit_record`."""
                        percent = int(max(0, min(100, p)))
                        up_dlg.setValue(percent)
                        base = str(m).strip() if m else "Upload Supabase..."
                        up_dlg.setLabelText(f"{base}\n{percent}%")
                        QApplication.processEvents()

                    payload[self.file_col_key] = supabase_storage_upload(
                        str(path),
                        progress_cb=up_pg,
                        cancelled_cb=lambda: up_dlg.wasCanceled(),
                    )
                    up_dlg.close()
                except Exception as e:
                    try:
                        up_dlg.close()
                    except Exception:
                        pass
                    QMessageBox.warning(self, "Storage", f"Upload cloud esuat:\n{e}\nPastrez fisierul local.")
        sets_list = [f"{k}=?" for k in cols]
        vals = [payload.get(k) for k in cols]
        if table_has_column(self.table_name, "updated_at"):
            sets_list.append("updated_at=?")
            vals.append(now_ts())
        if table_has_column(self.table_name, "device_id"):
            sets_list.append("device_id=?")
            vals.append(get_device_id())
        if table_has_column(self.table_name, "deleted"):
            sets_list.append("deleted=0")
        sets = ", ".join(sets_list)
        vals = vals + [rec_id]
        conn = get_conn()
        cur = conn.cursor()
        before_row = self._fetch_row_dict(cur, int(rec_id))
        cur.execute(f"UPDATE {self.table_name} SET {sets} WHERE id=?", vals)
        after_row = self._fetch_row_dict(cur, int(rec_id))
        conn.commit()
        conn.close()
        try:
            log_action("crud_edit", f"{self.table_name}: id={rec_id}")
        except Exception:
            pass
        try:
            self._emit_mutation("edit", int(rec_id), before_row, after_row, payload)
        except Exception:
            pass
        self.load_rows()

    def delete_record(self):
        """Sterge record in `SimpleCrudWidget`."""
        rec_id = self._selected_id()
        if rec_id is None:
            return
        if QMessageBox.question(
            self,
            "Confirmare",
            "Stergi inregistrarea selectata?",
            QMessageBox.StandardButton.Ok | QMessageBox.StandardButton.Cancel,
            QMessageBox.StandardButton.Cancel,
        ) != QMessageBox.StandardButton.Ok:
            return
        conn = get_conn()
        cur = conn.cursor()
        before_row = self._fetch_row_dict(cur, int(rec_id))
        if table_has_column(self.table_name, "deleted"):
            cur.execute(
                f"UPDATE {self.table_name} SET deleted=1, updated_at=?, device_id=? WHERE id=?",
                (now_ts(), get_device_id(), rec_id),
            )
        else:
            cur.execute(f"DELETE FROM {self.table_name} WHERE id=?", (rec_id,))
        after_row = self._fetch_row_dict(cur, int(rec_id))
        conn.commit()
        conn.close()
        try:
            log_action("crud_delete", f"{self.table_name}: id={rec_id}")
        except Exception:
            pass
        try:
            self._emit_mutation("delete", int(rec_id), before_row, after_row, None)
        except Exception:
            pass
        self.load_rows()

    def add_from_template(self):
        """Adauga from template in `SimpleCrudWidget`."""
        if not self.template_provider:
            return
        if not self.patient_id:
            QMessageBox.warning(self, "Info", "Selecteaza un pacient.")
            return
        master = get_master(self.patient_id)
        if master is None:
            QMessageBox.warning(self, "Info", "Pacientul nu exista.")
            return
        last = get_latest_consult(self.patient_id)
        include_letter_type = bool(self.template_provider.get("include_letter_type"))
        dlg = TemplateDialog(
            self.template_provider.get("title", "Sablon"),
            self.template_provider.get("templates", []),
            dict(master),
            dict(last) if last else {},
            include_letter_type=include_letter_type,
            parent=self,
        )
        if dlg.exec() != QDialog.DialogCode.Accepted:
            return
        payload = dlg.get_payload()
        if payload is None:
            return

        cols = [f["key"] for f in self.fields]
        vals = []
        for k in cols:
            vals.append(payload.get(k))
        for k, v in self.insert_defaults.items():
            if k not in cols:
                cols.append(k)
                vals.append(v() if callable(v) else v)

        cols = ["pacient_id"] + cols
        vals = [self.patient_id] + vals

        conn = get_conn()
        cur = conn.cursor()
        cur.execute(
            f"INSERT INTO {self.table_name} ({', '.join(cols)}) VALUES ({', '.join(['?']*len(cols))})",
            vals,
        )
        new_id = cur.lastrowid
        conn.commit()
        conn.close()
        try:
            log_action("template_add", f"{self.table_name}: id={new_id}")
        except Exception:
            pass
        self._page_index = 0
        self.load_rows()

    def export_selected_doc(self):
        """Exporta selected doc in `SimpleCrudWidget`."""
        if not self.template_provider:
            return
        rec_id = self._selected_id()
        if rec_id is None:
            return
        conn = get_conn()
        cur = conn.cursor()
        cur.execute(
            f"SELECT * FROM {self.table_name} WHERE id=?",
            (rec_id,),
        )
        row = cur.fetchone()
        conn.close()
        if row is None:
            return
        content = row["content"] if "content" in row.keys() else ""
        template_name = row["template_name"] if "template_name" in row.keys() else ""
        doc_date = row["date"] if "date" in row.keys() else ""
        doc_medic = row["doctor"] if "doctor" in row.keys() else ""
        signed_by = row["signed_by"] if "signed_by" in row.keys() else ""
        signature_path = row["signature_path"] if "signature_path" in row.keys() else ""

        master = get_master(self.patient_id) if self.patient_id else None
        meta = {
            "nume_prenume": master["nume_prenume"] if master else "",
            "cnp": master["cnp"] if master else "",
            "data": doc_date,
            "medic": doc_medic,
        }

        title = self.template_provider.get("export_title", "Document")
        if template_name:
            title = f"{title} - {template_name}"

        pdf_path = generate_text_report_pdf(
            title,
            content or "",
            meta,
            prefix=self.table_name,
            signature_path=signature_path,
            signed_by=signed_by,
        )
        rtf_path = generate_text_report_rtf(
            title,
            content or "",
            meta,
            prefix=self.table_name,
            signed_by=signed_by,
        )
        d = ReportPreviewDialog(pdf_path, rtf_path=rtf_path, parent=self)
        d.exec()

    def open_file_from_row(self):
        """Deschide file from row in `SimpleCrudWidget`."""
        if not self.file_col_key:
            return
        rec_id = self._selected_id()
        if rec_id is None:
            return
        conn = get_conn()
        cur = conn.cursor()
        cur.execute(
            f"SELECT {self.file_col_key} FROM {self.table_name} WHERE id=?",
            (rec_id,),
        )
        row = cur.fetchone()
        conn.close()
        if row is None:
            return
        path = row[0]
        if not path:
            QMessageBox.information(self, "Info", "Nu exista fisier atasat.")
            return
        if is_http_url(str(path)):
            QDesktopServices.openUrl(QUrl(str(path)))
        else:
            QDesktopServices.openUrl(QUrl.fromLocalFile(str(path)))


# ============================================================
# UI: Nomenclatoare
# ============================================================
class NomenclatoareDialog(QDialog):
    def __init__(self, parent=None):
        """Initializeaza dialogul `NomenclatoareDialog` si configureaza controalele interfetei."""
        super().__init__(parent)
        self.setWindowTitle("Nomenclatoare")
        self.resize(1120, 720)

        root = QVBoxLayout(self)
        root.addWidget(QLabel("Liste de coduri administrative pentru receptie/cazuri/raportare."))

        tabs = QTabWidget()
        root.addWidget(tabs, 1)

        display_cols = [
            ("Denumire", "denumire"),
            ("Cod DRG", "cod_drg"),
            ("Valid", "valid"),
        ]
        fields = [
            {"key": "denumire", "label": "Denumire"},
            {"key": "cod_drg", "label": "Cod DRG", "type": "int"},
            {"key": "valid", "label": "Valid", "type": "bool"},
        ]
        roles_edit = ("admin", "receptie")
        roles_delete = ("admin",)

        def _add_nom_tab(label: str, table_name: str):
            """Adauga nom tab in `NomenclatoareDialog`, ca helper intern in `__init__`."""
            tabs.addTab(
                SimpleCrudWidget(
                    "",
                    table_name,
                    display_cols,
                    fields,
                    order_by="COALESCE(cod_drg, 9999) ASC, denumire COLLATE NOCASE ASC",
                    can_add_roles=roles_edit,
                    can_edit_roles=roles_edit,
                    can_delete_roles=roles_delete,
                ),
                label,
            )

# ============================================================
# UI: Role/Permissions
# ============================================================
class RoleDialog(QDialog):
    def __init__(self, parent=None):
        """Initializeaza dialogul `RoleDialog` si configureaza controalele interfetei."""
        super().__init__(parent)
        self.setWindowTitle("Utilizator / Rol")
        self.setModal(True)
        self.resize(1220, 700)

        root = QVBoxLayout(self)
        main_row = QHBoxLayout()
        main_row.setSpacing(12)
        root.addLayout(main_row, 1)

        left_box = QGroupBox("Utilizator curent")
        left_box.setMaximumWidth(420)
        left_root = QVBoxLayout(left_box)
        form = QFormLayout()
        self.ed_user = QLineEdit()
        self.ed_full_name = QLineEdit()
        self.cb_role = QComboBox()
        self.cb_role.addItems(ROLE_CHOICES)
        self.ed_pass = QLineEdit()
        self.ed_pass.setEchoMode(QLineEdit.EchoMode.Password)
        self.cb_active = QComboBox()
        self.cb_active.addItems(["Activ", "Inactiv"])
        form.addRow("Utilizator:", self.ed_user)
        form.addRow("Nume si Prenume:", self.ed_full_name)
        form.addRow("Rol:", wrap_selector_widget(self.cb_role, self))
        form.addRow("Parola (optional):", self.ed_pass)
        form.addRow("Status:", wrap_selector_widget(self.cb_active, self))
        left_root.addLayout(form)

        btns_row = QHBoxLayout()
        self.btn_refresh = QPushButton("Refresh")
        apply_std_icon(self.btn_refresh, QStyle.StandardPixmap.SP_BrowserReload)
        btns_row.addWidget(self.btn_refresh)
        btns_row.addStretch(1)
        left_root.addLayout(btns_row)
        left_root.addStretch(1)
        main_row.addWidget(left_box, 0)

        right_host = QWidget()
        right_root = QHBoxLayout(right_host)
        right_root.setContentsMargins(0, 0, 0, 0)
        right_root.setSpacing(10)
        main_row.addWidget(right_host, 1)

        users_box = QGroupBox("Utilizatori existenti")
        users_root = QVBoxLayout(users_box)
        self.tbl_users = QTableWidget(0, 4)
        self.tbl_users.setHorizontalHeaderLabels(["User", "Nume si Prenume", "Rol", "Activ"])
        self.tbl_users.setEditTriggers(QAbstractItemView.EditTrigger.NoEditTriggers)
        self.tbl_users.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
        self.tbl_users.setSelectionMode(QAbstractItemView.SelectionMode.SingleSelection)
        self.tbl_users.verticalHeader().setDefaultSectionSize(24)
        h = self.tbl_users.horizontalHeader()
        h.setSectionResizeMode(QHeaderView.ResizeMode.Stretch)
        h.setStretchLastSection(True)
        self.tbl_users.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Expanding)
        users_root.addWidget(self.tbl_users, 1)
        right_root.addWidget(users_box, 1)

        perm_box = QGroupBox("Permisiuni functii (utilizator selectat)")
        perm_root = QVBoxLayout(perm_box)
        perm_actions = QHBoxLayout()
        self.btn_perm_all = QPushButton("Selecteaza toate")
        self.btn_perm_none = QPushButton("Deselecteaza toate")
        perm_actions.addWidget(self.btn_perm_all)
        perm_actions.addWidget(self.btn_perm_none)
        perm_actions.addStretch(1)
        perm_root.addLayout(perm_actions)

        perm_scroll = QScrollArea()
        perm_scroll.setWidgetResizable(True)
        perm_container = QWidget()
        perm_grid = QGridLayout(perm_container)
        perm_grid.setHorizontalSpacing(14)
        perm_grid.setVerticalSpacing(6)
        self._perm_checks: Dict[str, QCheckBox] = {}
        for idx, (feature_key, feature_label) in enumerate(FEATURE_PERMISSION_ITEMS):
            chk = QCheckBox(feature_label)
            chk.setChecked(True)
            self._perm_checks[feature_key] = chk
            perm_grid.addWidget(chk, idx // 2, idx % 2)
        perm_scroll.setWidget(perm_container)
        perm_root.addWidget(perm_scroll, 1)
        right_root.addWidget(perm_box, 1)

        btns = QDialogButtonBox(QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel)
        btns.accepted.connect(self.accept)
        btns.rejected.connect(self.reject)
        root.addWidget(btns)

        self.ed_user.setText(get_current_user())
        current_user = get_user(get_current_user()) or {}
        self.ed_full_name.setText((current_user.get("full_name") or "").strip())
        role = get_current_role()
        idx = self.cb_role.findText(role)
        self.cb_role.setCurrentIndex(idx if idx >= 0 else 0)
        self.cb_active.setCurrentIndex(0)

        self.btn_refresh.clicked.connect(self.reload_users)
        self.tbl_users.itemSelectionChanged.connect(self._load_selected_user)
        self.btn_perm_all.clicked.connect(self._set_all_permissions_checked)
        self.btn_perm_none.clicked.connect(self._set_no_permissions_checked)
        self.ed_user.editingFinished.connect(self._load_permissions_for_current_username)
        self.reload_users()
        self._load_permissions_for_current_username()

    def _set_all_permissions_checked(self):
        """Seteaza all permissions checked in `RoleDialog`."""
        for chk in self._perm_checks.values():
            chk.setChecked(True)

    def _set_no_permissions_checked(self):
        """Seteaza no permissions checked in `RoleDialog`."""
        for chk in self._perm_checks.values():
            chk.setChecked(False)

    def _load_permissions_for_current_username(self):
        """Incarca permissions for current username in `RoleDialog`."""
        username = (self.ed_user.text() or "").strip()
        allowed = get_user_allowed_features(username)
        for key, chk in self._perm_checks.items():
            chk.setChecked(key in allowed)

    def reload_users(self):
        """Reincarca users in `RoleDialog`."""
        rows = list_users()
        self.tbl_users.setRowCount(len(rows))
        for i, r in enumerate(rows):
            username = r.get("username") or ""
            full_name = (r.get("full_name") or "").strip()
            role = r.get("role") or ""
            active = 1 if int(r.get("active", 1) or 0) == 1 else 0
            it_user = QTableWidgetItem(username)
            it_full_name = QTableWidgetItem(full_name)
            it_role = QTableWidgetItem(role)
            it_active = QTableWidgetItem("Da" if active == 1 else "Nu")
            it_user.setIcon(get_role_icon(role, active))

            # color code by role / active
            if active == 0:
                bg = QBrush(QColor(230, 230, 230))
                fg = QBrush(QColor(120, 120, 120))
            else:
                if role == "admin":
                    bg = QBrush(QColor(207, 232, 255))
                    fg = QBrush(QColor(0, 64, 128))
                elif role == "medic":
                    bg = QBrush(QColor(220, 245, 220))
                    fg = QBrush(QColor(0, 90, 0))
                elif role == "asistenta":
                    bg = QBrush(QColor(255, 235, 205))
                    fg = QBrush(QColor(128, 64, 0))
                elif role == "receptie":
                    bg = QBrush(QColor(230, 220, 255))
                    fg = QBrush(QColor(64, 0, 128))
                else:
                    bg = QBrush(QColor(245, 245, 245))
                    fg = QBrush(QColor(0, 0, 0))

            for it in (it_user, it_full_name, it_role, it_active):
                it.setBackground(bg)
                it.setForeground(fg)

            it_user.setToolTip(f"Rol: {role or '-'} | Activ: {'Da' if active == 1 else 'Nu'}")
            self.tbl_users.setItem(i, 0, it_user)
            self.tbl_users.setItem(i, 1, it_full_name)
            self.tbl_users.setItem(i, 2, it_role)
            self.tbl_users.setItem(i, 3, it_active)

    def _load_selected_user(self):
        """Incarca selected user in `RoleDialog`."""
        row = self.tbl_users.currentRow()
        if row < 0:
            return
        it = self.tbl_users.item(row, 0)
        if not it:
            return
        username = it.text().strip()
        if not username:
            return
        u = get_user(username)
        if not u:
            return
        self.ed_user.setText(u.get("username") or "")
        self.ed_full_name.setText((u.get("full_name") or "").strip())
        idx = self.cb_role.findText(u.get("role") or "")
        self.cb_role.setCurrentIndex(idx if idx >= 0 else 0)
        self.ed_pass.setText("")
        self.cb_active.setCurrentIndex(0 if int(u.get("active", 1) or 0) == 1 else 1)
        self._load_permissions_for_current_username()

    def get_values(self) -> Tuple[str, str, str, str, int]:
        """Returneaza values in `RoleDialog`."""
        active = 1 if self.cb_active.currentIndex() == 0 else 0
        return (
            self.ed_user.text().strip() or DEFAULT_USER,
            self.ed_full_name.text().strip() or self.ed_user.text().strip() or DEFAULT_USER,
            self.cb_role.currentText().strip() or DEFAULT_ROLE,
            self.ed_pass.text().strip(),
            active,
        )

    def get_selected_permissions(self) -> set:
        """Returneaza selected permissions in `RoleDialog`."""
        return {key for key, chk in self._perm_checks.items() if chk.isChecked()}


# ============================================================
# UI: Login
# ============================================================
class LoginDialog(QDialog):
    def __init__(self, parent=None):
        """Initializeaza dialogul `LoginDialog` si configureaza controalele interfetei."""
        super().__init__(parent)
        self.setWindowTitle("Autentificare")
        self.setModal(True)
        self.resize(380, 180)

        root = QVBoxLayout(self)
        form = QFormLayout()
        self.ed_user = QLineEdit()
        self.ed_pass = QLineEdit()
        self.ed_pass.setEchoMode(QLineEdit.EchoMode.Password)

        user_row = QWidget()
        user_row_l = QHBoxLayout(user_row)
        user_row_l.setContentsMargins(0, 0, 0, 0)
        user_row_l.setSpacing(6)
        user_icon_lbl = QLabel()
        user_icon = get_user_icon()
        if not user_icon.isNull():
            user_icon_lbl.setPixmap(user_icon.pixmap(16, 16))
        user_icon_lbl.setFixedWidth(20)
        user_icon_lbl.setAlignment(Qt.AlignmentFlag.AlignCenter)
        user_row_l.addWidget(user_icon_lbl)
        user_row_l.addWidget(self.ed_user, 1)

        pass_row = QWidget()
        pass_row_l = QHBoxLayout(pass_row)
        pass_row_l.setContentsMargins(0, 0, 0, 0)
        pass_row_l.setSpacing(6)
        pass_icon_lbl = QLabel()
        pass_icon = get_lock_icon()
        if not pass_icon.isNull():
            pass_icon_lbl.setPixmap(pass_icon.pixmap(16, 16))
        pass_icon_lbl.setFixedWidth(20)
        pass_icon_lbl.setAlignment(Qt.AlignmentFlag.AlignCenter)
        pass_row_l.addWidget(pass_icon_lbl)
        pass_row_l.addWidget(self.ed_pass, 1)

        form.addRow("User:", user_row)
        form.addRow("Parola:", pass_row)
        root.addLayout(form)

        self.chk_show_pass = QCheckBox("Afiseaza parola")
        self.chk_show_pass.toggled.connect(self._toggle_password)
        root.addWidget(self.chk_show_pass)

        self.lbl_msg = QLabel("")
        self.lbl_msg.setStyleSheet("color: #b00020;")
        root.addWidget(self.lbl_msg)

        btns = QDialogButtonBox(QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel)
        btns.accepted.connect(self._on_accept)
        btns.rejected.connect(self.reject)
        root.addWidget(btns)

        self.ed_user.setFocus()
        self.user_row = None
        force_ascii_ui_texts(self)

    def _toggle_password(self, checked: bool):
        """Comuta password in `LoginDialog`."""
        self.ed_pass.setEchoMode(
            QLineEdit.EchoMode.Normal if checked else QLineEdit.EchoMode.Password
        )

    def try_login(self) -> Optional[Dict[str, Any]]:
        """Gestioneaza login in `LoginDialog`."""
        u = self.ed_user.text().strip()
        p = self.ed_pass.text().strip()
        row = validate_login(u, p)
        if not row:
            self.lbl_msg.setText("User sau parola incorecte.")
            return None
        if SUPABASE_AUTH_ENABLED:
            try:
                supabase_auth_login(u, p)
            except Exception as e:
                if SUPABASE_AUTH_REQUIRED:
                    self.lbl_msg.setText(f"Supabase login esuat: {e}")
                    return None
                else:
                    self.lbl_msg.setText(f"Login local OK. Supabase login esuat: {e}")
        return row

    def _on_accept(self):
        """Gestioneaza evenimentul accept in `LoginDialog`."""
        row = self.try_login()
        if row:
            self.user_row = row
            self.accept()


# ============================================================
# UI: Reminders Scheduler (local)
# ============================================================
class RemindersDialog(QDialog):
    def __init__(self, parent=None):
        """Initializeaza dialogul `RemindersDialog` si configureaza controalele interfetei."""
        super().__init__(parent)
        self.setWindowTitle("Remindere automate")
        self.setModal(True)
        self.resize(860, 760)

        outer = QVBoxLayout(self)
        scroll = QScrollArea(self)
        scroll.setWidgetResizable(True)
        scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        scroll.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
        scroll.setFrameShape(QFrame.Shape.NoFrame)
        outer.addWidget(scroll, 1)

        scroll_content = QWidget()
        scroll.setWidget(scroll_content)
        root = QVBoxLayout(scroll_content)
        form = QFormLayout()
        self.cb_enabled = QCheckBox("Activ")
        self.ed_time = QLineEdit()
        self.ed_time.setPlaceholderText("HH:MM, HH:MM")
        cur_time = get_setting("reminder_times", "08:00,12:00") or "08:00,12:00"
        self.ed_time.setText(cur_time)
        self.cb_enabled.setChecked(get_setting("reminder_auto_enabled", "0") == "1")
        self.cb_scheduler_mode = QComboBox()
        self.cb_scheduler_mode.addItem("Continuu (recomandat)", "continuous")
        self.cb_scheduler_mode.addItem("Ore fixe", "fixed_times")
        mode = (get_setting("reminder_scheduler_mode", "continuous") or "continuous").strip().lower()
        idx_mode = self.cb_scheduler_mode.findData(mode)
        self.cb_scheduler_mode.setCurrentIndex(idx_mode if idx_mode >= 0 else 0)

        self.cb_send_rule = QComboBox()
        for key, label in REMINDER_RULE_CHOICES:
            self.cb_send_rule.addItem(label, key)
        rule = _get_reminder_rule()
        idx_rule = self.cb_send_rule.findData(rule)
        self.cb_send_rule.setCurrentIndex(idx_rule if idx_rule >= 0 else 0)

        self.sp_run_interval = QSpinBox()
        self.sp_run_interval.setRange(5, 1440)
        self.sp_run_interval.setSuffix(" min")
        self.sp_run_interval.setValue(_get_reminder_run_interval_min())

        self.sp_retry_max = QSpinBox()
        self.sp_retry_max.setRange(1, 20)
        self.sp_retry_max.setValue(_setting_int("reminder_retry_max_attempts", 3, 1, 20))
        self.sp_retry_delay = QSpinBox()
        self.sp_retry_delay.setRange(1, 1440)
        self.sp_retry_delay.setSuffix(" min")
        self.sp_retry_delay.setValue(_setting_int("reminder_retry_delay_min", 20, 1, 1440))

        self.ed_smsmobileapi_url = QLineEdit()
        self.ed_smsmobileapi_url.setPlaceholderText("https://api.smsmobileapi.com/sendsms")
        self.ed_smsmobileapi_url.setText(get_setting("reminder_smsmobileapi_url", "") or "")

        self.ed_smsmobileapi_api_key = QLineEdit()
        self.ed_smsmobileapi_api_key.setEchoMode(QLineEdit.EchoMode.Password)
        self.ed_smsmobileapi_api_key.setPlaceholderText("API Key SMSMobileAPI")
        self.ed_smsmobileapi_api_key.setText(get_setting("reminder_smsmobileapi_api_key", "") or "")

        self.ed_smsmobileapi_from = QLineEdit()
        self.ed_smsmobileapi_from.setPlaceholderText("Sender (telefon, optional)")
        self.ed_smsmobileapi_from.setText(get_setting("reminder_smsmobileapi_from", "") or "")

        self.ed_test_phone = QLineEdit()
        self.ed_test_phone.setPlaceholderText("+407xxxxxxxx")
        self.ed_test_phone.setText(get_setting("reminder_test_phone", "") or "")

        form.addRow("Programare automata:", self.cb_enabled)
        form.addRow("Mod scheduler:", wrap_selector_widget(self.cb_scheduler_mode, self))
        form.addRow("Ore (HH:MM, separate prin virgula):", self.ed_time)
        form.addRow("Regula de trimitere:", wrap_selector_widget(self.cb_send_rule, self))
        form.addRow("Interval rulare (mod continuu):", self.sp_run_interval)
        form.addRow("Incercari maxime retry:", self.sp_retry_max)
        form.addRow("Delay retry:", self.sp_retry_delay)
        form.addRow("SMSMobileAPI URL:", self.ed_smsmobileapi_url)
        form.addRow("SMSMobileAPI API Key:", self.ed_smsmobileapi_api_key)
        form.addRow("SMSMobileAPI telefon expeditor:", self.ed_smsmobileapi_from)
        form.addRow("Numar test implicit:", self.ed_test_phone)
        root.addLayout(form)

        self.lbl_info = QLabel("Trimiterea SMS se face doar prin SMSMobileAPI (mod local).")
        self.lbl_info.setStyleSheet("color: gray;")
        root.addWidget(self.lbl_info)

        tpl_box = QGroupBox("Template-uri SMS")
        tpl_form = QFormLayout(tpl_box)
        self.ed_tpl_default = QTextEdit()
        self.ed_tpl_default.setPlaceholderText("Template reminder standard")
        self.ed_tpl_default.setFixedHeight(72)
        self.ed_tpl_default.setPlainText(get_setting("reminder_template_default", REMINDER_TEMPLATE_DEFAULT) or REMINDER_TEMPLATE_DEFAULT)
        self.ed_tpl_confirm = QTextEdit()
        self.ed_tpl_confirm.setPlaceholderText("Template pentru status Confirmat")
        self.ed_tpl_confirm.setFixedHeight(72)
        self.ed_tpl_confirm.setPlainText(get_setting("reminder_template_confirm", REMINDER_TEMPLATE_CONFIRM) or REMINDER_TEMPLATE_CONFIRM)
        self.ed_tpl_cancel = QTextEdit()
        self.ed_tpl_cancel.setPlaceholderText("Template pentru status Anulat")
        self.ed_tpl_cancel.setFixedHeight(72)
        self.ed_tpl_cancel.setPlainText(get_setting("reminder_template_cancel", REMINDER_TEMPLATE_CANCEL) or REMINDER_TEMPLATE_CANCEL)
        self.ed_tpl_ortopedie = QTextEdit()
        self.ed_tpl_ortopedie.setPlaceholderText("Template pentru programari de Ortopedie")
        self.ed_tpl_ortopedie.setFixedHeight(72)
        self.ed_tpl_ortopedie.setPlainText(
            get_setting("reminder_template_ortopedie", REMINDER_TEMPLATE_ORTOPEDIE) or REMINDER_TEMPLATE_ORTOPEDIE
        )
        self.ed_tpl_fizioterapie = QTextEdit()
        self.ed_tpl_fizioterapie.setPlaceholderText("Template pentru programari de Fizioterapie")
        self.ed_tpl_fizioterapie.setFixedHeight(72)
        self.ed_tpl_fizioterapie.setPlainText(
            get_setting("reminder_template_fizioterapie", REMINDER_TEMPLATE_FIZIOTERAPIE) or REMINDER_TEMPLATE_FIZIOTERAPIE
        )
        self.cb_manual_template = QComboBox()
        self.cb_manual_template.addItem("Standard", "default")
        self.cb_manual_template.addItem("Confirmare", "confirm")
        self.cb_manual_template.addItem("Anulare", "cancel")
        self.cb_manual_template.addItem("Ortopedie", "ortopedie")
        self.cb_manual_template.addItem("Fizioterapie", "fizioterapie")
        manual_key = _normalize_forced_template_key(get_setting("reminder_manual_template_key", "default") or "default") or "default"
        idx_manual = self.cb_manual_template.findData(manual_key)
        self.cb_manual_template.setCurrentIndex(idx_manual if idx_manual >= 0 else 0)
        tpl_form.addRow("Standard:", self.ed_tpl_default)
        tpl_form.addRow("Confirmare:", self.ed_tpl_confirm)
        tpl_form.addRow("Anulare:", self.ed_tpl_cancel)
        tpl_form.addRow("Ortopedie:", self.ed_tpl_ortopedie)
        tpl_form.addRow("Fizioterapie:", self.ed_tpl_fizioterapie)
        tpl_form.addRow("Template trimitere manuala:", wrap_selector_widget(self.cb_manual_template, self))
        root.addWidget(tpl_box)

        monitor_box = QGroupBox("Monitorizare trimitere")
        monitor_root = QVBoxLayout(monitor_box)
        self.txt_monitor = QTextEdit()
        self.txt_monitor.setReadOnly(True)
        self.txt_monitor.setMinimumHeight(160)
        monitor_root.addWidget(self.txt_monitor, 1)
        root.addWidget(monitor_box, 1)

        # Zona fixa (in afara scroll): actiuni + OK/Cancel
        fixed_actions = QWidget(self)
        fixed_actions_layout = QVBoxLayout(fixed_actions)
        fixed_actions_layout.setContentsMargins(0, 0, 0, 0)
        fixed_actions_layout.setSpacing(8)

        btns = QHBoxLayout()
        self.btn_test = QPushButton("Testeaza acum")
        apply_std_icon(self.btn_test, QStyle.StandardPixmap.SP_MediaPlay)
        btns.addWidget(self.btn_test)
        self.btn_verify_gateway = QPushButton("Verifica gateway")
        apply_std_icon(self.btn_verify_gateway, QStyle.StandardPixmap.SP_BrowserReload)
        btns.addWidget(self.btn_verify_gateway)
        self.btn_test_sms = QPushButton("Test trimitere SMS")
        apply_std_icon(self.btn_test_sms, QStyle.StandardPixmap.SP_MessageBoxInformation)
        btns.addWidget(self.btn_test_sms)
        self.btn_send_selected_template = QPushButton("Trimite mesaje (template selectat)")
        apply_std_icon(self.btn_send_selected_template, QStyle.StandardPixmap.SP_MediaPlay)
        btns.addWidget(self.btn_send_selected_template)
        self.btn_refresh_monitor = QPushButton("Refresh monitor")
        apply_std_icon(self.btn_refresh_monitor, QStyle.StandardPixmap.SP_BrowserReload)
        btns.addWidget(self.btn_refresh_monitor)
        btns.addStretch(1)
        fixed_actions_layout.addLayout(btns)

        box = QDialogButtonBox(QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel)
        box.accepted.connect(self.accept)
        box.rejected.connect(self.reject)
        fixed_actions_layout.addWidget(box)
        outer.addWidget(fixed_actions, 0)

        self.btn_test.clicked.connect(self._test_now)
        self.btn_verify_gateway.clicked.connect(self._test_gateway)
        self.btn_test_sms.clicked.connect(self._test_sms_send)
        self.btn_send_selected_template.clicked.connect(self._send_selected_template_now)
        self.btn_refresh_monitor.clicked.connect(self.refresh_monitor_view)
        self.refresh_monitor_view()

    def _test_now(self):
        """Testeaza now in `RemindersDialog`."""
        parent = self.parent()
        if hasattr(parent, "send_reminders_now"):
            parent.send_reminders_now(
                silent=False,
                sms_config=self.get_sms_config(),
                dispatch_mode=self.get_dispatch_mode(),
                trigger_dt=datetime.now(),
            )

    def _test_gateway(self):
        """Testeaza gateway in `RemindersDialog`."""
        cfg = self.get_sms_config()
        url = (cfg.get("smsmobileapi_url") or "").strip() or "https://api.smsmobileapi.com/sendsms"
        title = "SMSMobileAPI"
        missing_url_msg = "Completeaza SMSMobileAPI URL."
        if not url:
            QMessageBox.warning(self, title, missing_url_msg)
            return
        if not _is_http_url(url):
            QMessageBox.warning(self, title, "URL invalid. Exemplu: https://api.smsmobileapi.com/sendsms")
            return

        try:
            req = urllib.request.Request(url, method="GET")
            req.add_header("User-Agent", "PacientiApp/1.0")
            with urllib.request.urlopen(req, timeout=6) as resp:
                code = int(getattr(resp, "status", 200) or 200)
                QMessageBox.information(self, title, f"Endpoint accesibil (HTTP {code}).")
                return
        except urllib.error.HTTPError as e:
            code = int(getattr(e, "code", 0) or 0)
            if code in (200, 201, 202, 204, 400, 401, 403, 404, 405):
                QMessageBox.information(self, title, f"Endpoint raspunde (HTTP {code}).")
                return
            QMessageBox.warning(self, title, f"Endpoint a raspuns cu HTTP {code}.")
            return
        except urllib.error.URLError as e:
            QMessageBox.critical(self, title, f"Nu pot contacta endpoint-ul:\n{e.reason}")
            return
        except Exception as e:
            QMessageBox.critical(self, title, f"Eroare la verificare endpoint:\n{e}")
            return

    def _test_sms_send(self):
        """Testeaza SMS send in `RemindersDialog`."""
        cfg = self.get_sms_config()
        default_phone = (self.ed_test_phone.text() or "").strip()
        to, ok = QInputDialog.getText(self, "Test SMS", "Numar destinatar (ex: +407...):", text=default_phone)
        if not ok:
            return
        to = (to or "").strip()
        if not to:
            QMessageBox.warning(self, "Test SMS", "Introdu un numar de telefon.")
            return
        if not is_valid_test_phone(to):
            QMessageBox.warning(
                self,
                "Test SMS",
                "Numar invalid. Foloseste format +40..., 00... sau 07...",
            )
            return
        self.ed_test_phone.setText(to)
        msg, ok2 = QInputDialog.getText(
            self,
            "Test SMS",
            "Mesaj test:",
            text="Test SMS PacientiApp",
        )
        if not ok2:
            return
        msg = (msg or "").strip() or "Test SMS PacientiApp"

        parent = self.parent()
        if hasattr(parent, "send_test_sms_now"):
            parent.send_test_sms_now(to_number=to, message=msg, sms_config=cfg)

    def _send_selected_template_now(self):
        """Trimite selected template now in `RemindersDialog`."""
        key = self.get_manual_template_key()
        labels = {
            "default": "Standard",
            "confirm": "Confirmare",
            "cancel": "Anulare",
            "ortopedie": "Ortopedie",
            "fizioterapie": "Fizioterapie",
        }
        choice = labels.get(key, "Standard")
        ans = QMessageBox.question(
            self,
            "Trimite mesaje",
            f"Trimiti acum mesajele eligibile folosind template-ul: {choice}?",
            QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
            QMessageBox.StandardButton.No,
        )
        if ans != QMessageBox.StandardButton.Yes:
            return
        parent = self.parent()
        if hasattr(parent, "send_reminders_now"):
            parent.send_reminders_now(
                silent=False,
                sms_config=self.get_sms_config(),
                dispatch_mode=self.get_dispatch_mode(),
                trigger_dt=datetime.now(),
                force_template_key=key,
            )

    def get_values(self) -> Tuple[bool, str]:
        """Returneaza values in `RemindersDialog`."""
        enabled = self.cb_enabled.isChecked()
        t = (self.ed_time.text() or "").strip()
        return enabled, t

    def get_sms_config(self) -> Dict[str, Any]:
        """Returneaza SMS config in `RemindersDialog`."""
        return {
            "sms_provider": "SMSMOBILEAPI",
            "smsmobileapi_url": (self.ed_smsmobileapi_url.text() or "").strip(),
            "smsmobileapi_api_key": (self.ed_smsmobileapi_api_key.text() or "").strip(),
            "smsmobileapi_from": (self.ed_smsmobileapi_from.text() or "").strip(),
        }

    def get_test_phone(self) -> str:
        """Returneaza test phone in `RemindersDialog`."""
        return (self.ed_test_phone.text() or "").strip()

    def get_dispatch_mode(self) -> str:
        """Returneaza dispatch mode in `RemindersDialog`."""
        return "local"

    def get_scheduler_mode(self) -> str:
        """Returneaza scheduler mode in `RemindersDialog`."""
        return (self.cb_scheduler_mode.currentData() or "continuous").strip() or "continuous"

    def get_send_rule(self) -> str:
        """Returneaza send rule in `RemindersDialog`."""
        rule = (self.cb_send_rule.currentData() or REMINDER_RULE_DAY_BEFORE).strip()
        valid = {REMINDER_RULE_DAY_BEFORE, REMINDER_RULE_2H_BEFORE, REMINDER_RULE_SAME_DAY}
        return rule if rule in valid else REMINDER_RULE_DAY_BEFORE

    def get_manual_template_key(self) -> str:
        """Returneaza manual template key in `RemindersDialog`."""
        return _normalize_forced_template_key(self.cb_manual_template.currentData()) or "default"

    def get_run_interval_min(self) -> int:
        """Returneaza run interval min in `RemindersDialog`."""
        return int(self.sp_run_interval.value())

    def get_retry_config(self) -> Tuple[int, int]:
        """Returneaza retry config in `RemindersDialog`."""
        return int(self.sp_retry_max.value()), int(self.sp_retry_delay.value())

    def get_templates(self) -> Dict[str, str]:
        """Returneaza templates in `RemindersDialog`."""
        return {
            "default": (self.ed_tpl_default.toPlainText() or "").strip(),
            "confirm": (self.ed_tpl_confirm.toPlainText() or "").strip(),
            "cancel": (self.ed_tpl_cancel.toPlainText() or "").strip(),
            "ortopedie": (self.ed_tpl_ortopedie.toPlainText() or "").strip(),
            "fizioterapie": (self.ed_tpl_fizioterapie.toPlainText() or "").strip(),
        }

    def refresh_monitor_view(self):
        """Gestioneaza monitor view in `RemindersDialog`."""
        snap = get_reminder_monitor_snapshot(limit=30)
        lines = [
            f"Total cu status: {int(snap.get('total_state') or 0)}",
            f"Trimise: {int(snap.get('sent') or 0)}",
            f"In retry: {int(snap.get('retry_wait') or 0)}",
            f"Eroare finala: {int(snap.get('failed_final') or 0)}",
            f"Fara telefon: {int(snap.get('skipped_no_phone') or 0)}",
            "",
            "Ultimele evenimente:",
        ]
        logs = snap.get("recent_logs") if isinstance(snap.get("recent_logs"), list) else []
        if not logs:
            lines.append("- (fara evenimente)")
        else:
            for row in logs[:30]:
                lines.append(
                    f"- {row.get('attempted_at') or '-'} | appt#{row.get('appointment_id') or '-'} | "
                    f"{row.get('status') or '-'} | {row.get('phone') or '-'} | rule={row.get('dispatch_rule') or '-'}"
                )
                err = (row.get("error") or "").strip()
                if err:
                    lines.append(f"  eroare: {err[:180]}")
        self.txt_monitor.setPlainText("\n".join(lines))


# ============================================================
# UI: KPI Report
# ============================================================
class KpiDialog(QDialog):
    def __init__(self, parent=None):
        """Initializeaza dialogul `KpiDialog` si configureaza controalele interfetei."""
        super().__init__(parent)
        self.setWindowTitle("KPI")
        self.resize(520, 360)
        root = QVBoxLayout(self)

        form = QFormLayout()
        self.dt_from = DatePicker("YYYY-MM-DD", show_today=False)
        self.dt_to = DatePicker("YYYY-MM-DD", show_today=False)
        form.addRow("De la:", self.dt_from)
        form.addRow("Pana la:", self.dt_to)
        root.addLayout(form)

        self.btn_calc = QPushButton("Calculeaza")
        apply_std_icon(self.btn_calc, QStyle.StandardPixmap.SP_DialogApplyButton)
        root.addWidget(self.btn_calc)

        self.lbl_out = QLabel("")
        self.lbl_out.setWordWrap(True)
        root.addWidget(self.lbl_out, 1)

        self.btn_calc.clicked.connect(self.calc)

    def calc(self):
        """Calculeaza indicatorii necesari pentru afisarea curenta."""
        d_from = (self.dt_from.text() or "").strip()
        d_to = (self.dt_to.text() or "").strip()
        if d_from and not validate_ymd_or_empty(d_from):
            QMessageBox.warning(self, "Data invalida", "Data 'De la' invalida.")
            return
        if d_to and not validate_ymd_or_empty(d_to):
            QMessageBox.warning(self, "Data invalida", "Data 'Pana la' invalida.")
            return

        conn = get_conn()
        cur = conn.cursor()
        cur.execute("SELECT COUNT(*) FROM pacienti_master")
        total_pat = cur.fetchone()[0]
        cur.execute("SELECT COUNT(*) FROM consulturi")
        total_cons = cur.fetchone()[0]

        cons_in_range = 0
        if d_from or d_to:
            where = []
            args = []
            if d_from:
                where.append("data_consultului >= ?")
                args.append(d_from)
            if d_to:
                where.append("data_consultului <= ?")
                args.append(d_to)
            cur.execute(f"SELECT COUNT(*) FROM consulturi WHERE {' AND '.join(where)}", args)
            cons_in_range = cur.fetchone()[0]
        else:
            cons_in_range = total_cons

        rev_total = 0.0
        inv_count = 0
        if d_from or d_to:
            where = []
            args = []
            if d_from:
                where.append("date >= ?")
                args.append(d_from)
            if d_to:
                where.append("date <= ?")
                args.append(d_to)
            cur.execute(f"SELECT COUNT(*), COALESCE(SUM(total),0) FROM invoices WHERE {' AND '.join(where)}", args)
        else:
            cur.execute("SELECT COUNT(*), COALESCE(SUM(total),0) FROM invoices")
        row = cur.fetchone()
        if row:
            inv_count = row[0]
            rev_total = row[1]

        cur.execute("SELECT COUNT(*) FROM clinical_alerts WHERE active=1")
        alerts_active = cur.fetchone()[0]
        cur.execute("SELECT COUNT(*) FROM consulturi WHERE status_follow_up='Neprogramat'")
        no_show = cur.fetchone()[0]

        # no-show real: control date in past + neprogramat
        today_str = date.today().strftime("%Y-%m-%d")
        cur.execute(
            "SELECT COUNT(*) FROM consulturi WHERE status_follow_up='Neprogramat' AND data_revenire_control IS NOT NULL AND data_revenire_control<>'' AND data_revenire_control < ?",
            (today_str,),
        )
        no_show_real = cur.fetchone()[0]

        # consult duration from patient_flow
        cur.execute("SELECT consult_start, consult_end FROM patient_flow WHERE consult_start IS NOT NULL AND consult_end IS NOT NULL")
        rows_flow = cur.fetchall()
        durations = []
        for r in rows_flow:
            d1 = _parse_dt_any(r[0])
            d2 = _parse_dt_any(r[1])
            if not d1 or not d2:
                continue
            if d2 < d1:
                continue
            durations.append((d2 - d1).total_seconds() / 60.0)
        avg_dur = round(sum(durations) / len(durations), 1) if durations else 0
        conn.close()

        self.lbl_out.setText(
            "\n".join([
                f"Pacienti total: {total_pat}",
                f"Consulturi total: {total_cons}",
                f"Consulturi in interval: {cons_in_range}",
                f"Facturi in interval: {inv_count}",
                f"Venituri in interval: {rev_total}",
                f"Alerte active: {alerts_active}",
                f"Neprezentari (status Neprogramat): {no_show}",
                f"Neprezentari reale (control trecut): {no_show_real}",
                f"Timp mediu consult (minute): {avg_dur}",
            ])
        )


# ============================================================
# UI: Interoperabilitate
# ============================================================
class InteropDialog(QDialog):
    def __init__(self, parent=None):
        """Initializeaza dialogul `InteropDialog` si configureaza controalele interfetei."""
        super().__init__(parent)
        self.setWindowTitle("Interoperabilitate")
        self.resize(420, 220)
        root = QVBoxLayout(self)

        self.btn_fhir = QPushButton("Export FHIR JSON (basic)")
        self.btn_hl7 = QPushButton("Export HL7 (basic)")
        root.addWidget(self.btn_fhir)
        root.addWidget(self.btn_hl7)
        root.addStretch(1)

        self.btn_fhir.clicked.connect(self.export_fhir)
        self.btn_hl7.clicked.connect(self.export_hl7)

    def export_fhir(self):
        """Exporta FHIR in `InteropDialog`."""
        path, _ = QFileDialog.getSaveFileName(self, "Salveaza FHIR JSON", str(APP_DIR / "export_fhir.json"), "JSON (*.json)")
        if not path:
            return
        data = build_fhir_bundle()
        try:
            Path(path).write_text(json.dumps(data, ensure_ascii=True, indent=2), encoding="utf-8")
            QMessageBox.information(self, "OK", "Export FHIR complet.")
        except Exception as e:
            QMessageBox.critical(self, "Eroare", str(e))

    def export_hl7(self):
        """Exporta HL7 in `InteropDialog`."""
        path, _ = QFileDialog.getSaveFileName(self, "Salveaza HL7", str(APP_DIR / "export_hl7.txt"), "Text (*.txt)")
        if not path:
            return
        data = build_hl7_basic()
        try:
            Path(path).write_text(data, encoding="utf-8")
            QMessageBox.information(self, "OK", "Export HL7 complet.")
        except Exception as e:
            QMessageBox.critical(self, "Eroare", str(e))


# ============================================================
# UI: Inventory
# ============================================================
class InventoryMovementsDialog(QDialog):
    def __init__(self, parent=None):
        """Initializeaza dialogul `InventoryMovementsDialog` si configureaza controalele interfetei."""
        super().__init__(parent)
        self.setWindowTitle("Miscari stoc")
        self.resize(820, 520)
        root = QVBoxLayout(self)

        self.tbl = QTableWidget(0, 7)
        self.tbl.setHorizontalHeaderLabels(["ID", "Data", "Produs", "Cantitate", "Tip", "Motiv", "Pacient"])
        self.tbl.setEditTriggers(QAbstractItemView.EditTrigger.NoEditTriggers)
        self.tbl.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
        self.tbl.setSelectionMode(QAbstractItemView.SelectionMode.SingleSelection)
        self.tbl.verticalHeader().setDefaultSectionSize(24)
        h = self.tbl.horizontalHeader()
        h.setSectionResizeMode(QHeaderView.ResizeMode.ResizeToContents)
        self.tbl.setColumnHidden(0, True)
        root.addWidget(self.tbl, 1)

        self.reload()

    def reload(self):
        """Reincarca datele afisate in `InventoryMovementsDialog`."""
        conn = get_conn()
        cur = conn.cursor()
        cur.execute("""
            SELECT m.id, m.ts, i.name, m.qty, m.move_type, m.reason, m.pacient_id
            FROM inventory_movements m
            LEFT JOIN inventory_items i ON i.id = m.item_id
            ORDER BY m.id DESC
        """)
        rows = cur.fetchall()
        conn.close()
        self.tbl.setRowCount(len(rows))
        for i, r in enumerate(rows):
            for j, v in enumerate(r):
                self.tbl.setItem(i, j, QTableWidgetItem("" if v is None else str(v)))


class InventoryAdjustDialog(QDialog):
    def __init__(self, item_name: str, parent=None):
        """Initializeaza dialogul `InventoryAdjustDialog` si configureaza controalele interfetei."""
        super().__init__(parent)
        self.setWindowTitle("Ajustare stoc")
        self.setModal(True)
        self.resize(420, 240)
        root = QVBoxLayout(self)
        root.addWidget(QLabel(f"Produs: {item_name}"))

        form = QFormLayout()
        self.ed_qty = QLineEdit()
        self.ed_reason = QLineEdit()
        self.ed_pid = QLineEdit()
        self.ed_qty.setPlaceholderText("ex: 5 sau -3")
        self.ed_pid.setPlaceholderText("optional: id pacient")
        form.addRow("Cantitate:", self.ed_qty)
        form.addRow("Motiv:", self.ed_reason)
        form.addRow("Pacient ID:", self.ed_pid)
        root.addLayout(form)

        btns = QDialogButtonBox(QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel)
        btns.accepted.connect(self.accept)
        btns.rejected.connect(self.reject)
        root.addWidget(btns)

    def get_values(self) -> Optional[Tuple[float, str, Optional[int]]]:
        """Returneaza values in `InventoryAdjustDialog`."""
        try:
            qty = float(self.ed_qty.text().strip())
        except Exception:
            QMessageBox.warning(self, "Valoare invalida", "Cantitate invalida.")
            return None
        reason = self.ed_reason.text().strip()
        pid = self.ed_pid.text().strip()
        pid_val = None
        if pid:
            if not pid.isdigit():
                QMessageBox.warning(self, "Valoare invalida", "Pacient ID invalid.")
                return None
            pid_val = int(pid)
        return qty, reason, pid_val


class InventoryDialog(QDialog):
    def __init__(self, parent=None):
        """Initializeaza dialogul `InventoryDialog` si configureaza controalele interfetei."""
        super().__init__(parent)
        self.setWindowTitle("Stocuri")
        self.resize(980, 560)
        root = QVBoxLayout(self)

        self.items = SimpleCrudWidget(
            "Lista produse",
            "inventory_items",
            [
                ("Nume", "name"),
                ("UM", "unit"),
                ("Cantitate", "qty"),
                ("Min", "min_qty"),
                ("Locatie", "location"),
                ("Furnizor", "vendor"),
                ("Note", "notes"),
            ],
            [
                {"key": "name", "label": "Nume"},
                {"key": "unit", "label": "UM"},
                {"key": "qty", "label": "Cantitate", "type": "float"},
                {"key": "min_qty", "label": "Cantitate minima", "type": "float"},
                {"key": "location", "label": "Locatie"},
                {"key": "vendor", "label": "Furnizor"},
                {"key": "notes", "label": "Note", "type": "multiline"},
            ],
            patient_id=None,
            can_add_roles=("admin",),
            can_edit_roles=("admin",),
            can_delete_roles=("admin",),
        )
        root.addWidget(self.items, 1)

        btns = QHBoxLayout()
        self.btn_adjust = QPushButton("Ajusteaza stoc")
        self.btn_moves = QPushButton("Miscari stoc")
        self.btn_lots = QPushButton("Loturi/Expirari")
        btns.addWidget(self.btn_adjust)
        btns.addWidget(self.btn_moves)
        btns.addWidget(self.btn_lots)
        btns.addStretch(1)
        root.addLayout(btns)

        self.btn_adjust.clicked.connect(self.adjust_stock)
        self.btn_moves.clicked.connect(self.open_movements)
        self.btn_lots.clicked.connect(self.open_lots)

        if get_current_role() != "admin":
            self.btn_adjust.setEnabled(False)
            self.btn_lots.setEnabled(False)

    def _selected_item(self) -> Optional[Tuple[int, str, float]]:
        """Gestioneaza item in `InventoryDialog`."""
        row = self.items.tbl.currentRow()
        if row < 0:
            return None
        it_id = self.items.tbl.item(row, 0)
        it_name = self.items.tbl.item(row, 1)
        it_qty = self.items.tbl.item(row, 3)
        if not it_id or not it_name:
            return None
        try:
            item_id = int(it_id.text())
        except Exception:
            return None
        try:
            qty = float((it_qty.text() or "0").strip()) if it_qty else 0.0
        except Exception:
            qty = 0.0
        return item_id, it_name.text(), qty

    def adjust_stock(self):
        """Gestioneaza stock in `InventoryDialog`."""
        sel = self._selected_item()
        if not sel:
            return
        item_id, item_name, qty = sel
        d = InventoryAdjustDialog(item_name, parent=self)
        if d.exec() != QDialog.DialogCode.Accepted:
            return
        vals = d.get_values()
        if not vals:
            return
        delta, reason, pid = vals
        new_qty = qty + delta
        ts_local = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        conn = get_conn()
        cur = conn.cursor()
        sets = ["qty=?"]
        vals_item: List[Any] = [new_qty]
        if table_has_column("inventory_items", "updated_at"):
            sets.append("updated_at=?")
            vals_item.append(now_ts())
        if table_has_column("inventory_items", "device_id"):
            sets.append("device_id=?")
            vals_item.append(get_device_id())
        if table_has_column("inventory_items", "deleted"):
            sets.append("deleted=0")
        vals_item.append(int(item_id))
        cur.execute(f"UPDATE inventory_items SET {', '.join(sets)} WHERE id=?", tuple(vals_item))

        move_cols = ["item_id", "ts", "qty", "move_type", "reason", "pacient_id"]
        move_vals: List[Any] = [
            int(item_id),
            ts_local,
            float(delta),
            "in" if delta >= 0 else "out",
            reason,
            pid,
        ]
        if table_has_column("inventory_movements", "sync_id"):
            move_cols.append("sync_id")
            move_vals.append(uuid.uuid4().hex)
        if table_has_column("inventory_movements", "updated_at"):
            move_cols.append("updated_at")
            move_vals.append(now_ts())
        if table_has_column("inventory_movements", "deleted"):
            move_cols.append("deleted")
            move_vals.append(0)
        if table_has_column("inventory_movements", "device_id"):
            move_cols.append("device_id")
            move_vals.append(get_device_id())
        cur.execute(
            f"INSERT INTO inventory_movements({', '.join(move_cols)}) VALUES ({', '.join(['?'] * len(move_cols))})",
            tuple(move_vals),
        )
        conn.commit()
        conn.close()
        try:
            log_action("inventory_adjust", f"item_id={item_id}; delta={delta}; pid={pid or ''}")
        except Exception:
            pass
        self.items.load_rows()

    def open_movements(self):
        """Deschide movements in `InventoryDialog`."""
        d = InventoryMovementsDialog(parent=self)
        d.exec()

    def open_lots(self):
        """Deschide lots in `InventoryDialog`."""
        sel = self._selected_item()
        if not sel:
            QMessageBox.information(self, "Info", "Selecteaza un produs.")
            return
        item_id, item_name, _ = sel
        d = InventoryLotsDialog(item_id, item_name, parent=self)
        d.exec()


class InventoryLotsDialog(QDialog):
    def __init__(self, item_id: int, item_name: str, parent=None):
        """Initializeaza dialogul `InventoryLotsDialog` si configureaza controalele interfetei."""
        super().__init__(parent)
        self.setWindowTitle(f"Loturi - {item_name}")
        self.resize(720, 420)
        root = QVBoxLayout(self)
        self.crud = SimpleCrudWidget(
            f"Loturi pentru {item_name}",
            "inventory_lots",
            [
                ("Lot", "lot"),
                ("Expira", "expiry_date"),
                ("Cantitate", "qty"),
                ("Note", "notes"),
            ],
            [
                {"key": "item_id", "label": "Item ID"},
                {"key": "lot", "label": "Lot"},
                {"key": "expiry_date", "label": "Expira", "type": "date"},
                {"key": "qty", "label": "Cantitate", "type": "float"},
                {"key": "notes", "label": "Note", "type": "multiline"},
            ],
            patient_id=None,
            insert_defaults={"item_id": item_id},
            filter_sql="item_id=?",
            filter_args=(item_id,),
            can_add_roles=("admin",),
            can_edit_roles=("admin",),
            can_delete_roles=("admin",),
        )
        root.addWidget(self.crud, 1)


# ============================================================
# UI: Clinic settings
# ============================================================
class ClinicSettingsDialog(QDialog):
    def __init__(self, parent=None):
        """Initializeaza dialogul `ClinicSettingsDialog` si configureaza controalele interfetei."""
        super().__init__(parent)
        self.setWindowTitle("Setari clinica")
        self.setModal(True)
        self.resize(520, 260)
        root = QVBoxLayout(self)
        form = QFormLayout()

        self.ed_name = QLineEdit()
        self.ed_addr = QLineEdit()
        self.ed_phone = QLineEdit()
        self.ed_logo = QLineEdit()
        self.ed_cat_name_thr = QLineEdit()
        self.ed_cat_name_thr.setPlaceholderText("ex: 0.88")
        self.ed_cat_name_thr.setToolTip("Prag pentru potrivire nume similar pe aceeasi categorie la sync download (0.50 - 1.00)")
        btn_logo = QPushButton("Alege")
        btn_logo.setObjectName("secondary")
        btn_logo.setMinimumWidth(84)
        apply_std_icon(btn_logo, QStyle.StandardPixmap.SP_DialogOpenButton)
        row = QWidget()
        row_l = QHBoxLayout(row)
        row_l.setContentsMargins(0, 0, 0, 0)
        row_l.setSpacing(8)
        row_l.addWidget(self.ed_logo, 1)
        row_l.addWidget(btn_logo)
        form.addRow("Nume clinica:", self.ed_name)
        form.addRow("Adresa:", self.ed_addr)
        form.addRow("Telefon:", self.ed_phone)
        form.addRow("Prag similaritate categorie+nume:", self.ed_cat_name_thr)
        form.addRow("Logo (fisier):", row)
        root.addLayout(form)

        def _browse():
            """Gestioneaza operatia `_browse` in `ClinicSettingsDialog`."""
            path, _ = QFileDialog.getOpenFileName(self, "Alege logo", "", "Imagini (*.png *.jpg *.jpeg *.bmp)")
            if path:
                self.ed_logo.setText(path)

        btn_logo.clicked.connect(_browse)

        btns = QDialogButtonBox(QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel)
        btns.accepted.connect(self.accept)
        btns.rejected.connect(self.reject)
        root.addWidget(btns)

        cur = get_clinic_settings()
        self.ed_name.setText(cur.get("clinic_name") or "")
        self.ed_addr.setText(cur.get("clinic_address") or "")
        self.ed_phone.setText(cur.get("clinic_phone") or "")
        self.ed_logo.setText(cur.get("clinic_logo") or "")
        self.ed_cat_name_thr.setText(cur.get("category_name_match_threshold") or f"{CATEGORY_NAME_MATCH_THRESHOLD:.2f}")

    def get_values(self) -> Dict[str, str]:
        """Returneaza values in `ClinicSettingsDialog`."""
        return {
            "clinic_name": self.ed_name.text().strip(),
            "clinic_address": self.ed_addr.text().strip(),
            "clinic_phone": self.ed_phone.text().strip(),
            "clinic_logo": self.ed_logo.text().strip(),
            "category_name_match_threshold": self.ed_cat_name_thr.text().strip(),
        }


# ============================================================
# UI: Domiciliu picker
# ============================================================
class DomiciliuPickerDialog(QDialog):
    def __init__(self, current_value: str = "", parent=None):
        """Initializeaza dialogul `DomiciliuPickerDialog` si configureaza controalele interfetei."""
        super().__init__(parent)
        self.setWindowTitle("Selectie domiciliu")
        self.resize(520, 220)

        root = QVBoxLayout(self)
        form = QFormLayout()
        root.addLayout(form)

        self.cb_county = QComboBox()
        self.cb_county.setMinimumWidth(260)
        form.addRow("Judet", wrap_selector_widget(self.cb_county, self))

        self.cb_locality = QComboBox()
        self.cb_locality.setEditable(True)
        self.cb_locality.setMinimumWidth(340)
        self.cb_locality.setInsertPolicy(QComboBox.InsertPolicy.NoInsert)
        self.cb_locality.setSizeAdjustPolicy(QComboBox.SizeAdjustPolicy.AdjustToContents)
        self.cb_locality.lineEdit().setPlaceholderText("Alege sau scrie localitatea")
        form.addRow("Localitate", wrap_selector_widget(self.cb_locality, self))

        self.ed_preview = QLineEdit()
        self.ed_preview.setReadOnly(True)
        self.ed_preview.setPlaceholderText("Ex: Cluj-Napoca, Cluj")
        form.addRow("Domiciliu", self.ed_preview)

        self.lbl_hint = QLabel(
            "Lista este clasificata pe judete. Daca lipsesc localitati, foloseste Actualizeaza lista online."
        )
        self.lbl_hint.setObjectName("muted")
        self.lbl_hint.setWordWrap(True)
        root.addWidget(self.lbl_hint)

        row = QHBoxLayout()
        self.btn_refresh = QPushButton("Actualizeaza lista online")
        apply_std_icon(self.btn_refresh, QStyle.StandardPixmap.SP_BrowserReload)
        row.addWidget(self.btn_refresh)
        row.addStretch(1)
        root.addLayout(row)

        buttons = QDialogButtonBox(
            QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel
        )
        root.addWidget(buttons)

        self._county_localities: Dict[str, List[str]] = {}
        self._current_value = str(current_value or "").strip()

        counties = get_ro_counties()
        self.cb_county.addItems(counties)
        self.cb_county.currentIndexChanged.connect(self._on_county_changed)
        self.cb_locality.currentTextChanged.connect(self._on_locality_changed)
        self.btn_refresh.clicked.connect(self._refresh_online)
        buttons.accepted.connect(self.accept)
        buttons.rejected.connect(self.reject)

        self._prefill_current_value()
        force_ascii_ui_texts(self)

    def _refresh_online(self):
        """Gestioneaza online in `DomiciliuPickerDialog`."""
        pd = QProgressDialog("Actualizez lista de localitati...", "Anuleaza", 0, 100, self)
        pd.setWindowTitle("Localitati RO")
        pd.setWindowModality(Qt.WindowModality.WindowModal)
        pd.setAutoClose(False)
        pd.setAutoReset(False)
        pd.show()

        def pg(p, m=""):
            """Actualizeaza progresul operatiei in curs (helper intern pentru `_refresh_online`)."""
            pd.setValue(int(max(0, min(100, p))))
            if m:
                pd.setLabelText(str(m))
            QApplication.processEvents()

        try:
            cnt = ensure_ro_localities_dataset(
                progress_cb=pg,
                cancelled_cb=lambda: pd.wasCanceled(),
                force_refresh=True,
                allow_fallback=False,
            )
            pd.close()
            self.cb_county.blockSignals(True)
            self.cb_county.clear()
            self.cb_county.addItems(get_ro_counties())
            self.cb_county.blockSignals(False)
            self._prefill_current_value()
            QMessageBox.information(self, "Localitati", f"Lista actualizata. Total localitati: {cnt}")
        except Exception as e:
            pd.close()
            QMessageBox.warning(self, "Localitati", f"Nu pot actualiza lista:\n{e}")

    def _prefill_current_value(self):
        """Gestioneaza current value in `DomiciliuPickerDialog`."""
        counties = [self.cb_county.itemText(i) for i in range(self.cb_county.count())]
        if not counties:
            self._set_localities([])
            return

        current = self._current_value
        pref_county = ""
        pref_locality = ""

        if current:
            parts = [p.strip() for p in current.split(",") if p.strip()]
            if len(parts) >= 2:
                pref_locality = parts[0]
                pref_county = parts[-1]
            elif len(parts) == 1:
                pref_locality = parts[0]

        idx = -1
        if pref_county:
            norm_target = _norm(pref_county)
            for i, c in enumerate(counties):
                if _norm(c) == norm_target:
                    idx = i
                    break
        if idx < 0:
            idx = 0

        self.cb_county.setCurrentIndex(idx)
        if pref_locality:
            self.cb_locality.setCurrentText(pref_locality)
        self._on_locality_changed(self.cb_locality.currentText())

    def _set_localities(self, items: List[str]):
        """Seteaza localities in `DomiciliuPickerDialog`."""
        self.cb_locality.blockSignals(True)
        prev = (self.cb_locality.currentText() or "").strip()
        self.cb_locality.clear()
        self.cb_locality.addItems(items)
        if prev:
            self.cb_locality.setCurrentText(prev)
        self.cb_locality.blockSignals(False)

        model = QStringListModel(items, self.cb_locality)
        comp = QCompleter(model, self.cb_locality)
        comp.setCaseSensitivity(Qt.CaseSensitivity.CaseInsensitive)
        comp.setFilterMode(Qt.MatchFlag.MatchContains)
        comp.setCompletionMode(QCompleter.CompletionMode.PopupCompletion)
        self.cb_locality.setCompleter(comp)

    def _on_county_changed(self):
        """Gestioneaza evenimentul county changed in `DomiciliuPickerDialog`."""
        county = (self.cb_county.currentText() or "").strip()
        if not county:
            self._set_localities([])
            self._on_locality_changed(self.cb_locality.currentText())
            return
        if county not in self._county_localities:
            self._county_localities[county] = get_ro_localities_by_county(county)
        localities = self._county_localities.get(county, [])
        self._set_localities(localities)

        seat = get_ro_county_seat(county)
        chosen = ""
        if seat and localities:
            seat_norm = _norm(seat)
            for loc in localities:
                if _norm(loc) == seat_norm:
                    chosen = loc
                    break
        if not chosen and seat:
            chosen = seat
        if not chosen and localities:
            chosen = localities[0]
        if chosen:
            self.cb_locality.setCurrentText(chosen)

        self._on_locality_changed(self.cb_locality.currentText())

    def _on_locality_changed(self, txt: str):
        """Gestioneaza evenimentul locality changed in `DomiciliuPickerDialog`."""
        county = (self.cb_county.currentText() or "").strip()
        locality = str(txt or "").strip()
        if locality and county:
            self.ed_preview.setText(f"{locality}, {county}")
        elif locality:
            self.ed_preview.setText(locality)
        else:
            self.ed_preview.setText("")

    def get_value(self) -> str:
        """Returneaza value in `DomiciliuPickerDialog`."""
        return (self.ed_preview.text() or "").strip()


# ============================================================
# UI: Locations
# ============================================================
class LocationsDialog(QDialog):
    def __init__(self, parent=None):
        """Initializeaza dialogul `LocationsDialog` si configureaza controalele interfetei."""
        super().__init__(parent)
        self.setWindowTitle("Sedii")
        self.resize(720, 420)
        root = QVBoxLayout(self)

        self.crud = SimpleCrudWidget(
            "Sedii",
            "locations",
            [
                ("Nume", "name"),
                ("Adresa", "address"),
                ("Activ", "active"),
            ],
            [
                {"key": "name", "label": "Nume"},
                {"key": "address", "label": "Adresa"},
                {"key": "active", "label": "Activ", "type": "bool"},
            ],
            patient_id=None,
            can_add_roles=("admin",),
            can_edit_roles=("admin",),
            can_delete_roles=("admin",),
        )
        root.addWidget(self.crud, 1)

        btn_row = QHBoxLayout()
        self.btn_set_current = QPushButton("Seteaza ca sediu curent")
        apply_std_icon(self.btn_set_current, QStyle.StandardPixmap.SP_DialogApplyButton)
        btn_row.addWidget(self.btn_set_current)
        btn_row.addStretch(1)
        root.addLayout(btn_row)

        self.btn_set_current.clicked.connect(self.set_current)

    def set_current(self):
        """Seteaza current in `LocationsDialog`."""
        row = self.crud.tbl.currentRow()
        if row < 0:
            return
        it = self.crud.tbl.item(row, 0)
        if not it:
            return
        try:
            loc_id = int(it.text())
        except Exception:
            return
        set_current_location_id(loc_id)
        QMessageBox.information(self, "OK", "Sediul curent a fost actualizat.")


# ============================================================
# UI: Appointments
# ============================================================
class AppointmentQrDialog(QDialog):
    def __init__(self, code: str, parent=None):
        """Initializeaza dialogul `AppointmentQrDialog` si configureaza controalele interfetei."""
        super().__init__(parent)
        self.setWindowTitle("Check-in")
        self.resize(260, 300)
        root = QVBoxLayout(self)
        lbl = QLabel(f"Cod: {code}")
        root.addWidget(lbl)
        pix = generate_qr_pixmap(code, size=200)
        img = QLabel()
        img.setPixmap(pix)
        img.setAlignment(Qt.AlignmentFlag.AlignCenter)
        root.addWidget(img, 1)


class AppointmentsDialog(QDialog):
    def __init__(self, parent=None):
        """Initializeaza pagina Programari, filtrele, lista si actiunile bulk/SMS."""
        super().__init__(parent)
        self.setWindowTitle("Programari")
        self.resize(1220, 620)
        root = QVBoxLayout(self)

        content_row = QHBoxLayout()
        content_row.setSpacing(12)
        root.addLayout(content_row, 1)

        left_panel = QWidget()
        left_root = QVBoxLayout(left_panel)
        left_root.setContentsMargins(0, 0, 0, 0)
        left_root.setSpacing(8)
        left_panel.setMaximumWidth(430)

        cal_group = QGroupBox("Calendar programari")
        cal_group_root = QVBoxLayout(cal_group)
        cal_group_root.setContentsMargins(8, 8, 8, 8)
        cal_group_root.setSpacing(8)
        cal_box = QVBoxLayout()
        self.cal = QCalendarWidget()
        self.cal.setGridVisible(True)
        self.cal.setVerticalHeaderFormat(QCalendarWidget.VerticalHeaderFormat.NoVerticalHeader)
        self.cal.setStyleSheet(
            "QCalendarWidget QAbstractItemView {"
            "selection-background-color: #cfe8ff;"
            "gridline-color: #dfe3e8;"
            "padding: 6px;"
            "}"
            "QCalendarWidget QToolButton { font-weight: 600; }"
        )
        self.lbl_cal_month = QLabel("")
        self.lbl_cal_month.setStyleSheet("font-weight: 600;")
        cal_box.addWidget(self.lbl_cal_month)
        cal_box.addWidget(self.cal)
        self.btn_filter = QPushButton("Filtreaza dupa data")
        self.btn_reset = QPushButton("Reset")
        cal_btn_row = QHBoxLayout()
        cal_btn_row.addWidget(self.btn_filter)
        cal_btn_row.addWidget(self.btn_reset)
        cal_btn_row.addStretch(1)
        cal_box.addLayout(cal_btn_row)
        cal_group_root.addLayout(cal_box)
        left_root.addWidget(cal_group, 0)

        filter_group = QGroupBox("Filtrare rapida")
        filter_root = QVBoxLayout(filter_group)
        filter_root.setContentsMargins(8, 8, 8, 8)
        filter_root.setSpacing(6)

        self.ed_quick_search = QLineEdit()
        self.ed_quick_search.setPlaceholderText("Cauta dupa nume pacient / telefon...")
        filter_root.addWidget(self.ed_quick_search)

        med_stat_row = QHBoxLayout()
        med_stat_row.setSpacing(6)
        self.cb_filter_medic = QComboBox()
        self.cb_filter_medic.addItem("Medic: toti", "")
        self.cb_filter_status = QComboBox()
        self.cb_filter_status.addItem("Status: toate", "")
        for st in ["Programat", "Confirmat", "Anulat", "Realizat", "Check-in"]:
            self.cb_filter_status.addItem(st, st)
        med_stat_row.addWidget(wrap_selector_widget(self.cb_filter_medic, self), 1)
        med_stat_row.addWidget(wrap_selector_widget(self.cb_filter_status, self), 1)
        filter_root.addLayout(med_stat_row)

        range_row = QHBoxLayout()
        range_row.setSpacing(6)
        self.dt_filter_from = DatePicker("De la (YYYY-MM-DD)", show_today=False)
        self.dt_filter_to = DatePicker("Pana la (YYYY-MM-DD)", show_today=False)
        range_row.addWidget(self.dt_filter_from, 1)
        range_row.addWidget(self.dt_filter_to, 1)
        filter_root.addLayout(range_row)

        filter_btn_row = QHBoxLayout()
        self.btn_apply_filters = QPushButton("Aplica filtre")
        self.btn_clear_filters = QPushButton("Reset filtre")
        filter_btn_row.addWidget(self.btn_apply_filters)
        filter_btn_row.addWidget(self.btn_clear_filters)
        filter_btn_row.addStretch(1)
        filter_root.addLayout(filter_btn_row)

        sms_pick_group = QGroupBox("Selectie SMS (bife vizibile)")
        sms_pick_root = QVBoxLayout(sms_pick_group)
        sms_pick_root.setContentsMargins(8, 8, 8, 8)
        sms_pick_root.setSpacing(6)
        self.lbl_sms_pick_info = QLabel("Bifeaza programarile pentru SMS sau actiuni bulk.")
        self.lbl_sms_pick_info.setStyleSheet("color: #4b5563;")
        sms_pick_root.addWidget(self.lbl_sms_pick_info)
        self.sms_pick_scroll = QScrollArea()
        self.sms_pick_scroll.setWidgetResizable(True)
        self.sms_pick_scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.sms_pick_scroll.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
        self.sms_pick_wrap = QWidget()
        self.sms_pick_list = QVBoxLayout(self.sms_pick_wrap)
        self.sms_pick_list.setContentsMargins(0, 0, 0, 0)
        self.sms_pick_list.setSpacing(4)
        self.sms_pick_scroll.setWidget(self.sms_pick_wrap)
        sms_pick_root.addWidget(self.sms_pick_scroll, 1)
        sms_pick_btns = QHBoxLayout()
        self.btn_sms_pick_all = QPushButton("Bifeaza toate")
        self.btn_sms_pick_none = QPushButton("Debifeaza toate")
        sms_pick_btns.addWidget(self.btn_sms_pick_all)
        sms_pick_btns.addWidget(self.btn_sms_pick_none)
        sms_pick_btns.addStretch(1)
        sms_pick_root.addLayout(sms_pick_btns)
        monitor_group = QGroupBox("Monitor SMS (azi)")
        monitor_root = QVBoxLayout(monitor_group)
        monitor_root.setContentsMargins(8, 8, 8, 8)
        monitor_root.setSpacing(4)
        self.lbl_sms_monitor_sent = QLabel("Trimise: 0")
        self.lbl_sms_monitor_failed = QLabel("Esuate: 0")
        self.lbl_sms_monitor_no_phone = QLabel("Fara telefon: 0")
        self.lbl_sms_monitor_opt_out = QLabel("SMS dezactivat: 0")
        self.lbl_sms_monitor_blocked = QLabel("Blocari confirmare: 0")
        monitor_root.addWidget(self.lbl_sms_monitor_sent)
        monitor_root.addWidget(self.lbl_sms_monitor_failed)
        monitor_root.addWidget(self.lbl_sms_monitor_no_phone)
        monitor_root.addWidget(self.lbl_sms_monitor_opt_out)
        monitor_root.addWidget(self.lbl_sms_monitor_blocked)
        self.btn_sms_monitor_refresh = QPushButton("Refresh monitor")
        monitor_root.addWidget(self.btn_sms_monitor_refresh)
        left_root.addWidget(monitor_group, 0)
        left_root.addStretch(1)
        content_row.addWidget(left_panel, 0)

        list_group = QGroupBox("Lista programari")
        list_group_root = QVBoxLayout(list_group)
        list_group_root.setContentsMargins(8, 8, 8, 8)
        list_group_root.setSpacing(8)
        self.crud = SimpleCrudWidget(
            "",
            "appointments",
            [
                ("Pacient ID", "pacient_id"),
                ("Data", "date"),
                ("Ora", "time"),
                ("Durata", "duration_min"),
                ("Medic", "medic"),
                ("Status", "status"),
                ("Email", "reminder_email"),
                ("SMS", "reminder_sms"),
                ("Check-in", "checkin_code"),
            ],
            [
                {"key": "pacient_id", "label": "Pacient ID"},
                {"key": "date", "label": "Data", "type": "date"},
                {"key": "time", "label": "Ora (HH:MM)"},
                {"key": "duration_min", "label": "Durata (min)", "type": "int"},
                {"key": "medic", "label": "Medic"},
                {"key": "status", "label": "Status", "type": "choice", "choices": ["Programat", "Confirmat", "Anulat", "Realizat", "Check-in"]},
                {"key": "reminder_email", "label": "Email"},
                {"key": "reminder_sms", "label": "Telefon SMS"},
                {"key": "checkin_code", "label": "Check-in"},
                {"key": "notes", "label": "Note", "type": "multiline"},
                {"key": "location_id", "label": "Sediu ID"},
            ],
            patient_id=None,
            insert_defaults={
                "checkin_code": _gen_code,
                "location_id": lambda: get_current_location_id(),
            },
            can_add_roles=("admin", "receptie"),
            can_edit_roles=("admin", "receptie"),
            can_delete_roles=("admin",),
            on_mutation=self._on_appointment_crud_mutation,
        )
        sms_pick_group.setMinimumWidth(300)
        sms_pick_group.setMaximumWidth(420)
        list_row = QHBoxLayout()
        list_row.setSpacing(10)
        list_row.addWidget(self.crud, 1)
        list_row.addWidget(sms_pick_group, 0)
        list_group_root.addLayout(list_row, 1)
        list_group_root.addWidget(filter_group, 0)
        content_row.addWidget(list_group, 1)

        btns = QHBoxLayout()
        btns.setSpacing(10)
        self.btn_qr = QPushButton("Afiseaza QR")
        self.btn_email = QPushButton("Trimite email")
        self.cb_sms_template = QComboBox()
        self.cb_sms_template.addItem("Template Confirmare", "confirm")
        self.cb_sms_template.addItem("Template Anulare", "cancel")
        self.cb_sms_template.addItem("Template Ortopedie", "ortopedie")
        self.cb_sms_template.addItem("Template Fizioterapie", "fizioterapie")
        manual_key = _normalize_forced_template_key(get_setting("appointments_sms_template_key", "confirm") or "confirm") or "confirm"
        idx_tpl = self.cb_sms_template.findData(manual_key)
        self.cb_sms_template.setCurrentIndex(idx_tpl if idx_tpl >= 0 else 0)
        self.btn_sms = QPushButton("Trimite SMS selectate")
        self.btn_checkin = QPushButton("Check-in")
        self.cb_bulk_status = QComboBox()
        self.cb_bulk_status.addItem("Confirmat", "Confirmat")
        self.cb_bulk_status.addItem("Anulat", "Anulat")
        self.cb_bulk_status.addItem("Realizat", "Realizat")
        self.cb_bulk_status.addItem("Check-in", "Check-in")
        self.btn_bulk_status = QPushButton("Bulk update status")
        self.ed_bulk_medic = QLineEdit()
        self.ed_bulk_medic.setPlaceholderText("Medic nou pentru selectie")
        self.btn_bulk_medic = QPushButton("Bulk seteaza medic")
        self.spin_bulk_shift_days = QSpinBox()
        self.spin_bulk_shift_days.setRange(-365, 365)
        self.spin_bulk_shift_days.setValue(0)
        self.spin_bulk_shift_days.setToolTip("Numar zile: negativ muta in trecut, pozitiv in viitor.")
        self.btn_bulk_shift_date = QPushButton("Bulk muta data")

        action_group = QGroupBox("Actiuni programare")
        action_group_root = QHBoxLayout(action_group)
        action_group_root.setContentsMargins(8, 8, 8, 8)
        action_group_root.setSpacing(8)
        action_group_root.addWidget(self.btn_qr)
        action_group_root.addWidget(self.btn_email)
        action_group_root.addWidget(self.btn_checkin)
        action_group_root.addStretch(1)

        sms_group = QGroupBox("SMS Programari")
        sms_group_root = QHBoxLayout(sms_group)
        sms_group_root.setContentsMargins(8, 8, 8, 8)
        sms_group_root.setSpacing(8)
        sms_group_root.addWidget(QLabel("Template:"))
        sms_group_root.addWidget(wrap_selector_widget(self.cb_sms_template, self))
        sms_group_root.addWidget(self.btn_sms)
        self.btn_sms_audit = QPushButton("Audit SMS")
        sms_group_root.addWidget(self.btn_sms_audit)
        sms_group_root.addStretch(1)

        bulk_group = QGroupBox("Actiuni bulk")
        bulk_group_root = QVBoxLayout(bulk_group)
        bulk_group_root.setContentsMargins(8, 8, 8, 8)
        bulk_group_root.setSpacing(8)
        row_bulk_status = QHBoxLayout()
        row_bulk_status.addWidget(QLabel("Status:"))
        row_bulk_status.addWidget(wrap_selector_widget(self.cb_bulk_status, self), 1)
        row_bulk_status.addWidget(self.btn_bulk_status)
        bulk_group_root.addLayout(row_bulk_status)

        row_bulk_medic = QHBoxLayout()
        row_bulk_medic.addWidget(QLabel("Medic:"))
        row_bulk_medic.addWidget(self.ed_bulk_medic, 1)
        row_bulk_medic.addWidget(self.btn_bulk_medic)
        bulk_group_root.addLayout(row_bulk_medic)

        row_bulk_date = QHBoxLayout()
        row_bulk_date.addWidget(QLabel("Muta data cu zile:"))
        row_bulk_date.addWidget(self.spin_bulk_shift_days, 0)
        row_bulk_date.addWidget(self.btn_bulk_shift_date)
        row_bulk_date.addStretch(1)
        bulk_group_root.addLayout(row_bulk_date)

        btns.addWidget(action_group, 3)
        btns.addWidget(sms_group, 4)
        btns.addWidget(bulk_group, 4)
        btns.addStretch(1)
        root.addLayout(btns)

        self.btn_qr.clicked.connect(self.show_qr)
        self.btn_email.clicked.connect(self.send_email)
        self.btn_sms.clicked.connect(self.send_sms)
        self.btn_checkin.clicked.connect(self.mark_checkin)
        self.btn_filter.clicked.connect(self.filter_by_date)
        self.btn_reset.clicked.connect(self.reset_filter)
        self.btn_apply_filters.clicked.connect(self.apply_filters)
        self.btn_clear_filters.clicked.connect(self.reset_filter)
        self.btn_bulk_status.clicked.connect(self.bulk_update_status)
        self.btn_bulk_medic.clicked.connect(self.bulk_set_medic)
        self.btn_bulk_shift_date.clicked.connect(self.bulk_shift_date)
        self.ed_quick_search.returnPressed.connect(self.apply_filters)
        self.cb_filter_medic.currentIndexChanged.connect(self.apply_filters)
        self.cb_filter_status.currentIndexChanged.connect(self.apply_filters)
        self.btn_sms_pick_all.clicked.connect(self._sms_pick_check_all)
        self.btn_sms_pick_none.clicked.connect(self._sms_pick_uncheck_all)
        self.btn_sms_monitor_refresh.clicked.connect(self.refresh_sms_monitor_dashboard)
        self.btn_sms_audit.clicked.connect(self.open_sms_audit_dialog)
        self.cb_sms_template.currentIndexChanged.connect(self._apply_sms_selection_guard)
        self.cal.currentPageChanged.connect(self._update_cal_month_label)
        apply_std_icon(self.btn_apply_filters, QStyle.StandardPixmap.SP_DialogApplyButton)
        apply_std_icon(self.btn_clear_filters, QStyle.StandardPixmap.SP_DialogResetButton)
        apply_std_icon(self.btn_bulk_status, QStyle.StandardPixmap.SP_DialogApplyButton)
        apply_std_icon(self.btn_bulk_medic, QStyle.StandardPixmap.SP_DialogApplyButton)
        apply_std_icon(self.btn_bulk_shift_date, QStyle.StandardPixmap.SP_DialogApplyButton)
        apply_std_icon(self.btn_sms_pick_all, QStyle.StandardPixmap.SP_DialogYesButton)
        apply_std_icon(self.btn_sms_pick_none, QStyle.StandardPixmap.SP_DialogNoButton)
        apply_std_icon(self.btn_sms_monitor_refresh, QStyle.StandardPixmap.SP_BrowserReload)
        apply_std_icon(self.btn_sms_audit, QStyle.StandardPixmap.SP_FileDialogDetailedView)
        self._update_cal_month_label(self.cal.yearShown(), self.cal.monthShown())
        self._marked_dates = set()
        self._confirm_sms_sent_ids = set()
        self._sms_checked_ids = set()
        self._sms_checks_syncing = False
        self._filters_syncing = False
        self._sms_picker_checks: Dict[int, QCheckBox] = {}
        self._sms_picker_order: List[int] = []
        self._wrap_crud_loader()
        self._reload_filter_medic_values()
        self._refresh_confirm_sms_cache()
        self._sync_confirm_sms_status_column()
        self._sync_sms_checkboxes()
        self._apply_sms_selection_guard()
        self._refresh_calendar_marks()
        self.refresh_sms_monitor_dashboard()
        self._auto_import_controls()
        self._apply_bulk_action_permissions()
        self._install_shortcuts()

    def _update_cal_month_label(self, year: int, month: int):
        """Actualizeaza cal month label in `AppointmentsDialog`."""
        try:
            qd = QDate(year, month, 1)
            self.lbl_cal_month.setText(qd.toString("MMMM yyyy"))
        except Exception:
            self.lbl_cal_month.setText(f"{month:02d}/{year}")

    def _reload_filter_medic_values(self):
        """Reincarca filter medic values in `AppointmentsDialog`."""
        prev = (self.cb_filter_medic.currentData() or "").strip()
        vals: List[str] = []
        try:
            conn = get_conn()
            cur = conn.cursor()
            where = ["TRIM(COALESCE(medic,'')) <> ''"]
            if table_has_column("appointments", "deleted"):
                where.append("COALESCE(deleted,0)=0")
            cur.execute(
                f"""
                SELECT DISTINCT TRIM(COALESCE(medic,'')) AS medic
                FROM appointments
                WHERE {' AND '.join(where)}
                ORDER BY medic COLLATE NOCASE ASC
                """
            )
            vals = [str(r[0]).strip() for r in cur.fetchall() if str(r[0] or "").strip()]
            conn.close()
        except Exception:
            vals = []

        self._filters_syncing = True
        try:
            self.cb_filter_medic.clear()
            self.cb_filter_medic.addItem("Medic: toti", "")
            for medic_name in vals:
                self.cb_filter_medic.addItem(medic_name, medic_name)
            idx_prev = self.cb_filter_medic.findData(prev)
            self.cb_filter_medic.setCurrentIndex(idx_prev if idx_prev >= 0 else 0)
        finally:
            self._filters_syncing = False

    def _parse_filter_date_text(self, raw: str, end_of_month: bool = False) -> Tuple[bool, Optional[str]]:
        """Parseaza filter date text in `AppointmentsDialog`."""
        txt = (raw or "").strip()
        if not txt:
            return True, None
        kind, val = _parse_date_or_month(txt)
        if kind == "date" and isinstance(val, date):
            return True, val.strftime("%Y-%m-%d")
        if kind == "month" and isinstance(val, tuple) and len(val) == 2:
            year = int(val[0])
            month = int(val[1])
            if end_of_month:
                if month >= 12:
                    d = date(year + 1, 1, 1) - timedelta(days=1)
                else:
                    d = date(year, month + 1, 1) - timedelta(days=1)
            else:
                d = date(year, month, 1)
            return True, d.strftime("%Y-%m-%d")
        return False, None

    def apply_filters(self):
        """Aplica filtre rapide si avansate pe lista de programari."""
        if self._filters_syncing:
            return

        quick = (self.ed_quick_search.text() or "").strip().lower()
        medic = (self.cb_filter_medic.currentData() or "").strip()
        status = (self.cb_filter_status.currentData() or "").strip()

        ok_from, from_ymd = self._parse_filter_date_text(self.dt_filter_from.text(), end_of_month=False)
        ok_to, to_ymd = self._parse_filter_date_text(self.dt_filter_to.text(), end_of_month=True)
        if not ok_from:
            QMessageBox.warning(self, "Filtre programari", "Data 'De la' nu este valida.")
            return
        if not ok_to:
            QMessageBox.warning(self, "Filtre programari", "Data 'Pana la' nu este valida.")
            return
        if from_ymd and to_ymd and from_ymd > to_ymd:
            QMessageBox.warning(self, "Filtre programari", "Interval invalid: 'De la' este dupa 'Pana la'.")
            return

        clauses: List[str] = []
        args: List[Any] = []
        if from_ymd:
            clauses.append("date >= ?")
            args.append(from_ymd)
        if to_ymd:
            clauses.append("date <= ?")
            args.append(to_ymd)
        if medic:
            clauses.append("TRIM(COALESCE(medic,'')) = ?")
            args.append(medic)
        if status:
            clauses.append("TRIM(COALESCE(status,'')) = ?")
            args.append(status)
        if quick:
            like = f"%{quick}%"
            clauses.append(
                "("
                "LOWER(COALESCE(reminder_sms,'')) LIKE ? "
                "OR LOWER(COALESCE(reminder_email,'')) LIKE ? "
                "OR CAST(COALESCE(pacient_id,'') AS TEXT) LIKE ? "
                "OR pacient_id IN ("
                "  SELECT id FROM pacienti_master "
                "  WHERE LOWER(COALESCE(nume_prenume,'')) LIKE ? "
                "     OR LOWER(COALESCE(telefon,'')) LIKE ?"
                ")"
                ")"
            )
            args.extend([like, like, like, like, like])

        self.crud.filter_sql = " AND ".join(clauses) if clauses else None
        self.crud.filter_args = tuple(args)
        self.crud.load_rows()

    def filter_by_date(self):
        """Filtreaza programarile dupa data selectata in calendar."""
        d = self.cal.selectedDate().toString("yyyy-MM-dd")
        self._filters_syncing = True
        try:
            self.dt_filter_from.setText(d)
            self.dt_filter_to.setText(d)
        finally:
            self._filters_syncing = False
        self.apply_filters()

    def reset_filter(self):
        """Reseteaza filtrele de programari si reincarca lista completa."""
        self._filters_syncing = True
        try:
            self.ed_quick_search.clear()
            self.cb_filter_medic.setCurrentIndex(0)
            self.cb_filter_status.setCurrentIndex(0)
            self.dt_filter_from.clear()
            self.dt_filter_to.clear()
        finally:
            self._filters_syncing = False
        self.crud.filter_sql = None
        self.crud.filter_args = tuple()
        self.crud.load_rows()

    def _apply_bulk_action_permissions(self):
        """Aplica bulk action permissions in `AppointmentsDialog`."""
        can_bulk = get_current_role() in ("admin", "receptie")
        self.cb_bulk_status.setEnabled(can_bulk)
        self.btn_bulk_status.setEnabled(can_bulk)
        self.ed_bulk_medic.setEnabled(can_bulk)
        self.btn_bulk_medic.setEnabled(can_bulk)
        self.spin_bulk_shift_days.setEnabled(can_bulk)
        self.btn_bulk_shift_date.setEnabled(can_bulk)
        if can_bulk:
            self.btn_bulk_status.setToolTip("Actualizeaza statusul pentru programarile bifate.")
            self.btn_bulk_medic.setToolTip("Seteaza medicul pentru programarile bifate.")
            self.btn_bulk_shift_date.setToolTip("Muta data programarilor bifate cu +/- zile.")
        else:
            self.btn_bulk_status.setToolTip("Doar admin/receptie pot modifica bulk statusul.")
            self.btn_bulk_medic.setToolTip("Doar admin/receptie pot modifica bulk medic.")
            self.btn_bulk_shift_date.setToolTip("Doar admin/receptie pot modifica bulk data.")

    def _install_shortcuts(self):
        """Gestioneaza shortcuts in `AppointmentsDialog`."""
        self._shortcuts: List[QShortcut] = []

        def add(seq: str, handler, hint_widget: Optional[QWidget] = None):
            """Adauga elementul curent in colectia gestionata de helper (helper intern pentru `_install_shortcuts`)."""
            sc = QShortcut(QKeySequence(seq), self)
            sc.setContext(Qt.ShortcutContext.WindowShortcut)
            sc.activated.connect(handler)
            self._shortcuts.append(sc)
            if hint_widget is not None:
                append_shortcut_hint(hint_widget, seq)

        add("F5", lambda: self.crud.load_rows(), self.crud.btn_refresh)
        add("Ctrl+F", self._focus_quick_search, self.ed_quick_search)
        add("Ctrl+Shift+F", self.apply_filters, self.btn_apply_filters)
        add("Ctrl+R", self.reset_filter, self.btn_clear_filters)
        add("Ctrl+D", self.filter_by_date, self.btn_filter)
        add("Ctrl+M", self.send_sms, self.btn_sms)
        add("Ctrl+B", self.bulk_update_status, self.btn_bulk_status)
        add("Ctrl+Shift+B", self.bulk_set_medic, self.btn_bulk_medic)
        add("Ctrl+Alt+B", self.bulk_shift_date, self.btn_bulk_shift_date)
        add("Ctrl+Shift+M", self.open_sms_audit_dialog, self.btn_sms_audit)
        add("Ctrl+Shift+S", self._sms_pick_check_all, self.btn_sms_pick_all)
        add("Ctrl+Shift+X", self._sms_pick_uncheck_all, self.btn_sms_pick_none)

    def _focus_quick_search(self):
        """Gestioneaza quick search in `AppointmentsDialog`."""
        try:
            self.ed_quick_search.setFocus()
            self.ed_quick_search.selectAll()
        except Exception:
            pass

    def bulk_update_status(self):
        """Actualizeaza in bulk statusul pentru programarile selectate."""
        ids = self._bulk_selected_ids()
        if not ids:
            return

        new_status = (self.cb_bulk_status.currentData() or "").strip() or (self.cb_bulk_status.currentText() or "").strip()
        if not new_status:
            QMessageBox.warning(self, "Bulk status", "Selecteaza statusul nou.")
            return

        if QMessageBox.question(
            self,
            "Confirmare bulk update",
            f"Actualizez statusul la '{new_status}' pentru {len(ids)} programari?",
            QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
            QMessageBox.StandardButton.No,
        ) != QMessageBox.StandardButton.Yes:
            return

        changed, changed_ids = self._set_status_for_appointments(ids, new_status, source_action="appointments_bulk_status")

        try:
            log_action(
                "appointments_bulk_status",
                json.dumps(
                    {"status": new_status, "count": int(changed), "ids": [int(x) for x in ids], "changed_ids": changed_ids},
                    ensure_ascii=False,
                ),
            )
        except Exception:
            pass

        self.crud.load_rows()
        QMessageBox.information(
            self,
            "Bulk status",
            f"Status actualizat la '{new_status}' pentru {changed} programari.",
        )

    def bulk_set_medic(self):
        """Seteaza in bulk medicul pentru programarile selectate."""
        ids = self._bulk_selected_ids()
        if not ids:
            return
        medic_new = (self.ed_bulk_medic.text() or "").strip()
        if not medic_new:
            QMessageBox.warning(self, "Bulk medic", "Introdu medicul nou.")
            return
        if QMessageBox.question(
            self,
            "Confirmare bulk medic",
            f"Setez medicul '{medic_new}' pentru {len(ids)} programari?",
            QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
            QMessageBox.StandardButton.No,
        ) != QMessageBox.StandardButton.Yes:
            return

        conn = get_conn()
        cur = conn.cursor()
        _ensure_entity_audit_table(conn)
        before_map = self._fetch_appointment_rows_map(cur, ids)
        sets = ["medic=?"]
        vals: List[Any] = [medic_new]
        if table_has_column("appointments", "updated_at"):
            sets.append("updated_at=?")
            vals.append(now_ts())
        if table_has_column("appointments", "device_id"):
            sets.append("device_id=?")
            vals.append(get_device_id())
        if table_has_column("appointments", "deleted"):
            sets.append("deleted=0")
        ph = ", ".join(["?"] * len(ids))
        vals.extend([int(x) for x in ids])
        cur.execute(f"UPDATE appointments SET {', '.join(sets)} WHERE id IN ({ph})", tuple(vals))
        changed = int(cur.rowcount) if isinstance(cur.rowcount, int) and cur.rowcount >= 0 else len(ids)
        self._audit_appointment_changes(cur, ids, before_map, source_action="appointments_bulk_medic")
        self._sync_appointment_dependencies_cur(cur, ids, before_map=before_map, source_action="appointments_bulk_medic")
        conn.commit()
        conn.close()

        try:
            log_action(
                "appointments_bulk_medic",
                json.dumps({"medic": medic_new, "count": int(changed), "ids": [int(x) for x in ids]}, ensure_ascii=False),
            )
        except Exception:
            pass
        self.crud.load_rows()
        QMessageBox.information(self, "Bulk medic", f"Medic actualizat pentru {changed} programari.")

    def bulk_shift_date(self):
        """Decaleaza in bulk data programarilor selectate."""
        ids = self._bulk_selected_ids()
        if not ids:
            return
        days = int(self.spin_bulk_shift_days.value())
        if days == 0:
            QMessageBox.information(self, "Bulk data", "Seteaza un numar de zile diferit de 0.")
            return
        if QMessageBox.question(
            self,
            "Confirmare bulk data",
            f"Mut datele programarilor selectate cu {days} zile?",
            QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
            QMessageBox.StandardButton.No,
        ) != QMessageBox.StandardButton.Yes:
            return

        conn = get_conn()
        cur = conn.cursor()
        _ensure_entity_audit_table(conn)
        before_map = self._fetch_appointment_rows_map(cur, ids)
        changed = 0
        skipped = 0
        for appt_id in ids:
            row = before_map.get(int(appt_id))
            old_date = (row.get("date") or "").strip() if row else ""
            d = _safe_parse_ymd(old_date)
            if d is None:
                skipped += 1
                continue
            new_date = (d + timedelta(days=days)).strftime("%Y-%m-%d")
            sets = ["date=?"]
            vals: List[Any] = [new_date]
            if table_has_column("appointments", "updated_at"):
                sets.append("updated_at=?")
                vals.append(now_ts())
            if table_has_column("appointments", "device_id"):
                sets.append("device_id=?")
                vals.append(get_device_id())
            if table_has_column("appointments", "deleted"):
                sets.append("deleted=0")
            vals.append(int(appt_id))
            cur.execute(f"UPDATE appointments SET {', '.join(sets)} WHERE id=?", tuple(vals))
            if isinstance(cur.rowcount, int) and cur.rowcount > 0:
                changed += int(cur.rowcount)
        self._audit_appointment_changes(cur, ids, before_map, source_action="appointments_bulk_shift_date")
        self._sync_appointment_dependencies_cur(cur, ids, before_map=before_map, source_action="appointments_bulk_shift_date")
        conn.commit()
        conn.close()

        try:
            log_action(
                "appointments_bulk_shift_date",
                json.dumps({"days": days, "changed": int(changed), "skipped": int(skipped), "ids": [int(x) for x in ids]}, ensure_ascii=False),
            )
        except Exception:
            pass
        self.crud.load_rows()
        QMessageBox.information(
            self,
            "Bulk data",
            f"Date actualizate pentru {changed} programari.\nSarite (data invalida): {skipped}.",
        )

    def _bulk_selected_ids(self) -> List[int]:
        """Gestioneaza selected ID-uri in `AppointmentsDialog`."""
        if get_current_role() not in ("admin", "receptie"):
            QMessageBox.warning(self, "Actiune bulk", "Doar admin/receptie pot rula actiuni bulk.")
            return []
        ids = self._checked_appointment_ids()
        if not ids:
            ids = self._selected_appointment_ids()
        if not ids:
            QMessageBox.information(
                self,
                "Actiune bulk",
                "Bifeaza programari in zona SMS sau selecteaza cel putin un rand din lista.",
            )
            return []
        return [int(x) for x in ids]

    def _fetch_appointment_rows_map(self, cur: sqlite3.Cursor, ids: List[int]) -> Dict[int, Dict[str, Any]]:
        """Gestioneaza appointment rows map in `AppointmentsDialog`."""
        uniq_ids = sorted(set([int(x) for x in (ids or []) if int(x) > 0]))
        if not uniq_ids:
            return {}
        ph = ", ".join(["?"] * len(uniq_ids))
        cur.execute(f"SELECT * FROM appointments WHERE id IN ({ph})", tuple(uniq_ids))
        out: Dict[int, Dict[str, Any]] = {}
        for rr in cur.fetchall():
            try:
                out[int(rr["id"])] = dict(rr)
            except Exception:
                continue
        return out

    def _audit_appointment_changes(
        self,
        cur: sqlite3.Cursor,
        ids: List[int],
        before_map: Dict[int, Dict[str, Any]],
        source_action: str,
    ) -> None:
        """Gestioneaza appointment changes in `AppointmentsDialog`."""
        after_map = self._fetch_appointment_rows_map(cur, ids)
        for appt_id in ids:
            before_row = before_map.get(int(appt_id))
            after_row = after_map.get(int(appt_id))
            if before_row == after_row:
                continue
            _insert_entity_audit_cur(
                cur,
                "appointments",
                int(appt_id),
                "update",
                before_row,
                after_row,
                source_action=source_action,
            )

    def _appointment_tag(self, appointment_id: int) -> str:
        """Gestioneaza tag in `AppointmentsDialog`."""
        return f"[APPT#{int(appointment_id)}]"

    def _build_appointment_alert_message(self, row: Optional[Dict[str, Any]], appointment_id: int) -> str:
        """Construieste appointment alert message in `AppointmentsDialog`."""
        data = dict(row or {})
        date_txt = (data.get("date") or "").strip() or "-"
        time_txt = (data.get("time") or "").strip() or "--:--"
        medic_txt = (data.get("medic") or "").strip() or "-"
        status_txt = (data.get("status") or "").strip() or "-"
        return (
            f"{self._appointment_tag(appointment_id)} "
            f"Programare {date_txt} {time_txt} | Medic: {medic_txt} | Status: {status_txt}"
        )

    def _insert_medical_history_comm_cur(
        self,
        cur: sqlite3.Cursor,
        patient_id: Optional[int],
        appointment_id: Optional[int],
        channel: str,
        status: str,
        recipient: str,
        message: str,
        source_action: str,
    ) -> None:
        """Insereaza medical history comm cursor in `AppointmentsDialog`."""
        try:
            pid = int(patient_id or 0)
        except Exception:
            pid = 0
        if pid <= 0:
            return
        channel_txt = (channel or "Comunicare").strip().upper() or "COMUNICARE"
        status_txt = (status or "").strip() or "initiat"
        try:
            aid = int(appointment_id or 0)
        except Exception:
            aid = 0
        today_ymd = datetime.now().strftime("%Y-%m-%d")
        notes_parts: List[str] = []
        if aid > 0:
            notes_parts.append(self._appointment_tag(aid))
        if (recipient or "").strip():
            notes_parts.append(f"Destinatar: {recipient.strip()}")
        if (message or "").strip():
            notes_parts.append(f"Mesaj: {(message or '').strip()}")
        notes_txt = " | ".join([x for x in notes_parts if x.strip()]).strip()

        cols = ["pacient_id", "category", "item", "start_date", "end_date", "notes"]
        vals: List[Any] = [
            pid,
            "Comunicare",
            f"{channel_txt} {status_txt}",
            today_ymd,
            None,
            notes_txt or None,
        ]
        hist_cols = _db_table_columns_cur(cur, "medical_history")
        if "sync_id" in hist_cols:
            cols.append("sync_id")
            vals.append(uuid.uuid4().hex)
        if "updated_at" in hist_cols:
            cols.append("updated_at")
            vals.append(now_ts())
        if "deleted" in hist_cols:
            cols.append("deleted")
            vals.append(0)
        if "device_id" in hist_cols:
            cols.append("device_id")
            vals.append(get_device_id())

        cur.execute(
            f"INSERT INTO medical_history ({', '.join(cols)}) VALUES ({', '.join(['?'] * len(cols))})",
            tuple(vals),
        )
        hist_id = int(cur.lastrowid or 0)
        if hist_id > 0:
            _insert_entity_audit_cur(
                cur,
                "medical_history",
                hist_id,
                "insert",
                None,
                _fetch_row_dict_cur(cur, "medical_history", hist_id),
                source_action=source_action,
            )

    def _record_patient_communication(
        self,
        patient_id: Optional[int],
        appointment_id: Optional[int],
        channel: str,
        status: str,
        recipient: str,
        message: str,
        source_action: str,
    ) -> None:
        """Gestioneaza patient communication in `AppointmentsDialog`."""
        conn = get_conn()
        cur = conn.cursor()
        try:
            _ensure_entity_audit_table(conn)
            self._insert_medical_history_comm_cur(
                cur,
                patient_id=patient_id,
                appointment_id=appointment_id,
                channel=channel,
                status=status,
                recipient=recipient,
                message=message,
                source_action=source_action,
            )
            conn.commit()
        except Exception:
            conn.rollback()
        finally:
            conn.close()

    def _sync_single_appointment_alert_cur(
        self,
        cur: sqlite3.Cursor,
        appointment_id: int,
        before_row: Optional[Dict[str, Any]],
        after_row: Optional[Dict[str, Any]],
        source_action: str,
    ) -> None:
        """Sincronizeaza single appointment alert cursor in `AppointmentsDialog`."""
        appt_tag = self._appointment_tag(appointment_id)
        pivot = dict(after_row or before_row or {})
        try:
            pid = int(pivot.get("pacient_id") or 0)
        except Exception:
            pid = 0
        if pid <= 0:
            return

        cur.execute(
            """
            SELECT * FROM clinical_alerts
            WHERE pacient_id=? AND alert_type=? AND message LIKE ?
            ORDER BY id DESC
            LIMIT 1
            """,
            (pid, "Control programat", f"%{appt_tag}%"),
        )
        existing = cur.fetchone()
        existing_id = int(existing["id"]) if existing is not None else 0

        after_deleted = 0
        after_status_n = ""
        if isinstance(after_row, dict):
            after_deleted = _to_int_flag(after_row.get("deleted"))
            after_status_n = _norm(after_row.get("status") or "")
        should_be_active = bool(after_row) and after_deleted == 0 and after_status_n not in {"anulat", "realizat"}

        if should_be_active:
            due_date = (after_row.get("date") or "").strip() if isinstance(after_row, dict) else ""
            msg = self._build_appointment_alert_message(after_row, appointment_id)
            if existing is not None and existing_id > 0:
                before_alert = dict(existing)
                sets = ["message=?", "due_date=?", "active=1"]
                vals: List[Any] = [msg, due_date or None]
                if table_has_column("clinical_alerts", "updated_at"):
                    sets.append("updated_at=?")
                    vals.append(now_ts())
                if table_has_column("clinical_alerts", "device_id"):
                    sets.append("device_id=?")
                    vals.append(get_device_id())
                if table_has_column("clinical_alerts", "deleted"):
                    sets.append("deleted=0")
                vals.append(existing_id)
                cur.execute(f"UPDATE clinical_alerts SET {', '.join(sets)} WHERE id=?", tuple(vals))
                after_alert = _fetch_row_dict_cur(cur, "clinical_alerts", existing_id)
                if before_alert != after_alert:
                    _insert_entity_audit_cur(
                        cur,
                        "clinical_alerts",
                        existing_id,
                        "update",
                        before_alert,
                        after_alert,
                        source_action=source_action,
                    )
            else:
                cols = ["pacient_id", "alert_type", "message", "active", "due_date", "created_at"]
                vals = [pid, "Control programat", msg, 1, due_date or None, now_ts()]
                if table_has_column("clinical_alerts", "sync_id"):
                    cols.append("sync_id")
                    vals.append(uuid.uuid4().hex)
                if table_has_column("clinical_alerts", "updated_at"):
                    cols.append("updated_at")
                    vals.append(now_ts())
                if table_has_column("clinical_alerts", "deleted"):
                    cols.append("deleted")
                    vals.append(0)
                if table_has_column("clinical_alerts", "device_id"):
                    cols.append("device_id")
                    vals.append(get_device_id())
                cur.execute(
                    f"INSERT INTO clinical_alerts ({', '.join(cols)}) VALUES ({', '.join(['?'] * len(cols))})",
                    tuple(vals),
                )
                alert_id = int(cur.lastrowid or 0)
                if alert_id > 0:
                    _insert_entity_audit_cur(
                        cur,
                        "clinical_alerts",
                        alert_id,
                        "insert",
                        None,
                        _fetch_row_dict_cur(cur, "clinical_alerts", alert_id),
                        source_action=source_action,
                    )
            return

        if existing is not None and existing_id > 0:
            before_alert = dict(existing)
            sets = ["active=0"]
            vals: List[Any] = []
            if table_has_column("clinical_alerts", "updated_at"):
                sets.append("updated_at=?")
                vals.append(now_ts())
            if table_has_column("clinical_alerts", "device_id"):
                sets.append("device_id=?")
                vals.append(get_device_id())
            if table_has_column("clinical_alerts", "deleted"):
                sets.append("deleted=0")
            vals.append(existing_id)
            cur.execute(f"UPDATE clinical_alerts SET {', '.join(sets)} WHERE id=?", tuple(vals))
            after_alert = _fetch_row_dict_cur(cur, "clinical_alerts", existing_id)
            if before_alert != after_alert:
                _insert_entity_audit_cur(
                    cur,
                    "clinical_alerts",
                    existing_id,
                    "update",
                    before_alert,
                    after_alert,
                    source_action=source_action,
                )

    def _sync_appointment_reminder_runtime_cur(
        self,
        cur: sqlite3.Cursor,
        appointment_id: int,
        before_row: Optional[Dict[str, Any]],
        after_row: Optional[Dict[str, Any]],
    ) -> None:
        """Sincronizeaza appointment reminder runtime cursor in `AppointmentsDialog`."""
        aid = int(appointment_id)
        _ensure_reminder_runtime_tables(cur.connection)
        _ensure_appointment_sms_template_state_table(cur.connection)
        if after_row is None or _to_int_flag(after_row.get("deleted") if isinstance(after_row, dict) else 0) == 1:
            cur.execute("DELETE FROM appointment_reminder_state WHERE appointment_id=?", (aid,))
            cur.execute("DELETE FROM appointment_sms_template_state WHERE appointment_id=?", (aid,))
            return

        relevant = ("date", "time", "status", "reminder_sms", "reminder_email", "pacient_id", "deleted")
        changed = before_row is None
        if not changed and isinstance(before_row, dict):
            for key in relevant:
                left = (before_row.get(key) if before_row is not None else None) or ""
                right = (after_row.get(key) if after_row is not None else None) or ""
                if str(left).strip() != str(right).strip():
                    changed = True
                    break
        if not changed:
            return

        cur.execute("DELETE FROM appointment_reminder_state WHERE appointment_id=?", (aid,))
        if table_has_column("appointments", "reminder_sent_at"):
            cur.execute("UPDATE appointments SET reminder_sent_at=NULL WHERE id=?", (aid,))

    def _sync_appointment_dependencies_cur(
        self,
        cur: sqlite3.Cursor,
        ids: List[int],
        before_map: Optional[Dict[int, Dict[str, Any]]] = None,
        source_action: str = "",
    ) -> Dict[int, Dict[str, Any]]:
        """Sincronizeaza alertele si starea de remindere dupa modificari de programare."""
        uniq_ids = sorted(set([int(x) for x in (ids or []) if int(x) > 0]))
        if not uniq_ids:
            return {}
        before_map = before_map or {}
        after_map = self._fetch_appointment_rows_map(cur, uniq_ids)
        for aid in uniq_ids:
            self._sync_single_appointment_alert_cur(
                cur,
                aid,
                before_map.get(int(aid)),
                after_map.get(int(aid)),
                source_action=source_action or "appointments_sync_dependencies",
            )
            self._sync_appointment_reminder_runtime_cur(
                cur,
                aid,
                before_map.get(int(aid)),
                after_map.get(int(aid)),
            )
        return after_map

    def _upsert_checkin_flow_cur(
        self,
        cur: sqlite3.Cursor,
        appt_row: Dict[str, Any],
        source_action: str,
    ) -> None:
        """Insereaza sau actualizeaza checkin flow cursor in `AppointmentsDialog`."""
        row = dict(appt_row or {})
        try:
            pid = int(row.get("pacient_id") or 0)
        except Exception:
            pid = 0
        try:
            appt_id = int(row.get("id") or 0)
        except Exception:
            appt_id = 0
        if pid <= 0:
            return
        flow_cols = _db_table_columns_cur(cur, "patient_flow")
        if "checkin_time" not in flow_cols:
            return

        stamp_local = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        tag = self._appointment_tag(appt_id) if appt_id > 0 else ""
        checkin_note = (f"{tag} Check-in din Programari").strip()

        where = ["pacient_id=?"]
        args: List[Any] = [pid]
        if "deleted" in flow_cols:
            where.append("COALESCE(deleted,0)=0")
        cur.execute(
            f"SELECT * FROM patient_flow WHERE {' AND '.join(where)} ORDER BY id DESC LIMIT 1",
            tuple(args),
        )
        latest = cur.fetchone()

        if latest is not None and not str(latest["checkin_time"] or "").strip():
            flow_id = int(latest["id"])
            before_flow = dict(latest)
            sets = ["status=?", "checkin_time=?"]
            vals: List[Any] = ["Check-in", stamp_local]
            if "notes" in flow_cols:
                prev = str(latest["notes"] or "").strip()
                if checkin_note:
                    merged = checkin_note if not prev else (prev if tag and tag in prev else f"{prev} | {checkin_note}")
                else:
                    merged = prev
                sets.append("notes=?")
                vals.append(merged or None)
            if "updated_at" in flow_cols:
                sets.append("updated_at=?")
                vals.append(now_ts())
            if "device_id" in flow_cols:
                sets.append("device_id=?")
                vals.append(get_device_id())
            if "deleted" in flow_cols:
                sets.append("deleted=0")
            vals.append(flow_id)
            cur.execute(f"UPDATE patient_flow SET {', '.join(sets)} WHERE id=?", tuple(vals))
            after_flow = _fetch_row_dict_cur(cur, "patient_flow", flow_id)
            if before_flow != after_flow:
                _insert_entity_audit_cur(
                    cur,
                    "patient_flow",
                    flow_id,
                    "update",
                    before_flow,
                    after_flow,
                    source_action=source_action,
                )
            return

        cols = ["pacient_id", "status", "checkin_time"]
        vals: List[Any] = [pid, "Check-in", stamp_local]
        if "notes" in flow_cols:
            cols.append("notes")
            vals.append(checkin_note or None)
        if "created_at" in flow_cols:
            cols.append("created_at")
            vals.append(stamp_local)
        if "sync_id" in flow_cols:
            cols.append("sync_id")
            vals.append(uuid.uuid4().hex)
        if "updated_at" in flow_cols:
            cols.append("updated_at")
            vals.append(now_ts())
        if "deleted" in flow_cols:
            cols.append("deleted")
            vals.append(0)
        if "device_id" in flow_cols:
            cols.append("device_id")
            vals.append(get_device_id())
        cur.execute(
            f"INSERT INTO patient_flow ({', '.join(cols)}) VALUES ({', '.join(['?'] * len(cols))})",
            tuple(vals),
        )
        flow_id = int(cur.lastrowid or 0)
        if flow_id > 0:
            _insert_entity_audit_cur(
                cur,
                "patient_flow",
                flow_id,
                "insert",
                None,
                _fetch_row_dict_cur(cur, "patient_flow", flow_id),
                source_action=source_action,
            )

    def _set_status_for_appointments(self, ids: List[int], new_status: str, source_action: str) -> Tuple[int, List[int]]:
        """Aplica status nou, audit si efecte secundare pentru un lot de programari."""
        uniq_ids = sorted(set([int(x) for x in (ids or []) if int(x) > 0]))
        if not uniq_ids:
            return 0, []
        conn = get_conn()
        cur = conn.cursor()
        _ensure_entity_audit_table(conn)
        before_map = self._fetch_appointment_rows_map(cur, uniq_ids)
        if not before_map:
            conn.close()
            return 0, []

        sets = ["status=?"]
        vals: List[Any] = [new_status]
        if table_has_column("appointments", "updated_at"):
            sets.append("updated_at=?")
            vals.append(now_ts())
        if table_has_column("appointments", "device_id"):
            sets.append("device_id=?")
            vals.append(get_device_id())
        if table_has_column("appointments", "deleted"):
            sets.append("deleted=0")
        ph = ", ".join(["?"] * len(uniq_ids))
        vals.extend(uniq_ids)
        cur.execute(f"UPDATE appointments SET {', '.join(sets)} WHERE id IN ({ph})", tuple(vals))
        touched = int(cur.rowcount) if isinstance(cur.rowcount, int) and cur.rowcount >= 0 else len(uniq_ids)

        self._audit_appointment_changes(cur, uniq_ids, before_map, source_action=source_action)
        after_map = self._sync_appointment_dependencies_cur(
            cur,
            uniq_ids,
            before_map=before_map,
            source_action=source_action,
        )

        changed_ids: List[int] = []
        for aid in uniq_ids:
            if before_map.get(int(aid)) != after_map.get(int(aid)):
                changed_ids.append(int(aid))

        if _norm(new_status or "") == "check-in":
            for aid in uniq_ids:
                row = after_map.get(int(aid))
                if row is None:
                    continue
                self._upsert_checkin_flow_cur(cur, row, source_action=source_action)

        conn.commit()
        conn.close()
        return (len(changed_ids) if changed_ids else int(touched)), changed_ids

    def _on_appointment_crud_mutation(self, action: str, event: Dict[str, Any]) -> None:
        """Proceseaza evenimente CRUD din lista Programari pentru sincronizari auxiliare."""
        table_name = (event.get("table_name") or "").strip()
        if table_name != "appointments":
            return
        try:
            row_id = int(event.get("row_id") or 0)
        except Exception:
            row_id = 0
        if row_id <= 0:
            return
        before_row = event.get("before_row") if isinstance(event.get("before_row"), dict) else None
        after_row = event.get("after_row") if isinstance(event.get("after_row"), dict) else None
        act = (action or "").strip().lower()
        source_action = f"appointments_crud_{act or 'change'}"

        conn = get_conn()
        cur = conn.cursor()
        try:
            _ensure_entity_audit_table(conn)
            if act == "add":
                audit_action = "insert"
            elif act == "delete":
                audit_action = "soft_delete" if isinstance(after_row, dict) else "delete"
            else:
                audit_action = "update"
            _insert_entity_audit_cur(
                cur,
                "appointments",
                row_id,
                audit_action,
                before_row,
                after_row,
                source_action=source_action,
            )

            before_map = {int(row_id): dict(before_row)} if isinstance(before_row, dict) else {}
            after_map = self._sync_appointment_dependencies_cur(
                cur,
                [int(row_id)],
                before_map=before_map,
                source_action=source_action,
            )
            current_after = after_map.get(int(row_id))
            before_status = _norm((before_row or {}).get("status") or "") if isinstance(before_row, dict) else ""
            after_status = _norm((current_after or {}).get("status") or "") if isinstance(current_after, dict) else ""
            if after_status == "check-in" and (act == "add" or before_status != after_status):
                self._upsert_checkin_flow_cur(cur, current_after, source_action=source_action)
            conn.commit()
        except Exception:
            conn.rollback()
        finally:
            conn.close()

    def _sms_template_key(self) -> str:
        """Gestioneaza template key in `AppointmentsDialog`."""
        return _normalize_forced_template_key(self.cb_sms_template.currentData()) or "confirm"

    def _on_sms_check_item_changed(self, item: Optional[QTableWidgetItem]):
        # Deprecated path: selection for SMS is handled by the external checkbox panel.
        """Gestioneaza evenimentul SMS check item changed in `AppointmentsDialog`."""
        return

    def _refresh_sms_picker_info(self):
        """Gestioneaza SMS picker info in `AppointmentsDialog`."""
        total = len(self._sms_picker_order)
        selected = 0
        for appt_id in self._sms_picker_order:
            cb = self._sms_picker_checks.get(appt_id)
            if cb is not None and cb.isChecked():
                selected += 1
        self.lbl_sms_pick_info.setText(f"Programari bifate: {selected}/{total}")

    def _on_sms_picker_state_changed(self, appointment_id: int, checked: bool):
        """Gestioneaza evenimentul SMS picker state changed in `AppointmentsDialog`."""
        if self._sms_checks_syncing:
            return
        appt_id = int(appointment_id)
        if checked:
            self._sms_checked_ids.add(appt_id)
        else:
            self._sms_checked_ids.discard(appt_id)
        self._refresh_sms_picker_info()

    def _sms_pick_check_all(self):
        """Gestioneaza pick check all in `AppointmentsDialog`."""
        self._sms_checks_syncing = True
        try:
            for appt_id in self._sms_picker_order:
                cb = self._sms_picker_checks.get(appt_id)
                if cb is None or not cb.isEnabled():
                    continue
                cb.setChecked(True)
                self._sms_checked_ids.add(appt_id)
        finally:
            self._sms_checks_syncing = False
        self._refresh_sms_picker_info()

    def _sms_pick_uncheck_all(self):
        """Gestioneaza pick uncheck all in `AppointmentsDialog`."""
        self._sms_checks_syncing = True
        try:
            for appt_id in self._sms_picker_order:
                cb = self._sms_picker_checks.get(appt_id)
                if cb is None:
                    continue
                cb.setChecked(False)
                self._sms_checked_ids.discard(appt_id)
        finally:
            self._sms_checks_syncing = False
        self._refresh_sms_picker_info()

    def _checked_appointment_ids(self) -> List[int]:
        """Gestioneaza appointment ID-uri in `AppointmentsDialog`."""
        out: List[int] = []
        for appt_id in self._sms_picker_order:
            cb = self._sms_picker_checks.get(appt_id)
            if cb is not None and cb.isChecked() and cb.isEnabled():
                out.append(int(appt_id))
        return out

    def _sync_sms_checkboxes(self):
        """Sincronizeaza SMS checkboxes in `AppointmentsDialog`."""
        tbl = self.crud.tbl
        if tbl is None:
            return
        rows_data: List[Tuple[int, str, Optional[int], str, str, str]] = []
        valid_ids = set()
        pid_ids: set = set()
        for row in range(tbl.rowCount()):
            it_id = tbl.item(row, 0)
            if it_id is None:
                continue
            try:
                appt_id = int(it_id.text())
            except Exception:
                continue
            valid_ids.add(appt_id)
            pid = (tbl.item(row, 1).text() if tbl.item(row, 1) else "").strip()
            pid_int: Optional[int] = None
            try:
                pid_int = int(pid)
                pid_ids.add(pid_int)
            except Exception:
                pid_int = None
            d = (tbl.item(row, 2).text() if tbl.item(row, 2) else "").strip()
            hhmm = (tbl.item(row, 3).text() if tbl.item(row, 3) else "").strip()
            st = (tbl.item(row, 6).text() if tbl.item(row, 6) else "").strip()
            rows_data.append((appt_id, pid, pid_int, d, hhmm, st))
        self._sms_checked_ids = {x for x in self._sms_checked_ids if x in valid_ids}

        name_by_pid: Dict[int, str] = {}
        if pid_ids:
            conn = get_conn()
            cur = conn.cursor()
            ph = ", ".join(["?"] * len(pid_ids))
            cur.execute(
                f"SELECT id, COALESCE(nume_prenume,'') FROM pacienti_master WHERE id IN ({ph})",
                tuple(pid_ids),
            )
            for rr in cur.fetchall():
                try:
                    name_by_pid[int(rr[0])] = (rr[1] or "").strip()
                except Exception:
                    continue
            conn.close()

        self._sms_checks_syncing = True
        try:
            while self.sms_pick_list.count():
                it = self.sms_pick_list.takeAt(0)
                w = it.widget()
                if w is not None:
                    w.deleteLater()
            self._sms_picker_checks = {}
            self._sms_picker_order = []

            for appt_id, pid, pid_int, d, hhmm, st in rows_data:
                pname = name_by_pid.get(int(pid_int)) if pid_int is not None else ""
                txt = f"#{appt_id} | {pname or 'Pacient'} | PID {pid or '-'} | {d or '-'} {hhmm or '--:--'} | {st or '-'}"
                cb = QCheckBox(txt)
                cb.setChecked(appt_id in self._sms_checked_ids)
                cb.toggled.connect(lambda checked, aid=appt_id: self._on_sms_picker_state_changed(aid, bool(checked)))
                self.sms_pick_list.addWidget(cb)
                self._sms_picker_checks[appt_id] = cb
                self._sms_picker_order.append(appt_id)
            self.sms_pick_list.addStretch(1)
        finally:
            self._sms_checks_syncing = False
        self._refresh_sms_picker_info()

    def _selected_appointment_ids(self) -> List[int]:
        """Gestioneaza appointment ID-uri in `AppointmentsDialog`."""
        out: List[int] = []
        try:
            sm = self.crud.tbl.selectionModel()
            if sm is not None:
                for idx in sm.selectedRows(0):
                    it = self.crud.tbl.item(idx.row(), 0)
                    if not it:
                        continue
                    try:
                        out.append(int(it.text()))
                    except Exception:
                        continue
        except Exception:
            pass
        # Fallback: current row
        if not out:
            r = self._get_row()
            if r is not None:
                try:
                    out = [int(r["id"])]
                except Exception:
                    out = []
        # Preserve order + dedupe
        seen = set()
        ids: List[int] = []
        for v in out:
            if v in seen:
                continue
            seen.add(v)
            ids.append(v)
        return ids

    def _refresh_confirm_sms_cache(self):
        """Gestioneaza confirm SMS cache in `AppointmentsDialog`."""
        try:
            conn = get_conn()
            self._confirm_sms_sent_ids = _get_appointment_confirm_sent_ids(conn)
            conn.close()
        except Exception:
            self._confirm_sms_sent_ids = set()

    def _sync_confirm_sms_status_column(self):
        """Sincronizeaza confirm SMS status column in `AppointmentsDialog`."""
        tbl = self.crud.tbl
        if tbl is None:
            return
        header_name = "SMS confirmare"
        col_idx = -1
        for col in range(tbl.columnCount()):
            h = tbl.horizontalHeaderItem(col)
            txt = (h.text() if h is not None else "").strip().lower()
            if txt == header_name:
                col_idx = col
                break
        if col_idx < 0:
            col_idx = tbl.columnCount()
            tbl.insertColumn(col_idx)
            tbl.setHorizontalHeaderItem(col_idx, QTableWidgetItem(header_name))
            try:
                tbl.horizontalHeader().setSectionResizeMode(col_idx, QHeaderView.ResizeMode.ResizeToContents)
            except Exception:
                pass

        for row in range(tbl.rowCount()):
            it_id = tbl.item(row, 0)
            if it_id is None:
                continue
            try:
                appt_id = int(it_id.text())
            except Exception:
                continue
            sent = appt_id in self._confirm_sms_sent_ids
            txt = "Da" if sent else "Nu"
            it = tbl.item(row, col_idx)
            if it is None:
                it = QTableWidgetItem(txt)
                tbl.setItem(row, col_idx, it)
            else:
                it.setText(txt)
            it.setTextAlignment(int(Qt.AlignmentFlag.AlignCenter))
            it.setForeground(QBrush(QColor("#0f766e") if sent else QColor("#6b7280")))
            it.setToolTip("SMS confirmare trimis." if sent else "SMS confirmare netrimis.")

    def _apply_sms_selection_guard(self):
        """Blocheaza selectia pentru pacientii care nu mai trebuie sa primeasca template-ul."""
        lock_confirm = self._sms_template_key() == "confirm"
        self._sms_checks_syncing = True
        try:
            for appt_id in self._sms_picker_order:
                cb = self._sms_picker_checks.get(appt_id)
                if cb is None:
                    continue
                is_blocked = lock_confirm and (appt_id in self._confirm_sms_sent_ids)
                if is_blocked:
                    self._sms_checked_ids.discard(appt_id)
                    cb.setChecked(False)
                    cb.setEnabled(False)
                    cb.setToolTip("Confirmarea SMS a fost deja trimisa pentru aceasta programare.")
                else:
                    cb.setEnabled(True)
                    cb.setToolTip("Bifeaza pentru trimitere SMS.")
                    cb.setChecked(appt_id in self._sms_checked_ids)
        finally:
            self._sms_checks_syncing = False
        self._refresh_sms_picker_info()

    def _log_manual_confirm_blocked(self, appointment_ids: List[int]) -> None:
        """Gestioneaza manual confirm blocked in `AppointmentsDialog`."""
        ids = [int(x) for x in (appointment_ids or []) if int(x) > 0]
        if not ids:
            return
        try:
            rows = self._fetch_sms_target_rows(ids)
            by_id = {}
            for r in rows:
                try:
                    by_id[int(r["id"])] = r
                except Exception:
                    continue
            conn = get_conn()
            _ensure_reminder_runtime_tables(conn)
            cur = conn.cursor()
            attempted = now_ts()
            for aid in ids:
                rr = by_id.get(int(aid))
                phone = ""
                msg = "Blocat: confirmarea SMS a fost deja trimisa pentru aceasta programare."
                if rr is not None:
                    phone = normalize_ro_mobile_phone(rr["reminder_sms"]) or (rr["reminder_sms"] or "").strip()
                _insert_reminder_log(
                    cur,
                    int(aid),
                    trigger_at=attempted,
                    attempted_at=attempted,
                    status="manual_confirm_blocked",
                    phone=phone,
                    message=msg,
                    response="",
                    error="already_confirmed",
                    attempts=0,
                    dispatch_rule="manual_confirm",
                    source_action="selection_guard_blocked_confirm",
                )
            conn.commit()
            conn.close()
        except Exception:
            pass

    def refresh_sms_monitor_dashboard(self):
        """Reincarca indicatorii SMS din dashboard-ul paginii Programari."""
        try:
            snap = get_manual_sms_dashboard_snapshot()
        except Exception:
            snap = {"sent": 0, "failed": 0, "no_phone": 0, "opt_out": 0, "blocked_confirm": 0}
        self.lbl_sms_monitor_sent.setText(f"Trimise: {int(snap.get('sent') or 0)}")
        self.lbl_sms_monitor_failed.setText(f"Esuate: {int(snap.get('failed') or 0)}")
        self.lbl_sms_monitor_no_phone.setText(f"Fara telefon: {int(snap.get('no_phone') or 0)}")
        self.lbl_sms_monitor_opt_out.setText(f"SMS dezactivat: {int(snap.get('opt_out') or 0)}")
        self.lbl_sms_monitor_blocked.setText(f"Blocari confirmare: {int(snap.get('blocked_confirm') or 0)}")

    def open_sms_audit_dialog(self):
        """Deschide jurnalul audit cu detalii despre trimiterile SMS."""
        rows = get_manual_sms_audit_rows(limit=300)
        dlg = QDialog(self)
        dlg.setWindowTitle("Audit SMS pe utilizator")
        dlg.resize(1120, 560)
        root = QVBoxLayout(dlg)

        note = QLabel("Jurnal manual SMS: cine a trimis, cand, cui.")
        note.setStyleSheet("color: #4b5563;")
        root.addWidget(note)

        tbl = QTableWidget(0, 8, dlg)
        tbl.setHorizontalHeaderLabels(
            ["Cand", "Utilizator", "Rol", "Pacient", "Telefon", "Status", "Actiune", "Programare ID"]
        )
        tbl.setEditTriggers(QAbstractItemView.EditTrigger.NoEditTriggers)
        tbl.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
        tbl.setSelectionMode(QAbstractItemView.SelectionMode.SingleSelection)
        tbl.setRowCount(len(rows))
        for i, r in enumerate(rows):
            tbl.setItem(i, 0, QTableWidgetItem(str(r.get("attempted_at") or "")))
            tbl.setItem(i, 1, QTableWidgetItem(str(r.get("source_user") or "")))
            tbl.setItem(i, 2, QTableWidgetItem(str(r.get("source_role") or "")))
            patient_txt = str(r.get("patient_name") or "").strip()
            pid = str(r.get("pacient_id") or "").strip()
            if patient_txt and pid:
                patient_txt = f"{patient_txt} (PID {pid})"
            elif pid:
                patient_txt = f"PID {pid}"
            tbl.setItem(i, 3, QTableWidgetItem(patient_txt))
            tbl.setItem(i, 4, QTableWidgetItem(str(r.get("phone") or "")))
            tbl.setItem(i, 5, QTableWidgetItem(str(r.get("status") or "")))
            tbl.setItem(i, 6, QTableWidgetItem(str(r.get("source_action") or r.get("dispatch_rule") or "")))
            tbl.setItem(i, 7, QTableWidgetItem(str(r.get("appointment_id") or "")))
            msg_val = (r.get("message") or "").strip()
            err_val = (r.get("error") or "").strip()
            tip_parts = []
            if msg_val:
                tip_parts.append(f"Mesaj: {msg_val}")
            if err_val:
                tip_parts.append(f"Eroare: {err_val}")
            if tip_parts:
                for col in range(tbl.columnCount()):
                    cell = tbl.item(i, col)
                    if cell is not None:
                        cell.setToolTip("\n".join(tip_parts))
        try:
            hh = tbl.horizontalHeader()
            hh.setSectionResizeMode(QHeaderView.ResizeMode.ResizeToContents)
            hh.setSectionResizeMode(3, QHeaderView.ResizeMode.Stretch)
        except Exception:
            pass
        root.addWidget(tbl, 1)

        btn_close = QPushButton("Inchide")
        apply_std_icon(btn_close, QStyle.StandardPixmap.SP_DialogCloseButton)
        btn_close.clicked.connect(dlg.accept)
        row_btn = QHBoxLayout()
        row_btn.addStretch(1)
        row_btn.addWidget(btn_close)
        root.addLayout(row_btn)
        dlg.exec()

    def _fetch_sms_target_rows(self, appointment_ids: List[int]) -> List[sqlite3.Row]:
        """Gestioneaza SMS target rows in `AppointmentsDialog`."""
        ids = [int(x) for x in appointment_ids if int(x) > 0]
        if not ids:
            return []
        conn = get_conn()
        _ensure_appointment_sms_template_state_table(conn)
        cur = conn.cursor()
        has_deleted = table_has_column("appointments", "deleted")
        has_location_fk = table_has_column("appointments", "location_id")
        has_status_col = table_has_column("appointments", "status")
        status_select = "a.status" if has_status_col else "'' AS status"
        location_join = "LEFT JOIN locations l ON l.id=a.location_id" if has_location_fk else ""
        location_select = "COALESCE(l.name,'')" if has_location_fk else "''"
        where = [f"a.id IN ({', '.join(['?'] * len(ids))})"]
        args: List[Any] = list(ids)
        if has_deleted:
            where.append("COALESCE(a.deleted,0)=0")
        cur.execute(
            f"""
            SELECT
                a.id,
                a.pacient_id,
                a.date,
                a.time,
                a.medic,
                {status_select},
                a.reminder_sms,
                COALESCE(m.nume_prenume,'') AS nume_prenume,
                {location_select} AS location_name
            FROM appointments a
            LEFT JOIN pacienti_master m ON m.id=a.pacient_id
            {location_join}
            WHERE {' AND '.join(where)}
            """,
            args,
        )
        rows = cur.fetchall()
        conn.close()
        by_id = {}
        for r in rows:
            try:
                by_id[int(r["id"])] = r
            except Exception:
                continue
        ordered: List[sqlite3.Row] = []
        for aid in ids:
            if aid in by_id:
                ordered.append(by_id[aid])
        return ordered

    def _auto_import_controls(self):
        """Automatizeaza import controls in `AppointmentsDialog`."""
        try:
            added = auto_create_appointments_from_controls()
            if added:
                self.crud.load_rows()
        except Exception:
            pass

    def _get_row(self) -> Optional[sqlite3.Row]:
        """Returneaza row in `AppointmentsDialog`."""
        row = self.crud.tbl.currentRow()
        if row < 0:
            return None
        it = self.crud.tbl.item(row, 0)
        if not it:
            return None
        try:
            appt_id = int(it.text())
        except Exception:
            return None
        conn = get_conn()
        cur = conn.cursor()
        cur.execute("SELECT * FROM appointments WHERE id=?", (appt_id,))
        r = cur.fetchone()
        conn.close()
        return r

    def show_qr(self):
        """Afiseaza codul QR de check-in pentru programarea selectata."""
        r = self._get_row()
        if not r:
            return
        code = r["checkin_code"] or ""
        if not code:
            QMessageBox.information(self, "Info", "Nu exista cod de check-in.")
            return
        d = AppointmentQrDialog(code, parent=self)
        d.exec()
        if QMessageBox.question(
            self,
            "Finalizare check-in",
            "Pacientul a efectuat check-in? Marchez acum programarea ca 'Check-in'.",
            QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
            QMessageBox.StandardButton.No,
        ) != QMessageBox.StandardButton.Yes:
            return
        changed, changed_ids = self._set_status_for_appointments(
            [int(r["id"])],
            "Check-in",
            source_action="appointments_qr_checkin",
        )
        try:
            log_action(
                "appointments_qr_checkin",
                json.dumps(
                    {
                        "appointment_id": int(r["id"]),
                        "pacient_id": int(r["pacient_id"] or 0) if "pacient_id" in r.keys() else 0,
                        "changed": int(changed),
                        "changed_ids": changed_ids,
                    },
                    ensure_ascii=False,
                ),
            )
        except Exception:
            pass
        if changed > 0:
            self.crud.load_rows()
            QMessageBox.information(self, "Check-in", "Programarea a fost marcata ca 'Check-in'.")

    def send_email(self):
        """Trimite email de notificare catre pacientii selectati si logheaza actiunea."""
        r = self._get_row()
        if not r:
            return
        email = (r["reminder_email"] or "").strip()
        if not email:
            try:
                pid = r["pacient_id"]
                m = get_master(int(pid)) if pid else None
                email = (m.get("email") or "").strip() if m else ""
            except Exception:
                email = ""
        if not email:
            QMessageBox.information(self, "Info", "Nu exista email.")
            return
        subject = "Reminder programare"
        body = f"Programare in data {r['date'] or ''} la ora {r['time'] or ''}."
        opened = QDesktopServices.openUrl(QUrl(f"mailto:{email}?subject={subject}&body={body}"))
        try:
            pid_val = int(r["pacient_id"] or 0)
        except Exception:
            pid_val = 0
        try:
            appt_id_val = int(r["id"] or 0)
        except Exception:
            appt_id_val = 0
        self._record_patient_communication(
            patient_id=pid_val,
            appointment_id=appt_id_val,
            channel="Email",
            status="initiat" if opened else "esuat",
            recipient=email,
            message=body,
            source_action="appointments_send_email",
        )
        try:
            log_action(
                "appointments_send_email",
                json.dumps(
                    {
                        "appointment_id": appt_id_val,
                        "pacient_id": pid_val,
                        "email": email,
                        "opened": bool(opened),
                    },
                    ensure_ascii=False,
                ),
            )
        except Exception:
            pass

    def _get_sent_today_ids_for_template(self, template_key: str, day_ymd: str) -> set:
        """Returneaza sent today ID-uri for template in `AppointmentsDialog`."""
        key = _normalize_forced_template_key(template_key) or "confirm"
        status_tag = f"manual_{key}"
        conn = get_conn()
        _ensure_reminder_runtime_tables(conn)
        cur = conn.cursor()
        cur.execute(
            """
            SELECT DISTINCT appointment_id
            FROM reminder_dispatch_log
            WHERE appointment_id IS NOT NULL
              AND dispatch_rule=?
              AND status=?
              AND attempted_at IS NOT NULL
              AND SUBSTR(attempted_at, 1, 10)=?
            """,
            (status_tag, f"{status_tag}_sent", (day_ymd or "").strip()),
        )
        out = set()
        for rr in cur.fetchall():
            try:
                out.add(int(rr[0]))
            except Exception:
                continue
        conn.close()
        return out

    def _build_sms_jobs(self, rows: List[sqlite3.Row], template_key: str) -> List[Dict[str, Any]]:
        """Construieste lotul de mesaje SMS pe baza selectiei si template-ului ales."""
        jobs: List[Dict[str, Any]] = []
        now_local = datetime.now()
        templates = _get_reminder_templates()
        for r in rows:
            try:
                appt_id = int(r["id"])
            except Exception:
                continue
            pid_val = r["pacient_id"] if "pacient_id" in r.keys() else None
            try:
                pid = int(pid_val) if pid_val is not None else None
            except Exception:
                pid = None
            name = (r["nume_prenume"] or "").strip() if "nume_prenume" in r.keys() else ""
            if not name:
                name = f"PID {pid}" if pid else "Pacient"
            phone = normalize_ro_mobile_phone(r["reminder_sms"]) or (r["reminder_sms"] or "").strip()
            msg = _build_reminder_message(r, now_local, templates, forced_template_key=template_key)
            jobs.append(
                {
                    "appointment_id": appt_id,
                    "patient_id": pid,
                    "patient_name": name,
                    "phone": phone,
                    "message": msg,
                }
            )
        return jobs

    def _confirm_sms_preview(self, jobs: List[Dict[str, Any]], template_label: str) -> bool:
        """Afiseaza preview + confirmare finala inainte de trimiterea SMS-urilor."""
        if not jobs:
            return False
        max_show = 25
        lines: List[str] = []
        for i, j in enumerate(jobs[:max_show], start=1):
            lines.append(
                f"{i}. {j.get('patient_name') or 'Pacient'} | tel: {j.get('phone') or '-'} | appt#{j.get('appointment_id') or '-'}"
            )
            lines.append((j.get("message") or "").strip())
            lines.append("")
        if len(jobs) > max_show:
            lines.append(f"... plus inca {len(jobs) - max_show} mesaje.")

        msg = QMessageBox(self)
        msg.setWindowTitle("Preview SMS")
        msg.setIcon(QMessageBox.Icon.Information)
        msg.setText(f"Template: {template_label}\nPreview pentru {len(jobs)} mesaje.")
        msg.setInformativeText("Verifica mesajele in detalii, apoi continua.")
        msg.setDetailedText("\n".join(lines).strip())
        msg.setStandardButtons(QMessageBox.StandardButton.Ok | QMessageBox.StandardButton.Cancel)
        ok_btn = msg.button(QMessageBox.StandardButton.Ok)
        if ok_btn is not None:
            ok_btn.setText("Continua")
        cancel_btn = msg.button(QMessageBox.StandardButton.Cancel)
        if cancel_btn is not None:
            cancel_btn.setText("Anuleaza")
        return msg.exec() == QMessageBox.StandardButton.Ok

    def send_sms(self):
        """Trimite SMS pentru selectie, cu reguli anti-duplicat si jurnalizare completa."""
        template_key = self._sms_template_key()
        set_setting("appointments_sms_template_key", template_key)

        selected_ids = self._checked_appointment_ids()
        if not selected_ids:
            QMessageBox.information(self, "SMS", "Bifeaza cel putin o programare in zona de selectie SMS.")
            return

        if template_key == "confirm":
            blocked_ids = [x for x in selected_ids if x in self._confirm_sms_sent_ids]
            blocked = len(blocked_ids)
            if blocked > 0:
                QMessageBox.warning(
                    self,
                    "Confirmare deja trimisa",
                    f"{blocked} programari au deja SMS de confirmare trimis si au fost excluse.",
                )
                self._log_manual_confirm_blocked(blocked_ids)
                self.refresh_sms_monitor_dashboard()
            selected_ids = [x for x in selected_ids if x not in set(blocked_ids)]
            if not selected_ids:
                self._apply_sms_selection_guard()
                return

        day_ymd = datetime.now().strftime("%Y-%m-%d")
        sent_today_ids = self._get_sent_today_ids_for_template(template_key, day_ymd)
        if sent_today_ids:
            dedup_ids = [x for x in selected_ids if x not in sent_today_ids]
            dup_count = len(selected_ids) - len(dedup_ids)
            if dup_count > 0:
                QMessageBox.warning(
                    self,
                    "Anti-duplicat",
                    f"{dup_count} programari au deja SMS trimis azi pentru template-ul selectat si au fost excluse.",
                )
            selected_ids = dedup_ids
            if not selected_ids:
                self._apply_sms_selection_guard()
                return

        rows = self._fetch_sms_target_rows(selected_ids)
        if not rows:
            QMessageBox.information(self, "SMS", "Nu exista programari valide pentru trimitere.")
            return

        patient_ids_for_opt = []
        row_by_appt_id: Dict[int, sqlite3.Row] = {}
        for rr in rows:
            try:
                appt_id_val = int(rr["id"])
                row_by_appt_id[appt_id_val] = rr
            except Exception:
                continue
            try:
                pid_val = int(rr["pacient_id"] or 0)
            except Exception:
                pid_val = 0
            if pid_val > 0:
                patient_ids_for_opt.append(pid_val)

        opt_out_pids = get_sms_opt_out_patient_ids(patient_ids_for_opt)
        if opt_out_pids:
            blocked_opt_ids: List[int] = []
            for aid in list(selected_ids):
                rr = row_by_appt_id.get(int(aid))
                if rr is None:
                    continue
                try:
                    pid_val = int(rr["pacient_id"] or 0)
                except Exception:
                    pid_val = 0
                if pid_val > 0 and pid_val in opt_out_pids:
                    blocked_opt_ids.append(int(aid))
            if blocked_opt_ids:
                QMessageBox.warning(
                    self,
                    "SMS",
                    f"{len(blocked_opt_ids)} programari apartin unor pacienti cu SMS dezactivat si au fost excluse.",
                )
                selected_ids = [x for x in selected_ids if int(x) not in set(blocked_opt_ids)]
                if not selected_ids:
                    self._apply_sms_selection_guard()
                    return
                rows = self._fetch_sms_target_rows(selected_ids)
                row_by_appt_id = {int(r["id"]): r for r in rows if "id" in r.keys()}

        label_map = {
            "confirm": "Confirmare",
            "cancel": "Anulare",
            "ortopedie": "Ortopedie",
            "fizioterapie": "Fizioterapie",
        }
        choice_label = label_map.get(template_key, template_key)

        jobs = self._build_sms_jobs(rows, template_key)
        if not jobs:
            QMessageBox.information(self, "SMS", "Nu exista mesaje valide pentru trimitere.")
            return

        if not self._confirm_sms_preview(jobs, choice_label):
            return

        patient_ids = set()
        for j in jobs:
            try:
                pid = int(j.get("patient_id") or 0)
            except Exception:
                pid = 0
            if pid > 0:
                patient_ids.add(pid)
        total_patients = len(patient_ids) if patient_ids else len(jobs)
        bulk_threshold = _setting_int(
            SMS_BULK_CONFIRM_THRESHOLD_KEY,
            SMS_BULK_CONFIRM_THRESHOLD_DEFAULT,
            5,
            5000,
        )
        ans = QMessageBox.question(
            self,
            "Confirmare finala",
            f"Vor fi trimise {len(jobs)} mesaje ({choice_label}) catre {total_patients} pacienti. Continui?",
            QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
            QMessageBox.StandardButton.No,
        )
        if ans != QMessageBox.StandardButton.Yes:
            return
        if len(jobs) >= bulk_threshold:
            warn_bulk = QMessageBox.question(
                self,
                "Confirmare suplimentara",
                f"Lot mare detectat ({len(jobs)} SMS >= prag {bulk_threshold}).\nConfirmi trimiterea?",
                QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
                QMessageBox.StandardButton.No,
            )
            if warn_bulk != QMessageBox.StandardButton.Yes:
                return

        sms_cfg = build_sms_gateway_runtime_config()
        trigger_txt = datetime.now().strftime("%Y-%m-%d %H:%M")
        sent = 0
        failed: List[str] = []
        skipped_no_phone = 0
        skipped_opt_out = 0

        progress = QProgressDialog("Trimit SMS...", "Anuleaza", 0, len(jobs), self)
        progress.setWindowTitle("SMS Programari")
        progress.setWindowModality(Qt.WindowModality.WindowModal)
        progress.setAutoClose(True)
        progress.setAutoReset(True)
        progress.show()

        conn = get_conn()
        _ensure_appointment_sms_template_state_table(conn)
        cur = conn.cursor()
        for idx, job in enumerate(jobs, start=1):
            if progress.wasCanceled():
                break
            appt_id = int(job["appointment_id"])
            attempted_at = now_ts()
            phone = (job.get("phone") or "").strip()
            msg = (job.get("message") or "").strip()
            status_tag = f"manual_{template_key}"
            pid_job = int(job.get("patient_id") or 0) if str(job.get("patient_id") or "").strip() else 0

            if pid_job > 0 and pid_job in opt_out_pids:
                skipped_opt_out += 1
                _upsert_appointment_sms_template_state(
                    cur,
                    appt_id,
                    template_key=template_key,
                    status="skipped_opt_out",
                    error="Pacient cu SMS dezactivat",
                    sent_at="",
                )
                _insert_reminder_log(
                    cur,
                    appt_id,
                    trigger_at=trigger_txt,
                    attempted_at=attempted_at,
                    status=f"{status_tag}_skipped_opt_out",
                    phone="",
                    message=msg,
                    response="",
                    error="sms_opt_out",
                    attempts=1,
                    dispatch_rule=status_tag,
                    source_action="manual_send_sms_opt_out",
                )
                self._insert_medical_history_comm_cur(
                    cur,
                    patient_id=pid_job,
                    appointment_id=appt_id,
                    channel="SMS",
                    status="dezactivat",
                    recipient=phone,
                    message=msg,
                    source_action="manual_send_sms_opt_out",
                )
                conn.commit()
                progress.setValue(idx)
                progress.setLabelText(f"SMS {idx}/{len(jobs)}")
                QApplication.processEvents()
                continue

            if not phone:
                skipped_no_phone += 1
                _upsert_appointment_sms_template_state(
                    cur,
                    appt_id,
                    template_key=template_key,
                    status="skipped_no_phone",
                    error="Numar de telefon invalid sau lipsa",
                    sent_at="",
                )
                _insert_reminder_log(
                    cur,
                    appt_id,
                    trigger_at=trigger_txt,
                    attempted_at=attempted_at,
                    status=f"{status_tag}_skipped_no_phone",
                    phone="",
                    message=msg,
                    response="",
                    error="Numar de telefon invalid sau lipsa",
                    attempts=1,
                    dispatch_rule=status_tag,
                    source_action="manual_send_sms_no_phone",
                )
                self._insert_medical_history_comm_cur(
                    cur,
                    patient_id=pid_job,
                    appointment_id=appt_id,
                    channel="SMS",
                    status="fara_telefon",
                    recipient=phone,
                    message=msg,
                    source_action="manual_send_sms_no_phone",
                )
                conn.commit()
                progress.setValue(idx)
                progress.setLabelText(f"SMS {idx}/{len(jobs)}")
                QApplication.processEvents()
                continue

            try:
                res = _send_sms_with_retry(
                    phone,
                    msg,
                    sms_config=sms_cfg,
                    cancelled_cb=lambda: progress.wasCanceled(),
                )
                sent += 1
                pretty_res = ""
                try:
                    pretty_res = json.dumps(res, ensure_ascii=False)
                except Exception:
                    pretty_res = str(res)
                attempts_used = int(res.get("attempt", 1)) if isinstance(res, dict) else 1
                _upsert_appointment_sms_template_state(
                    cur,
                    appt_id,
                    template_key=template_key,
                    status="sent",
                    error="",
                    sent_at=attempted_at,
                )
                _insert_reminder_log(
                    cur,
                    appt_id,
                    trigger_at=trigger_txt,
                    attempted_at=attempted_at,
                    status=f"{status_tag}_sent",
                    phone=phone,
                    message=msg,
                    response=pretty_res,
                    error="",
                    attempts=attempts_used,
                    dispatch_rule=status_tag,
                    source_action="manual_send_sms_sent",
                )
                self._insert_medical_history_comm_cur(
                    cur,
                    patient_id=pid_job,
                    appointment_id=appt_id,
                    channel="SMS",
                    status="trimis",
                    recipient=phone,
                    message=msg,
                    source_action="manual_send_sms_sent",
                )
                conn.commit()
            except Exception as e:
                err = str(e)
                failed.append(f"#{appt_id}: {err}")
                _upsert_appointment_sms_template_state(
                    cur,
                    appt_id,
                    template_key=template_key,
                    status="failed",
                    error=err,
                    sent_at="",
                )
                _insert_reminder_log(
                    cur,
                    appt_id,
                    trigger_at=trigger_txt,
                    attempted_at=attempted_at,
                    status=f"{status_tag}_failed",
                    phone=phone,
                    message=msg,
                    response="",
                    error=err,
                    attempts=_setting_int(SMS_IMMEDIATE_RETRY_MAX_KEY, SMS_IMMEDIATE_RETRY_MAX_DEFAULT, 1, 6),
                    dispatch_rule=status_tag,
                    source_action="manual_send_sms_failed",
                )
                self._insert_medical_history_comm_cur(
                    cur,
                    patient_id=pid_job,
                    appointment_id=appt_id,
                    channel="SMS",
                    status="esuat",
                    recipient=phone,
                    message=msg,
                    source_action="manual_send_sms_failed",
                )
                conn.commit()

            progress.setValue(idx)
            progress.setLabelText(f"SMS {idx}/{len(jobs)}")
            QApplication.processEvents()
        conn.close()

        for appt_id in selected_ids:
            self._sms_checked_ids.discard(int(appt_id))
        self._refresh_confirm_sms_cache()
        self._sync_confirm_sms_status_column()
        self._sync_sms_checkboxes()
        self._apply_sms_selection_guard()

        lines = [
            f"Template: {choice_label}",
            f"Trimise: {sent}",
            f"Fara telefon: {skipped_no_phone}",
            f"SMS dezactivat: {skipped_opt_out}",
            f"Erori: {len(failed)}",
        ]
        try:
            log_action(
                "appointments_send_sms_manual",
                json.dumps(
                    {
                        "template": template_key,
                        "selected_count": len(selected_ids),
                        "sent": int(sent),
                        "skipped_no_phone": int(skipped_no_phone),
                        "skipped_opt_out": int(skipped_opt_out),
                        "failed": int(len(failed)),
                    },
                    ensure_ascii=False,
                ),
            )
        except Exception:
            pass
        if failed:
            sample = "\n".join(failed[:8])
            QMessageBox.warning(self, "SMS Programari", "\n".join(lines) + f"\n\nDetalii:\n{sample}")
        else:
            QMessageBox.information(self, "SMS Programari", "\n".join(lines))
        self.refresh_sms_monitor_dashboard()

    def mark_checkin(self):
        """Marcheaza check-in pentru programarea selectata si actualizeaza fluxul pacientului."""
        r = self._get_row()
        if not r:
            return
        changed, changed_ids = self._set_status_for_appointments(
            [int(r["id"])],
            "Check-in",
            source_action="appointments_checkin_button",
        )
        try:
            log_action(
                "appointments_checkin_button",
                json.dumps(
                    {
                        "appointment_id": int(r["id"]),
                        "pacient_id": int(r["pacient_id"] or 0) if "pacient_id" in r.keys() else 0,
                        "changed": int(changed),
                        "changed_ids": changed_ids,
                    },
                    ensure_ascii=False,
                ),
            )
        except Exception:
            pass
        self.crud.load_rows()

    def _wrap_crud_loader(self):
        """Infasoara CRUD loader in `AppointmentsDialog`."""
        if getattr(self, "_crud_wrapped", False):
            return
        self._crud_wrapped = True
        orig = self.crud.load_rows

        def _wrapped():
            """Infasoara functia initiala cu logica suplimentara de refresh (helper intern pentru `_wrap_crud_loader`)."""
            orig()
            self._reload_filter_medic_values()
            self._refresh_calendar_marks()
            self._refresh_confirm_sms_cache()
            self._sync_confirm_sms_status_column()
            self._sync_sms_checkboxes()
            self._apply_sms_selection_guard()
            self.refresh_sms_monitor_dashboard()

        self.crud.load_rows = _wrapped

    def _refresh_calendar_marks(self):
        """Gestioneaza calendar marks in `AppointmentsDialog`."""
        try:
            conn = get_conn()
            cur = conn.cursor()
            if table_has_column("appointments", "deleted"):
                cur.execute("""
                    SELECT DISTINCT date FROM appointments
                    WHERE COALESCE(deleted,0)=0 AND date IS NOT NULL AND TRIM(date) <> ''
                """)
            else:
                cur.execute("""
                    SELECT DISTINCT date FROM appointments
                    WHERE date IS NOT NULL AND TRIM(date) <> ''
                """)
            rows = cur.fetchall()
            conn.close()

            clear_fmt = QTextCharFormat()
            for d in list(self._marked_dates):
                self.cal.setDateTextFormat(d, clear_fmt)
            self._marked_dates.clear()

            fmt = QTextCharFormat()
            fmt.setBackground(QColor("#e8f4ff"))
            fmt.setForeground(QColor("#0b3d91"))
            fmt.setFontWeight(QFont.Weight.Bold)

            for r in rows:
                dstr = str(r[0]) if r and r[0] is not None else ""
                qd = QDate.fromString(dstr, "yyyy-MM-dd")
                if qd.isValid():
                    self.cal.setDateTextFormat(qd, fmt)
                    self._marked_dates.add(qd)
        except Exception:
            pass


# ============================================================
# UI: Waiting list / Tasks / Insurance / Lab import / Dashboard / Labels
# ============================================================
class WaitingListDialog(QDialog):
    def __init__(self, parent=None):
        """Initializeaza dialogul `WaitingListDialog` si configureaza controalele interfetei."""
        super().__init__(parent)
        self.setWindowTitle("Lista asteptare")
        self.resize(820, 520)
        root = QVBoxLayout(self)
        self.crud = SimpleCrudWidget(
            "Lista asteptare",
            "waiting_list",
            [
                ("Pacient ID", "pacient_id"),
                ("Prioritate", "priority"),
                ("Motiv", "reason"),
                ("Status", "status"),
                ("Creat", "created_at"),
            ],
            [
                {"key": "pacient_id", "label": "Pacient ID"},
                {"key": "priority", "label": "Prioritate", "type": "int"},
                {"key": "reason", "label": "Motiv"},
                {"key": "status", "label": "Status", "type": "choice", "choices": ["Asteptare", "In consult", "Rezolvat"]},
                {"key": "created_at", "label": "Creat la"},
                {"key": "notes", "label": "Note", "type": "multiline"},
                {"key": "location_id", "label": "Sediu ID"},
            ],
            patient_id=None,
            insert_defaults={
                "created_at": lambda: datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
                "location_id": lambda: get_current_location_id(),
            },
            can_add_roles=("admin", "receptie"),
            can_edit_roles=("admin", "receptie"),
            can_delete_roles=("admin",),
        )
        root.addWidget(self.crud, 1)


class TasksDialog(QDialog):
    def __init__(self, parent=None):
        """Initializeaza dialogul `TasksDialog` si configureaza controalele interfetei."""
        super().__init__(parent)
        self.setWindowTitle("Taskuri interne")
        self.resize(820, 520)
        root = QVBoxLayout(self)
        self.crud = SimpleCrudWidget(
            "Taskuri",
            "tasks",
            [
                ("Titlu", "title"),
                ("Asignat", "assigned_to"),
                ("Scadenta", "due_date"),
                ("Status", "status"),
                ("Creat", "created_at"),
            ],
            [
                {"key": "title", "label": "Titlu"},
                {"key": "assigned_to", "label": "Asignat"},
                {"key": "due_date", "label": "Scadenta", "type": "date"},
                {"key": "status", "label": "Status", "type": "choice", "choices": ["Nou", "In lucru", "Terminat"]},
                {"key": "notes", "label": "Note", "type": "multiline"},
                {"key": "created_at", "label": "Creat la"},
            ],
            patient_id=None,
            insert_defaults={"created_at": lambda: datetime.now().strftime("%Y-%m-%d %H:%M:%S")},
            can_add_roles=("admin", "medic", "asistenta", "receptie"),
            can_edit_roles=("admin", "medic", "asistenta", "receptie"),
            can_delete_roles=("admin",),
        )
        root.addWidget(self.crud, 1)


class InsuranceClaimsDialog(QDialog):
    def __init__(self, parent=None):
        """Initializeaza dialogul `InsuranceClaimsDialog` si configureaza controalele interfetei."""
        super().__init__(parent)
        self.setWindowTitle("Decontari / Asigurari")
        self.resize(820, 520)
        root = QVBoxLayout(self)
        self.crud = SimpleCrudWidget(
            "Decontari",
            "insurance_claims",
            [
                ("Pacient ID", "pacient_id"),
                ("Asigurator", "insurer"),
                ("Polita", "policy_no"),
                ("Suma", "amount"),
                ("Status", "status"),
                ("Factura ID", "invoice_id"),
            ],
            [
                {"key": "pacient_id", "label": "Pacient ID"},
                {
                    "key": "insurer",
                    "label": "Asigurator",
                },
                {"key": "policy_no", "label": "Numar polita"},
                {"key": "amount", "label": "Suma", "type": "float"},
                {"key": "status", "label": "Status", "type": "choice", "choices": ["Depus", "Aprobat", "Respins", "Platit"]},
                {"key": "invoice_id", "label": "Factura ID"},
                {"key": "notes", "label": "Note", "type": "multiline"},
                {"key": "created_at", "label": "Creat la"},
            ],
            patient_id=None,
            insert_defaults={"created_at": lambda: datetime.now().strftime("%Y-%m-%d %H:%M:%S")},
            can_add_roles=("admin", "receptie"),
            can_edit_roles=("admin", "receptie"),
            can_delete_roles=("admin",),
        )
        root.addWidget(self.crud, 1)


class LabImportDialog(QDialog):
    def __init__(self, parent=None):
        """Initializeaza dialogul `LabImportDialog` si configureaza controalele interfetei."""
        super().__init__(parent)
        self.setWindowTitle("Import laborator (CSV)")
        self.resize(480, 240)
        root = QVBoxLayout(self)
        root.addWidget(QLabel("CSV cu coloane: pacient_id, date, test_name, status, lab, result_text, result_file, notes"))
        btn = QPushButton("Importa CSV")
        apply_std_icon(btn, QStyle.StandardPixmap.SP_DialogOpenButton)
        root.addWidget(btn)
        btn.clicked.connect(self.import_csv)

    def import_csv(self):
        """Importa CSV in `LabImportDialog`."""
        path, _ = QFileDialog.getOpenFileName(self, "Alege CSV", "", "CSV (*.csv)")
        if not path:
            return
        rows = 0
        try:
            with open(path, "r", encoding="utf-8") as f:
                reader = csv.DictReader(f)
                conn = get_conn()
                cur = conn.cursor()
                insert_cols = ["pacient_id", "date", "test_name", "status", "lab", "result_text", "result_file", "notes"]
                has_sync_id = table_has_column("lab_orders", "sync_id")
                has_updated_at = table_has_column("lab_orders", "updated_at")
                has_deleted = table_has_column("lab_orders", "deleted")
                has_device_id = table_has_column("lab_orders", "device_id")
                if has_sync_id:
                    insert_cols.append("sync_id")
                if has_updated_at:
                    insert_cols.append("updated_at")
                if has_deleted:
                    insert_cols.append("deleted")
                if has_device_id:
                    insert_cols.append("device_id")
                sql_insert = (
                    f"INSERT INTO lab_orders({', '.join(insert_cols)}) "
                    f"VALUES ({', '.join(['?'] * len(insert_cols))})"
                )
                for r in reader:
                    pid = r.get("pacient_id") or ""
                    if not str(pid).strip().isdigit():
                        continue
                    vals: List[Any] = [
                        int(pid),
                        r.get("date") or "",
                        r.get("test_name") or "",
                        r.get("status") or "",
                        r.get("lab") or "",
                        r.get("result_text") or "",
                        r.get("result_file") or "",
                        r.get("notes") or "",
                    ]
                    if has_sync_id:
                        vals.append(uuid.uuid4().hex)
                    if has_updated_at:
                        vals.append(now_ts())
                    if has_deleted:
                        vals.append(0)
                    if has_device_id:
                        vals.append(get_device_id())
                    cur.execute(sql_insert, tuple(vals))
                    rows += 1
                conn.commit()
                conn.close()
            QMessageBox.information(self, "OK", f"Importate {rows} randuri.")
        except Exception as e:
            QMessageBox.critical(self, "Eroare", str(e))


class LabelsDialog(QDialog):
    def __init__(self, parent=None):
        """Initializeaza dialogul `LabelsDialog` si configureaza controalele interfetei."""
        super().__init__(parent)
        self.setWindowTitle("Etichete pacient")
        self.resize(520, 320)
        root = QVBoxLayout(self)
        form = QFormLayout()
        self.ed_pid = QLineEdit()
        self.ed_pid.setPlaceholderText("ID pacient")
        self.ed_extra = QLineEdit()
        self.ed_extra.setPlaceholderText("Text extra")
        form.addRow("Pacient ID:", self.ed_pid)
        form.addRow("Text extra:", self.ed_extra)
        root.addLayout(form)
        self.btn_export = QPushButton("Exporta eticheta PDF")
        root.addWidget(self.btn_export)
        self.btn_export.clicked.connect(self.export_label)

    def export_label(self):
        """Exporta label in `LabelsDialog`."""
        pid = (self.ed_pid.text() or "").strip()
        if not pid.isdigit():
            QMessageBox.warning(self, "Eroare", "ID pacient invalid.")
            return
        m = get_master(int(pid))
        if not m:
            QMessageBox.warning(self, "Eroare", "Pacientul nu exista.")
            return
        extra = self.ed_extra.text().strip()
        content = f"{m['nume_prenume'] or ''}\nCNP: {m['cnp'] or ''}\n{extra}"
        meta = {"nume_prenume": m["nume_prenume"] or "", "cnp": m["cnp"] or "", "data": "", "medic": ""}
        pdf_path = generate_text_report_pdf("Eticheta pacient", content, meta, prefix="label")
        d = ReportPreviewDialog(pdf_path, parent=self)
        d.exec()


class DashboardDialog(QDialog):
    def __init__(self, parent=None):
        """Initializeaza dialogul `DashboardDialog` si configureaza controalele interfetei."""
        super().__init__(parent)
        self.setWindowTitle("Dashboard")
        self.resize(900, 540)
        root = QVBoxLayout(self)
        try:
            from matplotlib.backends.backend_qtagg import FigureCanvasQTAgg as FigureCanvas
            from matplotlib.figure import Figure
        except Exception:
            QMessageBox.warning(self, "Lipseste matplotlib", matplotlib_missing_message())
            lbl = QLabel("Grafice indisponibile.")
            root.addWidget(lbl)
            return

        self.figure = Figure(figsize=(8, 4))
        self.canvas = FigureCanvas(self.figure)
        root.addWidget(self.canvas, 1)
        self.draw()

    def draw(self):
        """Deseneaza vizualizarea pe baza datelor curente."""
        self.figure.clear()
        ax1 = self.figure.add_subplot(121)
        ax2 = self.figure.add_subplot(122)

        conn = get_conn()
        cur = conn.cursor()
        cur.execute("""
            SELECT substr(data_consultului,1,7) as ym, COUNT(*)
            FROM consulturi
            WHERE data_consultului IS NOT NULL AND data_consultului <> ''
            GROUP BY ym
            ORDER BY ym
        """)
        rows = cur.fetchall()
        months = [r[0] for r in rows]
        counts = [r[1] for r in rows]

        cur.execute("""
            SELECT substr(date,1,7) as ym, COALESCE(SUM(total),0)
            FROM invoices
            WHERE date IS NOT NULL AND date <> ''
            GROUP BY ym
            ORDER BY ym
        """)
        rows2 = cur.fetchall()
        months2 = [r[0] for r in rows2]
        sums = [r[1] for r in rows2]
        conn.close()

        ax1.set_title("Consulturi/luna")
        ax1.plot(months, counts, marker="o")
        ax1.tick_params(axis='x', rotation=45)

        ax2.set_title("Venituri/luna")
        ax2.bar(months2, sums)
        ax2.tick_params(axis='x', rotation=45)

        try:
            with warnings.catch_warnings():
                warnings.simplefilter("ignore", UserWarning)
                self.figure.tight_layout()
        except Exception:
            pass
        self.canvas.draw()

# ============================================================
# UI: Patient modules
# ============================================================
class PatientModulesDialog(QDialog):
    def __init__(self, pacient_id: int, parent=None):
        """Initializeaza dialogul `PatientModulesDialog` si configureaza controalele interfetei."""
        super().__init__(parent)
        self.pacient_id = pacient_id
        self.setWindowTitle("Module pacient")
        self.resize(1100, 680)

        root = QVBoxLayout(self)
        tabs = QTabWidget()
        root.addWidget(tabs, 1)

        roles_add_edit = ("admin", "medic", "asistenta")
        roles_delete = ("admin", "medic")
        roles_billing_add = ("admin", "receptie")
        roles_billing_edit = ("admin", "receptie")
        roles_billing_delete = ("admin",)

        flow = SimpleCrudWidget(
            "Traseu pacient",
            "patient_flow",
            [
                ("Status", "status"),
                ("Check-in", "checkin_time"),
                ("Triere", "triage_time"),
                ("Start consult", "consult_start"),
                ("Sfarsit consult", "consult_end"),
                ("Externare", "discharge_time"),
                ("Note", "notes"),
            ],
            [
                {"key": "status", "label": "Status", "type": "choice", "choices": ["Check-in", "Triere", "Consult", "Externare"]},
                {"key": "checkin_time", "label": "Check-in"},
                {"key": "triage_time", "label": "Triere"},
                {"key": "consult_start", "label": "Start consult"},
                {"key": "consult_end", "label": "Sfarsit consult"},
                {"key": "discharge_time", "label": "Externare"},
                {"key": "notes", "label": "Note", "type": "multiline"},
            ],
            patient_id=pacient_id,
            insert_defaults={"created_at": lambda: datetime.now().strftime("%Y-%m-%d %H:%M:%S")},
            can_add_roles=roles_add_edit,
            can_edit_roles=roles_add_edit,
            can_delete_roles=roles_delete,
        )
        tabs.addTab(flow, "Traseu")

        hist = SimpleCrudWidget(
            "Istoric medical",
            "medical_history",
            [
                ("Categorie", "category"),
                ("Element", "item"),
                ("De la", "start_date"),
                ("Pana la", "end_date"),
                ("Note", "notes"),
            ],
            [
                {"key": "category", "label": "Categorie", "type": "choice", "choices": ["Diagnostic", "Alergie", "Medicatie", "Comunicare"]},
                {"key": "item", "label": "Element"},
                {"key": "start_date", "label": "De la", "type": "date"},
                {"key": "end_date", "label": "Pana la", "type": "date"},
                {"key": "notes", "label": "Note", "type": "multiline"},
            ],
            patient_id=pacient_id,
            can_add_roles=roles_add_edit,
            can_edit_roles=roles_add_edit,
            can_delete_roles=roles_delete,
        )
        tabs.addTab(hist, "Istoric")

        plans = SimpleCrudWidget(
            "Planuri tratament",
            "treatment_plans",
            [
                ("Nume", "name"),
                ("Protocol", "protocol"),
                ("Start", "start_date"),
                ("End", "end_date"),
                ("Status", "status"),
                ("Note", "notes"),
            ],
            [
                {"key": "name", "label": "Nume"},
                {"key": "protocol", "label": "Protocol", "type": "multiline"},
                {"key": "start_date", "label": "Start", "type": "date"},
                {"key": "end_date", "label": "End", "type": "date"},
                {"key": "status", "label": "Status", "type": "choice", "choices": ["Activ", "Inchis", "Suspendat"]},
                {"key": "notes", "label": "Note", "type": "multiline"},
            ],
            patient_id=pacient_id,
            can_add_roles=roles_add_edit,
            can_edit_roles=roles_add_edit,
            can_delete_roles=roles_delete,
        )
        tabs.addTab(plans, "Planuri")

        presc = SimpleCrudWidget(
            "Retete",
            "prescriptions",
            [
                ("Data", "date"),
                ("Medic", "doctor"),
                ("Sablon", "template_name"),
                ("Continut", "content"),
                ("Fisier", "file_path"),
                ("Semnat de", "signed_by"),
                ("Semnat la", "signed_at"),
            ],
            [
                {"key": "date", "label": "Data", "type": "date"},
                {"key": "doctor", "label": "Medic", "type": "choice", "choices": get_medic_dropdown_values()},
                {"key": "template_name", "label": "Sablon"},
                {"key": "content", "label": "Continut", "type": "multiline"},
                {"key": "file_path", "label": "Fisier", "type": "file"},
                {"key": "signed_by", "label": "Semnat de"},
                {"key": "signature_path", "label": "Semnatura", "type": "file"},
                {"key": "signed_at", "label": "Semnat la"},
            ],
            patient_id=pacient_id,
            file_col_key="file_path",
            template_provider={
                "title": "Reteta din sablon",
                "templates": PRESCRIPTION_TEMPLATES,
                "export_title": "Reteta",
                "include_letter_type": False,
            },
            can_add_roles=roles_add_edit,
            can_edit_roles=roles_add_edit,
            can_delete_roles=roles_delete,
        )
        tabs.addTab(presc, "Retete")

        letters = SimpleCrudWidget(
            "Scrisori medicale",
            "medical_letters",
            [
                ("Data", "date"),
                ("Medic", "doctor"),
                ("Tip", "letter_type"),
                ("Sablon", "template_name"),
                ("Continut", "content"),
                ("Fisier", "file_path"),
                ("Semnat de", "signed_by"),
                ("Semnat la", "signed_at"),
            ],
            [
                {"key": "date", "label": "Data", "type": "date"},
                {"key": "doctor", "label": "Medic", "type": "choice", "choices": get_medic_dropdown_values()},
                {"key": "letter_type", "label": "Tip", "type": "choice", "choices": ["Scrisoare medicala", "Adeverinta", "Bilet externare"]},
                {"key": "template_name", "label": "Sablon"},
                {"key": "content", "label": "Continut", "type": "multiline"},
                {"key": "file_path", "label": "Fisier", "type": "file"},
                {"key": "signed_by", "label": "Semnat de"},
                {"key": "signature_path", "label": "Semnatura", "type": "file"},
                {"key": "signed_at", "label": "Semnat la"},
            ],
            patient_id=pacient_id,
            file_col_key="file_path",
            template_provider={
                "title": "Scrisoare din sablon",
                "templates": LETTER_TEMPLATES,
                "export_title": "Scrisoare",
                "include_letter_type": True,
            },
            can_add_roles=roles_add_edit,
            can_edit_roles=roles_add_edit,
            can_delete_roles=roles_delete,
        )
        tabs.addTab(letters, "Scrisori")

        docs = SimpleCrudWidget(
            "Documente",
            "documents",
            [
                ("Categorie", "category"),
                ("Titlu", "title"),
                ("Data", "date"),
                ("Fisier", "file_path"),
                ("Note", "notes"),
            ],
            [
                {"key": "category", "label": "Categorie", "type": "choice", "choices": ["Analize", "Imaging", "Scanare", "Altele"]},
                {"key": "title", "label": "Titlu"},
                {"key": "date", "label": "Data", "type": "date"},
                {"key": "file_path", "label": "Fisier", "type": "file"},
                {"key": "notes", "label": "Note", "type": "multiline"},
            ],
            patient_id=pacient_id,
            file_col_key="file_path",
            can_add_roles=roles_add_edit,
            can_edit_roles=roles_add_edit,
            can_delete_roles=roles_delete,
        )
        tabs.addTab(docs, "Documente")

        alerts = SimpleCrudWidget(
            "Alerte clinice",
            "clinical_alerts",
            [
                ("Tip", "alert_type"),
                ("Mesaj", "message"),
                ("Activ", "active"),
                ("Scadenta", "due_date"),
            ],
            [
                {"key": "alert_type", "label": "Tip", "type": "choice", "choices": ["Alergie", "Interactiune", "Control programat", "Altele"]},
                {"key": "message", "label": "Mesaj", "type": "multiline"},
                {"key": "active", "label": "Activ", "type": "bool"},
                {"key": "due_date", "label": "Scadenta", "type": "date"},
            ],
            patient_id=pacient_id,
            insert_defaults={"created_at": lambda: datetime.now().strftime("%Y-%m-%d %H:%M:%S")},
            can_add_roles=roles_add_edit,
            can_edit_roles=roles_add_edit,
            can_delete_roles=roles_delete,
        )
        tabs.addTab(alerts, "Alerte")

        vacc = SimpleCrudWidget(
            "Vaccinari",
            "vaccinations",
            [
                ("Vaccin", "vaccine"),
                ("Doza", "dose"),
                ("Data", "date"),
                ("Scadenta", "due_date"),
                ("Status", "status"),
                ("Note", "notes"),
            ],
            [
                {"key": "vaccine", "label": "Vaccin"},
                {"key": "dose", "label": "Doza"},
                {"key": "date", "label": "Data", "type": "date"},
                {"key": "due_date", "label": "Scadenta", "type": "date"},
                {"key": "status", "label": "Status", "type": "choice", "choices": ["Programat", "Efectuat", "Amanat"]},
                {"key": "notes", "label": "Note", "type": "multiline"},
            ],
            patient_id=pacient_id,
            can_add_roles=roles_add_edit,
            can_edit_roles=roles_add_edit,
            can_delete_roles=roles_delete,
        )
        tabs.addTab(vacc, "Vaccinari")

        lab = SimpleCrudWidget(
            "Laborator",
            "lab_orders",
            [
                ("Data", "date"),
                ("Test", "test_name"),
                ("Status", "status"),
                ("Laborator", "lab"),
                ("Rezultat", "result_text"),
                ("Fisier", "result_file"),
                ("Note", "notes"),
            ],
            [
                {"key": "date", "label": "Data", "type": "date"},
                {"key": "test_name", "label": "Test"},
                {"key": "status", "label": "Status", "type": "choice", "choices": ["Cerere", "In lucru", "Gata"]},
                {"key": "lab", "label": "Laborator"},
                {"key": "result_text", "label": "Rezultat", "type": "multiline"},
                {"key": "result_file", "label": "Fisier", "type": "file"},
                {"key": "notes", "label": "Note", "type": "multiline"},
            ],
            patient_id=pacient_id,
            file_col_key="result_file",
            can_add_roles=roles_add_edit,
            can_edit_roles=roles_add_edit,
            can_delete_roles=roles_delete,
        )
        tabs.addTab(lab, "Laborator")

        bill = SimpleCrudWidget(
            "Facturare",
            "invoices",
            [
                ("Data", "date"),
                ("Total", "total"),
                ("Metoda", "method"),
                ("Status", "status"),
                ("Note", "notes"),
            ],
            [
                {"key": "date", "label": "Data", "type": "date"},
                {"key": "total", "label": "Total", "type": "float"},
                {"key": "method", "label": "Metoda", "type": "choice", "choices": ["Cash", "Card", "Decontare"]},
                {"key": "status", "label": "Status", "type": "choice", "choices": ["Neplatit", "Platit"]},
                {"key": "notes", "label": "Note", "type": "multiline"},
            ],
            patient_id=pacient_id,
            can_add_roles=roles_billing_add,
            can_edit_roles=roles_billing_edit,
            can_delete_roles=roles_billing_delete,
        )
        tabs.addTab(bill, "Facturare")


# ============================================================
# Interop helpers
# ============================================================
def _gender_from_sex(sex: Optional[str]) -> str:
    """Gestioneaza from sex."""
    s = (sex or "").strip().lower()
    if s in ("masculin", "m", "male"):
        return "male"
    if s in ("feminin", "f", "female"):
        return "female"
    return "unknown"


def build_fhir_bundle() -> Dict[str, Any]:
    """Construieste FHIR bundle."""
    conn = get_conn()
    cur = conn.cursor()
    cur.execute("SELECT * FROM pacienti_master")
    patients = cur.fetchall()
    cur.execute("SELECT * FROM consulturi")
    consults = cur.fetchall()
    conn.close()

    entries: List[Dict[str, Any]] = []
    for p in patients:
        pid = p["id"]
        res = {
            "resourceType": "Patient",
            "id": str(pid),
            "name": [{"text": p["nume_prenume"] or ""}],
            "gender": _gender_from_sex(p["sex"]),
            "birthDate": p["data_nasterii"] or None,
            "telecom": [{"system": "phone", "value": p["telefon"] or ""}],
        }
        entries.append({"resource": res})

    for c in consults:
        diag_txt = (c["diagnostic_liber"] or "").strip() or (c["diagnostic_principal"] or "")
        res = {
            "resourceType": "Encounter",
            "id": str(c["id"]),
            "status": "finished",
            "class": {"code": "AMB"},
            "subject": {"reference": f"Patient/{c['pacient_id']}"},
            "period": {"start": c["data_consultului"] or None},
            "reasonCode": [{"text": diag_txt}],
        }
        entries.append({"resource": res})

    return {"resourceType": "Bundle", "type": "collection", "entry": entries}


def build_hl7_basic() -> str:
    """Construieste HL7 basic."""
    conn = get_conn()
    cur = conn.cursor()
    cur.execute("SELECT * FROM pacienti_master ORDER BY id ASC")
    patients = cur.fetchall()
    cur.execute("""
        SELECT c.* FROM consulturi c
        JOIN (
            SELECT pacient_id, MAX(id) AS max_id
            FROM consulturi
            GROUP BY pacient_id
        ) t ON t.pacient_id = c.pacient_id AND t.max_id = c.id
    """)
    last_consults = {r["pacient_id"]: r for r in cur.fetchall()}
    conn.close()

    lines: List[str] = []
    ts = datetime.now().strftime("%Y%m%d%H%M%S")
    for p in patients:
        pid = p["id"]
        name = (p["nume_prenume"] or "").replace("^", " ")
        cnp = p["cnp"] or ""
        sex = (p["sex"] or "")[:1].upper()
        dob = (p["data_nasterii"] or "").replace("-", "")
        msh = f"MSH|^~\\&|MBM|MBM|EXT|EXT|{ts}||ADT^A01|{pid}|P|2.5"
        pid_seg = f"PID|||{pid}||{name}||{dob}|{sex}|||{p['domiciliu'] or ''}||{p['telefon'] or ''}|||{cnp}"
        pv1 = "PV1||O"
        lines.extend([msh, pid_seg, pv1])
        lc = last_consults.get(pid)
        if lc:
            diag = (((lc["diagnostic_liber"] or "").strip() or (lc["diagnostic_principal"] or "")).replace("^", " "))
            dg1 = f"DG1|1||{diag}||{(lc['data_consultului'] or '').replace('-', '')}|F"
            lines.append(dg1)
        lines.append("")
    return "\n".join(lines)


# ============================================================
# UI: Tools
# ============================================================
class ToolsDialog(QDialog):
    def __init__(self, parent=None):
        """Initializeaza dialogul `ToolsDialog` si configureaza controalele interfetei."""
        super().__init__(parent)
        self.setWindowTitle("Instrumente")
        self.resize(780, 520)
        root = QVBoxLayout(self)

        self.btn_periodic = QPushButton("Raport Alerta")
        self.btn_adv_search = QPushButton("Cautare avansata")
        self.btn_stats = QPushButton("Statistici avansate")
        self.btn_kpi = QPushButton("KPI")
        self.btn_followup = QPushButton("Modul follow-up")
        self.btn_import_map = QPushButton("Import Excel/CSV (mapare)")
        self.btn_view_import_profile_current = QPushButton("Vezi maparea curenta")
        self.btn_export_import_profile_current = QPushButton("Export mapare curenta")
        self.btn_reset_import_profile_current = QPushButton("Reset mapare curenta")
        self.btn_reset_import_profiles = QPushButton("Reset mapari import")
        self.btn_restore = QPushButton("Restore DB")
        self.btn_log = QPushButton("Log activitate")
        self.btn_error_log = QPushButton("Log erori")
        self.btn_interop = QPushButton("Interoperabilitate")
        self.btn_inventory = QPushButton("Stocuri")
        self.btn_role = QPushButton("Rol/Permisiuni")
        self.btn_backup_secure = QPushButton("Backup securizat")
        self.btn_sync_cloud = QPushButton("Sync cloud")
        self.btn_sync_cloud_full = QPushButton("Full re-sync cloud")
        self.btn_sync_status = QPushButton("Status sync")
        self.btn_test_supabase = QPushButton("Test conexiune Supabase")
        self.btn_reminders = QPushButton("Remindere automate")
        self.btn_clinic = QPushButton("Setari clinica")
        self.btn_locations = QPushButton("Sedii")
        self.btn_nomenclatoare = QPushButton("Nomenclatoare")
        self.btn_appt = QPushButton("Programari")
        self.btn_wait = QPushButton("Lista asteptare")
        self.btn_tasks = QPushButton("Taskuri interne")
        self.btn_claims = QPushButton("Decontari")
        self.btn_lab_import = QPushButton("Import laborator")
        self.btn_dashboard = QPushButton("Dashboard")
        self.btn_labels = QPushButton("Etichete")
        self.btn_icd10 = QPushButton("Import ICD-10")
        self.btn_update_app = QPushButton("Update aplicatie")
        self.btn_db_cleanup = QPushButton("Curata baza de date")
        self.btn_recycle_bin = QPushButton("Recycle Bin (restaurare)")
        if ICD10_READONLY_LOCAL:
            self.btn_icd10.setText("Actualizeaza ICD-10")

        all_buttons = [
            self.btn_periodic, self.btn_adv_search, self.btn_stats, self.btn_kpi,
            self.btn_followup, self.btn_import_map, self.btn_view_import_profile_current,
            self.btn_export_import_profile_current, self.btn_reset_import_profile_current, self.btn_reset_import_profiles,
            self.btn_restore, self.btn_log,
            self.btn_error_log, self.btn_interop, self.btn_inventory, self.btn_role,
            self.btn_backup_secure, self.btn_sync_cloud, self.btn_sync_cloud_full, self.btn_sync_status, self.btn_test_supabase, self.btn_reminders,
            self.btn_clinic, self.btn_locations, self.btn_nomenclatoare, self.btn_appt, self.btn_wait,
            self.btn_tasks, self.btn_claims, self.btn_lab_import, self.btn_dashboard, self.btn_labels, self.btn_icd10,
            self.btn_update_app, self.btn_db_cleanup, self.btn_recycle_bin
        ]
        for b in all_buttons:
            b.setMinimumSize(170, 64)
            b.setIconSize(QSize(28, 28))

        sc = QScrollArea()
        sc.setWidgetResizable(True)
        sc_host = QWidget()
        sc_layout = QVBoxLayout(sc_host)
        sc_layout.setContentsMargins(0, 0, 0, 0)
        sc_layout.setSpacing(10)

        group_specs: List[Tuple[str, str, List[QPushButton]]] = [
            (
                "analysis",
                "Rapoarte si analiza",
                [
                    self.btn_periodic,
                    self.btn_adv_search,
                    self.btn_stats,
                    self.btn_kpi,
                    self.btn_dashboard,
                    self.btn_followup,
                ],
            ),
            (
                "import",
                "Import, coduri si etichete",
                [
                    self.btn_import_map,
                    self.btn_view_import_profile_current,
                    self.btn_export_import_profile_current,
                    self.btn_reset_import_profile_current,
                    self.btn_reset_import_profiles,
                    self.btn_nomenclatoare,
                    self.btn_icd10,
                    self.btn_lab_import,
                    self.btn_labels,
                ],
            ),
            (
                "ops",
                "Programari si operare",
                [
                    self.btn_appt,
                    self.btn_wait,
                    self.btn_tasks,
                    self.btn_claims,
                    self.btn_reminders,
                ],
            ),
            (
                "admin",
                "Administrare clinica",
                [
                    self.btn_clinic,
                    self.btn_locations,
                    self.btn_inventory,
                    self.btn_interop,
                    self.btn_role,
                ],
            ),
            (
                "sync",
                "Sync, backup si mentenanta",
                [
                    self.btn_sync_cloud,
                    self.btn_sync_cloud_full,
                    self.btn_sync_status,
                    self.btn_test_supabase,
                    self.btn_backup_secure,
                    self.btn_restore,
                    self.btn_update_app,
                    self.btn_db_cleanup,
                    self.btn_recycle_bin,
                ],
            ),
            (
                "logs",
                "Loguri si diagnostic",
                [
                    self.btn_log,
                    self.btn_error_log,
                ],
            ),
        ]

        self._tools_group_sections: Dict[str, Tuple[QPushButton, QWidget]] = {}
        group_header_icons: Dict[str, QStyle.StandardPixmap] = {
            "analysis": QStyle.StandardPixmap.SP_FileDialogInfoView,
            "import": QStyle.StandardPixmap.SP_DialogOpenButton,
            "ops": QStyle.StandardPixmap.SP_FileDialogStart,
            "admin": QStyle.StandardPixmap.SP_DirHomeIcon,
            "sync": QStyle.StandardPixmap.SP_BrowserReload,
            "logs": QStyle.StandardPixmap.SP_FileDialogDetailedView,
        }

        def _set_tools_group_visible(group_key: str, visible: bool):
            """Seteaza tools group visible in `ToolsDialog`, ca helper intern in `__init__`."""
            pair = self._tools_group_sections.get(group_key)
            if not pair:
                return
            header_btn, content_widget = pair
            content_widget.setVisible(visible)
            base = (
                (header_btn.text() or "")
                .replace(UI_TRIANGLE_EXPANDED, "")
                .replace(UI_TRIANGLE_COLLAPSED, "")
                .replace("â–ľ", "")
                .replace("â–¸", "")
                .strip()
            )
            header_btn.setText(f"{base} {UI_TRIANGLE_EXPANDED if visible else UI_TRIANGLE_COLLAPSED}")

        def _toggle_tools_group(group_key: str):
            """Comuta tools group in `ToolsDialog`, ca helper intern in `__init__`."""
            pair = self._tools_group_sections.get(group_key)
            if not pair:
                return
            _btn, content_widget = pair
            _set_tools_group_visible(group_key, not content_widget.isVisible())

        for key, title, btns in group_specs:
            header_btn = QPushButton(f"{title} {UI_TRIANGLE_COLLAPSED}")
            header_btn.setObjectName("secondary")
            header_btn.setMinimumHeight(44)
            header_btn.setIconSize(QSize(20, 20))
            sp = group_header_icons.get(key)
            if sp is not None:
                apply_std_icon(header_btn, sp)

            content = QWidget()
            gl = QGridLayout(content)
            gl.setContentsMargins(14, 6, 0, 8)
            gl.setHorizontalSpacing(10)
            gl.setVerticalSpacing(10)
            cols = 3
            for idx, btn in enumerate(btns):
                gl.addWidget(btn, idx // cols, idx % cols)

            sc_layout.addWidget(header_btn)
            sc_layout.addWidget(content)
            self._tools_group_sections[key] = (header_btn, content)
            header_btn.clicked.connect(lambda _checked=False, k=key: _toggle_tools_group(k))
            _set_tools_group_visible(key, False)

        sc_layout.addStretch(1)
        sc.setWidget(sc_host)
        root.addWidget(sc, 1)

        # Icons
        apply_std_icon(self.btn_periodic, QStyle.StandardPixmap.SP_FileDialogInfoView)
        apply_std_icon(self.btn_adv_search, QStyle.StandardPixmap.SP_FileDialogContentsView)
        apply_std_icon(self.btn_stats, QStyle.StandardPixmap.SP_FileDialogListView)
        apply_std_icon(self.btn_kpi, QStyle.StandardPixmap.SP_ArrowUp)
        apply_std_icon(self.btn_followup, QStyle.StandardPixmap.SP_ArrowRight)
        apply_std_icon(self.btn_import_map, QStyle.StandardPixmap.SP_DialogOpenButton)
        apply_std_icon(self.btn_view_import_profile_current, QStyle.StandardPixmap.SP_FileDialogDetailedView)
        apply_std_icon(self.btn_export_import_profile_current, QStyle.StandardPixmap.SP_DialogSaveButton)
        apply_std_icon(self.btn_reset_import_profile_current, QStyle.StandardPixmap.SP_DialogResetButton)
        apply_std_icon(self.btn_reset_import_profiles, QStyle.StandardPixmap.SP_DialogResetButton)
        apply_std_icon(self.btn_restore, QStyle.StandardPixmap.SP_BrowserReload)
        apply_std_icon(self.btn_log, QStyle.StandardPixmap.SP_FileDialogDetailedView)
        apply_std_icon(self.btn_error_log, QStyle.StandardPixmap.SP_MessageBoxCritical)
        apply_std_icon(self.btn_interop, QStyle.StandardPixmap.SP_DirLinkIcon)
        apply_std_icon(self.btn_inventory, QStyle.StandardPixmap.SP_DriveHDIcon)
        apply_std_icon(self.btn_role, QStyle.StandardPixmap.SP_DialogYesButton)
        apply_std_icon(self.btn_backup_secure, QStyle.StandardPixmap.SP_DialogSaveButton)
        apply_std_icon(self.btn_sync_cloud, QStyle.StandardPixmap.SP_BrowserReload)
        apply_std_icon(self.btn_sync_cloud_full, QStyle.StandardPixmap.SP_ArrowDown)
        apply_std_icon(self.btn_sync_status, QStyle.StandardPixmap.SP_FileDialogDetailedView)
        apply_std_icon(self.btn_test_supabase, QStyle.StandardPixmap.SP_DriveNetIcon)
        apply_std_icon(self.btn_reminders, QStyle.StandardPixmap.SP_MessageBoxInformation)
        apply_std_icon(self.btn_clinic, QStyle.StandardPixmap.SP_DirHomeIcon)
        apply_std_icon(self.btn_locations, QStyle.StandardPixmap.SP_DirIcon)
        apply_std_icon(self.btn_nomenclatoare, QStyle.StandardPixmap.SP_FileDialogListView)
        apply_std_icon(self.btn_appt, QStyle.StandardPixmap.SP_FileDialogStart)
        apply_std_icon(self.btn_wait, QStyle.StandardPixmap.SP_MessageBoxInformation)
        apply_std_icon(self.btn_tasks, QStyle.StandardPixmap.SP_ArrowUp)
        apply_std_icon(self.btn_claims, QStyle.StandardPixmap.SP_DialogApplyButton)
        apply_std_icon(self.btn_lab_import, QStyle.StandardPixmap.SP_FileDialogNewFolder)
        apply_std_icon(self.btn_dashboard, QStyle.StandardPixmap.SP_ComputerIcon)
        apply_std_icon(self.btn_labels, QStyle.StandardPixmap.SP_FileIcon)
        apply_std_icon(self.btn_update_app, QStyle.StandardPixmap.SP_BrowserReload)
        apply_std_icon(self.btn_db_cleanup, QStyle.StandardPixmap.SP_TrashIcon)
        apply_std_icon(self.btn_recycle_bin, QStyle.StandardPixmap.SP_DialogOpenButton)
        if ICD10_READONLY_LOCAL:
            apply_std_icon(self.btn_icd10, QStyle.StandardPixmap.SP_BrowserReload)
        else:
            apply_std_icon(self.btn_icd10, QStyle.StandardPixmap.SP_DialogOpenButton)

        # Handlers are set by parent (App)
# ============================================================
# UI: Main App
# ============================================================
class App(QWidget):
    def __init__(self):
        """Initializeaza interfata principala, setarile utilizator si legaturile dintre module."""
        super().__init__()
        self.setWindowTitle(f"MBM - Analytic {APP_VERSION_LABEL}")
        if APP_ICON is not None:
            self.setWindowIcon(APP_ICON)
        self.resize(1280, 760)
        self.setMinimumSize(1100, 700)

        self.current_id: Optional[int] = None  # selected master
        self._last_alert_signature: Optional[str] = None
        self._main_table_page_size_options = [100, 250, 500, 1000]
        try:
            page_size_saved = int(get_setting("main_table_page_size", "250") or 250)
        except Exception:
            page_size_saved = 250
        if page_size_saved <= 0:
            page_size_saved = 250
        if page_size_saved not in self._main_table_page_size_options:
            self._main_table_page_size_options.append(page_size_saved)
            self._main_table_page_size_options = sorted(set(self._main_table_page_size_options))
        self._main_table_page_size = int(page_size_saved)
        self._main_table_page_index = 0
        self._main_table_total_rows = 0
        self._main_table_total_pages = 1
        self._main_table_query_signature: Optional[str] = None

        # autosave flags
        self._dirty_since_last_backup = False
        self._last_daily_backup_date: Optional[date] = None
        self._last_backup_prune_date: Optional[date] = None

        # status
        self._last_status_backup = None
        self._last_status_export = None
        self._last_status_import = None
        self._last_status_dupcheck = None
        self._last_status_sync = None
        self._sync_in_progress = False
        self._reminder_job_in_progress = False
        self._autosave_in_progress = False
        self._autosave_pending = False
        self._autosave_pending_reason = ""
        self._icd10_sync_in_progress = False
        self._local_bootstrap_in_progress = False
        self._borderless_mode = False
        self._normal_window_geometry: Optional[QRect] = None
        self._page_windows: Dict[str, QDialog] = {}
        self._session_sensitive_timeout_min = _setting_int(
            SESSION_SENSITIVE_TIMEOUT_MIN_KEY,
            SESSION_SENSITIVE_TIMEOUT_MIN_DEFAULT,
            5,
            720,
        )
        self._session_last_auth_at = datetime.now()
        self._consult_draft_loading = False
        self._consult_draft_tracking_enabled = False
        self._consult_draft_last_raw = ""
        self.consult_draft_timer = QTimer(self)
        self.consult_draft_timer.setSingleShot(True)
        self.consult_draft_timer.setInterval(int(CONSULT_DRAFT_AUTOSAVE_MS))
        self.consult_draft_timer.timeout.connect(self._save_consult_draft_now)

        root = QVBoxLayout()
        root.setContentsMargins(12, 12, 12, 12)
        root.setSpacing(10)

        # Header bar
        header = QFrame()
        header.setObjectName("headerBar")
        header_layout = QHBoxLayout(header)
        header_layout.setContentsMargins(12, 8, 12, 8)
        header_layout.setSpacing(10)

        lbl_title = QLabel("MBM - Analytic")
        lbl_title.setObjectName("appTitle")
        lbl_subtitle = QLabel("Management pacienti")
        lbl_subtitle.setObjectName("appSubtitle")
        lbl_version = QLabel(f"Versiune: {APP_VERSION_LABEL}")
        lbl_version.setObjectName("muted")
        lbl_version.setToolTip(f"Build aplicatie: {APP_VERSION_LABEL}")
        lbl_db = QLabel(f"DB: {DB_PATH.name}")
        lbl_db.setObjectName("muted")
        lbl_db.setToolTip(str(DB_PATH))

        title_box = QVBoxLayout()
        title_box.setSpacing(2)
        title_box.addWidget(lbl_title)
        meta_row = QHBoxLayout()
        meta_row.setSpacing(8)
        meta_row.addWidget(lbl_subtitle)
        meta_row.addWidget(lbl_version)
        meta_row.addWidget(lbl_db)
        meta_row.addStretch(1)
        title_box.addLayout(meta_row)
        header_layout.addLayout(title_box)
        header_layout.addStretch(1)

        self.cb_location = QComboBox()
        self.cb_location.setMinimumWidth(200)
        loc_lbl = QLabel("Sediu:")
        loc_lbl.setObjectName("muted")
        loc_box = QHBoxLayout()
        loc_box.setSpacing(6)
        loc_box.addWidget(loc_lbl)
        loc_box.addWidget(self.cb_location)
        header_layout.addLayout(loc_box)
        self.cb_location.currentIndexChanged.connect(self._on_location_changed)
        self._reload_locations_combo()

        self.lbl_net = QLabel("Offline")
        self.lbl_sync = QLabel("Sync: idle")
        self.lbl_net.setObjectName("muted")
        self.lbl_sync.setObjectName("muted")
        status_box = QVBoxLayout()
        status_box.setSpacing(2)
        status_box.addWidget(self.lbl_net)
        status_box.addWidget(self.lbl_sync)
        header_layout.addLayout(status_box)
        self._set_online_label(False)
        self._set_sync_label("Sync: idle")

        self.btn_report = QPushButton("Raport Alerta")
        self.btn_report.setObjectName("secondary")
        self.btn_report.clicked.connect(self.open_periodic_report_dialog)
        apply_std_icon(self.btn_report, QStyle.StandardPixmap.SP_FileDialogInfoView)

        self.btn_data_ops = QPushButton(f"Date/DB {UI_TRIANGLE_EXPANDED}")
        self.btn_data_ops.setObjectName("secondary")
        apply_std_icon(self.btn_data_ops, QStyle.StandardPixmap.SP_FileDialogDetailedView)

        self.menu_data_ops = QMenu(self.btn_data_ops)
        self.btn_import_excel = QAction("Import Excel/CSV", self.menu_data_ops)
        self.btn_import_excel.triggered.connect(self.import_excel_ui)
        self.btn_export_csv = QAction("Export CSV", self.menu_data_ops)
        self.btn_export_csv.triggered.connect(self.export_csv_ui)
        self.btn_backup = QAction("Backup DB", self.menu_data_ops)
        self.btn_backup.triggered.connect(self.backup_db)
        self.menu_data_ops.addAction(self.btn_import_excel)
        self.menu_data_ops.addAction(self.btn_export_csv)
        self.menu_data_ops.addAction(self.btn_backup)
        self.btn_data_ops.setMenu(self.menu_data_ops)
        try:
            st = self.style()
            if st is not None:
                self.btn_import_excel.setIcon(st.standardIcon(QStyle.StandardPixmap.SP_DialogOpenButton))
                self.btn_export_csv.setIcon(st.standardIcon(QStyle.StandardPixmap.SP_DialogSaveButton))
                self.btn_backup.setIcon(st.standardIcon(QStyle.StandardPixmap.SP_DialogSaveButton))
        except Exception:
            pass

        self.btn_tools = QPushButton("Instrumente")
        self.btn_tools.setObjectName("secondary")
        self.btn_tools.clicked.connect(self.open_tools_dialog)
        apply_std_icon(self.btn_tools, QStyle.StandardPixmap.SP_FileDialogDetailedView)

        header_layout.addWidget(self.btn_report)
        header_layout.addWidget(self.btn_data_ops)
        header_layout.addWidget(self.btn_tools)
        root.addWidget(header)

        splitter = QSplitter(Qt.Orientation.Horizontal)
        root.addWidget(splitter, 1)
        self._splitter = splitter

        # ---------------- LEFT ----------------
        left = QWidget()
        left_layout = QVBoxLayout(left)
        left_layout.setContentsMargins(0, 0, 0, 0)
        left_layout.setSpacing(10)
        self._left_panel = left

        # Keep action/search sections fixed and scroll only the form fields.
        fields_scroll = QScrollArea()
        fields_scroll.setWidgetResizable(True)
        fields_scroll.setFrameShape(QFrame.Shape.NoFrame)
        fields_scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        fields_scroll.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
        self._left_fields_scroll = fields_scroll

        fields_host = QWidget()
        fields_layout = QVBoxLayout(fields_host)
        fields_layout.setContentsMargins(0, 0, 0, 0)
        fields_layout.setSpacing(10)
        fields_scroll.setWidget(fields_host)

        actions_box = QGroupBox("Actiuni")
        actions_root = QVBoxLayout(actions_box)
        actions_root.setContentsMargins(8, 8, 8, 8)
        actions_root.setSpacing(6)
        self._actions_layout = None
        self.btn_save = QPushButton("Salveaza consult (nou)")
        self.btn_save.setObjectName("primary")
        self.btn_save.clicked.connect(self.save_consult)
        apply_std_icon(self.btn_save, QStyle.StandardPixmap.SP_DialogSaveButton)

        self.btn_update_master = QPushButton("Update pacient")
        self.btn_update_master.setObjectName("primary")
        self.btn_update_master.clicked.connect(self.update_master_ui)
        apply_std_icon(self.btn_update_master, QStyle.StandardPixmap.SP_DialogApplyButton)

        self.btn_delete = QPushButton("Sterge pacient")
        self.btn_delete.setObjectName("danger")
        self.btn_delete.clicked.connect(self.delete_master_ui)
        apply_std_icon(self.btn_delete, QStyle.StandardPixmap.SP_TrashIcon)

        self.btn_clear = QPushButton("Curata formular")
        self.btn_clear.setObjectName("secondary")
        self.btn_clear.clicked.connect(self.clear_form)
        apply_std_icon(self.btn_clear, QStyle.StandardPixmap.SP_DialogResetButton)

        self.btn_refresh = QPushButton("Refresh lista")
        self.btn_refresh.setObjectName("secondary")
        self.btn_refresh.clicked.connect(self.load_table)
        apply_std_icon(self.btn_refresh, QStyle.StandardPixmap.SP_BrowserReload)

        self.btn_avg_age = QPushButton("Medie Public tinta")
        self.btn_avg_age.setObjectName("secondary")
        self.btn_avg_age.clicked.connect(self.show_avg_age_dialog)
        apply_std_icon(self.btn_avg_age, QStyle.StandardPixmap.SP_FileDialogInfoView)

        self.btn_menu_pacient = QPushButton(f"Pacient {UI_TRIANGLE_COLLAPSED}")
        self.btn_menu_pacient.setObjectName("secondary")
        self.btn_menu_pacient.setIcon(get_user_icon(16))
        self.btn_menu_consult = QPushButton(f"Consult {UI_TRIANGLE_COLLAPSED}")
        self.btn_menu_consult.setObjectName("secondary")
        self.btn_menu_consult.setIcon(get_calendar_icon(16))
        self.btn_menu_utilitare = QPushButton(f"Utilitare {UI_TRIANGLE_COLLAPSED}")
        self.btn_menu_utilitare.setObjectName("secondary")
        apply_std_icon(self.btn_menu_utilitare, QStyle.StandardPixmap.SP_FileDialogDetailedView)

        self.menu_pacient_widget = QWidget()
        menu_pacient_layout = QVBoxLayout(self.menu_pacient_widget)
        menu_pacient_layout.setContentsMargins(6, 2, 6, 6)
        menu_pacient_layout.setSpacing(6)
        menu_pacient_layout.addWidget(self.btn_update_master)
        menu_pacient_layout.addWidget(self.btn_delete)

        self.menu_consult_widget = QWidget()
        menu_consult_layout = QVBoxLayout(self.menu_consult_widget)
        menu_consult_layout.setContentsMargins(6, 2, 6, 6)
        menu_consult_layout.setSpacing(6)
        menu_consult_layout.addWidget(self.btn_save)
        menu_consult_layout.addWidget(self.btn_clear)

        self.menu_utilitare_widget = QWidget()
        menu_utilitare_layout = QVBoxLayout(self.menu_utilitare_widget)
        menu_utilitare_layout.setContentsMargins(6, 2, 6, 6)
        menu_utilitare_layout.setSpacing(6)
        menu_utilitare_layout.addWidget(self.btn_refresh)
        menu_utilitare_layout.addWidget(self.btn_avg_age)

        menus_grid = QGridLayout()
        menus_grid.setHorizontalSpacing(8)
        menus_grid.setVerticalSpacing(4)
        menus_grid.addWidget(self.btn_menu_pacient, 0, 0)
        menus_grid.addWidget(self.btn_menu_consult, 0, 1)
        menus_grid.addWidget(self.btn_menu_utilitare, 0, 2)
        menus_grid.addWidget(self.menu_pacient_widget, 1, 0)
        menus_grid.addWidget(self.menu_consult_widget, 1, 1)
        menus_grid.addWidget(self.menu_utilitare_widget, 1, 2)
        menus_grid.setColumnStretch(0, 1)
        menus_grid.setColumnStretch(1, 1)
        menus_grid.setColumnStretch(2, 1)
        actions_root.addLayout(menus_grid)

        self._actions_submenus: Dict[str, Tuple[QPushButton, QWidget]] = {
            "pacient": (self.btn_menu_pacient, self.menu_pacient_widget),
            "consult": (self.btn_menu_consult, self.menu_consult_widget),
            "utilitare": (self.btn_menu_utilitare, self.menu_utilitare_widget),
        }
        self.btn_menu_pacient.clicked.connect(lambda: self._toggle_action_submenu("pacient"))
        self.btn_menu_consult.clicked.connect(lambda: self._toggle_action_submenu("consult"))
        self.btn_menu_utilitare.clicked.connect(lambda: self._toggle_action_submenu("utilitare"))
        self._set_action_submenu_state("")
        left_layout.addWidget(actions_box)

        # Master form
        gb_master = QGroupBox("Date pacient")
        master_layout = QVBoxLayout(gb_master)
        master_layout.setSpacing(8)

        gb_master_identity = QGroupBox("Identitate")
        master_identity_form = QFormLayout(gb_master_identity)
        master_identity_form.setHorizontalSpacing(10)
        master_identity_form.setVerticalSpacing(8)

        gb_master_contact = QGroupBox("Contact")
        master_contact_form = QFormLayout(gb_master_contact)
        master_contact_form.setHorizontalSpacing(10)
        master_contact_form.setVerticalSpacing(8)

        master_layout.addWidget(gb_master_identity)
        master_layout.addWidget(gb_master_contact)

        master_contact_keys = {"domiciliu", "telefon", "email", "sms_opt_out"}
        self.master_inputs = {}
        for label, key in MASTER_FIELDS:
            target_form = master_contact_form if key in master_contact_keys else master_identity_form
            if key in DATE_KEYS:
                w = DatePicker("YYYY-MM-DD", show_today=False)
            elif key == "sms_opt_out":
                w = QComboBox()
                w.addItem("DA", 0)
                w.addItem("NU", 1)
            else:
                w = QLineEdit()
                if key in ("sex", "varsta"):
                    w.setReadOnly(True)
                    w.setPlaceholderText("Auto din CNP / data nasterii")
            self.master_inputs[key] = w
            if key == "domiciliu":
                row_widget = QWidget()
                row_layout = QHBoxLayout(row_widget)
                row_layout.setContentsMargins(0, 0, 0, 0)
                row_layout.setSpacing(6)
                btn_pick = QPushButton("Alege")
                btn_pick.setObjectName("secondary")
                btn_pick.clicked.connect(self.open_domiciliu_picker)
                apply_std_icon(btn_pick, QStyle.StandardPixmap.SP_DialogOpenButton)
                row_layout.addWidget(w, 1)
                row_layout.addWidget(btn_pick)
                target_form.addRow(label, row_widget)
            else:
                if key == "sms_opt_out":
                    target_form.addRow(label, wrap_selector_widget(w, self))
                else:
                    target_form.addRow(label, w)
        fields_layout.addWidget(gb_master)

        # Auto-fill din CNP + live validate
        try:
            self.master_inputs["cnp"].editingFinished.connect(self._autofill_from_cnp_on_finish)
            self.master_inputs["cnp"].textChanged.connect(self.on_cnp_changed_live)
            self.on_cnp_changed_live(self.master_inputs["cnp"].text())
        except Exception:
            pass

        # Consult form
        gb_consult = QGroupBox("Consult curent (se adauga in ISTORIC)")
        self.consult_inputs = {}
        consult_layout = QVBoxLayout(gb_consult)
        consult_layout.setSpacing(8)

        gb_consult_general = QGroupBox("Date consult")
        consult_general_form = QFormLayout(gb_consult_general)
        consult_general_form.setHorizontalSpacing(10)
        consult_general_form.setVerticalSpacing(8)

        gb_consult_diag = QGroupBox("Diagnostic si observatii")
        consult_diag_form = QFormLayout(gb_consult_diag)
        consult_diag_form.setHorizontalSpacing(10)
        consult_diag_form.setVerticalSpacing(8)

        gb_consult_followup = QGroupBox("Follow-up si fizioterapie")
        consult_followup_form = QFormLayout(gb_consult_followup)
        consult_followup_form.setHorizontalSpacing(10)
        consult_followup_form.setVerticalSpacing(8)

        consult_layout.addWidget(gb_consult_general)
        consult_layout.addWidget(gb_consult_diag)
        consult_layout.addWidget(gb_consult_followup)

        consult_general_keys = {"data_consultului", "medic"}
        consult_diag_keys = {"diagnostic_principal", "diagnostic_secundar", "diagnostic_liber", "observatii"}

        for label, key in CONSULT_FIELDS:
            if key in consult_general_keys:
                target_form = consult_general_form
            elif key in consult_diag_keys:
                target_form = consult_diag_form
            else:
                target_form = consult_followup_form
            row_widget: QWidget
            if key == "data_revenire_control":
                w = DateTimePicker("YYYY-MM-DD", show_today=False)
                row_widget = w
            elif key in DATE_KEYS:
                w = DatePicker("YYYY-MM-DD", show_today=(key == "data_consultului"))
                row_widget = w

            elif key == "medic":
                w = QComboBox()
                w.addItem("")
                for medic_name in get_medic_dropdown_values():
                    w.addItem(medic_name)
                row_widget = wrap_selector_widget(w, self)

            elif key == "status_follow_up":
                w = QComboBox()
                w.addItems(["", "Programat", "Neprogramat"])
                row_widget = wrap_selector_widget(w, self)

            elif key in CONSULT_NOMENCLATOR_KEYS:
                w = QComboBox()
                w.addItem("")
                for val in get_nomenclator_values_by_key(key):
                    w.addItem(val)
                row_widget = wrap_selector_widget(w, self)

            elif key in CONSULT_BOOL_KEYS:
                w = QComboBox()
                w.addItems(["", "DA", "NU"])
                row_widget = wrap_selector_widget(w, self)

            elif key == "interval_luni_revenire":
                w = QSpinBox()
                w.setRange(0, 120)
                w.setSpecialValueText("")
                w.setToolTip("Interval in luni (0 = gol)")
                row_widget = wrap_selector_widget(w, self)

            elif key in TEXTAREA_KEYS:
                w = QTextEdit()
                w.setFixedHeight(70)
                row_widget = w

            else:
                w = QLineEdit()
                if key == "diagnostic_principal":
                    apply_icd10_completer(w, multi=False)
                elif key == "diagnostic_secundar":
                    apply_icd10_completer(w, multi=True)
                row_widget = w

            self.consult_inputs[key] = w
            target_form.addRow(label, row_widget)

        fields_layout.addWidget(gb_consult)
        self._bind_consult_draft_signals()

        search_box = QGroupBox("Cautare")
        search_line = QHBoxLayout(search_box)
        search_line.setSpacing(8)
        self.search = QLineEdit()
        self.search.setPlaceholderText("Cauta: nume / CNP / telefon ...")
        self.btn_search = QPushButton("Cauta")
        self.btn_search.setObjectName("primary")
        self.btn_search.clicked.connect(self.load_table)
        apply_std_icon(self.btn_search, QStyle.StandardPixmap.SP_FileDialogContentsView)
        self.btn_search_adv = QPushButton("Avansat")
        self.btn_search_adv.setObjectName("secondary")
        self.btn_search_adv.clicked.connect(self.open_advanced_search_dialog)
        apply_std_icon(self.btn_search_adv, QStyle.StandardPixmap.SP_DialogHelpButton)
        search_line.addWidget(self.search)
        search_line.addWidget(self.btn_search)
        search_line.addWidget(self.btn_search_adv)
        fields_layout.addStretch(1)
        left_layout.addWidget(fields_scroll, 1)
        left_layout.addWidget(search_box)
        self._init_search_completer()
        self._init_domiciliu_autocomplete()
        self._search_timer = QTimer(self)
        self._search_timer.setSingleShot(True)
        self._search_timer.setInterval(250)
        self._search_timer.timeout.connect(self._run_search_timer)
        self._last_search_text = ""
        self.search.textChanged.connect(self._queue_search_timer)

        splitter.addWidget(left)

        # ---------------- RIGHT ----------------
        right = QWidget()
        right_layout = QVBoxLayout(right)
        right_layout.setContentsMargins(0, 0, 0, 0)
        right_layout.setSpacing(10)

        summary_box = QGroupBox("Rezumat pacient")
        summary = QGridLayout(summary_box)
        summary.setHorizontalSpacing(12)
        summary.setVerticalSpacing(6)

        self.lbl_sum_name = QLabel("-")
        self.lbl_sum_cnp = QLabel("-")
        self.lbl_sum_phone = QLabel("-")
        self.lbl_sum_email = QLabel("-")
        self.lbl_sum_last = QLabel("-")
        self.lbl_sum_next = QLabel("-")

        lbl_name = QLabel("Nume:")
        lbl_cnp = QLabel("CNP:")
        lbl_phone = QLabel("Telefon:")
        lbl_email = QLabel("Email:")
        lbl_last = QLabel("Ultim consult:")
        lbl_next = QLabel("Control:")
        for lbl in (lbl_name, lbl_cnp, lbl_phone, lbl_email, lbl_last, lbl_next):
            lbl.setObjectName("muted")

        summary.addWidget(lbl_name, 0, 0)
        summary.addWidget(self.lbl_sum_name, 0, 1)
        summary.addWidget(lbl_cnp, 1, 0)
        summary.addWidget(self.lbl_sum_cnp, 1, 1)
        summary.addWidget(lbl_phone, 2, 0)
        summary.addWidget(self.lbl_sum_phone, 2, 1)
        summary.addWidget(lbl_email, 3, 0)
        summary.addWidget(self.lbl_sum_email, 3, 1)
        summary.addWidget(lbl_last, 0, 2)
        summary.addWidget(self.lbl_sum_last, 0, 3)
        summary.addWidget(lbl_next, 1, 2)
        summary.addWidget(self.lbl_sum_next, 1, 3)
        summary.setColumnStretch(1, 1)
        summary.setColumnStretch(3, 1)

        right_layout.addWidget(summary_box)

        self.table = QTableWidget(0, len(TABLE_COLS))
        self.table.setWordWrap(False)
        self.table.setAlternatingRowColors(True)
        self.table.setTextElideMode(Qt.TextElideMode.ElideRight)
        try:
            self.table.setHorizontalScrollMode(QAbstractItemView.ScrollMode.ScrollPerPixel)
            self.table.setVerticalScrollMode(QAbstractItemView.ScrollMode.ScrollPerPixel)
        except Exception:
            pass
        self.table.setHorizontalHeaderLabels([
            "ALERTA", "ID", "Nume", "CNP", "Sex", "Telefon", "Email", "Data nasterii", "Varsta",
            "Domiciliu", "Ultimul consult", "Ultim diagnostic", "Control", "Status"
        ])
        self.table.setColumnHidden(1, True)
        self.table.setItemDelegate(RowOutlineDelegate(self.table))
        self.table.setSortingEnabled(True)

        # Click / Double click
        self.table.cellClicked.connect(self.select_row)
        self.table.cellDoubleClicked.connect(self.open_patient_page_on_doubleclick)

        right_layout.addWidget(self.table)

        table_pager = QHBoxLayout()
        table_pager.setSpacing(8)
        self.btn_main_prev_page = QPushButton("Pagina anterioara")
        self.btn_main_next_page = QPushButton("Pagina urmatoare")
        self.cb_main_page_size = QComboBox()
        for sz in self._main_table_page_size_options:
            self.cb_main_page_size.addItem(f"{sz}/pagina", int(sz))
        idx_sz = self.cb_main_page_size.findData(int(self._main_table_page_size))
        self.cb_main_page_size.setCurrentIndex(idx_sz if idx_sz >= 0 else 0)
        self.lbl_main_page_info = QLabel("")
        self.lbl_main_page_info.setObjectName("muted")
        apply_std_icon(self.btn_main_prev_page, QStyle.StandardPixmap.SP_ArrowBack)
        apply_std_icon(self.btn_main_next_page, QStyle.StandardPixmap.SP_ArrowForward)
        self.btn_main_prev_page.clicked.connect(self._go_main_prev_page)
        self.btn_main_next_page.clicked.connect(self._go_main_next_page)
        self.cb_main_page_size.currentIndexChanged.connect(self._on_main_page_size_changed)
        table_pager.addWidget(self.btn_main_prev_page)
        table_pager.addWidget(self.btn_main_next_page)
        table_pager.addWidget(QLabel("Randuri/pagina:"))
        table_pager.addWidget(wrap_selector_widget(self.cb_main_page_size, self), 0)
        table_pager.addStretch(1)
        table_pager.addWidget(self.lbl_main_page_info, 0, Qt.AlignmentFlag.AlignRight)
        right_layout.addLayout(table_pager)

        # tabel NU editabil
        self.table.setEditTriggers(QAbstractItemView.EditTrigger.NoEditTriggers)
        self.table.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
        self.table.setSelectionMode(QAbstractItemView.SelectionMode.SingleSelection)

        # auto-dimensionare col
        h = self.table.horizontalHeader()
        h.setSectionResizeMode(QHeaderView.ResizeMode.ResizeToContents)
        h.setSectionsMovable(False)
        h.setHighlightSections(False)
        h.setStretchLastSection(True)
        self.table.verticalHeader().setDefaultSectionSize(22)
        self.table.verticalHeader().setSectionResizeMode(QHeaderView.ResizeMode.Fixed)
        self._table_layout_loaded = False
        self._table_layout_key = f"table_layout_main::{get_current_user()}"
        self._table_layout_timer = QTimer(self)
        self._table_layout_timer.setSingleShot(True)
        self._table_layout_timer.setInterval(500)
        self._table_layout_timer.timeout.connect(self._save_table_layout)
        h.sectionResized.connect(lambda *_: self._schedule_save_table_layout())
        QTimer.singleShot(0, self._load_table_layout)

        # row style cache
        self._row_bg_yellow = QBrush(QColor(255, 249, 196))
        self._row_bg_red = QBrush(QColor(255, 205, 210))
        self._row_bold_font = QFont()
        self._row_bold_font.setBold(True)

        splitter.addWidget(right)
        splitter.setChildrenCollapsible(False)
        splitter.setStretchFactor(0, 0)
        splitter.setStretchFactor(1, 1)
        self._right_panel = right
        self._splitter_initialized = False
        self._left_fixed_width = None
        self._force_left_panel_max_once = True
        QTimer.singleShot(0, self._force_lock_left_panel_width)
        QTimer.singleShot(0, self._relayout_actions_buttons)

        # bottom area grouped: status + quality + logout
        bottom_groups = QHBoxLayout()
        bottom_groups.setSpacing(8)

        status_group = QGroupBox("Status")
        status_layout = QHBoxLayout(status_group)
        self.lbl_status = QLabel("Ready")
        self.lbl_status.setStyleSheet("color: #4b4f56;")
        status_layout.addWidget(self.lbl_status)
        bottom_groups.addWidget(status_group, 1)

        self.btn_quality = QPushButton("Calitate Date")
        self.btn_quality.setObjectName("secondary")
        self.btn_quality.setMinimumWidth(220)
        apply_std_icon(self.btn_quality, QStyle.StandardPixmap.SP_MessageBoxWarning)
        self.menu_quality = QMenu(self.btn_quality)

        self.btn_check_dups = QAction("Verificare Duplicat", self.menu_quality)
        self.btn_check_dups.setToolTip("Cauta pacienti duplicat (CNP / nume identic / nume similar)")
        self.btn_check_dups.triggered.connect(self.run_duplicate_check_ui)

        self.btn_recalc_ages = QAction("Recalculeaza varstele", self.menu_quality)
        self.btn_recalc_ages.setToolTip("Recalculeaza varsta + sex din CNP pentru toti pacientii")
        self.btn_recalc_ages.triggered.connect(self.recalc_ages_ui)

        self.menu_quality.addAction(self.btn_check_dups)
        self.menu_quality.addAction(self.btn_recalc_ages)
        self.btn_quality.setMenu(self.menu_quality)
        try:
            st = self.style()
            if st is not None:
                self.btn_check_dups.setIcon(st.standardIcon(QStyle.StandardPixmap.SP_MessageBoxWarning))
                self.btn_recalc_ages.setIcon(st.standardIcon(QStyle.StandardPixmap.SP_BrowserReload))
        except Exception:
            pass

        bottom_groups.addWidget(self.btn_quality)

        self.btn_logout = QPushButton("Deconectare")
        self.btn_logout.setObjectName("secondary")
        apply_std_icon(self.btn_logout, QStyle.StandardPixmap.SP_DialogCloseButton)
        self.btn_logout.clicked.connect(self.logout)
        bottom_groups.addWidget(self.btn_logout)

        right_layout.addLayout(bottom_groups)

        # transient status system
        self._status_transient_msg: Optional[str] = None
        self._status_transient_until: Optional[datetime] = None
        self._status_transient_timer = QTimer(self)
        self._status_transient_timer.setInterval(1000)
        self._status_transient_timer.timeout.connect(self._refresh_status_bar)
        self._status_transient_timer.start()

        # Online indicator
        self._online_state = None
        self._online_timer = QTimer(self)
        self._online_timer.setInterval(30000)
        self._online_timer.timeout.connect(self._check_online_async)
        self._online_timer.start()
        QTimer.singleShot(0, self._check_online_async)

        self.setLayout(root)
        self._install_main_shortcuts()
        self.apply_role_permissions()
        self.load_table(auto_select_first=False)
        self._set_status_text()
        self._consult_draft_tracking_enabled = True
        QTimer.singleShot(350, self._restore_consult_draft_if_any)

        # ALERTA la pornire
        QTimer.singleShot(0, self.maybe_show_control_alert)

        # ALERTA periodic (60 min)
        self.control_timer = QTimer(self)
        self.control_timer.setInterval(60 * 60 * 1000)
        self.control_timer.timeout.connect(self.maybe_show_control_alert)
        self.control_timer.start()

        # AUTOSAVE periodic (5 min)
        self.autosave_timer = QTimer(self)
        self.autosave_timer.setInterval(AUTOSAVE_EVERY_SECONDS * 1000)
        self.autosave_timer.timeout.connect(self.maybe_autosave_backup)
        self.autosave_timer.start()

        # Debounce backup
        self.debounce_timer = QTimer(self)
        self.debounce_timer.setSingleShot(True)
        self.debounce_timer.setInterval(AUTOSAVE_DEBOUNCE_SECONDS * 1000)
        self.debounce_timer.timeout.connect(self.autosave_backup_now)

        # Auto sync (near real-time)
        if SYNC_INTERVAL_MIN and SYNC_INTERVAL_MIN > 0:
            self.sync_timer = QTimer(self)
            self.sync_timer.setInterval(int(SYNC_INTERVAL_MIN * 60 * 1000))
            self.sync_timer.timeout.connect(self.sync_cloud_silent)
            self.sync_timer.start()
            # Evita competitie pe UI imediat dupa login/startup.
            QTimer.singleShot(8000, self.sync_cloud_silent)

        # Auto maintenance (startup + periodic): local bootstrap + source sync
        self.maintenance_timer = QTimer(self)
        self.maintenance_timer.setInterval(int(max(30, int(AUTO_MAINTENANCE_INTERVAL_MIN)) * 60 * 1000))
        self.maintenance_timer.timeout.connect(self._periodic_maintenance_tick)
        self.maintenance_timer.start()
        QTimer.singleShot(3500, self._periodic_maintenance_tick)

        # Reminders auto (local, while app is running)
        self.reminder_timer = QTimer(self)
        self.reminder_timer.setInterval(int(max(5, _get_reminder_run_interval_min()) * 60 * 1000))
        self.reminder_timer.timeout.connect(self.check_auto_reminders)
        self.reminder_timer.start()

        # Auto update check (admin, once/day)
        QTimer.singleShot(12000, self._auto_check_updates)
        force_ascii_ui_texts(self)
        self.btn_data_ops.setText(f"Date/DB {UI_TRIANGLE_EXPANDED}")
        self._set_action_submenu_state("")
    # ---------------- transient status ----------------
    def _set_transient_status(self, msg: Optional[str], seconds: int = 3):
        """Seteaza transient status in `App`."""
        if not msg:
            self._status_transient_msg = None
            self._status_transient_until = None
            self._set_status_text()
            return
        self._status_transient_msg = str(msg)
        self._status_transient_until = datetime.now() + timedelta(seconds=max(1, int(seconds)))
        self._refresh_status_bar()

    def _refresh_status_bar(self):
        """Gestioneaza status bar in `App`."""
        if self._status_transient_msg and self._status_transient_until:
            if datetime.now() <= self._status_transient_until:
                self._set_status_text()
                base = self.lbl_status.text()
                self.lbl_status.setText(
                    f"{self._status_transient_msg}   |   {base}" if base else self._status_transient_msg
                )
                return
            else:
                self._status_transient_msg = None
                self._status_transient_until = None
                # Restauram textul de status o singura data la expirarea mesajului tranzitoriu.
                self._set_status_text()

    def _reset_sensitive_session_auth(self):
        """Gestioneaza sensitive session auth in `App`."""
        self._session_last_auth_at = datetime.now()

    def _requires_sensitive_reauth(self) -> bool:
        """Gestioneaza sensitive reauth in `App`."""
        timeout_min = max(1, int(getattr(self, "_session_sensitive_timeout_min", SESSION_SENSITIVE_TIMEOUT_MIN_DEFAULT)))
        last_auth = getattr(self, "_session_last_auth_at", None)
        if not isinstance(last_auth, datetime):
            return True
        return datetime.now() - last_auth >= timedelta(minutes=timeout_min)

    def _require_sensitive_reauth(self, action_label: str) -> bool:
        """Gestioneaza sensitive reauth in `App`."""
        if not self._requires_sensitive_reauth():
            return True
        user = (get_current_user() or DEFAULT_USER).strip() or DEFAULT_USER
        pwd, ok = QInputDialog.getText(
            self,
            "Reautentificare necesara",
            (
                f"Sesiunea pentru actiuni sensibile a expirat ({self._session_sensitive_timeout_min} minute).\n"
                f"Introdu parola pentru utilizatorul '{user}' ca sa continui: {action_label}"
            ),
            QLineEdit.EchoMode.Password,
        )
        if not ok:
            return False
        row = validate_login(user, (pwd or "").strip())
        if not row:
            try:
                log_action("session_reauth_failed", f"user={user}; action={action_label}")
            except Exception:
                pass
            QMessageBox.warning(self, "Reautentificare", "Parola invalida.")
            return False
        self._reset_sensitive_session_auth()
        try:
            log_action("session_reauth_ok", f"user={user}; action={action_label}")
        except Exception:
            pass
        self._set_transient_status("Reautentificare efectuata.", seconds=3)
        return True

    def _maybe_sync_icd10_startup(self):
        """Decide daca ruleaza sync ICD10 startup in `App`."""
        if not SUPABASE_URL or not SUPABASE_ANON_KEY:
            return
        if self._icd10_sync_in_progress:
            return
        self._icd10_sync_in_progress = True

        worker = Worker(sync_icd10_from_supabase, False)
        thread = QThread(self)
        worker.moveToThread(thread)

        def cleanup():
            """Curata resursele temporare folosite de operatia curenta (helper intern pentru `_maybe_sync_icd10_startup`)."""
            try:
                thread.quit()
                thread.wait()
            except Exception:
                pass
            self._icd10_sync_in_progress = False

        def on_finished(cnt):
            """Gestioneaza evenimentul finished in `App`, ca helper intern in `_maybe_sync_icd10_startup`."""
            cleanup()
            if int(cnt or 0) > 0:
                self._set_transient_status(f"ICD-10 actualizat ({cnt} coduri).", seconds=4)

        def on_error(msg):
            """Gestioneaza evenimentul error in `App`, ca helper intern in `_maybe_sync_icd10_startup`."""
            cleanup()
            self._set_transient_status(f"Actualizare ICD-10 esuata: {msg}", seconds=6)

        def on_cancelled():
            """Gestioneaza evenimentul cancelled in `App`, ca helper intern in `_maybe_sync_icd10_startup`."""
            cleanup()

        worker.finished.connect(on_finished)
        worker.error.connect(on_error)
        worker.cancelled.connect(on_cancelled)
        thread.started.connect(worker.run)
        thread.start()

    def _local_bootstrap_job(self) -> Dict[str, Any]:
        """Gestioneaza bootstrap job in `App`."""
        result: Dict[str, Any] = {
            "icd10_initialized": False,
            "icd10_bundle_copied": False,
            "localities_count": 0,
        }
        ensure_icd10_loaded()
        result["icd10_initialized"] = True
        try:
            global ICD10_BUNDLE_COPIED
            if ICD10_BUNDLE_COPIED:
                result["icd10_bundle_copied"] = True
                ICD10_BUNDLE_COPIED = False
        except Exception:
            pass
        try:
            result["localities_count"] = int(
                ensure_ro_localities_dataset(force_refresh=False, allow_fallback=True)
            )
        except Exception:
            result["localities_count"] = 0
        return result

    def _run_local_bootstrap_silent(self):
        """Ruleaza local bootstrap silent in `App`."""
        if self._local_bootstrap_in_progress:
            return
        self._local_bootstrap_in_progress = True

        worker = Worker(self._local_bootstrap_job)
        thread = QThread(self)
        worker.moveToThread(thread)

        def cleanup():
            """Curata resursele temporare folosite de operatia curenta (helper intern pentru `_run_local_bootstrap_silent`)."""
            try:
                thread.quit()
                thread.wait()
            except Exception:
                pass
            self._local_bootstrap_in_progress = False

        def on_finished(res):
            """Gestioneaza evenimentul finished in `App`, ca helper intern in `_run_local_bootstrap_silent`."""
            cleanup()
            try:
                payload = dict(res or {})
            except Exception:
                payload = {}
            if payload.get("icd10_bundle_copied"):
                self._set_transient_status("Resurse locale initializate (ICD-10).", seconds=4)

        def on_error(_msg):
            """Gestioneaza evenimentul error in `App`, ca helper intern in `_run_local_bootstrap_silent`."""
            cleanup()

        def on_cancelled():
            """Gestioneaza evenimentul cancelled in `App`, ca helper intern in `_run_local_bootstrap_silent`."""
            cleanup()

        worker.finished.connect(on_finished)
        worker.error.connect(on_error)
        worker.cancelled.connect(on_cancelled)
        thread.started.connect(worker.run)
        thread.start()

    def _periodic_maintenance_tick(self):
        """Gestioneaza maintenance tick in `App`."""
        # Nu porni mentenanta daca ruleaza deja un job greu in fundal.
        if self._sync_in_progress or self._reminder_job_in_progress or getattr(self, "_update_check_in_progress", False):
            return
        self._run_local_bootstrap_silent()
        if ICD10_READONLY_LOCAL and ICD10_SUPABASE_ENABLED:
            self._maybe_sync_icd10_startup()

    def _lock_left_panel_width(self):
        """Gestioneaza left panel width in `App`."""
        try:
            left = getattr(self, "_left_panel", None)
            right = getattr(self, "_right_panel", None)
            splitter = getattr(self, "_splitter", None)
            if left is None or right is None or splitter is None:
                return
            total = splitter.size().width()
            if total <= 0:
                return

            base_left_min = max(420, left.minimumSizeHint().width())
            # Tabelul din dreapta poate raporta un minimumSizeHint foarte mare
            # si comprima inutil zona de campuri la pornire. Limitam minimul util.
            right_hint = max(0, int(right.minimumSizeHint().width() or 0))
            base_right_min = max(520, min(680, right_hint if right_hint > 0 else 520))

            if total < (base_left_min + base_right_min):
                left_min = max(300, int(total * 0.35))
                right_min = max(320, int(total * 0.45))
            else:
                left_min = base_left_min
                right_min = base_right_min

            left.setMinimumWidth(int(left_min))
            left.setMaximumWidth(16777215)
            right.setMinimumWidth(int(right_min))

            max_left_allowed = max(int(left_min), total - int(right_min))
            # Implicit la pornire: splitter 50/50 (cat permite layout-ul minim).
            target_left = max(int(left_min), min(int(total * 0.5), max_left_allowed))

            sizes = splitter.sizes()
            current_left = sizes[0] if sizes and len(sizes) > 0 else target_left
            current_left = max(int(left_min), min(int(current_left), max_left_allowed))

            force_max = bool(getattr(self, "_force_left_panel_max_once", False))
            if not getattr(self, "_splitter_initialized", False) or force_max:
                splitter.setSizes([target_left, max(1, total - target_left)])
                self._splitter_initialized = True
                if force_max:
                    self._force_left_panel_max_once = False
            elif current_left != (sizes[0] if sizes and len(sizes) > 0 else -1):
                splitter.setSizes([current_left, max(1, total - current_left)])
        except Exception:
            pass

    def _force_lock_left_panel_width(self):
        """Gestioneaza lock left panel width in `App`."""
        try:
            self._force_left_panel_max_once = True
        except Exception:
            pass
        self._lock_left_panel_width()

    def _relayout_actions_buttons(self):
        """Gestioneaza actions buttons in `App`."""
        if getattr(self, "_actions_layout", None) is None:
            return
        try:
            layout = getattr(self, "_actions_layout", None)
            groups = getattr(self, "_actions_groups", None)
            left = getattr(self, "_left_panel", None)
            if layout is None or not groups or left is None:
                return

            for idx in reversed(range(layout.count())):
                item = layout.itemAt(idx)
                widget = item.widget() if item is not None else None
                if widget is not None:
                    layout.removeWidget(widget)

            panel_width = max(left.width(), left.minimumWidth())
            wide = panel_width >= 900

            if wide:
                for col, grp in enumerate(groups):
                    layout.addWidget(grp, 0, col)
                for col in range(len(groups)):
                    layout.setColumnStretch(col, 1)
            else:
                layout.addWidget(groups[0], 0, 0)
                layout.addWidget(groups[1], 0, 1)
                layout.addWidget(groups[2], 1, 0, 1, 2)
                layout.setColumnStretch(0, 1)
                layout.setColumnStretch(1, 1)
        except Exception:
            pass

    def _set_action_submenu_state(self, active_key: str):
        """Seteaza action submenu state in `App`."""
        try:
            menus = getattr(self, "_actions_submenus", {})
            for key, pair in menus.items():
                btn, panel = pair
                opened = key == active_key
                panel.setVisible(opened)
                label = (
                    (btn.text() or "")
                    .replace(UI_TRIANGLE_EXPANDED, "")
                    .replace(UI_TRIANGLE_COLLAPSED, "")
                    .replace("â–ľ", "")
                    .replace("â–¸", "")
                    .strip()
                )
                btn.setText(f"{label} {UI_TRIANGLE_EXPANDED if opened else UI_TRIANGLE_COLLAPSED}")
        except Exception:
            pass

    def _toggle_action_submenu(self, key: str):
        """Comuta action submenu in `App`."""
        try:
            menus = getattr(self, "_actions_submenus", {})
            pair = menus.get(key)
            if not pair:
                return
            btn, panel = pair
            opened = not panel.isVisible()
            panel.setVisible(opened)
            label = (
                (btn.text() or "")
                .replace(UI_TRIANGLE_EXPANDED, "")
                .replace(UI_TRIANGLE_COLLAPSED, "")
                .replace("â–ľ", "")
                .replace("â–¸", "")
                .strip()
            )
            btn.setText(f"{label} {UI_TRIANGLE_EXPANDED if opened else UI_TRIANGLE_COLLAPSED}")
        except Exception:
            pass

    def resizeEvent(self, event):
        """Gestioneaza redimensionarea ferestrei principale si recalculul layout-ului."""
        super().resizeEvent(event)
        try:
            self._lock_left_panel_width()
            self._relayout_actions_buttons()
        except Exception:
            pass

    def enter_borderless_workarea(self):
        """Gestioneaza borderless workarea in `App`."""
        try:
            if not self._borderless_mode:
                self._normal_window_geometry = self.geometry()
        except Exception:
            pass
        self.setWindowFlag(Qt.WindowType.FramelessWindowHint, True)
        screen = self.screen() or QApplication.primaryScreen()
        if screen is not None:
            self.setGeometry(screen.availableGeometry())
        self._borderless_mode = True
        self.show()

    def enter_normal_window(self):
        """Gestioneaza normal window in `App`."""
        self.setWindowFlag(Qt.WindowType.FramelessWindowHint, False)
        self._borderless_mode = False
        self.showNormal()
        try:
            if self._normal_window_geometry is not None and self._normal_window_geometry.isValid():
                self.setGeometry(self._normal_window_geometry)
            else:
                self.resize(1280, 760)
        except Exception:
            self.resize(1280, 760)

    def toggle_window_mode(self):
        """Comuta window mode in `App`."""
        if self._borderless_mode:
            self.enter_normal_window()
        else:
            self.enter_borderless_workarea()

    def _save_window_placement_settings(self):
        """Salveaza window placement settings in `App`."""
        try:
            if self._borderless_mode:
                state = "maximized"
            elif self.isMaximized():
                state = "maximized"
            else:
                state = "normal"

            geom = self.normalGeometry() if self.isMaximized() else self.geometry()
            geom_txt = ""
            if geom is not None and geom.isValid():
                geom_txt = f"{geom.x()},{geom.y()},{geom.width()},{geom.height()}"

            set_setting("ui_main_window_state", state)
            set_setting("ui_main_window_geometry", geom_txt)
        except Exception:
            pass

    def show_with_saved_window_placement(self):
        """Afiseaza with saved window placement in `App`."""
        state = (get_setting("ui_main_window_state", "maximized") or "maximized").strip().lower()
        raw_geom = (get_setting("ui_main_window_geometry", "") or "").strip()

        if state == "normal":
            restored = False
            if raw_geom:
                try:
                    parts = [int(p.strip()) for p in raw_geom.split(",")]
                    if len(parts) == 4 and parts[2] > 0 and parts[3] > 0:
                        self.setGeometry(QRect(parts[0], parts[1], parts[2], parts[3]))
                        restored = True
                except Exception:
                    restored = False
            if not restored:
                self.resize(1280, 760)
            self.showNormal()
            try:
                QTimer.singleShot(0, self._force_lock_left_panel_width)
                QTimer.singleShot(120, self._force_lock_left_panel_width)
                QTimer.singleShot(320, self._force_lock_left_panel_width)
            except Exception:
                pass
            return

        self.showMaximized()
        try:
            QTimer.singleShot(0, self._force_lock_left_panel_width)
            QTimer.singleShot(120, self._force_lock_left_panel_width)
            QTimer.singleShot(320, self._force_lock_left_panel_width)
        except Exception:
            pass

    def _activate_if_enabled(self, btn: Optional[QPushButton]):
        """Gestioneaza if enabled in `App`."""
        if btn is None:
            return
        try:
            if btn.isEnabled():
                btn.click()
        except Exception:
            pass

    def _focus_main_search(self):
        """Gestioneaza main search in `App`."""
        try:
            self.search.setFocus()
            self.search.selectAll()
        except Exception:
            pass

    def _install_main_shortcuts(self):
        """Gestioneaza main shortcuts in `App`."""
        self._main_shortcuts: List[QShortcut] = []

        def add(seq: str, handler):
            """Adauga elementul curent in colectia gestionata de helper (helper intern pentru `_install_main_shortcuts`)."""
            sc = QShortcut(QKeySequence(seq), self)
            sc.setContext(Qt.ShortcutContext.WindowShortcut)
            sc.activated.connect(handler)
            self._main_shortcuts.append(sc)

        add("Ctrl+S", lambda: self._activate_if_enabled(self.btn_save))
        add("Ctrl+Return", lambda: self._activate_if_enabled(self.btn_save))
        add("Ctrl+U", lambda: self._activate_if_enabled(self.btn_update_master))
        add("Ctrl+L", lambda: self._activate_if_enabled(self.btn_clear))
        add("F5", lambda: self._activate_if_enabled(self.btn_refresh))
        add("Ctrl+F", self._focus_main_search)
        add("Ctrl+Shift+F", lambda: self._activate_if_enabled(self.btn_search_adv))
        add("Ctrl+T", lambda: self._activate_if_enabled(self.btn_tools))
        add("Ctrl+Alt+A", self.open_appointments_dialog)
        add("Ctrl+Alt+M", self.open_reminders_dialog)

        append_shortcut_hint(self.btn_save, "Ctrl+S / Ctrl+Enter")
        append_shortcut_hint(self.btn_update_master, "Ctrl+U")
        append_shortcut_hint(self.btn_clear, "Ctrl+L")
        append_shortcut_hint(self.btn_refresh, "F5")
        append_shortcut_hint(self.search, "Ctrl+F")
        append_shortcut_hint(self.btn_search_adv, "Ctrl+Shift+F")
        append_shortcut_hint(self.btn_tools, "Ctrl+T")

    def _open_modeless_page(
        self,
        key: str,
        factory,
        on_close=None,
    ) -> Optional[QDialog]:
        """Deschide modeless page in `App`."""
        k = (key or "").strip().lower()
        if not k:
            return None
        existing = self._page_windows.get(k)
        if existing is not None:
            try:
                if existing.isVisible():
                    if existing.isMinimized():
                        existing.showNormal()
                    existing.raise_()
                    existing.activateWindow()
                    return existing
            except Exception:
                pass
            self._page_windows.pop(k, None)

        try:
            dlg = factory()
        except Exception as e:
            QMessageBox.warning(self, "Pagina", f"Nu pot deschide pagina:\n{e}")
            return None
        if dlg is None:
            return None
        geom_key = f"ui_page_window_geometry::{k}"
        state_key = f"ui_page_window_state::{k}"
        start_maximized = False
        try:
            dlg.setWindowModality(Qt.WindowModality.NonModal)
            dlg.setWindowFlag(Qt.WindowType.Window, True)
            dlg.setWindowFlag(Qt.WindowType.WindowContextHelpButtonHint, False)
            dlg.setAttribute(Qt.WidgetAttribute.WA_DeleteOnClose, True)
            if APP_ICON is not None:
                dlg.setWindowIcon(APP_ICON)
            raw_state = (get_setting(state_key, "normal") or "normal").strip().lower()
            start_maximized = raw_state == "maximized"
            raw_geom = (get_setting(geom_key, "") or "").strip()
            if raw_geom:
                parts = [int(x.strip()) for x in raw_geom.split(",")]
                if len(parts) == 4 and parts[2] > 160 and parts[3] > 120:
                    dlg.setGeometry(QRect(parts[0], parts[1], parts[2], parts[3]))
            else:
                cascade_idx = len(self._page_windows) % 6
                step = 26
                base_x = int(self.x()) + 56 + cascade_idx * step
                base_y = int(self.y()) + 56 + cascade_idx * step
                dlg.move(max(20, base_x), max(20, base_y))
        except Exception:
            pass

        def _save_placement():
            """Salveaza placement in `App`, ca helper intern in `_open_modeless_page`."""
            try:
                if dlg.isMaximized():
                    set_setting(state_key, "maximized")
                    gg = dlg.normalGeometry()
                else:
                    set_setting(state_key, "normal")
                    gg = dlg.geometry()
                if gg is not None and gg.isValid() and gg.width() > 0 and gg.height() > 0:
                    set_setting(geom_key, f"{gg.x()},{gg.y()},{gg.width()},{gg.height()}")
            except Exception:
                pass

        def _on_destroyed(_obj=None):
            """Gestioneaza evenimentul destroyed in `App`, ca helper intern in `_open_modeless_page`."""
            self._page_windows.pop(k, None)
            if callable(on_close):
                try:
                    on_close()
                except Exception:
                    pass

        try:
            dlg.finished.connect(lambda _code: _save_placement())
        except Exception:
            pass
        try:
            dlg.destroyed.connect(_on_destroyed)
        except Exception:
            pass
        self._page_windows[k] = dlg
        try:
            if start_maximized:
                dlg.showMaximized()
            else:
                dlg.show()
            dlg.raise_()
            dlg.activateWindow()
        except Exception:
            try:
                if start_maximized:
                    dlg.showMaximized()
                else:
                    dlg.show()
            except Exception:
                pass
        return dlg

    def _close_all_open_pages(self):
        """Inchide all open pages in `App`."""
        to_close: List[QWidget] = []
        seen_ids = set()

        registries: List[Dict[str, QDialog]] = []
        try:
            registries.append(getattr(self, "_page_windows", {}) or {})
        except Exception:
            pass
        try:
            registries.append(_patient_page_windows)
        except Exception:
            pass

        for reg in registries:
            for _k, dlg in list((reg or {}).items()):
                if dlg is None:
                    continue
                oid = id(dlg)
                if oid in seen_ids:
                    continue
                seen_ids.add(oid)
                to_close.append(dlg)
            try:
                reg.clear()
            except Exception:
                pass

        app = QApplication.instance()
        if app is not None:
            for w in list(app.topLevelWidgets()):
                if w is None or w is self:
                    continue
                if isinstance(w, QMessageBox):
                    continue
                oid = id(w)
                if oid in seen_ids:
                    continue
                seen_ids.add(oid)
                to_close.append(w)

        for w in to_close:
            try:
                w.close()
            except Exception:
                pass

    def keyPressEvent(self, event):
        """Proceseaza shortcut-urile globale de tastatura ale aplicatiei."""
        if event.key() == Qt.Key.Key_F11:
            self.toggle_window_mode()
            event.accept()
            return
        super().keyPressEvent(event)

    # ---------------- status helpers ----------------
    def _now_str(self):
        """Gestioneaza str in `App`."""
        return datetime.now().strftime("%Y-%m-%d %H:%M")

    def _set_status_backup(self):
        """Seteaza status backup in `App`."""
        self._last_status_backup = self._now_str()

    def _set_status_export(self):
        """Seteaza status export in `App`."""
        self._last_status_export = self._now_str()

    def _set_status_import(self):
        """Seteaza status import in `App`."""
        self._last_status_import = self._now_str()

    def _set_status_dupcheck(self):
        """Seteaza status dupcheck in `App`."""
        self._last_status_dupcheck = self._now_str()

    def _set_status_sync(self):
        """Seteaza status sync in `App`."""
        self._last_status_sync = self._now_str()
        try:
            self._set_sync_label(f"Sync: {self._last_status_sync}", "#0f766e")
        except Exception:
            pass

    def _set_status_text(self):
        """Seteaza status text in `App`."""
        parts = []
        if self._last_status_backup:
            parts.append(f"Backup: {self._last_status_backup}")
        if self._last_status_export:
            parts.append(f"CSV: {self._last_status_export}")
        if self._last_status_import:
            parts.append(f"Import: {self._last_status_import}")
        if self._last_status_dupcheck:
            parts.append(f"DupCheck: {self._last_status_dupcheck}")
        if self._last_status_sync:
            parts.append(f"Sync: {self._last_status_sync}")
        parts.append(f"User: {get_current_user()} ({get_current_role()})")
        sep = "  |  "
        self.lbl_status.setText(sep.join(parts) if parts else "Ready")

    def _set_online_label(self, online: bool):
        """Seteaza online label in `App`."""
        self._online_state = online
        if online:
            self.lbl_net.setText("Online")
            self.lbl_net.setStyleSheet("color: #16a34a; font-weight: 600;")
        else:
            self.lbl_net.setText("Offline")
            self.lbl_net.setStyleSheet("color: #dc2626; font-weight: 600;")

    def _set_sync_label(self, text: str, color: str = "#64748b"):
        """Seteaza sync label in `App`."""
        try:
            self.lbl_sync.setText(text)
            self.lbl_sync.setStyleSheet(f"color: {color}; font-weight: 600;")
        except Exception:
            pass

    def _check_online_async(self):
        """Gestioneaza online async in `App`."""
        if not SUPABASE_URL or not SUPABASE_ANON_KEY:
            self._set_online_label(False)
            return

        def _probe():
            """Testeaza conectivitatea in fundal si returneaza rezultatul (helper intern pentru `_check_online_async`)."""
            ok = False
            try:
                ok, _msg = test_supabase_connectivity(timeout_sec=5)
            except Exception:
                ok = False
            QTimer.singleShot(0, lambda ok=ok: self._set_online_label(ok))

        try:
            threading.Thread(target=_probe, daemon=True).start()
        except Exception:
            self._set_online_label(False)

    def test_supabase_connection_ui(self):
        """Testeaza Supabase connection interfata in `App`."""
        worker = Worker(test_supabase_connectivity, 6)

        def done(res):
            """Proceseaza finalizarea cu succes a operatiei asincrone (helper intern pentru `test_supabase_connection_ui`)."""
            ok = False
            msg = ""
            if isinstance(res, tuple) and len(res) >= 2:
                ok = bool(res[0])
                msg = str(res[1])
            else:
                msg = str(res)
            self._set_online_label(ok)
            if ok:
                QMessageBox.information(self, "Conexiune Supabase", f"Conexiune OK.\n\n{msg}")
            else:
                QMessageBox.warning(self, "Conexiune Supabase", f"Conexiune esuata.\n\n{msg}")

        self.run_worker_with_progress(
            "Test conexiune",
            "Testez conexiunea la Supabase...",
            worker,
            done,
        )

    def apply_role_permissions(self):
        """Aplica role permissions in `App`."""
        role = get_current_role()
        is_admin = role == "admin"
        can_edit = role in ("admin", "medic", "asistenta")
        can_delete = role == "admin"
        can_export = role in ("admin", "receptie")

        try:
            base_by_feature: Dict[str, bool] = {
                "main.save_consult": can_edit,
                "main.update_pacient": can_edit,
                "main.delete_pacient": can_delete,
                "main.import_excel": can_export,
                "main.export_csv": can_export,
                "main.backup_db": is_admin,
                "main.open_tools": True,
                "main.search_advanced": True,
                "main.check_duplicates": can_edit,
                "main.recalc_ages": True,
            }
            for feature_key, btn_attr in MAIN_FEATURE_BUTTONS:
                btn = getattr(self, btn_attr, None)
                if btn is None:
                    continue
                if not bool(base_by_feature.get(feature_key, True)):
                    btn.setEnabled(False)
                    continue
                btn.setEnabled(is_feature_allowed_for_current_user(feature_key))
            ops = [
                getattr(self, "btn_import_excel", None),
                getattr(self, "btn_export_csv", None),
                getattr(self, "btn_backup", None),
            ]
            enabled_any = any(op is not None and op.isEnabled() for op in ops)
            if getattr(self, "btn_data_ops", None) is not None:
                self.btn_data_ops.setEnabled(enabled_any)
            quality_ops = [
                getattr(self, "btn_check_dups", None),
                getattr(self, "btn_recalc_ages", None),
            ]
            enabled_quality = any(op is not None and op.isEnabled() for op in quality_ops)
            if getattr(self, "btn_quality", None) is not None:
                self.btn_quality.setEnabled(enabled_quality)
        except Exception:
            pass

    def _reload_locations_combo(self):
        """Reincarca locations combo in `App`."""
        try:
            ensure_default_location()
            conn = get_conn()
            cur = conn.cursor()
            cur.execute("SELECT id, name FROM locations ORDER BY id ASC")
            rows = cur.fetchall()
            conn.close()
            current_id = get_current_location_id()
            self.cb_location.blockSignals(True)
            self.cb_location.clear()
            for r in rows:
                self.cb_location.addItem(r["name"] or f"Sediu {r['id']}", r["id"])
            if current_id is not None:
                idx = self.cb_location.findData(current_id)
                if idx >= 0:
                    self.cb_location.setCurrentIndex(idx)
            self.cb_location.blockSignals(False)
        except Exception:
            pass

    def _on_location_changed(self):
        """Gestioneaza evenimentul location changed in `App`."""
        try:
            loc_id = self.cb_location.currentData()
            if loc_id is None:
                return
            set_current_location_id(int(loc_id))
            self._set_status_text()
        except Exception:
            pass

    # ---------------- CNP live ----------------
    def on_cnp_changed_live(self, _txt: str = ""):
        """Gestioneaza evenimentul CNP changed live in `App`."""
        raw = (self.master_inputs["cnp"].text() or "").strip()
        digits = normalize_cnp_digits(raw)
        cnp_edit = self.master_inputs["cnp"]

        if raw == "":
            cnp_edit.setStyleSheet(CNP_OK_STYLE)
            cnp_edit.setToolTip(
                "CNP opTional. DacT lipseTte, la salvare vei fi Tntrebat dacT salvezi fTrT CNP."
            )
            self._set_transient_status(None)
            return

        if len(digits) != 13:
            cnp_edit.setStyleSheet(CNP_INVALID_STYLE)
            cnp_edit.setToolTip(
                f"CNP invalid: {len(digits)} cifre (trebuie 13). La salvare poTi continua fTrT CNP."
            )
            self._set_transient_status(
                f"CNP invalid: {len(digits)}/13 cifre (la salvare poTi continua fTrT CNP)", seconds=4
            )
            return

        if not cnp_checksum_valid(digits):
            cnp_edit.setStyleSheet(CNP_INVALID_STYLE)
            cnp_edit.setToolTip(
                "CNP invalid: checksum greTit. La salvare poTi continua fTrT CNP."
            )
            self._set_transient_status(
                "CNP invalid: checksum greTit (la salvare poTi continua fTrT CNP)", seconds=4
            )
            return

        cnp_edit.setStyleSheet(CNP_OK_STYLE)
        cnp_edit.setToolTip("CNP valid (13 cifre + checksum).")
        self._set_transient_status(None)
        self._autofill_from_cnp_on_finish()

    def _autofill_from_cnp_on_finish(self):
        """Gestioneaza from CNP on finish in `App`."""
        cnp = (self.master_inputs["cnp"].text() or "").strip()
        digits = normalize_cnp_digits(cnp)
        if digits and cnp_checksum_valid(digits):
            self.master_inputs["cnp"].setText(digits)
            sx = sex_from_cnp(digits) or ""
            self.master_inputs["sex"].setText(sx)
            dn = birthdate_from_cnp(digits)
            if dn:
                cur_dn = (self.master_inputs["data_nasterii"].text() or "").strip()
                if (not cur_dn) or (not validate_ymd_or_empty(cur_dn)):
                    self.master_inputs["data_nasterii"].setText(dn)
                age = calc_age_ani(dn)
                if age is not None:
                    self.master_inputs["varsta"].setText(str(age))
        else:
            pass

    # ---------------- threaded runner ----------------
    def run_worker_with_progress(self, title: str, label: str, worker: Worker, on_done):
        """Ruleaza worker with progress in `App`."""
        dlg = QProgressDialog(label, "AnuleazT", 0, 100, self)
        dlg.setWindowTitle(title)
        dlg.setWindowModality(Qt.WindowModality.WindowModal)
        dlg.setAutoClose(False)
        dlg.setAutoReset(False)
        dlg.show()

        thread = QThread(self)
        worker.moveToThread(thread)

        def cleanup():
            """Curata resursele temporare folosite de operatia curenta (helper intern pentru `run_worker_with_progress`)."""
            try:
                thread.quit()
                thread.wait()
            except Exception:
                pass

        def on_progress(p, msg):
            """Gestioneaza evenimentul progress in `App`, ca helper intern in `run_worker_with_progress`."""
            percent = int(max(0, min(100, p)))
            dlg.setValue(percent)
            base = str(msg).strip() if msg else str(label)
            dlg.setLabelText(f"{base}\n{percent}%")

        def on_finished(res):
            """Gestioneaza evenimentul finished in `App`, ca helper intern in `run_worker_with_progress`."""
            dlg.close()
            cleanup()
            on_done(res)

        def on_error(msg):
            """Gestioneaza evenimentul error in `App`, ca helper intern in `run_worker_with_progress`."""
            dlg.close()
            cleanup()
            QMessageBox.critical(self, "Eroare", msg)

        def on_cancelled():
            """Gestioneaza evenimentul cancelled in `App`, ca helper intern in `run_worker_with_progress`."""
            dlg.close()
            cleanup()
            QMessageBox.information(self, "Anulat", "Operatiunea a fost anulata.")

        worker.progress.connect(on_progress)
        worker.finished.connect(on_finished)
        worker.error.connect(on_error)
        worker.cancelled.connect(on_cancelled)
        thread.started.connect(worker.run)

        def request_cancel():
            """Gestioneaza cancel in `App`, ca helper intern in `run_worker_with_progress`."""
            dlg.setLabelText("Se anuleazT...")
            worker.cancel()

        dlg.canceled.connect(request_cancel)
        thread.start()

    # ---------------- autosave ----------------
    def _autosave_backup_worker(self, reason: str = "") -> Dict[str, Any]:
        """Ruleaza backup-ul automat in thread separat pentru a evita blocarea UI."""
        out: Dict[str, Any] = {
            "ok": False,
            "reason": (reason or "").strip(),
            "daily_done": False,
            "prune_done": False,
        }
        try:
            try:
                conn = get_conn()
                conn.execute("PRAGMA wal_checkpoint(PASSIVE);")
                conn.close()
            except Exception:
                pass

            backup_ok = True
            last_path = last_backup_path()
            export_db_copy_atomic(str(last_path))
            if not _sqlite_backup_quick_check(last_path):
                backup_ok = False
                log_error(f"Backup quick_check invalid: {last_path}")
            out["last_path"] = str(last_path)

            today = date.today()
            out["today"] = today.isoformat()
            if self._last_daily_backup_date != today:
                day_path = daily_backup_path(today)
                export_db_copy_atomic(str(day_path))
                if not _sqlite_backup_quick_check(day_path):
                    backup_ok = False
                    log_error(f"Backup quick_check invalid: {day_path}")
                out["daily_done"] = True
                out["daily_path"] = str(day_path)

            if self._last_backup_prune_date != today:
                prune_report = prune_autobackups(AUTOBACKUP_RETENTION_DAYS)
                out["prune_done"] = True
                out["prune_report"] = prune_report
                if int(prune_report.get("errors") or 0) > 0:
                    log_error(f"Backup prune completed with errors: {prune_report}")

            out["ok"] = bool(backup_ok)
            return out
        except Exception as e:
            out["error"] = str(e)
            log_error("autosave_backup_worker failed", e)
            return out

    def autosave_backup_now(self, reason: str = ""):
        """Lanseaza backup automat non-blocant (exceptie: on_close ruleaza sincron)."""
        # La inchidere aplicatie, backup-ul trebuie finalizat inainte de exit.
        if (reason or "").strip() == "on_close":
            res = self._autosave_backup_worker(reason=reason)
            if bool((res or {}).get("ok")):
                self._dirty_since_last_backup = False
                self._set_status_backup()
                self._set_status_text()
            else:
                self._dirty_since_last_backup = True
            return

        if self._autosave_in_progress:
            self._autosave_pending = True
            self._autosave_pending_reason = (reason or "").strip()
            return

        self._autosave_in_progress = True
        worker = Worker(self._autosave_backup_worker, reason)
        thread = QThread(self)
        worker.moveToThread(thread)

        def cleanup():
            """Curata resursele worker-ului de autosave."""
            try:
                thread.quit()
                thread.wait()
            except Exception:
                pass

        def finalize_next_if_pending():
            """Replanifica un backup daca a fost cerut in timp ce rula unul."""
            if not self._autosave_pending:
                return
            next_reason = self._autosave_pending_reason or "pending"
            self._autosave_pending = False
            self._autosave_pending_reason = ""
            QTimer.singleShot(60, lambda nr=next_reason: self.autosave_backup_now(reason=nr))

        def on_finished(res):
            """Proceseaza rezultatul backup-ului automat asincron."""
            cleanup()
            self._autosave_in_progress = False
            ok = bool((res or {}).get("ok")) if isinstance(res, dict) else False
            if ok:
                self._dirty_since_last_backup = False
                today_txt = str((res or {}).get("today") or "").strip()
                if today_txt:
                    try:
                        self._last_daily_backup_date = datetime.strptime(today_txt, "%Y-%m-%d").date()
                    except Exception:
                        pass
                if bool((res or {}).get("prune_done")):
                    self._last_backup_prune_date = date.today()
                self._set_status_backup()
                self._set_status_text()
            else:
                self._dirty_since_last_backup = True
            finalize_next_if_pending()

        def on_error(msg):
            """Gestioneaza erori din worker-ul de autosave."""
            cleanup()
            self._autosave_in_progress = False
            self._dirty_since_last_backup = True
            log_error("autosave_backup_now failed", msg)
            finalize_next_if_pending()

        def on_cancelled():
            """Gestioneaza anularea worker-ului de autosave."""
            cleanup()
            self._autosave_in_progress = False
            self._dirty_since_last_backup = True
            finalize_next_if_pending()

        worker.finished.connect(on_finished)
        worker.error.connect(on_error)
        worker.cancelled.connect(on_cancelled)
        thread.started.connect(worker.run)
        thread.start()

    def mark_dirty_and_schedule_backup(self, reason: str):
        """Marcheaza dirty and schedule backup in `App`."""
        self._dirty_since_last_backup = True
        self.debounce_timer.start()

    def maybe_autosave_backup(self):
        """Decide daca ruleaza autosave backup in `App`."""
        if self._dirty_since_last_backup:
            self.autosave_backup_now(reason="timer_5_min")

    # ---------------- consult draft autosave ----------------
    def _consult_draft_setting_key(self) -> str:
        """Gestioneaza draft setting key in `App`."""
        user = (get_current_user() or DEFAULT_USER).strip() or DEFAULT_USER
        return f"{CONSULT_DRAFT_KEY_PREFIX}{user}"

    def _draft_has_values(self, payload: Optional[dict]) -> bool:
        """Gestioneaza has values in `App`."""
        if not isinstance(payload, dict):
            return False
        for v in payload.values():
            if isinstance(v, str) and v.strip():
                return True
            if isinstance(v, (int, float)) and float(v) != 0:
                return True
            if v not in (None, "", 0):
                return True
        return False

    def _bind_consult_draft_signals(self):
        """Leaga consult draft signals in `App`."""
        def _bind_widget(widget: Any):
            """Leaga widget in `App`, ca helper intern in `_bind_consult_draft_signals`."""
            if widget is None:
                return
            try:
                if isinstance(widget, DatePicker):
                    widget.edit.textChanged.connect(self._on_consult_draft_changed)
                    return
                if isinstance(widget, DateTimePicker):
                    widget.edit.textChanged.connect(self._on_consult_draft_changed)
                    widget.time_edit.textChanged.connect(self._on_consult_draft_changed)
                    return
                if isinstance(widget, QLineEdit):
                    widget.textChanged.connect(self._on_consult_draft_changed)
                    return
                if isinstance(widget, QTextEdit):
                    widget.textChanged.connect(self._on_consult_draft_changed)
                    return
                if isinstance(widget, QComboBox):
                    widget.currentTextChanged.connect(self._on_consult_draft_changed)
                    return
                if isinstance(widget, QSpinBox):
                    widget.valueChanged.connect(self._on_consult_draft_changed)
                    return
            except Exception:
                return

        for _, k in MASTER_FIELDS:
            _bind_widget(self.master_inputs.get(k))
        for _, k in CONSULT_FIELDS:
            _bind_widget(self.consult_inputs.get(k))

    def _on_consult_draft_changed(self, *_args):
        """Gestioneaza evenimentul consult draft changed in `App`."""
        if not getattr(self, "_consult_draft_tracking_enabled", False):
            return
        if getattr(self, "_consult_draft_loading", False):
            return
        try:
            self.consult_draft_timer.start()
        except Exception:
            pass

    def _save_consult_draft_now(self, force: bool = False):
        """Salveaza consult draft now in `App`."""
        if not force and not getattr(self, "_consult_draft_tracking_enabled", False):
            return
        if getattr(self, "_consult_draft_loading", False):
            return
        try:
            master_payload = self.master_payload_from_form()
            consult_payload = self.consult_payload_from_form()
        except Exception:
            return

        has_values = self._draft_has_values(master_payload) or self._draft_has_values(consult_payload)
        key = self._consult_draft_setting_key()
        if not has_values:
            try:
                delete_setting(key)
            except Exception:
                pass
            self._consult_draft_last_raw = ""
            return

        payload = {
            "saved_at": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
            "master": master_payload,
            "consult": consult_payload,
        }
        try:
            raw = json.dumps(payload, ensure_ascii=False, sort_keys=True)
        except Exception:
            return
        if not force and raw == (getattr(self, "_consult_draft_last_raw", "") or ""):
            return
        set_setting(key, raw)
        self._consult_draft_last_raw = raw

    def _clear_consult_draft(self):
        """Curata consult draft in `App`."""
        try:
            delete_setting(self._consult_draft_setting_key())
        except Exception:
            pass
        self._consult_draft_last_raw = ""

    def _is_main_form_empty(self) -> bool:
        """Verifica daca main form empty in `App`."""
        try:
            return not self._draft_has_values(self.master_payload_from_form()) and not self._draft_has_values(self.consult_payload_from_form())
        except Exception:
            return True

    def _apply_consult_draft(self, draft_payload: Dict[str, Any]) -> bool:
        """Aplica consult draft in `App`."""
        master_payload = draft_payload.get("master") if isinstance(draft_payload, dict) else None
        consult_payload = draft_payload.get("consult") if isinstance(draft_payload, dict) else None
        if not isinstance(master_payload, dict) and not isinstance(consult_payload, dict):
            return False

        self._consult_draft_loading = True
        try:
            if isinstance(master_payload, dict):
                for _, k in MASTER_FIELDS:
                    w = self.master_inputs.get(k)
                    if w is None:
                        continue
                    val = master_payload.get(k)
                    if k == "sms_opt_out" and isinstance(w, QComboBox):
                        try:
                            idx_sms = w.findData(_to_int_flag(val))
                            w.setCurrentIndex(idx_sms if idx_sms >= 0 else 0)
                        except Exception:
                            pass
                    else:
                        txt = "" if val is None else str(val)
                        try:
                            w.setText(txt)
                        except Exception:
                            pass
            if isinstance(consult_payload, dict):
                for _, k in CONSULT_FIELDS:
                    w = self.consult_inputs.get(k)
                    if w is None:
                        continue
                    val = consult_payload.get(k)
                    if k in CONSULT_COMBO_KEYS or k == "medic":
                        txt = "" if val is None else str(val).strip()
                        try:
                            idx = w.findText(txt)
                            if idx < 0 and txt:
                                w.addItem(txt)
                                idx = w.findText(txt)
                            w.setCurrentIndex(idx if idx >= 0 else 0)
                        except Exception:
                            pass
                    elif k == "interval_luni_revenire":
                        try:
                            w.setValue(int(val or 0))
                        except Exception:
                            w.setValue(0)
                    elif k in TEXTAREA_KEYS:
                        try:
                            w.setPlainText("" if val is None else str(val))
                        except Exception:
                            pass
                    else:
                        try:
                            w.setText("" if val is None else str(val))
                        except Exception:
                            pass
        finally:
            self._consult_draft_loading = False
        return True

    def _restore_consult_draft_if_any(self):
        """Restaureaza consult draft if any in `App`."""
        key = self._consult_draft_setting_key()
        raw = (get_setting(key, "") or "").strip()
        if not raw:
            return
        try:
            payload = json.loads(raw)
        except Exception:
            payload = {}
        if not isinstance(payload, dict):
            return
        if not self._draft_has_values(payload.get("master")) and not self._draft_has_values(payload.get("consult")):
            self._clear_consult_draft()
            return
        if not self._is_main_form_empty():
            return

        saved_at = str(payload.get("saved_at") or "").strip() or "necunoscut"
        ans = QMessageBox.question(
            self,
            "Draft consult",
            f"Am gasit un draft consult salvat la {saved_at}.\nVrei sa il restaurez?",
            QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
            QMessageBox.StandardButton.Yes,
        )
        if ans != QMessageBox.StandardButton.Yes:
            self._clear_consult_draft()
            return
        if self._apply_consult_draft(payload):
            self._set_transient_status("Draft consult restaurat.", seconds=4)
            self._save_consult_draft_now(force=True)

    # ---------------- common helpers ----------------
    def ask_yes_no(self, title: str, text: str, min_width: int | None = None) -> bool:
        """Gestioneaza yes no in `App`."""
        box = QMessageBox(self)
        box.setIcon(QMessageBox.Icon.Question)
        box.setWindowTitle(title)
        box.setText(text)
        box.setStandardButtons(QMessageBox.StandardButton.Ok | QMessageBox.StandardButton.Cancel)
        box.setDefaultButton(QMessageBox.StandardButton.Cancel)
        if min_width:
            box.setMinimumWidth(min_width)
        btn = box.exec()
        return btn == QMessageBox.StandardButton.Ok

    def clear_form(self):
        """Curata campurile din formularul principal fara a pierde starea aplicatiei."""
        if not self.ask_yes_no("Curata formular", "Esti sigur?", min_width=460):
            return
        self.do_clear_form(clear_draft=True)

    def do_clear_form(self, clear_draft: bool = False):
        """Gestioneaza clear form in `App`."""
        self.current_id = None
        for _, k in MASTER_FIELDS:
            w_master = self.master_inputs[k]
            if k == "sms_opt_out" and isinstance(w_master, QComboBox):
                w_master.setCurrentIndex(0)
            else:
                w_master.clear()
        for _, k in CONSULT_FIELDS:
            w = self.consult_inputs[k]
            if k in CONSULT_COMBO_KEYS or k == "medic":
                w.setCurrentIndex(0)
            elif k == "interval_luni_revenire":
                w.setValue(0)
            elif k in TEXTAREA_KEYS:
                w.setPlainText("")
            else:
                w.clear()
        try:
            self._clear_summary()
        except Exception:
            pass
        if clear_draft:
            self._clear_consult_draft()

    def master_payload_from_form(self) -> dict:
        """Gestioneaza payload from form in `App`."""
        payload = {}
        for _, k in MASTER_FIELDS:
            w = self.master_inputs[k]
            if k in DATE_KEYS:
                txt = w.text().strip()
                payload[k] = txt if txt else None
            elif k == "sms_opt_out":
                try:
                    payload[k] = int(w.currentData() or 0)
                except Exception:
                    payload[k] = 0
            else:
                payload[k] = w.text().strip() or None
        return payload

    def consult_payload_from_form(self) -> dict:
        """Gestioneaza payload from form in `App`."""
        payload = {}
        for _, k in CONSULT_FIELDS:
            w = self.consult_inputs[k]

            if k in DATE_KEYS:
                txt = w.text().strip()
                payload[k] = txt if txt else None

            elif k in CONSULT_COMBO_KEYS or k == "medic":
                val = w.currentText().strip()
                payload[k] = val if val else None

            elif k == "interval_luni_revenire":
                v = int(w.value())
                payload[k] = None if v == 0 else v

            elif k in TEXTAREA_KEYS:
                payload[k] = w.toPlainText().strip() or None

            else:
                payload[k] = w.text().strip() or None

        payload = normalize_consult_diagnoses(payload, parent=self)
        return payload

    def validate_master(self, payload: dict) -> Optional[str]:
        """Valideaza master in `App`."""
        if not payload.get("nume_prenume"):
            return "Nume Ti prenume este obligatoriu."
        if payload.get("data_nasterii") and not validate_ymd_or_empty(payload["data_nasterii"]):
            return "Data naTterii trebuie sT fie YYYY-MM-DD."
        return None

    def validate_consult(self, payload: dict) -> Optional[str]:
        """Valideaza consult in `App`."""
        if payload.get("data_consultului") and not validate_ymd_or_empty(payload["data_consultului"]):
            return "Data consultului trebuie sT fie YYYY-MM-DD."
        if payload.get("data_revenire_control") and not validate_ymd_hhmm_or_empty(payload["data_revenire_control"]):
            return "Data revenire control trebuie sa fie YYYY-MM-DD sau YYYY-MM-DD HH:MM."
        d_cons = _safe_parse_ymd(payload.get("data_consultului"))
        d_ctrl = _safe_parse_ymd(payload.get("data_revenire_control"))
        if d_cons is not None and d_ctrl is not None and d_ctrl < d_cons:
            return "Data revenire control nu poate fi inainte de data consultului."
        return None

    def confirm_or_drop_invalid_phone(self, master_payload: dict) -> Optional[dict]:
        """Confirma or drop invalid phone in `App`."""
        p = dict(master_payload or {})
        raw = (p.get("telefon") or "").strip()
        if not raw:
            return p
        normalized = normalize_ro_mobile_phone(raw) or raw
        if is_valid_ro_mobile_phone(normalized):
            p["telefon"] = normalized
            return p

        text = (
            "Telefonul introdus nu este valid pentru mobil RO.\n"
            "Exemple valide: 07xxxxxxxx, +407xxxxxxxx.\n\n"
            "Vrei sa continui si sa salvez pacientul fara telefon?"
        )
        btn = QMessageBox.question(
            self,
            "Telefon invalid",
            text,
            QMessageBox.StandardButton.Ok | QMessageBox.StandardButton.Cancel,
            QMessageBox.StandardButton.Cancel,
        )
        if btn != QMessageBox.StandardButton.Ok:
            return None
        p["telefon"] = None
        self._set_transient_status("Salvez pacientul fara telefon (numar invalid).", seconds=5)
        return p

    def confirm_cnp_sex_consistency(self, master_payload: dict) -> Optional[dict]:
        """Confirma CNP sex consistency in `App`."""
        p = dict(master_payload or {})
        cnp = (p.get("cnp") or "").strip()
        if not cnp or not cnp_is_valid_13(cnp):
            return p
        sex_cnp = sex_from_cnp(cnp)
        if not sex_cnp:
            return p
        sex_payload = (p.get("sex") or "").strip()
        if not sex_payload:
            p["sex"] = sex_cnp
            return p
        if _norm(sex_payload) == _norm(sex_cnp):
            p["sex"] = sex_cnp
            return p

        btn = QMessageBox.question(
            self,
            "Incoerenta CNP/Sex",
            (
                f"Sex introdus: {sex_payload}\n"
                f"Sex derivat din CNP: {sex_cnp}\n\n"
                "Corectez automat sexul conform CNP si continui salvarea?"
            ),
            QMessageBox.StandardButton.Ok | QMessageBox.StandardButton.Cancel,
            QMessageBox.StandardButton.Ok,
        )
        if btn != QMessageBox.StandardButton.Ok:
            return None
        p["sex"] = sex_cnp
        return p

    def confirm_or_drop_invalid_cnp(self, master_payload: dict) -> Optional[dict]:
        """Confirma or drop invalid CNP in `App`."""
        p = dict(master_payload or {})
        raw = (p.get("cnp") or "").strip()
        if not raw:
            text = (
                "CNP lipseTte.\n\n"
                "CNP trebuie sT aibT EXACT 13 cifre Ti checksum valid.\n"
                "Vrei sT continui Ti sT salvezi pacientul FTRT CNPT"
            )
            btn = QMessageBox.question(
                self, "CNP invalid", text,
                QMessageBox.StandardButton.Ok | QMessageBox.StandardButton.Cancel,
                QMessageBox.StandardButton.Cancel
            )
            if btn != QMessageBox.StandardButton.Ok:
                return None
            p["cnp"] = None
            p["sex"] = None
            self._set_transient_status("Salvez pacientul fTrT CNP (ai acceptat lipsT CNP).", seconds=5)
            return p

        digits = normalize_cnp_digits(raw)
        if len(digits) != 13:
            text = (
                f"CNP invalid: ai introdus {len(digits)} cifre (trebuie 13).\n\n"
                "Vrei sT continui Ti sT salvezi pacientul FTRT CNPT"
            )
            btn = QMessageBox.question(
                self, "CNP invalid", text,
                QMessageBox.StandardButton.Ok | QMessageBox.StandardButton.Cancel,
                QMessageBox.StandardButton.Cancel
            )
            if btn != QMessageBox.StandardButton.Ok:
                return None
            p["cnp"] = None
            p["sex"] = None
            self._set_transient_status("Salvez pacientul fTrT CNP (ai acceptat CNP invalid).", seconds=5)
            return p

        if not cnp_checksum_valid(digits):
            text = (
                "CNP invalid: checksum greTit.\n\n"
                "Vrei sT continui Ti sT salvezi pacientul FTRT CNPT"
            )
            btn = QMessageBox.question(
                self, "CNP invalid", text,
                QMessageBox.StandardButton.Ok | QMessageBox.StandardButton.Cancel,
                QMessageBox.StandardButton.Cancel
            )
            if btn != QMessageBox.StandardButton.Ok:
                return None
            p["cnp"] = None
            p["sex"] = None
            self._set_transient_status("Salvez pacientul fTrT CNP (ai acceptat CNP invalid).", seconds=5)
            return p

        p["cnp"] = digits
        return p

# ---------------- table fast upsert/remove ----------------
    def _table_name_col_index(self) -> int:
        """Gestioneaza name col index in `App`."""
        return 2  # "Nume"

    def _find_row_by_id(self, pid: int) -> Optional[int]:
        """Cauta row by ID in `App`."""
        for r in range(self.table.rowCount()):
            it = self.table.item(r, 1)
            if it and it.text().strip().isdigit() and int(it.text()) == pid:
                return r
        return None

    def _apply_row_style_and_values(self, row_idx: int, rd: dict):
        """Aplica row style and values in `App`."""
        bg_yellow = getattr(self, "_row_bg_yellow", QBrush(QColor(255, 249, 196)))
        bg_red = getattr(self, "_row_bg_red", QBrush(QColor(255, 205, 210)))
        bold = getattr(self, "_row_bold_font", QFont())

        v_cache = rd.get("varsta")
        if v_cache in ("", None):
            v_calc = calc_age_ani(rd.get("data_nasterii"))
        else:
            try:
                v_calc = int(v_cache)
            except Exception:
                v_calc = calc_age_ani(rd.get("data_nasterii"))

        status = control_status(rd.get("data_revenire_control"), days_ahead=7)
        if status == "today":
            alert_symbol = "đź”´"
            row_bg = bg_red
            tip = "CONTROL AZI"
        elif status == "soon":
            alert_symbol = "âŹ°"
            row_bg = bg_yellow
            tip = "Revenire control in urmatoarele 7 zile"
        else:
            alert_symbol = ""
            row_bg = None
            tip = ""

        values = {
            "alerta": alert_symbol,
            "id": rd.get("id"),
            "nume_prenume": rd.get("nume_prenume"),
            "cnp": rd.get("cnp"),
            "sex": rd.get("sex"),
            "telefon": rd.get("telefon"),
            "email": rd.get("email"),
            "data_nasterii": rd.get("data_nasterii"),
            "varsta": v_calc,
            "domiciliu": rd.get("domiciliu"),
            "ultimul_consult": rd.get("ultimul_consult"),
            "ultim_diagnostic": rd.get("ultim_diagnostic"),
            "data_revenire_control": rd.get("data_revenire_control"),
            "status_follow_up": rd.get("status_follow_up"),
        }

        for col_idx, key in enumerate(TABLE_COLS):
            val = values.get(key, "")
            item = QTableWidgetItem("" if val is None else str(val))
            item.setFlags(item.flags() & ~Qt.ItemFlag.ItemIsEditable)

            if key == "ultim_diagnostic" and (val or ""):
                item.setToolTip(str(val))
            if key == "alerta":
                item.setTextAlignment(Qt.AlignmentFlag.AlignCenter)

            if row_bg is not None:
                item.setBackground(row_bg)
                item.setFont(bold)
                if tip:
                    dctrl = values.get("data_revenire_control") or ""
                    item.setToolTip(f"{tip}\nData control: {dctrl}")

            self.table.setItem(row_idx, col_idx, item)

    def _table_upsert_patient_row(self, pid: int, force_reload_on_filter: bool = True):
        # Main table is paginated; full refresh keeps page boundaries and counters consistent.
        """Gestioneaza upsert patient row in `App`."""
        self.load_table(auto_select_first=False)

    def _table_remove_patient_row(self, pid: int, force_reload_on_filter: bool = True):
        """Gestioneaza remove patient row in `App`."""
        self.load_table(auto_select_first=False)

    # ---------------- list load ----------------
    def _queue_search_timer(self, _text: str):
        """Gestioneaza search timer in `App`."""
        try:
            self._search_timer.start()
        except Exception:
            pass

    def _run_search_timer(self):
        """Ruleaza search timer in `App`."""
        try:
            txt = self.search.text().strip()
            if txt == getattr(self, "_last_search_text", ""):
                return
            self._last_search_text = txt
            self.load_table()
        except Exception:
            pass

    def _apply_search_highlight(self, query: str):
        """Aplica search highlight in `App`."""
        qn = _norm(query or "")
        if len(qn) < 2:
            return
        highlight = QBrush(QColor(255, 244, 214))
        cols = [2, 3, 5, 6, 9, 11]
        for r in range(self.table.rowCount()):
            for c in cols:
                it = self.table.item(r, c)
                if not it:
                    continue
                if qn in _norm(it.text() or ""):
                    it.setBackground(highlight)

    def _update_main_table_pager_ui(self, rows_on_page: int):
        """Actualizeaza main table pager interfata in `App`."""
        total = max(0, int(getattr(self, "_main_table_total_rows", 0) or 0))
        pages = max(1, int(getattr(self, "_main_table_total_pages", 1) or 1))
        page_idx = max(0, int(getattr(self, "_main_table_page_index", 0) or 0))
        page_size = max(1, int(getattr(self, "_main_table_page_size", 250) or 250))

        if total <= 0:
            self.lbl_main_page_info.setText("Pagina 1/1 | 0 rezultate")
        else:
            start_idx = page_idx * page_size + 1
            end_idx = min(total, start_idx + max(0, int(rows_on_page)) - 1)
            self.lbl_main_page_info.setText(f"Pagina {page_idx + 1}/{pages} | {start_idx}-{end_idx} din {total}")

        self.btn_main_prev_page.setEnabled(total > 0 and page_idx > 0)
        self.btn_main_next_page.setEnabled(total > 0 and (page_idx + 1) < pages)

    def _go_main_prev_page(self):
        """Gestioneaza main prev page in `App`."""
        if self._main_table_page_index <= 0:
            return
        self._main_table_page_index -= 1
        self.load_table(auto_select_first=False)

    def _go_main_next_page(self):
        """Gestioneaza main next page in `App`."""
        if (self._main_table_page_index + 1) >= self._main_table_total_pages:
            return
        self._main_table_page_index += 1
        self.load_table(auto_select_first=False)

    def _on_main_page_size_changed(self):
        """Gestioneaza evenimentul main page size changed in `App`."""
        try:
            new_size = int(self.cb_main_page_size.currentData() or 0)
        except Exception:
            return
        if new_size <= 0:
            return
        if int(new_size) == int(self._main_table_page_size):
            self._update_main_table_pager_ui(self.table.rowCount())
            return
        self._main_table_page_size = int(new_size)
        self._main_table_page_index = 0
        try:
            set_setting("main_table_page_size", str(int(new_size)))
        except Exception:
            pass
        self.load_table(auto_select_first=False)

    def load_table(self, auto_select_first: bool = True):
        """Incarca pacientii in tabelul principal cu paginare si cautare."""
        q = self.search.text().strip()
        query_signature = q
        if query_signature != self._main_table_query_signature:
            self._main_table_query_signature = query_signature
            self._main_table_page_index = 0

        page_size = max(1, int(self._main_table_page_size))
        offset = max(0, int(self._main_table_page_index) * page_size)
        rows, total_rows = master_list_with_latest_consult_page(
            q,
            limit=page_size,
            offset=offset,
            include_total=True,
        )
        total_pages = max(1, (int(total_rows) + page_size - 1) // page_size)
        if self._main_table_page_index >= total_pages:
            self._main_table_page_index = max(0, total_pages - 1)
            offset = max(0, int(self._main_table_page_index) * page_size)
            rows, total_rows = master_list_with_latest_consult_page(
                q,
                limit=page_size,
                offset=offset,
                include_total=True,
            )
            total_pages = max(1, (int(total_rows) + page_size - 1) // page_size)
        self._main_table_total_rows = max(0, int(total_rows))
        self._main_table_total_pages = max(1, int(total_pages))
        self._last_search_text = q

        self.table.setUpdatesEnabled(False)
        self.table.setSortingEnabled(False)
        self.table.clearContents()
        self.table.setRowCount(len(rows))

        has_alert = False
        for i, r in enumerate(rows):
            self._apply_row_style_and_values(i, dict(r))
            it = self.table.item(i, 0)
            if it and (it.text() or "").strip():
                has_alert = True

        self._apply_search_highlight(q)
        self._cap_table_column_widths()

        self.table.setSortingEnabled(True)
        self.table.setUpdatesEnabled(True)
        self.table.viewport().update()
        self._update_main_table_pager_ui(len(rows))

        if len(rows) > 0 and auto_select_first:
            self.table.selectRow(0)
            self.select_row(0, 0)
        else:
            self.do_clear_form()
            if len(rows) > 0:
                try:
                    self.table.clearSelection()
                except Exception:
                    pass
            self._clear_summary()
        self.table.setColumnHidden(0, not has_alert)

    def _update_alert_column_visibility(self):
        """Actualizeaza alert column visibility in `App`."""
        try:
            has_alert = False
            for r in range(self.table.rowCount()):
                it = self.table.item(r, 0)
                if it and (it.text() or "").strip():
                    has_alert = True
                    break
            self.table.setColumnHidden(0, not has_alert)
        except Exception:
            pass

    def _set_table_rows(self, rows: List[sqlite3.Row]):
        # Used by advanced search result set (non-paginated custom list).
        """Seteaza table rows in `App`."""
        self._main_table_query_signature = None
        self._main_table_page_index = 0
        self._main_table_total_rows = len(rows)
        self._main_table_total_pages = 1
        self.table.setUpdatesEnabled(False)
        self.table.setSortingEnabled(False)
        self.table.clearContents()
        self.table.setRowCount(len(rows))
        has_alert = False
        for i, r in enumerate(rows):
            self._apply_row_style_and_values(i, dict(r))
            it = self.table.item(i, 0)
            if it and (it.text() or "").strip():
                has_alert = True
        try:
            self._apply_search_highlight(self.search.text().strip())
        except Exception:
            pass
        try:
            self._cap_table_column_widths()
        except Exception:
            pass
        self.table.setSortingEnabled(True)
        self.table.setUpdatesEnabled(True)
        self.table.viewport().update()
        self._update_main_table_pager_ui(len(rows))
        if len(rows) > 0:
            self.table.selectRow(0)
            self.select_row(0, 0)
        else:
            self.do_clear_form()
            self._clear_summary()
        self.table.setColumnHidden(0, not has_alert)

    def open_tools_dialog(self):
        """Deschide tools dialog in `App`."""
        def _factory():
            """Construieste instanta de dialog/pagina folosita de deschiderea modeless (helper intern pentru `open_tools_dialog`)."""
            dlg = ToolsDialog(parent=None)
            dlg.btn_periodic.clicked.connect(self.open_periodic_report_dialog)
            dlg.btn_adv_search.clicked.connect(self.open_advanced_search_dialog)
            dlg.btn_stats.clicked.connect(self.open_stats_dialog)
            dlg.btn_kpi.clicked.connect(self.open_kpi_dialog)
            dlg.btn_followup.clicked.connect(self.open_followup_dialog)
            dlg.btn_import_map.clicked.connect(self.import_excel_map_ui)
            dlg.btn_view_import_profile_current.clicked.connect(self.view_current_import_mapping_profile_ui)
            dlg.btn_export_import_profile_current.clicked.connect(self.export_current_import_mapping_profile_ui)
            dlg.btn_reset_import_profile_current.clicked.connect(self.reset_current_import_mapping_profile_ui)
            dlg.btn_reset_import_profiles.clicked.connect(self.reset_import_mapping_profiles_ui)
            dlg.btn_restore.clicked.connect(self.restore_db_ui)
            dlg.btn_log.clicked.connect(self.open_activity_log_dialog)
            dlg.btn_error_log.clicked.connect(self.open_error_log)
            dlg.btn_interop.clicked.connect(self.open_interop_dialog)
            dlg.btn_inventory.clicked.connect(self.open_inventory_dialog)
            dlg.btn_role.clicked.connect(self.open_role_dialog)
            dlg.btn_backup_secure.clicked.connect(self.backup_encrypted_ui)
            dlg.btn_sync_cloud.clicked.connect(self.sync_cloud_ui)
            dlg.btn_sync_cloud_full.clicked.connect(self.sync_cloud_full_resync_ui)
            dlg.btn_sync_status.clicked.connect(self.open_sync_status_dialog)
            dlg.btn_test_supabase.clicked.connect(self.test_supabase_connection_ui)
            dlg.btn_reminders.clicked.connect(self.open_reminders_dialog)
            dlg.btn_clinic.clicked.connect(self.open_clinic_settings)
            dlg.btn_locations.clicked.connect(self.open_locations_dialog)
            dlg.btn_nomenclatoare.clicked.connect(self.open_nomenclatoare_dialog)
            dlg.btn_appt.clicked.connect(self.open_appointments_dialog)
            dlg.btn_wait.clicked.connect(self.open_waiting_list_dialog)
            dlg.btn_tasks.clicked.connect(self.open_tasks_dialog)
            dlg.btn_claims.clicked.connect(self.open_claims_dialog)
            dlg.btn_lab_import.clicked.connect(self.open_lab_import_dialog)
            dlg.btn_dashboard.clicked.connect(self.open_dashboard_dialog)
            dlg.btn_labels.clicked.connect(self.open_labels_dialog)
            dlg.btn_icd10.clicked.connect(self.import_icd10_ui)
            dlg.btn_update_app.clicked.connect(self.check_updates_ui)
            dlg.btn_db_cleanup.clicked.connect(self.cleanup_database_ui)
            dlg.btn_recycle_bin.clicked.connect(self.open_recycle_bin_ui)

            for feature_key, btn_attr in TOOLS_FEATURE_BUTTONS:
                btn = getattr(dlg, btn_attr, None)
                if btn is not None and not is_feature_allowed_for_current_user(feature_key):
                    btn.setEnabled(False)

            role = get_current_role()
            if role != "admin":
                dlg.btn_role.setEnabled(False)
                dlg.btn_inventory.setEnabled(False)
                dlg.btn_restore.setEnabled(False)
                dlg.btn_interop.setEnabled(False)
                dlg.btn_clinic.setEnabled(False)
                dlg.btn_locations.setEnabled(False)
                dlg.btn_backup_secure.setEnabled(False)
                dlg.btn_sync_cloud.setEnabled(False)
                dlg.btn_sync_cloud_full.setEnabled(False)
                dlg.btn_sync_status.setEnabled(False)
                dlg.btn_reminders.setEnabled(False)
                dlg.btn_update_app.setEnabled(False)
                dlg.btn_error_log.setEnabled(False)
                dlg.btn_db_cleanup.setEnabled(False)
                dlg.btn_recycle_bin.setEnabled(False)
            if role not in ("admin", "medic"):
                dlg.btn_kpi.setEnabled(False)
                dlg.btn_stats.setEnabled(False)
                dlg.btn_dashboard.setEnabled(False)
            if role not in ("admin", "receptie"):
                dlg.btn_import_map.setEnabled(False)
                dlg.btn_view_import_profile_current.setEnabled(False)
                dlg.btn_export_import_profile_current.setEnabled(False)
                dlg.btn_reset_import_profile_current.setEnabled(False)
                dlg.btn_reset_import_profiles.setEnabled(False)
                dlg.btn_test_supabase.setEnabled(False)
                dlg.btn_appt.setEnabled(False)
                dlg.btn_wait.setEnabled(False)
                dlg.btn_claims.setEnabled(False)
            return dlg

        self._open_modeless_page("tools", _factory)

    def open_sync_status_dialog(self):
        """Deschide sync status dialog in `App`."""
        dialog = QDialog(self)
        dialog.setWindowTitle("Centru sync")
        dialog.resize(860, 600)

        root = QVBoxLayout(dialog)
        note = QLabel("Status sincronizare, conectivitate si randuri locale in asteptare upload.")
        note.setStyleSheet("color: #4b5563;")
        root.addWidget(note)

        txt = QTextEdit(dialog)
        txt.setReadOnly(True)
        root.addWidget(txt, 1)

        btn_row = QHBoxLayout()
        btn_refresh = QPushButton("Refresh")
        btn_test = QPushButton("Test conexiune")
        btn_sync_now = QPushButton("Sync acum")
        btn_export_json = QPushButton("Export JSON")
        btn_export_csv = QPushButton("Export CSV")
        btn_close = QPushButton("Inchide")
        btn_close.setObjectName("secondary")
        apply_std_icon(btn_refresh, QStyle.StandardPixmap.SP_BrowserReload)
        apply_std_icon(btn_test, QStyle.StandardPixmap.SP_DriveNetIcon)
        apply_std_icon(btn_sync_now, QStyle.StandardPixmap.SP_BrowserReload)
        apply_std_icon(btn_export_json, QStyle.StandardPixmap.SP_DialogSaveButton)
        apply_std_icon(btn_export_csv, QStyle.StandardPixmap.SP_DialogSaveButton)
        apply_std_icon(btn_close, QStyle.StandardPixmap.SP_DialogCloseButton)
        btn_row.addWidget(btn_refresh)
        btn_row.addWidget(btn_test)
        btn_row.addWidget(btn_sync_now)
        btn_row.addStretch(1)
        btn_row.addWidget(btn_export_json)
        btn_row.addWidget(btn_export_csv)
        btn_row.addWidget(btn_close)
        root.addLayout(btn_row)

        center_payload: Dict[str, Any] = {}

        def _collect_sync_center_payload() -> Dict[str, Any]:
            """Gestioneaza sync center payload in `App`, ca helper intern in `open_sync_status_dialog`."""
            raw = (get_setting("sync_last_summary_json", "") or "").strip()
            summary: Dict[str, Any] = {}
            if raw:
                try:
                    tmp = json.loads(raw)
                    if isinstance(tmp, dict):
                        summary = tmp
                except Exception:
                    summary = {}

            last_sync = (get_setting("sync_last_at", "") or "").strip()
            pending = get_sync_pending_upload_counts(last_sync or None)
            try:
                online_ok, online_msg = test_supabase_connectivity(timeout_sec=5)
            except Exception as e:
                online_ok, online_msg = False, str(e)
            return {
                "summary": summary,
                "last_sync": last_sync,
                "pending": pending,
                "online_ok": bool(online_ok),
                "online_msg": str(online_msg or ""),
                "generated_at": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
            }

        def _render_sync_center():
            """Renderizeaza sync center in `App`, ca helper intern in `open_sync_status_dialog`."""
            nonlocal center_payload
            center_payload = _collect_sync_center_payload()
            summary = center_payload.get("summary") if isinstance(center_payload.get("summary"), dict) else {}
            last_sync = str(center_payload.get("last_sync") or "")
            pending = center_payload.get("pending") if isinstance(center_payload.get("pending"), dict) else {}
            pending_tables = pending.get("tables") if isinstance(pending.get("tables"), dict) else {}
            pending_total = int(pending.get("total") or 0)
            online_ok = bool(center_payload.get("online_ok"))
            online_msg = str(center_payload.get("online_msg") or "")

            upload = summary.get("upload") if isinstance(summary.get("upload"), dict) else {}
            download = summary.get("download") if isinstance(summary.get("download"), dict) else {}
            tables = summary.get("tables") if isinstance(summary.get("tables"), list) else []
            if not tables:
                tables = sorted(set(list(upload.keys()) + list(download.keys()) + list(pending_tables.keys())))

            lines: List[str] = []
            lines.append(f"Generat la: {center_payload.get('generated_at') or '-'}")
            lines.append(f"Conectivitate Supabase: {'ONLINE' if online_ok else 'OFFLINE'}")
            if online_msg:
                lines.append(f"Detalii conectivitate: {online_msg}")
            lines.append(f"Ultima sincronizare finalizata: {summary.get('finished_at') or last_sync or '-'}")
            lines.append(f"Ultima pornire sync: {summary.get('started_at') or '-'}")
            lines.append(f"Durata ultima sync: {summary.get('duration_sec', '-')} sec")
            lines.append(f"Upload total ultima rulare: {int(summary.get('upload_total') or 0)} randuri")
            lines.append(f"Download total ultima rulare: {int(summary.get('download_total') or 0)} randuri")
            lines.append(f"Randuri locale in asteptare upload: {pending_total}")
            lines.append("")
            lines.append("Detaliu pe tabele:")
            for table in tables:
                up_cnt = int(upload.get(table) or 0)
                down_cnt = int(download.get(table) or 0)
                pending_cnt = int(pending_tables.get(table) or 0)
                lines.append(f"- {table}: upload_ultim={up_cnt}, download_ultim={down_cnt}, pending_upload={pending_cnt}")

            txt.setPlainText("\n".join(lines))

        def _export_json():
            """Exporta JSON in `App`, ca helper intern in `open_sync_status_dialog`."""
            stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            default_path = str(APP_DIR / f"sync_center_{stamp}.json")
            path, _ = QFileDialog.getSaveFileName(dialog, "Export centru sync (JSON)", default_path, "JSON (*.json)")
            if not path:
                return
            try:
                Path(path).write_text(json.dumps(center_payload, ensure_ascii=False, indent=2), encoding="utf-8")
                QMessageBox.information(dialog, "Centru sync", f"Export JSON salvat:\n{path}")
            except Exception as e:
                QMessageBox.warning(dialog, "Centru sync", f"Nu pot salva JSON:\n{e}")

        def _export_csv():
            """Exporta CSV in `App`, ca helper intern in `open_sync_status_dialog`."""
            stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            default_path = str(APP_DIR / f"sync_center_{stamp}.csv")
            path, _ = QFileDialog.getSaveFileName(dialog, "Export centru sync (CSV)", default_path, "CSV (*.csv)")
            if not path:
                return
            summary = center_payload.get("summary") if isinstance(center_payload.get("summary"), dict) else {}
            pending = center_payload.get("pending") if isinstance(center_payload.get("pending"), dict) else {}
            pending_tables = pending.get("tables") if isinstance(pending.get("tables"), dict) else {}
            upload = summary.get("upload") if isinstance(summary.get("upload"), dict) else {}
            download = summary.get("download") if isinstance(summary.get("download"), dict) else {}
            tables = sorted(set(list(upload.keys()) + list(download.keys()) + list(pending_tables.keys())))
            try:
                with open(path, "w", encoding="utf-8", newline="") as f:
                    writer = csv.writer(f)
                    writer.writerow(["metric", "value"])
                    writer.writerow(["generated_at", center_payload.get("generated_at") or ""])
                    writer.writerow(["online", "1" if center_payload.get("online_ok") else "0"])
                    writer.writerow(["online_msg", center_payload.get("online_msg") or ""])
                    writer.writerow(["last_sync", center_payload.get("last_sync") or ""])
                    writer.writerow(["upload_total", int(summary.get("upload_total") or 0)])
                    writer.writerow(["download_total", int(summary.get("download_total") or 0)])
                    writer.writerow(["pending_upload_total", int(pending.get("total") or 0)])
                    writer.writerow([])
                    writer.writerow(["table", "upload_last", "download_last", "pending_upload"])
                    for table in tables:
                        writer.writerow([table, int(upload.get(table) or 0), int(download.get(table) or 0), int(pending_tables.get(table) or 0)])
                QMessageBox.information(dialog, "Centru sync", f"Export CSV salvat:\n{path}")
            except Exception as e:
                QMessageBox.warning(dialog, "Centru sync", f"Nu pot salva CSV:\n{e}")

        def _run_sync_now():
            """Ruleaza sync now in `App`, ca helper intern in `open_sync_status_dialog`."""
            if QMessageBox.question(
                dialog,
                "Sync cloud",
                "Pornesc sincronizarea cloud acum?",
                QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
                QMessageBox.StandardButton.Yes,
            ) != QMessageBox.StandardButton.Yes:
                return
            dialog.accept()
            self.sync_cloud_ui()

        def _run_connectivity_test():
            """Ruleaza connectivity test in `App`, ca helper intern in `open_sync_status_dialog`."""
            ok, msg = test_supabase_connectivity(timeout_sec=6)
            if ok:
                QMessageBox.information(dialog, "Test conexiune", f"Conexiune OK.\n\n{msg}")
            else:
                QMessageBox.warning(dialog, "Test conexiune", f"Conexiune esuata.\n\n{msg}")
            _render_sync_center()

        btn_refresh.clicked.connect(_render_sync_center)
        btn_test.clicked.connect(_run_connectivity_test)
        btn_sync_now.clicked.connect(_run_sync_now)
        btn_export_json.clicked.connect(_export_json)
        btn_export_csv.clicked.connect(_export_csv)
        btn_close.clicked.connect(dialog.accept)

        _render_sync_center()
        dialog.exec()

    def open_periodic_report_dialog(self):
        """Deschide periodic report dialog in `App`."""
        self._open_modeless_page("periodic_report", lambda: PeriodicReportDialog(parent=None))

    def open_stats_dialog(self):
        """Deschide stats dialog in `App`."""
        self._open_modeless_page("stats", lambda: StatsDialog(parent=None))

    def open_kpi_dialog(self):
        """Deschide kpi dialog in `App`."""
        self._open_modeless_page("kpi", lambda: KpiDialog(parent=None))

    def open_followup_dialog(self):
        """Deschide followup dialog in `App`."""
        self._open_modeless_page("followup", lambda: FollowUpDialog(parent=None))

    def open_activity_log_dialog(self):
        """Deschide activity log dialog in `App`."""
        self._open_modeless_page("activity_log", lambda: ActivityLogDialog(parent=None))

    def open_error_log(self):
        """Deschide error log in `App`."""
        try:
            ERROR_LOG_PATH.parent.mkdir(parents=True, exist_ok=True)
            if not ERROR_LOG_PATH.exists():
                ERROR_LOG_PATH.write_text("", encoding="utf-8")
            QDesktopServices.openUrl(QUrl.fromLocalFile(str(ERROR_LOG_PATH)))
        except Exception as e:
            QMessageBox.warning(self, "Log erori", f"Nu pot deschide logul:\n{e}")

    def open_interop_dialog(self):
        """Deschide interop dialog in `App`."""
        self._open_modeless_page("interop", lambda: InteropDialog(parent=None))

    def open_inventory_dialog(self):
        """Deschide inventory dialog in `App`."""
        self._open_modeless_page("inventory", lambda: InventoryDialog(parent=None))

    def open_role_dialog(self):
        """Deschide role dialog in `App`."""
        if not self._require_sensitive_reauth("Rol/Permisiuni"):
            return
        if get_current_role() != "admin":
            QMessageBox.warning(self, "Permisiuni", "Doar adminul poate modifica roluri si permisiuni.")
            return
        d = RoleDialog(parent=self)
        if d.exec() == QDialog.DialogCode.Accepted:
            user, full_name, role, pwd, active = d.get_values()
            selected_permissions = d.get_selected_permissions()
            if not user:
                return
            if not get_user(user) and not pwd:
                QMessageBox.warning(self, "Utilizator", "Parola este obligatorie pentru utilizator nou.")
                return
            upsert_user(user, pwd if pwd else None, role, active, full_name)
            set_user_allowed_features(user, selected_permissions)
            set_current_user_role(user, role, full_name)
            self._reload_consult_medic_combo()
            self.apply_role_permissions()
            self._set_status_text()
            try:
                log_action("set_role", f"user={user}; role={role}")
            except Exception:
                pass

    def _reload_consult_medic_combo(self):
        """Reincarca consult medic combo in `App`."""
        try:
            w = self.consult_inputs.get("medic")
            if not isinstance(w, QComboBox):
                return
            current = w.currentText().strip()
            w.blockSignals(True)
            w.clear()
            w.addItem("")
            for medic_name in get_medic_dropdown_values():
                w.addItem(medic_name)
            if current:
                idx = w.findText(current)
                if idx < 0:
                    w.addItem(current)
                    idx = w.findText(current)
                if idx >= 0:
                    w.setCurrentIndex(idx)
            w.blockSignals(False)
        except Exception:
            pass

    def open_clinic_settings(self):
        """Deschide clinic settings in `App`."""
        d = ClinicSettingsDialog(parent=self)
        if d.exec() == QDialog.DialogCode.Accepted:
            set_clinic_settings(d.get_values())
            # Refresh app icon if logo was updated
            try:
                global APP_ICON
                APP_ICON = create_app_icon()
                if APP_ICON is not None:
                    QApplication.instance().setWindowIcon(APP_ICON)
                    self.setWindowIcon(APP_ICON)
            except Exception:
                pass
            QMessageBox.information(self, "OK", "Setari clinica salvate.")

    def open_reminders_dialog(self):
        """Deschide reminders dialog in `App`."""
        if not self._require_sensitive_reauth("Remindere automate"):
            return
        d = RemindersDialog(parent=self)
        if d.exec() == QDialog.DialogCode.Accepted:
            enabled, t = d.get_values()
            sms_cfg = d.get_sms_config()
            test_phone = d.get_test_phone()
            scheduler_mode = d.get_scheduler_mode()
            send_rule = d.get_send_rule()
            manual_template_key = d.get_manual_template_key()
            run_interval_min = d.get_run_interval_min()
            retry_max, retry_delay = d.get_retry_config()
            templates = d.get_templates()
            if enabled and scheduler_mode == "fixed_times" and not parse_hhmm_list(t):
                QMessageBox.warning(self, "Ora invalida", "Introdu ore in format HH:MM, separate prin virgula.")
                return
            set_setting("reminder_auto_enabled", "1" if enabled else "0")
            if t:
                set_setting("reminder_times", t)
            set_setting("reminder_scheduler_mode", scheduler_mode)
            set_setting("reminder_send_rule", send_rule)
            set_setting(REMINDER_INTERVAL_MIN_KEY, str(int(run_interval_min)))
            set_setting("reminder_retry_max_attempts", str(int(retry_max)))
            set_setting("reminder_retry_delay_min", str(int(retry_delay)))
            set_setting("reminder_template_default", templates.get("default") or REMINDER_TEMPLATE_DEFAULT)
            set_setting("reminder_template_confirm", templates.get("confirm") or REMINDER_TEMPLATE_CONFIRM)
            set_setting("reminder_template_cancel", templates.get("cancel") or REMINDER_TEMPLATE_CANCEL)
            set_setting("reminder_template_ortopedie", templates.get("ortopedie") or REMINDER_TEMPLATE_ORTOPEDIE)
            set_setting("reminder_template_fizioterapie", templates.get("fizioterapie") or REMINDER_TEMPLATE_FIZIOTERAPIE)
            set_setting("reminder_manual_template_key", manual_template_key)
            set_setting("reminder_sms_provider", "SMSMOBILEAPI")
            set_setting("reminder_smsmobileapi_url", sms_cfg.get("smsmobileapi_url") or "")
            set_setting("reminder_smsmobileapi_api_key", sms_cfg.get("smsmobileapi_api_key") or "")
            set_setting("reminder_smsmobileapi_from", sms_cfg.get("smsmobileapi_from") or "")
            set_setting("reminder_test_phone", test_phone)
            set_setting("reminder_dispatch_mode", "local")
            try:
                if hasattr(self, "reminder_timer") and self.reminder_timer is not None:
                    self.reminder_timer.setInterval(int(max(5, int(run_interval_min)) * 60 * 1000))
            except Exception:
                pass
            QMessageBox.information(self, "OK", "Setari remindere salvate.")

    def open_domiciliu_picker(self):
        """Deschide domiciliu picker in `App`."""
        try:
            pd = QProgressDialog("Pregatesc lista de localitati...", "Anuleaza", 0, 100, self)
            pd.setWindowTitle("Domiciliu")
            pd.setWindowModality(Qt.WindowModality.WindowModal)
            pd.setAutoClose(False)
            pd.setAutoReset(False)
            pd.show()

            def pg(p, m=""):
                """Actualizeaza progresul operatiei in curs (helper intern pentru `open_domiciliu_picker`)."""
                percent = int(max(0, min(100, p)))
                pd.setValue(percent)
                base = str(m).strip() if m else "Pregatesc lista de localitati..."
                pd.setLabelText(f"{base}\n{percent}%")
                QApplication.processEvents()

            ensure_ro_localities_dataset(progress_cb=pg, cancelled_cb=lambda: pd.wasCanceled())
            pd.close()
        except Exception:
            try:
                pd.close()
            except Exception:
                pass

        cur = (self.master_inputs.get("domiciliu").text() or "").strip()
        d = DomiciliuPickerDialog(current_value=cur, parent=self)
        if d.exec() != QDialog.DialogCode.Accepted:
            return
        value = d.get_value().strip()
        if value:
            self.master_inputs["domiciliu"].setText(value)
        self._refresh_domiciliu_autocomplete()

    def open_locations_dialog(self):
        """Deschide locations dialog in `App`."""
        self._open_modeless_page(
            "locations",
            lambda: LocationsDialog(parent=None),
            on_close=self._reload_locations_combo,
        )

    def open_nomenclatoare_dialog(self):
        """Deschide nomenclatoare dialog in `App`."""
        self._open_modeless_page(
            "nomenclatoare",
            lambda: NomenclatoareDialog(parent=None),
            on_close=self._reload_consult_nomenclatoare_combos,
        )

    def _reload_consult_nomenclatoare_combos(self):
        """Reincarca consult nomenclatoare combos in `App`."""
        try:
            for key in CONSULT_NOMENCLATOR_KEYS:
                w = self.consult_inputs.get(key)
                if not isinstance(w, QComboBox):
                    continue
                current = w.currentText().strip()
                w.blockSignals(True)
                w.clear()
                w.addItem("")
                for val in get_nomenclator_values_by_key(key):
                    w.addItem(val)
                if current:
                    idx = w.findText(current)
                    if idx >= 0:
                        w.setCurrentIndex(idx)
                w.blockSignals(False)
        except Exception:
            pass

    def open_appointments_dialog(self):
        """Deschide pagina Programari in fereastra separata modeless."""
        self._open_modeless_page("appointments", lambda: AppointmentsDialog(parent=None))

    def open_waiting_list_dialog(self):
        """Deschide waiting list dialog in `App`."""
        self._open_modeless_page("waiting_list", lambda: WaitingListDialog(parent=None))

    def open_tasks_dialog(self):
        """Deschide tasks dialog in `App`."""
        self._open_modeless_page("tasks", lambda: TasksDialog(parent=None))

    def open_claims_dialog(self):
        """Deschide claims dialog in `App`."""
        self._open_modeless_page("claims", lambda: InsuranceClaimsDialog(parent=None))

    def open_lab_import_dialog(self):
        """Deschide lab import dialog in `App`."""
        self._open_modeless_page("lab_import", lambda: LabImportDialog(parent=None))

    def open_dashboard_dialog(self):
        """Deschide dashboard dialog in `App`."""
        self._open_modeless_page("dashboard", lambda: DashboardDialog(parent=None))

    def open_labels_dialog(self):
        """Deschide labels dialog in `App`."""
        self._open_modeless_page("labels", lambda: LabelsDialog(parent=None))

    def import_icd10_ui(self):
        """Importa ICD10 interfata in `App`."""
        if ICD10_READONLY_LOCAL:
            worker = Worker(sync_icd10_from_supabase, True)

            def done(cnt):
                """Proceseaza finalizarea cu succes a operatiei asincrone (helper intern pentru `import_icd10_ui`)."""
                if int(cnt or 0) <= 0:
                    QMessageBox.information(self, "ICD-10", "Nu s-au gasit coduri in Supabase.")
                else:
                    QMessageBox.information(self, "ICD-10", f"Actualizate {cnt} diagnostice din Supabase.")

            self.run_worker_with_progress("ICD-10", "Descarc ICD-10 din Supabase...", worker, done)
            return
        path, _ = QFileDialog.getOpenFileName(
            self,
            "Import ICD-10 (CSV)",
            str(ICD10_CSV_PATH),
            "CSV (*.csv);;All files (*.*)"
        )
        if not path:
            return
        try:
            cnt = import_icd10_csv(path)
            QMessageBox.information(self, "ICD-10", f"Importate {cnt} diagnostice.")
        except Exception as e:
            QMessageBox.critical(self, "ICD-10", str(e))

    def logout(self):
        """Delogheaza utilizatorul curent si revine la ecranul de autentificare."""
        try:
            log_action("logout", f"user={get_current_user()}")
        except Exception:
            pass
        dlg = LoginDialog(self)
        if dlg.exec() != QDialog.DialogCode.Accepted:
            return
        user_row = dlg.user_row
        if not user_row:
            return
        set_current_user_role(
            user_row.get("username") or DEFAULT_USER,
            user_row.get("role") or DEFAULT_ROLE,
            (user_row.get("full_name") or user_row.get("username") or DEFAULT_USER),
        )
        self._reset_sensitive_session_auth()
        self.apply_role_permissions()
        self._set_status_text()

    def open_advanced_search_dialog(self):
        """Deschide advanced search dialog in `App`."""
        d = AdvancedSearchDialog(parent=self)
        d.exec()

    def apply_advanced_search(self, criteria: dict):
        """Aplica advanced search in `App`."""
        out = filter_master_rows_advanced(criteria)
        self._set_table_rows(out)
        log_action("advanced_search", f"rows={len(out)}")

    def _init_search_completer(self):
        """Initializeaza search completer in `App`."""
        self._search_model = QStringListModel([], self)
        self._search_completer = QCompleter(self._search_model, self)
        self._search_completer.setCaseSensitivity(Qt.CaseSensitivity.CaseInsensitive)
        self._search_completer.setFilterMode(Qt.MatchFlag.MatchContains)
        self._search_completer.setCompletionMode(QCompleter.CompletionMode.PopupCompletion)
        self.search.setCompleter(self._search_completer)
        self._search_completer.activated.connect(self._on_search_suggestion_selected)

        self._search_suggest_timer = QTimer(self)
        self._search_suggest_timer.setInterval(250)
        self._search_suggest_timer.setSingleShot(True)
        self._search_suggest_timer.timeout.connect(self._update_search_suggestions)
        self.search.textChanged.connect(self._schedule_search_suggestions)

    def _init_domiciliu_autocomplete(self):
        """Initializeaza domiciliu autocomplete in `App`."""
        try:
            domic = self.master_inputs.get("domiciliu")
            if not domic:
                return
            self._domiciliu_model = QStringListModel([], self)
            self._domiciliu_completer = QCompleter(self._domiciliu_model, self)
            self._domiciliu_completer.setCaseSensitivity(Qt.CaseSensitivity.CaseInsensitive)
            self._domiciliu_completer.setFilterMode(Qt.MatchFlag.MatchContains)
            self._domiciliu_completer.setCompletionMode(QCompleter.CompletionMode.PopupCompletion)
            domic.setCompleter(self._domiciliu_completer)
            # Defer heavy list population so initial window paint stays responsive.
            QTimer.singleShot(800, self._refresh_domiciliu_autocomplete)
        except Exception:
            pass

    def _refresh_domiciliu_autocomplete(self):
        """Gestioneaza domiciliu autocomplete in `App`."""
        try:
            model = getattr(self, "_domiciliu_model", None)
            if model is None:
                return
            model.setStringList(get_domiciliu_suggestions())
        except Exception:
            try:
                model = getattr(self, "_domiciliu_model", None)
                if model is not None:
                    model.setStringList([])
            except Exception:
                pass

    def _schedule_search_suggestions(self, _txt: str):
        """Gestioneaza search suggestions in `App`."""
        try:
            self._search_suggest_timer.stop()
            self._search_suggest_timer.start()
        except Exception:
            pass

    def _update_search_suggestions(self):
        """Actualizeaza search suggestions in `App`."""
        try:
            q = (self.search.text() or "").strip()
            if not q:
                self._search_model.setStringList([])
                return
            like = f"%{q}%"
            conn = get_conn()
            cur = conn.cursor()
            out = []
            seen = set()

            def add_rows(sql, limit):
                """Adauga rows in `App`, ca helper intern in `_update_search_suggestions`."""
                cur.execute(sql, (like, limit))
                for row in cur.fetchall():
                    v = (row[0] or "").strip()
                    if v and v not in seen:
                        seen.add(v)
                        out.append(v)

            add_rows(
                "SELECT nume_prenume FROM pacienti_master WHERE nume_prenume LIKE ? AND COALESCE(deleted,0)=0 ORDER BY nume_prenume LIMIT ?",
                12,
            )
            add_rows(
                "SELECT cnp FROM pacienti_master WHERE cnp LIKE ? AND COALESCE(deleted,0)=0 ORDER BY cnp LIMIT ?",
                8,
            )
            add_rows(
                "SELECT telefon FROM pacienti_master WHERE telefon LIKE ? AND COALESCE(deleted,0)=0 ORDER BY telefon LIMIT ?",
                8,
            )
            conn.close()
            self._search_model.setStringList(out)
        except Exception:
            try:
                self._search_model.setStringList([])
            except Exception:
                pass

    def _find_patient_ids_for_suggestion(self, text: str) -> List[int]:
        """Cauta patient ID-uri for suggestion in `App`."""
        t = (text or "").strip()
        if not t:
            return []
        digits = normalize_cnp_digits(t)
        cnp = digits if cnp_checksum_valid(digits) else None
        tel = normalize_ro_mobile_phone(t)
        conn = get_conn()
        cur = conn.cursor()
        cur.execute(
            """
            SELECT id FROM pacienti_master
            WHERE (
                (? IS NOT NULL AND TRIM(cnp)=?)
                OR (? IS NOT NULL AND TRIM(telefon)=?)
                OR LOWER(TRIM(nume_prenume)) = LOWER(?)
            )
            AND COALESCE(deleted,0)=0
            LIMIT 5
            """,
            (cnp, cnp, tel, tel, t),
        )
        rows = [int(r[0]) for r in cur.fetchall()]
        conn.close()
        return rows

    def _on_search_suggestion_selected(self, text):
        """Gestioneaza evenimentul search suggestion selected in `App`."""
        try:
            t = (str(text) if text is not None else "").strip()
            if not t:
                return
            self.search.setText(t)
            ids = self._find_patient_ids_for_suggestion(t)
            if len(ids) == 1:
                pid = ids[0]
                QTimer.singleShot(0, lambda pid=pid: self._open_patient_page(pid))
                return

            self.load_table()
            if not ids:
                return

            # daca sunt mai multe potriviri, afiseaza un dialog de selectie
            conn = get_conn()
            cur = conn.cursor()
            cur.execute(
                f"SELECT id, nume_prenume, cnp, telefon, data_nasterii, sex FROM pacienti_master WHERE id IN ({','.join(['?']*len(ids))}) AND COALESCE(deleted,0)=0",
                ids,
            )
            rows = [dict(r) for r in cur.fetchall()]
            conn.close()
            rows.sort(key=lambda x: (x.get("nume_prenume") or "").lower())

            dlg = QDialog(self)
            dlg.setWindowTitle("Selecteaza pacient")
            dlg.resize(720, 420)
            v = QVBoxLayout(dlg)
            v.addWidget(QLabel("Au fost gasite mai multe potriviri. Selecteaza pacientul:"))

            tbl = QTableWidget(0, 6)
            tbl.setHorizontalHeaderLabels(["ID", "Nume", "CNP", "Sex", "Telefon", "Data nasterii"])
            tbl.setEditTriggers(QAbstractItemView.EditTrigger.NoEditTriggers)
            tbl.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
            tbl.setSelectionMode(QAbstractItemView.SelectionMode.SingleSelection)
            tbl.verticalHeader().setDefaultSectionSize(26)
            h = tbl.horizontalHeader()
            h.setSectionResizeMode(QHeaderView.ResizeMode.ResizeToContents)
            tbl.setRowCount(len(rows))
            for i, r in enumerate(rows):
                tbl.setItem(i, 0, QTableWidgetItem(str(r.get("id", ""))))
                tbl.setItem(i, 1, QTableWidgetItem(r.get("nume_prenume") or ""))
                tbl.setItem(i, 2, QTableWidgetItem(r.get("cnp") or ""))
                tbl.setItem(i, 3, QTableWidgetItem(r.get("sex") or ""))
                tbl.setItem(i, 4, QTableWidgetItem(r.get("telefon") or ""))
                tbl.setItem(i, 5, QTableWidgetItem(r.get("data_nasterii") or ""))
            v.addWidget(tbl, 1)

            btns = QDialogButtonBox(QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel)
            try:
                ok_btn = btns.button(QDialogButtonBox.StandardButton.Ok)
                if ok_btn:
                    ok_btn.setText("Selecteaza")
                    apply_std_icon(ok_btn, QStyle.StandardPixmap.SP_DialogOkButton)
                cancel_btn = btns.button(QDialogButtonBox.StandardButton.Cancel)
                if cancel_btn:
                    apply_std_icon(cancel_btn, QStyle.StandardPixmap.SP_DialogCancelButton)
            except Exception:
                pass
            btns.accepted.connect(dlg.accept)
            btns.rejected.connect(dlg.reject)
            v.addWidget(btns)

            if dlg.exec() == QDialog.DialogCode.Accepted:
                row = tbl.currentRow()
                if row >= 0:
                    it = tbl.item(row, 0)
                    if it and it.text().strip().isdigit():
                        pid = int(it.text())
                        QTimer.singleShot(0, lambda pid=pid: self._open_patient_page(pid))
                        return
        except Exception as e:
            try:
                QMessageBox.warning(self, "Cautare", str(e))
            except Exception:
                pass
        self._update_table_fixed_width()

    def _open_patient_page(self, pid: int):
        """Deschide fisa pacientului pentru randul selectat din tabelul principal."""
        open_patient_page_window(
            pid,
            owner=self,
            on_close=lambda pid=pid: self._table_upsert_patient_row(pid),
            on_change=lambda changed_pid: self._table_upsert_patient_row(int(changed_pid)),
        )

    def _update_table_fixed_width(self):
        """Actualizeaza table fixed width in `App`."""
        try:
            if getattr(self, "_table_layout_loaded", False):
                return
            now = time.time()
            last = getattr(self, "_last_col_resize", 0.0)
            if now - last < 0.5:
                return
            self._last_col_resize = now
            self.table.resizeColumnsToContents()
            self._cap_table_column_widths()
        except Exception:
            pass

    def _cap_table_column_widths(self):
        """Gestioneaza table column widths in `App`."""
        try:
            max_w = {
                0: 40,   # alerta
                2: 240,  # nume
                3: 150,  # cnp
                5: 140,  # telefon
                6: 200,  # email
                7: 130,  # data nasterii
                9: 220,  # domiciliu
                10: 120, # ultim consult
                11: 320, # ultim diagnostic
                12: 120, # control
                13: 120, # status
            }
            for col, mw in max_w.items():
                try:
                    if self.table.columnWidth(col) > mw:
                        self.table.setColumnWidth(col, mw)
                except Exception:
                    pass
            try:
                self.table.horizontalHeader().setSectionResizeMode(QHeaderView.ResizeMode.Interactive)
            except Exception:
                pass
        except Exception:
            pass

    def _schedule_save_table_layout(self):
        """Gestioneaza save table layout in `App`."""
        try:
            self._table_layout_timer.start()
        except Exception:
            pass

    def _save_table_layout(self):
        """Salveaza table layout in `App`."""
        try:
            widths = [self.table.columnWidth(i) for i in range(self.table.columnCount())]
            set_setting(self._table_layout_key, json.dumps(widths))
        except Exception:
            pass

    def _load_table_layout(self):
        """Incarca table layout in `App`."""
        try:
            raw = get_setting(self._table_layout_key, "")
            if not raw:
                return
            widths = json.loads(raw)
            if not isinstance(widths, list) or len(widths) != self.table.columnCount():
                return
            for i, w in enumerate(widths):
                try:
                    self.table.setColumnWidth(i, int(w))
                except Exception:
                    pass
            try:
                self.table.horizontalHeader().setSectionResizeMode(QHeaderView.ResizeMode.Interactive)
            except Exception:
                pass
            self._table_layout_loaded = True
        except Exception:
            pass

    def select_row(self, row_idx, _):
        """Selecteaza row in `App`."""
        try:
            self.table.selectRow(row_idx)
            self.table.setCurrentCell(row_idx, 0)
        except Exception:
            pass
        it = self.table.item(row_idx, 1)  # id col
        if not it:
            return
        try:
            pid = int(it.text())
        except Exception:
            return

        m = get_master(pid)
        if m is None:
            self.load_table()
            return

        self.current_id = pid

        # fill master inputs
        for _, k in MASTER_FIELDS:
            v = m[k] if k in m.keys() else None
            w = self.master_inputs[k]
            if k in DATE_KEYS:
                w.setText("" if v is None else str(v))
            elif k == "sms_opt_out" and isinstance(w, QComboBox):
                idx_sms = w.findData(_to_int_flag(v))
                w.setCurrentIndex(idx_sms if idx_sms >= 0 else 0)
            else:
                w.setText("" if v is None else str(v))
        try:
            self._update_summary_from_row(row_idx)
        except Exception:
            pass

    def open_patient_page_on_doubleclick(self, row_idx: int, col_idx: int):
        """Handler dublu-click din tabel pentru deschiderea rapida a fisei."""
        it = self.table.item(row_idx, 1)
        if not it:
            return
        try:
            pid = int(it.text())
        except Exception:
            return
        self._open_patient_page(pid)

    def _update_summary_from_row(self, row_idx: int):
        """Actualizeaza summary from row in `App`."""
        def txt(col: int) -> str:
            """Formateaza textul sumar afisat in panoul principal (helper intern pentru `_update_summary_from_row`)."""
            it = self.table.item(row_idx, col)
            if not it:
                return "-"
            v = (it.text() or "").strip()
            return v if v else "-"

        self.lbl_sum_name.setText(txt(2))
        self.lbl_sum_cnp.setText(txt(3))
        self.lbl_sum_phone.setText(txt(5))
        self.lbl_sum_email.setText(txt(6))
        self.lbl_sum_last.setText(txt(10))
        self.lbl_sum_next.setText(txt(12))

    def _clear_summary(self):
        """Curata summary in `App`."""
        try:
            self.lbl_sum_name.setText("-")
            self.lbl_sum_cnp.setText("-")
            self.lbl_sum_phone.setText("-")
            self.lbl_sum_email.setText("-")
            self.lbl_sum_last.setText("-")
            self.lbl_sum_next.setText("-")
        except Exception:
            pass

    # ---------------- alerts ----------------
    def maybe_show_control_alert(self):
        """Decide daca ruleaza show control alert in `App`."""
        items = get_upcoming_controls(days_ahead=7)
        if not items:
            self._last_alert_signature = None
            return
        sig = "|".join(f"{it['id']}@{it['data_revenire_control']}" for it in items)
        if sig == self._last_alert_signature:
            return
        self._last_alert_signature = sig
        dlg = ControlAlertDialog(items, parent=self)
        dlg.exec()

    # ---------------- duplicate scan in background ----------------
    def scan_duplicates_background(self, progress_cb=None, cancelled_cb=None):
        """Scaneaza duplicates background in `App`."""
        def pg(p, m=""):
            """Actualizeaza progresul operatiei in curs (helper intern pentru `scan_duplicates_background`)."""
            if progress_cb:
                progress_cb(p, m)

        def is_cancelled():
            """Verifica daca cancelled in `App`, ca helper intern in `scan_duplicates_background`."""
            return bool(cancelled_cb and cancelled_cb())

        pg(0, "Caut duplicat CNPâ€¦")
        cnp_groups = find_duplicate_cnp_groups()
        if is_cancelled():
            pg(100, "Anulat.")
            return {"cnp_groups": [], "name_groups": [], "similar_pairs": []}

        pg(35, "Caut nume identicâ€¦")
        name_groups = find_exact_name_groups()
        if is_cancelled():
            pg(100, "Anulat.")
            return {"cnp_groups": [], "name_groups": [], "similar_pairs": []}

        pg(65, "Caut nume similareâ€¦")
        pairs = find_similar_name_pairs(threshold=FUZZY_THRESHOLD, limit=FUZZY_LIMIT)[:FUZZY_MAX_PAIRS]
        if is_cancelled():
            pg(100, "Anulat.")
            return {"cnp_groups": [], "name_groups": [], "similar_pairs": []}

        pg(100, "Gata.")
        return {"cnp_groups": cnp_groups, "name_groups": name_groups, "similar_pairs": pairs}

    def run_duplicate_check_ui(self):
        """Ruleaza duplicate check interfata in `App`."""
        worker = Worker(self.scan_duplicates_background)

        def after_scan(result):
            """Gestioneaza scan in `App`, ca helper intern in `run_duplicate_check_ui`."""
            problems = 0

            for g in result.get("cnp_groups", []):
                if g:
                    problems += 1

            for g in result.get("name_groups", []):
                if len(g) >= 2:
                    ids = [int(x["id"]) for x in g]
                    all_pairs_marked = True
                    for i in range(len(ids)):
                        for j in range(i + 1, len(ids)):
                            if not is_marked_not_duplicate(ids[i], ids[j]):
                                all_pairs_marked = False
                                break
                        if not all_pairs_marked:
                            break
                    if not all_pairs_marked:
                        problems += 1

            for a, b, score in result.get("similar_pairs", []):
                pid_a = int(a["id"])
                pid_b = int(b["id"])
                if not is_marked_not_duplicate(pid_a, pid_b):
                    problems += 1
                    break

            if problems == 0:
                QMessageBox.information(self, "OK", "Nu am gasit duplicari / similitudini conform regulilor.")
            else:
                QMessageBox.information(
                    self, "Rezultat",
                    f"Au fost gasite posibile duplicari/similitudini.\n"
                    f"- CNP duplicat: {len(result.get('cnp_groups', []))}\n"
                    f"- Nume identic: {len(result.get('name_groups', []))}\n"
                    f"- Nume similare: {len(result.get('similar_pairs', []))}\n\n"
                    f"Sfat: deschide fisa pacientului (dublu click pe nume) si corecteaza CNP/nume daca e cazul."
                )

            self._set_status_dupcheck()
            self._set_status_text()

        self.run_worker_with_progress("Verificare Duplicat", "Verific duplicateleâ€¦", worker, after_scan)

    # ---------------- Recalc ages UI ----------------
    def recalc_ages_ui(self):
        """Gestioneaza ages interfata in `App`."""
        if not self.ask_yes_no("Confirmare", "Recalculez varstele si sexul (din CNP) pentru toti pacientiiT"):
            return

        worker = Worker(job_recalc_ages)

        def done(res):
            """Proceseaza finalizarea cu succes a operatiei asincrone (helper intern pentru `recalc_ages_ui`)."""
            self.load_table()
            QMessageBox.information(
                self, "OK",
                "Recalculare finalizata.\n"
                f"Actualizate: {res.get('updated', 0)}\n"
                f"Data nasterii derivata: {res.get('derived_dn', 0)}\n"
                f"Sex derivat: {res.get('derived_sex', 0)}\n"
                f"Fara date valide: {res.get('invalid', 0)}"
            )
            self.mark_dirty_and_schedule_backup("after_recalc_ages")

        self.run_worker_with_progress("Recalculeaza varstele", "Recalculezâ€¦", worker, done)

    def show_avg_age_dialog(self):
        """Afiseaza avg age dialog in `App`."""
        dlg = AvgAgeByCategoryDialog(parent=self)
        dlg.exec()

    def _auto_send_consult_confirmation_sms(self, pid: int, consult_payload: Optional[Dict[str, Any]] = None):
        """Trimite automat SMS de confirmare dupa salvarea consultului din pagina principala."""
        try:
            patient_id = int(pid or 0)
        except Exception:
            return
        if patient_id <= 0:
            return

        try:
            m = get_master(patient_id)
        except Exception:
            m = None
        if m is None:
            return

        if _to_int_flag(m["sms_opt_out"] if "sms_opt_out" in m.keys() else 0) == 1:
            try:
                log_action("auto_consult_sms_skipped", f"pid={patient_id}; reason=sms_disabled")
            except Exception:
                pass
            return

        phone_raw = (m["telefon"] if "telefon" in m.keys() else "") or ""
        phone = normalize_ro_mobile_phone(phone_raw) or str(phone_raw).strip()
        if not phone:
            try:
                log_action("auto_consult_sms_skipped", f"pid={patient_id}; reason=missing_phone")
            except Exception:
                pass
            return

        cp = dict(consult_payload or {})
        slot = _consult_confirmation_slot(cp)
        if not slot:
            try:
                log_action("auto_consult_sms_skipped", f"pid={patient_id}; reason=missing_control_date")
            except Exception:
                pass
            return
        consult_date, consult_time = slot
        medic_name = (cp.get("medic") or "").strip() or "medic"

        clinic = get_clinic_settings()
        clinic_name = (clinic.get("clinic_name") or "Clinica").strip() or "Clinica"
        contact = (clinic.get("clinic_phone") or "").strip() or clinic_name
        templates = _get_reminder_templates()
        template = templates.get("confirm") or REMINDER_TEMPLATE_CONFIRM

        ctx = {
            "nume_prenume": (m["nume_prenume"] if "nume_prenume" in m.keys() else "") or "",
            "date": consult_date,
            "time": consult_time,
            "medic": medic_name,
            "location": clinic_name,
            "status": "Confirmat",
            "contact": contact,
        }
        msg = render_template_text(template, ctx)
        msg = re.sub(r"\s+", " ", (msg or "").strip())
        if not msg:
            msg = f"Programarea dvs este confirmata: {consult_date}, medic {medic_name}. {contact}"

        sms_cfg = build_sms_gateway_runtime_config()

        def _set_transient_async(text: str, seconds: int = 4):
            """Seteaza transient async in `App`, ca helper intern in `_auto_send_consult_confirmation_sms`."""
            def _apply():
                """Gestioneaza operatia `_apply` in `App`."""
                try:
                    self._set_transient_status(text, seconds=seconds)
                except Exception:
                    pass
            try:
                QTimer.singleShot(0, _apply)
            except Exception:
                pass

        def _run_send():
            """Ruleaza send in `App`, ca helper intern in `_auto_send_consult_confirmation_sms`."""
            try:
                res = _send_sms_with_retry(
                    phone,
                    msg,
                    sms_config=sms_cfg,
                    cancelled_cb=None,
                )
                attempts = 1
                if isinstance(res, dict):
                    try:
                        attempts = int(res.get("attempt", 1) or 1)
                    except Exception:
                        attempts = 1
                try:
                    log_action(
                        "auto_consult_sms_sent",
                        f"pid={patient_id}; phone={phone}; date={consult_date}; medic={medic_name}; attempts={attempts}",
                    )
                except Exception:
                    pass
                _set_transient_async("SMS confirmare trimis automat.", seconds=4)
            except Exception as e:
                try:
                    log_action(
                        "auto_consult_sms_failed",
                        f"pid={patient_id}; phone={phone}; err={str(e)}",
                    )
                except Exception:
                    pass
                _set_transient_async("SMS confirmare automata esuata.", seconds=6)

        try:
            threading.Thread(target=_run_send, daemon=True).start()
        except Exception:
            pass

    # ---------------- actions ----------------
    def save_consult(self):
        """Salveaza consult nou sau update de pacient din formularul principal."""
        master_payload = self.master_payload_from_form()
        consult_payload = self.consult_payload_from_form()

        err = self.validate_master(master_payload) or self.validate_consult(consult_payload)
        if err:
            QMessageBox.warning(self, "Date invalide", err)
            return

        master_payload = self.confirm_or_drop_invalid_phone(master_payload)
        if master_payload is None:
            return

        master_payload = self.confirm_or_drop_invalid_cnp(master_payload)
        if master_payload is None:
            return
        master_payload = self.confirm_cnp_sex_consistency(master_payload)
        if master_payload is None:
            return

        cnp = (master_payload.get("cnp") or "").strip()
        name = (master_payload.get("nume_prenume") or "").strip()

        try:
            # 1) CNP identic -> update master + add consult
            existing = find_master_by_cnp(cnp) if cnp else None
            if existing is not None:
                pid = int(existing["id"])
                merged = dict(existing)
                for _, k in MASTER_FIELDS:
                    nv = master_payload.get(k)
                    if nv:
                        merged[k] = nv
                merged = normalize_master_from_cnp(merged)

                update_master_and_insert_consult(pid, merged, consult_payload)

                self.mark_dirty_and_schedule_backup("after_insert_consult_existing_cnp")
                QMessageBox.information(self, "OK", "Consult adaugat la pacient existent (CNP identic).")
                self.current_id = pid
                self._table_upsert_patient_row(pid)
                self.maybe_show_control_alert()
                log_action("add_consult_existing_cnp", f"pid={pid}")
                self._auto_send_consult_confirmation_sms(pid, consult_payload)
                self.do_clear_form(clear_draft=True)
                return

            # 2) Nume identic -> dialog
            candidates = find_master_by_exact_name(name)
            if candidates:
                d = DuplicateNameResolutionDialog(master_payload, consult_payload, candidates, parent=self)
                if d.exec() == QDialog.DialogCode.Accepted:
                    if d.result_action == "merge":
                        pid = int(d.selected_target_id)
                        if d.corrected_master_payload:
                            m = get_master(pid)
                            mp = dict(m) if m else {}
                            mp["nume_prenume"] = d.corrected_master_payload.get("nume_prenume") or mp.get("nume_prenume")
                            mp["cnp"] = d.corrected_master_payload.get("cnp") or mp.get("cnp")
                            mp["telefon"] = d.corrected_master_payload.get("telefon") or mp.get("telefon")
                            mp["data_nasterii"] = d.corrected_master_payload.get("data_nasterii") or mp.get("data_nasterii")
                            if master_payload.get("domiciliu"):
                                mp["domiciliu"] = master_payload.get("domiciliu")
                            mp = normalize_master_from_cnp(mp)
                            update_master_and_insert_consult(pid, mp, consult_payload)
                        else:
                            insert_consult(pid, consult_payload)

                        self.mark_dirty_and_schedule_backup("after_merge_by_name")
                        QMessageBox.information(self, "OK", "Consult adaugat la pacient selectat (nume identic).")
                        self.current_id = pid
                        self._table_upsert_patient_row(pid)
                        self.maybe_show_control_alert()
                        log_action("add_consult_merge_name", f"pid={pid}")
                        self._auto_send_consult_confirmation_sms(pid, consult_payload)
                        self.do_clear_form(clear_draft=True)
                        return

                    elif d.result_action == "new":
                        pid = insert_master_and_consult(master_payload, consult_payload)

                        self.mark_dirty_and_schedule_backup("after_new_from_name_dialog")
                        QMessageBox.information(self, "OK", "Pacient nou creat + consult adaugat.")
                        self.current_id = pid
                        self._table_upsert_patient_row(pid)
                        self.maybe_show_control_alert()
                        log_action("add_consult_new_from_name", f"pid={pid}")
                        self._auto_send_consult_confirmation_sms(pid, consult_payload)
                        self.do_clear_form(clear_draft=True)
                        return
                else:
                    return

            # 3) pacient nou
            pid = insert_master_and_consult(master_payload, consult_payload)

            self.mark_dirty_and_schedule_backup("after_new_master_and_consult")
            QMessageBox.information(self, "OK", "Pacient nou creat + consult adaugat.")
            self.current_id = pid
            self._table_upsert_patient_row(pid)
            self.maybe_show_control_alert()
            log_action("add_consult_new", f"pid={pid}")
            self._auto_send_consult_confirmation_sms(pid, consult_payload)
            self.do_clear_form(clear_draft=True)

        except Exception as e:
            QMessageBox.critical(self, "Eroare", str(e))

    def update_master_ui(self):
        """Actualizeaza pacientul selectat pe baza campurilor din formular."""
        if self.current_id is None:
            QMessageBox.warning(self, "Editare", "Selecteaza un pacient din lista.")
            return
        payload = self.master_payload_from_form()
        err = self.validate_master(payload)
        if err:
            QMessageBox.warning(self, "Date invalide", err)
            return

        payload = self.confirm_or_drop_invalid_phone(payload)
        if payload is None:
            return

        payload = self.confirm_or_drop_invalid_cnp(payload)
        if payload is None:
            return
        payload = self.confirm_cnp_sex_consistency(payload)
        if payload is None:
            return

        try:
            payload = normalize_master_from_cnp(payload)
            update_master(self.current_id, payload)
            self.mark_dirty_and_schedule_backup("after_update_master")
            QMessageBox.information(self, "OK", "Date pacient actualizate.")
            self._table_upsert_patient_row(self.current_id)
            log_action("update_master", f"pid={self.current_id}")
            self.do_clear_form(clear_draft=True)
        except Exception as e:
            QMessageBox.critical(self, "Eroare", str(e))

    def delete_master_ui(self):
        """Sterge pacientul selectat cu validari si confirmare in UI."""
        if self.current_id is None:
            QMessageBox.warning(self, "Stergere", "Selecteaza un pacient din lista.")
            return
        if not self.ask_yes_no("Confirmare", "Stergi pacientul si TOT istoricul consulturilorT"):
            return
        pid = self.current_id
        try:
            delete_master(pid)
            self.mark_dirty_and_schedule_backup("after_delete_master")
            QMessageBox.information(self, "OK", "Pacient sters.")
            self._table_remove_patient_row(pid)
            self.do_clear_form(clear_draft=True)
            self.maybe_show_control_alert()
            log_action("delete_master", f"pid={pid}")
        except Exception as e:
            QMessageBox.critical(self, "Eroare", str(e))

    # ---------------- import/export/backup threaded ----------------
    def import_excel_ui(self):
        """Importa excel interfata in `App`."""
        path, _ = QFileDialog.getOpenFileName(
            self,
            "Alege fisier tabel",
            "",
            "Fisiere tabel (*.xlsx *.xls *.csv *.tsv);;Excel (*.xlsx *.xls);;CSV (*.csv);;TSV (*.tsv)",
        )
        if not path:
            return

        try:
            df = _prepare_tabular_df_for_import(_read_tabular_dataframe(path))
        except Exception as e:
            QMessageBox.critical(self, "Import tabel", f"Eroare la citire:\n{e}")
            return

        columns = [str(c) for c in df.columns]
        self._last_import_profile_key = _import_profile_key(columns)
        self._last_import_profile_columns = list(columns)
        mapping, scores = auto_map_tabular_columns(columns)
        saved_mapping = load_import_mapping_profile(columns)
        if saved_mapping:
            for k, v in saved_mapping.items():
                mapping[k] = v

        def run_import_with_mapping(mp: dict, mode: str):
            """Ruleaza import with mapping in `App`, ca helper intern in `import_excel_ui`."""
            worker = Worker(import_from_excel_mapping, path, mp)

            def after_import(res):
                """Gestioneaza import in `App`, ca helper intern in `run_import_with_mapping`."""
                inserted, skipped = res
                save_import_mapping_profile(columns, mp)
                self.mark_dirty_and_schedule_backup("after_import_excel_threaded")
                QMessageBox.information(self, "Import finalizat", f"Consulturi importate: {inserted}\nSarite: {skipped}")
                self.load_table()
                self.maybe_show_control_alert()
                self._set_status_import()
                self._set_status_text()
                log_action(
                    "import_tabular_auto" if mode == "auto" else "import_tabular_manual_fallback",
                    f"inserted={inserted}; skipped={skipped}; mapped={len([k for k,v in mp.items() if v])}",
                )

            self.run_worker_with_progress("Import tabel", "Import tabel...", worker, after_import)

        if not mapping.get("nume_prenume"):
            go_manual = self.ask_yes_no(
                "Mapare necesara",
                "Nu am putut detecta automat coloana pentru 'Nume si prenume'.\n"
                "Vrei sa alegi manual maparea coloanelor?",
            )
            if not go_manual:
                return
            dlg = ImportMapDialog(columns, parent=self)
            if dlg.exec() != QDialog.DialogCode.Accepted or not dlg.mapping:
                return
            run_import_with_mapping(dlg.mapping, mode="manual")
            return

        mapped_keys = [k for k, v in mapping.items() if v]
        missing_optional = [k for _, k in MASTER_FIELDS + CONSULT_FIELDS if k not in mapping]
        msg = (
            "Import automat din fisier tabelar (fara template fix).\n\n"
            f"Coloane detectate: {len(mapped_keys)} din {len(MASTER_FIELDS) + len(CONSULT_FIELDS)}\n"
            f"Camp obligatoriu detectat: nume_prenume ({mapping.get('nume_prenume')})"
        )
        if missing_optional:
            msg += "\n\nCampuri nedetectate (optionale):\n- " + "\n- ".join(missing_optional)
        high_conf = [k for k, sc in scores.items() if sc >= 0.90]
        if high_conf:
            msg += f"\n\nMapari cu incredere mare: {len(high_conf)}"
        if saved_mapping:
            msg += f"\n\nProfil mapare salvat folosit: {len([k for k, v in saved_mapping.items() if v])} campuri"

        if not self.ask_yes_no("Confirmare import", msg):
            return

        run_import_with_mapping(mapping, mode="auto")

    def import_excel_map_ui(self):
        """Importa excel map interfata in `App`."""
        path, _ = QFileDialog.getOpenFileName(
            self,
            "Alege fisier tabel",
            "",
            "Fisiere tabel (*.xlsx *.xls *.csv *.tsv);;Excel (*.xlsx *.xls);;CSV (*.csv);;TSV (*.tsv)",
        )
        if not path:
            return
        try:
            df = _prepare_tabular_df_for_import(_read_tabular_dataframe(path))
        except Exception as e:
            QMessageBox.critical(self, "Import tabel", f"Eroare la citire:\n{e}")
            return

        cols = list(df.columns)
        self._last_import_profile_key = _import_profile_key(cols)
        self._last_import_profile_columns = [str(c) for c in cols]
        dlg = ImportMapDialog(cols, parent=self)
        if dlg.exec() != QDialog.DialogCode.Accepted or not dlg.mapping:
            return

        worker = Worker(import_from_excel_mapping, path, dlg.mapping)

        def after_import(res):
            """Gestioneaza import in `App`, ca helper intern in `import_excel_map_ui`."""
            inserted, skipped = res
            save_import_mapping_profile(cols, dlg.mapping or {})
            self.mark_dirty_and_schedule_backup("after_import_excel_mapping")
            QMessageBox.information(self, "Import finalizat", f"Consulturi importate: {inserted}\nSarite: {skipped}")
            self.load_table()
            self.maybe_show_control_alert()
            self._set_status_import()
            self._set_status_text()
            log_action("import_tabular_mapping", f"inserted={inserted}; skipped={skipped}")

        self.run_worker_with_progress("Import tabel", "Import tabel (mapare)...", worker, after_import)

    def reset_import_mapping_profiles_ui(self):
        """Gestioneaza import mapping profiles interfata in `App`."""
        if not self.ask_yes_no(
            "Confirmare",
            "Sterg toate profilele salvate pentru maparea importului Excel/CSV?",
        ):
            return
        removed = delete_settings_by_prefix("import_mapping_profile::")
        QMessageBox.information(self, "Reset mapari", f"Profile sterse: {removed}")
        try:
            log_action("reset_import_mapping_profiles", f"removed={removed}")
        except Exception:
            pass

    def reset_current_import_mapping_profile_ui(self):
        """Gestioneaza current import mapping profile interfata in `App`."""
        key = getattr(self, "_last_import_profile_key", "") or ""
        if not key:
            QMessageBox.information(
                self,
                "Reset mapare curenta",
                "Nu exista profil curent in memorie.\nImporta mai intai un fisier Excel/CSV.",
            )
            return
        sig, col_cnt = _parse_import_profile_key(key)
        cols_preview = [str(c) for c in (getattr(self, "_last_import_profile_columns", []) or []) if str(c).strip()]
        msg = "Sterg doar profilul curent de mapare import?"
        if sig:
            short_sig = sig[:12]
            msg += f"\n\nSemnatura: {short_sig}...\nNumar coloane: {col_cnt}"
        if cols_preview:
            preview_txt = ", ".join(cols_preview[:5])
            if len(cols_preview) > 5:
                preview_txt += ", ..."
            msg += f"\nPrimele coloane: {preview_txt}"
        if not self.ask_yes_no("Confirmare", msg):
            return
        removed = delete_setting(key)
        QMessageBox.information(
            self,
            "Reset mapare curenta",
            "Profilul curent a fost sters." if removed else "Profilul curent nu exista deja.",
        )
        try:
            log_action("reset_current_import_mapping_profile", f"removed={1 if removed else 0}")
        except Exception:
            pass

    def view_current_import_mapping_profile_ui(self):
        """Gestioneaza current import mapping profile interfata in `App`."""
        key = getattr(self, "_last_import_profile_key", "") or ""
        cols_preview = [str(c) for c in (getattr(self, "_last_import_profile_columns", []) or []) if str(c).strip()]
        if not key:
            QMessageBox.information(
                self,
                "Mapare curenta",
                "Nu exista profil curent in memorie.\nImporta mai intai un fisier Excel/CSV.",
            )
            return

        raw = get_setting(key, "") or ""
        try:
            mp = json.loads(raw) if raw else {}
        except Exception:
            mp = {}
        if not isinstance(mp, dict):
            mp = {}

        sig, col_cnt = _parse_import_profile_key(key)
        lines = ["Profil curent de mapare import:"]
        if sig:
            lines.append(f"- Semnatura: {sig[:12]}...")
        if col_cnt:
            lines.append(f"- Numar coloane: {col_cnt}")
        if cols_preview:
            preview_txt = ", ".join(cols_preview[:5])
            if len(cols_preview) > 5:
                preview_txt += ", ..."
            lines.append(f"- Primele coloane: {preview_txt}")

        mapped_items = [(k, v) for k, v in mp.items() if v]
        if mapped_items:
            lines.append("")
            lines.append("Mapare salvata:")
            for k, v in sorted(mapped_items):
                lines.append(f"- {k} -> {v}")
        else:
            lines.append("")
            lines.append("Nu exista mapare salvata pentru acest profil.")

        QMessageBox.information(self, "Mapare curenta", "\n".join(lines))

    def export_current_import_mapping_profile_ui(self):
        """Exporta current import mapping profile interfata in `App`."""
        key = getattr(self, "_last_import_profile_key", "") or ""
        cols_preview = [str(c) for c in (getattr(self, "_last_import_profile_columns", []) or []) if str(c).strip()]
        if not key:
            QMessageBox.information(
                self,
                "Export mapare",
                "Nu exista profil curent in memorie.\nImporta mai intai un fisier Excel/CSV.",
            )
            return

        raw = get_setting(key, "") or ""
        try:
            mp = json.loads(raw) if raw else {}
        except Exception:
            mp = {}
        if not isinstance(mp, dict):
            mp = {}

        sig, col_cnt = _parse_import_profile_key(key)
        suggested = f"import_map_{(sig[:12] if sig else 'current')}.json"
        dest, _ = QFileDialog.getSaveFileName(
            self,
            "Export mapare curenta",
            str(APP_DIR / suggested),
            "JSON (*.json)",
        )
        if not dest:
            return

        payload = {
            "profile_key": key,
            "signature": sig,
            "column_count": col_cnt,
            "columns_preview": cols_preview,
            "mapping": mp,
            "exported_at": now_ts(),
        }

        try:
            Path(dest).write_text(json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8")
            QMessageBox.information(self, "Export mapare", f"Maparea curenta a fost exportata in:\n{dest}")
            log_action("export_current_import_mapping_profile", dest)
        except Exception as e:
            QMessageBox.critical(self, "Export mapare", f"Eroare la salvare:\n{e}")

    def export_csv_ui(self):
        """Exporta CSV interfata in `App`."""
        if not self._require_sensitive_reauth("Export CSV"):
            return
        dest, _ = QFileDialog.getSaveFileName(
            self, "Export CSV", str(APP_DIR / "pacienti_export.csv"), "CSV (*.csv)"
        )
        if not dest:
            return

        worker = Worker(job_export_csv, dest)

        def done(_):
            """Proceseaza finalizarea cu succes a operatiei asincrone (helper intern pentru `export_csv_ui`)."""
            QMessageBox.information(self, "OK", f"CSV creat:\n{dest}")
            self._set_status_export()
            self._set_status_text()
            log_action("export_csv", dest)

        self.run_worker_with_progress("Export CSV", "Export CSVâ€¦", worker, done)

    def backup_db(self):
        """Creeaza backup pentru baza de date in `App`."""
        if not self._require_sensitive_reauth("Backup DB"):
            return
        dest, _ = QFileDialog.getSaveFileName(
            self, "Salveaza backup DB", str(APP_DIR / "pacienti_backup.db"), "SQLite DB (*.db)"
        )
        if not dest:
            return

        worker = Worker(job_backup_db, dest)

        def done(_):
            """Proceseaza finalizarea cu succes a operatiei asincrone (helper intern pentru `backup_db`)."""
            QMessageBox.information(self, "OK", f"Backup creat:\n{dest}")
            self._set_status_backup()
            self._set_status_text()
            log_action("backup_db", dest)

        self.run_worker_with_progress("Backup DB", "Creez backup...", worker, done)

    def backup_encrypted_ui(self):
        """Creeaza backup pentru encrypted interfata in `App`."""
        if not self._require_sensitive_reauth("Backup securizat"):
            return
        dest, _ = QFileDialog.getSaveFileName(
            self, "Backup securizat", str(APP_DIR / "pacienti_backup.enc"), "Encrypted (*.enc)"
        )
        if not dest:
            return
        pwd, ok = QInputDialog.getText(self, "Parola", "Introdu parola pentru criptare:")
        if not ok or not pwd:
            return
        try:
            tmp = APP_DIR / "tmp_backup.db"
            export_db_copy_atomic(str(tmp))
            data = Path(tmp).read_bytes()
            enc = encrypt_bytes(data, pwd)
            Path(dest).write_bytes(enc)
            try:
                tmp.unlink()
            except Exception:
                pass
            QMessageBox.information(self, "OK", f"Backup securizat creat:\n{dest}")
            log_action("backup_encrypted", dest)
        except Exception as e:
            QMessageBox.critical(
                self,
                "Eroare",
                f"Criptarea nu este disponibila.\nInstaleaza: pip install cryptography\n\nDetalii: {e}",
            )

    def sync_cloud_ui(self):
        """Porneste sincronizarea cloud standard si afiseaza progresul in UI."""
        if not SUPABASE_URL or not SUPABASE_ANON_KEY:
            QMessageBox.warning(self, "Sync cloud", "Supabase nu este configurat.")
            return

        self._set_sync_label("Sync: in curs", "#f59e0b")
        worker = Worker(sync_all)

        def done(_):
            """Proceseaza finalizarea cu succes a operatiei asincrone (helper intern pentru `sync_cloud_ui`)."""
            self._set_transient_status("Sync cloud terminata", seconds=4)
            self._set_status_sync()
            self._set_status_text()
            try:
                log_action("sync_cloud", "manual")
            except Exception:
                pass

        self.run_worker_with_progress("Sync cloud", "Sincronizare cloud...", worker, done)

    def sync_cloud_full_resync_ui(self):
        """Porneste full re-sync cloud, inclusiv download complet."""
        if not self._require_sensitive_reauth("Full re-sync cloud"):
            return
        if not SUPABASE_URL or not SUPABASE_ANON_KEY:
            QMessageBox.warning(self, "Full re-sync cloud", "Supabase nu este configurat.")
            return

        msg = (
            "Se va rula re-sincronizare completa DIN CLOUD (download-only).\n"
            "- Nu trimite upload local catre Supabase.\n"
            "- Suprascrie local doar randurile existente in cloud cu acelasi sync_id.\n\n"
            "Aplicatia va crea backup local inainte de operatie. Continui?"
        )
        if not self.ask_yes_no("Full re-sync cloud", msg):
            return

        backup_path = ""
        try:
            ts = datetime.now().strftime("%Y-%m-%d_%H%M%S")
            backup = APP_DIR / f"backup_before_full_resync_{ts}.db"
            shutil.copy2(DB_PATH, backup)
            backup_path = str(backup)
        except Exception:
            backup_path = ""

        self._set_sync_label("Sync: full re-sync in curs", "#f59e0b")
        worker = Worker(sync_download_all_from_cloud)

        def done(res):
            """Proceseaza finalizarea cu succes a operatiei asincrone (helper intern pentru `sync_cloud_full_resync_ui`)."""
            try:
                self.load_table()
            except Exception:
                pass
            self._set_status_sync()
            self._set_status_text()
            self._set_sync_label("Sync: OK", "#16a34a")
            self._set_transient_status("Full re-sync cloud finalizat", seconds=5)
            try:
                log_action("sync_cloud_full_resync", json.dumps({"backup": backup_path}, ensure_ascii=False))
            except Exception:
                pass

            summary = (res or {}).get("summary") if isinstance(res, dict) else {}
            total = int((summary or {}).get("download_total") or 0)
            text = f"Full re-sync cloud finalizat.\nRanduri descarcate: {total}"
            if backup_path:
                text += f"\nBackup local: {backup_path}"
            QMessageBox.information(self, "Full re-sync cloud", text)

        self.run_worker_with_progress(
            "Full re-sync cloud",
            "Descarc toate datele din cloud...",
            worker,
            done,
        )

    def sync_cloud_silent(self):
        """Sincronizeaza cloud silent in `App`."""
        if not SUPABASE_URL or not SUPABASE_ANON_KEY:
            return
        if self._sync_in_progress:
            return
        self._sync_in_progress = True
        self._set_sync_label("Sync: in curs", "#f59e0b")

        worker = Worker(sync_all)
        thread = QThread(self)
        worker.moveToThread(thread)

        def cleanup():
            """Curata resursele temporare folosite de operatia curenta (helper intern pentru `sync_cloud_silent`)."""
            try:
                thread.quit()
                thread.wait()
            except Exception:
                pass
            self._sync_in_progress = False

        def on_finished(_):
            """Gestioneaza evenimentul finished in `App`, ca helper intern in `sync_cloud_silent`."""
            cleanup()
            self._set_status_sync()
            self._set_status_text()
            self._set_sync_label("Sync: OK", "#16a34a")

        def on_error(msg):
            """Gestioneaza evenimentul error in `App`, ca helper intern in `sync_cloud_silent`."""
            cleanup()
            self._set_transient_status(f"Sync cloud esuat: {msg}", seconds=6)
            self._set_sync_label("Sync: eroare", "#dc2626")

        worker.finished.connect(on_finished)
        worker.error.connect(on_error)
        thread.started.connect(worker.run)
        thread.start()

    def send_reminders_now(
        self,
        silent: bool = True,
        sms_config: Optional[Dict[str, Any]] = None,
        dispatch_mode: Optional[str] = None,
        trigger_dt: Optional[datetime] = None,
        force_template_key: Optional[str] = None,
    ):
        """Ruleaza manual jobul de remindere automate din interfata principala."""
        if self._reminder_job_in_progress:
            return
        self._reminder_job_in_progress = True
        runtime_sms_config = dict(sms_config or build_sms_gateway_runtime_config())
        mode = (dispatch_mode or build_reminder_dispatch_mode() or "local").strip() or "local"
        rule = _get_reminder_rule()
        trigger_at = trigger_dt or datetime.now()

        def done(res):
            """Proceseaza finalizarea cu succes a operatiei asincrone (helper intern pentru `send_reminders_now`)."""
            self._reminder_job_in_progress = False
            try:
                set_setting("reminder_last_run_date", datetime.now().strftime("%Y-%m-%d"))
                _set_reminder_last_run_at(datetime.now())
            except Exception:
                pass
            if not silent:
                QMessageBox.information(self, "Remindere", f"OK:\n{res}")
            self._set_transient_status("Remindere trimise", seconds=4)

        def on_error(msg):
            """Gestioneaza evenimentul error in `App`, ca helper intern in `send_reminders_now`."""
            self._reminder_job_in_progress = False
            if not silent:
                QMessageBox.critical(self, "Remindere", msg)
            else:
                self._set_transient_status(f"Remindere esuate: {msg}", seconds=6)

        if not silent:
            worker = Worker(
                send_reminders_job_local,
                runtime_sms_config,
                trigger_dt=trigger_at,
                dispatch_rule=rule,
                force_template_key=force_template_key,
            )
            worker.error.connect(lambda _msg: setattr(self, "_reminder_job_in_progress", False))
            worker.cancelled.connect(lambda: setattr(self, "_reminder_job_in_progress", False))
            self.run_worker_with_progress("Remindere", "Trimit remindere...", worker, done)
            return

        worker = Worker(
            send_reminders_job_local,
            runtime_sms_config,
            trigger_dt=trigger_at,
            dispatch_rule=rule,
            force_template_key=force_template_key,
        )

        worker.error.connect(on_error)
        worker.finished.connect(done)
        thread = QThread(self)
        worker.moveToThread(thread)
        thread.started.connect(worker.run)

        def cleanup():
            """Curata resursele temporare folosite de operatia curenta (helper intern pentru `send_reminders_now`)."""
            try:
                thread.quit()
                thread.wait()
            except Exception:
                pass

        worker.finished.connect(lambda _res: cleanup())
        worker.error.connect(lambda _msg: cleanup())
        thread.start()

    def send_test_sms_now(self, to_number: str, message: str, sms_config: Optional[Dict[str, Any]] = None):
        """Trimite SMS de test catre numarul configurat si afiseaza rezultatul."""
        payload = dict(sms_config or build_sms_gateway_runtime_config())
        mode = "local"
        provider = "SMSMOBILEAPI"
        to_txt = (to_number or "").strip()
        msg_txt = (message or "").strip() or "Test SMS PacientiApp"

        def on_finished(res):
            """Gestioneaza evenimentul finished in `App`, ca helper intern in `send_test_sms_now`."""
            try:
                pretty = json.dumps(res, ensure_ascii=False, indent=2) if isinstance(res, (dict, list)) else str(res)
            except Exception:
                pretty = str(res)
            if len(pretty) > 1800:
                pretty = pretty[:1800] + "\n..."
            QMessageBox.information(
                self,
                "Test SMS",
                f"Mod: {mode}\nProvider: {provider}\nDestinatar: {to_txt}\n\nRaspuns:\n{pretty}",
            )
            try:
                self._set_transient_status(f"Test SMS OK ({mode}/{provider})", seconds=5)
            except Exception:
                pass

        worker = Worker(_send_sms_via_selected_provider, to_txt, msg_txt, payload)
        self.run_worker_with_progress("Test SMS", "Trimit SMS de test...", worker, on_finished)

    def check_auto_reminders(self):
        """Tick periodic care declanseaza schedulerul de remindere automate."""
        try:
            if get_setting("reminder_auto_enabled", "0") != "1":
                return
            now = datetime.now()
            scheduler_mode = (get_setting("reminder_scheduler_mode", "continuous") or "continuous").strip().lower()
            if scheduler_mode not in ("continuous", "fixed_times"):
                scheduler_mode = "continuous"

            if scheduler_mode == "fixed_times":
                t_raw = get_setting("reminder_times", "08:00,12:00") or "08:00,12:00"
                times = parse_hhmm_list(t_raw)
                if not times:
                    return
                lookback_h = _setting_int("reminder_catchup_hours", 36, 1, 168)
                last_slot = _parse_slot_dt(get_setting(REMINDER_LAST_SLOT_KEY, "") or "")
                start_dt = (last_slot + timedelta(minutes=1)) if last_slot else (now - timedelta(hours=lookback_h))
                due_slots: List[datetime] = []
                dcur = start_dt.date()
                while dcur <= now.date():
                    for hhmm in times:
                        hh, mm = [int(x) for x in hhmm.split(":")]
                        slot = datetime(dcur.year, dcur.month, dcur.day, hh, mm)
                        if start_dt <= slot <= now:
                            due_slots.append(slot)
                    dcur += timedelta(days=1)
                due_slots.sort()
                if not due_slots:
                    return
                slot = due_slots[0]
                set_setting(REMINDER_LAST_SLOT_KEY, _fmt_slot_dt(slot))
                self.send_reminders_now(silent=True, trigger_dt=slot)
                return

            due, _wait_min = _reminder_interval_status(now, force=False)
            if not due:
                return
            self.send_reminders_now(silent=True, trigger_dt=now)
        except Exception:
            pass

    # ---------------- updates ----------------
    def check_updates_ui(self):
        """Gestioneaza updates interfata in `App`."""
        self.check_for_updates_async(show_no_update=True, record_today=False)

    def _auto_check_updates(self):
        """Automatizeaza check updates in `App`."""
        try:
            if get_current_role() != "admin":
                return
            today = date.today().isoformat()
            last = get_setting("update_last_check_date", "")
            if last == today:
                return
            self.check_for_updates_async(show_no_update=False, record_today=True)
        except Exception:
            pass

    def check_for_updates_async(self, show_no_update: bool = False, record_today: bool = False):
        """Gestioneaza for updates async in `App`."""
        if getattr(self, "_update_check_in_progress", False):
            return
        if not _get_update_manifest_url():
            if show_no_update:
                QMessageBox.information(self, "Update", "Update-urile nu sunt configurate.")
            return

        self._update_check_in_progress = True
        today = date.today().isoformat()

        def done(manifest):
            """Proceseaza finalizarea cu succes a operatiei asincrone (helper intern pentru `check_for_updates_async`)."""
            self._update_check_in_progress = False
            if record_today:
                set_setting("update_last_check_date", today)
            self._handle_update_manifest(manifest, show_no_update)

        def on_error(msg):
            """Gestioneaza evenimentul error in `App`, ca helper intern in `check_for_updates_async`."""
            self._update_check_in_progress = False
            if record_today:
                set_setting("update_last_check_date", today)
            if show_no_update:
                QMessageBox.warning(self, "Update", f"Eroare la verificare update:\n{msg}")

        if show_no_update:
            worker = Worker(fetch_update_manifest)

            def clear_in_progress(*_args):
                """Curata in progress in `App`, ca helper intern in `check_for_updates_async`."""
                self._update_check_in_progress = False
                if record_today:
                    set_setting("update_last_check_date", today)

            worker.error.connect(clear_in_progress)
            worker.cancelled.connect(clear_in_progress)
            self.run_worker_with_progress("Update", "Verific update disponibil...", worker, done)
            return

        worker = Worker(fetch_update_manifest)

        worker.finished.connect(done)
        worker.error.connect(on_error)
        thread = QThread(self)
        worker.moveToThread(thread)
        thread.started.connect(worker.run)

        def cleanup():
            """Curata resursele temporare folosite de operatia curenta (helper intern pentru `check_for_updates_async`)."""
            try:
                thread.quit()
                thread.wait()
            except Exception:
                pass

        worker.finished.connect(lambda _res: cleanup())
        worker.error.connect(lambda _msg: cleanup())
        thread.start()

    def _handle_update_manifest(self, manifest: Optional[Dict[str, Any]], show_no_update: bool):
        """Gestioneaza update manifest in `App`."""
        if not manifest:
            if show_no_update:
                QMessageBox.information(self, "Update", "Nu exista update disponibil.")
            return

        newv = (manifest.get("version") or "").strip()
        if not newv:
            if show_no_update:
                QMessageBox.warning(self, "Update", "Manifest invalid (versiune lipsa).")
            return
        if not _is_newer_version(APP_VERSION, newv):
            if show_no_update:
                QMessageBox.information(self, "Update", f"Aplicatia este la zi (v{APP_VERSION}).")
            return

        skip_v = (get_setting("update_skip_version", "") or "").strip()
        if skip_v and skip_v == newv:
            return

        notes = (manifest.get("notes") or "").strip()
        msg = f"Versiune noua disponibila: v{newv}\nVersiunea ta: v{APP_VERSION}\n\n"
        if notes:
            msg += f"Note:\n{notes}\n\n"
        msg += "Vrei sa descarci si instalezi update-ul acum?"

        if QMessageBox.question(
            self,
            "Update disponibil",
            msg,
            QMessageBox.StandardButton.Ok | QMessageBox.StandardButton.Cancel,
            QMessageBox.StandardButton.Cancel,
        ) != QMessageBox.StandardButton.Ok:
            return

        self._download_and_install_update(manifest)

    def _download_and_install_update(self, manifest: Dict[str, Any]):
        """Gestioneaza and install update in `App`."""
        url = (manifest.get("url") or "").strip()
        if not url:
            QMessageBox.warning(self, "Update", "URL lipsa in manifest.")
            return

        dest_dir = APP_DIR / "updates"
        dest_dir.mkdir(parents=True, exist_ok=True)
        fname = Path(urllib.parse.urlparse(url).path).name or f"MBM-Analytic-{manifest.get('version','')}.exe"
        dest = str(dest_dir / fname)

        worker = Worker(download_update_file, url, dest)

        def done(path):
            """Proceseaza finalizarea cu succes a operatiei asincrone (helper intern pentru `_download_and_install_update`)."""
            exp_hash = (manifest.get("sha256") or "").strip().lower()
            if exp_hash:
                got = sha256_file(path).lower()
                if got != exp_hash:
                    QMessageBox.critical(self, "Update", "Hash invalid. Update corupt.")
                    return

            if QMessageBox.question(
                self,
                "Instalare update",
                "Update descarcat. Se va porni installerul si aplicatia se va inchide. Continui?",
                QMessageBox.StandardButton.Ok | QMessageBox.StandardButton.Cancel,
                QMessageBox.StandardButton.Cancel,
            ) != QMessageBox.StandardButton.Ok:
                return
            try:
                subprocess.Popen([path], shell=False)
            except Exception:
                try:
                    os.startfile(path)  # type: ignore
                except Exception as e:
                    QMessageBox.critical(self, "Update", f"Nu pot porni installerul:\n{e}")
                    return
            QApplication.instance().quit()

        self.run_worker_with_progress("Update aplicatie", "Descarc update...", worker, done)

    def restore_db_ui(self):
        """Restaureaza baza de date interfata in `App`."""
        if not self._require_sensitive_reauth("Restore DB"):
            return
        path, _ = QFileDialog.getOpenFileName(self, "Restore DB", "", "SQLite DB (*.db)")
        if not path:
            return
        if not self.ask_yes_no("Confirmare", "Restaurarea va inlocui baza curenta. ContinuiT"):
            return
        try:
            ts = datetime.now().strftime("%Y-%m-%d_%H%M%S")
            backup = APP_DIR / f"backup_before_restore_{ts}.db"
            try:
                shutil.copy2(DB_PATH, backup)
            except Exception:
                pass
            shutil.copy2(path, DB_PATH)
            self.load_table()
            self._set_status_text()
            log_action("restore_db", path)
            QMessageBox.information(self, "OK", "Restaurare finalizata.")
        except Exception as e:
            QMessageBox.critical(self, "Restore DB", f"Eroare:\n{e}")

    def cleanup_database_ui(self):
        """Gestioneaza database interfata in `App`."""
        if not self._require_sensitive_reauth("Curatare DB"):
            return
        dlg = DatabaseCleanupDialog(self)
        if dlg.exec() != QDialog.DialogCode.Accepted:
            return

        seg_labels = {k: lbl for k, lbl, _ in DB_CLEANUP_SEGMENTS}
        if "all" in dlg.selected_segments:
            selected_txt = "Toate segmentele"
        else:
            selected_txt = ", ".join(seg_labels.get(k, k) for k in dlg.selected_segments)

        msg = (
            "Urmeaza sa stergi date din baza locala.\n\n"
            f"Segmente: {selected_txt}\n"
            f"Include utilizatori/setari: {'Da' if dlg.include_system else 'Nu'}\n\n"
            "Datele vor fi mutate in Recycle Bin + se va crea backup inainte de stergere. Continui?"
        )
        if not self.ask_yes_no("Confirmare stergere", msg):
            return

        backup_path = ""
        try:
            ts = datetime.now().strftime("%Y-%m-%d_%H%M%S")
            backup = APP_DIR / f"backup_before_cleanup_{ts}.db"
            shutil.copy2(DB_PATH, backup)
            backup_path = str(backup)
        except Exception:
            backup_path = ""

        try:
            counts, snapshot_id = cleanup_local_database_segments(
                dlg.selected_segments,
                include_system=dlg.include_system,
                action="cleanup_database",
            )
            total_deleted = int(sum(max(0, int(v or 0)) for v in counts.values()))
            self.load_table()
            self.do_clear_form()
            self.mark_dirty_and_schedule_backup("after_cleanup_database")
            self._set_status_text()
            try:
                log_action(
                    "cleanup_database",
                    json.dumps(
                        {
                            "segments": dlg.selected_segments,
                            "include_system": dlg.include_system,
                            "deleted_rows": total_deleted,
                            "recycle_snapshot_id": snapshot_id,
                        },
                        ensure_ascii=False,
                    ),
                )
            except Exception:
                pass

            details = "\n".join(f"- {tbl}: {cnt}" for tbl, cnt in sorted(counts.items()))
            text = f"Curatare finalizata.\nRanduri sterse: {total_deleted}"
            if backup_path:
                text += f"\nBackup: {backup_path}"
            if snapshot_id:
                text += f"\nRecycle Bin snapshot ID: {snapshot_id}"
            if details:
                text += f"\n\nDetalii:\n{details}"
            QMessageBox.information(self, "Curatare DB", text)
        except Exception as e:
            QMessageBox.critical(self, "Curatare DB", f"Eroare la stergere:\n{e}")

    def open_recycle_bin_ui(self):
        """Deschide recycle bin interfata in `App`."""
        dlg = RecycleBinDialog(self)
        if dlg.exec() != QDialog.DialogCode.Accepted:
            return
        snapshot_id = dlg.selected_snapshot_id
        if not snapshot_id:
            return

        table_counts = get_recycle_snapshot_table_counts(int(snapshot_id))
        total_rows = int(sum(table_counts.values()))
        details = "\n".join(f"- {tbl}: {cnt}" for tbl, cnt in sorted(table_counts.items()))
        msg = (
            f"Se va restaura snapshot-ul #{snapshot_id}.\n"
            f"Randuri in snapshot: {total_rows}\n\n"
            "Aplicatia va crea backup inainte de restaurare. Continui?"
        )
        if details:
            msg += f"\n\nDetalii:\n{details}"
        if not self.ask_yes_no("Confirmare restaurare", msg):
            return

        backup_path = ""
        try:
            ts = datetime.now().strftime("%Y-%m-%d_%H%M%S")
            backup = APP_DIR / f"backup_before_recycle_restore_{ts}.db"
            shutil.copy2(DB_PATH, backup)
            backup_path = str(backup)
        except Exception:
            backup_path = ""

        try:
            restored = restore_recycle_snapshot(int(snapshot_id))
            total_restored = int(sum(restored.values()))
            self.load_table()
            self._set_status_text()
            self.mark_dirty_and_schedule_backup("after_recycle_restore")
            try:
                log_action(
                    "restore_recycle_snapshot",
                    json.dumps(
                        {
                            "snapshot_id": int(snapshot_id),
                            "restored_rows": total_restored,
                        },
                        ensure_ascii=False,
                    ),
                )
            except Exception:
                pass

            details2 = "\n".join(f"- {tbl}: {cnt}" for tbl, cnt in sorted(restored.items()))
            text = f"Restaurare finalizata.\nRanduri restaurate: {total_restored}"
            if backup_path:
                text += f"\nBackup: {backup_path}"
            if details2:
                text += f"\n\nDetalii:\n{details2}"
            QMessageBox.information(self, "Recycle Bin", text)
        except Exception as e:
            QMessageBox.critical(self, "Recycle Bin", f"Eroare la restaurare:\n{e}")

    def closeEvent(self, event):
        """La inchidere aplicatie, inchide toate paginile deschise si persist setarile relevante."""
        btn = QMessageBox.question(
            self,
            "Inchidere aplicatie",
            "Esti sigur ca vrei sa inchizi aplicatia?",
            QMessageBox.StandardButton.Ok | QMessageBox.StandardButton.Cancel,
            QMessageBox.StandardButton.Cancel,
        )
        if btn != QMessageBox.StandardButton.Ok:
            event.ignore()
            return
        try:
            self._save_consult_draft_now(force=True)
        except Exception:
            pass
        try:
            self._close_all_open_pages()
        except Exception:
            pass
        try:
            self._save_window_placement_settings()
        except Exception:
            pass
        try:
            if getattr(self, "_dirty_since_last_backup", False):
                self.autosave_backup_now(reason="on_close")
        except Exception:
            pass
        super().closeEvent(event)


if __name__ == "__main__":
    args = [str(a).strip() for a in sys.argv[1:]]
    run_reminder_worker = "--run-reminders-worker" in args
    force_worker = "--force" in args
    run_self_check = "--self-check" in args

    _install_error_logging()

    if run_self_check:
        db_report = init_db()
        ensure_default_location()
        init_sync_schema()
        diag = db_report or {}
        schema_version_now = int((diag or {}).get("schema_version") or (diag or {}).get("schema_version_after") or 0)
        schema_target = int((diag or {}).get("schema_version_target") or int(DB_SCHEMA_VERSION_CURRENT))
        payload = {
            "ok": not bool((diag or {}).get("issues")),
            "schema_version": schema_version_now,
            "schema_version_target": schema_target,
            "issues": list((diag or {}).get("issues") or []),
            "migration": db_report or {},
        }
        try:
            print(json.dumps(payload, ensure_ascii=False, indent=2))
        except Exception:
            print(str(payload))
        sys.exit(0 if payload.get("ok") else 2)

    if run_reminder_worker:
        db_report = init_db()
        if db_report and (db_report.get("issues") or []):
            try:
                print(_format_schema_diagnostic_text(db_report), file=sys.stderr)
            except Exception:
                pass
        ensure_default_location()
        init_sync_schema()
        remove_diacritics_in_db()
        result = run_reminders_scheduler_once(force=force_worker)
        try:
            print(json.dumps(result, ensure_ascii=False))
        except Exception:
            print(str(result))
        sys.exit(0)

    app = QApplication(sys.argv)
    _ui_polish_filter = _UiPolishEventFilter(app)
    app.installEventFilter(_ui_polish_filter)
    setattr(app, "_ui_polish_filter", _ui_polish_filter)
    app.setApplicationName(f"MBM - Analytic {APP_VERSION_LABEL}")
    apply_global_button_style(app)

    APP_ICON = create_app_icon()
    app.setWindowIcon(APP_ICON)

    splash, bar = create_splash()
    splash.show()
    app.processEvents()

    bar.setValue(15)
    splash.showMessage("Initializare baza de date...", Qt.AlignmentFlag.AlignBottom | Qt.AlignmentFlag.AlignHCenter)
    app.processEvents()
    db_report = init_db()
    ensure_default_location()
    init_sync_schema()
    remove_diacritics_in_db()
    if db_report and (db_report.get("issues") or []):
        splash.hide()
        app.processEvents()
        if not show_schema_diagnostic_dialog(db_report):
            sys.exit(1)
        splash.show()
        app.processEvents()

    bar.setValue(60)
    splash.showMessage("Se incarca interfata...", Qt.AlignmentFlag.AlignBottom | Qt.AlignmentFlag.AlignHCenter)
    app.processEvents()
    splash.hide()
    # login
    login = LoginDialog()
    if login.exec() != QDialog.DialogCode.Accepted:
        sys.exit(0)
    user_row = login.user_row
    if not user_row:
        QMessageBox.warning(None, "Autentificare", "Autentificare esuata.")
        sys.exit(0)
    set_current_user_role(
        user_row.get("username") or DEFAULT_USER,
        user_row.get("role") or DEFAULT_ROLE,
        (user_row.get("full_name") or user_row.get("username") or DEFAULT_USER),
    )
    w = App()

    bar.setValue(90)
    splash.showMessage("Se finalizeaza...", Qt.AlignmentFlag.AlignBottom | Qt.AlignmentFlag.AlignHCenter)
    app.processEvents()
    w.show_with_saved_window_placement()

    bar.setValue(100)
    splash.showMessage("Gata", Qt.AlignmentFlag.AlignBottom | Qt.AlignmentFlag.AlignHCenter)
    app.processEvents()
    splash.finish(w)

    sys.exit(app.exec())
0


