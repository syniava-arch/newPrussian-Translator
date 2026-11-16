"""Структурная проверка данных переводчика Prūsiska bilā.

Не запускает pymorphy3 / Pyodide — работает только с JSON, поэтому быстрый:
~500мс на наших данных (dictionary 13 023 + overrides 11 191 + verb_frames
1 743 + sentence_memory 83 + propernames 2 090). Основное время — парсинг
overrides.json (10 МБ, ~175мс). Для сравнения: test_golden.py c pymorphy
стартует ~30 секунд, так что этот тест в ~60× быстрее.

Запуск:
    python3 tests/test_data_integrity.py
    python3 tests/test_data_integrity.py --verbose
    python3 tests/test_data_integrity.py --strict   # предупреждения = ошибки

Возвращает exit code 0 если все ERROR-проверки прошли; 1 если есть ERROR'ы.
В режиме --strict — также 1 при наличии WARNING'ов.

Полезно как pre-commit hook: проверяет массу данных (1826+ записей в
verb_frames + sentence_memory + PN) за 0.5с, тогда как test_golden проверяет
только 32 конкретных предложения за 30с. test_data_integrity ловит
СТРУКТУРНЫЕ баги (опечатки в JSON, дубликаты, битые ссылки); test_golden
ловит СЕМАНТИЧЕСКИЕ баги (неправильный перевод). Они дополняют друг друга.
"""
import json
import os
import re
import sys
import time
from collections import Counter, defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DATA = os.path.join(ROOT, "data")

# Допустимые прусские буквы в словах (используется в s/w/f полях dictionary,
# леммах propernames, ключах verb_frames, pr строках sentence_memory).
# Включает редкие диакритики, которые реально встречаются в наших данных:
#   ḑḐ (ḑāgs, meḑāni), ḿḾ (ipruḿbs, tiḿrintun), õ (astõnjai)
#   Литовые акценты (à è ì ò ù á é í ó ú) — встречаются в 46 headwords словаря
#   (àfrikisks, ámzisks, àsmens, architèkts...) как mark stress; не литовский leak.
# Символы литовского/латышского/польского (ə ɫ ẽ ṁ ḗ) НЕ входят — они
# разрешены только в lt/lv/pl полях dictionary, не в pr.
PR_LETTERS = "A-Za-zĀāĒēĪīŌōŪūČčĘęĖėĮįŠšŲųŽžŃńḐḑḿḾÕõàèìòùáéíóúÀÈÌÒÙÁÉÍÓÚĹĺĽľ"
# Слово: прусские буквы + дефис внутри (не в начале/конце). Stem-lemma с
# trailing '-' ('bab-', 'klēt-') — отдельный паттерн ниже.
PR_WORD_RE = re.compile(r"^[" + PR_LETTERS + r"]+(-[" + PR_LETTERS + r"]+)*$")
PR_STEM_RE = re.compile(r"^[" + PR_LETTERS + r"]+-$")  # 'bab-', 'klēt-'
PR_CHAR_RE = re.compile(r"[" + PR_LETTERS + r"]")

# Допустимые русские буквы (для ru полей и ru_out)
RU_LETTERS = "А-Яа-яЁё"
RU_WORD_RE = re.compile(r"^[" + RU_LETTERS + r"]+$")

# Допустимые падежи в propernames.pr (стандартный набор прусского склонения)
PR_CASES_SG = {"nom", "gen", "dat", "akk", "loc", "ins"}
PR_CASES_PL = {"nom", "gen", "dat", "akk"}
# Допустимые падежи в propernames.ru — наши данные используют прусский стиль
# (nom/gen/dat/akk/ins/prl), а не pymorphy (nomn/gent/datv/...).
RU_CASES = {"nom", "gen", "dat", "akk", "ins", "prl"}

# Допустимые object_case в verb_frames
VF_OBJECT_CASES = {"akk", "gent", "dat", None}


def load(name, default=None):
    path = os.path.join(DATA, name)
    if not os.path.exists(path):
        return default
    with open(path, encoding="utf-8") as f:
        return json.load(f)


# ---------------------------------------------------------------------------
# Коллектор результатов проверки
# ---------------------------------------------------------------------------
class Reporter:
    def __init__(self):
        self.errors = []
        self.warnings = []
        self.infos = []

    def err(self, check, msg):
        self.errors.append((check, msg))

    def warn(self, check, msg):
        self.warnings.append((check, msg))

    def info(self, check, msg):
        self.infos.append((check, msg))

    def summary(self, verbose=False):
        out = []
        out.append("")
        out.append("=" * 70)
        out.append("РЕЗУЛЬТАТЫ ПРОВЕРОК")
        out.append("=" * 70)
        # Если verbose, показать info
        if verbose:
            for check, msg in self.infos:
                out.append(f"  INFO   [{check}] {msg}")
        for check, msg in self.warnings:
            out.append(f"  WARN   [{check}] {msg}")
        for check, msg in self.errors:
            out.append(f"  ERROR  [{check}] {msg}")
        out.append("")
        out.append(f"ИТОГ: errors={len(self.errors)}  warnings={len(self.warnings)}  infos={len(self.infos)}")
        return "\n".join(out)


# ---------------------------------------------------------------------------
# Проверки
# ---------------------------------------------------------------------------

def check_files_load(r, files):
    """A1: Все data-файлы загружаются как ожидаемый тип."""
    expected_types = {
        "dictionary.json": list,
        "overrides.json": list,
        "phrasebook.json": list,
        "priorities.json": dict,
        "propernames.json": list,
        "propernames-curated.json": list,
        "sentence_memory.json": list,
        "verb_frames.json": dict,
    }
    for name, expected in expected_types.items():
        data = load(name)
        if data is None:
            r.err("A1_files_load", f"{name}: файл отсутствует или пустой")
            continue
        if not isinstance(data, expected) or (
            isinstance(data, (list, dict)) and len(data) == 0
        ):
            r.err("A1_files_load",
                  f"{name}: ожидается непустой {expected.__name__}, "
                  f"получен {type(data).__name__} с len={len(data) if isinstance(data,(list,dict)) else '-'}")
            continue
        r.info("A1_files_load", f"{name}: OK ({len(data)} записей)")


def check_sentence_memory_duplicates(r, memory):
    """A2: нет дубликатов ru (case-insensitive) и дубликатов pr."""
    ru_seen = {}
    pr_seen = {}
    for i, item in enumerate(memory):
        if not isinstance(item, dict):
            r.err("A2_memory_dups", f"idx {i}: запись не dict — {type(item).__name__}")
            continue
        ru = item.get("ru")
        if isinstance(ru, list):
            ru = ru[0] if ru else ""
        ru = (ru or "").strip()
        pr = (item.get("pr") or "").strip()
        if not ru:
            r.err("A2_memory_dups", f"idx {i}: пустое поле ru — {item}")
            continue
        if not pr:
            r.err("A2_memory_dups", f"idx {i}: пустое поле pr — {item}")
            continue
        ru_lower = ru.lower()
        if ru_lower in ru_seen:
            r.err("A2_memory_dups",
                  f"idx {i}: дубликат ru «{ru}» (раньше idx {ru_seen[ru_lower]})")
        else:
            ru_seen[ru_lower] = i
        if pr in pr_seen:
            r.err("A2_memory_dups",
                  f"idx {i}: дубликат pr «{pr}» (раньше idx {pr_seen[pr]})")
        else:
            pr_seen[pr] = i


def check_sentence_memory_fields(r, memory):
    """A3: каждая запись memory имеет ru, pr, ru_out, note."""
    missing_ru_out = 0
    missing_note = 0
    for i, item in enumerate(memory):
        if not isinstance(item, dict):
            continue
        if "ru_out" not in item or not str(item.get("ru_out", "")).strip():
            missing_ru_out += 1
            r.warn("A3_memory_fields",
                   f"idx {i}: нет ru_out — pr=«{(item.get('pr') or '')[:60]}»")
        if "note" not in item or not str(item.get("note", "")).strip():
            missing_note += 1
            r.warn("A3_memory_fields",
                   f"idx {i}: нет note — pr=«{(item.get('pr') or '')[:60]}»")
    if missing_ru_out == 0 and missing_note == 0:
        r.info("A3_memory_fields", f"все {len(memory)} записей имеют ru_out и note")


def check_sentence_memory_ru_lowercase(r, memory):
    """B1: memory.ru — нормализованный ключ, должен быть lowercase."""
    bad = []
    for i, item in enumerate(memory):
        ru = item.get("ru")
        if isinstance(ru, list):
            ru = ru[0] if ru else ""
        ru = ru or ""
        # Сравниваем с lowercase только если есть заглавные (исключая первую букву —
        # всё должно быть lowercase, включая первую, т.к. это lookup-key)
        if ru != ru.lower():
            bad.append((i, ru[:60]))
    if bad:
        for i, ru in bad:
            r.warn("B1_memory_ru_lower", f"idx {i}: ru не lowercase — «{ru}»")
    else:
        r.info("B1_memory_ru_lower", f"все {len(memory)} ru-ключей в lowercase")


def check_sentence_memory_pr_chars(r, memory):
    """B3: в memory.pr только прусские буквы (плюс пунктуация и цифры)."""
    # Разрешаем: прусские буквы, пробелы, стандартную пунктуацию, цифры,
    # кавычки (включая типографские «...» и "...")
    allowed_extra = set(" \t,.!?;:«»\"'()[]—–-0123456789/\u201C\u201D\u2018\u2019")
    bad = []
    for i, item in enumerate(memory):
        pr = item.get("pr") or ""
        for ch in pr:
            if ch in allowed_extra:
                continue
            if PR_CHAR_RE.match(ch):
                continue
            # Если это кириллица или латиница вне набора — flagged
            bad.append((i, ch, pr[:60]))
            break  # одна проблема на запись достаточно
    if bad:
        for i, ch, pr in bad[:20]:
            r.warn("B3_memory_pr_chars",
                   f"idx {i}: неразрешённый символ «{ch}» (U+{ord(ch):04X}) "
                   f"в pr «{pr}»")
        if len(bad) > 20:
            r.warn("B3_memory_pr_chars",
                   f"... ещё {len(bad)-20} записей с подозрительными символами")
    else:
        r.info("B3_memory_pr_chars",
               f"все {len(memory)} pr-строк содержат только прусские буквы")


def check_verb_frames_structure(r, frames):
    """A4: verb_frames — ключи lowercase, transitive bool, object_case валиден."""
    bad_keys_lower = []
    bad_transitive = []
    bad_case = []
    for lemma, frame in frames.items():
        if not isinstance(lemma, str) or not lemma.strip():
            r.err("A4_verb_frames_struct", f"lemma не строка: {lemma!r}")
            continue
        if lemma != lemma.lower():
            bad_keys_lower.append(lemma)
        if not isinstance(frame, dict):
            r.err("A4_verb_frames_struct",
                  f"lemma «{lemma}»: frame не dict — {type(frame).__name__}")
            continue
        if "transitive" not in frame:
            r.err("A4_verb_frames_struct", f"lemma «{lemma}»: нет поля transitive")
        elif not isinstance(frame.get("transitive"), bool):
            bad_transitive.append(
                (lemma, type(frame.get("transitive")).__name__, frame.get("transitive")))
        oc = frame.get("object_case")
        if oc not in VF_OBJECT_CASES:
            bad_case.append((lemma, oc))
        elif oc is not None and frame.get("transitive") is False:
            r.warn("A4_verb_frames_struct",
                   f"lemma «{lemma}»: transitive=False но object_case={oc} "
                   f"(обычно должно быть null)")
    if bad_keys_lower:
        for lemma in bad_keys_lower:
            r.err("A4_verb_frames_struct", f"lemma «{lemma}» не в lowercase")
    if bad_transitive:
        for lemma, t, v in bad_transitive:
            r.err("A4_verb_frames_struct",
                  f"lemma «{lemma}»: transitive типа {t} = {v!r} (должен быть bool)")
    if bad_case:
        for lemma, oc in bad_case:
            r.err("A4_verb_frames_struct",
                  f"lemma «{lemma}»: object_case={oc!r} (должен быть akk/gent/dat/null)")


def check_verb_frames_in_dictionary(r, frames, dictionary):
    """A5: каждая lemma в verb_frames существует в dictionary как слово (w поле).
    Reflexive-глаголы могут быть записаны как 'X si' (с пробелом) — это валидно."""
    dict_words = set((e.get("w") or "").lower() for e in dictionary if e.get("w"))
    not_in_dict = []
    non_pr_chars = []
    for lemma in frames:
        # Для lookup в dictionary используем полную строку (включая ' si')
        if lemma not in dict_words:
            not_in_dict.append(lemma)
        # Проверяем алфавит: разбиваем по пробелу, каждую часть проверяем отдельно
        # (это позволяет 'X si' где X — прусский инфинитив, а si — частица)
        parts = lemma.split()
        for part in parts:
            if not PR_WORD_RE.match(part):
                bad = set(c for c in part if not PR_CHAR_RE.match(c))
                if bad:
                    non_pr_chars.append((lemma, part, bad))
                    break
    if not_in_dict:
        for lemma in not_in_dict[:20]:
            r.err("A5_verb_frames_in_dict",
                  f"lemma «{lemma}» не найдена в dictionary.w")
        if len(not_in_dict) > 20:
            r.err("A5_verb_frames_in_dict",
                  f"... ещё {len(not_in_dict)-20} lemma не найдены")
    else:
        r.info("A5_verb_frames_in_dict",
               f"все {len(frames)} verb_frames lemma присутствуют в dictionary")
    if non_pr_chars:
        for lemma, part, chars in non_pr_chars[:10]:
            r.warn("A5_verb_frames_in_dict",
                   f"lemma «{lemma}»: часть «{part}» содержит непрусские символы: {chars}")


def check_dictionary_ids(r, dictionary):
    """A6: dictionary.i — присутствует, уникальный. Чаще int, но допускается
    string-id для специальных «составных» статей (напр. 'new-m-unit' = 'm' = «год»)."""
    ids = []
    missing_id = []
    bad_type = []
    string_ids = []
    for i, entry in enumerate(dictionary):
        if not isinstance(entry, dict):
            continue
        if "i" not in entry:
            missing_id.append(i)
            continue
        v = entry.get("i")
        if isinstance(v, bool):
            bad_type.append((i, type(v).__name__, v))
            continue
        if isinstance(v, int):
            ids.append(v)
        elif isinstance(v, str) and v.strip():
            # string-id — допускается, но помечаем как warning для аудита
            string_ids.append((i, v, entry.get("w", "?")))
            ids.append(v)  # уникальность учитываем
        else:
            bad_type.append((i, type(v).__name__, v))
    if missing_id:
        for i in missing_id[:10]:
            r.err("A6_dict_ids", f"idx {i}: нет поля i")
    if bad_type:
        for i, t, v in bad_type[:10]:
            r.err("A6_dict_ids", f"idx {i}: i типа {t} = {v!r}")
    id_counter = Counter(ids)
    dups = [(k, v) for k, v in id_counter.items() if v > 1]
    if dups:
        for k, c in dups[:10]:
            r.err("A6_dict_ids", f"дубликат id={k!r} (встречается {c} раз)")
    if string_ids:
        for i, v, w in string_ids[:10]:
            r.warn("A6_dict_ids",
                   f"idx {i}: string-id «{v}» (w={w!r}) — спецстатья; id={v!r}")
        if len(string_ids) > 10:
            r.warn("A6_dict_ids", f"... ещё {len(string_ids)-10} string-id записей")
    int_ids = [x for x in ids if isinstance(x, int)]
    if not dups and not bad_type and not missing_id:
        if int_ids:
            r.info("A6_dict_ids",
                   f"все {len(ids)} dictionary id уникальны "
                   f"({len(int_ids)} int + {len(string_ids)} string; диапазон int "
                   f"{min(int_ids)}–{max(int_ids)})")


def check_overrides_ids(r, overrides, dictionary):
    """A7: overrides.id — уникальный, ссылается на dictionary.i."""
    dict_ids = set(e.get("i") for e in dictionary if isinstance(e.get("i"), int))
    ids = []
    missing_id = []
    for i, entry in enumerate(overrides):
        if not isinstance(entry, dict):
            continue
        if "id" not in entry:
            missing_id.append((i, entry.get("word", "?")))
            continue
        v = entry.get("id")
        if not isinstance(v, int):
            r.err("A7_overrides_ids",
                  f"idx {i}: id не int — {type(v).__name__} = {v!r}")
            continue
        ids.append(v)
    # Дубликаты
    id_counter = Counter(ids)
    dups = [(k, v) for k, v in id_counter.items() if v > 1]
    if dups:
        for k, c in dups[:10]:
            r.err("A7_overrides_ids", f"дубликат id={k} (встречается {c} раз)")
    # Orphans
    orphans = [i for i in ids if i not in dict_ids]
    if orphans:
        for i in orphans[:10]:
            r.err("A7_overrides_ids",
                  f"orphan: id={i} не найден в dictionary.i")
        if len(orphans) > 10:
            r.err("A7_overrides_ids",
                  f"... ещё {len(orphans)-10} orphan-записей")
    # Без id — это warning (у нас 1 такая запись: wīrstats, ручное примечание)
    if missing_id:
        for i, word in missing_id:
            r.warn("A7_overrides_ids",
                   f"idx {i}: override «{word}» без id (ручная запись? если да — ОК)")
    if not dups and not orphans:
        r.info("A7_overrides_ids",
               f"все {len(ids)} overrides.id уникальны и ссылаются на dictionary")


def check_propernames_lemmas(r, propernames):
    """A8: propernames.lemma — уникальный, непустой, прусские символы
    (включая stem-формы с trailing '-' типа 'bab-', 'klēt-')."""
    lemmas = []
    empty = []
    bad_chars = []
    for i, entry in enumerate(propernames):
        lemma = entry.get("lemma")
        if not lemma or not str(lemma).strip():
            empty.append(i)
            continue
        lemma = str(lemma)
        lemmas.append(lemma)
        if not (PR_WORD_RE.match(lemma) or PR_STEM_RE.match(lemma)):
            bad_chars.append((i, lemma))
    if empty:
        for i in empty[:10]:
            r.err("A8_pn_lemmas", f"idx {i}: пустое поле lemma")
    if bad_chars:
        for i, lemma in bad_chars[:10]:
            r.warn("A8_pn_lemmas",
                   f"idx {i}: lemma «{lemma}» содержит непрусские символы")
    counter = Counter(lemmas)
    dups = [(k, v) for k, v in counter.items() if v > 1]
    if dups:
        for k, c in dups[:10]:
            r.err("A8_pn_lemmas", f"дубликат lemma «{k}» ({c} раз)")
    else:
        r.info("A8_pn_lemmas", f"все {len(lemmas)} propernames.lemma уникальны")


def check_propernames_pr_ru_structure(r, propernames):
    """A8b: propernames.pr и .ru — dict с sg/pl → case → form(s).
    Pr-сторона: для sg достаточно nom/gen/dat/akk (loc/ins опциональны),
    но если записано только nom (без gen/dat/akk) — это означает, что
    прусский склонение для этого имени неизвестно (топонимы типа Alītā, Apī).
    В этом случае помечаем как INFO (не error)."""
    bad_pr = []
    bad_ru = []
    nom_only = []
    for i, entry in enumerate(propernames):
        lemma = entry.get("lemma", "?")
        pr = entry.get("pr", {})
        if not isinstance(pr, dict):
            bad_pr.append((i, lemma, "pr not dict"))
            continue
        for num_key, cases in pr.items():
            num = num_key.lower()
            if num not in ("sg", "pl"):
                bad_pr.append((i, lemma, f"unknown number key «{num_key}»"))
                continue
            if not isinstance(cases, dict):
                bad_pr.append((i, lemma, f"{num_key}: cases not dict"))
                continue
            expected = PR_CASES_SG if num == "sg" else PR_CASES_PL
            # Все присутствующие ключи должны быть валидны
            extra = set(cases.keys()) - expected
            if extra:
                bad_pr.append((i, lemma, f"{num_key}: unknown cases {extra}"))
            # Обязательный минимум — nom/gen/dat/akk; если их нет — это
            # «неполная парадигма», помечаем как INFO (не error).
            required = {"nom", "gen", "dat", "akk"}
            missing = required - set(cases.keys())
            if missing and num == "sg" and set(cases.keys()) == {"nom"}:
                nom_only.append((i, lemma))
            elif missing:
                bad_pr.append((i, lemma, f"{num_key}: missing {missing}"))
        ru = entry.get("ru", {})
        if not isinstance(ru, dict):
            bad_ru.append((i, lemma, "ru not dict"))
            continue
        for num_key, cases in ru.items():
            num = num_key.lower()
            if num not in ("sg", "pl"):
                bad_ru.append((i, lemma, f"unknown number key «{num_key}»"))
                continue
            if not isinstance(cases, dict):
                bad_ru.append((i, lemma, f"{num_key}: cases not dict"))
                continue
            for case_key in cases:
                if case_key not in RU_CASES:
                    bad_ru.append((i, lemma, f"{num_key}: unknown case «{case_key}»"))
    if bad_pr:
        for i, lemma, reason in bad_pr[:20]:
            r.err("A8b_pn_pr_ru", f"idx {i} «{lemma}» pr: {reason}")
        if len(bad_pr) > 20:
            r.err("A8b_pn_pr_ru", f"... ещё {len(bad_pr)-20} проблем в pr")
    if bad_ru:
        for i, lemma, reason in bad_ru[:20]:
            r.err("A8b_pn_pr_ru", f"idx {i} «{lemma}» ru: {reason}")
    if nom_only:
        r.info("A8b_pn_pr_ru",
               f"{len(nom_only)} PN с неполной pr-парадигмой (только sg.nom; "
               f"русская сторона полная) — топонимы с неизвестным прусским "
               f"склонением; ОК")
    if not bad_pr and not bad_ru:
        r.info("A8b_pn_pr_ru",
               f"все {len(propernames)} propernames: pr/ru структура валидна "
               f"(+{len(nom_only)} с неполной pr)")


def check_propernames_meta(r, propernames):
    """A9: gender в {masc, fem, neut}, priority — int >=1, aliases — list."""
    bad_gender = []
    bad_priority = []
    bad_aliases = []
    for i, entry in enumerate(propernames):
        lemma = entry.get("lemma", "?")
        gender = entry.get("gender")
        if gender not in ("masc", "fem", "neut"):
            bad_gender.append((i, lemma, gender))
        prio = entry.get("priority")
        if not isinstance(prio, int) or isinstance(prio, bool) or prio < 1:
            bad_priority.append((i, lemma, prio))
        aliases = entry.get("aliases", [])
        if not isinstance(aliases, list):
            bad_aliases.append((i, lemma, f"aliases not list: {type(aliases).__name__}"))
        elif not all(isinstance(a, str) for a in aliases):
            bad_aliases.append((i, lemma, "aliases contains non-str"))
    if bad_gender:
        for i, lemma, g in bad_gender[:10]:
            r.err("A9_pn_meta", f"idx {i} «{lemma}»: gender={g!r}")
    if bad_priority:
        for i, lemma, p in bad_priority[:10]:
            r.err("A9_pn_meta", f"idx {i} «{lemma}»: priority={p!r}")
    if bad_aliases:
        for i, lemma, reason in bad_aliases[:10]:
            r.err("A9_pn_meta", f"idx {i} «{lemma}»: {reason}")
    if not (bad_gender or bad_priority or bad_aliases):
        r.info("A9_pn_meta",
               f"все {len(propernames)} propernames: gender/priority/aliases валидны")


def check_curated_subset(r, curated, propernames):
    """A10: каждый lemma в curated существует в основном propernames."""
    main_lemmas = set(e.get("lemma", "") for e in propernames)
    not_in_main = []
    for entry in curated:
        lemma = entry.get("lemma", "")
        if lemma not in main_lemmas:
            not_in_main.append(lemma)
    if not_in_main:
        for lemma in not_in_main:
            r.err("A10_curated_subset",
                  f"curated «{lemma}» не найден в основном propernames.json")
    else:
        r.info("A10_curated_subset",
               f"все {len(curated)} curated-lemma присутствуют в propernames.json")


def check_ru_aliases_consistency(r, propernames):
    """A11: ru_aliases — последовательный тип (всё str или всё dict) в одном entry."""
    mixed = []
    for i, entry in enumerate(propernames):
        al = entry.get("ru_aliases")
        if al is None:
            continue
        if not isinstance(al, list):
            r.err("A11_ru_aliases",
                  f"idx {i} «{entry.get('lemma')}»: ru_aliases не list — "
                  f"{type(al).__name__}")
            continue
        if not al:
            continue
        types = set(type(x).__name__ for x in al)
        if len(types) > 1:
            mixed.append((i, entry.get("lemma"), types))
        # Проверяем корректность dict-формы
        for x in al:
            if isinstance(x, dict):
                if "form" not in x or not x.get("form"):
                    r.err("A11_ru_aliases",
                          f"idx {i} «{entry.get('lemma')}»: dict-alias без form — {x}")
                if "case" in x and x["case"] not in RU_CASES:
                    r.warn("A11_ru_aliases",
                           f"idx {i} «{entry.get('lemma')}»: неизвестный case "
                           f"«{x['case']}» в alias {x}")
            elif not isinstance(x, str):
                r.err("A11_ru_aliases",
                      f"idx {i} «{entry.get('lemma')}»: alias типа {type(x).__name__}")
    if mixed:
        for i, lemma, types in mixed:
            r.warn("A11_ru_aliases",
                   f"idx {i} «{lemma}»: смешанные типы {types} "
                   f"(код умеет оба, но это data-smell)")


def check_priorities_references(r, priorities, dictionary):
    """A12: priorities.pr_to_ru — числовые ключи ссылаются на dictionary.i;
    строковые ключи присутствуют в dictionary.w."""
    dict_ids = set(str(e.get("i")) for e in dictionary if isinstance(e.get("i"), int))
    dict_words_lower = set((e.get("w") or "").lower() for e in dictionary if e.get("w"))
    pr_to_ru = priorities.get("pr_to_ru", {})
    if not isinstance(pr_to_ru, dict):
        r.err("A12_priorities_refs", "pr_to_ru не dict")
        return
    bad = []
    for k in pr_to_ru:
        if k.isdigit():
            if k not in dict_ids:
                bad.append((k, "numeric id not in dictionary.i"))
        else:
            if k.lower() not in dict_words_lower:
                bad.append((k, "string lemma not in dictionary.w"))
    if bad:
        for k, reason in bad[:20]:
            r.err("A12_priorities_refs", f"pr_to_ru key «{k}»: {reason}")
    else:
        r.info("A12_priorities_refs",
               f"все {len(pr_to_ru)} pr_to_ru ключей ссылаются на dictionary")


def check_phrasebook_duplicates(r, phrasebook):
    """A13: в phrasebook нет дубликатов pr (полных строк)."""
    pr_seen = {}
    bad = []
    for i, item in enumerate(phrasebook):
        pr = (item.get("pr") or "").strip()
        if not pr:
            continue
        if pr in pr_seen:
            bad.append((i, pr, pr_seen[pr]))
        else:
            pr_seen[pr] = i
    if bad:
        for i, pr, prev in bad:
            r.err("A13_phrasebook_dups",
                  f"idx {i}: дубликат pr «{pr[:60]}» (раньше idx {prev})")
    else:
        r.info("A13_phrasebook_dups",
               f"все {len(phrasebook)} pr-фраз в phrasebook уникальны")


def check_memory_vs_phrasebook_overlap(r, memory, phrasebook):
    """A14: pr-строки из sentence_memory не должны пересекаться с phrasebook.pr
    (memory и phrasebook — отдельные слои, иначе lookup неоднозначен)."""
    pb_prs = set((item.get("pr") or "").strip() for item in phrasebook if item.get("pr"))
    overlap = []
    for i, item in enumerate(memory):
        pr = (item.get("pr") or "").strip()
        if pr and pr in pb_prs:
            overlap.append((i, pr))
    if overlap:
        for i, pr in overlap:
            r.warn("A14_memory_phrasebook_overlap",
                   f"idx {i}: pr «{pr[:60]}» есть и в memory, и в phrasebook")
    else:
        r.info("A14_memory_phrasebook_overlap",
               f"нет пересечений pr между memory и phrasebook ({len(memory)} vs "
               f"{len(phrasebook)} записей)")


def check_dictionary_ru_field(r, dictionary):
    """A15: dictionary.ru — присутствует (если нет — словарь бесполезен для RU)."""
    no_ru = 0
    sample = []
    for i, entry in enumerate(dictionary):
        if not isinstance(entry, dict):
            continue
        ru = entry.get("ru", "")
        if not ru or not str(ru).strip():
            no_ru += 1
            if len(sample) < 5:
                sample.append((i, entry.get("w", "?")))
    if no_ru:
        r.warn("A15_dict_ru_field",
               f"{no_ru} dictionary-записей без ru (примеры: {sample})")
    else:
        r.info("A15_dict_ru_field",
               f"все {len(dictionary)} dictionary-записей имеют ru-перевод")


# ---------------------------------------------------------------------------
# Главная функция
# ---------------------------------------------------------------------------
def main():
    start = time.time()
    verbose = "--verbose" in sys.argv
    strict = "--strict" in sys.argv

    r = Reporter()

    # Загрузить всё
    memory = load("sentence_memory.json", [])
    frames = load("verb_frames.json", {})
    dictionary = load("dictionary.json", [])
    overrides = load("overrides.json", [])
    phrasebook = load("phrasebook.json", [])
    priorities = load("priorities.json", {})
    propernames = load("propernames.json", [])
    curated = load("propernames-curated.json", [])

    # A1: файлы загружаются
    check_files_load(r, None)

    # A2-A3, B1, B3: sentence_memory
    if isinstance(memory, list) and memory:
        check_sentence_memory_duplicates(r, memory)
        check_sentence_memory_fields(r, memory)
        check_sentence_memory_ru_lowercase(r, memory)
        check_sentence_memory_pr_chars(r, memory)

    # A4-A5: verb_frames
    if isinstance(frames, dict) and frames:
        check_verb_frames_structure(r, frames)
        if isinstance(dictionary, list) and dictionary:
            check_verb_frames_in_dictionary(r, frames, dictionary)

    # A6: dictionary ids
    if isinstance(dictionary, list) and dictionary:
        check_dictionary_ids(r, dictionary)
        check_dictionary_ru_field(r, dictionary)

    # A7: overrides ids
    if isinstance(overrides, list) and overrides and isinstance(dictionary, list):
        check_overrides_ids(r, overrides, dictionary)

    # A8-A9, A11: propernames
    if isinstance(propernames, list) and propernames:
        check_propernames_lemmas(r, propernames)
        check_propernames_pr_ru_structure(r, propernames)
        check_propernames_meta(r, propernames)
        check_ru_aliases_consistency(r, propernames)

    # A10: curated subset
    if isinstance(curated, list) and isinstance(propernames, list):
        check_curated_subset(r, curated, propernames)

    # A12: priorities references
    if isinstance(priorities, dict) and isinstance(dictionary, list) and dictionary:
        check_priorities_references(r, priorities, dictionary)

    # A13-A14: phrasebook
    if isinstance(phrasebook, list) and phrasebook:
        check_phrasebook_duplicates(r, phrasebook)
        if isinstance(memory, list) and memory:
            check_memory_vs_phrasebook_overlap(r, memory, phrasebook)

    elapsed = (time.time() - start) * 1000
    print(r.summary(verbose=verbose))
    print(f"время: {elapsed:.0f} мс")

    if r.errors:
        sys.exit(1)
    if strict and r.warnings:
        print("\n(strict mode: предупреждения считаются ошибками)")
        sys.exit(1)
    sys.exit(0)


if __name__ == "__main__":
    main()
