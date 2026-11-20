# -*- coding: utf-8 -*-
"""
Переводчик RU <-> прусский, версия для запуска в браузере через Pyodide.

load_data() принимает уже загруженные JSON-строки (не читает файлы с диска).
translate_sentence_json() (RU -> PR) и translate_pr_sentence_json() (PR -> RU)
возвращают результат как JSON-строку для вызова из JavaScript.
"""
import json
import re

import pymorphy3

POS_PREFIX_MAP = {
    "aj": "ADJF", "av": "ADVB", "pn": "NPRO", "prp": "PREP",
    "crd": "NUMR", "ord": "NUMR", "ij": "INTJ", "cj": "CONJ",
    "pcl": "PRCL", "encl": "PRCL", "pc": "PRTF",
}

PYMORPHY_TO_LOCAL = {
    "NOUN": "NOUN", "ADJF": "ADJF", "ADJS": "ADJF", "PRTF": "PRTF",
    "PRTS": "PRTF", "VERB": "VERB", "INFN": "VERB", "GRND": "VERB",
    "ADVB": "ADVB", "NPRO": "NPRO", "PREP": "PREP", "NUMR": "NUMR",
    "CONJ": "CONJ", "PRCL": "PRCL", "INTJ": "INTJ",
}

CASE_MAP = {"nomn": "nom", "gent": "gen", "datv": "dat", "accs": "akk", "ablt": None, "loct": "loc",
            "gen2": "gen", "acc2": "akk", "loc2": "loc"}
CASE_MAP_INV = {"nom": "nomn", "gen": "gent", "dat": "datv", "akk": "accs", "loc": "loct"}
# "loc" здесь не откат в датив: локатив выводится из генитива парадигмы
# (см. _derive_loc_from_gen), а в корпусе он и правда стоит после en:
# "Mes asmai teinū en Leītawai", "en widzemei".
RU_CASE_MARKER_TO_LOCAL = {"acc": "akk", "dat": "dat", "gen": "gen", "loc": "loc", "instr": "akk"}
PYMORPHY_CASE_TO_RU_MARKER = {"accs": "acc", "acc2": "acc", "datv": "dat", "gent": "gen",
                               "gen2": "gen", "loct": "loc", "loc2": "loc", "ablt": "instr"}
GENDER_MAP = {"masc": "masc", "femn": "fem", "neut": "neut"}
GENDER_MAP_INV = {"masc": "masc", "fem": "femn", "neut": "neut"}
NUMBER_MAP = {"sing": "sg", "plur": "pl"}
NUMBER_MAP_INV = {"sg": "sing", "pl": "plur"}
PERSON_ORDER = [
    ("1per", "sing"), ("2per", "sing"), ("3per", "sing"),
    ("1per", "plur"), ("2per", "plur"), ("3per", "plur"),
]
TENSE_MAP = {"pres": "present", "past": "past", "futr": "future"}

# для диакритики, которую пишущий может не набрать (макроны и т.п.);
# š/č/ž/ģ и т.д. НЕ сворачиваются - в проекте это отдельные буквы
_DIACRITIC_FOLD = str.maketrans({
    "ā": "a", "â": "a", "à": "a", "á": "a",
    "ē": "e", "ê": "e", "è": "e", "é": "e",
    "ī": "i", "î": "i", "ì": "i", "í": "i",
    "ō": "o", "ô": "o", "ò": "o", "ó": "o",
    "ū": "u", "û": "u", "ù": "u", "ú": "u",
})


def fold_diacritics(s):
    return s.translate(_DIACRITIC_FOLD)


morph = pymorphy3.MorphAnalyzer()

# заполняются load_data()
_ru_index = {}
_override_by_id = {}
_preposition_index = {}
_pr_preposition_senses = {}
_phrasebook = {}         # нормализованная RU-фраза -> готовый PR-перевод
_pr_phrasebook = {}      # прусская фраза (нормализованная) -> готовый RU-перевод
_pr_phrasebook_folded = {}  # то же без макронов - запасной вариант поиска
_pr_phrasebook_max_words = 1
_pr_to_ru_priority = {}
_verb_frames = {}               # прусская лемма (lower) -> {ru, transitive, object_case}
_sentence_memory = {}           # нормализованная RU-фраза -> готовый PR-перевод (полные предложения корпуса)
_pr_sentence_memory = {}        # прусская фраза -> готовый русский перевод
_pr_sentence_memory_folded = {} # то же без макронов
_pr_sentence_memory_max_words = 1
_ru_to_pr_priority = {}
_ru_max_phrase_words = 1
_pr_index = {}          # точная форма (в нижнем регистре) -> [(entry, label), ...]
_pr_index_folded = {}   # то же, но без макронов - запасной вариант поиска
_pr_max_phrase_words = 1
_entry_freq = {}                  # id статьи -> сколько раз её формы встречаются в корпусе
_headword_index = {}              # заголовок в нижнем регистре -> статья
_propernames = {}                 # lemma(lower) -> entry (PN-словарь)
_propername_lemma_index = {}      # любая форма/алиас имени (lower) -> entry
_propername_form_index = {}       # pr-форма(lower) -> (entry, number["sg"|"pl"], pr_case)
_ru_name_index = {}               # ru-форма(lower) -> (entry, number["sg"|"pl"], pr_case)
# Соответствие падежной метки в propernames.json и pymorphy-граммемы.
_PR_CASE_TO_RU = {"nom": "nomn", "gen": "gent", "dat": "datv",
                  "akk": "accs", "ins": "ablt", "prl": "loct"}
_RU_TO_PR_CASE = {v: k for k, v in _PR_CASE_TO_RU.items()}

# Кванторы, управляющие родительным падежом множественного числа:
# "delli kittans passas" -> "несколько других паспортов".
PR_GEN_PL_QUANTIFIERS = {"delli"}

# Русские варианты предлогов перед словами с беглой гласной: словарь обычно
# хранит базовую форму ("с", "в", "к"), а пользователь пишет "со", "во",
# "ко" и т.п. Нормализуем только для поиска, в отладке оставляем ввод.
PREPOSITION_ALIASES = {
    "во": "в",
    "со": "с",
    "ко": "к",
    "об": "о",
    "обо": "о",
    "ото": "от",
    "изо": "из",
    "безо": "без",
    "надо": "над",
    "подо": "под",
    "предо": "перед",
    "передо": "перед",
}

WORD_TOKEN_RE = re.compile(r"^[\wа-яёА-ЯЁ-]+$", re.UNICODE)
PUNCT_TOKEN_RE = re.compile(r"^[^\wа-яёА-ЯЁ]+$", re.UNICODE)
PR_WORD_TOKEN_RE = re.compile(r"^[\wāēīōūâêîôûàèìòùáéíóúŠšČčŽž-]+$", re.UNICODE)
PR_PUNCT_TOKEN_RE = re.compile(r"^[^\wāēīōūâêîôûàèìòùáéíóúŠšČčŽž]+$", re.UNICODE)

# Для обратного PR -> RU перевода один и тот же прусский падеж после
# предлога не всегда соответствует русскому падежу. Например, ēn + dat
# по-русски обычно "в/на ком? чём?" -> предложный падеж.
PR_PREP_RU_CASE = {
    "ēn": {"dat": "loct", "akk": "accs", None: "loct"},
    "en": {"dat": "loct", "akk": "accs", None: "loct"},
    "na": {"akk": "loct", "dat": "loct", None: "loct"},
    # 'pa' + akk в корпусе — временнóе «после сражения»: 'pa' управляет
    # родительным, как и русское «после» (статья 4045, prp acc → de nach).
    "pa": {"akk": "gent", "dat": "loct", "gen": "datv", None: "loct"},
    "prīki": {"akk": "gent", None: "gent"},
    "prīkin": {"akk": "gent", None: "gent"},
    "sēn": {"akk": "ablt", None: "ablt"},
    "sen": {"akk": "ablt", None: "ablt"},
    "ezze": {"dat": "gent", None: "loct"},
    "iz": {"akk": "gent", None: "gent"},
    "ērgi": {"akk": "gent", "gen": "gent", None: "gent"},
    "prēi": {"akk": "datv", None: "datv"},
    "prei": {"akk": "ablt", None: "ablt"},
}


def classify_pos(entry, override):
    s = entry.get("s", "").lower()
    # В поле s часть речи не всегда стоит первой: например,
    # "gen māise, pn po 1 sg ..." для majs. Поэтому смотрим все токены.
    s_tokens = set(re.findall(r"[a-z]+", s))
    # У предлогов иногда есть дополнительная помета "(av)"; предлог должен
    # выигрывать у наречия.
    if "prp" in s_tokens:
        return "PREP"
    # Заглушки форм (x=true) — это «āntran = acc от Āntars», у них в s нет
    # части речи, и раньше они все считались существительными. Из-за этого
    # местоимение tenā («она») проигрывало статье dis («он, она, тот, та»).
    # Часть речи берём у базовой статьи, на которую ссылается b, ТОЛЬКО если
    # у самой заглушки в s нет части речи (sen имеет prp в s, не delegating).
    if not s_tokens and entry.get("x") and entry.get("b"):
        base = _headword_index.get((entry.get("b") or "").lower())
        if base is not None and base is not entry and base.get("i") != entry.get("i"):
            return classify_pos(base, _override_by_id.get(base.get("i")))
    # Также cross-ref (x=true) с непустым s, но без явного POS в s,
    # должен делегировать базовому entry: 'ast' (id=241, s='↑ Būtwei ps 3',
    # b='Būtwei') — это форма глагола 'быть', а не существительное.
    # Без этого ast → NOUN → 'morph.parse(быть).inflect({nomn})' = 'бывшие'.
    if entry.get("x") and entry.get("b"):
        base = _headword_index.get((entry.get("b") or "").lower())
        if base is not None and base is not entry and base.get("i") != entry.get("i"):
            base_pos = classify_pos(base, _override_by_id.get(base.get("i")))
            if base_pos != "NOUN":
                return base_pos
    for code, pos in POS_PREFIX_MAP.items():
        if code != "prp" and code in s_tokens:
            return pos
    if override:
        if isinstance(override.get("conjugation"), dict):
            return "VERB"
        para = override.get("paradigm")
        if isinstance(para, dict) and "positive" in para:
            return "ADJF"
        if isinstance(para, dict):
            return "NOUN"
    w = entry.get("w", "")
    if w.endswith(("tun", "twei", "tuns")):
        return "VERB"
    return "NOUN"


def _ru_case_marker_from_chunk(chunk):
    m = re.search(r"\b(acc|dat|gen|loc|instr)\b", chunk.lower())
    return m.group(1) if m else None


def _clean_ru_chunk(chunk):
    """Убирает пояснения в скобках, падежные пометы и знаки препинания
    вокруг слова/фразы, чтобы 'привет!' стало 'привет' и совпало с тем,
    что вернёт морфоанализатор или что введёт пользователь."""
    chunk = re.sub(r"\(.*?\)", "", chunk)
    chunk = re.sub(r"\b(acc|dat|gen|loc|instr)\b", "", chunk)
    chunk = chunk.strip(" \t!?.,;:—-").strip().lower()
    chunk = re.sub(r"\s+", " ", chunk)
    return chunk


def _clean_ru_token(token):
    return re.sub(r"[^\wа-яёА-ЯЁ-]", "", token, flags=re.UNICODE).lower()


def _norm_ru_key(text):
    """Ключ русской фразы для фразбука.

    Знаки препинания внутри фразы не должны различать ключи: «... статью, где
    было написано, что ...» и тот же текст без запятых — одна статья.
    """
    key = _clean_ru_chunk(text)
    key = re.sub(r"[^\wа-яё-]+", " ", key, flags=re.UNICODE)
    return re.sub(r"\s+", " ", key).strip()


def _split_ru_field(ru_field):
    # Кроме запятых/слэшей/точек с запятой в словаре встречаются пары фраз
    # через вопросительный или восклицательный знак: "Как дела? Как поживаешь?".
    # Не разбиваем знаками препинания внутри скобок, чтобы не ломать пояснения
    # вроде "Пруссия (Балтийская, без Бранденбурга и Поммерании), Пруса".
    parts = []
    current = []
    depth = 0
    for ch in ru_field:
        if ch in "([{":
            depth += 1
            current.append(ch)
        elif ch in ")]}":
            depth = max(0, depth - 1)
            current.append(ch)
        elif depth == 0 and ch in ",/;!?":
            part = "".join(current).strip()
            if part:
                parts.append(part)
            current = []
        else:
            current.append(ch)
    part = "".join(current).strip()
    if part:
        parts.append(part)
    return parts or [ru_field]


def _clean_pr_phrase(text):
    """Нормализует прусскую фразу для поиска многословных заголовков.
    В отличие от простого lower(), убирает конечную пунктуацию и схлопывает
    пробелы, чтобы 'Kāigi tebbei ēit?' находилось по токенам без вопроса."""
    text = re.sub(r"[^\wāēīōūâêîôûàèìòùáéíóúŠšČčŽž-]+", " ", text, flags=re.UNICODE)
    return re.sub(r"\s+", " ", text).strip().lower()


def _norm_pr_key(text):
    """Ключ прусской фразы для поиска в фразбуке.

    Отличие от _clean_pr_phrase: тире, стоящее отдельным словом, схлопывается
    так же, как запятая, — «As bilāi: - Kāigi» и «As bilāi Kāigi» дают один ключ.
    """
    key = _clean_pr_phrase(text)
    while " - " in key:
        key = key.replace(" - ", " ")
    return key.strip()


def _expand_pr_slash_alternatives(form):
    """Разворачивает варианты через слэш в таблицах форм.

    В overrides часто встречается "a / b", а иногда "aux a / b". Если
    индексировать такую строку только целиком, пользовательский ввод одного
    варианта не находится. Для "asma aulaūwuns / aulaūwusi" добавляем и
    "asma aulaūwuns", и "asma aulaūwusi".
    """
    form = (form or "").strip()
    if not form:
        return []
    if "/" not in form:
        return [form]

    parts = [p.strip() for p in form.split("/") if p.strip()]
    if not parts:
        return [form]

    out = [form]
    first_words = parts[0].split()
    prefix = " ".join(first_words[:-1]) if len(first_words) > 1 else ""
    for idx, part in enumerate(parts):
        alt = part
        if idx > 0 and prefix and len(part.split()) == 1:
            alt = f"{prefix} {part}"
        if alt not in out:
            out.append(alt)
    return out


def _iter_pr_form_keys(form):
    seen = set()
    for alt in _expand_pr_slash_alternatives(form):
        for key in (alt.lower(), _clean_pr_phrase(alt)):
            if key and key not in seen:
                seen.add(key)
                yield key


def _load_phrasebook(phrasebook_json_str):
    """Загружает таблицу устойчивых выражений и готовых пар корпуса.

    Формат намеренно простой: список объектов с полем ru (строка или список
    строк), pr/out, необязательным ru_out и note. Русская сторона строит
    индекс RU -> PR, прусская - индекс PR -> RU, поэтому одна и та же
    статья работает в обоих направлениях.
    """
    if not phrasebook_json_str:
        return {}, {}, 1, 1
    try:
        data = json.loads(phrasebook_json_str)
    except Exception:
        return {}, {}, 1, 1
    if isinstance(data, dict):
        data = data.get("phrases", [])
    if not isinstance(data, list):
        return {}, {}, 1, 1

    phrases = {}
    pr_phrases = {}
    max_words = 1
    pr_max_words = 1
    for item in data:
        if not isinstance(item, dict):
            continue
        note = item.get("note") or "phrasebook"
        out = item.get("pr") or item.get("out") or item.get("to")
        if isinstance(out, list):
            # в данных 'pr' иногда лежит список вариантов — берём первый
            out = out[0] if out else ""
        out = str(out or "").strip()

        ru_values = item.get("ru") or item.get("source") or item.get("from")
        if isinstance(ru_values, str):
            ru_values = [ru_values]
        if not isinstance(ru_values, list):
            ru_values = []

        ru_out = item.get("ru_out")
        if isinstance(ru_out, list):
            ru_out = ru_out[0] if ru_out else ""
        ru_out = str(ru_out or "").strip()
        if not ru_out and ru_values:
            ru_out = str(ru_values[0]).strip()

        # RU -> PR: ключом служит каждая русская формулировка статьи.
        # Если статья заведена только со стороны PR (ru_out без ru), русский
        # текст тоже должен находиться - добавляем его в список ключей.
        if ru_out and ru_out not in ru_values:
            ru_values = ru_values + [ru_out]
        for ru in ru_values:
            key = _norm_ru_key(str(ru))
            if not key or not out:
                continue
            phrases[key] = {"out": out, "note": note}
            max_words = max(max_words, len(key.split()))

        # PR -> RU: ключом служит прусская фраза; перевод берём из ru_out,
        # а если его нет - из первой русской формулировки
        if out and ru_out:
            pr_key = _norm_pr_key(out)
            if pr_key and pr_key not in pr_phrases:
                pr_phrases[pr_key] = {"out": ru_out, "note": note, "src": out}
                pr_max_words = max(pr_max_words, len(pr_key.split()))
    return phrases, pr_phrases, max_words, pr_max_words


def _load_priorities(priorities_json_str):
    """Ручные приоритеты значений.

    Поддерживаем простой JSON:
    {
      "pr_to_ru": {"gints": "человек", "1957": "человек"},
      "ru_to_pr": {"тевтонский": ["Teutōtisks"]}
    }
    Первое поле меняет русский gloss статьи, второе влияет на выбор
    кандидата при RU -> PR.
    """
    if not priorities_json_str:
        return {}, {}
    try:
        data = json.loads(priorities_json_str)
    except Exception:
        return {}, {}
    if not isinstance(data, dict):
        return {}, {}

    pr_to_ru = {}
    raw_pr_to_ru = data.get("pr_to_ru") or data.get("gloss") or {}
    if isinstance(raw_pr_to_ru, dict):
        for key, value in raw_pr_to_ru.items():
            if value:
                pr_to_ru[str(key).lower()] = str(value)

    ru_to_pr = {}
    raw_ru_to_pr = data.get("ru_to_pr") or {}
    if isinstance(raw_ru_to_pr, dict):
        for ru, preferred in raw_ru_to_pr.items():
            key = _clean_ru_chunk(str(ru))
            if not key:
                continue
            if isinstance(preferred, str):
                preferred = [preferred]
            if isinstance(preferred, list):
                ru_to_pr[key] = [str(w).lower() for w in preferred if w]
    return pr_to_ru, ru_to_pr


def _collect_forms(node, label=""):
    """Рекурсивно собирает все прусские словоформы из paradigm/conjugation
    вместе с грамматической меткой (путь по ключам, плюс подпись лица для
    таблиц спряжения)."""
    out = []
    if isinstance(node, dict):
        if "f" in node and isinstance(node["f"], str):
            person = node.get("p")
            full_label = f"{label} {person}".strip() if person else label
            out.append((node["f"], full_label))
            return out
        for k, v in node.items():
            if k in ("g", "s", "title", "p"):
                continue
            out.extend(_collect_forms(v, f"{label}.{k}" if label else k))
    elif isinstance(node, list):
        for item in node:
            out.extend(_collect_forms(item, label))
    elif isinstance(node, str):
        if node.strip():
            out.append((node, label))
    return out


def _synthesize_fresh_entries(dictionary, overrides):
    """Повторяет логику 'fresh entry' из applyOverrides() в app.js: override
    с полем 'word', для которого нет ни совпадения по id, ни по headword,
    становится самостоятельной словарной статьёй (teutōtisks, plastātun и
    т.п.), а не просто патчем существующей. Без этого такие слова были
    видны на сайте, но непереводимы в обе стороны переводчиком."""
    by_word = {}
    for e in dictionary:
        by_word.setdefault((e.get("w") or "").lower(), []).append(e)
    by_id = {e.get("i"): e for e in dictionary}

    fresh = []
    for ov in overrides:
        word = ov.get("word")
        if not word:
            continue
        ov_id = ov.get("id")
        if ov_id is not None and ov_id in by_id:
            continue  # патч существующей записи по id
        if by_word.get(word.lower()):
            continue  # патч существующей записи по headword
        key = word.lower()
        entry = {
            "i": "new-" + key,
            "w": word,
            "l": (ov.get("letter") or word[0]).upper(),
            "f": ov.get("forms", ""),
            "x": bool(ov.get("is_form")),
            "b": ov.get("base_word", ""),
            "g": ov.get("grammar_note", ""),
            "s": ov.get("source") or "добавлено вручную",
            "ru": ov.get("ru", ""),
            "lt": ov.get("lt", ""),
            "lv": ov.get("lv", ""),
            "de": ov.get("de", ""),
            "en": ov.get("en", ""),
            "pl": ov.get("pl", ""),
        }
        fresh.append((entry, ov))
    return fresh


def _load_verb_frames(verb_frames_json_str):
    """Аудит, П.1.2: управление глаголов из verb_frames.json.

    Формат: {"wīdātun": {"ru": "видеть", "transitive": true, "object_case": "akk"}}.
    Используется как авторитетный источник переходности вместо pymorphy-тега
    русского глагола (который может не совпадать у видовых пар).
    """
    if not verb_frames_json_str:
        return {}
    try:
        data = json.loads(verb_frames_json_str)
    except Exception:
        return {}
    if not isinstance(data, dict):
        return {}
    frames = {}
    for word, fr in data.items():
        if isinstance(fr, dict):
            frames[str(word).lower()] = {
                "ru": fr.get("ru", ""),
                "transitive": bool(fr.get("transitive")),
                "object_case": fr.get("object_case"),
            }
    return frames


def _load_sentence_memory(sentence_memory_json_str):
    """Аудит, П.2.1: полные проверенные предложения корпуса — отдельно от
    фразбука. Применяются ТОЛЬКО при полном совпадении всей фразы и явно
    помечаются в диагностике как «готовый перевод корпуса».

    Возвращает (ru->pr, pr->ru, pr_folded, max_words).
    """
    if not sentence_memory_json_str:
        return {}, {}, {}, 1
    try:
        data = json.loads(sentence_memory_json_str)
    except Exception:
        return {}, {}, {}, 1
    if isinstance(data, dict):
        data = data.get("sentences", [])
    if not isinstance(data, list):
        return {}, {}, {}, 1

    ru_sm = {}
    pr_sm = {}
    max_words = 1
    for item in data:
        if not isinstance(item, dict):
            continue
        out = item.get("pr") or item.get("out") or item.get("to")
        if isinstance(out, list):
            out = out[0] if out else ""
        out = str(out or "").strip()
        ru_values = item.get("ru") or item.get("source") or item.get("from")
        if isinstance(ru_values, str):
            ru_values = [ru_values]
        if not isinstance(ru_values, list):
            ru_values = []
        ru_out = item.get("ru_out")
        if isinstance(ru_out, list):
            ru_out = ru_out[0] if ru_out else ""
        ru_out = str(ru_out or "").strip()
        if ru_out and ru_out not in ru_values:
            ru_values = ru_values + [ru_out]
        # RU → PR: только полное совпадение фразы
        for ru in ru_values:
            key = _norm_ru_key(str(ru))
            if key and out and key not in ru_sm:
                ru_sm[key] = {"out": out, "note": "готовый перевод корпуса"}
                max_words = max(max_words, len(key.split()))
        # PR → RU
        pr_key = _norm_pr_key(out) if out else ""
        if pr_key and ru_out and pr_key not in pr_sm:
            pr_sm[pr_key] = {"out": ru_out, "note": "готовый перевод корпуса"}
    pr_sm_folded = {}
    for k, v in pr_sm.items():
        pr_sm_folded.setdefault(fold_diacritics(k), v)
    return ru_sm, pr_sm, pr_sm_folded, max_words


def load_data(dictionary_json_str, overrides_json_str, phrasebook_json_str=None, priorities_json_str=None, propernames_json_str=None, verb_frames_json_str=None, sentence_memory_json_str=None):
    global _ru_index, _override_by_id, _preposition_index, _pr_preposition_senses, _phrasebook, _pr_phrasebook, _pr_phrasebook_folded, _pr_phrasebook_max_words, _pr_to_ru_priority, _ru_to_pr_priority, _ru_max_phrase_words, _pr_index, _pr_index_folded, _pr_max_phrase_words, _entry_freq, _headword_index, _propernames, _propername_lemma_index, _propername_form_index, _verb_frames, _sentence_memory, _pr_sentence_memory, _pr_sentence_memory_folded, _pr_sentence_memory_max_words
    dictionary = json.loads(dictionary_json_str)
    overrides = json.loads(overrides_json_str)
    (_phrasebook, _pr_phrasebook, phrasebook_max_words,
     pr_phrasebook_max_words) = _load_phrasebook(phrasebook_json_str)
    _pr_phrasebook_folded = {}
    for _pr_key, _pr_value in _pr_phrasebook.items():
        _pr_phrasebook_folded.setdefault(fold_diacritics(_pr_key), _pr_value)
    _pr_phrasebook_max_words = pr_phrasebook_max_words
    _pr_to_ru_priority, _ru_to_pr_priority = _load_priorities(priorities_json_str)
    _verb_frames = _load_verb_frames(verb_frames_json_str)
    (_sentence_memory, _pr_sentence_memory, _pr_sentence_memory_folded,
     _pr_sentence_memory_max_words) = _load_sentence_memory(sentence_memory_json_str)
    # Аудит, П.2.1: данные разделены по файлам, но предложения корпуса также
    # участвуют в поиске подфраз внутри длинного текста (как раньше, когда они
    # лежали в phrasebook) — с явной пометкой «готовый перевод корпуса».
    # Это сохраняет перевод склеенных реплик и прозрачность диагностики.
    for _sm_key, _sm_val in _sentence_memory.items():
        _phrasebook.setdefault(_sm_key, _sm_val)
    for _sm_key, _sm_val in _pr_sentence_memory.items():
        _pr_phrasebook.setdefault(_sm_key, _sm_val)
        _pr_phrasebook_folded.setdefault(fold_diacritics(_sm_key), _sm_val)
    phrasebook_max_words = max(phrasebook_max_words, _pr_sentence_memory_max_words)
    pr_phrasebook_max_words = max(pr_phrasebook_max_words, _pr_sentence_memory_max_words)
    _pr_phrasebook_max_words = pr_phrasebook_max_words
    _build_propername_index(propernames_json_str)

    _override_by_id = {o["id"]: o for o in overrides if "id" in o}

    fresh_entries = _synthesize_fresh_entries(dictionary, overrides)
    for entry, ov in fresh_entries:
        dictionary.append(entry)
        _override_by_id[entry["i"]] = ov

    ru_index = {}
    ru_max_phrase_words = 1
    for e in dictionary:
        ru_field = e.get("ru", "")
        if not ru_field:
            continue
        for raw_chunk in _split_ru_field(ru_field):
            chunk = _clean_ru_chunk(raw_chunk)
            if chunk:
                ru_index.setdefault(chunk, []).append(e)
                if " " in chunk:
                    ru_max_phrase_words = max(ru_max_phrase_words, len(chunk.split()))
    # В исходном словаре некоторые формы местоимений вынесены как cross-ref
    # без русского gloss (например, tenēi "они"). Добавляем безопасные
    # лемматические алиасы, чтобы pymorphy3 мог склонять их через overrides.
    by_headword = {e.get("w"): e for e in dictionary}
    _headword_index = {(e.get("w") or "").lower(): e for e in dictionary if e.get("w")}
    if "они" not in ru_index and by_headword.get("tāns"):
        ru_index["они"] = [by_headword["tāns"]]
    if "этот" in ru_index:
        for alias in ("это", "эта", "эти"):
            if alias not in ru_index:
                ru_index[alias] = ru_index["этот"]
    if "свой" in ru_index:
        for alias in ("своя", "свое", "своё", "свои"):
            if alias not in ru_index:
                ru_index[alias] = ru_index["свой"]

    # Нормализация ё↔е: pymorphy3 всегда возвращает лемму через "ё"
    # (лёгкий, мёртвый, тяжёлый, берёза, объём...), а в словаре Prūsiska bilā
    # переводы записаны через "е" (легкий, мертвый, тяжелый, береза, объем...).
    # Без этого 142 статьи не находятся при вводе русского слова. Добавляем
    # дублирующие ключи с правильной заменой 'е' → 'ё' только для слогов с
    # ударением (используем словарь pymorphy3 для проверки: если для слова
    # через 'е' pymorphy даёт лемму с 'ё', значит так и нужно индексировать).
    import pymorphy3 as _pm3
    _morph_local = _pm3.MorphAnalyzer()
    yo_keys = {}
    for k, v in list(ru_index.items()):
        if "е" not in k or " " in k:
            continue
        # Пробуем, что pymorphy думает про слово через 'е'
        # Если лемма содержит 'ё', создаём дублирующий ключ с заменой.
        p = _morph_local.parse(k)
        if not p:
            continue
        lemma = p[0].normal_form
        if "ё" not in lemma:
            continue
        # Сопоставляем позиции 'е' и 'ё' по длине — pymorphy3 обычно просто
        # меняет конкретные позиции, но для безопасности сравниваем лемму с
        # заменой всех 'е' на 'ё' и берём лемму, если они совпадают по длине.
        if len(lemma) == len(k):
            yo_key = lemma  # берём точную лемму pymorphy3
            if yo_key != k and yo_key not in ru_index and yo_key not in yo_keys:
                yo_keys[yo_key] = v
    ru_index.update(yo_keys)

    _ru_index = ru_index
    _ru_max_phrase_words = max(ru_max_phrase_words, phrasebook_max_words)

    preposition_index = {}
    pr_preposition_senses = {}
    for e in dictionary:
        s = e.get("s", "")
        if "prp" not in set(re.findall(r"[a-z]+", s.lower())):
            continue
        gov = "akk"
        gm = re.search(r"\b(acc|dat|gen)\b", s.lower())
        if gm:
            gov = RU_CASE_MARKER_TO_LOCAL[gm.group(1)]
        pr_preposition_senses.setdefault((e.get("w") or "").lower(), []).append({"entry": e, "gov": gov})
        ru_field = e.get("ru", "")
        for raw_chunk in _split_ru_field(ru_field):
            chunk_clean = _clean_ru_chunk(raw_chunk)
            if chunk_clean:
                # marker описывает русский падеж в помете словаря ("в acc" vs
                # "в loc"); gov — падеж, которым управляет прусский предлог.
                marker = _ru_case_marker_from_chunk(raw_chunk)
                preposition_index.setdefault(chunk_clean, []).append({
                    "word": e.get("w"),
                    "gov": gov,
                    "ru_case": marker,
                    "entry": e,
                })
    _preposition_index = preposition_index
    _pr_preposition_senses = pr_preposition_senses

    pr_index = {}
    pr_max_phrase_words = 1

    def add_pr_form(entry, form, label):
        nonlocal pr_max_phrase_words
        for key in _iter_pr_form_keys(form):
            pr_index.setdefault(key, []).append((entry, label))
            if " " in key:
                pr_max_phrase_words = max(pr_max_phrase_words, len(key.split()))

    for e in dictionary:
        headword = e.get("w", "")
        if headword:
            add_pr_form(e, headword, "")
        override = _override_by_id.get(e["i"])
        if override:
            for form, label in _collect_forms(override.get("paradigm")):
                add_pr_form(e, form, label)
            for form, label in _collect_forms(override.get("conjugation")):
                add_pr_form(e, form, label)
    _pr_index = pr_index
    _pr_max_phrase_words = max(pr_max_phrase_words, _pr_phrasebook_max_words)

    pr_index_folded = {}
    for form_lower, matches in pr_index.items():
        pr_index_folded.setdefault(fold_diacritics(form_lower), []).extend(matches)
    _pr_index_folded = pr_index_folded

    # Частоты статей по корпусу фразбука. Считаем по словоформам, а не по
    # заголовкам: «waīda» и «widāwuns» должны отдавать вес статье wīdātun,
    # хотя её инфинитива в тексте может не быть ни разу.
    #
    # Аудит v12 (фикс бага _lookup_pr_matches): одна словарная статья с
    # парадигмой добавляется в pr_index[multiple] — по одной записи на
    # каждую клетку парадигмы, даже если форма совпадает («dis» как
    # masc.sg.nom и fem.sg.nom; «di» — 10 клеток для di + 8 клеток для
    # dis через омонимию клитики). Раньше freq засчитывалась за КАЖДУЮ
    # запись, поэтому один токен «di» в корпусе поднимал freq[dis]
    # сразу на 8, и dis выигрывал у tāns для местоимения «Он». Дедуп по
    # entry.i внутри токена чинит это, не трогая _lookup_pr_matches
    # (дубликаты label нужны для _select_pr_match — там разные падежи
    # = разные интерпретации одной и той же формы).
    corpus_tokens = {}
    for corpus_key in _pr_phrasebook:
        for token in corpus_key.split():
            if token:
                corpus_tokens[token] = corpus_tokens.get(token, 0) + 1
    entry_freq = {}
    for token, count in corpus_tokens.items():
        seen_ids = set()
        for entry, _label in _lookup_pr_matches(token):
            eid = entry.get("i")
            if eid in seen_ids:
                continue
            seen_ids.add(eid)
            entry_freq[eid] = entry_freq.get(eid, 0) + count
    _entry_freq = entry_freq

    return {"words": len(dictionary), "overrides": len(_override_by_id), "prepositions": len(preposition_index), "phrases": len(_phrasebook) + len(_pr_phrasebook), "propernames": len(_propernames), "verb_frames": len(_verb_frames), "sentence_memory": len(_sentence_memory) + len(_pr_sentence_memory)}


def _derive_loc_from_gen(gen_form):
    """Локатив из генитива: парадигмы его не содержат (только nom/gen/dat/akk).

    Правило проверено на формах из корпуса: gen «Leītawas» → loc «Leītawai»
    ("... en Leītawai"), gen «wīrdas» → loc «wīrdai», gen «widzemes» →
    loc «widzemei» ("en widzemei"). Основы -a- дают -ai, основы -e-/-i- — -ei.
    """
    if not isinstance(gen_form, str):
        return None
    form = gen_form.strip()
    if not form or " " in form:
        return None
    if form.endswith("as"):
        return form[:-2] + "ai"
    if form.endswith(("es", "is")):
        return form[:-2] + "ei"
    if form.endswith("s"):
        return form[:-1] + "ai"
    return None


def pick_noun_form(override, gender_guess, number, case):
    para = override.get("paradigm")
    if not isinstance(para, dict):
        return None
    for g in [gender_guess] + [x for x in ("masc", "fem", "neut") if x != gender_guess]:
        gv = para.get(g)
        if not isinstance(gv, dict):
            continue
        nv = gv.get(number)
        if isinstance(nv, dict) and nv.get(case):
            return nv[case]
        # У прилагательных локатива нет; в корпусе на его месте стоит
        # форма, совпадающая с дативом ("en kawīdsmu deīktu"), её и берём.
        if case == "loc" and isinstance(nv, dict) and nv.get("dat"):
            return nv["dat"]
    return None


def pick_adj_form(override, gender_guess, number, case, degree="positive"):
    para = override.get("paradigm")
    if not isinstance(para, dict):
        return None
    deg = para.get(degree) or para.get("positive")
    if not isinstance(deg, dict):
        return None
    for g in [gender_guess] + [x for x in ("masc", "fem", "neut") if x != gender_guess]:
        gv = deg.get(g)
        if not isinstance(gv, dict):
            continue
        nv = gv.get(number)
        if isinstance(nv, dict) and nv.get(case):
            return nv[case]
        # Локатив в данных отсутствует — выводим его из генитива того же
        # числа, но только для единственного: форм мн. ч. в корпусе нет,
        # и придумывать их не из чего.
        if case == "loc" and number == "sg" and isinstance(nv, dict):
            derived = _derive_loc_from_gen(nv.get("gen"))
            if derived:
                return derived
    return None


def pick_verb_form(override, person, number, tense):
    conj = override.get("conjugation")
    if not isinstance(conj, dict):
        return None
    indic = conj.get("indicative")
    if not isinstance(indic, dict):
        return None
    rows = indic.get(TENSE_MAP.get(tense))
    if not isinstance(rows, list):
        return None
    try:
        idx = PERSON_ORDER.index((person, number))
    except ValueError:
        return None
    return rows[idx].get("f") if idx < len(rows) else None


def pymorphy_pos_to_local(tag):
    for key, val in PYMORPHY_TO_LOCAL.items():
        if key in tag:
            return val
    return None


# Аудит, П.1.5: причины последнего выбора кандидата — для режима диагностики.
# Заполняется choose_candidate, читается _translate_word_info для note.
_last_choose_reasons = []


def choose_candidate(candidates, wanted_pos, ru_key=None):
    """Выбирает наиболее подходящую словарную статью.

    Раньше выбор был просто "первое совпадение нужной части речи", из-за чего
    часто выигрывали омонимы без парадигмы. Теперь при прочих равных
    предпочитаем точную часть речи, ручной приоритет и наличие override —
    такую статью можно склонять/спрягать.

    Аудит, П.1.3: причины выбора (reasons) сохраняются в _last_choose_reasons
    и показываются в диагностической таблице — видно, ПОЧЕМУ выбрана статья.
    """
    global _last_choose_reasons
    preferred = _ru_to_pr_priority.get(_clean_ru_chunk(ru_key or ""), [])
    scored = []
    for order, e in enumerate(candidates):
        override = _override_by_id.get(e["i"])
        pos = classify_pos(e, override)
        pos_match = (wanted_pos is None) or (pos == wanted_pos)
        # pymorphy3 помечает притяжательные местоимения (мой/моя/моё) как ADJF,
        # а в словаре они могут быть pn. Считаем это совместимым.
        compatible_pronoun = wanted_pos == "ADJF" and pos == "NPRO"
        w_lower = (e.get("w") or "").lower()
        priority = preferred.index(w_lower) if w_lower in preferred else 10_000
        # Статья, у которой глосс ровно этот русский смысл, точнее статьи с
        # набором «он, она, тот, та». Сравниваем первый смысл, а не всю строку.
        first_gloss = _clean_ru_chunk((e.get("ru") or "").split(",")[0])
        exact_gloss = 0 if first_gloss and first_gloss == _clean_ru_chunk(ru_key or "") else 1
        # Частота в корпусе: живой текст важнее порядка в файле. Порог 50
        # чтобы одна очень частая статья не забивала всё остальное.
        freq = min(_entry_freq.get(e["i"], 0), 50)
        score = (
            0 if pos_match or compatible_pronoun else 1,
            priority,
            exact_gloss,
            -freq,
            0 if override else 1,
            order,
        )
        scored.append((score, e, override))
    scored.sort(key=lambda t: t[0])
    # Аудит, П.1.5: цепочка решения для диагностики
    best_score, best_e, best_override = scored[0]
    reasons = []
    if best_score[0] == 0:
        reasons.append(f"pos={wanted_pos or 'any'}")
    if best_score[1] < 10_000:
        reasons.append("priority")
    if best_score[2] == 0:
        reasons.append("exact-gloss")
    if best_score[3] < 0:
        reasons.append(f"freq={-best_score[3]}")
    if best_score[4] == 0:
        reasons.append("has-paradigm")
    _last_choose_reasons = reasons
    return best_e, best_override


def _preferred_gender_for_override(override, fallback_gender):
    """Пол прусского слова лучше брать из его собственной парадигмы.
    Например, русский "дом" masc, но прусский buttan — neut; прилагательное
    должно согласоваться с buttan, а не с русским родом.
    """
    if not override:
        return fallback_gender
    para = override.get("paradigm")
    if not isinstance(para, dict):
        return fallback_gender
    if "positive" in para and isinstance(para.get("positive"), dict):
        para = para["positive"]
    genders = [g for g in ("masc", "fem", "neut") if isinstance(para.get(g), dict)]
    if len(genders) == 1:
        return genders[0]
    return fallback_gender if fallback_gender in genders else (genders[0] if genders else fallback_gender)


def _declension_picker(wanted_pos, override):
    para = override.get("paradigm") if override else None
    # Прилагательные имеют уровни positive/comparative/..., местоимения и
    # существительные — сразу masc/fem/neut. Для ADJF без positive (мой -> majs)
    # используем именную парадигму.
    if wanted_pos in ("ADJF", "PRTF") and isinstance(para, dict) and "positive" in para:
        return pick_adj_form
    return pick_noun_form


def _parse_ru(clean):
    """Умный выбор pymorphy3-parse: перебираем parses и предпочитаем тот,
    чья лемма в _ru_index с override (можно склонять).

    Чинит pymorphy3-омонимию типа:
    - 'большая' → pymorphy[0].lemma = 'больший' (компаратив!), а не 'большой'
    - 'большую' → pymorphy[0].lemma = 'больший'
    - 'большие' → pymorphy[0].lemma = 'больший'
    - 'старое' → pymorphy[0].lemma = 'старое' (сущ.), а не 'старый' (прил.)
    """
    parses = morph.parse(clean)
    if not parses:
        return None
    # 1) ищем parse с леммой, у которой есть override (можно склонять)
    for p in parses:
        cands = _ru_index.get(p.normal_form) or _ru_index.get(clean)
        if cands:
            _, override = choose_candidate(cands, pymorphy_pos_to_local(str(p.tag)) or "NOUN", p.normal_form)
            if override and (override.get("paradigm") or override.get("conjugation")):
                return p
    # 2) иначе берём первый parse, чья лемма просто есть в словаре
    for p in parses:
        cands = _ru_index.get(p.normal_form) or _ru_index.get(clean)
        if cands:
            return p
    # 3) фоллбэк — первый parse (как было раньше)
    return parses[0]


# Русские глаголы-омонимы, у которых pymorphy3 часто даёт не ту лемму [0]:
#   "стоит" → pymorphy[0].lemma = "стоить", но в большинстве контекстов
#   (дом стоит, стол стоит, человек стоит) имеется в виду "стоять".
#   "стою/стоим" → "стоить" в [0], но в большинстве контекстов "стоять".
# Эти глаголы различаются по контексту: "стоять" - о положении, "стоить" - о цене.
# Контекстные подсказки для выбора леммы:
_STANDING_CONTEXT_NOUNS = {
    # существительные, после которых "стоит/стою/стоим" = "стоять"
    # здания и объекты
    "дом", "стол", "стул", "кресло", "шкаф", "дверь", "окно", "здание",
    "башня", "стена", "забор", "ворота", "машина", "автомобиль", "корабль",
    "лодка", "дерево", "столб", "флаг", "часы", "картина", "ваза",
    "цветок", "растение", "памятник", "статуя", "колонна", "арка",
    "крыльцо", "лестница",
    # деревья (часто "берёза стоит", "дуб стоит" — о положении в лесу/поле)
    "берёза", "береза", "дуб", "сосна", "ель", "пихта", "клён", "клен",
    "ива", "тополь", "осина", "каштан", "липа", "рябина", "яблоня",
    "вишня", "груша", "слива", "ольха", "ясень", "бук", "граб",
    # люди и животные
    "человек", "люди", "мужчина", "женщина", "ребёнок", "дети",
    "брат", "сестра", "отец", "мать", "сын", "дочь", "друг", "враг",
    "воин", "солдат", "офицер", "царь", "король", "князь",
    "священник", "учитель", "ученик", "часовой",
    "конь", "лошадь", "корова", "собака", "кошка", "птица",
    "волк", "медведь", "заяц", "лиса", "олень", "кабан",
    # Местоимения-подлежащие, после которых "стою/стоим" = "стоять"
    "я", "ты", "он", "она", "оно", "мы", "вы", "они",
    # Наречия места, рядом с которыми "стоит" = "стоять"
    "здесь", "там", "тут", "вверху", "внизу",
    "рядом", "около", "возле", "между",
}
_PRICE_CONTEXT_WORDS = {
    # слова, рядом с которыми "стоит" = "стоить"
    "сколько", "дорого", "дёшево", "дорогой", "дешёвый", "цена", "цен",
    "рубл", "доллар", "евро", "копе", "цент", "марка", "злот",
    "деньги", "денег", "денег", "стоимость", "оплата", "платёж",
    "билет", "товар", "продукт", "покупка", "покуп", "продаю", "продаёт",
    "много", "мало", "дешевле", "дороже",
}
# Пары лемм, которые pymorphy3 путает местами. Ключ — лемма[0], значение —
# альтернативная лемма, которую надо попробовать, если контекст подходит.
_VERB_OMOGRAPH_PAIRS = {
    "стоить": "стоять",   # "стоит/стою/стоим" в основном = "стоять"
    "лежать": "лежать",   # безопасно
    "сидеть": "сидеть",   # безопасно
}


def _smart_parse_with_context(tokens, idx, clean):
    """Умный выбор parse pymorphy3 с учётом контекста омонимов.

    Для омографов типа "стоит" (стоить vs стоять) проверяет окружающие слова:
    если рядом есть существительное положения (дом, стол, человек) — берём "стоять";
    если рядом есть слова цены (дорого, сколько, цена) — берём "стоить".
    Возвращает parse или None (если нет контекстной подсказки).
    """
    parses = morph.parse(clean)
    if not parses:
        return None
    # Ищем леммы всех parses
    lemmas = [p.normal_form for p in parses]
    # Если есть омограф-конкурент
    primary_lemma = lemmas[0]
    alt_lemma = _VERB_OMOGRAPH_PAIRS.get(primary_lemma)
    if not alt_lemma or alt_lemma == primary_lemma:
        return None
    if alt_lemma not in lemmas:
        return None
    # Проверяем контекст: соседние 3 слова в обе стороны
    context_words = []
    for j in range(max(0, idx - 3), min(len(tokens), idx + 4)):
        if j == idx:
            continue
        tok = tokens[j]
        clean_tok = _clean_ru_token(tok)
        if clean_tok:
            context_words.append(clean_tok.lower())
    # Ищем контекстные подсказки
    has_standing_context = any(w in _STANDING_CONTEXT_NOUNS for w in context_words)
    has_price_context = any(w in _PRICE_CONTEXT_WORDS for w in context_words)
    if has_standing_context and not has_price_context:
        # выбираем parse с леммой alt_lemma
        for p in parses:
            if p.normal_form == alt_lemma:
                return p
    if has_price_context and not has_standing_context:
        # остаётся primary_lemma (pymorphy[0])
        return parses[0]
    return None


def _local_pos_for_parse(parse):
    return pymorphy_pos_to_local(str(parse.tag)) or "NOUN"


def _grammemes_from_parse(parse, forced_case=None, agreement=None):
    tag = parse.tag
    gender_guess = GENDER_MAP.get(tag.gender, "masc")
    number = NUMBER_MAP.get(tag.number, "sg")
    case = forced_case or CASE_MAP.get(tag.case)
    if agreement:
        gender_guess = agreement.get("gender") or gender_guess
        number = agreement.get("number") or number
        case = agreement.get("case") or case
    return gender_guess, number, case


def _preposition_key(clean):
    return clean if clean in _preposition_index else PREPOSITION_ALIASES.get(clean)


def _prefer_corpus_form(choices):
    """Среди равнозначных вариантов берёт тот, что встречается в корпусе.

    Словарь даёт «ēn» (с макроном) и «en»; живой текст последовательно пишет
    «en». Порядок в файле об этом ничего не знает, частота знает.
    """
    if len(choices) < 2:
        return choices[0]
    best = max(choices, key=lambda c: _entry_freq.get((c.get("entry") or {}).get("i"), 0))
    if _entry_freq.get((best.get("entry") or {}).get("i"), 0) > 0:
        return best
    return choices[0]


def _select_preposition(clean, next_parse=None):
    key = _preposition_key(clean)
    if not key or key not in _preposition_index:
        return None
    choices = _preposition_index[key]

    # Варианты одного и того же предлога в словаре различаются написанием
    # (ēn/en) и пометкой падежа. Сначала сужаем набор до форм, которые реально
    # встречаются в корпусе: «en» — то, как пишет текст, «ēn» — как в словаре.
    attested = [c for c in choices
                if _entry_freq.get((c.get("entry") or {}).get("i"), 0) > 0]
    pool = attested or choices

    preferred = _ru_to_pr_priority.get(key, [])
    for pref in preferred:
        for choice in pool:
            if (choice.get("word") or "").lower() == pref:
                return choice
    if next_parse is not None:
        ru_case = PYMORPHY_CASE_TO_RU_MARKER.get(next_parse.tag.case)
        if ru_case:
            matching = [c for c in pool if c.get("ru_case") == ru_case]
            if matching:
                return matching[0]
            local_case = CASE_MAP.get(next_parse.tag.case)
            if local_case:
                matching = [c for c in pool if c.get("gov") == local_case]
                if matching:
                    return matching[0]
            # Смысл с нужным падежом в словаре есть, но его написание в
            # корпусе не встречается (у en засвидетельствован только akk-смысл,
            # loc-смысл записан как ēn). Берём управление у нужного смысла,
            # а написание — у формы из корпуса: "en Leītawai", не "ēn Leītawai".
            fallback_sense = [c for c in choices if c.get("ru_case") == ru_case]
            if not fallback_sense and local_case:
                fallback_sense = [c for c in choices if c.get("gov") == local_case]
            if fallback_sense and attested:
                merged = dict(fallback_sense[0])
                merged["word"] = attested[0].get("word") or merged.get("word")
                return merged
            # пометки падежа нет (en), но такая форма в корпусе — берём её
            if attested:
                return attested[0]
    return pool[0]


def _next_word_parse(tokens, start_idx, max_words=5):
    """Ищет разбор управляемого слова после предлога.

    Для "в большом доме" нельзя смотреть только на первое слово после
    предлога: это прилагательное, и его изолированный разбор бывает
    неоднозначен. Поэтому предпочитаем ближайшее существительное/местоимение,
    а первый разбор держим только как запасной вариант.
    """
    seen_words = 0
    first_parse = None
    for j in range(start_idx + 1, len(tokens)):
        tok = tokens[j]
        if PUNCT_TOKEN_RE.match(tok):
            return first_parse
        if not WORD_TOKEN_RE.match(tok):
            continue
        seen_words += 1
        clean = _clean_ru_token(tok)
        if clean:
            parse = _parse_ru(clean)
            if first_parse is None:
                first_parse = parse
            if _local_pos_for_parse(parse) in ("NOUN", "NPRO"):
                return parse
        if seen_words >= max_words:
            break
    return first_parse


def _agreement_from_following(tokens, start_idx, forced_case=None, max_words=5):
    """Согласование прилагательного/местоимения с ближайшим существительным.

    pymorphy3 без контекста часто разбирает формы вроде "молодой" как
    femn/gent или loct. Смотрим на следующее существительное и используем его
    число/падеж, а род — по возможности из выбранного прусского слова.
    """
    seen_words = 0
    for j in range(start_idx + 1, len(tokens)):
        tok = tokens[j]
        if PUNCT_TOKEN_RE.match(tok):
            return None
        if not WORD_TOKEN_RE.match(tok):
            continue
        seen_words += 1
        clean = _clean_ru_token(tok)
        if not clean:
            continue
        if _preposition_key(clean):
            return None
        parse = _parse_ru(clean)
        pos = _local_pos_for_parse(parse)
        if pos in ("VERB", "PREP", "CONJ", "PRCL", "INTJ", "ADVB"):
            return None
        if pos in ("NOUN", "NPRO"):
            lemma = parse.normal_form
            candidates = _ru_index.get(lemma) or _ru_index.get(clean)
            override = None
            if candidates:
                _, override = choose_candidate(candidates, pos, lemma)
            gender_guess = GENDER_MAP.get(parse.tag.gender, "masc")
            gender = _preferred_gender_for_override(override, gender_guess)
            number = NUMBER_MAP.get(parse.tag.number, "sg")
            case = forced_case or CASE_MAP.get(parse.tag.case) or "nom"
            return {"gender": gender, "number": number, "case": case}
        if seen_words >= max_words:
            return None
    return None


def _direct_object_case_for_parse(parse):
    """Возвращает akk для вероятного прямого дополнения после переходного
    глагола. Это исправляет русские омонимии nom/acc и gen/acc: "вижу дом",
    "вижу молодого человека". Явные dat/loct/ablt не трогаем.
    """
    pos = _local_pos_for_parse(parse)
    if pos not in ("NOUN", "NPRO", "ADJF", "PRTF"):
        return None
    if parse.tag.case in ("nomn", "gent", "accs"):
        return "akk"
    return None


def _subject_agreement_for_parse(parse):
    """Лицо/число ближайшего подлежащего для русских прошедших форм.
    В русском прошедшем времени лицо не выражено, а в прусской таблице оно
    есть: "мы были" должно брать 1pl, а не 3pl.
    """
    pos = _local_pos_for_parse(parse)
    if parse.tag.case not in ("nomn", None):
        return None
    number = "plur" if "plur" in parse.tag else "sing"
    person = next((p for p in ("1per", "2per", "3per") if p in parse.tag), None)
    if pos == "NPRO":
        person = person or "3per"
    elif pos == "NOUN":
        person = "3per"
    else:
        return None
    return {"person": person, "number": number}


# ---------------------------------------------------------------------------
# RU -> PR
# ---------------------------------------------------------------------------

def _translate_word_info(token, forced_case=None, agreement=None, preposition_choice=None, forced_case_reason=None, verb_agreement=None, parse_override=None):
    clean = _clean_ru_token(token)
    if not clean:
        return {"out": token, "note": None, "gov_case": None, "pos": None, "case_used": None, "consumes_case": False}

    phrase_override = _phrasebook.get(clean)
    if phrase_override:
        return {
            "out": phrase_override["out"],
            "note": phrase_override["note"],
            "gov_case": None,
            "pos": None,
            "case_used": None,
            "consumes_case": False,
        }

    if preposition_choice or _preposition_key(clean):
        choice = preposition_choice or _select_preposition(clean)
        if choice:
            return {
                "out": choice["word"],
                "note": f"предлог, управляет {choice['gov']}",
                "gov_case": choice["gov"],
                "pos": "PREP",
                "case_used": None,
                "consumes_case": False,
            }

    pn_out = _render_propername_ru_to_pr(clean, forced_case=forced_case, agreement=agreement)
    if pn_out:
        return {
            "out": pn_out,
            "note": "имя собственное (таблица PN)",
            "gov_case": None,
            "pos": "NPRO",
            "case_used": None,
            "consumes_case": False,
        }

    parse = parse_override if parse_override is not None else _parse_ru(clean)
    lemma = parse.normal_form
    tag = parse.tag
    wanted_pos = _local_pos_for_parse(parse)

    candidates = _ru_index.get(lemma) or _ru_index.get(clean)
    if not candidates:
        # Аудит, П.3.1: для неизвестного слова выводим исходное слово без [?]
        # в основном результате; техническая пометка — только в диагностике (П.3.2).
        return {"out": token, "note": "слово отсутствует в словаре", "gov_case": None, "pos": wanted_pos, "case_used": None, "consumes_case": wanted_pos in ("NOUN", "NPRO")}

    entry, override = choose_candidate(candidates, wanted_pos, lemma)
    base_form = entry.get("w")
    entry_pos = classify_pos(entry, override)
    # Аудит, П.1.5: цепочка решения в note — лемма + причины выбора кандидата.
    _choose_reasons = list(_last_choose_reasons)

    if override:
        if wanted_pos == "VERB" or entry_pos == "VERB":
            person = next((p for p in ("1per", "2per", "3per") if p in tag), None)
            number = "plur" if "plur" in tag else "sing"
            tense = "past" if "past" in tag else ("futr" if "futr" in tag else "pres")
            if verb_agreement and (person is None or tense == "past"):
                person = verb_agreement.get("person") or person
                number = verb_agreement.get("number") or number
            person = person or "3per"
            form = pick_verb_form(override, person, number, tense)
            if form:
                # Аудит, П.1.2: переходность берём из verb_frames.json по
                # прусской лемме (авторитетный источник), с фоллбэком на
                # pymorphy-тег русского глагола.
                frame = _verb_frames.get((base_form or "").lower())
                if frame is not None:
                    is_transitive = bool(frame.get("transitive"))
                else:
                    is_transitive = "tran" in tag
                return {
                    "out": form,
                    "note": f"{base_form}: {tense}/{person}/{number}" + (f" [{' '.join(_choose_reasons)}]" if _choose_reasons else ""),
                    "gov_case": None,
                    "pos": "VERB",
                    "case_used": None,
                    "consumes_case": False,
                    "is_transitive": is_transitive,
                }
        elif wanted_pos in ("NOUN", "ADJF", "PRTF", "NPRO") or entry_pos in ("NOUN", "ADJF", "NPRO"):
            gender_guess, number, case = _grammemes_from_parse(parse, forced_case, agreement)
            gender_guess = _preferred_gender_for_override(override, gender_guess) if entry_pos in ("NOUN", "NPRO") else gender_guess
            if case:
                picker = _declension_picker(wanted_pos, override)
                form = picker(override, gender_guess, number, case)
                if form:
                    if forced_case:
                        if forced_case_reason == "direct_object":
                            tail = " (прямое дополнение)"
                        else:
                            tail = " (падеж задан предлогом)"
                    elif agreement:
                        tail = " (согласовано с существительным)"
                    else:
                        tail = ""
                    return {
                        "out": form,
                        "note": f"{base_form}: {case}/{number}{tail}" + (f" [{' '.join(_choose_reasons)}]" if _choose_reasons else ""),
                        "gov_case": None,
                        "pos": entry_pos if entry_pos != "NOUN" else wanted_pos,
                        "case_used": case,
                        "consumes_case": (entry_pos in ("NOUN", "NPRO") and not (agreement and wanted_pos in ("ADJF", "PRTF"))),
                    }

    note = "словарная форма (без склонения)" if override else "нет парадигмы в overrides"
    return {"out": base_form or f"[{token}?]", "note": note, "gov_case": None, "pos": entry_pos, "case_used": None, "consumes_case": entry_pos in ("NOUN", "NPRO")}


def translate_word(token, forced_case=None):
    info = _translate_word_info(token, forced_case=forced_case)
    return info["out"], info["note"], info["gov_case"]


def _match_ru_phrase(tokens, start_idx):
    if _ru_max_phrase_words <= 1:
        return None

    # Фразы фразбука длиннее пары слов почти всегда содержат запятую. Собираем
    # слова, пропуская запятые и тире, и останавливаемся на границе фразы.
    pb_parts = []
    pb_positions = []
    j = start_idx
    while j < len(tokens) and len(pb_parts) < _ru_max_phrase_words:
        tok = tokens[j]
        if PUNCT_TOKEN_RE.match(tok):
            if tok in ".!?":
                break
            j += 1
            continue
        if not WORD_TOKEN_RE.match(tok):
            break
        clean = _clean_ru_token(tok)
        if not clean:
            break
        pb_parts.append(clean)
        pb_positions.append(j)
        j += 1
    for size in range(len(pb_parts), 1, -1):
        phrase = " ".join(pb_parts[:size])
        phrase_override = _phrasebook.get(phrase)
        if phrase_override:
            end_pos = pb_positions[size - 1]
            return {
                "end": end_pos + 1,
                "src": " ".join(tokens[start_idx:end_pos + 1]),
                "out": phrase_override["out"],
                "note": phrase_override["note"],
            }

    # Словарные многословные статьи - только по подряд идущим словам.
    parts = []
    positions = []
    j = start_idx
    while j < len(tokens) and len(parts) < _ru_max_phrase_words:
        tok = tokens[j]
        if PUNCT_TOKEN_RE.match(tok):
            break
        if WORD_TOKEN_RE.match(tok):
            clean = _clean_ru_token(tok)
            if not clean:
                break
            parts.append(clean)
            positions.append(j)
        else:
            break
        j += 1
    for size in range(len(parts), 1, -1):
        phrase = " ".join(parts[:size])
        candidates = _ru_index.get(phrase)
        if candidates:
            entry, _ = choose_candidate(candidates, None, phrase)
            return {
                "end": positions[size - 1] + 1,
                "src": " ".join(tokens[start_idx:positions[size - 1] + 1]),
                "out": entry.get("w") or phrase,
                "note": "многословная статья словаря",
            }
    return None


# ---------------------------------------------------------------------------
# Числительные
#
# В прусских образцах цифры сохраняются как есть ("en 1273 mettan", "750
# mettans"), поэтому «транслитерация» здесь — не запись числа словами, а
# передача управления: числительное диктует числу и падеж следующего
# существительного. Год ведёт себя как обычное слово в единственном числе,
# остальные числительные требуют множественного; родительный падеж, который в
# русском возникает после 5+, в образцах заменён винительным.
# ---------------------------------------------------------------------------

NUMERAL_TOKEN_RE = re.compile(r"^\d{1,9}$")
YEAR_MIN, YEAR_MAX = 1000, 2199
YEAR_LEMMAS = {"год", "года", "году", "годом", "годе", "лета", "лет"}


def _parse_numeral(tok):
    """Значение арабского числительного либо None."""
    t = tok.replace("\u00a0", "").replace(" ", "")
    if not NUMERAL_TOKEN_RE.match(t):
        return None
    return int(t)


def _numeral_governs(value, next_lemma):
    """(число, падеж-подсказка) для существительного после числительного."""
    if YEAR_MIN <= value <= YEAR_MAX and (next_lemma or "").lower() in YEAR_LEMMAS:
        return "sg", None
    if value == 1:
        return "sg", None
    return "pl", "akk"


def translate_sentence_json(sentence):
    # Готовая статья корпуса важнее пословного разбора: длинная фраза с
    # запятыми иначе разваливается на куски и переводится «по словам».
    whole_key = _norm_ru_key(sentence)
    # Аудит, П.2.1: сначала sentence_memory — полные проверенные предложения
    # корпуса. Явно помечаем «готовый перевод корпуса» в диагностике.
    sm_hit = _sentence_memory.get(whole_key) if whole_key else None
    if sm_hit:
        text = str(sm_hit["out"]).strip()
        return json.dumps({"translation": text, "words": [
            {"src": sentence.strip(), "out": text, "note": sm_hit["note"]}
        ]}, ensure_ascii=False)
    whole_hit = _phrasebook.get(whole_key) if whole_key else None
    if whole_hit:
        text = str(whole_hit["out"]).strip()
        return json.dumps({"translation": text, "words": [
            {"src": sentence.strip(), "out": text, "note": whole_hit["note"]}
        ]}, ensure_ascii=False)

    tokens = re.findall(r"[\wа-яёА-ЯЁ-]+|[^\w\s]", sentence, flags=re.UNICODE)
    out_words, debug = [], []
    pending_case = None          # управление ближайшим предлогом
    direct_object_pending = False  # после переходного глагола ждём дополнение
    subject_agreement = None      # ближайшее подлежащее для прошедших глаголов
    pending_numeral = None        # числительное, ждущее своё существительное
    i = 0
    while i < len(tokens):
        tok = tokens[i]
        if PUNCT_TOKEN_RE.match(tok):
            # Многословная словарная статья может уже содержать знак вопроса
            # или восклицания (например, "Kāigi tebbei ēit?"). Не дублируем
            # такой знак из исходного предложения.
            if not (out_words and str(out_words[-1]).endswith(tok)):
                out_words.append(tok)
            pending_case = None
            direct_object_pending = False
            subject_agreement = None
            pending_numeral = None
            i += 1
            continue

        num_value = _parse_numeral(tok)
        if num_value is not None:
            out_words.append(tok)
            debug.append({"src": tok, "out": tok, "note": "числительное: цифры сохраняются"})
            pending_numeral = num_value
            direct_object_pending = False
            i += 1
            continue

        clean = _clean_ru_token(tok)
        phrase = _match_ru_phrase(tokens, i)
        if phrase:
            out_words.append(phrase["out"])
            debug.append({"src": phrase["src"], "out": phrase["out"], "note": phrase["note"]})
            pending_case = None
            i = phrase["end"]
            continue

        prep_choice = None
        if clean and _preposition_key(clean):
            prep_choice = _select_preposition(clean, _next_word_parse(tokens, i))

        # Контекстный выбор parse: для омографов типа "стоит" (стоить vs стоять)
        # проверяем окружающие слова и выбираем нужную лемму.
        parse = None
        if clean and not prep_choice:
            smart_parse = _smart_parse_with_context(tokens, i, clean)
            parse = smart_parse if smart_parse is not None else (_parse_ru(clean) if clean else None)
        direct_case = None if pending_case or not direct_object_pending or not parse else _direct_object_case_for_parse(parse)
        effective_case = pending_case or direct_case
        case_reason = "preposition" if pending_case else ("direct_object" if direct_case else None)

        agreement = None
        if clean and not prep_choice:
            pos = _local_pos_for_parse(parse)
            if pos in ("ADJF", "PRTF"):
                agreement = _agreement_from_following(tokens, i, effective_case)
            elif pending_numeral is not None and pos in ("NOUN", "NPRO"):
                num, case_hint = _numeral_governs(pending_numeral, parse.normal_form)
                agreement = {"number": num}
                if case_hint and not effective_case:
                    agreement["case"] = case_hint

        info = _translate_word_info(
            tok,
            forced_case=effective_case,
            agreement=agreement,
            preposition_choice=prep_choice,
            forced_case_reason=case_reason,
            verb_agreement=subject_agreement,
            parse_override=smart_parse if (clean and not prep_choice and smart_parse is not None) else None,
        )
        out_words.append(info["out"])
        debug.append({"src": tok, "out": info["out"], "note": info["note"]})

        if info["pos"] == "PREP":
            pending_case = info["gov_case"]
            direct_object_pending = False
        elif pending_case and info.get("consumes_case"):
            pending_case = None
        elif pending_case and info["pos"] in ("VERB", "ADVB", "CONJ", "PRCL", "INTJ"):
            pending_case = None

        if info["pos"] == "VERB":
            direct_object_pending = bool(info.get("is_transitive"))
        elif direct_object_pending and info.get("consumes_case"):
            direct_object_pending = False
        elif direct_object_pending and info["pos"] in ("PREP", "CONJ", "PRCL", "INTJ"):
            direct_object_pending = False

        if pending_numeral is not None and info["pos"] in ("NOUN", "NPRO"):
            pending_numeral = None
        elif pending_numeral is not None and info["pos"] in ("VERB", "CONJ", "PRCL", "INTJ"):
            pending_numeral = None

        if parse is not None and not prep_choice and not effective_case:
            subj = _subject_agreement_for_parse(parse)
            if subj:
                subject_agreement = subj
        i += 1

    result = " ".join(out_words).replace(" ,", ",").replace(" .", ".").replace(" ?", "?").replace(" !", "!")
    result = result.replace("( ", "(").replace(" )", ")")
    return json.dumps({"translation": result, "words": debug}, ensure_ascii=False)


# ---------------------------------------------------------------------------
# PR -> RU
# ---------------------------------------------------------------------------

# Существительные-«ориентиры», после которых родительный топоним звучит
# приложением, а не согласованным определением: «деревня Покарвис»,
# «город Покарвис», а не «Покарвская деревня».
PN_APPOSITION_HEADS = {"kāiman", "kāims", "mēstan", "mēstas", "laūks"}

# Русское управление: после этих головных слов родительная группа переводится
# дативом («памятник Эркусу Мантасу», а не «памятник Эркуса Мантаса»).
RU_GEN_CHAIN_DAT_GOVERNORS = {"памятник"}

# Русский предлог выбирается по головному существительному за родительной
# цепочкой: 'en ... laūku' = «на поле», а не «в поле».
PR_PREP_RU_GLOSS_BY_HEAD = {"en": {"laūks": "на"}}

_S_CASE_MAP = {"nom": "nomn", "gen": "gent", "dat": "datv", "acc": "accs",
               "loc": "loct", "ins": "ablt"}
_S_GENDER_MAP = {"m": "masc", "f": "femn", "n": "neut"}


def _label_from_s_field(s_field):
    """Грамматическая метка из словарного поля s («n pl gen» → 'pl.gent').

    Свежие статьи корпуса (11xxx) несут падеж/число в s, но в PR-индекс
    попадают с пустой меткой — и выводят глосс без склонения («немец»
    вместо «немца»). Консервативно: при любой нераспознанной помете
    возвращаем '' — частичный разбор опаснее его отсутствия; именительный
    не даём вовсе (статья с пустой меткой и так выводит глосс как есть)."""
    toks = re.findall(r"[a-z]+", (s_field or "").lower())
    if not toks:
        return ""
    parts = []
    for t in toks:
        if t in _S_GENDER_MAP:
            parts.append(_S_GENDER_MAP[t])
        elif t == "sg":
            parts.append("sing")
        elif t == "pl":
            parts.append("plur")
        elif t in _S_CASE_MAP:
            parts.append(_S_CASE_MAP[t])
        else:
            return ""
    if not any(p in _S_CASE_MAP.values() for p in parts):
        return ""
    if "nomn" in parts:
        return ""
    return ".".join(parts)


def _label_grammar(label):
    """Из метки формы (masc.sg.akk, indicative.present as (я), ...)
    достаёт признаки, пригодные для синтеза русской формы."""
    parts = label.split(".") if label else []
    info = {"case": None, "ru_case": None, "number": None, "gender": None, "person": None, "tense": None}
    for p in parts:
        base = p.split(" ")[0]
        if base in CASE_MAP_INV:
            info["case"] = base
            info["ru_case"] = CASE_MAP_INV[base]
        if base in NUMBER_MAP_INV:
            info["number"] = NUMBER_MAP_INV[base]
        if base in GENDER_MAP_INV:
            info["gender"] = GENDER_MAP_INV[base]
        if base in ("present", "past", "future"):
            info["tense"] = {"present": "pres", "past": "past", "future": "futr"}[base]
    # Пустая метка = словарная форма (именительный падеж, ед.ч.). Раньше из‑за
    # pymorphy3 [0] для слов вроде "паспорт"/"память" возвращался случайный
    # падеж (accs), и согласование прилаганий ломалось ("прусского паспорт").
    if not parts and info["case"] is None:
        info["case"] = "nomn"
        info["ru_case"] = "nomn"
        # number НЕ фиксируем: для множественных/ Plural-лемм (Prūsai, Мантасы)
        # фиксирование sing давило pymorphy на единственное («Прус»). Оставляем
        # None — inflect({}) без числа оставит pymorphy в своём числе.
    last = parts[-1] if parts else ""
    if "(я)" in last:
        info.update({"person": "1per", "number": "sing"})
    elif "(ты)" in last:
        info.update({"person": "2per", "number": "sing"})
    elif "(мы)" in last:
        info.update({"person": "1per", "number": "plur"})
    elif "(вы)" in last:
        info.update({"person": "2per", "number": "plur"})
    elif "(он/она/оно)" in last:
        info.update({"person": "3per", "number": "sing"})
    elif "(они)" in last:
        info.update({"person": "3per", "number": "plur"})
    return info


def _label_to_ru_grammemes(label):
    parts = label.split(".")
    grammemes = set()
    for p in parts:
        base = p.split(" ")[0]
        if base in CASE_MAP_INV:
            grammemes.add(CASE_MAP_INV[base])
        if base in NUMBER_MAP_INV:
            grammemes.add(NUMBER_MAP_INV[base])
        if base in GENDER_MAP_INV:
            grammemes.add(GENDER_MAP_INV[base])
    last = parts[-1] if parts else ""
    if "(я)" in last:
        grammemes.update({"1per", "sing"})
    elif "(ты)" in last:
        grammemes.update({"2per", "sing"})
    elif "(мы)" in last:
        grammemes.update({"1per", "plur"})
    elif "(вы)" in last:
        grammemes.update({"2per", "plur"})
    elif "(он/она/оно)" in last or "(они)" in last:
        grammemes.add("3per")
        grammemes.add("plur" if "они" in last else "sing")
    if "present" in parts:
        grammemes.add("pres")
    if "past" in parts:
        grammemes.add("past")
    if "future" in parts:
        grammemes.add("futr")
    return grammemes


def _ru_pronoun_form(entry, label):
    """Личные местоимения нельзя надёжно получать из первого русского gloss.
    Например, статья jūsu хранит gloss "вы", но её sg.akk форма ten должна
    переводиться как "тебя". Поэтому задаём основные формы явно."""
    word = (entry.get("w") or "").lower()
    info = _label_grammar(label)
    number = info.get("number")
    case = info.get("ru_case") or "nomn"

    if word in {"as", "mes"}:
        if label == "" and word == "mes":
            number = "plur"
        if number == "plur":
            return {"nomn": "мы", "gent": "нас", "datv": "нам", "accs": "нас", "ablt": "нами", "loct": "нас"}.get(case, "мы")
        return {"nomn": "я", "gent": "меня", "datv": "мне", "accs": "меня", "ablt": "мной", "loct": "мне"}.get(case, "я")

    if word in {"tū", "jūs"}:
        if label == "" and word == "jūs":
            number = "plur"
        if number == "plur":
            return {"nomn": "вы", "gent": "вас", "datv": "вам", "accs": "вас", "ablt": "вами", "loct": "вас"}.get(case, "вы")
        return {"nomn": "ты", "gent": "тебя", "datv": "тебе", "accs": "тебя", "ablt": "тобой", "loct": "тебе"}.get(case, "ты")

    if word in {"tāns", "tenā", "tennan", "dis", "di"}:
        # tenā — форма женского рода («она»): без метки не считаем её мужской
        gender = info.get("gender") or ("femn" if word == "tenā" else "masc")
        if number == "plur":
            return {"nomn": "они", "gent": "их", "datv": "им", "accs": "их", "ablt": "ими", "loct": "них"}.get(case, "они")
        if gender == "femn":
            return {"nomn": "она", "gent": "её", "datv": "ей", "accs": "её", "ablt": "ей", "loct": "ней"}.get(case, "она")
        if gender == "neut":
            return {"nomn": "оно", "gent": "его", "datv": "ему", "accs": "его", "ablt": "им", "loct": "нём"}.get(case, "оно")
        return {"nomn": "он", "gent": "его", "datv": "ему", "accs": "его", "ablt": "им", "loct": "нём"}.get(case, "он")
    return None


def _ru_word_gender(word):
    """Пymorphy-род русского слова ('masc'/'femn'/'neut') или None.

    Род сказуемого берём у РУССКОГО подлежащего (аудит-принцип: сражение —
    средний род, хотя wālinsnā в прусском женский)."""
    clean = _clean_ru_token(word or "")
    if not clean:
        return None
    for p in morph.parse(clean):
        if p.tag.POS == "NOUN" and p.tag.gender:
            return p.tag.gender
    return None


def _ru_verb_form(gloss, label, subject_gender=None, override=None, subject_number=None):
    info = _label_grammar(label)
    tense = info.get("tense")
    number = info.get("number") or (subject_number or "sing")
    person = info.get("person") or "3per"

    # Prefer explicit Russian conjugation forms from override — authoritative,
    # no pymorphy3 drift (e.g. "победить" inflect {past,plur} → "победившие"
    # instead of "победили"). TENSE_MAP keys: pres/past/futr → present/past/future.
    if override:
        indic = ((override.get("conjugation") or {}).get("indicative") or {})
        candidates = []
        if tense and TENSE_MAP.get(tense):
            # явное время: только его строки (фоллбэк в past при present-метке
            # читал «statinna ставлю» как «поставил» через ru-строки past)
            candidates.append(TENSE_MAP.get(tense))
        else:
            candidates.append("past")
        for tk in candidates:
            rows = indic.get(tk)
            if not isinstance(rows, list) or not rows:
                continue
            try:
                idx = PERSON_ORDER.index((person, number))
            except ValueError:
                idx = 5 if (person, number) == ("3per", "plur") else 2
            idx = min(idx, len(rows) - 1)
            form = rows[idx]
            ru = form.get("ru") if isinstance(form, dict) else form
            if ru:
                # явная форма из override согласуется с родом подлежащего:
                # «фонд поставил», «tenā statinna» → «она поставила»
                if tense == "past" and number == "sing" and subject_gender:
                    try:
                        fin = morph.parse(ru)[0].inflect({"past", subject_gender})
                        if fin:
                            ru = fin.word
                    except Exception:
                        pass
                return ru

    grammemes = set()
    if tense == "past":
        grammemes.add("past")
        grammemes.add(number)
        if number == "sing":
            grammemes.add(subject_gender or "masc")
    elif tense in ("pres", "futr"):
        grammemes.update({tense, number, person})
    else:
        return None

    p = morph.parse(gloss)[0]
    try:
        inflected = p.inflect(grammemes)
    except Exception:
        inflected = None
    if inflected is None and tense in ("pres", "futr"):
        # совершенный вид в pymorphy не имеет «pres»-форм: русское будущее
        # совпадает с настоящим («установлю», «установит») — пробуем его
        alt_grammemes = (grammemes - {"pres", "futr"}) | {
            "futr" if tense == "pres" else "pres"}
        try:
            inflected = p.inflect(alt_grammemes)
        except Exception:
            inflected = None
    return inflected.word if inflected else None


def _ru_gloss_for_entry(entry, label, forced_case=None, agreement=None, subject_gender=None, subject_number=None, num_government=False, short_participle=False):
    """Возвращает (русское_слово, заметку) для статьи словаря, по
    возможности согласовав русское слово с распознанной грамматической
    формой. В отличие от ранней версии, не переносит прусский род на русские
    существительные: buttan neut, но русский "дом" masc.

    short_participle — страдательное причастие-предикатив после связки
    («будет установлен», «не установлен»): краткая форма вместо полной."""
    manual_gloss = (
        _pr_to_ru_priority.get(str(entry.get("i")).lower()) or
        _pr_to_ru_priority.get((entry.get("w") or "").lower())
    )
    # Override.ru — ручная правка перевода конкретной формы (напр., «Papeisātan»
    # → «написана»). Словарная статья того же id может нести инфинитив
    # («написать»), и pymorphy превращал его в «написавшие» при склонении по
    # пустой метке. Даём override приоритет над словарным ru.
    override = _override_by_id.get(entry.get("i"))
    override_ru = (override or {}).get("ru") if isinstance(override, dict) else None
    ru_field = (override_ru or "") or entry.get("ru", "")
    first_chunk = _split_ru_field(ru_field)[0] if ru_field else ""
    cleaned_chunk = _clean_ru_chunk(first_chunk)
    gloss = manual_gloss or cleaned_chunk or ru_field.strip() or "?"
    # Заглавная из словарного глосса — признак имени собственного («Натангия»):
    # _clean_ru_chunk всё снижает, но в переводе «в Натангии» нужна прописная.
    if (not manual_gloss and cleaned_chunk and first_chunk
            and first_chunk.strip()[:1].isupper() and gloss[:1].islower()):
        gloss = gloss[:1].upper() + gloss[1:]

    note_form = label.replace(".", "/") if label else "словарная форма"
    pos = classify_pos(entry, override)

    # Готовая форма-связка будущего времени: gloss и есть нужная русская
    # словоформа, инфлексия по пустой метке ломает её ('будет' → 'бывший').
    if (entry.get("w") or "").lower() == "wīrstats" and gloss == "будет":
        return gloss, note_form

    pronoun = _ru_pronoun_form(entry, label)
    if pronoun:
        return pronoun, note_form

    # v9 (Data 2.3): составные глоссы («варить пиво», «граничить с») не
    # склоняются через pymorphy и раньше уходили в «фразу не склоняем».
    # Теперь у спряжений есть авторитетные ru-строки — для глаголов читаем
    # их ДО этого выхода: «Tāns brāwi.» → «Он варит», а не «Он варить пиво».
    if pos == "VERB" and override and " " in (gloss or "").strip():
        verb_form = _ru_verb_form(gloss, label, subject_gender=subject_gender,
                                  override=override, subject_number=subject_number)
        if verb_form:
            return verb_form, note_form

    if not gloss or " " in gloss.strip():
        return gloss or "?", note_form  # фразу не склоняем

    # pymorphy3 даёт предложный "годе", но в датах по-русски нужна форма
    # "в 1273 году". Это частый случай для mettan.
    if gloss == "год" and forced_case == "loct":
        return "году", note_form

    # Числительное управляет родительным падежом множественного числа:
    # "750 mettans" -> "750 лет", а не "750 годы". У существительных род
    # задаёт лемма, поэтому его намеренно не добавляем.
    if num_government and pos in ("NOUN", "NPRO", "ADJF", "PRTF", "NUMR") \
            and (entry.get("w") or "").lower() not in PR_GEN_PL_QUANTIFIERS \
            and not forced_case:
        if gloss == "год":
            return "лет", note_form
        grammemes = {"gent", "plur"}
        if pos in ("ADJF", "PRTF") and _label_grammar(label).get("gender"):
            grammemes.add(_label_grammar(label)["gender"])
        p = morph.parse(gloss)[0]
        try:
            inflected = p.inflect(grammemes)
        except Exception:
            inflected = None
        if inflected:
            return inflected.word, note_form

    # Причастия: метка вида "participles.genders.masc.sg.nom" не содержит
    # времени, поэтому _ru_verb_form возвращал None и оставался инфинитив
    # ("aulaūwuns" -> "умереть" вместо "умерший").
    # Также обрабатываем формы на -uns, у которых в метке может не быть
    # "participles" (например, словарные заголовки типа aulaūwuns id=7797).
    if "participles" in label or entry.get("w", "").endswith("uns"):
        p = morph.parse(gloss)[0]
        info = _label_grammar(label)
        # Определяем залог причастия. В override может быть несколько типов
        # причастий (действительное наст./прош. и страдательное прош.), и все
        # они дают одинаковый label 'participles.genders.masc.sg.akk'.
        # Чтобы различить их, проверим саму форму слова: для каждой participle
        # в override ищем, в парадигме какого из них встречается наша форма.
        # Эвристика по форме:
        # - формы на -nts (statinānts, ainants) — действительного наст. вр.
        # - формы на -uns (aulaūwuns) — действительного прош. вр.
        # - формы на -ts (statīnts, swentints) — страдательного прош. вр.
        # Но у нас в этой точке нет самой формы (только entry и label).
        # Поэтому: если в override есть participle с headword на '-ts' (но не
        # '-nts'/'-uns'), и в его парадигме есть формы на '-tan'/'-tans'/...,
        # считаем нашу форму страдательной.
        is_passive = False
        override_local = _override_by_id.get(entry.get("i"))
        if override_local and "participles" in label:
            parts = (override_local.get("conjugation") or {}).get("participles", [])
            if isinstance(parts, list):
                # Сравниваем headword причастия с инфинитивом (entry.w или
                # override.word). В прусском:
                # - statīntun (инфинитив) + -nts → statinānts (действительное наст. вр.)
                # - statīntun + -uns → statīnuns (действительное прош. вр.)
                # - statīntun + -ts → statīnts (страдательное прош. вр.)
                # Эвристика: headword оканчивается на 'ts' (последние 2 символа),
                # но НЕ оканчивается на 'nts' (последние 3 символа).
                # Это работает, потому что:
                # - statinānts → оканчивается на -nts (действительное наст.)
                # - statīnuns → оканчивается на -uns (действительное прош.)
                # - statīnts → оканчивается на -ts, но НЕ на -nts (только 2 символа 'ts')
                #   (потому что в statīnts перед 'ts' стоит 'n' от основы, но 'nts' —
                #   это последние 3 символа, и они совпадают с суффиксом действительного
                #   наст. вр. -nts. Чтобы различить, нужно знать длину: у statinānts
                #   (действительное наст.) длина = 10, у statīnts (страдательное) длина = 8.)
                # Поэтому: страдательное причастие — это headword, который
                # совпадает с инфинитивом (минус -tun/-twei) + 'ts' (короткая форма).
                # Самый надёжный способ: headword заканчивается на 'ts' и его длина
                # МЕНЬШЕ, чем у инфинитива, обрезанного до -tun/-twei, + 3 (для '-nts').
                # Проще: если headword длиной ≤ длины инфинитива + 1, это страдательное.
                # Для statīntun (9) → statīnts (8) ≤ 10 ✓
                # Для statinānts (10) — здесь длина 10 = 9+1, но это действительное.
                # Нужна другая эвристика: headword оканчивается на 'ts', но не на 'nts'
                # (используя более точную проверку).
                # 'statīnts'.endswith('ts') → True
                # 'statīnts'.endswith('nts') → True (последние 3 символа: 'n','t','s')
                # Но у 'statinānts' последние 4 символа: 'ā','n','t','s' — поэтому
                # 'statinānts'.endswith('nts') → True.
                # Решение: сравниваем длину headword и проверяем, что последние 2 символа
                # 'ts', и что headword ДЛИННЕЕ, чем инфинитив минус 3 (если нет -nts).
                # Самый надёжный способ: headword оканчивается на 'ts' (последние 2),
                # но не содержит 'n' прямо перед 'ts' (т.е. headword[-2:] == 'ts' и
                # (длина < 3 или headword[-3] не 'n') — это statīnts, потому что
                # headword[-3] = 'n' (от statīn-). НЕ РАБОТАЕТ.
                # ИТОГО: используем точное сравнение с инфинитивом.
                inf_word = (entry.get("w") or "").lower()
                # Убираем типичные окончания инфинитива
                inf_stem = inf_word
                for suffix in ("twei", "tun", "tuns"):
                    if inf_stem.endswith(suffix):
                        inf_stem = inf_stem[:-len(suffix)]
                        break
                for p_def in parts:
                    hw = (p_def.get("headword") or "").lower()
                    # Страдательное причастие = основа инфинитива + 'ts' (без 'n')
                    # Действительное наст. = основа + 'ā' + 'nts' (или подобное)
                    # Действительное прош. = основа + 'uns' (с усечением 'tun' → 'uns'?)
                    # Для statīntun (основа 'statīn'):
                    #   statīnts = statīn + ts → страдательное (hw[:-2] == inf_stem)
                    #   statīnuns = statīn + uns → действительное прош.
                    #   statinānts = statīn + ā + nts → действительное наст.
                    # Эвристика: если hw == inf_stem + 'ts' (точно), это страдательное.
                    if hw == inf_stem + "ts":
                        is_passive = True
                        break
                    # Запасная эвристика: hw заканчивается на 'ts', длина = len(inf_stem)+2,
                    # и hw[:len(inf_stem)] == inf_stem. Это работает для statīnts.
                    if (hw.endswith("ts") and len(hw) == len(inf_stem) + 2
                            and hw[:len(inf_stem)] == inf_stem):
                        is_passive = True
                        break
        # Альтернативная эвристика по словарной форме entry.w (если article
        # является самим заголовком причастия, например id=343 aulaūwuns).
        word_lower = (entry.get("w") or "").lower()
        if (len(word_lower) >= 2 and word_lower.endswith("ts")
                and not (len(word_lower) >= 3 and word_lower[-3] == "n")):
            is_passive = True
        # Ещё одна эвристика: если форма - это сама статья cross-ref (x=true),
        # и её базовая статья (b) оканчивается на -ts (но не -nts/-uns) — тоже
        # страдательное причастие.
        if not is_passive and entry.get("x") and entry.get("b"):
            base = _headword_index.get((entry.get("b") or "").lower())
            if base is not None:
                bw = (base.get("w") or "").lower()
                if (len(bw) >= 2 and bw.endswith("ts")
                        and not (len(bw) >= 3 and bw[-3] == "n")):
                    is_passive = True
        # Краткая форма страдательного причастия-предикатива после связки:
        # 'wīrstats statīntan' → «будет установлен», 'ni pastāi statīntan' →
        # «не установлен» (а не «установленный»).
        if short_participle and is_passive:
            short_num = info.get("number") or subject_number or "sing"
            grammemes_short = {"PRTS", short_num}
            if short_num == "sing":
                grammemes_short.add(subject_gender or info.get("gender") or "masc")
            try:
                inflected = p.inflect(grammemes_short)
            except Exception:
                inflected = None
            if inflected:
                return inflected.word, note_form
            # краткая не получилась — падаем в полную форму ниже
        grammemes = {"PRTF", "past", "pssv" if is_passive else "actv"}
        grammemes.add(info.get("number") or subject_number or "sing")
        grammemes.add(subject_gender or info.get("gender") or "masc")
        grammemes.add(forced_case or info.get("ru_case") or "nomn")
        try:
            inflected = p.inflect(grammemes)
        except Exception:
            inflected = None
        if inflected:
            return inflected.word, note_form
        # Если страдательное не получилось (pymorphy не знает форму), попробуем
        # действительный залог как фоллбэк (старое поведение).
        if is_passive:
            grammemes_fallback = {"PRTF", "past", "actv"}
            grammemes_fallback.add(info.get("number") or subject_number or "sing")
            grammemes_fallback.add(subject_gender or info.get("gender") or "masc")
            grammemes_fallback.add(forced_case or info.get("ru_case") or "nomn")
            try:
                inflected = p.inflect(grammemes_fallback)
            except Exception:
                inflected = None
            if inflected:
                return inflected.word, note_form

    if pos == "VERB":
        verb = _ru_verb_form(gloss, label, subject_gender=subject_gender, override=override, subject_number=subject_number)
        if verb:
            return verb, note_form
        # Связка 'ast' (3sg present от būtwei) — особый случай: метка у неё
        # пустая (cross-ref на būtwei), _ru_verb_form возвращает None, а
        # через inflect({'nomn'}) получается бессмысленное 'бывшие'. Поэтому
        # для формы 'ast' с gloss='быть' возвращаем русскую связку 'есть'.
        if (entry.get("w") or "").lower() == "ast" and gloss == "быть":
            return "есть", note_form

    info = _label_grammar(label)
    ru_case = forced_case or (agreement or {}).get("case") or info.get("ru_case")
    number = (agreement or {}).get("number") or info.get("number")
    gender = (agreement or {}).get("gender") or info.get("gender")

    grammemes = set()
    if ru_case:
        grammemes.add(ru_case)
    if number:
        grammemes.add(number)
    # Русским существительным род задаёт сама лемма; чужой прусский род часто
    # ломает инфлексию. Для прилагательных/причастий род нужен.
    animacy = (agreement or {}).get("animacy")
    if pos in ("ADJF", "PRTF"):
        if gender:
            grammemes.add(gender)
        # В русском винительном падеже одушевленность различается только для мужского рода и во множественном числе
        if ru_case == "accs" and animacy and (gender == "masc" or number == "plur"):
            grammemes.add(animacy)

    if grammemes:
        p = morph.parse(gloss)[0]
        # Краткие прилагательные/причастия (PRTS) в русском не склоняются по
        # падежам: «написана» не надо превращать в «написанная» по пустой
        # метке. Возвращаем как есть.
        if "PRTS" in str(p.tag):
            return gloss, note_form
        # Инфинитив (INFN) нельзя склонять по падежам: morph.parse('быть')[0]
        # .inflect({nomn}) даёт причастие 'бывшие', что бессмысленно для
        # present 'ast' → должно быть 'есть'. Если словарный gloss — инфинитив
        # глагола, возвращаем как есть (или 'есть' для 'быть' как частый случай).
        if "INFN" in str(p.tag):
            if gloss == "быть" and "pres" in grammemes:
                return "есть", note_form
            return gloss, note_form
        try:
            inflected = p.inflect(grammemes)
        except Exception:
            inflected = None
        if inflected:
            out_word = inflected.word
            # pymorphy возвращает формы строчными; имя собственное
            # («Натангия» → «в Натангии») должно сохранить прописную.
            if gloss[:1].isupper() and out_word[:1].islower():
                out_word = out_word[:1].upper() + out_word[1:]
            return out_word, note_form

    return gloss, note_form


def _entry_has_ru_gloss(entry):
    ru_field = entry.get("ru", "")
    if not ru_field:
        return False
    first_chunk = _split_ru_field(ru_field)[0]
    return bool(_clean_ru_chunk(first_chunk) or ru_field.strip())


def _lookup_pr_matches(clean_key):
    return _pr_index.get(clean_key) or _pr_index_folded.get(fold_diacritics(clean_key)) or []


def _label_matches_agreement(label, agreement):
    if not agreement:
        return False
    info = _label_grammar(label)
    # Normalize number formats: PN table uses "pl"/"sg", _label_grammar uses "plur"/"sing"
    agr_num = agreement.get("number")
    if agr_num == "pl":
        agr_num = "plur"
    elif agr_num == "sg":
        agr_num = "sing"
    return bool(
        info.get("person") == agreement.get("person") and
        info.get("number") == agr_num
    )


def _select_pr_match(clean_key, prefer_pos=None, verb_agreement=None, next_pos_hint=None):
    matches = _lookup_pr_matches(clean_key)
    if not matches:
        return None

    # Проверяем, есть ли среди совпадений форма причастия из спряжения глагола,
    # а также альтернативная не-глагольная статья (напр., прилагательное
    # «мертвый» для aulaūwuns). Если есть и то, и то — отдаём причастие.
    has_participle_from_verb = False
    has_nonverb_with_gloss = False
    has_possessive = False
    has_personal_pron = False
    for entry, label in matches:
        override = _override_by_id.get(entry.get("i"))
        pos = classify_pos(entry, override)
        if "particip" in (label or "").lower() and pos == "VERB":
            has_participle_from_verb = True
        if pos != "VERB" and _entry_has_ru_gloss(entry) and not entry.get("x"):
            has_nonverb_with_gloss = True
        # Possessive (мой/твой/наш/ваш/свой) в словаре помечены как 'pn po X'
        # и попадают в NPRO. Поэтому判定аем по русскому gloss, а не по POS.
        # Personal: я/ты/мы/вы.
        first_gloss = _clean_ru_chunk((_split_ru_field(entry.get("ru") or ""))[0]) if entry.get("ru") else ""
        if first_gloss in ("мой", "твой", "наш", "ваш", "свой"):
            has_possessive = True
        elif first_gloss in ("я", "ты", "мы", "вы"):
            has_personal_pron = True
    prefer_participle = has_participle_from_verb and has_nonverb_with_gloss
    # Контекстный бонус: если омограф может быть и possessive ('мой'),
    # и personal ('мы'), а следующее слово — существительное/местоимение
    # в именительном/винительном, то possessive ('мой брат') почти всегда
    # правильнее личного ('мы брат'). Это чинит 'Hērkus ast mans brāti' →
    # 'Эркс есть мой брат', а не 'мы брат'.
    prefer_possessive = (
        has_possessive and has_personal_pron
        and next_pos_hint in ("NOUN", "NPRO")
    )

    def score(match):
        entry, label = match
        override = _override_by_id.get(entry.get("i"))
        pos = classify_pos(entry, override)
        pos_miss = 0 if (prefer_pos is None or pos == prefer_pos) else 1
        verb_miss = 0
        if prefer_pos == "VERB" and verb_agreement:
            verb_miss = 0 if _label_matches_agreement(label, verb_agreement) else 1
        # Причастие из спряжения в overrides имеет приоритет только когда
        # рядом есть не-глагольная статья (aulaūwuns → «умерший» из глагола,
        # а не «мертвый» из прилагательного). Для обычных случаев (papeisātan)
        # эта логика не включается.
        is_participle_bonus = (
            prefer_participle
            and "particip" in (label or "").lower()
            and pos == "VERB"
        )
        # Бонус possessive перед существительным.
        first_gloss = _clean_ru_chunk((_split_ru_field(entry.get("ru") or ""))[0]) if entry.get("ru") else ""
        is_possessive_bonus = (
            prefer_possessive
            and first_gloss in ("мой", "твой", "наш", "ваш", "свой")
        )
        # Вырожденная парадигма: одна и та же прусская форма стоит и в present,
        # и в past (statinna = и «ставлю», и «поставил» в данных statīntun).
        # Если у past-строк автор указал русские формы, при подлежащем в 3-м
        # лице читаем форму как прошедшее время: «fōnds ... statinna» =
        # «фонд поставил», а не «фонд ставит».
        # v9: ru-строки past теперь есть почти у всех глаголов (автозаполнение),
        # поэтому одного их наличия мало — требуется настоящая вырожденность:
        # форма present == форме past того же лица/числа. У нормальных глаголов
        # (wīdimai ≠ wīda) презенс остаётся презенсом.
        degenerate_past = 0
        if (prefer_pos == "VERB" and verb_agreement
                and verb_agreement.get("person") == "3per"
                and (label or "").startswith("indicative.")
                and "present" in label):
            ov = _override_by_id.get(entry.get("i"))
            indic_rows = (((ov or {}).get("conjugation") or {}).get("indicative") or {})
            past_rows = indic_rows.get("past") or []
            if isinstance(past_rows, list) and any(
                    isinstance(r, dict) and r.get("ru") for r in past_rows):
                pres_rows = indic_rows.get("present") or []
                try:
                    idx = PERSON_ORDER.index((verb_agreement.get("person"),
                                              verb_agreement.get("number")))
                except ValueError:
                    idx = None
                if idx is not None and idx < len(past_rows) and idx < len(pres_rows):
                    pf = (past_rows[idx].get("f") if isinstance(past_rows[idx], dict)
                          else past_rows[idx]) or ""
                    rf = (pres_rows[idx].get("f") if isinstance(pres_rows[idx], dict)
                          else pres_rows[idx]) or ""
                    pf = str(pf).split("/")[0].strip().lower()
                    rf = str(rf).split("/")[0].strip().lower()
                    if pf and pf == rf:
                        degenerate_past = 1
        # В словаре бывают дублеты: сначала cross-ref без русского gloss, затем
        # полноценная статья с переводом (например, aulaūwuns). Для обратного
        # перевода выбираем статью, из которой реально можно получить русский
        # перевод; потом учитываем контекстную часть речи.
        # Порядок score-компонентов:
        # 1) has_gloss — статья без русского перевода всегда проигрывает;
        # 2) is_possessive_bonus — possessive перед существительным выигрывает;
        # 3) cross_ref (x=true) — деприоритизирован: настоящая парадигмальная
        #    форма всегда выигрывает у cross-ref заглушки. Это чинит омографы
        #    типа 'tenēi' (которое и как masc.pl.nom от tāns, и как cross-ref
        #    на tāns) — раньше cross-ref выигрывал из-за label=="".
        # 4) pos_miss, verb_miss, participle_bonus — последующие критерии.
        return (
            not _entry_has_ru_gloss(entry),
            0 if is_possessive_bonus else 1,    # possessive перед сущ. выигрывает
            bool(entry.get("x")),               # cross-ref деприоритизирован ВЫШЕ label
            pos_miss,
            verb_miss,
            0 if is_participle_bonus else 1,
            label == "" if prefer_pos == "VERB" else label != "",
            degenerate_past,                    # вырожденная парадигма: 3 л. → past
        )

    return sorted(matches, key=score)[0]


def _select_pr_matches_tied(clean_key, prefer_pos=None, verb_agreement=None):
    """Как _select_pr_match, но возвращает ВСЕ статьи с лучшим (минимальным)
    счётом, а не только первую. Нужно, чтобы не терять настоящую
    многозначность омографов вроде предлога pa (под / после / по
    (согласно)) - раньше при равном счёте побеждала просто первая по
    порядку в файле статья, и остальные значения пропадали бесследно."""
    matches = _lookup_pr_matches(clean_key)
    if not matches:
        return []

    def score(match):
        entry, label = match
        override = _override_by_id.get(entry.get("i"))
        pos = classify_pos(entry, override)
        pos_miss = 0 if (prefer_pos is None or pos == prefer_pos) else 1
        verb_miss = 0
        if prefer_pos == "VERB" and verb_agreement:
            verb_miss = 0 if _label_matches_agreement(label, verb_agreement) else 1
        is_cross_ref = 1 if entry.get("x") else 0
        priority = (override or {}).get("priority", 99)
        is_exact_headword = 0 if (entry.get("w") or "").lower() == clean_key else 1
        has_manual_prio = 0 if (
            str(entry.get("i")).lower() in _pr_to_ru_priority or
            (entry.get("w") or "").lower() in _pr_to_ru_priority
        ) else 1
        info = _label_grammar(label)
        case = info.get("case") or "nom"
        case_rank = 0 if case == "nom" else 1

        return (
            not _entry_has_ru_gloss(entry),
            is_cross_ref,
            has_manual_prio,
            priority,
            pos_miss,
            verb_miss,
            is_exact_headword if label == "" else 0,
            0 if label != "" else 1,
            case_rank,
        )

    scored = sorted(matches, key=score)
    best = score(scored[0])
    seen, tied = set(), []
    for m in scored:
        if score(m) != best:
            break
        entry, _ = m
        if entry.get("i") in seen:
            continue  # несколько форм одной и той же статьи - не дублируем
        seen.add(entry.get("i"))
        tied.append(m)
    return tied


def _lookup_pr(clean_key):
    return _select_pr_match(clean_key)


def _build_propername_index(propernames_json_str):
    """Индексирует data/propernames.json.

    lemma/алиасы  -> entry;  pr-форма (в нижнем регистре) -> (entry, number, pr_case).
    Это покрытие для имён, которых нет в dictionary.json: позволяет отдавать
    заранее просчитанную русскую форму и склонять имя в любой падеж/число по
    таблице, минуя ненадёжную pymorphy3‑инфлексию собственных имён."""
    global _propernames, _propername_lemma_index, _propername_form_index, _ru_name_index
    _propernames, _propername_lemma_index, _propername_form_index = {}, {}, {}
    _ru_name_index = {}
    if not propernames_json_str:
        return
    try:
        data = json.loads(propernames_json_str)
    except Exception:
        return
    if isinstance(data, dict):
        data = [data]
    if not isinstance(data, list):
        return
    for entry in data:
        lemma = (entry.get("lemma") or "").lower()
        if not lemma:
            continue
        entry_l = dict(entry)
        _propernames[lemma] = entry_l
        keys = [lemma] + [a.lower() for a in (entry.get("aliases") or []) if a]
        for k in keys:
            _propername_lemma_index[k] = entry_l
        pr = entry.get("pr") or {}
        for num_key, cases in pr.items():            # "sg" | "pl"
            num = "pl" if "pl" in num_key.lower() else "sg"
            for pr_case, form in cases.items():       # "nom"/"gen"/... (можно список вариантов)
                forms = form if isinstance(form, list) else [form]
                for variant in forms:
                    form_lower = (variant or "").lower()
                    if not form_lower:
                        continue
                    existing = _propername_form_index.get(form_lower)
                    if existing is None:
                        _propername_form_index[form_lower] = (entry_l, num, pr_case)
                    else:
                        # Prefer lower priority number (1 > 50), then higher entry
                        new_pri = entry_l.get("priority")
                        old_pri = existing[0].get("priority")
                        if new_pri is not None and (old_pri is None or new_pri < old_pri):
                            _propername_form_index[form_lower] = (entry_l, num, pr_case)
                        elif new_pri == old_pri and entry_l is existing[0]:
                            # Same entry, keep existing
                            pass
                    # Запасной вариант без макронов: ввод часто бывает без диакритики
                    folded = fold_diacritics(form_lower)
                    if folded != form_lower:
                        existing2 = _propername_form_index.get(folded)
                        if existing2 is None:
                            _propername_form_index[folded] = (entry_l, num, pr_case)
                        else:
                            new_pri2 = entry_l.get("priority")
                            old_pri2 = existing2[0].get("priority")
                            if new_pri2 is not None and (old_pri2 is None or new_pri2 < old_pri2):
                                _propername_form_index[folded] = (entry_l, num, pr_case)
        ru = entry.get("ru") or {}
        try:
            for num_key, cases in ru.items():             # "sg" | "pl"
                num = "pl" if "pl" in num_key.lower() else "sg"
                for ru_case, form in cases.items():
                    forms = form if isinstance(form, list) else [form]
                    for variant in forms:
                        form_lower = (variant or "").lower()
                        if form_lower:
                            _ru_name_index[form_lower] = (entry_l, num, ru_case)
        except Exception as e:
            if 'abd' in (entry.get('lemma') or '').lower():
                print(f"ERROR indexing ru for {entry.get('lemma')}: {e}")

        # ru_aliases — альтернативные русские формы имени, которых нет в
        # основной парадигме (напр. "Эркус" как альтернатива "Эркс").
        # Индексируем как nomn, чтобы 'Эркус' находилось в RU → PR.
        for alias in (entry.get("ru_aliases") or []):
            if isinstance(alias, dict):
                form = alias.get("form", "")
                case = alias.get("case", "nomn")[:4]  # nomn/gent/datv/...
            else:
                form = alias
                case = "nomn"
            form_lower = (form or "").lower()
            if form_lower and form_lower not in _ru_name_index:
                _ru_name_index[form_lower] = (entry_l, "sg", case)

        # ru_adj — русское прилагательное от топонима («Покарвский» для
        # Pakarwis). Индексируем все его формы как «родительный атрибут»:
        # в прусском такая конструкция выражается генитивом («Pakarwjas
        # walinsnā»), поэтому любая форма прилагательного ведёт к pr-генитиву.
        # Это делает обратный перевод симметричным: «Покарвское сражение» →
        # 'Pakarwjas walinsnā' (аудит: симметрия обратного перевода).
        ru_adj_lemma = (entry.get("ru_adj") or "").strip()
        if ru_adj_lemma:
            for adj_form in _decline_ru_adjective_forms(ru_adj_lemma):
                adj_key = adj_form.lower()
                if adj_key and adj_key not in _ru_name_index:
                    _ru_name_index[adj_key] = (entry_l, "sg", "gen")



def _closest_variant(lemma, variants):
    """Из списка падежных вариантов берём ближайший к словарной лемме по общему
    началу: для Ērks родительный даёт [Ārkas, Ārkisa, Ērkus, ...] -> Ērkus."""
    lemma_l = (lemma or "").lower()

    def score(v):
        v_l = (v or "").lower()
        i = 0
        while i < min(len(lemma_l), len(v_l)) and lemma_l[i] == v_l[i]:
            i += 1
        return i

    return max(variants, key=score) if variants else None


def _render_propername_ru_to_pr(token, forced_case=None, agreement=None):
    """Прусская форма имени по русской словоформе (направление RU -> PR).

    Таблица propernames.json хранит заранее просчитанные русские формы, поэтому
    ищем токен напрямую; падеж берём из предлога/согласования, иначе — из самой
    русской формы. Возвращает строку либо None, если имя не найдено."""
    hit = _ru_name_index.get(_clean_ru_token(token))
    if not hit:
        return None
    entry, num, ru_case = hit
    # Падеж уже выражен самой русской словоформой ("Эркуса" — родительный);
    # принудительный падеж берём только если форма имени номинативная,
    # иначе согласование с главным словом ("паспорт Эркуса") ломает падеж.
    surface_ru_case = _PR_CASE_TO_RU.get(ru_case, "nomn")
    target_ru_case = surface_ru_case
    if surface_ru_case == "nomn" and forced_case:
        target_ru_case = forced_case
    pr_case = _RU_TO_PR_CASE.get(target_ru_case, "nom")
    pr = entry.get("pr") or {}
    form = (pr.get(num) or {}).get(pr_case)
    if form is None:
        form = (pr.get("sg") or {}).get(pr_case)
    if isinstance(form, list):
        form = _closest_variant(entry.get("lemma") or "", form)
    if not form:
        return None
    if token[:1].isupper():
        form = form[:1].upper() + form[1:]
    return form


def _lookup_propername(clean_token):
    """Возвращает (entry, number['sg'|'pl'], pr_case) для собственного имени,
    либо None. clean_token уже нижнего регистра (результат _clean_pr_token)."""
    entry = _propername_lemma_index.get(clean_token)
    if entry:
        return entry, "sg", "nom"
    hit = _propername_form_index.get(clean_token)
    if hit is None:
        hit = _propername_form_index.get(fold_diacritics(clean_token))
    return hit


def _render_propername(token, forced_case=None, agreement=None, prefer_nom=False):
    """Русская форма собственного имени с учётом падежа/числа.

    forced_case  — pymorphy‑граммема (nomn/gent/datv/...), принятая от предлога;
    agreement    — {'case','number','gender'} от согласования со существительным;
    prefer_nom   — если True, выбираем русскую форму в именительном даже тогда,
                   когда прусская форма соответствует род. (Нужно для омонографов
                   вроде 'Hērkus', который в propernames записан и как gen-вариант
                   Ērks, и как alias; в начале предложения он подлежащее → nom.)
    Приоритет падежа: forced_case > падеж найденной pr‑формы > agreement > nomn.
    """
    hit = _lookup_propername(_clean_pr_token(token))
    if not hit:
        return None
    entry, num, pr_case = hit
    if prefer_nom and not forced_case and not (agreement or {}).get("case"):
        target_ru_case = "nomn"
    else:
        target_ru_case = (
            forced_case
            or _PR_CASE_TO_RU.get(pr_case)
            or (agreement or {}).get("case")
            or "nomn"
        )
    target_num = (agreement or {}).get("number") or num
    target_num = target_num if target_num in ("sg", "pl") else "sg"
    # agreement приходит в pymorphy‑числах sing/plur; переводим в sg/pl
    if target_num in ("sing", "plur"):
        target_num = "pl" if target_num == "plur" else "sg"
    pr_key = _RU_TO_PR_CASE.get(target_ru_case, "nom")
    ru_cases = (entry.get("ru") or {}).get(target_num) or {}
    ru = ru_cases.get(pr_key) or ru_cases.get("nom") or ru_cases.get("nomn")
    if not ru:
        alt = {v: k for k, v in _PR_CASE_TO_RU.items()}
        ru = ru_cases.get(alt.get(target_ru_case, "nom"))
    if not ru:
        return None
    gender = entry.get("gender") or "masc"
    return {
        "out": ru,
        "note": f"{entry.get('lemma') or entry.get('lemma')}: имя (PN), {target_num}.{pr_key}",
        "pos": "NOUN",
        "gender": gender,
        "number": "plur" if target_num == "pl" else "sing",
        "ru_case": target_ru_case,
        "consumes_case": True,
    }


def _decline_ru_adjective_forms(ru_adj):
    """Падежные формы русского прилагательного во всех родах и числах (pymorphy3).
    Для прилагательных, которых нет в словаре pymorphy, используется угаданный
    разбор (-ский/-ная и т.п.). Возвращает список словоформ (в нижнем регистре)."""
    try:
        parses = morph.parse(ru_adj)
    except Exception:
        return []
    best = next((p for p in parses if p.tag.POS == "ADJF"), None)
    if best is None:
        return []
    forms = []
    for pym_case in ("nomn", "gent", "datv", "accs", "ablt", "loct"):
        for extra in (("sing", "masc"), ("sing", "femn"), ("sing", "neut"), ("plur",)):
            try:
                f = best.inflect({pym_case} | set(extra))
            except Exception:
                f = None
            if f and f.word:
                forms.append(f.word.lower())
    return forms


def _inflect_ru_adjective(ru_adj, head_word, case="nomn", number=None):
    """Согласует русское прилагательное с головным существительным.

    Род берётся из pymorphy-разбора РУССКОГО слова, а не из прусской граммемы:
    wālinsnā в прусском «женского» рода, а его русский перевод «сражение» —
    среднего, и определение должно быть «Покарвское», а не «Покарвская»."""
    target_case = case if case in ("nomn", "gent", "datv", "accs", "ablt", "loct") else "nomn"
    target_number = "plur" if number in ("plur", "pl") else "sing"
    gender = None
    head = (head_word or "").strip().lower()
    if head:
        try:
            hparses = morph.parse(head)
            hnoun = next((p for p in hparses if p.tag.POS == "NOUN"), None)
            if hnoun is not None:
                if "plur" in hnoun.tag:
                    target_number = "plur"
                else:
                    gender = hnoun.tag.gender
        except Exception:
            pass
    grammemes = {target_number, target_case}
    if target_number == "sing" and gender:
        grammemes.add(gender)
    try:
        parses = morph.parse(ru_adj)
        best = next((p for p in parses if p.tag.POS == "ADJF"), None)
        if best is None:
            return ru_adj
        f = best.inflect(grammemes)
        if f is None and gender:
            f = best.inflect({target_number, target_case})
        if f is None:
            return ru_adj
        out = f.word
        if ru_adj[:1].isupper():
            out = out[:1].upper() + out[1:]
        return out
    except Exception:
        return ru_adj


def _render_pn_adjective_ru(pn_entry, tokens, start_idx, forced_case=None):
    """Определение-прилагательное от топонима вместо родительного:
    'Pakarwjas walinsnā' → «Покарвское сражение» (а не «сражение Покарвиса»).

    Ищем головное существительное впереди (как _head_noun_ahead), берём его
    русский глосс и склоняем entry.ru_adj по pymorphy-роду/числу/падежу.
    Возвращает строку либо None (тогда сработает обычный родительный атрибут)."""
    ru_adj = (pn_entry.get("ru_adj") or "").strip()
    if not ru_adj:
        return None
    j = start_idx + 1
    seen = 0
    while j < len(tokens) and seen < 6:
        tok = tokens[j]
        if PR_PUNCT_TOKEN_RE.match(tok):
            return None
        clean = _clean_pr_token(tok)
        if not clean:
            j += 1
            continue
        seen += 1
        if clean.isdigit():
            j += 1
            continue
        if _lookup_propername(clean):
            j += 1
            continue
        m = _select_pr_match(clean)
        if not m:
            return None
        pos = _match_pos(m)
        if pos in ("NOUN", "NPRO"):
            info = _label_grammar(m[1])
            if info.get("ru_case") not in (None, "nomn", "nom", "accs"):
                return None
            gloss, _note = _ru_gloss_for_entry(m[0], m[1])
            head_word = re.split(r"[,;]+", (gloss or "").strip())[0].strip()
            head_word = re.split(r"\s+", head_word)[0] if head_word else ""
            ru_case = forced_case or info.get("ru_case")
            if ru_case == "nom":
                ru_case = "nomn"
            return _inflect_ru_adjective(ru_adj, head_word, ru_case or "nomn",
                                         info.get("number"))
        if pos in ("ADJF", "PRTF"):
            j += 1
            continue
        return None
    return None


def _clean_pr_token(token):
    return re.sub(r"[^\wāēīōūâêîôûàèìòùáéíóúŠšČčŽž-]", "", token, flags=re.UNICODE).lower()


def _candidate_has_pos(clean_key, pos):
    for entry, _ in _lookup_pr_matches(clean_key):
        override = _override_by_id.get(entry.get("i"))
        if classify_pos(entry, override) == pos:
            return True
    return False


def _match_pos(match):
    if not match:
        return None
    entry, _ = match
    return classify_pos(entry, _override_by_id.get(entry.get("i")))


def _next_pr_case(tokens, start_idx):
    for j in range(start_idx + 1, len(tokens)):
        tok = tokens[j]
        if PR_PUNCT_TOKEN_RE.match(tok):
            return None
        if not PR_WORD_TOKEN_RE.match(tok):
            continue
        clean = _clean_pr_token(tok)
        if clean.isdigit():
            continue
        found = _select_pr_match(clean)
        if found:
            # Формы собственных имён: словарные заглушки падежа не дают,
            # а 'nomn' по умолчанию (_label_grammar для пустой метки) давал
            # ложный nom вместо реального akk главного существительного
            # ('pa Pakarwjas wālinsnan' теряло «после + род.»). У PN-формы
            # падеж известен из самой PN-таблицы ('Ērkun' → akk).
            pn_hit = _lookup_propername(clean)
            if pn_hit:
                if pn_hit[2] == "gen":
                    # Атрибутивный генитив топонима («Pakarwjas wālinsnan») —
                    # предлог управляет ГЛАВНЫМ существительным, а не им:
                    # продолжаем поиск за ним.
                    continue
                if pn_hit[2]:
                    return pn_hit[2]
                continue
            if not found[1]:
                continue
            info = _label_grammar(found[1])
            if info.get("case"):
                return info["case"]
    return None


def _ru_case_after_pr_preposition(prep_clean, next_pr_case):
    mapping = PR_PREP_RU_CASE.get(prep_clean)
    if not mapping:
        return None
    return mapping.get(next_pr_case) or mapping.get(None)


def _select_pr_preposition_sense(clean, next_case, fallback):
    """У одного прусского предлога бывает несколько русских значений с
    разным управлением (pa: dat -> 'под', acc -> 'по'/'после'). Падеж
    следующего слова уже известен (next_case) - используем его, чтобы
    выбрать подходящий смысл, а не всегда первый по порядку в словаре
    (иначе 'по'/'после' с управлением acc всё равно получали бы перевод
    'под', который на самом деле требует dat).

    Если падеж известен, сужаем варианты до тех, что им управляют, и уже
    среди НИХ (не среди всех смыслов) пробуем ручной приоритет из
    priorities.json; на case-слепой fallback откатываемся только если
    падеж следующего слова вообще не удалось определить."""
    senses = _pr_preposition_senses.get(clean)
    if not senses or len(senses) < 2:
        return fallback

    candidates = senses
    if next_case:
        matching = [s for s in senses if s["gov"] == next_case]
        if matching:
            candidates = matching
            if len(matching) == 1:
                return (matching[0]["entry"], "")

    preferred_gloss = _pr_to_ru_priority.get(clean)
    if preferred_gloss:
        for s in candidates:
            first_ru = _split_ru_field(s["entry"].get("ru", ""))[0] if s["entry"].get("ru") else ""
            if _clean_ru_chunk(first_ru) == _clean_ru_chunk(preferred_gloss):
                return (s["entry"], "")

    if next_case:
        return (candidates[0]["entry"], "")

    return fallback


def _preposition_standalone_gloss(clean, fallback_gloss, fallback_note):
    """Падеж следующего слова неизвестен (предлог введён отдельно, без
    существительного) - вместо произвольного выбора первой статьи по
    порядку в словаре показываем все известные значения, например
    'под / после / по (согласно)' для pa, а не только 'под'."""
    senses = _pr_preposition_senses.get(clean)
    if not senses or len(senses) < 2:
        return fallback_gloss, fallback_note

    preferred_gloss = _pr_to_ru_priority.get(clean)
    if preferred_gloss:
        return fallback_gloss, fallback_note  # ручной приоритет уже выбрал смысл

    glosses = []
    for s in senses:
        first_ru = _split_ru_field(s["entry"].get("ru", ""))[0] if s["entry"].get("ru") else ""
        g = _clean_ru_chunk(first_ru)
        if g and g not in glosses:
            glosses.append(g)
    if len(glosses) <= 1:
        return fallback_gloss, fallback_note

    gov_by_gloss = {}
    for s in senses:
        first_ru = _split_ru_field(s["entry"].get("ru", ""))[0] if s["entry"].get("ru") else ""
        g = _clean_ru_chunk(first_ru)
        gov_by_gloss.setdefault(g, s["gov"])
    combined = " / ".join(f"{g} (+{gov_by_gloss[g]})" for g in glosses)
    return combined, f"омограф-предлог, {len(glosses)} значения в зависимости от падежа"


def _russian_noun_agreement(entry, label, forced_case=None):
    gloss, _ = _ru_gloss_for_entry(entry, label, forced_case=forced_case)
    if not gloss or " " in gloss:
        return None
    p = morph.parse(gloss)[0]
    info = _label_grammar(label)
    return {
        "gender": p.tag.gender or "masc",
        "number": info.get("number") or p.tag.number or "sing",
        "case": forced_case or info.get("ru_case") or p.tag.case or "nomn",
        "animacy": p.tag.animacy or "inan",
    }


def _next_pr_noun_agreement(tokens, start_idx, forced_case=None):
    for j in range(start_idx + 1, len(tokens)):
        tok = tokens[j]
        if PR_PUNCT_TOKEN_RE.match(tok):
            return None
        if not PR_WORD_TOKEN_RE.match(tok):
            continue
        clean = _clean_pr_token(tok)
        if clean.isdigit():
            continue
        found = _select_pr_match(clean, prefer_pos="NOUN") or _select_pr_match(clean, prefer_pos="NPRO")
        if found and _match_pos(found) in ("NOUN", "NPRO"):
            return _russian_noun_agreement(found[0], found[1], forced_case=forced_case)
        found_any = _select_pr_match(clean)
        if found_any and _match_pos(found_any) in ("VERB", "PREP", "CONJ", "PRCL", "INTJ", "ADVB"):
            return None
    return None


def _subject_agreement_from_pr(entry, label, output_word=None):
    info = _label_grammar(label)
    word = (entry.get("w") or "").lower()
    if word in {"as", "mes", "tū", "jūs"}:
        if output_word in {"я", "мы", "ты", "вы"}:
            return {
                "я": {"person": "1per", "number": "sing", "gender": "masc"},
                "мы": {"person": "1per", "number": "plur", "gender": None},
                "ты": {"person": "2per", "number": "sing", "gender": "masc"},
                "вы": {"person": "2per", "number": "plur", "gender": None},
            }[output_word]
    # 3-е лицо: род нужен для согласования сказуемого («она поставила»)
    if output_word in ("он", "она", "оно", "они"):
        return {
            "person": "3per",
            "number": "plur" if output_word == "они" else "sing",
            "gender": {"он": "masc", "она": "femn", "оно": "neut", "они": None}.get(output_word),
        }
    if info.get("ru_case") in (None, "nomn"):
        number = info.get("number")
        if not number and output_word:
            p = morph.parse(output_word)[0]
            number = NUMBER_MAP.get(p.tag.number or "sing", "sing")
        if not number:
            number = "sing"
        # Род — у РУССКОГО слова (восстание — ср.р., хотя senskīsnā в прусском
        # женский); прусский род — только запасной вариант.
        gender = (_ru_word_gender(output_word) or info.get("gender") or "masc")
        return {"person": "3per", "number": number, "gender": gender}
    return None


def translate_pr_word(token):
    clean = _clean_pr_token(token)
    if not clean:
        return token, None

    # Однословные статьи корпуса (Ahā, Jā, ēngliskai, Kwēi) должны работать и
    # внутри длинного текста, а не только при переводе слова целиком.
    pb = _pr_phrasebook.get(clean)
    if pb is None:
        pb = _pr_phrasebook_folded.get(fold_diacritics(clean))
    if pb:
        return pb["out"], pb["note"]

    tied = _select_pr_matches_tied(clean)
    if not tied:
        # Собственные имена часто отсутствуют в dictionary.json; PN‑таблица
        # покрывает их и отдаёт русскую форму с правильным падежом/числом.
        pn = _render_propername(token)
        if pn:
            return pn["out"], f"{pn['note']}"
        # Аудит, П.3.1 + П.3.4: исходное слово без [?], формулировка без опечатки
        return token, "слово отсутствует в словаре"

    if len(tied) == 1:
        entry, label = tied[0]
        gloss, note = _ru_gloss_for_entry(entry, label)
        return gloss, f"{entry.get('w')}: {note}"

    # несколько равноправных статей с одной и той же прусской формой
    # (настоящие омографы, например предлог pa) - показываем все известные
    # значения вместо того, чтобы произвольно выбрать одно по порядку в файле
    glosses = []
    for entry, label in tied:
        gloss, _ = _ru_gloss_for_entry(entry, label)
        if gloss and gloss not in glosses:
            glosses.append(gloss)
    if len(glosses) <= 1:
        entry, label = tied[0]
        gloss, note = _ru_gloss_for_entry(entry, label)
        return gloss, f"{entry.get('w')}: {note}"

    combined = " / ".join(glosses)
    return combined, f"{tied[0][0].get('w')}: омограф, {len(glosses)} значения"


def _match_pr_phrase(tokens, start_idx):
    if _pr_max_phrase_words <= 1:
        return None

    # Фразы корпуса часто содержат запятые и тире ("... peisātan, kāi ..."),
    # поэтому фразбук ищем по словам, пропуская внутрифразовую пунктуацию и
    # останавливаясь только на границе предложения.
    pb_parts = []
    pb_positions = []
    j = start_idx
    while j < len(tokens) and len(pb_parts) < _pr_max_phrase_words:
        tok = tokens[j]
        if PR_PUNCT_TOKEN_RE.match(tok):
            if tok in ".!?":
                break
            j += 1
            continue
        if not PR_WORD_TOKEN_RE.match(tok):
            break
        clean = _clean_pr_token(tok)
        if not clean:
            break
        pb_parts.append(clean)
        pb_positions.append(j)
        j += 1
    for size in range(len(pb_parts), 1, -1):
        phrase_key = " ".join(pb_parts[:size])
        pb = (_pr_phrasebook.get(phrase_key)
              or _pr_phrasebook_folded.get(fold_diacritics(phrase_key)))
        if pb:
            end_pos = pb_positions[size - 1]
            # закрывающие кавычки и скобки принадлежат фразе, а знак в конце
            # не дублируем, если он уже есть в готовом переводе
            k = end_pos + 1
            while k < len(tokens) and PR_PUNCT_TOKEN_RE.match(tokens[k]) and tokens[k] not in ".!?":
                k += 1
            if (k < len(tokens) and tokens[k] in ".!?"
                    and str(pb["out"]).rstrip().endswith(tokens[k])):
                k += 1
            return {
                "end": k,
                "src": " ".join(tokens[start_idx:k]),
                "out": pb["out"],
                "note": pb["note"],
                "from_pb": True,
            }

    # Многословные статьи словаря - только по подряд идущим токенам: через
    # запятую они не должны склеиваться.
    parts = []
    positions = []
    j = start_idx
    while j < len(tokens) and len(parts) < _pr_max_phrase_words:
        tok = tokens[j]
        if PR_PUNCT_TOKEN_RE.match(tok):
            break
        if PR_WORD_TOKEN_RE.match(tok):
            clean = _clean_pr_token(tok)
            if not clean:
                break
            parts.append(clean)
            positions.append(j)
        else:
            break
        j += 1
    for size in range(len(parts), 1, -1):
        phrase_key = " ".join(parts[:size])
        found = _lookup_pr(phrase_key)
        if found:
            entry, label = found
            gloss, note = _ru_gloss_for_entry(entry, label)
            return {
                "end": positions[size - 1] + 1,
                "src": " ".join(tokens[start_idx:positions[size - 1] + 1]),
                "out": gloss,
                "note": f"{entry.get('w')}: {note}",
                "from_pb": False,
            }
    return None


def _flush_held(out_words, debug, held):
    """Выводит отложенные в буфер принадлежательные имена (P1 reorder)."""
    if not held:
        return
    for h in held:
        out_words.append(h["out"])
        debug.append({"src": h["src"], "out": h["out"], "note": h["note"]})
    held.clear()


def _next_content_idx(tokens, start):
    """Индекс следующего содержательного токена (без пунктуации), либо None."""
    j = start
    while j < len(tokens):
        tok = tokens[j]
        if PR_PUNCT_TOKEN_RE.match(tok):
            return None
        clean = _clean_pr_token(tok)
        if clean:
            return j
        j += 1
    return None


def _prep_phrase_continues(tokens, i):
    """True, если после токена i ещё идёт слово (имя/прил/сущ) — значит
    предлог управляет не одной, а всей цепочкой («с Еркусом Мантасом»: оба
    имени во мнительном падеже). Падеж удерживаем, а не сбрасываем."""
    j = _next_content_idx(tokens, i + 1)
    if j is None:
        return False
    clean = _clean_pr_token(tokens[j])
    if clean and _lookup_propername(clean):
        return True
    m = _select_pr_match(clean)
    if not m:
        return False
    pos = _match_pos(m)
    if pos == "VERB":
        return False
    return pos in ("NOUN", "NPRO", "ADJF", "PRTF")


def _head_noun_entry_ahead(tokens, start, limit=6):
    """Возвращает (entry, label, idx) головного существительного через ≤limit
    контент-слов (имена/прил/числа пропускаются) после `start`, либо None:
    цепочка принадлежит ему («Ērkus Māntas prūsisks pass» → head = pass)."""
    j = start
    seen = 0
    while j < len(tokens) and seen < limit:
        tok = tokens[j]
        if PR_PUNCT_TOKEN_RE.match(tok):
            return None
        clean = _clean_pr_token(tok)
        if not clean:
            j += 1
            continue
        seen += 1
        if clean.isdigit():
            j += 1
            continue
        pn = _lookup_propername(clean)
        if pn:
            j += 1
            continue
        m = _select_pr_match(clean)
        if not m:
            return None
        pos = _match_pos(m)
        if pos in ("NOUN", "NPRO"):
            info = _label_grammar(m[1])
            if info.get("ru_case") in (None, "nomn", "nom", "accs"):
                return (m[0], m[1], j)
            return None
        if pos in ("ADJF", "PRTF"):
            j += 1
            continue
        return None
    return None


def _head_noun_ahead(tokens, start, limit=6):
    """True, если через ≤limit контент-слов (имена/прил/числа) после `start`
    идёт именительный существительный — т.е. цепочка принадлежит ему
    («Ērkus Māntas prūsisks pass» → head = pass)."""
    return _head_noun_entry_ahead(tokens, start, limit) is not None


def _passive_participle_forms(entry):
    """Множество форм страдательного причастия глагола (headword = основа
    инфинитива + 'ts'), либо None, если парадигмы причастий нет."""
    override = _override_by_id.get(entry.get("i"))
    if not override:
        return None
    inf_word = (entry.get("w") or "").lower()
    inf_stem = inf_word
    for suffix in ("twei", "tun", "tuns"):
        if inf_stem.endswith(suffix):
            inf_stem = inf_stem[:-len(suffix)]
            break
    parts = ((override.get("conjugation") or {}).get("participles") or [])
    if not isinstance(parts, list):
        return None
    for p_def in parts:
        if not isinstance(p_def, dict):
            continue
        hw = (p_def.get("headword") or "").lower()
        if hw and hw == inf_stem + "ts":
            return {f.lower() for f, _l in _collect_forms(p_def) if f}
    return None


def _is_passive_participle_form(entry, label, clean):
    """True, если найденная форма — страдательное причастие ('statīntan',
    'papeisātan'): определяем по парадигме причастия с headword на -ts."""
    if "participles" not in (label or ""):
        return False
    forms = _passive_participle_forms(entry)
    if forms is None:
        # без override-парадигмы — эвристика по форме
        return clean.endswith(("tan", "tans", "tas", "tasmu", "ts", "tā"))
    return clean in forms


def _noun_gen_match(clean_key):
    """Статья существительного/местоимения в родительном падеже, либо None."""
    # притяжательные ('māise brāti' = «мой брат») ведёт отдельное правило;
    # проверяем по ВСЕМ кандидатам формы: у омонима māise выбранная статья
    # может иметь глосс «я», а притяжательное «мой» — рядом
    for _entry, _label in _lookup_pr_matches(clean_key):
        _g = _clean_ru_chunk(
            (_split_ru_field(_entry.get("ru") or ""))[0]) if _entry.get("ru") else ""
        if _g in ("мой", "твой", "наш", "ваш", "свой"):
            return None
    found = _select_pr_match(clean_key, prefer_pos="NOUN")
    if not found or _match_pos(found) not in ("NOUN", "NPRO"):
        return None
    if _label_grammar(found[1]).get("ru_case") != "gent":
        return None
    return found


def _try_genitive_chain(tokens, start, pending_ru_case=None,
                        sentence_start_pending=True, subject_agreement=None):
    """Генитивная цепочка перед головным существительным (pr→ru).

    В прусском родительные определения стоят ПЕРЕД определяемым словом:
    'Undinawas pillis etteikāsnas fōnds' = «фонд воссоздания замка Ундинавы».
    По-русски головное существительное выходит первым, а родительные группы —
    в обратном порядке. Цепочка из одних имён (без существительного в
    генитиве) здесь не забирается — ею ведёт P1-механизм отложенных имён,
    кроме случая дативного управления («памятник Эркусу Мантасу»).

    Число с «m.» перед головным словом сливается с ним в «N-летие + род. падеж»
    ('755 m. gruntinsnan' → «755-летие основания»).

    Возвращает {"end": idx, "items": [(out, src, note), ...],
    "subject": {...}|None} либо None, если шаблон не распознан."""
    n = len(tokens)
    j = start
    units = []            # [{'kind': 'pn'|'noun', 'idxs': [...], 'match': tuple}]
    has_noun_gen = False
    numeral_idx = None    # позиция «755» перед «m.» и головным словом
    head = None

    # у омонима-прилагательного, согласующегося со следующим существительным,
    # приоритет перед именем (как в PN-ветке: 'gīwā minisnā' = «живая память»)
    first_clean = _clean_pr_token(tokens[start])
    if _candidate_has_pos(first_clean, "ADJF") and _next_pr_noun_agreement(
            tokens, start, forced_case=pending_ru_case):
        return None

    while j < n:
        tok = tokens[j]
        if PR_PUNCT_TOKEN_RE.match(tok):
            if (tok == "(" and units and units[-1]["kind"] == "pn"
                    and not units[-1].get("paren") and not units[-1].get("paren_closed")):
                units[-1]["paren"] = True
                units[-1]["idxs"].append(j)
                j += 1
                continue
            if tok == ")" and units and units[-1].get("paren"):
                units[-1]["paren"] = False
                units[-1]["paren_closed"] = True
                units[-1]["idxs"].append(j)
                j += 1
                continue
            return None
        clean = _clean_pr_token(tok)
        if not clean:
            j += 1
            continue
        if clean.isdigit():
            # «755 m. gruntinsnan» → «755-летие основания»
            if units and numeral_idx is None and j + 1 < n:
                nxt = _clean_pr_token(tokens[j + 1])
                if nxt in ("m", "mettan", "mettans"):
                    numeral_idx = j
                    j += 2
                    if j < n and tokens[j] == ".":
                        j += 1
                    continue
            return None
        if tok[:1].isupper():
            pn = _lookup_propername(clean)
            if pn:
                if units and units[-1].get("paren"):
                    # приложение в скобках: (Brandenburgas) при Undinawas
                    units[-1]["idxs"].append(j)
                    j += 1
                    continue
                if (units and units[-1]["kind"] == "pn"
                        and not units[-1].get("paren_closed")):
                    # имя из нескольких слов: Ērkus Māntas
                    units[-1]["idxs"].append(j)
                    j += 1
                    continue
                if pn[2] == "gen" or (
                        pn[2] == "nom" and not (sentence_start_pending
                                                and subject_agreement is None)):
                    units.append({"kind": "pn", "idxs": [j]})
                    j += 1
                    continue
                return None
        found = _noun_gen_match(clean)
        if found:
            units.append({"kind": "noun", "idxs": [j], "match": found})
            has_noun_gen = True
            j += 1
            continue
        # кандидат в головное существительное
        head_found = _select_pr_match(clean, prefer_pos="NOUN")
        if head_found and _match_pos(head_found) in ("NOUN", "NPRO"):
            head_info = _label_grammar(head_found[1])
            if head_info.get("ru_case") != "gent":
                head = (head_found, j)
                break
        return None
    if head is None or not units:
        return None

    (h_entry, h_label), head_idx = head
    first_ru = _split_ru_field(h_entry.get("ru") or "")[0] if h_entry.get("ru") else ""
    head_words = _clean_ru_chunk(first_ru).split()
    head_first_word = head_words[0] if head_words else ""
    # родительный-атрибут при «деревня/город/поле» ведёт P1-механизм приложений
    if not has_noun_gen and numeral_idx is None \
            and head_first_word not in RU_GEN_CHAIN_DAT_GOVERNORS:
        return None
    # и головное слово должно существовать
    if not _entry_has_ru_gloss(h_entry) and not (h_entry.get("ru") or "").strip():
        return None

    dat_units = head_first_word in RU_GEN_CHAIN_DAT_GOVERNORS
    head_forced = "gent" if numeral_idx is not None else pending_ru_case
    head_gloss, head_note = _ru_gloss_for_entry(h_entry, h_label,
                                                forced_case=head_forced)
    if not head_gloss:
        return None

    # определение-прилагательное от топонима: [Pakarwjas][wālinsnas] →
    # «Покарвского сражения» — единая родительная группа
    merged = []
    k = 0
    while k < len(units):
        u = units[k]
        nxt = units[k + 1] if k + 1 < len(units) else None
        if (u["kind"] == "pn" and not u.get("paren_closed") and nxt is not None
                and nxt["kind"] == "noun"):
            pn_hit = _lookup_propername(_clean_pr_token(tokens[u["idxs"][0]]))
            ru_adj = ((pn_hit[0].get("ru_adj") or "").strip() if pn_hit else "")
            if ru_adj:
                entry_n, label_n = nxt["match"]
                base_gloss, _n = _ru_gloss_for_entry(entry_n, label_n)
                head_word = re.split(r"\s+", (base_gloss or "").strip())[0] if base_gloss else ""
                adj = _inflect_ru_adjective(ru_adj, head_word, "gent",
                                            _label_grammar(label_n).get("number"))
                noun_g, _n2 = _ru_gloss_for_entry(entry_n, label_n, forced_case="gent")
                if adj and noun_g:
                    merged.append({
                        "kind": "adjnoun", "out": f"{adj} {noun_g}",
                        "src": f"{tokens[u['idxs'][0]]} {tokens[nxt['idxs'][0]]}",
                    })
                    k += 2
                    continue
        merged.append(u)
        k += 1
    units = merged

    items = []
    if numeral_idx is not None:
        items.append((
            f"{tokens[numeral_idx]}-летие",
            f"{tokens[numeral_idx]} {tokens[numeral_idx + 1]}",
            "число + m. перед существительным → «N-летие» + род. падеж",
        ))
    items.append((head_gloss, tokens[head_idx],
                  f"{h_entry.get('w')}: головное существительное генитивной цепочки; {head_note}"))
    unit_case = "datv" if dat_units else "gent"
    for unit in reversed(units):
        if unit["kind"] == "adjnoun":
            items.append((unit["out"], unit["src"],
                          f"{unit['src']}: определение от топонима, переставлено после «{head_first_word}»"))
        elif unit["kind"] == "noun":
            entry_n, label_n = unit["match"]
            g, _note = _ru_gloss_for_entry(entry_n, label_n, forced_case=unit_case)
            if not g:
                return None
            items.append((g, tokens[unit["idxs"][0]],
                          f"{entry_n.get('w')}: генитив переставлен после «{head_first_word}»"))
        else:  # цепочка имён, возможно с приложением в скобках
            in_paren = False
            for idx in unit["idxs"]:
                tok = tokens[idx]
                if not PR_WORD_TOKEN_RE.match(tok):
                    items.append((tok, tok, "приложение в скобках"))
                    if tok == "(":
                        in_paren = True
                    elif tok == ")":
                        in_paren = False
                    continue
                pn = _render_propername(tok, forced_case=None if in_paren else unit_case,
                                        prefer_nom=bool(in_paren))
                if not pn:
                    return None
                tail = "; приложение к имени" if in_paren else \
                    f"; генитив переставлен после «{head_first_word}»"
                items.append((pn["out"], tok, f"{pn['note']}{tail}"))

    subject = None
    if pending_ru_case is None and numeral_idx is None:
        head_info = _label_grammar(h_label)
        if head_info.get("ru_case") in (None, "nomn"):
            number = head_info.get("number") or "sing"
            subject = {"person": "3per", "number": number,
                       "gender": _ru_word_gender(head_gloss)
                       or head_info.get("gender") or "masc"}
    return {"end": head_idx + 1, "items": items, "subject": subject}


def _head_noun_beyond_genitives(tokens, start, limit=8):
    """Лемма головного существительного за родительными зависимыми (для выбора
    русского предлога: 'en Pakarwjas wālinsnas laūku' → голова laūks → «на»).
    Пропускает имена, числа и родительные существительные."""
    j = start + 1
    seen = 0
    while j < len(tokens) and seen < limit:
        tok = tokens[j]
        if PR_PUNCT_TOKEN_RE.match(tok):
            if tok in ("(", ")"):
                j += 1
                continue
            return None
        clean = _clean_pr_token(tok)
        if not clean:
            j += 1
            continue
        seen += 1
        if clean.isdigit():
            j += 1
            continue
        if tok[:1].isupper() and _lookup_propername(clean):
            j += 1
            continue
        found = _select_pr_match(clean, prefer_pos="NOUN")
        if found and _match_pos(found) in ("NOUN", "NPRO"):
            if _label_grammar(found[1]).get("ru_case") == "gent":
                j += 1
                continue
            return (found[0].get("w") or "").lower()
        return None
    return None


def _ru_sentence_capitalize(text):
    """Заглавная в начале и после границ предложения.

    Сокращения даты «г.»/«д.» границей не считаются: «…23 д. фонд поставил…»
    продолжается со строчной, если дальше идёт не сказуемое-глагол, а
    «…22 д. Произошло сражение» получает заглавную (глагол начинает новое
    предложение). После «г.» ведём себя по-старому: «г. Январь 22 д.» —
    с заглавной, как в принятых примерах корпуса."""
    if not text:
        return text
    out = [text[0].upper()]
    pos = 1
    for m in re.finditer(r"([.!?])(\s+)(\w)", text):
        start = m.start()
        prev = text[start - 1].lower() if start >= 1 else ""
        word = m.group(3)
        cap = True
        if prev in ("г", "д"):
            word_full = re.match(r"\w+", text[m.end() - 1:]).group(0).lower()
            parse0 = morph.parse(word_full)[0] if word_full else None
            tags = str(parse0.tag) if parse0 else ""
            is_finite_verb = ("VERB" in tags and not any(
                t in tags for t in ("INFN", "PRTF", "GRND", "PRTS")))
            cap = is_finite_verb if prev == "д" else True
        out.append(text[pos:start + 1 + len(m.group(2))])
        out.append(word.upper() if cap else word)
        pos = m.end()
    out.append(text[pos:])
    return "".join(out)


def translate_pr_sentence_json(sentence):
    # Готовая пара из корпуса перекрывает пословный разбор: иначе длинная
    # прусская реплика собирается из отдельных глосс и читается как набор слов.
    whole_key = _norm_pr_key(sentence)
    # Аудит, П.2.1: сначала sentence_memory — полные проверенные предложения.
    sm_hit = None
    if whole_key:
        sm_hit = (_pr_sentence_memory.get(whole_key)
                  or _pr_sentence_memory_folded.get(fold_diacritics(whole_key)))
    if sm_hit:
        text = str(sm_hit["out"]).strip()
        return json.dumps({"translation": text, "words": [
            {"src": sentence.strip(), "out": text, "note": sm_hit["note"]}
        ]}, ensure_ascii=False)
    whole_hit = None
    if whole_key:
        whole_hit = (_pr_phrasebook.get(whole_key)
                     or _pr_phrasebook_folded.get(fold_diacritics(whole_key)))
    if whole_hit:
        text = str(whole_hit["out"]).strip()
        return json.dumps({"translation": text, "words": [
            {"src": sentence.strip(), "out": text, "note": whole_hit["note"]}
        ]}, ensure_ascii=False)

    tokens = re.findall(r"[\wāēīōūâêîôûàèìòùáéíóúŠšČčŽž-]+|[^\w\s]", sentence, flags=re.UNICODE)
    # Сокращения года/дня сливаются с числом без пробела: «22d», «1273m».
    # Разбиваем на «число» + «буква-суффикс», иначе токен «22d» не найдётся
    # в словаре и суффикс d/m не сработает (как m → «г.»).
    split_tokens = []
    for _tok in tokens:
        _m_split = re.match(r"^(\d+)([a-zāēīōūâêîôûàèìòùáéíóúŠšČčŽž]+)$", _tok, flags=re.UNICODE)
        if _m_split and _m_split.group(1) and _m_split.group(2):
            split_tokens.append(_m_split.group(1))
            split_tokens.append(_m_split.group(2))
        else:
            split_tokens.append(_tok)
    tokens = split_tokens
    out_words, debug = [], []
    pending_ru_case = None       # русский падеж после прусского предлога
    subject_agreement = None     # подлежащее для выбора лица/числа глагола
    pending_number = False       # предыдущий токен — числительное/квантор (gen.pl)
    held = []                    # P1: отложенные принадлежательные родительные имена
    last_was_phrasebook = False  # последний токен был частью фразбуковой пары
    prev_was_subject_name = False  # предыдущий токен — имя в именительном (субъект)
    prev_was_subject_noun = False  # предыдущий токен — существительное-подлежащее
    finite_verb_seen = False      # в текущем предложении уже было сказуемое
    # Аудит (протекание состояния): признак «ещё не выведено ни одного слова
    # текущего предложения». Раньше для этого проверяли пустой out_words,
    # и после точки во втором предложении слово ошибочно считалось
    # дополнением предыдущего («живая память» теряла согласование).
    # Точка снова делает начало предложения началом предложения.
    sentence_start_pending = True
    i = 0
    n = len(tokens)
    while i < n:
        tok = tokens[i]

        if PR_PUNCT_TOKEN_RE.match(tok):
            if held:
                _flush_held(out_words, debug, held)
            if not (out_words and str(out_words[-1]).endswith(tok)):
                out_words.append(tok)
            pending_ru_case = None
            pending_number = False
            last_was_phrasebook = False
            prev_was_subject_name = False
            prev_was_subject_noun = False
            # Запятая часто отделяет приложение: подлежащее сохраняем, точка — нет.
            if tok in ".!?":
                subject_agreement = None
                finite_verb_seen = False
                sentence_start_pending = True
            i += 1
            continue

        clean = _clean_pr_token(tok)
        if clean.isdigit():
            if held:
                _flush_held(out_words, debug, held)
            out_words.append(tok)
            debug.append({"src": tok, "out": tok, "note": "число"})
            pending_number = True
            last_was_phrasebook = False
            prev_was_subject_name = False
            prev_was_subject_noun = False
            sentence_start_pending = False
            i += 1
            continue
        if clean.lower() in PR_GEN_PL_QUANTIFIERS:
            pending_number = True

        phrase = _match_pr_phrase(tokens, i)
        if phrase:
            if held:
                _flush_held(out_words, debug, held)
            out_words.append(phrase["out"])
            debug.append({"src": phrase["src"], "out": phrase["out"], "note": phrase["note"]})
            i = phrase["end"]
            # Фразбук/корпус глушит PN-атрибутив; многословная СЛОВАРНАЯ статья
            # (например, глагольная «audāi si») — нет: после «произошло»
            # «Pakarwjas walinsnā» — «Покарвское сражение».
            from_pb = bool(phrase.get("from_pb"))
            last_was_phrasebook = from_pb
            if not from_pb and not str(phrase.get("note") or "").startswith(
                    ("phrasebook", "готовый перевод корпуса")):
                finite_verb_seen = True
            prev_was_subject_noun = False
            sentence_start_pending = False
            continue

        # Однословные статьи корпуса (Ahā, Jā, ēngliskai, Kwēi, Prawerru) имеют
        # тот же приоритет, что и многословные: иначе внутри длинного текста они
        # уходят в словарные глоссы и получают не тот смысл.
        pb_word = (_pr_phrasebook.get(clean)
                   or _pr_phrasebook_folded.get(fold_diacritics(clean)))
        if pb_word:
            if held:
                _flush_held(out_words, debug, held)
            out_words.append(pb_word["out"])
            debug.append({"src": tok, "out": pb_word["out"], "note": pb_word["note"]})
            i += 1
            last_was_phrasebook = False
            prev_was_subject_name = False
            prev_was_subject_noun = False
            sentence_start_pending = False
            continue

        # Генитивная цепочка перед головным существительным: 'Undinawas pillis
        # etteikāsnas fōnds' → «фонд воссоздания замка Ундинавы» (порядок
        # родительных групп в русском обратен прусскому).
        gen_chain = _try_genitive_chain(tokens, i, pending_ru_case=pending_ru_case,
                                        sentence_start_pending=sentence_start_pending,
                                        subject_agreement=subject_agreement)
        if gen_chain:
            if held:
                _flush_held(out_words, debug, held)
            for out, src, note in gen_chain["items"]:
                out_words.append(out)
                debug.append({"src": src, "out": out, "note": note})
            if gen_chain.get("subject"):
                subject_agreement = gen_chain["subject"]
                prev_was_subject_noun = True
            else:
                prev_was_subject_noun = False
            prev_was_subject_name = False
            last_was_phrasebook = False
            pending_number = False
            sentence_start_pending = False
            i = gen_chain["end"]
            continue

        prefer_pos = None
        if subject_agreement and _candidate_has_pos(clean, "VERB"):
            prefer_pos = "VERB"
        elif _candidate_has_pos(clean, "ADJF") and _next_pr_noun_agreement(tokens, i, forced_case=pending_ru_case):
            prefer_pos = "ADJF"

        pn_name_hit = _lookup_propername(clean) if tok[:1].isupper() else None
        # P1: принадлежательное имя без предлога, стоящее перед родительным
        # существительным («Ērkus Māntas prūsisks pass»), откладываем и выводим
        # его после существительного: «паспорт Эрка Мантаса». Субъекты — имена в
        # именительном падеже в начале предложения — не трогаем.
        # Если же у формы есть словарный кандидат-прилагательное (gīwā «живая»),
        # согласующийся со следующим существительным, это определение, а не имя:
        # прилагательное выигрывает (аудит: имена, совпадающие с обычными словами).
        if (pn_name_hit is not None
                and (pending_ru_case is None or pn_name_hit[2] == "gen")
                and _head_noun_ahead(tokens, i)
                and not (subject_agreement is None and sentence_start_pending
                         and not held and pn_name_hit[2] == "nom")
                and not last_was_phrasebook
                and not prev_was_subject_name
                and prefer_pos != "ADJF"):
            pn_entry, _pn_num, pn_case = pn_name_hit
            head_ahead = _head_noun_entry_ahead(tokens, i)
            # Родительный топонима перед «ориентиром» (деревня/город/поле) —
            # приложение ПОСЛЕ существительного: 'prei Pakarwjas kāiman' →
            # «под деревней Покарвис», а не «под Покарвисом деревней».
            if (pn_case == "gen" and head_ahead
                    and (head_ahead[0].get("w") or "").lower() in PN_APPOSITION_HEADS):
                pn = _render_propername(tok, forced_case=None, prefer_nom=True)
                if pn and pn.get("out"):
                    held.append({"src": tok, "out": pn["out"],
                                 "note": f"{pn_entry.get('lemma')}: приложение к {head_ahead[0].get('w')}"})
                    sentence_start_pending = False
                    i += 1
                    last_was_phrasebook = False
                    prev_was_subject_name = False
                    prev_was_subject_noun = False
                    continue
            # Именная группа как единый блок (аудит, П.2.2): топоним в родительном
            # перед существительным и с полем ru_adj — согласованное определение:
            # 'Pakarwjas walinsnā' → «Покарвское сражение», а не
            # «сражение Покарвиса»; после предлога падеж берём от него
            # ('pa Pakarwjas wālinsnan' → «после Покарвисского сражения»).
            if pn_case == "gen" and (pn_entry.get("ru_adj") or "").strip():
                adj = _render_pn_adjective_ru(pn_entry, tokens, i,
                                              forced_case=pending_ru_case)
                if adj:
                    out_words.append(adj)
                    debug.append({"src": tok, "out": adj,
                                  "note": f"{pn_entry.get('lemma')}: определение от топонима ({adj})"})
                    sentence_start_pending = False
                    i += 1
                    last_was_phrasebook = False
                    prev_was_subject_name = False
                    prev_was_subject_noun = False
                    continue
            pn = _render_propername(tok, forced_case="gent")
            if pn and pn.get("out"):
                held.append({"src": tok, "out": pn["out"], "note": pn["note"]})
                sentence_start_pending = False
                i += 1
                last_was_phrasebook = False
                prev_was_subject_name = False
                prev_was_subject_noun = False
                continue

        last_was_phrasebook = False
        prev_was_subject_name = False
        # Proper-name priority: если слово написано с заглавной буквы и совпадает
        # с леммой/алиасом из PN‑таблицы — отдаём его, даже если такая форма встречается
        # в словаре как обычное слово (Māntas ≈ mānta «сокровище»).

        if tok[:1].isupper():
            pn_hit = _lookup_propername(clean)

            # Имя обрабатываем, если:
            # 1) оно найдено как nom-форма (точное совпадение с леммой/aliases); или
            # 2) есть pending_ru_case (имя после предлога); или
            # 3) слово в начале предложения (нет ещё out_words) — это, скорее
            #    всего, подлежащее, и даже если pr-форма в propernames записана
            #    как gen-вариант (Hērkus как gen от Ērks), оно должно переводиться
            #    через nom-форму (Эркс). prefer_nom=True форсирует это в _render_propername.
            is_sentence_start = (sentence_start_pending or not out_words or (
                len(out_words) == 1 and out_words[0] in ("«", '"', "(", "[", "—", "–", "-")
            ))
            # prefer_pos == "ADJF" означает: у этой формы есть словарное
            # прилагательное, согласующееся со следующим существительным
            # (атрибутивное «живая память»). Тогда имя собственное пропускаем.
            if pn_hit and prefer_pos != "ADJF" and (pn_hit[2] == "nom" or pending_ru_case or is_sentence_start):
                pn = _render_propername(tok, forced_case=pending_ru_case,
                                        prefer_nom=is_sentence_start and not pending_ru_case)
                if pn:
                    if held:
                        _flush_held(out_words, debug, held)
                    out_words.append(pn["out"])
                    debug.append({"src": tok, "out": pn["out"], "note": pn["note"]})
                    sentence_start_pending = False
                    if pending_ru_case:
                        # удерживаем падеж, если имя ещё не кончилось
                        if not _prep_phrase_continues(tokens, i):
                            pending_ru_case = None
                        prev_was_subject_name = False
                    else:
                        subject_agreement = {"person": "3per", "number": pn["number"], "gender": pn["gender"]}
                        prev_was_subject_name = True
                    i += 1
                    continue

        # Подсказка: если следующее содержательное слово — существительное/
        # местоимение, а текущий кандидат может быть possessive ('мой'),
        # предпочитаем possessive перед существительным ('мой брат', не 'мы брат').
        next_pos_hint = None
        if not prefer_pos:
            for j in range(i + 1, min(i + 4, len(tokens))):
                nt = tokens[j]
                if PR_PUNCT_TOKEN_RE.match(nt):
                    break
                nclean = _clean_pr_token(nt)
                if not nclean or nclean.isdigit():
                    continue
                if _lookup_propername(nclean):
                    next_pos_hint = "NOUN"
                    break
                nm = _select_pr_match(nclean)
                if nm:
                    npos = _match_pos(nm)
                    if npos in ("NOUN", "NPRO", "ADJF", "PRTF"):
                        next_pos_hint = "NOUN" if npos in ("NOUN", "NPRO") else None
                    break

        found = _select_pr_match(clean, prefer_pos=prefer_pos,
                                   verb_agreement=subject_agreement,
                                   next_pos_hint=next_pos_hint)
        if not found:
            # Собственные имена часто не внесены в dictionary.json: PN‑таблица
            # покрывает их и отдаёт русскую форму с нужным падежом/числом.
            pn = _render_propername(tok, forced_case=pending_ru_case)
            if pn:
                if held:
                    _flush_held(out_words, debug, held)
                out_words.append(pn["out"])
                debug.append({"src": tok, "out": pn["out"], "note": pn["note"]})
                if pending_ru_case:
                    # падеж удерживаем, если имя ещё не кончилось («с Еркусом Мантасом»)
                    if not _prep_phrase_continues(tokens, i):
                        pending_ru_case = None
                elif pn["ru_case"] in (None, "nomn"):
                    subject_agreement = {"person": "3per", "number": pn["number"], "gender": pn["gender"]}
                i += 1
                continue
            # Собственные имена в словарь часто не внесены; лучше оставить их в
            # тексте как есть (аудит, П.3.1).
            if tok[:1].isupper():
                if held:
                    _flush_held(out_words, debug, held)
                out_words.append(tok)
                debug.append({"src": tok, "out": tok, "note": "вероятно, имя собственное; слово отсутствует в словаре"})
                sentence_start_pending = False
                if not pending_ru_case:
                    subject_agreement = {"person": "3per", "number": "sing", "gender": "masc"}
            else:
                # Аудит, П.3.1 + П.3.2: исходное слово без [?] в переводе,
                # пометка — только в диагностической таблице.
                out_words.append(tok)
                debug.append({"src": tok, "out": tok, "note": "слово отсутствует в словаре"})
                sentence_start_pending = False
            i += 1
            continue

        entry, label = found
        # Свежие статьи корпуса несут падеж/число в поле s, но в PR-индекс
        # попадают с пустой меткой («miksjans» → «немец» без склонения).
        if not label:
            label = _label_from_s_field(entry.get("s") or "")
        pos = _match_pos(found)

        # Если идёт не голова предложения, а глагол/предлог/союз — значит
        # отложенные принадлежательные имена не нашли себя головного существительного
        # (цепочка прервалась): выводим их на месте.
        if held and pos not in ("NOUN", "NPRO", "ADJF", "PRTF"):
            _flush_held(out_words, debug, held)

        # «ni pastāi statīntan» = «не установлен»: связка «стал» перед кратким
        # страдательным причастием по-русски опускается (причастие-предикатив).
        if clean == "pastāi":
            nxt_idx = _next_content_idx(tokens, i)
            if nxt_idx is not None:
                nxt_clean = _clean_pr_token(tokens[nxt_idx])
                nxt_match = _select_pr_match(nxt_clean)
                if (nxt_match and "participles" in (nxt_match[1] or "")
                        and _is_passive_participle_form(nxt_match[0], nxt_match[1], nxt_clean)):
                    debug.append({"src": tok, "out": "",
                                  "note": "pastāi: связка опущена перед кратким страдательным причастием"})
                    finite_verb_seen = True
                    prev_was_subject_noun = False
                    sentence_start_pending = False
                    i += 1
                    continue

        if pos == "PREP":
            next_case = _next_pr_case(tokens, i)
            entry, label = _select_pr_preposition_sense(clean, next_case, (entry, label))
            pending_ru_case = _ru_case_after_pr_preposition(clean, next_case)
            pending_number = False
            gloss, note = _ru_gloss_for_entry(entry, label)
            # Русский предлог выбирается по головному существительному за
            # родительной цепочкой: 'en ... laūku' = «на поле», а не «в поле».
            by_head = PR_PREP_RU_GLOSS_BY_HEAD.get(clean)
            head_w = _head_noun_beyond_genitives(tokens, i)
            if by_head and head_w and by_head.get(head_w):
                gloss = by_head[head_w]
                note = f"перед «{head_w}» → «{gloss}»"
            if not next_case:
                # нет следующего слова (или его падеж не определить) - значит,
                # контекстно сузить смысл нечем; показываем все известные
                # значения, а не только то, что выиграло бы по умолчанию
                gloss, note = _preposition_standalone_gloss(clean, gloss, note)
            out_words.append(gloss)
            debug.append({"src": tok, "out": gloss, "note": f"{entry.get('w')}: {note}; далее {pending_ru_case or 'словарный падеж'}"})
            prev_was_subject_noun = False
            i += 1
            continue

        agreement = None
        # Контекстное правило для причастий после связки: если причастие
        # (с меткой 'participles...') идёт после глагола-связки (ast, pastāi,
        # bēi, etc.), оно является предикативом и должно переводиться в
        # именительном падеже, а не в винительном (который даётся меткой akk).
        # Пример: 'ni pastāi statīntan' = 'не был установлен' (statīntan
        # имеет label masc.sg.akk, но в контексте pastāi должно быть nom).
        # Важно: classify_pos для форм причастий возвращает VERB (потому что
        # entry.w = инфинитив), поэтому проверяем не pos=='PRTF', а label.
        is_participle_form = "participles" in (label or "")
        # effective_case_for_participle будет передан как forced_case в _ru_gloss_for_entry
        effective_case_for_participle = pending_ru_case
        short_participle = False
        if is_participle_form or pos in ("ADJF", "PRTF"):
            # Смотрим на 1-2 предыдущих содержательных токена
            prev_words = []
            for j in range(max(0, i - 3), i):
                pt = tokens[j] if j < len(tokens) else ""
                if PR_PUNCT_TOKEN_RE.match(pt):
                    break
                pclean = _clean_pr_token(pt)
                if pclean:
                    prev_words.append(pclean.lower())
            # Если предыдущее слово — связка, форсируем nom для причастия
            copula_words = {"ast", "bēi", "bīma", "bīmai", "astmai", "astei",
                            "pastāi", "pastāimai", "pastāitei", "wīrst", "wīrstmai",
                            "wīrstats"}
            short_participle = False
            if is_participle_form and any(w in copula_words for w in prev_words[-2:]):
                # forced_case: nomn (если нет pending_ru_case от предлога)
                if not pending_ru_case:
                    effective_case_for_participle = "nomn"
                # страдательное причастие-предикатив после связки — краткая форма:
                # «будет установлен», «не установлен» (а не «установленный»)
                short_participle = _is_passive_participle_form(entry, label, clean)
                agreement = {"case": effective_case_for_participle,
                              "number": None, "gender": None}
            else:
                agreement = _next_pr_noun_agreement(tokens, i, forced_case=pending_ru_case)

        # Причастие прошедшего времени непосредственно после подлежащего-
        # существительного (конечного глагола в предложении ещё не было) —
        # это сказуемое: 'Senskisnā spārtinusi si' → «восстание усилилось».
        # Формы на -usi/-uns — действительное прош. вр. (-ts страдательное,
        # -ants/-ints настоящее). Род/число берём у РУССКОГО подлежащего,
        # возвратное 'si' сливаем в '-сь/-ся'.
        if (is_participle_form and clean.endswith(("usi", "uns"))
                and prev_was_subject_noun and not finite_verb_seen
                and not pending_ru_case and out_words):
            ru_subject = out_words[-1]
            subj_gender = _ru_word_gender(ru_subject) or "masc"
            subj_num = "plur" if (subject_agreement or {}).get("number") in ("plur", "pl") else "sing"
            verb_variants = _split_ru_field(entry.get("ru") or "")
            verb_sv = _clean_ru_chunk(verb_variants[-1]) if verb_variants else ""
            vp = morph.parse(verb_sv)[0] if verb_sv else None
            finite = None
            if vp is not None:
                try:
                    fin = vp.inflect({"past", subj_num, subj_gender})
                    finite = fin.word if fin else None
                except Exception:
                    finite = None
            if finite:
                nxt_clean = _clean_pr_token(tokens[i + 1]) if i + 1 < n else ""
                if nxt_clean == "si":
                    finite += "сь" if finite[-1:] in "аеёиоуыэюя" else "ся"
                if held:
                    _flush_held(out_words, debug, held)
                out_words.append(finite)
                debug.append({"src": tok, "out": finite,
                              "note": f"{entry.get('w')}: причастие-сказуемое → конечный глагол"})
                if nxt_clean == "si":
                    debug.append({"src": tokens[i + 1], "out": "",
                                  "note": "возвратная частица слита с глаголом"})
                    i += 1
                finite_verb_seen = True
                prev_was_subject_noun = False
                sentence_start_pending = False
                i += 1
                continue

        # Аудит-паттерн «mans/māise»: притяжательное («мой/твой/наш/ваш/свой»)
        # в прусском часто стоит в родительной форме перед существительным,
        # но по-русски требует именительного: «мой брат», а не «моего брат».
        # Согласуем с родом/числом головного существительного. При генитиве
        # от квантора (delli...) и после предлога правило не применяется.
        if (pos in ("NOUN", "NPRO") and not pending_number and not pending_ru_case
                and not agreement):
            first_gloss = _clean_ru_chunk(
                (_split_ru_field(entry.get("ru") or ""))[0]) if entry.get("ru") else ""
            info0 = _label_grammar(label)
            if (first_gloss in ("мой", "твой", "наш", "ваш", "свой")
                    and info0.get("ru_case") == "gent"):
                nxt = _next_pr_noun_agreement(tokens, i, forced_case=None)
                if nxt and nxt.get("case") in ("nomn", "accs"):
                    agreement = nxt

        gloss, note = _ru_gloss_for_entry(
            entry,
            label,
            forced_case=effective_case_for_participle,
            agreement=agreement,
            subject_gender=(subject_agreement or {}).get("gender"),
            subject_number=(subject_agreement or {}).get("number"),
            num_government=pending_number,
            short_participle=short_participle,
        )
        out_words.append(gloss)
        debug.append({"src": tok, "out": gloss, "note": f"{entry.get('w')}: {note}"})
        sentence_start_pending = False

        info = _label_grammar(label)
        if pos in ("NOUN", "NPRO"):
            if pending_ru_case:
                if not _prep_phrase_continues(tokens, i):
                    pending_ru_case = None
            elif info.get("ru_case") in (None, "nomn"):
                # Союзы/частицы (be, jā, ni...) классифицируются как NOUN
                # из-за пустой пометы в словаре и затирали подлежащее:
                # 'be wērau' давало «и продолжался» вместо «и продолжалось».
                gp = morph.parse(_clean_ru_token(gloss) or gloss)
                if gp and str(gp[0].tag.POS) not in ("CONJ", "PRCL", "INTJ", "PREP"):
                    subj = _subject_agreement_from_pr(entry, label, gloss)
                    if subj:
                        subject_agreement = subj
                        prev_was_subject_noun = True
                else:
                    prev_was_subject_noun = False
            else:
                prev_was_subject_noun = False
            # P1: головное существительное выведено — теперь можно вывести
            # отложенные принадлежательные имена («паспорт Эрка Мантаса»).
            if held:
                _flush_held(out_words, debug, held)
        elif pos == "VERB":
            # После сказуемого подлежащее уже использовано, но его род может
            # понадобиться только для этого глагола.
            pending_number = False
            finite_verb_seen = True
            prev_was_subject_noun = False
        elif pos in ("CONJ", "PRCL", "INTJ"):
            pending_ru_case = None
            pending_number = False

        i += 1

    if held:
        _flush_held(out_words, debug, held)
    result = " ".join(out_words).replace(" ,", ",").replace(" .", ".").replace(" ?", "?").replace(" !", "!")
    result = result.replace("( ", "(").replace(" )", ")")
    # Русское предложение: первая буква заглавная и после .!? (собственные имена
    # уже пришли с заглавной из словаря — .upper() к ним не меняет букву).
    result = _ru_sentence_capitalize(result)
    # «о» -> «об» перед гласной (о/об, предлог).
    result = re.sub(r"(?<![а-яёА-ЯЁ])о ([ЭюяЁэюя])", lambda m: "об " + m.group(1), result)
    return json.dumps({"translation": result, "words": debug}, ensure_ascii=False)
