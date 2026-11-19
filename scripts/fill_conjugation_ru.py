# -*- coding: utf-8 -*-
"""Приоритет 2 (аудит Data 2.3): автозаполнение русских форм в глагольных
спряжениях overrides.json.

Для каждого conjugation-override находим словарную статью по id, берём её
русский глосс, выбираем первый глагольный смысл (pymorphy3) и заполняем
пустые поля ru в строках indicative present / past / future:

  present:  IMPF → {pres, число, лицо}; PERF → {futr, ...} (сов. вид:
            будущее = настоящее);
  future:   PERF → {futr, ...}; IMPF остаётся пустым (pymorphy не умеет
            аналитическое будущее «буду ставить» — движок сам подставит
            презенс);
  past:     ед.ч. → {past, sing, masc} (движок согласует род подлежащего
            во время перевода), мн.ч. → {past, plur}.

Существующие ru не перезаписываются (ручные правки statīntun и др.
остаются). Строки perfect/imperative не трогаем — движок их для pr→ru
не читает.

Запуск: python3 scripts/fill_conjugation_ru.py [--dry]
"""
import json
import os
import re
import sys

import pymorphy3

ROOT = "/home/z/my-project/download/ghsite_release"
morph = pymorphy3.MorphAnalyzer()

PERSON_SIGNS = [
    ("(он/она/оно)", "3per", "sing"),
    ("(он)", "3per", "sing"),
    ("(я)", "1per", "sing"),
    ("(ты)", "2per", "sing"),
    ("(мы)", "1per", "plur"),
    ("(вы)", "2per", "plur"),
    ("(они)", "3per", "plur"),
    # future/perfect-строки часто идут «голыми» местоимениями без скобок
    ("as", "1per", "sing"),
    ("tū", "2per", "sing"),
    ("tāns/tenā/tennan", "3per", "sing"),
    ("tāns/tenā", "3per", "sing"),
    ("tennan", "3per", "sing"),
    ("mes", "1per", "plur"),
    ("jūs", "2per", "plur"),
    ("tenēi/tennas", "3per", "plur"),
]


def pick_verb_parse(ru_field):
    """Первый смысл глосса, который pymorphy разбирает как глагол."""
    parts = re.split(r"[,;/]", ru_field or "")
    for part in parts:
        p = re.sub(r"\([^)]*\)", "", part).strip()
        p = re.sub(r"\s+", " ", p)
        if not p:
            continue
        for cand in (p, _strip_tail_prep(p)):
            if not cand:
                continue
            for ps in morph.parse(cand):
                if ps.tag.POS in ("INFN", "VERB"):
                    return ps
        # последнее средство для составных глоссов («варить пиво»): берём
        # первый токен, если он сам глагол
        first = p.split()[0]
        for ps in morph.parse(first):
            if ps.tag.POS in ("INFN", "VERB"):
                return ps
    return None


_TAIL_PREPS = {"с", "на", "от", "по", "в", "во", "за", "к", "ко", "о", "об",
               "из", "у", "для", "про", "над", "под", "между", "без", "перед"}


def _strip_tail_prep(p):
    """«граничить с» → «граничить»: глоссы часто несут хвостовое управление."""
    tokens = p.split()
    if len(tokens) > 1 and tokens[-1].lower() in _TAIL_PREPS:
        return " ".join(tokens[:-1])
    return None


def row_person_number(row):
    p = row.get("p") or ""
    for sign, person, number in PERSON_SIGNS:
        if sign in p:
            return person, number
    return None, None


def inflect_verb(parse, grammemes):
    try:
        fin = parse.inflect(grammemes)
    except Exception:
        fin = None
    return fin.word if fin else None


def ru_for_row(parse, tense, person, number):
    if tense in ("present", "future"):
        bases = ("pres", "futr") if tense == "present" else ("futr", "pres")
        for base in bases:
            w = inflect_verb(parse, {base, number, person})
            if w:
                return w
        return None
    if tense == "past":
        if number == "sing":
            return inflect_verb(parse, {"past", "sing", "masc"})
        return inflect_verb(parse, {"past", "plur"})
    return None


def main():
    dry = "--dry" in sys.argv
    with open(os.path.join(ROOT, "data", "dictionary.json"), encoding="utf-8") as fh:
        dict_data = json.load(fh)
    words = dict_data if isinstance(dict_data, list) else dict_data.get("w", [])
    id2entry = {e.get("i"): e for e in words}

    with open(os.path.join(ROOT, "data", "overrides.json"), encoding="utf-8") as fh:
        ovs = json.load(fh)

    filled = skipped_gloss = skipped_row = verbs_touched = 0
    for ov in ovs:
        conj = ov.get("conjugation")
        if not isinstance(conj, dict):
            continue
        entry = id2entry.get(ov.get("id")) if ov.get("id") is not None else None
        gloss = (entry or {}).get("ru") or ""
        parse = pick_verb_parse(gloss)
        if parse is None:
            skipped_gloss += 1
            continue
        touched = False
        indic = conj.get("indicative")
        if not isinstance(indic, dict):
            continue
        for tense in ("present", "past", "future"):
            rows = indic.get(tense)
            if not isinstance(rows, list):
                continue
            for row in rows:
                if not isinstance(row, dict):
                    continue
                if (row.get("ru") or "").strip():
                    continue  # ручные формы не трогаем
                person, number = row_person_number(row)
                if not person:
                    skipped_row += 1
                    continue
                ru = ru_for_row(parse, tense, person, number)
                if ru:
                    row["ru"] = ru
                    filled += 1
                    touched = True
        if touched:
            verbs_touched += 1

    print(f"строк заполнено: {filled}")
    print(f"глаголов затронуто: {verbs_touched}")
    print(f"без verb-глосса: {skipped_gloss}")
    print(f"строк без распознанного лица: {skipped_row}")

    if dry:
        print("DRY — файл не записан")
        return
    with open(os.path.join(ROOT, "data", "overrides.json"), "w", encoding="utf-8") as fh:
        json.dump(ovs, fh, ensure_ascii=False, indent=1)
    print("overrides.json записан")


if __name__ == "__main__":
    main()
