/* Переводчик RU -> прусский: загрузка Pyodide + pymorphy3, обвязка UI.
   Вся переводческая логика находится в translate_core.py и не меняется
   для работы в браузере — только источники данных заменены на fetch(). */

// Аудит: фиксированные версии пакетов — чтобы обновления PyPI не ломали сайт.
const PKG_VERSIONS = ["pymorphy3==2.0.6", "pymorphy3-dicts-ru==2.4.417150.4580142"];
const DATA_CACHE = "prussian-translator-data-v1";

const statusText = document.getElementById("status-text");
const loadingPanel = document.getElementById("loading");
const appPanel = document.getElementById("app");
const errorPanel = document.getElementById("error");
const errorText = document.getElementById("error-text");
const readyNote = document.getElementById("ready-note");
const translateBtn = document.getElementById("translate-btn");
const reloadBtn = document.getElementById("reload-btn");
const progressBar = document.getElementById("progress-bar");
const progressFill = document.getElementById("progress-fill");
const progressLabel = document.getElementById("progress-label");
const input = document.getElementById("input");
const resultWrap = document.getElementById("result-wrap");
const resultText = document.getElementById("result-text");
const breakdownBody = document.getElementById("breakdown-body");
const breakdownDetails = document.getElementById("breakdown-details");
const viewPlainBtn = document.getElementById("view-plain");
const viewBreakdownBtn = document.getElementById("view-breakdown");
const dirRuPrBtn = document.getElementById("dir-ru-pr");
const dirPrRuBtn = document.getElementById("dir-pr-ru");
const inputLabel = document.getElementById("input-label");
const resultLabel = document.getElementById("result-label");

// --- Обратная связь -------------------------------------------------------
// Заполните перед или сразу после деплоя (репозиторий появится только
// после того, как вы его создадите на GitHub). Если оставить пустым —
// соответствующая кнопка просто не показывается, скопировать отчёт
// можно всегда, это не требует настройки.
const FEEDBACK_CONFIG = {
  githubRepo: "", // например: "stanislavas/prussian-translator"
  email: "",      // например: "you@example.com"
};

let lastResult = null; // { direction, inputText, data } - для контекстного отчёта

let direction = "ru-pr"; // "ru-pr" | "pr-ru"

const DIRECTION_UI = {
  "ru-pr": {
    inputLabel: "Фраза по-русски",
    placeholder: "Например: Брат идёт в лес",
    resultLabel: "Прусский (черновой перевод)",
  },
  "pr-ru": {
    inputLabel: "Фраза по-прусски",
    placeholder: "Например: kaīls, brāti",
    resultLabel: "Русский (черновой перевод)",
  },
};

function setDirection(dir) {
  direction = dir;
  dirRuPrBtn.classList.toggle("active", dir === "ru-pr");
  dirPrRuBtn.classList.toggle("active", dir === "pr-ru");
  const ui = DIRECTION_UI[dir];
  inputLabel.textContent = ui.inputLabel;
  input.placeholder = ui.placeholder;
  resultLabel.textContent = ui.resultLabel;
  resultWrap.classList.add("hidden");
}

dirRuPrBtn.addEventListener("click", () => setDirection("ru-pr"));
dirPrRuBtn.addEventListener("click", () => setDirection("pr-ru"));

function setStatus(msg) {
  statusText.textContent = msg;
}

// Аудит: отображение прогресса по этапам загрузки.
function setProgress(pct, label) {
  if (!progressBar) return;
  if (pct >= 100) {
    progressBar.classList.add("hidden");
    return;
  }
  progressBar.classList.remove("hidden");
  if (progressFill) progressFill.style.width = pct + "%";
  if (progressLabel && label) progressLabel.textContent = label;
  if (statusText) statusText.textContent = label || statusText.textContent;
}

// Аудит: собственное кэширование данных проекта через Cache API.
// Сообщение «дальше браузер кэширует» раньше было обещанием без реализации —
// теперь файлы данных реально сохраняются в кэш и берутся оттуда при
// повторных заходах (работает в https, в т.ч. на GitHub Pages).
async function fetchCached(url) {
  if (typeof caches === "undefined") return fetchText(url); // http/file без кэша
  try {
    const cache = await caches.open(DATA_CACHE);
    const hit = await cache.match(url);
    if (hit) return hit.text();
    const resp = await fetch(url);
    if (!resp.ok) throw new Error(`${url}: HTTP ${resp.status}`);
    const text = await resp.text();
    try { await cache.put(url, new Response(text)); } catch (e) { /* квота — не критично */ }
    return text;
  } catch (err) {
    // Кэш недоступен (приватный режим, квота) — просто fetch
    return fetchText(url);
  }
}

// Аудит: кнопка «Обновить данные» — сброс кэша и перезагрузка.
async function resetDataCacheAndReload() {
  if (typeof caches !== "undefined") {
    try { await caches.delete(DATA_CACHE); } catch (e) { /* ignore */ }
  }
  location.reload();
}
if (reloadBtn) {
  reloadBtn.addEventListener("click", resetDataCacheAndReload);
  reloadBtn.classList.remove("hidden");
}

function showFatalError(msg) {
  loadingPanel.classList.add("hidden");
  errorPanel.classList.remove("hidden");
  errorText.textContent = msg;
}

async function fetchText(url) {
  const response = await fetch(url);
  if (!response.ok) throw new Error(`${url}: HTTP ${response.status}`);
  return response.text();
}

async function fetchCachedText(url) {
  return fetchCached(url);
}

async function fetchOptionalText(url, fallback = "[]") {
  try {
    return await fetchText(url);
  } catch (err) {
    // Optional data files (for example phrasebook.json) should not block boot.
    console.warn(`Optional file ${url} was not loaded`, err);
    return fallback;
  }
}

function joinJsonArrayShards(shardTexts) {
  const parts = [];
  for (const text of shardTexts) {
    const trimmed = text.trim();
    if (trimmed === "[]") continue;
    if (!trimmed.startsWith("[") || !trimmed.endsWith("]")) {
      throw new Error("Shard is not a JSON array");
    }
    const body = trimmed.slice(1, -1).trim();
    if (body) parts.push(body);
  }
  return `[${parts.join(",")}]`;
}

async function loadShardedSection(manifest, sectionName) {
  const section = manifest[sectionName];
  if (!section || !Array.isArray(section.shards) || !section.shards.length) {
    throw new Error(`manifest: missing ${sectionName} shards`);
  }
  const shardTexts = await Promise.all(section.shards.map((shard) => {
    if (!shard.path) throw new Error(`manifest: bad ${sectionName} shard path`);
    return fetchCached(`data/shards/${shard.path}`);
  }));
  return joinJsonArrayShards(shardTexts);
}

async function loadDictionaryData() {
  try {
    const manifestResponse = await fetchCached("data/shards/manifest.json");
    const manifest = JSON.parse(manifestResponse);
    if (manifest.schema !== 1) throw new Error("manifest.json: unsupported schema");

    const dictCount = manifest.dictionary?.shards?.length || 0;
    const overrideCount = manifest.overrides?.shards?.length || 0;
    setProgress(72, `Загружаю индексированные части словаря (${dictCount + overrideCount} файлов)…`);
    const [dictText, overridesText] = await Promise.all([
      loadShardedSection(manifest, "dictionary"),
      loadShardedSection(manifest, "overrides"),
    ]);
    return { dictText, overridesText, manifest, mode: "shards" };
  } catch (err) {
    console.warn("Sharded dictionary load failed; falling back to legacy JSON files", err);
    setStatus("Индексы не найдены, загружаю большие JSON-файлы словаря…");
    const [dictText, overridesText] = await Promise.all([
      fetchCached("data/dictionary.json"),
      fetchCached("data/overrides.json"),
    ]);
    return { dictText, overridesText, manifest: null, mode: "legacy" };
  }
}

async function boot() {
  try {
    setProgress(5, "Загружаю Pyodide (python в браузере)…");
    const pyodide = await loadPyodide();

    setProgress(30, "Устанавливаю pymorphy3 и русский словарь форм (~10 МБ, один раз)…");
    await pyodide.loadPackage("micropip");
    const micropip = pyodide.pyimport("micropip");
    // Аудит: фиксированные версии — обновления PyPI не ломают сайт внезапно.
    await micropip.install(PKG_VERSIONS);

    setProgress(65, "Загружаю данные словаря Prūsiska bilā…");
    const [dataFiles, phrasebookText, prioritiesText, propernamesText, verbFramesText, sentenceMemoryText, coreCode] = await Promise.all([
      loadDictionaryData(),
      fetchOptionalText("data/phrasebook.json", "[]"),
      fetchOptionalText("data/priorities.json", "{}"),
      fetchOptionalText("data/propernames.json", "{}"),
      fetchOptionalText("data/verb_frames.json", "{}"),
      fetchOptionalText("data/sentence_memory.json", "[]"),
      fetchText("translate_core.py"),
    ]);

    setProgress(90, "Строю индексы (словоформы, предлоги, парадигмы)…");
    await pyodide.runPythonAsync(coreCode);
    const loadData = pyodide.globals.get("load_data");
    const stats = loadData(
      dataFiles.dictText,
      dataFiles.overridesText,
      phrasebookText,
      prioritiesText,
      propernamesText,
      verbFramesText,
      sentenceMemoryText
    ).toJs({ dict_converter: Object.fromEntries });

    const dataMode = dataFiles.mode === "shards" ? "индексы" : "большие JSON";
    readyNote.textContent = `Слов: ${stats.words} · с парадигмами: ${stats.overrides} · фраз: ${stats.phrases || 0} · предложений корпуса: ${stats.sentence_memory || 0} · глаг. моделей: ${stats.verb_frames || 0} · имен: ${stats.propernames || 0} · данные: ${dataMode}`;

    const translateSentenceJson = pyodide.globals.get("translate_sentence_json");
    const translatePrSentenceJson = pyodide.globals.get("translate_pr_sentence_json");
    window.__translate = {
      "ru-pr": (text) => JSON.parse(translateSentenceJson(text)),
      "pr-ru": (text) => JSON.parse(translatePrSentenceJson(text)),
    };

    setProgress(100, "Готово");
    loadingPanel.classList.add("hidden");
    appPanel.classList.remove("hidden");
    input.focus();
  } catch (err) {
    console.error(err);
    showFatalError(
      "Не удалось загрузить переводчик: " + (err && err.message ? err.message : err) +
      ". Проверьте подключение к интернету (нужен доступ к cdn.jsdelivr.net и pypi.org для первой загрузки) и обновите страницу."
    );
  }
}

// Аудит, П.3.5: режим отображения — «Перевод» (по умолчанию) или
// «Перевод с разбором». Выбор сохраняется между заходами.
let viewMode = "plain";
try {
  const saved = localStorage.getItem("view-mode");
  if (saved === "plain" || saved === "breakdown") viewMode = saved;
} catch (e) { /* localStorage недоступен — не критично */ }

function applyViewMode() {
  if (viewPlainBtn) viewPlainBtn.classList.toggle("active", viewMode === "plain");
  if (viewBreakdownBtn) viewBreakdownBtn.classList.toggle("active", viewMode === "breakdown");
  if (breakdownDetails) breakdownDetails.classList.toggle("hidden", viewMode !== "breakdown");
}

if (viewPlainBtn) viewPlainBtn.addEventListener("click", () => {
  viewMode = "plain";
  try { localStorage.setItem("view-mode", viewMode); } catch (e) { /* ignore */ }
  applyViewMode();
});
if (viewBreakdownBtn) viewBreakdownBtn.addEventListener("click", () => {
  viewMode = "breakdown";
  try { localStorage.setItem("view-mode", viewMode); } catch (e) { /* ignore */ }
  applyViewMode();
});
applyViewMode();

function renderResult(data) {
  resultText.textContent = data.translation || "—";
  breakdownBody.innerHTML = "";
  for (const w of data.words) {
    const tr = document.createElement("tr");
    const src = document.createElement("td");
    src.textContent = w.src;
    const out = document.createElement("td");
    out.textContent = w.out;
    const note = document.createElement("td");
    note.textContent = w.note || "";
    tr.append(src, out, note);
    breakdownBody.appendChild(tr);
  }
  resultWrap.classList.remove("hidden");
  applyViewMode();
}

function doTranslate() {
  const text = input.value.trim();
  if (!text || !window.__translate) return;
  const data = window.__translate[direction](text);
  renderResult(data);
  lastResult = { direction, inputText: text, data };
  updateFeedbackLinks();
}

// --- Обратная связь --------------------------------------------------------

const DIRECTION_LABEL = { "ru-pr": "русский → прусский", "pr-ru": "прусский → русский" };

function buildReportText(comment) {
  const lines = ["Отзыв о переводчике Prūsiska bilā", "Страница: " + location.href, ""];

  if (lastResult) {
    lines.push("Направление: " + (DIRECTION_LABEL[lastResult.direction] || lastResult.direction));
    lines.push("Ввод: " + lastResult.inputText);
    lines.push("Перевод: " + (lastResult.data.translation || "—"));
    if (lastResult.data.words && lastResult.data.words.length) {
      lines.push("Разбор:");
      for (const w of lastResult.data.words) {
        lines.push(`  ${w.src} -> ${w.out}${w.note ? " (" + w.note + ")" : ""}`);
      }
    }
    lines.push("");
  }

  lines.push("Комментарий: " + (comment && comment.trim() ? comment.trim() : "(не указан)"));
  return lines.join("\n");
}

async function copyReport(text, noteEl) {
  try {
    await navigator.clipboard.writeText(text);
  } catch (err) {
    // запасной путь для браузеров/контекстов без Clipboard API
    const ta = document.createElement("textarea");
    ta.value = text;
    ta.style.position = "fixed";
    ta.style.opacity = "0";
    document.body.appendChild(ta);
    ta.select();
    try { document.execCommand("copy"); } catch (e2) { /* сдаёмся молча */ }
    document.body.removeChild(ta);
  }
  if (noteEl) {
    noteEl.classList.remove("hidden");
    setTimeout(() => noteEl.classList.add("hidden"), 4000);
  }
}

function githubIssueUrl(title, body) {
  if (!FEEDBACK_CONFIG.githubRepo) return null;
  const qs = `title=${encodeURIComponent(title)}&body=${encodeURIComponent(body)}`;
  return `https://github.com/${FEEDBACK_CONFIG.githubRepo}/issues/new?${qs}`;
}

function mailtoUrl(subject, body) {
  if (!FEEDBACK_CONFIG.email) return null;
  // mailto (RFC 6068) требует процентное кодирование пробелов как %20, а не
  // "+", как это делает URLSearchParams - иначе часть почтовых клиентов
  // покажет плюсы прямо в тексте письма.
  const qs = `subject=${encodeURIComponent(subject)}&body=${encodeURIComponent(body)}`;
  return `mailto:${FEEDBACK_CONFIG.email}?${qs}`;
}

function wireFeedbackLinkPair(githubEl, emailEl, buildTitle, buildBody) {
  const ghUrl = githubIssueUrl(buildTitle(), buildBody());
  if (ghUrl) {
    githubEl.href = ghUrl;
    githubEl.classList.remove("hidden");
  } else {
    githubEl.classList.add("hidden");
  }
  const mUrl = mailtoUrl(buildTitle(), buildBody());
  if (mUrl) {
    emailEl.href = mUrl;
    emailEl.classList.remove("hidden");
  } else {
    emailEl.classList.add("hidden");
  }
}

// -- контекстный блок (привязан к последнему переводу) --
const feedbackComment = document.getElementById("feedback-comment");
const feedbackCopyBtn = document.getElementById("feedback-copy");
const feedbackGithubLink = document.getElementById("feedback-github");
const feedbackEmailLink = document.getElementById("feedback-email");
const feedbackCopiedNote = document.getElementById("feedback-copied-note");

function updateFeedbackLinks() {
  const comment = feedbackComment ? feedbackComment.value : "";
  wireFeedbackLinkPair(
    feedbackGithubLink,
    feedbackEmailLink,
    () => "Замечание к переводу: " + (lastResult ? lastResult.inputText : ""),
    () => buildReportText(comment)
  );
}

if (feedbackCopyBtn) {
  feedbackCopyBtn.addEventListener("click", () => {
    copyReport(buildReportText(feedbackComment ? feedbackComment.value : ""), feedbackCopiedNote);
  });
}
if (feedbackComment) {
  feedbackComment.addEventListener("input", updateFeedbackLinks);
}

// -- общая форма в подвале (не привязана к конкретному переводу) --
const feedbackGeneralCopyBtn = document.getElementById("feedback-general-copy");
const feedbackGeneralGithubLink = document.getElementById("feedback-general-github");
const feedbackGeneralEmailLink = document.getElementById("feedback-general-email");
const feedbackGeneralCopiedNote = document.getElementById("feedback-general-copied-note");

function generalReportText() {
  return "Отзыв о переводчике Prūsiska bilā\nСтраница: " + location.href + "\n\nПожелание/замечание: ";
}

wireFeedbackLinkPair(
  feedbackGeneralGithubLink,
  feedbackGeneralEmailLink,
  () => "Отзыв о переводчике",
  generalReportText
);

if (feedbackGeneralCopyBtn) {
  feedbackGeneralCopyBtn.addEventListener("click", () => {
    copyReport(generalReportText(), feedbackGeneralCopiedNote);
  });
}

translateBtn.addEventListener("click", doTranslate);
input.addEventListener("keydown", (e) => {
  if ((e.key === "Enter") && (e.ctrlKey || e.metaKey)) {
    e.preventDefault();
    doTranslate();
  }
});

boot();
