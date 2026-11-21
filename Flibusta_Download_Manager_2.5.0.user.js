// ==UserScript==
// @name         Flibusta Download Manager 2.5.7
// @namespace    http://tampermonkey.net/
// @version      2.5.7
// @description  Batch books with original server filenames by default; optional readable names, remembered folder, retry and resume.
// @author       Flibusta multidownload contributors; revised edition
// @license      GPL-3.0-or-later
// @match        https://flibusta.is/*
// @match        http://flibustaongezhld6dibs2dps6vm4nvqg2kp7vgowbu76tzopgnhazqd.onion/*
// @match        http://zmw2cyw2vj7f6obx3msmdvdepdhnw2ctc4okza2zjxlukkdfckhq.b32.i2p/*
// @grant        GM_download
// @grant        GM_xmlhttpRequest
// @grant        GM_getValue
// @grant        GM_setValue
// @grant        GM_notification
// @connect      *
// @connect      self
// @connect      flibusta.is
// @connect      flibustaongezhld6dibs2dps6vm4nvqg2kp7vgowbu76tzopgnhazqd.onion
// @connect      zmw2cyw2vj7f6obx3msmdvdepdhnw2ctc4okza2zjxlukkdfckhq.b32.i2p
// @run-at       document-idle
// @noframes
// ==/UserScript==

/*
 * GPL-3.0-or-later. This script replaces the queue and parser in the
 * original Flibusta multidownload userscript (LRN, InvisibleOwl).
 *
 * Security model: no external dependencies or telemetry; only pages matched
 * above; all remote text is shown via textContent, never via innerHTML.
 * Image src comes only from parseBookInfo (same-site address).
 * A saved queue stores book URLs/titles locally in Tampermonkey storage.
 *
 * Downloads may redirect from a Flibusta page URL to a separate file
 * host. Tampermonkey may request permission for that host (@connect *).
 * Original filename mode reads Content-Disposition / final download URL.
 * If neither supplies a safe book filename, a readable fallback is used.
 * In direct readable-name mode GM_download cannot verify the body; enable Verify
 * file content for that guarantee.
 * Queues are scoped to one page URL. A stopped active download is allowed
 * to finish, avoiding ambiguous disk writes. Do not run the same page's
 * queue from multiple tabs concurrently when Web Locks is unavailable.
 */

(() => {
  'use strict';

  const VERSION = '2.5.7';
  const SETTINGS_KEY = 'fdm2:settings';
  const COLLAPSED_KEY = 'fdm2:collapsed';
  const FOLDER_DB = 'FlibustaDownloadManager';
  const FOLDER_STORE = 'preferences';
  const MAX_PAGES = 30;
  const MAX_BOOKS = 10000;
  const DEFAULTS = Object.freeze({
    format: 'fb2',
    naming: 'original',
    fallback: true,
    verify: true,
    parallel: 1,
    delay: 1200,
    retries: 3,
    idle: 20, // секунд без данных до обрыва и повтора
    allPages: false,
    askEach: false,
    skipDownloaded: true
  });
  const FORMATS = ['fb2', 'epub', 'mobi', 'azw3', 'pdf', 'djvu', 'txt', 'rtf', 'html', 'doc', 'docx', 'other'];
  const BOOK_PATH = /^\/b\/(\d+)\/?$/i;
  // «Выбрать всё» на сайте — не всегда label: подпись может быть соседним текстом.
  const SELECT_ALL = /выбрать\s*вс[её]|отметить\s*вс[её]|select\s*all|check\s*all|checkall|selectall|sel_all/i;
  const BOOK_RESOURCE = /^\/b\/(\d+)\/([^/?#]+)\/?$/i;
  const SERIES_PATH = /^\/(?:s|sequence)\/\d+\/?$/i;
  const GENRE_PATH = /^\/g\/\d+\/?$/i;
  const ZIP_MAGIC = [0x50, 0x4b, 0x03, 0x04];
  const STATUS_CODES = { queued: 'q', active: 'a', done: 'd', failed: 'f', skipped: 's' };
  const STATUS_NAMES = { q: 'queued', a: 'active', d: 'done', f: 'failed', s: 'skipped' };
  const SAFE_EXTENSION = /^(?:fb2\.zip|fb2|epub|mobi|azw3|pdf|djvu|txt|rtf|html|doc|docx)$/;
  const HISTORY_PREFIX = 'fdm2:history:';
  const HISTORY_BUCKET = 10000;
  const IDLE_TIMEOUT = 60000; // верхняя граница; рабочее значение — настройка «Обрыв без данных»
  const IDLE_CHOICES = [15, 20, 30, 60];
  const LIST_CACHE_PREFIX = 'fdm2:list:';
  const LIST_CACHE_INDEX = 'fdm2:list-index';
  const LIST_CACHE_MS = 86400000; // раскрытые списки автора/серии живут сутки
  const LIST_CACHE_MAX = 40;
  const BOOK_CACHE_PREFIX = 'fdm2:book:';
  const BOOK_CACHE_INDEX = 'fdm2:book-index';
  const BOOK_CACHE_MAX = 200;
  const SUB_LIMIT = 50; // столько книг раскрытого списка показывается сразу
  const REDIRECT_OFF_KEY = 'fdm2:manual-redirect-off';
  const REDIRECT_RETRY_MS = 7 * 86400000; // через неделю ручной режим пробуется снова
  const SAVE_IDLE_TIMEOUT = 120000;
  const MAX_RATE_HITS = 20; // накопительный счётчик 429/503 на одну книгу, не «подряд»
  const STATE_CHUNK = 200; // заданий в одном блоке статусов очереди
  const HISTORY_FLUSH_MS = 2000;
  const CATALOG_RETRIES = 3;
  const CATALOG_RETRY_MS = 1000;
  const CATALOG_MAX_WAIT_MS = 60000;
  const MAX_REDIRECTS = 5;

  const locationURL = new URL(location.href);
  const isAuthor = /^\/a\/\d+\/?$/i.test(locationURL.pathname);
  const isSeries = SERIES_PATH.test(locationURL.pathname);
  // Страница одной книги: /b/<id>. Панель скачивает именно её одной кнопкой.
  const isBook = /^\/b\/\d+\/?$/i.test(locationURL.pathname);
  // Рейтинги: «Топ дня», «Топ недели», «Популярные книги» (список «автор - книга») и «Оценённые книги» (таблица).
  const isStat = /^\/stat\/(?:24|w|b|r(?:\/(?:av|g|b))?)\/?$/i.test(locationURL.pathname);
  if (!isAuthor && !isSeries && !isBook && !isStat) return;

  if (document.getElementById('fdm-panel')) return;
  const main = document.querySelector('div#main') || document.querySelector('main') || document.body;
  const title = main.querySelector('h1') || main.querySelector('h2');
  const initialForm = isBook || isStat ? null : getBookForm(main, isAuthor);
  const statRows = isStat ? decorateStatRows() : [];

  const PAGE_KEY = 'fdm2:job:' + locationURL.origin + locationURL.pathname + locationURL.search;
  const FOLDER_INFO_KEY = 'fdm2:folder:' + locationURL.origin;
  const folderInfo = readStored(FOLDER_INFO_KEY, { selected: false, name: '' });
  let settings = readStored(SETTINGS_KEY, DEFAULTS);
  settings = sanitizeSettings(settings);
  const JOBS_KEY = PAGE_KEY + ':jobs';
  let state = loadState();
  if (!validStoredState(state)) state = null;
  if (state) {
    state.options = sanitizeSettings(state.options);
    state.cancelled = !!state.cancelled;
    state.version = VERSION;
    for (const job of state.jobs) {
      if (job.status === 'active') job.status = 'queued';
      // Storage is local but untrusted: never reuse a stored path as a filename.
      if (!SAFE_EXTENSION.test(job.extension)) job.extension = job.format === 'fb2' ? 'fb2.zip' : job.format;
      job.name = safeOriginalName(job.name) || (cleanFilePart(job.title, 125) + '.' + job.extension);
    }
    state.paused = true; // explicit resume after browser restart
  }

  const runtime = {
    active: 0,
    countsCache: null,
    queueLockRelease: null,
    queueLockPending: null,
    folderWriteTail: Promise.resolve(),
    cooldownUntil: state && Number.isFinite(state.cooldownUntil)
      ? Math.min(state.cooldownUntil, Date.now() + 86400000) : 0,
    jobsDirty: !!state && !state.splitStorage,
    // Блоки статусов: подпись последней записи и номера когда-либо записанных блоков.
    chunkSigs: new Map(),
    writtenChunks: new Set(Array.isArray(state?.chunks) ? state.chunks : []),
    // Подсказка persist(job): блоки известны только после полного прохода по этому списку заданий.
    syncedJobs: null,
    jobIndex: new Map(),
    history: new Map(),
    historyDirty: new Set(),
    historyTimer: null,
    prepareNotes: [],
    notesSignature: '',
    catalogProgress: null,
    cooldownTick: null,
    prepareController: null,
    errorSignature: '',
    timer: null,
    lastStart: 0,
    preparing: false,
    message: '',
    progress: new Map(),
    lastProgressRender: 0,
    folder: null,
    folderExpected: !!folderInfo?.selected,
    folderName: typeof folderInfo?.name === 'string' ? folderInfo.name : '',
    folderPermission: 'unknown',
    folderRestoring: !!folderInfo?.selected,
    folderRevision: 0,
    lastRemoteHost: '',
    nativeMaster: null,
    bookBoxes: [],
    onlyRecord: null, // книга, которую качает кнопка «⬇» в строке рейтинга или раскрытом списке
    bookInfoCache: new Map(), // id -> промис BookInfo: повторы и параллельные клики не бьют по хранилищу и сети
    selectedMode: isBook ? 'all' : 'checked',
    bookCount: 0,
    doneTimes: [] // моменты завершения последних книг — для оценки «осталось»
  };
  let ui;
  window.addEventListener?.('pagehide', () => flushHistory());
  renderInterface();
  runtime.bookBoxes = checkboxEntries();
  runtime.bookCount = pageBooks().length;
  showDoneMarks();
  attachNativeSelectAll();
  attachBookSelectionListener();
  render();
  restoreFolder();

  function getBookForm(root, author) {
    if (!root) return null;
    const forms = [...root.querySelectorAll('form')];
    if (author) forms.sort((a, b) => Number(/post/i.test(b.method)) - Number(/post/i.test(a.method)));
    const containsBook = node => [...node.querySelectorAll('a[href]')].some(a => {
      try { return BOOK_PATH.test(new URL(a.getAttribute('href'), location.href).pathname); }
      catch (_) { return false; }
    });
    return forms.find(containsBook) || (containsBook(root) ? root : null);
  }

  function readStored(key, fallback) {
    try { return GM_getValue(key, fallback); }
    catch (error) { console.warn('[FDM2] Cannot read storage:', error); return fallback; }
  }

  // Queue storage is split: the job list is written once per queue (JOBS_KEY);
  // statuses live in blocks of STATE_CHUNK jobs (JOBS_KEY:s:n), and only blocks
  // whose content changed are rewritten. One event then writes a header plus
  // one block, however many books are already finished.
  // persist(job...) — подсказка «изменились только эти задания»: сканируется их блок.
  // Без аргумента, до первого полного прохода или при любом сомнении — полный проход.
  function persist(...changed) {
    runtime.countsCache = null;
    try {
      let only = null;
      if (changed.length && !runtime.jobsDirty && runtime.syncedJobs === state.jobs) {
        only = new Set();
        for (const job of changed) {
          const i = runtime.jobIndex.get(job);
          if (i === undefined || state.jobs[i] !== job) { only = null; break; }
          only.add(Math.floor(i / STATE_CHUNK));
        }
      }
      if (!only) {
        runtime.jobIndex = new Map(state.jobs.map((job, i) => [job, i]));
        runtime.syncedJobs = state.jobs;
      }
      if (runtime.jobsDirty) {
        GM_setValue(JOBS_KEY, state.jobs.map(({ id, title, url, name, format, extension }) =>
          ({ id, title, url, name, format, extension })));
        runtime.jobsDirty = false;
      }
      for (let chunk = 0; chunk * STATE_CHUNK < state.jobs.length; chunk++) {
        if (only && !only.has(chunk)) continue;
        const delta = {};
        const end = Math.min(state.jobs.length, (chunk + 1) * STATE_CHUNK);
        for (let i = chunk * STATE_CHUNK; i < end; i++) {
          const job = state.jobs[i];
          if (job.status === 'queued' && !job.attempts && !job.rateHits && !job.error && (job.nameSource || 'pending') === 'pending') continue;
          delta[job.id] = [STATUS_CODES[job.status], job.attempts, job.nextTryAt || 0, job.rateHits || 0,
            job.name, job.nameSource || 'pending', job.error || ''];
        }
        const signature = JSON.stringify(delta);
        if (signature === runtime.chunkSigs.get(chunk) || (signature === '{}' && !runtime.writtenChunks.has(chunk))) continue;
        GM_setValue(JOBS_KEY + ':s:' + chunk, delta);
        runtime.chunkSigs.set(chunk, signature);
        runtime.writtenChunks.add(chunk);
      }
      GM_setValue(PAGE_KEY, {
        version: VERSION, key: PAGE_KEY, splitStorage: true, createdAt: state.createdAt,
        paused: state.paused, cancelled: state.cancelled, options: state.options,
        skippedByFormat: state.skippedByFormat || 0, skippedByHistory: state.skippedByHistory || 0,
        cooldownUntil: runtime.cooldownUntil || 0, count: state.jobs.length,
        chunks: [...runtime.writtenChunks].sort((a, b) => a - b)
      });
    }
    catch (error) { console.error('[FDM2] Cannot save queue:', error); setMessage('Не удалось сохранить очередь: ' + error.message); }
  }

  // Новая очередь вытесняет старую: её блоки статусов иначе остались бы в хранилище навсегда
  // (GM_deleteValue не выдан, поэтому затираем null).
  function dropStatusBlocks() {
    for (const chunk of runtime.writtenChunks) {
      try { GM_setValue(JOBS_KEY + ':s:' + chunk, null); }
      catch (error) { console.warn('[FDM2] Cannot drop old block:', error); }
    }
    runtime.chunkSigs.clear();
    runtime.writtenChunks.clear();
  }

  // Accepts the block format of 2.5, the earlier 2.5 header with an inline
  // delta, and the full-state format of 2.0–2.4.x. Never writes.
  // A block the header declares but storage lacks makes the queue unreadable.
  function loadState() {
    const raw = readStored(PAGE_KEY, null);
    if (!raw || typeof raw !== 'object' || !raw.splitStorage) return raw;
    const list = readStored(JOBS_KEY, null);
    if (!Array.isArray(list) || list.length !== raw.count) return null;
    const delta = raw.delta && typeof raw.delta === 'object' ? { ...raw.delta } : {};
    if (raw.chunks !== undefined) {
      const limit = Math.ceil(list.length / STATE_CHUNK);
      if (!Array.isArray(raw.chunks) || !raw.chunks.every(c => Number.isInteger(c) && c >= 0 && c < limit)) return null;
      for (const chunk of raw.chunks) {
        const block = readStored(JOBS_KEY + ':s:' + chunk, null);
        if (!block || typeof block !== 'object' || Array.isArray(block)) return null;
        Object.assign(delta, block);
      }
    }
    const jobs = list.map(base => {
      const job = { ...base, status: 'queued', attempts: 0, nextTryAt: 0, rateHits: 0, nameSource: 'pending', error: '' };
      const d = base && Object.prototype.hasOwnProperty.call(delta, base.id) ? delta[base.id] : null;
      if (Array.isArray(d)) {
        job.status = STATUS_NAMES[d[0]] || 'invalid';
        job.attempts = d[1]; job.nextTryAt = d[2]; job.rateHits = d[3];
        if (typeof d[4] === 'string') job.name = d[4];
        job.nameSource = typeof d[5] === 'string' ? d[5] : 'pending';
        job.error = typeof d[6] === 'string' ? d[6] : '';
      }
      return job;
    });
    return { ...raw, jobs };
  }

  // Download history: "id:format" entries in buckets of 10 000 IDs, so a
  // finished book rewrites one small bucket instead of the whole history.
  function historyKey(id) { return HISTORY_PREFIX + Math.floor(Number(id) / HISTORY_BUCKET); }

  function historyBucket(key, fresh = false) {
    if (!fresh && runtime.history.has(key)) return runtime.history.get(key);
    const raw = readStored(key, '');
    const set = new Set(typeof raw === 'string' && raw ? raw.split(',') : []);
    runtime.history.set(key, set);
    return set;
  }

  function isDownloaded(id, format) { return historyBucket(historyKey(id)).has(id + ':' + format); }

  function wasDownloaded(id) { return FORMATS.some(format => isDownloaded(id, format)); }

  /** Отметка «✓» у скачанных ранее книг. Только класс: текст ссылок и заголовка не меняется, его читают парсеры и имена файлов. */
  function showDoneMarks() {
    if (isBook) { title?.classList.toggle('fdm-done', wasDownloaded(locationURL.pathname.match(/\d+/)[0])); return; }
    for (const link of main.querySelectorAll('a[href]')) {
      if (link.closest('#fdm-panel')) continue;
      const id = bookIdentity(link, location.href);
      if (!id) continue;
      const done = wasDownloaded(id);
      link.classList.toggle('fdm-done', done);
      if (done && !link.title) link.title = 'Уже скачано';
      else if (!done && link.title === 'Уже скачано') link.removeAttribute('title');
    }
  }

  // Writes are batched: the in-memory set is the truth (isDownloaded sees
  // unflushed entries); flushHistory() persists it on a timer, pause, stop,
  // end of queue and pagehide.
  function markDownloaded(job) {
    const key = historyKey(job.id);
    const set = historyBucket(key, !runtime.historyDirty.has(key)); // re-read once per batch: another tab may have added entries
    const entry = job.id + ':' + job.format;
    if (set.has(entry)) return;
    set.add(entry);
    runtime.historyDirty.add(key);
    if (!runtime.historyTimer) {
      runtime.historyTimer = setTimeout(flushHistory, HISTORY_FLUSH_MS);
      runtime.historyTimer.unref?.();
    }
  }

  function flushHistory() {
    clearTimeout(runtime.historyTimer);
    runtime.historyTimer = null;
    for (const key of runtime.historyDirty) {
      const set = runtime.history.get(key);
      if (!set) { runtime.historyDirty.delete(key); continue; }
      try {
        const stored = readStored(key, ''); // keep entries another tab wrote meanwhile
        if (typeof stored === 'string' && stored) for (const entry of stored.split(',')) set.add(entry);
        GM_setValue(key, [...set].join(','));
        runtime.historyDirty.delete(key);
      } catch (error) { console.warn('[FDM2] Cannot save history:', error); }
    }
    // Неудачная запись остаётся в historyDirty; без таймера её повторит только следующий вызов.
    if (runtime.historyDirty.size > 0 && !runtime.historyTimer) {
      runtime.historyTimer = setTimeout(flushHistory, HISTORY_FLUSH_MS * 5);
      runtime.historyTimer.unref?.();
    }
  }

  function clearHistory() {
    if (queueBusy()) { setMessage('Поставьте загрузку на паузу перед очисткой истории.'); return; }
    if (!window.confirm('Забыть все ранее скачанные книги? Файлы на диске не удаляются.')) return;
    // GM_listValues is not granted; IDs above 10^7 are not expected on the site.
    for (let bucket = 0; bucket < 1000; bucket++) {
      const key = HISTORY_PREFIX + bucket;
      if (readStored(key, '')) { try { GM_setValue(key, ''); } catch (_) {} }
    }
    runtime.history.clear();
    runtime.historyDirty.clear();
    clearTimeout(runtime.historyTimer);
    runtime.historyTimer = null;
    showDoneMarks();
    setMessage('История скачанного очищена.');
  }

  function saveSettings() {
    settings = sanitizeSettings({
      format: ui.format.value,
      naming: ui.naming.value,
      fallback: ui.fallback.checked,
      verify: ui.verify.checked,
      parallel: Number(ui.parallel.value),
      delay: Number(ui.delay.value),
      retries: Number(ui.retries.value),
      idle: Number(ui.idle.value),
      allPages: ui.allPages.checked,
      askEach: ui.askEach.checked,
      skipDownloaded: ui.skipDownloaded.checked
    });
    try { GM_setValue(SETTINGS_KEY, settings); }
    catch (error) { console.warn('[FDM2] Cannot save settings:', error); }
    render();
  }

  function sanitizeSettings(raw) {
    const value = { ...DEFAULTS, ...(raw && typeof raw === 'object' ? raw : {}) };
    return {
      format: FORMATS.includes(value.format) ? value.format : DEFAULTS.format,
      naming: value.naming === 'readable' ? 'readable' : 'original',
      fallback: !!value.fallback,
      verify: !!value.verify,
      parallel: Math.min(2, Math.max(1, Number(value.parallel) || 1)),
      delay: Math.min(30000, Math.max(1000, Number(value.delay) || DEFAULTS.delay)),
      retries: Math.min(5, Math.max(0, Number(value.retries) || 0)),
      idle: IDLE_CHOICES.includes(Number(value.idle)) ? Number(value.idle) : DEFAULTS.idle,
      allPages: !!value.allPages,
      askEach: !!value.askEach,
      skipDownloaded: !!value.skipDownloaded
    };
  }

  function validStoredState(value) {
    return value && ['2.0.0', '2.1.0', '2.2.0', '2.3.0', '2.4.0', '2.4.1', '2.4.2', '2.5.0', '2.5.1', '2.5.2', '2.5.3', '2.5.4', '2.5.5', '2.5.6', VERSION].includes(value.version) && value.key === PAGE_KEY &&
      Array.isArray(value.jobs) && value.jobs.length <= MAX_BOOKS &&
      value.jobs.every(job => job && ['queued', 'active', 'done', 'failed', 'skipped'].includes(job.status) &&
        typeof job.url === 'string' && !!sameSiteURL(job.url) &&
        typeof job.name === 'string' && typeof job.id === 'string' &&
        Number.isInteger(job.attempts) && job.attempts >= 0 && job.attempts <= 100 &&
        (job.rateHits === undefined || (Number.isInteger(job.rateHits) && job.rateHits >= 0 && job.rateHits <= 100)) &&
        (job.nextTryAt === undefined || Number.isFinite(job.nextTryAt)) &&
        FORMATS.includes(job.format) && typeof job.extension === 'string');
  }

  function sameSiteURL(value, base = location.href) {
    try {
      const url = new URL(value, base);
      return url.origin === location.origin && /^https?:$/.test(url.protocol) ? url : null;
    } catch (_) { return null; }
  }

  function getTokens(form) {
    const tokens = [];
    const walker = document.createTreeWalker(form, NodeFilter.SHOW_ELEMENT);
    let node;
    while ((node = walker.nextNode())) {
      const tag = node.tagName;
      if ((tag === 'A' || tag === 'INPUT' || tag === 'BR') && !node.closest('#fdm-panel')) tokens.push(node);
    }
    return tokens;
  }

  function bookIdentity(link, base) {
    const url = sameSiteURL(link.getAttribute('href'), base);
    if (!url) return null;
    const match = url.pathname.match(BOOK_PATH);
    return match ? match[1] : null;
  }

  function getSeriesNumber(bookAnchor, checkbox, tokens, start, bookIndex) {
    // Read text between the nearest checkbox and the title, or fallback to
    // adjacent text nodes. No document/book ID is used as a series number.
    const preceding = checkbox || tokens[Math.max(start, bookIndex - 1)];
    if (preceding && preceding.parentNode && bookAnchor.parentNode === preceding.parentNode) {
      let text = '';
      let node = preceding.nextSibling;
      while (node && node !== bookAnchor && text.length < 70) {
        text += node.textContent || '';
        node = node.nextSibling;
      }
      const match = text.match(/(?:^|[\s–—-])(?:№\s*|#\s*)?(\d{1,4})\s*[.):\-–—]?\s*$/);
      if (match) return Number(match[1]);
    }
    const prevText = bookAnchor.previousSibling?.nodeType === 3 ? bookAnchor.previousSibling.textContent : '';
    const match = prevText.match(/(?:^|[\s–—-])(?:№\s*|#\s*)?(\d{1,4})\s*[.):\-–—]?\s*$/);
    return match ? Number(match[1]) : null;
  }

  function normalizeFormat(text, pathSegment) {
    const label = String(text || '').trim().toLowerCase();
    const path = String(pathSegment || '').trim().toLowerCase();
    if (path === 'read' || label === 'читать') return null;
    const explicit = label.match(/\((?:скачать\s+)?(fb2(?:\.zip)?|epub|mobi|azw3|pdf|djvu|txt|rtf|html|docx?|zip)\)/i);
    let format = explicit ? explicit[1] : '';
    if (!format && label.match(/\(скачать\)/i)) format = 'fb2.zip';
    if (!format && /^(?:fb2|epub|mobi|azw3|pdf|djvu|txt|rtf|html|docx?|zip)$/.test(path)) format = path;
    if (!format && path === 'download') format = 'fb2.zip';
    if (format === 'zip' || format === 'fb2.zip') return { format: 'fb2', extension: 'fb2.zip' };
    if (FORMATS.includes(format) && format !== 'other') {
      return { format, extension: format === 'fb2' ? 'fb2.zip' : format };
    }
    return null;
  }

  function extractBooks(form, baseURL = location.href) {
    const tokens = getTokens(form);
    const records = [];
    let series = '';
    let lineStart = 0;
    let priorBookEnd = 0;
    for (let i = 0; i < tokens.length; i++) {
      const token = tokens[i];
      if (token.tagName === 'BR') { lineStart = i + 1; continue; }
      if (token.tagName !== 'A') continue;
      const linkedURL = sameSiteURL(token.getAttribute('href'), baseURL);
      if (!linkedURL) continue;
      if (SERIES_PATH.test(linkedURL.pathname)) { series = token.textContent.trim(); continue; }
      if (GENRE_PATH.test(linkedURL.pathname)) { series = ''; continue; }
      const id = bookIdentity(token, baseURL);
      if (!id) continue;
      const begin = Math.max(lineStart, priorBookEnd);
      let checkbox = null;
      for (let k = begin; k < i; k++) {
        if (tokens[k].tagName === 'INPUT' && tokens[k].type === 'checkbox') checkbox = tokens[k];
      }
      const formats = [];
      let end = i + 1;
      for (; end < tokens.length; end++) {
        const item = tokens[end];
        if (item.tagName === 'BR') break;
        if (item.tagName !== 'A') continue;
        if (bookIdentity(item, baseURL)) break;
        const url = sameSiteURL(item.getAttribute('href'), baseURL);
        if (!url) continue;
        const match = url.pathname.match(BOOK_RESOURCE);
        if (!match || match[1] !== id) continue;
        const matchFormat = normalizeFormat(item.textContent, match[2]);
        if (!matchFormat) continue;
        formats.push({ ...matchFormat, url: url.href });
      }
      // Links do not necessarily have a BR delimiter in redesigned layouts.
      // The nearest checkbox before each title defines 'checked' even then.
      const titleText = token.textContent.replace(/\s+/g, ' ').trim();
      if (titleText) records.push({
        id, title: titleText, series, number: getSeriesNumber(token, checkbox, tokens, begin, i),
        checked: !!checkbox?.checked, checkboxElement: checkbox, formats
      });
      priorBookEnd = i + 1;
      // The outer loop intentionally continues through format links, where
      // non-book anchors are ignored, and stops normally at the next book.
    }
    return records;
  }

  // Книга со страницы /b/<id>: заголовок не ссылка, поэтому запись собирается из h1 и ссылок на форматы.
  function singleBook() {
    const id = locationURL.pathname.match(/\d+/)[0];
    const heading = (title?.textContent || document.title || '').replace(/\s+/g, ' ').trim();
    const name = heading.replace(/\s*\((?:fb2|epub|mobi|azw3|pdf|djvu|txt|rtf|html|docx?)\)\s*$/i, '').replace(/\s*\|\s*Флибуста\s*$/i, '');
    const formats = [];
    for (const link of main.querySelectorAll('a[href]')) {
      const url = sameSiteURL(link.getAttribute('href'), location.href);
      const match = url?.pathname.match(BOOK_RESOURCE);
      if (!match || match[1] !== id) continue;
      const found = normalizeFormat(link.textContent, match[2]);
      if (found && !formats.some(f => f.format === found.format)) formats.push({ ...found, url: url.href });
    }
    return { id, title: name || 'Книга ' + id, series: '', number: null, checked: true, checkboxElement: null, formats };
  }

  /** Строка рейтинга: флажок, «⬇» (скачать сразу), «+ автор» и «+ серия» (раскрыть их книги под строкой). */
  function decorateStatRows() {
    const rows = [];
    const style = document.createElement('style');
    style.textContent = '.fdm-row-tools{margin-left:10px;white-space:nowrap}.fdm-row-btn{margin-left:4px;padding:0 7px;border:1px solid #cfd9d5;' +
      'border-radius:6px;background:#f5f8f6;color:#196b59;font:12px/20px sans-serif;cursor:pointer}.fdm-row-btn:hover{background:#e9f4ef}' +
      '.fdm-row-btn:disabled{color:#617370;cursor:default}.fdm-sub{margin:4px 0 8px 24px;padding:0;list-style:none}' +
      '.fdm-sub li{margin:2px 0}.fdm-sub-note{color:#617370;font-size:12px;margin-left:4px}' +
      '.fdm-info{margin:4px 0 8px 24px;font-size:13px}.fdm-info::after{content:"";display:block;clear:both}' +
      '.fdm-info p{margin:4px 0}.fdm-info-cover{float:left;max-width:140px;max-height:200px;margin:0 10px 4px 0}' +
      '.fdm-info-meta{color:#617370;font-size:12px}.fdm-reviews{margin-top:6px;border-top:1px solid #cfd9d5}.fdm-review{margin:6px 0}';
    document.head.append(style);
    // Строка списка — <li>, строка таблицы «Оценённых» — первая ячейка <tr>.
    for (const row of main.querySelectorAll('li, tr')) {
      const cell = row.tagName === 'TR' ? row.querySelector(':scope > td') : row;
      if (!cell || cell.querySelector('.fdm-row-tools')) continue;
      const links = [...cell.querySelectorAll(':scope > a[href]')].map(a => ({ a, url: sameSiteURL(a.getAttribute('href'), location.href) }));
      const bookLink = links.find(l => l.url && /^\/b\/\d+\/?$/.test(l.url.pathname));
      if (!bookLink) continue;
      const id = bookLink.url.pathname.match(/\d+/)[0];
      // В таблице серия уже написана в строке; в списке её придётся запросить у страницы книги.
      const known = row.tagName === 'TR'
        ? (cell.querySelector('a[href]') && [...cell.querySelectorAll('a[href]')].map(a => sameSiteURL(a.getAttribute('href'), location.href))
          .find(url => url && SERIES_PATH.test(url.pathname))?.href) || null
        : undefined;
      const box = document.createElement('input');
      box.type = 'checkbox';
      const tools = element('span', 'fdm-row-tools');
      const get = element('button', 'fdm-row-btn', '⬇');
      get.type = 'button';
      get.title = 'Скачать эту книгу одним кликом';
      // Автор: в списке — первая ссылка /a/, в таблице — последняя (раньше идут переводчики).
      const authors = links.filter(l => l.url && /^\/a\/\d+\/?$/.test(l.url.pathname));
      const author = (row.tagName === 'TR' ? authors[authors.length - 1] : authors[0])?.url.href || null;
      const ctx = { id, author, known, open: null, sub: element('ul', 'fdm-sub'), subRows: [], buttons: {} };
      ctx.sub.hidden = true;
      ctx.sub.addEventListener('change', () => syncSubAll(ctx));
      const row0 = { id, title: bookLink.a.textContent.replace(/\s+/g, ' ').trim(), box };
      get.addEventListener('click', event => { event.preventDefault(); downloadOne(statRecord(row0)); });
      tools.append(get);
      for (const [kind, label, hint] of [['author', 'автор', 'Показать все книги автора'], ['series', 'серия', 'Показать все книги серии']]) {
        if (kind === 'author' && !author) continue;
        const btn = element('button', 'fdm-row-btn', '+ ' + label);
        btn.type = 'button';
        btn.title = hint;
        btn.addEventListener('click', event => { event.preventDefault(); toggleList(ctx, kind, btn); });
        ctx.buttons[kind] = btn;
        tools.append(btn);
      }
      tools.append(addInfoToggle(id, cell, ctx.sub));
      cell.prepend(box, ' ');
      cell.append(tools, ctx.sub);
      rows.push(row0);
    }
    return rows;
  }

  // В рейтинге нет ссылок на форматы, но адрес файла предсказуем: /b/<id>/<формат>.
  function statRecord(row) {
    const formats = row.formats?.length ? row.formats : ['fb2', 'epub', 'mobi'].map(format => ({
      format, extension: format === 'fb2' ? 'fb2.zip' : format, url: `${locationURL.origin}/b/${row.id}/${format}`
    }));
    return { id: row.id, title: row.title, series: row.series || '', number: row.number ?? null,
      checked: !!row.box?.checked, checkboxElement: row.box || null, formats };
  }

  /** Кнопка «⬇»: очередь из одной книги, историю «уже скачано» игнорирует — клик явный. */
  async function downloadOne(record) {
    if (queueBusy() || runtime.preparing) { setMessage('Очередь занята: дождитесь окончания или нажмите «Пауза».'); return; }
    runtime.onlyRecord = record;
    try { await prepare('checked'); } finally { runtime.onlyRecord = null; }
  }

  /** Адрес страницы серии книги или null: берётся из сведений о книге (кэш общий с «+ описание»). */
  async function seriesURLFor(id) {
    return (await bookInfo(id)).series;
  }

  /**
   * @typedef {{ cover: string|null, annotation: string[], genres: string[], year: string, size: string,
   *   rating: string, series: string|null, reviews: { who: string, when: string, text: string[] }[] }} BookInfo
   */
  /** Сведения со страницы книги /b/<id>: только текст и адреса этого же сайта, разметка сайта не переносится. */
  function parseBookInfo(doc) {
    const root = doc.querySelector('#main') || doc.body;
    const clean = s => s.replace(/\s+/g, ' ').trim();
    // обложка и серия — только адреса этого же сайта
    const coverImg = [...root.querySelectorAll('img')].find(img => img.getAttribute('alt') === 'Cover image');
    const coverURL = coverImg ? sameSiteURL(coverImg.getAttribute('src') || '', location.href) : null;
    const seriesURL = [...root.querySelectorAll('a[href]')]
      .map(a => sameSiteURL(a.getAttribute('href') || '', location.href))
      .find(url => url && SERIES_PATH.test(url.pathname));
    // аннотация: абзацы после заголовка до ближайшего разделителя
    const heading = [...root.querySelectorAll('h2')].find(h => h.textContent.trim() === 'Аннотация');
    const annotation = [];
    for (let el = heading ? heading.nextElementSibling : null; el; el = el.nextElementSibling) {
      if (['HR', 'H2', 'FORM'].includes(el.tagName)) break;
      if (el.tagName === 'P' && el.textContent.trim()) annotation.push(el.textContent.trim());
    }
    const genres = [...root.querySelectorAll('a.genre')].map(a => a.textContent.trim()).filter(Boolean);
    const year = (root.textContent.match(/издание\s+(\d{4})\s*г/) || [])[1] || '';
    const size = root.querySelector('span[style="size"]')?.textContent.trim() || '';
    const ratingText = (root.querySelector('#newann') || root).textContent;
    const rating = clean((ratingText.match(/Оценки:\s*([^\n]+?)\s*$/m) || [])[1] || '');
    // отзывы: «who» — ник, «when» — дата и оценка, остальное — строки текста до <br>
    const reviews = [...root.querySelectorAll('span[class^="container_"]')].map(span => {
      const b = span.querySelector('b');
      const who = clean(span.querySelector('b > a')?.textContent || '');
      let node = b ? b.nextSibling : null;
      let when = '';
      for (; node && node.nodeName !== 'BR'; node = node.nextSibling) when += node.textContent;
      when = clean(when).replace(/^в\s+/, '');
      const text = [];
      let line = '';
      for (; node; node = node.nextSibling) {
        if (node.nodeName === 'BR') { line = clean(line); if (line) text.push(line); line = ''; }
        else line += node.textContent;
      }
      line = clean(line);
      if (line) text.push(line);
      return { who, when, text };
    });
    return {
      cover: coverURL ? coverURL.href : null,
      annotation,
      genres,
      year,
      size,
      rating,
      series: seriesURL ? seriesURL.href : null,
      reviews
    };
  }

  /** BookInfo страницы /b/<id>: память страницы, затем кэш GM на сутки, иначе запрос. */
  function bookInfo(id) {
    if (runtime.bookInfoCache.has(id)) return runtime.bookInfoCache.get(id);
    const promise = (async () => {
      const key = BOOK_CACHE_PREFIX + id;
      const cached = readStored(key, null);
      if (cached && Date.now() - cached.t < LIST_CACHE_MS && cached.info) return cached.info;
      const html = await httpGetText(new URL('/b/' + id, locationURL.origin).href);
      const info = parseBookInfo(new DOMParser().parseFromString(html, 'text/html'));
      try {
        const index = readStored(BOOK_CACHE_INDEX, []).filter(k => k !== key);
        index.push(key);
        while (index.length > BOOK_CACHE_MAX) GM_setValue(index.shift(), null);
        GM_setValue(key, { t: Date.now(), info });
        GM_setValue(BOOK_CACHE_INDEX, index);
      } catch (error) { console.warn('[FDM2] Cannot cache book:', error); }
      return info;
    })();
    runtime.bookInfoCache.set(id, promise);
    // ошибка не должна застревать в памяти — «ошибка, ещё раз» должна повторить запрос
    promise.catch(() => runtime.bookInfoCache.delete(id));
    return promise;
  }

  /** Кнопка «+ описание» и место под рамку: клик раскрывает/сворачивает обложку, аннотацию и отзывы книги. */
  function addInfoToggle(id, parent, before) {
    const btn = element('button', 'fdm-row-btn', '+ описание');
    btn.type = 'button';
    btn.title = 'Показать обложку и аннотацию';
    let box = null;
    btn.addEventListener('click', async event => {
      event.preventDefault();
      if (box && !box.hidden) { box.hidden = true; btn.textContent = '+ описание'; return; }
      if (box) { box.hidden = false; btn.textContent = '− описание'; return; }
      btn.disabled = true;
      btn.textContent = '…';
      try {
        box = renderInfo(await bookInfo(id));
        if (before) parent.insertBefore(box, before); else parent.append(box);
        btn.textContent = '− описание';
      } catch (error) {
        btn.textContent = 'ошибка, ещё раз';
        btn.title = 'Не удалось загрузить описание: ' + error.message;
      } finally {
        btn.disabled = false;
      }
    });
    return btn;
  }

  /** Рамка описания: только createElement/textContent; src картинки — из parseBookInfo. */
  function renderInfo(info) {
    const box = element('div', 'fdm-info');
    if (info.cover) {
      const img = element('img', 'fdm-info-cover');
      img.src = info.cover;
      img.alt = 'Обложка';
      img.loading = 'lazy';
      box.append(img);
    }
    const meta = [info.genres.join(', '), info.year && `издание ${info.year} г.`, info.size, info.rating && 'Оценки: ' + info.rating].filter(Boolean);
    if (meta.length) box.append(element('div', 'fdm-info-meta', meta.join(' · ')));
    if (info.annotation.length) for (const text of info.annotation) box.append(element('p', '', text));
    else box.append(element('p', 'fdm-sub-note', 'Аннотации нет.'));
    if (info.reviews.length) {
      const list = element('div', 'fdm-reviews');
      list.hidden = true;
      for (const review of info.reviews) {
        const item = element('div', 'fdm-review');
        item.append(element('b', '', review.who), ' ', element('span', 'fdm-sub-note', review.when));
        for (const line of review.text) item.append(element('p', '', line));
        list.append(item);
      }
      const toggle = element('button', 'fdm-row-btn', `Отзывы (${info.reviews.length})`);
      toggle.type = 'button';
      toggle.addEventListener('click', event => {
        event.preventDefault();
        list.hidden = !list.hidden;
        toggle.textContent = list.hidden ? `Отзывы (${info.reviews.length})` : 'Скрыть отзывы';
      });
      box.append(toggle, list);
    }
    return box;
  }

  /** Книги страницы автора или серии: из кэша на сутки, иначе запрос с повторами. Формат записи — как у extractBooks. */
  async function listBooks(url, author) {
    const key = LIST_CACHE_PREFIX + url;
    const cached = readStored(key, null);
    if (cached && Date.now() - cached.t < LIST_CACHE_MS && Array.isArray(cached.books)) return cached.books;
    const doc = new DOMParser().parseFromString(await httpGetText(url), 'text/html');
    const root = doc.querySelector('div#main') || doc.querySelector('main') || doc.body;
    const form = getBookForm(root, author);
    const books = form ? extractBooks(form, url).map(({ id, title, series, number, formats }) => ({ id, title, series, number, formats })) : [];
    try {
      const index = readStored(LIST_CACHE_INDEX, []).filter(k => k !== key);
      index.push(key);
      while (index.length > LIST_CACHE_MAX) GM_setValue(index.shift(), null);
      GM_setValue(key, { t: Date.now(), books });
      GM_setValue(LIST_CACHE_INDEX, index);
    } catch (error) { console.warn('[FDM2] Cannot cache list:', error); }
    return books;
  }

  /** «+ автор» / «+ серия»: раскрыть список под строкой рейтинга, повторный клик сворачивает. */
  async function toggleList(ctx, kind, btn) {
    const label = kind === 'author' ? 'автор' : 'серия';
    if (ctx.open === kind) {
      ctx.sub.hidden = true;
      ctx.open = null;
      btn.textContent = '+ ' + label;
      return;
    }
    btn.disabled = true;
    btn.textContent = '…';
    let keepDisabled = false;
    try {
      const url = kind === 'author' ? ctx.author : ctx.known !== undefined ? ctx.known : await seriesURLFor(ctx.id);
      if (!url) { btn.textContent = 'нет серии'; keepDisabled = true; return; }
      const books = await listBooks(url, kind === 'author');
      renderSubList(ctx, books);
      for (const [other, b] of Object.entries(ctx.buttons)) {
        if (b.textContent.startsWith('−')) b.textContent = '+ ' + (other === 'author' ? 'автор' : 'серия');
      }
      ctx.open = kind;
      ctx.sub.hidden = false;
      btn.textContent = '− ' + label;
    } catch (error) {
      btn.textContent = 'ошибка, ещё раз';
      btn.title = 'Не удалось загрузить список: ' + error.message;
    } finally {
      btn.disabled = keepDisabled;
    }
  }

  function renderSubList(ctx, books) {
    // Прежние строки этого раскрытия уходят из списка отметок.
    for (const row of ctx.subRows) statRows.splice(statRows.indexOf(row), 1);
    ctx.subRows = [];
    ctx.sub.replaceChildren();
    if (!books.length) ctx.sub.append(element('li', 'fdm-sub-note', 'Книги не найдены.'));
    const allItem = element('li');
    ctx.allBtn = element('button', 'fdm-row-btn fdm-sub-all', 'отметить все');
    ctx.allBtn.type = 'button';
    ctx.allBtn.addEventListener('click', event => {
      event.preventDefault();
      const on = !ctx.subRows.every(row => row.box.checked);
      for (const row of ctx.subRows) row.box.checked = on;
      syncSubAll(ctx);
      render();
    });
    allItem.append(ctx.allBtn);
    ctx.sub.append(allItem);
    const addItems = list => {
      for (const book of list) {
        const li = element('li');
        const present = statRows.some(row => row.id === book.id);
        const row = { ...book };
        if (!present) {
          row.box = document.createElement('input');
          row.box.type = 'checkbox';
          li.append(row.box, ' ');
          statRows.push(row);
          ctx.subRows.push(row);
        }
        const link = element('a', '', book.title);
        link.href = `${locationURL.origin}/b/${book.id}`;
        li.append(link);
        const note = [book.series, book.number].filter(x => x !== '' && x != null).join(' - ');
        if (note) li.append(element('span', 'fdm-sub-note', '(' + note + ')'));
        if (present) li.append(element('span', 'fdm-sub-note', 'уже в списке'));
        const get = element('button', 'fdm-row-btn', '⬇');
        get.type = 'button';
        get.title = 'Скачать эту книгу одним кликом';
        get.addEventListener('click', event => { event.preventDefault(); downloadOne(statRecord(row)); });
        li.append(get, addInfoToggle(book.id, li));
        ctx.sub.append(li);
      }
    };
    addItems(books.slice(0, SUB_LIMIT));
    if (books.length > SUB_LIMIT) {
      const moreItem = element('li');
      const more = element('button', 'fdm-row-btn', `ещё ${books.length - SUB_LIMIT}`);
      more.type = 'button';
      more.addEventListener('click', event => { event.preventDefault(); moreItem.remove(); addItems(books.slice(SUB_LIMIT)); syncSubAll(ctx); refreshBooks(); });
      moreItem.append(more);
      ctx.sub.append(moreItem);
    }
    syncSubAll(ctx);
    refreshBooks();
  }

  /** Подпись «отметить все / снять отметки» раскрытого списка; без собственных флажков кнопки нет. */
  function syncSubAll(ctx) {
    if (!ctx.allBtn) return;
    ctx.allBtn.parentElement.hidden = !ctx.subRows.length;
    ctx.allBtn.textContent = ctx.subRows.length && ctx.subRows.every(row => row.box.checked) ? 'снять отметки' : 'отметить все';
  }

  function refreshBooks() {
    runtime.bookBoxes = checkboxEntries();
    runtime.bookCount = pageBooks().length;
    showDoneMarks();
    render();
  }

  function pageBooks() {
    if (isBook) return [singleBook()];
    if (isStat) return statRows.map(statRecord);
    return initialForm ? extractBooks(initialForm) : [];
  }

  function selectFormat(book, opts) {
    const formats = book.formats;
    if (!Array.isArray(formats) || !formats.length) return null;
    if (opts.format === 'other') return formats[0];
    const preferred = formats.find(f => f.format === opts.format);
    if (preferred) return preferred;
    if (!opts.fallback) return null;
    return [...formats].sort((a, b) => FORMATS.indexOf(a.format) - FORMATS.indexOf(b.format))[0];
  }

  function cleanFilePart(part, max = 130) {
    let result = String(part ?? '').normalize('NFC')
      .replace(/[\x00-\x1f<>:"/\\|?*]/g, '_')
      .replace(/\s+/g, ' ').replace(/[.\s]+$/g, '').trim();
    if (!result) result = 'Без названия';
    if (/^(?:CON|PRN|AUX|NUL|COM[1-9]|LPT[1-9])(?:\.|$)/i.test(result)) result = '_' + result;
    return Array.from(result).slice(0, max).join('');
  }

  function fileNameFor(book, format, authorName, pad) {
    const prefix = [];
    if (isAuthor) prefix.push(cleanFilePart(authorName, 65));
    if (isAuthor && book.series) prefix.push(cleanFilePart(book.series, 65));
    if (book.number !== null && Number.isFinite(book.number)) {
      prefix.push(String(book.number).padStart(pad, '0'));
    }
    prefix.push(cleanFilePart(book.title, 125));
    const extension = '.' + format.extension;
    let stem = prefix.join(' - ');
    stem = Array.from(stem).slice(0, Math.max(50, 180 - extension.length)).join('').replace(/[.\s]+$/g, '');
    return stem + extension;
  }

  // Keep a server-provided basename as-is whenever it is safe for a local
  // filesystem. Both Content-Disposition and a redirect URL are untrusted.
  // Preserve underscores, casing and numeric IDs in valid names.
  function safeOriginalName(value) {
    if (typeof value !== 'string') return '';
    let file = value.trim().replace(/[\\/]+/g, '/').split('/').pop() || '';
    file = file.normalize('NFC').replace(/[\x00-\x1f\x7f<>:"|?*]/g, '_')
      .replace(/[.\s]+$/g, '');
    if (!file || file === '.' || file === '..') return '';
    if (/^(?:CON|PRN|AUX|NUL|COM[1-9]|LPT[1-9])(?:\.|$)/i.test(file)) file = '_' + file;
    // Do not accept an executable or misleading URL path as a book filename.
    if (!/\.(?:fb2(?:\.zip)?|epub|mobi|azw3|pdf|djvu|txt|rtf|html|doc|docx|zip|rar|7z)$/i.test(file)) return '';
    if (Array.from(file).length > 220) {
      const match = file.match(/(\.fb2\.zip|\.[^.]+)$/i);
      const extension = match ? match[0] : '';
      file = Array.from(file.slice(0, -extension.length)).slice(0, 220 - extension.length).join('') + extension;
    }
    return file;
  }

  function decodeExtendedFileName(raw) {
    const candidate = String(raw).trim().replace(/^"|"$/g, '');
    const match = candidate.match(/^([^']*)'[^']*'(.*)$/);
    if (!match) return '';
    try {
      const bytes = [];
      for (let i = 0; i < match[2].length; i++) {
        if (match[2][i] === '%') {
          if (!/^[0-9a-f]{2}$/i.test(match[2].slice(i + 1, i + 3))) return '';
          bytes.push(parseInt(match[2].slice(i + 1, i + 3), 16));
          i += 2;
        } else {
          const cp = match[2].codePointAt(i);
          const encoded = new TextEncoder().encode(String.fromCodePoint(cp));
          bytes.push(...encoded);
          if (cp > 0xffff) i++;
        }
      }
      const encoding = match[1].toLowerCase();
      if (!['utf-8', 'iso-8859-1', 'latin1'].includes(encoding)) return '';
      return new TextDecoder(encoding, { fatal: true }).decode(new Uint8Array(bytes));
    } catch (_) { return ''; }
  }

  // Parse semicolon-separated parameters without splitting quoted filenames.
  function dispositionFilename(headers) {
    const line = String(headers || '').split(/\r?\n/).find(s => /^content-disposition\s*:/i.test(s));
    if (!line) return '';
    const params = line.slice(line.indexOf(':') + 1).match(/(?:;|^)\s*([\w*-]+)\s*=\s*(?:"((?:\\.|[^"\\])*)"|([^;]*))/g) || [];
    const values = new Map();
    for (const part of params) {
      const match = part.match(/(?:;|^)\s*([\w*-]+)\s*=\s*(?:"((?:\\.|[^"\\])*)"|([^;]*))/);
      if (match) values.set(match[1].toLowerCase(), match[2] !== undefined
        ? match[2].replace(/\\(["\\])/g, '$1') : match[3].trim());
    }
    const extended = values.get('filename*');
    const decoded = extended ? decodeExtendedFileName(extended) : '';
    return safeOriginalName(decoded) || safeOriginalName(values.get('filename'));
  }

  function serverFilename(headers, finalURL) {
    const fromHeader = dispositionFilename(headers);
    if (fromHeader) return { name: fromHeader, source: 'content-disposition' };
    try {
      const path = new URL(finalURL).pathname;
      const last = path.slice(path.lastIndexOf('/') + 1);
      const fromURL = safeOriginalName(decodeURIComponent(last));
      if (fromURL) return { name: fromURL, source: 'redirect-url' };
    } catch (_) {}
    return { name: '', source: 'fallback' };
  }

  function createJobs(books, opts) {
    const unique = new Set();
    const existingNames = new Set();
    const maxNumber = books.reduce((max, book) => Math.max(max, book.number || 0), 0);
    const padding = String(maxNumber).length;
    const authorName = title?.textContent.trim() || document.title || 'Автор';
    const jobs = [];
    let missingFormat = 0;
    let alreadyDownloaded = 0;
    let truncated = false;
    for (const book of books) {
      if (unique.has(book.id)) continue;
      unique.add(book.id);
      const selected = selectFormat(book, opts);
      if (!selected) { missingFormat++; continue; }
      if (opts.skipDownloaded && isDownloaded(book.id, selected.format)) { alreadyDownloaded++; continue; }
      if (jobs.length >= MAX_BOOKS) { truncated = true; break; }
      let name = fileNameFor(book, selected, authorName, padding);
      if (existingNames.has(name.toLowerCase())) {
        const ext = '.' + selected.extension;
        name = name.slice(0, -ext.length) + ' [' + book.id + ']' + ext;
      }
      existingNames.add(name.toLowerCase());
      jobs.push({
        id: book.id, title: book.title, url: selected.url, name,
        format: selected.format, extension: selected.extension, nameSource: 'pending', status: 'queued',
        attempts: 0, nextTryAt: 0, rateHits: 0, error: ''
      });
    }
    return { jobs, missingFormat, alreadyDownloaded, truncated };
  }

  function discoverPages(root, baseURL) {
    const pages = [];
    for (const link of root.querySelectorAll('a[href]')) {
      const url = sameSiteURL(link.getAttribute('href'), baseURL);
      if (!url || url.pathname !== locationURL.pathname || !url.searchParams.has('page')) continue;
      if (!/^\d{1,3}$/.test(url.searchParams.get('page'))) continue;
      const number = Number(url.searchParams.get('page'));
      if (number > 500) continue;
      // Keep only page parameter (avoid filters or search actions).
      const safe = new URL(baseURL);
      safe.searchParams.set('page', String(number));
      pages.push(safe.href);
    }
    return pages;
  }

  function abortError() { return new DOMException('Подготовка отменена', 'AbortError'); }

  function waitFor(ms, signal) {
    return new Promise((resolve, reject) => {
      if (signal?.aborted) { reject(abortError()); return; }
      const finish = () => { signal?.removeEventListener('abort', cancel); resolve(); };
      const timer = setTimeout(finish, ms);
      const cancel = () => { clearTimeout(timer); reject(abortError()); };
      signal?.addEventListener('abort', cancel, { once: true });
    });
  }

  // Network errors, timeouts, 429 and 5xx are transient: the caller may retry.
  function transient(error, retryAfter = 0) {
    error.transient = true;
    error.retryAfterMs = retryAfter;
    return error;
  }

  // Retries transient failures up to CATALOG_RETRIES times; honours Retry-After
  // (capped) and abandons the wait as soon as the signal aborts.
  async function httpGetText(url, signal) {
    for (let attempt = 0; ; attempt++) {
      try { return await httpGetOnce(url, signal); }
      catch (error) {
        if (!error?.transient || attempt >= CATALOG_RETRIES || signal?.aborted) throw error;
        await waitFor(Math.min(CATALOG_MAX_WAIT_MS, Math.max(error.retryAfterMs || 0, CATALOG_RETRY_MS * 2 ** attempt)), signal);
      }
    }
  }

  function httpGetOnce(url, signal) {
    return new Promise((resolve, reject) => {
      const safe = sameSiteURL(url);
      if (!safe) { reject(new Error('Внешний адрес отклонён')); return; }
      let request;
      let settled = false;
      const finish = (error, text) => {
        if (settled) return;
        settled = true;
        signal?.removeEventListener('abort', cancel);
        if (error) reject(error); else resolve(text);
      };
      const cancel = () => { finish(abortError()); request?.abort(); };
      if (signal?.aborted) { finish(abortError()); return; }
      signal?.addEventListener('abort', cancel, { once: true });
      try {
        request = GM_xmlhttpRequest({
          method: 'GET', url: safe.href, responseType: 'text', timeout: 30000,
          onload: response => {
            if (response.status !== 200) {
              const error = new Error('HTTP ' + response.status);
              finish(response.status === 429 || response.status >= 500
                ? transient(error, retryAfterMs(response.responseHeaders)) : error);
              return;
            }
            if (response.finalUrl && !sameSiteURL(response.finalUrl)) {
              finish(new Error('Перенаправление на другой сайт')); return;
            }
            finish(null, response.responseText || response.response || '');
          },
          onerror: () => finish(transient(new Error('Ошибка сети при чтении страницы'))),
          ontimeout: () => finish(transient(new Error('Тайм-аут при чтении страницы'))),
          onabort: () => finish(abortError())
        });
      } catch (error) { finish(error); }
    });
  }

  async function collectBooks(mode, opts, signal) {
    const current = pageBooks();
    if (isBook) return current;
    if (runtime.onlyRecord) return [runtime.onlyRecord];
    if (!opts.allPages || mode === 'checked') return mode === 'checked' ? current.filter(x => x.checked) : current;
    const all = [...current];
    const seenURLs = new Set([location.href]);
    const queue = discoverPages(main, location.href);
    // Always include page zero, even if the current page is a middle page.
    const firstURL = new URL(location.href);
    firstURL.searchParams.delete('page');
    if (firstURL.href !== location.href) queue.unshift(firstURL.href);
    let count = 0;
    const unreachable = [];
    const deferred = [];
    const guessed = new Set();
    let secondChance = false;
    for (;;) {
      while (queue.length && count < MAX_PAGES - 1) {
        const url = queue.shift();
        if (seenURLs.has(url)) continue;
        seenURLs.add(url);
        count++;
        runtime.catalogProgress = { index: count + 1, total: Math.min(MAX_PAGES, count + 1 + queue.length) };
        setMessage(`Проверяю страницы каталога (найдено ${all.length} книг)`);
        if (count > 1) await waitFor(opts.delay, signal);
        let markup;
        try { markup = await httpGetText(url, signal); }
        catch (error) {
          if (error?.name === 'AbortError') throw error;
          console.warn('[FDM2] Catalogue page failed:', url, error);
          // Угаданная страница могла быть просто концом каталога: не ошибка, без новых догадок.
          if (guessed.has(url)) continue;
          const failed = new URL(url);
          const page = failed.searchParams.get('page');
          if (!secondChance) deferred.push(url); else unreachable.push(page === null ? 'первая' : 'page=' + page);
          // Ссылки на следующие страницы были только на упавшей: пробуем page=N+1 вслепую.
          failed.searchParams.set('page', String(Number(page || 0) + 1));
          if (!seenURLs.has(failed.href) && !queue.includes(failed.href)) { guessed.add(failed.href); queue.push(failed.href); }
          continue;
        }
        const doc = new DOMParser().parseFromString(markup, 'text/html');
        const root = doc.querySelector('div#main') || doc.querySelector('main') || doc.body;
        const form = getBookForm(root, isAuthor);
        if (!form) { console.warn('[FDM2] Page without recognized books:', url); continue; }
        all.push(...extractBooks(form, url));
        for (const next of discoverPages(root, url)) if (!seenURLs.has(next) && !queue.includes(next)) queue.push(next);
      }
      if (secondChance || !deferred.length) break;
      // Последний шанс: упавшие страницы ещё раз, с тем же разбором и лимитом.
      secondChance = true;
      for (const url of deferred) { seenURLs.delete(url); queue.unshift(url); }
    }
    if (unreachable.length) runtime.prepareNotes.push(`Страницы каталога не загрузились (${unreachable.join(', ')}); книги с них и со страниц после них могут отсутствовать в очереди.`);
    if (queue.length) runtime.prepareNotes.push(`Достигнут лимит ${MAX_PAGES} страниц: ещё ${queue.length} не проверено.`);
    return all;
  }

  function countJobs() {
    if (runtime.countsCache?.state === state) return runtime.countsCache.counts;
    const counts = { queued: 0, active: 0, done: 0, failed: 0, skipped: 0,
      firstActive: null, failedJobs: [], fallbackNames: 0 };
    for (const job of state?.jobs || []) {
      counts[job.status]++;
      if (job.status === 'active' && !counts.firstActive) counts.firstActive = job;
      if (job.status === 'failed') counts.failedJobs.push(job);
      if (job.status === 'done' && job.nameSource === 'fallback') counts.fallbackNames++;
    }
    runtime.countsCache = { state, counts };
    return counts;
  }

  function setMessage(value) {
    runtime.message = value;
    if (ui) render();
  }

  function queueBusy() { return runtime.preparing || runtime.active > 0 || !!(state && !state.paused && countJobs().queued); }

  async function acquireQueueLock() {
    if (runtime.queueLockRelease) return true;
    if (!navigator.locks?.request) return true;
    if (runtime.queueLockPending) return runtime.queueLockPending;
    runtime.queueLockPending = new Promise((resolve, reject) => {
      navigator.locks.request(PAGE_KEY, { ifAvailable: true }, lock => {
        if (!lock) { resolve(false); return; }
        return new Promise(release => {
          runtime.queueLockRelease = release;
          resolve(true);
        });
      }).catch(reject);
    });
    try {
      const acquired = await runtime.queueLockPending;
      if (!acquired) setMessage('Очередь этой страницы уже запущена в другой вкладке.');
      return acquired;
    } catch (error) {
      setMessage('Не удалось заблокировать очередь: ' + error.message);
      return false;
    } finally { runtime.queueLockPending = null; }
  }

  function releaseQueueLock() {
    if (runtime.preparing || runtime.active || (state && !state.paused && state.jobs.some(job => job.status === 'queued'))) return;
    runtime.queueLockRelease?.();
    runtime.queueLockRelease = null;
  }

  async function prepare(mode) {
    if (queueBusy() || runtime.queueLockPending) return;
    if (!await folderIsReady()) return;
    const counts = countJobs();
    if (state && (counts.queued || counts.active) && !window.confirm('Старая очередь будет заменена. Продолжить?')) return;
    if (!await acquireQueueLock()) return;
    if (queueBusy()) return;
    runtime.preparing = true;
    runtime.prepareController = new AbortController();
    runtime.message = 'Ищу книги…';
    runtime.prepareNotes = [];
    runtime.catalogProgress = null;
    runtime.doneTimes = [];
    saveSettings();
    render();
    try {
      const records = await collectBooks(mode, settings, runtime.prepareController.signal);
      const { jobs, missingFormat, alreadyDownloaded, truncated } = createJobs(records, runtime.onlyRecord ? { ...settings, skipDownloaded: false } : settings);
      if (truncated) runtime.prepareNotes.push(`Очередь обрезана: взято ${MAX_BOOKS} книг, остальные не вошли.`);
      const notes = runtime.prepareNotes.length ? ' ' + runtime.prepareNotes.join(' ') : '';
      if (!jobs.length) {
        const detail = !records.length ? (mode === 'checked'
          ? 'На странице нет отмеченных книг. Используйте «Отметить все книги».'
          : 'Книги не распознаны: возможно, изменилась структура страницы.')
          : alreadyDownloaded && !missingFormat
          ? `Все книги (${alreadyDownloaded}) уже скачаны ранее. Чтобы скачать снова, отключите «Пропускать уже скачанные».`
          : `${missingFormat} книг без подходящего формата` + (alreadyDownloaded ? `, ${alreadyDownloaded} уже скачаны` : '') +
            '. Попробуйте «Любой доступный».';
        setMessage('Очередь не создана. ' + detail + notes);
        return;
      }
      state = {
        version: VERSION, key: PAGE_KEY, createdAt: Date.now(),
        paused: false, cancelled: false, options: { ...settings }, skippedByFormat: missingFormat,
        skippedByHistory: alreadyDownloaded, jobs
      };
      runtime.jobsDirty = true;
      dropStatusBlocks();
      runtime.cooldownUntil = 0;
      persist();
      runtime.lastStart = 0;
      runtime.message = `${jobs.length} книг в очереди` + (missingFormat ? `, пропущено по формату: ${missingFormat}` : '') +
        (alreadyDownloaded ? `, уже скачано ранее: ${alreadyDownloaded}` : '') + notes;
    } catch (error) {
      setMessage(error.name === 'AbortError' ? 'Подготовка очереди отменена.' : 'Не удалось построить очередь: ' + error.message);
      console.error('[FDM2] Queue preparation:', error);
    } finally {
      runtime.preparing = false;
      runtime.prepareController = null;
      runtime.catalogProgress = null;
      render();
      pump();
      releaseQueueLock();
    }
  }

  function clearTimer() {
    if (runtime.timer !== null) { clearTimeout(runtime.timer); runtime.timer = null; }
  }

  function schedulePump(ms) {
    clearTimer();
    runtime.timer = setTimeout(() => { runtime.timer = null; pump(); }, Math.max(50, ms));
  }

  function pump() {
    clearTimer();
    if (!state || state.paused || runtime.preparing) { releaseQueueLock(); return; }
    const opts = state.options;
    const now = Date.now();
    if (runtime.cooldownUntil > now) { schedulePump(runtime.cooldownUntil - now); return; }
    while (runtime.active < opts.parallel) {
      const next = state.jobs.find(job => job.status === 'queued' && (job.nextTryAt || 0) <= Date.now());
      if (!next) break;
      const wait = Math.max(0, runtime.lastStart + opts.delay - Date.now());
      if (wait > 0) { schedulePump(wait); break; }
      runtime.lastStart = Date.now();
      launch(next);
    }
    const pending = state.jobs.filter(job => job.status === 'queued');
    if (pending.length && runtime.active < opts.parallel) {
      const earliest = Math.min(...pending.map(job => Math.max(job.nextTryAt || 0, runtime.lastStart + opts.delay)));
      schedulePump(Math.max(50, earliest - now));
    }
    if (!pending.length && runtime.active === 0) {
      state.paused = true;
      flushHistory();
      persist();
      setMessage('Загрузка завершена. Проверьте количество ошибок и журнал.');
      notifyFinished();
      releaseQueueLock();
    }
    render();
  }

  /** Системное уведомление об окончании очереди: если вкладка скрыта или книг больше одной. */
  function notifyFinished() {
    if (typeof GM_notification !== 'function') return;
    const counts = countJobs();
    if (!document.hidden && state.jobs.length < 2) return;
    try {
      GM_notification({
        title: 'Flibusta Download Manager',
        text: `Скачано ${counts.done} из ${state.jobs.length}` + (counts.failed ? `, ошибок ${counts.failed}` : ''),
        timeout: 15000,
        onclick: () => window.focus()
      });
    } catch (error) { console.warn('[FDM2] Cannot notify:', error); }
  }

  /** «Осталось ≈ …» по среднему промежутку между последними завершёнными книгами; null — пока не по чему судить. */
  function timeLeft(remaining) {
    const times = runtime.doneTimes;
    if (times.length < 2 || !remaining) return null;
    const seconds = Math.round((times[times.length - 1] - times[0]) / (times.length - 1) * remaining / 1000);
    if (seconds < 60) return 'меньше минуты';
    const minutes = Math.round(seconds / 60);
    return minutes < 60 ? `${minutes} мин` : `${Math.floor(minutes / 60)} ч ${minutes % 60} мин`;
  }

  function launch(job) {
    job.status = 'active';
    job.attempts += 1;
    runtime.active += 1;
    persist(job);
    render();
    download(job, state.options).then(result => {
      job.status = 'done';
      job.name = result.name;
      job.nameSource = result.source;
      job.error = '';
      markDownloaded(job);
      runtime.doneTimes = [...runtime.doneTimes.slice(-10), Date.now()];
      showDoneMarks();
    }).catch(error => {
      const message = error?.message || String(error);
      job.error = message;
      // A rate limit is the server's state, not a fault of this book: it does
      // not consume a retry, but is capped so a permanent 429 cannot loop.
      const rateLimited = !!error?.rateLimited;
      if (rateLimited) {
        job.attempts = Math.max(0, job.attempts - 1);
        job.rateHits = (job.rateHits || 0) + 1;
        runtime.cooldownUntil = Math.max(runtime.cooldownUntil,
          Date.now() + Math.max(error.retryAfterMs || 0, Math.min(60000, 10000 * 2 ** (job.rateHits - 1))));
      }
      if (state.cancelled) {
        job.status = 'skipped';
      } else if (rateLimited ? job.rateHits <= MAX_RATE_HITS
        : error?.retryable !== false && job.attempts <= state.options.retries) {
        job.status = 'queued';
        job.nextTryAt = rateLimited ? 0 : Date.now() + Math.min(60000, 1500 * 2 ** (job.attempts - 1));
      } else {
        job.status = 'failed';
      }
      console.warn('[FDM2] Download problem:', job.id, message);
    }).finally(() => {
      runtime.active -= 1;
      runtime.progress.delete(job.id);
      persist(job);
      render();
      pump();
    });
  }

  function retryAfterMs(headers, now = Date.now()) {
    const match = String(headers || '').match(/^retry-after:\s*(.+)$/im);
    if (!match) return 0;
    const value = match[1].trim();
    const ms = /^\d+$/.test(value) ? Number(value) * 1000 : Date.parse(value) - now;
    return Number.isFinite(ms) ? Math.max(0, Math.min(ms, 86400000)) : 0;
  }

  function downloadError(message, retryable = true, rateLimited = false) {
    const error = new Error(message);
    error.retryable = retryable;
    error.rateLimited = rateLimited;
    return error;
  }

  function updateProgress(job, event) {
    const loaded = Number(event.loaded) || 0;
    const total = Number(event.total) || Number(event.totalSize) || 0;
    runtime.progress.set(job.id, { loaded, total });
    if (Date.now() - runtime.lastProgressRender > 180) {
      runtime.lastProgressRender = Date.now();
      render();
    }
  }

  function useDownload(url, name, job, askEach = false) {
    return new Promise((resolve, reject) => {
      let settled = false;
      let handle = null;
      let idle = null;
      const done = (error) => {
        if (settled) return;
        settled = true;
        clearTimeout(idle);
        if (error) reject(error); else resolve();
      };
      // GM_download may never call back (extension conflicts, closed dialogs).
      // Without a watchdog the job stays active and blocks the queue. Not
      // retryable: the browser may still have saved the file, and a silent
      // retry would create a duplicate. A save dialog may legitimately wait.
      const arm = () => {
        if (askEach) return;
        clearTimeout(idle);
        idle = setTimeout(() => {
          try { handle?.abort?.(); } catch (_) {}
          done(downloadError(`GM_download не ответил за ${SAVE_IDLE_TIMEOUT / 1000} с. Проверьте папку загрузок перед повтором.`, false));
        }, SAVE_IDLE_TIMEOUT);
      };
      try {
        arm();
        handle = GM_download({
          url, name, saveAs: askEach, conflictAction: 'uniquify',
          onload: () => done(null),
          onerror: response => {
            const code = response?.error || 'unknown';
            const detail = String(response?.details || '');
            done(downloadError(`Ошибка сохранения: ${code} ${detail}`.trim(),
              !['not_enabled', 'not_permitted', 'not_whitelisted', 'not_supported'].includes(code)));
          },
          ontimeout: () => done(downloadError('Тайм-аут сохранения файла')),
          onprogress: event => { arm(); updateProgress(job, event); }
        });
      } catch (error) { done(downloadError('GM_download: ' + error.message, false)); }
    });
  }

  function blockedIPv4(a) {
    return a.some(v => v > 255) || a[0] === 0 || a[0] === 10 || a[0] === 127 || a[0] >= 224 ||
      (a[0] === 169 && a[1] === 254) || (a[0] === 192 && a[1] === 168) ||
      (a[0] === 172 && a[1] >= 16 && a[1] <= 31) ||
      (a[0] === 100 && a[1] >= 64 && a[1] <= 127);
  }

  // Eight 16-bit groups of an IPv6 literal (no brackets), or null if malformed.
  function ipv6Groups(host) {
    const halves = host.split('::');
    if (halves.length > 2) return null;
    const side = text => {
      const parts = text ? text.split(':') : [];
      const last = parts[parts.length - 1];
      if (last && last.includes('.')) {
        const q = last.split('.').map(Number);
        if (q.length !== 4 || q.some(v => !Number.isInteger(v) || v > 255)) return null;
        parts.splice(-1, 1, ((q[0] << 8) | q[1]).toString(16), ((q[2] << 8) | q[3]).toString(16));
      }
      return parts.every(p => /^[0-9a-f]{1,4}$/i.test(p)) ? parts.map(p => parseInt(p, 16)) : null;
    };
    const head = side(halves[0]);
    const tail = halves.length === 2 ? side(halves[1]) : [];
    if (!head || !tail) return null;
    const fill = 8 - head.length - tail.length;
    if (halves.length === 2 ? fill < 1 : fill !== 0) return null;
    return [...head, ...Array(fill).fill(0), ...tail];
  }

  function safeRedirectTarget(raw) {
    try {
      const endpoint = new URL(raw);
      if (!['http:', 'https:'].includes(endpoint.protocol) || endpoint.username || endpoint.password) return null;
      const h = endpoint.hostname.toLowerCase().replace(/^\[|\]$/g, '').replace(/\.+$/, '');
      if (!h || h === 'localhost' || h.endsWith('.localhost') || h.endsWith('.local') || h.endsWith('.internal') || h.endsWith('.lan')) return null;
      if (h.includes(':')) {
        const g = ipv6Groups(h);
        if (!g) return null;
        const v4 = [g[6] >> 8, g[6] & 255, g[7] >> 8, g[7] & 255];
        const lowZero = g.slice(0, 5).every(v => v === 0);
        if (g.slice(0, 6).every(v => v === 0)) return null; // ::, ::1, IPv4-compatible
        if (lowZero && g[5] === 0xffff) return blockedIPv4(v4) ? null : endpoint; // IPv4-mapped
        if (g[0] === 0x64 && g[1] === 0xff9b && g.slice(2, 6).every(v => v === 0) && blockedIPv4(v4)) return null; // NAT64
        if ((g[0] & 0xfe00) === 0xfc00 || (g[0] & 0xffc0) === 0xfe80 || (g[0] & 0xff00) === 0xff00) return null;
      }
      if (/^\d+\.\d+\.\d+\.\d+$/.test(h) && blockedIPv4(h.split('.').map(Number))) return null;
      return endpoint;
    } catch (_) { return null; }
  }

  function locationHeader(headers) {
    return String(headers || '').match(/^location:\s*(.+)$/im)?.[1].trim() || '';
  }

  // Redirects are followed by hand so every hop is checked BEFORE it is
  // requested. If the environment cannot do that (status 0, 3xx without
  // Location) the request falls back to redirect:'follow' and the final
  // address is checked after the response, as before.
  // No total timeout: a large DjVu over Tor/I2P may legitimately take many
  // minutes. The request is aborted only after IDLE_TIMEOUT without data.
  function getBlob(job) {
    return new Promise((resolve, reject) => {
      let idle = null;
      let stalled = false;
      let request = null;
      // Не поддерживается в этой среде — запомнено: сразу follow, без ожидания отказа на каждой книге.
      let manual = !(Date.now() - Number(readStored(REDIRECT_OFF_KEY, 0)) < REDIRECT_RETRY_MS);
      let hops = 0;
      const idleMs = Math.min(IDLE_TIMEOUT, (state?.options?.idle || settings.idle || DEFAULTS.idle) * 1000);
      const manualOff = () => { manual = false; try { GM_setValue(REDIRECT_OFF_KEY, Date.now()); } catch (_) {} };
      const arm = () => {
        clearTimeout(idle);
        idle = setTimeout(() => { stalled = true; try { request?.abort(); } catch (_) {} fail(); }, idleMs);
      };
      const fail = () => reject(downloadError(`Нет данных от сервера ${Math.round(idleMs / 1000)} с`));
      const finish = () => clearTimeout(idle);
      // Some Tampermonkey/browser builds never complete redirect:'manual' (timeout, network error).
      // Before the first hop that means the mode itself failed: retry once with 'follow'.
      const fallBack = () => {
        if (!manual || hops > 0) return false;
        manualOff();
        console.warn('[FDM2] redirect:manual не сработал, используется режим follow с проверкой после запроса.');
        step(job.url);
        return true;
      };
      const step = url => {
        try {
          arm();
          request = GM_xmlhttpRequest({
            method: 'GET', url, responseType: 'blob', timeout: 0, redirect: manual ? 'manual' : 'follow',
            onload: response => {
              finish();
              const redirected = response.status >= 300 && response.status < 400;
              if (manual && (response.status === 0 || redirected)) {
                const next = redirected ? locationHeader(response.responseHeaders) : '';
                if (!next) {
                  manualOff();
                  console.warn('[FDM2] Ручное перенаправление недоступно, используется режим follow с проверкой после запроса.');
                  step(url);
                  return;
                }
                let target = null;
                try { target = safeRedirectTarget(new URL(next, url).href); } catch (_) {}
                if (!target) { reject(downloadError('Перенаправление на недопустимый адрес', false)); return; }
                if (++hops > MAX_REDIRECTS) { reject(downloadError('Слишком много перенаправлений', false)); return; }
                step(target.href);
                return;
              }
              if (response.status !== 200) {
                const error = downloadError('HTTP ' + response.status, response.status >= 500 || response.status === 429,
                  response.status === 429 || response.status === 503);
                error.retryAfterMs = retryAfterMs(response.responseHeaders);
                reject(error);
                return;
              }
              // The original link is always within Flibusta. Its file server may
              // be on a different public host; direct browser downloads follow
              // that redirect. Check the final protocol/host and actual file.
              const endpoint = safeRedirectTarget(response.finalUrl || url);
              if (!endpoint) {
                reject(downloadError('Перенаправление на недопустимый адрес', false));
                return;
              }
              runtime.lastRemoteHost = endpoint.hostname;
              if (endpoint.origin !== location.origin) {
                console.info('[FDM2] Файловый сервер:', endpoint.hostname);
              }
              if (!(response.response instanceof Blob)) {
                reject(downloadError('Сервер вернул неожиданный тип данных'));
                return;
              }
              resolve({ blob: response.response, headers: response.responseHeaders || '', finalURL: endpoint.href });
            },
            onerror: response => { finish(); if (fallBack()) return; reject(downloadError('Ошибка сети или нет разрешения Tampermonkey на файловый сервер' + (response?.error ? ': ' + response.error : ''))); },
            ontimeout: () => { finish(); if (fallBack()) return; reject(downloadError('Тайм-аут получения книги')); },
            onabort: () => { finish(); if (stalled) return; if (fallBack()) return; reject(downloadError('Загрузка прервана')); },
            onprogress: event => { arm(); updateProgress(job, event); }
          });
        } catch (error) { finish(); reject(downloadError('GM_xmlhttpRequest: ' + error.message)); }
      };
      step(job.url);
    });
  }

  async function inspectBlob(blob, headers, job) {
    if (!blob.size) throw downloadError('Сервер вернул пустой файл', false);
    const head = new Uint8Array(await blob.slice(0, 65536).arrayBuffer());
    const zipped = ZIP_MAGIC.every((byte, i) => head[i] === byte);
    const encoding = head[0] === 0xff && head[1] === 0xfe ? 'utf-16le'
      : head[0] === 0xfe && head[1] === 0xff ? 'utf-16be'
      : head[0] === 0x3c && head[1] === 0 ? 'utf-16le'
      : head[0] === 0 && head[1] === 0x3c ? 'utf-16be' : 'utf-8';
    const text = new TextDecoder(encoding, { fatal: false }).decode(head).replace(/^\uFEFF/, '').trimStart().toLowerCase();
    const serverHTML = /^\s*content-type:\s*text\/html\b/im.test(headers);
    if (job.format !== 'html' && (serverHTML || /^<(?:!doctype\s+html|html|head|body)\b/.test(text))) {
      throw downloadError('Вместо книги сервер вернул HTML-страницу', false);
    }
    if (job.format === 'epub' && !zipped) throw downloadError('EPUB не содержит ZIP-сигнатуру', false);
    if (job.format === 'pdf' && !text.startsWith('%pdf-')) {
      throw downloadError('Некорректная сигнатура PDF', false);
    }
    if (job.format === 'fb2') {
      if (!zipped && !/<fictionbook(?:\s|>)/.test(text)) {
        throw downloadError(blob.size > head.length
          ? 'Не удалось проверить FB2: корневой элемент не найден в первых 64 КиБ'
          : 'В файле FB2 не найден корневой элемент FictionBook', false);
      }
      const ext = zipped ? '.fb2.zip' : '.fb2';
      return job.name.replace(/\.fb2(?:\.zip)?$/i, '') + ext;
    }
    return job.name;
  }

  function writeIntoFolder(blob, fileName, directory = runtime.folder) {
    const write = () => writeIntoFolderSerial(blob, fileName, directory);
    const task = runtime.folderWriteTail.then(() => navigator.locks?.request
      ? navigator.locks.request('fdm2:folder-write', write) : write());
    runtime.folderWriteTail = task.catch(() => {});
    return task;
  }

  async function writeIntoFolderSerial(blob, fileName, directory) {
    if (!directory) throw downloadError('Папка не выбрана', false);
    const permission = await folderAccess(directory);
    if (permission !== 'granted') throw downloadError('Браузер отозвал доступ к папке. Выберите папку повторно.', false);
    const ext = fileName.match(/(\.(?:fb2\.zip|[^.]+))$/i)?.[1] || '';
    const stem = ext ? fileName.slice(0, -ext.length) : fileName;
    let candidate = fileName;
    let handle;
    for (let index = 0; index < 100; index++) {
      try {
        await directory.getFileHandle(candidate);
        candidate = `${stem} (${index + 1})${ext}`;
      } catch (error) {
        // A directory with the same name occupies the candidate: try the next one.
        if (error?.name === 'TypeMismatchError') { candidate = `${stem} (${index + 1})${ext}`; continue; }
        if (error?.name !== 'NotFoundError') {
          throw downloadError('Не удалось проверить имя файла в папке: ' + (error?.name || error?.message || error), false);
        }
        handle = await directory.getFileHandle(candidate, { create: true });
        break;
      }
    }
    if (!handle) throw downloadError('Не удалось подобрать уникальное имя файла', false);
    const writable = await handle.createWritable();
    try { await writable.write(blob); await writable.close(); }
    catch (error) { try { await writable.abort(); } catch (_) {} throw error; }
    return candidate;
  }

  async function download(job, opts) {
    if (!sameSiteURL(job.url)) throw downloadError('Адрес файла не соответствует сайту', false);
    if (runtime.folderExpected && !runtime.folder) throw downloadError('Ранее выбранная папка недоступна. Восстановите доступ.', false);
    const dir = runtime.folder;
    // Readable naming can directly download from URL when validation and a
    // custom directory are not requested. Original naming MUST read GET
    // metadata; GM_download(name: ...) otherwise overrides the HTTP name.
    if (opts.naming === 'readable' && !opts.verify && !dir) {
      await useDownload(job.url, job.name, job, opts.askEach);
      return { name: job.name, source: 'generated' };
    }
    const { blob, headers, finalURL } = await getBlob(job);
    const checkedName = opts.verify ? await inspectBlob(blob, headers, job) : job.name;
    const origin = opts.naming === 'readable'
      ? { name: checkedName, source: 'generated' }
      : serverFilename(headers, finalURL);
    const actualName = origin.name || checkedName;
    const source = origin.name ? origin.source : 'fallback';
    if (source === 'fallback') {
      console.warn('[FDM2] Оригинальное имя файла отсутствует в ответе сервера. Использован запасной вариант:', job.url);
    }
    if (dir) return { name: await writeIntoFolder(blob, actualName, dir), source };
    // Prefer Blob on Tampermonkey >=5.4.6226. A sandbox-local blob: URL
    // may be rejected by GM_download in some browser/extension modes.
    try {
      await useDownload(blob, actualName, job, opts.askEach);
      return { name: actualName, source };
    } catch (error) {
      if (error.retryable === false) throw error;
      console.warn('[FDM2] GM_download(Blob) failed; trying a blob URL:', error);
      const objectURL = URL.createObjectURL(blob);
      try {
        await useDownload(objectURL, actualName, job, opts.askEach);
        return { name: actualName, source };
      } finally { URL.revokeObjectURL(objectURL); }
    }
  }

  function pause() {
    if (!state) return;
    state.paused = true;
    runtime.doneTimes = []; // время паузы не должно попасть в оценку «осталось»
    clearTimer();
    flushHistory();
    persist();
    setMessage('Пауза: выполняющиеся загрузки завершатся, новые не начнутся.');
    releaseQueueLock();
  }

  async function resume() {
    if (!state || runtime.preparing) return;
    if (!await folderIsReady()) return;
    if (!state.jobs.some(job => job.status === 'queued')) return;
    if (!await acquireQueueLock()) return;
    state.cancelled = false;
    state.paused = false;
    persist();
    setMessage('Загрузка продолжена');
    pump();
  }

  function stop() {
    if (runtime.preparing) { runtime.prepareController?.abort(); return; }
    if (!state || !window.confirm('Отменить оставшиеся задания? Уже начатые файлы могут завершиться.')) return;
    state.cancelled = true;
    state.paused = true;
    for (const job of state.jobs) if (job.status === 'queued') job.status = 'skipped';
    clearTimer();
    flushHistory();
    persist();
    setMessage('Оставшаяся очередь отменена');
    releaseQueueLock();
  }

  async function retryFailed() {
    if (!state || runtime.preparing || runtime.active) return;
    if (!await folderIsReady()) return;
    const failed = state.jobs.filter(job => job.status === 'failed');
    if (!failed.length || !await acquireQueueLock()) return;
    state.cancelled = false;
    runtime.doneTimes = [];
    for (const job of failed) {
      job.status = 'queued'; job.attempts = 0; job.rateHits = 0; job.nextTryAt = 0; job.error = '';
    }
    state.paused = false;
    persist();
    setMessage(`Повторяю ${failed.length} неудачных загрузок`);
    pump();
  }

  function exportReport() {
    if (!state) return;
    const contents = {
      script: 'Flibusta Download Manager ' + VERSION,
      createdAt: new Date(state.createdAt).toISOString(),
      sourcePage: location.href,
      options: state.options,
      books: state.jobs.map(({ id, title, url, name, nameSource, format, status, attempts, error }) => ({
        id, title, url, name, nameSource, format, status, attempts, error
      }))
    };
    const blob = new Blob([JSON.stringify(contents, null, 2)], { type: 'application/json;charset=utf-8' });
    const url = URL.createObjectURL(blob);
    const anchor = document.createElement('a');
    anchor.href = url;
    anchor.download = 'flibusta-download-report-' + new Date().toISOString().slice(0, 10) + '.json';
    document.body.appendChild(anchor);
    anchor.click();
    anchor.remove();
    setTimeout(() => URL.revokeObjectURL(url), 5000);
  }

  function checkboxEntries() {
    if (isStat) return statRows.map(row => row.box);
    if (!initialForm) return [];
    const seen = new Set();
    return extractBooks(initialForm).map(book => book.checkboxElement)
      .filter(node => node && !seen.has(node) && (seen.add(node), true));
  }

  function setBookSelection(checked) {
    const boxes = runtime.bookBoxes;
    for (const box of boxes) {
      box.checked = checked;
    }
    if (runtime.nativeMaster) runtime.nativeMaster.checked = checked;
    setMessage(`${boxes.filter(x => x.checked).length} из ${boxes.length} книг отмечено`);
    render();
  }

  function isNativeSelectAll(box) {
    if (!box || box.tagName !== 'INPUT' || box.type !== 'checkbox' || box.closest('#fdm-panel')) return false;
    if (runtime.bookBoxes.includes(box)) return false;
    const near = box.parentElement && box.parentElement.textContent.length < 60 ? box.parentElement.textContent : '';
    const key = [box.id, box.name, box.labels?.[0]?.textContent, box.closest('label')?.textContent,
      box.nextSibling?.textContent, box.nextElementSibling?.textContent?.slice(0, 40), near].filter(Boolean).join(' ');
    return SELECT_ALL.test(key);
  }

  function attachNativeSelectAll() {
    for (const box of document.querySelectorAll('input[type="checkbox"]')) {
      if (isNativeSelectAll(box)) runtime.nativeMaster = box;
    }
    // Делегирование: галочку сайт может дорисовать уже после запуска скрипта.
    document.addEventListener('change', event => {
      if (!isNativeSelectAll(event.target)) return;
      runtime.nativeMaster = event.target;
      setBookSelection(event.target.checked);
    }, true);
  }

  function attachBookSelectionListener() {
    main.addEventListener('change', event => {
      // Список флажков растёт, когда в рейтинге раскрывают автора или серию.
      if (!runtime.bookBoxes.includes(event.target)) return;
      if (runtime.nativeMaster) runtime.nativeMaster.checked = runtime.bookBoxes.every(box => box.checked);
      render();
    });
  }

  function openFolderDB() {
    return new Promise((resolve, reject) => {
      if (!globalThis.indexedDB) { reject(Error('IndexedDB недоступна')); return; }
      const request = indexedDB.open(FOLDER_DB, 1);
      request.onupgradeneeded = () => {
        if (!request.result.objectStoreNames.contains(FOLDER_STORE)) {
          request.result.createObjectStore(FOLDER_STORE);
        }
      };
      request.onsuccess = () => resolve(request.result);
      request.onerror = () => reject(request.error || Error('Ошибка открытия IndexedDB'));
    });
  }

  async function folderDB(operation, value) {
    const db = await openFolderDB();
    try {
      return await new Promise((resolve, reject) => {
        const tx = db.transaction(FOLDER_STORE, operation === 'get' ? 'readonly' : 'readwrite');
        const store = tx.objectStore(FOLDER_STORE);
        const key = 'folder:' + location.origin;
        const request = operation === 'get' ? store.get(key)
          : operation === 'put' ? store.put(value, key) : store.delete(key);
        let result;
        request.onsuccess = () => { result = request.result; };
        tx.oncomplete = () => resolve(result);
        tx.onerror = () => reject(tx.error || Error('Ошибка IndexedDB'));
        tx.onabort = () => reject(tx.error || Error('Запись папки отменена'));
      });
    } finally { db.close(); }
  }

  async function folderAccess(handle = runtime.folder) {
    if (!handle) return 'missing';
    try {
      return typeof handle.queryPermission === 'function'
        ? await handle.queryPermission({ mode: 'readwrite' }) : 'granted';
    } catch (_) { return 'denied'; }
  }

  async function restoreFolder() {
    if (!runtime.folderExpected) return;
    const revision = runtime.folderRevision;
    try {
      const handle = await folderDB('get');
      if (revision !== runtime.folderRevision) return;
      if (handle?.kind !== 'directory' || !handle.name) {
        runtime.folderPermission = 'missing';
        setMessage('Ранее выбрана папка «' + runtime.folderName + '», но сохранить доступ к ней не удалось. Выберите её снова.');
      } else {
        runtime.folder = handle;
        runtime.folderName = handle.name;
        runtime.folderPermission = await folderAccess(handle);
        if (revision !== runtime.folderRevision) return;
        setMessage(runtime.folderPermission === 'granted'
          ? `Папка «${handle.name}» восстановлена и доступна для записи.`
          : `Папка «${handle.name}» восстановлена. Нажмите «Разрешить папку» перед загрузкой.`);
      }
    } catch (error) {
      if (revision === runtime.folderRevision) {
        runtime.folderPermission = 'missing';
        setMessage('Имя папки «' + runtime.folderName + '» сохранено, но восстановление доступа не удалось: ' + error.message);
      }
    } finally {
      if (revision === runtime.folderRevision) { runtime.folderRestoring = false; render(); }
    }
  }

  async function folderIsReady() {
    if (!runtime.folderExpected) return true;
    if (runtime.folderRestoring) {
      setMessage('Идёт восстановление выбранной папки. Повторите действие после его завершения.');
      return false;
    }
    runtime.folderPermission = await folderAccess();
    render();
    if (runtime.folderPermission !== 'granted') {
      setMessage(`Папка «${runtime.folderName || 'неизвестно'}» сохранена, но запись недоступна. ` +
        (runtime.folder ? 'Нажмите «Разрешить папку».' : 'Выберите папку повторно.'));
      return false;
    }
    return true;
  }

  async function grantFolder() {
    if (!runtime.folder) {
      setMessage('Нет сохранённого доступа к папке. Нажмите «Выбрать папку…».');
      return;
    }
    try {
      runtime.folderPermission = typeof runtime.folder.requestPermission === 'function'
        ? await runtime.folder.requestPermission({ mode: 'readwrite' }) : await folderAccess();
      setMessage(runtime.folderPermission === 'granted'
        ? `Доступ к папке «${runtime.folderName}» разрешён.`
        : 'Браузер не разрешил запись в эту папку.');
    } catch (error) { setMessage('Не удалось получить доступ к папке: ' + error.message); }
    render();
  }

  async function selectFolder() {
    if (queueBusy()) { setMessage('Поставьте загрузку на паузу перед сменой папки.'); return; }
    if (typeof window.showDirectoryPicker !== 'function' || !window.isSecureContext) {
      setMessage('Выбор одной папки недоступен здесь. Включите «Спрашивать место для каждого файла» или задайте папку в настройках браузера.');
      return;
    }
    try {
      const directory = await window.showDirectoryPicker({ mode: 'readwrite', id: 'flibusta-books' });
      runtime.folderRevision++;
      runtime.folder = directory;
      runtime.folderExpected = true;
      runtime.folderName = directory.name;
      runtime.folderPermission = await folderAccess(directory);
      runtime.folderRestoring = false;
      GM_setValue(FOLDER_INFO_KEY, { selected: true, name: directory.name });
      try {
        await folderDB('put', directory);
        setMessage(`Папка «${directory.name}» выбрана и запомнена. После перезапуска может потребоваться разрешить доступ.`);
      } catch (error) {
        setMessage(`Папка «${directory.name}» выбрана, но сохранить доступ не удалось: ${error.message}. После перезапуска выберите её снова.`);
      }
    } catch (error) {
      if (error?.name !== 'AbortError') setMessage('Не удалось выбрать папку: ' + error.message);
    }
    render();
  }

  async function clearFolder() {
    runtime.folderRevision++;
    runtime.folder = null;
    runtime.folderExpected = false;
    runtime.folderName = '';
    runtime.folderPermission = 'unknown';
    runtime.folderRestoring = false;
    GM_setValue(FOLDER_INFO_KEY, { selected: false, name: '' });
    try { await folderDB('delete'); }
    catch (error) { console.warn('[FDM2] Не удалось очистить сохранённую папку:', error); }
    setMessage('Папка сброшена. Файлы будут сохраняться через браузер.');
    render();
  }

  async function diagnose() {
    const books = pageBooks();
    const selected = books.filter(x => x.checked).length;
    const formats = books.filter(x => x.formats.length).length;
    const sample = books.find(x => x.formats.length)?.formats[0];
    if (!sample) {
      setMessage(`Диагностика: найдено ${books.length} книг, ${selected} отмечено, ${formats} со ссылками. Проверить сеть невозможно: нет ссылки на книгу.`);
      return;
    }
    setMessage(`Диагностика: ${books.length} книг, ${selected} отмечено, ${formats} со ссылками; проверяю доступность загрузки…`);
    try {
      const response = await new Promise((resolve, reject) => {
        GM_xmlhttpRequest({ method: 'HEAD', url: sample.url, timeout: 12000,
          onload: resolve, onerror: () => reject(Error('ошибка сети')),
          ontimeout: () => reject(Error('тайм-аут 12 сек')),
          onabort: () => reject(Error('запрос отменён')) });
      });
      const target = safeRedirectTarget(response.finalUrl || sample.url);
      const redirectNote = target && target.origin !== location.origin
        ? ` Файл перенаправлен на ${target.hostname} — это нормально, если сервер выдаёт книгу.` : '';
      setMessage(`Диагностика: ${books.length} книг, ${selected} отмечено, ${formats} со ссылками; HTTP ${response.status} (HEAD).${redirectNote} ${[405,501].includes(response.status) ? 'Сервер не поддерживает HEAD, это не доказывает сбой скачивания.' : response.status >= 400 ? 'Ошибка ответа сервера.' : 'Сервер отвечает; фактический GET не проверялся.'}`);
    } catch (error) { setMessage(`Диагностика: ${books.length} книг, ${selected} отмечено, ${formats} со ссылками; проверка соединения: ${error.message}.`); }
  }

  function element(tag, className = '', value) {
    const item = document.createElement(tag);
    if (className) item.className = className;
    if (value !== undefined) item.textContent = String(value);
    return item;
  }

  function control(label, node) {
    const wrapper = element('label', 'fdm-control');
    wrapper.append(element('span', '', label), node);
    return wrapper;
  }

  function button(label, action) {
    const btn = element('button', 'fdm-btn', label);
    btn.type = 'button';
    btn.addEventListener('click', action);
    return btn;
  }

  function select(options, value) {
    const node = element('select', 'fdm-select');
    for (const [key, label] of options) {
      const option = element('option', '', label);
      option.value = key;
      node.appendChild(option);
    }
    node.value = String(value);
    node.addEventListener('change', saveSettings);
    return node;
  }

  function checkbox(checked) {
    const input = document.createElement('input');
    input.type = 'checkbox'; input.checked = !!checked;
    input.addEventListener('change', saveSettings);
    return input;
  }

  function icon(name) {
    const paths = {
      download: 'M12 3v12m-5-5 5 5 5-5M4 16v4h16v-4',
      folder: 'M3 7V5h6l2 2h10v13H3z',
      settings: 'M4 6h16M4 12h16M4 18h16M8 3v6m8 0v6M9 15v6',
      chevron: 'm6 9 6 6 6-6'
    };
    const svg = document.createElementNS('http://www.w3.org/2000/svg', 'svg');
    svg.setAttribute('viewBox', '0 0 24 24');
    svg.setAttribute('class', 'fdm-icon');
    svg.setAttribute('fill', 'none');
    svg.setAttribute('stroke', 'currentColor');
    svg.setAttribute('stroke-width', '1.7');
    svg.setAttribute('stroke-linecap', 'round');
    svg.setAttribute('stroke-linejoin', 'round');
    svg.setAttribute('aria-hidden', 'true');
    svg.setAttribute('focusable', 'false');
    const path = document.createElementNS('http://www.w3.org/2000/svg', 'path');
    path.setAttribute('d', paths[name]);
    svg.appendChild(path);
    return svg;
  }

  function renderInterface() {
    const style = document.createElement('style');
    style.textContent = `
      #fdm-panel{--fdm-ink:#233c3b;--fdm-muted:#617370;--fdm-edge:#dbe5e1;--fdm-bg:#fff;--fdm-pale:#f5f8f6;
        --fdm-accent:#196b59;--fdm-hover:#125543;--fdm-tint:#e9f4ef;--fdm-track:#e5ede9;--fdm-error:#a33535;--fdm-warn:#8a5a00;--fdm-warn-bg:#fff6df;
        color-scheme:light;color:var(--fdm-ink);margin:16px 0 22px;max-width:860px;min-width:0;
        font:14px/1.5 system-ui,-apple-system,Segoe UI,Arial,sans-serif;background:var(--fdm-bg);
        border:1px solid var(--fdm-edge);border-radius:18px;box-shadow:0 6px 24px #20382e0a;position:relative}
      #fdm-panel *{box-sizing:border-box}
      #fdm-panel button,#fdm-panel select,#fdm-panel summary{font:inherit;letter-spacing:normal;text-transform:none}
      #fdm-panel :is(button,select,summary,input):focus-visible{outline:3px solid #76b6a0;outline-offset:3px}
      #fdm-panel :is(button,select,input):disabled{opacity:.5;cursor:not-allowed}
      #fdm-panel button:not(:disabled){cursor:pointer}
      #fdm-panel .fdm-top{display:flex;align-items:center;justify-content:space-between;gap:16px;padding:20px 22px 16px}
      #fdm-panel .fdm-brand{display:flex;align-items:center;gap:12px;min-width:0}
      #fdm-panel .fdm-top-actions{display:flex;align-items:center;gap:10px;flex-wrap:wrap;justify-content:flex-end}
      #fdm-panel .fdm-mini-status{font-size:12px;color:var(--fdm-muted);font-variant-numeric:tabular-nums}
      #fdm-panel:not(.fdm-collapsed) .fdm-mini-status,#fdm-panel.fdm-collapsed .fdm-select-all{display:none}
      #fdm-panel.fdm-collapsed>:not(.fdm-top){display:none!important}
      #fdm-panel.fdm-collapsed .fdm-top{padding-bottom:20px}
      .fdm-done::after{content:" ✓";color:#2e8b57;font-weight:700}
      #fdm-panel .fdm-brand-copy{min-width:0}
      #fdm-panel .fdm-icon{width:20px;height:20px;flex-shrink:0;display:block}
      #fdm-panel .fdm-mark{display:grid;place-items:center;background:var(--fdm-tint);color:var(--fdm-accent);
        width:40px;height:40px;flex-shrink:0;border-radius:12px}
      #fdm-panel .fdm-mark .fdm-icon{width:23px;height:23px}
      #fdm-panel .fdm-heading{font-weight:720;font-size:15px;line-height:1.3;overflow-wrap:anywhere}
      #fdm-panel .fdm-version{font-size:11px;color:var(--fdm-muted);margin-top:3px}
      #fdm-panel .fdm-toolbar{display:flex;gap:12px;align-items:end;padding:0 22px 20px;flex-wrap:wrap}
      #fdm-panel .fdm-field{display:flex;flex-direction:column;gap:6px;min-width:0;margin:0}
      #fdm-panel .fdm-field>span{color:var(--fdm-muted);font-size:12px;font-weight:550}
      #fdm-panel .fdm-select{height:40px;min-height:40px;width:100%;border:1px solid var(--fdm-edge);
        background:var(--fdm-bg);color:var(--fdm-ink);padding:7px 10px;border-radius:10px;font-size:13px}
      #fdm-panel .fdm-format-wrap{width:110px}
      #fdm-panel .fdm-mode-wrap{flex:1;min-width:150px;max-width:270px}
      #fdm-panel .fdm-primary{border:1px solid transparent;border-radius:10px;padding:8px 23px;min-height:40px;
        background:var(--fdm-accent);color:#fff;font-size:13px;font-weight:650;white-space:nowrap}
      #fdm-panel .fdm-primary:not(:disabled):hover{background:var(--fdm-hover)}
      #fdm-panel .fdm-btn{border:1px solid var(--fdm-edge);background:var(--fdm-bg);color:var(--fdm-ink);
        border-radius:9px;padding:7px 11px;min-height:34px;font-size:12px}
      #fdm-panel .fdm-btn:not(:disabled):hover{background:var(--fdm-tint)}
      #fdm-panel .fdm-text-btn{border:0;border-radius:8px;background:transparent;color:var(--fdm-accent);
        padding:7px 4px;min-height:34px;font-weight:600;font-size:12px;white-space:nowrap}
      #fdm-panel .fdm-text-btn:not(:disabled):hover{text-decoration:underline}
      #fdm-panel .fdm-small-actions{display:flex;align-items:center;gap:8px;margin-left:auto;flex-wrap:wrap}
      #fdm-panel .fdm-subrow{display:flex;align-items:center;gap:12px;justify-content:space-between;flex-wrap:wrap;
        padding:13px 22px;background:var(--fdm-pale);border-top:1px solid var(--fdm-edge)}
      #fdm-panel .fdm-folder{min-width:0;display:flex;align-items:center;gap:11px;font-size:12px;flex:1}
      #fdm-panel .fdm-folder-icon{color:var(--fdm-muted);flex-shrink:0}
      #fdm-panel .fdm-folder-name{font-weight:600;overflow-wrap:anywhere}
      #fdm-panel .fdm-folder-hint{font-size:11px;color:var(--fdm-muted);margin-top:2px}
      #fdm-panel .fdm-mini{padding:6px 10px}
      #fdm-panel .fdm-settings{margin:0;border-top:1px solid var(--fdm-edge)}
      #fdm-panel .fdm-settings>summary{list-style:none;cursor:pointer;display:flex;align-items:center;
        justify-content:space-between;padding:14px 22px;font-size:12px;font-weight:600;color:var(--fdm-muted);border-radius:0 0 18px 18px}
      #fdm-panel summary::-webkit-details-marker{display:none}
      #fdm-panel .fdm-summary-label{display:flex;gap:10px;align-items:center}
      #fdm-panel .fdm-summary-label .fdm-icon{width:17px;height:17px}
      #fdm-panel .fdm-chevron{transition:transform .18s;width:16px;height:16px}
      #fdm-panel details[open]>.fdm-settings-summary .fdm-chevron{transform:rotate(180deg)}
      #fdm-panel .fdm-settings-body{border-top:1px solid var(--fdm-edge);padding:20px 22px;background:var(--fdm-pale);border-radius:0 0 18px 18px}
      #fdm-panel .fdm-settings-groups{display:grid;grid-template-columns:1fr 1fr;gap:24px}
      #fdm-panel .fdm-setting-group{margin:0;padding:0;border:0;min-width:0}
      #fdm-panel .fdm-setting-group>legend{float:none;width:100%;margin:0 0 14px;padding:0;color:var(--fdm-ink);font-size:13px;font-weight:650}
      #fdm-panel .fdm-settings-grid{display:grid;grid-template-columns:1fr 1fr;gap:12px}
      #fdm-panel .fdm-checks{display:flex;flex-direction:column;gap:9px;margin-top:14px}
      #fdm-panel .fdm-check{display:flex;align-items:flex-start;gap:9px;min-height:24px;color:var(--fdm-ink);font-size:12px;margin:0;line-height:1.5}
      #fdm-panel .fdm-check input{accent-color:var(--fdm-accent);margin:3px 0 0;flex-shrink:0;width:15px;height:15px}
      #fdm-panel .fdm-advanced-actions{display:flex;align-items:center;flex-wrap:wrap;gap:8px;margin-top:20px;padding-top:16px;border-top:1px solid var(--fdm-edge)}
      #fdm-panel .fdm-job{border-top:1px solid var(--fdm-edge);padding:17px 22px;background:var(--fdm-bg)}
      #fdm-panel .fdm-job-head{display:flex;align-items:center;justify-content:space-between;gap:10px;flex-wrap:wrap}
      #fdm-panel .fdm-job-title{font-weight:650;font-size:13px}
      #fdm-panel .fdm-job-stats{font-size:12px;color:var(--fdm-muted);margin:10px 0}
      #fdm-panel .fdm-bar{height:6px;background:var(--fdm-track);border-radius:20px;overflow:hidden}
      #fdm-panel .fdm-fill{height:100%;width:0;background:var(--fdm-accent);border-radius:inherit;transition:width .15s linear}
      #fdm-panel .fdm-current{margin-top:14px;padding:11px 13px;background:var(--fdm-pale);border:1px solid var(--fdm-edge);border-radius:10px}
      #fdm-panel .fdm-current-head{display:flex;align-items:baseline;gap:10px;min-width:0;font-size:12px;flex-wrap:wrap}
      #fdm-panel .fdm-current-label{color:var(--fdm-muted);flex-shrink:0;font-size:11px}
      #fdm-panel .fdm-current-title{flex:1;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;font-weight:550}
      #fdm-panel .fdm-current-percent{color:var(--fdm-accent);flex-shrink:0;font-variant-numeric:tabular-nums}
      #fdm-panel .fdm-current .fdm-bar{height:3px;margin-top:9px}
      #fdm-panel .fdm-queue-actions{display:flex;gap:6px;flex-wrap:wrap;align-items:center}
      #fdm-panel .fdm-menu{position:relative;font-size:12px}
      #fdm-panel .fdm-menu>summary{cursor:pointer;list-style:none;padding:7px 10px;border:1px solid var(--fdm-edge);border-radius:9px;min-height:34px}
      #fdm-panel .fdm-menu-items{position:absolute;right:0;top:calc(100% + 5px);z-index:5;background:var(--fdm-bg);
        border:1px solid var(--fdm-edge);border-radius:12px;box-shadow:0 8px 24px #0002;padding:5px;min-width:190px;display:flex;flex-direction:column;gap:3px}
      #fdm-panel .fdm-menu-items .fdm-btn{text-align:left;border:0;width:100%}
      #fdm-panel .fdm-errors-box{margin-top:12px}
      #fdm-panel .fdm-errors-box>summary{font-size:12px;cursor:pointer;color:var(--fdm-error);font-weight:600}
      #fdm-panel .fdm-errors{max-height:170px;overflow:auto;padding-left:20px;font-size:12px;color:var(--fdm-error);overflow-wrap:anywhere}
      #fdm-panel .fdm-message{display:block;padding:12px 22px;border-top:1px solid var(--fdm-edge);font-size:12px;color:var(--fdm-muted);overflow-wrap:anywhere}
      #fdm-panel .fdm-notice{margin-top:10px;padding:8px 11px;font-size:12px;color:var(--fdm-ink);background:var(--fdm-warn-bg);
        border:1px solid var(--fdm-warn);border-radius:10px;overflow-wrap:anywhere}
      #fdm-panel .fdm-notes{display:block;padding:12px 22px;border-top:1px solid var(--fdm-edge);font-size:12px;color:var(--fdm-ink);
        background:var(--fdm-warn-bg);border-left:3px solid var(--fdm-warn);overflow-wrap:anywhere}
      #fdm-panel .fdm-notes>div+div{margin-top:4px}
      #fdm-panel .fdm-catalog{background:var(--fdm-pale);border-color:var(--fdm-edge)}
      #fdm-panel .fdm-current-attempt{color:var(--fdm-warn);flex-shrink:0;font-size:11px}
      #fdm-panel .fdm-message:empty,#fdm-panel .fdm-redirect:empty{display:none}
      #fdm-panel .fdm-redirect{font-size:11px;color:var(--fdm-muted);margin-top:10px;overflow-wrap:anywhere}
      #fdm-panel [hidden]{display:none!important}
      @media(max-width:640px){#fdm-panel .fdm-settings-groups{grid-template-columns:1fr;gap:22px}
        #fdm-panel .fdm-setting-group+.fdm-setting-group{border-top:1px solid var(--fdm-edge);padding-top:18px}
        #fdm-panel .fdm-top{padding:16px;align-items:flex-start;gap:10px;flex-wrap:wrap}
        #fdm-panel .fdm-toolbar{padding:0 16px 16px;gap:10px}
        #fdm-panel .fdm-subrow,#fdm-panel .fdm-job,#fdm-panel .fdm-message,#fdm-panel .fdm-notes,#fdm-panel .fdm-settings>summary,#fdm-panel .fdm-settings-body{padding-left:16px;padding-right:16px}
        #fdm-panel .fdm-mode-wrap{max-width:none;min-width:120px}#fdm-panel .fdm-primary{flex:1}
        #fdm-panel .fdm-small-actions{margin-left:0}#fdm-panel .fdm-menu-items{right:auto;left:0}}
      @media(prefers-color-scheme:dark){#fdm-panel{color-scheme:dark;--fdm-ink:#e1ebe6;--fdm-muted:#a3b6ac;
        --fdm-edge:#35463e;--fdm-bg:#1d2823;--fdm-pale:#23312a;--fdm-accent:#91cbb0;--fdm-hover:#acdbc4;
        --fdm-tint:#2c4236;--fdm-track:#364b3f;--fdm-error:#f0aaa6;--fdm-warn:#e6c26b;--fdm-warn-bg:#3a3321;box-shadow:0 6px 24px #0002}
        #fdm-panel .fdm-primary{color:#162b21}}
      @media(prefers-reduced-motion:reduce){#fdm-panel .fdm-fill,#fdm-panel .fdm-chevron{transition:none}}
    `;
    document.head.appendChild(style);

    const panel = element('section');
    panel.id = 'fdm-panel';
    panel.setAttribute('aria-label', 'Flibusta Download Manager');
    const top = element('div', 'fdm-top');
    const brand = element('div', 'fdm-brand');
    const mark = element('span', 'fdm-mark'); mark.append(icon('download'));
    const textBrand = element('div', 'fdm-brand-copy');
    textBrand.append(element('div', 'fdm-heading', 'Flibusta Download Manager'),
      element('div', 'fdm-version', `Версия ${VERSION}`));
    brand.append(mark, textBrand);
    const selectionButton = button('Отметить все', () => {
      const boxes = runtime.bookBoxes;
      setBookSelection(!boxes.length ? false : !boxes.every(box => box.checked));
    });
    selectionButton.classList.replace('fdm-btn', 'fdm-text-btn');
    selectionButton.classList.add('fdm-select-all');
    const miniStatus = element('span', 'fdm-mini-status');
    miniStatus.setAttribute('aria-live', 'polite');
    const collapseButton = button('', () => setCollapsed(!panel.classList.contains('fdm-collapsed')));
    collapseButton.classList.replace('fdm-btn', 'fdm-text-btn');
    function setCollapsed(on, save = true) {
      panel.classList.toggle('fdm-collapsed', on);
      collapseButton.textContent = on ? 'Развернуть' : 'Свернуть';
      collapseButton.setAttribute('aria-expanded', String(!on));
      if (save) { try { GM_setValue(COLLAPSED_KEY, on); } catch (error) { console.warn('[FDM2] Cannot save panel state:', error); } }
    }
    const topActions = element('div', 'fdm-top-actions');
    topActions.append(miniStatus, selectionButton, collapseButton);
    top.append(brand, topActions);
    panel.append(top);
    setCollapsed(!!readStored(COLLAPSED_KEY, false), false);

    const toolbar = element('div', 'fdm-toolbar');
    const format = select(FORMATS.map(f => [f, f === 'other' ? 'Любой' : f.toUpperCase()]), settings.format);
    const formatField = element('label', 'fdm-field fdm-format-wrap');
    formatField.append(element('span', '', 'Формат'), format);
    const selectedMode = select([['checked', 'Отмеченные'], ['all', 'Все книги']], runtime.selectedMode);
    selectedMode.addEventListener('change', () => { runtime.selectedMode = selectedMode.value; render(); });
    const modeField = element('label', 'fdm-field fdm-mode-wrap');
    modeField.append(element('span', '', 'Что скачать'), selectedMode);
    modeField.hidden = isBook;
    const start = button('Скачать', () => prepare(runtime.selectedMode));
    start.classList.replace('fdm-btn', 'fdm-primary');
    toolbar.append(formatField, modeField, start);
    panel.append(toolbar);

    const subrow = element('div', 'fdm-subrow');
    const folder = element('div', 'fdm-folder');
    const folderIcon = element('span', 'fdm-folder-icon'); folderIcon.append(icon('folder'));
    folder.append(folderIcon);
    const folderInfo = element('div');
    const folderStatus = element('div', 'fdm-folder-name');
    const folderHint = element('div', 'fdm-folder-hint');
    folderInfo.append(folderStatus, folderHint);
    folder.append(folderInfo);
    const miniActions = element('div', 'fdm-small-actions');
    const folderButton = button('Изменить папку', selectFolder);
    folderButton.classList.add('fdm-mini');
    const folderGrantButton = button('Разрешить доступ', grantFolder);
    folderGrantButton.classList.add('fdm-mini');
    miniActions.append(folderGrantButton, folderButton);
    subrow.append(folder, miniActions);
    panel.append(subrow);

    const queue = element('section', 'fdm-job');
    queue.setAttribute('aria-label', 'Состояние загрузок');
    const jobHead = element('div', 'fdm-job-head');
    const jobTitle = element('div', 'fdm-job-title');
    const queueActions = element('div', 'fdm-queue-actions');
    const pauseButton = button('Пауза', pause);
    const resumeButton = button('Продолжить', resume);
    const retryButton = button('Повторить неудачные', retryFailed);
    const menu = element('details', 'fdm-menu');
    const menuSummary = element('summary', '', 'Ещё ···');
    const menuItems = element('div', 'fdm-menu-items');
    const stopButton = button('Отменить очередь', () => { stop(); menu.open = false; });
    const exportButton = button('Сохранить отчёт', () => { exportReport(); menu.open = false; });
    menuItems.append(stopButton, exportButton);
    menu.append(menuSummary, menuItems);
    queueActions.append(pauseButton, resumeButton, retryButton, menu);
    jobHead.append(jobTitle, queueActions);
    const stats = element('div', 'fdm-job-stats');
    const catalog = element('div', 'fdm-notice fdm-catalog');
    catalog.setAttribute('role', 'status');
    const cooldown = element('div', 'fdm-notice fdm-cooldown');
    cooldown.setAttribute('role', 'status');
    const bar = element('div', 'fdm-bar');
    bar.setAttribute('role', 'progressbar');
    bar.setAttribute('aria-label', 'Прогресс загрузки книг');
    bar.setAttribute('aria-valuemin', '0');bar.setAttribute('aria-valuemax', '100');
    const fill = element('div', 'fdm-fill'); bar.append(fill);
    const errorBox = element('details', 'fdm-errors-box');
    const errorSummary = element('summary', '', 'Ошибки загрузки');
    const errorList = element('ol', 'fdm-errors');
    errorBox.append(errorSummary, errorList);
    const redirectStatus = element('div', 'fdm-redirect');
    const current = element('div', 'fdm-current');
    const currentHead = element('div', 'fdm-current-head');
    const currentTitle = element('span', 'fdm-current-title');
    const currentPercent = element('span', 'fdm-current-percent');
    const currentAttempt = element('span', 'fdm-current-attempt');
    currentHead.append(element('span', 'fdm-current-label', 'Сейчас'), currentTitle, currentAttempt, currentPercent);
    const currentBar = element('div', 'fdm-bar');
    currentBar.setAttribute('role', 'progressbar');
    currentBar.setAttribute('aria-label', 'Загрузка текущей книги');
    currentBar.setAttribute('aria-valuemin', '0');
    currentBar.setAttribute('aria-valuemax', '100');
    const currentFill = element('div', 'fdm-fill'); currentBar.append(currentFill);
    current.append(currentHead, currentBar);
    queue.append(jobHead, stats, catalog, cooldown, bar, current, errorBox, redirectStatus);
    panel.append(queue);

    const optionsDetails = element('details', 'fdm-settings');
    const optionsSummary = element('summary', 'fdm-settings-summary');
    const labelSummary = element('span', 'fdm-summary-label');
    labelSummary.append(icon('settings'), element('span', '', 'Дополнительные настройки'));
    const chevron = icon('chevron'); chevron.classList.add('fdm-chevron');
    optionsSummary.append(labelSummary, chevron);
    const optionsBody = element('div', 'fdm-settings-body');
    const optionsGroups = element('div', 'fdm-settings-groups');
    const savingGroup = element('fieldset', 'fdm-setting-group');
    savingGroup.append(element('legend', '', 'Сохранение'));
    const downloadGroup = element('fieldset', 'fdm-setting-group');
    downloadGroup.append(element('legend', '', 'Загрузка'));
    const downloadGrid = element('div', 'fdm-settings-grid');
    const naming = select([['original', 'Оригинальное (с сервера)'], ['readable', 'Название книги и номер']], settings.naming);
    const fallback = checkbox(settings.fallback);
    const verify = checkbox(settings.verify);
    const allPages = checkbox(settings.allPages);
    const askEach = checkbox(settings.askEach);
    const skipDownloaded = checkbox(settings.skipDownloaded);
    const parallel = select([['1', '1'], ['2', '2']], settings.parallel);
    const delay = select([['1000', '1 c'], ['1200', '1,2 c'], ['2000', '2 c'], ['3000', '3 c'], ['5000', '5 c']], settings.delay);
    const retries = select([['0', '0'], ['1', '1'], ['2', '2'], ['3', '3'], ['5', '5']], settings.retries);
    const idle = select(IDLE_CHOICES.map(n => [String(n), n + ' c']), settings.idle);
    function settingSelect(labelText, node) {
      const field = element('label', 'fdm-field');
      field.append(element('span', '', labelText), node);
      return field;
    }
    function settingCheckbox(labelText, node) {
      const field = element('label', 'fdm-check');
      field.append(node, element('span', '', labelText));
      return field;
    }
    const savingChecks = element('div', 'fdm-checks');
    savingChecks.append(
      settingCheckbox('Проверять содержимое файлов', verify),
      settingCheckbox('Спрашивать место для каждого файла', askEach)
    );
    savingGroup.append(settingSelect('Имя файла', naming), savingChecks);
    downloadGrid.append(
      settingSelect('Одновременно', parallel),
      settingSelect('Пауза между файлами', delay),
      settingSelect('Повторы при ошибке', retries),
      settingSelect('Обрыв без данных', idle)
    );
    const downloadChecks = element('div', 'fdm-checks');
    downloadChecks.append(
      settingCheckbox('Резервный формат, если выбранный недоступен', fallback),
      settingCheckbox('Остальные страницы каталога (макс. 30)', allPages),
      settingCheckbox('Пропускать уже скачанные (по истории)', skipDownloaded)
    );
    downloadGroup.append(downloadGrid, downloadChecks);
    optionsGroups.append(savingGroup, downloadGroup);
    const moreActions = element('div', 'fdm-advanced-actions');
    const diagnosticButton = button('Диагностика сайта', diagnose);
    const resetFolderButton = button('Сбросить папку', clearFolder);
    const clearHistoryButton = button('Очистить историю', clearHistory);
    moreActions.append(diagnosticButton, resetFolderButton, clearHistoryButton);
    optionsBody.append(optionsGroups, moreActions);
    optionsDetails.append(optionsSummary, optionsBody);
    panel.append(optionsDetails);

    const notes = element('div', 'fdm-notes');
    notes.setAttribute('role', 'status');
    notes.setAttribute('aria-label', 'Итоги подготовки');
    panel.append(notes);
    const message = element('div', 'fdm-message');
    message.setAttribute('role', 'status');
    message.setAttribute('aria-live', 'polite');
    panel.append(message);
    if (title) title.insertAdjacentElement('afterend', panel); else main.prepend(panel);
    ui = { panel, miniStatus, collapseButton, format, naming, fallback, verify, allPages, askEach, skipDownloaded, parallel, delay, retries, idle,
      selectedMode, selectionButton, start, folderButton, folderGrantButton, resetFolderButton, clearHistoryButton,
      diagnosticButton, pauseButton, resumeButton, stopButton, retryButton, exportButton,
      queue, jobTitle, stats, bar, fill, current, currentTitle, currentPercent, currentAttempt, currentBar, currentFill, catalog, cooldown, notes, message, errorBox, errorSummary, errorList, folderStatus, folderHint, redirectStatus };
  }

  function render() {
    if (!ui) return;
    const counts = countJobs();
    const total = state?.jobs.length || 0;
    const finished = counts.done + counts.failed + counts.skipped;
    const busy = queueBusy();
    const bookTotal = runtime.bookBoxes.length;
    const selectedCount = runtime.bookBoxes.filter(box => box.checked).length;
    const toDownload = runtime.selectedMode === 'checked' ? selectedCount : runtime.bookCount;
    ui.selectionButton.hidden = bookTotal === 0;
    ui.selectionButton.textContent = selectedCount === bookTotal && bookTotal > 0
      ? `Снять отметки · ${selectedCount}/${bookTotal}` : `Отметить все · ${selectedCount}/${bookTotal}`;
    ui.selectionButton.disabled = busy;
    ui.start.disabled = busy || (runtime.selectedMode === 'checked' ? selectedCount === 0 : (runtime.bookCount === 0 && !settings.allPages));
    const displayedTotal = runtime.selectedMode === 'all' && settings.allPages ? `${toDownload}+` : String(toDownload);
    ui.start.textContent = runtime.preparing ? 'Подготавливаю…' : `Скачать (${displayedTotal})`;
    ui.selectedMode.disabled = busy;
    ui.folderButton.disabled = busy;
    ui.folderGrantButton.hidden = !runtime.folderExpected || !runtime.folder || runtime.folderPermission === 'granted';
    ui.folderGrantButton.disabled = busy || !runtime.folder || runtime.folderRestoring;
    ui.resetFolderButton.disabled = busy || !runtime.folderExpected;
    ui.clearHistoryButton.disabled = busy;
    for (const ctl of [ui.format, ui.naming, ui.fallback, ui.verify, ui.parallel, ui.delay, ui.retries, ui.idle, ui.allPages, ui.askEach, ui.skipDownloaded]) ctl.disabled = busy;

    ui.folderStatus.textContent = runtime.folderExpected
      ? `Папка: ${runtime.folderName || 'неизвестно'}`
      : settings.askEach ? 'Папка: спрашивать для каждого файла' : 'Папка: загрузки браузера';
    ui.folderHint.textContent = runtime.folderExpected
      ? runtime.folderRestoring ? 'Восстанавливаю доступ…'
        : runtime.folderPermission === 'granted' ? 'Выбрана и доступна для записи'
        : runtime.folder ? 'Нужно разрешить запись' : 'Нужно выбрать заново'
      : 'Можно изменить место сохранения';

    ui.queue.hidden = !(state?.jobs?.length || runtime.preparing);
    const finishedPercent = total ? Math.round(finished / total * 100) : 0;
    ui.jobTitle.textContent = runtime.preparing ? 'Подготовка очереди…' :
      counts.active ? `Загружается ${counts.active} ${counts.active === 1 ? 'книга' : 'книги'}` :
      counts.queued ? state?.paused ? 'Загрузка приостановлена' : 'Книги ожидают загрузки' :
      counts.failed ? 'Завершено с ошибками' : 'Загрузка завершена';
    ui.stats.textContent = `Готово ${counts.done} из ${total} · В очереди ${counts.queued} · Ошибки ${counts.failed}` +
      (state?.skippedByFormat ? ` · Без формата ${state.skippedByFormat}` : '') +
      (state?.skippedByHistory ? ` · Скачано ранее ${state.skippedByHistory}` : '');
    const left = state && !state.paused ? timeLeft(counts.queued + counts.active) : null;
    if (left) ui.stats.textContent += ` · Осталось ≈ ${left}`;
    // Свёрнутая панель показывает только итог: очередь или сколько книг к скачиванию.
    ui.miniStatus.textContent = total ? `${finished}/${total}` + (counts.active ? ' ⬇' : '') + (counts.failed ? ` · ошибок ${counts.failed}` : '')
      : `к скачиванию ${displayedTotal}`;
    ui.fill.style.width = finishedPercent + '%';
    ui.bar.setAttribute('aria-valuenow', String(finishedPercent));
    ui.pauseButton.hidden = !state || state.paused || !busy || runtime.preparing;
    ui.pauseButton.disabled = !state || state.paused || !busy;
    ui.resumeButton.hidden = !state || !state.paused || !counts.queued;
    ui.resumeButton.disabled = !state || !state.paused || !counts.queued || runtime.preparing;
    ui.retryButton.hidden = !counts.failed;
    ui.retryButton.disabled = !state || !counts.failed || runtime.active > 0 || runtime.preparing;
    ui.stopButton.disabled = !runtime.preparing && (!state || !counts.queued);
    ui.exportButton.disabled = !state || !total;
    ui.errorBox.hidden = !counts.failed;
    ui.errorSummary.textContent = `Ошибки загрузки (${counts.failed}) · подробнее`;
    // Don't discard the opened details element on every progress event.
    const failed = counts.failedJobs;
    const errorSignature = JSON.stringify([failed.length, failed.slice(0, 25).map(job => [job.id, job.name, job.error])]);
    if (errorSignature !== runtime.errorSignature) {
      runtime.errorSignature = errorSignature;
      ui.errorList.replaceChildren();
      for (const job of failed.slice(0, 25)) ui.errorList.appendChild(element('li', '', `${job.name}: ${job.error}`));
      if (failed.length > 25) ui.errorList.appendChild(element('li', '', `Ещё ${failed.length - 25} записей — в отчёте`));
    }
    ui.redirectStatus.textContent = runtime.lastRemoteHost && runtime.lastRemoteHost !== location.hostname
      ? `Файловый сервер: ${runtime.lastRemoteHost}` : '';
    // Notes of the last preparation stay until the next one starts.
    const notes = runtime.prepareNotes;
    const notesSignature = JSON.stringify(notes);
    if (notesSignature !== runtime.notesSignature) {
      runtime.notesSignature = notesSignature;
      ui.notes.replaceChildren(...notes.map(note => element('div', '', note)));
    }
    ui.notes.hidden = !notes.length;
    ui.catalog.hidden = !(runtime.preparing && runtime.catalogProgress);
    if (!ui.catalog.hidden) {
      ui.catalog.textContent = `Страницы каталога: ${runtime.catalogProgress.index} из ${runtime.catalogProgress.total}`;
    }
    // Shared pause after 429/503: counted down once a second while it lasts.
    const now = Date.now();
    const cooling = !!state && !state.paused && runtime.cooldownUntil > now;
    ui.cooldown.hidden = !cooling;
    if (cooling) {
      ui.cooldown.textContent = `Сервер просит подождать: осталось ${Math.ceil((runtime.cooldownUntil - now) / 1000)} с`;
      if (!runtime.cooldownTick) runtime.cooldownTick = setInterval(render, 1000);
    } else if (runtime.cooldownTick) {
      clearInterval(runtime.cooldownTick);
      runtime.cooldownTick = null;
    }
    const active = counts.firstActive;
    ui.current.hidden = !active;
    if (active) {
      const p = runtime.progress.get(active.id);
      const percent = p?.total > 0 ? Math.min(100, Math.max(0, Math.round(100 * p.loaded / p.total))) : null;
      ui.currentTitle.textContent = active.title;
      ui.currentTitle.title = active.title;
      ui.currentAttempt.hidden = !(active.attempts > 1);
      ui.currentAttempt.textContent = `попытка ${active.attempts} из ${(state.options.retries || 0) + 1}`;
      ui.currentPercent.textContent = percent !== null ? `${percent}%` : p?.loaded
        ? `${(p.loaded / 1048576).toFixed(1)} МиБ` : 'Ожидание…';
      ui.currentBar.hidden = percent === null;
      if (percent !== null) {
        ui.currentFill.style.width = percent + '%';
        ui.currentBar.setAttribute('aria-valuenow', String(percent));
      } else ui.currentBar.removeAttribute('aria-valuenow');
    }
    const fallbackNames = counts.fallbackNames;
    ui.message.textContent = (runtime.message || '') +
      (fallbackNames ? ` · Для ${fallbackNames} файлов сервер не сообщил оригинальное имя.` : '');
  }
})();
