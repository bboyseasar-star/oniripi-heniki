'use strict';

const $ = s => document.querySelector(s);
const $$ = s => Array.from(document.querySelectorAll(s));
const storage = (() => {
  const mem = new Map();
  return {
    get(k, d = null) { try { return localStorage.getItem(k) ?? d; } catch { return mem.get(k) ?? d; } },
    set(k, v) { try { localStorage.setItem(k, v); } catch { mem.set(k, v); } },
    del(k) { try { localStorage.removeItem(k); } catch { mem.delete(k); } }
  };
})();

let level = 1, qi = 0, score = 0, questions = [], current = null, hintsShown = 0, answered = false, focusField = null, reviewMode = false, reviews = [];
let graphAnimation = null, graphManualX = null, graphState = null;
const KEY = 'oniripi-heniki';

function gcd(a, b) { a = Math.abs(a); b = Math.abs(b); while (b) [a, b] = [b, a % b]; return a || 1; }
function frac(n, d = 1) { if (d < 0) { n = -n; d = -d; } const g = gcd(n, d); return { n: n / g, d: d / g }; }
function parseLatex(v) {
  v = String(v || '').trim().replace(/\s+/g, '').replace(/[−ー－]/g, '-');
  v = v.replace(/\\dfrac/g, '\\frac').replace(/\\left|\\right|\\,/g, '');
  let m = v.match(/^(-?)\\frac{?(-?\d+)}?{?(-?\d+)}?$/);
  if (m) return Number(m[3]) ? frac((m[1] ? -1 : 1) * Number(m[2]), Number(m[3])) : null;
  m = v.match(/^(-?\d+)\/(-?\d+)$/);
  if (m) return Number(m[2]) ? frac(Number(m[1]), Number(m[2])) : null;
  if (/^-?\d+(\.\d+)?$/.test(v)) {
    const n = Number(v);
    return Number.isInteger(n) ? frac(n) : frac(Math.round(n * 1000), 1000);
  }
  return null;
}
function parseRange(v, variable) {
  let s = String(v || '').trim().replace(/\s+/g, '').replace(/[−ー－]/g, '-');
  s = s.replace(/\\left|\\right|\\mleft|\\mright|\\,/g, '');
  s = s.replace(/\\leqq|\\leqslant|\\leq|\\le/g, '≤').replace(/≦/g, '≤');
  s = s.replace(new RegExp(`\\{${variable}\\}`, 'g'), variable);
  const parts = s.split('≤');
  if (parts.length !== 3 || parts[1] !== variable) return [null, null];
  return [parseLatex(parts[0]), parseLatex(parts[2])];
}
function same(a, b) { return a && b && a.n === b.n && a.d === b.d; }
function ansTex(q) {
  const t = HenikiQuestions.tex;
  if (q.type === 'A') return `\\( ${t(q.answers[0])}\\leqq y\\leqq ${t(q.answers[1])} \\)`;
  if (q.type === 'B') return `\\( ${t(q.answers[0])}\\leqq x\\leqq ${t(q.answers[1])} \\)`;
  if (q.type === 'C') return `\\( a=${t(q.answers[0])},\\ b=${t(q.answers[1])} \\)`;
  return `\\( ${t(q.answers[0])}\\leqq x\\leqq ${t(q.answers[1])},\\ ${t(q.answers[2])}\\leqq y\\leqq ${t(q.answers[3])} \\)`;
}
function setScreen(id) { $$('.screen').forEach(s => s.classList.remove('active')); $(id).classList.add('active'); }
function typeset() {
  if (window.MathJax?.typesetPromise) MathJax.typesetPromise();
  else window.addEventListener('mathjax-ready', typeset, { once: true });
}
function renderStart() {
  $('#high-score').textContent = Number(storage.get(`${KEY}-high-${level}`, 0)) || '--';
  const hist = JSON.parse(storage.get(`${KEY}-hist`, '[]'));
  $('#history-list').innerHTML = hist.length ? hist.slice(0, 20).map(h => `Lv.${h.level} ${h.score}点 ${h.passed ? '合格' : '復習'} / ${h.date}`).join('<br>') : 'まだ記録がないよ！';
}
function start(list = null) {
  qi = 0; score = 0; reviews = []; reviewMode = !!list; questions = list || HenikiQuestions.make(level); setScreen('#screen-quiz'); showQuestion();
}
function showQuestion() {
  current = questions[qi]; hintsShown = 0; answered = false; focusField = null; graphManualX = null;
  $('#level-tag').textContent = `Lv.${level}`; $('#q-counter').textContent = `Q ${qi + 1} / ${questions.length}`;
  $('#progress-fill').style.width = `${qi / questions.length * 100}%`; $('#score-display').textContent = `${score}点`;
  $('#question-label').innerHTML = current.label; $('#question-display').innerHTML = current.question; $('#question-extra').innerHTML = current.extra;
  $('#hint-list').innerHTML = ''; $('#hint-warning').classList.add('hidden');
  $('#feedback-box').className = 'feedback-box hidden'; $('#next-btn').classList.add('hidden'); $('#submit-btn').classList.remove('hidden'); $('#hint-btn').disabled = false;
  $('#response-row').classList.remove('has-feedback');
  renderAnswer(); redrawGraph(); typeset();
}
function mf(id, wide = false) {
  return `<div class="mf-container${wide ? ' range' : ''}"><math-field id="${id}" virtual-keyboard-mode="off"></math-field></div>`;
}
function renderAnswer() {
  const yLine = `<div class="answer-line">${mf('ans-y-range', true)}</div>`;
  const xLine = `<div class="answer-line">${mf('ans-x-range', true)}</div>`;
  const labeledYLine = `<div class="answer-line range-labeled"><span class="range-label range-label-y">\\( y \\) の変域</span>${mf('ans-y-range', true)}</div>`;
  const labeledXLine = `<div class="answer-line range-labeled"><span class="range-label range-label-x">\\( x \\) の変域</span>${mf('ans-x-range', true)}</div>`;
  const abLine = `<div class="answer-line">\\( a= \\) ${mf('ans-a')} \\( b= \\) ${mf('ans-b')}</div>`;
  $('#answer-grid').innerHTML = current.type === 'A' ? yLine : current.type === 'B' ? xLine : current.type === 'C' ? abLine : labeledXLine + labeledYLine;
  const isRangeQuestion = current.type !== 'C';
  $('#input-note').textContent = isRangeQuestion ? '※変域は「最小値≦文字≦最大値」まで入力してね。' : '※半角英数字で入力してね。分数は下のボタンが便利。';
  $('#le-key').classList.toggle('hidden', !isRangeQuestion);
  $$('math-field').forEach(el => {
    forceHalfWidthInput(el.id);
    el.addEventListener('focus', () => { focusField = el; });
  });
}
function forceHalfWidthInput(id) {
  const el = document.getElementById(id);
  if (!el) return;
  el.setAttribute('inputmode', 'latin');
  el.addEventListener('compositionend', ev => {
    const data = ev.data;
    if (!data) return;
    const converted = data.replace(/[０-９]/g, s => String.fromCharCode(s.charCodeAt(0) - 0xFEE0)).replace(/[－ー−]/g, '-').replace(/[／]/g, '/');
    el.value = '';
    el.insert(converted);
  });
}
function values() {
  const get = id => parseLatex(document.getElementById(id)?.value);
  if (current.type === 'A') return parseRange(document.getElementById('ans-y-range')?.value, 'y');
  if (current.type === 'B') return parseRange(document.getElementById('ans-x-range')?.value, 'x');
  if (current.type === 'C') return [get('ans-a'), get('ans-b')];
  return [
    ...parseRange(document.getElementById('ans-x-range')?.value, 'x'),
    ...parseRange(document.getElementById('ans-y-range')?.value, 'y')
  ];
}
function responseTex(got) {
  const t = f => f ? HenikiQuestions.tex(f) : '?';
  if (current.type === 'A') return `\\( ${t(got[0])}\\leqq y\\leqq ${t(got[1])} \\)`;
  if (current.type === 'B') return `\\( ${t(got[0])}\\leqq x\\leqq ${t(got[1])} \\)`;
  if (current.type === 'C') return `\\( a=${t(got[0])},\\ b=${t(got[1])} \\)`;
  return `\\( ${t(got[0])}\\leqq x\\leqq ${t(got[1])},\\ ${t(got[2])}\\leqq y\\leqq ${t(got[3])} \\)`;
}
function finishQuestion(ok, giveup = false) {
  answered = true;
  if (ok) score += Math.round(100 / questions.length);
  const fb = $('#feedback-box');
  fb.className = `feedback-box ${ok ? 'ok' : giveup ? 'giveup' : 'ng'} ${ok ? '' : 'pulse'}`;
  $('#response-row').classList.add('has-feedback');
  const got = values();
  fb.innerHTML = ok
    ? `正解！ グラフで端の対応も確認しよう。<br>正しい答え: ${ansTex(current)}`
    : `${giveup ? '答えを確認しました。' : 'おしい！もう一度復習しよう。'}<br>あなたの解答: ${responseTex(got)}<br>正しい答え: ${ansTex(current)}<br>計算: ${current.process}`;
  reviews.push({ q: current.question, ok, ans: ansTex(current), process: current.process, source: current });
  $('#score-display').textContent = `${score}点`; $('#submit-btn').classList.add('hidden'); $('#next-btn').classList.remove('hidden'); $('#hint-btn').disabled = true;
  redrawGraph(true); typeset();
}
function check() {
  if (answered) return;
  const got = values();
  const ok = got.length === current.answers.length && got.every((v, i) => same(v, current.answers[i]));
  finishQuestion(ok, false);
}
function hint() {
  if (answered) return;
  const lastHintIndex = current.hints.length - 1;
  if (hintsShown === lastHintIndex) {
    finishQuestion(false, true);
    const div = document.createElement('div');
    div.className = 'hint-item';
    div.innerHTML = `ヒント${hintsShown + 1}: ${current.hints[hintsShown]}`;
    $('#hint-list').appendChild(div);
    typeset();
    return;
  }
  const div = document.createElement('div');
  div.className = 'hint-item';
  div.innerHTML = `ヒント${hintsShown + 1}: ${current.hints[hintsShown]}`;
  $('#hint-list').appendChild(div);
  hintsShown++;
  $('#hint-warning').classList.toggle('hidden', hintsShown !== lastHintIndex);
  redrawGraph();
  typeset();
}
function next() { qi++; if (qi >= questions.length) result(); else showQuestion(); }
function result() {
  $('#progress-fill').style.width = '100%'; setScreen('#screen-result');
  const passed = score >= 80;
  $('#result-score').textContent = `${score}点`;
  $('#result-badge').textContent = passed ? ['変域マスター！', '逆転もバッチリ！', 'いい集中力！'][Math.floor(Math.random() * 3)] : 'まちがいだけ復習しよう';
  $('#review-list').innerHTML = reviews.map((r, i) => `<div class="review-item"><b>Q${i + 1} ${r.ok ? '正解' : '復習'}</b><br>正しい答え: ${r.ans}<br>${r.process}</div>`).join('');
  const wrong = reviews.filter(r => !r.ok).map(r => r.source);
  $('#review-wrong-btn').classList.toggle('hidden', wrong.length === 0);
  $('#review-wrong-btn').onclick = () => start(wrong);
  const hsKey = `${KEY}-high-${level}`;
  storage.set(hsKey, String(Math.max(score, Number(storage.get(hsKey, 0)))));
  const hist = JSON.parse(storage.get(`${KEY}-hist`, '[]'));
  hist.unshift({ level, score, passed, date: new Date().toLocaleString('ja-JP') });
  storage.set(`${KEY}-hist`, JSON.stringify(hist.slice(0, 20)));
  if (passed && window.confetti) confetti({ particleCount: 120, spread: 70, origin: { y: 0.62 } });
  typeset();
}
function insertKey(cmd) {
  if (!focusField) focusField = document.querySelector('math-field');
  if (!focusField) return;
  if (cmd === 'clear') { focusField.value = ''; focusField.focus(); return; }
  const latex = cmd === 'frac' ? '\\frac{#0}{#?}' : cmd === 'le' ? '\\leqq ' : '-';
  try { focusField.executeCommand(['insert', latex]); } catch { try { focusField.insert(latex); } catch {} }
  focusField.focus();
}
function redrawGraph(forceFull = false) {
  if (!current) return;
  if (graphAnimation) cancelAnimationFrame(graphAnimation);
  const reveal = forceFull || answered || current.type === 'D' ? 3 : hintsShown;
  drawGraph(current, reveal);
  if (current.type === 'A' && reveal >= 1 && reveal < 3 && !document.hidden) {
    const animate = now => {
      if (!current || answered || current.type !== 'A' || hintsShown < 1 || hintsShown >= 3 || document.hidden) return;
      drawGraph(current, reveal, now);
      graphAnimation = requestAnimationFrame(animate);
    };
    graphAnimation = requestAnimationFrame(animate);
  }
}
function niceStep(range) {
  if (range <= 12) return 1;
  if (range <= 24) return 2;
  if (range <= 50) return 5;
  return 10;
}
function niceBounds(lo, hi, padRatio = 0.18) {
  if (lo === hi) { lo -= 4; hi += 4; }
  const span = hi - lo;
  const pad = Math.max(2, span * padRatio);
  lo -= pad; hi += pad;
  const step = niceStep(hi - lo);
  return [Math.floor(lo / step) * step, Math.ceil(hi / step) * step, step];
}
function graphBounds(q, w, h) {
  const ys = [0, HenikiQuestions.val(q.y1), HenikiQuestions.val(q.y2)];
  const xs = [0, q.x1, q.x2];
  let [xMin, xMax, xStep] = niceBounds(Math.min(...xs), Math.max(...xs));
  let [yMin, yMax, yStep] = niceBounds(Math.min(...ys), Math.max(...ys));
  // xからyを読む問題では、対象区間を画面の中央で十分に追える倍率を優先する。
  if (q.type === 'A') return { xMin, xMax, yMin, yMax, xStep, yStep };
  // 横長画面でも、今回使う区間が細い線に見えないように表示倍率を抑える。
  const plotRatio = Math.min(1.8, Math.max(1, (w - 56) / Math.max(1, h - 36)));
  let xSpan = xMax - xMin;
  let ySpan = yMax - yMin;
  if (xSpan / ySpan < plotRatio) {
    const need = ySpan * plotRatio;
    const mid = (xMin + xMax) / 2;
    xMin = mid - need / 2; xMax = mid + need / 2;
  } else {
    const need = xSpan / plotRatio;
    const mid = (yMin + yMax) / 2;
    yMin = mid - need / 2; yMax = mid + need / 2;
  }
  xStep = niceStep(xMax - xMin);
  yStep = niceStep(yMax - yMin);
  xMin = Math.floor(xMin / xStep) * xStep; xMax = Math.ceil(xMax / xStep) * xStep;
  yMin = Math.floor(yMin / yStep) * yStep; yMax = Math.ceil(yMax / yStep) * yStep;
  return { xMin, xMax, yMin, yMax, xStep, yStep };
}
function drawLabel(ctx, text, x, y, color, align = 'center') {
  ctx.save();
  ctx.font = '700 15px Outfit, sans-serif';
  ctx.textAlign = align;
  ctx.textBaseline = 'middle';
  ctx.lineWidth = 5;
  ctx.strokeStyle = '#ffffff';
  ctx.fillStyle = color;
  ctx.strokeText(text, x, y);
  ctx.fillText(text, x, y);
  ctx.restore();
}
function drawPoint(ctx, x, y, color, r = 7) {
  ctx.beginPath();
  ctx.fillStyle = color;
  ctx.strokeStyle = '#ffffff';
  ctx.lineWidth = 3;
  ctx.arc(x, y, r, 0, Math.PI * 2);
  ctx.fill();
  ctx.stroke();
}
function drawDashed(ctx, x1, y1, x2, y2, color) {
  ctx.save();
  ctx.strokeStyle = color;
  ctx.lineWidth = 2;
  ctx.setLineDash([7, 6]);
  ctx.beginPath();
  ctx.moveTo(x1, y1);
  ctx.lineTo(x2, y2);
  ctx.stroke();
  ctx.restore();
}
function drawLineSegment(ctx, px, py, q, fromX, toX, color, width, dash = []) {
  ctx.save();
  ctx.strokeStyle = color; ctx.lineWidth = width; ctx.lineCap = 'round'; ctx.setLineDash(dash);
  ctx.beginPath();
  ctx.moveTo(px(fromX), py(HenikiQuestions.val(HenikiQuestions.fx(q.a, q.b, fromX))));
  ctx.lineTo(px(toX), py(HenikiQuestions.val(HenikiQuestions.fx(q.a, q.b, toX))));
  ctx.stroke(); ctx.restore();
}
function drawLegend(ctx, right, top) {
  ctx.save();
  ctx.font = '700 12px Outfit, sans-serif'; ctx.textBaseline = 'middle';
  const x = right - 148, y = top + 12;
  ctx.fillStyle = 'rgba(255,255,255,.92)'; ctx.strokeStyle = '#cbd5e1'; ctx.lineWidth = 1;
  ctx.beginPath(); ctx.roundRect(x, y, 140, 44, 8); ctx.fill(); ctx.stroke();
  ctx.strokeStyle = '#94a3b8'; ctx.setLineDash([5, 5]); ctx.lineWidth = 2;
  ctx.beginPath(); ctx.moveTo(x + 9, y + 14); ctx.lineTo(x + 32, y + 14); ctx.stroke();
  ctx.setLineDash([]); ctx.fillStyle = '#475569'; ctx.fillText('変域の外', x + 39, y + 14);
  ctx.strokeStyle = '#f97316'; ctx.lineWidth = 3;
  ctx.beginPath(); ctx.moveTo(x + 9, y + 31); ctx.lineTo(x + 32, y + 31); ctx.stroke();
  ctx.fillStyle = '#f97316'; ctx.beginPath(); ctx.arc(x + 21, y + 31, 4, 0, Math.PI * 2); ctx.fill();
  ctx.fillText('動く範囲', x + 39, y + 31); ctx.restore();
}
function graphNumber(n) {
  const rounded = Math.round(n * 10) / 10;
  return Number.isInteger(rounded) ? String(rounded) : String(rounded.toFixed(1));
}
function drawArrowLine(ctx, x1, y1, x2, y2, color) {
  ctx.save();
  ctx.strokeStyle = color;
  ctx.fillStyle = color;
  ctx.lineWidth = 6;
  ctx.lineCap = 'round';
  ctx.beginPath();
  ctx.moveTo(x1, y1);
  ctx.lineTo(x2, y2);
  ctx.stroke();
  ctx.restore();
}
function drawXRange(ctx, q, px, axisY) {
  drawArrowLine(ctx, px(q.x1), axisY, px(q.x2), axisY, '#1d4ed8');
  drawPoint(ctx, px(q.x1), axisY, '#1d4ed8', 6);
  drawPoint(ctx, px(q.x2), axisY, '#1d4ed8', 6);
}
function drawYRange(ctx, yLo, yHi, py, axisX) {
  drawArrowLine(ctx, axisX, py(yLo), axisX, py(yHi), '#ef4444');
  drawPoint(ctx, axisX, py(yLo), '#ef4444', 6);
  drawPoint(ctx, axisX, py(yHi), '#ef4444', 6);
}
function drawGraph(q, reveal, now = performance.now()) {
  const c = $('#graph-canvas'), dpr = window.devicePixelRatio || 1, rect = c.getBoundingClientRect();
  c.width = Math.max(1, rect.width * dpr); c.height = Math.max(1, rect.height * dpr);
  const ctx = c.getContext('2d'), w = rect.width, h = rect.height;
  ctx.scale(dpr, dpr);
  ctx.clearRect(0, 0, w, h);
  ctx.fillStyle = '#f8fafc';
  ctx.fillRect(0, 0, w, h);

  const left = 46, top = 14, right = w - 18, bottom = h - 30;
  const plotW = right - left, plotH = bottom - top;
  const { xMin, xMax, yMin, yMax, xStep, yStep } = graphBounds(q, w, h);
  const px = x => left + (x - xMin) / (xMax - xMin) * plotW;
  const py = y => bottom - (y - yMin) / (yMax - yMin) * plotH;
  const clampX = x => Math.max(left, Math.min(right, px(x)));
  const clampY = y => Math.max(top, Math.min(bottom, py(y)));

  ctx.fillStyle = '#ffffff';
  ctx.fillRect(left, top, plotW, plotH);
  ctx.strokeStyle = '#cbd5e1';
  ctx.lineWidth = 1.5;
  ctx.strokeRect(left, top, plotW, plotH);

  ctx.save();
  ctx.beginPath();
  ctx.rect(left, top, plotW, plotH);
  ctx.clip();

  for (let x = Math.ceil(xMin / (xStep / 2)) * (xStep / 2); x <= xMax + 1e-9; x += xStep / 2) {
    const isMajor = Math.abs(x / xStep - Math.round(x / xStep)) < 1e-9;
    ctx.strokeStyle = isMajor ? '#d6dee9' : '#edf2f7';
    ctx.lineWidth = isMajor ? 1.2 : 0.7;
    ctx.beginPath(); ctx.moveTo(px(x), top); ctx.lineTo(px(x), bottom); ctx.stroke();
  }
  for (let y = Math.ceil(yMin / (yStep / 2)) * (yStep / 2); y <= yMax + 1e-9; y += yStep / 2) {
    const isMajor = Math.abs(y / yStep - Math.round(y / yStep)) < 1e-9;
    ctx.strokeStyle = isMajor ? '#d6dee9' : '#edf2f7';
    ctx.lineWidth = isMajor ? 1.2 : 0.7;
    ctx.beginPath(); ctx.moveTo(left, py(y)); ctx.lineTo(right, py(y)); ctx.stroke();
  }

  ctx.strokeStyle = '#334155';
  ctx.lineWidth = 2.6;
  if (yMin <= 0 && yMax >= 0) { ctx.beginPath(); ctx.moveTo(left, py(0)); ctx.lineTo(right, py(0)); ctx.stroke(); }
  if (xMin <= 0 && xMax >= 0) { ctx.beginPath(); ctx.moveTo(px(0), top); ctx.lineTo(px(0), bottom); ctx.stroke(); }

  const p1 = { x: q.x1, y: HenikiQuestions.val(q.y1) };
  const p2 = { x: q.x2, y: HenikiQuestions.val(q.y2) };
  const yLo = Math.min(p1.y, p2.y), yHi = Math.max(p1.y, p2.y);
  const axisY = clampY(0);
  const axisX = clampX(0);
  const explore = q.type === 'A' && reveal >= 1;
  if (explore) {
    drawLineSegment(ctx, px, py, q, xMin, q.x1, '#94a3b8', 2.5, [8, 7]);
    drawLineSegment(ctx, px, py, q, q.x1, q.x2, '#f97316', 5);
    drawLineSegment(ctx, px, py, q, q.x2, xMax, '#94a3b8', 2.5, [8, 7]);
  } else drawLineSegment(ctx, px, py, q, xMin, xMax, '#2563eb', 4);
  if (reveal >= 1 && reveal < 3) {
    if (q.type === 'B') drawYRange(ctx, yLo, yHi, py, axisX);
    else drawXRange(ctx, q, px, axisY);
  }
  if (reveal >= 2) {
    [p1, p2].forEach(p => {
      drawDashed(ctx, px(p.x), clampY(0), px(p.x), py(p.y), '#2563eb');
      drawDashed(ctx, clampX(0), py(p.y), px(p.x), py(p.y), '#ef4444');
      drawPoint(ctx, px(p.x), py(p.y), '#475569', 6);
    });
  }
  if (explore && reveal < 3) {
    const phase = (Math.sin(now / 780) + 1) / 2;
    const movingX = graphManualX == null ? q.x1 + (q.x2 - q.x1) * phase : graphManualX;
    const movingY = HenikiQuestions.val(HenikiQuestions.fx(q.a, q.b, movingX));
    drawDashed(ctx, px(movingX), axisY, px(movingX), py(movingY), '#2563eb');
    drawDashed(ctx, axisX, py(movingY), px(movingX), py(movingY), '#ef4444');
    drawPoint(ctx, px(movingX), py(movingY), '#f97316', 10);
    graphState = { left, right, xMin, xMax, x1: q.x1, x2: q.x2 };
  } else graphState = null;
  if (reveal >= 3) {
    ctx.strokeStyle = '#f97316';
    ctx.lineWidth = 10;
    ctx.lineCap = 'round';
    ctx.beginPath(); ctx.moveTo(px(p1.x), py(p1.y)); ctx.lineTo(px(p2.x), py(p2.y)); ctx.stroke();
    drawXRange(ctx, q, px, axisY);
    drawYRange(ctx, yLo, yHi, py, axisX);
    drawPoint(ctx, px(p1.x), py(p1.y), '#ef4444', 8);
    drawPoint(ctx, px(p2.x), py(p2.y), '#ef4444', 8);
  }
  ctx.restore();

  ctx.font = '600 13px Outfit, sans-serif';
  ctx.textAlign = 'center';
  ctx.textBaseline = 'top';
  ctx.fillStyle = '#64748b';
  for (let x = Math.ceil(xMin / xStep) * xStep; x <= xMax + 1e-9; x += xStep) {
    if (Math.abs(x) < 1e-9) continue;
    ctx.fillText(graphNumber(x), px(x), clampY(0) + 8);
  }
  ctx.textAlign = 'left';
  ctx.textBaseline = 'middle';
  for (let y = Math.ceil(yMin / yStep) * yStep; y <= yMax + 1e-9; y += yStep) {
    if (Math.abs(y) < 1e-9) continue;
    ctx.fillText(graphNumber(y), clampX(0) + 8, py(y));
  }
  ctx.font = '700 14px Outfit, sans-serif';
  ctx.fillStyle = '#334155';
  if (xMin <= 0 && xMax >= 0 && yMin <= 0 && yMax >= 0) ctx.fillText('O', px(0) + 8, py(0) + 14);
  ctx.font = 'italic 700 16px Georgia, serif';
  ctx.fillText('x', right - 14, clampY(0) - 14);
  ctx.fillText('y', clampX(0) + 10, top + 12);

  if (reveal >= 1 && reveal < 3) {
    if (q.type === 'A') {
      drawLegend(ctx, right, top);
      drawLabel(ctx, '← ドラッグ / 矢印キーで点を動かす →', (px(q.x1) + px(q.x2)) / 2, top + 72, '#9a3412');
      drawLabel(ctx, String(q.x1), px(q.x1), axisY + 24, '#1d4ed8');
      drawLabel(ctx, String(q.x2), px(q.x2), axisY + 24, '#1d4ed8');
      drawLabel(ctx, 'xの変域', (px(q.x1) + px(q.x2)) / 2, Math.min(bottom + 18, axisY + 44), '#1d4ed8');
      if (reveal >= 2) {
        const lowPoint = p1.y === yLo ? p1 : p2;
        const highPoint = p1.y === yHi ? p1 : p2;
        const labelX = point => px(point.x) > right - 205 ? px(point.x) - 70 : px(point.x) + 70;
        drawLabel(ctx, `yの最小 = ${graphNumber(yLo)}`, labelX(lowPoint), py(yLo) - 16, '#dc2626');
        drawLabel(ctx, `yの最大 = ${graphNumber(yHi)}`, labelX(highPoint), py(yHi) + 16, '#dc2626');
      }
    } else if (q.type === 'B') {
      drawLabel(ctx, graphNumber(yLo), axisX - 18, py(yLo), '#ef4444', 'right');
      drawLabel(ctx, graphNumber(yHi), axisX - 18, py(yHi), '#ef4444', 'right');
      drawLabel(ctx, 'yの変域', Math.max(14, axisX - 42), (py(yLo) + py(yHi)) / 2, '#ef4444', 'center');
    } else {
      drawLabel(ctx, String(q.x1), px(q.x1), axisY + 24, '#1d4ed8');
      drawLabel(ctx, String(q.x2), px(q.x2), axisY + 24, '#1d4ed8');
      drawLabel(ctx, 'xの変域', (px(q.x1) + px(q.x2)) / 2, Math.min(bottom + 18, axisY + 44), '#1d4ed8');
    }
  }
  if (reveal >= 3) {
    drawLabel(ctx, String(q.x1), px(q.x1), axisY + 24, '#1d4ed8');
    drawLabel(ctx, String(q.x2), px(q.x2), axisY + 24, '#1d4ed8');
    drawLabel(ctx, 'xの変域', (px(q.x1) + px(q.x2)) / 2, Math.min(bottom + 18, axisY + 44), '#1d4ed8');
    drawLabel(ctx, graphNumber(yLo), axisX - 18, py(yLo), '#ef4444', 'right');
    drawLabel(ctx, graphNumber(yHi), axisX - 18, py(yHi), '#ef4444', 'right');
    drawLabel(ctx, 'yの変域', Math.max(14, axisX - 42), (py(yLo) + py(yHi)) / 2, '#ef4444', 'center');
  }
}

$$('.level-btn').forEach(b => b.addEventListener('click', () => { $$('.level-btn').forEach(x => x.classList.remove('active')); b.classList.add('active'); level = Number(b.dataset.level); renderStart(); }));
$('#start-btn').addEventListener('click', () => start());
$('#submit-btn').addEventListener('click', check);
$('#next-btn').addEventListener('click', next);
$('#hint-btn').addEventListener('click', hint);
$('#quit-btn').addEventListener('click', () => { if (!answered && current) reviews.push({ q: current.question, ok: false, ans: ansTex(current), process: '中断しました。', source: current }); result(); });
$('#retry-btn').addEventListener('click', () => start());
$('#home-btn').addEventListener('click', () => { setScreen('#screen-start'); renderStart(); });
$('#reset-btn').addEventListener('click', () => { if (confirm('学習履歴と最高スコアをリセットしますか？')) { storage.del(`${KEY}-hist`); [1, 2, 3].forEach(l => storage.del(`${KEY}-high-${l}`)); renderStart(); } });
$$('.hkey').forEach(b => b.addEventListener('click', () => insertKey(b.dataset.cmd)));
function setGraphPointFromClientX(clientX) {
  if (!graphState || !current || current.type !== 'A' || hintsShown < 1 || answered) return;
  const rect = $('#graph-canvas').getBoundingClientRect();
  const plotX = Math.max(graphState.left, Math.min(graphState.right, clientX - rect.left));
  const rawX = graphState.xMin + (plotX - graphState.left) / (graphState.right - graphState.left) * (graphState.xMax - graphState.xMin);
  graphManualX = Math.max(graphState.x1, Math.min(graphState.x2, rawX));
  redrawGraph();
}
$('#graph-canvas').addEventListener('pointerdown', ev => {
  if (!graphState) return;
  ev.preventDefault();
  $('#graph-canvas').focus({ preventScroll: true });
  $('#graph-canvas').setPointerCapture(ev.pointerId);
  setGraphPointFromClientX(ev.clientX);
});
$('#graph-canvas').addEventListener('pointermove', ev => {
  if ($('#graph-canvas').hasPointerCapture(ev.pointerId)) setGraphPointFromClientX(ev.clientX);
});
$('#graph-canvas').addEventListener('pointerup', ev => {
  if ($('#graph-canvas').hasPointerCapture(ev.pointerId)) $('#graph-canvas').releasePointerCapture(ev.pointerId);
});
$('#graph-canvas').addEventListener('keydown', ev => {
  if (!graphState || !['ArrowLeft', 'ArrowRight'].includes(ev.key)) return;
  ev.preventDefault();
  const step = (graphState.x2 - graphState.x1) / 20;
  const base = graphManualX == null ? (graphState.x1 + graphState.x2) / 2 : graphManualX;
  graphManualX = Math.max(graphState.x1, Math.min(graphState.x2, base + (ev.key === 'ArrowRight' ? step : -step)));
  redrawGraph();
});
document.addEventListener('visibilitychange', () => { if (!document.hidden && current) redrawGraph(); });
window.addEventListener('resize', () => current && redrawGraph());
renderStart();
