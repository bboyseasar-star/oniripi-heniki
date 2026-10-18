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

let level = 1, qi = 0, score = 0, questions = [], current = null, hintsShown = 0, answered = false, focusField = null, reviewMode = false, reviews = [], currentRaws = null;
let graphAnimation = null, graphManualX = null, graphState = null;
const KEY = 'oniripi-heniki';

/* ===== 採点（DOM に触らない。回帰テストからも呼ぶ） =====
   採点は GRADER-CORE（grader-core.js）に任せる。正解は q.answers（有理数 {n,d}）を HenikiQuestions.fmt で
   文字列（'-3/2'・'5'）にして渡す。小数の丸めや許容誤差では比べない。
   raws は欄ごとの生の LaTeX：型 A=[y の変域]、B=[x の変域]、C=[a, b]、D=[x の変域, y の変域]。
   戻り値は GraderCore の結果 {status, reason, parts, …} に、画面に出すアプリ側の一言 note を足したもの。 */
// MathLive が真ん中の文字を「\le{y}」のように波かっこで包んでも読めるようにする（変域の欄だけ）
function henikiPreRange(raw) { return String(raw == null ? '' : raw).replace(/\{\s*([xy])\s*\}/g, ' $1 '); }
function henikiRange(raw, v, lo, hi) {
  return GraderCore.gradeRange(henikiPreRange(raw), { v: v, lo: lo, hi: hi, loIncl: true, hiIncl: true });
}
function henikiHasDecimal(raw) {
  const n = GraderCore.normalize(raw);
  return !!(n && n.s && n.s.indexOf('.') >= 0);
}
// 正解（'-3/2' など）が有限小数で書けるか（分母が 2 と 5 だけ）
function henikiTerminates(ans) {
  const m = String(ans).match(/(\d+)\/(\d+)/);
  let d = m ? parseInt(m[2], 10) : 1;
  while (d % 2 === 0) d /= 2;
  while (d % 5 === 0) d /= 5;
  return d === 1;
}
function gradeAnswer(q, raws) {
  raws = raws || [];
  const f = HenikiQuestions.fmt, A = q.answers.map(f);
  const n = q.type === 'C' || q.type === 'D' ? 2 : 1;
  // 空欄・空の枠が1つでもあれば採点しない（書き直してもらう）
  for (let i = 0; i < n; i++) if (GraderCore.isBlank(raws[i])) return { status: 'empty', reason: 'empty', note: '' };
  for (let i = 0; i < n; i++) if (GraderCore.hasEmptySlot(raws[i])) return { status: 'unreadable', reason: 'emptySlot', note: '' };
  let r, vars, ans;
  if (q.type === 'A' || q.type === 'B') {
    const v = q.type === 'A' ? 'y' : 'x';
    r = henikiRange(raws[0], v, A[0], A[1]); vars = [v]; ans = [A];
  } else if (q.type === 'C') {
    const ra = GraderCore.gradeNumber(raws[0], A[0], { lhs: 'a' });
    const rb = GraderCore.gradeNumber(raws[1], A[1], { lhs: 'b' });
    r = GraderCore.worst([ra, rb]); r.parts = [ra, rb]; vars = ['a', 'b']; ans = [[A[0]], [A[1]]];
  } else {
    const rx = henikiRange(raws[0], 'x', A[0], A[1]);
    const ry = henikiRange(raws[1], 'y', A[2], A[3]);
    r = GraderCore.worst([rx, ry]); r.parts = [rx, ry]; vars = ['x', 'y']; ans = [[A[0], A[1]], [A[2], A[3]]];
  }
  r.note = henikiNote(q, r, raws, vars, ans);
  return r;
}
// GraderCore の一言が無いときに足す、アプリ側の一言（未約分・符号2つは決定どおり何も出さない）
function henikiNote(q, r, raws, vars, ans) {
  const isRange = q.type !== 'C';
  // 欄ごとの結果（変域の欄は、その中の両端の結果も見る）
  const fields = q.type === 'A' || q.type === 'B' ? [r] : (r.parts || []);
  for (let i = 0; i < fields.length; i++) {
    const fr = fields[i], v = vars[i], raw = raws[i];
    if (isRange) {
      if (fr.reason === 'inclusive') return '端の値をふくむときは ≦ を使おう';
      if (fr.reason === 'separator') {
        const nz = GraderCore.normalize(henikiPreRange(raw));
        if (nz.s && nz.s.indexOf(',') >= 0 && /[≤≥<>]/.test(nz.s)) return `「-1≦${v}≦7」のように1つの式で書こう`;
      }
      if (fr.reason === 'variable') return `真ん中には文字 ${v} だけを書こう（最小値≦${v}≦最大値）`;
      if (fr.reason === 'shape' || fr.reason === 'direction') return `「最小値≦${v}≦最大値」の形で書こう`;
    }
    const ends = fr.parts && fr.parts.length ? fr.parts : [fr];
    for (const e of ends) if (e.reason === 'expression') return '計算を最後までして、1つの数で答えよう';
    for (let k = 0; k < ends.length; k++) {
      if (ends[k].status === 'wrong' && ends[k].reason === 'value' && henikiHasDecimal(raw) && !henikiTerminates(ans[i][k] != null ? ans[i][k] : ans[i][0])) return '割り切れない数は分数で答えよう';
    }
  }
  return '';
}
/* ===== 仮想キーボード（タッチ端末） =====
   仮想キーボードの ⏎ は keydown を出さず、欄に beforeinput（inputType 'insertLineBreak'）を出す（MathLive 0.98.4 で確認）。
   キーボードの Enter は keydown で受けて既定の動作を止めるので beforeinput は出ないが、念のため直前に Enter の keydown が
   あったときは何もしない（二重に採点しない）。 */
function onVirtualEnter(field, fn){
  if(!field) return;
  var lastKeyEnter = 0;
  field.addEventListener('keydown', function(e){ if(e.key === 'Enter') lastKeyEnter = Date.now(); }, { capture: true });
  field.addEventListener('beforeinput', function(e){
    if(e.inputType !== 'insertLineBreak') return;
    e.preventDefault();
    if(Date.now() - lastKeyEnter < 500) return;
    fn(e);
  });
}
// 締め切ったら仮想キーボードを閉じる（「次へ」を隠さないように）。
// 出ていたときだけ欄からフォーカスを外す（キーボード付きの端末では、そのまま Enter で次へ進めるように）
function closeVirtualKeyboard(fields){
  var vk = window.mathVirtualKeyboard, wasVisible = false;
  try{ wasVisible = !!(vk && vk.visible); if(vk && vk.hide) vk.hide(); }catch(e){ /* 何もしない */ }
  if(wasVisible) (fields || []).forEach(function(f){ try{ if(f && f.blur) f.blur(); }catch(e){ /* 何もしない */ } });
}
function henikiNeedsRewrite(r) { return r.reason === 'empty' || r.reason === 'emptySlot'; }
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
  $('#level-tag').textContent = reviewMode ? '復習' : `Lv.${level}`; $('#q-counter').textContent = `Q ${qi + 1} / ${questions.length}`;
  $('#progress-fill').style.width = `${qi / questions.length * 100}%`; $('#score-display').textContent = `${score}点`;
  $('#question-label').innerHTML = current.label; $('#question-display').innerHTML = current.question; $('#question-extra').innerHTML = current.extra;
  $('#hint-list').innerHTML = ''; $('#hint-warning').classList.add('hidden');
  $('#feedback-box').className = 'feedback-box hidden'; $('#next-btn').classList.add('hidden'); $('#submit-btn').classList.remove('hidden'); $('#hint-btn').disabled = false;
  $('#response-row').classList.remove('has-feedback');
  renderAnswer(); redrawGraph(); typeset();
  // 次の問題では、最初の欄にすぐ入力できるようにする
  setTimeout(() => { const f = document.querySelector('#answer-grid math-field'); try { if (f && !answered) f.focus(); } catch (e) { /* 何もしない */ } }, 60);
}
function mf(id, wide = false) {
  return `<div class="mf-container${wide ? ' range' : ''}"><math-field id="${id}"></math-field></div>`;
}
function renderAnswer() {
  const yLine = `<div class="answer-line">${mf('ans-y-range', true)}</div>`;
  const xLine = `<div class="answer-line">${mf('ans-x-range', true)}</div>`;
  const labeledYLine = `<div class="answer-line range-labeled"><span class="range-label range-label-y">\\( y \\) の変域</span>${mf('ans-y-range', true)}</div>`;
  const labeledXLine = `<div class="answer-line range-labeled"><span class="range-label range-label-x">\\( x \\) の変域</span>${mf('ans-x-range', true)}</div>`;
  const abLine = `<div class="answer-line">\\( a= \\) ${mf('ans-a')} \\( b= \\) ${mf('ans-b')}</div>`;
  $('#answer-grid').innerHTML = current.type === 'A' ? yLine : current.type === 'B' ? xLine : current.type === 'C' ? abLine : labeledXLine + labeledYLine;
  clearFlash();
  const isRangeQuestion = current.type !== 'C';
  $('#input-note').textContent = isRangeQuestion ? NOTE_RANGE : NOTE_AB;
  delete $('#input-note').dataset.orig;
  $('#le-key').classList.toggle('hidden', !isRangeQuestion);
  $$('math-field').forEach(el => {
    // 欄は問題ごとに作り直すので、作った直後に1回だけ設定する（値の書き換えはしない。全角は採点時にそろえる）
    GraderCore.setupMathField(el, { onEnter: onFieldEnter });
    onVirtualEnter(el, onFieldEnter);   // 仮想キーボードの ⏎
    // タッチ端末で入力できるよう、仮想キーボードは auto にしておく（MathLive 0.98 の欄は OS のキーボードが出ない）。
    // 部品の版が古くても auto になるよう、ここでも指定する（キーボード付きの端末では出ない）
    el.setAttribute('math-virtual-keyboard-policy', 'auto');
    try { el.mathVirtualKeyboardPolicy = 'auto'; } catch (e) { /* 定義前でも属性で効く */ }
    el.addEventListener('focus', () => { focusField = el; });
  });
}
const NOTE_RANGE = '※変域は「最小値≦文字≦最大値」の形で入力してね。分数は約分して書こう。割り切れない数は分数で。';
const NOTE_AB = '※分数は約分して書こう。割り切れない数は分数で（分数は下のボタンが便利）。';
// Enter：未採点なら採点、採点済みなら次へ。押しっぱなしでは進まない
function onFieldEnter(e) {
  if (e && e.repeat) return;
  if (!$('#modal-overlay').classList.contains('hidden')) return;
  if (answered) next(); else check();
}
// 欄ごとの生の LaTeX（gradeAnswer に渡す順）
function getRaws() {
  const get = id => { const el = document.getElementById(id); return el ? (el.getValue ? el.getValue('latex') : el.value) : ''; };
  if (current.type === 'A') return [get('ans-y-range')];
  if (current.type === 'B') return [get('ans-x-range')];
  if (current.type === 'C') return [get('ans-a'), get('ans-b')];
  return [get('ans-x-range'), get('ans-y-range')];
}
function escapeHtml(s) { return String(s).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;'); }
// 生徒の入力（MathLive の LaTeX）を MathJax で表示できる形にする。生の LaTeX を文字のまま見せない
function texOf(s){
  return escapeHtml(String(s)
    // 全角の数字・記号は半角にそろえて見せる（「１．５」が「1、5」のように崩れないように）
    .replace(/[！-～]/g,c=>String.fromCharCode(c.charCodeAt(0)-0xFEE0)).replace(/　/g,' ')
    .replace(/[−ーｰ]/g,'-')
    .replace(/\\dfrac/g,'\\frac').replace(/\\mleft/g,'\\left').replace(/\\mright/g,'\\right')
    .replace(/\\placeholder(?![A-Za-z])\s*(?:\[[^\]]*\])?\s*(?:\{[^{}]*\})?/g,'\\square')
    // キーボードで打った <= >= や \le \ge・≤ ≥ は、正しい答えと同じ ≦ ≧ で見せる
    .replace(/<=|=</g,'\\leqq ').replace(/>=|=>/g,'\\geqq ')
    .replace(/\\leq?(?![A-Za-z])/g,'\\leqq').replace(/\\geq?(?![A-Za-z])/g,'\\geqq')
    .replace(/\u2264/g,'\\leqq ').replace(/\u2265/g,'\\geqq ')
    // % は MathJax ではコメントの記号なので、\% にして消えないようにする
    .replace(/(^|[^\\])%/g,'$1\\%')
    // スラッシュの分数（MathLive で「-4/2」と打ったまま）も縦の分数で見せる
    .replace(/(\d+(?:\.\d+)?)\s*\/\s*(\d+(?:\.\d+)?)/g,'\\frac{$1}{$2}')
    // MathJax が知らない \degree は ^{\circ} にする
    .replace(/\{\}\^\{?\\degree\}?/g,'^{\\circ}').replace(/\^\{?\\degree\}?/g,'^{\\circ}').replace(/\\degree(?![A-Za-z])/g,'^{\\circ}'));
}
function responseTex(raws, q = current) {
  const t = s => (s && !GraderCore.isBlank(s)) ? texOf(s) : '?';
  if (q.type === 'A' || q.type === 'B') return `\\( ${t(raws[0])} \\)`;
  if (q.type === 'C') return `\\( a=${t(raws[0])},\\ b=${t(raws[1])} \\)`;
  return `\\( ${t(raws[0])},\\ ${t(raws[1])} \\)`;
}
// 答えに分数があれば、約束ごとを解説に出しておく（×の画面では未約分の理由を言わない決定のため）
function ruleNote(q) {
  return q.answers.some(a => a.d !== 1) ? '※分数は約分して書こう。割り切れない数は分数で答えよう。' : '';
}
let noteTimer;
function flashNote(msg) {
  const note = $('#input-note');
  if (note.dataset.orig === undefined) note.dataset.orig = note.textContent;
  note.textContent = msg; note.classList.add('is-alert');
  clearTimeout(noteTimer);
  noteTimer = setTimeout(clearFlash, 2200);
}
// 一時的な注意を消して、元の案内に戻す（採点したとき・次の問題へ進んだときも）
function clearFlash() {
  clearTimeout(noteTimer);
  const note = $('#input-note');
  if (note && note.dataset.orig !== undefined) { note.textContent = note.dataset.orig; delete note.dataset.orig; }
  if (note) note.classList.remove('is-alert');
}
// r: gradeAnswer の結果（ギブアップは {status:'wrong', reason:'giveUp'}）
function hasAnyInput(raws) { return !!raws && raws.some(s => s && !GraderCore.isBlank(s)); }
function finishQuestion(r, raws, giveup = false) {
  answered = true;
  closeVirtualKeyboard(Array.from(document.querySelectorAll('#answer-grid math-field')));
  nextGuardUntil = Date.now() + NEXT_GUARD_MS;
  if (!hasAnyInput(raws)) raws = null;   // ギブアップでも、書いていた答えは見せる
  clearFlash();
  const ok = r.status === 'correct';
  const tri = r.status === 'negDenominator';   // △（0点）。×と同じ流れで締め切り、復習リストへ
  if (ok) score += Math.round(100 / questions.length);
  const fb = $('#feedback-box');
  fb.className = `feedback-box ${ok ? 'ok' : tri ? 'tri' : giveup ? 'giveup' : 'ng'} ${ok ? '' : 'pulse'}`;
  $('#response-row').classList.add('has-feedback');
  const msg = giveup ? '' : (r.note || GraderCore.message(r));
  const rule = ruleNote(current);
  const head = giveup ? '答えを確認しました。' : tri ? '△ おしい！（0点）' : '不正解。もう一度復習しよう。';
  fb.innerHTML = ok
    ? `正解！ グラフで端の対応も確認しよう。<br>正しい答え: ${ansTex(current)}`
    : `${head}${msg ? `<span class="fb-msg">${escapeHtml(msg)}</span>` : '<br>'}あなたの解答: ${raws ? responseTex(raws) : 'なし'}<br>正しい答え: ${ansTex(current)}<br>計算: ${current.process}${rule ? `<br>${rule}` : ''}`;
  reviews.push({ q: current.question, ok, mark: GraderCore.mark(r), ans: ansTex(current), mine: raws ? responseTex(raws) : 'なし', process: current.process, source: current });
  $('#score-display').textContent = `${score}点`; $('#submit-btn').classList.add('hidden'); $('#next-btn').classList.remove('hidden'); $('#hint-btn').disabled = true;
  redrawGraph(true); typeset();
}
function check() {
  if (answered) return;
  const raws = getRaws();
  const r = gradeAnswer(current, raws);
  // 空欄・空の枠は採点せず、書き直してもらう（この問題は締め切らない）
  if (henikiNeedsRewrite(r)) { flashNote(r.reason === 'emptySlot' || raws.some(v => GraderCore.hasEmptySlot(v)) ? '空いている枠（□）があるよ。うめてから判定してね' : (current.type === 'C' || current.type === 'D' ? '全部の欄を入力してね！' : '答えを入力してね！')); return; }
  finishQuestion(r, raws, false);
}
function hint() {
  if (answered) return;
  const lastHintIndex = current.hints.length - 1;
  if (hintsShown === lastHintIndex) {
    finishQuestion({ status: 'wrong', reason: 'giveUp' }, getRaws(), true);
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
// 「判定する」の連打で、同じ位置に出る「次へ」まで押してしまわないよう、採点直後は少しだけ押せなくする
const NEXT_GUARD_MS = 400;
let nextGuardUntil = 0;
function onNextClick(e) {
  if (e && e.isTrusted && Date.now() < nextGuardUntil) return;   // 指・マウスの連打だけ止める
  next();
}
function next() { qi++; if (qi >= questions.length) result(); else showQuestion(); }
function result() {
  $('#progress-fill').style.width = '100%'; setScreen('#screen-result');
  const passed = score >= 80;
  $('#result-score').textContent = `${score}点`;
  $('#result-badge').textContent = passed ? ['変域マスター！', '逆転もバッチリ！', 'いい集中力！'][Math.floor(Math.random() * 3)] : 'まちがいだけ復習しよう';
  $('#review-list').innerHTML = reviews.map((r, i) => `<div class="review-item"><b>Q${i + 1} ${r.ok ? '正解' : r.mark === '△' ? '△ 復習（分母のマイナス）' : '復習'}</b>　${r.q}<br>あなた: ${r.mine || 'なし'} ／ 正しい答え: ${r.ans}${r.ok ? '' : `<br>${r.process}`}</div>`).join('');
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
  drawGraph(current, reveal, performance.now(), graphVisuals());
  if (current.type === 'A' && reveal >= 1 && reveal < 3 && !document.hidden) {
    const animate = now => {
      if (!current || answered || current.type !== 'A' || hintsShown < 1 || hintsShown >= 3 || document.hidden) return;
      drawGraph(current, reveal, now, graphVisuals());
      graphAnimation = requestAnimationFrame(animate);
    };
    graphAnimation = requestAnimationFrame(animate);
  }
}
function graphVisuals() {
  return {
    showGrid: level !== 2,
    showScale: level === 1
  };
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
function drawGraph(q, reveal, now = performance.now(), visuals = graphVisuals()) {
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

  if (visuals.showGrid) {
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

  if (visuals.showScale) {
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
$('#next-btn').addEventListener('click', onNextClick);
$('#hint-btn').addEventListener('click', hint);
// ほかの鬼リピと同じく、確認してからホームへ戻る（記録はしない）
$('#quit-btn').addEventListener('click', () => {
  showConfirm({ title: 'ホームに戻る？', message: 'いまのチャレンジは記録されません。', okText: '戻る' }).then(ok => { if (ok) { setScreen('#screen-start'); renderStart(); } });
});
$('#retry-btn').addEventListener('click', () => start());
$('#home-btn').addEventListener('click', () => { setScreen('#screen-start'); renderStart(); });
$('#reset-btn').addEventListener('click', () => {
  showConfirm({ title: '履歴を消す？', message: '学習履歴と最高スコアを消すよ。', okText: '消す', danger: true }).then(ok => { if (ok) { storage.del(`${KEY}-hist`); [1, 2, 3, 4].forEach(l => storage.del(`${KEY}-high-${l}`)); renderStart(); } });
});
// 確認の画面（confirm の代わり）
function showConfirm({ title, message, okText = 'OK', cancelText = 'キャンセル', danger = false }) {
  return new Promise(resolve => {
    const ov = $('#modal-overlay'), card = $('#modal-card');
    $('#modal-title').textContent = title; $('#modal-message').textContent = message;
    $('#modal-ok').textContent = okText; $('#modal-cancel').textContent = cancelText;
    card.classList.toggle('is-danger', danger);
    ov.classList.remove('hidden');
    const done = v => { ov.classList.add('hidden'); cleanup(); resolve(v); };
    const onOk = () => done(true), onCancel = () => done(false), onBg = e => { if (e.target === ov) done(false); };
    function cleanup() { $('#modal-ok').removeEventListener('click', onOk); $('#modal-cancel').removeEventListener('click', onCancel); ov.removeEventListener('click', onBg); }
    $('#modal-ok').addEventListener('click', onOk); $('#modal-cancel').addEventListener('click', onCancel); ov.addEventListener('click', onBg);
    try { $('#modal-cancel').focus(); } catch (e) { /* 何もしない */ }
  });
}
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
