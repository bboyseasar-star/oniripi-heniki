// ===== GRADER-CORE BEGIN v1 =====
// 数学ドリル共通の採点部品。各アプリで同じ内容を使う。
// 回ごと・問ごとの違いは、呼び出すときの設定（opts）だけで表す。
// v1.3（2026-10-18）: 正規表現の中の全角・目に見えない文字を \u 表記に書き換えた（動きは v1.2 と同じ。
//   GAS エディタへのコピペで目に見えない文字が落ち、採点が静かに変わる事故を防ぐ）。
// 判定結果 status:
//   correct（○）/ notReduced（×：値は合うが約分・符号・整理が終わっていない）/
//   negDenominator（△：0点。分母にだけマイナス）/ wrong（×）/
//   unreadable（×：読めない・書きかけ）/ empty（未入力。提出前に止める）
var GraderCore = (function () {
  'use strict';

  var B0 = BigInt(0), B1 = BigInt(1), B10 = BigInt(10);
  var LIMITS = { maxLength: 200, maxDigits: 15, maxDepth: 8, maxExponent: 20 };
  var ST = {
    CORRECT: 'correct', NOT_REDUCED: 'notReduced', NEG_DEN: 'negDenominator',
    WRONG: 'wrong', UNREADABLE: 'unreadable', EMPTY: 'empty'
  };
  // 組み合わせたときに、どれを全体の結果にするか（大きいほど強い）
  var SEVERITY = { correct: 0, negDenominator: 1, notReduced: 2, empty: 3, unreadable: 3, wrong: 4 };
  // 画面に出す一言（reason が優先。無ければ status）
  var MESSAGES = {
    negDenominator: '値は合っています。マイナスは分子か分数の前に書こう',
    // 未約分・符号2つは「不正解」とだけ示す（△扱いの文は出さない）
    unreduced: '',
    doubleNegative: '',
    notSimplified: '式は合っています。y=ax+b の形に整理しよう',
    swapped: '問題の指示に合わせて、y= の形で書こう',
    notSolved: '問題の指示に合わせて、y= の形で書こう',
    integerOnly: '問題の指示に合わせて、整数で答えよう',
    decimalOnly: '問題の指示に合わせて、小数で答えよう',
    decimalNotAllowed: '問題の指示に合わせて、分数で答えよう',
    mixedNumber: '帯分数は使わずに、仮分数で書こう',
    unreadable: '式（数）として読み取れませんでした'
  };
  // 記録シートの answer の末尾に付ける印（正誤欄は boolean のまま）
  var TAGS = {
    negDenominator: '［△分母のマイナス］', unreduced: '［未約分］', doubleNegative: '［未約分］',
    notSimplified: '［未整理］', swapped: '［左右］'
  };

  function ReadErr(reason) { this.reason = reason; } // 読めない → unreadable
  function SemErr(reason) { this.reason = reason; }  // 読めたが答えになっていない → wrong
  function res(status, reason, extra) {
    var r = { status: status, reason: reason || '' };
    if (extra) for (var k in extra) if (Object.prototype.hasOwnProperty.call(extra, k)) r[k] = extra[k];
    return r;
  }
  function has(o, k) { return Object.prototype.hasOwnProperty.call(o, k); }

  /* ---------- 有理数（BigInt） ---------- */
  function babs(x) { return x < B0 ? -x : x; }
  function gcd(a, b) { a = babs(a); b = babs(b); while (b !== B0) { var t = a % b; a = b; b = t; } return a; }
  function rat(n, d) {
    if (d === undefined) d = B1;
    if (d === B0) throw new ReadErr('zeroDenominator');
    if (d < B0) { n = -n; d = -d; }
    var g = gcd(n, d); if (g === B0) g = B1;
    return { n: n / g, d: d / g };
  }
  function rAdd(a, b) { return rat(a.n * b.d + b.n * a.d, a.d * b.d); }
  function rSub(a, b) { return rat(a.n * b.d - b.n * a.d, a.d * b.d); }
  function rMul(a, b) { return rat(a.n * b.n, a.d * b.d); }
  function rDiv(a, b) { if (b.n === B0) throw new ReadErr('zeroDenominator'); return rat(a.n * b.d, a.d * b.n); }
  function rEq(a, b) { return a.n === b.n && a.d === b.d; }
  function rLe(a, b) { return a.n * b.d <= b.n * a.d; }
  function rAbs(a) { return { n: babs(a.n), d: a.d }; }
  function rIsZero(a) { return a.n === B0; }

  /* ---------- 1次式（定数 k ＋ 文字ごとの係数 c） ---------- */
  function linConst(r) { return { k: r, c: {} }; }
  function linVar(name) { var c = {}; c[name] = rat(B1); return { k: rat(B0), c: c }; }
  function linKeys(L) { // 0 でない「枠」の一覧（文字名と、定数は '1'）
    var out = [];
    for (var v in L.c) if (has(L.c, v) && !rIsZero(L.c[v])) out.push(v);
    out.sort();
    if (!rIsZero(L.k)) out.push('1');
    return out;
  }
  function linIsConst(L) { return linKeys(L).filter(function (k) { return k !== '1'; }).length === 0; }
  function linScale(L, r) {
    var c = {};
    for (var v in L.c) if (has(L.c, v)) c[v] = rMul(L.c[v], r);
    return { k: rMul(L.k, r), c: c };
  }
  function linAdd(A, Bv, sign) {
    var c = {}, v;
    for (v in A.c) if (has(A.c, v)) c[v] = A.c[v];
    for (v in Bv.c) if (has(Bv.c, v)) {
      var b = sign < 0 ? rat(-Bv.c[v].n, Bv.c[v].d) : Bv.c[v];
      c[v] = c[v] ? rAdd(c[v], b) : b;
    }
    return { k: sign < 0 ? rSub(A.k, Bv.k) : rAdd(A.k, Bv.k), c: c };
  }
  function linMul(A, Bv) {
    if (linIsConst(A)) return linScale(Bv, A.k);
    if (linIsConst(Bv)) return linScale(A, Bv.k);
    throw new SemErr('nonlinear');
  }
  function linDiv(A, Bv) {
    if (!linIsConst(Bv)) throw new SemErr('nonlinear');
    if (rIsZero(Bv.k)) throw new ReadErr('zeroDenominator');
    return linScale(A, rat(Bv.k.d, Bv.k.n));
  }
  function linCoef(L, key) { return key === '1' ? L.k : (L.c[key] || rat(B0)); }
  function linEq(A, Bv) {
    var keys = linKeys(A).concat(linKeys(Bv));
    for (var i = 0; i < keys.length; i++) if (!rEq(linCoef(A, keys[i]), linCoef(Bv, keys[i]))) return false;
    return true;
  }
  function linHas(L, v) { return !!L.c[v] && !rIsZero(L.c[v]); }

  /* ---------- 入力の正規化 ---------- */
  var RE_PLACEHOLDER = /\\placeholder(?![A-Za-z])\s*(?:\[[^\]]*\])?\s*(?:\{[^{}]*\})?/g;

  function toStr(raw) { return raw == null ? '' : String(raw); }
  // 空の枠（\placeholder）が残っているか
  function hasEmptySlot(raw) { return /\\placeholder(?![A-Za-z])/.test(toStr(raw)); }
  // 何も書いていない（空欄・空の枠だけ・かっことカンマだけ）なら true
  function isBlank(raw) {
    var s = toStr(raw).replace(RE_PLACEHOLDER, '')
      .replace(/\\(?:left|right|mleft|mright|frac|dfrac|tfrac)(?![A-Za-z])/g, '')
      .replace(/\\[,;:! ]|\\q?quad(?![A-Za-z])/g, '')
      .replace(/[\s\u3000(){}\[\]\uFF08\uFF09,\uFF0C\u3001]/g, '');
    return s === '';
  }
  function zenToHan(s) {
    return s.replace(/[\uFF01-\uFF5E]/g, function (c) { return String.fromCharCode(c.charCodeAt(0) - 0xFEE0); })
      .replace(/\u3000/g, ' ');
  }
  // 全角→半角と記号のゆれをそろえる。入力にも単位の側にも同じものをかける
  // （長音「ー」を「-」にするので、単位「平方センチメートル」も同じ形にしてから比べる）
  function unifySymbols(s) {
    s = zenToHan(s);
    s = s.replace(/[\u2212\u30FC\uFF70\u2010-\u2015\u2500\uFE63]/g, '-'); // 負号のゆれ（長音・各種ダッシュ）
    s = s.replace(/[\u3001]/g, ',');
    s = s.replace(/[\u00D7\u00B7\u22C5\u30FB\u2219]/g, '*').replace(/\u00F7/g, '/');
    return s;
  }
  function stripUnits(s, units) {
    if (!units || !units.length) return s;
    for (var i = 0; i < units.length; i++) {
      var u = unifySymbols(String(units[i])); // 回避用の「平方センチメ-トル」も同じ形になる
      var cands = ['\\text{' + u + '}', '\\mathrm{' + u + '}', '\\operatorname{' + u + '}', u];
      for (var j = 0; j < cands.length; j++) {
        var t = s.replace(/\s+$/, '');
        if (t.length > cands[j].length && t.slice(-cands[j].length) === cands[j]) return t.slice(0, -cands[j].length);
      }
    }
    return s;
  }
  // 採点用の1本の文字列にそろえる。{s} か {empty:true} か {error:reason} を返す。
  // 小数点「．」は消さずに「.」にする。「1,2」「1 2」を 12 にしない。
  function normalize(raw, opts) {
    opts = opts || {};
    var s = toStr(raw);
    if (isBlank(s)) return { empty: true };
    if (hasEmptySlot(s)) return { error: 'emptySlot' };
    s = s.replace(/[\u200B-\u200D\u2060\uFEFF]/g, '');
    // コマンドの直後の全角英字（\leqqｙ・\cdotｘ）は、半角にするとコマンド名とつながるので、先に空白で区切る
    s = s.replace(/(\\[A-Za-z]+)(?=[\uFF21-\uFF3A\uFF41-\uFF5A])/g, '$1 ');
    s = unifySymbols(s); // 全角→半角・負号のゆれ（長音も）・読点・掛け算記号
    s = stripUnits(s, opts.units);
    // \left・\right を先に消す（後の \le 置換で \left が「≤ft」に化けないように）
    s = s.replace(/\\(?:left|right|mleft|mright|middle|bigl|bigr|Bigl|Bigr|big|Big)(?![A-Za-z])/g, '');
    s = s.replace(/\\(?:dfrac|tfrac|cfrac)(?![A-Za-z])/g, '\\frac');
    s = s.replace(/\\(?:cdot|times|ast)(?![A-Za-z])/g, '*').replace(/\\div(?![A-Za-z])/g, '/');
    s = s.replace(/\\(?:leqq|leqslant|leq|le)(?![A-Za-z])/g, '≤').replace(/\\(?:geqq|geqslant|geq|ge)(?![A-Za-z])/g, '≥');
    s = s.replace(/\\lt(?![A-Za-z])/g, '<').replace(/\\gt(?![A-Za-z])/g, '>');
    s = s.replace(/[\u2266\u2A7D]/g, '≤').replace(/[\u2267\u2A7E]/g, '≥');
    s = s.replace(/([<>\u2264\u2265])\s*\{\}/g, '$1'); // MathLive の「\lt{}」
    s = s.replace(/\\lbrack(?![A-Za-z])/g, '[').replace(/\\rbrack(?![A-Za-z])/g, ']')
      .replace(/\\lparen(?![A-Za-z])/g, '(').replace(/\\rparen(?![A-Za-z])/g, ')');
    s = s.replace(/\\(?:displaystyle|textstyle)(?![A-Za-z])/g, '');
    // 大文字の文字（Y=2X+1）は小文字として読む（\ コマンドの中は変えない）
    s = s.replace(/\\[A-Za-z]+|[A-Z]/g, function (m) { return m.length === 1 ? m.toLowerCase() : m; });
    s = s.replace(/\\q?quad(?![A-Za-z])/g, ' ').replace(/\\[,;:! ]/g, ' ').replace(/~/g, ' ');
    // 数字と数字が空白で区切られている（「1 2」「1\,2」）のは並び書き。12 と読まない
    if (/[0-9.]\s+[0-9.]/.test(s)) return { error: 'spacedDigits' };
    s = s.replace(/\s+/g, '');
    s = s.replace(/<=|=</g, '≤').replace(/>=|=>/g, '≥');
    if (s === '') return { empty: true };
    if (s.length > LIMITS.maxLength) return { error: 'tooLong' };
    var cmds = s.match(/\\[A-Za-z]+/g) || [];
    for (var i = 0; i < cmds.length; i++) if (cmds[i] !== '\\frac') return { error: 'command' };
    if (/\\frac[A-Za-z]/.test(s)) return { error: 'command' };
    if (!/^[0-9a-z.+\-*\/^(){}\[\]\\=,<>\u2264\u2265]*$/.test(s)) return { error: 'character' };
    return { s: s };
  }

  /* ---------- 構文木 ---------- */
  function parse(src, vars) {
    var pos = 0, depth = 0;
    function peek() { return src.charAt(pos); }
    function isFracAt() { return src.substr(pos, 5) === '\\frac' && !/[A-Za-z]/.test(src.charAt(pos + 5)); }
    function enter() { if (++depth > LIMITS.maxDepth) throw new ReadErr('tooDeep'); }
    function numNode(text) {
      if (text.replace('.', '').length > LIMITS.maxDigits) throw new ReadErr('tooManyDigits');
      if (/^0[0-9]/.test(text)) throw new ReadErr('leadingZero');
      var parts = text.split('.'), whole = parts[0], dec = parts[1] || '';
      var den = B1; for (var i = 0; i < dec.length; i++) den *= B10;
      return { t: 'num', text: text, isInt: parts.length === 1, v: rat(BigInt((whole || '0') + dec), den) };
    }
    function varNode(ch) {
      if (vars.indexOf(ch) < 0) throw new SemErr('unknownLetter');
      return { t: 'var', name: ch };
    }
    function expr() {
      var node = term();
      while (peek() === '+' || peek() === '-') {
        var op = src.charAt(pos++);
        node = { t: op === '+' ? 'add' : 'sub', a: node, b: term() };
      }
      return node;
    }
    function startsFactor() {
      var ch = peek();
      return ch === '(' || ch === '[' || ch === '{' || isFracAt() || /[a-z0-9.]/.test(ch);
    }
    function term() {
      var node = unary();
      for (;;) {
        var ch = peek();
        if (ch === '*' || ch === '/') { pos++; node = { t: ch === '*' ? 'mul' : 'div', a: node, b: unary() }; continue; }
        if (!startsFactor()) return node;
        if (/[0-9.]/.test(ch)) throw new ReadErr('digitAfterFactor'); // x2、(3)4 など
        var right = power();
        // 数のすぐ後ろに数の分数（2\frac{1}{3}）は帯分数。掛け算として読まない
        if (stripSigns(node).core.t === 'num' && right.t === 'frac' && !hasVar(right)) throw new SemErr('mixedNumber');
        node = { t: 'mul', a: node, b: right, implicit: true };
      }
    }
    function unary() {
      var ch = peek();
      if (ch === '+' || ch === '-') {
        pos++;
        if (peek() === '+' || peek() === '-') throw new ReadErr('doubleSign');
        return { t: ch === '-' ? 'neg' : 'pos', x: power() };
      }
      return power();
    }
    function power() {
      var base = atom();
      if (peek() !== '^') return base;
      pos++;
      var e;
      if (peek() === '{') e = group('{', '}');
      else if (/[0-9]/.test(peek())) e = numNode(src.charAt(pos++));
      else throw new ReadErr('badExponent');
      return { t: 'pow', a: base, e: e };
    }
    function group(open, close) {
      pos++; enter();
      if (peek() === close) throw new ReadErr('emptyGroup');
      var n = expr();
      if (src.charAt(pos) !== close) throw new ReadErr('unclosed');
      pos++; depth--;
      return { t: 'paren', x: n };
    }
    function fracArg() {
      if (peek() === '{') return group('{', '}');
      var ch = peek(); // TeX の省略形 \frac12・\frac2x：引数は1文字ずつ
      if (/[0-9]/.test(ch)) { pos++; return numNode(ch); }
      if (/[a-z]/.test(ch)) { pos++; return varNode(ch); }
      throw new ReadErr('fracArgument');
    }
    function atom() {
      var ch = peek();
      if (ch === '(') return group('(', ')');
      if (ch === '[') return group('[', ']');
      if (ch === '{') return group('{', '}');
      if (isFracAt()) {
        pos += 5; enter();
        var a = fracArg(), b = fracArg();
        depth--;
        return { t: 'frac', num: a, den: b };
      }
      var m = /^(?:[0-9]+(?:\.[0-9]+)?|\.[0-9]+)/.exec(src.slice(pos));
      if (m) { pos += m[0].length; return numNode(m[0]); }
      if (/[a-z]/.test(ch)) { pos++; return varNode(ch); }
      throw new ReadErr(ch ? 'unexpected' : 'unexpectedEnd');
    }
    if (src === '') throw new ReadErr('emptyPart');
    var tree = expr();
    if (pos !== src.length) throw new ReadErr('trailing');
    return tree;
  }

  function hasVar(node) {
    if (!node || typeof node !== 'object') return false;
    if (node.t === 'var') return true;
    return hasVar(node.x) || hasVar(node.a) || hasVar(node.b) || hasVar(node.num) || hasVar(node.den) || hasVar(node.e);
  }
  function stripSigns(node) {
    var neg = 0;
    for (;;) {
      if (node.t === 'neg') { neg++; node = node.x; }
      else if (node.t === 'pos' || node.t === 'paren') node = node.x;
      else break;
    }
    return { neg: neg, core: node };
  }
  function evalLin(node) {
    switch (node.t) {
      case 'num': return linConst(node.v);
      case 'var': return linVar(node.name);
      case 'paren': case 'pos': return evalLin(node.x);
      case 'neg': return linScale(evalLin(node.x), rat(-B1));
      case 'add': return linAdd(evalLin(node.a), evalLin(node.b), 1);
      case 'sub': return linAdd(evalLin(node.a), evalLin(node.b), -1);
      case 'mul': return linMul(evalLin(node.a), evalLin(node.b));
      case 'div': return linDiv(evalLin(node.a), evalLin(node.b));
      case 'frac': return linDiv(evalLin(node.num), evalLin(node.den));
      case 'pow': {
        var e = evalLin(node.e), b = evalLin(node.a);
        if (!linIsConst(e) || e.k.d !== B1 || babs(e.k.n) > BigInt(LIMITS.maxExponent)) throw new SemErr('badExponent');
        if (!linIsConst(b)) { if (e.k.n === B1) return b; throw new SemErr('nonlinear'); }
        var r = rat(B1);
        for (var i = B0; i < babs(e.k.n); i++) r = rMul(r, b.k);
        return linConst(e.k.n < B0 ? rDiv(rat(B1), r) : r);
      }
      default: throw new ReadErr('node');
    }
  }

  /* ---------- 表し方の点検（約分・分母の負号・二重の負号・整理） ---------- */
  function intLit(node) {
    var s = stripSigns(node);
    return s.core.t === 'num' && s.core.isInt ? { neg: s.neg, v: s.core.v.n } : null;
  }
  // 分子が「整数」「文字」「整数×文字」なら係数と負号の数を返す。それ以外は null
  function monoCoef(node) {
    var s = stripSigns(node), core = s.core;
    if (core.t === 'num') return core.isInt ? { neg: s.neg, c: core.v.n } : null;
    if (core.t === 'var') return { neg: s.neg, c: B1 };
    if (core.t === 'mul') {
      var a = stripSigns(core.a), b = stripSigns(core.b);
      if (a.core.t === 'num' && a.core.isInt && b.core.t === 'var') return { neg: s.neg + a.neg + b.neg, c: a.core.v.n };
      if (a.core.t === 'var' && b.core.t === 'num' && b.core.isInt) return { neg: s.neg + a.neg + b.neg, c: b.core.v.n };
    }
    return null;
  }
  function fracParts(node) { return node.t === 'frac' ? [node.num, node.den] : [node.a, node.b]; }
  function collectFlags(node, flags) {
    if (!node || typeof node !== 'object') return flags;
    if (node.t === 'frac' || node.t === 'div') {
      var p = fracParts(node), nm = monoCoef(p[0]), dn = intLit(p[1]);
      if (nm && dn) {
        var negs = nm.neg + dn.neg;
        if (negs >= 2) flags.doubleNegative = true;
        else if (dn.neg === 1) flags.negDenominator = true;
        var c = babs(nm.c), d = babs(dn.v);
        if (d === B1 || c === B0 || (d !== B0 && gcd(c, d) !== B1)) flags.unreduced = true;
      } else {
        flags.notSimplified = true; // 分子・分母に式や小数（\frac{x+1}{2}、\frac{1.5}{3}）
        // まとめた分数（\frac{-300x+2400}{2}）でも、分子の係数すべてと分母に公約数がある・分母が1なら未約分
        var numL = null;
        try { numL = evalLin(p[0]); } catch (e) { numL = null; }
        if (dn && numL) {
          var g = babs(dn.v), allInt = true, keys = linKeys(numL);
          for (var i = 0; i < keys.length; i++) {
            var cf = linCoef(numL, keys[i]);
            if (cf.d !== B1) { allInt = false; break; }
            g = gcd(g, cf.n);
          }
          if (allInt && keys.length && (babs(dn.v) === B1 || g !== B1)) flags.unreduced = true;
          if (dn.neg === 1) flags.negDenominator = true;
        }
      }
    }
    if (node.t === 'neg') {
      var inner = stripSigns(node.x);
      if (inner.neg > 0) flags.doubleSign = true; // -(-3)
      if (inner.core.t === 'frac' || inner.core.t === 'div') {
        var q = fracParts(inner.core), nm2 = monoCoef(q[0]), dn2 = intLit(q[1]);
        if ((nm2 && nm2.neg) || (dn2 && dn2.neg)) flags.doubleNegative = true; // -\frac{-2}{3}
      }
    }
    // x-(-2)、x+(-2) のような二重の符号は整理されていない
    if ((node.t === 'add' || node.t === 'sub') && node.b.t === 'paren') {
      var rb = node.b.x;
      while (rb.t === 'paren') rb = rb.x;
      if (rb.t === 'neg' || rb.t === 'pos') flags.doubleSign = true;
    }
    collectFlags(node.x, flags); collectFlags(node.a, flags); collectFlags(node.b, flags);
    collectFlags(node.num, flags); collectFlags(node.den, flags); collectFlags(node.e, flags);
    return flags;
  }
  // 一番外側の足し算・引き算の項に分ける
  function topTerms(node, out) {
    out = out || [];
    var n = node;
    while (n.t === 'paren') n = n.x;
    if (n.t === 'add' || n.t === 'sub') { topTerms(n.a, out); topTerms(n.b, out); }
    else out.push(n);
    return out;
  }
  // 同類項がまとまっていない・かっこが残っている（2(x+1)）・0 の項がある → 整理されていない
  function termsNotSimplified(node) {
    var terms = topTerms(node), seen = {};
    for (var i = 0; i < terms.length; i++) {
      var keys = linKeys(evalLin(terms[i]));
      if (keys.length !== 1) return true;
      if (seen[keys[0]]) return true;
      seen[keys[0]] = true;
    }
    return false;
  }
  // 値が合っているときの、表し方による結果。
  // opts.allowUnsimplified: y=ax+b に整理していない式（かっこ形・まとめた分数・+0）も○にする
  function formStatus(flags, opts) {
    if (flags.doubleNegative) return res(ST.NOT_REDUCED, 'doubleNegative');
    if (flags.unreduced) return res(ST.NOT_REDUCED, 'unreduced');
    if ((flags.notSimplified || flags.doubleSign) && !(opts && opts.allowUnsimplified)) return res(ST.NOT_REDUCED, 'notSimplified');
    if (flags.negDenominator) return res(ST.NEG_DEN, 'negDenominator');
    return res(ST.CORRECT, '');
  }
  function guard(fn) {
    try { return fn(); }
    catch (e) {
      if (e instanceof ReadErr) return res(ST.UNREADABLE, e.reason);
      if (e instanceof SemErr) return res(ST.WRONG, e.reason);
      if (e && /^GraderCore:/.test(e.message || '')) throw e; // 作り手の誤りは隠さない
      return res(ST.UNREADABLE, 'internal');
    }
  }
  // 模範解答（先生が書く）を読む。読めなければ作り手の誤りなので例外にする
  var answerCache = {};
  function answerTree(text) {
    var key = String(text);
    if (has(answerCache, key)) return answerCache[key];
    var n = normalize(text);
    if (!n.s) throw new Error('GraderCore: 模範解答が読めません: ' + text);
    answerCache[key] = n.s;
    return n.s;
  }
  function answerValue(text) {
    var s = answerTree(text), L;
    try { L = evalLin(parse(s, [])); } catch (e) { L = null; }
    if (!L || !linIsConst(L)) throw new Error('GraderCore: 模範解答（数）が読めません: ' + text);
    return L.k;
  }
  function answerLin(text, vars) {
    var s = answerTree(text);
    try { return evalLin(parse(s, vars)); }
    catch (e) { throw new Error('GraderCore: 模範解答（式）が読めません: ' + text); }
  }
  // 「y=-3」のように、欄の文字と同じ文字を書き添えた答え。
  // lhs: 許す文字（'y' や ['x','y']）。違う文字なら wrong、許していなければ null を返す
  function stripLhs(s, lhs) {
    var m = /^([a-z])=(?!.*=)/.exec(s);
    if (!m) return { s: s };
    var list = lhs == null ? [] : (Array.isArray(lhs) ? lhs : [lhs]);
    if (list.indexOf(m[1]) >= 0) return { s: s.slice(2) };
    return list.length ? { r: res(ST.WRONG, 'otherLetter') } : { r: res(ST.UNREADABLE, 'separator') };
  }

  /* ---------- 数（整数・分数・小数） ---------- */
  // opts.form: 'any'（既定。等しい小数も○）| 'fraction'（分数で答えよ：小数は×）
  //          | 'integer'（整数で答えよ：小数・分数は×）| 'decimal'（小数第○位まで：分数は×）
  // opts.tol: 許容幅（文字列 '0.005' など。読み取り問題だけ）
  // opts.lhs: 'y' なら「y=-3」も読む。opts.units: ['km'] なら「160km」も読む
  // opts.thousands: 3桁区切り「1,200」を読む（既定 true。「1,2」「12,00」は読めない）
  function gradeNumberS(s, answer, opts) {
    return guard(function () {
      var tree = parse(s, []);
      var v = evalLin(tree);
      if (!linIsConst(v)) throw new SemErr('hasLetter');
      var a = answerValue(answer);
      var ok = opts.tol ? rLe(rAbs(rSub(v.k, a)), answerValue(opts.tol)) : rEq(v.k, a);
      if (!ok) return res(ST.WRONG, 'value');
      var sc = stripSigns(tree), core = sc.core, flags = collectFlags(tree, {});
      if (core.t === 'num') {
        if (flags.doubleNegative || flags.doubleSign) return res(ST.NOT_REDUCED, 'doubleNegative');
        if (!core.isInt && opts.form === 'fraction') return res(ST.WRONG, 'decimalNotAllowed');
        if (!core.isInt && opts.form === 'integer') return res(ST.WRONG, 'integerOnly');
        return res(ST.CORRECT, core.isInt ? '' : 'decimal');
      }
      if ((core.t === 'frac' || core.t === 'div') && intLit(fracParts(core)[0]) && intLit(fracParts(core)[1])) {
        if (opts.form === 'integer') return res(ST.WRONG, 'integerOnly');
        if (opts.form === 'decimal') return res(ST.WRONG, 'decimalOnly');
        return formStatus(flags, null);
      }
      return res(ST.WRONG, 'expression'); // 2*3、1+1、\frac{1.5}{3} のような計算途中
    });
  }
  function prepNumber(s, opts) {
    var p = stripLhs(s, opts.lhs);
    if (p.r) return p;
    s = p.s;
    if (opts.thousands !== false && /^[-+]?[0-9]{1,3}(?:,[0-9]{3})+(?:\.[0-9]+)?$/.test(s)) s = s.replace(/,/g, '');
    if (/[=,<>\u2264\u2265]/.test(s)) return { r: res(ST.UNREADABLE, 'separator') };
    return { s: s };
  }
  function gradeNumber(raw, answer, opts) {
    opts = opts || {};
    var n = normalize(raw, opts);
    if (n.empty) return res(ST.EMPTY, 'empty');
    if (n.error) return res(ST.UNREADABLE, n.error);
    var p = prepNumber(n.s, opts);
    if (p.r) return p.r;
    return gradeNumberS(p.s, answer, opts);
  }

  /* ---------- 1次式（欄の外に y= があるとき） ---------- */
  // opts.vars: ['x'] など。opts.optionalLhs: 'y' なら、生徒が「y=」を付けて書いても読む。
  // opts.lhsSwap: true なら「…=y」も読む（欄の外に y= が印字されていない欄だけ。印字された欄では使わない）
  // opts.allowUnsimplified: y=ax+b に整理していない式も○（★H。ch3-4-4 だけ true）
  function gradeLinearS(s, answer, opts) {
    var vars = opts.vars || ['x'];
    return guard(function () {
      var tree = parse(s, vars), L = evalLin(tree);
      if (!linEq(L, answerLin(answer, vars))) return res(ST.WRONG, 'value');
      var flags = collectFlags(tree, {});
      if (termsNotSimplified(tree)) flags.notSimplified = true;
      return formStatus(flags, opts);
    });
  }
  // 式・変域の中の3桁区切り（y=-100x+10,000）のカンマを外す。「1,2」「12,00」は外さない（読めない）
  function stripThousandsInExpr(s) {
    return s.replace(/(^|[^0-9.,])([0-9]{1,3}(?:,[0-9]{3})+)(?![0-9.,])/g, function (m, pre, num) { return pre + num.replace(/,/g, ''); });
  }
  function gradeLinear(raw, answer, opts) {
    opts = opts || {};
    var n = normalize(raw, opts);
    if (n.empty) return res(ST.EMPTY, 'empty');
    if (n.error) return res(ST.UNREADABLE, n.error);
    var s = stripThousandsInExpr(n.s), lhs = opts.optionalLhs, swapped = false;
    if (lhs && s.indexOf(lhs + '=') === 0) s = s.slice(lhs.length + 1);
    else if (lhs && opts.lhsSwap && s.slice(-(lhs.length + 1)) === '=' + lhs) { s = s.slice(0, -(lhs.length + 1)); swapped = true; }
    if (/[=,<>\u2264\u2265]/.test(s)) return res(ST.UNREADABLE, 'separator');
    var r = gradeLinearS(s, answer, opts);
    r.swapped = swapped;
    return r;
  }

  /* ---------- 等式 ---------- */
  // opts.mode: 'solved'（y=… の形を問う。左右入れ替えを○にするかを opts.allowSwap で必ず指定）
  //          | 'equivalent'（連立の式を作る問。同じ解をもつ式なら○：項の順・左右・移項・両辺の定数倍・
  //            正確な小数係数。式を作る問なので約分・整理の点検はしない）
  // opts.vars: 使う文字（['x','y']、['a','b'] など）。opts.allowUnsimplified: solved で整理していない式も○
  // 戻り値に swapped（左右を入れ替えて書いたか）を付ける
  function splitEq(s) {
    var parts = s.split('=');
    if (parts.length !== 2) throw new ReadErr(parts.length < 2 ? 'noEquals' : 'manyEquals');
    if (parts[0] === '' || parts[1] === '') throw new ReadErr('emptySide');
    return parts;
  }
  function gradeEquation(raw, answer, opts) {
    opts = opts || {};
    var vars = opts.vars || ['x', 'y'], mode = opts.mode || 'solved';
    if (mode === 'solved' && typeof opts.allowSwap !== 'boolean') throw new Error('GraderCore: solved の問は allowSwap（左右入れ替えを○にするか）を必ず指定してください');
    var ans = answerTree(answer).split('=');
    if (ans.length !== 2) throw new Error('GraderCore: 等式の模範解答には = がちょうど1つ要ります: ' + answer);
    if (mode === 'solved' && !/^[a-z]$/.test(ans[0])) throw new Error('GraderCore: solved の模範解答は「y=…」の形で書いてください: ' + answer);
    var n = normalize(raw, opts);
    if (n.empty) return res(ST.EMPTY, 'empty');
    if (n.error) return res(ST.UNREADABLE, n.error);
    var es = stripThousandsInExpr(n.s);
    if (/[,<>\u2264\u2265]/.test(es)) return res(ST.UNREADABLE, 'separator');
    return guard(function () {
      var sides = splitEq(es);
      var tL = parse(sides[0], vars), tR = parse(sides[1], vars);
      var L = evalLin(tL), R = evalLin(tR);
      if (mode === 'solved') {
        var target = ans[0], expected = answerLin(ans[1], vars), swapped, other;
        if (tL.t === 'var' && tL.name === target && !linHas(R, target)) { swapped = false; other = tR; }
        else if (tR.t === 'var' && tR.name === target && !linHas(L, target)) { swapped = true; other = tL; }
        else return res(ST.WRONG, 'notSolved', { swapped: false }); // 2x+3y=3 など。値が同じでも×
        if (!linEq(evalLin(other), expected)) return res(ST.WRONG, 'value', { swapped: swapped });
        if (swapped && !opts.allowSwap) return res(ST.WRONG, 'swapped', { swapped: true });
        var flags = collectFlags(other, {});
        if (termsNotSimplified(other)) flags.notSimplified = true;
        var r = formStatus(flags, opts); r.swapped = swapped; return r;
      }
      // equivalent: (左辺)-(右辺) が模範解答の 0 でない定数倍か
      var D = linAdd(L, R, -1), A = linAdd(answerLin(ans[0], vars), answerLin(ans[1], vars), -1);
      var keys = linKeys(A);
      if (!keys.length) throw new Error('GraderCore: 模範解答の式が 0=0 です: ' + answer);
      var ratio = rDiv(linCoef(D, keys[0]), linCoef(A, keys[0]));
      if (rIsZero(ratio) || !linEq(D, linScale(A, ratio))) return res(ST.WRONG, 'value', { swapped: false });
      return res(ST.CORRECT, '', { swapped: false });
    });
  }

  /* ---------- 組み合わせ ---------- */
  function worst(results) {
    var w = res(ST.CORRECT, '');
    for (var i = 0; i < results.length; i++) {
      var st = results[i].status === ST.EMPTY ? ST.UNREADABLE : results[i].status;
      if (SEVERITY[st] > SEVERITY[w.status]) w = res(st, results[i].reason);
    }
    return w;
  }

  /* ---------- 座標・数の組 (a, b) ---------- */
  // answers: ['0', '-3'] など。opts は数の採点と同じ（form・tol）に加えて
  //   opts.vars: 成分の文字（既定 ['x','y']。「x=0,y=-3」も読む）
  //   opts.allowLabel: 「B(0,-3)」「点B(0,-3)」の点の名前を読み飛ばす（既定 true）
  //   opts.requireParens: かっこ必須（既定 false。「0,-3」も○）
  function splitTop(s, sep) {
    var out = [], depth = 0, cur = '';
    for (var i = 0; i < s.length; i++) {
      var ch = s.charAt(i);
      if (ch === '(' || ch === '{' || ch === '[') depth++;
      if (ch === ')' || ch === '}' || ch === ']') depth--;
      if (depth < 0) return null;
      if (ch === sep && depth === 0) { out.push(cur); cur = ''; } else cur += ch;
    }
    if (depth !== 0) return null;
    out.push(cur);
    return out;
  }
  var RE_POINT_LABEL = /^\s*\u70B9?\s*(?:\\(?:mathrm|text|mathit|operatorname)\{\s*[A-Z\uFF21-\uFF3A]\s*\}|[A-Z\uFF21-\uFF3A])\s*[=\uFF1D]?\s*(?=\\left|\\lparen|\(|\uFF08)/;
  function gradeTuple(raw, answers, opts) {
    opts = opts || {};
    var vars = opts.vars || ['x', 'y'];
    var src = toStr(raw);
    if (opts.allowLabel !== false) src = src.replace(RE_POINT_LABEL, '');
    var n = normalize(src, opts);
    if (n.empty) return res(ST.EMPTY, 'empty');
    if (n.error) return res(ST.UNREADABLE, n.error);
    var s = n.s, wrapped = false;
    while (s.charAt(0) === '(' || s.charAt(s.length - 1) === ')') {
      // 外側のかっこは、最初と最後が対になっているときだけはずす（書きかけ「(0,-3」は読めない）
      if (s.charAt(0) !== '(' || s.charAt(s.length - 1) !== ')' || splitTop(s.slice(1, -1), ',') === null) {
        if (wrapped) break; // 「((0),(-3))」の内側は成分のかっこ
        return res(ST.UNREADABLE, 'unclosed');
      }
      s = s.slice(1, -1); wrapped = true;
    }
    if (!wrapped && opts.requireParens) return res(ST.UNREADABLE, 'noParens');
    var parts = splitTop(s, ',');
    if (!parts) return res(ST.UNREADABLE, 'unclosed');
    if (parts.length !== answers.length) return res(ST.WRONG, 'count');
    // 全部の成分に名前が付いていて（y=-3,x=0）、名前が成分の文字の並べ替えなら、名前の順に並べ直す
    var labels = parts.map(function (pt) { var m = /^([a-z])=/.exec(pt); return m ? m[1] : null; });
    if (labels.every(function (l) { return l; }) && labels.slice().sort().join() === vars.slice(0, parts.length).sort().join()) {
      var sorted = [];
      for (var li = 0; li < parts.length; li++) sorted[vars.indexOf(labels[li])] = parts[li];
      parts = sorted;
    }
    var rs = [];
    for (var i = 0; i < parts.length; i++) {
      var part = parts[i];
      if (part === '') { rs.push(res(ST.UNREADABLE, 'emptyPart')); continue; }
      var p = prepNumber(part, { lhs: vars[i] || null, thousands: false });
      rs.push(p.r ? p.r : gradeNumberS(p.s, answers[i], opts));
    }
    var w = worst(rs); w.parts = rs; return w;
  }

  /* ---------- 変域・不等式 ---------- */
  // spec: { v:'y', lo:'-3', hi:'5', loIncl:true, hiIncl:true }（片側だけなら lo か hi を null）
  //   loIncl・hiIncl は true（≦）/ false（<）/ 'any'（どちらでも○。区間の境目など）
  // opts.allowReverse: 逆向き（5≥y≥-3。向きがそろっていること）を○にするか（既定 true）
  // 分けて書く形（y≥-3,y≤5）は読めない（×）
  function gradeRange(raw, spec, opts) {
    opts = opts || {};
    var allowReverse = opts.allowReverse !== false;
    var n = normalize(raw, opts);
    if (n.empty) return res(ST.EMPTY, 'empty');
    if (n.error) return res(ST.UNREADABLE, n.error);
    var rsrc = stripThousandsInExpr(n.s);
    if (/[=,]/.test(rsrc)) return res(ST.UNREADABLE, 'separator');
    var tokens = rsrc.split(/([\u2264<\u2265>])/);
    var nums = [], ops = [];
    for (var i = 0; i < tokens.length; i++) (i % 2 ? ops : nums).push(tokens[i]);
    for (i = 0; i < nums.length; i++) if (nums[i] === '') return res(ST.UNREADABLE, 'emptyPart');
    var asc = ops.every(function (o) { return o === '≤' || o === '<'; });
    var desc = ops.every(function (o) { return o === '≥' || o === '>'; });
    if (!asc && !desc) return res(ST.WRONG, 'direction');
    var two = spec.lo != null && spec.hi != null;
    if (ops.length !== (two ? 2 : 1)) return res(ST.WRONG, 'shape');
    // 片側だけで文字が左（x≥2、x≤5）は、文字が右の形（2≤x、5≥x）に読み替える
    if (!two && nums[0] === spec.v) {
      var flip = { '≤': '≥', '<': '>', '≥': '≤', '>': '<' };
      return gradeRange(nums[1] + flip[ops[0]] + nums[0], spec, { allowReverse: true });
    }
    if (desc && !allowReverse && two) return res(ST.WRONG, 'reversed');
    // 小さい方から並べ直す
    if (desc) { nums.reverse(); ops.reverse(); }
    var lo = null, loOp = null, hi = null, hiOp = null, mid;
    if (two) { lo = nums[0]; loOp = ops[0]; mid = nums[1]; hiOp = ops[1]; hi = nums[2]; }
    else if (spec.lo != null) { lo = nums[0]; loOp = ops[0]; mid = nums[1]; }
    else { mid = nums[0]; hiOp = ops[0]; hi = nums[1]; }
    if (mid !== spec.v) return res(ST.WRONG, 'variable');
    function inclOk(op, want) { return want === 'any' || (op === '≤' || op === '≥') === !!want; }
    var rs = [];
    if (spec.lo != null) {
      if (!inclOk(loOp, spec.loIncl)) return res(ST.WRONG, 'inclusive');
      rs.push(gradeNumberS(lo, spec.lo, opts));
    }
    if (spec.hi != null) {
      if (!inclOk(hiOp, spec.hiIncl)) return res(ST.WRONG, 'inclusive');
      rs.push(gradeNumberS(hi, spec.hi, opts));
    }
    var w = worst(rs); w.parts = rs; w.reversed = desc; return w;
  }

  /* ---------- 複数の欄に複数の答え（順不同も可） ---------- */
  function permutations(n) {
    if (n === 0) return [[]];
    var out = [], sub = permutations(n - 1);
    for (var i = 0; i < sub.length; i++) for (var j = 0; j <= sub[i].length; j++) {
      var p = sub[i].slice(); p.splice(j, 0, n - 1); out.push(p);
    }
    return out;
  }
  // 1対1の対応で一番よい組み合わせを選ぶ。余分な欄に何か書いてあれば×（空の欄は無視）
  function matchSet(raws, answers, gradeOne, ordered) {
    var filled = [];
    for (var i = 0; i < raws.length; i++) if (!isBlank(raws[i])) filled.push(raws[i]);
    if (!filled.length) return res(ST.EMPTY, 'empty');
    if (filled.length < answers.length) return res(ST.WRONG, 'missing');
    if (filled.length > answers.length) return res(ST.WRONG, 'extra');
    if (answers.length > 6) throw new Error('GraderCore: 複数の答えは 6 個まで');
    var table = filled.map(function (r) { return answers.map(function (a) { return gradeOne(r, a); }); });
    var perms = ordered ? [answers.map(function (_, k) { return k; })] : permutations(answers.length);
    var best = null;
    perms.forEach(function (p) {
      var rs = p.map(function (ai, fi) { return table[fi][ai]; }), w = worst(rs);
      var score = SEVERITY[w.status] * 100 + rs.reduce(function (t, r) { return t + SEVERITY[r.status === ST.EMPTY ? ST.UNREADABLE : r.status]; }, 0);
      if (!best || score < best.score) best = { score: score, w: w, rs: rs };
    });
    best.w.parts = best.rs; return best.w;
  }
  // 数の答えが複数（ch3-4-3 Q7 など）。opts.ordered: 順番どおりか（既定 false）
  function gradeSet(raws, answers, opts) {
    opts = opts || {};
    return matchSet(raws, answers, function (r, a) { return gradeNumber(r, a, opts); }, opts.ordered);
  }
  // 連立方程式の式を2本作る問（ch3-2-3 3(2)、renritsu-08 式①②）。欄の順は自由、1本ずつ同値
  function gradeEquationSet(raws, answers, opts) {
    var o = {}; opts = opts || {};
    for (var k in opts) if (has(opts, k)) o[k] = opts[k];
    o.mode = 'equivalent';
    return matchSet(raws, answers, function (r, a) { return gradeEquation(r, a, o); }, opts.ordered);
  }

  /* ---------- 記号（選択肢・○） ---------- */
  // expected: 'A' や ['ア','あ'] など。'○' を指定すると ○◯〇 のどれでも○
  function gradeChoice(raw, expected) {
    var s = zenToHan(toStr(raw)).replace(/\\text\{([^{}]*)\}/g, '$1').replace(/[\s\u3000]/g, '');
    if (s === '') return res(ST.EMPTY, 'empty');
    s = s.replace(/[\u25EF\u3007\u2B55]/g, '○').toUpperCase();
    var list = Array.isArray(expected) ? expected : [expected];
    for (var i = 0; i < list.length; i++) {
      var e = zenToHan(String(list[i])).replace(/[\u25EF\u3007\u2B55]/g, '○').toUpperCase();
      if (s === e) return res(ST.CORRECT, '');
    }
    return res(ST.WRONG, 'choice');
  }

  /* ---------- 画面・得点・記録 ---------- */
  function points(r) { return (r && r.status) === ST.CORRECT ? 1 : 0; }
  function isCorrect(r) { return (r && r.status) === ST.CORRECT; } // 記録の正誤欄（boolean）
  function mark(r) {
    var st = r && r.status;
    return st === ST.CORRECT ? '○' : st === ST.NEG_DEN ? '△' : '×';
  }
  function message(r) {
    if (!r || r.status === ST.CORRECT || r.status === ST.EMPTY) return '';
    if (has(MESSAGES, r.reason)) return MESSAGES[r.reason];
    return has(MESSAGES, r.status) ? MESSAGES[r.status] : '';
  }
  // 記録用の印。［△分母のマイナス］［未約分］［未整理］［左右］のどれか、または ''
  function recordTag(r) {
    if (!r) return '';
    if (r.status === ST.NEG_DEN) return TAGS.negDenominator;
    return has(TAGS, r.reason) ? TAGS[r.reason] : '';
  }
  // 記録する answer の文字（生の入力）の末尾に印を付ける
  function tagAnswer(text, r) { var t = recordTag(r); return toStr(text) + (t ? ' ' + t : ''); }

  /* ---------- 入力欄の設定（値は書き換えない。全角・半角は採点時にそろえる） ---------- */
  function onEnterKey(el, fn) {
    el.addEventListener('keydown', function (e) {
      // IME 変換中の Enter（確定のための Enter）では提出しない
      if (e.key === 'Enter' && !e.isComposing && e.keyCode !== 229) { e.preventDefault(); fn(e); }
    }, { capture: true });
  }
  function setupMathField(mf, opts) {
    if (!mf) return;
    opts = opts || {};
    mf.removeAttribute('virtual-keyboard-mode'); // 0.98 では効かない古い属性
    // 'auto': タッチ端末では欄をタップすると仮想キーボードが出る（0.98.4 の欄は inputmode="none" で
    // OS のキーボードが出ないため、'manual' にするとタッチで入力できなくなる）。物理キーボードでは出ない。
    mf.setAttribute('math-virtual-keyboard-policy', 'auto');
    try { mf.mathVirtualKeyboardPolicy = 'auto'; } catch (e) { /* 定義前の欄でも属性で効く */ }
    if (opts.onEnter) onEnterKey(mf, opts.onEnter);
  }
  function setupTextInput(inp, opts) {
    if (!inp) return;
    opts = opts || {};
    if (inp.type === 'number') inp.type = 'text'; // number 型は全角や「-」の途中で値が空になる
    inp.setAttribute('autocomplete', 'off');
    inp.setAttribute('autocapitalize', 'off');
    inp.setAttribute('spellcheck', 'false');
    if (opts.onEnter) onEnterKey(inp, opts.onEnter);
  }

  return {
    VERSION: 'v1.3', STATUS: ST, MESSAGES: MESSAGES, TAGS: TAGS,
    normalize: normalize, isBlank: isBlank, hasEmptySlot: hasEmptySlot,
    gradeNumber: gradeNumber, gradeLinear: gradeLinear, gradeEquation: gradeEquation,
    gradeTuple: gradeTuple, gradeRange: gradeRange, gradeSet: gradeSet, gradeEquationSet: gradeEquationSet,
    gradeChoice: gradeChoice,
    worst: worst, points: points, isCorrect: isCorrect, mark: mark, message: message,
    recordTag: recordTag, tagAnswer: tagAnswer,
    setupMathField: setupMathField, setupTextInput: setupTextInput
  };
})();
// ===== GRADER-CORE END v1 =====
if (typeof module !== 'undefined' && module.exports) module.exports = GraderCore;
