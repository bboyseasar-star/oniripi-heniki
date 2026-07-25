'use strict';

const HenikiQuestions = (() => {
  const rnd = (a, b) => Math.floor(Math.random() * (b - a + 1)) + a;
  const choice = arr => arr[rnd(0, arr.length - 1)];
  const gcd = (a, b) => {
    a = Math.abs(a); b = Math.abs(b);
    while (b) [a, b] = [b, a % b];
    return a || 1;
  };
  const frac = (n, d = 1) => {
    if (d < 0) { n = -n; d = -d; }
    const g = gcd(n, d);
    return { n: n / g, d: d / g };
  };
  const add = (a, b) => frac(a.n * b.d + b.n * a.d, a.d * b.d);
  const mul = (a, b) => frac(a.n * b.n, a.d * b.d);
  const val = f => f.n / f.d;
  const fx = (a, b, x) => add(mul(a, frac(x)), b);
  const minmax = (a, b) => val(a) <= val(b) ? [a, b] : [b, a];
  const tex = f => {
    if (f.d === 1) return String(f.n);
    return f.n < 0 ? `-\\frac{${Math.abs(f.n)}}{${f.d}}` : `\\frac{${f.n}}{${f.d}}`;
  };
  const fmt = f => f.d === 1 ? String(f.n) : `${f.n}/${f.d}`;
  const linetex = (a, b) => {
    const A = tex(a);
    let s = A === '1' ? 'x' : A === '-1' ? '-x' : `${A}x`;
    if (b.n > 0) s += `+${tex(b)}`;
    if (b.n < 0) s += tex(b);
    return s;
  };
  const bankA = lv => {
    const a = lv === 1
      ? frac(rnd(1, 5))
      : choice([frac(-5), frac(-4), frac(-3), frac(-2), frac(-1), frac(1), frac(2), frac(3), frac(4), frac(5), frac(1, 2), frac(-1, 2)]);
    const b = frac(rnd(-8, 8));
    const x1 = rnd(-6, 4), x2 = x1 + rnd(2, 7);
    const y1 = fx(a, b, x1), y2 = fx(a, b, x2), [lo, hi] = minmax(y1, y2);
    return {
      id: crypto.randomUUID ? crypto.randomUUID() : String(Date.now() + Math.random()),
      type: 'A', a, b, x1, x2, y1, y2, answers: [lo, hi],
      label: '\\( x \\) の変域から \\( y \\) の変域を求めなさい',
      question: `\\( y=${linetex(a, b)} \\) で、\\( ${x1}\\leqq x\\leqq ${x2} \\) のとき、\\( y \\) の変域を求めなさい。`,
      extra: a.n < 0 ? '右下がりの直線なので、端の対応が逆になります。' : '右上がりの直線なので、\\( x \\) と \\( y \\) は同じ向きに増えます。',
      hints: [
        `\\( x \\) の変域の両端、\\( x=${x1} \\) と \\( x=${x2} \\) を代入します。`,
        `\\( x=${x1} \\) のとき \\( y=${tex(y1)} \\)、\\( x=${x2} \\) のとき \\( y=${tex(y2)} \\) です。`,
        `${a.n < 0 ? '\\( a<0 \\) なので大小が逆転します。' : '\\( a>0 \\) なのでそのまま並びます。'} 答えは \\( ${tex(lo)}\\leqq y\\leqq ${tex(hi)} \\) です。`
      ],
      process: `両端を代入して \\( ${tex(y1)} \\), \\( ${tex(y2)} \\) を出し、小さい順に並べます。`
    };
  };
  const bankB = () => {
    const a = choice([frac(-4), frac(-3), frac(-2), frac(-1), frac(1), frac(2), frac(3), frac(4), frac(1, 2), frac(-1, 2)]);
    const b = frac(rnd(-6, 6));
    const x1 = rnd(-5, 3), x2 = x1 + rnd(2, 6);
    const y1 = fx(a, b, x1), y2 = fx(a, b, x2), [ylo, yhi] = minmax(y1, y2);
    const yForX1 = y1;
    const yForX2 = y2;
    const left1 = tex(add(yForX1, frac(-b.n, b.d)));
    return {
      id: crypto.randomUUID ? crypto.randomUUID() : String(Date.now() + Math.random()),
      type: 'B', a, b, x1, x2, y1, y2, answers: [frac(x1), frac(x2)],
      label: '\\( y \\) の変域から \\( x \\) の変域を求めなさい',
      question: `\\( y=${linetex(a, b)} \\) で、\\( ${tex(ylo)}\\leqq y\\leqq ${tex(yhi)} \\) のとき、\\( x \\) の変域を求めなさい。`,
      extra: '\\( y \\) の端の値を \\( x \\) に戻して考えます。',
      hints: [
        `\\( y \\) の変域の端の値を、元の式 \\( y=${linetex(a, b)} \\) の \\( y \\) に1つずつ代入します。`,
        `まず \\( y=${tex(yForX1)} \\) を代入すると、\\( ${tex(yForX1)}=${linetex(a, b)} \\) です。この方程式を \\( x \\) について解きます。`,
        `定数項 \\( ${tex(b)} \\) を左辺へ移すと \\( ${left1}=${tex(a)}x \\)。両辺を \\( ${tex(a)} \\) で割って、\\( x=${x1} \\) です。`,
        `次に \\( y=${tex(yForX2)} \\) を代入します。\\( ${tex(yForX2)}=${linetex(a, b)} \\) を同じように解くと、\\( x=${x2} \\) です。`,
        `求めた2つの値を小さい順に並べます。答えは \\( ${x1}\\leqq x\\leqq ${x2} \\) です。`
      ],
      process: `\\( y \\) の両端を元の式へ1つずつ代入し、それぞれの方程式を \\( x \\) について解いて、小さい順に並べます。`
    };
  };
  const bankC = () => {
    const a = choice([frac(-4), frac(-3), frac(-2), frac(-1), frac(1), frac(2), frac(3), frac(4)]);
    const b = frac(rnd(-6, 6));
    const x1 = rnd(-4, 3), x2 = x1 + rnd(2, 5);
    const y1 = fx(a, b, x1), y2 = fx(a, b, x2), [ylo, yhi] = minmax(y1, y2);
    const eq1 = `${x1 === 1 ? '' : x1 === -1 ? '-' : x1}a+b=${tex(y1)}`;
    const eq2 = `${x2 === 1 ? '' : x2 === -1 ? '-' : x2}a+b=${tex(y2)}`;
    const dx = x2 - x1;
    const dy = add(y2, frac(-y1.n, y1.d));
    return {
      id: crypto.randomUUID ? crypto.randomUUID() : String(Date.now() + Math.random()),
      type: 'C', a, b, x1, x2, y1, y2, answers: [a, b],
      label: '変域から \\( a,b \\) を求めなさい',
      question: `\\( y=ax+b \\) で、\\( a${a.n > 0 ? '>' : '<'}0 \\)、\\( ${x1}\\leqq x\\leqq ${x2} \\) のとき \\( ${tex(ylo)}\\leqq y\\leqq ${tex(yhi)} \\) である。\\( a,b \\) の値を求めなさい。`,
      extra: '端点どうしの対応を見つけるのがポイントです。',
      hints: [
        a.n > 0 ? '右上がりなので小さい \\( x \\) に小さい \\( y \\) が対応します。' : '右下がりなので小さい \\( x \\) に大きい \\( y \\) が対応します。',
        `対応する端点は \\( (${x1},${tex(y1)}) \\) と \\( (${x2},${tex(y2)}) \\) です。まず、それぞれを \\( y=ax+b \\) に代入します。`,
        `代入すると、次の連立方程式ができます。\\[\\begin{cases}${eq1}\\\\[4pt]${eq2}\\end{cases}\\]`,
        `2つ目の式から1つ目の式を引くと、\\( ${dx}a=${tex(dy)} \\) です。両辺を \\( ${dx} \\) で割って、\\( a=${tex(a)} \\) となります。`,
        `\\( a=${tex(a)} \\) を \\( ${eq1} \\) に戻して、\\( b=${tex(b)} \\)。答えは \\( a=${tex(a)},\\ b=${tex(b)} \\) です。`
      ],
      process: `端点を \\( y=ax+b \\) に代入して連立方程式を作り、2式を引いて \\( a \\) を求めたあと、元の式へ代入して \\( b \\) を求めます。`
    };
  };
  const bankD = () => {
    const a = choice([frac(-3), frac(-2), frac(-1), frac(1), frac(2), frac(3)]);
    const b = frac(rnd(-4, 4));
    const x1 = rnd(-5, 2), x2 = x1 + rnd(3, 6);
    const y1 = fx(a, b, x1), y2 = fx(a, b, x2), [ylo, yhi] = minmax(y1, y2);
    return {
      id: crypto.randomUUID ? crypto.randomUUID() : String(Date.now() + Math.random()),
      type: 'D', a, b, x1, x2, y1, y2, answers: [frac(x1), frac(x2), ylo, yhi],
      label: 'グラフから \\( x,y \\) の変域を読み取りなさい',
      question: '太線部分を見て、\\( x \\) の変域と \\( y \\) の変域を答えなさい。',
      extra: '赤い点が変域の両端です。',
      hints: [
        '太線の左右の端の \\( x \\) 座標を読み取ります。',
        `端点は \\( (${x1},${tex(y1)}) \\) と \\( (${x2},${tex(y2)}) \\) です。`,
        `\\( x \\) は \\( ${x1}\\leqq x\\leqq ${x2} \\)、\\( y \\) は \\( ${tex(ylo)}\\leqq y\\leqq ${tex(yhi)} \\) です。`
      ],
      process: '端点の座標を読み取り、\\( x \\) 座標と \\( y \\) 座標をそれぞれ小さい順に並べます。'
    };
  };
  const make = level => {
    const makers = level === 1 ? [() => bankA(1)] : level === 2 ? [() => bankA(2), bankB] : [() => bankA(3), bankB, bankC, bankD];
    return Array.from({ length: 5 }, () => choice(makers)());
  };
  return { make, tex, fmt, val, fx };
})();
