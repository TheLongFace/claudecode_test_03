// かきかきかき 採点エンジン
// 一筆の座標列から「牡蠣度」「柿度」「餓鬼度」を 0〜100 で出す。
// 柿と牡蠣は「閉じたループ」の形で判定する。ループは一筆全体（始点と終点が近いとき）と、
// 線が自分と交差してできた部分ループの両方から探す。だから「餓鬼が柿を持ってる絵」でも、
// 中の丸いループが柿として拾われる。餓鬼は一筆全体のゴチャつき具合で判定する。
(function (root) {
  const clamp = (v, lo = 0, hi = 1) => Math.max(lo, Math.min(hi, v));
  const dist = (a, b) => Math.hypot(a.x - b.x, a.y - b.y);
  const gauss = (v, mu, sd) => Math.exp(-(((v - mu) / sd) ** 2));

  function pathLength(pts, closed) {
    let L = 0;
    for (let i = 1; i < pts.length; i++) L += dist(pts[i - 1], pts[i]);
    if (closed && pts.length > 1) L += dist(pts[pts.length - 1], pts[0]);
    return L;
  }

  // 等間隔に n 点へ打ち直す
  function resample(pts, n, closed) {
    const src = closed ? pts.concat([pts[0]]) : pts;
    const L = pathLength(src, false);
    if (L === 0) return src.slice(0, 1);
    const step = L / (closed ? n : n - 1);
    const out = [{ x: src[0].x, y: src[0].y }];
    let acc = 0;
    for (let i = 1; i < src.length && out.length < n; i++) {
      let a = src[i - 1];
      const b = src[i];
      let d = dist(a, b);
      while (acc + d >= step && out.length < n) {
        const t = (step - acc) / d;
        const p = { x: a.x + (b.x - a.x) * t, y: a.y + (b.y - a.y) * t };
        out.push(p);
        a = p;
        d = dist(a, b);
        acc = 0;
      }
      acc += d;
    }
    while (out.length < n) out.push({ ...src[src.length - 1] });
    return out;
  }

  function bbox(pts) {
    let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
    for (const p of pts) {
      if (p.x < minX) minX = p.x;
      if (p.y < minY) minY = p.y;
      if (p.x > maxX) maxX = p.x;
      if (p.y > maxY) maxY = p.y;
    }
    return { minX, minY, maxX, maxY, w: maxX - minX, h: maxY - minY };
  }

  function area(pts) {
    let s = 0;
    for (let i = 0; i < pts.length; i++) {
      const a = pts[i], b = pts[(i + 1) % pts.length];
      s += a.x * b.y - b.x * a.y;
    }
    return Math.abs(s) / 2;
  }

  function hull(pts) {
    const p = pts.slice().sort((a, b) => a.x - b.x || a.y - b.y);
    if (p.length < 3) return p;
    const cross = (o, a, b) => (a.x - o.x) * (b.y - o.y) - (a.y - o.y) * (b.x - o.x);
    const lower = [], upper = [];
    for (const q of p) {
      while (lower.length >= 2 && cross(lower[lower.length - 2], lower[lower.length - 1], q) <= 0) lower.pop();
      lower.push(q);
    }
    for (let i = p.length - 1; i >= 0; i--) {
      const q = p[i];
      while (upper.length >= 2 && cross(upper[upper.length - 2], upper[upper.length - 1], q) <= 0) upper.pop();
      upper.push(q);
    }
    return lower.slice(0, -1).concat(upper.slice(0, -1));
  }

  // 主軸（PCA）: 細長さと向き
  function principal(pts) {
    let cx = 0, cy = 0;
    for (const p of pts) { cx += p.x; cy += p.y; }
    cx /= pts.length; cy /= pts.length;
    let sxx = 0, syy = 0, sxy = 0;
    for (const p of pts) {
      const dx = p.x - cx, dy = p.y - cy;
      sxx += dx * dx; syy += dy * dy; sxy += dx * dy;
    }
    const tr = sxx + syy, det = sxx * syy - sxy * sxy;
    const disc = Math.sqrt(Math.max(0, tr * tr / 4 - det));
    const l1 = tr / 2 + disc, l2 = Math.max(1e-9, tr / 2 - disc);
    const ang = 0.5 * Math.atan2(2 * sxy, sxx - syy);
    return { cx, cy, elong: Math.sqrt(l1 / l2), ux: Math.cos(ang), uy: Math.sin(ang) };
  }

  // 各点での曲がり角（符号つき, rad）
  function turning(pts, k, closed) {
    const n = pts.length, out = new Array(n).fill(0);
    for (let i = 0; i < n; i++) {
      let a = i - k, c = i + k;
      if (closed) { a = (a + n) % n; c = c % n; }
      else if (a < 0 || c >= n) continue;
      const p = pts[a], q = pts[i], r = pts[c];
      const a1 = Math.atan2(q.y - p.y, q.x - p.x), a2 = Math.atan2(r.y - q.y, r.x - q.x);
      let d = a2 - a1;
      while (d > Math.PI) d -= 2 * Math.PI;
      while (d < -Math.PI) d += 2 * Math.PI;
      out[i] = d;
    }
    return out;
  }

  // 曲がる向きが何回切り替わったか（ギザギザ・フリル度）
  function signFlips(th, idx, thr) {
    let flips = 0, last = 0;
    for (const i of idx) {
      const t = th[i];
      if (Math.abs(t) < thr) continue;
      const s = Math.sign(t);
      if (last && s !== last) flips++;
      last = s;
    }
    return flips;
  }

  function segIntersect(p1, p2, p3, p4) {
    const d = (p2.x - p1.x) * (p4.y - p3.y) - (p2.y - p1.y) * (p4.x - p3.x);
    if (d === 0) return false;
    const t = ((p3.x - p1.x) * (p4.y - p3.y) - (p3.y - p1.y) * (p4.x - p3.x)) / d;
    const u = ((p3.x - p1.x) * (p2.y - p1.y) - (p3.y - p1.y) * (p2.x - p1.x)) / d;
    return t > 0 && t < 1 && u > 0 && u < 1;
  }

  function intersections(pts) {
    const out = [];
    for (let i = 0; i < pts.length - 1; i++) {
      for (let j = i + 2; j < pts.length - 1; j++) {
        if (segIntersect(pts[i], pts[i + 1], pts[j], pts[j + 1])) out.push([i, j]);
      }
    }
    return out;
  }

  // 1つのループを柿・牡蠣の目で見る
  function judgeLoop(rawLoop, closure, corners) {
    const loop = resample(rawLoop, 96, true);
    const bb = bbox(loop);
    const A = area(loop);
    const H = hull(loop);
    const Ah = Math.max(1e-6, area(H));
    const Ph = pathLength(H, true);
    const hullCirc = (4 * Math.PI * Ah) / (Ph * Ph);
    const solidity = clamp(A / Ah);
    const pc = principal(loop);
    const th = turning(loop, 2, true);

    // ループ自体がぐちゃぐちゃに交差してたら、それは柿でも牡蠣でもなく落書き
    const messy = 1 / (1 + 0.3 * Math.max(0, intersections(loop).length - 4));

    // 柿: まんまる + なめらか + 上にへた
    const lowerIdx = [];
    loop.forEach((p, i) => { if (p.y > bb.minY + 0.35 * bb.h) lowerIdx.push(i); });
    const lowerFlips = signFlips(th, lowerIdx, 0.14);
    const hetaCorners = corners.filter(p =>
      p.x > bb.minX - 0.15 * bb.w && p.x < bb.maxX + 0.15 * bb.w &&
      p.y > bb.minY - 0.45 * bb.h && p.y < bb.minY + 0.3 * bb.h).length;
    const kRound = clamp((hullCirc - 0.8) / 0.16);
    const kAspect = gauss(pc.elong, 1.05, 0.3);
    const kSmooth = 1 - clamp((lowerFlips - 1) / 6);
    const kHeta = clamp(hetaCorners / 3);
    const kFill = clamp((solidity - 0.7) / 0.2);
    const kaki = 100 * closure * messy * kFill ** 0.5 *
      (0.35 * kRound + 0.25 * kAspect + 0.15 * kSmooth + 0.25 * kHeta);

    // 牡蠣: ちょい細長い涙型 + フチがフリフリ
    const flips = signFlips(th, loop.map((_, i) => i), 0.14);
    let bins = [[Infinity, -Infinity], [Infinity, -Infinity], [Infinity, -Infinity]];
    const us = loop.map(p => (p.x - pc.cx) * pc.ux + (p.y - pc.cy) * pc.uy);
    const uMin = Math.min(...us), uMax = Math.max(...us);
    loop.forEach((p, i) => {
      const v = -(p.x - pc.cx) * pc.uy + (p.y - pc.cy) * pc.ux;
      const b = Math.min(2, Math.floor(((us[i] - uMin) / (uMax - uMin + 1e-9)) * 3));
      bins[b][0] = Math.min(bins[b][0], v);
      bins[b][1] = Math.max(bins[b][1], v);
    });
    const wEnd0 = Math.max(0, bins[0][1] - bins[0][0]), wEnd2 = Math.max(0, bins[2][1] - bins[2][0]);
    const oElong = gauss(pc.elong, 1.9, 0.6);
    const oRuffle = clamp((flips - 2) / 12);
    const oTear = clamp((Math.abs(wEnd0 - wEnd2) / Math.max(wEnd0, wEnd2, 1e-6)) * 2.5);
    const oSolid = clamp((solidity - 0.6) / 0.25);
    const oyster = 100 * closure * messy *
      (0.25 * oElong + 0.45 * oRuffle + 0.1 * oTear + 0.2 * oSolid);

    return {
      kaki: clamp(kaki, 0, 100),
      oyster: clamp(oyster, 0, 100),
      loop: rawLoop,
      detail: { hullCirc, solidity, elong: pc.elong, flips, lowerFlips, hetaCorners },
    };
  }

  function score(rawPts) {
    const empty = { oyster: 0, kaki: 0, gaki: 0, tooShort: true };
    if (!rawPts || rawPts.length < 5) return empty;
    const L0 = pathLength(rawPts, false);
    const bb0 = bbox(rawPts);
    const D = Math.hypot(bb0.w, bb0.h);
    if (L0 < 40 || D < 25) return empty;

    const n = clamp(Math.round(L0 / (D * 0.02)), 120, 320);
    const pts = resample(rawPts, n, false);
    const bb = bbox(pts);

    const th2 = turning(pts, 2, false);
    const corners = [];
    for (let i = 0; i < pts.length; i++) {
      // 周り3点の中で一番曲がった点だけ数える
      if (Math.abs(th2[i]) > 1.05 &&
          Math.abs(th2[i]) >= Math.abs(th2[i - 1] || 0) &&
          Math.abs(th2[i]) >= Math.abs(th2[i + 1] || 0)) corners.push(pts[i]);
    }

    const X = intersections(pts);

    // ループ候補
    const candidates = [];
    const gap = dist(pts[0], pts[pts.length - 1]);
    const closure = clamp(1 - (gap / D - 0.12) / 0.3);
    if (closure > 0) candidates.push({ pts, closure });
    for (const [i, j] of X) {
      const loop = pts.slice(i + 1, j + 1);
      if (loop.length < 12) continue;
      const lb = bbox(loop);
      if (pathLength(loop, true) < 0.15 * L0 || lb.w * lb.h < 0.02 * bb.w * bb.h) continue;
      candidates.push({ pts: loop, closure: 1 });
    }

    let bestKaki = { kaki: 0, loop: null }, bestOyster = { oyster: 0, loop: null };
    for (const c of candidates) {
      const j = judgeLoop(c.pts, c.closure, corners);
      if (j.kaki > bestKaki.kaki) bestKaki = j;
      if (j.oyster > bestOyster.oyster) bestOyster = j;
    }

    // 餓鬼: 交差だらけ・トゲトゲ・線が多い・縦長
    const ink = L0 / (2 * (bb0.w + bb0.h) + 1e-6);
    const gX = clamp((X.length - 2) / 6); // へたの交差くらいは見逃す
    const gCorner = clamp((corners.length - 3) / 8);
    const gInk = clamp((ink - 0.9) / 1.6);
    const gTall = clamp((bb.h / (bb.w + 1e-6) - 0.9) / 0.9);
    const gaki = 100 * (0.3 * gX + 0.25 * gCorner + 0.3 * gInk + 0.15 * gTall);

    return {
      oyster: Math.round(bestOyster.oyster),
      kaki: Math.round(bestKaki.kaki),
      gaki: Math.round(clamp(gaki, 0, 100)),
      oysterLoop: bestOyster.oyster > 25 ? bestOyster.loop : null,
      kakiLoop: bestKaki.kaki > 25 ? bestKaki.loop : null,
      stats: {
        crossings: X.length, corners: corners.length, ink: +ink.toFixed(2),
        kakiDetail: bestKaki.detail, oysterDetail: bestOyster.detail,
      },
    };
  }

  // 合計: 一番高いやつをそのまま、残りも少しずつ足す（満点は100、越えたら限界突破）
  function total(s) {
    const v = [s.oyster, s.kaki, s.gaki].sort((a, b) => b - a);
    return Math.round(v[0] + 0.5 * v[1] + 0.25 * v[2]);
  }

  const api = { score, total };
  if (typeof module !== "undefined" && module.exports) module.exports = api;
  else root.KakiScore = api;
})(this);
