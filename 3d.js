// Signal Box Simulator: first-person / overview 3D renderer.
// Loaded on demand by index.html when "3D" is picked on the start menu; needs three.js (r128) and window.SBS from the engine.
(() => {
'use strict';
const A = window.SBS, $ = A.$;
const U = .1, X3 = A.X3, Z3 = A.Z3, ROAD_X = A.ROAD_X;
let S, SC, B3, view, renderer, camera, scene, booted = false, camMode = 'box', locked = false, yaw0 = 0, th = 0;
const interactives = [], mats = {}, insts = {};
const modeLook = { box: { yaw: 0, pitch: 0 }, walk: { yaw: 0, pitch: 0 } }, walk = { x: 0, z: 0, sy: 0, eye: 0 };
let sigLamps = {}, trainMeshes = new Map(), carMeshes = new Map(), last3d = performance.now();
const MODES = ['box', 'walk', 'over'], WH = 2.6;

// ---- helpers ------------------------------------------------------------
const mat = c => mats[c] || (mats[c] = new THREE.MeshLambertMaterial({ color: c }));
const glow = c => new THREE.MeshBasicMaterial({ color: c });
function box(w, h, d, color, x, y, z, parent = scene, shadow = true) {
  const m = new THREE.Mesh(new THREE.BoxGeometry(w, h, d), typeof color === 'number' ? mat(color) : color);
  m.position.set(x, y, z); m.castShadow = shadow; m.receiveShadow = true; parent.add(m); return m;
}
const hitMat = new THREE.MeshBasicMaterial({ transparent: true, opacity: 0, depthWrite: false });
function hitbox(geo, x, y, z, parent, data, rot) {
  const m = new THREE.Mesh(geo, hitMat); m.position.set(x, y, z); if (rot) m.rotation.set(rot[0], rot[1], rot[2]);
  m.userData = data; parent.add(m); interactives.push(m); return m;
}
function label(lines, w, h, fg = '#f2e6c0', bg = '#1d1a16') {
  const c = document.createElement('canvas'); c.width = 256; c.height = Math.round(256 * h / w);
  const g = c.getContext('2d'); g.fillStyle = bg; g.fillRect(0, 0, c.width, c.height); g.fillStyle = fg; g.textAlign = 'center'; g.textBaseline = 'middle';
  lines.forEach((t, i) => { g.font = 'bold ' + Math.floor(c.height / (lines.length + .7)) + 'px sans-serif'; g.fillText(t, c.width / 2, c.height * (i + .5) / lines.length); });
  return new THREE.Mesh(new THREE.PlaneGeometry(w, h), new THREE.MeshBasicMaterial({ map: new THREE.CanvasTexture(c) }));
}
const sphere = (r, color) => new THREE.Mesh(new THREE.SphereGeometry(r, 12, 8), glow(color));

function newScene() {
  scene = new THREE.Scene(); interactives.length = 0; for (const k in insts) delete insts[k];
  scene.background = new THREE.Color(0xa9cfe8); scene.fog = new THREE.Fog(0xa9cfe8, 80, 280);
  scene.add(new THREE.HemisphereLight(0xd8ecff, 0x4a6a3a, .85));
  const sun = new THREE.DirectionalLight(0xfff0d0, 1.1);
  sun.position.set(35, 55, 25); sun.castShadow = true; sun.shadow.mapSize.set(2048, 2048);
  Object.assign(sun.shadow.camera, { left: -70, right: 70, top: 70, bottom: -70, near: 1, far: 220 });
  scene.add(sun);
}

// ---- the world: ground, road or path, any number of tracks, crossing deck, trees ----------
// o: tracks (sim y px), skew (road tan angle), roadW, roadColor, roadZ, centre, deckColor, trees, treeSkip, poles
function buildWorld(o) {
  const zs = o.tracks.map(Z3), zmin = Math.min(...zs) - 2, zmax = Math.max(...zs) + 2, k = o.skew || 0, a = Math.atan(k), rw = o.roadW || 6;
  th = a;
  const g = new THREE.Mesh(new THREE.PlaneGeometry(800, 800), mat(0x426f36)); g.rotation.x = -Math.PI / 2; g.receiveShadow = true; scene.add(g);
  const [rz0, rz1] = o.roadZ || [-400, 400];
  const road = box(rw, .05, rz1 - rz0, o.roadColor || 0x44474c, 0, .03, (rz0 + rz1) / 2, scene, false); road.rotation.y = a;
  if (o.centre !== false) for (let z = -300; z < 300; z += 4) if ((z < zmin - 1 || z > zmax + 1) && z > rz0 && z < rz1) { const d = box(.12, .02, 2, 0xdcdccc, z * k, .07, z, scene, false); d.rotation.y = a; }
  for (const z of zs) {
    box(560, .2, 3, 0x7a746a, 0, .1, z, scene, false);
    const sl = new THREE.InstancedMesh(new THREE.BoxGeometry(.3, .12, 2.4), mat(0x4b3a2a), 700), m = new THREE.Matrix4();
    for (let i = 0; i < 700; i++) { m.setPosition(-280 + i * .8, .26, z); sl.setMatrixAt(i, m); }
    sl.receiveShadow = true; scene.add(sl);
    for (const dz of [-.72, .72]) box(560, .16, .1, 0xa5abb1, 0, .38, z + dz, scene, false);
  }
  const deck = box(rw, .34, (zmax - zmin) / Math.cos(a), o.deckColor || 0x2c2e32, ((zmax + zmin) / 2) * k, .17, (zmax + zmin) / 2, scene, false); deck.rotation.y = a;
  for (const z of zs) for (const dz of [-.72, .72]) box(rw / Math.cos(a) + .3, .1, .1, 0xa5abb1, (z + dz) * k, .38, z + dz, scene, false);
  if (o.poles) for (let x = -250; x <= 250; x += 25) if (Math.abs(x) > 8) { box(.15, 6, .15, 0x5b4630, x, 3, o.poles); box(1.6, .12, .12, 0x5b4630, x, 5.7, o.poles); }
  let seed = 7; const rnd = () => (seed = (seed * 16807) % 2147483647) / 2147483647;
  const trunkG = new THREE.CylinderGeometry(.25, .35, 2, 6), leafG = new THREE.ConeGeometry(1.8, 5, 7);
  for (let i = 0, n = o.trees || 260; i < n; i++) {
    const x = (rnd() - .5) * 280, z = (rnd() - .5) * 280;
    if (Math.abs(x - z * k) < 8 || (z > zmin - 2 && z < zmax + 2) || (o.treeSkip && o.treeSkip(x, z))) continue;
    const s = .8 + rnd() * .9, t = new THREE.Group(); t.position.set(x, 0, z); t.scale.setScalar(s);
    const tr = new THREE.Mesh(trunkG, mat(0x5b4630)); tr.position.y = 1; tr.castShadow = true;
    const lf = new THREE.Mesh(leafG, mat(rnd() > .5 ? 0x2f5d2c : 0x3b6e31)); lf.position.y = 4; lf.castShadow = true;
    t.add(tr, lf); scene.add(t);
  }
}

function makeSignal(cfg) {
  const g = new THREE.Group(); g.position.set(X3(cfg.x), 0, Z3(cfg.y)); scene.add(g);
  const side = -cfg.dir * .22;
  box(.16, 4.4, .16, 0xcfd3d6, 0, 2.2, 0, g); box(.5, 1.5, .4, 0x151515, 0, 4.6, 0, g);
  const red = sphere(.17, 0xff3030), grn = sphere(.17, 0x30ff70);
  red.position.set(side, 4.95, 0); grn.position.set(side, 4.35, 0); g.add(red, grn);
  box(.9, .06, .06, 0x151515, side * 1.0, 5.45, 0, g, false);
  return { red, grn };
}

// ---- the signal box: raised room, windows west and south, optional door in the east wall -------
function buildRoom(sbox, floorY, door) {
  const wall = 0xe8e2d0, wood = 0x6a4a35, wy = floorY + WH / 2;
  box(7.6, floorY - .2, 5.8, 0x8a4f37, 0, (floorY - .2) / 2, 0, sbox);
  box(7.6, .2, 5.6, 0x8a6a45, 0, floorY - .1, 0, sbox, false);
  box(7.8, WH, .2, wall, 0, wy, -2.6, sbox);
  if (door) { box(.2, WH, 1.8, wall, 3.6, wy, -1.7, sbox); box(.2, WH, 1.8, wall, 3.6, wy, 1.7, sbox); box(.2, .6, 1.6, wall, 3.6, floorY + 2.3, 0, sbox); }
  else box(.2, WH, 5.8, wall, 3.6, wy, 0, sbox);
  box(.2, 1, 5.8, wood, -3.6, floorY + .5, 0, sbox); box(.2, .6, 5.8, wall, -3.6, floorY + 2.3, 0, sbox);
  for (const z of [-2.6, -1.3, 0, 1.3, 2.6]) box(.2, 1, .14, wall, -3.6, floorY + 1.5, z, sbox);
  box(7.8, 1, .2, wood, 0, floorY + .5, 2.6, sbox); box(7.8, .6, .2, wall, 0, floorY + 2.3, 2.6, sbox);
  for (const x of [-3.6, -1.2, 1.2]) box(.14, 1, .2, wall, x, floorY + 1.5, 2.6, sbox);
  const roof = box(8.6, .3, 6.6, 0x4d4d55, 0, floorY + WH + .15, 0, sbox);
  const pl = new THREE.PointLight(0xffe2b0, .8, 14); pl.position.set(0, floorY + 2.2, 0); sbox.add(pl);
  return roof;
}
function buildLevers(sbox, floorY) {
  const levers = [];
  box(3.4, .3, .6, 0x2b2b30, 0, floorY + .15, -2.2, sbox);
  for (let i = 0; i < 6; i++) {
    const x = -1.25 + i * .5, sig = SC.signals[i];
    const pivot = new THREE.Group(); pivot.position.set(x, floorY + .3, -2.15); sbox.add(pivot);
    box(.07, 1.3, .07, 0x8d9399, 0, .65, 0, pivot); box(.11, .36, .15, sig ? 0xd22a22 : 0x222222, 0, 1.4, 0, pivot);
    hitbox(new THREE.BoxGeometry(.4, 1.7, .5), 0, .8, 0, pivot, sig ? { act: 'lever', id: sig.id } : { act: 'spare' });
    levers.push({ pivot, id: sig && sig.id });
    const plate = label(sig ? [String(i + 1), sig.name.toUpperCase().replace(' SIGNAL', ' SIG')] : [String(i + 1), 'SPARE'], .44, .32); plate.position.set(x, floorY + 1.9, -2.49); sbox.add(plate);
  }
  return levers;
}
function makeInst(sbox, floorY, sig, z) {
  const c = document.createElement('canvas'); c.width = 256; c.height = 320; const tex = new THREE.CanvasTexture(c);
  const body = box(.28, .9, .7, 0x5b3a22, 3.35, floorY + 1.45, z, sbox); body.userData = { act: 'inst', id: sig.id }; interactives.push(body);
  const face = new THREE.Mesh(new THREE.PlaneGeometry(.62, .78), new THREE.MeshBasicMaterial({ map: tex }));
  face.position.set(3.35 - .146, floorY + 1.45, z); face.rotation.y = -Math.PI / 2; sbox.add(face);
  insts[sig.id] = { c, tex, title: sig.name.toUpperCase(), last: '' };
}
function drawInst(id, now) {
  const I = insts[id], st = S.inst[id], blink = st === 'offered' ? Math.floor(now * 2.5) % 2 : 0, key = st + blink;
  if (I.last === key) return; I.last = key;
  const g = I.c.getContext('2d'); g.fillStyle = '#1b1712'; g.fillRect(0, 0, 256, 320);
  g.fillStyle = '#f2e6c0'; g.textAlign = 'center'; g.font = 'bold 30px sans-serif'; g.fillText(I.title, 128, 48);
  g.fillStyle = st === 'accepted' ? '#2ecc71' : st === 'offered' ? (blink ? '#ffb020' : '#5a4010') : '#c0392b';
  g.beginPath(); g.arc(128, 150, 62, 0, 7); g.fill();
  g.fillStyle = '#f2e6c0'; g.font = 'bold 28px sans-serif';
  g.fillText(st === 'accepted' ? 'LINE CLEAR' : st === 'offered' ? 'TRAIN OFFERED' : 'LINE BLOCKED', 128, 262);
  I.tex.needsUpdate = true;
}

// ---- trains, cars, walkers -------------------------------------------------------
function makeTrainMesh(tr) {
  const L = SC.trainLen / 10, g = new THREE.Group(), col = tr.sig.color || 0x2a4d86;
  box(L, 2.8, 2.8, col, 0, 2.2, 0, g); box(L + .05, .35, 2.85, 0xeeeeee, 0, 1.7, 0, g); box(L - .4, .25, 2.4, 0xc9ced3, 0, 3.7, 0, g);
  for (let i = -L / 2 + 1.5; i <= L / 2 - 1.5; i += 2.2) for (const s of [-1, 1]) box(1.4, .7, .05, 0x9fd3e8, i, 2.6, s * 1.42, g, false);
  box(3, .5, 2.4, 0x222222, -L / 3, .65, 0, g); box(3, .5, 2.4, 0x222222, L / 3, .65, 0, g);
  g.userData.lamps = [1, -1].map(s => { const m = sphere(.22, 0xffffff); m.position.set(s * (L / 2 + .02), 1.6, 0); g.add(m); return m; });
  scene.add(g); return g;
}
function makeCar(c) {
  const g = new THREE.Group();
  if (c.ped) {
    box(.5, .9, .4, c.col, 0, .65, 0, g); const h = sphere(.22, 0xf3d2b0); h.position.y = 1.3; g.add(h);
    g.userData.haz = { visible: false }; scene.add(g); return g;
  }
  box(1.5, .6, 3, c.col, 0, .65, 0, g); box(1.3, .55, 1.5, 0x20262c, 0, 1.2, -c.dy * .15, g);
  for (const s of [-1, 1]) { const h = new THREE.Mesh(new THREE.BoxGeometry(.28, .2, .08), glow(0xffeeaa)); h.position.set(s * .5, .7, c.dy * 1.5); g.add(h); }
  const haz = new THREE.Mesh(new THREE.BoxGeometry(1.6, .15, .1), glow(0xffa020)); haz.position.set(0, .8, -c.dy * 1.5); haz.visible = false; g.add(haz); g.userData.haz = haz;
  scene.add(g); return g;
}

// ---- crossing devices ---------------------------------------------------------------------
function postHead(x, z, dir, h, w, hh, border) {
  box(.14, h, .14, 0x4a4f56, x, h / 2, z);
  if (border) box(w + .12, hh + .12, .1, 0xe5242b, x, h + .1, z + dir * .03);
  box(w, hh, .12, 0x111111, x, h + .1, z + dir * (border ? .08 : .0));
}
const gatesBailey = () => {
  const gates = [[ROAD_X + 34, 205, -Math.PI / 2, -Math.PI], [ROAD_X - 34, 315, Math.PI / 2, 0]].map(([px, py, a0, a1]) => {
    const post = new THREE.Group(); post.position.set(X3(px), 0, Z3(py)); scene.add(post);
    const cyl = new THREE.Mesh(new THREE.CylinderGeometry(.22, .26, 1.3, 10), mat(0x555a60)); cyl.position.y = .65; cyl.castShadow = true; post.add(cyl);
    const arm = new THREE.Group(); arm.position.y = 1.2; post.add(arm);
    box(6.2, .2, .12, 0xf2f2f2, 3.1, 0, 0, arm); for (let i = 0; i < 6; i++) box(.55, .21, .13, 0xd22a22, .5 + i * 1.0, 0, 0, arm, false);
    const lamp = sphere(.2, 0x553300); lamp.position.set(0, 1.55, 0); post.add(lamp);
    return { arm, a0, a1, lamp };
  });
  return now => { const blink = S.gate > .02 && S.gate < .999 && Math.floor(now * 3) % 2; for (const gt of gates) { gt.arm.rotation.y = -(gt.a0 + (gt.a1 - gt.a0) * S.gate); gt.lamp.material.color.set(blink ? 0xffb020 : 0x553300); } };
};
const strawBarriers = () => {
  // two full barriers hanging from the east side of the skewed road, lying parallel to the rails when down
  const k = SC.crossing.skew, half = 30 * Math.sqrt(1 + k * k), arms = [];
  for (const by of [200, 320]) {
    const post = new THREE.Group(); post.position.set(((by - 260) * k + half + 5) * U, 0, Z3(by)); scene.add(post);
    box(.5, 1.1, .5, 0x555a60, 0, .55, 0, post);
    const pivot = new THREE.Group(); pivot.position.y = 1.1; post.add(pivot);
    box(7.5, .16, .12, 0xf2f2f2, -3.75, 0, 0, pivot); for (let i = 0; i < 9; i++) box(.45, .17, .13, 0xd22a22, -.45 - i * .8, 0, 0, pivot, false);
    const lamp = sphere(.2, 0x553300); lamp.position.set(.2, 1.8, 0); post.add(lamp); arms.push({ pivot, lamp });
  }
  return now => { const blink = S.gate > .02 && S.gate < .999 && Math.floor(now * 3) % 2; for (const a of arms) { a.pivot.rotation.z = -(Math.PI / 2) * (1 - S.gate); a.lamp.material.color.set(S.gate >= .999 ? 0xff3030 : blink ? 0xffb020 : 0x553300); } };
};
const trolleyGates = () => {
  // four trolley gates: each long bar slides through a box at the road edge, poking out of the back when open
  const gates = [];
  for (const by of [200, 320]) for (const s of [-1, 1]) {
    box(1.2, .9, .8, 0x555a60, s * 3.6, .45, Z3(by));
    const bar = new THREE.Group(); bar.position.set(0, .6, Z3(by)); scene.add(bar);
    box(3.8, .14, .12, 0xf2f2f2, 0, 0, 0, bar); for (let i = -1.5; i <= 1.6; i += 1) box(.4, .15, .13, 0xd22a22, i, 0, 0, bar, false);
    const lamp = sphere(.18, 0x553300); lamp.position.set(s * 3.6, 1.15, Z3(by)); scene.add(lamp); gates.push({ bar, s, lamp });
  }
  return now => {
    const g = S.gate, blink = g > .02 && g < .999 && Math.floor(now * 3) % 2;
    for (const o of gates) { const pt = (3 - 31 * g) / 10; o.bar.position.x = o.s * 3 + o.s * (pt + 1.9); o.lamp.material.color.set(g >= .999 ? 0xff3030 : blink ? 0xffb020 : 0x553300); }
  };
};
const germanBarriers = () => {
  // four booms, both sides of the line and both halves of the road, rising and falling together; flashing red lamps under a St Andrew's cross
  const arms = [], lamps = [];
  for (const zz of [-9, 9]) for (const s of [1, -1]) {
    const post = new THREE.Group(); post.position.set(-s * 3.4, 0, zz); scene.add(post);
    box(.4, 1.1, .4, 0x555a60, 0, .55, 0, post);
    const pivot = new THREE.Group(); pivot.position.y = 1.1; post.add(pivot);
    box(3.0, .16, .12, 0xf2f2f2, s * 1.5, 0, 0, pivot); for (let i = 0; i < 5; i++) box(.4, .17, .13, 0xd22a22, s * (.3 + i * .6), 0, 0, pivot, false);
    arms.push({ pivot, s });
  }
  for (const [x, z, d] of [[-4.6, -14.8, -1], [4.6, -14.8, -1], [-4.6, 14.8, 1], [4.6, 14.8, 1]]) {
    box(.14, 3.4, .14, 0x4a4f56, x, 1.7, z);
    for (const a of [Math.PI / 4, -Math.PI / 4]) { const r = box(1.0, .2, .04, 0xd22a22, x, 3.9, z, scene, false); r.rotation.z = a; const w = box(.9, .1, .05, 0xffffff, x, 3.9, z + d * .02, scene, false); w.rotation.z = a; }
    box(.9, .4, .12, 0x111111, x, 3.2, z);
    const a = sphere(.13, 0x3a1010), b = sphere(.13, 0x3a1010); a.position.set(x - .22, 3.2, z + d * .09); b.position.set(x + .22, 3.2, z + d * .09); scene.add(a, b); lamps.push([a, b]);
  }
  return now => {
    for (const a of arms) a.pivot.rotation.z = a.s * (Math.PI / 2) * (1 - S.gate);
    const ph = Math.floor(now * 2) % 2, on = S.gate > .02;
    for (const [a, b] of lamps) { a.material.color.set(on && ph === 0 ? 0xff3030 : 0x3a1010); b.material.color.set(on && ph === 1 ? 0xff3030 : 0x3a1010); }
  };
};
const mwlLights = () => {
  const heads = [];
  for (const [x, z, d] of [[3.8, -5.5, -1], [-3.8, -5.5, -1], [-3.8, 5.5, 1], [3.8, 5.5, 1]]) {
    postHead(x, z, d, 2.6, .5, 1.0, true);
    const r = sphere(.14, 0xff3030), gr = sphere(.14, 0x30ff70); r.position.set(x, 3.0, z + d * .16); gr.position.set(x, 2.55, z + d * .16); scene.add(r, gr); heads.push({ r, gr });
  }
  return () => { for (const h of heads) { h.r.material.color.set(S.lights ? 0xff3030 : 0x3a1010); h.gr.material.color.set(S.lights ? 0x103a1c : 0x30ff70); } };
};
const footLights = () => {
  const lamps = [];
  for (const [x, z, d] of [[1.6, -3.8, -1], [-1.6, 3.8, 1]]) {
    postHead(x, z, d, 1.9, .4, .5, true); const r = sphere(.12, 0x3a1010); r.position.set(x, 2.1, z + d * .12); scene.add(r); lamps.push(r);
  }
  return () => { for (const r of lamps) r.material.color.set(S.lights ? 0xff3030 : 0x3a1010); };
};
const flashLights = () => {
  const heads = [];
  for (const [x, z, d] of [[4, -5.5, -1], [-4, -5.5, -1], [-4, 5.5, 1], [4, 5.5, 1]]) {
    postHead(x, z, d, 2.6, 1.1, .5, false);
    const a = sphere(.17, 0x2a1a1a), b = sphere(.17, 0x2a1a1a); a.position.set(x - .28, 2.7, z + d * .1); b.position.set(x + .28, 2.7, z + d * .1); scene.add(a, b); heads.push([a, b]);
  }
  return now => {
    const warn = S.cmd && !S.lights, ph = Math.floor(now * 2) % 2, col = warn ? 0xffb020 : 0xff3030;
    for (const [a, b] of heads) { a.material.color.set(warn ? (ph === 0 ? col : 0x2a1a1a) : S.lights ? (ph === 0 ? col : 0x2a1a1a) : 0x2a1a1a); b.material.color.set(warn ? (ph === 0 ? col : 0x2a1a1a) : S.lights ? (ph === 1 ? col : 0x2a1a1a) : 0x2a1a1a); }
  };
};

// ---- in-box controls: a gate wheel, or a two-button console -------------------------------------
function wheelControl(sbox, floorY, sx, sz, name) {
  const wheel = new THREE.Group(); wheel.position.set(2.6, floorY + 1.25, 1.6); sbox.add(wheel);
  box(.22, 1.1, .22, 0x555a60, 2.6, floorY + .55, 1.6, sbox);
  const brass = new THREE.MeshLambertMaterial({ color: 0xc9a15a });
  wheel.add(new THREE.Mesh(new THREE.TorusGeometry(.38, .035, 8, 28), brass));
  wheel.add(new THREE.Mesh(new THREE.CylinderGeometry(.07, .07, .12, 10), brass).rotateX(Math.PI / 2));
  for (let i = 0; i < 4; i++) { const sp = new THREE.Mesh(new THREE.BoxGeometry(.76, .05, .05), brass); sp.rotation.z = i * Math.PI / 4; wheel.add(sp); }
  hitbox(new THREE.CylinderGeometry(.46, .46, .2, 16), 0, 0, 0, wheel, { act: 'wheel' }, [Math.PI / 2, 0, 0]);
  const wp = label(name, .5, .3); wp.position.set(2.6, floorY + .75, 1.49); wp.rotation.y = Math.PI; sbox.add(wp);
  return { blockers: [{ x: sx + 2.6, z: sz + 1.6, r: .55, y: floorY }], update() { wheel.rotation.z = -S.gate * Math.PI * 6; },
    interact(u, button) { if (u.act === 'wheel') { A.held.close = button === 0; A.held.open = button === 2; return true; } return false; },
    hint(u) { return u.act === 'wheel' ? 'Wheel: hold left mouse to close, right mouse to open' : null; } };
}
function consoleControl(sbox, floorY, sx, sz, px, pz, labels, hints) {
  const ped = new THREE.Group(); ped.position.set(px, floorY, pz); sbox.add(ped);
  box(1.5, .9, .6, 0x3a3f46, 0, .45, 0, ped);
  const lo = new THREE.Mesh(new THREE.CylinderGeometry(.13, .13, .08, 14), mat(0xd22a22)); lo.position.set(-.35, .95, 0); ped.add(lo);
  const hi = new THREE.Mesh(new THREE.CylinderGeometry(.13, .13, .08, 14), mat(0x2ecc71)); hi.position.set(.35, .95, 0); ped.add(hi);
  hitbox(new THREE.CylinderGeometry(.24, .24, .3, 12), -.35, .95, 0, ped, { act: 'barrier', cmd: 'lower' });
  hitbox(new THREE.CylinderGeometry(.24, .24, .3, 12), .35, .95, 0, ped, { act: 'barrier', cmd: 'raise' });
  [-.35, .35].forEach((x, i) => { const p = label([labels[i]], .5, .18); p.position.set(x, .915, .22); p.rotation.x = -Math.PI / 2; ped.add(p); });
  const l1 = sphere(.07, 0x333333), l2 = sphere(.07, 0x333333); l1.position.set(-.35, .92, -.2); l2.position.set(.35, .92, -.2); ped.add(l1, l2);
  return { blockers: [{ x: sx + px, z: sz + pz, r: .85, y: floorY }],
    update() { l1.material.color.set(S.gate >= .999 ? 0x30ff70 : 0x333333); l2.material.color.set(A.carsInZone().length ? 0xff3030 : 0x30ff70); },
    interact(u) { if (u.act === 'barrier') { A.cmdBarrier(u.cmd); return true; } return false; },
    hint(u) { return u.act === 'barrier' ? hints[u.cmd === 'lower' ? 0 : 1] : null; } };
}

// ---- stairs from the east door down to the ground, and walkable ground outside ------------------------------
function buildStairs(sbox, floorY) {
  const n = Math.round(floorY / .25), run = .5, rise = floorY / n;
  for (let i = 0; i < n; i++) { const top = floorY - rise * (i + 1) + .05; box(run, Math.max(.1, top), 1.8, 0x8a8f95, 3.7 + run * (i + .5), Math.max(.1, top) / 2, 0, sbox); }
  const len = Math.hypot(n * run, floorY);
  for (const dz of [-.95, .95]) { const r = box(len, .07, .07, 0x8a9097, 3.7 + n * run / 2, floorY / 2 + 1.0, dz, sbox, false); r.rotation.z = -Math.atan2(floorY, n * run); }
  for (const dz of [-.95, .95]) { box(.07, 1.0, .07, 0x8a9097, 3.75, floorY + .5, dz, sbox, false); box(.07, 1.0, .07, 0x8a9097, 3.7 + n * run, .5, dz, sbox, false); }
  return { x0: 3.7, x1: 3.7 + n * run, y0: floorY };
}
function outsideSurfaces(w) {
  const zs = w.tracks.map(Z3), zmin = Math.min(...zs), zmax = Math.max(...zs), k = w.skew || 0, hw = (w.roadW || 6) / 2 / Math.cos(Math.atan(k)) + .3;
  const out = [{ x0: -70, x1: 70, z0: -45, z1: zmin - 1.8, y: 0 }];                                            // the ground north of the line
  for (let z = zmin - 1.8; z < zmax + 1.8; z += 1) out.push({ x0: (z + .5) * k - hw, x1: (z + .5) * k + hw, z0: z, z1: z + 1, y: .34 });   // across the line on the crossing
  for (let z = zmax + 1.8, e = w.roadZ ? w.roadZ[1] : 45; z < e; z += 2) out.push({ x0: (z + 1) * k - hw, x1: (z + 1) * k + hw, z0: z, z1: z + 2, y: .05 });   // the road south of it
  return out;
}

// ---- a standard box for the simpler scenarios: door and stairs on the east side ---------------------------
function buildSimple(d) {
  buildWorld(d.world);
  if (d.scenery) d.scenery();
  const floorY = 3.2, [sx, sz] = d.box, sbox = new THREE.Group(); sbox.position.set(sx, 0, sz); scene.add(sbox);
  const roof = buildRoom(sbox, floorY, true);
  const levers = buildLevers(sbox, floorY);
  const iz = SC.signals.length === 3 ? [-2.0, -1.25, 1.7] : [-1.7, 1.7];
  SC.signals.forEach((s, i) => makeInst(sbox, floorY, s, iz[i]));
  const st = buildStairs(sbox, floorY);
  box(1.2, .06, .6, 0x5b3a22, -2.7, floorY + .9, -1.2, sbox); box(.08, .9, .08, 0x5b3a22, -2.7, floorY + .45, -1.2, sbox);
  const ctl = d.control.type === 'wheel' ? wheelControl(sbox, floorY, sx, sz, d.control.name) : consoleControl(sbox, floorY, sx, sz, 2.2, 1.6, d.control.labels, d.control.hints);
  const dev = d.device();
  return { roof, levers, sbox, surfaces: [
      { x0: sx + st.x0, x1: sx + st.x1, z0: sz - .8, z1: sz + .8, y0: st.y0, y1: 0, axis: 'x' },
      { x0: sx - 3.4, x1: sx + 3.3, z0: sz - 2.4, z1: sz + 2.4, y: floorY }, { x0: sx + 3.3, x1: sx + 3.7, z0: sz - .8, z1: sz + .8, y: floorY },
      ...outsideSurfaces(d.world)],
    blockers: [...ctl.blockers, { x0: sx - 3.9, x1: sx + 3.9, z0: sz - 2.95, z1: sz + 2.95, y: 0 }],
    seat: new THREE.Vector3(sx - 1.8, floorY + 1.65, sz + 1.0), look: new THREE.Vector3(0, 1.0, 0),
    overview: { pos: d.overview || [24, 17, 28], at: [sx * .4, 0, sz * .3] }, start: { x: sx, z: sz + .5, y: floorY },
    update(now) { ctl.update(); dev(now); }, interact: ctl.interact, hint: ctl.hint };
}

const forestSkip = (bx, bz) => (x, z) => Math.abs(x - bx) < 6 && Math.abs(z - bz) < 5;

const SIMPLE = {
  bailey: { box: [9.5, -9], control: { type: 'wheel', name: ['GATE', 'WHEEL'] }, device: gatesBailey,
    world: { tracks: [260], poles: 5.5, treeSkip: (x, z) => x > 3 && x < 17 && z > -16 && z < -2 } },
  strawlake: { box: [17.7, -12.2], control: { type: 'wheel', name: ['BARRIER', 'WHEEL'] }, device: strawBarriers, overview: [34, 20, 30],
    world: { tracks: [235, 285], skew: Math.tan(22.5 * Math.PI / 180), roadW: 6, treeSkip: forestSkip(17.7, -12.2) },
    scenery() {   // the lake south-west of the crossing
      const lake = new THREE.Mesh(new THREE.CylinderGeometry(17, 17, .06, 32), mat(0x2d6a9f)); lake.position.set(-29, .04, 14.5); lake.scale.z = .31; scene.add(lake);
      for (let i = 0; i < 22; i++) box(.06, 1.1, .06, 0x8a9a4a, -44 + i * 1.4 + Math.sin(i * 1.7) * .3, .55, 10 + Math.sin(i) * .6, scene, false);
    } },
  leeforest: { box: [13.6, -9.7], control: { type: 'console', labels: ['LIGHTS RED', 'GREEN'], hints: ['Set road lights red', 'Road lights green'] }, device: mwlLights,
    world: { tracks: [260], trees: 900, treeSkip: forestSkip(13.6, -9.7) } },
  quayfootpath: { box: [14.7, -9.7], control: { type: 'console', labels: ['RED ON', 'OFF'], hints: ['Show the red lights', 'Red lights off'] }, device: footLights,
    world: { tracks: [260], roadW: 1.8, roadColor: 0xb5a98a, deckColor: 0x8a7f68, centre: false, roadZ: [-20, 15.8], treeSkip: (x, z) => z > 12 || forestSkip(14.7, -9.7)(x, z) },
    scenery() {
      box(800, .05, 200, 0x2a5f8f, 0, .05, 115.8, scene, false); box(800, .5, 2.6, 0x7e8187, 0, .25, 14.5, scene, false);
      for (let x = -80; x < 80; x += 9) box(.6, .6, .6, 0x333333, x, .8, 15.4, scene, false);
      for (const [x, z, c] of [[10, 8, 0xb5482f], [14.2, 8, 0x2f6bb5], [18.4, 8, 0xc9a24a], [10, 10.4, 0x3f8a56], [14.2, 10.4, 0xb5482f]]) { box(3.8, 2.4, 2, c, x, 1.2, z); }
      for (const [x, c] of [[-31, 0xd8d2c2], [27, 0xe8c53a]]) { box(12, 1.2, 2.6, c, x, .3, 19.4, scene, false); box(4, 1.6, 1.6, 0xb23b3b, x, 1.5, 19.4, scene, false); }
    } },
  brickworks: { box: [14.7, -9.7], control: { type: 'console', labels: ['FLASH ON', 'OFF'], hints: ['Start the flashing lights', 'Flashing lights off'] }, device: flashLights,
    world: { tracks: [260], treeSkip: (x, z) => forestSkip(14.7, -9.7)(x, z) || (x > -45 && x < 30 && z > 6 && z < 24) },
    scenery() {
      box(15, 4, 7, 0x9b4a32, 15.5, 2, 10.5); box(15, .4, 7.4, 0x6f2f20, 15.5, 4.2, 10.5);
      const ch = new THREE.Mesh(new THREE.CylinderGeometry(.9, 1.2, 14, 10), mat(0x7a3a28)); ch.position.set(24.9, 7, 9); ch.castShadow = true; scene.add(ch);
      for (let i = 0; i < 4; i++) box(3.2, 2, 2, 0xc0623a, 8 + i * 4, 1, 17);
      const pit = new THREE.Mesh(new THREE.CylinderGeometry(15, 15, .06, 28), mat(0x8a6a44)); pit.position.set(-28, .05, 14); pit.scale.z = .45; scene.add(pit);
      const pit2 = new THREE.Mesh(new THREE.CylinderGeometry(11, 11, .08, 28), mat(0x6d5234)); pit2.position.set(-28, .06, 14.4); pit2.scale.z = .35; scene.add(pit2);
    } },
  valleybridge: { box: [14.7, -9.7], control: { type: 'wheel', name: ['TROLLEY', 'WHEEL'] }, device: trolleyGates, overview: [30, 20, 30],
    world: { tracks: [235, 285], treeSkip: (x, z) => forestSkip(14.7, -9.7)(x, z) || (z < -14 && z > -28) },
    scenery() {   // river across the valley with the road on a stone bridge
      const pts = []; for (let i = 0; i <= 16; i++) { const t = i / 16, m = 1 - t; pts.push([X3(m * m * m * 0 + 3 * m * m * t * 250 + 3 * m * t * t * 750 + t * t * t * 1000), Z3(m * m * m * 70 + 3 * m * m * t * 30 + 3 * m * t * t * 100 + t * t * t * 50)]); }
      for (let i = 0; i < 16; i++) { const [x0, z0] = pts[i], [x1, z1] = pts[i + 1], len = Math.hypot(x1 - x0, z1 - z0) + .3, seg = box(len, .03, 3.4, 0x2a6aa0, (x0 + x1) / 2, .015, (z0 + z1) / 2, scene, false); seg.rotation.y = -Math.atan2(z1 - z0, x1 - x0); }
      for (const s of [-1, 1]) box(.5, .9, 4.2, 0x9a968c, s * 3.3, .45, -19.6);
    } }
};

// ---- Tuborne (four tracks, footbridge, stairs) -------------------------------------------------------
function buildTuborne() {
  buildWorld({ tracks: [185, 235, 285, 335], treeSkip: (x, z) => x > -10 && x < 56 && z > -26 && z < 22 });
  const floorY = 4.0, sbox = new THREE.Group(); sbox.position.set(19.6, 0, -17); scene.add(sbox);
  const roof = buildRoom(sbox, floorY, true), levers = buildLevers(sbox, floorY);
  [-2.0, -1.2, 1.2, 2.0].forEach((z, i) => makeInst(sbox, floorY, SC.signals[i], z));
  const ctl = consoleControl(sbox, floorY, 19.6, -17, -1.0, 1.7, ['LOWER', 'RAISE'], ['Lower barriers', 'Raise barriers']);
  box(2.7, .3, 32, 0x6b6e73, 24.65, 3.85, -3.5);
  for (const z of [-11.5, 0, 11.5]) box(.3, z === 0 ? 3.7 : 2.9, .3, 0x4a4f56, 24.65, z === 0 ? 1.85 : 2.45, z);
  box(.08, 1.1, 14.5, 0x8a9097, 23.4, 4.6, 5.25, scene, false); box(.08, 1.1, 6.3, 0x8a9097, 25.95, 4.6, -16.35, scene, false); box(.08, 1.1, 20.6, 0x8a9097, 25.95, 4.6, -.5, scene, false);
  for (const z of [-12, 11]) {
    for (let i = 0; i < 12; i++) { const top = 4.0 - .25 * (i + 1); box(.5, top - 1.0, 1.8, 0x7d8087, 26.25 + i * .5, 1.0 + (top - 1.0) / 2, z); }
    for (const dz of [-.95, .95]) { const r = box(6.7, .07, .07, 0x8a9097, 29, 3.6, z + dz, scene, false); r.rotation.z = -Math.atan2(3, 6); }
  }
  for (const sgn of [-1, 1]) {
    const z = sgn * 11.5;
    box(29, 1, 5, 0xb9b4a8, 29.5, .5, z); box(29, .02, .35, 0xe8c53a, 29.5, 1.01, sgn * 9.3, scene, false);
    for (let i = 0; i < 4; i++) box(.15, 3.2, .15, 0x444a52, 34 + i * 3, 2.6, sgn * 12.9);
    box(10.5, .15, 4.4, 0x3d4a5c, 38.5, 4.25, z);
    box(1.6, .4, .5, 0x6a4a35, 33, 1.3, sgn * 12.6); box(1.6, .4, .5, 0x6a4a35, 39, 1.3, sgn * 12.6);
    const nb = label(['TUBORNE'], 3.2, .7, '#ffffff', '#1f4f9a'); nb.position.set(41.5, 2.6, sgn * 9.6); if (sgn > 0) nb.rotation.y = Math.PI; scene.add(nb);
    box(.12, 2, .12, 0x444a52, 40, 2, sgn * 9.6);
  }
  const arms = [];
  for (const [px, pz, s, entry] of [[-3.4, 13.5, 1, true], [3.4, 13.5, -1, false], [3.4, -13.5, -1, true], [-3.4, -13.5, 1, false]]) {
    const post = new THREE.Group(); post.position.set(px, 0, pz); scene.add(post);
    box(.5, 1.1, .5, 0x555a60, 0, .55, 0, post);
    const pivot = new THREE.Group(); pivot.position.y = 1.1; post.add(pivot);
    box(3.1, .16, .12, 0xf2f2f2, s * 1.65, 0, 0, pivot); for (let i = 0; i < 5; i++) box(.4, .17, .13, 0xd22a22, s * (.4 + i * .62), 0, 0, pivot, false);
    arms.push({ pivot, s, entry });
  }
  const lampsRL = [];
  for (const [px, pz] of [[-4.2, 15], [4.2, 15], [4.2, -15], [-4.2, -15]]) {
    box(.14, 3.4, .14, 0x4a4f56, px, 1.7, pz); box(.5, 1.0, .3, 0x151515, px, 3.2, pz);
    const a = sphere(.16, 0x440000), b = sphere(.16, 0x440000);
    a.position.set(px - .12, 3.4, pz + (pz > 0 ? -.17 : .17)); b.position.set(px + .12, 3.4, pz + (pz > 0 ? -.17 : .17)); scene.add(a, b); lampsRL.push([a, b]);
  }
  const sx = 19.6, sz = -17;
  return { roof, levers, sbox,
    surfaces: [
      { x0: 26, x1: 32, z0: -12.9, z1: -11.1, y0: 4.0, y1: 1.0, axis: 'x' }, { x0: 26, x1: 32, z0: 11.1, z1: 12.9, y0: 4.0, y1: 1.0, axis: 'x' },
      { x0: sx - 3.4, x1: sx + 3.3, z0: sz - 2.4, z1: sz + 2.4, y: floorY }, { x0: sx + 3.3, x1: sx + 3.7, z0: sz - .8, z1: sz + .8, y: floorY },
      { x0: 23.3, x1: 26.0, z0: -19.4, z1: 12.4, y: floorY }, { x0: 15, x1: 44, z0: -13.8, z1: -9.4, y: 1.0 }, { x0: 15, x1: 44, z0: 9.4, z1: 13.8, y: 1.0 }],
    blockers: [...ctl.blockers, { x: 24.65, z: -11.5, r: .4, y: 1.0 }, { x: 24.65, z: 11.5, r: .4, y: 1.0 }],
    seat: new THREE.Vector3(sx - 1.6, floorY + 1.65, sz + .8), look: new THREE.Vector3(0, 1.0, 0),
    overview: { pos: [52, 40, 52], at: [12, 0, -2] }, start: { x: sx, z: sz, y: floorY },
    update(now) {
      ctl.update();
      const e = Math.min(1, S.gate * 2), x = Math.max(0, (S.gate - .5) * 2);
      for (const a of arms) a.pivot.rotation.z = a.s * (Math.PI / 2) * (1 - (a.entry ? e : x));
      const flash = S.lights && S.gate < .999 ? Math.floor(now * 2) % 2 : -1;
      for (const [a, b] of lampsRL) { a.material.color.set(S.lights && (flash === -1 || flash === 0) ? 0xff2020 : 0x440000); b.material.color.set(S.lights && (flash === -1 || flash === 1) ? 0xff2020 : 0x440000); }
    }, interact: ctl.interact, hint: ctl.hint };
}

// ---- Otla (hand-swung gates, steps down from the box) -----------------------------------------------------
function buildOtla() {
  buildWorld({ tracks: [260], poles: 5.5, treeSkip: (x, z) => x > 14 && x < 38 && z > -16 && z < -1 });
  box(25.5, .04, 3.6, 0xb5a98a, 17.25, .03, -4.8, scene, false);
  const floorY = 1.4, sx = 22, sz = -10, sbox = new THREE.Group(); sbox.position.set(sx, 0, sz); scene.add(sbox);
  const roof = buildRoom(sbox, floorY, true), levers = buildLevers(sbox, floorY);
  makeInst(sbox, floorY, SC.signals[0], -1.7); makeInst(sbox, floorY, SC.signals[1], 1.7);
  box(1.2, .06, .6, 0x5b3a22, -2.7, floorY + .9, 1.2, sbox); box(.08, .9, .08, 0x5b3a22, -2.7, floorY + .45, 1.2, sbox);
  for (let i = 0; i < 4; i++) { const top = 1.1 - i * .3; box(.7, top, 1.8, 0x8a8f95, 4.05 + i * .7, top / 2, 0, sbox); }
  const sign = label(['OTLA', 'CROSSING'], 1.6, .8, '#ffffff', '#1f4f9a'); sign.position.set(4.6, 2.2, -3.2); scene.add(sign); box(.1, 2.2, .1, 0x444a52, 4.6, 1.1, -3.25);
  const leaves = [];
  for (const [side, pz, sideSign] of [['n', -1.9, -1], ['s', 1.9, 1]]) for (const s of [1, -1]) {   // posts beside the rails; open, the leaves lie across the line
    const post = new THREE.Group(); post.position.set(-s * 3.3, 0, pz); scene.add(post);
    box(.2, 1.3, .2, 0x555a60, 0, .65, 0, post);
    const leaf = new THREE.Group(); post.add(leaf);
    for (let k = 0; k < 4; k++) box(3.2, .09, .09, k % 2 ? 0xd22a22 : 0xf2f2f2, s * 1.6, .3 + k * .25, 0, leaf);
    box(.09, .9, .09, 0xf2f2f2, s * 3.15, .6, 0, leaf); box(.09, .9, .09, 0xf2f2f2, s * 1.6, .6, 0, leaf);
    hitbox(new THREE.BoxGeometry(3.2, 1.2, .6), s * 1.6, .6, 0, leaf, { act: 'gate', side });
    leaves.push({ leaf, side, s, sideSign });
  }
  return { roof, levers, sbox,
    surfaces: [
      { x0: sx + 3.7, x1: sx + 6.5, z0: sz - .8, z1: sz + .8, y0: floorY, y1: 0, axis: 'x' }, { x0: sx - 3.4, x1: sx + 3.3, z0: sz - 2.4, z1: sz + 2.4, y: floorY },
      { x0: sx + 3.3, x1: sx + 3.7, z0: sz - .8, z1: sz + .8, y: floorY }, { x0: sx + 6.5, x1: sx + 12, z0: -13, z1: -7, y: 0 },
      { x0: -6, x1: 34, z0: -7, z1: -2.4, y: 0 }, { x0: -3, x1: 3, z0: -1.6, z1: 1.6, y: .34 }, { x0: -3, x1: 3, z0: -30, z1: 30, y: .05 }],
    blockers: [], seat: new THREE.Vector3(sx - 1.6, floorY + 1.65, sz + .8), look: new THREE.Vector3(0, 1.0, 0),
    overview: { pos: [34, 22, 30], at: [8, 0, -4] }, start: { x: sx, z: sz, y: floorY },
    update() { for (const l of leaves) l.leaf.rotation.y = l.sideSign * l.s * (Math.PI / 2) * (1 - S.gates[l.side]); },
    interact(u) { if (u.act === 'gate') { A.swingGate(u.side); return true; } return false; },
    hint(u) { return u.act === 'gate' ? `${u.side === 'n' ? 'North' : 'South'} gates: click to swing ${S.gateTarget[u.side] ? 'open' : 'shut'}` : null; } };
}

SIMPLE.parkside = { box: [9.7, -10.3], control: { type: 'wheel', name: ['BARRIER', 'WHEEL'] }, device: germanBarriers, overview: [36, 24, 36],
  world: { tracks: [210, 260, 310], trees: 0, centre: true },
  scenery() {   // the town: terraces either side, the park to the north-west, station platform and plaza to the south-east
    const cols = [0xb5876b, 0xc9b48a, 0x9a6a5a, 0xb9a58f, 0x8f7a6a];
    const house = (x, z, w, d, h, c) => { box(w, h, d, c, x, h / 2, z); const roof = new THREE.Mesh(new THREE.ConeGeometry(Math.max(w, d) * .72, 1.8, 4), mat(0x6f3a2a)); roof.position.set(x, h + .9, z); roof.rotation.y = Math.PI / 4; roof.castShadow = true; scene.add(roof); };
    for (let i = 0; i < 7; i++) house(6 + i * 5.8 + 2.6, -20, 5.2, 7, 6 + (i % 3) * .8, cols[i % 5]);
    for (let i = 0; i < 7; i++) house(-46 + i * 5.8 + 2.6, 17.5, 5.2, 6.6, 5.5, cols[(i + 2) % 5]);
    box(36, .06, 15, 0x4f7a3f, -21, .04, -15.5, scene, false);
    const pond = new THREE.Mesh(new THREE.CylinderGeometry(7, 7, .08, 24), mat(0x2f6aa0)); pond.position.set(-29, .08, -16.5); pond.scale.z = .45; scene.add(pond);
    const trunk = new THREE.CylinderGeometry(.25, .35, 2, 6), leaf = new THREE.ConeGeometry(1.8, 5, 7);
    for (let i = 0; i < 12; i++) { const x = -38 + (i * 37) % 34, z = -22 + (i * 53) % 10; if (Math.hypot((x + 29) / 8.5, (z + 16.5) / 4) < 1) continue; const g = new THREE.Group(); g.position.set(x, 0, z); const a = new THREE.Mesh(trunk, mat(0x5b4630)); a.position.y = 1; const b = new THREE.Mesh(leaf, mat(0x2f5d2c)); b.position.y = 4; a.castShadow = b.castShadow = true; g.add(a, b); scene.add(g); }
    box(29, 1, 3, 0xb9b4a8, 29.5, .5, 8.5); box(29, .02, .35, 0xe8c53a, 29.5, 1.01, 7.2, scene, false);
    box(12, 4.4, 4.4, 0xa8734e, 21, 2.2, 14.5); box(13.2, .9, 5.6, 0x6f3a2a, 21, 4.8, 14.5);
    box(26, .06, 5, 0xc9c4b8, 19, .04, 22.5, scene, false); const fo = new THREE.Mesh(new THREE.CylinderGeometry(1.4, 1.6, .5, 14), mat(0x4f93c9)); fo.position.set(19, .3, 22.5); scene.add(fo);
  } };
const BUILDERS = { tuborne: buildTuborne, otla: buildOtla };
for (const k in SIMPLE) BUILDERS[k] = () => buildSimple(SIMPLE[k]);

// ---- views, mouse and keyboard ------------------------------------------------------------------------------
function setView(m) {
  camMode = m; B3.roof.visible = m !== 'over';
  document.querySelectorAll('#modes3d button').forEach(b => b.classList.toggle('on', b.dataset.m === m));
  $('xhair').style.display = m === 'walk' ? 'block' : 'none';
  if (m !== 'walk' && document.pointerLockElement) document.exitPointerLock();
  if (m === 'over') { camera.position.set(...B3.overview.pos); camera.rotation.set(0, 0, 0); camera.lookAt(...B3.overview.at); }
  $('hint').textContent = m === 'walk' ? 'Click to look around · WASD to walk · click levers, instruments and controls' : '';
}
const ray = new THREE.Raycaster(); ray.far = 4.8;
const ndc = new THREE.Vector2(0, 0); let dragLook = false;
function aimed() {
  ray.setFromCamera(locked ? new THREE.Vector2(0, 0) : ndc, camera);
  const h = ray.intersectObjects(interactives, false)[0]; return h ? h.object.userData : null;
}
function hintFor(u) {
  if (!u) return !locked ? 'Click to look around · WASD to walk · Esc frees the mouse' : '';
  const own = B3.hint(u); if (own) return own;
  if (u.act === 'lever') return `Lever: ${A.sigById(u.id).name}. Click to ${S.sigOff[u.id] ? 'restore' : 'pull'}`;
  if (u.act === 'spare') return 'Spare lever';
  if (u.act === 'inst') { const s = A.sigById(u.id); return S.inst[u.id] === 'offered' ? `${s.name} instrument: click to accept the train` : `${s.name} block instrument`; }
  return '';
}
function setNdc(e) { const r = view.getBoundingClientRect(); ndc.set(((e.clientX - r.left) / r.width) * 2 - 1, -((e.clientY - r.top) / r.height) * 2 + 1); }
function boot() {
  if (booted) return; booted = true;
  view = $('view'); renderer = new THREE.WebGLRenderer({ antialias: true });
  renderer.setPixelRatio(Math.min(devicePixelRatio, 2)); renderer.shadowMap.enabled = true; view.appendChild(renderer.domElement);
  camera = new THREE.PerspectiveCamera(62, 2, .1, 600); camera.rotation.order = 'YXZ';
  const resize = () => { const w = view.clientWidth, h = view.clientHeight; renderer.setSize(w, h, false); camera.aspect = w / h; camera.updateProjectionMatrix(); };
  new ResizeObserver(resize).observe(view); resize();
  document.querySelectorAll('#modes3d button').forEach(b => b.onclick = () => setView(b.dataset.m));
  addEventListener('keydown', e => { if (e.key === 'v' || e.key === 'V') setView(MODES[(MODES.indexOf(camMode) + 1) % 3]); });
  view.addEventListener('contextmenu', e => e.preventDefault());
  document.addEventListener('pointerlockchange', () => { locked = document.pointerLockElement === renderer.domElement; });
  view.addEventListener('pointerdown', e => {
    if (!S) return; setNdc(e);
    if (camMode === 'over') return;
    if (camMode === 'walk' && !locked) { try { const r = renderer.domElement.requestPointerLock(); if (r && r.catch) r.catch(() => {}); } catch (_) {} }
    const u = camMode === 'walk' ? aimed() : null;
    if (!u) { dragLook = true; return; }
    if (!S.running || B3.interact(u, e.button)) return;
    if (u.act === 'lever') A.toggleLever(u.id);
    else if (u.act === 'spare') A.say('Spare lever — not in use.', 3);
    else if (u.act === 'inst') { if (S.inst[u.id] === 'offered') A.accept(u.id); else A.say('Nothing offered on that instrument.', 3); }
  });
  addEventListener('pointerup', () => { dragLook = false; A.held.open = false; A.held.close = false; });
  view.addEventListener('pointermove', e => {
    setNdc(e);
    if (!S || camMode === 'over' || !(locked || dragLook)) return;
    const L = modeLook[camMode], s = locked ? -1 : 1;
    L.yaw += s * e.movementX * .0035; L.pitch += s * e.movementY * .0035;
  });
}

// walkable surfaces: flat or ramped rectangles; you can step between ones within 0.7 of your height
const rampH = (s, x, z) => s.axis === 'x' ? s.y0 + (s.y1 - s.y0) * (x - s.x0) / (s.x1 - s.x0) : s.y0 + (s.y1 - s.y0) * (z - s.z0) / (s.z1 - s.z0);
const inRect = (s, x, z) => x >= s.x0 && x <= s.x1 && z >= s.z0 && z <= s.z1;
function surfaceY(x, z, curY) {
  let best = null, bd = 1e9;
  for (const s of B3.surfaces) {
    if (!inRect(s, x, z)) continue;
    const h = s.axis ? rampH(s, x, z) : s.y;
    if (s.axis && Math.abs(h - curY) <= .35) return h;          // a stair under your feet beats the flat floor below it
    const d = Math.abs(h - curY); if (d < bd) { bd = d; best = h; }
  }
  return bd <= .7 ? best : null;
}
function walkStep(dx, dz) {
  const at = (nx, nz) => {
    const y = surfaceY(nx, nz, walk.sy); if (y === null) return false;
    for (const s of B3.surfaces) if (s.axis && inRect(s, nx, nz) && y < rampH(s, nx, nz) - .45) return false;   // can't walk through the underside of stairs
    for (const b of B3.blockers) if (Math.abs(y - b.y) < 1.5 && (b.r ? Math.hypot(nx - b.x, nz - b.z) < b.r : nx > b.x0 && nx < b.x1 && nz > b.z0 && nz < b.z1)) return false;
    walk.x = nx; walk.z = nz; walk.sy = y; return true;
  };
  if (!at(walk.x + dx, walk.z + dz) && !at(walk.x + dx, walk.z)) at(walk.x, walk.z + dz);
}

// ---- per-frame sync ---------------------------------------------------------------------------------------------
function frame() {
  const tNow = performance.now(), dt = Math.min(.05, (tNow - last3d) / 1000); last3d = tNow;
  const now = S.t;
  for (const s of SC.signals) { const off = S.sigOff[s.id], L = sigLamps[s.id]; L.red.material.color.set(off ? 0x3a1010 : 0xff3030); L.grn.material.color.set(off ? 0x30ff70 : 0x103a1c); }
  for (const tr of S.trains) {
    let m = trainMeshes.get(tr); if (!m) { m = makeTrainMesh(tr); trainMeshes.set(tr, m); }
    m.position.set(X3(tr.x - tr.dir * SC.trainLen / 2), 0, Z3(tr.sig.ty));
    m.userData.lamps[0].material.color.set(tr.dir > 0 ? 0xffffff : 0xff2020); m.userData.lamps[1].material.color.set(tr.dir > 0 ? 0xff2020 : 0xffffff);
  }
  for (const [tr, m] of trainMeshes) if (!S.trains.includes(tr)) { scene.remove(m); trainMeshes.delete(tr); }
  for (const c of S.cars) {
    let m = carMeshes.get(c); if (!m) { m = makeCar(c); carMeshes.set(c, m); }
    m.position.set(X3(c.x), 0, Z3(c.y)); m.rotation.y = th; m.userData.haz.visible = c.stall > 0 && Math.floor(now * 3) % 2 === 0;
  }
  for (const [c, m] of carMeshes) if (!S.cars.includes(c)) { scene.remove(m); carMeshes.delete(c); }
  for (const l of B3.levers) { const target = l.id && S.sigOff[l.id] ? .65 : -.15; l.pivot.rotation.x += (target - l.pivot.rotation.x) * Math.min(1, dt * 10); }
  for (const s of SC.signals) drawInst(s.id, now);
  B3.update(now);
  if (camMode !== 'over') {
    const L = modeLook[camMode], keys = A.keys;
    if (camMode === 'box') { L.yaw = Math.max(yaw0 - 1.3, Math.min(yaw0 + 1.3, L.yaw)); L.pitch = Math.max(-.6, Math.min(.35, L.pitch)); camera.position.copy(B3.seat); }
    else {
      L.pitch = Math.max(-1.3, Math.min(1.3, L.pitch));
      const f = (keys.w ? 1 : 0) - (keys.s ? 1 : 0), rr = (keys.d ? 1 : 0) - (keys.a ? 1 : 0);
      if (f || rr) { const sp = 2.8 * dt, fx = -Math.sin(L.yaw), fz = -Math.cos(L.yaw), rx = Math.cos(L.yaw), rz = -Math.sin(L.yaw); walkStep((fx * f + rx * rr) * sp, (fz * f + rz * rr) * sp); }
      walk.eye += (walk.sy - walk.eye) * Math.min(1, dt * 14);
      camera.position.set(walk.x, walk.eye + 1.65, walk.z);
      const u = aimed(); $('hint').textContent = hintFor(u); $('xhair').classList.toggle('on', !!u);
    }
    camera.rotation.set(L.pitch, L.yaw, 0);
  }
  renderer.render(scene, camera);
}

function start() {
  boot(); S = A.S; SC = A.SC; th = 0;
  newScene(); sigLamps = {}; trainMeshes = new Map(); carMeshes = new Map();
  if (!BUILDERS[SC.key]) throw new Error('no 3D version of ' + SC.title + ' in this copy of 3d.js; refresh the page');
  B3 = BUILDERS[SC.key]();
  for (const s of SC.signals) sigLamps[s.id] = makeSignal(s);
  const d = B3.look.clone().sub(B3.seat); yaw0 = Math.atan2(-d.x, -d.z);
  const p0 = Math.atan2(d.y, Math.hypot(d.x, d.z));
  modeLook.box = { yaw: yaw0, pitch: p0 }; modeLook.walk = { yaw: yaw0, pitch: p0 * .3 };
  walk.x = B3.start.x; walk.z = B3.start.z; walk.sy = walk.eye = B3.start.y;
  setView('box');
  return { frame };
}
window.SBS3D = { start, debug: () => ({ walk, walkStep, B3 }) };
})();
