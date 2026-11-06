/* =====================================================================
   ROSHAMBO : THE GRID ARENA — shared game engine (theme-agnostic)
   Loaded by design-1-aurora.html / design-2-candy.html / design-3-atelier.html
   Board structure + UI are themed via CSS classes/variables; team colours
   and token art are the fixed game identity.
   DOM contract (IDs) is documented at the bottom of this file.
===================================================================== */
"use strict";

const COLORS = {
  green : {main:"#2fae57", dark:"#1c7a3b", light:"#82e2a3", name:"Green",  seat:"Top-Left",  corner:"tl"},
  blue  : {main:"#3b82f6", dark:"#1e56b3", light:"#93c5ff", name:"Blue",   seat:"Top-Right", corner:"tr"},
  red   : {main:"#ef4553", dark:"#ae2431", light:"#ff9aa4", name:"Red",    seat:"Bottom-Right",corner:"br"},
  yellow: {main:"#f2a51c", dark:"#a9720e", light:"#ffd37d", name:"Yellow", seat:"Bottom-Left", corner:"bl"}
};
const SEAT_ORDER = ["green","blue","red","yellow"];
const COUNT_SEATS = {2:["green","red"], 3:["green","blue","red"], 4:["green","blue","red","yellow"]};

const GRID = 9, RIM = 70, CELL = 100;
const cx = c => RIM + c*CELL + CELL/2;
const cy = r => RIM + r*CELL + CELL/2;
const key = (r,c) => r+","+c;

const PADS = {
  green : [[0,2],[6,0],[5,5]],
  blue  : [[0,6],[6,8],[5,3]],
  red   : [[2,8],[8,6],[3,3]],
  yellow: [[2,0],[8,2],[3,5]]
};
const PAD_AT = {};
for (const col in PADS) for (const [r,c] of PADS[col]) PAD_AT[key(r,c)] = col;

const WALLS = [
  [0,2,1,2],[0,3,1,3],[0,5,1,5],[0,6,1,6],
  [1,2,1,3],[2,2,2,3],[1,4,1,5],[2,4,2,5],
  [1,4,2,4],
  [1,0,1,1],[2,0,2,1],[2,1,2,2],[3,1,3,2],
  [2,6,2,7],[3,6,3,7],[1,7,1,8],[2,7,2,8],
  [7,2,8,2],[7,3,8,3],[7,5,8,5],[7,6,8,6],
  [6,2,6,3],[7,2,7,3],[6,4,6,5],[7,4,7,5],
  [6,4,7,4],
  [6,0,6,1],[7,0,7,1],[5,1,5,2],[6,1,6,2],
  [5,6,5,7],[6,6,6,7],[6,7,6,8],[7,7,7,8]
];
const WALLSET = new Set();
for (const [r1,c1,r2,c2] of WALLS){ WALLSET.add(key(r1,c1)+"|"+key(r2,c2)); WALLSET.add(key(r2,c2)+"|"+key(r1,c1)); }
const wallBetween = (r1,c1,r2,c2) => WALLSET.has(key(r1,c1)+"|"+key(r2,c2));

const STARS = {green:[35,35], blue:[1005,35], red:[1005,1005], yellow:[35,1005]};
const KINDS = ["rock","paper","scissors"];
const BEATS = {rock:"scissors", scissors:"paper", paper:"rock"};

let S = null, uid = 1;

/* ---------------- state ---------------- */
function freshState(seats, modes){
  const st = {
    seats, modes, stacks:{}, pieces:[], burned:new Set(),
    turn:0, phase:"awaitRoll", die:0, sel:null, dests:[],
    log:[], over:false, chase:null
  };
  for (const col of seats){
    KINDS.forEach((kind,i)=>{
      const pad = PADS[col][i];
      const p = {id:uid++, color:col, kind, r:pad[0], c:pad[1], phaser:false, held:[], captured:false, capturer:null, freed:false};
      st.pieces.push(p);
      const k = key(p.r,p.c);
      (st.stacks[k] = st.stacks[k]||[]).push(p);
    });
  }
  return st;
}
const inB  = (r,c) => r>=0 && r<GRID && c>=0 && c<GRID;
const topOf = stack => stack[stack.length-1];
const stackAt = (r,c) => S.stacks[key(r,c)] || null;
const piecesOnBoard = col => S.pieces.filter(p=>!p.captured && !p.freed && p.color===col);
const allOnBoard = () => S.pieces.filter(p=>!p.captured && !p.freed);
const trophiesOf = col => S.pieces.filter(p=>p.captured && p.capturer===col && !p.freed);
const freedOf   = col => S.pieces.filter(p=>p.freed && p.color===col);
function scoreOf(col){ return 3*piecesOnBoard(col).length + 2*trophiesOf(col).length + 1*freedOf(col).length; }
function movablePieces(col){
  const out = [];
  for (const k in S.stacks){ const st=S.stacks[k]; if(!st.length) continue;
    const t=topOf(st); if(t.color===col && !t.captured && !t.freed) out.push(t); }
  return out;
}

/* ---------------- movement ---------------- */
function cellPassable(r,c){
  if (!inB(r,c)) return false;
  if (PAD_AT[key(r,c)] && !stackAt(r,c)) return false;
  return true;
}
function legalDestinations(piece, dist){
  const res = new Map();
  const visited = new Set([key(piece.r,piece.c)]);
  const dfs = (r,c,left,path)=>{
    if (left===0){ const k=key(r,c); if(!res.has(k)) res.set(k, path.slice()); return; }
    for (const [dr,dc] of [[-1,0],[1,0],[0,-1],[0,1]]){
      const nr=r+dr, nc=c+dc; if(!inB(nr,nc)) continue;
      const nk=key(nr,nc); if(visited.has(nk)) continue;
      if (!piece.phaser && wallBetween(r,c,nr,nc)) continue;
      const occ = stackAt(nr,nc); const isFinal = left===1;
      if (occ){ if(!isFinal || occ.length>=3) continue; }
      else if (!cellPassable(nr,nc)) continue;
      visited.add(nk); path.push([nr,nc]);
      dfs(nr,nc,left-1,path);
      visited.delete(nk); path.pop();
    }
  };
  dfs(piece.r,piece.c,dist,[[piece.r,piece.c]]);
  res.delete(key(piece.r,piece.c));
  return res;
}
function movableWithDest(col,die){ return movablePieces(col).filter(p=>legalDestinations(p,die).size); }
function anyLegalMove(col, die){ const m=movableWithDest(col,die); return m.length?{piece:m[0]}:null; }

/* ---------------- sound ---------------- */
let AC=null, SOUND_ON=true;
function beep(freq, dur=0.09, type="triangle", vol=0.14, when=0){
  if (!SOUND_ON) return;
  try{
    AC = AC || new (window.AudioContext||window.webkitAudioContext)();
    const t = AC.currentTime + when;
    const osc = AC.createOscillator(); osc.type=type; osc.frequency.value=freq;
    const gn = AC.createGain(); gn.gain.setValueAtTime(vol,t);
    gn.gain.exponentialRampToValueAtTime(0.001,t+dur);
    osc.connect(gn); gn.connect(AC.destination); osc.start(t); osc.stop(t+dur+0.02);
  }catch(e){}
}
const sfx = {
  roll:  ()=>{for(let i=0;i<5;i++)beep(300+i*60,.05,"square",.07,i*.06);},
  step:  ()=>beep(520,.05,"sine",.09),
  stomp: ()=>{beep(160,.18,"sawtooth",.18);beep(90,.3,"square",.16,.08);},
  flip:  ()=>{beep(700,.1,"sine",.11);beep(1050,.14,"sine",.11,.09);},
  rescue:()=>{[660,880,1100].forEach((f,i)=>beep(f,.12,"triangle",.13,i*.09));},
  win:   ()=>{[523,659,784,1046].forEach((f,i)=>beep(f,.22,"triangle",.15,i*.13));},
  deny:  ()=>beep(180,.15,"square",.11)
};

/* ---------------- SVG art ---------------- */
function face(cx0, cy0, s, wink){
  return `
    <circle cx="${cx0-8*s}" cy="${cy0}" r="${2.6*s}" fill="#2a2233"/>
    ${wink
      ? `<path d="M ${cx0+3*s} ${cy0-1*s} q ${4*s} ${3*s} ${8*s} 0" stroke="#2a2233" stroke-width="${2*s}" stroke-linecap="round" fill="none"/>`
      : `<circle cx="${cx0+8*s}" cy="${cy0}" r="${2.6*s}" fill="#2a2233"/>`}
    <circle cx="${cx0-13*s}" cy="${cy0+5*s}" r="${3*s}" fill="#ff9aa0" opacity=".6"/>
    <circle cx="${cx0+13*s}" cy="${cy0+5*s}" r="${3*s}" fill="#ff9aa0" opacity=".6"/>
    <path d="M ${cx0-4*s} ${cy0+5*s} q ${4*s} ${4.5*s} ${8*s} 0" stroke="#2a2233" stroke-width="${1.8*s}" stroke-linecap="round" fill="none"/>`;
}
/* shared standing base for fighters */
function pedestal(C){ return `
    <ellipse cx="0" cy="25.5" rx="21" ry="7.5" fill="${C.dark}"/>
    <ellipse cx="0" cy="24" rx="21" ry="7.5" fill="${C.main}"/>
    <ellipse cx="0" cy="23" rx="14" ry="4.6" fill="${C.light}" opacity=".5"/>`; }
/* the arm/wrist rising out of the pedestal */
function wrist(C){ return `
    <rect x="-9" y="4" width="18" height="18" rx="7" fill="${C.main}" stroke="${C.dark}" stroke-width="2.8"/>`; }
/* ROCK — closed fist, four knuckle bumps on top, thumb wrapped across */
function artRock(C){ return `
    ${pedestal(C)}${wrist(C)}
    <g stroke="${C.dark}" stroke-width="2.8" stroke-linejoin="round">
      <circle cx="-13.5" cy="-13" r="7" fill="${C.main}"/>
      <circle cx="-4.5" cy="-15" r="7" fill="${C.main}"/>
      <circle cx="4.5" cy="-15" r="7" fill="${C.main}"/>
      <circle cx="13.5" cy="-13" r="7" fill="${C.main}"/>
      <rect x="-20" y="-12" width="40" height="25" rx="11" fill="${C.main}"/>
      <rect x="-6" y="2" width="26" height="11" rx="5.5" fill="${C.light}" transform="rotate(-7 7 7.5)"/>
    </g>
    <ellipse cx="-9" cy="-8" rx="8" ry="4" fill="#fff" opacity=".28" stroke="none"/>
    ${face(-1,-3,0.7,false)}`; }
/* PAPER — open palm, four fanned fingers, thumb to the side */
function artPaper(C){ return `
    ${pedestal(C)}${wrist(C)}
    <g stroke="${C.dark}" stroke-width="2.6" stroke-linejoin="round">
      <rect x="-19" y="-30" width="8.5" height="23" rx="4.2" fill="${C.main}" transform="rotate(-7 -14.8 -18)"/>
      <rect x="-9"  y="-35" width="8.5" height="28" rx="4.2" fill="${C.main}" transform="rotate(-2 -4.8 -21)"/>
      <rect x="0.5" y="-34" width="8.5" height="27" rx="4.2" fill="${C.main}" transform="rotate(3 4.8 -20)"/>
      <rect x="10"  y="-29" width="8.5" height="22" rx="4.2" fill="${C.main}" transform="rotate(8 14.2 -18)"/>
      <rect x="-19" y="-13" width="38" height="27" rx="11" fill="${C.main}"/>
      <rect x="-28" y="-8" width="14" height="10" rx="5" fill="${C.main}" transform="rotate(-24 -21 -3)"/>
    </g>
    <ellipse cx="-5" cy="-3" rx="10" ry="5" fill="#fff" opacity=".22" stroke="none"/>
    ${face(0,0,0.68,false)}`; }
/* SCISSORS — V-sign hand, two extended light blades, folded knuckles, thumb across */
function artScissors(C){ return `
    ${pedestal(C)}${wrist(C)}
    <g stroke="${C.dark}" stroke-width="2.6" stroke-linejoin="round">
      <rect x="-12.5" y="-35" width="9.5" height="32" rx="4.7" fill="${C.light}" transform="rotate(-11 -7.8 -19)"/>
      <rect x="2" y="-37" width="9.5" height="34" rx="4.7" fill="${C.light}" transform="rotate(7 6.8 -20)"/>
      <circle cx="-2" cy="-8" r="5.5" fill="${C.main}"/>
      <circle cx="8" cy="-6.5" r="5" fill="${C.main}"/>
      <rect x="-17" y="-9" width="34" height="23" rx="10" fill="${C.main}"/>
      <rect x="-13" y="2" width="25" height="9.5" rx="4.7" fill="${C.main}" transform="rotate(7 -0.5 6.8)"/>
    </g>
    <ellipse cx="-8" cy="-1" rx="7" ry="4" fill="#fff" opacity=".2" stroke="none"/>
    ${face(1,-1,0.6,true)}`; }
const ART = {rock:artRock, paper:artPaper, scissors:artScissors};
function tokenSVG(piece, x, y, scale){
  const inner = ART[piece.kind](COLORS[piece.color]);
  const body = piece.phaser
    ? `<g filter="url(#ghostGlow)" opacity="0.92">${inner}</g><g opacity="0.55">${inner}</g>
       <path d="M 0 -6 l 2.5 -6 2.5 6 6 2.5 -6 2.5 -2.5 6 -2.5 -6 -6 -2.5 z" fill="#fff" transform="translate(28,-22)" opacity=".95"/>`
    : inner;
  const shadow = `<ellipse class="tok-shadow" cx="1.5" cy="31" rx="24" ry="7.5" fill="url(#tokShadow)"${piece.phaser?' opacity=".45"':''}/>`;
  return `<g class="tok" transform="translate(${x},${y}) scale(${scale})">${shadow}${body}</g>`;
}
function starSVG(col, size, wink){
  const C = COLORS[col];
  const P = "M 0 -30 L 7.6 -10.4 L 28.5 -9.3 L 12.4 3.9 L 17.6 24.3 L 0 13 L -17.6 24.3 L -12.4 3.9 L -28.5 -9.3 L -7.6 -10.4 Z";
  return `<g class="star-shape" transform="scale(${size})">
    <ellipse cx="0" cy="27" rx="17" ry="5" fill="${C.dark}" opacity=".6"/>
    <path d="${P}" fill="${C.main}" stroke="${C.dark}" stroke-width="3.4" stroke-linejoin="round"/>
    <path d="M 0 -30 L 7.6 -10.4 L 28.5 -9.3 L 12.4 3.9 L 0 8 Z" fill="${C.light}" opacity=".5"/>
    <path d="M 0 -22 L 4 -11" stroke="#fff" stroke-width="3.4" stroke-linecap="round" opacity=".6"/>
    ${face(0,-2,0.9,wink)}</g>`;
}

/* ---------------- board ---------------- */
function drawBoard(){
  const svg = document.getElementById("board");
  let out = `<defs>
    <radialGradient id="floorGrad" cx="50%" cy="40%" r="78%"><stop class="fg1" offset="0%"/><stop class="fg2" offset="100%"/></radialGradient>
    <linearGradient id="rimGrad" x1="0" y1="0" x2="0" y2="1"><stop class="rg1" offset="0%"/><stop class="rg2" offset="100%"/></linearGradient>
    <linearGradient id="padGrad" x1="0" y1="0" x2="0" y2="1"><stop class="pg1" offset="0%"/><stop class="pg2" offset="100%"/></linearGradient>
    <linearGradient id="depthGrad" x1="0" y1="0" x2="0" y2="1"><stop offset="0%" stop-color="#3a3427" stop-opacity=".5"/><stop offset="100%" stop-color="#3a3427" stop-opacity=".26"/></linearGradient>
    <radialGradient id="tokShadow"><stop offset="0%" stop-color="#0b1220" stop-opacity=".36"/><stop offset="65%" stop-color="#0b1220" stop-opacity=".16"/><stop offset="100%" stop-color="#0b1220" stop-opacity="0"/></radialGradient>
    <radialGradient id="pitShade"><stop offset="0%" stop-color="#0b1220" stop-opacity=".17"/><stop offset="70%" stop-color="#0b1220" stop-opacity=".06"/><stop offset="100%" stop-color="#0b1220" stop-opacity="0"/></radialGradient>
    <linearGradient id="lightGrad" x1="0" y1="0" x2="0" y2="1"><stop offset="0%" stop-color="#ffffff" stop-opacity=".4"/><stop offset="45%" stop-color="#ffffff" stop-opacity="0"/><stop offset="100%" stop-color="#0b1220" stop-opacity=".17"/></linearGradient>
    <filter id="softShadow" x="-30%" y="-30%" width="160%" height="160%"><feDropShadow dx="0" dy="3" stdDeviation="4" flood-color="#0b1220" flood-opacity="0.28"/></filter>
    <filter id="ghostGlow" x="-70%" y="-70%" width="240%" height="240%">
      <feGaussianBlur stdDeviation="5" result="b"/><feFlood class="glow-flood" result="c"/>
      <feComposite in="c" in2="b" operator="in" result="g"/><feMerge><feMergeNode in="g"/><feMergeNode in="SourceGraphic"/></feMerge>
    </filter>
  </defs>`;
  out += `<rect class="rim" x="6" y="6" width="1028" height="1028" rx="44"/>`;
  out += `<rect class="rim-line" x="26" y="26" width="988" height="988" rx="32"/>`;
  out += `<rect class="floor-bg" x="${RIM-8}" y="${RIM-8}" width="${GRID*CELL+16}" height="${GRID*CELL+16}" rx="20" filter="url(#softShadow)"/>`;
  for (let r=0;r<GRID;r++) for (let c=0;c<GRID;c++)
    out += `<rect class="tile ${(r+c)%2?"tile-alt":""}" x="${RIM+c*CELL+3}" y="${RIM+r*CELL+3}" width="${CELL-6}" height="${CELL-6}" rx="10"/>`;
  out += `<ellipse class="pit-shade" cx="${cx(4)}" cy="${cy(4)}" rx="168" ry="168" fill="url(#pitShade)" pointer-events="none"/>`;
  out += `<rect class="pit-ring" x="${RIM+3*CELL+8}" y="${RIM+3*CELL+8}" width="${3*CELL-16}" height="${3*CELL-16}" rx="26"/>`;
  for (const k in PAD_AT){
    const col=PAD_AT[k], [r,c]=k.split(",").map(Number);
    out += `<g class="pad" data-pad="${k}" data-color="${col}">
      <rect class="pad-side" x="${RIM+c*CELL+13}" y="${RIM+r*CELL+20}" width="${CELL-26}" height="${CELL-26}" rx="14" fill="url(#depthGrad)"/>
      <rect class="pad-base" x="${RIM+c*CELL+13}" y="${RIM+r*CELL+13}" width="${CELL-26}" height="${CELL-26}" rx="14"/>
      <rect class="pad-face" x="${RIM+c*CELL+19}" y="${RIM+r*CELL+19}" width="${CELL-38}" height="${CELL-38}" rx="10" fill="${COLORS[col].main}" stroke="${COLORS[col].dark}" stroke-width="3"/>
      <rect class="pad-sheen" x="${RIM+c*CELL+25}" y="${RIM+r*CELL+25}" width="${CELL-50}" height="9" rx="4" fill="${COLORS[col].light}" opacity=".85"/>
    </g>`;
  }
  for (const [r1,c1,r2,c2] of WALLS){
    if (key(r1,c1) > key(r2,c2)) continue;
    let x1,y1,x2,y2,horiz;
    if (r1===r2){ horiz=false; const x=RIM+(Math.max(c1,c2))*CELL; x1=x2=x; y1=RIM+r1*CELL+13; y2=RIM+r1*CELL+CELL-13; }
    else { horiz=true; const y=RIM+(Math.max(r1,r2))*CELL; y1=y2=y; x1=RIM+c1*CELL+13; x2=RIM+c1*CELL+CELL-13; }
    out += wallChain(x1,y1,x2,y2,horiz);
  }
  for (const col in STARS){
    const [x,y]=STARS[col];
    out += `<g class="star star-${col}" data-star="${col}" transform="translate(${x},${y})">
      <ellipse class="star-shadow" cx="2" cy="28" rx="28" ry="8.5" fill="url(#tokShadow)"/>
      <circle class="star-halo" r="33"/><circle class="star-halo2" r="25"/>${starSVG(col,0.72,true)}</g>`;
  }
  out += `<rect class="floor-light" x="${RIM-8}" y="${RIM-8}" width="${GRID*CELL+16}" height="${GRID*CELL+16}" rx="20" fill="url(#lightGrad)" pointer-events="none"/>`;
  out += `<g id="pieceLayer"></g><g id="destLayer"></g><g id="fxLayer"></g>`;
  svg.innerHTML = out;
  paintPadsBurned();
}
function wallChain(x1,y1,x2,y2,horiz){
  const len = horiz ? Math.abs(x2-x1) : Math.abs(y2-y1);
  const n = Math.max(2, Math.round(len/26));
  let s = `<g class="wall">`;
  for (let i=0;i<n;i++){
    const t=(i+0.5)/n, px=x1+(x2-x1)*t, py=y1+(y2-y1)*t, w=20, h=16;
    s += `<rect class="wall-depth" x="${px-w/2+3}" y="${py-h/2+7}" width="${w}" height="${h}" rx="7" transform="rotate(${i%2?8:-8} ${px+2.5} ${py+5})" fill="url(#depthGrad)"/>`;
    s += `<rect class="wall-stone" x="${px-w/2}" y="${py-h/2}" width="${w}" height="${h}" rx="7" transform="rotate(${i%2?8:-8} ${px} ${py})"/>`;
    s += `<rect class="wall-sheen" x="${px-w/2+3}" y="${py-h/2+2}" width="${w-8}" height="4" rx="2"/>`;
  }
  return s+`</g>`;
}
function paintPadsBurned(){
  document.querySelectorAll("#board .pad").forEach(g=>{
    g.classList.toggle("burned", S.burned.has(g.dataset.pad));
  });
}

/* ---------------- pieces + destinations ---------------- */
function drawPieces(){
  const layer = document.getElementById("pieceLayer");
  const col = S.seats[S.turn];
  let out = "";
  for (const k in S.stacks){
    const stack = S.stacks[k]; if(!stack.length) continue;
    const [r,c]=k.split(",").map(Number); const bx=cx(c), by=cy(r);
    stack.forEach((p,i)=>{
      const lift=i*7, x=bx-lift*0.55, y=by-6-lift;
      const isTop = i===stack.length-1;
      const isSel = S.sel && S.sel===p;
      const isMovable = S.phase==="choose" && p.color===col && isTop && legalDestinations(p,S.die).size>0;
      const dim = !(isMovable || isSel) && S.phase==="choose" && p.color===col ? false : (!isMovable && !isSel && S.phase==="choose");
      out += `<g class="piece-g${isMovable?" movable":""}${isSel?" selected":""}${dim?" dim":""}" data-piece="${p.id}" transform="translate(${x},${y})">
        ${isMovable?`<circle class="move-halo" r="40"/>`:""}
        ${isSel?`<circle class="sel-ring" r="42"/>`:""}
        ${tokenSVG(p,0,0,0.78)}
        ${isTop && stack.length>1?`<g class="stack-badge" transform="translate(31,-32)"><rect x="-11" y="-11" width="22" height="22" rx="8"/><text y="5" text-anchor="middle">${stack.length}</text></g>`:""}
      </g>`;
    });
  }
  layer.innerHTML = out;
  layer.querySelectorAll(".piece-g").forEach(g=>g.addEventListener("click", ()=>onPieceClick(+g.dataset.piece)));
}
function destInfo(piece, r, c){
  const occ = stackAt(r,c);
  if (!occ) return {cls:"dest-move", label:"MOVE"};
  const guard = topOf(occ);
  if (guard.color===piece.color) return {cls:"dest-support", label:"SUPPORT"};
  if (BEATS[piece.kind]===guard.kind) return {cls:"dest-stomp", label:"STOMP +2"};
  if (BEATS[guard.kind]===piece.kind) return {cls:"dest-risk", label:"RISK"};
  return {cls:"dest-lock", label:"LOCK"};
}
function drawDests(){
  const layer = document.getElementById("destLayer");
  let out = "";
  for (const d of S.dests){
    const x=cx(d.c), y=cy(d.r); const info=destInfo(S.sel,d.r,d.c);
    out += `<g class="cellhit ${info.cls}" data-r="${d.r}" data-c="${d.c}" transform="translate(${x},${y})">
      <rect class="dest-cell" x="-46" y="-46" width="92" height="92" rx="16"/>
      <circle class="dest-dot" r="13"/>
      <rect class="dest-lab-bg" x="-40" y="20" width="80" height="24" rx="12"/>
      <text class="dest-lab" y="36" text-anchor="middle">${info.label}</text>
      <circle class="dest-hit" r="48" fill="transparent"/>
    </g>`;
  }
  layer.innerHTML = out;
  layer.querySelectorAll(".cellhit").forEach(g=>g.addEventListener("click", ()=>onDestClick(+g.dataset.r, +g.dataset.c)));
}

/* ---------------- UI helpers ---------------- */
const $ = id => document.getElementById(id);
function setStatus(t){ $("statusLine").innerHTML = t; }
function showToast(type, title, msg){
  const stack=$("toastStack"); if(!stack) return;
  const el=document.createElement("div"); el.className="toast toast-"+type;
  el.innerHTML=`<span class="tt-badge">${type.toUpperCase()}</span><div class="tt-body"><b>${title}</b><span>${msg}</span></div>`;
  stack.appendChild(el); requestAnimationFrame(()=>el.classList.add("show"));
  setTimeout(()=>{ el.classList.remove("show"); setTimeout(()=>el.remove(),320); }, 2600);
}
const toast = msg => showToast("info","Notice",msg);
function log(html){ S.log.unshift(html); if(S.log.length>50)S.log.pop();
  $("log").innerHTML = S.log.map(l=>`<div class="ev">${l}</div>`).join(""); }
const cname = col => COLORS[col].name;
const cbadge = col => `<b class="cname cname-${col}">${cname(col)}</b>`;
const currentIsAI = () => S.modes[S.seats[S.turn]]==="ai";

/* ---------------- turn flow ---------------- */
function beginTurn(){
  if (S.over) return;
  S.phase="awaitRoll"; S.sel=null; S.dests=[];
  updateHUD(); drawPieces(); drawDests();
  const col=S.seats[S.turn];
  if (currentIsAI()){ setStatus(`<span class="ai-chip">🤖 ${cname(col)} is plotting…</span>`); $("rollBtn").disabled=true; setTimeout(aiTakeTurn, 750); }
  else { $("rollBtn").disabled=false; setStatus(`<b>${cname(col)}</b> — press <b>Roll</b> to begin your move.`); }
}
const CUBE_ROT={1:"rotateX(0deg) rotateY(0deg)",2:"rotateY(-90deg)",3:"rotateX(-90deg)",4:"rotateX(90deg)",5:"rotateY(90deg)",6:"rotateY(180deg)"};
function showDie(v){
  const die=$("die");
  if (die.classList.contains("cube3d")){ die.style.transform=CUBE_ROT[v]; die.dataset.value=v; }
  else die.textContent=v;
}
function rollDie(cb){
  const die=$("die"); die.classList.add("rolling"); sfx.roll();
  let ticks=0;
  const iv=setInterval(()=>{ showDie(1+Math.floor(Math.random()*6));
    if(++ticks>9){ clearInterval(iv); die.classList.remove("rolling"); S.die=1+Math.floor(Math.random()*6); showDie(S.die); cb(S.die); }
  },90);
}
function afterRoll(die){
  const col=S.seats[S.turn];
  log(`${cbadge(col)} rolled a <b>${die}</b>.`);
  const movable = movableWithDest(col, die);
  if (!movable.length){
    setStatus(`${cname(col)} can't move ${die} exactly — turn forfeited.`);
    log(`😖 ${cbadge(col)} has no legal path of exactly ${die} — forfeits.`);
    sfx.deny(); showToast("warn","No legal path",`${cname(col)} can't move exactly ${die}. Turn skipped.`);
    setTimeout(endTurn, 1200); return;
  }
  S.phase="choose";
  if (currentIsAI()){ aiChooseAndMove(); return; }
  if (movable.length===1){ onPieceClick(movable[0].id); setStatus(`Now tap a <b>glowing square</b> to move.`); }
  else { setStatus(`Tap a <b>pulsing fighter</b> to reveal its glowing squares.`); drawPieces(); }
}
function onPieceClick(id){
  if (S.over || S.phase!=="choose") return;
  const p=S.pieces.find(x=>x.id===id); if(!p) return;
  const col=S.seats[S.turn];
  if (p.color!==col || topOf(stackAt(p.r,p.c))!==p){ toast("That fighter isn't yours to move."); return; }
  const dests=legalDestinations(p,S.die);
  if (!dests.size){ toast("No legal path of that length."); sfx.deny(); return; }
  S.sel=p;
  S.dests=[...dests.entries()].map(([k,path])=>{ const [r,c]=k.split(",").map(Number); return {r,c,path}; });
  drawPieces(); drawDests();
}
function onDestClick(r,c){
  if (S.over || S.phase!=="choose" || !S.sel) return;
  const d=S.dests.find(x=>x.r===r&&x.c===c); if(!d){ toast("Can't land there."); return; }
  const mover=S.sel; S.phase="animating"; drawDests();
  animateMove(mover, d.path, ()=>{
    landPiece(mover,r,c); S.sel=null; S.dests=[];
    drawPieces(); drawDests(); updateHUD();
    if (checkMatchEnd()) return;
    endTurn();
  });
}
function removePieceFromStack(piece){
  const st=stackAt(piece.r,piece.c);
  if(st){ const i=st.indexOf(piece); if(i>=0)st.splice(i,1); if(!st.length)delete S.stacks[key(piece.r,piece.c)]; }
}
function animateMove(piece, path, done){
  removePieceFromStack(piece);
  const startK=key(path[0][0],path[0][1]);
  if (PAD_AT[startK]) S.burned.add(startK);
  paintPadsBurned();
  let curTemp=null;
  const clearTemp=()=>{ if(curTemp){ const st=S.stacks[curTemp]; if(st){const j=st.indexOf(piece); if(j>=0)st.splice(j,1); if(!st.length)delete S.stacks[curTemp];} curTemp=null; } };
  let i=1;
  const stepFn=()=>{
    if (i>=path.length-1){
      clearTemp();
      const last=path[path.length-1]; piece.r=last[0]; piece.c=last[1];
      sfx.step(); done(); return;
    }
    clearTemp();
    piece.r=path[i][0]; piece.c=path[i][1];
    curTemp=key(piece.r,piece.c); S.stacks[curTemp]=[piece];
    sfx.step(); drawPieces();
    const g=document.querySelector(`.piece-g[data-piece="${piece.id}"]`); if(g){ g.classList.remove("dim"); g.classList.add("hopping"); }
    i++; setTimeout(stepFn, 250);
  };
  stepFn();
}

/* ---------------- combat ---------------- */
function landPiece(piece, r, c){
  const k=key(r,c), target=S.stacks[k], padHere=PAD_AT[k];
  if (padHere) S.burned.add(k);
  if (!target){ S.stacks[k]=[piece]; return; }
  const guard=topOf(target);
  if (guard.color===piece.color){ target.push(piece); log(`${cbadge(piece.color)} raised a friendly tower (${target.length} high).`); return; }
  if (BEATS[piece.kind]===guard.kind){
    target.pop(); capture(guard, piece); target.push(piece); ascend(piece);
    sfx.stomp(); sfx.flip();
    log(`💥 ${kindName(piece.kind)} ${cbadge(piece.color)} stomped ${kindName(guard.kind)} ${cbadge(guard.color)}! <b>+2</b>, ascends to <b>Phaser</b>.`);
    fxStomp(cx(c),cy(r));
  } else if (BEATS[guard.kind]===piece.kind){
    capture(piece, guard); ascend(guard); sfx.stomp(); sfx.flip();
    log(`🛡 ${kindName(guard.kind)} ${cbadge(guard.color)} counter-stomped the ${kindName(piece.kind)} ${cbadge(piece.color)}! <b>+2</b>, ascends.`);
    fxStomp(cx(c),cy(r));
  } else {
    target.push(piece);
    log(`🔒 Mirror Lock! Two ${kindName(piece.kind)}s deadlocked — the lower fighter is pinned.`);
  }
}
const kindName = k => k.charAt(0).toUpperCase()+k.slice(1);
const ascend = p => { p.phaser=true; };
function capture(victim, capturerPiece){
  victim.captured=true; victim.capturer=capturerPiece.color; victim.heldBy=capturerPiece; capturerPiece.held.push(victim);
  const rescuer=capturerPiece.color;
  for (const held of victim.held.slice()){
    if (held.color===rescuer){
      held.freed=true; held.captured=false; held.capturer=null; held.heldBy=null;
      victim.held.splice(victim.held.indexOf(held),1); sfx.rescue();
      log(`✨ ${cbadge(rescuer)} liberated a captive ally! <b>+1 rescue</b>.`);
    } else {
      held.heldBy=capturerPiece; held.capturer=rescuer;
      victim.held.splice(victim.held.indexOf(held),1); capturerPiece.held.push(held);
    }
  }
}
function fxStomp(x,y){
  const fx=$("fxLayer");
  fx.innerHTML=`<g transform="translate(${x},${y})"><circle class="fx-ring" r="10"><animate attributeName="r" from="10" to="54" dur="0.5s" fill="freeze"/><animate attributeName="opacity" from=".9" to="0" dur="0.5s" fill="freeze"/></circle></g>`;
  setTimeout(()=>fx.innerHTML="",540);
}

/* ---------------- turn advance / endgame ---------------- */
function endTurn(){
  if (S.over) return;
  if (S.chase){ advanceChase(); return; }
  for (let i=0;i<S.seats.length;i++){ S.turn=(S.turn+1)%S.seats.length; if(piecesOnBoard(S.seats[S.turn]).length) break; }
  maybeStartChase(); if (S.over) return; passOrBegin();
}
function aliveColors(){ const s=new Set(); for(const p of allOnBoard())s.add(p.color); return [...s]; }
function checkMatchEnd(){
  const board=allOnBoard(), cols=aliveColors();
  if (cols.length<=1){ finishMatch("Only one team still fields fighters on the arena floor."); return true; }
  const kinds=new Set(board.map(p=>p.kind));
  if (kinds.size===1){ finishMatch(`⚖ Identical Standoff — only ${kindName(board[0].kind)}s remain, so no knockout is possible.`); return true; }
  drawPieces(); updateHUD(); return false;
}
function maybeStartChase(){
  const cols=aliveColors(); if(cols.length!==2) return;
  const counts=cols.map(c=>({c,n:piecesOnBoard(c).length}));
  const prey=counts.find(x=>x.n===1), hunt=counts.find(x=>x.n>=2);
  if(!prey||!hunt) return;
  S.chase={hunter:hunt.c, prey:prey.c, hunterTurns:0, preyTurns:0};
  S.turn=S.seats.indexOf(S.chase.hunter);
  log(`🏁 <b>FINAL 3 CHANCES!</b> ${cbadge(hunt.c)} hunts the lone ${cbadge(prey.c)} fighter.`);
  updateChaseBanner();
}
function updateChaseBanner(){
  const el=$("chaseBanner"); if(!el) return;
  if(!S.chase){ el.style.display="none"; return; }
  el.style.display="block";
  el.innerHTML=`🏃 Final 3 Chances — Hunter ${cname(S.chase.hunter)} (${S.chase.hunterTurns}/3) · Prey ${cname(S.chase.prey)} (${S.chase.preyTurns}/3)`;
}
function advanceChase(){
  const ch=S.chase, just=S.seats[S.turn];
  if (just===ch.hunter) ch.hunterTurns++; else ch.preyTurns++;
  updateChaseBanner();
  if (ch.hunterTurns>=3 && ch.preyTurns>=3){ finishMatch("🏃 The runner survived all 3 chances — straight to final scoring."); return; }
  const cols=aliveColors();
  if (cols.length!==2 || piecesOnBoard(ch.prey).length!==1 || piecesOnBoard(ch.hunter).length<2){
    log("The standoff shape changed — chase lifted, play continues."); S.chase=null; updateChaseBanner();
    S.turn=(S.turn+1)%S.seats.length; passOrBegin(); return;
  }
  S.turn=S.seats.indexOf(just===ch.hunter?ch.prey:ch.hunter); passOrBegin();
}
function passOrBegin(){
  const col=S.seats[S.turn], human=S.modes[col]==="human";
  const twoHumans=S.seats.filter(c=>S.modes[c]==="human").length>1;
  if (human && twoHumans){
    setStatus("Waiting for the next player…");
    $("passStar").innerHTML=`<svg viewBox="-42 -42 84 84" class="big-star">${starSVG(col,1,false)}</svg>`;
    $("passTitle").textContent=`Pass the device to ${cname(col)}`;
    $("passText").textContent=`Keep your plan secret — ${cname(col)} takes the arena next.`;
    $("passOverlay").classList.remove("hidden");
    $("passBtn").onclick=()=>{ $("passOverlay").classList.add("hidden"); beginTurn(); };
  } else beginTurn();
}

/* ---------------- scoring ---------------- */
function finishMatch(reason){
  S.over=true; S.phase="over"; updateChaseBanner();
  const rows=S.seats.map(c=>({col:c, alive:piecesOnBoard(c).length, tro:trophiesOf(c).length, safe:freedOf(c).length, score:scoreOf(c)}))
    .sort((a,b)=>b.score-a.score || b.tro-a.tro);
  const top=rows[0].score; let tied=rows.filter(r=>r.score===top); let tieNote="";
  if (tied.length>1){
    const byTro=Math.max(...tied.map(r=>r.tro)); const still=tied.filter(r=>r.tro===byTro);
    if (still.length>1) tieNote="Trophies couldn't break the tie — the Nexus Sprint decides it!";
    else { tieNote="Broken by the Trophy tiebreaker."; tied=still; }
  }
  const winner=tied.length===1?tied[0].col:null;
  showEndScreen(rows, reason, winner, tieNote, tied);
}
function showEndScreen(rows, reason, winner, tieNote, tied){
  $("endSub").textContent=reason;
  $("endTitle").textContent=winner?`${cname(winner)} Wins!`:"Match Over";
  $("endStar").innerHTML=winner?`<svg viewBox="-42 -42 84 84" class="big-star">${starSVG(winner,1,false)}</svg>`:"";
  let html=`<tr><th>Team</th><th>On Board ×3</th><th>Trophies ×2</th><th>Rescues ×1</th><th>Score</th></tr>`;
  for (const r of rows) html+=`<tr class="${winner===r.col?"win":""}"><td class="cname cname-${r.col}">${cname(r.col)}</td><td>${r.alive}</td><td>${r.tro}</td><td>${r.safe}</td><td><b>${r.score}</b></td></tr>`;
  $("endTable").innerHTML=html;
  $("nexusArea").innerHTML=tieNote?`<p class="nexus-note">${tieNote}</p>`:"";
  if (winner) sfx.win();
  $("endOverlay").classList.remove("hidden");
  if (!winner && tied.length>1){
    const btn=document.createElement("button"); btn.className="btn-primary"; btn.style.marginTop="6px"; btn.textContent="⚡ Run the Nexus Sprint";
    btn.onclick=()=>{ btn.disabled=true; runNexusSprint(tied.map(r=>r.col)); };
    $("nexusArea").appendChild(btn);
  }
  $("endAgainBtn").onclick=()=>{ $("endOverlay").classList.add("hidden"); $("passOverlay").classList.add("hidden"); $("game").classList.add("hidden"); $("setup").classList.remove("hidden"); };
  $("endRulesBtn").onclick=()=>openRules();
}
function runNexusSprint(cols){
  const area=$("nexusArea");
  area.innerHTML=`<div class="nexus-box"><b>⚡ Nexus Sprint</b> — first to reach the Pit center wins outright!<div id="sprintLog" class="sprint-log"></div></div>`;
  const dist=col=>{ const ps=piecesOnBoard(col); return ps.length?Math.min(...ps.map(p=>Math.abs(p.r-4)+Math.abs(p.c-4))):99; };
  const state=cols.map(c=>({col:c,pos:dist(c)})); let idx=0,rounds=0;
  const tick=()=>{ const s=state[idx]; const roll=1+Math.floor(Math.random()*6); s.pos=Math.max(0,s.pos-roll);
    $("sprintLog").innerHTML+=`<div>${cbadge(s.col)} rolls <b>${roll}</b> — ${s.pos===0?"reaches the Pit center! 🏆":`${s.pos} to go`}</div>`;
    beep(s.pos===0?900:400+roll*60,.1);
    if (s.pos===0){ sfx.win(); $("endTitle").textContent=`${cname(s.col)} wins the Nexus Sprint!`;
      $("endStar").innerHTML=`<svg viewBox="-42 -42 84 84" class="big-star">${starSVG(s.col,1,false)}</svg>`;
      $("sprintLog").innerHTML+=`<div class="sprint-win">${cname(s.col)} takes the crown!</div>`; return; }
    idx=(idx+1)%state.length;
    if(++rounds>40){ const w=state[Math.floor(Math.random()*state.length)]; $("sprintLog").innerHTML+=`<div class="sprint-win">Fate crowns ${cname(w.col)}!</div>`; return; }
    setTimeout(tick,750);
  };
  setTimeout(tick,500);
}

/* ---------------- AI ---------------- */
function dangerZones(){
  const zone={}, cur=S.seats[S.turn];
  for (const k in S.stacks){ const st=S.stacks[k]; if(!st.length)continue; const p=topOf(st); if(p.color===cur)continue;
    for(let d=1;d<=6;d++) for(const kk of legalDestinations(p,d).keys()) (zone[kk]=zone[kk]||[]).push(p); }
  return zone;
}
function scoreAIMove(piece,dest,zone){
  const k=key(dest.r,dest.c); let v=0; const occ=stackAt(dest.r,dest.c), my=piece.color;
  if (occ){ const g=topOf(occ);
    if (g.color===my) v+=6;
    else if (BEATS[piece.kind]===g.kind){ v+=120+30*g.held.length+20; }
    else if (BEATS[g.kind]===piece.kind) v-=140;
    else v+=26;
  }
  const threats=zone[k]||[];
  for (const t of threats){ if(occ&&topOf(occ).color!==my) continue;
    if (BEATS[t.kind]===piece.kind) v-=34; else if (BEATS[piece.kind]===t.kind) v+=10; else v-=4; }
  v += (8-(Math.abs(dest.r-4)+Math.abs(dest.c-4)))*1.5;
  const en=Math.min(...allOnBoard().filter(p=>p.color!==my).map(p=>Math.abs(p.r-dest.r)+Math.abs(p.c-dest.c)),9);
  if(!occ) v+=Math.max(0,7-en);
  return v+Math.random()*6;
}
function aiTakeTurn(){ if(S.over)return; $("rollBtn").disabled=true; rollDie(afterRoll); }
function aiChooseAndMove(){
  const col=S.seats[S.turn], die=S.die, zone=dangerZones(); let best=null;
  for (const p of movableWithDest(col,die)) for (const [k,path] of legalDestinations(p,die)){
    const [r,c]=k.split(",").map(Number); const v=scoreAIMove(p,{r,c},zone);
    if(!best||v>best.v) best={p,r,c,path,v};
  }
  if(!best){ setTimeout(endTurn,400); return; }
  S.sel=best.p; S.phase="animating";
  animateMove(best.p, best.path, ()=>{
    landPiece(best.p,best.p.r,best.p.c); S.sel=null;
    drawPieces(); drawDests(); updateHUD();
    if(checkMatchEnd()) return; setTimeout(endTurn,550);
  });
}

/* ---------------- HUD ---------------- */
function updateHUD(){
  const col=S.seats[S.turn], pill=$("turnPill");
  pill.style.setProperty("--turn-color", COLORS[col].main);
  pill.dataset.color=col;
  $("turnName").textContent=`${cname(col)}${S.modes[col]==="ai"?" · AI":""}`;
  $("rollBtn").style.setProperty("--roll-color", COLORS[col].main);
  $("leftPanel").innerHTML = S.seats.map(c=>{
    const active=c===col && !S.over;
    return `<div class="pcard ${active?"active":""}" data-color="${c}">
      <div class="pc-top"><span class="pc-star"><svg viewBox="-42 -42 84 84">${starSVG(c,0.62,false)}</svg></span>
        <span class="pc-name">${cname(c)}</span><span class="pc-score">${scoreOf(c)}</span></div>
      <div class="pc-meta">${S.modes[c]==="ai"?"🤖 AI":"🧑 Human"} · ${piecesOnBoard(c).length}/3 on board</div>
      <div class="pc-vaults"><span class="vault">🏆 <b>${trophiesOf(c).length}</b> trophies</span><span class="vault">🛡 <b>${freedOf(c).length}</b> rescues</span></div>
    </div>`;
  }).join("");
  paintPadsBurned(); updateChaseBanner();
  document.querySelectorAll("#board .star").forEach(g=>{
    g.classList.toggle("star-off", !S.seats.includes(g.dataset.star));
  });
}

/* ---------------- rules ---------------- */
const RULES_HTML = `
  <h3>Objective</h3><p>Score the most by stomping enemy fighters (+2 trophies), liberating captured allies (+1) and keeping your squad alive (+3 each).</p>
  <h3>Setup</h3><p>Each team deploys Rock, Paper &amp; Scissors on its 2 rim Pads + 1 Pit Pad, all Solid-side up.</p>
  <h3>Movement</h3><ul>
    <li>Turns go clockwise: Green → Blue → Red → Yellow.</li>
    <li>Roll the die and move <b>one</b> fighter the <b>exact</b> number of squares, orthogonally — never revisit a square in one turn.</li>
    <li><b>Tap a pulsing fighter</b>, then tap a <b>glowing square</b>. Labels show MOVE / STOMP / SUPPORT / LOCK / RISK.</li>
    <li><b>One-way threshold:</b> once a fighter leaves its Pad, that Pad burns forever — empty Pads can never be entered.</li>
    <li><b>Bodies block:</b> you may only enter an occupied square as your final step (to Stomp or Stack).</li></ul>
  <h3>Stone Blocks &amp; Phaser Power</h3><ul>
    <li>Solid fighters walk around stone walls. After any knockout the winner <b>ascends</b> to <b>Phaser</b> and glides straight through walls.</li>
    <li>Phasers have no extra armor — they can still be stomped and captured.</li></ul>
  <h3>Combat</h3><ul>
    <li>Rock ▸ Scissors  Paper ▸ Rock. Only the top fighter of a stack defends.</li>
    <li><b>Revenge Rescue:</b> a fighter you stomped that holds one of YOUR captives frees them to your Safe Vault (+1). Other captives transfer to your Trophy Vault.</li>
    <li><b>Mirror Lock:</b> identical types deadlock (max 3 high); the lower fighter is pinned. Same-color landings raise a friendly tower.</li></ul>
  <h3>Match End &amp; Scoring</h3><ul>
    <li><b>Final 3 Chances:</b> a 2-vs-1 standoff gives hunter &amp; prey 3 alternating turns. <b>Identical Standoff:</b> only one type left.</li>
    <li>Score = 3×survivors + 2×trophies + 1×rescues. Ties break by trophies, then a Nexus Sprint dice-race to the Pit center.</li></ul>
  <p class="house-note"><b>House rulings:</b> no exact path ⇒ forfeit · losing an attack ⇒ defender counter-stomps · chase lifts if the standoff shape changes.</p>`;
function openRules(){ $("rulesModal").classList.remove("hidden"); }
function closeRules(){ $("rulesModal").classList.add("hidden"); }

/* ---------------- setup ---------------- */
let setupCount=2;
const setupModes={green:"ai",blue:"ai",red:"human",yellow:"ai"};
function renderSeats(){
  const seats=COUNT_SEATS[setupCount];
  $("seats").innerHTML=SEAT_ORDER.map(c=>{
    const on=seats.includes(c);
    return `<div class="seat ${on?"on":"off"}" data-color="${c}">
      <div class="seat-star"><svg viewBox="-42 -42 84 84">${starSVG(c,0.85,false)}</svg></div>
      <div class="seat-name">${COLORS[c].name}</div><div class="seat-pos">${COLORS[c].seat}</div>
      <div class="mode-row">
        <button class="mode-btn ${setupModes[c]==="human"?"on":""}" data-c="${c}" data-m="human">🧑 Human</button>
        <button class="mode-btn ${setupModes[c]==="ai"?"on":""}" data-c="${c}" data-m="ai">🤖 AI</button>
      </div></div>`;
  }).join("");
}
function startGame(){
  uid=1; const seats=COUNT_SEATS[setupCount].slice().sort((a,b)=>SEAT_ORDER.indexOf(a)-SEAT_ORDER.indexOf(b));
  const modesObj={}; for(const c of seats) modesObj[c]=setupModes[c];
  S=freshState(seats,modesObj);
  $("setup").classList.add("hidden"); $("game").classList.remove("hidden");
  $("passOverlay").classList.add("hidden");
  $("log").innerHTML=""; $("chaseBanner").style.display="none";
  drawBoard();
  log(`⚔ Match start — ${seats.map(c=>cbadge(c)).join(" · ")} deploy onto the Grid Arena.`);
  const twoHumans=seats.filter(c=>S.modes[c]==="human").length>1;
  if (twoHumans) passOrBegin(); else beginTurn();
}

/* ---------------- delegated router (sandbox-safe) ---------------- */
function bindRouter(){
  document.addEventListener("click", e=>{
    const t=e.target.closest("[data-nav],[data-m],[data-n],[data-act]"); if(!t) return;
    if (t.dataset.n){ setupCount=+t.dataset.n; document.querySelectorAll("[data-n]").forEach(b=>b.classList.toggle("on", b===t)); renderSeats(); }
    else if (t.dataset.m){ setupModes[t.dataset.c]=t.dataset.m; renderSeats(); }
    else if (t.dataset.nav==="start"){ startGame(); }
    else if (t.dataset.nav==="rules"){ openRules(); }
    else if (t.dataset.nav==="closeRules"){ closeRules(); }
    else if (t.dataset.nav==="sound"){ SOUND_ON=!SOUND_ON; t.textContent=SOUND_ON?"🔊 Sound":"🔇 Muted"; }
    else if (t.dataset.nav==="quit"){ $("confirmModal").classList.remove("hidden"); }
    else if (t.dataset.nav==="confirmQuit"){ $("confirmModal").classList.add("hidden"); $("passOverlay").classList.add("hidden"); $("game").classList.add("hidden"); $("setup").classList.remove("hidden"); }
    else if (t.dataset.nav==="confirmCancel"){ $("confirmModal").classList.add("hidden"); }
  });
  $("rollBtn").addEventListener("click", ()=>{ if(S && !S.over && S.phase==="awaitRoll" && !currentIsAI()){ $("rollBtn").disabled=true; rollDie(afterRoll); } });
}

/* ---------------- boot ---------------- */
function boot(){
  $("rulesBody").innerHTML=RULES_HTML;
  $("starsStrip").innerHTML=SEAT_ORDER.map(c=>`<span class="strip-star"><svg viewBox="-42 -42 84 84">${starSVG(c,0.9,true)}</svg></span>`).join("");
  document.querySelector('[data-n="2"]').classList.add("on");
  renderSeats(); bindRouter();
}
if (document.readyState!=="loading") boot(); else document.addEventListener("DOMContentLoaded", boot);

/* DOM contract IDs:
   setup: #starsStrip #seats [data-n=2|3|4] [data-nav=start] [data-nav=rules]
   game : #turnPill #turnName [data-nav=sound] [data-nav=rules] [data-nav=quit]
          #leftPanel #board(svg) #die #rollBtn #statusLine #chaseBanner #log #rightPanel
   overlays: #passOverlay(#passStar #passTitle #passText #passBtn)
             #rulesModal(#rulesBody [data-nav=closeRules])
             #endOverlay(#endStar #endTitle #endSub #endTable #nexusArea #endAgainBtn #endRulesBtn)
             #confirmModal([data-nav=confirmQuit][data-nav=confirmCancel])
             #toastStack
*/
