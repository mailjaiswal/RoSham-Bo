// Headless engine test for RoSham Bo — loads engine.js with DOM stubs
const fs = require("fs"), vm = require("vm");
const js = fs.readFileSync(__dirname + "/engine.js", "utf8");

function mkEl(){ return {
  innerHTML:"", textContent:"", value:"", disabled:false, style:{setProperty(){}}, dataset:{},
  classList:{add(){},remove(){},toggle(){},contains(){return false}},
  addEventListener(){}, querySelector(){return mkEl()}, querySelectorAll(){return []},
  appendChild(){}, setAttribute(){}, onclick:null, onclick2:null
};}
const sandbox = {
  console, setTimeout, setInterval, clearInterval, clearTimeout, Math, JSON,
  requestAnimationFrame:cb=>cb(),
  document:{ getElementById:(()=>{const cache={}; return id=>cache[id]||(cache[id]=mkEl());})(), querySelectorAll:()=>[], querySelector:()=>mkEl(), createElement:()=>mkEl(), addEventListener(){}, readyState:"complete" },
  window:{ AudioContext:undefined, webkitAudioContext:undefined },
  confirm:()=>true, alert(){}, localStorage:{getItem:()=>null,setItem(){}}
};
sandbox.globalThis = sandbox;
vm.createContext(sandbox);
vm.runInContext(js + `
  ;globalThis.__api = { S:()=>S, setS:v=>{S=v}, freshState, legalDestinations, anyLegalMove,
    landPiece, removePieceFromStack, allOnBoard, piecesOnBoard, trophiesOf, freedOf, scoreOf,
    checkMatchEnd, maybeStartChase, aliveColors, WALLS, wallBetween, PADS, PAD_AT, key, inB,
    stackAt, topOf, movablePieces, capture, BEATS, KINDS, GRID, drawBoard, drawPieces, getPiece:id=>S.pieces.find(p=>p.id===id) };
`, sandbox);
const A = sandbox.__api;

/* ---- 1. connectivity: all floor cells reachable ignoring pads-as-walls? BFS over non-pad cells ---- */
let wallsCount = A.WALLS.length;
function passable(r,c){ return A.inB(r,c) && !A.PAD_AT[A.key(r,c)]; }
const seen = new Set(["4,4"]); const q=[[4,4]];
while(q.length){
  const [r,c]=q.pop();
  for(const [dr,dc] of [[-1,0],[1,0],[0,-1],[0,1]]){
    const nr=r+dr,nc=c+dc,k=A.key(nr,nc);
    if(!passable(nr,nc)||seen.has(k)) continue;
    if(A.wallBetween(r,c,nr,nc)) continue;
    seen.add(k); q.push([nr,nc]);
  }
}
console.log("walls:",wallsCount,"| floor cells reachable from pit center:",seen.size,"of",81-12,"non-pad cells");
if (seen.size !== 81-12) { console.log("!! board disconnected"); process.exit(1); }

/* ---- 2. movement sanity: solid vs phaser, pad blocking ---- */
let S = A.freshState(["green","blue","red","yellow"],["ai","ai","ai","ai"]);
A.setS(S);
const gp = S.pieces.find(p=>p.color==="green"&&p.kind==="rock"); // on pad (0,2)
let d1 = A.legalDestinations(gp,1);
if (d1.has("1,2")) { console.log("!! wall between 0,2 and 1,2 not respected"); process.exit(1); }
// empty pads must be unenterable: vacate the blue pad at (0,6) first, then probe
delete S.stacks["0,6"];
let d4 = A.legalDestinations(gp,4);
if (d4.has("0,6")) { console.log("!! empty pad enterable"); process.exit(1); }
// but an occupied pad IS a legal stomp/stack target
S.stacks["0,6"]=[S.pieces.find(p=>p.color==="blue"&&p.kind==="paper")];
let d4b = A.legalDestinations(gp,4);
if (!d4b.has("0,6")) { console.log("!! occupied pad should be enterable as final step"); process.exit(1); }
gp.phaser = true;
const dp = A.legalDestinations(gp,1);
if (!dp.has("1,2")) { console.log("!! phaser cannot phase wall"); process.exit(1); }
console.log("movement sanity OK (solid blocked by wall, pads dead, phaser phases)");

/* ---- 3. full random self-play games must terminate ---- */
for (let g=0; g<40; g++){
  S = A.freshState(["green","blue","red","yellow"],["ai","ai","ai","ai"]);
  A.setS(S);
  let steps=0, chases=0;
  while(!S.over && steps<4000){
    steps++;
    const col=S.seats[S.turn];
    const die=1+Math.floor(Math.random()*6);
    const mv=A.anyLegalMove(col,die);
    if(mv){
      const dests=[...A.legalDestinations(mv.piece,die).entries()];
      const [k,path]=dests[Math.floor(Math.random()*dests.length)];
      const [r,c]=k.split(",").map(Number);
      A.removePieceFromStack(mv.piece);
      const st0=A.key(path[0][0],path[0][1]);
      if(A.PAD_AT[st0]) S.burned.add(st0);
      const last=path[path.length-1];
      mv.piece.r=last[0]; mv.piece.c=last[1];
      A.landPiece(mv.piece,r,c);
      if(A.checkMatchEnd()) break;
    }
    if(S.chase){ chases++; S.turn=(S.turn+1)%S.seats.length;
      // chase: 6 half-turns then manual end check mirrors advanceChase
      continue; }
    for(let i=0;i<S.seats.length;i++){ S.turn=(S.turn+1)%S.seats.length;
      if(A.piecesOnBoard(S.seats[S.turn]).length) break; }
    A.maybeStartChase();
  }
  if(!S.over){ console.log("!! game",g,"did not terminate in",steps,"steps"); process.exit(1); }
}
console.log("40 random full games all reached a decisive end ✔");

/* ---- 4. combat unit tests ---- */
S = A.freshState(["green","blue"],["ai","ai"]); A.setS(S);
const at=(r,c)=>{const st=S.stacks[A.key(r,c)];return st&&A.topOf(st);};
// clear board and place: red rock at (4,4), blue scissors at (4,6)
S.stacks={}; S.pieces.forEach(p=>{p.captured=true;});
const rr={id:901,color:"red",kind:"rock",r:4,c:4,phaser:false,held:[],captured:false,capturer:null,freed:false};
const bs={id:902,color:"blue",kind:"scissors",r:4,c:6,phaser:false,held:[],captured:false,capturer:null,freed:false};
S.stacks["4,4"]=[rr]; S.stacks["4,6"]=[bs]; S.pieces.push(rr,bs);
rr.r=4;rr.c=5; A.landPiece(rr,4,6); // rock stomps scissors
if (!bs.captured || bs.capturer!=="red" || !rr.phaser){ console.log("!! stomp failed", bs.captured, bs.capturer, rr.phaser); process.exit(1); }
if (at(4,6)!==rr){ console.log("!! attacker did not take the square"); process.exit(1); }
console.log("stomp + ascension OK");
// mirror lock
S.stacks={};
const br={id:903,color:"blue",kind:"rock",r:2,c:2,phaser:false,held:[],captured:false,capturer:null,freed:false};
const rr2={id:904,color:"red",kind:"rock",r:2,c:3,phaser:false,held:[],captured:false,capturer:null,freed:false};
S.stacks["2,2"]=[br]; S.stacks["2,3"]=[rr2]; S.pieces.push(br,rr2);
rr2.r=2;rr2.c=2; A.landPiece(rr2,2,2);
if (S.stacks["2,2"].length!==2 || br.captured){ console.log("!! mirror lock failed"); process.exit(1); }
console.log("mirror lock OK");
// rescue: red rock A holds green piece; blue paper stomps A -> green freed to blue? (green!=blue so transfer)
S.stacks={}; S.pieces.forEach(p=>{p.captured=true;p.freed=false;p.held=[];});
const hold={id:910,color:"yellow",kind:"rock",r:0,c:0,phaser:false,held:[],captured:true,capturer:"red",freed:false};
const cap ={id:911,color:"red",kind:"rock",r:6,c:6,phaser:false,held:[hold],captured:false,capturer:null,freed:false};
const pap ={id:912,color:"yellow",kind:"paper",r:6,c:7,phaser:false,held:[],captured:false,capturer:null,freed:false};
hold.r=6;hold.c=6;
S.stacks["6,6"]=[cap]; S.stacks["6,7"]=[pap]; S.pieces.push(cap,pap);
pap.r=6;pap.c=6; A.landPiece(pap,6,6); // paper beats rock
if (!hold.freed || hold.capturer!==null){ console.log("!! revenge rescue failed", hold.freed, hold.capturer); process.exit(1); }
if (!cap.captured || cap.capturer!=="yellow"){ console.log("!! capture failed"); process.exit(1); }
console.log("revenge rescue OK");

/* ---- 5. art rendering smoke: drawBoard + drawPieces produce clean SVG ---- */
S = A.freshState(["green","blue","red","yellow"],{green:"ai",blue:"ai",red:"ai",yellow:"ai"}); A.setS(S);
S.phase="choose"; S.turn=0; S.die=3;
A.drawBoard(); A.drawPieces();
const boardHTML = sandbox.document.getElementById("board").innerHTML;
const pieceHTML = sandbox.document.getElementById("pieceLayer").innerHTML;
for (const [name,html] of [["board",boardHTML],["pieces",pieceHTML]]){
  if (/NaN|undefined|null/.test(html)){ console.log("!! "+name+" SVG contains NaN/undefined"); process.exit(1); }
}
const tokCount = (pieceHTML.match(/class="tok"/g)||[]).length;
if (tokCount !== 12){ console.log("!! expected 12 tokens rendered, got", tokCount); process.exit(1); }
for (const kind of ["#2fae57","#3b82f6","#ef4553","#f2a51c"]){
  if (!pieceHTML.includes(kind)){ console.log("!! player color missing in rendered art:", kind); process.exit(1); }
}
// every coordinate pair inside translate(...) must be finite
for (const m of pieceHTML.matchAll(/translate\(([-\d.]+),([-\d.]+)\)/g)){
  if (!isFinite(+m[1]) || !isFinite(+m[2])){ console.log("!! non-finite translate in pieces"); process.exit(1); }
}
console.log("art render smoke OK (12 tokens, all 4 team colors, no NaN coords)");
console.log("ALL ENGINE TESTS PASSED");
