/* ============================================================
 * 中式八球 · 网页版（HTML5 Canvas + 原生 JavaScript）
 * ------------------------------------------------------------
 * 课程：《人工智能基础技术及应用》期末大作业
 *
 * 代码结构（方便按章节写报告）：
 *   第 1 部分  常量、DOM 与全局状态
 *   第 2 部分  球与球台的建模
 *   第 3 部分  物理引擎：运动、摩擦、碰撞、落袋、加塞
 *   第 4 部分  规则引擎：犯规、球组、回合、胜负
 *   第 5 部分  AI 对手：几何瞄准 + 路径检测 + 难度扰动
 *   第 6 部分  输入处理与有限状态机（含角度旋钮、加塞盘）
 *   第 7 部分  Canvas 渲染
 *   第 8 部分  固定时间步长的游戏主循环
 * ============================================================ */
(() => {
  "use strict";

  /* ==========================================================
   * 第 1 部分：常量、DOM 与全局状态
   * ========================================================== */

  // 球台参数。坐标原点在“台面有效区域”的左上角，不含库边。
  const CFG = {
    W: 900,                 // 台面宽（像素）
    H: 450,                 // 台面高，宽高比 2:1
    RAIL: 54,               // 四周库边 / 木框宽度
    BALL_R: 12,             // 球半径
    POCKET_R: 21,           // 袋口判定半径
    FRICTION: 1.15,         // 指数摩擦系数（越大停得越快）
    RESTITUTION_BALL: 0.96, // 球与球碰撞恢复系数
    RESTITUTION_WALL: 0.9,  // 球与库边碰撞恢复系数
    STOP_SPEED: 9,          // 速度低于该值视为静止（像素/秒）
    MIN_SPEED: 320,         // 最小击球速度
    MAX_SPEED: 1650,        // 最大击球速度
    FIXED_DT: 1 / 120,      // 物理固定时间步长（秒）
    POWER_MIN: 5,           // 可自由选择的最小力度
    POWER_DEFAULT: 55,      // 默认力度
    SPIN_DECAY: 0.9,        // 加塞强度衰减系数
    SPIN_BALL_FOLLOW: 0.3,  // 高杆 / 低杆对母球碰撞后速度的影响
    SPIN_BALL_SIDE: 0.18,   // 侧塞对母球碰撞后横向速度的影响
    SPIN_CUSHION: 0.22      // 侧塞对库边反弹角的影响
  };

  const LOGICAL_W = CFG.W + CFG.RAIL * 2; // 画布逻辑宽度 1008
  const LOGICAL_H = CFG.H + CFG.RAIL * 2; // 画布逻辑高度 558
  const TAU = Math.PI * 2;

  // 六个袋口：四角 + 上下中袋
  const POCKETS = [
    { x: 0, y: 0 }, { x: CFG.W / 2, y: 0 }, { x: CFG.W, y: 0 },
    { x: 0, y: CFG.H }, { x: CFG.W / 2, y: CFG.H }, { x: CFG.W, y: CFG.H }
  ];

  // 1–7 全色球，9–15 花色球，同号颜色相同
  const BALL_COLORS = {
    1: "#f2c14e", 2: "#2f6fed", 3: "#e5484d", 4: "#8b5cf6",
    5: "#f97316", 6: "#16a34a", 7: "#9f1239", 8: "#15181b",
    9: "#f2c14e", 10: "#2f6fed", 11: "#e5484d", 12: "#8b5cf6",
    13: "#f97316", 14: "#16a34a", 15: "#9f1239"
  };

  // ---------- DOM ----------
  const canvas = document.getElementById("gameCanvas");
  const ctx = canvas.getContext("2d");
  const powerFill = document.getElementById("powerFill");
  const powerValue = document.getElementById("powerValue");
  const powerRange = document.getElementById("powerRange");
  const powerHandle = document.getElementById("powerHandle");
  const shootBtn = document.getElementById("shootBtn");
  const tablePanel = document.getElementById("tablePanel");
  const focusBtn = document.getElementById("focusBtn");
  const focusExit = document.getElementById("focusExit");
  const statusText = document.getElementById("statusText");
  const hintText = document.getElementById("hintText");
  const logList = document.getElementById("logList");
  const resultOverlay = document.getElementById("resultOverlay");
  const resultTitle = document.getElementById("resultTitle");
  const resultReason = document.getElementById("resultReason");
  const modeSwitch = document.getElementById("modeSwitch");
  const difficultyRow = document.getElementById("difficultyRow");
  const difficultySelect = document.getElementById("difficulty");
  const soundBtn = document.getElementById("soundBtn");
  const helpModal = document.getElementById("helpModal");
  const angleKnob = document.getElementById("angleKnob");
  const knobNeedle = document.getElementById("knobNeedle");
  const angleValue = document.getElementById("angleValue");
  const spinPad = document.getElementById("spinPad");
  const spinDot = document.getElementById("spinDot");
  const spinValue = document.getElementById("spinValue");

  // ---------- 全局游戏状态（状态机的“数据部分”） ----------
  const game = {
    phase: "aiming",      // aiming | shooting | resolving | ballInHand | aiThinking | gameOver
    mode: "pvp",          // pvp | ai
    difficulty: "normal", // easy | normal | hard
    current: 0,           // 当前击球方：0 或 1
    players: [],
    breakDone: false,     // 是否已完成开球
    ballInHand: false,    // 是否处于自由球状态
    cueHeld: false,       // 白球是否被拿起（等待放置）
    winner: null,
    shot: null,           // 当前这一杆的统计数据
    pending: null,        // 结算后待执行的动作
    resolveTimer: 0,
    aiTimer: 0,
    log: []
  };

  let balls = [];
  let cueBall = null;

  // 瞄准与自由力度
  let aimAngle = 0;          // 弧度
  let power = CFG.POWER_DEFAULT; // 5–100，可自由选择并保留
  let mouse = { x: CFG.W * 0.7, y: CFG.H / 2, inside: false };

  // 开球 / 自由球拖拽状态：手指按住白球或台面时，预览并放置白球
  const cueDrag = {
    active: false,
    pointerId: null,
    offsetX: 0,
    offsetY: 0
  };

  // 母球加塞：x 为左右（+右塞），y 为上下（+高杆 / -低杆），范围 -1 ~ 1
  const english = { x: 0, y: 0 };

  // 粒子、火花、扩散环、浮动文字
  const effects = [];
  let screenShake = 0;
  let lastImpactFx = 0;
  let clothPattern = null;

  // 音效
  let audioCtx = null;
  let soundOn = true;
  let lastHitSound = 0;

  /* ==========================================================
   * 第 2 部分：球与球台的建模
   * ========================================================== */

  /** 球的类型：cue 白球 / solid 全色 / stripe 花色 / eight 黑八 */
  function ballType(id) {
    if (id === 0) return "cue";
    if (id === 8) return "eight";
    return id < 8 ? "solid" : "stripe";
  }

  function createBall(id, x, y) {
    return {
      id,
      x,
      y,
      vx: 0,
      vy: 0,
      spinX: 0,               // 侧旋强度（-1 ~ 1，正为右塞）
      spinY: 0,               // 高杆 / 低杆（-1 ~ 1，正为高杆）
      potted: false,          // 是否已落袋
      color: id === 0 ? "#f7f7f2" : BALL_COLORS[id],
      type: ballType(id)
    };
  }

  /**
   * 摆球：三角形球堆，8 号球固定在第三排中间。
   * 底角放一颗全色、一颗花色，符合常见摆球习惯。
   */
  function rackBalls() {
    balls = [];
    cueBall = createBall(0, CFG.W * 0.22, CFG.H / 2);
    balls.push(cueBall);

    const R = CFG.BALL_R;
    const gap = 0.8;                    // 球之间留一点缝隙，避免初始重叠
    const spacing = R * 2 + gap;
    const rowGap = spacing * Math.sqrt(3) / 2;
    const apexX = CFG.W * 0.72;         // 球堆顶点

    // 从上到下、从左到右依次摆放
    const layout = [
      [1],
      [11, 2],
      [3, 8, 12],
      [13, 4, 14, 5],
      [6, 15, 9, 7, 10]
    ];

    layout.forEach((row, rowIndex) => {
      row.forEach((id, i) => {
        const x = apexX + rowIndex * rowGap;
        const y = CFG.H / 2 + (i - rowIndex / 2) * spacing;
        balls.push(createBall(id, x, y));
      });
    });
  }

  function getBall(id) {
    return balls.find((b) => b.id === id) || null;
  }

  function activeBalls() {
    return balls.filter((b) => !b.potted);
  }

  /** 某个球组（solid / stripe）在台面上还剩几颗 */
  function remainingOfGroup(group) {
    return balls.filter((b) => !b.potted && b.type === group).length;
  }

  /** 当前玩家是否已经清台，进入“打 8 号球”阶段 */
  function isOnEight(playerIndex) {
    const player = game.players[playerIndex];
    return Boolean(player && player.group && remainingOfGroup(player.group) === 0);
  }

  function isAITurn() {
    return Boolean(game.players[game.current] && game.players[game.current].isAI);
  }

  /* ==========================================================
   * 第 3 部分：物理引擎
   * ----------------------------------------------------------
   * 采用“固定时间步长 + 子步进”：
   *   1. 每帧按速度大小把位移拆成多个小步，防止高速穿透；
   *   2. 球与球用等质量弹性碰撞公式，沿法线交换动量；
   *   3. 球与库边按恢复系数反弹；
   *   4. 指数摩擦让球自然减速并停止；
   *   5. 加塞：球球碰撞与库边反弹时施加旋转冲量。
   * ========================================================== */

  function updatePhysics(dt) {
    // 找到本帧最大速度，决定子步数量（每步位移不超过约 0.45R）
    let maxSpeed = 0;
    for (const b of balls) {
      if (b.potted) continue;
      maxSpeed = Math.max(maxSpeed, Math.hypot(b.vx, b.vy));
    }
    const steps = Math.min(
      12,
      Math.max(1, Math.ceil((maxSpeed * dt) / (CFG.BALL_R * 0.45)))
    );
    const h = dt / steps;

    for (let s = 0; s < steps; s++) {
      // 1) 位置积分
      for (const b of balls) {
        if (b.potted) continue;
        b.x += b.vx * h;
        b.y += b.vy * h;
      }

      // 2) 落袋检测（先于库边反弹，避免球在袋口被弹回）
      checkPockets();

      // 3) 库边碰撞
      for (const b of balls) {
        if (!b.potted) collideCushion(b);
      }

      // 4) 球与球碰撞（两两检测，16 颗球计算量很小）
      for (let i = 0; i < balls.length; i++) {
        if (balls[i].potted) continue;
        for (let j = i + 1; j < balls.length; j++) {
          if (balls[j].potted) continue;
          collideBalls(balls[i], balls[j]);
        }
      }
    }

    // 5) 指数摩擦：v = v * e^(-k·dt)；加塞强度单独更快衰减
    const damp = Math.exp(-CFG.FRICTION * dt);
    const spinDamp = Math.exp(-CFG.SPIN_DECAY * dt);
    for (const b of balls) {
      if (b.potted) continue;
      b.vx *= damp;
      b.vy *= damp;
      b.spinX *= spinDamp;
      b.spinY *= spinDamp;
      if (Math.hypot(b.vx, b.vy) < CFG.STOP_SPEED) {
        b.vx = 0;
        b.vy = 0;
        b.spinX = 0;
        b.spinY = 0;
      }
    }
  }

  /** 落袋：球心进入袋口判定圆即可 */
  function checkPockets() {
    for (const b of balls) {
      if (b.potted) continue;
      for (const p of POCKETS) {
        if (Math.hypot(b.x - p.x, b.y - p.y) > CFG.POCKET_R) continue;

        b.potted = true;
        b.vx = 0;
        b.vy = 0;

        if (b.id === 0) {
          if (game.shot) game.shot.cuePotted = true;
        } else if (game.shot) {
          game.shot.potted.push(b.id);
        }

        spawnPotEffect(p.x, p.y, b.color, b.id);
        screenShake = Math.max(screenShake, b.id === 8 ? 4.2 : 2.8);
        playTone(b.id === 0 ? 160 : 220, 0.12, 0.05, "sine");
        break;
      }
    }
  }

  /** 库边反弹：把球拉回台面内，并反转对应方向速度 */
  function collideCushion(b) {
    const r = CFG.BALL_R;
    const e = CFG.RESTITUTION_WALL;
    const preSpeed = Math.hypot(b.vx, b.vy);
    let hit = false;

    // 侧塞会在库边产生切向速度，(nx, ny) 是库边指向台内的法线
    const applyCushionSpin = (nx, ny) => {
      if (b.id !== 0 || Math.abs(b.spinX) < 0.02) return;
      const kick = preSpeed * CFG.SPIN_CUSHION * b.spinX;
      b.vx += -ny * kick;
      b.vy += nx * kick;
    };

    if (b.x < r) {
      b.x = r;
      if (b.vx < 0) { b.vx = -b.vx * e; hit = true; applyCushionSpin(1, 0); }
    } else if (b.x > CFG.W - r) {
      b.x = CFG.W - r;
      if (b.vx > 0) { b.vx = -b.vx * e; hit = true; applyCushionSpin(-1, 0); }
    }

    if (b.y < r) {
      b.y = r;
      if (b.vy < 0) { b.vy = -b.vy * e; hit = true; applyCushionSpin(0, 1); }
    } else if (b.y > CFG.H - r) {
      b.y = CFG.H - r;
      if (b.vy > 0) { b.vy = -b.vy * e; hit = true; applyCushionSpin(0, -1); }
    }

    if (!hit) return;

    // 每次碰库都会消耗一部分旋转
    if (b.id === 0) {
      b.spinX *= 0.55;
      b.spinY *= 0.8;
    }

    // 规则统计：白球碰到目标球之后，是否有球碰库
    if (game.shot && game.shot.firstHit !== null) {
      game.shot.railAfterContact = true;
    }

    const speed = Math.hypot(b.vx, b.vy);
    if (speed > 120) playImpact(speed * 0.3);
    if (speed > 210) spawnCushionFx(b.x, b.y, speed, b.color);
  }

  /**
   * 等质量弹性碰撞（带恢复系数）。
   * 只在两球接近时处理，沿法线方向施加冲量。
   */
  function collideBalls(a, b) {
    let dx = b.x - a.x;
    let dy = b.y - a.y;
    let dist = Math.hypot(dx, dy);
    const minDist = CFG.BALL_R * 2;

    if (dist >= minDist) return;
    if (dist === 0) {
      // 完全重合的极端情况：随便推开一点
      dx = 0.01;
      dy = 0;
      dist = 0.01;
    }

    const nx = dx / dist;
    const ny = dy / dist;

    // 位置修正，防止两球“粘住”
    const overlap = minDist - dist;
    a.x -= nx * overlap * 0.5;
    a.y -= ny * overlap * 0.5;
    b.x += nx * overlap * 0.5;
    b.y += ny * overlap * 0.5;

    // 相对速度在法线方向的分量
    const rvx = b.vx - a.vx;
    const rvy = b.vy - a.vy;
    const velocityAlongNormal = rvx * nx + rvy * ny;
    if (velocityAlongNormal > 0) return; // 已经在分离，不再施加冲量

    // 加塞：先记录母球碰撞前的运动方向与速度（碰撞后会被冲量改变）
    const cueSphere = a.id === 0 ? a : (b.id === 0 ? b : null);
    let cueDirX = 0;
    let cueDirY = 0;
    let cueSpeed = 0;
    if (cueSphere) {
      cueSpeed = Math.hypot(cueSphere.vx, cueSphere.vy);
      if (cueSpeed > 1) {
        cueDirX = cueSphere.vx / cueSpeed;
        cueDirY = cueSphere.vy / cueSpeed;
      }
    }

    const e = CFG.RESTITUTION_BALL;
    const impulse = (-(1 + e) * velocityAlongNormal) / 2; // 等质量，除以 2
    a.vx -= impulse * nx;
    a.vy -= impulse * ny;
    b.vx += impulse * nx;
    b.vy += impulse * ny;

    // 加塞效果：高杆跟进 / 低杆回缩 + 侧塞横向偏移
    if (
      cueSphere &&
      cueSpeed > 50 &&
      (Math.abs(cueSphere.spinX) > 0.02 || Math.abs(cueSphere.spinY) > 0.02)
    ) {
      const impactSpeed = Math.abs(velocityAlongNormal);

      // 高杆：沿击球方向再推一把；低杆：反向拉回
      const follow = cueSphere.spinY * CFG.SPIN_BALL_FOLLOW * impactSpeed;
      cueSphere.vx += cueDirX * follow;
      cueSphere.vy += cueDirY * follow;

      // 侧塞：垂直于击球方向产生横向速度
      const side = cueSphere.spinX * CFG.SPIN_BALL_SIDE * impactSpeed;
      cueSphere.vx += -cueDirY * side;
      cueSphere.vy += cueDirX * side;

      // 旋转在碰撞时被大量消耗
      cueSphere.spinX *= 0.4;
      cueSphere.spinY *= 0.45;
    }

    // 记录白球第一次碰到的球（用于犯规判断）
    if (game.shot && game.shot.firstHit === null) {
      if (a.id === 0) game.shot.firstHit = b.id;
      else if (b.id === 0) game.shot.firstHit = a.id;
    }

    const impact = Math.abs(velocityAlongNormal);
    if (impact > 90) playImpact(impact * 0.35);
    if (impact > 125) {
      spawnCollisionFx(
        (a.x + b.x) / 2,
        (a.y + b.y) / 2,
        impact,
        nx,
        ny
      );
    }
  }

  /** 所有球都静止？ */
  function allBallsStopped() {
    return balls.every((b) => b.potted || (b.vx === 0 && b.vy === 0));
  }

  /**
   * 瞄准预测：从白球沿击球方向发射一条“扫掠圆”射线，
   * 求与其它球（半径 2R）和库边的最早交点。
   * 这是台球辅助线的几何基础，也用于 AI 的路径判断。
   */
  function predictAim(angle) {
    const cue = cueBall;
    const dx = Math.cos(angle);
    const dy = Math.sin(angle);
    let bestT = Infinity;
    let hitBall = null;

    for (const b of balls) {
      if (b.potted || b.id === 0) continue;
      const ox = b.x - cue.x;
      const oy = b.y - cue.y;
      const projection = ox * dx + oy * dy;
      if (projection <= 0) continue;

      const perp2 = ox * ox + oy * oy - projection * projection;
      const rr = CFG.BALL_R * 2;
      if (perp2 > rr * rr) continue;

      const t = projection - Math.sqrt(rr * rr - perp2);
      if (t > 0 && t < bestT) {
        bestT = t;
        hitBall = b;
      }
    }

    // 与库边的交点
    let wallT = Infinity;
    const r = CFG.BALL_R;
    if (dx > 0) wallT = Math.min(wallT, (CFG.W - r - cue.x) / dx);
    if (dx < 0) wallT = Math.min(wallT, (r - cue.x) / dx);
    if (dy > 0) wallT = Math.min(wallT, (CFG.H - r - cue.y) / dy);
    if (dy < 0) wallT = Math.min(wallT, (r - cue.y) / dy);

    if (!Number.isFinite(wallT)) wallT = 0;
    if (bestT > wallT) {
      bestT = wallT;
      hitBall = null;
    }

    return {
      t: Math.max(0, bestT),
      x: cue.x + dx * bestT,
      y: cue.y + dy * bestT,
      ball: hitBall
    };
  }

  /* ==========================================================
   * 第 4 部分：规则引擎
   * ----------------------------------------------------------
   * 每杆结束后统一结算：
   *   1. 8 号球特殊处理（开球重摆 / 胜负）
   *   2. 开球后首次进球定球组
   *   3. 统计进球、判断犯规
   *   4. 决定继续击球、交换回合或自由球
   * ========================================================== */

  function resolveShot() {
    const shot = game.shot;
    if (!shot) return;

    game.phase = "resolving";
    game.resolveTimer = 1.15;

    const me = game.players[game.current];
    const opponent = game.players[1 - game.current];
    const potted = shot.potted.filter((id) => id !== 0);

    // -------- 情况 A：开球时 8 号球落袋 → 重新摆球，由原开球方重开 --------
    if (potted.includes(8) && shot.isBreak) {
      game.pending = { type: "rerack", breaker: game.current };
      addLog("开球时 8 号球落袋，重新摆球", "foul");
      setStatus("8 号球开球落袋，重新摆球", "foul");
      setHint("本杆不计分，开球方重新开球");
      return;
    }

    // -------- 情况 B：8 号球落袋 → 直接判定胜负 --------
    if (potted.includes(8)) {
      // 合法条件：已定组、赛前已清台、白球未落袋、第一颗碰到的是 8 号球
      const legal =
        Boolean(me.group) &&
        shot.onEightBefore &&
        !shot.cuePotted &&
        shot.firstHit === 8;

      game.winner = legal ? game.current : 1 - game.current;
      const winner = game.players[game.winner];

      game.pending = {
        type: "gameOver",
        winner: game.winner,
        reason: legal
          ? "合法打进 8 号球"
          : `${me.name} 提前打进 8 号球或击球犯规，判负`
      };

      if (legal) {
        addLog(`${winner.name} 合法打进 8 号球，获胜！`, "win");
        setStatus(`${winner.name} 获胜！`, "win");
      } else {
        addLog(`${me.name} 违规打进 8 号球，判负`, "foul");
        setStatus(`${winner.name} 获胜！`, "win");
      }
      setHint("点击“再来一局”重新开始");
      return;
    }

    // -------- 情况 C：开球后首次进球，确定球组 --------
    if (!me.group && potted.length > 0) {
      const firstType = ballType(potted[0]);
      if (firstType === "solid" || firstType === "stripe") {
        me.group = firstType;
        opponent.group = firstType === "solid" ? "stripe" : "solid";
        const label = firstType === "solid" ? "全色球 1–7" : "花色球 9–15";
        addLog(`${me.name} 选定 ${label}`);
      }
    }

    // -------- 统计进球：己方球记分，对方球也算给对方 --------
    let ownPotted = 0;
    for (const id of potted) {
      const type = ballType(id);
      let owner = null;
      if (game.players[0].group === type) owner = game.players[0];
      else if (game.players[1].group === type) owner = game.players[1];

      if (owner && !owner.potted.includes(id)) {
        owner.potted.push(id);
        owner.potted.sort((a, b) => a - b);
      }
      if (owner === me && type === me.group) ownPotted++;
    }

    // -------- 犯规判断 --------
    let foul = false;
    let foulReason = "";

    if (shot.cuePotted) {
      foul = true;
      foulReason = "白球落袋";
    } else if (shot.firstHit === null) {
      foul = true;
      foulReason = "空杆，未碰到任何球";
    } else {
      const firstType = ballType(shot.firstHit);
      if (firstType === "eight" && !shot.onEightBefore) {
        foul = true;
        foulReason = "未清台先碰 8 号球";
      } else if (me.group && firstType !== "eight" && firstType !== me.group) {
        foul = true;
        foulReason = "先碰到对方球";
      }
    }

    // 击球后必须有球碰库或落袋（白球落袋已经单独判罚）
    if (!foul && !shot.railAfterContact && potted.length === 0) {
      foul = true;
      foulReason = "击球后无球碰库";
    }

    if (foul) {
      me.fouls += 1;
      addLog(`${me.name} 犯规：${foulReason}`, "foul");
    }

    // -------- 回合与状态转移 --------
    const switchTurn = foul || ownPotted === 0;
    const ballInHand = foul;

    if (foul) {
      setStatus(`${me.name} 犯规：${foulReason}`, "foul");
      setHint(`${opponent.name} 获得自由球，可任意摆放白球`);
    } else if (ownPotted > 0) {
      setStatus(`${me.name} 打进 ${ownPotted} 颗己方球，继续击球`, "win");
      setHint("保持手感，继续瞄准击球");
      addLog(`${me.name} 打进 ${ownPotted} 颗己方球，继续击球`);
    } else if (potted.length > 0) {
      setStatus(`${me.name} 打进对方球，交换回合`);
      setHint(`${opponent.name} 击球`);
      addLog(`${me.name} 打进对方球，交换回合`);
    } else {
      setStatus(`${me.name} 未进球，交换回合`);
      setHint(`${opponent.name} 击球`);
      addLog(`${me.name} 未进球，交换回合`);
    }

    // 清台提示
    if (me.group && remainingOfGroup(me.group) === 0 && !foul) {
      addLog(`${me.name} 已清台，目标 8 号球`, "win");
    }

    if (shot.isBreak) game.breakDone = true;

    game.pending = {
      type: "next",
      switchTurn,
      ballInHand
    };

    updateHUD();
  }

  /** 结算动画播放完后，真正执行状态切换 */
  function finishResolve() {
    const pending = game.pending;
    game.pending = null;

    if (!pending) {
      beginTurn();
      return;
    }

    if (pending.type === "gameOver") {
      game.phase = "gameOver";
      showResult(game.winner, pending.reason);
      updateHUD();
      return;
    }

    if (pending.type === "rerack") {
      rackBalls();
      game.players.forEach((p) => { p.potted = []; });
      game.breakDone = false;
      game.ballInHand = true;   // 重新开球也允许自由摆放白球
      game.cueHeld = false;
      game.current = pending.breaker;
      game.shot = null;
      beginTurn();
      return;
    }

    game.shot = null;

    if (pending.switchTurn) game.current = 1 - game.current;
    if (pending.ballInHand) game.ballInHand = true;

    // 白球落袋后需要恢复，再进入自由球 / 击球状态
    if (cueBall.potted) restoreCueBall();

    beginTurn();
  }

  function restoreCueBall() {
    cueBall.potted = false;
    cueBall.vx = 0;
    cueBall.vy = 0;
    cueBall.x = CFG.W * 0.25;
    cueBall.y = CFG.H / 2;
  }

  /**
   * 进入某一方的回合，根据“是否 AI / 是否自由球”切换到对应状态。
   * 这是状态机里的核心分支。
   */
  function beginTurn() {
    game.shot = null;
    game.cueHeld = false;
    if (cueBall) {
      cueBall.spinX = 0;
      cueBall.spinY = 0;
    }
    updatePowerUI();
    updateShotControls();

    const player = game.players[game.current];
    updateHUD();

    if (player.isAI) {
      if (game.ballInHand) {
        aiPlaceCueBall();
        game.ballInHand = false;
        game.cueHeld = false;
      }
      game.phase = "aiThinking";
      game.aiTimer = 0.85;
      setStatus("电脑正在思考…", "thinking");
      setHint("AI 正在枚举目标球与袋口，计算最佳线路");
      updateHUD();
      return;
    }

    if (game.ballInHand) {
      if (cueBall.potted) restoreCueBall();
      game.phase = "ballInHand";
      if (!game.breakDone) {
        setStatus(`${player.name} 开球：先摆放白球`);
        setHint("拖动白球或点击台面放置，然后选择力度点击“击球”");
      } else {
        setStatus(`${player.name} 获得自由球`);
        setHint("拖动白球或点击台面任意合法位置放置");
      }
    } else {
      game.phase = "aiming";
      setStatus(`${player.name} 击球`);
      setHint("拖动台面瞄准，选择力度后点击“击球”（空格）");
    }
    updateHUD();
  }

  /** 白球是否放在合法位置：台内、不压球、不压袋口 */
  function isValidCuePosition(x, y) {
    const r = CFG.BALL_R;
    if (x < r + 2 || x > CFG.W - r - 2 || y < r + 2 || y > CFG.H - r - 2) {
      return false;
    }
    for (const b of balls) {
      if (b.potted || b.id === 0) continue;
      if (Math.hypot(b.x - x, b.y - y) < r * 2 + 1) return false;
    }
    for (const p of POCKETS) {
      if (Math.hypot(p.x - x, p.y - y) < CFG.POCKET_R + r + 2) return false;
    }
    return true;
  }

  /** 当前拖拽 / 点击时白球的目标位置 */
  function cueDropTarget() {
    if (!cueDrag.active) return { x: mouse.x, y: mouse.y };
    return {
      x: mouse.x + cueDrag.offsetX,
      y: mouse.y + cueDrag.offsetY
    };
  }

  /** 把白球放到指定位置，并结束摆球状态 */
  function placeCueAt(x, y) {
    if (game.phase !== "ballInHand") return false;
    if (!isValidCuePosition(x, y)) {
      setStatus("该位置不能放置白球", "foul");
      setHint("请避开其它球和袋口，拖到台面内重新放置");
      playTone(150, 0.08, 0.035, "square");
      return false;
    }

    cueBall.potted = false;
    cueBall.vx = 0;
    cueBall.vy = 0;
    cueBall.x = x;
    cueBall.y = y;

    game.cueHeld = false;
    game.ballInHand = false;
    game.phase = "aiming";
    aimAngle = cueBall.x < CFG.W / 2 ? 0 : Math.PI;

    setStatus(`${game.players[game.current].name} 击球`);
    setHint("拖动台面瞄准，选择力度后点击“击球”（空格）");
    spawnRing(x, y, "rgba(102, 255, 196, 0.85)", 8, 34, 0.42, 2);
    spawnBurst(x, y, "#7dffca", 8, 35, 95, 0.36, 1.4);
    playTone(520, 0.06, 0.04, "triangle");
    updateHUD();
    return true;
  }

  function tryPlaceCue() {
    if (game.phase !== "ballInHand" || !mouse.inside) return false;
    const target = cueDropTarget();
    return placeCueAt(target.x, target.y);
  }

  /* ==========================================================
   * 第 5 部分：AI 对手
   * ----------------------------------------------------------
   * 核心思想（几何 + 枚举 + 启发式评分）：
   *   1. 确定合法目标球（己方球；清台后为 8 号球）；
   *   2. 对“每颗目标球 × 每个袋口”枚举组合；
   *   3. 计算假想球（ghost ball）位置：
   *      白球需要撞到目标球后方 2R 处，才能把目标球送向袋口；
   *   4. 用点到线段距离检查两条路径是否被其它球挡住；
   *   5. 按切球角度、距离打分，选最高分；
   *   6. 根据难度加入瞄准误差，模拟不同水平。
   * ========================================================== */

  function aiTargets() {
    const me = game.players[game.current];
    const active = balls.filter((b) => !b.potted && b.id !== 0);

    if (!me.group) {
      // 球组未定时，先打任意非 8 号球
      return active.filter((b) => b.id !== 8);
    }

    const own = active.filter((b) => ballType(b.id) === me.group);
    return own.length > 0 ? own : active.filter((b) => b.id === 8);
  }

  /** 点 (px,py) 到线段 (ax,ay)-(bx,by) 的最短距离 */
  function pointSegmentDistance(px, py, ax, ay, bx, by) {
    const abx = bx - ax;
    const aby = by - ay;
    const lengthSq = abx * abx + aby * aby;
    if (lengthSq === 0) return Math.hypot(px - ax, py - ay);

    let t = ((px - ax) * abx + (py - ay) * aby) / lengthSq;
    t = Math.max(0, Math.min(1, t));
    return Math.hypot(px - (ax + t * abx), py - (ay + t * aby));
  }

  /** 路径是否畅通：忽略指定球，其它球与线段距离小于 2R 即视为遮挡 */
  function pathClear(ax, ay, bx, by, ignoreIds) {
    for (const b of balls) {
      if (b.potted || ignoreIds.includes(b.id)) continue;
      // 留 2 像素安全余量，避免“擦边”被判定为可通行
      if (pointSegmentDistance(b.x, b.y, ax, ay, bx, by) < CFG.BALL_R * 2 + 2) {
        return false;
      }
    }
    return true;
  }

  /**
   * 枚举所有“目标球 × 袋口”，返回最佳击球方案。
   * 返回值包含击球角度、力度建议等。
   */
  function findBestShot(cueX, cueY) {
    const targets = aiTargets();
    let best = null;

    for (const target of targets) {
      for (const pocket of POCKETS) {
        // 目标球 → 袋口方向
        const pdx = pocket.x - target.x;
        const pdy = pocket.y - target.y;
        const pocketDist = Math.hypot(pdx, pdy);
        if (pocketDist < 1) continue;

        const ux = pdx / pocketDist;
        const uy = pdy / pocketDist;

        // 假想球球心：目标球后方 2R 处
        const ghostX = target.x - ux * CFG.BALL_R * 2;
        const ghostY = target.y - uy * CFG.BALL_R * 2;

        // 假想球必须在台面内
        if (
          ghostX < CFG.BALL_R + 1 || ghostX > CFG.W - CFG.BALL_R - 1 ||
          ghostY < CFG.BALL_R + 1 || ghostY > CFG.H - CFG.BALL_R - 1
        ) continue;

        // 白球 → 假想球方向
        const cdx = ghostX - cueX;
        const cdy = ghostY - cueY;
        const cueDist = Math.hypot(cdx, cdy);
        if (cueDist < CFG.BALL_R) continue;

        // 切球角度：白球入射方向与目标球出球方向的夹角余弦
        const cosCut = (cdx / cueDist) * ux + (cdy / cueDist) * uy;
        if (cosCut < 0.25) continue; // 太薄，容易失误

        // 两条路径都要畅通
        if (!pathClear(cueX, cueY, ghostX, ghostY, [0, target.id])) continue;
        if (!pathClear(target.x, target.y, pocket.x, pocket.y, [0, target.id])) continue;

        // 启发式评分：角度越正、总距离越短越好
        const score = cosCut * 10 - (cueDist + pocketDist) / 1100;

        if (!best || score > best.score) {
          best = {
            score,
            target,
            pocket,
            cueDist,
            pocketDist,
            angle: Math.atan2(cdy, cdx)
          };
        }
      }
    }

    if (best) return best;

    // 没有可进球线路：退化为“打最近的合法球”防守
    const sorted = [...targets].sort(
      (a, b) =>
        Math.hypot(a.x - cueX, a.y - cueY) -
        Math.hypot(b.x - cueX, b.y - cueY)
    );

    // 优先选择“白球到球心”路径畅通的最近目标，避免先碰到别的球
    let nearest = sorted.find((target) =>
      pathClear(cueX, cueY, target.x, target.y, [0, target.id])
    ) || sorted[0] || null;

    let nearestDist = Infinity;
    if (nearest) {
      nearestDist = Math.hypot(nearest.x - cueX, nearest.y - cueY);
    }

    if (!nearest) return { angle: 0, power: 45, target: null, pocket: null };
    return {
      angle: Math.atan2(nearest.y - cueY, nearest.x - cueX),
      power: 48,
      target: nearest,
      pocket: null,
      cueDist: nearestDist,
      pocketDist: 0,
      score: 0
    };
  }

  /** AI 自由球：在若干候选点中挑一个“能打出最好线路”的位置 */
  function aiPlaceCueBall() {
    const candidates = [];
    for (let ix = 1; ix <= 7; ix++) {
      for (let iy = 1; iy <= 5; iy++) {
        candidates.push({
          x: (CFG.W * ix) / 8,
          y: (CFG.H * iy) / 6
        });
      }
    }

    let bestPos = null;
    let bestScore = -Infinity;

    for (const pos of candidates) {
      if (!isValidCuePosition(pos.x, pos.y)) continue;
      const plan = findBestShot(pos.x, pos.y);
      const score = plan && plan.pocket ? plan.score : -100;
      if (score > bestScore) {
        bestScore = score;
        bestPos = pos;
      }
    }

    if (!bestPos) bestPos = { x: CFG.W * 0.25, y: CFG.H / 2 };

    cueBall.potted = false;
    cueBall.vx = 0;
    cueBall.vy = 0;
    cueBall.x = bestPos.x;
    cueBall.y = bestPos.y;
  }

  /** AI 真正出杆：计算方案 + 难度误差 + 调用统一击球函数 */
  function aiShoot() {
    const plan = findBestShot(cueBall.x, cueBall.y);

    let angle = plan.angle;
    let shotPower = plan.power || 48;

    if (plan.pocket) {
      const distance = plan.cueDist + plan.pocketDist;
      shotPower = Math.max(38, Math.min(92, 32 + distance / 16));
    }

    // 难度参数：[角度误差(弧度), 力度误差]
    const errorCfg = {
      easy: [0.055, 14],
      normal: [0.022, 6],
      hard: [0.007, 2]
    }[game.difficulty] || [0.022, 6];

    angle += (Math.random() * 2 - 1) * errorCfg[0];
    shotPower = Math.max(
      25,
      Math.min(100, shotPower + (Math.random() * 2 - 1) * errorCfg[1])
    );

    aimAngle = angle;

    if (plan.target) {
      const pocketName = plan.pocket ? "袋口" : "防守";
      addLog(`电脑瞄准 ${plan.target.id} 号球（${pocketName}）`);
    }

    setStatus("电脑击球", "thinking");
    launchShot(angle, shotPower, "ai");
  }

  /* ==========================================================
   * 第 6 部分：输入处理与有限状态机
   * ========================================================== */

  /** 把屏幕坐标转换成台面坐标 */
  function toTableCoords(event) {
    const rect = canvas.getBoundingClientRect();
    if (rect.width === 0 || rect.height === 0) return null;

    return {
      x: ((event.clientX - rect.left) / rect.width) * LOGICAL_W - CFG.RAIL,
      y: ((event.clientY - rect.top) / rect.height) * LOGICAL_H - CFG.RAIL
    };
  }

  /** 把角度规范到 (-π, π] */
  function normalizeAngle(angle) {
    while (angle <= -Math.PI) angle += TAU;
    while (angle > Math.PI) angle -= TAU;
    return angle;
  }

  /**
   * 角度微调：以“度”为单位增减瞄准角。
   * 鼠标负责粗瞄，旋钮 / 方向键负责细瞄。
   */
  function adjustAim(deltaDeg) {
    if (game.phase !== "aiming" || isAITurn() || game.cueHeld) return;
    aimAngle = normalizeAngle(aimAngle + (deltaDeg * Math.PI) / 180);
    updateShotControls();
  }

  /** 把加塞参数翻译成中文提示 */
  function englishLabel(value = english) {
    if (Math.hypot(value.x, value.y) < 0.08) return "无塞";

    const parts = [];
    if (value.y > 0.12) parts.push("高杆");
    else if (value.y < -0.12) parts.push("低杆");
    if (value.x > 0.12) parts.push("右塞");
    else if (value.x < -0.12) parts.push("左塞");
    return parts.length > 0 ? parts.join(" + ") : "轻微加塞";
  }

  // 缓存上一次的显示值，避免每帧都写 DOM
  let knobShownDeg = null;
  let spinShownLabel = null;

  function updateShotControls() {
    const deg = (aimAngle * 180) / Math.PI;
    if (knobShownDeg === null || Math.abs(deg - knobShownDeg) > 0.05) {
      const shown = ((deg % 360) + 360) % 360;
      knobNeedle.style.transform = `rotate(${deg}deg)`;
      angleValue.textContent = `${shown.toFixed(1)}°`;
      angleKnob.setAttribute("aria-valuenow", shown.toFixed(1));
      knobShownDeg = deg;
    }

    spinDot.style.transform =
      `translate(${(english.x * 30).toFixed(1)}px, ${(-english.y * 30).toFixed(1)}px)`;
    spinDot.classList.toggle("active", Math.hypot(english.x, english.y) > 0.05);

    const label = englishLabel();
    if (label !== spinShownLabel) {
      spinValue.textContent = label;
      spinShownLabel = label;
    }
  }

  /* ---------- 角度旋钮：拖拽旋转 ---------- */
  let knobDrag = null;

  function endKnobDrag(event) {
    if (!knobDrag) return;
    knobDrag = null;
    angleKnob.classList.remove("dragging");
    if (event && angleKnob.hasPointerCapture(event.pointerId)) {
      angleKnob.releasePointerCapture(event.pointerId);
    }
  }

  angleKnob.addEventListener("pointerdown", (event) => {
    if (game.phase !== "aiming" || isAITurn()) return;
    ensureAudio();

    const rect = angleKnob.getBoundingClientRect();
    const cx = rect.left + rect.width / 2;
    const cy = rect.top + rect.height / 2;

    knobDrag = {
      startPointer: Math.atan2(event.clientY - cy, event.clientX - cx),
      startAim: aimAngle,
      cx,
      cy
    };

    angleKnob.classList.add("dragging");
    angleKnob.setPointerCapture(event.pointerId);
    event.preventDefault();
  });

  angleKnob.addEventListener("pointermove", (event) => {
    if (!knobDrag) return;

    const pointer = Math.atan2(event.clientY - knobDrag.cy, event.clientX - knobDrag.cx);
    let delta = pointer - knobDrag.startPointer;
    if (delta > Math.PI) delta -= TAU;
    if (delta < -Math.PI) delta += TAU;

    aimAngle = normalizeAngle(knobDrag.startAim + delta);
    updateShotControls();
  });

  angleKnob.addEventListener("pointerup", endKnobDrag);
  angleKnob.addEventListener("pointercancel", endKnobDrag);

  // 旋钮旁的 ±1° / ±0.2° 按钮
  document.querySelectorAll("[data-angle-step]").forEach((button) => {
    button.addEventListener("click", () => {
      adjustAim(parseFloat(button.dataset.angleStep));
    });
  });

  /* ---------- 加塞圆盘：点击 / 拖动选择击球点 ---------- */
  let spinDragging = false;

  function setEnglishFromPointer(event) {
    const rect = spinPad.getBoundingClientRect();
    const cx = rect.left + rect.width / 2;
    const cy = rect.top + rect.height / 2;
    const radius = rect.width * 0.45;

    let dx = (event.clientX - cx) / radius;
    let dy = (event.clientY - cy) / radius;
    const length = Math.hypot(dx, dy);
    if (length > 1) {
      dx /= length;
      dy /= length;
    }

    english.x = dx;
    english.y = -dy; // 屏幕 y 向下，物理上“上”为正
    updateShotControls();
  }

  spinPad.addEventListener("pointerdown", (event) => {
    if (game.phase !== "aiming" || isAITurn()) return;
    ensureAudio();
    spinDragging = true;
    spinPad.setPointerCapture(event.pointerId);
    setEnglishFromPointer(event);
    event.preventDefault();
  });

  spinPad.addEventListener("pointermove", (event) => {
    if (spinDragging) setEnglishFromPointer(event);
  });

  const endSpinDrag = (event) => {
    spinDragging = false;
    if (event && spinPad.hasPointerCapture(event.pointerId)) {
      spinPad.releasePointerCapture(event.pointerId);
    }
  };

  spinPad.addEventListener("pointerup", endSpinDrag);
  spinPad.addEventListener("pointercancel", endSpinDrag);

  document.getElementById("spinReset").addEventListener("click", () => {
    english.x = 0;
    english.y = 0;
    updateShotControls();
  });

  /** 设置自由力度（5–100），保留到下一次击球 */
  function setPower(value) {
    power = Math.max(CFG.POWER_MIN, Math.min(100, Number(value) || CFG.POWER_DEFAULT));
    updatePowerUI();
  }

  function canHumanShoot() {
    return Boolean(
      cueBall &&
      !cueBall.potted &&
      game.phase === "aiming" &&
      !isAITurn() &&
      !game.cueHeld
    );
  }

  /** 按当前选择的力度出杆 */
  function shootSelectedPower() {
    if (!canHumanShoot()) return;
    ensureAudio();
    launchShot(aimAngle, power, "human");
  }

  /** 统一出杆入口：人类和 AI 都走这里 */
  function launchShot(angle, shotPower, source, spinOverride = null) {
    if (!cueBall || cueBall.potted) return;

    // AI 默认不加塞，保持几何瞄准的可预测性；人类使用当前加塞设置
    const appliedSpin = source === "ai"
      ? { x: 0, y: 0 }
      : { ...(spinOverride || english) };

    const speed =
      CFG.MIN_SPEED + (shotPower / 100) * (CFG.MAX_SPEED - CFG.MIN_SPEED);

    cueBall.spinX = appliedSpin.x;
    cueBall.spinY = appliedSpin.y;
    cueBall.vx = Math.cos(angle) * speed;
    cueBall.vy = Math.sin(angle) * speed;

    // 击球瞬间：球杆皮头闪光 + 巧粉粒子 + 轻微震动
    spawnShotFx(cueBall.x, cueBall.y, angle, appliedSpin, shotPower);
    screenShake = Math.max(screenShake, 1.2 + shotPower * 0.018);

    game.shot = {
      firstHit: null,          // 白球第一颗碰到的球
      railAfterContact: false, // 碰球后是否有球碰库
      potted: [],              // 本杆落袋的球号
      cuePotted: false,        // 白球是否落袋
      onEightBefore: isOnEight(game.current), // 出杆前是否已清台
      isBreak: !game.breakDone,
      power: shotPower,
      spin: appliedSpin         // 本杆加塞
    };

    game.phase = "shooting";
    game.cueHeld = false;
    if (source !== "ai") {
      power = shotPower;
      updatePowerUI();
    }
    updateHUD();

    const player = game.players[game.current];
    setStatus(`${player.name} 击球中…`);
    setHint("球在运动，请稍候…");

    if (source === "human") {
      const label = englishLabel(appliedSpin);
      const extra = label === "无塞" ? "" : `，${label}`;
      addLog(`${player.name} 击球（力度 ${Math.round(shotPower)}%${extra}）`);
    }

    playTone(110, 0.08, 0.05, "triangle");
  }

  // ---------- 鼠标 / 触摸：拖动只负责瞄准或摆球，出杆统一由按钮触发 ----------
  function updatePointerPosition(event) {
    const pos = toTableCoords(event);
    if (!pos) return null;

    mouse.x = pos.x;
    mouse.y = pos.y;
    mouse.inside =
      pos.x >= 0 && pos.x <= CFG.W && pos.y >= 0 && pos.y <= CFG.H;
    return pos;
  }

  function aimAtPointer() {
    if (!cueBall || cueBall.potted) return;
    const dx = mouse.x - cueBall.x;
    const dy = mouse.y - cueBall.y;
    if (Math.hypot(dx, dy) > 8) {
      aimAngle = Math.atan2(dy, dx);
      updateShotControls();
    }
  }

  canvas.addEventListener("pointermove", (event) => {
    const pos = updatePointerPosition(event);
    if (!pos) return;

    if (game.phase === "aiming" && !isAITurn() && !game.cueHeld) {
      aimAtPointer();
    }
  });

  canvas.addEventListener("pointerdown", (event) => {
    event.preventDefault();
    ensureAudio();

    const pos = updatePointerPosition(event);
    if (!pos || !mouse.inside) return;

    if (game.phase === "ballInHand") {
      // 点在白球附近时保持相对偏移，像真正“抓住”白球；
      // 点在其他位置时，以该点为落点。
      const nearCue =
        cueBall &&
        !cueBall.potted &&
        Math.hypot(pos.x - cueBall.x, pos.y - cueBall.y) <= CFG.BALL_R * 2.8;

      cueDrag.active = true;
      cueDrag.pointerId = event.pointerId;
      cueDrag.offsetX = nearCue ? cueBall.x - pos.x : 0;
      cueDrag.offsetY = nearCue ? cueBall.y - pos.y : 0;

      setHint(nearCue ? "拖动白球，松手放置" : "松手把白球放到此处");
      try {
        canvas.setPointerCapture(event.pointerId);
      } catch (error) {
        // 某些浏览器 / 合成事件不支持指针捕获，不影响拖拽逻辑
      }
      return;
    }

    if (game.phase === "aiming" && !isAITurn()) {
      aimAtPointer();
    }
  });

  function finishCueDrag(event, place) {
    if (!cueDrag.active) return;

    const target = cueDropTarget();
    const pointerId = cueDrag.pointerId;
    cueDrag.active = false;
    cueDrag.pointerId = null;
    cueDrag.offsetX = 0;
    cueDrag.offsetY = 0;

    if (event && pointerId !== null && canvas.hasPointerCapture(pointerId)) {
      canvas.releasePointerCapture(pointerId);
    }

    if (!place) return;

    const inside =
      target.x >= 0 && target.x <= CFG.W &&
      target.y >= 0 && target.y <= CFG.H;
    if (!inside) {
      setStatus("白球必须放在台面内", "foul");
      setHint("拖动白球或点击台面合法位置");
      return;
    }
    placeCueAt(target.x, target.y);
  }

  canvas.addEventListener("pointerup", (event) => finishCueDrag(event, true));
  canvas.addEventListener("pointercancel", (event) => finishCueDrag(event, false));

  // 指针在画布外松开也能完成摆球
  window.addEventListener("pointerup", (event) => finishCueDrag(event, true));

  canvas.addEventListener("pointerleave", () => {
    if (!cueDrag.active) mouse.inside = false;
  });

  canvas.addEventListener("contextmenu", (event) => event.preventDefault());

  // ---------- 键盘 ----------
  window.addEventListener("keydown", (event) => {
    if (event.target && ["SELECT", "INPUT", "TEXTAREA"].includes(event.target.tagName)) {
      return;
    }

    if (event.code === "Space") {
      event.preventDefault();
      if (!event.repeat) shootSelectedPower();
    } else if (event.key === "ArrowUp" || event.key === "ArrowDown") {
      event.preventDefault();
      setPower(power + (event.key === "ArrowUp" ? 5 : -5));
    } else if (event.key === "ArrowLeft" || event.key === "ArrowRight") {
      if (game.phase === "aiming" && !isAITurn()) {
        event.preventDefault();
        const step = event.shiftKey ? 0.2 : 1;
        adjustAim(event.key === "ArrowRight" ? step : -step);
      }
    } else if (event.key === "r" || event.key === "R") {
      resetGame();
    } else if (event.key === "Escape") {
      if (tablePanel.classList.contains("focus")) {
        setFocusMode(false);
      } else {
        closeHelp();
      }
    } else if (event.key === "h" || event.key === "H") {
      toggleHelp();
    }
  });

  // ---------- 按钮 ----------
  modeSwitch.addEventListener("click", (event) => {
    const button = event.target.closest("button[data-mode]");
    if (!button) return;
    const mode = button.dataset.mode;
    if (mode === game.mode) return;
    game.mode = mode;
    modeSwitch.querySelectorAll("button").forEach((b) => {
      b.classList.toggle("active", b.dataset.mode === mode);
    });
    difficultyRow.classList.toggle("hidden", mode !== "ai");
    resetGame();
  });

  difficultySelect.addEventListener("change", () => {
    game.difficulty = difficultySelect.value;
    addLog(`AI 难度调整为：${difficultySelect.options[difficultySelect.selectedIndex].text}`);
  });

  document.getElementById("restartBtn").addEventListener("click", resetGame);
  document.getElementById("resultRestart").addEventListener("click", resetGame);

  // ---------- 自由力度滑杆 + 击球按钮 ----------
  powerRange.addEventListener("pointerdown", ensureAudio);
  powerRange.addEventListener("input", () => setPower(powerRange.value));
  shootBtn.addEventListener("click", shootSelectedPower);

  // ---------- 手机专注模式（不依赖 Fullscreen API） ----------
  function setFocusMode(enabled) {
    tablePanel.classList.toggle("focus", enabled);
    focusExit.hidden = !enabled;
    focusBtn.setAttribute("aria-pressed", String(enabled));
    focusBtn.textContent = enabled ? "退出全屏" : "全屏";
    if (enabled) {
      setHint("专注模式：拖动台面瞄准，选择力度后点击“击球”");
    }
    // 画布尺寸随布局变化，重新计算 DPR 分辨率
    requestAnimationFrame(resizeCanvas);
  }

  function toggleFocusMode() {
    setFocusMode(!tablePanel.classList.contains("focus"));
  }

  focusBtn.addEventListener("click", toggleFocusMode);
  focusExit.addEventListener("click", () => setFocusMode(false));

  soundBtn.addEventListener("click", () => {
    soundOn = !soundOn;
    soundBtn.textContent = `音效：${soundOn ? "开" : "关"}`;
    soundBtn.setAttribute("aria-pressed", String(soundOn));
  });

  document.getElementById("helpBtn").addEventListener("click", toggleHelp);
  document.getElementById("closeHelp").addEventListener("click", closeHelp);
  helpModal.addEventListener("click", (event) => {
    if (event.target === helpModal) closeHelp();
  });

  function toggleHelp() {
    helpModal.hidden = !helpModal.hidden;
  }

  function closeHelp() {
    helpModal.hidden = true;
  }

  /* ==========================================================
   * 第 7 部分：Canvas 渲染
   * ========================================================== */

  /** 根据设备像素比设置画布分辨率，保证高清屏不模糊 */
  function resizeCanvas() {
    const dpr = Math.min(window.devicePixelRatio || 1, 2);
    const w = Math.round(LOGICAL_W * dpr);
    const h = Math.round(LOGICAL_H * dpr);
    if (canvas.width !== w || canvas.height !== h) {
      canvas.width = w;
      canvas.height = h;
    }
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  }

  function roundRect(x, y, w, h, r) {
    const radius = Math.min(r, w / 2, h / 2);
    ctx.beginPath();
    ctx.moveTo(x + radius, y);
    ctx.arcTo(x + w, y, x + w, y + h, radius);
    ctx.arcTo(x + w, y + h, x, y + h, radius);
    ctx.arcTo(x, y + h, x, y, radius);
    ctx.arcTo(x, y, x + w, y, radius);
    ctx.closePath();
  }

  /** 颜色混合：把 hex 颜色向白色或黑色靠拢 */
  function mixColor(hex, target, amount) {
    const num = parseInt(hex.slice(1), 16);
    const r = (num >> 16) & 255;
    const g = (num >> 8) & 255;
    const b = num & 255;
    const tr = target === "white" ? 255 : 0;
    const tg = target === "white" ? 255 : 0;
    const tb = target === "white" ? 255 : 0;
    const mix = (c, t) => Math.round(c + (t - c) * amount);
    return `rgb(${mix(r, tr)}, ${mix(g, tg)}, ${mix(b, tb)})`;
  }

  function render(now) {
    ctx.clearRect(0, 0, LOGICAL_W, LOGICAL_H);
    ctx.fillStyle = "#070b09";
    ctx.fillRect(0, 0, LOGICAL_W, LOGICAL_H);

    ctx.save();
    // 轻微屏幕震动：只在球台内部，避免露出页面底色
    if (screenShake > 0.04) {
      ctx.translate(
        (Math.random() * 2 - 1) * screenShake,
        (Math.random() * 2 - 1) * screenShake
      );
    }

    drawTableBase();

    ctx.save();
    ctx.translate(CFG.RAIL, CFG.RAIL);

    drawPockets();
    drawTableMarkings();
    drawAim(now);
    drawBalls();
    drawCuePlacementGhost(now);
    drawEffects();

    ctx.restore();

    drawRailDiamonds();
    ctx.restore();
  }

  function drawTableBase() {
    // 球台投影
    ctx.save();
    ctx.shadowColor = "rgba(0, 0, 0, 0.8)";
    ctx.shadowBlur = 24;
    ctx.shadowOffsetY = 12;
    ctx.fillStyle = "#080604";
    roundRect(2, 4, LOGICAL_W - 4, LOGICAL_H - 4, 24);
    ctx.fill();
    ctx.restore();

    // 木质外框
    const wood = ctx.createLinearGradient(0, 0, 0, LOGICAL_H);
    wood.addColorStop(0, "#5a3d25");
    wood.addColorStop(0.24, "#795734");
    wood.addColorStop(0.52, "#5b3d24");
    wood.addColorStop(0.78, "#3b2718");
    wood.addColorStop(1, "#21140c");
    ctx.fillStyle = wood;
    roundRect(3, 3, LOGICAL_W - 6, LOGICAL_H - 6, 24);
    ctx.fill();

    // 木纹：被裁切在木框内，增加真实木料层次
    ctx.save();
    roundRect(3, 3, LOGICAL_W - 6, LOGICAL_H - 6, 24);
    ctx.clip();
    for (let i = 0; i < 34; i++) {
      const y = 5 + (i / 33) * (LOGICAL_H - 10);
      const wobble = Math.sin(i * 1.7) * 4;
      ctx.beginPath();
      ctx.moveTo(-6, y);
      ctx.bezierCurveTo(
        LOGICAL_W * 0.28, y + wobble,
        LOGICAL_W * 0.66, y - wobble * 0.8,
        LOGICAL_W + 6, y + wobble * 0.35
      );
      ctx.strokeStyle = i % 3 === 0
        ? "rgba(255, 221, 168, 0.055)"
        : "rgba(20, 9, 3, 0.16)";
      ctx.lineWidth = i % 4 === 0 ? 1.6 : 0.8;
      ctx.stroke();
    }

    // 木框上的两道浅色拼接线
    ctx.strokeStyle = "rgba(255, 225, 176, 0.07)";
    ctx.lineWidth = 1;
    for (const inset of [13, 19]) {
      roundRect(inset, inset, LOGICAL_W - inset * 2, LOGICAL_H - inset * 2, 18);
      ctx.stroke();
    }
    ctx.restore();

    // 外框倒角高光 + 深色内边
    const bevel = ctx.createLinearGradient(0, 0, 0, LOGICAL_H);
    bevel.addColorStop(0, "rgba(255, 236, 200, 0.32)");
    bevel.addColorStop(0.18, "rgba(255, 221, 168, 0.08)");
    bevel.addColorStop(1, "rgba(0, 0, 0, 0.28)");
    ctx.strokeStyle = bevel;
    ctx.lineWidth = 2;
    roundRect(4, 4, LOGICAL_W - 8, LOGICAL_H - 8, 23);
    ctx.stroke();

    ctx.strokeStyle = "rgba(0, 0, 0, 0.55)";
    ctx.lineWidth = 1.5;
    roundRect(CFG.RAIL - 20, CFG.RAIL - 20, CFG.W + 40, CFG.H + 40, 16);
    ctx.stroke();

    // 四角黄铜装饰螺钉
    const drawScrew = (x, y, r) => {
      const brass = ctx.createRadialGradient(x - r * 0.4, y - r * 0.4, 0, x, y, r);
      brass.addColorStop(0, "#fff0c4");
      brass.addColorStop(0.45, "#d8b878");
      brass.addColorStop(1, "#5e4524");
      ctx.beginPath();
      ctx.arc(x, y, r, 0, TAU);
      ctx.fillStyle = brass;
      ctx.fill();
      ctx.strokeStyle = "rgba(20, 12, 5, 0.75)";
      ctx.lineWidth = 1;
      ctx.stroke();
      ctx.beginPath();
      ctx.moveTo(x - r * 0.42, y);
      ctx.lineTo(x + r * 0.42, y);
      ctx.strokeStyle = "rgba(70, 45, 20, 0.75)";
      ctx.lineWidth = 1;
      ctx.stroke();
    };
    drawScrew(17, 17, 6.5);
    drawScrew(LOGICAL_W - 17, 17, 6.5);
    drawScrew(17, LOGICAL_H - 17, 6.5);
    drawScrew(LOGICAL_W - 17, LOGICAL_H - 17, 6.5);

    // 库边内衬：深绿色台呢包边 + 倒角
    const cushion = ctx.createLinearGradient(0, CFG.RAIL - 14, 0, CFG.RAIL + 6);
    cushion.addColorStop(0, "#061d16");
    cushion.addColorStop(0.45, "#0c402e");
    cushion.addColorStop(1, "#072b1f");
    ctx.fillStyle = cushion;
    roundRect(CFG.RAIL - 14, CFG.RAIL - 14, CFG.W + 28, CFG.H + 28, 14);
    ctx.fill();

    // 台呢
    const felt = ctx.createRadialGradient(
      CFG.RAIL + CFG.W * 0.48,
      CFG.RAIL + CFG.H * 0.36,
      16,
      CFG.RAIL + CFG.W * 0.5,
      CFG.RAIL + CFG.H * 0.52,
      CFG.W * 0.72
    );
    felt.addColorStop(0, "#158969");
    felt.addColorStop(0.48, "#0d6a4e");
    felt.addColorStop(0.82, "#09533c");
    felt.addColorStop(1, "#063d2b");
    ctx.fillStyle = felt;
    ctx.fillRect(CFG.RAIL, CFG.RAIL, CFG.W, CFG.H);

    // 台呢纤维纹理
    const pattern = getClothPattern();
    if (pattern) {
      ctx.save();
      ctx.beginPath();
      ctx.rect(CFG.RAIL, CFG.RAIL, CFG.W, CFG.H);
      ctx.clip();
      ctx.globalAlpha = 0.2;
      ctx.fillStyle = pattern;
      ctx.fillRect(CFG.RAIL, CFG.RAIL, CFG.W, CFG.H);
      ctx.restore();
    }

    // 顶部灯光与四周暗角，让台面有微微的下沉感
    const topLight = ctx.createLinearGradient(0, CFG.RAIL, 0, CFG.RAIL + CFG.H);
    topLight.addColorStop(0, "rgba(192, 255, 224, 0.11)");
    topLight.addColorStop(0.32, "rgba(192, 255, 224, 0.02)");
    topLight.addColorStop(1, "rgba(0, 0, 0, 0.16)");
    ctx.fillStyle = topLight;
    ctx.fillRect(CFG.RAIL, CFG.RAIL, CFG.W, CFG.H);

    const vignette = ctx.createRadialGradient(
      CFG.RAIL + CFG.W * 0.5,
      CFG.RAIL + CFG.H * 0.5,
      CFG.W * 0.2,
      CFG.RAIL + CFG.W * 0.5,
      CFG.RAIL + CFG.H * 0.5,
      CFG.W * 0.72
    );
    vignette.addColorStop(0, "rgba(0, 0, 0, 0)");
    vignette.addColorStop(0.72, "rgba(0, 0, 0, 0.08)");
    vignette.addColorStop(1, "rgba(0, 0, 0, 0.36)");
    ctx.fillStyle = vignette;
    ctx.fillRect(CFG.RAIL, CFG.RAIL, CFG.W, CFG.H);

    // 库边落在台呢上的柔和阴影（四个方向各一条渐变）
    const shadowSize = 15;
    let shade = ctx.createLinearGradient(0, CFG.RAIL, 0, CFG.RAIL + shadowSize);
    shade.addColorStop(0, "rgba(0, 0, 0, 0.36)");
    shade.addColorStop(1, "rgba(0, 0, 0, 0)");
    ctx.fillStyle = shade;
    ctx.fillRect(CFG.RAIL, CFG.RAIL, CFG.W, shadowSize);

    shade = ctx.createLinearGradient(0, CFG.RAIL + CFG.H, 0, CFG.RAIL + CFG.H - shadowSize);
    shade.addColorStop(0, "rgba(0, 0, 0, 0.36)");
    shade.addColorStop(1, "rgba(0, 0, 0, 0)");
    ctx.fillStyle = shade;
    ctx.fillRect(CFG.RAIL, CFG.RAIL + CFG.H - shadowSize, CFG.W, shadowSize);

    shade = ctx.createLinearGradient(CFG.RAIL, 0, CFG.RAIL + shadowSize, 0);
    shade.addColorStop(0, "rgba(0, 0, 0, 0.3)");
    shade.addColorStop(1, "rgba(0, 0, 0, 0)");
    ctx.fillStyle = shade;
    ctx.fillRect(CFG.RAIL, CFG.RAIL, shadowSize, CFG.H);

    shade = ctx.createLinearGradient(CFG.RAIL + CFG.W, 0, CFG.RAIL + CFG.W - shadowSize, 0);
    shade.addColorStop(0, "rgba(0, 0, 0, 0.3)");
    shade.addColorStop(1, "rgba(0, 0, 0, 0)");
    ctx.fillStyle = shade;
    ctx.fillRect(CFG.RAIL + CFG.W - shadowSize, CFG.RAIL, shadowSize, CFG.H);

    // 台面内框细高光
    ctx.strokeStyle = "rgba(168, 255, 219, 0.18)";
    ctx.lineWidth = 1.2;
    ctx.strokeRect(CFG.RAIL + 0.75, CFG.RAIL + 0.75, CFG.W - 1.5, CFG.H - 1.5);
  }

  /** 生成一张低对比度噪点纹理，模拟台呢纤维 */
  function getClothPattern() {
    if (clothPattern) return clothPattern;

    const tile = document.createElement("canvas");
    tile.width = 72;
    tile.height = 72;
    const g = tile.getContext("2d");
    g.clearRect(0, 0, tile.width, tile.height);

    for (let i = 0; i < 760; i++) {
      const bright = Math.random() > 0.55;
      g.fillStyle = bright
        ? `rgba(210, 255, 232, ${0.05 + Math.random() * 0.12})`
        : `rgba(0, 28, 18, ${0.08 + Math.random() * 0.15})`;
      const size = Math.random() > 0.9 ? 2 : 1;
      g.fillRect(
        Math.floor(Math.random() * tile.width),
        Math.floor(Math.random() * tile.height),
        size,
        size
      );
    }

    clothPattern = ctx.createPattern(tile, "repeat");
    return clothPattern;
  }

  /** 库边上的菱形瞄准点（装饰） */
  function drawRailDiamonds() {
    ctx.save();

    const drawDiamond = (x, y) => {
      // 内嵌圆槽
      ctx.beginPath();
      ctx.arc(x, y, 5.2, 0, TAU);
      ctx.fillStyle = "rgba(31, 19, 10, 0.7)";
      ctx.fill();

      const brass = ctx.createLinearGradient(x - 4, y - 4, x + 4, y + 4);
      brass.addColorStop(0, "#fff0c8");
      brass.addColorStop(0.5, "#d8b878");
      brass.addColorStop(1, "#826134");
      ctx.beginPath();
      ctx.moveTo(x, y - 3.8);
      ctx.lineTo(x + 3.8, y);
      ctx.lineTo(x, y + 3.8);
      ctx.lineTo(x - 3.8, y);
      ctx.closePath();
      ctx.fillStyle = brass;
      ctx.fill();
      ctx.strokeStyle = "rgba(20, 12, 5, 0.5)";
      ctx.lineWidth = 0.6;
      ctx.stroke();
    };

    for (const k of [1, 2, 3, 5, 6, 7]) {
      const x = CFG.RAIL + (CFG.W * k) / 8;
      drawDiamond(x, CFG.RAIL / 2);
      drawDiamond(x, CFG.RAIL + CFG.H + CFG.RAIL / 2);
    }
    for (const k of [1, 2, 3]) {
      const y = CFG.RAIL + (CFG.H * k) / 4;
      drawDiamond(CFG.RAIL / 2, y);
      drawDiamond(CFG.RAIL + CFG.W + CFG.RAIL / 2, y);
    }
    ctx.restore();
  }

  function drawPockets() {
    const r = CFG.POCKET_R;

    for (const p of POCKETS) {
      ctx.save();

      // 袋口落在台呢上的阴影
      ctx.beginPath();
      ctx.arc(p.x + 1.5, p.y + 3, r + 12, 0, TAU);
      ctx.fillStyle = "rgba(0, 0, 0, 0.34)";
      ctx.fill();

      // 深色皮革外圈
      const leather = ctx.createRadialGradient(
        p.x - r * 0.35, p.y - r * 0.4, r * 0.3,
        p.x, p.y, r + 12
      );
      leather.addColorStop(0, "#2d1d13");
      leather.addColorStop(0.72, "#1b110b");
      leather.addColorStop(1, "#0b0704");
      ctx.beginPath();
      ctx.arc(p.x, p.y, r + 10, 0, TAU);
      ctx.fillStyle = leather;
      ctx.fill();

      // 黄铜/金属袋圈
      const brass = ctx.createLinearGradient(
        p.x - r - 8, p.y - r - 8,
        p.x + r + 8, p.y + r + 8
      );
      brass.addColorStop(0, "#5c4324");
      brass.addColorStop(0.24, "#f0d7a0");
      brass.addColorStop(0.48, "#9d7842");
      brass.addColorStop(0.72, "#e4c485");
      brass.addColorStop(1, "#4a341b");
      ctx.beginPath();
      ctx.arc(p.x, p.y, r + 6.5, 0, TAU);
      ctx.strokeStyle = brass;
      ctx.lineWidth = 4;
      ctx.stroke();

      // 内圈细亮线
      ctx.beginPath();
      ctx.arc(p.x, p.y, r + 4.3, 0, TAU);
      ctx.strokeStyle = "rgba(255, 245, 205, 0.42)";
      ctx.lineWidth = 0.9;
      ctx.stroke();

      // 黑洞：中心纯黑，边缘带一点绿色环境反光
      const hole = ctx.createRadialGradient(
        p.x - 2, p.y - 3, 1,
        p.x, p.y, r + 3.5
      );
      hole.addColorStop(0, "#000000");
      hole.addColorStop(0.58, "#010403");
      hole.addColorStop(0.88, "#06120d");
      hole.addColorStop(1, "#0d2f23");
      ctx.beginPath();
      ctx.arc(p.x, p.y, r + 3.5, 0, TAU);
      ctx.fillStyle = hole;
      ctx.fill();

      // 袋口内壁高光：左上角一小段月牙
      ctx.beginPath();
      ctx.arc(p.x, p.y, r + 2.4, Math.PI * 0.92, Math.PI * 1.55);
      ctx.strokeStyle = "rgba(198, 255, 229, 0.19)";
      ctx.lineWidth = 1.4;
      ctx.stroke();

      // 四个小铆钉
      for (let k = 0; k < 4; k++) {
        const a = Math.PI / 4 + k * Math.PI / 2;
        const bx = p.x + Math.cos(a) * (r + 6.5);
        const by = p.y + Math.sin(a) * (r + 6.5);
        ctx.beginPath();
        ctx.arc(bx, by, 1.55, 0, TAU);
        ctx.fillStyle = "rgba(255, 239, 190, 0.7)";
        ctx.fill();
        ctx.strokeStyle = "rgba(30, 18, 8, 0.55)";
        ctx.lineWidth = 0.5;
        ctx.stroke();
      }

      ctx.restore();
    }
  }

  function drawTableMarkings() {
    ctx.save();

    // 台面中央的淡色 8 号水印，低头视角更像真实球台
    ctx.font = '900 92px "Georgia", "Times New Roman", serif';
    ctx.textAlign = "center";
    ctx.textBaseline = "middle";
    ctx.fillStyle = "rgba(210, 255, 232, 0.025)";
    ctx.fillText("8", CFG.W * 0.5, CFG.H * 0.51);

    // 开球线（四分之一处）
    ctx.strokeStyle = "rgba(225, 255, 240, 0.10)";
    ctx.lineWidth = 1;
    ctx.setLineDash([4, 6]);
    ctx.beginPath();
    ctx.moveTo(CFG.W * 0.25, 0);
    ctx.lineTo(CFG.W * 0.25, CFG.H);
    ctx.stroke();
    ctx.setLineDash([]);

    // 置球点 + 小十字标记
    const spot = (x, y, radius, alpha) => {
      ctx.beginPath();
      ctx.arc(x, y, radius, 0, TAU);
      ctx.fillStyle = `rgba(240, 255, 246, ${alpha})`;
      ctx.fill();

      ctx.strokeStyle = `rgba(240, 255, 246, ${alpha * 0.55})`;
      ctx.lineWidth = 0.8;
      ctx.beginPath();
      ctx.moveTo(x - radius * 2.4, y);
      ctx.lineTo(x + radius * 2.4, y);
      ctx.moveTo(x, y - radius * 2.4);
      ctx.lineTo(x, y + radius * 2.4);
      ctx.stroke();
    };

    spot(CFG.W * 0.72, CFG.H / 2, 2.4, 0.20);
    spot(CFG.W * 0.5, CFG.H / 2, 1.8, 0.09);

    ctx.restore();
  }

  function drawBalls() {
    for (const b of balls) {
      if (b.potted) continue;
      if (b.id === 0 && game.cueHeld) continue;
      drawBall(b);
    }
  }

  function drawBall(b) {
    const x = b.x;
    const y = b.y;
    const r = CFG.BALL_R;

    // 阴影
    ctx.beginPath();
    ctx.ellipse(x + 2.5, y + 3.5, r * 1.02, r * 0.9, 0, 0, TAU);
    ctx.fillStyle = "rgba(0,0,0,0.32)";
    ctx.fill();

    // 球体底色
    if (b.id === 0) {
      const white = ctx.createRadialGradient(
        x - r * 0.35, y - r * 0.42, r * 0.1,
        x, y, r * 1.08
      );
      white.addColorStop(0, "#ffffff");
      white.addColorStop(0.55, "#f4f4ee");
      white.addColorStop(1, "#b9bdb6");
      ctx.beginPath();
      ctx.arc(x, y, r, 0, TAU);
      ctx.fillStyle = white;
      ctx.fill();
    } else if (b.type === "stripe") {
      // 花色球：白底 + 中间色带
      const base = ctx.createRadialGradient(
        x - r * 0.35, y - r * 0.42, r * 0.1,
        x, y, r * 1.08
      );
      base.addColorStop(0, "#ffffff");
      base.addColorStop(0.7, "#f0f0e8");
      base.addColorStop(1, "#c2c5bd");
      ctx.beginPath();
      ctx.arc(x, y, r, 0, TAU);
      ctx.fillStyle = base;
      ctx.fill();

      ctx.save();
      ctx.beginPath();
      ctx.arc(x, y, r - 0.5, 0, TAU);
      ctx.clip();
      const band = ctx.createLinearGradient(x, y - r * 0.6, x, y + r * 0.6);
      band.addColorStop(0, mixColor(b.color, "white", 0.28));
      band.addColorStop(0.5, b.color);
      band.addColorStop(1, mixColor(b.color, "black", 0.28));
      ctx.fillStyle = band;
      ctx.fillRect(x - r, y - r * 0.52, r * 2, r * 1.04);
      ctx.restore();
    } else {
      // 全色球 / 8 号球
      const grad = ctx.createRadialGradient(
        x - r * 0.35, y - r * 0.42, r * 0.1,
        x, y, r * 1.08
      );
      grad.addColorStop(0, mixColor(b.color, "white", 0.5));
      grad.addColorStop(0.5, b.color);
      grad.addColorStop(1, mixColor(b.color, "black", 0.38));
      ctx.beginPath();
      ctx.arc(x, y, r, 0, TAU);
      ctx.fillStyle = grad;
      ctx.fill();
    }

    // 球体高光
    const gloss = ctx.createRadialGradient(
      x - r * 0.38, y - r * 0.45, 0,
      x, y, r * 1.1
    );
    gloss.addColorStop(0, "rgba(255,255,255,0.55)");
    gloss.addColorStop(0.35, "rgba(255,255,255,0.08)");
    gloss.addColorStop(1, "rgba(0,0,0,0.25)");
    ctx.beginPath();
    ctx.arc(x, y, r, 0, TAU);
    ctx.fillStyle = gloss;
    ctx.fill();

    // 母球加塞标记：瞄准时显示当前选择，运动时显示剩余旋转
    if (b.id === 0) {
      const shownSpin = (game.phase === "aiming" || game.phase === "ballInHand")
        ? english
        : { x: b.spinX, y: b.spinY };
      const magnitude = Math.hypot(shownSpin.x, shownSpin.y);

      if (magnitude > 0.05) {
        const ox = shownSpin.x * r * 0.55;
        const oy = -shownSpin.y * r * 0.55;

        ctx.beginPath();
        ctx.moveTo(x, y);
        ctx.lineTo(x + ox, y + oy);
        ctx.strokeStyle = "rgba(229, 72, 77, 0.55)";
        ctx.lineWidth = 1.2;
        ctx.stroke();

        ctx.beginPath();
        ctx.arc(x + ox, y + oy, r * 0.2 + 1.6, 0, TAU);
        ctx.fillStyle = "rgba(255, 255, 255, 0.9)";
        ctx.fill();

        ctx.beginPath();
        ctx.arc(x + ox, y + oy, r * 0.2, 0, TAU);
        ctx.fillStyle = "#e5484d";
        ctx.fill();
      }
    }

    // 球号白底
    if (b.id !== 0) {
      ctx.beginPath();
      ctx.arc(x, y, r * 0.5, 0, TAU);
      ctx.fillStyle = "#f8f8f2";
      ctx.fill();
      ctx.strokeStyle = "rgba(0,0,0,0.12)";
      ctx.lineWidth = 0.8;
      ctx.stroke();

      ctx.fillStyle = "#101410";
      ctx.font = `800 ${Math.round(r * 0.72)}px "Microsoft YaHei", sans-serif`;
      ctx.textAlign = "center";
      ctx.textBaseline = "middle";
      ctx.fillText(String(b.id), x, y + 0.5);
    }

    // 轮廓
    ctx.beginPath();
    ctx.arc(x, y, r, 0, TAU);
    ctx.strokeStyle = "rgba(0,0,0,0.28)";
    ctx.lineWidth = 0.8;
    ctx.stroke();
  }

  function drawAim() {
    if (game.phase !== "aiming" || isAITurn()) return;
    if (!cueBall || cueBall.potted || game.cueHeld) return;

    const dirX = Math.cos(aimAngle);
    const dirY = Math.sin(aimAngle);
    const hit = predictAim(aimAngle);

    ctx.save();

    // 瞄准虚线
    ctx.beginPath();
    ctx.moveTo(cueBall.x, cueBall.y);
    ctx.lineTo(hit.x, hit.y);
    ctx.setLineDash([7, 7]);
    ctx.strokeStyle = "rgba(255,255,255,0.45)";
    ctx.lineWidth = 1.5;
    ctx.stroke();
    ctx.setLineDash([]);

    // 假想球（白球接触瞬间的位置）
    ctx.beginPath();
    ctx.arc(hit.x, hit.y, CFG.BALL_R, 0, TAU);
    ctx.strokeStyle = "rgba(255,255,255,0.65)";
    ctx.lineWidth = 1.4;
    ctx.stroke();

    // 目标球预计运动方向
    if (hit.ball) {
      const bx = hit.ball.x - hit.x;
      const by = hit.ball.y - hit.y;
      const dist = Math.hypot(bx, by) || 1;
      ctx.beginPath();
      ctx.moveTo(hit.ball.x, hit.ball.y);
      ctx.lineTo(hit.ball.x + (bx / dist) * 95, hit.ball.y + (by / dist) * 95);
      ctx.strokeStyle = "rgba(216,184,120,0.55)";
      ctx.lineWidth = 1.2;
      ctx.stroke();
    }

    // 球杆：选择的力度越大，向后拉得越远
    const pull = 8 + power * 0.34;
    const near = CFG.BALL_R + 8 + pull;
    const far = near + 235;

    // 白球外侧的力度环，直观显示当前选择的力度
    ctx.beginPath();
    ctx.arc(
      cueBall.x, cueBall.y, CFG.BALL_R + 6,
      -Math.PI / 2,
      -Math.PI / 2 + TAU * (power / 100)
    );
    ctx.strokeStyle = "rgba(255, 222, 150, 0.55)";
    ctx.lineWidth = 1.6;
    ctx.stroke();

    const stickGradient = ctx.createLinearGradient(
      cueBall.x - dirX * near, cueBall.y - dirY * near,
      cueBall.x - dirX * far, cueBall.y - dirY * far
    );
    stickGradient.addColorStop(0, "#f0d3a0");
    stickGradient.addColorStop(0.45, "#c99657");
    stickGradient.addColorStop(1, "#6b4524");

    ctx.beginPath();
    ctx.moveTo(cueBall.x - dirX * near, cueBall.y - dirY * near);
    ctx.lineTo(cueBall.x - dirX * far, cueBall.y - dirY * far);
    ctx.strokeStyle = stickGradient;
    ctx.lineWidth = 6;
    ctx.lineCap = "round";
    ctx.stroke();

    // 皮头
    ctx.beginPath();
    ctx.moveTo(cueBall.x - dirX * near, cueBall.y - dirY * near);
    ctx.lineTo(cueBall.x - dirX * (near + 9), cueBall.y - dirY * (near + 9));
    ctx.strokeStyle = "#4d8ad6";
    ctx.lineWidth = 5.5;
    ctx.stroke();

    ctx.restore();
  }

  function drawCuePlacementGhost(now) {
    if (game.phase !== "ballInHand") return;

    // 白球脚下的脉动光圈，提示“这颗球可以拖动”
    if (cueBall && !cueBall.potted) {
      const pulse = 1 + Math.sin(now * 0.006) * 0.16;
      ctx.save();
      ctx.beginPath();
      ctx.arc(cueBall.x, cueBall.y, CFG.BALL_R + 5, 0, TAU);
      ctx.strokeStyle = "rgba(102, 255, 196, 0.72)";
      ctx.lineWidth = 1.8;
      ctx.stroke();
      ctx.beginPath();
      ctx.arc(cueBall.x, cueBall.y, (CFG.BALL_R + 9) * pulse, 0, TAU);
      ctx.strokeStyle = "rgba(102, 255, 196, 0.22)";
      ctx.lineWidth = 1;
      ctx.stroke();
      ctx.restore();
    }

    if (!mouse.inside && !cueDrag.active) return;

    const target = cueDropTarget();
    const valid = isValidCuePosition(target.x, target.y);
    const color = valid ? "86, 245, 181" : "255, 106, 106";

    ctx.save();

    if (cueDrag.active && cueBall && !cueBall.potted) {
      ctx.beginPath();
      ctx.moveTo(cueBall.x, cueBall.y);
      ctx.lineTo(target.x, target.y);
      ctx.setLineDash([3, 7]);
      ctx.strokeStyle = `rgba(${color}, 0.34)`;
      ctx.lineWidth = 1;
      ctx.stroke();
      ctx.setLineDash([]);
    }

    // 落点预览球
    ctx.beginPath();
    ctx.arc(target.x, target.y, CFG.BALL_R, 0, TAU);
    ctx.fillStyle = `rgba(${color}, 0.2)`;
    ctx.fill();
    ctx.strokeStyle = `rgba(${color}, 0.94)`;
    ctx.lineWidth = 2;
    ctx.setLineDash([4, 4]);
    ctx.stroke();
    ctx.setLineDash([]);

    // 内外十字准星
    ctx.strokeStyle = `rgba(${color}, 0.7)`;
    ctx.lineWidth = 1;
    ctx.beginPath();
    ctx.moveTo(target.x - CFG.BALL_R - 4, target.y);
    ctx.lineTo(target.x - CFG.BALL_R + 2, target.y);
    ctx.moveTo(target.x + CFG.BALL_R - 2, target.y);
    ctx.lineTo(target.x + CFG.BALL_R + 4, target.y);
    ctx.moveTo(target.x, target.y - CFG.BALL_R - 4);
    ctx.lineTo(target.x, target.y - CFG.BALL_R + 2);
    ctx.moveTo(target.x, target.y + CFG.BALL_R - 2);
    ctx.lineTo(target.x, target.y + CFG.BALL_R + 4);
    ctx.stroke();

    if (!valid) {
      ctx.font = '700 11px "Microsoft YaHei", sans-serif';
      ctx.textAlign = "center";
      ctx.textBaseline = "bottom";
      ctx.fillStyle = "rgba(255, 142, 142, 0.95)";
      ctx.fillText("此处不能放球", target.x, target.y - CFG.BALL_R - 8);
    }

    ctx.restore();
  }

  function pushEffect(effect) {
    effects.push(effect);
    // 手机端限制粒子上限，避免连续碰撞时掉帧
    if (effects.length > 320) effects.splice(0, effects.length - 320);
  }

  function spawnRing(x, y, color, radius0, radius1, life, width) {
    pushEffect({
      kind: "ring",
      x, y,
      radius0,
      radius1,
      life,
      maxLife: life,
      color,
      width
    });
  }

  function spawnBurst(x, y, color, count, speedMin, speedMax, lifeMax, size) {
    for (let i = 0; i < count; i++) {
      const angle = Math.random() * TAU;
      const speed = speedMin + Math.random() * (speedMax - speedMin);
      const life = lifeMax * (0.68 + Math.random() * 0.32);
      pushEffect({
        kind: "particle",
        x, y,
        vx: Math.cos(angle) * speed,
        vy: Math.sin(angle) * speed,
        life,
        maxLife: life,
        color,
        size,
        drag: 0.93,
        gravity: 20
      });
    }
  }

  function spawnSpark(x, y, color, count, speedMin, speedMax, dirX, dirY) {
    for (let i = 0; i < count; i++) {
      const base = Math.atan2(dirY, dirX);
      const spread = (Math.random() - 0.5) * 1.7;
      const angle = base + spread + (Math.random() < 0.5 ? Math.PI : 0);
      const speed = speedMin + Math.random() * (speedMax - speedMin);
      const life = 0.16 + Math.random() * 0.22;
      pushEffect({
        kind: "particle",
        spark: true,
        x, y,
        vx: Math.cos(angle) * speed,
        vy: Math.sin(angle) * speed,
        life,
        maxLife: life,
        color,
        size: 1.1,
        drag: 0.9,
        gravity: 80
      });
    }
  }

  function spawnFloatingText(x, y, text, color, size = 14) {
    const life = 0.86;
    pushEffect({
      kind: "text",
      x, y,
      vy: -30,
      life,
      maxLife: life,
      color,
      text,
      size
    });
  }

  /** 击球瞬间：皮头闪光、巧粉碎屑、力度扩散环 */
  function spawnShotFx(x, y, angle, spin, shotPower) {
    spawnRing(x, y, "rgba(255, 243, 203, 0.95)", CFG.BALL_R + 2, CFG.BALL_R + 30, 0.34, 2.4);
    spawnRing(x, y, "rgba(255, 255, 255, 0.65)", 2, 14 + shotPower * 0.18, 0.22, 1.4);

    const backX = -Math.cos(angle);
    const backY = -Math.sin(angle);
    const count = 5 + Math.round(shotPower / 18);
    for (let i = 0; i < count; i++) {
      const spread = (Math.random() - 0.5) * 1.25;
      const a = angle + Math.PI + spread;
      const speed = 38 + Math.random() * (70 + shotPower * 0.9);
      const life = 0.24 + Math.random() * 0.26;
      pushEffect({
        kind: "particle",
        x: x + backX * (CFG.BALL_R + 4),
        y: y + backY * (CFG.BALL_R + 4),
        vx: Math.cos(a) * speed,
        vy: Math.sin(a) * speed,
        life,
        maxLife: life,
        color: Math.random() > 0.4 ? "#e7d9a7" : "#f8f3df",
        size: 1.2 + Math.random() * 1.4,
        drag: 0.9,
        gravity: 40
      });
    }

    if (Math.hypot(spin.x, spin.y) > 0.1) {
      spawnFloatingText(
        x, y - 27,
        englishLabel(spin),
        "rgba(255, 220, 140, 0.95)",
        11
      );
    }
  }

  /** 球与球碰撞：火花 + 细小冲击环 + 屏幕震动 */
  function spawnCollisionFx(x, y, impact, nx, ny) {
    const now = performance.now();
    if (now - lastImpactFx < 16) return;
    lastImpactFx = now;

    const power = Math.min(1.6, impact / 520);
    spawnSpark(x, y, "#fff3c7", 2 + Math.round(power * 5), 55, 180 + impact * 0.12, nx, ny);
    spawnRing(x, y, "rgba(255, 241, 200, 0.75)", 2, 7 + impact * 0.03, 0.2, 1.1);
    screenShake = Math.max(screenShake, Math.min(1.6, impact / 620));
  }

  /** 碰库：小范围绿色台呢粉尘 */
  function spawnCushionFx(x, y, speed, color) {
    const now = performance.now();
    if (now - lastImpactFx < 20) return;
    lastImpactFx = now;
    const count = Math.min(6, 2 + Math.round(speed / 380));
    for (let i = 0; i < count; i++) {
      const a = Math.random() * TAU;
      const s = 18 + Math.random() * 65;
      const life = 0.2 + Math.random() * 0.2;
      pushEffect({
        kind: "particle",
        x, y,
        vx: Math.cos(a) * s,
        vy: Math.sin(a) * s,
        life,
        maxLife: life,
        color: Math.random() > 0.55 ? "#a8ffd9" : color,
        size: 1 + Math.random() * 1.3,
        drag: 0.9,
        gravity: 20
      });
    }
  }

  /** 落袋：彩色粒子 + 金色扩散环 + 浮动球号 */
  function spawnPotEffect(x, y, color, id) {
    spawnBurst(x, y, color, 22, 45, 240, 0.52, 1.7);
    spawnBurst(x, y, "#ffe5a3", 7, 30, 130, 0.65, 1.3);
    spawnRing(x, y, "rgba(255, 228, 158, 0.95)", 4, 40, 0.52, 2.4);
    spawnRing(x, y, "rgba(255, 255, 255, 0.7)", 2, 22, 0.3, 1.2);

    const label = id === 0 ? "白球落袋" : id === 8 ? "8 号球落袋" : `${id} 号球落袋`;
    spawnFloatingText(
      x,
      y < CFG.H / 2 ? y + 34 : y - 30,
      label,
      id === 0 ? "rgba(255, 138, 138, 0.98)" : id === 8 ? "#ffe29a" : "rgba(235, 255, 244, 0.96)",
      id === 8 ? 16 : 13
    );
  }

  function updateEffects(dt) {
    for (let i = effects.length - 1; i >= 0; i--) {
      const p = effects[i];
      p.life -= dt;

      if (p.life <= 0) {
        effects.splice(i, 1);
        continue;
      }

      if (p.kind === "particle") {
        p.x += p.vx * dt;
        p.y += p.vy * dt;
        const damp = Math.pow(p.drag || 0.94, dt * 60);
        p.vx *= damp;
        p.vy *= damp;
        p.vy += (p.gravity || 0) * dt;
      } else if (p.kind === "text") {
        p.y += p.vy * dt;
        p.vy *= 0.96;
      }
    }

    if (screenShake > 0.02) {
      screenShake *= Math.exp(-9 * dt);
    } else {
      screenShake = 0;
    }
  }

  function drawEffects() {
    ctx.save();

    // 先画发光类特效，最后画文字，避免被叠加模式冲淡
    ctx.globalCompositeOperation = "lighter";
    for (const p of effects) {
      if (p.kind === "text") continue;
      const alpha = Math.max(0, p.life / p.maxLife);

      if (p.kind === "ring") {
        const progress = 1 - alpha;
        const radius = p.radius0 + (p.radius1 - p.radius0) * progress;
        ctx.beginPath();
        ctx.arc(p.x, p.y, Math.max(0.5, radius), 0, TAU);
        ctx.globalAlpha = alpha * 0.9;
        ctx.strokeStyle = p.color;
        ctx.lineWidth = Math.max(0.4, p.width * alpha);
        ctx.stroke();
      } else if (p.spark) {
        ctx.beginPath();
        ctx.moveTo(p.x, p.y);
        ctx.lineTo(p.x - p.vx * 0.018, p.y - p.vy * 0.018);
        ctx.globalAlpha = alpha;
        ctx.strokeStyle = p.color;
        ctx.lineWidth = p.size;
        ctx.stroke();
      } else {
        ctx.beginPath();
        ctx.arc(p.x, p.y, p.size * (0.55 + alpha * 0.45), 0, TAU);
        ctx.globalAlpha = alpha * 0.85;
        ctx.fillStyle = p.color;
        ctx.fill();
      }
    }

    ctx.globalCompositeOperation = "source-over";
    for (const p of effects) {
      if (p.kind !== "text") continue;
      const alpha = Math.max(0, p.life / p.maxLife);
      ctx.globalAlpha = Math.min(1, alpha * 1.7);
      ctx.font = `800 ${p.size}px "Microsoft YaHei", sans-serif`;
      ctx.textAlign = "center";
      ctx.textBaseline = "middle";
      ctx.fillStyle = p.color;
      ctx.shadowColor = "rgba(0, 0, 0, 0.8)";
      ctx.shadowBlur = 5;
      ctx.fillText(p.text, p.x, p.y);
      ctx.shadowBlur = 0;
    }

    ctx.restore();
  }

  /* ==========================================================
   * 第 8 部分：HUD、音效与游戏主循环
   * ========================================================== */

  function updatePowerUI() {
    const value = Math.max(CFG.POWER_MIN, Math.min(100, power));
    powerFill.style.width = `${value}%`;
    powerHandle.style.left = `${value}%`;
    powerValue.textContent = `${Math.round(value)}%`;

    const rounded = String(Math.round(value));
    if (powerRange.value !== rounded) powerRange.value = rounded;

    const enabled = canHumanShoot();
    if (shootBtn.disabled === enabled) shootBtn.disabled = !enabled;
    shootBtn.setAttribute("aria-disabled", String(!enabled));
    shootBtn.title = enabled
      ? "按选择的力度击球（空格）"
      : "等待轮到你击球";
  }

  function setStatus(text, tone = "") {
    statusText.textContent = text;
    statusText.className = "status-text" + (tone ? ` ${tone}` : "");
  }

  function setHint(text) {
    hintText.textContent = text;
  }

  function addLog(text, type = "") {
    game.log.push({ text, type });
    if (game.log.length > 30) game.log.shift();
    renderLog();
  }

  function renderLog() {
    logList.innerHTML = "";
    const recent = game.log.slice(-7);
    for (const item of recent) {
      const li = document.createElement("li");
      li.textContent = item.text;
      if (item.type) li.className = item.type;
      logList.appendChild(li);
    }
    logList.scrollTop = logList.scrollHeight;
  }

  function updateHUD() {
    game.players.forEach((player, index) => {
      const card = document.getElementById(`playerCard${index}`);
      if (!card) return;

      const active = game.phase !== "gameOver" && index === game.current;
      card.classList.toggle("active", active);
      card.classList.toggle("ai-turn", active && player.isAI);

      card.querySelector(".player-name").textContent = player.name;
      card.querySelector(".turn-badge").textContent = player.isAI
        ? "电脑击球"
        : "击球中";

      const groupBadge = card.querySelector(".group-badge");
      if (player.group === "solid") {
        groupBadge.textContent = "全色 1–7";
        groupBadge.className = "group-badge solid";
      } else if (player.group === "stripe") {
        groupBadge.textContent = "花色 9–15";
        groupBadge.className = "group-badge stripe";
      } else {
        groupBadge.textContent = "未定组";
        groupBadge.className = "group-badge";
      }

      card.querySelector(".score-text").textContent =
        `进球 ${player.potted.length}`;
      card.querySelector(".foul-text").textContent =
        `犯规 ${player.fouls}`;

      // 七颗己方球的小图标
      const ballRow = card.querySelector(".ball-row");
      ballRow.innerHTML = "";

      const ids = player.group === "solid"
        ? [1, 2, 3, 4, 5, 6, 7]
        : player.group === "stripe"
          ? [9, 10, 11, 12, 13, 14, 15]
          : [1, 2, 3, 4, 5, 6, 7];

      for (const id of ids) {
        const dot = document.createElement("span");
        dot.className = "mini-ball";
        if (player.group === "stripe") dot.classList.add("stripe");
        if (player.group && player.potted.includes(id)) dot.classList.add("potted");

        if (player.group) {
          dot.textContent = String(id);
          dot.style.setProperty("--ball-color", BALL_COLORS[id]);
          if (player.group === "solid") dot.style.background = BALL_COLORS[id];
        } else {
          dot.style.background = "#38443c";
        }
        ballRow.appendChild(dot);
      }
    });
  }

  function showResult(winnerIndex, reason) {
    const winner = game.players[winnerIndex];
    resultTitle.textContent = `${winner.name} 获胜`;
    resultReason.textContent = reason;
    resultOverlay.hidden = false;
  }

  function hideResult() {
    resultOverlay.hidden = true;
  }

  // ---------- 音效（Web Audio 合成，无需外部音频文件） ----------
  function ensureAudio() {
    if (!audioCtx) {
      const AudioContextClass = window.AudioContext || window.webkitAudioContext;
      if (!AudioContextClass) return;
      audioCtx = new AudioContextClass();
    }
    if (audioCtx.state === "suspended") audioCtx.resume();
  }

  function playTone(frequency, duration, volume, type = "sine") {
    if (!soundOn) return;
    try {
      ensureAudio();
      if (!audioCtx) return;

      const now = audioCtx.currentTime;
      const oscillator = audioCtx.createOscillator();
      const gain = audioCtx.createGain();

      oscillator.type = type;
      oscillator.frequency.setValueAtTime(frequency, now);
      gain.gain.setValueAtTime(volume, now);
      gain.gain.exponentialRampToValueAtTime(0.0001, now + duration);

      oscillator.connect(gain);
      gain.connect(audioCtx.destination);
      oscillator.start(now);
      oscillator.stop(now + duration);
    } catch (error) {
      // 音频失败不影响游戏
    }
  }

  function playImpact(strength) {
    const now = performance.now();
    if (now - lastHitSound < 28) return;
    lastHitSound = now;
    const volume = Math.min(0.08, 0.012 + strength * 0.00008);
    playTone(360 + Math.random() * 90, 0.045, volume, "square");
  }

  // ---------- 固定时间步长主循环 ----------
  let lastTime = 0;
  let accumulator = 0;

  function update(dt) {
    if (game.phase === "shooting") {
      updatePhysics(dt);
      if (allBallsStopped()) resolveShot();
    } else if (game.phase === "resolving") {
      game.resolveTimer -= dt;
      if (game.resolveTimer <= 0) finishResolve();
    } else if (game.phase === "aiThinking") {
      game.aiTimer -= dt;
      if (game.aiTimer <= 0) aiShoot();
    }

    updateEffects(dt);
  }

  function frame(now) {
    if (!lastTime) lastTime = now;
    let dt = (now - lastTime) / 1000;
    lastTime = now;
    dt = Math.min(dt, 0.05); // 切后台回来时避免“物理爆炸”

    accumulator += dt;
    let guard = 0;
    while (accumulator >= CFG.FIXED_DT && guard < 8) {
      update(CFG.FIXED_DT);
      accumulator -= CFG.FIXED_DT;
      guard++;
    }

    updatePowerUI();
    render(now);
    requestAnimationFrame(frame);
  }

  // ---------- 初始化 / 重开 ----------
  function resetGame() {
    // 依据模式创建两位玩家
    game.players = [
      {
        name: game.mode === "ai" ? "玩家" : "玩家 1",
        group: null,
        potted: [],
        fouls: 0,
        isAI: false
      },
      {
        name: game.mode === "ai" ? "电脑" : "玩家 2",
        group: null,
        potted: [],
        fouls: 0,
        isAI: game.mode === "ai"
      }
    ];

    game.current = 0;
    game.breakDone = false;
    game.ballInHand = true;   // 开球前先让玩家自由摆放白球
    game.cueHeld = false;
    game.winner = null;
    game.shot = null;
    game.pending = null;
    game.resolveTimer = 0;
    game.aiTimer = 0;
    game.log = [];

    rackBalls();
    effects.length = 0;
    screenShake = 0;

    cueDrag.active = false;
    cueDrag.pointerId = null;
    power = CFG.POWER_DEFAULT;
    english.x = 0;
    english.y = 0;
    game.phase = "ballInHand";
    aimAngle = 0;

    hideResult();
    helpModal.hidden = true;
    difficultyRow.classList.toggle("hidden", game.mode !== "ai");
    updateHUD();
    updatePowerUI();
    updateShotControls();
    setStatus(`${game.players[0].name} 开球：先摆放白球`);
    setHint("拖动白球或点击台面放置，然后选择力度点击“击球”");

    addLog("新对局开始，玩家 1 先摆放白球");
    if (game.mode === "ai") addLog("人机对战：你是玩家，电脑为对手");
  }

  function init() {
    resizeCanvas();
    window.addEventListener("resize", resizeCanvas);

    game.difficulty = difficultySelect.value;
    resetGame();

    // 预热音频上下文（第一次用户交互时真正创建）
    ensureAudio();

    requestAnimationFrame(frame);
  }

  /* ==========================================================
   * 调试接口（可选）
   * ----------------------------------------------------------
   * 仅用于课程演示、截图和自动化测试；不影响正常游戏。
   * 在浏览器控制台里输入 BilliardsDebug.state() 可查看局面。
   * ========================================================== */
  window.BilliardsDebug = {
    state() {
      return {
        phase: game.phase,
        mode: game.mode,
        current: game.current,
        breakDone: game.breakDone,
        ballInHand: game.ballInHand,
        winner: game.winner,
        players: game.players.map((p) => ({
          name: p.name,
          group: p.group,
          potted: [...p.potted],
          fouls: p.fouls,
          isAI: p.isAI
        })),
        balls: balls.map((b) => ({
          id: b.id,
          x: Math.round(b.x),
          y: Math.round(b.y),
          potted: b.potted
        }))
      };
    },

    /** 直接按角度和力度击球（绕过蓄力，方便测试）；可选传入加塞 {x, y} */
    shoot(angle, shotPower, spinVec) {
      if (game.phase === "aiming") {
        launchShot(angle, shotPower, "debug", spinVec || null);
      }
    },

    /** 设置瞄准角（弧度） */
    setAim(angle) {
      aimAngle = normalizeAngle(angle);
      updateShotControls();
    },

    /** 设置自由力度 */
    setPower(value) {
      power = Math.max(CFG.POWER_MIN, Math.min(100, Number(value) || CFG.POWER_DEFAULT));
      updatePowerUI();
    },

    /** 在开球 / 自由球阶段直接摆放白球 */
    placeCue(x, y) {
      if (game.phase === "ballInHand") {
        mouse.x = x;
        mouse.y = y;
        mouse.inside = true;
        return placeCueAt(x, y);
      }
      return false;
    },

    /** 设置加塞（x 左右，y 上下，范围 -1 ~ 1） */
    setEnglish(x, y) {
      english.x = Math.max(-1, Math.min(1, x));
      english.y = Math.max(-1, Math.min(1, y));
      const length = Math.hypot(english.x, english.y);
      if (length > 1) {
        english.x /= length;
        english.y /= length;
      }
      updateShotControls();
    },

    /** 摆放某颗球（球号 0 表示白球） */
    setBall(id, x, y) {
      const ball = getBall(id);
      if (!ball) return;
      ball.x = x;
      ball.y = y;
      ball.vx = 0;
      ball.vy = 0;
      ball.potted = false;
    },

    /** 直接把某颗球标记为已落袋（用于构造测试局面） */
    removeBall(id) {
      const ball = getBall(id);
      if (!ball) return;
      ball.potted = true;
      ball.vx = 0;
      ball.vy = 0;
    },

    /** 设置某位玩家的球组，用于测试 8 号球胜负 */
    setGroup(playerIndex, group) {
      if (game.players[playerIndex]) game.players[playerIndex].group = group;
    },

    /** 跳过开球标记，用于构造 8 号球测试局面 */
    setBreakDone(value = true) {
      game.breakDone = Boolean(value);
    },

    /** 直接切换击球方（用于测试 AI 回合） */
    setCurrent(index) {
      if (index !== 0 && index !== 1) return;
      game.current = index;
      beginTurn();
    },

    /** 查看 AI 当前会选择的击球方案 */
    plan() {
      const plan = findBestShot(cueBall.x, cueBall.y);
      return {
        angle: plan.angle,
        power: plan.power,
        target: plan.target ? plan.target.id : null,
        pocket: plan.pocket,
        cueDist: plan.cueDist,
        pocketDist: plan.pocketDist,
        score: plan.score
      };
    },

    /** 查看更完整的运行时状态（含白球是否被拿起） */
    detail() {
      return {
        ...this.state(),
        cueHeld: game.cueHeld,
        cueDragging: cueDrag.active,
        power,
        aimAngle,
        english: { ...english },
        cueSpin: { x: cueBall.spinX, y: cueBall.spinY },
        mouse: { ...mouse }
      };
    },

    reset: resetGame
  };

  init();
})();
