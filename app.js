/**
 * LIQORA Water Management Dashboard — app.js
 *
 * Connects to Firebase Realtime Database at:
 *   liquora/telemetry   (existing path — unchanged)
 *
 * All existing Firebase fields are preserved.
 * New diagnostic state is computed in the browser only.
 *
 * Leak detection:   Uses ohtLevel + active sump/bore flow rate
 *                   over a 2-minute rolling window while a pump is running.
 *                   Compares integrated inflow (L) with expected OHT volume
 *                   change from its level reading and configured capacity.
 *                   Requires 2 consecutive mismatched windows to raise warning.
 *
 * Blockage detection: Watches sumpFlowRate / boreFlowRate while the
 *                     corresponding pump is active.  After a startup transient
 *                     (5 s, matching SUMP/BORE_FLOW_CHECK_DELAY in firmware),
 *                     if flow stays below lowFlowThreshold for blockageDelaySec
 *                     it raises a "Possible blockage / low flow" warning.
 *                     Hysteresis: clears only after flow is above threshold for
 *                     5 consecutive seconds.  Separate from dry-run protection.
 */

import { initializeApp }      from "https://www.gstatic.com/firebasejs/13.1.0/firebase-app.js";
import { getDatabase, onValue, ref } from "https://www.gstatic.com/firebasejs/13.1.0/firebase-database.js";

// ────────────────────────────────────────────────────────────
// Firebase config — unchanged from original
// ────────────────────────────────────────────────────────────
const firebaseConfig = {
  apiKey:            "AIzaSyD3Q_CMuMgIZKVn-09KMzkWqnjQUCP6nlA",
  authDomain:        "test-base-2fb81.firebaseapp.com",
  databaseURL:       "https://test-base-2fb81-default-rtdb.firebaseio.com",
  projectId:         "test-base-2fb81",
  storageBucket:     "test-base-2fb81.firebasestorage.app",
  messagingSenderId: "762253667867",
  appId:             "1:762253667867:web:f0f98e60e83b30555d12be",
  measurementId:     "G-9WTY2SLE6H",
};

const fbApp      = initializeApp(firebaseConfig);
const database   = getDatabase(fbApp);
const telemetryRef = ref(database, "liquora/telemetry");   // ← same path as firmware

// ────────────────────────────────────────────────────────────
// Settings (persisted to localStorage)
// ────────────────────────────────────────────────────────────
const SETTINGS_KEY = "liqora_settings_v1";

function defaultSettings() {
  return {
    sumpCapacity:      2000,   // litres
    ohtCapacity:       2000,   // litres
    nominalFlow:       15.0,   // L/min
    lowFlowThreshold:  5.0,    // L/min  — low-flow alarm
    blockageDelaySec:  10,     // seconds of low-flow before blockage warning
    demoMode:          false,
    audibleAlarm:      false,
  };
}

let settings = { ...defaultSettings() };

function loadSettings() {
  try {
    const stored = JSON.parse(localStorage.getItem(SETTINGS_KEY) || "{}");
    settings = { ...defaultSettings(), ...stored };
  } catch (_) { /* ignore */ }
}

function saveSettings() {
  localStorage.setItem(SETTINGS_KEY, JSON.stringify(settings));
}

// ────────────────────────────────────────────────────────────
// Demo data generator
// ────────────────────────────────────────────────────────────
let demoPhase = 0;

function makeDemoSnapshot() {
  demoPhase = (demoPhase + 1) % 360;
  const t = demoPhase * Math.PI / 180;
  const sumpLevel  = Math.max(15, Math.min(98, 50 + 30 * Math.sin(t)));
  const ohtLevel   = Math.max(30, Math.min(95, 65 + 20 * Math.cos(t * 0.7)));
  const sumpPumpOn = ohtLevel < 85 && sumpLevel >= 15;
  const borePumpOn = false;
  return {
    sumpLevel:             +sumpLevel.toFixed(1),
    ohtLevel:              +ohtLevel.toFixed(1),
    sumpFlowRate:          sumpPumpOn ? +(13 + 3 * Math.sin(t * 2)).toFixed(2) : 0,
    boreFlowRate:          borePumpOn ? +(10 + 2 * Math.cos(t * 2)).toFixed(2) : 0,
    currentSource:         sumpPumpOn ? "SUMP" : (borePumpOn ? "BORE" : "NONE"),
    sumpAvailable:         sumpLevel >= 40,
    sumpLockedOut:         false,
    boreLockedOut:         false,
    municipalFillingActive:sumpLevel < 15,
    ohtFillingActive:      ohtLevel < 85,
    relays: {
      sumpPump:       sumpPumpOn,
      borePump:       borePumpOn,
      municipalValve: sumpLevel < 15,
      in4:            true,
    },
    updatedAt: Date.now(),
    _isDemo: true,
  };
}

// ────────────────────────────────────────────────────────────
// State
// ────────────────────────────────────────────────────────────
let lastData           = null;
let lastFirebaseUpdate = null;    // ms timestamp of last real Firebase update
let demoInterval       = null;
let isDemoMode         = false;

// Session accumulation (resets on page load — in-browser only)
let sessionPumpedL     = 0;       // integrated inflow litres
let sessionSumpS       = 0;       // seconds sump pump has been active
let sessionBoreS       = 0;       // seconds bore pump has been active
let sessionSumpL       = 0;       // litres from sump this session
let sessionBoreL       = 0;       // litres from bore this session
let sessionMuniL       = 0;       // litres from municipal (estimated)

// ── Blockage detection state ──
const blockage = {
  sump: {
    active:           false,   // pump is on and past startup transient
    lowFlowStartMs:   null,    // when flow first went below threshold
    warned:           false,   // warning currently active
    clearCounterS:    0,       // seconds above threshold (hysteresis)
  },
  bore: {
    active:           false,
    lowFlowStartMs:   null,
    warned:           false,
    clearCounterS:    0,
  },
};

// Startup-transient filter (mirror firmware's SUMP/BORE_FLOW_CHECK_DELAY = 5 s)
const PUMP_STARTUP_GRACE_MS = 5000;
let sumpPumpOnSinceMs = null;
let borePumpOnSinceMs = null;
let prevSumpPumpOn    = false;
let prevBorePumpOn    = false;

// ── Leak detection state ──
const LEAK_WINDOW_SEC       = 120;    // 2-minute rolling window
const LEAK_WINDOWS_TO_WARN  = 2;      // sustained mismatch across N windows
const LEAK_CLEAR_WINDOWS    = 2;      // must clear for N windows before resolving
const LEAK_TOLERANCE_FRAC   = 0.25;   // 25% discrepancy tolerance

let ohtLevelHistory   = [];   // [{ts, level}] ring-buffer
let leakWindowsBad    = 0;
let leakWindowsGood   = 0;
let leakWarned        = false;
let lastLeakCheckTs   = null;

// ── Analytics counters ──
let blockageIncidents = 0;
let leakAlerts        = 0;

// ── Event log (browser-side only) ──
const MAX_EVENTS   = 50;
let eventLog       = [];

// ── Flow chart data ──
const CHART_POINTS = 60;  // 60 samples (≈5 min at 5 s intervals)
let flowHistory    = { sump: [], bore: [], labels: [] };

// ────────────────────────────────────────────────────────────
// Utility helpers
// ────────────────────────────────────────────────────────────
const $ = (id) => document.getElementById(id);

function setText(id, text) {
  const el = $(id);
  if (el) el.textContent = text;
}

function setClass(id, cls) {
  const el = $(id);
  if (el) el.className = cls;
}

function fmt(n, decimals = 1) {
  const num = Number(n);
  return Number.isFinite(num) ? num.toFixed(decimals) : "—";
}

function fmtLitres(pct, capacityL) {
  const num = Number(pct);
  if (!Number.isFinite(num)) return "—";
  return Math.round((num / 100) * capacityL);
}

function timeStr(ts) {
  if (!ts) return "—";
  const d = new Date(Number(ts));
  return isNaN(d.getTime()) ? "—" : d.toLocaleTimeString();
}

function addEvent(type, title, desc, equipment = "") {
  const ev = { type, title, desc, equipment, ts: Date.now() };
  eventLog.unshift(ev);
  if (eventLog.length > MAX_EVENTS) eventLog.pop();
  renderEventLog();
}

// ────────────────────────────────────────────────────────────
// Tab navigation
// ────────────────────────────────────────────────────────────
const TABS = ["tabControl", "tabTanks", "tabPipeline", "tabStatus", "tabBluetooth"];
const TAB_TITLES = {
  tabControl:   "Dashboard",
  tabTanks:     "Water Monitoring",
  tabPipeline:  "Equipment Status",
  tabStatus:    "Analytics & History",
  tabBluetooth: "Bluetooth & Wi-Fi",
};

function switchTab(tabId) {
  TABS.forEach((id) => {
    const el = $(id);
    const btn = document.querySelector(`[data-tab="${id}"]`);
    if (!el || !btn) return;
    if (id === tabId) {
      el.hidden = false;
      el.classList.add("active");
      btn.classList.add("active");
      btn.setAttribute("aria-current", "page");
    } else {
      el.hidden = true;
      el.classList.remove("active");
      btn.classList.remove("active");
      btn.removeAttribute("aria-current");
    }
  });
  setText("pageTitle", TAB_TITLES[tabId] || "LIQORA");
}

document.querySelectorAll(".nav-btn").forEach((btn) => {
  btn.addEventListener("click", () => switchTab(btn.dataset.tab));
});

$("goToEventsBtn").addEventListener("click", () => switchTab("tabStatus"));

// ────────────────────────────────────────────────────────────
// Demo mode toggle
// ────────────────────────────────────────────────────────────
function applyDemoMode(active) {
  isDemoMode = active;
  settings.demoMode = active;
  saveSettings();

  const toggleBtn  = $("demoToggle");
  const demoCheck  = $("settingDemoMode");
  const demoBadge  = $("sysBadgeDemo");

  if (toggleBtn) {
    toggleBtn.setAttribute("aria-pressed", String(active));
    toggleBtn.classList.toggle("demo-active", active);
  }
  if (demoCheck)  demoCheck.checked = active;
  if (demoBadge)  demoBadge.classList.toggle("hidden", !active);

  if (active) {
    if (!demoInterval) {
      demoInterval = setInterval(() => {
        applySnapshot(makeDemoSnapshot());
      }, 1500);
    }
    addEvent("info", "Demo Mode Enabled", "Synthetic telemetry replacing live Firebase data.", "Settings");
  } else {
    clearInterval(demoInterval);
    demoInterval = null;
    addEvent("info", "Demo Mode Disabled", "Resumed live Firebase data.", "Settings");
  }
}

$("demoToggle").addEventListener("click", () => applyDemoMode(!isDemoMode));

$("settingDemoMode").addEventListener("change", (e) => applyDemoMode(e.target.checked));

// ────────────────────────────────────────────────────────────
// Settings save
// ────────────────────────────────────────────────────────────
function applySettingsFromUI() {
  settings.sumpCapacity     = Math.max(100, +$("settingSumpCapacity").value || 2000);
  settings.ohtCapacity      = Math.max(100, +$("settingOhtCapacity").value  || 2000);
  settings.nominalFlow      = Math.max(1,   +$("settingNominalFlow").value  || 15);
  settings.lowFlowThreshold = Math.max(0.1, +$("settingLowFlow").value      || 5);
  settings.blockageDelaySec = Math.max(5,   +$("settingBlockageDelay").value|| 10);
  settings.audibleAlarm     = $("settingAudibleAlarm").checked;
  saveSettings();
  // Reset diagnostic state when thresholds change
  blockage.sump.lowFlowStartMs = null;
  blockage.bore.lowFlowStartMs = null;
  addEvent("info", "Settings Saved", `Thresholds updated — nominal: ${settings.nominalFlow} L/min, low-flow alarm: ${settings.lowFlowThreshold} L/min, blockage delay: ${settings.blockageDelaySec} s.`, "Settings");
}

$("saveSettingsBtn").addEventListener("click", () => {
  applySettingsFromUI();
  $("saveSettingsBtn").textContent = "✓ Saved";
  setTimeout(() => { $("saveSettingsBtn").textContent = "Save & Apply Settings"; }, 2000);
});

function syncSettingsToUI() {
  $("settingSumpCapacity").value  = settings.sumpCapacity;
  $("settingOhtCapacity").value   = settings.ohtCapacity;
  $("settingNominalFlow").value   = settings.nominalFlow;
  $("settingLowFlow").value       = settings.lowFlowThreshold;
  $("settingBlockageDelay").value = settings.blockageDelaySec;
  $("settingAudibleAlarm").checked= settings.audibleAlarm;
  $("settingDemoMode").checked    = settings.demoMode;
}

// ────────────────────────────────────────────────────────────
// Sensor health helpers
// ────────────────────────────────────────────────────────────
function sensorHealthLabel(level) {
  if (level === null || level === undefined || level < 0) return ["err", "FAULT"];
  return ["ok", "NORMAL"];
}

function pumpLockoutLabel(locked) {
  return locked ? ["warn", "Locked out"] : ["", "Normal"];
}

// ────────────────────────────────────────────────────────────
// Blockage detection
// ────────────────────────────────────────────────────────────
const BLOCKAGE_HYSTERESIS_S = 5;   // seconds above threshold before clearing

function runBlockageDiagnostic(data, nowMs) {
  const sumpPumpOn = !!(data.relays?.sumpPump);
  const borePumpOn = !!(data.relays?.borePump);
  const sumpFlow   = Number(data.sumpFlowRate ?? 0);
  const boreFlow   = Number(data.boreFlowRate  ?? 0);

  // Track pump start times for startup transient
  if (sumpPumpOn && !prevSumpPumpOn) {
    sumpPumpOnSinceMs = nowMs;
    blockage.sump.lowFlowStartMs = null;
    blockage.sump.clearCounterS  = 0;
  }
  if (!sumpPumpOn && prevSumpPumpOn) {
    sumpPumpOnSinceMs = null;
    blockage.sump.lowFlowStartMs = null;
    if (blockage.sump.warned) {
      blockage.sump.warned = false;
      addEvent("info", "Blockage Warning Cleared", "Sump pump stopped — blockage watch reset.", "Sump Pump");
    }
  }
  if (borePumpOn && !prevBorePumpOn) {
    borePumpOnSinceMs = nowMs;
    blockage.bore.lowFlowStartMs = null;
    blockage.bore.clearCounterS  = 0;
  }
  if (!borePumpOn && prevBorePumpOn) {
    borePumpOnSinceMs = null;
    blockage.bore.lowFlowStartMs = null;
    if (blockage.bore.warned) {
      blockage.bore.warned = false;
      addEvent("info", "Blockage Warning Cleared", "Bore pump stopped — blockage watch reset.", "Bore Pump");
    }
  }
  prevSumpPumpOn = sumpPumpOn;
  prevBorePumpOn = borePumpOn;

  // ── Sump blockage check ──
  if (sumpPumpOn && sumpPumpOnSinceMs !== null) {
    const sinceStartup = nowMs - sumpPumpOnSinceMs;
    if (sinceStartup >= PUMP_STARTUP_GRACE_MS) {
      if (sumpFlow < settings.lowFlowThreshold) {
        if (blockage.sump.lowFlowStartMs === null) {
          blockage.sump.lowFlowStartMs = nowMs;
          blockage.sump.clearCounterS  = 0;
        }
        const lowFlowSec = (nowMs - blockage.sump.lowFlowStartMs) / 1000;
        if (lowFlowSec >= settings.blockageDelaySec && !blockage.sump.warned) {
          blockage.sump.warned = true;
          blockageIncidents++;
          addEvent("warn",
            "Possible Blockage / Low Flow — Sump",
            `Sump flow (${sumpFlow.toFixed(2)} L/min) stayed below ${settings.lowFlowThreshold} L/min for ${Math.round(lowFlowSec)} s. Nominal: ${settings.nominalFlow} L/min.`,
            "Sump Pump");
          beepAlarm();
        }
      } else {
        // Flow is back above threshold — hysteresis counter
        if (blockage.sump.warned) {
          blockage.sump.clearCounterS++;
          if (blockage.sump.clearCounterS >= BLOCKAGE_HYSTERESIS_S) {
            blockage.sump.warned = false;
            blockage.sump.clearCounterS = 0;
            addEvent("info", "Sump Flow Restored", `Sump flow returned to ${sumpFlow.toFixed(2)} L/min.`, "Sump Pump");
          }
        }
        blockage.sump.lowFlowStartMs = null;
      }
    }
  }

  // ── Bore blockage check ──
  if (borePumpOn && borePumpOnSinceMs !== null) {
    const sinceStartup = nowMs - borePumpOnSinceMs;
    if (sinceStartup >= PUMP_STARTUP_GRACE_MS) {
      if (boreFlow < settings.lowFlowThreshold) {
        if (blockage.bore.lowFlowStartMs === null) {
          blockage.bore.lowFlowStartMs = nowMs;
          blockage.bore.clearCounterS  = 0;
        }
        const lowFlowSec = (nowMs - blockage.bore.lowFlowStartMs) / 1000;
        if (lowFlowSec >= settings.blockageDelaySec && !blockage.bore.warned) {
          blockage.bore.warned = true;
          blockageIncidents++;
          addEvent("warn",
            "Possible Blockage / Low Flow — Bore",
            `Bore flow (${boreFlow.toFixed(2)} L/min) stayed below ${settings.lowFlowThreshold} L/min for ${Math.round(lowFlowSec)} s. Nominal: ${settings.nominalFlow} L/min.`,
            "Bore Pump");
          beepAlarm();
        }
      } else {
        if (blockage.bore.warned) {
          blockage.bore.clearCounterS++;
          if (blockage.bore.clearCounterS >= BLOCKAGE_HYSTERESIS_S) {
            blockage.bore.warned = false;
            blockage.bore.clearCounterS = 0;
            addEvent("info", "Bore Flow Restored", `Bore flow returned to ${boreFlow.toFixed(2)} L/min.`, "Bore Pump");
          }
        }
        blockage.bore.lowFlowStartMs = null;
      }
    }
  }
}

// ────────────────────────────────────────────────────────────
// Leak detection
// ────────────────────────────────────────────────────────────
function runLeakDiagnostic(data, nowMs, elapsedS) {
  const ohtLevel   = Number(data.ohtLevel   ?? -1);
  const sumpFlow   = Number(data.sumpFlowRate ?? 0);
  const boreFlow   = Number(data.boreFlowRate  ?? 0);
  const sumpPumpOn = !!(data.relays?.sumpPump);
  const borePumpOn = !!(data.relays?.borePump);
  const pumpRunning = sumpPumpOn || borePumpOn;

  // Only accumulate when a pump is running and sensors are valid
  if (pumpRunning && ohtLevel >= 0) {
    const activeFlow = sumpPumpOn ? sumpFlow : boreFlow;
    ohtLevelHistory.push({ ts: nowMs, level: ohtLevel, flow: activeFlow });
  }

  // Prune history older than LEAK_WINDOW_SEC
  const cutoff = nowMs - LEAK_WINDOW_SEC * 1000;
  ohtLevelHistory = ohtLevelHistory.filter((p) => p.ts >= cutoff);

  // Check every LEAK_WINDOW_SEC seconds
  if (lastLeakCheckTs && (nowMs - lastLeakCheckTs) < LEAK_WINDOW_SEC * 1000) return;
  lastLeakCheckTs = nowMs;

  if (ohtLevelHistory.length < 4) return;  // not enough data
  if (!pumpRunning) {
    // Pump stopped — reset window without raising/clearing
    ohtLevelHistory = [];
    return;
  }

  // OHT volume change from level readings
  const first = ohtLevelHistory[0];
  const last  = ohtLevelHistory[ohtLevelHistory.length - 1];
  const levelDeltaPct    = last.level - first.level;  // positive = rising
  const expectedVolDelta = (levelDeltaPct / 100) * settings.ohtCapacity;  // litres

  // Integrated inflow over the window
  const windowSec   = (last.ts - first.ts) / 1000;
  const avgFlow     = ohtLevelHistory.reduce((s, p) => s + p.flow, 0) / ohtLevelHistory.length;
  const integratedL = avgFlow * (windowSec / 60);

  // Discrepancy: if water is entering but tank level is not rising proportionally
  // Requires pump actively flowing (not dry-run / lockout state)
  if (avgFlow < settings.lowFlowThreshold) {
    // Flow too low to be meaningful for leak detection
    ohtLevelHistory = [];
    return;
  }

  const discrepancy = integratedL - Math.max(0, expectedVolDelta);
  const discrepancyFrac = discrepancy / Math.max(1, integratedL);

  const mismatch = discrepancyFrac > LEAK_TOLERANCE_FRAC;

  if (mismatch) {
    leakWindowsBad++;
    leakWindowsGood = 0;
    if (leakWindowsBad >= LEAK_WINDOWS_TO_WARN && !leakWarned) {
      leakWarned = true;
      leakAlerts++;
      addEvent("warn",
        "Possible Leak or Unmetered Water Use — OHT",
        `Over ${Math.round(windowSec)} s: measured inflow ~${integratedL.toFixed(1)} L but OHT level changed only ${levelDeltaPct.toFixed(1)}% (~${expectedVolDelta.toFixed(1)} L of ${settings.ohtCapacity} L). Discrepancy ~${discrepancy.toFixed(1)} L (${(discrepancyFrac*100).toFixed(0)}%). Without an outlet-flow sensor, normal consumption cannot be excluded.`,
        "OHT Sensor");
    }
  } else {
    leakWindowsGood++;
    leakWindowsBad = 0;
    if (leakWindowsGood >= LEAK_CLEAR_WINDOWS && leakWarned) {
      leakWarned = false;
      leakWindowsGood = 0;
      addEvent("info", "Leak Warning Cleared", "OHT level and inflow are now consistent.", "OHT Sensor");
    }
  }

  ohtLevelHistory = [];  // start fresh window
}

// ────────────────────────────────────────────────────────────
// Audible alarm (Web Audio API)
// ────────────────────────────────────────────────────────────
function beepAlarm() {
  if (!settings.audibleAlarm) return;
  try {
    const ctx = new (window.AudioContext || window.webkitAudioContext)();
    const osc = ctx.createOscillator();
    const gain = ctx.createGain();
    osc.connect(gain);
    gain.connect(ctx.destination);
    osc.frequency.value = 880;
    gain.gain.setValueAtTime(0.3, ctx.currentTime);
    gain.gain.exponentialRampToValueAtTime(0.001, ctx.currentTime + 0.6);
    osc.start();
    osc.stop(ctx.currentTime + 0.6);
  } catch (_) { /* unsupported */ }
}

// ────────────────────────────────────────────────────────────
// Session accumulation
// ────────────────────────────────────────────────────────────
let lastAccumTs = null;

function accumulateSession(data, nowMs) {
  if (!lastAccumTs) { lastAccumTs = nowMs; return; }
  const elapsedMin = (nowMs - lastAccumTs) / 60000;
  lastAccumTs = nowMs;

  const sumpFlow = Number(data.sumpFlowRate ?? 0);
  const boreFlow = Number(data.boreFlowRate  ?? 0);
  const sumpPumpOn = !!(data.relays?.sumpPump);
  const borePumpOn = !!(data.relays?.borePump);

  if (sumpPumpOn && sumpFlow > 0) {
    const delta = sumpFlow * elapsedMin;
    sessionPumpedL += delta;
    sessionSumpL   += delta;
    sessionSumpS   += (nowMs - (lastAccumTs - elapsedMin * 60000)) / 1000;
  }
  if (borePumpOn && boreFlow > 0) {
    const delta = boreFlow * elapsedMin;
    sessionPumpedL += delta;
    sessionBoreL   += delta;
    sessionBoreS   += (nowMs - (lastAccumTs - elapsedMin * 60000)) / 1000;
  }
  if (data.municipalFillingActive) {
    // No flow sensor on municipal line — estimate is not possible; leave as 0
  }
}

// ────────────────────────────────────────────────────────────
// Flow chart (canvas)
// ────────────────────────────────────────────────────────────
let flowChartCtx = null;

function initFlowChart() {
  const canvas = $("flowChart");
  if (!canvas) return;
  flowChartCtx = canvas.getContext("2d");
  canvas.width  = canvas.offsetWidth  || 600;
  canvas.height = canvas.offsetHeight || 200;
}

function pushFlowHistory(sumpFlow, boreFlow) {
  const label = new Date().toLocaleTimeString("en", { hour: "2-digit", minute: "2-digit", second: "2-digit" });
  flowHistory.sump.push(sumpFlow);
  flowHistory.bore.push(boreFlow);
  flowHistory.labels.push(label);
  if (flowHistory.sump.length > CHART_POINTS) {
    flowHistory.sump.shift();
    flowHistory.bore.shift();
    flowHistory.labels.shift();
  }
}

function drawFlowChart() {
  if (!flowChartCtx) return;
  const canvas = $("flowChart");
  const W = canvas.width = canvas.offsetWidth || 600;
  const H = canvas.height;
  const ctx = flowChartCtx;

  ctx.clearRect(0, 0, W, H);

  const data = flowHistory.sump;
  if (data.length < 2) {
    ctx.fillStyle = "#4a6070";
    ctx.font = "13px Inter, sans-serif";
    ctx.textAlign = "center";
    ctx.fillText("Waiting for flow data…", W / 2, H / 2);
    return;
  }

  const pad = { t: 16, r: 12, b: 28, l: 40 };
  const gW = W - pad.l - pad.r;
  const gH = H - pad.t - pad.b;

  const allVals = [...flowHistory.sump, ...flowHistory.bore];
  const maxY = Math.max(settings.nominalFlow * 1.2, ...allVals, 1);

  // Grid lines
  ctx.strokeStyle = "#1e2f40";
  ctx.lineWidth   = 1;
  for (let i = 0; i <= 4; i++) {
    const y = pad.t + (gH / 4) * i;
    ctx.beginPath();
    ctx.moveTo(pad.l, y);
    ctx.lineTo(pad.l + gW, y);
    ctx.stroke();
    const label = ((1 - i / 4) * maxY).toFixed(0);
    ctx.fillStyle = "#4a6070";
    ctx.font = "10px Inter, sans-serif";
    ctx.textAlign = "right";
    ctx.fillText(label, pad.l - 5, y + 4);
  }

  // Low-flow threshold line
  const threshY = pad.t + gH * (1 - settings.lowFlowThreshold / maxY);
  ctx.strokeStyle = "rgba(240,160,75,.5)";
  ctx.lineWidth = 1;
  ctx.setLineDash([4, 3]);
  ctx.beginPath();
  ctx.moveTo(pad.l, threshY);
  ctx.lineTo(pad.l + gW, threshY);
  ctx.stroke();
  ctx.setLineDash([]);
  ctx.fillStyle = "#f0a04b";
  ctx.font = "9px Inter, sans-serif";
  ctx.textAlign = "left";
  ctx.fillText(`${settings.lowFlowThreshold} L/min`, pad.l + 3, threshY - 3);

  function drawLine(vals, color) {
    if (vals.length < 2) return;
    ctx.beginPath();
    ctx.strokeStyle = color;
    ctx.lineWidth = 2;
    ctx.lineJoin = "round";
    vals.forEach((v, i) => {
      const x = pad.l + (i / (vals.length - 1)) * gW;
      const y = pad.t + gH * (1 - v / maxY);
      i === 0 ? ctx.moveTo(x, y) : ctx.lineTo(x, y);
    });
    ctx.stroke();
  }

  drawLine(flowHistory.sump, "#4ecdc4");
  drawLine(flowHistory.bore, "#4d8ef8");

  // X axis labels (first and last)
  if (flowHistory.labels.length >= 2) {
    ctx.fillStyle = "#4a6070";
    ctx.font = "9px Inter, sans-serif";
    ctx.textAlign = "left";
    ctx.fillText(flowHistory.labels[0], pad.l, H - 6);
    ctx.textAlign = "right";
    ctx.fillText(flowHistory.labels[flowHistory.labels.length - 1], pad.l + gW, H - 6);
  }
}

// ────────────────────────────────────────────────────────────
// Donut chart (canvas)
// ────────────────────────────────────────────────────────────
function drawDonut(sumpPct, borePct, muniPct) {
  const canvas = $("sourceDonut");
  if (!canvas) return;
  const ctx = canvas.getContext("2d");
  const W = 200, H = 200;
  canvas.width = W; canvas.height = H;
  ctx.clearRect(0, 0, W, H);

  const total = sumpPct + borePct + muniPct;
  if (total <= 0) {
    ctx.fillStyle = "#253545";
    ctx.beginPath();
    ctx.arc(W / 2, H / 2, 70, 0, Math.PI * 2);
    ctx.fill();
    ctx.fillStyle = "#4a6070";
    ctx.font = "12px Inter, sans-serif";
    ctx.textAlign = "center";
    ctx.fillText("No data", W / 2, H / 2 + 5);
    return;
  }

  const segments = [
    { pct: sumpPct / total, color: "#4d8ef8" },
    { pct: borePct / total, color: "#4ecdc4" },
    { pct: muniPct / total, color: "#9b8efb" },
  ];

  let start = -Math.PI / 2;
  const cx = W / 2, cy = H / 2, r = 75, innerR = 45;

  segments.forEach(({ pct, color }) => {
    if (pct <= 0) return;
    const angle = pct * Math.PI * 2;
    ctx.beginPath();
    ctx.moveTo(cx, cy);
    ctx.arc(cx, cy, r, start, start + angle);
    ctx.closePath();
    ctx.fillStyle = color;
    ctx.fill();
    start += angle;
  });

  // Punch inner hole
  ctx.beginPath();
  ctx.arc(cx, cy, innerR, 0, Math.PI * 2);
  ctx.fillStyle = "#1c2d3e";
  ctx.fill();

  // Center label
  const topSrc = sumpPct >= borePct && sumpPct >= muniPct ? "Sump" : (borePct >= muniPct ? "Bore" : "Muni");
  const topPct = Math.max(sumpPct, borePct, muniPct);
  ctx.fillStyle = "#e8f0f5";
  ctx.font = "bold 18px Inter, sans-serif";
  ctx.textAlign = "center";
  ctx.fillText(`${Math.round((topPct / total) * 100)}%`, cx, cy - 3);
  ctx.fillStyle = "#8ba8bb";
  ctx.font = "11px Inter, sans-serif";
  ctx.fillText(topSrc, cx, cy + 14);
}

// ────────────────────────────────────────────────────────────
// Warning banners
// ────────────────────────────────────────────────────────────
function renderWarningBanners() {
  const area = $("warningBanners");
  if (!area) return;
  area.innerHTML = "";

  const warnings = [];
  if (blockage.sump.warned) {
    warnings.push({
      level: "warn",
      title: "⚠ Possible Blockage / Low Flow — Sump Pump",
      detail: `Sump flow has been below ${settings.lowFlowThreshold} L/min while the sump pump is running. Check for pipe blockage, closed valve, or suction air lock.`,
    });
  }
  if (blockage.bore.warned) {
    warnings.push({
      level: "warn",
      title: "⚠ Possible Blockage / Low Flow — Bore Pump",
      detail: `Bore flow has been below ${settings.lowFlowThreshold} L/min while the bore pump is running. Check for pipe blockage or pump issue.`,
    });
  }
  if (leakWarned) {
    warnings.push({
      level: "warn",
      title: "⚠ Possible Leak or Unmetered Water Use — OHT",
      detail: `Measured inflow to OHT is significantly higher than the observed level rise over a ${LEAK_WINDOW_SEC} s window. Without an outlet-flow sensor, normal consumption cannot be excluded. Monitor the situation.`,
    });
  }

  if (warnings.length === 0) return;

  warnings.forEach(({ level, title, detail }) => {
    const div = document.createElement("div");
    div.className = `warning-banner${level === "error" ? " warning-banner--red" : ""}`;
    div.innerHTML = `
      <div class="warning-icon">${level === "error" ? "🔴" : "🟡"}</div>
      <div class="warning-body">
        <div class="warning-title">${title}</div>
        <div class="warning-detail">${detail}</div>
      </div>`;
    area.appendChild(div);
  });
}

// ────────────────────────────────────────────────────────────
// Event log renderer
// ────────────────────────────────────────────────────────────
function renderEventLog() {
  const list = $("recentEventsList");
  if (!list) return;

  if (eventLog.length === 0) {
    list.innerHTML = '<div class="event-empty">No events recorded yet.</div>';
    return;
  }

  // Show last 5 in the dashboard tab
  const preview = eventLog.slice(0, 5);
  list.innerHTML = preview.map((ev) => {
    const badgeClass = ev.type === "warn" ? "event-badge--warn" : ev.type === "error" ? "event-badge--error" : "event-badge--info";
    const badgeLabel = ev.type === "warn" ? "WARN" : ev.type === "error" ? "CRIT" : "INFO";
    const timeLabel  = timeStr(ev.ts);
    const equip      = ev.equipment ? ` · ${ev.equipment}` : "";
    return `
      <div class="event-item">
        <span class="event-badge ${badgeClass}">${badgeLabel}</span>
        <div class="event-body">
          <div class="event-title">${ev.title}</div>
          <div class="event-desc">${ev.desc}</div>
          <div class="event-meta">${timeLabel}${equip}</div>
        </div>
      </div>`;
  }).join("");
}

// ────────────────────────────────────────────────────────────
// Main snapshot applier — updates ALL elements from data
// ────────────────────────────────────────────────────────────
let prevData = null;

function applySnapshot(data) {
  if (!data) return;
  lastData = data;
  const nowMs = Date.now();

  // ── Accumulate session & run diagnostics ──
  accumulateSession(data, nowMs);
  runBlockageDiagnostic(data, nowMs);

  const sumpLevel = Number(data.sumpLevel  ?? -1);
  const ohtLevel  = Number(data.ohtLevel   ?? -1);
  const sumpValid = sumpLevel >= 0;
  const ohtValid  = ohtLevel  >= 0;
  const sumpFlow  = Number(data.sumpFlowRate ?? 0);
  const boreFlow  = Number(data.boreFlowRate  ?? 0);
  const source    = (data.currentSource || "NONE").toUpperCase();

  // Leak diagnostic (only when sensors are valid)
  if (sumpValid && ohtValid) runLeakDiagnostic(data, nowMs, 5);

  // Flow history for chart
  pushFlowHistory(sumpValid ? sumpFlow : 0, ohtValid ? boreFlow : 0);

  // ── Sensor health ──
  const [sumpSensorCls, sumpSensorLbl] = sensorHealthLabel(data.sumpLevel);
  const [ohtSensorCls,  ohtSensorLbl]  = sensorHealthLabel(data.ohtLevel);

  // ── Tank health badges ──
  function tankHealth(level, isSump) {
    if (!Number.isFinite(Number(level)) || Number(level) < 0) return ["error", "SENSOR FAULT"];
    const pct = Number(level);
    if (isSump) {
      if (pct < 15) return ["error", "CRITICAL"];
      if (pct < 40) return ["warn",  "LOW"];
      return ["", "HEALTHY"];
    } else {
      if (pct >= 95) return ["", "FULL"];
      if (pct > 60)  return ["", "OPTIMAL"];
      if (pct > 30)  return ["", "SUFFICIENT"];
      return ["warn", "LOW"];
    }
  }
  const [sumpBadgeCls, sumpBadgeLbl] = tankHealth(data.sumpLevel, true);
  const [ohtBadgeCls,  ohtBadgeLbl]  = tankHealth(data.ohtLevel,  false);

  // ── Tank fill visuals ──
  function applyFill(fillId, pct) {
    const el = $(fillId);
    if (!el) return;
    el.style.height = Number.isFinite(Number(pct)) && pct >= 0 ? `${Math.max(0, Math.min(100, Number(pct)))}%` : "0%";
  }
  applyFill("sumpFill",  sumpLevel);
  applyFill("ohtFill",   ohtLevel);
  applyFill("sumpFill2", sumpLevel);
  applyFill("ohtFill2",  ohtLevel);

  // ── Level text (all tabs) ──
  function levelText(val) {
    return Number.isFinite(Number(val)) && Number(val) >= 0 ? `${Number(val).toFixed(1)}%` : "—";
  }
  const sumpPct   = levelText(data.sumpLevel);
  const ohtPct    = levelText(data.ohtLevel);
  const sumpCap   = settings.sumpCapacity;
  const ohtCap    = settings.ohtCapacity;
  const sumpL     = sumpValid ? fmtLitres(sumpLevel, sumpCap) : "—";
  const ohtL      = ohtValid  ? fmtLitres(ohtLevel,  ohtCap)  : "—";

  setText("sumpLevel",      sumpPct);
  setText("ohtLevel",       ohtPct);
  setText("sumpLitres",     `${sumpL} / ${sumpCap} L`);
  setText("ohtLitres",      `${ohtL} / ${ohtCap} L`);
  setText("sumpLevelTanks", sumpPct);
  setText("ohtLevelTanks",  ohtPct);
  setText("sumpLitresTanks",`${sumpL} Litres Available`);
  setText("ohtLitresTanks", `${ohtL} Litres Capacity`);

  // ── Sensor health labels ──
  function applySensorHealth(id, cls, lbl) {
    const el = $(id);
    if (!el) return;
    el.textContent = lbl;
    el.className   = cls === "ok" ? "txt-green" : cls === "err" ? "txt-red" : "txt-orange";
  }
  applySensorHealth("sumpSensorHealth", sumpSensorCls, sumpSensorLbl);
  applySensorHealth("sumpSensorTanks",  sumpSensorCls, sumpSensorLbl);
  applySensorHealth("equipSumpSensor",  sumpSensorCls, sumpSensorLbl);
  applySensorHealth("safetySensorSump", sumpSensorCls, sumpSensorLbl);
  applySensorHealth("pipelineSumpSensor",sumpSensorCls,sumpSensorLbl);

  applySensorHealth("equipOhtSensor",   ohtSensorCls,  ohtSensorLbl);
  applySensorHealth("safetySensorOht",  ohtSensorCls,  ohtSensorLbl);
  applySensorHealth("pipelineOhtSensor",ohtSensorCls,  ohtSensorLbl);

  // ── Tank health badges ──
  function applyBadge(id, cls, lbl) {
    const el = $(id);
    if (!el) return;
    el.textContent = lbl;
    el.className   = "badge badge-health" + (cls ? " " + cls : "");
  }
  applyBadge("sumpHealthBadge",  sumpBadgeCls, sumpBadgeLbl);
  applyBadge("sumpHealthBadge2", sumpBadgeCls, sumpBadgeLbl);
  applyBadge("ohtHealthBadge",   ohtBadgeCls,  ohtBadgeLbl);
  applyBadge("ohtHealthBadge2",  ohtBadgeCls,  ohtBadgeLbl);

  // OHT demand badge (tanks tab)
  const ohtDemandActive = !!(data.ohtFillingActive);
  {
    const el = $("ohtDemandBadge");
    if (el) {
      el.textContent = ohtDemandActive ? "OHT Demand Active" : "OHT Demand Inactive";
      el.className = ohtDemandActive ? "badge badge-outline-orange" : "badge badge-outline";
    }
  }

  // OHT ETA estimation
  if (ohtValid && source !== "NONE") {
    const activeFlow = (source === "SUMP") ? sumpFlow : boreFlow;
    if (activeFlow > 0.1) {
      const remaining = Math.max(0, 100 - ohtLevel) / 100 * ohtCap;
      const etaMin = remaining / activeFlow;
      setText("ohtEta", etaMin > 60 ? `~${(etaMin/60).toFixed(1)} hrs` : `~${Math.round(etaMin)} mins to 100% full`);
    } else {
      setText("ohtEta", "Pump not flowing");
    }
  } else {
    setText("ohtEta", "—");
  }

  // ── System Overview ──
  setText("overviewSource",     source === "NONE" ? "NONE" : source);
  const activeFlow = source === "SUMP" ? sumpFlow : (source === "BORE" ? boreFlow : 0);
  setText("overviewFlowVal",   activeFlow > 0 ? `${activeFlow.toFixed(1)} L/min` : "—");
  setText("overviewFlowStatus",activeFlow > 0 ? "Status: FLOWING" : "Status: IDLE");
  setText("overviewTotalPumped",sessionPumpedL > 0 ? `${sessionPumpedL.toFixed(1)} L` : "—");

  // Pipeline condition
  const pipelineOk = !blockage.sump.warned && !blockage.bore.warned;
  setText("overviewPipeline",     pipelineOk ? "NORMAL" : "WARNING");
  setText("overviewPipelineHint", pipelineOk ? "Head Pressure: Normal" : "Check flow sensors");

  // ── Source overview ──
  setText("overviewSource",    source);
  setText("activeSource",      source);
  setText("ohtDemand",         ohtDemandActive ? "YES" : "NO");
  {
    const el = $("ohtDemand");
    if (el) el.className = ohtDemandActive ? "txt-green" : "txt-muted";
  }
  setText("ohtDemandText", ohtDemandActive ? "YES (Filling required)" : "NO");
  {
    const el = $("ohtDemandText");
    if (el) el.className = ohtDemandActive ? "txt-green" : "txt-muted";
  }

  // Source tabs indicator
  {
    const sumpTab = $("srcSumpTab");
    const boreTab = $("srcBoreTab");
    if (sumpTab && boreTab) {
      sumpTab.className = source === "SUMP" ? "source-tab source-tab--active" : "source-tab";
      boreTab.className = source === "BORE" ? "source-tab source-tab--active" : "source-tab";
    }
  }
  setText("preferredSource", source !== "NONE" ? source : "SUMP");

  // ── Relay/pump states ──
  function relayState(id, val) {
    const el = $(id);
    if (!el) return;
    const on = Boolean(val);
    el.textContent = on ? "ON" : "OFF";
    el.className   = "equip-state" + (id.includes("pipeline") ? " equip-state--lg" : "") + (on ? " on" : " off");
  }
  relayState("equipSumpPump",     data.relays?.sumpPump);
  relayState("equipBorePump",     data.relays?.borePump);
  relayState("equipMunicipalValve",data.relays?.municipalValve);
  relayState("pipelineSumpPump",  data.relays?.sumpPump);
  relayState("pipelineBorePump",  data.relays?.borePump);
  relayState("pipelineMunicipalValve",data.relays?.municipalValve);
  relayState("pipelineRelayIn4",  data.relays?.in4);

  // ── Lockouts ──
  function lockoutLabel(id, val) {
    const el = $(id);
    if (!el) return;
    const locked = Boolean(val);
    el.textContent = locked ? "Locked out" : "Normal";
    el.className   = locked ? "txt-orange" : "txt-green";
  }
  lockoutLabel("equipSumpLockout",  data.sumpLockedOut);
  lockoutLabel("equipBoreLockout",  data.boreLockedOut);
  lockoutLabel("safetyLockoutSump", data.sumpLockedOut);
  lockoutLabel("safetyLockoutBore", data.boreLockedOut);

  // ── Municipal / OHT fill states ──
  function fillLabel(id, val) {
    const el = $(id);
    if (!el) return;
    const active = Boolean(val);
    el.textContent = active ? "Active" : "Inactive";
    el.className   = active ? "txt-teal" : "txt-muted";
  }
  fillLabel("safetyMunicipal",  data.municipalFillingActive);
  fillLabel("safetyOhtFilling", data.ohtFillingActive);

  // ── Flow sensor health ──
  const flowSensorOk = !blockage.sump.warned && !blockage.bore.warned;
  const flowSensorEl = $("equipFlowSensor");
  if (flowSensorEl) {
    flowSensorEl.textContent = flowSensorOk ? "Normal" : "Warning";
    flowSensorEl.className   = flowSensorOk ? "txt-green" : "txt-orange";
  }
  const pfEl = $("pipelineFlowSensor");
  if (pfEl) {
    pfEl.textContent = flowSensorOk ? "NORMAL" : "WARNING";
    pfEl.className   = "equip-state equip-state--lg" + (flowSensorOk ? " ok" : " warn");
  }

  // ── Blockage protection status ──
  const blockageEl = $("equipBlockage");
  if (blockageEl) {
    blockageEl.textContent = pipelineOk ? "Normal" : "Warning";
    blockageEl.className   = pipelineOk ? "txt-green" : "txt-orange";
  }
  const psEl = $("pipelineStatus");
  if (psEl) {
    psEl.textContent = pipelineOk ? "NORMAL" : "WARNING";
    psEl.className   = "equip-state equip-state--lg" + (pipelineOk ? " ok" : " warn");
  }

  // ── Flow readings in pipeline tab ──
  setText("pipelineSumpFlow", `${sumpFlow.toFixed(2)} L/min`);
  setText("pipelineBoreFlow", `${boreFlow.toFixed(2)} L/min`);

  // ── Analytics ──
  setText("analyticsTotalPumped",  sessionPumpedL > 0 ? `${sessionPumpedL.toFixed(1)} L` : "—");
  setText("analyticsAvgDay",       "Session total");
  setText("analyticsSource",       source);
  setText("analyticsSourceHint",   source !== "NONE" ? `Flow: ${activeFlow.toFixed(1)} L/min` : "No active source");
  setText("analyticsBlockageCount",String(blockageIncidents));
  setText("analyticsBlockageHint", blockageIncidents > 0 ? "Check event log" : "No incidents");
  setText("analyticsLeakCount",    String(leakAlerts));
  setText("analyticsLeakHint",     leakAlerts > 0 ? "Check event log" : "—");

  // Source donut (session)
  const totalL = sessionSumpL + sessionBoreL + sessionMuniL;
  if (totalL > 0) {
    const sp = Math.round((sessionSumpL / totalL) * 100);
    const bp = Math.round((sessionBoreL / totalL) * 100);
    const mp = Math.round((sessionMuniL / totalL) * 100);
    setText("legSump", String(sp));
    setText("legBore", String(bp));
    setText("legMuni", String(mp));
    drawDonut(sessionSumpL, sessionBoreL, sessionMuniL);
  } else {
    drawDonut(source === "SUMP" ? 1 : 0, source === "BORE" ? 1 : 0, 0);
    setText("legSump", source === "SUMP" ? "100" : "0");
    setText("legBore", source === "BORE" ? "100" : "0");
    setText("legMuni", "0");
  }

  // ── Wi-Fi status (inferred from data freshness) ──
  const lastTs = data.updatedAt ? Number(data.updatedAt) : null;
  const dataAge = lastTs ? (nowMs - lastTs) : null;
  const wifiOk  = dataAge !== null && dataAge < 30000;  // 30 s stale threshold
  {
    const el = $("wifiConnStatus");
    if (el) {
      el.textContent = wifiOk ? "Connected" : (dataAge ? "Stale / Possibly offline" : "—");
      el.className   = wifiOk ? "txt-green" : "txt-orange";
    }
    setText("wifiLastConn", lastTs ? timeStr(lastTs) : "—");
    setText("wifiStatusBadge", wifiOk ? "Connected via Firebase" : "Firebase (stale)");
  }

  // ── Last updated footer ──
  const updStr = lastTs ? `Updated ${timeStr(lastTs)}${data._isDemo ? " · DEMO" : ""}` : "Waiting for data…";
  setText("lastUpdatedFooter", updStr);
  setText("lastCommText",      `Autonomous ESP32 supervisory node · Last communication: ${timeStr(lastTs)}`);

  // ── ESP32 badge ──
  const badge = $("esp32Badge");
  if (badge) {
    if (data._isDemo) {
      badge.textContent = "DEMO";
      badge.className   = "badge badge-esp32 error";
    } else if (wifiOk) {
      badge.textContent = "ESP32 Online";
      badge.className   = "badge badge-esp32 live";
    } else {
      badge.textContent = "ESP32 Offline";
      badge.className   = "badge badge-esp32 error";
    }
  }

  // ── Warnings ──
  renderWarningBanners();

  // ── Charts ──
  drawFlowChart();
}

// ────────────────────────────────────────────────────────────
// Firebase listener — unchanged from original pattern
// ────────────────────────────────────────────────────────────
onValue(
  telemetryRef,
  (snapshot) => {
    if (isDemoMode) return;   // demo mode overrides

    const badge = $("esp32Badge");
    const data  = snapshot.val();

    if (!data) {
      if (badge) {
        badge.textContent = "Connected · waiting for ESP32";
        badge.className   = "badge badge-esp32";
      }
      return;
    }

    lastFirebaseUpdate = Date.now();
    applySnapshot(data);
  },
  (error) => {
    console.error("Firebase read failed:", error);
    const badge = $("esp32Badge");
    if (badge) {
      badge.textContent = "Firebase error";
      badge.className   = "badge badge-esp32 error";
    }
  }
);

// ────────────────────────────────────────────────────────────
// Stale-data monitor (checks every 15 s whether Firebase is silent)
// ────────────────────────────────────────────────────────────
setInterval(() => {
  if (isDemoMode || !lastData) return;
  const age = lastFirebaseUpdate ? (Date.now() - lastFirebaseUpdate) : null;
  const badge = $("esp32Badge");
  if (!badge) return;
  if (age && age > 30000) {
    badge.textContent = "ESP32 Offline";
    badge.className   = "badge badge-esp32 error";
  }
}, 15000);

// ────────────────────────────────────────────────────────────
// Init
// ────────────────────────────────────────────────────────────
function init() {
  loadSettings();
  syncSettingsToUI();
  initFlowChart();

  // Switch to demo mode if stored setting is on
  if (settings.demoMode) applyDemoMode(true);

  // Initial event
  addEvent("info", "Dashboard Started", "LIQORA monitoring dashboard loaded. Listening to Firebase at liquora/telemetry.", "System");
}

init();
