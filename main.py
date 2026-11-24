from ursina import *
from ursina.color import Color
from PIL import Image, ImageDraw
from panda3d.core import Filename, AudioSound
import builtins
import math
import os
import random
from panda3d.core import ColorScaleAttrib
import sys
import tempfile
import wave
from array import array

P, RW, N = 64, 18, 16
WORLD = P * N
ROAD_C = RW / 2
LANE = 4.5
S_BLOCK = P - RW
DIR_H = [90, 0, 270, 180]
DIR_X = [1, 0, -1, 0]
DIR_Z = [0, 1, 0, -1]
TAU = math.tau

TINTS = [
    [(196, 218, 238), (176, 204, 220), (205, 210, 220), (166, 196, 206)],
    [(255, 255, 255), (255, 242, 228), (244, 230, 220), (255, 248, 238)],
    [(255, 252, 246), (236, 236, 236), (255, 242, 220), (228, 236, 246)],
]
CAR_COLORS = [(200, 40, 40), (40, 90, 200), (235, 205, 50), (60, 160, 80), (230, 130, 40),
              (120, 60, 160), (215, 215, 215), (38, 38, 44), (150, 150, 158), (20, 110, 120)]
CAR_BODIES = ["sedan", "hatch", "suv", "pickup", "van", "sedan", "hatch", "suv"]
SKINS = [(236, 190, 150), (214, 160, 120), (180, 128, 92), (130, 88, 62), (250, 214, 184)]
HAIRS = [(42, 30, 24), (90, 60, 35), (20, 20, 20), (190, 160, 90), (150, 60, 40), (200, 200, 200)]
SHIRTS = [(230, 90, 90), (90, 170, 230), (240, 220, 90), (120, 220, 130), (220, 140, 220),
          (240, 160, 80), (240, 240, 240), (60, 60, 70), (90, 200, 190)]
PANTS = [(40, 50, 90), (60, 60, 60), (90, 70, 50), (30, 30, 30), (70, 90, 130), (120, 110, 90)]
SHOES = [(30, 30, 34), (235, 235, 235), (90, 60, 40), (180, 40, 40)]

is_night = False
night_blend = 0.0
day_night_btn = None
day_night_label = None
street_lamps = []
sky_ent = None


helis = []
heli_timer = 0.0
class WantedSystem:
    STATES = ("none", "searching", "spotted", "lost_contact", "nearby_unseen")
    EVIDENCE_TYPES = ("face", "clothes", "car", "weapon", "camera", "duo")

    def __init__(self):
        self.level = 0
        self.state = "none"
        self.evidence = set()
        self.alert_center = [0, 0]
        self.alert_radius = 0.0
        self.hot_timer = 0.0
        self.last_seen_pos = [0, 0]
        self.pending = 0
        self.search_timer = 0.0

    def commit_crime(self, x, z, crime_type, evidence_types=None):
        levels = {"shooting": 1, "air_shot": 1, "car_shot": 1, "carjack": 2,
                  "cop_car_steal": 2, "kill_ped": 2, "kill_cop": 3, "explosion": 3}
        lvl = levels.get(crime_type, 1)
        report_crime(x, z, max(lvl, player.stars), evidence_types)

    def update_state(self, dt):
        self.level = player.stars
        if self.level == 0:
            if self.hot_timer > 0:
                self.hot_timer -= dt
                self.state = "nearby_unseen"
            else:
                self.state = "none"
                self.evidence.clear()
                self.alert_radius = 0.0
            return

        dist_to_alert = math.hypot(player.x - self.alert_center[0], player.z - self.alert_center[1])
        player_in_zone = dist_to_alert < self.alert_radius

        seen = False
        knows = police_knows_player()
        for cp in cops:
            d = math.hypot(cp.x - player.x, cp.z - player.z)
            if d < 60 and knows and clear_line(cp.x, cp.z, player.x, player.z):
                seen = True
                break
        if not seen:
            for c in cars:
                if c.kind == "police" and c.driver == "cop":
                    d = math.hypot(c.x - player.x, c.z - player.z)
                    if d < 85 and knows and clear_line(c.x, c.z, player.x, player.z):
                        seen = True
                        break
        if not seen:
            for h in helis:
                if h.hp > 0 and math.hypot(h.x - player.x, h.z - player.z) < 110:
                    seen = True
                    break

        if seen:
            self.state = "spotted"
            self.last_seen_pos = [player.x, player.z]
            self.alert_center = [player.x, player.z]
            self.search_timer = 0.0
            player.crime_t = 0.0
        elif self.state == "spotted":
            self.state = "lost_contact"
            self.search_timer = 15.0 + self.level * 5.0

        if self.state == "lost_contact":
            self.search_timer -= dt
            if self.search_timer <= 0:
                if player_in_zone:
                    self.state = "nearby_unseen"
                    self.search_timer = 10.0
                else:
                    self.drop_level()

        if self.state == "nearby_unseen":
            self.search_timer -= dt
            if not player_in_zone or self.search_timer <= 0:
                self.drop_level()

        if self.level >= 6:
            self.state = "spotted" if seen else "lost_contact"
            self.search_timer = 999.0

    def drop_level(self):
        self.level = max(0, self.level - 1)
        if self.level == 0:
            self.hot_timer = 30.0
            self.state = "nearby_unseen"
            self.alert_radius = 0.0
        else:
            self.state = "lost_contact"
            self.search_timer = 15.0
            self.alert_radius = max(80, self.alert_radius - 40)

    def change_clothes(self):
        self.evidence.discard("clothes")
        self.evidence.discard("face")

    def change_car(self):
        self.evidence.discard("car")

def drop_level(self):
    self.level = max(0, self.level - 1)
    if self.level == 0:
        self.hot_timer = 30.0
        self.state = "nearby_unseen"
        self.alert_radius = 0.0
    else:
        self.state = "lost_contact"
        self.search_timer = 15.0
        self.alert_radius = max(80, self.alert_radius - 40)


def apply_crime(self, x, z, level, evidence_types=None):
        if evidence_types is None:
            evidence_types = ["face", "clothes"]
        self.alert_center = [x, z]
        self.alert_radius = max(self.alert_radius, 140.0 + level * 60)
        for ev in evidence_types:
            self.evidence.add(ev)
        self.level = min(6, max(self.level, level))
        player.stars = max(player.stars, self.level)
        player.crime_t = 0.0
        self.state = "spotted"
        self.last_seen_pos = [player.x, player.z]
        self.search_timer = 0.0
        self.hot_timer = 30.0
        self.pending = 0

def change_clothes(self):
    self.evidence.discard("clothes")
    self.evidence.discard("face")






wanted = WantedSystem()

EVIDENCE_COLORS = {
    "face": (200, 170, 120),
    "clothes": (90, 140, 200),
    "car": (200, 60, 60),
    "weapon": (180, 180, 60),
    "camera": (100, 200, 100),
    "duo": (200, 100, 200),
}
hud_evidence = []

def spawn_heli():
    angle = random.uniform(0, TAU)
    dist = random.uniform(150, 250)
    x = cl(player.x + math.cos(angle) * dist, 50, WORLD - 50)
    z = cl(player.z + math.sin(angle) * dist, 50, WORLD - 50)
    h = Heli()
    h.activate(x, z)
    helis.append(h)

def release_heli(h):
    if h in helis:
        helis.remove(h)
    h.active = False
    h.root.enabled = False

def cl(v, a, b):
    return max(a, min(b, v))


def rgb(r, g, b, a=255):
    return Color(r / 255, g / 255, b / 255, a / 255)


def tc(col, k=1.0):
    return Color(min(1.0, col[0] * k / 255), min(1.0, col[1] * k / 255), min(1.0, col[2] * k / 255), 1)


def adiff(a, b):
    return (a - b + 180) % 360 - 180


def shade(c, k):
    return tuple(cl(int(v * k), 0, 255) for v in c)


SR = 22050


def noise(n, rng):
    return [rng.uniform(-1.0, 1.0) for _ in range(n)]


def lowpass(s, a):
    y = 0.0
    out = []
    for x in s:
        y += a * (x - y)
        out.append(y)
    return out


def highpass(s, a):
    lo = lowpass(s, a)
    return [x - l for x, l in zip(s, lo)]


def normalize(s, peak):
    m = max(1e-9, max(abs(x) for x in s))
    k = peak / m
    return [x * k for x in s]


def loopify(s, fade):
    n = len(s) - fade
    out = s[:n]
    for i in range(fade):
        k = i / fade
        out[i] = out[i] * k + s[n + i] * (1 - k)
    return out


def save_wav(path, s):
    data = array("h", [int(max(-1.0, min(1.0, x)) * 32000) for x in s])
    if sys.byteorder == "big":
        data.byteswap()
    with wave.open(path, "wb") as w:
        w.setnchannels(1)
        w.setsampwidth(2)
        w.setframerate(SR)
        w.writeframes(data.tobytes())


def gen_engine():
    rng = random.Random(1)
    fade = 800
    n = SR + fade
    sig = []
    for i in range(n):
        t = i / SR
        ph = 46.0 * t
        s = (0.45 * math.sin(TAU * ph) + 0.32 * math.sin(2 * TAU * ph) + 0.22 * math.sin(3 * TAU * ph)
             + 0.12 * math.sin(5 * TAU * ph))
        s *= 0.82 + 0.18 * math.sin(TAU * 9 * t)
        sig.append(s)
    nz = lowpass(noise(n, rng), 0.1)
    sig = [a + 0.35 * b for a, b in zip(sig, nz)]
    return loopify(normalize(sig, 0.7), fade)


def gen_gun():
    rng = random.Random(2)
    n = int(SR * 0.4)
    nz = noise(n, rng)
    out = []
    for i in range(n):
        t = i / SR
        out.append(nz[i] * math.exp(-t * 28) * 0.9 + math.sin(TAU * 95 * t) * math.exp(-t * 16) * 0.8
                   + math.sin(TAU * 1700 * t) * math.exp(-t * 90) * 0.25)
    return normalize(out, 0.95)












def gen_step():
    rng = random.Random(6)
    n = int(SR * 0.14)
    nz = lowpass(noise(n, rng), 0.25)
    return normalize([nz[i] * math.exp(-(i / SR) * 35) for i in range(n)], 0.7)


























GENS = {"engine": gen_engine, "gun": gen_gun, "step": gen_step}
SFX_DIR = os.path.join(tempfile.gettempdir(), "gta3d_sfx_v1")


def ensure_sounds(folder):
    os.makedirs(folder, exist_ok=True)
    marker = os.path.join(folder, "ready")
    if os.path.exists(marker):
        return
    print("Генерирую звуки (только при первом запуске)...")
    for name, fn in GENS.items():
        save_wav(os.path.join(folder, name + ".wav"), fn())
    open(marker, "w").close()


class Sound:
    def __init__(self):
        self.ok = False
        self.pools = {}
        self.idx = {}
        self.slots = {}
        try:
            ensure_sounds(SFX_DIR)
            self.ok = True
        except Exception:
            self.ok = False

    def load(self, name):
        return builtins.base.loader.loadSfx(Filename.fromOsSpecific(os.path.join(SFX_DIR, name + ".wav")))

    def preload(self):
        if not self.ok:
            return
        try:
            for name in GENS:
                if name == "engine":
                    continue
                self.pools[name] = [self.load(name) for _ in range(5 if name == "gun" else 3)]
                self.idx[name] = 0
        except Exception:
            self.ok = False

    def play(self, name, vol=1.0, rate=1.0, pan=0.0):
        if not self.ok or vol < 0.02:
            return
        try:
            pool = self.pools[name]
            i = self.idx[name]
            self.idx[name] = (i + 1) % len(pool)
            s = pool[i]
            s.setVolume(min(1.0, vol))
            s.setPlayRate(rate)
            s.setBalance(pan)
            s.play()
        except Exception:
            self.ok = False

    def at(self, name, x, z, vol=1.0, rate=1.0, rng=110.0):
        dx, dz = x - cam_pos[0], z - cam_pos[2]
        d = math.hypot(dx, dz)
        if d > rng:
            return
        att = (1 - d / rng) ** 1.5
        sy, cy = math.sin(math.radians(cam_yaw)), math.cos(math.radians(cam_yaw))
        pan = cl((dx * cy - dz * sy) / max(d, 6.0), -1, 1) * 0.85
        self.play(name, vol * att, rate, pan)

    def loop(self, slot, name, vol, rate=1.0, pan=0.0):
        if not self.ok:
            return
        try:
            s = self.slots.get(slot)
            if s is None:
                s = self.load(name)
                s.setLoop(True)
                self.slots[slot] = s
            if vol < 0.015:
                if s.status() == AudioSound.PLAYING:
                    s.stop()
                return
            s.setVolume(min(1.0, vol))
            s.setPlayRate(rate)
            s.setBalance(pan)
            if s.status() != AudioSound.PLAYING:
                s.play()
        except Exception:
            self.ok = False

    def loop_at(self, slot, name, x, z, vol, rate=1.0, rng=110.0):
        dx, dz = x - cam_pos[0], z - cam_pos[2]
        d = math.hypot(dx, dz)
        if d > rng:
            self.loop(slot, name, 0)
            return
        att = (1 - d / rng) ** 1.5
        sy, cy = math.sin(math.radians(cam_yaw)), math.cos(math.radians(cam_yaw))
        pan = cl((dx * cy - dz * sy) / max(d, 6.0), -1, 1) * 0.85
        self.loop(slot, name, vol * att, rate, pan)


app = Ursina(title="GRAND THEFT PYTHON 3D", borderless=False)
window.exit_button.visible = False
window.fps_counter.enabled = True
mouse_look = True
mouse.visible = False
mouse.locked = True
camera.fov = 85
camera.clip_plane_near = 0.3
cam_pos = [0.0, 1.7, 0.0]
cam_yaw, cam_pitch, cam_free, cam_idle = 0.0, 14.0, 0.0, 0.0

try:
    Sky()
except Exception:
    pass
try:
    scene.fog_color = Color(0.72, 0.8, 0.9, 1)
    scene.fog_density = (90, 340)
except Exception:
    pass

snd = Sound()
snd.preload()


class MB:
    def __init__(self):
        self.v, self.c, self.uv, self.t = [], [], [], []

    def quad(self, p0, p1, p2, p3, c0, c1, c2, c3, uv=None):
        n = len(self.v)
        self.v += [p0, p1, p2, p3]
        self.c += [c0, c1, c2, c3]
        self.uv += uv if uv else [Vec2(0, 0)] * 4
        self.t.append((n, n + 1, n + 2))
        self.t.append((n, n + 2, n + 3))

    def mesh(self):
        return Mesh(vertices=self.v, triangles=self.t, colors=self.c, uvs=self.uv, static=True)


SK = {"z+": 0.95, "x+": 0.82, "z-": 0.62, "x-": 0.7, "top": 1.1}


def wall(mb, ax, az, bx, bz, y0, y1, col, k, nu, ny, textured, ao):
    if ao > 0 and y1 - y0 > 8:
        segs = [(y0, y0 + 8, 1 - ao, 1.0), (y0 + 8, y1, 1.0, 1.0)]
    else:
        segs = [(y0, y1, 1 - ao, 1.0)]
    for ya, yb, ka, kb in segs:
        ca, cb = tc(col, k * ka), tc(col, k * kb)
        va, vb = (ya - y0) / (y1 - y0) * ny, (yb - y0) / (y1 - y0) * ny
        uv = [Vec2(0, va), Vec2(nu, va), Vec2(nu, vb), Vec2(0, vb)] if textured else None
        mb.quad(Vec3(ax, ya, az), Vec3(bx, ya, bz), Vec3(bx, yb, bz), Vec3(ax, yb, az), ca, ca, cb, cb, uv)


def box(mb, cx, cy, cz, sx, sy, sz, col, sides=True, top=True, tex=False, ao=0.0, bright=1.0):
    xa, xb, ya, yb, za, zb = cx - sx / 2, cx + sx / 2, cy - sy / 2, cy + sy / 2, cz - sz / 2, cz + sz / 2
    if sides:
        nx_, nz_, ny_ = max(1, round(sx / 16)), max(1, round(sz / 16)), max(1, round(sy / 14))
        wall(mb, xa, zb, xb, zb, ya, yb, col, SK["z+"] * bright, nx_, ny_, tex, ao)
        wall(mb, xb, za, xa, za, ya, yb, col, SK["z-"] * bright, nx_, ny_, tex, ao)
        wall(mb, xb, zb, xb, za, ya, yb, col, SK["x+"] * bright, nz_, ny_, tex, ao)
        wall(mb, xa, za, xa, zb, ya, yb, col, SK["x-"] * bright, nz_, ny_, tex, ao)
    if top:
        c = tc(col, SK["top"] * bright)
        mb.quad(Vec3(xa, yb, za), Vec3(xb, yb, za), Vec3(xb, yb, zb), Vec3(xa, yb, zb), c, c, c, c)


def flat(mb, xa, za, xb, zb, y, col):
    c = tc(col)
    mb.quad(Vec3(xa, y, za), Vec3(xb, y, za), Vec3(xb, y, zb), Vec3(xa, y, zb), c, c, c, c)


def tex_from(im):
    t = Texture(im)
    try:
        t.filtering = "mipmap"
    except Exception:
        pass
    return t


def make_glass():
    S = 256
    im = Image.new("RGB", (S, S), (60, 75, 95))
    d = ImageDraw.Draw(im)
    rng = random.Random(21)
    for gx in range(8):
        for gy in range(8):
            x0, y0 = gx * 32, gy * 32
            base = rng.randint(-14, 14)
            for yy in range(y0 + 2, y0 + 30):
                t = (yy - y0) / 32
                d.line((x0 + 2, yy, x0 + 29, yy), fill=(int(96 + base - 35 * t), int(142 + base - 30 * t), int(188 + base - 24 * t)))
            if rng.random() < 0.1:
                d.rectangle((x0 + 2, y0 + 2, x0 + 29, y0 + 29), fill=(250, 232, 170))
            d.polygon([(x0 + 3, y0 + 3), (x0 + 14, y0 + 3), (x0 + 3, y0 + 16)], fill=(175, 205, 230))
    for k in range(9):
        d.line((k * 32, 0, k * 32, S), fill=(44, 52, 64), width=2)
        d.line((0, k * 32, S, k * 32), fill=(44, 52, 64), width=2)
    return tex_from(im)


def make_brick():
    S = 256
    im = Image.new("RGB", (S, S), (205, 195, 180))
    d = ImageDraw.Draw(im)
    rng = random.Random(22)
    for row in range(32):
        y = row * 8
        off = 0 if row % 2 == 0 else 8
        for bx in range(-1, 17):
            x = bx * 16 + off
            v = rng.randint(-14, 14)
            d.rectangle((x + 1, y + 1, x + 15, y + 7), fill=(176 + v, 92 + v // 2, 74 + v // 2))
    for gx in range(4):
        for gy in range(4):
            x0, y0 = gx * 64 + 14, gy * 64 + 10
            x1, y1 = x0 + 36, y0 + 36
            lit = rng.random() < 0.14
            d.rectangle((x0 - 3, y0 - 3, x1 + 3, y1 + 3), fill=(238, 236, 230))
            for yy in range(y0, y1):
                t = (yy - y0) / 36
                d.line((x0, yy, x1, yy), fill=(255, 228, 150) if lit else (int(84 - 28 * t), int(112 - 32 * t), int(146 - 36 * t)))
            d.line(((x0 + x1) // 2, y0, (x0 + x1) // 2, y1), fill=(238, 236, 230), width=2)
            d.rectangle((x0 - 8, y1 + 4, x1 + 8, y1 + 9), fill=(112, 108, 104))
            for k in range(5):
                xx = x0 - 6 + k * 11
                d.line((xx, y1 + 9, xx, y1 + 18), fill=(70, 70, 74), width=1)
            d.line((x0 - 8, y1 + 18, x1 + 8, y1 + 18), fill=(70, 70, 74), width=2)
    return tex_from(im)


def make_concrete():
    S = 256
    im = Image.new("RGB", (S, S), (208, 208, 204))
    d = ImageDraw.Draw(im)
    rng = random.Random(23)
    for gy in range(4):
        y0 = gy * 64
        for yy in range(y0 + 14, y0 + 46):
            t = (yy - y0 - 14) / 32
            d.line((0, yy, S, yy), fill=(int(78 - 26 * t), int(104 - 30 * t), int(138 - 34 * t)))
        for gx in range(8):
            x0 = gx * 32
            if rng.random() < 0.16:
                d.rectangle((x0 + 2, y0 + 16, x0 + 30, y0 + 44), fill=(255, 228, 150))
            d.line((x0, y0 + 14, x0, y0 + 46), fill=(220, 220, 216), width=3)
        d.rectangle((0, y0 + 10, S, y0 + 14), fill=(176, 176, 172))
        d.rectangle((0, y0 + 46, S, y0 + 50), fill=(176, 176, 172))
        d.line((0, y0 + 2, S, y0 + 2), fill=(190, 190, 186), width=2)
    for k in range(0, S, 64):
        d.line((k, 0, k, S), fill=(190, 190, 186), width=1)
    return tex_from(im)


def make_asphalt():
    S = 128
    im = Image.new("RGB", (S, S), (50, 52, 56))
    px = im.load()
    rng = random.Random(24)
    for x in range(S):
        for y in range(S):
            v = rng.randint(-8, 8)
            px[x, y] = (50 + v, 52 + v, 56 + v)
    d = ImageDraw.Draw(im)
    for _ in range(5):
        x, y = rng.randint(0, S), rng.randint(0, S)
        d.line((x, y, x + rng.randint(-30, 30), y + rng.randint(-30, 30)), fill=(36, 37, 40), width=1)
    return Texture(im)


blocks = {}
parks = set()
block_rects_for_map = []
chunk_meshes = {}
CH = 2


def mb_for(x, z, kind):
    key = (int(x // (P * CH)), int(z // (P * CH)), kind)
    m = chunk_meshes.get(key)
    if m is None:
        m = chunk_meshes[key] = MB()
    return m


Entity(model="plane", scale=(WORLD + 3000, 1, WORLD + 3000), position=(WORLD / 2, -0.1, WORLD / 2),
       color=rgb(86, 132, 80))
Entity(model="plane", scale=(WORLD, 1, WORLD), position=(WORLD / 2, 0, WORLD / 2), color=rgb(255, 255, 255),
       texture=make_asphalt(), texture_scale=(WORLD / 5, WORLD / 5))

Y_MARK = 0.07
YEL, WHT = (232, 202, 70), (225, 225, 225)

for k in range(N):
    rc = k * P + ROAD_C
    for i in range(N):
        s0 = i * P + RW + 4.5
        s1 = (i + 1) * P - 4.5 if i < N - 1 else WORLD - 0.5
        mid = (s0 + s1) / 2
        gx = mb_for(mid, rc, "g")
        gz = mb_for(rc, mid, "g")
        for off in (-0.18, 0.18):
            flat(gx, s0, rc + off - 0.1, s1, rc + off + 0.1, Y_MARK, YEL)
            flat(gz, rc + off - 0.1, s0, rc + off + 0.1, s1, Y_MARK, YEL)
        for off in (0.7, RW - 0.7):
            flat(gx, s0, k * P + off - 0.08, s1, k * P + off + 0.08, Y_MARK, WHT)
            flat(gz, k * P + off - 0.08, s0, k * P + off + 0.08, s1, Y_MARK, WHT)

for i in range(N):
    for j in range(N):
        ix, jz = i * P, j * P
        g = mb_for(ix + RW / 2, jz + RW / 2, "g")
        for s in range(8):
            o = 1.2 + s * 2.1
            flat(g, ix + RW + 0.8, jz + o, ix + RW + 3.8, jz + o + 1.1, Y_MARK, (232, 232, 232))
            if i > 0:
                flat(g, ix - 3.8, jz + o, ix - 0.8, jz + o + 1.1, Y_MARK, (232, 232, 232))
            flat(g, ix + o, jz + RW + 0.8, ix + o + 1.1, jz + RW + 3.8, Y_MARK, (232, 232, 232))
            if j > 0:
                flat(g, ix + o, jz - 3.8, ix + o + 1.1, jz - 0.8, Y_MARK, (232, 232, 232))


def traffic_light(g, x, z, state):
    box(g, x, 3.05, z, 0.2, 5.5, 0.2, (58, 60, 66))
    box(g, x, 5.55, z, 0.5, 1.2, 0.5, (28, 28, 32))
    for face_z in (1, -1):
        for n_, (cy, on, off) in enumerate(((5.95, (255, 50, 40), (80, 20, 20)),
                                            (5.55, (255, 200, 40), (90, 70, 20)),
                                            (5.15, (60, 230, 90), (20, 70, 30)))):
            lit = (state == 0 and n_ == 2) or (state == 1 and n_ == 0)
            box(g, x, cy, z + face_z * 0.26, 0.26, 0.26, 0.04, on if lit else off, bright=1.0)
    for face_x in (1, -1):
        for n_, (cy, on, off) in enumerate(((5.95, (255, 50, 40), (80, 20, 20)),
                                            (5.55, (255, 200, 40), (90, 70, 20)),
                                            (5.15, (60, 230, 90), (20, 70, 30)))):
            lit = (state == 1 and n_ == 2) or (state == 0 and n_ == 0)
            box(g, x + face_x * 0.26, cy, z, 0.04, 0.26, 0.26, on if lit else off, bright=1.0)


def street_tree(g, tx, tz):
    box(g, tx, 2.0, tz, 0.35, 3.4, 0.35, (96, 66, 40))
    gcol = random.choice([(56, 128, 62), (70, 146, 72), (48, 110, 56)])
    box(g, tx, 4.4, tz, 2.6, 2.0, 2.6, gcol)
    box(g, tx, 5.7, tz, 1.7, 1.2, 1.7, shade(gcol, 1.1))


def bench(g, x, z, along_x):
    if along_x:
        box(g, x, 0.75, z, 1.8, 0.1, 0.5, (120, 80, 50))
        box(g, x, 1.1, z - 0.22, 1.8, 0.4, 0.08, (120, 80, 50))
        for s in (-0.7, 0.7):
            box(g, x + s, 0.55, z, 0.1, 0.5, 0.45, (50, 50, 54))
    else:
        box(g, x, 0.75, z, 0.5, 0.1, 1.8, (120, 80, 50))
        box(g, x - 0.22, 1.1, z, 0.08, 0.4, 1.8, (120, 80, 50))
        for s in (-0.7, 0.7):
            box(g, x, 0.55, z + s, 0.45, 0.5, 0.1, (50, 50, 54))


def bus_stop(g, x, z):
    box(g, x, 3.1, z, 3.4, 0.14, 1.6, (60, 70, 90))
    for sx in (-1.6, 1.6):
        box(g, x + sx, 1.7, z + 0.7, 0.1, 2.8, 0.1, (60, 60, 66))
    box(g, x, 1.8, z + 0.74, 3.2, 1.8, 0.04, (150, 190, 215))
    box(g, x, 0.85, z + 0.4, 2.2, 0.08, 0.5, (110, 80, 54))


def add_building(xa, za, xb, zb):
    bw, bd = xb - xa, zb - za
    cx, cz = (xa + xb) / 2, (za + zb) / 2
    tall = random.random() < 0.17
    h = random.uniform(34, 64) if tall else random.uniform(10, 26)
    ti = 0 if tall else random.choice((0, 1, 1, 2, 2))
    tint = random.choice(TINTS[ti])
    g = mb_for(cx, cz, "g")
    f = mb_for(cx, cz, "f%d" % ti)
    flat(g, xa - 2.2, za - 2.2, xb + 2.2, zb + 2.2, 0.31, (126, 126, 120))
    band = random.choice([(66, 74, 88), (92, 62, 58), (64, 84, 76), (88, 88, 94)])
    box(g, cx, 2.1, cz, bw + 0.15, 3.6, bd + 0.15, band, top=False, ao=0.3)
    for side in (1, -1):
        zz = zb + 0.09 if side == 1 else za - 0.09
        box(g, cx - bw * 0.22, 2.0, zz, bw * 0.34, 1.9, 0.05, (150, 192, 218))
        box(g, cx + bw * 0.28, 1.7, zz, 1.5, 2.6, 0.08, (40, 36, 34))
        box(g, cx + bw * 0.28, 1.0, zz + 0.03, 0.12, 0.12, 0.05, (210, 190, 80))
    awn = random.choice([(190, 50, 50), (50, 110, 170), (60, 140, 80), (210, 170, 50)])
    box(g, cx, 4.0, cz, bw + 0.9, 0.18, bd + 0.9, awn)
    box(g, cx, 3.82, cz, bw + 0.9, 0.18, bd + 0.9, shade(awn, 0.7), top=False)
    sign = random.choice([(255, 60, 120), (60, 220, 255), (255, 220, 60), (120, 255, 120)])
    box(g, cx - bw * 0.22, 4.7, zb + 0.35, bw * 0.34, 0.6, 0.1, sign, bright=1.0)
    box(f, cx, 0.3 + h / 2, cz, bw, h, bd, tint, top=False, tex=True, ao=0.3)
    cornice = (200, 196, 190)
    box(g, cx, 0.3 + h + 0.25, cz, bw + 0.5, 0.5, bd + 0.5, shade(cornice, 0.85))
    ry = 0.3 + h + 0.5
    flat(g, xa + 0.3, za + 0.3, xb - 0.3, zb - 0.3, ry + 0.01, (86, 86, 90))
    for _ in range(random.randint(1, 3)):
        ax = random.uniform(xa + 2, xb - 2)
        az = random.uniform(za + 2, zb - 2)
        box(g, ax, ry + 0.6, az, random.uniform(1.5, 3), 1.2, random.uniform(1.5, 3), (150, 150, 156))
        box(g, ax, ry + 1.3, az, 0.8, 0.2, 0.8, (110, 110, 116))
    if random.random() < 0.4:
        tx, tz = random.uniform(xa + 3, xb - 3), random.uniform(za + 3, zb - 3)
        for lx in (-0.9, 0.9):
            for lz in (-0.9, 0.9):
                box(g, tx + lx, ry + 1.0, tz + lz, 0.12, 2.0, 0.12, (70, 70, 74))
        box(g, tx, ry + 3.0, tz, 2.6, 2.0, 2.6, (150, 110, 80))
        box(g, tx, ry + 4.2, tz, 2.8, 0.4, 2.8, (90, 70, 54))
    box(g, xb - 2.0, ry + 1.3, zb - 2.0, 2.4, 2.6, 2.4, shade(cornice, 0.8))
    if tall:
        th = random.uniform(8, 16)
        box(f, cx, ry + th / 2, cz, bw * 0.62, th, bd * 0.62, tint, top=False, tex=True)
        box(g, cx, ry + th + 0.25, cz, bw * 0.62 + 0.4, 0.5, bd * 0.62 + 0.4, shade(cornice, 0.85))
        box(g, cx, ry + th + 4.5, cz, 0.2, 8, 0.2, (170, 40, 40))
        box(g, cx, ry + th + 8.6, cz, 0.4, 0.4, 0.4, (255, 60, 60), bright=1.0)
    elif random.random() < 0.3:
        box(g, xa + 1.5, ry + 3.5, za + 1.5, 0.2, 7, 0.2, (170, 40, 40))


for i in range(N):
    for j in range(N):
        x0, z0 = i * P + RW, j * P + RW
        cx0, cz0 = x0 + S_BLOCK / 2, z0 + S_BLOCK / 2
        g = mb_for(cx0, cz0, "g")
        box(g, cx0, 0.15, cz0, S_BLOCK, 0.3, S_BLOCK, (164, 164, 158))
        for off in range(4, int(S_BLOCK), 6):
            flat(g, x0 + off, z0 + 0.05, x0 + off + 0.08, z0 + S_BLOCK - 0.05, 0.305, (140, 140, 134))
        block_rects_for_map.append((x0, z0, i, j))
        for lx, lz in ((x0 + 0.9, z0 + 0.9), (x0 + S_BLOCK - 0.9, z0 + 0.9),
                       (x0 + 0.9, z0 + S_BLOCK - 0.9), (x0 + S_BLOCK - 0.9, z0 + S_BLOCK - 0.9)):
            box(g, lx, 3.05, lz, 0.18, 5.5, 0.18, (62, 64, 70))
            box(g, lx, 5.9, lz, 0.55, 0.18, 0.55, (255, 244, 200), bright=1.0)
        if (i + j) % 2 == 0:
            traffic_light(g, x0 + 0.6, z0 + 0.6, (i + j) // 2 % 2)
        else:
            traffic_light(g, x0 + S_BLOCK - 0.6, z0 + S_BLOCK - 0.6, (i * j) % 2)
        box(g, x0 + 1.0, 0.65, z0 + 12, 0.35, 0.7, 0.35, (200, 40, 40))
        box(g, x0 + 1.0, 1.05, z0 + 12, 0.42, 0.12, 0.42, (170, 30, 30))
        box(g, x0 + S_BLOCK - 1.0, 0.7, z0 + S_BLOCK - 14, 0.5, 0.8, 0.5, (40, 90, 60))
        for tz_ in (14, 32):
            if random.random() < 0.6:
                street_tree(g, x0 + 0.8, z0 + tz_)
        if random.random() < 0.5:
            bench(g, x0 + 10, z0 + 0.9, True)
        if random.random() < 0.15:
            bus_stop(g, x0 + S_BLOCK / 2, z0 + 1.6)
        if random.random() < 0.13:
            parks.add((i, j))
            blocks[(i, j)] = []
            box(g, cx0, 0.375, cz0, S_BLOCK - 5, 0.15, S_BLOCK - 5, (84, 150, 80))
            box(g, cx0, 0.46, cz0, 2.4, 0.04, S_BLOCK - 5, (190, 176, 140))
            box(g, cx0, 0.46, cz0, S_BLOCK - 5, 0.04, 2.4, (190, 176, 140))
            box(g, cx0, 0.7, cz0, 3.0, 0.5, 3.0, (150, 150, 150))
            box(g, cx0, 1.2, cz0, 1.6, 0.6, 1.6, (120, 170, 220))
            for _ in range(9):
                tx = x0 + random.uniform(6, S_BLOCK - 6)
                tz = z0 + random.uniform(6, S_BLOCK - 6)
                if abs(tx - cx0) < 3 or abs(tz - cz0) < 3:
                    continue
                box(g, tx, 1.95, tz, 0.5, 3, 0.5, (100, 68, 42))
                gc = random.choice([(56, 128, 62), (70, 146, 72), (48, 110, 56)])
                box(g, tx, 4.4, tz, random.uniform(3.2, 4.2), 2.2, random.uniform(3.2, 4.2), gc)
                box(g, tx, 6.0, tz, 2.3, 1.6, 2.3, shade(gc, 1.1))
            for _ in range(6):
                fx = x0 + random.uniform(4, S_BLOCK - 4)
                fz = z0 + random.uniform(4, S_BLOCK - 4)
                box(g, fx, 0.6, fz, 1.2, 0.3, 1.2, random.choice([(220, 60, 90), (240, 200, 60), (160, 80, 200)]))
            continue
        m = 3
        inner = S_BLOCK - 2 * m
        w = (inner - 3) / 2
        mode = random.choice((1, 2, 4, 4))
        if mode == 1:
            rects = [(x0 + m, z0 + m, x0 + m + inner, z0 + m + inner)]
        elif mode == 2:
            if random.random() < 0.5:
                rects = [(x0 + m, z0 + m, x0 + m + w, z0 + m + inner),
                         (x0 + m + w + 3, z0 + m, x0 + m + inner, z0 + m + inner)]
            else:
                rects = [(x0 + m, z0 + m, x0 + m + inner, z0 + m + w),
                         (x0 + m, z0 + m + w + 3, x0 + m + inner, z0 + m + inner)]
        else:
            rects = []
            for a in (0, 1):
                for b in (0, 1):
                    xa, za = x0 + m + a * (w + 3), z0 + m + b * (w + 3)
                    rects.append((xa, za, xa + w, za + w))
        blocks[(i, j)] = rects
        for r in rects:
            add_building(*r)

cloud = MB()
for _ in range(16):
    ccx, ccz, cy_ = random.uniform(-100, WORLD + 100), random.uniform(-100, WORLD + 100), random.uniform(110, 160)
    for _ in range(random.randint(3, 5)):
        sx, sz = random.uniform(30, 70), random.uniform(20, 40)
        px_, pz_ = ccx + random.uniform(-30, 30), ccz + random.uniform(-20, 20)
        sy = random.uniform(8, 14)
        box(cloud, px_, cy_, pz_, sx, sy, sz, (246, 248, 252), bright=0.92)
        flat(cloud, px_ - sx / 2, pz_ - sz / 2, px_ + sx / 2, pz_ + sz / 2, cy_ - sy / 2, (214, 220, 232))
Entity(model=cloud.mesh(), double_sided=True)

FACADES = [make_glass(), make_brick(), make_concrete()]
for (ci, cj, kind), mbx in chunk_meshes.items():
    if kind == "g":
        Entity(model=mbx.mesh(), double_sided=True)
    else:
        Entity(model=mbx.mesh(), texture=FACADES[int(kind[1])], double_sided=True)


def hits_building(x, z, r):
    for xa, za, xb, zb in blocks.get((int(x // P), int(z // P)), ()):
        cx = max(xa, min(x, xb))
        cz = max(za, min(z, zb))
        if (x - cx) ** 2 + (z - cz) ** 2 < r * r:
            return True
    return False


def move_circle(o, dx, dz, r):
    nx = cl(o.x + dx, 3, WORLD - 3)
    if not hits_building(nx, o.z, r):
        o.x = nx
    nz = cl(o.z + dz, 3, WORLD - 3)
    if not hits_building(o.x, nz, r):
        o.z = nz


def build_person(shirt, pants, skin, hair, style, outfit, shoes, glasses=False, beard=False):
    body, leg, arm = MB(), MB(), MB()
    dark = (36, 30, 26)
    box(body, 0, 0.9, 0, 0.6, 0.26, 0.34, pants)
    box(body, 0, 1.02, 0, 0.62, 0.07, 0.36, dark)
    box(body, 0, 1.02, 0.185, 0.09, 0.06, 0.02, (210, 190, 80))
    box(body, 0, 1.31, 0, 0.66, 0.6, 0.36, shirt)
    box(body, 0, 1.64, 0, 0.15, 0.14, 0.15, shade(skin, 0.95))
    box(body, 0, 1.6, 0.02, 0.3, 0.05, 0.22, shade(shirt, 1.15))

    if outfit == "jacket":
        box(body, 0, 1.3, 0.185, 0.035, 0.58, 0.02, shade(shirt, 0.6))
        box(body, -0.19, 1.15, 0.185, 0.16, 0.12, 0.02, shade(shirt, 0.8))
        box(body, 0.19, 1.15, 0.185, 0.16, 0.12, 0.02, shade(shirt, 0.8))

    elif outfit == "cop":
        navy = (30, 45, 80)
        vest = (140, 130, 100)
        belt = (25, 25, 25)
        glove = (20, 20, 22)
        box(body, 0, 1.35, 0.02, 0.55, 0.42, 0.32, vest)
        box(body, 0, 1.35, 0.19, 0.35, 0.30, 0.04, shade(vest, 0.85))   # Передняя панель
        box(body, 0, 1.35, -0.17, 0.35, 0.30, 0.04, shade(vest, 0.85))  # Задняя панель
        for yy in (1.22, 1.38):
            box(body, -0.12, yy, 0.20, 0.10, 0.08, 0.03, shade(vest, 0.7))
            box(body,  0.12, yy, 0.20, 0.10, 0.08, 0.03, shade(vest, 0.7))
        box(body, 0, 1.05, 0, 0.64, 0.07, 0.38, belt)
        box(body, 0.22, 1.05, 0.14, 0.07, 0.07, 0.05, (40, 40, 40))
        box(body, -0.22, 1.05, 0.10, 0.06, 0.06, 0.04, (50, 50, 50))
        box(body, 0.29, 1.48, 0.06, 0.06, 0.06, 0.02, (200, 170, 50))
        box(body, -0.29, 1.48, 0.06, 0.08, 0.05, 0.02, (30, 80, 160))
        box(body, -0.24, 1.50, 0.12, 0.04, 0.09, 0.03, (20, 20, 20))
        box(body, -0.24, 1.57, 0.12, 0.01, 0.05, 0.01, (20, 20, 20))
        box(body, 0, 0.55, 0.16, 0.16, 0.14, 0.05, (30, 30, 30))

    elif outfit == "stripe":
        for yy in (1.12, 1.3, 1.48):
            box(body, 0, yy, 0, 0.67, 0.06, 0.37, shade(shirt, 0.55))

    elif outfit == "hoodie":
        box(body, 0, 1.6, -0.1, 0.4, 0.12, 0.2, shade(shirt, 0.9))
        box(body, 0, 1.12, 0.185, 0.4, 0.14, 0.02, shade(shirt, 0.8))

    hy = 1.9
    box(body, 0, hy, 0, 0.34, 0.36, 0.34, skin)
    for sx in (-1, 1):
        box(body, sx * 0.19, hy - 0.02, 0, 0.04, 0.1, 0.07, shade(skin, 0.9))
        box(body, sx * 0.085, hy + 0.03, 0.172, 0.08, 0.055, 0.02, (250, 250, 250))
        box(body, sx * 0.085, hy + 0.03, 0.182, 0.04, 0.045, 0.02, (30, 40, 60))
        box(body, sx * 0.085, hy + 0.1, 0.176, 0.1, 0.022, 0.02, hair)
    box(body, 0, hy - 0.04, 0.2, 0.06, 0.09, 0.06, shade(skin, 0.88))
    box(body, 0, hy - 0.13, 0.176, 0.11, 0.025, 0.02, (160, 70, 70))

    if glasses:
        box(body, 0, hy + 0.03, 0.19, 0.3, 0.07, 0.03, (14, 14, 18))
        box(body, 0, hy + 0.03, 0.2, 0.05, 0.02, 0.02, (14, 14, 18))
    if beard:
        box(body, 0, hy - 0.11, 0.18, 0.28, 0.1, 0.03, hair)
        box(body, 0, hy - 0.05, 0.2, 0.12, 0.025, 0.03, hair)

    if style == "short":
        box(body, 0, hy + 0.2, 0, 0.37, 0.1, 0.37, hair)
        box(body, 0, hy + 0.06, -0.15, 0.37, 0.3, 0.08, hair)
        for sx in (-1, 1):
            box(body, sx * 0.18, hy + 0.1, 0, 0.04, 0.16, 0.3, hair)
        box(body, 0, hy + 0.16, 0.17, 0.3, 0.06, 0.04, hair)
    elif style == "long":
        box(body, 0, hy + 0.2, 0, 0.38, 0.1, 0.38, hair)
        box(body, 0, hy - 0.08, -0.16, 0.38, 0.55, 0.08, hair)
        for sx in (-1, 1):
            box(body, sx * 0.19, hy - 0.04, 0.0, 0.04, 0.45, 0.3, hair)
        box(body, 0, hy + 0.16, 0.17, 0.3, 0.06, 0.04, hair)
    elif style == "cap":
        if outfit == "cop":
            capc = (30, 45, 80)
            box(body, 0, hy + 0.2, 0, 0.38, 0.1, 0.38, capc)
            box(body, 0, hy + 0.15, 0.27, 0.34, 0.03, 0.22, shade(capc, 0.5))
            box(body, 0, hy + 0.22, 0.0, 0.20, 0.04, 0.20, shade(capc, 1.2))
            box(body, 0, hy + 0.06, -0.15, 0.36, 0.14, 0.06, hair)
        else:
            capc = random.choice([(200, 40, 40), (40, 90, 200), (30, 30, 34), (240, 240, 240)])
            box(body, 0, hy + 0.2, 0, 0.38, 0.1, 0.38, capc)
            box(body, 0, hy + 0.15, 0.27, 0.34, 0.03, 0.2, shade(capc, 0.6))
            box(body, 0, hy + 0.06, -0.15, 0.36, 0.14, 0.06, hair)
    elif style == "afro":
        box(body, 0, hy + 0.2, -0.02, 0.52, 0.34, 0.52, hair)

    sleeve_long = outfit != "tee"
    if sleeve_long:
        arm_col = shirt
        if outfit == "cop":
            arm_col = (30, 45, 80)
        box(arm, 0, -0.27, 0, 0.2, 0.54, 0.24, arm_col, top=False)
        box(arm, 0, -0.55, 0, 0.21, 0.05, 0.25, shade(arm_col, 0.7), top=False)
        hand_col = (20, 20, 22) if outfit == "cop" else skin
        box(arm, 0, -0.64, 0, 0.15, 0.16, 0.17, hand_col, top=False)
    else:
        box(arm, 0, -0.14, 0, 0.21, 0.28, 0.25, shirt, top=False)
        box(arm, 0, -0.48, 0, 0.17, 0.4, 0.2, skin, top=False)
        box(arm, 0, -0.7, 0, 0.15, 0.12, 0.17, skin, top=False)

    box(leg, 0, -0.36, 0, 0.27, 0.72, 0.3, pants, top=False)
    box(leg, 0, -0.66, 0, 0.285, 0.05, 0.315, shade(pants, 0.75), top=False)
    box(leg, 0, -0.74, 0.06, 0.29, 0.12, 0.42, shoes, top=False)
    box(leg, 0, -0.79, 0.06, 0.3, 0.04, 0.44,
        (235, 235, 235) if shoes != (235, 235, 235) else (120, 120, 120), top=False)
    return body, leg, arm


def build_gun():
    g = MB()
    box(g, 0, 0.02, 0.15, 0.055, 0.08, 0.34, (44, 44, 50))
    box(g, 0, 0.02, 0.34, 0.03, 0.03, 0.06, (20, 20, 22))
    box(g, 0, -0.02, 0.12, 0.05, 0.04, 0.24, (70, 70, 76))
    box(g, 0, -0.09, 0.04, 0.05, 0.14, 0.07, (36, 28, 22))
    box(g, 0, -0.05, 0.1, 0.02, 0.05, 0.06, (30, 30, 34))
    box(g, 0, 0.07, 0.3, 0.015, 0.02, 0.02, (220, 220, 220))
    return g


class Person:
    def __init__(self, shirt, pants, skin, hair, style, outfit, shoes, glasses=False, beard=False):
        body, leg, arm = build_person(shirt, pants, skin, hair, style, outfit, shoes, glasses, beard)
        self.root = Entity(enabled=False)
        Entity(parent=self.root, model=body.mesh(), double_sided=True)
        self.legs = [Entity(parent=self.root, model=leg.mesh(), double_sided=True, position=(s * 0.16, 0.8, 0))
                     for s in (-1, 1)]
        self.arms = [Entity(parent=self.root, model=arm.mesh(), double_sided=True, position=(s * 0.43, 1.54, 0))
                     for s in (-1, 1)]
        self.gun = Entity(parent=self.root, model=build_gun().mesh(), double_sided=True,
                          position=(0.43, 1.52, 0.6), enabled=False)
        self.shadow = Entity(parent=self.root, model="plane", scale=(0.95, 1, 0.95), position=(0, 0.06, 0),
                             color=rgb(30, 31, 34))
        self.phase = 0.0

    def animate(self, speed, dt, aiming=False):
        self.phase += speed * dt * 1.8
        sw = math.sin(self.phase) * 38 * min(1, speed / 3)
        self.legs[0].rotation_x = sw
        self.legs[1].rotation_x = -sw
        self.arms[0].rotation_x = -sw * 0.8 if not aiming else -35
        self.arms[1].rotation_x = -90 if aiming else sw * 0.8
        self.gun.enabled = aiming


def random_person(kind="ped"):
    if kind == "cop":
        return Person(
            shirt=(30, 45, 80),
            pants=(25, 28, 35),
            skin=random.choice(SKINS),
            hair=(30, 24, 20),
            style="cap",
            outfit="cop",
            shoes=(20, 20, 22),
            glasses=random.random() < 0.3,
            beard=random.random() < 0.25
        )
    return Person(random.choice(SHIRTS), random.choice(PANTS), random.choice(SKINS), random.choice(HAIRS),
                  random.choice(["short", "short", "long", "cap", "afro", "bald"]),
                  random.choice(["tee", "tee", "jacket", "stripe", "hoodie"]), random.choice(SHOES),
                  glasses=random.random() < 0.15, beard=random.random() < 0.18)

def build_car(col, kind, body):
    mb = MB()
    L = {"sedan": 4.5, "hatch": 3.9, "suv": 4.7, "pickup": 5.1, "van": 4.8, "taxi": 4.5, "police": 4.6}[body]
    hl = L / 2
    dark = (30, 30, 34)
    flat(mb, -1.3, -hl - 0.4, 1.3, hl + 0.4, 0.06, (20, 21, 24))
    wz = hl - 1.0
    for sx in (-1, 1):
        for sz in (-1, 1):
            box(mb, sx * 1.0, 0.37, sz * wz, 0.32, 0.74, 0.74, (20, 20, 22))
            box(mb, sx * 1.17, 0.37, sz * wz, 0.04, 0.46, 0.46, (196, 196, 202))
            box(mb, sx * 1.19, 0.37, sz * wz, 0.02, 0.14, 0.14, (90, 90, 96))
    box(mb, 0, 0.68, 0, 2.0, 0.62, L, col)
    box(mb, 0, 0.42, 0, 2.03, 0.1, L - 1.0, dark)
    for sz in (-1, 1):
        box(mb, 0, 0.55, sz * (hl + 0.01), 2.06, 0.3, 0.2, (46, 46, 52))
        box(mb, 0, 0.7, sz * (hl + 0.02), 2.04, 0.05, 0.2, (200, 200, 205))
    box(mb, 0, 1.03, hl * 0.45, 1.82, 0.05, hl * 0.75, shade(col, 1.12))
    dims = {"sedan": (2.0, 0.62, -0.25), "hatch": (2.2, 0.64, -0.3), "suv": (2.7, 0.78, -0.35),
            "pickup": (1.5, 0.66, 0.55), "van": (2.0, 0.8, 0.6), "taxi": (2.0, 0.62, -0.25),
            "police": (2.0, 0.62, -0.25)}
    cl_, ch_, cz_ = dims[body]
    if body == "van":
        box(mb, 0, 1.69, -0.1, 2.0, 1.4, L - 1.2, col)
        box(mb, 0, 1.85, hl - 0.58, 1.8, 0.62, 0.05, (48, 68, 94))
        for sx in (-1, 1):
            box(mb, sx * 1.005, 1.95, 0.9, 0.03, 0.5, 1.2, (48, 68, 94))
        box(mb, 0, 2.4, -0.1, 1.9, 0.08, L - 1.4, shade(col, 0.9))
        ch_ = 1.4
    else:
        cy = 0.99 + ch_ / 2
        box(mb, 0, cy, cz_, 1.76, ch_, cl_, (48, 68, 94))
        for sz in (-1, 1):
            for sx in (-1, 1):
                box(mb, sx * 0.88, cy, cz_ + sz * (cl_ / 2 - 0.05), 0.07, ch_, 0.1, col)
        for sx in (-1, 1):
            box(mb, sx * 0.88, cy, cz_, 0.07, ch_, 0.09, col)
        box(mb, 0, 0.99 + ch_ + 0.05, cz_, 1.8, 0.1, cl_ + 0.1, shade(col, 0.94))
        box(mb, 0, cy + 0.05, cz_ + cl_ / 2 + 0.005, 1.4, ch_ * 0.45, 0.02, (130, 166, 200))
    if body == "pickup":
        bz = -hl + 1.0
        box(mb, 0, 1.0, bz, 1.8, 0.06, 1.9, (34, 34, 38))
        for sx in (-1, 1):
            box(mb, sx * 0.95, 1.2, bz, 0.1, 0.42, 2.0, col)
        box(mb, 0, 1.2, bz - 1.0, 1.9, 0.42, 0.1, col)
        box(mb, 0, 1.2, bz + 1.0, 1.9, 0.46, 0.1, col)
    if body == "suv":
        for sx in (-1, 1):
            box(mb, sx * 0.8, 1.84, cz_, 0.06, 0.06, cl_, (60, 60, 66))
    for sx in (-1, 1):
        box(mb, sx * 0.68, 0.86, hl + 0.01, 0.52, 0.2, 0.1, (60, 60, 66))
        box(mb, sx * 0.68, 0.86, hl + 0.06, 0.44, 0.14, 0.04, (255, 246, 196))
        box(mb, sx * 0.68, 0.86, -hl - 0.01, 0.52, 0.2, 0.1, (80, 12, 12))
        box(mb, sx * 0.68, 0.86, -hl - 0.06, 0.44, 0.14, 0.04, (220, 30, 30))
        box(mb, sx * 0.9, 0.5, hl + 0.1, 0.16, 0.1, 0.06, (255, 230, 150))
        box(mb, sx * 1.08, 1.12, cz_ + cl_ / 2 - 0.1, 0.14, 0.12, 0.22, col)
        for hz_ in (0.5, -0.6):
            box(mb, sx * 1.01, 0.72, hz_, 0.03, 0.06, 0.2, (210, 210, 215))
        for sz_ in (0.1, -1.0):
            box(mb, sx * 1.012, 0.68, sz_, 0.02, 0.56, 0.03, (30, 30, 34))
    box(mb, 0, 0.8, hl + 0.03, 0.9, 0.2, 0.06, (30, 30, 34))
    for k in range(3):
        box(mb, 0, 0.74 + k * 0.06, hl + 0.065, 0.86, 0.02, 0.02, (190, 190, 195))
    for sz in (-1, 1):
        box(mb, 0, 0.52, sz * (hl + 0.12), 0.5, 0.22, 0.03, (236, 236, 226))
        box(mb, 0, 0.52, sz * (hl + 0.14), 0.4, 0.07, 0.02, (40, 40, 60))
    box(mb, 0.6, 0.3, -hl - 0.1, 0.1, 0.1, 0.22, (70, 70, 76))
    light_y, light_z = 0.99 + ch_ + 0.25, cz_
    if body == "taxi":
        box(mb, 0, 0.99 + ch_ + 0.2, cz_, 0.7, 0.22, 0.3, (250, 240, 200), bright=1.0)
        box(mb, 0, 0.99 + ch_ + 0.2, cz_, 0.72, 0.06, 0.32, (30, 30, 34))
    if body == "police":
        box(mb, 0, 0.7, 0.0, 2.06, 0.32, 2.4, (15, 15, 18))
        for sx in (-1, 1):
            box(mb, sx * 1.02, 0.72, cz_, 0.02, 0.18, 1.2, (220, 220, 220))
        box(mb, 0, 0.99 + ch_ + 0.18, cz_, 1.4, 0.08, 0.30, (20, 20, 24))
        box(mb, 0, 0.55, hl + 0.15, 1.6, 0.25, 0.08, (30, 30, 34))
        box(mb, 0, 0.42, hl + 0.18, 1.4, 0.06, 0.06, (30, 30, 34))
        box(mb, -0.5, 0.99 + ch_ + 0.3, cz_ - 0.3, 0.02, 0.4, 0.02, (20, 20, 20))
        box(mb, 0.5, 0.99 + ch_ + 0.25, cz_ - 0.3, 0.02, 0.3, 0.02, (20, 20, 20))
        box(mb, -1.02, 0.95, cz_ + 0.3, 0.08, 0.08, 0.12, (30, 30, 34))
    return mb, light_y, light_z


class Car:
    def __init__(self, col, kind="civ", body="sedan"):
        self.col, self.kind, self.body = col, kind, body
        self.x = self.z = self.h = self.v = 0.0
        self.hp = 100.0
        self.driver = None
        self.dir = 0
        self.cruise = 10.0
        self.maxv = 30.0
        self.nox = self.stuck = self.ghost = self.rev = self.idle = self.smoke_t = self.honk_cd = self.crash_cd = 0.0
        self.rev_steer = 1
        self.deployed = False
        self.vis = True
        self.active = False
        mb, ly, lz = build_car(col, kind, body)
        self.root = Entity(model=mb.mesh(), double_sided=True, enabled=False)
        self.l1 = self.l2 = None
        if kind == "police":
            self.l1 = Entity(parent=self.root, model="cube", scale=(0.6, 0.15, 0.35), position=(-0.45, ly, lz),
                             color=rgb(255, 40, 40))
            self.l2 = Entity(parent=self.root, model="cube", scale=(0.6, 0.15, 0.35), position=(0.45, ly, lz),
                             color=rgb(60, 80, 255))

    def reset(self, x, z, h):
        self.x, self.z, self.h = x, z, h
        self.v = 0.0
        self.hp = 100.0
        self.driver = None
        self.dir = min(range(4), key=lambda d: abs(adiff(DIR_H[d], h)))
        self.cruise = random.uniform(9, 14)
        self.maxv = random.uniform(26, 36) if self.kind == "civ" else 34
        self.nox = self.stuck = self.ghost = self.rev = self.idle = self.smoke_t = self.honk_cd = self.crash_cd = 0.0
        self.deployed = False
        self.vis = True
        self.active = True
        self.root.enabled = True
        self.sync()

    def sync(self):
        self.root.position = (self.x, 0, self.z)
        self.root.rotation_y = self.h

    def pts(self, offs=(-1.5, 0, 1.5)):
        sh, ch = math.sin(math.radians(self.h)), math.cos(math.radians(self.h))
        return [(self.x + sh * o, self.z + ch * o) for o in offs]


class Ped:
    def __init__(self):
        self.person = random_person("ped")
        self.root = self.person.root
        self.person.root.scale = random.uniform(0.93, 1.07)
        self.x = self.z = self.h = 0.0
        self.t = 1.0
        self.state = "walk"
        self.idle = False
        self.vis = True
        self.active = False

    def activate(self, x, z):
        self.x, self.z = x, z
        self.h = random.uniform(0, 360)
        self.t = random.uniform(1, 4)
        self.state = "walk"
        self.idle = random.random() < 0.25
        self.vis = True
        self.active = True
        self.root.rotation_x = 0
        self.root.y = 0
        self.person.shadow.enabled = True
        self.root.position = (x, 0, z)
        self.root.enabled = True

    def update(self, dt):
        far = abs(self.x - player.x) > 130 or abs(self.z - player.z) > 130
        if far:
            if self.vis:
                self.root.enabled = False
                self.vis = False
            return
        if not self.vis:
            self.root.enabled = True
            self.vis = True
        self.t -= dt
        if self.t <= 0:
            self.t = random.uniform(1.5, 4)
            self.state = "walk"
            self.h = random.uniform(0, 360)
            self.idle = random.random() < 0.25
        sp = 7.5 if self.state == "flee" else (0 if self.idle else 1.6)
        if sp:
            nx = self.x + math.sin(math.radians(self.h)) * sp * dt
            nz = self.z + math.cos(math.radians(self.h)) * sp * dt
            if hits_building(nx, nz, 0.5) or not (3 < nx < WORLD - 3 and 3 < nz < WORLD - 3):
                self.h += 180 + random.uniform(-30, 30)
            else:
                self.x, self.z = nx, nz
        self.person.animate(sp, dt)
        self.root.position = (self.x, 0, self.z)
        self.root.rotation_y = self.h

def police_knows_player():
    if player.stars <= 0:
        return False
    ev = wanted.evidence
    if not ev:
        return True
    if player.car:
        return ("car" in ev) or ("face" in ev) or ("clothes" in ev)
    if ("face" in ev) or ("clothes" in ev):
        return True
    if ("weapon" in ev) and (held_keys["e"] or held_keys["enter"]):
        return True
    return False


def police_target():
    if wanted.state == "spotted":
        return player.x, player.z
    return wanted.last_seen_pos[0], wanted.last_seen_pos[1]


def steer_person_around(o, tx, tz, speed, dt, radius=0.55):
    dx, dz = tx - o.x, tz - o.z
    d = math.hypot(dx, dz)
    if d < 0.001:
        return o.h, 0.0
    base = math.degrees(math.atan2(dx, dz))
    for off in (0, 22, -22, 45, -45, 70, -70, 100, -100, 135, -135, 180):
        h = base + off
        sh, ch = math.sin(math.radians(h)), math.cos(math.radians(h))
        if not hits_building(o.x + sh * 2.0, o.z + ch * 2.0, radius) and \
                not hits_building(o.x + sh * speed * dt, o.z + ch * speed * dt, radius):
            return h, speed
    return base + 180, speed * 0.4


def drive_step(c, dt, throttle, steer):
    ox, oz, oh, ov = c.x, c.z, c.h, c.v
    physics(c, dt, throttle, steer)
    sh, ch = math.sin(math.radians(c.h)), math.cos(math.radians(c.h))
    nx = cl(c.x + sh * c.v * dt, 4, WORLD - 4)
    nz = cl(c.z + ch * c.v * dt, 4, WORLD - 4)
    blocked = False
    for o in (-1.7, 0.0, 1.7):
        if hits_building(nx + sh * o, nz + ch * o, 1.15):
            blocked = True
            break
    if blocked:
        c.x, c.z, c.h, c.v = ox, oz, oh, ov
        c.v = -abs(ov) * 0.25
        c.rev = 1.2
        c.rev_steer = random.choice((-1, 1))
        c.stuck = 1.0
        return False
    c.x, c.z = nx, nz
    return True

class Cop:
    def __init__(self):
        self.person = random_person("cop")
        self.root = self.person.root
        self.x = self.z = self.h = 0.0
        self.hp = 60.0
        self.cd = 1.0
        self.idle = 0.0
        self.active = False

    def activate(self, x, z):
        self.x, self.z = x, z
        self.h = 0.0
        self.hp = 60.0
        self.cd = random.uniform(0.3, 1.0)
        self.idle = 0.0
        self.active = True
        self.root.rotation_x = 0
        self.root.y = 0
        self.person.shadow.enabled = True
        self.root.position = (x, 0, z)
        self.root.enabled = True

    def update(self, dt):
        moving = 0.0
        aiming = False
        if player.alive and player.stars > 0:
            tx, tz = police_target()
            dx, dz = player.x - self.x, player.z - self.z
            d = math.hypot(dx, dz) + 1e-6
            los = clear_line(self.x, self.z, player.x, player.z)
            knows = police_knows_player()
            spotted = los and knows and d < 70
            run_sp = 7.2 if player.stars >= 3 else 6.2

            if spotted:
                self.h += cl(adiff(math.degrees(math.atan2(dx, dz)), self.h), -240 * dt, 240 * dt)
                if d > 11:
                    h, sp = steer_person_around(self, player.x, player.z, run_sp, dt)
                    self.h += cl(adiff(h, self.h), -240 * dt, 240 * dt)
                    move_circle(self, math.sin(math.radians(self.h)) * sp * dt,
                                math.cos(math.radians(self.h)) * sp * dt, 0.5)
                    moving = sp
                elif d < 5:
                    move_circle(self, -dx / d * 3.2 * dt, -dz / d * 3.2 * dt, 0.5)
                    moving = 3.2
                else:
                    aiming = True

                self.cd -= dt
                if d < 34 and self.cd <= 0:
                    self.cd = random.uniform(0.5, 1.0) if player.stars >= 3 else random.uniform(0.7, 1.2)
                    tracer(self.x, 1.3, self.z, self.h, min(d, 34))
                    scare(self.x, self.z)
                    snd.at("gun", self.x, self.z, 0.7, 0.85, 160)
                    if random.random() < (0.4 if player.stars >= 3 else 0.3):
                        hurt_player(8)
            else:
                h, sp = steer_person_around(self, tx, tz, run_sp * 0.85, dt)
                self.h += cl(adiff(h, self.h), -200 * dt, 200 * dt)
                move_circle(self, math.sin(math.radians(self.h)) * sp * dt,
                            math.cos(math.radians(self.h)) * sp * dt, 0.5)
                moving = sp
                self.cd = max(self.cd, 0.25)
        elif player.alive:
            self.idle += dt
            self.person.animate(0, dt)
            self.root.position = (self.x, 0, self.z)
            self.root.rotation_y = self.h
            return

        self.person.animate(moving, dt, aiming=aiming)
        self.root.position = (self.x, 0, self.z)
        self.root.rotation_y = self.h

class Player:
    def __init__(self):
        self.person = Person((200, 40, 40), (50, 70, 120), (236, 190, 150), (42, 30, 24), "short", "jacket",
                             (235, 235, 235), glasses=True)
        self.root = self.person.root
        self.money = 500
        self.reset()

    def reset(self):
        self.x = 3 * P + RW + 1.4
        self.z = 3 * P + RW + 20
        self.y = 0.0
        self.vy = 0.0
        self.h = 0.0
        self.hp = 100.0
        self.car = None
        self.cd = 0.0
        self.stars = 0
        self.crime_t = 0.0
        self.hit_cd = 0.0
        self.hot_timer = 0.0
        self.alive = True
        self.dead_t = 0.0
        self.root.enabled = True
        self.root.rotation_x = 0
        self.root.y = 0
        self.person.shadow.enabled = True


player = Player()
cam_pos[0], cam_pos[2] = player.x, player.z

cars, peds, cops, corpses = [], [], [], []
car_free = {"civ": [], "police": []}
ped_free, cop_free = [], []
for _ in range(32):
    car_free["civ"].append(Car(random.choice(CAR_COLORS), "civ", random.choice(CAR_BODIES)))
for _ in range(2):
    car_free["civ"].append(Car((240, 200, 40), "civ", "taxi"))
for _ in range(6):
    car_free["police"].append(Car((240, 240, 245), "police", "police"))
for _ in range(46):
    ped_free.append(Ped())
for _ in range(8):
    cop_free.append(Cop())
mine = Car((200, 40, 40), "civ", "sedan")


def ui(**kw):
    return Entity(parent=camera.ui, **kw)


_hud_cache = {}


def set_text(t, key, s):
    if _hud_cache.get(key) != s:
        _hud_cache[key] = s
        t.text = s


hud_money = Text(text="", position=(0.86, 0.47), origin=(0.5, 0.5), scale=2, color=rgb(120, 230, 120))
hud_speed = Text(text="", position=(0.86, -0.40), origin=(0.5, 0.5), scale=2.2, color=rgb(255, 255, 255))
hud_stars = [ui(model="quad", scale=0.035, rotation_z=45, position=(0.86 - k * 0.045, 0.40, -0.01),
                color=rgb(30, 30, 30)) for k in range(6)]
ui(model="quad", origin=(-0.5, 0), scale=(0.31, 0.03), position=(-0.84, -0.44, 0), color=rgb(0, 0, 0))
hud_hp = ui(model="quad", origin=(-0.5, 0), scale=(0.3, 0.022), position=(-0.835, -0.44, -0.01), color=rgb(200, 40, 40))
ui(model="quad", origin=(-0.5, 0), scale=(0.31, 0.03), position=(-0.84, -0.40, 0), color=rgb(0, 0, 0))
hud_car = ui(model="quad", origin=(-0.5, 0), scale=(0.3, 0.022), position=(-0.835, -0.40, -0.01), color=rgb(70, 140, 220))
hud_cross = Text(text="+", origin=(0, 0), scale=2, color=rgb(255, 255, 255))
hud_wasted = Text(text="WASTED", origin=(0, 0), scale=9, color=rgb(200, 30, 30), enabled=False)
hud_flash = ui(model="quad", scale=(3, 2), color=Color(0.85, 0.05, 0.05, 0.0), z=0.5, enabled=False)

MM = 0.30
MMX, MMY = -0.70, 0.33


def quad_xy(mb, cx, cy, hs, col):
    c = tc(col)
    n = len(mb.v)
    mb.v += [Vec3(cx - hs, cy - hs, 0), Vec3(cx + hs, cy - hs, 0), Vec3(cx + hs, cy + hs, 0), Vec3(cx - hs, cy + hs, 0)]
    mb.c += [c] * 4
    mb.uv += [Vec2(0, 0)] * 4
    mb.t += [(n, n + 1, n + 2), (n, n + 2, n + 3)]


mm_bg, mm_blocks = MB(), MB()
quad_xy(mm_bg, MMX, MMY, MM / 2 + 0.005, (10, 10, 14))
quad_xy(mm_bg, MMX, MMY, MM / 2, (70, 72, 78))
for (x0, z0, i, j) in block_rects_for_map:
    quad_xy(mm_blocks, MMX + ((x0 + S_BLOCK / 2) / WORLD - 0.5) * MM, MMY + ((z0 + S_BLOCK / 2) / WORLD - 0.5) * MM,
            S_BLOCK / WORLD * MM / 2, (80, 140, 80) if (i, j) in parks else (125, 125, 120))
ui(model=mm_bg.mesh(), double_sided=True, z=0)
ui(model=mm_blocks.mesh(), double_sided=True, z=-0.01)
mm_player = ui(model="quad", scale=0.012, position=(MMX, MMY, -0.03), color=rgb(255, 255, 255))
mm_dots = [ui(model="quad", scale=0.01, position=(MMX, MMY, -0.02), color=rgb(60, 90, 255), enabled=False)
           for _ in range(10)]


def mm_pos(x, z):
    return (MMX + (x / WORLD - 0.5) * MM, MMY + (z / WORLD - 0.5) * MM)


fx_free, fx_live = [], []
for _ in range(140):
    fx_free.append([Entity(model="cube", enabled=False), 0.0, 0.0, 0.0, 0.0, 1.0, 1.0, 0.0])
tr_pool = [[Entity(model="cube", enabled=False, color=rgb(255, 235, 120)), 0.0] for _ in range(6)]
tr_idx = 0
decal_pool = [[Entity(model="plane", enabled=False), 0.0] for _ in range(80)]
decal_idx = 0
pick_pool = [[Entity(model="cube", enabled=False, scale=(0.5, 0.12, 0.3), color=rgb(50, 190, 80)), 0, False] for _ in range(14)]
t_game = 0.0
spawn_timer = 0.0
cop_timer = 0.0
hud_timer = 0.0
audio_t = 0.0
skid_t = 0.0
skid_on = False
step_sign = 1.0
was_air = False
prev_stars = 0
prev_hp = 100.0
flash_a = 0.0
hurt_cd = 0.0


def spawn_fx(x, y, z, vx, vy, vz, life, size, col, grav=0.0):
    if not fx_free:
        return
    p = fx_free.pop()
    e = p[0]
    e.position = (x, y, z)
    e.scale = size
    e.color = col
    e.enabled = True
    p[1], p[2], p[3], p[4], p[5], p[6], p[7] = vx, vy, vz, life, life, size, grav
    fx_live.append(p)


def update_fx(dt):
    for p in fx_live[:]:
        p[4] -= dt
        e = p[0]
        if p[4] <= 0:
            e.enabled = False
            fx_live.remove(p)
            fx_free.append(p)
            continue
        p[2] -= p[7] * dt
        e.x += p[1] * dt
        e.y += p[2] * dt
        e.z += p[3] * dt
        e.scale = p[6] * (p[4] / p[5])
    for t in tr_pool:
        if t[1] > 0:
            t[1] -= dt
            if t[1] <= 0:
                t[0].enabled = False
    for d in decal_pool:
        if d[1] > 0:
            d[1] -= dt
            if d[1] <= 0:
                d[0].enabled = False
    for pk in pick_pool:
        if pk[2]:
            pk[0].rotation_y += 120 * dt


def spawn_decal(x, z, sx, sz, rot, col, life, y=0.09):
    global decal_idx
    d = decal_pool[decal_idx]
    decal_idx = (decal_idx + 1) % len(decal_pool)
    e = d[0]
    e.position = (x, y, z)
    e.scale = (sx, 1, sz)
    e.rotation_y = rot
    e.color = col
    e.enabled = True
    d[1] = life


def spawn_pickup(x, z, amt):
    for pk in pick_pool:
        if not pk[2]:
            pk[0].position = (x, 0.5, z)
            pk[0].enabled = True
            pk[1], pk[2] = amt, True
            return


def tracer3d(x0, y0, z0, x1, y1, z1):
    global tr_idx
    dx, dy, dz = x1 - x0, y1 - y0, z1 - z0
    ln = math.sqrt(dx * dx + dy * dy + dz * dz)
    if ln < 0.2:
        return
    t = tr_pool[tr_idx]
    tr_idx = (tr_idx + 1) % len(tr_pool)
    e = t[0]
    e.position = ((x0 + x1) / 2, (y0 + y1) / 2, (z0 + z1) / 2)
    e.scale = (0.03, 0.03, ln)
    e.rotation_y = math.degrees(math.atan2(dx, dz))
    e.rotation_x = -math.degrees(math.atan2(dy, math.hypot(dx, dz)))
    e.color = Color(1, 1, 1, 0.4)
    e.enabled = True
    t[1] = 0.05

def tracer(x, y, z, h, length):
    sh, ch = math.sin(math.radians(h)), math.cos(math.radians(h))
    sx, sz = x + sh * 0.9, z + ch * 0.9
    tx, ty, tz = player.x, player.y + 1.3, player.z
    spawn_bullet(sx, y, sz, tx - sx, ty - y, tz - sz, "cop")

def scare(x, z):
    for pd in peds:
        if abs(pd.x - x) < 45 and abs(pd.z - z) < 45:
            pd.state = "flee"
            pd.t = 5
            pd.h = math.degrees(math.atan2(pd.x - x, pd.z - z)) + random.uniform(-30, 30)


def add_wanted(level): player.stars = cl(max(player.stars, level), 0, 6); player.crime_t = 0


def hurt_player(dmg):
    if not player.alive:
        return
    if player.car:
        player.car.hp -= dmg
        player.hp -= dmg * 0.3
    else:
        player.hp -= dmg


def blood_burst(x, z):
    for _ in range(9):
        a = random.uniform(0, TAU)
        sp = random.uniform(1.5, 4.5)
        spawn_fx(x, 1.0, z, math.cos(a) * sp, random.uniform(2, 5), math.sin(a) * sp, 0.6, 0.16, rgb(150, 20, 20), 14)


def kill_ped(pd, by_player=True):
    if pd in peds:
        peds.remove(pd)
    pd.call_t = 0.0
    pd.root.enabled = True
    pd.vis = True
    pd.root.rotation_x = 85
    pd.root.y = 0.2
    pd.person.shadow.enabled = False
    pd.person.gun.enabled = False
    corpses.append([pd, 10.0, ped_free])
    blood_burst(pd.x, pd.z)
    spawn_decal(pd.x, pd.z, 0.7, 0.7, random.uniform(0, 360), rgb(120, 18, 18), 20)
    if random.random() < 0.5:
        spawn_pickup(pd.x, pd.z, random.randint(20, 120))
    if by_player:
        report_crime(pd.x, pd.z, max(2, player.stars), ["face", "clothes", "weapon"])


def kill_cop(cp):
    if not hasattr(wanted, "apply_crime"):
        patch_wanted_object()
    if cp in cops:
        cops.remove(cp)
    cp.root.rotation_x = 85
    cp.root.y = 0.2
    cp.person.shadow.enabled = False
    cp.person.gun.enabled = False
    corpses.append([cp, 10.0, cop_free])
    blood_burst(cp.x, cp.z)
    spawn_decal(cp.x, cp.z, 0.7, 0.7, random.uniform(0, 360), rgb(120, 18, 18), 20)
    spawn_pickup(cp.x, cp.z, random.randint(50, 200))
    wanted.apply_crime(cp.x, cp.z, max(3, player.stars + 1), ["face", "clothes", "weapon"])


def release_car(c):
    if c in cars:
        cars.remove(c)
    c.active = False
    c.driver = None
    c.root.enabled = False
    car_free[c.kind].append(c)


def release_cop(cp):
    if cp in cops:
        cops.remove(cp)
    cp.active = False
    cp.root.enabled = False
    cop_free.append(cp)


def release_ped(pd):
    if pd in peds:
        peds.remove(pd)
    pd.active = False
    pd.root.enabled = False
    ped_free.append(pd)


def explode(c):
    for _ in range(22):
        a = random.uniform(0, TAU)
        sp = random.uniform(1, 9)
        spawn_fx(c.x, 1.0, c.z, math.cos(a) * sp, random.uniform(1, 7), math.sin(a) * sp, random.uniform(0.5, 1.0),
                 random.uniform(0.5, 1.3), random.choice([rgb(255, 170, 40), rgb(255, 90, 30), rgb(255, 220, 90)]), 4)
    for _ in range(14):
        a = random.uniform(0, TAU)
        sp = random.uniform(0.5, 3)
        spawn_fx(c.x, 1.5, c.z, math.cos(a) * sp, random.uniform(2, 6), math.sin(a) * sp, random.uniform(1.0, 1.8),
                 random.uniform(1.2, 2.4), rgb(60, 60, 62), -1.5)
    for _ in range(10):
        a = random.uniform(0, TAU)
        sp = random.uniform(3, 10)
        spawn_fx(c.x, 1.0, c.z, math.cos(a) * sp, random.uniform(3, 9), math.sin(a) * sp, 1.2, 0.35, rgb(*c.col), 18)
    spawn_decal(c.x, c.z, 4, 4, random.uniform(0, 360), rgb(22, 22, 22), 40)
    if player.car is c:
        player.car = None
        player.x, player.z = c.x, c.z
        player.root.enabled = True
        player.hp -= 35
    elif player.alive and math.hypot(player.x - c.x, player.z - c.z) < 5:
        player.hp -= 40
    was_police = c.kind == "police"
    release_car(c)
    for pd in peds[:]:
        if math.hypot(pd.x - c.x, pd.z - c.z) < 5:
            kill_ped(pd, False)
    for cp in cops[:]:
        if math.hypot(cp.x - c.x, cp.z - c.z) < 5:
            kill_cop(cp)
    report_crime(c.x, c.z, max(4 if was_police else 3, player.stars), ["weapon", "face", "clothes"])


def die():
    player.alive = False
    player.dead_t = 3.5
    if player.car:
        player.car.driver = None
        player.car = None
    player.root.enabled = True
    player.root.rotation_x = 85
    player.root.y = 0.2
    player.person.shadow.enabled = False
    hud_wasted.enabled = True
    for b in bullets_live[:]:
        kill_bullet(b)


def spawn_player_car():
    """Личная тачка рядом с точкой возрождения, быстрее вертолёта."""
    global mine
    if mine in cars:
        cars.remove(mine)
    if mine not in car_free["civ"]:
        car_free["civ"].append(mine)

    best = None
    for d in range(4):
        for off in (6.8, -6.8):
            if d in (0, 2):
                j = nearest_road_j(player.z)
                x = player.x + 8
                z = j * P + ROAD_C + off
            else:
                i = nearest_road_i(player.x)
                x = i * P + ROAD_C + off
                z = player.z + 8
            x = cl(x, 10, WORLD - 10)
            z = cl(z, 10, WORLD - 10)
            if hits_building(x, z, 2.0):
                continue
            if any(abs(c.x - x) < 6 and abs(c.z - z) < 6 for c in cars):
                continue
            dd = math.hypot(x - player.x, z - player.z)
            if best is None or dd < best[0]:
                best = (dd, x, z, d)
    if best is None:
        x, z, d = player.x + 6, player.z, 0
    else:
        _, x, z, d = best

    car_free["civ"].remove(mine)
    mine.reset(x, z, DIR_H[d])
    mine.maxv = 52
    mine.cruise = 20
    mine.driver = None
    cars.append(mine)

def respawn():
    global heli_down_flag
    money = int(player.money * 0.9)
    player.reset()
    player.money = money
    hud_wasted.enabled = False

    heli_down_flag = False
    globals()["_fbi_on"] = False

    wanted.level = 0
    wanted.state = "none"
    wanted.evidence.clear()
    wanted.alert_radius = 0.0
    wanted.hot_timer = 0.0
    wanted.search_timer = 0.0
    wanted.pending = 0
    wanted.alert_center = [player.x, player.z]
    wanted.last_seen_pos = [player.x, player.z]
    player.stars = 0
    player.crime_t = 0.0
    player.hot_timer = 0.0

    for b in bullets_live[:]:
        kill_bullet(b)
    for pd in peds:
        pd.call_t = 0.0

    for cp in cops[:]:
        release_cop(cp)
    for c in cars[:]:
        if c.kind == "police" or getattr(c, "fbi", False):
            if c in fbi_cars:
                fbi_cars.remove(c)
            release_car(c)
    for h in helis[:]:
        release_heli(h)

    for co in corpses[:]:
        corpses.remove(co)
        co[0].active = False
        co[0].root.enabled = False
        co[2].append(co[0])

    spawn_player_car()
    cam_pos[0], cam_pos[2] = player.x, player.z

def road_spot(mind, maxd):
    for _ in range(25):
        a, d = random.uniform(0, TAU), random.uniform(mind, maxd)
        x = cl(player.x + math.cos(a) * d, 10, WORLD - 10)
        z = cl(player.z + math.sin(a) * d, 10, WORLD - 10)
        dr = random.randrange(4)
        if dr in (0, 2):
            rj = int(cl(round((z - ROAD_C) / P), 0, N - 1))
            z = rj * P + ROAD_C + (-LANE if dr == 0 else LANE)
        else:
            ri = int(cl(round((x - ROAD_C) / P), 0, N - 1))
            x = ri * P + ROAD_C + (LANE if dr == 1 else -LANE)
        if math.hypot(x - player.x, z - player.z) < mind:
            continue
        if any(abs(c.x - x) < 10 and abs(c.z - z) < 10 for c in cars):
            continue
        return x, z, dr
    return None


def spawn_civ(mind, maxd, parked=False):
    pool = car_free["civ"]
    if not pool:
        return
    spot = road_spot(mind, maxd)
    if not spot:
        return
    x, z, d = spot
    if parked:
        along = x if d in (0, 2) else z
        if along % P < RW + 8:
            return
        if d in (0, 2):
            z = (round((z - ROAD_C) / P) * P + ROAD_C) + (-6.8 if d == 0 else 6.8)
        else:
            x = (round((x - ROAD_C) / P) * P + ROAD_C) + (6.8 if d == 1 else -6.8)
    c = pool.pop(random.randrange(len(pool)))
    c.reset(x, z, DIR_H[d])
    c.dir = d
    c.driver = None if parked else "ai"
    cars.append(c)


def spawn_ped(mind, maxd):
    if not ped_free:
        return
    for _ in range(15):
        a, d = random.uniform(0, TAU), random.uniform(mind, maxd)
        x, z = player.x + math.cos(a) * d, player.z + math.sin(a) * d
        if not (6 < x < WORLD - 6 and 6 < z < WORLD - 6) or hits_building(x, z, 1.0):
            continue
        pd = ped_free.pop()
        pd.activate(x, z)
        peds.append(pd)
        return


def physics(c, dt, throttle, steer, handbrake=False):
    if throttle > 0:
        c.v += (18 if c.v >= 0 else 34) * throttle * dt
    elif throttle < 0:
        c.v -= (34 if c.v > 0 else 12) * (-throttle) * dt
    c.v -= c.v * 0.4 * dt

    drift_active = handbrake and abs(c.v) > 6
    if drift_active:
        c.v *= max(0.0, 1 - 0.6 * dt)
        steer_mult = 2.4
        grip_loss = 0.55
    else:
        if handbrake:
            c.v *= max(0.0, 1 - 2.0 * dt)
        steer_mult = 1.0
        grip_loss = 0.0

    c.v = cl(c.v, -8, c.maxv)
    if abs(c.v) < 0.2 and throttle == 0:
        c.v = 0

    raw_turn = steer * 75 * dt * cl(c.v / 6, -1, 1) * (1 - 0.5 * min(1, abs(c.v) / 35))
    c.h += raw_turn * steer_mult

    if drift_active:
        c.drift_angle = getattr(c, "drift_angle", 0.0)
        c.drift_angle += (raw_turn * steer_mult * grip_loss - c.drift_angle) * min(1, 4 * dt)
    else:
        c.drift_angle = getattr(c, "drift_angle", 0.0) * max(0.0, 1 - 6 * dt)

def move_car(c, dt):
    ox, oz, oh = c.x, c.z, c.h
    da = getattr(c, "drift_angle", 0.0)
    move_h = c.h + da * 0.6
    sh, ch = math.sin(math.radians(move_h)), math.cos(math.radians(move_h))
    c.x = cl(c.x + sh * c.v * dt, 4, WORLD - 4)
    c.z = cl(c.z + ch * c.v * dt, 4, WORLD - 4)

    for px, pz in c.pts((-1.7, 0, 1.7)):
        if hits_building(px, pz, 1.05):
            c.x, c.z, c.h = ox, oz, oh
            c.drift_angle = 0.0
            if abs(c.v) > 6 and c.crash_cd <= 0:
                c.crash_cd = 0.3
                for _ in range(5):
                    spawn_fx(px, 0.8, pz, random.uniform(-3, 3), random.uniform(1, 4), random.uniform(-3, 3),
                             0.4, 0.15, rgb(255, 210, 90), 10)
            if abs(c.v) > 12:
                c.hp -= (abs(c.v) - 10) * 2.2
            c.v = -c.v * 0.3
            c.stuck += 0.3
            break

    if abs(da) > 0.5 and abs(c.v) > 8:
        c.smoke_t = getattr(c, "smoke_t", 0.0)
        if c.smoke_t <= 0:
            c.smoke_t = 0.05
            sh2, ch2 = math.sin(math.radians(c.h)), math.cos(math.radians(c.h))
            for side in (-1, 1):
                wx = c.x - sh2 * 1.4 + ch2 * side * 0.9
                wz = c.z - ch2 * 1.4 - sh2 * side * 0.9
                spawn_decal(wx, wz, 0.35, 1.0, c.h + da * 30, rgb(20, 20, 22), 12, 0.085)
                spawn_fx(wx, 0.25, wz, random.uniform(-1, 1), random.uniform(0.5, 1.5), random.uniform(-1, 1),
                         0.5, 0.6, rgb(200, 200, 205), -0.8)


def ai_drive(c, dt):
    c.h += cl(adiff(DIR_H[c.dir], c.h), -240 * dt, 240 * dt)
    c.honk_cd -= dt
    sh, ch = math.sin(math.radians(c.h)), math.cos(math.radians(c.h))
    blocked = False
    if c.ghost > 0:
        c.ghost -= dt
    else:
        for o in cars:
            if o is c:
                continue
            dx, dz = o.x - c.x, o.z - c.z
            if abs(dx) > 25 or abs(dz) > 25:
                continue
            f, l = dx * sh + dz * ch, dx * ch - dz * sh
            if 0 < f < 14 and abs(l) < 3.2:
                if math.cos(math.radians(o.h - c.h)) > 0.5 or o.driver in (None, "player"):
                    blocked = True
                    break
        if not blocked and player.alive and player.car is None:
            dx, dz = player.x - c.x, player.z - c.z
            f, l = dx * sh + dz * ch, dx * ch - dz * sh
            if 0 < f < 15 and abs(l) < 2.4:
                blocked = True
    if blocked:
        c.stuck += dt
        if c.stuck > 3:
            c.ghost, c.stuck = 2.5, 0
    else:
        c.stuck = max(0, c.stuck - dt)
    c.v += cl((0 if blocked else c.cruise) - c.v, -25 * dt, 11 * dt)
    px, pz = c.x, c.z
    c.x += DIR_X[c.dir] * c.v * dt
    c.z += DIR_Z[c.dir] * c.v * dt
    if c.dir in (0, 2):
        tz = round((c.z - ROAD_C) / P) * P + ROAD_C + (-LANE if c.dir == 0 else LANE)
        c.z += (tz - c.z) * min(1, 5 * dt)
    else:
        tx = round((c.x - ROAD_C) / P) * P + ROAD_C + (LANE if c.dir == 1 else -LANE)
        c.x += (tx - c.x) * min(1, 5 * dt)
    if (c.dir == 0 and c.x > WORLD - 25) or (c.dir == 2 and c.x < 25) or \
            (c.dir == 1 and c.z > WORLD - 25) or (c.dir == 3 and c.z < 25):
        c.dir = (c.dir + 2) % 4
        c.nox = 40
        return
    c.nox -= abs(c.v) * dt
    if c.nox <= 0 and (c.x != px or c.z != pz):
        if c.dir in (0, 2):
            ni = round((c.x - ROAD_C) / P)
            cx = ni * P + ROAD_C
            if (px - cx) * (c.x - cx) <= 0 and 0 <= ni < N and random.random() < 0.35:
                rj = round((c.z - ROAD_C) / P)
                opts = ([1] if rj < N - 1 else []) + ([3] if rj > 0 else [])
                if opts:
                    c.dir = random.choice(opts)
                    c.x = cx + (LANE if c.dir == 1 else -LANE)
                    c.nox = 25
        else:
            nj = round((c.z - ROAD_C) / P)
            cz = nj * P + ROAD_C
            if (pz - cz) * (c.z - cz) <= 0 and 0 <= nj < N and random.random() < 0.35:
                ri = round((c.x - ROAD_C) / P)
                opts = ([0] if ri < N - 1 else []) + ([2] if ri > 0 else [])
                if opts:
                    c.dir = random.choice(opts)
                    c.z = cz + (-LANE if c.dir == 0 else LANE)
                    c.nox = 25


def road_lane_x(i, d):
    return i * P + ROAD_C + (LANE if d == 1 else -LANE)


def road_lane_z(j, d):
    return j * P + ROAD_C + (-LANE if d == 0 else LANE)


def nearest_road_i(x):
    return int(cl(round((x - ROAD_C) / P), 0, N - 1))


def nearest_road_j(z):
    return int(cl(round((z - ROAD_C) / P), 0, N - 1))


def cop_route_target(c, tx, tz):
    horizontal = c.dir in (0, 2)
    if horizontal:
        j = nearest_road_j(c.z)
        cz = j * P + ROAD_C
        if abs(c.z - cz) > RW * 0.6:
            i = nearest_road_i(c.x)
            return road_lane_x(i, 1 if tz > c.z else 3), c.z, (1 if tz > c.z else 3)
        ni = nearest_road_i(tx)
        cx = ni * P + ROAD_C
        if abs(c.x - cx) < 6 and abs(tz - cz) > P * 0.5:
            nd = 1 if tz > cz else 3
            return cx + (LANE if nd == 1 else -LANE), cz, nd
        nd = 0 if tx > c.x else 2
        return tx, road_lane_z(j, nd), nd
    else:
        i = nearest_road_i(c.x)
        cx = i * P + ROAD_C
        if abs(c.x - cx) > RW * 0.6:
            j = nearest_road_j(c.z)
            return c.x, road_lane_z(j, 0 if tx > c.x else 2), (0 if tx > c.x else 2)
        nj = nearest_road_j(tz)
        cz = nj * P + ROAD_C
        if abs(c.z - cz) < 6 and abs(tx - cx) > P * 0.5:
            nd = 0 if tx > cx else 2
            return cx, cz + (-LANE if nd == 0 else LANE), nd
        nd = 1 if tz > c.z else 3
        return road_lane_x(i, nd), tz, nd

def cop_drive(c, dt):
    tx, tz = police_target()
    pdist = math.hypot(player.x - c.x, player.z - c.z)
    direct = pdist < 30 and clear_line(c.x, c.z, player.x, player.z)

    if pdist < 13 and player.car is None and not c.deployed and player.alive and abs(c.v) < 4:
        c.deployed = True
        side = (math.cos(math.radians(c.h)), -math.sin(math.radians(c.h)))
        for s in (-1, 1):
            if cop_free:
                cp = cop_free.pop()
                cp.activate(c.x + side[0] * 2.6 * s, c.z + side[1] * 2.6 * s)
                cops.append(cp)
        c.driver = None
        c.v = 0
        return

    if c.rev > 0:
        c.rev -= dt
        drive_step(c, dt, -1.0, c.rev_steer)
        return

    if direct:
        gx, gz = player.x, player.z
        if player.car:
            lead = cl(pdist / 20, 0.3, 1.5)
            gx += math.sin(math.radians(player.car.h)) * player.car.v * lead * 0.5
            gz += math.cos(math.radians(player.car.h)) * player.car.v * lead * 0.5
    else:
        gx, gz, nd = cop_route_target(c, tx, tz)
        if abs(adiff(DIR_H[nd], c.h)) < 60:
            c.dir = nd

    dx, dz = gx - c.x, gz - c.z
    dist = math.hypot(dx, dz)
    diff = adiff(math.degrees(math.atan2(dx, dz)), c.h)

    c.maxv = 34 + player.stars * 3.5
    throttle = 1.0
    if abs(diff) > 75 and c.v > 10:
        throttle = -0.35
    elif abs(diff) > 32:
        throttle = 0.6
    if dist < 8 and not player.car:
        throttle = -0.2

    ok = drive_step(c, dt, throttle, cl(diff / 24, -1, 1))

    if ok and abs(c.v) < 1.8 and dist > 8:
        c.stuck += dt
        if c.stuck > 0.6:
            c.rev, c.stuck = 1.1, 0.0
            c.rev_steer = random.choice((-1, 1))
    else:
        c.stuck = max(0.0, c.stuck - dt)

def car_collisions():
    n = len(cars)
    for i in range(n):
        a = cars[i]
        for j in range(i + 1, n):
            b = cars[j]
            if a.driver == "ai" and b.driver == "ai":
                continue
            if abs(a.x - b.x) > 6 or abs(a.z - b.z) > 6:
                continue
            best = None
            for p in a.pts((-1.4, 0, 1.4)):
                for q in b.pts((-1.4, 0, 1.4)):
                    d = math.hypot(q[0] - p[0], q[1] - p[1])
                    if d < 2.1 and (best is None or d < best[0]):
                        best = (d, p, q)
            if best:
                d, p, q = best
                if d < 0.01:
                    nx, nz, d = 1, 0, 0.01
                else:
                    nx, nz = (q[0] - p[0]) / d, (q[1] - p[1]) / d
                push = (2.1 - d) / 2
                a.x -= nx * push
                a.z -= nz * push
                b.x += nx * push
                b.z += nz * push
                imp = abs(a.v) + abs(b.v)
                a.v *= 0.75
                b.v *= 0.75
                if imp > 8 and a.crash_cd <= 0:
                    a.crash_cd = 0.3
                    for _ in range(5):
                        spawn_fx(p[0], 0.8, p[1], random.uniform(-3, 3), random.uniform(1, 4), random.uniform(-3, 3),
                                 0.4, 0.15, rgb(255, 210, 90), 10)
                if imp > 12:
                    dmg = (imp - 10) * 1.6
                    a.hp -= dmg
                    b.hp -= dmg


def car_impacts(c):
    if abs(c.v) < 4.5:
        return
    pts = c.pts()
    by_player = c.driver == "player"
    for pd in peds[:]:
        if abs(pd.x - c.x) < 4 and abs(pd.z - c.z) < 4:
            if any(math.hypot(pd.x - px, pd.z - pz) < 1.3 for px, pz in pts):
                kill_ped(pd, by_player)
    for cp in cops[:]:
        if abs(cp.x - c.x) < 4 and abs(cp.z - c.z) < 4:
            if any(math.hypot(cp.x - px, cp.z - pz) < 1.3 for px, pz in pts):
                cp.hp -= 90
                if cp.hp <= 0:
                    kill_cop(cp)
    if not by_player and player.alive and player.car is None and player.hit_cd <= 0:
        if any(math.hypot(player.x - px, player.z - pz) < 1.4 for px, pz in pts):
            player.hp -= abs(c.v) * 2.2
            player.hit_cd = 0.6


def clear_line(ox, oz, tx, tz):
    d = math.hypot(tx - ox, tz - oz)
    steps = int(d / 1.5)
    for s in range(1, steps):
        t = s / max(1, steps)
        if hits_building(ox + (tx - ox) * t, oz + (tz - oz) * t, 0.1):
            return False
    return True


def aim_ray():
    """Реальный луч прицела: откуда смотрим и куда направлен центр экрана."""
    sy = math.sin(math.radians(cam_yaw))
    cy = math.cos(math.radians(cam_yaw))
    cp = math.cos(math.radians(cam_pitch))
    sp = math.sin(math.radians(cam_pitch))
    c = player.car
    dist = (8.5 + abs(c.v) * 0.12) if c else 4.2
    ox = cam_pos[0] - sy * cp * dist
    oy = cam_pos[1] + sp * dist
    oz = cam_pos[2] - cy * cp * dist
    dx, dy, dz = sy * cp, -sp, cy * cp
    return ox, oy, oz, dx, dy, dz


def angle_to_target(ox, oy, oz, dx, dy, dz, tx, ty, tz):
    vx, vy, vz = tx - ox, ty - oy, tz - oz
    ln = math.sqrt(vx * vx + vy * vy + vz * vz)
    if ln < 0.001:
        return 180.0, 0.0
    dot = cl((vx * dx + vy * dy + vz * dz) / ln, -1.0, 1.0)
    return math.degrees(math.acos(dot)), ln

BULLET_SPEED = 190.0
bullets_live = []
bullets_free = []


def init_bullets():
    if bullets_free or bullets_live:
        return
    for _ in range(70):
        e = Entity(model="cube", scale=(0.07, 0.07, 0.9), color=rgb(255, 225, 40), enabled=False)
        bullets_free.append([e, 0.0, 0.0, 0.0, 0.0, "player"])


def gun_muzzle_pos():
    h = math.radians(player.h)
    sh, ch = math.sin(h), math.cos(h)
    rx, rz = ch, -sh
    return (player.x + rx * 0.43 + sh * 0.95,
            player.y + 1.52,
            player.z + rz * 0.43 + ch * 0.95)


def spawn_bullet(x, y, z, dx, dy, dz, owner="player"):
    init_bullets()
    if not bullets_free:
        return
    b = bullets_free.pop()
    e = b[0]
    ln = math.sqrt(dx * dx + dy * dy + dz * dz)
    if ln < 1e-6:
        bullets_free.append(b)
        return
    dx, dy, dz = dx / ln, dy / ln, dz / ln
    b[1], b[2], b[3] = dx * BULLET_SPEED, dy * BULLET_SPEED, dz * BULLET_SPEED
    b[4] = 1.5
    b[5] = owner
    e.position = (x, y, z)
    e.rotation_y = math.degrees(math.atan2(dx, dz))
    e.rotation_x = -math.degrees(math.atan2(dy, math.hypot(dx, dz)))
    e.color = rgb(255, 225, 40) if owner == "player" else rgb(255, 130, 40)
    e.enabled = True
    bullets_live.append(b)
    spawn_fx(x, y, z, 0, 0, 0, 0.05, 0.22, rgb(255, 245, 160))


def kill_bullet(b):
    b[0].enabled = False
    if b in bullets_live:
        bullets_live.remove(b)
    bullets_free.append(b)


def update_bullets(dt):
    for b in bullets_live[:]:
        b[4] -= dt
        e = b[0]
        if b[4] <= 0:
            kill_bullet(b)
            continue
        hit = False
        for _ in range(3):
            sdt = dt / 3.0
            nx, ny, nz = e.x + b[1] * sdt, e.y + b[2] * sdt, e.z + b[3] * sdt
            if ny <= 0.05 or hits_building(nx, nz, 0.12):
                for _ in range(3):
                    spawn_fx(nx, max(0.1, ny), nz, random.uniform(-2, 2), random.uniform(1, 3),
                             random.uniform(-2, 2), 0.25, 0.1, rgb(255, 220, 120), 12)
                hit = True
                break
            e.position = (nx, ny, nz)
            if b[5] == "player":
                for pd in peds[:]:
                    if abs(pd.x - nx) < 1.0 and abs(pd.z - nz) < 1.0 and 0.2 < ny < 2.2:
                        kill_ped(pd)
                        hit = True
                        break
                if hit:
                    break
                for cp in cops[:]:
                    if abs(cp.x - nx) < 1.0 and abs(cp.z - nz) < 1.0 and 0.2 < ny < 2.2:
                        cp.hp -= 25
                        blood_burst(cp.x, cp.z)
                        report_crime(cp.x, cp.z, max(3, player.stars), ["weapon", "face", "clothes"])
                        if cp.hp <= 0:
                            kill_cop(cp)
                        hit = True
                        break
                if hit:
                    break
                for hl in helis[:]:
                    if hl.hp > 0 and math.hypot(hl.x - nx, hl.z - nz) < 3.2 and abs(hl.y - ny) < 2.8:
                        hl.hp -= 25
                        for _ in range(5):
                            spawn_fx(nx, ny, nz, random.uniform(-4, 4), random.uniform(-2, 3),
                                     random.uniform(-4, 4), 0.4, 0.18, rgb(255, 210, 90), 8)
                        hit = True
                        break
                if hit:
                    break
                for c in cars[:]:
                    if c.driver == "player":
                        continue
                    if abs(c.x - nx) < 2.4 and abs(c.z - nz) < 2.6 and 0.2 < ny < 2.4:
                        c.hp -= 14
                        for _ in range(4):
                            spawn_fx(nx, ny, nz, random.uniform(-3, 3), random.uniform(1, 4),
                                     random.uniform(-3, 3), 0.35, 0.14, rgb(255, 210, 90), 10)
                        report_crime(c.x, c.z, max(1, player.stars), ["weapon", "face", "clothes"])
                        if c.hp <= 0:
                            explode(c)
                        hit = True
                        break
            else:
                if player.alive and abs(player.x - nx) < 0.9 and abs(player.z - nz) < 0.9 \
                        and player.y < ny < player.y + 2.1:
                    hurt_player(8)
                    hit = True
            if hit:
                break
        if hit:
            kill_bullet(b)

def shoot():
    mx, my, mz = gun_muzzle_pos()
    rox, roy, roz, rdx, rdy, rdz = aim_ray()

    best, aim_point = None, None
    cands = [(o, 1.2, 7.0) for o in peds] + [(o, 1.2, 7.0) for o in cops] + \
            [(o, 1.0, 7.0) for o in cars if o.driver != "player"] + \
            [(o, o.y, 9.0) for o in helis if o.hp > 0]
    for o, ty, limit in cands:
        ang, ln = angle_to_target(rox, roy, roz, rdx, rdy, rdz, o.x, ty, o.z)
        if ln > 170 or ang > limit:
            continue
        score = ang + ln * 0.03
        if best is None or score < best:
            best, aim_point = score, (o.x, ty, o.z)

    if aim_point is None:
        aim_point = (rox + rdx * 130, roy + rdy * 130, roz + rdz * 130)

    dx, dy, dz = aim_point[0] - mx, aim_point[1] - my, aim_point[2] - mz
    dx += random.uniform(-0.7, 0.7)
    dy += random.uniform(-0.7, 0.7)
    dz += random.uniform(-0.7, 0.7)
    spawn_bullet(mx, my, mz, dx, dy, dz, "player")

    snd.play("gun", 0.85, random.uniform(0.95, 1.08))
    scare(player.x, player.z)
    report_crime(player.x, player.z, max(1, player.stars), ["weapon", "face", "clothes"])

def try_exit_car():
    c = player.car
    if abs(c.v) > 8:
        return
    rx, rz = math.cos(math.radians(c.h)), -math.sin(math.radians(c.h))
    fx, fz = math.sin(math.radians(c.h)), math.cos(math.radians(c.h))
    for sx, sz in ((rx * 2.3, rz * 2.3), (-rx * 2.3, -rz * 2.3), (-fx * 3.2, -fz * 3.2)):
        if not hits_building(c.x + sx, c.z + sz, 0.6):
            player.x, player.z = c.x + sx, c.z + sz
            player.y, player.vy = 0.0, 0.0
            c.driver = None
            player.car = None
            player.root.enabled = True
            return


def try_enter_car():
    best, bd = None, 4.0
    for c in cars:
        d = min(math.hypot(player.x - px, player.z - pz) for px, pz in c.pts())
        if d < bd:
            best, bd = c, d
    if not best:
        return
    old_car = player.car
    if best.driver == "ai":
        rx, rz = math.cos(math.radians(best.h)), -math.sin(math.radians(best.h))
        if ped_free:
            pd = ped_free.pop()
            pd.activate(best.x - rx * 2.3, best.z - rz * 2.3)
            pd.state, pd.t = "flee", 6
            peds.append(pd)
        wanted.commit_crime(best.x, best.z, "carjack", ["car", "face"])
    elif best.driver == "cop":
        wanted.commit_crime(best.x, best.z, "cop_car_steal", ["car", "face"])
    best.driver = "player"
    best.v = 0
    best.root.enabled = True
    player.car = best
    player.root.enabled = False
    player.person.shadow.enabled = False
    if old_car is not best:
        wanted.change_car()


def input(key):
    global mouse_look
    if key == "escape":
        application.quit()
    if key == "f" and player.alive:
        if player.car:
            try_exit_car()
        else:
            try_enter_car()
    if key == "m":
        mouse_look = not mouse_look
        mouse.locked = mouse_look
        mouse.visible = not mouse_look


cam_pivot = Entity()
camera.parent = cam_pivot


def update_camera(dt):
    global cam_yaw, cam_pitch, cam_free, cam_idle
    look = int(bool(held_keys["right arrow"])) - int(bool(held_keys["left arrow"]))
    pit = int(bool(held_keys["down arrow"])) - int(bool(held_keys["up arrow"]))
    mv = mouse.velocity if mouse_look else (0, 0, 0)
    moved = look != 0 or pit != 0 or abs(mv[0]) > 0.0003 or abs(mv[1]) > 0.0003
    cam_yaw += look * 115 * dt + mv[0] * 40
    cam_pitch = cl(cam_pitch + pit * 70 * dt - mv[1] * 40, -75, 70)
    cam_idle = 0.0 if moved else cam_idle + dt
    c = player.car
    heading = c.h if c else player.h
    if held_keys["c"]:
        cam_yaw += adiff(heading, cam_yaw) * min(1, 6 * dt)
    if c:
        if cam_idle > 1.2 and cam_pitch > -5:
            cam_yaw += adiff(c.h, cam_yaw) * min(1, 2.5 * dt)
        tx, ty, tz = c.x, 1.9, c.z
        dist = 8.5 + abs(c.v) * 0.12
        camera.x = 0
        camera.fov += ((85 + abs(c.v) * 0.8) - camera.fov) * min(1, 3 * dt)
    else:
        tx, ty, tz = player.x, player.y + 1.7, player.z
        dist = 4.2
        camera.x = 0.7
        camera.fov += (85 - camera.fov) * min(1, 3 * dt)
    k = min(1, 14 * dt)
    cam_pos[0] += (tx - cam_pos[0]) * k
    cam_pos[1] += (ty - cam_pos[1]) * k
    cam_pos[2] += (tz - cam_pos[2]) * k
    sy, cy = math.sin(math.radians(cam_yaw)), math.cos(math.radians(cam_yaw))
    cp = math.cos(math.radians(cam_pitch))
    while dist > 1.3:
        bx, bz = cam_pos[0] - sy * cp * dist, cam_pos[2] - cy * cp * dist
        by = cam_pos[1] + math.sin(math.radians(cam_pitch)) * dist
        if by < 0.4:
            dist -= 0.5
            continue
        if not hits_building(bx, bz, 0.8):
            break
        dist -= 0.5
    cam_pivot.position = (cam_pos[0], cam_pos[1], cam_pos[2])
    cam_pivot.rotation = (cam_pitch, cam_yaw, 0)
    camera.z = -dist


def update_audio(dt):
    global audio_t
    audio_t -= dt
    if audio_t > 0:
        return
    audio_t = 0.08
    p = player
    if p.car:
        c = p.car
        r = abs(c.v) / max(1.0, c.maxv)
        snd.loop("eng_p", "engine", 0.3 + 0.3 * min(1.0, r), 0.55 + r * 1.9)
    else:
        snd.loop("eng_p", "engine", 0.0)
    movers = [c for c in cars if c.driver in ("ai", "cop") and c.active]
    movers.sort(key=lambda c: (c.x - cam_pos[0]) ** 2 + (c.z - cam_pos[2]) ** 2)
    for k in range(3):
        if k < len(movers):
            c = movers[k]
            snd.loop_at("eng%d" % k, "engine", c.x, c.z, 0.55, 0.55 + min(1.0, abs(c.v) / 30) * 1.6, 70)
        else:
            snd.loop("eng%d" % k, "engine", 0.0)

def police_knows_player():
    if player.stars <= 0:
        return False
    ev = wanted.evidence
    if not ev:
        return True
    if player.car:
        return ("car" in ev) or ("face" in ev) or ("clothes" in ev)
    if ("face" in ev) or ("clothes" in ev):
        return True
    if ("weapon" in ev) and (held_keys["e"] or held_keys["enter"]):
        return True
    return False


def build_wanted_hud():
    global hud_stars, hud_evidence, hud_wstate, hud_wlast
    if globals().get("hud_wstate") is not None:
        return
    for s in globals().get("hud_stars", []):
        s.enabled = False
    for item in globals().get("hud_evidence", []):
        try:
            if isinstance(item, tuple):
                for part in item[1:]:
                    part.enabled = False
            else:
                item.enabled = False
        except Exception:
            pass
    hud_stars = [ui(model="quad", scale=0.04, rotation_z=45,
                    position=(0.60 + k * 0.05, 0.40, -0.02), color=rgb(35, 35, 35)) for k in range(6)]
    names = {"face": "ЛИЦО", "clothes": "ОДЕЖДА", "car": "МАШИНА",
             "weapon": "ОРУЖИЕ", "camera": "КАМЕРА", "duo": "ПАРА"}
    hud_evidence = []
    for i, et in enumerate(WantedSystem.EVIDENCE_TYPES):
        x = 0.60 + i * 0.048
        icon = ui(model="quad", scale=0.018, position=(x, 0.35, -0.02), color=rgb(35, 35, 35))
        lbl = Text(text=names[et], parent=camera.ui, position=(x, 0.325, -0.03),
                   origin=(0, 0), scale=0.42, color=rgb(90, 90, 90))
        hud_evidence.append((et, icon, lbl))
    hud_wstate = Text(text="", parent=camera.ui, position=(0.86, 0.29, -0.03),
                      origin=(0.5, 0), scale=0.7, color=rgb(235, 235, 235))
    hud_wlast = Text(text="", parent=camera.ui, position=(0.86, 0.265, -0.03),
                     origin=(0.5, 0), scale=0.6, color=rgb(180, 180, 180))

def build_police_render():
    global pk_ring, pk_last, pk_lines
    if globals().get("pk_ring") is not None:
        return
    mb = MB()
    seg = 72
    for i in range(seg):
        a0, a1 = TAU * i / seg, TAU * (i + 1) / seg
        r0, r1 = 0.985, 1.0
        p0 = Vec3(math.cos(a0) * r1, 0.13, math.sin(a0) * r1)
        p1 = Vec3(math.cos(a1) * r1, 0.13, math.sin(a1) * r1)
        p2 = Vec3(math.cos(a1) * r0, 0.13, math.sin(a1) * r0)
        p3 = Vec3(math.cos(a0) * r0, 0.13, math.sin(a0) * r0)
        c = tc((255, 215, 40))
        mb.quad(p0, p1, p2, p3, c, c, c, c)
    pk_ring = Entity(model=mb.mesh(), double_sided=True, enabled=False)
    pk_last = Entity(model="cube", scale=(1.1, 2.6, 1.1), color=Color(1, 0.85, 0.1, 0.5), enabled=False)
    pk_lines = [Entity(model="cube", enabled=False) for _ in range(28)]


def update_police_render(dt):
    if globals().get("pk_ring") is None:
        build_police_render()
    pk_ring.enabled = False
    pk_last.enabled = False
    for e in pk_lines:
        e.enabled = False

def update_wanted_hud():
    if globals().get("hud_wstate") is None:
        build_wanted_hud()
    searching = wanted.state in ("lost_contact", "nearby_unseen", "searching")
    pulse = int(t_game * 8) % 2
    slow = int(t_game * 3) % 2
    for k, s in enumerate(hud_stars):
        if k < player.stars:
            if searching:
                s.color = rgb(255, 220, 20) if slow else rgb(60, 55, 20)
            else:
                s.color = rgb(255, 220, 20) if pulse else rgb(215, 175, 0)
        elif player.stars == 0 and player.hot_timer > 0 and k == 0:
            s.color = rgb(120, 95, 10) if pulse else rgb(70, 55, 5)
        else:
            s.color = rgb(35, 35, 35)
    for et, icon, lbl in hud_evidence:
        if et in wanted.evidence:
            icon.color = rgb(*EVIDENCE_COLORS.get(et, (255, 255, 255)))
            lbl.color = rgb(240, 240, 240)
        else:
            icon.color = rgb(35, 35, 35)
            lbl.color = rgb(85, 85, 85)
    ru = {"none": "РОЗЫСКА НЕТ", "searching": "ПОЛИЦИЯ ИЩЕТ", "spotted": "ВАС ВИДЯТ",
          "lost_contact": "КОНТАКТ ПОТЕРЯН", "nearby_unseen": "РЯДОМ, НО НЕ ВИДЯТ"}
    set_text(hud_wstate, "wstate", ru.get(wanted.state, wanted.state))
    if player.stars > 0 and searching:
        set_text(hud_wlast, "wlast", "ПОИСК: %d с" % max(0, int(wanted.search_timer)))
    else:
        set_text(hud_wlast, "wlast", "")

def clean_dev_visuals():
    window.fps_counter.enabled = False
    window.exit_button.visible = False
    window.entity_counter.enabled = False
    window.collider_counter.enabled = False
    try:
        scene.clearColliders()
    except Exception:
        pass
    for e in list(scene.entities):
        if getattr(e, "name", "") in ("collider", "grid", "axis", "debug"):
            e.enabled = False
    for t in tr_pool:
        t[0].enabled = False
        t[1] = 0.0



fbi_cars = []
heli_down_flag = False


def spawn_fbi():
    if not car_free["police"]:
        return
    spot = road_spot(120, 220)
    if not spot:
        return
    x, z, d = spot
    c = car_free["police"].pop()
    c.reset(x, z, DIR_H[d])
    c.driver = "cop"
    c.maxv = 46
    c.cruise = 22
    c.col = (28, 28, 34)
    c.root.color = rgb(28, 28, 34)
    c.fbi = True
    cars.append(c)
    fbi_cars.append(c)
    for _ in range(2):
        if cop_free:
            cp = cop_free.pop()
            cp.activate(x + random.uniform(-3, 3), z + random.uniform(-3, 3))
            cp.hp = 120
            cp.fbi = True
            cp.person.root.color = rgb(60, 60, 70)
            cops.append(cp)


def update_fbi(dt):
    if not heli_down_flag or not player.alive:
        return
    n = sum(1 for c in cars if getattr(c, "fbi", False))
    if n < 6 and random.random() < dt * 0.7:
        spawn_fbi()



witness_marks = []


def init_witness_marks():
    global witness_marks
    if witness_marks:
        return
    for _ in range(24):
        witness_marks.append(Entity(model="cube", scale=(0.22, 0.22, 0.22),
                                    color=rgb(255, 60, 60), enabled=False))


def report_crime(x, z, level, evidence_types=None):
    if not hasattr(wanted, "apply_crime"):
        patch_wanted_object()
    if evidence_types is None:
        evidence_types = ["face", "clothes"]
    if player.car:
        evidence_types = list(evidence_types) + ["car"]
    seen = False
    for pd in peds:
        d = math.hypot(pd.x - x, pd.z - z)
        if d < 38 and clear_line(x, z, pd.x, pd.z):
            seen = True
            if getattr(pd, "call_t", 0.0) <= 0:
                pd.call_t = 3.5
                pd.call_level = level
                pd.call_ev = list(evidence_types)
                pd.call_pos = [x, z]
                pd.state = "flee"
                pd.t = 5
                pd.h = math.degrees(math.atan2(pd.x - x, pd.z - z)) + random.uniform(-25, 25)
    for cp in cops:
        if math.hypot(cp.x - x, cp.z - z) < 70 and clear_line(cp.x, cp.z, x, z):
            seen = True
            wanted.apply_crime(x, z, level, evidence_types)
            break
    if not seen:
        return
    wanted.pending = max(wanted.pending, level)

def update_witnesses(dt):
    init_witness_marks()
    if not hasattr(wanted, "apply_crime"):
        patch_wanted_object()
    used = 0
    for pd in peds:
        ct = getattr(pd, "call_t", 0.0)
        if ct > 0:
            pd.call_t -= dt
            if used < len(witness_marks):
                m = witness_marks[used]
                used += 1
                m.enabled = True
                m.position = (pd.x, 2.6 + math.sin(t_game * 8) * 0.12, pd.z)
                m.rotation_y += 200 * dt
                m.color = rgb(255, 60, 60) if int(t_game * 6) % 2 else rgb(255, 200, 60)
            if pd.call_t <= 0:
                pos = getattr(pd, "call_pos", [pd.x, pd.z])
                lvl = getattr(pd, "call_level", 1)
                ev = getattr(pd, "call_ev", ["face", "clothes"])
                wanted.apply_crime(pos[0], pos[1], lvl, ev)
    for i in range(used, len(witness_marks)):
        witness_marks[i].enabled = False


def police_knows_player():
    if player.stars <= 0:
        return False
    ev = wanted.evidence
    if not ev:
        return True
    if player.car:
        return ("car" in ev) or ("face" in ev) or ("clothes" in ev)
    if ("face" in ev) or ("clothes" in ev):
        return True
    if ("weapon" in ev) and (held_keys["e"] or held_keys["enter"]):
        return True
    return False


def police_target():
    if wanted.state == "spotted":
        return player.x, player.z
    return wanted.last_seen_pos[0], wanted.last_seen_pos[1]

def patch_wanted_object():
    if hasattr(wanted, "apply_crime") and hasattr(wanted, "pending"):
        return

    wanted.pending = getattr(wanted, "pending", 0)

    def apply_crime(x, z, level, evidence_types=None):
        if evidence_types is None:
            evidence_types = ["face", "clothes"]
        wanted.alert_center = [x, z]
        wanted.alert_radius = max(wanted.alert_radius, 140.0 + level * 60)
        for ev in evidence_types:
            wanted.evidence.add(ev)
        wanted.level = min(6, max(wanted.level, level))
        player.stars = max(player.stars, wanted.level)
        player.crime_t = 0.0
        wanted.state = "spotted"
        wanted.last_seen_pos = [player.x, player.z]
        wanted.search_timer = 0.0
        wanted.hot_timer = 30.0
        wanted.pending = 0

    wanted.apply_crime = apply_crime


def build_day_night_ui():
    global day_night_btn, day_night_label
    if day_night_btn is not None:
        return
    day_night_btn = Button(
        parent=camera.ui,
        text="",
        position=(0.80, 0.20),
        scale=(0.16, 0.055),
        color=rgb(45, 48, 60),
        highlight_color=rgb(70, 75, 95),
        pressed_color=rgb(30, 32, 42)
    )
    day_night_label = Text(
        text="ДЕНЬ",
        parent=camera.ui,
        position=(0.80, 0.20),
        origin=(0, 0),
        scale=0.9,
        color=rgb(255, 230, 140)
    )
    day_night_btn.on_click = toggle_day_night


def toggle_day_night():
    global is_night
    is_night = not is_night
    if is_night:
        day_night_label.text = "НОЧЬ"
        day_night_label.color = rgb(150, 190, 255)
        day_night_btn.color = rgb(20, 22, 38)
    else:
        day_night_label.text = "ДЕНЬ"
        day_night_label.color = rgb(255, 230, 140)
        day_night_btn.color = rgb(45, 48, 60)


def collect_sky():
    global sky_ent
    if sky_ent is not None:
        return
    for e in scene.entities:
        if e.__class__.__name__ == "Sky":
            sky_ent = e
            return


def update_day_night(dt):
    global night_blend
    build_day_night_ui()
    collect_sky()

    target = 1.0 if is_night else 0.0
    night_blend += (target - night_blend) * min(1.0, 1.6 * dt)
    k = night_blend

    day_fog = (0.72, 0.80, 0.90)
    night_fog = (0.05, 0.06, 0.12)
    try:
        scene.fog_color = Color(
            day_fog[0] + (night_fog[0] - day_fog[0]) * k,
            day_fog[1] + (night_fog[1] - day_fog[1]) * k,
            day_fog[2] + (night_fog[2] - day_fog[2]) * k,
            1
        )
        scene.fog_density = (90 - 40 * k, 340 - 140 * k)
    except Exception:
        pass

    if sky_ent is not None:
        try:
            sky_ent.color = Color(1 - 0.85 * k, 1 - 0.85 * k, 1 - 0.72 * k, 1)
        except Exception:
            pass

    try:
        from panda3d.core import ColorScaleAttrib
        builtins.base.render.setAttrib(ColorScaleAttrib.make((1 - 0.62 * k, 1 - 0.62 * k, 1 - 0.50 * k, 1)))
    except Exception:
        pass

    if held_keys["n"] and globals().get("_dn_cd", 0.0) <= 0:
        globals()["_dn_cd"] = 0.4
        toggle_day_night()
    globals()["_dn_cd"] = max(0.0, globals().get("_dn_cd", 0.0) - dt)

def update():
    global t_game, spawn_timer, cop_timer, hud_timer, cam_yaw, skid_t, skid_on, step_sign, was_air, prev_stars, prev_hp, flash_a, hurt_cd, heli_timer
    dt = min(time.dt, 0.05)
    t_game += dt
    if not globals().get("_dev_cleaned"):
        clean_dev_visuals()
    globals()["_dev_cleaned"] = True
    hurt_cd -= dt
    p = player
    p.hit_cd -= dt
    update_camera(dt)

    up, down = held_keys["w"], held_keys["s"]
    left, right = held_keys["a"], held_keys["d"]
    shooting = bool(held_keys["e"] or held_keys["enter"])
    skid_on = False

    if p.alive:
        if p.car is None:
            fx, fz = math.sin(math.radians(cam_yaw)), math.cos(math.radians(cam_yaw))
            rx, rz = fz, -fx
            sx_, sz_ = int(bool(right)) - int(bool(left)), int(bool(up)) - int(bool(down))
            mx = sx_ * rx + sz_ * fx
            mz = sx_ * rz + sz_ * fz
            ml = math.hypot(mx, mz)
            speed = 0.0
            if ml > 0:
                speed = 9.0 if (held_keys["left shift"] or held_keys["shift"]) else 5.0
                move_circle(p, mx / ml * speed * dt, mz / ml * speed * dt, 0.45)
                if not shooting:
                    target = math.degrees(math.atan2(mx, mz))
                    p.h += adiff(target, p.h) * min(1, 12 * dt)
                    if sz_ > 0 and cam_idle > 0.8:
                        cam_yaw += adiff(p.h, cam_yaw) * min(1, 1.6 * dt)
            if shooting:
                p.h += adiff(cam_yaw, p.h) * min(1, 18 * dt)
            if held_keys["space"] and p.y <= 0.001:
                p.vy = 7.0
            p.vy -= 22 * dt
            p.y = max(0.0, p.y + p.vy * dt)
            if p.y == 0.0 and p.vy < 0:
                p.vy = 0.0
            was_air = p.y > 0.001
            p.cd -= dt
            if shooting and p.cd <= 0:
                shoot()
                p.cd = 0.16
            p.person.animate(speed, dt, aiming=shooting)
            s_ = math.sin(p.person.phase)
            if speed > 0 and p.y <= 0.001 and s_ * step_sign < 0:
                snd.play("step", 0.35 if speed < 6 else 0.5, random.uniform(0.9, 1.15))
            if s_ != 0:
                step_sign = s_
            p.root.position = (p.x, p.y, p.z)
            p.root.rotation_y = p.h
        else:
            p.x, p.z = p.car.x, p.car.z
            c = p.car
            steer_abs = abs(int(bool(right)) - int(bool(left)))
            if abs(c.v) > 10 and (held_keys["space"] or (steer_abs and abs(c.v) > 24)):
                skid_on = True
                skid_t -= dt
                if skid_t <= 0:
                    skid_t = 0.06
                    sh, ch = math.sin(math.radians(c.h)), math.cos(math.radians(c.h))
                    for side in (-1, 1):
                        wx = c.x - sh * 1.3 + ch * side
                        wz = c.z - ch * 1.3 - sh * side
                        spawn_decal(wx, wz, 0.3, 0.9, c.h, rgb(24, 24, 26), 14, 0.085)
                        spawn_fx(wx, 0.3, wz, random.uniform(-1, 1), random.uniform(0.5, 1.5), random.uniform(-1, 1),
                                 0.6, 0.7, rgb(190, 190, 195), -1.0)
        if p.hp <= 0:
            die()
    else:
        p.dead_t -= dt
        if p.dead_t <= 0:
            respawn()

    for c in cars[:]:
        c.crash_cd -= dt
        if c.driver == "player":
            physics(c, dt, int(bool(up)) - int(bool(down)), int(bool(right)) - int(bool(left)),
                    bool(held_keys["space"]))
            move_car(c, dt)
        elif c.driver == "ai":
            ai_drive(c, dt)
        elif c.driver == "cop":
            cop_drive(c, dt)
        elif abs(c.v) > 0.2:
            physics(c, dt, 0, 0, True)
            move_car(c, dt)
        if c.hp < 35:
            c.smoke_t -= dt
            if c.smoke_t <= 0:
                c.smoke_t = 0.12
                spawn_fx(c.x, 1.3, c.z, random.uniform(-0.5, 0.5), 3.0, random.uniform(-0.5, 0.5), 1.0, 0.9,
                         rgb(70, 70, 72), -0.5)
        if c.l1 is not None and c.driver in ("cop", "player"):
            on = int(t_game * 6) % 2 == 0
            c.l1.color = rgb(255, 40, 40) if on else rgb(80, 0, 0)
            c.l2.color = rgb(0, 0, 90) if on else rgb(60, 80, 255)
    car_collisions()
    for c in cars[:]:
        car_impacts(c)
    for c in cars[:]:
        if c.hp <= 0:
            explode(c)
        else:
            far = abs(c.x - p.x) > 250 or abs(c.z - p.z) > 250
            if far == c.vis:
                c.vis = not far
                c.root.enabled = c.vis
            if c.vis:
                c.sync()

    for h in helis[:]:
        h.update(dt)
        far = abs(h.x - p.x) > 350 or abs(h.z - p.z) > 350
        if far:
            release_heli(h)

    for pd in peds:
        pd.update(dt)
    for cp in cops:
        cp.update(dt)
    for co in corpses[:]:
        co[1] -= dt
        if co[1] <= 0:
            corpses.remove(co)
            co[0].active = False
            co[0].root.enabled = False
            co[2].append(co[0])

    for pk in pick_pool:
        if pk[2] and p.alive and math.hypot(pk[0].x - p.x, pk[0].z - p.z) < 1.8:
            p.money += pk[1]
            pk[2] = False
            pk[0].enabled = False
    update_fx(dt)
    update_bullets(dt)
    update_day_night(dt)

    wanted.update_state(dt)

    if p.stars > 0 and p.stars < 6:
        p.crime_t += dt
        if p.crime_t > 14 and wanted.state != "spotted":
            p.stars -= 1
            p.crime_t = 8
            wanted.level = p.stars
            if p.stars == 0:
                p.hot_timer = 30.0
                wanted.hot_timer = 30.0
    if p.stars == 0 and p.hot_timer > 0:
        p.hot_timer -= dt
        if p.hot_timer <= 0:
            p.hot_timer = 0.0
    prev_stars = p.stars

    spawn_timer -= dt
    cop_timer -= dt
    want = (0, 2, 3, 4, 5, 6, 8)[min(p.stars, 6)]
    n_cop = sum(1 for c in cars if c.kind == "police" and c.driver == "cop")
    if p.alive and p.stars > 0 and n_cop < want and cop_timer <= 0 and car_free["police"]:
        spot = road_spot(110, 200)
        if spot:
            x, z, d = spot
            c = car_free["police"].pop()
            c.reset(x, z, DIR_H[d])
            c.driver = "cop"
            cars.append(c)
        cop_timer = 2.0

    heli_want = 1 if p.stars >= 4 else (1 if p.stars >= 3 and random.random() < 0.3 else 0)
    n_heli = len(helis)
    if p.alive and p.stars >= 3 and n_heli < heli_want and heli_timer <= 0:
        spawn_heli()
        heli_timer = 15.0
    heli_timer -= dt

    for c in cars[:]:
        far = math.hypot(c.x - p.x, c.z - p.z)
        if c.driver == "player":
            continue
        if c.kind == "police":
            if p.stars == 0:
                c.idle += dt
                if c.idle > 8 and far > 80:
                    release_car(c)
                    continue
            if far > 900:
                release_car(c)
        elif far > 350:
            release_car(c)
    for cp in cops[:]:
        far = math.hypot(cp.x - p.x, cp.z - p.z)
        if p.stars == 0:
            cp.idle += dt
            if cp.idle > 10 and far > 70:
                release_cop(cp)
                continue
        if far > 700:
            release_cop(cp)

    if spawn_timer <= 0:
        spawn_timer = 0.2
        if sum(1 for c in cars if c.driver == "ai") < 48:
            spawn_civ(80, 300)
            spawn_civ(80, 300)
        if len(peds) < 115:
            spawn_ped(40, 240)
            spawn_ped(40, 240)
    for pd in peds[:]:
        if math.hypot(pd.x - p.x, pd.z - p.z) > 320:
            release_ped(pd)

    if p.hp < prev_hp - 1 and p.alive and hurt_cd <= 0:
        flash_a = min(0.55, flash_a + 0.35)
        hurt_cd = 0.3
    prev_hp = p.hp
    if not p.alive:
        hud_flash.enabled = True
        hud_flash.color = Color(0, 0, 0, 0.5)
    elif flash_a > 0:
        flash_a = max(0.0, flash_a - dt * 1.2)
        hud_flash.enabled = flash_a > 0.01
        hud_flash.color = Color(0.85, 0.05, 0.05, flash_a)
    else:
        hud_flash.enabled = False

    update_audio(dt)
    update_police_render(dt)
    update_wanted_hud()
    update_fbi(dt)
    update_witnesses(dt)
    update_police_render(dt)
    update_wanted_hud()

    set_text(hud_money, "money", "$ %d" % p.money)
    hud_hp.scale_x = 0.3 * cl(p.hp, 0, 100) / 100
    if p.car:
        hud_car.enabled = True
        hud_car.scale_x = 0.3 * cl(p.car.hp, 0, 100) / 100
        set_text(hud_speed, "speed", "%d км/ч" % (int(abs(p.car.v) * 3.6 / 5) * 5))
    else:
        hud_car.enabled = False
        set_text(hud_speed, "speed", "")
    hud_cross.enabled = p.alive and p.car is None
    hud_timer -= dt
    if hud_timer <= 0:
        hud_timer = 0.12
        mm_player.position = (*mm_pos(p.x, p.z), -0.03)
        dots = [c for c in cars if c.kind == "police"] + cops + helis
        for k, dot in enumerate(mm_dots):
            if k < len(dots):
                dot.enabled = True
                dot.position = (*mm_pos(dots[k].x, dots[k].z), -0.02)
                dot.color = rgb(255, 50, 50) if int(t_game * 4) % 2 else rgb(60, 90, 255)
            else:
                dot.enabled = False

class Heli:
    def __init__(self):
        self.x = self.z = self.y = self.h = 0.0
        self.v = 0.0
        self.vy = 0.0
        self.spin = 0.0
        self.hp = 200.0
        self.active = False
        self.vis = True
        self.shoot_cd = 0.0
        mb = MB()
        box(mb, 0, 0, 0, 1.8, 1.2, 3.5, (240, 240, 245))
        box(mb, 0, 0.7, 0, 1.4, 0.8, 2.0, (48, 68, 94))
        box(mb, 0, 0.8, -1.2, 0.3, 0.3, 3.0, (200, 200, 205))
        box(mb, 0, 1.2, 0, 0.15, 0.15, 7.0, (60, 60, 66))
        box(mb, 0, 1.2, 0, 6.5, 0.08, 0.15, (60, 60, 66))
        box(mb, 0, -0.5, 1.2, 0.3, 0.3, 0.3, (30, 30, 34))
        box(mb, 0, -0.5, -1.2, 0.3, 0.3, 0.3, (30, 30, 34))
        box(mb, 0.6, -0.3, 0.5, 0.15, 0.15, 0.4, (20, 20, 24))
        self.root = Entity(model=mb.mesh(), double_sided=True, enabled=False)
        self.spotlight = Entity(parent=self.root, model="cube", scale=(0.2, 0.2, 0.2),
                                position=(0.6, -0.5, 0.5), color=rgb(255, 240, 180))
        self.rotor = Entity(parent=self.root, model="cube", scale=(6.5, 0.04, 0.15),
                            position=(0, 1.2, 0), color=rgb(60, 60, 66))

    def activate(self, x, z):
        self.x, self.z = x, z
        self.y = 45.0
        self.h = random.uniform(0, 360)
        self.v = 0.0
        self.vy = 0.0
        self.spin = 0.0
        self.hp = 200.0
        self.shoot_cd = 0.0
        self.active = True
        self.vis = True
        self.root.rotation_x = 0
        self.root.rotation_z = 0
        self.root.enabled = True
        self.root.position = (self.x, self.y, self.z)

    def crash(self, dt):
        global heli_down_flag
        self.vy -= 26 * dt
        self.y += self.vy * dt
        self.spin += 260 * dt
        self.x += math.sin(math.radians(self.h)) * 10 * dt
        self.z += math.cos(math.radians(self.h)) * 10 * dt
        self.root.position = (self.x, max(0.5, self.y), self.z)
        self.root.rotation_y = self.h + self.spin
        self.root.rotation_z = 35
        self.rotor.rotation_y += 200 * dt
        if random.random() < 0.6:
            spawn_fx(self.x, self.y, self.z, random.uniform(-1, 1), -2, random.uniform(-1, 1),
                     1.2, 1.4, rgb(60, 60, 62), -1.0)
        if self.y <= 1.0:
            for _ in range(26):
                a = random.uniform(0, TAU)
                sp = random.uniform(2, 11)
                spawn_fx(self.x, 1.0, self.z, math.cos(a) * sp, random.uniform(2, 9), math.sin(a) * sp,
                         random.uniform(0.5, 1.1), random.uniform(0.6, 1.5),
                         random.choice([rgb(255, 170, 40), rgb(255, 90, 30), rgb(255, 220, 90)]), 6)
            spawn_decal(self.x, self.z, 6, 6, random.uniform(0, 360), rgb(20, 20, 20), 60)
            snd.at("gun", self.x, self.z, 1.0, 0.4, 400)
            if math.hypot(player.x - self.x, player.z - self.z) < 8:
                hurt_player(45)
            heli_down_flag = True
            if not hasattr(wanted, "apply_crime"):
                patch_wanted_object()
            wanted.apply_crime(self.x, self.z, 6, ["face", "clothes", "car", "weapon"])
            player.stars = 6
            wanted.level = 6
            wanted.alert_radius = 400.0
            release_heli(self)

    def update(self, dt):
        if self.hp <= 0:
            self.crash(dt)
            return

        if not player.alive:
            self.h += 30 * dt
            self.y = max(30.0, self.y - 5 * dt)
            if self.y <= 30.0:
                release_heli(self)
            self.root.position = (self.x, self.y, self.z)
            self.root.rotation_y = self.h
            self.rotor.rotation_y += 720 * dt
            return

        dx, dz = player.x - self.x, player.z - self.z
        dist = math.hypot(dx, dz)
        target_h = math.degrees(math.atan2(dx, dz))
        self.h += cl(adiff(target_h, self.h), -90 * dt, 90 * dt)

        if dist > 40:
            self.x += math.sin(math.radians(self.h)) * 28 * dt
            self.z += math.cos(math.radians(self.h)) * 28 * dt
        elif dist < 20:
            self.x -= math.sin(math.radians(self.h)) * 12 * dt
            self.z -= math.cos(math.radians(self.h)) * 12 * dt

        target_y = 40.0 + math.sin(t_game * 0.5) * 5.0
        self.y += (target_y - self.y) * min(1, 2.0 * dt)

        self.shoot_cd -= dt
        if self.shoot_cd <= 0 and dist < 60:
            self.shoot_cd = random.uniform(0.8, 1.5)
            tracer(self.x, self.y - 0.5, self.z, self.h, min(dist, 55))
            snd.at("gun", self.x, self.z, 0.5, 0.7, 200)
            if random.random() < 0.3:
                hurt_player(10)

        self.root.position = (self.x, self.y, self.z)
        self.root.rotation_y = self.h
        self.rotor.rotation_y += 720 * dt
        self.root.rotation_z = cl(adiff(target_h, self.h) * 0.3, -15, 15)

# ЗАМЕНИТЬ блок спавна в конце файла:
for _ in range(40): # Было 22, стало 40 машин
    spawn_civ(0, 350)
for _ in range(15): # Было 10, стало 15 припаркованных
    spawn_civ(0, 350, parked=True)
for _ in range(90): # Было 40, стало 90 пешеходов (улицы будут полными)
    spawn_ped(0, 300)

mine.reset(3 * P + ROAD_C + 6.8, 3 * P + RW + 20, 0)
mine.maxv = 38
cars.append(mine)
cam_yaw = 0.0
clean_dev_visuals()
build_wanted_hud()
build_police_render()
init_bullets()
build_day_night_ui()

app.run()