// ============================================================================
//  ZOMBIE SIEGE 3D  —  C++ / SDL2  (для Cxxdroid на Android)
//  Кооперативное выживание против зомби: рейкастинг-3D, прокачка, баррикады.
//
//  Cxxdroid: сначала Меню -> Install Libraries -> SDL2 (один раз), потом Run.
//  Играть вместе: все в одной Wi-Fi сети (или на точке доступа одного из вас).
//    Хост: "СОЗДАТЬ ИГРУ"  ->  друзья: "ПРИСОЕДИНИТЬСЯ" -> тап по игре или ввод IP.
//
//  Управление: левый палец — ходьба, правый — камера.
//  ЯЩИКИ на карте можно ломать стрельбой (у каждого 50 HP): 70% пусто, 25% лом 5-15, 5% случайное оружие + аптечка.
//  ГРАНАТЫ: ГРАНАТА (взрыв: до 260 урона в радиусе 3.4, ломает ящики) и ОГЛУШ. (ВСЕ зомби замирают на 5 с). ПК: G / H. Старт по 2 шт., макс. 9, продаются за лом.
//  Кнопки: ОГОНЬ, АВТО (автострельба), СТРОЙ (баррикада/ремонт), ЗАРЯД, СМЕНА, СТАРТ, МАГАЗИН.
//  МАГАЗИН: покупай оружие и аптечки за лом (в одиночной игре время на паузе).
//  ПК: WASD/стрелки, Q/E, ПРОБЕЛ, B, R, TAB, ENTER, M (магазин)
//  Меню -> НАСТРОЙКИ: расположение кнопок (перетаскивай пальцем), левша, размер кнопок, графика.
// ============================================================================
#include <stddef.h>
#include <stdio.h>
#include <SDL2/SDL.h>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdarg>
#include <string>
#include <vector>
#include <map>
#include <queue>
#include <algorithm>
#include <sstream>
#include <ctime>
#include <signal.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <sys/select.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <arpa/inet.h>
#include <fcntl.h>
#include <unistd.h>
#include <errno.h>

#ifndef MSG_NOSIGNAL
#define MSG_NOSIGNAL 0
#endif

// ============================ НАСТРОЙКИ ============================
enum { S_PISTOL = 0, S_SHOTGUN, S_RIFLE, S_REVOLVER, S_SMG, S_SNIPER, S_LMG, S_OBREZ, S_RELOAD, S_EMPTY, S_HIT, S_HEAD, S_ZDIE, S_GROAN1, S_GROAN2, S_ROAR, S_JUMP, S_LAND,
       S_SPIT, S_SPLAT, S_EXPLODE, S_HURT, S_PICKUP, S_LEVEL, S_WAVE, S_CLEAR, S_BUY, S_CLICK, S_BUILD, S_BREAK, S_SLAM, S_STEP1, S_STEP2, S_HEART,
       S_WIND, S_CRICKET, S_N };
static bool soundOn = true;
static void playSound(int id, float vol = 1.f, float pan = 0.f, float rate = 1.f, bool loop = false);
static void playAt(int id, float x, float y, float vol = 1.f, float rate = 1.f);
static void toastSound(const std::string& t);
static void ambientStart();
static void ambientStop();
static void stopAllSounds();
static const bool LANDSCAPE = true;   // true — горизонтально, false — вертикально
static const bool ROT_CW = true;      // если окно вертикальное: true — повернуть картинку по часовой (телефон наклони влево), false — против
static const int   RAYS = 200;        // (не используется: качество графики выбирается в НАСТРОЙКАХ)
static const float FOV_LAND = 66.f, FOV_PORT = 54.f;
static const int   N = 36;            // размер карты
static const float MAXD = 16.f;
static const int   MAX_ZOMBIES = 44;
static const float LOOK_SENS = 3.2f;
static const int   PORT = 5555, DISC_PORT = 5556, MAX_PLAYERS = 4;
static const float SNAP_DT = 1.f / 20.f;
static const char* SAVE_FILE = "zombie_siege_save.txt";
// ===================================================================

typedef unsigned int u32;
struct Col { unsigned char r, g, b, a; };
static inline Col C(int r, int g, int b, int a = 255) { Col c = {(unsigned char)std::max(0, std::min(255, r)), (unsigned char)std::max(0, std::min(255, g)), (unsigned char)std::max(0, std::min(255, b)), (unsigned char)a}; return c; }
static inline u32 PX(Col c) { return ((u32)c.a << 24) | ((u32)c.r << 16) | ((u32)c.g << 8) | c.b; }
static inline Col shade(Col c, float k) { return C((int)(c.r * k), (int)(c.g * k), (int)(c.b * k), c.a); }

// ============================ ГЕНЕРАТОР СЛУЧАЙНЫХ ============================
static u32 rngs = 2463534242u;
static u32 rnd32() { rngs ^= rngs << 13; rngs ^= rngs >> 17; rngs ^= rngs << 5; return rngs; }
static float frand() { return (rnd32() & 0xFFFFFF) / 16777216.0f; }
static float rr(float a, float b) { return a + (b - a) * frand(); }
static int irand(int a, int b) { return a + (int)(rnd32() % (u32)(b - a + 1)); }

// ============================ ГЛОБАЛЬНОЕ СОСТОЯНИЕ ============================
static SDL_Window* win = NULL;
static SDL_Renderer* ren = NULL;
static int W = 960, H = 540;              // логические размеры (то, что рисуем)
static int PW = 960, PH = 540;            // реальные размеры окна
static bool rotMode = false;              // true: рисуем повёрнутым на 90 градусов
static SDL_Texture* rt = NULL;
static bool portrait = false;
static float U = 5.4f;
static float TANH_ = 0.65f, FOCAL = 400.f;
static float CAMX[1024];
static float zbuf[1024];
static int RW = RAYS;

static int G[N * N];
static float bhp[N * N], bmx[N * N];
static float VARR[N * N];
static int nei[N * N][4], nnei[N * N];
static const int INF = 1 << 30;
static int flowv[N * N];
static std::vector<int> spawnCells;
static const int C0 = N / 2;

static void initTables() {
    for (int i = 0; i < N * N; i++) {
        VARR[i] = frand();
        int x = i % N, y = i / N, n = 0;
        if (x > 0) nei[i][n++] = i - 1;
        if (x < N - 1) nei[i][n++] = i + 1;
        if (y > 0) nei[i][n++] = i - N;
        if (y < N - 1) nei[i][n++] = i + N;
        nnei[i] = n;
    }
}

static void makeMap() {
    for (int i = 0; i < N * N; i++) { G[i] = 0; bhp[i] = 0; bmx[i] = 0; }
    for (int i = 0; i < N; i++) { G[i] = 1; G[(N - 1) * N + i] = 1; G[i * N] = 1; G[i * N + N - 1] = 1; }
    for (int k = 0; k < 38; k++) {
        int w = irand(1, 3), h = irand(1, 3);
        int x = irand(2, N - 2 - w), y = irand(2, N - 2 - h);
        if (fabsf(x + w / 2.f - C0) < 9 && fabsf(y + h / 2.f - C0) < 9) continue;
        int typ = frand() < 0.45f ? 1 : 3;
        for (int yy = y; yy < y + h; yy++) for (int xx = x; xx < x + w; xx++) G[yy * N + xx] = typ;
    }
    for (int y = C0 - 4; y <= C0 + 4; y++)
        for (int x = C0 - 4; x <= C0 + 4; x++) {
            bool edge = (x == C0 - 4 || x == C0 + 4 || y == C0 - 4 || y == C0 + 4);
            G[y * N + x] = edge ? 1 : 0;
        }
    for (int k = C0 - 1; k <= C0; k++) {
        G[(C0 - 4) * N + k] = 0; G[(C0 + 4) * N + k] = 0;
        G[k * N + C0 - 4] = 0; G[k * N + C0 + 4] = 0;
    }
}

static void makeDuelMap() {        // компактная симметричная арена для дуэли: без баррикад, только колонны-укрытия
    for (int i = 0; i < N * N; i++) { G[i] = 0; bhp[i] = 0; bmx[i] = 0; }
    for (int i = 0; i < N; i++) { G[i] = 1; G[(N - 1) * N + i] = 1; G[i * N] = 1; G[i * N + N - 1] = 1; }
    const int R = 12;                // половина стороны арены
    for (int y = 0; y < N; y++) for (int x = 0; x < N; x++) {
        int dx = x - C0, dy = y - C0;
        if (std::max(abs(dx), abs(dy)) > R) G[y * N + x] = 1;
    }
    const int off[][2] = {{-7, -7}, {7, -7}, {-7, 7}, {7, 7}, {0, 0}};
    for (int k = 0; k < 5; k++) {
        int cx = C0 + off[k][0], cy = C0 + off[k][1];
        for (int yy = cy; yy <= cy + 1; yy++) for (int xx = cx; xx <= cx + 1; xx++)
            if (xx > 1 && yy > 1 && xx < N - 2 && yy < N - 2) G[yy * N + xx] = 1;
    }
}
// ============================ ДАННЫЕ ============================
struct WeaponDef { const char* name; float dmg, rate; int pellets; float spread; int mag; float reload; int price; bool pierce; };
static const int NW = 8;                 // число видов оружия
static const int MEDKIT_PRICE = 20;
static const WeaponDef WEAP[NW] = {
    {"ПИСТОЛЕТ", 24, 0.32f, 1, 0.010f, 12, 1.0f, 0, false},
    {"ДРОБОВИК", 13, 0.85f, 7, 0.11f, 6, 1.7f, 55, false},
    {"АВТОМАТ", 17, 0.10f, 1, 0.030f, 30, 1.5f, 100, false},
    {"РЕВОЛЬВЕР", 58, 0.55f, 1, 0.006f, 6, 1.6f, 40, false},
    {"ПП", 10, 0.065f, 1, 0.055f, 40, 1.3f, 75, false},
    {"СНАЙПЕРКА", 120, 1.15f, 1, 0.002f, 5, 2.0f, 140, true},
    {"ПУЛЕМЁТ", 15, 0.055f, 1, 0.050f, 90, 2.4f, 160, false},
    {"ОБРЕЗ", 20, 1.00f, 12, 0.150f, 2, 1.0f, 65, false},
};
// ============================ МОНЕТЫ И СКИНЫ ОРУЖИЯ ============================
static const int NSKINS = 4;                    // 0 — обычный (бесплатный), 1..3 — покупные за монеты
struct SkinDef { const char* name; int price; Col tint; float strength; };
static const SkinDef SKINS[NSKINS] = {
    {"ОБЫЧНЫЙ", 0,   C(0, 0, 0), 0.00f},
    {"ЦИФРА",   90,  C(104, 124, 104), 0.55f},   // серо-зелёный цифровой камуфляж
    {"БОЕВОЙ",  180, C(176, 40, 34), 0.55f},     // тактический красный
    {"ЗОЛОТО",  350, C(255, 201, 86), 0.68f},    // золотое покрытие
};
static int coins = 0;                            // монеты, даются за проигранную игру, тратятся на скины
static int lastCoinsGain = 0;                    // сколько монет начислено за последнюю смерть (для экрана «ты погиб»)
static int weaponSkin[NW] = {0, 0, 0, 0, 0, 0, 0, 0};   // выбранный скин для каждого вида оружия
static bool skinOwned[NW][NSKINS];               // куплен ли скин (обычный скин всегда куплен)
static int skinsTab = 0;                         // какое оружие сейчас открыто на экране «СКИНЫ»
static void initSkinOwn() { for (int i = 0; i < NW; i++) { skinOwned[i][0] = true; for (int s = 1; s < NSKINS; s++) skinOwned[i][s] = false; } }
static const int NSHOP = NW + 3;
static const int SHOP_ORDER[NSHOP] = {0, 3, 1, 7, 4, 2, 6, 5, 100, 101, 102};   // порядок карточек в магазине (100 = аптечка, 101 = взрывная граната, 102 = оглушающая)
static const int WLVL_MAX = 5;                // макс. уровень прокачки одного оружия
static int wUpgCost(int idx, int lvl) { return 15 + lvl * 14 + WEAP[idx].price / 5; }   // цена в ломе за следующий уровень
struct UpgDef { const char* title; const char* desc; };
static const UpgDef UPGS[9] = {
    {"УРОН +20%", "ВСЕ ПУЛИ БЬЮТ СИЛЬНЕЕ"},
    {"СКОРОСТРЕЛЬНОСТЬ +15%", "СТРЕЛЯЕШЬ ЧАЩЕ"},
    {"ЗДОРОВЬЕ +25", "МАКС. HP И ЛЕЧЕНИЕ НА 25"},
    {"СКОРОСТЬ +10%", "БЫСТРЕЕ БЕГАЕШЬ"},
    {"МАГАЗИН +30%", "БОЛЬШЕ ПАТРОНОВ В ОБОЙМЕ"},
    {"КРЕПКИЕ СТЕНЫ +50%", "ТВОИ БАРРИКАДЫ ДЕРЖАТСЯ ДОЛЬШЕ"},
    {"ДЕШЁВАЯ СТРОЙКА -1", "БАРРИКАДА СТОИТ НА 1 ЛОМ МЕНЬШЕ"},
    {"РЕГЕНЕРАЦИЯ +1 HP/С", "МЕДЛЕННО ЛЕЧИШЬСЯ САМ"},
    {"МАРОДЁР +30%", "БОЛЬШЕ ЛОМА С ЗОМБИ"},
};
struct ZKind { float hp, spd, dmg; int xp, sMin, sMax; float r, hs; Col skin, shirt, pants; };
static const int NZK = 6;
static const ZKind ZK[NZK] = {
    {34, 1.05f, 9, 10, 1, 2, 0.30f, 0.95f, {95, 140, 80, 255}, {90, 60, 50, 255}, {40, 50, 90, 255}},         // 0 обычный
    {22, 2.15f, 6, 16, 1, 3, 0.27f, 0.90f, {150, 150, 90, 255}, {60, 90, 60, 255}, {60, 60, 60, 255}},        // 1 бегун
    {150, 0.80f, 22, 45, 4, 7, 0.42f, 1.25f, {80, 110, 100, 255}, {70, 40, 90, 255}, {35, 35, 45, 255}},      // 2 громила
    {30, 0.95f, 12, 24, 2, 3, 0.30f, 0.95f, {165, 190, 70, 255}, {58, 82, 50, 255}, {40, 40, 40, 255}},       // 3 плевака (стреляет кислотой)
    {26, 1.75f, 30, 22, 2, 4, 0.30f, 0.95f, {150, 120, 90, 255}, {205, 92, 30, 255}, {50, 50, 60, 255}},      // 4 подрывник (взрывается)
    {900, 0.95f, 30, 250, 25, 40, 0.55f, 1.65f, {124, 62, 62, 255}, {64, 22, 22, 255}, {30, 25, 30, 255}},    // 5 тиран (босс)
};
static const Col PCOL[4] = {{70, 150, 255, 255}, {255, 170, 50, 255}, {90, 220, 110, 255}, {230, 90, 200, 255}};

struct Player {
    int id = 0; std::string name;
    float x = 0, y = 0, ang = 0, hp = 100, maxhp = 100, xp = 0, need = 60;
    int level = 1, scrap = 14, kills = 0, weapon = 0, cost = 4, pending = 0;
    bool unl[NW] = {true, false, false, false, false, false, false, false};
    int ammo[NW] = {12, 6, 30, 6, 40, 5, 90, 2};
    int wLvl[NW] = {0, 0, 0, 0, 0, 0, 0, 0};      // уровень прокачки каждого оружия за лом (0..WLVL_MAX)
    float dmgMul = 1, rateMul = 1, spdMul = 1, magMul = 1, wallMul = 1, scrapMul = 1, regen = 0;
    float fireCd = 0, reload = 0, flash = 0, hurt = 0, hit = 0, bob = 0;
    bool autoF = true, dead = false, menu = false, fire = false;
    int cards[3] = {0, 1, 2};
    float pitch = 0;                    // взгляд вверх/вниз
    int combo = 0; float comboT = 0;    // серия убийств (бонус лома)
    int gren[2] = {2, 2};               // гранаты: 0 взрывные, 1 оглушающие
    float grenCd = 0;                   // пауза между бросками
    float jumpZ = 0, jumpV = 0;         // высота прыжка и вертикальная скорость
    bool perkSet = false;              // класс уже применён хостом
    float headT = 0;                    // таймер «попал в голову»
    float tx = 0, ty = 0;
};
struct Zombie {
    int id = 0, kind = 0; float x = 0, y = 0, hp = 1, maxhp = 1, spd = 1, dmg = 1, cd = 0, flash = 0, r = 0.3f, hs = 0.95f; int xp = 10;
    float tx = 0, ty = 0;
    float spitCd = 1.5f, slamCd = 4.f, slamFlash = 0.f, stun = 0.f; bool boom = false, slam = false;
};
struct Spit { float x, y, vx, vy, life, dmg; };
struct Boom { float x, y, dmg; };
static std::vector<Spit> spits;                          // кислотные плевки
static std::vector<Boom> booms;                          // отложенные взрывы
static int difficulty = 1;                               // 0 лёгко, 1 нормально, 2 сложно
static const float DHF[3] = {0.75f, 1.f, 1.4f}, DDF[3] = {0.65f, 1.f, 1.4f}, DNF[3] = {0.8f, 1.f, 1.25f};
struct Gren { float x, y, z, vx, vy, vz, fuse; int type, owner, id; };      // type: 0 взрывная, 1 оглушающая
static std::vector<Gren> grens;
static int grenIdCounter = 1;
static const float STUN_TIME = 5.f;                 // на сколько секунд оглушаются ВСЕ зомби
static const float GREN_RADIUS = 3.4f, GREN_DMG = 260.f;
static const int GREN_MAX = 9;
static const int GREN_PRICE[2] = {18, 14};          // цена одной гранаты в ломе (взрывная, оглушающая)
struct Crate { float x, y; int kind; };  // 0 лом, 1 аптечка, 2 опыт

enum { M_MENU = 0, M_JOIN = 1, M_PLAY = 2, M_DEAD = 3, M_LAYOUT = 4, M_SETTINGS = 5, M_SKINS = 6, M_DUEL = 7, M_QUESTS = 8 };
// ---- дуэль: игрок против игрока (с ботом или с другом по сети) ----
static bool duelMode = false;      // сейчас идёт дуэль, а не выживание против зомби
static bool duelBot = false;       // соперник в дуэли — бот, а не другой человек
static int duelScore[2] = {0, 0};  // счёт раундов: индекс — id игрока (в дуэли это всегда 0 и 1)
static int duelRoundNum = 1;       // номер текущего раунда
static const int DUEL_ROUNDS_TO_WIN = 3;   // матч до 3 побед (best of 5)
static int duelBotLevel = 1;       // выбранная сложность бота (0..3)
struct BotLevelDef { const char* name; int weapon; float hp; float spdMul; float dmgMul; float turnRate; float aimTol; float engageDist; };
// ============================ КЛАССЫ (ПЕРКИ) ИГРОКА ============================
struct PerkDef { const char* name; const char* desc; };
static const PerkDef PERKS[4] = {
    {"БЕЗ КЛАССА", "ИГРАТЬ БЕЗ БОНУСОВ"},
    {"ШТУРМОВИК", "+18% СКОРОСТРЕЛЬНОСТЬ ВСЕГО ОРУЖИЯ"},
    {"СНАЙПЕР", "+20% УРОН ОТ ВСЕХ ПОПАДАНИЙ"},
    {"МЕДИК", "ПАССИВНАЯ РЕГЕНЕРАЦИЯ +1.5 HP/С"},
};
static int selectedPerk = 0;      // выбранный класс (сохраняется), 0 — без бонусов
static void applyPerkId(Player& p, int perk);
static void applyPerk(Player& p) { applyPerkId(p, selectedPerk); }
static void applyPerkId(Player& p, int perk) {
    switch (perk) {
        case 1: p.rateMul *= 0.85f; break;      // штурмовик: быстрее стреляет
        case 2: p.dmgMul *= 1.20f; break;        // снайпер: больше урона
        case 3: p.regen += 1.5f; break;          // медик: регенерация HP
        default: break;
    }
}
// ============================ ЕЖЕДНЕВНЫЕ ЗАДАНИЯ ============================
enum { QT_KILLS = 0, QT_WAVE = 1, QT_DUELWIN = 2, QT_HEADSHOT = 3 };
struct DailyQuest { int type = 0, target = 1, progress = 0, reward = 0; bool claimed = false; };
static DailyQuest dailyQ[3];
static int dailyDayId = -1;
static int duelWinsBot[4] = {0, 0, 0, 0}, duelLossBot[4] = {0, 0, 0, 0};   // статистика дуэлей с ботом по уровням сложности
static int duelWinsFriend = 0, duelLossFriend = 0;                        // статистика дуэлей с другом по сети
static const BotLevelDef BOTLV[4] = {          // имя, оружие, HP, скорость, урон, скорость поворота, точность прицела, дальность боя
    {"ЛЁГКИЙ",  0, 70,  0.85f, 0.75f, 1.6f, 0.24f, 7.f},
    {"СРЕДНИЙ", 2, 100, 1.00f, 1.00f, 2.6f, 0.14f, 9.f},
    {"СЛОЖНЫЙ", 6, 130, 1.15f, 1.15f, 3.6f, 0.09f, 10.f},
    {"ЭКСПЕРТ", 5, 150, 1.25f, 1.30f, 4.5f, 0.05f, 12.f},
};
// ---- настройки (сохраняются в файл) ----
static const int NBTN = 10;
static bool shopOpen = false;                 // открыт ли магазин
static bool paused = false;                   // пауза (только одиночная игра)
static bool aimAssist = true, tutDone = false, newRecord = false, autoFireOn = true;
static bool wantQuit = false, confirmExit = false;   // выход из игры через меню (с подтверждением)
static float settingsScroll = 0.f, settingsMaxScroll = 0.f;   // прокрутка списка настроек
static bool settingsDragging = false; static long long settingsDragId = -2; static float settingsDragX0 = 0, settingsDragY0 = 0; static bool settingsMoved = false;      // помощь в прицеле, обучение пройдено, новый рекорд
static float bannerT = 0, bannerMax = 2.6f; static int bannerCol = 0; static std::string bannerS, bannerS2; static int lastBannerWave = -1; static bool lastBannerPrep = true;
static float bloodMoon = 0;                   // 0..1: «кровавая луна» во время волны
static bool bloodNight = false;               // редкое событие (10% шанс на волну): зомби злее и лома больше
static int hudCombo = 0, lastKillsSeen = 0, statHead = 0; static float hudComboT = 0, comboPop = 0, runTime = 0;
static bool leftHand = false;                 // управление для левши
static float btnScale = 1.f;                  // размер кнопок
static int quality = 1;                       // графика: 0 низкая, 1 средняя, 2 высокая
static float sensitivity = 1.f;               // чувствительность камеры
static bool showFps = true;                   // счётчик FPS
static bool autoQ = true;                     // автоснижение графики при низком FPS
static bool invertY = false;                  // инверсия вертикальной оси
static const float PITCH_MAX = 0.38f;         // предел взгляда вверх/вниз (радианы)
static bool hasCustom[2] = {false, false};    // свои позиции кнопок (0 горизонтально, 1 вертикально)
static float customPos[2][NBTN][2];
static const int QRAYS[3] = {140, 200, 280};
static void relayout();
enum { R_SOLO = 0, R_HOST = 1, R_CLIENT = 2 };

static std::map<int, Player> players;
static Player* P = NULL;
static int meId = 0;
static std::vector<Zombie> zombies;
static std::vector<Crate> crates;
static int zidc = 0;
static void fxReset();
static void genDecos();
static void bakeGround();
static int mode = M_MENU, netRole = R_SOLO;
static int wave = 0; static bool prep = true; static float ptimer = 40.f;
static int toSpawn = 0, leftZ = 0; static float spawnT = 0, flowT = 0; static bool flowDirty = true;
static std::string toastS; static float toastT = 0;
static float deadT = 0; static int bestWave = 0; static bool mmDirty = true;
static std::string ipStr = "192.168.", msgStr, hostIp;
static float pickT = 0, sendT = 0, snapT = 0, discT = 0, waitT = 0;

static int mag_size(const Player& p, int i) { return std::max(1, (int)(WEAP[i].mag * p.magMul * (1.f + 0.08f * p.wLvl[i]))); }
static float wmax(const Player& p) { return 100.f * p.wallMul; }
static float bratio(int idx) { return bmx[idx] > 0 ? bhp[idx] / bmx[idx] : 1.f; }

// ============================ СЕТЬ (низкий уровень) ============================
struct Peer { int fd = -1; std::string in, out; int pid = -1; bool alive = true; };
static std::vector<Peer> peers;
static Peer link_; static bool linked = false;
static int lsock = -1, bsock = -1, dsock = -1;
struct Found { std::string ip; double t; };
static std::vector<Found> found;

static void setNB(int fd) { int f = fcntl(fd, F_GETFL, 0); fcntl(fd, F_SETFL, f | O_NONBLOCK); }
static void netFlush(Peer& p) {
    while (!p.out.empty() && p.alive) {
        ssize_t n = ::send(p.fd, p.out.data(), p.out.size(), MSG_NOSIGNAL);
        if (n > 0) p.out.erase(0, (size_t)n);
        else { if (errno == EAGAIN || errno == EWOULDBLOCK || errno == EINTR) break; p.alive = false; }
    }
    if (p.out.size() > 2000000) p.alive = false;
}
static void netSend(Peer& p, const std::string& s) { if (!p.alive) return; p.out += s; p.out += '\n'; netFlush(p); }
static void netRecv(Peer& p, std::vector<std::string>& out) {
    char buf[8192];
    while (p.alive) {
        ssize_t n = ::recv(p.fd, buf, sizeof buf, 0);
        if (n > 0) p.in.append(buf, (size_t)n);
        else if (n == 0) { p.alive = false; break; }
        else { if (errno == EAGAIN || errno == EWOULDBLOCK || errno == EINTR) break; p.alive = false; break; }
    }
    size_t pos;
    while ((pos = p.in.find('\n')) != std::string::npos) { out.push_back(p.in.substr(0, pos)); p.in.erase(0, pos + 1); }
}
static void netClose(Peer& p) { if (p.fd >= 0) { ::close(p.fd); p.fd = -1; } p.alive = false; }
static std::string fmt(const char* f, ...) {
    char buf[512]; va_list ap; va_start(ap, f); vsnprintf(buf, sizeof buf, f, ap); va_end(ap); return std::string(buf);
}
static std::string localIp() {
    const char* targets[] = {"10.255.255.255", "192.168.255.255", "172.16.255.255", "8.8.8.8"};
    for (int i = 0; i < 4; i++) {
        int s = socket(AF_INET, SOCK_DGRAM, 0);
        if (s < 0) continue;
        int one = 1; setsockopt(s, SOL_SOCKET, SO_BROADCAST, &one, sizeof one);
        sockaddr_in a; memset(&a, 0, sizeof a); a.sin_family = AF_INET; a.sin_port = htons(1); inet_pton(AF_INET, targets[i], &a.sin_addr);
        if (connect(s, (sockaddr*)&a, sizeof a) == 0) {
            sockaddr_in me; socklen_t l = sizeof me;
            if (getsockname(s, (sockaddr*)&me, &l) == 0) {
                char b[64]; inet_ntop(AF_INET, &me.sin_addr, b, sizeof b);
                ::close(s);
                if (strncmp(b, "127.", 4) != 0 && strcmp(b, "0.0.0.0") != 0) return b;
                continue;
            }
        }
        ::close(s);
    }
    return "?";
}

// ============================ ФИЗИКА / КАРТА ============================
static bool decoBlocks(float x, float y, float r, bool ignoreCrate = false, bool isZombie = false);
static bool freeAt(float x, float y, float r, bool ignoreCrate = false, bool isZombie = false) {
    return G[(int)(y - r) * N + (int)(x - r)] == 0 && G[(int)(y - r) * N + (int)(x + r)] == 0 &&
           G[(int)(y + r) * N + (int)(x - r)] == 0 && G[(int)(y + r) * N + (int)(x + r)] == 0 && !decoBlocks(x, y, r, ignoreCrate, isZombie);
}
static void tryMove(float& px, float& py, float nx, float ny, float r, bool ignoreCrate = false, bool isZombie = false) {
    if (freeAt(nx, py, r, ignoreCrate, isZombie)) px = nx;
    if (freeAt(px, ny, r, ignoreCrate, isZombie)) py = ny;
}
static float wallDist(float ox, float oy, float ang, float maxd = MAXD) {
    float dx = cosf(ang), dy = sinf(ang);
    int mx = (int)ox, my = (int)oy;
    float ddx = dx != 0 ? fabsf(1.f / dx) : 1e30f, ddy = dy != 0 ? fabsf(1.f / dy) : 1e30f;
    int sx, sy; float sdx, sdy;
    if (dx < 0) { sx = -1; sdx = (ox - mx) * ddx; } else { sx = 1; sdx = (mx + 1.f - ox) * ddx; }
    if (dy < 0) { sy = -1; sdy = (oy - my) * ddy; } else { sy = 1; sdy = (my + 1.f - oy) * ddy; }
    for (int i = 0; i < 80; i++) {
        float d;
        if (sdx < sdy) { d = sdx; sdx += ddx; mx += sx; } else { d = sdy; sdy += ddy; my += sy; }
        if (d > maxd) return maxd;
        if (G[my * N + mx]) return d;
    }
    return maxd;
}
static const float HEAD_MULT = 2.5f;      // множитель урона в голову
static const float HEAD_FROM = 0.70f;      // голова: верхние 30% роста зомби
// луч из глаз игрока (высота 0.5) идёт под углом pitch; попасть можно только в тело по высоте: 0 .. рост
static int hitTarget(const Player& pl, float ang, float pitch, float* tOut, bool* headOut) {
    float wd = wallDist(pl.x, pl.y, ang);
    float c = cosf(ang), s = sinf(ang), tp = tanf(pitch), bt = wd; int best = -1; bool bh = false;
    for (size_t i = 0; i < zombies.size(); i++) {
        const Zombie& z = zombies[i];
        float rx = z.x - pl.x, ry = z.y - pl.y, t = rx * c + ry * s;
        if (t > 0 && t < bt && fabsf(-rx * s + ry * c) < z.r + 0.06f) {
            float rz = 0.5f + t * tp;
            if (rz < -0.04f || rz > z.hs + 0.05f) continue;         // выше или ниже зомби
            best = (int)i; bt = t; bh = rz >= z.hs * HEAD_FROM;
        }
    }
    if (tOut) *tOut = bt;
    if (headOut) *headOut = bh;
    return best;
}

static int hitTargetPlayer(const Player& pl, float ang, float pitch, float* tOut, bool* headOut) {   // дуэль: луч ищет другого живого игрока
    float wd = wallDist(pl.x, pl.y, ang);
    float c = cosf(ang), s = sinf(ang), tp = tanf(pitch), bt = wd; int best = -1; bool bh = false;
    for (std::map<int, Player>::iterator it = players.begin(); it != players.end(); ++it) {
        Player& op = it->second;
        if (op.id == pl.id || op.dead) continue;
        float rx = op.x - pl.x, ry = op.y - pl.y, t = rx * c + ry * s;
        if (t > 0 && t < bt && fabsf(-rx * s + ry * c) < 0.30f) {
            float rz = 0.5f + t * tp;
            if (rz < -0.04f || rz > 1.0f) continue;
            best = op.id; bt = t; bh = rz >= 1.0f * HEAD_FROM;
        }
    }
    if (tOut) *tOut = bt;
    if (headOut) *headOut = bh;
    return best;      // id игрока-цели (не индекс), либо -1
}
static void computeFlow() {
    for (int i = 0; i < N * N; i++) flowv[i] = INF;
    typedef std::pair<int, int> PI;
    std::priority_queue<PI, std::vector<PI>, std::greater<PI> > q;
    for (std::map<int, Player>::iterator it = players.begin(); it != players.end(); ++it) {
        if (it->second.dead) continue;
        int s = (int)it->second.y * N + (int)it->second.x;
        if (flowv[s] > 0) { flowv[s] = 0; q.push(PI(0, s)); }
    }
    while (!q.empty()) {
        PI t = q.top(); q.pop();
        int d = t.first, i = t.second;
        if (d > flowv[i]) continue;
        for (int k = 0; k < nnei[i]; k++) {
            int j = nei[i][k], c = G[j];
            if (c == 1 || c == 3) continue;
            int nd = d + (c == 0 ? 1 : 6);
            if (nd < flowv[j]) { flowv[j] = nd; q.push(PI(nd, j)); }
        }
    }
    flowDirty = false; flowT = 0.5f;
}
static void bfsDist(int src, std::vector<int>& dist) {      // расстояние (в клетках) от src до всех проходимых клеток карты
    dist.assign(N * N, INF); dist[src] = 0;
    std::queue<int> q; q.push(src);
    while (!q.empty()) {
        int i = q.front(); q.pop();
        for (int k = 0; k < nnei[i]; k++) {
            int j = nei[i][k], c = G[j];
            if (c == 1 || c == 3) continue;
            if (dist[j] > dist[i] + 1) { dist[j] = dist[i] + 1; q.push(j); }
        }
    }
}
static void duelSpawnPoints(float* ax, float* ay, float* bx, float* by) {   // две точки подальше друг от друга (по факту прохода, не по прямой)
    int start = C0 * N + C0;
    if (G[start] == 1 || G[start] == 3) for (int i = 0; i < N * N; i++) if (G[i] != 1 && G[i] != 3) { start = i; break; }
    std::vector<int> d1; bfsDist(start, d1);
    int bi = start, bd = -1;
    for (int i = 0; i < N * N; i++) if (d1[i] < INF && d1[i] > bd) { bd = d1[i]; bi = i; }
    std::vector<int> d2; bfsDist(bi, d2);
    int bj = bi, bd2 = -1;
    for (int i = 0; i < N * N; i++) if (d2[i] < INF && d2[i] > bd2) { bd2 = d2[i]; bj = i; }
    *ax = (bi % N) + 0.5f; *ay = (bi / N) + 0.5f;
    *bx = (bj % N) + 0.5f; *by = (bj / N) + 0.5f;
}
static void placeDuelPlayers() {     // разводит дуэлянтов по разным концам карты (используется в начале каждого раунда)
    if (!duelMode || !players.count(0)) return;
    Player* a = &players[0]; Player* b = players.count(1) ? &players[1] : NULL;
    float ax, ay, bx, by; duelSpawnPoints(&ax, &ay, &bx, &by);
    a->x = ax; a->y = ay; a->ang = atan2f(by - ay, bx - ax);
    if (b) { b->x = bx; b->y = by; b->ang = atan2f(ay - by, ax - bx); }
    flowDirty = true;
}

// ============================ ИГРОКИ ============================
static Player newPlayer(int pid) {
    Player p; p.id = pid;
    p.name = pid == 0 ? "ХОСТ" : fmt("ИГРОК %d", pid + 1);
    static const float off[4][2] = {{0, 0}, {1.3f, 0}, {-1.3f, 0}, {0, 1.3f}};
    p.x = C0 + 0.5f + off[pid % 4][0]; p.y = C0 + 0.5f + off[pid % 4][1];
    for (int i = 0; i < NW; i++) p.ammo[i] = mag_size(p, i);
    p.autoF = autoFireOn;
    return p;
}
static std::vector<Player*> alivePlayers() {
    std::vector<Player*> v;
    for (std::map<int, Player>::iterator it = players.begin(); it != players.end(); ++it) if (!it->second.dead) v.push_back(&it->second);
    return v;
}
static Player* nearestPlayer(float x, float y, float* dOut) {
    Player* best = NULL; float bd = 1e18f;
    for (std::map<int, Player>::iterator it = players.begin(); it != players.end(); ++it) {
        Player& p = it->second; if (p.dead) continue;
        float d = (p.x - x) * (p.x - x) + (p.y - y) * (p.y - y);
        if (d < bd) { bd = d; best = &p; }
    }
    if (dOut) *dOut = best ? sqrtf(bd) : 0;
    return best;
}
static void toast(const std::string& t, float d = 2.6f, Player* pl = NULL) {
    if (!pl || pl == P) { toastS = t; toastT = d; toastSound(t); }
    if (netRole == R_HOST)
        for (size_t i = 0; i < peers.size(); i++)
            if (!pl || pl->id == peers[i].pid) netSend(peers[i], fmt("T %.1f ", d) + t);
}

static void spawnCrates(int n) {
    for (int k = 0; k < n; k++)
        for (int t = 0; t < 20; t++) {
            int c;
            if (frand() < 0.85f && !spawnCells.empty()) c = spawnCells[irand(0, (int)spawnCells.size() - 1)];
            else c = (C0 + irand(-3, 3)) * N + C0 + irand(-3, 3);
            float d; Player* pl = nearestPlayer(c % N + 0.5f, c / N + 0.5f, &d);
            if (G[c] == 0 && (!pl || d > 3)) {
                float r = frand(); Crate cr; cr.x = c % N + 0.5f; cr.y = c / N + 0.5f;
                cr.kind = r < 0.6f ? 0 : (r < 0.85f ? 1 : 2);
                crates.push_back(cr); break;
            }
        }
}

static void ensureWeaponSprite(int wi);   // строим спрайт оружия сразу целиком (заранее объявлено ниже, определение дальше по файлу)
static void newGame() {
    if (duelMode) makeDuelMap(); else makeMap();
    zombies.clear(); crates.clear(); players.clear(); fxReset(); genDecos(); bakeGround(); spits.clear(); booms.clear(); grens.clear();
    meId = 0; players[0] = newPlayer(0); P = &players[0]; applyPerk(*P); paused = false; newRecord = false; bannerT = 0; lastBannerWave = -1; lastBannerPrep = true; bloodMoon = 0; bloodNight = false; hudCombo = 0; lastKillsSeen = 0; hudComboT = 0; statHead = 0; runTime = 0;
    wave = 0; prep = true; ptimer = 40.f; toSpawn = 0; spawnT = 0; flowT = 0; flowDirty = true; mmDirty = true;
    toastS.clear(); toastT = 0;
    computeFlow();
    spawnCells.clear();
    for (int i = 0; i < N * N; i++)
        if (flowv[i] < INF && (abs(i % N - C0) > 5 || abs(i / N - C0) > 5)) spawnCells.push_back(i);
    spawnCrates(duelMode ? 3 : 8);
    toast("НОЧЬ БЛИЗКО! УСПЕЙ УКРЕПИТЬСЯ", 5.f);
    ensureWeaponSprite(P->weapon);   // оружие в руках готовим сразу — иначе первые секунды игры его не видно
    mode = M_PLAY; ambientStart();
}

static void saveData() {
    FILE* f = fopen(SAVE_FILE, "w");
    if (!f) return;
    fprintf(f, "best=%d\nip=%s\nleft=%d\nbscale=%.2f\nquality=%d\nsens=%.2f\ninvy=%d\n", bestWave, ipStr.c_str(), leftHand ? 1 : 0, btnScale, quality, sensitivity, invertY ? 1 : 0);
    fprintf(f, "fps=%d\nautoq=%d\nsound=%d\ndiff=%d\n", showFps ? 1 : 0, autoQ ? 1 : 0, soundOn ? 1 : 0, difficulty);
    fprintf(f, "aim=%d\nhint=%d\nauto=%d\n", aimAssist ? 1 : 0, tutDone ? 1 : 0, autoFireOn ? 1 : 0);
    fprintf(f, "coins=%d\n", coins);
    fprintf(f, "perk=%d\n", selectedPerk);
    fprintf(f, "skinsel="); for (int i = 0; i < NW; i++) fprintf(f, "%d ", weaponSkin[i]); fprintf(f, "\n");
    fprintf(f, "skinown="); for (int i = 0; i < NW; i++) for (int s = 0; s < NSKINS; s++) fprintf(f, "%d ", skinOwned[i][s] ? 1 : 0); fprintf(f, "\n");
    fprintf(f, "duelwbot="); for (int i = 0; i < 4; i++) fprintf(f, "%d ", duelWinsBot[i]); fprintf(f, "\n");
    fprintf(f, "duellbot="); for (int i = 0; i < 4; i++) fprintf(f, "%d ", duelLossBot[i]); fprintf(f, "\n");
    fprintf(f, "duelfriend=%d %d\n", duelWinsFriend, duelLossFriend);
    fprintf(f, "dailyid=%d\n", dailyDayId);
    for (int i = 0; i < 3; i++) fprintf(f, "quest%d=%d %d %d %d %d\n", i, dailyQ[i].type, dailyQ[i].target, dailyQ[i].progress, dailyQ[i].reward, dailyQ[i].claimed ? 1 : 0);
    for (int o = 0; o < 2; o++)
        if (hasCustom[o]) {
            fprintf(f, "lay%d=", o);
            for (int i = 0; i < NBTN; i++) fprintf(f, "%.4f %.4f ", customPos[o][i][0], customPos[o][i][1]);
            fprintf(f, "\n");
        }
    fclose(f);
}
static void loadData() {
    initSkinOwn();
    FILE* f = fopen(SAVE_FILE, "r");
    if (!f) return;
    char line[600];
    while (fgets(line, sizeof line, f)) {
        size_t n = strlen(line);
        while (n && (line[n - 1] == '\n' || line[n - 1] == '\r')) line[--n] = 0;
        char* eq = strchr(line, '=');
        if (!eq) continue;
        *eq = 0; const char* k = line; const char* v = eq + 1;
        if (!strcmp(k, "best")) bestWave = atoi(v);
        else if (!strcmp(k, "ip")) { if (*v) ipStr = v; }
        else if (!strcmp(k, "left")) leftHand = atoi(v) != 0;
        else if (!strcmp(k, "bscale")) btnScale = (float)atof(v);
        else if (!strcmp(k, "quality")) quality = atoi(v);
        else if (!strcmp(k, "sens")) sensitivity = (float)atof(v);
        else if (!strcmp(k, "invy")) invertY = atoi(v) != 0;
        else if (!strcmp(k, "fps")) showFps = atoi(v) != 0;
        else if (!strcmp(k, "autoq")) autoQ = atoi(v) != 0;
        else if (!strcmp(k, "sound")) soundOn = atoi(v) != 0;
        else if (!strcmp(k, "diff")) difficulty = std::max(0, std::min(2, atoi(v)));
        else if (!strcmp(k, "aim")) aimAssist = atoi(v) != 0;
        else if (!strcmp(k, "hint")) tutDone = atoi(v) != 0;
        else if (!strcmp(k, "auto")) autoFireOn = atoi(v) != 0;
        else if (!strcmp(k, "coins")) coins = std::max(0, atoi(v));
        else if (!strcmp(k, "perk")) selectedPerk = std::max(0, std::min(3, atoi(v)));
        else if (!strcmp(k, "skinsel")) {
            const char* p = v; char* e = NULL;
            for (int i = 0; i < NW; i++) { long val = strtol(p, &e, 10); if (e == p) break; weaponSkin[i] = std::max(0, std::min(NSKINS - 1, (int)val)); p = e; }
        }
        else if (!strcmp(k, "skinown")) {
            const char* p = v; char* e = NULL;
            for (int i = 0; i < NW; i++) for (int s = 0; s < NSKINS; s++) { long val = strtol(p, &e, 10); if (e == p) break; skinOwned[i][s] = val != 0; p = e; }
            for (int i = 0; i < NW; i++) skinOwned[i][0] = true;   // обычный скин всегда доступен
        }
        else if (!strcmp(k, "duelwbot")) { const char* p = v; char* e = NULL; for (int i = 0; i < 4; i++) { long val = strtol(p, &e, 10); if (e == p) break; duelWinsBot[i] = (int)val; p = e; } }
        else if (!strcmp(k, "duellbot")) { const char* p = v; char* e = NULL; for (int i = 0; i < 4; i++) { long val = strtol(p, &e, 10); if (e == p) break; duelLossBot[i] = (int)val; p = e; } }
        else if (!strcmp(k, "duelfriend")) { std::istringstream ds(v); ds >> duelWinsFriend >> duelLossFriend; }
        else if (!strcmp(k, "dailyid")) dailyDayId = atoi(v);
        else if (!strncmp(k, "quest", 5) && strlen(k) == 6) {
            int i = k[5] - '0';
            if (i >= 0 && i < 3) {
                int cl = 0; std::istringstream qs(v);
                qs >> dailyQ[i].type >> dailyQ[i].target >> dailyQ[i].progress >> dailyQ[i].reward >> cl;
                dailyQ[i].claimed = cl != 0;
            }
        }
        else if (!strncmp(k, "lay", 3) && (k[3] == '0' || k[3] == '1')) {
            int o = k[3] - '0'; float a[NBTN * 2]; int cnt = 0; const char* p = v; char* e = NULL;
            for (; cnt < NBTN * 2; cnt++) { a[cnt] = strtof(p, &e); if (e == p) break; p = e; }
            if (cnt == NBTN * 2 || cnt == 16) { for (int i = 0; i < NBTN; i++) { if (i * 2 + 1 < cnt) { customPos[o][i][0] = a[i * 2]; customPos[o][i][1] = a[i * 2 + 1]; } else { customPos[o][i][0] = -1.f; customPos[o][i][1] = -1.f; } } hasCustom[o] = true; }
        }
    }
    fclose(f);
    btnScale = std::max(0.6f, std::min(1.6f, btnScale));
    quality = std::max(0, std::min(2, quality));
    sensitivity = std::max(0.3f, std::min(3.0f, sensitivity));
}

// ============================ ПРОКАЧКА ============================
static void gainXp(Player& pl, float n) {
    pl.xp += n;
    while (pl.xp >= pl.need) {
        pl.xp -= pl.need; pl.level++; pl.need = 60.f + 45.f * pl.level; pl.pending++;
    }
}
static void openLevelUp(Player& pl) {
    int a = irand(0, 8), b, c;
    do { b = irand(0, 8); } while (b == a);
    do { c = irand(0, 8); } while (c == a || c == b);
    pl.cards[0] = a; pl.cards[1] = b; pl.cards[2] = c; pl.menu = true;
}
static void applyUpgrade(Player& pl, int uid) {
    if (!pl.menu || (uid != pl.cards[0] && uid != pl.cards[1] && uid != pl.cards[2])) return;
    switch (uid) {
        case 0: pl.dmgMul *= 1.2f; break;
        case 1: pl.rateMul *= 0.87f; break;
        case 2: pl.maxhp += 25; pl.hp = std::min(pl.maxhp, pl.hp + 25); break;
        case 3: pl.spdMul *= 1.1f; break;
        case 4: pl.magMul *= 1.3f; for (int i = 0; i < NW; i++) pl.ammo[i] = mag_size(pl, i); break;
        case 5: pl.wallMul *= 1.5f; break;
        case 6: pl.cost = std::max(2, pl.cost - 1); break;
        case 7: pl.regen += 1.f; break;
        case 8: pl.scrapMul *= 1.3f; break;
    }
    pl.pending--; pl.menu = false;
}

// ============================ ЗОМБИ / ОРУЖИЕ (хост) ============================
static void gameOver();
static int todayId() { time_t t = time(NULL); struct tm* lt = localtime(&t); return lt ? lt->tm_year * 400 + lt->tm_yday : 0; }
static void questCheckComplete(int i) {
    if (!dailyQ[i].claimed && dailyQ[i].progress >= dailyQ[i].target) {
        dailyQ[i].claimed = true; coins += dailyQ[i].reward; saveData();
        toast(fmt("ЗАДАНИЕ ВЫПОЛНЕНО! +%d МОНЕТ", dailyQ[i].reward), 3.f);
    }
}
static void ensureDaily() {           // раз в сутки выдаёт 3 новых случайных задания
    int id = todayId();
    if (id == dailyDayId) return;
    dailyDayId = id;
    struct QP { int type, target, reward; };
    static const QP POOL[6] = {{QT_KILLS, 40, 30}, {QT_KILLS, 100, 70}, {QT_WAVE, 5, 40}, {QT_WAVE, 10, 90}, {QT_DUELWIN, 1, 50}, {QT_HEADSHOT, 15, 45}};
    int idx[6] = {0, 1, 2, 3, 4, 5};
    for (int i = 5; i > 0; i--) { int j = irand(0, i); std::swap(idx[i], idx[j]); }
    for (int i = 0; i < 3; i++) { dailyQ[i].type = POOL[idx[i]].type; dailyQ[i].target = POOL[idx[i]].target; dailyQ[i].reward = POOL[idx[i]].reward; dailyQ[i].progress = 0; dailyQ[i].claimed = false; }
    saveData();
}
static void questProgress(int type, int amount) {     // накопительная цель (убийства, дуэли, хэдшоты)
    ensureDaily();
    for (int i = 0; i < 3; i++) if (dailyQ[i].type == type && !dailyQ[i].claimed) { dailyQ[i].progress = std::min(dailyQ[i].target, dailyQ[i].progress + amount); questCheckComplete(i); }
}
static void questSet(int type, int value) {            // цель-максимум (например, волна)
    ensureDaily();
    for (int i = 0; i < 3; i++) if (dailyQ[i].type == type && !dailyQ[i].claimed) { dailyQ[i].progress = std::max(dailyQ[i].progress, std::min(dailyQ[i].target, value)); questCheckComplete(i); }
}
static void killZombie(int zi, Player* killer) {
    Zombie z = zombies[zi];
    zombies.erase(zombies.begin() + zi);
    const ZKind& k = ZK[z.kind];
    if (z.kind == 4) { Boom b = {z.x, z.y, z.dmg}; booms.push_back(b); }
    if (z.kind == 5) for (int q = 0; q < 4; q++) { Crate cr; cr.x = z.x + rr(-1.f, 1.f); cr.y = z.y + rr(-1.f, 1.f); cr.kind = q == 0 ? 1 : (q == 1 ? 2 : 0); if (G[(int)cr.y * N + (int)cr.x] == 0) crates.push_back(cr); }
    if (killer) { killer->kills++; killer->scrap += (int)(irand(k.sMin, k.sMax) * killer->scrapMul * (bloodNight ? 1.6f : 1.f) + 0.5f); if (killer == P) questProgress(QT_KILLS, 1); }
    if (killer) { killer->combo++; killer->comboT = 3.5f; if (killer->combo >= 3) killer->scrap += killer->combo / 3; }   // серия: бонус лома
    for (std::map<int, Player>::iterator it = players.begin(); it != players.end(); ++it) {
        Player& p = it->second; if (p.dead) continue;
        gainXp(p, &p == killer ? (float)z.xp : std::max(1.f, floorf(z.xp * 0.3f + 0.5f)));
    }
}
static void damageZombie(int zi, float d, Player* pl) {
    zombies[zi].hp -= d; zombies[zi].flash = 0.10f;
    if (zombies[zi].hp <= 0) killZombie(zi, pl);
}
static void checkDuelEnd();
static void hurtPlayer(Player& pl, float d) {
    if (mode != M_PLAY || pl.dead) return;
    if (pl.menu && !peers.empty()) return;
    pl.hp -= d; pl.hurt = 0.35f;
    if (pl.hp <= 0) {
        pl.hp = 0; pl.dead = true; pl.fire = false; flowDirty = true;
        if (players.size() > 1) toast(pl.name + " ПОГИБ!", 2.5f);
        if (duelMode) checkDuelEnd();
        else if (alivePlayers().empty()) gameOver();
    }
}
static void startReload(Player& pl) {
    if (pl.dead || pl.reload > 0 || pl.ammo[pl.weapon] >= mag_size(pl, pl.weapon)) return;
    pl.reload = WEAP[pl.weapon].reload;
}
static int hitBox(const Player& pl, float ang, float pitch, float maxT);      // ломаемые ящики (определены ниже, рядом с декорациями)
static void damageBox(int i, float d, Player* pl);
static void blastBoxes(float x, float y, float r, float dmg, Player* owner);      // взрыв ломает ящики в радиусе
static std::string boxSnapshot();
static void boxSync(int idx, int pct);
static void tryFire(Player& pl) {
    const WeaponDef& w = WEAP[pl.weapon];
    if (pl.fireCd > 0 || pl.reload > 0 || pl.dead) return;
    if (pl.ammo[pl.weapon] <= 0) { startReload(pl); return; }
    pl.ammo[pl.weapon]--; pl.fireCd = w.rate * pl.rateMul; pl.flash = 0.07f;
    float lvlMul = 1.f + 0.15f * pl.wLvl[pl.weapon];    // прокачка оружия за лом: +15% урона за уровень
    if (w.pierce) {      // пробивает всех зомби на линии выстрела
        float a = pl.ang + rr(-w.spread, w.spread), wd = wallDist(pl.x, pl.y, a), c = cosf(a), sn = sinf(a);
        std::vector<std::pair<float, int> > hits;
        { int bi = hitBox(pl, a, pl.pitch, wd); if (bi >= 0) { damageBox(bi, w.dmg * pl.dmgMul * lvlMul, &pl); pl.hit = 0.12f; } }
        for (size_t k = 0; k < zombies.size(); k++) {
            float rx = zombies[k].x - pl.x, ry = zombies[k].y - pl.y, t = rx * c + ry * sn, rz = 0.5f + t * tanf(pl.pitch);
            if (t > 0 && t < wd && fabsf(-rx * sn + ry * c) < zombies[k].r + 0.06f && rz > -0.04f && rz < zombies[k].hs + 0.05f) hits.push_back(std::make_pair(t, zombies[k].id));
        }
        std::sort(hits.begin(), hits.end());
        for (size_t k = 0; k < hits.size(); k++)
            for (size_t zi = 0; zi < zombies.size(); zi++)
                if (zombies[zi].id == hits[k].second) {
                    float rz = 0.5f + hits[k].first * tanf(pl.pitch); bool head = rz >= zombies[zi].hs * HEAD_FROM;
                    damageZombie((int)zi, w.dmg * pl.dmgMul * lvlMul * powf(0.8f, (float)k) * (head ? HEAD_MULT : 1.f), &pl); pl.hit = 0.12f; if (head) pl.headT = 0.35f; break;
                }
        if (duelMode) {
            float t2; bool head2 = false;
            int oid = hitTargetPlayer(pl, a, pl.pitch, &t2, &head2);
            if (oid >= 0) {
                float d = w.dmg * pl.dmgMul * lvlMul * (head2 ? HEAD_MULT : 1.f);
                hurtPlayer(players[oid], d); pl.hit = 0.12f; if (head2) pl.headT = 0.35f;
            }
        }
    } else
    for (int i = 0; i < w.pellets; i++) {
        float a = pl.ang + rr(-w.spread, w.spread), t, pj = pl.pitch + rr(-w.spread, w.spread) * 0.6f; bool head = false;
        int zi = hitTarget(pl, a, pj, &t, &head);
        int bi = hitBox(pl, a, pj, t);      // ящик ближе, чем цель/стена — пуля попадает в него
        if (bi >= 0) {
            float d = w.dmg * pl.dmgMul * lvlMul;
            if (w.pellets > 1) d *= std::max(0.3f, 1.f - t / 9.f);
            damageBox(bi, d, &pl); pl.hit = 0.12f;
        } else if (zi >= 0) {
            float d = w.dmg * pl.dmgMul * lvlMul;
            if (w.pellets > 1) d *= std::max(0.3f, 1.f - t / 9.f);
            if (head) { d *= HEAD_MULT; pl.headT = 0.35f; }
            damageZombie(zi, d, &pl); pl.hit = 0.12f;
        }
        if (duelMode) {
            float t2; bool head2 = false;
            int oid = hitTargetPlayer(pl, a, pj, &t2, &head2);
            if (oid >= 0) {
                float d = w.dmg * pl.dmgMul * lvlMul;
                if (w.pellets > 1) d *= std::max(0.3f, 1.f - t2 / 9.f);
                if (head2) { d *= HEAD_MULT; pl.headT = 0.35f; }
                hurtPlayer(players[oid], d); pl.hit = 0.12f;
            }
        }
    }
    if (pl.ammo[pl.weapon] <= 0) startReload(pl);
}
// ---------- гранаты ----------
static void throwGrenade(Player& pl, int type) {
    if (pl.dead || pl.menu || mode != M_PLAY || type < 0 || type > 1) return;
    if (pl.grenCd > 0) return;
    if (pl.gren[type] <= 0) { toast(type == 0 ? "НЕТ ГРАНАТ" : "НЕТ ОГЛУШАЮЩИХ ГРАНАТ", 1.2f, &pl); return; }
    if (grens.size() >= 24) return;
    pl.gren[type]--; pl.grenCd = 0.6f;
    Gren g; float sp = 8.f;
    g.x = pl.x + cosf(pl.ang) * 0.4f; g.y = pl.y + sinf(pl.ang) * 0.4f;
    if (!freeAt(g.x, g.y, 0.08f, true)) { g.x = pl.x; g.y = pl.y; }
    g.z = 0.5f + pl.jumpZ; g.vx = cosf(pl.ang) * sp; g.vy = sinf(pl.ang) * sp; g.vz = 2.0f + pl.pitch * 6.f;
    g.fuse = 1.8f; g.type = type; g.owner = pl.id; g.id = grenIdCounter++;
    grens.push_back(g);
}
static void detonate(const Gren& g) {
    Player* owner = NULL;
    std::map<int, Player>::iterator oi = players.find(g.owner);
    if (oi != players.end()) owner = &oi->second;
    if (g.type == 0) {
        const float R = GREN_RADIUS;
        for (int zi = (int)zombies.size() - 1; zi >= 0; zi--) {
            float dx = zombies[zi].x - g.x, dy = zombies[zi].y - g.y, d = hypotf(dx, dy);
            if (d > R + zombies[zi].r) continue;
            if (d > 0.6f && wallDist(g.x, g.y, atan2f(dy, dx)) < d - 0.3f) continue;      // стена закрывает от взрыва
            damageZombie(zi, GREN_DMG * (1.f - 0.65f * std::min(1.f, d / R)), owner);
        }
        blastBoxes(g.x, g.y, R, 90.f, owner);      // взрыв ломает ящики
        for (std::map<int, Player>::iterator it = players.begin(); it != players.end(); ++it) {      // осторожно: свой урон
            Player& p = it->second; if (p.dead) continue;
            float dx = p.x - g.x, dy = p.y - g.y, d = hypotf(dx, dy);
            if (d > R) continue;
            if (d > 0.6f && wallDist(g.x, g.y, atan2f(dy, dx)) < d - 0.3f) continue;
            hurtPlayer(p, 45.f * (1.f - d / R));
        }
    } else {
        for (size_t i = 0; i < zombies.size(); i++) zombies[i].stun = STUN_TIME;      // ВСЕ зомби на карте
        if (owner) toast(fmt("ЗОМБИ ОГЛУШЕНЫ НА %d С", (int)STUN_TIME), 1.8f, owner);
    }
}
static void updateGrenades(float dt) {
    for (size_t i = 0; i < grens.size();) {
        Gren& g = grens[i];
        g.fuse -= dt; g.vz -= 9.f * dt; g.z += g.vz * dt;
        if (g.z < 0.06f) {
            g.z = 0.06f; g.vz = g.vz < -0.8f ? -g.vz * 0.45f : 0.f;
            float f = expf(-3.f * dt); g.vx *= f; g.vy *= f;
        }
        float nx = g.x + g.vx * dt, ny = g.y + g.vy * dt;
        if (freeAt(nx, g.y, 0.08f, true)) g.x = nx; else g.vx = -g.vx * 0.5f;
        if (freeAt(g.x, ny, 0.08f, true)) g.y = ny; else g.vy = -g.vy * 0.5f;
        if (g.fuse <= 0) { Gren c = g; grens.erase(grens.begin() + i); detonate(c); } else i++;
    }
}
static std::string grenSnapshot() {
    std::string s = fmt("%d ", (int)grens.size());
    for (size_t i = 0; i < grens.size(); i++) s += fmt("%d %.2f %.2f %.2f %d ", grens[i].id, grens[i].x, grens[i].y, grens[i].z, grens[i].type);
    return s;
}
static void switchWeapon(Player& pl) {
    if (pl.dead) return;
    for (int k = 1; k <= NW; k++) {
        int i = (pl.weapon + k) % NW;
        if (pl.unl[i]) { pl.weapon = i; pl.reload = 0; toast(WEAP[i].name, 1.2f, &pl); return; }
    }
}
static void equipWeapon(Player& pl, int i) {
    if (pl.dead || i < 0 || i >= NW || !pl.unl[i]) return;
    pl.weapon = i; pl.reload = 0;
}
static void buyItem(Player& pl, int idx) {
    if (pl.dead) return;
    if (idx == 100) {
        if (pl.hp >= pl.maxhp - 0.5f) { toast("ЗДОРОВЬЕ УЖЕ ПОЛНОЕ", 1.5f, &pl); return; }
        if (pl.scrap < MEDKIT_PRICE) { toast(fmt("НУЖНО ЛОМА: %d", MEDKIT_PRICE), 1.5f, &pl); return; }
        pl.scrap -= MEDKIT_PRICE; pl.hp = std::min(pl.maxhp, pl.hp + 50); toast("АПТЕЧКА: +50 HP", 1.5f, &pl);
        return;
    }
    if (idx == 101 || idx == 102) {
        int t = idx - 101;
        if (pl.gren[t] >= GREN_MAX) { toast("ПОЛНЫЙ ЗАПАС ГРАНАТ", 1.5f, &pl); return; }
        if (pl.scrap < GREN_PRICE[t]) { toast(fmt("НУЖНО ЛОМА: %d", GREN_PRICE[t]), 1.5f, &pl); return; }
        pl.scrap -= GREN_PRICE[t]; pl.gren[t]++;
        toast(t == 0 ? "КУПЛЕНО: ГРАНАТА" : "КУПЛЕНО: ОГЛУШАЮЩАЯ ГРАНАТА", 1.5f, &pl);
        return;
    }
    if (idx < 0 || idx >= NW) return;
    if (pl.unl[idx]) { equipWeapon(pl, idx); return; }
    if (pl.scrap < WEAP[idx].price) { toast(fmt("НУЖНО ЛОМА: %d", WEAP[idx].price), 1.5f, &pl); return; }
    pl.scrap -= WEAP[idx].price; pl.unl[idx] = true; pl.ammo[idx] = mag_size(pl, idx);
    equipWeapon(pl, idx);
    toast(std::string("КУПЛЕНО: ") + WEAP[idx].name, 2.f, &pl);
}
static void upgradeWeapon(Player& pl, int idx) {          // прокачка оружия за лом (урон + вместимость магазина)
    if (pl.dead || idx < 0 || idx >= NW || !pl.unl[idx]) return;
    if (pl.wLvl[idx] >= WLVL_MAX) { toast("ОРУЖИЕ УЖЕ МАКС. УРОВНЯ", 1.5f, &pl); return; }
    int cost = wUpgCost(idx, pl.wLvl[idx]);
    if (pl.scrap < cost) { toast(fmt("НУЖНО ЛОМА: %d", cost), 1.5f, &pl); return; }
    pl.scrap -= cost; pl.wLvl[idx]++; pl.ammo[idx] = mag_size(pl, idx);
    toast(fmt("%s УЛУЧШЕНО ДО +%d", WEAP[idx].name, pl.wLvl[idx]), 2.f, &pl);
}
static void buildOrRepair(Player& pl) {
    if (pl.dead) return;
    float dx = cosf(pl.ang), dy = sinf(pl.ang);
    int pcell = (int)pl.y * N + (int)pl.x;
    for (int k = 1; k <= 26; k++) {
        float t = k * 0.1f;
        int idx = (int)(pl.y + dy * t) * N + (int)(pl.x + dx * t);
        if (idx == pcell) continue;
        if (G[idx] == 2) {
            float mx = bmx[idx];
            if (bhp[idx] >= mx - 1) { toast("БАРРИКАДА ЦЕЛАЯ", 1.2f, &pl); return; }
            if (pl.scrap < 1) { toast("НЕТ ЛОМА ДЛЯ РЕМОНТА", 1.5f, &pl); return; }
            pl.scrap--; bhp[idx] = std::min(mx, bhp[idx] + mx * 0.4f); toast("ПОЧИНЕНО", 0.8f, &pl); return;
        }
        if (G[idx] != 0) break;
    }
    int cx = (int)(pl.x + dx * 1.35f), cy = (int)(pl.y + dy * 1.35f), idx = cy * N + cx;
    if (idx == pcell || !(cx >= 1 && cx <= N - 2 && cy >= 1 && cy <= N - 2)) { toast("СЮДА НЕЛЬЗЯ", 1.2f, &pl); return; }
    if (G[idx] != 0) { toast("КЛЕТКА ЗАНЯТА", 1.2f, &pl); return; }
    if (pl.scrap < pl.cost) { toast(fmt("НУЖНО ЛОМА: %d", pl.cost), 1.5f, &pl); return; }
    for (size_t i = 0; i < zombies.size(); i++)
        if (fabsf(zombies[i].x - (cx + 0.5f)) < 0.8f && fabsf(zombies[i].y - (cy + 0.5f)) < 0.8f) { toast("МЕШАЕТ ЗОМБИ!", 1.2f, &pl); return; }
    for (std::map<int, Player>::iterator it = players.begin(); it != players.end(); ++it)
        if (!it->second.dead && fabsf(it->second.x - (cx + 0.5f)) < 0.8f && fabsf(it->second.y - (cy + 0.5f)) < 0.8f) { toast("МЕШАЕТ ИГРОК!", 1.2f, &pl); return; }
    pl.scrap -= pl.cost; G[idx] = 2; bhp[idx] = bmx[idx] = wmax(pl); mmDirty = true; flowDirty = true;
    if (&pl == P) playSound(S_BUILD, 0.9f); else playAt(S_BUILD, pl.x, pl.y, 0.9f);
}

static void spawnZombie(int force = -1) {
    int n = std::max(1, (int)alivePlayers().size());
    int kind = 0;
    if (force >= 0) kind = force;
    else {
        float r = frand();
        float p2 = wave >= 4 ? std::min(0.2f, 0.05f + 0.02f * wave) : 0.f, p3 = wave >= 3 ? std::min(0.16f, 0.04f + 0.02f * (wave - 2)) : 0.f;
        float p4 = wave >= 4 ? std::min(0.14f, 0.03f + 0.02f * (wave - 3)) : 0.f, p1 = wave >= 2 ? std::min(0.32f, 0.10f + 0.02f * wave) : 0.f;
        if (r < p2) kind = 2; else if (r < p2 + p3) kind = 3; else if (r < p2 + p3 + p4) kind = 4; else if (r < p2 + p3 + p4 + p1) kind = 1;
    }
    int cell = -1;
    for (int t = 0; t < 25; t++) {
        int c = spawnCells[irand(0, (int)spawnCells.size() - 1)]; float d;
        Player* pl = nearestPlayer(c % N + 0.5f, c / N + 0.5f, &d);
        if ((!pl || d > 12) && !decoBlocks(c % N + 0.5f, c / N + 0.5f, 0.25f)) { cell = c; break; }
    }
    if (cell < 0) cell = spawnCells[irand(0, (int)spawnCells.size() - 1)];
    const ZKind& k = ZK[kind];
    Zombie z; z.id = ++zidc; z.kind = kind; z.x = cell % N + 0.5f; z.y = cell / N + 0.5f;
    float bossScale = kind == 5 ? (1.f + 0.30f * (wave / 5 - 1)) : 1.f;
    float bnHp = bloodNight ? 1.25f : 1.f, bnSpd = bloodNight ? 1.15f : 1.f, bnDmg = bloodNight ? 1.2f : 1.f;
    z.maxhp = k.hp * (1.f + 0.10f * (wave - 1)) * (1.f + 0.15f * (n - 1)) * DHF[difficulty] * bossScale * bnHp; z.hp = z.maxhp;
    z.spd = k.spd * rr(0.9f, 1.1f) * (1.f + 0.02f * wave) * bnSpd; z.dmg = k.dmg * (1.f + 0.05f * (wave - 1)) * DDF[difficulty] * bnDmg;
    z.xp = k.xp; z.r = k.r; z.hs = k.hs; z.cd = rr(0.2f, 0.8f); z.spitCd = rr(0.8f, 2.2f); z.slamCd = rr(3.f, 5.f);
    zombies.push_back(z);
}

static void explodeAt(const Boom& b) {          // взрыв подрывника: урон игрокам, баррикадам и соседним зомби
    const float R = 2.5f;
    for (std::map<int, Player>::iterator it = players.begin(); it != players.end(); ++it) {
        Player& p = it->second; if (p.dead) continue;
        float d = hypotf(p.x - b.x, p.y - b.y);
        if (d < R) hurtPlayer(p, b.dmg * (1.f - d / R));
    }
    int cx = (int)b.x, cy = (int)b.y;
    for (int dy = -3; dy <= 3; dy++)
        for (int dx = -3; dx <= 3; dx++) {
            int nx = cx + dx, ny = cy + dy; if (nx < 1 || ny < 1 || nx >= N - 1 || ny >= N - 1) continue;
            int idx = ny * N + nx; if (G[idx] != 2) continue;
            float d = hypotf(nx + 0.5f - b.x, ny + 0.5f - b.y);
            if (d < R + 0.4f) {
                bhp[idx] -= 95.f * (1.f - d / (R + 0.4f));
                if (bhp[idx] <= 0) { G[idx] = 0; bhp[idx] = bmx[idx] = 0; mmDirty = true; flowDirty = true; }
            }
        }
    std::vector<int> ids;
    for (size_t i = 0; i < zombies.size(); i++) if (hypotf(zombies[i].x - b.x, zombies[i].y - b.y) < R) ids.push_back(zombies[i].id);
    for (size_t k = 0; k < ids.size(); k++)
        for (size_t i = 0; i < zombies.size(); i++)
            if (zombies[i].id == ids[k]) { float d = hypotf(zombies[i].x - b.x, zombies[i].y - b.y); damageZombie((int)i, 55.f * (1.f - d / R), NULL); break; }
}
static void processBooms() { int guard = 0; while (!booms.empty() && guard++ < 40) { Boom b = booms.back(); booms.pop_back(); explodeAt(b); } booms.clear(); }
static void updateSpits(float dt) {
    for (size_t i = 0; i < spits.size();) {
        Spit& sp = spits[i]; sp.x += sp.vx * dt; sp.y += sp.vy * dt; sp.life -= dt;
        bool kill = sp.life <= 0 || sp.x < 1 || sp.y < 1 || sp.x >= N - 1 || sp.y >= N - 1;
        if (!kill) {
            int c = (int)sp.y * N + (int)sp.x;
            if (G[c] == 1 || G[c] == 3) kill = true;
            else if (G[c] == 2) { bhp[c] -= 14.f; if (bhp[c] <= 0) { G[c] = 0; bhp[c] = bmx[c] = 0; mmDirty = true; flowDirty = true; } kill = true; }
        }
        if (!kill)
            for (std::map<int, Player>::iterator it = players.begin(); it != players.end(); ++it) {
                Player& p = it->second; if (p.dead) continue;
                if (hypotf(p.x - sp.x, p.y - sp.y) < 0.45f) { hurtPlayer(p, sp.dmg); kill = true; break; }
            }
        if (kill) { spits[i] = spits.back(); spits.pop_back(); } else i++;
    }
}

static void updateZombies(float dt) {
    size_t n = zombies.size();
    for (size_t zi = 0; zi < n; zi++) {
        Zombie& z = zombies[zi];
        z.cd -= dt; if (z.flash > 0) z.flash -= dt; if (z.slamFlash > 0) z.slamFlash -= dt;
        if (z.stun > 0) { z.stun -= dt; continue; }      // оглушён: не ходит, не бьёт, не плюётся
        float d; Player* pl = nearestPlayer(z.x, z.y, &d);
        if (!pl) continue;
        if (z.kind == 5) {         // босс бьёт по земле
            z.slamCd -= dt;
            if (z.slamCd <= 0 && d < 3.3f) {
                z.slamCd = 6.5f; z.slamFlash = 0.45f;
                for (std::map<int, Player>::iterator it = players.begin(); it != players.end(); ++it) {
                    Player& p = it->second; if (p.dead) continue;
                    float dd = hypotf(p.x - z.x, p.y - z.y);
                    if (dd < 3.6f) hurtPlayer(p, z.dmg * 0.7f * (1.f - dd / 3.9f));
                }
            }
        }
        if (z.kind == 4 && d < 1.4f) { z.boom = true; continue; }
        if (z.kind == 3 && d < 7.5f && d > 1.8f) {           // плевака стоит на расстоянии и плюётся
            z.spitCd -= dt;
            float a = atan2f(pl->y - z.y, pl->x - z.x);
            if (z.spitCd <= 0 && wallDist(z.x, z.y, a) > d - 0.4f) {
                Spit sp = {z.x, z.y, cosf(a) * 6.f, sinf(a) * 6.f, 2.2f, z.dmg};
                spits.push_back(sp); z.spitCd = 2.6f;
            }
            continue;
        }
        if (d < 1.05f) { if (z.cd <= 0) { hurtPlayer(*pl, z.dmg); z.cd = 0.9f; } continue; }
        int ci = (int)z.y * N + (int)z.x;
        float tx = pl->x, ty = pl->y; int attack = -1;
        if (flowv[ci] > 1 && flowv[ci] < INF) {
            int best = ci, bv = flowv[ci];
            for (int k = 0; k < nnei[ci]; k++) { int j = nei[ci][k]; if (flowv[j] < bv) { bv = flowv[j]; best = j; } }
            if (best != ci) {
                float bx = best % N + 0.5f, by = best / N + 0.5f; tx = bx; ty = by;
                if (G[best] == 2 && hypotf(bx - z.x, by - z.y) < 0.95f) attack = best;
            }
        }
        if (attack >= 0) {
            if (z.kind == 4) { z.boom = true; continue; }
            if (z.cd <= 0) {
                z.cd = 0.9f; bhp[attack] -= z.dmg * 2.f;
                if (bhp[attack] <= 0) { G[attack] = 0; bhp[attack] = bmx[attack] = 0; mmDirty = true; flowDirty = true; toast("БАРРИКАДУ РАЗРУШИЛИ!", 1.5f); }
            }
            continue;
        }
        float dx = tx - z.x, dy = ty - z.y, dd = hypotf(dx, dy);
        if (dd > 0.02f) { float step = z.spd * dt; tryMove(z.x, z.y, z.x + dx / dd * step, z.y + dy / dd * step, 0.22f, false, true); }
    }
    for (int i = (int)zombies.size() - 1; i >= 0; i--)
        if (zombies[i].boom) { Boom b = {zombies[i].x, zombies[i].y, zombies[i].dmg}; booms.push_back(b); zombies.erase(zombies.begin() + i); }
    n = zombies.size();
    for (size_t i = 0; i < n; i++)
        for (size_t j = i + 1; j < n; j++) {
            Zombie &a = zombies[i], &b = zombies[j];
            float dx = a.x - b.x;
            if (dx > -0.5f && dx < 0.5f) {
                float dy = a.y - b.y;
                if (dy > -0.5f && dy < 0.5f) {
                    float d2 = dx * dx + dy * dy;
                    if (d2 > 0.0001f && d2 < 0.25f) {
                        float d = sqrtf(d2), p = (0.5f - d) * 0.5f, ux = dx / d * p, uy = dy / d * p;
                        tryMove(a.x, a.y, a.x + ux, a.y + uy, 0.22f, false, true);
                        tryMove(b.x, b.y, b.x - ux, b.y - uy, 0.22f, false, true);
                    }
                }
            }
        }
}

static void startWave() {
    wave++; prep = false;
    if (!duelMode) questSet(QT_WAVE, wave);
    int n = std::max(1, (int)players.size());
    toSpawn = (int)((5 + wave * 3) * (1.f + 0.55f * (n - 1)) * DNF[difficulty]);
    bloodNight = frand() < 0.10f;                      // 10% шанс на кровавую ночь
    if (bloodNight) toSpawn = (int)(toSpawn * 1.4f);
    spawnT = 1.f; toast(fmt("ВОЛНА %d!", wave), 2.5f);
    if (wave % 5 == 0) { toSpawn = (int)(toSpawn * 0.7f); spawnZombie(5); toast(fmt("ВОЛНА %d: БОСС - ТИРАН!", wave), 3.5f); }
    if (bloodNight) toast("КРОВАВАЯ НОЧЬ! ЗОМБИ ЯРОСТНЕЕ, НО БОЛЬШЕ ЛОМА", 3.5f);
}
static void waveCleared() {
    prep = true; ptimer = 30.f;
    for (std::map<int, Player>::iterator it = players.begin(); it != players.end(); ++it) {
        Player& p = it->second;
        if (p.dead) {
            p.dead = false; p.hp = p.maxhp * 0.5f; p.x = C0 + 0.5f + rr(-1.5f, 1.5f); p.y = C0 + 0.5f + rr(-1.5f, 1.5f);
            toast("ТЕБЯ ПОДНЯЛИ! ДЕРЖИСЬ!", 2.5f, &p);
        } else p.hp = std::min(p.maxhp, p.hp + p.maxhp * 0.25f);
        p.scrap += 8 + wave * 2 + (wave % 5 == 0 ? 25 : 0);
        for (int i = 0; i < NW; i++) p.ammo[i] = mag_size(p, i);
    }
    flowDirty = true;
    spawnCrates(5 + wave + 2 * ((int)players.size() - 1));
    if (wave > bestWave) { bestWave = wave; newRecord = true; saveData(); }
    toast(fmt("ВОЛНА %d ОТБИТА! ЧИНИ СТЕНЫ, СОБИРАЙ ЯЩИКИ", wave), 4.f);
}

static void spawnBurst(float x, float y, float z, int n, float spd, int mode);
static const float JUMP_V0 = 3.0f, JUMP_G = 9.4f;
static void doJump(Player& pl) {
    if (pl.dead || pl.menu) return;
    if (pl.jumpZ > 0.01f || pl.jumpV > 0.01f) return;      // уже в воздухе
    pl.jumpV = JUMP_V0;
    if (&pl == P) playSound(S_JUMP, 0.55f); else playAt(S_JUMP, pl.x, pl.y, 0.6f);
}
static void updateJumpPhysics(Player& pl, float dt) {
    if (pl.jumpZ <= 0.f && pl.jumpV <= 0.f) return;
    pl.jumpV -= JUMP_G * dt; pl.jumpZ += pl.jumpV * dt;
    if (pl.jumpZ <= 0.f) {
        pl.jumpZ = 0.f;
        if (pl.jumpV < -1.2f) {
            if (&pl == P) { playSound(S_LAND, 0.5f); spawnBurst(pl.x, pl.y, 0.12f, 6, 1.6f, 2); }
            else playAt(S_LAND, pl.x, pl.y, 0.45f);
        }
        pl.jumpV = 0.f;
    }
}
static void updatePlayer(Player& pl, float dt) {
    updateJumpPhysics(pl, dt);
    pl.grenCd = std::max(0.f, pl.grenCd - dt); pl.fireCd = std::max(0.f, pl.fireCd - dt); pl.flash = std::max(0.f, pl.flash - dt);
    pl.hurt = std::max(0.f, pl.hurt - dt); pl.hit = std::max(0.f, pl.hit - dt); pl.headT = std::max(0.f, pl.headT - dt);
    pl.comboT = std::max(0.f, pl.comboT - dt); if (pl.comboT <= 0) pl.combo = 0;
    if (pl.dead) return;
    if (pl.reload > 0) { pl.reload -= dt; if (pl.reload <= 0) { pl.reload = 0; pl.ammo[pl.weapon] = mag_size(pl, pl.weapon); } }
    if (pl.regen > 0 && pl.hp < pl.maxhp) pl.hp = std::min(pl.maxhp, pl.hp + pl.regen * dt);
    bool fire = pl.fire && !pl.menu;
    if (!fire && pl.autoF && pl.fireCd <= 0 && pl.reload <= 0 && !zombies.empty() && !pl.menu) {
        if (hitTarget(pl, pl.ang, pl.pitch, NULL, NULL) >= 0) fire = true;
    }
    if (fire) tryFire(pl);
    for (size_t i = 0; i < crates.size();) {
        if (hypotf(crates[i].x - pl.x, crates[i].y - pl.y) < 0.8f) {
            int k = crates[i].kind; crates.erase(crates.begin() + i);
            if (k == 0) { int n = (int)(irand(6, 12) * pl.scrapMul); pl.scrap += n; toast(fmt("+%d ЛОМА", n), 1.2f, &pl); }
            else if (k == 1) { pl.hp = std::min(pl.maxhp, pl.hp + 35); toast("АПТЕЧКА +35 HP", 1.2f, &pl); }
            else { gainXp(pl, 30); toast("+30 ОПЫТА", 1.2f, &pl); }
        } else i++;
    }
    if (pl.pending > 0 && !pl.menu) openLevelUp(pl);
}

static void updateDuelBot(float dt) {      // ИИ соперника в дуэли: держит дистанцию, стрейфит и стреляет, когда видит игрока; сила зависит от duelBotLevel
    if (!players.count(1) || !P || P->dead) { if (players.count(1)) players[1].fire = false; return; }
    Player& b = players[1];
    if (b.dead) { b.fire = false; return; }
    const BotLevelDef& bl = BOTLV[std::max(0, std::min(3, duelBotLevel))];
    float dx = P->x - b.x, dy = P->y - b.y, dist = hypotf(dx, dy), ta = atan2f(dy, dx);
    float da = ta - b.ang; while (da > 3.14159f) da -= 6.28318f; while (da < -3.14159f) da += 6.28318f;
    b.ang += std::max(-bl.turnRate * dt, std::min(bl.turnRate * dt, da));
    b.pitch = 0;
    float desired = bl.engageDist * 0.4f, mvx = 0, mvy = 0;
    if (dist > desired + 0.5f) { mvx = cosf(ta); mvy = sinf(ta); }
    else if (dist < desired - 0.5f) { mvx = -cosf(ta); mvy = -sinf(ta); }
    else { mvx = -sinf(ta); mvy = cosf(ta); }        // стрейф по кругу вокруг игрока
    float spd = 3.0f * b.spdMul * dt, nx = b.x + mvx * spd, ny = b.y + mvy * spd;
    if (G[(int)b.y * N + (int)nx] != 1) b.x = nx;
    if (G[(int)ny * N + (int)b.x] != 1) b.y = ny;
    bool aligned = fabsf(da) < bl.aimTol;
    float wd = wallDist(b.x, b.y, ta);
    b.fire = aligned && dist < wd + 0.3f && dist < bl.engageDist;
    if (b.reload <= 0 && b.ammo[b.weapon] <= 0) startReload(b);
}
static void simUpdate(float dt) {
    if (duelMode && duelBot) updateDuelBot(dt);
    std::vector<Player*> pv;
    for (std::map<int, Player>::iterator it = players.begin(); it != players.end(); ++it) pv.push_back(&it->second);
    for (size_t i = 0; i < pv.size(); i++) updatePlayer(*pv[i], dt);
    if (mode != M_PLAY) return;
    if (!duelMode) {
        if (prep) { ptimer -= dt; if (ptimer <= 0) startWave(); }
        else {
            if (toSpawn > 0) {
                spawnT -= dt;
                if (spawnT <= 0 && (int)zombies.size() < MAX_ZOMBIES) {
                    spawnZombie(); toSpawn--;
                    int n = std::max(1, (int)players.size());
                    spawnT = std::max(0.3f, (1.6f - 0.08f * wave) / (1.f + 0.3f * (n - 1)));
                }
            } else if (zombies.empty()) waveCleared();
        }
    }
    flowT -= dt;
    if (flowDirty || flowT <= 0) computeFlow();
    updateZombies(dt);
    updateSpits(dt);
    updateGrenades(dt);
    processBooms();
    leftZ = (int)zombies.size() + toSpawn;
}

// ============================ СЕТЬ (игровая часть) ============================
static std::string snapshotFor(Peer& pk);
static void awardDeathCoins() {         // монеты за проигранную игру: зависят от волны и числа убитых зомби
    lastCoinsGain = std::max(5, P->kills / 3 + wave * 4);
    coins += lastCoinsGain; saveData();
}
static void gameOver() {
    mode = M_DEAD; deadT = 1.2f;
    if (wave > bestWave) { bestWave = wave; newRecord = true; saveData(); }
    awardDeathCoins();
    if (netRole == R_HOST) for (size_t i = 0; i < peers.size(); i++) netSend(peers[i], snapshotFor(peers[i]));
}
static void checkDuelEnd() {         // дуэль: раунд оканчивается, как только один из двух бойцов погиб
    if (mode != M_PLAY) return;
    int loserId = -1, winnerId = -1;
    for (std::map<int, Player>::iterator it = players.begin(); it != players.end(); ++it) {
        if (it->second.dead) loserId = it->first; else winnerId = it->first;
    }
    if (loserId < 0) return;
    if (winnerId == 0 || winnerId == 1) duelScore[winnerId]++;
    bool matchOver = winnerId >= 0 && duelScore[winnerId] >= DUEL_ROUNDS_TO_WIN;
    if (matchOver) {
        mode = M_DEAD; deadT = 1.2f;
        bool iWon = (winnerId == P->id);
        lastCoinsGain = iWon ? 90 : 25; coins += lastCoinsGain;
        if (duelBot) { int lv = std::max(0, std::min(3, duelBotLevel)); if (iWon) duelWinsBot[lv]++; else duelLossBot[lv]++; }
        else { if (iWon) duelWinsFriend++; else duelLossFriend++; }
        if (iWon) questProgress(QT_DUELWIN, 1);
        saveData();
    } else {
        duelRoundNum++;
        for (std::map<int, Player>::iterator it = players.begin(); it != players.end(); ++it) {
            Player& pp = it->second;
            pp.dead = false; pp.hp = pp.maxhp; pp.fire = false; pp.reload = 0; pp.jumpZ = 0; pp.jumpV = 0;
            for (int wi = 0; wi < NW; wi++) if (pp.unl[wi]) pp.ammo[wi] = mag_size(pp, wi);
        }
        placeDuelPlayers();
        toast(fmt("РАУНД %d   СЧЁТ %d:%d", duelRoundNum, duelScore[0], duelScore[1]), 3.f);
    }
    if (netRole == R_HOST) for (size_t i = 0; i < peers.size(); i++) netSend(peers[i], snapshotFor(peers[i]));
}

static void shutdownNet() {
    ambientStop();
    for (size_t i = 0; i < peers.size(); i++) netClose(peers[i]);
    peers.clear();
    if (linked) { netClose(link_); linked = false; }
    if (lsock >= 0) { ::close(lsock); lsock = -1; }
    if (bsock >= 0) { ::close(bsock); bsock = -1; }
    if (dsock >= 0) { ::close(dsock); dsock = -1; }
    netRole = R_SOLO;
}

static bool startHost() {
    shutdownNet();
    lsock = socket(AF_INET, SOCK_STREAM, 0);
    int one = 1; setsockopt(lsock, SOL_SOCKET, SO_REUSEADDR, &one, sizeof one);
    sockaddr_in a; memset(&a, 0, sizeof a); a.sin_family = AF_INET; a.sin_addr.s_addr = htonl(INADDR_ANY); a.sin_port = htons(PORT);
    if (lsock < 0 || bind(lsock, (sockaddr*)&a, sizeof a) != 0 || listen(lsock, 4) != 0) {
        msgStr = "НЕ УДАЛОСЬ ОТКРЫТЬ ПОРТ"; if (lsock >= 0) { ::close(lsock); lsock = -1; } mode = M_MENU; return false;
    }
    setNB(lsock);
    bsock = socket(AF_INET, SOCK_DGRAM, 0);
    if (bsock >= 0) { setsockopt(bsock, SOL_SOCKET, SO_BROADCAST, &one, sizeof one); setNB(bsock); }
    netRole = R_HOST; hostIp = localIp(); discT = 0;
    newGame();
    toast("ИГРА СОЗДАНА! ДРУЗЬЯ ВВОДЯТ IP: " + hostIp, 6.f);
    return true;
}

static void startDuelBot() {          // дуэль против бота: полностью локально, без сети
    const BotLevelDef& bl = BOTLV[std::max(0, std::min(3, duelBotLevel))];
    shutdownNet(); duelMode = true; duelBot = true; duelScore[0] = duelScore[1] = 0; duelRoundNum = 1; newGame();
    prep = false; ptimer = 0; toSpawn = 0; zombies.clear();
    players[1] = newPlayer(1); players[1].name = fmt("БОТ (%s)", bl.name);
    players[1].unl[bl.weapon] = true; players[1].weapon = bl.weapon; players[1].ammo[bl.weapon] = mag_size(players[1], bl.weapon);
    players[1].maxhp = bl.hp; players[1].hp = bl.hp; players[1].spdMul = bl.spdMul; players[1].dmgMul = bl.dmgMul;
    placeDuelPlayers();
    toastS.clear(); toastT = 0; toast(fmt("РАУНД 1 ИЗ %d! СЛОЖНОСТЬ: %s", DUEL_ROUNDS_TO_WIN * 2 - 1, bl.name), 3.f);
}
static void startDuelHost() {         // дуэль с другом: та же сеть, что и в коопе, но бой друг против друга
    duelMode = true; duelBot = false; duelScore[0] = duelScore[1] = 0; duelRoundNum = 1;
    if (startHost()) { prep = false; ptimer = 0; toSpawn = 0; zombies.clear(); placeDuelPlayers(); toastS.clear(); toastT = 0; toast("ДУЭЛЬ: ЖДЁМ СОПЕРНИКА. IP: " + hostIp, 6.f); }
    else duelMode = false;
}
static void openJoin() {
    shutdownNet(); mode = M_JOIN; found.clear(); msgStr.clear();
    dsock = socket(AF_INET, SOCK_DGRAM, 0);
    if (dsock >= 0) {
        int one = 1; setsockopt(dsock, SOL_SOCKET, SO_REUSEADDR, &one, sizeof one);
#ifdef SO_REUSEPORT
        setsockopt(dsock, SOL_SOCKET, SO_REUSEPORT, &one, sizeof one);
#endif
        sockaddr_in a; memset(&a, 0, sizeof a); a.sin_family = AF_INET; a.sin_addr.s_addr = htonl(INADDR_ANY); a.sin_port = htons(DISC_PORT);
        if (bind(dsock, (sockaddr*)&a, sizeof a) != 0) { ::close(dsock); dsock = -1; } else setNB(dsock);
    }
}

static void connectTo(const std::string& ip) {
    if (ip.empty()) { msgStr = "ВВЕДИ IP-АДРЕС"; return; }
    msgStr = "ПОДКЛЮЧАЮСЬ...";
    int s = socket(AF_INET, SOCK_STREAM, 0);
    sockaddr_in a; memset(&a, 0, sizeof a); a.sin_family = AF_INET; a.sin_port = htons(PORT);
    if (s < 0 || inet_pton(AF_INET, ip.c_str(), &a.sin_addr) != 1) { msgStr = "НЕВЕРНЫЙ IP-АДРЕС"; if (s >= 0) ::close(s); return; }
    setNB(s);
    int r = connect(s, (sockaddr*)&a, sizeof a);
    if (r != 0 && errno != EINPROGRESS) { msgStr = "НЕ УДАЛОСЬ ПОДКЛЮЧИТЬСЯ"; ::close(s); return; }
    if (r != 0) {
        fd_set ws; FD_ZERO(&ws); FD_SET(s, &ws); timeval tv; tv.tv_sec = 3; tv.tv_usec = 500000;
        int e = 1;
        if (select(s + 1, NULL, &ws, NULL, &tv) > 0) { socklen_t l = sizeof e; getsockopt(s, SOL_SOCKET, SO_ERROR, &e, &l); }
        if (e != 0) { msgStr = "НЕ УДАЛОСЬ ПОДКЛЮЧИТЬСЯ"; ::close(s); return; }
    }
    int one = 1; setsockopt(s, IPPROTO_TCP, TCP_NODELAY, &one, sizeof one);
    link_ = Peer(); link_.fd = s; linked = true; netRole = R_CLIENT; waitT = 4.f; saveData();
}

static void hostAccept() {
    if (lsock < 0 || mode != M_PLAY) return;
    for (int k = 0; k < 4; k++) {
        int s = accept(lsock, NULL, NULL);
        if (s < 0) return;
        setNB(s);
        int one = 1; setsockopt(s, IPPROTO_TCP, TCP_NODELAY, &one, sizeof one);
        Peer pk; pk.fd = s;
        int pid = -1;
        if (!(duelMode && players.size() >= 2)) for (int i = 1; i < MAX_PLAYERS; i++) if (!players.count(i)) { pid = i; break; }
        if (pid < 0) { netSend(pk, "F"); netClose(pk); continue; }
        pk.pid = pid;
        Player pl = newPlayer(pid);
        int sum = 0; for (std::map<int, Player>::iterator it = players.begin(); it != players.end(); ++it) sum += it->second.level;
        pl.level = std::max(1, sum / (int)players.size() - 1); pl.need = 60.f + 45.f * pl.level;
        players[pid] = pl; flowDirty = true;
        if (duelMode) placeDuelPlayers();
        P = &players[meId];
        std::string g; for (int i = 0; i < N * N; i++) g += (char)('0' + G[i]);
        peers.push_back(pk);
        netSend(peers.back(), fmt("H %d %d ", pid, wave) + g);
        toast(pl.name + " ПОДКЛЮЧИЛСЯ", 2.5f);
    }
}

static void hostMsg(Peer& pk, const std::string& m) {
    std::map<int, Player>::iterator it = players.find(pk.pid);
    if (it == players.end() || m.empty()) return;
    Player& pl = it->second;
    if (m[0] == 'I') {
        float x, y, a, pit = 0; int f, au;
        if (sscanf(m.c_str() + 1, "%f %f %f %d %d %f", &x, &y, &a, &f, &au, &pit) >= 5) {
            x = std::min(N - 1.3f, std::max(1.3f, x)); y = std::min(N - 1.3f, std::max(1.3f, y));
            if (!pl.dead && !pl.menu && fabsf(x - pl.x) < 3 && fabsf(y - pl.y) < 3 && freeAt(x, y, 0.2f, pl.jumpZ > 0.12f)) { pl.x = x; pl.y = y; }
            pl.ang = a; pl.fire = f != 0; pl.autoF = au != 0; pl.pitch = std::max(-PITCH_MAX, std::min(PITCH_MAX, pit));
        }
    } else if (m[0] == 'A') {
        std::string k = m.size() > 2 ? m.substr(2) : "";
        if (k == "build") buildOrRepair(pl);
        else if (k == "reload") startReload(pl);
        else if (k == "weapon") switchWeapon(pl);
        else if (k == "start") { if (prep && !pl.dead) startWave(); }
        else if (k == "jump") doJump(pl);
        else if (k == "gren0") throwGrenade(pl, 0);
        else if (k == "gren1") throwGrenade(pl, 1);
    } else if (m[0] == 'B') {
        buyItem(pl, atoi(m.c_str() + 1));
    } else if (m[0] == 'E') {
        equipWeapon(pl, atoi(m.c_str() + 1));
    } else if (m[0] == 'U') {
        upgradeWeapon(pl, atoi(m.c_str() + 1));
    } else if (m[0] == 'C') {
        if (!pl.perkSet) { pl.perkSet = true; applyPerkId(pl, std::max(0, std::min(3, atoi(m.c_str() + 1)))); }
    } else if (m[0] == 'K') {
        int u = atoi(m.c_str() + 1); applyUpgrade(pl, u);
    }
}

static std::string snapshotFor(Peer& pk) {
    std::string s = fmt("S %d %d %.1f %d %d %d %d %d %d ", wave, prep ? 1 : 0, ptimer, leftZ, mode == M_DEAD ? 1 : 0, duelMode ? 1 : 0, duelScore[0], duelScore[1], duelRoundNum);
    s += fmt("%d ", (int)players.size());
    for (std::map<int, Player>::iterator it = players.begin(); it != players.end(); ++it) {
        Player& p = it->second;
        s += fmt("%d %.2f %.2f %d %d %d %.2f ", p.id, p.x, p.y, p.dead ? 1 : 0, p.flash > 0 ? 1 : 0, p.weapon, p.jumpZ);
    }
    s += fmt("%d ", (int)zombies.size());
    for (size_t i = 0; i < zombies.size(); i++) {
        Zombie& z = zombies[i];
        s += fmt("%d %.2f %.2f %d %d %d %d ", z.id, z.x, z.y, z.kind, (int)z.hp, (int)z.maxhp, (z.flash > 0 ? 1 : 0) | (z.slamFlash > 0 ? 2 : 0) | (z.stun > 0 ? 4 : 0));
    }
    s += fmt("%d ", (int)spits.size());
    for (size_t i = 0; i < spits.size(); i++) s += fmt("%.2f %.2f ", spits[i].x, spits[i].y);
    s += fmt("%d ", (int)crates.size());
    for (size_t i = 0; i < crates.size(); i++) s += fmt("%.1f %.1f %d ", crates[i].x, crates[i].y, crates[i].kind);
    int nb = 0; std::string bs;
    for (int i = 0; i < N * N; i++) if (G[i] == 2) { nb++; bs += fmt("%d %d ", i, (int)(100 * bratio(i))); }
    s += fmt("%d ", nb) + bs;
    s += boxSnapshot();
    s += grenSnapshot();
    std::map<int, Player>::iterator it = players.find(pk.pid);
    if (it != players.end()) {
        Player& p = it->second;
        int mask = 0; for (int i = 0; i < NW; i++) if (p.unl[i]) mask |= 1 << i;
        s += fmt("%d %d %d %d %d %d %d %d ", (int)p.hp, (int)p.maxhp, (int)p.xp, (int)p.need, p.level, p.scrap, p.kills, p.weapon);
        for (int i = 0; i < NW; i++) s += fmt("%d ", p.ammo[i]);
        int wlp = 0; for (int i = 0; i < NW; i++) wlp |= p.wLvl[i] << (3 * i);   // уровни прокачки всех 6 видов оружия по 3 бита
        s += fmt("%.2f %d %d %d %d %d %d %d %d %.3f %.3f %d %d %d %d", p.reload, p.cost, p.pending, mask, p.menu ? 1 : 0, p.cards[0], p.cards[1], p.cards[2], wlp,
                 p.magMul, p.wallMul, p.headT > 0 ? 2 : (p.hit > 0 ? 1 : 0), p.hurt > 0.25f ? 1 : 0, p.gren[0], p.gren[1]);
    }
    return s;
}

static void hostNet(float dt) {
    hostAccept();
    for (size_t i = 0; i < peers.size();) {
        std::vector<std::string> ms; netRecv(peers[i], ms);
        for (size_t k = 0; k < ms.size(); k++) hostMsg(peers[i], ms[k]);
        if (!peers[i].alive) {
            std::map<int, Player>::iterator it = players.find(peers[i].pid);
            std::string nm;
            if (it != players.end()) { nm = it->second.name; players.erase(it); }
            netClose(peers[i]); peers.erase(peers.begin() + i);
            P = &players[meId]; flowDirty = true;
            if (!nm.empty()) toast(nm + " ВЫШЕЛ", 2.5f);
        } else i++;
    }
    snapT -= dt;
    if (snapT <= 0) { snapT = SNAP_DT; for (size_t i = 0; i < peers.size(); i++) netSend(peers[i], snapshotFor(peers[i])); }
    for (size_t i = 0; i < peers.size(); i++) netFlush(peers[i]);
    discT -= dt;
    if (discT <= 0 && bsock >= 0) {
        discT = 1.f;
        std::string msg = fmt("ZS1|HOST|%d", PORT);
        std::vector<std::string> dests; dests.push_back("255.255.255.255");
        size_t p = hostIp.rfind('.');
        if (hostIp != "?" && p != std::string::npos) dests.push_back(hostIp.substr(0, p) + ".255");
        for (size_t i = 0; i < dests.size(); i++) {
            sockaddr_in a; memset(&a, 0, sizeof a); a.sin_family = AF_INET; a.sin_port = htons(DISC_PORT);
            inet_pton(AF_INET, dests[i].c_str(), &a.sin_addr);
            sendto(bsock, msg.data(), msg.size(), 0, (sockaddr*)&a, sizeof a);
        }
    }
}

static void pollDiscovery() {
    if (dsock < 0) return;
    double now = SDL_GetTicks() / 1000.0;
    for (int k = 0; k < 8; k++) {
        char buf[128]; sockaddr_in from; socklen_t l = sizeof from;
        ssize_t n = recvfrom(dsock, buf, sizeof buf - 1, 0, (sockaddr*)&from, &l);
        if (n <= 0) break;
        buf[n] = 0;
        if (strncmp(buf, "ZS1|", 4) == 0) {
            char ip[64]; inet_ntop(AF_INET, &from.sin_addr, ip, sizeof ip);
            bool ok = false;
            for (size_t i = 0; i < found.size(); i++) if (found[i].ip == ip) { found[i].t = now; ok = true; }
            if (!ok) { Found f; f.ip = ip; f.t = now; found.push_back(f); }
        }
    }
    for (size_t i = 0; i < found.size();) { if (now - found[i].t > 4.0) found.erase(found.begin() + i); else i++; }
}

static std::map<int, int> dummy;
static void ensureWeaponSprite(int wi);
static void applyHello(const std::string& m) {
    // H id wave G
    int id, w; char* g = NULL;
    std::istringstream is(m.substr(2)); std::string gs;
    is >> id >> w >> gs; (void)g;
    if ((int)gs.size() < N * N) return;
    for (int i = 0; i < N * N; i++) { G[i] = gs[i] - '0'; bhp[i] = 0; bmx[i] = 0; }
    zombies.clear(); crates.clear(); players.clear(); fxReset(); genDecos(); bakeGround(); spits.clear(); booms.clear(); grens.clear();
    meId = id; players[id] = newPlayer(id); P = &players[id];
    wave = w; mmDirty = true; toastS.clear(); mode = M_PLAY; leftZ = 0; paused = false;
    if (dsock >= 0) { ::close(dsock); dsock = -1; }
    ensureWeaponSprite(P->weapon);   // оружие в руках готовим сразу — иначе первые секунды после входа его не видно
    toast("ТЫ В ИГРЕ! ДЕРЖИТЕСЬ ВМЕСТЕ.", 3.f); ambientStart();
    if (linked) netSend(link_, fmt("C %d", selectedPerk));
}

static void applySnap(const std::string& line) {
    std::istringstream is(line.substr(2));
    int w, pr, lf, md, dm, s0, s1, rn, np;
    float tm;
    if (!(is >> w >> pr >> tm >> lf >> md >> dm >> s0 >> s1 >> rn >> np)) return;
    wave = w; prep = pr != 0; ptimer = tm; leftZ = lf; duelMode = dm != 0; duelScore[0] = s0; duelScore[1] = s1; duelRoundNum = rn;
    std::vector<int> ids;
    for (int i = 0; i < np; i++) {
        int id, dead, fl, wpn; float x, y, jz = 0; is >> id >> x >> y >> dead >> fl >> wpn >> jz;
        ids.push_back(id);
        if (id == meId) {
            if (P->dead && !dead) { P->x = x; P->y = y; }
            else if (hypotf(P->x - x, P->y - y) > 4.f) { P->x = x; P->y = y; }
            P->dead = dead != 0;
            if (fl && P->flash <= 0) P->flash = 0.07f;
            continue;
        }
        if (!players.count(id)) { players[id] = newPlayer(id); players[id].x = x; players[id].y = y; P = &players[meId]; }
        Player& p = players[id]; p.tx = x; p.ty = y; p.dead = dead != 0; p.weapon = std::max(0, std::min(NW - 1, wpn)); p.jumpZ = jz; if (fl && p.flash <= 0) p.flash = 0.07f;
    }
    for (std::map<int, Player>::iterator it = players.begin(); it != players.end();) {
        if (it->first != meId && std::find(ids.begin(), ids.end(), it->first) == ids.end()) players.erase(it++); else ++it;
    }
    P = &players[meId];
    int nz; is >> nz;
    std::vector<Zombie> nzv;
    for (int i = 0; i < nz; i++) {
        int id, kind, hp, mhp, fl; float x, y; is >> id >> x >> y >> kind >> hp >> mhp >> fl;
        Zombie z; bool have = false;
        for (size_t k = 0; k < zombies.size(); k++) if (zombies[k].id == id) { z = zombies[k]; have = true; break; }
        if (!have) { z.x = x; z.y = y; }
        if (kind < 0 || kind >= NZK) kind = 0;
        z.id = id; z.kind = kind; z.tx = x; z.ty = y; z.hp = (float)hp; z.maxhp = (float)std::max(1, mhp);
        z.r = ZK[kind].r; z.hs = ZK[kind].hs; z.flash = (fl & 1) ? 0.1f : 0.f; z.slam = (fl & 2) != 0; z.stun = (fl & 4) ? 0.3f : 0.f;
        nzv.push_back(z);
    }
    zombies.swap(nzv);
    int nsp; is >> nsp; spits.clear();
    for (int i = 0; i < nsp; i++) { Spit sp = {0, 0, 0, 0, 1, 0}; is >> sp.x >> sp.y; spits.push_back(sp); }
    int nc; is >> nc; crates.clear();
    for (int i = 0; i < nc; i++) { Crate c; is >> c.x >> c.y >> c.kind; crates.push_back(c); }
    int nb; is >> nb;
    static std::vector<int> seen;
    std::vector<int> now;
    bool changed = false;
    for (int i = 0; i < nb; i++) {
        int idx, pct; is >> idx >> pct;
        if (idx < 0 || idx >= N * N) continue;
        now.push_back(idx); bhp[idx] = (float)pct; bmx[idx] = 100.f;
        if (G[idx] != 2) { G[idx] = 2; changed = true; }
    }
    for (size_t i = 0; i < seen.size(); i++)
        if (std::find(now.begin(), now.end(), seen[i]) == now.end()) { if (G[seen[i]] == 2) { G[seen[i]] = 0; changed = true; } bhp[seen[i]] = bmx[seen[i]] = 0; }
    seen = now;
    if (changed) mmDirty = true;
    int nbx = 0; is >> nbx;
    for (int i = 0; i < nbx; i++) { int bidx = -1, bpct = 100; is >> bidx >> bpct; boxSync(bidx, bpct); }
    int ngr = 0; is >> ngr; grens.clear();
    for (int i = 0; i < ngr && i < 64; i++) { Gren g; g.vx = g.vy = g.vz = 0; g.fuse = 1; g.owner = -1; g.id = 0; g.type = 0; is >> g.id >> g.x >> g.y >> g.z >> g.type; grens.push_back(g); }
    int hp, mh, xp, nd, lv, sc, kl, wp, am[NW], cs, pd, mask, mn, c0, c1, c2, dmy, ht, hu, g0 = 0, g1 = 0; float rl, mm, wm;
    bool okp = (bool)(is >> hp >> mh >> xp >> nd >> lv >> sc >> kl >> wp);
    for (int i = 0; i < NW && okp; i++) okp = (bool)(is >> am[i]);
    if (okp && (is >> rl >> cs >> pd >> mask >> mn >> c0 >> c1 >> c2 >> dmy >> mm >> wm >> ht >> hu >> g0 >> g1)) {
        P->hp = (float)hp; P->maxhp = (float)mh; P->xp = (float)xp; P->need = (float)nd; P->level = lv; P->scrap = sc; P->kills = kl;
        P->weapon = std::max(0, std::min(NW - 1, wp)); for (int i = 0; i < NW; i++) { P->ammo[i] = am[i]; P->unl[i] = (mask >> i) & 1; }
        P->reload = rl; P->cost = cs; P->pending = pd; P->magMul = mm; P->wallMul = wm;
        for (int i = 0; i < NW; i++) P->wLvl[i] = (dmy >> (3 * i)) & 7;
        if (ht) P->hit = 0.12f;
        if (ht == 2) P->headT = 0.35f;
        if (hu) P->hurt = 0.35f;
        P->gren[0] = std::max(0, std::min(GREN_MAX, g0)); P->gren[1] = std::max(0, std::min(GREN_MAX, g1));
        if (pickT <= 0) { P->menu = mn != 0; P->cards[0] = c0; P->cards[1] = c1; P->cards[2] = c2; }
    }
    if (md == 1 && mode == M_PLAY) {
        mode = M_DEAD; deadT = 1.2f;
        if (duelMode) {
            bool iWon = !P->dead;
            lastCoinsGain = iWon ? 90 : 25; coins += lastCoinsGain;
            if (iWon) { duelWinsFriend++; questProgress(QT_DUELWIN, 1); } else duelLossFriend++;
            saveData();
        }
        else { if (wave > bestWave) { bestWave = wave; newRecord = true; saveData(); } awardDeathCoins(); }
    }
}

static void lostConnection(const std::string& m) { shutdownNet(); mode = M_MENU; msgStr = m; }

// ============================ ВВОД (состояние касаний) ============================
struct Touch { long long id; int role; int btn; float x, y, ox, oy; };  // role: 1 кнопка, 2 стик, 3 обзор
static std::vector<Touch> touches;
enum { B_FIRE = 0, B_BUILD, B_WEAPON, B_RELOAD, B_AUTO, B_START, B_SHOP, B_JUMP, B_GREN, B_STUN, NB };
static_assert(NB == NBTN, "NBTN must equal NB");
struct BtnGeo { float cx, cy, r; };
static BtnGeo BTN[NB];
static const char* BLABEL[NB] = {"ОГОНЬ", "СТРОЙ", "СМЕНА", "ЗАРЯД", "АВТО", "СТАРТ", "МАГАЗИН", "ПРЫЖОК", "ГРАНАТА", "ОГЛУШ."};
static const Col BCOL[NB] = {{220, 60, 50, 255}, {220, 160, 50, 255}, {80, 140, 230, 255}, {90, 200, 120, 255}, {170, 90, 220, 255}, {240, 240, 240, 255}, {235, 190, 40, 255}, {70, 170, 200, 255}, {90, 150, 60, 255}, {70, 130, 235, 255}};
static const Uint8* KEYS = NULL;

static void makeBtnLayout() {
    BtnGeo d[NB] = {};
    if (portrait) {
        d[B_FIRE] = {W - 15 * U, H - 22 * U, 12 * U}; d[B_BUILD] = {W - 36 * U, H - 11 * U, 8 * U};
        d[B_WEAPON] = {W - 13 * U, H - 44 * U, 7 * U}; d[B_RELOAD] = {W - 30 * U, H - 37 * U, 6.5f * U};
        d[B_JUMP] = {W - 9 * U, H - 60 * U, 6 * U};          // на месте бывшей АВТО
        d[B_RELOAD] = {W - 40 * U, H - 37 * U, 6.5f * U};    // подальше от карты
        d[B_START] = {W / 2.f, 58 * U, 8 * U}; d[B_SHOP] = {W - 30 * U, H - 52 * U, 6.5f * U};      // переопределятся ниже картой
        d[B_GREN] = {W - 30 * U, H - 58 * U, 6.f * U}; d[B_STUN] = {W - 30 * U, H - 74 * U, 6.f * U};
    } else {
        d[B_FIRE] = {W - 15 * U, H - 24 * U, 12 * U}; d[B_BUILD] = {W - 37 * U, H - 13 * U, 8 * U};
        d[B_WEAPON] = {W - 30 * U, H - 40 * U, 7 * U}; d[B_RELOAD] = {W - 9 * U, H - 50 * U, 6.5f * U};
        d[B_JUMP] = {W - 50 * U, H - 33 * U, 6.5f * U};      // на месте бывшей АВТО
        d[B_RELOAD] = {W - 58 * U, H - 15 * U, 6.5f * U};    // подальше от карты
        d[B_START] = {W - 56 * U, H - 13 * U, 8 * U}; d[B_SHOP] = {W - 22 * U, H - 62 * U, 6.5f * U};      // переопределятся ниже картой
        d[B_GREN] = {W - 44 * U, H - 50 * U, 6.f * U}; d[B_STUN] = {W - 60 * U, H - 44 * U, 6.f * U};
    }
    {   // СТАРТ и МАГАЗИН переехали к миникарте (там всегда есть место, независимо от разворота)
        int mp = std::max(2, (int)(std::min(W, H) * 0.30f / N));
        float mmX = W - N * mp - 2 * U, mmY = 2 * U, mmW = (float)(N * mp);
        float r1 = 7.f * U, r2 = 6.f * U, gap = 2.f * U;
        d[B_START] = {mmX + mmW / 2.f, mmY + N * mp + r1 + gap, r1};
        d[B_SHOP] = {mmX + mmW / 2.f, mmY + N * mp + 2 * r1 + gap * 2 + r2, r2};
    }
    int o = portrait ? 1 : 0;
    float sc = std::max(0.6f, std::min(1.6f, btnScale));
    for (int i = 0; i < NB; i++) {
        float cx = d[i].cx, cy = d[i].cy, r = d[i].r * sc;
        if (hasCustom[o] && customPos[o][i][0] >= 0.f) { cx = customPos[o][i][0] * W; cy = customPos[o][i][1] * H; }
        else if (leftHand && i != B_START && i != B_SHOP) cx = W - cx;   // рядом с картой — не зеркалим
        cx = std::max(r, std::min(W - r, cx)); cy = std::max(r, std::min(H - r, cy));
        BTN[i].cx = cx; BTN[i].cy = cy; BTN[i].r = r;
    }
}

// ============================ РИСОВАНИЕ: примитивы ============================
static void setCol(Col c) { SDL_SetRenderDrawColor(ren, c.r, c.g, c.b, c.a); }
static void fillRect(float x, float y, float w, float h, Col c) {
    SDL_Rect r = {(int)x, (int)y, std::max(1, (int)(w + 0.5f)), std::max(1, (int)(h + 0.5f))};
    setCol(c); SDL_RenderFillRect(ren, &r);
}
static void frameRect(float x, float y, float w, float h, int t, Col c) {
    fillRect(x, y, w, t, c); fillRect(x, y + h - t, w, t, c); fillRect(x, y, t, h, c); fillRect(x + w - t, y, t, h, c);
}
static void fillCircle(float cx, float cy, float r, Col c) {
    setCol(c); int ri = (int)r;
    for (int y = -ri; y <= ri; y++) {
        int xo = (int)sqrtf((float)(ri * ri - y * y));
        SDL_Rect s = {(int)cx - xo, (int)cy + y, 2 * xo + 1, 1}; SDL_RenderFillRect(ren, &s);
    }
}
static void ringCircle(float cx, float cy, float r, float th, Col c) {
    setCol(c); int ro = (int)r, ri = (int)std::max(0.f, r - th);
    for (int y = -ro; y <= ro; y++) {
        int xo = (int)sqrtf((float)(ro * ro - y * y));
        if (abs(y) < ri) {
            int xi = (int)sqrtf((float)(ri * ri - y * y));
            SDL_Rect a = {(int)cx - xo, (int)cy + y, xo - xi + 1, 1}, b = {(int)cx + xi, (int)cy + y, xo - xi + 1, 1};
            SDL_RenderFillRect(ren, &a); SDL_RenderFillRect(ren, &b);
        } else { SDL_Rect s = {(int)cx - xo, (int)cy + y, 2 * xo + 1, 1}; SDL_RenderFillRect(ren, &s); }
    }
}
// выпуклый многоугольник
static void fillPoly(const float* px, const float* py, int n, Col c) {
#if SDL_VERSION_ATLEAST(2, 0, 18)
    SDL_Vertex v[16];
    for (int i = 0; i < n && i < 16; i++) { v[i].position.x = px[i]; v[i].position.y = py[i]; v[i].color.r = c.r; v[i].color.g = c.g; v[i].color.b = c.b; v[i].color.a = c.a; v[i].tex_coord.x = 0; v[i].tex_coord.y = 0; }
    int idx[42], m = 0;
    for (int i = 1; i + 1 < n && m + 3 <= 42; i++) { idx[m++] = 0; idx[m++] = i; idx[m++] = i + 1; }
    SDL_RenderGeometry(ren, NULL, v, n, idx, m);
#else
    float ymin = 1e9f, ymax = -1e9f;
    for (int i = 0; i < n; i++) { ymin = std::min(ymin, py[i]); ymax = std::max(ymax, py[i]); }
    int y0 = std::max(0, (int)ymin), y1 = std::min(H - 1, (int)ymax);
    setCol(c);
    for (int y = y0; y <= y1; y++) {
        float fy = y + 0.5f, xl = 1e9f, xr = -1e9f;
        for (int i = 0; i < n; i++) {
            int j = (i + 1) % n;
            float ay = py[i], by = py[j];
            if ((fy >= ay && fy < by) || (fy >= by && fy < ay)) {
                float t = (fy - ay) / (by - ay), x = px[i] + t * (px[j] - px[i]);
                xl = std::min(xl, x); xr = std::max(xr, x);
            }
        }
        if (xr >= xl) { SDL_Rect r = {(int)xl, y, std::max(1, (int)(xr - xl) + 1), 1}; SDL_RenderFillRect(ren, &r); }
    }
#endif
}

// ============================ ШРИФТ 5x7 (кириллица) ============================
struct Glyph { int cp; const char* rows; };
static const Glyph GLYPHS[] = {
    {' ', "....." "....." "....." "....." "....." "....." "....."},
    {'0', ".###." "#...#" "#..##" "#.#.#" "##..#" "#...#" ".###."},
    {'1', "..#.." ".##.." "..#.." "..#.." "..#.." "..#.." ".###."},
    {'2', ".###." "#...#" "....#" "...#." "..#.." ".#..." "#####"},
    {'3', ".###." "#...#" "....#" "..##." "....#" "#...#" ".###."},
    {'4', "...#." "..##." ".#.#." "#..#." "#####" "...#." "...#."},
    {'5', "#####" "#...." "####." "....#" "....#" "#...#" ".###."},
    {'6', "..##." ".#..." "#...." "####." "#...#" "#...#" ".###."},
    {'7', "#####" "....#" "...#." "..#.." ".#..." ".#..." ".#..."},
    {'8', ".###." "#...#" "#...#" ".###." "#...#" "#...#" ".###."},
    {'9', ".###." "#...#" "#...#" ".####" "....#" "...#." ".##.."},
    {'.', "....." "....." "....." "....." "....." "..#.." "..#.."},
    {',', "....." "....." "....." "....." "..#.." "..#.." ".#..."},
    {':', "....." "..#.." "..#.." "....." "..#.." "..#.." "....."},
    {'-', "....." "....." "....." ".###." "....." "....." "....."},
    {'+', "....." "..#.." "..#.." "#####" "..#.." "..#.." "....."},
    {'/', "....#" "....#" "...#." "..#.." ".#..." "#...." "#...."},
    {'%', "##..#" "##..#" "...#." "..#.." ".#..." "#..##" "#..##"},
    {'!', "..#.." "..#.." "..#.." "..#.." "..#.." "....." "..#.."},
    {'?', ".###." "#...#" "....#" "...#." "..#.." "....." "..#.."},
    {'(', "...#." "..#.." ".#..." ".#..." ".#..." "..#.." "...#."},
    {')', ".#..." "..#.." "...#." "...#." "...#." "..#.." ".#..."},
    {'<', "...#." "..#.." ".#..." "#...." ".#..." "..#.." "...#."},
    {'>', ".#..." "..#.." "...#." "....#" "...#." "..#.." ".#..."},
    {'=', "....." "....." "#####" "....." "#####" "....." "....."},
    {'I', ".###." "..#.." "..#.." "..#.." "..#.." "..#.." ".###."},
    {'F', "#####" "#...." "#...." "####." "#...." "#...." "#...."},
    {'S', ".####" "#...." "#...." ".###." "....#" "....#" "####."},
    {'D', "####." "#...#" "#...#" "#...#" "#...#" "#...#" "####."},
    {0x410, ".###." "#...#" "#...#" "#####" "#...#" "#...#" "#...#"},  // А
    {0x411, "#####" "#...." "#...." "####." "#...#" "#...#" "####."},  // Б
    {0x412, "####." "#...#" "#...#" "####." "#...#" "#...#" "####."},  // В
    {0x413, "#####" "#...." "#...." "#...." "#...." "#...." "#...."},  // Г
    {0x414, "..##." ".#.#." ".#.#." ".#.#." ".#.#." "#####" "#...#"},  // Д
    {0x415, "#####" "#...." "#...." "####." "#...." "#...." "#####"},  // Е
    {0x416, "#.#.#" "#.#.#" ".###." "..#.." ".###." "#.#.#" "#.#.#"},  // Ж
    {0x417, ".###." "#...#" "....#" "..##." "....#" "#...#" ".###."},  // З
    {0x418, "#...#" "#...#" "#..##" "#.#.#" "##..#" "#...#" "#...#"},  // И
    {0x419, ".#.#." "#...#" "#..##" "#.#.#" "##..#" "#...#" "#...#"},  // Й
    {0x41A, "#...#" "#..#." "#.#.." "##..." "#.#.." "#..#." "#...#"},  // К
    {0x41B, "..###" ".#..#" ".#..#" ".#..#" "#...#" "#...#" "#...#"},  // Л
    {0x41C, "#...#" "##.##" "#.#.#" "#.#.#" "#...#" "#...#" "#...#"},  // М
    {0x41D, "#...#" "#...#" "#...#" "#####" "#...#" "#...#" "#...#"},  // Н
    {0x41E, ".###." "#...#" "#...#" "#...#" "#...#" "#...#" ".###."},  // О
    {0x41F, "#####" "#...#" "#...#" "#...#" "#...#" "#...#" "#...#"},  // П
    {0x420, "####." "#...#" "#...#" "####." "#...." "#...." "#...."},  // Р
    {0x421, ".###." "#...#" "#...." "#...." "#...." "#...#" ".###."},  // С
    {0x422, "#####" "..#.." "..#.." "..#.." "..#.." "..#.." "..#.."},  // Т
    {0x423, "#...#" "#...#" "#...#" ".####" "....#" "...#." ".##.."},  // У
    {0x424, "..#.." ".###." "#.#.#" "#.#.#" ".###." "..#.." "..#.."},  // Ф
    {0x425, "#...#" "#...#" ".#.#." "..#.." ".#.#." "#...#" "#...#"},  // Х
    {0x426, "#..#." "#..#." "#..#." "#..#." "#..#." "#####" "....#"},  // Ц
    {0x427, "#...#" "#...#" "#...#" ".####" "....#" "....#" "....#"},  // Ч
    {0x428, "#.#.#" "#.#.#" "#.#.#" "#.#.#" "#.#.#" "#.#.#" "#####"},  // Ш
    {0x429, "#.#.#" "#.#.#" "#.#.#" "#.#.#" "#.#.#" "#####" "....#"},  // Щ
    {0x42A, "##..." ".#..." ".#..." ".###." ".#..#" ".#..#" ".###."},  // Ъ
    {0x42B, "#...#" "#...#" "#...#" "###.#" "#.#.#" "#.#.#" "###.#"},  // Ы
    {0x42C, "#...." "#...." "#...." "####." "#...#" "#...#" "####."},  // Ь
    {0x42D, "####." "....#" "....#" ".####" "....#" "....#" "####."},  // Э
    {0x42E, "#..#." "#.#.#" "#.#.#" "###.#" "#.#.#" "#.#.#" "#..#."},  // Ю
    {0x42F, ".####" "#...#" "#...#" ".####" ".#..#" "#...#" "#...#"},  // Я
};
static const int NGLYPH = sizeof(GLYPHS) / sizeof(GLYPHS[0]);
static SDL_Texture* fontTex = NULL;
static std::map<int, int> glyphIdx;

static SDL_Texture* makeTex(const std::vector<u32>& px, int w, int h) {
    SDL_Texture* t = SDL_CreateTexture(ren, SDL_PIXELFORMAT_ARGB8888, SDL_TEXTUREACCESS_STATIC, w, h);
    if (!t) return NULL;
    SDL_UpdateTexture(t, NULL, px.data(), w * 4);
    SDL_SetTextureBlendMode(t, SDL_BLENDMODE_BLEND);
    return t;
}
static void clearTextCache();
static void makeFont() {
    clearTextCache();
    if (fontTex) SDL_DestroyTexture(fontTex);
    std::vector<u32> px((size_t)NGLYPH * 6 * 8, 0);
    int wpx = NGLYPH * 6;
    for (int g = 0; g < NGLYPH; g++) {
        glyphIdx[GLYPHS[g].cp] = g;
        for (int i = 0; i < 35; i++)
            if (GLYPHS[g].rows[i] == '#') px[(size_t)(i / 5) * wpx + g * 6 + (i % 5)] = 0xFFFFFFFFu;
    }
    fontTex = makeTex(px, wpx, 8);
}
static int utf8next(const std::string& s, size_t& i) {
    unsigned char c = (unsigned char)s[i];
    if (c < 0x80) { i++; return c; }
    if ((c >> 5) == 6 && i + 1 < s.size()) { int cp = ((c & 31) << 6) | (s[i + 1] & 63); i += 2; return cp; }
    if ((c >> 4) == 14 && i + 2 < s.size()) { int cp = ((c & 15) << 12) | ((s[i + 1] & 63) << 6) | (s[i + 2] & 63); i += 3; return cp; }
    i++; return '?';
}
static int normCp(int cp) {
    if (cp >= 'a' && cp <= 'z') cp -= 32;
    if (cp >= 0x430 && cp <= 0x44F) cp -= 0x20;
    if (cp == 0x451 || cp == 0x401) cp = 0x415;
    if (cp == 0x2013 || cp == 0x2014) cp = '-';
    switch (cp) {
        case 'A': return 0x410; case 'B': return 0x412; case 'C': return 0x421; case 'E': return 0x415;
        case 'H': return 0x41D; case 'K': return 0x41A; case 'M': return 0x41C; case 'O': return 0x41E;
        case 'P': return 0x420; case 'T': return 0x422; case 'X': return 0x425; case 'Y': return 0x423;
        case 'Z': return 0x417; case 'G': return 0x413; case 'L': return 0x41B;
    }
    return cp;
}
static int textLen(const std::string& s) { int n = 0; size_t i = 0; while (i < s.size()) { utf8next(s, i); n++; } return n; }
enum { A_TL = 0, A_TC, A_TR, A_C, A_BR, A_BC, A_ML };
struct TextTex { SDL_Texture* t; int w, h; unsigned last; };
static unsigned textFrame = 0;                          // номер кадра — чтобы знать, какие надписи давно не показывали
static std::map<std::string, TextTex> textCache;        // готовые надписи: один вызов отрисовки вместо десятков
static void clearTextCache() { for (std::map<std::string, TextTex>::iterator it = textCache.begin(); it != textCache.end(); ++it) if (it->second.t) SDL_DestroyTexture(it->second.t); textCache.clear(); }
static void evictText() {                                // убираем понемногу (не больше 24 за раз) давно не показанные надписи, а не всё сразу
    int removed = 0;
    for (std::map<std::string, TextTex>::iterator it = textCache.begin(); it != textCache.end() && removed < 24;) {
        if (textFrame - it->second.last > 120) { if (it->second.t) SDL_DestroyTexture(it->second.t); textCache.erase(it++); removed++; } else ++it;
    }
    while (textCache.size() > 700 && removed < 48) {      // страховка от разрастания: выкидываем самые старые
        std::map<std::string, TextTex>::iterator oldest = textCache.begin();
        for (std::map<std::string, TextTex>::iterator it = textCache.begin(); it != textCache.end(); ++it) if (it->second.last < oldest->second.last) oldest = it;
        if (oldest->second.t) SDL_DestroyTexture(oldest->second.t);
        textCache.erase(oldest); removed++;
    }
}
static void drawText(const std::string& s, float x, float y, float sc, Col col, int anchor = A_TL, float maxw = 0, bool shadow = true) {
    if (s.empty() || !fontTex) return;
    int n = textLen(s);
    int isc = std::max(1, (int)sc);
    if (maxw > 0 && (n * 6 - 1) * isc > maxw) isc = std::max(1, (int)(maxw / (n * 6 - 1)));
    int w = (n * 6 - 1) * isc, h = 7 * isc;
    int ox = (int)x, oy = (int)y;
    if (anchor == A_TC || anchor == A_C || anchor == A_BC) ox -= w / 2;
    if (anchor == A_TR || anchor == A_BR) ox -= w;
    if (anchor == A_C || anchor == A_ML) oy -= h / 2;
    if (anchor == A_BR || anchor == A_BC) oy -= h;
    int off = shadow ? std::max(1, isc / 3) : 0;
    std::string key = s + fmt("|%d|%d,%d,%d,%d|%d", isc, col.r, col.g, col.b, col.a, shadow ? 1 : 0);
    std::map<std::string, TextTex>::iterator it = textCache.find(key);
    if (it == textCache.end()) {
        if (textCache.size() > 300) evictText();
        int tw = w + off, th = h + off;
        std::vector<u32> px((size_t)tw * th, 0);
        u32 shC = PX(C(0, 0, 0, std::min(255, 200 * col.a / 255))), tC = PX(col);
        size_t i = 0; int k = 0;
        while (i < s.size()) {
            int cp = normCp(utf8next(s, i));
            std::map<int, int>::iterator gi = glyphIdx.find(cp);
            if (gi != glyphIdx.end() && cp != ' ') {
                const char* rows = GLYPHS[gi->second].rows;
                for (int gy = 0; gy < 7; gy++)
                    for (int gx = 0; gx < 5; gx++) {
                        if (rows[gy * 5 + gx] != '#') continue;
                        for (int sy = 0; sy < isc; sy++)
                            for (int sx = 0; sx < isc; sx++) {
                                int X = k * 6 * isc + gx * isc + sx, Y = gy * isc + sy;
                                if (shadow) px[(size_t)(Y + off) * tw + X + off] = shC;
                            }
                    }
                for (int gy = 0; gy < 7; gy++)
                    for (int gx = 0; gx < 5; gx++) {
                        if (rows[gy * 5 + gx] != '#') continue;
                        for (int sy = 0; sy < isc; sy++)
                            for (int sx = 0; sx < isc; sx++) px[(size_t)(gy * isc + sy) * tw + k * 6 * isc + gx * isc + sx] = tC;
                    }
            }
            k++;
        }
        TextTex tt; tt.t = makeTex(px, tw, th); tt.w = tw; tt.h = th; tt.last = textFrame;
        it = textCache.insert(std::make_pair(key, tt)).first;
    }
    it->second.last = textFrame;
    if (!it->second.t) return;
    SDL_Rect dst = {ox, oy, it->second.w, it->second.h};
    SDL_RenderCopy(ren, it->second.t, NULL, &dst);
}
static float FS() { return std::max(1.f, floorf(0.44f * U)); }
static float FM() { return std::max(1.f, floorf(0.66f * U)); }
static float FL() { return std::max(1.f, floorf(1.4f * U)); }
static float FXL() { return std::max(1.f, floorf(2.0f * U)); }
static float textH(float sc) { return 7 * std::max(1, (int)sc); }
static float textW(const std::string& s, float sc, float maxw = 0) {
    int n = textLen(s), isc = std::max(1, (int)sc);
    if (maxw > 0 && (n * 6 - 1) * isc > maxw) isc = std::max(1, (int)(maxw / (n * 6 - 1)));
    return (float)((n * 6 - 1) * isc);
}

// ============================ СПРАЙТЫ (процедурные) ============================
struct Canvas {      // холст с масштабом: рисуем в "логических" координатах, храним в sc раз большем разрешении
    int w, h, sc; std::vector<u32> px;
    Canvas(int W_, int H_, int sc_ = 1) : w(W_), h(H_), sc(sc_), px((size_t)W_ * H_, 0) {}
    void raw(int x, int y, int ww, int hh, Col c) { for (int j = y; j < y + hh; j++) for (int i = x; i < x + ww; i++) if (i >= 0 && j >= 0 && i < w && j < h) px[(size_t)j * w + i] = PX(c); }
    void rect(int x, int y, int ww, int hh, Col c) { raw(x * sc, y * sc, ww * sc, hh * sc, c); }
    void circle(int cx0, int cy0, int r0, Col c) {
        int cx = cx0 * sc + sc / 2, cy = cy0 * sc + sc / 2, r = r0 * sc;
        for (int j = cy - r; j <= cy + r; j++) for (int i = cx - r; i <= cx + r; i++) if ((i - cx) * (i - cx) + (j - cy) * (j - cy) <= r * r && i >= 0 && j >= 0 && i < w && j < h) px[(size_t)j * w + i] = PX(c);
    }
    void line(int x0, int y0, int x1, int y1, int t, Col c) {
        x0 *= sc; y0 *= sc; x1 *= sc; y1 *= sc; t *= sc;
        int steps = std::max(abs(x1 - x0), abs(y1 - y0)); if (steps == 0) steps = 1;
        for (int s_ = 0; s_ <= steps; s_++) { int x = x0 + (x1 - x0) * s_ / steps, y = y0 + (y1 - y0) * s_ / steps; raw(x - t / 2, y - t / 2, t, t, c); }
    }
};
// ============================ ТЕКСТУРЫ (процедурные) ============================
static u32 hashu(int x, int y, int s) { u32 h = (u32)x * 374761393u + (u32)y * 668265263u + (u32)s * 2246822519u; h = (h ^ (h >> 13)) * 1274126177u; return h ^ (h >> 16); }
static float hnoise(int x, int y, int s = 0) { return (hashu(x, y, s) & 0xFFFF) / 65535.f; }
static float vnoiseP(float x, float y, int s, int per) {   // плавный шум с периодом per (для бесшовности)
    int xi = (int)floorf(x), yi = (int)floorf(y); float fx = x - xi, fy = y - yi;
    fx = fx * fx * (3 - 2 * fx); fy = fy * fy * (3 - 2 * fy);
    int x0 = ((xi % per) + per) % per, x1 = (x0 + 1) % per, y0 = ((yi % per) + per) % per, y1 = (y0 + 1) % per;
    float a = hnoise(x0, y0, s), b = hnoise(x1, y0, s), c = hnoise(x0, y1, s), d = hnoise(x1, y1, s);
    return a + (b - a) * fx + (c - a) * fy + (a - b - c + d) * fx * fy;
}
static const int TS = 128;                    // размер текстур стен и пола
static float DETA[TS * TS], DETB[TS * TS];       // тайловый шум для мелкой фактуры земли
static u32 T_STONE[TS * TS], T_PLANK[TS * TS], T_HEDGE[TS * TS], T_CRACK[TS * TS], T_CONC[TS * TS], T_COBBLE[TS * TS];
static bool texGenDone = false;
static inline float sstep(float a, float b, float x) { float t = std::max(0.f, std::min(1.f, (x - a) / (b - a))); return t * t * (3 - 2 * t); }
static void genTextures() {
    if (texGenDone) return;
    texGenDone = true;
    for (int y = 0; y < TS; y++)
        for (int x = 0; x < TS; x++) {
            int i = y * TS + x;
            // ---------- каменная кладка ----------
            {
                int row = y / 16, off = (row & 1) * 16, xx = (x + off) & (TS - 1), bx = xx / 32, lx = xx % 32, ly = y % 16;
                float bn = hnoise(bx, row, 1), base = 96 + bn * 54;
                float r = base + (hnoise(bx, row, 2) - 0.5f) * 26, g = base + (hnoise(bx, row, 4) - 0.5f) * 16, b = base + 12 + (hnoise(bx, row, 6) - 0.5f) * 18;
                float tintv = hnoise(bx, row, 20);
                if (tintv > 0.88f) { r *= 1.18f; g *= 0.92f; b *= 0.86f; }          // редкие красноватые кирпичи
                else if (tintv < 0.10f) { r *= 0.88f; g *= 0.98f; b *= 1.08f; }    // холодные серо-синие
                float grain = (vnoiseP(x / 2.f, y / 2.f, 3, 64) - 0.5f) * 30 + (hnoise(x, y, 3) - 0.5f) * 14;
                r += grain; g += grain; b += grain;
                float bev = 0;                                          // свет сверху-слева
                if (ly < 4) bev += 20 * (4 - ly) / 4.f;
                if (lx < 4) bev += 12 * (4 - lx) / 4.f;
                if (ly > 11) bev -= 26 * (ly - 11) / 4.f;
                if (lx > 27) bev -= 16 * (lx - 27) / 4.f;
                r += bev; g += bev; b += bev;
                if (hnoise(x / 3, y / 3, 8) > 0.988f && std::min(std::min(lx, 31 - lx), std::min(ly, 15 - ly)) < 8) { r *= 0.62f; g *= 0.62f; b *= 0.62f; }   // сколы
                if (hnoise(bx, row, 9) > 0.84f) {                        // трещина в кирпиче
                    float cyl = 7.f + 5.f * sinf(lx * 0.33f + bx * 2.f);
                    if (fabsf(ly - cyl) < 0.8f && lx > 3 && lx < 28) { r *= 0.35f; g *= 0.35f; b *= 0.35f; }
                }
                float mo = vnoiseP(x / 16.f, y / 16.f, 7, 8) * 0.55f + vnoiseP(x / 4.f, y / 4.f, 17, 32) * 0.45f + (ly > 9 ? 0.06f : 0.f) + y / (float)TS * 0.10f;
                if (mo > 0.62f) { float t = std::min(1.f, (mo - 0.62f) * 4.5f); r = r * (1 - t) + (46 + hnoise(x, y, 18) * 14) * t; g = g * (1 - t) + (98 + hnoise(x, y, 18) * 30) * t; b = b * (1 - t) + 40 * t; }
                float sv = vnoiseP(x / 8.f, y / 32.f, 19, 16);          // потёки
                if (sv > 0.68f) { float t = (sv - 0.68f) * 2.2f; r *= 1 - t * 0.35f; g *= 1 - t * 0.35f; b *= 1 - t * 0.3f; }
                if (ly < 2 || lx < 2) { float m = 40 + hnoise(x, y, 9) * 12; r = m; g = m - 2; b = m + 5; }             // шов
                else if (ly == 2 || lx == 2) { r *= 0.6f; g *= 0.6f; b *= 0.62f; }
                float ao = 1.f;
                if (y < 14) ao = 0.74f + 0.26f * sstep(0, 14, (float)y);
                if (y > TS - 20) ao = std::min(ao, 0.70f + 0.30f * sstep((float)TS, (float)(TS - 20), (float)y));
                r *= ao; g *= ao; b *= ao;
                T_STONE[i] = PX(C((int)r, (int)g, (int)b));
            }
            // ---------- доски баррикады ----------
            {
                int pr = y / 32, ly = y % 32;
                float wr = 150 + hnoise(pr, 1, 11) * 34, wg = 100 + hnoise(pr, 1, 12) * 22, wb = 56 + hnoise(pr, 1, 13) * 10;
                float grain = 0.80f + 0.36f * vnoiseP(x / 32.f + pr * 3, y * 0.5f, 14 + pr, 4) + 0.12f * vnoiseP(x / 4.f, y / 1.5f, 15, 32);
                float r = wr * grain, g = wg * grain, b = wb * grain;
                float nz = (hnoise(x, y, 15) - 0.5f);
                r += nz * 14; g += nz * 10; b += nz * 6;
                float kx = 20 + hnoise(pr, 2, 16) * 88, ky = pr * 32 + 8 + hnoise(pr, 3, 16) * 16, kd = sqrtf((x - kx) * (x - kx) + (y - ky) * (y - ky) * 2.5f);
                if (kd < 8) { float t = 0.55f + 0.2f * sinf(kd * 1.6f); r *= t; g *= t; b *= t; }
                int seam = 30 + (pr * 41) % 68;
                if (ly < 2 || ly > 29) { r = 50; g = 30; b = 15; }
                else if (ly == 2) { r += 24; g += 20; b += 10; }
                else if (ly > 27) { r *= 0.7f; g *= 0.7f; b *= 0.7f; }
                if (x == seam) { r *= 0.42f; g *= 0.42f; b *= 0.42f; }
                else if (x == seam + 1) { r += 20; g += 16; b += 8; }
                for (int nx : {9, 118}) {
                    float dd = sqrtf((float)((x - nx) * (x - nx) + (ly - 16) * (ly - 16)));
                    if (dd < 3.5f) { float hi = dd < 1.6f ? 1.f : 0.f; r = 64 + hi * 130 * (x < nx ? 1 : 0.6f); g = r; b = r + 6; }
                    else if (dd < 5.f) { r *= 0.7f; g *= 0.7f; b *= 0.7f; }
                }
                float ao = 1.f;
                if (y < 10) ao = 0.8f + 0.2f * sstep(0, 10, (float)y);
                if (y > TS - 14) ao = 0.75f + 0.25f * sstep((float)TS, (float)(TS - 14), (float)y);
                T_PLANK[i] = PX(C((int)(r * ao), (int)(g * ao), (int)(b * ao)));
            }
            // ---------- живая изгородь ----------
            {
                float n = vnoiseP(x / 8.f, y / 8.f, 11, 16) * 0.45f + vnoiseP(x / 4.f, y / 4.f, 12, 32) * 0.35f + vnoiseP(x / 2.f, y / 2.f, 13, 64) * 0.20f;
                float r = 18 + n * 40, g = 54 + n * 104, b = 20 + n * 32;
                float rid = 0.5f + 0.5f * sinf((x + y) * 0.55f + vnoiseP(x / 4.f, y / 4.f, 14, 32) * 6.f);
                r *= 0.85f + 0.2f * rid; g *= 0.85f + 0.2f * rid;
                float sp = hnoise(x, y, 13);
                if (sp < 0.13f) { r *= 0.45f; g *= 0.45f; b *= 0.45f; }
                else if (sp > 0.95f) { r += 30; g += 40; b += 10; }
                float ao = 1.f;
                if (y > TS - 22) ao = 0.62f + 0.38f * sstep((float)TS, (float)(TS - 22), (float)y);
                if (y < 12) ao = std::min(ao, 0.8f + 0.2f * sstep(0, 12, (float)y));
                T_HEDGE[i] = PX(C((int)(r * ao), (int)(g * ao), (int)(b * ao)));
            }
            // ---------- бетон ----------
            {
                float n = vnoiseP(x / 4.f, y / 4.f, 31, 32), st = vnoiseP(x / 32.f, y / 32.f, 32, 4), rs = vnoiseP(x / 8.f, y / 8.f, 33, 16);
                float v = 86 + n * 28 + (hnoise(x, y, 33) - 0.5f) * 12;
                if (st > 0.62f) v -= (st - 0.62f) * 80;
                float r = v, g = v + 2, b = v + 6;
                if (rs > 0.74f) { float t = (rs - 0.74f) * 3.f; r += 26 * t; g += 8 * t; b -= 6 * t; }
                int jx = x % 64, jy = y % 64;
                if (jx < 2 || jy < 2) { r = g = b = 40; }
                else if (jx == 2 || jy == 2) { r += 18; g += 18; b += 18; }
                else if (jx == 63 || jy == 63) { r -= 12; g -= 12; b -= 12; }
                T_CONC[i] = PX(C((int)r, (int)g, (int)b));
            }
            // ---------- булыжная дорожка ----------
            {
                int row = y / 16, off = (row & 1) * 8, xx = (x + off) & (TS - 1), lx = xx % 16, ly = y % 16, sx = xx / 16;
                float u = (lx - 7.5f) / 8.f, v = (ly - 7.5f) / 8.f, e = powf(fabsf(u), 3.5f) + powf(fabsf(v), 3.5f);
                float base = 108 + hnoise(sx, row, 132) * 40, r, g, b;
                if (e > 0.92f) { float m = 42 + hnoise(x, y, 133) * 12; r = m; g = m - 2; b = m - 4; }
                else {
                    float k = 1.05f - 0.34f * e + (-(u + v)) * 0.16f + (hnoise(x, y, 134) - 0.5f) * 0.18f;
                    r = base * k * 1.02f; g = base * k * 0.96f; b = base * k * 0.90f;
                    if (vnoiseP(x / 8.f, y / 8.f, 135, 16) > 0.7f) { r *= 0.8f; g *= 1.04f; b *= 0.8f; }
                }
                T_COBBLE[i] = PX(C((int)r, (int)g, (int)b));
            }
            T_CRACK[i] = 0;
        }
    for (int y = 0; y < TS; y++)
        for (int x = 0; x < TS; x++) {
            DETA[y * TS + x] = vnoiseP(x / 8.f, y / 8.f, 301, 16) * 0.5f + vnoiseP(x / 4.f, y / 4.f, 302, 32) * 0.3f + vnoiseP(x / 2.f, y / 2.f, 303, 64) * 0.2f;
            DETB[y * TS + x] = vnoiseP(x / 2.f, y / 2.f, 304, 64) * 0.55f + hnoise(x, y, 305) * 0.45f;
        }
    // плющ, свисающий по стене
    for (int k = 0; k < 9; k++) {
        float x = (float)(hashu(k, 1, 131) % TS), ph = (hashu(k, 3, 131) % 628) / 100.f; int len = 40 + (int)(hashu(k, 2, 131) % 84);
        for (int y = 0; y < len && y < TS; y++) {
            x += sinf(y * 0.13f + ph) * 0.6f + (hnoise(y, k, 132) - 0.5f) * 0.8f;
            int ix = ((int)x + TS) % TS;
            T_STONE[y * TS + ix] = PX(C(28, 58, 28));
            if (y % 3 == 0) {
                int side = (hnoise(y, k, 136) > 0.5f) ? 1 : -1;
                for (int ly = -2; ly <= 2; ly++)
                    for (int lx = 0; lx <= 3; lx++) {
                        if (lx * lx + ly * ly * 2 > 9) continue;
                        int px = ((ix + side * (lx + 1)) % TS + TS) % TS, py = y + ly; if (py < 0 || py >= TS) continue;
                        float sh = 0.75f + 0.5f * hnoise(px, py, 137) + (ly < 0 ? 0.2f : -0.05f);
                        T_STONE[py * TS + px] = PX(C((int)(38 * sh), (int)(112 * sh), (int)(40 * sh)));
                    }
            }
        }
    }
    // трещины: стены (прозрачная текстура)
    for (int k = 0; k < 8; k++) {
        float x = (float)(hashu(k, 1, 41) % TS), y = (float)(hashu(k, 2, 41) % TS), a = (hashu(k, 3, 41) % 628) / 100.f;
        for (int s = 0; s < 90; s++) {
            int ix = ((int)x + TS) % TS, iy = ((int)y + TS) % TS;
            T_CRACK[iy * TS + ix] = PX(C(18, 10, 6, 240)); T_CRACK[iy * TS + (ix + 1) % TS] = PX(C(18, 10, 6, 150)); T_CRACK[((iy + 1) % TS) * TS + ix] = PX(C(18, 10, 6, 110));
            a += (hnoise(s, k, 42) - 0.5f) * 1.2f; x += cosf(a) * 1.2f; y += sinf(a) * 1.2f;
            if (s == 40) { float x2 = x, y2 = y, a2 = a + 0.9f; for (int q = 0; q < 30; q++) { int jx = ((int)x2 + TS) % TS, jy = ((int)y2 + TS) % TS; T_CRACK[jy * TS + jx] = PX(C(18, 10, 6, 200)); a2 += (hnoise(q, k, 43) - 0.5f) * 1.1f; x2 += cosf(a2); y2 += sinf(a2); } }
        }
    }
    // трещины и царапины на бетоне
    for (int k = 0; k < 4; k++) {
        float x = (float)(hashu(k, 5, 44) % TS), y = (float)(hashu(k, 6, 44) % TS), a = (hashu(k, 7, 44) % 628) / 100.f;
        for (int s = 0; s < 70; s++) {
            int ix = ((int)x + TS) % TS, iy = ((int)y + TS) % TS;
            T_CONC[iy * TS + ix] = PX(C(34, 34, 40));
            a += (hnoise(s, k, 45) - 0.5f) * 0.9f; x += cosf(a); y += sinf(a);
        }
    }
}

// ---------- стены в двойном разрешении (для «Средней» и «Высокой»): те же кирпичи и плющ, но вдвое детальнее ----------
static const int TSH = 256;                          // размер «крупной» текстуры стены
static std::vector<u32> HW_TEX[4];
static SDL_Texture* WALLHI[4] = {NULL, NULL, NULL, NULL};
static bool hiWallsGen = false;
static void genHiWalls() {
    if (hiWallsGen) return;
    hiWallsGen = true;
    const int S = TSH; const float kk = 128.f / S;
    for (int t = 1; t <= 3; t++) HW_TEX[t].assign((size_t)S * S, 0xFF000000u);
    for (int y = 0; y < S; y++)
        for (int x = 0; x < S; x++) {
            float u = (x + 0.5f) * kk, v = (y + 0.5f) * kk;     // координаты в «старой» сетке 128x128, но с дробной частью
            size_t i = (size_t)y * S + x;
            {   // ---------- каменная кладка ----------
                int row = (int)(v / 16.f), off = (row & 1) * 16;
                float ux = fmodf(u + off, 128.f); int bx = (int)(ux / 32.f); float lx = ux - bx * 32.f, ly = v - row * 16.f;
                float bn = hnoise(bx, row, 1), base = 96 + bn * 54;
                float r = base + (hnoise(bx, row, 2) - 0.5f) * 26, g = base + (hnoise(bx, row, 4) - 0.5f) * 16, b = base + 12 + (hnoise(bx, row, 6) - 0.5f) * 18;
                float tintv = hnoise(bx, row, 20);
                if (tintv > 0.88f) { r *= 1.18f; g *= 0.92f; b *= 0.86f; }
                else if (tintv < 0.10f) { r *= 0.88f; g *= 0.98f; b *= 1.08f; }
                float grain = (vnoiseP(u / 2.f, v / 2.f, 3, 64) - 0.5f) * 30 + (hnoise(x, y, 3) - 0.5f) * 14 + (vnoiseP(u * 2.f, v * 2.f, 21, 256) - 0.5f) * 12;
                r += grain; g += grain; b += grain;
                float bev = 0;
                if (ly < 4) bev += 20 * (4 - ly) / 4.f;
                if (lx < 4) bev += 12 * (4 - lx) / 4.f;
                if (ly > 11) bev -= 26 * (ly - 11) / 4.f;
                if (lx > 27) bev -= 16 * (lx - 27) / 4.f;
                r += bev; g += bev; b += bev;
                if (hnoise((int)(u / 3.f), (int)(v / 3.f), 8) > 0.988f && std::min(std::min(lx, 31 - lx), std::min(ly, 15 - ly)) < 8) { r *= 0.62f; g *= 0.62f; b *= 0.62f; }
                if (hnoise(bx, row, 9) > 0.84f) {
                    float cyl = 7.f + 5.f * sinf(lx * 0.33f + bx * 2.f);
                    if (fabsf(ly - cyl) < 0.8f && lx > 3 && lx < 28) { r *= 0.35f; g *= 0.35f; b *= 0.35f; }
                }
                float mo = vnoiseP(u / 16.f, v / 16.f, 7, 8) * 0.55f + vnoiseP(u / 4.f, v / 4.f, 17, 32) * 0.45f + (ly > 9 ? 0.06f : 0.f) + v / 128.f * 0.10f;
                if (mo > 0.62f) { float t = std::min(1.f, (mo - 0.62f) * 4.5f); r = r * (1 - t) + (46 + hnoise(x, y, 18) * 14) * t; g = g * (1 - t) + (98 + hnoise(x, y, 18) * 30) * t; b = b * (1 - t) + 40 * t; }
                float sv = vnoiseP(u / 8.f, v / 32.f, 19, 16);
                if (sv > 0.68f) { float t = (sv - 0.68f) * 2.2f; r *= 1 - t * 0.35f; g *= 1 - t * 0.35f; b *= 1 - t * 0.3f; }
                if (ly < 2 || lx < 2) { float m = 40 + hnoise(x, y, 9) * 12; r = m; g = m - 2; b = m + 5; }
                else if (ly < 3 || lx < 3) { r *= 0.6f; g *= 0.6f; b *= 0.62f; }
                float ao = 1.f;
                if (v < 14) ao = 0.74f + 0.26f * sstep(0, 14, v);
                if (v > 128 - 20) ao = std::min(ao, 0.70f + 0.30f * sstep(128.f, 108.f, v));
                r *= ao; g *= ao; b *= ao;
                HW_TEX[1][i] = PX(C((int)r, (int)g, (int)b));
            }
            {   // ---------- доски баррикады ----------
                int pr = (int)(v / 32.f); float ly = v - pr * 32.f;
                float wr = 150 + hnoise(pr, 1, 11) * 34, wg = 100 + hnoise(pr, 1, 12) * 22, wb = 56 + hnoise(pr, 1, 13) * 10;
                float grain = 0.80f + 0.36f * vnoiseP(u / 32.f + pr * 3, v * 0.5f, 14 + pr, 4) + 0.12f * vnoiseP(u / 4.f, v / 1.5f, 15, 32) + 0.05f * (vnoiseP(u * 2.f, v * 6.f, 23, 256) - 0.5f);
                float r = wr * grain, g = wg * grain, b = wb * grain;
                float nz = (hnoise(x, y, 15) - 0.5f);
                r += nz * 14; g += nz * 10; b += nz * 6;
                float kx = 20 + hnoise(pr, 2, 16) * 88, ky = pr * 32 + 8 + hnoise(pr, 3, 16) * 16, kd = sqrtf((u - kx) * (u - kx) + (v - ky) * (v - ky) * 2.5f);
                if (kd < 8) { float t = 0.55f + 0.2f * sinf(kd * 1.6f); r *= t; g *= t; b *= t; }
                int seam = 30 + (pr * 41) % 68;
                if (ly < 2 || ly >= 30) { r = 50; g = 30; b = 15; }
                else if (ly < 3) { r += 24; g += 20; b += 10; }
                else if (ly >= 28) { r *= 0.7f; g *= 0.7f; b *= 0.7f; }
                if (u >= seam && u < seam + 1) { r *= 0.42f; g *= 0.42f; b *= 0.42f; }
                else if (u >= seam + 1 && u < seam + 2) { r += 20; g += 16; b += 8; }
                for (int nx : {9, 118}) {
                    float dd = sqrtf((u - (nx + 0.5f)) * (u - (nx + 0.5f)) + (ly - 16) * (ly - 16));
                    if (dd < 3.5f) { float hi = dd < 1.6f ? 1.f : 0.f; r = 64 + hi * 130 * (u < nx + 0.5f ? 1 : 0.6f); g = r; b = r + 6; }
                    else if (dd < 5.f) { r *= 0.7f; g *= 0.7f; b *= 0.7f; }
                }
                float ao = 1.f;
                if (v < 10) ao = 0.8f + 0.2f * sstep(0, 10, v);
                if (v > 128 - 14) ao = 0.75f + 0.25f * sstep(128.f, 114.f, v);
                HW_TEX[2][i] = PX(C((int)(r * ao), (int)(g * ao), (int)(b * ao)));
            }
            {   // ---------- живая изгородь ----------
                float n = vnoiseP(u / 8.f, v / 8.f, 11, 16) * 0.45f + vnoiseP(u / 4.f, v / 4.f, 12, 32) * 0.35f + vnoiseP(u / 2.f, v / 2.f, 13, 64) * 0.20f;
                float r = 18 + n * 40, g = 54 + n * 104, b = 20 + n * 32;
                float rid = 0.5f + 0.5f * sinf((u + v) * 0.55f + vnoiseP(u / 4.f, v / 4.f, 14, 32) * 6.f);
                r *= 0.85f + 0.2f * rid; g *= 0.85f + 0.2f * rid;
                float lf = vnoiseP(u, v, 22, 128); r *= 0.90f + 0.20f * lf; g *= 0.90f + 0.20f * lf;      // «листики» помельче
                float sp = hnoise(x, y, 13);
                if (sp < 0.13f) { r *= 0.45f; g *= 0.45f; b *= 0.45f; }
                else if (sp > 0.95f) { r += 30; g += 40; b += 10; }
                float ao = 1.f;
                if (v > 128 - 22) ao = 0.62f + 0.38f * sstep(128.f, 106.f, v);
                if (v < 12) ao = std::min(ao, 0.8f + 0.2f * sstep(0, 12, v));
                HW_TEX[3][i] = PX(C((int)(r * ao), (int)(g * ao), (int)(b * ao)));
            }
        }
    // плющ: те же лозы, что и на обычной стене, но с настоящими листьями (с прожилкой и светлой кромкой)
    for (int k = 0; k < 9; k++) {
        float x = (float)(hashu(k, 1, 131) % 128), ph = (hashu(k, 3, 131) % 628) / 100.f; int len = 40 + (int)(hashu(k, 2, 131) % 84);
        std::vector<float> path;
        for (int y = 0; y < len && y < 128; y++) { x += sinf(y * 0.13f + ph) * 0.6f + (hnoise(y, k, 132) - 0.5f) * 0.8f; path.push_back(x); }
        for (int y = 0; y < (int)path.size(); y++) {
            int hx = ((int)floorf(path[y] * 2.f) % S + S) % S;
            for (int sub = 0; sub < 2; sub++) {
                int hy = y * 2 + sub; if (hy >= S) continue;
                HW_TEX[1][(size_t)hy * S + hx] = PX(C(26, 54, 26)); HW_TEX[1][(size_t)hy * S + (hx + 1) % S] = PX(C(34, 70, 32));
            }
            if (y % 3 == 0) {
                int side = (hnoise(y, k, 136) > 0.5f) ? 1 : -1;
                for (int ly = -5; ly <= 5; ly++)
                    for (int lx = 0; lx <= 8; lx++) {
                        float fx = lx / 2.f, fy = ly / 2.f;
                        if (fx * fx + fy * fy * 2.f > 9.5f) continue;
                        int px = ((hx + side * (lx + 2)) % S + S) % S, py = y * 2 + ly; if (py < 0 || py >= S) continue;
                        float sh = 0.75f + 0.5f * hnoise(px, py, 137) + (ly < 0 ? 0.2f : -0.05f);
                        bool rim = fx * fx + fy * fy * 2.f > 7.4f, vein = ly == 0 && lx >= 1;
                        if (rim) sh += 0.16f;
                        if (vein) sh += 0.22f;
                        HW_TEX[1][(size_t)py * S + px] = PX(C((int)(38 * sh), (int)(112 * sh), (int)(40 * sh)));
                    }
            }
        }
    }
}
static SDL_Texture* makeTexSmooth(const std::vector<u32>& px, int w, int h);
static void makeHiWallTex(bool force = false) {
    genHiWalls();
    for (int t = 1; t <= 3; t++) {
        if (WALLHI[t] && !force) continue;
        if (WALLHI[t]) SDL_DestroyTexture(WALLHI[t]);
        WALLHI[t] = makeTexSmooth(HW_TEX[t], TSH, TSH);
        if (WALLHI[t]) SDL_SetTextureBlendMode(WALLHI[t], SDL_BLENDMODE_NONE);
    }
}

// ---------- эффекты (кровь, частицы) ----------
struct Particle { float x, y, z, vx, vy, vz, life, maxl, sz; Col c; };
static std::vector<Particle> parts;
struct ZLite { float hp, x, y; int kind; bool slam; };
struct Corpse { float x, y; int kind; float t; };
struct Decal { float x, y, size, age; bool scorch; };
static std::vector<Corpse> corpses;
static std::vector<Decal> decals;
struct DmgNum { float x, y, z, vz, life, maxl; int val; bool head; };
static std::vector<DmgNum> dmgNums;
static std::map<int, ZLite> lastZ;
static float animT = 0;
static void spawnBurst(float x, float y, float z, int n, float spd, int mode = 0) {
    for (int i = 0; i < n && parts.size() < 420; i++) {
        Particle p; p.x = x; p.y = y; p.z = z;
        float a = frand() * 6.2832f, s = spd * (0.3f + frand());
        p.vx = cosf(a) * s; p.vy = sinf(a) * s; p.vz = frand() * spd * 1.3f + 0.6f;
        p.life = p.maxl = 0.6f + frand() * 1.2f; p.sz = 0.03f + frand() * 0.045f;
        float r = frand();
        if (mode == 1) { p.c = r < 0.35f ? C(255, 150, 40) : (r < 0.7f ? C(255, 215, 90) : C(78, 76, 78)); p.sz = 0.05f + frand() * 0.07f; p.life = p.maxl = 0.5f + frand() * 1.1f; }
        else if (mode == 2) { p.c = C(150 + irand(0, 30), 138 + irand(0, 24), 116); p.sz = 0.05f + frand() * 0.06f; }
        else if (mode == 3) { p.c = r < 0.5f ? C(240, 248, 255) : C(140, 200, 255); p.sz = 0.04f + frand() * 0.06f; p.life = p.maxl = 0.5f + frand() * 0.8f; }
        else p.c = r < 0.7f ? C(140 + irand(0, 70), 18, 16) : C(84, 150, 36);
        parts.push_back(p);
    }
}
// ============================ ЗВУК (весь синтезируется в коде, файлов не нужно) ============================
static SDL_AudioDeviceID adev = 0;
static bool audioOK = false;
static const int SR = 22050;
static std::vector<short> SND[S_N];
struct Voice { int id; float pos, step, gl, gr; bool loop, active; };
static Voice voices[28];
static float masterVol = 0.9f;

static inline float srnd() { return frand() * 2.f - 1.f; }
static void sTone(std::vector<float>& b, float t0, float dur, float f0, float f1, float amp, float decay, int wave, float vib = 0.f) {
    int n0 = (int)(t0 * SR), n = (int)(dur * SR);
    if ((int)b.size() < n0 + n) b.resize(n0 + n, 0.f);
    float ph = 0.f;
    for (int i = 0; i < n; i++) {
        float t = (float)i / SR, fr = t / dur, f = f0 + (f1 - f0) * fr;
        if (vib > 0.f) f *= 1.f + vib * sinf(t * 37.f);
        ph += 6.2831853f * f / SR;
        float s;
        if (wave == 0) s = sinf(ph);
        else if (wave == 1) { float q = ph / 6.2831853f; s = 2.f * (q - floorf(q)) - 1.f; }
        else { float q = ph / 6.2831853f; s = (q - floorf(q)) < 0.5f ? 1.f : -1.f; }
        b[n0 + i] += s * amp * expf(-decay * t) * std::min(1.f, t / 0.004f);
    }
}
static void sNoise(std::vector<float>& b, float t0, float dur, float amp, float decay, float lp, float hp = 0.f) {
    int n0 = (int)(t0 * SR), n = (int)(dur * SR);
    if ((int)b.size() < n0 + n) b.resize(n0 + n, 0.f);
    float y = 0.f, y2 = 0.f;
    for (int i = 0; i < n; i++) {
        float t = (float)i / SR, x = srnd();
        y += lp * (x - y);
        float o = y;
        if (hp > 0.f) { y2 += hp * (y - y2); o = y - y2; }
        b[n0 + i] += o * amp * expf(-decay * t) * std::min(1.f, t / 0.002f);
    }
}
static void sFinish(int id, std::vector<float>& b, float peak) {
    float mx = 1e-6f;
    for (size_t i = 0; i < b.size(); i++) mx = std::max(mx, fabsf(b[i]));
    SND[id].resize(b.size());
    float k = peak * 32767.f / mx;
    for (size_t i = 0; i < b.size(); i++) {
        float v = b[i] * k;
        if (i + 200 > b.size()) v *= (float)(b.size() - i) / 200.f;      // плавный конец, без щелчка
        SND[id][i] = (short)std::max(-32767.f, std::min(32767.f, v));
    }
}
static void genSounds() {
    for (int id = 0; id < S_N; id++) {
        std::vector<float> b;
        switch (id) {
            case S_PISTOL: sTone(b, 0, 0.12f, 150, 50, 0.9f, 22, 0); sNoise(b, 0, 0.09f, 0.9f, 42, 0.55f); sNoise(b, 0, 0.02f, 0.5f, 90, 0.9f, 0.2f); sNoise(b, 0.02f, 0.3f, 0.22f, 9, 0.10f); sFinish(id, b, 0.62f); break;
            case S_SHOTGUN: sTone(b, 0, 0.25f, 95, 32, 1.0f, 14, 0); sNoise(b, 0, 0.22f, 1.0f, 14, 0.4f); sNoise(b, 0.02f, 0.6f, 0.35f, 6, 0.08f); sNoise(b, 0, 0.03f, 0.5f, 60, 0.9f, 0.2f); sFinish(id, b, 0.8f); break;
            case S_RIFLE: sTone(b, 0, 0.1f, 170, 60, 0.8f, 30, 0); sNoise(b, 0, 0.07f, 0.9f, 55, 0.72f); sNoise(b, 0, 0.015f, 0.6f, 120, 0.95f, 0.25f); sNoise(b, 0.02f, 0.25f, 0.2f, 10, 0.12f); sFinish(id, b, 0.62f); break;
            case S_REVOLVER: sTone(b, 0, 0.2f, 115, 38, 1.0f, 16, 0); sNoise(b, 0, 0.14f, 0.95f, 28, 0.45f); sNoise(b, 0.02f, 0.5f, 0.3f, 7, 0.09f); sNoise(b, 0, 0.02f, 0.6f, 90, 0.9f, 0.2f); sFinish(id, b, 0.8f); break;
            case S_SMG: sTone(b, 0, 0.06f, 210, 90, 0.7f, 45, 0); sNoise(b, 0, 0.05f, 0.9f, 70, 0.65f); sNoise(b, 0.02f, 0.12f, 0.12f, 20, 0.15f); sFinish(id, b, 0.5f); break;
            case S_SNIPER: sTone(b, 0, 0.35f, 72, 28, 1.0f, 9, 0); sNoise(b, 0, 0.3f, 1.0f, 10, 0.3f); sNoise(b, 0, 0.03f, 0.7f, 70, 0.95f, 0.3f); sNoise(b, 0.05f, 1.0f, 0.3f, 3.5f, 0.06f); sFinish(id, b, 0.85f); break;
            case S_LMG: sTone(b, 0, 0.07f, 155, 55, 0.85f, 35, 0); sNoise(b, 0, 0.06f, 0.95f, 55, 0.6f); sNoise(b, 0, 0.02f, 0.55f, 95, 0.9f, 0.2f); sNoise(b, 0.02f, 0.18f, 0.18f, 10, 0.13f); sFinish(id, b, 0.68f); break;
            case S_OBREZ: sTone(b, 0, 0.18f, 105, 30, 1.0f, 12, 0); sNoise(b, 0, 0.20f, 1.0f, 12, 0.45f); sNoise(b, 0.015f, 0.5f, 0.32f, 5, 0.09f); sNoise(b, 0, 0.025f, 0.55f, 65, 0.9f, 0.22f); sFinish(id, b, 0.85f); break;
            case S_RELOAD: sNoise(b, 0.0f, 0.02f, 0.8f, 90, 0.9f, 0.15f); sTone(b, 0.0f, 0.03f, 2400, 1800, 0.25f, 90, 0); sNoise(b, 0.32f, 0.03f, 0.9f, 80, 0.9f, 0.15f); sTone(b, 0.32f, 0.04f, 1500, 1100, 0.3f, 80, 0); sNoise(b, 0.5f, 0.05f, 0.5f, 60, 0.5f); sFinish(id, b, 0.4f); break;
            case S_EMPTY: sNoise(b, 0, 0.02f, 0.8f, 100, 0.9f, 0.2f); sTone(b, 0, 0.03f, 1200, 900, 0.3f, 90, 0); sFinish(id, b, 0.35f); break;
            case S_HIT: sNoise(b, 0, 0.07f, 0.8f, 38, 0.3f); sTone(b, 0, 0.09f, 190, 80, 0.7f, 30, 0); sFinish(id, b, 0.5f); break;
            case S_JUMP: sTone(b, 0, 0.09f, 260, 430, 0.55f, 16, 0); sNoise(b, 0, 0.03f, 0.4f, 60, 0.9f, 0.15f); sFinish(id, b, 0.42f); break;
            case S_LAND: sNoise(b, 0, 0.1f, 0.9f, 24, 0.35f); sTone(b, 0, 0.08f, 140, 60, 0.6f, 22, 0); sFinish(id, b, 0.5f); break;
            case S_HEAD: sNoise(b, 0, 0.08f, 0.8f, 36, 0.35f); sTone(b, 0, 0.1f, 200, 90, 0.7f, 28, 0); sTone(b, 0.01f, 0.18f, 1500, 1400, 0.35f, 22, 0); sFinish(id, b, 0.55f); break;
            case S_ZDIE: sTone(b, 0, 0.8f, 140, 45, 0.7f, 3.5f, 1, 0.05f); sNoise(b, 0, 0.5f, 0.35f, 5, 0.1f); sFinish(id, b, 0.55f); { float y = 0; for (size_t i = 0; i < SND[id].size(); i++) { y += 0.16f * (SND[id][i] - y); SND[id][i] = (short)y; } } break;
            case S_GROAN1: sTone(b, 0, 1.0f, 96, 68, 0.8f, 2.4f, 1, 0.06f); sNoise(b, 0, 0.9f, 0.25f, 3, 0.06f); sFinish(id, b, 0.4f); { float y = 0; for (size_t i = 0; i < SND[id].size(); i++) { y += 0.14f * (SND[id][i] - y); SND[id][i] = (short)y; } } break;
            case S_GROAN2: sTone(b, 0, 0.8f, 122, 90, 0.8f, 3.0f, 1, 0.08f); sNoise(b, 0, 0.7f, 0.22f, 4, 0.07f); sFinish(id, b, 0.4f); { float y = 0; for (size_t i = 0; i < SND[id].size(); i++) { y += 0.16f * (SND[id][i] - y); SND[id][i] = (short)y; } } break;
            case S_ROAR: sTone(b, 0, 1.6f, 62, 44, 0.9f, 1.4f, 1, 0.07f); sTone(b, 0, 1.6f, 31, 22, 0.7f, 1.4f, 0); sNoise(b, 0, 1.4f, 0.35f, 1.6f, 0.08f); sFinish(id, b, 0.7f); { float y = 0; for (size_t i = 0; i < SND[id].size(); i++) { y += 0.2f * (SND[id][i] - y); SND[id][i] = (short)y; } } break;
            case S_SPIT: sTone(b, 0, 0.25f, 950, 220, 0.4f, 8, 0); sNoise(b, 0, 0.22f, 0.5f, 10, 0.75f, 0.1f); sFinish(id, b, 0.4f); break;
            case S_SPLAT: sNoise(b, 0, 0.15f, 0.9f, 20, 0.22f); sTone(b, 0, 0.1f, 300, 120, 0.4f, 30, 0); sFinish(id, b, 0.45f); break;
            case S_EXPLODE: sNoise(b, 0, 1.4f, 1.0f, 3.2f, 0.09f); sTone(b, 0, 0.7f, 75, 24, 1.0f, 4.5f, 0); sNoise(b, 0, 0.3f, 0.6f, 14, 0.6f); sNoise(b, 0.1f, 0.5f, 0.3f, 6, 0.3f); sFinish(id, b, 0.9f); break;
            case S_HURT: sNoise(b, 0, 0.12f, 0.8f, 26, 0.25f); sTone(b, 0, 0.2f, 210, 95, 0.8f, 16, 0); sFinish(id, b, 0.6f); break;
            case S_PICKUP: sTone(b, 0, 0.1f, 880, 880, 0.5f, 18, 0); sTone(b, 0.07f, 0.16f, 1320, 1320, 0.5f, 14, 0); sFinish(id, b, 0.4f); break;
            case S_LEVEL: { static const float N4[4] = {523.f, 659.f, 784.f, 1047.f}; for (int k = 0; k < 4; k++) sTone(b, k * 0.11f, 0.4f, N4[k], N4[k], 0.5f, 6, 0); sFinish(id, b, 0.5f); } break;
            case S_WAVE: sTone(b, 0, 1.3f, 110, 110, 0.6f, 1.6f, 1, 0.01f); sTone(b, 0, 1.3f, 165, 165, 0.4f, 1.6f, 1, 0.01f); sTone(b, 0, 1.3f, 220, 220, 0.25f, 1.6f, 1, 0.01f); sFinish(id, b, 0.55f); { float y = 0; for (size_t i = 0; i < SND[id].size(); i++) { y += 0.3f * (SND[id][i] - y); SND[id][i] = (short)y; } } break;
            case S_CLEAR: { static const float N3[3] = {659.f, 784.f, 988.f}; for (int k = 0; k < 3; k++) sTone(b, k * 0.16f, 0.6f, N3[k], N3[k], 0.5f, 4.5f, 0); sFinish(id, b, 0.5f); } break;
            case S_BUY: sTone(b, 0, 0.12f, 1568, 1568, 0.5f, 18, 0); sTone(b, 0.06f, 0.25f, 2093, 2093, 0.5f, 12, 0); sNoise(b, 0, 0.02f, 0.4f, 100, 0.9f, 0.2f); sFinish(id, b, 0.4f); break;
            case S_CLICK: sNoise(b, 0, 0.012f, 0.8f, 120, 0.9f, 0.2f); sTone(b, 0, 0.02f, 1300, 1000, 0.3f, 100, 0); sFinish(id, b, 0.3f); break;
            case S_BUILD: sTone(b, 0, 0.06f, 190, 120, 0.8f, 40, 0); sNoise(b, 0, 0.05f, 0.6f, 50, 0.35f); sTone(b, 0.16f, 0.07f, 175, 110, 0.8f, 36, 0); sNoise(b, 0.16f, 0.05f, 0.6f, 50, 0.35f); sFinish(id, b, 0.55f); break;
            case S_BREAK: for (int k = 0; k < 7; k++) sNoise(b, k * 0.06f + frand() * 0.03f, 0.12f, 0.7f, 22, 0.3f + frand() * 0.3f); sTone(b, 0, 0.4f, 95, 50, 0.6f, 8, 0); sFinish(id, b, 0.65f); break;
            case S_SLAM: sTone(b, 0, 0.5f, 62, 24, 1.0f, 5, 0); sNoise(b, 0, 0.6f, 0.8f, 6, 0.1f); sFinish(id, b, 0.85f); break;
            case S_STEP1: sNoise(b, 0, 0.07f, 0.8f, 40, 0.07f); sFinish(id, b, 0.3f); break;
            case S_STEP2: sNoise(b, 0, 0.07f, 0.8f, 44, 0.09f); sFinish(id, b, 0.3f); break;
            case S_HEART: sTone(b, 0, 0.09f, 62, 45, 1.0f, 28, 0); sTone(b, 0.2f, 0.09f, 58, 42, 0.8f, 28, 0); sFinish(id, b, 0.55f); break;
            case S_WIND: {
                const int L = SR * 5, X = SR / 2;
                std::vector<float> raw(L + X); float y = 0, y2 = 0;
                for (int i = 0; i < L + X; i++) { float t = (float)i / SR, mod = 0.55f + 0.45f * sinf(t * 6.2831853f * 0.4f), x = srnd(); y += (0.02f + 0.03f * mod) * (x - y); y2 += 0.02f * (y - y2); raw[i] = (y * 0.7f + y2 * 0.5f) * (0.5f + 0.5f * mod); }
                b.assign(L, 0.f);
                for (int i = 0; i < L; i++) { float v = raw[i]; if (i < X) { float w = (float)i / X; v = raw[i] * w + raw[L + i] * (1.f - w); } b[i] = v; }
                float mx = 1e-6f; for (int i = 0; i < L; i++) mx = std::max(mx, fabsf(b[i]));
                SND[id].resize(L); for (int i = 0; i < L; i++) SND[id][i] = (short)(b[i] / mx * 0.5f * 32767.f);
            } break;
            case S_CRICKET: {
                const int L = SR * 4; b.assign(L, 0.f);
                for (int k = 0; k < 9; k++) { float t0 = 0.25f + k * 0.42f; if (t0 + 0.22f > 4.f) break; for (int q = 0; q < 4; q++) sTone(b, t0 + q * 0.05f, 0.03f, 4200 + (k % 3) * 150, 4300, 0.5f, 80, 0); }
                b.resize(L, 0.f);
                float mx = 1e-6f; for (int i = 0; i < L; i++) mx = std::max(mx, fabsf(b[i]));
                SND[id].resize(L); for (int i = 0; i < L; i++) SND[id][i] = (short)(b[i] / mx * 0.35f * 32767.f);
            } break;
        }
    }
}
static void audioCb(void*, Uint8* stream, int len) {
    short* out = (short*)stream; int frames = len / 4;
    for (int i = 0; i < frames; i++) {
        int l = 0, r = 0;
        for (int v = 0; v < 28; v++) {
            Voice& V = voices[v];
            if (!V.active) continue;
            const std::vector<short>& bf = SND[V.id];
            int ip = (int)V.pos;
            if (ip + 1 >= (int)bf.size()) { if (V.loop) { V.pos -= (float)bf.size(); ip = (int)V.pos; if (ip < 0) ip = 0; } else { V.active = false; continue; } }
            float fr = V.pos - ip; int s = (int)(bf[ip] * (1.f - fr) + bf[std::min((int)bf.size() - 1, ip + 1)] * fr);
            V.pos += V.step;
            l += (int)(s * V.gl); r += (int)(s * V.gr);
        }
        out[2 * i] = (short)std::max(-32767, std::min(32767, l)); out[2 * i + 1] = (short)std::max(-32767, std::min(32767, r));
    }
}
static void playSound(int id, float vol, float pan, float rate, bool loop) {
    if (!audioOK || !soundOn || id < 0 || id >= S_N || SND[id].empty()) return;
    SDL_LockAudioDevice(adev);
    int slot = -1; float oldest = 1e9f;
    for (int v = 0; v < 28; v++) { if (!voices[v].active) { slot = v; break; } if (voices[v].pos < oldest && !voices[v].loop) { oldest = voices[v].pos; slot = v; } }
    if (slot >= 0) {
        Voice& V = voices[slot]; V.id = id; V.pos = 0; V.step = rate; V.loop = loop; V.active = true;
        float g = std::max(0.f, std::min(1.5f, vol)) * masterVol, p = std::max(-1.f, std::min(1.f, pan));
        V.gl = g * sqrtf(0.5f * (1.f - p)); V.gr = g * sqrtf(0.5f * (1.f + p));
    }
    SDL_UnlockAudioDevice(adev);
}
static void playAt(int id, float x, float y, float vol, float rate) {
    if (!P) return;
    float rx = x - P->x, ry = y - P->y, d = sqrtf(rx * rx + ry * ry);
    float att = 1.f / (1.f + d * 0.38f); if (d > 22.f) return;
    float pan = d > 0.05f ? (rx * (-sinf(P->ang)) + ry * cosf(P->ang)) / d : 0.f;
    playSound(id, vol * att * 1.3f, pan * 0.85f, rate * (0.96f + 0.08f * frand()), false);
}
static void stopAllSounds() {
    if (!audioOK) return;
    SDL_LockAudioDevice(adev);
    for (int v = 0; v < 28; v++) voices[v].active = false;
    SDL_UnlockAudioDevice(adev);
}
static bool ambientOn = false;
static void ambientStart() {
    if (ambientOn || !audioOK || !soundOn) return;
    ambientOn = true; playSound(S_WIND, 0.30f, 0.f, 1.f, true); playSound(S_CRICKET, 0.14f, 0.2f, 1.f, true);
}
static void ambientStop() {
    if (!ambientOn) return;
    ambientOn = false;
    if (!audioOK) return;
    SDL_LockAudioDevice(adev);
    for (int v = 0; v < 28; v++) if (voices[v].loop) voices[v].active = false;
    SDL_UnlockAudioDevice(adev);
}
static bool initAudio() {
    if (SDL_InitSubSystem(SDL_INIT_AUDIO) != 0) return false;
    SDL_AudioSpec want, have; memset(&want, 0, sizeof want);
    want.freq = SR; want.format = AUDIO_S16SYS; want.channels = 2; want.samples = 1024; want.callback = audioCb;
    adev = SDL_OpenAudioDevice(NULL, 0, &want, &have, 0);
    if (adev == 0) return false;
    genSounds();
    SDL_PauseAudioDevice(adev, 0);
    audioOK = true;
    return true;
}
static void toastSound(const std::string& t) {       // звук по тексту уведомления (работает и у клиента)
    if (t.find("КУПЛЕНО") == 0) playSound(S_BUY, 0.8f);
    else if (t.find("АПТЕЧКА: +50") == 0) playSound(S_PICKUP, 0.7f);
    else if (t.find("ПОЧИНЕНО") == 0) playSound(S_BUILD, 0.6f);
    else if (t.find("БАРРИКАДУ") == 0) playSound(S_BREAK, 0.7f);
    else if (t.find("ВОЛНА") == 0) playSound(t.find("ОТБИТА") != std::string::npos ? S_CLEAR : S_WAVE, 0.8f);
}

static float fireAnim = 0.f, gDt = 0.016f, shakeT = 0.f, boomFlashT = 0.f, stunFlashT = 0.f;         // фаза анимации выстрела (1 -> 0)
static bool shotEvent = false, lastFlashHigh = false;
static const float FANIM[NW] = {0.30f, 0.85f, 0.17f, 0.42f, 0.14f, 0.95f, 0.13f, 0.80f};   // длительность анимации по оружию
static void spawnDecal(float x, float y, float size, bool scorch = false) {
    Decal d; d.x = x + rr(-0.25f, 0.25f); d.y = y + rr(-0.25f, 0.25f); d.size = size; d.age = 0; d.scorch = scorch;
    if (decals.size() >= 90) decals.erase(decals.begin());
    decals.push_back(d);
}
static void updateParts(float dt) {
    animT += dt;
    {   // баннеры волн, кровавая луна, серия убийств, статистика забега
        if (mode == M_PLAY) {
            if (!prep && wave > 0 && (wave != lastBannerWave || lastBannerPrep)) {
                bool boss = wave % 5 == 0;
                bannerS = fmt("ВОЛНА %d", wave); bannerS2 = bloodNight ? "КРОВАВАЯ НОЧЬ!" : (boss ? "БОСС - ТИРАН!" : ""); bannerCol = bloodNight ? 3 : (boss ? 1 : 0); bannerT = bannerMax = (boss || bloodNight) ? 3.2f : 2.4f;
            } else if (prep && !lastBannerPrep && wave > 0) { bannerS = fmt("ВОЛНА %d ОТБИТА!", wave); bannerS2 = "ЧИНИ СТЕНЫ И СОБИРАЙ ЯЩИКИ"; bannerCol = 2; bannerT = bannerMax = 2.8f; }
            lastBannerWave = wave; lastBannerPrep = prep;
            runTime += dt;
        }
        bannerT = std::max(0.f, bannerT - dt);
        float tgt = (mode == M_PLAY && !prep && wave > 0) ? 1.f : 0.f; bloodMoon += (tgt - bloodMoon) * std::min(1.f, dt * 0.9f);
        if (P->kills > lastKillsSeen) { hudCombo += P->kills - lastKillsSeen; hudComboT = 3.5f; comboPop = 0.3f; }
        if (P->kills < lastKillsSeen) hudCombo = 0;
        lastKillsSeen = P->kills;
        if (hudComboT > 0) { hudComboT -= dt; if (hudComboT <= 0) hudCombo = 0; }
        comboPop = std::max(0.f, comboPop - dt);
        static float lastHeadT = 0; if (P->headT > 0.3f && lastHeadT <= 0.3f) { statHead++; questProgress(QT_HEADSHOT, 1); } lastHeadT = P->headT;
    }
    {   // события выстрела: по переднему фронту вспышки запускаем анимацию
        bool high = P && P->flash > 0.062f;
        if (high && !lastFlashHigh) { fireAnim = 1.f; shotEvent = true; }
        lastFlashHigh = high;
        if (fireAnim > 0.f) fireAnim = std::max(0.f, fireAnim - dt / FANIM[std::max(0, std::min(NW - 1, P->weapon))]);
    }
    {   // звуки по событиям: выстрелы всех игроков, перезарядка, урон, сердцебиение, подбор ящиков, повышение уровня, стоны зомби
        static std::map<int, bool> lastFl;
        for (std::map<int, Player>::iterator it = players.begin(); it != players.end(); ++it) {
            Player& pp = it->second; bool high = pp.flash > 0.062f; bool& lf = lastFl[pp.id];
            if (high && !lf) { int sid = std::max(0, std::min(NW - 1, pp.weapon)); if (&pp == P) playSound(sid, 0.85f); else playAt(sid, pp.x, pp.y, 0.9f); }
            lf = high;
        }
        static float lastReload = 0, lastHurt = 0, heartT = 0, groanT = 3.f; static bool lastMenu = false;
        if (P->reload > 0 && lastReload <= 0) playSound(S_RELOAD, 0.6f);
        lastReload = P->reload;
        if (P->hurt >= 0.33f && lastHurt < 0.33f) playSound(S_HURT, 0.9f);
        lastHurt = P->hurt;
        if (P->menu && !lastMenu) playSound(S_LEVEL, 0.8f);
        lastMenu = P->menu;
        heartT -= dt;
        if (mode == M_PLAY && !P->dead && P->hp < P->maxhp * 0.33f && heartT <= 0) { playSound(S_HEART, 0.7f); heartT = 0.9f; }
        groanT -= dt;
        if (groanT <= 0 && mode == M_PLAY && !zombies.empty()) {
            groanT = rr(2.2f, 5.5f);
            const Zombie& z = zombies[irand(0, (int)zombies.size() - 1)];
            playAt(z.kind == 5 ? S_ROAR : (frand() < 0.5f ? S_GROAN1 : S_GROAN2), z.x, z.y, 0.8f, z.kind == 2 ? 0.8f : (z.kind == 1 ? 1.15f : 1.f));
        }
        static std::vector<std::pair<float, float> > lastCr;
        if (mode == M_PLAY) {
            for (size_t i = 0; i < lastCr.size(); i++) {
                bool still = false;
                for (size_t k = 0; k < crates.size(); k++) if (fabsf(crates[k].x - lastCr[i].first) < 0.06f && fabsf(crates[k].y - lastCr[i].second) < 0.06f) { still = true; break; }
                if (!still && hypotf(lastCr[i].first - P->x, lastCr[i].second - P->y) < 1.6f) playSound(S_PICKUP, 0.8f);
            }
        }
        lastCr.clear();
        for (size_t k = 0; k < crates.size(); k++) lastCr.push_back(std::make_pair(crates[k].x, crates[k].y));
    }
    {
        static size_t lastSpits = 0;
        if (spits.size() > lastSpits && mode == M_PLAY) playAt(S_SPIT, spits.back().x, spits.back().y, 0.8f);
        lastSpits = spits.size();
        shakeT = std::max(0.f, shakeT - dt); boomFlashT = std::max(0.f, boomFlashT - dt); stunFlashT = std::max(0.f, stunFlashT - dt);
    }
    for (size_t i = 0; i < dmgNums.size();) { DmgNum& d = dmgNums[i]; d.life -= dt; d.z += d.vz * dt; d.vz *= 0.94f; if (d.life <= 0) dmgNums.erase(dmgNums.begin() + i); else i++; }
    for (size_t i = 0; i < corpses.size();) { corpses[i].t += dt; if (corpses[i].t > 12.f) corpses.erase(corpses.begin() + i); else i++; }
    for (size_t i = 0; i < decals.size();) { decals[i].age += dt; if (decals[i].age > 60.f) decals.erase(decals.begin() + i); else i++; }
    for (size_t i = 0; i < parts.size();) {
        Particle& p = parts[i];
        p.life -= dt;
        if (p.life <= 0) { parts[i] = parts.back(); parts.pop_back(); continue; }
        if (p.z > 0.025f || p.vz > 0) {
            p.vz -= 9.f * dt; p.x += p.vx * dt; p.y += p.vy * dt; p.z += p.vz * dt;
            if (p.z < 0.025f) { p.z = 0.025f; p.vz = 0; p.vx = p.vy = 0; }
        }
        i++;
    }
}
static void explosionFx(float x, float y) {
    spawnBurst(x, y, 0.4f, 70, 5.5f, 1); spawnBurst(x, y, 0.4f, 30, 2.5f, 2);
    spawnDecal(x, y, 1.6f, true);
    playAt(S_EXPLODE, x, y, 1.0f);
    float d = hypotf(x - P->x, y - P->y);
    if (d < 9.f) { shakeT = std::max(shakeT, 0.45f * (1.f - d / 9.f) + 0.1f); boomFlashT = std::max(boomFlashT, 0.28f * (1.f - d / 9.f) + 0.05f); }
}
static std::map<int, Gren> lastG;
static void stunFx(float x, float y) {
    spawnBurst(x, y, 0.4f, 46, 4.8f, 3); spawnBurst(x, y, 0.5f, 18, 2.2f, 3);
    playAt(S_EXPLODE, x, y, 0.8f, 1.8f);
    float d = hypotf(x - P->x, y - P->y);
    stunFlashT = std::max(stunFlashT, d < 8.f ? 0.9f : 0.45f);
    if (d < 9.f) shakeT = std::max(shakeT, 0.2f);
}
static void trackEffects() {
    {   // гранаты: звук броска и эффект взрыва (одинаково у хоста и у клиентов)
        std::map<int, Gren> nowG;
        for (size_t i = 0; i < grens.size(); i++) {
            nowG[grens[i].id] = grens[i];
            if (!lastG.count(grens[i].id)) playAt(S_JUMP, grens[i].x, grens[i].y, 0.5f, 1.5f);
        }
        for (std::map<int, Gren>::iterator it = lastG.begin(); it != lastG.end(); ++it)
            if (!nowG.count(it->first)) { if (it->second.type == 0) explosionFx(it->second.x, it->second.y); else stunFx(it->second.x, it->second.y); }
        lastG.swap(nowG);
    }
    std::map<int, ZLite> now;
    for (size_t i = 0; i < zombies.size(); i++) {
        const Zombie& z = zombies[i];
        bool sl = z.slam || z.slamFlash > 0;
        ZLite zl = {z.hp, z.x, z.y, z.kind, sl};
        std::map<int, ZLite>::iterator it = lastZ.find(z.id);
        if (it != lastZ.end() && z.hp < it->second.hp - 0.5f) {
            DmgNum dn; dn.x = z.x + rr(-0.15f, 0.15f); dn.y = z.y + rr(-0.15f, 0.15f); dn.z = z.hs * 0.95f; dn.vz = 0.55f; dn.maxl = dn.life = 0.9f; dn.val = (int)(it->second.hp - z.hp + 0.5f); dn.head = P->headT > 0;
            if (dmgNums.size() < 40) dmgNums.push_back(dn);
            playAt(P->headT > 0 ? S_HEAD : S_HIT, z.x, z.y, 0.8f); spawnBurst(z.x, z.y, 0.55f, 5, 2.2f); if (frand() < 0.45f) spawnDecal(z.x, z.y, 0.35f + frand() * 0.2f); }
        if (it == lastZ.end() && z.kind == 5 && mode == M_PLAY) playAt(S_ROAR, z.x, z.y, 1.2f);
        if (it != lastZ.end() && sl && !it->second.slam) {           // удар босса о землю
            spawnBurst(z.x, z.y, 0.1f, 40, 3.8f, 2); playAt(S_SLAM, z.x, z.y, 1.1f);
            float d = hypotf(z.x - P->x, z.y - P->y); if (d < 8.f) shakeT = std::max(shakeT, 0.4f * (1.f - d / 8.f) + 0.1f);
        }
        now[z.id] = zl;
    }
    for (std::map<int, ZLite>::iterator it = lastZ.begin(); it != lastZ.end(); ++it)
        if (!now.count(it->first)) {
            if (it->second.kind == 4) explosionFx(it->second.x, it->second.y);
            spawnBurst(it->second.x, it->second.y, 0.5f, it->second.kind == 5 ? 60 : 18, 3.4f);
            playAt(S_ZDIE, it->second.x, it->second.y, 0.9f); playAt(S_SPLAT, it->second.x, it->second.y, 0.6f);
            spawnDecal(it->second.x, it->second.y, 0.9f + frand() * 0.4f); spawnDecal(it->second.x, it->second.y, 0.5f + frand() * 0.3f);
            Corpse c = {it->second.x, it->second.y, it->second.kind, 0.f};
            if (corpses.size() >= 40) corpses.erase(corpses.begin());
            corpses.push_back(c);
        }
    lastZ.swap(now);
}
static void fxReset() { parts.clear(); lastG.clear(); lastZ.clear(); corpses.clear(); decals.clear(); dmgNums.clear(); }
// ---------- декорации мира (камни, трава, пни, бочки, кости): детерминированы по карте, поэтому сеть не нужна ----------
struct Deco { float x, y; int kind; };
static std::vector<Deco> decos;
static const float DHS[8] = {0.22f, 0.24f, 0.34f, 0.60f, 0.14f, 0.60f, 0.44f, 0.80f};     // высота предметов
static const float DR[8] = {0.f, 0.f, 0.30f, 0.18f, 0.f, 0.18f, 0.16f, 0.f};            // радиус столкновения (0 — проходимый); бочки (3,5) и ящик (6) уменьшены, чтобы через них было легче перепрыгнуть
static int solidDeco[N * N];
static const float BOX_HP = 50.f;                // прочность ящика (kind 6)
static std::vector<float> boxHp;                 // HP каждой декорации: у ящиков BOX_HP..0, у остальных -1
static void genDecos() {
    decos.clear();
    for (int i = 0; i < N * N; i++) solidDeco[i] = -1;
    for (int i = 0; i < N * N; i++) {
        int cx = i % N, cy = i / N;
        if (G[i] == 1 || G[i] == 3 || (abs(cx - C0) <= 5 && abs(cy - C0) <= 5)) continue;
        u32 h = hashu(cx, cy, 91);
        if (h % 100 >= 12) continue;
        int n = 1 + (int)((h >> 8) % 2);
        for (int k = 0; k < n; k++) {
            Deco d; u32 h2 = hashu(cx, cy, 92 + k);
            d.x = cx + 0.2f + (h2 & 255) / 255.f * 0.6f; d.y = cy + 0.2f + ((h2 >> 8) & 255) / 255.f * 0.6f;
            int r = (int)((h2 >> 16) % 10);
            if (r <= 2 || r == 9) d.kind = 0; else if (r == 3) d.kind = 6; else if (r <= 5) d.kind = 1; else if (r == 6) d.kind = 2; else if (r == 7) d.kind = ((h2 >> 24) & 1) ? 5 : 3; else d.kind = 4;
            decos.push_back(d);
            if (DR[d.kind] > 0.f && solidDeco[i] < 0) solidDeco[i] = (int)decos.size() - 1;      // не более одного твёрдого предмета на клетку
        }
    }
    // факелы по обе стороны от четырёх проёмов убежища
    static const float TO[4][2] = {{-1.8f, -4.45f}, {1.8f, -4.45f}, {-1.8f, 5.45f}, {1.8f, 5.45f}};
    for (int q = 0; q < 4; q++) { Deco d = {C0 + TO[q][0], C0 + TO[q][1], 7}; decos.push_back(d); Deco e = {C0 + TO[q][1], C0 + TO[q][0], 7}; decos.push_back(e); }
    boxHp.assign(decos.size(), -1.f);
    for (size_t q = 0; q < decos.size(); q++) if (decos[q].kind == 6) boxHp[q] = BOX_HP;
}
static bool decoBlocks(float x, float y, float r, bool ignoreCrate, bool isZombie) {
    int cx = (int)x, cy = (int)y;
    for (int dy = -1; dy <= 1; dy++)
        for (int dx = -1; dx <= 1; dx++) {
            int nx = cx + dx, ny = cy + dy;
            if (nx < 0 || ny < 0 || nx >= N || ny >= N) continue;
            int di = solidDeco[ny * N + nx];
            if (di < 0 || G[ny * N + nx] != 0) continue;
            const Deco& d = decos[di];
            if (ignoreCrate && (d.kind == 3 || d.kind == 5 || d.kind == 6)) continue;      // в прыжке перескакиваем через бочки и ящик
            if (isZombie && (d.kind == 2 || d.kind == 3 || d.kind == 5 || d.kind == 6)) continue;   // зомби проходят сквозь пни, бочки и ящики
            float ddx = d.x - x, ddy = d.y - y, rr2 = r + DR[d.kind];
            if (ddx * ddx + ddy * ddy < rr2 * rr2) return true;
        }
    return false;
}

// ---------- разрушаемые ящики: HP, попадания, лут ----------
static int hitBox(const Player& pl, float ang, float pitch, float maxT) {      // ближайший целый ящик на линии выстрела (ближе maxT), иначе -1
    float c = cosf(ang), sn = sinf(ang), tp = tanf(pitch), bt = maxT; int best = -1;
    for (size_t i = 0; i < decos.size(); i++) {
        if (decos[i].kind != 6 || boxHp[i] <= 0) continue;
        float rx = decos[i].x - pl.x, ry = decos[i].y - pl.y, t = rx * c + ry * sn;
        if (t > 0 && t < bt && fabsf(-rx * sn + ry * c) < 0.30f) {
            float rz = 0.5f + t * tp;
            if (rz < -0.10f || rz > DHS[6] + 0.15f) continue;      // выше или ниже ящика (с запасом, чтобы попадать прицелом «в центр»)
            best = (int)i; bt = t;
        }
    }
    return best;
}
static void boxFx(int i, bool broken) {
    const Deco& d = decos[i];
    if (broken) { spawnBurst(d.x, d.y, 0.25f, 22, 2.2f, 2); playAt(S_HIT, d.x, d.y, 1.0f, 0.6f); }
    else { spawnBurst(d.x, d.y, 0.3f, 5, 1.2f, 2); playAt(S_HIT, d.x, d.y, 0.5f, 0.9f); }
}
static void boxUnblock(int i) {
    int cell = (int)decos[i].y * N + (int)decos[i].x;
    if (cell >= 0 && cell < N * N && solidDeco[cell] == i) solidDeco[cell] = -1;
}
static void boxLoot(Player& pl) {      // 70% пусто, 25% лом 5-15, 5% случайное оружие + аптечка
    float r = frand();
    if (r < 0.70f) { toast("ЯЩИК ПУСТ", 1.0f, &pl); return; }
    if (r < 0.95f) { int n = irand(5, 15); pl.scrap += n; toast(fmt("+%d ЛОМА", n), 1.2f, &pl); return; }
    int w = irand(0, NW - 1);
    pl.hp = std::min(pl.maxhp, pl.hp + 35);
    if (!pl.unl[w]) { pl.unl[w] = true; pl.ammo[w] = mag_size(pl, w); equipWeapon(pl, w); toast(std::string("НАЙДЕНО: ") + WEAP[w].name + " +35 HP", 2.2f, &pl); }
    else { pl.ammo[w] = mag_size(pl, w); toast(std::string("ПАТРОНЫ: ") + WEAP[w].name + " +35 HP", 2.2f, &pl); }
}
static void damageBox(int i, float d, Player* pl) {
    if (i < 0 || i >= (int)decos.size() || decos[i].kind != 6 || boxHp[i] <= 0) return;
    boxHp[i] -= d;
    bool brk = boxHp[i] <= 0;
    if (brk) boxHp[i] = 0;
    boxFx(i, brk);
    if (brk) { boxUnblock(i); if (pl) boxLoot(*pl); }
}
static void blastBoxes(float x, float y, float r, float dmg, Player* owner) {
    for (size_t i = 0; i < decos.size(); i++)
        if (decos[i].kind == 6 && boxHp[i] > 0 && hypotf(decos[i].x - x, decos[i].y - y) < r) damageBox((int)i, dmg, owner);
}
static std::string boxSnapshot() {     // повреждённые и сломанные ящики: «индекс процент_HP» (для клиентов по сети)
    int n = 0; std::string b;
    for (size_t i = 0; i < decos.size(); i++)
        if (decos[i].kind == 6 && boxHp[i] < BOX_HP) { n++; b += fmt("%d %d ", (int)i, boxHp[i] <= 0 ? 0 : std::max(1, (int)(100 * boxHp[i] / BOX_HP))); }
    return fmt("%d ", n) + b;
}
static void boxSync(int idx, int pct) {
    if (idx < 0 || idx >= (int)decos.size() || decos[idx].kind != 6) return;
    float nh = pct <= 0 ? 0.f : BOX_HP * pct / 100.f;
    if (nh >= boxHp[idx]) return;
    boxHp[idx] = nh;
    boxFx(idx, nh <= 0);
    if (nh <= 0) boxUnblock(idx);
}

// ---------- SDL-текстуры ----------
struct VSprite { std::vector<u32> pxl[3]; int w = 0, h = 0; float ax = 0, ay = 0, mx = 0, my = 0, ex = 0, ey = 0, wx = 0, wy = 0, mvx = 0, mvy = 0; SDL_Texture* texl[3] = {NULL, NULL, NULL}; bool ready = false; };
static VSprite VSPR[NW];
static SDL_Texture *ZTEX[6][2], *PTEX[4][2], *CTEX[3], *DTEX[8], *TORCHGLOW = NULL, *BLOODTEX = NULL, *MISTTEX = NULL, *LIGHTTEX = NULL;
static SDL_Texture *WALLTEX[4], *CRACKTEX = NULL, *SKYTEX = NULL, *FLOORTEX = NULL, *VIGTEX = NULL, *VIGRED = NULL, *SHADOWTEX = NULL;
static std::vector<u32> floorBuf;
static int FLW = 200, FLH = 100; static float FLPX = 5.f;
static float HZ = 270.f;
static float EYE_H = 0.5f;   // высота глаз игрока: 0.5 обычно, растёт в прыжке — используется и полом, и стенами, и спрайтами
static const int FOGR = 34, FOGG = 26, FOGB = 58;   // цвет дымки = цвет неба у горизонта
static float FLASH_L[1024], FOGA[1024]; static int FOGY0[1024], FOGY1[1024], FOGX[1025];
static const int SKYW = 2048, SKYH = 160;

static SDL_Texture* makeTexSmooth(const std::vector<u32>& px, int w, int h) {
    SDL_SetHint(SDL_HINT_RENDER_SCALE_QUALITY, "1");
    SDL_Texture* t = makeTex(px, w, h);
    SDL_SetHint(SDL_HINT_RENDER_SCALE_QUALITY, "0");
    return t;
}
static void postFx(Canvas& c) {           // контур + свет слева + лёгкий шум
    std::vector<u32> src = c.px;
    auto clear_at = [&](int x, int y) { return x < 0 || y < 0 || x >= c.w || y >= c.h || (src[(size_t)y * c.w + x] >> 24) == 0; };
    for (int y = 0; y < c.h; y++)
        for (int x = 0; x < c.w; x++) {
            u32 p = src[(size_t)y * c.w + x];
            if ((p >> 24) == 0) continue;
            bool edge = false;
            for (int d = 1; d <= c.sc && !edge; d++) edge = clear_at(x - d, y) || clear_at(x + d, y) || clear_at(x, y - d) || clear_at(x, y + d);
            float k = 1.14f - 0.32f * x / (float)c.w - 0.08f * y / (float)c.h + (hnoise(x, y, 5) - 0.5f) * 0.09f;
            if (edge) k *= 0.42f;
            c.px[(size_t)y * c.w + x] = PX(C((int)(((p >> 16) & 255) * k), (int)(((p >> 8) & 255) * k), (int)((p & 255) * k)));
        }
}
// ---------- декорации: крупные текстуры 128x128 с честным освещением ----------
static void decoOutline(Canvas& c, int th, float k) {
    std::vector<u32> src = c.px;
    auto clear_at = [&](int x, int y) { return x < 0 || y < 0 || x >= c.w || y >= c.h || (src[(size_t)y * c.w + x] >> 24) == 0; };
    for (int y = 0; y < c.h; y++)
        for (int x = 0; x < c.w; x++) {
            u32 p = src[(size_t)y * c.w + x];
            if ((p >> 24) == 0) continue;
            bool lit = clear_at(x - 1, y) || clear_at(x, y - 1);      // грань к свету (верх-лево) — мягкий блик
            bool sh = false;
            for (int d = 1; d <= th && !lit && !sh; d++) sh = clear_at(x - d, y) || clear_at(x + d, y) || clear_at(x, y - d) || clear_at(x, y + d);
            float rr = (float)((p >> 16) & 255), gg = (float)((p >> 8) & 255), bb = (float)(p & 255);
            if (lit) { rr = rr * 0.72f + 62.f; gg = gg * 0.72f + 62.f; bb = bb * 0.72f + 66.f; }        // блик по освещённой кромке — объём
            else if (sh) { rr *= k; gg *= k; bb *= k; }                                                 // тень по остальному контуру
            else continue;
            c.px[(size_t)y * c.w + x] = PX(C((int)std::min(255.f, rr), (int)std::min(255.f, gg), (int)std::min(255.f, bb)));
        }
}
static inline void decoPut(Canvas& c, int x, int y, float r, float g, float b) {
    if (x >= 0 && y >= 0 && x < c.w && y < c.h) c.px[(size_t)y * c.w + x] = PX(C((int)std::max(0.f, std::min(255.f, r)), (int)std::max(0.f, std::min(255.f, g)), (int)std::max(0.f, std::min(255.f, b))));
}
static void drawBarrel(Canvas& c, Col base, int seed) {
    const int cx = 64, rx = 40, topY = 34, ry = 13, botY = 108;
    for (int y = 14; y < 128; y++)
        for (int x = 16; x < 112; x++) {
            float u = (x - cx) / (float)rx;
            if (fabsf(u) > 1.f) continue;
            float sq = sqrtf(std::max(0.f, 1.f - u * u)), topEdge = topY - ry * sq, rim = topY + ry * sq, botEdge = botY + ry * sq;
            if (y < topEdge || y > botEdge) continue;
            float r, g, b;
            if (y < rim) {                                           // крышка
                float dy = (y - topY) / (float)ry, d = sqrtf(u * u + dy * dy), lit = 0.8f + 0.2f * (-u * 0.5f - dy * 0.4f), ring = 0.5f + 0.5f * sinf(d * 24.f);
                r = base.r * 0.5f * lit * (0.88f + 0.2f * ring) + 32; g = base.g * 0.5f * lit * (0.88f + 0.2f * ring) + 32; b = base.b * 0.5f * lit * (0.88f + 0.2f * ring) + 34;
                if (d > 0.86f) { r = base.r * 0.85f + 40; g = base.g * 0.85f + 40; b = base.b * 0.85f + 40; }      // обод
                float d1 = hypotf(x - 48.f, (y - 36.f) * 1.6f), d2 = hypotf(x - 80.f, (y - 33.f) * 1.6f);
                if (d1 < 6.f) { float t = 150.f - d1 * 7; r = g = b = t; }
                if (d2 < 4.5f) { float t = 118.f - d2 * 6; r = g = b = t; }
            } else {                                                 // корпус
                float lit = std::max(0.f, -0.6f * u + 0.8f * sq), k = 0.40f + 0.80f * lit;
                r = base.r * k; g = base.g * k; b = base.b * k;
                for (int q = 0; q < 2; q++) {                        // рёбра жёсткости
                    float dyr = y - (topY + (q ? 62 : 28) + ry * sq);
                    if (fabsf(dyr) < 5.f) { float t = 1.f - 0.5f * (dyr / 5.f) * 0.7f; r *= t; g *= t; b *= t; if (fabsf(dyr) < 1.3f) { r *= 0.62f; g *= 0.62f; b *= 0.62f; } if (dyr > -4.f && dyr < -2.5f) { r += 24; g += 24; b += 24; } }
                }
                float rust = vnoiseP(x / 10.f, y / 10.f, seed, 16) * 0.6f + vnoiseP(x / 4.f, y / 4.f, seed + 1, 32) * 0.4f + (y - topY) / 260.f;
                if (rust > 0.64f) { float t = std::min(1.f, (rust - 0.64f) * 4.f); r = r * (1 - t) + 118 * k * t; g = g * (1 - t) + 62 * k * t; b = b * (1 - t) + 30 * k * t; }
                if (hnoise(x / 2, y / 5, seed + 2) > 0.988f) { r += 34; g += 34; b += 34; }                       // царапины
                float dyl = y - (topY + ry * sq);
                if (fabsf(u) < 0.40f && dyl > 14 && dyl < 46) {      // предупреждающий знак
                    float lk = 0.55f + 0.6f * lit;
                    bool border = fabsf(u) > 0.37f || dyl < 16 || dyl > 44;
                    if (border) { r = 20; g = 20; b = 22; }
                    else { r = 238 * lk; g = 196 * lk; b = 40 * lk; if (fabsf(u) < 0.17f && dyl > 22 && dyl < 38) { r = 22; g = 22; b = 26; } }
                }
                if (y > botEdge - 9) { float t = 0.7f + 0.3f * (botEdge - y) / 9.f; r *= t; g *= t; b *= t; }         // тень у низа
            }
            decoPut(c, x, y, r, g, b);
        }
    decoOutline(c, 2, 0.5f);
}
static void drawStump(Canvas& c) {
    const int cx = 64, topY = 46, ry = 13, botY = 110;
    for (int y = 24; y < 128; y++)
        for (int x = 12; x < 116; x++) {
            float flare = 10.f * std::max(0.f, std::min(1.f, (y - 92) / 18.f)), rx = 32.f + flare, u = (x - cx) / rx;
            if (fabsf(u) > 1.f) continue;
            float sq = sqrtf(std::max(0.f, 1.f - u * u)), topEdge = topY - ry * sq, rim = topY + ry * sq, botEdge = botY + ry * sq * 0.6f;
            if (y < topEdge || y > botEdge) continue;
            float r, g, b;
            if (y < rim) {                                           // спил: годовые кольца
                float dy = (y - topY) / (float)ry, ux = (x - cx) / 32.f, d = sqrtf(ux * ux + dy * dy);
                float ring = 0.5f + 0.5f * sinf(d * 38.f + vnoiseP(x / 8.f, y / 8.f, 61, 16) * 3.f);
                r = 176 * (0.80f + 0.22f * ring); g = 128 * (0.80f + 0.22f * ring); b = 76 * (0.80f + 0.22f * ring);
                if (d > 0.9f) { r = 104; g = 70; b = 40; }
                if (d < 0.08f) { r *= 0.7f; g *= 0.7f; b *= 0.7f; }
            } else {                                                 // кора
                float lit = std::max(0.f, -0.6f * u + 0.8f * sq), k = 0.38f + 0.85f * lit;
                float gr = vnoiseP(x / 3.f, y / 24.f, 62, 32), br = vnoiseP(x / 2.f, y / 6.f, 63, 64);
                float t = k * (0.65f + 0.5f * gr) * (0.9f + 0.2f * br);
                r = 108 * t; g = 72 * t; b = 42 * t;
                if (vnoiseP(x / 10.f, y / 10.f, 64, 16) > 0.7f && y > topY + 16) { r = 52 * k; g = 96 * k; b = 44 * k; }   // мох
            }
            decoPut(c, x, y, r, g, b);
        }
    decoOutline(c, 2, 0.5f);
}
static void drawRocks(Canvas& c) {
    struct Blob { float cx, cy, rx, ry; };
    static const Blob bl[3] = {{40, 94, 30, 20}, {82, 90, 32, 24}, {60, 70, 26, 22}};
    const float Lx = -0.5f, Ly = -0.6f, Lz = 0.62f;
    for (int i = 0; i < 3; i++)
        for (int y = 0; y < 128; y++)
            for (int x = 0; x < 128; x++) {
                float dx = (x - bl[i].cx) / bl[i].rx, dy = (y - bl[i].cy) / bl[i].ry, d2 = dx * dx + dy * dy;
                if (d2 > 1.f) continue;
                float nz = sqrtf(1.f - d2), nx = dx * 0.9f, ny = dy * 0.9f, nl = sqrtf(nx * nx + ny * ny + nz * nz);
                float lit = std::max(0.f, (nx * Lx + ny * Ly + nz * Lz) / nl), f = vnoiseP(x / 6.f, y / 6.f, 51 + i, 32), gn = hnoise(x, y, 55);
                float k = (0.42f + 0.85f * lit) * (0.86f + 0.26f * f);
                float base = 118 + i * 8 + (gn - 0.5f) * 20;
                float r = base * k, g = base * k, b = (base + 8) * k;
                if (dy < -0.25f && vnoiseP(x / 8.f, y / 8.f, 56 + i, 16) > 0.55f) { r = 54 * k + 10; g = 108 * k + 10; b = 46 * k; }       // мох сверху
                if (hnoise(x / 3, y / 3, 57 + i) > 0.985f) { r *= 0.5f; g *= 0.5f; b *= 0.5f; }
                decoPut(c, x, y, r, g, b);
            }
    decoOutline(c, 2, 0.55f);
}
static void drawCrate(Canvas& c) {
    for (int y = 34; y < 124; y++)
        for (int x = 18; x < 110; x++) {
            bool front = x >= 22 && x < 106 && y >= 62 && y < 120;
            float tl = 22 + (62 - y) * 0.30f, tr = 106 - (62 - y) * 0.30f;            // верхняя грань: трапеция
            bool top = y >= 38 && y < 62 && x >= tl && x < tr;
            if (!front && !top) continue;
            float r, g, b;
            float grain = vnoiseP(x / 20.f, y * 0.7f, 71, 8), nz = (hnoise(x, y, 72) - 0.5f) * 14;
            if (top) {
                float pl = ((y - 38) % 8);
                float k = 1.05f + 0.25f * grain; r = 178 * k + nz; g = 130 * k + nz * 0.7f; b = 76 * k;
                if (pl < 1.5f) { r *= 0.55f; g *= 0.55f; b *= 0.55f; }
            } else {
                int pl = (y - 62) % 14;
                float k = 0.78f + 0.3f * grain; r = 148 * k + nz; g = 104 * k + nz * 0.7f; b = 58 * k;
                if (pl < 2) { r *= 0.5f; g *= 0.5f; b *= 0.5f; } else if (pl == 2) { r += 22; g += 18; b += 10; }
                bool brace = x < 36 || x >= 92 || (fabsf((x - 36) * 0.9f - (y - 70) * 1.0f) < 4.2f && x >= 36 && x < 92 && y >= 66);
                if (brace) { r *= 0.72f; g *= 0.72f; b *= 0.72f; if (x < 24 || x > 104 || fabsf((x - 36) * 0.9f - (y - 70)) < 1.2f) { r *= 0.7f; g *= 0.7f; b *= 0.7f; } }
                for (int nxp : {28, 100}) for (int nyp : {70, 92, 112}) { float dd = hypotf((float)(x - nxp), (float)(y - nyp)); if (dd < 3.2f) { r = g = b = 150.f - dd * 20; } }
                if (y > 112) { float t = 0.7f + 0.3f * (120.f - y) / 8.f; r *= t; g *= t; b *= t; }
            }
            decoPut(c, x, y, r, g, b);
        }
    decoOutline(c, 2, 0.5f);
}
static const int NDECO = 8;
static void drawDecoArt(Canvas& c, int k) {   // c: 128x128, sc=4 (логические координаты 32x32 для простых предметов)
    if (k == 0) {          // пучок травы
        for (int i = 0; i < 26; i++) {
            int bx = 4 + (i * 5) % 24, h_ = 8 + (i * 7) % 15, lean = ((i * 3) % 7) - 3;
            Col gc = C(30 + (i * 13) % 30, 62 + (i * 29) % 46, 24 + (i * 11) % 22);
            c.line(bx, 30, bx + lean / 2, 30 - h_ / 2, 1, gc); c.line(bx + lean / 2, 30 - h_ / 2, bx + lean, 30 - h_, 1, shade(gc, 1.18f));
        }
        c.circle(23, 12, 1, C(200, 200, 190));
        decoOutline(c, 1, 0.6f);
    } else if (k == 1) drawRocks(c);
    else if (k == 2) drawStump(c);
    else if (k == 3) drawBarrel(c, C(72, 118, 78), 81);
    else if (k == 4) {     // кости
        c.circle(12, 24, 5, C(226, 222, 204)); c.rect(10, 28, 5, 3, C(226, 222, 204)); c.rect(9, 23, 2, 2, C(30, 26, 26)); c.rect(13, 23, 2, 2, C(30, 26, 26));
        c.line(18, 28, 30, 22, 2, C(220, 216, 198)); c.line(18, 22, 30, 29, 2, C(220, 216, 198)); c.circle(31, 22, 1, C(220, 216, 198)); c.circle(31, 29, 1, C(220, 216, 198));
        decoOutline(c, 2, 0.5f);
    } else if (k == 5) drawBarrel(c, C(170, 62, 48), 91);
    else if (k == 7) {     // стойка факела
        c.rect(14, 12, 4, 20, C(96, 64, 38)); c.rect(14, 12, 1, 20, C(128, 88, 52)); c.rect(17, 12, 1, 20, C(66, 42, 24));
        c.rect(10, 9, 12, 3, C(56, 58, 66)); c.rect(9, 6, 14, 3, C(72, 74, 84)); c.rect(11, 5, 10, 1, C(30, 30, 34));
        c.rect(12, 28, 8, 2, C(70, 46, 28));
        decoOutline(c, 2, 0.5f);
    }
    else drawCrate(c);
}

// ---------- трава: пучки из отдельных изогнутых травинок с тенью у основания (для «Средней» и «Высокой») ----------
static SDL_Texture* GRASSTEX[3] = {NULL, NULL, NULL};
static void gpx(std::vector<u32>& px, int S, int x, int y, float r, float g, float b, float a) {      // положить полупрозрачную точку «поверх»
    if (x < 0 || y < 0 || x >= S || y >= S || a <= 0.f) return;
    u32 d = px[(size_t)y * S + x]; float da = ((d >> 24) & 255) / 255.f, oa = a + da * (1.f - a);
    float dr = (d >> 16) & 255, dg = (d >> 8) & 255, db = d & 255;
    float rr_ = oa > 0 ? (r * a + dr * da * (1.f - a)) / oa : 0, gg_ = oa > 0 ? (g * a + dg * da * (1.f - a)) / oa : 0, bb_ = oa > 0 ? (b * a + db * da * (1.f - a)) / oa : 0;
    px[(size_t)y * S + x] = PX(C((int)rr_, (int)gg_, (int)bb_, (int)(oa * 255.f)));
}
static void drawGrassTuft(std::vector<u32>& px, int S, int variant) {
    px.assign((size_t)S * S, 0);
    int nb = 46 + variant * 6; const float baseY = S * 0.95f;
    for (int b = 0; b < nb; b++) {
        u32 h = hashu(b, variant, 411);
        float fr = (h & 1023) / 1023.f, fr2 = ((h >> 10) & 1023) / 1023.f, fr3 = ((h >> 20) & 1023) / 1023.f;
        float spread = 0.5f - 0.5f * fabsf(fr - 0.5f) * 2.f;                                    // в середине пучка травинки выше
        float bx = S * (0.16f + 0.68f * fr), tall = S * (0.30f + 0.62f * (0.35f + spread) * (0.55f + 0.45f * fr2));
        float lean = (fr3 - 0.5f) * S * 0.42f + (fr - 0.5f) * S * 0.22f;                        // веером в стороны
        float curve = (fr2 - 0.5f) * S * 0.20f;
        bool dry = ((h >> 5) % 100) < 12;
        float w0 = S * (0.030f + 0.018f * fr2);
        int steps = (int)(tall * 1.4f);
        for (int st = 0; st <= steps; st++) {
            float t = st / (float)steps, omt = 1.f - t;
            float cx = bx + lean * t + curve * t * (1.f - t) * 2.f, cy = baseY - tall * t;      // изогнутая линия травинки
            float w = w0 * (1.f - 0.92f * t * t);                                                 // сужается к кончику
            float sh = 0.55f + 0.55f * t;                                                         // у основания темнее, к кончику светлее
            float r, g, bl;
            if (dry) { r = 96 + 50 * t; g = 88 + 44 * t; bl = 40 + 20 * t; }
            else { r = 20 + 68 * t * (0.6f + fr2 * 0.6f); g = (46 + 84 * t) * (0.82f + 0.36f * fr3); bl = 18 + 28 * t; }
            r *= sh; g *= sh; bl *= sh;
            int xr = (int)ceilf(w) + 1;
            for (int dx = -xr; dx <= xr; dx++) {
                float dd = fabsf(dx + (cx - floorf(cx)) * -1.f + 0.f);
                float cov = std::max(0.f, std::min(1.f, w * 0.5f + 0.75f - fabsf(dx - (cx - floorf(cx)) + 0.5f)));
                float lit = dx < 0 ? 1.12f : 0.86f;                                                // левая сторона светлее — свет слева
                gpx(px, S, (int)floorf(cx) + dx, (int)cy, r * lit, g * lit, bl * lit, cov);
                (void)dd; (void)omt;
            }
        }
        if (fr2 > 0.86f && !dry) {                                                                  // редкие колоски
            float tx = bx + lean, ty = baseY - tall;
            for (int e = 0; e < 9; e++) { float a = e / 9.f; gpx(px, S, (int)(tx + curve * 0.0f), (int)(ty - e * S * 0.012f), 150 + 30 * a, 132 + 20 * a, 70, 0.9f); gpx(px, S, (int)tx + 1, (int)(ty - e * S * 0.012f), 120, 104, 52, 0.7f); }
        }
    }
    if (variant == 2) {                                                                              // в одном из пучков — мелкие цветочки
        for (int f = 0; f < 5; f++) { u32 h = hashu(f, 9, 412); int fx = (int)(S * (0.22f + 0.56f * ((h & 255) / 255.f))), fy = (int)(S * (0.18f + 0.30f * (((h >> 8) & 255) / 255.f)));
            Col fc = (f & 1) ? C(250, 240, 200) : C(250, 210, 80); for (int dy = -2; dy <= 2; dy++) for (int dx = -2; dx <= 2; dx++) if (dx * dx + dy * dy <= 4) gpx(px, S, fx + dx, fy + dy, fc.r, fc.g, fc.b, 0.95f); gpx(px, S, fx, fy, 200, 130, 40, 1.f); }
    }
    for (int y = 0; y < S; y++) {                                                                    // тень у земли (густая часть пучка внизу темнее)
        float k = y > S * 0.72f ? 1.f - 0.38f * (y - S * 0.72f) / (S * 0.28f) : 1.f;
        for (int x = 0; x < S; x++) { u32 d = px[(size_t)y * S + x]; if (!(d >> 24)) continue; px[(size_t)y * S + x] = PX(C((int)(((d >> 16) & 255) * k), (int)(((d >> 8) & 255) * k), (int)((d & 255) * k), (int)(d >> 24))); }
    }
}
static void makeGrassTex() {
    for (int v = 0; v < 3; v++) {
        std::vector<u32> px; drawGrassTuft(px, 128, v);
        if (GRASSTEX[v]) SDL_DestroyTexture(GRASSTEX[v]);
        GRASSTEX[v] = makeTexSmooth(px, 128, 128);
    }
}

static void initVModels();
static void makeSprites() {
    initVModels();
    genTextures();
    for (int k = 0; k < NZK; k++)
        for (int f = 0; f < 2; f++) {
            if (ZTEX[k][f]) SDL_DestroyTexture(ZTEX[k][f]);
            Canvas c(80, 128, 2); const ZKind& z = ZK[k];
            int le = f ? 0 : -3, re = f ? -3 : 0;
            c.rect(11, 40, 8, 20 + le, z.pants); c.rect(21, 40, 8, 20 + re, z.pants);
            c.rect(10, 58 + le, 10, 6, C(25, 22, 22)); c.rect(20, 58 + re, 10, 6, C(25, 22, 22));
            int th_ = k == 5 ? 8 : (k == 2 ? 6 : 5);
            c.line(10, 23, f ? 3 : 6, f ? 42 : 38, th_, z.skin); c.line(30, 23, f ? 37 : 34, f ? 38 : 44, th_, z.skin);
            if (k == 5) { c.rect(4, 18, 32, 8, z.shirt); c.rect(7, 20, 26, 22, z.shirt); c.rect(2, 14, 4, 6, C(200, 190, 160)); c.rect(34, 14, 4, 6, C(200, 190, 160)); }   // широкие плечи, шипы
            else c.rect(9, 20, 22, 22, z.shirt);
            c.rect(9, 38, 5, 4, C(0, 0, 0, 0)); c.rect(17, 40, 4, 2, C(0, 0, 0, 0)); c.rect(26, 39, 5, 3, C(0, 0, 0, 0));   // рваный подол
            c.rect(13, 36, 5, 5, z.skin);
            c.rect(21, 26, 6, 4, C(120, 20, 20)); c.rect(12, 30, 3, 6, C(120, 20, 20)); c.rect(24, 33, 3, 3, C(100, 16, 16));
            c.circle(20, 12, 10, z.skin);
            c.rect(11, 3, 18, 4, C(40, 30, 26)); c.rect(10, 5, 3, 5, C(40, 30, 26));   // волосы
            if (k == 5) { c.rect(9, 0, 3, 8, C(210, 200, 170)); c.rect(28, 0, 3, 8, C(210, 200, 170)); }   // рога
            postFx(c);
            c.circle(16, 11, 2, C(255, 60, 40)); c.circle(24, 11, 2, C(255, 60, 40)); c.rect(16, 11, 1, 1, C(255, 230, 120)); c.rect(24, 11, 1, 1, C(255, 230, 120));
            c.rect(15, 17, 10, 3, C(60, 8, 8)); c.rect(16, 17, 2, 2, C(220, 210, 190)); c.rect(21, 17, 2, 2, C(220, 210, 190));
            if (k == 3) { c.circle(20, 27, 6, C(150, 255, 60)); c.circle(20, 27, 3, C(225, 255, 150)); c.rect(14, 17, 12, 5, C(140, 255, 60)); c.rect(16, 18, 8, 2, C(230, 255, 170)); }   // кислотный мешок и пасть
            if (k == 4) { c.rect(13, 27, 4, 12, C(205, 40, 40)); c.rect(18, 27, 4, 12, C(215, 52, 46)); c.rect(23, 27, 4, 12, C(190, 36, 36)); c.rect(12, 31, 16, 2, C(30, 30, 30)); c.line(20, 27, 22, 22, 1, C(40, 40, 40)); c.circle(22, 21, 2, C(255, 200, 40)); c.circle(22, 21, 1, C(255, 255, 210)); }   // динамит с горящим фитилём
            if (k == 5) { c.circle(16, 11, 3, C(255, 210, 40)); c.circle(24, 11, 3, C(255, 210, 40)); }
            ZTEX[k][f] = makeTexSmooth(c.px, 80, 128);
        }
    for (int k = 0; k < 4; k++)
        for (int f = 0; f < 2; f++) {
            if (PTEX[k][f]) SDL_DestroyTexture(PTEX[k][f]);
            Canvas c(80, 128, 2); Col col = PCOL[k], dark = shade(col, 0.55f);
            int le = f ? 0 : -3, re = f ? -3 : 0;
            c.rect(11, 40, 8, 20 + le, C(45, 50, 60)); c.rect(21, 40, 8, 20 + re, C(45, 50, 60));
            c.rect(10, 58 + le, 10, 6, C(20, 20, 22)); c.rect(20, 58 + re, 10, 6, C(20, 20, 22));
            c.rect(9, 20, 22, 22, col); c.rect(9, 36, 22, 3, dark); c.rect(11, 22, 18, 3, shade(col, 1.2f));
            c.line(10, 23, 15, 37, 5, dark); c.line(30, 23, 25, 37, 5, dark);
            c.rect(17, 28, 6, 15, C(30, 30, 34));
            c.circle(20, 12, 9, C(215, 170, 135)); c.circle(20, 9, 10, C(70, 82, 60));
            c.rect(14, 11, 12, 8, C(215, 170, 135));
            postFx(c);
            c.rect(16, 12, 3, 2, C(30, 30, 30)); c.rect(22, 12, 3, 2, C(30, 30, 30));
            PTEX[k][f] = makeTexSmooth(c.px, 80, 128);
        }
    for (int k = 0; k < 3; k++) {
        if (CTEX[k]) SDL_DestroyTexture(CTEX[k]);
        Canvas c(64, 64, 2);
        if (k == 0) {
            c.rect(2, 6, 28, 24, C(110, 110, 120)); c.rect(2, 6, 28, 3, C(170, 170, 180)); c.rect(2, 27, 28, 3, C(170, 170, 180));
            c.rect(2, 6, 3, 24, C(170, 170, 180)); c.rect(27, 6, 3, 24, C(170, 170, 180));
            c.line(2, 6, 30, 30, 2, C(170, 170, 180)); c.line(30, 6, 2, 30, 2, C(170, 170, 180));
        } else if (k == 1) {
            c.rect(2, 6, 28, 24, C(235, 235, 235)); c.rect(13, 10, 6, 16, C(215, 30, 30)); c.rect(8, 15, 16, 6, C(215, 30, 30));
        } else { c.circle(16, 16, 13, C(60, 120, 255)); c.circle(16, 16, 7, C(180, 220, 255)); c.circle(13, 12, 2, C(255, 255, 255)); }
        postFx(c);
        CTEX[k] = makeTexSmooth(c.px, 64, 64);
    }
    {   // ореол факела
        std::vector<u32> tg(64 * 64);
        for (int y = 0; y < 64; y++)
            for (int x = 0; x < 64; x++) {
                float nx = (x - 31.5f) / 31.5f, ny = (y - 31.5f) / 31.5f, r = sqrtf(nx * nx + ny * ny), t = std::max(0.f, 1.f - r);
                tg[y * 64 + x] = PX(C(255, 150, 60, (int)(220 * t * t * t)));
            }
        if (TORCHGLOW) SDL_DestroyTexture(TORCHGLOW);
        TORCHGLOW = makeTexSmooth(tg, 64, 64);
        if (TORCHGLOW) SDL_SetTextureBlendMode(TORCHGLOW, SDL_BLENDMODE_ADD);
    }
    {   // тёплое световое пятно от фонаря (складывается с картинкой)
        std::vector<u32> lt(128 * 128);
        for (int y = 0; y < 128; y++)
            for (int x = 0; x < 128; x++) {
                float nx = (x - 63.5f) / 63.5f, ny = (y - 63.5f) / 63.5f, r = sqrtf(nx * nx + ny * ny), t = std::max(0.f, 1.f - r);
                lt[y * 128 + x] = PX(C(255, 232, 190, (int)(64 * t * t)));
            }
        if (LIGHTTEX) SDL_DestroyTexture(LIGHTTEX);
        LIGHTTEX = makeTexSmooth(lt, 128, 128);
        if (LIGHTTEX) SDL_SetTextureBlendMode(LIGHTTEX, SDL_BLENDMODE_ADD);
    }
    // лужа крови (плоская) и полосы приземного тумана
    {
        std::vector<u32> bl(64 * 32);
        for (int y = 0; y < 32; y++)
            for (int x = 0; x < 64; x++) {
                float nx = (x - 31.5f) / 31.5f, ny = (y - 15.5f) / 15.5f, r2 = nx * nx + ny * ny;
                float n = vnoiseP(x / 8.f, y / 8.f, 81, 8), edge = 0.75f + 0.45f * n;
                float a = r2 < edge ? std::min(1.f, (edge - r2) * 3.f) : 0.f;
                float dk = vnoiseP(x / 4.f, y / 4.f, 82, 16);
                bl[y * 64 + x] = PX(C((int)(96 + 40 * dk), (int)(8 + 8 * dk), (int)(8 + 6 * dk), (int)(a * 225)));
            }
        if (BLOODTEX) SDL_DestroyTexture(BLOODTEX);
        BLOODTEX = makeTexSmooth(bl, 64, 32);
        std::vector<u32> ms(512 * 64);
        for (int y = 0; y < 64; y++)
            for (int x = 0; x < 512; x++) {
                float n = vnoiseP(x / 64.f, y / 10.f, 83, 8) * 0.65f + vnoiseP(x / 16.f, y / 6.f, 84, 32) * 0.35f;
                float env = sinf(y / 63.f * 3.14159f); env *= env;
                float a = std::max(0.f, std::min(1.f, (n - 0.38f) * 2.4f)) * env;
                ms[y * 512 + x] = PX(C(128, 138, 178, (int)(a * 120)));
            }
        if (MISTTEX) SDL_DestroyTexture(MISTTEX);
        MISTTEX = makeTexSmooth(ms, 512, 64);
    }
    // декорации мира
    for (int k = 0; k < NDECO; k++) {
        if (DTEX[k]) SDL_DestroyTexture(DTEX[k]);
        Canvas c(128, 128, 4);
        drawDecoArt(c, k);
        DTEX[k] = makeTexSmooth(c.px, 128, 128);
    }
    // стены
    for (int t = 1; t <= 3; t++) {
        if (WALLTEX[t]) SDL_DestroyTexture(WALLTEX[t]);
        const u32* src = t == 1 ? T_STONE : (t == 2 ? T_PLANK : T_HEDGE);
        WALLTEX[t] = makeTexSmooth(std::vector<u32>(src, src + TS * TS), TS, TS);
        if (WALLTEX[t]) SDL_SetTextureBlendMode(WALLTEX[t], SDL_BLENDMODE_NONE);
    }
    if (quality > 0) makeHiWallTex(true);   // крупные стены — только на «Средней/Высокой»
    makeGrassTex();
    for (int i = 0; i < NW; i++)     // текстуры оружия пересоздаём из сохранённых пикселей (после сброса устройства)
        if (VSPR[i].ready)
            for (int l = 0; l < 3; l++) { if (VSPR[i].texl[l]) SDL_DestroyTexture(VSPR[i].texl[l]); VSPR[i].texl[l] = makeTexSmooth(VSPR[i].pxl[l], VSPR[i].w, VSPR[i].h); }
    if (CRACKTEX) SDL_DestroyTexture(CRACKTEX);
    CRACKTEX = makeTexSmooth(std::vector<u32>(T_CRACK, T_CRACK + TS * TS), TS, TS);
    // небо: градиент, звёзды, луна, облака
    {
        std::vector<u32> px((size_t)SKYW * SKYH);
        for (int y = 0; y < SKYH; y++) {
            float t = y / (float)(SKYH - 1);
            float r = 5 + 29 * powf(t, 1.7f), g = 7 + 19 * powf(t, 1.5f), b = 22 + 36 * powf(t, 1.2f);
            for (int x = 0; x < SKYW; x++) {
                float cl = vnoiseP(x / 64.f, y / 24.f, 51, 32);
                float cv = cl > 0.58f ? (cl - 0.58f) * 45 * (0.4f + t) : 0;
                px[(size_t)y * SKYW + x] = PX(C((int)(r + cv), (int)(g + cv * 0.9f), (int)(b + cv * 1.2f)));
            }
        }
        for (int i = 0; i < 620; i++) {
            int x = hashu(i, 1, 61) % SKYW, y = hashu(i, 2, 61) % (SKYH - 24), br = 130 + hashu(i, 3, 61) % 125;
            px[(size_t)y * SKYW + x] = PX(C(br, br, std::min(255, br + 20)));
            if (br > 190) { px[(size_t)y * SKYW + (x + 1) % SKYW] = PX(C(br - 40, br - 40, br - 20)); px[(size_t)std::min(SKYH - 1, y + 1) * SKYW + x] = PX(C(br - 40, br - 40, br - 20)); px[(size_t)std::min(SKYH - 1, y + 1) * SKYW + (x + 1) % SKYW] = PX(C(br - 60, br - 60, br - 40)); }
            if (br > 220) { px[(size_t)y * SKYW + (x + 1) % SKYW] = PX(C(br - 80, br - 80, br - 60)); px[(size_t)std::min(SKYH - 1, y + 1) * SKYW + x] = PX(C(br - 80, br - 80, br - 60)); }
        }
        if (SKYTEX) SDL_DestroyTexture(SKYTEX);
        SKYTEX = makeTexSmooth(px, SKYW, SKYH);
        if (SKYTEX) SDL_SetTextureBlendMode(SKYTEX, SDL_BLENDMODE_NONE);
    }
    // виньетка (тёмная и красная), тень
    {
        std::vector<u32> a(128 * 72), b(128 * 72);
        for (int y = 0; y < 72; y++)
            for (int x = 0; x < 128; x++) {
                float nx = (x / 127.f - 0.5f) * 2, ny = (y / 71.f - 0.5f) * 2, r = sqrtf(nx * nx * 0.75f + ny * ny * 0.95f);
                float t = std::max(0.f, std::min(1.f, (r - 0.5f) / 0.8f)); t = t * t;
                a[y * 128 + x] = PX(C(0, 0, 8, (int)(205 * t)));
                b[y * 128 + x] = PX(C(255, 20, 20, (int)(230 * t)));
            }
        if (VIGTEX) SDL_DestroyTexture(VIGTEX);
        if (VIGRED) SDL_DestroyTexture(VIGRED);
        VIGTEX = makeTexSmooth(a, 128, 72); VIGRED = makeTexSmooth(b, 128, 72);
        std::vector<u32> sh(32 * 16);
        for (int y = 0; y < 16; y++)
            for (int x = 0; x < 32; x++) {
                float nx = (x - 15.5f) / 15.5f, ny = (y - 7.5f) / 7.5f, r2 = nx * nx + ny * ny;
                sh[y * 32 + x] = PX(C(0, 0, 0, r2 < 1 ? (int)(170 * (1 - r2)) : 0));
            }
        if (SHADOWTEX) SDL_DestroyTexture(SHADOWTEX);
        SHADOWTEX = makeTexSmooth(sh, 32, 16);
    }
}

// ============================ РЕНДЕР 3D ============================
static const float MOON_ANG = 1.05f;
static void renderSky() {
    if (!SKYTEX || HZ < 4.f) return;
    float hs = HZ + 2.f, tileW = SKYW * hs / SKYH;             // квадратные пиксели: звёзды круглые
    float off = fmodf(P->ang * FOCAL, tileW); if (off < 0) off += tileW;
    for (float x = -off; x < W; x += tileW) { SDL_Rect a = {(int)floorf(x), 0, (int)ceilf(tileW) + 1, (int)hs}; SDL_RenderCopy(ren, SKYTEX, NULL, &a); }
    float da = MOON_ANG - P->ang; while (da > 3.14159f) da -= 6.28318f; while (da < -3.14159f) da += 6.28318f;
    float mx = W / 2.f + da * FOCAL, my = HZ * 0.30f, mr = std::max(6.f, U * 3.2f);
    if (mx > -mr * 5 && mx < W + mr * 5) {
        float bm = bloodMoon * 0.9f;
        auto T = [&](int r, int g, int b, int a) { return C((int)(r + (250 - r) * bm), (int)(g + (70 - g) * bm), (int)(b + (55 - b) * bm), a); };
        fillCircle(mx, my, mr * 4.2f, T(190, 200, 255, 10)); fillCircle(mx, my, mr * 3.0f, T(200, 210, 255, 16)); fillCircle(mx, my, mr * 2.0f, T(215, 225, 255, 30));
        fillCircle(mx, my, mr, T(238, 238, 218, 255)); fillCircle(mx - mr * 0.3f, my - mr * 0.2f, mr * 0.28f, T(214, 214, 196, 255)); fillCircle(mx + mr * 0.35f, my + mr * 0.3f, mr * 0.2f, T(218, 218, 200, 255));
    }
}
static inline float vn(float x, float y, int seed) { return vnoiseP(x, y, seed, 4096); }
// Земля считается один раз для всей карты ("запекается"), а на кадре только читается из таблицы + мелкий шум вблизи.
static void groundShade(float fx, float fy, float fp, float* R, float* Gc, float* Bc, float* Sw) {
    float L1 = vn(fx * 0.20f, fy * 0.20f, 201), L2 = vn(fx * 0.65f, fy * 0.65f, 202), M1 = vn(fx * 2.4f, fy * 2.4f, 203);
    float M2 = 0.5f;
    if (fp < 0.05f) M2 = vn(fx * 9.f, fy * 9.f, 204);
    float t = M1 * 0.55f + M2 * 0.45f;
    float r = 30 + t * 40, g = 42 + t * 46, b = 22 + t * 18;                                  // тёмно-оливковая трава
    float dry = sstep(0.55f, 0.76f, L1 * 0.7f + L2 * 0.3f);                                    // сухие участки
    r += (88 - r) * dry * 0.55f; g += (80 - g) * dry * 0.42f; b += (44 - b) * dry * 0.32f;
    float sw = sstep(0.70f, 0.82f, L1 + (M2 - 0.5f) * 0.25f);                                  // проплешины с землёй
    r += (70 - r) * sw; g += (54 - g) * sw; b += (40 - b) * sw;
    *R = r; *Gc = g; *Bc = b; *Sw = sw;
}
static bool gmapReady = false;
static bool floorValid = false; static unsigned long long floorSig = 0;   // пол уже посчитан для этого положения камеры — можно не пересчитывать
static const int GR = 10;                                   // клеток запечённой карты на единицу мира
static std::vector<u32> gmap;
static void bakeGround() {
    int GW = N * GR;
    gmap.assign((size_t)GW * GW, 0);
    for (int gy = 0; gy < GW; gy++)
        for (int gx = 0; gx < GW; gx++) {
            float fx = (gx + 0.5f) / GR, fy = (gy + 0.5f) / GR, r, g, b, sw;
            groundShade(fx, fy, 1.f / GR, &r, &g, &b, &sw);
            int ix = std::min(N - 1, (int)fx), iy = std::min(N - 1, (int)fy);
            float ao = 1.f, fxr = fx - ix, fyr = fy - iy;                         // тень у оснований стен
            if (ix > 0 && (G[iy * N + ix - 1] == 1 || G[iy * N + ix - 1] == 3)) ao = std::min(ao, 0.5f + 0.5f * sstep(0.f, 0.5f, fxr));
            if (ix < N - 1 && (G[iy * N + ix + 1] == 1 || G[iy * N + ix + 1] == 3)) ao = std::min(ao, 0.5f + 0.5f * sstep(0.f, 0.5f, 1.f - fxr));
            if (iy > 0 && (G[(iy - 1) * N + ix] == 1 || G[(iy - 1) * N + ix] == 3)) ao = std::min(ao, 0.5f + 0.5f * sstep(0.f, 0.5f, fyr));
            if (iy < N - 1 && (G[(iy + 1) * N + ix] == 1 || G[(iy + 1) * N + ix] == 3)) ao = std::min(ao, 0.5f + 0.5f * sstep(0.f, 0.5f, 1.f - fyr));
            float wp = sstep(0.74f, 0.80f, vn(fx * 0.5f, fy * 0.5f, 113));
            int a = ((int)(wp * 15.f + 0.5f) << 4) | (int)(sw * 15.f + 0.5f);
            gmap[(size_t)gy * GW + gx] = ((u32)a << 24) | ((u32)std::min(255, (int)(r * ao)) << 16) | ((u32)std::min(255, (int)(g * ao)) << 8) | (u32)std::min(255, (int)(b * ao));
        }
    gmapReady = true; floorValid = false;
}
static inline void gmapSample(float fx, float fy, float* r, float* g, float* b, float* pw, float* sw) {
    const int GW = N * GR;
    float gx = fx * GR - 0.5f, gy = fy * GR - 0.5f;
    int x0 = (int)floorf(gx), y0 = (int)floorf(gy); float tx = gx - x0, ty = gy - y0;
    int x1 = std::min(GW - 1, std::max(0, x0 + 1)), y1 = std::min(GW - 1, std::max(0, y0 + 1)); x0 = std::min(GW - 1, std::max(0, x0)); y0 = std::min(GW - 1, std::max(0, y0));
    u32 a = gmap[(size_t)y0 * GW + x0], b_ = gmap[(size_t)y0 * GW + x1], c = gmap[(size_t)y1 * GW + x0], d = gmap[(size_t)y1 * GW + x1];
    float w00 = (1 - tx) * (1 - ty), w10 = tx * (1 - ty), w01 = (1 - tx) * ty, w11 = tx * ty;
    *r = ((a >> 16) & 255) * w00 + ((b_ >> 16) & 255) * w10 + ((c >> 16) & 255) * w01 + ((d >> 16) & 255) * w11;
    *g = ((a >> 8) & 255) * w00 + ((b_ >> 8) & 255) * w10 + ((c >> 8) & 255) * w01 + ((d >> 8) & 255) * w11;
    *b = (a & 255) * w00 + (b_ & 255) * w10 + (c & 255) * w01 + (d & 255) * w11;
    *pw = (((a >> 28) & 15) * w00 + ((b_ >> 28) & 15) * w10 + ((c >> 28) & 15) * w01 + ((d >> 28) & 15) * w11) * (1.f / 15.f);
    *sw = ((((a >> 24) & 15) * w00 + ((b_ >> 24) & 15) * w10 + ((c >> 24) & 15) * w01 + ((d >> 24) & 15) * w11)) * (1.f / 15.f);
}
static inline float detSample(const float* tex, float x, float y) {
    int x0 = (int)floorf(x), y0 = (int)floorf(y); float tx = x - x0, ty = y - y0;
    int xa = x0 & (TS - 1), xb = (x0 + 1) & (TS - 1), ya = y0 & (TS - 1), yb = (y0 + 1) & (TS - 1);
    return (tex[ya * TS + xa] * (1 - tx) + tex[ya * TS + xb] * tx) * (1 - ty) + (tex[yb * TS + xa] * (1 - tx) + tex[yb * TS + xb] * tx) * ty;
}
static std::vector<u32> floorBuf2;
static int FLW2 = 0, FLH2 = 0; static float FLPX2 = 3.f, NEAR_OFF = 0.f; static SDL_Texture* FLOORTEX2 = NULL;
static bool pathCell(int ix, int iy) {     // булыжные дорожки от проёмов убежища
    int dx = ix - C0, dy = iy - C0;
    if ((dx == -1 || dx == 0) && abs(dy) > 4 && abs(dy) <= 11) return true;
    if ((dy == -1 || dy == 0) && abs(dx) > 4 && abs(dx) <= 11) return true;
    return false;
}
static float FLDXC[1024], FLDYC[1024], FLLITE[1024], FLHIDE[1024];
static void floorRows(std::vector<u32>& buf, int bw, float pix, float offStart, int r0, int r1, float dx, float dy, float plx, float ply, const float* hide = NULL, float yTop = 0.f) {
    float px = P->x, py = P->y;
    const float FR = FOGR, FG = FOGG, FB = FOGB;
    for (int c = 0; c < bw && c < 1024; c++) {        // то, что не зависит от строки, считаем один раз на столбец (результат тот же)
        float cx = 2.f * (c + 0.5f) * pix / W - 1.f, a = 1.f - fabsf(cx) * 0.85f;
        FLDXC[c] = dx + plx * cx; FLDYC[c] = dy + ply * cx; FLLITE[c] = 0.82f + 0.32f * a * a;
    }
    for (int r = r0; r < r1; r++) {
        float off = offStart + (r + 0.5f) * pix, d = FOCAL * EYE_H / off;
        if (off < 1.f) continue;
        float kd = std::max(0.f, 1.f - d / MAXD), k = 0.30f + 0.70f * kd, fa = powf(1.f - kd, 1.6f) * 0.72f, fp = pix * d / FOCAL;
        float wA = 1.f - sstep(0.15f, 0.40f, fp * 1.0f), wB = 1.f - sstep(0.15f, 0.40f, fp * 12.f);      // мелкие детали исчезают вдали
        u32* row = &buf[(size_t)r * bw];
        const float hideT = yTop + (r + 1.5f) * pix + 2.f;     // ниже этой границы (с запасом в один тексель для сглаживания) пол уже виден
        for (int c = 0; c < bw; c++) {
            if (hide && hide[c] >= hideT) continue;             // этот кусок пола целиком закрыт стеной — его никто не увидит
            float fx = px + FLDXC[c] * d, fy = py + FLDYC[c] * d;
            int ix = std::max(0, std::min(N - 1, (int)floorf(fx))), iy = std::max(0, std::min(N - 1, (int)floorf(fy)));
            float cr, cg, cb;
            bool conc = ix >= C0 - 3 && ix <= C0 + 3 && iy >= C0 - 3 && iy <= C0 + 3, path = !conc && pathCell(ix, iy);
            float dA = 0.5f, dB = 0.5f;
            if (wA > 0.02f) dA = 0.5f + (detSample(DETA, fx * 8.f, fy * 8.f) - 0.5f) * wA;
            if (wB > 0.02f) dB = 0.5f + (detSample(DETB, fx * 32.f, fy * 32.f) - 0.5f) * wB;
            if (conc || path) {
                int tu = (int)((fx - floorf(fx)) * TS) & (TS - 1), tv = (int)((fy - floorf(fy)) * TS) & (TS - 1);
                u32 t0 = conc ? T_CONC[tv * TS + tu] : T_COBBLE[tv * TS + tu];
                float det = 0.86f + 0.28f * dB;
                cr = ((t0 >> 16) & 255) * det; cg = ((t0 >> 8) & 255) * det; cb = (t0 & 255) * det;
            } else {
                float pw, sw;
                gmapSample(fx, fy, &cr, &cg, &cb, &pw, &sw);
                float kk = 0.66f + 0.62f * (dA * 0.55f + dB * 0.45f);                                // зернистость травы
                cr *= kk; cg *= kk; cb *= kk;
                if (wB > 0.4f && sw < 0.5f) { if (dB > 0.66f) { cr += 16; cg += 22; cb += 4; } else if (dB < 0.34f) { cr *= 0.65f; cg *= 0.65f; cb *= 0.65f; } }
                if (wB > 0.5f && sw > 0.5f && dB > 0.72f) { float gs = 96 + dA * 60; cr = gs; cg = gs * 0.97f; cb = gs * 0.92f; }   // камешки в земле
                if (pw > 0.f) {                                                 // лужа: тёмная вода с отражением неба
                    float refl = 0.5f + 0.5f * (1.f - kd), rip = 0.9f + 0.2f * dB;
                    float pr = 20 + 40 * refl * rip, pg = 28 + 48 * refl * rip, pb = 42 + 74 * refl * rip;
                    cr += (pr - cr) * pw * 0.85f; cg += (pg - cg) * pw * 0.85f; cb += (pb - cb) * pw * 0.85f;
                }
            }
            float lite = FLLITE[c];
            float v = (0.88f + 0.24f * VARR[iy * N + ix]) * k * lite;
            int rr_ = (int)(cr * v * 0.9f * (1 - fa) + FR * fa), gg = (int)(cg * v * 0.95f * (1 - fa) + FG * fa), bb = (int)(cb * v * (1 - fa) + FB * fa);
            row[c] = 0xFF000000u | ((u32)std::min(255, rr_) << 16) | ((u32)std::min(255, gg) << 8) | (u32)std::min(255, bb);
        }
    }
}
static float WBOT[1024];      // нижний край стены в каждом столбце (ниже него виден пол)
static void renderFloor(float dx, float dy, float plx, float ply) {
    if (!FLOORTEX || floorBuf.empty()) return;
    if (!gmapReady) bakeGround();
    int r0 = std::max(0, (int)floorf(-HZ / FLPX)), r1 = std::min(FLH, (int)ceilf((H - HZ) / FLPX) + 1);
    // где именно пол закрыт стенами: для каждого столбца пола берём самую высокую из стен, что его перекрывают (с запасом на сглаживание)
    float gmin = 1e9f;
    for (int c = 0; c < FLW && c < 1024; c++) {
        float xa = (c - 0.5f) * FLPX, xb = (c + 1.5f) * FLPX;
        int ia = std::max(0, (int)floorf(xa * RW / W)), ib = std::min(RW - 1, (int)floorf(xb * RW / W));
        float m = 1e9f;
        for (int i = ia; i <= ib; i++) m = std::min(m, WBOT[i]);
        FLHIDE[c] = m; gmin = std::min(gmin, m);
    }
    int rFirst = std::max(r0, (int)floorf((gmin - 2.f - HZ) / FLPX - 1.5f) + 1);   // строки выше — целиком под стенами: их не считаем (но размер и положение картинки пола оставляем прежними)
    if (r1 <= rFirst) return;                                                       // весь пол закрыт стенами — рисовать нечего
    unsigned long long sig = 1469598103934665603ULL;                            // «отпечаток» всего, от чего зависит пол
    auto mix = [&](float f) { unsigned u; memcpy(&u, &f, 4); sig = (sig ^ u) * 1099511628211ULL; };
    mix(P->x); mix(P->y); mix(P->ang); mix(HZ); mix(EYE_H); mix((float)r0); mix((float)rFirst); mix((float)r1); mix((float)FLW); mix(FLPX); mix((float)W); mix((float)H);
    for (int c = 0; c < FLW && c < 1024; c++) mix(FLHIDE[c]);
    if (!(floorValid && sig == floorSig)) {                                       // камера и стены те же — картинка пола уже лежит в текстуре
        floorRows(floorBuf, FLW, FLPX, 0.f, rFirst, r1, dx, dy, plx, ply, FLHIDE, HZ);
        SDL_Rect ur = {0, rFirst, FLW, r1 - rFirst};
        SDL_UpdateTexture(FLOORTEX, &ur, &floorBuf[(size_t)rFirst * FLW], FLW * 4);
        floorSig = sig; floorValid = true;
    }
    SDL_Rect src = {0, r0, FLW, r1 - r0}, dst = {0, (int)(HZ + r0 * FLPX), W, (int)ceilf((r1 - r0) * FLPX) + 1};
    SDL_RenderCopy(ren, FLOORTEX, &src, &dst);
}
static float WD[1024], WF[1024]; static int WC[1024], WI[1024], WT[1024]; static char WSD[1024];
static void renderWalls() {
    float px = P->x, py = P->y, dx = cosf(P->ang), dy = sinf(P->ang), plx = -dy * TANH_, ply = dx * TANH_;
    int mx0 = (int)px, my0 = (int)py;
    for (int c = 0; c < RW && c < 1024; c++) { float a = 1.f - fabsf(CAMX[c]) * 0.85f; FLASH_L[c] = 0.82f + 0.32f * a * a; }
    renderSky();
    for (int i = 0; i < RW; i++) {                    // проход 1: лучи — до какой стены и где она кончается (пол по этим данным считаем только видимый)
        float cx = CAMX[i], rdx = dx + plx * cx, rdy = dy + ply * cx;
        int mx = mx0, my = my0;
        float ddx = rdx != 0 ? fabsf(1.f / rdx) : 1e30f, ddy = rdy != 0 ? fabsf(1.f / rdy) : 1e30f, sdx, sdy;
        int sx, sy;
        if (rdx < 0) { sx = -1; sdx = (px - mx) * ddx; } else { sx = 1; sdx = (mx + 1.f - px) * ddx; }
        if (rdy < 0) { sy = -1; sdy = (py - my) * ddy; } else { sy = 1; sdy = (my + 1.f - py) * ddy; }
        int side = 0, c = 0;
        for (int k = 0; k < 80; k++) {
            if (sdx < sdy) { sdx += ddx; mx += sx; side = 0; } else { sdy += ddy; my += sy; side = 1; }
            c = G[my * N + mx]; if (c) break;
        }
        float dist = side == 0 ? (sdx - ddx) : (sdy - ddy);
        if (dist < 0.05f) dist = 0.05f;
        zbuf[i] = dist;
        float wx = side == 0 ? py + dist * rdy : px + dist * rdx; wx -= floorf(wx);
        int tx = std::min(TS - 1, (int)(wx * TS));
        if ((side == 0 && rdx > 0) || (side == 1 && rdy < 0)) tx = TS - 1 - tx;
        WD[i] = dist; WC[i] = c; WI[i] = my * N + mx; WT[i] = tx; WSD[i] = (char)side;
        WF[i] = ((side == 0 && rdx > 0) || (side == 1 && rdy < 0)) ? 1.f - wx : wx;     // где именно на стене попал луч (0..1), с учётом отражения
        WBOT[i] = WALLTEX[c & 3] ? HZ + EYE_H * FOCAL / dist - 1.f : -1e9f;
    }
    renderFloor(dx, dy, plx, ply);
    for (int i = 0; i < RW; i++) {                    // проход 2: рисуем стены
        float dist = WD[i]; int c = WC[i], idx = WI[i], tx = WT[i], side = WSD[i];
        float lh = FOCAL / dist, y0 = HZ - (1.f - EYE_H) * lh;
        float kd = std::max(0.f, 1.f - dist / MAXD);
        float k = 0.30f + 0.70f * kd; if (side) k *= 0.74f;
        float v = k * FLASH_L[i] * (0.9f + 0.1f * VARR[idx]), ratio = 1.f;
        if (c == 2) { ratio = std::min(1.f, bratio(idx)); v *= 0.6f + 0.4f * ratio; }
        SDL_Texture* wt = WALLTEX[c & 3];
        FOGA[i] = 0.f;              // на случай редкого continue ниже — не тащим мусор с прошлого кадра
        if (!wt) continue;
        int xa = i * W / RW, xb = (i + 1) * W / RW;
        SDL_Rect src = {tx, 0, 1, TS}, dst = {xa, (int)floorf(y0), xb - xa, (int)ceilf(lh) + 1};
        SDL_Texture* dtex = wt; SDL_Rect dsrc = src;
        if (quality > 0) {      // «Средняя/Высокая»: ближние стены — из крупной текстуры, а вместо одного тексельного столбика берём столько, сколько реально покрывает луч (без полос и мерцания)
            bool hi = WALLHI[c & 3] && lh >= 190.f;
            int S = hi ? TSH : TS; dtex = hi ? WALLHI[c & 3] : wt;
            float cover = 0.f;
            if (i > 0 && i < RW - 1 && WI[i - 1] == idx && WI[i + 1] == idx && WSD[i - 1] == WSD[i] && WSD[i + 1] == WSD[i]) cover = fabsf(WF[i + 1] - WF[i - 1]) * 0.5f * S;
            int w = std::max(1, std::min(6, (int)(cover + 0.5f)));
            int sx = (int)floorf(WF[i] * S - w * 0.5f + 0.5f); sx = std::max(0, std::min(S - w, sx));
            dsrc.x = sx; dsrc.y = 0; dsrc.w = w; dsrc.h = S;
        }
        SDL_SetTextureColorMod(dtex, (Uint8)(255 * std::min(1.f, v * 0.90f)), (Uint8)(255 * std::min(1.f, v * 0.95f)), (Uint8)(255 * std::min(1.f, v)));
        SDL_RenderCopy(ren, dtex, &dsrc, &dst);
        if (c == 2 && ratio < 0.6f && CRACKTEX) {
            SDL_SetTextureColorMod(CRACKTEX, (Uint8)(255 * std::min(1.f, v)), (Uint8)(255 * std::min(1.f, v)), (Uint8)(255 * std::min(1.f, v)));
            SDL_SetTextureAlphaMod(CRACKTEX, (Uint8)(255 * std::min(1.f, (0.6f - ratio) * 3 + 0.4f)));
            SDL_RenderCopy(ren, CRACKTEX, &src, &dst);
        }
        float fa = powf(1.f - kd, 1.6f) * 0.72f;      // дымка вдали: копим и рисуем позже слитными полосами — так вместо кучи мелких заливок получается несколько широких
        FOGA[i] = fa; FOGY0[i] = dst.y; FOGY1[i] = dst.y + dst.h; FOGX[i] = xa; FOGX[i + 1] = xb;
    }
    for (int i = 0; i < RW;) {                        // склеиваем соседние столбцы со схожей дымкой в одну заливку
        if (FOGA[i] <= 0.06f) { i++; continue; }
        int j = i, y0 = FOGY0[i], y1 = FOGY1[i]; float fsum = FOGA[i]; int qa = (int)(FOGA[i] * 12.f);
        while (j + 1 < RW && FOGA[j + 1] > 0.06f && (int)(FOGA[j + 1] * 12.f) == qa) {
            j++; y0 = std::min(y0, FOGY0[j]); y1 = std::max(y1, FOGY1[j]); fsum += FOGA[j];
        }
        float favg = fsum / (j - i + 1);
        fillRect((float)FOGX[i], (float)y0, (float)(FOGX[j + 1] - FOGX[i]), (float)(y1 - y0), C(FOGR, FOGG, FOGB, (int)(favg * 255)));
        i = j + 1;
    }
}

static void drawRuns(SDL_Texture* tex, int tw, int th, float x0, float top, float sw, float sh, float ty) {
    int c0 = std::max(0, (int)floorf(x0 * RW / W)), c1 = std::min(RW - 1, (int)floorf((x0 + sw) * RW / W));
    int c = c0;
    while (c <= c1) {
        if (zbuf[c] <= ty) { c++; continue; }
        int run = c;
        while (c <= c1 && zbuf[c] > ty) c++;
        float dx0 = std::max(x0, (float)(run * W / RW)), dx1 = std::min(x0 + sw, (float)(c * W / RW));
        if (dx1 <= dx0) continue;
        int sx0 = (int)((dx0 - x0) / sw * tw), sx1 = (int)ceilf((dx1 - x0) / sw * tw);
        sx0 = std::max(0, sx0); sx1 = std::min(tw, std::max(sx1, sx0 + 1));
        SDL_Rect src = {sx0, 0, sx1 - sx0, th}, dst = {(int)dx0, (int)top, std::max(1, (int)(dx1 - dx0 + 0.5f)), (int)sh};
        SDL_RenderCopy(ren, tex, &src, &dst);
    }
}

struct SpriteRef { float ty, tx; int type; int idx; };   // type: 0 зомби, 1 ящик, 2 игрок, 3 декорация, 4 труп, 5 лужа, 6 плевок
static void renderSprites() {
    float dx = cosf(P->ang), dy = sinf(P->ang), plx = -dy * TANH_, ply = dx * TANH_;
    float inv = 1.f / (plx * dy - dx * ply);
    std::vector<SpriteRef> lst;
    for (size_t i = 0; i < zombies.size(); i++) {
        float rx = zombies[i].x - P->x, ry = zombies[i].y - P->y, ty = inv * (-ply * rx + plx * ry);
        if (ty > 0.15f && ty < MAXD) lst.push_back({ty, inv * (dy * rx - dx * ry), 0, (int)i});
    }
    for (size_t i = 0; i < crates.size(); i++) {
        float rx = crates[i].x - P->x, ry = crates[i].y - P->y, ty = inv * (-ply * rx + plx * ry);
        if (ty > 0.15f && ty < MAXD) lst.push_back({ty, inv * (dy * rx - dx * ry), 1, (int)i});
    }
    for (std::map<int, Player>::iterator it = players.begin(); it != players.end(); ++it) {
        Player& p = it->second; if (&p == P || p.dead) continue;
        float rx = p.x - P->x, ry = p.y - P->y, ty = inv * (-ply * rx + plx * ry);
        if (ty > 0.15f && ty < MAXD) lst.push_back({ty, inv * (dy * rx - dx * ry), 2, p.id});
    }
    for (size_t i = 0; i < decos.size(); i++) {
        const Deco& d = decos[i];
        if (G[(int)d.y * N + (int)d.x] != 0) continue;
        if (d.kind == 6 && boxHp[i] <= 0) continue;      // ящик разбит
        float rx = d.x - P->x, ry = d.y - P->y, ty = inv * (-ply * rx + plx * ry);
        if (ty > 0.2f && ty < 11.f) { float tx = inv * (dy * rx - dx * ry); if (fabsf(tx) < ty * 1.5f + 0.4f) lst.push_back({ty, tx, 3, (int)i}); }
    }
    if (quality > 0) {          // дополнительная трава вокруг игрока: на «Средней» реже, на «Высокой» гуще; никак не влияет на игру и сеть
        const int per = quality == 1 ? 1 : 2, R = quality == 1 ? 6 : 8; const float dens = quality == 1 ? 0.6f : 0.95f;
        int cx0 = (int)P->x, cy0 = (int)P->y;
        for (int cy = cy0 - R; cy <= cy0 + R; cy++)
            for (int cx = cx0 - R; cx <= cx0 + R; cx++) {
                if (cx < 1 || cy < 1 || cx >= N - 1 || cy >= N - 1) continue;
                int cell = cy * N + cx;
                if (G[cell] != 0 || solidDeco[cell] >= 0 || (abs(cx - C0) <= 5 && abs(cy - C0) <= 5) || pathCell(cx, cy)) continue;
                for (int j = 0; j < per; j++) {
                    u32 h = hashu(cx, cy, 401 + j);
                    if ((h & 255) / 255.f >= dens) continue;
                    float gx = cx + 0.1f + ((h >> 8) & 255) / 255.f * 0.8f, gy = cy + 0.1f + ((h >> 16) & 255) / 255.f * 0.8f;
                    float rx = gx - P->x, ry = gy - P->y, ty = inv * (-ply * rx + plx * ry);
                    if (ty > 0.3f && ty < R + 1.f) { float tx = inv * (dy * rx - dx * ry); if (fabsf(tx) < ty * 1.5f + 0.4f) lst.push_back({ty, tx, 8, cell * 2 + j}); }
                }
            }
    }
    for (size_t i = 0; i < corpses.size(); i++) {
        float rx = corpses[i].x - P->x, ry = corpses[i].y - P->y, ty = inv * (-ply * rx + plx * ry);
        if (ty > 0.2f && ty < MAXD) { float tx = inv * (dy * rx - dx * ry); if (fabsf(tx) < ty * 1.5f + 0.6f) lst.push_back({ty, tx, 4, (int)i}); }
    }
    for (size_t i = 0; i < decals.size(); i++) {
        float rx = decals[i].x - P->x, ry = decals[i].y - P->y, ty = inv * (-ply * rx + plx * ry);
        if (ty > 0.2f && ty < MAXD) { float tx = inv * (dy * rx - dx * ry); if (fabsf(tx) < ty * 1.5f + 0.6f) lst.push_back({ty, tx, 5, (int)i}); }
    }
    for (size_t i = 0; i < spits.size(); i++) {
        float rx = spits[i].x - P->x, ry = spits[i].y - P->y, ty = inv * (-ply * rx + plx * ry);
        if (ty > 0.15f && ty < MAXD) lst.push_back({ty, inv * (dy * rx - dx * ry), 6, (int)i});
    }
    for (size_t i = 0; i < grens.size(); i++) {
        float rx = grens[i].x - P->x, ry = grens[i].y - P->y, ty = inv * (-ply * rx + plx * ry);
        if (ty > 0.15f && ty < MAXD) lst.push_back({ty, inv * (dy * rx - dx * ry), 7, (int)i});
    }
    std::sort(lst.begin(), lst.end(), [](const SpriteRef& a, const SpriteRef& b) { return a.ty > b.ty; });
    for (size_t li = 0; li < lst.size(); li++) {
        const SpriteRef& s = lst[li];
        if (s.type == 8) {           // дополнительный пучок травы
            int cell = s.idx / 2, j = s.idx % 2; u32 h = hashu(cell % N, cell / N, 401 + j);
            float sz = 0.70f + ((h >> 24) & 255) / 255.f * 0.55f, sh = FOCAL * 0.21f * sz / s.ty;
            if (sh < 2 || sh > H * 2) continue;
            float sxc = W / 2.f * (1.f + s.tx / s.ty), floorY = HZ + FOCAL * EYE_H / s.ty, top = floorY - sh;
            float shd = std::max(0.16f, 1.f - s.ty / MAXD); int vv = (int)(255 * shd);
            float vr = 0.86f + 0.24f * (((h >> 4) & 255) / 255.f), vg = 0.92f + 0.16f * (((h >> 12) & 255) / 255.f);
            SDL_Texture* gt = GRASSTEX[h % 3]; if (!gt) continue;
            SDL_SetTextureColorMod(gt, (Uint8)std::min(255.f, vv * vr), (Uint8)std::min(255.f, vv * vg), (Uint8)vv);
            drawRuns(gt, 128, 128, sxc - sh / 2, top, sh, sh, s.ty);
            continue;
        }
        if (s.type == 7) {           // граната в полёте
            const Gren& g = grens[s.idx];
            float sxc = W / 2.f * (1.f + s.tx / s.ty), fy = HZ + FOCAL * (EYE_H - g.z) / s.ty, fl = HZ + FOCAL * EYE_H / s.ty, r = std::max(2.f, FOCAL * 0.07f / s.ty);
            int col = (int)floorf(sxc * RW / W);
            if (col < 0 || col >= RW || zbuf[col] <= s.ty) continue;
            if (SHADOWTEX) { SDL_SetTextureAlphaMod(SHADOWTEX, 200); drawRuns(SHADOWTEX, 32, 16, sxc - r * 1.5f, fl - r * 0.4f, r * 3.f, r * 0.8f, s.ty); }
            fillCircle(sxc, fy, r, g.type == 0 ? C(70, 104, 60) : C(90, 150, 225));
            ringCircle(sxc, fy, r, std::max(1.f, r * 0.2f), C(25, 35, 28));
            fillRect(sxc - r * 0.28f, fy - r * 1.35f, r * 0.56f, r * 0.45f, C(205, 205, 210));
            if (((int)(animT * 7.f)) & 1) fillCircle(sxc, fy, std::max(1.f, r * 0.32f), g.type == 0 ? C(255, 60, 40) : C(255, 255, 255));
            continue;
        }
        if (s.type == 6) {           // кислотный плевок
            float sxc = W / 2.f * (1.f + s.tx / s.ty), fy = HZ + FOCAL * (EYE_H - 0.45f) / s.ty, r = std::max(2.f, FOCAL * 0.10f / s.ty);
            int col = (int)floorf(sxc * RW / W);
            if (col < 0 || col >= RW || zbuf[col] <= s.ty) continue;
            if (TORCHGLOW) { SDL_SetTextureColorMod(TORCHGLOW, 70, 255, 90); SDL_SetTextureAlphaMod(TORCHGLOW, 230); float gs = r * 6.f; SDL_Rect gr = {(int)(sxc - gs / 2), (int)(fy - gs / 2), (int)gs, (int)gs}; SDL_RenderCopy(ren, TORCHGLOW, NULL, &gr); SDL_SetTextureColorMod(TORCHGLOW, 255, 255, 255); }
            fillCircle(sxc, fy, r, C(150, 255, 90)); fillCircle(sxc, fy, std::max(1.f, r * 0.5f), C(235, 255, 200));
            continue;
        }
        if (s.type == 5) {           // лужа крови на полу
            const Decal& d = decals[s.idx];
            float sxc = W / 2.f * (1.f + s.tx / s.ty), w2 = FOCAL * d.size / s.ty, h2 = w2 * 0.32f, floorY = HZ + FOCAL * EYE_H / s.ty;
            if (w2 < 2 || w2 > W * 3 || !BLOODTEX) continue;
            float shd = std::max(0.2f, 1.f - s.ty / MAXD); int v = (int)(255 * shd);
            float fade = d.age > 30.f ? std::max(0.f, 1.f - (d.age - 30.f) / 30.f) : 1.f;
            if (d.scorch) SDL_SetTextureColorMod(BLOODTEX, v / 5, v / 5, v / 5); else SDL_SetTextureColorMod(BLOODTEX, v, v, v);
            SDL_SetTextureAlphaMod(BLOODTEX, (Uint8)(235 * fade));
            drawRuns(BLOODTEX, 64, 32, sxc - w2 / 2, floorY - h2 / 2, w2, h2, s.ty);
            continue;
        }
        SDL_Texture* tex; float hs; int tw, th; float bobo = 0;
        if (s.type == 0) {
            const Zombie& z = zombies[s.idx];
            int fr = ((int)(animT * 5.f + z.id * 0.7f)) & 1;
            tex = ZTEX[z.kind][fr]; hs = z.hs; tw = 80; th = 128; bobo = sinf(animT * 9.f + z.id) * 0.018f;
        } else if (s.type == 1) { tex = CTEX[crates[s.idx].kind]; hs = 0.34f; tw = 64; th = 64; bobo = sinf(animT * 3.f + s.idx) * 0.02f + 0.03f; }
        else if (s.type == 3) { tex = (decos[s.idx].kind == 0 && quality > 0 && GRASSTEX[0]) ? GRASSTEX[s.idx % 3] : DTEX[decos[s.idx].kind]; hs = DHS[decos[s.idx].kind]; tw = 128; th = 128; }
        else if (s.type == 4) { tex = ZTEX[corpses[s.idx].kind][1]; hs = ZK[corpses[s.idx].kind].hs; tw = 80; th = 128; }
        else {
            const Player& p = players[s.idx];
            bool mv = hypotf(p.tx - p.x, p.ty - p.y) > 0.02f;
            int fr = mv ? (((int)(animT * 7.f)) & 1) : 1;
            tex = PTEX[s.idx % 4][fr]; hs = 0.95f; tw = 80; th = 128;
        }
        if (!tex) continue;
        float sxc = W / 2.f * (1.f + s.tx / s.ty), sh = FOCAL * hs / s.ty;
        if (sh < 2 || sh > H * 4) continue;
        float sw = sh * tw / th, corpseA = 1.f;
        if (s.type == 4) {
            const Corpse& c = corpses[s.idx]; float f = std::min(1.f, c.t / 0.35f);
            f = f * f * (3 - 2 * f); sh *= 1.f - 0.74f * f; sw *= 1.f + 0.85f * f;
            corpseA = c.t > 8.f ? std::max(0.f, 1.f - (c.t - 8.f) / 4.f) : 1.f;
        }
        float jumpOff = (s.type == 2) ? players[s.idx].jumpZ * FOCAL / s.ty : 0.f;
        float x0 = sxc - sw / 2, floorY = HZ + FOCAL * EYE_H / s.ty, top = floorY - sh - bobo * sh - jumpOff;
        float shd = 1.f - s.ty / MAXD; if (shd < 0.16f) shd = 0.16f;
        if (s.type == 4) shd *= 0.55f;
        int v = (int)(255 * shd);
        // тень на земле
        if (SHADOWTEX && s.type != 4) {
            float w2 = sw * (s.type == 1 || s.type == 3 ? 0.9f : 1.15f), h2 = w2 * 0.30f;
            SDL_SetTextureAlphaMod(SHADOWTEX, (Uint8)(230 * std::min(1.f, shd + 0.3f)));
            drawRuns(SHADOWTEX, 32, 16, sxc - w2 / 2, floorY - h2 * 0.5f, w2, h2, s.ty);
        }
        bool flash = s.type == 0 && zombies[s.idx].flash > 0;
        float tr = 0.92f, tg = 0.96f, tb = 1.f;
        if (s.type == 0) { int zid_ = zombies[s.idx].id; tr *= 0.88f + 0.24f * hnoise(zid_, 1, 5); tg *= 0.88f + 0.24f * hnoise(zid_, 2, 5); tb *= 0.88f + 0.24f * hnoise(zid_, 3, 5); }   // у каждого зомби свой оттенок
        if (s.type == 0 && zombies[s.idx].stun > 0) { tr *= 0.65f; tg *= 0.85f; tb *= 1.2f; }      // оглушённый зомби синеет
        SDL_SetTextureColorMod(tex, (Uint8)std::min(255.f, v * tr), flash ? v / 3 : (Uint8)std::min(255.f, v * tg), flash ? v / 3 : (Uint8)std::min(255.f, v * tb));
        if (s.type == 4) SDL_SetTextureAlphaMod(tex, (Uint8)(255 * corpseA));
        drawRuns(tex, tw, th, x0, top, sw, sh, s.ty);
        if (s.type == 4) SDL_SetTextureAlphaMod(tex, 255);
        if (s.type == 3 && decos[s.idx].kind == 7) {              // живое пламя факела
            int fcol = (int)floorf(sxc * RW / W);
            if (fcol >= 0 && fcol < RW && zbuf[fcol] > s.ty) {
                float fl = 0.86f + 0.14f * sinf(animT * 13.f + s.idx * 1.7f) + 0.07f * sinf(animT * 31.f + s.idx);
                float fx = sxc + sinf(animT * 9.f + s.idx) * sh * 0.012f, fy = top + sh * 0.10f, fr = sh * 0.115f * fl;
                if (TORCHGLOW) { SDL_SetTextureAlphaMod(TORCHGLOW, (Uint8)(235 * fl)); float gs = sh * 3.4f; SDL_Rect gr = {(int)(fx - gs / 2), (int)(fy - gs / 2), (int)gs, (int)gs}; SDL_RenderCopy(ren, TORCHGLOW, NULL, &gr); }
                float px_[4] = {fx, fx + fr * 0.8f, fx, fx - fr * 0.8f}, py_[4] = {fy - fr * 2.1f, fy - fr * 0.1f, fy + fr * 0.8f, fy - fr * 0.1f};
                fillPoly(px_, py_, 4, C(255, 110, 20));
                float qx[4] = {fx, fx + fr * 0.5f, fx, fx - fr * 0.5f}, qy[4] = {fy - fr * 1.4f, fy - fr * 0.05f, fy + fr * 0.55f, fy - fr * 0.05f};
                fillPoly(qx, qy, 4, C(255, 190, 50));
                float wx[4] = {fx, fx + fr * 0.24f, fx, fx - fr * 0.24f}, wy[4] = {fy - fr * 0.6f, fy + fr * 0.05f, fy + fr * 0.4f, fy + fr * 0.05f};
                fillPoly(wx, wy, 4, C(255, 245, 190));
            }
        }
        int colc = (int)floorf(sxc * RW / W);
        if (s.type == 0 && zombies[s.idx].hp < zombies[s.idx].maxhp && colc >= 0 && colc < RW && zbuf[colc] > s.ty) {
            float bw = std::max(sw, 12.f), bx = sxc - bw / 2;
            fillRect(bx, top - 8, bw, 5, C(30, 0, 0)); fillRect(bx + 1, top - 7, (bw - 2) * std::max(0.f, zombies[s.idx].hp) / zombies[s.idx].maxhp, 3, C(230, 40, 30));
        }
        if (s.type == 0 && zombies[s.idx].stun > 0 && colc >= 0 && colc < RW && zbuf[colc] > s.ty) {      // «звёздочки» над оглушённым
            for (int k = 0; k < 3; k++) { float a = animT * 6.f + k * 2.094f; fillCircle(sxc + cosf(a) * sw * 0.32f, top - 4 + sinf(a) * 3.f, std::max(2.f, sh * 0.035f), C(255, 230, 80)); }
        }
        if (s.type == 3 && decos[s.idx].kind == 6 && boxHp[s.idx] < BOX_HP && colc >= 0 && colc < RW && zbuf[colc] > s.ty) {      // полоска HP повреждённого ящика
            float bw = std::max(sw * 0.9f, 12.f), bx = sxc - bw / 2, fr = std::max(0.f, boxHp[s.idx]) / BOX_HP;
            fillRect(bx, top - 8, bw, 5, C(30, 20, 0)); fillRect(bx + 1, top - 7, (bw - 2) * fr, 3, C(255, 190, 50));
        }
        if (s.type == 2 && colc >= 0 && colc < RW && zbuf[colc] > s.ty) fillRect(sxc - 8, top - 10, 16, 5, PCOL[s.idx % 4]);
    }
}
static void renderParticles() {
    float dx = cosf(P->ang), dy = sinf(P->ang), plx = -dy * TANH_, ply = dx * TANH_, inv = 1.f / (plx * dy - dx * ply);
    for (size_t i = 0; i < parts.size(); i++) {
        const Particle& p = parts[i];
        float rx = p.x - P->x, ry = p.y - P->y, ty = inv * (-ply * rx + plx * ry);
        if (ty < 0.15f || ty > MAXD) continue;
        float tx = inv * (dy * rx - dx * ry), sx = W / 2.f * (1.f + tx / ty), sy = HZ + FOCAL * (EYE_H - p.z) / ty, sz = std::max(2.f, FOCAL * p.sz / ty);
        int col = (int)floorf(sx * RW / W);
        if (col < 0 || col >= RW || zbuf[col] <= ty) continue;
        float shd = std::max(0.25f, 1.f - ty / MAXD), al = std::min(1.f, p.life / (p.maxl * 0.35f));
        fillRect(sx - sz / 2, sy - sz / 2, sz, sz, C((int)(p.c.r * shd), (int)(p.c.g * shd), (int)(p.c.b * shd), (int)(255 * al)));
    }
}

// ---------- оружие от первого лица ----------
struct VBox { float x0, x1, y0, y1, z0, z1; Col col; float sh; int mv; };
struct VModel { int n; VBox b[40]; float muz; int mvKind; float mvScale; };
static const Col SKINC = {205, 160, 125, 255}, SKIND = {186, 140, 106, 255}, SLEEVEC = {48, 62, 84, 255}, CUFFC = {84, 102, 134, 255};
static const Col DARKC = {54, 56, 62, 255}, DARKER = {20, 20, 24, 255}, STEELC = {105, 108, 118, 255}, STEELL = {160, 163, 176, 255}, WOODC = {125, 80, 42, 255}, WOODD = {84, 52, 26, 255};
static const Col LENSC = {90, 170, 230, 255};
static VModel VMS[NW];
static bool vmInit = false;
// mv: 0 — неподвижная часть, 1 — подвижная (затвор/цевьё), анимируется при выстреле
static void vmAdd(VModel& m, float x0, float x1, float y0, float y1, float z0, float z1, Col c, float sh = 0.f, int mv = 0) {
    if (m.n < 40) { VBox b = {x0, x1, y0, y1, z0, z1, c, sh, mv}; m.b[m.n++] = b; }
}
static void vmArm(VModel& m) {        // рука идёт от кисти назад и вниз, к камере
    vmAdd(m, -0.26f, 0.26f, -1.55f, -0.50f, -2.9f, -0.30f, SLEEVEC);
    vmAdd(m, -0.29f, 0.29f, -1.05f, -0.42f, -0.95f, -0.45f, CUFFC);
}
static void vmHandPistol(VModel& m) {
    vmAdd(m, -0.20f, -0.12f, 0.20f, 0.36f, 0.05f, 0.90f, SKINC);                      // большой палец
    vmAdd(m, -0.168f, 0.168f, -0.78f, 0.12f, -0.28f, 0.42f, SKINC, -0.30f);          // кисть
    vmAdd(m, -0.192f, 0.192f, -0.62f, -0.43f, 0.30f, 0.58f, SKIND, -0.30f);           // пальцы
    vmAdd(m, -0.192f, 0.192f, -0.40f, -0.21f, 0.30f, 0.58f, SKIND, -0.30f);
    vmAdd(m, -0.192f, 0.192f, -0.18f, 0.01f, 0.30f, 0.58f, SKIND, -0.30f);
}
// доп. детали для оружия: мушка, целик, спусковая скоба, антабка (для реалистичности вида)
static void vmPostSight(VModel& m, float z, float yBase, float h, Col c) {                 // мушка (передний прицел)
    vmAdd(m, -0.018f, 0.018f, yBase, yBase + h, z, z + 0.035f, c);
    vmAdd(m, -0.05f, 0.05f, yBase - 0.02f, yBase + 0.02f, z - 0.01f, z + 0.045f, c);        // основание мушки
}
static void vmNotchSight(VModel& m, float z, float yBase, float h, Col c) {                // целик (задний прицел, вырез)
    vmAdd(m, -0.06f, -0.02f, yBase, yBase + h, z, z + 0.03f, c);
    vmAdd(m, 0.02f, 0.06f, yBase, yBase + h, z, z + 0.03f, c);
}
static void vmGuard(VModel& m, float zA, float zB, float yBot, float yTop, Col c) {         // спусковая скоба (петля вокруг спуска)
    float za = std::min(zA, zB), zb = std::max(zA, zB);
    vmAdd(m, -0.022f, 0.022f, yBot, yTop, za, za + 0.03f, c);
    vmAdd(m, -0.022f, 0.022f, yBot, yTop, zb - 0.03f, zb, c);
    vmAdd(m, -0.022f, 0.022f, yBot, yBot + 0.03f, za, zb, c);
}
static void vmSwivel(VModel& m, float z, float y, Col c) { vmAdd(m, -0.032f, 0.032f, y, y + 0.06f, z, z + 0.03f, c); }   // антабка ремня
static void initVModels() {
    if (vmInit) return;
    vmInit = true;
    for (int i = 0; i < NW; i++) VMS[i].n = 0;
    {   // 0: пистолет
        VModel& m = VMS[0]; m.muz = 2.12f; m.mvKind = 1; m.mvScale = 1.f;
        vmAdd(m, -0.13f, 0.13f, 0.15f, 0.35f, 0.20f, 1.70f, STEELC);
        vmAdd(m, -0.13f, 0.13f, -0.70f, 0.20f, -0.05f, 0.38f, DARKC, -0.30f);
        vmAdd(m, -0.055f, 0.055f, 0.44f, 0.62f, 2.10f, 2.14f, DARKER);
        vmAdd(m, -0.05f, 0.05f, -0.06f, -0.02f, 0.50f, 1.00f, DARKC);
        vmAdd(m, -0.05f, 0.05f, -0.06f, 0.15f, 0.96f, 1.00f, DARKC);
        vmAdd(m, -0.03f, 0.03f, 0.00f, 0.14f, 0.62f, 0.68f, STEELC);
        vmAdd(m, -0.15f, 0.15f, 0.35f, 0.70f, 0.10f, 2.10f, DARKC, 0, 1);              // затвор
        vmAdd(m, -0.07f, 0.07f, 0.70f, 0.725f, 0.28f, 2.00f, STEELL, 0, 1);
        for (int i = 0; i < 4; i++) vmAdd(m, -0.156f, 0.156f, 0.38f, 0.68f, 0.22f + 0.09f * i, 0.25f + 0.09f * i, DARKER, 0, 1);
        vmAdd(m, -0.156f, 0.156f, 0.50f, 0.66f, 0.85f, 1.35f, DARKER, 0, 1);
        vmAdd(m, -0.05f, 0.05f, 0.70f, 0.78f, 0.15f, 0.27f, STEELC, 0, 1);
        vmAdd(m, -0.03f, 0.03f, 0.70f, 0.77f, 1.95f, 2.05f, STEELC, 0, 1);
        vmGuard(m, 0.55f, 0.75f, -0.06f, 0.16f, DARKC);                               // спусковая скоба
        vmPostSight(m, 2.00f, 0.76f, 0.12f, DARKER);                                  // мушка (посажена на кожух-затвор без зазора)
        vmAdd(m, -0.05f, 0.05f, 0.76f, 0.96f, 0.14f, 0.24f, DARKER);                  // курок
        vmHandPistol(m); vmArm(m);
    }
    {   // 3: револьвер
        VModel& m = VMS[3]; m.muz = 2.54f; m.mvKind = 0; m.mvScale = 1.f;
        vmAdd(m, -0.12f, 0.12f, 0.15f, 0.45f, 0.10f, 1.00f, STEELC);
        vmAdd(m, -0.13f, 0.13f, -0.70f, 0.20f, -0.05f, 0.38f, WOODC, -0.30f);
        vmAdd(m, -0.15f, 0.15f, 0.28f, 0.68f, 0.55f, 1.15f, STEELL);
        for (int i = 0; i < 3; i++) vmAdd(m, -0.156f, 0.156f, 0.32f, 0.64f, 0.68f + 0.18f * i, 0.72f + 0.18f * i, DARKER);
        vmAdd(m, -0.07f, 0.07f, 0.42f, 0.62f, 1.15f, 2.50f, DARKC);
        vmAdd(m, -0.08f, 0.08f, 0.68f, 0.72f, 0.30f, 1.20f, DARKC);
        vmAdd(m, -0.03f, 0.03f, 0.62f, 0.68f, 1.15f, 2.50f, DARKER);
        vmAdd(m, -0.03f, 0.03f, 0.62f, 0.78f, 2.40f, 2.50f, STEELC);
        vmAdd(m, -0.05f, 0.05f, 0.72f, 0.80f, 0.20f, 0.32f, STEELC);
        vmAdd(m, -0.03f, 0.03f, 0.55f, 0.80f, -0.05f, 0.15f, STEELC);
        vmAdd(m, -0.075f, 0.075f, 0.40f, 0.64f, 2.50f, 2.54f, DARKER);
        vmAdd(m, -0.05f, 0.05f, -0.06f, -0.02f, 0.50f, 1.00f, DARKC);
        vmAdd(m, -0.05f, 0.05f, -0.06f, 0.15f, 0.96f, 1.00f, DARKC);
        vmAdd(m, -0.03f, 0.03f, 0.00f, 0.14f, 0.62f, 0.68f, STEELC);
        vmGuard(m, 0.02f, 0.32f, -0.06f, 0.16f, STEELC);                              // спусковая скоба
        vmPostSight(m, 2.42f, 0.77f, 0.11f, DARKER);                                  // мушка на стволе (без зазора)
        vmAdd(m, -0.04f, 0.04f, 0.80f, 0.98f, 0.12f, 0.24f, DARKER);                  // курок
        vmHandPistol(m); vmArm(m);
    }
    {   // 1: дробовик
        VModel& m = VMS[1]; m.muz = 3.45f; m.mvKind = 2; m.mvScale = 1.5f;
        vmAdd(m, -0.09f, 0.09f, 0.45f, 0.63f, 0.20f, 3.40f, DARKC);
        vmAdd(m, -0.08f, 0.08f, 0.22f, 0.40f, 0.20f, 3.00f, STEELC);
        vmAdd(m, -0.17f, 0.17f, 0.10f, 0.72f, -0.60f, 0.55f, DARKC);
        vmAdd(m, -0.08f, 0.08f, 0.72f, 0.745f, -0.5f, 0.5f, STEELL);
        vmAdd(m, -0.13f, 0.13f, -0.25f, 0.35f, -2.30f, -0.60f, WOODC);
        vmAdd(m, -0.095f, 0.095f, 0.44f, 0.64f, 3.40f, 3.44f, DARKER);
        vmAdd(m, -0.15f, 0.15f, 0.12f, 0.42f, 1.30f, 2.10f, WOODC, 0, 1);              // цевьё (помпа)
        for (int i = 0; i < 3; i++) vmAdd(m, -0.156f, 0.156f, 0.14f, 0.40f, 1.42f + 0.22f * i, 1.48f + 0.22f * i, WOODD, 0, 1);
        vmAdd(m, -0.136f, 0.136f, -0.75f, 0.10f, -0.55f, 0.00f, SKINC, -0.25f);
        vmGuard(m, -0.12f, 0.15f, -0.02f, 0.16f, DARKC);                              // спусковая скоба
        vmPostSight(m, 3.32f, 0.61f, 0.14f, DARKER);                                  // мушка-«бусина» (посажена прямо на ствол)
        vmSwivel(m, -2.22f, 0.02f, STEELC);                                           // антабка на прикладе
        vmSwivel(m, 2.90f, 0.62f, STEELC);                                            // антабка на цевье
        vmArm(m);
    }
    {   // 2: автомат
        VModel& m = VMS[2]; m.muz = 3.25f; m.mvKind = 0; m.mvScale = 1.f;
        vmAdd(m, -0.06f, 0.06f, 0.50f, 0.62f, 1.80f, 3.20f, STEELC);
        vmAdd(m, -0.14f, 0.14f, 0.25f, 0.62f, 0.30f, 1.80f, WOODC);
        for (int i = 0; i < 3; i++) vmAdd(m, -0.144f, 0.144f, 0.34f, 0.50f, 0.55f + 0.40f * i, 0.75f + 0.40f * i, DARKER);
        vmAdd(m, -0.15f, 0.15f, 0.20f, 0.75f, -0.80f, 0.30f, DARKC);
        vmAdd(m, -0.05f, 0.05f, 0.75f, 0.78f, -0.7f, 0.25f, STEELL);
        vmAdd(m, -0.10f, 0.10f, -0.70f, 0.25f, 0.00f, 0.40f, STEELC, -0.35f);
        vmAdd(m, -0.12f, 0.12f, -0.10f, 0.50f, -2.30f, -0.80f, WOODC);
        vmAdd(m, -0.07f, 0.07f, 0.49f, 0.63f, 3.20f, 3.28f, DARKER);
        vmAdd(m, -0.02f, 0.02f, 0.62f, 0.78f, 3.00f, 3.05f, STEELC);
        vmAdd(m, -0.136f, 0.136f, -0.75f, 0.10f, -0.55f, 0.00f, SKINC, -0.25f);
        vmGuard(m, -0.02f, 0.25f, -0.06f, 0.18f, DARKC);                              // спусковая скоба
        vmPostSight(m, 3.02f, 0.77f, 0.14f, DARKER);                                  // мушка (без зазора над стволом)
        vmNotchSight(m, -0.68f, 0.77f, 0.13f, DARKER);                                // целик (без зазора над планкой)
        vmAdd(m, -0.16f, -0.10f, 0.36f, 0.46f, -0.32f, -0.16f, STEELL);               // переводчик огня
        vmSwivel(m, 1.72f, 0.64f, DARKER);                                            // антабка у ствола
        vmAdd(m, -0.10f, 0.10f, -0.62f, 0.08f, 0.06f, 0.36f, DARKC);                  // магазин, верх
        vmAdd(m, -0.095f, 0.095f, -0.98f, -0.58f, 0.12f, 0.44f, DARKC);               // магазин, изогнутый низ
        vmArm(m);
    }
    {   // 4: ПП
        VModel& m = VMS[4]; m.muz = 2.44f; m.mvKind = 0; m.mvScale = 1.f;
        vmAdd(m, -0.09f, 0.09f, -1.00f, 0.28f, 0.55f, 0.90f, STEELC);
        vmAdd(m, -0.12f, 0.12f, -0.70f, 0.28f, -0.20f, 0.22f, DARKC, -0.25f);
        vmAdd(m, -0.14f, 0.14f, 0.28f, 0.72f, -0.30f, 1.60f, DARKC);
        vmAdd(m, -0.07f, 0.07f, 0.72f, 0.74f, -0.20f, 1.50f, STEELL);
        vmAdd(m, -0.146f, 0.146f, 0.50f, 0.66f, 0.30f, 0.90f, DARKER);
        for (int i = 0; i < 3; i++) vmAdd(m, -0.146f, 0.146f, 0.34f, 0.46f, 1.00f + 0.2f * i, 1.10f + 0.2f * i, DARKER);
        vmAdd(m, -0.06f, 0.06f, 0.46f, 0.64f, 1.60f, 2.40f, STEELC);
        vmAdd(m, -0.055f, 0.055f, 0.48f, 0.62f, 2.40f, 2.44f, DARKER);
        vmAdd(m, -0.02f, 0.02f, 0.72f, 0.84f, 2.20f, 2.26f, STEELC);
        vmAdd(m, -0.05f, 0.05f, 0.72f, 0.80f, 0.00f, 0.12f, STEELC);
        vmAdd(m, -0.02f, 0.02f, 0.40f, 0.46f, -1.60f, -0.30f, STEELL);
        vmAdd(m, -0.152f, 0.152f, -0.75f, 0.12f, -0.30f, 0.30f, SKINC, -0.25f);
        vmAdd(m, -0.176f, 0.176f, -0.60f, -0.36f, 0.20f, 0.44f, SKIND, -0.25f);
        vmAdd(m, -0.176f, 0.176f, -0.32f, -0.08f, 0.20f, 0.44f, SKIND, -0.25f);
        vmGuard(m, -0.02f, 0.28f, -0.05f, 0.15f, DARKC);                              // спусковая скоба
        vmAdd(m, -0.15f, -0.09f, 0.34f, 0.44f, 0.55f, 0.70f, STEELL);                 // переводчик огня
        vmSwivel(m, -0.95f, 0.44f, STEELC);                                           // антабка на прикладе
        vmArm(m);
    }
    {   // 5: снайперка
        VModel& m = VMS[5]; m.muz = 4.40f; m.mvKind = 0; m.mvScale = 1.f;
        vmAdd(m, -0.055f, 0.055f, 0.50f, 0.62f, 1.20f, 4.20f, STEELC);
        vmAdd(m, -0.13f, 0.13f, -0.35f, 0.40f, -2.60f, -0.90f, WOODC);
        vmAdd(m, -0.12f, 0.12f, 0.40f, 0.55f, -2.40f, -1.40f, WOODD);
        vmAdd(m, -0.14f, 0.14f, 0.22f, 0.72f, -0.90f, 1.20f, DARKC);
        vmAdd(m, -0.05f, 0.05f, 0.72f, 0.82f, 0.00f, 0.15f, STEELC);
        vmAdd(m, -0.05f, 0.05f, 0.72f, 0.82f, 1.00f, 1.15f, STEELC);
        vmAdd(m, -0.10f, 0.10f, 0.82f, 1.05f, -0.10f, 1.70f, DARKC);
        vmAdd(m, -0.12f, 0.12f, 0.80f, 1.07f, 1.70f, 2.10f, DARKC);
        vmAdd(m, -0.10f, 0.10f, 0.83f, 1.04f, 2.10f, 2.13f, LENSC);
        vmAdd(m, -0.03f, 0.03f, 1.05f, 1.12f, 0.80f, 0.95f, STEELC);
        vmAdd(m, -0.08f, 0.08f, 0.46f, 0.66f, 4.20f, 4.40f, DARKER);
        vmAdd(m, -0.11f, 0.11f, -0.60f, 0.22f, -0.70f, -0.30f, WOODC, -0.25f);
        vmAdd(m, -0.136f, 0.136f, -0.75f, 0.10f, -0.75f, -0.25f, SKINC, -0.25f);
        vmAdd(m, -0.16f, 0.16f, -0.60f, -0.30f, -0.75f, -0.40f, SKIND, -0.25f);
        vmAdd(m, -0.112f, 0.112f, 0.20f, 0.45f, 0.40f, 0.90f, SKIND);
        vmAdd(m, -0.03f, 0.03f, 1.08f, 1.22f, 0.42f, 0.50f, DARKER);                  // барабанчик прицела (высота)
        vmAdd(m, -0.16f, -0.10f, 0.92f, 1.00f, 0.60f, 0.68f, DARKER);                 // барабанчик прицела (боковой)
        vmGuard(m, -0.62f, -0.34f, -0.06f, 0.15f, DARKC);                             // спусковая скоба
        vmAdd(m, -0.14f, -0.08f, -0.95f, 0.35f, 1.05f, 1.12f, STEELC);                // сошка, левая нога
        vmAdd(m, 0.08f, 0.14f, -0.95f, 0.35f, 1.05f, 1.12f, STEELC);                  // сошка, правая нога
        vmSwivel(m, -2.50f, 0.32f, STEELC);                                           // антабка на прикладе
        vmArm(m);
    }
    {   // 6: пулемёт
        VModel& m = VMS[6]; m.muz = 3.65f; m.mvKind = 0; m.mvScale = 1.f;
        vmAdd(m, -0.06f, 0.06f, 0.50f, 0.62f, 1.80f, 3.62f, STEELC);
        vmAdd(m, -0.15f, 0.15f, 0.20f, 0.75f, -0.60f, 1.80f, DARKC);
        vmAdd(m, -0.12f, 0.12f, -0.05f, 0.45f, -2.35f, -0.60f, WOODC);
        vmAdd(m, -0.05f, 0.05f, 0.75f, 0.78f, -0.50f, 1.75f, STEELL);
        vmAdd(m, -0.17f, 0.17f, -0.55f, 0.15f, 0.65f, 1.35f, DARKER);              // ящик-магазин снизу
        vmAdd(m, -0.14f, -0.08f, -0.95f, 0.55f, 3.30f, 3.36f, STEELC);              // сошки: левая нога (вниз, к земле)
        vmAdd(m, 0.08f, 0.14f, -0.95f, 0.55f, 3.30f, 3.36f, STEELC);                // сошки: правая нога
        vmAdd(m, -0.07f, 0.07f, 0.46f, 0.66f, 3.60f, 3.65f, DARKER);
        vmAdd(m, -0.02f, 0.02f, 0.62f, 0.78f, -0.55f, -0.50f, STEELC);
        vmAdd(m, -0.136f, 0.136f, -0.75f, 0.10f, -0.55f, 0.00f, SKINC, -0.25f);
        vmGuard(m, -0.32f, -0.02f, -0.06f, 0.18f, DARKC);                             // спусковая скоба
        vmPostSight(m, 3.47f, 0.60f, 0.18f, DARKER);                                  // мушка (посажена прямо на ствол, не висит)
        vmNotchSight(m, -0.45f, 0.77f, 0.13f, DARKER);                                // целик (сдвинут на планку, без зазора)
        vmAdd(m, -0.03f, 0.03f, 0.78f, 1.05f, 1.55f, 1.62f, DARKC);                   // ручка переноски, стойка
        vmAdd(m, -0.03f, 0.03f, 0.78f, 1.05f, 2.00f, 2.07f, DARKC);                   // ручка переноски, стойка
        vmAdd(m, -0.03f, 0.03f, 1.00f, 1.06f, 1.55f, 2.07f, DARKC);                   // ручка переноски, перекладина
        vmSwivel(m, 1.75f, 0.64f, STEELC);                                            // антабка у ствола
        vmArm(m);
    }
    {   // 7: обрез
        VModel& m = VMS[7]; m.muz = 1.65f; m.mvKind = 0; m.mvScale = 1.f;
        vmAdd(m, -0.10f, -0.02f, 0.40f, 0.58f, 0.20f, 1.55f, DARKC);               // левый ствол
        vmAdd(m, 0.02f, 0.10f, 0.40f, 0.58f, 0.20f, 1.55f, DARKC);                 // правый ствол
        vmAdd(m, -0.15f, 0.15f, 0.15f, 0.70f, -0.35f, 0.30f, STEELC);
        vmAdd(m, -0.13f, 0.13f, 0.15f, 0.42f, 0.05f, 0.55f, WOODC);
        vmAdd(m, -0.12f, 0.12f, -0.85f, 0.20f, -0.65f, -0.10f, WOODD);
        vmAdd(m, -0.03f, 0.03f, 0.68f, 0.80f, -0.15f, 0.05f, STEELL);
        vmAdd(m, -0.11f, 0.11f, 0.38f, 0.60f, 1.53f, 1.57f, DARKER);
        vmAdd(m, -0.136f, 0.136f, -0.75f, 0.10f, -0.45f, 0.05f, SKINC, -0.25f);
        vmGuard(m, -0.06f, 0.20f, -0.06f, 0.14f, STEELC);                             // спусковая скоба (двойной спуск)
        vmAdd(m, -0.10f, -0.03f, 0.62f, 0.78f, 0.08f, 0.20f, DARKER);                 // левый курок
        vmAdd(m, 0.03f, 0.10f, 0.62f, 0.78f, 0.08f, 0.20f, DARKER);                   // правый курок
        vmAdd(m, -0.02f, 0.02f, 0.58f, 0.68f, 1.45f, 1.55f, DARKER);                  // мушка-обрубок на конце ствола
        vmArm(m);
    }
}

// ============================ ОРУЖИЕ: предрендер с фасками, материалами и тенями ============================
struct V3 { float x, y, z; };
static inline V3 v3(float x, float y, float z) { V3 r = {x, y, z}; return r; }
static inline V3 operator+(V3 a, V3 b) { return v3(a.x + b.x, a.y + b.y, a.z + b.z); }
static inline V3 operator-(V3 a, V3 b) { return v3(a.x - b.x, a.y - b.y, a.z - b.z); }
static inline V3 operator*(V3 a, float s) { return v3(a.x * s, a.y * s, a.z * s); }
static inline float dot3(V3 a, V3 b) { return a.x * b.x + a.y * b.y + a.z * b.z; }
static inline V3 norm3(V3 a) { float l = sqrtf(dot3(a, a)); if (l < 1e-8f) l = 1; return a * (1.f / l); }

enum { MT_DARK, MT_BLACK, MT_STEEL, MT_BRIGHT, MT_WOOD, MT_WOODD, MT_SKIN, MT_SKIND, MT_CLOTH, MT_CUFF, MT_LENS, MT_N };
struct MatDef { float kd, ks, shin, metal, bevel; };
static const MatDef MATS[MT_N] = {
    {0.85f, 0.55f, 42, 0.55f, 0.024f},   // тёмный металл
    {0.60f, 0.30f, 30, 0.35f, 0.020f},   // чёрный
    {0.75f, 0.75f, 70, 0.80f, 0.022f},   // сталь
    {0.75f, 0.95f, 90, 0.92f, 0.022f},   // светлый металл
    {1.00f, 0.20f, 14, 0.00f, 0.050f},   // дерево
    {1.00f, 0.16f, 12, 0.00f, 0.050f},   // тёмное дерево
    {1.00f, 0.14f, 10, 0.00f, 0.075f},   // кожа
    {1.00f, 0.12f, 10, 0.00f, 0.070f},   // кожа (тень)
    {1.00f, 0.04f, 6, 0.00f, 0.060f},    // ткань
    {1.00f, 0.06f, 8, 0.00f, 0.045f},    // манжета
    {0.35f, 1.00f, 100, 0.70f, 0.010f},  // линза
};
static int matOf(Col c) {
    struct K { unsigned char r, g, b; int m; };
    static const K ks[] = {{54, 56, 62, MT_DARK}, {20, 20, 24, MT_BLACK}, {105, 108, 118, MT_STEEL}, {160, 163, 176, MT_BRIGHT}, {125, 80, 42, MT_WOOD}, {84, 52, 26, MT_WOODD},
                           {205, 160, 125, MT_SKIN}, {186, 140, 106, MT_SKIND}, {48, 62, 84, MT_CLOTH}, {84, 102, 134, MT_CUFF}, {90, 170, 230, MT_LENS}};
    for (size_t i = 0; i < sizeof(ks) / sizeof(ks[0]); i++) if (ks[i].r == c.r && ks[i].g == c.g && ks[i].b == c.b) return ks[i].m;
    return MT_DARK;
}

// параметры камеры предрендера оружия
// параметры камеры предрендера оружия: вид сзади, ствол смотрит вперёд (к центру экрана)
// положение оружия на экране: правее (X) и ниже (Y) — меняй эти числа, чтобы сдвинуть
static const float VM_POS_LX = 27.f, VM_POS_LY = 46.f;     // горизонтально: вправо от центра, вниз от центра
static const float VM_POS_PX = 24.f, VM_POS_PY = 26.f;     // вертикально: вправо от центра, вверх от нижнего края
static float VM_F = 100.f, VM_GZ = 3.4f, VM_YAW = 0.02f, VM_DXO = 14.f, VM_DYO = 33.f, VM_SCALE = 1.4f;
static float UREF = 6.f;                 // масштаб предрендера (зависит от графики)

static float fakeEnv(V3 r) {         // условное окружение для бликов на металле: небо, земля, мягкий бокс-свет
    float t = r.y * 0.5f + 0.5f, s = std::max(0.f, std::min(1.f, (t - 0.35f) / 0.4f));
    float e = 0.10f + 0.55f * s * s * (3 - 2 * s);
    float bx = fabsf(r.x + 0.35f), by = fabsf(r.y - 0.45f);
    if (bx < 0.16f && by < 0.28f) e += 0.75f * (1 - bx / 0.16f) * (1 - by / 0.28f);
    if (fabsf(r.x - 0.55f) < 0.05f && r.y > 0.05f) e += 0.25f;
    return e;
}
static V3 shadeHit(int mat, Col base, V3 pl, V3 n, V3 rayDir, float shadow) {
    const MatDef& m = MATS[mat];
    static const V3 L1 = norm3(v3(-0.45f, 0.80f, -0.40f)), L2 = norm3(v3(0.70f, 0.15f, -0.60f));
    V3 alb = v3(base.r / 255.f, base.g / 255.f, base.b / 255.f), V = rayDir * -1.f;
    float tx = 1.f;
    if (mat == MT_WOOD || mat == MT_WOODD) {
        float g = vnoiseP(pl.z * 2.2f + 50, (pl.x + pl.y * 0.7f) * 34.f + 50, 71, 512), ring = 0.5f + 0.5f * sinf((pl.x + 0.6f * pl.y) * 26.f + g * 5.f);
        tx = 0.78f + 0.20f * g + 0.22f * ring;
    } else if (mat == MT_DARK || mat == MT_STEEL || mat == MT_BRIGHT || mat == MT_BLACK) {
        tx = 0.94f + 0.12f * vnoiseP(pl.x * 90 + 80, pl.y * 90 + 80 + pl.z * 4, 72, 512);
    } else if (mat == MT_SKIN || mat == MT_SKIND) {
        tx = 0.95f + 0.10f * vnoiseP(pl.x * 30 + 60, pl.z * 30 + pl.y * 30 + 60, 73, 512);
    } else if (mat == MT_CLOTH || mat == MT_CUFF) {
        tx = 0.90f + 0.08f * sinf(pl.x * 150.f) * sinf(pl.z * 150.f) + 0.06f * vnoiseP(pl.x * 20 + 40, pl.z * 20 + 40, 74, 512);
    }
    float nl1 = std::max(0.f, dot3(n, L1)) * shadow, nl2 = std::max(0.f, dot3(n, L2));
    float up = n.y * 0.5f + 0.5f;
    V3 amb = v3(0.20f + 0.16f * up, 0.21f + 0.18f * up, 0.26f + 0.24f * up);
    V3 diff = v3(alb.x * (amb.x + 0.95f * nl1 + 0.30f * nl2), alb.y * (amb.y + 0.92f * nl1 + 0.30f * nl2), alb.z * (amb.z + 0.88f * nl1 + 0.34f * nl2)) * (m.kd * tx);
    V3 H = norm3(L1 + V);
    float sp = powf(std::max(0.f, dot3(n, H)), m.shin) * m.ks * shadow;
    V3 R = rayDir - n * (2.f * dot3(rayDir, n));
    float env = fakeEnv(R);
    env += m.metal * 0.28f * (0.5f + 0.5f * sinf(pl.z * 3.2f + pl.x * 9.f));   // переливы света по металлу
    V3 col = diff * (1.f - m.metal * 0.62f) + v3(alb.x * 0.85f + 0.15f, alb.y * 0.85f + 0.15f, alb.z * 0.85f + 0.18f) * (env * m.metal * 0.85f * (0.55f + 0.45f * shadow));
    col = col + v3(1.f, 0.97f, 0.9f) * (sp * (0.55f + 0.5f * m.metal));
    float rim = powf(1.f - std::max(0.f, dot3(n, V)), 3.f) * 0.20f;
    if (mat == MT_SKIN || mat == MT_SKIND) col = col + v3(0.55f, 0.20f, 0.14f) * rim; else col = col + v3(0.35f, 0.42f, 0.6f) * rim;
    return col;
}

struct PBox { const VBox* b; int mat; int layer; float x0, y0, x1, y1; float lo[3], hi[3]; };
static bool slabHit(const float* o, const float* d, const float* lo, const float* hi, float* tOut, int* axOut, int* sgOut) {
    float tmin = -1e30f, tmax = 1e30f; int ax = 0, sg = 0;
    for (int i = 0; i < 3; i++) {
        if (fabsf(d[i]) < 1e-9f) { if (o[i] < lo[i] || o[i] > hi[i]) return false; continue; }
        float inv = 1.f / d[i], t1 = (lo[i] - o[i]) * inv, t2 = (hi[i] - o[i]) * inv;
        if (t1 > t2) std::swap(t1, t2);
        if (t1 > tmin) { tmin = t1; ax = i; sg = d[i] > 0 ? -1 : 1; }
        if (t2 < tmax) tmax = t2;
        if (tmin > tmax) return false;
    }
    if (tmin < 1e-4f) return false;
    *tOut = tmin; *axOut = ax; *sgOut = sg; return true;
}

struct WBuild {
    bool active = false; int wi = 0, w = 0, h = 0, py = 0, packL = 0;
    float F = 0, gz = 0, cy_ = 1, sy_ = 0, wx0 = 0, wy0 = 0, dxo = 0, dyo = 0;
    V3 og, L1g; std::vector<PBox> boxes; std::vector<float> cr[3], cg[3], cb[3], ca[3];
};
static WBuild WB;

static void wbBegin(int wi) {
    initVModels();
    WBuild& B = WB; B = WBuild(); B.active = true; B.wi = wi;
    VSprite& S = VSPR[wi]; const VModel& vm = VMS[wi];
    B.F = VM_F * UREF; B.gz = VM_GZ; const float yaw = VM_YAW; B.cy_ = cosf(yaw); B.sy_ = sinf(yaw);
    B.dxo = VM_DXO * UREF; B.dyo = VM_DYO * UREF;
    const float gx = B.dxo / B.F * B.gz, gy = -B.dyo / B.F * B.gz;
    float minx = 1e9f, miny = 1e9f, maxx = -1e9f, maxy = -1e9f;
    for (int i = 0; i < vm.n; i++) {
        const VBox& b = vm.b[i];
        PBox pb; pb.b = &b; pb.mat = matOf(b.col);
        pb.layer = b.mv ? 2 : ((pb.mat == MT_CLOTH || pb.mat == MT_CUFF) ? 1 : 0);
        pb.lo[0] = b.x0; pb.lo[1] = b.y0; pb.lo[2] = b.z0; pb.hi[0] = b.x1; pb.hi[1] = b.y1; pb.hi[2] = b.z1;
        float bx0 = 1e9f, by0 = 1e9f, bx1 = -1e9f, by1 = -1e9f;
        for (int a = 0; a < 2; a++) for (int c = 0; c < 2; c++) for (int d = 0; d < 2; d++) {
            float xs = a ? b.x1 : b.x0, ys = c ? b.y1 : b.y0, zs = d ? b.z1 : b.z0;
            float zz = zs + b.sh * (b.y1 - ys), rx = xs * B.cy_ - zz * B.sy_, rz = xs * B.sy_ + zz * B.cy_;
            float X = gx + rx, Y = gy + ys, Z = B.gz + rz;
            if (Z < 0.15f) continue;
            float sx = B.F * X / Z, sy = -B.F * Y / Z;
            bx0 = std::min(bx0, sx); bx1 = std::max(bx1, sx); by0 = std::min(by0, sy); by1 = std::max(by1, sy);
        }
        pb.x0 = bx0 - 2; pb.x1 = bx1 + 2; pb.y0 = by0 - 2; pb.y1 = by1 + 2;
        minx = std::min(minx, bx0); maxx = std::max(maxx, bx1); miny = std::min(miny, by0); maxy = std::max(maxy, by1);
        B.boxes.push_back(pb);
    }
    maxx = std::min(maxx, B.dxo + 62.f * UREF); maxy = std::min(maxy, B.dyo + 36.f * UREF);   // дальше края экрана рука не нужна
    const float margin = 8.f;
    B.wx0 = floorf(minx - margin); B.wy0 = floorf(miny - margin);
    B.w = std::max(16, std::min(1100, (int)ceilf(maxx + margin - B.wx0))); B.h = std::max(16, std::min(900, (int)ceilf(maxy + margin - B.wy0)));
    S.w = B.w; S.h = B.h; S.ax = B.dxo - B.wx0; S.ay = B.dyo - B.wy0;
    auto projPt = [&](float xs, float ys, float zs, float* ox, float* oy) {
        float rx = xs * B.cy_ - zs * B.sy_, rz = xs * B.sy_ + zs * B.cy_;
        float X = gx + rx, Y = gy + ys, Z = B.gz + rz; *ox = B.F * X / Z - B.wx0; *oy = -B.F * Y / Z - B.wy0;
    };
    projPt(0.f, 0.52f, vm.muz + 0.05f, &S.mx, &S.my);
    projPt(0.16f, 0.58f, vm.muz * 0.42f, &S.ex, &S.ey);
    {   // запястье и вектор сдвига подвижной части (0.4 ед. назад вдоль ствола)
        float bestV = -1; const VBox* hand = NULL;
        for (int i = 0; i < vm.n; i++) {
            int m = matOf(vm.b[i].col);
            if (m != MT_SKIN && m != MT_SKIND) continue;
            const VBox& q = vm.b[i]; float v = (q.x1 - q.x0) * (q.y1 - q.y0) * (q.z1 - q.z0);
            if (v > bestV) { bestV = v; hand = &q; }
        }
        if (hand) { float xs = (hand->x0 + hand->x1) / 2, ys = hand->y0, zs = hand->z0 + hand->sh * (hand->y1 - ys); projPt(xs, ys, zs, &S.wx, &S.wy); }
        else { S.wx = S.ax; S.wy = S.ay; }
        float ax_, ay_, bx_, by_; projPt(0.f, 0.52f, 1.0f, &ax_, &ay_); projPt(0.f, 0.52f, 0.6f, &bx_, &by_);
        S.mvx = bx_ - ax_; S.mvy = by_ - ay_;
    }
    V3 v = v3(-gx, -gy, -B.gz);
    B.og = v3(v.x * B.cy_ + v.z * B.sy_, v.y, -v.x * B.sy_ + v.z * B.cy_);
    static const V3 L1 = norm3(v3(-0.45f, 0.80f, -0.40f));
    B.L1g = v3(L1.x * B.cy_ + L1.z * B.sy_, L1.y, -L1.x * B.sy_ + L1.z * B.cy_);
    size_t n = (size_t)B.w * B.h;
    for (int l = 0; l < 3; l++) { B.cr[l].assign(n, 0); B.cg[l].assign(n, 0); B.cb[l].assign(n, 0); B.ca[l].assign(n, 0); }
}

static void wbRows(int rows) {
    WBuild& B = WB;
    const V3 L1 = norm3(v3(-0.45f, 0.80f, -0.40f));
    auto toG = [&](V3 d) { return v3(d.x * B.cy_ + d.z * B.sy_, d.y, -d.x * B.sy_ + d.z * B.cy_); };
    static const float SO[4][2] = {{0.25f, 0.25f}, {0.75f, 0.25f}, {0.25f, 0.75f}, {0.75f, 0.75f}};
    struct Hit { float t; int bi, ax, sg; float o[3], d[3]; };
    for (int r = 0; r < rows && B.py < B.h; r++, B.py++) {
        int py = B.py;
        for (int px = 0; px < B.w; px++) {
            float acc[3][3] = {{0, 0, 0}, {0, 0, 0}, {0, 0, 0}}, cov[3] = {0, 0, 0};
            for (int s = 0; s < 4; s++) {
                float sxp = B.wx0 + px + SO[s][0], syp = B.wy0 + py + SO[s][1];
                V3 dcam = norm3(v3(sxp / B.F, -syp / B.F, 1.f)), dg = toG(dcam);
                Hit best[3]; for (int l = 0; l < 3; l++) { best[l].bi = -1; best[l].t = 1e30f; }
                for (size_t i = 0; i < B.boxes.size(); i++) {
                    const PBox& pb = B.boxes[i];
                    if (sxp < pb.x0 || sxp > pb.x1 || syp < pb.y0 || syp > pb.y1) continue;
                    float sh = pb.b->sh, o[3] = {B.og.x, B.og.y, B.og.z - sh * (pb.b->y1 - B.og.y)}, d[3] = {dg.x, dg.y, dg.z + sh * dg.y};
                    float t; int ax, sg;
                    Hit& h = best[pb.layer];
                    if (slabHit(o, d, pb.lo, pb.hi, &t, &ax, &sg) && t < h.t) { h.t = t; h.bi = (int)i; h.ax = ax; h.sg = sg; for (int k = 0; k < 3; k++) { h.o[k] = o[k]; h.d[k] = d[k]; } }
                }
                for (int ly = 0; ly < 3; ly++) {
                    const Hit& h = best[ly];
                    if (h.bi < 0) continue;
                    const PBox& pb = B.boxes[h.bi]; const VBox& b = *pb.b;
                    float pl[3] = {h.o[0] + h.d[0] * h.t, h.o[1] + h.d[1] * h.t, h.o[2] + h.d[2] * h.t};
                    float nl[3] = {0, 0, 0}; nl[h.ax] = (float)h.sg;
                    float minDim = std::min(b.x1 - b.x0, std::min(b.y1 - b.y0, b.z1 - b.z0)), rEff = std::min(MATS[pb.mat].bevel, 0.5f * minDim);
                    for (int k = 0; k < 3; k++) {
                        if (k == h.ax) continue;
                        float dlo = pl[k] - pb.lo[k], dhi = pb.hi[k] - pl[k], dd = std::min(dlo, dhi);
                        if (dd < rEff) { float t = 1.f - dd / rEff; nl[k] += (dlo < dhi ? -1.f : 1.f) * t * 1.05f; }
                    }
                    V3 ng = norm3(v3(nl[0], nl[1] + b.sh * nl[2], nl[2]));
                    V3 nc = norm3(v3(ng.x * B.cy_ - ng.z * B.sy_, ng.y, ng.x * B.sy_ + ng.z * B.cy_));
                    float shadow = 1.f;
                    if (dot3(nc, L1) > 0.02f) {
                        V3 hp = B.og + dg * h.t, ho = hp + toG(nc) * 0.006f;
                        int occ = 0;
                        for (int j = 0; j < 2; j++) {
                            V3 dl = norm3(B.L1g + v3(j ? 0.06f : -0.06f, 0.02f, 0.f));
                            bool hit = false;
                            for (size_t i = 0; i < B.boxes.size() && !hit; i++) {
                                const PBox& q = B.boxes[i]; float sh = q.b->sh, o[3] = {ho.x, ho.y, ho.z - sh * (q.b->y1 - ho.y)}, d[3] = {dl.x, dl.y, dl.z + sh * dl.y};
                                float t; int ax, sg;
                                if (slabHit(o, d, q.lo, q.hi, &t, &ax, &sg) && t < 3.f) hit = true;
                            }
                            if (hit) occ++;
                        }
                        shadow = 1.f - 0.62f * occ / 2.f;
                    }
                    Col bcol = b.col;
                    int skinId = weaponSkin[B.wi];
                    if (skinId != 0 && pb.mat != MT_SKIN && pb.mat != MT_SKIND && pb.mat != MT_CLOTH && pb.mat != MT_CUFF && pb.mat != MT_LENS) {
                        const SkinDef& sk = SKINS[skinId]; float st = sk.strength;
                        bcol = C((int)(b.col.r * (1 - st) + sk.tint.r * st), (int)(b.col.g * (1 - st) + sk.tint.g * st), (int)(b.col.b * (1 - st) + sk.tint.b * st), b.col.a);
                    }
                    V3 col = shadeHit(pb.mat, bcol, v3(pl[0], pl[1], pl[2]), nc, dcam, shadow);
                    acc[ly][0] += col.x; acc[ly][1] += col.y; acc[ly][2] += col.z; cov[ly] += 1.f;
                }
            }
            size_t id = (size_t)py * B.w + px;
            for (int l = 0; l < 3; l++) {
                if (cov[l] > 0) { B.cr[l][id] = acc[l][0] / cov[l]; B.cg[l][id] = acc[l][1] / cov[l]; B.cb[l][id] = acc[l][2] / cov[l]; }
                B.ca[l][id] = cov[l] / 4.f;
            }
        }
    }
}

static void wbPack(int w, int h, const std::vector<float>& R, const std::vector<float>& G_, const std::vector<float>& Bc, const std::vector<float>& A, std::vector<u32>& out) {
    out.assign((size_t)w * h, 0);
    auto tone = [](float v) { v = v / (1.f + 0.18f * v); return (int)std::max(0.f, std::min(255.f, powf(std::max(0.f, v), 0.92f) * 255.f * 1.12f)); };
    for (int y = 0; y < h; y++)
        for (int x = 0; x < w; x++) {
            size_t id = (size_t)y * w + x;
            if (A[id] <= 0) continue;
            float k = 1.f;
            if (A[id] > 0.3f) {
                bool edge = false;
                for (int dy = -2; dy <= 2 && !edge; dy++) for (int dx = -2; dx <= 2 && !edge; dx++) {
                    int xx = x + dx, yy = y + dy;
                    if (xx < 0 || yy < 0 || xx >= w || yy >= h || A[(size_t)yy * w + xx] < 0.05f) edge = true;
                }
                if (edge) k = 0.55f;
            }
            out[id] = PX(C(tone(R[id] * k), tone(G_[id] * k), tone(Bc[id] * k), (int)(std::min(1.f, A[id]) * 255)));
        }
}
static bool wbFinishStep() {          // упаковка спрайта по одному слою за вызов (а не всё сразу) — чтобы не было одного долгого кадра
    WBuild& B = WB; VSprite& S = VSPR[B.wi]; int w = B.w, h = B.h, l = B.packL;
    wbPack(w, h, B.cr[l], B.cg[l], B.cb[l], B.ca[l], S.pxl[l]);
    if (S.texl[l]) SDL_DestroyTexture(S.texl[l]);
    S.texl[l] = makeTexSmooth(S.pxl[l], w, h);
    B.cr[l].clear(); B.cg[l].clear(); B.cb[l].clear(); B.ca[l].clear();
    if (++B.packL < 3) return false;
    S.ready = true;
    B.active = false; B.boxes.clear();
    return true;
}
static void wbFinish() { while (!wbFinishStep()) {} }
static void setWeaponQuality() {       // размер предрендера зависит от графики; при смене пересобираем оружие
    static const float QU[3] = {4.6f, 6.5f, 8.f};
    float nu = QU[std::max(0, std::min(2, quality))];
    if (fabsf(nu - UREF) < 0.01f) return;
    UREF = nu; WB.active = false;
    for (int i = 0; i < NW; i++) { VSPR[i].ready = false; for (int l = 0; l < 3; l++) if (VSPR[i].texl[l]) { SDL_DestroyTexture(VSPR[i].texl[l]); VSPR[i].texl[l] = NULL; } }
}
static void renderWeaponSprite(int wi) { wbBegin(wi); while (WB.py < WB.h) wbRows(64); wbFinish(); }
static void invalidateWeaponSprite(int wi) {      // пересобрать спрайт оружия (например, после смены скина)
    if (WB.active && WB.wi == wi) WB.active = false;
    VSPR[wi].ready = false;
    for (int l = 0; l < 3; l++) { if (VSPR[wi].texl[l]) { SDL_DestroyTexture(VSPR[wi].texl[l]); VSPR[wi].texl[l] = NULL; } }
}

struct Casing { float x, y, vx, vy, life, rot, vr; };
static std::vector<Casing> casings;
struct Smoke { float x, y, vx, vy, life, maxl, size; };
static std::vector<Smoke> smokes;

static void ensureWeaponSprite(int wi) {
    if (VSPR[wi].ready) return;
    if (WB.active && WB.wi == wi) { while (WB.py < WB.h) wbRows(64); wbFinish(); return; }
    WB.active = false; renderWeaponSprite(wi);
}
static void prerenderStep(Uint32 budgetMs = 10) {      // готовим оружие в фоне маленькими порциями (чтобы меню не подвисало)
    if (!WB.active) { for (int i = 0; i < NW; i++) if (!VSPR[i].ready) { wbBegin(i); break; } }
    if (!WB.active) return;
    Uint32 t0 = SDL_GetTicks();
    while (WB.py < WB.h && SDL_GetTicks() - t0 < budgetMs) wbRows(2);
    if (WB.py >= WB.h) wbFinishStep();
}

static void prerenderPrefer(int wi, Uint32 budgetMs) {      // строим спрайт нужного оружия частями, кадр не подвисает
    if (VSPR[wi].ready) return;
    if (!WB.active || WB.wi != wi) { WB.active = false; wbBegin(wi); }
    Uint32 t0 = SDL_GetTicks();
    while (WB.py < WB.h && SDL_GetTicks() - t0 < budgetMs) wbRows(1);
    if (WB.py >= WB.h) wbFinishStep();
}

static void drawViewmodel() {
    int wi = std::max(0, std::min(NW - 1, P->weapon));
    if (!VSPR[wi].ready) prerenderPrefer(wi, 6);   // пока строится — просто не рисуем
    VSprite& S = VSPR[wi];
    if (!S.ready || !S.texl[0]) return;
    const VModel& vm = VMS[wi];
    float k = U / UREF * VM_SCALE;
    float offx = (portrait ? VM_POS_PX : VM_POS_LX) * U, basey = portrait ? H - VM_POS_PY * U : H / 2.f + VM_POS_LY * U;   // положение рукояти на экране (в единицах U)
    float ox = W / 2.f + offx, oy = basey;
    static const float RS[NW] = {1.f, 1.7f, 0.6f, 1.5f, 0.45f, 2.0f, 0.9f, 2.3f};       // сила отдачи по оружию
    float r = fireAnim, t = 1.f - r, r2 = r * r * RS[wi];
    float tx = 0, ty = 0, ang = 0, sc = 1.f;
    if (P->bob > 0) { tx += sinf(P->bob * 7.f) * 1.3f * U; ty += fabsf(cosf(P->bob * 7.f)) * 1.3f * U; }
    ty += P->jumpZ * U * 1.0f; ang += P->jumpV * 0.5f;   // оружие чуть отстаёт при взлёте/падении
    tx += r2 * 1.7f * U; ty += r2 * 3.4f * U; ang += r2 * 5.5f; sc += r2 * 0.055f;
    if (P->reload > 0) {
        float wr = WEAP[wi].reload, prog = std::min(1.f, std::max(0.f, (wr - P->reload) / wr)), sn = sinf(prog * 3.14159f);
        ty += 24.f * U * sn; tx += 6.f * U * sn; ang += 26.f * sn;
    }
    float amt = 0;                      // смещение подвижной части: 0..1
    if (r > 0) {
        if (vm.mvKind == 1) amt = t < 0.22f ? t / 0.22f : powf(std::max(0.f, 1.f - (t - 0.22f) / 0.78f), 2.f);
        else if (vm.mvKind == 2 && t > 0.35f) { float p = (t - 0.35f) / 0.55f; if (p < 1.f) amt = sinf(p * 3.14159f); }
    }
    amt *= vm.mvScale;
    float ck = k * sc, cx = S.ax * ck, cy = S.ay * ck;
    float ca_ = cosf(ang * 3.14159f / 180.f), sa_ = sinf(ang * 3.14159f / 180.f);
    float wrx = (S.wx - S.ax) * ck, wry = (S.wy - S.ay) * ck;
    float shx = wrx * ca_ - wry * sa_ - wrx, shy = wrx * sa_ + wry * ca_ - wry;
    SDL_Rect dst = {(int)(ox + tx - cx), (int)(oy + ty - cy), (int)(S.w * ck), (int)(S.h * ck)};
    if (S.texl[1]) { SDL_Rect d2 = dst; d2.x += (int)shx; d2.y += (int)shy; SDL_RenderCopy(ren, S.texl[1], NULL, &d2); }      // рукав: не поворачивается
    SDL_Point center = {(int)cx, (int)cy};
    SDL_RenderCopyEx(ren, S.texl[0], NULL, &dst, ang, &center, SDL_FLIP_NONE);                                                  // оружие и кисть
    if (S.texl[2]) {                                                                                                            // затвор / цевьё
        float dvx = S.mvx * ck * amt, dvy = S.mvy * ck * amt;
        SDL_Rect d3 = dst; d3.x += (int)(dvx * ca_ - dvy * sa_); d3.y += (int)(dvx * sa_ + dvy * ca_);
        SDL_RenderCopyEx(ren, S.texl[2], NULL, &d3, ang, &center, SDL_FLIP_NONE);
    }
    auto toScreen = [&](float sx, float sy, float* X, float* Y) {
        float rx = (sx - S.ax) * ck, ry = (sy - S.ay) * ck;
        *X = ox + tx + rx * ca_ - ry * sa_; *Y = oy + ty + rx * sa_ + ry * ca_;
    };
    if (shotEvent) {                 // гильзы и дым в момент выстрела
        shotEvent = false;
        if (wi != 1 && wi != 3 && wi != 5) {
            Casing c; toScreen(S.ex, S.ey, &c.x, &c.y);
            c.vx = rr(4.f, 8.f) * U; c.vy = -rr(5.f, 9.f) * U; c.life = 0.7f; c.rot = rr(0.f, 6.f); c.vr = rr(-14.f, 14.f);
            if (casings.size() < 40) casings.push_back(c);
        }
        float mx0, my0; toScreen(S.mx, S.my, &mx0, &my0);
        int ns = wi == 1 ? 7 : (wi == 5 ? 6 : 3);
        for (int i = 0; i < ns && smokes.size() < 60; i++) {
            Smoke sm; sm.x = mx0 + rr(-0.6f, 0.6f) * U; sm.y = my0 + rr(-0.6f, 0.6f) * U; sm.vx = rr(-2.5f, 2.f) * U; sm.vy = -rr(3.f, 7.f) * U; sm.maxl = sm.life = rr(0.5f, 0.95f); sm.size = rr(0.8f, 1.5f) * U;
            smokes.push_back(sm);
        }
    }
    for (size_t i = 0; i < casings.size();) {
        Casing& c = casings[i]; c.life -= gDt; c.vy += 34.f * U * gDt; c.x += c.vx * gDt; c.y += c.vy * gDt; c.rot += c.vr * gDt;
        if (c.life <= 0 || c.y > H + 20) { casings[i] = casings.back(); casings.pop_back(); continue; }
        float al = std::min(1.f, c.life / 0.25f), cs = fabsf(sinf(c.rot)) * 0.5f + 0.5f;
        fillRect(c.x - 0.25f * U, c.y - 0.25f * U * cs, 0.55f * U, 0.32f * U + 0.3f * U * cs, C(224, 178, 66, (int)(255 * al)));
        i++;
    }
    for (size_t i = 0; i < smokes.size();) {
        Smoke& sm = smokes[i]; sm.life -= gDt;
        if (sm.life <= 0) { smokes[i] = smokes.back(); smokes.pop_back(); continue; }
        sm.x += sm.vx * gDt; sm.y += sm.vy * gDt; sm.vx *= 0.97f; sm.vy *= 0.96f; float a = sm.life / sm.maxl, sz = sm.size * (1.8f - a);
        fillCircle(sm.x, sm.y, sz, C(150, 155, 170, (int)(70 * a)));
        i++;
    }
    if (P->flash > 0) {
        float mx, my; toScreen(S.mx, S.my, &mx, &my);
        float kick = P->flash / 0.07f;
        float rr0 = 63.f * U / (4.2f + vm.muz) * (0.7f + 0.6f * kick) * VM_SCALE, sx[12], sy[12];
        for (int i = 0; i < 12; i++) { float a = i * 3.14159f / 6 + kick * 0.4f, rr_ = i % 2 == 0 ? rr0 * (0.85f + 0.3f * ((i / 2) % 2)) : rr0 * 0.40f; sx[i] = mx + cosf(a) * rr_; sy[i] = my + sinf(a) * rr_; }
        fillCircle(mx, my, rr0 * 1.5f, C(255, 160, 50, 14)); fillCircle(mx, my, rr0 * 1.05f, C(255, 175, 60, 26)); fillCircle(mx, my, rr0 * 0.75f, C(255, 190, 70, 44));
        for (int i = 0; i < 12; i++) { float tx3[3] = {mx, sx[i], sx[(i + 1) % 12]}, ty3[3] = {my, sy[i], sy[(i + 1) % 12]}; fillPoly(tx3, ty3, 3, C(255, 205, 70, 230)); }
        fillCircle(mx, my, std::max(2.f, rr0 * 0.38f), C(255, 250, 215));
    }
}

// ============================ HUD / ЭКРАНЫ ============================
static SDL_Texture* mmTex = NULL;
static void clearBtnCache();
static void drawBar(float x, float y, float w, float h, float frac, Col c) {
    fillRect(x, y, w, h, C(18, 18, 24, 230));
    float fw = w * std::max(0.f, std::min(1.f, frac));
    fillRect(x, y, fw, h, c);
    fillRect(x, y, fw, h * 0.42f, C(255, 255, 255, 55));
    fillRect(x, y + h * 0.8f, fw, h * 0.2f, C(0, 0, 0, 60));
    frameRect(x, y, w, h, 1, C(255, 255, 255, 200));
}
static void drawMinimap() {
    int px = std::max(2, (int)(std::min(W, H) * 0.30f / N));
    float ox = (float)(W - N * px - (int)(2 * U)), oy = 2 * U;
    SDL_SetRenderDrawBlendMode(ren, SDL_BLENDMODE_BLEND);
    if (mmDirty || !mmTex) {          // карта перерисовывается только при изменении стен
        int D = N * px; std::vector<u32> pix((size_t)D * D, PX(C(0, 0, 0, 120)));
        for (int i = 0; i < N * N; i++) {
            int c = G[i]; if (!c) continue;
            Col col = c == 1 ? C(140, 140, 150) : (c == 3 ? C(40, 120, 55) : C(200, 130, 50));
            for (int yy = 0; yy < px; yy++) for (int xx = 0; xx < px; xx++) pix[(size_t)((i / N) * px + yy) * D + (i % N) * px + xx] = PX(col);
        }
        if (mmTex) SDL_DestroyTexture(mmTex);
        mmTex = makeTex(pix, D, D); mmDirty = false;
    }
    if (mmTex) { SDL_Rect mr = {(int)ox, (int)oy, N * px, N * px}; SDL_RenderCopy(ren, mmTex, NULL, &mr); }
    for (size_t i = 0; i < zombies.size(); i++) fillRect(ox + (int)(zombies[i].x * px) - 1, oy + (int)(zombies[i].y * px) - 1, 3, 3, C(255, 50, 50));
    for (size_t i = 0; i < crates.size(); i++) fillRect(ox + (int)(crates[i].x * px) - 1, oy + (int)(crates[i].y * px) - 1, 2, 2, C(90, 200, 255));
    for (std::map<int, Player>::iterator it = players.begin(); it != players.end(); ++it) {
        Player& p = it->second; if (&p == P || p.dead) continue;
        fillRect(ox + p.x * px - 2, oy + p.y * px - 2, 4, 4, PCOL[p.id % 4]);
    }
    fillRect(ox + P->x * px - 2, oy + P->y * px - 2, 4, 4, C(255, 255, 0));
    float ax = ox + P->x * px, ay = oy + P->y * px;
    setCol(C(255, 255, 0)); SDL_RenderDrawLine(ren, (int)ax, (int)ay, (int)(ax + cosf(P->ang) * px * 3), (int)(ay + sinf(P->ang) * px * 3));
}
static void stickVec(const Touch& t, float* vx, float* vy) {
    float R = 14 * U; *vx = (t.x - t.ox) / R; *vy = (t.y - t.oy) / R;
    float m = hypotf(*vx, *vy);
    if (m > 1) { *vx /= m; *vy /= m; }
    if (m < 0.12f) { *vx = 0; *vy = 0; }
}
static std::map<long, SDL_Texture*> btnTexCache;
static void clearBtnCache() { for (std::map<long, SDL_Texture*>::iterator it = btnTexCache.begin(); it != btnTexCache.end(); ++it) if (it->second) SDL_DestroyTexture(it->second); btnTexCache.clear(); }
static SDL_Texture* getBtnTex(int i, bool held) {
    long key = ((long)(int)BTN[i].r << 8) | (i << 1) | (held ? 1 : 0);
    std::map<long, SDL_Texture*>::iterator it = btnTexCache.find(key);
    if (it != btnTexCache.end()) return it->second;
    int R = (int)BTN[i].r, D = 2 * R + 2; float th = std::max(2.f, U * 0.35f);
    std::vector<u32> px((size_t)D * D, 0);
    Col bc = BCOL[i]; float a0 = held ? 190.f : 95.f, hl = held ? 22.f : 36.f;
    for (int y = 0; y < D; y++)
        for (int x = 0; x < D; x++) {
            float dx = x + 0.5f - D / 2.f, dy = y + 0.5f - D / 2.f, d = sqrtf(dx * dx + dy * dy);
            float edge = std::max(0.f, std::min(1.f, R - d + 0.5f));
            if (edge <= 0.f) continue;
            float r = bc.r, g = bc.g, b = bc.b, a = a0;
            float hx = dx + R * 0.16f, hy = dy + R * 0.30f, hd = sqrtf(hx * hx + hy * hy);
            if (hd < R * 0.56f) { float t = hl / 255.f; r += (255 - r) * t; g += (255 - g) * t; b += (255 - b) * t; a = a + (255 - a) * t * 0.5f; }
            if (d > R - th) { float t = 200.f / 255.f; r += (255 - r) * t; g += (255 - g) * t; b += (255 - b) * t; a = a + (255 - a) * t; }
            px[(size_t)y * D + x] = PX(C((int)r, (int)g, (int)b, (int)(a * edge)));
        }
    SDL_Texture* t = makeTexSmooth(px, D, D);
    btnTexCache[key] = t;
    return t;
}
static void drawButtons(bool all = false) {
    for (int i = 0; i < NB; i++) {
        if (i == B_START && !prep && !all) continue;
        if (i == B_AUTO) continue;               // перенесено в настройки
        bool held = false;
        for (size_t t = 0; t < touches.size(); t++) if (touches[t].role == 1 && touches[t].btn == i) held = true;
        SDL_Texture* bt = getBtnTex(i, held);
        if (bt) { int R = (int)BTN[i].r, D = 2 * R + 2; SDL_Rect br = {(int)(BTN[i].cx - D / 2.f), (int)(BTN[i].cy - D / 2.f), D, D}; SDL_RenderCopy(ren, bt, NULL, &br); }
        if (i == B_AUTO) {
            float lh7 = textH(FS());
            drawText(BLABEL[i], BTN[i].cx, BTN[i].cy - lh7 * 1.15f, FS(), C(255, 255, 255), A_TC, BTN[i].r * 1.7f, false);
            drawText(P->autoF ? "ВКЛ" : "ВЫКЛ", BTN[i].cx, BTN[i].cy + lh7 * 0.15f, FS(), C(255, 255, 255), A_TC, BTN[i].r * 1.7f, false);
        } else if (i == B_FIRE && mode == M_PLAY) {
            std::string ammo = P->reload > 0 ? "ПЕРЕЗАРЯДКА" : fmt("%d/%d", P->ammo[P->weapon], mag_size(*P, P->weapon));
            drawText(BLABEL[i], BTN[i].cx, BTN[i].cy - textH(FM()) * 0.95f - 2, FS(), C(255, 255, 255), A_TC, BTN[i].r * 1.5f, false);
            drawText(ammo, BTN[i].cx, BTN[i].cy + 2, FM(), P->reload > 0 ? C(255, 220, 120) : C(255, 255, 255), A_TC, BTN[i].r * 1.6f, false);
        } else if ((i == B_GREN || i == B_STUN) && mode == M_PLAY) {
            int cnt = P->gren[i == B_GREN ? 0 : 1];
            drawText(BLABEL[i], BTN[i].cx, BTN[i].cy - textH(FS()) * 1.05f, FS(), C(255, 255, 255), A_TC, BTN[i].r * 1.8f, false);
            drawText(fmt("X%d", cnt), BTN[i].cx, BTN[i].cy + 1, FM(), cnt > 0 ? C(255, 255, 255) : C(255, 120, 110), A_TC, BTN[i].r * 1.6f, false);
        } else drawText(BLABEL[i], BTN[i].cx, BTN[i].cy, FS(), C(255, 255, 255), A_C, BTN[i].r * 1.7f, false);
    }
}
static SDL_Rect tutBtnRect() {
    float pw = portrait ? 0.94f * W : 0.70f * W, ph = portrait ? 78 * U : 64 * U, bw = 30 * U, bh = 8.5f * U;
    SDL_Rect r = {(int)(W / 2.f - bw / 2), (int)(H / 2.f + ph / 2 - bh - 2 * U), (int)bw, (int)bh}; (void)pw; return r;
}
static void drawTutorial() {
    float pw = portrait ? 0.94f * W : 0.70f * W, ph = portrait ? 78 * U : 64 * U, px = (W - pw) / 2, py = H / 2.f - ph / 2;
    fillRect(px, py, pw, ph, C(6, 8, 18, 215)); frameRect(px, py, pw, ph, 2, C(255, 255, 255, 190));
    drawText("КАК ИГРАТЬ", W / 2.f, py + 2 * U, FM(), C(255, 215, 90), A_TC, pw - 4 * U);
    static const char* L[8] = {"ЛЕВЫЙ ПАЛЕЦ - ХОДИТЬ", "ПРАВЫЙ - ПОВОРОТ И ВЗГЛЯД ВВЕРХ-ВНИЗ", "ОГОНЬ - СТРЕЛЬБА, АВТО - САМА СТРЕЛЯЕТ", "В ГОЛОВУ БЬЁТ В 2.5 РАЗА СИЛЬНЕЕ",
                               "СТРОЙ - БАРРИКАДЫ В ПРОЁМАХ ЗА ЛОМ", "ЯЩИКИ ДАЮТ ЛОМ И АПТЕЧКИ", "МАГАЗИН - НОВОЕ ОРУЖИЕ", "СТАРТ - НАЧАТЬ ВОЛНУ РАНЬШЕ"};
    float ly = py + 2 * U + textH(FM()) + 3.f * U, step = (ph - 2 * U - textH(FM()) - 3.f * U - 13 * U) / 8.f;
    for (int i = 0; i < 8; i++) drawText(L[i], W / 2.f, ly + i * step, FS(), i == 3 ? C(255, 215, 90) : C(235, 240, 255), A_TC, pw - 4 * U);
    SDL_Rect r = tutBtnRect();
    fillRect((float)r.x, (float)r.y, (float)r.w, r.h * 0.5f, C(70, 132, 90)); fillRect((float)r.x, r.y + r.h * 0.5f, (float)r.w, r.h * 0.5f + 1, C(44, 84, 58));
    frameRect((float)r.x, (float)r.y, (float)r.w, (float)r.h, 2, C(255, 255, 255, 210));
    drawText("ПОНЯТНО", r.x + r.w / 2.f, r.y + r.h / 2.f, FM(), C(255, 255, 255), A_C, r.w * 0.9f);
}
static SDL_Rect pauseBtnRect() { SDL_Rect r = {(int)(49.5f * U), (int)(1.6f * U), (int)(8.5f * U), (int)(8.5f * U)}; return r; }
static void drawHud() {
    float fs = FS(), fm = FM();
    if (!paused && !P->dead) {   // кнопка паузы / меню
        SDL_Rect pr = pauseBtnRect();
        fillRect((float)pr.x, (float)pr.y, (float)pr.w, (float)pr.h, C(0, 0, 0, 110)); frameRect((float)pr.x, (float)pr.y, (float)pr.w, (float)pr.h, 2, C(255, 255, 255, 170));
        fillRect(pr.x + pr.w * 0.30f, pr.y + pr.h * 0.24f, pr.w * 0.14f, pr.h * 0.52f, C(255, 255, 255, 230)); fillRect(pr.x + pr.w * 0.56f, pr.y + pr.h * 0.24f, pr.w * 0.14f, pr.h * 0.52f, C(255, 255, 255, 230));
    }
    {   // подложка под статистику слева
        float ph = 24.5f * U + (players.size() > 1 ? (players.size() - 1) * 4.6f * U : 0.f), pw = 47.5f * U;
        fillRect(0, 0, pw, ph, C(0, 0, 0, 78)); fillRect(0, ph - 2, pw, 2, C(255, 255, 255, 34)); fillRect(pw - 2, 0, 2, ph, C(255, 255, 255, 34));
    }
    { float hf = P->hp / std::max(1.f, P->maxhp);
      drawBar(2 * U, 2 * U, 42 * U, 4.2f * U, hf, hf > 0.6f ? C(70, 190, 90) : (hf > 0.3f ? C(225, 185, 50) : C(215, 50, 45))); }
    drawText(fmt("HP %d/%d", (int)P->hp, (int)P->maxhp), 3 * U, 2.6f * U, fs, C(255, 255, 255));
    drawBar(2 * U, 7.2f * U, 42 * U, 2.6f * U, P->xp / P->need, C(80, 170, 255));
    drawText(fmt("УР. %d", P->level), 2 * U, 10.6f * U, fs, C(255, 255, 255));
    drawText(fmt("ЛОМ: %d", P->scrap), 22 * U, 10.6f * U, fs, C(255, 215, 90));
    drawText(fmt("УБИТО: %d", P->kills), 2 * U, 14.8f * U, fs, C(255, 255, 255));
    drawText(WEAP[P->weapon].name, 27 * U, 14.8f * U, fs, C(210, 230, 255));
    if (P->pending > 0) drawText("ЕСТЬ УЛУЧШЕНИЕ!", 2 * U, 19 * U, fs, C(120, 255, 120));
    float y = 23.5f * U;
    for (std::map<int, Player>::iterator it = players.begin(); it != players.end(); ++it) {
        Player& p = it->second; if (&p == P) continue;
        fillRect(2 * U, y + 0.3f * U, 2.4f * U, 2.4f * U, PCOL[p.id % 4]);
        drawText(p.name + (p.dead ? " (ПОГИБ)" : ""), 5.4f * U, y, fs, p.dead ? C(255, 120, 120) : C(255, 255, 255));
        y += 4.6f * U;
    }
    float wy = portrait ? 33 * U : 1.5f * U;
    if (duelMode) {                    // в дуэли вместо волны показываем здоровье соперника
        Player* opp = NULL;
        for (std::map<int, Player>::iterator it = players.begin(); it != players.end(); ++it) if (&it->second != P) { opp = &it->second; break; }
        std::string t1 = opp ? fmt("РАУНД %d   СЧЁТ %d:%d   %s: %d HP", duelRoundNum, duelScore[P->id], duelScore[opp->id], opp->name.c_str(), std::max(0, (int)opp->hp)) : "ДУЭЛЬ";
        float pw = textW(t1, fm, W * 0.9f) + 4 * U, ph = textH(fm) + 2 * U;
        fillRect(W / 2.f - pw / 2, wy - 1.2f * U, pw, ph, C(0, 0, 0, 82));
        drawText(t1, W / 2.f, wy, fm, C(255, 110, 90), A_TC, W * 0.9f);
    } else {
        {   // подложка под заголовок волны
            std::string t1 = prep ? fmt("ПОДГОТОВКА  %d С", std::max(0, (int)ptimer + 1)) : fmt("ВОЛНА %d   ЗОМБИ: %d", wave, leftZ);
            float w1 = textW(t1, fm, W * 0.9f), pw = w1 + 4 * U, ph = textH(fm) + 2 * U;
            if (prep) { float w2 = textW("ЗАДЕЛАЙ ПРОЁМЫ (СТРОЙ), СОБЕРИ ЯЩИКИ", fs, W * 0.9f); pw = std::max(w1, w2) + 4 * U; ph = textH(fm) + textH(fs) + 4.5f * U; }
            fillRect(W / 2.f - pw / 2, wy - 1.2f * U, pw, ph, C(0, 0, 0, 82));
        }
        if (prep) {
            drawText(fmt("ПОДГОТОВКА  %d С", std::max(0, (int)ptimer + 1)), W / 2.f, wy, fm, C(140, 230, 255), A_TC, W * 0.9f);
            drawText("ЗАДЕЛАЙ ПРОЁМЫ (СТРОЙ), СОБЕРИ ЯЩИКИ", W / 2.f, wy + 6.5f * U, fs, C(255, 255, 255), A_TC, W * 0.9f);
        } else drawText(fmt("ВОЛНА %d   ЗОМБИ: %d", wave, leftZ), W / 2.f, wy, fm, C(255, 110, 90), A_TC, W * 0.9f);
    }
    {   // здоровье босса
        const Zombie* boss = NULL;
        for (size_t i = 0; i < zombies.size(); i++) if (zombies[i].kind == 5) { boss = &zombies[i]; break; }
        if (boss) {
            float bw = std::min(W * 0.5f, 60 * U), bx = W / 2.f - bw / 2, by = portrait ? wy + 27 * U : 29 * U;
            drawText("ТИРАН", W / 2.f, by - textH(fs) - 4, fs, C(255, 120, 100), A_TC, W * 0.3f);
            drawBar(bx, by, bw, 3.6f * U, boss->hp / std::max(1.f, boss->maxhp), C(200, 40, 50));
        }
    }
    if (toastT > 0 && !toastS.empty()) {
        float tw = textW(toastS, fs, portrait ? W * 0.94f : W * 0.5f) + 3 * U, ty = portrait ? wy + 12 * U : 15 * U;
        fillRect(W / 2.f - tw / 2, ty - 1.0f * U, tw, textH(fs) + 2 * U, C(0, 0, 0, 90));
    }
    if (toastT > 0 && !toastS.empty()) drawText(toastS, W / 2.f, portrait ? wy + 12 * U : 15 * U, fs, C(255, 255, 140), A_TC, portrait ? W * 0.94f : W * 0.5f);
    if (netRole == R_HOST) drawText(fmt("ТЫ ХОСТ  IP: %s  ИГРОКОВ: %d/%d", hostIp.c_str(), (int)players.size(), MAX_PLAYERS), 2 * U, H - 5 * U, fs, C(150, 255, 170));
    else if (netRole == R_CLIENT) drawText("ТЫ " + P->name + " (В СЕТИ)", 2 * U, H - 5 * U, fs, C(150, 255, 170));
    std::string ammo = P->reload > 0 ? "ПЕРЕЗАРЯДКА" : fmt("%d/%d", P->ammo[P->weapon], mag_size(*P, P->weapon));
    {   // цена стройки под кнопкой СТРОЙ (следует за раскладкой)
        float bx = BTN[B_BUILD].cx, by = BTN[B_BUILD].cy + BTN[B_BUILD].r + 3;
        if (by + textH(fs) > H) drawText(fmt("СТРОЙ: %d ЛОМА", P->cost), bx, BTN[B_BUILD].cy - BTN[B_BUILD].r - 3, fs, C(255, 215, 90), A_BC, W * 0.3f);
        else drawText(fmt("СТРОЙ: %d ЛОМА", P->cost), bx, by, fs, C(255, 215, 90), A_TC, W * 0.3f);
    }
    if (bannerT > 0 && mode == M_PLAY) {   // крупный баннер волны
        float t = bannerT / bannerMax, al = std::min(1.f, std::min(t * 3.5f, (1.f - t) * 8.f)), sc = FL() * (1.f + 0.35f * (1.f - t));
        Col c = bannerCol == 3 ? C(255, 20, 20) : bannerCol == 1 ? C(255, 80, 60) : (bannerCol == 2 ? C(120, 255, 140) : C(255, 200, 80)); c.a = (Uint8)(255 * al);
        drawText(bannerS, W / 2.f, H * 0.24f, sc, c, A_TC, W * 0.9f);
        if (!bannerS2.empty()) drawText(bannerS2, W / 2.f, H * 0.24f + textH(sc) + 1.6f * U, FM(), C(255, 255, 255, (int)(230 * al)), A_TC, W * 0.9f);
    }
    if (hudCombo >= 2 && hudComboT > 0 && mode == M_PLAY) {   // серия убийств
        float al = std::min(1.f, hudComboT / 0.6f), sc = FM() * (1.f + 0.6f * (comboPop / 0.3f)), bx = W / 2.f + 7 * U, by = H / 2.f + 5 * U;
        drawText(fmt("СЕРИЯ: %d", hudCombo), bx, by, sc, C(255, 220, 90, (int)(255 * al)), A_TL, W * 0.3f);
        fillRect(bx, by + textH(sc) + 0.8f * U, 14 * U * (hudComboT / 3.5f), 0.7f * U, C(255, 200, 60, (int)(200 * al)));
    }
    Col ch = P->headT > 0 ? C(255, 210, 40) : (P->hit > 0 ? C(255, 60, 60) : C(60, 255, 90));
    float cx = W / 2.f, cy = H / 2.f, g = U * 1.2f, a = U * 2.4f, th = 2;
    fillRect(cx - a, cy - 1, a - g, th, ch); fillRect(cx + g, cy - 1, a - g, th, ch);
    fillRect(cx - 1, cy - a, th, a - g, ch); fillRect(cx - 1, cy + g, th, a - g, ch);
    if (P->headT > 0) {   // выстрел в голову: золотой прицел и надпись
        float al = std::min(1.f, P->headT / 0.2f);
        for (int q = 0; q < 4; q++) { float dx_ = (q % 2 ? 1 : -1) * U * 2.6f, dy_ = (q < 2 ? -1 : 1) * U * 2.6f; fillRect(cx + dx_ - 2, cy + dy_ - 2, 4, 4, C(255, 210, 40, (int)(230 * al))); }
        drawText("В ГОЛОВУ!", cx, cy - U * 9.f - (1.f - al) * U * 2.f, FM(), C(255, 215, 60, (int)(255 * al)), A_TC, W * 0.4f);
    }
    for (size_t i = 0; i < touches.size(); i++)
        if (touches[i].role == 2) {
            float vx, vy; stickVec(touches[i], &vx, &vy); float R = 14 * U;
            ringCircle(touches[i].ox, touches[i].oy, R, 2, C(255, 255, 255));
            fillCircle(touches[i].ox + vx * R, touches[i].oy + vy * R, 5 * U, C(255, 255, 255, 140));
        }
}

struct UIBtn { SDL_Rect r; std::string label; std::string act; Col col; };
static std::vector<UIBtn> ui;
static void uiButton(const UIBtn& b, float sc) {
    float x = (float)b.r.x, y = (float)b.r.y, w = (float)b.r.w, h = (float)b.r.h;
    fillRect(x + U * 0.25f, y + U * 0.4f, w, h, C(0, 0, 0, 100));                       // тень
    fillRect(x, y, w, h * 0.5f, shade(b.col, 1.28f)); fillRect(x, y + h * 0.5f, w, h * 0.5f + 1, shade(b.col, 0.80f));
    fillRect(x + 2, y + 2, w - 4, std::max(1.f, h * 0.05f), C(255, 255, 255, 70));      // блик сверху
    fillRect(x + 2, y + h - 2 - std::max(1.f, h * 0.04f), w - 4, std::max(1.f, h * 0.04f), C(0, 0, 0, 60));
    frameRect(x, y, w, h, std::max(2, (int)(U * 0.28f)), C(255, 255, 255, 210));
    drawText(b.label, x + w / 2.f, y + h / 2.f, sc, C(255, 255, 255), A_C, w * 0.92f);
}
static void cardRects(SDL_Rect* out) {
    if (portrait) {
        float cw = 0.88f * W, ch = 0.19f * H, gap = 0.025f * H, x0 = (W - cw) / 2, y0 = 0.20f * H;
        for (int i = 0; i < 3; i++) out[i] = {(int)x0, (int)(y0 + i * (ch + gap)), (int)cw, (int)ch};
    } else {
        float cw = 0.29f * W, ch = 0.5f * H, gap = 0.025f * W, x0 = (W - (3 * cw + 2 * gap)) / 2, y0 = 0.30f * H;
        for (int i = 0; i < 3; i++) out[i] = {(int)(x0 + i * (cw + gap)), (int)y0, (int)cw, (int)ch};
    }
}
static void drawWrapped(const std::string& text, float sc, Col col, const SDL_Rect& r, float ypos) {
    std::vector<std::string> lines; std::string cur; std::istringstream is(text); std::string w;
    int isc = std::max(1, (int)sc);
    while (is >> w) {
        std::string t = cur.empty() ? w : cur + " " + w;
        if ((textLen(t) * 6 - 1) * isc > r.w - 2 * U && !cur.empty()) { lines.push_back(cur); cur = w; } else cur = t;
    }
    lines.push_back(cur);
    float y = r.y + r.h * ypos;
    for (size_t i = 0; i < lines.size(); i++) { drawText(lines[i], r.x + r.w / 2.f, y, sc, col, A_TC, r.w - 2 * U); y += 9 * isc; }
}
static void drawLevelUp() {
    SDL_SetRenderDrawBlendMode(ren, SDL_BLENDMODE_BLEND);
    fillRect(0, 0, (float)W, (float)H, C(0, 0, 0, 170));
    drawText(fmt("НОВЫЙ УРОВЕНЬ %d - ВЫБЕРИ УЛУЧШЕНИЕ", P->level), W / 2.f, 0.12f * H, FM(), C(255, 255, 120), A_TC, W * 0.94f);
    if (!peers.empty() || netRole == R_CLIENT) drawText("ИГРА ИДЁТ ДАЛЬШЕ - ТЫ ПОКА НЕУЯЗВИМ", W / 2.f, 0.07f * H, FS(), C(255, 255, 255), A_TC, W * 0.94f);
    SDL_Rect rc[3]; cardRects(rc);
    for (int i = 0; i < 3; i++) {
        fillRect((float)rc[i].x, (float)rc[i].y, (float)rc[i].w, (float)rc[i].h, C(35, 40, 60));
        frameRect((float)rc[i].x, (float)rc[i].y, (float)rc[i].w, (float)rc[i].h, std::max(2, (int)(U * 0.4f)), C(255, 220, 90));
        drawWrapped(UPGS[P->cards[i]].title, FM(), C(255, 255, 255), rc[i], 0.10f);
        drawWrapped(UPGS[P->cards[i]].desc, FS(), C(190, 210, 255), rc[i], 0.55f);
    }
}
// ============================ МАГАЗИН ============================
struct IconR { int x, y, w, h, c; };
static const IconR IC0[] = {{4, 2, 24, 4, 0}, {6, 6, 16, 2, 1}, {8, 8, 5, 6, 0}, {26, 1, 2, 1, 1}};
static const IconR IC1[] = {{12, 3, 27, 2, 0}, {12, 5, 24, 1, 1}, {20, 5, 8, 3, 2}, {6, 2, 8, 5, 0}, {0, 3, 7, 6, 2}, {8, 7, 3, 4, 2}};
static const IconR IC2[] = {{22, 3, 17, 1, 1}, {6, 2, 18, 4, 0}, {20, 2, 10, 3, 2}, {12, 6, 4, 7, 1}, {0, 3, 7, 5, 2}, {36, 1, 1, 3, 1}};
static const IconR IC3[] = {{14, 2, 24, 2, 0}, {9, 1, 6, 5, 1}, {4, 2, 7, 4, 0}, {2, 6, 5, 7, 2}, {37, 1, 1, 1, 1}};
static const IconR IC4[] = {{6, 2, 22, 5, 0}, {28, 3, 9, 2, 1}, {12, 7, 4, 8, 1}, {5, 7, 4, 6, 0}, {0, 3, 6, 1, 1}, {26, 1, 2, 1, 1}};
static const IconR IC5[] = {{16, 3, 23, 1, 1}, {6, 2, 14, 4, 0}, {10, 0, 14, 2, 0}, {24, 0, 1, 2, 3}, {0, 3, 8, 6, 2}, {12, 6, 3, 3, 1}};
static const IconR IC6[] = {{22, 3, 18, 1, 1}, {6, 2, 20, 4, 0}, {20, 2, 12, 3, 1}, {12, 6, 4, 9, 0}, {0, 3, 7, 5, 2}, {14, 9, 10, 5, 0}};
static const IconR IC7[] = {{4, 3, 14, 4, 0}, {4, 5, 12, 1, 1}, {16, 2, 6, 5, 2}, {2, 7, 5, 7, 0}, {18, 3, 3, 3, 1}};
static const IconR* const ICONS[NW] = {IC0, IC1, IC2, IC3, IC4, IC5, IC6, IC7};
static const int ICONN[NW] = {4, 6, 6, 5, 6, 6, 6, 5};
static const Col ICOL[4] = {{74, 76, 88, 255}, {150, 154, 168, 255}, {156, 102, 54, 255}, {130, 210, 255, 255}};
static void drawIcon(int idx, float x, float y, float w, float h) {
    float u = std::min(w / 40.f, h / 16.f), ox = x + (w - 40 * u) / 2, oy = y + (h - 16 * u) / 2;
    for (int k = 0; k < ICONN[idx]; k++) {   // тёмная подложка для контура
        const IconR& r = ICONS[idx][k];
        fillRect(ox + r.x * u - u * 0.5f, oy + r.y * u - u * 0.5f, r.w * u + u, r.h * u + u, C(0, 0, 0, 200));
    }
    for (int k = 0; k < ICONN[idx]; k++) {
        const IconR& r = ICONS[idx][k];
        fillRect(ox + r.x * u, oy + r.y * u, r.w * u, r.h * u, ICOL[r.c]);
    }
}
static void layoutShop() {
    ui.clear();
    int cols = portrait ? 2 : 6, rows = portrait ? 6 : 2;
    float mx = 0.03f * W, top = portrait ? 0.15f * H : 0.21f * H, bot = portrait ? 0.03f * H : 0.04f * H, gap = 1.6f * U;
    float cw = (W - 2 * mx - (cols - 1) * gap) / cols, ch = (H - top - bot - (rows - 1) * gap) / rows;
    for (int k = 0; k < NSHOP; k++) {
        int r = k / cols, c = k % cols;
        SDL_Rect card = {(int)(mx + c * (cw + gap)), (int)(top + r * (ch + gap)), (int)cw, (int)ch};
        int widx = SHOP_ORDER[k];
        float sh = std::max(textH(FM()) + 10.f, 0.16f * ch);
        if (widx < NW && P && P->unl[widx] && P->wLvl[widx] < WLVL_MAX) {   // полная широкая полоса прокачки — крупная и понятная, лежит НАД полосой покупки/экипировки
            float ush = std::max(textH(FM()) + 8.f, 0.15f * ch);
            UIBtn up; up.r = {card.x + 3, (int)(card.y + ch - sh - ush - 5), (int)cw - 6, (int)ush};
            up.label = ""; up.act = fmt("upg:%d", widx); up.col = C(60, 100, 55); ui.push_back(up);   // добавлена ПЕРЕД кнопкой карточки, чтобы тап по полосе не перехватывался покупкой
        }
        UIBtn b; b.r = card; b.label = ""; b.act = fmt("buy:%d", widx); b.col = C(30, 36, 56); ui.push_back(b);
    }
    UIBtn cb; cb.r = {(int)(W - 26 * U), (int)(2 * U), (int)(24 * U), (int)(9 * U)}; cb.label = "ЗАКРЫТЬ"; cb.act = "shopclose"; cb.col = C(120, 60, 60); ui.push_back(cb);
}
static void drawShop() {
    SDL_SetRenderDrawBlendMode(ren, SDL_BLENDMODE_BLEND);
    fillRect(0, 0, (float)W, (float)H, C(6, 8, 16, 236));
    drawText("МАГАЗИН", 3 * U, 2.5f * U, FL() * 0.7f, C(255, 225, 120), A_TL, W * 0.45f);
    drawText(fmt("ЛОМ: %d", P->scrap), 3 * U, 12.5f * U, FM(), C(255, 215, 90), A_TL, W * 0.5f);
    layoutShop();
    float fs = FS(), fm = FM();
    for (size_t k = 0; k < ui.size(); k++) {
        const UIBtn& b = ui[k];
        if (b.act == "shopclose") { uiButton(b, fs); continue; }
        if (b.act.compare(0, 4, "upg:") == 0) continue;      // кнопки прокачки рисуются отдельно ниже
        int idx = atoi(b.act.c_str() + 4);
        bool gr = idx == 101 || idx == 102; int gt = idx - 101;
        bool med = idx == 100, owned = !med && !gr && P->unl[idx], eq = owned && P->weapon == idx;
        int price = med ? MEDKIT_PRICE : gr ? GREN_PRICE[gt] : WEAP[idx].price;
        bool can = med ? (P->scrap >= price && P->hp < P->maxhp - 0.5f) : gr ? (P->scrap >= price && P->gren[gt] < GREN_MAX) : (owned || P->scrap >= price);
        Col bg = eq ? C(26, 66, 46) : owned ? C(30, 46, 74) : can ? C(38, 44, 66) : C(34, 30, 40);
        Col fr = eq ? C(120, 255, 160) : owned ? C(110, 160, 255) : can ? C(255, 220, 110) : C(110, 100, 120);
        float x = (float)b.r.x, y = (float)b.r.y, w = (float)b.r.w, h = (float)b.r.h;
        fillRect(x, y, w, h, bg); frameRect(x, y, w, h, std::max(2, (int)(U * 0.3f)), fr);
        std::string nm = med ? "АПТЕЧКА" : gr ? std::string(gt == 0 ? "ГРАНАТА" : "ОГЛУШ. ГРАНАТА") : (owned && P->wLvl[idx] > 0 ? fmt("%s +%d", WEAP[idx].name, P->wLvl[idx]) : std::string(WEAP[idx].name));
        drawText(nm, x + w / 2, y + 0.05f * h, fm, C(255, 255, 255), A_TC, w * 0.92f);
        if (med) {
            float cs = std::min(w * 0.3f, h * 0.22f), cx = x + w / 2 - cs / 2, cy = y + 0.20f * h;
            fillRect(cx, cy, cs, cs, C(235, 235, 235)); fillRect(cx + cs * 0.4f, cy + cs * 0.15f, cs * 0.2f, cs * 0.7f, C(215, 30, 30)); fillRect(cx + cs * 0.15f, cy + cs * 0.4f, cs * 0.7f, cs * 0.2f, C(215, 30, 30));
        } else if (gr) {
            float cs = std::min(w * 0.3f, h * 0.22f), cx = x + w / 2, cy = y + 0.30f * h;
            fillCircle(cx, cy, cs * 0.5f, gt == 0 ? C(80, 120, 66) : C(96, 160, 232)); ringCircle(cx, cy, cs * 0.5f, std::max(1.f, cs * 0.07f), C(30, 40, 30));
            fillRect(cx - cs * 0.13f, cy - cs * 0.72f, cs * 0.26f, cs * 0.3f, C(205, 205, 210));
            fillRect(cx - cs * 0.5f, cy - cs * 0.05f, cs, cs * 0.1f, gt == 0 ? C(230, 70, 50) : C(240, 245, 255));
        } else drawIcon(idx, x + w * 0.1f, y + 0.17f * h, w * 0.8f, 0.20f * h);
        float ly = y + 0.38f * h, lh = textH(fs) + 2;
        std::vector<std::string> lines;
        if (med) { lines.push_back("ЛЕЧИТ: +50 HP"); }
        else if (gr) {
            if (gt == 0) { lines.push_back(fmt("УРОН: ДО %d", (int)GREN_DMG)); lines.push_back(fmt("РАДИУС: %.1f", GREN_RADIUS)); lines.push_back("ЛОМАЕТ ЯЩИКИ"); }
            else { lines.push_back("ОГЛУШАЕТ ВСЕХ"); lines.push_back(fmt("ЗОМБИ НА %d С", (int)STUN_TIME)); }
            lines.push_back(fmt("ЕСТЬ: %d", P->gren[gt]));
        } else {
            const WeaponDef& wd = WEAP[idx];
            lines.push_back(wd.pellets > 1 ? fmt("УРОН: %dX%d", (int)wd.dmg, wd.pellets) : fmt("УРОН: %d", (int)wd.dmg));
            lines.push_back(fmt("ТЕМП: %.1f/С", 1.f / wd.rate));
            lines.push_back(fmt("ОБОЙМА: %d", wd.mag));
            if (wd.pierce) lines.push_back("ПРОБИВАЕТ ВСЕХ");
        }
        for (size_t i = 0; i < lines.size(); i++) drawText(lines[i], x + w * 0.06f, ly + i * lh, fs, C(200, 210, 235), A_TL, w * 0.88f, false);
        float sh = std::max(textH(fm) + 10.f, 0.16f * h);
        Col sc = eq ? C(50, 150, 90) : owned ? C(50, 90, 170) : can ? C(50, 150, 70) : C(120, 50, 50);
        fillRect(x + 3, y + h - sh - 3, w - 6, sh, sc);
        std::string st = (gr && P->gren[gt] >= GREN_MAX) ? std::string("ПОЛНЫЙ ЗАПАС") : eq ? "В РУКАХ" : owned ? "ВЗЯТЬ" : can ? fmt("КУПИТЬ: %d", price) : (med && P->hp >= P->maxhp - 0.5f ? std::string("ЗДОРОВ") : fmt("НУЖНО: %d", price));
        drawText(st, x + w / 2, y + h - 3 - sh / 2, fm, C(255, 255, 255), A_C, w * 0.86f, false);
        if (!med && owned && P->wLvl[idx] >= WLVL_MAX) {   // максимальный уровень — показываем прямо на карточке
            float ush = std::max(textH(fm) + 8.f, 0.15f * h), uy = y + h - sh - ush - 5;
            fillRect(x + 3, uy, w - 6, ush, C(60, 55, 40)); frameRect(x + 3, uy, w - 6, ush, 1, C(210, 190, 120));
            drawText("МАКС. УРОВЕНЬ", x + w / 2, uy + ush / 2, fs, C(230, 210, 150), A_C, w * 0.9f, false);
        }
    }
    for (size_t k = 0; k < ui.size(); k++) {   // широкая понятная полоса прокачки — рисуется поверх карточек, крупный текст и цена
        const UIBtn& b = ui[k];
        if (b.act.compare(0, 4, "upg:") != 0) continue;
        int idx = atoi(b.act.c_str() + 4);
        int lvl = P->wLvl[idx], cost = wUpgCost(idx, lvl);
        bool can = P->scrap >= cost;
        float x = (float)b.r.x, y = (float)b.r.y, w = (float)b.r.w, h = (float)b.r.h;
        fillRect(x, y, w, h, can ? C(45, 120, 60, 245) : C(55, 42, 42, 245));
        frameRect(x, y, w, h, std::max(1, (int)(U * 0.22f)), can ? C(190, 255, 170) : C(160, 130, 130));
        drawText(fmt("УЛУЧШИТЬ +%d", lvl + 1), x + w * 0.30f, y + h / 2, fm, C(255, 255, 255), A_C, w * 0.56f, false);
        drawText(fmt("%d ЛОМ", cost), x + w * 0.80f, y + h / 2, fm, can ? C(255, 230, 140) : C(220, 150, 150), A_C, w * 0.42f, false);
    }
}
static void shopAction(const std::string& act) {
    if (act == "shopclose") { shopOpen = false; return; }
    if (act.compare(0, 4, "upg:") == 0) {
        int idx = atoi(act.c_str() + 4);
        if (netRole == R_CLIENT) { if (!linked) return; netSend(link_, fmt("U %d", idx)); }
        else upgradeWeapon(*P, idx);
        return;
    }
    if (act.compare(0, 4, "buy:") == 0) {
        int idx = atoi(act.c_str() + 4);
        if (netRole == R_CLIENT) {
            if (!linked) return;
            bool owned = idx >= 0 && idx < NW && P->unl[idx];
            netSend(link_, fmt(owned ? "E %d" : "B %d", idx));
        } else buyItem(*P, idx);
    }
}

// ============================ СКИНЫ ОРУЖИЯ (за монеты) ============================
static void drawBackdrop();
static void layoutSkins() {
    ui.clear();
    float tw = (W - 4 * U) / NW, th = portrait ? 8 * U : 9 * U, ty = portrait ? 0.13f * H : 0.15f * H, tx0 = 2 * U;
    for (int i = 0; i < NW; i++) {
        UIBtn b; b.r = {(int)(tx0 + i * tw), (int)ty, (int)(tw - 1.0f * U), (int)th};
        b.label = ""; b.act = fmt("wtab:%d", i); b.col = (i == skinsTab) ? C(70, 110, 150) : C(34, 38, 56); ui.push_back(b);
    }
    int cols = portrait ? 2 : NSKINS, rows = portrait ? 2 : 1;
    float top = ty + th + 3 * U, bot = portrait ? 0.05f * H : 0.06f * H, gap = 1.6f * U, mx = 0.07f * W;
    float cw = (W - 2 * mx - (cols - 1) * gap) / cols, ch = (H - top - bot - (rows - 1) * gap) / rows;
    for (int s = 0; s < NSKINS; s++) {
        int r = s / cols, c = s % cols;
        SDL_Rect card = {(int)(mx + c * (cw + gap)), (int)(top + r * (ch + gap)), (int)cw, (int)ch};
        UIBtn b; b.r = card; b.label = ""; b.act = fmt("sbuy:%d", s); b.col = C(30, 36, 56); ui.push_back(b);
    }
    UIBtn cb; cb.r = {(int)(W - 26 * U), (int)(2 * U), (int)(24 * U), (int)(9 * U)}; cb.label = "НАЗАД"; cb.act = "menu"; cb.col = C(120, 60, 60); ui.push_back(cb);
}
static void drawSkins() {
    drawBackdrop();
    SDL_SetRenderDrawBlendMode(ren, SDL_BLENDMODE_BLEND);
    fillRect(0, 0, (float)W, (float)H, C(6, 8, 16, 210));
    drawText("СКИНЫ ОРУЖИЯ", W / 2.f, 2.5f * U, FL() * 0.65f, C(255, 225, 120), A_TC, W * 0.6f);
    drawText(fmt("МОНЕТЫ: %d", coins), W - 27 * U, 2.5f * U, FM(), C(255, 215, 90), A_TR, W * 0.35f);
    layoutSkins();
    float fs = FS(), fm = FM();
    for (size_t k = 0; k < ui.size(); k++) {
        const UIBtn& b = ui[k];
        float x = (float)b.r.x, y = (float)b.r.y, w = (float)b.r.w, h = (float)b.r.h;
        if (b.act == "menu") { uiButton(b, fm); continue; }
        if (b.act.compare(0, 5, "wtab:") == 0) {
            int wi = atoi(b.act.c_str() + 5);
            fillRect(x, y, w, h, b.col); frameRect(x, y, w, h, std::max(1, (int)(U * 0.22f)), wi == skinsTab ? C(255, 230, 140) : C(90, 95, 120));
            drawIcon(wi, x + w * 0.06f, y + h * 0.10f, w * 0.88f, h * 0.72f);
            continue;
        }
        if (b.act.compare(0, 5, "sbuy:") == 0) {
            int s = atoi(b.act.c_str() + 5);
            const SkinDef& sk = SKINS[s];
            bool owned = skinOwned[skinsTab][s], eq = owned && weaponSkin[skinsTab] == s;
            bool can = owned || coins >= sk.price;
            Col bg = eq ? C(26, 66, 46) : owned ? C(30, 46, 74) : can ? C(38, 44, 66) : C(34, 30, 40);
            Col fr = eq ? C(120, 255, 160) : owned ? C(110, 160, 255) : can ? C(255, 220, 110) : C(110, 100, 120);
            fillRect(x, y, w, h, bg); frameRect(x, y, w, h, std::max(2, (int)(U * 0.3f)), fr);
            drawText(sk.name, x + w / 2, y + 0.06f * h, fm, C(255, 255, 255), A_TC, w * 0.9f);
            float sw = std::min(w * 0.5f, h * 0.34f), sx = x + w / 2 - sw / 2, sy = y + 0.24f * h;
            Col swc = s == 0 ? C(160, 163, 176) : sk.tint;
            fillRect(sx, sy, sw, sw, swc); frameRect(sx, sy, sw, sw, std::max(1, (int)(U * 0.2f)), C(20, 20, 24));
            float shb = std::max(textH(fm) + 10.f, 0.18f * h);
            Col sc = eq ? C(50, 150, 90) : owned ? C(50, 90, 170) : can ? C(50, 150, 70) : C(120, 50, 50);
            fillRect(x + 3, y + h - shb - 3, w - 6, shb, sc);
            std::string st = eq ? "НАДЕТО" : owned ? "НАДЕТЬ" : can ? fmt("КУПИТЬ: %d", sk.price) : fmt("НУЖНО: %d", sk.price);
            drawText(st, x + w / 2, y + h - 3 - shb / 2, fm, C(255, 255, 255), A_C, w * 0.86f, false);
            (void)fs;
            continue;
        }
    }
}
static void drawBackdrop() {       // ночное небо, луна, силуэты зомби — фон меню и настроек
    SDL_SetRenderDrawBlendMode(ren, SDL_BLENDMODE_BLEND);
    float gy = H * 0.72f;
    if (SKYTEX) {
        float tileW = SKYW * gy / SKYH, off = fmodf(animT * 22.f, tileW);
        for (float x = -off; x < W; x += tileW) { SDL_Rect a = {(int)floorf(x), 0, (int)ceilf(tileW) + 1, (int)gy}; SDL_RenderCopy(ren, SKYTEX, NULL, &a); }
    } else fillRect(0, 0, (float)W, gy, C(14, 12, 30));
    float mx = W * 0.80f, my = gy * 0.30f, mr = std::max(8.f, H * 0.045f);
    fillCircle(mx, my, mr * 4.2f, C(190, 200, 255, 10)); fillCircle(mx, my, mr * 3.0f, C(200, 210, 255, 16)); fillCircle(mx, my, mr * 2.0f, C(215, 225, 255, 30));
    fillCircle(mx, my, mr, C(238, 238, 218)); fillCircle(mx - mr * 0.3f, my - mr * 0.2f, mr * 0.28f, C(214, 214, 196));
    for (int b = 0; b < 12; b++) { float t = b / 12.f; fillRect(0, gy + b * (H - gy) / 12.f, (float)W, (H - gy) / 12.f + 1, C((int)(24 - 12 * t), (int)(34 - 16 * t), (int)(24 - 10 * t))); }
    for (int k = 0; k < 7; k++) {
        float sh = H * (0.30f + 0.06f * (k % 3)), sw = sh * 0.625f, x = W * (0.06f + 0.15f * k) + sinf(animT * 0.6f + k * 1.7f) * U * 1.2f;
        SDL_Texture* t = ZTEX[k % 3][((int)(animT * 1.6f + k)) & 1];
        if (!t) continue;
        float gyk = gy + (H - gy) * (0.55f + 0.14f * (k % 3));
        SDL_SetTextureColorMod(t, 14, 16, 28); SDL_SetTextureAlphaMod(t, 240);
        SDL_Rect d = {(int)(x - sw / 2), (int)(gyk - sh), (int)sw, (int)sh}; SDL_RenderCopy(ren, t, NULL, &d);
        SDL_SetTextureColorMod(t, 255, 255, 255); SDL_SetTextureAlphaMod(t, 255);
        float ey = gyk - sh + sh * 0.17f, es = std::max(2.f, sw * 0.06f);
        fillRect(x - sw * 0.10f - es / 2, ey, es, es, C(255, 50, 40, 230)); fillRect(x + sw * 0.10f - es / 2, ey, es, es, C(255, 50, 40, 230));
    }
    if (VIGTEX) { SDL_Rect full = {0, 0, W, H}; SDL_SetTextureAlphaMod(VIGTEX, 255); SDL_RenderCopy(ren, VIGTEX, NULL, &full); }
}
static void layoutMenu() {
    ui.clear();
    float bw = portrait ? 0.86f * W : 0.40f * W, bh = portrait ? 8.6f * U : 10.f * U, gap = portrait ? 1.6f * U : 2.f * U, x = (W - bw) / 2, y0 = portrait ? 0.27f * H : 0.31f * H;
    const char* lab[8] = {"ИГРА В ОДИНОЧКУ", "СОЗДАТЬ ИГРУ (КООП)", "ПРИСОЕДИНИТЬСЯ К ДРУГУ", "ДУЭЛЬ", "ЗАДАНИЯ ДНЯ", "СКИНЫ ОРУЖИЯ", "НАСТРОЙКИ", "ВЫХОД"};
    const char* act[8] = {"solo", "host", "join", "duel", "quests", "skins", "settings", "exit"};
    Col col[8] = {C(55, 105, 70), C(60, 85, 140), C(120, 70, 130), C(150, 60, 50), C(50, 120, 130), C(150, 120, 40), C(90, 90, 100), C(130, 55, 50)};
    for (int i = 0; i < 8; i++) {
        float bx = x, by = y0 + i * (bh + gap);
        if (!portrait) { int cc = i % 2, rowi = i / 2; bx = W / 2.f - bw - gap / 2 + cc * (bw + gap); by = y0 + rowi * (bh + gap); }   // две колонки: 8 кнопок в один столбец не влезали в экран
        UIBtn b; b.r = {(int)bx, (int)by, (int)bw, (int)bh}; b.label = lab[i]; b.act = act[i]; b.col = col[i]; ui.push_back(b);
    }
}
static void drawMenu() {
    drawBackdrop();
    {   // заголовок со свечением
        float ty = portrait ? 0.05f * H : 0.03f * H, g = std::max(2.f, U * 0.5f);
        for (int k = 0; k < 4; k++) drawText("ЗОМБИ-ОСАДА 3D", W / 2.f + (k % 2 ? g : -g), ty + (k < 2 ? g : -g), FXL(), C(255, 40, 30, 60), A_TC, W * 0.94f, false);
        drawText("ЗОМБИ-ОСАДА 3D", W / 2.f, ty, FXL(), C(232, 56, 44), A_TC, W * 0.94f);
    }
    drawText("КООП ДО 4 ИГРОКОВ ПО ЛОКАЛЬНОЙ СЕТИ", W / 2.f, portrait ? 0.19f * H : 0.22f * H, FS(), C(230, 230, 230), A_TC, W * 0.94f);
    layoutMenu();
    for (size_t i = 0; i < ui.size(); i++) uiButton(ui[i], FM());
    if (!msgStr.empty()) drawText(msgStr, W / 2.f, 0.83f * H, FS(), C(255, 140, 120), A_TC, W * 0.94f);
    if (bestWave) drawText(fmt("РЕКОРД: ВОЛНА %d   МОНЕТЫ: %d", bestWave, coins), W / 2.f, 0.90f * H, FM(), C(255, 215, 90), A_TC, W * 0.94f);
}
static void layoutDuelMenu() {
    ui.clear();
    float bw = portrait ? 0.86f * W : 0.5f * W, bh = portrait ? 7.4f * U : 8.f * U, gap = portrait ? 1.4f * U : 1.5f * U, x = (W - bw) / 2, y0 = portrait ? 0.28f * H : 0.24f * H;
    std::string lab[6] = {
        fmt("БОТ: %s", BOTLV[0].name), fmt("БОТ: %s", BOTLV[1].name), fmt("БОТ: %s", BOTLV[2].name), fmt("БОТ: %s", BOTLV[3].name),
        "С ДРУГОМ ПО СЕТИ", "НАЗАД"
    };
    const char* act[6] = {"duelbot:0", "duelbot:1", "duelbot:2", "duelbot:3", "duelhost", "menu"};
    Col col[6] = {C(70, 130, 90), C(150, 130, 50), C(160, 90, 40), C(150, 50, 50), C(60, 85, 140), C(90, 90, 100)};
    for (int i = 0; i < 6; i++) { UIBtn b; b.r = {(int)x, (int)(y0 + i * (bh + gap)), (int)bw, (int)bh}; b.label = lab[i]; b.act = act[i]; b.col = col[i]; ui.push_back(b); }
}
static void drawDuelMenu() {
    drawBackdrop();
    SDL_SetRenderDrawBlendMode(ren, SDL_BLENDMODE_BLEND);
    fillRect(0, 0, (float)W, (float)H, C(6, 8, 16, 200));
    drawText("ДУЭЛЬ", W / 2.f, portrait ? 0.07f * H : 0.06f * H, FXL(), C(255, 90, 70), A_TC, W * 0.7f);
    drawText("ОДИН НА ОДИН, ДО 3 ПОБЕД. ВЫБЕРИ СЛОЖНОСТЬ БОТА ИЛИ ЗОВИ ДРУГА", W / 2.f, portrait ? 0.15f * H : 0.14f * H, FS(), C(230, 230, 230), A_TC, W * 0.94f);
    layoutDuelMenu();
    for (size_t i = 0; i < ui.size(); i++) uiButton(ui[i], FM());
    std::string rec = fmt("РЕКОРД: ЛЁГК %d-%d  СРЕД %d-%d  СЛОЖН %d-%d  ЭКСП %d-%d  ДРУГ %d-%d",
        duelWinsBot[0], duelLossBot[0], duelWinsBot[1], duelLossBot[1], duelWinsBot[2], duelLossBot[2], duelWinsBot[3], duelLossBot[3], duelWinsFriend, duelLossFriend);
    drawText(rec, W / 2.f, 0.95f * H, FS() * 0.85f, C(180, 190, 210), A_TC, W * 0.96f);
    if (!msgStr.empty()) drawText(msgStr, W / 2.f, 0.90f * H, FS(), C(255, 140, 120), A_TC, W * 0.94f);
}
static const char* questLabel(int type) {
    switch (type) {
        case QT_KILLS: return "УБЕЙ %d ЗОМБИ";
        case QT_WAVE: return "ДОЙДИ ДО ВОЛНЫ %d";
        case QT_DUELWIN: return "ВЫИГРАЙ %d ДУЭЛЬ(И)";
        default: return "УБЕЙ %d В ГОЛОВУ";
    }
}
static void drawQuests() {
    drawBackdrop();
    SDL_SetRenderDrawBlendMode(ren, SDL_BLENDMODE_BLEND);
    fillRect(0, 0, (float)W, (float)H, C(6, 8, 16, 210));
    drawText("ЕЖЕДНЕВНЫЕ ЗАДАНИЯ", W / 2.f, 0.08f * H, FXL() * 0.7f, C(255, 225, 120), A_TC, W * 0.9f);
    drawText("ОБНОВЛЯЮТСЯ РАЗ В СУТКИ", W / 2.f, 0.15f * H, FS(), C(200, 200, 210), A_TC, W * 0.9f);
    ensureDaily();
    float fm = FM(), fs = FS();
    float top = 0.24f * H, ch = portrait ? 13.5f * U : 14.5f * U, gap = 2.2f * U, cw = W * 0.86f, cx = (W - cw) / 2;
    ui.clear();
    for (int i = 0; i < 3; i++) {
        float y = top + i * (ch + gap);
        const DailyQuest& q = dailyQ[i];
        bool done = q.claimed;
        Col bg = done ? C(26, 66, 46) : C(30, 36, 56);
        fillRect(cx, y, cw, ch, bg); frameRect(cx, y, cw, ch, std::max(2, (int)(U * 0.25f)), done ? C(120, 255, 160) : C(90, 95, 120));
        drawText(fmt(questLabel(q.type), q.target), cx + 3 * U, y + 0.18f * ch, fm, C(255, 255, 255), A_TL, cw - 6 * U);
        float bx = cx + 3 * U, by = y + 0.52f * ch, bw = cw - 6 * U, bh = 0.20f * ch;
        fillRect(bx, by, bw, bh, C(20, 22, 32));
        float frac = std::min(1.f, (float)q.progress / std::max(1, q.target));
        fillRect(bx, by, bw * frac, bh, done ? C(120, 220, 140) : C(90, 160, 230));
        frameRect(bx, by, bw, bh, 2, C(10, 10, 14));
        drawText(fmt("%d / %d", q.progress, q.target), bx + bw / 2, by + bh / 2, fs, C(255, 255, 255), A_C, bw * 0.9f, false);
        drawText(done ? fmt("ПОЛУЧЕНО: +%d МОНЕТ", q.reward) : fmt("НАГРАДА: +%d МОНЕТ", q.reward), cx + 3 * U, y + ch - 0.16f * ch, fs, C(255, 205, 70), A_TL, cw - 6 * U);
    }
    UIBtn cb; cb.r = {(int)(W - 26 * U), (int)(2 * U), (int)(24 * U), (int)(9 * U)}; cb.label = "НАЗАД"; cb.act = "menu"; cb.col = C(120, 60, 60); ui.push_back(cb);
    uiButton(ui[0], fm);
}
static void layoutExitConfirm() {
    ui.clear();
    float bw = portrait ? 0.8f * W : 0.42f * W, bh = 11 * U, gap = 2.4f * U, x = (W - bw) / 2, y = H / 2.f + gap / 2;
    UIBtn a; a.r = {(int)x, (int)y, (int)bw, (int)bh}; a.label = "ОСТАТЬСЯ"; a.act = "exitno"; a.col = C(55, 105, 70); ui.push_back(a);
    UIBtn b; b.r = {(int)x, (int)(y + bh + gap), (int)bw, (int)bh}; b.label = "ВЫЙТИ ИЗ ИГРЫ"; b.act = "exityes"; b.col = C(130, 55, 50); ui.push_back(b);
}
static void drawExitConfirm() {
    fillRect(0, 0, (float)W, (float)H, C(0, 0, 10, 180));
    drawText("ВЫЙТИ ИЗ ИГРЫ?", W / 2.f, H / 2.f - 26 * U, FXL(), C(255, 255, 255), A_TC, W * 0.8f);
    layoutExitConfirm();
    for (size_t i = 0; i < ui.size(); i++) uiButton(ui[i], FM());
}
static const char* QNAME[3] = {"НИЗКАЯ", "СРЕДНЯЯ", "ВЫСОКАЯ"};
static const char* DNAME[3] = {"ЛЕГКО", "НОРМА", "СЛОЖНО"};
static void layoutSettings() {
    ui.clear();
    float bw = portrait ? 0.88f * W : 0.62f * W, x = (W - bw) / 2, rh = portrait ? 9.f * U : 8.0f * U, gap = portrait ? 1.6f * U : 1.2f * U, y = portrait ? 0.15f * H : 0.145f * H;
    auto add = [&](float xx, float ww, const std::string& lab, const std::string& act, Col col) {
        UIBtn b; b.r = {(int)xx, (int)y, (int)ww, (int)rh}; b.label = lab; b.act = act; b.col = col; ui.push_back(b);
    };
    float sb = 14 * U, hw = (bw - gap) / 2;
    add(x, bw, "РАСПОЛОЖЕНИЕ КНОПОК", "layout", C(60, 85, 140)); y += rh + gap;
    add(x, bw, leftHand ? "УПРАВЛЕНИЕ: ЛЕВША" : "УПРАВЛЕНИЕ: ПРАВША", "hand", C(80, 70, 130)); y += rh + gap;
    add(x, sb, "-", "size-", C(50, 55, 80)); add(x + bw - sb, sb, "+", "size+", C(50, 55, 80)); y += rh + gap;
    add(x, sb, "-", "sens-", C(50, 55, 80)); add(x + bw - sb, sb, "+", "sens+", C(50, 55, 80)); y += rh + gap;
    add(x, hw, invertY ? "ОСЬ Y: ИНВЕРСИЯ" : "ОСЬ Y: ОБЫЧНАЯ", "invy", C(70, 90, 120)); add(x + hw + gap, hw, aimAssist ? "АВТОНАВОД: ВКЛ" : "АВТОНАВОД: ВЫКЛ", "aim", C(70, 90, 120)); y += rh + gap;
    add(x, bw, std::string("ГРАФИКА: ") + QNAME[quality], "quality", C(60, 110, 90)); y += rh + gap;
    add(x, hw, showFps ? "FPS: ВКЛ" : "FPS: ВЫКЛ", "fps", C(60, 100, 120)); add(x + hw + gap, hw, autoQ ? "АВТО-ГРАФИКА: ВКЛ" : "АВТО-ГРАФИКА: ВЫКЛ", "autoq", C(60, 100, 120)); y += rh + gap;
    add(x, hw, autoFireOn ? "АВТО-ОГОНЬ: ВКЛ" : "АВТО-ОГОНЬ: ВЫКЛ", "autofire", C(150, 90, 190)); add(x + hw + gap, hw, soundOn ? "ЗВУК: ВКЛ" : "ЗВУК: ВЫКЛ", "sound", C(90, 90, 130)); y += rh + gap;
    add(x, bw, std::string("СЛОЖНОСТЬ: ") + DNAME[difficulty], "diff", C(130, 90, 90)); y += rh + gap;
    add(x, bw, std::string("КЛАСС: ") + PERKS[selectedPerk].name, "class", C(90, 60, 140)); y += rh + gap + 3.6f * U;   // место под описание класса
    add(x, hw, "СБРОС КНОПОК", "reset", C(120, 80, 50)); add(x + hw + gap, hw, "НАЗАД", "menu", C(110, 60, 60)); y += rh;
    float contentTop = portrait ? 0.15f * H : 0.145f * H, bottomPad = 3 * U;
    settingsMaxScroll = std::max(0.f, y + bottomPad - H);
    settingsScroll = std::max(0.f, std::min(settingsMaxScroll, settingsScroll));
    for (size_t i = 0; i < ui.size(); i++) ui[i].r.y -= (int)settingsScroll;
    (void)contentTop;
}
static void drawSettings() {
    drawBackdrop();
    fillRect(0, 0, (float)W, (float)H, C(0, 0, 0, 120));
    drawText("НАСТРОЙКИ", W / 2.f, portrait ? 0.06f * H : 0.03f * H, FL() * 0.8f, C(255, 255, 255), A_TC, W * 0.9f);
    layoutSettings();
    for (size_t i = 0; i < ui.size(); i++) uiButton(ui[i], FM());
    // подпись размера между кнопками - и +
    for (size_t i = 0; i < ui.size(); i++) {
        float lw = (portrait ? 0.88f * W : 0.62f * W) - 32 * U;
        if (ui[i].act == "size-") drawText(fmt("РАЗМЕР КНОПОК: %d%%", (int)(btnScale * 100 + 0.5f)), W / 2.f, ui[i].r.y + ui[i].r.h / 2.f, FM(), C(255, 255, 255), A_C, lw);
        if (ui[i].act == "sens-") drawText(fmt("ЧУВСТВИТЕЛЬНОСТЬ: %d%%", (int)(sensitivity * 100 + 0.5f)), W / 2.f, ui[i].r.y + ui[i].r.h / 2.f, FM(), C(255, 255, 255), A_C, lw);
        if (ui[i].act == "class") drawText(PERKS[selectedPerk].desc, W / 2.f, ui[i].r.y + ui[i].r.h + 1.3f * U, FS() * 0.85f, C(200, 200, 215), A_TC, lw);
    }
    if (settingsMaxScroll > 1.f) {   // полоска прокрутки справа + подсказка, если список не помещается
        float trackX = W - 3 * U, trackY = portrait ? 0.15f * H : 0.145f * H, trackH = H - trackY - 2 * U;
        fillRect(trackX, trackY, 1.2f * U, trackH, C(255, 255, 255, 40));
        float thumbH = std::max(6 * U, trackH * trackH / (trackH + settingsMaxScroll)), thumbY = trackY + (trackH - thumbH) * (settingsScroll / settingsMaxScroll);
        fillRect(trackX, thumbY, 1.2f * U, thumbH, C(255, 255, 255, 150));
        if (settingsScroll < settingsMaxScroll - 1.f) drawText("ЕЩЁ НИЖЕ", W / 2.f, H - 2.2f * U, FS(), C(255, 255, 255, 170), A_BC, W * 0.5f);
    }
}
static int dragBtn = -1; static long long dragId = -2;
static void enterLayoutEditor() {
    int o = portrait ? 1 : 0;      // снимок текущих позиций как отправную точку для перетаскивания, но НЕ замораживаем раскладку, пока палец правда не потянет кнопку — иначе просто открыв этот экран, человек навсегда лишается будущих улучшений расположения по умолчанию
    if (!hasCustom[o]) for (int i = 0; i < NB; i++) { customPos[o][i][0] = BTN[i].cx / W; customPos[o][i][1] = BTN[i].cy / H; }
    dragBtn = -1; dragId = -2; mode = M_LAYOUT;
}
static void layoutEditorUi() {
    ui.clear();
    float bw = 21 * U, bh = 9 * U, gap = 1.5f * U, x0 = (W - (4 * bw + 3 * gap)) / 2, y = 2 * U;
    const char* lab[4] = {"ГОТОВО", "СБРОС", "-", "+"};
    const char* act[4] = {"edone", "ereset", "size-", "size+"};
    Col col[4] = {C(55, 120, 70), C(120, 80, 50), C(50, 55, 80), C(50, 55, 80)};
    for (int i = 0; i < 4; i++) { UIBtn b; b.r = {(int)(x0 + i * (bw + gap)), (int)y, (int)bw, (int)bh}; b.label = lab[i]; b.act = act[i]; b.col = col[i]; ui.push_back(b); }
}
static void drawLayoutEditor() {
    fillRect(0, 0, (float)W, (float)H, C(14, 16, 26));
    for (int gx = 0; gx <= 10; gx++) fillRect(gx * W / 10.f, 0, 1, (float)H, C(255, 255, 255, 14));
    for (int gy = 0; gy <= 10; gy++) fillRect(0, gy * H / 10.f, (float)W, 1, C(255, 255, 255, 14));
    // зоны управления
    float zx = portrait ? (leftHand ? W * 0.5f : 0.f) : (leftHand ? W * 0.58f : 0.f), zw = portrait ? W * 0.5f : (leftHand ? W * 0.42f : W * 0.42f), zy = portrait ? H * 0.5f : 0.f, zh = portrait ? H * 0.5f : (float)H;
    fillRect(zx, zy, zw, zh, C(70, 140, 255, 26)); frameRect(zx, zy, zw, zh, 2, C(70, 140, 255, 90));
    drawText("ДЖОЙСТИК", zx + zw / 2, zy + zh / 2 - textH(FM()), FM(), C(140, 190, 255, 200), A_TC, zw * 0.9f, false);
    drawText("ВСЁ ОСТАЛЬНОЕ - КАМЕРА", W / 2.f, H * 0.5f - 2 * U, FS(), C(200, 200, 200, 160), A_TC, W * 0.6f, false);
    // место миникарты
    { int px = std::max(2, (int)(std::min(W, H) * 0.30f / N)); float mw = (float)N * px; frameRect(W - mw - 2 * U, 2 * U, mw, mw, 2, C(200, 200, 90, 120)); drawText("КАРТА", W - mw / 2 - 2 * U, 2 * U + mw / 2, FS(), C(220, 220, 120, 170), A_C, mw, false); }
    drawButtons(true);
    layoutEditorUi();
    for (size_t i = 0; i < ui.size(); i++) uiButton(ui[i], ui[i].label.size() > 2 ? FS() : FM());
    drawText("ПЕРЕТАСКИВАЙ КНОПКИ ПАЛЬЦЕМ", W / 2.f, 12.5f * U, FS(), C(255, 255, 140), A_TC, W * 0.7f);
    drawText(fmt("РАЗМЕР: %d%%", (int)(btnScale * 100 + 0.5f)), W / 2.f, 12.5f * U + textH(FS()) + 6, FS(), C(255, 255, 255), A_TC, W * 0.5f);
}
static void layoutJoin() {
    ui.clear();
    static const char* KEYL[12] = {"1", "2", "3", "4", "5", "6", "7", "8", "9", ".", "0", "<-"};
    float kx, kw, ky, kh, gap, hx, hw, hy; SDL_Rect back, go;
    if (portrait) {
        kx = 0.08f * W; kw = 0.84f * W; ky = 0.14f * H + 13 * U + 3 * 10.5f * U + 4 * U; kh = 13 * U; gap = 2 * U;
        hx = 0.08f * W; hw = 0.84f * W; hy = 0.14f * H + 13 * U;
        float by = ky + 4 * (kh + gap) + 2 * U;
        back = {(int)(0.08f * W), (int)by, (int)(0.40f * W), (int)kh}; go = {(int)(0.52f * W), (int)by, (int)(0.40f * W), (int)kh};
    } else {
        kx = 0.54f * W; kw = 0.42f * W; ky = 8 * U; kh = 11.5f * U; gap = 1.6f * U; hx = 0.04f * W; hw = 0.46f * W; hy = 30 * U;
        float by = ky + 4 * (kh + gap) + U;
        back = {(int)(0.54f * W), (int)by, (int)(0.20f * W), (int)kh}; go = {(int)(0.76f * W), (int)by, (int)(0.20f * W), (int)kh};
    }
    float cw = (kw - 2 * gap) / 3;
    for (int i = 0; i < 12; i++) {
        int r = i / 3, c = i % 3; UIBtn b; b.r = {(int)(kx + c * (cw + gap)), (int)(ky + r * (kh + gap)), (int)cw, (int)kh};
        b.label = KEYL[i]; b.act = std::string("key:") + KEYL[i]; b.col = C(50, 55, 80); ui.push_back(b);
    }
    UIBtn b1; b1.r = back; b1.label = "НАЗАД"; b1.act = "menu"; b1.col = C(110, 60, 60); ui.push_back(b1);
    UIBtn b2; b2.r = go; b2.label = "ВОЙТИ"; b2.act = "connect"; b2.col = C(55, 120, 70); ui.push_back(b2);
    for (size_t i = 0; i < found.size() && i < 3; i++) {
        UIBtn b; b.r = {(int)hx, (int)(hy + i * 10.5f * U), (int)hw, (int)(9 * U)}; b.label = found[i].ip + " (ХОСТ)"; b.act = "pick:" + found[i].ip; b.col = C(60, 85, 140); ui.push_back(b);
    }
}
static void drawJoin() {
    drawBackdrop();
    fillRect(0, 0, (float)W, (float)H, C(0, 0, 0, 130));
    float cxm = portrait ? W / 2.f : W * 0.27f;
    drawText("ПРИСОЕДИНИТЬСЯ", cxm, portrait ? 0.05f * H : 3 * U, FM(), C(255, 255, 255), A_TC, W * 0.5f);
    SDL_Rect box = portrait ? SDL_Rect{(int)(0.08f * W), (int)(0.14f * H - 4 * U), (int)(0.84f * W), (int)(10 * U)}
                            : SDL_Rect{(int)(0.04f * W), (int)(13 * U), (int)(0.46f * W), (int)(10 * U)};
    fillRect((float)box.x, (float)box.y, (float)box.w, (float)box.h, C(25, 28, 45));
    frameRect((float)box.x, (float)box.y, (float)box.w, (float)box.h, 2, C(255, 255, 255));
    drawText(ipStr.empty() ? "IP ХОСТА" : ipStr, box.x + box.w / 2.f, box.y + box.h / 2.f, FM(), ipStr.empty() ? C(150, 150, 150) : C(255, 255, 120), A_C, box.w * 0.9f);
    layoutJoin();
    for (size_t i = 0; i < ui.size(); i++) uiButton(ui[i], ui[i].act.compare(0, 4, "pick") == 0 ? FS() : FM());
    if (found.empty()) drawText("ИЩУ ИГРЫ В СЕТИ...", cxm, portrait ? 0.14f * H + 13 * U : 30 * U, FS(), C(170, 170, 190), A_TC, W * 0.4f);
    if (!msgStr.empty()) drawText(msgStr, cxm, portrait ? 0.93f * H : 0.72f * H, FS(), C(255, 200, 120), A_TC, portrait ? W * 0.94f : W * 0.48f);
}
static void drawDead() {
    SDL_SetRenderDrawBlendMode(ren, SDL_BLENDMODE_BLEND);
    fillRect(0, 0, (float)W, (float)H, C(0, 0, 0, 165));
    if (duelMode) {
        bool won = !P->dead;
        drawText(won ? "ПОБЕДА!" : "ПОРАЖЕНИЕ", W / 2.f, 0.12f * H, FXL(), won ? C(120, 255, 140) : C(230, 40, 40), A_TC, W * 0.94f);
        float y = 0.32f * H, st = textH(FM()) * 1.7f;
        drawText(won ? "ТЫ ПОБЕДИЛ В ДУЭЛИ" : "ТЫ ПРОИГРАЛ ДУЭЛЬ", W / 2.f, y, FM(), C(255, 255, 255), A_TC, W * 0.94f); y += st;
        drawText(fmt("СЧЁТ ПО РАУНДАМ: %d:%d", duelScore[0], duelScore[1]), W / 2.f, y, FM(), C(255, 255, 255), A_TC, W * 0.94f); y += st;
        drawText(fmt("УБИТО ВЫСТРЕЛАМИ: %d", P->kills), W / 2.f, y, FM(), C(255, 255, 255), A_TC, W * 0.94f); y += st;
        drawText(fmt("+%d МОНЕТ ЗА ДУЭЛЬ (ВСЕГО: %d)", lastCoinsGain, coins), W / 2.f, y, FM(), C(255, 205, 70), A_TC, W * 0.94f);
        if (deadT <= 0) drawText("КОСНИСЬ ЭКРАНА - В МЕНЮ", W / 2.f, 0.88f * H, FM(), C(120, 255, 140), A_TC, W * 0.94f);
        return;
    }
    drawText(players.size() > 1 ? "ВАС СЪЕЛИ" : "ТЕБЯ СЪЕЛИ", W / 2.f, 0.09f * H, FXL(), C(230, 40, 40), A_TC, W * 0.94f);
    float y = 0.27f * H, st = textH(FM()) * 1.7f;
    if (newRecord && wave >= bestWave && wave > 0) {
        float pul = 0.75f + 0.25f * sinf(animT * 6.f);
        drawText("НОВЫЙ РЕКОРД!", W / 2.f, y, FM() * 1.3f, C(255, (int)(215 * pul), 60), A_TC, W * 0.9f); y += st * 1.4f;
    }
    int tm = (int)runTime;
    drawText(fmt("ВОЛНА: %d", wave), W / 2.f, y, FM(), C(255, 255, 255), A_TC, W * 0.94f); y += st;
    drawText(fmt("УБИТО: %d", P->kills), W / 2.f, y, FM(), C(255, 255, 255), A_TC, W * 0.94f); y += st;
    drawText(fmt("В ГОЛОВУ: %d", statHead), W / 2.f, y, FM(), C(255, 215, 90), A_TC, W * 0.94f); y += st;
    drawText(fmt("ВРЕМЯ: %d:%02d   УРОВЕНЬ: %d", tm / 60, tm % 60, P->level), W / 2.f, y, FM(), C(255, 255, 255), A_TC, W * 0.94f); y += st;
    drawText(fmt("РЕКОРД: ВОЛНА %d", bestWave), W / 2.f, y, FM(), C(255, 215, 90), A_TC, W * 0.94f); y += st;
    drawText(fmt("+%d МОНЕТ ЗА ИГРУ (ВСЕГО: %d)", lastCoinsGain, coins), W / 2.f, y, FM(), C(255, 205, 70), A_TC, W * 0.94f);
    if (deadT <= 0) drawText("КОСНИСЬ ЭКРАНА - В МЕНЮ", W / 2.f, 0.88f * H, FM(), C(120, 255, 140), A_TC, W * 0.94f);
}

static void layoutPause() {
    ui.clear();
    float bw = portrait ? 0.8f * W : 0.42f * W, bh = 11 * U, gap = 2.4f * U, x = (W - bw) / 2, y = H / 2.f - bh - gap / 2;
    UIBtn a; a.r = {(int)x, (int)y, (int)bw, (int)bh}; a.label = "ПРОДОЛЖИТЬ"; a.act = "resume"; a.col = C(55, 105, 70); ui.push_back(a);
    UIBtn b; b.r = {(int)x, (int)(y + bh + gap), (int)bw, (int)bh}; b.label = "В МЕНЮ"; b.act = "menu"; b.col = C(120, 60, 60); ui.push_back(b);
}
static void drawPause() {
    fillRect(0, 0, (float)W, (float)H, C(0, 0, 10, 150));
    drawText((netRole == R_SOLO && peers.empty()) ? "ПАУЗА" : "МЕНЮ", W / 2.f, H / 2.f - 33 * U, FXL(), C(255, 255, 255), A_TC, W * 0.8f);
    layoutPause();
    for (size_t i = 0; i < ui.size(); i++) uiButton(ui[i], FM());
}
static void drawFrame() {
    SDL_SetRenderDrawBlendMode(ren, SDL_BLENDMODE_BLEND);
    if (mode == M_MENU) { drawMenu(); if (confirmExit) drawExitConfirm(); return; }
    if (mode == M_JOIN) { drawJoin(); return; }
    if (mode == M_SETTINGS) { drawSettings(); return; }
    if (mode == M_SKINS) { drawSkins(); return; }
    if (mode == M_DUEL) { drawDuelMenu(); return; }
    if (mode == M_QUESTS) { drawQuests(); return; }
    if (mode == M_LAYOUT) { drawLayoutEditor(); return; }
    {   // покачивание камеры при ходьбе и отдача
        float bobY = P->bob > 0 ? sinf(P->bob * 7.f) * U * 0.35f : 0.f, kickY = fireAnim > 0 ? fireAnim * fireAnim * U * 1.3f : 0.f;
        float shake = P->hurt > 0 ? sinf(animT * 70.f) * U * 0.55f * std::min(1.f, P->hurt / 0.35f) : 0.f;    // тряска при уроне
        if (shakeT > 0) shake += sinf(animT * 63.f) * U * 1.0f * std::min(1.f, shakeT / 0.35f);            // тряска от взрывов и ударов босса
        HZ = H / 2.f + bobY + kickY + shake + tanf(P->pitch) * FOCAL;   // взгляд вверх/вниз сдвигает горизонт
        EYE_H = 0.5f + P->jumpZ;   // настоящий прыжок: меняется высота глаз, а не сдвигается картинка — пол и стены сами встают правильно
    }
    renderWalls();
    renderSprites();
    renderParticles();
    {   // всплывающие числа урона над зомби
        float dx = cosf(P->ang), dy = sinf(P->ang), plx = -dy * TANH_, ply = dx * TANH_, inv = 1.f / (plx * dy - dx * ply);
        for (size_t i = 0; i < dmgNums.size(); i++) {
            const DmgNum& d = dmgNums[i];
            float rx = d.x - P->x, ry = d.y - P->y, ty = inv * (-ply * rx + plx * ry);
            if (ty < 0.3f || ty > 12.f) continue;
            float tx = inv * (dy * rx - dx * ry), sx = W / 2.f * (1.f + tx / ty), sy = HZ + FOCAL * (EYE_H - d.z) / ty;
            int col = (int)(sx * RW / W);
            if (col < 0 || col >= RW || zbuf[col] < ty) continue;
            float a = std::min(1.f, d.life / (d.maxl * 0.5f)), sz = std::max(1.f, floorf((d.head ? 0.62f : 0.44f) * U * std::min(1.f, 5.f / (ty + 1.5f)) + 0.5f));
            Col c = d.head ? C(255, 215, 60, (int)(255 * a)) : (d.val >= 60 ? C(255, 140, 50, (int)(255 * a)) : C(255, 255, 255, (int)(230 * a)));
            drawText(fmt("%d", d.val), sx, sy, sz, c, A_C, 0, true);
        }
    }
    if (MISTTEX) {   // приземный туман: два слоя плывут с разной скоростью
        float bandH = H * 0.12f, y0 = HZ - bandH * 0.45f;
        for (int layer = 0; layer < 2; layer++) {
            float tw_ = W * (layer ? 1.6f : 1.1f), off = fmodf(animT * (layer ? 9.f : 5.f) + P->ang * FOCAL * 0.15f, tw_); if (off < 0) off += tw_;
            SDL_SetTextureAlphaMod(MISTTEX, layer ? 46 : 70);
            for (float x = -off; x < W; x += tw_) { SDL_Rect a = {(int)floorf(x), (int)(y0 + layer * bandH * 0.12f), (int)ceilf(tw_) + 1, (int)bandH}; SDL_RenderCopy(ren, MISTTEX, NULL, &a); }
        }
    }
    if (!P->dead) drawViewmodel();
    if (P->flash > 0) fillRect(0, 0, (float)W, (float)H, C(255, 190, 90, (int)(30 * P->flash / 0.07f)));
    if (bloodMoon > 0.02f) {
        float bnk = bloodNight ? 2.2f : 1.f;   // в кровавую ночь оттенок гуще и пульсирует сильнее
        fillRect(0, 0, (float)W, (float)H, C(160, 0, 0, (int)((14 * bloodMoon + 4 * bloodMoon * sinf(animT * (bloodNight ? 3.2f : 2.f))) * bnk)));
    }
    if (LIGHTTEX) {   // световое пятно перед игроком (ярче при выстреле)
        float lw = H * 1.5f, lh = H * 1.05f; SDL_Rect lr = {(int)(W / 2.f - lw / 2), (int)(H * 0.56f - lh / 2), (int)lw, (int)lh};
        SDL_SetTextureAlphaMod(LIGHTTEX, (Uint8)(P->flash > 0 ? 200 : 70)); SDL_RenderCopy(ren, LIGHTTEX, NULL, &lr);
    }
    if (boomFlashT > 0) fillRect(0, 0, (float)W, (float)H, C(255, 175, 70, (int)(std::min(1.f, boomFlashT / 0.25f) * 120)));
    if (stunFlashT > 0) fillRect(0, 0, (float)W, (float)H, C(235, 245, 255, (int)(std::min(1.f, stunFlashT / 0.4f) * 210)));
    if (VIGTEX) { SDL_Rect full = {0, 0, W, H}; SDL_SetTextureAlphaMod(VIGTEX, 255); SDL_RenderCopy(ren, VIGTEX, NULL, &full); }
    if (P->hurt > 0) {
        float hk = std::min(1.f, P->hurt / 0.35f);
        if (VIGRED) { SDL_Rect full = {0, 0, W, H}; SDL_SetTextureAlphaMod(VIGRED, (Uint8)(255 * hk)); SDL_RenderCopy(ren, VIGRED, NULL, &full); }
        fillRect(0, 0, (float)W, (float)H, C(200, 0, 0, (int)(hk * 55)));
    }
    if (P->hp < P->maxhp * 0.3f && !P->dead && VIGRED) {   // пульсация при низком здоровье
        SDL_Rect full = {0, 0, W, H}; SDL_SetTextureAlphaMod(VIGRED, (Uint8)(60 + 50 * sinf(animT * 6.f)));
        SDL_RenderCopy(ren, VIGRED, NULL, &full);
    }
    drawMinimap();
    drawHud();
    drawButtons();
    if (!tutDone && mode == M_PLAY && !P->menu && !shopOpen && !paused) drawTutorial();      // обучение поверх кнопок
    if (mode == M_PLAY && P->dead) {
        drawText("ТЫ ПОГИБ", W / 2.f, 0.30f * H, FL(), C(230, 50, 50), A_TC, W * 0.9f);
        drawText("ДРУЗЬЯ ДЕРЖАТСЯ... ВЕРНЁШЬСЯ ПОСЛЕ ВОЛНЫ", W / 2.f, 0.30f * H + 13 * U, FS(), C(255, 255, 255), A_TC, W * 0.94f);
    } else if (mode == M_PLAY && P->menu) drawLevelUp();
    else if (mode == M_PLAY && shopOpen) drawShop();
    else if (mode == M_DEAD) drawDead();
}

// ============================ ВВОД ============================
static void press(int b) {
    if (b != B_FIRE) playSound(S_CLICK, 0.45f);
    if (b == B_SHOP) { if (!P->dead && mode == M_PLAY) shopOpen = !shopOpen; return; }
    if (netRole == R_CLIENT) {
        if (b == B_AUTO) P->autoF = !P->autoF;
        else if (b == B_JUMP) { doJump(*P); if (linked) netSend(link_, "A jump"); }        // локально сразу, хосту — чтобы видели остальные
        else if (linked) {
            const char* n = b == B_BUILD ? "build" : b == B_RELOAD ? "reload" : b == B_WEAPON ? "weapon" : b == B_START ? "start" : b == B_GREN ? "gren0" : b == B_STUN ? "gren1" : NULL;
            if (n) netSend(link_, std::string("A ") + n);
        }
        return;
    }
    if (b == B_BUILD) buildOrRepair(*P);
    else if (b == B_WEAPON) switchWeapon(*P);
    else if (b == B_RELOAD) startReload(*P);
    else if (b == B_AUTO) P->autoF = !P->autoF;
    else if (b == B_START) { if (prep && !P->dead) startWave(); }
    else if (b == B_JUMP) doJump(*P);
    else if (b == B_GREN) throwGrenade(*P, 0);
    else if (b == B_STUN) throwGrenade(*P, 1);
}
static void uiAction(const std::string& act) {
    if (act == "exit") { confirmExit = true; }
    else if (act == "exitno") { confirmExit = false; }
    else if (act == "exityes") { saveData(); wantQuit = true; }
    else if (act == "solo") { shutdownNet(); duelMode = false; duelBot = false; msgStr.clear(); newGame(); }
    else if (act == "host") { duelMode = false; duelBot = false; msgStr.clear(); startHost(); }
    else if (act == "join") { duelMode = false; duelBot = false; openJoin(); }
    else if (act == "duel") { mode = M_DUEL; }
    else if (act == "quests") { mode = M_QUESTS; }
    else if (act == "class") { selectedPerk = (selectedPerk + 1) % 4; saveData(); }
    else if (act.compare(0, 8, "duelbot:") == 0) { duelBotLevel = std::max(0, std::min(3, atoi(act.c_str() + 8))); msgStr.clear(); startDuelBot(); }
    else if (act == "duelhost") { msgStr.clear(); startDuelHost(); }
    else if (act == "menu") { paused = false; shutdownNet(); duelMode = false; duelBot = false; mode = M_MENU; msgStr.clear(); }
    else if (act == "settings") { mode = M_SETTINGS; settingsScroll = 0.f; }
    else if (act == "layout") enterLayoutEditor();
    else if (act == "edone") { mode = M_SETTINGS; saveData(); }
    else if (act == "ereset") { hasCustom[0] = hasCustom[1] = false; relayout(); int o = portrait ? 1 : 0; for (int i = 0; i < NB; i++) { customPos[o][i][0] = BTN[i].cx / W; customPos[o][i][1] = BTN[i].cy / H; } hasCustom[o] = true; saveData(); }
    else if (act == "hand") {
        leftHand = !leftHand;
        for (int o = 0; o < 2; o++) if (hasCustom[o]) for (int i = 0; i < NB; i++) if (customPos[o][i][0] >= 0.f) customPos[o][i][0] = 1.f - customPos[o][i][0];
        relayout(); saveData();
    }
    else if (act == "sens-") { sensitivity = std::max(0.3f, sensitivity - 0.1f); saveData(); }
    else if (act == "sens+") { sensitivity = std::min(3.0f, sensitivity + 0.1f); saveData(); }
    else if (act == "invy") { invertY = !invertY; saveData(); }
    else if (act == "fps") { showFps = !showFps; saveData(); }
    else if (act == "sound") { soundOn = !soundOn; if (!soundOn) { stopAllSounds(); ambientOn = false; } else if (mode == M_PLAY) ambientStart(); saveData(); }
    else if (act == "autoq") { autoQ = !autoQ; saveData(); }
    else if (act == "aim") { aimAssist = !aimAssist; saveData(); }
    else if (act == "autofire") { autoFireOn = !autoFireOn; P->autoF = autoFireOn; saveData(); }
    else if (act == "tutok") { tutDone = true; saveData(); }
    else if (act == "diff") { difficulty = (difficulty + 1) % 3; saveData(); }
    else if (act == "resume") { paused = false; }
    else if (act == "size-") { btnScale = std::max(0.6f, btnScale - 0.1f); relayout(); saveData(); }
    else if (act == "size+") { btnScale = std::min(1.6f, btnScale + 0.1f); relayout(); saveData(); }
    else if (act == "quality") { quality = (quality + 1) % 3; relayout(); saveData(); }
    else if (act == "reset") { hasCustom[0] = hasCustom[1] = false; relayout(); saveData(); }
    else if (act == "skins") { mode = M_SKINS; skinsTab = 0; }
    else if (act.compare(0, 5, "wtab:") == 0) { skinsTab = std::max(0, std::min(NW - 1, atoi(act.c_str() + 5))); }
    else if (act.compare(0, 5, "sbuy:") == 0) {
        int s = atoi(act.c_str() + 5);
        if (s < 0 || s >= NSKINS) return;
        if (!skinOwned[skinsTab][s]) {
            int price = SKINS[s].price;
            if (coins < price) { toast(fmt("НУЖНО МОНЕТ: %d", price), 1.5f); return; }
            coins -= price; skinOwned[skinsTab][s] = true;
        }
        weaponSkin[skinsTab] = s; invalidateWeaponSprite(skinsTab); saveData();
    }
    else if (act == "connect") connectTo(ipStr);
    else if (act.compare(0, 5, "pick:") == 0) { ipStr = act.substr(5); connectTo(ipStr); }
    else if (act.compare(0, 4, "key:") == 0) {
        std::string k = act.substr(4);
        if (k == "<-") { if (!ipStr.empty()) ipStr.erase(ipStr.size() - 1); }
        else if (ipStr.size() < 15) ipStr += k;
    }
}
static void backToMenu() { shutdownNet(); duelMode = false; duelBot = false; mode = M_MENU; msgStr.clear(); }
static bool soloCanPause() { return mode == M_PLAY && !P->dead; }   // меню доступно и в сетевой игре (там игру оно не останавливает)
static void tdown(long long id, float x, float y) {
    if (confirmExit && mode == M_MENU) {
        layoutExitConfirm();
        for (size_t i = 0; i < ui.size(); i++) { const SDL_Rect& r = ui[i].r; if (x >= r.x && x < r.x + r.w && y >= r.y && y < r.y + r.h) { std::string act = ui[i].act; playSound(S_CLICK, 0.6f); uiAction(act); return; } }
        return;
    }
    if (paused && mode == M_PLAY) {
        layoutPause();
        for (size_t i = 0; i < ui.size(); i++) { const SDL_Rect& r = ui[i].r; if (x >= r.x && x < r.x + r.w && y >= r.y && y < r.y + r.h) { std::string act = ui[i].act; playSound(S_CLICK, 0.6f); uiAction(act); return; } }
        return;
    }
    if (!tutDone && mode == M_PLAY && !P->menu && !shopOpen) {
        SDL_Rect tr = tutBtnRect(); float pw = portrait ? 0.94f * W : 0.70f * W, ph = portrait ? 78 * U : 64 * U;
        if (x >= tr.x && x < tr.x + tr.w && y >= tr.y && y < tr.y + tr.h) { tutDone = true; saveData(); playSound(S_CLICK, 0.6f); return; }
        if (x >= (W - pw) / 2 && x < (W + pw) / 2 && y >= H / 2.f - ph / 2 && y < H / 2.f + ph / 2) return;      // тапы по карточке не проваливаются в игру
    }
    if (soloCanPause()) { SDL_Rect pr = pauseBtnRect(); if (x >= pr.x && x < pr.x + pr.w && y >= pr.y && y < pr.y + pr.h) { paused = true; touches.clear(); return; } }
    if (mode == M_SETTINGS) {
        settingsDragging = true; settingsDragId = id; settingsDragX0 = x; settingsDragY0 = y; settingsMoved = false;
        return;
    }
    if (mode == M_MENU || mode == M_JOIN || mode == M_LAYOUT || mode == M_SKINS || mode == M_DUEL || mode == M_QUESTS) {
        for (size_t i = 0; i < ui.size(); i++) {
            const SDL_Rect& r = ui[i].r;
            if (x >= r.x && x < r.x + r.w && y >= r.y && y < r.y + r.h) {
                std::string act = ui[i].act; playSound(S_CLICK, 0.6f);
                if (act.compare(0, 4, "key:") == 0) act = "key:" + ui[i].label;
                uiAction(act);
                return;
            }
        }
        if (mode == M_LAYOUT) {
            for (int b = 0; b < NB; b++) {
                if (b == B_AUTO) continue;      // больше не в игровом HUD
                if (hypotf(x - BTN[b].cx, y - BTN[b].cy) <= BTN[b].r * 1.2f) { dragBtn = b; dragId = id; break; }
            }
        }
        return;
    }
    if (mode == M_DEAD) { if (deadT <= 0) backToMenu(); return; }
    if (P->menu && !P->dead) {
        SDL_Rect rc[3]; cardRects(rc);
        for (int i = 0; i < 3; i++)
            if (x >= rc[i].x && x < rc[i].x + rc[i].w && y >= rc[i].y && y < rc[i].y + rc[i].h) {
                if (netRole == R_CLIENT) { netSend(link_, fmt("K %d", P->cards[i])); P->menu = false; pickT = 0.5f; }
                else applyUpgrade(*P, P->cards[i]);
                break;
            }
        return;
    }
    if (shopOpen) {
        for (size_t i = 0; i < ui.size(); i++) {
            const SDL_Rect& r = ui[i].r;
            if (x >= r.x && x < r.x + r.w && y >= r.y && y < r.y + r.h) { std::string act = ui[i].act; playSound(S_CLICK, 0.5f); shopAction(act); return; }
        }
        return;
    }
    for (int b = 0; b < NB; b++) {
        if (b == B_START && !prep) continue;
        if (b == B_AUTO) continue;      // перенесено в настройки
        if (hypotf(x - BTN[b].cx, y - BTN[b].cy) <= BTN[b].r * 1.2f) {
            Touch t = {id, 1, b, x, y, x, y}; touches.push_back(t); press(b); return;
        }
    }
    bool stick = portrait ? ((leftHand ? x > W * 0.5f : x < W * 0.5f) && y > H * 0.5f) : (leftHand ? x > W * 0.58f : x < W * 0.42f);
    Touch t = {id, stick ? 2 : 3, 0, x, y, x, y}; touches.push_back(t);
}
static void tmove(long long id, float x, float y, float dx, float dy) {
    if (mode == M_SETTINGS && id == settingsDragId) {
        settingsScroll = std::max(0.f, std::min(settingsMaxScroll, settingsScroll - dy));
        if (fabsf(x - settingsDragX0) > 6 * U || fabsf(y - settingsDragY0) > 6 * U) settingsMoved = true;
        return;
    }
    if (mode == M_LAYOUT && id == dragId && dragBtn >= 0) {
        int o = portrait ? 1 : 0; float r = BTN[dragBtn].r;
        x = std::max(r, std::min(W - r, x)); y = std::max(r, std::min(H - r, y));
        BTN[dragBtn].cx = x; BTN[dragBtn].cy = y; customPos[o][dragBtn][0] = x / W; customPos[o][dragBtn][1] = y / H;
        hasCustom[o] = true;         // раскладка стала «своей» только теперь — на реальном перетаскивании
        return;
    }
    for (size_t i = 0; i < touches.size(); i++)
        if (touches[i].id == id) {
            touches[i].x = x; touches[i].y = y;
            if (touches[i].role == 3 && mode == M_PLAY) {
                P->ang += dx / (float)W * LOOK_SENS * sensitivity;
                P->pitch += (invertY ? 1.f : -1.f) * dy / (float)W * LOOK_SENS * sensitivity * 0.9f;      // свайп вверх — смотреть вверх
                P->pitch = std::max(-PITCH_MAX, std::min(PITCH_MAX, P->pitch));
            }
        }
}
static void tup(long long id) {
    if (mode == M_SETTINGS && id == settingsDragId) {
        bool moved = settingsMoved; settingsDragging = false; settingsDragId = -2;
        if (!moved) {
            layoutSettings();
            for (size_t i = 0; i < ui.size(); i++) {
                const SDL_Rect& r = ui[i].r;
                if (settingsDragX0 >= r.x && settingsDragX0 < r.x + r.w && settingsDragY0 >= r.y && settingsDragY0 < r.y + r.h) {
                    std::string act = ui[i].act; playSound(S_CLICK, 0.6f); uiAction(act); break;
                }
            }
        }
        return;
    }
    if (id == dragId) { dragId = -2; dragBtn = -1; saveData(); return; }
    for (size_t i = 0; i < touches.size(); i++) if (touches[i].id == id) { touches.erase(touches.begin() + i); return; }
}

static void relayout();
static void mapPt(float px, float py, float* lx, float* ly) {
    if (!rotMode) { *lx = px; *ly = py; }
    else if (ROT_CW) { *lx = py; *ly = PW - px; }
    else { *lx = PH - py; *ly = px; }
}
static float mapDx(float dxp, float dyp) { return !rotMode ? dxp : (ROT_CW ? dyp : -dyp); }
static float mapDy(float dxp, float dyp) { return !rotMode ? dyp : (ROT_CW ? -dxp : dxp); }
static bool fingerSeen = false;
static bool handleEvents() {
    SDL_Event e;
    while (SDL_PollEvent(&e)) {
        switch (e.type) {
            case SDL_QUIT: return false;
            case SDL_APP_WILLENTERBACKGROUND: if (mode == M_PLAY && netRole == R_SOLO && peers.empty() && !P->dead) { paused = true; touches.clear(); } break;
            case SDL_WINDOWEVENT: if ((e.window.event == SDL_WINDOWEVENT_FOCUS_LOST || e.window.event == SDL_WINDOWEVENT_MINIMIZED) && mode == M_PLAY && netRole == R_SOLO && peers.empty() && !P->dead) { paused = true; touches.clear(); } break;
            case SDL_KEYDOWN: {
                SDL_Keycode k = e.key.keysym.sym;
                if (k == SDLK_AC_BACK || k == SDLK_p || k == SDLK_ESCAPE) {                 // «Назад» / P / Esc: пауза в игре, диалог выхода в меню
                    if (mode == M_MENU && confirmExit) { confirmExit = false; break; }
                    if (mode == M_PLAY && !P->dead) { paused = !paused; touches.clear(); break; }
                    if (mode == M_MENU && k != SDLK_p) { confirmExit = true; break; }
                    if (k == SDLK_ESCAPE) return false;
                    if (k == SDLK_AC_BACK) { if (mode == M_SETTINGS || mode == M_JOIN || mode == M_SKINS || mode == M_DUEL || mode == M_QUESTS) uiAction("menu"); else if (mode == M_LAYOUT) uiAction("edone"); break; }
                }
                if (mode == M_JOIN) {
                    if ((k >= SDLK_0 && k <= SDLK_9) || k == SDLK_PERIOD) uiAction(std::string("key:") + (char)k);
                    else if (k == SDLK_BACKSPACE) uiAction("key:<-");
                    else if (k == SDLK_RETURN) uiAction("connect");
                } else if (mode == M_MENU) { if (k == SDLK_RETURN || k == SDLK_SPACE) uiAction("solo"); }
                else if (mode == M_PLAY) {
                    if (k == SDLK_b) press(B_BUILD); else if (k == SDLK_m) press(B_SHOP); else if (k == SDLK_r) press(B_RELOAD); else if (k == SDLK_j) press(B_JUMP); else if (k == SDLK_g) press(B_GREN); else if (k == SDLK_h) press(B_STUN);
                    else if (k == SDLK_TAB || k == SDLK_x) press(B_WEAPON); else if (k == SDLK_RETURN) press(B_START);
                    else if (P->menu && (k == SDLK_1 || k == SDLK_2 || k == SDLK_3)) {
                        int i = k - SDLK_1;
                        if (netRole == R_CLIENT) { netSend(link_, fmt("K %d", P->cards[i])); P->menu = false; pickT = 0.5f; }
                        else applyUpgrade(*P, P->cards[i]);
                    }
                } else if (mode == M_DEAD && deadT <= 0) backToMenu();
                break;
            }
            case SDL_FINGERDOWN: { fingerSeen = true; float lx, ly; mapPt(e.tfinger.x * PW, e.tfinger.y * PH, &lx, &ly); tdown((long long)e.tfinger.fingerId, lx, ly); break; }
            case SDL_FINGERMOTION: { fingerSeen = true; float lx, ly; mapPt(e.tfinger.x * PW, e.tfinger.y * PH, &lx, &ly); tmove((long long)e.tfinger.fingerId, lx, ly, mapDx(e.tfinger.dx * PW, e.tfinger.dy * PH), mapDy(e.tfinger.dx * PW, e.tfinger.dy * PH)); break; }
            case SDL_FINGERUP: fingerSeen = true; tup((long long)e.tfinger.fingerId); break;
            case SDL_MOUSEBUTTONDOWN: if (!fingerSeen && e.button.which != SDL_TOUCH_MOUSEID) { float lx, ly; mapPt((float)e.button.x, (float)e.button.y, &lx, &ly); tdown(-1, lx, ly); } break;
            case SDL_MOUSEMOTION: if (!fingerSeen && e.motion.which != SDL_TOUCH_MOUSEID) { float lx, ly; mapPt((float)e.motion.x, (float)e.motion.y, &lx, &ly); tmove(-1, lx, ly, mapDx((float)e.motion.xrel, (float)e.motion.yrel), mapDy((float)e.motion.xrel, (float)e.motion.yrel)); } break;
            case SDL_MOUSEBUTTONUP: if (!fingerSeen && e.button.which != SDL_TOUCH_MOUSEID) tup(-1); break;
            case SDL_RENDER_DEVICE_RESET: case SDL_RENDER_TARGETS_RESET: relayout(); makeFont(); makeSprites(); break;
        }
    }
    return true;
}

// ============================ ОБНОВЛЕНИЕ ============================
static void localMove(float dt, float fwd, float strafe) {
    float m = hypotf(fwd, strafe);
    if (m > 1) { fwd /= m; strafe /= m; }
    float sp = 3.3f * P->spdMul * dt, ca = cosf(P->ang), sa = sinf(P->ang);
    if (m > 0) {
        static float stepAcc = 0; static bool stepFlip = false;
        float ox0 = P->x, oy0 = P->y;
        P->bob += dt; tryMove(P->x, P->y, P->x + (fwd * ca - strafe * sa) * sp, P->y + (fwd * sa + strafe * ca) * sp, 0.22f, P->jumpZ > 0.12f);
        stepAcc += hypotf(P->x - ox0, P->y - oy0);
        if (stepAcc > 0.95f) { stepAcc = 0; stepFlip = !stepFlip; playSound(stepFlip ? S_STEP1 : S_STEP2, 0.32f, 0.f, 0.94f + 0.12f * frand()); }
    }
    else P->bob = 0;
}
static void clientNet(float dt) {
    if (!linked) return;
    std::vector<std::string> ms; netRecv(link_, ms);
    for (size_t i = 0; i < ms.size(); i++) {
        const std::string& m = ms[i];
        if (m.empty()) continue;
        if (m[0] == 'H') { applyHello(m); waitT = 0; }
        else if (m[0] == 'S' && (mode == M_PLAY || mode == M_DEAD)) applySnap(m);
        else if (m[0] == 'T') { std::istringstream is(m.substr(2)); float d; is >> d; std::string rest; std::getline(is, rest); if (!rest.empty() && rest[0] == ' ') rest.erase(0, 1); toastS = rest; toastT = d; toastSound(rest); }
        else if (m[0] == 'F') { lostConnection("ИГРА ЗАПОЛНЕНА (МАКСИМУМ 4 ИГРОКА)"); return; }
    }
    if (!link_.alive) { lostConnection("СВЯЗЬ С ХОСТОМ ПОТЕРЯНА"); return; }
    if (mode == M_JOIN && waitT > 0) { waitT -= dt; if (waitT <= 0) { lostConnection("ХОСТ НЕ ОТВЕТИЛ"); return; } }
    if (mode == M_PLAY) {
        sendT -= dt;
        if (sendT <= 0) {
            sendT = 1.f / 20.f;
            bool fire = false;
            for (size_t i = 0; i < touches.size(); i++) if (touches[i].role == 1 && touches[i].btn == B_FIRE) fire = true;
            if (KEYS && KEYS[SDL_SCANCODE_SPACE]) fire = true;
            netSend(link_, fmt("I %.3f %.3f %.3f %d %d %.3f", P->x, P->y, P->ang, (fire && !P->dead) ? 1 : 0, P->autoF ? 1 : 0, P->pitch));
        }
    }
    netFlush(link_);
    float k = std::min(1.f, dt * 14.f);
    for (std::map<int, Player>::iterator it = players.begin(); it != players.end(); ++it)
        if (&it->second != P) { it->second.x += (it->second.tx - it->second.x) * k; it->second.y += (it->second.ty - it->second.y) * k; it->second.flash = std::max(0.f, it->second.flash - dt); }
    for (size_t i = 0; i < zombies.size(); i++) {
        zombies[i].x += (zombies[i].tx - zombies[i].x) * k; zombies[i].y += (zombies[i].ty - zombies[i].y) * k;
        if (zombies[i].flash > 0) zombies[i].flash -= dt;
    }
}
static void update(float dt) {
    if (paused && mode == M_PLAY && netRole == R_SOLO && peers.empty()) return;   // замирает только одиночная игра                 // пауза: всё замирает
    if (toastT > 0) toastT -= dt;
    pickT = std::max(0.f, pickT - dt);
    updateParts(dt);
    if (mode == M_JOIN) { pollDiscovery(); if (netRole == R_CLIENT) clientNet(dt); return; }
    if (mode == M_DEAD) { deadT -= dt; P->hurt = std::max(P->hurt, 0.2f); return; }
    if (mode != M_PLAY) { shopOpen = false; return; }
    if (P->dead) shopOpen = false;
    float fwd = 0, strafe = 0; bool fire = false;
    for (size_t i = 0; i < touches.size(); i++) {
        if (touches[i].role == 2) { float vx, vy; stickVec(touches[i], &vx, &vy); strafe += vx; fwd -= vy; }
        else if (touches[i].role == 1 && touches[i].btn == B_FIRE) fire = true;
    }
    if (KEYS) {
        if (KEYS[SDL_SCANCODE_W] || KEYS[SDL_SCANCODE_UP]) fwd += 1;
        if (KEYS[SDL_SCANCODE_S] || KEYS[SDL_SCANCODE_DOWN]) fwd -= 1;
        if (KEYS[SDL_SCANCODE_D]) strafe += 1;
        if (KEYS[SDL_SCANCODE_A]) strafe -= 1;
        if (KEYS[SDL_SCANCODE_RIGHT] || KEYS[SDL_SCANCODE_E]) P->ang += 2.2f * dt;
        if (KEYS[SDL_SCANCODE_LEFT] || KEYS[SDL_SCANCODE_Q]) P->ang -= 2.2f * dt;
        if (KEYS[SDL_SCANCODE_SPACE]) fire = true;
    }
    if (aimAssist && (fire || P->flash > 0.02f) && !P->dead && !P->menu && !shopOpen) {     // мягкая помощь: при стрельбе доворачивает к ближайшему зомби
        float bestA = 0.13f, bd = 0; bool found = false;
        for (size_t i = 0; i < zombies.size(); i++) {
            float ddx = zombies[i].x - P->x, ddy = zombies[i].y - P->y, dist = sqrtf(ddx * ddx + ddy * ddy);
            if (dist < 0.7f || dist > 12.f) continue;
            float ta = atan2f(ddy, ddx), da = ta - P->ang; while (da > 3.14159f) da -= 6.28318f; while (da < -3.14159f) da += 6.28318f;
            if (fabsf(da) < bestA && wallDist(P->x, P->y, ta) > dist - 0.4f) { bestA = fabsf(da); bd = da; found = true; }
        }
        if (found) P->ang += std::max(-2.4f * dt, std::min(2.4f * dt, bd));
    }
    if (netRole == R_CLIENT) {
        if (!P->dead && !P->menu) localMove(dt, fwd, strafe); else P->bob = 0;
        P->flash = std::max(0.f, P->flash - dt); P->hurt = std::max(0.f, P->hurt - dt); P->hit = std::max(0.f, P->hit - dt); P->headT = std::max(0.f, P->headT - dt);
        updateJumpPhysics(*P, dt);
        clientNet(dt);
        trackEffects();
        return;
    }
    if (peers.empty() && (P->menu || shopOpen)) return;    // пауза на время выбора улучшения (одиночная игра)
    if (!P->dead && !P->menu) localMove(dt, fwd, strafe); else P->bob = 0;
    P->fire = fire && !P->dead && !P->menu;
    simUpdate(dt);
    trackEffects();
    if (netRole == R_HOST) hostNet(dt);
}

// ============================ ЭКРАН / ЗАПУСК ============================
static void relayout() {
    SDL_GetRendererOutputSize(ren, &PW, &PH);
    if (rt) { SDL_DestroyTexture(rt); rt = NULL; }
    // если ориентация окна не совпадает с желаемой — рисуем повёрнутым на 90 градусов
    rotMode = (LANDSCAPE != (PW > PH)) && PW != PH;
    if (rotMode) {
        W = PH; H = PW;
        rt = SDL_CreateTexture(ren, SDL_PIXELFORMAT_ARGB8888, SDL_TEXTUREACCESS_TARGET, W, H);
        if (!rt) { rotMode = false; W = PW; H = PH; }
    } else { W = PW; H = PH; }
    portrait = H > W;
    U = portrait ? W / 100.f : std::min(H / 100.f, W / 178.f);
    { static const float QF[3] = {1.f / 11.f, 1.f / 9.f, 1.f / 7.5f}; RW = std::max(90, std::min(300, (int)(W * QF[std::max(0, std::min(2, quality))]))); }
    float fov = portrait ? FOV_PORT : FOV_LAND;
    TANH_ = tanf(fov * 3.14159265f / 360.f);
    FOCAL = (W / 2.f) / TANH_;
    for (int i = 0; i < RW; i++) CAMX[i] = 2.f * (i + 0.5f) / RW - 1.f;
    clearBtnCache();
    makeBtnLayout();
    for (int i = 0; i < NB; i++) if (i != B_AUTO && BTN[i].r >= 1.f) { getBtnTex(i, false); getBtnTex(i, true); }   // готовим кнопки заранее — без подвиса при первом касании
    mmDirty = true;
    setWeaponQuality();
    if (quality > 0) makeHiWallTex();      // при переходе с «Низкой» на «Среднюю/Высокую» — готовим крупные стены
    // буфер пола (рисуется в малом разрешении и растягивается)
    { static const float FQ[3] = {1.f, 1.3f, 1.4f}; FLW = std::min(1000, (int)ceilf(RW * FQ[std::max(0, std::min(2, quality))])); }   // клеток пола: на «Средней/Высокой» заметно больше, чем лучей
    FLPX = (float)W / FLW; FLH = (int)((H / 2.f + tanf(PITCH_MAX) * FOCAL + 90) / FLPX) + 2;
    floorBuf.assign((size_t)FLW * FLH, 0xFF000000u);
    floorValid = false;
    if (FLOORTEX) SDL_DestroyTexture(FLOORTEX);
    SDL_SetHint(SDL_HINT_RENDER_SCALE_QUALITY, "1");
    FLOORTEX = SDL_CreateTexture(ren, SDL_PIXELFORMAT_ARGB8888, SDL_TEXTUREACCESS_STREAMING, FLW, FLH);
    // ближний слой пола с мелкими пикселями
    if (FLOORTEX2) { SDL_DestroyTexture(FLOORTEX2); FLOORTEX2 = NULL; }
    floorBuf2.clear(); FLW2 = FLH2 = 0; NEAR_OFF = 1e7f;   // мелкий слой пола под ногами убран совсем: каждый кадр он заново загружал в GPU сотни тысяч пикселей — самый дорогой пункт кадра на реальном телефоне
    SDL_SetHint(SDL_HINT_RENDER_SCALE_QUALITY, "0");
}

static float fpsAvg = 60.f, msFrame = 16.f, msUpd = 0.f, msRen = 0.f, msPres = 0.f;
static void drawFpsOverlay() {
    if (!showFps) return;
    int px = std::max(2, (int)(std::min(W, H) * 0.30f / N));
    float y = (mode == M_PLAY) ? 2 * U + N * px + 1.5f * U : 2 * U, x = W - 2 * U;
    static float acc = 1.f; static std::string s1, s2;
    acc += gDt;
    if (acc >= 0.25f || s1.empty()) { acc = 0.f; s1 = fmt("FPS %d", (int)(fpsAvg + 0.5f)); s2 = fmt("%.0f/%.0f/%.0f/%.0f МС", msUpd, msRen, msPres, std::max(0.f, msFrame - msUpd - msRen - msPres)); }
    Col col = fpsAvg >= 45 ? C(120, 255, 140) : (fpsAvg >= 28 ? C(255, 220, 90) : C(255, 90, 80));
    fillRect(x - textW("FPS 000", FS(), W * 0.3f) - 1.5f * U, y - 0.6f * U, textW("FPS 000", FS(), W * 0.3f) + 2.4f * U, 2 * textH(FS()) + 2.8f * U, C(0, 0, 0, 120));
    drawText(s1, x, y, FS(), col, A_TR, W * 0.3f);
    drawText(s2, x, y + textH(FS()) + 0.8f * U, FS() * 0.75f, C(200, 210, 230), A_TR, W * 0.3f);   // обновление / отрисовка / показ / прочее
}
static void drawPauseIfNeeded() { if (paused && mode == M_PLAY) drawPause(); }
static void renderScreen() {
    textFrame++;
    if (rotMode && rt) {
        SDL_SetRenderTarget(ren, rt);
        setCol(C(0, 0, 0)); SDL_RenderClear(ren);
        drawFrame(); drawPauseIfNeeded(); drawFpsOverlay();
        SDL_SetRenderTarget(ren, NULL);
        setCol(C(0, 0, 0)); SDL_RenderClear(ren);
        SDL_Rect dst = {PW / 2 - W / 2, PH / 2 - H / 2, W, H};
        SDL_RenderCopyEx(ren, rt, NULL, &dst, ROT_CW ? 90.0 : 270.0, NULL, SDL_FLIP_NONE);
    } else {
        setCol(C(0, 0, 0)); SDL_RenderClear(ren);
        drawFrame(); drawPauseIfNeeded(); drawFpsOverlay();
    }
}

int main(int argc, char* argv[]) {
    (void)argc; (void)argv;
    signal(SIGPIPE, SIG_IGN);
    rngs ^= (u32)SDL_GetTicks() * 2654435761u; if (!rngs) rngs = 1;
#ifdef SDL_HINT_ORIENTATIONS
    SDL_SetHint(SDL_HINT_ORIENTATIONS, LANDSCAPE ? "LandscapeLeft LandscapeRight" : "Portrait");
#endif
#ifdef SDL_HINT_TOUCH_MOUSE_EVENTS
    SDL_SetHint(SDL_HINT_TOUCH_MOUSE_EVENTS, "0");
#endif
    SDL_SetHint(SDL_HINT_RENDER_SCALE_QUALITY, "0");
    if (SDL_Init(SDL_INIT_VIDEO | SDL_INIT_TIMER) != 0) { printf("SDL_Init: %s\n", SDL_GetError()); return 1; }
    win = SDL_CreateWindow("Zombie Siege 3D", SDL_WINDOWPOS_UNDEFINED, SDL_WINDOWPOS_UNDEFINED, 960, 540, SDL_WINDOW_SHOWN | SDL_WINDOW_FULLSCREEN_DESKTOP);
    if (!win) { printf("Window: %s\n", SDL_GetError()); return 1; }
    ren = SDL_CreateRenderer(win, -1, SDL_RENDERER_ACCELERATED | SDL_RENDERER_PRESENTVSYNC);
    if (!ren) ren = SDL_CreateRenderer(win, -1, SDL_RENDERER_SOFTWARE);
    if (!ren) { printf("Renderer: %s\n", SDL_GetError()); return 1; }
    initTables(); loadData(); ensureDaily();
    initAudio();
    relayout(); makeFont(); makeSprites();
    mode = M_MENU; P = &players[0];
    KEYS = SDL_GetKeyboardState(NULL);
    Uint32 last = SDL_GetTicks();
    bool running = true;
    const double pf = 1000.0 / (double)SDL_GetPerformanceFrequency();
    float lowT = 0, playT = 0;
    while (running) {
        Uint32 now = SDL_GetTicks();
        float dt = std::min(0.05f, (now - last) / 1000.f); last = now; gDt = dt;
        float frameMs = std::max(1.f, (float)(dt * 1000.f));
        if (dt > 0) { fpsAvg += (1.f / dt - fpsAvg) * 0.06f; msFrame += (frameMs - msFrame) * 0.06f; }
        if (mode == M_MENU || mode == M_SETTINGS || mode == M_JOIN) prerenderStep(10);   // готовим спрайты оружия, пока ты в меню (в игре не трогаем — там нужный спрайт строится сам, понемногу)
        running = handleEvents() && !wantQuit;
        int nw, nh; SDL_GetRendererOutputSize(ren, &nw, &nh);
        if (nw != PW || nh != PH) relayout();
        Uint64 t0 = SDL_GetPerformanceCounter();
        update(dt);
        Uint64 t1 = SDL_GetPerformanceCounter();
        renderScreen();
        Uint64 t2 = SDL_GetPerformanceCounter();
        SDL_RenderPresent(ren);
        Uint64 t3 = SDL_GetPerformanceCounter();
        msUpd += ((float)((t1 - t0) * pf) - msUpd) * 0.08f; msRen += ((float)((t2 - t1) * pf) - msRen) * 0.08f; msPres += ((float)((t3 - t2) * pf) - msPres) * 0.08f;
        // автоснижение графики, если стабильно меньше ~24 кадров в секунду
        if (mode == M_PLAY) playT += dt; else { playT = 0; lowT = 0; }
        if (autoQ && mode == M_PLAY && quality > 0 && playT > 6.f) {
            if (fpsAvg < 24.f) lowT += dt; else lowT = std::max(0.f, lowT - dt * 2.f);
            if (lowT > 3.f) {
                quality--; relayout(); saveData(); lowT = 0; fpsAvg = 30.f;
                toast(std::string("ГРАФИКА СНИЖЕНА ДЛЯ ПЛАВНОСТИ: ") + QNAME[quality], 3.5f);
            }
        } else lowT = 0;
        { Uint32 el = SDL_GetTicks() - now; if (el < 8) SDL_Delay(8 - el); }   // спим только недостающее до 8 мс, а не лишние 8
    }
    shutdownNet();
    SDL_Quit();
    return 0;
}
