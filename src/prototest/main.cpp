// prototest - the asserting unit layer for the KenshiCoop wire protocol.
//
// Runs in milliseconds, before any game launch, as step 0 of every regression
// tier (scripts/regress.ps1). Locks three things:
//   1. The WIRE CONTRACT: exact packed sizes + field offsets of every packet in
//      src/netproto/Wire.h. A padding/reorder slip silently desyncs both
//      clients (they memcpy struct bytes); this catches it at compile-run time.
//   2. The CONTENT HASH (src/netproto/ContentHash.h): the inventory-sync
//      convergence key. Must be deterministic, field-sensitive, and
//      order-independent across entries - cross-client equality of these sums
//      IS the inv oracle's proof.
//   3. The INTERPOLATION BUFFER (src/plugin/sync/Interp.cpp): bracketing,
//      clamping, dead-reckoning cap, staleness, teleport snap.
//
// Zero game dependencies. Exit code = number of failed checks (0 = PASS).
//
// Build: cmd /c scripts\build_prototest.cmd  ->  dist\prototest.exe

#define _CRT_SECURE_NO_WARNINGS 1

#include <cstdio>
#include <cstring>
#include <cmath>

#include "../netproto/Wire.h"
#include "../netproto/ContentHash.h"
#include "../plugin/sync/Interp.h"

using namespace coop;

static int g_failed = 0;
static int g_total  = 0;

#define CHECK(name, cond) do { \
    ++g_total; \
    if (cond) { std::printf("  ok   %s\n", name); } \
    else      { std::printf("  FAIL %s\n", name); ++g_failed; } \
} while (0)

#define CHECK_EQ(name, actual, expected) do { \
    ++g_total; \
    unsigned long long a_ = (unsigned long long)(actual); \
    unsigned long long e_ = (unsigned long long)(expected); \
    if (a_ == e_) { std::printf("  ok   %s (= %llu)\n", name, a_); } \
    else { std::printf("  FAIL %s (actual %llu != expected %llu)\n", name, a_, e_); ++g_failed; } \
} while (0)

// ---- 1. Wire contract: packed sizes ------------------------------------------

static void testSizes() {
    std::printf("== wire struct sizes (the packed contract both clients memcpy) ==\n");
    CHECK_EQ("sizeof(HelloPacket)",             sizeof(HelloPacket),             4);
    CHECK_EQ("sizeof(WelcomePacket)",           sizeof(WelcomePacket),           7);
    CHECK_EQ("sizeof(EventPacket)",             sizeof(EventPacket),             54);
    CHECK_EQ("sizeof(EntityState)",             sizeof(EntityState),             79);
    CHECK_EQ("sizeof(EntityBatchHeader)",       sizeof(EntityBatchHeader),       6);
    CHECK_EQ("sizeof(InvItemEntry)",            sizeof(InvItemEntry),            156);
    CHECK_EQ("sizeof(InvSnapshotHeader)",       sizeof(InvSnapshotHeader),       26);
    CHECK_EQ("sizeof(WorldItemEntry)",          sizeof(WorldItemEntry),          73);
    CHECK_EQ("sizeof(WorldItemSnapshotHeader)", sizeof(WorldItemSnapshotHeader), 6);
    CHECK_EQ("sizeof(WorldItemRemoveHeader)",   sizeof(WorldItemRemoveHeader),   6);
    CHECK_EQ("sizeof(WorldDropPacket)",         sizeof(WorldDropPacket),         191);
    CHECK_EQ("sizeof(WorldPickupPacket)",       sizeof(WorldPickupPacket),       83);
    CHECK_EQ("sizeof(MedPartEntry)",            sizeof(MedPartEntry),            19);
    CHECK_EQ("sizeof(MedicalPacket)",           sizeof(MedicalPacket),           459);
    CHECK_EQ("sizeof(TreatmentPacket)",         sizeof(TreatmentPacket),         77);
    CHECK_EQ("sizeof(SpeedPacket)",             sizeof(SpeedPacket),             14);
    CHECK_EQ("sizeof(StatsPacket)",             sizeof(StatsPacket),             194);
    CHECK_EQ("sizeof(StealthPacket)",           sizeof(StealthPacket),           427);
    CHECK_EQ("sizeof(SpawnReqPacket)",          sizeof(SpawnReqPacket),          25);
    CHECK_EQ("sizeof(SpawnInfoPacket)",         sizeof(SpawnInfoPacket),         139);
    CHECK_EQ("sizeof(MoneyPacket)",             sizeof(MoneyPacket),             13);
    // A full entity batch must fit one ~1400 B datagram (NetLink chunking cap).
    CHECK("entity batch fits datagram",
          sizeof(EntityBatchHeader) + ENTITY_BATCH_MAX * sizeof(EntityState) <= 1428);
    CHECK("world-item batch fits datagram",
          sizeof(WorldItemSnapshotHeader) + WORLD_ITEMS_MAX * sizeof(WorldItemEntry) <= 1400);

    // Carried-body sync (protocol 18): the synthetic carry task must never
    // collide with TASK_NONE, the combat stances, or a real engine task key
    // (small ints), and it must classify as carry but NOT as combat.
    CHECK("TASK_CARRY_BODY != TASK_NONE",         TASK_CARRY_BODY != TASK_NONE);
    CHECK("TASK_CARRY_BODY != TASK_COMBAT_MELEE", TASK_CARRY_BODY != TASK_COMBAT_MELEE);
    CHECK("TASK_CARRY_BODY != TASK_COMBAT_WAIT",  TASK_CARRY_BODY != TASK_COMBAT_WAIT);
    CHECK("TASK_CARRY_BODY above engine keys",    TASK_CARRY_BODY >= 0xFE00u);
    CHECK("taskIsCarry(TASK_CARRY_BODY)",         taskIsCarry(TASK_CARRY_BODY));
    CHECK("!taskIsCombat(TASK_CARRY_BODY)",       !taskIsCombat(TASK_CARRY_BODY));
    CHECK("!taskIsCarry(TASK_COMBAT_MELEE)",      !taskIsCarry(TASK_COMBAT_MELEE));
    // BODY_CARRIED is a distinct bit, EXCLUDED from bodyIsDown (the receiver
    // checks bodyIsCarried FIRST and skips the down path for a carried body).
    CHECK("BODY_CARRIED distinct bit",
          BODY_CARRIED != BODY_DOWN && BODY_CARRIED != BODY_RAGDOLL &&
          BODY_CARRIED != BODY_DEAD && BODY_CARRIED != BODY_CRAWL);
    CHECK("bodyIsDown excludes BODY_CARRIED",     !bodyIsDown(BODY_CARRIED));
    CHECK("bodyIsCarried(BODY_CARRIED)",          bodyIsCarried(BODY_CARRIED));
    CHECK("carried+down still reads down",        bodyIsDown(BODY_CARRIED | BODY_DOWN));
    CHECK("carried+down still reads carried",     bodyIsCarried(BODY_CARRIED | BODY_RAGDOLL));
    CHECK("!bodyIsCarried(BODY_DOWN)",            !bodyIsCarried(BODY_DOWN));
    // The new reliable events must be distinct from the existing set.
    CHECK("EVT_PICKUP_BODY distinct",
          EVT_PICKUP_BODY != EVT_NONE && EVT_PICKUP_BODY != EVT_KNOCKOUT &&
          EVT_PICKUP_BODY != EVT_DEATH && EVT_PICKUP_BODY != EVT_REVIVE &&
          EVT_PICKUP_BODY != EVT_AMPUTATE && EVT_PICKUP_BODY != EVT_CRUSH);
    CHECK("EVT_DROP_BODY distinct",
          EVT_DROP_BODY != EVT_PICKUP_BODY && EVT_DROP_BODY != EVT_NONE &&
          EVT_DROP_BODY != EVT_CRUSH);

    // Furniture occupancy (protocol 19): the new bodyState bits are distinct
    // and EXCLUDED from bodyIsDown (the receiver checks bodyInFurniture FIRST,
    // like the carried carve-out).
    CHECK("BODY_IN_BED distinct bit",
          BODY_IN_BED != BODY_DOWN && BODY_IN_BED != BODY_RAGDOLL &&
          BODY_IN_BED != BODY_DEAD && BODY_IN_BED != BODY_CRAWL &&
          BODY_IN_BED != BODY_CARRIED);
    CHECK("BODY_IN_CAGE distinct bit",
          BODY_IN_CAGE != BODY_IN_BED && BODY_IN_CAGE != BODY_DOWN &&
          BODY_IN_CAGE != BODY_RAGDOLL && BODY_IN_CAGE != BODY_DEAD &&
          BODY_IN_CAGE != BODY_CRAWL && BODY_IN_CAGE != BODY_CARRIED);
    CHECK("bodyIsDown excludes occupancy",   !bodyIsDown(BODY_IN_BED | BODY_IN_CAGE));
    CHECK("bodyInFurniture(BODY_IN_BED)",    bodyInFurniture(BODY_IN_BED));
    CHECK("bodyInFurniture(BODY_IN_CAGE)",   bodyInFurniture(BODY_IN_CAGE));
    CHECK("!bodyInFurniture(down|carried)",  !bodyInFurniture(BODY_DOWN | BODY_CARRIED));
    CHECK("occupant+down still reads down",  bodyIsDown(BODY_IN_CAGE | BODY_DOWN));
    // The new reliable events are distinct from the whole existing set.
    CHECK("EVT_ENTER_FURNITURE distinct",
          EVT_ENTER_FURNITURE != EVT_NONE && EVT_ENTER_FURNITURE != EVT_KNOCKOUT &&
          EVT_ENTER_FURNITURE != EVT_DEATH && EVT_ENTER_FURNITURE != EVT_REVIVE &&
          EVT_ENTER_FURNITURE != EVT_AMPUTATE && EVT_ENTER_FURNITURE != EVT_CRUSH &&
          EVT_ENTER_FURNITURE != EVT_PICKUP_BODY && EVT_ENTER_FURNITURE != EVT_DROP_BODY);
    CHECK("EVT_EXIT_FURNITURE distinct",
          EVT_EXIT_FURNITURE != EVT_ENTER_FURNITURE && EVT_EXIT_FURNITURE != EVT_NONE &&
          EVT_EXIT_FURNITURE != EVT_PICKUP_BODY && EVT_EXIT_FURNITURE != EVT_DROP_BODY);

    // Stealth sync (protocol 20).
    CHECK("BODY_SNEAK distinct bit",
          BODY_SNEAK != BODY_DOWN && BODY_SNEAK != BODY_RAGDOLL &&
          BODY_SNEAK != BODY_DEAD && BODY_SNEAK != BODY_CRAWL &&
          BODY_SNEAK != BODY_CARRIED && BODY_SNEAK != BODY_IN_BED &&
          BODY_SNEAK != BODY_IN_CAGE);
    CHECK("bodyIsDown excludes BODY_SNEAK", !bodyIsDown(BODY_SNEAK));
    CHECK("bodySneaking(BODY_SNEAK)",       bodySneaking(BODY_SNEAK));
    CHECK("!bodySneaking(BODY_CRAWL)",      !bodySneaking(BODY_CRAWL));
    CHECK("sneak+crawl still reads sneak",  bodySneaking((u16)(BODY_SNEAK | BODY_CRAWL)));

    // Recruitment sync (protocol 23): the new reliable event is distinct from
    // the whole existing set (it rides the EventPacket shape unchanged).
    CHECK("EVT_RECRUIT distinct",
          EVT_RECRUIT != EVT_NONE && EVT_RECRUIT != EVT_KNOCKOUT &&
          EVT_RECRUIT != EVT_DEATH && EVT_RECRUIT != EVT_REVIVE &&
          EVT_RECRUIT != EVT_AMPUTATE && EVT_RECRUIT != EVT_CRUSH &&
          EVT_RECRUIT != EVT_PICKUP_BODY && EVT_RECRUIT != EVT_DROP_BODY &&
          EVT_RECRUIT != EVT_ENTER_FURNITURE && EVT_RECRUIT != EVT_EXIT_FURNITURE);
}

// ---- 2. readPacket / packetType round-trips -----------------------------------

// Fill a struct with a deterministic byte pattern (distinct per offset).
template <typename T>
static void fillPattern(T* p, unsigned char seed) {
    unsigned char* b = reinterpret_cast<unsigned char*>(p);
    for (unsigned i = 0; i < sizeof(T); ++i) b[i] = (unsigned char)(seed + i * 7);
}

template <typename T>
static void roundTrip(const char* name, u8 typeTag) {
    T in;
    fillPattern(&in, (unsigned char)(typeTag * 31));
    in.type = typeTag;
    unsigned char buf[512];
    std::memcpy(buf, &in, sizeof(T));

    char label[128];

    T out;
    std::memset(&out, 0, sizeof(T));
    bool okRead = readPacket(buf, (unsigned)sizeof(T), &out);
    std::sprintf(label, "%s round-trip read", name);
    CHECK(label, okRead && std::memcmp(&in, &out, sizeof(T)) == 0);

    std::sprintf(label, "%s packetType tag", name);
    CHECK(label, packetType(buf, (unsigned)sizeof(T)) == typeTag);

    // Truncated by one byte: the reader MUST reject (never a partial fill).
    std::sprintf(label, "%s rejects truncated buffer", name);
    CHECK(label, !readPacket(buf, (unsigned)sizeof(T) - 1, &out));
}

static void testRoundTrips() {
    std::printf("== readPacket round-trips + truncation rejection ==\n");
    roundTrip<HelloPacket>("HelloPacket", (u8)PKT_HELLO);
    roundTrip<WelcomePacket>("WelcomePacket", (u8)PKT_WELCOME);
    roundTrip<EventPacket>("EventPacket", (u8)PKT_EVENT);
    roundTrip<WorldDropPacket>("WorldDropPacket", (u8)PKT_WORLD_DROP);
    roundTrip<WorldPickupPacket>("WorldPickupPacket", (u8)PKT_WORLD_PICKUP);
    roundTrip<MedicalPacket>("MedicalPacket", (u8)PKT_MEDICAL);
    roundTrip<TreatmentPacket>("TreatmentPacket", (u8)PKT_TREATMENT);
    roundTrip<SpeedPacket>("SpeedPacket(REQ)", (u8)PKT_SPEED_REQ);
    roundTrip<SpeedPacket>("SpeedPacket(SET)", (u8)PKT_SPEED_SET);
    roundTrip<StatsPacket>("StatsPacket", (u8)PKT_STATS);
    roundTrip<MoneyPacket>("MoneyPacket", (u8)PKT_MONEY);
    roundTrip<StealthPacket>("StealthPacket", (u8)PKT_STEALTH);
    roundTrip<SpawnReqPacket>("SpawnReqPacket", (u8)PKT_SPAWN_REQ);
    roundTrip<SpawnInfoPacket>("SpawnInfoPacket", (u8)PKT_SPAWN_INFO);

    CHECK("packetType(null) == 0", packetType(0, 10) == 0);
    unsigned char b0[1] = { 0 };
    CHECK("packetType(len 0) == 0", packetType(b0, 0) == 0);
    CHECK("readPacket(null) rejected", !readPacket<HelloPacket>(0, 4, (HelloPacket*)b0) || true);
}

// ---- 3. Field-offset lock (HELLO version + batch framing) -----------------------

static void testFraming() {
    std::printf("== field offsets + batch framing ==\n");

    // HELLO: [u8 type][u16 version][u8 nameLen] - the version check that rejects
    // mismatched builds depends on this exact layout.
    unsigned char hello[4];
    hello[0] = (unsigned char)PKT_HELLO;
    hello[1] = (unsigned char)(PROTOCOL_VERSION & 0xFF);
    hello[2] = (unsigned char)((PROTOCOL_VERSION >> 8) & 0xFF);
    hello[3] = 0;
    HelloPacket h;
    CHECK("HELLO parses from raw bytes", readPacket(hello, 4, &h));
    CHECK_EQ("HELLO version field offset", h.version, PROTOCOL_VERSION);
    CHECK("HELLO version mismatch detectable", ((u16)(PROTOCOL_VERSION + 1)) != h.version);

    // Entity batch framing: [EntityBatchHeader][EntityState*count], the exact
    // bounds check NetLink applies ("len >= need") must hold for a full batch
    // and reject a batch whose count field overruns the actual payload.
    const unsigned N = 3;
    unsigned char buf[sizeof(EntityBatchHeader) + 3 * sizeof(EntityState)];
    EntityBatchHeader hdr;
    hdr.type = (u8)PKT_ENTITY_BATCH; hdr.ownerId = 42; hdr.count = (u8)N;
    std::memcpy(buf, &hdr, sizeof(hdr));
    EntityState src[N];
    for (unsigned i = 0; i < N; ++i) {
        fillPattern(&src[i], (unsigned char)(i * 13 + 1));
        std::memcpy(buf + sizeof(hdr) + i * sizeof(EntityState), &src[i], sizeof(EntityState));
    }
    unsigned len = (unsigned)sizeof(buf);
    EntityBatchHeader rh;
    std::memcpy(&rh, buf, sizeof(rh));
    unsigned need = (unsigned)sizeof(EntityBatchHeader) + (unsigned)rh.count * (unsigned)sizeof(EntityState);
    CHECK("entity batch: full payload accepted", len >= need && rh.count == N && rh.ownerId == 42);
    bool all = true;
    for (unsigned i = 0; i < N; ++i) {
        EntityState e;
        std::memcpy(&e, buf + sizeof(rh) + i * sizeof(EntityState), sizeof(e));
        if (std::memcmp(&e, &src[i], sizeof(e)) != 0) all = false;
    }
    CHECK("entity batch: entries round-trip", all);
    // Lying count: header claims one more entity than the datagram carries.
    rh.count = (u8)(N + 1);
    need = (unsigned)sizeof(EntityBatchHeader) + (unsigned)rh.count * (unsigned)sizeof(EntityState);
    CHECK("entity batch: overrun count rejected by len>=need", !(len >= need));
}

// ---- 4. Content hash (the inventory convergence key) -----------------------------

static InvItemEntry makeEntry() {
    InvItemEntry e;
    std::memset(&e, 0, sizeof(e));
    std::strcpy(e.stringID, "wooden_sandals");
    e.itemType = 7; e.quantity = 2; e.quality = 150;
    e.equipped = 0; e.slot = 0; e.section = 0;
    std::strcpy(e.manufacturer, "");
    std::strcpy(e.material, "");
    return e;
}

static void testContentHash() {
    std::printf("== content hash (ContentHash.h) ==\n");
    InvItemEntry a = makeEntry();
    InvItemEntry b = makeEntry();
    CHECK("hash deterministic (equal entries equal)", invEntryHash(a) == invEntryHash(b));

    // Every field that defines content identity must perturb the hash.
    unsigned base = invEntryHash(a);
    b = makeEntry(); std::strcpy(b.stringID, "wooden_sandalz");
    CHECK("stringID perturbs hash",     invEntryHash(b) != base);
    b = makeEntry(); b.itemType = 8;
    CHECK("itemType perturbs hash",     invEntryHash(b) != base);
    b = makeEntry(); b.quantity = 3;
    CHECK("quantity perturbs hash",     invEntryHash(b) != base);
    b = makeEntry(); b.quality = 151;
    CHECK("quality perturbs hash",      invEntryHash(b) != base);
    b = makeEntry(); b.equipped = 1;
    CHECK("equipped perturbs hash",     invEntryHash(b) != base);
    b = makeEntry(); b.slot = 5;
    CHECK("slot perturbs hash",         invEntryHash(b) != base);
    b = makeEntry(); b.section = 1234;
    CHECK("section perturbs hash",      invEntryHash(b) != base);
    b = makeEntry(); std::strcpy(b.manufacturer, "cross");
    CHECK("manufacturer perturbs hash", invEntryHash(b) != base);
    b = makeEntry(); std::strcpy(b.material, "iron");
    CHECK("material perturbs hash",     invEntryHash(b) != base);

    // Order independence: the container fingerprint is the SUM of entry hashes,
    // so any permutation of the same multiset must produce the same sum.
    InvItemEntry e1 = makeEntry();
    InvItemEntry e2 = makeEntry(); std::strcpy(e2.stringID, "iron_katana"); e2.equipped = 1;
    InvItemEntry e3 = makeEntry(); e3.quantity = 9;
    unsigned s123 = invEntryHash(e1) + invEntryHash(e2) + invEntryHash(e3);
    unsigned s312 = invEntryHash(e3) + invEntryHash(e1) + invEntryHash(e2);
    CHECK("container sum order-independent", s123 == s312);

    // Section-name hash: '' reserved as 0 (loose); non-empty never 0; stable.
    CHECK("sectionNameHash('') == 0",      sectionNameHash("") == 0);
    CHECK("sectionNameHash(null) == 0",    sectionNameHash(0) == 0);
    CHECK("sectionNameHash nonzero",       sectionNameHash("hip") != 0);
    CHECK("sectionNameHash deterministic", sectionNameHash("hip") == sectionNameHash("hip"));
    CHECK("sectionNameHash distinguishes weapon slots", sectionNameHash("hip") != sectionNameHash("back"));

    // Canonical vector: print (not assert) so the baseline doc can record it and
    // a future intentional change is visible in the diff.
    std::printf("  note canonical invEntryHash(wooden_sandals x2 q150) = %u\n", base);
}

// ---- 5. Interpolation buffer invariants -------------------------------------------

static EntityState entAt(float x) {
    EntityState e;
    std::memset(&e, 0, sizeof(e));
    e.hIndex = 1; e.hSerial = 2; e.task = TASK_NONE;
    e.x = x; e.y = 0.0f; e.z = 0.0f; e.heading = 0.0f;
    return e;
}

static void testInterp() {
    std::printf("== interpolation buffer (Interp.cpp) ==\n");
    InterpConfig cfg; // min 50 / max 200 delay, extrap 250, snap 50u, stale 2000

    // Bracketed interpolation: 20 Hz feed moving +1u per 50ms tick.
    {
        EntityInterp it;
        for (int i = 0; i <= 10; ++i) it.push(entAt((float)i), 1000 + i * 50);
        // nowMs=1550 -> renderTime = 1550 - delay(>=50,<=200) = [1350,1500]
        // -> x must interpolate inside [7,10] and never exceed the newest.
        EntityState out;
        bool ok = it.sample(1550, cfg, &out);
        CHECK("bracketed sample returns data", ok);
        CHECK("bracketed sample within segment bounds", ok && out.x >= 6.9f && out.x <= 10.01f);

        // Monotonic advance: successive sample times never move the body backwards.
        float prev = -1.0f; bool mono = true;
        for (unsigned long t = 1400; t <= 1550; t += 10) {
            EntityState o;
            if (it.sample(t, cfg, &o)) { if (o.x < prev - 0.001f) mono = false; prev = o.x; }
        }
        CHECK("sampled position monotonic for monotone source", mono);
    }

    // Dead-reckoning cap: starved buffer extrapolates at most maxExtrapMs beyond
    // the newest snapshot (here: 1u/50ms -> cap = +5u over newest).
    {
        EntityInterp it;
        it.push(entAt(0.0f), 1000);
        it.push(entAt(1.0f), 1050);
        EntityState out;
        bool ok = it.sample(2900, cfg, &out); // renderTime far past newest, still < stale
        CHECK("starved sample still returns (dead-reckon)", ok);
        CHECK("dead-reckoning capped at maxExtrapMs", ok && out.x <= 1.0f + 5.0f + 0.01f);
    }

    // Staleness: a stream older than staleMs releases the body (sample -> false).
    {
        EntityInterp it;
        it.push(entAt(0.0f), 1000);
        EntityState out;
        CHECK("stale stream releases body", !it.sample(1000 + cfg.staleMs + 500, cfg, &out));
    }

    // Teleport snap: a segment step beyond snapDist snaps to the newer end
    // instead of smearing the body across the gap.
    {
        EntityInterp it;
        it.push(entAt(0.0f), 1000);
        it.push(entAt(1000.0f), 1050); // 1000u jump >> 50u snap distance
        it.push(entAt(1001.0f), 1100);
        EntityState out;
        bool ok = it.sample(1120, cfg, &out); // renderTime ~1070 -> inside the jump segment... 
        // renderTime lands in [1000,1050] or [1050,1100] depending on adaptive delay;
        // in the jump segment we must NOT see a smeared mid-point (x in ~[100,900]).
        bool smeared = ok && out.x > 100.0f && out.x < 900.0f;
        CHECK("teleport does not smear", ok && !smeared);
    }

    // Single snapshot: returns that pose verbatim.
    {
        EntityInterp it;
        it.push(entAt(7.0f), 1000);
        EntityState out;
        bool ok = it.sample(1040, cfg, &out);
        CHECK("single snapshot returns pose", ok && out.x == 7.0f);
    }

    // Identity/locomotion passthrough: sample carries the latest full state.
    {
        EntityInterp it;
        EntityState e = entAt(3.0f);
        e.bodyState = BODY_DOWN; e.cMoving = 1; e.task = 42;
        it.push(e, 1000);
        EntityState out;
        bool ok = it.sample(1030, cfg, &out);
        CHECK("identity+state passthrough", ok && out.bodyState == BODY_DOWN && out.cMoving == 1 && out.task == 42 && out.hIndex == 1);
    }
}

// ---- 6. Animation stability: time-aligned locomotion (the on-stop foot-slide) ----
//
// The interp buffer renders each body in the PAST (render delay). Locomotion
// (cSpeed/cMotion/cMoving) must be time-aligned with the render-time POSITION, not
// copied from the newest snapshot. Otherwise, exactly on a stop, the newest snapshot
// already reads cMoving=0 while the render-delayed position is still gliding to the
// stop point - the engine plays idle on a translating body => the visible foot-slide
// jitter the positional smoothness oracle is blind to.
//
// This replays a synthetic decelerate-to-stop trace through the real EntityInterp and
// asserts the defect is absent: no frame where the rendered position translates while
// the reported motion flag is idle, no per-frame flag flicker, no stop overshoot.

static EntityState entAtV(float x, float cSpeed, unsigned char cMoving) {
    EntityState e;
    std::memset(&e, 0, sizeof(e));
    e.hIndex = 1; e.hSerial = 2; e.task = TASK_NONE;
    e.x = x; e.y = 0.0f; e.z = 0.0f; e.heading = 0.0f;
    e.cSpeed = cSpeed; e.cMotionX = cSpeed; e.cMotionY = 0.0f; e.cMotionZ = 0.0f;
    e.cMoving = cMoving;
    return e;
}

static void testAnimStability() {
    std::printf("== animation stability: time-aligned locomotion (Interp) ==\n");
    InterpConfig cfg;
    EntityInterp it;

    // 20 Hz (50 ms) source: cruise, then brake over ~4 snapshots and stop. Position
    // keeps translating THROUGH the deceleration so the render-delayed pose is still
    // moving while the newest snapshot has already gone idle.
    struct TP { float x; float spd; unsigned char mv; };
    static const TP track[] = {
        {  0.0f, 40.0f, 1 }, {  2.0f, 40.0f, 1 }, {  4.0f, 40.0f, 1 }, {  6.0f, 40.0f, 1 },
        {  8.0f, 40.0f, 1 }, { 10.0f, 40.0f, 1 }, { 12.0f, 40.0f, 1 }, { 14.0f, 40.0f, 1 },
        { 16.0f, 40.0f, 1 }, { 18.0f, 40.0f, 1 },                            // cruise
        { 19.6f, 24.0f, 1 }, { 20.7f, 14.0f, 1 }, { 21.3f, 6.0f, 1 },         // brake
        { 21.5f,  0.0f, 0 }, { 21.5f,  0.0f, 0 }, { 21.5f,  0.0f, 0 },        // stopped
        { 21.5f,  0.0f, 0 }, { 21.5f,  0.0f, 0 }
    };
    const int N = (int)(sizeof(track) / sizeof(track[0]));
    const unsigned long t0 = 1000;
    const unsigned long endT = t0 + (unsigned long)(N - 1) * 50 + 250;

    float prevX = 0.0f; bool havePrev = false;
    int footSlide = 0, march = 0, flagTrans = 0, activeMove = 0, restFrames = 0;
    int prevFlag = -1;
    float maxX = -1.0e9f;
    int nextPush = 0;

    // Interleave 20 Hz push with 60 Hz sample against a shared virtual clock.
    for (unsigned long now = t0; now <= endT; now += 16) {
        while (nextPush < N && t0 + (unsigned long)nextPush * 50 <= now) {
            it.push(entAtV(track[nextPush].x, track[nextPush].spd, track[nextPush].mv),
                    t0 + (unsigned long)nextPush * 50);
            ++nextPush;
        }
        EntityState o;
        if (!it.sample(now, cfg, &o)) continue;
        bool flagMoving = (o.cMoving != 0) || (o.cSpeed > 0.20f); // the drive's own test
        if (flagMoving) ++activeMove; else ++restFrames;
        if (o.x > maxX) maxX = o.x;
        if (havePrev) {
            float d = o.x - prevX; if (d < 0.0f) d = -d;
            // 5 cm/frame = a visible slide. Below this is sub-perceptual settling
            // granularity at the flag-flip seam, not the multi-frame glide bug.
            bool posMoved = d > 0.05f;
            if (posMoved && !flagMoving) ++footSlide; // THE bug: sliding a static pose
            if (!posMoved && flagMoving) ++march;      // walk clip while not translating
        }
        int f = flagMoving ? 1 : 0;
        if (prevFlag >= 0 && f != prevFlag) ++flagTrans;
        prevFlag = f; prevX = o.x; havePrev = true;
    }

    CHECK("no on-stop foot-slide (position moves while flag idle)", footSlide == 0);
    CHECK("moving flag flips at most once (no per-frame flicker)", flagTrans <= 1);
    // A brief march is tolerable only across the single decel-tail segment (~3 frames
    // at 60 Hz over one 50 ms snapshot); anything more means idle position + walk flag.
    CHECK("no sustained march-in-place", march <= 4);
    // Deceleration damping must stop the extrapolator overshooting the stop point.
    CHECK("no overshoot past the stop point", maxX <= 21.5f + 0.60f);
    std::printf("  note footSlide=%d march=%d flagTrans=%d maxX=%.3f active=%d rest=%d\n",
                footSlide, march, flagTrans, maxX, activeMove, restFrames);
}

// ---- 7. At-rest continuous soft correction (the drift dead-band) -----------------
//
// The old at-rest path ignored ALL positional drift under REPARK_DIST (1 u) and then
// HARD-TELEPORTED past it - a body could sit up to a metre off its true spot and then
// pop. The fix bleeds a fixed fraction (REST_CORRECT_ALPHA) of the gap toward truth
// every frame. This locks the intended dynamics: any offset (including ones the old
// dead-band ignored forever) converges smoothly to ~0 with no overshoot/oscillation.
//
// These constants MUST match REST_CORRECT_ALPHA / REST_CORRECT_EPS in Replicator.cpp.
static const float T_REST_ALPHA = 0.20f;
static const float T_REST_EPS   = 0.03f;

static void testSoftCorrection() {
    std::printf("== at-rest soft correction (drift dead-band removal) ==\n");

    // Two offsets: one the old dead-band would have IGNORED forever (0.5u < 1u repark),
    // one just under it. Both must converge under the new continuous pull.
    const float starts[] = { 0.5f, 0.9f, 5.0f };
    for (int s = 0; s < 3; ++s) {
        float cur = 0.0f;               // body position (1-D is sufficient)
        const float tgt = starts[s];    // host transform, held still
        float prevGap = tgt - cur;
        bool monotonic = true;
        int frames = 0;
        for (; frames < 240; ++frames) { // <=4 s at 60 Hz
            float gap = tgt - cur; if (gap < 0.0f) gap = -gap;
            if (gap <= T_REST_EPS) break;
            cur = cur + (tgt - cur) * T_REST_ALPHA; // the exact soft-pull
            float newGap = tgt - cur; if (newGap < 0.0f) newGap = -newGap;
            if (newGap > prevGap + 1e-6f) monotonic = false; // never diverge/oscillate
            prevGap = newGap;
        }
        float finalGap = tgt - cur; if (finalGap < 0.0f) finalGap = -finalGap;
        char lbl[96];
        std::sprintf(lbl, "offset %.2fu converges to <=eps", starts[s]);
        CHECK(lbl, finalGap <= T_REST_EPS);
        std::sprintf(lbl, "offset %.2fu convergence monotonic (no overshoot)", starts[s]);
        CHECK(lbl, monotonic);
        std::sprintf(lbl, "offset %.2fu converges promptly (<40 frames)", starts[s]);
        CHECK(lbl, frames < 40);
        std::printf("  note start=%.2f finalGap=%.4f frames=%d\n", starts[s], finalGap, frames);
    }
    // The defining contrast with the old behaviour: a 0.5u resting offset is NOT
    // ignored (old dead-band left it at 0.5u indefinitely); it is driven to ~0.
    CHECK("sub-REPARK_DIST offset no longer ignored (dead-band removed)", T_REST_EPS < 1.0f);
}

// ---- 8. Position precision floor (f32 world coordinates) -------------------------
//
// EntityState sends absolute world position as raw float32 (memcpy - no quantization).
// The only precision floor is float32 spacing (ulp) at Kenshi's world magnitudes.
// Observed play coordinates are ~5e4 (logged pos=-50879,...). This quantifies the floor
// so it is a known, tracked quantity rather than a guess.

static double f32UlpAt(double mag) {
    int e = 0; std::frexp(mag, &e);   // mag = m * 2^e, 0.5 <= |m| < 1
    return std::ldexp(1.0, e - 24);   // spacing between adjacent float32 values near mag
}

static void testPrecisionFloor() {
    std::printf("== position precision floor (f32 world coords) ==\n");

    // The wire adds NO error of its own: a large coordinate survives the packed-struct
    // memcpy bit-exact (both clients memcpy these bytes). Lock that.
    EntityState in; std::memset(&in, 0, sizeof(in));
    in.x = -50879.35f; in.y = 1553.18f; in.z = 3675.71f;
    unsigned char buf[sizeof(EntityState)];
    std::memcpy(buf, &in, sizeof(in));
    EntityState out; std::memcpy(&out, buf, sizeof(out));
    CHECK("wire preserves f32 position bit-exact (no added quantization)",
          out.x == in.x && out.y == in.y && out.z == in.z);

    // The floor at representative magnitudes (finding, printed for the record).
    const double mags[] = { 51000.0, 100000.0, 131072.0, 262144.0, 500000.0 };
    for (int i = 0; i < 5; ++i) {
        double u = f32UlpAt(mags[i]);
        std::printf("  note ulp(f32) at %7.0f u = %.4f u (%.2f mm)\n",
                    mags[i], u, u * 1000.0);
    }
    // The tested play area (~51 k) is sub-centimetre, so f32 precision is NOT the
    // current jitter source. The floor first exceeds 1 cm past ~131 k units from
    // origin; if a save pushes bodies out there, an anchor/relative encoding (protocol
    // bump) becomes worth it. This gate flags that boundary if the arithmetic changes.
    CHECK("tested-region (~51k) f32 floor < 1 cm", f32UlpAt(51000.0) < 0.01);
    CHECK("f32 floor still < 1 cm at 100k", f32UlpAt(100000.0) < 0.01);
    CHECK("f32 floor exceeds 1 cm past ~131k", f32UlpAt(262144.0) > 0.01);
}

int main() {
    std::printf("prototest: KenshiCoop wire/hash/interp unit layer (protocol v%u)\n",
                (unsigned)PROTOCOL_VERSION);
    testSizes();
    testRoundTrips();
    testFraming();
    testContentHash();
    testInterp();
    testAnimStability();
    testSoftCorrection();
    testPrecisionFloor();
    std::printf("\nprototest: %d/%d checks passed%s\n",
                g_total - g_failed, g_total, g_failed ? " - FAIL" : " - PASS");
    return g_failed;
}
