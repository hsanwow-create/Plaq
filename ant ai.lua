-- ant colony AI v4 | OpenRouter | not run in-game
-- v4: casualty learning + auto recall, probe attacks on unverified routes, siege reflex (defend/recall/hatch),
--     wider monster threat radius, scouting diagnostics, smarter alliances (spam bots, distrust players, end-game ally_end)
-- start a SOLO match yourself; bot plays once MatchState == playing.

local Players = game:GetService("Players")
local RS = game:GetService("ReplicatedStorage")
local HttpService = game:GetService("HttpService")
local UIS = game:GetService("UserInputService")
local lp = Players.LocalPlayer

local env = (getgenv and getgenv()) or _G
if env.__ANT_STOP then pcall(env.__ANT_STOP) end

local cfg = {
    Key = env.OPENROUTER_KEY or "PUT_OPENROUTER_KEY_HERE", -- FILL: sk-or-...  (don't share the script with the key inside)
    Model = "google/gemini-2.5-flash",
    Interval = 6,
    MaxTokens = 1000,
    Temperature = 0.4,
    UseAI = true,
    AutoDefend = true,   -- siege reflex
    Monsters = true,
    Allies = true,
    Scout = true,
    HomeReserve = 4,
    ProbeSize = 6,       -- soldiers sent first on a route nobody has verified
    Run = true,
}
local httpReq = (syn and syn.request) or (http and http.request) or http_request or request

-- game handles -----------------------------------------------------------------
local AG = RS:WaitForChild("AntGame", 15)
local World = AG:WaitForChild("World")
local Colonies = World:WaitForChild("Colonies")
local Remotes = AG:WaitForChild("Remotes")
local Action = Remotes:WaitForChild("Action")
local ViewRemote = Remotes:WaitForChild("View")
local okC, Config = pcall(require, AG:WaitForChild("Config"))
if not okC or type(Config) ~= "table" then Config = {} end
local SUPER_FOOD = (Config.SUPER and Config.SUPER.cost and Config.SUPER.cost.food) or 75
local MAX_FEEDERS = Config.MAX_FEEDERS or 3
local ALLY_MAX = (Config.ALLY and Config.ALLY.max) or 3
local PRISON_LEVEL = Config.PRISON_LEVEL or 2

-- log ---------------------------------------------------------------------------
local logs = {}
local logLabel
local function log(s)
    s = os.date("%M:%S") .. " " .. tostring(s)
    table.insert(logs, s)
    while #logs > 11 do table.remove(logs, 1) end
    print("[ANT] " .. s)
    if logLabel then pcall(function() logLabel.Text = table.concat(logs, "\n") end) end
end

-- helpers ---------------------------------------------------------------------------
local function myFolder()
    for _, f in ipairs(Colonies:GetChildren()) do
        if f:GetAttribute("OwnerId") == lp.UserId then return f end
    end
end

local function colonyByIndex(idx)
    for _, c in ipairs(Colonies:GetChildren()) do
        if c:GetAttribute("Index") == idx then return c end
    end
end

local function parseOrders(s)
    local t = {}
    for k, v in string.gmatch(s or "", "([^:,]+):(%d+)") do t[k] = tonumber(v) end
    return t
end

local function sumOrders(t)
    local n = 0
    for _, v in pairs(t) do n = n + v end
    return n
end

local function int(v, d) v = tonumber(v); if not v then return d end return math.floor(v) end

local function freeSoldiers(f)
    local soldiers = f:GetAttribute("Soldiers") or 0
    return math.max(0, soldiers - sumOrders(parseOrders(f:GetAttribute("NestOrders"))) - sumOrders(parseOrders(f:GetAttribute("AntOrders"))))
end

local function allySet(f)
    local s = {}
    for n in string.gmatch(f:GetAttribute("Allies") or "", "%d+") do s[tonumber(n)] = true end
    return s
end

local function countAllies(f)
    local n = 0
    for _ in pairs(allySet(f)) do n = n + 1 end
    return n
end

local function nestPos(c) return c:GetAttribute("NestX") or 0, c:GetAttribute("NestY") or 0 end

local function dist(f, c)
    local ax, ay = nestPos(f)
    local bx, by = nestPos(c)
    return math.floor(math.sqrt((bx - ax) ^ 2 + (by - ay) ^ 2))
end

local function segDist(px, py, ax, ay, bx, by)
    local dx, dy = bx - ax, by - ay
    local l2 = dx * dx + dy * dy
    local t = l2 > 0 and math.clamp(((px - ax) * dx + (py - ay) * dy) / l2, 0, 1) or 0
    local cx, cy = ax + t * dx, ay + t * dy
    return math.sqrt((px - cx) ^ 2 + (py - cy) ^ 2), t
end

-- upgrade costs straight from Config ----------------------------------------------------------------
local UPG = { nest = "Nest", soldier = "Soldier", worker = "Worker", nursery = "Nursery" }
local UPG_ATTR = { Nest = "NestLevel", Soldier = "SoldierLv", Worker = "WorkerLv", Nursery = "NurseryCap" }

local function upgradeCost(key, f)
    local ok, res = pcall(function()
        if key == "Nest" then
            local lvl = f:GetAttribute("NestLevel") or 1
            local nx = Config.NEST_LEVELS and Config.NEST_LEVELS[lvl + 1]
            if not nx then return "max" end
            return { food = nx.food or 0, wood = nx.wood or 0, need_ants = nx.ants }
        elseif key == "Nursery" then
            local cap = f:GetAttribute("NurseryCap") or Config.NURSERY_START or 3
            if Config.NURSERY_MAX and cap >= Config.NURSERY_MAX then return "max" end
            local c = Config.nurseryCost(cap)
            return { food = c.food or 0, wood = c.wood or 0 }
        else
            local lv = f:GetAttribute(UPG_ATTR[key]) or 1
            if Config.MAX_LEVEL and lv >= Config.MAX_LEVEL then return "max" end
            local c = Config.UPGRADE_COST[key][lv]
            if not c then return "max" end
            return { food = c.food or 0, wood = c.wood or 0 }
        end
    end)
    if ok then return res end
end

local function affordable(c, f)
    if type(c) ~= "table" then return false end
    if (f:GetAttribute("Food") or 0) < c.food or (f:GetAttribute("Wood") or 0) < c.wood then return false end
    if c.need_ants and (f:GetAttribute("Total") or 0) < c.need_ants then return false end
    return true
end

-- View hook: lets the bot look at other parts of the map (scouting) ------------------------------------------
-- risk: hookmetamethod on __namecall can be detected by anti-cheat; if the game has one, set cfg.Scout=false
local conns = {}
local function track(c) conns[#conns + 1] = c return c end

local scoutPos = nil
local curCenter, lastHW, lastHH = nil, nil, nil
local hookOK = false
do
    local ok = pcall(function()
        if not (hookmetamethod and getnamecallmethod) then error("no hookmetamethod") end
        local old
        local fn = function(self, ...)
            if self == ViewRemote and getnamecallmethod() == "FireServer" then
                local x, y, hw, hh = ...
                if type(x) == "number" and type(hw) == "number" then
                    lastHW, lastHH = hw, hh
                    if scoutPos then
                        curCenter = scoutPos
                        return old(self, scoutPos.x, scoutPos.y, hw, hh)
                    end
                    curCenter = { x = x, y = y }
                end
            end
            return old(self, ...)
        end
        old = hookmetamethod(game, "__namecall", newcclosure and newcclosure(fn) or fn)
    end)
    hookOK = ok
end

-- monsters from the game's own Snap buffer ---------------------------------------------------------------------
local MONSTER_KINDS = { "Spider", "Scorpion", "Termite", "TermiteSoldier", "TermiteMound" }
local known = {}
local snapCount, lastSnapMon = 0, 0

local function parseSnap(p)
    local n = buffer.readu16(p, 0)
    local off = 2 + n * 11
    local len = buffer.len(p)
    local out, c = {}, 0
    if len > off then
        local cnt = buffer.readu8(p, off)
        off = off + 1
        for _ = 1, cnt do
            if off + 13 > len then break end
            local id = buffer.readu16(p, off)
            out[id] = {
                id = id,
                x = buffer.readu16(p, off + 2) / 8,
                y = buffer.readu16(p, off + 4) / 8,
                kind = MONSTER_KINDS[buffer.readu8(p, off + 6)] or "Spider",
                state = buffer.readu8(p, off + 7),
                hp = buffer.readu8(p, off + 8) / 255,
                owner = buffer.readu8(p, off + 10),
                seen = os.clock(),
            }
            c = c + 1
            off = off + 13
        end
    end
    return out, c
end

track(Remotes:WaitForChild("Snap").OnClientEvent:Connect(function(p)
    if typeof(p) ~= "buffer" then return end
    local ok, out, c = pcall(parseSnap, p)
    if not ok then return end
    snapCount = snapCount + 1
    lastSnapMon = c
    if curCenter and lastHW then
        for id, m in pairs(known) do
            if not out[id] and math.abs(m.x - curCenter.x) < lastHW * 0.9 and math.abs(m.y - curCenter.y) < lastHH * 0.9 then
                known[id] = nil
            end
        end
    end
    for id, m in pairs(out) do known[id] = m end
end))

local KNOWN_TTL = 30
local function liveMonster(id)
    local m = known[id]
    if m and os.clock() - m.seen < KNOWN_TTL then return m end
end

local function countKnown()
    local n = 0
    for _, m in pairs(known) do if os.clock() - m.seen < KNOWN_TTL then n = n + 1 end end
    return n
end

local function waitSnaps(n, timeout)
    local target = snapCount + n
    local t = os.clock()
    while snapCount < target and os.clock() - t < timeout do task.wait(0.05) end
end

local scoutBusy = false
local scoutedAt = {}

local function scoutRoute(f, c)
    if not (cfg.Scout and hookOK) then return false end
    while scoutBusy do task.wait(0.1) end
    scoutBusy = true
    local ok = pcall(function()
        local ax, ay = nestPos(f)
        local bx, by = nestPos(c)
        local len = math.sqrt((bx - ax) ^ 2 + (by - ay) ^ 2)
        local hw, hh = lastHW or 700, lastHH or 400
        local step = math.max(150, hw * 1.5)
        local n = math.min(10, math.ceil(len / step))
        for i = 0, n do
            local t = n > 0 and i / n or 0
            scoutPos = { x = ax + (bx - ax) * t, y = ay + (by - ay) * t }
            pcall(ViewRemote.FireServer, ViewRemote, scoutPos.x, scoutPos.y, hw, hh) -- goes through our hook, same args
            task.wait(0.05)
            waitSnaps(2, 1.2)
        end
    end)
    scoutPos = nil
    scoutBusy = false
    if ok then scoutedAt[c:GetAttribute("Index")] = os.clock() end
    return ok
end

-- threat radius: biggest "aggro-like" numeric field of the monster's Config entry (min 200)
local radiusCache, radiusLogged = {}, {}
local function threatRadius(kind)
    if radiusCache[kind] then return radiusCache[kind] end
    local mc = Config.MONSTERS and Config.MONSTERS[kind]
    local best, field = 200, "default"
    if type(mc) == "table" then
        for k, v in pairs(mc) do
            local kk = tostring(k):lower()
            if type(v) == "number" and (kk:find("aggro") or kk:find("sight") or kk:find("range") or kk:find("chase") or kk:find("detect") or kk:find("alert") or kk:find("vision") or kk:find("notice")) then
                if v > best then best, field = v, tostring(k) end
            end
        end
    end
    radiusCache[kind] = best
    if not radiusLogged[kind] then radiusLogged[kind] = true; log(string.format("threat radius %s = %d (%s)", kind, best, field)) end
    return best
end

local function routeMonsters(f, c)
    local ax, ay = nestPos(f)
    local bx, by = nestPos(c)
    local list = {}
    for id, m in pairs(known) do
        if m.owner == 0 and m.state ~= 4 and m.kind ~= "TermiteMound" and os.clock() - m.seen < KNOWN_TTL then
            local d, t = segDist(m.x, m.y, ax, ay, bx, by)
            if d <= threatRadius(m.kind) then
                list[#list + 1] = { id = id, kind = m.kind, off_path = math.floor(d), along_pct = math.floor(t * 100), hp_pct = math.floor(m.hp * 100) }
            end
        end
    end
    table.sort(list, function(x, y) return x.along_pct < y.along_pct end)
    return list
end

-- route learning: casualties after each attack ------------------------------------------------------------------
local watch = {}          -- idx -> attack being monitored
local blockedUntil = {}   -- idx -> os.clock()
local routeProven = {}    -- idx -> true
local hatchTotal = 0      -- soldiers/supers we hatched (so new hatches don't hide casualties)
local siegeUntil = 0

local function armyCount(f) return (f:GetAttribute("Soldiers") or 0) + (f:GetAttribute("Supers") or 0) end

local function checkWatches(f)
    local orders = parseOrders(f:GetAttribute("NestOrders"))
    local army = armyCount(f)
    for idx, w in pairs(watch) do
        local c = colonyByIndex(idx)
        if not c then
            watch[idx] = nil
        else
            local el = os.clock() - w.t0
            local lost = w.base + (hatchTotal - w.hatch0) - army
            local hpNow = c:GetAttribute("NestHP") or 0
            local dmg = (w.nestHp0 - hpNow) > math.max(1, 0.01 * (c:GetAttribute("NestMaxHP") or 1))
            if lost >= math.max(3, 0.35 * w.sent) and not dmg and el < 150 then
                if orders[tostring(idx)] then Action:FireServer("CancelNest", idx) end
                blockedUntil[idx] = os.clock() + 240
                routeProven[idx] = nil
                log(string.format("route to #%d LETHAL: lost %d/%d, no nest damage -> recalled, blocked 240s", idx, lost, w.sent))
                watch[idx] = nil
            elseif el > 3 and not orders[tostring(idx)] then
                if lost >= 0.5 * w.sent and not dmg then
                    blockedUntil[idx] = os.clock() + 240
                    log(string.format("attack on #%d ended badly (lost %d/%d) -> blocked", idx, lost, w.sent))
                elseif lost < 0.4 * w.sent then
                    routeProven[idx] = true
                    log(string.format("route to #%d verified (lost %d/%d)", idx, lost, w.sent))
                end
                watch[idx] = nil
            elseif el > 50 and lost < 0.25 * w.sent then
                routeProven[idx] = true
                watch[idx] = nil
            end
        end
    end
end

-- allies -------------------------------------------------------------------------------------------------------------
local pendingAsks = {}
local urgent = false
track(Remotes:WaitForChild("Event").OnClientEvent:Connect(function(kind, ...)
    if kind == "AllyAsk" then
        local k, from, life, n, by = ...
        if type(k) == "string" and type(from) == "number" then
            pendingAsks[from .. "|" .. k] = { kind = k, from = from, n = n, by = by, deadline = os.clock() + (tonumber(life) or 15) - 1 }
            urgent = true
        end
    end
end))

-- snapshot ---------------------------------------------------------------------------------------------------------
local function snapshot()
    local f = myFolder()
    if not f then return end
    local now = workspace:GetServerTimeNow()
    local a = function(n, d) local v = f:GetAttribute(n); if v == nil then return d end return v end
    local growing = select(2, string.gsub(a("Eggs", ""), "[^,]+", ""))
    local soldiers = a("Soldiers", 0)
    local supers = a("Supers", 0)
    local incoming = parseOrders(a("Incoming", ""))
    local allies = allySet(f)
    local nestMax = math.max(1, a("NestMaxHP", 1))
    local nestLv = a("NestLevel", 1)
    local free = freeSoldiers(f)

    local enemies, allyList, lend = {}, {}, {}
    for idx, exp in string.gmatch(a("LendCd", ""), "(%d+):(%d+)") do lend[tonumber(idx)] = tonumber(exp) end
    for _, c in ipairs(Colonies:GetChildren()) do
        local idx = c:GetAttribute("Index")
        if c ~= f and idx and (c:GetAttribute("NestHP") or 0) > 0 then
            local info = {
                index = idx,
                name = tostring(c:GetAttribute("Name") or "?"),
                power = math.floor(c:GetAttribute("Power") or 0),
                ants = c:GetAttribute("Total") or 0,
                nest_level = c:GetAttribute("NestLevel") or 1,
                nest_hp_pct = math.floor(100 * (c:GetAttribute("NestHP") or 0) / math.max(1, c:GetAttribute("NestMaxHP") or 1)),
                dist = dist(f, c),
                ai = c:GetAttribute("IsAI") == true,
            }
            if allies[idx] then
                info.lend_ready = (lend[idx] or 0) <= now
                table.insert(allyList, info)
            else
                local rm = routeMonsters(f, c)
                local age = scoutedAt[idx] and (os.clock() - scoutedAt[idx]) or nil
                local status
                if #rm > 0 then status = "DANGER"
                elseif routeProven[idx] then status = "verified (previous attack survived)"
                elseif age and age < 60 then status = "clear (scouted)"
                else status = "UNVERIFIED (only a small probe will be allowed)" end
                info.route = { status = status, monsters_near_path = rm, scouted_s_ago = age and math.floor(age) or nil }
                local b = blockedUntil[idx]
                if b and b > os.clock() then info.blocked_lethal_for_s = math.floor(b - os.clock()) end
                table.insert(enemies, info)
            end
        end
    end
    table.sort(enemies, function(x, y) return x.dist < y.dist end)
    while #enemies > 8 do table.remove(enemies) end

    local asks, t = {}, os.clock()
    for key, p in pairs(pendingAsks) do
        local c = colonyByIndex(p.from)
        if p.deadline <= t or not c then
            pendingAsks[key] = nil
        else
            table.insert(asks, {
                kind = p.kind, from = p.from, from_name = tostring(c:GetAttribute("Name") or "?"),
                from_is_ai_bot = c:GetAttribute("IsAI") == true,
                from_power = math.floor(c:GetAttribute("Power") or 0), from_dist = dist(f, c),
                soldiers_requested = p.n, seconds_left = math.floor(p.deadline - t),
                already_ally = allies[p.from] == true,
            })
        end
    end
    local outReq = {}
    for n in string.gmatch(a("AllyOut", ""), "%d+") do outReq[#outReq + 1] = tonumber(n) end

    local prisoners, cell = {}, 0
    for ty, fed, need in string.gmatch(a("Prisoners", ""), "(%a+):(%d+):(%d+)") do
        cell = cell + 1
        prisoners[#prisoners + 1] = { cell = cell, kind = ty, fed = tonumber(fed), need = tonumber(need) }
    end

    local mons = {}
    if cfg.Monsters then
        local nx, ny = nestPos(f)
        for id, m in pairs(known) do
            if m.owner == 0 and os.clock() - m.seen < KNOWN_TTL then
                local mc = Config.MONSTERS and Config.MONSTERS[m.kind] or {}
                table.insert(mons, {
                    id = id, kind = m.kind, down = m.state == 4,
                    hp_pct = math.floor(m.hp * 100), hp_max = mc.hp,
                    bite_dmg = mc.bite and mc.bite.dmg, speed = mc.speed,
                    capture_wood = mc.capture, tame_food = mc.tame,
                    pack = mc.pack, mound = mc.mound, wood_reward = mc.wood,
                    dist_from_my_nest = math.floor(math.sqrt((m.x - nx) ^ 2 + (m.y - ny) ^ 2)),
                    seen_s_ago = math.floor(os.clock() - m.seen),
                })
            end
        end
        table.sort(mons, function(x, y) return x.dist_from_my_nest < y.dist_from_my_nest end)
        while #mons > 8 do table.remove(mons) end
    end

    local upgrades = {}
    for lower, key in pairs(UPG) do
        local c = upgradeCost(key, f)
        if c == "max" then upgrades[lower] = "max"
        elseif type(c) == "table" then
            upgrades[lower] = { food = c.food, wood = c.wood, need_total_ants = c.need_ants, affordable = affordable(c, f) }
        else upgrades[lower] = "unknown" end
    end

    local start = World:GetAttribute("MatchStart")
    local sStats
    pcall(function() sStats = Config.antStats("Soldier", a("SoldierLv", 1)) end)
    return {
        t = start and math.floor(now - start) or 0,
        peace_left = math.max(0, math.floor((World:GetAttribute("PeaceUntil") or 0) - now)),
        playing = World:GetAttribute("MatchState") == "playing",
        siege = os.clock() < siegeUntil,
        me = {
            food = a("Food", 0), wood = a("Wood", 0),
            eggs_ready = a("Available", 0), eggs_growing = growing, nursery_cap = a("NurseryCap", 3),
            workers = a("Workers", 0), soldiers = soldiers, supers = supers, pets = a("Pets", 0),
            total_ants = a("Total", 0),
            free_soldiers = free,
            effective_army = free + 2 * supers,
            home_reserve = cfg.HomeReserve,
            attacks_out = parseOrders(a("NestOrders", "")),
            incoming_raids = incoming,
            soldier_lv = a("SoldierLv", 1), worker_lv = a("WorkerLv", 1), nest_lv = nestLv,
            soldier_stats = sStats,
            nest_hp_pct = math.floor(100 * a("NestHP", 0) / nestMax),
            power = math.floor(a("Power", 0)),
            want_wood = a("WantWood", 0), want_feeders = a("WantFeeders", 0), on_food = a("JobFood", 0),
            under_raid = next(incoming) ~= nil,
            prison_open = nestLv >= PRISON_LEVEL, prisoners = prisoners,
        },
        upgrades = upgrades,
        enemies = enemies,
        allies = allyList, ally_max = ALLY_MAX, my_pending_ally_requests = outReq,
        ally_requests_to_me = asks,
        wild_monsters_known = mons,
        super_food_cost = SUPER_FOOD, max_feeders = MAX_FEEDERS,
    }, f
end

-- executor -----------------------------------------------------------------------------------------------------------
local lastUp = {}
local lastAtk, lastDef, lastHunt, lastAllyReq = 0, 0, 0, 0

local function setJob(f, kind, attr, target)
    local workers = f:GetAttribute("Workers") or 0
    local cap = kind == "Feeder" and math.min(MAX_FEEDERS, workers) or workers
    target = math.clamp(target, 0, cap)
    local d = target - (f:GetAttribute(attr) or 0)
    local step = d > 0 and 1 or -1
    for _ = 1, math.min(math.abs(d), 10) do
        Action:FireServer("Job", kind, step)
        task.wait(0.08)
    end
    return d
end

local function petsArg(f, v)
    local have = f:GetAttribute("Pets") or 0
    if v == "all" then return have end
    return math.min(int(v, 0), have)
end

local function exec(a, f)
    local k = tostring(a.type or a.action or ""):lower()

    if k == "hatch" then
        local role = ({ worker = "Worker", soldier = "Soldier", super = "Super" })[tostring(a.role or ""):lower()]
        if not role then return "hatch: bad role" end
        local n = math.clamp(int(a.n, 1), 1, 10)
        local ready = f:GetAttribute("Available") or 0
        local food = f:GetAttribute("Food") or 0
        local sent = 0
        for _ = 1, n do
            if ready <= 0 then break end
            if role == "Super" then
                if food < SUPER_FOOD then break end
                food = food - SUPER_FOOD
            end
            Action:FireServer("Role", role, 1)
            if role ~= "Worker" then hatchTotal = hatchTotal + 1 end
            ready = ready - 1
            sent = sent + 1
            task.wait(0.15)
        end
        if sent == 0 then return "hatch " .. role .. ": nothing (no egg/food)", true end
        return string.format("hatch %s x%d", role, sent)

    elseif k == "upgrade" then
        local key = UPG[tostring(a.what or ""):lower()]
        if not key then return "upgrade: bad target" end
        local c = upgradeCost(key, f)
        if c == "max" then return "upgrade " .. key .. ": already max", true end
        if type(c) == "table" then
            if not affordable(c, f) then
                return string.format("upgrade %s: skipped, needs %df/%dw%s", key, c.food, c.wood, c.need_ants and (" & " .. c.need_ants .. " ants") or ""), true
            end
        elseif os.clock() - (lastUp[key] or -99) < 30 then
            return "upgrade " .. key .. ": backoff", true
        end
        if os.clock() - (lastUp[key] or -99) < 3 then return "upgrade " .. key .. ": cooldown", true end
        lastUp[key] = os.clock()
        local before = f:GetAttribute(UPG_ATTR[key])
        Action:FireServer("Upgrade", key)
        task.wait(0.7)
        return "upgrade " .. key .. (f:GetAttribute(UPG_ATTR[key]) ~= before and ": OK" or ": failed")

    elseif k == "job" then
        local out = {}
        if a.wood ~= nil then out[#out + 1] = "wood " .. setJob(f, "Wood", "WantWood", int(a.wood, 0)) end
        if a.feeders ~= nil then out[#out + 1] = "feeders " .. setJob(f, "Feeder", "WantFeeders", int(a.feeders, 0)) end
        return "job " .. table.concat(out, ", ")

    elseif k == "attack" then
        if workspace:GetServerTimeNow() < (World:GetAttribute("PeaceUntil") or 0) then return "attack: peace not over", true end
        if os.clock() < siegeUntil then return "attack REFUSED: my nest is under siege, defend first" end
        if os.clock() - lastAtk < 8 then return "attack: cooldown", true end
        local idx = int(a.target, nil)
        local c = idx and colonyByIndex(idx)
        if not c or c == f then return "attack: target gone" end
        if allySet(f)[idx] then return "attack: target is my ally (use ally_end first)" end
        if (blockedUntil[idx] or 0) > os.clock() then
            return string.format("attack #%d REFUSED: previous attack on this route was wiped out, blocked %ds more. pick another target or hunt the blocker", idx, blockedUntil[idx] - os.clock())
        end
        local free = freeSoldiers(f)
        local avail = math.max(0, free - cfg.HomeReserve)
        local n = (a.soldiers == "all" or a.soldiers == nil) and avail or math.min(int(a.soldiers, avail), avail)
        if n < 1 then return "attack: no free soldiers beyond home reserve", true end

        local scouted = false
        if not scoutedAt[idx] or os.clock() - scoutedAt[idx] > 20 then scouted = scoutRoute(f, c) else scouted = true end
        local rm = routeMonsters(f, c)
        log(string.format("route check #%d: hook=%s scouted=%s monsters_on_path=%d known=%d", idx, tostring(hookOK), tostring(scouted), #rm, countKnown()))
        if #rm > 0 and a.force ~= true then
            local names = {}
            for _, m in ipairs(rm) do names[#names + 1] = m.kind .. "#" .. m.id end
            return "attack #" .. idx .. " REFUSED: monsters on route (" .. table.concat(names, ",") .. "). hunt them first, pick another target, or build many supers"
        end
        local verified = routeProven[idx] or (scouted and #rm == 0 and countKnown() > 0)
        local probe = false
        if not verified then
            n = math.min(n, cfg.ProbeSize)
            probe = true
        end
        lastAtk = os.clock()
        local pets = probe and 0 or petsArg(f, a.pets)
        local base = armyCount(f)
        Action:FireServer("AttackNest", idx, n, pets)
        watch[idx] = { t0 = os.clock(), sent = n, base = base, hatch0 = hatchTotal, nestHp0 = c:GetAttribute("NestHP") or 0 }
        task.wait(0.7)
        local ok = parseOrders(f:GetAttribute("NestOrders"))[tostring(idx)] ~= nil
        return string.format("%s #%d with %d+%dpets: %s", probe and "PROBE attack" or "attack", idx, n, pets, ok and "sent" or "no order registered")

    elseif k == "recall" then
        local idx = int(a.target, nil)
        if not idx then return "recall: no target", true end
        Action:FireServer("CancelNest", idx)
        watch[idx] = nil
        return "recall attack on #" .. idx

    elseif k == "defend" then
        if os.clock() - lastDef < 5 then return "defend: cooldown", true end
        lastDef = os.clock()
        Action:FireServer("Defend")
        return "defend"

    elseif k == "hunt" then
        if not cfg.Monsters then return "hunt: disabled", true end
        if os.clock() < siegeUntil then return "hunt REFUSED: nest under siege" end
        if os.clock() - lastHunt < 6 then return "hunt: cooldown", true end
        local id = int(a.target, nil)
        local m = id and liveMonster(id)
        if not m or m.owner ~= 0 then return "hunt: monster unknown/expired" end
        if m.state == 4 then return "hunt: already knocked out (use capture)", true end
        local free = freeSoldiers(f)
        local avail = math.max(0, free - cfg.HomeReserve)
        local n = (a.soldiers == "all" or a.soldiers == nil) and avail or math.min(int(a.soldiers, avail), avail)
        if n < 1 then return "hunt: no free soldiers beyond home reserve", true end
        lastHunt = os.clock()
        local pets = petsArg(f, a.pets)
        Action:FireServer("Hunt", id, n, pets)
        return string.format("hunt %s #%d with %d+%dpets", m.kind, id, n, pets)

    elseif k == "capture" then
        if not cfg.Monsters then return "capture: disabled", true end
        local id = int(a.target, nil)
        local m = id and liveMonster(id)
        if not m or m.owner ~= 0 or m.state ~= 4 then return "capture: monster not knocked out/known", true end
        local need = Config.MONSTERS and Config.MONSTERS[m.kind] and Config.MONSTERS[m.kind].capture or 0
        if (f:GetAttribute("Wood") or 0) < need then return string.format("capture: needs %d wood", need), true end
        if (f:GetAttribute("NestLevel") or 1) < PRISON_LEVEL then return "capture: prison locked", true end
        Action:FireServer("Capture", id)
        return "capture " .. m.kind .. " #" .. id

    elseif k == "tame" then
        if not cfg.Monsters then return "tame: disabled", true end
        local cell = int(a.cell, nil)
        local target, cn = nil, 0
        for ty, fed, need in string.gmatch(f:GetAttribute("Prisoners") or "", "(%a+):(%d+):(%d+)") do
            cn = cn + 1
            if cn == cell then target = { ty = ty, fed = tonumber(fed), need = tonumber(need) } end
        end
        if not target then return "tame: no prisoner in that cell", true end
        local presses = math.ceil(math.max(0, target.need - target.fed) / 10)
        presses = math.min(presses, math.floor((f:GetAttribute("Food") or 0) / 10), int(a.max_presses, 20), 30)
        if presses < 1 then return "tame: no food", true end
        for _ = 1, presses do
            Action:FireServer("Tame", cell)
            task.wait(0.1)
        end
        return string.format("tame %s cell %d x%d (+%d food)", target.ty, cell, presses, presses * 10)

    elseif k == "ally_answer" then
        if not cfg.Allies then return "ally_answer: disabled", true end
        local from = int(a.from, nil)
        local found
        for key, p in pairs(pendingAsks) do
            if p.from == from then found = p; pendingAsks[key] = nil end
        end
        if not found then return "ally_answer: request expired", true end
        local accept = a.accept == true
        if accept and found.kind == "ally" and countAllies(f) >= ALLY_MAX then accept = false end
        Action:FireServer("AllyAnswer", from, accept)
        return string.format("ally %s from #%d: %s", found.kind, from, accept and "ACCEPT" or "decline")

    elseif k == "ally_request" then
        if not cfg.Allies then return "ally_request: disabled", true end
        if os.clock() - lastAllyReq < 20 then return "ally_request: cooldown", true end
        local idx = int(a.target, nil)
        if not idx or not colonyByIndex(idx) or allySet(f)[idx] then return "ally_request: bad target", true end
        if countAllies(f) >= ALLY_MAX then return "ally_request: max allies", true end
        lastAllyReq = os.clock()
        Action:FireServer("AllyRequest", idx)
        return "ally_request -> #" .. idx

    elseif k == "ally_soldiers" then
        if not cfg.Allies then return "ally_soldiers: disabled", true end
        local idx = int(a.target, nil)
        if not idx or not allySet(f)[idx] then return "ally_soldiers: not an ally", true end
        for i, exp in string.gmatch(f:GetAttribute("LendCd") or "", "(%d+):(%d+)") do
            if tonumber(i) == idx and tonumber(exp) > workspace:GetServerTimeNow() then return "ally_soldiers: on cooldown", true end
        end
        Action:FireServer("AllySoldiers", idx)
        return "ally_soldiers <- #" .. idx

    elseif k == "ally_end" then
        local idx = int(a.target, nil)
        if not idx or not allySet(f)[idx] then return "ally_end: not an ally", true end
        Action:FireServer("AllyEnd", idx)
        return "ally_end #" .. idx .. " (alliance ended peacefully)"

    elseif k == "ally_betray" then
        -- carries a "traitor" penalty in the game; only for emergencies
        local idx = int(a.target, nil)
        if not idx or not allySet(f)[idx] then return "ally_betray: not an ally", true end
        Action:FireServer("AllyBetray", idx)
        return "ally_betray #" .. idx .. " (TRAITOR mark!)"

    elseif k == "wait" then
        return "wait", true
    end
    return "unknown action: " .. k
end

-- siege reflexes (run every 0.5s, independent of the LLM) -------------------------------------------------------------
local lastNestHp, hitAt = nil, -99
local lastRecallAll, lastSiegeHatch = 0, 0

local function reflexes(f)
    local hp = f:GetAttribute("NestHP") or 0
    if lastNestHp and hp < lastNestHp - 0.5 then hitAt = os.clock() end
    lastNestHp = hp
    local incomingN = sumOrders(parseOrders(f:GetAttribute("Incoming")))
    local free = freeSoldiers(f)
    local siege = (os.clock() - hitAt < 15) or (incomingN > 0 and incomingN > free * 0.6)
    if siege then siegeUntil = os.clock() + 45 end
    if not (siege and cfg.AutoDefend) then return end

    if os.clock() - lastDef > 3 then
        lastDef = os.clock()
        Action:FireServer("Defend")
        log("SIEGE: defend")
    end
    if os.clock() - lastRecallAll > 8 then
        lastRecallAll = os.clock()
        for k in pairs(parseOrders(f:GetAttribute("NestOrders"))) do Action:FireServer("CancelNest", tonumber(k) or k) end
        for k in pairs(parseOrders(f:GetAttribute("AntOrders"))) do Action:FireServer("Cancel", tonumber(k) or k) end
        watch = {}
    end
    if os.clock() - lastSiegeHatch > 2 then
        lastSiegeHatch = os.clock()
        local ready = f:GetAttribute("Available") or 0
        local food = f:GetAttribute("Food") or 0
        for _ = 1, math.min(ready, 6) do
            local role = food >= SUPER_FOOD and "Super" or "Soldier"
            if role == "Super" then food = food - SUPER_FOOD end
            Action:FireServer("Role", role, 1)
            hatchTotal = hatchTotal + 1
            task.wait(0.12)
        end
        for _, key in ipairs({ "Soldier", "Nest" }) do
            local c = upgradeCost(key, f)
            if type(c) == "table" and affordable(c, f) and os.clock() - (lastUp[key] or -99) > 5 then
                lastUp[key] = os.clock()
                Action:FireServer("Upgrade", key)
            end
        end
    end
end

-- heuristic fallback ---------------------------------------------------------------------------------------------------
local function huntNeed(kind)
    if kind == "Scorpion" then return 40 end
    if kind == "Spider" then return 25 end
    return 15
end

local function heuristic(S)
    local me, acts = S.me, {}

    if cfg.Allies then
        local cnt = #S.allies
        for _, r in ipairs(S.ally_requests_to_me) do
            local accept = false
            if r.kind == "ally" then
                accept = (cnt < S.ally_max) and not r.already_ally
            elseif r.kind == "soldiers" or r.kind == "help" then
                local need = (r.soldiers_requested or 3)
                if r.from_is_ai_bot then accept = me.free_soldiers >= need + 12 and not S.siege and not me.under_raid
                else accept = me.free_soldiers >= need + 40 and not S.siege and not me.under_raid end -- real players exploit this
            end
            if accept and r.kind == "ally" then cnt = cnt + 1 end
            acts[#acts + 1] = { type = "ally_answer", from = r.from, accept = accept }
        end
        -- keep asking bots until one says yes (they accept eventually); prefer bots, nearest first
        if cnt < S.ally_max and #S.my_pending_ally_requests == 0 and S.t > 20 then
            local pick
            for _, e in ipairs(S.enemies) do
                if e.ai then pick = e break end
            end
            pick = pick or S.enemies[1]
            if pick then acts[#acts + 1] = { type = "ally_request", target = pick.index } end
        end
        for _, al in ipairs(S.allies) do
            if al.lend_ready and me.free_soldiers < 60 then acts[#acts + 1] = { type = "ally_soldiers", target = al.index } end
        end
        -- last survivors can't both win: if only allies remain, end the alliance with the weakest and fight
        if #S.enemies == 0 and #S.allies > 0 then
            table.sort(S.allies, function(x, y) return x.power < y.power end)
            acts[#acts + 1] = { type = "ally_end", target = S.allies[1].index }
        end
    end

    local w, s = me.workers, me.soldiers + me.supers
    if me.eggs_ready > 0 then
        local nw, ns = 0, 0
        for _ = 1, me.eggs_ready do
            local wk, sd = w + nw, s + ns
            if (not S.siege) and (wk < 6 or (wk < 14 and sd >= wk * 0.8)) then nw = nw + 1 else ns = ns + 1 end
        end
        if nw > 0 then acts[#acts + 1] = { type = "hatch", role = "worker", n = nw } end
        if ns > 0 then
            local food, supersN = me.food, 0
            if (S.t > 60 and s >= 3) or S.siege then
                while supersN < ns and food >= SUPER_FOOD + (S.siege and 0 or 30) do
                    supersN = supersN + 1
                    food = food - SUPER_FOOD
                end
            end
            if supersN > 0 then acts[#acts + 1] = { type = "hatch", role = "super", n = supersN } end
            if ns - supersN > 0 then acts[#acts + 1] = { type = "hatch", role = "soldier", n = ns - supersN } end
        end
    end
    local feeders = w >= 3 and math.clamp(math.floor(w * 0.3) + 1, 1, MAX_FEEDERS) or 0
    local wood = (me.wood < 40 and w >= 4) and math.floor(w * 0.25) or 0
    acts[#acts + 1] = { type = "job", feeders = feeders, wood = wood }

    local order = S.siege and { "soldier", "nest", "nursery" } or { "nursery", me.worker_lv <= me.soldier_lv and "worker" or "soldier", "nest" }
    for _, k in ipairs(order) do
        local u = S.upgrades[k]
        if type(u) == "table" and u.affordable then acts[#acts + 1] = { type = "upgrade", what = k } end
    end

    if cfg.Monsters and not S.siege then
        for _, p in ipairs(me.prisoners) do
            if me.food >= (p.need - p.fed) + 60 then acts[#acts + 1] = { type = "tame", cell = p.cell } end
        end
        for _, m in ipairs(S.wild_monsters_known) do
            if m.down and m.capture_wood and me.wood >= m.capture_wood and me.prison_open then
                acts[#acts + 1] = { type = "capture", target = m.id }
            end
        end
    end

    if S.peace_left <= 0 and not S.siege and me.free_soldiers > me.home_reserve + 5 then
        local clearTarget, blocker
        local weak = {}
        for _, e in ipairs(S.enemies) do
            if e.power <= me.power * 0.8 and not e.blocked_lethal_for_s then weak[#weak + 1] = e end
        end
        table.sort(weak, function(x, y) return x.power < y.power end)
        for _, e in ipairs(weak) do
            if e.route.status == "DANGER" then
                blocker = blocker or e.route.monsters_near_path[1]
            else
                clearTarget = e
                break
            end
        end
        if clearTarget then
            acts[#acts + 1] = { type = "attack", target = clearTarget.index, soldiers = "all", pets = "all" }
        elseif blocker and cfg.Monsters and me.effective_army >= huntNeed(blocker.kind) then
            acts[#acts + 1] = { type = "hunt", target = blocker.id, soldiers = "all", pets = "all" }
        end
    end
    return { thought = "heuristic", actions = acts }
end

-- LLM ------------------------------------------------------------------------------------------------------------------------
local SYS = [[
You control one ant colony in a real-time ant-war game against AI colonies (and sometimes real players). GOAL: win = be the last colony standing (destroy every enemy nest) while keeping yours alive.
Mechanics:
- Workers gather food automatically. Workers assigned to "wood" bring wood; workers assigned to "feeders" (max max_feeders) feed the queen, which lays eggs into the nursery (cap = nursery_cap). Unassigned workers gather food.
- Ready eggs (eggs_ready) are hatched into worker, soldier or super (super costs super_food_cost food, MUCH tougher). Hatched ants cannot be changed. Never leave eggs_ready unused.
- Upgrades: state.upgrades gives EXACT cost and whether it is affordable. Only request affordable=true upgrades. nest upgrades also need total ants >= need_total_ants.
- Raids are impossible while peace_left > 0. Afterwards colonies raid you. The colony in first place gets raided constantly.
DEFENSE FIRST: if state.siege is true your nest is being hit: do NOT attack or hunt (the code refuses), hatch supers/soldiers, keep soldiers home, upgrade soldiers. Losing the nest loses the game; one bad attack that gets your army killed makes you the next victim. Leave home_reserve soldiers at home always.
ROUTES AND MONSTERS (the most important lesson): armies walk a STRAIGHT LINE to the target; the path cannot be changed. Wild spiders/scorpions sit on the map and AUTOMATICALLY attack any army passing within their range, wiping out small ants. A scorpion one-shots a worker, kills a soldier in 2 bites, a super in 3-4; a spider needs ~3 bites on a super; scorpion > spider. A 51-soldier army died to one scorpion. Therefore:
- enemies[].route.status: "DANGER" (monsters_near_path listed), "clear (scouted)", "verified" (a previous attack survived), or "UNVERIFIED" (only a small probe will be sent; if the probe survives the route becomes verified and the next attack can be full-size).
- enemies[].blocked_lethal_for_s means an earlier attack on that route was wiped out: NEVER re-attack it until it expires, choose a different target or clear the blocker first. Do NOT repeat a failing attack. Read last_results: "REFUSED" means the code protected you, change the plan.
- If a route is DANGER: hunt the monster first with enough army (compare effective_army, supers, soldier_stats with hp_max/bite_dmg; scorpion needs far more than spider; bring pets), or choose another target, or build supers. Never send small ants through monsters. "force":true bypasses only the monster check and only for overwhelming super armies.
- Prefer SUPERS over plain soldiers once the economy runs (food reserve ~30+). Mixed supers+soldiers survive.
- hunt {target:monster id}; at 0 hp a monster is "down". capture {id} cages a DOWN monster (capture_wood wood, needs prison_open). Prisoners sit in cells (me.prisoners): tame {cell} feeds 10 food per press until fed==need; a tamed monster becomes a PET that fights for you (pass pets:"all" in attack/hunt).
- recall {target} cancels a marching attack (the code also recalls automatically when an attack is being slaughtered).
ALLIES:
- Bots (ai=true) eventually accept alliance requests if you keep asking; they lend 3 soldiers when asked (ally_soldiers, long cooldown, ask whenever lend_ready). Real players (ai=false) are unreliable: they often refuse, rarely send soldiers, and often BETRAY when two or three players attack you. Accept their alliances if useful but never depend on them; don't lend them soldiers unless you have a huge surplus (they ask when you're first place).
- ally_requests_to_me expire in ~15s: answer NOW. kind "ally": accept if it covers an exposed side, requester is strong/near; decline if you have ally_max or it is weak/far. kind "soldiers"/"help": accept only if free_soldiers is far above n and no siege.
- Max ally_max allies. Allies are not valid attack targets. THE GAME HAS ONE WINNER: when only allies remain, you must break the alliance with ally_end {target} (peaceful; prefer this) and fight; ally_betray carries a traitor penalty, use only in an emergency (e.g. an ally is about to win).
Typical plan: ~10 workers, 1-2 feeders, 1-3 wood workers; nursery+worker upgrades early; then supers/soldiers; clear monsters near the nest; take the weakest colony with a verified/clear route, repeatedly; keep allies from bots; end alliances at the end.
You receive JSON state each turn plus last_results and your previous notes. Reply with ONLY one JSON object, no markdown:
{"thought":"<=30 words plan","actions":[ ... max 10 ... ]}
Allowed actions:
{"type":"hatch","role":"worker|soldier|super","n":1-10}
{"type":"upgrade","what":"nursery|worker|soldier|nest"}
{"type":"job","wood":<target wood workers>,"feeders":<target feeders>}   (either key optional)
{"type":"attack","target":<enemy colony index>,"soldiers":"all" or number,"pets":"all" or number,"force":false}
{"type":"recall","target":<enemy colony index>}
{"type":"hunt","target":<monster id>,"soldiers":number or "all","pets":"all" or number}
{"type":"capture","target":<monster id>}
{"type":"tame","cell":<prisoner cell>}
{"type":"ally_answer","from":<colony index>,"accept":true|false}
{"type":"ally_request","target":<colony index>}
{"type":"ally_soldiers","target":<ally colony index>}
{"type":"ally_end","target":<ally colony index>}
{"type":"ally_betray","target":<ally colony index>}
{"type":"defend"}
{"type":"wait"}
]]

local function extractJson(s)
    s = tostring(s or "")
    local a, b = s:find("{"), nil
    for i = #s, 1, -1 do if s:sub(i, i) == "}" then b = i break end end
    if not a or not b then return nil end
    local ok, t = pcall(HttpService.JSONDecode, HttpService, s:sub(a, b))
    if ok and type(t) == "table" then return t end
end

local function askAI(S, results, notes)
    if not httpReq then return nil, "executor has no request()" end
    if cfg.Key == "" or cfg.Key:find("PUT_") then return nil, "no API key" end
    S.last_results = results
    S.my_previous_notes = notes
    local body = HttpService:JSONEncode({
        model = cfg.Model,
        temperature = cfg.Temperature,
        max_tokens = cfg.MaxTokens,
        messages = {
            { role = "system", content = SYS },
            { role = "user", content = HttpService:JSONEncode(S) },
        },
    })
    local ok, res = pcall(httpReq, {
        Url = "https://openrouter.ai/api/v1/chat/completions",
        Method = "POST",
        Headers = {
            ["Content-Type"] = "application/json",
            ["Authorization"] = "Bearer " .. cfg.Key,
            ["X-Title"] = "AntBot",
        },
        Body = body,
    })
    if not ok then return nil, "http error: " .. tostring(res) end
    if res.StatusCode ~= 200 then return nil, "HTTP " .. tostring(res.StatusCode) .. " " .. tostring(res.Body):sub(1, 120) end
    local okJ, j = pcall(HttpService.JSONDecode, HttpService, res.Body)
    local content = okJ and j.choices and j.choices[1] and j.choices[1].message and j.choices[1].message.content
    local plan = extractJson(content)
    if not plan or type(plan.actions) ~= "table" then return nil, "bad reply: " .. tostring(content):sub(1, 100) end
    return plan
end

-- main loops --------------------------------------------------------------------------------------------------------------------
local alive = true
local fails, heurUntil = 0, 0
local lastDecide = -99
local results, notes = {}, ""
local statusLabel

local function decide()
    local S, f = snapshot()
    if not S then return "no colony" end
    if not S.playing then return "waiting for match" end
    local plan, err
    if cfg.UseAI and os.clock() > heurUntil then
        plan, err = askAI(S, results, notes)
        if plan then fails = 0 else
            fails = fails + 1
            log("AI fail (" .. fails .. "): " .. tostring(err))
            if fails >= 3 then heurUntil = os.clock() + 60; fails = 0; log("AI down 60s -> heuristic") end
        end
    end
    local usedAI = plan ~= nil
    plan = plan or heuristic(S)
    notes = tostring(plan.thought or ""):sub(1, 200)
    log((usedAI and "AI: " or "H: ") .. notes)
    results = {}
    for i, a in ipairs(plan.actions) do
        if i > 10 then break end
        if type(a) == "table" then
            local ok, r, quiet = pcall(exec, a, f)
            if not ok then r = "err " .. tostring(r) end
            results[#results + 1] = r
            if not quiet then log(" > " .. tostring(r)) end
            task.wait(0.1)
        end
    end
    return "ok"
end

task.spawn(function()
    while alive do
        task.wait(0.5)
        if cfg.Run then
            pcall(function()
                local f = myFolder()
                if f and World:GetAttribute("MatchState") == "playing" then
                    reflexes(f)
                    checkWatches(f)
                end
            end)
            if urgent or os.clock() - lastDecide >= cfg.Interval then
                urgent = false
                lastDecide = os.clock()
                local ok, r = pcall(decide)
                if not ok then log("decide err: " .. tostring(r)) end
                if statusLabel then
                    pcall(function()
                        statusLabel.Text = string.format("%s | hook:%s mon:%d/%d snaps:%d%s", ok and tostring(r) or "error",
                            hookOK and "Y" or "N", lastSnapMon, countKnown(), snapCount, os.clock() < siegeUntil and " SIEGE" or "")
                    end)
                end
            end
        end
    end
end)

-- background scouting of the two nearest non-allied colonies every ~30s (only near/after peace end)
task.spawn(function()
    local turn = 0
    while alive do
        task.wait(30)
        if cfg.Run and cfg.Scout and hookOK then
            pcall(function()
                local S, f = snapshot()
                if not S or not S.playing or S.peace_left > 20 or S.siege or #S.enemies == 0 then return end
                turn = turn % math.min(2, #S.enemies) + 1
                local c = colonyByIndex(S.enemies[turn].index)
                if c then
                    scoutRoute(f, c)
                    log(string.format("scouted #%d: %d monsters on path, %d known", S.enemies[turn].index, #routeMonsters(f, c), countKnown()))
                end
            end)
        end
    end
end)

-- UI ---------------------------------------------------------------------------------------------------------------------------------
local saved = env.__ANT_POS or {}

local gui = Instance.new("ScreenGui")
gui.Name = "AntAI"
gui.ResetOnSpawn = false
gui.IgnoreGuiInset = true
gui.DisplayOrder = 1000
local pg = lp:FindFirstChildOfClass("PlayerGui") or lp:WaitForChild("PlayerGui", 10)
gui.Parent = pg

local frame, mini
local function savePos()
    pcall(function()
        env.__ANT_POS = {
            frame = { frame.Position.X.Offset, frame.Position.Y.Offset },
            mini = { mini.Position.X.Offset, mini.Position.Y.Offset },
        }
    end)
end

local function draggable(handle, target, onTap)
    local dragging, moved, start, startPos
    track(handle.InputBegan:Connect(function(i)
        if i.UserInputType == Enum.UserInputType.MouseButton1 or i.UserInputType == Enum.UserInputType.Touch then
            dragging, moved, start, startPos = true, false, i.Position, target.Position
            local c
            c = i.Changed:Connect(function()
                if i.UserInputState == Enum.UserInputState.End then
                    dragging = false
                    c:Disconnect()
                    if moved then savePos() elseif onTap then pcall(onTap) end
                end
            end)
        end
    end))
    track(UIS.InputChanged:Connect(function(i)
        if not dragging then return end
        if i.UserInputType == Enum.UserInputType.MouseMovement or i.UserInputType == Enum.UserInputType.Touch then
            local d = i.Position - start
            if d.Magnitude > 6 then moved = true end
            if moved then
                pcall(function() target.Position = UDim2.fromOffset(startPos.X.Offset + d.X, startPos.Y.Offset + d.Y) end)
            end
        end
    end))
end

local fp = saved.frame or { 12, 120 }
frame = Instance.new("Frame")
frame.Size = UDim2.fromOffset(330, 0)
frame.AutomaticSize = Enum.AutomaticSize.Y
frame.Position = UDim2.fromOffset(fp[1], fp[2])
frame.BackgroundColor3 = Color3.fromRGB(20, 20, 24)
frame.BorderSizePixel = 0
frame.Parent = gui
local layout = Instance.new("UIListLayout")
layout.SortOrder = Enum.SortOrder.LayoutOrder
layout.Padding = UDim.new(0, 2)
layout.Parent = frame

local bar = Instance.new("Frame")
bar.Size = UDim2.new(1, 0, 0, 30)
bar.BackgroundColor3 = Color3.fromRGB(30, 30, 38)
bar.BorderSizePixel = 0
bar.LayoutOrder = 0
bar.Parent = frame
local title = Instance.new("TextLabel")
title.Size = UDim2.new(1, -30, 1, 0)
title.BackgroundTransparency = 1
title.Font = Enum.Font.Code
title.TextSize = 14
title.TextColor3 = Color3.new(1, 1, 1)
title.Text = "ANT AI v4 (drag)"
title.Parent = bar
local close = Instance.new("TextButton")
close.Size = UDim2.fromOffset(30, 30)
close.Position = UDim2.new(1, -30, 0, 0)
close.BackgroundColor3 = Color3.fromRGB(150, 40, 40)
close.BorderSizePixel = 0
close.Font = Enum.Font.Code
close.TextSize = 15
close.TextColor3 = Color3.new(1, 1, 1)
close.Text = "X"
close.Parent = bar
track(close.Activated:Connect(function() frame.Visible = false end))
draggable(title, frame)

local order = 0
local function toggle(text, key)
    order = order + 1
    local b = Instance.new("TextButton")
    b.Size = UDim2.new(1, 0, 0, 28)
    b.BorderSizePixel = 0
    b.Font = Enum.Font.Code
    b.TextSize = 14
    b.TextColor3 = Color3.new(1, 1, 1)
    b.LayoutOrder = order
    local function refresh()
        b.Text = text .. ": " .. (cfg[key] and "ON" or "OFF")
        b.BackgroundColor3 = cfg[key] and Color3.fromRGB(40, 120, 70) or Color3.fromRGB(40, 40, 48)
    end
    track(b.Activated:Connect(function() cfg[key] = not cfg[key]; refresh() end))
    refresh()
    b.Parent = frame
end
toggle("Bot running", "Run")
toggle("AI (OpenRouter)", "UseAI")
toggle("Siege defense", "AutoDefend")
toggle("Monsters (hunt/tame)", "Monsters")
toggle("Allies", "Allies")
toggle("Route scouting", "Scout")

order = order + 1
statusLabel = Instance.new("TextLabel")
statusLabel.Size = UDim2.new(1, 0, 0, 34)
statusLabel.BackgroundColor3 = Color3.fromRGB(28, 28, 34)
statusLabel.BorderSizePixel = 0
statusLabel.Font = Enum.Font.Code
statusLabel.TextSize = 12
statusLabel.TextColor3 = Color3.fromRGB(180, 255, 180)
statusLabel.TextWrapped = true
statusLabel.Text = "starting"
statusLabel.LayoutOrder = order
statusLabel.Parent = frame

order = order + 1
logLabel = Instance.new("TextLabel")
logLabel.Size = UDim2.new(1, 0, 0, 0)
logLabel.AutomaticSize = Enum.AutomaticSize.Y
logLabel.BackgroundColor3 = Color3.fromRGB(14, 14, 18)
logLabel.BorderSizePixel = 0
logLabel.Font = Enum.Font.Code
logLabel.TextSize = 12
logLabel.TextColor3 = Color3.new(1, 1, 1)
logLabel.TextXAlignment = Enum.TextXAlignment.Left
logLabel.TextWrapped = true
logLabel.Text = "-"
logLabel.LayoutOrder = order
logLabel.Parent = frame

local mp = saved.mini or { 12, 70 }
mini = Instance.new("TextButton")
mini.Size = UDim2.fromOffset(44, 44)
mini.Position = UDim2.fromOffset(mp[1], mp[2])
mini.BackgroundColor3 = Color3.fromRGB(30, 30, 38)
mini.BorderSizePixel = 0
mini.Font = Enum.Font.Code
mini.TextSize = 15
mini.TextColor3 = Color3.new(1, 1, 1)
mini.Text = "AI"
mini.Parent = gui
draggable(mini, mini, function() frame.Visible = not frame.Visible end)

env.__ANT_STOP = function()
    alive = false
    scoutPos = nil
    for _, c in ipairs(conns) do pcall(function() c:Disconnect() end) end
    pcall(function() gui:Destroy() end)
end

log("loaded v4. model=" .. cfg.Model .. (httpReq and "" or " | NO request()!") .. (hookOK and " | scouting hook OK" or " | NO hook: routes only learned from casualties/probes"))
