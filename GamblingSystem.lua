--!strict
-- ServerScriptService.GamblingSystem
-- handles all server-side gacha/crate spinning logic, from weight calculation
-- to awarding items, pity systems, and cross-server lucky pull broadcasts

-- --- Services ------------------------------------------------------
-- pulling in all the roblox services we need upfront so nothing errors later

local Players             = game:GetService("Players")
local ReplicatedStorage   = game:GetService("ReplicatedStorage")
local ServerScriptService = game:GetService("ServerScriptService")
local HttpService         = game:GetService("HttpService")
local MessagingService    = game:GetService("MessagingService")
local Workspace           = game:GetService("Workspace")
local MemoryStoreService  = game:GetService("MemoryStoreService")

-- --- Remotes -------------------------------------------------------
-- these are the remote events the client fires to request a spin
-- and receive lucky pull chat messages

local RemoteEvents        = ReplicatedStorage:WaitForChild("RemoteEvents")
local SpinRemote          = RemoteEvents:FindFirstChild("SpinGacha") :: RemoteEvent?
local LuckyPullChatRemote = RemoteEvents:FindFirstChild("LuckyPullChat") :: RemoteEvent?

-- --- Modules -------------------------------------------------------
-- loading all required modules - dictionary holds item/crate definitions,
-- playerDataService manages persistent player data, and the rest are
-- various helper services for progression, indexing, rate limiting, etc.

local Dictionary                  = require(ReplicatedStorage:WaitForChild("Dictionary"))
local PlayerDataService           = require(ServerScriptService:WaitForChild("Data"):WaitForChild("PlayerDataHandler"))
local RollProgressionService      = require(ServerScriptService.Services:WaitForChild("RollProgressionService"))
local IndexService                = require(ServerScriptService.Services:WaitForChild("IndexService"))
local ExistsService               = require(ServerScriptService.Services:WaitForChild("ExistsService"))
local ActiveCrateLimiterService   = require(ServerScriptService.Services:WaitForChild("ActiveCrateLimiterService"))
local GachaTokens                 = require(ServerScriptService:WaitForChild("GamblingTokens"))
local Format                      = require(ReplicatedStorage.Modules._Utility.Format)
local AdvancedGradientRichText    = require(ReplicatedStorage.Modules._Utility.AdvancedGradientRichText)
local Console                     = require(ReplicatedStorage:WaitForChild("Modules"):WaitForChild("_Shared"):WaitForChild("Console"))

local Logger = Console:CreateLogger("GamblingSystem")
Logger:Begin()

-- optional rate limit module, only require it if it actually exists in the tree
local RateLimitModule = ServerScriptService:FindFirstChild("RateLimit")
local RateLimit       = RateLimitModule and require(RateLimitModule) or nil

-- --- Dictionary ----------------------------------------------------
-- shorthand references to the baddies (collectible items) and crates tables
-- from the shared dictionary so we dont have to type Dictionary.X everywhere

local Baddies = Dictionary.Baddies
local Crates  = Dictionary.Crates

-- --- Optional services --------------------------------------------
-- weather service is optional because not every place uses the weather system,
-- so we pcall the require and just set it to nil if it fails

local WeatherService: any = nil
do
	local ok, svc = pcall(function()
		return require(ServerScriptService.Services:WaitForChild("WeatherService"))
	end)
	if ok then
		WeatherService = svc
	end
end

-- --- Assets --------------------------------------------------------
-- references to the client-side model folder and animations so we can
-- clone models for the lucky pull showcase display

local ClientAssets  = ReplicatedStorage:WaitForChild("ClientAssets")
local BaddiesFolder = ClientAssets:WaitForChild("Baddies")
local Animations    = ClientAssets:WaitForChild("Animations")
local IdleAnim      = Animations:FindFirstChild("Idle")

-- --- Config --------------------------------------------------------
-- main tuning knobs for the whole system. release mode controls whether
-- the active crate slot frees up immediately or waits for the client
-- reveal animation to finish before allowing another spin

local RELEASE_MODE: "immediate" | "delay" = "delay"
local RELEASE_AFTER_SECONDS               = 7

local CONFIG = {
	SpinCooldownSeconds    = 1.25,   -- minimum time between spins
	MinSpinCooldownSeconds = 0.45,   -- hard floor for cooldown

	SlotCount              = 50,     -- total visual slots in the spin strip
	WinnerIndex            = 45,     -- which slot the actual winner sits at

	LuckyPullMinOrder      = 10,     -- rarity order threshold to trigger a server-wide lucky pull announcement
	LuckyPullTopic         = "MostRecentLuckyPull_v1",
	MaxLuckyPullsPerSec    = 2,      -- rate limit for broadcasting lucky pulls

	LuckExponentPerOrder   = 0.35,   -- controls how much luck scales per rarity tier
	LuckBoostClamp         = { Min = 0.90, Max = 7.50 },  -- prevents luck from going too crazy in either direction

	WeightCacheTTL         = 60,     -- seconds before we refresh the base weight cache
	ResultPoolSize         = 10,     -- how many result tables we keep pooled for reuse

	WeightMin              = 1e-12,  -- floor so no weight ever hits exactly zero
}

-- memory store sorted map for persisting the most recent lucky pull across servers
local LATEST_PULL_KEY = "MostRecentLuckyPull_Latest_v1"
local latestPullMap   = MemoryStoreService:GetSortedMap(LATEST_PULL_KEY)

-- --- State ---------------------------------------------------------
-- luckySeen tracks pull ids we already processed so we dont double-broadcast,
-- cachedEntries holds the full item pool after first load,
-- rarityOrderCache avoids repeated lookups for the same rarity string

local luckySeen: { [string]: boolean } = {}
local cachedEntries: { any }?          = nil
local rarityOrderCache: { [string]: number } = {}

-- base weight cache with a ttl so we periodically pick up any dictionary changes
local baseWeightCache: { [string]: number } = {}
local weightCacheTime                       = 0

-- object pool for result tables to reduce garbage collection pressure during spins
local resultTablePool: { { any } } = {}

local lastLuckyPullBroadcast = 0

-- --- Result table pooling ------------------------------------------
-- instead of allocating a new 50-slot table every spin, we reuse old ones
-- from the pool. getResultTable grabs one or creates a fresh one,
-- returnResultTable puts it back for later use

local function getResultTable(): { any }
	local t = table.remove(resultTablePool)
	if t then
		table.clear(t)
		return t
	end

	return table.create(CONFIG.SlotCount)
end

local function returnResultTable(t: { any })
	if #resultTablePool < CONFIG.ResultPoolSize then
		table.insert(resultTablePool, t)
	end
end

-- --- Small utils ---------------------------------------------------
-- basic math helpers - custom clamp because we use it in hot paths,
-- clampLuckMult sanitizes luck values so nan or negatives default to 1,
-- randRange gives a random float between min and max rounded to 2 decimals

local function clamp(n: number, a: number, b: number): number
	if n < a then return a end
	if n > b then return b end
	return n
end

local function clampLuckMult(x: number): number
	if type(x) ~= "number" or x ~= x or x <= 0 then
		return 1
	end
	return x
end

local function randRange(minV: number, maxV: number): number
	if type(minV) ~= "number" then minV = 1 end
	if type(maxV) ~= "number" then maxV = 1 end
	if minV > maxV then minV, maxV = maxV, minV end
	return math.floor((minV + (maxV - minV) * math.random()) * 100 + 0.5) / 100
end

-- quick wrapper to grab a players data store, returns nil if not loaded yet
local function getStore(player: Player): any?
	return PlayerDataService.GetData(player)
end

-- fire-and-forget write to memory store so other servers can see the latest lucky pull
local function safeSetLatestPull(payload: any)
	task.spawn(function()
		pcall(function()
			latestPullMap:SetAsync("latest", payload, 86400)
		end)
	end)
end

-- try to read latest lucky pull from memory store, returns nil on failure
local function safeGetLatestPull(): any?
	local ok, value = pcall(function()
		return latestPullMap:GetAsync("latest")
	end)
	return ok and value or nil
end

-- looks up the numeric order for a rarity string (like "common" = 1, "legendary" = 8 etc)
-- caches results so we only call into the dictionary module once per rarity
local function safeGetRarityOrder(rarity: string): number
	local cached = rarityOrderCache[rarity]
	if cached then
		return cached
	end

	local order = 1
	if Baddies and type(Baddies.GetRarityOrder) == "function" then
		local ok, v = pcall(Baddies.GetRarityOrder, rarity)
		if ok and type(v) == "number" then
			order = v
		end
	end

	rarityOrderCache[rarity] = order
	return order
end

-- --- Entries -------------------------------------------------------
-- builds and caches the full list of rollable items from the dictionary.
-- tries the proper GetAllEntries api first, falls back to manually iterating
-- the baddies table if that method doesnt exist. sorts by rarity descending
-- so higher rarity items come first in the list

local function getAllEntries(): { any }
	if cachedEntries then
		return cachedEntries
	end

	if Baddies and type(Baddies.GetAllEntries) == "function" then
		local ok, list = pcall(Baddies.GetAllEntries)
		if ok and type(list) == "table" then
			cachedEntries = list
			return cachedEntries
		end
	end

	-- fallback: manually build entries from the raw baddies table
	local out = {}
	local t   = Baddies and Baddies.Baddies
	if type(t) == "table" then
		for name, info in pairs(t) do
			if type(name) == "string" and name ~= "" and type(info) == "table" then
				out[#out + 1] = {
					Name        = name,
					DisplayName = info.DisplayName or name,
					Rarity      = info.Rarity or "Common",
				}
			end
		end
	end

	table.sort(out, function(a, b)
		local oa = safeGetRarityOrder(a.Rarity)
		local ob = safeGetRarityOrder(b.Rarity)
		if oa ~= ob then return oa > ob end
		return a.Name < b.Name
	end)

	cachedEntries = out
	return cachedEntries
end

-- --- Weather luck --------------------------------------------------
-- weather can apply a global luck multiplier to all rolls. we cache these
-- values for 30 seconds so we dont spam the weather service every single spin.
-- supports two possible method names since the api changed at some point

local weatherLuckCache: { [string]: number } = {}
local weatherCacheTime                       = 0

local function safeGetWeatherLuckMult(weatherId: any): number
	if type(weatherId) ~= "string" or weatherId == "" or weatherId == "None" then
		return 1
	end

	local now = os.clock()
	if now - weatherCacheTime > 30 then
		table.clear(weatherLuckCache)
		weatherCacheTime = now
	end

	local cached = weatherLuckCache[weatherId]
	if cached then
		return cached
	end

	local mult = 1
	if WeatherService then
		if type(WeatherService.GetLuckMultiplier) == "function" then
			local ok, v = pcall(WeatherService.GetLuckMultiplier, weatherId)
			if ok and type(v) == "number" and v > 0 then mult = v end
		elseif type(WeatherService.GetLuckMult) == "function" then
			local ok, v = pcall(WeatherService.GetLuckMult, weatherId)
			if ok and type(v) == "number" and v > 0 then mult = v end
		end
	end

	weatherLuckCache[weatherId] = mult
	return mult
end

-- --- Weights -------------------------------------------------------
-- getBaseWeight fetches the raw drop weight for an item from the dictionary,
-- cached with a configurable ttl so hot-reloading dictionary changes
-- eventually propagate without needing a server restart

local function getBaseWeight(name: string): number
	local now = os.clock()
	if now - weightCacheTime > CONFIG.WeightCacheTTL then
		table.clear(baseWeightCache)
		weightCacheTime = now
	end

	local cached = baseWeightCache[name]
	if cached then
		return cached
	end

	local w = 0
	if Baddies and type(Baddies.GetWeight) == "function" then
		local ok, result = pcall(Baddies.GetWeight, name, nil)
		if ok and type(result) == "number" and result > 0 then
			w = result
		end
	end

	baseWeightCache[name] = w
	return w
end

-- takes a base weight and applies luck scaling, crate-specific multipliers,
-- and order-based exponential boosting. higher rarity items benefit more
-- from luck because the exponent grows with rarity order. the clamp
-- prevents extreme outliers from breaking the distribution
local function applyLuckAndCrateToWeight(baseW: number, order: number, crateType: string, luckMult: number): number
	if baseW <= 0 then return 0 end

	local crateLuck      = 1
	local crateOrderMult = 1

	-- some crate types have their own luck multiplier and per-order weight scaling
	if Crates then
		if type(Crates.GetCrateLuckMult) == "function" then
			crateLuck = tonumber(Crates.GetCrateLuckMult(crateType)) or 1
		end
		if type(Crates.GetOrderWeightMultiplier) == "function" then
			crateOrderMult = tonumber(Crates.GetOrderWeightMultiplier(crateType, order)) or 1
		end
	end

	-- combine player luck with crate luck, floor at 1 so it never nerfs
	local effectiveLuck = math.max(1, clampLuckMult(luckMult) * math.max(1, crateLuck))

	-- exponential boost: higher order items get more benefit from luck
	-- order 1 (common) gets no boost, order 2+ gets progressively more
	local power    = math.max(0, order - 1) * CONFIG.LuckExponentPerOrder
	local luckBoost = 1
	if power > 0 then
		luckBoost = effectiveLuck ^ power
		luckBoost = clamp(luckBoost, CONFIG.LuckBoostClamp.Min, CONFIG.LuckBoostClamp.Max)
	end

	local w = baseW * crateOrderMult * luckBoost
	return math.max(w, CONFIG.WeightMin)
end

-- filters the item pool to only include items at or above a minimum rarity order,
-- used by the hard pity system to guarantee a certain rarity floor
local function filterPoolMinOrder(pool: { any }, minOrder: number): { any }
	if minOrder <= 0 then
		return pool
	end

	local out = {}
	for _, e in ipairs(pool) do
		if safeGetRarityOrder(e.Rarity) >= minOrder then
			out[#out + 1] = e
		end
	end
	return out
end

-- weighted random selection from a pool of items. builds a cumulative weight
-- table factoring in luck, crate bonuses, and soft pity multipliers, then
-- picks a random point along the total weight and walks forward to find the winner.
-- this is the core roll function for the actual winning item
local function rollFromPoolWeighted(pool: { any }, crateType: string, luckMult: number, pitySnap: { [string]: number }): any?
	local n = #pool
	if n == 0 then return nil end

	local total   = 0
	local weights = table.create(n)

	for i = 1, n do
		local entry = pool[i]
		local order = safeGetRarityOrder(entry.Rarity)
		local baseW = getBaseWeight(entry.Name)

		-- soft pity gives a gradual multiplier boost the longer you go without hitting a rarity
		local pityMult = RollProgressionService.GetSoftPityMultiplier(order, pitySnap)
		local w        = applyLuckAndCrateToWeight(baseW, order, crateType, luckMult) * pityMult

		weights[i] = w
		total     += w
	end

	-- if all weights are zero somehow, just pick uniformly at random
	if total <= 0 then
		return pool[math.random(1, n)]
	end

	-- standard cumulative weight selection
	local r = math.random() * total
	local c = 0
	for i = 1, n do
		c += weights[i]
		if r <= c then
			return pool[i]
		end
	end

	return pool[n]
end

-- simpler weighted roll just using base weights with no luck or pity applied,
-- used for filling the non-winning visual slots in the spin strip
local function rollFiller(pool: { any }): any?
	local n = #pool
	if n == 0 then return nil end

	local total   = 0
	local weights = table.create(n)

	for i = 1, n do
		local w = getBaseWeight(pool[i].Name)
		weights[i] = w
		total     += w
	end

	if total <= 0 then
		return pool[math.random(1, n)]
	end

	local r = math.random() * total
	local c = 0
	for i = 1, n do
		c += weights[i]
		if r <= c then
			return pool[i]
		end
	end

	return pool[n]
end

-- --- Spin generation ----------------------------------------------
-- builds the full array of 50 items for the visual spin strip.
-- the real winner goes at index 45 (so the animation lands on it),
-- and the rest are filler items rolled with base weights only.
-- handles weather luck, new player boosts, hard pity floors, and
-- guaranteed item overrides from special tokens

local function generateSpinResults(
	player: Player,
	crateType: string,
	weatherId: string?,
	luckMultFromToken: number,
	pitySnap: { [string]: number },
	guaranteedName: string?
): ({ any }, number)
	local pool    = getAllEntries()
	local results = getResultTable()

	if #pool == 0 then
		return results, CONFIG.WinnerIndex
	end

	-- combine token luck with weather luck into one base value
	local weatherLuck = safeGetWeatherLuckMult(weatherId)
	local baseLuck    = clampLuckMult((tonumber(luckMultFromToken) or 1) * weatherLuck)

	-- roll progression service applies any new player boost on top of base luck
	-- this is the single source of truth for effective luck so nothing stacks weird
	local combinedLuck = clampLuckMult(RollProgressionService.ApplyEffectiveLuck(player, baseLuck))

	-- hard pity check: if the player has gone too long without a rare drop,
	-- we force the pool to only contain items above a certain rarity threshold
	local forceMinOrder = RollProgressionService.GetHardMinOrder(pitySnap)
	local winnerPool    = pool

	if forceMinOrder > 0 then
		local filtered = filterPoolMinOrder(pool, forceMinOrder)
		if #filtered > 0 then
			winnerPool = filtered
		end
	end

	-- if the token had a guaranteed item name, try to find it in the pool first
	local winner: any? = nil
	if type(guaranteedName) == "string" and guaranteedName ~= "" then
		for _, e in ipairs(winnerPool) do
			if e.Name == guaranteedName then
				winner = e
				break
			end
		end
	end

	-- normal weighted roll if no guarantee was set or the guaranteed item wasnt found
	if not winner then
		winner = rollFromPoolWeighted(winnerPool, crateType, combinedLuck, pitySnap) or winnerPool[1]
	end

	-- place winner at the designated index, fill the rest with visual filler
	results[CONFIG.WinnerIndex] = winner

	for i = 1, CONFIG.SlotCount do
		if i ~= CONFIG.WinnerIndex then
			results[i] = rollFiller(pool) or pool[1]
		end
	end

	return results, CONFIG.WinnerIndex
end

-- --- Data safety helpers ------------------------------------------
-- makes sure nested tables exist in the players data store before we try
-- to write into them. walks through a path of keys and creates empty
-- tables at each level if they dont already exist. prevents nil index
-- errors when the client reads the data later

local function ensureTablePath(player: Player, parts: { string })
	if not PlayerDataService.IsReady(player) then return end
	local store = PlayerDataService.GetData(player)
	if type(store) ~= "table" then return end

	local cur: any         = store
	local built: { string } = {}

	for i = 1, #parts do
		local key = parts[i]
		built[i]  = key

		if type(cur[key]) ~= "table" then
			PlayerDataService.SetKey(player, built, {})
			if type(cur[key]) ~= "table" then
				cur[key] = {}
			end
		end

		cur = cur[key]
	end
end

-- --- Award ---------------------------------------------------------
-- creates the actual item in the players data after a winning roll.
-- generates a uuid for the instance, rolls random stat multipliers
-- within the rarity-defined ranges, increments the owned count,
-- stores the full instance details, and updates the global exists
-- counter plus the players discovery index

local function awardBaddie(player: Player, wonEntry: any, crateType: string, weatherId: string?): (string?)
	local baddieUUID = HttpService:GenerateGUID(false)

	-- make sure the parent tables exist so clients dont hit nil references
	ensureTablePath(player, { "Baddies" })
	ensureTablePath(player, { "BaddieInstances" })

	-- grab the stat multiplier ranges for this item (coins, gems, luck)
	-- defaults are pretty tight ranges if the dictionary doesnt specify
	local ranges
	if Baddies and type(Baddies.GetMultipliers) == "function" then
		local ok, r = pcall(Baddies.GetMultipliers, wonEntry.Name)
		if ok and type(r) == "table" then
			ranges = r
		end
	end
	ranges = ranges or { Coins = { 1.00, 1.10 }, Gems = { 1.00, 1.06 }, Luck = { 1.00, 1.02 } }

	local coinsRange = ranges.Coins or ranges.Cash or { 1, 1.10 }
	local gemsRange  = ranges.Gems or { 1, 1.06 }
	local luckRange  = ranges.Luck or { 1, 1.02 }

	-- roll each stat independently within its range
	local coins = randRange(coinsRange[1], coinsRange[2])
	local gems  = randRange(gemsRange[1], gemsRange[2])
	local luck  = randRange(luckRange[1], luckRange[2])

	local obtainedAt = os.time()

	-- increment the simple "how many of this item do i own" counter
	do
		local store = getStore(player)
		local cur   = 0
		if store and type(store.Baddies) == "table" then
			cur = tonumber(store.Baddies[wonEntry.Name]) or 0
		end
		PlayerDataService.SetKey(player, { "Baddies", wonEntry.Name }, cur + 1)
	end

	-- store the full instance with all its rolled stats under the uuid key
	PlayerDataService.SetKey(player, { "BaddieInstances", baddieUUID }, {
		Name        = wonEntry.Name,
		DisplayName = wonEntry.DisplayName,
		Rarity      = wonEntry.Rarity,
		ObtainedAt  = obtainedAt,
		Favourited  = false,
		WeatherId   = (type(weatherId) == "string" and weatherId ~= "" and weatherId ~= "None") and weatherId or nil,
		Stats = {
			Coins = coins,
			Gems  = gems,
			Luck  = luck,
		},
	})

	-- bump the global counter for how many of this item exist across all players
	task.spawn(function()
		pcall(function()
			ExistsService.Increment(wonEntry.Name, 1)
		end)
	end)

	-- mark this item as discovered in the players collection index for this crate
	if IndexService and type(IndexService.MarkDiscovered) == "function" then
		pcall(function()
			IndexService.MarkDiscovered(player, crateType, wonEntry.Name)
		end)
	end

	return baddieUUID
end

-- --- Lucky pull visuals -------------------------------------------
-- these functions handle the in-world showcase model and chat broadcast
-- that fires when someone pulls a really rare item

-- makes sure a model has an animator component so we can play animations on it.
-- checks for a humanoid first, falls back to creating an animation controller
-- if the model doesnt have one (for non-humanoid display models)
local function ensureAnimatorOnModel(model: Model): Animator?
	local hum = model:FindFirstChildOfClass("Humanoid")
	if hum then
		local animator = hum:FindFirstChildOfClass("Animator")
		if not animator then
			animator        = Instance.new("Animator")
			animator.Parent = hum
		end
		return animator
	end

	local ac = model:FindFirstChildOfClass("AnimationController")
	if not ac then
		ac      = Instance.new("AnimationController")
		ac.Name = "AnimationController"
		ac.Parent = model
	end

	local animator = ac:FindFirstChildOfClass("Animator")
	if not animator then
		animator        = Instance.new("Animator")
		animator.Parent = ac
	end
	return animator
end

-- loads and plays the idle animation on a showcase model so it doesnt just stand there frozen
local function playIdle(model: Model)
	if not IdleAnim or not IdleAnim:IsA("Animation") then return end
	local animator = ensureAnimatorOnModel(model)
	if not animator then return end

	task.spawn(function()
		local ok, track = pcall(function()
			return animator:LoadAnimation(IdleAnim)
		end)
		if ok and track then
			track.Looped = true
			pcall(function()
				track:Play(0.1, 1, 1)
			end)
		end
	end)
end

-- abbreviates large numbers for the chat message (1500000 becomes 1.5M etc)
local function shortInt(n: number): string
	n = math.floor(tonumber(n) or 0)
	if n < 1000 then return tostring(n) end

	local units = {
		{ 1e15, "Q" },
		{ 1e12, "T" },
		{ 1e9,  "B" },
		{ 1e6,  "M" },
		{ 1e3,  "K" },
	}

	for _, u in ipairs(units) do
		if n >= u[1] then
			local v = n / u[1]
			if v < 10 then
				return string.format("%.1f%s", v, u[2]):gsub("%.0", "")
			else
				return string.format("%d%s", math.floor(v + 0.5), u[2])
			end
		end
	end

	return tostring(n)
end

-- generates two slightly shifted colors from a base rarity color to create
-- a gradient effect. higher rarity items get a slightly bigger hue shift
-- so they look more visually distinct in the chat announcement
local function gradientFromRarityColor(base: Color3, rarity: string?): (Color3, Color3)
	local h, s, v = base:ToHSV()
	local order   = rarity and safeGetRarityOrder(rarity) or 1

	local hueShift = (0.035 + (order - 1) * 0.006) % 1
	local s0       = math.clamp(s * 0.90 + 0.18, 0, 1)
	local s1       = math.clamp(s * 1.05 + 0.10, 0, 1)
	local v0       = math.clamp(v * 1.18 + 0.06, 0, 1)
	local v1       = math.clamp(v * 0.70 + 0.02, 0, 1)

	return Color3.fromHSV(h, s0, v0), Color3.fromHSV((h + hueShift) % 1, s1, v1)
end

-- builds the rich text and plain text versions of the lucky pull chat message.
-- applies a gradient color sequence based on the rarity so rare pulls
-- really pop in the chat with a colorful announcement
local function buildLuckyPullMessage(pullerName: string, wonEntry: any, denomOverride: number?): { RichText: string, PlainText: string }
	local baddieName = wonEntry and (wonEntry.DisplayName or wonEntry.Name) or "???"
	local rarity     = wonEntry and wonEntry.Rarity or "Common"

	-- figure out the odds denominator for the "1 in X" display text
	local denom = tonumber(denomOverride) or 0
	if denom <= 0 and Dictionary.Baddies and Dictionary.Baddies.GetOddsDenom and wonEntry then
		denom = tonumber(Dictionary.Baddies.GetOddsDenom(wonEntry.Name)) or 0
	end

	local oddsText = denom > 0 and (" (1 in " .. shortInt(denom) .. ")") or ""
	local plain    = string.format("LUCKY PULL! %s pulled %s%s", pullerName, baddieName, oddsText)

	-- get the rarity color and build a gradient sequence for the rich text
	local baseColour = Color3.new(1, 1, 1)
	if Dictionary.Baddies and type(Dictionary.Baddies.GetRarityColor) == "function" then
		local ok, c = pcall(Dictionary.Baddies.GetRarityColor, rarity)
		if ok and typeof(c) == "Color3" then
			baseColour = c
		end
	end

	local c0, c1 = gradientFromRarityColor(baseColour, rarity)
	local seq    = ColorSequence.new({
		ColorSequenceKeypoint.new(0, c0),
		ColorSequenceKeypoint.new(1, c1),
	})

	local rich = AdvancedGradientRichText(plain, seq)
	return { RichText = rich, PlainText = plain }
end

-- fires the lucky pull message to every player in this server via remote event
local function broadcastLuckyPullChat(pullerName: string, wonEntry: any, denomOverride: number?)
	if LuckyPullChatRemote and LuckyPullChatRemote:IsA("RemoteEvent") then
		local msg = buildLuckyPullMessage(pullerName, wonEntry, denomOverride)
		LuckyPullChatRemote:FireAllClients(msg)
	end
end

-- places the pulled model in the world showcase area. destroys any existing
-- showcase model first, clones from the template, anchors all parts so it
-- doesnt fall through the ground, scales it up, and plays idle animation
local function throwLuckyPullToShowcase(wonName: string)
	local thrown = Workspace:FindFirstChild("__THROWN")
	if not thrown then
		thrown      = Instance.new("Folder")
		thrown.Name = "__THROWN"
		thrown.Parent = Workspace
	end

	-- the marker part defines where the showcase model gets positioned
	local marker = thrown:FindFirstChild("MostRecentLuckyPull")
	if not marker or not marker:IsA("BasePart") then return end

	local template = BaddiesFolder:FindFirstChild(wonName)
	if not template or not template:IsA("Model") then return end

	-- clear out the old showcase model before placing the new one
	for _, ch in ipairs(thrown:GetChildren()) do
		if ch:IsA("Model") then
			ch:Destroy()
		end
	end

	local clone = template:Clone()
	clone.Name  = wonName
	clone.Parent = thrown

	-- anchor everything and disable all collision so it purely visual
	for _, d in ipairs(clone:GetDescendants()) do
		if d:IsA("BasePart") then
			d.Anchored  = true
			d.CanCollide = false
			d.CanTouch   = false
			d.CanQuery   = false
		end
	end

	pcall(function() clone:ScaleTo(3) end)
	pcall(function() clone:PivotTo(marker.CFrame) end)

	playIdle(clone)
end

-- publishes a lucky pull to all other game servers via messaging service
-- and persists it to memory store. rate limited so we dont flood the network
-- if multiple people pull rare items at the same time
local function publishLuckyPull(pullId: string, pullerName: string, wonEntry: any, denomOverride: number?)
	local now = os.clock()
	if now - lastLuckyPullBroadcast < (1 / CONFIG.MaxLuckyPullsPerSec) then
		return
	end
	lastLuckyPullBroadcast = now

	local payload = {
		PullId      = pullId,
		Name        = wonEntry and wonEntry.Name,
		DisplayName = wonEntry and (wonEntry.DisplayName or wonEntry.Name),
		Rarity      = wonEntry and wonEntry.Rarity,
		PullerName  = pullerName,
		OddsDenom   = tonumber(denomOverride) or 0,
		At          = os.time(),
	}

	-- persist to memory store so new servers can show the latest pull on join
	safeSetLatestPull(payload)

	-- broadcast to all active servers
	task.spawn(function()
		pcall(function()
			MessagingService:PublishAsync(CONFIG.LuckyPullTopic, payload)
		end)
	end)
end

-- handles incoming lucky pull messages from other servers (or memory store on init).
-- deduplicates by pull id so the same pull never triggers twice, then updates
-- the showcase model and optionally fires the chat announcement
local function onLuckyPullMessage(payload: any, silent: boolean?)
	if type(payload) ~= "table" then return end

	local pullId = payload.PullId
	if type(pullId) ~= "string" or pullId == "" then return end
	if luckySeen[pullId] then return end
	luckySeen[pullId] = true

	local modelName = payload.Name
	if type(modelName) ~= "string" or modelName == "" then return end

	throwLuckyPullToShowcase(modelName)
	if silent then return end

	local pullerName = (type(payload.PullerName) == "string" and payload.PullerName ~= "") and payload.PullerName or "Someone"
	local wonEntry   = {
		Name        = payload.Name,
		DisplayName = payload.DisplayName or payload.Name,
		Rarity      = payload.Rarity or "Common",
	}

	if LuckyPullChatRemote and LuckyPullChatRemote:IsA("RemoteEvent") then
		local msg = buildLuckyPullMessage(pullerName, wonEntry, tonumber(payload.OddsDenom))
		LuckyPullChatRemote:FireAllClients(msg)
	end
end

-- subscribe to cross-server lucky pull messages so we display them in real time
pcall(function()
	MessagingService:SubscribeAsync(CONFIG.LuckyPullTopic, function(msg)
		onLuckyPullMessage(msg and msg.Data, false)
	end)
end)

-- on server startup, load the most recent lucky pull from memory store
-- and silently place the model in the showcase (no chat message since its old)
task.spawn(function()
	local payload = safeGetLatestPull()
	if payload then
		onLuckyPullMessage(payload, true)
	end
end)

-- --- Active slot release ------------------------------------------
-- releases the players active crate slot so they can spin again.
-- in immediate mode it frees instantly, in delay mode it waits
-- a few seconds for the client reveal animation to finish first

local function releaseActive(player: Player, requestUUID: string)
	if RELEASE_MODE == "immediate" then
		pcall(function()
			ActiveCrateLimiterService:Finish(player, requestUUID)
		end)
	else
		task.delay(RELEASE_AFTER_SECONDS, function()
			pcall(function()
				ActiveCrateLimiterService:Finish(player, requestUUID)
			end)
		end)
	end
end

-- --- Server event --------------------------------------------------
-- main spin handler. this fires when the client sends a spin request.
-- flow: validate -> consume token -> build pity snapshot -> roll ->
-- award item -> update progression -> broadcast if lucky -> send results back.
-- wrapped in pcall with cleanup so we always release the active slot even if something errors

if not SpinRemote then
	Console:Warn("GamblingSystem", "SpinGacha remote missing")
else
	SpinRemote.OnServerEvent:Connect(function(player: Player, requestUUID: any)
		-- basic validation to make sure the request is legit
		if typeof(player) ~= "Instance" or not player:IsA("Player") then return end
		if type(requestUUID) ~= "string" or requestUUID == "" then return end
		if not PlayerDataService.IsReady(player) then return end

		-- consume the gacha token - this is the only gate that decides if the spin proceeds.
		-- if the player doesnt have a valid token, we bail here
		local tokenMeta = GachaTokens.Consume(player, requestUUID)
		if not tokenMeta then
			return
		end

		local didReturnResults = false
		local resultsToReturn: { any }? = nil

		-- cleanup runs no matter what, even if the spin logic errors out.
		-- returns the pooled table and releases the active crate slot
		local function cleanup()
			if resultsToReturn then
				local t = resultsToReturn
				resultsToReturn = nil
				task.delay(5, function()
					returnResultTable(t)
				end)
			end

			releaseActive(player, requestUUID)
		end

		local ok, err = pcall(function()
			-- pull metadata out of the consumed token
			local weatherId: string? = nil
			local luckMultFromToken  = 1
			local crateType          = "Default"
			local guaranteed: string? = nil

			if type(tokenMeta) == "table" then
				if type(tokenMeta.WeatherId) == "string" then
					weatherId = tokenMeta.WeatherId
				end

				luckMultFromToken = tonumber(tokenMeta.LuckMult) or 1

				if type(tokenMeta.CrateType) == "string" and tokenMeta.CrateType ~= "" then
					crateType = tokenMeta.CrateType
				end

				if type(tokenMeta.GuaranteedBaddie) == "string" and tokenMeta.GuaranteedBaddie ~= "" then
					guaranteed = tokenMeta.GuaranteedBaddie
				end
			end

			-- initialize pity tracking tables for this crate type if first time
			RollProgressionService.EnsurePityCrate(player, crateType)

			local store = PlayerDataService.GetData(player)
			if not store then return end

			-- snapshot the current pity counters before rolling so the roll
			-- uses consistent values even if something else writes mid-spin
			local pitySnap = RollProgressionService.GetPitySnapshot(store, crateType)

			-- generate the full spin strip and pick the winner
			local results, winnerIndex = generateSpinResults(player, crateType, weatherId, luckMultFromToken, pitySnap, guaranteed)
			resultsToReturn = results

			local won = results[winnerIndex]
			if not won then
				return
			end

			-- write the item into the players data store
			local baddieUUID = awardBaddie(player, won, crateType, weatherId)
			if not baddieUUID then
				return
			end

			-- record this roll in the progression system and compute new pity values
			local wonOrder = safeGetRarityOrder(won.Rarity)
			RollProgressionService.RecordRoll(player, crateType, wonOrder)

			local newPity = RollProgressionService.ComputeNewPity(pitySnap, wonOrder)
			RollProgressionService.CommitPity(player, crateType, newPity)

			-- if the pull was rare enough, broadcast it to everyone in all servers
			if wonOrder >= CONFIG.LuckyPullMinOrder then
				local pullId = HttpService:GenerateGUID(false)
				luckySeen[pullId] = true

				throwLuckyPullToShowcase(won.Name)
				broadcastLuckyPullChat(player.Name, won, nil)
				publishLuckyPull(pullId, player.Name, won, nil)
			end

			-- send the full spin results back to the client for the visual animation
			SpinRemote:FireClient(player, {
				Success     = true,
				UUID        = requestUUID,
				Results     = results,
				WinnerIndex = winnerIndex,
				WonBaddie   = won,
				BaddieUUID  = baddieUUID,
				WeatherId   = weatherId,
				LuckMult    = luckMultFromToken,
				CrateType   = crateType,
				Pity        = newPity,
			})

			didReturnResults = true
		end)

		-- always run cleanup even if the pcall caught an error
		cleanup()

		if not ok then
			warn(("[GamblingSystem] Spin handler error (%s): %s"):format(player.Name, tostring(err)))
		end
	end)
end

-- --- Cleanup -------------------------------------------------------
-- release any held gacha tokens when a player leaves so nothing leaks

Players.PlayerRemoving:Connect(function(player: Player)
	GachaTokens.Cleanup(player)
end)

-- periodic sweep to prevent the luckySeen dedup table from growing forever.
-- checks every 5 minutes and clears it if it gets above 1000 entries.
-- this is fine because pull ids are random guids so collisions are not a concern
task.spawn(function()
	while true do
		task.wait(300)

		local count = 0
		for _ in pairs(luckySeen) do
			count += 1
		end

		if count > 1000 then
			table.clear(luckySeen)
		end
	end
end)

Logger:End()
