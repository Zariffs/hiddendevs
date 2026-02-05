--!strict
-- ServerScriptService.GamblingSystem
-- i didnt add extra comments since i already comment all my code regardless, its minimal but its enough

-- --- Services ------------------------------------------------------

local Players             = game:GetService("Players")
local ReplicatedStorage   = game:GetService("ReplicatedStorage")
local ServerScriptService = game:GetService("ServerScriptService")
local HttpService         = game:GetService("HttpService")
local MessagingService    = game:GetService("MessagingService")
local Workspace           = game:GetService("Workspace")
local MemoryStoreService  = game:GetService("MemoryStoreService")

-- --- Remotes -------------------------------------------------------

local RemoteEvents        = ReplicatedStorage:WaitForChild("RemoteEvents")
local SpinRemote          = RemoteEvents:FindFirstChild("SpinGacha") :: RemoteEvent?
local LuckyPullChatRemote = RemoteEvents:FindFirstChild("LuckyPullChat") :: RemoteEvent?

-- --- Modules -------------------------------------------------------

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

-- optional rate limit module (if you use it elsewhere)
local RateLimitModule = ServerScriptService:FindFirstChild("RateLimit")
local RateLimit       = RateLimitModule and require(RateLimitModule) or nil

-- --- Dictionary ----------------------------------------------------

local Baddies = Dictionary.Baddies
local Crates  = Dictionary.Crates

-- --- Optional services --------------------------------------------

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

local ClientAssets  = ReplicatedStorage:WaitForChild("ClientAssets")
local BaddiesFolder = ClientAssets:WaitForChild("Baddies")
local Animations    = ClientAssets:WaitForChild("Animations")
local IdleAnim      = Animations:FindFirstChild("Idle")

-- --- Config --------------------------------------------------------

-- if you want "active crates" to stay blocked until the reveal viewport is done,
-- use release mode "delay" and tune the release seconds to match your client flow
local RELEASE_MODE: "immediate" | "delay" = "delay"
local RELEASE_AFTER_SECONDS               = 7

local CONFIG = {
	SpinCooldownSeconds    = 1.25,
	MinSpinCooldownSeconds = 0.45,

	SlotCount              = 50,
	WinnerIndex            = 45,

	LuckyPullMinOrder      = 10,
	LuckyPullTopic         = "MostRecentLuckyPull_v1",
	MaxLuckyPullsPerSec    = 2,

	LuckExponentPerOrder   = 0.35,
	LuckBoostClamp         = { Min = 0.90, Max = 7.50 },

	WeightCacheTTL         = 60,
	ResultPoolSize         = 10,

	WeightMin              = 1e-12,
}

local LATEST_PULL_KEY = "MostRecentLuckyPull_Latest_v1"
local latestPullMap   = MemoryStoreService:GetSortedMap(LATEST_PULL_KEY)

-- --- State ---------------------------------------------------------

local luckySeen: { [string]: boolean } = {}
local cachedEntries: { any }?          = nil
local rarityOrderCache: { [string]: number } = {}

local baseWeightCache: { [string]: number } = {}
local weightCacheTime                       = 0

local resultTablePool: { { any } } = {}

local lastLuckyPullBroadcast = 0

-- --- Result table pooling ------------------------------------------

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

local function getStore(player: Player): any?
	return PlayerDataService.GetData(player)
end

local function safeSetLatestPull(payload: any)
	task.spawn(function()
		pcall(function()
			latestPullMap:SetAsync("latest", payload, 86400)
		end)
	end)
end

local function safeGetLatestPull(): any?
	local ok, value = pcall(function()
		return latestPullMap:GetAsync("latest")
	end)
	return ok and value or nil
end

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

local function applyLuckAndCrateToWeight(baseW: number, order: number, crateType: string, luckMult: number): number
	if baseW <= 0 then return 0 end

	local crateLuck      = 1
	local crateOrderMult = 1

	if Crates then
		if type(Crates.GetCrateLuckMult) == "function" then
			crateLuck = tonumber(Crates.GetCrateLuckMult(crateType)) or 1
		end
		if type(Crates.GetOrderWeightMultiplier) == "function" then
			crateOrderMult = tonumber(Crates.GetOrderWeightMultiplier(crateType, order)) or 1
		end
	end

	local effectiveLuck = math.max(1, clampLuckMult(luckMult) * math.max(1, crateLuck))

	local power    = math.max(0, order - 1) * CONFIG.LuckExponentPerOrder
	local luckBoost = 1
	if power > 0 then
		luckBoost = effectiveLuck ^ power
		luckBoost = clamp(luckBoost, CONFIG.LuckBoostClamp.Min, CONFIG.LuckBoostClamp.Max)
	end

	local w = baseW * crateOrderMult * luckBoost
	return math.max(w, CONFIG.WeightMin)
end

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

local function rollFromPoolWeighted(pool: { any }, crateType: string, luckMult: number, pitySnap: { [string]: number }): any?
	local n = #pool
	if n == 0 then return nil end

	local total   = 0
	local weights = table.create(n)

	for i = 1, n do
		local entry = pool[i]
		local order = safeGetRarityOrder(entry.Rarity)
		local baseW = getBaseWeight(entry.Name)

		local pityMult = RollProgressionService.GetSoftPityMultiplier(order, pitySnap)
		local w        = applyLuckAndCrateToWeight(baseW, order, crateType, luckMult) * pityMult

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

	local weatherLuck = safeGetWeatherLuckMult(weatherId)
	local baseLuck    = clampLuckMult((tonumber(luckMultFromToken) or 1) * weatherLuck)

	-- new player boost happens here (single source of truth)
	local combinedLuck = clampLuckMult(RollProgressionService.ApplyEffectiveLuck(player, baseLuck))

	local forceMinOrder = RollProgressionService.GetHardMinOrder(pitySnap)
	local winnerPool    = pool

	if forceMinOrder > 0 then
		local filtered = filterPoolMinOrder(pool, forceMinOrder)
		if #filtered > 0 then
			winnerPool = filtered
		end
	end

	local winner: any? = nil
	if type(guaranteedName) == "string" and guaranteedName ~= "" then
		for _, e in ipairs(winnerPool) do
			if e.Name == guaranteedName then
				winner = e
				break
			end
		end
	end

	if not winner then
		winner = rollFromPoolWeighted(winnerPool, crateType, combinedLuck, pitySnap) or winnerPool[1]
	end

	results[CONFIG.WinnerIndex] = winner

	for i = 1, CONFIG.SlotCount do
		if i ~= CONFIG.WinnerIndex then
			results[i] = rollFiller(pool) or pool[1]
		end
	end

	return results, CONFIG.WinnerIndex
end

-- --- Data safety helpers ------------------------------------------

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

local function awardBaddie(player: Player, wonEntry: any, crateType: string, weatherId: string?): (string?)
	local baddieUUID = HttpService:GenerateGUID(false)

	-- make sure parents exist (prevents deep index nil in clients)
	ensureTablePath(player, { "Baddies" })
	ensureTablePath(player, { "BaddieInstances" })

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

	local coins = randRange(coinsRange[1], coinsRange[2])
	local gems  = randRange(gemsRange[1], gemsRange[2])
	local luck  = randRange(luckRange[1], luckRange[2])

	local obtainedAt = os.time()

	-- owned count
	do
		local store = getStore(player)
		local cur   = 0
		if store and type(store.Baddies) == "table" then
			cur = tonumber(store.Baddies[wonEntry.Name]) or 0
		end
		PlayerDataService.SetKey(player, { "Baddies", wonEntry.Name }, cur + 1)
	end

	-- instance details
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

	task.spawn(function()
		pcall(function()
			ExistsService.Increment(wonEntry.Name, 1)
		end)
	end)

	-- index tracking
	if IndexService and type(IndexService.MarkDiscovered) == "function" then
		pcall(function()
			IndexService.MarkDiscovered(player, crateType, wonEntry.Name)
		end)
	end

	return baddieUUID
end

-- --- Lucky pull visuals -------------------------------------------

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

local function buildLuckyPullMessage(pullerName: string, wonEntry: any, denomOverride: number?): { RichText: string, PlainText: string }
	local baddieName = wonEntry and (wonEntry.DisplayName or wonEntry.Name) or "???"
	local rarity     = wonEntry and wonEntry.Rarity or "Common"

	local denom = tonumber(denomOverride) or 0
	if denom <= 0 and Dictionary.Baddies and Dictionary.Baddies.GetOddsDenom and wonEntry then
		denom = tonumber(Dictionary.Baddies.GetOddsDenom(wonEntry.Name)) or 0
	end

	local oddsText = denom > 0 and (" (1 in " .. shortInt(denom) .. ")") or ""
	local plain    = string.format("LUCKY PULL! %s pulled %s%s", pullerName, baddieName, oddsText)

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

local function broadcastLuckyPullChat(pullerName: string, wonEntry: any, denomOverride: number?)
	if LuckyPullChatRemote and LuckyPullChatRemote:IsA("RemoteEvent") then
		local msg = buildLuckyPullMessage(pullerName, wonEntry, denomOverride)
		LuckyPullChatRemote:FireAllClients(msg)
	end
end

local function throwLuckyPullToShowcase(wonName: string)
	local thrown = Workspace:FindFirstChild("__THROWN")
	if not thrown then
		thrown      = Instance.new("Folder")
		thrown.Name = "__THROWN"
		thrown.Parent = Workspace
	end

	local marker = thrown:FindFirstChild("MostRecentLuckyPull")
	if not marker or not marker:IsA("BasePart") then return end

	local template = BaddiesFolder:FindFirstChild(wonName)
	if not template or not template:IsA("Model") then return end

	for _, ch in ipairs(thrown:GetChildren()) do
		if ch:IsA("Model") then
			ch:Destroy()
		end
	end

	local clone = template:Clone()
	clone.Name  = wonName
	clone.Parent = thrown

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

	safeSetLatestPull(payload)

	task.spawn(function()
		pcall(function()
			MessagingService:PublishAsync(CONFIG.LuckyPullTopic, payload)
		end)
	end)
end

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

pcall(function()
	MessagingService:SubscribeAsync(CONFIG.LuckyPullTopic, function(msg)
		onLuckyPullMessage(msg and msg.Data, false)
	end)
end)

task.spawn(function()
	local payload = safeGetLatestPull()
	if payload then
		onLuckyPullMessage(payload, true)
	end
end)

-- --- Active slot release ------------------------------------------

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

if not SpinRemote then
	Console:Warn("GamblingSystem", "SpinGacha remote missing")
else
	SpinRemote.OnServerEvent:Connect(function(player: Player, requestUUID: any)
		-- validate request
		if typeof(player) ~= "Instance" or not player:IsA("Player") then return end
		if type(requestUUID) ~= "string" or requestUUID == "" then return end
		if not PlayerDataService.IsReady(player) then return end

		-- consume token (only gate)
		local tokenMeta = GachaTokens.Consume(player, requestUUID)
		if not tokenMeta then
			return
		end

		local didReturnResults = false
		local resultsToReturn: { any }? = nil

		local function cleanup()
			-- return pooled result table if we allocated it
			if resultsToReturn then
				local t = resultsToReturn
				resultsToReturn = nil
				task.delay(5, function()
					returnResultTable(t)
				end)
			end

			-- always release active slot after consume
			releaseActive(player, requestUUID)
		end

		local ok, err = pcall(function()
			-- parse token meta
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

			-- ensure pity tables exist for crate
			RollProgressionService.EnsurePityCrate(player, crateType)

			local store = PlayerDataService.GetData(player)
			if not store then return end

			local pitySnap = RollProgressionService.GetPitySnapshot(store, crateType)

			-- roll
			local results, winnerIndex = generateSpinResults(player, crateType, weatherId, luckMultFromToken, pitySnap, guaranteed)
			resultsToReturn = results

			local won = results[winnerIndex]
			if not won then
				return
			end

			-- award (server side)
			local baddieUUID = awardBaddie(player, won, crateType, weatherId)
			if not baddieUUID then
				return
			end

			-- progression
			local wonOrder = safeGetRarityOrder(won.Rarity)
			RollProgressionService.RecordRoll(player, crateType, wonOrder)

			local newPity = RollProgressionService.ComputeNewPity(pitySnap, wonOrder)
			RollProgressionService.CommitPity(player, crateType, newPity)

			-- lucky pull broadcast
			if wonOrder >= CONFIG.LuckyPullMinOrder then
				local pullId = HttpService:GenerateGUID(false)
				luckySeen[pullId] = true

				throwLuckyPullToShowcase(won.Name)
				broadcastLuckyPullChat(player.Name, won, nil)
				publishLuckyPull(pullId, player.Name, won, nil)
			end

			-- respond to client
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

		-- always cleanup + release slot, even if errors
		cleanup()

		if not ok then
			warn(("[GamblingSystem] Spin handler error (%s): %s"):format(player.Name, tostring(err)))
		end
	end)
end

-- --- Cleanup -------------------------------------------------------

Players.PlayerRemoving:Connect(function(player: Player)
	GachaTokens.Cleanup(player)
end)

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
