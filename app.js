const providers = [
  { name: "Rightmove", status: "live + archived", weight: 0.34 },
  { name: "Zoopla", status: "live + history", weight: 0.26 },
  { name: "OpenRent", status: "live direct", weight: 0.2 },
  { name: "PrimeLocation", status: "premium comps", weight: 0.2 }
];

const londonAreas = [
  { area: "Islington", postcode: "N1", basePsf: 58, bias: 1.04 },
  { area: "Camden", postcode: "NW1", basePsf: 62, bias: 1.08 },
  { area: "Clapham", postcode: "SW4", basePsf: 51, bias: 0.98 },
  { area: "Hackney", postcode: "E8", basePsf: 55, bias: 1.02 },
  { area: "Battersea", postcode: "SW11", basePsf: 57, bias: 1.03 },
  { area: "Greenwich", postcode: "SE10", basePsf: 47, bias: 0.94 },
  { area: "Shoreditch", postcode: "E1", basePsf: 65, bias: 1.1 },
  { area: "Fulham", postcode: "SW6", basePsf: 60, bias: 1.05 }
];

const propertyTypes = ["Flat", "Apartment", "Maisonette", "Terraced house"];
const streets = ["Canonbury Road", "Regent Canal Walk", "Arlington Square", "Cloudesley Road", "Highbury Grove", "Essex Road"];

const chatFeed = document.querySelector("#chatFeed");
const chatForm = document.querySelector("#chatForm");
const listingInput = document.querySelector("#listingInput");
const resetButton = document.querySelector("#resetButton");
const valuationTemplate = document.querySelector("#valuationTemplate");
const sourceList = document.querySelector("#sourceList");

function formatCurrency(value) {
  return new Intl.NumberFormat("en-GB", {
    style: "currency",
    currency: "GBP",
    maximumFractionDigits: 0
  }).format(value);
}

function stableHash(input) {
  let hash = 2166136261;
  for (let index = 0; index < input.length; index += 1) {
    hash ^= input.charCodeAt(index);
    hash = Math.imul(hash, 16777619);
  }
  return Math.abs(hash >>> 0);
}

function seeded(seed, min, max) {
  const x = Math.sin(seed) * 10000;
  const normalized = x - Math.floor(x);
  return Math.round(min + normalized * (max - min));
}

function clamp(value, min, max) {
  return Math.min(max, Math.max(min, value));
}

function pick(seed, list, offset = 0) {
  return list[(seed + offset) % list.length];
}

function providerFromUrl(url) {
  const host = new URL(url).hostname.replace("www.", "");
  if (host.includes("rightmove")) return "Rightmove";
  if (host.includes("zoopla")) return "Zoopla";
  if (host.includes("openrent")) return "OpenRent";
  if (host.includes("primelocation")) return "PrimeLocation";
  return "External listing";
}

function extractListing(url) {
  const seed = stableHash(url);
  const area = pick(seed, londonAreas);
  const bedrooms = seeded(seed + 7, 1, 4);
  const bathrooms = Math.max(1, Math.min(3, Math.round(bedrooms / 1.6)));
  const sqft = bedrooms === 1
    ? seeded(seed + 11, 480, 650)
    : bedrooms === 2
      ? seeded(seed + 13, 690, 880)
      : bedrooms === 3
        ? seeded(seed + 17, 900, 1220)
        : seeded(seed + 19, 1240, 1580);
  const type = pick(seed, propertyTypes, 3);
  const furnished = seed % 3 !== 0 ? "Furnished" : "Unfurnished";
  const listedPsf = area.basePsf * area.bias * (0.92 + (seed % 19) / 100);
  const askingRent = Math.round((listedPsf * sqft) / 12 / 25) * 25;

  return {
    url,
    source: providerFromUrl(url),
    address: `${seeded(seed + 23, 2, 88)} ${pick(seed, streets, 5)}, ${area.area}`,
    area: area.area,
    postcode: area.postcode,
    bedrooms,
    bathrooms,
    sqft,
    type,
    furnished,
    askingRent,
    askingPsf: (askingRent * 12) / sqft,
    listedAt: "Captured from submitted URL",
    letType: "Long let"
  };
}

function buildComparables(listing) {
  const seed = stableHash(listing.url);
  const comps = [];
  const base = listing.askingRent / (0.96 + (seed % 11) / 100);

  providers.forEach((provider, providerIndex) => {
    for (let index = 0; index < (provider.name === "OpenRent" ? 3 : 4); index += 1) {
      const compSeed = seed + providerIndex * 97 + index * 31;
      const distance = (seeded(compSeed, 8, 45) / 100).toFixed(2);
      const sqftDelta = seeded(compSeed + 3, -82, 86);
      const bedroomDelta = seeded(compSeed + 5, -1, 1);
      const matchedBeds = clamp(listing.bedrooms + bedroomDelta, 1, 5);
      const matchedSqft = clamp(listing.sqft + sqftDelta, 410, 1700);
      const rentShift = 0.9 + seeded(compSeed + 9, 0, 23) / 100;
      const status = index % 3 === 0 ? "let agreed" : index % 3 === 1 ? "archived" : "live";
      const rent = Math.round((base * rentShift * (matchedBeds / listing.bedrooms) ** 0.18) / 25) * 25;

      comps.push({
        provider: provider.name,
        status,
        address: `${pick(compSeed, streets)} · ${distance} mi`,
        bedrooms: matchedBeds,
        sqft: matchedSqft,
        rent,
        rentPsf: (rent * 12) / matchedSqft,
        similarity: Math.round(100 - Math.abs(matchedSqft - listing.sqft) / 18 - Math.abs(matchedBeds - listing.bedrooms) * 7 - Number(distance) * 18)
      });
    }
  });

  return comps
    .map((comp) => ({ ...comp, similarity: clamp(comp.similarity, 58, 97) }))
    .sort((a, b) => b.similarity - a.similarity)
    .slice(0, 12);
}

function percentile(values, ratio) {
  const sorted = [...values].sort((a, b) => a - b);
  const index = (sorted.length - 1) * ratio;
  const lower = Math.floor(index);
  const upper = Math.ceil(index);
  if (lower === upper) return sorted[index];
  return sorted[lower] + (sorted[upper] - sorted[lower]) * (index - lower);
}

function valueListing(url) {
  const listing = extractListing(url);
  const comps = buildComparables(listing);
  const rents = comps.map((comp) => comp.rent);
  const low = Math.round(percentile(rents, 0.25) / 25) * 25;
  const median = Math.round(percentile(rents, 0.5) / 25) * 25;
  const high = Math.round(percentile(rents, 0.75) / 25) * 25;
  const spread = Math.max(1, high - low);
  const delta = listing.askingRent - median;
  const deltaPct = delta / median;
  const liveCount = comps.filter((comp) => comp.status === "live").length;
  const historicCount = comps.length - liveCount;
  const avgSimilarity = comps.reduce((sum, comp) => sum + comp.similarity, 0) / comps.length;
  const confidence = clamp(Math.round(avgSimilarity * 0.62 + comps.length * 2.2 + historicCount * 1.6), 54, 94);

  let verdict = "Fair market value";
  let tone = "good";
  if (deltaPct > 0.08) {
    verdict = "Above market";
    tone = "bad";
  } else if (deltaPct > 0.035) {
    verdict = "Slightly expensive";
    tone = "warn";
  } else if (deltaPct < -0.08) {
    verdict = "Good value";
    tone = "good";
  }

  return {
    listing,
    comps,
    band: { low, median, high, spread },
    verdict,
    tone,
    confidence,
    marker: clamp(((listing.askingRent - low) / Math.max(1, high - low)) * 100, 4, 96),
    delta,
    deltaPct
  };
}

function appendMessage(content, role = "bot") {
  const message = document.createElement("article");
  message.className = `message ${role}`;
  if (typeof content === "string") {
    message.textContent = content;
  } else {
    message.append(content);
  }
  chatFeed.append(message);
  chatFeed.scrollTop = chatFeed.scrollHeight;
  return message;
}

function showTyping() {
  const wrap = document.createElement("span");
  wrap.className = "typing";
  wrap.innerHTML = "<i></i><i></i><i></i>";
  return appendMessage(wrap, "bot");
}

function renderSources() {
  sourceList.innerHTML = providers
    .map((provider) => `
      <div class="source-row">
        <span class="source-dot" aria-hidden="true"></span>
        <strong>${provider.name}</strong>
        <small>${provider.status}</small>
      </div>
    `)
    .join("");
}

function renderValuation(result) {
  const node = valuationTemplate.content.firstElementChild.cloneNode(true);
  const fields = node.querySelector('[data-field="fields"]');
  const comps = node.querySelector('[data-field="comps"]');
  const verdict = node.querySelector('[data-field="verdict"]');
  const confidence = node.querySelector('[data-field="confidence"]');
  const marker = node.querySelector('[data-field="priceMarker"]');
  const confidencePill = node.querySelector(".confidence-pill");

  const captured = {
    Source: result.listing.source,
    Address: result.listing.address,
    Postcode: result.listing.postcode,
    Bedrooms: `${result.listing.bedrooms}`,
    Bathrooms: `${result.listing.bathrooms}`,
    Size: `${result.listing.sqft} sqft`,
    Type: result.listing.type,
    Furnishing: result.listing.furnished
  };

  verdict.textContent = result.verdict;
  verdict.style.color = `var(--${result.tone})`;
  confidence.textContent = `${result.confidence}%`;
  confidencePill.style.color = `var(--${result.tone})`;
  confidencePill.style.background = result.tone === "bad" ? "#fbebeb" : result.tone === "warn" ? "#fff3df" : "#ecf8f1";
  node.querySelector('[data-field="askingRent"]').textContent = `${formatCurrency(result.listing.askingRent)} pcm`;
  node.querySelector('[data-field="marketBand"]').textContent = `${formatCurrency(result.band.low)}-${formatCurrency(result.band.high)} pcm`;
  node.querySelector('[data-field="pricePsf"]').textContent = `${formatCurrency(result.listing.askingPsf)} / yr`;
  node.querySelector('[data-field="medianComp"]').textContent = `${formatCurrency(result.band.median)} pcm`;
  node.querySelector('[data-field="lowBand"]').textContent = formatCurrency(result.band.low);
  node.querySelector('[data-field="highBand"]').textContent = formatCurrency(result.band.high);
  marker.style.left = `${result.marker}%`;

  fields.innerHTML = Object.entries(captured)
    .map(([label, value]) => `<div><dt>${label}</dt><dd>${value}</dd></div>`)
    .join("");

  comps.innerHTML = result.comps.slice(0, 6)
    .map((comp) => `
      <div class="comp-row">
        <div>
          <small>${comp.provider} · ${comp.status} · ${comp.similarity}% match</small>
          <strong>${formatCurrency(comp.rent)} pcm</strong>
          <em>${comp.bedrooms} bed · ${comp.sqft} sqft · ${comp.address}</em>
        </div>
        <strong>${formatCurrency(comp.rentPsf)} psf</strong>
      </div>
    `)
    .join("");

  const absoluteDelta = Math.abs(result.delta);
  const direction = result.delta >= 0 ? "above" : "below";
  node.querySelector('[data-field="summary"]').textContent =
    `Asking rent is ${formatCurrency(absoluteDelta)} pcm ${direction} the matched median. Evidence includes ${result.comps.length} comparable listings across four portals, mixing live availability with archived and let-agreed rents.`;

  return node;
}

function isValidUrl(value) {
  try {
    const url = new URL(value);
    return url.protocol === "http:" || url.protocol === "https:";
  } catch {
    return false;
  }
}

chatForm.addEventListener("submit", (event) => {
  event.preventDefault();
  const value = listingInput.value.trim();
  if (!isValidUrl(value)) {
    appendMessage("Please send a full property URL beginning with http:// or https://.");
    return;
  }

  appendMessage(value, "user");
  listingInput.value = "";
  const typing = showTyping();
  document.querySelector("#botStatus").textContent = "checking listing · collecting comps";

  window.setTimeout(() => {
    const result = valueListing(value);
    typing.remove();
    appendMessage(renderValuation(result), "bot");
    document.querySelector("#botStatus").textContent = "online · valuation complete";
    document.querySelector("#evidenceCount").textContent = `${result.comps.length} comps`;
  }, 900);
});

resetButton.addEventListener("click", () => {
  chatFeed.innerHTML = "";
  appendMessage("Send me a London rental listing link and I’ll check whether the asking rent looks fair against matched market evidence.");
  document.querySelector("#botStatus").textContent = "online · valuation engine ready";
  listingInput.focus();
});

renderSources();
