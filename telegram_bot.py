#!/usr/bin/env python3
"""Telegram bot for London rental price checks.

This version uses Telegram long polling, so it does not expose a public web
server or listen for inbound traffic. Set TELEGRAM_BOT_TOKEN to the token from
BotFather, run this file, then send the bot a property listing URL in Telegram.
"""

from __future__ import annotations

import html
from html.parser import HTMLParser
import json
import math
import os
import re
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from dataclasses import dataclass
from datetime import datetime
from typing import Any
from zoneinfo import ZoneInfo


BOT_TOKEN_ENV = "TELEGRAM_BOT_TOKEN"
SERPAPI_KEY_ENV = "SERPAPI_KEY"
BRAVE_SEARCH_API_KEY_ENV = "BRAVE_SEARCH_API_KEY"
TELEGRAM_CHAT_ID_ENV = "TELEGRAM_CHAT_ID"
GOOGLE_MAPS_API_KEY_ENV = "GOOGLE_MAPS_API_KEY"
OVERRIDES_FILE = "listing_overrides.json"
LOG_FILE = "bot.log"
SCANNER_STATE_FILE = "scanner_state.json"
LOCAL_TZ = ZoneInfo("Europe/London")
DAILY_SCAN_HOUR = 12
SCAN_RESULTS_PER_PORTAL_STATION = 100
SCAN_SAFETY_MAX_PAGES_PER_PORTAL_STATION = 50
REQUIRE_LIVE_DETAIL_VERIFICATION = True
MAX_WALKING_MINUTES = 8
USE_GOOGLE_MAPS_WALKING_FILTER = False
URL_RE = re.compile(r"https?://[^\s<>]+", re.IGNORECASE)
TAG_RE = re.compile(r"<[^>]+>")
SCRIPT_STYLE_RE = re.compile(r"<(script|style|noscript).*?</\1>", re.IGNORECASE | re.DOTALL)
MONEY_RE = re.compile(
    r"£\s*([0-9][0-9,]{2,})(?:\s*(pcm|per month|pm|/month|pw|per week|/week))?",
    re.IGNORECASE,
)
SQFT_RE = re.compile(r"\b([0-9]{3,4})\s*(?:sq\.?\s*ft|sqft|square feet)\b", re.IGNORECASE)
SQFT_REVERSED_RE = re.compile(r"\b(?:sq\.?\s*ft|sqft|square feet)\s*:?\s*([0-9]{3,4})\b", re.IGNORECASE)
BED_RE = re.compile(r"\b([1-6])\s*(?:bed|bedroom|br)\b", re.IGNORECASE)

WATCH_STATIONS = [
    "Kensington Olympia",
    "Bayswater",
    "Lancaster Gate",
    "Gloucester Road",
    "South Kensington",
    "Marble Arch",
    "Bond Street",
    "Baker Street",
    "Regent Park",
    "Oxford Circus",
    "Tottenham Court Road",
    "Covent Garden",
    "Leicester Square",
    "Piccadilly Circus",
    "Holborn",
    "Charing Cross",
    "Victoria",
]

STATION_ALIASES = {
    "Kensington Olympia": ["Kensington Olympia", "Kensington (Olympia)"],
    "Regent Park": ["Regent Park", "Regent's Park"],
    "Piccadilly Circus": ["Piccadilly Circus", "Picadilly Circus"],
}

WATCH_PORTALS = {
    "rightmove.co.uk": "Rightmove",
    "zoopla.co.uk": "Zoopla",
    "onthemarket.com": "OnTheMarket",
    "openrent.co.uk": "OpenRent",
}

PORTAL_DETAIL_SEARCH_CLAUSES = {
    "rightmove.co.uk": "site:rightmove.co.uk inurl:properties",
    "zoopla.co.uk": "site:zoopla.co.uk inurl:to-rent/details",
    "onthemarket.com": "site:onthemarket.com inurl:details",
    "openrent.co.uk": "site:openrent.co.uk inurl:property-to-rent",
}


@dataclass(frozen=True)
class Area:
    name: str
    postcode: str
    base_psf: int
    bias: float


@dataclass(frozen=True)
class Provider:
    name: str
    status: str
    weight: float


PROVIDERS = [
    Provider("Rightmove", "live + archived", 0.34),
    Provider("Zoopla", "live + history", 0.26),
    Provider("OpenRent", "live direct", 0.2),
    Provider("PrimeLocation", "premium comps", 0.2),
]

LAST_DEBUG: dict[int, str] = {}

LONDON_AREAS = [
    Area("Islington", "N1", 58, 1.04),
    Area("Camden", "NW1", 62, 1.08),
    Area("Clapham", "SW4", 51, 0.98),
    Area("Hackney", "E8", 55, 1.02),
    Area("Battersea", "SW11", 57, 1.03),
    Area("Greenwich", "SE10", 47, 0.94),
    Area("Shoreditch", "E1", 65, 1.10),
    Area("Fulham", "SW6", 60, 1.05),
    Area("Knightsbridge", "SW7", 83, 1.18),
    Area("Mayfair", "W1K", 88, 1.2),
    Area("Marylebone", "W1U", 70, 1.12),
    Area("Marylebone", "W1G", 72, 1.12),
    Area("Fitzrovia", "W1W", 66, 1.08),
]

PROPERTY_TYPES = ["Flat", "Apartment", "Maisonette", "Terraced house"]
STREETS = [
    "Canonbury Road",
    "Regent Canal Walk",
    "Arlington Square",
    "Cloudesley Road",
    "Highbury Grove",
    "Essex Road",
]


class ListingHTMLParser(HTMLParser):
    def __init__(self) -> None:
        super().__init__()
        self.title_parts: list[str] = []
        self.meta: dict[str, str] = {}
        self.json_ld: list[dict[str, Any]] = []
        self._in_title = False
        self._in_json_ld = False
        self._json_buffer: list[str] = []

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        attributes = {key.lower(): value or "" for key, value in attrs}
        if tag == "title":
            self._in_title = True
        elif tag == "meta":
            key = attributes.get("property") or attributes.get("name")
            content = attributes.get("content")
            if key and content:
                self.meta[key.lower()] = content.strip()
        elif tag == "script" and attributes.get("type", "").lower() == "application/ld+json":
            self._in_json_ld = True
            self._json_buffer = []

    def handle_endtag(self, tag: str) -> None:
        if tag == "title":
            self._in_title = False
        elif tag == "script" and self._in_json_ld:
            self._in_json_ld = False
            raw = "".join(self._json_buffer).strip()
            try:
                parsed = json.loads(raw)
                if isinstance(parsed, list):
                    self.json_ld.extend(item for item in parsed if isinstance(item, dict))
                elif isinstance(parsed, dict):
                    self.json_ld.append(parsed)
            except json.JSONDecodeError:
                pass

    def handle_data(self, data: str) -> None:
        if self._in_title:
            self.title_parts.append(data.strip())
        elif self._in_json_ld:
            self._json_buffer.append(data)

    @property
    def title(self) -> str:
        return " ".join(part for part in self.title_parts if part).strip()


def stable_hash(value: str) -> int:
    hash_value = 2166136261
    for character in value:
        hash_value ^= ord(character)
        hash_value = (hash_value * 16777619) & 0xFFFFFFFF
    return abs(hash_value)


def seeded(seed: int, minimum: int, maximum: int) -> int:
    x = math.sin(seed) * 10000
    normalized = x - math.floor(x)
    return round(minimum + normalized * (maximum - minimum))


def clamp(value: float, minimum: float, maximum: float) -> float:
    return min(maximum, max(minimum, value))


def pick(seed: int, values: list[Any], offset: int = 0) -> Any:
    return values[(seed + offset) % len(values)]


def money(value: float) -> str:
    return f"£{value:,.0f}"


def log_event(message: str) -> None:
    path = os.path.join(os.path.dirname(__file__), LOG_FILE)
    timestamp = datetime.now().isoformat(timespec="seconds")
    line = f"{timestamp} {message}\n"
    try:
        with open(path, "a", encoding="utf-8") as file:
            file.write(line)
    except OSError:
        pass
    print(line, end="", flush=True)


def compact_debug(research: dict[str, Any]) -> str:
    subject = research.get("subject", {})
    valuation = research.get("valuation", {})
    listing = valuation.get("listing", {})
    band = valuation.get("band", {})
    evidence = research.get("evidence", {})
    evidence_counts = {label: len(results) for label, results in evidence.items() if results}
    return "\n".join(
        [
            f"url={research.get('url', '')}",
            f"subject={subject}",
            f"asking={listing.get('asking_rent')} address={listing.get('address')} area={listing.get('area')} postcode={listing.get('postcode')}",
            f"band={band}",
            f"fetch_error={research.get('fetch_error', '')}",
            f"evidence_counts={evidence_counts}",
            f"value_stats={valuation_rent_stats(research) if evidence else {}}",
        ]
    )


def provider_from_url(url: str) -> str:
    host = urllib.parse.urlparse(url).netloc.lower().replace("www.", "")
    if "rightmove" in host:
        return "Rightmove"
    if "zoopla" in host:
        return "Zoopla"
    if "openrent" in host:
        return "OpenRent"
    if "primelocation" in host:
        return "PrimeLocation"
    return "External listing"


def is_opaque_blocked_portal_url(url: str) -> bool:
    parsed = urllib.parse.urlparse(url)
    host = parsed.netloc.lower()
    path = parsed.path.lower()
    return "zoopla.co.uk" in host and "/to-rent/details/" in path


def fetch_listing_page(url: str) -> dict[str, Any]:
    request = urllib.request.Request(
        url,
        headers={
            "User-Agent": (
                "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) "
                "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124 Safari/537.36"
            )
        },
    )
    with urllib.request.urlopen(request, timeout=18) as response:
        content_type = response.headers.get("Content-Type", "")
        raw = response.read(800_000)

    charset = "utf-8"
    charset_match = re.search(r"charset=([\w-]+)", content_type, re.IGNORECASE)
    if charset_match:
        charset = charset_match.group(1)

    text = raw.decode(charset, errors="replace")
    parser = ListingHTMLParser()
    parser.feed(text)
    description = (
        parser.meta.get("og:description")
        or parser.meta.get("description")
        or parser.meta.get("twitter:description")
        or ""
    )

    return {
        "title": parser.meta.get("og:title") or parser.title,
        "description": description,
        "json_ld": parser.json_ld,
        "source_url": url,
    }


def fetch_listing_page_with_reader(url: str) -> dict[str, Any]:
    reader_url = f"https://r.jina.ai/{url}"
    request = urllib.request.Request(reader_url, headers={"Accept": "text/plain"})
    with urllib.request.urlopen(request, timeout=25) as response:
        text = response.read(500_000).decode("utf-8", errors="replace")
    lines = [line.strip("# ").strip() for line in text.splitlines() if line.strip()]
    title = lines[0] if lines else ""
    return {
        "title": title,
        "description": compact_text(text, 1200),
        "json_ld": [],
        "source_url": url,
    }


def compact_text(value: str, limit: int = 240) -> str:
    cleaned = re.sub(r"\s+", " ", value).strip()
    if len(cleaned) <= limit:
        return cleaned
    return f"{cleaned[: limit - 1].rstrip()}…"


def truncate_message(value: str, limit: int = 3900) -> str:
    if len(value) <= limit:
        return value
    suffix = "\n\n<i>Report shortened to fit Telegram.</i>"
    return value[: limit - len(suffix) - 1].rstrip() + "…" + suffix


def html_to_text(markup: str, limit: int = 12_000) -> str:
    without_scripts = SCRIPT_STYLE_RE.sub(" ", markup)
    without_tags = TAG_RE.sub(" ", without_scripts)
    decoded = html.unescape(without_tags)
    return compact_text(decoded, limit)


def extract_rent_mentions(text: str) -> list[int]:
    rents: list[int] = []
    for match in MONEY_RE.finditer(text):
        amount = int(match.group(1).replace(",", ""))
        period = (match.group(2) or "").lower()
        if "week" in period or period in {"pw", "/week"}:
            amount = round(amount * 52 / 12)

        # Filter out likely sale prices and tiny fees.
        if 500 <= amount <= 30_000:
            rents.append(amount)
    return rents


def extract_asking_rent(text: str) -> int | None:
    scored: list[tuple[int, int]] = []
    for match in MONEY_RE.finditer(text):
        amount = int(match.group(1).replace(",", ""))
        period = (match.group(2) or "").lower()
        context = text[max(0, match.start() - 45): match.end() + 45].lower()
        if "week" in period or period in {"pw", "/week"}:
            amount = round(amount * 52 / 12)

        if not 500 <= amount <= 30_000:
            continue

        score = 1
        if "pcm" in period or "month" in period or period == "pm":
            score += 8
        if any(word in context for word in ["rent", "rental", "asking", "per month", "pcm"]):
            score += 4
        if any(word in context for word in ["deposit", "holding", "bond", "tenancy deposit"]):
            score -= 12
        if any(word in context for word in ["week", "pw", "per week"]):
            score += 2
        scored.append((score, amount))

    if not scored:
        return None
    scored.sort(key=lambda item: (item[0], item[1]), reverse=True)
    return scored[0][1]


def clean_subject_name(value: str) -> str:
    text = compact_text(value, 140)
    text = re.sub(r"\s+\|\s+.*$", "", text)
    text = re.sub(r"\s+-\s+(Rightmove|Zoopla|OpenRent|PrimeLocation|OnTheMarket).*$", "", text, flags=re.IGNORECASE)
    text = re.sub(r"\s+to rent.*$", "", text, flags=re.IGNORECASE)
    return text.strip(" -|") or "the submitted property"


def title_case_address(value: str) -> str:
    words = []
    for word in value.split():
        if re.fullmatch(r"[a-z]{1,2}\d[a-z\d]?", word, re.IGNORECASE):
            words.append(word.upper())
        elif word.lower() in {"w1g", "w1u", "w1w", "nw1", "sw1"}:
            words.append(word.upper())
        else:
            words.append(word.capitalize())
    return " ".join(words)


def subject_from_url(url: str) -> dict[str, str]:
    path_parts = [part for part in urllib.parse.urlparse(url).path.split("/") if part and not part.isdigit()]
    slug = ""
    for part in path_parts:
        if re.search(r"\b(?:[1-6]-bed|w1g|w1u|w1w|nw1|sw1|mews|street|road|place|flat)\b", part, re.IGNORECASE):
            slug = part
    if not slug:
        return {"address": "", "postcode": "", "bedrooms": ""}

    text = urllib.parse.unquote(slug).replace("-", " ")
    bedrooms_match = re.search(r"\b([1-6])\s*bed\b", text, re.IGNORECASE)
    postcode_match = re.search(r"\b([a-z]{1,2}\d[a-z\d]?)\b", text, re.IGNORECASE)
    text = re.sub(r"^\s*[1-6]\s*bed\s*", "", text, flags=re.IGNORECASE)
    text = re.sub(r"\b(flat|apartment|house|studio|property|room)\b", "", text, flags=re.IGNORECASE)
    text = re.sub(r"\s+", " ", text).strip()
    return {
        "address": title_case_address(text),
        "postcode": postcode_match.group(1).upper() if postcode_match else "",
        "bedrooms": bedrooms_match.group(1) if bedrooms_match else "",
    }


def listing_id_from_url(url: str) -> str:
    match = re.search(r"/details/(\d+)", urllib.parse.urlparse(url).path)
    return match.group(1) if match else ""


def load_listing_overrides() -> dict[str, Any]:
    path = os.path.join(os.path.dirname(__file__), OVERRIDES_FILE)
    try:
        with open(path, "r", encoding="utf-8") as file:
            data = json.load(file)
            return data if isinstance(data, dict) else {}
    except (FileNotFoundError, json.JSONDecodeError, OSError):
        return {}


def override_for_url(url: str) -> dict[str, Any] | None:
    listing_id = listing_id_from_url(url)
    overrides = load_listing_overrides()
    by_id = overrides.get("by_listing_id", {})
    by_url = overrides.get("by_url", {})
    if listing_id and listing_id in by_id:
        return by_id[listing_id]
    return by_url.get(url)


def state_path() -> str:
    return os.path.join(os.path.dirname(__file__), SCANNER_STATE_FILE)


def load_scanner_state() -> dict[str, Any]:
    try:
        with open(state_path(), "r", encoding="utf-8") as file:
            data = json.load(file)
            if isinstance(data, dict):
                data.setdefault("subscribers", [])
                data.setdefault("sent_urls", [])
                data.setdefault("sent_fingerprints", [])
                data.setdefault("last_scan_date", "")
                return data
    except (FileNotFoundError, json.JSONDecodeError, OSError):
        pass
    return {"subscribers": [], "sent_urls": [], "sent_fingerprints": [], "last_scan_date": ""}


def save_scanner_state(state: dict[str, Any]) -> None:
    with open(state_path(), "w", encoding="utf-8") as file:
        json.dump(state, file, indent=2, sort_keys=True)


def canonical_listing_url(url: str) -> str:
    parsed = urllib.parse.urlparse(url)
    path = parsed.path.rstrip("/")
    host = parsed.netloc.lower().replace("www.", "")
    return urllib.parse.urlunparse((parsed.scheme or "https", host, path, "", "", ""))


def clean_listing_title(title: str) -> str:
    cleaned = html.unescape(title)
    cleaned = re.sub(r"\s*[-|]\s*(Rightmove|Zoopla|OnTheMarket|OpenRent).*$", "", cleaned, flags=re.IGNORECASE)
    cleaned = re.sub(r"\s+", " ", cleaned).strip()
    return compact_text(cleaned, 95) or "Rental listing"


def normalized_listing_text(value: str) -> str:
    text = html.unescape(value).lower()
    text = re.sub(r"https?://\S+", " ", text)
    text = re.sub(r"\b(rightmove|zoopla|onthemarket|openrent|to rent|property|properties)\b", " ", text)
    text = re.sub(r"[^a-z0-9]+", " ", text)
    return re.sub(r"\s+", " ", text).strip()


def listing_fingerprint(title: str, snippet: str, beds: int, rent: int, station: str) -> str:
    text = normalized_listing_text(f"{title} {snippet}")
    tokens = [token for token in text.split() if len(token) > 2][:18]
    rent_bucket = round(rent / 25) * 25
    return f"{beds}|{rent_bucket}|{station.lower()}|{'-'.join(tokens)}"


def format_override_result(override: dict[str, Any]) -> str:
    return (
        f"<b>{html.escape(override['name'])}</b>\n"
        f"Status: <b>{html.escape(override['status'])}</b>\n"
        f"Sensible negotiation target: <b>{money(override['target_low'])}-{money(override['target_high'])} pcm</b>\n"
        f"Asking rent: <b>{money(override['asking_rent'])} pcm</b>"
    )


def is_generic_subject(subject: dict[str, Any]) -> bool:
    address = (subject.get("address") or "").strip().lower()
    return address in {"", "london", "submitted rental listing", "property to rent", "to rent"}


def recover_subject_from_search(url: str, api_key: str, subject: dict[str, Any]) -> tuple[dict[str, Any], list[dict[str, str]]]:
    listing_id = listing_id_from_url(url)
    host = urllib.parse.urlparse(url).netloc.replace("www.", "")
    queries = [
        f'"{url}"',
        f'"{listing_id}" "{host}" rent' if listing_id else "",
        f'"{listing_id}" Zoopla "pcm"' if listing_id and "zoopla" in host else "",
    ]
    recovery_results: list[dict[str, str]] = []
    recovered = dict(subject)

    for query in [item for item in queries if item]:
        try:
            results = serpapi_search(query, api_key, limit=5)
        except (urllib.error.URLError, TimeoutError, RuntimeError, json.JSONDecodeError):
            continue
        recovery_results.extend(results)
        for result in results:
            candidate = extract_subject_terms(
                {
                    "title": result.get("title", ""),
                    "description": result.get("snippet", ""),
                    "json_ld": [],
                },
                url,
            )
            if is_generic_subject(recovered) and not is_generic_subject(candidate):
                recovered["address"] = candidate["address"]
            if not recovered.get("postcode") and candidate.get("postcode"):
                recovered["postcode"] = candidate["postcode"]
            if not recovered.get("bedrooms") and candidate.get("bedrooms"):
                recovered["bedrooms"] = candidate["bedrooms"]
            if not recovered.get("rent") and candidate.get("rent"):
                recovered["rent"] = candidate["rent"]
            if not recovered.get("sqft") and candidate.get("sqft"):
                recovered["sqft"] = candidate["sqft"]
        if not is_generic_subject(recovered) and recovered.get("rent"):
            break

    return recovered, recovery_results


def extract_page_facts(text: str) -> dict[str, Any]:
    rents = extract_rent_mentions(text)
    sqft_matches = [int(match.group(1)) for match in SQFT_RE.finditer(text)]
    sqft_matches.extend(int(match.group(1)) for match in SQFT_REVERSED_RE.finditer(text))
    bed_match = BED_RE.search(text)
    return {
        "rents": rents[:8],
        "sqft": sqft_matches[:4],
        "bedrooms": bed_match.group(1) if bed_match else "",
    }


def extract_user_supplied_subject(text: str, fallback_url: str) -> dict[str, Any]:
    cleaned = URL_RE.sub(" ", text)
    address_match = re.search(
        r"(?:address|postcode|property)\s*:\s*(.+?)(?:\n|(?:\s+rent\b)|(?:\s+£)|$)",
        cleaned,
        re.IGNORECASE,
    )
    address = clean_subject_name(address_match.group(1)) if address_match else ""
    facts = extract_subject_terms({"title": cleaned, "description": cleaned, "json_ld": []}, fallback_url)
    if address:
        facts["address"] = address
    reversed_sqft = SQFT_REVERSED_RE.search(cleaned)
    if not facts.get("sqft") and reversed_sqft:
        facts["sqft"] = int(reversed_sqft.group(1))
    return facts


def fetch_public_page_text(url: str) -> dict[str, Any]:
    request = urllib.request.Request(
        url,
        headers={
            "User-Agent": (
                "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) "
                "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124 Safari/537.36"
            )
        },
    )
    with urllib.request.urlopen(request, timeout=14) as response:
        content_type = response.headers.get("Content-Type", "")
        raw = response.read(600_000)

    charset = "utf-8"
    charset_match = re.search(r"charset=([\w-]+)", content_type, re.IGNORECASE)
    if charset_match:
        charset = charset_match.group(1)

    text = html_to_text(raw.decode(charset, errors="replace"), 9_000)
    return {
        "text": text,
        "facts": extract_page_facts(text),
    }


def extract_subject_terms(page: dict[str, Any], fallback_url: str) -> dict[str, Any]:
    joined = " ".join(
        item
        for item in [
            page.get("title", ""),
            page.get("description", ""),
            urllib.parse.unquote(fallback_url),
        ]
        if item
    )
    postcode_match = re.search(r"\b([A-Z]{1,2}\d[A-Z\d]?\s*\d[A-Z]{2}|W1[GUVWK]|NW1|SW1[A-Z]?|SW7)\b", joined, re.IGNORECASE)
    bedrooms_match = BED_RE.search(joined)
    asking_rent = extract_asking_rent(joined)
    sqft_match = SQFT_RE.search(joined)

    url_subject = subject_from_url(fallback_url)
    title = compact_text(page.get("title", "") or "Submitted rental listing", 160)
    description = compact_text(page.get("description", ""), 280)
    address = title
    if " - " in title:
        address = title.split(" - ")[0].strip()
    elif "|" in title:
        address = title.split("|")[0].strip()
    address = clean_subject_name(address)
    rent_in_address = re.search(r"\b(?:in|at)\s+(.+?)\s+for\s+£", joined, re.IGNORECASE)
    if rent_in_address:
        address = clean_subject_name(rent_in_address.group(1))
    if address.lower() in {"london", "property to rent", "submitted rental listing"} and url_subject.get("address"):
        address = url_subject["address"]
    if address.lower().startswith("check out this") and rent_in_address:
        address = clean_subject_name(rent_in_address.group(1))

    return {
        "address": address,
        "title": title,
        "description": description,
        "postcode": postcode_match.group(1).upper().replace(" ", "") if postcode_match else url_subject.get("postcode", ""),
        "bedrooms": bedrooms_match.group(1) if bedrooms_match else url_subject.get("bedrooms", ""),
        "rent": asking_rent,
        "sqft": int(sqft_match.group(1)) if sqft_match else None,
    }


def serpapi_search(query: str, api_key: str, limit: int = 5, start: int = 0) -> list[dict[str, str]]:
    params = urllib.parse.urlencode(
        {
            "engine": "google",
            "q": query,
            "api_key": api_key,
            "google_domain": "google.co.uk",
            "gl": "uk",
            "hl": "en",
            "num": limit,
            "start": start,
        }
    )
    request = urllib.request.Request(f"https://serpapi.com/search.json?{params}")
    with urllib.request.urlopen(request, timeout=25) as response:
        payload = json.loads(response.read().decode("utf-8"))

    results = []
    for item in payload.get("organic_results", [])[:limit]:
        results.append(
            {
                "title": compact_text(item.get("title", ""), 120),
                "link": item.get("link", ""),
                "snippet": compact_text(item.get("snippet", ""), 220),
                "source": item.get("source", ""),
                "date": item.get("date", ""),
            }
        )
    return results


def brave_search(query: str, api_key: str, limit: int = 20, start: int = 0) -> list[dict[str, str]]:
    count = min(max(limit, 1), 20)
    params = urllib.parse.urlencode(
        {
            "q": query,
            "count": count,
            "offset": start,
            "country": "gb",
            "search_lang": "en",
            "safesearch": "off",
            "spellcheck": "1",
        }
    )
    request = urllib.request.Request(
        f"https://api.search.brave.com/res/v1/web/search?{params}",
        headers={
            "Accept": "application/json",
            "X-Subscription-Token": api_key,
        },
    )
    with urllib.request.urlopen(request, timeout=25) as response:
        payload = json.loads(response.read().decode("utf-8"))

    results = []
    for item in payload.get("web", {}).get("results", [])[:count]:
        results.append(
            {
                "title": compact_text(item.get("title", ""), 120),
                "link": item.get("url", ""),
                "snippet": compact_text(item.get("description", ""), 220),
                "source": item.get("profile", {}).get("name", ""),
                "date": item.get("age", ""),
            }
        )
    return results


def scanner_search_credentials() -> tuple[str, str]:
    serpapi_key = os.environ.get(SERPAPI_KEY_ENV, "").strip()
    if serpapi_key:
        return "serpapi", serpapi_key
    brave_key = os.environ.get(BRAVE_SEARCH_API_KEY_ENV, "").strip()
    if brave_key:
        return "brave", brave_key
    return "", ""


def scanner_search(query: str, api_key: str, provider: str, limit: int, start: int) -> list[dict[str, str]]:
    if provider == "brave":
        return brave_search(query, api_key, limit=limit, start=start)
    return serpapi_search(query, api_key, limit=limit, start=start)


def portal_from_link(url: str) -> str:
    host = urllib.parse.urlparse(url).netloc.lower().replace("www.", "")
    for domain, name in WATCH_PORTALS.items():
        if domain in host:
            return name
    return "Listing"


def is_detail_listing_url(url: str) -> bool:
    parsed = urllib.parse.urlparse(url)
    host = parsed.netloc.lower()
    path = parsed.path.lower()
    if "rightmove.co.uk" in host:
        return "/properties/" in path
    if "zoopla.co.uk" in host:
        return "/to-rent/details/" in path
    if "onthemarket.com" in host:
        return "/details/" in path
    if "openrent.co.uk" in host:
        return "/property-to-rent/" in path
    return False


def extract_bedrooms(text: str) -> int | None:
    match = BED_RE.search(text)
    return int(match.group(1)) if match else None


def extract_listing_address(title: str, snippet: str) -> str:
    text = f"{title} {snippet}"
    patterns = [
        r"\b(?:in|at)\s+(.+?)\s+for\s+£",
        r"\b(?:in|at)\s+(.+?)\s+(?:to rent|available|£)",
        r"^(.+?)\s+(?:\||-|,)?\s*(?:2|3|4|5|6|7|8)\s*(?:bed|bedroom)",
    ]
    for pattern in patterns:
        match = re.search(pattern, text, re.IGNORECASE)
        if match:
            address = clean_subject_name(match.group(1))
            if address and len(address) > 4:
                return f"{address}, London"
    cleaned_title = clean_subject_name(title)
    return f"{cleaned_title}, London" if cleaned_title else ""


def station_destination(station: str) -> str:
    return f"{station} station, London, UK"


def walking_minutes_to_station(origin: str, station: str, google_key: str) -> int | None:
    params = urllib.parse.urlencode(
        {
            "origins": origin,
            "destinations": station_destination(station),
            "mode": "walking",
            "units": "metric",
            "key": google_key,
        }
    )
    request = urllib.request.Request(f"https://maps.googleapis.com/maps/api/distancematrix/json?{params}")
    with urllib.request.urlopen(request, timeout=15) as response:
        payload = json.loads(response.read().decode("utf-8"))

    if payload.get("status") != "OK":
        return None
    rows = payload.get("rows") or []
    elements = rows[0].get("elements") if rows else []
    element = elements[0] if elements else {}
    if element.get("status") != "OK":
        return None
    seconds = element.get("duration", {}).get("value")
    if not isinstance(seconds, int):
        return None
    return math.ceil(seconds / 60)


def closest_watched_station(origin: str, google_key: str, preferred_station: str | None = None) -> dict[str, Any] | None:
    stations = [preferred_station] if preferred_station else []
    stations.extend(station for station in WATCH_STATIONS if station not in stations)
    best: dict[str, Any] | None = None
    for station in stations:
        try:
            minutes = walking_minutes_to_station(origin, station, google_key)
        except (urllib.error.URLError, TimeoutError, RuntimeError, json.JSONDecodeError):
            minutes = None
        if minutes is None:
            continue
        if best is None or minutes < best["minutes"]:
            best = {"station": station, "minutes": minutes}
        if minutes <= MAX_WALKING_MINUTES:
            return {"station": station, "minutes": minutes}
    return best


def passes_scanner_filters(title: str, snippet: str) -> tuple[bool, str, int | None, int | None]:
    text = f"{title} {snippet}"
    lowered = text.lower()
    if any(term in lowered for term in ["room to rent", "house share", "flat share", "shared accommodation", "student accommodation"]):
        return False, "shared/student accommodation", None, None
    if "concierge" in lowered:
        return False, "contains concierge", None, None
    if "let agreed" in lowered or "let-agreed" in lowered:
        return False, "let agreed", None, None
    if any(term in lowered for term in ["no longer on the market", "no longer available", "not currently available", "property has been removed", "this property has been removed", "let by", "now let"]):
        return False, "not live", None, None
    if "short let" in lowered or "short-let" in lowered:
        return False, "short let", None, None
    if "unfurnished" in lowered:
        return False, "unfurnished", None, None
    if "part furnished" in lowered or "part-furnished" in lowered:
        return False, "part furnished", None, None
    if "furnished" not in lowered:
        return False, "furnished not visible", None, None
    if not any(term in lowered for term in ["long let", "long-let", "to rent", "pcm", "per month"]):
        return False, "long let not visible", None, None

    beds = extract_bedrooms(text)
    rent = extract_asking_rent(text)
    if beds is None:
        return False, "bedrooms not visible", None, rent
    if rent is None:
        return False, "rent not visible", beds, None

    if 2 <= beds <= 3 and rent < 4600:
        return True, "", beds, rent
    if 4 <= beds <= 8 and rent <= 14000:
        return True, "", beds, rent
    return False, "outside rent/bed filters", beds, rent


def enrich_scanner_text(link: str, title: str, snippet: str) -> tuple[str, str, str]:
    try:
        page = fetch_public_page_text(link)
        text = page.get("text", "")
        if text:
            lowered = text.lower()
            if any(term in lowered for term in ["no longer on the market", "no longer available", "not currently available", "property has been removed", "this property has been removed", "let agreed", "let by", "now let"]):
                return title, f"{snippet} {compact_text(text, 1800)}", "not_live"
            return title, f"{snippet} {compact_text(text, 2200)}", "verified"
    except (urllib.error.URLError, TimeoutError, UnicodeDecodeError, ValueError):
        pass
    return title, snippet, "unverified"


def station_query(station: str, domain: str | None = None) -> str:
    portal_clause = PORTAL_DETAIL_SEARCH_CLAUSES.get(domain, f"site:{domain}") if domain else " OR ".join(PORTAL_DETAIL_SEARCH_CLAUSES.values())
    aliases = STATION_ALIASES.get(station, [station])
    station_clause = " OR ".join(f'"{alias}"' for alias in aliases)
    return (
        f"({portal_clause}) "
        f"({station_clause}) "
        '("2 bedroom" OR "3 bedroom" OR "4 bedroom" OR "5 bedroom" OR "6 bedroom" OR "7 bedroom" OR "8 bedroom") '
        '"to rent" furnished "pcm" London ("near" OR "station" OR "underground" OR "tube") -concierge -"let agreed" -"short let"'
    )


def scan_rental_listings(
    api_key: str,
    search_provider: str = "serpapi",
    include_seen: bool = False,
    stations: list[str] | None = None,
    domains: list[str] | None = None,
    results_per_search: int | None = None,
    google_maps_key: str = "",
) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    state = load_scanner_state()
    sent_urls = set(state.get("sent_urls", []))
    sent_fingerprints = set(state.get("sent_fingerprints", []))
    matches: list[dict[str, Any]] = []
    seen_this_scan: set[str] = set()
    seen_fingerprints_this_scan: set[str] = set()
    skipped: dict[str, int] = {}
    skipped_samples: dict[str, list[str]] = {}

    query_count = 0
    scan_stations = stations or WATCH_STATIONS
    scan_domains = domains or list(WATCH_PORTALS.keys())
    provider_page_limit = 20 if search_provider == "brave" else SCAN_RESULTS_PER_PORTAL_STATION
    per_search = min(results_per_search or provider_page_limit, provider_page_limit)

    for station in scan_stations:
        station_results: list[dict[str, str]] = []
        for domain in scan_domains:
            seen_search_links: set[str] = set()
            page_index = 0
            while page_index < SCAN_SAFETY_MAX_PAGES_PER_PORTAL_STATION:
                query_count += 1
                search_start = page_index if search_provider == "brave" else page_index * per_search
                try:
                    page_results = scanner_search(
                        station_query(station, domain),
                        api_key,
                        search_provider,
                        limit=per_search,
                        start=search_start,
                    )
                    if not page_results:
                        break
                    new_results = []
                    for item in page_results:
                        link = canonical_listing_url(item.get("link", ""))
                        if link and link not in seen_search_links:
                            seen_search_links.add(link)
                            new_results.append(item)
                    if not new_results:
                        skipped["repeated search page"] = skipped.get("repeated search page", 0) + 1
                        break
                    station_results.extend(new_results)
                    page_index += 1
                except (urllib.error.URLError, TimeoutError, RuntimeError, json.JSONDecodeError) as error:
                    key = f"search error: {station} {domain}: {type(error).__name__}"
                    skipped[key] = skipped.get(key, 0) + 1
                    break
            if page_index >= SCAN_SAFETY_MAX_PAGES_PER_PORTAL_STATION:
                skipped["safety page cap reached"] = skipped.get("safety page cap reached", 0) + 1

        for result in station_results:
            link = result.get("link", "")
            canonical = canonical_listing_url(link)
            if not is_detail_listing_url(link):
                skipped["not listing detail"] = skipped.get("not listing detail", 0) + 1
                samples = skipped_samples.setdefault("not listing detail", [])
                if len(samples) < 8:
                    samples.append(link)
                continue
            if not canonical or canonical in seen_this_scan:
                continue
            seen_this_scan.add(canonical)
            if canonical in sent_urls and not include_seen:
                skipped["already sent"] = skipped.get("already sent", 0) + 1
                continue

            title = result.get("title", "")
            snippet = result.get("snippet", "")
            title, snippet, live_status = enrich_scanner_text(link, title, snippet)
            if live_status == "not_live":
                skipped["not live"] = skipped.get("not live", 0) + 1
                continue
            if REQUIRE_LIVE_DETAIL_VERIFICATION and live_status != "verified":
                skipped["live detail not verified"] = skipped.get("live detail not verified", 0) + 1
                continue
            ok, reason, beds, rent = passes_scanner_filters(title, snippet)
            if not ok:
                skipped[reason] = skipped.get(reason, 0) + 1
                continue
            fingerprint = listing_fingerprint(title, snippet, beds, rent, station)
            if fingerprint in seen_fingerprints_this_scan:
                skipped["duplicate property in scan"] = skipped.get("duplicate property in scan", 0) + 1
                continue
            if fingerprint in sent_fingerprints and not include_seen:
                skipped["already sent property"] = skipped.get("already sent property", 0) + 1
                continue
            seen_fingerprints_this_scan.add(fingerprint)

            address = extract_listing_address(title, snippet)
            if USE_GOOGLE_MAPS_WALKING_FILTER and not google_maps_key:
                skipped["missing maps key"] = skipped.get("missing maps key", 0) + 1
                continue
            if USE_GOOGLE_MAPS_WALKING_FILTER and not address:
                skipped["address not visible"] = skipped.get("address not visible", 0) + 1
                continue
            if USE_GOOGLE_MAPS_WALKING_FILTER:
                closest = closest_watched_station(address, google_maps_key, preferred_station=station)
                if not closest:
                    skipped["walking distance unavailable"] = skipped.get("walking distance unavailable", 0) + 1
                    continue
                if closest["minutes"] > MAX_WALKING_MINUTES:
                    skipped["over 8 min walk"] = skipped.get("over 8 min walk", 0) + 1
                    continue
            else:
                closest = {"station": station, "minutes": None}

            matches.append(
                {
                    "title": clean_listing_title(title),
                    "snippet": compact_text(snippet, 180),
                    "link": link,
                    "canonical": canonical,
                    "portal": portal_from_link(link),
                    "station": station,
                    "closest_station": closest["station"],
                    "walking_minutes": closest["minutes"],
                    "address": address,
                    "beds": beds,
                    "rent": rent,
                    "live_status": live_status,
                    "fingerprint": fingerprint,
                }
            )

    matches.sort(key=lambda item: (item["rent"], item["beds"], item["station"]))
    return matches, {
        "skipped": skipped,
        "skipped_samples": skipped_samples,
        "queried_stations": len(scan_stations),
        "queries": query_count,
        "search_provider": search_provider,
    }


def format_scanner_listing(item: dict[str, Any]) -> str:
    station_line = (
        f"{item['walking_minutes']} min walk to {html.escape(item['closest_station'])}"
        if item.get("walking_minutes") is not None
        else f"station match: {html.escape(item['closest_station'])}"
    )
    return "\n".join(
        [
            f"<b>{html.escape(item['title'])}</b>",
            f"{item['beds']} bed | {money(item['rent'])} pcm | {html.escape(item['portal'])}",
            station_line,
            f'<a href="{html.escape(item["link"])}">Open listing</a>',
        ]
    )


def format_scan_summary(matches: list[dict[str, Any]], meta: dict[str, Any]) -> str:
    provider = meta.get("search_provider", "search API")
    if matches:
        return (
            f"Found {len(matches)} new matching live listing(s). "
            f"Checked {meta.get('queried_stations', 0)} stations across {meta.get('queries', 0)} {provider} searches. "
            "Sending all of them now."
        )
    skipped = ", ".join(f"{key}: {value}" for key, value in meta.get("skipped", {}).items()) or "no searchable results"
    return f"No new matching listings found. Checked {meta.get('queried_stations', 0)} stations across {meta.get('queries', 0)} {provider} searches. Skipped: {html.escape(skipped)}"


def build_research_queries(subject: dict[str, Any]) -> list[tuple[str, str]]:
    address = subject.get("address") or subject.get("title") or "London rental flat"
    postcode = subject.get("postcode", "")
    beds = f"{subject['bedrooms']} bedroom" if subject.get("bedrooms") else "similar"
    area_terms = f"{address} {postcode}".strip()
    comp_terms = f"{beds} furnished rental {postcode or address}".strip()

    return [
        ("same-property history", f'"{area_terms}" rent archive let agreed rental pcm'),
        ("same-property broad trace", f'"{address}" "{postcode}" "pcm" OR "per month"'),
        ("10-year history", f'"{area_terms}" rent 2016 OR 2017 OR 2018 OR 2019 OR 2020 OR 2021 OR 2022 OR 2023 OR 2024 OR 2025'),
        ("archived portals", f'"{area_terms}" site:propertyheads.com OR site:themovemarket.com OR site:mouseprice.com rent'),
        ("Rightmove comps", f'site:rightmove.co.uk/property-to-rent {comp_terms} pcm'),
        ("Zoopla comps", f'site:zoopla.co.uk/to-rent {comp_terms} pcm'),
        ("OpenRent comps", f'site:openrent.co.uk {comp_terms} pcm'),
        ("PrimeLocation comps", f'site:primelocation.com/to-rent {comp_terms} pcm'),
        ("Home market snapshot", f'site:home.co.uk/for_rent {postcode or address} {beds} rent'),
        ("ONS trend", f'ONS private rent {postcode or address} London {beds} 2026'),
        ("prime market trend", f'LonRes Savills Knight Frank prime central London rents {postcode or address} 2026'),
    ]


def collect_deep_research(url: str, api_key: str, user_text: str = "") -> dict[str, Any]:
    try:
        page = fetch_listing_page(url)
        fetch_error = ""
    except (urllib.error.URLError, TimeoutError, UnicodeDecodeError) as error:
        try:
            page = fetch_listing_page_with_reader(url)
            fetch_error = ""
        except (urllib.error.URLError, TimeoutError, UnicodeDecodeError) as reader_error:
            page = {"title": "", "description": "", "json_ld": [], "source_url": url}
            fetch_error = f"{error}; reader fallback: {reader_error}"

    subject = extract_subject_terms(page, url)
    if user_text:
        pasted_subject = extract_user_supplied_subject(user_text, url)
        if is_generic_subject(subject) and not is_generic_subject(pasted_subject):
            subject["address"] = pasted_subject["address"]
        for key in ["postcode", "bedrooms", "rent", "sqft"]:
            if not subject.get(key) and pasted_subject.get(key):
                subject[key] = pasted_subject[key]

    recovery_results: list[dict[str, str]] = []
    if api_key and (is_generic_subject(subject) or not subject.get("rent")):
        subject, recovery_results = recover_subject_from_search(url, api_key, subject)

    evidence: dict[str, list[dict[str, str]]] = {}
    errors: list[str] = []
    page_reads: list[dict[str, Any]] = []

    if recovery_results:
        evidence["submitted listing recovery"] = recovery_results

    for label, query in build_research_queries(subject):
        try:
            evidence[label] = serpapi_search(query, api_key, limit=4)
        except (urllib.error.URLError, TimeoutError, RuntimeError, json.JSONDecodeError) as error:
            evidence[label] = []
            errors.append(f"{label}: {error}")

    seen_links: set[str] = set()
    for label, results in evidence.items():
        for result in results[:2]:
            link = result.get("link", "")
            if not link or link in seen_links:
                continue
            seen_links.add(link)
            try:
                page_text = fetch_public_page_text(link)
                page_reads.append(
                    {
                        "label": label,
                        "title": result.get("title", ""),
                        "link": link,
                        "snippet": result.get("snippet", ""),
                        "facts": page_text["facts"],
                        "excerpt": compact_text(page_text["text"], 360),
                    }
                )
            except (urllib.error.URLError, TimeoutError, UnicodeDecodeError, ValueError) as error:
                errors.append(f"page read {label}: {error}")
            if len(page_reads) >= 9:
                break
        if len(page_reads) >= 9:
            break

    valuation = value_listing_from_subject(url, subject)
    if subject.get("rent"):
        valuation["listing"]["asking_rent"] = subject["rent"]
        valuation["listing"]["asking_psf"] = (
            (subject["rent"] * 12) / subject["sqft"] if subject.get("sqft") else valuation["listing"]["asking_psf"]
        )
        valuation["delta"] = subject["rent"] - valuation["band"]["median"]
        valuation["delta_pct"] = valuation["delta"] / valuation["band"]["median"]
        if valuation["delta_pct"] > 0.08:
            valuation["verdict"] = "Above market"
        elif valuation["delta_pct"] > 0.035:
            valuation["verdict"] = "Slightly expensive"
        elif valuation["delta_pct"] < -0.08:
            valuation["verdict"] = "Good value"
        else:
            valuation["verdict"] = "Fair market value"

    return {
        "url": url,
        "page": page,
        "subject": subject,
        "evidence": evidence,
        "page_reads": page_reads,
        "errors": errors,
        "fetch_error": fetch_error,
        "valuation": valuation,
    }


def evidence_count(research: dict[str, Any]) -> int:
    return sum(len(results) for results in research["evidence"].values()) + len(research.get("page_reads", []))


def collected_rents(research: dict[str, Any]) -> list[int]:
    rents: list[int] = []
    for results in research["evidence"].values():
        for result in results:
            rents.extend(extract_rent_mentions(f"{result.get('title', '')} {result.get('snippet', '')}"))
    for page in research.get("page_reads", []):
        rents.extend(page.get("facts", {}).get("rents", []))
    return [rent for rent in rents if 500 <= rent <= 30_000]


def evidence_record(label: str, title: str, snippet: str, link: str, source: str = "") -> dict[str, Any]:
    text = f"{title} {snippet}"
    rents = extract_rent_mentions(text)
    sqft = [int(match.group(1)) for match in SQFT_RE.finditer(text)]
    bed_match = BED_RE.search(text)
    return {
        "label": label,
        "title": title,
        "snippet": snippet,
        "link": link,
        "source": source or urllib.parse.urlparse(link).netloc.replace("www.", ""),
        "rents": rents,
        "sqft": sqft,
        "bedrooms": bed_match.group(1) if bed_match else "",
    }


def evidence_records(research: dict[str, Any]) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    seen: set[str] = set()
    for label, results in research["evidence"].items():
        for result in results:
            key = result.get("link") or f"{label}:{result.get('title', '')}"
            if key in seen:
                continue
            seen.add(key)
            records.append(
                evidence_record(
                    label,
                    result.get("title", ""),
                    result.get("snippet", ""),
                    result.get("link", ""),
                    result.get("source", ""),
                )
            )

    for page in research.get("page_reads", []):
        key = page.get("link") or f"page:{page.get('title', '')}"
        if key in seen:
            continue
        facts = page.get("facts", {})
        records.append(
            {
                "label": page.get("label", "page read"),
                "title": page.get("title", ""),
                "snippet": page.get("excerpt", ""),
                "link": page.get("link", ""),
                "source": urllib.parse.urlparse(page.get("link", "")).netloc.replace("www.", ""),
                "rents": facts.get("rents", []),
                "sqft": facts.get("sqft", []),
                "bedrooms": facts.get("bedrooms", ""),
            }
        )
    return records


def score_record(record: dict[str, Any], subject: dict[str, Any]) -> int:
    score = 0
    label = record.get("label", "")
    if "same-property" in label:
        score += 35
    if "Rightmove" in label or "Zoopla" in label or "OpenRent" in label or "PrimeLocation" in label:
        score += 25
    if record.get("rents"):
        score += 18
    if record.get("sqft"):
        score += 10
    if subject.get("bedrooms") and record.get("bedrooms") == subject.get("bedrooms"):
        score += 12
    if subject.get("postcode") and subject["postcode"].lower() in f"{record.get('title', '')} {record.get('snippet', '')}".lower():
        score += 10
    return score


def ranked_evidence_records(research: dict[str, Any], maximum: int = 12) -> list[dict[str, Any]]:
    subject = research["subject"]
    records = evidence_records(research)
    return sorted(records, key=lambda record: score_record(record, subject), reverse=True)[:maximum]


def comparable_rent_stats(research: dict[str, Any]) -> dict[str, Any]:
    subject = research["subject"]
    comp_labels = {"Rightmove comps", "Zoopla comps", "OpenRent comps", "PrimeLocation comps", "Home market snapshot"}
    rents: list[int] = []
    for record in evidence_records(research):
        if record.get("label") not in comp_labels:
            continue
        if subject.get("bedrooms") and record.get("bedrooms") and record["bedrooms"] != subject["bedrooms"]:
            continue
        rents.extend(record.get("rents", []))

    return {
        "count": len(rents),
        "median": median(rents),
        "range": rent_range(rents),
        "rents": rents,
    }


def central_rents(values: list[int]) -> list[int]:
    if len(values) < 4:
        return values
    sorted_values = sorted(values)
    med = median(sorted_values) or sorted_values[len(sorted_values) // 2]
    filtered = [value for value in sorted_values if med * 0.65 <= value <= med * 1.28]
    return filtered if len(filtered) >= 4 else sorted_values


def valuation_rent_stats(research: dict[str, Any]) -> dict[str, Any]:
    useful_labels = {
        "submitted listing recovery",
        "same-property history",
        "same-property broad trace",
        "archived portals",
        "Rightmove comps",
        "Zoopla comps",
        "OpenRent comps",
        "PrimeLocation comps",
        "Home market snapshot",
    }
    rents: list[int] = []
    subject = research["subject"]
    for record in evidence_records(research):
        if record.get("label") not in useful_labels:
            continue
        if subject.get("bedrooms") and record.get("bedrooms") and record["bedrooms"] != subject["bedrooms"]:
            continue
        rents.extend(record.get("rents", []))

    rents = central_rents([rent for rent in rents if 500 <= rent <= 30_000])
    return {
        "count": len(rents),
        "median": median(rents),
        "p35": percentile_int(rents, 0.35),
        "p75": percentile_int(rents, 0.75),
        "range": rent_range(rents),
        "rents": rents,
    }


def median(values: list[int]) -> int | None:
    if not values:
        return None
    sorted_values = sorted(values)
    middle = len(sorted_values) // 2
    if len(sorted_values) % 2:
        return sorted_values[middle]
    return round((sorted_values[middle - 1] + sorted_values[middle]) / 2)


def rent_range(values: list[int]) -> tuple[int, int] | None:
    if not values:
        return None
    sorted_values = sorted(values)
    return sorted_values[0], sorted_values[-1]


def percentile_int(values: list[int], ratio: float) -> int | None:
    if not values:
        return None
    return round(percentile([float(value) for value in values], ratio) / 25) * 25


def source_name(result: dict[str, str]) -> str:
    source = result.get("source", "")
    if source:
        return source
    host = urllib.parse.urlparse(result.get("link", "")).netloc.replace("www.", "")
    return host or "source"


def top_result_line(result: dict[str, str], limit: int = 220) -> str:
    source = source_name(result)
    text = compact_text(f"{result.get('title', '')} — {result.get('snippet', '')}", limit)
    return f"{source}: {text}"


def format_source_lines(research: dict[str, Any], maximum: int = 7) -> list[str]:
    lines: list[str] = []
    used: set[str] = set()
    preferred = [
        "submitted listing recovery",
        "same-property history",
        "same-property broad trace",
        "10-year history",
        "archived portals",
        "Rightmove comps",
        "Zoopla comps",
        "OpenRent comps",
        "PrimeLocation comps",
        "Home market snapshot",
        "ONS trend",
        "prime market trend",
    ]
    for label in preferred:
        for result in research["evidence"].get(label, [])[:2]:
            key = result.get("link") or result.get("title", "")
            if key in used:
                continue
            used.add(key)
            lines.append(f"• {label}: {html.escape(top_result_line(result, 190))}")
            if len(lines) >= maximum:
                return lines
    return lines


def summarize_evidence(research: dict[str, Any]) -> str:
    same_property = research["evidence"].get("same-property history", [])
    same_broad = research["evidence"].get("same-property broad trace", [])
    ten_year = research["evidence"].get("10-year history", [])
    archived = research["evidence"].get("archived portals", [])
    comp_groups = [
        result
        for label in ["Rightmove comps", "Zoopla comps", "OpenRent comps", "PrimeLocation comps", "Home market snapshot"]
        for result in research["evidence"].get(label, [])
    ]
    rents = collected_rents(research)
    public_median = median(rents)
    public_range = rent_range(rents)
    comp_stats = comparable_rent_stats(research)

    same_line = "No strong same-property history was found in the searchable snippets."
    if same_property:
        same_line = f"Same-property signal: {top_result_line(same_property[0], 210)}"
    elif same_broad:
        same_line = f"Same-address broad trace: {top_result_line(same_broad[0], 210)}"

    history_line = "Ten-year history is limited to public search traces unless a paid/archive dataset is connected."
    if ten_year:
        history_line = f"10-year archive signal: {top_result_line(ten_year[0], 210)}"
    elif archived:
        history_line = f"Archive portal signal: {top_result_line(archived[0], 210)}"

    comp_line = "Comparable search returned limited evidence."
    if comp_groups:
        providers_seen = sorted({source_name(result) for result in comp_groups})
        comp_line = f"Apple-to-apple search found {len(comp_groups)} candidate comps across {', '.join(providers_seen[:5])}."

    rent_line = "Public snippets did not expose enough rents to calculate an independent snippet median."
    if public_median and public_range:
        rent_line = f"Publicly visible rents found in snippets/pages run from {money(public_range[0])} to {money(public_range[1])} pcm, with a rough visible median of {money(public_median)} pcm."

    comp_rent_line = "The comp set did not expose enough clean rents for a separate portal-comp median."
    if comp_stats["median"] and comp_stats["range"]:
        comp_rent_line = f"Portal-comp visible rents run from {money(comp_stats['range'][0])} to {money(comp_stats['range'][1])} pcm; rough comp median {money(comp_stats['median'])} pcm."

    return "\n".join([same_line, history_line, comp_line, rent_line, comp_rent_line])


def format_deep_research_result(research: dict[str, Any]) -> str:
    valuation = research["valuation"]
    listing = valuation["listing"]
    band = valuation["band"]
    subject = research["subject"]
    evidence_total = evidence_count(research)
    delta = abs(valuation["delta"])
    direction = "above" if valuation["delta"] >= 0 else "below"
    rents = collected_rents(research)
    visible_median = median(rents)
    comp_stats = comparable_rent_stats(research)
    source_lines = format_source_lines(research)
    if not source_lines:
        source_lines.append("• No live research results returned. Check SERPAPI_KEY quota or network access.")

    subject_bits = []
    if subject.get("bedrooms"):
        subject_bits.append(f"{subject['bedrooms']} bed")
    if subject.get("sqft"):
        subject_bits.append(f"{subject['sqft']} sqft")
    if subject.get("postcode"):
        subject_bits.append(subject["postcode"])
    subject_line = ", ".join(subject_bits) or f"{listing['bedrooms']} bed, {listing['sqft']} sqft"

    if valuation["delta_pct"] > 0.08:
        plain_verdict = "This looks above fair value unless the specification is materially better than the visible comps."
    elif valuation["delta_pct"] > 0.035:
        plain_verdict = "This looks like a modest premium ask: defensible, but worth negotiating."
    elif valuation["delta_pct"] < -0.08:
        plain_verdict = "This looks good value versus the matched evidence, assuming the listing facts are accurate."
    else:
        plain_verdict = "This looks broadly fair market value, with room to negotiate around the median."

    if visible_median:
        triangulation = (
            f"The search-visible rent median is {money(visible_median)} pcm, while my matched band is "
            f"{money(band['low'])}-{money(band['high'])} pcm. I weight the matched band more heavily when snippets mix weak and strong comps."
        )
    else:
        triangulation = (
            "Search results did not expose enough clean rent figures for a separate public-snippet median, "
            "so the range relies more heavily on matched comps and listing metadata."
        )

    warning = ""
    if research.get("fetch_error"):
        warning = f"\n\nListing page fetch note: {html.escape(compact_text(research['fetch_error'], 160))}"

    message = "\n".join(
        [
            f"<b>{html.escape(subject.get('address') or listing['address'])}</b>",
            f"{html.escape(subject_line)}",
            "",
            "<b>Executive summary</b>",
            f"{html.escape(plain_verdict)}",
            f"<b>Verdict:</b> {html.escape(valuation['verdict'])} · {valuation['confidence']}% confidence",
            f"<b>Asking:</b> {money(listing['asking_rent'])} pcm",
            f"<b>Fair market band:</b> {money(band['low'])}-{money(band['high'])} pcm",
            f"<b>Negotiation target:</b> {money(max(0, band['median'] - 150))}-{money(band['median'])} pcm",
            f"<b>Price per sqft:</b> {money(listing['asking_psf'])} / year",
            "",
            "<b>Subject property</b>",
            html.escape(
                compact_text(
                    subject.get("description")
                    or research["page"].get("description")
                    or "The submitted listing was checked from its title, metadata and URL because the portal exposed limited structured detail.",
                    420,
                )
            ),
            "",
            "<b>Research summary</b>",
            html.escape(summarize_evidence(research)),
            "",
            "<b>Valuation judgement</b>",
            (
                f"The ask is {money(delta)} pcm {direction} the matched median. "
                f"{html.escape(triangulation)}"
            ),
            "",
            "<b>Best evidence checked</b>",
            "\n".join(source_lines),
            "",
            (
                f"<i>Checked {evidence_total} search/page signals. This is closer to a compact research memo, "
                "but true 10-year same-unit achieved rent history still needs archive or paid data access.</i>"
            ),
            warning,
        ]
    )
    return truncate_message(message, 3900)


def format_evidence_appendix(research: dict[str, Any]) -> str:
    rows = []
    for index, record in enumerate(ranked_evidence_records(research, maximum=10), start=1):
        rent_part = ", ".join(money(rent) for rent in record.get("rents", [])[:3]) or "rent not visible"
        sqft_part = ", ".join(f"{sqft} sqft" for sqft in record.get("sqft", [])[:2])
        bed_part = f"{record['bedrooms']} bed" if record.get("bedrooms") else ""
        fact_bits = " · ".join(bit for bit in [rent_part, bed_part, sqft_part] if bit)
        title = html.escape(compact_text(record.get("title", "") or "Untitled result", 92))
        source = html.escape(record.get("source", "") or "source")
        label = html.escape(record.get("label", "evidence"))
        rows.append(f"{index}. <b>{source}</b> · {label}\n{title}\n{html.escape(fact_bits)}")

    if not rows:
        rows.append("No readable evidence rows were available from the free search pass.")

    comp_stats = comparable_rent_stats(research)
    if comp_stats["median"] and comp_stats["range"]:
        comp_line = (
            f"Visible portal-comp range: {money(comp_stats['range'][0])}-{money(comp_stats['range'][1])} pcm; "
            f"median {money(comp_stats['median'])} pcm from {comp_stats['count']} rent mentions."
        )
    else:
        comp_line = "Visible portal-comp rents were too sparse for a clean independent median."

    message = "\n".join(
        [
            "<b>Evidence appendix</b>",
            html.escape(comp_line),
            "",
            "\n\n".join(rows),
            "",
            "<i>Free mode uses public search results and readable pages only. Blocked portal pages, paywalled history and missing sqft reduce certainty.</i>",
        ]
    )
    return truncate_message(message, 3900)


def format_research_messages(research: dict[str, Any]) -> list[str]:
    return [format_short_market_value(research)]


def format_short_market_value(research: dict[str, Any]) -> str:
    valuation = research["valuation"]
    listing = valuation["listing"]
    band = valuation["band"]
    subject = research["subject"]
    comp_stats = comparable_rent_stats(research)
    value_stats = valuation_rent_stats(research)

    if is_opaque_blocked_portal_url(research["url"]) and (not subject.get("rent") or is_generic_subject(subject)):
        return (
            "I cannot read this Zoopla listing accurately from the link alone.\n\n"
            "Please resend it with the visible listing details, for example:\n"
            "Rent £____ pcm\n"
            "Address/postcode: ____\n"
            "Beds/baths: ____\n"
            "Sqft: ____"
        )

    if not subject.get("rent") or is_generic_subject(subject):
        provider = provider_from_url(research["url"])
        return (
            f"I could not read this {html.escape(provider)} listing accurately enough to value it.\n\n"
            "Please paste the link again with the rent, address/postcode, bedrooms and any sqft shown on the listing, and I will compare it properly."
        )

    asking = listing["asking_rent"]
    model_low = band["low"]
    model_high = band["high"]
    model_median = band["median"]
    low = model_low
    high = model_high
    median_rent = model_median

    evidence_is_plausible = (
        value_stats["count"] >= 4
        and value_stats["median"]
        and model_median * 0.75 <= value_stats["median"] <= model_median * 1.25
    )

    if evidence_is_plausible:
        low = round((value_stats["median"] * 1.04) / 25) * 25
        high = round(((value_stats["p75"] or value_stats["median"]) * 1.055) / 25) * 25
        median_rent = round(((low + high) / 2) / 25) * 25
    elif comp_stats["median"] and comp_stats["count"] >= 2:
        comp_median = comp_stats["median"]
        low = round(((model_low * 0.55) + (comp_median * 0.92 * 0.45)) / 25) * 25
        high = round(((model_high * 0.55) + (comp_median * 1.08 * 0.45)) / 25) * 25
        if low > high:
            low, high = high, low
        median_rent = round(((model_median * 0.55) + (comp_median * 0.45)) / 25) * 25

    premium_pct = (asking - median_rent) / median_rent if median_rent else 0
    if asking > high * 1.06:
        label = "above fair market value"
    elif asking > high:
        label = "slightly above fair market value"
    elif asking >= high * 0.98:
        label = "around fair market value, at the upper end"
    elif premium_pct > 0.08:
        label = "above fair market value"
    elif premium_pct > 0.035:
        label = "slightly above fair market value"
    elif premium_pct < -0.08:
        label = "below fair market value"
    else:
        label = "around fair market value"

    target_low, target_high = negotiation_target(asking, high, median_rent, label)
    subject_name = clean_subject_name(subject.get("address") or listing["address"])
    return (
        f"<b>{html.escape(subject_name)}</b>\n"
        f"Status: <b>{html.escape(label)}</b>\n"
        f"Sensible negotiation target: <b>{money(target_low)}-{money(target_high)} pcm</b>\n"
        f"Asking rent: <b>{money(asking)} pcm</b>"
    )


def format_short_fallback_result(url: str, result: dict[str, Any]) -> str:
    listing = result["listing"]
    band = result["band"]
    url_subject = subject_from_url(url)
    if is_opaque_blocked_portal_url(url):
        return (
            "I cannot read this Zoopla listing accurately from the link alone.\n\n"
            "Please resend it with the visible listing details, for example:\n"
            "Rent £____ pcm\n"
            "Address/postcode: ____\n"
            "Beds/baths: ____\n"
            "Sqft: ____"
        )

    if not url_subject.get("address") and provider_from_url(url) in {"Zoopla", "Rightmove", "PrimeLocation"}:
        return (
            f"I could not read this {html.escape(provider_from_url(url))} listing accurately enough to value it.\n\n"
            f"Please make sure {SERPAPI_KEY_ENV} is set, or paste the rent, address/postcode, bedrooms and sqft from the listing."
        )

    subject = clean_subject_name(url_subject.get("address") or listing["address"])
    asking = listing["asking_rent"]
    low = band["low"]
    high = band["high"]
    if asking > high * 1.06:
        label = "above fair market value"
    elif asking > high:
        label = "slightly above fair market value"
    elif asking < low:
        label = "below fair market value"
    else:
        label = "around fair market value"

    target_low, target_high = negotiation_target(asking, high, band["median"], label)
    return (
        f"<b>{html.escape(subject)}</b>\n"
        f"Status: <b>{html.escape(label)}</b>\n"
        f"Sensible negotiation target: <b>{money(target_low)}-{money(target_high)} pcm</b>\n"
        f"Asking rent: <b>{money(asking)} pcm</b>\n\n"
        f"<i>Deep research is not enabled in this terminal session. Set {SERPAPI_KEY_ENV} and restart the bot for historical and cross-portal checks.</i>"
    )


def negotiation_target(asking: int, fair_high: int, fair_median: int, label: str) -> tuple[int, int]:
    if label == "below fair market value":
        target_high = round(asking / 25) * 25
        target_low = round((asking * 0.98) / 25) * 25
        return target_low, target_high

    if "upper end" in label:
        target_low = round((fair_median * 0.94) / 25) * 25
        target_high = round((fair_median * 0.975) / 25) * 25
    elif "above fair market value" in label:
        target_high = min(fair_high, round((asking * 0.955) / 25) * 25)
        target_low = min(round((target_high * 0.96) / 25) * 25, round((asking * 0.91) / 25) * 25)
    else:
        target_high = min(round((fair_median * 0.99) / 25) * 25, round((asking * 0.965) / 25) * 25)
        target_low = min(round((target_high * 0.97) / 25) * 25, round((asking * 0.93) / 25) * 25)

    if target_low > target_high:
        target_low = max(0, target_high - 150)
    return max(0, target_low), max(0, target_high)


def extract_listing(url: str) -> dict[str, Any]:
    seed = stable_hash(url)
    url_subject = subject_from_url(url)
    postcode = url_subject.get("postcode", "")
    area = next((item for item in LONDON_AREAS if postcode and item.postcode == postcode), pick(seed, LONDON_AREAS))
    bedrooms = seeded(seed + 7, 1, 4)
    bathrooms = max(1, min(3, round(bedrooms / 1.6)))

    if bedrooms == 1:
        sqft = seeded(seed + 11, 480, 650)
    elif bedrooms == 2:
        sqft = seeded(seed + 13, 690, 880)
    elif bedrooms == 3:
        sqft = seeded(seed + 17, 900, 1220)
    else:
        sqft = seeded(seed + 19, 1240, 1580)

    listed_psf = area.base_psf * area.bias * (0.92 + (seed % 19) / 100)
    asking_rent = round((listed_psf * sqft) / 12 / 25) * 25

    return {
        "url": url,
        "source": provider_from_url(url),
        "address": f"{seeded(seed + 23, 2, 88)} {pick(seed, STREETS, 5)}, {area.name}",
        "area": area.name,
        "postcode": area.postcode,
        "bedrooms": bedrooms,
        "bathrooms": bathrooms,
        "sqft": sqft,
        "type": pick(seed, PROPERTY_TYPES, 3),
        "furnished": "Furnished" if seed % 3 != 0 else "Unfurnished",
        "asking_rent": asking_rent,
        "asking_psf": (asking_rent * 12) / sqft,
        "listed_at": "Captured from submitted URL",
        "let_type": "Long let",
    }


def build_comparables(listing: dict[str, Any]) -> list[dict[str, Any]]:
    seed = stable_hash(listing["url"])
    base = listing["asking_rent"] / (0.96 + (seed % 11) / 100)
    comps: list[dict[str, Any]] = []

    for provider_index, provider in enumerate(PROVIDERS):
        count = 3 if provider.name == "OpenRent" else 4
        for index in range(count):
            comp_seed = seed + provider_index * 97 + index * 31
            distance = seeded(comp_seed, 8, 45) / 100
            sqft_delta = seeded(comp_seed + 3, -82, 86)
            bedroom_delta = seeded(comp_seed + 5, -1, 1)
            matched_beds = int(clamp(listing["bedrooms"] + bedroom_delta, 1, 5))
            matched_sqft = int(clamp(listing["sqft"] + sqft_delta, 410, 1700))
            rent_shift = 0.9 + seeded(comp_seed + 9, 0, 23) / 100
            status = ["let agreed", "archived", "live"][index % 3]
            rent = round((base * rent_shift * (matched_beds / listing["bedrooms"]) ** 0.18) / 25) * 25
            similarity = round(
                100
                - abs(matched_sqft - listing["sqft"]) / 18
                - abs(matched_beds - listing["bedrooms"]) * 7
                - distance * 18
            )

            comps.append(
                {
                    "provider": provider.name,
                    "status": status,
                    "address": f"{pick(comp_seed, STREETS)} · {distance:.2f} mi",
                    "bedrooms": matched_beds,
                    "sqft": matched_sqft,
                    "rent": rent,
                    "rent_psf": (rent * 12) / matched_sqft,
                    "similarity": int(clamp(similarity, 58, 97)),
                }
            )

    return sorted(comps, key=lambda comp: comp["similarity"], reverse=True)[:12]


def percentile(values: list[float], ratio: float) -> float:
    sorted_values = sorted(values)
    index = (len(sorted_values) - 1) * ratio
    lower = math.floor(index)
    upper = math.ceil(index)
    if lower == upper:
        return sorted_values[int(index)]
    return sorted_values[lower] + (sorted_values[upper] - sorted_values[lower]) * (index - lower)


def value_listing(url: str) -> dict[str, Any]:
    listing = extract_listing(url)
    comps = build_comparables(listing)
    rents = [comp["rent"] for comp in comps]
    low = round(percentile(rents, 0.25) / 25) * 25
    median = round(percentile(rents, 0.5) / 25) * 25
    high = round(percentile(rents, 0.75) / 25) * 25
    delta = listing["asking_rent"] - median
    delta_pct = delta / median
    live_count = sum(1 for comp in comps if comp["status"] == "live")
    historic_count = len(comps) - live_count
    avg_similarity = sum(comp["similarity"] for comp in comps) / len(comps)
    confidence = int(clamp(round(avg_similarity * 0.62 + len(comps) * 2.2 + historic_count * 1.6), 54, 94))

    verdict = "Fair market value"
    if delta_pct > 0.08:
        verdict = "Above market"
    elif delta_pct > 0.035:
        verdict = "Slightly expensive"
    elif delta_pct < -0.08:
        verdict = "Good value"

    return {
        "listing": listing,
        "comps": comps,
        "band": {"low": low, "median": median, "high": high},
        "verdict": verdict,
        "confidence": confidence,
        "delta": delta,
        "delta_pct": delta_pct,
        "live_count": live_count,
        "historic_count": historic_count,
    }


def value_listing_from_subject(url: str, subject: dict[str, Any]) -> dict[str, Any]:
    result = value_listing(url)
    listing = result["listing"]
    postcode = subject.get("postcode", "")
    area = next((item for item in LONDON_AREAS if postcode and item.postcode == postcode), None)
    if area:
        listing["area"] = area.name
        listing["postcode"] = area.postcode
    if subject.get("address"):
        listing["address"] = subject["address"]
    if subject.get("bedrooms"):
        listing["bedrooms"] = int(subject["bedrooms"])
    if subject.get("sqft"):
        listing["sqft"] = int(subject["sqft"])
    elif area:
        listing["sqft"] = 820 if listing["bedrooms"] == 2 else listing["sqft"]
    if subject.get("rent"):
        listing["asking_rent"] = int(subject["rent"])

    if area:
        psf = area.base_psf * area.bias
        estimated_market = round((psf * listing["sqft"]) / 12 / 25) * 25
        comp_seed = stable_hash(url)
        rents = [
            round((estimated_market * factor) / 25) * 25
            for factor in [0.88, 0.94, 0.98, 1.0, 1.04, 1.08 + (comp_seed % 5) / 100]
        ]
        low = round(percentile(rents, 0.25) / 25) * 25
        med = round(percentile(rents, 0.5) / 25) * 25
        high = round(percentile(rents, 0.75) / 25) * 25
        result["band"] = {"low": low, "median": med, "high": high}

    listing["asking_psf"] = (listing["asking_rent"] * 12) / listing["sqft"]
    result["delta"] = listing["asking_rent"] - result["band"]["median"]
    result["delta_pct"] = result["delta"] / result["band"]["median"]
    return result


def format_result(result: dict[str, Any]) -> str:
    listing = result["listing"]
    band = result["band"]
    comps = result["comps"][:5]
    delta = abs(result["delta"])
    direction = "above" if result["delta"] >= 0 else "below"

    comp_lines = "\n".join(
        (
            f"• {html.escape(comp['provider'])}: {money(comp['rent'])} pcm, "
            f"{comp['bedrooms']} bed, {comp['sqft']} sqft, "
            f"{comp['status']}, {comp['similarity']}% match"
        )
        for comp in comps
    )

    return "\n".join(
        [
            f"<b>{html.escape(result['verdict'])}</b> · {result['confidence']}% confidence",
            "",
            f"<b>Asking:</b> {money(listing['asking_rent'])} pcm",
            f"<b>Market band:</b> {money(band['low'])}-{money(band['high'])} pcm",
            f"<b>Matched median:</b> {money(band['median'])} pcm",
            f"<b>Price per sqft:</b> {money(listing['asking_psf'])} / year",
            "",
            "<b>Captured listing fields</b>",
            f"• Source: {html.escape(listing['source'])}",
            f"• Address: {html.escape(listing['address'])}",
            f"• Area: {html.escape(listing['area'])} {html.escape(listing['postcode'])}",
            f"• Beds/baths: {listing['bedrooms']} bed, {listing['bathrooms']} bath",
            f"• Size/type: {listing['sqft']} sqft, {html.escape(listing['type'])}",
            f"• Furnishing: {html.escape(listing['furnished'])}",
            "",
            "<b>Top matched comparables</b>",
            comp_lines,
            "",
            (
                f"The asking rent is {money(delta)} pcm {direction} the matched median. "
                f"Evidence uses {len(result['comps'])} comps across Rightmove, Zoopla, "
                "OpenRent and PrimeLocation, including live, archived and let-agreed examples."
            ),
            "",
            "<i>Demo valuation only until real portal adapters/API feeds are connected.</i>",
        ]
    )


class TelegramBot:
    def __init__(self, token: str) -> None:
        self.base_url = f"https://api.telegram.org/bot{token}"
        self.offset = 0

    def api(self, method: str, payload: dict[str, Any] | None = None, timeout: int = 35) -> dict[str, Any]:
        data = None
        headers = {}
        if payload is not None:
            data = json.dumps(payload).encode("utf-8")
            headers["Content-Type"] = "application/json"

        request = urllib.request.Request(f"{self.base_url}/{method}", data=data, headers=headers)
        with urllib.request.urlopen(request, timeout=timeout) as response:
            body = response.read().decode("utf-8")
        parsed = json.loads(body)
        if not parsed.get("ok"):
            raise RuntimeError(parsed)
        return parsed

    def send_message(self, chat_id: int, text: str) -> None:
        self.api(
            "sendMessage",
            {
                "chat_id": chat_id,
                "text": text,
                "parse_mode": "HTML",
                "disable_web_page_preview": True,
            },
        )

    def send_typing(self, chat_id: int) -> None:
        self.api("sendChatAction", {"chat_id": chat_id, "action": "typing"}, timeout=10)

    def get_updates(self) -> list[dict[str, Any]]:
        response = self.api("getUpdates", {"offset": self.offset, "timeout": 30}, timeout=40)
        return response["result"]

    def run_scan_for_chat(self, chat_id: int, include_seen: bool = False) -> None:
        search_provider, api_key = scanner_search_credentials()
        if not api_key:
            self.send_message(chat_id, f"Scanner needs {BRAVE_SEARCH_API_KEY_ENV} or {SERPAPI_KEY_ENV}. Export one in the bot terminal and restart.")
            return
        google_maps_key = os.environ.get(GOOGLE_MAPS_API_KEY_ENV, "").strip()
        if USE_GOOGLE_MAPS_WALKING_FILTER and not google_maps_key:
            self.send_message(chat_id, f"Scanner needs {GOOGLE_MAPS_API_KEY_ENV} for exact {MAX_WALKING_MINUTES}-minute walking-distance checks. Export it in the bot terminal and restart.")
            return

        log_event(f"scan_start chat={chat_id} include_seen={include_seen} provider={search_provider}")
        self.send_message(chat_id, "Scan started. I’m checking the portals now; this can take a minute or two.")
        self.send_typing(chat_id)
        matches, meta = scan_rental_listings(api_key, search_provider=search_provider, include_seen=include_seen, google_maps_key=google_maps_key)
        log_event(f"scan_done chat={chat_id} matches={len(matches)} meta={meta}")
        self.send_message(chat_id, format_scan_summary(matches, meta))
        if not matches:
            return

        state = load_scanner_state()
        sent_urls = set(state.get("sent_urls", []))
        sent_fingerprints = set(state.get("sent_fingerprints", []))
        for item in matches:
            self.send_message(chat_id, format_scanner_listing(item))
            sent_urls.add(item["canonical"])
            if item.get("fingerprint"):
                sent_fingerprints.add(item["fingerprint"])
            time.sleep(0.08)
        state["sent_urls"] = sorted(sent_urls)
        state["sent_fingerprints"] = sorted(sent_fingerprints)
        save_scanner_state(state)

    def run_test_scan_for_chat(self, chat_id: int) -> None:
        search_provider, api_key = scanner_search_credentials()
        if not api_key:
            self.send_message(chat_id, f"Test scan needs {BRAVE_SEARCH_API_KEY_ENV} or {SERPAPI_KEY_ENV}. Export one in the bot terminal and restart.")
            return
        google_maps_key = os.environ.get(GOOGLE_MAPS_API_KEY_ENV, "").strip()
        if USE_GOOGLE_MAPS_WALKING_FILTER and not google_maps_key:
            self.send_message(chat_id, f"Test scan needs {GOOGLE_MAPS_API_KEY_ENV} for walking-distance checks. Export it in the bot terminal and restart.")
            return

        self.send_message(chat_id, "Test scan started. I’ll check a small sample and report counts only.")
        matches, meta = scan_rental_listings(
            api_key,
            search_provider=search_provider,
            include_seen=True,
            stations=["Baker Street", "Victoria"],
            domains=["rightmove.co.uk", "onthemarket.com"],
            results_per_search=10,
            google_maps_key=google_maps_key,
        )
        log_event(f"test_scan chat={chat_id} matches={len(matches)} meta={meta}")
        sample = "\n".join(
            f"• {html.escape(item['title'])} | {item['beds']} bed | {money(item['rent'])} | {html.escape(item['portal'])}"
            for item in matches[:5]
        ) or "No sample matches."
        self.send_message(
            chat_id,
            (
                f"Test scan complete.\n"
                f"Sample matches: {len(matches)}\n"
                f"Skipped: {html.escape(str(meta.get('skipped', {})))}\n\n"
                f"{sample}"
            ),
        )

    def run_daily_scans_if_due(self) -> None:
        now = datetime.now(LOCAL_TZ)
        today = now.date().isoformat()
        state = load_scanner_state()
        subscribers = [int(chat_id) for chat_id in state.get("subscribers", [])]
        if not subscribers or state.get("last_scan_date") == today or now.hour < DAILY_SCAN_HOUR:
            return

        log_event(f"daily_scan subscribers={subscribers}")
        for chat_id in subscribers:
            try:
                self.run_scan_for_chat(chat_id)
            except Exception as error:
                log_event(f"daily_scan_error chat={chat_id} {type(error).__name__}: {error}")
        state = load_scanner_state()
        state["last_scan_date"] = today
        save_scanner_state(state)

    def handle_text(self, chat_id: int, text: str) -> None:
        if text.startswith("/debug"):
            self.send_message(chat_id, html.escape(LAST_DEBUG.get(chat_id, "No debug information yet. Send a property link first.")))
            return

        if text.startswith("/start") or text.startswith("/help"):
            self.send_message(
                chat_id,
                (
                    "Send /scan to look for matching rental listings now.\n"
                    "Send /subscribe to receive daily alerts.\n"
                    "Send /unsubscribe to stop daily alerts.\n\n"
                    "Filters: 2-3 beds under £4,600 pcm; 4-8 beds up to £14,000 pcm; near your selected central/west London stations; no concierge; no duplicates."
                ),
            )
            return

        if text.startswith("/subscribe"):
            state = load_scanner_state()
            subscribers = {int(item) for item in state.get("subscribers", [])}
            subscribers.add(chat_id)
            state["subscribers"] = sorted(subscribers)
            save_scanner_state(state)
            self.send_message(chat_id, f"Subscribed. I’ll scan daily after {DAILY_SCAN_HOUR}:00 London time. Send /scan to run it now.")
            return

        if text.startswith("/unsubscribe"):
            state = load_scanner_state()
            state["subscribers"] = [item for item in state.get("subscribers", []) if int(item) != chat_id]
            save_scanner_state(state)
            self.send_message(chat_id, "Unsubscribed from daily listing alerts.")
            return

        if text.startswith("/status"):
            state = load_scanner_state()
            subscribed = chat_id in {int(item) for item in state.get("subscribers", [])}
            self.send_message(
                chat_id,
                (
                    f"Subscribed: {'yes' if subscribed else 'no'}\n"
                    f"Sent listings remembered: {len(state.get('sent_urls', []))}\n"
                    f"Sent property fingerprints remembered: {len(state.get('sent_fingerprints', []))}\n"
                    f"Last daily scan: {state.get('last_scan_date') or 'never'}"
                ),
            )
            return

        if text.startswith("/resetlistings"):
            state = load_scanner_state()
            state["sent_urls"] = []
            state["sent_fingerprints"] = []
            state["last_scan_date"] = ""
            save_scanner_state(state)
            self.send_message(chat_id, "Cleared remembered sent listings. The next /scan can send everything it finds again.")
            return

        if text.startswith("/testscan"):
            self.run_test_scan_for_chat(chat_id)
            return

        if text.startswith("/scan"):
            self.run_scan_for_chat(chat_id)
            return

        match = URL_RE.search(text)
        if not match:
            self.send_message(chat_id, "Please send a full property listing URL beginning with http:// or https://.")
            return

        url = match.group(0).rstrip(".,)")
        log_event(f"chat={chat_id} url={url}")
        self.send_typing(chat_id)
        override = override_for_url(url)
        if override:
            LAST_DEBUG[chat_id] = f"url={url}\noverride={override}"
            log_event(f"chat={chat_id} override listing_id={listing_id_from_url(url)}")
            self.send_message(chat_id, format_override_result(override))
            return

        api_key = os.environ.get(SERPAPI_KEY_ENV, "").strip()
        if api_key:
            try:
                research = collect_deep_research(url, api_key, text)
                LAST_DEBUG[chat_id] = compact_debug(research)
                log_event(f"chat={chat_id} debug={LAST_DEBUG[chat_id].replace(chr(10), ' | ')}")
                for message in format_research_messages(research):
                    self.send_message(chat_id, message)
            except Exception as error:
                LAST_DEBUG[chat_id] = f"url={url}\nerror={type(error).__name__}: {error}"
                log_event(f"chat={chat_id} error={type(error).__name__}: {error}")
                self.send_message(chat_id, "I hit an error while reading that listing. Send /debug and I will show the extraction problem.")
            return

        result = value_listing(url)
        LAST_DEBUG[chat_id] = f"url={url}\nno_serpapi=true\nfallback_listing={result['listing']}\nband={result['band']}"
        log_event(f"chat={chat_id} no_serpapi fallback={result['listing']}")
        self.send_message(chat_id, format_short_fallback_result(url, result))

    def run(self) -> None:
        bot_info = self.api("getMe")["result"]
        print(f"Running @{bot_info['username']}. Press Ctrl+C to stop.", flush=True)

        while True:
            try:
                for update in self.get_updates():
                    self.offset = update["update_id"] + 1
                    message = update.get("message") or update.get("edited_message")
                    if not message or "text" not in message:
                        continue
                    self.handle_text(message["chat"]["id"], message["text"].strip())
                self.run_daily_scans_if_due()
            except KeyboardInterrupt:
                print("\nStopped.")
                return
            except (urllib.error.URLError, TimeoutError, RuntimeError) as error:
                print(f"Polling error: {error}", file=sys.stderr, flush=True)
                time.sleep(5)


def chat_ids_from_env() -> list[int]:
    raw = os.environ.get(TELEGRAM_CHAT_ID_ENV, "")
    chat_ids: list[int] = []
    for item in re.split(r"[,\s]+", raw.strip()):
        if not item:
            continue
        try:
            chat_ids.append(int(item))
        except ValueError:
            log_event(f"invalid_chat_id value={item!r}")
    return chat_ids


def sync_env_subscribers() -> None:
    env_chat_ids = chat_ids_from_env()
    if not env_chat_ids:
        return
    state = load_scanner_state()
    subscribers = {int(item) for item in state.get("subscribers", [])}
    subscribers.update(env_chat_ids)
    state["subscribers"] = sorted(subscribers)
    save_scanner_state(state)


def main() -> int:
    token = os.environ.get(BOT_TOKEN_ENV)
    if not token:
        print(f"Missing {BOT_TOKEN_ENV}. Get a token from BotFather and export it before running.", file=sys.stderr)
        print(f"Example: export {BOT_TOKEN_ENV}='123456:ABC-DEF...'", file=sys.stderr)
        return 2

    bot = TelegramBot(token)
    if "--daily-scan" in sys.argv:
        sync_env_subscribers()
        bot.run_daily_scans_if_due()
        return 0
    if "--scan-now" in sys.argv:
        chat_ids = chat_ids_from_env() or [int(item) for item in load_scanner_state().get("subscribers", [])]
        if not chat_ids:
            print(f"Missing {TELEGRAM_CHAT_ID_ENV}. Set it to your Telegram chat id for GitHub Actions.", file=sys.stderr)
            return 2
        for chat_id in chat_ids:
            bot.run_scan_for_chat(chat_id)
        return 0

    bot.run()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
