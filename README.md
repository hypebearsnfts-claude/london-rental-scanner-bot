# London Rental Price Checker Telegram Bot

A Telegram bot for checking whether a London rental listing appears fair against matched comparables.

## What it does

- Accepts a user-submitted property listing URL in Telegram.
- Captures core listing fields in a deterministic demo extractor.
- Builds comparable evidence across Rightmove, Zoopla, OpenRent and PrimeLocation.
- Mixes live, archived and let-agreed comparable rents.
- Computes asking rent, market band, price-per-sqft, verdict and confidence.
- Optional live research mode searches for same-property history, ten-year rental traces and apple-to-apple area comps before replying with a concise summary.

## Why this is not public

`telegram_bot.py` uses Telegram long polling. It does not open a public web server and it does not listen for inbound traffic. Your computer simply asks Telegram for new messages and sends replies back through Telegram's HTTPS API.

## Create your Telegram bot

1. Open Telegram and message `@BotFather`.
2. Send `/newbot`.
3. Choose a bot name and username.
4. Copy the token BotFather gives you.

## Run the real Telegram bot

No third-party Python packages are required.

```sh
export TELEGRAM_BOT_TOKEN="paste-your-botfather-token-here"
export BRAVE_SEARCH_API_KEY="paste-your-brave-search-api-key-here"
# Or use SERPAPI_KEY instead.
python3 telegram_bot.py
```

Then open Telegram, message your bot, and paste a listing URL.

Stop the bot with `Ctrl+C`.

## Run daily from GitHub Actions

The repository includes `.github/workflows/daily-rental-scan.yml`. GitHub Actions can run the listing radar even when your laptop is off.

Add these repository secrets in GitHub:

- `TELEGRAM_BOT_TOKEN`
- `TELEGRAM_CHAT_ID`
- `BRAVE_SEARCH_API_KEY`
- Optional fallback: `SERPAPI_KEY`

The scheduled workflow runs at 11:00 and 12:00 UTC. The Python script checks London local time and only sends the daily scan once after 12:00 London time, including daylight-saving changes. Manual `workflow_dispatch` runs scan immediately.

After each successful scan, the workflow commits the updated `scanner_state.json` so the next day does not resend the same URLs or same-property fingerprints.

## Research filter bot

The bot can also run as a daily rental-listing radar.

Telegram commands:

- `/scan` searches now and sends new matching listings.
- `/subscribe` enables daily alerts after 12:00 London time.
- `/unsubscribe` stops daily alerts.
- `/status` shows subscription and duplicate-memory status.
- `/resetlistings` clears remembered sent listings if you want to rerun the first scan from scratch.
- `/testscan` runs a small sample scan and reports counts without saving/sending all listings.

Current filters:

- 2-3 bedrooms below £4,600 pcm.
- 4-8 bedrooms up to £14,000 pcm.
- Furnished only, where furnishing is visible in the public search result.
- Excludes visible part-furnished, shared accommodation, house-share, flat-share and student-accommodation results.
- Long-let style rentals only; excludes visible short-let results.
- Search focus around Kensington Olympia, Bayswater, Lancaster Gate, Gloucester Road, South Kensington, Marble Arch, Bond Street, Baker Street, Regent Park, Oxford Circus, Tottenham Court Road, Covent Garden, Leicester Square, Piccadilly Circus, Holborn, Charing Cross and Victoria.
- Includes station-name aliases such as `Kensington (Olympia)`, `Regent's Park` and the common Piccadilly spelling variant.
- Station-name matching only. The bot searches for listings that mention the watched stations or nearby station context; it does not enforce exact walking distance.
- Excludes listings where the visible title/snippet contains `concierge`.
- Excludes listings where the visible title/snippet contains `let agreed`.
- Remembers sent listing URLs and same-property fingerprints in `scanner_state.json`, so duplicate cross-posts from different portals are less likely to be resent.
- Searches each portal separately for each station, keeps paginating until there are no new search results, and sends every new match it finds; there is no artificial send cap. A high safety cap prevents infinite loops if the search API repeats pages. Brave Search uses 20 results per page; SerpApi can request larger pages.
- Checks the live detail page where possible and skips results that look removed, no longer available, let agreed, now let, or not live.

Limitations: this uses public search plus readable listing pages via SerpApi, so it cannot guarantee every hidden/private listing inside each portal database. Station proximity is based on station-name matching, not exact walking distance. Some portals block detail-page reads; the scanner skips unverified blocked results rather than sending stale listings.

## Enable deep research mode

The bot cannot use ChatGPT's built-in Deep Research by itself. To research the public web from your own machine, give it a search API key. This version supports SerpApi because it works from a simple Python script without extra packages.

```sh
export TELEGRAM_BOT_TOKEN="paste-your-botfather-token-here"
export SERPAPI_KEY="paste-your-serpapi-key-here"
python3 telegram_bot.py
```

With `SERPAPI_KEY` set, each property valuation link triggers the research workflow below silently:

- listing page fetch and metadata extraction where the portal allows it;
- same-address historical rental searches;
- ten-year archive trace searches;
- portal-specific comparable searches across Rightmove, Zoopla, OpenRent and PrimeLocation;
- wider free-web checks across archive portals, Home.co.uk, ONS and prime-market sources;
- a short Telegram answer with fair market value, negotiation target and premium/fair-value verdict.

Without `SERPAPI_KEY`, the bot still replies, but it uses the deterministic demo valuation logic and tells you deep research is not enabled.

## Optional local visual prototype

The earlier browser mock is still available for interface design:

```sh
python3 -m http.server 5173 --bind 127.0.0.1
```

Then visit `http://127.0.0.1:5173`.

## Production notes

The current implementation is a working Telegram bot with deterministic fallback valuation logic and optional live search. For production, replace the demo extractor in `telegram_bot.py` with compliant source adapters, API feeds, browser-rendered extraction, cache storage, and audit logs for every comparable included in a verdict. For true ten-year same-unit rent history, you will likely need paid/archive data because portals do not expose a complete public achieved-rent tape.
