# Site solution backup

A copy of the solution write-ups that **principia-math.com serves from its own file store**
rather than from GitHub. For 247 projects those bytes existed in exactly one place; this
directory is a second place.

**493 files, 17.5 MB, 247 projects** — 246 solution PDFs and 247 LaTeX sources (one project
publishes a source with no PDF). Taken 2026-10-26 from
`https://principia-math.com/api/ws/files/<id>`, the URL each project's solution stage pointed
at. `MANIFEST.json` records, for every file, its project id and title, the project page, the
original URL, the stored path, the byte count and the sha256.

## What this is not

- **Not a publication, and not a claim.** Nothing here was re-derived, re-checked or reviewed.
  The site hosts these because someone solved the problem there; this directory only mirrors
  the bytes.
- **Not linked from the site.** No project's stage link points into this directory — each one
  still points at the site's own copy. So nothing on Principia depends on this directory, and
  deleting it would break no link. That is deliberate: a backup that things depend on is not a
  backup.
- **Not formalized.** Most of these problems have no Lean formalization at all. The 143 that
  do are in [`../mathdb/`](../mathdb/), and what "verified" means for those — including that
  only one has been through the Comparator — is in
  [`../mathdb/VERIFICATION.md`](../mathdb/VERIFICATION.md). A write-up being present here says
  nothing about machine checking.
- **Not every solution the site holds.** Three projects whose write-ups are the work of named
  people other than this repository's maintainers were deliberately left out, since copying
  someone's solution into this organization's repository is their decision to make: MathDB
  #328424, #369283 and #380445. Everything here belongs to a project that is *ownerless* on
  Principia — bulk-loaded content with no author recorded on the site.

## Verifying a copy against the site

Each row in `MANIFEST.json` carries the source URL and the sha256 of what was stored, so a
copy can be checked rather than trusted:

```sh
python - <<'PY'
import hashlib, json, urllib.request
rows = json.load(open("MANIFEST.json", encoding="utf-8"))
bad = []
for r in rows:
    live = urllib.request.urlopen(r["source_url"]).read()
    if hashlib.sha256(live).hexdigest() != r["sha256"]:
        bad.append(r["stored_as"])
print("differ from the site:", bad or "none")
PY
```

A mismatch means the site's copy changed after this snapshot, not that the backup is corrupt —
compare against the stored file's own hash to tell the two apart.
