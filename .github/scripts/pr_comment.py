#!/usr/bin/env python3
"""Create or update the single bench comment on a pull request.

One comment per pull request, edited in place.  The first call of a run finds
the PR's existing bench comment by the hidden marker on its first line (so a
re-run or a new push reuses it) or creates it, and records the id in
$BENCH_OUT/comment_id; later calls in the same run go straight to that id.
Standard library only.

usage: pr_comment.py <pr-number> <status text>
env:   GITHUB_TOKEN GITHUB_REPOSITORY   (provided by Actions)
       BENCH_OUT                        dir holding progress.txt / compare.txt from bench_ab.sh
       GITHUB_SERVER_URL GITHUB_RUN_ID  for the run link, optional
"""
import json, os, sys, time, urllib.request
from pathlib import Path

MARKER = '<!-- pathmap-bench-ab -->'
LIMIT = 65536            # GitHub's comment body cap
PROGRESS_LINES = 40

pr, status = sys.argv[1], sys.argv[2] if len(sys.argv) > 2 else ''
out = Path(os.environ['BENCH_OUT'])
repo = os.environ['GITHUB_REPOSITORY']
api = f'https://api.github.com/repos/{repo}'
headers = {'Authorization': f"Bearer {os.environ['GITHUB_TOKEN']}",
           'Accept': 'application/vnd.github+json', 'Content-Type': 'application/json'}
run_url = f"{os.environ.get('GITHUB_SERVER_URL', 'https://github.com')}/{repo}/actions/runs/{os.environ.get('GITHUB_RUN_ID', '')}"


def call(method, url, data=None):
    req = urllib.request.Request(url, method=method, headers=headers,
                                 data=json.dumps(data).encode() if data is not None else None)
    with urllib.request.urlopen(req, timeout=30) as r:
        return json.load(r)


def read(name):
    p = out / name
    return p.read_text() if p.is_file() else ''


parts = [MARKER, f'### Bench A/B vs base: {status}', '',
         f"[run log]({run_url}) · updated {time.strftime('%Y-%m-%d %H:%M:%S', time.gmtime())} UTC"]
progress = read('progress.txt').splitlines()
if progress:
    parts += ['', f'<details><summary>progress (last {PROGRESS_LINES} lines)</summary>', '', '```',
              *progress[-PROGRESS_LINES:], '```', '</details>']
compare = read('compare.txt')
if compare:
    head = '\n'.join(parts)
    room = LIMIT - len(head) - 200
    if len(compare) > room:
        compare = compare[:room] + '\n… truncated; the full table is in the bench-out artifact\n'
    parts += ['', '```', compare.rstrip(), '```']
body = '\n'.join(parts)

id_file = out / 'comment_id'
if id_file.is_file():
    cid = id_file.read_text().strip()
    how = 'updated'
else:
    found = [c['id'] for c in call('GET', f'{api}/issues/{pr}/comments?per_page=100') if c['body'].startswith(MARKER)]
    cid = found[0] if found else None
    how = 'reused' if found else 'created'
if cid is None:
    cid = call('POST', f'{api}/issues/{pr}/comments', {'body': body})['id']
else:
    call('PATCH', f'{api}/issues/comments/{cid}', {'body': body})
id_file.write_text(str(cid))
print(f'comment {cid} {how}: {len(body)} chars')
