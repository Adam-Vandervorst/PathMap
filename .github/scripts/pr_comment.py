#!/usr/bin/env python3
"""Create or update the single bench comment on a pull request.

One comment per pull request, edited in place: a status line, a link to the
job that produced it, and bench_ab.py's summary.md once it exists.  The
first call of a run finds the PR's existing bench comment by the hidden marker
on its first line (so a re-run or a new push reuses it) or creates it, and
records the id in $BENCH_OUT/comment_id; later calls in the same run go
straight to that id.  Standard library only.

usage: pr_comment.py <pr-number> <status text>
env:   GITHUB_TOKEN GITHUB_REPOSITORY GITHUB_RUN_ID RUNNER_NAME   (provided by Actions)
       BENCH_OUT                        dir holding summary.md from bench_ab.py
       GITHUB_SERVER_URL                optional
"""
import json, os, sys, time, urllib.request
from pathlib import Path

MARKER = '<!-- pathmap-bench-ab -->'
LIMIT = 65536            # GitHub's comment body cap

pr, status = sys.argv[1], sys.argv[2] if len(sys.argv) > 2 else ''
out = Path(os.environ['BENCH_OUT'])
repo = os.environ['GITHUB_REPOSITORY']
api = f'https://api.github.com/repos/{repo}'
headers = {'Authorization': f"Bearer {os.environ['GITHUB_TOKEN']}",
           'Accept': 'application/vnd.github+json', 'Content-Type': 'application/json'}
run_id = os.environ.get('GITHUB_RUN_ID', '')
run_url = f"{os.environ.get('GITHUB_SERVER_URL', 'https://github.com')}/{repo}/actions/runs/{run_id}"


def call(method, url, data=None):
    req = urllib.request.Request(url, method=method, headers=headers,
                                 data=json.dumps(data).encode() if data is not None else None)
    with urllib.request.urlopen(req, timeout=30) as r:
        return json.load(r)


def read(name):
    p = out / name
    return p.read_text() if p.is_file() else ''


def job_url():
    """Link to this job's log: the job in progress on this runner within the run.  Cached per run."""
    cache = out / 'job_url'
    if cache.is_file():
        return cache.read_text().strip()
    url = run_url
    try:
        jobs = call('GET', f'{api}/actions/runs/{run_id}/jobs?per_page=100')['jobs']
        mine = [j for j in jobs if j.get('runner_name') == os.environ.get('RUNNER_NAME') and j.get('status') == 'in_progress']
        if mine:
            url = mine[0]['html_url']
            cache.write_text(url)
    except Exception as e:                       # the run link is a fine fallback
        print(f'job lookup failed, using run link: {e}', file=sys.stderr)
    return url


parts = [MARKER, f'### Bench A/B vs base: {status}', '',
         f"[job log]({job_url()}) · {time.strftime('%Y-%m-%d %H:%M:%S', time.gmtime())} UTC"]
summary = read('summary.md')
if summary:
    head = '\n'.join(parts)
    room = LIMIT - len(head) - 200
    if len(summary) > room:
        summary = summary[:room] + '\n\n… truncated; see the bench-out artifact\n'
    parts += ['', summary.rstrip()]
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
