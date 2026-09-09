#!/usr/bin/env python3
"""Create or update one job's comment on a pull request.

One comment per pull request and job id, edited in place: a title with a
status, a link to the job that produced it, and the job's summary.md once it
exists.  The first call of a run finds the PR's existing comment by the hidden
marker on its first line (so a re-run or a new push reuses it) or creates it,
and records the id in <dir>/comment_id; later calls in the same run go straight
to that id.  Standard library only.

usage: pr_comment.py [--id ID] [--title TITLE] [--dir DIR] <pr-number> <status text>
       --id     comment identity, one per job          (default bench-ab)
       --title  heading before the status              (default "Bench A/B vs base")
       --dir    dir holding summary.md, comment_id     (default $BENCH_OUT)
       --create-only-if FILE  create the comment only when FILE exists; an existing comment is
                              always updated (so a clean run clears earlier findings)
env:   GITHUB_TOKEN GITHUB_REPOSITORY GITHUB_RUN_ID RUNNER_NAME   (provided by Actions)
       GITHUB_SERVER_URL                optional
"""
import argparse, json, os, sys, time, urllib.request
from pathlib import Path

LIMIT = 65536            # GitHub's comment body cap

ap = argparse.ArgumentParser()
ap.add_argument('--id', default='bench-ab')
ap.add_argument('--title', default='Bench A/B vs base')
ap.add_argument('--dir', default=os.environ.get('BENCH_OUT'))
ap.add_argument('--create-only-if')
ap.add_argument('pr')
ap.add_argument('status', nargs='?', default='')
args = ap.parse_args()
pr, status = args.pr, args.status
MARKER = f'<!-- pathmap-{args.id} -->'
out = Path(args.dir)
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


parts = [MARKER, f'### {args.title}: {status}', '',
         f"[job log]({job_url()}) · {time.strftime('%Y-%m-%d %H:%M:%S', time.gmtime())} UTC"]
summary = read('summary.md')
if summary.startswith('# '):                 # the comment has its own heading
    summary = summary.split('\n', 1)[1].lstrip('\n') if '\n' in summary else ''
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
if cid is None and args.create_only_if and not Path(args.create_only_if).exists():
    print(f'no comment yet and {args.create_only_if} is absent: nothing to report')
    sys.exit(0)
if cid is None:
    cid = call('POST', f'{api}/issues/{pr}/comments', {'body': body})['id']
else:
    call('PATCH', f'{api}/issues/comments/{cid}', {'body': body})
id_file.write_text(str(cid))
print(f'comment {cid} {how}: {len(body)} chars')
