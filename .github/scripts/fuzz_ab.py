#!/usr/bin/env python3
"""Differential fuzz of two commits against the Lean model, as a regression gate.

The crate at HEAD has known divergences from the model, so "zero divergences"
cannot be the bar.  Instead both commits are run on identical inputs, and an
input that diverges on HEAD but not on BASE is reported as a GitHub warning
annotation (the job stays green) or, with FUZZ_STRICT=1, fails the job.  A
run that does not finish always fails the job.  For the first REPROS newly
diverging inputs with distinct first-differing operations, the input is
shrunk with lean/shrink.py and a standalone Rust reproducer is emitted with
`pathmap_trace --repro` into the summary and $FUZZ_OUT/repro/.  The harness
(differential/) and the model (lean/) are taken from HEAD for both sides, so
the only thing that differs is the crate under test in src/.  If BASE cannot
be built with HEAD's harness, BASE's own harness is tried; if that fails too
there is no baseline, which is reported loudly and does not fail the job.

usage: fuzz_ab.py <base-sha> <head-sha>

env:  FUZZ_INPUTS        random programs, model vs crate        (default 20000)
      FUZZ_ACT_INPUTS    random programs with the ACT read side (default 5000; 0 skips)
      FUZZ_SEED          (default 7)
      FUZZ_JOBS          worker processes                        (default 16)
      FUZZ_STRICT        1 = new divergences fail the job instead of warning (default 0)
      FUZZ_REPROS        newly diverging inputs to shrink and turn into Rust (default 3)
      FUZZ_OUT           output dir                              (default ./fuzz-out)
      CARGO_TARGET_DIR   parent of the per-side target dirs      (default ./target)
      LAKE_CACHE         optional dir to keep lean's .lake build dirs across runs
"""
import os, re, shutil, subprocess, sys, time
from pathlib import Path

FAIL_RE = re.compile(r'^FAIL (\S+) \[saved ([^\]]*)\]: (.*)$')
SUMMARY_RE = re.compile(r'^(\d+)/(\d+) inputs agree \((\d+) hit known bugs, (\d+) new divergences\)')
KNOWN_RE = re.compile(r'^  known x(\d+): (.*)$')


def log(*a, **kw):
    print(*a, flush=True, **kw)


def git(*args, cwd=None, check=True):
    return subprocess.run(['git', *args], cwd=cwd, check=check, text=True, capture_output=True).stdout.strip()


def tail(path, n=30):
    return '\n'.join(Path(path).read_text().splitlines()[-n:])


class Fuzz:
    def __init__(self, base, head):
        self.repo = Path.cwd()
        self.base_sha, self.head_sha = base, head
        self.inputs = int(os.environ.get('FUZZ_INPUTS', 20000))
        self.act_inputs = int(os.environ.get('FUZZ_ACT_INPUTS', 5000))
        self.seed = os.environ.get('FUZZ_SEED', '7')
        self.jobs = os.environ.get('FUZZ_JOBS', '16')
        self.out = Path(os.environ.get('FUZZ_OUT', self.repo / 'fuzz-out')).resolve()
        self.target = Path(os.environ.get('CARGO_TARGET_DIR', self.repo / 'target')).resolve()
        self.lake_cache = os.environ.get('LAKE_CACHE')
        self.strict = os.environ.get('FUZZ_STRICT', '0') == '1'
        self.repros = int(os.environ.get('FUZZ_REPROS', 3))
        self.base_src = self.out / 'src-base'
        self.modes = [('crate', self.inputs, [])]
        if self.act_inputs > 0:
            self.modes.append(('act', self.act_inputs, ['--act']))

    def short(self, sha):
        return git('rev-parse', '--short', sha, cwd=self.repo)

    def cleanup(self):
        subprocess.run(['git', 'worktree', 'remove', '--force', str(self.base_src)], cwd=self.repo,
                       capture_output=True)

    def build_side(self, side, src):
        """lake build + cargo build into this side's target dir.  Returns False on failure."""
        if self.lake_cache:
            cache = Path(self.lake_cache) / side
            cache.mkdir(parents=True, exist_ok=True)
            lake = src / 'lean' / '.lake'
            if lake.is_symlink() or lake.exists():
                lake.unlink() if lake.is_symlink() else shutil.rmtree(lake)
            lake.symlink_to(cache)
        for name, cmd, cwd in (('lake', ['lake', 'build'], src / 'lean'),
                               ('build', ['cargo', 'build', '--release', '-p', 'differential',
                                          '--target-dir', str(self.target / f'fuzz-{side}')], src)):
            logf = self.out / f'{name}-{side}.log'
            t0 = time.time()
            with open(logf, 'w') as f:
                p = subprocess.run(cmd, cwd=cwd, stdout=f, stderr=subprocess.STDOUT)
            if p.returncode:
                log(f'{name} for {side} failed:\n{tail(logf)}')
                return False
            log(f'   {" ".join(cmd[:2])} for {side}: ok in {time.time() - t0:.0f}s (log: {logf.name})')
        return True

    def prepare_base(self):
        """Build base with head's harness and model; fall back to base's own.  Returns the baseline kind."""
        log(f"== building base ({self.short(self.base_sha)}) with head's differential/ and lean/")
        for d in ('differential', 'lean'):
            shutil.rmtree(self.base_src / d)
            shutil.copytree(self.repo / d, self.base_src / d, symlinks=True,
                            ignore=shutil.ignore_patterns('.lake'))
        if self.build_side('base', self.base_src):
            return 'head-harness'
        log("== head's harness does not build against base; trying base's own")
        git('checkout', '--', 'differential', 'lean', cwd=self.base_src)
        git('clean', '-fdq', '--', 'differential', 'lean', cwd=self.base_src)
        return 'base-harness' if self.build_side('base', self.base_src) else 'none'

    def run_side(self, side, src, label, n, flags):
        env = dict(os.environ,
                   TMPDIR=str(self.out / f'fails-{side}-{label}'),
                   PATHMAP_TRACE=str(self.target / f'fuzz-{side}' / 'release' / 'pathmap_trace'),
                   PATHMAP_ACT_TRACE=str(self.target / f'fuzz-{side}' / 'release' / 'act_trace'))
        Path(env['TMPDIR']).mkdir(parents=True, exist_ok=True)
        log(f'== fuzz {label} {side}: {n} inputs, seed {self.seed}')
        outf = self.out / f'fuzz-{label}-{side}.txt'
        with open(outf, 'w') as f:
            subprocess.run([str(src / 'lean' / 'differential.py'), '--random', str(n), '--seed', self.seed,
                            '--maxlen', '300', '--max-fails', '0', '-j', self.jobs, *flags],
                           cwd=src, env=env, stdout=f, stderr=subprocess.STDOUT)
        text = outf.read_text()
        info = [l for l in text.splitlines() if SUMMARY_RE.match(l) or 'child restart' in l]
        log('\n'.join(info) if info else tail(outf, 5))

    def parse(self, label, side):
        """fails: name -> {'path', 'msg', 'detail'}; summary: (agree, total, known, new); known: class -> count."""
        fails, summary, last, known = {}, None, None, {}
        p = self.out / f'fuzz-{label}-{side}.txt'
        if p.is_file():
            for line in p.read_text().splitlines():
                if m := FAIL_RE.match(line):
                    last = fails[m.group(1)] = {'path': m.group(2), 'msg': m.group(3), 'detail': []}
                elif line.startswith('  ') and last is not None:
                    last['detail'].append(line.strip())      # the "lean: ..." / "crate: ..." trace lines
                else:
                    last = None
                if m := SUMMARY_RE.match(line):
                    summary = tuple(map(int, m.groups()))
                if m := KNOWN_RE.match(line):
                    known[m.group(2)] = int(m.group(1))
        return fails, summary, known

    @staticmethod
    def kind(f):
        """What diverged: the first-differing op from the model's trace line, else the message shape."""
        for d in f['detail']:
            if d.startswith('lean:'):
                parts = d.split()
                if len(parts) > 1 and parts[1].startswith(('MAP', 'ROOT')):
                    return f'{parts[1]} (final state)'
                if len(parts) > 2:
                    return parts[2]
        return re.sub(r'\d+', 'N', f['msg'])

    def repro(self, label, name, f, flags):
        """Shrink one newly diverging input and emit a Rust reproducer.  Returns markdown."""
        rdir = self.out / 'repro'
        rdir.mkdir(exist_ok=True)
        stem = rdir / f'{label}-{name.replace("#", "_")}'
        env = dict(os.environ,
                   PATHMAP_ORACLE=os.environ.get('PATHMAP_ORACLE') or str(self.repo / 'lean' / '.lake' / 'build' / 'bin' / 'pathmap-oracle'),
                   PATHMAP_TRACE=str(self.target / 'fuzz-head' / 'release' / 'pathmap_trace'),
                   PATHMAP_ACT_TRACE=str(self.target / 'fuzz-head' / 'release' / 'act_trace'))
        small = stem.with_suffix('.min.bin')
        note = ''
        try:
            r = subprocess.run([str(self.repo / 'lean' / 'shrink.py'), f['path'], '-o', str(small), *flags],
                               cwd=self.repo, env=env, capture_output=True, text=True, timeout=600)
            sizes = next((l for l in r.stdout.splitlines() if ' -> ' in l and 'bytes' in l), None)
            if r.returncode or not small.is_file():
                raise RuntimeError((r.stdout + r.stderr).strip().splitlines()[-1:] or ['shrink failed'])
            note = sizes.split(', written')[0] if sizes else 'shrunk'
        except (subprocess.TimeoutExpired, RuntimeError) as e:
            shutil.copy(f['path'], small)
            note = f'not shrunk ({e}); reproducer is for the full input'
        r = subprocess.run([env['PATHMAP_TRACE'], '--repro', str(small)], capture_output=True, text=True)
        code = r.stdout if r.returncode == 0 else f'// pathmap_trace --repro failed:\n// {r.stderr.strip()}'
        stem.with_suffix('.rs').write_text(code)
        act_note = ' (act mode: the harness reads map1 through an ArenaCompactTree; the reproducer uses a PathMap read zipper)' if flags else ''
        log(f'== repro {label} {name}: {self.kind(f)}, {note}\n{code}')
        return '\n'.join([f'<details><summary><code>{name}</code>: first differs at <code>{self.kind(f)}</code>, {note}{act_note}</summary>', '',
                           f"{f['msg']}", *[f'    {d}' for d in f['detail']], '', '```rust', code.rstrip(), '```', '', '</details>', ''])

    def summarize(self, baseline):
        """Write summary.md (with reproducers for the first few new divergences); return (new divergences, unfinished runs)."""
        L = [f'# Differential fuzz: head {self.short(self.head_sha)} vs base {self.short(self.base_sha)}', '', '', '']
        if baseline == 'none':
            L += ['**No baseline**: base could not be built with either harness, so only head was run and nothing is gated.', '']
        elif baseline == 'base-harness':
            L += ["Base was built with its own harness and model (head's did not build against it), "
                  'so harness changes may show up as differences.', '']
        new_total, unfinished = 0, 0
        for label, n, _ in self.modes:
            hf, hs, hk = self.parse(label, 'head')
            bf, bs, bk = self.parse(label, 'base')
            L += [f'## {label}: {n} inputs, seed {self.seed}', '',
                  'agree = model and crate match; known = the divergence matches a classified bug in '
                  'differential.py; new = it matches none.  Only the new set is compared input by input below.', '',
                  '| side | agree | known | new divergences |', '|---|---:|---:|---:|']
            for side, s in (('head', hs), ('base', bs)):
                if s:
                    L.append(f'| {side} | {s[0]}/{s[1]} | {s[2]} | {s[3]} |')
                elif side == 'head' or baseline != 'none':
                    L.append(f'| {side} | run did not finish, see fuzz-{label}-{side}.txt | | |')
                    unfinished += 1
            if baseline != 'none' and hs and bs:
                new = sorted(set(hf) - set(bf))          # names are random#NNNNN, so this is input order
                fixed = sorted(set(bf) - set(hf))
                L += ['', f'{len(new)} input(s) diverge on head but not on base; {len(fixed)} diverge on base but not on head.']
                changed = sorted(((bk.get(k, 0), hk.get(k, 0), k) for k in set(bk) | set(hk) if bk.get(k, 0) != hk.get(k, 0)),
                                 key=lambda t: -abs(t[0] - t[1]))
                if changed:
                    L += ['', '### Known-class hits that changed', '', '| known class | base | head |', '|---|---:|---:|']
                    L += [f'| {k[:100]} | {b} | {h} |' for b, h, k in changed[:10]]
                    if len(changed) > 10:
                        L.append(f'| … {len(changed) - 10} more | | |')
                if new:
                    new_total += len(new)
                    log(f'::{"error" if self.strict else "warning"} title=Differential fuzz ({label})::{len(new)} input(s) diverge from the model on head '
                        f'but not on base, e.g. {new[0]}: {hf[new[0]]["msg"][:150]}')
                    kinds = {}                                # first-differing op -> [input names], input order
                    for name in new:
                        kinds.setdefault(self.kind(hf[name]), []).append(name)
                    L += ['', f'### Newly diverging inputs (head only): {len(new)} input(s), {len(kinds)} kind(s)', '',
                          '| first differs at | inputs | first example |', '|---|---:|---|']
                    for k, names in list(kinds.items())[:10]:
                        L.append(f'| `{k}` | {len(names)} | `{names[0]}`: {hf[names[0]]["msg"][:80]} |')
                    if len(kinds) > 10:
                        L.append(f'| … {len(kinds) - 10} more kind(s) | | see fuzz-{label}-head.txt |')
                    picked = [names[0] for names in kinds.values()][:self.repros]
                    if picked:
                        flags = next(fl for lb, _, fl in self.modes if lb == label)
                        L += ['', f'### Reproducers: first {len(picked)} distinct kind(s), shrunk', '']
                        L += [self.repro(label, name, hf[name], flags) for name in picked]
                if fixed:
                    L += ['', f'<details><summary>{len(fixed)} input(s) fixed on head</summary>', '']
                    L += [f'- `{name}`' for name in fixed[:50]]
                    L += ['', '</details>']
            L.append('')
        if unfinished:
            L[2] = '**FAIL: a fuzz run did not finish**'
        elif new_total:
            L[2] = f'**{"FAIL" if self.strict else "WARNING"}: {new_total} new divergence(s) relative to base**'
        else:
            L[2] = '**OK: no new divergences relative to base**'
        text = '\n'.join(L) + '\n'
        (self.out / 'summary.md').write_text(text)
        findings = self.out / 'findings'                  # exists only when there is something to report
        findings.unlink(missing_ok=True)
        if new_total or unfinished:
            findings.write_text(f'{new_total} new divergences, {unfinished} unfinished runs\n')
        log(text, end='')
        return new_total, unfinished

    def main(self):
        self.out.mkdir(parents=True, exist_ok=True)
        for f in self.out.iterdir():
            if f.suffix in ('.txt', '.log', '.md'):
                f.unlink()
        shutil.rmtree(self.out / 'repro', ignore_errors=True)
        self.cleanup()
        try:
            git('worktree', 'add', '--detach', str(self.base_src), self.base_sha, cwd=self.repo)
            log(f'== building head ({self.short(self.head_sha)})')
            if not self.build_side('head', self.repo):
                sys.exit(1)
            baseline = self.prepare_base()
            for label, n, flags in self.modes:
                self.run_side('head', self.repo, label, n, flags)
                if baseline != 'none':
                    self.run_side('base', self.base_src, label, n, flags)
            new_total, unfinished = self.summarize(baseline)
            return 1 if unfinished or (self.strict and new_total) else 0
        finally:
            self.cleanup()


if __name__ == '__main__':
    if len(sys.argv) != 3:
        sys.exit('usage: fuzz_ab.py <base-sha> <head-sha>')
    sys.exit(Fuzz(sys.argv[1], sys.argv[2]).main())
