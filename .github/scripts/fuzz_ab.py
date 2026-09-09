#!/usr/bin/env python3
"""Differential fuzz of two commits against the Lean model, as a regression gate.

The crate at HEAD has known divergences from the model, so "zero divergences"
cannot be the bar.  Instead both commits are run on identical inputs, and an
input that diverges on HEAD but not on BASE is reported as a GitHub warning
annotation (the job stays green) or, with FUZZ_STRICT=1, fails the job.  A
run that does not finish always fails the job.  The harness
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
      FUZZ_OUT           output dir                              (default ./fuzz-out)
      CARGO_TARGET_DIR   parent of the per-side target dirs      (default ./target)
      LAKE_CACHE         optional dir to keep lean's .lake build dirs across runs
"""
import os, re, shutil, subprocess, sys
from pathlib import Path

FAIL_RE = re.compile(r'^FAIL (\S+) \[saved [^\]]*\]: (.*)$')
SUMMARY_RE = re.compile(r'^(\d+)/(\d+) inputs agree \((\d+) hit known bugs, (\d+) new divergences\)')


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
            with open(logf, 'w') as f:
                p = subprocess.run(cmd, cwd=cwd, stdout=f, stderr=subprocess.STDOUT)
            if p.returncode:
                log(f'{name} for {side} failed:\n{tail(logf)}')
                return False
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
        fails, summary = {}, None
        p = self.out / f'fuzz-{label}-{side}.txt'
        if p.is_file():
            for line in p.read_text().splitlines():
                if m := FAIL_RE.match(line):
                    fails[m.group(1)] = m.group(2)
                if m := SUMMARY_RE.match(line):
                    summary = tuple(map(int, m.groups()))
        return fails, summary

    def summarize(self, baseline):
        """Write summary.md; return (new divergences, unfinished runs)."""
        L = [f'# Differential fuzz: head {self.short(self.head_sha)} vs base {self.short(self.base_sha)}', '', '', '']
        if baseline == 'none':
            L += ['**No baseline**: base could not be built with either harness, so only head was run and nothing is gated.', '']
        elif baseline == 'base-harness':
            L += ["Base was built with its own harness and model (head's did not build against it), "
                  'so harness changes may show up as differences.', '']
        new_total, unfinished = 0, 0
        for label, n, _ in self.modes:
            hf, hs = self.parse(label, 'head')
            bf, bs = self.parse(label, 'base')
            L += [f'## {label}: {n} inputs, seed {self.seed}', '',
                  '| side | agree | known | new divergences |', '|---|---:|---:|---:|']
            for side, s in (('head', hs), ('base', bs)):
                if s:
                    L.append(f'| {side} | {s[0]}/{s[1]} | {s[2]} | {s[3]} |')
                elif side == 'head' or baseline != 'none':
                    L.append(f'| {side} | run did not finish, see fuzz-{label}-{side}.txt | | |')
                    unfinished += 1
            if baseline != 'none' and hs and bs:
                new = sorted(set(hf) - set(bf))
                fixed = sorted(set(bf) - set(hf))
                L += ['', f'{len(new)} input(s) diverge on head but not on base; {len(fixed)} diverge on base but not on head.']
                if new:
                    new_total += len(new)
                    log(f'::{"error" if self.strict else "warning"} title=Differential fuzz ({label})::{len(new)} input(s) diverge from the model on head '
                        f'but not on base, e.g. {new[0]}: {hf[new[0]][:150]}')
                    L += ['', '### Newly diverging inputs (head only)', '']
                    L += [f'- `{name}`: {hf[name][:200]}' for name in new[:50]]
                    if len(new) > 50:
                        L.append(f'- … and {len(new) - 50} more, see fuzz-{label}-head.txt')
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
        log(text, end='')
        return new_total, unfinished

    def main(self):
        self.out.mkdir(parents=True, exist_ok=True)
        for f in self.out.iterdir():
            if f.suffix in ('.txt', '.log', '.md'):
                f.unlink()
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
