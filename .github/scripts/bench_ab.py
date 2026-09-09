#!/usr/bin/env python3
"""A/B benchmark of two commits on the same machine.

Builds the bench binaries for BASE and HEAD once each (separate target dirs),
then runs them for ROUNDS rounds, alternating which side goes first and
pinning every run to one core.  As soon as both sides of a bench have run in
a round, its compare table (per-round divan medians averaged over the rounds
finished so far, via benches/divan_fmt.py) is printed and saved as
$BENCH_OUT/cmp-<bench>.txt; $BENCH_OUT/compare.txt, the concatenation, is
rewritten after every completed round.  Progress lines go to
$BENCH_OUT/progress.txt.  pr_comment.py posts compare.txt to the PR.

usage: bench_ab.py <base-sha> <head-sha>

env:  BENCH_ROUNDS       rounds per side                (default 3)
      BENCHES            space separated bench targets  (default: the set used in BENCH_BUGFIXES)
      BENCH_CPU          core to pin to                 (default 3)
      BENCH_OUT          output directory               (default ./bench-out)
      DIVAN_SAMPLE_COUNT sample count for benches that do not set their own (default 40)
      CARGO_TARGET_DIR   parent of the two per-side target dirs (default ./target)
"""
import json, os, re, subprocess, sys, time, tomllib
from pathlib import Path

DEFAULT_BENCHES = 'shakespeare cities sparse_keys binary_keys superdense_keys act_paths zipper_head_owned product_zipper'


def log(*a, **kw):
    print(*a, flush=True, **kw)


def git(*args, cwd=None):
    return subprocess.run(['git', *args], cwd=cwd, check=True, text=True, capture_output=True).stdout.strip()


class Bench:
    def __init__(self, base, head):
        self.repo = Path.cwd()
        self.base_sha, self.head_sha = base, head
        self.rounds = int(os.environ.get('BENCH_ROUNDS', 3))
        self.benches = os.environ.get('BENCHES', DEFAULT_BENCHES).split()
        self.cpu = os.environ.get('BENCH_CPU', '3')
        self.out = Path(os.environ.get('BENCH_OUT', self.repo / 'bench-out')).resolve()
        self.target = Path(os.environ.get('CARGO_TARGET_DIR', self.repo / 'target')).resolve()
        self.base_src = self.out / 'src-base'
        self.bins = {}
        os.environ.setdefault('DIVAN_SAMPLE_COUNT', '40')
        sys.path.insert(0, str(self.repo / 'benches'))
        import divan_fmt
        self.fmt = divan_fmt

    def progress(self, msg):
        with open(self.out / 'progress.txt', 'a') as f:
            f.write(f'{time.strftime("%H:%M:%S", time.gmtime())} {msg}\n')

    def short(self, sha):
        return git('rev-parse', '--short', sha, cwd=self.repo)

    def cleanup(self):
        subprocess.run(['git', 'worktree', 'remove', '--force', str(self.base_src)], cwd=self.repo,
                       capture_output=True)

    def required_features(self, src):
        """Features the requested benches declare via required-features, limited to those the tree has."""
        t = tomllib.loads((src / 'Cargo.toml').read_text())
        have = set(t.get('features', {}))
        need = set()
        for b in t.get('bench', []):
            if b.get('name') in self.benches:
                need |= set(b.get('required-features', []))
        return sorted(need & have)

    def build_side(self, side, src):
        feats = self.required_features(src)
        target = self.target / f'ab-{side}'
        log(f'== building {side} ({self.short(git("rev-parse", "HEAD", cwd=src))}) into {target}'
            + (f' with features {",".join(feats)}' if feats else ''))
        cmd = ['cargo', 'bench', '--no-run', '--message-format=json', '--target-dir', str(target)]
        for b in self.benches:
            cmd += ['--bench', b]
        if feats:
            cmd += ['--features', ','.join(feats)]
        with open(self.out / f'build-{side}.log', 'w') as err:
            p = subprocess.run(cmd, cwd=src, stdout=subprocess.PIPE, stderr=err, text=True)
        if p.returncode:
            sys.exit(f'build of {side} failed:\n' + tail(self.out / f'build-{side}.log'))
        exes = {}
        for line in p.stdout.splitlines():
            m = json.loads(line)
            if m.get('reason') == 'compiler-artifact' and m.get('executable') and 'bench' in m['target']['kind']:
                exes[m['target']['name']] = m['executable']
        (self.out / f'bins-{side}.txt').write_text(''.join(f'{k} {v}\n' for k, v in exes.items()))
        missing = [b for b in self.benches if b not in exes]
        if missing:
            sys.exit(f'no executable for bench(es) {missing} on {side}')
        self.bins[side] = exes

    def run(self, side, bench, rnd):
        t0 = time.time()
        with open(self.out / f'{side}-{bench}-r{rnd}.txt', 'w') as out, open(self.out / f'run-{side}.log', 'a') as err:
            subprocess.run(['taskset', '-c', self.cpu, self.bins[side][bench], '--bench'],
                           cwd=self.repo, stdout=out, stderr=err, check=True)
        self.progress(f'round {rnd}/{self.rounds} {bench} {side} {time.time() - t0:.0f}s')

    def compare_bench(self, bench, rounds_so_far):
        """Average each side's rounds so far, compare medians, save and print the table."""
        avg = {}
        for side in ('base', 'head'):
            files = sorted(self.out.glob(f'{side}-{bench}-r*.txt'))
            data = [self.fmt.parse_divan_output(f.read_text()) for f in files]
            avg[side] = self.fmt.average_fields(data)
            (self.out / f'{side}-{bench}-avg.txt').write_text(self.fmt.render_divan_table(avg[side]) + '\n')
        table = self.fmt.render_divan_table(self.fmt.compare_fields(avg['base'], avg['head'], 'median_ns'))
        table = re.sub(r'\x1b\[[0-9;]*m', '', table)
        text = (f'{bench}  (base {self.short(self.base_sha)}  head {self.short(self.head_sha)}'
                f'  rounds {rounds_so_far}  median ns)\n{table}\n\n')
        (self.out / f'cmp-{bench}.txt').write_text(text)
        log(text, end='')

    def compare_rounds(self):
        tmp = self.out / 'compare.tmp'
        tmp.write_text(''.join((self.out / f'cmp-{b}.txt').read_text() for b in self.benches))
        tmp.rename(self.out / 'compare.txt')

    def main(self):
        self.out.mkdir(parents=True, exist_ok=True)
        for f in self.out.iterdir():
            if f.suffix in ('.txt', '.log', '.json'):
                f.unlink()
        self.cleanup()
        try:
            git('worktree', 'add', '--detach', str(self.base_src), self.base_sha, cwd=self.repo)
            self.progress(f'plan: {self.rounds} round(s) x base/head x [{" ".join(self.benches)}], core {self.cpu}')
            self.progress(f'building base {self.short(self.base_sha)}')
            self.build_side('base', self.base_src)
            self.progress(f'building head {self.short(self.head_sha)}')
            self.build_side('head', self.repo)
            for rnd in range(1, self.rounds + 1):
                order = ('base', 'head') if rnd % 2 else ('head', 'base')
                for bench in self.benches:
                    for side in order:
                        log(f'== round {rnd}/{self.rounds} {bench} {side}')
                        self.run(side, bench, rnd)
                    self.compare_bench(bench, rnd)
                self.compare_rounds()
                self.progress(f'round {rnd}/{self.rounds} done, compare.txt refreshed')
            log(f'== final compare over {self.rounds} round(s): {self.out / "compare.txt"}')
        finally:
            self.cleanup()


def tail(path, n=30):
    return '\n'.join(Path(path).read_text().splitlines()[-n:])


if __name__ == '__main__':
    if len(sys.argv) != 3:
        sys.exit('usage: bench_ab.py <base-sha> <head-sha>')
    Bench(sys.argv[1], sys.argv[2]).main()
