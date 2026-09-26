from collections import defaultdict
import re

def parse_divan_output(text):
    results = {}
    current_group = None

    # Match benchmark row lines
    row_re = re.compile(
        r"""^[│╰├ ]*[├╰]─\s*
            (?P<case>.+?)\s+
            (?P<fastest_val>[\d.]+)\s+(?P<fastest_unit>\S+)\s*│\s*
            (?P<slowest_val>[\d.]+)\s+(?P<slowest_unit>\S+)\s*│\s*
            (?P<median_val>[\d.]+)\s+(?P<median_unit>\S+)\s*│\s*
            (?P<mean_val>[\d.]+)\s+(?P<mean_unit>\S+)\s*│\s*
            (?P<samples>\d+)\s*│\s*
            (?P<iters>\d+)
        """,
        re.VERBOSE
    )
    # Match group header line
    group_re = re.compile(
        r"^[│╰├ ]*[├╰]─\s+([^\s│]+)\s+│"
    )
    header_re = re.compile(
        r"""^
        \s*?([A-Za-z0-9_]+)
        \s+fastest\s+│\s*slowest\s+│\s*median\s+│\s*mean\s+│\s*samples\s+│\s*iters
        """,
        re.VERBOSE
    )

    lines = text.strip().splitlines()

    for line in lines:
        if '│' not in line:
            continue

        group_match = group_re.match(line)
        if group_match and '(' not in line:
            current_group = group_match.group(1).strip()
            continue

        header_match = header_re.match(line)
        if header_match:
            current_group = header_match.group(1).strip()

        row_match = row_re.match(line)
        if row_match:
            (case, fastest_val, fastest_unit,
             slowest_val, slowest_unit,
             median_val, median_unit,
             mean_val, mean_unit,
             samples, iters) = row_match.groups()

            def to_ns(val, unit):
                scale = {'ns': 1, 'µs': 1e3, 'us': 1e3, 'ms': 1e6, 's': 1e9}
                return float(val) * scale[unit]

            results[(current_group, case)] = {
                'fastest_ns': to_ns(fastest_val, fastest_unit),
                'slowest_ns': to_ns(slowest_val, slowest_unit),
                'median_ns': to_ns(median_val, median_unit),
                'mean_ns': to_ns(mean_val, mean_unit),
                'samples': int(samples),
                'iters': int(iters),
            }
    return results

def average_fields(data_sets):
    count = len(data_sets)
    averaged = {}

    for (key, _) in data_sets[0].items():
        totals = defaultdict(int)
        avg = data_sets[0][key]
        ns_keys = [k for k in data_sets[0][key] if k.endswith('_ns')]

        # Find all *_ns fields to average
        for i in range(count):
            for ns_key in ns_keys:
                totals[ns_key] += data_sets[i][key][ns_key]

        for ns_key in ns_keys:
            avg[ns_key] = totals[ns_key] / count

        averaged[key] = avg

    return averaged

def compare_fields(base, other, field_name):
    results = {}
    for (key, base_record) in base.items():
        if field_name in base_record:
            base_val = base_record[field_name]
            if key not in other:
                continue
            other_val = other[key][field_name]
            diff = other_val - base_val
            results[key] = {
                'base': base_val,
                'other': other_val,
                'diff': diff,
                'pct': diff / base_val,
            }
    return results

def case_sort_key(case):
    try:
        return (0, float(case))  # numeric values come first
    except (ValueError, TypeError):
        return (1, str(case))    # non-numeric values come after, sorted as strings

def render_divan_table(data):
    # Group and sort
    grouped = defaultdict(list)
    for (group, case), stats in data.items():
        grouped[group].append((case, stats))
    for group in grouped:
        grouped[group].sort(key=lambda item: case_sort_key(item[0]))

    if not grouped:
        return "(no cases)"
    (_, first_record) = next(iter(grouped.values()))[0]
    lines = []

    # Header
    if 'samples' in first_record:
        lines.append("                                  fastest  │      slowest │       median │         mean │ samples│ iters")
    elif 'base' in first_record:
        lines.append("                                     base  │        other │       change │      percent │")
    else:
        lines.append("                                  fastest  │      slowest │       median │         mean │")

    # Content
    for group in grouped.keys():
        lines.append(f"├─ {group:<32}        │{'':14}│{'':14}│{'':14}│{'':8}│")
        group_items = grouped[group]

        for i, (case, stats) in enumerate(group_items):
            prefix = "│  ╰─" if i == len(group_items) - 1 else "│  ├─"

            if 'base' in stats:
                base = format_ns(stats['base'])
                other = format_ns(stats['other'])
                diff = format_ns(stats['diff'])
                pct = colorize_percentage(stats['pct'])

                line = f"{prefix} {case:<23}{base:>13} │{other:>13} │{diff:>13} │{pct:>13} │"

            else:
                fastest = format_ns(stats['fastest_ns'])
                slowest = format_ns(stats['slowest_ns'])
                median = format_ns(stats['median_ns'])
                mean   = format_ns(stats['mean_ns'])

                if 'samples' in stats:
                    line = f"{prefix} {case:<23}{fastest:>13} │{slowest:>13} │{median:>13} │{mean:>13} │{stats['samples']:>7} │{stats['iters']:>6}"
                else:
                    line = f"{prefix} {case:<23}{fastest:>13} │{slowest:>13} │{median:>13} │{mean:>13} │"

            lines.append(line)

    return "\n".join(lines)

def colorize_percentage(val: float) -> str:
    if val < -0.05:
        color = "\033[32m"  # green
    elif val > 0.05:
        color = "\033[31m"  # red
    else:
        color = "\033[30m"  # black
    reset = "\033[0m"
    return f"{color}{val:10.2%}{reset}"

def format_ns(ns):
    abs_ns = abs(ns)
    if abs_ns > 1e9:
        return f"{ns/1e9:.2f} s"
    if abs_ns > 1e6:
        return f"{ns/1e6:.2f} ms"
    if abs_ns > 1e3:
        return f"{ns/1e3:.2f} µs"
    return f"{ns:.0f} ns"
