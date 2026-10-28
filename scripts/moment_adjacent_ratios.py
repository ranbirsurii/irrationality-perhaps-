"""Exact adjacent-even ratios of complete moment bounds; no extrapolation."""
from fractions import Fraction as Q
from pathlib import Path
import json
from moment_metric_reduction import construct


def main():
    rows = []
    for r in (3, 4, 5):
        previous = None
        for n in range(2*r, 2*r+18, 2):
            case = construct(r, n)
            value = max(Q(f['moment_bound_squared']) for f in case['forms'])
            if previous is not None:
                ratio = value/previous
                rows.append({'weight':2*r+1,'index':n,'ratio':str(ratio),
                             'below_one':ratio < 1})
            previous = value
    assert all(Q(row['ratio']) < Q(1,100000) for row in rows)
    root = Path(__file__).resolve().parents[1]
    (root/'notes/moment-adjacent-ratios.json').write_text(json.dumps({
        'cases':rows,'uniform_contraction_proved':False},indent=2))
    print(len(rows), 'exact tested ratios below 1/100000; no all-index assertion')


if __name__ == '__main__':
    main()
