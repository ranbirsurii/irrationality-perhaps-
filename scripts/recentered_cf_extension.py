"""Extend exact recentered certificates without extrapolating their rates."""
import json
from fractions import Fraction
from pathlib import Path
from recentered_cf_root import check, rational_controls


def main():
    profiles = [(7, 24), (7, 28), (13, 12), (15, 14)]
    ceilings = [Fraction(6, 10**92), Fraction(2, 10**106),
                Fraction(2, 10**79), Fraction(9, 10**101)]
    records = []
    for (s, n), ceiling in zip(profiles, ceilings):
        record = check(s, n)
        assert Fraction(record['certified_common_majorant']) < ceiling
        record['exact_rational_ceiling'] = str(ceiling)
        records.append(record)
        print(s, n, 'exact common bound <', ceiling, flush=True)
    output = {'cases': records,
              'rational_negative_controls': rational_controls(),
              'uniform_decay_proved': False}
    target = Path(__file__).resolve().parents[1] / 'notes/recentered-cf-extension.json'
    target.write_text(json.dumps(output, indent=2))
    print('Four profiles and twelve signed-prefix certificates passed.')


if __name__ == '__main__':
    main()
