from fractions import Fraction as Q
from math import gcd, lcm, log
from pathlib import Path
import argparse
import json
import sys
from symmetric_pade_audit import poised_period_coordinates
from zeta_enclosure import euler_maclaurin_zeta_interval


def main():
    sys.set_int_max_str_digits(200000)
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    interval = euler_maclaurin_zeta_interval(5, 96)
    reports = []
    for n in (2, 4, 8, 12, 20):
        maximum = (5 * (n + 1) - 2 - n % 2) // 2
        coordinates = []
        for m in range(maximum + 1):
            values = poised_period_coordinates(2, n, m)
            d = lcm(*(q.denominator for q in values))
            integer = [int(d * q) for q in values]
            content = gcd(*integer)
            coordinates.append([q // content for q in integer])
        candidates, seen, best = [], set(), None
        for i in range(maximum + 1):
            for j in range(i + 1, maximum + 1):
                first, second = coordinates[i], coordinates[j]
                h = gcd(first[0], second[0])
                if not h:
                    continue
                weights = [second[0] // h, -first[0] // h]
                assert weights[0] * first[0] + weights[1] * second[0] == 0
                a = weights[0] * first[1] + weights[1] * second[1]
                b = weights[0] * first[2] + weights[1] * second[2]
                if not a:
                    continue
                content = gcd(a, b)
                a, b = a // content, b // content
                if a < 0:
                    a, b = -a, -b
                    weights = [-w for w in weights]
                key = (a, b)
                if key in seen:
                    continue
                seen.add(key)
                zlo, zhi = interval
                lo, hi = a * zlo + b, a * zhi + b
                assert lo * hi > 0
                lower, upper = min(abs(lo), abs(hi)), max(abs(lo), abs(hi))
                record = {'profile': [i, j], 'primitive_target_coefficient': str(a),
                          'primitive_constant': str(b),
                          'primitive_combination': [str(x) for x in weights],
                          'output_content': str(content),
                          'combination_one_sign': all(w >= 0 for w in weights) or
                                                  all(w <= 0 for w in weights)}
                candidates.append(record)
                if best is None or upper < best[0]:
                    best = (upper, lower, record)
        assert best is not None
        upper, lower, record = best
        certified = True
        for candidate in candidates:
            if candidate is record:
                continue
            a, b = int(candidate['primitive_target_coefficient']), int(candidate['primitive_constant'])
            lo, hi = a * interval[0] + b, a * interval[1] + b
            certified = certified and upper < min(abs(lo), abs(hi))
        assert certified
        result = {'weight': 5, 'index': n, 'maximum_block_length': maximum,
                  'distinct_nonzero_target_candidates': len(candidates),
                  'best_candidate': record,
                  'best_primitive_abs_interval': [str(lower), str(upper)],
                  'best_abs_lt_one': upper < 1,
                  'best_certified_among_enumerated_candidates': certified,
                  'log_best_primitive_abs_per_index':
                      (log((lower + upper).numerator) - log((lower + upper).denominator) - log(2)) / n,
                  'candidates': candidates}
        reports.append(result)
        print('weight 5', n, len(candidates), 'best profile', record['profile'],
              'below one', upper < 1,
              'log/n', round(result['log_best_primitive_abs_per_index'], 6), flush=True)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps({
            'scope': 'Finite exhaustive two-kernel profile search at five indices. '
                     'No asymptotic optimality or irrationality conclusion.',
            'rows': reports}, indent=2), encoding='utf-8')


if __name__ == '__main__':
    main()
