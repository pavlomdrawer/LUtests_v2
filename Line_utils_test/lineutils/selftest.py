import Rhino.Geometry as rg
import Grasshopper as gh
import System
import math
import random
from collections import defaultdict

GLOBAL_TOL = 0.01

LineUtils = None

class SelfTest(object):
    """
    Lightweight, opt-in self-tests for LineUtils.

    Usage inside Grasshopper (IronPython 2.7):

        summary = LineUtils.SelfTest.run_parsing()
        # or
        summary = LineUtils.SelfTest.run_basic()
        summary = LineUtils.SelfTest.run_all()

    Each test case is small and is executed via LineUtils.run_with_timeout()
    so that a broken test cannot freeze Rhino.
    """

    # Default per-test timeout in seconds
    DEFAULT_TIMEOUT = 0.25

    # -------------------
    # Small helpers
    # -------------------

    @staticmethod
    def _almost_equal(a, b, eps = GLOBAL_TOL):
        """
        Numeric comparison with absolute tolerance.
        Falls back to == if types do not support subtraction.
        """
        try:
            return abs(a - b) <= eps
        except TypeError:
            return a == b

    @staticmethod
    def _almost_equal_point(p, q, eps = GLOBAL_TOL):
        """
        Compare two rg.Point3d with tolerance.
        """
        return (abs(p.X - q.X) <= eps and
                abs(p.Y - q.Y) <= eps and
                abs(p.Z - q.Z) <= eps)

    @staticmethod
    def _resolve_target(name):
        """
        Resolve a string like 'parse_measure' or
        'ConduitLookup.classify_size' to a callable.
        """
        if '.' in name:
            cls_name, meth_name = name.split('.', 1)
            cls = getattr(LineUtils, cls_name)
            return getattr(cls, meth_name)
        return getattr(LineUtils, name)

    @staticmethod
    def _run_case(case, timeout_sec):
        """
        Execute a single test case with timeout.
        case dict keys:
            - name    : human-readable name
            - target  : function name or 'Class.method'
            - args    : tuple of positional args
            - kwargs  : dict of keyword args (optional)
            - expected: expected result
            - kind    : 'float', 'point', 'sequence', or 'exact'
        """
        fn = LineUtils.SelfTest._resolve_target(case['target'])
        args = case.get('args') or ()
        kwargs = case.get('kwargs') or {}
        status = 'ok'
        result = None
        err_str = None

        def _call():
            return fn(*args, **kwargs)

        # Make sure exceptions do not bubble out and kill the component
        try:
            result = LineUtils.run_with_timeout(_call, timeout_sec)
        except Exception as e:
            status = 'error'
            err_str = repr(e)
            result = None
        else:
            if result == "expired":
                status = 'timeout'
            else:
                expected = case.get('expected')
                kind = case.get('kind', 'exact')

                if kind == 'float':
                    if not LineUtils.SelfTest._almost_equal(result, expected):
                        status = 'mismatch'

                elif kind == 'point':
                    if not LineUtils.SelfTest._almost_equal_point(result, expected):
                        status = 'mismatch'

                elif kind == 'sequence':
                    exp = expected
                    if len(result) != len(exp):
                        status = 'mismatch'
                    else:
                        for a, b in zip(result, exp):
                            # Handle numeric sub-items approximately,
                            # other values exactly
                            if isinstance(a, float) or isinstance(b, float):
                                if not LineUtils.SelfTest._almost_equal(a, b):
                                    status = 'mismatch'
                                    break
                            else:
                                if a != b:
                                    status = 'mismatch'
                                    break

                else:  # 'exact' fallback
                    if result != expected:
                        status = 'mismatch'

        return {
            'name': case.get('name'),
            'target': case.get('target'),
            'status': status,       # 'ok', 'mismatch', 'timeout', 'error'
            'result': result,
            'expected': case.get('expected'),
            'error': err_str,
        }

    @staticmethod
    def _run_group(group_name, cases, timeout_sec, verbose):
        """
        Run a list of cases and return a summary dict.
        """
        if timeout_sec is None:
            timeout_sec = LineUtils.SelfTest.DEFAULT_TIMEOUT

        results = []
        passed = 0
        failed = 0
        timeouts = 0
        errors = 0

        for case in cases:
            r = LineUtils.SelfTest._run_case(case, timeout_sec)
            results.append(r)
            st = r['status']

            if st == 'ok':
                passed += 1
            else:
                failed += 1
                if st == 'timeout':
                    timeouts += 1
                if st == 'error':
                    errors += 1

            if verbose:
                print('[%s] %-30s %r -> %r' %
                      (st.upper(), case.get('name'), case.get('args'), r['result']))

        return {
            'group': group_name,
            'total': len(cases),
            'passed': passed,
            'failed': failed,
            'timeouts': timeouts,
            'errors': errors,
            'cases': results,
        }

    # -------------------
    # Test case builders
    # -------------------

    @staticmethod
    def _parsing_cases():
        """
        Tests for parse_measure / parse_scale.

        To add more cases later, just append more add(...) calls here.
        """
        cases = []

        def add(name, target, args, expected, kind):
            cases.append({
                'name': name,
                'target': target,
                'args': tuple(args),
                'expected': expected,
                'kind': kind,
            })

        # --- parse_measure ---

        add('parse_measure_zero',
            'parse_measure',
            ('0',),
            0.0,
            'float')

        add('parse_measure_feet',
            'parse_measure',
            ("6'",),
            72.0,
            'float')

        add('parse_measure_neg_feet',
            'parse_measure',
            ("-6'",),
            -72.0,
            'float')

        add('parse_measure_inches',
            'parse_measure',
            ('12"',),
            12.0,
            'float')

        add('parse_measure_fraction',
            'parse_measure',
            ('3/4"',),
            0.75,
            'float')

        add('parse_measure_mixed',
            'parse_measure',
            ('1 1/4"',),
            1.25,
            'float')

        add('parse_measure_feet_mixed',
            'parse_measure',
            ("2'-1 1/8\"",),
            25.125,
            'float')

        add('parse_measure_negative',
            'parse_measure',
            ('-3/8"',),
            -0.375,
            'float')

        add('parse_measure_error',
            'parse_measure',
            ('foo',),
            "Can't parse measure 'foo'",
            'exact')

        # --- parse_scale ---

        add('parse_scale_simple',
            'parse_scale',
            ('1" = 1\'-0"',),
            12.0,
            'float')

        add('parse_scale_halfinch',
            'parse_scale',
            ('1/2" = 1\'-0"',),
            24.0,
            'float')

        add('parse_scale_three_eighth',
            'parse_scale',
            ('3/8" = 1\'-0"',),
            32.0,
            'float')

        add('parse_scale_mixed',
            'parse_scale',
            ('1 1/2" = 2\'-0"',),
            16.0,
            'float')

        add('parse_scale_nospace',
            'parse_scale',
            ('1/8"=1\'-0"',),
            96.0,
            'float')

        add('parse_scale_words',
            'parse_scale',
            ('1/8 in = 1 ft',),
            96.0,
            'float')

        add('parse_scale_single',
            'parse_scale',
            ('3/8"',),
            0.375,
            'float')

        add('parse_scale_no_measures',
            'parse_scale',
            ('abc',),
            "No measures found in 'abc'",
            'exact')

        return cases

    @staticmethod
    def _basic_numeric_cases():
        """
        Small pure-numeric helpers that are easy and safe to test.
        """
        cases = []

        def add(name, target, args, expected, kind):
            cases.append({
                'name': name,
                'target': target,
                'args': tuple(args),
                'expected': expected,
                'kind': kind,
            })

        # --- inchify ---

        add('inchify_zero',
            'inchify',
            (0.0,),
            0.0,
            'float')

        add('inchify_exact_half',
            'inchify',
            (1.5,),
            1.5,
            'float')

        add('inchify_round_up',
            'inchify',
            (1.499,),
            1.5,
            'float')

        add('inchify_third',
            'inchify',
            (1.333,),
            1.34375,
            'float')

        add('inchify_almost_int',
            'inchify',
            (2.999,),
            3.0,
            'float')

        # --- filter_unique_nonzero ---

        add('filter_unique_nonzero_basic',
            'filter_unique_nonzero',
            ([0.0, 0.011, 0.0110001, 0.03, -0.009], 0.01),
            [0.011, 0.03],
            'sequence')

        # --- largest_by_abs ---

        add('largest_by_abs',
            'largest_by_abs',
            ([-1.0, 2.0, -3.0],),
            -3.0,
            'float')

        add('largest_by_abs_empty',
            'largest_by_abs',
            ([],),
            0.0,
            'float')

        # --- consecutive_pairs ---

        add('consecutive_pairs_basic',
            'consecutive_pairs',
            ([1, 2, 3],),
            [[1, 2], [2, 3]],
            'sequence')

        add('consecutive_pairs_short',
            'consecutive_pairs',
            ([1],),
            [],
            'sequence')

        # --- weighted_average ---

        add('weighted_average_basic',
            'weighted_average',
            ([1.0, 2.0, 3.0], [1.0, 1.0, 2.0]),
            2.25,
            'float')

        add('weighted_average_zero_wsum',
            'weighted_average',
            ([1.0, 2.0], [0.0, 0.0]),
            0.0,
            'float')

        add('weighted_average_mismatch',
            'weighted_average',
            ([1.0, 2.0], [1.0],),
            0.0,
            'float')

        # --- distance_l1 ---

        add('distance_l1_zero',
            'distance_l1',
            (((0.0, 0.0), (0.0, 0.0))),
            0.0,
            'float')

        add('distance_l1_axis',
            'distance_l1',
            (((0.0, 0.0), (3.0, 4.0))),
            7.0,
            'float')

        add('distance_l1_symmetry',
            'distance_l1',
            (((5.0, -2.0), (-1.0, 1.0))),
            9.0,
            'float')

        # --- angle (polar) ---

        add('angle_east',
            'angle',
            (((0.0, 0.0), (1.0, 0.0))),
            0.0,
            'float')

        add('angle_north',
            'angle',
            (((0.0, 0.0), (0.0, 1.0))),
            math.pi * 0.5,
            'float')

        add('angle_west',
            'angle',
            (((0.0, 0.0), (-1.0, 0.0))),
            math.pi,
            'float')

        add('angle_south',
            'angle',
            (((0.0, 0.0), (0.0, -1.0))),
            math.pi * 1.5,
            'float')

        add('angle_diag',
            'angle',
            (((0.0, 0.0), (1.0, 1.0))),
            math.pi * 0.25,
            'float')

        return cases


    @staticmethod
    def _geometry_cases():
        """
        Simple geometry tests that only touch very cheap functions:
        orientation_of_line, get_position, get_domain, domains_overlap,
        and some small helpers around them.
        """
        cases = []

        def add(name, target, args, expected, kind):
            cases.append({
                'name': name,
                'target': target,
                'args': tuple(args),
                'expected': expected,
                'kind': kind,
            })

        # Vertical line: X constant, Y varies
        vline = rg.Line(rg.Point3d(5, 0, 0), rg.Point3d(5, 10, 0))
        # Horizontal line: Y constant, X varies
        hline = rg.Line(rg.Point3d(0, 3, 0), rg.Point3d(10, 3, 0))
        # Non-orthogonal
        dline = rg.Line(rg.Point3d(0, 0, 0), rg.Point3d(10, 10, 0))

        # --- orientation_of_line ---

        add('orientation_vertical',
            'orientation_of_line',
            (vline,),
            LineUtils.Orientation.VERTICAL,
            'exact')

        add('orientation_horizontal',
            'orientation_of_line',
            (hline,),
            LineUtils.Orientation.HORIZONTAL,
            'exact')

        add('orientation_nonorth',
            'orientation_of_line',
            (dline,),
            LineUtils.Orientation.NONORTH,
            'exact')

        # --- get_position ---

        add('position_vertical',
            'get_position',
            (vline, LineUtils.Orientation.VERTICAL),
            5.0,
            'float')

        add('position_horizontal',
            'get_position',
            (hline, LineUtils.Orientation.HORIZONTAL),
            3.0,
            'float')

        # --- get_domain ---

        add('domain_vertical',
            'get_domain',
            (vline, LineUtils.Orientation.VERTICAL),
            [0.0, 10.0],
            'sequence')

        add('domain_horizontal',
            'get_domain',
            (hline, LineUtils.Orientation.HORIZONTAL),
            [0.0, 10.0],
            'sequence')

        # --- domains_overlap ---

        add('domains_overlap_true',
            'domains_overlap',
            ([0.0, 10.0], [9.0, 20.0]),
            True,
            'exact')

        add('domains_overlap_false',
            'domains_overlap',
            ([0.0, 10.0], [10.1, 20.0]),
            False,
            'exact')

        add('domains_overlap_touch',
            'domains_overlap',
            ([0.0, 10.0], [10.0, 20.0]),
            True,
            'exact')

        add('domains_overlap_negative',
            'domains_overlap',
            ([-5.0, -1.0], [-3.0, 2.0]),
            True,
            'exact')

        # --- is_vertical / is_horizontal ---

        add('is_vertical_true',
            'is_vertical',
            (vline,),
            True,
            'exact')

        add('is_vertical_false',
            'is_vertical',
            (hline,),
            False,
            'exact')

        add('is_horizontal_true',
            'is_horizontal',
            (hline,),
            True,
            'exact')

        add('is_horizontal_false',
            'is_horizontal',
            (vline,),
            False,
            'exact')

        # --- filter_same_direction / filter_by_flag ---

        ref = rg.Line(rg.Point3d(0, 0, 0), rg.Point3d(10, 0, 0))
        par = rg.Line(rg.Point3d(5, 5, 0), rg.Point3d(15, 5, 0))    # parallel
        anti = rg.Line(rg.Point3d(5, 5, 0), rg.Point3d(-5, 5, 0))   # anti-parallel
        perp = rg.Line(rg.Point3d(0, 0, 0), rg.Point3d(0, 10, 0))   # perpendicular

        add('filter_same_direction_basic',
            'filter_same_direction',
            (ref, [par, anti, perp]),
            [True, True, False],
            'sequence')

        add('filter_by_flag_basic',
            'filter_by_flag',
            (['a', 'b', 'c'], [True, False, True]),
            ['a', 'c'],
            'sequence')

        add('filter_by_flag_all_false',
            'filter_by_flag',
            (['a', 'b', 'c'], [False, False, False]),
            [],
            'sequence')

        # --- _snap01 / _in01 ---

        add('snap01_below_zero',
            '_snap01',
            (-0.1, 0.001),
            0.0,
            'float')

        add('snap01_above_one',
            '_snap01',
            (1.001, 0.001),
            1.0,
            'float')

        add('snap01_inside',
            '_snap01',
            (0.5, 0.001),
            0.5,
            'float')

        add('in01_inside_exclusive',
            '_in01',
            (0.5, False, 0.001),
            True,
            'exact')

        add('in01_outside_exclusive',
            '_in01',
            (0.0, False, 0.001),
            False,
            'exact')

        add('in01_endpoint_inclusive_low',
            '_in01',
            (0.0, True, 0.001),
            True,
            'exact')

        add('in01_endpoint_inclusive_high',
            '_in01',
            (1.0, True, 0.001),
            True,
            'exact')

        return cases

    # -------------------
    # Public entry points
    # -------------------

    @staticmethod
    def run_parsing(timeout_sec=None, verbose=True):
        """
        Run only parsing-related tests (parse_measure / parse_scale).
        """
        cases = LineUtils.SelfTest._parsing_cases()
        return LineUtils.SelfTest._run_group('parsing', cases, timeout_sec, verbose)

    @staticmethod
    def run_basic(timeout_sec=None, verbose=True):
        """
        Run parsing + basic numeric + simple geometry tests.
        Cheap and safe to run often.
        """
        cases = []
        cases.extend(LineUtils.SelfTest._parsing_cases())
        cases.extend(LineUtils.SelfTest._basic_numeric_cases())
        cases.extend(LineUtils.SelfTest._geometry_cases())
        return LineUtils.SelfTest._run_group('basic', cases, timeout_sec, verbose)

    @staticmethod
    def run_all(timeout_sec=None, verbose=True):
        """
        Alias for run_basic for now.
        Kept separate so you can add heavier tests later.
        """
        return LineUtils.SelfTest.run_basic(timeout_sec, verbose)


