import Rhino.Geometry as rg
import math

LineUtils = None

class ConduitLookup(object):
    """
    Conduits trade size, inner/outer diameters, bend offset lookup, all preconverted to float
    Its a dictionary key = size as float
    """
    SIZES = [0.0, 0.5, 0.75, 1.0, 1.25, 1.5, 2.0, 2.5, 3.0, 3.5, 4.0, 6.0, 8.0]

    SPEC = {
        # trade: inner diameter (inches), outer diameter (inches), min_bend (inches), linear_section (inches)
        0.0:   {'trade': '0"', 'id': 0.0, 'od': 0.0, 'min_bend': 0.0, 'linear_section': 0.0}, #for debugging purposes
        0.5:   {'trade': '1/2"',     'id': 0.625,    'od': 0.71875,   'min_bend': 4.0,      'linear_section': 1.75},   # ID=5/8",       OD=23/32",    MinBend=4",       Linear section=1 3/4"
        0.75:  {'trade': '3/4"',     'id': 0.8125,   'od': 0.9375,    'min_bend': 5.4375,   'linear_section': 2.25},   # ID=13/16",     OD=15/16",    MinBend=5 7/16",  Linear section=2 1/4"
        1.0:   {'trade': '1"',       'id': 1.0625,   'od': 1.15625,   'min_bend': 7.0,      'linear_section': 2.25},   # ID=1 1/16",    OD=1 5/32",   MinBend=7",       Linear section=2 1/4"
        1.25:  {'trade': '1 1/4"',   'id': 1.3125,   'od': 1.5,       'min_bend': 8.8125,   'linear_section': 3.0},    # ID=1 5/16",    OD=1 1/2",    MinBend=8 13/16", Linear section=3"
        1.5:   {'trade': '1 1/2"',   'id': 1.625,    'od': 1.75,      'min_bend': 8.375,    'linear_section': 3.5},    # ID=1 5/8",     OD=1 3/4",    MinBend=8 3/8",   Linear section=3 1/2"
        2.0:   {'trade': '2"',       'id': 2.0625,   'od': 2.1875,    'min_bend': 9.25,     'linear_section': 4.0},    # ID=2 1/16",    OD=2 3/16",   MinBend=9 1/4",   Linear section=4"
        2.5:   {'trade': '2 1/2"',   'id': 2.71875,  'od': 2.875,     'min_bend': 13.90625, 'linear_section': 4.75},   # ID=2 23/32",   OD=2 7/8",    MinBend=13 29/32",Linear section=4 3/4"
        3.0:   {'trade': '3"',       'id': 3.34375,  'od': 3.5,       'min_bend': 16.46875, 'linear_section': 6.0},    # ID=3 11/32",   OD=3 1/2",    MinBend=16 15/32",Linear section=6"
        3.5:   {'trade': '3 1/2"',   'id': 3.84375,  'od': 4.0,       'min_bend': 19.8125,  'linear_section': 7.25},   # ID=3 27/32",   OD=4",        MinBend=19 13/16",Linear section=7 1/4"
        4.0:   {'trade': '4"',       'id': 4.34375,  'od': 4.5,       'min_bend': 21.5,     'linear_section': 8.5},    # ID=4 11/32",   OD=4 1/2",    MinBend=21 1/2",  Linear section=8 1/2"
        6.0:   {'trade': '6"',       'id': 6.0,      'od': 6.625,     'min_bend': 31.5,     'linear_section': 13.5},   # ID=6",         OD=6 5/8",    MinBend=31 1/2",  Linear section=13 1/2"
        8.0:   {'trade': '8"',       'id': 8.0,      'od': 8.96875,   'min_bend': 36.0,     'linear_section': 18.5},   # ID=8",         OD=8 31/32",  MinBend=36",      Linear section=18 1/2"
    }

    @staticmethod
    def _interpolate_conduit_specs(size):
        """
        Build and evaluate cubic splines for id, od, and min_bend
        across available sizes, returning inchified floats.
        """
        sizes = sorted(LineUtils.ConduitLookup.SPEC.keys())
        id_vals = [LineUtils.ConduitLookup.SPEC[s]['id'] for s in sizes]
        od_vals = [LineUtils.ConduitLookup.SPEC[s]['od'] for s in sizes]
        mb_vals = [LineUtils.ConduitLookup.SPEC[s]['min_bend'] for s in sizes]
        ls_vals = [LineUtils.ConduitLookup.SPEC[s]['linear_section'] for s in sizes]
        
        coeff_id = LineUtils.calculate_spline_coefficients(sizes, id_vals)
        coeff_od = LineUtils.calculate_spline_coefficients(sizes, od_vals)
        coeff_mb = LineUtils.calculate_spline_coefficients(sizes, mb_vals)
        coeff_ls = LineUtils.calculate_spline_coefficients(sizes, ls_vals)
        
        id_val = LineUtils.cubic_spline(sizes, coeff_id, size)
        od_val = LineUtils.cubic_spline(sizes, coeff_od, size)
        mb_val = LineUtils.cubic_spline(sizes, coeff_mb, size)
        ls_val = LineUtils.cubic_spline(sizes, coeff_ls, size)
        
        return {
            'trade': LineUtils.inchify(size),
            'id': LineUtils.inchify(id_val),
            'od': LineUtils.inchify(od_val),
            'min_bend': LineUtils.inchify(mb_val),
            'linear_section': LineUtils.inchify(ls_val)
        }

    @staticmethod
    def get_specs(size):
        #ensure size is float, default to 0.75
        try:
            sizef = float(size)
        except:
            sizef = 0.75
            
        if sizef not in LineUtils.ConduitLookup.SPEC:
            return LineUtils.ConduitLookup._interpolate_conduit_specs(sizef)
            
        specs = LineUtils.ConduitLookup.SPEC[sizef]
        return {
            'trade': LineUtils.inchify(sizef),
            'id': LineUtils.inchify(specs['id']),
            'od': LineUtils.inchify(specs['od']),
            'min_bend': LineUtils.inchify(specs['min_bend']),
            'linear_section': LineUtils.inchify(specs['linear_section'])
        }
    
    @staticmethod
    def classify_size(size):
        """
        Classify the input size:
        - 'lookedup' if float and exact match in SPEC
        - 'interpolated' if float but not in SPEC
        - 'invalid' if cannot parse as float
        """
        try:
            sizef = float(size)
        except (TypeError, ValueError):
            return 'invalid'
        if sizef in LineUtils.ConduitLookup.SPEC:
            return 'lookedup'
        return 'interpolated'


