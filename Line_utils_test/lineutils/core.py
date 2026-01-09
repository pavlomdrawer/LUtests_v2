import Rhino.Geometry as rg
import math
import copy
import inspect
import itertools
import time
import System
import re
import zipfile
import xml.etree.ElementTree as ET
import Rhino.Collections as rc
import Grasshopper as gh
from collections import defaultdict
import random

version = 0.83

try:
    ghenv.Component.Message = "{0:.2f}".format(version) + " LineUtils library"
except:
    pass #working on imported lib

GLOBAL_TOL = 0.01 #need to fine tune, maybe 0.001 is better
ANG_EPS = 1e-6   # for dot-products
defaultpath = gh.Kernel.Data.GH_Path(0)
unitX = rg.Vector3d(1, 0, 0)
unitY = rg.Vector3d(0, 1, 0)
unitZ = rg.Vector3d(0, 0, 1) 

class LineUtils(object):
    VERSION = version
    
    class Orientation(object):
        """
        Simple enumeration for line orientation.
        """
        VERTICAL = "vertical"
        HORIZONTAL = "horizontal"
        NONORTH = "nonorth"


    class AngleLookup(object):
        """
        Acceptable bend angles lookup
        """
        ANGLES = [5.0, 10.0, 15.0, 22.5, 30.0, 45.0, 90.0]

        SPEC = {
            #angles in radians
            5.0:  math.pi * 5.0  / 180.0,
            10.0: math.pi * 10.0 / 180.0,
            15.0: math.pi * 15.0 / 180.0,
            22.5: math.pi * 22.5 / 180.0,
            30.0: math.pi * 30.0 / 180.0,
            45.0: math.pi * 45.0 / 180.0,
            90.0: math.pi * 90.0 / 180.0,
        }

        @staticmethod
        def get_specs(deg):
            return LineUtils.AngleLookup.SPEC[deg]


    @staticmethod
    def prefilter_polyline_tree(polylinesbatch, tol = GLOBAL_TOL):
        """
        takes a tree of polylines as input and tries to realign all axis of all
        polilines to simplify and straighten them, resnaps all polyline points
        to reconstructed axis
        """
        try:
            rawlines = []
            
            for polylines_ in polylinesbatch.Branches:
                for poly in list(polylines_):
                    #DO NOT merge collinear, it breaks the tolerances
                    #poly.MergeColinearSegments(GLOBAL_TOL, False)
                    if poly:
                        for i in range(poly.SegmentCount):
                            rawlines.append(poly.SegmentAt(i))
            
            resplit = LineUtils.split_lines_at_intersections(rawlines, tol, False)
            deduped = LineUtils.dedupe_lines(resplit, tol)
            sweeped = LineUtils.build_collinear_polylines_sweep(deduped, tol, 1.0)
            axised = [LineUtils.fit_weighted_line_from_polyline(sweep) for sweep in sweeped]
            resnapped = LineUtils.extend_lines_to_touch_others(axised)
            
            polylinesnapped = gh.DataTree[System.Object]()
            
            for path in polylinesbatch.Paths:
                polydata = list(polylinesbatch.Branch(path))
                polyresnapped = LineUtils.snap_polylines_points_to_lines(polydata, resnapped, keepempty = True)
                for p in polyresnapped:
                    if p:
                        p.MergeColinearSegments(tol, False)
                polylinesnapped.AddRange(polyresnapped, path)
            
            return polylinesnapped
        except:
            return "check your data type, has to be a tree of polylines"

    @staticmethod
    def linear_to_log(v, exponent=2.0):
        """
        Remap a linear input [0.0, 1.0] onto a logarithmic curve [0.0, 1.0].
        Clamps any input outside the [0.0, 1.0] range.
        """
        # clamp input
        # clamp input
        if v < 0.0:
            v = 0.0
        elif v > 1.0:
            v = 1.0
        # apply power mapping
        return v ** exponent

    @staticmethod
    def inchify(size):
        """
        Round a decimal inch measurement to nearest standard fraction
        (1/2, 1/4, 1/8, 1/16, or 1/32) and return the resulting float value.
        """
        whole = int(size)
        frac = size - whole
        denominators = [2, 4, 8, 16, 32]
        best_num = 0; best_den = 1; best_diff = None
        for d in denominators:
            n = int(frac * d + 0.5)
            diff = abs(frac - (float(n) / d))
            if best_diff is None or diff < best_diff:
                best_diff = diff; best_num = n; best_den = d
        def gcd(a, b):
            while b:
                a, b = b, a % b
            return a
        g = gcd(best_num, best_den)
        num_s = best_num // g; den_s = best_den // g
        if num_s == den_s:
            return float(whole + 1)
        if num_s == 0:
            return float(whole)
        return whole + float(num_s) / den_s

    # --- Spline Interpolation methods ---
    @staticmethod
    def solve_linear_system(A, b):
        """
        Solve a linear system Ax = b using Gaussian elimination
        with partial pivoting. Returns solution vector x.
        """
        n = len(A)
        for i in range(n):
            # find pivot
            max_el = abs(A[i][i]); max_row = i
            for k in range(i+1, n):
                if abs(A[k][i]) > max_el:
                    max_el = abs(A[k][i]); max_row = k
            A[i], A[max_row] = A[max_row], A[i]
            b[i], b[max_row] = b[max_row], b[i]
            # eliminate
            for k in range(i+1, n):
                c = -A[k][i] / A[i][i]
                for j in range(i, n):
                    if i == j:
                        A[k][j] = 0
                    else:
                        A[k][j] += c * A[i][j]
                b[k] += c * b[i]
        # back substitution
        x = [0 for _ in range(n)]
        for i in range(n-1, -1, -1):
            x[i] = b[i] / A[i][i]
            for k in range(i-1, -1, -1):
                b[k] -= A[k][i] * x[i]
        return x

    @staticmethod
    def calculate_spline_coefficients(x, y):
        """
        Compute cubic spline coefficients for given points (x, y).
        Returns tuples (a, b, c, d) representing spline segments.
        """
        n = len(x) - 1
        a = {k: v for k, v in enumerate(y)}
        h = {k: x[k+1] - x[k] for k in range(n)}
        # set up system
        A = [[0]*(n+1) for _ in range(n+1)]
        b = [0] * (n+1)
        for i in range(1, n):
            A[i][i-1] = h[i-1]
            A[i][i]   = 2*(h[i-1] + h[i])
            A[i][i+1] = h[i]
            b[i] = 3*((a[i+1] - a[i]) / h[i] - (a[i] - a[i-1]) / h[i-1])
        A[0][0] = 1; A[n][n] = 1
        c = LineUtils.solve_linear_system(A, b)
        bcoef = {}; dcoef = {}
        for i in range(n):
            bcoef[i] = (a[i+1] - a[i]) / h[i] - (h[i]*(c[i+1] + 2*c[i]) / 3)
            dcoef[i] = (c[i+1] - c[i]) / (3*h[i])
        return a, bcoef, c, dcoef

    @staticmethod
    def cubic_spline(x, coeffs, xi):
        """
        Evaluate the cubic spline at point xi using precomputed coefficients.
        Returns interpolated value or None if xi is out of range.
        """
        a, bcoef, c, dcoef = coeffs
        n = len(x) - 1
        for i in range(n):
            if x[i] <= xi <= x[i+1]:
                dx = xi - x[i]
                return a[i] + bcoef[i]*dx + c[i]*dx**2 + dcoef[i]*dx**3
        return None

    # --- Pipe generation methods ---
    @staticmethod
    def _bisector_plane(v1, v2, origin):
        """
        Create bisector plane for section placement.
        If v1 and v2 are colinear, returns a plane perpendicular to that direction.
        """
        # detect parallel or anti-parallel: cross will be near zero
        if abs(v1.IsParallelTo(v2, GLOBAL_TOL)) == 1:
            # For straight segments, just use a plane whose normal is the segment vector:
            return rg.Plane(origin, v2)

        # otherwise, compute true bisector plane
        bisector = v1 * v2.Length + v2 * v1.Length
        normal   = rg.Vector3d.CrossProduct(v1, v2)
        return rg.Plane(origin, bisector, normal)

    @staticmethod
    def _mesh_strip(p1, p2):
        """
        Create a quad strip mesh between two rings
        """
        m = rg.Mesh()
        cnt = p1.Count
        for i in range(cnt - 1):
            m.Vertices.Add(p1[i])
            m.Vertices.Add(p2[i])
        for j in range(cnt - 2):
            m.Faces.AddFace(j * 2 + 2, j * 2 + 3, j * 2 + 1, j * 2)
        last = cnt - 2
        m.Faces.AddFace(0, 1, last * 2 + 1, last * 2)
        return m

    @staticmethod
    def _create_ring(pt, vec, radius, segments):
        """
        Generate a circular ring at point along vector
        """
        plane = rg.Plane(pt, vec)
        cir = rg.Circle(plane, radius)
        ring = rg.Polyline()
        segf = float(segments)
        for i in range(int(segments) + 1):
            t = i * (2.0 * math.pi / segf) #fix for integer division when imported library
            ring.Add(cir.PointAt(t))
        return ring

    @staticmethod
    def _advance_ring(prev_ring, travel, sec_plane):
        """
        Project prev_ring along travel onto sec_plane
        """
        new_ring = rg.Polyline()
        for pt in prev_ring:
            line = rg.Line(pt, travel, 10.0)
            rc, t = rg.Intersect.Intersection.LinePlane(line, sec_plane)
            if not rc:
                t = 0.0
            new_ring.Add(line.PointAt(t))
        return new_ring

    @staticmethod
    def _build_rings(pl, radius, segments, closed):
        """
        Build sequence of rings along polyline
        """
        rings = [LineUtils._create_ring(pl[0], pl[1] - pl[0], radius, segments)]
        count = pl.Count
        if closed:
            v_start = pl[1] - pl[0]
            v_prev = pl[count - 2] - pl[0]
            sec_plane = LineUtils._bisector_plane(v_start, v_prev, pl[0])
            rings = [LineUtils._advance_ring(rings[0], pl[1] - pl[0], sec_plane)]
            start = 1; end = count - 2
        else:
            start = 0; end = count - 3
        for j in range(start, end + 1):
            v_prev = pl[j] - pl[j + 1]
            v_next = pl[j + 2] - pl[j + 1]
            sec_plane = LineUtils._bisector_plane(v_prev, v_next, pl[j + 1])
            travel = pl[j + 1] - pl[j]
            rings.append(LineUtils._advance_ring(rings[-1], travel, sec_plane))
        if not closed:
            end_pt = pl[count - 1]
            end_vec = pl[count - 2] - end_pt
            proj = rg.Polyline(rings[-1])
            xf = rg.Transform.PlanarProjection(rg.Plane(end_pt, end_vec))
            proj.Transform(xf)
            rings.append(proj)
        return rings

    @staticmethod
    def make_open(pl, radius, segments):
        """
        Generate pipe mesh for an open polyline
        """
        rings = LineUtils._build_rings(pl, radius, segments, False)
        mesh = rg.Mesh()
        for i in range(len(rings) - 1):
            mesh.Append(LineUtils._mesh_strip(rings[i], rings[i + 1]))
        mesh.Vertices.CombineIdentical(True, True)
        return mesh

    @staticmethod
    def make_closed(pl, radius, segments):
        """
        Generate pipe mesh for a closed polyline
        """
        rings = LineUtils._build_rings(pl, radius, segments, True)
        mesh = rg.Mesh()
        for i in range(len(rings) - 1):
            mesh.Append(LineUtils._mesh_strip(rings[i], rings[i + 1]))
        mesh.Append(LineUtils._mesh_strip(rings[0], rings[-1]))
        mesh.Vertices.CombineIdentical(True, True)
        return mesh

    @staticmethod
    def _compute_cut(r, s, theta, tol = GLOBAL_TOL):
        """
        Given bend radius r and deflection θ,  
        find the tangent offset (r·tan(θ/2)) from the pipe intersection,  
        then add the fitting’s straight stub length s.
        If near 0 -> no cut
        """
        if abs(theta) <= tol:
            return 0
        else:
            return r * math.tan(math.radians(theta/2.0)) + s

    @staticmethod
    def compute_raise(L, ang_deg, tol=GLOBAL_TOL):
        """
        Vertical rise of a straight segment of length L set at ang_deg to horizontal.
        """
        #ang_deg = 90 - ang_deg
        a = abs(ang_deg) % 180.0
        
        if a <= tol: 
            return 0
            
        if abs(a - 180.0) <= tol: 
            return 0
         
        h = L * math.sin(math.radians(a))
        
        if h <= tol: 
            return 0

        return h

    @staticmethod
    def compute_run(L, ang_deg, tol=GLOBAL_TOL):
        """
        Horizontal run of a straight segment of length L set at ang_deg to horizontal.
        """
        a = abs(ang_deg) % 180.0

        if a <= tol:
            return L

        if abs(a - 180.0) <= tol:
            return L

        if abs(a - 90.0) <= tol:
            return 0

        r = L * abs(math.cos(math.radians(a)))

        if r <= tol:
            return 0

        return r

    @staticmethod
    def compute_opposite(adjacent, ang_deg, tol=GLOBAL_TOL):
        """
        Opposite side (vertical) for a right‑triangle given adjacent side and angle to horizontal.
        """
        a = abs(ang_deg)%180.0
        if a <= tol or abs(a-180.0) <= tol:
            return 0
            
        if abs(a-90.0) <= tol:
            return float('inf')
            
        opp = adjacent*math.tan(math.radians(a))
        
        if abs(opp) <= tol:
            return 0
            
        return opp

    @staticmethod
    def fit_angle_to_height(L, avail_h, tol=GLOBAL_TOL):
        """
        Return the steepest angle whose rise fits in avail_h. 
        """
        if L <= tol:
            return 0.0
            
        if avail_h <= tol:
            return 0.0
            
        if avail_h >= L - tol:
            return 90.0
            
        ratio = avail_h / float(L)
        
        if ratio > 1.0:
            ratio = 1.0
            
        return math.degrees(math.asin(ratio))

    @staticmethod
    def smallest_ge(seq, x):
        """
        Smallest greater or equal from list of values
        """
        best = None
        for v in seq:
            if v >= x:
                if best is None or v < best: best = v
        return best

    @staticmethod
    def compute_pipe(pipepolyline, traderadius, segments, compute_normals, mergecollinear = True, linearsegments = 0.5, placefittings = False):
        """
        Create a mesh pipe along a polyline without caps
        Linear segments should be a 0.0 to 1.0 value which will 
        approximate curvature into polyline based on radius
        """
        radius = LineUtils.ConduitLookup.get_specs(traderadius)['od']/2
        
        segments = max(segments, 3)
        
        min_factor = 0.01   # when linearsegments == 0.0 -> mapped == 0.01 * radius
        max_factor = 5.0   # when linearsegments == 1.0 -> mapped == 5.0 * radius
        
        # clamp linearsegments to [0.0, 1.0]
        clamped = LineUtils.linear_to_log(linearsegments, 2)
        if clamped < 0.0:
            clamped = 0.0
        elif clamped > 1.0:
            clamped = 1.0
        
        # linearly map to [min_factor * radius, max_factor * radius]
        mapped = radius * (min_factor + (max_factor - min_factor) * clamped)
        
        linearsegmentresolution = mapped
        
        poly = None
        polycrvflag = False
        if isinstance(pipepolyline, rg.Polyline):
            poly = pipepolyline
        elif hasattr(pipepolyline, 'TryGetPolyline'):
            result, pl = pipepolyline.TryGetPolyline()
            if result:
                poly = pl
            else:
                polycrvflag = True
                polycrv = pipepolyline.ToPolyline(linearsegmentresolution*3, math.pi, linearsegmentresolution, float("inf"))
                poly = polycrv.ToPolyline()
                
        if poly is None or poly.Count < 2:
            return None
        
        #NOTE placeholder passing handling if polycrvflag
        if placefittings and not polycrvflag:
            angleschain = [] 
            fittingplanes = []
            segmentschain = []
            poly.MergeColinearSegments(GLOBAL_TOL, True) #always merge, collinear segment fittings arent usec currently
            
            #extract straight segments
            for i in range(poly.SegmentCount):
                seg = poly.SegmentAt(i)
                segmentschain.append(seg)
            
            #for each joint, get angle and bisector plane
            for i in range(len(segmentschain) - 1):
                seg1 = segmentschain[i]
                seg2 = segmentschain[i + 1]
                
                v1 = seg1.Direction
                v2 = seg2.Direction
                v1.Unitize()
                v2.Unitize()
                
                # dot‐acos gives 0 to 180°, always nonnegative
                angle_rad = math.acos(max(-1.0, min(1.0, v1 * v2)))
                angle_deg = round(math.degrees(angle_rad), 3)
                angleschain.append(angle_deg)
                
                # bisector direction (handles 180° by picking a perp if zero)
                bis = rg.Vector3d(v1 + v2)
                if bis.IsZero:
                    # perpendicular in-plane
                    bis = rg.Vector3d(-v1.Y, v1.X, 0)
                bis.Unitize()
                
                # normal from cross product
                normal = rg.Vector3d.CrossProduct(v1, v2)
                normal.Unitize()
                
                # plane at the joint point, x-axis=bisector, z-axis=normal
                origin = seg1.To
                # compute a proper Y-axis so that Plane.Z == normal
                yaxis = rg.Vector3d.CrossProduct(normal, bis)
                yaxis.Unitize()
                
                plane = rg.Plane(origin, bis, yaxis)
                fittingplanes.append(plane)
            
            segment_angle_pairs = []  # will hold tuples of (segment, startAng, endAng)
            
            for i, seg in enumerate(segmentschain):
                # start angle: 0° if first, otherwise the previous joint angle
                if i == 0:
                    start_ang = 0.0
                else:
                    start_ang = angleschain[i - 1]
                
                # end angle: 0° if last, otherwise the next joint angle
                if i == len(segmentschain) - 1:
                    end_ang = 0.0
                else:
                    end_ang = angleschain[i]
                
                segment_angle_pairs.append((seg, start_ang, end_ang))
            
            linearstub = LineUtils.ConduitLookup.get_specs(traderadius)['linear_section']
            bendradius = LineUtils.ConduitLookup.get_specs(traderadius)['min_bend']
            
            cutsegments = []
            for sap in segment_angle_pairs:
                seg, st_a, e_a = sap
                seglen = seg.Length
                startcut = LineUtils._compute_cut(bendradius, linearstub, st_a)
                endcut = LineUtils._compute_cut(bendradius, linearstub, e_a)
                cutlen = startcut + endcut
                
                if seglen > cutlen + GLOBAL_TOL:
                    newseg = rg.Line(seg.From, seg.To) #create a "deepcopy"
                    newseg.Extend(-startcut, -endcut)
                    cutsegments.append(newseg)
                else:
                    pass #doesnt need to be placed
            
            finalmesh = rg.Mesh()
            for cutseg in cutsegments:
                cutpoly = rg.Polyline([cutseg.From, cutseg.To])
                segment = LineUtils.compute_pipe(cutpoly, traderadius, segments, compute_normals, mergecollinear, linearsegments, placefittings = False)
                #print "segment", segment
                finalmesh.Append(segment)
            
            turnsegments = []
            for angle, plane in zip(angleschain, fittingplanes):
                linearlen = LineUtils._compute_cut(bendradius, linearstub, angle)
                half = math.radians((180-angle)/2) #here lets say 30degree is considered as 150 in such planes
                dx = math.sin(half)*linearlen
                dy = math.cos(half)*linearlen
                p1 = plane.Origin + plane.XAxis*dx + plane.YAxis*dy
                p2 = plane.Origin + plane.XAxis*-dx + plane.YAxis*dy
                polyturn = rg.Polyline([p1, plane.Origin, p2])
                
                filletedturn = LineUtils.fillet2(polyturn, bendradius, segments = 10)
                turnmesh = LineUtils.compute_pipe(filletedturn, traderadius, segments, compute_normals, mergecollinear, linearsegments, placefittings = False)
                
                finalmesh.Append(turnmesh)
                #turnsegments.append(filletedturn)
                #turnsegments.append(polyturn)
            
            #return turnsegments
            return finalmesh
            #return cutsegments
            #print segment_angle_pairs
            #print angleschain
            #return fittingplanes
            
            
        else: #always here if polycrvflag currently
            if mergecollinear:
                poly.MergeColinearSegments(GLOBAL_TOL, True)
            
            mesh = LineUtils.make_closed(poly, radius, segments) if poly.IsClosed else LineUtils.make_open(poly, radius, segments)
            if compute_normals:
                mesh.Normals.ComputeNormals()
                mesh.UnifyNormals()
                
            return mesh
    
    @staticmethod
    def fillet2(polyline, radius, segments = 10):
        """
        Takes a polyline with EXACTLY 2 segments as input
        creates a fillet with n segments
        fillet is not an arch, result is always a polyline
        """
        # must be exactly two segments
        if polyline.Count != 3:
            return "Polyline must have exactly 2 segments"
        
        p0, p1, p2 = polyline[0], polyline[1], polyline[2]
    
        #build a plane through p1 using p0->p1 and p2->p1
        plane = rg.Plane(p1, p0, p2)
    
        #project into that plane (unpack success,u,v)
        ok, u0, v0 = plane.ClosestParameter(p0)
        ok, u1, v1 = plane.ClosestParameter(p1)
        ok, u2, v2 = plane.ClosestParameter(p2)
        p0_2d = rg.Point2d(u0, v0)
        p1_2d = rg.Point2d(u1, v1)
        p2_2d = rg.Point2d(u2, v2)
    
        #compute the two trim points along each incoming/outgoing edge
        vA = p0_2d - p1_2d; vA.Unitize()
        vB = p2_2d - p1_2d; vB.Unitize()
        theta = math.acos(vA * vB)
        d = radius / math.tan(theta/2.0)
        tp1_2d = p1_2d + vA * d
        tp2_2d = p1_2d + vB * d
    
        #find the 2D center of the circular fillet
        bis = vA + vB; bis.Unitize()
        h = radius / math.sin(theta/2.0)
        center2d = p1_2d + bis * h
    
        #compute start/end angles
        angle1 = math.atan2(tp1_2d.Y - center2d.Y, tp1_2d.X - center2d.X)
        angle2 = math.atan2(tp2_2d.Y - center2d.Y, tp2_2d.X - center2d.X)
    
        # normalize into [-Pi, Pi] in one go
        delta = (angle2 - angle1 + math.pi) % (2*math.pi) - math.pi
    
        #sample the arc in 'segments' steps
        arc2d = []
        for i in range(segments + 1):
            t = float(i) / segments
            ang = angle1 + delta * t
            x = center2d.X + math.cos(ang) * radius
            y = center2d.Y + math.sin(ang) * radius
            arc2d.append(rg.Point2d(x, y))
    
        #build the new 2D polyline and map back to world
        pts2d = [p0_2d, tp1_2d] + arc2d[1:-1] + [tp2_2d, p2_2d]
        pts3d = [plane.PointAt(pt.X, pt.Y) for pt in pts2d]
    
        return rg.Polyline(pts3d)

    @staticmethod
    def boundary_surface(curve, tol = GLOBAL_TOL):
        """
        Create planar Brep from a  boundary edge curve.
        (possibly empty if compute failed)
        """
        #No input -> nothing
        if not curve:
            #print "here"
            return None
            
        #Normalize polyline input
        if isinstance(curve, rg.Polyline):
            poly = curve
        elif hasattr(curve, 'TryGetPolyline'):
            result, pl = curve.TryGetPolyline()
            if result:
                poly = pl
            else:
                polycrv = curve.ToPolyline(tol*3, math.pi, tol, float("inf"))
                poly = polycrv.ToPolyline()

        pl = poly

        if pl.IsClosed:
            seg_cnt = pl.SegmentCount - 1 
            if seg_cnt in (3, 4):
                pts = [pl[i] for i in range(seg_cnt)]
                # handle triangle and quad separately
                if seg_cnt == 3:
                    brep = rg.Brep.CreateFromCornerPoints(
                        pts[0], pts[1], pts[2], tol)
                else:
                    brep = rg.Brep.CreateFromCornerPoints(
                        pts[0], pts[1], pts[2], pts[3], tol)
            else:
                brep = rg.Brep.CreatePlanarBreps(pl.ToPolylineCurve(), tol)[0]
                #print "not 3, 4, count {}".format(seg_cnt)
                
            if brep:
                return brep
        else:
            #print "notclosed"
            return None

    @staticmethod
    def extrusion(curve, direction, tol = GLOBAL_TOL):
        """
        Closed polyline as input 
        Returns capped rg.Extrusion
        """
        
        #Normalize polyline input
        if isinstance(curve, rg.Polyline):
            poly = curve
        elif hasattr(curve, 'TryGetPolyline'):
            result, pl = curve.TryGetPolyline()
            if result:
                poly = pl
            else:
                polycrv = curve.ToPolyline(tol*3, math.pi, tol, float("inf"))
                poly = polycrv.ToPolyline()
        
        if poly:
            #print "here", poly.IsClosed
            if poly.IsClosed:
                #NOTE: ToPolylineCurve() mostly gave no results, while ToNurbsCurve() worked very well 
                ext = rg.Extrusion.Create(poly.ToNurbsCurve(), direction.Length, True)
                #print [p.Z for p in poly]
                #print ext#, direction, direction.Length, poly, poly.ToPolylineCurve()
                return ext

        return None


    #currently here, need to think on where to put this style functions
    #box from rectangle, for example for line box intersection
    @staticmethod
    def rectangle_to_box(rect, thickness=10.0):
        """
        Creates a Box from a Rectangle3d by extruding it along its plane normal
        to the specified thickness.
        """
        plane = rect.Plane
        x_int = rect.X
        y_int = rect.Y
        z_int = rg.Interval(-thickness/2.0, thickness/2.0)
        return rg.Box(plane, x_int, y_int, z_int)
    
    @staticmethod
    def offset_rectangle(rect, offset, tol = GLOBAL_TOL):
        """
        Returns a new Rectangle3d expanded by the given offset on X and Y,
        enforcing a minimum size based on tolerance.
        """
        x, y = rect.X, rect.Y
        xmin, xmax = x.Min - offset, x.Max + offset
        ymin, ymax = y.Min - offset, y.Max + offset
        if xmax - xmin < tol:
            m = (xmin + xmax) * 0.5
            xmin, xmax = m - tol/2, m + tol/2
        if ymax - ymin < tol:
            m = (ymin + ymax) * 0.5
            ymin, ymax = m - tol/2, m + tol/2
        return rg.Rectangle3d(rect.Plane, rg.Interval(xmin, xmax), rg.Interval(ymin, ymax))

    @staticmethod
    def rebuild_rectangle(rect):
        """
        Rebuilds a Rectangle3d so its extents align to world X/Y axes,
        preserving its original elevation.
        """
        # get world‐space corners
        corners = [rect.Corner(i) for i in range(4)]
        xs = [pt.X for pt in corners]
        ys = [pt.Y for pt in corners]
        xmin, xmax = min(xs), max(xs)
        ymin, ymax = min(ys), max(ys)
        # build a world‐XY plane at the original Z height
        z      = rect.Plane.Origin.Z
        origin = rg.Point3d(xmin, ymin, z)
        plane  = rg.Plane(origin, rg.Vector3d.XAxis, rg.Vector3d.YAxis)
        # width along world X, height along world Y
        w = xmax - xmin
        h = ymax - ymin
        return rg.Rectangle3d(plane, w, h)

    @staticmethod
    def rectangle_axis(rect):
        """
        Returns the long axis of the rectangle as an rg.Line from midpoint to midpoint.
        """
        # get the four corners
        corners = [rect.Corner(i) for i in range(4)]
        # compute edge lengths
        lengths = [corners[i].DistanceTo(corners[(i+1)%4]) for i in range(4)]
        # find the longest edge index
        idx = lengths.index(max(lengths))
        # choose opposite midpoints based on edge orientation
        if idx in (0, 2):
            p1 = (corners[0] + corners[3]) / 2.0
            p2 = (corners[1] + corners[2]) / 2.0
        else:
            p1 = (corners[0] + corners[1]) / 2.0
            p2 = (corners[2] + corners[3]) / 2.0
        return rg.Line(p1, p2)

    @staticmethod
    def rectangle_from_line(line, thickness, extend = True):
        """
        Returns a Rectangle of n thickness around the line as its axis
        extend is adding half thickness to each end making rectangle sdf-like
        """
        if extend:
            rfl = rg.Line(line.From, line.To) #create a copy
            rfl.Extend(thickness/2, thickness/2)
            line = rfl
        v = line.UnitTangent
        
        perp = rg.Vector3d(-v.Y, v.X, 0)          # perpendicular in XY
        plane = rg.Plane(line.From, v, perp)      # X = line, Y = perp, normal = Z
        x_int = rg.Interval(0, line.Length)
        y_int = rg.Interval(-thickness/2.0, thickness/2.0)
        return rg.Rectangle3d(plane, x_int, y_int)

    @staticmethod
    def get_bounds_for_line(line, rect, axis):
        """
        Calculates a line’s projection interval on a rectangle along an axis if
        they overlap, returning that interval or None.
        """
        origin = rect.Plane.Origin
        if axis == 'y':
            rmin = origin.Y
            rmax = origin.Y + rect.Height
            lxmin = min(line.From.X, line.To.X)
            lxmax = max(line.From.X, line.To.X)
            rxmin = origin.X
            rxmax = origin.X + rect.Width
            if lxmax < rxmin - GLOBAL_TOL or lxmin > rxmax + GLOBAL_TOL:
                return None
        else:  # axis == 'x'
            rmin = origin.X
            rmax = origin.X + rect.Width
            lymin = min(line.From.Y, line.To.Y)
            lymax = max(line.From.Y, line.To.Y)
            rymin = origin.Y
            rymax = origin.Y + rect.Height
            if lymax < rymin - GLOBAL_TOL or lymin > rymax + GLOBAL_TOL:
                return None
        return (rmin, rmax)

    @staticmethod
    def get_rectangle_bounds(rect):
        """
        Calculates world-aligned X and Y bounds of a Rectangle3d,
        returning [[xmin, xmax], [ymin, ymax]].
        """
        bbox = rect.BoundingBox
        return [[bbox.Min.X, bbox.Max.X], [bbox.Min.Y, bbox.Max.Y]]

    @staticmethod
    def get_union_interval_containing(c, intervals):
        """
        Merges sorted intervals and returns the one containing a coordinate within
        tolerance, or None if no interval applies.
        """
        merged = LineUtils.merge_intervals(intervals)
        for (u_min, u_max) in merged:
            if c > u_min + GLOBAL_TOL and c < u_max - GLOBAL_TOL:
                return (u_min, u_max)
        return None

    @staticmethod
    def rects_collide(rect1, rect2):
        """
        Returns True if two Rectangle3d objects overlap by:
         - BoundingBox test  
         - Any corner of one lies Inside/Coincident with the other  
         - Any of their edges intersect
        """
        checker = (rg.PointContainment.Inside,
                   rg.PointContainment.Coincident)

        # Fast reject via AABB overlap on X/Y
        bb1 = rect1.BoundingBox
        bb2 = rect2.BoundingBox
        # no overlap if one box is entirely left/right or above/below the other
        if (bb1.Max.X < bb2.Min.X or bb1.Min.X > bb2.Max.X
         or bb1.Max.Y < bb2.Min.Y or bb1.Min.Y > bb2.Max.Y):
            return False

        #Corner containment
        for i in range(4):
            if rect1.Contains(rect2.Corner(i)) in checker:
                return True
            if rect2.Contains(rect1.Corner(i)) in checker:
                return True

        #Edge intersections: convert to closed curves and test
        crv1 = rect1.ToNurbsCurve()
        crv2 = rect2.ToNurbsCurve()
        events = rg.Intersect.Intersection.CurveCurve(
            crv1, crv2, GLOBAL_TOL, GLOBAL_TOL
        )
        if events and len(events) > 0:
            return True

        return False
    
    @staticmethod
    def polylines_collide(plA, plB):
        """
        Fast polyline‐vs‐polyline collision (AABB + segment intersection + containment)
        """
        bbA = plA.BoundingBox
        bbB = plB.BoundingBox
    
        # 1) AABB reject
        if bbA.Max.X < bbB.Min.X or bbA.Min.X > bbB.Max.X or \
           bbA.Max.Y < bbB.Min.Y or bbA.Min.Y > bbB.Max.Y:
            return False
    
        # 2) Segment‐segment intersections
        for i in range(plA.Count - 1):
            segA = rg.LineCurve(rg.Line(plA[i], plA[i+1]))
            for j in range(plB.Count - 1):
                segB = rg.LineCurve(rg.Line(plB[j], plB[j+1]))
                evts = rg.Intersect.Intersection.CurveCurve(
                    segA, segB, GLOBAL_TOL, GLOBAL_TOL
                )
                if evts:
                    return True
    
        # 3) Full‐containment check
        crvA = rg.PolylineCurve(plA)
        crvB = rg.PolylineCurve(plB)
        checker = (rg.PointContainment.Inside, rg.PointContainment.Coincident)
    
        # If any vertex of A lies inside or on B
        for pt in plA:
            if crvB.Contains(pt) in checker:
                return True
    
        # If any vertex of B lies inside or on A
        for pt in plB:
            if crvA.Contains(pt) in checker:
                return True
    
        return False
    
    @staticmethod
    def flatten_to_xy(rect):
        """
        project rectangle to world XY plane, preserving rotation about Z
        """
        p0 = rect.Corner(0)
        p1 = rect.Corner(1)
        p3 = rect.Corner(3)
        p0_flat = rg.Point3d(p0.X, p0.Y, 0)
        dir_x = rg.Vector3d(p1.X - p0.X, p1.Y - p0.Y, 0)
        dir_y = rg.Vector3d(p3.X - p0.X, p3.Y - p0.Y, 0)
        dir_x.Unitize()
        dir_y.Unitize()
        plane = rg.Plane(p0_flat, dir_x, dir_y)
        return rg.Rectangle3d(plane, rect.Width, rect.Height)

    @staticmethod
    def find_intersecting_rect_pairs(rects):
        """
        takes list of Rectangles, returns list of (i, j) index pairs that intersect in XY
        uses sweep-line on axis-aligned bboxes then precise LineUtils.rects_collide
        """
        flats = [LineUtils.flatten_to_xy(r) for r in rects]
        events = []
        for i, r in enumerate(flats):
            bb = r.BoundingBox
            events.append((bb.Min.X, True, i))
            events.append((bb.Max.X, False, i))
        events.sort(key=lambda e: (e[0], not e[1]))

        active = []
        hits = []
        for x, start, i in events:
            if start:
                bb_i = flats[i].BoundingBox
                minY, maxY = bb_i.Min.Y, bb_i.Max.Y
                for j in active:
                    bb_j = flats[j].BoundingBox
                    if bb_j.Max.Y >= minY and bb_j.Min.Y <= maxY:
                        if LineUtils.rects_collide(flats[i], flats[j]):
                            hits.append((j, i))
                active.append(i)
            else:
                active.remove(i)
        return hits

    @staticmethod
    def union_intersecting_rects_outline(rects, tol=GLOBAL_TOL):
        """
        takes list of Rectangle3d, groups intersecting ones and returns list of Polylines for outlines
        """
        pairs = LineUtils.find_intersecting_rect_pairs(rects)
        adj = {}
        for i, j in pairs:
            adj.setdefault(i, []).append(j)
            adj.setdefault(j, []).append(i)
        clusters = []
        visited = set()
        for idx in range(len(rects)):
            if idx in visited:
                continue
            stack = [idx]
            cluster = []
            while stack:
                n = stack.pop()
                if n not in visited:
                    visited.add(n)
                    cluster.append(n)
                    for m in adj.get(n, []):
                        if m not in visited:
                            stack.append(m)
            clusters.append(cluster)
        outlines = []
        
        #print "Created {} clusters".format(len(clusters))
        
        for cluster in clusters:
            curves = [LineUtils.flatten_to_xy(rects[i]).ToNurbsCurve() for i in cluster]
            unioned = rg.Curve.CreateBooleanUnion(curves, tol)
            for c in unioned or []:
                #print c
                #print c.TryGetPolyline()
                bool, pl = c.TryGetPolyline()#rg.Polyline()
                if bool:
                    outlines.append(pl)
                else:
                    outlines.append(c)
        return outlines

    @staticmethod
    def line_in_polyline(line, polylines):
        """
        Takes a Line and list of Polylines, returns index of first polyline containing both endpoints, else -1
        """
        for i, pl in enumerate(polylines):
            pc = rg.PolylineCurve(pl)
            if pc.Contains(line.From) != rg.PointContainment.Outside and pc.Contains(line.To) != rg.PointContainment.Outside:
                return i
        return -1

    @staticmethod
    def line_outside_rectangles(line, rectangles, thickness=10.0, tol=GLOBAL_TOL):
        """
        Returns a list of Line segments representing those portions of the finite
        line segment that do NOT lie within any of the given Rectangle3d objects.
        """
        # Parametric domain of the finite line
        seg_dom = rg.Interval(0.0, 1.0)

        # 1) Collect all hit‐intervals where the line enters/exits each rectangle (as a thin box)
        intervals = []
        for rect in rectangles:
            box = LineUtils.rectangle_to_box(rect, thickness)
            hit, iv = rg.Intersect.Intersection.LineBox(line, box, tol)
            if not hit:
                continue
            t0, t1 = iv.Min, iv.Max
            lo = max(seg_dom.Min, min(t0, t1))
            hi = min(seg_dom.Max, max(t0, t1))
            if hi > lo + tol:
                intervals.append((lo, hi))

        # 2) Merge overlapping or touching intervals
        merged = LineUtils.merge_intervals(intervals)

        # 3) Compute complement intervals in [0,1]
        outside = []
        current = seg_dom.Min
        for a, b in merged:
            if a > current + tol:
                outside.append((current, a))
            current = max(current, b)
        if seg_dom.Max > current + tol:
            outside.append((current, seg_dom.Max))

        # 4) Build and return the actual line segments
        segments = []
        for t0, t1 in outside:
            pt0 = line.PointAt(t0)
            pt1 = line.PointAt(t1)
            segments.append(rg.Line(pt0, pt1))
        return segments

    @staticmethod
    def _offset_along_axis(rect, axis, amount):
        """
        Returns a new Rectangle3d offset along one local axis by 'amount':
        negative extends Min, positive extends Max.
        """
        x, y = rect.X, rect.Y
        if axis == 'x':
            new_x = rg.Interval(x.Min + min(amount,0), x.Max + max(amount,0))
            return rg.Rectangle3d(rect.Plane, new_x, y)
        else:
            new_y = rg.Interval(y.Min + min(amount,0), y.Max + max(amount,0))
            return rg.Rectangle3d(rect.Plane, x, new_y)

    @staticmethod
    def _max_extension(slave, axis, direction, limit, master_rects):
        """
        Binary‐searches the max extension (up to 'limit') along one axis/direction
        before colliding with any master rectangles.
        """
        lo, hi, best = 0.0, limit, 0.0
        for _ in range(10):
            mid = (lo + hi) / 2.0
            test = LineUtils._offset_along_axis(slave, axis, direction * mid)
            if any(LineUtils.rects_collide(test, m) for m in master_rects):
                hi = mid
            else:
                best = mid
                lo = mid
        return best * direction

    @staticmethod
    def extend_rectangles(master_rects, slave_rects, extenddistance):
        """
        Extends each slave rectangle along its long axis by up to 'extenddistance'
        in both directions, stopping each way if it collides with any master.
        Returns a new list of extended Rectangle3d objects.
        """
        extended = []
        for slave in slave_rects:
            # pick the longer local axis
            axis = 'x' if slave.Width >= slave.Height else 'y'
            # compute negative and positive extensions
            neg_ext = LineUtils._max_extension(slave, axis, -1, extenddistance, master_rects)
            pos_ext = LineUtils._max_extension(slave, axis, +1, extenddistance, master_rects)
            x, y = slave.X, slave.Y
            # build new intervals
            new_x = (rg.Interval(x.Min + min(0,neg_ext), x.Max + max(0,pos_ext)) if axis == 'x' else x)
            new_y = (rg.Interval(y.Min + min(0,neg_ext), y.Max + max(0,pos_ext)) if axis == 'y' else y)
            
            extended.append(rg.Rectangle3d(slave.Plane, new_x, new_y))

        return extended

    @staticmethod
    def merge_intervals(intervals, tol = GLOBAL_TOL):
        """
        Merges overlapping or touching numeric intervals into a consolidated list.
        """
        if not intervals:
            return []
            
        sorted_int = sorted(intervals, key=lambda x: x[0])
        
        merged = [sorted_int[0]]
        for current in sorted_int[1:]:
            last = merged[-1]
            if current[0] <= last[1] + tol:
                merged[-1] = (last[0], max(last[1], current[1]))
            else:
                merged.append(current)
        return merged

    @staticmethod
    def encode(v, rounding=3, anglealigned = False):
        """
        Return the angle of a vector in the XY plane modulo π.
        """
        #added extra snapping to Pi and 2Pi to better adjust for tolerance
        v2d = rg.Vector3d(v.X, v.Y, 0)
        
        if not v2d.IsZero:
            v2d.Unitize()
            
        a = math.atan2(v2d.Y, v2d.X)
        if a < 0:
            a += 2 * math.pi
        if anglealigned:
            r = round(a, rounding)
            if r == round(2 * math.pi, rounding):
                r = 0.0
            return r
        else:
            r = round(a % math.pi, rounding)
            if r == round(math.pi, rounding):
                r = 0.0
            return r

    @staticmethod
    def find_param_group(groups, val, tol=GLOBAL_TOL):
        """
        Return existing key within tolerance or None.
        """
        for k in groups:
            if abs(k - val) < tol:
                return k
        return None

    @staticmethod
    def _ensure_positive_tol(t, fallback=1e-9):
        """
        Internal helper: make sure a tolerance is strictly positive.
        Used where 0.0 would cause divisions or degenerate behavior.
        """
        if t <= 0.0:
            return fallback
        return t

    @staticmethod
    def _qbucket(v, t):
        """
        Stable quantization bucket using "round half away from zero".
        """
        t = LineUtils._ensure_positive_tol(t)
        return int(math.floor((v / t) + 0.5))
    
    @staticmethod
    def _qhash_point(pt, t, use_z=False):
        kx = LineUtils._qbucket(pt.X, t)
        ky = LineUtils._qbucket(pt.Y, t)
        if use_z:
            kz = LineUtils._qbucket(pt.Z, t)
        else:
            kz = 0
        return (kx, ky, kz)

    @staticmethod
    def dedupe_lines(lines, tol=GLOBAL_TOL, use_z=False):
        """
        Remove duplicates by snapping endpoints into tolerance-based point groups.
        AB == BA. By default groups in 2D (ignore Z).
        """
        result = []
        seen = set()
    
        tol = LineUtils._ensure_positive_tol(tol)
        
        if not lines:
            return []
    
        # maps tolerant point "keys" -> representative (we just use tuple keys)
        groups2d = {}  # (x,y) -> (x,y)
        groups3d = {}  # (x,y,z) -> (x,y,z)
    
        def key2d(pt):
            k = LineUtils._find_point_group2d(groups2d, pt.X, pt.Y, tol)
            if k is None:
                k = (pt.X, pt.Y)
                groups2d[k] = k
            return k
    
        def key3d(pt):
            # simple 3D version mirroring the 2D one
            for kx, ky, kz in groups3d:
                dx = pt.X - kx
                dy = pt.Y - ky
                dz = pt.Z - kz
                if dx*dx + dy*dy + dz*dz <= tol*tol:
                    return (kx, ky, kz)
            k = (pt.X, pt.Y, pt.Z)
            groups3d[k] = k
            return k
    
        for ln in lines:
            if ln is None:
                continue
            try:
                if hasattr(ln, 'Length'):
                    if ln.Length <= tol:
                        continue
                p0 = ln.From
                p1 = ln.To
            except:
                continue
            if p0 is None or p1 is None:
                continue
    
            # snap endpoints into tolerant clusters (2D default)
            if use_z:
                k0 = key3d(p0)
                k1 = key3d(p1)
            else:
                k0 = key2d(p0)  # uses _find_point_group2d under the hood
                k1 = key2d(p1)
    
            # collapse degenerate after snapping
            if k0 == k1:
                continue
    
            # orientation-insensitive canonical key
            key = (k0, k1) if k0 <= k1 else (k1, k0)
    
            if key in seen:
                continue
            seen.add(key)
            result.append(ln)
    
        return result

    @staticmethod
    def process_lines(rawlines, tol=GLOBAL_TOL, anglealigned=False, perlevel=False):
        """
        Merge near-collinear lines into axis-aligned segments.
        """
        
        #rawlines = LineUtils.dedupe_lines(rawlines, tol)
        
        #if requested, split by .Z first
        if perlevel:
            z_groups = {}
            for ln in rawlines:
                z = ln.From.Z
                key = LineUtils.find_param_group(z_groups, z, tol)
                if key is None:
                    z_groups[z] = []
                    key = z
                z_groups[key].append(ln)
            processed = []
            for group in z_groups.values():
                processed.extend(LineUtils.process_lines(group, tol, anglealigned, perlevel=False))
            return processed
        
        #to help out with tolerance issues
        for iter in range(3):
            extrajoin = 3.0
            lines = [rg.Line(l.From, l.To) for l in rawlines]
            
            for line in lines:
                line.Extend(extrajoin, extrajoin)
            groups = {}
            
            for ln in lines:
                angle = LineUtils.encode(ln.Direction, 16, anglealigned)
                key = LineUtils.find_param_group(groups, angle, tol)
                if key is None:
                    groups[angle] = []
                    key = angle
                groups[key].append(ln)
                
            processed_lines = []
            
            for group_angle, glines in groups.items():
                delta = math.pi/2 - group_angle
                
                #pts = [rg.Point3d((ln.From.X + ln.To.X) * 0.5, (ln.From.Y + ln.To.Y) * 0.5, (ln.From.Z + ln.To.Z) * 0.5) for ln in glines]
                #n = len(pts)
                #origin = rg.Point3d(sum(pt.X for pt in pts) / n, sum(pt.Y for pt in pts) / n, sum(pt.Z for pt in pts) / n)
                origin = rg.Point3d(0, 0, 0)
                                    
                T = rg.Transform.Rotation(delta, origin)
                #_, T_inv = T.TryGetInverse()
                T_inv = rg.Transform.Rotation(-delta, origin)
                
                rotated_lines = []
                
                for ln in glines:
                    ln_copy = rg.Line(ln.From, ln.To)
                    ln_copy.Transform(T)
                    rotated_lines.append(ln_copy)
                vert_groups = {}
                
                for ln in rotated_lines:
                    xv = (ln.From.X + ln.To.X) * 0.5
                    key = LineUtils.find_param_group(vert_groups, xv, tol)
                    if key is None:
                        vert_groups[xv] = []
                        key = xv
                    y0, y1 = sorted([ln.From.Y, ln.To.Y])
                    vert_groups[key].append((y0, y1))
                    
                for xval, intervals in vert_groups.items():
                    merged_ints = LineUtils.merge_intervals(intervals, tol)
                    
                    for st, en in merged_ints:
                        new_line = rg.Line(rg.Point3d(xval, st, origin.Z),
                                           rg.Point3d(xval, en, origin.Z))
                        new_line.Transform(T_inv)
                        #extend back 
                        new_line.Extend(-extrajoin, -extrajoin)
                        processed_lines.append(new_line)

            rawlines = processed_lines
        return processed_lines

    @staticmethod
    def _orth_frame(normal):
        """
        Return orthonormal X,Y,Z axes with Z aligned to the given vector.
        """
        n = rg.Vector3d(normal.X, normal.Y, normal.Z)
        if not n.IsZero: 
            n.Unitize()
        up = rg.Vector3d(0, 0, 1)
        if abs(rg.Vector3d.Multiply(n, up)) > 0.9: 
            up = rg.Vector3d(1, 0, 0)
            
        x = rg.Vector3d.CrossProduct(up, n); x.Unitize()
        y = rg.Vector3d.CrossProduct(n, x); y.Unitize()
        return x, y, n

    @staticmethod
    def encode3d(v):
        """
        Unitize and sign-normalize a 3D vector for parallel grouping.
        """
        u = rg.Vector3d(v.X, v.Y, v.Z)
        if not u.IsZero: 
            u.Unitize()
        if u.Z < 0 or (abs(u.Z) < GLOBAL_TOL and (u.Y < 0 or (abs(u.Y) < GLOBAL_TOL and u.X < 0))):
            u *= -1.0
        return (u.X, u.Y, u.Z)

    @staticmethod
    def _find_dir_group3d(groups, dir_key, cos_thresh):
        """
        Find an existing direction key within angular threshold.
        """
        ux, uy, uz = dir_key
        for k in groups:
            kx, ky, kz = k
            if abs(ux*kx + uy*ky + uz*kz) >= cos_thresh: 
                return k
        return None

    @staticmethod
    def _find_point_group2d(groups, x, y, tol=GLOBAL_TOL):
        """
        Find 2D key in dict within given distance tolerance.
        """
        for kx, ky in groups:
            dx = x - kx
            dy = y - ky
            if dx*dx + dy*dy <= tol*tol: 
                return (kx, ky)
        return None

    @staticmethod
    def process_lines_3d(rawlines, tol=GLOBAL_TOL, anglealigned=False, perlevel=False, type = "legacy", iterations=3):
        """
        Merge near-collinear 3D lines along their true axes with minimal drift.
        Type can be "sweep" or "legacy", sweep is more kitter resistant but longer
        """
        if type == "sweep":
            resplit = LineUtils.split_lines_at_intersections(rawlines, GLOBAL_TOL, False)
            deduped = LineUtils.dedupe_lines(resplit, GLOBAL_TOL)
            sweeped = LineUtils.build_collinear_polylines_sweep(deduped, GLOBAL_TOL, 1.0)
            axised = [LineUtils.fit_weighted_line_from_polyline(sweep) for sweep in sweeped]
            resnapped = LineUtils.extend_lines_to_touch_others(axised)
            
            return resnapped
        if type == "legacy":
            if not rawlines: 
                return []
            for _ in range(iterations):
                extrajoin = 3.0
                lines = []
                for l in rawlines:
                    ln = rg.Line(l.From, l.To)
                    ln.Extend(extrajoin, extrajoin)
                    if ln.Length > tol: 
                        lines.append(ln)
                if not lines: return []
    
                # scale-aware angular threshold so lateral drift ≤ tol
                bb = rg.BoundingBox([ln.From for ln in lines] + [ln.To for ln in lines])
                span = bb.Diagonal.Length
                if span <= 0.0: 
                    span = max([ln.Length for ln in lines] + [1.0])
                theta = min(0.25, math.asin(min(1.0, tol / span)))
                cos_thresh = math.cos(theta)
    
                dir_groups = {}
                for ln in lines:
                    dkey = LineUtils.encode3d(ln.Direction)
                    key = LineUtils._find_dir_group3d(dir_groups, dkey, cos_thresh)
                    if key is None:
                        dir_groups[dkey] = []
                        key = dkey
                    dir_groups[key].append(ln)
    
                processed = []
                for dkey, glines in dir_groups.items():
                    ux, uy, uz = dkey
                    mids = [rg.Point3d((ln.From.X+ln.To.X)*0.5, (ln.From.Y+ln.To.Y)*0.5, (ln.From.Z+ln.To.Z)*0.5) for ln in glines]
                    n = len(mids)
                    
                    origin = rg.Point3d(sum(p.X for p in mids)/n, sum(p.Y for p in mids)/n, sum(p.Z for p in mids)/n)
                    xaxis, yaxis, zaxis = LineUtils._orth_frame(rg.Vector3d(ux, uy, uz))
                    
                    from_plane = rg.Plane(origin, xaxis, yaxis)
                    to_plane = rg.Plane(origin, rg.Vector3d.XAxis, rg.Vector3d.YAxis)
                    T = rg.Transform.PlaneToPlane(from_plane, to_plane)
                    T_inv = rg.Transform.PlaneToPlane(to_plane, from_plane)
    
                    rot = []
                    for ln in glines:
                        lc = rg.Line(ln.From, ln.To)
                        lc.Transform(T)
                        rot.append(lc)
    
                    rails = {}
                    for ln in rot:
                        xv = (ln.From.X + ln.To.X) * 0.5
                        yv = (ln.From.Y + ln.To.Y) * 0.5
                        k = LineUtils._find_point_group2d(rails, xv, yv, tol)
                        if k is None:
                            rails[(xv, yv)] = []
                            k = (xv, yv)
                        z0, z1 = sorted([ln.From.Z, ln.To.Z])
                        rails[k].append((z0, z1))
    
                    for (xv, yv), intervals in rails.items():
                        merged = LineUtils.merge_intervals(intervals, tol)
                        for st, en in merged:
                            nl = rg.Line(rg.Point3d(xv, yv, st), rg.Point3d(xv, yv, en))
                            nl.Transform(T_inv)
                            nl.Extend(-extrajoin, -extrajoin)
                            if nl.IsValid and nl.Length > tol: 
                                processed.append(nl)
                rawlines = processed
            return processed

    @staticmethod
    def _unique_params(pvals, tol = GLOBAL_TOL, include_endpoints=False):
        """
        Deduplicate and sort parameter values in [0,1], applying the same
        snapping and inclusion rules as _snap01 / _in01.
        """
        ps = []
        for p in pvals:
            if include_endpoints:
                if p >= -tol and p <= 1.0 + tol:
                    ps.append(p)
            else:
                if p > tol and p < 1.0 - tol:
                    ps.append(p)
        if not ps:
            return []
        ps = sorted(ps)
        out = []
        for p in ps:
            if not out or abs(p - out[-1]) > tol:
                if p < 0.0 + tol:
                    p = 0.0
                if p > 1.0 - tol:
                    p = 1.0
                out.append(p)
        return out

    @staticmethod
    def _split_line_at_params(ln, pvals, tol = GLOBAL_TOL):
        pvals = LineUtils._unique_params(pvals, tol, include_endpoints=True)
        segs = []
        start = 0.0
        for p in pvals:
            if p > start + tol and p < 1.0 - tol:
                a = ln.PointAt(start)
                b = ln.PointAt(p)
                s = rg.Line(a, b)
                if s.IsValid and s.Length > tol:
                    segs.append(s)
                start = p
        s = rg.Line(ln.PointAt(start), ln.PointAt(1.0))
        if s.IsValid and s.Length > tol:
            segs.append(s)
        return segs

    @staticmethod
    def _build_rtree_for_lines(lines_in, tol):
        bboxes = []
        tree = rg.RTree()
        for i, ln in enumerate(lines_in):
            bb = ln.BoundingBox
            if not bb.IsValid:
                bb = rg.BoundingBox(ln.From, ln.To)
            bb.Inflate(tol)
            bboxes.append(bb)
            tree.Insert(bb, i)
        return tree, bboxes

    @staticmethod
    def _snap01(p, tol):
        if p < 0.0 + tol:
            return 0.0
        if p > 1.0 - tol:
            return 1.0
        return p

    @staticmethod
    def _in01(p, include_endpoints, tol):
        if include_endpoints:
            if p >= 0.0 and p <= 1.0:
                return True
            return False
        else:
            if p > tol and p < 1.0 - tol:
                return True
            return False

    @staticmethod
    def _closest_param_and_dist(ln, pt):
        a = ln.From
        b = ln.To
        dx = b.X - a.X
        dy = b.Y - a.Y
        dz = b.Z - a.Z
        vx = pt.X - a.X
        vy = pt.Y - a.Y
        vz = pt.Z - a.Z
        denom = dx*dx + dy*dy + dz*dz
        if denom <= 0.0:
            return 0.0, pt.DistanceTo(a)
        t = (vx*dx + vy*dy + vz*dz) / denom
        if t < 0.0:
            t = 0.0
        if t > 1.0:
            t = 1.0
        cx = a.X + t*dx
        cy = a.Y + t*dy
        cz = a.Z + t*dz
        dx2 = pt.X - cx
        dy2 = pt.Y - cy
        dz2 = pt.Z - cz
        d = math.sqrt(dx2*dx2 + dy2*dy2 + dz2*dz2)
        return t, d

    @staticmethod
    def _snap_point_to_unique(pt, uniq_pts, tol):
        best = None
        bestd2 = None
        r2 = tol * tol
        for q in uniq_pts:
            dx = q.X - pt.X
            dy = q.Y - pt.Y
            dz = q.Z - pt.Z
            d2 = dx*dx + dy*dy + dz*dz
            if d2 <= r2:
                if best is None or d2 < bestd2:
                    best = q
                    bestd2 = d2
        if best is None:
            return pt
        return best

    @staticmethod
    def split_lines_at_intersections(lines_in, tol=0.01, include_endpoints=False):
        if not lines_in:
            return []

        n = len(lines_in)
        paramdict = {}
        for i in range(n):
            paramdict[i] = []

        rtree, bboxes = LineUtils._build_rtree_for_lines(lines_in, tol)
        idxs = range(n)

        for i in idxs:
            li = lines_in[i]
            bbox = bboxes[i]
            candidate_indices = []

            def search_cb(sender, e):
                j = e.Id
                if j <= i:
                    return
                candidate_indices.append(j)

            rtree.Search(bbox, search_cb)

            for j in candidate_indices:
                lj = lines_in[j]
                rc, a, b = rg.Intersect.Intersection.LineLine(li, lj, tol, True)
                if rc:
                    a = LineUtils._snap01(a, tol)
                    b = LineUtils._snap01(b, tol)
                    if LineUtils._in01(a, include_endpoints, tol):
                        paramdict[i].append(a)
                    if LineUtils._in01(b, include_endpoints, tol):
                        paramdict[j].append(b)

        out = []
        for i in idxs:
            ln = lines_in[i]
            if paramdict[i]:
                segs = LineUtils._split_line_at_params(ln, paramdict[i], tol)
                if segs:
                    for s in segs:
                        if s.IsValid and s.Length > tol:
                            out.append(s)
            else:
                if ln.IsValid and ln.Length > tol:
                    out.append(ln)

        if not out:
            return out

        ptTol = tol * 0.25
        if ptTol > 1e-6:
            ptTol = 1e-6
        if ptTol <= 0.0:
            ptTol = 1e-9

        pts = []
        for ln in out:
            pts.append(ln.From)
            pts.append(ln.To)

        uniq_arr = rg.Point3d.CullDuplicates(pts, ptTol)
        uniq_pts = []
        if uniq_arr:
            for p in uniq_arr:
                uniq_pts.append(p)
        else:
            uniq_pts = pts

        rebuilt = []
        for ln in out:
            p0o = ln.From
            p1o = ln.To
            p0s = LineUtils._snap_point_to_unique(p0o, uniq_pts, ptTol)
            p1s = LineUtils._snap_point_to_unique(p1o, uniq_pts, ptTol)
            if p0s.DistanceTo(p1s) <= ptTol:
                rebuilt.append(rg.Line(p0o, p1o))
            else:
                rebuilt.append(rg.Line(p0s, p1s))

        final_lines = []
        for ln in rebuilt:
            L = ln.Length
            if L <= tol:
                continue
            param_eps = ptTol / L
            if param_eps > 0.49:
                param_eps = 0.49
            if param_eps < 1e-9:
                param_eps = 1e-9

            params = []
            for pt in uniq_pts:
                t, d = LineUtils._closest_param_and_dist(ln, pt)
                if d <= ptTol:
                    t = LineUtils._snap01(t, param_eps)
                    if t > param_eps and t < 1.0 - param_eps:
                        params.append(t)

            if params:
                params.sort()
                cleaned = []
                for tk in params:
                    if not cleaned:
                        cleaned.append(tk)
                    else:
                        if abs(tk - cleaned[-1]) > param_eps:
                            cleaned.append(tk)
                segs = LineUtils._split_line_at_params(ln, cleaned, tol)
                if segs:
                    for s in segs:
                        if s.IsValid and s.Length > tol:
                            final_lines.append(s)
                else:
                    if ln.IsValid and ln.Length > tol:
                        final_lines.append(ln)
            else:
                if ln.IsValid and ln.Length > tol:
                    final_lines.append(ln)

        return final_lines

    @staticmethod
    def build_collinear_polylines_sweep(lines_in, tol=GLOBAL_TOL, angle_deg=1.0):
        """
        line sweep algorithm to join touching close enough angled lines into a polyline
        """
        result = []
        if not lines_in:
            return result
    
        rad = angle_deg * math.pi / 180.0
        cos_thr = math.cos(rad)
        pts = []
        for ln in lines_in:
            if not ln or not ln.IsValid:
                continue
            if ln.Length <= tol:
                continue
            pts.append(ln.From)
            pts.append(ln.To)
    
        uniq_arr = rg.Point3d.CullDuplicates(pts, tol)
        uniq_pts = []
        if uniq_arr:
            for p in uniq_arr:
                uniq_pts.append(p)
        else:
            for p in pts:
                uniq_pts.append(p)
    
        snapped = []
        for ln in lines_in:
            if not ln or not ln.IsValid:
                continue
            if ln.Length <= tol:
                continue
            a = LineUtils._snap_point_to_unique(ln.From, uniq_pts, tol)
            b = LineUtils._snap_point_to_unique(ln.To, uniq_pts, tol)
            if a.DistanceTo(b) <= tol:
                continue
            snapped.append((a, b, ln))
    
        if not snapped:
            return result
    
        pindex = {}
        for i, p in enumerate(uniq_pts):
            key = (p.X, p.Y, p.Z)
            pindex[key] = i
    
        edges = []
        for a, b, ln in snapped:
            ia = pindex[(a.X, a.Y, a.Z)]
            ib = pindex[(b.X, b.Y, b.Z)]
            edges.append((ia, ib, a, b))
    
        adj = {}
        for i in range(len(uniq_pts)):
            adj[i] = []
        for k, e in enumerate(edges):
            ia, ib, a, b = e
            adj[ia].append(k)
            adj[ib].append(k)
    
        used = [False for _ in edges]
        seeds = []
        for k, e in enumerate(edges):
            ia, ib, a, b = e
            minx = a.X if a.X <= b.X else b.X
            miny = a.Y if a.Y <= b.Y else b.Y
            seeds.append((minx, miny, k))
        seeds.sort()
    
        def unit_vec(p, q):
            vx = q.X - p.X
            vy = q.Y - p.Y
            vz = q.Z - p.Z
            L = math.sqrt(vx*vx + vy*vy + vz*vz)
            if L <= 0.0:
                return (0.0, 0.0, 0.0)
            return (vx / L, vy / L, vz / L)
    
        def dot_abs(u, v):
            d = u[0]*v[0] + u[1]*v[1] + u[2]*v[2]
            if d < 0.0:
                d = -d
            return d
    
        for _, _, seed_k in seeds:
            if used[seed_k]:
                continue
    
            ia, ib, pa, pb = edges[seed_k]
            u0 = unit_vec(pa, pb)
            poly_pts = [pa, pb]
            used[seed_k] = True
            start_id = ia
            end_id = ib
    
            for _ in range(len(edges)):
                best_k = None
                best_side = None
                best_dot = None
                for ek in adj[end_id]:
                    if used[ek]:
                        continue
                    eia, eib, ea, eb = edges[ek]
                    if eia == end_id:
                        ud = unit_vec(ea, eb)
                        d = dot_abs(u0, ud)
                        if d >= cos_thr:
                            if best_k is None or d > best_dot:
                                best_k = ek
                                best_side = 'end_forward'
                                best_dot = d
                    elif eib == end_id:
                        ud = unit_vec(eb, ea)
                        d = dot_abs(u0, ud)
                        if d >= cos_thr:
                            if best_k is None or d > best_dot:
                                best_k = ek
                                best_side = 'end_backward'
                                best_dot = d
                if best_k is None:
                    break
                eia, eib, ea, eb = edges[best_k]
                if best_side == 'end_forward':
                    poly_pts.append(eb)
                    end_id = eib
                else:
                    poly_pts.append(ea)
                    end_id = eia
                used[best_k] = True
    
            for _ in range(len(edges)):
                best_k = None
                best_side = None
                best_dot = None
                for ek in adj[start_id]:
                    if used[ek]:
                        continue
                    eia, eib, ea, eb = edges[ek]
                    if eib == start_id:
                        ud = unit_vec(ea, eb)
                        d = dot_abs(u0, ud)
                        if d >= cos_thr:
                            if best_k is None or d > best_dot:
                                best_k = ek
                                best_side = 'start_backward'
                                best_dot = d
                    elif eia == start_id:
                        ud = unit_vec(eb, ea)
                        d = dot_abs(u0, ud)
                        if d >= cos_thr:
                            if best_k is None or d > best_dot:
                                best_k = ek
                                best_side = 'start_forward'
                                best_dot = d
                if best_k is None:
                    break
                eia, eib, ea, eb = edges[best_k]
                if best_side == 'start_backward':
                    poly_pts.insert(0, ea)
                    start_id = eia
                else:
                    poly_pts.insert(0, eb)
                    start_id = eib
                used[best_k] = True
    
            if len(poly_pts) >= 2:
                pl = rg.Polyline(poly_pts)
                if pl.IsValid and pl.Length > tol:
                    result.append(pl)
    
        return result

    @staticmethod
    def fit_weighted_line_from_polyline(pl, tol=GLOBAL_TOL, max_iter=25):
        """
        used to rebuild a jittery polyline which is supposed to be an axis into a single line
        """
        if pl is None:
            return rg.Line(rg.Point3d(0.0, 0.0, 0.0), rg.Point3d(0.0, 0.0, 0.0))
        if not hasattr(pl, 'Count'):
            return rg.Line(rg.Point3d(0.0, 0.0, 0.0), rg.Point3d(0.0, 0.0, 0.0))
        n = pl.Count
        if n < 2:
            return rg.Line(rg.Point3d(0.0, 0.0, 0.0), rg.Point3d(0.0, 0.0, 0.0))
    
        sum_w = 0.0
        cx = 0.0
        cy = 0.0
        cz = 0.0
        i = 0
        while i < n - 1:
            p = pl[i]
            q = pl[i + 1]
            L = p.DistanceTo(q)
            if L > tol:
                mx = 0.5 * (p.X + q.X)
                my = 0.5 * (p.Y + q.Y)
                mz = 0.5 * (p.Z + q.Z)
                sum_w += L
                cx += L * mx
                cy += L * my
                cz += L * mz
            i += 1
        if sum_w <= 0.0:
            a = pl[0]
            b = pl[n - 1]
            return rg.Line(a, b)
    
        cx /= sum_w
        cy /= sum_w
        cz /= sum_w
        C = rg.Point3d(cx, cy, cz)
    
        sxx = 0.0
        sxy = 0.0
        sxz = 0.0
        syy = 0.0
        syz = 0.0
        szz = 0.0
        i = 0
        while i < n - 1:
            p = pl[i]
            q = pl[i + 1]
            L = p.DistanceTo(q)
            if L > tol:
                mx = 0.5 * (p.X + q.X)
                my = 0.5 * (p.Y + q.Y)
                mz = 0.5 * (p.Z + q.Z)
                dx = mx - cx
                dy = my - cy
                dz = mz - cz
                sxx += L * dx * dx
                sxy += L * dx * dy
                sxz += L * dx * dz
                syy += L * dy * dy
                syz += L * dy * dz
                szz += L * dz * dz
            i += 1
    
        vx = pl[n - 1].X - pl[0].X
        vy = pl[n - 1].Y - pl[0].Y
        vz = pl[n - 1].Z - pl[0].Z
        vL = math.sqrt(vx*vx + vy*vy + vz*vz)
        if vL <= 0.0:
            vx = 1.0
            vy = 0.0
            vz = 0.0
            vL = 1.0
        vx /= vL
        vy /= vL
        vz /= vL
    
        k = 0
        eps = 1e-12
        while k < max_iter:
            nx = sxx * vx + sxy * vy + sxz * vz
            ny = sxy * vx + syy * vy + syz * vz
            nz = sxz * vx + syz * vy + szz * vz
            nL = math.sqrt(nx*nx + ny*ny + nz*nz)
            if nL <= eps:
                break
            nx /= nL
            ny /= nL
            nz /= nL
            dvx = nx - vx
            dvy = ny - vy
            dvz = nz - vz
            dL = math.sqrt(dvx*dvx + dvy*dvy + dvz*dvz)
            vx = nx
            vy = ny
            vz = nz
            if dL <= 1e-6:
                break
            k += 1
    
        if k == 0 and nL <= eps:
            sx = 0.0
            sy = 0.0
            sz = 0.0
            i = 0
            while i < n - 1:
                p = pl[i]
                q = pl[i + 1]
                L = p.DistanceTo(q)
                if L > tol:
                    sx += (q.X - p.X)
                    sy += (q.Y - p.Y)
                    sz += (q.Z - p.Z)
                i += 1
            vL = math.sqrt(sx*sx + sy*sy + sz*sz)
            if vL <= 0.0:
                a = pl[0]
                b = pl[n - 1]
                return rg.Line(a, b)
            vx = sx / vL
            vy = sy / vL
            vz = sz / vL
    
        a = pl[0]
        b = pl[n - 1]
        ax = a.X - cx
        ay = a.Y - cy
        az = a.Z - cz
        bx = b.X - cx
        by = b.Y - cy
        bz = b.Z - cz
        ta = ax*vx + ay*vy + az*vz
        tb = bx*vx + by*vy + bz*vz
        A = rg.Point3d(cx + ta*vx, cy + ta*vy, cz + ta*vz)
        B = rg.Point3d(cx + tb*vx, cy + tb*vy, cz + tb*vz)
        if A.DistanceTo(B) <= tol:
            return rg.Line(pl[0], pl[n - 1])
        return rg.Line(A, B)

    @staticmethod
    def extend_lines_to_touch_others(lines_in, tol=GLOBAL_TOL):
        """
        takes a list of lines as input and for every line it check it's endpoints 
        if they are within tolerance of some other line (be it endpoint or just on the line) 
        if yes, than rebuild that line extending that point so that it lies exactly 
        on that other line (treat lines as finite)
        """
        out = []
        if not lines_in:
            return out
        tree, bboxes = LineUtils._build_rtree_for_lines(lines_in, tol)
        n = len(lines_in)
        for i in range(n):
            ln = lines_in[i]
            if not ln or not ln.IsValid:
                continue
            if ln.Length <= tol:
                continue
            p0 = ln.From
            p1 = ln.To
            q0 = p0
            q1 = p1
    
            def best_target(pt, self_index):
                best_j = -1
                best_t = 0.0
                best_d = None
                bb = rg.BoundingBox(rg.Point3d(pt.X - tol, pt.Y - tol, pt.Z - tol), rg.Point3d(pt.X + tol, pt.Y + tol, pt.Z + tol))
                cand = []
                def cb(sender, e):
                    if e.Id != self_index:
                        cand.append(e.Id)
                tree.Search(bb, cb)
                k = 0
                while k < len(cand):
                    j = cand[k]
                    lj = lines_in[j]
                    t, d = LineUtils._closest_param_and_dist(lj, pt)
                    if d <= tol:
                        if best_d is None or d < best_d:
                            best_d = d
                            best_j = j
                            best_t = t
                    k += 1
                if best_j == -1:
                    return None
                lj = lines_in[best_j]
                tgt = lj.PointAt(best_t)
                if tgt.DistanceTo(lj.From) <= tol:
                    return lj.From
                if tgt.DistanceTo(lj.To) <= tol:
                    return lj.To
                return tgt
    
            tgt0 = best_target(p0, i)
            if tgt0 is not None:
                q0 = tgt0
            tgt1 = best_target(p1, i)
            if tgt1 is not None:
                q1 = tgt1
    
            if q0.DistanceTo(q1) > tol:
                out.append(rg.Line(q0, q1))
            else:
                out.append(ln)
        return out
    
    
    @staticmethod
    def snap_polylines_points_to_lines(polylines_in, lines_in, tol=GLOBAL_TOL, keepempty = False):
        """
        takes a list of polyline and a list of lines for every point in that polyline 
        (not rebuilding the polyline itself, keeping it as is) first search if that 
        point is within tolerance of any of those lines endpoint, if so move it there, 
        if not check if the point is within tolerance of any line itself (finite portion) 
        if yes pull it to that line (closest if multiple hit)
        """
        out = []
        if not polylines_in:
            return out
        if not lines_in:
            for pl in polylines_in:
                if pl and pl.IsValid:
                    out.append(pl)
            return out
    
        tree, bboxes = LineUtils._build_rtree_for_lines(lines_in, tol)
        endpoints = []
        j = 0
        while j < len(lines_in):
            ln = lines_in[j]
            if ln and ln.IsValid:
                endpoints.append(ln.From)
                endpoints.append(ln.To)
            j += 1
        uniq_arr = rg.Point3d.CullDuplicates(endpoints, tol)
        uniq_endpts = []
        if uniq_arr:
            i = 0
            while i < len(uniq_arr):
                uniq_endpts.append(uniq_arr[i])
                i += 1
        else:
            i = 0
            while i < len(endpoints):
                uniq_endpts.append(endpoints[i])
                i += 1
    
        def closest_endpoint(pt):
            best = None
            bestd2 = None
            i = 0
            r2 = tol * tol
            while i < len(uniq_endpts):
                q = uniq_endpts[i]
                dx = q.X - pt.X
                dy = q.Y - pt.Y
                dz = q.Z - pt.Z
                d2 = dx*dx + dy*dy + dz*dz
                if d2 <= r2:
                    if best is None or d2 < bestd2:
                        best = q
                        bestd2 = d2
                i += 1
            return best
    
        def closest_on_any_line(pt):
            best = None
            bestd = None
            bb = rg.BoundingBox(rg.Point3d(pt.X - tol, pt.Y - tol, pt.Z - tol), rg.Point3d(pt.X + tol, pt.Y + tol, pt.Z + tol))
            cand = []
            def cb(sender, e):
                cand.append(e.Id)
            tree.Search(bb, cb)
            i = 0
            while i < len(cand):
                idx = cand[i]
                ln = lines_in[idx]
                t, d = LineUtils._closest_param_and_dist(ln, pt)
                if d <= tol:
                    q = ln.PointAt(t)
                    if best is None or d < bestd:
                        best = q
                        bestd = d
                i += 1
            return best
    
        for pl in polylines_in:
            if not pl or not pl.IsValid:
                if keepempty:
                    out.append(None)
                continue
            pts = []
            for i in range(pl.Count):
                p = pl[i]
                ep = closest_endpoint(p)
                if ep is not None:
                    pts.append(ep)
                else:
                    q = closest_on_any_line(p)
                    if q is not None:
                        pts.append(q)
                    else:
                        pts.append(p)
            newpl = rg.Polyline(pts)
            out.append(newpl)
        return out


    @staticmethod
    def vector_between_lines(line1, line2, tol=GLOBAL_TOL):
        """
        Return the shortest vector to move line1 (as infinite) onto line2 (as infinite).
        """
        p1 = line1.From
        p2 = line2.From
        v  = line2.Direction
        w0 = p1 - p2
        t  = (v * w0) / (v * v)
        projection = p2 + v * t
        return projection - p1

    @staticmethod
    def push_line(line, axis, rects):
        """
        Translates a line out of overlapping rectangles in one step:
        vertical lines move horizontally, horizontal lines move vertically.
        """
        # normalize axis so that callers can provide orientation names or axes
        axis_key = axis
        try:
            string_types = (basestring,)  # type: ignore[name-defined]
        except NameError:  # Python 3
            string_types = (str,)
        if isinstance(axis_key, string_types):
            axis_key = axis_key.lower()
        if axis_key in ('vertical', LineUtils.Orientation.VERTICAL):
            axis_key = 'x'
        elif axis_key in ('horizontal', LineUtils.Orientation.HORIZONTAL):
            axis_key = 'y'

        if axis_key not in ('x', 'y'):
            return rg.Vector3d(0, 0, 0)

        # determine which orientation defines the domain we need to test
        perp_orientation = (LineUtils.Orientation.VERTICAL if axis_key == 'x'
                            else LineUtils.Orientation.HORIZONTAL)
        domain = LineUtils.get_domain(line, perp_orientation)

        # midpoint coordinate along the axis we are translating on
        center = (LineUtils.get_position(line, LineUtils.Orientation.VERTICAL)
                  if axis_key == 'x'
                  else LineUtils.get_position(line, LineUtils.Orientation.HORIZONTAL))

        intervals = []
        for r in rects:
            o = r.Plane.Origin
            if axis_key == 'x':
                perp_int = (o.Y + r.Y.Min, o.Y + r.Y.Max)
                axis_int = (o.X + r.X.Min, o.X + r.X.Max)
            else:
                perp_int = (o.X + r.X.Min, o.X + r.X.Max)
                axis_int = (o.Y + r.Y.Min, o.Y + r.Y.Max)
            if LineUtils.domains_overlap(domain, perp_int):
                intervals.append((min(axis_int), max(axis_int)))

        if not intervals:
            return rg.Vector3d(0, 0, 0)

        merged = LineUtils.merge_intervals(intervals)

        push = 0.0
        for idx, (u_min, u_max) in enumerate(merged):
            if center + GLOBAL_TOL < u_min or center - GLOBAL_TOL > u_max:
                continue

            # compute offsets needed to exit on either side of the interval
            left_target = u_min - GLOBAL_TOL
            right_target = u_max + GLOBAL_TOL
            left_offset = left_target - center
            right_offset = right_target - center

            # choose direction requiring the least translation magnitude
            if abs(left_offset) <= abs(right_offset):
                push = left_offset
            else:
                push = right_offset
            break

        if axis_key == 'x':
            return rg.Vector3d(push, 0, 0)
        return rg.Vector3d(0, push, 0)

    @staticmethod
    def push_line_constrained(line, axis, rects, minpar, maxpar, bestpar = 0):
        """
        Translates a line out of overlapping rectangles in one step:
        vertical lines move horizontally, horizontal lines move vertically.
        Will not push outside constraints, if the target push goes beyond
        constraints will fallback on bestparameter or fallback to 0 if abscent
        """
        #for debugging
        # override axis: vertical lines -> horizontal movement, else -> vertical
        #axis = 'x' if LineUtils.is_vertical(line) else 'y'
        if axis == 'x':
            perp_orient = 'vertical'
        else: 
            perp_orient = 'horizontal'
        
        #bestpar = None
        # domain on the perpendicular axis
        domain = LineUtils.get_domain(line, perp_orient)
        # center coordinate on the movement axis
        c = (line.From.X + line.To.X) / 2.0 if axis == 'x' else (line.From.Y + line.To.Y) / 2.0

        # collect movement‐axis intervals from rects overlapping in perp domain
        intervals = []
        for r in rects:
            o = r.Plane.Origin
            if axis == 'x':
                perp_int = (o.Y + r.Y.Min, o.Y + r.Y.Max)
                axis_int = (o.X + r.X.Min, o.X + r.X.Max)
            else:
                perp_int = (o.X + r.X.Min, o.X + r.X.Max)
                axis_int = (o.Y + r.Y.Min, o.Y + r.Y.Max)
            if LineUtils.domains_overlap(domain, perp_int):
                intervals.append(axis_int)
        
        pushvector = rg.Vector3d(0, 0, 0)
        
        # merge and find containing interval
        for u_min, u_max in LineUtils.merge_intervals(intervals):
            if c > u_min + GLOBAL_TOL and c < u_max - GLOBAL_TOL:
                off = 0
                if abs(u_min - c) < abs(u_max - c):
                    off = (u_min - c) 
                else:
                    off = (u_max - c)
                
                if axis == 'x':
                    parameter = line.From.X
                    moved = parameter+off

                    if moved < maxpar and moved > minpar:
                        pushvector = rg.Vector3d(off, 0, 0)
                    elif moved >= maxpar:
                        if bestpar:
                            offset = moved-bestpar
                        else:
                            offset = moved-maxpar
                        pushvector = rg.Vector3d(off - offset, 0, 0)

                    elif moved <= minpar:
                        if bestpar:
                            offset = moved-bestpar
                        else:
                            offset = moved-minpar
                        pushvector = rg.Vector3d(off - offset, 0, 0)

                else: #if "y"
                    parameter = line.From.Y
                    moved = parameter+off

                    if moved < maxpar and moved > minpar:
                        pushvector = rg.Vector3d(0, off, 0)
                    elif moved >= maxpar:
                        if bestpar:
                            offset = moved-bestpar
                        else:
                            offset = moved-maxpar
                        pushvector = rg.Vector3d(0, off - offset, 0)

                    elif moved <= minpar:
                        if bestpar:
                            offset = moved-bestpar
                        else:
                            offset = moved-minpar
                        pushvector = rg.Vector3d(0, off - offset, 0)
                
                break

        # no overlap -> no move
        return pushvector

    @staticmethod
    def push_lines_onepass(lines, rects, axis='x', spacebuffer_value=5.0, tol=GLOBAL_TOL):
        """
        One‑pass, center‑out resolver that moves all parallel segments together,
        preserving order and respecting no‑fly rectangles.
        Minimal spacing between neighbors = min(original_gap, spacebuffer_value).
        axis: 'x' -> move in X (vertical lines), 'y' -> move in Y (horizontal lines)
        Returns list[rg.Vector3d] in the same order as 'lines'.
        """
        if not lines:
            return []

        # Movement axis and PERPENDICULAR orientation (critical fix)
        if axis == 'x':
            # vertical lines move in X -> use Y domain for overlap tests
            def pos(ln):  # center on X
                return (ln.From.X + ln.To.X) * 0.5
            def dom_perp(ln):  # Y-interval
                y0, y1 = ln.From.Y, ln.To.Y
                return (y0, y1) if y0 <= y1 else (y1, y0)
        else:
            # horizontal lines move in Y -> use X domain for overlap tests
            def pos(ln):  # center on Y
                return (ln.From.Y + ln.To.Y) * 0.5
            def dom_perp(ln):  # X-interval
                x0, x1 = ln.From.X, ln.To.X
                return (x0, x1) if x0 <= x1 else (x1, x0)

        # Per‑line data
        n = len(lines)
        positions = [pos(ln) for ln in lines]
        domains   = [dom_perp(ln) for ln in lines]

        # For each line, collect union of movement‑axis intervals from rects
        # whose PERP interval overlaps the line’s PERP domain
        def _merge(ints):
            return LineUtils.merge_intervals(ints, tol) if ints else []

        covers = [[] for _ in range(n)]
        for i in range(n):
            ivs = []
            dperp_lo, dperp_hi = domains[i]
            for r in rects:
                o = r.Plane.Origin
                if axis == 'x':
                    # vertical move: perp=Y, axis=X
                    perp_iv = (o.Y + r.Y.Min, o.Y + r.Y.Max)
                    axis_iv = (o.X + r.X.Min, o.X + r.X.Max)
                else:
                    # horizontal move: perp=X, axis=Y
                    perp_iv = (o.X + r.X.Min, o.X + r.X.Max)
                    axis_iv = (o.Y + r.Y.Min, o.Y + r.Y.Max)
                # overlap test on PERP axis
                if (dperp_hi + tol >= min(perp_iv) and dperp_lo <= max(perp_iv) + tol):
                    a0, a1 = axis_iv
                    if a1 < a0:
                        a0, a1 = a1, a0
                    ivs.append((a0, a1))
            covers[i] = _merge(ivs)

        # Partition into components by PERP overlap (sweep)
        idxs = sorted(range(n), key=lambda i: domains[i][0])
        comps = []
        if idxs:
            cur = [idxs[0]]
            cur_max = domains[idxs[0]][1]
            for j in idxs[1:]:
                lo, hi = domains[j]
                if lo <= cur_max + tol:
                    cur.append(j)
                    if hi > cur_max:
                        cur_max = hi
                else:
                    comps.append(cur)
                    cur = [j]
                    cur_max = hi
            comps.append(cur)

        # Utilities to clear out of a merged union in one step
        def _contains(ints, u):
            for a, b in ints:
                if u >= a - tol and u <= b + tol:
                    return (a, b)
            return None
        def _clear_left(i_idx, x):
            iv = _contains(covers[i_idx], x)
            return (iv[0] - tol) if iv is not None else x
        def _clear_right(i_idx, x):
            iv = _contains(covers[i_idx], x)
            return (iv[1] + tol) if iv is not None else x

        offsets = [0.0] * n

        for comp in comps:
            comp_sorted = sorted(comp, key=lambda i: positions[i])
            x0   = [positions[i] for i in comp_sorted]
            xnew = list(x0)
            m = len(comp_sorted)
            
            if m == 0:
                continue

            # Neighbor spacing = min(original gap, spacebuffer_value)
            dmin = [min(x0[k+1] - x0[k], spacebuffer_value) for k in range(m - 1)]

            # Center‑out deterministic order (alternate sides)
            order = []
            if m % 2 == 1:
                mid = m // 2
                order.append(mid)
                for d in range(1, m):
                    r = mid + d
                    l = mid - d
                    if r < m:
                        order.append(r)
                    if l >= 0:
                        order.append(l)
            else:
                left = (m // 2) - 1
                right = (m // 2)
                order.extend([left, right])
                for d in range(1, m):
                    r = right + d
                    l = left - d
                    if r < m:
                        order.append(r)
                    if l >= 0:
                        order.append(l)

            # Process center‑out
            for j in order:
                i_idx = comp_sorted[j]
                cur   = xnew[j]
                iv    = _contains(covers[i_idx], cur)
                if iv is None:
                    continue

                # Cheapest initial escape (ties -> left)
                left_target  = iv[0] - tol
                right_target = iv[1] + tol
                left_cost    = cur - left_target
                right_cost   = right_target - cur

                if left_cost <= right_cost:
                    xnew[j] = _clear_left(i_idx, left_target)
                    # chain left
                    for k in range(j - 1, -1, -1):
                        need   = dmin[k]
                        target = xnew[k + 1] - need
                        if xnew[k] > target:
                            xnew[k] = target
                        idk = comp_sorted[k]
                        xnew[k] = _clear_left(idk, xnew[k])
                else:
                    xnew[j] = _clear_right(i_idx, right_target)
                    # chain right
                    for k in range(j + 1, m):
                        need   = dmin[k - 1]
                        target = xnew[k - 1] + need
                        if xnew[k] < target:
                            xnew[k] = target
                        idk = comp_sorted[k]
                        xnew[k] = _clear_right(idk, xnew[k])

            # write back offsets
            for j, idx in enumerate(comp_sorted):
                offsets[idx] = xnew[j] - x0[j]

        # Build vectors in original order
        if axis == 'x':
            return [rg.Vector3d(offsets[i], 0.0, 0.0) for i in range(n)]
        else:
            return [rg.Vector3d(0.0, offsets[i], 0.0) for i in range(n)]

    @staticmethod
    def push_verticals_onepass(lines, rects, spacebuffer_value=5.0, tol=GLOBAL_TOL):
        return LineUtils.push_lines_onepass(lines, rects, axis='x',
                                            spacebuffer_value=spacebuffer_value, tol=tol)

    @staticmethod
    def push_horizontals_onepass(lines, rects, spacebuffer_value=5.0, tol=GLOBAL_TOL):
        return LineUtils.push_lines_onepass(lines, rects, axis='y',
                                            spacebuffer_value=spacebuffer_value, tol=tol)

    @staticmethod
    def lxl(line, lines, tol=GLOBAL_TOL):
        """
        Checks whether a finite line intersects any line in a list within a
        given tolerance, returning True on the first valid interior
        intersection. The tolerance can be optionally specified.
        """
        flag = False
        
        for l in lines:
            bool, p1, p2 = rg.Intersect.Intersection.LineLine(line, l, tol, True) #finite

            if bool:
                if p1 < 1.0 - tol and p1 > tol:
                    flag =True
                    break
        return flag
    
    @staticmethod
    def lxb(line, boxes, infinite = False):
        """
        Determines if a line intersects any Box in a list by testing overlapping
        parametric intervals,
        returning True if any hit occurs.
        """
        boxhit = False
       
        for box in boxes:
            #this treats line as infinite, so hits are not the only parameter to judge 
            #intersections
            bhit, interval = rg.Intersect.Intersection.LineBox(line, box, 0.0)
            #ist, iend = interval
            #smaller = min(ist, iend)
            #inint = smaller > 0.0 and smaller < 1.0 #in interval
            inint = LineUtils.domains_overlap(rg.Interval(0.0, 1.0), interval)
            
            if bhit:
                if infinite or inint:
                    boxhit = True
                    break
        #return False
        return boxhit
    
    #Rhinocommon only has line x box
    @staticmethod
    def lxr(line, rectangles, infinite = False):
        """
        Tests intersection between a line and Rectangle3d list,
        returning True if any hit occurs.
        """
        boxes = map(LineUtils.rectangle_to_box, rectangles)
        return LineUtils.lxb(line, boxes, infinite)

    @staticmethod
    def poly_hits_rects(polyline, rectangles):
        """
        Returns True if any finite segment of the polyline intersects
        any of the given Rectangle3d objects
        """
        if polyline is None:
            return False
        if not rectangles:
            return False
        for i in range(polyline.SegmentCount):
            seg = polyline.SegmentAt(i)
            if LineUtils.lxr(seg, rectangles):
                return True
        return False

    @staticmethod
    def line_inside_percentage(line, rectangles):
        """
        Calculates the percentage of a line's length that lies strictly within any
        given Rectangle3d objects, returning a float 0.0–100.0.
        """
        if line.Length <= 0:
            return 0.0

        intervals = []
        seg_dom = rg.Interval(0.0, 1.0)

        for rect in rectangles:
            box = LineUtils.rectangle_to_box(rect, thickness=10.0)
            hit, iv = rg.Intersect.Intersection.LineBox(line, box, GLOBAL_TOL)
            if not hit:
                continue
            t0, t1 = iv.Min, iv.Max
            lo = max(seg_dom.Min, min(t0, t1))
            hi = min(seg_dom.Max, max(t0, t1))
            if hi > lo + GLOBAL_TOL:
                intervals.append((lo, hi))

        merged = LineUtils.merge_intervals(intervals)
        covered = sum(b - a for a, b in merged)
        return (covered * 100.0)

    @staticmethod
    def filter_same_direction(line, lines, tol=GLOBAL_TOL):
        """
        Returns a list of booleans indicating if each line in 'lines' shares the
        general direction of 'line', ignoring sign. Uses dot product with tolerance
        to determine near-parallelism.
        """
        # get unit direction of reference line
        d0 = line.Direction
        d0.Unitize()
        flags = []
        for l in lines:
            # unit direction of test line
            d = l.Direction
            d.Unitize()
            # absolute dot gives 1.0 for parallel or anti-parallel
            flags.append(abs(d0 * d) >= 1.0 - tol)
        return flags

    @staticmethod
    def filter_by_flag(items, flags):
        """
        Returns only those items whose corresponding flag is True.
        """
        return list(itertools.compress(items, flags))

    @staticmethod
    def is_vertical(line, tol=GLOBAL_TOL):
        """
        Returns True if a line is effectively vertical within a given tolerance.
        """
        return abs(line.From.X - line.To.X) < tol
    
    @staticmethod
    def is_horizontal(line, tol=GLOBAL_TOL):
        """
        Returns True if a line is effectively horizontal within a given tolerance.
        """
        return abs(line.From.Y - line.To.Y) < tol

    @staticmethod
    def orientation_of_line(line, tol=GLOBAL_TOL):
        """
        Return Orientation constant for a line.
        """
        if LineUtils.is_vertical(line, tol):
            return LineUtils.Orientation.VERTICAL
        if LineUtils.is_horizontal(line, tol):
            return LineUtils.Orientation.HORIZONTAL
        return LineUtils.Orientation.NONORTH

    @staticmethod
    def get_position(line, orientation):
        """
        Calculates the midpoint coordinate of a line along the specified orientation
        (“vertical” or “horizontal”).
        """
        if orientation == LineUtils.Orientation.VERTICAL:
            return (line.From.X + line.To.X) / 2.0
        elif orientation == LineUtils.Orientation.HORIZONTAL:
            return (line.From.Y + line.To.Y) / 2.0
        return 0.0
    
    @staticmethod
    def get_domain(line, orientation):
        """
        Returns the sorted [min, max] coordinates of a line along the specified
        orientation (“vertical” or “horizontal”).
        """
        if orientation == LineUtils.Orientation.VERTICAL:
            return sorted([line.From.Y, line.To.Y])
        elif orientation == LineUtils.Orientation.HORIZONTAL:
            return sorted([line.From.X, line.To.X])
        return [0.0, 0.0]
    
    @staticmethod
    def domains_overlap(d1, d2, tol=1e-6):
        """
        Returns True if two numeric domains overlap within the given tolerance.
        """
        return (d1[1] + tol >= d2[0]) and (d2[1] + tol >= d1[0])
    
    @staticmethod
    def create_line(pos, domain, orientation):
        """
        Constructs a vertical or horizontal line at a fixed coordinate,
        spanning the specified domain (“vertical” or “horizontal”).
        """
        if orientation == LineUtils.Orientation.VERTICAL:
            pt1 = rg.Point3d(pos, domain[0], 0)
            pt2 = rg.Point3d(pos, domain[1], 0)
        elif orientation == LineUtils.Orientation.HORIZONTAL:
            pt1 = rg.Point3d(domain[0], pos, 0)
            pt2 = rg.Point3d(domain[1], pos, 0)
        return rg.Line(pt1, pt2)
    
    @staticmethod
    def group_lines(sorted_lines, grouper, orientation, weight_map=None):
        """
        Clusters sorted lines by proximity: lines within grouper distance and
        overlapping domains are merged into groups (“vertical” or “horizontal”).
        """
        groups = []
        for idx, line in sorted_lines:
            pos = LineUtils.get_position(line, orientation)
            dom = LineUtils.get_domain(line, orientation)
            merged = False
            
            # compute this line's weight
            if weight_map:
                weight = weight_map.get(idx, 1.0)
            else:
                weight = 1.0
            
            for g in groups:
                if abs(pos - LineUtils.get_position(g['target'], orientation)) < grouper:
                    if LineUtils.domains_overlap(dom, LineUtils.get_domain(g['target'], orientation)):
                        gdom = LineUtils.get_domain(g['target'], orientation)
                        new_dom = [min(dom[0], gdom[0]), max(dom[1], gdom[1])]
                        
                        # compute the target line's weight
                        tgt_idx = g['target_idx']                              
                        tgt_weight = weight_map.get(tgt_idx, 1.0) if weight_map else 1.0 
                        
                        if line.Length * weight >= g['target'].Length * tgt_weight:   
                            new_pos = pos 
                            g['target_idx'] = idx 
                        else:
                            new_pos = LineUtils.get_position(g['target'], orientation)
                        g['target'] = LineUtils.create_line(new_pos, new_dom, orientation)
                        g['members'].append((idx, line))
                        merged = True
                        break
            if not merged:
                # initialize target_idx for weight lookups
                groups.append({'target': line, 'members': [(idx, line)], 'target_idx': idx})
                
        return groups
    
    @staticmethod
    def transform_line(line, transform):
        """
        Applies a given Transform to a copy of a line.
        """
        tline = rg.Line(line.From, line.To)
        tline.Transform(transform)
        return tline
    
    #try moving origin line and check for intersections before operation
    @staticmethod
    def compute_transform(orig_line, target_line, orientation, avoidrects = []):
        """
        Computes a translation Transform to align one line to another along an
        orientation, optionally avoiding collisions with rectangles.
        """
        checkcollision = len(avoidrects) > 0

        if orientation == LineUtils.Orientation.VERTICAL:
            dx = target_line.From.X - orig_line.From.X
            vec = rg.Vector3d(dx, 0, 0)
            
        elif orientation == LineUtils.Orientation.HORIZONTAL:
            dy = target_line.From.Y - orig_line.From.Y
            vec = rg.Vector3d(0, dy, 0)
        else:
            return rg.Transform.Identity

        translation = rg.Transform.Translation(vec)
        if checkcollision:
            checkline = LineUtils.transform_line(orig_line, translation)
            if not LineUtils.lxr(checkline, avoidrects):
                return translation
            return rg.Transform.Identity
            
        #fallback
        return translation
        
    @staticmethod
    def grouper(lines, grouper, noflies = [], weight_map=None, keyed = False, pull_mode = 0):
        """
        Identifies vertical and horizontal lines and groups them by proximity,
        computes translations to align group members, and returns a list of
        transforms for all lines.

        pull_mode:
            0 - pull to longest (legacy)
            1 - pull to weighted average position of group
            2 - pull to middle (midrange) position of group
        """
        vert = []
        horiz = []
        nonorth = {}
        i = 0
        while i < len(lines):
            line = lines[i]
            if LineUtils.is_vertical(line):
                vert.append((i, line))
            elif LineUtils.is_horizontal(line):
                horiz.append((i, line))
            else:
                nonorth[i] = rg.Transform.Identity
            i += 1

        vert_sorted = sorted(vert, key=lambda x: LineUtils.get_position(x[1], LineUtils.Orientation.VERTICAL))
        horiz_sorted = sorted(horiz, key=lambda x: LineUtils.get_position(x[1], LineUtils.Orientation.HORIZONTAL))

        transforms = {}
        groups_dict = {}
        group_idx = 0

        def _compute_group_target_line(group, orientation):
            if pull_mode == 0:
                return group['target']

            dom_min = None
            dom_max = None
            positions = []
            weights = []
            j = 0
            while j < len(group['members']):
                idx, ln = group['members'][j]
                dom = LineUtils.get_domain(ln, orientation)
                if dom_min is None or dom[0] < dom_min:
                    dom_min = dom[0]
                if dom_max is None or dom[1] > dom_max:
                    dom_max = dom[1]
                pos = LineUtils.get_position(ln, orientation)
                positions.append(pos)

                if weight_map:
                    w = weight_map.get(idx, 1.0)
                else:
                    w = 1.0
                w = w * ln.Length
                weights.append(w)
                j += 1

            if dom_min is None or dom_max is None or not positions:
                return group['target']

            if pull_mode == 1:
                target_pos = LineUtils.weighted_average(positions, weights)
            elif pull_mode == 2:
                min_pos = min(positions)
                max_pos = max(positions)
                target_pos = (min_pos + max_pos) * 0.5
            else:
                target_pos = LineUtils.get_position(group['target'], orientation)

            dom_list = [dom_min, dom_max]
            return LineUtils.create_line(target_pos, dom_list, orientation)

        for g in LineUtils.group_lines(vert_sorted, grouper, LineUtils.Orientation.VERTICAL, weight_map):
            member_ids = []
            target_line = _compute_group_target_line(g, LineUtils.Orientation.VERTICAL)
            k = 0
            while k < len(g['members']):
                idx, orig = g['members'][k]
                transforms[idx] = LineUtils.compute_transform(orig, target_line, LineUtils.Orientation.VERTICAL, noflies)
                member_ids.append(idx)
                k += 1
            groups_dict[group_idx] = member_ids
            group_idx += 1

        for g in LineUtils.group_lines(horiz_sorted, grouper, LineUtils.Orientation.HORIZONTAL, weight_map):
            member_ids = []
            target_line = _compute_group_target_line(g, LineUtils.Orientation.HORIZONTAL)
            k = 0
            while k < len(g['members']):
                idx, orig = g['members'][k]
                transforms[idx] = LineUtils.compute_transform(orig, target_line, LineUtils.Orientation.HORIZONTAL, noflies)
                member_ids.append(idx)
                k += 1
            groups_dict[group_idx] = member_ids
            group_idx += 1

        for key_idx in nonorth:
            transforms[key_idx] = nonorth[key_idx]

        if keyed:
            return transforms, groups_dict
        else:
            return [transforms[i] for i in sorted(transforms.keys())]

    @staticmethod
    def filter_unique_nonzero(values, tol = GLOBAL_TOL):
        """
        Filters a list of numeric values, returning only those non-zero above
        tolerance and unique within tolerance.
        """
        unique = []
        for v in values:
            if abs(v) > tol and not any(abs(v - u) <= tol for u in unique):
                unique.append(v)
        return unique
        
    @staticmethod
    def largest_by_abs(values):
        """
        Returns the value with the greatest absolute magnitude from a list,
        or zero if the list is empty.
        """
        if len(values):
            return max(values, key=abs)
        else:
            return 0.0
            
    @staticmethod
    def consecutive_pairs(lst):
        """
        Converts a list of values into a list of consecutive two-element pairs.
        """
        if len(lst) < 2: return []
        return [[lst[i], lst[i+1]] for i in range(len(lst)-1)]

    @staticmethod
    def weighted_average(values, weights):
        """
        Calculates the weighted average of a list of numeric values given corresponding
        weights, returning a float. If weights sum to zero or lists mismatch, returns 0.0.
        """
        # mismatch or empty -> zero
        if len(values) != len(weights) or not values:
            return 0.0

        total = 0.0
        wsum = 0.0
        for v, w in zip(values, weights):
            total += v * w
            wsum += w

        # avoid division by zero
        if abs(wsum) < GLOBAL_TOL:
            return 0.0

        return total / wsum

    @staticmethod
    def average_point(points):
        """
        Arithmetic mean of a list of rg.Point3d.
        """
        if not points:
            return rg.Point3d(0, 0, 0)

        sx = 0.0
        sy = 0.0
        sz = 0.0
        n = len(points)
        
        for p in points:
            sx += p.X
            sy += p.Y
            sz += p.Z

        return rg.Point3d(sx / n, sy / n, sz / n)

    @staticmethod
    def median_point(points):
        """
        Coordinate-wise median (middle value) of the points.
        """
        if not points:
            return rg.Point3d(0, 0, 0)

        xs = sorted([p.X for p in points])
        ys = sorted([p.Y for p in points])
        zs = sorted([p.Z for p in points])
        n = len(points)
        mid = n // 2

        def _med(arr):
            if n % 2 == 1:
                return arr[mid]
            return (arr[mid - 1] + arr[mid]) * 0.5

        return rg.Point3d(_med(xs), _med(ys), _med(zs))

    @staticmethod
    def midrange_point(points):
        """
        Midpoint of min and max along each axis.
        """
        if not points:
            return rg.Point3d(0, 0, 0)

        xs = [p.X for p in points]
        ys = [p.Y for p in points]
        zs = [p.Z for p in points]

        return rg.Point3d(
            (min(xs) + max(xs)) * 0.5,
            (min(ys) + max(ys)) * 0.5,
            (min(zs) + max(zs)) * 0.5
        )

    @staticmethod
    def geometric_median_point(points, max_iters = 50, tol = GLOBAL_TOL):
        """
        Geometric median: the point minimizing sum of distances to all points.
        Uses Weiszfeld's algorithm; falls back to average if coincident.
        """
        n = len(points)
        if n == 0:
            return rg.Point3d(0, 0, 0)

        # start at the centroid
        current = LineUtils.average_point(points)
        for i in range(max_iters):
            num_x = 0.0
            num_y = 0.0
            num_z = 0.0
            denom = 0.0
            for p in points:
                dx = current.X - p.X
                dy = current.Y - p.Y
                dz = current.Z - p.Z
                dist = math.sqrt(dx * dx + dy * dy + dz * dz)
                if dist < tol:
                    # one point is at current => that's the median
                    return p
                w = 1.0 / dist
                num_x += p.X * w
                num_y += p.Y * w
                num_z += p.Z * w
                denom += w

            next_pt = rg.Point3d(num_x / denom, num_y / denom, num_z / denom)
            move = current.DistanceTo(next_pt)
            current = next_pt
            if move < tol:
                break

        return current

    @staticmethod
    def central_point(points, style="average"):
        """
        Returns a central point of 'points' according to 'style'.
        Styles: "average", "median", "midrange", "geometric"
        """
        if style == "average":
            return LineUtils.average_point(points)
        if style == "median":
            return LineUtils.median_point(points)
        if style == "midrange":
            return LineUtils.midrange_point(points)
        if style == "geometric":
            return LineUtils.geometric_median_point(points)

    @staticmethod
    def create_cells_from_grid(lines, tol=GLOBAL_TOL):
        """
        Build closed cell polylines from a planar line grid.
        Returns a list polylines one per cell.
        """
    
        if not lines:
            return []
    
        segs = LineUtils.split_lines_at_intersections(lines, tol, include_endpoints=True)
        if not segs:
            segs = lines
    
        key_to_pt = {}
        def _key_for_point(pt):
            k = LineUtils._find_point_group2d(key_to_pt, pt.X, pt.Y, tol)
            if k is None:
                k = (pt.X, pt.Y)
                key_to_pt[k] = rg.Point3d(pt.X, pt.Y, 0)
            return k
    
        halfedges = []
        edge_lookup = {}
        verts = {}
    
        for ln in segs:
            a = _key_for_point(ln.From)
            b = _key_for_point(ln.To)
    
            he_ab = {"origin": a, "target": b, "twin": None, "visited": False}
            he_ba = {"origin": b, "target": a, "twin": None, "visited": False}
    
            halfedges.append(he_ab)
            halfedges.append(he_ba)
    
            edge_lookup[(a, b)] = he_ab
            edge_lookup[(b, a)] = he_ba
    
            if a not in verts:
                verts[a] = []
            if b not in verts:
                verts[b] = []
            verts[a].append(he_ab)
            verts[b].append(he_ba)
    
        def _he_angle(he):
            ox, oy = he["origin"]
            tx, ty = he["target"]
            dx = tx - ox
            dy = ty - oy
            ang = math.atan2(dy, dx)
            if ang < 0.0:
                ang = ang + 2.0 * math.pi
            return ang
    
        for v in verts:
            lst = verts[v]
            lst.sort(key=_he_angle)
    
        for he in halfedges:
            twin = edge_lookup.get((he["target"], he["origin"]))
            he["twin"] = twin
    
        def _next_rule(he):
            if he["twin"] is None:
                return None
            v = he["target"]
            lst = verts.get(v)
            if not lst:
                return None
            try:
                idx = lst.index(he["twin"])
            except:
                return None
            if len(lst) == 0:
                return None
            nxt = lst[(idx - 1) % len(lst)]
            return nxt
    
        def _polygon_area(keys):
            area = 0.0
            i = 0
            while i < len(keys) - 1:
                x1 = keys[i][0]
                y1 = keys[i][1]
                x2 = keys[i + 1][0]
                y2 = keys[i + 1][1]
                area = area + (x1 * y2 - x2 * y1)
                i = i + 1
            if area < 0.0:
                area = -area
            return 0.5 * area
    
        faces = []
        for he in halfedges:
            if he["visited"]:
                continue
            if he["twin"] is None:
                continue
    
            face = []
            start = he
            cur = he
            steps = 0
    
            while True:
                he["visited"] = True
                face.append(cur["origin"])
    
                nxt = _next_rule(cur)
                if nxt is None:
                    break
    
                if nxt == start:
                    face.append(start["origin"])
                    break
    
                cur = nxt
                he = cur
                steps = steps + 1
                if steps > 10000:
                    break
    
            if len(face) > 3:
                faces.append(face)
    
        if not faces:
            return []
    
        biggest = None
        biggest_idx = -1
        i = 0
        while i < len(faces):
            a = _polygon_area(faces[i])
            if biggest is None or a > biggest:
                biggest = a
                biggest_idx = i
            i = i + 1
    
        cells = []
        i = 0
        while i < len(faces):
            if i != biggest_idx:
                keys = faces[i]
                if keys[0] != keys[-1]:
                    keys = list(keys)
                    keys.append(keys[0])
    
                pl = rg.Polyline()
                j = 0
                while j < len(keys):
                    k = keys[j]
                    pt = key_to_pt[k]
                    pl.Add(pt)
                    j = j + 1
    
                if pl.Count >= 4:
                    pl.MergeColinearSegments(tol, True)
                    if pl.IsClosed:
                        cells.append(pl)
            i = i + 1
    
        return cells

    @staticmethod
    def unique_points(points, tol=1e-8):
        """
        Return unique 2D points (XY plane) within a given tolerance.
        """
        unique = []
        for p in points:
            if not any(abs(p.X - q.X) < tol and abs(p.Y - q.Y) < tol for q in unique):
                unique.append(p)
        return unique

    @staticmethod
    def _circumcircle_contains(a, b, c, p):
        """
        Return True if p lies inside the circumcircle of triangle (a, b, c).
        """
        ax, ay = a.X, a.Y
        bx, by = b.X, b.Y
        cx, cy = c.X, c.Y
        dx, dy = p.X, p.Y
        d = 2*(ax*(by-cy) + bx*(cy-ay) + cx*(ay-by))
        
        if abs(d) < 1e-8:
            return False
            
        asq = ax*ax + ay*ay
        bsq = bx*bx + by*by
        csq = cx*cx + cy*cy
        ux = (asq*(by-cy) + bsq*(cy-ay) + csq*(ay-by)) / d
        uy = (asq*(cx-bx) + bsq*(ax-cx) + csq*(bx-ax)) / d
        return ((dx-ux)**2 + (dy-uy)**2) < ((ax-ux)**2 + (ay-uy)**2)

    @staticmethod
    def _delaunay(points):
        """
        Bowyer–Watson Delaunay triangulation of 2D points.
        Returns list of index triples into `points`.
        """
        pts = [(p.X, p.Y) for p in points]
        n = len(pts)
        xs, ys = zip(*pts)
        xmin, xmax = min(xs), max(xs)
        ymin, ymax = min(ys), max(ys)
        dx, dy = xmax-xmin, ymax-ymin
        dmax = max(dx, dy)
        mx, my = (xmin+xmax)/2.0, (ymin+ymax)/2.0
        super_pts = [
            (mx-2*dmax, my-dmax),
            (mx,        my+2*dmax),
            (mx+2*dmax, my-dmax)
        ]
        ext = pts + super_pts
        tris = [(n, n+1, n+2)]
        for i, (x, y) in enumerate(pts):
            bad, edges = [], {}
            for tri in tris:
                xi, yi = ext[tri[0]]; a = rg.Point3d(xi, yi, 0)
                xj, yj = ext[tri[1]]; b = rg.Point3d(xj, yj, 0)
                xk, yk = ext[tri[2]]; c = rg.Point3d(xk, yk, 0)
                p = rg.Point3d(x, y, 0)
                if LineUtils._circumcircle_contains(a, b, c, p):
                    bad.append(tri)
                    for u, v in ((tri[0],tri[1]), (tri[1],tri[2]), (tri[2],tri[0])):
                        key = tuple(sorted((u, v)))
                        edges[key] = edges.get(key, 0) + 1
            tris = [t for t in tris if t not in bad]
            for (u, v), cnt in edges.items():
                if cnt == 1:
                    tris.append((u, v, i))
        # remove triangles using super-vertices
        return [t for t in tris if all(j < n for j in t)]

    @staticmethod
    def _alpha_shape_edges(points, alpha):
        """
        Return boundary edges of the α-shape for 2D points.
        """
        tris = LineUtils._delaunay(points)
        edge_count = {}
        for tri in tris:
            a, b, c = (points[j] for j in tri)
            ab, ac = b-a, c-a
            d = 2*(ab.X*ac.Y - ab.Y*ac.X)
            if abs(d) < 1e-8:
                continue
            asq = ab.X*ab.X + ab.Y*ab.Y
            csq = ac.X*ac.X + ac.Y*ac.Y
            cx = (ac.Y*asq - ab.Y*csq) / d
            cy = (ab.X*csq - ac.X*asq) / d
            if math.hypot(cx, cy) <= alpha:
                for u, v in ((tri[0],tri[1]), (tri[1],tri[2]), (tri[2],tri[0])):
                    key = tuple(sorted((u, v)))
                    edge_count[key] = edge_count.get(key, 0) + 1
        return [edge for edge, cnt in edge_count.items() if cnt == 1]

    @staticmethod
    def estimate_alpha(points):
        """
        Estimate a good alpha value based on point spread.
        """
        unique = LineUtils.unique_points(points)
        if len(unique) < 2:
            return 1.0
        xs = [p.X for p in unique]; ys = [p.Y for p in unique]
        dx = max(xs) - min(xs); dy = max(ys) - min(ys)
        diag = math.hypot(dx, dy)
        finetune = 5.0 #extra multiplier hand picked
        return (diag / math.sqrt(len(unique))) * finetune

    @staticmethod
    def concave_hull_points(points, alpha=None):
        """
        Return list of Lines forming the concave hull of Point3d list (XY).
        """
        pts2d = [rg.Point3d(p.X, p.Y, 0) for p in points]
        unique = LineUtils.unique_points(pts2d)
        if alpha is None:
            alpha = LineUtils.estimate_alpha(unique)
        edges = LineUtils._alpha_shape_edges(unique, alpha)
        return [rg.Line(unique[i], unique[j]) for i, j in edges]

    @staticmethod
    def concave_hull_lines(lines, alpha=None):
        """
        Return concave hull of line segments by their endpoints.
        """
        pts = []
        for ln in lines:
            pts.append(rg.Point3d(ln.From.X, ln.From.Y, 0))
            pts.append(rg.Point3d(ln.To.X,   ln.To.Y,   0))
        return LineUtils.concave_hull_points(pts, alpha)

    @staticmethod
    def join_lines(lines, mergecollinear=True, tol=1e-8):
        """
        Join lines into polylines by connecting touching endpoints.
        """
        endpoints = []
        for ln in lines:
            endpoints.append(rg.Point3d(ln.From.X, ln.From.Y, 0))
            endpoints.append(rg.Point3d(ln.To.X,   ln.To.Y,   0))
        unique = {}
        for p in endpoints:
            key = (round(p.X/tol), round(p.Y/tol))
            if key not in unique:
                unique[key] = (p.X, p.Y)
        adj = {}
        for idx, ln in enumerate(lines):
            p1 = (round(ln.From.X/tol), round(ln.From.Y/tol))
            p2 = (round(ln.To.X/tol),   round(ln.To.Y/tol))
            adj.setdefault(p1, []).append((p2, idx))
            adj.setdefault(p2, []).append((p1, idx))
        visited = set()
        polylines = []
        for idx, ln in enumerate(lines):
            if idx in visited:
                continue
            start = (round(ln.From.X/tol), round(ln.From.Y/tol))
            comp_keys = set([start]); comp_lines = set()
            queue = [start]
            while queue:
                k = queue.pop(0)
                for neigh, li in adj.get(k, []):
                    comp_lines.add(li)
                    if neigh not in comp_keys:
                        comp_keys.add(neigh)
                        queue.append(neigh)
            deg_one = [k for k in comp_keys if sum(1 for (n,li) in adj[k] if li in comp_lines) == 1]
            cur = deg_one[0] if deg_one else start
            pts_seq = [cur]
            while True:
                found = False
                for neigh, li in adj[cur]:
                    if li in comp_lines and li not in visited:
                        visited.add(li)
                        pts_seq.append(neigh)
                        cur = neigh
                        found = True
                        break
                if not found:
                    break
            pline = rg.Polyline([rg.Point3d(unique[k][0], unique[k][1], 0) for k in pts_seq])
            polylines.append(pline)
        
        if mergecollinear:
            for poly in polylines:
                poly.MergeColinearSegments(GLOBAL_TOL, True)
        
        return polylines

    @staticmethod
    def circle_points(center, radius, count):
        """
        Returns a list of `count` rg.Point3d objects evenly distributed around
        a circle of given `radius` centered at `center`.
        """
        # guard: count must be int ≥ 1
        if not isinstance(count, int) or count < 1:
            return None
        else:
            pts = []
            
            for i in range(count):
                angle = 2.0 * math.pi * i / count
                x = center.X + radius * math.cos(angle)
                y = center.Y + radius * math.sin(angle)
                z = center.Z
                pts.append(rg.Point3d(x, y, z))
            
            return pts

    @staticmethod
    def _point_in_poly(pt, polyl, tol=1e-6):
        """
        returns True if pt is inside or on boundary.
        Uses distance-to-edge for boundary, then ray-casting for in/out.
        """
        # prepare closed vertex list
        pts = list(polyl)
        if not pts:
            return False
        if pts[0] != pts[-1]:
            pts.append(pts[0])
        x, y = pt.X, pt.Y
        
        # if the point is very close to any edge, count it as inside
        for i in range(len(pts)-1):
            if LineUtils._dist_point_seg(pt, pts[i], pts[i+1], tol) <= tol:
                return True
        
        # ray-casting
        inside = False
        for i in range(len(pts)-1):
            xi, yi = pts[i].X, pts[i].Y
            xj, yj = pts[i+1].X, pts[i+1].Y
            # check edge straddles horizontal ray
            if ((yi > y) != (yj > y)):
                xint = xi + (y - yi) * (xj - xi) / (yj - yi)
                if x < xint:
                    inside = not inside
        return inside

    @staticmethod
    def _dist_point_seg(pt, a, b, tol=1e-6):
        """
        Euclidean distance from point pt to segment AB.
        """
        vx, vy = b.X - a.X, b.Y - a.Y
        wx, wy = pt.X - a.X, pt.Y - a.Y
        denom = vx*vx + vy*vy
        if denom < tol:
            return math.hypot(wx, wy)
        t = (wx*vx + wy*vy) / denom
        if t <= 0:
            return math.hypot(wx, wy)
        if t >= 1:
            dx, dy = pt.X - b.X, pt.Y - b.Y
            return math.hypot(dx, dy)
        projx = a.X + t * vx
        projy = a.Y + t * vy
        return math.hypot(pt.X - projx, pt.Y - projy)

    @staticmethod
    def _interp(pa, pb, va, vb, iso, tol=1e-6):
        """
        Linear interpolate between points pa and pb where sdf crosses iso.
        """
        if abs(vb - va) < tol:
            t = 0.5
        else:
            t = (iso - va) / float(vb - va)
        return rg.Point3d(
            pa.X + t*(pb.X - pa.X),
            pa.Y + t*(pb.Y - pa.Y),
            0
        )

    @staticmethod
    def offset_polyline(pline, offset, resolution=50, tol=1e-6):
        """
        SDF-based offset of a planar polyline (XY plane only).
        returns list of Polylines (possibly multiple loops).
        """
        # close the loop
        verts = list(pline)
        if verts and verts[0] != verts[-1]:
            verts.append(verts[0])
    
        # compute bbox and pad offset margin
        margin = 0.1
        xs = [p.X for p in verts]
        ys = [p.Y for p in verts]
        
        minx, maxx = min(xs), max(xs)
        miny, maxy = min(ys), max(ys)
        
        w0 = maxx - minx
        h0 = maxy - miny
        
        pad_x = margin * w0
        pad_y = margin * h0
        m = abs(offset)
        
        minx -= pad_x + m
        maxx += pad_x + m
        miny -= pad_y + m
        maxy += pad_y + m
    
        # grid dimensions
        width, height = maxx - minx, maxy - miny
        cell = max(width, height) / float(resolution)
        nx, ny = int(round(width/cell)), int(round(height/cell))
    
        # sample signed distance field
        vals = [[0.0]*(nx+1) for _ in range(ny+1)]
        for i in range(ny+1):
            y = miny + i*cell
            for j in range(nx+1):
                x = minx + j*cell
                p = rg.Point3d(x, y, 0)
                inside = LineUtils._point_in_poly(p, verts, tol)
                dmin = min(
                    LineUtils._dist_point_seg(p, a, b, tol)
                    for a, b in zip(verts, verts[1:])
                )
                vals[i][j] = -dmin if inside else dmin
    
        # marching squares at iso=offset
        iso, lines = offset, []
        for i in range(ny):
            for j in range(nx):
                v0, v1 = vals[i][j],     vals[i][j+1]
                v3, v2 = vals[i+1][j],   vals[i+1][j+1]
                pts = [
                    rg.Point3d(minx+j*cell,   miny+i*cell,   0),
                    rg.Point3d(minx+(j+1)*cell, miny+i*cell,   0),
                    rg.Point3d(minx+(j+1)*cell, miny+(i+1)*cell, 0),
                    rg.Point3d(minx+j*cell,     miny+(i+1)*cell, 0)
                ]
                cs = [v >= iso for v in (v0, v1, v2, v3)]
                case = (cs[0]<<3)|(cs[1]<<2)|(cs[2]<<1)|cs[3]
                if case in (0, 15):
                    continue
    
                edges = []
                for k, (c_curr, c_next) in enumerate(zip(cs, cs[1:]+cs[:1])):
                    if c_curr != c_next:
                        a, b = pts[k], pts[(k+1)%4]
                        va, vb = (v0, v1, v2, v3)[k], (v1, v2, v3, v0)[k]
                        edges.append(LineUtils._interp(a, b, va, vb, iso, tol))
    
                if len(edges) == 2:
                    lines.append(rg.Line(edges[0], edges[1]))
                elif len(edges) == 4:
                    if case in (5, 10):
                        lines.append(rg.Line(edges[0], edges[3]))
                        lines.append(rg.Line(edges[1], edges[2]))
                    else:
                        lines.append(rg.Line(edges[0], edges[1]))
                        lines.append(rg.Line(edges[2], edges[3]))
    
        return LineUtils.join_lines(lines, mergecollinear=True, tol=tol)

    @staticmethod
    def filter_external_polylines(polylines, tol=1e-6):
        """
        Return only those closed polylines that are not fully contained
        within any other polyline in the list.
        """
        external = []
        for i, pl in enumerate(polylines):
            # get distinct vertices (drop closing duplicate)
            pts = list(pl)
            if pts and pts[0] == pts[-1]:
                pts = pts[:-1]
            # check if all vertices lie inside some other polyline
            inside_any = False
            for j, other in enumerate(polylines):
                if i == j:
                    continue
                other_pts = list(other)
                if other_pts and other_pts[0] == other_pts[-1]:
                    other_pts = other_pts[:-1]
                # test all vertices of pl against other
                if all(LineUtils._point_in_poly(p, other_pts, tol) for p in pts):
                    inside_any = True
                    break
            if not inside_any:
                external.append(pl)
        return external

    @staticmethod
    def is_point_in_any_polyline(pt, polylines, tol=1e-6):
        """
        Return True if point pt lies inside or on the boundary of
        any closed polyline in the given list.
        """
        for pl in polylines:
            pts = list(pl)
            # drop closing duplicate
            if pts and pts[0] == pts[-1]:
                pts = pts[:-1]
            if LineUtils._point_in_poly(pt, pts, tol):
                return True
        return False

    @staticmethod
    def time_block(name):
        """
        Use as: with LineUtils.time_block('name of what is being profiled')
        """
        class _Timer(object):
            def __enter__(self_inner):
                self_inner.t0 = time.clock()
                return self_inner
            def __exit__(self_inner, exc_type, exc, tb):
                dt = time.clock() - self_inner.t0
                print('%s took %.3f s' % (name, dt))
        return _Timer()

    @staticmethod
    def profile(func):
        """
        Use as decorator: @LineUtils.profile
        """
        def wrapper(*args, **kwargs):
            t0 = time.clock()
            result = func(*args, **kwargs)
            dt = time.clock() - t0
            print('%s took %.3f s' % (func.__name__, dt))
            return result
        return wrapper

    @staticmethod
    def timeout(seconds):
        """
        Use as decorator: @LineUtils.timeout(5)
        If the wrapped function doesn’t finish in <seconds>, returns "expired".
        """
        def decorator(func):
            def wrapper(*args, **kwargs):
                result = [None]
                exception = [None]
                def target():
                    try:
                        result[0] = func(*args, **kwargs)
                    except Exception as e:
                        exception[0] = e

                thread = System.Threading.Thread(System.Threading.ThreadStart(target))
                thread.IsBackground = True
                thread.Start()

                if not thread.Join(int(seconds * 1000)):
                    thread.Abort()
                    return "expired"

                if exception[0]:
                    # re-raise original exception
                    raise exception[0]
                return result[0]
            return wrapper
        return decorator

    @staticmethod
    def run_with_timeout(func, seconds):
        """
        Use as: LineUtils.run_with_timeout(lambda: your_func(arg1, arg2), 5)
        Returns the function’s result, or "expired" if it times out.
        """
        result = [None]
        exception = [None]
        def target():
            try:
                result[0] = func()
            except Exception as e:
                exception[0] = e

        thread = System.Threading.Thread(System.Threading.ThreadStart(target))
        thread.IsBackground = True
        thread.Start()

        if not thread.Join(int(seconds * 1000)):
            thread.Abort()
            return "expired"

        if exception[0]:
            raise exception[0]
        return result[0]

    @staticmethod
    def parallel(func, args_list, max_threads=4):
        """
        Use as: results = LineUtils.parallel(my_func, [a, b, c], max_threads=4)
        Runs my_func(item) over each item in args_list in up to max_threads
        concurrent threads. Returns a list of results in the same order.
        If any call raises, returns "failed to compute"
        """
        n = len(args_list)
        results = [None] * n
        exceptions = [None] * n
        idx = [0]
        lock = System.Object()

        def worker():
            while True:
                System.Threading.Monitor.Enter(lock)
                try:
                    if idx[0] >= n:
                        break
                    i = idx[0]
                    idx[0] += 1
                finally:
                    System.Threading.Monitor.Exit(lock)

                try:
                    results[i] = func(args_list[i])
                except Exception as e:
                    exceptions[i] = e

        # spawn up to max_threads workers
        threads = []
        count = max_threads if max_threads < n else n
        for _ in range(count):
            t = System.Threading.Thread(System.Threading.ThreadStart(worker))
            t.IsBackground = True
            t.Start()
            threads.append(t)

        # wait for all to finish
        for t in threads:
            t.Join()

        # re-raise first exception, if any
        for e in exceptions:
            if e:
                return "failed to compute"

        return results

    @staticmethod
    def clip_line_rectangle(line, rect, tol=GLOBAL_TOL):
        """
        Clip a line segment to a rectangle using the Liang-Barsky algorithm.
        """
        bb = rect.BoundingBox
        x0, y0, z0 = line.From.X, line.From.Y, line.From.Z
        x1, y1, z1 = line.To.X, line.To.Y, line.To.Z
        dx = x1 - x0
        dy = y1 - y0
        dz = z1 - z0
        p = [-dx, dx, -dy, dy]
        q = [x0 - bb.Min.X, bb.Max.X - x0, y0 - bb.Min.Y, bb.Max.Y - y0]
        u1, u2 = 0.0, 1.0
        for pi, qi in zip(p, q):
            if abs(pi) < tol:
                if qi < 0:
                    return []
            else:
                t = qi / float(pi)
                if pi < 0:
                    if t > u2:
                        return []
                    if t > u1:
                        u1 = t
                else:
                    if t < u1:
                        return []
                    if t < u2:
                        u2 = t
        if u2 < u1:
            return []
        p0 = rg.Point3d(x0 + u1*dx, y0 + u1*dy, z0 + u1*dz)
        p1 = rg.Point3d(x0 + u2*dx, y0 + u2*dy, z0 + u2*dz)
        return [rg.Line(p0, p1)]

    @staticmethod
    def polyline_intersection_rect(pline, rect, tol=GLOBAL_TOL):
        """
        Return list of Polyline segments of `pline` inside `rect`.
        """
        inside = []
        current = []
        pts = list(pline)
        for a, b in zip(pts, pts[1:]):
            segs = LineUtils.clip_line_rectangle(rg.Line(a, b), rect, tol)
            if not segs:
                if current:
                    inside.append(rg.Polyline(current))
                    current = []
                continue
            seg = segs[0]
            if not current:
                current.append(seg.From)
            current.append(seg.To)
        if current:
            inside.append(rg.Polyline(current))
        return inside

    @staticmethod
    def polyline_difference_rect(pline, rect, tol=GLOBAL_TOL):
        """
        Return polyline segments of `pline` outside `rect`.
        """
        segments = []
        pts = list(pline)
        for a, b in zip(pts, pts[1:]):
            outs = LineUtils.line_outside_rectangles(rg.Line(a, b), [rect], 10.0, tol)
            segments.extend([rg.Polyline([seg.From, seg.To]) for seg in outs])
        return segments
    
    @staticmethod
    def segment_to_segment_distance(seg1, seg2):
        """
        Compute the shortest distance between two finite line segments seg1 and seg2 (rg.Line).
        """
        A = seg1.From
        B = seg1.To
        C = seg2.From
        D = seg2.To
    
        # direction vectors
        u = B - A
        v = D - C
        w0 = A - C
    
        a = u * u  # dot(u, u)
        b = u * v  # dot(u, v)
        c = v * v  # dot(v, v)
        d = u * w0 # dot(u, w0)
        e = v * w0 # dot(v, w0)
    
        denom = a * c - b * b
        # initial (s, t) for infinite lines
        if abs(denom) > 1e-12:
            s = (b * e - c * d) / denom
            t = (a * e - b * d) / denom
        else:
            # parallel or nearly parallel
            s = 0.0
            if abs(c) > 1e-12:
                t = e / c
            else:
                t = 0.0
    
        # clamp s, t to [0,1]
        if s < 0.0:
            s = 0.0
        elif s > 1.0:
            s = 1.0
    
        if t < 0.0:
            t = 0.0
        elif t > 1.0:
            t = 1.0
    
        # After clamping one, recompute the other if needed
        # Check if s was clamped
        if s == 0.0 or s == 1.0:
            # solve for t that minimizes distance to P(s)
            Ps = rg.Point3d(
                A.X + u.X * s,
                A.Y + u.Y * s,
                A.Z + u.Z * s
            )
            w = Ps - C
            if abs(c) > 1e-12:
                t_candidate = (v * w) / c
                if t_candidate < 0.0:
                    t = 0.0
                elif t_candidate > 1.0:
                    t = 1.0
                else:
                    t = t_candidate
    
        # Check if t was clamped
        if t == 0.0 or t == 1.0:
            # solve for s that minimizes distance to Q(t)
            Qt = rg.Point3d(
                C.X + v.X * t,
                C.Y + v.Y * t,
                C.Z + v.Z * t
            )
            w = A - Qt
            if abs(a) > 1e-12:
                s_candidate = (u * w) / a
                if s_candidate < 0.0:
                    s = 0.0
                elif s_candidate > 1.0:
                    s = 1.0
                else:
                    s = s_candidate
    
        # Closest points on each segment
        P_closest = rg.Point3d(
            A.X + u.X * s,
            A.Y + u.Y * s,
            A.Z + u.Z * s
        )
        Q_closest = rg.Point3d(
            C.X + v.X * t,
            C.Y + v.Y * t,
            C.Z + v.Z * t
        )
    
        return P_closest.DistanceTo(Q_closest)

    @staticmethod
    def simplify_polyline(pline, tol=GLOBAL_TOL):
        """
        Simplify a polyline using the Ramer-Douglas-Peucker algorithm.
        """
        pts = list(pline)
        if len(pts) <= 2:
            return rg.Polyline(pts)
        keep = [0, len(pts)-1]
        stack = [(0, len(pts)-1)]
        while stack:
            s, e = stack.pop()
            a, b = pts[s], pts[e]
            ax, ay, az = a.X, a.Y, a.Z
            bx, by, bz = b.X, b.Y, b.Z
            dx, dy, dz = bx-ax, by-ay, bz-az
            d2 = dx*dx + dy*dy + dz*dz
            maxd = -1.0
            idx = None
            for i in range(s+1, e):
                p = pts[i]
                if d2 == 0:
                    dist = a.DistanceTo(p)
                else:
                    t = ((p.X-ax)*dx + (p.Y-ay)*dy + (p.Z-az)*dz) / d2
                    t = max(0.0, min(1.0, t))
                    proj = rg.Point3d(ax+t*dx, ay+t*dy, az+t*dz)
                    dist = p.DistanceTo(proj)
                if dist > maxd:
                    maxd = dist
                    idx = i
            if maxd > tol and idx is not None:
                stack.append((s, idx))
                stack.append((idx, e))
            else:
                keep.append(e)
        keep = sorted(set(keep))
        simp = [pts[i] for i in keep]
        return rg.Polyline(simp)

    @staticmethod
    def smooth_polyline(pline, factor=0.25, iterations=1):
        """
        Smooth a polyline using Chaikin's algorithm.
        """
        pts = list(pline)
        closed = pts[0] == pts[-1]
        for _ in range(iterations):
            new_pts = []
            rng = range(len(pts)-1) if not closed else range(len(pts))
            for i in rng:
                p0 = pts[i]
                p1 = pts[(i+1) % len(pts)]
                q = rg.Point3d(
                    p0.X + factor*(p1.X - p0.X),
                    p0.Y + factor*(p1.Y - p0.Y),
                    p0.Z + factor*(p1.Z - p0.Z)
                )
                r = rg.Point3d(
                    p1.X - factor*(p1.X - p0.X),
                    p1.Y - factor*(p1.Y - p0.Y),
                    p1.Z - factor*(p1.Z - p0.Z)
                )
                new_pts.extend([q, r])
            if not closed:
                new_pts = [pts[0]] + new_pts + [pts[-1]]
            else:
                new_pts.append(new_pts[0])
            pts = new_pts
        return rg.Polyline(pts)

    @staticmethod
    def _cross2d(a, b, c):
        return (b.X - a.X)*(c.Y - a.Y) - (b.Y - a.Y)*(c.X - a.X)

    @staticmethod
    def convex_hull(points):
        """
        Return the convex hull of 2D points.
        """
        pts = LineUtils.unique_points([rg.Point3d(p.X, p.Y, 0) for p in points])
        if len(pts) <= 1:
            return pts
        pts.sort(key=lambda p: (p.X, p.Y))
        lower = []
        for p in pts:
            while len(lower) >= 2 and LineUtils._cross2d(lower[-2], lower[-1], p) <= 0:
                lower.pop()
            lower.append(p)
        upper = []
        for p in reversed(pts):
            while len(upper) >= 2 and LineUtils._cross2d(upper[-2], upper[-1], p) <= 0:
                upper.pop()
            upper.append(p)
        return lower[:-1] + upper[:-1]

    @staticmethod
    def laplacian_smooth_polyline(pline, factor=0.5, iterations=1):
        """
        Smooth a polyline using Laplacian smoothing.

        Each interior vertex moves toward the average of its neighbors by
        `factor` on each iteration. Endpoints of an open polyline are kept
        fixed. A closed polyline is treated as a loop.
        """
        pts = list(pline)
        if len(pts) <= 2:
            return rg.Polyline(pts)
        closed = pts[0] == pts[-1]
        for _ in range(iterations):
            new_pts = [pts[0]] if not closed else []
            n = len(pts) - 1 if closed else len(pts)
            for i in range(1 if not closed else 0, n - 1):
                prev_pt = pts[i - 1]
                next_pt = pts[(i + 1) % len(pts)]
                cur_pt = pts[i]
                x = cur_pt.X + factor * ((prev_pt.X + next_pt.X) / 2.0 - cur_pt.X)
                y = cur_pt.Y + factor * ((prev_pt.Y + next_pt.Y) / 2.0 - cur_pt.Y)
                z = cur_pt.Z + factor * ((prev_pt.Z + next_pt.Z) / 2.0 - cur_pt.Z)
                new_pts.append(rg.Point3d(x, y, z))
            if closed:
                new_pts.append(new_pts[0])
            else:
                new_pts.append(pts[-1])
            pts = new_pts
        return rg.Polyline(pts)

    @staticmethod
    def minimum_bounding_rectangle(points):
        """
        Compute oriented minimum bounding rectangle of points.
        """
        hull = LineUtils.convex_hull(points)
        if not hull:
            return None
        if len(hull) == 1:
            p = hull[0]
            plane = rg.Plane(p, rg.Vector3d.XAxis, rg.Vector3d.YAxis)
            return rg.Rectangle3d(plane, 0.0, 0.0)
        min_area = None
        best_rect = None
        n = len(hull)
        for i in range(n):
            p0 = hull[i]
            p1 = hull[(i+1) % n]
            ang = math.atan2(p1.Y - p0.Y, p1.X - p0.X)
            cos_a = math.cos(-ang)
            sin_a = math.sin(-ang)
            xs = []
            ys = []
            for p in hull:
                x = p.X * cos_a - p.Y * sin_a
                y = p.X * sin_a + p.Y * cos_a
                xs.append(x)
                ys.append(y)
            minx, maxx = min(xs), max(xs)
            miny, maxy = min(ys), max(ys)
            area = (maxx - minx) * (maxy - miny)
            if min_area is None or area < min_area:
                min_area = area
                cx = (minx + maxx) / 2.0
                cy = (miny + maxy) / 2.0
                cos_ang = math.cos(ang)
                sin_ang = math.sin(ang)
                center = rg.Point3d(
                    cos_ang*cx - sin_ang*cy,
                    sin_ang*cx + cos_ang*cy,
                    0
                )
                plane = rg.Plane(center,
                                 rg.Vector3d(cos_ang, sin_ang, 0),
                                 rg.Vector3d(-sin_ang, cos_ang, 0))
                xint = rg.Interval(minx - cx, maxx - cx)
                yint = rg.Interval(miny - cy, maxy - cy)
                best_rect = rg.Rectangle3d(plane, xint, yint)
        return best_rect

    @staticmethod
    def _segments_intersect(a1, a2, b1, b2, tol=GLOBAL_TOL):
        def ccw(p1, p2, p3):
            return (p3.Y - p1.Y)*(p2.X - p1.X) > (p2.Y - p1.Y)*(p3.X - p1.X)
        if (max(a1.X, a2.X) + tol < min(b1.X, b2.X) or
            max(b1.X, b2.X) + tol < min(a1.X, a2.X) or
            max(a1.Y, a2.Y) + tol < min(b1.Y, b2.Y) or
            max(b1.Y, b2.Y) + tol < min(a1.Y, a2.Y)):
            return False
        d1 = ccw(a1, b1, b2)
        d2 = ccw(a2, b1, b2)
        d3 = ccw(a1, a2, b1)
        d4 = ccw(a1, a2, b2)
        if d1 != d2 and d3 != d4:
            return True
        return False

    @staticmethod
    def sweep_line_intersections(lines, tol=GLOBAL_TOL):
        """
        Find all segment index pairs that intersect using a sweep algorithm.
        """
        events = []
        for idx, ln in enumerate(lines):
            minx = min(ln.From.X, ln.To.X)
            maxx = max(ln.From.X, ln.To.X)
            events.append((minx, 0, idx))
            events.append((maxx, 1, idx))
        events.sort()
        active = []
        hits = []
        for x, typ, idx in events:
            if typ == 0:
                for j in active:
                    if LineUtils._segments_intersect(lines[idx].From, lines[idx].To,
                                                    lines[j].From, lines[j].To, tol):
                        hits.append((idx, j))
                active.append(idx)
            else:
                if idx in active:
                    active.remove(idx)
        return hits

    @staticmethod
    def find_furthest_point(test_point, points):
        """
        Return the point in 'points' farthest from 'test_point'.
        """
        furthest = None
        max_dist = -float('inf')
        for p in points:
            d = test_point.DistanceTo(p)
            if d > max_dist:
                max_dist, furthest = d, p
        return furthest

    @staticmethod
    def circle_center(p1, p2):
        """
        Given two points, return center and radius of their diameter circle.
        """
        cx = (p1.X + p2.X) / 2.0
        cy = (p1.Y + p2.Y) / 2.0
        center = rg.Point3d(cx, cy, 0)
        radius = p1.DistanceTo(p2) / 2.0
        return center, radius

    @staticmethod
    def circle_three_points(p1, p2, p3, tol=GLOBAL_TOL):
        """
        Return center and radius through three non-colinear points, else (None, None).
        """
        # area test for colinearity
        area = p1.X*(p2.Y-p3.Y) + p2.X*(p3.Y-p1.Y) + p3.X*(p1.Y-p2.Y)
        
        if abs(area) < tol:
            return None, None
        
        A = p2.X - p1.X
        B = p2.Y - p1.Y
        C = p3.X - p1.X
        D = p3.Y - p1.Y
        E = A*(p1.X+p2.X) + B*(p1.Y+p2.Y)
        F = C*(p1.X+p3.X) + D*(p1.Y+p3.Y)
        G = 2*(A*(p3.Y-p2.Y) - B*(p3.X-p2.X))
        
        if abs(G) < tol:
            return None, None
            
        cx = (D*E - B*F) / G
        cy = (A*F - C*E) / G
        center = rg.Point3d(cx, cy, 0)
        radius = center.DistanceTo(p1)
        
        return center, radius

    @staticmethod
    def is_point_inside_circle(center, radius, point, tol=GLOBAL_TOL):
        """
        Return True if 'point' lies within or on the circle.
        """
        return point.DistanceTo(center) <= radius + tol

    @staticmethod
    def minimal_enclosing_circle(points, tol=GLOBAL_TOL):
        """
        Compute smallest circle enclosing all points (pairs + triplets method).
        Returns (center, radius) or (None, None) if no points.
        """
        n = len(points)
        
        if n == 0:
            return None, None
        if n == 1:
            return points[0], 0.0
        if n == 2:
            return LineUtils.circle_center(points[0], points[1])
        
        best_c, best_r = None, float('inf')
        
        # pairs
        for i, j in itertools.combinations(range(n), 2):
            c, r = LineUtils.circle_center(points[i], points[j])
            if all(p.DistanceTo(c) <= r + tol for p in points) and r < best_r:
                best_c, best_r = c, r
                
        # triplets
        for i, j, k in itertools.combinations(range(n), 3):
            c, r = LineUtils.circle_three_points(points[i], points[j], points[k], tol)
            if c is not None and all(p.DistanceTo(c) <= r + tol for p in points) and r < best_r:
                best_c, best_r = c, r
                
        return best_c, best_r

    @staticmethod
    def snap_point_to_grid(pt, step):
        """
        Snap a point to the nearest grid location.
        """
        x = round(pt.X / step) * step
        y = round(pt.Y / step) * step
        z = round(pt.Z / step) * step
        return rg.Point3d(x, y, z)

    @staticmethod
    def snap_line_to_grid(line, step):
        """
        Snap both endpoints of a line to the grid.
        """
        return rg.Line(LineUtils.snap_point_to_grid(line.From, step),
                       LineUtils.snap_point_to_grid(line.To, step))

    @staticmethod
    def is_polyline_self_intersecting(pline, tol=1e-8):
        """
        Return True if `pline` self-intersects.
        """
        pts = list(pline)
        segs = [(pts[i], pts[i+1]) for i in range(len(pts)-1)]
        for i in range(len(segs)):
            for j in range(i+1, len(segs)):
                if j == i+1:
                    continue
                if LineUtils._segments_intersect(segs[i][0], segs[i][1], segs[j][0], segs[j][1], tol):
                    return True
        return False

    @staticmethod
    def safe_batch(func, args_list, timeout_sec=5, max_threads=4):
        """
        Run parrallel compute with per-call timeout.
        """
        def wrapped(arg):
            return LineUtils.run_with_timeout(lambda: func(arg), timeout_sec)
        return LineUtils.parallel(wrapped, args_list, max_threads)

    # — Finds individual “measure” tokens (mixed, fraction, int, or feet-only) —
    MEASURE_RE = re.compile(r"""
        (?:
            # 1) Feet + inches (mixed/fraction/int), e.g. -2'-1 1/4", 3'-3/8", 4'-6"
            -?\d+\s*'\s*(?:-\s*)?          # signed feet + apostrophe + optional dash
            (?:
                \d+\s+\d+/\d+             # mixed inches (1 1/4)
              |
                \d+/\d+                   # fraction only (3/8)
              |
                \d+                       # integer inches (6)
            )
            \s*"
          |
            # 2) Mixed inches without feet, e.g. -1 1/4"
            -?\d+\s+\d+/\d+\s*"
          |
            # 3) Fraction only, e.g. -3/8"
            -?\d+/\d+\s*"
          |
            # 4) Integer inches without feet, e.g. -12"
            -?\d+\s*"
          |
            # 5) Feet only, e.g. -6'
            -?\d+\s*'
        )
    """, re.VERBOSE)

    # — Breaks a single token into feet + one of (mixed, fraction, int) inches —
    PARTS_RE = re.compile(r"""
        ^\s*
        (?:(?P<feet>\d+)\s*'\s*(?:-\s*)?)?   # optional feet (e.g. 2')
        (?:
            (?P<inch_int>\d+)\s+(?P<num>\d+)\s*/\s*(?P<den>\d+)  # mixed inches (1 1/4)
          |
            (?P<num2>\d+)\s*/\s*(?P<den2>\d+)                    # fraction only (3/8)
          |
            (?P<inch_only>\d+)                                  # integer inches (6)
        )
        \s*"
        \s*$
    """, re.VERBOSE)

    @staticmethod
    def parse_measure(tok):
        """
        Parse a feet/inches token (possibly negative) into a float number of inches.
        
        Supported forms:
          "0"           ->   0.0
          "1'-0\""      ->  12.0
          "3/4\""       ->   0.75
          "1 1/4\""     ->   1.25
          "2'-1 1/8\""  ->  25.125
          "-4' 0\""     -> -48.0
          "-3/8\""      ->  -0.375
          "6'"          ->  72.0
          "-6'"         -> -72.0

        Returns a float, or an error string if parsing fails.
        """
        tok = tok.strip()
        
        # 1) Handle leading minus
        sign = 1.0
        if tok.startswith('-'):
            sign = -1.0
            tok = tok[1:].strip()

        # 2) Raw number (integer or decimal), e.g. "0", "5", "0.0"
        if tok.replace('.', '', 1).isdigit():
            return sign * float(tok)

        # 3) Feet-only, e.g. "6'" or "-4'"
        if tok.endswith("'"):
            num_feet = tok[:-1].strip()
            if not num_feet.isdigit():
                return "Can't parse measure %r" % (tok + "'")
            return sign * (int(num_feet) * 12.0)

        # 4) Mixed/fraction/int inches (with optional feet)
        m = LineUtils.PARTS_RE.match(tok)
        if not m:
            return "Can't parse measure %r" % tok

        feet = int(m.group('feet')) if m.group('feet') else 0
        inches = 0.0

        # 4a) Mixed inches: "inch_int num/den"
        if m.group('inch_int') and m.group('num') and m.group('den'):
            inch_int = int(m.group('inch_int'))
            num = int(m.group('num'))
            den = int(m.group('den'))
            inches = inch_int + (num / float(den))

        # 4b) Fraction-only: "num2/den2"
        elif m.group('num2') and m.group('den2'):
            num2 = int(m.group('num2'))
            den2 = int(m.group('den2'))
            inches = num2 / float(den2)

        # 4c) Integer-only inches
        elif m.group('inch_only'):
            inches = int(m.group('inch_only'))

        total_inches = feet * 12.0 + inches
        return sign * total_inches

    @staticmethod
    def parse_scale(s):
        """
        Parse a scale string like “1\" = 1'-0\"" (or variations) and return:
          - If two measures found -> (real_inches / draw_inches) as float.
          - If one measure found -> its inch value (float).
          - Otherwise -> an error string.
        """
        # Normalize curly quotes and common words
        s = s.replace('“', '"').replace('”', '"').lower()
        s = re.sub(r'\\([\'"])', r'\1', s) #support for 1/8"=1\'-0" style
        s = re.sub(r'\bft\b', "'", s)
        s = re.sub(r'\bin\b', '"', s)
        s = re.sub(r'\s*=\s*', ' = ', s) #support for 1/8"=1\'-0" style

        # Extract all “measure” tokens
        toks = LineUtils.MEASURE_RE.findall(s)
        if not toks:
            return "No measures found in %r" % s

        # If only one token, return its inch value
        if len(toks) == 1:
            return LineUtils.parse_measure(toks[0])

        # Otherwise, take the first two as draw & real
        draw_tok, real_tok = toks[0], toks[1]

        din = LineUtils.parse_measure(draw_tok)
        if isinstance(din, str):
            return din  # error message

        rin = LineUtils.parse_measure(real_tok)
        if isinstance(rin, str):
            return rin  # error message

        if din == 0:
            return "Drawing measure is zero in %r" % s

        return rin / din

    @staticmethod
    def read_xlsx(file_path, sheetname, filter_word=None):
        """
        Reads all data from the specified sheet in an .xlsx file, returning a list of rows,
        where each row is a list of cell‐values (strings or None). Blank cells become None.
        Any row that is entirely empty—or contains the exact filter_word in any cell—is dropped.
        Any column that is entirely empty (after row‐pruning) is also dropped, so the returned
        grid is rectangular. Errors are printed (e.g. file not found, sheet not found), and
        an empty list is returned on failure.
    
        Args:
            file_path (str): Path to the .xlsx file.
            sheetname (str): Name of the sheet to read.
            filter_word (str or None): If provided, any row containing a cell == filter_word
                                       will be skipped entirely. Default is None (no extra filtering).
    
        Returns:
            List[List[str or None]]: 2D list of cell values, with no entirely‐blank rows or columns,
                                     and with rows containing filter_word removed. Returns [] on errors.
        """
        data = []
        try:
            z = zipfile.ZipFile(file_path, 'r')
        except Exception as e:
            print("Error: cannot open '%s' as a ZIP archive: %s" % (file_path, e))
            return data
    
        # XML namespace constants
        NS_SHEET = '{http://schemas.openxmlformats.org/spreadsheetml/2006/main}'
        NS_REL   = {'ns': 'http://schemas.openxmlformats.org/package/2006/relationships'}
    
        # 1) Find the path to the requested sheet inside the XLSX
        sheet_path = None
        try:
            with z.open('xl/workbook.xml') as wb_file:
                wb_tree = ET.parse(wb_file)
                sheets = wb_tree.findall('.//%ssheet' % NS_SHEET)
                for sheet in sheets:
                    if sheet.get('name') == sheetname:
                        sheet_id = sheet.get(
                            '{http://schemas.openxmlformats.org/officeDocument/2006/relationships}id'
                        )
                        if not sheet_id:
                            print("Error: sheet '%s' has no relationship ID." % sheetname)
                            return data
    
                        try:
                            with z.open('xl/_rels/workbook.xml.rels') as rels_file:
                                rels_tree = ET.parse(rels_file)
                                relationships = rels_tree.findall('.//ns:Relationship', NS_REL)
                                for rel in relationships:
                                    if rel.get('Id') == sheet_id:
                                        target = rel.get('Target')
                                        if not target:
                                            continue
                                        sheet_path = 'xl/' + target.replace('\\', '/')
                                        break
                        except Exception as e_rels:
                            print("Error: cannot read relationships for workbook: %s" % e_rels)
                            return data
    
                        break
    
            if not sheet_path:
                print("Error: sheet named '%s' not found in workbook." % sheetname)
                return data
    
        except Exception as e_wb:
            print("Error: failed to parse 'xl/workbook.xml': %s" % e_wb)
            return data
    
        # 2) Read shared strings (if present)
        shared_strings = []
        try:
            with z.open('xl/sharedStrings.xml') as ss_file:
                ss_tree = ET.parse(ss_file)
                for t in ss_tree.findall('.//%st' % NS_SHEET):
                    shared_strings.append(t.text or '')
        except KeyError:
            # If sharedStrings.xml doesn’t exist, proceed with empty list
            shared_strings = []
        except Exception as e_ss:
            print("Warning: failed to read sharedStrings.xml: %s" % e_ss)
            shared_strings = []
    
        # 3) Parse the sheet XML and collect raw rows
        try:
            with z.open(sheet_path) as sheet_file:
                sheet_tree = ET.parse(sheet_file)
                for row in sheet_tree.findall('.//%srow' % NS_SHEET):
                    row_data = []
                    for c in row.findall('%sc' % NS_SHEET):
                        v = c.find('%sv' % NS_SHEET)
                        if v is None or v.text is None:
                            # no <v> or empty <v> -> treat as None
                            row_data.append(None)
                        else:
                            val = v.text
                            if c.get('t') == 's':
                                try:
                                    idx = int(val)
                                    if 0 <= idx < len(shared_strings):
                                        val = shared_strings[idx]
                                    else:
                                        print("Warning: sharedStrings index %d out of range" % idx)
                                        val = None
                                except Exception:
                                    print("Warning: invalid sharedStrings index '%s'" % val)
                                    val = None
                            row_data.append(val)
                    data.append(row_data)
    
        except KeyError:
            print("Error: cannot open sheet file '%s' in archive." % sheet_path)
            return []
        except Exception as e_sheet:
            print("Error: failed to parse sheet XML '%s': %s" % (sheet_path, e_sheet))
            return []
    
        # If we got no rows at all, return empty
        if not data:
            return []
    
        def is_row_empty(row):
                # empty if every cell is None or whitespace-only
                for cell in row:
                    if cell is None:
                        continue
                    try:
                        s = unicode(cell)
                    except:
                        s = cell
                    if s is None:
                        continue
                    if s.strip() != '':
                        return False
                return True

        pruned_rows = []
        for row in data:
            # 4a) Skip if entire row is empty
            if is_row_empty(row):
                continue
    
            # 4b) Skip if filter_word is provided and matches any cell exactly
            if filter_word is not None:
                skip_due_to_filter = False
                for cell in row:
                    # Compare only non-None cells
                    if cell == filter_word:
                        skip_due_to_filter = True
                        break
                if skip_due_to_filter:
                    continue
    
            # Otherwise, keep the row
            pruned_rows.append(row)
    
        if not pruned_rows:
            # All rows were empty or filtered out -> nothing to return
            return []
    
        # === 5) Pad all rows to the same length with None (so columns line up) ===
        max_cols = max(len(r) for r in pruned_rows)
        for r in pruned_rows:
            if len(r) < max_cols:
                r.extend([None] * (max_cols - len(r)))
    
        return pruned_rows
    
    
    @staticmethod
    def color_from_hsv(h, s, v, alpha = 255.0):
        """
        Construct an HSV (Hue, Saturation, Value) color
        """
        if s == 0.0:
            r = g = b = int(v * 255)
            return System.Drawing.Color.FromArgb(r, g, b)
        
        h = h / 60.0  # Sector 0 to 5
        i = int(System.Math.Floor(h))
        f = h - i
        p = v * (1 - s)
        q = v * (1 - s * f)
        t = v * (1 - s * (1 - f))
        
        if i == 0:
            r, g, b = v, t, p
        elif i == 1:
            r, g, b = q, v, p
        elif i == 2:
            r, g, b = p, v, t
        elif i == 3:
            r, g, b = p, q, v
        elif i == 4:
            r, g, b = t, p, v
        else:
            r, g, b = v, p, q
        
        r = int(round(r * 255))
        g = int(round(g * 255))
        b = int(round(b * 255))
        
        return System.Drawing.Color.FromArgb(alpha, r, g, b)
    
    @staticmethod
    def colors_generator(num_colors, alpha = 255.0):
        """
        Generate n colors equally spaced apart in the hsv scale
        special cases: 1 color -> black, 2 colors -> black/white
        """
        
        n = num_colors
        colors = []
        if n <= 0:
            return colors
        elif n == 1:
            # Return black for n=1
            colors.append(System.Drawing.Color.FromArgb(alpha, 0, 0, 0))
            return colors
        elif n == 2:
            # Return black and white for n=2
            colors.append(System.Drawing.Color.FromArgb(alpha, 0, 0, 0))      # Black
            colors.append(System.Drawing.Color.FromArgb(alpha, 255, 255, 255))# White
            return colors
        
        for i in range(n):
            hue = (i * 360.0 / n) % 360  # Evenly spaced hues
            saturation = 0.9              # High saturation for vibrancy
            value = 0.9                   # High value for brightness
            colors.append(LineUtils.color_from_hsv(hue, saturation, value, alpha))
        
        return colors


    @staticmethod
    def to_xy2(p):
        """
        Convert Rhino point to xy tuple
        Keep z ignored as algorithm is 2D
        Returns float(x), float(y)
        """
        return (float(p.X), float(p.Y))

    @staticmethod
    def bbox_xy(points, pad):
        """
        Compute xy bbox with optional pad
        Pad default is 5% of max span plus epsilon
        Returns (x0, y0, x1, y1)
        """
        xs = [p.X for p in points]
        ys = [p.Y for p in points]
        x0 = min(xs)
        x1 = max(xs)
        y0 = min(ys)
        y1 = max(ys)
        dx = x1 - x0
        dy = y1 - y0
        if pad is None:
            pad_xy = 0.05 * max(dx, dy) + 1e-9
        else:
            pad_xy = pad
        return (x0 - pad_xy, y0 - pad_xy, x1 + pad_xy, y1 + pad_xy)

    @staticmethod
    def same_point(a, b, tol):
        """
        Compare xy tuples with tol
        Returns True or False
        """
        if abs(a[0] - b[0]) <= tol and abs(a[1] - b[1]) <= tol:
            return True
        else:
            return False

    @staticmethod
    def distance_l1(p, q):
        """
        Manhattan distance helper
        Works on 2D tuples
        Returns float
        """
        return abs(p[0] - q[0]) + abs(p[1] - q[1])

    @staticmethod
    def angle(p1, p2):
        """
        Polar angle 0..2Pi
        Based on atan2 with wrap
        Returns float radians
        """
        ang = math.atan2(p2[1] - p1[1], p2[0] - p1[0])
        if ang < 0.0:
            ang = 2.0 * math.pi + ang
        else:
            ang = ang
        return ang

    @staticmethod
    def seg_intersection(l1a, l1b, l2a, l2b, tol):
        """
        Segment intersection in xy
        Returns (x,y) or None
        Handles parallel by denom==0
        """
        x1 = l1a[0]
        y1 = l1a[1]
        x2 = l1b[0]
        y2 = l1b[1]
        x3 = l2a[0]
        y3 = l2a[1]
        x4 = l2b[0]
        y4 = l2b[1]
        denom = (y4 - y3) * (x2 - x1) - (x4 - x3) * (y2 - y1)

        if abs(denom) <= 0.0:
            return None
        ua = ((x4 - x3) * (y1 - y3) - (y4 - y3) * (x1 - x3)) / float(denom)
        ub = ((x2 - x1) * (y1 - y3) - (y2 - y1) * (x1 - x3)) / float(denom)
        if ua < -tol or ua > 1.0 + tol or ub < -tol or ub > 1.0 + tol:
            return None
        xi = x1 + ua * (x2 - x1)
        yi = y1 + ua * (y2 - y1)
        return (xi, yi)

    @staticmethod
    def clean_data(raw):
        """
        Break L1 degeneracy ties
        Tiny jitter when |dx|==|dy|
        In place modification
        """
        n = len(raw)
        i = 0
        while i < n:
            xi = raw[i][0]
            yi = raw[i][1]
            j = i + 1
            while j < n:
                dx = raw[j][0] - xi
                dy = raw[j][1] - yi
                if abs(abs(dx) - abs(dy)) <= 0.0:
                    raw[j] = (raw[j][0] + 1e-10 * yi, raw[j][1] + 2e-10 * raw[j][0])
                else:
                    raw[j] = raw[j]
                j += 1
            i += 1
        return raw

    @staticmethod
    def bisector_intersection(B1, B2, tol):
        """
        Intersect two poly-bisectors
        Scans consecutive segments
        Returns first hit or None
        """
        if B1 is B2:
            return None
        i = 0
        while i < len(B1['points']) - 1:
            a1 = B1['points'][i]
            a2 = B1['points'][i + 1]
            j = 0
            ok = False
            while j < len(B2['points']) - 1:
                b1 = B2['points'][j]
                b2 = B2['points'][j + 1]
                pt = LineUtils.seg_intersection(a1, a2, b1, b2, tol)
                if pt is not None:
                    ok = True
                    break
                else:
                    j += 1
            if ok:
                return pt
            else:
                i += 1
        return None

    @staticmethod
    def is_bisector_trapped(trap_site, bisector):
        """
        Trap test against site
        All points no closer to others
        Returns True or False
        """
        k = 0
        while k < len(bisector['points']):
            pt = bisector['points'][k]
            if LineUtils.distance_l1(trap_site['site'], pt) <= LineUtils.distance_l1(bisector['sites'][0]['site'], pt) and LineUtils.distance_l1(trap_site['site'], pt) <= LineUtils.distance_l1(bisector['sites'][1]['site'], pt):
                k += 1
            else:
                return False
        return True

    @staticmethod
    def trim_bisector(target, intersector, intersection):
        """
        Trim target by intersector
        Keep points nearer to target sites
        Append intersection if present
        """

        polygon_site = None
        for s in intersector['sites']:
            found = False
            for t in target['sites']:
                if s is t:
                    found = True
                    break
                else:
                    found = found
            if not found:
                polygon_site = s
                break
            else:
                polygon_site = polygon_site
        new_pts = []
        k = 0

        while k < len(target['points']):
            p = target['points'][k]
            if LineUtils.distance_l1(p, target['sites'][0]['site']) < LineUtils.distance_l1(p, polygon_site['site']) and LineUtils.distance_l1(p, target['sites'][1]['site']) < LineUtils.distance_l1(p, polygon_site['site']):
                new_pts.append(p)
            else:
                new_pts = new_pts
            k += 1

        if intersection is not None:
            new_pts.append(intersection)
        else:
            new_pts = new_pts

        if target['up']:
            new_pts.sort(key=lambda t: t[1])
        else:
            new_pts.sort(key=lambda t: t[0])

        target['points'] = new_pts

    @staticmethod
    def find_hop_to(bisector, hop_from):
        """
        Hop across bisector ends
        Return opposite site dict
        Simple pointer logic
        """
        if bisector['sites'][0] is hop_from:
            return bisector['sites'][1]
        else:
            return bisector['sites'][0]

    @staticmethod
    def get_extreme_point(bisector, go_up):
        """
        Extreme Y value along bisector
        Max for up, min for down
        Returns float
        """

        val = -1.0e300
        if not go_up:
            val = 1.0e300
        i = 0

        while i < len(bisector['points']):
            y = bisector['points'][i][1]
            if go_up:
                if y > val:
                    val = y
                else:
                    val = val
            else:
                if y < val:
                    val = y
                else:
                    val = val
            i += 1
        return val

    @staticmethod
    def is_new_bisector_upward(hop_to, hop_from, site, go_up):
        """
        Decide stroke direction
        Based on relative geometry
        Returns True or False
        """

        dx = hop_to['site'][0] - site['site'][0]
        dy = hop_to['site'][1] - site['site'][1]
        if abs(dx) <= 0.0:
            return site['site'][1] > hop_to['site'][1]
        else:
            slope = dy / float(dx)
            intercept = hop_to['site'][1] - slope * hop_to['site'][0]
            above = hop_from['site'][1] > slope * hop_from['site'][0] + intercept
            return above

    @staticmethod
    def determine_first_border_cross(cropR, cropL, current_crop_point, tol):
        """
        Which side crosses first
        Compare vertical distances
        Returns "right" "left" or None
        """

        dyR = abs(cropR['point'][1] - current_crop_point[1])
        dyL = abs(cropL['point'][1] - current_crop_point[1])
        if abs(dyR - dyL) <= tol:
            return None
        else:
            if dyR < dyL:
                return "right"
            else:
                return "left"

    @staticmethod
    def clear_out_orphans(orphanage, trap_point):
        """
        Remove trapped bisectors
        Uses is_bisector_trapped
        Returns filtered list
        """

        out = []
        i = 0
        while i < len(orphanage['bisectors']):
            b = orphanage['bisectors'][i]
            if not LineUtils.is_bisector_trapped(trap_point, b):
                out.append(b)
            else:
                out = out
            i += 1
        return out

    @staticmethod
    def find_correct_w(w, nearest_neighbor, find_bisector):
        """
        Walk to a valid neighbor
        Avoid starting on trapped
        Returns site dict
        """

        starting = find_bisector(w, nearest_neighbor)
        traps = []
        i = 0
        while i < len(w['bisectors']):
            b = w['bisectors'][i]
            hop_to = LineUtils.find_hop_to(b, w)
            traps.append({'hopTo': hop_to, 'isTrapped': LineUtils.is_bisector_trapped(hop_to, starting)})
            i += 1
        filt = [t for t in traps if t['isTrapped']]
        if len(filt) > 0:
            filt.sort(key=lambda t: LineUtils.distance_l1(t['hopTo']['site'], nearest_neighbor['site']))
            return LineUtils.find_correct_w(filt[0]['hopTo'], nearest_neighbor, find_bisector)
        else:
            return w

    @staticmethod
    def check_for_orphans(trapper, trapped, go_up, find_bisector):
        """
        Choose trapped candidate
        Heuristic for dead ends
        Returns bisector or None
        """

        cands = []
        i = 0
        while i < len(trapped['bisectors']):
            b = trapped['bisectors'][i]
            hop_to = LineUtils.find_hop_to(b, trapped)
            cond = go_up == (hop_to['site'][1] < trapped['site'][1]) and LineUtils.is_bisector_trapped(trapper, b)
            if cond:
                cands.append(b)
            else:
                cands = cands
            i += 1
        def extreme(bis):
            hop = LineUtils.find_hop_to(bis, trapped)
            ml = find_bisector(hop, trapper)
            return LineUtils.get_extreme_point(ml, go_up)
        if len(cands) == 0:
            return None
        else:
            if go_up:
                cands.sort(key=lambda b: -extreme(b))
            else:
                cands.sort(key=lambda b: extreme(b))
            return cands[0]

    @staticmethod
    def determine_starting_bisector(w, nearest_neighbor, width, last_intersect, find_bisector, tol):
        """
        Pick starting bisector
        Uses rightward probe test
        Returns dict with fields
        """
        if last_intersect is None:
            last_intersect = w['site']
        else:
            last_intersect = last_intersect
        z = [width, w['site'][1]]
        zline = {'points': [w['site'], z]}
        hit = None
        i = 0

        while i < len(nearest_neighbor['bisectors']):
            b = nearest_neighbor['bisectors'][i]
            pt = LineUtils.bisector_intersection(zline, b, tol)
            if pt is not None:
                hit = {'point': pt, 'bisector': b}
                break
            else:
                i += 1
        if hit is not None:
            if LineUtils.distance_l1(w['site'], hit['point']) > LineUtils.distance_l1(nearest_neighbor['site'], hit['point']):
                sb = find_bisector(w, nearest_neighbor)
                return {'startingBisector': sb, 'w': w, 'nearestNeighbor': nearest_neighbor, 'startingIntersection': hit['point']}
            else:
                if LineUtils.distance_l1(w['site'], hit['point']) < LineUtils.distance_l1(nearest_neighbor['site'], hit['point']) and hit['point'][0] > last_intersect[0]:
                    nextR = None
                    if hit['bisector']['sites'][0] is nearest_neighbor:
                        nextR = hit['bisector']['sites'][1]
                    else:
                        nextR = hit['bisector']['sites'][0]
                    return LineUtils.determine_starting_bisector(w, nextR, width, hit['point'], find_bisector, tol)
                else:
                    w2 = LineUtils.find_correct_w(w, nearest_neighbor, find_bisector)
                    sb2 = find_bisector(w2, nearest_neighbor)
                    return {'startingBisector': sb2, 'w': w2, 'nearestNeighbor': nearest_neighbor, 'startingIntersection': hit['point']}
        else:
            w3 = LineUtils.find_correct_w(w, nearest_neighbor, find_bisector)
            sb3 = find_bisector(w3, nearest_neighbor)
            return {'startingBisector': sb3, 'w': w3, 'nearestNeighbor': nearest_neighbor, 'startingIntersection': w3['site']}

    @staticmethod
    def walk_merge_line(currentR, currentL, currentBisector, currentCropPoint, goUp, crossedBorder, mergeArray, find_bisector, width, height, tol):
        """
        Merge walk procedure
        Trims and hops across graph
        Appends visited bisectors
        """

        owns = True
        k = 0

        while k < len(currentBisector['sites']):
            if currentBisector['sites'][k] is currentR or currentBisector['sites'][k] is currentL:
                k += 1
            else:
                owns = False
                break
        if not owns:
            currentBisector = find_bisector(currentR, currentL)
            LineUtils.trim_bisector(currentBisector, crossedBorder, currentCropPoint)
            mergeArray.append(currentBisector)

        cropLArray = []
        i = 0

        while i < len(currentL['bisectors']):
            b = currentL['bisectors'][i]
            pt = LineUtils.bisector_intersection(currentBisector, b, tol)
            if pt is not None:
                hopTo = LineUtils.find_hop_to(b, currentL)
                cond_dir = goUp == LineUtils.is_new_bisector_upward(hopTo, currentL, currentR, goUp)
                cond_dup = not (LineUtils.same_point(pt, currentCropPoint, tol) and b is crossedBorder)
                if cond_dir and cond_dup:
                    cropLArray.append({'bisector': b, 'point': pt})
                else:
                    cropLArray = cropLArray
            else:
                cropLArray = cropLArray
            i += 1

        cropLArray.sort(key=lambda e: LineUtils.angle(currentL['site'], LineUtils.find_hop_to(e['bisector'], currentL)['site']), reverse=True)
        tmp = []
        i = 0

        while i < len(cropLArray):
            e = cropLArray[i]
            hopTo = LineUtils.find_hop_to(e['bisector'], currentL)
            newML = find_bisector(currentR, hopTo)
            LineUtils.trim_bisector(newML, e['bisector'], e['point'])
            ok = True
            j = 0
            while j < len(cropLArray):
                if j != i:
                    otherHop = LineUtils.find_hop_to(cropLArray[j]['bisector'], currentL)
                    if LineUtils.is_bisector_trapped(otherHop, newML) and otherHop is not hopTo:
                        ok = False
                        break
                    else:
                        ok = ok
                else:
                    ok = ok
                j += 1
            if ok:
                tmp.append(e)
            else:
                tmp = tmp
            i += 1

        cropLArray = tmp
        cropRArray = []
        i = 0

        while i < len(currentR['bisectors']):
            b = currentR['bisectors'][i]
            pt = LineUtils.bisector_intersection(currentBisector, b, tol)
            if pt is not None:
                hopTo = LineUtils.find_hop_to(b, currentR)
                cond_dir = goUp == LineUtils.is_new_bisector_upward(hopTo, currentR, currentL, goUp)
                cond_dup = not (LineUtils.same_point(pt, currentCropPoint, tol) and b is crossedBorder)
                if cond_dir and cond_dup:
                    cropRArray.append({'bisector': b, 'point': pt})
                else:
                    cropRArray = cropRArray
            else:
                cropRArray = cropRArray
            i += 1

        cropRArray.sort(key=lambda e: LineUtils.angle(currentR['site'], LineUtils.find_hop_to(e['bisector'], currentR)['site']))
        tmp2 = []
        i = 0

        while i < len(cropRArray):
            e = cropRArray[i]
            hopTo = LineUtils.find_hop_to(e['bisector'], currentR)
            newML = find_bisector(currentL, hopTo)
            LineUtils.trim_bisector(newML, e['bisector'], e['point'])
            ok = True
            j = 0
            while j < len(cropRArray):
                if j != i:
                    otherHop = LineUtils.find_hop_to(cropRArray[j]['bisector'], currentR)
                    if LineUtils.is_bisector_trapped(otherHop, newML) and otherHop is not hopTo:
                        ok = False
                        break
                    else:
                        ok = ok
                else:
                    ok = ok
                j += 1
            if ok:
                tmp2.append(e)
            else:
                tmp2 = tmp2
            i += 1

        cropRArray = tmp2
        cropL = None
        if len(cropLArray) > 0 and cropLArray[0]['bisector'] is not currentBisector:
            cropL = cropLArray[0]
        else:
            if goUp:
                cropL = {'bisector': None, 'point': (float('inf'), float('inf'))}
            else:
                cropL = {'bisector': None, 'point': (-float('inf'), -float('inf'))}
        cropR = None
        if len(cropRArray) > 0 and cropRArray[0]['bisector'] is not currentBisector:
            cropR = cropRArray[0]
        else:
            if goUp:
                cropR = {'bisector': None, 'point': (float('inf'), float('inf'))}
            else:
                cropR = {'bisector': None, 'point': (-float('inf'), -float('inf'))}
        if cropL['bisector'] is None and cropR['bisector'] is None:
            left_orphan = LineUtils.check_for_orphans(currentR, currentL, goUp, find_bisector)
            right_orphan = LineUtils.check_for_orphans(currentL, currentR, goUp, find_bisector)
            if left_orphan is not None:
                for s in left_orphan['sites']:
                    s['bisectors'] = [b for b in s['bisectors'] if b is not left_orphan]
                hopTo = LineUtils.find_hop_to(left_orphan, currentL)
                currentR = LineUtils.find_correct_w(currentR, hopTo, find_bisector)
                newB = find_bisector(hopTo, currentR)
                mergeArray.append(newB)
                return LineUtils.walk_merge_line(currentR, hopTo, newB, currentCropPoint, goUp, crossedBorder, mergeArray, find_bisector, width, height, tol)
            else:
                if right_orphan is not None:
                    for s in right_orphan['sites']:
                        s['bisectors'] = [b for b in s['bisectors'] if b is not right_orphan]
                    hopTo2 = LineUtils.find_hop_to(right_orphan, currentR)
                    currentL = LineUtils.find_correct_w(currentL, hopTo2, find_bisector)
                    newB2 = find_bisector(hopTo2, currentL)
                    mergeArray.append(newB2)
                    return LineUtils.walk_merge_line(hopTo2, currentL, newB2, currentCropPoint, goUp, crossedBorder, mergeArray, find_bisector, width, height, tol)
                else:
                    return mergeArray

        first = LineUtils.determine_first_border_cross(cropR, cropL, currentCropPoint, tol)
        if first == "right":
            LineUtils.trim_bisector(cropR['bisector'], currentBisector, cropR['point'])
            LineUtils.trim_bisector(currentBisector, cropR['bisector'], cropR['point'])
            currentBisector['intersections'].append(cropR['point'])
            crossedBorder = cropR['bisector']
            currentR = LineUtils.find_hop_to(cropR['bisector'], currentR)
            currentCropPoint = cropR['point']
        else:
            if first == "left":
                LineUtils.trim_bisector(cropL['bisector'], currentBisector, cropL['point'])
                LineUtils.trim_bisector(currentBisector, cropL['bisector'], cropL['point'])
                currentBisector['intersections'].append(cropL['point'])
                crossedBorder = cropL['bisector']
                currentL = LineUtils.find_hop_to(cropL['bisector'], currentL)
                currentCropPoint = cropL['point']
            else:
                LineUtils.trim_bisector(cropR['bisector'], currentBisector, cropR['point'])
                LineUtils.trim_bisector(currentBisector, cropR['bisector'], cropR['point'])
                currentBisector['intersections'].append(cropR['point'])
                crossedBorder = cropR['bisector']
                currentR = LineUtils.find_hop_to(cropR['bisector'], currentR)
                currentCropPoint = cropR['point']
                LineUtils.trim_bisector(cropL['bisector'], currentBisector, cropL['point'])
                LineUtils.trim_bisector(currentBisector, cropL['bisector'], cropL['point'])
                currentBisector['intersections'].append(cropL['point'])
                crossedBorder = cropL['bisector']
                currentL = LineUtils.find_hop_to(cropL['bisector'], currentL)
                currentCropPoint = cropL['point']

        return LineUtils.walk_merge_line(currentR, currentL, currentBisector, currentCropPoint, goUp, crossedBorder, mergeArray, find_bisector, width, height, tol)

    @staticmethod
    def find_L1_bisector(P1, P2, width, height):
        """
        Build L1 bisector polyline
        Axis or ±1 slope segments
        Returns dict descriptor
        """
        x1 = P1['site'][0]
        y1 = P1['site'][1]
        x2 = P2['site'][0]
        y2 = P2['site'][1]
        dx = x1 - x2
        dy = y1 - y2
        mid = [(x1 + x2) / 2.0, (y1 + y2) / 2.0]

        if abs(dx) <= 0.0 and abs(dy) <= 0.0:
            raise Exception("Duplicate site")
        if abs(dx) <= 0.0:
            pts = [[0.0, mid[1]], [width, mid[1]]]
            return {'sites': [P1, P2], 'up': False, 'points': pts, 'intersections': [], 'compound': False}
        if abs(dy) <= 0.0:
            pts = [[mid[0], 0.0], [mid[0], height]]
            return {'sites': [P1, P2], 'up': True, 'points': pts, 'intersections': [], 'compound': False}

        slope = -1.0
        if (dy / float(dx)) <= 0.0:
            slope = 1.0
        intercept = mid[1] - slope * mid[0]

        if abs(dx) >= abs(dy):
            v1 = [(y1 - intercept) / slope, y1]
            v2 = [(y2 - intercept) / slope, y2]
            up = True
            verts = [v1, v2]
            verts.sort(key=lambda p: p[1])
            pts = [[verts[0][0], 0.0], verts[0], verts[1], [verts[1][0], height]]
            pts.sort(key=lambda p: p[1])
            return {'sites': [P1, P2], 'up': up, 'points': pts, 'intersections': [], 'compound': False}
        else:
            v1 = [x1, x1 * slope + intercept]
            v2 = [x2, x2 * slope + intercept]
            up = False
            verts = [v1, v2]
            verts.sort(key=lambda p: p[0])
            pts = [[0.0, verts[0][1]], verts[0], verts[1], [width, verts[1][1]]]
            pts.sort(key=lambda p: p[0])
            return {'sites': [P1, P2], 'up': up, 'points': pts, 'intersections': [], 'compound': False}

    @staticmethod
    def curry_find_bisector(callback, width, height):
        """
        Partial for bisector maker
        Fix width and height args
        Returns callable(a,b)
        """
        def f(a, b):
            return callback(a, b, width, height)
        return f

    @staticmethod
    def recursive_split(split_array, find_bisector, width, height, tol):
        """
        Divide and conquer build
        Split, solve, then merge
        Returns flattened sites
        """
        n = len(split_array)
        if n > 2:
            mid = int((n - (n % 2)) / 2)
            L = LineUtils.recursive_split(split_array[0:mid], find_bisector, width, height, tol)
            R = LineUtils.recursive_split(split_array[mid:], find_bisector, width, height, tol)
            neis = sorted(R, key=lambda s: LineUtils.distance_l1(L[-1]['site'], s['site']))
            start = LineUtils.determine_starting_bisector(L[-1], neis[0], width, None, find_bisector, tol)
            initialB = start['startingBisector']
            initialR = start['nearestNeighbor']
            initialL = start['w']
            upStroke = LineUtils.walk_merge_line(initialR, initialL, initialB, [width, height], True, None, [], find_bisector, width, height, tol)
            downStroke = LineUtils.walk_merge_line(initialR, initialL, initialB, [0.0, 0.0], False, None, [], find_bisector, width, height, tol)
            mergeArray = [initialB] + upStroke + downStroke
            for bis in mergeArray:
                bis['mergeLine'] = n
                bis['sites'][0]['bisectors'] = LineUtils.clear_out_orphans(bis['sites'][0], bis['sites'][1])
                bis['sites'][1]['bisectors'] = LineUtils.clear_out_orphans(bis['sites'][1], bis['sites'][0])
                for s in bis['sites']:
                    s['bisectors'].append(bis)
            return L + R
        else:
            if n == 2:
                bis = find_bisector(split_array[0], split_array[1])
                split_array[0]['bisectors'].append(bis)
                split_array[1]['bisectors'].append(bis)
                return split_array
            else:
                return split_array

    @staticmethod
    def generate_L1_voronoi(site_points, width, height, nudge = True, tol = GLOBAL_TOL):
        #print "gl1", tol
        """
        Prepare site graph list
        Optional nudge cleans ties
        Returns site dicts array
        """
        data = site_points[:]
        if nudge:
            data = LineUtils.clean_data(data)
        else:
            data = data
        sites = sorted(data, key=lambda a: (a[0], a[1]))
        sites = [{'site': [float(s[0]), float(s[1])], 'bisectors': []} for s in sites]
        find_b = LineUtils.curry_find_bisector(LineUtils.find_L1_bisector, width, height)
        graph = LineUtils.recursive_split(sites, find_b, width, height, tol)

        return graph

    @staticmethod
    def build_edges_from_bisectors(sites, x0, y0, width, height, tol):
        #print tol
        """
        Extract unique edges
        Quantized by tol to dedupe
        Returns (segs, pairs)
        """

        qu = {}
        segs = []
        pairs = 0
        for s in sites:
            pairs += len(s['bisectors'])
            i = 0
            while i < len(s['bisectors']):
                b = s['bisectors'][i]
                j = 0
                while j < len(b['points']) - 1:
                    a = b['points'][j]
                    c = b['points'][j + 1]
                    p = (a[0] + x0, a[1] + y0)
                    q = (c[0] + x0, c[1] + y0)
                    if abs(p[0] - q[0]) <= tol and abs(p[1] - q[1]) <= tol:
                        j += 1
                    else:
                        k1 = int(round(min(p[0], q[0]) / tol))
                        k2 = int(round(min(p[1], q[1]) / tol))
                        k3 = int(round(max(p[0], q[0]) / tol))
                        k4 = int(round(max(p[1], q[1]) / tol))
                        key = (k1, k2, k3, k4)
                        if key in qu:
                            j += 1
                        else:
                            qu[key] = True
                            pa = rg.Point3d(p[0], p[1], 0.0)
                            pb = rg.Point3d(q[0], q[1], 0.0)
                            #segs.append(rg.LineCurve(pa, pb))
                            segs.append(rg.Line(pa, pb))
                            j += 1
                i += 1
        return segs, pairs

    @staticmethod
    def ManhattanVoronoi(Points, Pad, nudge=True, tol=GLOBAL_TOL):
        #print tol
        """
        Compute L1 Voronoi (Manhattan) diagram in XY.
        Returns edges (as Lines), pair count, segment count
        Higher tolerance than usual 0.01 is reccomended, 0.0001 is a good safe start
        """
        if Points is None or len(Points) == 0:
            return [], 0, 0
        pts_xy = [rg.Point3d(p.X, p.Y, 0.0) for p in Points]
        x0, y0, x1, y1 = LineUtils.bbox_xy(pts_xy, Pad)
        width = x1 - x0
        height = y1 - y0
        raw = [(p.X - x0, p.Y - y0) for p in pts_xy]
        sites = LineUtils.generate_L1_voronoi(raw, width, height, nudge, tol)
        edges, pairs = LineUtils.build_edges_from_bisectors(sites, x0, y0, width, height, tol)

        rect = [
            rg.Line(rg.Point3d(x0, y0, 0.0), rg.Point3d(x1, y0, 0.0)),
            rg.Line(rg.Point3d(x1, y0, 0.0), rg.Point3d(x1, y1, 0.0)),
            rg.Line(rg.Point3d(x1, y1, 0.0), rg.Point3d(x0, y1, 0.0)),
            rg.Line(rg.Point3d(x0, y1, 0.0), rg.Point3d(x0, y0, 0.0))
        ]
        
        edges.extend(rect)
        return edges, pairs, len(edges)

    @staticmethod
    def telegram_send_message(token, chat_id, text):
        """
        POST /sendMessage. Returns Telegram JSON or 'failed...' text.
        """
        try:
            url = "https://api.telegram.org/bot%s/sendMessage" % token
            data = System.Collections.Specialized.NameValueCollection()
            data.Add("chat_id", str(chat_id))
            data.Add("text", text)
            client = System.Net.WebClient()
            result_bytes = client.UploadValues(url, data)
            return System.Text.Encoding.UTF8.GetString(result_bytes)
        except Exception as ex:
            return "failed to send: " + str(ex)
    
    
    @staticmethod
    def telegram_send_file_from_path(token, chat_id, file_path, mime_type=None, filename=None, caption=None):
        """
        Reads file bytes and POSTs /sendDocument.
        """
        try:
            if not System.IO.File.Exists(file_path):
                return "failed to send document: file not found"
            b = System.IO.File.ReadAllBytes(file_path)
            name = filename if filename else System.IO.Path.GetFileName(file_path)
            return LineUtils.telegram_send_file(token, chat_id, name, b, mime_type, caption)
        except Exception as ex:
            return "failed to send document: " + str(ex)
    
    
    @staticmethod
    def telegram_send_file(token, chat_id, filename, content, mime_type=None, caption=None):
        """
        POST /sendDocument with in-memory content. 'content' may be str/unicode or byte[]/bytearray.
        """
        try:
            url = "https://api.telegram.org/bot%s/sendDocument" % token
            boundary = "----------%s" % System.Guid.NewGuid().ToString("N")
            crlf = "\r\n"
            enc = System.Text.Encoding.UTF8
    
            # normalize content -> .NET byte[]
            net_bytes = None
            try:
                # .NET byte[] detection
                tp = content.GetType()
                if tp.IsArray and tp.GetElementType() == System.Byte:
                    net_bytes = content
            except:
                net_bytes = None
            if net_bytes is None:
                if isinstance(content, bytearray):
                    net_bytes = System.Array.CreateInstance(System.Byte, len(content))
                    i = 0
                    for v in content:
                        net_bytes[i] = int(v)
                        i = i + 1
                elif isinstance(content, str) or isinstance(content, System.String):
                    net_bytes = enc.GetBytes(content)
                else:
                    # fallback: try to convert iterables of ints
                    try:
                        net_bytes = System.Array.CreateInstance(System.Byte, len(content))
                        i = 0
                        for v in content:
                            net_bytes[i] = int(v)
                            i = i + 1
                    except:
                        return "failed to send document: unsupported content type"
    
            if mime_type is None or mime_type == "":
                mime_type = "application/octet-stream"
    
            # build multipart preamble
            parts = []
            parts.append("--" + boundary)
            parts.append('Content-Disposition: form-data; name="chat_id"')
            parts.append("")
            parts.append(str(chat_id))
    
            if caption is not None:
                parts.append("--" + boundary)
                parts.append('Content-Disposition: form-data; name="caption"')
                parts.append("")
                parts.append(caption)
    
            parts.append("--" + boundary)
            parts.append('Content-Disposition: form-data; name="document"; filename="%s"' % filename)
            parts.append("Content-Type: %s" % mime_type)
            parts.append("")
            pre_bytes = enc.GetBytes(crlf.join(parts) + crlf)
            post_bytes = enc.GetBytes(crlf + "--" + boundary + "--" + crlf)
    
            ms = System.IO.MemoryStream()
            ms.Write(pre_bytes, 0, pre_bytes.Length)
            ms.Write(net_bytes, 0, net_bytes.Length)
            ms.Write(post_bytes, 0, post_bytes.Length)
    
            client = System.Net.WebClient()
            client.Headers.Add("Content-Type", "multipart/form-data; boundary=%s" % boundary)
            resp = client.UploadData(url, ms.ToArray())
            return enc.GetString(resp)
        except Exception as ex:
            return "failed to send document: " + str(ex)
    
    
    @staticmethod
    def svg_from_polylines(polylines, closed_polylines, polylinescolor, hatchescolor, padding_ratio=0.1, stroke_width=1.0, fill_opacity=0.2):
        """
        Returns an SVG string (UTF-8) built from open and closed polylines.
        Colors expected as objects with .R/.G/.B. Accepts Polyline or PolylineCurve.
        """
        def _to_polylist(items):
            out = []
            for it in items or []:
                if hasattr(it, "ToPolyline"):
                    out.append(it.ToPolyline())
                elif hasattr(it, "TryGetPolyline"):
                    ok, pl = it.TryGetPolyline()
                    if ok:
                        out.append(pl)
                else:
                    out.append(it)
            return out
    
        pls = _to_polylist(polylines or [])
        cls = _to_polylist(closed_polylines or [])
    
        # bounds
        have_pts = False
        minx = 0.0; miny = 0.0; maxx = 0.0; maxy = 0.0
        for pl in pls + cls:
            for p in pl:
                if not have_pts:
                    minx = p.X; miny = p.Y; maxx = p.X; maxy = p.Y
                    have_pts = True
                else:
                    if p.X < minx:
                        minx = p.X
                    if p.X > maxx:
                        maxx = p.X
                    if p.Y < miny:
                        miny = p.Y
                    if p.Y > maxy:
                        maxy = p.Y
    
        if not have_pts:
            return """<?xml version="1.0" encoding="UTF-8" standalone="no"?><svg xmlns="http://www.w3.org/2000/svg" version="1.1" width="1" height="1"/>"""
    
        width = maxx - minx
        height = maxy - miny
        pad_x = width * padding_ratio
        pad_y = height * padding_ratio
        new_w = width + 2.0 * pad_x
        new_h = height + 2.0 * pad_y
        off_x = -minx + pad_x
        off_y = -miny + pad_y
    
        def _ptlist(pl):
            pts = []
            for pt in pl:
                ax = pt.X + off_x
                ay = pt.Y + off_y
                pts.append("%.6f,%.6f" % (ax, ay))
            return " ".join(pts)
    
        def _rgb(c, default):
            if c is None:
                r = default[0]; g = default[1]; b = default[2]
                return "rgb(%d,%d,%d)" % (r, g, b)
            try:
                return "rgb(%d,%d,%d)" % (int(c.R), int(c.G), int(c.B))
            except:
                r = default[0]; g = default[1]; b = default[2]
                return "rgb(%d,%d,%d)" % (r, g, b)
    
        sb = System.Text.StringBuilder()
        sb.Append('<?xml version="1.0" encoding="UTF-8" standalone="no"?>')
        sb.Append('\n')
        sb.Append('<svg xmlns="http://www.w3.org/2000/svg" version="1.1" width="%s" height="%s" viewBox="0 0 %s %s">' % (str(new_w), str(new_h), str(new_w), str(new_h)))
        sb.Append('\n')
        sb.Append('  <g transform="scale(1,-1) translate(0,-%s)">' % str(new_h))
        sb.Append('\n')
    
        # open polylines
        pc = polylinescolor or []
        i = 0
        for pl in pls:
            col = pc[i] if i < len(pc) else None
            color_str = _rgb(col, (0, 0, 0))
            sb.Append('    <polyline points="%s" fill="none" stroke="%s" stroke-width="%.3f"/>\n' % (_ptlist(pl), color_str, float(stroke_width)))
            i = i + 1
    
        # closed filled
        hc = hatchescolor or []
        j = 0
        for pl in cls:
            col = hc[j] if j < len(hc) else None
            color_str = _rgb(col, (0, 0, 0))
            sb.Append('    <polygon points="%s" fill="%s" fill-opacity="%.3f" stroke="%s" stroke-width="%.3f"/>\n' % (_ptlist(pl), color_str, float(fill_opacity), color_str, float(stroke_width)))
            j = j + 1
    
        sb.Append('  </g>\n</svg>\n')
        return sb.ToString()
    
    @staticmethod
    def png_from_polylines(polylines, closed_polylines, polylinescolor, hatchescolor, width_px=1024, height_px=1024, padding_ratio=0.1, stroke_px=2.0, fill_opacity=0.2):
        """
        Rasterize geometry to PNG bytes for Telegram preview.
        """
        enc = System.Text.Encoding.UTF8
    
        def _to_polylist(items):
            out = []
            if items is None:
                return out
            for it in items:
                if hasattr(it, "ToPolyline"):
                    out.append(it.ToPolyline())
                elif hasattr(it, "TryGetPolyline"):
                    ok, pl = it.TryGetPolyline()
                    if ok:
                        out.append(pl)
                else:
                    out.append(it)
            return out
    
        pls = _to_polylist(polylines)
        cls = _to_polylist(closed_polylines)
    
        have_pts = False
        minx = 0.0; miny = 0.0; maxx = 0.0; maxy = 0.0
        for pl in pls + cls:
            for p in pl:
                if not have_pts:
                    minx = p.X; miny = p.Y; maxx = p.X; maxy = p.Y
                    have_pts = True
                else:
                    if p.X < minx:
                        minx = p.X
                    if p.X > maxx:
                        maxx = p.X
                    if p.Y < miny:
                        miny = p.Y
                    if p.Y > maxy:
                        maxy = p.Y
    
        if not have_pts:
            return System.Array.CreateInstance(System.Byte, 0)
    
        bw = maxx - minx
        bh = maxy - miny
        if bw <= 0.0:
            bw = 1.0
        if bh <= 0.0:
            bh = 1.0
    
        pad_w = float(width_px) * padding_ratio
        pad_h = float(height_px) * padding_ratio
        sx = (float(width_px) - 2.0 * pad_w) / bw
        sy = (float(height_px) - 2.0 * pad_h) / bh
        s = sx if sx < sy else sy
        vis_w = bw * s
        vis_h = bh * s
        left = (float(width_px) - vis_w) * 0.5
        bottom = (float(height_px) - vis_h) * 0.5
    
        def _mapx(x):
            return float(left + (x - minx) * s)
    
        def _mapy(y):
            return float(height_px - (bottom + (y - miny) * s))
    
        def _color_rgb(c, a255):
            if c is None:
                return System.Drawing.Color.FromArgb(a255, 0, 0, 0)
            try:
                return System.Drawing.Color.FromArgb(a255, int(c.R), int(c.G), int(c.B))
            except:
                return System.Drawing.Color.FromArgb(a255, 0, 0, 0)
    
        bmp = System.Drawing.Bitmap(int(width_px), int(height_px), System.Drawing.Imaging.PixelFormat.Format32bppArgb)
        g = System.Drawing.Graphics.FromImage(bmp)
        g.SmoothingMode = System.Drawing.Drawing2D.SmoothingMode.AntiAlias
        g.Clear(System.Drawing.Color.White)
    
        alpha_fill = int(max(0, min(255, int(fill_opacity * 255.0))))
        if alpha_fill < 0:
            alpha_fill = 0
        if alpha_fill > 255:
            alpha_fill = 255
    
        # filled polygons first
        hc = hatchescolor or []
        j = 0
        for pl in cls:
            c = hc[j] if j < len(hc) else None
            b = System.Drawing.SolidBrush(_color_rgb(c, alpha_fill))
            pts = System.Array.CreateInstance(System.Drawing.PointF, len(pl))
            k = 0
            for pt in pl:
                pts[k] = System.Drawing.PointF(_mapx(pt.X), _mapy(pt.Y))
                k = k + 1
            g.FillPolygon(b, pts)
            b.Dispose()
            j = j + 1
    
        # open polylines
        pc = polylinescolor or []
        i = 0
        for pl in pls:
            c = pc[i] if i < len(pc) else None
            pen = System.Drawing.Pen(_color_rgb(c, 255), float(stroke_px))
            prev = None
            for pt in pl:
                xy = System.Drawing.PointF(_mapx(pt.X), _mapy(pt.Y))
                if prev is not None:
                    g.DrawLine(pen, prev, xy)
                prev = xy
            pen.Dispose()
            i = i + 1
    
        g.Dispose()
        ms = System.IO.MemoryStream()
        bmp.Save(ms, System.Drawing.Imaging.ImageFormat.Png)
        arr = ms.ToArray()
        bmp.Dispose()
        ms.Dispose()
        return arr
    
    
    @staticmethod
    def telegram_send_photo(token, chat_id, filename, photo_bytes, caption=None):
        """
        POST /sendPhoto with in-memory PNG/JPEG bytes for instant preview.
        """
        try:
            url = "https://api.telegram.org/bot%s/sendPhoto" % token
            boundary = "----------%s" % System.Guid.NewGuid().ToString("N")
            crlf = "\r\n"
            enc = System.Text.Encoding.UTF8
    
            net_bytes = None
            try:
                tp = photo_bytes.GetType()
                if tp.IsArray and tp.GetElementType() == System.Byte:
                    net_bytes = photo_bytes
            except:
                net_bytes = None
            if net_bytes is None:
                if isinstance(photo_bytes, bytearray):
                    net_bytes = System.Array.CreateInstance(System.Byte, len(photo_bytes))
                    i = 0
                    for v in photo_bytes:
                        net_bytes[i] = int(v)
                        i = i + 1
                else:
                    return "failed to send photo: unsupported bytes"
    
            parts = []
            parts.append("--" + boundary)
            parts.append('Content-Disposition: form-data; name="chat_id"')
            parts.append("")
            parts.append(str(chat_id))
    
            if caption is not None:
                parts.append("--" + boundary)
                parts.append('Content-Disposition: form-data; name="caption"')
                parts.append("")
                parts.append(caption)
    
            parts.append("--" + boundary)
            parts.append('Content-Disposition: form-data; name="photo"; filename="%s"' % filename)
            # if your bytes are JPEG, set image/jpeg
            mime_type = "image/png"
            parts.append("Content-Type: %s" % mime_type)
            parts.append("")
            pre = enc.GetBytes(crlf.join(parts) + crlf)
            post = enc.GetBytes(crlf + "--" + boundary + "--" + crlf)
    
            ms = System.IO.MemoryStream()
            ms.Write(pre, 0, pre.Length)
            ms.Write(net_bytes, 0, net_bytes.Length)
            ms.Write(post, 0, post.Length)
    
            client = System.Net.WebClient()
            client.Headers.Add("Content-Type", "multipart/form-data; boundary=%s" % boundary)
            resp = client.UploadData(url, ms.ToArray())
            return enc.GetString(resp)
        except Exception as ex:
            return "failed to send photo: " + str(ex)
    
    
    @staticmethod
    def telegram_send_document_with_thumbnail(token, chat_id, filename, file_bytes, mime_type, thumb_jpeg_bytes, caption=None):
        """
        Optional: sendDocument with a custom JPEG thumbnail (<=200kB, <=320x320).
        """
        try:
            url = "https://api.telegram.org/bot%s/sendDocument" % token
            boundary = "----------%s" % System.Guid.NewGuid().ToString("N")
            crlf = "\r\n"
            enc = System.Text.Encoding.UTF8
    
            def _to_net_bytes(data):
                try:
                    tp = data.GetType()
                    if tp.IsArray and tp.GetElementType() == System.Byte:
                        return data
                except:
                    pass
                if isinstance(data, bytearray):
                    arr = System.Array.CreateInstance(System.Byte, len(data))
                    i = 0
                    for v in data:
                        arr[i] = int(v)
                        i = i + 1
                    return arr
                return None
    
            file_net = _to_net_bytes(file_bytes)
            thumb_net = _to_net_bytes(thumb_jpeg_bytes)
            if file_net is None or thumb_net is None:
                return "failed to send document: unsupported bytes"
    
            parts = []
            parts.append("--" + boundary)
            parts.append('Content-Disposition: form-data; name="chat_id"')
            parts.append("")
            parts.append(str(chat_id))
    
            if caption is not None:
                parts.append("--" + boundary)
                parts.append('Content-Disposition: form-data; name="caption"')
                parts.append("")
                parts.append(caption)
    
            parts.append("--" + boundary)
            parts.append('Content-Disposition: form-data; name="document"; filename="%s"' % filename)
            parts.append("Content-Type: %s" % (mime_type if mime_type else "application/octet-stream"))
            parts.append("")
    
            pre = enc.GetBytes(crlf.join(parts) + crlf)
            #mid = enc.GetBytes(crlf + "--" + boundary + crlf + 'Content-Disposition: form-data; name="thumbnail"; filename="thumb.jpg"' + crlf + "Content-Type: image/jpeg" + crlf + crlf)
            mid = enc.GetBytes(crlf + "--" + boundary + crlf + 'Content-Disposition: form-data; name="thumb"; filename="thumb.jpg"' + crlf + "Content-Type: image/jpeg" + crlf + crlf)
            post = enc.GetBytes(crlf + "--" + boundary + "--" + crlf)
    
            ms = System.IO.MemoryStream()
            ms.Write(pre, 0, pre.Length)
            ms.Write(file_net, 0, file_net.Length)
            ms.Write(mid, 0, mid.Length)
            ms.Write(thumb_net, 0, thumb_net.Length)
            ms.Write(post, 0, post.Length)
    
            client = System.Net.WebClient()
            client.Headers.Add("Content-Type", "multipart/form-data; boundary=%s" % boundary)
            resp = client.UploadData(url, ms.ToArray())
            return enc.GetString(resp)
        except Exception as ex:
            return "failed to send document: " + str(ex)

    @staticmethod
    def print_version():
        """
        Return current LineUtils version as string
        """
        s = "%.2f" % LineUtils.VERSION  + " LineUtils library"
        return s

    @staticmethod
    def generate_wiki(target_cls):
        """
        Generates a Markdown wiki of every public method in the given class.
        """

        spacer = "----------------------------------"
        title = "     {0} API     ".format(target_cls.__name__)
        lines = [spacer, title, spacer, "\n"]

        # collect and sort public methods
        methods = inspect.getmembers(target_cls, inspect.isfunction)
        count = 0
        for name, func in methods:
            #internal method
            if name.startswith("_"):
                continue
                
            count += 1
            idx = "{:02d}.".format(count)

            # build signature
            try:
                argspec = inspect.getargspec(func)
                args = argspec.args or []
                sig = "{name}({args})".format(
                    name=name,
                    args=", ".join(args)
                )
            except TypeError:
                # built-ins or callables without retrievable signature
                sig = name + "()"

            # clean and indent docstring
            doc = inspect.getdoc(func) or ""
            doc_lines = []
            for dl in doc.splitlines():
                doc_lines.append("   " + dl)

            # append enumeration, signature, and doc
            lines.append("{idx} `{sig}`".format(idx=idx, sig=sig))
            lines.append("")
            lines.extend(doc_lines)
            lines.append("")

        return "\n".join(lines)


