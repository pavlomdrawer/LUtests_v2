"""
GH Python (IronPython)
Description: Reconnect and re-route conduit polylines at a panel with optional Manhattan logic and device-aware tolerance.

Inputs:
    LineUtils       : LineUtils           — helper class instance used for panel reconnection logic
    panel           : rg.Rectangle3d      — panel outline in 3D
    panelplane      : rg.Plane            — panel plane used for projection and orientation
    polylines       : List[rg.Polyline]   — main input, list of conduit centreline polylines
    conduitsize     : List[float]         — conduit size per polyline; list length must match polylines
    spacing         : float               — target centre-to-centre distance between conduits
    removeshorts    : bool                — treat single-segment polylines as Manhattan runs if False; best to default at False
    pullstart       : bool                — when connections exit panel from both sides: single row if False, double row if True
    manhattanradius : float               — if end of a polyline is within this distance from panel centre, treat as Manhattan polyline
    devicemode      : bool                — enable device-aware logic using devicetolerance
    devicetolerance : float               — distance around connection rectangles within which a connection is considered covered

Outputs:
    reconnected : List[rg.Polyline] — list of reconnected / adjusted conduit polylines
"""

import Rhino.Geometry as rg
import Grasshopper as gh
import math
from collections import defaultdict
import itertools
import System
import random
import copy

class Panelconnection(object):
    def Run(self, LineUtils, panel, panelplane, polylines, conduitsizes, spacing = 1.0,
            removeshorts = False, pullstart = True, manhattanradius = 25.0,
            devicemode = False, devicetolerance = 0.0):
        
        GLOBAL_TOL = 0.01
        defaultpath = gh.Kernel.Data.GH_Path(0)
        unitX = rg.Vector3d(1, 0, 0)
        unitY = rg.Vector3d(0, 1, 0)
        unitZ = rg.Vector3d(0, 0, 1) 
        lineargap = 4.0 #4" between bends
        
        spacing_ = copy.deepcopy(spacing)
        spacing = 0
        
        conduitsizes_ = copy.deepcopy(conduitsizes)
        conduitsizes = [0 for _ in conduitsizes]
        
        #dont apply angled if offset is more than x minimal shifts
        offsetshitcoof = 10#2000#10.00
        
        sidesextra = 3.0
        
        n_items = len(polylines)
        orig_idx = list(range(n_items))  # tracks where each current item came from
        
        porigin = panelplane.Origin
        
        def x_positions(diameters, gap, angle_deg, padding, tol = GLOBAL_TOL):
            if angle_deg <= tol:
                return [0]
            ang = angle_deg * math.pi / 180.0
            n = len(diameters)
            if n == 0:
                return [0]
            # first center
            pos = padding + diameters[0] / 2.0
            if n == 1:
                return [0, pos, pos*2]
            centers = [pos]
            # subsequent centers
            for i in range(1, n):
                if ang == 0.0:
                    dx = diameters[i-1]/2.0 + gap + diameters[i]/2.0
                else:
                    dx = (diameters[i-1]/2.0 + gap + diameters[i]/2.0) / math.sin(ang)
                pos += dx
                centers.append(pos)
            # end of end padding
            end = centers[-1] + diameters[-1]/2.0 + padding
            values = [0]+centers+[end]
            rvalues = [round(v, 3) for v in values]
            
            return rvalues
        
        def split_up_down(plane, lines, tol = GLOBAL_TOL):
            origin_uv = plane.RemapToPlaneSpace(plane.Origin)[1]
            upper = []
            lower = []
            for i, ln in enumerate(lines):
                mid_uv = plane.RemapToPlaneSpace(ln.PointAt(0.5))[1]
                if mid_uv.X - origin_uv.X > tol:
                    upper.append((i, ln))
                else:
                    lower.append((i, ln))
            return upper, lower
        
        def classify_direction(plane, line, tol = GLOBAL_TOL):
            d = rg.Vector3d(line.Direction)
            d.Unitize()
            ax_y = rg.Vector3d(plane.XAxis)
            ax_x = rg.Vector3d(plane.YAxis)
            
            if abs(d * ax_y) >= 1.0 - tol:
                return 'straight'
                
            if d * ax_x > 0:
                return 'right'
            return 'left'
        
        def _sort_block(plane, items, tag, is_upper):
            if tag == 'straight':
                #key_fun = lambda it: plane.RemapToPlaneSpace(it[1].PointAtStart)[1].Y
                key_fun = lambda it: plane.RemapToPlaneSpace(it[1].From)[1].Y
                reverse_flag = False#True  # always descending Y
            else:
                #key_fun = lambda it: plane.RemapToPlaneSpace(it[1].PointAtStart)[1].X
                key_fun = lambda it: plane.RemapToPlaneSpace(it[1].From)[1].X
                if tag == 'left':
                    reverse_flag = is_upper  # upper -> asc lower -> desc
                else:  # 'right'
                    reverse_flag = not is_upper      # upper -> desc lower -> asc
            
            return sorted(items, key=key_fun, reverse=reverse_flag)
        
        def sort_lines(plane, lines, tol = GLOBAL_TOL):
            upper, lower = split_up_down(plane, lines, tol)
            #lower = []
            ordered = []
            
            for grp, is_upper in ((upper, False), (lower, True)):
                buckets = {'left': [], 'straight': [], 'right': []}
                tagorder = ['left', 'straight', 'right']
                if is_upper:
                    #tagorder.reverse()
                    pass
                
                #print "is_upper ", is_upper
                #print tagorder
                
                for idx, ln in grp:
                    buckets[classify_direction(plane, ln, tol)].append((idx, ln))
                
                #print buckets
                
                for tag in tagorder:
                    ordered.extend(_sort_block(plane, buckets[tag], tag, is_upper))
                    
            sorted_lines = [item[1] for item in ordered]
            index_map = [item[0] for item in ordered]
            
            return sorted_lines, index_map
        
        def snappolyline(polyline, plane, point, moveflag = False, tol = GLOBAL_TOL):
            if polyline.SegmentCount <= 2:
                #print tol
                return [False, polyline]
            
            firstsegment = polyline.SegmentAt(0)
            fsdir = firstsegment.UnitTangent
            planeX = plane.XAxis
            dot = fsdir*planeX
            
            result, targetplanept = plane.RemapToPlaneSpace(point)
                    
            newpoly = [None, None]
            
            polypts = list(polyline)
            firstp = polypts[0]
            secondp = polypts[1]
            otherpts = polypts[1:]
            otherpts2 = polypts[2:]
            
            _, firstplanep = plane.RemapToPlaneSpace(firstp)
            _, secondplanep = plane.RemapToPlaneSpace(secondp)
            
            #print tol
            
            if abs(dot) >= 1 - tol: #same dir
                
                #if False:#moveflag:
                if moveflag:
                    remappedxy = plane.PointAt(targetplanept.X, targetplanept.Y, firstplanep.Z)
                    remapped2nd = plane.PointAt(secondplanep.X, targetplanept.Y, secondplanep.Z) 
                    
                    newpoly = [True, rg.Polyline([remappedxy, remapped2nd]+otherpts2)]
                else:
                    #print "here"
                    remappedxy = plane.PointAt(targetplanept.X, firstplanep.Y, firstplanep.Z)
                    
                    newpoly = [False, rg.Polyline([remappedxy]+otherpts)]
            else:
                
                remappedxy = plane.PointAt(firstplanep.X, targetplanept.Y, firstplanep.Z)
                extrapt = plane.PointAt(targetplanept.X, targetplanept.Y, firstplanep.Z)
                
                newpoly = [True, rg.Polyline([extrapt, remappedxy]+otherpts)]
                #newpoly = [True, rg.Polyline([remappedxy]+otherpts)]
            #print "_______"
            
            #newpoly[1].DeleteShortSegments(tol)
            
            return newpoly
        
        def clean_polyline(pl, mindistance, tol = GLOBAL_TOL):
            # if ≤2 segments, nothing to do
            if pl.SegmentCount <= 2:
                return pl
                
            tol_rad = math.radians(tol)
            pts = list(pl)
            i = 0
            # walk sliding window of 3 segments -> 4 points
            
            while i <= len(pts) - 4:
                p0 = pts[i]
                p1 = pts[i+1]
                p2 = pts[i+2]
                p3 = pts[i+3]
                
                # first segment
                v1 = p1 - p0
                if not v1.Unitize():
                    i += 1
                    continue
                    
                # middle segment: capture its length before unitizing
                raw_v2 = p2 - p1
                seg2_len = raw_v2.Length
                v2 = rg.Vector3d(raw_v2)
                v2.Unitize()
                # third segment
                v3 = p3 - p2
                if not v3.Unitize():
                    i += 1
                    continue
                    
                # angles between segments
                ang12 = rg.Vector3d.VectorAngle(v1, v2)
                ang23 = rg.Vector3d.VectorAngle(v2, v3)
                
                # test both ~90° within tol
                if abs(ang12 - math.pi/2) <= tol_rad and abs(ang23 - math.pi/2) <= tol_rad:
                    # if middle is too short, remove it and merge
                    if seg2_len < mindistance + tol:
                        new_p3 = rg.Point3d(p3)
                        # align along axis of first segment
                        if abs(v1.X) > abs(v1.Y):
                            new_p3.Y = p0.Y
                        else:
                            new_p3.X = p0.X
                        # drop the middle point, replace next point
                        pts.pop(i+2)
                        pts[i+2] = new_p3
                        # shift index by extra 1 so next triplet spans correctly
                        i += 2
                        continue
                i += 1
             
            return rg.Polyline(pts)
        
        def clean_beginning(pl, mindistance, tol = GLOBAL_TOL):
            #print "in clean"
            # if ≤2 segments, nothing to do
            if pl.SegmentCount <= 2:
                return pl
            
            else:
                polypts = copy.deepcopy(list(pl))
                if polypts[1].DistanceTo(polypts[2]) <= mindistance:
                    shift = polypts[1]-polypts[2]
                    polypts[0] -= shift
                    #remove 2nd and 3rd pts
                    popd = polypts.pop(1)
                    popd = polypts.pop(1)
                    return rg.Polyline(polypts)
                else:
                    return pl 
        
        def extend_polyline_segments(pl, mindistance, mode='triplet', tol=GLOBAL_TOL):
            """
            Extend/collapse segments in a polyline.
            
            'triplet'  - three-seg groups: if middle seg is short, extend it.
            'singular' - each seg: if ≤ tol, collapse it
                         elif < mindistance+tol, extend to mindistance.
            'singular_first'- only the first segment
                              if ≤ tol, collapse it
                              elif < mindistance+tol, extend it.
            """
            pl.MergeColinearSegments(tol, False)
            
            # nothing to do for 0 or 1 segment
            if pl.SegmentCount <= 1:
                return pl
        
            # copy points and precompute tolerance in radians
            pts = list(pl)
            tol_rad = math.radians(tol)
        
            # --- Triplet mode ---
            if mode == 'triplet':
                i = 0
                max_i = len(pts) - 4
                while i <= max_i:
                    p0 = pts[i]
                    p1 = pts[i+1]
                    p2 = pts[i+2]
                    p3 = pts[i+3]
        
                    v1 = p1 - p0
                    if not v1.Unitize():
                        i += 1
                        continue
        
                    raw_v2 = p2 - p1
                    seg2_len = raw_v2.Length
                    v2 = rg.Vector3d(raw_v2)
                    v2.Unitize()
        
                    v3 = p3 - p2
                    if not v3.Unitize():
                        i += 1
                        continue
        
                    ang12 = rg.Vector3d.VectorAngle(v1, v2)
                    ang23 = rg.Vector3d.VectorAngle(v2, v3)
        
                    is_perp1 = abs(ang12 - math.pi/2) <= tol_rad
                    is_perp2 = abs(ang23 - math.pi/2) <= tol_rad
                    is_short = seg2_len < mindistance + tol
        
                    if is_perp1 and is_perp2 and is_short:
                        # compute new p2 extended to mindistance
                        new_p2 = rg.Point3d(p1)
                        new_p2 = new_p2 + v2 * mindistance
                        delta = new_p2 - p2
        
                        pts[i+2] = new_p2
        
                        # shift only p3 along the extension axis
                        if abs(raw_v2.X) > abs(raw_v2.Y):
                            pts[i+3].X += delta.X
                        else:
                            pts[i+3].Y += delta.Y
        
                        i += 2
                    else:
                        i += 1
        
            # --- Singular-first mode ---
            elif mode == 'singular_first':
                # only operate on the very first segment
                if len(pts) < 2:
                    return rg.Polyline(pts)
        
                p0 = pts[0]
                p1 = pts[1]
        
                raw_v = p1 - p0
                seg_len = raw_v.Length
        
                # collapse tiny first segment
                if seg_len <= tol:
                    delta = rg.Vector3d(raw_v)
                    pts.pop(1)
                    j = 1
                    while j < len(pts):
                        pts[j].X = pts[j].X - delta.X
                        pts[j].Y = pts[j].Y - delta.Y
                        pts[j].Z = pts[j].Z - delta.Z
                        j = j + 1
        
                # extend short first segment
                elif seg_len < mindistance + tol and len(pts) > 2:
                    v = rg.Vector3d(raw_v)
                    v.Unitize()
                    new_p1 = rg.Point3d(p0)
                    new_p1 = new_p1 + v * mindistance
                    ext_delta = new_p1 - p1
        
                    pts[1] = new_p1
        
                    # shift only the next point along dominant axis
                    if abs(raw_v.X) > abs(raw_v.Y):
                        pts[2].X = pts[2].X + ext_delta.X
                    else:
                        pts[2].Y = pts[2].Y + ext_delta.Y
        
                return rg.Polyline(pts)
        
            # --- Singular mode ---
            elif mode == 'singular':
                i = 0
                while i < len(pts) - 1:
                    p0 = pts[i]
                    p1 = pts[i+1]
        
                    raw_v = p1 - p0
                    seg_len = raw_v.Length
        
                    # collapse tiny segment
                    if seg_len <= tol:
                        delta = rg.Vector3d(raw_v)
                        pts.pop(i+1)
                        j = i + 1
                        while j < len(pts):
                            pts[j].X -= delta.X
                            pts[j].Y -= delta.Y
                            pts[j].Z -= delta.Z
                            j += 1
                        continue
        
                    # extend short segment, only if next point exists
                    if seg_len < mindistance + tol and i+2 < len(pts):
                        v = rg.Vector3d(raw_v)
                        v.Unitize()
                        new_p1 = rg.Point3d(p0)
                        new_p1 = new_p1 + v * mindistance
                        ext_delta = new_p1 - p1
        
                        pts[i+1] = new_p1
        
                        # shift only the very next point along dominant axis
                        if abs(raw_v.X) > abs(raw_v.Y):
                            pts[i+2].X += ext_delta.X
                        else:
                            pts[i+2].Y += ext_delta.Y
        
                    i += 1
        
            # unknown mode: return original
            else:
                return pl
        
            return rg.Polyline(pts)
        
        def repull(MasterPolys, SlavePolys):
            Tol = 0.001
            ANG_EPS = 1e-9
            ParallelDot = 0.999
            SegIndex = 1  
        
            def _unit_xy(v):
                if v.Length > 0.0:
                    v.Unitize()
                return v
        
            def _left_normal_xy(v):
                n = rg.Vector3d(-v.Y, v.X, 0.0)
                if n.Length > 0.0:
                    n.Unitize()
                return n
        
            def _dot_xy(a, b):
                return a.X * b.X + a.Y * b.Y
        
            def _to_polyline(obj):
                if obj is None:
                    return None
                if isinstance(obj, rg.Polyline):
                    return rg.Polyline(obj)
                if isinstance(obj, rg.PolylineCurve):
                    return obj.ToPolyline()
                try:
                    tmp = rg.Polyline()
                    ok = obj.TryGetPolyline(tmp)
                    if ok:
                        return tmp
                except:
                    pass
                return None
        
            Out = []
        
            m_count = len(MasterPolys)
            s_count = len(SlavePolys)
        
            for i in range(m_count):
                m_in = MasterPolys[i]
        
                if i >= s_count:
                    Out.append(m_in)
                    continue
        
                s_in = SlavePolys[i]
        
                m_pl = _to_polyline(m_in)
                s_pl = _to_polyline(s_in)
        
                if m_pl is None or s_pl is None:
                    Out.append(m_in)
                    continue
        
                if m_pl.SegmentCount != s_pl.SegmentCount:
                    Out.append(m_in)
                    continue
        
                if SegIndex < 0 or SegIndex >= m_pl.SegmentCount:
                    Out.append(m_in)
                    continue
        
                ok_parallel = True
                for j in range(m_pl.SegmentCount):
                    ml = m_pl.SegmentAt(j)
                    sl = s_pl.SegmentAt(j)
        
                    md = rg.Vector3d(ml.Direction.X, ml.Direction.Y, 0.0)
                    sd = rg.Vector3d(sl.Direction.X, sl.Direction.Y, 0.0)
        
                    if md.Length <= Tol or sd.Length <= Tol:
                        ok_parallel = False
                        break
        
                    _unit_xy(md)
                    _unit_xy(sd)
        
                    dot = md * sd
                    if dot < 0.0:
                        dot = -dot
        
                    if dot < ParallelDot:
                        ok_parallel = False
                        break
        
                if not ok_parallel:
                    Out.append(m_in)
                    continue
        
                mseg = m_pl.SegmentAt(SegIndex)
                sseg = s_pl.SegmentAt(SegIndex)
        
                dcur = rg.Vector3d(mseg.Direction.X, mseg.Direction.Y, 0.0)
                if dcur.Length <= Tol:
                    Out.append(m_in)
                    continue
                _unit_xy(dcur)
        
                ncur = _left_normal_xy(dcur)
                if ncur.Length <= Tol:
                    Out.append(m_in)
                    continue
        
                p = rg.Point3d(sseg.From)
                a = rg.Vector3d(p.X - mseg.From.X, p.Y - mseg.From.Y, 0.0)
                t = _dot_xy(a, dcur)
                proj = rg.Point3d(mseg.From.X + dcur.X * t, mseg.From.Y + dcur.Y * t, p.Z)
        
                v = rg.Vector3d(proj.X - p.X, proj.Y - p.Y, proj.Z - p.Z)
                d = _dot_xy(v, ncur)
        
                def _along(dir_vec):
                    if dir_vec.Length <= Tol:
                        return rg.Vector3d(ncur.X * d, ncur.Y * d, v.Z)
        
                    dp = rg.Vector3d(dir_vec.X, dir_vec.Y, 0.0)
                    _unit_xy(dp)
        
                    denom = _dot_xy(dp, ncur)
                    if abs(denom) < ANG_EPS:
                        return rg.Vector3d(ncur.X * d, ncur.Y * d, v.Z)
        
                    s = d / denom
                    return rg.Vector3d(dp.X * s, dp.Y * s, v.Z)
        
                segcount = s_pl.SegmentCount
                has_prev = False
                has_next = False
                prev_dir = rg.Vector3d(0.0, 0.0, 0.0)
                next_dir = rg.Vector3d(0.0, 0.0, 0.0)
        
                if SegIndex > 0:
                    pln = s_pl.SegmentAt(SegIndex - 1)
                    prev_dir = rg.Vector3d(pln.Direction.X, pln.Direction.Y, 0.0)
                    if prev_dir.Length > Tol:
                        has_prev = True
        
                if SegIndex < segcount - 1:
                    nln = s_pl.SegmentAt(SegIndex + 1)
                    next_dir = rg.Vector3d(nln.Direction.X, nln.Direction.Y, 0.0)
                    if next_dir.Length > Tol:
                        has_next = True
        
                if has_prev:
                    ds = _along(prev_dir)
                else:
                    ds = rg.Vector3d(ncur.X * d, ncur.Y * d, v.Z)
        
                if has_next:
                    de = _along(next_dir)
                else:
                    de = rg.Vector3d(ncur.X * d, ncur.Y * d, v.Z)
        
                pts = []
                for p0 in s_pl:
                    pts.append(rg.Point3d(p0))
        
                idx0 = SegIndex
                idx1 = SegIndex + 1
        
                if idx0 < 0 or idx1 >= len(pts):
                    Out.append(m_in)
                    continue
        
                p0 = pts[idx0]
                p1 = pts[idx1]
        
                pts[idx0] = rg.Point3d(p0.X + ds.X, p0.Y + ds.Y, p0.Z + ds.Z)
                pts[idx1] = rg.Point3d(p1.X + de.X, p1.Y + de.Y, p1.Z + de.Z)
        
                if s_pl.IsClosed:
                    if idx0 == 0:
                        pts[len(pts) - 1] = rg.Point3d(pts[0])
                    if idx1 == 0:
                        pts[len(pts) - 1] = rg.Point3d(pts[0])
        
                Out.append(rg.Polyline(pts))
            
            return Out
        
        def remove_spikes(pl, tol_deg=GLOBAL_TOL):
            """remove any back‑tracking spikes from a polyline
            spike is detected when two consecutive segments are nearly 180* apart 
            tolerance is defaulted to global tol, but much tighter is reccomended 0.0001
            """
            # if fewer than 2 segments, nothing to clean
            if pl.SegmentCount < 2:
                return pl
            tol = math.radians(tol_deg)
            pts = list(pl)
            i = 0
            while i < len(pts) - 2:
                p0 = pts[i]
                p1 = pts[i+1]
                p2 = pts[i+2]
                v1 = p1 - p0
                if not v1.Unitize():
                    i += 1
                    continue
                v2 = p2 - p1
                if not v2.Unitize():
                    i += 1
                    continue
                ang = rg.Vector3d.VectorAngle(v1, v2)
                # if they reverse direction within tol, drop the spike apex
                if abs(ang - math.pi) <= tol:
                    pts.pop(i+1)
                    # re‑test at same index since list got shorter
                    continue
                i += 1
            return rg.Polyline(pts)
        
        def middle_line_in_rectangle(rect, plane, tol=GLOBAL_TOL):
            center = rect.Center
            dir_y = plane.YAxis
            infinite_line = rg.Line(center - dir_y * 1e6, center + dir_y * 1e6)
        
            rect_curve = rect.ToNurbsCurve()
            intersections = rg.Intersect.Intersection.CurveLine(rect_curve, infinite_line, tol, tol)
        
            if not intersections or intersections.Count != 2:
                return None
        
            pt1 = intersections[0].PointA
            pt2 = intersections[1].PointA
            
            return rg.Line(pt1, pt2)
        
        def apply_perm(seq, perm):
            return [seq[i] for i in perm]
        
        def restore_input_order(seq, idx_track):
            n = len(idx_track)
            out = [None for _ in range(n)]
            for pos, orig in enumerate(idx_track):
                out[orig] = seq[pos]
            return out
        
        def snap_parameters(parameters0, parameters1):
            epsilon = 1e-9
            tol = 0.01
            max_iterations = 50
        
            def abs_float(x):
                if x < 0.0:
                    return -x
                return x
        
            p0 = []
            p1 = []
            i = 0
            for i in range(len(parameters0)):
                p0.append(float(parameters0[i]))
            i = 0
            for i in range(len(parameters1)):
                p1.append(float(parameters1[i]))
        
            n0 = len(p0)
            n1 = len(p1)
            if n0 == 0 or n1 == 0:
                return p0, p1
        
            min0 = p0[0]
            max0 = p0[0]
            i = 1
            for i in range(1, n0):
                v = p0[i]
                if v < min0:
                    min0 = v
                if v > max0:
                    max0 = v
            domain0 = max0 - min0
        
            min1 = p1[0]
            max1 = p1[0]
            i = 1
            for i in range(1, n1):
                v = p1[i]
                if v < min1:
                    min1 = v
                if v > max1:
                    max1 = v
            domain1 = max1 - min1
        
            best_diff = None
            anchor0 = 0
            anchor1 = 0
            i = 0
            for i in range(n0):
                a = p0[i]
                j = 0
                for j in range(n1):
                    b = p1[j]
                    d = a - b
                    if d < 0.0:
                        d = -d
                    if best_diff is None or d < best_diff:
                        best_diff = d
                        anchor0 = i
                        anchor1 = j
        
            if domain0 < domain1:
                delta = p1[anchor1] - p0[anchor0]
                i = 0
                for i in range(n0):
                    p0[i] = p0[i] + delta
            elif domain1 < domain0:
                delta = p0[anchor0] - p1[anchor1]
                j = 0
                for j in range(n1):
                    p1[j] = p1[j] + delta
            else:
                delta = p1[anchor1] - p0[anchor0]
                i = 0
                for i in range(n0):
                    p0[i] = p0[i] + delta
        
            anchor_value = p0[anchor0]
        
            locked0 = []
            locked1 = []
            i = 0
            for i in range(n0):
                locked0.append(False)
            i = 0
            for i in range(n1):
                locked1.append(False)
        
            locked0[anchor0] = True
            locked1[anchor1] = True
        
            def process_side(side):
                iteration = 0
                for iteration in range(max_iterations):
                    candidates = []
        
                    if side == -1:
                        i = 0
                        for i in range(anchor0):
                            if locked0[i]:
                                continue
                            d = p0[i] - anchor_value
                            if d < 0.0:
                                d = -d
                            candidates.append((d, 0, i))
                        j = 0
                        for j in range(anchor1):
                            if locked1[j]:
                                continue
                            d = p1[j] - anchor_value
                            if d < 0.0:
                                d = -d
                            candidates.append((d, 1, j))
                    else:
                        i = anchor0 + 1
                        for i in range(anchor0 + 1, n0):
                            if locked0[i]:
                                continue
                            d = p0[i] - anchor_value
                            if d < 0.0:
                                d = -d
                            candidates.append((d, 0, i))
                        j = anchor1 + 1
                        for j in range(anchor1 + 1, n1):
                            if locked1[j]:
                                continue
                            d = p1[j] - anchor_value
                            if d < 0.0:
                                d = -d
                            candidates.append((d, 1, j))
        
                    if not candidates:
                        break
        
                    candidates.sort()
        
                    changed = False
        
                    ci = 0
                    for ci in range(len(candidates)):
                        d_c, list_id, idx = candidates[ci]
        
                        if list_id == 0 and locked0[idx]:
                            continue
                        if list_id == 1 and locked1[idx]:
                            continue
        
                        if list_id == 0:
                            v_c = p0[idx]
                        else:
                            v_c = p1[idx]
        
                        # collect all "smaller or equal" (closer/equal to anchor) in other list
                        partner_indices = []
                        partner_dists = []
        
                        if list_id == 0:
                            # candidate in list 0, search list 1
                            if side == -1:
                                start = 0
                                end = anchor1
                            else:
                                start = anchor1 + 1
                                end = n1
                            j = start
                            for j in range(start, end):
                                if locked1[j]:
                                    continue
                                d_o = p1[j] - anchor_value
                                if d_o < 0.0:
                                    d_o = -d_o
                                if d_o < d_c - tol or abs_float(d_o - d_c) <= tol:
                                    partner_indices.append(j)
                                    partner_dists.append(d_o)
        
                            if len(partner_indices) > 0:
                                # pick partner furthest from anchor (max distance)
                                best_pos = 0
                                best_d = partner_dists[0]
                                t = 1
                                for t in range(1, len(partner_indices)):
                                    if partner_dists[t] > best_d + epsilon:
                                        best_d = partner_dists[t]
                                        best_pos = t
                                best_k = partner_indices[best_pos]
                                v_o = p1[best_k]
                                delta2 = v_c - v_o
        
                                if side == -1:
                                    k = 0
                                    for k in range(0, best_k + 1):
                                        p1[k] = p1[k] + delta2
                                else:
                                    k = best_k
                                    for k in range(best_k, n1):
                                        p1[k] = p1[k] + delta2
        
                                locked0[idx] = True
                                locked1[best_k] = True
        
                                # lock all closer ones from that list that also matched condition
                                t = 0
                                for t in range(len(partner_indices)):
                                    k2 = partner_indices[t]
                                    d2 = partner_dists[t]
                                    if k2 != best_k:
                                        if d2 + epsilon < best_d:
                                            locked1[k2] = True
        
                                changed = True
        
                        else:
                            # candidate in list 1, search list 0
                            if side == -1:
                                start = 0
                                end = anchor0
                            else:
                                start = anchor0 + 1
                                end = n0
                            i2 = start
                            for i2 in range(start, end):
                                if locked0[i2]:
                                    continue
                                d_o = p0[i2] - anchor_value
                                if d_o < 0.0:
                                    d_o = -d_o
                                if d_o < d_c - tol or abs_float(d_o - d_c) <= tol:
                                    partner_indices.append(i2)
                                    partner_dists.append(d_o)
        
                            if len(partner_indices) > 0:
                                best_pos = 0
                                best_d = partner_dists[0]
                                t = 1
                                for t in range(1, len(partner_indices)):
                                    if partner_dists[t] > best_d + epsilon:
                                        best_d = partner_dists[t]
                                        best_pos = t
                                best_k = partner_indices[best_pos]
                                v_o = p0[best_k]
                                delta2 = v_c - v_o
        
                                if side == -1:
                                    k = 0
                                    for k in range(0, best_k + 1):
                                        p0[k] = p0[k] + delta2
                                else:
                                    k = best_k
                                    for k in range(best_k, n0):
                                        p0[k] = p0[k] + delta2
        
                                locked1[idx] = True
                                locked0[best_k] = True
        
                                t = 0
                                for t in range(len(partner_indices)):
                                    k2 = partner_indices[t]
                                    d2 = partner_dists[t]
                                    if k2 != best_k:
                                        if d2 + epsilon < best_d:
                                            locked0[k2] = True
        
                                changed = True
        
                        if changed:
                            break
        
                    if not changed:
                        break
        
            process_side(-1)
            process_side(1)
        
            return p0, p1
        
        TolDeg = 1.0
        RightDeg = 90.0
        
        def _is_angle_non_orth(v1, v2, tol_deg):
            if v1.IsTiny() or v2.IsTiny():
                return False
            a = rg.Vector3d.VectorAngle(v1, v2)
            deg = math.degrees(a)
            m = deg % RightDeg
            if m > RightDeg * 0.5:
                m = RightDeg - m
            if m > tol_deg:
                return True
            return False
        
        def ispolyselfnonorth(pl):
            segs = pl.GetSegments()
            if len(segs) < 2:
                return False
            for i in range(len(segs) - 1):
                v1 = segs[i].Direction
                v2 = segs[i + 1].Direction
                if _is_angle_non_orth(v1, v2, TolDeg):
                    return True
            return False
        
        def ispolynonorthtoplane(pl, pln):
            segs = pl.GetSegments()
            if len(segs) == 0:
                return False
            v = segs[0].Direction
            x = pln.XAxis
            if _is_angle_non_orth(v, x, TolDeg):
                return True
            return False
        
        ExtLen = 10.0
        
        def poly_add_start_axis_segment(pl, pln):
            # Collect polyline points
            pts = []
            for p in pl:
                pts.append(p)
                
            if len(pts) < 2:
                return pl
        
            p0 = pts[0]
            p1 = pts[1]
        
            # First segment direction (projected into the plane to avoid Z/noise)
            v = p1 - p0
            v.Unitize()
            
            # Plane axes
            x = rg.Vector3d(pln.XAxis)
            y = rg.Vector3d(pln.YAxis)
        
            # Use sign of dot with XAxis to decide:
            # angle in [90..180] (side-agnostic)  <=>  dot(v, x) <= 0
            dx = v * x
            dy = v * y
            
            checkvec = p0 - pln.Origin
            checkvec.Unitize()
        
            dir_vec = None
        
            if dx >= 0.0:
                if checkvec * x < 0:
                    # Choose +Y or -Y based on which makes a shallower angle with the first segment
                    # This is equivalent to choosing the sign of dy in plane coords
                    dir_vec = rg.Vector3d(y)
                    if dy < 0.0:
                        dir_vec.Reverse()
                else:
                    # Choose XAxis, but flip it so it points "toward plane center" (plane origin)
                    dir_vec = rg.Vector3d(x)
                    dir_vec.Unitize()
                    if dir_vec*v < 0:
                        dir_vec.Reverse()
            else:
                if dx < 0 and checkvec * x < 0:
                    dir_vec = rg.Vector3d(x)
                    dir_vec.Reverse()
                else:
                    # Choose +Y or -Y based on which makes a shallower angle with the first segment
                    # This is equivalent to choosing the sign of dy in plane coords
                    dir_vec = rg.Vector3d(y)
                    if dy < 0.0:
                        dir_vec.Reverse()
        
            # IMPORTANT: we insert a NEW START point, so the new first segment is (p0 - p_new)
            # To make that segment direction == dir_vec, we must place p_new at (p0 - dir_vec * ExtLen)
            dir_vec.Unitize()
            p_new = p0 - dir_vec * ExtLen
            pts.insert(0, p_new)
        
            return rg.Polyline(pts)
        
        def scale_around(x, center, factor):
            return x - (center + (x - center) * factor)
        
        if devicemode:
            if abs(devicetolerance) > GLOBAL_TOL:
                panel = LineUtils.offset_rectangle(panel, devicetolerance)
        
        #reusing normal logic if not under condition, dirty patch
        run_else = False
        
        if devicemode and len(polylines) == 1:
            #print "devmode 1"
            dpolyline = polylines[0]
            firstseg = dpolyline.SegmentAt(0)
            hitspanel = LineUtils.lxr(firstseg, [panel], True)
            if hitspanel:
                #print "in panel"
                porigin = panelplane.Origin
                newp = firstseg.ClosestPoint(porigin, False) #treat as infinite
                polypts = list(dpolyline)
                polypts[0] = newp
                rerespaced = rg.PolylineCurve(polypts)
            else:
                run_else = True
        else:
            run_else = True
        
        #print run_else
        
        #portion to handle polylinebundle nonorth to panel
        for i, checkpoly in enumerate(polylines):
            selfno = ispolyselfnonorth(checkpoly)
            planeno = ispolynonorthtoplane(checkpoly, panelplane)
            #print planeno, selfno
            if planeno:
                stubbedpoly = poly_add_start_axis_segment(checkpoly, panelplane)
                polylines[i] = stubbedpoly
                
        #run a check if all segments are already near panel
        closetopanel = 100.0 #hardcoded distance where everythign else could get overriden and simplest direct connection made
        matchpanel = False
        pulledbuffer = []
        
        #buffercheck = 2 if len(polylines) <= 3 else 0
        
        for polybuffer in polylines:    
            firstseg = polybuffer.SegmentAt(0)
            hitspanel = LineUtils.lxr(firstseg, [panel], True)
            porigin = panelplane.Origin
            shortchecklen = porigin.DistanceTo(polybuffer.First)
            if hitspanel and shortchecklen < closetopanel:# and polybuffer.SegmentCount > buffercheck:
                newpstart = firstseg.ClosestPoint(porigin, False) #treat as infinite
                newpoly = rg.Polyline([newpstart]+list(polybuffer)[1:])
                pulledbuffer.append(newpoly)
            else:
                break
        else:
            #matchpanel branch if it didnt break
            matchpanel = True
        
        #print "matchpanel {}".format(matchpanel)
        
        if matchpanel:
            rerespaced = pulledbuffer
        elif run_else:
            polylines_ = []
            
            #short start to end collapsing
            planecenter = panelplane.Origin
            for poly in polylines:
                lastp = poly.Last
                dist = planecenter.DistanceTo(lastp)
                if dist <= manhattanradius:
                    newpol = rg.Polyline([planecenter, lastp])
                    polylines_.append(newpol)
                else:
                    polylines_.append(poly)
            
            polylines = polylines_

            #don't use other angles for now, keep 90
            #angleslookup = LineUtils.AngleLookup.ANGLES
            angleslookup = [90]
            
            #boundspreview = LineUtils.rectangle_axis(panel)
            boundspreview = middle_line_in_rectangle(panel, panelplane)
            
            panelwidth = boundspreview.Length
            od_lookup = [LineUtils.ConduitLookup.get_specs(cs)["od"] for cs in conduitsizes]
            
            #1.0" padding on both ends
            padding = 1.0
            positions = x_positions(od_lookup, spacing, 90, padding)
            mostgradualangle = 90
            
            if positions[-1] <= panelwidth:
                #loop from higher to lower except for 90
                for a in angleslookup[-2::-1]:
                    testpos = x_positions(od_lookup, spacing, a, padding)
                    if testpos[-1] <= panelwidth:
                        positions = testpos
                        mostgradualangle = a
                    else:
                        break
                
                #as the most gradual angle is found, center the positions
                offset = (panelwidth-positions[-1])/2
                positions = [p+offset for p in positions][1:-1]
            else:
                #in case positions dont fit even at 90*, scale uniformly to fit
                coof = panelwidth/positions[-1]
                positions = [p*coof for p in positions][1:-1]
            
            startpts = [boundspreview.PointAtLength(p) for p in positions]
            
            boundspreviewnormal = boundspreview.UnitTangent
            
            #print "mostgradualangle : {}".format(mostgradualangle)
            
            #debugging
            b = startpts 
            firstsegments = [poly.SegmentAt(0) for poly in polylines]
            upperg, lowerg = split_up_down(panelplane, firstsegments)
            try:
                uidx, upper = zip(*upperg)
            except:
                pass
            try:
                lidx, lower = zip(*lowerg) 
            except:
                pass
            #debugging end
            
            #loop start
            iteration_counter = 0
            max_iterations = 5 #was 5
            
            #save og before changes
            ogpolylines = [rg.Polyline(list(poly)) for poly in polylines]
            lastflags = [False for _ in ogpolylines]
            
            # set up a dict to hold each quadrant’s offset
            offsetsdict = dict.fromkeys(('upperleft','upperright','lowerleft','lowerright'), 0)
            
            while iteration_counter < max_iterations:
                iteration_counter += 1
                #print [p.Length for p in polylines]
                
                #prefilter
                for p in polylines:
                    p.MergeColinearSegments(GLOBAL_TOL, False)
                    p.DeleteShortSegments(GLOBAL_TOL)
            
                #print [p.Length for p in polylines]
                
                firstsegments = [poly.SegmentAt(0) for poly in polylines]
                sorted_curves, lookupidx = sort_lines(panelplane, firstsegments)
                
                polylines = apply_perm(polylines, lookupidx)
                conduitsizes = apply_perm(conduitsizes, lookupidx)
                lastflags = apply_perm(lastflags, lookupidx)
                orig_idx = apply_perm(orig_idx, lookupidx)
                sorted_polys = polylines
                
                #snapping pass
                #print "iteration ", iteration_counter
                #print "prepass", lastflags
                
                flags, polylines = zip(*[snappolyline(polyline, panelplane, point, mflag) for polyline, point, mflag in zip(sorted_polys, startpts, lastflags)])
                #flags, polylines = zip(*[snappolyline(polyline, panelplane, point, True) for polyline, point, mflag in zip(sorted_polys, startpts, lastflags)])
                
                lastflags = list(flags)
                
                #print [p.Length for p in polylines], "here"
                #print "afterpass", lastflags
                
                #polylines = snapped
                tweakedpoly = []
                
                for poly, conduitsize, conduitsize_, pidx in zip(polylines, conduitsizes, conduitsizes_, range(len(polylines))):
                    #print "here", iteration_counter
                    od_size = LineUtils.ConduitLookup.get_specs(conduitsize)["od"]
                    #linearstub = LineUtils.ConduitLookup.get_specs(conduitsize)['linear_section']
                    #bendradius = LineUtils.ConduitLookup.get_specs(conduitsize)['min_bend']
                    linearstub = LineUtils.ConduitLookup.get_specs(conduitsize_)['linear_section']
                    bendradius = LineUtils.ConduitLookup.get_specs(conduitsize_)['min_bend']
                    
                    startcut = LineUtils._compute_cut(bendradius, linearstub, 90)
                    
                    #to be safe calculated at 2x 90 degree turns + the linear section between
                    #checklength = 0#experiment at 0
                    checklength = lineargap + startcut*2 
                    
                    #print checklength
                    
                    first_s = poly.SegmentAt(0)
                    first_s_len = first_s.Length
                    
                    next_s_len = float('inf')
                    if poly.SegmentCount > 1:
                        next_s = poly.SegmentAt(1)
                        next_s_len = next_s.Length
                    
                    polypts = list(poly)
                    
                    filteredpts = polypts
                    
                    #print "iteration ", iteration_counter

                    #checking first and second for potentiall shortness
                    #print first_s.Length, checklength, next_s_len
                    #print first_s.From.DistanceTo(porigin), closetopanel
                    
                    #only do aggresive optimizations if already close to panel
                    if first_s.Length < checklength or next_s_len < checklength and first_s.From.DistanceTo(porigin) < closetopanel:
                        lastflags[pidx] = False #reset flag
                        #print next_s_len < checklength
                        if len(polypts) == 2:
                            #unchanged
                            pass
                        elif abs(boundspreviewnormal*first_s.UnitTangent) < GLOBAL_TOL or next_s_len < checklength:
                            #if the first segment is short and perpendicular to panel
                            #need to also remove second to fix it
                            #or if the second is too short need to remove 1st and 2nd
                            #remove first 2 segments
                            if len(polypts) > 3:
                                filteredpts = polypts[2:]
                            else:
                                filteredpts = polypts[1:]
                            #print "here"
                        else:
                            #print "here"
                            #remove first segment, leave just last one
                            filteredpts = polypts[1:]
                        #else:
                            #remove first 2 segments
                            #filteredpts = polypts[2:]
                    
                    else:
                        pass
                        #print "passed"
                    
                    if abs(boundspreviewnormal*first_s.UnitTangent) < GLOBAL_TOL and False:
                        #print "here"
                        filteredpts = filteredpts[1:] #remove 1 more
            #        if next_s_len < checklength:
            #            #print next_s_len
            #            filteredpts = filteredpts[1:] #remove 1 more
                    
                    tweakedpoly.append(rg.Polyline(filteredpts))
                
                #print "afterlenchecks", lastflags
                
                #reassign
                polylines = tweakedpoly
            
            #print [p.Length for p in polylines]
            
            #snap too close segments
            adjustedpoly = []
            
            smallestangle = LineUtils.AngleLookup.ANGLES[0]
            #print smallestangle, "smallestangle"
            
            #prefilter
            for p in polylines:
                p.MergeColinearSegments(GLOBAL_TOL, False)
                p.DeleteShortSegments(GLOBAL_TOL)
            
            checkpolys = polylines
            c = []
            
            
            sorters = []
            upperleft = []
            upperright = []
            lowerleft = []
            lowerright = []
            
            #print polylines
            #print [p.Length for p in polylines]
            
            #print "START HERE"
            
            for pl, p, idx in zip(polylines, startpts, range(len(polylines))):
                nc = pl.ToNurbsCurve()
                p2 = nc.PointAtLength(min(pl.Length-GLOBAL_TOL, 20.0))
                sline = rg.Line(p, p2)
                sorters.append(sline)
                u, l = split_up_down(panelplane, [sline])
                if u:
                    #print u[0][1]
                    dir = classify_direction(panelplane, u[0][1], 0.0001)
                    if dir == "left":
                        upperleft.append(idx)
                    else:
                        upperright.append(idx)
                if l:
                    dir = classify_direction(panelplane, l[0][1], 0.0001)
                    #print dir
                    if dir == "left":
                        lowerleft.append(idx)
                    else:
                        lowerright.append(idx)
            
            #print "upperleft {}, upperright {}, lowerleft {}, lowerright {}".format(upperleft, upperright, lowerleft, lowerright)
            
            # build a lookup dict mapping each index to its “quadrant” name
            quadrant = {}
            quadrant.update({i: 'upperleft'   for i in upperleft})
            quadrant.update({i: 'upperright'  for i in upperright})
            quadrant.update({i: 'lowerleft'   for i in lowerleft})
            quadrant.update({i: 'lowerright'  for i in lowerright})
            
            #print quadrant
            #print offsetsdict
            
            #sortedsorters, lookupidx = sort_lines(panelplane, sorters)
            #
            #print lookupidx
            
            ##offset for 90 degree turns
            #curroffset = 0
            #upperleftoffset = 0
            #upperrightoffset = 0
            #lowerleftoffset = 0
            #lowerrightoffset = 0
            
            #resort for finalprocessing
            neworder = range(len(polylines))
            neworder = upperleft + upperright[::-1] + lowerleft + lowerright[::-1]
            
            polylines = apply_perm(polylines, neworder)
            conduitsizes = apply_perm(conduitsizes, neworder)
            startpts = apply_perm(startpts, neworder)
            orig_idx = apply_perm(orig_idx, neworder)
            
            #print neworder
            #neworder = [neworder[i] for i in neworder]
            
            for polyline, conduitsize, conduitsize_, point, sortidx in zip(polylines, conduitsizes, conduitsizes_, startpts, range(len(polylines))):
                #print sortidx
                q = quadrant.get(sortidx)
                #print loc
                
                polyline.MergeColinearSegments(GLOBAL_TOL, False)
                #rg.Polyline.MergeColinearSegments(GLOBAL_TOl, FALSE)
                
                od_size = LineUtils.ConduitLookup.get_specs(conduitsize)["od"]
                #linearstub = LineUtils.ConduitLookup.get_specs(conduitsize)['linear_section']
                #bendradius = LineUtils.ConduitLookup.get_specs(conduitsize)['min_bend']
                linearstub = LineUtils.ConduitLookup.get_specs(conduitsize_)['linear_section']
                bendradius = LineUtils.ConduitLookup.get_specs(conduitsize_)['min_bend']
                
                #calculate for smallest angle
                startcut = LineUtils._compute_cut(bendradius, linearstub, smallestangle)
                
                minlength = lineargap + startcut*2 
                minimalraise = LineUtils.compute_raise(minlength, smallestangle)
                
                polypts = list(polyline)
                
                first_s = polyline.SegmentAt(0)
                firstp = polypts[0]
                secondp = polypts[1]
                otherpts2 = polypts[2:]
                
                c.append(first_s)
                
                #print first_s.UnitTangent
                #print  round(abs(boundspreviewnormal*first_s.UnitTangent))
                #print polyline.SegmentCount
                #print "___"
            
                _, planep = panelplane.RemapToPlaneSpace(point)
                _, firstplanep = panelplane.RemapToPlaneSpace(firstp)
                
                if abs(boundspreviewnormal*first_s.UnitTangent) < GLOBAL_TOL:
                    heightshiftsigned = planep.Y - firstplanep.Y
                    heightshift = abs(heightshiftsigned)
                    #if startsegment is within minlength from panel exit
                    #than shift it to panel exit
                    if heightshift < minimalraise:# and False:
                        print heightshift ,minimalraise
                        #print "first trigger"
                        _, secondplanep = panelplane.RemapToPlaneSpace(secondp)
                        #print "shifting"
                        remappedxy = panelplane.PointAt(planep.X, planep.Y, firstplanep.Z)
                        remapped2nd = panelplane.PointAt(secondplanep.X, planep.Y, secondplanep.Z) 
                        
                        newpoly = rg.Polyline([remappedxy, remapped2nd]+otherpts2)
                        adjustedpoly.append(newpoly)
                    #else process shift at specified parameters
                    else:
                        #print "in here"
                        anglecalc = LineUtils.fit_angle_to_height(minlength, heightshift)
                        minfitted = LineUtils.smallest_ge(LineUtils.AngleLookup.ANGLES, anglecalc)
                        
                        offsetdist = abs(planep.Y -firstplanep.Y)
                        
                        #at the most gradual offset
                        #mostgradualangle = 45
                        #print mostgradualangle
                        startcut_ = LineUtils._compute_cut(bendradius, linearstub, mostgradualangle)
                        minlength_ = lineargap + startcut_*2 
                        minimalraise_ = LineUtils.compute_raise(minlength_, mostgradualangle)
                        minrun = LineUtils.compute_run(minlength_, mostgradualangle)
                        minopp = LineUtils.compute_opposite(offsetdist, 90-mostgradualangle)
                        
                        _, secondplanep = panelplane.RemapToPlaneSpace(secondp)
                        
                        conditions = [
                            first_s.Length >= minopp+minlength,   #length of first segment has to be larger than minimal opposite righttriangle side and minimal length of 2 fitting + space between
                            offsetdist >= minimalraise_,  #it has to be shifted more than minimalraise else fittings + space between wont fit
                            offsetdist <= minimalraise_*offsetshitcoof,  #this is a visual addition to prevent extremely long angled segments
                            mostgradualangle < 90  #90 degree isnt angled, it has to start with straight segment, so its excluded
                        ]
                        
                        #need to add 2 fittings at end
                        #if first_s.Length >= minopp+minlength and offsetdist >= minimalraise_ and offsetdist <= minimalraise_*offsetshitcoof and mostgradualangle < 90: 
                        if all(conditions): #too many conditions, more elegant this way
                            #print minimalraise_*offsetshitcoof
                            #print "can fit !!"
                            newp = first_s.PointAtLength(minopp) #pnt at distance and at parameter ISNT always same for lines
                            #panelplane.PointAt(minopp, secondplanep.Y, secondplanep.Z)
                            adjustedpoly.append(rg.Polyline([point, newp, secondp]+otherpts2))
                        else:
                            #print "here"
                            #if point falls within plane, let it be
                            if abs(firstplanep.Y) <= panelwidth/2 and len(polylines) == 1:
                                #print "here"
                                adjustedpoly.append(polyline)
                            else:
                                #start offsets
                                curroffset = 0
                                
                                if offsetsdict[q] == 0:
                                    offsetsdict[q] = minlength
                                else:
                                    offsetsdict[q] = offsetsdict[q] + od_size + spacing
                                
                                curroffset = offsetsdict[q]
            #                    if curroffset == 0:
            #                        curroffset = minlength
            #                    else:
            #                        #add spacing and its diameter (diamter isnt super accurate but will do)
            #                        curroffset += od_size + spacing
                                
                                if secondplanep.X > 0:
                                    newpone = panelplane.PointAt(curroffset, planep.Y, planep.Z)
                                    newptwo = panelplane.PointAt(curroffset, secondplanep.Y, planep.Z)
                                else:
                                    newpone = panelplane.PointAt(-curroffset, planep.Y, planep.Z)
                                    newptwo = panelplane.PointAt(-curroffset, secondplanep.Y, planep.Z)
                                
                                adjustedpoly.append(rg.Polyline([point, newpone, newptwo, secondp]+otherpts2))
                                    
                                #print "cant fit"
                        
                        #print planep.Y, firstplanep.Y, offsetdist, "___",minlength_,   minimalraise_, minrun, "__", minopp
                        
                        #
                        #print anglecalc, minfitted
                        
                        #print minlength, heightshift, anglecalc, heightshiftsigned
                        #print minfitted
                        #print "___"
                        
                        #if panel exits dont fit for minimal segments length in a bundle
                        #compress all to fit
                        
                        #if 90 degrees need extra processing
                        if mostgradualangle >= 90:
                            pass
                            #adjustedpoly.append(polyline)
                        #under 90 degrees gradual, do gradual directly out of panel
                        else:
                            #print mostgradualangle
                            pass
                            #adjustedpoly.append(polyline)
                    #print planep.Y
                    #print firstp.Y
                    
                    #print "pass"
                    
                #perpendicular
                else:
                    #print "here"
                    #check if it can connect
                    _, secondplanep = panelplane.RemapToPlaneSpace(secondp)
                    #print secondplanep
                    #print planep
                    secondshifted = rg.Point3d(secondplanep.X, planep.Y, secondplanep.Z)
                    #print secondshifted
                    checkdist = secondplanep.DistanceTo(secondshifted)
                    #just a direct connection
                    if checkdist<minlength and len(polypts) == 2 and removeshorts:
                        #print "direct connection"
                        #adjustedpoly.append(rg.Polyline([point, secondp]))
                        pass
                        adjustedpoly.append(rg.Polyline([point, secondp]))
                    #90* connection
                    else:
                        #print "90* connection"
                        shiftedinplane = panelplane.PointAt(secondshifted.X, secondshifted.Y, secondshifted.Z)
                        #adjustedpoly.append(rg.Polyline([point, shiftedinplane, secondp]))
                        adjustedpoly.append(rg.Polyline([point, shiftedinplane, secondp]+otherpts2))
                    #print checkdist
                    #print "perpendicular"
                    #a = snappolyline(polyline, panelplane, point, False, 0.02)
                    #print "aftersnap"
                    #adjustedpoly.append(polyline)
                    #not perpendicular to panel
                    pass
                #print minimalraise
            
            readjustedpoly = []
            
            upperleftmin = 0
            upperrightmin = 0
            lowerleftmin = 0
            lowerrightmin = 0
            
            upperleftfs = []
            upperrightfs = []
            lowerleftfs = []
            lowerrightfs = []
            
            def finalsortkey(poly):
                _, p = panelplane.RemapToPlaneSpace(list(poly)[0])
                return round(p.Y, 3)
            
            def fit_number(lst, x ,spacing, tol = GLOBAL_TOL):
                if not lst:
                    return x
                    
                s=sorted(lst)
                c=x
                
                while True:
                    blocker=None
                    for y in s:
                        # only tolerate being closer than (spacing - GLOBAL_TOL)
                        if abs(c-y) < spacing - tol:
                            blocker=y
                            break
                    # no conflicts -> c fits everywhere
                    if blocker is None:
                        return c
                    # bump c up just past the blocker by full spacing
                    c=blocker + spacing
            
            fittol = 0.01
            
            for polyline_, conduitsize in zip(adjustedpoly, conduitsizes):
                od_size = LineUtils.ConduitLookup.get_specs(conduitsize)["od"]
                linearstub = LineUtils.ConduitLookup.get_specs(conduitsize)['linear_section']
                bendradius = LineUtils.ConduitLookup.get_specs(conduitsize)['min_bend']
                
                polyline = polyline_
                
                #calculate for smallest angle
                startcut = LineUtils._compute_cut(bendradius, linearstub, smallestangle)
                
                minlength = lineargap + startcut*2 
                
                secondsegment = polyline.SegmentAt(1) if polyline.SegmentCount > 1 else polyline.SegmentAt(0)
                firstslen = polyline.SegmentAt(0).Length
                
                u, l = split_up_down(panelplane, [secondsegment])
                
                minoffset = minlength
                
                spcng = od_size + spacing
                #minlen = minlength-spcng
                minlen = minlength
                #print "spacing {}".format(spcng)
                
                #startcut = 0.01 #testing
                
                if u:
                    #print u[0][1]
                    dir = classify_direction(panelplane, u[0][1], 0.0001)
                    if dir == "left":
                        if upperleftmin == 0:
                            upperleftmin = minlen
                            #
                        else:
                            upperleftmin += spcng
                        #minoffset = upperleftmin
                        #upperleftfs.append(max(firstslen, upperleftmin))
                        minoffset = fit_number(upperleftfs, upperleftmin, spcng, fittol) 
                        upperleftfs.append(max(firstslen, minoffset))
                    else:
                        if upperrightmin == 0:
                            upperrightmin = minlen
                        else:
                            upperrightmin += spcng
                        #minoffset = upperrightmin
                        #upperrightfs.append(max(firstslen, upperrightmin))
                        minoffset = fit_number(upperrightfs, upperrightmin, spcng, fittol) 
                        upperrightfs.append(max(firstslen, minoffset))
                if l:
                    dir = classify_direction(panelplane, l[0][1], 0.0001)
                    #print dir
                    if dir == "left":
                        if lowerleftmin == 0:
                            lowerleftmin = minlen
                        else:
                            lowerleftmin += spcng
                        #minoffset = lowerleftmin
                        #lowerleftfs.append(max(firstslen, lowerleftmin))
                        #print lowerleftfs
                        #print lowerleftmin
                        minoffset = fit_number(lowerleftfs, lowerleftmin, spcng, fittol) 
                        lowerleftfs.append(max(firstslen, minoffset))
                        #print minoffset
                        #minoffset = 0
                    else:
                        if lowerrightmin == 0:
                            lowerrightmin = minlen
                        else:
                            lowerrightmin += spcng
                        #minoffset = lowerrightmin
                        #lowerrightfs.append(max(firstslen, lowerrightmin))
                        minoffset = fit_number(lowerrightfs, lowerrightmin, spcng, fittol) 
                        lowerrightfs.append(max(firstslen, minoffset))
                
                #ensure minlength for all segments, but calculated first only for first obv
                #extended = extend_polyline_segments(polyline, minlength, 'singular')
                #extended = extend_polyline_segments(extended, minoffset, 'singular_first')
                extended = extend_polyline_segments(polyline, minoffset, 'singular_first')
        
                polyline = extended
                
                #iteratively clean for a couple iterations
                for j in range(0):
                    unspiked = remove_spikes(polyline, 0.0001)
                    if unspiked.SegmentCount <= 3:
                        pass
                        minlength = startcut*2  #let it fit without linear segment
                        minlength = 0.01
                        
                    cleaned = clean_polyline(unspiked, minlength)
            
                    polyline = cleaned
                
                #extended = extend_polyline_segments(polyline, minlength, 'singular')
                #extended = polyline
                #print minlength
                
                readjustedpoly.append(polyline)
                #readjustedpoly.append(polyline_)
            
            readjustedpoly_debug = [rc.ToPolylineCurve() for rc in readjustedpoly]
            
            ##finalsort
            #firstsegments = [poly.SegmentAt(1) for poly in adjustedpoly]
            ##print firstsegments
            #sorted_curves, lookupidx = sort_lines(panelplane, firstsegments)
            #
            #print lookupidx
            
            adjustedpoly = restore_input_order(adjustedpoly, orig_idx)
            readjustedpoly = restore_input_order(readjustedpoly, orig_idx)
            polylines = restore_input_order(polylines, orig_idx)
            
            snapped = polylines
            
            # ---- extra per-side push using 2nd segment in panelplane X ----
            
            origin_ok, origin_uv = panelplane.RemapToPlaneSpace(panelplane.Origin)
            
            left_indices = []
            right_indices = []
            center_indices = []
            mid_x_values = []
            
            for idx, pl in enumerate(readjustedpoly):
                if pl.SegmentCount > 1:
                    seg = pl.SegmentAt(1)
                else:
                    seg = pl.SegmentAt(0)
            
                mid_pt = seg.PointAt(0.5)
                remap_ok, mid_uv = panelplane.RemapToPlaneSpace(mid_pt)
            
                if remap_ok:
                    mid_x = mid_uv.X
                    dx = mid_x - origin_uv.X
                else:
                    mid_x = None
                    dx = 0.0
            
                mid_x_values.append(mid_x)
            
                if dx > GLOBAL_TOL:
                    left_indices.append(idx)
                elif dx < -GLOBAL_TOL:
                    right_indices.append(idx)
                else:
                    center_indices.append(idx)
            
            # if some land exactly on origin X, assign them to the smaller side
            for idx in center_indices:
                if len(left_indices) <= len(right_indices):
                    left_indices.append(idx)
                else:
                    right_indices.append(idx)
            
            # find bundles: indices whose 2nd segment X matches some other 2nd segment X
            stacked_indices = set()
            for i in range(len(mid_x_values)):
                x_i = mid_x_values[i]
                if x_i is None:
                    continue
                for j in range(len(mid_x_values)):
                    if i == j:
                        continue
                    x_j = mid_x_values[j]
                    if x_j is None:
                        continue
                    if abs(x_j - x_i) <= GLOBAL_TOL:
                        stacked_indices.add(i)
                        break
            
            n_left = len(left_indices)
            n_right = len(right_indices)
            #print "n_left, n_right:", n_left, n_right
            
            extra_left = 0.0
            extra_right = 0.0
            
            #for now
            smallestconduit = min(conduitsizes_)
            
            if spacing_ > 0.0:
                if n_left > 1:
                    extra_left = 0.5 * (spacing_ + smallestconduit) * float(n_left - 1)
                if n_right > 1:
                    extra_right = 0.5 * (spacing_ + smallestconduit) * float(n_right - 1)
            
            #print extra_left, extra_right
            
            # direction along which the 2nd segment should move "away" in panelplane
            push_axis = rg.Vector3d(panelplane.XAxis)  # change to YAxis if that is your push dir
            if not push_axis.IsZero:
                push_axis.Unitize()
            
                new_readjusted = []
            
                for idx, pl in enumerate(readjustedpoly):
                    d = 0.0
                    if idx in left_indices:
                        d = extra_left
                    elif idx in right_indices:
                        d = -extra_right  # negative to move away from origin on the other side
            
                    # only push if:
                    # - this index is part of a stacked bundle (same X as others)
                    # - 2nd segment is NOT the last one
                    if d != 0.0 and idx in stacked_indices:
                        seg_count = pl.SegmentCount
                        if seg_count > 2 and pl.Count > 2:
                            move_vec = rg.Vector3d(push_axis)
                            move_vec = move_vec * d
            
                            pts = list(pl)
                            # move only the 2nd segment endpoints: pts[1] and pts[2]
                            pts[1] = pts[1] + move_vec
                            pts[2] = pts[2] + move_vec
            
                            new_pl = rg.Polyline(pts)
                            new_readjusted.append(new_pl)
                        else:
                            new_readjusted.append(pl)
                    else:
                        new_readjusted.append(pl)
            
                readjustedpoly = new_readjusted
            
            # ---- end extra per-side push ----
            
            #cached
            spacing = spacing_
            conduitsize = gh.DataTree[System.Object]()#conduitsizes_
            polylines = gh.DataTree[System.Object]()
            
            conduitsize.AddRange(conduitsizes_, defaultpath)
            polylines.AddRange(readjustedpoly, defaultpath)
            
            polylines_LR = gh.DataTree[System.Object]()
            conduitsize_LR = gh.DataTree[System.Object]()
            
            path_left = gh.Kernel.Data.GH_Path(0)
            path_right = gh.Kernel.Data.GH_Path(1)
            
            for idx, pl in enumerate(readjustedpoly):
                size = conduitsizes_[idx]
            
                if idx in left_indices:
                    polylines_LR.Add(pl, path_left)
                    conduitsize_LR.Add(size, path_left)
                elif idx in right_indices:
                    polylines_LR.Add(pl, path_right)
                    conduitsize_LR.Add(size, path_right)
                else:
                    # should not happen because center_indices are reassigned,
                    # but keep it in defaultpath just in case
                    polylines_LR.Add(pl, defaultpath)
                    conduitsize_LR.Add(size, defaultpath)
            
            #print conduitsize.Branch(0)
            #print polylines.Branch(0)
            #print  gh.DataTree[System.Int32]([0], defaultpath)
            
            sp = LineUtils.Spacing()
            
            #sp_results = sp.Run(polylines, conduitsize, optionalkeys = gh.DataTree[System.Int32]([0], defaultpath),
            #                    spacing = spacing, perpanel = False, perlevel = False, 
            #                    pulltogether = True, pushflag = False, pullstart = pullstart)
            
            #pushflag is resource intensive
            sp_results = sp.Run(polylines_LR, conduitsize_LR, optionalkeys = gh.DataTree[System.Int32]([0], defaultpath),
                                spacing = spacing, perpanel = True, perlevel = False, 
                                pulltogether = True, pushflag = False, pullstart = pullstart)
            
            rawlinelookup, linelookup, rebuiltree, polys, polys2, finaltree, treeflags, doublepolys, Boundaryobjects = sp_results
            
            #2 step process for 2nd segment to ensure proper order
            #repull(MasterPolys, SlavePolys)
            repulltest = gh.DataTree[System.Object]()
            
            for path in polylines_LR.Paths:
                masterpolys = list(polylines_LR.Branch(path))
                slavepolys = list(finaltree.Branch(path))
                #print " len(masterpolys), len(slavepolys)", len(masterpolys), len(slavepolys)
                repulled = repull(masterpolys, slavepolys)
                #print "repulled ", len(repulled)
                repulltest.AddRange(repulled, path)
                #repulltest.extend(repulled)
            
            sp2 = LineUtils.Spacing()
            sp_results2 = sp2.Run(repulltest, conduitsize_LR, optionalkeys = gh.DataTree[System.Int32]([0], defaultpath),
                                spacing = spacing, perpanel = True, perlevel = False, 
                                pulltogether = True, pushflag = False, pullstart = pullstart)
                                
            rawlinelookup, linelookup, rebuiltree, polys, polys2, rerespaced_, treeflags, doublepolys, Boundaryobjects = sp_results2
            finaltree = gh.DataTree[System.Object]()
            
            for path in rerespaced_.Paths:
                r_polys = list(rerespaced_.Branch(path))
                c_sizes = list(conduitsize_LR.Branch(path))
                
                for rpoly, conduitsize in zip(r_polys, c_sizes):
                    od_size = LineUtils.ConduitLookup.get_specs(conduitsize)["od"]
                    linearstub = LineUtils.ConduitLookup.get_specs(conduitsize)['linear_section']
                    bendradius = LineUtils.ConduitLookup.get_specs(conduitsize)['min_bend']
                    
                    startcut = LineUtils._compute_cut(bendradius, linearstub, smallestangle)
                    minlength = lineargap + startcut*2 
                    minlength_ = startcut*2 
                    
                    #cleaned = clean_polyline(rpoly, minlength)
                    cleaned = clean_beginning(rpoly, minlength_) #do without linear as more conservative for now 
                    finaltree.Add(cleaned, path)
            
            respaced = []
            
            planeY = panelplane.YAxis
            planeY.Unitize()
            
            cutstart = True
            
            if finaltree.BranchCount <= 1:
                cutstart = False
                #for simplicity of unification
                
                if path_left in finaltree.Paths:
                    finaltree.AddRange([], path_right)
                else:
                    finaltree.AddRange([], path_left)
            
            #if only one line on a side and it would be reasonable to just run it straight
            porigin = panelplane.Origin
            panelXax = panelplane.XAxis
            
            for branch in finaltree.Branches:
                if len(branch) == 1:
                    #checking hits
                    dpolyline = branch[0]
                    firstseg = dpolyline.SegmentAt(0)
                    lastseg = dpolyline.SegmentAt(dpolyline.SegmentCount - 1)
                    hitspanel1 = LineUtils.lxr(lastseg, [panel], True)
                    hitspanel2 = LineUtils.lxr(firstseg, [panel], True)
                    
                    shortchecklen = porigin.DistanceTo(dpolyline.Last)
                    manhcheck = shortchecklen <= manhattanradius
                    #short segment manhattan
                    if manhcheck:
                        #print "shortie"
                        checkline = rg.Line(dpolyline.Last,  panelXax)
                        hitcheck = LineUtils.lxr(checkline, [panel], True)
                        newp = checkline.ClosestPoint(porigin, False) #treat as infinite
                        newpoly = rg.Polyline([newp, dpolyline.Last])
                        branch[0] = newpoly
                    else:
                        if hitspanel1 and hitspanel2 and manhcheck:
                            #print "in panel"
                            newp = lastseg.ClosestPoint(porigin, False) #treat as infinite
                            newpoly = rg.Polyline([newp, dpolyline.Last])
                            branch[0] = newpoly
                else:
                    for i in range(len(branch)):
                        dpolyline = branch[i]
                        #snake segments within a panel, special case, was 3 do for all ? 
                        if dpolyline.SegmentCount == 3:
                            firstseg = dpolyline.SegmentAt(0)
                            lastseg = dpolyline.SegmentAt(dpolyline.SegmentCount - 1)
                            hitspanel1 = LineUtils.lxr(lastseg, [panel], True)
                            hitspanel2 = LineUtils.lxr(firstseg, [panel], True)
                            if hitspanel1 and hitspanel2:
                                #print "in panel"
                                newpstart = firstseg.ClosestPoint(porigin, False) #treat as infinite
                                newpend = firstseg.ClosestPoint(dpolyline.Last, False) #treat as infinite
                                newpoly = rg.Polyline([newpstart, newpend])
                                branch[i] = newpoly
                        else:
                            pass
                            #print "here not snake"
            if False:
            #if finaltree.BranchCount <= 1:
                for branch in finaltree.Branches:
                    respaced.extend(list(branch))
            else:
                parameters0 = []
                parameters1 = []
                offsets0 = []
                offsets1 = []
                offsets_left_branch = []
                offsets_right_branch = []
                
                for j in [0, 1]:
            #        try:
                    for poly in finaltree.Branch(j):
                        startp = poly.First
                        remap_ok, mid_uv = panelplane.RemapToPlaneSpace(startp)
                        par = mid_uv.Y
                        if j == 0:
                            parameters0.append(par)
                        else:
                            parameters1.append(par)
            #        except:
            #            pass
                
                parameters0.sort()
                parameters1.sort()
                
                #print parameters0, parameters1
                
                if pullstart:
                    new0, new1 = snap_parameters(parameters0, parameters1)
                else:
                    new0, new1 = parameters0, parameters1
                
                #print new0, new1
                
                workwidth = 1.0
                if sidesextra * 2 < panelwidth * 0.5:
                    workwidth = panelwidth - sidesextra * 2
                else:
                    workwidth = panelwidth
                
                panelzero = panelplane.Origin.Y
                allpars = new0 + new1
                minpar_ = min(allpars)
                maxpar_ = max(allpars)
                midpar_ = minpar_ * 0.5 + maxpar_ * 0.5
                pardomain_ = abs(maxpar_ - minpar_)
                paroffset = midpar_ - 0
                scalefactor = 1.0
                
                if pardomain_ > workwidth:
                    scalefactor = workwidth / pardomain_
                
                #scalefactor = 1.0
                
                for p0, n0 in zip(parameters0, new0):
                    offset0 = n0 - p0 - paroffset
                    off0 = p0 + offset0
                    scalef = off0 * (1 - scalefactor)
                    offset0 -= scalef
                    ovec0 = copy.deepcopy(planeY)
                    ovec0 *= offset0
                    offsets0.append(ovec0)
                
                for p1, n1 in zip(parameters1, new1):
                    offset1 = n1 - p1 - paroffset
                    off1 = p1 + offset1
                    scalef = off1 * (1 - scalefactor)
                    offset1 -= scalef
                    ovec1 = copy.deepcopy(planeY)
                    ovec1 *= offset1
                    offsets1.append(ovec1)
                
                #print offsets0, offsets1
                
                # build offsets per-branch, matching branch poly order
                left_polys = list(finaltree.Branch(0))
                right_polys = list(finaltree.Branch(1))
                used0 = [False] * len(parameters0)
                used1 = [False] * len(parameters1)
                tol_par = 1e-6
                
                porigin = panelplane.Origin
                
                run_else = False
                
                for poly in left_polys:
                    startp = poly.First
                    remap_ok, mid_uv = panelplane.RemapToPlaneSpace(startp)
                    par = mid_uv.Y
                    offset_vec = None
                    for k in range(len(parameters0)):
                        if not used0[k]:
                            if abs(parameters0[k] - par) <= tol_par:
                                offset_vec = offsets0[k]
                                used0[k] = True
                                break
                    offsets_left_branch.append(offset_vec)
                
                for poly in right_polys:
                    startp = poly.First
                    remap_ok, mid_uv = panelplane.RemapToPlaneSpace(startp)
                    par = mid_uv.Y
                    offset_vec = None
                    for k in range(len(parameters1)):
                        if not used1[k]:
                            if abs(parameters1[k] - par) <= tol_par:
                                offset_vec = offsets1[k]
                                used1[k] = True
                                break
                    offsets_right_branch.append(offset_vec)
                
                # original respaced (not strictly needed, but kept)
                for branch in finaltree.Branches:
                    respaced.extend(list(branch))
                
                # reorder to match readjustedpoly indexing
                left_set = set(left_indices)
                right_set = set(right_indices)
                
                respaced_ordered = []
                offsets_respaced = []
                left_i = 0
                right_i = 0
                
                for idx in range(len(readjustedpoly)):
                    if idx in left_set:
                        respaced_ordered.append(left_polys[left_i])
                        offsets_respaced.append(offsets_left_branch[left_i])
                        left_i += 1
                    elif idx in right_set:
                        respaced_ordered.append(right_polys[right_i])
                        offsets_respaced.append(offsets_right_branch[right_i])
                        right_i += 1
                    else:
                        respaced_ordered.append(readjustedpoly[idx])
                        offsets_respaced.append(None)
                
                respaced = respaced_ordered
                # offsets_respaced now has same indexing as respaced / readjustedpoly
            
            rerespaced = []
            
            trimdist = 1.0 #remove 1 inch
            
            for rspcd, ovec in zip(respaced, offsets_respaced):
                newpoly = copy.deepcopy(list(rspcd))
                trnsfrm = rg.Transform.Translation(ovec)
                for j in [0, 1]:
                    newpoly[j].Transform(trnsfrm)
                
                if cutstart and pullstart:
                    cutvec = rg.Vector3d(newpoly[0] - newpoly[1])
                    cutvec.Unitize()
                    cutvec *= -trimdist
                    trimsf = rg.Transform.Translation(cutvec)
                    newpoly[0].Transform(trimsf)
            
                newcrv = rg.PolylineCurve(newpoly)
                rerespaced.append(newcrv)
            
        #reconnected = rerespaced
        return rerespaced

# make the class docstring match the top-of-file docstring (single source of truth)
Panelconnection.__doc__ = __doc__

#guard, so it doesn't run on import, but will run in regular components
if __name__ == "__main__":
    ghenv.Component.Message = "v0.45 panelconnections classed"

    pc = Panelconnection()
    pc_results = pc.Run(LineUtils, panel, panelplane, polylines, conduitsizes, spacing,
                        removeshorts, pullstart, manhattanradius, devicemode, devicetolerance)

    reconnected = pc_results


