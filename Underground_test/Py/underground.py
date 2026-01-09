"""
GH Python (IronPython)
Description: Reconnect and re-route conduit polylines at a panel with optional Manhattan logic and device-aware tolerance.

Inputs:
    LineUtils           : LineUtils                 - helper class instance 
    panelsgeometry      : Tree[rg.Rectangle3d]      - panel outline in 3D, has to be tree 1 panel per branch, matching connections
    panelplane          : Tree[rg.Plane]            - panel plane used for projection and orientation, has to be tree 1 plane per branch, matching connections
    connections         : Tree[rg.Polyline]         - main input, list of lines from panel to end point
    conduitsize         : Tree[float]               - conduit size per polyline; list length must match polylines
    noflies             : List[rg.rg.Rectangle3d]   - list of nofly zones, flat for whole floor
    spacing             : float                     - target centre-to-centre distance between conduits
    iterations          : int                       - number of optimizational iteration, not less than 1, 3 is a good balance
    groupingdistance    : float                     - distance of undergroungg runs sticking together
    enforcebendradius   : bool                      - do a "freebend" only if it does fit in a preset distance, otherwise smaller ones will be formed as needed
    splitafter          : int                       - if panel has more than "splitafter" connections to it, it will get split evenly into 2 levels

Outputs:
    reconnectedtree : Tree[rg.Polyline] - tree of underground connection polylines [*;0] branch is the default layer, [*;1] is 2nd layer
    conduitsizestree: Tree[float]       - tree of conduitsizes with the same [*;0] and [*;1] branch structure to match 
"""

import Rhino.Geometry as rg
import Grasshopper as gh
import System
import itertools
import copy
import math
import sys
import os
import imp

class Underground(object):
    def Run(self, LineUtils, panelsgeometry, panels, connections, conduitsizes,
                  noflies, spacing = 1.0, iterations = 3, groupingdistance = 25.0, 
                  enforcebendradius = False, splitafter = 15):
        GLOBAL_TOL = 0.01
        ANG_EPS = 1e-6
        defaultpath = gh.Kernel.Data.GH_Path(0)
        unitX = rg.Vector3d(1, 0, 0)
        unitY = rg.Vector3d(0, 1, 0)
        unitZ = rg.Vector3d(0, 0, 1) 
        lineargap = 4.0 #4" between bends
        freebend = 300 #300" bend radius is "free"
        maxturns = 360 #including entrances which are already 2x 90
        #ghenv.Component.Message = "v0.25 underground merged" #has to be at the end here  
        roffset = 15
        
        # Name of the environment variable to read
        VAR_NAME = "DRAWER_PROJECT_ROOT"
        
        # Get project root from environment variable
        drawer_project = os.environ.get(VAR_NAME)
        
        # Validate existence
        if not drawer_project:
            raise ValueError(
                "Environment variable '{}' is not set. "
                "Please define it in your system environment.".format(VAR_NAME)
            )
        
        #panelconnections import
        local_path = "Gh\Panelconnections\Py\panelconnections.py"
        
        # Normalize and safely combine paths
        PanelConnectionsPath = os.path.join(drawer_project, local_path)
        
        #import library
        ModuleName = "panelconnections"
        if ModuleName in sys.modules:
            del sys.modules[ModuleName]
        
        pc_mod = imp.load_source(ModuleName, PanelConnectionsPath)
        pc_runner = pc_mod.Panelconnection()
        
        #print PanelConnectionsPath
        
        
        def _unit_xy(v):
            if v.Length > 0.0:
                v.Unitize()
            return v
        
        def _left_normal_xy(v):
            n = rg.Vector3d(-v.Y, v.X, 0.0)
            if n.Length > 0.0:
                n.Unitize()
            return n
        
        
        class PolyPoint(object):
            def __init__(self, x, y, z=0.0):
                self.pt = rg.Point3d(x, y, z)
        
            def move(self, vector):
                xform = rg.Transform.Translation(vector)
                self.pt.Transform(xform)
        
            @property
            def location(self):
                return self.pt
        
        class PolySegment(object):
            def __init__(self, start_point, end_point):
                self.start = start_point
                self.end = end_point
                self.lookupid = -1              # default lookup index
                self.lookup_geometry = None
                self.dir = rg.Vector3d(0.0, 0.0, 0.0)
                self.norm = rg.Vector3d(0.0, 0.0, 0.0)
                self.prev_dir = rg.Vector3d(0.0, 0.0, 0.0)
                self.prev_norm = rg.Vector3d(0.0, 0.0, 0.0)
                self.next_dir = rg.Vector3d(0.0, 0.0, 0.0)
                self.next_norm = rg.Vector3d(0.0, 0.0, 0.0)
                self.has_prev = False
                self.has_next = False
                self.bindex = -1 #default bundleindex
        
            @property
            def geometry(self):
                return rg.Line(self.start.pt, self.end.pt)
        
            def set_id(self, id):
                self.lookupid = id
        
            def set_lookup_geometry(self, line):
                self.lookup_geometry = rg.Line(line.From, line.To)
        
            def move(self, vector):
                v = rg.Vector3d(vector.X, vector.Y, vector.Z)
        
                if self.lookup_geometry:
                    dcur = rg.Vector3d(self.lookup_geometry.Direction.X, self.lookup_geometry.Direction.Y, 0.0)
                else:
                    dcur = rg.Vector3d(self.dir.X, self.dir.Y, 0.0)
        
                if dcur.Length <= GLOBAL_TOL:
                    dcur = self.geometry.Direction
                if dcur.Length <= GLOBAL_TOL:
                    return
        
                dcur.Unitize()
                ncur = rg.Vector3d(-dcur.Y, dcur.X, 0.0)
        
                d = v.X * ncur.X + v.Y * ncur.Y
        
                def _along(dir_vec):
                    if dir_vec.Length <= GLOBAL_TOL:
                        return rg.Vector3d(ncur.X * d, ncur.Y * d, v.Z)
                    dp = rg.Vector3d(dir_vec.X, dir_vec.Y, 0.0)
                    dp.Unitize()
                    denom = dp.X * ncur.X + dp.Y * ncur.Y
                    if abs(denom) < ANG_EPS:
                        return rg.Vector3d(ncur.X * d, ncur.Y * d, v.Z)
                    s = d / denom
                    return rg.Vector3d(dp.X * s, dp.Y * s, v.Z)
        
                if self.has_prev:
                    ds = _along(self.prev_dir)
                else:
                    ds = rg.Vector3d(ncur.X * d, ncur.Y * d, v.Z)
        
                if self.has_next:
                    de = _along(self.next_dir)
                else:
                    de = rg.Vector3d(ncur.X * d, ncur.Y * d, v.Z)
        
                self.start.move(ds)
                self.end.move(de)
        
        
        class Polyline(object):
            def __init__(self, rawpoints, ghpath = defaultpath, tradesize = 1.0):
                self.rawpoints = list(rawpoints)
                self.ghpath = ghpath #actual GH_Path 
                self.tradesize = tradesize
                self._build()
        
            def _build(self):
                unique = []
                for p in self.rawpoints:
                    if not unique or unique[-1].DistanceTo(p) > GLOBAL_TOL:
                        unique.append(rg.Point3d(p.X, p.Y, p.Z))
        
                filtered = []
                for i in range(len(unique)):
                    if i == 0 or i == len(unique) - 1:
                        filtered.append(unique[i])
                    else:
                        p0 = unique[i - 1]
                        p1 = unique[i]
                        p2 = unique[i + 1]
                        v1 = rg.Vector3d(p1.X - p0.X, p1.Y - p0.Y, p1.Z - p0.Z)
                        v2 = rg.Vector3d(p2.X - p1.X, p2.Y - p1.Y, p2.Z - p1.Z)
                        if rg.Vector3d.CrossProduct(v1, v2).Length > GLOBAL_TOL:
                            filtered.append(p1)
        
                self.points = [PolyPoint(p.X, p.Y, p.Z) for p in filtered]
                self.segments = []
        
                for i in range(len(self.points) - 1):
                    seg = PolySegment(self.points[i], self.points[i + 1])
                    self.segments.append(seg)
        
                for i in range(len(self.segments)):
                    seg = self.segments[i]
        
                    dir_cur = seg.geometry.Direction
                    _unit_xy(dir_cur)
                    seg.dir = rg.Vector3d(dir_cur.X, dir_cur.Y, 0.0)
                    seg.norm = _left_normal_xy(seg.dir)
        
                    if i > 0:
                        dir_prev = self.segments[i - 1].geometry.Direction
                        _unit_xy(dir_prev)
                        seg.prev_dir = rg.Vector3d(dir_prev.X, dir_prev.Y, 0.0)
                        seg.prev_norm = _left_normal_xy(seg.prev_dir)
                        seg.has_prev = True
                    else:
                        seg.has_prev = False
        
                    if i < len(self.segments) - 1:
                        dir_next = self.segments[i + 1].geometry.Direction
                        _unit_xy(dir_next)
                        seg.next_dir = rg.Vector3d(dir_next.X, dir_next.Y, 0.0)
                        seg.next_norm = _left_normal_xy(seg.next_dir)
                        seg.has_next = True
                    else:
                        seg.has_next = False
        
            def move_segment(self, index, vector):
                if index < 0 or index >= len(self.segments):
                    return
                self.segments[index].move(vector)
        
            def move_segments(self, indices, vectors):
                if len(indices) != len(vectors):
                    return
                for idx, vec in zip(indices, vectors):
                    self.move_segment(idx, vec)
        
            def assign_ids(self, candidates):
                for seg in self.segments:
                    best_idx = find_best_candidate(seg.geometry, candidates)
                    seg.set_id(best_idx)
                    seg.set_lookup_geometry(candidates[best_idx])
        
            @property
            def polyline_geometry(self):
                pts = [pt.location for pt in self.points]
                return rg.Polyline(pts)
        
        
        def find_best_candidate(checksegment, candidates):
            #direction prep helps with tolerance, grid is also prepped
            segment = rg.Line(*sorted([checksegment.From, checksegment.To], key=lambda point: (point.X, point.Y)))
            # Precompute angle buckets for candidates
            angle_buckets = {}
            for i, cand in enumerate(candidates):
                dir_vec = cand.Direction
                dir_vec.Unitize()
                key = round(abs(dir_vec * unitY), 2)
                #key = LineUtils.encode(dir_vec)
                if key not in angle_buckets:
                    angle_buckets[key] = []
                angle_buckets[key].append(i)
            
            #print angle_buckets.keys()
            
            seg_dir = segment.Direction
            seg_dir.Unitize()
            key = round(abs(seg_dir * unitY), 2)#LineUtils.encode(seg_dir, 2)
        
            bucket = angle_buckets.get(key, [])
        
            best_idx = -1
            best_dist = float('inf')
            
            mid = segment.PointAt(0.5)
            
            for i in bucket:
                dist = candidates[i].DistanceTo(mid, True)
                if dist < best_dist:
                    best_dist = dist
                    best_idx = i
        
            return best_idx
        
        manhattans = []
        polysc = []
        
        rawaxis = []
        
        for connpath in connections.Paths:
            connbranch = list(connections.Branch(connpath))
            
            try:
                sizebranch = list(conduitsizes.Branch(connpath))
                panelbranch = list(panels.Branch(connpath))
            except:
                print "branches mismatch"
                break
            
            panel = panelbranch[0]
            #need this tweak 
            panelY = panel.XAxis
            panelX = panel.YAxis
            
            for connection, tradesize in zip(connbranch, sizebranch):
                st = connection.From
                en = connection.To
                
                stl = rg.Line(st, panelY, 1.0)
                enl = rg.Line(en, panelX, 1.0)
                
                _, stpar, enpar = rg.Intersect.Intersection.LineLine(stl, enl, GLOBAL_TOL, False) #infinite
                isec = stl.PointAt(stpar)
                
                rawaxis.append(rg.Line(st, isec))
                rawaxis.append(rg.Line(isec, en))
                
                testpoly = rg.PolylineCurve([st, isec, en])
                manhattans.append(testpoly)
                
                poly = rg.Polyline([st, isec, en])
                pol = Polyline(poly, connpath, tradesize)
                polysc.append(pol)
        
        groupdist = groupingdistance#50.00
        
        mainaxis2 = LineUtils.grouper(rawaxis, groupdist, noflies)
        mainaxis = LineUtils.grouper(rawaxis, groupdist)
        minaxis_ = LineUtils.grouper(rawaxis, groupdist, keyed = True)
        
        grpkeys = minaxis_[-1]
        
        cnts = 0
        
        for key, value in grpkeys.items():
            #print value
            cnts += len(value)
        
        #print cnts
        
        moves = [mainaxis[i:i+2] for i in range(0, len(mainaxis), 2)]
        rawlines = []
        
        for poly, move in zip(polysc, moves):
            #print move
            vecs = []
            for m in move:
                _, vec, _, = m.DecomposeRigid(GLOBAL_TOL)
                vecs.append(vec)
            
            #print vecs
            
            poly.move_segments([0, 1], vecs)
            polygeo = poly.polyline_geometry
            
            polygeo.RemoveNearlyEqualSubsequentPoints(0.01)
            for i in range(polygeo.SegmentCount):
                rawlines.append(polygeo.SegmentAt(i))
        
        linelookup = LineUtils.process_lines_3d(rawlines, GLOBAL_TOL, False, False)
        
        for poly in polysc:
            poly.assign_ids(linelookup)
        
        
        #polysclass unpacking 
        polysclass = polysc
        
        polys = gh.DataTree[System.Object]()
        rawstarts = gh.DataTree[System.Object]()
        rawends = gh.DataTree[System.Object]()
        lookupids = gh.DataTree[System.Object]()
        
        
        for polysc in polysclass:
            pth = polysc.ghpath
            poly = polysc.polyline_geometry
            polys.Add(poly, pth)
            
            pts = polysc.rawpoints
            rawstarts.Add(pts[0], pth)
            rawends.Add(pts[-1], pth)
            
            ids = []
            for segment in polysc.segments:
                ids.append(segment.lookupid)
            
            lookupids.AddRange(ids, pth) 
        
        # END OF PREP
        
        sp = LineUtils.Spacing()
        
        #pushflag is resource intensive
        sp_results = sp.Run(polys, conduitsizes, optionalkeys = gh.DataTree[System.Int32]([0], defaultpath),
                            spacing = spacing, perpanel = False, perlevel = False, 
                            pulltogether = True, pushflag = False, pullstart = True)
        
        _, _, _, _, _, _, _, doublepolys, _ = sp_results
        
        #ITERATIVE PASS
        
        prepnoflies = [LineUtils.offset_rectangle(r, roffset) for r in noflies]
        prepnoflies_f = [LineUtils.offset_rectangle(r, roffset*0.5) for r in noflies]
        
        doublepolys = copy.deepcopy(doublepolys)
        polyclass = copy.deepcopy(polysclass)
        
        #ghpath gets wiped on deepcopy ? 
        for plc_, plc in zip(polysclass, polyclass):
            plc.ghpath = plc_.ghpath
            #print plc.ghpath
        
        def extremes(V):
            zero = rg.Vector3d(0.0, 0.0, 0.0)
            if V is None:
                V = []
        
            xs = []
            ys = []
            for v in V:
                if v.Y == 0.0 and v.Z == 0.0 and v.X != 0.0:
                    xs.append(v.X)
                elif v.X == 0.0 and v.Z == 0.0 and v.Y != 0.0:
                    ys.append(v.Y)
        
            max_pos_x = 0.0
            min_neg_x = 0.0
            for x in xs:
                if x > 0.0:
                    if x > max_pos_x:
                        max_pos_x = x
                elif x < 0.0:
                    if x < min_neg_x:
                        min_neg_x = x
        
            max_pos_y = 0.0
            min_neg_y = 0.0
            for y in ys:
                if y > 0.0:
                    if y > max_pos_y:
                        max_pos_y = y
                elif y < 0.0:
                    if y < min_neg_y:
                        min_neg_y = y
        
            has_x = len(xs) > 0
            has_y = len(ys) > 0
            if not has_x and not has_y:
                return [zero, zero]
        
            if has_x and not has_y:
                return [rg.Vector3d(min_neg_x, 0.0, 0.0), rg.Vector3d(max_pos_x, 0.0, 0.0)]
        
            if has_y and not has_x:
                return [rg.Vector3d(0.0, min_neg_y, 0.0), rg.Vector3d(0.0, max_pos_y, 0.0)]
        
            ax_amp = max(abs(min_neg_x), abs(max_pos_x))
            ay_amp = max(abs(min_neg_y), abs(max_pos_y))
            if ax_amp >= ay_amp:
                return [rg.Vector3d(min_neg_x, 0.0, 0.0), rg.Vector3d(max_pos_x, 0.0, 0.0)]
            else:
                return [rg.Vector3d(0.0, min_neg_y, 0.0), rg.Vector3d(0.0, max_pos_y, 0.0)]

        def sum_turn_angles_degrees(polyline, tol = GLOBAL_TOL):
            pts = None
            vectors = []
            total = 0.0
            i = 0
            n = 0
            v_prev = rg.Vector3d.Unset
            v_curr = rg.Vector3d.Unset
            dot = 0.0
            angle = 0.0
            deg_per_rad = 180.0 / math.pi
        
            if isinstance(polyline, rg.Polyline):
                n = polyline.Count
                pts = []
                for i in range(n):
                    pts.append(polyline[i])
            else:
                pts = []
                for p in polyline:
                    pts.append(p)
                n = len(pts)
        
            if n < 3:
                return 0.0
        
            for i in range(n - 1):
                v_curr = pts[i + 1] - pts[i]
                if not v_curr.IsValid:
                    continue
                if v_curr.Length <= tol:
                    continue
                if not v_curr.Unitize():
                    continue
                vectors.append(v_curr)
        
            if len(vectors) < 2:
                return 0.0
        
            for i in range(1, len(vectors)):
                v_prev = vectors[i - 1]
                v_curr = vectors[i]
        
                if not v_prev.IsValid:
                    continue
                if not v_curr.IsValid:
                    continue
        
                dot = rg.Vector3d.Multiply(v_prev, v_curr)
        
                if math.isnan(dot):
                    continue
        
                if dot > 1.0:
                    dot = 1.0
                if dot < -1.0:
                    dot = -1.0
        
                angle = math.acos(dot)
                total += angle * deg_per_rad
        
            return total


        def carve_freeturn_arc(polyline, freeturn):
            pts = []
            n = 0
            i = 0
            best_i = 0
            best_min_len = -1.0
            seg_len_a = 0.0
            seg_len_b = 0.0
            corner = None
            u = rg.Vector3d.Unset
            v = rg.Vector3d.Unset
            phi = 0.0
            t = 0.0
            d = 0.0
            a_pt = None
            b_pt = None
            bis = rg.Vector3d.Unset
            center = rg.Point3d.Unset
            mid_pt = None
            left_pts = []
            right_pts = []
            left_rest = None
            right_rest = None
            arc = None
        
            for p in polyline:
                pts.append(p)
            n = len(pts)
        
            for i in range(n - 2):
                seg_len_a = pts[i].DistanceTo(pts[i + 1])
                seg_len_b = pts[i + 1].DistanceTo(pts[i + 2])
                if seg_len_a < seg_len_b:
                    if seg_len_a > best_min_len:
                        best_min_len = seg_len_a
                        best_i = i
                else:
                    if seg_len_b > best_min_len:
                        best_min_len = seg_len_b
                        best_i = i
        
            if best_min_len < 0.0:
                return None
        
            seg_len_a = pts[best_i].DistanceTo(pts[best_i + 1])
            seg_len_b = pts[best_i + 1].DistanceTo(pts[best_i + 2])
            corner = pts[best_i + 1]
        
            if freeturn > best_min_len:
                if enforcebendradius:
                    return [polyline]
                    
                freeturn = 0.8 * best_min_len
        
            u = pts[best_i] - corner
            v = pts[best_i + 2] - corner
            u.Unitize()
            v.Unitize()
        
            phi = rg.Vector3d.VectorAngle(u, v)
            t = freeturn / math.tan(phi * 0.5)
            d = freeturn / math.sin(phi * 0.5)
        
            a_pt = rg.Point3d(corner.X + u.X * t, corner.Y + u.Y * t, corner.Z + u.Z * t)
            b_pt = rg.Point3d(corner.X + v.X * t, corner.Y + v.Y * t, corner.Z + v.Z * t)
        
            bis = u + v
            bis.Unitize()
            center = rg.Point3d(corner.X + bis.X * d, corner.Y + bis.Y * d, corner.Z + bis.Z * d)
            mid_pt = rg.Point3d(center.X - bis.X * freeturn, center.Y - bis.Y * freeturn, center.Z - bis.Z * freeturn)
        
            left_pts = []
            for i in range(0, best_i + 1):
                left_pts.append(pts[i])
            left_pts.append(a_pt)
        
            right_pts = []
            right_pts.append(b_pt)
            for i in range(best_i + 2, n):
                right_pts.append(pts[i])
        
            left_rest = rg.Polyline(left_pts)
            right_rest = rg.Polyline(right_pts)
            arc = rg.Arc(a_pt, mid_pt, b_pt)
        
            return [left_rest, arc, right_rest]
            
        def solver():
            pushdict = {}
            
            test1 = []
            testver = []
            testhor = []
            
            moves_ = []
            bkeys = []
            
            for poly, polysc, ukey, dpoly in zip(polyspaced, polyclass, range(len(polyspaced)), doublepolys):
                fpass = dpoly.firstpass
                spass = dpoly.finalpass
                
                bunkeys = []
                for fseg, sseg in zip(fpass.segments, spass.segments):
                    fsort = fseg.sort_idx
                    sgeo = sseg.geometry
                    bunkeys.append(fsort)
            
                bkeys.append(bunkeys)
                
                ids = []
                for segment in polysc.segments:
                    ids.append(segment.lookupid)
                
                currmoves = []
                
                polysegs = []
                for i in range(poly.SegmentCount):
                    polyseg = poly.SegmentAt(i)
                    orientation = LineUtils.orientation_of_line(polyseg)
            
                    pushvec = LineUtils.push_line(polyseg, orientation, prepnoflies)
                    summ = sum([pushvec.X, pushvec.Y, pushvec.Z])
            
                    flag = summ
                    currmoves.append(flag)
                    #currmoves.append(summ)
            
                    trnsfrm = rg.Transform.Translation(pushvec)
                    polyseg.Transform(trnsfrm)
                    test1.append(polyseg)
                    
                    if orientation == "vertical":
                        testver.append(polyseg)
                    if orientation == "horizontal":
                        testhor.append(polyseg)
            
                    currsort = bunkeys[i]
            
                    currid = ids[i] #could break, need to recheck
                    if currid in pushdict:
                        pushdict[currid].append([pushvec, currsort, flag, dpoly.segmentpairs[i]])
                    else:
                        pushdict[currid] = [[pushvec, currsort, flag, dpoly.segmentpairs[i]]]
                    
                    polysegs.append(polyseg)
                
                moves_.append(currmoves)
            
            maxdict = {}
            
            
            for k in pushdict:
                vectors = pushdict[k]
            
                sortedvectors = sorted(vectors, key = lambda x: x[1], reverse = True)
                bounds = extremes([v[0] for v in vectors])
                offsets = [sv[2] for sv in sortedvectors]
                
                eps = 0.01  # treat tiny magnitudes as zero 
                left, right = bounds
                zero = rg.Vector3d(0, 0, 0)
                
                moves = []
                right_sticky = False      
                zero_run_start = None     
                
                for i, v in enumerate(offsets):
                    if v > eps:  # positive
                        moves.append(right)
                        right_sticky = True
                        zero_run_start = None  # zeros before this are no longer consecutive to a future negative
                    elif v < -eps:  # negative
                        moves.append(left)
                        right_sticky = False
                        # backfill the immediately preceding 0-vectors with 'left'
                        if zero_run_start is not None:
                            for j in range(zero_run_start, i):
                                moves[j] = left
                            zero_run_start = None
                    else:  # zero (within +/- eps)
                        if right_sticky:
                            moves.append(right)  # keep pushing right through zeros
                        else:
                            moves.append(zero)   # true zero for now, may be back-filled if a negative arrives next
                            if zero_run_start is None:
                                zero_run_start = i
                
                for j in range(len(moves)):
                    movev = moves[j]
                    pseg = sortedvectors[j][-1]
                    pseg.final.move(movev)
                
                maxdict[k] = bounds
                
            a = []
            b = []
            testpush = []
            
            for poly, polysc, dpoly in zip(polyspaced, polyclass, doublepolys):
                fpass = dpoly.firstpass
                spass = dpoly.finalpass
                for fseg, sseg in zip(fpass.segments, spass.segments):
                    fsort = fseg.sort_idx
                    sgeo = sseg.geometry
                    a.append(fsort)
                    b.append(sgeo)
                    
                ids = []
                for segment in polysc.segments:
                    ids.append(segment.lookupid)
                
                polysegs = []
                for i in range(poly.SegmentCount):
                    polyseg = poly.SegmentAt(i)
                    orientation = LineUtils.orientation_of_line(polyseg)
                    v = LineUtils.push_line(polyseg, orientation, prepnoflies)
                    summ = sum([v.X, v.Y, v.Z])
                    
                    try:
                        currid = ids[i] #could break, need to recheck
                        
                        if summ > -0.01:
                            flag = 1
                        else:
                            flag = 0
                        
                        trnsfrm = rg.Transform.Translation(maxdict[currid][flag])
                        polyseg.Transform(trnsfrm)
                        
                        testpush.append(polyseg)
                    except:
                        pass
        
        def poly_hits_noflies(poly, rects):
            """
            Returns True if ANY segment of this polyline intersects ANY of the given rectangles.
            Uses the same LineUtils.lxr logic as everywhere else.
            """
            if not rects:
                return False
        
            for i in range(poly.SegmentCount):
                seg = poly.SegmentAt(i)
                if LineUtils.lxr(seg, rects):
                    return True
        
            return False
        
        def solver_onepass():
            v_lines = []
            v_refs = []
            h_lines = []
            h_refs = []
            v_static = []
            h_static = []
        
            for poly, polysc, dpoly in zip(polyspaced, polyclass, doublepolys):
                hits = LineUtils.poly_hits_rects(poly, prepnoflies)
                for i in range(poly.SegmentCount):
                    ln = poly.SegmentAt(i)
                    ori = LineUtils.orientation_of_line(ln)
        
                    if ori == LineUtils.Orientation.VERTICAL or ori == "vertical":
                        if hits:
                            v_lines.append(ln)
                            v_refs.append(dpoly.segmentpairs[i])
                        else:
                            v_static.append(ln)
        
                    elif ori == LineUtils.Orientation.HORIZONTAL or ori == "horizontal":
                        if hits:
                            h_lines.append(ln)
                            h_refs.append(dpoly.segmentpairs[i])
                        else:
                            h_static.append(ln)
        
            if not v_lines and not h_lines:
                return
        
            spacebuffer_value = 5.0
        
            # vertical: colliding lines are moved; non-colliding become keep-out rectangles
            v_rects = list(prepnoflies)
            for ln in v_static:
                y0 = ln.From.Y
                y1 = ln.To.Y
                if y1 < y0:
                    y0, y1 = y1, y0
                cx = (ln.From.X + ln.To.X) * 0.5
                xmin = cx - spacebuffer_value
                xmax = cx + spacebuffer_value
                rect = rg.Rectangle3d(rg.Plane.WorldXY, rg.Interval(xmin, xmax), rg.Interval(y0, y1))
                v_rects.append(rect)
        
            # horizontal: same idea
            h_rects = list(prepnoflies)
            for ln in h_static:
                x0 = ln.From.X
                x1 = ln.To.X
                if x1 < x0:
                    x0, x1 = x1, x0
                cy = (ln.From.Y + ln.To.Y) * 0.5
                ymin = cy - spacebuffer_value
                ymax = cy + spacebuffer_value
                rect = rg.Rectangle3d(rg.Plane.WorldXY, rg.Interval(x0, x1), rg.Interval(ymin, ymax))
                h_rects.append(rect)
        
            v_vecs = LineUtils.push_verticals_onepass(v_lines, v_rects, spacebuffer_value=spacebuffer_value, tol=GLOBAL_TOL)
            h_vecs = LineUtils.push_horizontals_onepass(h_lines, h_rects, spacebuffer_value=spacebuffer_value, tol=GLOBAL_TOL)
        
            for ds, vec in zip(v_refs, v_vecs):
                if vec.Length > GLOBAL_TOL:
                    ds.final.move(vec)
        
            for ds, vec in zip(h_refs, h_vecs):
                if vec.Length > GLOBAL_TOL:
                    ds.final.move(vec)
        
        def build_joined_curve(fpoly,  startcut):
            MAX_SPLITS = 50
            degrees = 0.0
            freeturn = 0.0
            segments = []
            i = 0
            j = 0
            total = 0.0
            changed = False
            item = None
            res = None
            left_poly = None
            right_poly = None
            arc = None
            join_input = []
            joined_list = None
            out = None
            best = None
            best_len = 0.0
            crv = None
            degrees = sum_turn_angles_degrees(fpoly) + 180.0
            freeturn = freebend + lineargap + startcut
            segments = [fpoly]
            if degrees > maxturns + GLOBAL_TOL * 2.0:
                for i in range(MAX_SPLITS):
                    total = 0.0
                    for j in range(len(segments)):
                        item = segments[j]
                        try:
                            total += sum_turn_angles_degrees(item)
                        except:
                            pass
                    total += 180.0
                    if total <= maxturns + GLOBAL_TOL * 2.0:
                        break
                    changed = False
                    for j in range(len(segments)):
                        item = segments[j]
                        res = carve_freeturn_arc(item, freeturn)
                        if res is not None:
                            del segments[j]
                            if len(res) > 1:
                                left_poly = res[0]
                                arc = res[1]
                                right_poly = res[2]
                                segments.insert(j, right_poly)
                                segments.insert(j, arc)
                                segments.insert(j, left_poly)
                            else:
                                segments.insert(j, res[0])
                            changed = True
                            break
                    if not changed:
                        break
            join_input = []
            for j in range(len(segments)):
                item = segments[j]
                try:
                    crv = item.ToPolylineCurve()
                except:
                    crv = rg.ArcCurve(item)
                join_input.append(crv)
            joined_list = rg.Curve.JoinCurves(join_input, GLOBAL_TOL)
            if joined_list is None:
                return None
            if len(joined_list) == 0:
                return None
            if len(joined_list) == 1:
                return joined_list[0]
            best = joined_list[0]
            best_len = best.GetLength()
            for j in range(1, len(joined_list)):
                crv = joined_list[j]
                if crv.GetLength() > best_len:
                    best = crv
                    best_len = crv.GetLength()
            print "curve got trimmed"
            return best
        
        polyspaced = [dpoly.finalpass.polyline_geometry for dpoly in  doublepolys]
        
        for iteration in range(iterations):
            solver_onepass()
            #reassign new geometry
            polyspaced = [dpoly.finalpass.polyline_geometry for dpoly in  doublepolys]
        
        pushed = []
        testsegments = []
        testsegments_a = []
        
        pushedtree = gh.DataTree[System.Object]()
        
        a = []
        
        for dpoly, cpoly in zip(doublepolys, polyclass):
            basegeo = list(dpoly.finalpass.polyline_geometry.GetEnumerator())
            #print basegeo
            
            newpolypts = copy.deepcopy(basegeo)
            rawpoints = copy.deepcopy(cpoly.rawpoints)
            conduitsize = copy.deepcopy(cpoly.tradesize)
        
            od_size = LineUtils.ConduitLookup.get_specs(conduitsize)["od"]
            linearstub = LineUtils.ConduitLookup.get_specs(conduitsize)['linear_section']
            bendradius = LineUtils.ConduitLookup.get_specs(conduitsize)['min_bend']
            
            startcut = LineUtils._compute_cut(bendradius, linearstub, 90)
            
            #to be safe calculated at 2x 90 degree turns + the linear section between
            #checklength = 0#experiment at 0
            checklength = lineargap + startcut*2 
            #for testing
            #checklength *= 0.5
            #print checklength
            
            oglast = rawpoints[-1]
            
            #if the shift from og position is larger than minimum conduit length than
            #add extra segment
            
            if oglast.DistanceTo(basegeo[-1]) >= checklength + GLOBAL_TOL:
                newpolypts.append(copy.deepcopy(oglast))
                testsegment = rg.Line(basegeo[-1], oglast)
        
                orientation = LineUtils.orientation_of_line(testsegment)
                pushvec = LineUtils.push_line(testsegment, orientation, prepnoflies_f)
                trnsfrm = rg.Transform.Translation(pushvec)
        
                lkp = [-2, -1]
                for k in lkp:
                    newpolypts[k].Transform(trnsfrm)
                
                #if shift of the last segment is larger than minimum conduit length
                #add 1 more segment
                
                if pushvec.Length >= checklength + GLOBAL_TOL:
                    newpolypts.append(oglast)
                else:
                    pass
                
        
            fpoly = rg.Polyline(newpolypts)
            fpoly.CollapseShortSegments(GLOBAL_TOL)
            fpoly.MergeColinearSegments(GLOBAL_TOL, False)
            
            joined = [build_joined_curve(fpoly,  startcut)]   
            
            if joined is not None and len(joined) > 0:
                pushed.append(joined[0])
                pushedtree.Add(joined[0], cpoly.ghpath)
            else:
                for k in range(len(join_input)):
                    pushed.append(join_input[k])
                    pushedtree.Add(join_input[k], cpoly.ghpath)
        
        #def run_panelconnections(path, LineUtils, panel, panelplane, polylines, 
        #                         conduitsizes, spacing, removeshorts, pullstart, 
        #                         manhattanradius, devicemode, devicetolerance):
        
        def split_if_longer(lst, n):
            if len(lst) <= n:
                return [lst]
            mid = (len(lst) + 1) // 2  # first half gets the extra if odd
            return [lst[:mid], lst[mid:]]
        
        reconnectedtree = gh.DataTree[System.Object]()
        conduitsizestree = gh.DataTree[System.Object]()
        
        maxperpanel = splitafter#15 #split into 2 layers if otherwise
        
        for path in pushedtree.Paths:
            _panelplane = list(panels.Branch(path))[0]
            _panel = list(panelsgeometry.Branch(path))[0]
            _polylines = []
            for ptpoly in list(pushedtree.Branch(path)):
                _poly = ptpoly.ToPolyline()
                if _poly:
                    _polylines.append(_poly)
                
            _conduitsizes = list(conduitsizes.Branch(path))
            
            polylists = split_if_longer(_polylines, maxperpanel)
            sizelists = split_if_longer(_conduitsizes, maxperpanel)
            
            for j in range(len(polylists)):
                _polylinesj = polylists[j]
                _conduitsizesj = sizelists[j]
                
                #large manhattanradius
                reconnected = pc_runner.Run(LineUtils, _panel, _panelplane, _polylinesj,
                                            _conduitsizesj, spacing, False, True, 500.0, False, 0.0)
                                                  
                jpath = gh.Kernel.Data.GH_Path(*list(path.Indices) + [j])
                
                conduitsizestree.AddRange(_conduitsizesj, jpath)
                
                #reconnectedtree.AddRange(reconnected, jpath)
                for rcpoly, rcsize in zip(reconnected, _conduitsizesj):
                    od_size = LineUtils.ConduitLookup.get_specs(rcsize)["od"]
                    linearstub = LineUtils.ConduitLookup.get_specs(rcsize)['linear_section']
                    bendradius = LineUtils.ConduitLookup.get_specs(rcsize)['min_bend']
                    
                    startcut = LineUtils._compute_cut(bendradius, linearstub, 90)
                    
                    try:
                        _rcpoly = rcpoly.ToPolyline()
                    except:
                        _rcpoly = rcpoly
                    
                    if _rcpoly:
                        bendchecked = build_joined_curve(_rcpoly, startcut)
                        reconnectedtree.Add(bendchecked, jpath)
                    else:
                        reconnectedtree.Add(rcpoly, jpath)
        
        #has to be after calling panelconnections
        #ghenv.Component.Message = "v0.25 underground merged"
        
        return (reconnectedtree, conduitsizestree)

# make the class docstring match the top-of-file docstring (single source of truth)
Underground.__doc__ = __doc__

#guard, so it doesn't run on import, but will run in regular components
if __name__ == "__main__":
    ghenv.Component.Message = "v0.26 underground classed"

    ug = Underground()
    ug_results = ug.Run(LineUtils, panelsgeometry, panels, connections, conduitsizes,
                        noflies, spacing, iterations, groupingdistance, enforcebendradius, splitafter)
    reconnectedtree, conduitsizestree = ug_results
