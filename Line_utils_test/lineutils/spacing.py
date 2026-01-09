import Rhino.Geometry as rg
import Grasshopper as gh
import System
import math
import itertools
import copy
import random
from collections import defaultdict

GLOBAL_TOL = 0.01
ANG_EPS = 1e-6
defaultpath = gh.Kernel.Data.GH_Path(0)
unitX = rg.Vector3d(1, 0, 0)
unitY = rg.Vector3d(0, 1, 0)
unitZ = rg.Vector3d(0, 0, 1)

LineUtils = None

class Spacing(object):
    """
    spacing version 0.87
    
    This module implements a two-pass “spacing” solver for polylines. It takes in a tree of input polylines, 
    converts them into segments, maps each segment onto a global lookup of axis (axis are created from all the baselines merged together whenever they touch), 
    computes turn directions and sort-orders, and finally repositions each segment so that bundles of pipes are evenly spaced (either per-panel or mixed together).
    
    --------------------
    - **Segmentization**  
      - Break each raw polyline into it's segments
      - Wrap each consecutive point pair in a `PolySegment`, tracking path and polyline indices
      - PolySegment class is usefull for storing all data about it and having the ability to move it
      as a part of polyline, similar to Offset Curve Loose
    - **Lookup & Identification**  
      - Build a global “lookup” of unique line geometries, this is used for axis determination 
      - For each segment, find its best matching lookup line (by bucketed angle + midpoint distance (midpoint distance worked the most reliably, so far problemless))  
    - **Turn & Sort Properties**  
      - In each `Polyline`, determine “previous”, “self” and “next” turn direction per segment (used to assign scores)
      - Compute per-segment sort chains (`sortchain`, `sortchainraw`) and group-indices based on turn/quadrant,
      sort chain holds information abotu all next segments in that polyline
    - **Score calculation logic**
      - Every segment is assigned a score based on :
          its panels id weight, panels are sorted based on left straight right turns and this is the heaviest influencer 
          its turns direction weight, left -> straight -> right in strength
          its turns parameter, parameter is flipped for right turns (so that both for left and right smaller values meaning earlier turns are position outside)
          finalweight = turnparameter + turndirection + panelid
    - **Offset Computation**  
      - Group segments by lookup ID and, within each group, by direction match  
      - Compute raw offsets (centered around zero) or bundle offsets (averaging subgroup positions)  
      - Move each segment along a perpendicular vector scaled by its offset  
    - **Double-Pass Refinement**  
      - First pass is mainly used to define bundle centers, as if segments go in opposite direction in a lookup axis, scoring is tricky
      - Second pass deals with bundles all in sam edirection, so scoring is reliable 
      (all lines wont be in same direction only in extreme corner cases, which could result in few extra overlaps, but the issue would be minuscule)
      - Produce paired “first” & “final” polylines and align them into bundle clusters (for ease of use, to be able to reference both first and final passes data) 
    - **Final Output**  
      - Reassemble moved polylines back into a `Grasshopper.DataTree` for downstream use  , keeping empty branches if present
    
    Public Classes
    --------------
    ### PolyPoint  
    Lightweight wrapper around `rg.Point3d` with a `.move(vector)` helper.
    
    ### PolySegment  
    Encapsulates one line segment between two `PolyPoint`s.  
    - Properties:  
      - `.geometry` -> `rg.Line`  
      - `.startpar` / `.endpar` -> nearest parameter on lookup axis line (to determine who turns first)
      - `.quadrant` -> compass quadrant of segment  
      - `.dirmatch` -> whether segment aligns with its lookup axis orientation  
      - `.sort_idx` -> computed sort key for ordering  
    
    ### Polyline  
    Builds a chain of `PolyPoint`s and `PolySegment`s from raw points.  
    - `_build()`  
      - Filters collinear points, instantiates segments  
    - `assign_ids(...)` / `assign_ids_raw(...)`  
    - `finalize_segments()`  
      - Computes turn directions, chains (`nextturnchain`, `scorechain`, `endchain`), and sort-chains  
    - Offsets:  
      - `move_segment`, `move_segments`  
      - `compute_dirflags`  
    - Properties:  
      - `.polyline_geometry` -> Rhino `Polyline`  
      - `.dirflagged` -> whether any segment failed alignment  
    
    ### DoubleSegment & DoublePoly  
    Pair up corresponding first- and final-pass segments to compute domain intervals, ordered geometry, and to support cluster re-alignment.
    """

    def Run(self, polylines, conduitsize, optionalkeys = gh.DataTree[System.Int32]([0], defaultpath),
            spacing = 1.0, perpanel = False, perlevel = False, pulltogether = True, 
            pushflag = True, pullstart = True, bimmode = False, prefilter = False,
            speedmode = False):
        """
        returns: rawlinelookup, linelookup, rebuiltree, polys, polys2, finaltree, treeflags, doublepolys, Boundaryobjects
        pushflag effects compute the most, for iterating quickly it's best to disable it
        and keep just for final code
        """
        
        #pushflag = True #push colliding bundles apart
        bothpasses = True #for debugging, if False only 1 pass is run, more intersections
        debugglobals = True #debug outputs
        
        # shorter sortchains in speedmode *slight accuracy reduction
        sortchain_span = 10 if speedmode else 50
        
        if speedmode:
            # Fast mode: skip most expensive global steps
            pushflag = False
            prefilter = False
        
        if prefilter:
            polylines = LineUtils.prefilter_polyline_tree(polylines)

        
        #nonorth move helpers 
        
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
            def __init__(self, start_point, end_point, polypath = None, 
                        polypathidx = None, polyidx = None, tradesize = 0.0,
                        outerdiameter = 0.0, optionalkey = 0.0, bimmode = False):
                
                self.start = start_point
                self.end = end_point
                self.polypath = polypath        # GH_path of parent polyline
                self.polypathidx = polypathidx  # index of GH_path among all parent polylines paths
                self.polyidx = polyidx          # index of parent polyline among all parent polylines
                #self.pathsortidx = [1000, 1000, 1000, 1000] #in group calculated sort idx %left %straight %right numelements
                self.pathsortidx = [0, 0, 0, 0] # in group calculated sort idx %left %straight %right numelements
                self.pathsortidx_ = 0           # idx sorted by pathsortidx
                self.optionalkey = optionalkey  # optional key to influence positioning
                self.bimmode = bimmode          # solve sorting inside bundle itself only
                self.lookupid = -1              # default lookup index
                self.lookupidflip = -1
                self.lookupidraw = -1
                self.lookup_geometry = None      # actual flipped lookup line geometry
                self.lookup_geometry_flip = None
                self.lookup_geometry_raw = None
                self.prevturn = "Unset"
                self.nextturn = "Straight"
                self.selfturn = "Straight"
                self.startchain = []             # chain of start parameters
                self.endchain = []               # chain of end parameters
                self.nextturnchain = []
                self.prevturnchain = []
                self.scorechain = []
                self.sortchain = [] #mainattempt
                self.sortchainflip = []
                self.sortchainraw = []
                self.polydirflagged = False
                self.bundleindex = -1 #default
                self.bim_dirsign = 1
                self.bim_panelrank = 0
                self.bim_bundlekey = None
                self.tradesize = tradesize
                self.outerdiameter = outerdiameter
                self.dir = rg.Vector3d(0.0, 0.0, 0.0) #additions for nonorth
                self.norm = rg.Vector3d(0.0, 0.0, 0.0)
                self.prev_dir = rg.Vector3d(0.0, 0.0, 0.0)
                self.prev_norm = rg.Vector3d(0.0, 0.0, 0.0)
                self.next_dir = rg.Vector3d(0.0, 0.0, 0.0)
                self.next_norm = rg.Vector3d(0.0, 0.0, 0.0)
                self.has_prev = False
                self.has_next = False
        
            @property
            def geometry(self):
                return rg.Line(self.start.pt, self.end.pt)
        
            @property
            def startpar(self):
                if not self.lookup_geometry:
                    return -1.0
                # raw parameter on infinite line
                return round(self.lookup_geometry.ClosestParameter(self.geometry.From), 3)
        
            @property
            def endpar(self):
                if not self.lookup_geometry:
                    return -1.0
                
                return round(self.lookup_geometry.ClosestParameter(self.geometry.To), 3)
        
            @property
            def endparraw(self):
                if not self.lookup_geometry_raw:
                    return -1.0
                # raw parameter on infinite line
                return round(self.lookup_geometry_raw.ClosestParameter(self.geometry.To), 3)
        
        
            #new for nonorth
            def move(self, vector):
                # always start from the input vector
                v = rg.Vector3d(vector.X, vector.Y, vector.Z)
        
                # 1) use the LOOKUP axis so every segment in the bundle shares the same frame
                if self.lookup_geometry:
                    dcur = rg.Vector3d(self.lookup_geometry.Direction.X,
                                       self.lookup_geometry.Direction.Y, 0.0)
                else:
                    dcur = rg.Vector3d(self.dir.X, self.dir.Y, 0.0)
                if dcur.Length <= GLOBAL_TOL:
                    dcur = self.geometry.Direction
                if dcur.Length <= GLOBAL_TOL:
                    return
                dcur.Unitize()
                ncur = rg.Vector3d(-dcur.Y, dcur.X, 0.0)  # shared unit normal for the bundle
        
                # how far we want to move in the normal direction (same for all lines in the bundle)
                d = v.X * ncur.X + v.Y * ncur.Y
        
                # helper: move an endpoint along a given direction so its normal shift equals d
                def _along(dir_vec):
                    if dir_vec.Length <= GLOBAL_TOL:
                        # no reliable neighbor: just translate by the shared normal
                        return rg.Vector3d(ncur.X * d, ncur.Y * d, v.Z)
                    dp = rg.Vector3d(dir_vec.X, dir_vec.Y, 0.0); dp.Unitize()
                    denom = dp.X * ncur.X + dp.Y * ncur.Y    # == cos(angle(dp, ncur))
                    if abs(denom) < ANG_EPS:
                        # almost parallel to the axis -> treat as pure normal translation
                        return rg.Vector3d(ncur.X * d, ncur.Y * d, v.Z)
                    s = d / denom
                    return rg.Vector3d(dp.X * s, dp.Y * s, v.Z)
        
                ds = _along(self.prev_dir) if self.has_prev else rg.Vector3d(ncur.X * d, ncur.Y * d, v.Z)
                de = _along(self.next_dir) if self.has_next else rg.Vector3d(ncur.X * d, ncur.Y * d, v.Z)
        
                self.start.move(ds)
                self.end.move(de)
        
        
            def set_id(self, id):
                self.lookupid = id
        
            def set_lookup_geometry(self, line):
                # store a copy of the flipped lookup line
                self.lookup_geometry = rg.Line(line.From, line.To)
        
            def set_id_raw(self, id):
                self.lookupidraw = id
        
            def set_lookup_geometry_raw(self, line):
                # store a copy of the flipped lookup line
                self.lookup_geometry_raw = rg.Line(line.From, line.To)
        
            def set_polydirflag(self, flag):
                self.polydirflagged = flag
            
            def set_pathsortidx(self, psort):
                self.pathsortidx = psort
        
            def set_pathsortidx_(self, psort_):
                self.pathsortidx_ = psort_
        
            def set_optionalkey(self, o_key):
                self.optionalkey = o_key

            def set_bimmode(self, bim):
                self.bimmode = bim

            """
            unset means straight
            left -> 0
            unset -> 1
            right -> 2
            """
            @property
            def groupindexnext(self):
                if self.nextturn == "Left":
                    return 1#0
                elif self.nextturn == "Straight":
                    return 3#1
                elif self.nextturn == "Right":
                    return 5#2
            
            @property
            def groupindexnextflip(self):
                if self.nextturn == "Left":
                    return 6#6#2
                elif self.nextturn == "Straight":
                    return 3#3#1
                elif self.nextturn == "Right":
                    return 0#0#0
        
            @property
            def quadrant(self): 
                v = self.geometry.Direction
                if abs(v.Y) >= abs(v.X):
                    if v.Y > 0:
                        direction = "Up quadrant"
                    else:
                        direction = "Down quadrant"
                else:
                    if v.X > 0:
                        direction = "Right quadrant"
                    else:
                        direction = "Left quadrant"
                return direction
                
            @property
            def dirmatch(self):
                selfdir = self.geometry.Direction
                selfdir.Unitize()
                lkpdir = self.lookup_geometry.Direction
                lkpdir.Unitize()
                dot = selfdir * lkpdir
                
                return dot > 0.5
        
            @property
            def sort_idx(self):
                if perpanel:
                    pathoffset = self.pathsortidx_ * 10
                else:
                    pathoffset = 0

                gi = self.groupindexnext
                gi_flip = self.groupindexnextflip

                # BIMMODE: make the parameter "travel-direction stable"
                # so reversed segments don't invert the ordering logic.
                if self.bimmode:
                    par = self.endpar

                    # If segment runs opposite axis orientation, invert parameter
                    if not self.dirmatch:
                        par = 1 - par

                    # Keep  "Right turn parameter flip" behaviour
                    if self.nextturn == "Right":
                        par = 1 - par

                    # If travelling opposite the axis, flip Left/Right weighting
                    gi_use = gi if self.dirmatch else gi_flip

                    return par + gi_use + pathoffset + self.optionalkey

                # Non-bimmode: keep legacy behaviour (close to original)
                calcpar = 0.0
                if gi == 5 or gi_flip == 0:
                    calcpar = 1 - self.endpar
                else:
                    calcpar = self.endpar

                finpar = calcpar + gi
                return finpar + pathoffset + self.optionalkey
        
            @property
            def sort_idx_raw(self):
                gi = self.groupindexnext
                calcpar = 0.0
                
                if gi == 2:
                    calcpar = 1 - self.endparraw
                else:
                    calcpar = self.endparraw
                
                finpar = calcpar + gi 
                
                return finpar
        
        
        class Polyline(object):
            def __init__(self, rawpoints, ghpath=defaultpath, ghidx = -1, 
                        absidx = -1, pathidx = -1, tradesize = 0.0, 
                        outerdiameter = 0.0, optionalkey = 0.0, bimmode = False):
                
                self.rawpoints = list(rawpoints)
                self.ghpath = ghpath #actual GH_Path 
                self.ghidx = ghidx   #index of polyline inside path
                self.absidx = absidx #index of polyline among all polylines
                self.pathidx = pathidx#index of GH_Path among all paths
                self.tradesize = tradesize
                self.outerdiameter = outerdiameter
                self.optionalkey = optionalkey
                self.bimmode = bimmode
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
                        p0, p1, p2 = unique[i-1], unique[i], unique[i+1]
                        v1 = rg.Vector3d(p1.X-p0.X, p1.Y-p0.Y, p1.Z-p0.Z)
                        v2 = rg.Vector3d(p2.X-p1.X, p2.Y-p1.Y, p2.Z-p1.Z)
                        if rg.Vector3d.CrossProduct(v1, v2).Length > GLOBAL_TOL:
                            filtered.append(p1)
        
                self.points = [PolyPoint(p.X, p.Y, p.Z) for p in filtered]
                self.segments = []
                
                #for i in range(len(self.points) - 1):
                #    self.segments.append(PolySegment(self.points[i], self.points[i+1], self.ghpath, self.pathidx, self.absidx, self.tradesize, self.outerdiameter, self.optionalkey))
                #rework for nonorth
                for i in range(len(self.points) - 1):
                    seg = PolySegment(self.points[i], self.points[i+1], self.ghpath,
                                      self.pathidx, self.absidx, self.tradesize, 
                                      self.outerdiameter, self.optionalkey, self.bimmode)
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
                    print "IndexError: Segment index out of range."
                    return
                self.segments[index].move(vector)
        
            def move_segments(self, indices, vectors):
                if len(indices) != len(vectors):
                    print "ValueError: indices and vectors must be the same length."
                    return
                for idx, vec in zip(indices, vectors):
                    self.move_segment(idx, vec)
        
            def assign_ids(self, candidates):
                for seg in self.segments:
                    best_idx = find_best_candidate(seg.geometry, candidates)
                    seg.set_id(best_idx)
                    seg.set_lookup_geometry(candidates[best_idx])
        
            def assign_ids_raw(self, candidates):
                for seg in self.segments:
                    best_idx = find_best_candidate(seg.geometry, candidates)
                    seg.set_id_raw(best_idx)
                    seg.set_lookup_geometry_raw(candidates[best_idx])
        
            def finalize_segments(self):
                count = len(self.segments)
                for i, seg in enumerate(self.segments):
                    # previous turn
                    if i > 0:
                        prev_dir = self.segments[i-1].geometry.Direction
                        prev_dir.Unitize()
                        cur_dir = seg.geometry.Direction
                        cur_dir.Unitize()
                        cross = rg.Vector3d.CrossProduct(prev_dir, cur_dir)
                        if cross.Z > 0:
                            seg.prevturn = "Left"
                            seg.selfturn = "Left"
                        else:
                            seg.prevturn = "Right"
                            seg.selfturn = "Right"
        
                    # next turn
                    if i < count - 1:
                        next_dir = self.segments[i+1].geometry.Direction
                        next_dir.Unitize()
                        cur_dir = seg.geometry.Direction
                        cur_dir.Unitize()
                        cross = rg.Vector3d.CrossProduct(cur_dir, next_dir)
                        if cross.Z > 0:
                            seg.nextturn = "Left"
                        else:
                            seg.nextturn = "Right"
                
                verflag = False
                cur_dir = seg.geometry.Direction
                cur_dir.Unitize()
                
                if cur_dir * unitY > 0.5:
                    verflag = True
                
                for i, seg in enumerate(self.segments):
                    seg.nextturnchain = []
                    for k in range(2): # this segment + next 1
                        idx = i + k # -1 #-1 experimental edit
                        if idx < count:
                            seg.nextturnchain.append(self.segments[idx].nextturn)
                        else:
                            seg.nextturnchain.append("Unset")
                
                for i, seg in enumerate(self.segments):
                    seg.scorechain = []
                    for j in range(5):  # this segment + next 4
                        idx = i + j
                        
                        if idx < count:
                            #trn = self.segments[idx].nextturn
                            trn = self.segments[idx].selfturn
                            glen = round(self.segments[idx].geometry.Length, 3)
                            if trn == "Left":
                                seg.scorechain.append(-glen)
                                #seg.scorechain.append(glen)
                            else:
                                seg.scorechain.append(glen)
                        else:
                            seg.scorechain.append(999999)
        
                # build startchain and endchain for each segment
                for i, seg in enumerate(self.segments):
                    seg.endchain = []
                    for j in range(5):  # this segment + next 4
                        idx = i + j
                        
                        if idx < count:
                            ioffset = self.segments[idx].groupindexnext
                            idxpar = self.segments[idx].endpar
                            bracketpar = -1
                            if ioffset in [0, 1, 2]:
                                bracketpar = 0
                            if ioffset == 3:
                                bracketpar = 1
                            if ioffset in [4, 5, 6]:
                                bracketpar = 2
                            seg.endchain.append(bracketpar + idxpar)
                        else:
                            seg.endchain.append(0.0)
        
                for seg in self.segments:
                    if self.dirflagged:
                        pass
                        seg.set_polydirflag(True)
                        #seg.polydirflagged = True
        
                for i, seg in enumerate(self.segments):
                    seg.sortchain = []
                    seg.sortchainflip = []
                    seg.sortchainraw = []
                    for j in range(sortchain_span):  #5 for debugging, normally could be more
                        idx = i + j
                        
                        if idx < count:
                            soridx = self.segments[idx].sort_idx
                            seg.sortchain.append(soridx)
                        else:
                            seg.sortchain.append(100)
                            
                    seg.sortchain.append(self.absidx) #add a unique consistent index as the last resort for consistent sorting for identical polys
        
            def compute_dirflags(self):
                for seg in self.segments:
                    if self.dirflagged:
                        pass
                        seg.set_polydirflag(True)
                        #seg.polydirflagged = True
        
            @property
            def polyline_geometry(self):
                pts = [pt.location for pt in self.points]
                return rg.Polyline(pts)
            
            @property
            def dirflagged(self):
                for sgm in self.segments:
                    if sgm.dirmatch == False:
                        return True
                return False
        
        safeext = spacing*100
        
        class DoubleSegment(object):
            def __init__(self, first, final):
                self.first = first 
                self.final = final
                self.bundleidx = -1
                self.outlineidx = -1
                self.boundlegroup = -1 #for boundary pushing grouping
                self.maxslotdiameter = first.outerdiameter
        
            def set_bundleidx(self, idx):
                self.bundleidx = idx
        
            def set_outlineidx(self, idx):
                self.outlineidx = idx
            
            def set_maxslotdiameter(self, diameter):
                self.maxslotdiameter = diameter
        
            def set_boundlegroup(self, idx):
                self.boundlegroup = idx
        
            @property
            def id(self):
                return self.first.lookupid
            
            @property
            def p1(self):
                #return self.first.startpar
                return self.lookup.ClosestParameter(self.geometry.From)
                #return self.first.lookup_geometry.ClosestParameter(self.geometry.From)
            
            @property
            def p2(self):
                #return self.first.endpar
                return self.lookup.ClosestParameter(self.geometry.To)
                #return self.first.lookup_geometry.ClosestParameter(self.geometry.To)
            
            @property
            def domain(self):
                return rg.Interval(*sorted([self.p1, self.p2]))
            
            @property
            def geometry(self):
                geo = self.final.geometry
                pts = sorted([geo.From, geo.To], key = lambda p: (p.X, p.Y))
                return rg.Line(*pts)
            
            @property
            def lookup(self):
                lkpg = self.first.lookup_geometry
                lkpline = rg.Line(lkpg.From, lkpg.To)
                #lkpline.Extend(safeext, safeext) #need to check if needed
                return lkpline
            
            
        class DoublePoly(object):
            def __init__(self, polyfirstpass, polyfinalpass):
                self.firstpass = polyfirstpass
                self.finalpass = polyfinalpass
                # build and cache your DoubleSegment objects just once
                pairs = zip(self.firstpass.segments, self.finalpass.segments)
                self._segmentpairs = [DoubleSegment(a, b) for a, b in pairs]
        
            @property
            def segmentpairs(self):
                return self._segmentpairs
        
        
        class Boundary(object):
            def __init__(self, geometry, bundleidx, outlineidx, encoded, axis, z):
                self.geometry = geometry
                self.bundleidx = bundleidx
                self.outlineidx = outlineidx
                self.encoded = encoded
                self.axis = axis
                self.movevector = rg.Vector3d(0, 0, 0)
                self.z = z
                self.boundlegroup = -1 #for boundary pushing grouping
        
            def set_movevector(self, vec):
                self.movevector = vec
        
            def set_boundlegroup(self, idx):
                self.boundlegroup = idx
        
        candidate_cache = {'candidates': None, 'buckets': None}
        
        
        def find_best_candidate(checksegment, candidates):
            # direction prep helps with tolerance, grid is also prepped
            segment = rg.Line(*sorted([checksegment.From, checksegment.To],
                                      key=lambda point: (point.X, point.Y)))
            
            # segment direction key (unchanged logic)
            seg_dir = segment.Direction
            seg_dir.Unitize()
            seg_key = round(abs(seg_dir * unitY), 2)
        
            # build / reuse angle buckets for this candidate list
            if speedmode:
                cached_candidates = candidate_cache['candidates']
                angle_buckets = candidate_cache['buckets']
                if cached_candidates is not candidates or angle_buckets is None:
                    angle_buckets = {}
                    for i, cand in enumerate(candidates):
                        dir_vec = cand.Direction
                        dir_vec.Unitize()
                        key = round(abs(dir_vec * unitY), 2)
                        if key not in angle_buckets:
                            angle_buckets[key] = []
                        angle_buckets[key].append(i)
                    candidate_cache['candidates'] = candidates
                    candidate_cache['buckets'] = angle_buckets
            else:
                # original per-call behaviour (no caching)
                angle_buckets = {}
                for i, cand in enumerate(candidates):
                    dir_vec = cand.Direction
                    dir_vec.Unitize()
                    key = round(abs(dir_vec * unitY), 2)
                    if key not in angle_buckets:
                        angle_buckets[key] = []
                    angle_buckets[key].append(i)
        
            bucket = angle_buckets.get(seg_key, [])
        
            best_idx = -1
            best_dist = float('inf')
        
            mid = segment.PointAt(0.5)
        
            for i in bucket:
                dist = candidates[i].DistanceTo(mid, True)
                if dist < best_dist:
                    best_dist = dist
                    best_idx = i
        
            return best_idx
            
        def computeindices(n):
            # raw pairs
            if n <= 2:
                return []
            else:
                center = n // 2
                if n % 2 == 0:
                    centers = {center - 1, center}
                    left = [i for i in range(n - 1) if i + 1 < center]
                else:
                    centers = {center}
                    left = [i for i in range(n - 1) if i + 1 <= center]
                right = [i for i in range(n - 1) if i >= center]
                left.sort(reverse=True)
                indexpairs = []
                for l, r in zip(left, right):
                    indexpairs += [[l, l + 1], [r + 1, r]]
            
            #extend each pair toward the centers
            extended_indexpairs = []
            min_c = min(centers)
            for i, j in indexpairs:
                path = [i, j]
                while path[-1] not in centers:
                    step = 1 if path[-1] < min_c else -1
                    path.append(path[-1] + step)
                extended_indexpairs.append(path)
            
            return extended_indexpairs
        
        if debugglobals:
            linelookup = None
            rawlinelookup = None
        
        def solver(polylines, solveparts = False, bimmode = False):
            if debugglobals:
                global rawlinelookup
                global linelookup #for debugging
            
            polys = []
            rawlinelookup = []
            segments_list = []
            
            icounter = 0
            
            for paidx, path in enumerate(polylines.Paths):
                polysatpath = list(polylines.Branch(path))
                polysizes = list(conduitsize.Branch(path))
                
                #print list(polysatpath)
                #print "next"
                #print bool(polysatpath)
                
                #optionalkey
                o_key = 0
                if path in optionalkeys.Paths:
                    o_key = optionalkeys.Branch(path)[0]
                
                for pidx, p in enumerate(polysatpath):
                    if p: #could be empty
                        trade_size = polysizes[pidx]
                        od_size = LineUtils.ConduitLookup.get_specs(trade_size)["od"]
                        #print p
                        #print list(p), path, pidx, icounter, paidx, trade_size, od_size, o_key
                        #print bimmode
                        polyobj = Polyline(list(p), path, pidx, icounter, paidx, trade_size, od_size, o_key, bimmode)
                        icounter += 1
                        polysegs = polyobj.segments
                        for polyseg in polysegs:
                            rawlinelookup.append(polyseg.geometry)
                            #segments_list.append(polyseg)
                        polys.append(polyobj)
            
            #linelookup = LineUtils.process_lines(rawlinelookup, 0.01, False, perlevel)
            #linelookupraw = LineUtils.process_lines(rawlinelookup, 0.01, True, perlevel)
            iters = 1 if speedmode else 3
            linelookup = LineUtils.process_lines_3d(rawlinelookup, 0.01, False, perlevel, "legacy", iters)
            linelookupraw = LineUtils.process_lines_3d(rawlinelookup, 0.01, True, perlevel, "legacy", iters)
        
            vectors = [[] for _ in linelookup]
            weight = [[] for _ in linelookup]

            
            if speedmode:
                for poly in polys:
                    poly.assign_ids(linelookup)
                    for seg in poly.segments:
                        seggeo = seg.geometry
                        # reuse id computed in assign_ids to avoid a second nearest-lookup
                        idx = seg.lookupid
                        if idx < 0:
                            continue
                        weight[idx].append(seggeo.Length)
                        segvec = seggeo.Direction
                        segvec.Unitize()
                        vectors[idx].append(segvec)
            else:
                for poly in polys:
                    poly.assign_ids(linelookup)
                    
                    for seg in poly.segments:
                        #print seg
                        seggeo = seg.geometry
                        idx = find_best_candidate(seggeo, linelookup)
                        weight[idx].append(seggeo.Length)
                        segvec = seggeo.Direction
                        segvec.Unitize()
                        #print segvec
                        vectors[idx].append(segvec)
        
            dominant_vectors = []

            
            for vec_list, w_list in zip(vectors, weight):
                #print vec_list
                if not vec_list:
                    continue  #added for robustness
                ref = rg.Vector3d(vec_list[0])
                ref.Unitize()
            
                pos_w = 0.0
                neg_w = 0.0
                for v, w in zip(vec_list, w_list):
                    if v * ref >= 0:  # dot product ≥ 0 => same hemisphere
                        pos_w += w
                    else:
                        neg_w += w
            
                if pos_w >= neg_w:
                    dominant = rg.Vector3d(ref)
                else:
                    dominant = rg.Vector3d(-ref.X, -ref.Y, -ref.Z)
            
                dominant_vectors.append(dominant)
            
            #adjust lines to match dominant vector
            for line, vec in zip(linelookup, dominant_vectors):
                linedir = line.Direction
                linedir.Unitize()
                dotcheck = linedir * vec 
                if dotcheck < 0:
                    pass
                    line.Flip()
            
            flippedlookup = []
            for l in linelookup:
                flipline = rg.Line(l.To, l.From)
                flippedlookup.append(flipline)
            
            #perpanel data fill
            perplookup = []
            if speedmode:
                def _prep_poly_for_panel(poly):
                    poly.assign_ids(linelookup)
                    poly.finalize_segments()
                    return poly.segments
                panel_results = LineUtils.parallel(_prep_poly_for_panel, polys)
                if panel_results == "failed to compute":
                    # safe fallback to original single-thread path
                    for poly in polys:
                        poly.assign_ids(linelookup) 
                        poly.finalize_segments()
                        polysegs = poly.segments
                        for polyseg in polysegs:
                            perplookup.append(polyseg)
                else:
                    for polysegs in panel_results:
                        if polysegs:
                            for polyseg in polysegs:
                                perplookup.append(polyseg)
            else:
                for poly in polys:
                    poly.assign_ids(linelookup) 
                    poly.finalize_segments()
                    polysegs = poly.segments
                    for polyseg in polysegs:
                        perplookup.append(polyseg)
            
            groupspre = defaultdict(list)
            for seg in perplookup:
                groupspre[seg.lookupid].append(seg)

            
            #print "groupspre", len(groupspre.values())
            
            for grps in groupspre.values():
                idx_map={}
                for gr in grps:
                    idx_map.setdefault(gr.polypathidx,[]).append(gr)
                
                stats=[]
                for elems in idx_map.values():
                    elemslagged = not elems[0].dirmatch
                    
                    counts={'Left':0,'Straight':0,'Right':0}
                    for e in elems:
                        if e.endpar<1.0: #only not end segments
                            counts[e.nextturn]+=1
                            
                    total=len(elems)
                    left=counts['Left']
                    straight=counts['Straight']
                    right=counts['Right']
                    
                    if elemslagged:
                        pass #flip l r if its in opposite direction to bundle
                        left, right = right, left
                    
                    #key=[left, straight, right]
                    key=[-left, straight, right]
                    
                    if right > left:
                        total_key = -total
                    else:
                        total_key = total
                        
                    key.append(total_key)
                    stats.append((key,elems))
                
                stats.sort(key=lambda x: x[0])
        #        if grps[0].quadrant in ["Up quadrant", "Down quadrant"]:
        #            stats.sort(key=lambda x: x[0])
        #        else:
        #            stats.sort(key=lambda x: x[0], reverse = True)
                
                for idx,item in enumerate(stats):
                    cnts, elems = item
                    for e in elems:
                        e.set_pathsortidx(cnts)
                        e.set_pathsortidx_(idx)
        
            #finalize data fill (mostly sortchains)
            if speedmode:
                def _finalize_poly(poly):
                    poly.assign_ids(linelookup)
                    poly.finalize_segments()
                    poly.assign_ids_raw(linelookupraw)
                    return poly.segments
                finalize_results = LineUtils.parallel(_finalize_poly, polys)
                if finalize_results == "failed to compute":
                    # fallback: original single-threaded behaviour
                    for poly in polys:
                        poly.assign_ids(linelookup) 
                        poly.finalize_segments()
                        poly.assign_ids_raw(linelookupraw)
                        
                        #move seglist creation here
                        polysegs = poly.segments
                        for polyseg in polysegs:
                            segments_list.append(polyseg)
                else:
                    for polysegs in finalize_results:
                        if polysegs:
                            for polyseg in polysegs:
                                segments_list.append(polyseg)
            else:
                for poly in polys:
                    poly.assign_ids(linelookup) 
                    poly.finalize_segments()
                    poly.assign_ids_raw(linelookupraw)
                    
                    #move seglist creation here
                    polysegs = poly.segments
                    for polyseg in polysegs:
                        segments_list.append(polyseg)
            
            groups = defaultdict(list)
            for seg in segments_list:
                groups[seg.lookupid].append(seg)
            
            for lid, group in groups.items():
                if lid < 0 or not group:
                    continue
            
                d = linelookup[lid].Direction
                d.Unitize()
                
                ordered = group

                if bimmode:
                    # ------------------------------------------------------------
                    # BIMMODE: panel-first precompute (internal order is isolated),
                    # then global ordering only at the bundle level.
                    #
                    # Also: FORCE split by direction so each bundle moves 1 way.
                    # ------------------------------------------------------------
                    panelbundles = defaultdict(list)

                    for seg in ordered:
                        segdir = seg.geometry.Direction
                        segdir.Unitize()
                        dot = segdir * d
                        dirsign = 1 if dot >= 0 else -1

                        seg.bim_dirsign = dirsign
                        panelbundles[(seg.polypathidx, dirsign)].append(seg)

                    panelbundle_lists = []

                    for (pathidx, dirsign), blist in panelbundles.items():
                        # 1) Precompute internal order (panel isolated)
                        blist.sort(key=lambda s: s.sortchain)

                        for r, s in enumerate(blist):
                            s.bim_panelrank = r
                            s.bim_bundlekey = (pathidx, dirsign)

                        # 2) Bundle-level key (decides where the bundle sits globally)
                        counts = {'Left': 0, 'Straight': 0, 'Right': 0}
                        for s in blist:
                            if s.endpar < 1.0:  # mimic your existing "skip end segments"
                                if s.nextturn in counts:
                                    counts[s.nextturn] += 1

                        left = counts['Left']
                        straight = counts['Straight']
                        right = counts['Right']
                        total = len(blist)

                        # If bundle runs opposite axis direction, swap Left/Right for global ordering
                        if dirsign < 0:
                            left, right = right, left

                        key = [-left, straight, right]
                        total_key = -total if right > left else total
                        key.append(total_key)

                        # Keep forward bundles before backward bundles when keys match
                        dir_order = 0 if dirsign > 0 else 1
                        key.append(dir_order)

                        # Stable tie-break (dict order in py2 is not stable)
                        key.append(pathidx)

                        panelbundle_lists.append((key, blist))

                    panelbundle_lists.sort(key=lambda x: x[0])

                    # groupsperpath == the actual BIMMODE bundles (panel+direction)
                    groupsperpath = [blist for _, blist in panelbundle_lists]

                    # Final ordered list = concatenated bundles (NO interleaving)
                    ordered = []
                    for blist in groupsperpath:
                        ordered.extend(blist)

                else:
                    ordered.sort(key=lambda s: s.sortchain)
                    groups2 = [list(g) for _, g in itertools.groupby(ordered, lambda s: s.dirmatch)]
                
                count = len(ordered)
                center = (count - 1) / 2.0
                center_global = center
                
                diameters = [s.outerdiameter for s in ordered]
                total_length = sum(diameters) + spacing * (len(ordered) - 1)
                center_offsets = []
                current_left = -total_length / 2.0
                #print diameters
                for diameter in diameters:
                    # cluster center = left edge + half its width
                    center_offsets.append(current_left + diameter / 2.0)
                    # advance left edge past this cluster + one spacing
                    current_left += diameter + spacing
                    
                raw_offsets = center_offsets#[(i - center_global) * spacing for i in range(count)]
                
                # map each segment to its raw offset
                seg_to_offset = {seg: raw_offsets[i] for i, seg in enumerate(ordered)}
            
                #perp = rg.Vector3d(-d.Y, d.X, 0)
                perp = rg.Vector3d(d.Y, -d.X, 0)
                perp.Unitize() #extra robustness
                
                if solveparts:
                    for idx, seg in enumerate(ordered):
                        offset = center_offsets[idx]#(idx - center) * spacing
                        move_vec = rg.Vector3d(perp)
                        move_vec *= offset
                        seg.move(move_vec)
                        seg.bundleindex = idx
            
                else:
                    if bimmode:
                        #for each subgroup in groupsperpath, compute its mean offset.
                        for bundle_index, subgroup in enumerate(groupsperpath):
                            mean_off = sum(seg_to_offset[seg] for seg in subgroup) / len(subgroup)
                        
                            #move every segment in this subgroup to that subgroup center
                            for seg in subgroup:
                                move_vec = rg.Vector3d(perp)
                                move_vec *= mean_off
                                seg.move(move_vec)
                                seg.bundleindex = bundle_index
                    else:
                        #print "not here"
                        #for each subgroup in groups2, compute its mean offset.
                        for bundle_index, subgroup in enumerate(groups2):
                            mean_off = sum(seg_to_offset[seg] for seg in subgroup) / len(subgroup)
                        
                            #move every segment in this subgroup to that subgroup center
                            for seg in subgroup:
                                move_vec = rg.Vector3d(perp)
                                move_vec *= mean_off
                                seg.move(move_vec)
                                seg.bundleindex = bundle_index
            
            secondpasscandidates = []
            firstpasses = []
            for poly in polys:
                if poly.dirflagged:
                    secondpasscandidates.append(poly)
                else:
                    firstpasses.append(poly)
            
            
            rebuiltree = gh.DataTree[System.Object]()
            
            for path in polylines.Paths:
                polysatpath = polylines.Branch(path)
                if len(polysatpath) < 1:
                    rebuiltree.AddRange([], path)
            
            for poly in polys:
                path = poly.ghpath
                rebuiltree.Add(poly.polyline_geometry, path)
            
            return rebuiltree, polys
        
        
        if not bothpasses: #for debugging
            #rebuiltree, polys = solver(polylines, True)
            rebuiltree, polys = solver(polylines, False)
            testpass, polys2, finaltree, treeflags, doublepolys, Boundaryobjects = [], [], [], [], [], []
        else:
            if bimmode:
                rebuiltree, polys = solver(polylines, False, True)
                testpass, polys2 = solver(rebuiltree, True, True)
            else:
                rebuiltree, polys = solver(polylines, False)
                testpass, polys2 = solver(rebuiltree, True)

            # speedmode: skip bundles & boundary pushing, use polys2 as final output
            if speedmode:
                finaltree = gh.DataTree[System.Object]()
                treeflags = gh.DataTree[System.Object]()
                for path in polylines.Paths:
                    polysatpath = polylines.Branch(path)
                    if len(polysatpath) < 1:
                        finaltree.AddRange([], path)
                        treeflags.AddRange([], path)
                for poly, flagpoly in zip(polys2, polys):
                    path = poly.ghpath
                    finaltree.Add(poly.polyline_geometry, path)
                    treeflags.Add(flagpoly.dirflagged, path)
                doublepolys = []
                Boundaryobjects = []
                return (rawlinelookup, linelookup, rebuiltree, polys, polys2, finaltree, treeflags, doublepolys, Boundaryobjects)

            doublepolys = [DoublePoly(poly, poly2) for poly, poly2 in zip(polys, polys2)]
            
            dsegments = []
            for doublepoly in doublepolys:
                for dseg in doublepoly.segmentpairs:
                    dsegments.append(dseg)
            
            bundles = defaultdict(list)
            
            for dseg in dsegments:
                bundles[dseg.id].append(dseg)
            
            
            gg, f, e, d, c, b, a = [], [], [], [], [], [], []
            coltags, coltags2 = [], []
            
            if pulltogether:
                #order matters, go from larger to smaller
                sortedbundles = sorted(bundles.values(), key = len, reverse = True)
                #tbundle = sortedbundles[0] #50 #6 #23
                #sortedbundles = [sortedbundles[0]] #2
                
                for tbundle in sortedbundles:
                    if not pullstart:
                        isfirst = False
                        for dline in tbundle:
                            if not dline.first.has_prev:
                                isfirst = True
                                break
                                
                        #this is a bundle containing first segment
                        if isfirst:
                            continue
                        
                    dd = tbundle[0].lookup.Direction
                    dd.Unitize()
                    dmid = tbundle[0].lookup.PointAt(0.5) #midpoint
                    perp2 = rg.Vector3d(dd.Y, -dd.X, 0)
                    perpline = rg.Line(dmid, perp2)
                    perpvec = rg.Vector3d(dd.Y, -dd.X, 0)
                    
                    #tbundle.sort(key = lambda t: perpline.ClosestParameter(t.geometry.From))
                    
                    sorted_lines = sorted(tbundle, key=lambda l: l.domain.T0)
                    groupedbundle = []
                    for line in sorted_lines:
                        if not groupedbundle or not LineUtils.domains_overlap(line.domain, groupedbundle[-1]['domain'], tol=-0.0005): #negative tol reduce the domains
                            groupedbundle.append({'lines': [line], 'domain': line.domain})
                        else:
                            grp = groupedbundle[-1]
                            grp['lines'].append(line)
                            grp['domain'] = rg.Interval.FromUnion(grp['domain'], line.domain)
                    
                    #print "groupedbundles : {}".format(len(groupedbundle))
                    
                    for bundlegrp in groupedbundle:
                        #print "here"
                        sortedgrp = sorted(bundlegrp["lines"], key = lambda t: perpline.ClosestParameter(t.geometry.From))
                     
                        grplen = len(sortedgrp)
                        lookup_lists = computeindices(grplen)
                        domain_slots = [[member.domain] for member in sortedgrp]
                        idx_slots = [[i_] for i_, member in enumerate(sortedgrp)]
                        
                        for lookup_list in lookup_lists:
                            seed_idx = lookup_list[0]
                            haysack = lookup_list[1:]
                            
                            currdom = domain_slots[seed_idx][0]
                            #candidatedoms = [domain_slots[hay] for hay in haysack] 
                            
                            conflict = False
                            newpos = seed_idx
                            #for candidatedom, hay in zip(candidatedoms, haysack):
                            for hay in haysack:
                                candidatedom = domain_slots[hay]
                                if any([LineUtils.domains_overlap(currdom, canddom, tol=-0.0005) for canddom in candidatedom]):
                                    conflict = True
                                    break
                                else:
                                    pass
                                    newpos = hay
                            
                            if newpos == seed_idx:
                                pass
                                #subgroup_collections.append([sortedgrp[seed_idx]])
                            else:
                                domain_slots[newpos].append(currdom)
                                domain_slots[seed_idx] = [rg.Interval(-100.0, -99.0)]
                                
                                idx_slots[newpos].append(seed_idx)
                                idx_slots[seed_idx] = []
                                #subgroup_collections.append([
                            
                        subgroup_collections = []
                        #print idx_slots
                        for slot in idx_slots:
                            if slot:
                                collection = []
                                for s in slot:
                                    collection.append(sortedgrp[s])
                                subgroup_collections.append(collection)
                    
                        #subgroup_collections.append(current_cluster)
            
                        bcount = grplen
                        bcenter = (bcount - 1) / 2.0
                        
                        for bidx, bseg in enumerate(sortedgrp):
                            #resetprevoffsets
                            segp = bseg.geometry.From
                            projectp = perpline.ClosestPoint(segp, False) #false infinite
                            adjustvec = rg.Vector3d(dmid-projectp)
                            
                            bseg.final.move(adjustvec)#resetoffsets
            
                        ccount = len(subgroup_collections)
                        
                        #compute each cluster’s real diameter and stash in a list to walk them
                        position_max_diameter_list = [max([c.first.outerdiameter for c in cl]) for cl in subgroup_collections]
                        
                        #total span of all clusters + gaps
                        total_length = sum(position_max_diameter_list) + spacing * (ccount - 1)
                        
                        #build a list of center‐offsets for each cluster
                        center_offsets = []
                        current_left = -total_length / 2.0
                        for diameter in position_max_diameter_list:
                            # cluster center = left edge + half its width
                            center_offsets.append(current_left + diameter / 2.0)
                            # advance left edge past this cluster + one spacing
                            current_left += diameter + spacing
                        
                        for cidx, cluster in enumerate(subgroup_collections):
                            # build the vector along your perpvec
                            offset = center_offsets[cidx]
                            move_vec = rg.Vector3d(perpvec)
                            move_vec *= offset
                        
                            for item in cluster:
                                #needed to create "boundary regions" of each cluster accurately
                                #else too many regions are created with too many gaps
                                item.set_maxslotdiameter(position_max_diameter_list[cidx])
                                gg.append(cidx)
                                item.final.move(move_vec)  # your custom move
            
            #bundles grouped on unique paths
            bundleboundaries = []
            
            #print "first bundles", len(bundles)
            #print bundles
            
            bundletolerance = 0.3
            
            Boundaryobjects = []
            
            for bidx, bundle in enumerate(bundles.values()):
                rectangles = []
                geometries = []
                vectorkey = bundle[0].geometry.Direction
                vectorkey.Unitize()
                
                anglekey = LineUtils.encode(vectorkey, 3)
                
                bundle_z = bundle[0].geometry.From.Z
                
                #print bundle
                for elem in bundle:
                    elem.set_bundleidx(bidx)
                    line = elem.geometry
                    geometries.append(line)
                    #size = elem.first.outerdiameter
                    size = elem.maxslotdiameter
                    rectangle = LineUtils.rectangle_from_line(line, size + spacing + bundletolerance)
                    rectangles.append(rectangle)
                    
                bundleboundary = LineUtils.union_intersecting_rects_outline(rectangles)
                for oidx, bound in enumerate(bundleboundary):
                    bndry = Boundary(bound, bidx, oidx, anglekey, vectorkey, bundle_z)
                    Boundaryobjects.append(bndry)
                
                lineindexlookup = [LineUtils.line_in_polyline(l, bundleboundary) for l in geometries]
                
                for elem, lil in zip(bundle, lineindexlookup):
                    elem.set_outlineidx(lil)
                #print "Vector {}, Angle {}, Bundlelen {}, unionregions {}, index lookup {}".format(0, anglekey, len(bundle), len(bundleboundary), lineindexlookup)
                #print len(bundle), "___", len(bundleboundary), "___", lineindexlookup
                
                bundleboundaries.append(bundleboundary)
                
            #print len(bundles)
            
            #_________OVERLAP PUSHING LOGIC_______
            # Maximum number of iterations for overlap resolution
            MAX_IT = 50
            
            # Reset all move vectors to zero
            for b in Boundaryobjects:
                b.movevector = rg.Vector3d(0, 0, 0)
            
            # Group boundaries by encoded key and optional Z-level clustering
            groups = {}
            for b in Boundaryobjects:
                if perlevel:
                    # snap Z to tolerance grid
                    zlvl = round(b.z / bundletolerance) * bundletolerance
                    key = (b.encoded, zlvl)
                else:
                    key = b.encoded
                groups.setdefault(key, []).append(b)
            
            #print len(groups.values())
            
            if pushflag: #pushout mechanism
                for group in groups.values():
                    # ─── ensure smaller boundaries go first ───
                    group.sort(key=lambda b: b.geometry.Length)
                    
                    # make a mutable copy of each boundary’s geometry
                    lookup = {}
                    for b in group:
                        lookup[b] = rg.Polyline(b.geometry)
                
                    locked = set()
                    it = 0
                    changed = True
                    
                    #track collision links inside this group
                    edges = defaultdict(set)
                    for _b in group:
                        edges[_b] = set()
                
                    # repeat until no more pushes or iteration limit reached
                    while changed and it < MAX_IT:
                        changed = False
                        it = it + 1
                
                        for b in group:
                            if b in locked:
                                continue
                
                            pl_s = lookup[b]
                            collided_with = None
                
                            # find first collider for b
                            for bL in group:
                                if bL is b:
                                    continue
                                if LineUtils.polylines_collide(pl_s, lookup[bL]):
                                    collided_with = bL
                                    break
                                
                            #remember that these two boundaries interacted
                            if collided_with is not None:
                                edges[b].add(collided_with)
                                edges[collided_with].add(b)
                
                            if collided_with is None:
                                continue
                
                            # build a unit perpendicular direction
                            perp = rg.Vector3d(-b.axis.Y, b.axis.X, 0)
                            perp.Unitize()
                
                            # ——— compute total shift in +perp direction ———
                            total_pos = 0.0
                            temp_pl = rg.Polyline(pl_s)
                            while True:
                                next_collider = None
                                for bO in group:
                                    if bO is b:
                                        continue
                                    if LineUtils.polylines_collide(temp_pl, lookup[bO]):
                                        next_collider = bO
                                        break
                                if next_collider is None:
                                    break
                
                                # for each vertex, shoot an infinite +perp ray to next_collider
                                pos_dists = []
                                for pt in temp_pl:
                                    start_pt = rg.Point3d(pt)
                                    end_pt = rg.Point3d(start_pt + perp * 1e6)
                                    line_curve = rg.LineCurve(start_pt, end_pt)
                                    poly_curve = rg.PolylineCurve(lookup[next_collider])
                                    events = rg.Intersect.Intersection.CurveCurve(
                                        line_curve, poly_curve, 0.0, 0.0
                                    )
                                    for ev in events:
                                        if ev.ParameterA > 0:
                                            pos_dists.append(ev.ParameterA)
                
                                if pos_dists:
                                    shift = max(pos_dists)
                                else:
                                    shift = 0.0
                                shift = shift + GLOBAL_TOL
                
                                total_pos = total_pos + shift
                                translation = rg.Transform.Translation(perp * shift)
                                temp_pl.Transform(translation)
                
                            # ——— compute total shift in -perp direction ———
                            total_neg = 0.0
                            temp_pl = rg.Polyline(pl_s)
                            while True:
                                next_collider = None
                                for bO in group:
                                    if bO is b:
                                        continue
                                    if LineUtils.polylines_collide(temp_pl, lookup[bO]):
                                        next_collider = bO
                                        break
                                if next_collider is None:
                                    break
                
                                # for each vertex, shoot an infinite -perp ray to next_collider
                                neg_dists = []
                                for pt in temp_pl:
                                    start_pt = rg.Point3d(pt)
                                    end_pt = rg.Point3d(start_pt - perp * 1e6)
                                    line_curve = rg.LineCurve(start_pt, end_pt)
                                    poly_curve = rg.PolylineCurve(lookup[next_collider])
                                    events = rg.Intersect.Intersection.CurveCurve(
                                        line_curve, poly_curve, 0.0, 0.0
                                    )
                                    for ev in events:
                                        if ev.ParameterA > 0:
                                            neg_dists.append(ev.ParameterA)
                
                                if neg_dists:
                                    shift = max(neg_dists)
                                else:
                                    shift = 0.0
                                shift = shift + GLOBAL_TOL
                
                                total_neg = total_neg + shift
                                translation = rg.Transform.Translation(perp * -shift)
                                temp_pl.Transform(translation)
                
                            # choose the shorter unsigned total shift
                            if total_pos <= total_neg:
                                shift_vec = perp * total_pos
                            else:
                                shift_vec = perp * -total_neg
                
                            # apply the chosen shift to the real geometry
                            translation = rg.Transform.Translation(shift_vec)
                            lookup[b].Transform(translation)
                            b.movevector = b.movevector + shift_vec
                
                            # lock this boundary and the one it first collided with
                            locked.add(b)
                            locked.add(collided_with)
                
                            changed = True
                            break  # restart from the top of the while loop
                
                        if changed:
                            continue
                
                    #assign boundlegroup ids for this group based on collision graph
                    visited = set()
                    gid = 0
                    for seed in group:
                        if seed in visited:
                            continue
                        stack = [seed]
                        component = []
                        while stack:
                            cur = stack.pop()
                            if cur in visited:
                                continue
                            visited.add(cur)
                            component.append(cur)
                            for nb in edges.get(cur, ()):
                                if nb not in visited:
                                    stack.append(nb)
                        for m in component:
                            m.boundlegroup = gid
                        gid = gid + 1
                
                    # warn if iteration limit reached
                    if it >= MAX_IT:
                        print("Warning: maximum iterations reached for one group")
                    else:
                        print "{} optimization iterations out of {} set as max".format(it, MAX_IT)
            
            
            #_________APPLYING BOUNDARIES SHIFTS_______
            boundarylookup = defaultdict(lambda: defaultdict(list))
            
            for b in Boundaryobjects:
                boundarylookup[b.bundleidx][b.outlineidx].append(b)
            
            for doublepoly in doublepolys:
                for doublesegment in doublepoly.segmentpairs:
                    ds = doublesegment
                    try:
                        linkedboundary = boundarylookup[ds.bundleidx][ds.outlineidx][0]
                        shift = linkedboundary.movevector
                        
                        #persist boundary linked-group id on the segment
                        ds.set_boundlegroup(linkedboundary.boundlegroup)
                        
                        if shift.Length > GLOBAL_TOL:
                            pass
                            doublesegment.final.move(shift)
                    except:
                        print "bundleindex {}, outlineindex {}".format(ds.bundleidx, ds.outlineidx)
            
            #_________FORMING FINAL DATATREES_______
            
            adjusted = []
            for dseg in dsegments:
                adjusted.append(dseg.final.geometry)
            
            finaltree = gh.DataTree[System.Object]()
            treeflags = gh.DataTree[System.Object]()
            
            for path in polylines.Paths:
                polysatpath = polylines.Branch(path)
                if len(polysatpath) < 1:
                    finaltree.AddRange([], path)
                    treeflags.AddRange([], path)
            
            for poly, flagpoly in zip(polys2, polys):
                #print dir(poly)
                #break
                path = poly.ghpath
                finaltree.Add(poly.polyline_geometry, path)
                treeflags.Add(flagpoly.dirflagged, path)
        
        # return outputs 
        return (rawlinelookup, linelookup, rebuiltree, polys, polys2, finaltree, treeflags, doublepolys, Boundaryobjects)

