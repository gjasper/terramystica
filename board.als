module board

abstract sig Player {
	next: one Player,
	desiredTerrain: one TerrainType
}

one sig Player1 extends Player {} {
    next = Player2
    desiredTerrain = TypeA
}
one sig Player2 extends Player {} {
    next = Player3
    desiredTerrain = TypeB
}
one sig Player3 extends Player {} {
    next = Player4
    desiredTerrain = TypeC
}
one sig Player4 extends Player {} {
    next = Player1
    desiredTerrain = TypeD
}

abstract sig Round {
	next: one Round
}

one sig Start extends Round {} { next = Round1}
one sig Round1 extends Round {} { next = Round2}
one sig Round2 extends Round {} { next = Round3}
one sig Round3 extends Round {} { next = Round4}
one sig Round4 extends Round {} { next = Round5}
one sig Round5 extends Round {} { next = Round6}
one sig Round6 extends Round {} { next = Round7}
one sig Round7 extends Round {} { next = Round8}
one sig Round8 extends Round {} { next = Round9}
one sig Round9 extends Round {} { next = Round10}
one sig Round10 extends Round {} { next = Round11}
one sig Round11 extends Round {} { next = Round12}
one sig Round12 extends Round {} { next = Round13}
one sig Round13 extends Round {} { next = Round14}
one sig Round14 extends Round {} { next = Round15}
one sig Round15 extends Round {} { next = Round16}
one sig Round16 extends Round {} { next = Finish}
one sig Finish extends Round {} { next = Finish}

abstract sig TerrainType {}
one sig TypeA extends TerrainType {}
one sig TypeB extends TerrainType {}
one sig TypeC extends TerrainType {}
one sig TypeD extends TerrainType {}

abstract sig BuildingTier {
	next: one BuildingTier
}
one sig TierI extends BuildingTier {} { next = TierII }
one sig TierII extends BuildingTier {} { next = TierIII }
one sig TierIII extends BuildingTier {} { next = TierIV }
one sig TierIV extends BuildingTier {} { next =  TierIV }

abstract sig Tile {
    NE: one Tile,
    E: one Tile,
    SE: one Tile,
    SW: one Tile,
    W: one Tile,
    NW: one Tile,
    var terrainType: one TerrainType,
    var ownedBy: lone Player,
    var building: lone BuildingTier
}

one sig Wall extends Tile {} { ownedBy = Player - Player }
abstract sig GameTile extends Tile {}

abstract sig Corner extends GameTile {} {
    #NonCorner = 1 || no ((NE + E + SE + SW + W + NW) & Corner) // min(#GameTile) == 5
    // no ((NE + E + SE + SW + W + NW) & Corner) // min(#GameTile) == 8
}

sig NonCorner extends GameTile {} {
    #NonCorner = 1 || #((NE + E + SE + SW + W + NW) & Corner) < 3
    #(NE + E + SE + SW + W + NW - Wall) > 2
}

one sig NECorner extends Corner {} {
    NE = Wall
    E = Wall
    SE = Wall
    SW in NonCorner
    W in GameTile
    NW = Wall
}

one sig NWCorner extends Corner {} {
    NE = Wall
    E in GameTile
    SE in NonCorner
    SW = Wall
    W = Wall
    NW = Wall
}

one sig SECorner extends Corner {} {
    NE = Wall
    E = Wall
    SE = Wall
    SW = Wall
    NW in NonCorner
    W in GameTile
}

one sig SWCorner extends Corner {} {
    NE in NonCorner
    E in GameTile
    SE = Wall
    SW = Wall
    W = Wall
    NW = Wall
}

fact SharedNeighbors {
	all t : GameTile, se: t.SE, w: se.W |
        ((se + w) not in GameTile) || (w.NE = t && t.SW = w)
	all t : GameTile, e: t.E, sw: e.SW |
        ((e + sw) not in GameTile) || (sw.NW = t && t.SE = sw)
	all t : GameTile, sw: t.SW, nw: sw.NW |
        ((sw + nw) not in GameTile) || (nw.E = t && t.W = nw)
	all t : GameTile, w: t.W, ne: w.NE |
        ((w + ne) not in GameTile) || (ne.SE = t && t.NW = ne)
	all t : GameTile, nw: t.NW, e: nw.E |
        ((nw + e) not in GameTile) || (e.SW = t && t.NE = e)
	all t : GameTile, ne: t.NE, se: ne.SE |
        ((ne + se) not in GameTile) || (se.W = t && t.E = se)
}

fact NeighborIsMirrored {
    all t : GameTile |
            (t.NE = Wall || t.NE.SW = t)
        &&  (t.NW = Wall || t.NW.SE = t)
        &&  (t.W = Wall || t.W.E = t)
        &&  (t.SW = Wall || t.SW.NE = t)
        &&  (t.SE = Wall || t.SE.NW = t)
        &&  (t.E = Wall || t.E.W = t)
}

fact NoSelfNeighbor {
    all t : GameTile |
            t.NE != t
        &&  t.NW != t
        &&  t.W != t
        &&  t.SW != t
        &&  t.SE != t
        &&  t.E != t
}

fact NoRepeatedNeighbor {
    all t : GameTile |
            ((t.NE + t.E) in Wall || t.NE != t.E)
        &&  ((t.NE + t.SE) in Wall || t.NE != t.SE)
        &&  ((t.NE + t.SW) in Wall || t.NE != t.SW)
        &&  ((t.NE + t.W) in Wall || t.NE != t.W)
        &&  ((t.NE + t.NW) in Wall || t.NE != t.NW)
        &&  ((t.E + t.SE) in Wall || t.E != t.SE)
        &&  ((t.E + t.SW) in Wall || t.E != t.SW)
        &&  ((t.E + t.W) in Wall || t.E != t.W)
        &&  ((t.E + t.NW) in Wall || t.E != t.NW)
        &&  ((t.SE + t.SW) in Wall || t.SE != t.SW)
        &&  ((t.SE + t.W) in Wall || t.SE != t.W)
        &&  ((t.SE + t.NW) in Wall || t.SE != t.NW)
        &&  ((t.SW + t.W) in Wall || t.SW != t.W)
        &&  ((t.SW + t.NW) in Wall || t.SW != t.NW)
        &&  ((t.W + t.NW) in Wall || t.W != t.NW)
}

fact WallPointsToItself {
	all t : Wall |
            t.NE = Wall
        &&  t.NW = Wall
        &&  t.W = Wall
        &&  t.SW = Wall
        &&  t.SE = Wall
        &&  t.E = Wall
}

fact CornersAreReachable {
    all t : GameTile |
           NECorner in t.*Neighbors
        && SECorner in t.*Neighbors
        && SWCorner in t.*Neighbors
        && NWCorner in t.*Neighbors
}

fact CornersAreCorners {
    SWCorner.^E.SE = Wall
    SECorner.^W.SW = Wall
    NWCorner.^E.NE = Wall
    NECorner.^W.NW = Wall
}

fact BoardIsSquare {
    SWCorner.^E.SE = Wall
    SECorner.^W.SW = Wall
    NWCorner.^E.NE = Wall
    NECorner.^W.NW = Wall
    SECorner in SWCorner.*E
    SWCorner in SECorner.*W
    NECorner in NWCorner.*E
    NWCorner in NECorner.*W
}

fun Neighbors : Tile -> Tile {
    NE + E + SE + SW + W + NW
}
