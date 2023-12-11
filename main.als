open board

enum ActionType { Noop, Transform, Build, BuildFirst }

one sig Game {
	var currentPlayer: one Player,
	var currentAction: one ActionType
}

pred noTileIsOwned {
    all t: GameTile | no t.ownedBy && no t.building
}

pred someTilesForEachTerrain {
    some t: GameTile | t.terrainType = TypeA
    some t: GameTile | t.terrainType = TypeB
    some t: GameTile | t.terrainType = TypeC
    some t: GameTile | t.terrainType = TypeD
}

pred noSameTypeNeighbor {
    all t : GameTile |
            t.terrainType != t.NE.terrainType
        &&  t.terrainType != t.E.terrainType
        &&  t.terrainType != t.SE.terrainType
        &&  t.terrainType != t.SW.terrainType
        &&  t.terrainType != t.W.terrainType
        &&  t.terrainType != t.SW.terrainType
}

pred noOwnershipChange [tiles: GameTile] {
    all t : tiles | t.ownedBy' = t.ownedBy
}

pred noBuildingChange [tiles: GameTile] {
    all t : tiles | t.building' = t.building
}

pred noTerrainChange [tiles: GameTile] {
    all t : tiles | t.terrainType' = t.terrainType
}

pred transform [t: GameTile] {
	// pre
    no t.ownedBy
    no t.building
    (t.terrainType != Game.currentPlayer'.desiredTerrain)
    Game.currentPlayer' in t.Neighbors.ownedBy
	// post
	t.terrainType' != t.terrainType
	t.terrainType' = Game.currentPlayer'.desiredTerrain
	// frame
    noOwnershipChange[GameTile]
    noBuildingChange[GameTile]
    noTerrainChange[GameTile - t]
    Game.currentAction' = Transform
}

pred buildFirst [t: GameTile] {
	// pre
    no t.ownedBy
    no t.building
    t.terrainType = Game.currentPlayer'.desiredTerrain
    no ownedBy.(Game.currentPlayer')
	// post
	t.ownedBy' = Game.currentPlayer'
    t.building' = TierI
    // frame
    noOwnershipChange[GameTile - t]
    noBuildingChange[GameTile - t]
    noTerrainChange[GameTile]
    // track
    Game.currentAction' = BuildFirst
}

pred build [t: GameTile] {
	// pre
    no t.ownedBy
    no t.building
    Game.currentPlayer' in t.Neighbors.ownedBy
    t.terrainType' = Game.currentPlayer'.desiredTerrain
	// post
	t.ownedBy' = Game.currentPlayer'
    t.building' = TierI
    // frame
    noOwnershipChange[GameTile - t]
    noBuildingChange[GameTile - t]
    noTerrainChange[GameTile]
    // track
    Game.currentAction' = Build
}

pred init {
	someTilesForEachTerrain
	noSameTypeNeighbor
    noTileIsOwned
    Game.currentAction = Noop
}

pred trans {
	some t: GameTile | transform [t]
    or
	some t: GameTile | buildFirst [t]
    or
	some t: GameTile | build [t]
}

pred passTurn {
	Game.currentPlayer' = Game.currentPlayer.next
}

pred System {
	init
	always (trans and passTurn)
}

pred AllActions {
	#GameTile = 12
    eventually Game.currentAction = BuildFirst
    eventually Game.currentAction = Build
    eventually Game.currentAction = Transform
}

pred TwoSquaresEach {
    eventually all p: Player | #ownedBy.p = 2
}

run execution {
    System
	TwoSquaresEach
} for 13 but 15..20 steps
