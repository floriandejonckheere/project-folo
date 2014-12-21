/**
 * ramsey_numbers.als - Calculating Ramsey numbers in Alloy 4
 *
 * Florian Dejonckheere <florian@floriandejonckheere.be>
 * Jasper D'haene <jasper.dhaene@gmail.com>
 *
 * */

/**
 * Om dit probleem wat interessanter en modelleerbaarder
 * te maken, stellen we dat de te calculeren Ramseygetallen
 * gewoon het antwoord zijn van het 'party problem':
 * 
 * R(m,n) = Hoeveel gasten moeten er uitgenodigd worden
 * zodat >= m elkaar kennen en >= n elkaar niet kennen.
 *
 * Hint: R(3, 3) = 6 [1]
 * Hint: R(3, 3) = R(3, 3, 2)
 * Hint: R(3) = R(3, 3, 3) = R(3, 3, 3; 3)
 * Hint: R(3, 3, 3) = 17 [2]
 *
 * [1] http://mathworld.wolfram.com/RamseyNumber.html
 * [2] http://en.wikibooks.org/wiki/Combinatorics/Bounds_for_Ramsey_numbers
 *
 * */

sig Colour {}
sig Node {}

sig Edge {
	connection: Node -> Node,
	colour: one Colour
}{
	// No self-referencing
	all node:Node | (node -> node not in connection)
}

// Make sure that 'colouring' is the same as Edge->colour
fact {
	colour = ~(Graph.colouring)
}

// Make sure symmetric relations have the same colour
fact {
	all e: Edge | some e': Edge | {
		e.connection = ~(e'.connection) => e.colour = e'.colour
	}
}

// Force a monochromely-coloured set with X nodes
pred Colours [col: Colour, X: Int] {
	#((~(Graph.colouring)).col) = X
}

one sig Graph{
	nodes: set Node,

	// Edges: Node -> Node
	edges: set Edge,
	colouring: Colour one -> some Edge
}{
	// All nodes in graph
	all node: Node | node in nodes

	// All edges in graph
	all edge:Edge | edge in edges

	// Edges relationship is symmetrical
	all edge: Edge | some edge':Edge | edge.connection = ~(edge'.connection)

	// Every edge only connects 2 points
	all edge: Edge | one edge.connection

	// Complete graph
	all n, n' : Node | some e:Edge | n != n' => n -> n' in e.connection
}

/**
 * Run the numbers
 *
 * #Edge should be #(N)*#(N-1)
 * N = 3 => E = 6
 * N = 4 => E = 12
 * N = 5 => E = 20
 * N = 6 => E = 30
 *
 * */
run {
	// Make sure two sets of disjointly coloured edges exist
	some c, c': Colour | c != c' and {
		Colours[c, 3]
		Colours[c', 3]
	}
} for exactly 2 Colour, exactly 3 Node, exactly 6 Edge
