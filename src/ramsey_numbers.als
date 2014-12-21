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
		e.connection = ~(e'.connection) && e.colour = e'.colour
	}
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

pred Sub_Graph [ X:  Int] {
	some col: Colour | some edges_set:  set col.(Graph.colouring) | 
		#edges_set = X
		&& No_Symmetry[edges_set] // Geen A->B en B->A in edges_set.
		&& Mutual_Friends[edges_set] // Alle edges zijn op een willekeurige manier verbonden met elkaar
}

pred No_Symmetry[edges_set:set Edge]{
	all edge: edges_set | all edge':(edges_set-edge) | edge.connection != ~(edge'.connection)
}

fun Nodes_In_Set[edges:set Edge]: set Node{
	{
		n: Node | some n':Node | {
			n ->n' in edges.connection || n'->n in edges.connection
		}
	}
}

pred Mutual_Friends[edges_set:set Edge]{
	all node: Nodes_In_Set[edges_set] |  all node': (Nodes_In_Set[edges_set] - node) |
	node->node' in edges_set.connection || node'->node in edges_set.connection
}

/**
 * #Edge should be #Node*(#Node-1)
 */

// R(r,s) = R(5,2) = 5
run {
	// Input X = (r * (r-1))/2. Choose either r or s
	Sub_Graph[10]
}
for 2 Colour, exactly 5 Node, exactly 20 Edge
