/**
 * ramsey_numbers.als - Calculating Ramsey numbers in Alloy 4
 *
 * Florian Dejonckheere <florian@floriandejonckheere.be>
 * Jasper D'haene <jasper.dhaene@gmail.com>
 *
 * */

/**
 * Om dit probleem wat interessanter en modelleerbaarder
 *  te maken, stellen we dat de te calculeren Ramseygetallen
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

sig Colour{}

sig Node{}

sig Edge{
	connection: Node ->Node,
	colour:  one Colour
}{
	//no self-referencing
	all node:Node | (node->node not in connection)

}

//make sure that 'colouring' is the same as Edge->colour
fact {
	colour = ~(Graph.colouring)
}

//specify the colour conditions
fact {
	//there are X edges in the same colour and Y in a different. X+Y=#Edge. X and Y are even.
	some col:Colour | #((~(Graph.colouring)).col) = 4
	some col:Colour | #((~(Graph.colouring)).col) = 2
}


one sig Graph{
	nodes : set Node,
//	edges: Node -> Node
    edges: set Edge,
	colouring: Colour one -> some Edge
}{
	//all nodes in graph
	all node: Node | node in nodes
	//all edges in graph
	all edge:Edge | edge in edges

   //edges relationship is symmetrical
	all edge: Edge | some edge':Edge | edge.connection = ~(edge'.connection)
	
	//every edge only connects 2 points
	all edge: Edge | one edge.connection

   //complete graph
   all node, node' : Node | some edge:Edge | node != node' => node->node' in edge.connection

}

run {} for 1 Graph, exactly 2 Colour,  exactly 3 Node,  exactly 6 Edge
