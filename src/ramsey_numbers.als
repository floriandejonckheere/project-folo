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

sig Node{colour: one Colour }

one sig Graph{
	nodes : set Node,
	edges: Node -> Node
}{
	//no self-referencing
	all node:Node |  (node->node not in edges)
	//all node->node relationships need to be nodes from the set 'nodes'
	all node: Node | (edges.node in nodes) && (~edges.node in nodes)

	//all nodes in graph
	all node: Node | node in nodes
	//all nodes need to be in a 'edge' relationship
	//TODO:not sure of this one
   //all node: Node | some node': Node | node->node' in edges

   //edges relationship is symmetrical
   edges = ~edges

   //edge from a node to every other node
   all node, node' : Node | node != node' => node' in edges.node

}


run {} for 1 Graph, exactly 3 Colour,  exactly 4 Node
