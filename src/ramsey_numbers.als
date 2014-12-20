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

sig Node{ }

sig State{
	nodes : Node,
	edges: Node->Node
}{
	//no self-referencing
	all node: Node,state: State{
		no state.edges.node = node
	}
}
