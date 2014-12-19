/*
* ramsey_numbers.als - Calculating Ramsey numbers in Alloy 4
*
* Florian Dejonckheere <florian@floriandejonckheere.be>
* Jasper D'haene <jasper.dhaene@gmail.com>
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
