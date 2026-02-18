from ptl_multiplex_framework import InterLayerCouplingLogic

class SimpleCoupling(InterLayerCouplingLogic):
    """A simple implementation of inter-layer coupling.

    This class allows transitions between layers if the source node's
    position (excluding the layer identifier) is the same as the target
    node's position in the target layer.
    """
    def __init__(self, allowed_transitions: dict = None):
        super().__init__()
        # allowed_transitions is a dictionary where keys are source_layer_ids
        # and values are lists of target_layer_ids that are allowed from that source.
        # Example: {'A': ['B', 'C'], 'B': ['A']}
        self.allowed_transitions = allowed_transitions if allowed_transitions else {}

    def get_possible_targets(self, source_node_info: dict, source_layer: 'PTLLayer', target_layer: 'PTLLayer') -> list[dict]:
        """Determines if a transition from source_node in source_layer to a node in target_layer is possible.

        For this simple implementation, a transition is possible if:
        1. The target_layer is listed as an allowed transition from the source_layer.
        2. The node coordinates (excluding layer ID) are identical.
        """
        possible_targets = []
        source_layer_id = source_layer.boundary_id
        target_layer_id = target_layer.boundary_id

        if source_layer_id in self.allowed_transitions and target_layer_id in self.allowed_transitions[source_layer_id]:
            # Assume source_node_info contains the coordinate of the source node
            # For simplicity, we'll assume the target node has the same coordinate in the target layer
            # In a real scenario, this might involve more complex logic or querying the target layer
            possible_targets.append({
                "coordinate": source_node_info.get("coordinate"), # Carry over the coordinate
                "layer_id": target_layer_id
            })
        
        return possible_targets

    def can_traverse(self, source_node_info: dict, target_node_info: dict, source_layer: 'PTLLayer', target_layer: 'PTLLayer') -> bool:
        """Checks if a specific transition is allowed based on the defined rules."""
        source_layer_id = source_layer.boundary_id
        target_layer_id = target_layer.boundary_id

        if source_layer_id in self.allowed_transitions and target_layer_id in self.allowed_transitions[source_layer_id]:
            # For this simple implementation, we assume if the layers are allowed to connect,
            # any node can transition to its counterpart in the other layer.
            # A more complex implementation would check specific node properties.
            return True
        return False

# Example Usage (Illustrative)
if __name__ == "__main__":
    # This part is for demonstration and testing; not part of the class definition itself.
    # Create dummy PTLModel instances for layers
    class DummyPTLModel:
        def __init__(self, boundary_id):
            self.boundary_id = boundary_id

        def get_node(self, coordinate):
            # Dummy node retrieval
            return {"coordinate": coordinate, "layer_id": self.boundary_id}
    
    # Need PTLLayer for the example to run, let's define a dummy one or import it
    # For now, let's assume it's available or comment out the example that needs it.
    # To make this runnable standalone for basic logic check, we might need to simplify
    # or mock PTLLayer if it's not defined here.
    
    # Simplified example without PTLLayer dependency for quick check:
    allowed_transitions_config = {
        "A": ["B", "C"],
        "B": ["A"]
    }
    simple_coupling_logic = SimpleCoupling(allowed_transitions_config)
    
    # Mocking layer objects with just boundary_id for the logic to work
    class MockLayer: 
        def __init__(self, boundary_id): self.boundary_id = boundary_id

    layer_A = MockLayer("A")
    layer_B = MockLayer("B")
    layer_C = MockLayer("C")

    source_node_example = {"coordinate": (1, 2, 3)}

    print(f"Testing transitions from Layer A with node at {source_node_example['coordinate']}:")
    possible_targets_from_A = simple_coupling_logic.get_possible_targets(source_node_example, layer_A, layer_B)
    print(f"To Layer B: {possible_targets_from_A}")
    possible_targets_from_A_to_C = simple_coupling_logic.get_possible_targets(source_node_example, layer_A, layer_C)
    print(f"To Layer C: {possible_targets_from_A_to_C}")

    source_node_B_example = {"coordinate": (4, 5, 6)}
    print(f"\nTesting transitions from Layer B with node at {source_node_B_example['coordinate']}:")
    possible_targets_from_B_to_A = simple_coupling_logic.get_possible_targets(source_node_B_example, layer_B, layer_A)
    print(f"To Layer A: {possible_targets_from_B_to_A}")

    possible_targets_from_B_to_C = simple_coupling_logic.get_possible_targets(source_node_B_example, layer_B, layer_C)
    print(f"To Layer C: {possible_targets_from_B_to_C}")

    print(f"\nCan traverse from A to B? {simple_coupling_logic.can_traverse(source_node_example, {}, layer_A, layer_B)}")
    print(f"Can traverse from B to C? {simple_coupling_logic.can_traverse(source_node_B_example, {}, layer_B, layer_C)}")

