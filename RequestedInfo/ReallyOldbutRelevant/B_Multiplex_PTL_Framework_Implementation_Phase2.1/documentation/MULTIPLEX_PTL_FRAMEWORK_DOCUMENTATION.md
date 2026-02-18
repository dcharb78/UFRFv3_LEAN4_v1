# UFRF Multiplex PTL Framework Documentation

## 1. Introduction

This document provides comprehensive documentation for the UFRF (Unified Fractal Resonance Framework) Multiplex Positional Transition Lattice (PTL) framework. The framework is designed to model and simulate complex systems by representing different boundary conditions as distinct PTL layers and managing the interactions (coupling) between these layers. This allows for a nuanced exploration of how entities or information traverse and transform across varied contextual environments within the UFRF.

The core idea is to have multiple, potentially heterogeneous, PTL instances, each representing a specific boundary condition or state-space, and a managing framework that orchestrates these layers and the transitions between them. This approach provides flexibility in modeling systems where the underlying rules or structures change based on context or state.

## 2. Architecture Overview

The Multiplex PTL framework consists of the following key components:

*   **`PTLModel_v12` (Positional Transition Lattice Model, Version 12):** This is the fundamental building block, representing a single PTL. It encapsulates the nodes (PTLCoordinates), their attributes, and the intra-layer connections (edges) that define possible transitions within that specific boundary condition. Each instance of `PTLModel_v12` is associated with a unique `boundary_id`.
*   **`PTLLayer`:** A wrapper class that holds an instance of `PTLModel_v12`. It acts as an identifiable layer within the multiplex system, identified by its `boundary_id`.
*   **`InterLayerCouplingLogic`:** An abstract base class defining the interface for how transitions *between* different PTLLayers occur. Concrete implementations of this class will define specific rules and conditions for inter-layer traversal. The `SimpleCoupling` class is one such concrete implementation provided as a basic example.
*   **`MultiplexPTLManager`:** The central orchestrator. It manages a collection of `PTLLayer` objects and the `InterLayerCouplingLogic` rules that define how these layers are connected. It provides methods to add/remove layers, define coupling rules, and query possible inter-layer transitions.
*   **`ptl_multiplex_visualizer_v0`:** A utility module for generating 3D visualizations of the multiplex PTL structure, including layers, nodes, and inter/intra-layer connections. This helps in understanding the complex network formed by the multiplex PTL.

### Architectural Diagram (Conceptual)

```
+-------------------------+
| MultiplexPTLManager     |
|-------------------------|
| - layers: Dict[str, PTLLayer] |
| - coupling_rules: List  |
|-------------------------|
| + add_layer()           |
| + remove_layer()        |
| + define_coupling_rule()|
| + get_inter_layer_transitions() |
+-------------------------+
          | 1..*
          | manages
          v
+-------------------------+
| PTLLayer                |
|-------------------------|
| - boundary_id: str      |
| - ptl_instance: PTLModel_v12 |
+-------------------------+
          | 1
          | contains
          v
+-------------------------+
| PTLModel_v12            |
|-------------------------|
| - boundary_id: str      |
| - nodes: Dict[PTLCoordinate, PTLNode] |
| - ... (methods for PTL ops) |
+-------------------------+

+-------------------------+
| InterLayerCouplingLogic |
| (Abstract)              |
|-------------------------|
| + get_possible_targets()|
| + can_traverse()        |
+-------------------------+
          ^
          | (implements)
          |
+-------------------------+
| SimpleCoupling          |
| (Concrete Logic)        |
+-------------------------+
```

## 3. Core Components - API Documentation

### 3.1. `PTLModel_v12`

(Adapted from `ptl_model.py` provided by the user, now `ptl_model_v12.py`)

**File:** `ptl_model_v12.py`

This class is responsible for the definition and operation of a single PTL.

*   **`PTLCoordinate(domain_id, level_id, system_id, cycle_id)`**: A named tuple representing the unique address of a node within the PTL hierarchy.
*   **`PTLNode(coordinate, attributes=None)`**: Represents a single node in the PTL. It stores its `PTLCoordinate` and any associated `attributes` (e.g., state, energy). It also maintains a dictionary of `neighbors` and the type of connection to them.
*   **`PTLModel_v12(boundary_id, config=None)`**:
    *   `__init__(self, boundary_id: str, config: Optional[Dict[str, Any]] = None)`: Initializes the PTL model with a specific boundary ID and optional configuration.
    *   `get_or_create_node(self, coordinate: PTLCoordinate, attributes: Optional[Dict[str, Any]] = None) -> PTLNode`: Retrieves an existing node or creates a new one at the given coordinate.
    *   `add_connection(self, source_coord: PTLCoordinate, target_coord: PTLCoordinate, connection_type: str, attributes: Optional[Dict[str, Any]] = None)`: Adds a directed connection between two nodes.
    *   `establish_intra_system_connections(self, domain_id: int, level_id: int, system_id: int)`: Creates the standard 13-position cycle connections for a given system.
    *   `establish_inter_system_transition(self, domain_id: int, level_id: int, current_system_id: int)`: Creates a transition from position 10 (Rest) of the current system to the seed positions (11, 12, 13 mapped to 1, 2, 3) of the next system.
    *   `get_node(self, coordinate: PTLCoordinate) -> Optional[PTLNode]`: Retrieves a node by its coordinate.
    *   `get_neighbors(self, coordinate: PTLCoordinate, connection_type: Optional[str] = None) -> Dict[PTLCoordinate, Dict[str, Any]]`: Retrieves neighbors of a node, optionally filtered by connection type.

### 3.2. `ptl_multiplex_framework.py`

**File:** `ptl_multiplex_framework.py`

This module contains the classes for managing the multiplexed PTL environment.

*   **`PTLModelFramework = PTLModel_v12`**: An alias for `PTLModel_v12` used within the framework for clarity, especially in type hinting for layers.

*   **`InterLayerCouplingLogic` (Abstract Base Class)**:
    *   `__init__(self, config: Optional[Dict[str, Any]] = None)`: Constructor.
    *   `get_possible_targets(self, source_node_info: Dict[str, Any], source_layer: "PTLLayer", target_layer: "PTLLayer") -> List[Dict[str, Any]]`: Abstract method. Implementations should return a list of potential target node information in the `target_layer` given a `source_node_info` from the `source_layer`.
    *   `can_traverse(self, source_node_info: Dict[str, Any], target_node_info: Dict[str, Any], source_layer: "PTLLayer", target_layer: "PTLLayer") -> bool`: Abstract method. Implementations should return `True` if a specific transition is allowed, `False` otherwise.

*   **`PTLLayer`**:
    *   `__init__(self, boundary_id: str, ptl_model_instance: PTLModelFramework)`: Initializes a layer with a unique `boundary_id` and an instance of `PTLModelFramework` (which is `PTLModel_v12`).
    *   `get_node(self, coordinate: PTLCoordinate) -> Optional[PTLNode]`: Delegates to the internal PTL instance.
    *   `get_neighbors(self, coordinate: PTLCoordinate) -> List[PTLNode]`: Delegates to the internal PTL instance.

*   **`MultiplexPTLManager`**:
    *   `__init__(self)`: Initializes the manager with empty layer and coupling rule stores.
    *   `add_layer(self, boundary_id: str, ptl_config: Optional[Dict[str, Any]] = None) -> PTLLayer`: Creates a new `PTLModel_v12` instance and a `PTLLayer`, adds it to the manager, and returns the created `PTLLayer`.
    *   `get_layer(self, boundary_id: str) -> Optional[PTLLayer]`: Retrieves a layer by its `boundary_id`.
    *   `remove_layer(self, boundary_id: str) -> bool`: Removes a layer and its associated coupling rules. Returns `True` if successful.
    *   `define_coupling_rule(self, rule_id: str, source_layer_id: str, target_layer_id: str, coupling_logic: InterLayerCouplingLogic) -> None`: Defines a coupling rule between two layers using a specific `InterLayerCouplingLogic` instance.
    *   `get_inter_layer_transitions(self, source_node_coordinate: PTLCoordinate, source_layer_id: str) -> List[Tuple[PTLCoordinate, str, str]]`: Given a node coordinate in a source layer, returns a list of possible target node coordinates, their layer IDs, and the rule ID enabling the transition. Each tuple is `(target_coordinate, target_layer_id, rule_id)`.

### 3.3. `simple_coupling.py`

**File:** `simple_coupling.py`

Provides a basic, example implementation of `InterLayerCouplingLogic`.

*   **`SimpleCoupling(InterLayerCouplingLogic)`**:
    *   `__init__(self, allowed_transitions: Optional[Dict[str, List[str]]] = None)`: Initializes with a dictionary defining allowed transitions. E.g., `{"LayerA": ["LayerB"]}` means transitions from LayerA to LayerB are generally permitted by this logic if other conditions are met.
    *   `get_possible_targets(self, source_node_info: Dict[str, Any], source_layer: PTLLayer, target_layer: PTLLayer) -> List[Dict[str, Any]]`: If the transition between `source_layer` and `target_layer` is in `allowed_transitions`, it proposes the same coordinate in the `target_layer` as a possible target.
    *   `can_traverse(self, source_node_info: Dict[str, Any], target_node_info: Dict[str, Any], source_layer: PTLLayer, target_layer: PTLLayer) -> bool`: Returns `True` if the transition between the layers is generally allowed by the `allowed_transitions` configuration.

### 3.4. `ptl_multiplex_visualizer_v0.py`

**File:** `ptl_multiplex_visualizer_v0.py`

Provides functions to visualize the multiplex PTL.

*   **`SimpleVisualCoupling(InterLayerCouplingLogic)`**: A simplified coupling logic specifically for visualization examples, connecting a node to its counterpart in a specified target layer.
*   **`visualize_multiplex_ptl(manager: MultiplexPTLManager, output_filename="/home/ubuntu/ufrf_project/multiplex_ptl_3d.png")`**: Generates a 3D plot of the entire multiplex PTL managed by the `manager`. Nodes are colored by layer, and inter-layer connections are distinctly visualized. The plot is saved to `output_filename`.
    *   Nodes are positioned based on their PTL coordinates (Domain, Level, System, Cycle), with an additional Z-offset for each layer to provide visual separation.
    *   Intra-layer edges are drawn based on the `PTLModel_v12` connections.
    *   Inter-layer edges are drawn based on the defined coupling rules in the `MultiplexPTLManager`.

## 4. Usage Examples

### 4.1. Setting up the Multiplex PTL Manager

```python
from ptl_multiplex_framework import MultiplexPTLManager
from ptl_model_v12 import PTLCoordinate # Assuming PTLCoordinate is defined
from simple_coupling import SimpleCoupling

# Initialize the manager
manager = MultiplexPTLManager()

# Add PTL layers (each representing a different boundary condition)
layer_alpha = manager.add_layer(boundary_id="Alpha")
layer_beta = manager.add_layer(boundary_id="Beta")

# Populate the PTL models within each layer (example)
# (The PTLModel_v12 instances are created by add_layer, 
# but you need to call their methods to build their internal structure)
ptl_alpha_model = layer_alpha.ptl_instance
ptl_alpha_model.establish_intra_system_connections(domain_id=1, level_id=1, system_id=1)

ptl_beta_model = layer_beta.ptl_instance
ptl_beta_model.establish_intra_system_connections(domain_id=1, level_id=1, system_id=1)

print(f"Manager has layers: {list(manager.layers.keys())}")
```

### 4.2. Defining Inter-Layer Coupling

```python
# Define a simple coupling logic: Alpha can transition to Beta
coupling_logic_ab = SimpleCoupling(allowed_transitions={"Alpha": ["Beta"]})

# Define the rule in the manager
manager.define_coupling_rule(
    rule_id="AlphaToBetaRule",
    source_layer_id="Alpha",
    target_layer_id="Beta",
    coupling_logic=coupling_logic_ab
)

print(f"Coupling rules: {manager.coupling_rules}")
```

### 4.3. Querying Possible Transitions

```python
# Assume a PTLCoordinate exists in Layer Alpha
coord_in_alpha = PTLCoordinate(domain_id=1, level_id=1, system_id=1, cycle_id=5)

# Get possible inter-layer transitions from this coordinate in Layer Alpha
possible_transitions = manager.get_inter_layer_transitions(
    source_node_coordinate=coord_in_alpha,
    source_layer_id="Alpha"
)

if possible_transitions:
    for target_coord, target_layer, rule_id in possible_transitions:
        print(f"Possible transition from {coord_in_alpha} in Alpha to {target_coord} in {target_layer} via rule {rule_id}")
else:
    print(f"No inter-layer transitions found from {coord_in_alpha} in Alpha.")
```

### 4.4. Visualizing the Multiplex PTL

```python
from ptl_multiplex_visualizer_v0 import visualize_multiplex_ptl, SimpleVisualCoupling

# (Assuming manager is set up with layers and populated PTL models as above)
# For visualization, you might use a specific coupling logic for clarity

vis_manager = MultiplexPTLManager()

ptl_A = vis_manager.add_layer("VisA").ptl_instance
ptl_A.establish_intra_system_connections(1,1,1)

ptl_B = vis_manager.add_layer("VisB").ptl_instance
ptl_B.establish_intra_system_connections(1,1,1)

# Use SimpleVisualCoupling (or your custom logic)
coupling_A_to_B_viz = SimpleVisualCoupling(target_layer_id="VisB")
vis_manager.define_coupling_rule("VizRule_A_to_B", "VisA", "VisB", coupling_A_to_B_viz)

# Generate and save the visualization
visualize_multiplex_ptl(vis_manager, output_filename="/home/ubuntu/ufrf_project/my_multiplex_visualization.png")
print("Visualization generated.")
```

## 5. Extending the Framework

### 5.1. Custom PTL Models

While `PTLModel_v12` provides a specific UFRF-aligned structure, the `PTLLayer` can theoretically hold any object that adheres to a minimal PTL model interface (e.g., has `get_node`, `get_neighbors` methods, and a `nodes` attribute if the visualizer is to be used as-is). For deeper integration, ensure your custom model is compatible with `PTLCoordinate` and `PTLNode` concepts or adapt the framework components.

### 5.2. Custom Coupling Logic

The most common extension point will be creating new classes that inherit from `InterLayerCouplingLogic`. This allows for defining sophisticated rules for how transitions between layers occur, potentially based on:

*   Node attributes (e.g., energy levels, states).
*   Probabilistic transitions.
*   Global state of the multiplex system.
*   Specific UFRF theoretical constructs for inter-boundary traversal.

To create a custom coupling logic:

1.  Create a new Python class that inherits from `InterLayerCouplingLogic`.
2.  Implement the `get_possible_targets` method: This method should analyze the `source_node_info`, `source_layer`, and `target_layer` to determine what nodes in the `target_layer` are potential candidates for transition. It should return a list of dictionaries, where each dictionary represents a target node and includes at least its `"coordinate"`.
3.  Implement the `can_traverse` method: This method should take specific `source_node_info`, `target_node_info`, and their respective layers, and return `True` if the transition is allowed by the logic, and `False` otherwise.

Example skeleton for custom logic:

```python
from ptl_multiplex_framework import InterLayerCouplingLogic, PTLLayer
from typing import Dict, List, Any

class MyCustomCoupling(InterLayerCouplingLogic):
    def __init__(self, custom_param: Any):
        super().__init__()
        self.custom_param = custom_param

    def get_possible_targets(self, source_node_info: Dict[str, Any], source_layer: PTLLayer, target_layer: PTLLayer) -> List[Dict[str, Any]]:
        # Implement logic to find potential targets in target_layer
        # based on source_node_info, source_layer, and self.custom_param
        possible = []
        # ... your logic ...
        # if a_target_coordinate is found:
        #     possible.append({"coordinate": a_target_coordinate, "some_attribute": "value"})
        return possible

    def can_traverse(self, source_node_info: Dict[str, Any], target_node_info: Dict[str, Any], source_layer: PTLLayer, target_layer: PTLLayer) -> bool:
        # Implement logic to confirm if transition is allowed
        # based on source, target, layers, and self.custom_param
        # ... your logic ...
        return True # or False
```

## 6. Future Considerations (Quantum PTL Placeholder)

The current framework focuses on the classical multiplex PTL. As per user input, the detailed implementation of Quantum PTL concepts (entanglement, quantum states on nodes) has been deferred.

**Suggestion for later exploration:**

*   **Quantum Node States:** `PTLNode` attributes could be extended to include quantum state representations (e.g., state vectors, density matrices). These could be related to superpositions of enharmonic potentials or other UFRF-specific constructs.
*   **Entanglement:** Coupling logic could be developed to model entanglement between nodes, potentially across different layers. This would require defining how entanglement is established, characterized (e.g., entanglement measures), and how it affects transitions.
*   **Quantum Evolution/Measurement:** The `PTLModel_v12` or a specialized QuantumPTLModel could incorporate mechanisms for state evolution (e.g., applying unitary operators) and measurement, consistent with UFRF theory.
*   The `InterLayerCouplingLogic` could be adapted to handle quantum information transfer or transformation during inter-layer transitions.

This area will require significant theoretical input from UFRF experts to ensure accurate modeling.

## 7. Conclusion

The UFRF Multiplex PTL framework provides a robust and extensible platform for modeling systems with multiple, interacting boundary conditions. Its modular design allows for the integration of custom PTL structures and sophisticated inter-layer coupling mechanisms, paving the way for advanced simulations and explorations within the UFRF paradigm.

