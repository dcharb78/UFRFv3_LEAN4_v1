# ptl_multiplex_visualizer_v0.py
# Author: Daniel Charboneau (via Manus AI Agent)
# Date: May 08, 2025
# Version: 0.1.0

"""
Basic 3D visualization for the UFRF Multiplex PTL framework.
Uses NetworkX for graph representation and Matplotlib for 3D plotting.
"""

import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
import networkx as nx
import random

# Assuming the other PTL files are in the same directory or accessible in PYTHONPATH
# For direct execution, ensure these files are in /home/ubuntu/ufrf_project/
from ptl_multiplex_framework import MultiplexPTLManager, PTLLayer, InterLayerCouplingLogic, PTLModel_v12 as PTLModelFramework # Alias to avoid clash
from ptl_model_v12 import PTLCoordinate, PTLNode, PTLModel_v12, CYCLES_PER_SYSTEM # The actual PTL model

# Define a concrete PTLCoordinate for use if not already available globally
# PTLCoordinate = namedtuple("PTLCoordinate", ["domain_id", "level_id", "system_id", "cycle_id"])

class SimpleVisualCoupling(InterLayerCouplingLogic):
    """Simple coupling for visualization: connects node (d,l,s,c) in layer A to (d,l,s,c) in layer B if they exist."""
    def __init__(self, target_layer_id: str):
        super().__init__()
        self.target_layer_id = target_layer_id

    def get_possible_targets(self, source_node_info: dict, source_layer: PTLLayer, target_layer: PTLLayer) -> list[dict]:
        if target_layer.boundary_id == self.target_layer_id:
            # Try to connect to the same coordinate in the target layer
            # In a real scenario, we would check if target_layer.ptl_instance.nodes.get(source_node_info["coordinate"])
            # For visualization, we assume it might exist for demonstration
            return [{"coordinate": source_node_info["coordinate"], "attributes": {}}]
        return []

    def can_traverse(self, source_node_info: dict, target_node_info: dict, source_layer: PTLLayer, target_layer: PTLLayer) -> bool:
        return target_layer.boundary_id == self.target_layer_id

def visualize_multiplex_ptl(manager: MultiplexPTLManager, output_filename="/home/ubuntu/ufrf_project/multiplex_ptl_3d.png"):
    """Generates and saves a 3D visualization of the multiplex PTL."""
    G = nx.Graph()
    pos = {}
    node_colors = []
    node_labels = {}
    layer_color_map = {}
    
    # Assign colors to layers
    colors = ["r", "g", "b", "y", "c", "m", "orange", "purple", "brown"]
    for i, layer_id in enumerate(manager.layers.keys()):
        layer_color_map[layer_id] = colors[i % len(colors)]

    # Add nodes and intra-layer edges
    for layer_id, ptl_layer in manager.layers.items():
        ptl_instance = ptl_layer.ptl_instance
        layer_z_offset = list(manager.layers.keys()).index(layer_id) * 5 # Offset layers in Z for visibility

        for coord, node_obj in ptl_instance.nodes.items():
            # Define a unique ID for networkx node: (layer_id, domain, level, system, cycle)
            node_id = (layer_id, coord.domain_id, coord.level_id, coord.system_id, coord.cycle_id)
            G.add_node(node_id)
            # Position: map PTLCoordinate to 3D space, with layer offset
            # Simple mapping: domain->x, level->y, system->z_within_layer, cycle->small_offset_or_size
            pos[node_id] = (coord.domain_id * 2, 
                            coord.level_id * 2, 
                            coord.system_id * 2 + layer_z_offset + (coord.cycle_id / CYCLES_PER_SYSTEM * 0.5))
            node_colors.append(layer_color_map[layer_id])
            node_labels[node_id] = f"L:{layer_id[0]}\nC:{coord.cycle_id}"

            # Intra-layer edges
            for neighbor_coord, attrs in node_obj.neighbors.items():
                neighbor_id = (layer_id, neighbor_coord.domain_id, neighbor_coord.level_id, neighbor_coord.system_id, neighbor_coord.cycle_id)
                if G.has_node(neighbor_id): # Ensure neighbor is added if it exists
                    G.add_edge(node_id, neighbor_id, type="intra-layer", color=layer_color_map[layer_id])
    
    # Add inter-layer edges
    for rule in manager.coupling_rules:
        source_layer_id = rule["source_layer_id"]
        target_layer_id = rule["target_layer_id"]
        logic = rule["logic"]
        source_layer = manager.get_layer(source_layer_id)
        target_layer = manager.get_layer(target_layer_id)

        if not source_layer or not target_layer:
            continue

        for source_coord_obj, source_node_obj in source_layer.ptl_instance.nodes.items():
            source_node_id_nx = (source_layer_id, source_coord_obj.domain_id, source_coord_obj.level_id, source_coord_obj.system_id, source_coord_obj.cycle_id)
            source_node_info = {"coordinate": source_coord_obj, "attributes": source_node_obj.attributes}
            
            possible_targets_info = logic.get_possible_targets(source_node_info, source_layer, target_layer)
            for target_info in possible_targets_info:
                target_coord_obj = target_info["coordinate"]
                # Ensure target node exists in the target layer for visualization
                if target_layer.ptl_instance.nodes.get(target_coord_obj):
                    target_node_id_nx = (target_layer_id, target_coord_obj.domain_id, target_coord_obj.level_id, target_coord_obj.system_id, target_coord_obj.cycle_id)
                    if G.has_node(source_node_id_nx) and G.has_node(target_node_id_nx):
                         if logic.can_traverse(source_node_info, target_info, source_layer, target_layer):
                            G.add_edge(source_node_id_nx, target_node_id_nx, type="inter-layer", color="black", weight=2)

    if not G.nodes():
        print("Graph is empty, cannot visualize.")
        return

    # 3D plot
    fig = plt.figure(figsize=(16, 12))
    ax = fig.add_subplot(111, projection="3d")

    # Draw nodes
    x_nodes = [pos[n][0] for n in G.nodes()]
    y_nodes = [pos[n][1] for n in G.nodes()]
    z_nodes = [pos[n][2] for n in G.nodes()]
    ax.scatter(x_nodes, y_nodes, z_nodes, c=node_colors, s=100, alpha=0.7)

    # Draw edges
    for u, v, data in G.edges(data=True):
        x = [pos[u][0], pos[v][0]]
        y = [pos[u][1], pos[v][1]]
        z = [pos[u][2], pos[v][2]]
        edge_color = data.get("color", "gray")
        line_width = 2 if data.get("type") == "inter-layer" else 0.5
        ax.plot(x, y, z, color=edge_color, alpha=0.5, linewidth=line_width)

    # Add labels (can be very cluttered for large graphs)
    # for node, (x,y,z) in pos.items():
    #     ax.text(x, y, z, node_labels[node], size=8, color='k')

    ax.set_xlabel("Domain ID")
    ax.set_ylabel("Level ID")
    ax.set_zlabel("System ID & Layer Offset")
    plt.title("3D Multiplex PTL Visualization")
    plt.savefig(output_filename)
    plt.close(fig)
    print(f"Visualization saved to {output_filename}")

if __name__ == "__main__":
    # Setup a sample Multiplex PTL Manager
    manager = MultiplexPTLManager()

    # Create Layer A
    ptl_A_model = PTLModel_v12(boundary_id="A")
    # Populate PTL A (e.g., one system in one domain/level)
    for s_id in range(1, 2): # System 1
        ptl_A_model.establish_intra_system_connections(domain_id=1, level_id=1, system_id=s_id)
    manager.add_layer(boundary_id="A", ptl_config=None) # The model is passed via PTLLayer constructor in framework
    # Manually assign the created model to the layer for this script's direct use
    manager.get_layer("A").ptl_instance = ptl_A_model 

    # Create Layer B
    ptl_B_model = PTLModel_v12(boundary_id="B")
    for s_id in range(1, 2): # System 1
        ptl_B_model.establish_intra_system_connections(domain_id=1, level_id=1, system_id=s_id)
    manager.add_layer(boundary_id="B", ptl_config=None)
    manager.get_layer("B").ptl_instance = ptl_B_model
    
    # Define coupling rule: A -> B for corresponding nodes
    coupling_A_to_B = SimpleVisualCoupling(target_layer_id="B")
    manager.define_coupling_rule("A_to_B_viz", "A", "B", coupling_A_to_B)

    # Define coupling rule: B -> A for corresponding nodes
    coupling_B_to_A = SimpleVisualCoupling(target_layer_id="A")
    manager.define_coupling_rule("B_to_A_viz", "B", "A", coupling_B_to_A)

    visualize_multiplex_ptl(manager)

    # Example with a slightly more complex structure
    manager_complex = MultiplexPTLManager()
    ptl_X_model = PTLModel_v12(boundary_id="X")
    ptl_X_model.establish_intra_system_connections(1,1,1)
    ptl_X_model.establish_intra_system_connections(1,1,2)
    ptl_X_model.establish_inter_system_transition(1,1,1)
    manager_complex.add_layer("X")
    manager_complex.get_layer("X").ptl_instance = ptl_X_model

    ptl_Y_model = PTLModel_v12(boundary_id="Y")
    ptl_Y_model.establish_intra_system_connections(1,1,1)
    manager_complex.add_layer("Y")
    manager_complex.get_layer("Y").ptl_instance = ptl_Y_model

    coupling_X_to_Y = SimpleVisualCoupling(target_layer_id="Y")
    manager_complex.define_coupling_rule("X_to_Y_complex", "X", "Y", coupling_X_to_Y)
    visualize_multiplex_ptl(manager_complex, "/home/ubuntu/ufrf_project/multiplex_ptl_3d_complex.png")

