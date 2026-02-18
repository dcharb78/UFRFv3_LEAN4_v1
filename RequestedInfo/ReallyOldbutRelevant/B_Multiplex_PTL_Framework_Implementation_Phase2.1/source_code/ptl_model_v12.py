#!/usr/bin/env python3
# ptl_model_v12.py
# Author: Daniel Charboneau (via Manus AI Agent)
# Date: May 08, 2025
# Version: 12.0.0

"""
Represents the UFRF Positional Transition Lattice (PTL) model for a single boundary condition.
Adapted from ptl_model.py (assumed v11) for use within the Multiplex PTL Framework.
Key changes:
  - PTLattice class now accepts a boundary_id during initialization.
  - Designed to be instantiable multiple times for different layers.
"""

import json
from collections import namedtuple
from typing import Dict, List, Tuple, Any, Optional # Added for clarity

# Define the PTL coordinate structure as a named tuple for clarity and immutability
PTLCoordinate = namedtuple("PTLCoordinate", ["domain_id", "level_id", "system_id", "cycle_id"])

# UFRF Hierarchical Constants (as per design document)
CYCLES_PER_SYSTEM = 13
SYSTEMS_PER_LEVEL = 13
LEVELS_PER_DOMAIN = 13 # Assuming 13 for now, can be configured

# Default Structural Costs (Pathfinder will apply UFRF-specific costs based on type)
DEFAULT_STRUCTURAL_COST = 1.0
INTER_SYSTEM_TRANSITION_DEFAULT_COST = 1.0 
INTER_LEVEL_TRANSITION_DEFAULT_COST = 1.0 
INTER_DOMAIN_TRANSITION_DEFAULT_COST = 1.0

class PTLNode:
    """Represents a node in the Pascal-Tetrahedral Lattice (PTL).
    A node corresponds to a "Seed Tetrahedron" unit, which encapsulates a UFRF Cycle.
    """
    def __init__(self, coordinate: PTLCoordinate, ufrf_mapping_data: Optional[Dict[str, Any]] = None):
        if not isinstance(coordinate, PTLCoordinate):
            raise TypeError("Coordinate must be a PTLCoordinate named tuple.")
        self.coordinate: PTLCoordinate = coordinate # (domain_id, level_id, system_id, cycle_id)
        self.ufrf_mapping_data: Dict[str, Any] = ufrf_mapping_data if ufrf_mapping_data else {}
        self.attributes: Dict[str, Any] = {} # For PTL-specific attributes (e.g., geometric properties, state)
        self.neighbors: Dict[PTLCoordinate, Dict[str, Any]] = {} 

    def __repr__(self) -> str:
        return f"PTLNode(D={self.coordinate.domain_id}, L={self.coordinate.level_id}, S={self.coordinate.system_id}, C={self.coordinate.cycle_id})"

    def __eq__(self, other: Any) -> bool:
        if isinstance(other, PTLNode):
            return self.coordinate == other.coordinate
        return False

    def __hash__(self) -> int:
        return hash(self.coordinate)

    def to_dict(self) -> Dict[str, Any]:
        serialized_neighbors = { 
            str(n_coord): attr 
            for n_coord, attr in self.neighbors.items()
        }
        return {
            "coordinate": self.coordinate._asdict(),
            "ufrf_mapping_data": self.ufrf_mapping_data,
            "attributes": self.attributes,
            "neighbors": serialized_neighbors
        }

class PTLModel_v12: # Renamed PTLattice to PTLModel_v12 for consistency with framework design
    """Represents the Pascal-Tetrahedral Lattice for a specific boundary condition.
    This class manages PTL nodes and their relationships within that boundary.
    """
    def __init__(self, boundary_id: str, config: Optional[Dict[str, Any]] = None):
        if not isinstance(boundary_id, str) or not boundary_id:
            raise ValueError("boundary_id must be a non-empty string.")
            
        self.boundary_id: str = boundary_id
        self.config: Dict[str, Any] = config if config else {}
        self.nodes: Dict[PTLCoordinate, PTLNode] = {} # Store nodes by their PTLCoordinate
        
        # Configuration for hierarchy can be overridden by config if needed
        self.cycles_per_system: int = self.config.get("cycles_per_system", CYCLES_PER_SYSTEM)
        self.systems_per_level: int = self.config.get("systems_per_level", SYSTEMS_PER_LEVEL)
        self.levels_per_domain: int = self.config.get("levels_per_domain", LEVELS_PER_DOMAIN)
        print(f"PTLModel_v12 initialized for boundary: {self.boundary_id} with config: {self.config}")

    def get_or_create_node(self, coordinate: PTLCoordinate, ufrf_mapping_data: Optional[Dict[str, Any]] = None) -> PTLNode:
        if isinstance(coordinate, dict) and all(k in coordinate for k in PTLCoordinate._fields):
            coordinate = PTLCoordinate(**coordinate)
        elif not isinstance(coordinate, PTLCoordinate):
            raise TypeError("Coordinate must be a PTLCoordinate or a compatible dict.")

        if coordinate not in self.nodes:
            self.nodes[coordinate] = PTLNode(coordinate, ufrf_mapping_data)
        elif ufrf_mapping_data:
            if self.nodes[coordinate].ufrf_mapping_data:
                 self.nodes[coordinate].ufrf_mapping_data.update(ufrf_mapping_data)
            else:
                 self.nodes[coordinate].ufrf_mapping_data = ufrf_mapping_data
        return self.nodes[coordinate]

    def add_connection(self, coord1: PTLCoordinate, coord2: PTLCoordinate, attributes: Optional[Dict[str, Any]] = None, two_way: bool = True):
        node1 = self.get_or_create_node(coord1)
        node2 = self.get_or_create_node(coord2)
        
        conn_attributes = attributes if attributes is not None else {}
        if "cost" not in conn_attributes: # Add default structural cost if not specified
            conn_attributes["cost"] = DEFAULT_STRUCTURAL_COST 

        if coord2 not in node1.neighbors:
            node1.neighbors[coord2] = conn_attributes.copy()
        else: 
            node1.neighbors[coord2].update(conn_attributes)
            
        if two_way:
            reverse_conn_attributes = conn_attributes.copy()
            if coord1 not in node2.neighbors:
                node2.neighbors[coord1] = reverse_conn_attributes
            else: 
                node2.neighbors[coord1].update(reverse_conn_attributes)

    def find_neighbors(self, node_coord: PTLCoordinate) -> List[PTLCoordinate]:
        if node_coord not in self.nodes:
            return []
        node = self.nodes[node_coord]
        return list(node.neighbors.keys())

    def get_connection_attributes(self, coord1: PTLCoordinate, coord2: PTLCoordinate) -> Optional[Dict[str, Any]]:
        if coord1 in self.nodes and coord2 in self.nodes[coord1].neighbors:
            return self.nodes[coord1].neighbors[coord2]
        return None

    def establish_intra_system_connections(self, domain_id: int, level_id: int, system_id: int):
        # Ensure all 13 cycle nodes exist for the system
        for i in range(1, self.cycles_per_system + 1):
            self.get_or_create_node(PTLCoordinate(domain_id, level_id, system_id, i))

        # UFRF Library Phase Definitions:
        # Seed Phase: Positions 1-3
        # Amplify Phase: Positions 4-6
        # Harmonize Phase: Positions 7-9
        # Transition: Position 10 (Rest)
        # New Seed Phase: Positions 11-13

        # 1. Primary Flow Path (C1->C2...->C9->C10 and C10->C11->C12->C13)
        for i in range(1, self.cycles_per_system): # C1 to C12, connecting to C2 to C13
            if i == 10 and (i + 1) == 11: # C10 -> C11 (start of New Seed from Transition)
                 pass 
            elif i == 9 and (i+1) == 10: # C9 -> C10 (into Transition/Rest)
                 pass 
            elif (i+1) == 1: 
                continue
            
            source_coord = PTLCoordinate(domain_id, level_id, system_id, i)
            target_coord = PTLCoordinate(domain_id, level_id, system_id, i + 1)
            attrs = {"type": "primary_flow"} 
            self.add_connection(source_coord, target_coord, attributes=attrs, two_way=False)
            reverse_attrs = {"type": "primary_flow_reverse_traversal"}
            self.add_connection(target_coord, source_coord, attributes=reverse_attrs, two_way=False)
        
        # 2. Reset Flow (C10 to C1 of the same system)
        c10_coord = PTLCoordinate(domain_id, level_id, system_id, 10)
        c1_coord = PTLCoordinate(domain_id, level_id, system_id, 1)
        self.add_connection(c10_coord, c1_coord, attributes={"type": "reset_flow"}, two_way=False)

        # 3. Seed Influence Connections (C1 to Amplify Phase C4, C5, C6 - two-way)
        seed_pos_1 = PTLCoordinate(domain_id, level_id, system_id, 1)
        amplify_phase_cycles = [4, 5, 6]
        for target_cycle_id in amplify_phase_cycles:
            target_coord = PTLCoordinate(domain_id, level_id, system_id, target_cycle_id)
            self.add_connection(seed_pos_1, target_coord, attributes={"type": "seed_influence"}, two_way=True)

        # 4. Intra-Phase Connections (two-way)
        phase_definitions = {
            "intra_phase_seed": [1, 2, 3],
            "intra_phase_amplify": [4, 5, 6],
            "intra_phase_harmonize": [7, 8, 9],
            "intra_phase_new_seed": [11, 12, 13]
        }

        for phase_type, cycle_ids in phase_definitions.items():
            for i in range(len(cycle_ids)):
                for j in range(i + 1, len(cycle_ids)):
                    coord_a = PTLCoordinate(domain_id, level_id, system_id, cycle_ids[i])
                    coord_b = PTLCoordinate(domain_id, level_id, system_id, cycle_ids[j])
                    self.add_connection(coord_a, coord_b, attributes={"type": phase_type}, two_way=True)

    def establish_inter_system_transition(self, domain_id: int, level_id: int, source_system_id: int):
        if not (1 <= source_system_id < self.systems_per_level):
            return
        target_system_id = source_system_id + 1
        source_node_coord = PTLCoordinate(domain_id, level_id, source_system_id, self.cycles_per_system) 
        target_node_coord = PTLCoordinate(domain_id, level_id, target_system_id, 1)
        self.get_or_create_node(source_node_coord) 
        self.get_or_create_node(target_node_coord)
        attrs = {"type": "inter_system_seed_transition", "cost": INTER_SYSTEM_TRANSITION_DEFAULT_COST}
        self.add_connection(source_node_coord, target_node_coord, attributes=attrs, two_way=False)

    def establish_inter_level_transition(self, domain_id: int, source_level_id: int, direction: str = "up"):
        if direction == "up":
            if not (1 <= source_level_id < self.levels_per_domain):
                return
            target_level_id = source_level_id + 1
            source_system_id = self.systems_per_level 
            source_cycle_id = self.cycles_per_system   
            target_system_id = 1                       
            target_cycle_id = 1                        
        elif direction == "down":
            if not (1 < source_level_id <= self.levels_per_domain):
                return
            target_level_id = source_level_id - 1
            source_system_id = 1
            source_cycle_id = 1
            target_system_id = self.systems_per_level
            target_cycle_id = self.cycles_per_system
        else:
            raise ValueError("Direction must be 'up' or 'down'.")

        source_coord = PTLCoordinate(domain_id, source_level_id, source_system_id, source_cycle_id)
        target_coord = PTLCoordinate(domain_id, target_level_id, target_system_id, target_cycle_id)
        self.get_or_create_node(source_coord)
        self.get_or_create_node(target_coord)
        attrs = {"type": f"inter_level_transition_{direction}", "cost": INTER_LEVEL_TRANSITION_DEFAULT_COST}
        self.add_connection(source_coord, target_coord, attributes=attrs, two_way=False) 

    def establish_inter_domain_transition(self, source_domain_id: int, direction: str = "up"):
        # Assuming domains are linearly ordered for now
        # This might need more complex logic based on UFRF theory for domain topology
        if direction == "up":
            target_domain_id = source_domain_id + 1
            source_level_id = self.levels_per_domain    
            source_system_id = self.systems_per_level 
            source_cycle_id = self.cycles_per_system   
            target_level_id = 1                       
            target_system_id = 1                       
            target_cycle_id = 1                        
        elif direction == "down":
            if source_domain_id <= 1: 
                return
            target_domain_id = source_domain_id - 1
            source_level_id = 1
            source_system_id = 1
            source_cycle_id = 1
            target_level_id = self.levels_per_domain
            target_system_id = self.systems_per_level
            target_cycle_id = self.cycles_per_system
        else:
            raise ValueError("Direction must be 'up' or 'down'.")

        source_coord = PTLCoordinate(source_domain_id, source_level_id, source_system_id, source_cycle_id)
        target_coord = PTLCoordinate(target_domain_id, target_level_id, target_system_id, target_cycle_id)
        self.get_or_create_node(source_coord)
        self.get_or_create_node(target_coord)
        attrs = {"type": f"inter_domain_transition_{direction}", "cost": INTER_DOMAIN_TRANSITION_DEFAULT_COST}
        self.add_connection(source_coord, target_coord, attributes=attrs, two_way=False)

    def to_json_str(self, pretty: bool = True) -> str:
        serialized_nodes = { 
            # Convert PTLCoordinate to a string representation for JSON keys if necessary
            # For now, assuming the PTLCoordinate namedtuple can be stringified by the caller if needed for dict keys
            # Or, if PTLCoordinate is complex, ensure it's serializable or use a string version of it as key here.
            # Using str(ptl_coord) might be too verbose. Let's assume PTLCoordinate can be a key in a dict that json.dumps handles.
            # For robust JSON, keys should be strings. Let's make it explicit.
            f"{ptl_coord.domain_id}_{ptl_coord.level_id}_{ptl_coord.system_id}_{ptl_coord.cycle_id}": node.to_dict() 
            for ptl_coord, node in self.nodes.items()
        }
        return json.dumps(
            {
                "boundary_id": self.boundary_id,
                "config": self.config,
                "nodes": serialized_nodes
            },
            indent=4 if pretty else None,
            default=str # Handles any non-standard types if they sneak in
        )

# --- Main execution block for conceptual testing (can be removed or kept for standalone testing) ---
def main():
    print("PTL Model v12 (Intra-System Connections v2.0 - Python)")
    ptl_boundary_A = PTLModel_v12(boundary_id="BoundaryA")

    d_id, l_id, s_id = 1, 1, 1
    ptl_boundary_A.establish_intra_system_connections(d_id, l_id, s_id)
    print(f"Established intra-system connections for D{d_id}:L{l_id}:S{s_id} in {ptl_boundary_A.boundary_id}")

    c1_node_coord = PTLCoordinate(d_id, l_id, s_id, 1)
    if c1_node_coord in ptl_boundary_A.nodes:
        print(f"Neighbors of {c1_node_coord} in {ptl_boundary_A.boundary_id}:")
        for neighbor_coord, attributes in ptl_boundary_A.nodes[c1_node_coord].neighbors.items():
            print(f"  -> {neighbor_coord} (Type: {attributes.get('type')})")
    
    ptl_boundary_B = PTLModel_v12(boundary_id="BoundaryB", config={"cycles_per_system": 10})
    ptl_boundary_B.establish_intra_system_connections(d_id,l_id,s_id)
    print(f"Established intra-system connections for D{d_id}:L{l_id}:S{s_id} in {ptl_boundary_B.boundary_id} (10 cycles/system)")
    c1_node_coord_b = PTLCoordinate(d_id, l_id, s_id, 1)
    if c1_node_coord_b in ptl_boundary_B.nodes:
        print(f"Neighbors of {c1_node_coord_b} in {ptl_boundary_B.boundary_id}:")
        for neighbor_coord, attributes in ptl_boundary_B.nodes[c1_node_coord_b].neighbors.items():
            print(f"  -> {neighbor_coord} (Type: {attributes.get('type')})")

    # print(ptl_boundary_A.to_json_str())

if __name__ == "__main__":
    main()

