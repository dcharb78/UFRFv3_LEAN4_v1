# test_multiplex_ptl_suite.py
# Author: Daniel Charboneau (via Manus AI Agent)
# Date: May 08, 2025
# Version: 1.0.0

"""
Test suite for the UFRF Multiplex PTL framework.
This script tests the integration and functionality of:
- ptl_multiplex_framework.py
- ptl_model_v12.py
- simple_coupling.py (as a concrete InterLayerCouplingLogic)
- ptl_multiplex_visualizer_v0.py
"""

import os
import unittest

# Ensure the project directory is in the Python path for imports
import sys
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), ".")))

from ptl_multiplex_framework import MultiplexPTLManager, PTLLayer, PTLModelFramework # Alias for PTLModel_v12 in framework
from ptl_model_v12 import PTLModel_v12, PTLCoordinate, PTLNode, CYCLES_PER_SYSTEM
from simple_coupling import SimpleCoupling # Assumed to be in the same directory or accessible
from ptl_multiplex_visualizer_v0 import visualize_multiplex_ptl, SimpleVisualCoupling

class TestMultiplexPTLFramework(unittest.TestCase):

    def setUp(self):
        """Set up for each test method."""
        self.manager = MultiplexPTLManager()
        self.output_dir = "/home/ubuntu/ufrf_project/test_outputs"
        os.makedirs(self.output_dir, exist_ok=True)

    def test_01_ptl_model_v12_creation_and_population(self):
        print("\nRunning test_01_ptl_model_v12_creation_and_population...")
        ptl_model = PTLModel_v12(boundary_id="TestBoundary1")
        self.assertEqual(ptl_model.boundary_id, "TestBoundary1")
        ptl_model.establish_intra_system_connections(domain_id=1, level_id=1, system_id=1)
        # Expect 13 nodes for one system
        self.assertEqual(len(ptl_model.nodes), CYCLES_PER_SYSTEM)
        c1_coord = PTLCoordinate(1,1,1,1)
        self.assertIn(c1_coord, ptl_model.nodes)
        print("test_01_ptl_model_v12_creation_and_population: PASSED")

    def test_02_multiplex_manager_add_get_remove_layer(self):
        print("\nRunning test_02_multiplex_manager_add_get_remove_layer...")
        self.manager.add_layer(boundary_id="LayerAlpha")
        layer_alpha = self.manager.get_layer("LayerAlpha")
        self.assertIsNotNone(layer_alpha)
        self.assertEqual(layer_alpha.boundary_id, "LayerAlpha")
        self.assertIsInstance(layer_alpha.ptl_instance, PTLModelFramework) # Checks against the alias used in framework
        
        # Test adding a PTLModel_v12 instance directly to the layer for population
        # (as the framework add_layer creates a new PTLModelFramework stub)
        actual_ptl_model = PTLModel_v12(boundary_id="LayerAlpha")
        actual_ptl_model.establish_intra_system_connections(1,1,1)
        layer_alpha.ptl_instance = actual_ptl_model # Replace stub with populated model
        self.assertEqual(len(layer_alpha.ptl_instance.nodes), CYCLES_PER_SYSTEM)

        removed = self.manager.remove_layer("LayerAlpha")
        self.assertTrue(removed)
        self.assertIsNone(self.manager.get_layer("LayerAlpha"))
        print("test_02_multiplex_manager_add_get_remove_layer: PASSED")

    def test_03_simple_coupling_logic(self):
        print("\nRunning test_03_simple_coupling_logic...")
        # Create dummy layers for testing coupling logic (not added to manager here)
        ptl_model_A = PTLModel_v12("A")
        ptl_model_B = PTLModel_v12("B")
        layer_A_dummy = PTLLayer("A", PTLModelFramework("A")) # Use framework's PTLModel for type consistency
        layer_A_dummy.ptl_instance = ptl_model_A # Assign actual model
        layer_B_dummy = PTLLayer("B", PTLModelFramework("B"))
        layer_B_dummy.ptl_instance = ptl_model_B

        coupling_config = {"A": ["B"]}
        coupling = SimpleCoupling(allowed_transitions=coupling_config)
        
        source_coord = PTLCoordinate(1,1,1,1)
        ptl_model_A.get_or_create_node(source_coord) # Ensure node exists in dummy model A
        source_node_info = {"coordinate": source_coord}

        targets = coupling.get_possible_targets(source_node_info, layer_A_dummy, layer_B_dummy)
        self.assertEqual(len(targets), 1)
        self.assertEqual(targets[0]["coordinate"], source_coord)
        self.assertEqual(targets[0]["layer_id"], "B")
        self.assertTrue(coupling.can_traverse(source_node_info, targets[0], layer_A_dummy, layer_B_dummy))
        print("test_03_simple_coupling_logic: PASSED")

    def test_04_manager_define_and_get_inter_layer_transitions(self):
        print("\nRunning test_04_manager_define_and_get_inter_layer_transitions...")
        self.manager.add_layer("LayerX")
        self.manager.add_layer("LayerY")
        
        # Populate the actual PTL models within the layers
        layer_x_ptl = PTLModel_v12("LayerX")
        layer_x_ptl.establish_intra_system_connections(1,1,1)
        self.manager.get_layer("LayerX").ptl_instance = layer_x_ptl

        layer_y_ptl = PTLModel_v12("LayerY")
        layer_y_ptl.establish_intra_system_connections(1,1,1) # Same structure for simplicity
        self.manager.get_layer("LayerY").ptl_instance = layer_y_ptl

        coupling_logic_xy = SimpleCoupling(allowed_transitions={"LayerX": ["LayerY"]})
        self.manager.define_coupling_rule("X_to_Y", "LayerX", "LayerY", coupling_logic_xy)

        source_coord = PTLCoordinate(1,1,1,5) # A node that exists in LayerX
        transitions = self.manager.get_inter_layer_transitions(source_coord, "LayerX")
        self.assertEqual(len(transitions), 1)
        target_coord, target_layer_id, rule_id = transitions[0]
        self.assertEqual(target_coord, source_coord) # SimpleCoupling maps to same coord
        self.assertEqual(target_layer_id, "LayerY")
        self.assertEqual(rule_id, "X_to_Y")
        print("test_04_manager_define_and_get_inter_layer_transitions: PASSED")

    def test_05_visualization_output(self):
        print("\nRunning test_05_visualization_output...")
        # Setup a manager with some layers and coupling for visualization
        viz_manager = MultiplexPTLManager()
        ptl_A_model = PTLModel_v12(boundary_id="VisA")
        ptl_A_model.establish_intra_system_connections(1,1,1)
        viz_manager.add_layer("VisA")
        viz_manager.get_layer("VisA").ptl_instance = ptl_A_model

        ptl_B_model = PTLModel_v12(boundary_id="VisB")
        ptl_B_model.establish_intra_system_connections(1,1,1) # Same system for simplicity
        viz_manager.add_layer("VisB")
        viz_manager.get_layer("VisB").ptl_instance = ptl_B_model

        # Use SimpleVisualCoupling from the visualizer script for consistency
        coupling_A_to_B = SimpleVisualCoupling(target_layer_id="VisB")
        viz_manager.define_coupling_rule("VisA_to_VisB", "VisA", "VisB", coupling_A_to_B)

        output_image_path = os.path.join(self.output_dir, "test_visualization.png")
        visualize_multiplex_ptl(viz_manager, output_filename=output_image_path)
        self.assertTrue(os.path.exists(output_image_path))
        print(f"test_05_visualization_output: PASSED (Image generated at {output_image_path})")

    def test_06_full_integration_complex_visualization(self):
        print("\nRunning test_06_full_integration_complex_visualization...")
        manager_complex = MultiplexPTLManager()
        
        ptl_X_model = PTLModel_v12(boundary_id="ComplexX")
        ptl_X_model.establish_intra_system_connections(1,1,1)
        ptl_X_model.establish_intra_system_connections(1,1,2)
        ptl_X_model.establish_inter_system_transition(1,1,1) # D1:L1:S1 -> D1:L1:S2
        manager_complex.add_layer("ComplexX")
        manager_complex.get_layer("ComplexX").ptl_instance = ptl_X_model

        ptl_Y_model = PTLModel_v12(boundary_id="ComplexY")
        ptl_Y_model.establish_intra_system_connections(1,1,1) # Only one system in Y
        manager_complex.add_layer("ComplexY")
        manager_complex.get_layer("ComplexY").ptl_instance = ptl_Y_model
        
        ptl_Z_model = PTLModel_v12(boundary_id="ComplexZ")
        ptl_Z_model.establish_intra_system_connections(1,2,1) # Different level
        manager_complex.add_layer("ComplexZ")
        manager_complex.get_layer("ComplexZ").ptl_instance = ptl_Z_model

        coupling_X_to_Y = SimpleVisualCoupling(target_layer_id="ComplexY")
        manager_complex.define_coupling_rule("X_to_Y_cplx", "ComplexX", "ComplexY", coupling_X_to_Y)
        
        coupling_Y_to_Z = SimpleVisualCoupling(target_layer_id="ComplexZ")
        manager_complex.define_coupling_rule("Y_to_Z_cplx", "ComplexY", "ComplexZ", coupling_Y_to_Z)

        output_image_path_complex = os.path.join(self.output_dir, "test_visualization_complex.png")
        visualize_multiplex_ptl(manager_complex, output_filename=output_image_path_complex)
        self.assertTrue(os.path.exists(output_image_path_complex))
        print(f"test_06_full_integration_complex_visualization: PASSED (Image generated at {output_image_path_complex})")

if __name__ == "__main__":
    print("Starting UFRF Multiplex PTL Test Suite...")
    # Ensure PTLCoordinate is available if visualizer or other modules need it directly
    # This is a bit of a hack for standalone execution; ideally, imports handle this.
    if "PTLCoordinate" not in globals():
        from collections import namedtuple
        PTLCoordinate = namedtuple("PTLCoordinate", ["domain_id", "level_id", "system_id", "cycle_id"])
        CYCLES_PER_SYSTEM = 13 # Make sure this is defined if visualizer uses it directly

    unittest.main()

