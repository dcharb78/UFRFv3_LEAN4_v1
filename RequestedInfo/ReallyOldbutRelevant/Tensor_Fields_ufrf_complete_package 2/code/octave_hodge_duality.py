import numpy as np
from .differential_geometry_core import DifferentialGeometryCore

class OctaveHodgeDuality:
    """
    Implements Hodge duality between inner and outer octaves.
    
    Author: Daniel Charboneau
    License: Creative Commons Attribution-NonCommercial 4.0 International
    """
    
    def __init__(self, dimensional_base=13):
        """
        Initialize the octave Hodge duality calculator.
        
        Args:
            dimensional_base: Base for dimensional calculations (default: 13)
        """
        self.dimensional_base = dimensional_base
        self.dg_core = DifferentialGeometryCore(dimensional_base)
        self.phi = (1 + np.sqrt(5)) / 2  # Golden ratio
        
        # Define inner and outer octave positions
        self.inner_octave = [4, 5, 6, 7, 8, 9]
        self.outer_octave = [1, 2, 3, 10, 11, 12, 13]
        
        # Initialize duality mappings
        self.initialize_duality_mappings()
    
    def initialize_duality_mappings(self):
        """Initialize the duality mappings between inner and outer octave positions."""
        # Create mapping from inner to outer octave
        self.inner_to_outer = {
            4: 3,    # Inner position 4 maps to outer position 3
            5: 2,    # Inner position 5 maps to outer position 2
            6: 1,    # Inner position 6 maps to outer position 1
            7: 13,   # Inner position 7 maps to outer position 13
            8: 12,   # Inner position 8 maps to outer position 12
            9: 11    # Inner position 9 maps to outer position 11
            # Position 10 is considered part of the outer octave
        }
        
        # Create mapping from outer to inner octave
        self.outer_to_inner = {
            1: 6,    # Outer position 1 maps to inner position 6
            2: 5,    # Outer position 2 maps to inner position 5
            3: 4,    # Outer position 3 maps to inner position 4
            10: None,  # Outer position 10 has no direct inner mapping
            11: 9,   # Outer position 11 maps to inner position 9
            12: 8,   # Outer position 12 maps to inner position 8
            13: 7    # Outer position 13 maps to inner position 7
        }
    
    def calculate_hodge_dual_position(self, position, boundary):
        """
        Calculate the Hodge dual position for a given position.
        
        Args:
            position: Position within boundary (1-13)
            boundary: Boundary number (1+)
            
        Returns:
            Dual position within the same boundary
        """
        # Check if position is in inner or outer octave
        if position in self.inner_octave:
            # Inner to outer mapping
            dual_position = self.inner_to_outer[position]
        elif position in self.outer_octave:
            # Outer to inner mapping
            dual_position = self.outer_to_inner[position]
            if dual_position is None:
                # Position 10 maps to the average of positions 6 and 7
                dual_position = 6.5
        else:
            # Invalid position
            dual_position = position
        
        return dual_position
    
    def calculate_hodge_dual_boundary(self, boundary):
        """
        Calculate the Hodge dual boundary for a given boundary.
        
        Args:
            boundary: Boundary number (1+)
            
        Returns:
            Dual boundary number
        """
        # Dual boundary is related to original boundary by golden ratio
        # For simplicity, we use the nearest boundary to the golden ratio multiple
        dual_boundary = int(round(boundary * self.phi))
        
        return max(1, dual_boundary)
    
    def calculate_hodge_dual_point(self, position, boundary):
        """
        Calculate the Hodge dual point (position and boundary).
        
        Args:
            position: Position within boundary (1-13)
            boundary: Boundary number (1+)
            
        Returns:
            Tuple of (dual_position, dual_boundary)
        """
        dual_position = self.calculate_hodge_dual_position(position, boundary)
        dual_boundary = self.calculate_hodge_dual_boundary(boundary)
        
        return (dual_position, dual_boundary)
    
    def calculate_hodge_star_operator(self, position, boundary):
        """
        Calculate the Hodge star operator at a given position and boundary.
        
        Args:
            position: Position within boundary (1-13)
            boundary: Boundary number (1+)
            
        Returns:
            2x2 matrix representing the Hodge star operator
        """
        # Get metric tensor
        metric = self.dg_core.create_metric_tensor(position, boundary)
        
        # Calculate metric determinant
        g_det = np.linalg.det(metric)
        
        # Levi-Civita symbol in 2D
        epsilon = np.zeros((2, 2))
        epsilon[0, 1] = 1
        epsilon[1, 0] = -1
        
        # Calculate Hodge star operator
        hodge_star = np.zeros((2, 2))
        for i in range(2):
            for j in range(2):
                for k in range(2):
                    for l in range(2):
                        hodge_star[i, j] += epsilon[i, j] * epsilon[k, l] * metric[k, l] / np.sqrt(g_det)
        
        return hodge_star
    
    def calculate_duality_coherence(self, position1, boundary1, position2, boundary2):
        """
        Calculate coherence between a point and its dual.
        
        Args:
            position1: Position in first boundary (1-13)
            boundary1: First boundary number (1+)
            position2: Position in second boundary (1-13)
            boundary2: Second boundary number (1+)
            
        Returns:
            Duality coherence value (0-1)
        """
        # Calculate dual points
        dual_position1, dual_boundary1 = self.calculate_hodge_dual_point(position1, boundary1)
        dual_position2, dual_boundary2 = self.calculate_hodge_dual_point(position2, boundary2)
        
        # Calculate Riemann tensors
        riemann1 = self.dg_core.calculate_riemann_tensor(int(round(position1)), boundary1)
        riemann2 = self.dg_core.calculate_riemann_tensor(int(round(position2)), boundary2)
        dual_riemann1 = self.dg_core.calculate_riemann_tensor(int(round(dual_position1)), dual_boundary1)
        dual_riemann2 = self.dg_core.calculate_riemann_tensor(int(round(dual_position2)), dual_boundary2)
        
        # Calculate tensor similarities
        direct_similarity = self._calculate_tensor_similarity(riemann1, riemann2)
        dual_similarity = self._calculate_tensor_similarity(dual_riemann1, dual_riemann2)
        cross_similarity1 = self._calculate_tensor_similarity(riemann1, dual_riemann2)
        cross_similarity2 = self._calculate_tensor_similarity(riemann2, dual_riemann1)
        
        # Calculate duality coherence
        duality_coherence = 0.4 * direct_similarity + 0.4 * dual_similarity + 0.1 * cross_similarity1 + 0.1 * cross_similarity2
        
        return duality_coherence
    
    def _calculate_tensor_similarity(self, tensor1, tensor2):
        """
        Calculate similarity between two tensors.
        
        Args:
            tensor1: First tensor
            tensor2: Second tensor
            
        Returns:
            Similarity value (0-1)
        """
        # Calculate Frobenius norm of difference
        diff_norm = np.sqrt(np.sum((tensor1 - tensor2)**2))
        
        # Calculate Frobenius norms of individual tensors
        norm1 = np.sqrt(np.sum(tensor1**2))
        norm2 = np.sqrt(np.sum(tensor2**2))
        
        # Avoid division by zero
        if norm1 == 0 or norm2 == 0:
            return 0.0
        
        # Calculate similarity (1 for identical tensors, decreasing as difference increases)
        similarity = 1.0 / (1.0 + diff_norm / (norm1 + norm2))
        
        return similarity
    
    def calculate_inner_outer_duality_coherence(self, boundary1, boundary2):
        """
        Calculate duality coherence between inner and outer octaves across boundaries.
        
        Args:
            boundary1: First boundary number (1+)
            boundary2: Second boundary number (1+)
            
        Returns:
            Dictionary of duality coherence values
        """
        # Calculate coherence for inner octave positions
        inner_coherences = []
        for pos in self.inner_octave:
            dual_pos = self.inner_to_outer[pos]
            coherence = self.calculate_duality_coherence(pos, boundary1, dual_pos, boundary2)
            inner_coherences.append(coherence)
        
        # Calculate coherence for outer octave positions
        outer_coherences = []
        for pos in self.outer_octave:
            if pos != 10:  # Skip position 10 which has no direct mapping
                dual_pos = self.outer_to_inner[pos]
                coherence = self.calculate_duality_coherence(pos, boundary1, dual_pos, boundary2)
                outer_coherences.append(coherence)
        
        # Calculate average coherences
        inner_avg = sum(inner_coherences) / len(inner_coherences) if inner_coherences else 0
        outer_avg = sum(outer_coherences) / len(outer_coherences) if outer_coherences else 0
        overall_avg = (inner_avg + outer_avg) / 2
        
        return {
            'inner_to_outer': inner_avg,
            'outer_to_inner': outer_avg,
            'overall': overall_avg
        }
    
    def calculate_duality_coherence_matrix(self, max_boundary=3):
        """
        Calculate duality coherence matrix for all positions across multiple boundaries.
        
        Args:
            max_boundary: Maximum boundary to consider (default: 3)
            
        Returns:
            3D numpy array of duality coherence values [position, boundary1, boundary2]
        """
        # Initialize coherence matrix
        coherence_matrix = np.zeros((self.dimensional_base, max_boundary, max_boundary))
        
        # Calculate coherence for all position-boundary combinations
        for pos in range(1, self.dimensional_base + 1):
            dual_pos = self.calculate_hodge_dual_position(pos, 1)
            for b1 in range(1, max_boundary + 1):
                for b2 in range(1, max_boundary + 1):
                    coherence = self.calculate_duality_coherence(pos, b1, int(round(dual_pos)), b2)
                    coherence_matrix[pos-1, b1-1, b2-1] = coherence
        
        return coherence_matrix
    
    def verify_hodge_duality_properties(self, position, boundary):
        """
        Verify that Hodge duality properties hold at a given position and boundary.
        
        Args:
            position: Position within boundary (1-13)
            boundary: Boundary number (1+)
            
        Returns:
            Dictionary of verification results
        """
        # Calculate Hodge star operator
        hodge_star = self.calculate_hodge_star_operator(position, boundary)
        
        # Verify that applying Hodge star twice gives identity (up to sign)
        # In 2D, * * = -1 for 1-forms
        identity_check = np.matmul(hodge_star, hodge_star)
        identity_error = np.max(np.abs(identity_check + np.eye(2)))
        
        # Calculate dual position and boundary
        dual_position, dual_boundary = self.calculate_hodge_dual_point(position, boundary)
        
        # Calculate Riemann tensors
        riemann = self.dg_core.calculate_riemann_tensor(position, boundary)
        dual_riemann = self.dg_core.calculate_riemann_tensor(int(round(dual_position)), dual_boundary)
        
        # Verify Bianchi identities
        bianchi1_error = self.dg_core.verify_first_bianchi_identity(position, boundary)
        dual_bianchi1_error = self.dg_core.verify_first_bianchi_identity(int(round(dual_position)), dual_boundary)
        
        return {
            'identity_error': float(identity_error),
            'bianchi1_error': float(bianchi1_error),
            'dual_bianchi1_error': float(dual_bianchi1_error)
        }
