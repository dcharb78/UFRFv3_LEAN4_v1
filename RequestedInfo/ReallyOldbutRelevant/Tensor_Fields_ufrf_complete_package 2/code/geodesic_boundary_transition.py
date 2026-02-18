import numpy as np
from .differential_geometry_core import DifferentialGeometryCore

class GeodesicBoundaryTransition:
    """
    Handles transitions between boundaries using geodesic paths.
    
    Author: Daniel Charboneau
    License: Creative Commons Attribution-NonCommercial 4.0 International
    """
    
    def __init__(self, dimensional_base=13):
        """
        Initialize the geodesic boundary transition handler.
        
        Args:
            dimensional_base: Base for dimensional calculations (default: 13)
        """
        self.dimensional_base = dimensional_base
        self.dg_core = DifferentialGeometryCore(dimensional_base)
        self.phi = (1 + np.sqrt(5)) / 2  # Golden ratio
        
    def calculate_optimal_transition(self, position1, boundary1, position2, boundary2, steps=10):
        """
        Calculate the optimal transition path between positions in different boundaries.
        
        Args:
            position1: Position in first boundary (1-13)
            boundary1: First boundary number (1+)
            position2: Position in second boundary (1-13)
            boundary2: Second boundary number (1+)
            steps: Number of steps along the transition path
            
        Returns:
            List of (position, boundary) points along the optimal path
        """
        # Calculate geodesic path
        geodesic = self.dg_core.calculate_geodesic(position1, boundary1, position2, boundary2, steps)
        
        # Calculate golden ratio path
        golden_path = self.calculate_golden_ratio_path(position1, boundary1, position2, boundary2, steps)
        
        # Calculate coherence for both paths
        geodesic_coherence = self.calculate_path_coherence(geodesic)
        golden_coherence = self.calculate_path_coherence(golden_path)
        
        # Choose the path with higher coherence
        if golden_coherence > geodesic_coherence:
            return golden_path
        else:
            return geodesic
    
    def calculate_golden_ratio_path(self, position1, boundary1, position2, boundary2, steps=10):
        """
        Calculate a transition path based on golden ratio projections.
        
        Args:
            position1: Position in first boundary (1-13)
            boundary1: First boundary number (1+)
            position2: Position in second boundary (1-13)
            boundary2: Second boundary number (1+)
            steps: Number of steps along the transition path
            
        Returns:
            List of (position, boundary) points along the golden ratio path
        """
        # Initialize path
        path = []
        
        # Parameter along the path
        t_values = np.linspace(0, 1, steps)
        
        # Determine if positions are in inner or outer octave
        is_outer1 = position1 in [1, 2, 3, 10, 11, 12, 13]
        is_outer2 = position2 in [1, 2, 3, 10, 11, 12, 13]
        
        # Calculate golden ratio projections
        for t in t_values:
            # Linear interpolation for boundary
            boundary = boundary1 + t * (boundary2 - boundary1)
            
            # Golden ratio weighted interpolation for position
            if is_outer1 and is_outer2:
                # Outer-to-outer: use golden ratio weighting
                weight = (1 - t) + t * self.phi
                position = ((1 - t) * position1 + t * position2 * self.phi) / weight
            elif not is_outer1 and not is_outer2:
                # Inner-to-inner: use inverse golden ratio weighting
                weight = (1 - t) + t / self.phi
                position = ((1 - t) * position1 + t * position2 / self.phi) / weight
            else:
                # Inner-to-outer or outer-to-inner: use special transition
                if is_outer1:
                    # Outer-to-inner: transition through position 4
                    if t < 0.5:
                        position = position1 + 2 * t * (4 - position1)
                    else:
                        position = 4 + 2 * (t - 0.5) * (position2 - 4)
                else:
                    # Inner-to-outer: transition through position 10
                    if t < 0.5:
                        position = position1 + 2 * t * (10 - position1)
                    else:
                        position = 10 + 2 * (t - 0.5) * (position2 - 10)
            
            # Ensure position is within valid range
            position = max(1, min(self.dimensional_base, position))
            
            # Add point to path
            path.append((position, boundary))
        
        return path
    
    def calculate_path_coherence(self, path):
        """
        Calculate the overall coherence of a transition path.
        
        Args:
            path: List of (position, boundary) points along the path
            
        Returns:
            Overall coherence value (0-1)
        """
        if len(path) < 2:
            return 1.0  # Perfect coherence for single point
        
        # Calculate coherence between adjacent points
        coherences = []
        for i in range(len(path) - 1):
            pos1, bound1 = path[i]
            pos2, bound2 = path[i + 1]
            
            # Calculate Riemann tensors at both positions
            riemann1 = self.dg_core.calculate_riemann_tensor(int(round(pos1)), int(round(bound1)))
            riemann2 = self.dg_core.calculate_riemann_tensor(int(round(pos2)), int(round(bound2)))
            
            # Calculate tensor similarity
            similarity = self._calculate_tensor_similarity(riemann1, riemann2)
            coherences.append(similarity)
        
        # Calculate overall coherence as geometric mean
        product = 1.0
        for coherence in coherences:
            product *= coherence
        
        overall_coherence = product ** (1.0 / len(coherences))
        
        return overall_coherence
    
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
    
    def find_optimal_boundary_transition(self, position, boundary1, boundary2, max_intermediate=3):
        """
        Find the optimal sequence of boundary transitions for a given position.
        
        Args:
            position: Position within boundary (1-13)
            boundary1: Starting boundary number (1+)
            boundary2: Ending boundary number (1+)
            max_intermediate: Maximum number of intermediate boundaries to consider
            
        Returns:
            List of boundary numbers representing the optimal transition sequence
        """
        # Direct transition
        direct_path = [(position, boundary1), (position, boundary2)]
        direct_coherence = self.calculate_path_coherence(direct_path)
        
        best_path = [boundary1, boundary2]
        best_coherence = direct_coherence
        
        # Try paths with intermediate boundaries
        for num_intermediate in range(1, max_intermediate + 1):
            # Generate candidate intermediate boundaries
            candidates = self._generate_candidate_boundaries(boundary1, boundary2, num_intermediate)
            
            for intermediate_boundaries in candidates:
                # Construct full boundary sequence
                boundaries = [boundary1] + intermediate_boundaries + [boundary2]
                
                # Construct path
                path = [(position, b) for b in boundaries]
                
                # Calculate coherence
                coherence = self.calculate_path_coherence(path)
                
                # Update best path if better
                if coherence > best_coherence:
                    best_path = boundaries
                    best_coherence = coherence
        
        return best_path
    
    def _generate_candidate_boundaries(self, boundary1, boundary2, num_intermediate):
        """
        Generate candidate intermediate boundaries for transition.
        
        Args:
            boundary1: Starting boundary number (1+)
            boundary2: Ending boundary number (1+)
            num_intermediate: Number of intermediate boundaries to generate
            
        Returns:
            List of lists, each containing intermediate boundary numbers
        """
        candidates = []
        
        # Linear spacing
        linear_spacing = np.linspace(boundary1, boundary2, num_intermediate + 2)[1:-1]
        linear_candidates = [int(round(b)) for b in linear_spacing]
        candidates.append(linear_candidates)
        
        # Fibonacci-based spacing
        fib_candidates = []
        for i in range(num_intermediate):
            # Use Fibonacci sequence to generate intermediate boundaries
            ratio = (i + 1) / (num_intermediate + 1)
            fib_boundary = boundary1 + ratio * (boundary2 - boundary1)
            fib_candidates.append(int(round(fib_boundary)))
        candidates.append(fib_candidates)
        
        # Golden ratio based spacing
        golden_candidates = []
        for i in range(num_intermediate):
            # Use golden ratio to generate intermediate boundaries
            ratio = (1 - (1 / self.phi) ** (i + 1)) / (1 - (1 / self.phi) ** (num_intermediate + 1))
            golden_boundary = boundary1 + ratio * (boundary2 - boundary1)
            golden_candidates.append(int(round(golden_boundary)))
        candidates.append(golden_candidates)
        
        return candidates
    
    def calculate_transition_coherence_matrix(self, max_position=13, max_boundary=3):
        """
        Calculate coherence matrix for transitions between all positions across boundaries.
        
        Args:
            max_position: Maximum position to consider (default: 13)
            max_boundary: Maximum boundary to consider (default: 3)
            
        Returns:
            4D numpy array of coherence values [position1, boundary1, position2, boundary2]
        """
        # Initialize coherence matrix
        coherence_matrix = np.zeros((max_position, max_boundary, max_position, max_boundary))
        
        # Calculate coherence for all position-boundary pairs
        for pos1 in range(1, max_position + 1):
            for b1 in range(1, max_boundary + 1):
                for pos2 in range(1, max_position + 1):
                    for b2 in range(1, max_boundary + 1):
                        # Skip identical points
                        if pos1 == pos2 and b1 == b2:
                            coherence_matrix[pos1-1, b1-1, pos2-1, b2-1] = 1.0
                            continue
                        
                        # Calculate optimal transition
                        path = self.calculate_optimal_transition(pos1, b1, pos2, b2, steps=5)
                        
                        # Calculate coherence
                        coherence = self.calculate_path_coherence(path)
                        
                        # Store in matrix
                        coherence_matrix[pos1-1, b1-1, pos2-1, b2-1] = coherence
        
        return coherence_matrix
