"""
Cross-Scale Coherence Optimizer for UFRF Framework

This module implements enhanced cross-scale coherence mechanisms to optimize
unity maintenance across system boundaries using musical-like harmonic relationships.

Author: Daniel Charboneau
License: Creative Commons Attribution-NonCommercial 4.0 International
"""

import numpy as np
import time
from collections import defaultdict
from .harmonic_unity_function import HarmonicUnityFunction, HarmonicDimensionalMapper

class CrossScaleCoherenceOptimizer:
    """
    Implements enhanced cross-scale coherence mechanisms to optimize unity maintenance
    across system boundaries using musical-like harmonic relationships.
    """
    
    def __init__(self, dimensional_base=13):
        """
        Initialize the cross-scale coherence optimizer.
        
        Args:
            dimensional_base: Base for dimensional calculations (default: 13)
        """
        self.dimensional_base = dimensional_base
        self.unity_function = HarmonicUnityFunction(dimensional_base)
        self.mapper = HarmonicDimensionalMapper(dimensional_base)
        self.coherence_cache = {}
        
        # Define boundary resonance patterns
        self.boundary_resonance_patterns = self._define_boundary_resonance_patterns()
        
        # Define scale transition matrices
        self.scale_transition_matrices = self._define_scale_transition_matrices()
    
    def _define_boundary_resonance_patterns(self):
        """
        Define resonance patterns at system boundaries.
        
        Returns:
            Dictionary of boundary resonance patterns
        """
        patterns = {}
        
        # First boundary (1-13)
        patterns[1] = {
            'fundamental': [1, 13],  # Fundamental positions
            'perfect_fifth': [5, 9],  # Perfect fifth positions
            'perfect_fourth': [4, 10],  # Perfect fourth positions
            'major_third': [5],  # Major third positions
            'minor_third': [6],  # Minor third positions
            'center': [7]  # Center position
        }
        
        # Second boundary (14-26)
        patterns[2] = {
            'fundamental': [14, 26],
            'perfect_fifth': [18, 22],
            'perfect_fourth': [17, 23],
            'major_third': [18],
            'minor_third': [19],
            'center': [20]
        }
        
        # Third boundary (27-39)
        patterns[3] = {
            'fundamental': [27, 39],
            'perfect_fifth': [31, 35],
            'perfect_fourth': [30, 36],
            'major_third': [31],
            'minor_third': [32],
            'center': [33]
        }
        
        # Fourth boundary (40-52)
        patterns[4] = {
            'fundamental': [40, 52],
            'perfect_fifth': [44, 48],
            'perfect_fourth': [43, 49],
            'major_third': [44],
            'minor_third': [45],
            'center': [46]
        }
        
        return patterns
    
    def _define_scale_transition_matrices(self):
        """
        Define transition matrices between scales.
        
        Returns:
            Dictionary of scale transition matrices
        """
        matrices = {}
        
        # Cycle to System transition matrix
        matrices['c_to_S'] = np.array([
            [1.0, 0.5, 0.3, 0.2, 0.1, 0.1, 0.1, 0.1, 0.1, 0.2, 0.3, 0.5, 1.0],  # c=1
            [0.5, 1.0, 0.5, 0.3, 0.2, 0.1, 0.1, 0.1, 0.1, 0.1, 0.2, 0.3, 0.5],  # c=2
            [0.3, 0.5, 1.0, 0.5, 0.3, 0.2, 0.1, 0.1, 0.1, 0.1, 0.1, 0.2, 0.3],  # c=3
            [0.2, 0.3, 0.5, 1.0, 0.5, 0.3, 0.2, 0.1, 0.1, 0.1, 0.1, 0.1, 0.2],  # c=4
            [0.1, 0.2, 0.3, 0.5, 1.0, 0.5, 0.3, 0.2, 0.1, 0.1, 0.1, 0.1, 0.1],  # c=5
            [0.1, 0.1, 0.2, 0.3, 0.5, 1.0, 0.5, 0.3, 0.2, 0.1, 0.1, 0.1, 0.1],  # c=6
            [0.1, 0.1, 0.1, 0.2, 0.3, 0.5, 1.0, 0.5, 0.3, 0.2, 0.1, 0.1, 0.1],  # c=7
            [0.1, 0.1, 0.1, 0.1, 0.2, 0.3, 0.5, 1.0, 0.5, 0.3, 0.2, 0.1, 0.1],  # c=8
            [0.1, 0.1, 0.1, 0.1, 0.1, 0.2, 0.3, 0.5, 1.0, 0.5, 0.3, 0.2, 0.1],  # c=9
            [0.2, 0.1, 0.1, 0.1, 0.1, 0.1, 0.2, 0.3, 0.5, 1.0, 0.5, 0.3, 0.2],  # c=10
            [0.3, 0.2, 0.1, 0.1, 0.1, 0.1, 0.1, 0.2, 0.3, 0.5, 1.0, 0.5, 0.3],  # c=11
            [0.5, 0.3, 0.2, 0.1, 0.1, 0.1, 0.1, 0.1, 0.2, 0.3, 0.5, 1.0, 0.5],  # c=12
            [1.0, 0.5, 0.3, 0.2, 0.1, 0.1, 0.1, 0.1, 0.1, 0.2, 0.3, 0.5, 1.0],  # c=13
        ])
        
        # System to Level transition matrix
        matrices['S_to_L'] = np.array([
            [1.0, 0.3, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.3, 1.0],  # S=1
            [0.3, 1.0, 0.3, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.3],  # S=2
            [0.1, 0.3, 1.0, 0.3, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1],  # S=3
            [0.1, 0.1, 0.3, 1.0, 0.3, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1],  # S=4
            [0.1, 0.1, 0.1, 0.3, 1.0, 0.3, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1],  # S=5
            [0.1, 0.1, 0.1, 0.1, 0.3, 1.0, 0.3, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1],  # S=6
            [0.1, 0.1, 0.1, 0.1, 0.1, 0.3, 1.0, 0.3, 0.1, 0.1, 0.1, 0.1, 0.1],  # S=7
            [0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.3, 1.0, 0.3, 0.1, 0.1, 0.1, 0.1],  # S=8
            [0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.3, 1.0, 0.3, 0.1, 0.1, 0.1],  # S=9
            [0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.3, 1.0, 0.3, 0.1, 0.1],  # S=10
            [0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.3, 1.0, 0.3, 0.1],  # S=11
            [0.3, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.3, 1.0, 0.3],  # S=12
            [1.0, 0.3, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.3, 1.0],  # S=13
        ])
        
        # Level to Domain transition matrix
        matrices['L_to_D'] = np.array([
            [1.0, 0.2, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.2, 1.0],  # L=1
            [0.2, 1.0, 0.2, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.2],  # L=2
            [0.1, 0.2, 1.0, 0.2, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1],  # L=3
            [0.1, 0.1, 0.2, 1.0, 0.2, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1],  # L=4
            [0.1, 0.1, 0.1, 0.2, 1.0, 0.2, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1],  # L=5
            [0.1, 0.1, 0.1, 0.1, 0.2, 1.0, 0.2, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1],  # L=6
            [0.1, 0.1, 0.1, 0.1, 0.1, 0.2, 1.0, 0.2, 0.1, 0.1, 0.1, 0.1, 0.1],  # L=7
            [0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.2, 1.0, 0.2, 0.1, 0.1, 0.1, 0.1],  # L=8
            [0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.2, 1.0, 0.2, 0.1, 0.1, 0.1],  # L=9
            [0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.2, 1.0, 0.2, 0.1, 0.1],  # L=10
            [0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.2, 1.0, 0.2, 0.1],  # L=11
            [0.2, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.2, 1.0, 0.2],  # L=12
            [1.0, 0.2, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.2, 1.0],  # L=13
        ])
        
        return matrices
    
    def optimize_cross_scale_coherence(self, n):
        """
        Optimize cross-scale coherence for a number.
        
        Args:
            n: Number to optimize
            
        Returns:
            Dictionary with optimized coherence
        """
        # Check cache
        if n in self.coherence_cache:
            return self.coherence_cache[n]
        
        # Get dimensional mapping
        mapping = self.mapper.map_with_unity(n)
        
        # Extract dimensional coordinates
        c = mapping['cycle_position']
        S = mapping['system_level']
        L = mapping['level']
        D = mapping['domain']
        boundary_level = mapping['boundary_level']
        
        # Analyze adjacent scale coherence
        adjacent_coherence = self.analyze_adjacent_scale_coherence(c, S, L, D)
        
        # Analyze boundary coherence
        boundary_coherence = self.analyze_boundary_coherence(n, boundary_level)
        
        # Analyze harmonic coherence
        harmonic_coherence = self.analyze_harmonic_coherence(n, mapping)
        
        # Calculate overall coherence
        overall_coherence = (
            adjacent_coherence['overall_coherence'] * 0.4 +
            boundary_coherence['overall_coherence'] * 0.4 +
            harmonic_coherence['overall_coherence'] * 0.2
        )
        
        # Apply coherence optimization
        optimized_unity = self.apply_coherence_optimization(
            n, mapping['contextual_unity'], overall_coherence)
        
        # Create result
        result = {
            'number': n,
            'dimensional_mapping': mapping,
            'adjacent_scale_coherence': adjacent_coherence,
            'boundary_coherence': boundary_coherence,
            'harmonic_coherence': harmonic_coherence,
            'overall_coherence': overall_coherence,
            'original_unity': mapping['contextual_unity'],
            'optimized_unity': optimized_unity,
            'unity_improvement': optimized_unity - mapping['contextual_unity']
        }
        
        # Cache result
        self.coherence_cache[n] = result
        
        return result
    
    def analyze_adjacent_scale_coherence(self, c, S, L, D):
        """
        Analyze coherence between adjacent scales.
        
        Args:
            c: Cycle position
            S: System level
            L: Level
            D: Domain
            
        Returns:
            Dictionary with adjacent scale coherence
        """
        # Calculate cycle-to-system coherence
        c_to_S_coherence = self.calculate_scale_transition_coherence(c, S, 'c_to_S')
        
        # Calculate system-to-level coherence
        S_to_L_coherence = self.calculate_scale_transition_coherence(S, L, 'S_to_L')
        
        # Calculate level-to-domain coherence
        L_to_D_coherence = self.calculate_scale_transition_coherence(L, D, 'L_to_D')
        
        # Calculate overall adjacent scale coherence
        overall_coherence = (c_to_S_coherence + S_to_L_coherence + L_to_D_coherence) / 3
        
        return {
            'cycle_to_system': c_to_S_coherence,
            'system_to_level': S_to_L_coherence,
            'level_to_domain': L_to_D_coherence,
            'overall_coherence': overall_coherence
        }
    
    def calculate_scale_transition_coherence(self, scale1, scale2, transition_type):
        """
        Calculate coherence for a scale transition.
        
        Args:
            scale1: First scale value
            scale2: Second scale value
            transition_type: Type of transition ('c_to_S', 'S_to_L', or 'L_to_D')
            
        Returns:
            Coherence value
        """
        # Get transition matrix
        matrix = self.scale_transition_matrices.get(transition_type)
        
        if matrix is None:
            return 0.5  # Default coherence
        
        # Adjust indices (1-based to 0-based)
        i = min(scale1 - 1, len(matrix) - 1)
        j = min(scale2 - 1, len(matrix[0]) - 1)
        
        # Get coherence from matrix
        coherence = matrix[i, j]
        
        return coherence
    
    def analyze_boundary_coherence(self, n, boundary_level):
        """
        Analyze coherence across system boundaries.
        
        Args:
            n: Number
            boundary_level: Boundary level
            
        Returns:
            Dictionary with boundary coherence
        """
        # Calculate position within boundary
        position = ((n - 1) % self.dimensional_base) + 1
        
        # Calculate boundary position coherence
        boundary_position_coherence = self.calculate_boundary_position_coherence(n, boundary_level)
        
        # Calculate cross-boundary resonance
        cross_boundary_coherence = self.calculate_cross_boundary_coherence(n, boundary_level)
        
        # Calculate boundary pattern coherence
        pattern_coherence = self.calculate_boundary_pattern_coherence(n, boundary_level)
        
        # Calculate overall boundary coherence
        overall_coherence = (
            boundary_position_coherence * 0.3 +
            cross_boundary_coherence * 0.4 +
            pattern_coherence * 0.3
        )
        
        return {
            'boundary_position_coherence': boundary_position_coherence,
            'cross_boundary_coherence': cross_boundary_coherence,
            'pattern_coherence': pattern_coherence,
            'overall_coherence': overall_coherence
        }
    
    def calculate_boundary_position_coherence(self, n, boundary_level):
        """
        Calculate coherence based on position within boundary.
        
        Args:
            n: Number
            boundary_level: Boundary level
            
        Returns:
            Boundary position coherence
        """
        # Calculate position within boundary
        position = ((n - 1) % self.dimensional_base) + 1
        
        # Highest coherence for boundary positions (1 and 13)
        if position == 1 or position == self.dimensional_base:
            return 1.0
        
        # High coherence for center position (7)
        if position == 7:
            return 0.9
        
        # High coherence for perfect fifth positions (5 and 9)
        if position == 5 or position == 9:
            return 0.85
        
        # Moderate coherence for perfect fourth positions (4 and 10)
        if position == 4 or position == 10:
            return 0.8
        
        # Moderate coherence for third positions (3 and 11)
        if position == 3 or position == 11:
            return 0.75
        
        # Lower coherence for other positions
        return 0.7
    
    def calculate_cross_boundary_coherence(self, n, boundary_level):
        """
        Calculate coherence across system boundaries.
        
        Args:
            n: Number
            boundary_level: Boundary level
            
        Returns:
            Cross-boundary coherence
        """
        # No cross-boundary coherence for first boundary
        if boundary_level == 1:
            return 0.8  # Default coherence for first boundary
        
        # Calculate position within boundary
        position = ((n - 1) % self.dimensional_base) + 1
        
        # Calculate corresponding positions in lower boundaries
        coherence_sum = 0
        count = 0
        
        for lower_boundary in range(1, boundary_level):
            corresponding_position = position + (lower_boundary - 1) * self.dimensional_base
            
            # Calculate ratio
            ratio = n / corresponding_position
            
            # Calculate coherence based on ratio
            if abs(ratio - round(ratio)) < 0.01:  # Integer ratio
                coherence = 1.0
            elif abs(ratio - (round(ratio * 2) / 2)) < 0.01:  # Half-integer ratio
                coherence = 0.9
            elif abs(ratio - (round(ratio * 3) / 3)) < 0.01:  # Third-integer ratio
                coherence = 0.8
            else:
                coherence = 0.7
            
            coherence_sum += coherence
            count += 1
        
        return coherence_sum / count if count > 0 else 0.8
    
    def calculate_boundary_pattern_coherence(self, n, boundary_level):
        """
        Calculate coherence based on boundary resonance patterns.
        
        Args:
            n: Number
            boundary_level: Boundary level
            
        Returns:
            Pattern coherence
        """
        # Get boundary patterns
        patterns = self.boundary_resonance_patterns.get(boundary_level)
        
        if patterns is None:
            return 0.7  # Default coherence
        
        # Check if number is in any pattern
        for pattern_type, numbers in patterns.items():
            if n in numbers:
                # Assign coherence based on pattern type
                if pattern_type == 'fundamental':
                    return 1.0
                elif pattern_type == 'perfect_fifth':
                    return 0.95
                elif pattern_type == 'perfect_fourth':
                    return 0.9
                elif pattern_type == 'major_third':
                    return 0.85
                elif pattern_type == 'minor_third':
                    return 0.8
                elif pattern_type == 'center':
                    return 0.9
        
        # Default coherence for numbers not in any pattern
        return 0.7
    
    def analyze_harmonic_coherence(self, n, mapping):
        """
        Analyze coherence based on harmonic relationships.
        
        Args:
            n: Number
            mapping: Dimensional mapping
            
        Returns:
            Dictionary with harmonic coherence
        """
        harmonic_properties = mapping['harmonic_properties']
        
        # Calculate harmonic series coherence
        series_coherence = self.calculate_harmonic_series_coherence(n, harmonic_properties.get('harmonic_series', []))
        
        # Calculate resonant positions coherence
        resonance_coherence = self.calculate_resonance_coherence(n, harmonic_properties.get('resonant_positions', []))
        
        # Calculate consonance coherence
        consonance_coherence = self.calculate_consonance_coherence(n, harmonic_properties.get('consonance_map', {}))
        
        # Calculate overall harmonic coherence
        overall_coherence = (series_coherence + resonance_coherence + consonance_coherence) / 3
        
        return {
            'harmonic_series_coherence': series_coherence,
            'resonance_coherence': resonance_coherence,
            'consonance_coherence': consonance_coherence,
            'overall_coherence': overall_coherence
        }
    
    def calculate_harmonic_series_coherence(self, n, harmonic_series):
        """
        Calculate coherence based on harmonic series.
        
        Args:
            n: Number
            harmonic_series: Harmonic series
            
        Returns:
            Harmonic series coherence
        """
        if not harmonic_series:
            return 0.7  # Default coherence
        
        # Check if n is in the harmonic series
        if n in harmonic_series:
            return 1.0
        
        # Check if n is close to a harmonic
        min_distance = min(abs(n - h) / h for h in harmonic_series if h != 0)
        
        # Convert distance to coherence (closer = higher coherence)
        coherence = max(0.7, 1.0 - min_distance)
        
        return coherence
    
    def calculate_resonance_coherence(self, n, resonant_positions):
        """
        Calculate coherence based on resonant positions.
        
        Args:
            n: Number
            resonant_positions: Resonant positions
            
        Returns:
            Resonance coherence
        """
        if not resonant_positions:
            return 0.7  # Default coherence
        
        # Calculate average resonance strength
        total_resonance = 0
        for pos in resonant_positions:
            ratio = max(n, pos) / min(n, pos) if min(n, pos) != 0 else 1
            
            # Calculate resonance strength based on ratio
            if abs(ratio - round(ratio)) < 0.01:  # Integer ratio
                resonance_strength = 1.0
            elif abs(ratio - (round(ratio * 2) / 2)) < 0.01:  # Half-integer ratio
                resonance_strength = 0.9
            elif abs(ratio - (round(ratio * 3) / 3)) < 0.01:  # Third-integer ratio
                resonance_strength = 0.8
            else:
                resonance_strength = 0.7
            
            total_resonance += resonance_strength
        
        return total_resonance / len(resonant_positions)
    
    def calculate_consonance_coherence(self, n, consonance_map):
        """
        Calculate coherence based on consonance map.
        
        Args:
            n: Number
            consonance_map: Consonance map
            
        Returns:
            Consonance coherence
        """
        if not consonance_map:
            return 0.7  # Default coherence
        
        # Count consonant relationships
        consonant_count = sum(1 for relation in consonance_map.values() 
                             if relation in ['unison', 'octave', 'perfect_fifth', 'perfect_fourth'])
        
        # Calculate consonance ratio
        consonance_ratio = consonant_count / len(consonance_map)
        
        # Convert ratio to coherence
        coherence = 0.7 + 0.3 * consonance_ratio
        
        return coherence
    
    def apply_coherence_optimization(self, n, unity, coherence):
        """
        Apply coherence optimization to unity value.
        
        Args:
            n: Number
            unity: Original unity value
            coherence: Overall coherence
            
        Returns:
            Optimized unity value
        """
        # Calculate optimization factor
        optimization_factor = self.calculate_optimization_factor(n, coherence)
        
        # Apply optimization
        optimized_unity = unity * optimization_factor
        
        # Ensure unity is in valid range [0, 1]
        optimized_unity = max(0.0, min(1.0, optimized_unity))
        
        return optimized_unity
    
    def calculate_optimization_factor(self, n, coherence):
        """
        Calculate optimization factor based on coherence.
        
        Args:
            n: Number
            coherence: Overall coherence
            
        Returns:
            Optimization factor
        """
        # Base factor
        base_factor = 1.0
        
        # Adjust factor based on coherence
        if coherence >= 0.9:
            # High coherence: boost unity
            coherence_adjustment = 1.2
        elif coherence >= 0.8:
            # Good coherence: slight boost
            coherence_adjustment = 1.1
        elif coherence >= 0.7:
            # Moderate coherence: no change
            coherence_adjustment = 1.0
        elif coherence >= 0.6:
            # Low coherence: slight reduction
            coherence_adjustment = 0.9
        else:
            # Very low coherence: significant reduction
            coherence_adjustment = 0.8
        
        # Adjust factor based on number properties
        if self.unity_function.is_prime(n):
            # Prime numbers get a boost
            property_adjustment = 1.1
        else:
            # Non-prime numbers: no adjustment
            property_adjustment = 1.0
        
        # Calculate final factor
        optimization_factor = base_factor * coherence_adjustment * property_adjustment
        
        return optimization_factor
    
    def optimize_range(self, start, end):
        """
        Optimize cross-scale coherence for a range of numbers.
        
        Args:
            start: Start of range
            end: End of range
            
        Returns:
            Dictionary with optimization results
        """
        results = []
        
        for n in range(start, end + 1):
            results.append(self.optimize_cross_scale_coherence(n))
        
        # Calculate statistics
        original_unity_maintained = sum(1 for r in results if r['original_unity'] >= 0.8)
        optimized_unity_maintained = sum(1 for r in results if r['optimized_unity'] >= 0.8)
        
        original_rate = original_unity_maintained / len(results)
        optimized_rate = optimized_unity_maintained / len(results)
        
        improvement = optimized_rate - original_rate
        
        return {
            'results': results,
            'original_unity_maintained': original_unity_maintained,
            'optimized_unity_maintained': optimized_unity_maintained,
            'total_count': len(results),
            'original_unity_rate': original_rate,
            'optimized_unity_rate': optimized_rate,
            'improvement': improvement
        }


# Test function
def test_cross_scale_coherence_optimizer():
    """
    Tests the CrossScaleCoherenceOptimizer class.
    """
    optimizer = CrossScaleCoherenceOptimizer()
    
    # Test for key boundary numbers
    test_cases = [1, 13, 14, 26, 27, 39, 40, 52]
    
    for n in test_cases:
        # Optimize cross-scale coherence
        result = optimizer.optimize_cross_scale_coherence(n)
        
        print(f"Number {n}:")
        print(f"  Original unity: {result['original_unity']:.4f}")
        print(f"  Optimized unity: {result['optimized_unity']:.4f}")
        print(f"  Unity improvement: {result['unity_improvement']:.4f}")
        print(f"  Overall coherence: {result['overall_coherence']:.4f}")
        print(f"  Adjacent scale coherence: {result['adjacent_scale_coherence']['overall_coherence']:.4f}")
        print(f"  Boundary coherence: {result['boundary_coherence']['overall_coherence']:.4f}")
        print(f"  Harmonic coherence: {result['harmonic_coherence']['overall_coherence']:.4f}")
        print()
    
    # Test optimization for ranges
    ranges = [(1, 13), (14, 26), (27, 39), (40, 52)]
    
    for start, end in ranges:
        range_result = optimizer.optimize_range(start, end)
        
        print(f"Range {start}-{end}:")
        print(f"  Original unity rate: {range_result['original_unity_rate']:.4f}")
        print(f"  Optimized unity rate: {range_result['optimized_unity_rate']:.4f}")
        print(f"  Improvement: {range_result['improvement']:.4f}")
        print(f"  Unity maintained: {range_result['optimized_unity_maintained']}/{range_result['total_count']}")
        print()


if __name__ == "__main__":
    test_cross_scale_coherence_optimizer()
