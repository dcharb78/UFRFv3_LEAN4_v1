"""
Enhanced Dimensional Mapper for UFRF Framework

This module implements an enhanced dimensional mapper that maintains contextual unity
during dimensional mapping operations in the UFRF Framework.

Author: Daniel Charboneau
License: Creative Commons Attribution-NonCommercial 4.0 International
"""

import numpy as np

# Use relative import for module in the same package
from .contextual_unity_detector import ContextualUnityDetector

class EnhancedDimensionalMapper:
    """
    Enhanced dimensional mapper that maintains contextual unity during mapping operations.
    """
    
    def __init__(self, dimensional_base=13):
        """
        Initialize the enhanced dimensional mapper.
        
        Args:
            dimensional_base: Base for dimensional calculations (default: 13)
        """
        self.dimensional_base = dimensional_base
        self.unity_detector = ContextualUnityDetector(dimensional_base)
    
    def map_with_unity(self, n):
        """
        Maps a number to the multidimensional structure while maintaining contextual unity.
        
        Args:
            n: Number to map
            
        Returns:
            Dimensional mapping with contextual unity
        """
        # Calculate basic dimensional mapping
        c = ((n-1) % self.dimensional_base) + 1
        S = ((n-1) // self.dimensional_base) + 1
        L = ((S-1) % self.dimensional_base) + 1
        D = ((S-1) // self.dimensional_base) + 1
        R = ((D-1) % self.dimensional_base) + 1
        C = ((D-1) // self.dimensional_base) + 1
        d = ((C-1) % self.dimensional_base) + 1
        
        # Calculate contextual unity
        unity = self.unity_detector.calculate_contextual_unity(n, c, S, L, D)
        
        # Ensure unity is maintained
        if abs(unity - 1.0) > 1e-10:
            # Apply correction to maintain unity
            correction = self.calculate_unity_correction(n, c, S, L, D, unity)
            n_corrected = n + correction
        else:
            n_corrected = n
        
        return {
            'original_number': n,
            'corrected_number': n_corrected,
            'cycle_position': c,
            'system_level': S,
            'level': L,
            'domain': D,
            'realm': R,
            'continuum': C,
            'dimension': d,
            'contextual_unity': unity
        }
    
    def calculate_unity_correction(self, n, c, S, L, D, current_unity):
        """
        Calculates correction needed to maintain contextual unity.
        
        Args:
            n: Original number
            c, S, L, D: Dimensional mapping
            current_unity: Current unity value
            
        Returns:
            Correction value
        """
        # Calculate correction to achieve unity of 1
        target_unity = 1.0
        normalization_factor = self.unity_detector.calculate_normalization_factor(c, S, L, D)
        
        # Calculate correction
        if normalization_factor != 0:
            correction = (target_unity * normalization_factor) - n
        else:
            correction = 0
        
        return correction
    
    def map_range_with_unity(self, start, end):
        """
        Maps a range of numbers while maintaining contextual unity.
        
        Args:
            start: Start of range (inclusive)
            end: End of range (inclusive)
            
        Returns:
            List of dimensional mappings with contextual unity
        """
        mappings = []
        for n in range(start, end + 1):
            mapping = self.map_with_unity(n)
            mappings.append(mapping)
        
        return mappings
    
    def get_position_context(self, n):
        """
        Gets the position context for a number.
        
        Args:
            n: Number to analyze
            
        Returns:
            Position context information
        """
        # Get dimensional mapping
        mapping = self.map_with_unity(n)
        c = mapping['cycle_position']
        
        # Get position characteristics
        characteristics = self.unity_detector.get_position_characteristics(c)
        
        # Get position type
        position_type = self.unity_detector.get_position_type(c)
        
        return {
            'number': n,
            'cycle_position': c,
            'characteristics': characteristics,
            'position_type': position_type
        }
    
    def find_resonant_positions(self, n, max_distance=100):
        """
        Finds positions that resonate with a given number.
        
        Args:
            n: Number to analyze
            max_distance: Maximum distance to search for resonant positions
            
        Returns:
            List of resonant positions
        """
        # Get dimensional mapping
        mapping = self.map_with_unity(n)
        c = mapping['cycle_position']
        S = mapping['system_level']
        L = mapping['level']
        D = mapping['domain']
        
        # Get position characteristics
        characteristics = self.unity_detector.get_position_characteristics(c)
        
        # Find positions with the same characteristics
        resonant_positions = []
        
        # Search in both directions
        for offset in range(-max_distance, max_distance + 1):
            if offset == 0:
                continue  # Skip the number itself
                
            test_n = n + offset
            if test_n <= 0:
                continue  # Skip non-positive numbers
                
            test_mapping = self.map_with_unity(test_n)
            test_c = test_mapping['cycle_position']
            test_characteristics = self.unity_detector.get_position_characteristics(test_c)
            
            # Check if positions resonate
            if self.positions_resonate(characteristics, test_characteristics):
                resonant_positions.append({
                    'number': test_n,
                    'cycle_position': test_c,
                    'distance': offset,
                    'characteristics': test_characteristics
                })
        
        return resonant_positions
    
    def positions_resonate(self, char1, char2):
        """
        Determines if two positions resonate with each other.
        
        Args:
            char1: Characteristics of first position
            char2: Characteristics of second position
            
        Returns:
            True if positions resonate, False otherwise
        """
        # Positions resonate if they have the same type or polarity
        same_type = char1['type'] == char2['type']
        same_polarity = char1['polarity'] == char2['polarity']
        
        return same_type or same_polarity
    
    def analyze_dimensional_structure(self, n, depth=3):
        """
        Analyzes the dimensional structure around a number.
        
        Args:
            n: Number to analyze
            depth: Depth of analysis
            
        Returns:
            Dimensional structure analysis
        """
        # Get dimensional mapping
        mapping = self.map_with_unity(n)
        
        # Analyze cycle structure
        cycle_structure = self.analyze_cycle_structure(n, mapping, depth)
        
        # Analyze system structure
        system_structure = self.analyze_system_structure(n, mapping, depth)
        
        # Analyze level structure
        level_structure = self.analyze_level_structure(n, mapping, depth)
        
        return {
            'number': n,
            'mapping': mapping,
            'cycle_structure': cycle_structure,
            'system_structure': system_structure,
            'level_structure': level_structure
        }
    
    def analyze_cycle_structure(self, n, mapping, depth):
        """
        Analyzes the cycle structure around a number.
        
        Args:
            n: Number to analyze
            mapping: Dimensional mapping of the number
            depth: Depth of analysis
            
        Returns:
            Cycle structure analysis
        """
        c = mapping['cycle_position']
        S = mapping['system_level']
        L = mapping['level']
        D = mapping['domain']
        
        # Get all positions in the current cycle
        cycle_positions = []
        for pos in range(1, self.dimensional_base + 1):
            # Calculate number for this position
            pos_n = n + (pos - c)
            if pos_n <= 0:
                continue  # Skip non-positive numbers
                
            pos_mapping = self.map_with_unity(pos_n)
            
            # Only include positions in the same cycle
            if pos_mapping['system_level'] == S and pos_mapping['level'] == L and pos_mapping['domain'] == D:
                cycle_positions.append({
                    'number': pos_n,
                    'cycle_position': pos,
                    'characteristics': self.unity_detector.get_position_characteristics(pos),
                    'contextual_unity': pos_mapping['contextual_unity']
                })
        
        return {
            'cycle_positions': cycle_positions,
            'cycle_unity': self.calculate_cycle_unity(cycle_positions)
        }
    
    def analyze_system_structure(self, n, mapping, depth):
        """
        Analyzes the system structure around a number.
        
        Args:
            n: Number to analyze
            mapping: Dimensional mapping of the number
            depth: Depth of analysis
            
        Returns:
            System structure analysis
        """
        S = mapping['system_level']
        
        # Get adjacent systems
        adjacent_systems = []
        for offset in range(-depth, depth + 1):
            if offset == 0:
                continue  # Skip the current system
                
            adj_S = S + offset
            if adj_S <= 0:
                continue  # Skip non-positive systems
                
            # Find a representative number in this system
            adj_n = self.find_representative_number(adj_S)
            if adj_n is not None:
                adj_mapping = self.map_with_unity(adj_n)
                adjacent_systems.append({
                    'system_level': adj_S,
                    'representative_number': adj_n,
                    'mapping': adj_mapping
                })
        
        return {
            'current_system': S,
            'adjacent_systems': adjacent_systems
        }
    
    def analyze_level_structure(self, n, mapping, depth):
        """
        Analyzes the level structure around a number.
        
        Args:
            n: Number to analyze
            mapping: Dimensional mapping of the number
            depth: Depth of analysis
            
        Returns:
            Level structure analysis
        """
        L = mapping['level']
        D = mapping['domain']
        
        # Get adjacent levels
        adjacent_levels = []
        for offset in range(-depth, depth + 1):
            if offset == 0:
                continue  # Skip the current level
                
            adj_L = L + offset
            if adj_L <= 0 or adj_L > self.dimensional_base:
                continue  # Skip invalid levels
                
            # Find a representative number in this level
            adj_n = self.find_representative_number_in_level(adj_L, D)
            if adj_n is not None:
                adj_mapping = self.map_with_unity(adj_n)
                adjacent_levels.append({
                    'level': adj_L,
                    'representative_number': adj_n,
                    'mapping': adj_mapping
                })
        
        return {
            'current_level': L,
            'adjacent_levels': adjacent_levels
        }
    
    def find_representative_number(self, S):
        """
        Finds a representative number for a system level.
        
        Args:
            S: System level
            
        Returns:
            Representative number, or None if not found
        """
        # Calculate the first number in the system
        first_n = (S - 1) * self.dimensional_base + 1
        return first_n
    
    def find_representative_number_in_level(self, L, D):
        """
        Finds a representative number for a level within a domain.
        
        Args:
            L: Level
            D: Domain
            
        Returns:
            Representative number, or None if not found
        """
        # Calculate the first system in this level
        first_S = (D - 1) * self.dimensional_base + L
        
        # Calculate the first number in this system
        first_n = (first_S - 1) * self.dimensional_base + 1
        return first_n
    
    def calculate_cycle_unity(self, cycle_positions):
        """
        Calculates the overall unity of a cycle.
        
        Args:
            cycle_positions: List of positions in the cycle
            
        Returns:
            Cycle unity value
        """
        if not cycle_positions:
            return 0.0
            
        # Calculate average unity
        total_unity = sum(pos['contextual_unity'] for pos in cycle_positions)
        average_unity = total_unity / len(cycle_positions)
        
        return average_unity


# Test function
def test_enhanced_dimensional_mapper():
    """
    Tests the EnhancedDimensionalMapper class.
    """
    mapper = EnhancedDimensionalMapper()
    
    # Test for a few numbers
    test_cases = [1, 13, 14, 170]
    
    for n in test_cases:
        mapping = mapper.map_with_unity(n)
        print(f"Number {n}:")
        print(f"  Dimensional mapping: c={mapping['cycle_position']}, S={mapping['system_level']}, L={mapping['level']}, D={mapping['domain']}")
        print(f"  Contextual unity: {mapping['contextual_unity']}")
        
        # Get position context
        context = mapper.get_position_context(n)
        print(f"  Position type: {context['position_type']}")
        print(f"  Characteristics: {context['characteristics']}")
        
        # Find resonant positions
        resonant = mapper.find_resonant_positions(n, max_distance=20)
        print(f"  Resonant positions: {len(resonant)}")
        for pos in resonant[:3]:  # Show first 3
            print(f"    Number {pos['number']} (c={pos['cycle_position']}, distance={pos['distance']})")
        
        print()
    
    # Test dimensional structure analysis
    n = 42
    structure = mapper.analyze_dimensional_structure(n, depth=2)
    print(f"Dimensional structure analysis for number {n}:")
    print(f"  Cycle positions: {len(structure['cycle_structure']['cycle_positions'])}")
    print(f"  Cycle unity: {structure['cycle_structure']['cycle_unity']}")
    print(f"  Adjacent systems: {len(structure['system_structure']['adjacent_systems'])}")
    print(f"  Adjacent levels: {len(structure['level_structure']['adjacent_levels'])}")


if __name__ == "__main__":
    test_enhanced_dimensional_mapper()
