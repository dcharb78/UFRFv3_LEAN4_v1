"""
Cross-Scale Context Analyzer for UFRF Framework

This module implements the Cross-Scale Context Analyzer component that analyzes
contextual relationships across multiple scales in the UFRF Framework.

Author: Daniel Charboneau
License: Creative Commons Attribution-NonCommercial 4.0 International
"""

import numpy as np

# Use relative imports for modules in the same package
from .contextual_unity_detector import ContextualUnityDetector
from .enhanced_dimensional_mapper import EnhancedDimensionalMapper

class CrossScaleContextAnalyzer:
    """
    Analyzes contextual relationships across multiple scales.
    """
    
    def __init__(self, dimensional_base=13):
        """
        Initialize the cross-scale context analyzer.
        
        Args:
            dimensional_base: Base for dimensional calculations (default: 13)
        """
        self.dimensional_base = dimensional_base
        self.unity_detector = ContextualUnityDetector(dimensional_base)
        self.dimensional_mapper = EnhancedDimensionalMapper(dimensional_base)
    
    def analyze_cross_scale_context(self, n, dimensional_mapping=None):
        """
        Analyzes contextual relationships across multiple scales.
        
        Args:
            n: Number being analyzed
            dimensional_mapping: Dimensional mapping of the number (optional)
            
        Returns:
            Cross-scale context analysis
        """
        # Get dimensional mapping if not provided
        if dimensional_mapping is None:
            dimensional_mapping = self.dimensional_mapper.map_with_unity(n)
            
        c = dimensional_mapping['cycle_position']
        S = dimensional_mapping['system_level']
        L = dimensional_mapping['level']
        D = dimensional_mapping['domain']
        R = dimensional_mapping['realm']
        C = dimensional_mapping['continuum']
        d = dimensional_mapping['dimension']
        
        # Analyze adjacent scale contexts
        adjacent_scale_contexts = {
            'cycle_to_system': self.analyze_adjacent_scale_context(n, c, S, 'cycle', 'system'),
            'system_to_level': self.analyze_adjacent_scale_context(n, S, L, 'system', 'level'),
            'level_to_domain': self.analyze_adjacent_scale_context(n, L, D, 'level', 'domain'),
            'domain_to_realm': self.analyze_adjacent_scale_context(n, D, R, 'domain', 'realm'),
            'realm_to_continuum': self.analyze_adjacent_scale_context(n, R, C, 'realm', 'continuum'),
            'continuum_to_dimension': self.analyze_adjacent_scale_context(n, C, d, 'continuum', 'dimension')
        }
        
        # Analyze non-adjacent scale contexts
        non_adjacent_scale_contexts = {
            'cycle_to_level': self.analyze_non_adjacent_scale_context(n, c, L, 'cycle', 'level'),
            'cycle_to_domain': self.analyze_non_adjacent_scale_context(n, c, D, 'cycle', 'domain'),
            'system_to_domain': self.analyze_non_adjacent_scale_context(n, S, D, 'system', 'domain'),
            'level_to_realm': self.analyze_non_adjacent_scale_context(n, L, R, 'level', 'realm')
        }
        
        # Calculate overall cross-scale coherence
        coherence_values = [
            adjacent_scale_contexts['cycle_to_system']['coherence'],
            adjacent_scale_contexts['system_to_level']['coherence'],
            adjacent_scale_contexts['level_to_domain']['coherence'],
            non_adjacent_scale_contexts['cycle_to_level']['coherence'],
            non_adjacent_scale_contexts['cycle_to_domain']['coherence']
        ]
        
        overall_coherence = self.calculate_cross_scale_coherence(coherence_values)
        
        return {
            'number': n,
            'dimensional_mapping': dimensional_mapping,
            'adjacent_scale_contexts': adjacent_scale_contexts,
            'non_adjacent_scale_contexts': non_adjacent_scale_contexts,
            'overall_coherence': overall_coherence
        }
    
    def analyze_adjacent_scale_context(self, n, pos1, pos2, scale1_name, scale2_name):
        """
        Analyzes context between adjacent scales.
        
        Args:
            n: Number being analyzed
            pos1: Position in first scale
            pos2: Position in second scale
            scale1_name: Name of first scale
            scale2_name: Name of second scale
            
        Returns:
            Adjacent scale context analysis
        """
        # Calculate ratio
        ratio = pos2 / pos1 if pos1 != 0 else 0
        
        # Calculate difference
        difference = pos2 - pos1
        
        # Determine relationship type
        if ratio == 1:
            relationship_type = 'identity'
        elif ratio > 1:
            relationship_type = 'expansion'
        else:
            relationship_type = 'contraction'
        
        # Calculate contextual unity across scales
        unity = self.calculate_cross_scale_unity(n, pos1, pos2, scale1_name, scale2_name)
        
        # Calculate harmony
        harmony = self.calculate_harmony(pos1, pos2)
        
        # Calculate coherence
        coherence = self.calculate_coherence(unity)
        
        return {
            'ratio': ratio,
            'difference': difference,
            'relationship_type': relationship_type,
            'unity': unity,
            'harmony': harmony,
            'coherence': coherence
        }
    
    def analyze_non_adjacent_scale_context(self, n, pos1, pos2, scale1_name, scale2_name):
        """
        Analyzes context between non-adjacent scales.
        
        Args:
            n: Number being analyzed
            pos1: Position in first scale
            pos2: Position in second scale
            scale1_name: Name of first scale
            scale2_name: Name of second scale
            
        Returns:
            Non-adjacent scale context analysis
        """
        # Calculate ratio
        ratio = pos2 / pos1 if pos1 != 0 else 0
        
        # Calculate difference
        difference = pos2 - pos1
        
        # Determine relationship type
        if ratio == 1:
            relationship_type = 'identity'
        elif ratio > 1:
            relationship_type = 'expansion'
        else:
            relationship_type = 'contraction'
        
        # Calculate contextual unity across scales
        unity = self.calculate_cross_scale_unity(n, pos1, pos2, scale1_name, scale2_name)
        
        # Calculate harmony with adjustment for non-adjacent scales
        harmony = self.calculate_harmony(pos1, pos2) * 0.8  # Reduce harmony for non-adjacent scales
        
        # Calculate coherence
        coherence = self.calculate_coherence(unity) * 0.9  # Reduce coherence for non-adjacent scales
        
        return {
            'ratio': ratio,
            'difference': difference,
            'relationship_type': relationship_type,
            'unity': unity,
            'harmony': harmony,
            'coherence': coherence
        }
    
    def calculate_cross_scale_unity(self, n, pos1, pos2, scale1_name, scale2_name):
        """
        Calculates contextual unity across different scales.
        
        Args:
            n: Number being analyzed
            pos1: Position in first scale
            pos2: Position in second scale
            scale1_name: Name of first scale
            scale2_name: Name of second scale
            
        Returns:
            Cross-scale contextual unity
        """
        # For adjacent scales, unity is calculated based on the relationship between positions
        if pos1 == 0 or pos2 == 0:
            return 0.0
            
        # Calculate unity based on the relationship between positions
        ratio = pos2 / pos1
        
        # Unity is highest when ratio is close to 1 or to the golden ratio (1.618)
        golden_ratio = 1.618
        
        # Calculate distance from ideal ratios
        distance_from_identity = abs(ratio - 1.0)
        distance_from_golden = abs(ratio - golden_ratio)
        
        # Use the minimum distance
        min_distance = min(distance_from_identity, distance_from_golden)
        
        # Convert distance to unity (1.0 for perfect match, decreasing as distance increases)
        unity = 1.0 / (1.0 + min_distance)
        
        return unity
    
    def calculate_harmony(self, pos1, pos2):
        """
        Calculates harmony between positions in different scales.
        
        Args:
            pos1: Position in first scale
            pos2: Position in second scale
            
        Returns:
            Harmony value (0-1)
        """
        if pos1 == 0 or pos2 == 0:
            return 0.0
            
        # Calculate harmony based on the relationship between positions
        # Harmony is highest when positions are related by simple ratios
        
        # Calculate ratio
        ratio = pos2 / pos1 if pos1 <= pos2 else pos1 / pos2
        
        # Simple ratios have higher harmony
        simple_ratios = [1.0, 2.0, 3.0/2.0, 4.0/3.0, 5.0/4.0, 6.0/5.0]
        
        # Calculate distance from simple ratios
        min_distance = float('inf')
        for simple_ratio in simple_ratios:
            distance = abs(ratio - simple_ratio)
            min_distance = min(min_distance, distance)
        
        # Convert distance to harmony (1.0 for perfect match, decreasing as distance increases)
        harmony = 1.0 / (1.0 + min_distance)
        
        return harmony
    
    def calculate_coherence(self, unity):
        """
        Calculates coherence based on contextual unity.
        
        Args:
            unity: Contextual unity value
            
        Returns:
            Coherence value (0-1)
        """
        # Coherence is highest when unity is exactly 1
        return 1.0 - abs(unity - 1.0)
    
    def calculate_cross_scale_coherence(self, coherence_values):
        """
        Calculates overall cross-scale coherence.
        
        Args:
            coherence_values: List of coherence values
            
        Returns:
            Overall coherence value (0-1)
        """
        # Overall coherence is the geometric mean of individual coherences
        if not coherence_values:
            return 0.0
            
        # Filter out zero values
        non_zero_values = [value for value in coherence_values if value > 0]
        if not non_zero_values:
            return 0.0
            
        # Calculate geometric mean
        product = 1.0
        for value in non_zero_values:
            product *= value
            
        return product ** (1.0 / len(non_zero_values))
    
    def analyze_multi_scale_relationships(self, n, depth=3):
        """
        Analyzes relationships across multiple scales for a number.
        
        Args:
            n: Number to analyze
            depth: Depth of analysis
            
        Returns:
            Multi-scale relationship analysis
        """
        # Get dimensional mapping
        mapping = self.dimensional_mapper.map_with_unity(n)
        
        # Analyze cross-scale context
        cross_scale_context = self.analyze_cross_scale_context(n, mapping)
        
        # Analyze scale transitions
        scale_transitions = self.analyze_scale_transitions(n, mapping, depth)
        
        # Analyze scale resonance
        scale_resonance = self.analyze_scale_resonance(n, mapping, depth)
        
        return {
            'number': n,
            'dimensional_mapping': mapping,
            'cross_scale_context': cross_scale_context,
            'scale_transitions': scale_transitions,
            'scale_resonance': scale_resonance
        }
    
    def analyze_scale_transitions(self, n, mapping, depth):
        """
        Analyzes transitions between scales.
        
        Args:
            n: Number being analyzed
            mapping: Dimensional mapping of the number
            depth: Depth of analysis
            
        Returns:
            Scale transition analysis
        """
        c = mapping['cycle_position']
        S = mapping['system_level']
        L = mapping['level']
        D = mapping['domain']
        
        # Analyze cycle-to-system transitions
        cycle_system_transitions = self.analyze_cycle_system_transitions(n, c, S, depth)
        
        # Analyze system-to-level transitions
        system_level_transitions = self.analyze_system_level_transitions(n, S, L, depth)
        
        # Analyze level-to-domain transitions
        level_domain_transitions = self.analyze_level_domain_transitions(n, L, D, depth)
        
        return {
            'cycle_system_transitions': cycle_system_transitions,
            'system_level_transitions': system_level_transitions,
            'level_domain_transitions': level_domain_transitions
        }
    
    def analyze_cycle_system_transitions(self, n, c, S, depth):
        """
        Analyzes transitions between cycles and systems.
        
        Args:
            n: Number being analyzed
            c: Cycle position
            S: System level
            depth: Depth of analysis
            
        Returns:
            Cycle-system transition analysis
        """
        transitions = []
        
        # Analyze transitions at cycle boundaries
        for cycle_pos in [1, self.dimensional_base]:
            # Calculate number at this cycle position
            cycle_n = n + (cycle_pos - c)
            if cycle_n <= 0:
                continue
                
            # Get mapping for this number
            cycle_mapping = self.dimensional_mapper.map_with_unity(cycle_n)
            
            # Check if this is a system boundary
            is_system_boundary = (cycle_pos == self.dimensional_base)
            
            # Calculate next number
            next_n = cycle_n + 1 if is_system_boundary else cycle_n
            if next_n <= 0:
                continue
                
            # Get mapping for next number
            next_mapping = self.dimensional_mapper.map_with_unity(next_n)
            
            # Check if system changes
            system_changes = (next_mapping['system_level'] != cycle_mapping['system_level'])
            
            transitions.append({
                'position': cycle_pos,
                'number': cycle_n,
                'is_system_boundary': is_system_boundary,
                'system_changes': system_changes,
                'current_mapping': cycle_mapping,
                'next_mapping': next_mapping
            })
        
        return transitions
    
    def analyze_system_level_transitions(self, n, S, L, depth):
        """
        Analyzes transitions between systems and levels.
        
        Args:
            n: Number being analyzed
            S: System level
            L: Level
            depth: Depth of analysis
            
        Returns:
            System-level transition analysis
        """
        transitions = []
        
        # Analyze transitions at system boundaries
        for system_offset in range(-depth, depth + 1):
            system_level = S + system_offset
            if system_level <= 0:
                continue
                
            # Find a representative number in this system
            system_n = self.dimensional_mapper.find_representative_number(system_level)
            if system_n is None:
                continue
                
            # Get mapping for this number
            system_mapping = self.dimensional_mapper.map_with_unity(system_n)
            
            # Check if this is a level boundary
            is_level_boundary = (system_level % self.dimensional_base == 0)
            
            # Calculate next system
            next_system = system_level + 1
            
            # Find a representative number in the next system
            next_system_n = self.dimensional_mapper.find_representative_number(next_system)
            if next_system_n is None:
                continue
                
            # Get mapping for next number
            next_mapping = self.dimensional_mapper.map_with_unity(next_system_n)
            
            # Check if level changes
            level_changes = (next_mapping['level'] != system_mapping['level'])
            
            transitions.append({
                'system_level': system_level,
                'number': system_n,
                'is_level_boundary': is_level_boundary,
                'level_changes': level_changes,
                'current_mapping': system_mapping,
                'next_mapping': next_mapping
            })
        
        return transitions
    
    def analyze_level_domain_transitions(self, n, L, D, depth):
        """
        Analyzes transitions between levels and domains.
        
        Args:
            n: Number being analyzed
            L: Level
            D: Domain
            depth: Depth of analysis
            
        Returns:
            Level-domain transition analysis
        """
        transitions = []
        
        # Analyze transitions at level boundaries
        for level_offset in range(-depth, depth + 1):
            level = L + level_offset
            if level <= 0 or level > self.dimensional_base:
                continue
                
            # Find a representative number in this level
            level_n = self.dimensional_mapper.find_representative_number_in_level(level, D)
            if level_n is None:
                continue
                
            # Get mapping for this number
            level_mapping = self.dimensional_mapper.map_with_unity(level_n)
            
            # Check if this is a domain boundary
            is_domain_boundary = (level == self.dimensional_base)
            
            # Calculate next level or domain
            if is_domain_boundary:
                next_level = 1
                next_domain = D + 1
            else:
                next_level = level + 1
                next_domain = D
                
            # Find a representative number in the next level/domain
            next_n = self.dimensional_mapper.find_representative_number_in_level(next_level, next_domain)
            if next_n is None:
                continue
                
            # Get mapping for next number
            next_mapping = self.dimensional_mapper.map_with_unity(next_n)
            
            # Check if domain changes
            domain_changes = (next_mapping['domain'] != level_mapping['domain'])
            
            transitions.append({
                'level': level,
                'domain': D,
                'number': level_n,
                'is_domain_boundary': is_domain_boundary,
                'domain_changes': domain_changes,
                'current_mapping': level_mapping,
                'next_mapping': next_mapping
            })
        
        return transitions
    
    def analyze_scale_resonance(self, n, mapping, depth):
        """
        Analyzes resonance between scales.
        
        Args:
            n: Number being analyzed
            mapping: Dimensional mapping of the number
            depth: Depth of analysis
            
        Returns:
            Scale resonance analysis
        """
        c = mapping['cycle_position']
        S = mapping['system_level']
        L = mapping['level']
        D = mapping['domain']
        
        # Analyze resonance between cycle and system
        cycle_system_resonance = self.analyze_cycle_system_resonance(c, S)
        
        # Analyze resonance between system and level
        system_level_resonance = self.analyze_system_level_resonance(S, L)
        
        # Analyze resonance between level and domain
        level_domain_resonance = self.analyze_level_domain_resonance(L, D)
        
        # Calculate overall resonance
        resonance_values = [
            cycle_system_resonance['resonance_strength'],
            system_level_resonance['resonance_strength'],
            level_domain_resonance['resonance_strength']
        ]
        
        overall_resonance = sum(resonance_values) / len(resonance_values)
        
        return {
            'cycle_system_resonance': cycle_system_resonance,
            'system_level_resonance': system_level_resonance,
            'level_domain_resonance': level_domain_resonance,
            'overall_resonance': overall_resonance
        }
    
    def analyze_cycle_system_resonance(self, c, S):
        """
        Analyzes resonance between cycle and system.
        
        Args:
            c: Cycle position
            S: System level
            
        Returns:
            Cycle-system resonance analysis
        """
        # Calculate resonance based on relationship between c and S
        
        # Resonance is strongest when c and S are related by simple ratios
        ratio = S / c if c <= S else c / S
        
        # Simple ratios have stronger resonance
        simple_ratios = [1.0, 2.0, 3.0/2.0, 4.0/3.0, 5.0/4.0, 6.0/5.0]
        
        # Calculate distance from simple ratios
        min_distance = float('inf')
        closest_ratio = 1.0
        for simple_ratio in simple_ratios:
            distance = abs(ratio - simple_ratio)
            if distance < min_distance:
                min_distance = distance
                closest_ratio = simple_ratio
        
        # Convert distance to resonance strength (1.0 for perfect match, decreasing as distance increases)
        resonance_strength = 1.0 / (1.0 + min_distance)
        
        # Determine resonance type
        if closest_ratio == 1.0:
            resonance_type = 'unison'
        elif closest_ratio == 2.0:
            resonance_type = 'octave'
        elif closest_ratio == 3.0/2.0:
            resonance_type = 'perfect_fifth'
        elif closest_ratio == 4.0/3.0:
            resonance_type = 'perfect_fourth'
        elif closest_ratio == 5.0/4.0:
            resonance_type = 'major_third'
        elif closest_ratio == 6.0/5.0:
            resonance_type = 'minor_third'
        else:
            resonance_type = 'complex'
        
        return {
            'cycle_position': c,
            'system_level': S,
            'ratio': ratio,
            'closest_simple_ratio': closest_ratio,
            'resonance_type': resonance_type,
            'resonance_strength': resonance_strength
        }
    
    def analyze_system_level_resonance(self, S, L):
        """
        Analyzes resonance between system and level.
        
        Args:
            S: System level
            L: Level
            
        Returns:
            System-level resonance analysis
        """
        # Calculate resonance based on relationship between S and L
        
        # Resonance is strongest when S and L are related by simple ratios
        ratio = S / L if L <= S else L / S
        
        # Simple ratios have stronger resonance
        simple_ratios = [1.0, 2.0, 3.0/2.0, 4.0/3.0, 5.0/4.0, 6.0/5.0]
        
        # Calculate distance from simple ratios
        min_distance = float('inf')
        closest_ratio = 1.0
        for simple_ratio in simple_ratios:
            distance = abs(ratio - simple_ratio)
            if distance < min_distance:
                min_distance = distance
                closest_ratio = simple_ratio
        
        # Convert distance to resonance strength (1.0 for perfect match, decreasing as distance increases)
        resonance_strength = 1.0 / (1.0 + min_distance)
        
        # Determine resonance type
        if closest_ratio == 1.0:
            resonance_type = 'unison'
        elif closest_ratio == 2.0:
            resonance_type = 'octave'
        elif closest_ratio == 3.0/2.0:
            resonance_type = 'perfect_fifth'
        elif closest_ratio == 4.0/3.0:
            resonance_type = 'perfect_fourth'
        elif closest_ratio == 5.0/4.0:
            resonance_type = 'major_third'
        elif closest_ratio == 6.0/5.0:
            resonance_type = 'minor_third'
        else:
            resonance_type = 'complex'
        
        return {
            'system_level': S,
            'level': L,
            'ratio': ratio,
            'closest_simple_ratio': closest_ratio,
            'resonance_type': resonance_type,
            'resonance_strength': resonance_strength
        }
    
    def analyze_level_domain_resonance(self, L, D):
        """
        Analyzes resonance between level and domain.
        
        Args:
            L: Level
            D: Domain
            
        Returns:
            Level-domain resonance analysis
        """
        # Calculate resonance based on relationship between L and D
        
        # Resonance is strongest when L and D are related by simple ratios
        ratio = D / L if L <= D else L / D
        
        # Simple ratios have stronger resonance
        simple_ratios = [1.0, 2.0, 3.0/2.0, 4.0/3.0, 5.0/4.0, 6.0/5.0]
        
        # Calculate distance from simple ratios
        min_distance = float('inf')
        closest_ratio = 1.0
        for simple_ratio in simple_ratios:
            distance = abs(ratio - simple_ratio)
            if distance < min_distance:
                min_distance = distance
                closest_ratio = simple_ratio
        
        # Convert distance to resonance strength (1.0 for perfect match, decreasing as distance increases)
        resonance_strength = 1.0 / (1.0 + min_distance)
        
        # Determine resonance type
        if closest_ratio == 1.0:
            resonance_type = 'unison'
        elif closest_ratio == 2.0:
            resonance_type = 'octave'
        elif closest_ratio == 3.0/2.0:
            resonance_type = 'perfect_fifth'
        elif closest_ratio == 4.0/3.0:
            resonance_type = 'perfect_fourth'
        elif closest_ratio == 5.0/4.0:
            resonance_type = 'major_third'
        elif closest_ratio == 6.0/5.0:
            resonance_type = 'minor_third'
        else:
            resonance_type = 'complex'
        
        return {
            'level': L,
            'domain': D,
            'ratio': ratio,
            'closest_simple_ratio': closest_ratio,
            'resonance_type': resonance_type,
            'resonance_strength': resonance_strength
        }


# Test function
def test_cross_scale_context_analyzer():
    """
    Tests the CrossScaleContextAnalyzer class.
    """
    analyzer = CrossScaleContextAnalyzer()
    
    # Test for a few numbers
    test_cases = [1, 13, 14, 170]
    
    for n in test_cases:
        # Analyze cross-scale context
        context = analyzer.analyze_cross_scale_context(n)
        print(f"Number {n}:")
        print(f"  Overall coherence: {context['overall_coherence']}")
        
        # Print adjacent scale contexts
        print("  Adjacent scale contexts:")
        for scale_pair, scale_context in context['adjacent_scale_contexts'].items():
            print(f"    {scale_pair}: coherence = {scale_context['coherence']}, relationship = {scale_context['relationship_type']}")
        
        print()
    
    # Test multi-scale relationships
    n = 42
    relationships = analyzer.analyze_multi_scale_relationships(n, depth=2)
    print(f"Multi-scale relationships for number {n}:")
    print(f"  Overall resonance: {relationships['scale_resonance']['overall_resonance']}")
    print(f"  Cycle-system resonance: {relationships['scale_resonance']['cycle_system_resonance']['resonance_type']} ({relationships['scale_resonance']['cycle_system_resonance']['resonance_strength']})")
    print(f"  System-level resonance: {relationships['scale_resonance']['system_level_resonance']['resonance_type']} ({relationships['scale_resonance']['system_level_resonance']['resonance_strength']})")
    print(f"  Level-domain resonance: {relationships['scale_resonance']['level_domain_resonance']['resonance_type']} ({relationships['scale_resonance']['level_domain_resonance']['resonance_strength']})")


if __name__ == "__main__":
    test_cross_scale_context_analyzer()
