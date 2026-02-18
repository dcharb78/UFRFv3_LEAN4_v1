"""
Resonance Pattern Recognizer for UFRF Framework

This module implements the Resonance Pattern Recognizer component that identifies
resonance patterns that maintain contextual unity in the UFRF Framework.

Author: Daniel Charboneau
License: Creative Commons Attribution-NonCommercial 4.0 International
"""

import numpy as np
from collections import defaultdict

# Use relative imports for modules in the same package
from .contextual_unity_detector import ContextualUnityDetector
from .enhanced_dimensional_mapper import EnhancedDimensionalMapper
from .cross_scale_context_analyzer import CrossScaleContextAnalyzer

class ResonancePatternRecognizer:
    """
    Recognizes resonance patterns that maintain contextual unity.
    """
    
    def __init__(self, dimensional_base=13):
        """
        Initialize the resonance pattern recognizer.
        
        Args:
            dimensional_base: Base for dimensional calculations (default: 13)
        """
        self.dimensional_base = dimensional_base
        self.unity_detector = ContextualUnityDetector(dimensional_base)
        self.dimensional_mapper = EnhancedDimensionalMapper(dimensional_base)
        self.context_analyzer = CrossScaleContextAnalyzer(dimensional_base)
        
        # Define resonance pattern types
        self.resonance_types = {
            'intra_scale': ['cycle', 'system', 'level', 'domain'],
            'cross_scale': ['cycle_to_system', 'system_to_level', 'level_to_domain', 'cycle_to_level', 'cycle_to_domain'],
            'harmonic': ['first_order', 'second_order', 'third_order']
        }
        
        # Define resonance pattern characteristics
        self.pattern_characteristics = {
            'identity': {'strength': 1.0, 'stability': 'high', 'coherence': 'perfect'},
            'complementary': {'strength': 0.9, 'stability': 'high', 'coherence': 'strong'},
            'harmonic': {'strength': 0.8, 'stability': 'medium', 'coherence': 'strong'},
            'golden_ratio': {'strength': 0.85, 'stability': 'high', 'coherence': 'strong'},
            'fibonacci': {'strength': 0.75, 'stability': 'medium', 'coherence': 'moderate'},
            'octave': {'strength': 0.7, 'stability': 'medium', 'coherence': 'moderate'},
            'fifth': {'strength': 0.65, 'stability': 'medium', 'coherence': 'moderate'},
            'fourth': {'strength': 0.6, 'stability': 'low', 'coherence': 'weak'},
            'third': {'strength': 0.55, 'stability': 'low', 'coherence': 'weak'},
            'dissonant': {'strength': 0.3, 'stability': 'very_low', 'coherence': 'weak'}
        }
    
    def recognize_resonance_patterns(self, n, dimensional_mapping=None, previous_mappings=None):
        """
        Recognizes resonance patterns that maintain contextual unity.
        
        Args:
            n: Number being analyzed
            dimensional_mapping: Dimensional mapping of the number (optional)
            previous_mappings: Previous dimensional mappings (optional)
            
        Returns:
            Recognized resonance patterns
        """
        # Get dimensional mapping if not provided
        if dimensional_mapping is None:
            dimensional_mapping = self.dimensional_mapper.map_with_unity(n)
            
        c = dimensional_mapping['cycle_position']
        S = dimensional_mapping['system_level']
        L = dimensional_mapping['level']
        D = dimensional_mapping['domain']
        
        # Initialize previous mappings if not provided
        if previous_mappings is None:
            previous_mappings = []
            
        # Recognize intra-scale resonance patterns
        intra_scale_patterns = self.recognize_intra_scale_patterns(n, c, S, L, D, previous_mappings)
        
        # Recognize cross-scale resonance patterns
        cross_scale_patterns = self.recognize_cross_scale_patterns(n, c, S, L, D, previous_mappings)
        
        # Recognize harmonic resonance patterns
        harmonic_patterns = self.recognize_harmonic_patterns(n, c, S, L, D, previous_mappings)
        
        # Calculate overall resonance strength
        overall_strength = self.calculate_overall_resonance_strength(
            intra_scale_patterns['strength'],
            cross_scale_patterns['strength'],
            harmonic_patterns['strength']
        )
        
        return {
            'number': n,
            'dimensional_mapping': dimensional_mapping,
            'intra_scale': intra_scale_patterns,
            'cross_scale': cross_scale_patterns,
            'harmonic': harmonic_patterns,
            'overall_strength': overall_strength
        }
    
    def recognize_intra_scale_patterns(self, n, c, S, L, D, previous_mappings):
        """
        Recognizes resonance patterns within a single scale.
        
        Args:
            n: Number being analyzed
            c, S, L, D: Dimensional mapping
            previous_mappings: Previous dimensional mappings
            
        Returns:
            Intra-scale resonance patterns
        """
        # Recognize cycle resonance patterns
        cycle_resonance = self.recognize_cycle_resonance(n, c, previous_mappings)
        
        # Recognize system resonance patterns
        system_resonance = self.recognize_system_resonance(n, S, previous_mappings)
        
        # Recognize level resonance patterns
        level_resonance = self.recognize_level_resonance(n, L, previous_mappings)
        
        # Recognize domain resonance patterns
        domain_resonance = self.recognize_domain_resonance(n, D, previous_mappings)
        
        # Calculate overall intra-scale resonance strength
        strength = (
            cycle_resonance['strength'] +
            system_resonance['strength'] +
            level_resonance['strength'] +
            domain_resonance['strength']
        ) / 4
        
        return {
            'cycle_resonance': cycle_resonance,
            'system_resonance': system_resonance,
            'level_resonance': level_resonance,
            'domain_resonance': domain_resonance,
            'strength': strength
        }
    
    def recognize_cycle_resonance(self, n, c, previous_mappings):
        """
        Recognizes resonance patterns within the cycle.
        
        Args:
            n: Number being analyzed
            c: Cycle position
            previous_mappings: Previous dimensional mappings
            
        Returns:
            Cycle resonance patterns
        """
        # Get position characteristics
        characteristics = self.unity_detector.get_position_characteristics(c)
        
        # Find resonant positions within the cycle
        resonant_positions = []
        for pos in range(1, self.dimensional_base + 1):
            if pos == c:
                continue  # Skip the position itself
                
            pos_characteristics = self.unity_detector.get_position_characteristics(pos)
            
            # Check if positions resonate
            if self.positions_resonate(characteristics, pos_characteristics):
                resonant_positions.append(pos)
        
        # Identify resonance patterns
        patterns = []
        
        # Check for seed phase resonance
        if c in [1, 2, 3] and any(pos in [1, 2, 3] for pos in resonant_positions):
            patterns.append('seed_phase')
        
        # Check for inner octave resonance
        if c in [4, 5, 6, 7, 8, 9] and any(pos in [4, 5, 6, 7, 8, 9] for pos in resonant_positions):
            patterns.append('inner_octave')
        
        # Check for next seed resonance
        if c in [11, 12, 13] and any(pos in [11, 12, 13] for pos in resonant_positions):
            patterns.append('next_seed')
        
        # Check for polarity resonance
        if characteristics['polarity'] == 'positive' and any(
            self.unity_detector.get_position_characteristics(pos)['polarity'] == 'positive'
            for pos in resonant_positions
        ):
            patterns.append('positive_polarity')
        
        if characteristics['polarity'] == 'negative' and any(
            self.unity_detector.get_position_characteristics(pos)['polarity'] == 'negative'
            for pos in resonant_positions
        ):
            patterns.append('negative_polarity')
        
        # Calculate resonance strength
        strength = len(resonant_positions) / (self.dimensional_base - 1)
        
        return {
            'position': c,
            'characteristics': characteristics,
            'resonant_positions': resonant_positions,
            'patterns': patterns,
            'strength': strength
        }
    
    def recognize_system_resonance(self, n, S, previous_mappings):
        """
        Recognizes resonance patterns within the system level.
        
        Args:
            n: Number being analyzed
            S: System level
            previous_mappings: Previous dimensional mappings
            
        Returns:
            System resonance patterns
        """
        # Find systems with resonant properties
        resonant_systems = []
        
        # Check for systems that are multiples or factors of the current system
        for system_level in range(1, S * 2):
            if system_level == S:
                continue  # Skip the system itself
                
            # Check if systems resonate
            if self.systems_resonate(S, system_level):
                resonant_systems.append(system_level)
        
        # Identify resonance patterns
        patterns = []
        
        # Check for harmonic system resonance
        if any(S % system == 0 or system % S == 0 for system in resonant_systems):
            patterns.append('harmonic')
        
        # Check for fibonacci system resonance
        fibonacci_numbers = self.generate_fibonacci_numbers(S * 2)
        if S in fibonacci_numbers and any(system in fibonacci_numbers for system in resonant_systems):
            patterns.append('fibonacci')
        
        # Check for prime system resonance
        if self.is_prime(S) and any(self.is_prime(system) for system in resonant_systems):
            patterns.append('prime')
        
        # Calculate resonance strength
        strength = len(resonant_systems) / (S * 2 - 1) if S * 2 - 1 > 0 else 0
        
        return {
            'system_level': S,
            'resonant_systems': resonant_systems,
            'patterns': patterns,
            'strength': strength
        }
    
    def recognize_level_resonance(self, n, L, previous_mappings):
        """
        Recognizes resonance patterns within the level.
        
        Args:
            n: Number being analyzed
            L: Level
            previous_mappings: Previous dimensional mappings
            
        Returns:
            Level resonance patterns
        """
        # Find levels with resonant properties
        resonant_levels = []
        
        # Check for levels that resonate with the current level
        for level in range(1, self.dimensional_base + 1):
            if level == L:
                continue  # Skip the level itself
                
            # Check if levels resonate
            if self.levels_resonate(L, level):
                resonant_levels.append(level)
        
        # Identify resonance patterns
        patterns = []
        
        # Check for complementary level resonance
        if self.dimensional_base + 1 - L in resonant_levels:
            patterns.append('complementary')
        
        # Check for harmonic level resonance
        if any(L % level == 0 or level % L == 0 for level in resonant_levels):
            patterns.append('harmonic')
        
        # Check for golden ratio level resonance
        golden_ratio = 1.618
        for level in resonant_levels:
            ratio = max(L, level) / min(L, level)
            if abs(ratio - golden_ratio) < 0.1:
                patterns.append('golden_ratio')
                break
        
        # Calculate resonance strength
        strength = len(resonant_levels) / (self.dimensional_base - 1)
        
        return {
            'level': L,
            'resonant_levels': resonant_levels,
            'patterns': patterns,
            'strength': strength
        }
    
    def recognize_domain_resonance(self, n, D, previous_mappings):
        """
        Recognizes resonance patterns within the domain.
        
        Args:
            n: Number being analyzed
            D: Domain
            previous_mappings: Previous dimensional mappings
            
        Returns:
            Domain resonance patterns
        """
        # Find domains with resonant properties
        resonant_domains = []
        
        # Check for domains that are multiples or factors of the current domain
        for domain in range(1, D * 2):
            if domain == D:
                continue  # Skip the domain itself
                
            # Check if domains resonate
            if self.domains_resonate(D, domain):
                resonant_domains.append(domain)
        
        # Identify resonance patterns
        patterns = []
        
        # Check for harmonic domain resonance
        if any(D % domain == 0 or domain % D == 0 for domain in resonant_domains):
            patterns.append('harmonic')
        
        # Check for fibonacci domain resonance
        fibonacci_numbers = self.generate_fibonacci_numbers(D * 2)
        if D in fibonacci_numbers and any(domain in fibonacci_numbers for domain in resonant_domains):
            patterns.append('fibonacci')
        
        # Check for prime domain resonance
        if self.is_prime(D) and any(self.is_prime(domain) for domain in resonant_domains):
            patterns.append('prime')
        
        # Calculate resonance strength
        strength = len(resonant_domains) / (D * 2 - 1) if D * 2 - 1 > 0 else 0
        
        return {
            'domain': D,
            'resonant_domains': resonant_domains,
            'patterns': patterns,
            'strength': strength
        }
    
    def recognize_cross_scale_patterns(self, n, c, S, L, D, previous_mappings):
        """
        Recognizes resonance patterns across different scales.
        
        Args:
            n: Number being analyzed
            c, S, L, D: Dimensional mapping
            previous_mappings: Previous dimensional mappings
            
        Returns:
            Cross-scale resonance patterns
        """
        # Recognize cycle-to-system resonance patterns
        cycle_to_system = self.recognize_cycle_to_system_resonance(n, c, S)
        
        # Recognize system-to-level resonance patterns
        system_to_level = self.recognize_system_to_level_resonance(n, S, L)
        
        # Recognize level-to-domain resonance patterns
        level_to_domain = self.recognize_level_to_domain_resonance(n, L, D)
        
        # Recognize cycle-to-level resonance patterns
        cycle_to_level = self.recognize_cycle_to_level_resonance(n, c, L)
        
        # Recognize cycle-to-domain resonance patterns
        cycle_to_domain = self.recognize_cycle_to_domain_resonance(n, c, D)
        
        # Calculate overall cross-scale resonance strength
        strength = (
            cycle_to_system['strength'] +
            system_to_level['strength'] +
            level_to_domain['strength'] +
            cycle_to_level['strength'] +
            cycle_to_domain['strength']
        ) / 5
        
        return {
            'cycle_to_system': cycle_to_system,
            'system_to_level': system_to_level,
            'level_to_domain': level_to_domain,
            'cycle_to_level': cycle_to_level,
            'cycle_to_domain': cycle_to_domain,
            'strength': strength
        }
    
    def recognize_cycle_to_system_resonance(self, n, c, S):
        """
        Recognizes resonance patterns between cycle and system.
        
        Args:
            n: Number being analyzed
            c: Cycle position
            S: System level
            
        Returns:
            Cycle-to-system resonance patterns
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
        strength = 1.0 / (1.0 + min_distance)
        
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
        
        # Identify resonance patterns
        patterns = []
        
        # Check for identity resonance
        if c == S:
            patterns.append('identity')
        
        # Check for harmonic resonance
        if c % S == 0 or S % c == 0:
            patterns.append('harmonic')
        
        # Check for golden ratio resonance
        golden_ratio = 1.618
        if abs(ratio - golden_ratio) < 0.1:
            patterns.append('golden_ratio')
        
        return {
            'cycle_position': c,
            'system_level': S,
            'ratio': ratio,
            'closest_simple_ratio': closest_ratio,
            'resonance_type': resonance_type,
            'patterns': patterns,
            'strength': strength
        }
    
    def recognize_system_to_level_resonance(self, n, S, L):
        """
        Recognizes resonance patterns between system and level.
        
        Args:
            n: Number being analyzed
            S: System level
            L: Level
            
        Returns:
            System-to-level resonance patterns
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
        strength = 1.0 / (1.0 + min_distance)
        
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
        
        # Identify resonance patterns
        patterns = []
        
        # Check for identity resonance
        if S == L:
            patterns.append('identity')
        
        # Check for harmonic resonance
        if S % L == 0 or L % S == 0:
            patterns.append('harmonic')
        
        # Check for golden ratio resonance
        golden_ratio = 1.618
        if abs(ratio - golden_ratio) < 0.1:
            patterns.append('golden_ratio')
        
        return {
            'system_level': S,
            'level': L,
            'ratio': ratio,
            'closest_simple_ratio': closest_ratio,
            'resonance_type': resonance_type,
            'patterns': patterns,
            'strength': strength
        }
    
    def recognize_level_to_domain_resonance(self, n, L, D):
        """
        Recognizes resonance patterns between level and domain.
        
        Args:
            n: Number being analyzed
            L: Level
            D: Domain
            
        Returns:
            Level-to-domain resonance patterns
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
        strength = 1.0 / (1.0 + min_distance)
        
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
        
        # Identify resonance patterns
        patterns = []
        
        # Check for identity resonance
        if L == D:
            patterns.append('identity')
        
        # Check for harmonic resonance
        if L % D == 0 or D % L == 0:
            patterns.append('harmonic')
        
        # Check for golden ratio resonance
        golden_ratio = 1.618
        if abs(ratio - golden_ratio) < 0.1:
            patterns.append('golden_ratio')
        
        return {
            'level': L,
            'domain': D,
            'ratio': ratio,
            'closest_simple_ratio': closest_ratio,
            'resonance_type': resonance_type,
            'patterns': patterns,
            'strength': strength
        }
    
    def recognize_cycle_to_level_resonance(self, n, c, L):
        """
        Recognizes resonance patterns between cycle and level.
        
        Args:
            n: Number being analyzed
            c: Cycle position
            L: Level
            
        Returns:
            Cycle-to-level resonance patterns
        """
        # Calculate resonance based on relationship between c and L
        
        # Resonance is strongest when c and L are related by simple ratios
        ratio = L / c if c <= L else c / L
        
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
        # Reduce strength for non-adjacent scales
        strength = (1.0 / (1.0 + min_distance)) * 0.9
        
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
        
        # Identify resonance patterns
        patterns = []
        
        # Check for identity resonance
        if c == L:
            patterns.append('identity')
        
        # Check for harmonic resonance
        if c % L == 0 or L % c == 0:
            patterns.append('harmonic')
        
        # Check for golden ratio resonance
        golden_ratio = 1.618
        if abs(ratio - golden_ratio) < 0.1:
            patterns.append('golden_ratio')
        
        return {
            'cycle_position': c,
            'level': L,
            'ratio': ratio,
            'closest_simple_ratio': closest_ratio,
            'resonance_type': resonance_type,
            'patterns': patterns,
            'strength': strength
        }
    
    def recognize_cycle_to_domain_resonance(self, n, c, D):
        """
        Recognizes resonance patterns between cycle and domain.
        
        Args:
            n: Number being analyzed
            c: Cycle position
            D: Domain
            
        Returns:
            Cycle-to-domain resonance patterns
        """
        # Calculate resonance based on relationship between c and D
        
        # Resonance is strongest when c and D are related by simple ratios
        ratio = D / c if c <= D else c / D
        
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
        # Reduce strength for non-adjacent scales
        strength = (1.0 / (1.0 + min_distance)) * 0.8
        
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
        
        # Identify resonance patterns
        patterns = []
        
        # Check for identity resonance
        if c == D:
            patterns.append('identity')
        
        # Check for harmonic resonance
        if c % D == 0 or D % c == 0:
            patterns.append('harmonic')
        
        # Check for golden ratio resonance
        golden_ratio = 1.618
        if abs(ratio - golden_ratio) < 0.1:
            patterns.append('golden_ratio')
        
        return {
            'cycle_position': c,
            'domain': D,
            'ratio': ratio,
            'closest_simple_ratio': closest_ratio,
            'resonance_type': resonance_type,
            'patterns': patterns,
            'strength': strength
        }
    
    def recognize_harmonic_patterns(self, n, c, S, L, D, previous_mappings):
        """
        Recognizes harmonic resonance patterns.
        
        Args:
            n: Number being analyzed
            c, S, L, D: Dimensional mapping
            previous_mappings: Previous dimensional mappings
            
        Returns:
            Harmonic resonance patterns
        """
        # Recognize first-order harmonic patterns
        first_order = self.recognize_first_order_harmonics(n, c, S, L, D)
        
        # Recognize second-order harmonic patterns
        second_order = self.recognize_second_order_harmonics(n, c, S, L, D)
        
        # Recognize third-order harmonic patterns
        third_order = self.recognize_third_order_harmonics(n, c, S, L, D)
        
        # Calculate overall harmonic resonance strength
        strength = (
            first_order['strength'] +
            second_order['strength'] * 0.8 +
            third_order['strength'] * 0.6
        ) / 2.4
        
        return {
            'first_order': first_order,
            'second_order': second_order,
            'third_order': third_order,
            'strength': strength
        }
    
    def recognize_first_order_harmonics(self, n, c, S, L, D):
        """
        Recognizes first-order harmonic patterns.
        
        Args:
            n: Number being analyzed
            c, S, L, D: Dimensional mapping
            
        Returns:
            First-order harmonic patterns
        """
        # First-order harmonics are direct multiples or factors of the number
        harmonics = []
        
        # Check for harmonics that are multiples or factors of the number
        for factor in range(1, int(n**0.5) + 1):
            if n % factor == 0:
                # Add both factor and its complement
                harmonics.append(factor)
                if factor != n // factor:
                    harmonics.append(n // factor)
        
        # Remove the number itself
        if n in harmonics:
            harmonics.remove(n)
        
        # Identify harmonic patterns
        patterns = []
        
        # Check for octave harmonic
        if n * 2 in harmonics or n // 2 in harmonics:
            patterns.append('octave')
        
        # Check for perfect fifth harmonic
        if int(n * 3 / 2) in harmonics or int(n * 2 / 3) in harmonics:
            patterns.append('perfect_fifth')
        
        # Check for perfect fourth harmonic
        if int(n * 4 / 3) in harmonics or int(n * 3 / 4) in harmonics:
            patterns.append('perfect_fourth')
        
        # Calculate harmonic strength
        strength = len(harmonics) / n if n > 0 else 0
        
        return {
            'number': n,
            'harmonics': harmonics,
            'patterns': patterns,
            'strength': min(strength, 1.0)  # Cap at 1.0
        }
    
    def recognize_second_order_harmonics(self, n, c, S, L, D):
        """
        Recognizes second-order harmonic patterns.
        
        Args:
            n: Number being analyzed
            c, S, L, D: Dimensional mapping
            
        Returns:
            Second-order harmonic patterns
        """
        # Second-order harmonics involve relationships between dimensional components
        harmonics = []
        
        # Check for harmonics between dimensional components
        if c * S == n:
            harmonics.append(('c*S', c, S))
        
        if c * L == n:
            harmonics.append(('c*L', c, L))
        
        if S * L == n:
            harmonics.append(('S*L', S, L))
        
        if c * D == n:
            harmonics.append(('c*D', c, D))
        
        if S * D == n:
            harmonics.append(('S*D', S, D))
        
        if L * D == n:
            harmonics.append(('L*D', L, D))
        
        # Identify harmonic patterns
        patterns = []
        
        # Check for cycle-system harmonic
        if ('c*S', c, S) in harmonics:
            patterns.append('cycle_system')
        
        # Check for system-level harmonic
        if ('S*L', S, L) in harmonics:
            patterns.append('system_level')
        
        # Check for level-domain harmonic
        if ('L*D', L, D) in harmonics:
            patterns.append('level_domain')
        
        # Calculate harmonic strength
        strength = len(harmonics) / 6  # 6 possible relationships
        
        return {
            'number': n,
            'harmonics': harmonics,
            'patterns': patterns,
            'strength': strength
        }
    
    def recognize_third_order_harmonics(self, n, c, S, L, D):
        """
        Recognizes third-order harmonic patterns.
        
        Args:
            n: Number being analyzed
            c, S, L, D: Dimensional mapping
            
        Returns:
            Third-order harmonic patterns
        """
        # Third-order harmonics involve complex relationships between dimensional components
        harmonics = []
        
        # Check for harmonics involving three or more dimensional components
        if c * S * L == n:
            harmonics.append(('c*S*L', c, S, L))
        
        if c * S * D == n:
            harmonics.append(('c*S*D', c, S, D))
        
        if c * L * D == n:
            harmonics.append(('c*L*D', c, L, D))
        
        if S * L * D == n:
            harmonics.append(('S*L*D', S, L, D))
        
        if c * S * L * D == n:
            harmonics.append(('c*S*L*D', c, S, L, D))
        
        # Identify harmonic patterns
        patterns = []
        
        # Check for full dimensional harmonic
        if ('c*S*L*D', c, S, L, D) in harmonics:
            patterns.append('full_dimensional')
        
        # Check for triple component harmonic
        if len([h for h in harmonics if len(h) == 4]) > 0:
            patterns.append('triple_component')
        
        # Calculate harmonic strength
        strength = len(harmonics) / 5  # 5 possible relationships
        
        return {
            'number': n,
            'harmonics': harmonics,
            'patterns': patterns,
            'strength': strength
        }
    
    def calculate_overall_resonance_strength(self, intra_scale_strength, cross_scale_strength, harmonic_strength):
        """
        Calculates overall resonance strength.
        
        Args:
            intra_scale_strength: Intra-scale resonance strength
            cross_scale_strength: Cross-scale resonance strength
            harmonic_strength: Harmonic resonance strength
            
        Returns:
            Overall resonance strength
        """
        # Weight the different types of resonance
        weighted_strength = (
            intra_scale_strength * 0.4 +
            cross_scale_strength * 0.4 +
            harmonic_strength * 0.2
        )
        
        return weighted_strength
    
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
    
    def systems_resonate(self, S1, S2):
        """
        Determines if two systems resonate with each other.
        
        Args:
            S1: First system level
            S2: Second system level
            
        Returns:
            True if systems resonate, False otherwise
        """
        # Systems resonate if they are related by simple ratios
        if S1 == 0 or S2 == 0:
            return False
            
        # Calculate ratio
        ratio = S1 / S2 if S2 <= S1 else S2 / S1
        
        # Check if ratio is close to a simple ratio
        simple_ratios = [1.0, 2.0, 3.0/2.0, 4.0/3.0, 5.0/4.0, 6.0/5.0]
        
        for simple_ratio in simple_ratios:
            if abs(ratio - simple_ratio) < 0.1:
                return True
                
        # Check if one is a multiple of the other
        if S1 % S2 == 0 or S2 % S1 == 0:
            return True
            
        # Check if both are in the Fibonacci sequence
        fibonacci_numbers = self.generate_fibonacci_numbers(max(S1, S2) * 2)
        if S1 in fibonacci_numbers and S2 in fibonacci_numbers:
            return True
            
        # Check if both are prime
        if self.is_prime(S1) and self.is_prime(S2):
            return True
            
        return False
    
    def levels_resonate(self, L1, L2):
        """
        Determines if two levels resonate with each other.
        
        Args:
            L1: First level
            L2: Second level
            
        Returns:
            True if levels resonate, False otherwise
        """
        # Levels resonate if they are related by simple ratios
        if L1 == 0 or L2 == 0:
            return False
            
        # Calculate ratio
        ratio = L1 / L2 if L2 <= L1 else L2 / L1
        
        # Check if ratio is close to a simple ratio
        simple_ratios = [1.0, 2.0, 3.0/2.0, 4.0/3.0, 5.0/4.0, 6.0/5.0]
        
        for simple_ratio in simple_ratios:
            if abs(ratio - simple_ratio) < 0.1:
                return True
                
        # Check if one is a multiple of the other
        if L1 % L2 == 0 or L2 % L1 == 0:
            return True
            
        # Check if they are complementary within the dimensional base
        if L1 + L2 == self.dimensional_base + 1:
            return True
            
        # Check if both are in the Fibonacci sequence
        fibonacci_numbers = self.generate_fibonacci_numbers(self.dimensional_base * 2)
        if L1 in fibonacci_numbers and L2 in fibonacci_numbers:
            return True
            
        return False
    
    def domains_resonate(self, D1, D2):
        """
        Determines if two domains resonate with each other.
        
        Args:
            D1: First domain
            D2: Second domain
            
        Returns:
            True if domains resonate, False otherwise
        """
        # Domains resonate if they are related by simple ratios
        if D1 == 0 or D2 == 0:
            return False
            
        # Calculate ratio
        ratio = D1 / D2 if D2 <= D1 else D2 / D1
        
        # Check if ratio is close to a simple ratio
        simple_ratios = [1.0, 2.0, 3.0/2.0, 4.0/3.0, 5.0/4.0, 6.0/5.0]
        
        for simple_ratio in simple_ratios:
            if abs(ratio - simple_ratio) < 0.1:
                return True
                
        # Check if one is a multiple of the other
        if D1 % D2 == 0 or D2 % D1 == 0:
            return True
            
        # Check if both are in the Fibonacci sequence
        fibonacci_numbers = self.generate_fibonacci_numbers(max(D1, D2) * 2)
        if D1 in fibonacci_numbers and D2 in fibonacci_numbers:
            return True
            
        # Check if both are prime
        if self.is_prime(D1) and self.is_prime(D2):
            return True
            
        return False
    
    def generate_fibonacci_numbers(self, limit):
        """
        Generates Fibonacci numbers up to a limit.
        
        Args:
            limit: Upper limit for Fibonacci numbers
            
        Returns:
            List of Fibonacci numbers
        """
        fibonacci = [1, 1]
        while fibonacci[-1] + fibonacci[-2] <= limit:
            fibonacci.append(fibonacci[-1] + fibonacci[-2])
        return fibonacci
    
    def is_prime(self, n):
        """
        Determines if a number is prime.
        
        Args:
            n: Number to check
            
        Returns:
            True if the number is prime, False otherwise
        """
        if n <= 1:
            return False
        if n <= 3:
            return True
        if n % 2 == 0 or n % 3 == 0:
            return False
        i = 5
        while i * i <= n:
            if n % i == 0 or n % (i + 2) == 0:
                return False
            i += 6
        return True


# Test function
def test_resonance_pattern_recognizer():
    """
    Tests the ResonancePatternRecognizer class.
    """
    recognizer = ResonancePatternRecognizer()
    
    # Test for a few numbers
    test_cases = [1, 13, 14, 170]
    
    for n in test_cases:
        # Recognize resonance patterns
        patterns = recognizer.recognize_resonance_patterns(n)
        print(f"Number {n}:")
        print(f"  Overall resonance strength: {patterns['overall_strength']}")
        
        # Print intra-scale patterns
        print("  Intra-scale patterns:")
        print(f"    Cycle: {patterns['intra_scale']['cycle_resonance']['patterns']}")
        print(f"    System: {patterns['intra_scale']['system_resonance']['patterns']}")
        print(f"    Level: {patterns['intra_scale']['level_resonance']['patterns']}")
        print(f"    Domain: {patterns['intra_scale']['domain_resonance']['patterns']}")
        
        # Print cross-scale patterns
        print("  Cross-scale patterns:")
        print(f"    Cycle-to-System: {patterns['cross_scale']['cycle_to_system']['patterns']}")
        print(f"    System-to-Level: {patterns['cross_scale']['system_to_level']['patterns']}")
        print(f"    Level-to-Domain: {patterns['cross_scale']['level_to_domain']['patterns']}")
        
        # Print harmonic patterns
        print("  Harmonic patterns:")
        print(f"    First-order: {patterns['harmonic']['first_order']['patterns']}")
        print(f"    Second-order: {patterns['harmonic']['second_order']['patterns']}")
        print(f"    Third-order: {patterns['harmonic']['third_order']['patterns']}")
        
        print()


if __name__ == "__main__":
    test_resonance_pattern_recognizer()
