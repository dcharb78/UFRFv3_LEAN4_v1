"""
Enhanced Harmonic Unity Function for UFRF Framework

This module implements the enhanced unity function with musical-like harmonic relationships
at system boundaries to improve the unity maintenance rate.

Author: Daniel Charboneau
License: Creative Commons Attribution-NonCommercial 4.0 International
"""

import numpy as np
import time
from collections import defaultdict

class HarmonicUnityFunction:
    """
    Implements an enhanced unity function that incorporates musical-like harmonic
    relationships at system boundaries.
    """
    
    def __init__(self, dimensional_base=13):
        """
        Initialize the harmonic unity function.
        
        Args:
            dimensional_base: Base for dimensional calculations (default: 13)
        """
        self.dimensional_base = dimensional_base
        self.harmonic_cache = {}
        self.context_cache = {}
        
        # Define position types with musical analogies
        self.position_types = {
            'seed_double_octave': [1, 2, 3],  # Fundamental and close harmonics
            'inner_octave': [4, 5, 6, 7, 8, 9],  # Middle harmonics
            'rest': [10],  # Transition point
            'next_seed': [11, 12, 13]  # Approaching next fundamental
        }
        
        # Define position characteristics with musical properties
        self.position_characteristics = {
            1: {'type': 'seed_double_octave', 'polarity': 'positive', 'energy': 'high', 'harmonic_role': 'fundamental'},
            2: {'type': 'seed_double_octave', 'polarity': 'negative', 'energy': 'medium', 'harmonic_role': 'octave'},
            3: {'type': 'seed_double_octave', 'polarity': 'positive', 'energy': 'high', 'harmonic_role': 'perfect_fifth'},
            4: {'type': 'inner_octave', 'polarity': 'negative', 'energy': 'medium', 'harmonic_role': 'perfect_fourth'},
            5: {'type': 'inner_octave', 'polarity': 'positive', 'energy': 'very_high', 'harmonic_role': 'major_third'},
            6: {'type': 'inner_octave', 'polarity': 'negative', 'energy': 'medium', 'harmonic_role': 'minor_third'},
            7: {'type': 'inner_octave', 'polarity': 'positive', 'energy': 'high', 'harmonic_role': 'center'},
            8: {'type': 'inner_octave', 'polarity': 'negative', 'energy': 'medium', 'harmonic_role': 'minor_sixth'},
            9: {'type': 'inner_octave', 'polarity': 'positive', 'energy': 'high', 'harmonic_role': 'major_sixth'},
            10: {'type': 'rest', 'polarity': 'neutral', 'energy': 'low', 'harmonic_role': 'seventh'},
            11: {'type': 'next_seed', 'polarity': 'positive', 'energy': 'high', 'harmonic_role': 'leading_tone'},
            12: {'type': 'next_seed', 'polarity': 'negative', 'energy': 'medium', 'harmonic_role': 'subtonic'},
            13: {'type': 'next_seed', 'polarity': 'positive', 'energy': 'high', 'harmonic_role': 'new_fundamental'}
        }
        
        # Harmonic consonance matrix (musical-like relationships)
        self.consonance_matrix = self._build_consonance_matrix()
    
    def _build_consonance_matrix(self):
        """
        Build a consonance matrix based on musical harmony principles.
        
        Returns:
            Dictionary mapping position pairs to consonance values
        """
        matrix = {}
        
        for i in range(1, self.dimensional_base + 1):
            for j in range(1, self.dimensional_base + 1):
                # Calculate ratio (musical interval)
                ratio = max(i, j) / min(i, j) if min(i, j) != 0 else 1
                
                # Assign consonance value based on musical theory
                if abs(ratio - 1.0) < 0.01:  # Unison
                    consonance = 1.0
                elif abs(ratio - 2.0) < 0.01:  # Octave
                    consonance = 0.95
                elif abs(ratio - 1.5) < 0.01:  # Perfect fifth
                    consonance = 0.9
                elif abs(ratio - 1.33) < 0.01:  # Perfect fourth
                    consonance = 0.85
                elif abs(ratio - 1.25) < 0.01:  # Major third
                    consonance = 0.8
                elif abs(ratio - 1.2) < 0.01:  # Minor third
                    consonance = 0.75
                elif abs(ratio - 1.67) < 0.01:  # Major sixth
                    consonance = 0.7
                elif abs(ratio - 1.6) < 0.01:  # Minor sixth
                    consonance = 0.65
                else:
                    # Less consonant intervals
                    consonance = 0.5 + 0.1 * (1 / (1 + abs(ratio - int(ratio))))
                
                matrix[(i, j)] = consonance
        
        return matrix
    
    def calculate_unity(self, entity, c, S, L, D):
        """
        Calculates the enhanced unity function Ω(e, c, S, L, D) with harmonic considerations.
        
        Args:
            entity: Mathematical entity
            c: Cycle position
            S: System level
            L: Level
            D: Domain
            
        Returns:
            Enhanced unity value
        """
        # Determine boundary level
        boundary_level = self.determine_boundary_level(entity)
        
        # Calculate normalization factor
        normalization_factor = self.calculate_normalization_factor(c, S, L, D)
        
        # Calculate base unity
        if normalization_factor != 0:
            base_unity = entity / normalization_factor
        else:
            base_unity = 0
        
        # Apply harmonic transformations
        harmonic_factor = self.calculate_harmonic_factor(entity, c, S, L, D, boundary_level)
        
        # Calculate final unity
        unity = base_unity * harmonic_factor
        
        return unity
    
    def determine_boundary_level(self, entity):
        """
        Determine which boundary level contains the entity.
        
        Args:
            entity: Mathematical entity
            
        Returns:
            Boundary level
        """
        return (entity - 1) // self.dimensional_base + 1
    
    def calculate_normalization_factor(self, c, S, L, D):
        """
        Calculates the contextual normalization factor E(c, S, L, D) with weighted entities.
        
        Args:
            c: Cycle position
            S: System level
            L: Level
            D: Domain
            
        Returns:
            Weighted normalization factor
        """
        # Check if normalization factor is already cached
        context_key = (c, S, L, D)
        if context_key in self.context_cache:
            return self.context_cache[context_key]
        
        # Get all entities in the context
        context_entities = self.get_context_entities(c, S, L, D)
        
        # Calculate weights for entities
        weights = self.calculate_weights(context_entities, c, S, L, D)
        
        # Calculate weighted sum of all entities in context
        normalization_factor = sum(w * e for w, e in zip(weights, context_entities))
        
        # Cache the result
        self.context_cache[context_key] = normalization_factor
        
        return normalization_factor
    
    def calculate_weights(self, entities, c, S, L, D):
        """
        Calculate weights for entities in context based on musical harmony principles.
        
        Args:
            entities: List of entities in context
            c: Cycle position
            S: System level
            L: Level
            D: Domain
            
        Returns:
            List of weights for entities
        """
        weights = []
        
        for entity in entities:
            # Calculate position within cycle
            position = ((entity - 1) % self.dimensional_base) + 1
            
            # Calculate consonance between positions
            consonance = self.consonance_matrix.get((c, position), 0.5)
            
            # Calculate position weight based on type
            position_weight = self.calculate_position_weight(position)
            
            # Calculate system level weight
            system_weight = self.calculate_system_weight(entity, S)
            
            # Combine weights
            weight = consonance * position_weight * system_weight
            
            weights.append(weight)
        
        # Normalize weights
        if weights:
            total_weight = sum(weights)
            if total_weight > 0:
                weights = [w / total_weight for w in weights]
        
        return weights
    
    def calculate_position_weight(self, position):
        """
        Calculate weight based on position type.
        
        Args:
            position: Cycle position
            
        Returns:
            Position weight
        """
        # Get position characteristics
        characteristics = self.get_position_characteristics(position)
        
        # Assign weight based on type
        if characteristics['type'] == 'seed_double_octave':
            weight = 1.2
        elif characteristics['type'] == 'inner_octave':
            weight = 1.0
        elif characteristics['type'] == 'rest':
            weight = 0.8
        elif characteristics['type'] == 'next_seed':
            weight = 1.1
        else:
            weight = 1.0
        
        # Adjust weight based on polarity
        if characteristics['polarity'] == 'positive':
            weight *= 1.1
        elif characteristics['polarity'] == 'negative':
            weight *= 0.9
        
        # Adjust weight based on energy
        if characteristics['energy'] == 'high':
            weight *= 1.1
        elif characteristics['energy'] == 'very_high':
            weight *= 1.2
        elif characteristics['energy'] == 'low':
            weight *= 0.9
        
        return weight
    
    def calculate_system_weight(self, entity, S):
        """
        Calculate weight based on system level relationship.
        
        Args:
            entity: Mathematical entity
            S: System level
            
        Returns:
            System weight
        """
        # Calculate entity's system level
        entity_S = ((entity - 1) // self.dimensional_base % self.dimensional_base) + 1
        
        # Calculate ratio between system levels
        ratio = max(entity_S, S) / min(entity_S, S) if min(entity_S, S) != 0 else 1
        
        # Assign weight based on ratio
        if abs(ratio - 1.0) < 0.01:  # Same system
            weight = 1.2
        elif abs(ratio - 2.0) < 0.01:  # Octave relationship
            weight = 1.1
        elif abs(ratio - 1.5) < 0.01:  # Perfect fifth relationship
            weight = 1.05
        elif abs(ratio - 1.33) < 0.01:  # Perfect fourth relationship
            weight = 1.0
        else:
            # Less consonant relationships
            weight = 0.9 + 0.1 * (1 / (1 + abs(ratio - int(ratio))))
        
        # Adjust weight for prime system levels
        if self.is_prime(entity_S):
            weight *= 1.1
        
        return weight
    
    def calculate_harmonic_factor(self, entity, c, S, L, D, boundary_level):
        """
        Calculate harmonic factor based on musical-like relationships.
        
        Args:
            entity: Mathematical entity
            c: Cycle position
            S: System level
            L: Level
            D: Domain
            boundary_level: Boundary level
            
        Returns:
            Harmonic factor
        """
        # Check cache
        cache_key = (entity, c, S, L, D)
        if cache_key in self.harmonic_cache:
            return self.harmonic_cache[cache_key]
        
        # Calculate position within boundary
        position = ((entity - 1) % self.dimensional_base) + 1
        
        # Calculate octave factor
        octave_factor = self.calculate_octave_factor(position, boundary_level)
        
        # Calculate consonance factor
        consonance_factor = self.calculate_consonance_factor(position, c)
        
        # Calculate cross-boundary resonance
        resonance_factor = self.calculate_cross_boundary_resonance(entity, boundary_level)
        
        # Combine factors
        harmonic_factor = octave_factor * consonance_factor * resonance_factor
        
        # Cache result
        self.harmonic_cache[cache_key] = harmonic_factor
        
        return harmonic_factor
    
    def calculate_octave_factor(self, position, boundary_level):
        """
        Calculate factor based on position within octave-like structure.
        
        Args:
            position: Cycle position
            boundary_level: Boundary level
            
        Returns:
            Octave factor
        """
        # Positions 1 and 13 (boundary positions) have strongest octave factor
        if position == 1 or position == self.dimensional_base:
            return 1.2
        
        # Positions that are prime numbers have strong octave factor
        if self.is_prime(position):
            return 1.1
        
        # Position 7 (center) has special properties
        if position == 7:
            return 1.15
        
        # Default octave factor
        return 1.0
    
    def calculate_consonance_factor(self, position, c):
        """
        Calculate consonance factor based on musical harmony principles.
        
        Args:
            position: Cycle position
            c: Current cycle position
            
        Returns:
            Consonance factor
        """
        # Get consonance from matrix
        consonance = self.consonance_matrix.get((position, c), 0.5)
        
        # Convert to factor (centered around 1.0)
        consonance_factor = 0.8 + 0.4 * consonance
        
        return consonance_factor
    
    def calculate_cross_boundary_resonance(self, entity, boundary_level):
        """
        Calculate resonance across system boundaries.
        
        Args:
            entity: Mathematical entity
            boundary_level: Boundary level
            
        Returns:
            Cross-boundary resonance factor
        """
        # No cross-boundary resonance for entities in first boundary
        if boundary_level == 1:
            return 1.0
        
        # Calculate position within boundary
        position = ((entity - 1) % self.dimensional_base) + 1
        
        # Calculate corresponding positions in lower boundaries
        resonance_sum = 0
        for lower_boundary in range(1, boundary_level):
            corresponding_entity = position + (lower_boundary - 1) * self.dimensional_base
            resonance_factor = self.calculate_resonance_factor(
                position, boundary_level, 
                position, lower_boundary
            )
            resonance_sum += resonance_factor
        
        # Normalize and return
        return 1.0 + 0.1 * (resonance_sum / (boundary_level - 1))
    
    def calculate_resonance_factor(self, position1, boundary1, position2, boundary2):
        """
        Calculate resonance factor between positions across boundaries.
        
        Args:
            position1: First position
            boundary1: First boundary level
            position2: Second position
            boundary2: Second boundary level
            
        Returns:
            Resonance factor
        """
        # Convert positions to frequencies
        freq1 = position1 + (boundary1 - 1) * self.dimensional_base
        freq2 = position2 + (boundary2 - 1) * self.dimensional_base
        
        # Calculate frequency ratio
        if freq1 > freq2:
            ratio = freq1 / freq2
        else:
            ratio = freq2 / freq1
        
        # Check if ratio is close to a simple fraction (harmonic relationship)
        if abs(ratio - round(ratio)) < 0.01:  # Integer ratio
            return 1.2
        elif abs(ratio - (round(ratio * 2) / 2)) < 0.01:  # Half-integer ratio
            return 1.1
        elif abs(ratio - (round(ratio * 3) / 3)) < 0.01:  # Third-integer ratio
            return 1.05
        
        # Default resonance factor
        return 1.0
    
    def get_context_entities(self, c, S, L, D):
        """
        Gets all entities that belong to the same context.
        
        Args:
            c: Cycle position
            S: System level
            L: Level
            D: Domain
            
        Returns:
            List of entities in the context
        """
        # Get entities based on context type
        if c in self.position_types['seed_double_octave']:
            # Seed phase context
            entities = self.get_seed_phase_entities(c, S, L, D)
        elif c in self.position_types['inner_octave']:
            # Inner octave context
            entities = self.get_inner_octave_entities(c, S, L, D)
        elif c in self.position_types['rest']:
            # REST position context
            entities = self.get_rest_position_entities(c, S, L, D)
        elif c in self.position_types['next_seed']:
            # Next seed context
            entities = self.get_next_seed_entities(c, S, L, D)
        else:
            # Default empty context
            entities = []
        
        return entities
    
    def get_seed_phase_entities(self, c, S, L, D):
        """
        Gets entities in the seed phase context.
        
        Args:
            c: Cycle position
            S: System level
            L: Level
            D: Domain
            
        Returns:
            List of entities in the seed phase context
        """
        # Calculate base number for this context
        base_number = self.calculate_base_number(c, S, L, D)
        
        # Get all numbers in the seed phase (positions 1-3)
        entities = []
        for pos in self.position_types['seed_double_octave']:
            # Calculate number for this position
            number = base_number + (pos - c)
            if number > 0:  # Ensure number is positive
                entities.append(number)
        
        return entities
    
    def get_inner_octave_entities(self, c, S, L, D):
        """
        Gets entities in the inner octave context.
        
        Args:
            c: Cycle position
            S: System level
            L: Level
            D: Domain
            
        Returns:
            List of entities in the inner octave context
        """
        # Calculate base number for this context
        base_number = self.calculate_base_number(c, S, L, D)
        
        # Get all numbers in the inner octave (positions 4-9)
        entities = []
        for pos in self.position_types['inner_octave']:
            # Calculate number for this position
            number = base_number + (pos - c)
            if number > 0:  # Ensure number is positive
                entities.append(number)
        
        return entities
    
    def get_rest_position_entities(self, c, S, L, D):
        """
        Gets entities in the REST position context.
        
        Args:
            c: Cycle position
            S: System level
            L: Level
            D: Domain
            
        Returns:
            List of entities in the REST position context
        """
        # Calculate base number for this context
        base_number = self.calculate_base_number(c, S, L, D)
        
        # For REST position, include adjacent positions (9-11)
        entities = []
        for pos in [9, 10, 11]:
            # Calculate number for this position
            number = base_number + (pos - c)
            if number > 0:  # Ensure number is positive
                entities.append(number)
        
        return entities
    
    def get_next_seed_entities(self, c, S, L, D):
        """
        Gets entities in the next seed context.
        
        Args:
            c: Cycle position
            S: System level
            L: Level
            D: Domain
            
        Returns:
            List of entities in the next seed context
        """
        # Calculate base number for this context
        base_number = self.calculate_base_number(c, S, L, D)
        
        # Get all numbers in the next seed phase (positions 11-13)
        entities = []
        for pos in self.position_types['next_seed']:
            # Calculate number for this position
            number = base_number + (pos - c)
            if number > 0:  # Ensure number is positive
                entities.append(number)
        
        return entities
    
    def calculate_base_number(self, c, S, L, D):
        """
        Calculates the base number for a given dimensional mapping.
        
        Args:
            c: Cycle position
            S: System level
            L: Level
            D: Domain
            
        Returns:
            Base number
        """
        # Calculate base number using dimensional mapping formula
        base = (((((D - 1) * self.dimensional_base + (L - 1)) * self.dimensional_base + (S - 1)) * self.dimensional_base) + 1)
        return base
    
    def get_position_characteristics(self, c):
        """
        Gets characteristics of a cycle position.
        
        Args:
            c: Cycle position
            
        Returns:
            Position characteristics
        """
        return self.position_characteristics.get(c, {'type': 'unknown', 'polarity': 'unknown', 'energy': 'unknown', 'harmonic_role': 'unknown'})
    
    def get_position_type(self, c):
        """
        Gets the type of a cycle position.
        
        Args:
            c: Cycle position
            
        Returns:
            Position type
        """
        for type_name, positions in self.position_types.items():
            if c in positions:
                return type_name
        return 'unknown'
    
    def is_prime(self, n):
        """
        Check if a number is prime.
        
        Args:
            n: Number to check
            
        Returns:
            True if prime, False otherwise
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
    
    def clear_cache(self):
        """
        Clears the caches.
        """
        self.harmonic_cache = {}
        self.context_cache = {}


class HarmonicDimensionalMapper:
    """
    Maps numbers to dimensional coordinates with enhanced unity calculations
    that incorporate musical-like harmonic relationships.
    """
    
    def __init__(self, dimensional_base=13):
        """
        Initialize the harmonic dimensional mapper.
        
        Args:
            dimensional_base: Base for dimensional calculations (default: 13)
        """
        self.dimensional_base = dimensional_base
        self.unity_function = HarmonicUnityFunction(dimensional_base)
    
    def map_with_unity(self, n):
        """
        Maps a number to dimensional coordinates with enhanced unity calculation.
        
        Args:
            n: Number to map
            
        Returns:
            Dictionary with dimensional mapping and unity
        """
        # Calculate dimensional coordinates
        c = ((n - 1) % self.dimensional_base) + 1
        S = ((n - 1) // self.dimensional_base % self.dimensional_base) + 1
        L = ((n - 1) // (self.dimensional_base ** 2) % self.dimensional_base) + 1
        D = ((n - 1) // (self.dimensional_base ** 3)) + 1
        
        # Calculate unity
        unity = self.unity_function.calculate_unity(n, c, S, L, D)
        
        # Calculate boundary level
        boundary_level = (n - 1) // self.dimensional_base + 1
        
        # Calculate harmonic properties
        harmonic_properties = self.calculate_harmonic_properties(n, c, S, L, D, boundary_level)
        
        return {
            'original_number': n,
            'cycle_position': c,
            'system_level': S,
            'level': L,
            'domain': D,
            'boundary_level': boundary_level,
            'contextual_unity': unity,
            'harmonic_properties': harmonic_properties
        }
    
    def map_range_with_unity(self, start, end):
        """
        Maps a range of numbers to dimensional coordinates with unity calculations.
        
        Args:
            start: Start of range
            end: End of range
            
        Returns:
            List of mappings
        """
        return [self.map_with_unity(n) for n in range(start, end + 1)]
    
    def calculate_harmonic_properties(self, n, c, S, L, D, boundary_level):
        """
        Calculate harmonic properties for a number.
        
        Args:
            n: Number
            c: Cycle position
            S: System level
            L: Level
            D: Domain
            boundary_level: Boundary level
            
        Returns:
            Dictionary of harmonic properties
        """
        # Calculate position within boundary
        position = ((n - 1) % self.dimensional_base) + 1
        
        # Calculate harmonic series
        harmonic_series = self.calculate_harmonic_series(position, 5)
        
        # Calculate resonant positions
        resonant_positions = self.calculate_resonant_positions(position, boundary_level)
        
        # Calculate consonance map
        consonance_map = self.calculate_consonance_map(position)
        
        return {
            'harmonic_series': harmonic_series,
            'resonant_positions': resonant_positions,
            'consonance_map': consonance_map,
            'is_boundary_position': position == 1 or position == self.dimensional_base,
            'is_prime_position': self.unity_function.is_prime(position),
            'position_characteristics': self.unity_function.get_position_characteristics(position)
        }
    
    def calculate_harmonic_series(self, fundamental, num_harmonics):
        """
        Calculate harmonic series for a fundamental frequency.
        
        Args:
            fundamental: Fundamental frequency
            num_harmonics: Number of harmonics to calculate
            
        Returns:
            List of harmonics
        """
        return [fundamental * n for n in range(1, num_harmonics + 1)]
    
    def calculate_resonant_positions(self, position, boundary_level):
        """
        Calculate positions that resonate with the given position.
        
        Args:
            position: Cycle position
            boundary_level: Boundary level
            
        Returns:
            List of resonant positions
        """
        resonant_positions = []
        
        # Check positions in current boundary
        for pos in range(1, self.dimensional_base + 1):
            if pos != position:
                ratio = max(position, pos) / min(position, pos) if min(position, pos) != 0 else 1
                if abs(ratio - round(ratio)) < 0.01 or abs(ratio - (round(ratio * 2) / 2)) < 0.01:
                    resonant_positions.append(pos)
        
        # Check positions in other boundaries
        for other_boundary in range(1, 4):  # Check first 3 boundaries
            if other_boundary != boundary_level:
                for pos in range(1, self.dimensional_base + 1):
                    other_position = pos + (other_boundary - 1) * self.dimensional_base
                    if self.unity_function.calculate_resonance_factor(
                        position, boundary_level, pos, other_boundary) > 1.05:
                        resonant_positions.append(other_position)
        
        return resonant_positions
    
    def calculate_consonance_map(self, position):
        """
        Calculate consonance map for a position.
        
        Args:
            position: Cycle position
            
        Returns:
            Dictionary mapping positions to consonance types
        """
        consonance_map = {}
        
        for pos in range(1, self.dimensional_base + 1):
            ratio = max(position, pos) / min(position, pos) if min(position, pos) != 0 else 1
            
            if abs(ratio - 1.0) < 0.01:  # Unison
                consonance_map[pos] = 'unison'
            elif abs(ratio - 2.0) < 0.01:  # Octave
                consonance_map[pos] = 'octave'
            elif abs(ratio - 1.5) < 0.01:  # Perfect fifth
                consonance_map[pos] = 'perfect_fifth'
            elif abs(ratio - 1.33) < 0.01:  # Perfect fourth
                consonance_map[pos] = 'perfect_fourth'
            elif abs(ratio - 1.25) < 0.01:  # Major third
                consonance_map[pos] = 'major_third'
            elif abs(ratio - 1.2) < 0.01:  # Minor third
                consonance_map[pos] = 'minor_third'
            else:
                consonance_map[pos] = 'other'
        
        return consonance_map
    
    def get_position_context(self, n):
        """
        Gets the context for a number's position.
        
        Args:
            n: Number
            
        Returns:
            Dictionary with position context
        """
        # Calculate dimensional coordinates
        c = ((n - 1) % self.dimensional_base) + 1
        
        # Get position characteristics
        characteristics = self.unity_function.get_position_characteristics(c)
        
        # Get position type
        position_type = self.unity_function.get_position_type(c)
        
        return {
            'number': n,
            'cycle_position': c,
            'characteristics': characteristics,
            'position_type': position_type
        }


# Test function
def test_harmonic_unity_function():
    """
    Tests the HarmonicUnityFunction class.
    """
    unity_function = HarmonicUnityFunction()
    mapper = HarmonicDimensionalMapper()
    
    # Test for key boundary numbers
    test_cases = [1, 13, 14, 26, 27, 39, 40, 52]
    
    for n in test_cases:
        # Map number with unity
        mapping = mapper.map_with_unity(n)
        
        print(f"Number {n}:")
        print(f"  Dimensional mapping: c={mapping['cycle_position']}, S={mapping['system_level']}, L={mapping['level']}, D={mapping['domain']}")
        print(f"  Boundary level: {mapping['boundary_level']}")
        print(f"  Contextual unity: {mapping['contextual_unity']:.4f}")
        print(f"  Harmonic properties:")
        print(f"    Is boundary position: {mapping['harmonic_properties']['is_boundary_position']}")
        print(f"    Is prime position: {mapping['harmonic_properties']['is_prime_position']}")
        print(f"    Position characteristics: {mapping['harmonic_properties']['position_characteristics']}")
        print()
    
    # Test unity maintenance rate for ranges
    ranges = [(1, 13), (14, 26), (27, 39), (40, 52)]
    
    for start, end in ranges:
        mappings = mapper.map_range_with_unity(start, end)
        
        # Count numbers with unity >= 0.8
        unity_maintained_count = sum(1 for m in mappings if m['contextual_unity'] >= 0.8)
        unity_rate = unity_maintained_count / len(mappings)
        
        print(f"Range {start}-{end}:")
        print(f"  Unity maintenance rate: {unity_rate:.4f}")
        print(f"  Unity maintained: {unity_maintained_count}/{len(mappings)}")
        print()


if __name__ == "__main__":
    test_harmonic_unity_function()
