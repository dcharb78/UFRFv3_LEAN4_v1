"""
Contextual Unity Detector for UFRF Framework

This module implements the "Always One in Context" principle by detecting and maintaining
contextual unity across all scales of the UFRF Framework.

Author: Daniel Charboneau
License: Creative Commons Attribution-NonCommercial 4.0 International
"""

import numpy as np
from collections import defaultdict

class ContextualUnityDetector:
    """
    Implements the "Always One in Context" principle by detecting and maintaining
    contextual unity across all scales of the UFRF Framework.
    """
    
    def __init__(self, dimensional_base=13):
        """
        Initialize the contextual unity detector.
        
        Args:
            dimensional_base: Base for dimensional calculations (default: 13)
        """
        self.dimensional_base = dimensional_base
        self.context_cache = {}
        
        # Define position types
        self.position_types = {
            'seed_double_octave': [1, 2, 3],
            'inner_octave': [4, 5, 6, 7, 8, 9],
            'rest': [10],
            'next_seed': [11, 12, 13]
        }
        
        # Define position characteristics
        self.position_characteristics = {
            1: {'type': 'seed_double_octave', 'polarity': 'positive', 'energy': 'high'},
            2: {'type': 'seed_double_octave', 'polarity': 'negative', 'energy': 'medium'},
            3: {'type': 'seed_double_octave', 'polarity': 'positive', 'energy': 'high'},
            4: {'type': 'inner_octave', 'polarity': 'negative', 'energy': 'medium'},
            5: {'type': 'inner_octave', 'polarity': 'positive', 'energy': 'very_high'},
            6: {'type': 'inner_octave', 'polarity': 'negative', 'energy': 'medium'},
            7: {'type': 'inner_octave', 'polarity': 'positive', 'energy': 'high'},
            8: {'type': 'inner_octave', 'polarity': 'negative', 'energy': 'medium'},
            9: {'type': 'inner_octave', 'polarity': 'positive', 'energy': 'high'},
            10: {'type': 'rest', 'polarity': 'neutral', 'energy': 'low'},
            11: {'type': 'next_seed', 'polarity': 'positive', 'energy': 'high'},
            12: {'type': 'next_seed', 'polarity': 'negative', 'energy': 'medium'},
            13: {'type': 'next_seed', 'polarity': 'positive', 'energy': 'high'}
        }
    
    def calculate_contextual_unity(self, entity, c, S, L, D):
        """
        Calculates the contextual unity function Ω(e, c, S, L, D).
        
        Args:
            entity: Mathematical entity
            c: Cycle position
            S: System level
            L: Level
            D: Domain
            
        Returns:
            Contextual unity value (should be 1 if principle is maintained)
        """
        # Calculate normalization factor
        normalization_factor = self.calculate_normalization_factor(c, S, L, D)
        
        # Calculate contextual unity
        if normalization_factor != 0:
            contextual_unity = entity / normalization_factor
        else:
            contextual_unity = 0
            
        return contextual_unity
    
    def calculate_normalization_factor(self, c, S, L, D):
        """
        Calculates the contextual normalization factor E(c, S, L, D).
        
        Args:
            c: Cycle position
            S: System level
            L: Level
            D: Domain
            
        Returns:
            Normalization factor
        """
        # Check if normalization factor is already cached
        context_key = (c, S, L, D)
        if context_key in self.context_cache:
            return self.context_cache[context_key]
        
        # Get all entities in the context
        context_entities = self.get_context_entities(c, S, L, D)
        
        # Calculate sum of all entities in context
        normalization_factor = sum(context_entities)
        
        # Cache the result
        self.context_cache[context_key] = normalization_factor
        
        return normalization_factor
    
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
        return self.position_characteristics.get(c, {'type': 'unknown', 'polarity': 'unknown', 'energy': 'unknown'})
    
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
    
    def clear_cache(self):
        """
        Clears the context cache.
        """
        self.context_cache = {}


# Test function
def test_contextual_unity_detector():
    """
    Tests the ContextualUnityDetector class.
    """
    detector = ContextualUnityDetector()
    
    # Test for a few numbers
    test_cases = [
        (1, 1, 1, 1, 1),  # First number
        (13, 13, 1, 1, 1),  # End of first cycle
        (14, 1, 2, 1, 1),  # Start of second cycle
        (170, 1, 14, 2, 1)  # Higher number
    ]
    
    for n, c, S, L, D in test_cases:
        unity = detector.calculate_contextual_unity(n, c, S, L, D)
        print(f"Number {n} (c={c}, S={S}, L={L}, D={D}): Unity = {unity}")
        
        # Get context entities
        entities = detector.get_context_entities(c, S, L, D)
        print(f"  Context entities: {entities}")
        
        # Get normalization factor
        normalization_factor = detector.calculate_normalization_factor(c, S, L, D)
        print(f"  Normalization factor: {normalization_factor}")
        
        print()


if __name__ == "__main__":
    test_contextual_unity_detector()
