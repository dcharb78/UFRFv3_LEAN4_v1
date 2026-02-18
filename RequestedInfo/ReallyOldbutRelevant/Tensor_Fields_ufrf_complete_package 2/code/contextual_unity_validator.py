"""
Contextual Unity Validator for UFRF Framework

This module implements the Contextual Unity Validator component that validates
that the "Always One in Context" principle is maintained during exploration.

Author: Daniel Charboneau
License: Creative Commons Attribution-NonCommercial 4.0 International
"""

import numpy as np
import json
from collections import defaultdict

# Use relative imports for modules in the same package
from .contextual_unity_detector import ContextualUnityDetector
from .enhanced_dimensional_mapper import EnhancedDimensionalMapper
from .cross_scale_context_analyzer import CrossScaleContextAnalyzer
from .resonance_pattern_recognizer import ResonancePatternRecognizer

class ContextualUnityValidator:
    """
    Validates that the "Always One in Context" principle is maintained during exploration.
    """
    
    def __init__(self, dimensional_base=13):
        """
        Initialize the contextual unity validator.
        
        Args:
            dimensional_base: Base for dimensional calculations (default: 13)
        """
        self.dimensional_base = dimensional_base
        self.unity_detector = ContextualUnityDetector(dimensional_base)
        self.dimensional_mapper = EnhancedDimensionalMapper(dimensional_base)
        self.context_analyzer = CrossScaleContextAnalyzer(dimensional_base)
        self.pattern_recognizer = ResonancePatternRecognizer(dimensional_base)
        
        # Initialize validation metrics
        self.validation_metrics = {
            'total_numbers_validated': 0,
            'unity_maintained_count': 0,
            'unity_violations_count': 0,
            'average_unity_score': 0.0,
            'scale_specific_metrics': {
                'cycle': {'maintained': 0, 'violated': 0, 'average_score': 0.0},
                'system': {'maintained': 0, 'violated': 0, 'average_score': 0.0},
                'level': {'maintained': 0, 'violated': 0, 'average_score': 0.0},
                'domain': {'maintained': 0, 'violated': 0, 'average_score': 0.0}
            },
            'cross_scale_metrics': {
                'cycle_to_system': {'maintained': 0, 'violated': 0, 'average_score': 0.0},
                'system_to_level': {'maintained': 0, 'violated': 0, 'average_score': 0.0},
                'level_to_domain': {'maintained': 0, 'violated': 0, 'average_score': 0.0}
            },
            'resonance_metrics': {
                'intra_scale': {'maintained': 0, 'violated': 0, 'average_score': 0.0},
                'cross_scale': {'maintained': 0, 'violated': 0, 'average_score': 0.0},
                'harmonic': {'maintained': 0, 'violated': 0, 'average_score': 0.0}
            }
        }
        
        # Initialize validation thresholds
        self.validation_thresholds = {
            'unity_score': 0.7,
            'scale_specific': 0.6,
            'cross_scale': 0.65,
            'resonance': 0.5
        }
        
        # Initialize validation history
        self.validation_history = []
    
    def validate_contextual_unity(self, n, dimensional_mapping=None):
        """
        Validates that the "Always One in Context" principle is maintained.
        
        Args:
            n: Number being validated
            dimensional_mapping: Dimensional mapping of the number (optional)
            
        Returns:
            Validation results
        """
        # Get dimensional mapping if not provided
        if dimensional_mapping is None:
            dimensional_mapping = self.dimensional_mapper.map_with_unity(n)
            
        c = dimensional_mapping['cycle_position']
        S = dimensional_mapping['system_level']
        L = dimensional_mapping['level']
        D = dimensional_mapping['domain']
        
        # Validate unity in each scale
        cycle_validation = self.validate_cycle_unity(n, c)
        system_validation = self.validate_system_unity(n, S)
        level_validation = self.validate_level_unity(n, L)
        domain_validation = self.validate_domain_unity(n, D)
        
        # Validate cross-scale unity
        cross_scale_validation = self.validate_cross_scale_unity(n, c, S, L, D)
        
        # Validate resonance patterns
        resonance_validation = self.validate_resonance_patterns(n, c, S, L, D)
        
        # Calculate overall unity score
        overall_unity_score = self.calculate_overall_unity_score(
            cycle_validation['unity_score'],
            system_validation['unity_score'],
            level_validation['unity_score'],
            domain_validation['unity_score'],
            cross_scale_validation['unity_score'],
            resonance_validation['unity_score']
        )
        
        # Determine if unity is maintained
        unity_maintained = overall_unity_score >= self.validation_thresholds['unity_score']
        
        # Update validation metrics
        self.update_validation_metrics(
            unity_maintained,
            overall_unity_score,
            cycle_validation,
            system_validation,
            level_validation,
            domain_validation,
            cross_scale_validation,
            resonance_validation
        )
        
        # Create validation result
        validation_result = {
            'number': n,
            'dimensional_mapping': dimensional_mapping,
            'unity_maintained': unity_maintained,
            'overall_unity_score': overall_unity_score,
            'scale_validations': {
                'cycle': cycle_validation,
                'system': system_validation,
                'level': level_validation,
                'domain': domain_validation
            },
            'cross_scale_validation': cross_scale_validation,
            'resonance_validation': resonance_validation
        }
        
        # Add to validation history
        self.validation_history.append(validation_result)
        
        return validation_result
    
    def validate_cycle_unity(self, n, c):
        """
        Validates unity within the cycle.
        
        Args:
            n: Number being validated
            c: Cycle position
            
        Returns:
            Cycle unity validation
        """
        # Get position characteristics
        characteristics = self.unity_detector.get_position_characteristics(c)
        
        # Calculate unity score based on position characteristics
        unity_score = self.calculate_position_unity_score(characteristics)
        
        # Determine if unity is maintained
        unity_maintained = unity_score >= self.validation_thresholds['scale_specific']
        
        # Identify unity factors
        unity_factors = []
        
        if characteristics['type'] == 'seed':
            unity_factors.append('seed_position')
        
        if characteristics['polarity'] == 'positive':
            unity_factors.append('positive_polarity')
        
        if c == 1 or c == self.dimensional_base:
            unity_factors.append('boundary_position')
        
        return {
            'cycle_position': c,
            'characteristics': characteristics,
            'unity_score': unity_score,
            'unity_maintained': unity_maintained,
            'unity_factors': unity_factors
        }
    
    def validate_system_unity(self, n, S):
        """
        Validates unity within the system level.
        
        Args:
            n: Number being validated
            S: System level
            
        Returns:
            System unity validation
        """
        # Calculate system characteristics
        system_characteristics = self.calculate_system_characteristics(S)
        
        # Calculate unity score based on system characteristics
        unity_score = self.calculate_system_unity_score(system_characteristics)
        
        # Determine if unity is maintained
        unity_maintained = unity_score >= self.validation_thresholds['scale_specific']
        
        # Identify unity factors
        unity_factors = []
        
        if system_characteristics['is_prime']:
            unity_factors.append('prime_system')
        
        if system_characteristics['is_fibonacci']:
            unity_factors.append('fibonacci_system')
        
        if S == 1 or S % self.dimensional_base == 0:
            unity_factors.append('boundary_system')
        
        return {
            'system_level': S,
            'characteristics': system_characteristics,
            'unity_score': unity_score,
            'unity_maintained': unity_maintained,
            'unity_factors': unity_factors
        }
    
    def validate_level_unity(self, n, L):
        """
        Validates unity within the level.
        
        Args:
            n: Number being validated
            L: Level
            
        Returns:
            Level unity validation
        """
        # Calculate level characteristics
        level_characteristics = self.calculate_level_characteristics(L)
        
        # Calculate unity score based on level characteristics
        unity_score = self.calculate_level_unity_score(level_characteristics)
        
        # Determine if unity is maintained
        unity_maintained = unity_score >= self.validation_thresholds['scale_specific']
        
        # Identify unity factors
        unity_factors = []
        
        if level_characteristics['is_prime']:
            unity_factors.append('prime_level')
        
        if level_characteristics['is_fibonacci']:
            unity_factors.append('fibonacci_level')
        
        if L == 1 or L == self.dimensional_base:
            unity_factors.append('boundary_level')
        
        return {
            'level': L,
            'characteristics': level_characteristics,
            'unity_score': unity_score,
            'unity_maintained': unity_maintained,
            'unity_factors': unity_factors
        }
    
    def validate_domain_unity(self, n, D):
        """
        Validates unity within the domain.
        
        Args:
            n: Number being validated
            D: Domain
            
        Returns:
            Domain unity validation
        """
        # Calculate domain characteristics
        domain_characteristics = self.calculate_domain_characteristics(D)
        
        # Calculate unity score based on domain characteristics
        unity_score = self.calculate_domain_unity_score(domain_characteristics)
        
        # Determine if unity is maintained
        unity_maintained = unity_score >= self.validation_thresholds['scale_specific']
        
        # Identify unity factors
        unity_factors = []
        
        if domain_characteristics['is_prime']:
            unity_factors.append('prime_domain')
        
        if domain_characteristics['is_fibonacci']:
            unity_factors.append('fibonacci_domain')
        
        if D == 1:
            unity_factors.append('first_domain')
        
        return {
            'domain': D,
            'characteristics': domain_characteristics,
            'unity_score': unity_score,
            'unity_maintained': unity_maintained,
            'unity_factors': unity_factors
        }
    
    def validate_cross_scale_unity(self, n, c, S, L, D):
        """
        Validates unity across different scales.
        
        Args:
            n: Number being validated
            c, S, L, D: Dimensional mapping
            
        Returns:
            Cross-scale unity validation
        """
        # Analyze cross-scale context
        cross_scale_context = self.context_analyzer.analyze_cross_scale_context(n)
        
        # Validate cycle-to-system unity
        cycle_to_system = self.validate_cycle_to_system_unity(n, c, S, cross_scale_context)
        
        # Validate system-to-level unity
        system_to_level = self.validate_system_to_level_unity(n, S, L, cross_scale_context)
        
        # Validate level-to-domain unity
        level_to_domain = self.validate_level_to_domain_unity(n, L, D, cross_scale_context)
        
        # Calculate overall cross-scale unity score
        unity_score = (
            cycle_to_system['unity_score'] +
            system_to_level['unity_score'] +
            level_to_domain['unity_score']
        ) / 3
        
        # Determine if unity is maintained
        unity_maintained = unity_score >= self.validation_thresholds['cross_scale']
        
        return {
            'cycle_to_system': cycle_to_system,
            'system_to_level': system_to_level,
            'level_to_domain': level_to_domain,
            'unity_score': unity_score,
            'unity_maintained': unity_maintained,
            'overall_coherence': cross_scale_context['overall_coherence']
        }
    
    def validate_cycle_to_system_unity(self, n, c, S, cross_scale_context):
        """
        Validates unity between cycle and system.
        
        Args:
            n: Number being validated
            c: Cycle position
            S: System level
            cross_scale_context: Cross-scale context analysis
            
        Returns:
            Cycle-to-system unity validation
        """
        # Get cycle-to-system context
        context = cross_scale_context['adjacent_scale_contexts']['cycle_to_system']
        
        # Calculate unity score based on context
        unity_score = context['coherence']
        
        # Determine if unity is maintained
        unity_maintained = unity_score >= self.validation_thresholds['cross_scale']
        
        # Identify unity factors
        unity_factors = []
        
        if context['relationship_type'] == 'identity':
            unity_factors.append('identity_relationship')
        
        if context['harmony'] > 0.8:
            unity_factors.append('high_harmony')
        
        if c == S:
            unity_factors.append('position_equals_system')
        
        return {
            'cycle_position': c,
            'system_level': S,
            'unity_score': unity_score,
            'unity_maintained': unity_maintained,
            'unity_factors': unity_factors,
            'context': context
        }
    
    def validate_system_to_level_unity(self, n, S, L, cross_scale_context):
        """
        Validates unity between system and level.
        
        Args:
            n: Number being validated
            S: System level
            L: Level
            cross_scale_context: Cross-scale context analysis
            
        Returns:
            System-to-level unity validation
        """
        # Get system-to-level context
        context = cross_scale_context['adjacent_scale_contexts']['system_to_level']
        
        # Calculate unity score based on context
        unity_score = context['coherence']
        
        # Determine if unity is maintained
        unity_maintained = unity_score >= self.validation_thresholds['cross_scale']
        
        # Identify unity factors
        unity_factors = []
        
        if context['relationship_type'] == 'identity':
            unity_factors.append('identity_relationship')
        
        if context['harmony'] > 0.8:
            unity_factors.append('high_harmony')
        
        if S % L == 0:
            unity_factors.append('system_multiple_of_level')
        
        return {
            'system_level': S,
            'level': L,
            'unity_score': unity_score,
            'unity_maintained': unity_maintained,
            'unity_factors': unity_factors,
            'context': context
        }
    
    def validate_level_to_domain_unity(self, n, L, D, cross_scale_context):
        """
        Validates unity between level and domain.
        
        Args:
            n: Number being validated
            L: Level
            D: Domain
            cross_scale_context: Cross-scale context analysis
            
        Returns:
            Level-to-domain unity validation
        """
        # Get level-to-domain context
        context = cross_scale_context['adjacent_scale_contexts']['level_to_domain']
        
        # Calculate unity score based on context
        unity_score = context['coherence']
        
        # Determine if unity is maintained
        unity_maintained = unity_score >= self.validation_thresholds['cross_scale']
        
        # Identify unity factors
        unity_factors = []
        
        if context['relationship_type'] == 'identity':
            unity_factors.append('identity_relationship')
        
        if context['harmony'] > 0.8:
            unity_factors.append('high_harmony')
        
        if L % D == 0 or D % L == 0:
            unity_factors.append('level_domain_multiple')
        
        return {
            'level': L,
            'domain': D,
            'unity_score': unity_score,
            'unity_maintained': unity_maintained,
            'unity_factors': unity_factors,
            'context': context
        }
    
    def validate_resonance_patterns(self, n, c, S, L, D):
        """
        Validates resonance patterns.
        
        Args:
            n: Number being validated
            c, S, L, D: Dimensional mapping
            
        Returns:
            Resonance pattern validation
        """
        # Recognize resonance patterns
        patterns = self.pattern_recognizer.recognize_resonance_patterns(n)
        
        # Validate intra-scale resonance
        intra_scale = self.validate_intra_scale_resonance(patterns['intra_scale'])
        
        # Validate cross-scale resonance
        cross_scale = self.validate_cross_scale_resonance(patterns['cross_scale'])
        
        # Validate harmonic resonance
        harmonic = self.validate_harmonic_resonance(patterns['harmonic'])
        
        # Calculate overall resonance unity score
        unity_score = (
            intra_scale['unity_score'] +
            cross_scale['unity_score'] +
            harmonic['unity_score']
        ) / 3
        
        # Determine if unity is maintained
        unity_maintained = unity_score >= self.validation_thresholds['resonance']
        
        return {
            'intra_scale': intra_scale,
            'cross_scale': cross_scale,
            'harmonic': harmonic,
            'unity_score': unity_score,
            'unity_maintained': unity_maintained,
            'overall_strength': patterns['overall_strength']
        }
    
    def validate_intra_scale_resonance(self, intra_scale_patterns):
        """
        Validates intra-scale resonance patterns.
        
        Args:
            intra_scale_patterns: Intra-scale resonance patterns
            
        Returns:
            Intra-scale resonance validation
        """
        # Calculate unity score based on intra-scale resonance strength
        unity_score = intra_scale_patterns['strength']
        
        # Determine if unity is maintained
        unity_maintained = unity_score >= self.validation_thresholds['resonance']
        
        # Identify unity factors
        unity_factors = []
        
        if len(intra_scale_patterns['cycle_resonance']['patterns']) > 0:
            unity_factors.append('cycle_resonance')
        
        if len(intra_scale_patterns['system_resonance']['patterns']) > 0:
            unity_factors.append('system_resonance')
        
        if len(intra_scale_patterns['level_resonance']['patterns']) > 0:
            unity_factors.append('level_resonance')
        
        if len(intra_scale_patterns['domain_resonance']['patterns']) > 0:
            unity_factors.append('domain_resonance')
        
        return {
            'unity_score': unity_score,
            'unity_maintained': unity_maintained,
            'unity_factors': unity_factors,
            'patterns': intra_scale_patterns
        }
    
    def validate_cross_scale_resonance(self, cross_scale_patterns):
        """
        Validates cross-scale resonance patterns.
        
        Args:
            cross_scale_patterns: Cross-scale resonance patterns
            
        Returns:
            Cross-scale resonance validation
        """
        # Calculate unity score based on cross-scale resonance strength
        unity_score = cross_scale_patterns['strength']
        
        # Determine if unity is maintained
        unity_maintained = unity_score >= self.validation_thresholds['resonance']
        
        # Identify unity factors
        unity_factors = []
        
        if len(cross_scale_patterns['cycle_to_system']['patterns']) > 0:
            unity_factors.append('cycle_to_system_resonance')
        
        if len(cross_scale_patterns['system_to_level']['patterns']) > 0:
            unity_factors.append('system_to_level_resonance')
        
        if len(cross_scale_patterns['level_to_domain']['patterns']) > 0:
            unity_factors.append('level_to_domain_resonance')
        
        if len(cross_scale_patterns['cycle_to_level']['patterns']) > 0:
            unity_factors.append('cycle_to_level_resonance')
        
        if len(cross_scale_patterns['cycle_to_domain']['patterns']) > 0:
            unity_factors.append('cycle_to_domain_resonance')
        
        return {
            'unity_score': unity_score,
            'unity_maintained': unity_maintained,
            'unity_factors': unity_factors,
            'patterns': cross_scale_patterns
        }
    
    def validate_harmonic_resonance(self, harmonic_patterns):
        """
        Validates harmonic resonance patterns.
        
        Args:
            harmonic_patterns: Harmonic resonance patterns
            
        Returns:
            Harmonic resonance validation
        """
        # Calculate unity score based on harmonic resonance strength
        unity_score = harmonic_patterns['strength']
        
        # Determine if unity is maintained
        unity_maintained = unity_score >= self.validation_thresholds['resonance']
        
        # Identify unity factors
        unity_factors = []
        
        if len(harmonic_patterns['first_order']['patterns']) > 0:
            unity_factors.append('first_order_harmonic')
        
        if len(harmonic_patterns['second_order']['patterns']) > 0:
            unity_factors.append('second_order_harmonic')
        
        if len(harmonic_patterns['third_order']['patterns']) > 0:
            unity_factors.append('third_order_harmonic')
        
        return {
            'unity_score': unity_score,
            'unity_maintained': unity_maintained,
            'unity_factors': unity_factors,
            'patterns': harmonic_patterns
        }
    
    def calculate_position_unity_score(self, characteristics):
        """
        Calculates unity score based on position characteristics.
        
        Args:
            characteristics: Position characteristics
            
        Returns:
            Unity score
        """
        # Calculate base score
        base_score = 0.5
        
        # Adjust score based on position type
        if characteristics['type'] == 'seed':
            base_score += 0.3
        elif characteristics['type'] == 'transition':
            base_score += 0.1
        elif characteristics['type'] == 'integration':
            base_score += 0.2
        
        # Adjust score based on polarity
        if characteristics['polarity'] == 'positive':
            base_score += 0.1
        
        # Adjust score based on stability
        if characteristics['stability'] == 'high':
            base_score += 0.1
        elif characteristics['stability'] == 'medium':
            base_score += 0.05
        
        return min(base_score, 1.0)  # Cap at 1.0
    
    def calculate_system_characteristics(self, S):
        """
        Calculates system characteristics.
        
        Args:
            S: System level
            
        Returns:
            System characteristics
        """
        # Check if system is prime
        is_prime = self.is_prime(S)
        
        # Check if system is in Fibonacci sequence
        fibonacci_numbers = self.generate_fibonacci_numbers(S * 2)
        is_fibonacci = S in fibonacci_numbers
        
        # Check if system is a power of the dimensional base
        is_power_of_base = False
        temp = 1
        while temp <= S:
            if temp == S:
                is_power_of_base = True
                break
            temp *= self.dimensional_base
        
        # Check if system is a multiple of the dimensional base
        is_multiple_of_base = (S % self.dimensional_base == 0)
        
        return {
            'is_prime': is_prime,
            'is_fibonacci': is_fibonacci,
            'is_power_of_base': is_power_of_base,
            'is_multiple_of_base': is_multiple_of_base
        }
    
    def calculate_system_unity_score(self, characteristics):
        """
        Calculates unity score based on system characteristics.
        
        Args:
            characteristics: System characteristics
            
        Returns:
            Unity score
        """
        # Calculate base score
        base_score = 0.5
        
        # Adjust score based on characteristics
        if characteristics['is_prime']:
            base_score += 0.2
        
        if characteristics['is_fibonacci']:
            base_score += 0.15
        
        if characteristics['is_power_of_base']:
            base_score += 0.1
        
        if characteristics['is_multiple_of_base']:
            base_score += 0.05
        
        return min(base_score, 1.0)  # Cap at 1.0
    
    def calculate_level_characteristics(self, L):
        """
        Calculates level characteristics.
        
        Args:
            L: Level
            
        Returns:
            Level characteristics
        """
        # Check if level is prime
        is_prime = self.is_prime(L)
        
        # Check if level is in Fibonacci sequence
        fibonacci_numbers = self.generate_fibonacci_numbers(self.dimensional_base * 2)
        is_fibonacci = L in fibonacci_numbers
        
        # Check if level is at a boundary
        is_boundary = (L == 1 or L == self.dimensional_base)
        
        # Check if level is in the golden section of the dimensional base
        golden_section = int(self.dimensional_base * 0.618)
        is_golden_section = (L == golden_section)
        
        return {
            'is_prime': is_prime,
            'is_fibonacci': is_fibonacci,
            'is_boundary': is_boundary,
            'is_golden_section': is_golden_section
        }
    
    def calculate_level_unity_score(self, characteristics):
        """
        Calculates unity score based on level characteristics.
        
        Args:
            characteristics: Level characteristics
            
        Returns:
            Unity score
        """
        # Calculate base score
        base_score = 0.5
        
        # Adjust score based on characteristics
        if characteristics['is_prime']:
            base_score += 0.15
        
        if characteristics['is_fibonacci']:
            base_score += 0.15
        
        if characteristics['is_boundary']:
            base_score += 0.1
        
        if characteristics['is_golden_section']:
            base_score += 0.1
        
        return min(base_score, 1.0)  # Cap at 1.0
    
    def calculate_domain_characteristics(self, D):
        """
        Calculates domain characteristics.
        
        Args:
            D: Domain
            
        Returns:
            Domain characteristics
        """
        # Check if domain is prime
        is_prime = self.is_prime(D)
        
        # Check if domain is in Fibonacci sequence
        fibonacci_numbers = self.generate_fibonacci_numbers(D * 2)
        is_fibonacci = D in fibonacci_numbers
        
        # Check if domain is the first domain
        is_first = (D == 1)
        
        # Check if domain is a power of the dimensional base
        is_power_of_base = False
        temp = 1
        while temp <= D:
            if temp == D:
                is_power_of_base = True
                break
            temp *= self.dimensional_base
        
        return {
            'is_prime': is_prime,
            'is_fibonacci': is_fibonacci,
            'is_first': is_first,
            'is_power_of_base': is_power_of_base
        }
    
    def calculate_domain_unity_score(self, characteristics):
        """
        Calculates unity score based on domain characteristics.
        
        Args:
            characteristics: Domain characteristics
            
        Returns:
            Unity score
        """
        # Calculate base score
        base_score = 0.5
        
        # Adjust score based on characteristics
        if characteristics['is_prime']:
            base_score += 0.15
        
        if characteristics['is_fibonacci']:
            base_score += 0.15
        
        if characteristics['is_first']:
            base_score += 0.1
        
        if characteristics['is_power_of_base']:
            base_score += 0.1
        
        return min(base_score, 1.0)  # Cap at 1.0
    
    def calculate_overall_unity_score(self, cycle_score, system_score, level_score, domain_score, cross_scale_score, resonance_score):
        """
        Calculates overall unity score.
        
        Args:
            cycle_score: Cycle unity score
            system_score: System unity score
            level_score: Level unity score
            domain_score: Domain unity score
            cross_scale_score: Cross-scale unity score
            resonance_score: Resonance unity score
            
        Returns:
            Overall unity score
        """
        # Calculate weighted average of scores
        weighted_score = (
            cycle_score * 0.15 +
            system_score * 0.15 +
            level_score * 0.15 +
            domain_score * 0.15 +
            cross_scale_score * 0.25 +
            resonance_score * 0.15
        )
        
        return weighted_score
    
    def update_validation_metrics(self, unity_maintained, overall_unity_score, cycle_validation, system_validation, level_validation, domain_validation, cross_scale_validation, resonance_validation):
        """
        Updates validation metrics.
        
        Args:
            unity_maintained: Whether unity is maintained
            overall_unity_score: Overall unity score
            cycle_validation: Cycle unity validation
            system_validation: System unity validation
            level_validation: Level unity validation
            domain_validation: Domain unity validation
            cross_scale_validation: Cross-scale unity validation
            resonance_validation: Resonance unity validation
        """
        # Update overall metrics
        self.validation_metrics['total_numbers_validated'] += 1
        
        if unity_maintained:
            self.validation_metrics['unity_maintained_count'] += 1
        else:
            self.validation_metrics['unity_violations_count'] += 1
            
        # Update average unity score
        total_score = self.validation_metrics['average_unity_score'] * (self.validation_metrics['total_numbers_validated'] - 1)
        total_score += overall_unity_score
        self.validation_metrics['average_unity_score'] = total_score / self.validation_metrics['total_numbers_validated']
        
        # Update scale-specific metrics
        self.update_scale_metrics('cycle', cycle_validation)
        self.update_scale_metrics('system', system_validation)
        self.update_scale_metrics('level', level_validation)
        self.update_scale_metrics('domain', domain_validation)
        
        # Update cross-scale metrics
        self.update_cross_scale_metrics('cycle_to_system', cross_scale_validation['cycle_to_system'])
        self.update_cross_scale_metrics('system_to_level', cross_scale_validation['system_to_level'])
        self.update_cross_scale_metrics('level_to_domain', cross_scale_validation['level_to_domain'])
        
        # Update resonance metrics
        self.update_resonance_metrics('intra_scale', resonance_validation['intra_scale'])
        self.update_resonance_metrics('cross_scale', resonance_validation['cross_scale'])
        self.update_resonance_metrics('harmonic', resonance_validation['harmonic'])
    
    def update_scale_metrics(self, scale_name, validation):
        """
        Updates scale-specific metrics.
        
        Args:
            scale_name: Name of the scale
            validation: Scale validation
        """
        metrics = self.validation_metrics['scale_specific_metrics'][scale_name]
        
        if validation['unity_maintained']:
            metrics['maintained'] += 1
        else:
            metrics['violated'] += 1
            
        # Update average score
        total_score = metrics['average_score'] * (metrics['maintained'] + metrics['violated'] - 1)
        total_score += validation['unity_score']
        metrics['average_score'] = total_score / (metrics['maintained'] + metrics['violated'])
    
    def update_cross_scale_metrics(self, scale_pair, validation):
        """
        Updates cross-scale metrics.
        
        Args:
            scale_pair: Name of the scale pair
            validation: Cross-scale validation
        """
        metrics = self.validation_metrics['cross_scale_metrics'][scale_pair]
        
        if validation['unity_maintained']:
            metrics['maintained'] += 1
        else:
            metrics['violated'] += 1
            
        # Update average score
        total_score = metrics['average_score'] * (metrics['maintained'] + metrics['violated'] - 1)
        total_score += validation['unity_score']
        metrics['average_score'] = total_score / (metrics['maintained'] + metrics['violated'])
    
    def update_resonance_metrics(self, resonance_type, validation):
        """
        Updates resonance metrics.
        
        Args:
            resonance_type: Type of resonance
            validation: Resonance validation
        """
        metrics = self.validation_metrics['resonance_metrics'][resonance_type]
        
        if validation['unity_maintained']:
            metrics['maintained'] += 1
        else:
            metrics['violated'] += 1
            
        # Update average score
        total_score = metrics['average_score'] * (metrics['maintained'] + metrics['violated'] - 1)
        total_score += validation['unity_score']
        metrics['average_score'] = total_score / (metrics['maintained'] + metrics['violated'])
    
    def get_validation_metrics(self):
        """
        Gets the current validation metrics.
        
        Returns:
            Validation metrics
        """
        return self.validation_metrics
    
    def get_validation_history(self):
        """
        Gets the validation history.
        
        Returns:
            Validation history
        """
        return self.validation_history
    
    def save_validation_metrics(self, filename):
        """
        Saves validation metrics to a file.
        
        Args:
            filename: Name of the file to save to
        """
        with open(filename, 'w') as f:
            json.dump(self.validation_metrics, f, indent=4)
    
    def save_validation_history(self, filename):
        """
        Saves validation history to a file.
        
        Args:
            filename: Name of the file to save to
        """
        # Convert validation history to a simpler format for saving
        simplified_history = []
        for validation in self.validation_history:
            simplified = {
                'number': validation['number'],
                'unity_maintained': validation['unity_maintained'],
                'overall_unity_score': validation['overall_unity_score']
            }
            simplified_history.append(simplified)
            
        with open(filename, 'w') as f:
            json.dump(simplified_history, f, indent=4)
    
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
def test_contextual_unity_validator():
    """
    Tests the ContextualUnityValidator class.
    """
    validator = ContextualUnityValidator()
    
    # Test for a few numbers
    test_cases = [1, 13, 14, 170]
    
    for n in test_cases:
        # Validate contextual unity
        validation = validator.validate_contextual_unity(n)
        print(f"Number {n}:")
        print(f"  Unity maintained: {validation['unity_maintained']}")
        print(f"  Overall unity score: {validation['overall_unity_score']}")
        
        # Print scale validations
        print("  Scale validations:")
        for scale, scale_validation in validation['scale_validations'].items():
            print(f"    {scale}: {scale_validation['unity_maintained']} (score: {scale_validation['unity_score']})")
        
        # Print cross-scale validation
        print("  Cross-scale validation:")
        print(f"    Unity maintained: {validation['cross_scale_validation']['unity_maintained']}")
        print(f"    Unity score: {validation['cross_scale_validation']['unity_score']}")
        
        # Print resonance validation
        print("  Resonance validation:")
        print(f"    Unity maintained: {validation['resonance_validation']['unity_maintained']}")
        print(f"    Unity score: {validation['resonance_validation']['unity_score']}")
        
        print()
    
    # Print validation metrics
    metrics = validator.get_validation_metrics()
    print("Validation metrics:")
    print(f"  Total numbers validated: {metrics['total_numbers_validated']}")
    print(f"  Unity maintained count: {metrics['unity_maintained_count']}")
    print(f"  Unity violations count: {metrics['unity_violations_count']}")
    print(f"  Average unity score: {metrics['average_unity_score']}")


if __name__ == "__main__":
    test_contextual_unity_validator()
