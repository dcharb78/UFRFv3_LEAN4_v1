"""
Standalone Test for Unified Context Implementation

This module provides a standalone test for the Unified Context implementation
without requiring external dependencies.

Author: Daniel Charboneau
License: Creative Commons Attribution-NonCommercial 4.0 International
"""

import os
import sys
import json
import time
import random
import numpy as np
import matplotlib.pyplot as plt
from datetime import datetime

# Create output directory
output_dir = "./test_results"
os.makedirs(output_dir, exist_ok=True)

class MockPhaseDetector:
    """Mock implementation of PhaseDetector for testing purposes."""
    
    def detect_phases(self, n, dimensional_mapping, previous_mappings=None):
        """
        Detects phases for a number.
        
        Args:
            n: Number to process
            dimensional_mapping: Dimensional mapping of the number
            previous_mappings: Previous dimensional mappings (optional)
            
        Returns:
            Detected phases
        """
        phases = []
        
        # Detect cycle completion phases
        if n % 8 == 0:
            phases.append({
                'type': 'cycle_completion',
                'subtype': 'primary_cycle',
                'description': f"Primary cycle completion at number {n}"
            })
        
        # Detect dimension boundary phases
        if n % 13 == 0:
            phases.append({
                'type': 'dimension_boundary',
                'subtype': 'primary_dimension',
                'description': f"Primary dimension boundary at number {n}"
            })
        
        # Detect position phases
        if n % 7 == 0:
            phases.append({
                'type': 'position',
                'subtype': 'primary_position',
                'description': f"Primary position at number {n}"
            })
        
        # Detect resonance phases
        if n % 11 == 0:
            phases.append({
                'type': 'resonance',
                'subtype': 'primary_resonance',
                'description': f"Primary resonance at number {n}"
            })
        
        # Ensure at least one phase is detected
        if not phases:
            phases.append({
                'type': 'default',
                'subtype': 'default',
                'description': f"Default phase at number {n}"
            })
        
        return phases

class MockAnalysisTriggerSystem:
    """Mock implementation of AnalysisTriggerSystem for testing purposes."""
    
    def determine_analyses(self, phases):
        """
        Determines which analyses to run based on detected phases.
        
        Args:
            phases: Detected phases
            
        Returns:
            Analyses to run
        """
        analyses_to_run = []
        
        # Determine analyses based on phase types
        for phase in phases:
            if phase['type'] == 'cycle_completion':
                analyses_to_run.append('pattern')
            
            if phase['type'] == 'dimension_boundary':
                analyses_to_run.append('geometry')
            
            if phase['type'] == 'position':
                analyses_to_run.append('feature')
            
            if phase['type'] == 'resonance':
                analyses_to_run.append('resonance')
        
        # Ensure at least one analysis is run
        if not analyses_to_run:
            analyses_to_run.append('geometry')
        
        return analyses_to_run

class MockFeatureIntegrationSystem:
    """Mock implementation of FeatureIntegrationSystem for testing purposes."""
    
    def integrate_feature(self, feature):
        """
        Integrates a feature.
        
        Args:
            feature: Feature to integrate
            
        Returns:
            Integration result
        """
        # Simulate feature integration
        success = random.random() > 0.1  # 90% success rate
        
        return {
            'success': success,
            'feature_id': f"feature_{int(time.time())}_{random.randint(1000, 9999)}",
            'integration_time': random.uniform(0.001, 0.01)
        }

class ContextualUnityDetector:
    """
    Detects contextual unity for elements in the UFRF Framework.
    """
    
    def __init__(self, dimensional_base=13):
        """
        Initialize the contextual unity detector.
        
        Args:
            dimensional_base: Base for dimensional calculations (default: 13)
        """
        self.dimensional_base = dimensional_base
    
    def detect_unity(self, n, dimensional_mapping):
        """
        Detects unity for a number.
        
        Args:
            n: Number to detect unity for
            dimensional_mapping: Dimensional mapping of the number
            
        Returns:
            Unity detection result
        """
        # Extract contextual scales from dimensional mapping
        cycle_context = dimensional_mapping.get('cycle', 1)
        system_context = dimensional_mapping.get('system', 1)
        level_context = dimensional_mapping.get('level', 1)
        domain_context = dimensional_mapping.get('domain', 1)
        
        # Calculate unity function
        unity_value = self.calculate_unity_function(n, cycle_context, system_context, level_context, domain_context)
        
        # Evaluate unity maintenance
        unity_maintained = self.evaluate_unity_maintenance(unity_value)
        
        return {
            'number': n,
            'dimensional_mapping': dimensional_mapping,
            'unity_value': unity_value,
            'unity_maintained': unity_maintained
        }
    
    def calculate_unity_function(self, e, c, S, L, D):
        """
        Calculates the unity function Ω(e, c, S, L, D) = e/E(c, S, L, D).
        
        Args:
            e: Element being evaluated
            c: Cycle context
            S: System context
            L: Level context
            D: Domain context
            
        Returns:
            Unity function value
        """
        # Calculate contextual environment function E(c, S, L, D)
        E = self.calculate_contextual_environment(c, S, L, D)
        
        # Calculate unity function Ω(e, c, S, L, D) = e/E(c, S, L, D)
        if E != 0:
            omega = e / E
        else:
            omega = 0
        
        return omega
    
    def calculate_contextual_environment(self, c, S, L, D):
        """
        Calculates the contextual environment function E(c, S, L, D).
        
        Args:
            c: Cycle context
            S: System context
            L: Level context
            D: Domain context
            
        Returns:
            Contextual environment value
        """
        # Simple implementation for testing
        # In a real implementation, this would involve more complex calculations
        E = (c * S * L * D) % self.dimensional_base
        
        # Ensure E is not zero to avoid division by zero
        if E == 0:
            E = 1
        
        return E
    
    def evaluate_unity_maintenance(self, unity_value):
        """
        Evaluates whether unity is maintained.
        
        Args:
            unity_value: Unity function value
            
        Returns:
            Whether unity is maintained
        """
        # Unity is maintained if the unity value is approximately 1
        # Allow for some numerical precision issues
        return 0.9 <= unity_value <= 1.1

class EnhancedDimensionalMapper:
    """
    Maps numbers to dimensional representations with unity considerations.
    """
    
    def __init__(self, dimensional_base=13):
        """
        Initialize the enhanced dimensional mapper.
        
        Args:
            dimensional_base: Base for dimensional calculations (default: 13)
        """
        self.dimensional_base = dimensional_base
    
    def map_with_unity(self, n):
        """
        Maps a number with unity considerations.
        
        Args:
            n: Number to map
            
        Returns:
            Dimensional mapping with unity context
        """
        # Calculate dimensional position
        position = self.calculate_dimensional_position(n)
        
        # Determine unity context
        unity_context = self.determine_unity_context(n, position)
        
        # Create dimensional mapping
        dimensional_mapping = {
            'number': n,
            'position': position,
            'dimension': position % self.dimensional_base,
            'cycle': position // self.dimensional_base + 1,
            'system': (position // (self.dimensional_base * 8)) + 1,
            'level': (position // (self.dimensional_base * 8 * 8)) + 1,
            'domain': (position // (self.dimensional_base * 8 * 8 * 8)) + 1,
            'unity_context': unity_context
        }
        
        return dimensional_mapping
    
    def calculate_dimensional_position(self, n):
        """
        Calculates dimensional position.
        
        Args:
            n: Number to calculate position for
            
        Returns:
            Dimensional position
        """
        # Simple implementation for testing
        # In a real implementation, this would involve more complex calculations
        return n - 1
    
    def determine_unity_context(self, n, position):
        """
        Determines unity context for a position.
        
        Args:
            n: Number
            position: Dimensional position
            
        Returns:
            Unity context
        """
        # Simple implementation for testing
        # In a real implementation, this would involve more complex calculations
        cycle_unity = (position % (self.dimensional_base * 8)) == 0
        system_unity = (position % (self.dimensional_base * 8 * 8)) == 0
        level_unity = (position % (self.dimensional_base * 8 * 8 * 8)) == 0
        
        return {
            'cycle_unity': cycle_unity,
            'system_unity': system_unity,
            'level_unity': level_unity,
            'overall_unity': cycle_unity or system_unity or level_unity
        }

class CrossScaleContextAnalyzer:
    """
    Analyzes contextual relationships across different scales.
    """
    
    def __init__(self, dimensional_base=13):
        """
        Initialize the cross-scale context analyzer.
        
        Args:
            dimensional_base: Base for dimensional calculations (default: 13)
        """
        self.dimensional_base = dimensional_base
    
    def analyze_cross_scale_context(self, n, dimensional_mapping):
        """
        Analyzes cross-scale context.
        
        Args:
            n: Number to analyze
            dimensional_mapping: Dimensional mapping of the number
            
        Returns:
            Cross-scale context analysis
        """
        # Extract scale data from dimensional mapping
        scale_data = {
            'cycle': dimensional_mapping.get('cycle', 1),
            'system': dimensional_mapping.get('system', 1),
            'level': dimensional_mapping.get('level', 1),
            'domain': dimensional_mapping.get('domain', 1)
        }
        
        # Calculate scale coherence
        scale_coherence = self.calculate_scale_coherence(scale_data)
        
        # Calculate cross-scale coherence
        cross_scale_coherence = self.calculate_cross_scale_coherence(scale_data)
        
        # Calculate overall coherence
        overall_coherence = (sum(scale_coherence.values()) + cross_scale_coherence) / (len(scale_coherence) + 1)
        
        return {
            'number': n,
            'dimensional_mapping': dimensional_mapping,
            'scale_data': scale_data,
            'scale_coherence': scale_coherence,
            'cross_scale_coherence': cross_scale_coherence,
            'overall_coherence': overall_coherence
        }
    
    def calculate_scale_coherence(self, scale_data):
        """
        Calculates coherence within each scale.
        
        Args:
            scale_data: Scale data
            
        Returns:
            Scale coherence
        """
        # Simple implementation for testing
        # In a real implementation, this would involve more complex calculations
        scale_coherence = {}
        
        for scale_name, scale_value in scale_data.items():
            # Calculate coherence based on scale value
            coherence = 1.0 - (scale_value % self.dimensional_base) / self.dimensional_base
            scale_coherence[scale_name] = coherence
        
        return scale_coherence
    
    def calculate_cross_scale_coherence(self, scale_data):
        """
        Calculates coherence across scales.
        
        Args:
            scale_data: Scale data
            
        Returns:
            Cross-scale coherence
        """
        # Simple implementation for testing
        # In a real implementation, this would involve more complex calculations
        cycle = scale_data.get('cycle', 1)
        system = scale_data.get('system', 1)
        level = scale_data.get('level', 1)
        domain = scale_data.get('domain', 1)
        
        # Calculate cross-scale coherence based on relationships between scales
        coherence = 1.0 - abs((cycle / system) - (system / level)) / self.dimensional_base
        
        return max(0.0, min(1.0, coherence))

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
    
    def recognize_resonance_patterns(self, n, dimensional_mapping):
        """
        Recognizes resonance patterns.
        
        Args:
            n: Number to analyze
            dimensional_mapping: Dimensional mapping of the number
            
        Returns:
            Recognized resonance patterns
        """
        # Detect intra-scale resonance
        intra_scale_resonance = self.detect_intra_scale_resonance(n, dimensional_mapping)
        
        # Detect cross-scale resonance
        cross_scale_resonance = self.detect_cross_scale_resonance(n, dimensional_mapping)
        
        # Detect harmonic resonance
        harmonic_resonance = self.detect_harmonic_resonance(n, dimensional_mapping)
        
        # Calculate overall resonance strength
        overall_strength = (intra_scale_resonance['strength'] + cross_scale_resonance['strength'] + harmonic_resonance['strength']) / 3
        
        return {
            'number': n,
            'dimensional_mapping': dimensional_mapping,
            'intra_scale': intra_scale_resonance,
            'cross_scale': cross_scale_resonance,
            'harmonic': harmonic_resonance,
            'overall_strength': overall_strength
        }
    
    def detect_intra_scale_resonance(self, n, dimensional_mapping):
        """
        Detects resonance within scales.
        
        Args:
            n: Number to analyze
            dimensional_mapping: Dimensional mapping of the number
            
        Returns:
            Intra-scale resonance
        """
        # Simple implementation for testing
        # In a real implementation, this would involve more complex calculations
        cycle = dimensional_mapping.get('cycle', 1)
        dimension = dimensional_mapping.get('dimension', 0)
        
        # Calculate resonance strength based on relationship between cycle and dimension
        strength = 1.0 - (dimension / self.dimensional_base)
        
        return {
            'type': 'intra_scale',
            'strength': max(0.0, min(1.0, strength)),
            'description': f"Intra-scale resonance with strength {strength:.2f}"
        }
    
    def detect_cross_scale_resonance(self, n, dimensional_mapping):
        """
        Detects resonance across scales.
        
        Args:
            n: Number to analyze
            dimensional_mapping: Dimensional mapping of the number
            
        Returns:
            Cross-scale resonance
        """
        # Simple implementation for testing
        # In a real implementation, this would involve more complex calculations
        cycle = dimensional_mapping.get('cycle', 1)
        system = dimensional_mapping.get('system', 1)
        
        # Calculate resonance strength based on relationship between cycle and system
        strength = 1.0 - abs(1 - (cycle / (system * 8))) if system > 0 else 0.0
        
        return {
            'type': 'cross_scale',
            'strength': max(0.0, min(1.0, strength)),
            'description': f"Cross-scale resonance with strength {strength:.2f}"
        }
    
    def detect_harmonic_resonance(self, n, dimensional_mapping):
        """
        Detects harmonic resonance.
        
        Args:
            n: Number to analyze
            dimensional_mapping: Dimensional mapping of the number
            
        Returns:
            Harmonic resonance
        """
        # Simple implementation for testing
        # In a real implementation, this would involve more complex calculations
        position = dimensional_mapping.get('position', 0)
        
        # Calculate resonance strength based on position
        strength = 1.0 - ((position % 12) / 12)
        
        return {
            'type': 'harmonic',
            'strength': max(0.0, min(1.0, strength)),
            'description': f"Harmonic resonance with strength {strength:.2f}"
        }

class ContextualUnityValidator:
    """
    Validates that the "Always One in Context" principle is maintained.
    """
    
    def __init__(self, dimensional_base=13):
        """
        Initialize the contextual unity validator.
        
        Args:
            dimensional_base: Base for dimensional calculations (default: 13)
        """
        self.dimensional_base = dimensional_base
        self.unity_detector = ContextualUnityDetector(dimensional_base)
        self.context_analyzer = CrossScaleContextAnalyzer(dimensional_base)
        self.pattern_recognizer = ResonancePatternRecognizer(dimensional_base)
    
    def validate_contextual_unity(self, n, dimensional_mapping):
        """
        Validates contextual unity.
        
        Args:
            n: Number to validate
            dimensional_mapping: Dimensional mapping of the number
            
        Returns:
            Validation result
        """
        # Detect unity
        unity_detection = self.unity_detector.detect_unity(n, dimensional_mapping)
        
        # Analyze cross-scale context
        cross_scale_context = self.context_analyzer.analyze_cross_scale_context(n, dimensional_mapping)
        
        # Recognize resonance patterns
        resonance_patterns = self.pattern_recognizer.recognize_resonance_patterns(n, dimensional_mapping)
        
        # Validate unity within each scale
        scale_validations = {}
        for scale_name, scale_coherence in cross_scale_context['scale_coherence'].items():
            scale_validations[scale_name] = self.validate_scale_unity(scale_name, {
                'coherence': scale_coherence,
                'value': cross_scale_context['scale_data'][scale_name]
            })
        
        # Validate unity across scales
        cross_scale_validation = self.validate_cross_scale_unity(cross_scale_context)
        
        # Validate unity in resonance patterns
        resonance_validation = self.validate_resonance_unity(resonance_patterns)
        
        # Calculate overall unity score
        scale_scores = [validation['unity_score'] for validation in scale_validations.values()]
        overall_unity_score = (sum(scale_scores) + cross_scale_validation['unity_score'] + resonance_validation['unity_score']) / (len(scale_scores) + 2)
        
        return {
            'number': n,
            'dimensional_mapping': dimensional_mapping,
            'unity_maintained': unity_detection['unity_maintained'],
            'unity_value': unity_detection['unity_value'],
            'scale_validations': scale_validations,
            'cross_scale_validation': cross_scale_validation,
            'resonance_validation': resonance_validation,
            'overall_unity_score': overall_unity_score
        }
    
    def validate_scale_unity(self, scale_name, scale_data):
        """
        Validates unity within a scale.
        
        Args:
            scale_name: Name of the scale
            scale_data: Scale data
            
        Returns:
            Scale validation result
        """
        # Simple implementation for testing
        # In a real implementation, this would involve more complex calculations
        coherence = scale_data.get('coherence', 0.0)
        value = scale_data.get('value', 1)
        
        # Calculate unity score based on coherence and value
        unity_score = coherence * (1.0 - (value % self.dimensional_base) / self.dimensional_base)
        
        # Determine if unity is maintained within the scale
        unity_maintained = unity_score > 0.7
        
        return {
            'scale_name': scale_name,
            'unity_score': unity_score,
            'unity_maintained': unity_maintained,
            'description': f"Unity {'maintained' if unity_maintained else 'not maintained'} within {scale_name} scale with score {unity_score:.2f}"
        }
    
    def validate_cross_scale_unity(self, cross_scale_context):
        """
        Validates unity across scales.
        
        Args:
            cross_scale_context: Cross-scale context
            
        Returns:
            Cross-scale validation result
        """
        # Simple implementation for testing
        # In a real implementation, this would involve more complex calculations
        cross_scale_coherence = cross_scale_context.get('cross_scale_coherence', 0.0)
        
        # Calculate unity score based on cross-scale coherence
        unity_score = cross_scale_coherence
        
        # Determine if unity is maintained across scales
        unity_maintained = unity_score > 0.7
        
        return {
            'unity_score': unity_score,
            'unity_maintained': unity_maintained,
            'description': f"Unity {'maintained' if unity_maintained else 'not maintained'} across scales with score {unity_score:.2f}"
        }
    
    def validate_resonance_unity(self, resonance_patterns):
        """
        Validates unity in resonance patterns.
        
        Args:
            resonance_patterns: Resonance patterns
            
        Returns:
            Resonance validation result
        """
        # Simple implementation for testing
        # In a real implementation, this would involve more complex calculations
        overall_strength = resonance_patterns.get('overall_strength', 0.0)
        
        # Calculate unity score based on overall resonance strength
        unity_score = overall_strength
        
        # Determine if unity is maintained in resonance patterns
        unity_maintained = unity_score > 0.7
        
        return {
            'unity_score': unity_score,
            'unity_maintained': unity_maintained,
            'description': f"Unity {'maintained' if unity_maintained else 'not maintained'} in resonance patterns with score {unity_score:.2f}"
        }

class UnifiedContextIntegrator:
    """
    Integrates the Unified Context components with the Real-Time Discovery System.
    """
    
    def __init__(self, dimensional_base=13):
        """
        Initialize the unified context integrator.
        
        Args:
            dimensional_base: Base for dimensional calculations (default: 13)
        """
        self.dimensional_base = dimensional_base
        
        # Initialize Unified Context components
        self.unity_detector = ContextualUnityDetector(dimensional_base)
        self.dimensional_mapper = EnhancedDimensionalMapper(dimensional_base)
        self.context_analyzer = CrossScaleContextAnalyzer(dimensional_base)
        self.pattern_recognizer = ResonancePatternRecognizer(dimensional_base)
        self.unity_validator = ContextualUnityValidator(dimensional_base)
        
        # Initialize Real-Time Discovery components (using mock implementations for testing)
        self.phase_detector = MockPhaseDetector()
        self.analysis_trigger = MockAnalysisTriggerSystem()
        self.feature_integrator = MockFeatureIntegrationSystem()
        
        # Initialize integration metrics
        self.integration_metrics = {
            'total_numbers_processed': 0,
            'phases_detected': 0,
            'analyses_triggered': 0,
            'features_discovered': 0,
            'unity_maintained_count': 0,
            'unity_violations_count': 0,
            'average_unity_score': 0.0,
            'average_processing_time': 0.0
        }
        
        # Initialize integration history
        self.integration_history = []
    
    def process_number(self, n, previous_mappings=None):
        """
        Processes a number through the integrated system.
        
        Args:
            n: Number to process
            previous_mappings: Previous dimensional mappings (optional)
            
        Returns:
            Processing results
        """
        start_time = time.time()
        
        # Map number with unity
        dimensional_mapping = self.dimensional_mapper.map_with_unity(n)
        
        # Detect phases
        phases = self.phase_detector.detect_phases(n, dimensional_mapping, previous_mappings)
        
        # Determine analyses to run
        analyses_to_run = self.analysis_trigger.determine_analyses(phases)
        
        # Validate contextual unity
        unity_validation = self.unity_validator.validate_contextual_unity(n, dimensional_mapping)
        
        # Initialize processing results
        processing_results = {
            'number': n,
            'dimensional_mapping': dimensional_mapping,
            'phases': phases,
            'analyses_to_run': analyses_to_run,
            'unity_validation': unity_validation,
            'features_discovered': [],
            'processing_time': 0.0
        }
        
        # Run analyses and discover features
        if analyses_to_run:
            features = self.run_analyses(n, dimensional_mapping, phases, analyses_to_run, unity_validation)
            processing_results['features_discovered'] = features
        
        # Calculate processing time
        processing_time = time.time() - start_time
        processing_results['processing_time'] = processing_time
        
        # Update integration metrics
        self.update_integration_metrics(processing_results)
        
        # Add to integration history
        self.integration_history.append(processing_results)
        
        return processing_results
    
    def run_analyses(self, n, dimensional_mapping, phases, analyses_to_run, unity_validation):
        """
        Runs analyses and discovers features.
        
        Args:
            n: Number being processed
            dimensional_mapping: Dimensional mapping of the number
            phases: Detected phases
            analyses_to_run: Analyses to run
            unity_validation: Unity validation results
            
        Returns:
            Discovered features
        """
        discovered_features = []
        
        # Run each analysis
        for analysis_type in analyses_to_run:
            # Run analysis based on type
            if analysis_type == 'geometry':
                features = self.analyze_geometry(n, dimensional_mapping, phases, unity_validation)
                discovered_features.extend(features)
            
            elif analysis_type == 'resonance':
                features = self.analyze_resonance(n, dimensional_mapping, phases, unity_validation)
                discovered_features.extend(features)
            
            elif analysis_type == 'pattern':
                features = self.analyze_pattern(n, dimensional_mapping, phases, unity_validation)
                discovered_features.extend(features)
            
            elif analysis_type == 'feature':
                features = self.analyze_feature(n, dimensional_mapping, phases, unity_validation)
                discovered_features.extend(features)
        
        # Validate and integrate features
        validated_features = []
        for feature in discovered_features:
            # Validate feature
            validation_result = self.validate_feature(feature, unity_validation)
            
            if validation_result['is_valid']:
                # Integrate feature
                integration_result = self.feature_integrator.integrate_feature(feature)
                
                if integration_result['success']:
                    validated_features.append({
                        'feature': feature,
                        'validation': validation_result,
                        'integration': integration_result
                    })
        
        return validated_features
    
    def analyze_geometry(self, n, dimensional_mapping, phases, unity_validation):
        """
        Analyzes geometry and discovers features.
        
        Args:
            n: Number being processed
            dimensional_mapping: Dimensional mapping of the number
            phases: Detected phases
            unity_validation: Unity validation results
            
        Returns:
            Discovered features
        """
        features = []
        
        # Analyze cross-scale context
        cross_scale_context = self.context_analyzer.analyze_cross_scale_context(n, dimensional_mapping)
        
        # Check for high coherence
        if cross_scale_context['overall_coherence'] > 0.8:
            # Create feature for high cross-scale coherence
            feature = {
                'type': 'geometry',
                'subtype': 'cross_scale_coherence',
                'number': n,
                'dimensional_mapping': dimensional_mapping,
                'coherence': cross_scale_context['overall_coherence'],
                'description': f"High cross-scale coherence ({cross_scale_context['overall_coherence']:.2f}) at number {n}",
                'unity_maintained': unity_validation['unity_maintained'],
                'discovery_phase': [phase for phase in phases if phase['type'] == 'dimension_boundary'][0] if any(phase['type'] == 'dimension_boundary' for phase in phases) else phases[0]
            }
            
            features.append(feature)
        
        # Check for dimensional boundary features
        if any(phase['type'] == 'dimension_boundary' for phase in phases):
            # Get dimensional boundary phase
            boundary_phase = [phase for phase in phases if phase['type'] == 'dimension_boundary'][0]
            
            # Create feature for dimensional boundary
            feature = {
                'type': 'geometry',
                'subtype': 'dimensional_boundary',
                'number': n,
                'dimensional_mapping': dimensional_mapping,
                'boundary_type': boundary_phase['subtype'],
                'description': f"Dimensional boundary ({boundary_phase['subtype']}) at number {n}",
                'unity_maintained': unity_validation['unity_maintained'],
                'discovery_phase': boundary_phase
            }
            
            features.append(feature)
        
        # Check for position features
        if any(phase['type'] == 'position' for phase in phases):
            # Get position phase
            position_phase = [phase for phase in phases if phase['type'] == 'position'][0]
            
            # Create feature for position
            feature = {
                'type': 'geometry',
                'subtype': 'position',
                'number': n,
                'dimensional_mapping': dimensional_mapping,
                'position_type': position_phase['subtype'],
                'description': f"Position feature ({position_phase['subtype']}) at number {n}",
                'unity_maintained': unity_validation['unity_maintained'],
                'discovery_phase': position_phase
            }
            
            features.append(feature)
        
        return features
    
    def analyze_resonance(self, n, dimensional_mapping, phases, unity_validation):
        """
        Analyzes resonance and discovers features.
        
        Args:
            n: Number being processed
            dimensional_mapping: Dimensional mapping of the number
            phases: Detected phases
            unity_validation: Unity validation results
            
        Returns:
            Discovered features
        """
        features = []
        
        # Recognize resonance patterns
        resonance_patterns = self.pattern_recognizer.recognize_resonance_patterns(n, dimensional_mapping)
        
        # Check for strong overall resonance
        if resonance_patterns['overall_strength'] > 0.7:
            # Create feature for strong overall resonance
            feature = {
                'type': 'resonance',
                'subtype': 'overall',
                'number': n,
                'dimensional_mapping': dimensional_mapping,
                'strength': resonance_patterns['overall_strength'],
                'description': f"Strong overall resonance ({resonance_patterns['overall_strength']:.2f}) at number {n}",
                'unity_maintained': unity_validation['unity_maintained'],
                'discovery_phase': [phase for phase in phases if phase['type'] == 'resonance'][0] if any(phase['type'] == 'resonance' for phase in phases) else phases[0]
            }
            
            features.append(feature)
        
        # Check for strong intra-scale resonance
        if resonance_patterns['intra_scale']['strength'] > 0.7:
            # Create feature for strong intra-scale resonance
            feature = {
                'type': 'resonance',
                'subtype': 'intra_scale',
                'number': n,
                'dimensional_mapping': dimensional_mapping,
                'strength': resonance_patterns['intra_scale']['strength'],
                'description': f"Strong intra-scale resonance ({resonance_patterns['intra_scale']['strength']:.2f}) at number {n}",
                'unity_maintained': unity_validation['unity_maintained'],
                'discovery_phase': [phase for phase in phases if phase['type'] == 'resonance'][0] if any(phase['type'] == 'resonance' for phase in phases) else phases[0]
            }
            
            features.append(feature)
        
        # Check for strong cross-scale resonance
        if resonance_patterns['cross_scale']['strength'] > 0.7:
            # Create feature for strong cross-scale resonance
            feature = {
                'type': 'resonance',
                'subtype': 'cross_scale',
                'number': n,
                'dimensional_mapping': dimensional_mapping,
                'strength': resonance_patterns['cross_scale']['strength'],
                'description': f"Strong cross-scale resonance ({resonance_patterns['cross_scale']['strength']:.2f}) at number {n}",
                'unity_maintained': unity_validation['unity_maintained'],
                'discovery_phase': [phase for phase in phases if phase['type'] == 'resonance'][0] if any(phase['type'] == 'resonance' for phase in phases) else phases[0]
            }
            
            features.append(feature)
        
        # Check for strong harmonic resonance
        if resonance_patterns['harmonic']['strength'] > 0.7:
            # Create feature for strong harmonic resonance
            feature = {
                'type': 'resonance',
                'subtype': 'harmonic',
                'number': n,
                'dimensional_mapping': dimensional_mapping,
                'strength': resonance_patterns['harmonic']['strength'],
                'description': f"Strong harmonic resonance ({resonance_patterns['harmonic']['strength']:.2f}) at number {n}",
                'unity_maintained': unity_validation['unity_maintained'],
                'discovery_phase': [phase for phase in phases if phase['type'] == 'resonance'][0] if any(phase['type'] == 'resonance' for phase in phases) else phases[0]
            }
            
            features.append(feature)
        
        return features
    
    def analyze_pattern(self, n, dimensional_mapping, phases, unity_validation):
        """
        Analyzes patterns and discovers features.
        
        Args:
            n: Number being processed
            dimensional_mapping: Dimensional mapping of the number
            phases: Detected phases
            unity_validation: Unity validation results
            
        Returns:
            Discovered features
        """
        features = []
        
        # Check for cycle completion patterns
        if any(phase['type'] == 'cycle_completion' for phase in phases):
            # Get cycle completion phase
            cycle_phase = [phase for phase in phases if phase['type'] == 'cycle_completion'][0]
            
            # Create feature for cycle completion
            feature = {
                'type': 'pattern',
                'subtype': 'cycle_completion',
                'number': n,
                'dimensional_mapping': dimensional_mapping,
                'cycle_type': cycle_phase['subtype'],
                'description': f"Cycle completion pattern ({cycle_phase['subtype']}) at number {n}",
                'unity_maintained': unity_validation['unity_maintained'],
                'discovery_phase': cycle_phase
            }
            
            features.append(feature)
        
        return features
    
    def analyze_feature(self, n, dimensional_mapping, phases, unity_validation):
        """
        Analyzes features and discovers meta-features.
        
        Args:
            n: Number being processed
            dimensional_mapping: Dimensional mapping of the number
            phases: Detected phases
            unity_validation: Unity validation results
            
        Returns:
            Discovered features
        """
        features = []
        
        # Check for high unity score
        if unity_validation['overall_unity_score'] > 0.9:
            # Create feature for high unity score
            feature = {
                'type': 'feature',
                'subtype': 'high_unity',
                'number': n,
                'dimensional_mapping': dimensional_mapping,
                'unity_score': unity_validation['overall_unity_score'],
                'description': f"High unity score ({unity_validation['overall_unity_score']:.2f}) at number {n}",
                'unity_maintained': unity_validation['unity_maintained'],
                'discovery_phase': phases[0]
            }
            
            features.append(feature)
        
        # Check for perfect scale-specific unity
        for scale_name, scale_validation in unity_validation['scale_validations'].items():
            if scale_validation['unity_score'] > 0.95:
                # Create feature for perfect scale-specific unity
                feature = {
                    'type': 'feature',
                    'subtype': f'perfect_{scale_name}_unity',
                    'number': n,
                    'dimensional_mapping': dimensional_mapping,
                    'unity_score': scale_validation['unity_score'],
                    'description': f"Perfect {scale_name} unity ({scale_validation['unity_score']:.2f}) at number {n}",
                    'unity_maintained': unity_validation['unity_maintained'],
                    'discovery_phase': phases[0]
                }
                
                features.append(feature)
        
        # Check for perfect cross-scale unity
        if unity_validation['cross_scale_validation']['unity_score'] > 0.95:
            # Create feature for perfect cross-scale unity
            feature = {
                'type': 'feature',
                'subtype': 'perfect_cross_scale_unity',
                'number': n,
                'dimensional_mapping': dimensional_mapping,
                'unity_score': unity_validation['cross_scale_validation']['unity_score'],
                'description': f"Perfect cross-scale unity ({unity_validation['cross_scale_validation']['unity_score']:.2f}) at number {n}",
                'unity_maintained': unity_validation['unity_maintained'],
                'discovery_phase': phases[0]
            }
            
            features.append(feature)
        
        return features
    
    def validate_feature(self, feature, unity_validation):
        """
        Validates a discovered feature.
        
        Args:
            feature: Feature to validate
            unity_validation: Unity validation results
            
        Returns:
            Validation result
        """
        # Initialize validation result
        validation_result = {
            'is_valid': False,
            'validation_score': 0.0,
            'validation_factors': []
        }
        
        # Calculate validation score based on feature type
        if feature['type'] == 'geometry':
            validation_score = 0.8
        elif feature['type'] == 'resonance':
            validation_score = 0.85
        elif feature['type'] == 'pattern':
            validation_score = 0.9
        elif feature['type'] == 'feature':
            validation_score = 0.95
        else:
            validation_score = 0.7
        
        # Adjust score based on unity maintenance
        if feature['unity_maintained']:
            validation_score += 0.1
        else:
            validation_score -= 0.2
        
        # Ensure score is in range [0, 1]
        validation_score = max(0.0, min(1.0, validation_score))
        
        # Determine if feature is valid
        is_valid = validation_score >= 0.7
        
        # Identify validation factors
        validation_factors = []
        
        if feature['unity_maintained']:
            validation_factors.append('unity_maintained')
        
        if 'strength' in feature and feature['strength'] > 0.7:
            validation_factors.append('high_strength')
        
        if 'unity_score' in feature and feature['unity_score'] > 0.8:
            validation_factors.append('high_unity_score')
        
        # Update validation result
        validation_result['is_valid'] = is_valid
        validation_result['validation_score'] = validation_score
        validation_result['validation_factors'] = validation_factors
        
        return validation_result
    
    def update_integration_metrics(self, processing_results):
        """
        Updates integration metrics.
        
        Args:
            processing_results: Processing results
        """
        # Update total numbers processed
        self.integration_metrics['total_numbers_processed'] += 1
        
        # Update phases detected
        self.integration_metrics['phases_detected'] += len(processing_results['phases'])
        
        # Update analyses triggered
        self.integration_metrics['analyses_triggered'] += len(processing_results['analyses_to_run'])
        
        # Update features discovered
        self.integration_metrics['features_discovered'] += len(processing_results['features_discovered'])
        
        # Update unity metrics
        if processing_results['unity_validation']['unity_maintained']:
            self.integration_metrics['unity_maintained_count'] += 1
        else:
            self.integration_metrics['unity_violations_count'] += 1
        
        # Update average unity score
        self.integration_metrics['average_unity_score'] = (
            (self.integration_metrics['average_unity_score'] * (self.integration_metrics['total_numbers_processed'] - 1) +
             processing_results['unity_validation']['overall_unity_score']) /
            self.integration_metrics['total_numbers_processed']
        )
        
        # Update average processing time
        self.integration_metrics['average_processing_time'] = (
            (self.integration_metrics['average_processing_time'] * (self.integration_metrics['total_numbers_processed'] - 1) +
             processing_results['processing_time']) /
            self.integration_metrics['total_numbers_processed']
        )
    
    def process_number_range(self, start, end):
        """
        Processes a range of numbers through the integrated system.
        
        Args:
            start: Start of range
            end: End of range
            
        Returns:
            Processing results for the range
        """
        # Reset integration metrics
        self.reset_integration_metrics()
        
        # Process each number in the range
        processing_results = []
        previous_mappings = []
        
        for n in range(start, end + 1):
            # Process number
            result = self.process_number(n, previous_mappings)
            processing_results.append(result)
            
            # Update previous mappings
            previous_mappings.append(result['dimensional_mapping'])
            if len(previous_mappings) > 10:
                previous_mappings.pop(0)
        
        # Calculate range statistics
        range_statistics = self.calculate_range_statistics(processing_results)
        
        return {
            'range': {'start': start, 'end': end},
            'integration_metrics': self.integration_metrics,
            'range_statistics': range_statistics
        }
    
    def reset_integration_metrics(self):
        """
        Resets integration metrics.
        """
        self.integration_metrics = {
            'total_numbers_processed': 0,
            'phases_detected': 0,
            'analyses_triggered': 0,
            'features_discovered': 0,
            'unity_maintained_count': 0,
            'unity_violations_count': 0,
            'average_unity_score': 0.0,
            'average_processing_time': 0.0
        }
        
        # Clear integration history
        self.integration_history = []
    
    def calculate_range_statistics(self, processing_results):
        """
        Calculates statistics for a range of processing results.
        
        Args:
            processing_results: List of processing results
            
        Returns:
            Range statistics
        """
        # Calculate unity maintenance rate
        unity_maintained_count = sum(1 for result in processing_results if result['unity_validation']['unity_maintained'])
        unity_maintenance_rate = unity_maintained_count / len(processing_results) if processing_results else 0
        
        # Calculate average unity score
        average_unity_score = sum(result['unity_validation']['overall_unity_score'] for result in processing_results) / len(processing_results) if processing_results else 0
        
        # Calculate feature discovery rate
        total_features = sum(len(result['features_discovered']) for result in processing_results)
        feature_discovery_rate = total_features / len(processing_results) if processing_results else 0
        
        # Calculate average processing time
        average_processing_time = sum(result['processing_time'] for result in processing_results) / len(processing_results) if processing_results else 0
        
        # Calculate phase statistics
        phase_counts = {}
        for result in processing_results:
            for phase in result['phases']:
                phase_type = phase['type']
                if phase_type not in phase_counts:
                    phase_counts[phase_type] = 0
                phase_counts[phase_type] += 1
        
        # Calculate feature type statistics
        feature_type_counts = {}
        for result in processing_results:
            for feature in result['features_discovered']:
                feature_type = feature['feature']['type']
                if feature_type not in feature_type_counts:
                    feature_type_counts[feature_type] = 0
                feature_type_counts[feature_type] += 1
        
        return {
            'unity_maintained_count': unity_maintained_count,
            'unity_maintenance_rate': unity_maintenance_rate,
            'average_unity_score': average_unity_score,
            'total_features': total_features,
            'feature_discovery_rate': feature_discovery_rate,
            'average_processing_time': average_processing_time,
            'phase_counts': phase_counts,
            'feature_type_counts': feature_type_counts
        }
    
    def save_processing_results(self, results, filename):
        """
        Saves processing results to a file.
        
        Args:
            results: Processing results
            filename: Name of the file
        """
        with open(filename, 'w') as f:
            json.dump(results, f, indent=2)

class UnifiedContextTester:
    """
    Tests and validates the Unified Context implementation.
    """
    
    def __init__(self, output_dir="./test_results"):
        """
        Initialize the unified context tester.
        
        Args:
            output_dir: Directory to save test results (default: ./test_results)
        """
        self.output_dir = output_dir
        
        # Create output directory if it doesn't exist
        os.makedirs(self.output_dir, exist_ok=True)
        
        # Initialize integrator
        self.integrator = UnifiedContextIntegrator()
        
        # Initialize test metrics
        self.test_metrics = {
            'total_tests_run': 0,
            'successful_tests': 0,
            'failed_tests': 0,
            'average_unity_maintenance_rate': 0.0,
            'average_feature_discovery_rate': 0.0,
            'average_processing_time': 0.0
        }
    
    def run_basic_tests(self):
        """
        Runs basic tests for the Unified Context implementation.
        
        Returns:
            Test results
        """
        print("Running basic tests...")
        
        # Test cases
        test_cases = [
            {'name': 'single_digit', 'start': 1, 'end': 9},
            {'name': 'first_dimension', 'start': 10, 'end': 19},
            {'name': 'second_dimension', 'start': 20, 'end': 29},
            {'name': 'prime_rich', 'start': 30, 'end': 50},
            {'name': 'dimensional_boundary', 'start': 168, 'end': 172}
        ]
        
        # Run tests
        test_results = []
        
        for test_case in test_cases:
            print(f"  Running test case: {test_case['name']} ({test_case['start']}-{test_case['end']})")
            
            # Process range
            start_time = time.time()
            range_results = self.integrator.process_number_range(test_case['start'], test_case['end'])
            processing_time = time.time() - start_time
            
            # Create test result
            test_result = {
                'test_case': test_case,
                'range_results': range_results,
                'processing_time': processing_time,
                'success': range_results['range_statistics']['unity_maintenance_rate'] > 0.8
            }
            
            # Add to test results
            test_results.append(test_result)
            
            # Update test metrics
            self.update_test_metrics(test_result)
            
            print(f"    Unity maintenance rate: {range_results['range_statistics']['unity_maintenance_rate']:.2f}")
            print(f"    Feature discovery rate: {range_results['range_statistics']['feature_discovery_rate']:.2f}")
            print(f"    Processing time: {processing_time:.4f} seconds")
            print(f"    Success: {test_result['success']}")
            
            print()
        
        # Save test results
        timestamp = int(time.time())
        filename = os.path.join(self.output_dir, f"basic_test_results_{timestamp}.json")
        self.save_test_results(test_results, filename)
        
        print(f"Basic test results saved to {filename}")
        
        # Generate visualizations
        self.generate_basic_visualizations(test_results, timestamp)
        
        return test_results
    
    def run_extended_tests(self, start=1, end=1000):
        """
        Runs extended tests for the Unified Context implementation.
        
        Args:
            start: Start of range (default: 1)
            end: End of range (default: 1000)
            
        Returns:
            Test results
        """
        print(f"Running extended tests for range {start}-{end}...")
        
        # Process range
        start_time = time.time()
        range_results = self.integrator.process_number_range(start, end)
        processing_time = time.time() - start_time
        
        # Create test result
        test_result = {
            'test_case': {'name': 'extended', 'start': start, 'end': end},
            'range_results': range_results,
            'processing_time': processing_time,
            'success': range_results['range_statistics']['unity_maintenance_rate'] > 0.8
        }
        
        # Update test metrics
        self.update_test_metrics(test_result)
        
        print(f"  Unity maintenance rate: {range_results['range_statistics']['unity_maintenance_rate']:.2f}")
        print(f"  Feature discovery rate: {range_results['range_statistics']['feature_discovery_rate']:.2f}")
        print(f"  Processing time: {processing_time:.4f} seconds")
        print(f"  Success: {test_result['success']}")
        
        # Save test results
        timestamp = int(time.time())
        filename = os.path.join(self.output_dir, f"extended_test_results_{timestamp}.json")
        self.save_test_results(test_result, filename)
        
        print(f"Extended test results saved to {filename}")
        
        # Generate visualizations
        self.generate_extended_visualizations(test_result, timestamp)
        
        return test_result
    
    def update_test_metrics(self, test_result):
        """
        Updates test metrics.
        
        Args:
            test_result: Test result
        """
        # Update total tests run
        self.test_metrics['total_tests_run'] += 1
        
        # Update successful/failed tests
        if test_result['success']:
            self.test_metrics['successful_tests'] += 1
        else:
            self.test_metrics['failed_tests'] += 1
        
        # Update average unity maintenance rate
        self.test_metrics['average_unity_maintenance_rate'] = (
            (self.test_metrics['average_unity_maintenance_rate'] * (self.test_metrics['total_tests_run'] - 1) +
             test_result['range_results']['range_statistics']['unity_maintenance_rate']) /
            self.test_metrics['total_tests_run']
        )
        
        # Update average feature discovery rate
        self.test_metrics['average_feature_discovery_rate'] = (
            (self.test_metrics['average_feature_discovery_rate'] * (self.test_metrics['total_tests_run'] - 1) +
             test_result['range_results']['range_statistics']['feature_discovery_rate']) /
            self.test_metrics['total_tests_run']
        )
        
        # Update average processing time
        self.test_metrics['average_processing_time'] = (
            (self.test_metrics['average_processing_time'] * (self.test_metrics['total_tests_run'] - 1) +
             test_result['processing_time']) /
            self.test_metrics['total_tests_run']
        )
    
    def save_test_results(self, test_results, filename):
        """
        Saves test results to a file.
        
        Args:
            test_results: Test results
            filename: Name of the file
        """
        with open(filename, 'w') as f:
            json.dump(test_results, f, indent=2)
    
    def generate_basic_visualizations(self, test_results, timestamp):
        """
        Generates visualizations for basic test results.
        
        Args:
            test_results: Test results
            timestamp: Timestamp for filenames
        """
        # Generate unity maintenance rate visualization
        self.generate_unity_maintenance_rate_visualization(test_results, timestamp)
        
        # Generate feature discovery rate visualization
        self.generate_feature_discovery_rate_visualization(test_results, timestamp)
        
        # Generate processing time visualization
        self.generate_processing_time_visualization(test_results, timestamp)
    
    def generate_unity_maintenance_rate_visualization(self, test_results, timestamp):
        """
        Generates unity maintenance rate visualization.
        
        Args:
            test_results: Test results
            timestamp: Timestamp for filename
        """
        # Extract data
        labels = [result['test_case']['name'] for result in test_results]
        values = [result['range_results']['range_statistics']['unity_maintenance_rate'] for result in test_results]
        
        # Create figure
        plt.figure(figsize=(10, 6))
        
        # Create bar chart
        plt.bar(labels, values, color='#4CAF50')
        
        # Add labels and title
        plt.xlabel('Test Case')
        plt.ylabel('Unity Maintenance Rate')
        plt.title('Unity Maintenance Rates Across Test Cases')
        
        # Add horizontal line at 0.8 (success threshold)
        plt.axhline(y=0.8, color='r', linestyle='-', label='Success Threshold')
        
        # Add legend
        plt.legend()
        
        # Save figure
        filename = os.path.join(self.output_dir, f"unity_maintenance_rate_{timestamp}.png")
        plt.savefig(filename)
        plt.close()
    
    def generate_feature_discovery_rate_visualization(self, test_results, timestamp):
        """
        Generates feature discovery rate visualization.
        
        Args:
            test_results: Test results
            timestamp: Timestamp for filename
        """
        # Extract data
        labels = [result['test_case']['name'] for result in test_results]
        values = [result['range_results']['range_statistics']['feature_discovery_rate'] for result in test_results]
        
        # Create figure
        plt.figure(figsize=(10, 6))
        
        # Create bar chart
        plt.bar(labels, values, color='#FF9800')
        
        # Add labels and title
        plt.xlabel('Test Case')
        plt.ylabel('Feature Discovery Rate')
        plt.title('Feature Discovery Rates Across Test Cases')
        
        # Save figure
        filename = os.path.join(self.output_dir, f"feature_discovery_rate_{timestamp}.png")
        plt.savefig(filename)
        plt.close()
    
    def generate_processing_time_visualization(self, test_results, timestamp):
        """
        Generates processing time visualization.
        
        Args:
            test_results: Test results
            timestamp: Timestamp for filename
        """
        # Extract data
        labels = [result['test_case']['name'] for result in test_results]
        values = [result['processing_time'] for result in test_results]
        
        # Create figure
        plt.figure(figsize=(10, 6))
        
        # Create bar chart
        plt.bar(labels, values, color='#2196F3')
        
        # Add labels and title
        plt.xlabel('Test Case')
        plt.ylabel('Processing Time (seconds)')
        plt.title('Processing Times Across Test Cases')
        
        # Save figure
        filename = os.path.join(self.output_dir, f"processing_time_{timestamp}.png")
        plt.savefig(filename)
        plt.close()
    
    def generate_extended_visualizations(self, test_result, timestamp):
        """
        Generates visualizations for extended test results.
        
        Args:
            test_result: Test result
            timestamp: Timestamp for filenames
        """
        # Generate unity maintenance visualization
        self.generate_unity_maintenance_visualization(test_result, timestamp)
        
        # Generate feature type distribution visualization
        self.generate_feature_type_distribution_visualization(test_result, timestamp)
        
        # Generate phase distribution visualization
        self.generate_phase_distribution_visualization(test_result, timestamp)
    
    def generate_unity_maintenance_visualization(self, test_result, timestamp):
        """
        Generates unity maintenance visualization.
        
        Args:
            test_result: Test result
            timestamp: Timestamp for filename
        """
        # Extract data
        range_statistics = test_result['range_results']['range_statistics']
        
        # Create figure
        plt.figure(figsize=(10, 6))
        
        # Create bar chart
        labels = ['Unity Maintained', 'Unity Violations']
        values = [range_statistics['unity_maintained_count'], test_result['range_results']['range']['end'] - test_result['range_results']['range']['start'] + 1 - range_statistics['unity_maintained_count']]
        colors = ['#4CAF50', '#F44336']
        
        plt.bar(labels, values, color=colors)
        
        # Add labels and title
        plt.xlabel('Unity Status')
        plt.ylabel('Count')
        plt.title('Unity Maintenance Distribution')
        
        # Add text with unity maintenance rate
        plt.text(0.5, 0.9, f"Unity Maintenance Rate: {range_statistics['unity_maintenance_rate']:.2f}", 
                 horizontalalignment='center', verticalalignment='center', transform=plt.gca().transAxes)
        
        # Save figure
        filename = os.path.join(self.output_dir, f"unity_maintenance_{timestamp}.png")
        plt.savefig(filename)
        plt.close()
    
    def generate_feature_type_distribution_visualization(self, test_result, timestamp):
        """
        Generates feature type distribution visualization.
        
        Args:
            test_result: Test result
            timestamp: Timestamp for filename
        """
        # Extract data
        range_statistics = test_result['range_results']['range_statistics']
        feature_type_counts = range_statistics.get('feature_type_counts', {})
        
        # Check if feature type counts exist
        if not feature_type_counts:
            return
        
        # Create figure
        plt.figure(figsize=(10, 6))
        
        # Create pie chart
        labels = list(feature_type_counts.keys())
        values = list(feature_type_counts.values())
        
        plt.pie(values, labels=labels, autopct='%1.1f%%', startangle=90)
        
        # Add title
        plt.title('Feature Type Distribution')
        
        # Equal aspect ratio ensures that pie is drawn as a circle
        plt.axis('equal')
        
        # Save figure
        filename = os.path.join(self.output_dir, f"feature_type_distribution_{timestamp}.png")
        plt.savefig(filename)
        plt.close()
    
    def generate_phase_distribution_visualization(self, test_result, timestamp):
        """
        Generates phase distribution visualization.
        
        Args:
            test_result: Test result
            timestamp: Timestamp for filename
        """
        # Extract data
        range_statistics = test_result['range_results']['range_statistics']
        phase_counts = range_statistics.get('phase_counts', {})
        
        # Check if phase counts exist
        if not phase_counts:
            return
        
        # Create figure
        plt.figure(figsize=(12, 6))
        
        # Create bar chart
        labels = list(phase_counts.keys())
        values = list(phase_counts.values())
        
        plt.bar(labels, values)
        
        # Add labels and title
        plt.xlabel('Phase Type')
        plt.ylabel('Count')
        plt.title('Phase Distribution')
        
        # Rotate x-axis labels
        plt.xticks(rotation=45, ha='right')
        
        # Adjust layout
        plt.tight_layout()
        
        # Save figure
        filename = os.path.join(self.output_dir, f"phase_distribution_{timestamp}.png")
        plt.savefig(filename)
        plt.close()

def main():
    """
    Main function.
    """
    # Create tester
    tester = UnifiedContextTester()
    
    # Run basic tests
    basic_test_results = tester.run_basic_tests()
    
    # Run extended tests
    extended_test_result = tester.run_extended_tests(start=1, end=100)
    
    print("\nTest Summary:")
    print(f"Total Tests Run: {tester.test_metrics['total_tests_run']}")
    print(f"Successful Tests: {tester.test_metrics['successful_tests']}")
    print(f"Failed Tests: {tester.test_metrics['failed_tests']}")
    print(f"Average Unity Maintenance Rate: {tester.test_metrics['average_unity_maintenance_rate']:.2f}")
    print(f"Average Feature Discovery Rate: {tester.test_metrics['average_feature_discovery_rate']:.2f}")
    print(f"Average Processing Time: {tester.test_metrics['average_processing_time']:.4f} seconds")

if __name__ == "__main__":
    main()
