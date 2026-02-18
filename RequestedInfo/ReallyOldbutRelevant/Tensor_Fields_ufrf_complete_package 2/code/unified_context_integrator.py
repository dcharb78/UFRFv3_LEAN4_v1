"""
Unified Context Integration for UFRF Framework

This module integrates the Unified Context components with the Real-Time Discovery System
to ensure the "Always One in Context" principle is maintained during exploration.

Author: Daniel Charboneau
License: Creative Commons Attribution-NonCommercial 4.0 International
"""

import os
import sys
import json
import time
import numpy as np
from datetime import datetime

# Use relative imports for modules in the same package
from .contextual_unity_detector import ContextualUnityDetector
from .enhanced_dimensional_mapper import EnhancedDimensionalMapper
from .cross_scale_context_analyzer import CrossScaleContextAnalyzer
from .resonance_pattern_recognizer import ResonancePatternRecognizer
from .contextual_unity_validator import ContextualUnityValidator

# Import real_time_discovery modules
# These imports need to be adjusted based on the actual location of these modules
# For now, we'll use a try-except block to handle potential import errors
try:
    # Try relative import first (if real_time_discovery is a sibling package)
    from ..real_time_discovery.phase_detection import PhaseDetector
    from ..real_time_discovery.analysis_trigger_system import AnalysisTriggerSystem
    from ..real_time_discovery.feature_integration_system import FeatureIntegrationSystem
except ImportError:
    # If that fails, try absolute import (assuming the package is installed or in PYTHONPATH)
    try:
        from real_time_discovery.phase_detection import PhaseDetector
        from real_time_discovery.analysis_trigger_system import AnalysisTriggerSystem
        from real_time_discovery.feature_integration_system import FeatureIntegrationSystem
    except ImportError:
        # If both fail, provide placeholder classes for testing
        class PhaseDetector:
            def detect_phases(self, n, dimensional_mapping, previous_mappings=None):
                return [{'type': 'placeholder', 'subtype': 'placeholder'}]
                
        class AnalysisTriggerSystem:
            def determine_analyses(self, phases):
                return []
                
        class FeatureIntegrationSystem:
            def integrate_feature(self, feature):
                return {'success': True}

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
        
        # Initialize Real-Time Discovery components
        self.phase_detector = PhaseDetector()
        self.analysis_trigger = AnalysisTriggerSystem()
        self.feature_integrator = FeatureIntegrationSystem()
        
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
        
        # Check for system completion patterns
        if any(phase['type'] == 'system_completion' for phase in phases):
            # Get system completion phase
            system_phase = [phase for phase in phases if phase['type'] == 'system_completion'][0]
            
            # Create feature for system completion
            feature = {
                'type': 'pattern',
                'subtype': 'system_completion',
                'number': n,
                'dimensional_mapping': dimensional_mapping,
                'system_type': system_phase['subtype'],
                'description': f"System completion pattern ({system_phase['subtype']}) at number {n}",
                'unity_maintained': unity_validation['unity_maintained'],
                'discovery_phase': system_phase
            }
            
            features.append(feature)
        
        # Check for level completion patterns
        if any(phase['type'] == 'level_completion' for phase in phases):
            # Get level completion phase
            level_phase = [phase for phase in phases if phase['type'] == 'level_completion'][0]
            
            # Create feature for level completion
            feature = {
                'type': 'pattern',
                'subtype': 'level_completion',
                'number': n,
                'dimensional_mapping': dimensional_mapping,
                'level_type': level_phase['subtype'],
                'description': f"Level completion pattern ({level_phase['subtype']}) at number {n}",
                'unity_maintained': unity_validation['unity_maintained'],
                'discovery_phase': level_phase
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
            Discovered meta-features
        """
        features = []
        
        # Check for feature integration phases
        if any(phase['type'] == 'feature_integration' for phase in phases):
            # Get feature integration phase
            integration_phase = [phase for phase in phases if phase['type'] == 'feature_integration'][0]
            
            # Create meta-feature for feature integration
            feature = {
                'type': 'feature',
                'subtype': 'integration',
                'number': n,
                'dimensional_mapping': dimensional_mapping,
                'integration_type': integration_phase['subtype'],
                'description': f"Feature integration ({integration_phase['subtype']}) at number {n}",
                'unity_maintained': unity_validation['unity_maintained'],
                'discovery_phase': integration_phase
            }
            
            features.append(feature)
        
        # Check for feature emergence phases
        if any(phase['type'] == 'feature_emergence' for phase in phases):
            # Get feature emergence phase
            emergence_phase = [phase for phase in phases if phase['type'] == 'feature_emergence'][0]
            
            # Create meta-feature for feature emergence
            feature = {
                'type': 'feature',
                'subtype': 'emergence',
                'number': n,
                'dimensional_mapping': dimensional_mapping,
                'emergence_type': emergence_phase['subtype'],
                'description': f"Feature emergence ({emergence_phase['subtype']}) at number {n}",
                'unity_maintained': unity_validation['unity_maintained'],
                'discovery_phase': emergence_phase
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
        
        # Check if unity is maintained
        if unity_validation['unity_maintained']:
            validation_result['validation_factors'].append('unity_maintained')
            validation_result['validation_score'] += 0.5
        
        # Check feature type-specific validation
        if feature['type'] == 'geometry':
            # Validate geometry feature
            if feature['subtype'] == 'cross_scale_coherence' and feature['coherence'] > 0.8:
                validation_result['validation_factors'].append('high_coherence')
                validation_result['validation_score'] += 0.3
            
            if feature['subtype'] == 'dimensional_boundary':
                validation_result['validation_factors'].append('dimensional_boundary')
                validation_result['validation_score'] += 0.2
            
            if feature['subtype'] == 'position':
                validation_result['validation_factors'].append('position_feature')
                validation_result['validation_score'] += 0.1
        
        elif feature['type'] == 'resonance':
            # Validate resonance feature
            if feature['subtype'] == 'overall' and feature['strength'] > 0.7:
                validation_result['validation_factors'].append('strong_overall_resonance')
                validation_result['validation_score'] += 0.3
            
            if feature['subtype'] in ['intra_scale', 'cross_scale', 'harmonic'] and feature['strength'] > 0.7:
                validation_result['validation_factors'].append(f"strong_{feature['subtype']}_resonance")
                validation_result['validation_score'] += 0.2
        
        elif feature['type'] == 'pattern':
            # Validate pattern feature
            if feature['subtype'] == 'cycle_completion':
                validation_result['validation_factors'].append('cycle_completion')
                validation_result['validation_score'] += 0.3
            
            if feature['subtype'] == 'system_completion':
                validation_result['validation_factors'].append('system_completion')
                validation_result['validation_score'] += 0.3
            
            if feature['subtype'] == 'level_completion':
                validation_result['validation_factors'].append('level_completion')
                validation_result['validation_score'] += 0.2
        
        elif feature['type'] == 'feature':
            # Validate meta-feature
            if feature['subtype'] == 'integration':
                validation_result['validation_factors'].append('feature_integration')
                validation_result['validation_score'] += 0.3
            
            if feature['subtype'] == 'emergence':
                validation_result['validation_factors'].append('feature_emergence')
                validation_result['validation_score'] += 0.4
        
        # Determine if feature is valid
        validation_result['is_valid'] = validation_result['validation_score'] >= 0.6
        
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
        total_score = self.integration_metrics['average_unity_score'] * (self.integration_metrics['total_numbers_processed'] - 1)
        total_score += processing_results['unity_validation']['overall_unity_score']
        self.integration_metrics['average_unity_score'] = total_score / self.integration_metrics['total_numbers_processed']
        
        # Update average processing time
        total_time = self.integration_metrics['average_processing_time'] * (self.integration_metrics['total_numbers_processed'] - 1)
        total_time += processing_results['processing_time']
        self.integration_metrics['average_processing_time'] = total_time / self.integration_metrics['total_numbers_processed']
    
    def get_integration_metrics(self):
        """
        Gets the current integration metrics.
        
        Returns:
            Integration metrics
        """
        return self.integration_metrics
    
    def get_integration_history(self):
        """
        Gets the integration history.
        
        Returns:
            Integration history
        """
        return self.integration_history
    
    def save_integration_metrics(self, filename):
        """
        Saves integration metrics to a file.
        
        Args:
            filename: Name of the file to save to
        """
        with open(filename, 'w') as f:
            json.dump(self.integration_metrics, f, indent=4)
    
    def save_integration_history(self, filename):
        """
        Saves integration history to a file.
        
        Args:
            filename: Name of the file to save to
        """
        # Convert integration history to a simpler format for saving
        simplified_history = []
        for result in self.integration_history:
            simplified = {
                'number': result['number'],
                'unity_maintained': result['unity_validation']['unity_maintained'],
                'overall_unity_score': result['unity_validation']['overall_unity_score'],
                'phases_detected': len(result['phases']),
                'analyses_run': len(result['analyses_to_run']),
                'features_discovered': len(result['features_discovered']),
                'processing_time': result['processing_time']
            }
            simplified_history.append(simplified)
            
        with open(filename, 'w') as f:
            json.dump(simplified_history, f, indent=4)


# Test function
def test_unified_context_integrator():
    """
    Tests the UnifiedContextIntegrator class.
    """
    integrator = UnifiedContextIntegrator()
    
    # Test for a few numbers
    test_cases = [1, 13, 14, 170]
    
    for n in test_cases:
        # Process number
        result = integrator.process_number(n)
        print(f"Number {n}:")
        print(f"  Unity maintained: {result['unity_validation']['unity_maintained']}")
        print(f"  Overall unity score: {result['unity_validation']['overall_unity_score']}")
        print(f"  Phases detected: {len(result['phases'])}")
        print(f"  Analyses run: {len(result['analyses_to_run'])}")
        print(f"  Features discovered: {len(result['features_discovered'])}")
        print(f"  Processing time: {result['processing_time']:.6f} seconds")
        print()
    
    # Print integration metrics
    metrics = integrator.get_integration_metrics()
    print("Integration metrics:")
    print(f"  Total numbers processed: {metrics['total_numbers_processed']}")
    print(f"  Phases detected: {metrics['phases_detected']}")
    print(f"  Analyses triggered: {metrics['analyses_triggered']}")
    print(f"  Features discovered: {metrics['features_discovered']}")
    print(f"  Unity maintained count: {metrics['unity_maintained_count']}")
    print(f"  Unity violations count: {metrics['unity_violations_count']}")
    print(f"  Average unity score: {metrics['average_unity_score']}")
    print(f"  Average processing time: {metrics['average_processing_time']:.6f} seconds")


if __name__ == "__main__":
    test_unified_context_integrator()
