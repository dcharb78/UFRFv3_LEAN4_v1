"""
Unity Validation Framework for UFRF Framework

This module implements a comprehensive validation framework to verify that
the enhanced unity maintenance system achieves the target unity maintenance rate.

Author: Daniel Charboneau
License: Creative Commons Attribution-NonCommercial 4.0 International
"""

import numpy as np
import time
import json
import os
import matplotlib.pyplot as plt
from datetime import datetime
from collections import defaultdict

from .harmonic_unity_function import HarmonicUnityFunction, HarmonicDimensionalMapper
from .cross_scale_coherence_optimizer import CrossScaleCoherenceOptimizer

class UnityValidationFramework:
    """
    Implements a comprehensive validation framework to verify that the enhanced
    unity maintenance system achieves the target unity maintenance rate.
    """
    
    def __init__(self, dimensional_base=13):
        """
        Initialize the unity validation framework.
        
        Args:
            dimensional_base: Base for dimensional calculations (default: 13)
        """
        self.dimensional_base = dimensional_base
        self.unity_function = HarmonicUnityFunction(dimensional_base)
        self.mapper = HarmonicDimensionalMapper(dimensional_base)
        self.optimizer = CrossScaleCoherenceOptimizer(dimensional_base)
        
        # Define validation thresholds
        self.thresholds = {
            'unity_maintenance': 0.8,  # Target unity maintenance rate
            'prime_unity_maintenance': 0.9,  # Target unity maintenance rate for primes
            'cross_scale_coherence': 0.95,  # Target cross-scale coherence
            'performance_factor': 1.5  # Maximum allowed performance degradation
        }
        
        # Initialize validation results
        self.validation_results = {}
        
        # Define test ranges
        self.test_ranges = [
            (1, 13),    # First boundary
            (14, 26),   # Second boundary
            (27, 39),   # Third boundary
            (40, 52),   # Fourth boundary
            (1, 52),    # First four boundaries combined
            (53, 169),  # Higher range
            (170, 500)  # Extended range
        ]
        
        # Define special number sets
        self.special_number_sets = {
            'primes': self._generate_primes(500),
            'fibonacci': self._generate_fibonacci(500),
            'boundary_positions': self._generate_boundary_positions(500)
        }
    
    def _generate_primes(self, limit):
        """
        Generate prime numbers up to a limit.
        
        Args:
            limit: Upper limit
            
        Returns:
            List of prime numbers
        """
        primes = []
        for n in range(2, limit + 1):
            if self.unity_function.is_prime(n):
                primes.append(n)
        return primes
    
    def _generate_fibonacci(self, limit):
        """
        Generate Fibonacci numbers up to a limit.
        
        Args:
            limit: Upper limit
            
        Returns:
            List of Fibonacci numbers
        """
        fibonacci = [1, 1]
        while fibonacci[-1] + fibonacci[-2] <= limit:
            fibonacci.append(fibonacci[-1] + fibonacci[-2])
        return fibonacci
    
    def _generate_boundary_positions(self, limit):
        """
        Generate boundary positions up to a limit.
        
        Args:
            limit: Upper limit
            
        Returns:
            List of boundary positions
        """
        positions = []
        for n in range(1, limit + 1):
            position = ((n - 1) % self.dimensional_base) + 1
            if position == 1 or position == self.dimensional_base:
                positions.append(n)
        return positions
    
    def validate_unity_maintenance(self):
        """
        Validate that the enhanced unity maintenance system achieves the target rate.
        
        Returns:
            Dictionary with validation results
        """
        # Initialize results
        results = {
            'ranges': {},
            'special_sets': {},
            'overall': {
                'total_numbers': 0,
                'unity_maintained': 0,
                'unity_maintenance_rate': 0.0,
                'threshold_achieved': False
            }
        }
        
        # Validate each test range
        total_numbers = 0
        total_unity_maintained = 0
        
        for start, end in self.test_ranges:
            range_result = self.validate_range(start, end)
            results['ranges'][f"{start}-{end}"] = range_result
            
            total_numbers += range_result['total_count']
            total_unity_maintained += range_result['unity_maintained']
        
        # Validate special number sets
        for set_name, numbers in self.special_number_sets.items():
            set_result = self.validate_number_set(numbers, set_name)
            results['special_sets'][set_name] = set_result
        
        # Calculate overall results
        if total_numbers > 0:
            overall_rate = total_unity_maintained / total_numbers
            threshold_achieved = overall_rate >= self.thresholds['unity_maintenance']
            
            results['overall'] = {
                'total_numbers': total_numbers,
                'unity_maintained': total_unity_maintained,
                'unity_maintenance_rate': overall_rate,
                'threshold_achieved': threshold_achieved
            }
        
        # Store validation results
        self.validation_results['unity_maintenance'] = results
        
        return results
    
    def validate_range(self, start, end):
        """
        Validate unity maintenance for a range of numbers.
        
        Args:
            start: Start of range
            end: End of range
            
        Returns:
            Dictionary with validation results
        """
        # Optimize range
        optimization_result = self.optimizer.optimize_range(start, end)
        
        # Extract key metrics
        unity_maintained = optimization_result['optimized_unity_maintained']
        total_count = optimization_result['total_count']
        unity_rate = optimization_result['optimized_unity_rate']
        
        # Check if threshold is achieved
        threshold_achieved = unity_rate >= self.thresholds['unity_maintenance']
        
        # Calculate detailed metrics
        position_stats = self.calculate_position_stats(start, end)
        
        return {
            'start': start,
            'end': end,
            'unity_maintained': unity_maintained,
            'total_count': total_count,
            'unity_maintenance_rate': unity_rate,
            'threshold_achieved': threshold_achieved,
            'position_stats': position_stats
        }
    
    def validate_number_set(self, numbers, set_name):
        """
        Validate unity maintenance for a set of numbers.
        
        Args:
            numbers: List of numbers
            set_name: Name of the set
            
        Returns:
            Dictionary with validation results
        """
        # Initialize counters
        unity_maintained = 0
        total_count = len(numbers)
        
        # Check each number
        for n in numbers:
            # Optimize coherence
            result = self.optimizer.optimize_cross_scale_coherence(n)
            
            # Check if unity is maintained
            if result['optimized_unity'] >= self.thresholds['unity_maintenance']:
                unity_maintained += 1
        
        # Calculate unity rate
        unity_rate = unity_maintained / total_count if total_count > 0 else 0.0
        
        # Determine threshold
        if set_name == 'primes':
            threshold = self.thresholds['prime_unity_maintenance']
        else:
            threshold = self.thresholds['unity_maintenance']
        
        # Check if threshold is achieved
        threshold_achieved = unity_rate >= threshold
        
        return {
            'set_name': set_name,
            'unity_maintained': unity_maintained,
            'total_count': total_count,
            'unity_maintenance_rate': unity_rate,
            'threshold': threshold,
            'threshold_achieved': threshold_achieved
        }
    
    def calculate_position_stats(self, start, end):
        """
        Calculate statistics for different cycle positions.
        
        Args:
            start: Start of range
            end: End of range
            
        Returns:
            Dictionary with position statistics
        """
        # Initialize position stats
        position_stats = {pos: {'count': 0, 'unity_maintained': 0, 'rate': 0.0}
                         for pos in range(1, self.dimensional_base + 1)}
        
        # Process each number
        for n in range(start, end + 1):
            # Calculate position
            position = ((n - 1) % self.dimensional_base) + 1
            
            # Optimize coherence
            result = self.optimizer.optimize_cross_scale_coherence(n)
            
            # Update stats
            position_stats[position]['count'] += 1
            if result['optimized_unity'] >= self.thresholds['unity_maintenance']:
                position_stats[position]['unity_maintained'] += 1
        
        # Calculate rates
        for pos, stats in position_stats.items():
            if stats['count'] > 0:
                stats['rate'] = stats['unity_maintained'] / stats['count']
        
        return position_stats
    
    def validate_cross_scale_coherence(self):
        """
        Validate cross-scale coherence.
        
        Returns:
            Dictionary with validation results
        """
        # Initialize results
        results = {
            'ranges': {},
            'overall': {
                'total_numbers': 0,
                'coherent_numbers': 0,
                'coherence_rate': 0.0,
                'threshold_achieved': False
            }
        }
        
        # Validate each test range
        total_numbers = 0
        total_coherent = 0
        
        for start, end in self.test_ranges:
            range_result = self.validate_coherence_range(start, end)
            results['ranges'][f"{start}-{end}"] = range_result
            
            total_numbers += range_result['total_count']
            total_coherent += range_result['coherent_count']
        
        # Calculate overall results
        if total_numbers > 0:
            overall_rate = total_coherent / total_numbers
            threshold_achieved = overall_rate >= self.thresholds['cross_scale_coherence']
            
            results['overall'] = {
                'total_numbers': total_numbers,
                'coherent_numbers': total_coherent,
                'coherence_rate': overall_rate,
                'threshold_achieved': threshold_achieved
            }
        
        # Store validation results
        self.validation_results['cross_scale_coherence'] = results
        
        return results
    
    def validate_coherence_range(self, start, end):
        """
        Validate cross-scale coherence for a range of numbers.
        
        Args:
            start: Start of range
            end: End of range
            
        Returns:
            Dictionary with validation results
        """
        # Initialize counters
        coherent_count = 0
        total_count = end - start + 1
        
        # Check each number
        for n in range(start, end + 1):
            # Optimize coherence
            result = self.optimizer.optimize_cross_scale_coherence(n)
            
            # Check if coherence is sufficient
            if result['overall_coherence'] >= self.thresholds['cross_scale_coherence']:
                coherent_count += 1
        
        # Calculate coherence rate
        coherence_rate = coherent_count / total_count if total_count > 0 else 0.0
        
        # Check if threshold is achieved
        threshold_achieved = coherence_rate >= self.thresholds['cross_scale_coherence']
        
        return {
            'start': start,
            'end': end,
            'coherent_count': coherent_count,
            'total_count': total_count,
            'coherence_rate': coherence_rate,
            'threshold_achieved': threshold_achieved
        }
    
    def validate_performance(self):
        """
        Validate performance of the enhanced system.
        
        Returns:
            Dictionary with validation results
        """
        # Initialize results
        results = {
            'ranges': {},
            'overall': {
                'original_time': 0.0,
                'enhanced_time': 0.0,
                'performance_ratio': 0.0,
                'threshold_achieved': False
            }
        }
        
        # Validate each test range
        total_original_time = 0.0
        total_enhanced_time = 0.0
        
        for start, end in self.test_ranges[:3]:  # Use only first three ranges for performance testing
            range_result = self.validate_performance_range(start, end)
            results['ranges'][f"{start}-{end}"] = range_result
            
            total_original_time += range_result['original_time']
            total_enhanced_time += range_result['enhanced_time']
        
        # Calculate overall results
        if total_original_time > 0:
            performance_ratio = total_enhanced_time / total_original_time
            threshold_achieved = performance_ratio <= self.thresholds['performance_factor']
            
            results['overall'] = {
                'original_time': total_original_time,
                'enhanced_time': total_enhanced_time,
                'performance_ratio': performance_ratio,
                'threshold_achieved': threshold_achieved
            }
        
        # Store validation results
        self.validation_results['performance'] = results
        
        return results
    
    def validate_performance_range(self, start, end):
        """
        Validate performance for a range of numbers.
        
        Args:
            start: Start of range
            end: End of range
            
        Returns:
            Dictionary with validation results
        """
        # Measure time for original implementation
        original_start_time = time.time()
        
        for n in range(start, end + 1):
            # Map with unity using original implementation
            self.mapper.map_with_unity(n)
        
        original_time = time.time() - original_start_time
        
        # Measure time for enhanced implementation
        enhanced_start_time = time.time()
        
        for n in range(start, end + 1):
            # Optimize coherence using enhanced implementation
            self.optimizer.optimize_cross_scale_coherence(n)
        
        enhanced_time = time.time() - enhanced_start_time
        
        # Calculate performance ratio
        performance_ratio = enhanced_time / original_time if original_time > 0 else float('inf')
        
        # Check if threshold is achieved
        threshold_achieved = performance_ratio <= self.thresholds['performance_factor']
        
        return {
            'start': start,
            'end': end,
            'original_time': original_time,
            'enhanced_time': enhanced_time,
            'performance_ratio': performance_ratio,
            'threshold_achieved': threshold_achieved
        }
    
    def run_comprehensive_validation(self):
        """
        Run comprehensive validation of the enhanced unity maintenance system.
        
        Returns:
            Dictionary with all validation results
        """
        # Validate unity maintenance
        unity_results = self.validate_unity_maintenance()
        
        # Validate cross-scale coherence
        coherence_results = self.validate_cross_scale_coherence()
        
        # Validate performance
        performance_results = self.validate_performance()
        
        # Combine results
        comprehensive_results = {
            'unity_maintenance': unity_results,
            'cross_scale_coherence': coherence_results,
            'performance': performance_results,
            'overall_success': (
                unity_results['overall']['threshold_achieved'] and
                coherence_results['overall']['threshold_achieved'] and
                performance_results['overall']['threshold_achieved']
            ),
            'timestamp': datetime.now().timestamp()
        }
        
        # Store comprehensive results
        self.validation_results['comprehensive'] = comprehensive_results
        
        return comprehensive_results
    
    def generate_validation_report(self, output_dir='test_results'):
        """
        Generate a validation report with visualizations.
        
        Args:
            output_dir: Directory to save report files
            
        Returns:
            Dictionary with report file paths
        """
        # Ensure output directory exists
        os.makedirs(output_dir, exist_ok=True)
        
        # Run comprehensive validation if not already done
        if 'comprehensive' not in self.validation_results:
            self.run_comprehensive_validation()
        
        # Get timestamp for file names
        timestamp = int(self.validation_results['comprehensive']['timestamp'])
        
        # Save results to JSON
        results_file = os.path.join(output_dir, f'validation_results_{timestamp}.json')
        with open(results_file, 'w') as f:
            json.dump(self.validation_results, f, indent=2)
        
        # Generate visualizations
        visualization_files = self.generate_visualizations(output_dir, timestamp)
        
        # Create report summary
        report = {
            'results_file': results_file,
            'visualization_files': visualization_files,
            'summary': self.create_report_summary(),
            'timestamp': timestamp
        }
        
        return report
    
    def generate_visualizations(self, output_dir, timestamp):
        """
        Generate visualizations of validation results.
        
        Args:
            output_dir: Directory to save visualization files
            timestamp: Timestamp for file names
            
        Returns:
            Dictionary with visualization file paths
        """
        visualization_files = {}
        
        # Generate unity maintenance visualization
        unity_file = os.path.join(output_dir, f'unity_maintenance_{timestamp}.png')
        self.visualize_unity_maintenance(unity_file)
        visualization_files['unity_maintenance'] = unity_file
        
        # Generate coherence visualization
        coherence_file = os.path.join(output_dir, f'cross_scale_coherence_{timestamp}.png')
        self.visualize_cross_scale_coherence(coherence_file)
        visualization_files['cross_scale_coherence'] = coherence_file
        
        # Generate performance visualization
        performance_file = os.path.join(output_dir, f'performance_{timestamp}.png')
        self.visualize_performance(performance_file)
        visualization_files['performance'] = performance_file
        
        # Generate position stats visualization
        position_file = os.path.join(output_dir, f'position_stats_{timestamp}.png')
        self.visualize_position_stats(position_file)
        visualization_files['position_stats'] = position_file
        
        return visualization_files
    
    def visualize_unity_maintenance(self, output_file):
        """
        Visualize unity maintenance results.
        
        Args:
            output_file: File to save visualization
        """
        # Get unity maintenance results
        results = self.validation_results['unity_maintenance']
        
        # Extract range data
        ranges = []
        rates = []
        threshold = self.thresholds['unity_maintenance']
        
        for range_key, range_result in results['ranges'].items():
            ranges.append(range_key)
            rates.append(range_result['unity_maintenance_rate'])
        
        # Create figure
        plt.figure(figsize=(10, 6))
        
        # Create bar chart
        bars = plt.bar(ranges, rates, color='skyblue')
        
        # Add threshold line
        plt.axhline(y=threshold, color='red', linestyle='--', label=f'Threshold ({threshold})')
        
        # Add labels and title
        plt.xlabel('Number Range')
        plt.ylabel('Unity Maintenance Rate')
        plt.title('Unity Maintenance Rate by Number Range')
        
        # Add data labels
        for bar in bars:
            height = bar.get_height()
            plt.text(bar.get_x() + bar.get_width()/2., height,
                    f'{height:.2f}', ha='center', va='bottom')
        
        # Add legend
        plt.legend()
        
        # Adjust layout
        plt.tight_layout()
        
        # Save figure
        plt.savefig(output_file)
        plt.close()
    
    def visualize_cross_scale_coherence(self, output_file):
        """
        Visualize cross-scale coherence results.
        
        Args:
            output_file: File to save visualization
        """
        # Get coherence results
        results = self.validation_results['cross_scale_coherence']
        
        # Extract range data
        ranges = []
        rates = []
        threshold = self.thresholds['cross_scale_coherence']
        
        for range_key, range_result in results['ranges'].items():
            ranges.append(range_key)
            rates.append(range_result['coherence_rate'])
        
        # Create figure
        plt.figure(figsize=(10, 6))
        
        # Create bar chart
        bars = plt.bar(ranges, rates, color='lightgreen')
        
        # Add threshold line
        plt.axhline(y=threshold, color='red', linestyle='--', label=f'Threshold ({threshold})')
        
        # Add labels and title
        plt.xlabel('Number Range')
        plt.ylabel('Coherence Rate')
        plt.title('Cross-Scale Coherence Rate by Number Range')
        
        # Add data labels
        for bar in bars:
            height = bar.get_height()
            plt.text(bar.get_x() + bar.get_width()/2., height,
                    f'{height:.2f}', ha='center', va='bottom')
        
        # Add legend
        plt.legend()
        
        # Adjust layout
        plt.tight_layout()
        
        # Save figure
        plt.savefig(output_file)
        plt.close()
    
    def visualize_performance(self, output_file):
        """
        Visualize performance results.
        
        Args:
            output_file: File to save visualization
        """
        # Get performance results
        results = self.validation_results['performance']
        
        # Extract range data
        ranges = []
        original_times = []
        enhanced_times = []
        threshold_factor = self.thresholds['performance_factor']
        
        for range_key, range_result in results['ranges'].items():
            ranges.append(range_key)
            original_times.append(range_result['original_time'])
            enhanced_times.append(range_result['enhanced_time'])
        
        # Create figure
        plt.figure(figsize=(10, 6))
        
        # Set bar width
        bar_width = 0.35
        
        # Set positions
        r1 = np.arange(len(ranges))
        r2 = [x + bar_width for x in r1]
        
        # Create bar chart
        plt.bar(r1, original_times, color='lightblue', width=bar_width, label='Original Implementation')
        plt.bar(r2, enhanced_times, color='coral', width=bar_width, label='Enhanced Implementation')
        
        # Add threshold line for enhanced times
        for i, orig_time in enumerate(original_times):
            plt.axhline(y=orig_time * threshold_factor, xmin=(i/len(ranges)), xmax=((i+1)/len(ranges)),
                       color='red', linestyle='--')
        
        # Add labels and title
        plt.xlabel('Number Range')
        plt.ylabel('Processing Time (seconds)')
        plt.title('Performance Comparison')
        plt.xticks([r + bar_width/2 for r in range(len(ranges))], ranges)
        
        # Add legend
        plt.legend()
        
        # Adjust layout
        plt.tight_layout()
        
        # Save figure
        plt.savefig(output_file)
        plt.close()
    
    def visualize_position_stats(self, output_file):
        """
        Visualize position statistics.
        
        Args:
            output_file: File to save visualization
        """
        # Get unity maintenance results for the first four boundaries combined
        range_key = "1-52"
        if range_key in self.validation_results['unity_maintenance']['ranges']:
            range_result = self.validation_results['unity_maintenance']['ranges'][range_key]
            position_stats = range_result['position_stats']
            
            # Extract position data
            positions = list(range(1, self.dimensional_base + 1))
            rates = [position_stats[pos]['rate'] for pos in positions]
            threshold = self.thresholds['unity_maintenance']
            
            # Create figure
            plt.figure(figsize=(10, 6))
            
            # Create bar chart
            bars = plt.bar(positions, rates, color='lightcoral')
            
            # Add threshold line
            plt.axhline(y=threshold, color='red', linestyle='--', label=f'Threshold ({threshold})')
            
            # Add labels and title
            plt.xlabel('Cycle Position')
            plt.ylabel('Unity Maintenance Rate')
            plt.title('Unity Maintenance Rate by Cycle Position (Range 1-52)')
            
            # Add data labels
            for bar in bars:
                height = bar.get_height()
                plt.text(bar.get_x() + bar.get_width()/2., height,
                        f'{height:.2f}', ha='center', va='bottom')
            
            # Add legend
            plt.legend()
            
            # Adjust layout
            plt.tight_layout()
            
            # Save figure
            plt.savefig(output_file)
            plt.close()
    
    def create_report_summary(self):
        """
        Create a summary of the validation report.
        
        Returns:
            Dictionary with report summary
        """
        # Get comprehensive results
        results = self.validation_results['comprehensive']
        
        # Create summary
        summary = {
            'unity_maintenance': {
                'rate': results['unity_maintenance']['overall']['unity_maintenance_rate'],
                'threshold': self.thresholds['unity_maintenance'],
                'achieved': results['unity_maintenance']['overall']['threshold_achieved']
            },
            'cross_scale_coherence': {
                'rate': results['cross_scale_coherence']['overall']['coherence_rate'],
                'threshold': self.thresholds['cross_scale_coherence'],
                'achieved': results['cross_scale_coherence']['overall']['threshold_achieved']
            },
            'performance': {
                'ratio': results['performance']['overall']['performance_ratio'],
                'threshold': self.thresholds['performance_factor'],
                'achieved': results['performance']['overall']['threshold_achieved']
            },
            'special_sets': {
                'primes': results['unity_maintenance']['special_sets']['primes']['unity_maintenance_rate'],
                'fibonacci': results['unity_maintenance']['special_sets']['fibonacci']['unity_maintenance_rate'],
                'boundary_positions': results['unity_maintenance']['special_sets']['boundary_positions']['unity_maintenance_rate']
            },
            'overall_success': results['overall_success']
        }
        
        return summary


# Test function
def test_unity_validation_framework():
    """
    Tests the UnityValidationFramework class.
    """
    validator = UnityValidationFramework()
    
    # Run comprehensive validation
    results = validator.run_comprehensive_validation()
    
    # Print summary
    print("Validation Summary:")
    print(f"Unity Maintenance Rate: {results['unity_maintenance']['overall']['unity_maintenance_rate']:.4f}")
    print(f"Unity Threshold Achieved: {results['unity_maintenance']['overall']['threshold_achieved']}")
    print(f"Cross-Scale Coherence Rate: {results['cross_scale_coherence']['overall']['coherence_rate']:.4f}")
    print(f"Coherence Threshold Achieved: {results['cross_scale_coherence']['overall']['threshold_achieved']}")
    print(f"Performance Ratio: {results['performance']['overall']['performance_ratio']:.4f}")
    print(f"Performance Threshold Achieved: {results['performance']['overall']['threshold_achieved']}")
    print(f"Overall Success: {results['overall_success']}")
    
    # Generate report
    report = validator.generate_validation_report()
    
    print("\nReport Files:")
    print(f"Results File: {report['results_file']}")
    print("Visualization Files:")
    for name, file in report['visualization_files'].items():
        print(f"  {name}: {file}")


if __name__ == "__main__":
    test_unity_validation_framework()
