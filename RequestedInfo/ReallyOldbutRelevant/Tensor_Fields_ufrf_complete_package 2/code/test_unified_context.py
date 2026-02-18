"""
Test and Validation for Unified Context Implementation

This module tests and validates the Unified Context implementation to ensure
the "Always One in Context" principle is maintained during exploration.

Author: Daniel Charboneau
License: Creative Commons Attribution-NonCommercial 4.0 International
"""

import os
import sys
import json
import time
import numpy as np
import matplotlib.pyplot as plt
from datetime import datetime

# Add parent directory to path to import other components
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from unified_context.contextual_unity_detector import ContextualUnityDetector
from unified_context.enhanced_dimensional_mapper import EnhancedDimensionalMapper
from unified_context.cross_scale_context_analyzer import CrossScaleContextAnalyzer
from unified_context.resonance_pattern_recognizer import ResonancePatternRecognizer
from unified_context.contextual_unity_validator import ContextualUnityValidator
from unified_context.unified_context_integrator import UnifiedContextIntegrator

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
        self.generate_visualizations(test_result, timestamp)
        
        return test_result
    
    def run_comparative_tests(self):
        """
        Runs comparative tests for the Unified Context implementation.
        
        Returns:
            Test results
        """
        print("Running comparative tests...")
        
        # Test cases
        test_cases = [
            {'name': 'small_range', 'start': 1, 'end': 100},
            {'name': 'medium_range', 'start': 1, 'end': 500},
            {'name': 'large_range', 'start': 1, 'end': 1000}
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
        filename = os.path.join(self.output_dir, f"comparative_test_results_{timestamp}.json")
        self.save_test_results(test_results, filename)
        
        print(f"Comparative test results saved to {filename}")
        
        # Generate comparative visualizations
        self.generate_comparative_visualizations(test_results, timestamp)
        
        return test_results
    
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
    
    def generate_visualizations(self, test_result, timestamp):
        """
        Generates visualizations for test results.
        
        Args:
            test_result: Test result
            timestamp: Timestamp for filenames
        """
        # Extract data
        range_statistics = test_result['range_results']['range_statistics']
        
        # Generate unity maintenance visualization
        self.generate_unity_maintenance_visualization(test_result, timestamp)
        
        # Generate feature discovery visualization
        self.generate_feature_discovery_visualization(test_result, timestamp)
        
        # Generate phase distribution visualization
        self.generate_phase_distribution_visualization(test_result, timestamp)
        
        # Generate feature type distribution visualization
        self.generate_feature_type_distribution_visualization(test_result, timestamp)
    
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
    
    def generate_feature_discovery_visualization(self, test_result, timestamp):
        """
        Generates feature discovery visualization.
        
        Args:
            test_result: Test result
            timestamp: Timestamp for filename
        """
        # Extract data
        range_statistics = test_result['range_results']['range_statistics']
        
        # Create figure
        plt.figure(figsize=(10, 6))
        
        # Create bar chart
        labels = ['Numbers Processed', 'Features Discovered']
        values = [test_result['range_results']['range']['end'] - test_result['range_results']['range']['start'] + 1, range_statistics['total_features']]
        colors = ['#2196F3', '#FF9800']
        
        plt.bar(labels, values, color=colors)
        
        # Add labels and title
        plt.xlabel('Category')
        plt.ylabel('Count')
        plt.title('Feature Discovery Distribution')
        
        # Add text with feature discovery rate
        plt.text(0.5, 0.9, f"Feature Discovery Rate: {range_statistics['feature_discovery_rate']:.2f}", 
                 horizontalalignment='center', verticalalignment='center', transform=plt.gca().transAxes)
        
        # Save figure
        filename = os.path.join(self.output_dir, f"feature_discovery_{timestamp}.png")
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
        phase_counts = range_statistics['phase_counts']
        
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
    
    def generate_feature_type_distribution_visualization(self, test_result, timestamp):
        """
        Generates feature type distribution visualization.
        
        Args:
            test_result: Test result
            timestamp: Timestamp for filename
        """
        # Extract data
        range_statistics = test_result['range_results']['range_statistics']
        feature_type_counts = range_statistics['feature_type_counts']
        
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
    
    def generate_comparative_visualizations(self, test_results, timestamp):
        """
        Generates comparative visualizations for test results.
        
        Args:
            test_results: List of test results
            timestamp: Timestamp for filenames
        """
        # Generate comparative unity maintenance visualization
        self.generate_comparative_unity_maintenance_visualization(test_results, timestamp)
        
        # Generate comparative feature discovery visualization
        self.generate_comparative_feature_discovery_visualization(test_results, timestamp)
        
        # Generate comparative processing time visualization
        self.generate_comparative_processing_time_visualization(test_results, timestamp)
    
    def generate_comparative_unity_maintenance_visualization(self, test_results, timestamp):
        """
        Generates comparative unity maintenance visualization.
        
        Args:
            test_results: List of test results
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
        plt.title('Comparative Unity Maintenance Rates')
        
        # Add horizontal line at 0.8 (success threshold)
        plt.axhline(y=0.8, color='r', linestyle='-', label='Success Threshold')
        
        # Add legend
        plt.legend()
        
        # Save figure
        filename = os.path.join(self.output_dir, f"comparative_unity_maintenance_{timestamp}.png")
        plt.savefig(filename)
        plt.close()
    
    def generate_comparative_feature_discovery_visualization(self, test_results, timestamp):
        """
        Generates comparative feature discovery visualization.
        
        Args:
            test_results: List of test results
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
        plt.title('Comparative Feature Discovery Rates')
        
        # Save figure
        filename = os.path.join(self.output_dir, f"comparative_feature_discovery_{timestamp}.png")
        plt.savefig(filename)
        plt.close()
    
    def generate_comparative_processing_time_visualization(self, test_results, timestamp):
        """
        Generates comparative processing time visualization.
        
        Args:
            test_results: List of test results
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
        plt.title('Comparative Processing Times')
        
        # Save figure
        filename = os.path.join(self.output_dir, f"comparative_processing_time_{timestamp}.png")
        plt.savefig(filename)
        plt.close()
    
    def run_all_tests(self):
        """
        Runs all tests for the Unified Context implementation.
        
        Returns:
            All test results
        """
        print("Running all tests...")
        
        # Run basic tests
        basic_test_results = self.run_basic_tests()
        
        # Run extended tests
        extended_test_result = self.run_extended_tests()
        
        # Run comparative tests
        comparative_test_results = self.run_comparative_tests()
        
        # Combine all test results
        all_test_results = {
            'basic_test_results': basic_test_results,
            'extended_test_result': extended_test_result,
            'comparative_test_results': comparative_test_results,
            'test_metrics': self.test_metrics
        }
        
        # Save all test results
        timestamp = int(time.time())
        filename = os.path.join(self.output_dir, f"all_test_results_{timestamp}.json")
        self.save_test_results(all_test_results, filename)
        
        print(f"All test results saved to {filename}")
        
        # Generate summary visualization
        self.generate_summary_visualization(all_test_results, timestamp)
        
        return all_test_results
    
    def generate_summary_visualization(self, all_test_results, timestamp):
        """
        Generates summary visualization for all test results.
        
        Args:
            all_test_results: All test results
            timestamp: Timestamp for filename
        """
        # Extract data
        test_metrics = all_test_results['test_metrics']
        
        # Create figure
        plt.figure(figsize=(12, 8))
        
        # Create subplots
        plt.subplot(2, 2, 1)
        
        # Create pie chart for test success/failure
        labels = ['Successful Tests', 'Failed Tests']
        values = [test_metrics['successful_tests'], test_metrics['failed_tests']]
        colors = ['#4CAF50', '#F44336']
        
        plt.pie(values, labels=labels, colors=colors, autopct='%1.1f%%', startangle=90)
        plt.title('Test Success/Failure Distribution')
        
        # Create bar chart for average rates
        plt.subplot(2, 2, 2)
        
        labels = ['Unity Maintenance', 'Feature Discovery']
        values = [test_metrics['average_unity_maintenance_rate'], test_metrics['average_feature_discovery_rate']]
        colors = ['#4CAF50', '#FF9800']
        
        plt.bar(labels, values, color=colors)
        plt.title('Average Rates')
        plt.ylim(0, 1)
        
        # Create bar chart for processing time
        plt.subplot(2, 2, 3)
        
        plt.bar(['Average Processing Time'], [test_metrics['average_processing_time']], color='#2196F3')
        plt.title('Average Processing Time')
        plt.ylabel('Seconds')
        
        # Create text summary
        plt.subplot(2, 2, 4)
        
        summary_text = f"Test Summary:\n\n"
        summary_text += f"Total Tests Run: {test_metrics['total_tests_run']}\n"
        summary_text += f"Successful Tests: {test_metrics['successful_tests']}\n"
        summary_text += f"Failed Tests: {test_metrics['failed_tests']}\n\n"
        summary_text += f"Average Unity Maintenance Rate: {test_metrics['average_unity_maintenance_rate']:.2f}\n"
        summary_text += f"Average Feature Discovery Rate: {test_metrics['average_feature_discovery_rate']:.2f}\n"
        summary_text += f"Average Processing Time: {test_metrics['average_processing_time']:.4f} seconds"
        
        plt.text(0.5, 0.5, summary_text, horizontalalignment='center', verticalalignment='center', transform=plt.gca().transAxes)
        plt.axis('off')
        
        # Adjust layout
        plt.tight_layout()
        
        # Save figure
        filename = os.path.join(self.output_dir, f"test_summary_{timestamp}.png")
        plt.savefig(filename)
        plt.close()


# Main function
def main():
    """
    Main function.
    """
    # Parse command-line arguments
    import argparse
    
    parser = argparse.ArgumentParser(description='Test and validate the Unified Context implementation.')
    parser.add_argument('--output-dir', type=str, default='./test_results', help='Directory to save test results')
    parser.add_argument('--extended-start', type=int, default=1, help='Start of range for extended tests')
    parser.add_argument('--extended-end', type=int, default=1000, help='End of range for extended tests')
    parser.add_argument('--run-all', action='store_true', help='Run all tests')
    parser.add_argument('--run-basic', action='store_true', help='Run basic tests')
    parser.add_argument('--run-extended', action='store_true', help='Run extended tests')
    parser.add_argument('--run-comparative', action='store_true', help='Run comparative tests')
    
    args = parser.parse_args()
    
    # Create tester
    tester = UnifiedContextTester(output_dir=args.output_dir)
    
    # Run tests
    if args.run_all:
        tester.run_all_tests()
    else:
        if args.run_basic:
            tester.run_basic_tests()
        
        if args.run_extended:
            tester.run_extended_tests(start=args.extended_start, end=args.extended_end)
        
        if args.run_comparative:
            tester.run_comparative_tests()
        
        # If no tests specified, run all tests
        if not (args.run_basic or args.run_extended or args.run_comparative):
            tester.run_all_tests()


if __name__ == "__main__":
    main()
