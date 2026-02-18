import numpy as np
from .differential_geometry_core import DifferentialGeometryCore

class DifferentialFormCoherence:
    """
    Uses differential forms for coherence calculations across boundaries.
    
    Author: Daniel Charboneau
    License: Creative Commons Attribution-NonCommercial 4.0 International
    """
    
    def __init__(self, dimensional_base=13):
        """
        Initialize the differential form coherence calculator.
        
        Args:
            dimensional_base: Base for dimensional calculations (default: 13)
        """
        self.dimensional_base = dimensional_base
        self.dg_core = DifferentialGeometryCore(dimensional_base)
        self.phi = (1 + np.sqrt(5)) / 2  # Golden ratio
    
    def calculate_0_form(self, position, boundary):
        """
        Calculate 0-form (scalar field) at a given position and boundary.
        
        Args:
            position: Position within boundary (1-13)
            boundary: Boundary number (1+)
            
        Returns:
            Scalar value representing the 0-form
        """
        # Determine if position is in inner or outer octave
        is_outer = position in [1, 2, 3, 10, 11, 12, 13]
        
        # Calculate base value
        if is_outer:
            # Outer octave positions have higher base values
            base_value = 0.8 + 0.2 * (position / self.dimensional_base)
        else:
            # Inner octave positions have moderate base values
            base_value = 0.5 + 0.3 * (position / self.dimensional_base)
        
        # Apply boundary scaling
        boundary_factor = 1.0 / (1.0 + 0.1 * (boundary - 1))
        
        # Calculate final value
        value = base_value * boundary_factor
        
        return value
    
    def calculate_1_form(self, position, boundary):
        """
        Calculate 1-form (covector field) at a given position and boundary.
        
        Args:
            position: Position within boundary (1-13)
            boundary: Boundary number (1+)
            
        Returns:
            2D numpy array representing the 1-form components
        """
        # Get metric tensor
        metric = self.dg_core.create_metric_tensor(position, boundary)
        
        # Calculate 0-form
        scalar = self.calculate_0_form(position, boundary)
        
        # Calculate gradient of 0-form (approximated)
        grad_p = self._approximate_scalar_derivative(position, boundary, 'position')
        grad_b = self._approximate_scalar_derivative(position, boundary, 'boundary')
        
        # Construct 1-form
        one_form = np.array([grad_p, grad_b])
        
        # Lower indices using metric
        one_form_lowered = np.zeros(2)
        for i in range(2):
            for j in range(2):
                one_form_lowered[i] += metric[i, j] * one_form[j]
        
        return one_form_lowered
    
    def _approximate_scalar_derivative(self, position, boundary, coordinate, delta=0.1):
        """
        Approximate the derivative of a scalar field with respect to a coordinate.
        
        Args:
            position: Position within boundary (1-13)
            boundary: Boundary number (1+)
            coordinate: 'position' or 'boundary'
            delta: Small increment for finite difference approximation
            
        Returns:
            Scalar derivative
        """
        if coordinate == 'position':
            # Forward point
            pos_forward = min(self.dimensional_base, position + delta)
            scalar_forward = self.calculate_0_form(pos_forward, boundary)
            
            # Backward point
            pos_backward = max(1, position - delta)
            scalar_backward = self.calculate_0_form(pos_backward, boundary)
            
            # Central difference approximation
            derivative = (scalar_forward - scalar_backward) / (pos_forward - pos_backward)
            
        elif coordinate == 'boundary':
            # Forward point
            bound_forward = boundary + delta
            scalar_forward = self.calculate_0_form(position, bound_forward)
            
            # Backward point
            bound_backward = max(1, boundary - delta)
            scalar_backward = self.calculate_0_form(position, bound_backward)
            
            # Central difference approximation
            derivative = (scalar_forward - scalar_backward) / (bound_forward - bound_backward)
        
        return derivative
    
    def calculate_2_form(self, position, boundary):
        """
        Calculate 2-form (antisymmetric tensor) at a given position and boundary.
        
        Args:
            position: Position within boundary (1-13)
            boundary: Boundary number (1+)
            
        Returns:
            2x2 numpy array representing the 2-form components
        """
        # Calculate 1-form
        one_form = self.calculate_1_form(position, boundary)
        
        # Calculate exterior derivative of 1-form (approximated)
        d_one_form_p = self._approximate_form_derivative(position, boundary, 'position', form_type=1)
        d_one_form_b = self._approximate_form_derivative(position, boundary, 'boundary', form_type=1)
        
        # Construct 2-form (antisymmetric tensor)
        two_form = np.zeros((2, 2))
        two_form[0, 1] = d_one_form_p[1] - d_one_form_b[0]
        two_form[1, 0] = -two_form[0, 1]
        
        return two_form
    
    def _approximate_form_derivative(self, position, boundary, coordinate, form_type=0, delta=0.1):
        """
        Approximate the derivative of a differential form with respect to a coordinate.
        
        Args:
            position: Position within boundary (1-13)
            boundary: Boundary number (1+)
            coordinate: 'position' or 'boundary'
            form_type: 0 for 0-form, 1 for 1-form
            delta: Small increment for finite difference approximation
            
        Returns:
            Derivative of the form
        """
        if form_type == 0:
            # 0-form derivative
            return self._approximate_scalar_derivative(position, boundary, coordinate, delta)
        
        elif form_type == 1:
            # 1-form derivative
            if coordinate == 'position':
                # Forward point
                pos_forward = min(self.dimensional_base, position + delta)
                form_forward = self.calculate_1_form(pos_forward, boundary)
                
                # Backward point
                pos_backward = max(1, position - delta)
                form_backward = self.calculate_1_form(pos_backward, boundary)
                
                # Central difference approximation
                derivative = (form_forward - form_backward) / (pos_forward - pos_backward)
                
            elif coordinate == 'boundary':
                # Forward point
                bound_forward = boundary + delta
                form_forward = self.calculate_1_form(position, bound_forward)
                
                # Backward point
                bound_backward = max(1, boundary - delta)
                form_backward = self.calculate_1_form(position, bound_backward)
                
                # Central difference approximation
                derivative = (form_forward - form_backward) / (bound_forward - bound_backward)
            
            return derivative
    
    def calculate_hodge_dual(self, form, position, boundary, form_type=0):
        """
        Calculate the Hodge dual of a differential form.
        
        Args:
            form: Differential form (scalar, vector, or tensor)
            position: Position within boundary (1-13)
            boundary: Boundary number (1+)
            form_type: 0 for 0-form, 1 for 1-form, 2 for 2-form
            
        Returns:
            Hodge dual of the form
        """
        # Get metric tensor
        metric = self.dg_core.create_metric_tensor(position, boundary)
        
        # Calculate metric determinant
        g_det = np.linalg.det(metric)
        
        if form_type == 0:
            # Hodge dual of 0-form is a 2-form (volume form)
            dual = np.zeros((2, 2))
            dual[0, 1] = form * np.sqrt(g_det)
            dual[1, 0] = -dual[0, 1]
            return dual
            
        elif form_type == 1:
            # Hodge dual of 1-form is a 1-form
            dual = np.zeros(2)
            
            # Levi-Civita symbol in 2D
            epsilon = np.zeros((2, 2))
            epsilon[0, 1] = 1
            epsilon[1, 0] = -1
            
            # Calculate dual components
            for i in range(2):
                for j in range(2):
                    for k in range(2):
                        dual[i] += epsilon[i, j] * metric[j, k] * form[k] / np.sqrt(g_det)
            
            return dual
            
        elif form_type == 2:
            # Hodge dual of 2-form is a 0-form (scalar)
            dual = form[0, 1] / np.sqrt(g_det)
            return dual
    
    def calculate_coherence_from_forms(self, position1, boundary1, position2, boundary2):
        """
        Calculate coherence between two positions using differential forms.
        
        Args:
            position1: Position in first boundary (1-13)
            boundary1: First boundary number (1+)
            position2: Position in second boundary (1-13)
            boundary2: Second boundary number (1+)
            
        Returns:
            Coherence value (0-1)
        """
        # Calculate 0-forms
        scalar1 = self.calculate_0_form(position1, boundary1)
        scalar2 = self.calculate_0_form(position2, boundary2)
        
        # Calculate 1-forms
        one_form1 = self.calculate_1_form(position1, boundary1)
        one_form2 = self.calculate_1_form(position2, boundary2)
        
        # Calculate 2-forms
        two_form1 = self.calculate_2_form(position1, boundary1)
        two_form2 = self.calculate_2_form(position2, boundary2)
        
        # Calculate Hodge duals
        dual_scalar1 = self.calculate_hodge_dual(scalar1, position1, boundary1, form_type=0)
        dual_one_form1 = self.calculate_hodge_dual(one_form1, position1, boundary1, form_type=1)
        dual_two_form1 = self.calculate_hodge_dual(two_form1, position1, boundary1, form_type=2)
        
        # Calculate coherence components
        
        # 0-form coherence (scalar similarity)
        scalar_coherence = 1.0 - abs(scalar1 - scalar2) / max(scalar1, scalar2, 1e-6)
        
        # 1-form coherence (vector similarity)
        one_form_norm1 = np.sqrt(np.sum(one_form1**2))
        one_form_norm2 = np.sqrt(np.sum(one_form2**2))
        one_form_dot = np.sum(one_form1 * one_form2)
        
        if one_form_norm1 > 0 and one_form_norm2 > 0:
            one_form_coherence = abs(one_form_dot) / (one_form_norm1 * one_form_norm2)
        else:
            one_form_coherence = 0.0
        
        # 2-form coherence (tensor similarity)
        two_form_norm1 = np.sqrt(np.sum(two_form1**2))
        two_form_norm2 = np.sqrt(np.sum(two_form2**2))
        two_form_dot = np.sum(two_form1 * two_form2)
        
        if two_form_norm1 > 0 and two_form_norm2 > 0:
            two_form_coherence = abs(two_form_dot) / (two_form_norm1 * two_form_norm2)
        else:
            two_form_coherence = 0.0
        
        # Dual form coherence
        dual_scalar_coherence = 1.0 - abs(dual_two_form1 - self.calculate_hodge_dual(two_form2, position2, boundary2, form_type=2)) / max(abs(dual_two_form1), 1e-6)
        
        # Combine coherence components
        # Weight by form degree (higher weight for higher forms)
        combined_coherence = (
            0.2 * scalar_coherence +
            0.3 * one_form_coherence +
            0.3 * two_form_coherence +
            0.2 * dual_scalar_coherence
        )
        
        return combined_coherence
    
    def calculate_boundary_coherence_from_forms(self, boundary1, boundary2):
        """
        Calculate coherence between two boundaries using differential forms.
        
        Args:
            boundary1: First boundary number (1+)
            boundary2: Second boundary number (1+)
            
        Returns:
            Dictionary of coherence values for different position types
        """
        # Calculate coherence for all positions
        all_coherences = []
        inner_coherences = []
        outer_coherences = []
        
        for pos in range(1, self.dimensional_base + 1):
            coherence = self.calculate_coherence_from_forms(pos, boundary1, pos, boundary2)
            all_coherences.append(coherence)
            
            # Separate inner and outer octave positions
            if pos in [4, 5, 6, 7, 8, 9]:
                inner_coherences.append(coherence)
            else:
                outer_coherences.append(coherence)
        
        # Calculate average coherences
        all_avg = sum(all_coherences) / len(all_coherences)
        inner_avg = sum(inner_coherences) / len(inner_coherences) if inner_coherences else 0
        outer_avg = sum(outer_coherences) / len(outer_coherences) if outer_coherences else 0
        
        return {
            'all': all_avg,
            'inner': inner_avg,
            'outer': outer_avg
        }
    
    def calculate_form_coherence_matrix(self, max_boundary=3):
        """
        Calculate coherence matrix for all positions across multiple boundaries using differential forms.
        
        Args:
            max_boundary: Maximum boundary to consider (default: 3)
            
        Returns:
            3D numpy array of coherence values [position, boundary1, boundary2]
        """
        # Initialize coherence matrix
        coherence_matrix = np.zeros((self.dimensional_base, max_boundary, max_boundary))
        
        # Calculate coherence for all position-boundary combinations
        for pos in range(1, self.dimensional_base + 1):
            for b1 in range(1, max_boundary + 1):
                for b2 in range(1, max_boundary + 1):
                    coherence = self.calculate_coherence_from_forms(pos, b1, pos, b2)
                    coherence_matrix[pos-1, b1-1, b2-1] = coherence
        
        return coherence_matrix
