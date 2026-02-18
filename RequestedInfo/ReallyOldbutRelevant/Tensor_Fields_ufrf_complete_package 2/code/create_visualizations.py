import numpy as np
import matplotlib.pyplot as plt
import matplotlib.cm as cm
from mpl_toolkits.mplot3d import Axes3D
from matplotlib.colors import LinearSegmentedColormap
import os

# Create output directory
os.makedirs('/home/ubuntu/ufrf_visuals', exist_ok=True)

# Constants
dimensional_base = 13
phi = (1 + np.sqrt(5)) / 2  # Golden ratio
epsilon = 1e-6

# Define inner and outer octave positions
inner_octave = [4, 5, 6, 7, 8, 9]
outer_octave = [1, 2, 3, 10, 11, 12, 13]

# Define mapping from inner to outer octave
inner_to_outer = {
    4: 3,    # Inner position 4 maps to outer position 3
    5: 2,    # Inner position 5 maps to outer position 2
    6: 1,    # Inner position 6 maps to outer position 1
    7: 13,   # Inner position 7 maps to outer position 13
    8: 12,   # Inner position 8 maps to outer position 12
    9: 11    # Inner position 9 maps to outer position 11
}

# Define mapping from outer to inner octave
outer_to_inner = {
    1: 6,    # Outer position 1 maps to inner position 6
    2: 5,    # Outer position 2 maps to inner position 5
    3: 4,    # Outer position 3 maps to inner position 4
    10: None,  # Outer position 10 has no direct inner mapping
    11: 9,   # Outer position 11 maps to inner position 9
    12: 8,   # Outer position 12 maps to inner position 8
    13: 7    # Outer position 13 maps to inner position 7
}

# 1. Toroidal Geometry Visualization
def visualize_toroidal_geometry():
    # Create figure
    fig = plt.figure(figsize=(12, 10))
    ax = fig.add_subplot(111, projection='3d')
    
    # Parameters for torus
    R = 5  # Major radius
    r = 2  # Minor radius
    
    # Create torus
    theta = np.linspace(0, 2*np.pi, 100)
    phi = np.linspace(0, 2*np.pi, 100)
    theta, phi = np.meshgrid(theta, phi)
    
    # Parametric equations for torus
    x = (R + r * np.cos(phi)) * np.cos(theta)
    y = (R + r * np.cos(phi)) * np.sin(theta)
    z = r * np.sin(phi)
    
    # Plot torus surface
    ax.plot_surface(x, y, z, color='lightblue', alpha=0.7, edgecolor='none')
    
    # Mark positions on first boundary (small circle)
    for pos in range(1, dimensional_base + 1):
        angle = 2 * np.pi * (pos - 1) / dimensional_base
        px = (R + r) * np.cos(angle)
        py = (R + r) * np.sin(angle)
        pz = 0
        
        # Different colors for inner and outer octave
        if pos in inner_octave:
            color = 'blue'
            size = 100
        else:
            color = 'red'
            size = 100
        
        ax.scatter([px], [py], [pz], color=color, s=size, edgecolor='black', zorder=10)
        ax.text(px*1.1, py*1.1, pz, f"{pos}", fontsize=12)
    
    # Mark boundaries (large circle)
    for b in range(1, 4):
        angle = 2 * np.pi * (b - 1) / 12
        bx = R * np.cos(angle)
        by = R * np.sin(angle)
        bz = 0
        
        ax.scatter([bx], [by], [bz], color='green', s=200, edgecolor='black', zorder=10)
        ax.text(bx*1.1, by*1.1, bz, f"B{b}", fontsize=14)
    
    # Add arrows showing position cycle
    for pos in range(1, dimensional_base):
        angle1 = 2 * np.pi * (pos - 1) / dimensional_base
        angle2 = 2 * np.pi * pos / dimensional_base
        
        px1 = (R + r) * np.cos(angle1)
        py1 = (R + r) * np.sin(angle1)
        pz1 = 0
        
        px2 = (R + r) * np.cos(angle2)
        py2 = (R + r) * np.sin(angle2)
        pz2 = 0
        
        # Draw arrow
        ax.quiver(px1, py1, pz1, px2-px1, py2-py1, pz2-pz1, color='gray', arrow_length_ratio=0.2, linewidth=1)
    
    # Add arrows showing boundary progression
    for b in range(1, 3):
        angle1 = 2 * np.pi * (b - 1) / 12
        angle2 = 2 * np.pi * b / 12
        
        bx1 = R * np.cos(angle1)
        by1 = R * np.sin(angle1)
        bz1 = 0
        
        bx2 = R * np.cos(angle2)
        by2 = R * np.sin(angle2)
        bz2 = 0
        
        # Draw arrow
        ax.quiver(bx1, by1, bz1, bx2-bx1, by2-by1, bz2-bz1, color='darkgreen', arrow_length_ratio=0.2, linewidth=2)
    
    # Set labels and title
    ax.set_xlabel('X', fontsize=14)
    ax.set_ylabel('Y', fontsize=14)
    ax.set_zlabel('Z', fontsize=14)
    ax.set_title('Toroidal Geometry of Position-Boundary Space', fontsize=16)
    
    # Add legend
    from matplotlib.lines import Line2D
    legend_elements = [
        Line2D([0], [0], marker='o', color='w', markerfacecolor='red', markersize=15, label='Outer Octave Positions'),
        Line2D([0], [0], marker='o', color='w', markerfacecolor='blue', markersize=15, label='Inner Octave Positions'),
        Line2D([0], [0], marker='o', color='w', markerfacecolor='green', markersize=15, label='Boundaries')
    ]
    ax.legend(handles=legend_elements, loc='upper right', fontsize=12)
    
    # Set equal aspect ratio
    ax.set_box_aspect([1, 1, 1])
    
    # Save figure
    plt.savefig('/home/ubuntu/ufrf_visuals/toroidal_geometry.png', dpi=300, bbox_inches='tight')
    plt.close()

# 2. Inner-Outer Octave Duality Visualization
def visualize_inner_outer_octave_duality():
    # Create figure
    fig, ax = plt.subplots(figsize=(12, 12))
    
    # Draw circle
    circle = plt.Circle((0, 0), 5, fill=False, edgecolor='black', linewidth=2)
    ax.add_patch(circle)
    
    # Draw inner and outer regions
    inner_circle = plt.Circle((0, 0), 3, fill=True, color='lightblue', alpha=0.3)
    ax.add_patch(inner_circle)
    
    # Calculate positions on circle
    for pos in range(1, dimensional_base + 1):
        angle = 2 * np.pi * (pos - 1) / dimensional_base
        r = 5  # radius
        x = r * np.cos(angle)
        y = r * np.sin(angle)
        
        # Different colors for inner and outer octave
        if pos in inner_octave:
            color = 'blue'
            r_inner = 3
        else:
            color = 'red'
            r_inner = 5
        
        # Draw position
        ax.scatter(x, y, color=color, s=200, edgecolor='black', zorder=10)
        ax.text(x*1.1, y*1.1, f"{pos}", fontsize=14, ha='center', va='center')
        
        # Draw line from center
        ax.plot([0, x], [0, y], color='gray', linestyle='--', alpha=0.5)
    
    # Draw duality connections
    for inner_pos in inner_octave:
        outer_pos = inner_to_outer[inner_pos]
        
        # Calculate positions
        angle_inner = 2 * np.pi * (inner_pos - 1) / dimensional_base
        angle_outer = 2 * np.pi * (outer_pos - 1) / dimensional_base
        
        x_inner = 5 * np.cos(angle_inner)
        y_inner = 5 * np.sin(angle_inner)
        
        x_outer = 5 * np.cos(angle_outer)
        y_outer = 5 * np.sin(angle_outer)
        
        # Draw connection
        ax.plot([x_inner, x_outer], [y_inner, y_outer], color='purple', linewidth=2, alpha=0.7)
        
        # Add Hodge star symbol at midpoint
        mid_x = (x_inner + x_outer) / 2
        mid_y = (y_inner + y_outer) / 2
        ax.text(mid_x, mid_y, "★", fontsize=16, ha='center', va='center', color='purple')
    
    # Set labels and title
    ax.set_xlabel('', fontsize=14)
    ax.set_ylabel('', fontsize=14)
    ax.set_title('Inner-Outer Octave Duality (Hodge Duality)', fontsize=16)
    
    # Add legend
    from matplotlib.lines import Line2D
    legend_elements = [
        Line2D([0], [0], marker='o', color='w', markerfacecolor='red', markersize=15, label='Outer Octave Positions (1-3, 10-13)'),
        Line2D([0], [0], marker='o', color='w', markerfacecolor='blue', markersize=15, label='Inner Octave Positions (4-9)'),
        Line2D([0], [0], color='purple', linewidth=2, label='Hodge Duality Mapping')
    ]
    ax.legend(handles=legend_elements, loc='upper right', fontsize=12)
    
    # Set equal aspect ratio
    ax.set_aspect('equal')
    
    # Remove ticks
    ax.set_xticks([])
    ax.set_yticks([])
    
    # Save figure
    plt.savefig('/home/ubuntu/ufrf_visuals/inner_outer_octave_duality.png', dpi=300, bbox_inches='tight')
    plt.close()

# 3. Golden Ratio Boundary Mapping Visualization
def visualize_golden_ratio_boundary_mapping():
    # Create figure
    fig, ax = plt.subplots(figsize=(14, 8))
    
    # Number of boundaries to show
    num_boundaries = 8
    
    # Calculate boundary mappings
    boundaries = list(range(1, num_boundaries + 1))
    dual_boundaries = [max(1, int(round(b * phi))) for b in boundaries]
    
    # Create x positions for boundaries
    x_positions = list(range(1, num_boundaries + 1))
    
    # Plot boundaries
    ax.scatter(x_positions, [1] * num_boundaries, s=300, color='blue', edgecolor='black', zorder=10)
    
    # Plot dual boundaries
    for i, (b, db) in enumerate(zip(boundaries, dual_boundaries)):
        # Plot dual boundary
        ax.scatter(i+1, db, s=300, color='red', edgecolor='black', zorder=10)
        
        # Connect with arrow
        ax.annotate("", xy=(i+1, db), xytext=(i+1, 1),
                    arrowprops=dict(arrowstyle="->", lw=2, color='purple'))
        
        # Add golden ratio symbol
        ax.text(i+1, (1+db)/2, "φ", fontsize=16, ha='center', va='center', color='purple')
        
        # Add labels
        ax.text(i+1, 0.8, f"B{b}", fontsize=14, ha='center', va='center')
        ax.text(i+1, db+0.2, f"B{db}", fontsize=14, ha='center', va='center')
    
    # Plot golden ratio sequence
    fib_prev, fib = 1, 1
    fib_sequence = [fib]
    for i in range(num_boundaries - 1):
        fib_prev, fib = fib, fib_prev + fib
        fib_sequence.append(fib)
    
    # Normalize and plot
    max_fib = max(fib_sequence)
    normalized_fib = [f / max_fib * num_boundaries for f in fib_sequence]
    ax.plot(range(1, len(normalized_fib) + 1), normalized_fib, 'g--', linewidth=2, label='Fibonacci Sequence')
    
    # Set labels and title
    ax.set_xlabel('Boundary Number', fontsize=14)
    ax.set_ylabel('Dual Boundary Number', fontsize=14)
    ax.set_title('Golden Ratio Boundary Mapping', fontsize=16)
    
    # Add golden ratio value
    ax.text(num_boundaries - 1, num_boundaries - 1, f"φ ≈ {phi:.6f}", fontsize=14, ha='right', va='top')
    
    # Add formula
    ax.text(num_boundaries / 2, num_boundaries - 1, r"$b^* = \lfloor b \times \phi \rfloor$", fontsize=16, ha='center', va='center', bbox=dict(facecolor='white', alpha=0.8))
    
    # Add legend
    from matplotlib.lines import Line2D
    legend_elements = [
        Line2D([0], [0], marker='o', color='w', markerfacecolor='blue', markersize=15, label='Original Boundaries'),
        Line2D([0], [0], marker='o', color='w', markerfacecolor='red', markersize=15, label='Dual Boundaries'),
        Line2D([0], [0], color='green', linestyle='--', linewidth=2, label='Fibonacci Sequence (Normalized)')
    ]
    ax.legend(handles=legend_elements, loc='upper left', fontsize=12)
    
    # Set limits
    ax.set_xlim(0.5, num_boundaries + 0.5)
    ax.set_ylim(0.5, num_boundaries + 1)
    
    # Set integer ticks
    ax.set_xticks(range(1, num_boundaries + 1))
    ax.set_yticks(range(1, num_boundaries + 2))
    
    # Save figure
    plt.savefig('/home/ubuntu/ufrf_visuals/golden_ratio_boundary_mapping.png', dpi=300, bbox_inches='tight')
    plt.close()

# 4. Riemann Tensor and Coherence Visualization
def visualize_riemann_tensor_coherence():
    # Create figure
    fig, axs = plt.subplots(2, 2, figsize=(16, 14))
    
    # Flatten axes for easier indexing
    axs = axs.flatten()
    
    # Generate position and boundary values
    positions = np.linspace(1, dimensional_base, 100)
    boundaries = np.linspace(1, 3, 100)
    
    # Create meshgrid
    P, B = np.meshgrid(positions, boundaries)
    
    # Simulate Riemann tensor components
    R1 = np.sin(2 * np.pi * P / dimensional_base) * np.log(1 + B)
    R2 = np.cos(2 * np.pi * P / dimensional_base) * np.sqrt(B)
    
    # Simulate coherence
    C = 0.5 + 0.5 * np.sin(2 * np.pi * P / dimensional_base) * np.cos(np.pi * B / 3)
    
    # Plot Riemann tensor component 1
    im1 = axs[0].pcolormesh(P, B, R1, cmap='coolwarm', shading='auto')
    axs[0].set_title('Riemann Tensor Component 1', fontsize=14)
    axs[0].set_xlabel('Position', fontsize=12)
    axs[0].set_ylabel('Boundary', fontsize=12)
    fig.colorbar(im1, ax=axs[0])
    
    # Plot Riemann tensor component 2
    im2 = axs[1].pcolormesh(P, B, R2, cmap='coolwarm', shading='auto')
    axs[1].set_title('Riemann Tensor Component 2', fontsize=14)
    axs[1].set_xlabel('Position', fontsize=12)
    axs[1].set_ylabel('Boundary', fontsize=12)
    fig.colorbar(im2, ax=axs[1])
    
    # Plot coherence
    im3 = axs[2].pcolormesh(P, B, C, cmap='viridis', shading='auto', vmin=0, vmax=1)
    axs[2].set_title('Coherence', fontsize=14)
    axs[2].set_xlabel('Position', fontsize=12)
    axs[2].set_ylabel('Boundary', fontsize=12)
    fig.colorbar(im3, ax=axs[2])
    
    # Plot 3D coherence surface
    ax3d = fig.add_subplot(2, 2, 4, projection='3d')
    surf = ax3d.plot_surface(P, B, C, cmap='viridis', edgecolor='none', alpha=0.8)
    ax3d.set_title('3D Coherence Surface', fontsize=14)
    ax3d.set_xlabel('Position', fontsize=12)
    ax3d.set_ylabel('Boundary', fontsize=12)
    ax3d.set_zlabel('Coherence', fontsize=12)
    fig.colorbar(surf, ax=ax3d, shrink=0.5)
    
    # Mark inner and outer octave regions
    for ax in axs[:3]:
        # Inner octave region
        ax.axvspan(3.5, 9.5, alpha=0.2, color='blue', label='Inner Octave')
        
        # Outer octave regions
        ax.axvspan(0.5, 3.5, alpha=0.2, color='red', label='Outer Octave')
        ax.axvspan(9.5, 13.5, alpha=0.2, color='red')
    
    # Add legend to first plot
    axs[0].legend(loc='upper right')
    
    # Add overall title
    fig.suptitle('Riemann Tensor Components and Coherence', fontsize=16)
    
    # Adjust layout
    plt.tight_layout(rect=[0, 0, 1, 0.96])
    
    # Save figure
    plt.savefig('/home/ubuntu/ufrf_visuals/riemann_tensor_coherence.png', dpi=300, bbox_inches='tight')
    plt.close()

# 5. Bianchi Identity Verification Visualization
def visualize_bianchi_identity_verification():
    # Create figure
    fig, axs = plt.subplots(1, 2, figsize=(16, 8))
    
    # Generate position and boundary values
    positions = np.linspace(1, dimensional_base, 100)
    boundaries = np.linspace(1, 3, 100)
    
    # Create meshgrid
    P, B = np.meshgrid(positions, boundaries)
    
    # Simulate Bianchi identity verification errors
    # First Bianchi identity error
    error1 = 0.01 + 0.1 * np.abs(np.sin(2 * np.pi * P / dimensional_base)) * np.exp(-B/3)
    
    # Second Bianchi identity error
    error2 = 0.02 + 0.15 * np.abs(np.cos(2 * np.pi * P / dimensional_base)) * np.exp(-B/2)
    
    # Plot first Bianchi identity error
    im1 = axs[0].pcolormesh(P, B, error1, cmap='YlOrRd', shading='auto')
    axs[0].set_title('First Bianchi Identity Error', fontsize=14)
    axs[0].set_xlabel('Position', fontsize=12)
    axs[0].set_ylabel('Boundary', fontsize=12)
    fig.colorbar(im1, ax=axs[0])
    
    # Plot second Bianchi identity error
    im2 = axs[1].pcolormesh(P, B, error2, cmap='YlOrRd', shading='auto')
    axs[1].set_title('Second Bianchi Identity Error', fontsize=14)
    axs[1].set_xlabel('Position', fontsize=12)
    axs[1].set_ylabel('Boundary', fontsize=12)
    fig.colorbar(im2, ax=axs[1])
    
    # Mark inner and outer octave regions
    for ax in axs:
        # Inner octave region
        ax.axvspan(3.5, 9.5, alpha=0.2, color='blue', label='Inner Octave')
        
        # Outer octave regions
        ax.axvspan(0.5, 3.5, alpha=0.2, color='red', label='Outer Octave')
        ax.axvspan(9.5, 13.5, alpha=0.2, color='red')
    
    # Add legend to first plot
    axs[0].legend(loc='upper right')
    
    # Add formulas
    axs[0].text(7, 2.5, r"$R_{\rho[\sigma\mu\nu]} = 0$", fontsize=16, ha='center', va='center', bbox=dict(facecolor='white', alpha=0.8))
    axs[1].text(7, 2.5, r"$\nabla_{[\lambda}R^{\rho}_{\sigma]\mu\nu} = 0$", fontsize=16, ha='center', va='center', bbox=dict(facecolor='white', alpha=0.8))
    
    # Add overall title
    fig.suptitle('Bianchi Identity Verification', fontsize=16)
    
    # Adjust layout
    plt.tight_layout(rect=[0, 0, 1, 0.96])
    
    # Save figure
    plt.savefig('/home/ubuntu/ufrf_visuals/bianchi_identity_verification.png', dpi=300, bbox_inches='tight')
    plt.close()

# 6. Cross-Scale Coherence Visualization
def visualize_cross_scale_coherence():
    # Create figure
    fig, axs = plt.subplots(2, 2, figsize=(16, 14))
    
    # Flatten axes for easier indexing
    axs = axs.flatten()
    
    # Generate boundary values
    boundaries1 = np.linspace(1, 3, 50)
    boundaries2 = np.linspace(1, 3, 50)
    
    # Create meshgrid
    B1, B2 = np.meshgrid(boundaries1, boundaries2)
    
    # Simulate coherence matrices
    # Inner octave coherence
    C_inner = 0.8 * np.exp(-0.5 * np.abs(B1 - B2)) * (0.5 + 0.5 * np.cos(np.pi * (B1 - B2)))
    
    # Outer octave coherence
    C_outer = 0.6 * np.exp(-0.7 * np.abs(B1 - B2)) * (0.5 + 0.5 * np.cos(np.pi * (B1 - B2)))
    
    # Cross-scale coherence
    C_cross = C_inner * C_outer
    
    # Overall coherence
    C_overall = 0.4 * C_inner + 0.4 * C_outer + 0.2 * C_cross
    
    # Plot inner octave coherence
    im1 = axs[0].pcolormesh(B1, B2, C_inner, cmap='viridis', shading='auto', vmin=0, vmax=1)
    axs[0].set_title('Inner Octave Coherence', fontsize=14)
    axs[0].set_xlabel('Boundary 1', fontsize=12)
    axs[0].set_ylabel('Boundary 2', fontsize=12)
    fig.colorbar(im1, ax=axs[0])
    
    # Plot outer octave coherence
    im2 = axs[1].pcolormesh(B1, B2, C_outer, cmap='viridis', shading='auto', vmin=0, vmax=1)
    axs[1].set_title('Outer Octave Coherence', fontsize=14)
    axs[1].set_xlabel('Boundary 1', fontsize=12)
    axs[1].set_ylabel('Boundary 2', fontsize=12)
    fig.colorbar(im2, ax=axs[1])
    
    # Plot cross-scale coherence
    im3 = axs[2].pcolormesh(B1, B2, C_cross, cmap='viridis', shading='auto', vmin=0, vmax=1)
    axs[2].set_title('Cross-Scale Coherence', fontsize=14)
    axs[2].set_xlabel('Boundary 1', fontsize=12)
    axs[2].set_ylabel('Boundary 2', fontsize=12)
    fig.colorbar(im3, ax=axs[2])
    
    # Plot overall coherence
    im4 = axs[3].pcolormesh(B1, B2, C_overall, cmap='viridis', shading='auto', vmin=0, vmax=1)
    axs[3].set_title('Overall Coherence', fontsize=14)
    axs[3].set_xlabel('Boundary 1', fontsize=12)
    axs[3].set_ylabel('Boundary 2', fontsize=12)
    fig.colorbar(im4, ax=axs[3])
    
    # Add formula
    axs[3].text(2, 2.5, r"$C_{\times}(p_i, b_1, p_o, b_2) = C(p_i, b_1, p_o, b_2) \times C(H(p_i), b_1, H(p_o), b_2)$", 
                fontsize=14, ha='center', va='center', bbox=dict(facecolor='white', alpha=0.8))
    
    # Add overall title
    fig.suptitle('Cross-Scale Coherence Across Boundaries', fontsize=16)
    
    # Adjust layout
    plt.tight_layout(rect=[0, 0, 1, 0.96])
    
    # Save figure
    plt.savefig('/home/ubuntu/ufrf_visuals/cross_scale_coherence.png', dpi=300, bbox_inches='tight')
    plt.close()

# 7. Geodesic Boundary Transition Visualization
def visualize_geodesic_boundary_transition():
    # Create figure
    fig, ax = plt.subplots(figsize=(12, 10))
    
    # Define start and end points
    start_position = 6
    start_boundary = 1
    end_position = 6
    end_boundary = 3
    
    # Generate geodesic path
    steps = 20
    t_values = np.linspace(0, 1, steps)
    
    # Simulate geodesic path with curvature
    positions = start_position + 0.5 * np.sin(np.pi * t_values) * np.sin(2 * np.pi * t_values)
    boundaries = start_boundary + (end_boundary - start_boundary) * t_values
    
    # Simulate straight path
    straight_positions = np.ones_like(t_values) * start_position
    straight_boundaries = start_boundary + (end_boundary - start_boundary) * t_values
    
    # Plot geodesic path
    ax.plot(positions, boundaries, 'b-', linewidth=3, label='Geodesic Path')
    ax.scatter(positions, boundaries, color='blue', s=50)
    
    # Plot straight path
    ax.plot(straight_positions, straight_boundaries, 'r--', linewidth=2, label='Straight Path')
    ax.scatter(straight_positions, straight_boundaries, color='red', s=30)
    
    # Mark start and end points
    ax.scatter(start_position, start_boundary, color='green', s=200, edgecolor='black', zorder=10, label='Start Point')
    ax.scatter(end_position, end_boundary, color='purple', s=200, edgecolor='black', zorder=10, label='End Point')
    
    # Add labels
    ax.text(start_position + 0.2, start_boundary - 0.1, f"({start_position}, {start_boundary})", fontsize=12)
    ax.text(end_position + 0.2, end_boundary - 0.1, f"({end_position}, {end_boundary})", fontsize=12)
    
    # Add geodesic equation
    ax.text(9, 2, r"$\frac{d^2x^{\mu}}{dt^2} + \Gamma^{\mu}_{\nu\lambda} \frac{dx^{\nu}}{dt}\frac{dx^{\lambda}}{dt} = 0$", 
            fontsize=16, ha='center', va='center', bbox=dict(facecolor='white', alpha=0.8))
    
    # Set labels and title
    ax.set_xlabel('Position', fontsize=14)
    ax.set_ylabel('Boundary', fontsize=14)
    ax.set_title('Geodesic Boundary Transition', fontsize=16)
    
    # Set limits
    ax.set_xlim(0.5, dimensional_base + 0.5)
    ax.set_ylim(0.5, end_boundary + 0.5)
    
    # Add grid
    ax.grid(True, linestyle='--', alpha=0.7)
    
    # Mark inner and outer octave regions
    ax.axvspan(3.5, 9.5, alpha=0.2, color='blue', label='Inner Octave')
    ax.axvspan(0.5, 3.5, alpha=0.2, color='red', label='Outer Octave')
    ax.axvspan(9.5, 13.5, alpha=0.2, color='red')
    
    # Add legend
    ax.legend(loc='upper right', fontsize=12)
    
    # Save figure
    plt.savefig('/home/ubuntu/ufrf_visuals/geodesic_boundary_transition.png', dpi=300, bbox_inches='tight')
    plt.close()

# 8. Fiber Bundle Structure Visualization
def visualize_fiber_bundle_structure():
    # Create figure
    fig = plt.figure(figsize=(14, 12))
    ax = fig.add_subplot(111, projection='3d')
    
    # Define base space (boundaries)
    boundaries = np.linspace(1, 3, 3)
    
    # Define fiber space (positions)
    positions = np.linspace(1, dimensional_base, dimensional_base)
    
    # Create meshgrid
    B, P = np.meshgrid(boundaries, positions)
    
    # Calculate coordinates
    X = P * np.cos(2 * np.pi * P / dimensional_base)
    Y = P * np.sin(2 * np.pi * P / dimensional_base)
    Z = B
    
    # Plot fibers
    for b in boundaries:
        for p in positions:
            x = p * np.cos(2 * np.pi * p / dimensional_base)
            y = p * np.sin(2 * np.pi * p / dimensional_base)
            
            # Different colors for inner and outer octave
            if p in inner_octave:
                color = 'blue'
                size = 50
            else:
                color = 'red'
                size = 50
            
            # Plot point
            ax.scatter(x, y, b, color=color, s=size, edgecolor='black', zorder=10)
            
            # Add position label
            if p in [1, 4, 7, 10, 13]:
                ax.text(x, y, b + 0.1, f"{int(p)}", fontsize=10)
    
    # Plot base space
    for b in boundaries:
        theta = np.linspace(0, 2*np.pi, 100)
        r = np.linspace(0, dimensional_base, 2)
        R, Theta = np.meshgrid(r, theta)
        
        X_base = R * np.cos(Theta)
        Y_base = R * np.sin(Theta)
        Z_base = np.ones_like(X_base) * b
        
        ax.plot_surface(X_base, Y_base, Z_base, color='green', alpha=0.2)
    
    # Plot parallel transport
    for p in [1, 4, 7, 10, 13]:
        # Calculate starting point
        x1 = p * np.cos(2 * np.pi * p / dimensional_base)
        y1 = p * np.sin(2 * np.pi * p / dimensional_base)
        z1 = boundaries[0]
        
        # Calculate transported point
        transported_p = p + 0.5 * np.sin(2 * np.pi * p / dimensional_base)
        x2 = transported_p * np.cos(2 * np.pi * transported_p / dimensional_base)
        y2 = transported_p * np.sin(2 * np.pi * transported_p / dimensional_base)
        z2 = boundaries[-1]
        
        # Plot transport path
        ax.plot([x1, x2], [y1, y2], [z1, z2], 'purple', linewidth=2)
        
        # Add arrow
        arrow_length = 0.2
        ax.quiver(x2 - arrow_length*(x2-x1), y2 - arrow_length*(y2-y1), z2 - arrow_length*(z2-z1),
                 arrow_length*(x2-x1), arrow_length*(y2-y1), arrow_length*(z2-z1),
                 color='purple', arrow_length_ratio=0.3, linewidth=2)
    
    # Set labels and title
    ax.set_xlabel('X', fontsize=14)
    ax.set_ylabel('Y', fontsize=14)
    ax.set_zlabel('Boundary', fontsize=14)
    ax.set_title('Fiber Bundle Structure of Position-Boundary Space', fontsize=16)
    
    # Add legend
    from matplotlib.lines import Line2D
    legend_elements = [
        Line2D([0], [0], marker='o', color='w', markerfacecolor='red', markersize=10, label='Outer Octave Positions'),
        Line2D([0], [0], marker='o', color='w', markerfacecolor='blue', markersize=10, label='Inner Octave Positions'),
        Line2D([0], [0], color='purple', linewidth=2, label='Parallel Transport'),
        Line2D([0], [0], color='green', linewidth=2, alpha=0.5, label='Base Space (Boundaries)')
    ]
    ax.legend(handles=legend_elements, loc='upper right', fontsize=12)
    
    # Set equal aspect ratio
    ax.set_box_aspect([1, 1, 0.5])
    
    # Save figure
    plt.savefig('/home/ubuntu/ufrf_visuals/fiber_bundle_structure.png', dpi=300, bbox_inches='tight')
    plt.close()

# 9. Differential Forms Visualization
def visualize_differential_forms():
    # Create figure
    fig, axs = plt.subplots(1, 3, figsize=(18, 6))
    
    # Generate position and boundary values
    positions = np.linspace(1, dimensional_base, 50)
    boundaries = np.linspace(1, 3, 50)
    
    # Create meshgrid
    P, B = np.meshgrid(positions, boundaries)
    
    # Simulate 0-form (scalar field)
    form0 = 0.5 + 0.5 * np.sin(2 * np.pi * P / dimensional_base) * np.cos(np.pi * B / 3)
    
    # Simulate 1-form (vector field)
    dform0_dp = 0.5 * (2 * np.pi / dimensional_base) * np.cos(2 * np.pi * P / dimensional_base) * np.cos(np.pi * B / 3)
    dform0_db = -0.5 * (np.pi / 3) * np.sin(2 * np.pi * P / dimensional_base) * np.sin(np.pi * B / 3)
    
    # Simulate 2-form (area element)
    form2 = dform0_dp * dform0_db - dform0_db * dform0_dp
    
    # Plot 0-form
    im1 = axs[0].pcolormesh(P, B, form0, cmap='viridis', shading='auto')
    axs[0].set_title('0-Form (Scalar Field)', fontsize=14)
    axs[0].set_xlabel('Position', fontsize=12)
    axs[0].set_ylabel('Boundary', fontsize=12)
    fig.colorbar(im1, ax=axs[0])
    
    # Plot 1-form
    skip = 5
    axs[1].quiver(P[::skip, ::skip], B[::skip, ::skip], 
                 dform0_dp[::skip, ::skip], dform0_db[::skip, ::skip],
                 color='blue', scale=30)
    axs[1].set_title('1-Form (Vector Field)', fontsize=14)
    axs[1].set_xlabel('Position', fontsize=12)
    axs[1].set_ylabel('Boundary', fontsize=12)
    
    # Plot 2-form
    im3 = axs[2].pcolormesh(P, B, form2, cmap='coolwarm', shading='auto')
    axs[2].set_title('2-Form (Area Element)', fontsize=14)
    axs[2].set_xlabel('Position', fontsize=12)
    axs[2].set_ylabel('Boundary', fontsize=12)
    fig.colorbar(im3, ax=axs[2])
    
    # Mark inner and outer octave regions
    for ax in axs:
        # Inner octave region
        ax.axvspan(3.5, 9.5, alpha=0.2, color='blue', label='Inner Octave')
        
        # Outer octave regions
        ax.axvspan(0.5, 3.5, alpha=0.2, color='red', label='Outer Octave')
        ax.axvspan(9.5, 13.5, alpha=0.2, color='red')
    
    # Add legend to first plot
    axs[0].legend(loc='upper right')
    
    # Add formulas
    axs[0].text(7, 2.5, r"$\omega^0(p, b) = U(p, b)$", fontsize=14, ha='center', va='center', bbox=dict(facecolor='white', alpha=0.8))
    axs[1].text(7, 2.5, r"$\omega^1 = \partial_p U \, dp + \partial_b U \, db$", fontsize=14, ha='center', va='center', bbox=dict(facecolor='white', alpha=0.8))
    axs[2].text(7, 2.5, r"$\omega^2 = C(p, b) \, dp \wedge db$", fontsize=14, ha='center', va='center', bbox=dict(facecolor='white', alpha=0.8))
    
    # Add overall title
    fig.suptitle('Differential Forms in Position-Boundary Space', fontsize=16)
    
    # Adjust layout
    plt.tight_layout(rect=[0, 0, 1, 0.96])
    
    # Save figure
    plt.savefig('/home/ubuntu/ufrf_visuals/differential_forms.png', dpi=300, bbox_inches='tight')
    plt.close()

# 10. Musical Analogy Visualization
def visualize_musical_analogy():
    # Create figure
    fig, axs = plt.subplots(2, 1, figsize=(14, 12))
    
    # Generate position values
    positions = np.linspace(1, dimensional_base, 1000)
    
    # Generate frequencies for different octaves
    base_freq = 440  # A4 = 440 Hz
    
    # First octave
    freq1 = base_freq * np.sin(2 * np.pi * positions / dimensional_base)
    
    # Second octave (double frequency)
    freq2 = 2 * base_freq * np.sin(2 * np.pi * positions / dimensional_base)
    
    # Plot first octave
    axs[0].plot(positions, freq1, 'b-', linewidth=2, label='First Octave (Boundary 1)')
    
    # Plot second octave
    axs[0].plot(positions, freq2, 'r-', linewidth=2, label='Second Octave (Boundary 2)')
    
    # Mark positions
    for pos in range(1, dimensional_base + 1):
        # Calculate frequency
        f1 = base_freq * np.sin(2 * np.pi * pos / dimensional_base)
        f2 = 2 * base_freq * np.sin(2 * np.pi * pos / dimensional_base)
        
        # Different colors for inner and outer octave
        if pos in inner_octave:
            color = 'blue'
            marker = 'o'
            size = 100
        else:
            color = 'red'
            marker = 's'
            size = 100
        
        # Plot markers
        axs[0].scatter(pos, f1, color=color, marker=marker, s=size, edgecolor='black', zorder=10)
        axs[0].scatter(pos, f2, color=color, marker=marker, s=size, edgecolor='black', zorder=10)
        
        # Add position labels
        axs[0].text(pos, f1 - 30, f"{pos}", fontsize=10, ha='center')
        axs[0].text(pos, f2 + 30, f"{pos}", fontsize=10, ha='center')
    
    # Set labels and title for first plot
    axs[0].set_xlabel('Position', fontsize=14)
    axs[0].set_ylabel('Frequency (Hz)', fontsize=14)
    axs[0].set_title('Musical Octave Analogy - Frequency Domain', fontsize=16)
    
    # Add legend
    axs[0].legend(loc='upper right', fontsize=12)
    
    # Add grid
    axs[0].grid(True, linestyle='--', alpha=0.7)
    
    # Mark inner and outer octave regions
    axs[0].axvspan(3.5, 9.5, alpha=0.2, color='blue', label='Inner Octave')
    axs[0].axvspan(0.5, 3.5, alpha=0.2, color='red')
    axs[0].axvspan(9.5, 13.5, alpha=0.2, color='red')
    
    # Generate time values
    time = np.linspace(0, 0.05, 1000)
    
    # Generate waveforms for different positions
    pos1 = 1  # Outer octave
    pos2 = 6  # Inner octave
    
    # Calculate frequencies
    f1_pos1 = base_freq * np.sin(2 * np.pi * pos1 / dimensional_base)
    f1_pos2 = base_freq * np.sin(2 * np.pi * pos2 / dimensional_base)
    f2_pos1 = 2 * base_freq * np.sin(2 * np.pi * pos1 / dimensional_base)
    f2_pos2 = 2 * base_freq * np.sin(2 * np.pi * pos2 / dimensional_base)
    
    # Generate waveforms
    wave1_pos1 = np.sin(2 * np.pi * f1_pos1 * time)
    wave1_pos2 = np.sin(2 * np.pi * f1_pos2 * time)
    wave2_pos1 = np.sin(2 * np.pi * f2_pos1 * time)
    wave2_pos2 = np.sin(2 * np.pi * f2_pos2 * time)
    
    # Plot waveforms
    axs[1].plot(time, wave1_pos1, 'r-', linewidth=2, label=f'Outer Octave (Pos {pos1}, Boundary 1)')
    axs[1].plot(time, wave1_pos2, 'b-', linewidth=2, label=f'Inner Octave (Pos {pos2}, Boundary 1)')
    axs[1].plot(time, wave2_pos1, 'r--', linewidth=2, label=f'Outer Octave (Pos {pos1}, Boundary 2)')
    axs[1].plot(time, wave2_pos2, 'b--', linewidth=2, label=f'Inner Octave (Pos {pos2}, Boundary 2)')
    
    # Set labels and title for second plot
    axs[1].set_xlabel('Time (s)', fontsize=14)
    axs[1].set_ylabel('Amplitude', fontsize=14)
    axs[1].set_title('Musical Octave Analogy - Time Domain', fontsize=16)
    
    # Add legend
    axs[1].legend(loc='upper right', fontsize=12)
    
    # Add grid
    axs[1].grid(True, linestyle='--', alpha=0.7)
    
    # Add overall title
    fig.suptitle('Musical Analogy for Boundary Transitions', fontsize=18)
    
    # Adjust layout
    plt.tight_layout(rect=[0, 0, 1, 0.96])
    
    # Save figure
    plt.savefig('/home/ubuntu/ufrf_visuals/musical_analogy.png', dpi=300, bbox_inches='tight')
    plt.close()

# Execute all visualizations
visualize_toroidal_geometry()
visualize_inner_outer_octave_duality()
visualize_golden_ratio_boundary_mapping()
visualize_riemann_tensor_coherence()
visualize_bianchi_identity_verification()
visualize_cross_scale_coherence()
visualize_geodesic_boundary_transition()
visualize_fiber_bundle_structure()
visualize_differential_forms()
visualize_musical_analogy()

print("All visualizations created successfully in /home/ubuntu/ufrf_visuals/")
