import os
import re

def fix_imports(filepath):
    with open(filepath, 'r') as f:
        content = f.read()

    # Find all import lines (assuming they are strictly 'import ...')
    # We need to handle single line imports.
    # Regex for import lines: ^import .*$
    import_pattern = re.compile(r'^import .*$', re.MULTILINE)
    imports = import_pattern.findall(content)

    if not imports:
        print(f"No imports found in {filepath}")
        return

    # Remove imports from content
    # We replace them with empty strings, but need to be careful about newlines.
    # Better: split into lines, filter, and reassemble.
    lines = content.splitlines()
    non_import_lines = [line for line in lines if not line.startswith('import ')]
    
    # Reconstruct content
    new_content = '\n'.join(imports) + '\n\n' + '\n'.join(non_import_lines)
    
    # Remove excessive newlines if any (optional, but good for cleanup)
    new_content = re.sub(r'\n{3,}', '\n\n', new_content)

    with open(filepath, 'w') as f:
        f.write(new_content)
    print(f"Fixed {filepath}")

def main():
    ufrf_dir = 'UFRF'
    if not os.path.exists(ufrf_dir):
        print(f"Directory {ufrf_dir} not found")
        return

    for filename in os.listdir(ufrf_dir):
        if filename.endswith(".lean"):
            fix_imports(os.path.join(ufrf_dir, filename))

if __name__ == "__main__":
    main()
