import itertools
import re
import time
from collections import defaultdict

# --- Configuration ---

# Set the maximum length of proofs to search for.
# The `a -> a` proof is 5 steps.
# WARNING: The number of proofs grows exponentially.
# With the new 9-formula basis, MAX_LENGTH = 5 is a heavy computation
# that may take several minutes.
# MAX_LENGTH = 7 is computationally infeasible and will exhaust memory.
MAX_LENGTH = 5
OUTPUT_FILENAME = "proof_output.txt"

def generate_wff_basis(max_depth=1):
    """
    Generates a set of all WFFs up to a given depth
    using atoms {'a', 'b'}.
    
    NOTE: max_depth=2 generates 74 formulas, which creates a
    search space so large (trillions of trillions of proofs)
    that it is impossible to compute. This function is
    provided for demonstration, not for use.
    """
    atoms = {'a', 'b'}
    wffs_by_depth = {0: atoms}
    all_wffs = set(atoms)

    for depth in range(1, max_depth + 1):
        wffs_by_depth[depth] = set()
        
        # Add formulas of the form (¬A)
        # where depth(A) == depth - 1
        for a in wffs_by_depth[depth - 1]:
            wffs_by_depth[depth].add(f"(¬{a})")

        # Add formulas of the form (A → B)
        # where max(depth(A), depth(B)) == depth - 1
        for i in range(depth):
            j = depth - 1
            # Case 1: depth(A) = i, depth(B) = j
            for a in wffs_by_depth[i]:
                for b in wffs_by_depth[j]:
                    wffs_by_depth[depth].add(f"({a} → {b})")
            
            if i != j:
                # Case 2: depth(A) = j, depth(B) = i
                for a in wffs_by_depth[j]:
                    for b in wffs_by_depth[i]:
                        wffs_by_depth[depth].add(f"({a} → {b})")

        all_wffs.update(wffs_by_depth[depth])
        
    return sorted(list(all_wffs))

# --- WFF Basis Definition ---

# The "building block" formulas to use for axiom substitutions.
# A small, curated list is necessary for the search to complete.
# We've added the user's examples: (¬(¬a)) and ((¬a) → (¬b))
#
WFF_BASIS = [
    'a', 'b',                 # Depth 0
    '(¬a)', '(¬b)',           # Depth 1 (¬A)
    '(a → a)',                # Depth 1 (A → B)
    '(a → b)',                # Depth 1 (A → B)
    '(¬(¬a))',                # Depth 2 (¬¬A) - User Example
    '((¬a) → (¬b))',          # Depth 2 (¬A → ¬B) - User Example
    '((¬b) → (¬a))',          # Depth 2 (¬B → ¬A) - Useful for A3
]

# --- Smaller basis for faster testing ---
# WFF_BASIS = [
#     'a', 'b',                 # Depth 0
#     '(¬a)',                   # Depth 1 (¬A)
#     '(a → a)',                # Depth 1 (A → B)
#     '(a → b)',                # Depth 1 (A → B)
# ]


# --- !! DO NOT UNCOMMENT THIS !! ---
# This is the line you requested. It will make the script unusable.
# WFF_BASIS = generate_wff_basis(max_depth=2)
# print(f"Using {len(WFF_BASIS)} WFFs for basis.")
# ---

# --- Axiom and Rule Definitions ---

# The axiom templates
AXIOM_TEMPLATES = {
    'A1': ('(A → (B → A))', ['A', 'B']),
    'A2': ('((A → (B → C)) → ((A → B) → (A → C)))', ['A', 'B', 'C']),
    'A3': ('((¬B → ¬A) → (A → B))', ['A', 'B']),
}

def substitute(template, sub_dict):
    """
    Substitutes variables (A, B, C) in a template with WFFs.
    We use regex with word boundaries (\b) to avoid partial matches.
    """
    formula = template
    # Sort keys by length (longest first) to handle nested substitutions
    # e.g., if we had 'A' and 'AA' as keys. Not strictly needed here.
    sorted_keys = sorted(sub_dict.keys(), key=len, reverse=True)
    
    for var in sorted_keys:
        wff = sub_dict[var]
        # \b ensures we replace 'A' but not 'AX'
        formula = re.sub(r'\b' + re.escape(var) + r'\b', wff, formula)
    return formula

def apply_mp(p, p_implies_q):
    """
    Tries to apply Modus Ponens.
    If p_implies_q is of the form '(p → q)', returns q.
    Otherwise, returns None.
    """
    # Ensure formulas are fully parenthesized
    expected_form = f"({p} → "
    
    if p_implies_q.startswith(expected_form) and p_implies_q.endswith(")"):
        # Extract q
        q = p_implies_q[len(expected_form):-1]
        return q
    return None

def print_proof(steps, justifications, file_handle):
    """
    Prints a single proof in the desired format to the file.
    """
    if not steps:
        return
        
    # Find max formula length for alignment
    max_len = max(len(s) for s in steps)
    
    lines = []
    for i, (step, just) in enumerate(zip(steps, justifications), 1):
        lines.append(f"  {i}. {step:<{max_len}}   {just}\n")
    lines.append("-" * 20 + "\n")
    
    file_handle.write("".join(lines))


def get_proof_complexity(steps):
    """
    Calculates a complexity score for a proof.
    We'll use the sum of the lengths of all formulas in the proof.
    """
    return sum(len(s) for s in steps)

# --- Proof Search ---

def find_all_proofs(file_handle):
    """
    Main function to find all proofs up to MAX_LENGTH.
    Writes all output to the provided file_handle.
    """
    
    # proofs_at_len[k] will store all unique proofs of *exactly* length k
    # A proof is stored as a tuple: ( (steps...), (justifications...) )
    proofs_at_len = defaultdict(list)
    
    # We store the set of unique *step sequences* at each length
    # to avoid adding duplicate proofs.
    seen_steps_at_len = defaultdict(set)
    
    total_proof_count = 0

    file_handle.write(f"--- Generating all Axiom instances (Length 1) ---\n")
    file_handle.write(f"Using WFF Basis (size {len(WFF_BASIS)}): {WFF_BASIS}\n\n")
    
    # --- Step 1: Generate all Length 1 proofs (Axiom Instantiations) ---
    for name, (template, vars) in AXIOM_TEMPLATES.items():
        # Generate all combinations of WFFs for the variables
        sub_combinations = itertools.product(WFF_BASIS, repeat=len(vars))
        
        for combo in sub_combinations:
            sub_dict = dict(zip(vars, combo))
            
            # Create the justification string
            sub_str = ', '.join(f'{k}={v}' for k, v in sub_dict.items())
            just = f"{name} [{sub_str}]"
            
            formula = substitute(template, sub_dict)
            
            steps = (formula,)
            justs = (just,)
            
            # Use the new check: add if this 1-step proof is new
            if steps not in seen_steps_at_len[1]:
                proof = (steps, justs)
                proofs_at_len[1].append(proof)
                seen_steps_at_len[1].add(steps)
                total_proof_count += 1

    file_handle.write(f"Found {len(proofs_at_len[1])} unique length-1 proofs.\n\n")
    file_handle.write(f"--- Searching for proofs up to length {MAX_LENGTH} ---\n")
    
    # --- Step 2: Generate proofs of length k > 1 ---
    for k in range(2, MAX_LENGTH + 1):
        prev_proofs = proofs_at_len[k - 1]
        if not prev_proofs:
            file_handle.write(f"No proofs of length {k-1} found, stopping search.\n")
            break
            
        file_handle.write(f"Generating proofs of length {k} from {len(prev_proofs)} proofs of length {k-1}...\n")
        
        for proof in prev_proofs:
            steps, justs = proof
            
            # --- Option A: Add an Axiom instance ---
            # This allows sequences like (Axiom, Axiom, Axiom...)
            for axiom_proof in proofs_at_len[1]:
                ax_step, ax_just = axiom_proof[0][0], axiom_proof[1][0]
                
                new_steps = steps + (ax_step,)
                
                # Check if this *entire sequence of steps* has been seen
                if new_steps not in seen_steps_at_len[k]:
                    new_justs = justs + (ax_just,)
                    new_proof = (new_steps, new_justs)
                    
                    proofs_at_len[k].append(new_proof)
                    seen_steps_at_len[k].add(new_steps)
                    total_proof_count += 1
            
            # --- Option B: Add a Modus Ponens step ---
            # This allows sequences like (Axiom, Axiom, MP(1,2))
            for i in range(k - 1): # Line 'p'
                for j in range(k - 1): # Line '(p -> q)'
                    if i == j:
                        continue
                        
                    p = steps[i]
                    p_implies_q = steps[j]
                    
                    q = apply_mp(p, p_implies_q)
                    
                    if q:
                        # We found a valid MP application
                        new_steps = steps + (q,)
                        
                        # Check if this *entire sequence of steps* has been seen
                        if new_steps not in seen_steps_at_len[k]:
                            new_justs = justs + (f"MP ({i+1},{j+1})",)
                            new_proof = (new_steps, new_justs)
                            
                            proofs_at_len[k].append(new_proof)
                            seen_steps_at_len[k].add(new_steps)
                            total_proof_count += 1

        file_handle.write(f"Found {len(proofs_at_len[k])} new unique proofs of length {k}.\n")
        if not proofs_at_len[k]:
            file_handle.write(f"No new proofs of length {k} found, stopping search.\n")
            break
        # RAM-saving measure: clear the set for the previous level
        seen_steps_at_len.pop(k-1, None)

    file_handle.write("\n--- Search Complete ---\n")
    
    # --- Step 3: Collect and print all proofs ---
    all_proofs = []
    for k in range(3, MAX_LENGTH + 1): # Start from 3 to skip proofs of length < 3
        all_proofs.extend(proofs_at_len[k])
        
    file_handle.write(f"Found a total of {total_proof_count} proofs (including non-minimal).\n")

    # Filter for proofs that use MP
    proofs_with_mp = []
    for steps, justs in all_proofs:
        # Check if any justification uses Modus Ponens
        uses_mp = False
        for just in justs:
            if just.startswith("MP"):
                uses_mp = True
                break
        if uses_mp:
            proofs_with_mp.append((steps, justs))

    file_handle.write(f"Found {len(proofs_with_mp)} proofs of length 3 or more that use Modus Ponens.\n")
    
    if not proofs_with_mp:
        file_handle.write("No proofs found with length 3 or more that use MP.\n")
        return

    # New Filtering Logic: Find the *simplest* proof for each unique theorem
    best_proofs_for_theorem = {}
    
    for proof in proofs_with_mp:
        steps, justs = proof
        theorem = steps[-1] # The final line is the theorem
        complexity = get_proof_complexity(steps)
        
        if theorem not in best_proofs_for_theorem:
            # This is the first proof we've found for this theorem
            best_proofs_for_theorem[theorem] = proof
        else:
            # We already have a proof for this theorem, check if this new one is simpler
            current_best_proof = best_proofs_for_theorem[theorem]
            current_best_complexity = get_proof_complexity(current_best_proof[0])
            
            # This proof is simpler if its complexity score is lower,
            # or if scores are tied and it has fewer lines.
            if complexity < current_best_complexity or \
               (complexity == current_best_complexity and len(steps) < len(current_best_proof[0])):
                best_proofs_for_theorem[theorem] = proof

    file_handle.write(f"Filtering down to the simplest proof for each of {len(best_proofs_for_theorem)} unique theorems...\n\n")

    # Sort the final list of best proofs: first by length, then by theorem
    final_proofs = sorted(best_proofs_for_theorem.values(), key=lambda p: (len(p[0]), p[0][-1]))

    for steps, justs in final_proofs:
        print_proof(steps, justs, file_handle)

if __name__ == "__main__":
    start_time = time.time()
    
    try:
        with open(OUTPUT_FILENAME, "w", encoding="utf-8") as f:
            f.write(f"Starting proof generation at {time.ctime()}\n")
            f.write(f"Max Length: {MAX_LENGTH}\n")
            f.write(f"Basis Size: {len(WFF_BASIS)}\n")
            f.write("="*30 + "\n\n")
            
            find_all_proofs(f)
            
            end_time = time.time()
            f.write(f"\nTotal execution time: {end_time - start_time:.4f} seconds.\n")
            
        print(f"Successfully wrote output to {OUTPUT_FILENAME}")
        print(f"Total execution time: {end_time - start_time:.4f} seconds.")
        
    except Exception as e:
        print(f"An error occurred: {e}")
        end_time = time.time()
        print(f"Total execution time before error: {end_time - start_time:.4f} seconds.")