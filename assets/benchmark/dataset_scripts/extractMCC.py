import os
import argparse
from xml.etree import ElementTree as ET
from typing import Dict, Set

# The XML namespace used in MCC property files.
MCC_NAMESPACE = "http://mcc.lip6.fr/"

class CTLParser:
    """
    Parses MCC XML property files and translates CTL formulas into a custom
    string format based on a given grammar.

    This class handles the core logic of:
    1. Abstracting complex atomic propositions into simple identifiers (p0, p1, ...).
    2. Recursively translating the XML structure into a CTL string.
    """

    def __init__(self):
        # A dictionary to store the mapping from a canonical representation of
        # an atomic proposition (XML subtree) to its simple identifier (e.g., 'p0').
        self.propositions_map: Dict[str, str] = {}
        # A counter to generate new proposition identifiers.
        self.prop_counter = 0

    def _get_prop_id(self, node: ET.Element) -> str:
        """
        Abstracts a complex atomic proposition XML node into a simple identifier.

        If the proposition has been seen before, it returns the existing ID.
        Otherwise, it creates a new ID (e.g., 'p1', 'p2'), stores the mapping,
        and returns the new ID.

        Args:
            node: The XML element representing the atomic proposition.

        Returns:
            A simple string identifier for the proposition.
        """
        # Canonicalize the XML node to a string to use as a dictionary key.
        # This ensures the same XML structure always maps to the same ID.
        canonical_key = ET.tostring(node).decode('utf-8')

        if canonical_key not in self.propositions_map:
            new_id = f"p{self.prop_counter}"
            self.propositions_map[canonical_key] = new_id
            self.prop_counter += 1
        
        return self.propositions_map[canonical_key]

    def _tag(self, tag_name: str) -> str:
        """Helper to prepend the MCC namespace to a tag name."""
        return f"{{{MCC_NAMESPACE}}}{tag_name}"

    def translate_formula_node(self, node: ET.Element) -> str:
        """
        Recursively translates an XML formula node into a CTL string.

        Args:
            node: The current XML element in the formula tree.

        Returns:
            The string representation of the CTL formula for that node.
        """
        tag = node.tag
        children = list(node)

        # Boolean Connectives
        if tag == self._tag("conjunction"):
            # The grammar uses '&' for conjunction
            return f"({' & '.join(self.translate_formula_node(c) for c in children)})"
        
        if tag == self._tag("disjunction"):
            # The grammar uses '|' for disjunction
            return f"({' | '.join(self.translate_formula_node(c) for c in children)})"

        if tag == self._tag("negation"):
            return f"!({self.translate_formula_node(children[0])})"

        # Temporal Operators (Path Quantifiers)
        if tag in [self._tag("all-paths"), self._tag("exists-path")]:
            quantifier = "A" if tag == self._tag("all-paths") else "E"
            
            # The actual operator is the child of the quantifier node.
            op_node = children[0]
            op_tag = op_node.tag
            op_children = list(op_node)

            if op_tag == self._tag("globally"):
                # AG(...) or EG(...)
                return f"{quantifier}G ({self.translate_formula_node(op_children[0])})"
            
            if op_tag == self._tag("finally"):
                # AF(...) or EF(...)
                return f"{quantifier}F ({self.translate_formula_node(op_children[0])})"

            if op_tag == self._tag("next"):
                # AX(...) or EX(...) - Represented as Weak Until for grammar compatibility
                # A[X p] is equivalent to A[false W p]
                return f"{quantifier}(false W ({self.translate_formula_node(op_children[0])}))"
            
            if op_tag == self._tag("until"):
                # A[... U ...] or E[... U ...]
                before_expr = self.translate_formula_node(op_children[0].find(self._tag("*")))
                reach_expr = self.translate_formula_node(op_children[1].find(self._tag("*")))
                return f"{quantifier}({before_expr} U {reach_expr})"

        # Base Case: Atomic Propositions
        # Any other recognized tag is treated as part of an atomic proposition.
        if tag in [self._tag("integer-le"), self._tag("is-fireable"), self._tag("tokens-count")]:
            return self._get_prop_id(node)

        # If a tag is not recognized, it might be a wrapper. Recurse into its child.
        if children:
            return self.translate_formula_node(children[0])

        raise ValueError(f"Unknown or unhandled XML tag: {tag}")


    def extract_properties_from_file(self, file_path: str) -> Dict[str, str]:
        """
        Extracts all CTL properties from a single MCC properties.xml file.

        Args:
            file_path: The path to the properties.xml file.

        Returns:
            A dictionary mapping property IDs to their translated CTL strings.
        """
        try:
            tree = ET.parse(file_path)
            root = tree.getroot()
        except ET.ParseError as e:
            print(f"Warning: Could not parse XML file {file_path}. Error: {e}")
            return {}

        extracted_props = {}
        # Find all <property> elements in the file
        for prop_node in root.findall(f".//{self._tag('property')}"):
            prop_id_node = prop_node.find(self._tag("id"))
            formula_node = prop_node.find(self._tag("formula"))

            if prop_id_node is not None and formula_node is not None:
                prop_id = prop_id_node.text
                # Reset state for each file to keep proposition maps local
                # Or keep it global if you want p0, p1... to be unique across all files.
                # For this implementation, we assume a new parser instance per file run.
                try:
                    ctl_string = self.translate_formula_node(formula_node)
                    extracted_props[prop_id] = ctl_string
                except ValueError as e:
                    print(f"Warning: Could not translate property {prop_id} in {file_path}. Error: {e}")
        
        return extracted_props

def main():
    """Main function to run the CTL property extraction script."""
    parser = argparse.ArgumentParser(
        description="Extract CTL properties from a folder of MCC XML files and translate them to a custom grammar."
    )
    parser.add_argument("input_folder", 
                        type=str, default= "./rawFiles", 
                        help="The path to the folder containing MCC benchmark directories.")
    parser.add_argument(
        "-o", "--output", type=str, default="./extractedFiles",
        help="Path to the output file to save the results. (Default: extracted_properties.txt)"
    )
    args = parser.parse_args()


    output_folder = args.output
    if not os.path.exists(output_folder):
        print(f"Warning: Output folder {output_folder} did not exist, I am creating a new one")
        os.makedirs(output_folder)
    else:
        output_folder_new = output_folder # Start with the base name
        counter = 1
        while True:
            # Create a new name with a formatted number (e.g., _001, _002)
            output_folder_new = f"{output_folder}_{counter:03d}"
            if not os.path.exists(output_folder_new):
                # Found an available name, break the loop
                break
            counter += 1
        os.makedirs(output_folder_new)
        print(f"Next available folder name is: {output_folder_new}")
        output_folder = output_folder_new

    if not os.path.isdir(args.input_folder):
        print(f"Error: Input folder not found at '{args.input_folder}'")
        return

    all_properties = {}
    print(f"Searching for 'properties.xml' files in '{args.input_folder}'...")

    # Walk through the directory to find all properties.xml files
    for root, _, files in os.walk(args.input_folder):
        for file in files:
            if file == ".DS_Store":
                continue
            file_path = os.path.join(root, file)
            print(f"  -> Processing {file_path}")
            
            # Use a new parser for each file to ensure proposition IDs (p0, p1)
            # are local to that file's context.
            ctl_parser = CTLParser()
            properties = ctl_parser.extract_properties_from_file(file_path)
            
            if properties:
                # Add the filename to the property ID for uniqueness across files
                for prop_id, ctl_str in properties.items():
                    unique_id = f"{os.path.basename(os.path.dirname(file_path))}_{prop_id}"
                    all_properties[unique_id] = ctl_str

            print(f"\nExtracted a total of {len(all_properties)} properties.")

            # Write results to the output file
            with open(f"{output_folder}/{file[:-4]}.txt", "w") as f:
                #f.write("# CTL Properties extracted from MCC Benchmarks\n")
                #f.write("# Format: <Unique_Property_ID>: <Translated_CTL_String>\n\n")
                for prop_id, ctl_str in all_properties.items():
                    f.write(f"{ctl_str}\n")

    print(f"Results saved to '{args.output}'")


if __name__ == "__main__":
    main()


    