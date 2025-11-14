

import os 
import argparse
from xml.etree import ElementTree as ET
from typing import Dict, Set
import shutil
import tarfile
#from tqdm import tqdm
# The XML namespace used in MCC property files.
MCC_NAMESPACE = "http://mcc.lip6.fr/"

PERCENTAGE = 10  # Print progress every 10%
NUM_WORKERS = 8  # Number of parallel workers for file processing
SERIAL = False  # Whether to process files serially or in parallel
class CTLParser:
    """
    Parses MCC XML property files and translates CTL formulas into a custom
    string format based on a given grammar.

    This class handles the core logic of:
    1. Abstracting complex atomic propositions into simple identifiers (p0, p1, ...).
    2. Recursively translating the XML structure into a CTL string.
    """

    def __init__(self, lola_compatible: bool = True):
        # A dictionary to store the mapping from a canonical representation of
        # an atomic proposition (XML subtree) to its simple identifier (e.g., 'p0').
        self.propositions_map: Dict[str, str] = {}
        # A counter to generate new proposition identifiers.
        self.prop_counter = 0
        self.lola_compatible = lola_compatible
        if lola_compatible:
            self.AND = "AND"
            self.OR = "OR"
            self.NOT = "NOT"
            self.ALLPATH = "A"
            self.EXPATH = "E"
            self.G = "G"
            self.F = "F"
            self.U = "U"
            self.W = "W"
            self.X = "X"
            self.end = ":"
            self.false = "FALSE"
            self.true = "TRUE"
        else:
            self.AND = "&"
            self.OR = "|"
            self.NOT = "!"
            self.ALLPATH = "A"
            self.EXPATH = "E"
            self.G = "G"
            self.F = "F"
            self.U = "U"
            self.W = "W"
            self.end = ""
            self.false = "false"
            self.true = "true"
            

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
        return canonical_key

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
            # The grammar uses 'AND' for conjunction
            return f"({f' {self.AND} '.join(self.translate_formula_node(c) for c in children)})"
        
        if tag == self._tag("disjunction"):
            # The grammar uses 'OR' for disjunction
            return f"({f' {self.OR} '.join(self.translate_formula_node(c) for c in children)})"

        if tag == self._tag("negation"):
            return f"{self.NOT}({self.translate_formula_node(children[0])})"

        # Temporal Operators (Path Quantifiers)
        if tag in [self._tag("all-paths"), self._tag("exists-path")]:
            quantifier = self.ALLPATH if tag == self._tag("all-paths") else self.EXPATH
            
            # The actual operator is the child of the quantifier node.
            op_node = children[0]
            op_tag = op_node.tag
            op_children = list(op_node)

            if op_tag == self._tag("globally"):
                # AG(...) or EG(...)
                return f"{quantifier}{self.G} ({self.translate_formula_node(op_children[0])})"
            
            if op_tag == self._tag("finally"):
                # AF(...) or EF(...)
                return f"{quantifier}{self.F} ({self.translate_formula_node(op_children[0])})"

            if op_tag == self._tag("next"):
                if not self.lola_compatible:
                    # AX(...) or EX(...) - Represented as Weak Until for grammar compatibility
                    # A[X p] is equivalent to A[false W p]
                    return f"{quantifier}({self.false} {self.W} ({self.translate_formula_node(op_children[0])}))"
                
                # A[X p] or E[X p]
                return f"{quantifier}{self.X} ({self.translate_formula_node(op_children[0])})"
            
            if op_tag == self._tag("until"):
                # A[... U ...] or E[... U ...]
                before_expr = self.translate_formula_node(op_children[0].find(self._tag("*")))
                reach_expr = self.translate_formula_node(op_children[1].find(self._tag("*")))
                return f"{quantifier}({before_expr} {self.U} {reach_expr})"

        # Base Case: Atomic Propositions
        # Any other recognized tag is treated as part of an atomic proposition.
        if tag == self._tag("integer-le"):
            before = self.translate_formula_node(children[0])
            after = self.translate_formula_node(children[1])
            return f"({before} <= {after})"
        if tag == self._tag("integer-eq"):
            before = self.translate_formula_node(children[0])
            after = self.translate_formula_node(children[1])
            return f"({before} = {after})"

        if tag in [self._tag("place"), self._tag("integer-constant")]:
            return node.text
        if tag == self._tag("tokens-count"):
            return f"{self.translate_formula_node(children[0])}"

        if tag == self._tag("is-fireable"):
            print(self.translate_formula_node(children[0]))
            return f"{self.translate_formula_node(children[0])}"

        # If a tag is not recognized, it might be a wrapper. Recurse into its child.
        if children:
            return self.translate_formula_node(children[0])

        input("wait")
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
        prop_nodes = root.findall(self._tag("property"))
        for i, prop_node in enumerate(prop_nodes):
            prop_id_node = prop_node.find(self._tag("id"))
            formula_node = prop_node.find(self._tag("formula"))
            if prop_id_node is not None and formula_node is not None:
                prop_id = prop_id_node.text
                # Reset state for each file to keep proposition maps local
                # Or keep it global if you want p0, p1... to be unique across all files.
                # For this implementation, we assume a new parser instance per file run.
                try:
                    ctl_string = self.translate_formula_node(formula_node)
                    extracted_props[prop_id] = ctl_string + self.end if i < len(prop_nodes) - 1 else ctl_string
                except ValueError as e:
                    print(f"Warning: Could not translate property {prop_id} in {file_path}. Error: {e}")
        
        return extracted_props






def create_directory(path):
    os.makedirs(path, exist_ok=True)
    #print(f"Created directory: {path}")


def create_temp_and_model_dirs(base_dir, main_output_folder):
    temp_dir = base_dir.replace("_raw", "_raw_temp")
    create_directory(temp_dir)

    model_dir = os.path.join(main_output_folder, "Models")
    create_directory(model_dir)

    for folder_name in os.listdir(base_dir):
        folder_path = os.path.join(base_dir, folder_name)
        if os.path.isdir(folder_path):
            create_directory(os.path.join(temp_dir, folder_name))
            create_directory(os.path.join(model_dir, folder_name))

    return temp_dir, model_dir


def unzip_tgz_to_folder(tgz_file, extract_to):
    #if not os.path.isdir(extract_to):
    #    print(f"Error: Expected directory at '{extract_to}' not found.")
    #    return
    if not os.path.exists(extract_to) or not os.listdir(extract_to):
        create_directory(extract_to)
        with tarfile.open(tgz_file, "r:gz") as tar:
            tar.extractall(path=os.path.dirname(tgz_file))
        #print(f"Unzipped {tgz_file} to {os.path.dirname(tgz_file)}")


def copy_files_to_dest(unzipped_dir, new_folder_path, new_model_path, tgz_name, copy_models=True):
    ctl_file_path = os.path.join(unzipped_dir, "CTLCardinality.xml")
    model_file_path = os.path.join(unzipped_dir, "model.pnml")

    if os.path.exists(ctl_file_path):
        shutil.copy(ctl_file_path, os.path.join(new_folder_path, tgz_name.replace(".tgz", ".xml")))
    else:
        print(f"CTLCardinality.xml not found in {unzipped_dir}")

    if os.path.exists(model_file_path) and copy_models:
        #before copying the model, we need to run
        # pompet to-lola model_file_path.pnml model_file_path.lola
        lola_file_name = tgz_name.split("/")[-1].replace('.tgz', '.lola')
        lola_file_path = os.path.join(new_model_path, lola_file_name)
        if not os.path.exists(lola_file_path):
            #print(f"Warning: {lola_file_path} already exists.")
            if "StigmergyElection-PT-11b" in model_file_path:
                print("Debug")
                print("skipping StigmergyElection-PT-11b for now")
                return
            print(f"Converting {model_file_path} to {lola_file_path} using pompet...")
            exit_code = os.system(f"pompet to-lola {model_file_path} {lola_file_path}")
            if exit_code != 0:
                print(f"Error: pompet failed to convert {model_file_path} to {lola_file_path}.")
        #shutil.copy(lola_file_path, os.path.join(new_model_path, lola_file_path))


def process_tgz_files(base_dir, temp_dir, model_dir, copy_models=True):
    for folder_name in sorted(os.listdir(base_dir)):
        folder_path = os.path.join(base_dir, folder_name)
        if not os.path.isdir(folder_path):
            continue

        new_folder_path = os.path.join(temp_dir, folder_name)
        new_model_path = os.path.join(model_dir, folder_name)
        if SERIAL:
            for i,file_name in enumerate(sorted(os.listdir(folder_path))):
                if not file_name.endswith(".tgz"):
                    continue
                

                tgz_file_path = os.path.join(folder_path, file_name)
                unzipped_dir = tgz_file_path.replace(".tgz", "")

                unzip_tgz_to_folder(tgz_file_path, unzipped_dir)
                copy_files_to_dest(unzipped_dir, new_folder_path, new_model_path, file_name, copy_models)
                # print every 10%
                if i % max(1, len(os.listdir(folder_path)) // PERCENTAGE) == 0:
                    print(f"Processed {i+1}/{len(os.listdir(folder_path))} files in {folder_name}")
        else:
            def unzip_and_copy(tgz_file_path, unzipped_dir, dest_folder, model_path, file_name, copy_models):
                unzip_tgz_to_folder(tgz_file_path, unzipped_dir)
                copy_files_to_dest(unzipped_dir, dest_folder, model_path, file_name, copy_models)

            from concurrent.futures import ThreadPoolExecutor, as_completed

            with ThreadPoolExecutor(max_workers=NUM_WORKERS) as executor:
                futures = []
                for i,file_name in enumerate(sorted(os.listdir(folder_path))):
                    if not file_name.endswith(".tgz"):
                        continue

                    tgz_file_path = os.path.join(folder_path, file_name)
                    unzipped_dir = tgz_file_path.replace(".tgz", "")
                    futures.append(executor.submit(unzip_and_copy, tgz_file_path, unzipped_dir, new_folder_path, new_model_path, file_name, copy_models))
                    #futures.append(executor.submit(unzip_tgz_to_folder, tgz_file_path, unzipped_dir))
                    #futures.append(executor.submit(copy_files_to_dest, unzipped_dir, new_folder_path, new_model_path, file_name))

                for i, future in enumerate(as_completed(futures)):
                    # print every 10%
                    if i % max(1, len(futures) // PERCENTAGE) == 0:
                        print(f"Processed {i+1}/{len(futures)} tasks in {folder_name}")


def create_output_folder(base_dir):
    output_folder = os.path.join(base_dir.replace("_raw", ""), "Properties")

    #if not os.path.exists(output_folder):
    #    create_directory(output_folder)
    #else:
    #    counter = 1
    #    while True:
    #        output_folder_new = f"{output_folder}_{counter:03d}"
    #        if not os.path.exists(output_folder_new):
    #            create_directory(output_folder_new)
    #            output_folder = output_folder_new
    #            break
    #        counter += 1

    return output_folder


def extract_properties_from_temp(temp_dir, output_folder):
    for folder_name in sorted(os.listdir(temp_dir)):
        folder_path = os.path.join(temp_dir, folder_name)
        if not os.path.isdir(folder_path):
            continue

        new_folder_path = os.path.join(output_folder, folder_name)
        create_directory(new_folder_path)
        #print every 25%
        if SERIAL:
            for i, (root, _, files) in enumerate(os.walk(folder_path)):
                for file in files:
                    if file == ".DS_Store":
                        continue

                    file_path = os.path.join(root, file)
                    ctl_parser = CTLParser(lola_compatible=True)
                    properties = ctl_parser.extract_properties_from_file(file_path)

                    if properties:
                        txt_file_path = os.path.join(new_folder_path, file.replace(".xml", ".ctl"))
                        with open(txt_file_path, "w") as f:
                            for _, ctl_str in properties.items():
                                f.write(f"{ctl_str}\n")

                    ctl_parser = CTLParser(lola_compatible=False)
                    properties = ctl_parser.extract_properties_from_file(file_path)

                    if properties:
                        txt_file_path = os.path.join(new_folder_path, file.replace(".xml", ".txt"))
                        with open(txt_file_path, "w") as f:
                            for _, ctl_str in properties.items():
                                f.write(f"{ctl_str}\n")

                if i % max(1, len(os.walk(folder_path)) // PERCENTAGE) == 0:
                    print(f"Extracted properties from {i+1} files in {folder_name}")
        else:
            def process_file(file_path, dest_folder):
                if file_path.endswith(".DS_Store"):
                    return
                try:
                    ctl_parser = CTLParser(lola_compatible=True)
                    properties = ctl_parser.extract_properties_from_file(file_path)
                except Exception as e:
                    print(f"Error processing {file_path}: {e}")
                    return

                if properties:
                    txt_file_path = os.path.join(dest_folder, os.path.basename(file_path).replace(".xml", ".ctl"))
                    with open(txt_file_path, "w") as f:
                        for _, ctl_str in properties.items():
                            f.write(f"{ctl_str}\n")

                ctl_parser = CTLParser(lola_compatible=False)
                properties = ctl_parser.extract_properties_from_file(file_path)

                if properties:
                    txt_file_path = os.path.join(dest_folder, os.path.basename(file_path).replace(".xml", ".txt"))
                    with open(txt_file_path, "w") as f:
                        for _, ctl_str in properties.items():
                            f.write(f"{ctl_str}\n")

            from concurrent.futures import ThreadPoolExecutor, as_completed

            all_files = [os.path.join(root, file) for root, _, files in os.walk(folder_path) for file in files if file != ".DS_Store"]
            with ThreadPoolExecutor(max_workers=NUM_WORKERS) as executor:
                futures = {executor.submit(process_file, file_path, new_folder_path): file_path for file_path in all_files}

                for i, future in enumerate(as_completed(futures)):


                    # print every 10%
                    if i % max(1, len(futures) // PERCENTAGE) == 0:
                        print(f"Extracted properties from {i+1}/{len(futures)} files in {folder_name}")
def main():
    main_output_folder = "Dataset"
    create_directory(main_output_folder)

    base_dir = "Dataset_raw"
    if not os.path.isdir(base_dir):
        print(f"Error: Input folder not found at '{base_dir}'")
        return
    print(f"Extracting models from '{base_dir}'")
    temp_dir, model_dir = create_temp_and_model_dirs(base_dir, main_output_folder)
    process_tgz_files(base_dir, temp_dir, model_dir, copy_models=True)
    print(f"Extracting properties from '{base_dir}'")
    output_folder = create_output_folder(base_dir)
    extract_properties_from_temp(temp_dir, output_folder)

    #shutil.rmtree(temp_dir)
    print(f"Removed temporary directory: {temp_dir}")
    print(f"Results saved to '{output_folder}'")


def test():
    ctl_parser = CTLParser()
    test_file = "Dataset_raw_temp/2018/AirplaneLD-COL-0010.xml"
    properties = ctl_parser.extract_properties_from_file(test_file)
    for prop_id, ctl_str in properties.items():
        print(f"{prop_id}: {ctl_str}")


if __name__ == "__main__":
    main()
    #test()
    
    