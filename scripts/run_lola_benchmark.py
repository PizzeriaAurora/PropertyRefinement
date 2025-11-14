import subprocess
import os 
import time
import datetime
import psutil
import select
from tqdm import tqdm
import sys


def test_one_model(model_path, property_file, timeout_h=10):
    cmd = ["lola", model_path, "--formula", property_file]
    mem_usage = 0
    peak_mem = 0
    start_time = time.perf_counter()

    try:
        proc = subprocess.Popen(
            ["/usr/bin/time", "-v"] + cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            bufsize=1  # line-buffered
        )
        p = psutil.Process(proc.pid)
        timeout_s = timeout_h * 3600

        full_output = []

        # Make stdout non-blocking
        fd = proc.stdout.fileno()
        os.set_blocking(fd, False)

        while True:
            # Check if process ended
            if proc.poll() is not None and not select.select([fd], [], [], 0)[0]:
                break

            # Non-blocking read if data is ready
            ready, _, _ = select.select([fd], [], [], 0.1)
            if ready:
                line = proc.stdout.readline()
                if line:
                    print(line, end="")
                    sys.stdout.flush()
                    full_output.append(line)

            # Track memory
            try:
                mem = p.memory_info().rss
                if mem > peak_mem:
                    peak_mem = mem
            except psutil.NoSuchProcess:
                break

            # Timeout check
            if time.perf_counter() - start_time > timeout_s:
                print(f"Timeout: killing process after {timeout_h} hours.")
                for child in p.children(recursive=True):
                    child.kill()
                p.kill()
                proc.wait()
                raise subprocess.TimeoutExpired(cmd, timeout=timeout_s)

        end_time = time.perf_counter()
        elapsed_time = end_time - start_time

        stdout = "".join(full_output)
        stderr = ""  # merged into stdout

        # Parse memory info from /usr/bin/time
        peak_memory = None
        for line in stdout.splitlines():
            if "Maximum resident set size" in line:
                try:
                    peak_memory = int(line.split(":")[1].strip())
                except (IndexError, ValueError):
                    pass

    except subprocess.TimeoutExpired:
        end_time = time.perf_counter()
        elapsed_time = end_time - start_time
        mem_usage = peak_mem // 1024
        peak_memory = None
        stdout, stderr = "", ""

    except Exception as e:
        end_time = time.perf_counter()
        elapsed_time = end_time - start_time
        mem_usage = peak_mem // 1024
        peak_memory = None
        stdout, stderr = "", ""
        print(f"Error running lola on {model_path}: {e}")

    mem_usage = peak_mem // 1024
    return elapsed_time, mem_usage, peak_memory

def run_folder(parent, folder, timeout_h, 
               results_path="results",
               suffix="now",
               model_folder= "Models", property_file="Properties"):
    models = [f for f in os.listdir(os.path.join(parent,model_folder, folder,)) if f.endswith('.lola')]
    #for each of the model, we take the property file with the same name but with .ctl extension and we save them as dictionary
    model_property_map = {}
    for m in sorted(models):
        name = os.path.basename(m).replace('.lola', '')
        prop_file = os.path.join(parent, property_file, folder, name + '.ctl')
        if os.path.exists(prop_file):
            model_property_map[m] = prop_file
        else:
            #for now!
            #model_property_map[m] = '/home/luca/Documents/CTL_TOOL/spissi.ctl'
            print(f"Property file {prop_file} does not exist for model {m}, skipping.")
    #now = datetime.datetime.now()

    csv_file = os.path.join(results_path, f"{folder.split('/')[-1]}_results_{suffix}.csv")
    with open(csv_file, "w") as f:
        f.write("Benchmark,Time(ms),Memory(KB)\n")
    bar = tqdm(total=len(model_property_map), desc=f"Running benchmarks in {folder}")

    for model, prop in model_property_map.items():
        bar.set_postfix(model=model, property=os.path.basename(prop))
        model_path = os.path.join(parent, model_folder, folder, model)
        
        elapsed_time, mem_usage, peak_memory = test_one_model(model_path, prop, timeout_h)
        

        with open(csv_file, "a") as f:
            f.write(f"{model},{elapsed_time * 1000},{peak_memory if peak_memory is not None else 'N/A'}\n")
        
        bar.update(1)

    bar.close()
    print(f"\nResults saved to {csv_file}")


def main():
    parent = "assets/benchmark/Dataset"
    folders = sorted(os.listdir(os.path.join(parent, "Models")))
    output_folder = "results"
    now = datetime.datetime.now()
    date_time = now.strftime("%Y-%m-%d_%H-%M-%S")
    output_folder = os.path.join(output_folder, date_time)

    timeout = 2 #hours

    if not os.path.exists(output_folder):
        os.makedirs(output_folder)

    for folder in folders:
        print(f"Running benchmarks in folder: {folder}")
        run_folder(parent, folder,timeout , results_path=output_folder)


if __name__ == "__main__":
    main()
