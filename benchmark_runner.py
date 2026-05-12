import os
import subprocess
import time
from pathlib import Path

# Đường dẫn đến thư mục chứa các file instances (.txt)
INSTANCE_FOLDER = "instances/paperInstances/TXT_10-25_4-5_U40"

# Lệnh gọi giải (giữ nguyên phần {instance} để script tự điền tên file)
SOLVE_COMMAND = "python3 work_encoding/maxsat_solver.py {instance} --solver ./solver/EvalMaxSAT_bin"

# Cài đặt thời gian (giây)
INSTANCE_TIMEOUT = 120       
TOTAL_BENCHMARK_TIMEOUT = 1800 

def run_benchmark():
    folder_path = Path(INSTANCE_FOLDER)
    if not folder_path.exists():
        print(f"[ERROR] Thu mục không tồn tại: {INSTANCE_FOLDER}")
        return

    # Lấy danh sách các file .txt trong thư mục
    instances = sorted([f for f in folder_path.glob("*.txt")])
    print(f"[INFO] Tìm thấy {len(instances)} instances trong {INSTANCE_FOLDER}")
    print(f"[INFO] Bắt đầu chạy benchmark (Tổng thời gian tối đa: {TOTAL_BENCHMARK_TIMEOUT/60} phút)\n")

    results = {
        "solved": 0,
        "unsat": 0,
        "timeout": 0,
        "error": 0
    }
    
    start_bench_time = time.time()

    for idx, inst_path in enumerate(instances):
        # Kiểm tra tổng thời gian chạy benchmark
        if time.time() - start_bench_time > TOTAL_BENCHMARK_TIMEOUT:
            print("\n[STOP] Đã hết 30 phút tổng cộng. Dừng benchmark.")
            break

        print(f"[{idx+1}/{len(instances)}] Đang giải: {inst_path.name}...", end="", flush=True)
        
        cmd = SOLVE_COMMAND.format(instance=str(inst_path))
        t0 = time.time()
        
        try:
            # Chạy lệnh với timeout 2 phút
            process = subprocess.run(
                cmd.split(),
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                timeout=INSTANCE_TIMEOUT
            )
            
            elapsed = time.time() - t0
            output = process.stdout + process.stderr

            # Kiểm tra kết quả trong output
            if "OK" in output or "optimal" in output.lower() or "Optimum found" in output:
                print(f" XONG ({elapsed:.2f}s)")
                results["solved"] += 1
            elif "UNSATISFIABLE" in output or "unsat" in output.lower():
                print(f" UNSAT ({elapsed:.2f}s)")
                results["unsat"] += 1
            else:
                print(f" LỖI (Không nhận diện được kết quả)")
                results["error"] += 1

        except subprocess.TimeoutExpired:
            print(f" TIMEOUT (> {INSTANCE_TIMEOUT}s)")
            results["timeout"] += 1
        except Exception as e:
            print(f" LỖI HỆ THỐNG: {e}")
            results["error"] += 1

    # In báo cáo cuối cùng
    total_time = time.time() - start_bench_time
    print("\n" + "="*40)
    print("      KẾT QUẢ BENCHMARK")
    print("="*40)
    print(f"Thư mục:        {INSTANCE_FOLDER}")
    print(f"Tổng thời gian:  {total_time/60:.2f} phút")
    print(f"Số bài giải được: {results['solved']}")
    print(f"Số bài UNSAT:     {results['unsat']}")
    print(f"Số bài Timeout:   {results['timeout']}")
    print(f"Số bài bị lỗi:    {results['error']}")
    print("="*40)

if __name__ == "__main__":
    run_benchmark()
