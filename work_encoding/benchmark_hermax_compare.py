import time
import sys
import os
from pathlib import Path

# Tắt stdout của PySAT / hermax log để in bảng đẹp hơn
class HiddenPrints:
    def __enter__(self):
        self._original_stdout = sys.stdout
        sys.stdout = open(os.devnull, 'w')
    def __exit__(self, exc_type, exc_val, exc_tb):
        sys.stdout.close()
        sys.stdout = self._original_stdout

# PySAT encodings
from hcorap_encoding_origin import HCORAPInstance as HInstance_org, HCORAPEncoding as HEnc_org
from hcorap_encoding_new import HCORAPInstance as HInstance_new, HCORAPEncoding as HEnc_new
from maxsat_solver import solve_maxsat

# Hermax encoding
from hcorap_encoding_hermax import HCORAPInstance as HInstance_hmx, HCORAPEncodingHermax, verify_solution as verify_hmx

def run_benchmark():
    # Lấy thử 2 instances đầu tiên hoặc chỉ định cứng
    instances = [
        "instances/paperInstances/TXT_10-25_4-5_U40/instance_30_10_4_1.txt",
        "instances/paperInstances/TXT_10-25_4-5_U40/instance_40_10_4_1.txt",
        "instance_30_10_4_1.txt",
        "instance_40_10_4_1.txt",
    ]
    instances = [p for p in instances if Path(p).exists()]
    if not instances:
        folder_path = Path("instances/paperInstances/TXT_10-25_4-5_U40")
        if folder_path.exists():
            instances = sorted([str(f) for f in folder_path.glob("*.txt")])[:2]
        else:
            folder_path = Path(".")
            instances = sorted([str(f) for f in folder_path.glob("instance*.txt")])[:2]
            
    if not instances:
        print("Không tìm thấy file instance nào để chạy benchmark!")
        return
        
    print("=" * 115)
    print(f"{'Instance':<25} | {'Origin (s)':<12} | {'Origin Obj':<12} | {'New (s)':<12} | {'New Obj':<12} | {'Hermax (s)':<12} | {'Hermax Obj':<12}")
    print("-" * 115)

    for p in instances:
        name = Path(p).name[:25]
        
        # --- Origin ---
        t0 = time.time()
        with HiddenPrints():
            i_org = HInstance_org(p)
            e_org = HEnc_org(i_org)
            res_org = solve_maxsat(e_org)
        t_org = time.time() - t0
        obj_org = (res_org[0] + e_org.konstant_revenue) if res_org and res_org[0] is not False else "UNSAT"

        # --- New ---
        t0 = time.time()
        with HiddenPrints():
            i_new = HInstance_new(p)
            e_new = HEnc_new(i_new)
            res_new = solve_maxsat(e_new)
        t_new = time.time() - t0
        obj_new = (res_new[0] + e_new.konstant_revenue) if res_new and res_new[0] is not False else "UNSAT"

        # --- Hermax ---
        t0 = time.time()
        with HiddenPrints():
            i_hmx = HInstance_hmx(p)
            e_hmx = HCORAPEncodingHermax(i_hmx)
            r_hmx = e_hmx.m.solve()
        t_hmx = time.time() - t0
        
        if r_hmx.ok:
            obj_hmx = e_hmx.total_soft + e_hmx.konstant_revenue - r_hmx.cost
        else:
            obj_hmx = "UNSAT"

        print(f"{name:<25} | {t_org:<12.2f} | {str(obj_org):<12} | {t_new:<12.2f} | {str(obj_new):<12} | {t_hmx:<12.2f} | {str(obj_hmx):<12}", flush=True)
    print("=" * 115)

if __name__ == '__main__':
    run_benchmark()
