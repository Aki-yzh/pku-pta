import os
import shutil
import json
import time
from shlex import quote
import random
import subprocess
import psutil
import traceback
from pathlib import Path

uid, serial = os.environ['TOKEN'].split(':')

global_path = Path('/mnt/global_space')
driver_path = Path('/mnt/user_space') / serial
student_path = Path('/home/student')

if not driver_path.is_dir():
    print('\n== 提交不存在')
    exit(0)

if (driver_path / 'result.json').is_file():
    print('\n== 已经评测过了')
    exit(0)

load_avg = psutil.getloadavg()[0]

print(f'\n== 当前评测机负载: {psutil.getloadavg()[0]:.1f} / {psutil.cpu_count()}')
if load_avg / psutil.cpu_count() > .5:
    assert input(' - 当前负载较高，要继续吗？[y/N]').lower()=='y'

try:
    def check_perm(p):
        stat = p.stat()
        assert stat.st_uid==0, f'{p} creator error: {stat.st_uid}'
        assert (stat.st_mode&0o777)==0o700, f'{p} permission error: {oct(stat.st_mode)}'

    check_perm(Path('/mnt'))

    print('\n== 评测环境：')
    subprocess.check_call('uname -a', shell=True)
    subprocess.check_call('java -version', shell=True)
    subprocess.check_call('python3 -VV', shell=True)

    submission_path = student_path / 'submission'

    if (driver_path / 'submission.zip').is_file():
        print('\n== 提交的文件是 .zip')

        shutil.copy(driver_path / 'submission.zip', student_path / 'submission.zip')
        (student_path / 'submission.zip').chmod(0o644)
        subprocess.check_call(f'su student -c "cd {quote(str(student_path))} && unzip -o -d submission submission.zip"', shell=True)

        if not (submission_path / 'run.sh').is_file(): # maybe in a directory
            for p in submission_path.iterdir():
                if (p / 'run.sh').is_file():
                    submission_path = p
                    break
            else:
                raise AssertionError('找不到 run.sh')

        for dir in ['testcase', 'output', 'java-benchmarks']:
            if (submission_path / dir).is_dir():
                print(f' - 删除了提交中的 {dir} 目录')
                shutil.rmtree(submission_path / dir)
            elif (submission_path / dir).is_file():
                print(f' - 删除了提交中的 {dir} 文件')
                (submission_path / dir).unlink()

    elif (driver_path / 'submission.jar').is_file():
        print('\n== 提交的文件是 .jar')

        submission_path.mkdir()
        shutil.chown(submission_path, 'student', 'student')
        shutil.copy(driver_path / 'submission.jar', submission_path / 'submission.jar')
        (submission_path / 'submission.jar').chmod(0o644)

        cmdline = 'java -jar submission.jar -a pku-pta -cp testcase -m $1'

        print(f' - 评测时将运行以下命令：{cmdline}')

        with (submission_path / 'run.sh').open('w') as f:
            f.write(f'#!/bin/bash\n{cmdline}\n')
        shutil.chown(submission_path / 'run.sh', 'student', 'student')

    (submission_path / 'java-benchmarks').symlink_to(student_path / 'java-benchmarks')
    shutil.copytree(global_path / 'benchmark', submission_path / 'testcase' / 'benchmark')

    def parse_benchmark(txt):
        ret = []

        for line in txt.splitlines():
            line = line.strip()
            if line:
                method_name, timeout_s = line.split(',')
                timeout_s = int(timeout_s)
                ret.append((method_name, timeout_s))

        return ret

    NUM_PUBLIC = 6

    benchmark = parse_benchmark((global_path / 'benchmark.txt').read_text())
    assert len(benchmark)>=NUM_PUBLIC

    global_testcase_path = global_path / 'tests'
    global_answers_path = global_path / 'answers'

    student_testcase_path = submission_path / 'testcase' / 'test'
    student_output_path = submission_path / 'result.txt'

    def kill_tree(pid):
        try:
            p = psutil.Process(pid)
            for c in p.children(recursive=True):
                c.kill()
            p.kill()
        except psutil.NoSuchProcess:
            pass

    def parse_output(txt):
        ret = {}

        for line in txt.splitlines():
            line = line.strip()
            if line:
                ptr, objects = line.split(':')

                ptr = int(ptr.strip())
                objects = set(int(t) for t in objects.split() if int(t)>0)

                ret[ptr] = objects

        return ret

    def judge_score(userans, stdans):
        std_p2o = sum(len(stdans[pt]) for pt in stdans)
        user_p2o = sum(len(userans[pt]) for pt in userans)
        score = 0
        for pt in stdans:
            objs = stdans[pt]
            if pt not in userans:
                return ('unsound', user_p2o, std_p2o), 0
            elif not objs.issubset(userans[pt]):
                return ('unsound', user_p2o, std_p2o), 1.0
            score += 1 / (len(userans[pt]) + 1) * (len(objs) + 1)
        score /= len(stdans)
        return ('sound', user_p2o, std_p2o), score + 1

    def run_case(method_name, timeout_s, show_output=False):
        # prepare benchmark

        method_path = Path(method_name.replace('.', '/') + '.java')
        (student_testcase_path / method_path).parent.mkdir(parents=True, exist_ok=True)
        shutil.copy(global_testcase_path / method_path, student_testcase_path / method_path)

        output_arg = None # output to current stdout

        try:
            t1 = time.time()

            # run student process

            if not show_output:
                output_arg = (driver_path / f'{method_name}-stdout.txt').open('w')

            p = subprocess.Popen(
                f'su student -c "cd {quote(str(submission_path))} && chmod +x run.sh && PATH=$PATH ./run.sh {quote("test."+method_name)}"',
                shell=True,
                stdout=output_arg,
                stderr=subprocess.STDOUT,
            )
            try:
                retcode = p.wait(timeout=timeout_s)
                t2 = time.time()
            except subprocess.TimeoutExpired:
                return ('error', 'run_timeout'), 0
            finally:
                # cleanup student process
                kill_tree(p.pid)

            if retcode!=0:
                return ('error', 'retcode', retcode), 0

            if not student_output_path.is_file():
                return ('error', 'result_not_found'), 0
            
            if not show_output:
                shutil.copyfile(student_output_path, driver_path / f'{method_name}-result.txt')
            
            # read output

            try:
                output = parse_output(student_output_path.read_text('utf-8'))
            except Exception as e:
                print(f'\n== 原始输出：\n{student_output_path.read_text("utf-8")}')
                return ('error', 'result_parse_error', repr(e)), 0
            
            # judge score

            answer = parse_output((global_answers_path / f'{method_name}.stdout').read_text('utf-8'))
            desc, score = judge_score(output, answer)

            if show_output:
                print(f'    输出：{output}')
                print(f'    答案：{answer}')
                print(f'    分数：{score:.2f} {desc}')

            return desc, score
            
        finally:
            # close stdout file
            if output_arg:
                output_arg.close()

            # remove previous test case
            (student_testcase_path / method_path).unlink(missing_ok=True)

            # remove previous output file
            student_output_path.unlink(missing_ok=True)

            # cleanup .class files
            for p in student_testcase_path.glob('**/*.class'):
                p.unlink()

    for b in benchmark[:NUM_PUBLIC]:
        print(f'\n== 运行公开测试用例 {b[0]}')
        desc, score = run_case(b[0], b[1], show_output=True)
        assert score>=1.99999, f'未通过公开测试用例 {b[0]}'

    print(f'\n== 运行隐藏测试用例')

    result = {
        'tot_score': 0,
        'error': None,
        'cases': {},
    }

    for idx, (method_name, timeout_s) in enumerate(benchmark[NUM_PUBLIC:]):
        print(f' - {idx+1} / {len(benchmark)-NUM_PUBLIC}')
        desc, score = run_case(method_name, timeout_s)
        result['cases'][method_name] = (desc, score)
        result['tot_score'] += score

    print(f'\n== 隐藏测试用例总分：{result["tot_score"]:.2f}')

    with (driver_path / 'result.json').open('w') as f:
        json.dump(result, f, indent=1)

except Exception:
    with (driver_path / 'result.json').open('w') as f:
        json.dump({
            'tot_score': 0,
            'error': traceback.format_exc(),
        }, f, indent=1)

    print('\n')
    raise

else:
    print('\nDone.')

finally:
    time.sleep(.3)
    shutil.copy('/root/main.stdout', driver_path / 'main.stdout.txt')