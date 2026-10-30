# AL positive proof run: 서버 종료 전 상태와 재개 방법

2026-10-30에 기록했다. 서버가 2026-10-31 22:00 KST(13:00 UTC)에 꺼질 예정이라 실행을 중지했다. 먼저 40M 재시도 대기 스크립트를 종료해 재시도가 자동으로 시작되지 않게 했다. 이어서 case_1708이 끝난 직후 본 실행에 SIGINT를 보냈고, `results.json`에는 `status: failed, error: interrupted`가 기록되었다. 같은 커밋에 들어간 `positive-proof-progress.md`는 중지 시점의 최종 케이스별 PASS/FAIL이다.

## 실행 정보

| 항목 | 값 |
| --- | --- |
| 시작 / 중지 | 2026-10-27 08:52 UTC 시작, 2026-10-30 01:30 UTC 중지 (64.6시간) |
| 러너 | `prove_positive_cases.py --kernel-only --case-timeout 1800`, heartbeats 기본값 4M, fuel 128 → 512 → 2048 |
| 커밋 / Lean | `3f3f9441`에서 시작 (러너 해시는 HEAD와 동일), Lean 4.34.1 |
| manifest | `typecheck-cases-al.tsv`, sha256 `459a18ef…`, accept 1,334건을 P4 소스 크기 오름차순으로 실행 |
| 실행 파일 | `_build/default/p4spec/lib/lean-skeleton/main.exe`, sha256 `3b3a394d…` |
| 산출물 | `generated/positive-al-20261027/` (gitignore, 1.6 GB). 재개에 필요한 것은 `results.json`(2.0 MB)과 `Semantics.olean`(413 MB) |
| 프로세스 | 모두 중지. 본 실행 PID 3863960, 재시도 대기 스크립트 `generated/positive-al-retry-hb40m.sh` PID 316972 |

## 진행 현황

| 상태 | 건수 | 비고 |
| --- | ---: | --- |
| proved | 578 | fuel 128: 61, 512: 505, 2048: 12 |
| evaluation-error | 318 | 모두 4M heartbeat 초과. fuel 2048에서 311건, 512에서 7건 |
| proof-error | 2 | 아래 표 |
| unsupportedChoice | 2 | 아래 표 |
| **완료 합계** | **900 / 1,334** | 크기순 앞 900건 |
| 중단 | 1 | case_1808 (`table-entries-optional-bmv2.p4`). fuel 128 probe 뒤 fuel 512 probe 도중 중지됨 |
| pending | 433 | 1,626 – 239,182 bytes |

case_1808은 `results.json`에 `outOfFuel`로, `positive-proof-progress.md`에 FAIL로 남아 있지만 실제 결과가 아니다. 러너는 fuel마다 행 상태를 갱신하는데, 중지 신호를 받으면 그 행을 마지막 중간 상태 그대로 저장하기 때문이다. 아직 실행하지 않은 케이스로 취급한다.

heartbeat 실패가 아닌 4건은 원인을 아직 분석하지 않았다.

| Case | 소스 | 상태 | 내용 |
| --- | --- | --- | --- |
| 955 | `issue1540.p4` | proof-error | fuel 512 `#reduce` probe는 success(supply 27). `rfl` 증명은 Application type mismatch로 실패 |
| 1754 | `spec-ex16.p4` | proof-error | 위와 같은 양상(supply 22) |
| 1281 | `issue5231-const-int-concat.p4` | unsupportedChoice | fuel 512 |
| 1206 | `issue3531.p4` | unsupportedChoice | fuel 2048 |

## 소요 시간 추세

크기순으로 실행하므로 남은 케이스일수록 크고 오래 걸린다. 가장 큰 증명 성공 케이스는 case_1708(1,619 bytes, 702초)이다. 최근 100건 중 91건이 heartbeat 실패였다.

| 소스 크기 (bytes) | 케이스 수 | 평균 소요 |
| --- | ---: | ---: |
| 1,000 – 1,199 | 105 | 303초 |
| 1,200 – 1,399 | 134 | 575초 |
| 1,400 – 1,619 | 85 | 773초 |

남은 434건(case_1808 포함)의 크기 분위수는 10% 1,929, 25% 2,161, 50% 2,941, 75% 4,369, 90% 5,420 bytes다.

## 남은 작업량 (추정)

- 남은 케이스 중 작은 쪽 100건 정도는 건당 약 900~1,550초 걸릴 것으로 본다. 나머지는 대부분 케이스 제한 1,800초 근처까지 걸릴 것으로 본다.
- 이 추정대로면 4M 실행을 끝까지 마치는 데 약 8일이 더 든다.

## 보존 상태

- 작업 디렉터리는 컨테이너 overlay 루트에 있다. 컨테이너를 재시작하면 유지되지만, 재생성하면 `generated/` 아래 산출물과 재시도 스크립트가 사라진다. 그럴 가능성이 있으면 `results.json`과 `Semantics.olean`을 미리 백업한다.
- `results.json`이 없어지면 아래 명령의 `--offset` 값으로 900을 그대로 쓴다. 이 커밋의 `positive-proof-progress.md`에서 case_1808을 뺀 PASS/FAIL 행 수와 같다. 다만 `--skip-proved-from`과 `--semantics-from`은 쓸 수 없다. 이 경우 Semantics를 다시 컴파일해야 하고, 증명된 케이스도 건너뛰지 못한다.

## 재부팅 후 재개

러너는 기존 `--output`/`--report` 경로를 거부하므로 같은 디렉터리에서 이어서 실행할 수 없다. 새 경로로 실행하되, 다음 두 옵션을 쓴다.

- `--offset`: 끝난 케이스를 건너뛴다. 실행 순서가 (bytes, 경로, case_id)로 고정되어 있어서 가능하다.
- `--semantics-from`: 이전 실행에서 컴파일한 Semantics를 해시 검사 후 재사용한다.

먼저 실행 파일과 manifest가 기록과 같은지 확인한다.

```bash
cd /home/p4-spectec
export PATH=/root/.elan/bin:$PATH ELAN_TOOLCHAIN=leanprover/lean4:v4.34.1
sha256sum _build/default/p4spec/lib/lean-skeleton/main.exe p4spec/test/backend-lean/typecheck-cases-al.tsv
# 3b3a394ddb9a6bf7… 와 459a18efdf8bfb43… 이어야 한다
T=p4spec/test/backend-lean; PREV=$T/generated/positive-al-20261027
```

### 권장: 남은 4M 실행을 건너뛰고 40M 재시도로 바로 진행

heartbeat 한도는 끝까지 실행되는 케이스의 결과나 걸리는 시간을 바꾸지 않는다. 따라서 4M에서 증명되는 케이스는 40M에서도 같은 시간에 증명된다. 남은 434건을 4M으로 먼저 돌리면 약 8일을 써서 대부분 실패를 기록한 뒤 같은 케이스를 다시 돌리게 된다. 아래 명령은 `generated/positive-al-retry-hb40m.sh`가 대기를 마친 뒤 실행하는 명령과 같다. 증명되지 않은 756건(앞 900건 중 실패 322건과 나머지 434건)을 40M으로 실행한다.

```bash
setsid nohup python3 $T/prove_positive_cases.py \
  --exe /home/p4-spectec/_build/default/p4spec/lib/lean-skeleton/main.exe \
  --spec /home/p4-spectec/spec -I /home/p4-spectec/p4c/p4include \
  --kernel-only --case-timeout 1800 --heartbeats 40000000 \
  --manifest $T/typecheck-cases-al.tsv \
  --semantics-from $PREV --skip-proved-from $PREV \
  --output $T/generated/positive-al-20261027-hb40m \
  --report $T/positive-proof-retry-progress.md \
  > $T/generated/positive-al-20261027-hb40m.console.txt 2>&1 < /dev/null &
```

`generated/positive-al-retry-hb40m.sh`가 남아 있으면 그 스크립트를 실행해도 된다. 기록된 PID가 더 이상 러너가 아니므로 대기하지 않고 바로 시작한다.

40M 재시도가 도중에 끊기면 같은 방식으로 이어서 실행한다. 이때 다음 세 가지를 바꾼다.

- `--offset`: 40M 실행의 `results.json`에서 계산한 완료 건수를 넣는다.
- `--skip-proved-from`: `$PREV` 그대로 둔다.
- `--output`, `--report`: 새 경로(예: `positive-al-20261027-hb40m-resume`)를 쓴다.

### 대안: 원래 계획대로 4M 실행 마무리

case_1808 때문에 `results.json`의 상태로 완료 건수를 세면 901이 되어 case_1808을 건너뛴다. 따라서 완료 건수 900을 직접 넣는다. case_1808은 크기순 정렬에서 0부터 센 900번째 케이스다.

```bash
DONE=900
setsid nohup python3 $T/prove_positive_cases.py \
  --exe /home/p4-spectec/_build/default/p4spec/lib/lean-skeleton/main.exe \
  --spec /home/p4-spectec/spec -I /home/p4-spectec/p4c/p4include \
  --kernel-only --case-timeout 1800 \
  --manifest $T/typecheck-cases-al.tsv \
  --offset $DONE --semantics-from $PREV \
  --output $T/generated/positive-al-20261027-resume \
  --report $T/positive-proof-resume-progress.md \
  > $T/generated/positive-al-20261027-resume.console.txt 2>&1 < /dev/null &
```

`--skip-proved-from`은 디렉터리를 하나만 받는다. 그래서 이후 40M 재시도는 resume 실행에서 증명된 케이스를 다시 실행한다. 이를 피하려면 이 옵션이 여러 디렉터리를 받도록 러너를 고쳐야 한다.

## 주의

- 40M 재시도에서 실제로 걸리는 제한은 heartbeat보다 케이스 제한 1,800초일 가능성이 크다. 4M heartbeat 실패 케이스는 fuel 2048 probe에서만 235~959초를 썼고, 그 전에 fuel 512 probe가 130~720초를 썼다.
- 권장안의 756건이 모두 상한까지 걸리면 약 16일(756 × 1,800초)이 든다.
- 40M 재시도가 도중에 끊기면 그 실행에서도 case_1808과 같은 중간 상태 행이 생길 수 있다. 이어서 실행할 때는 `--offset`에 마지막으로 기록된 행을 빼고 넣는다.
