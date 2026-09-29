# IL 관계 인수 처리 계획

**목표:** 인수가 있는 SpecTec IL `RelD`를 Lean의 인덱스가 있는 `Prop`으로 번역한다. `otherwise` 규칙은 계속 오류로 처리한다.

**접근:** `Mixfix.args`로 관계 선언과 규칙의 모든 인수를 원래 순서대로 읽는다. Lean AST에 관계의 인수 타입, 규칙의 타입이 붙은 변수, 전제 적용, 결론 적용을 표현하고, 이를 귀납 관계로 출력한다. 이 계획은 IL의 선언적 규칙만 다루며, `otherwise`와 버려지는 전제의 의미는 후속 단계에서 다룬다.

**기술:** OCaml 5.1, Dune, SpecTec `Lang.Il`, Lean 4.

**참고:** IL 정의는 `p4spec/lib/lang/il/ast.ml`, 관계 입력 힌트는 `p4spec/lib/lang/hints/input.ml`에 있다.

## 제약

- `RelD`에 `Some elsegroup`이 있으면 인수 개수와 무관하게 해당 소스 위치를 표시하며 실패한다.
- `hint(input ...)`에 나오지 않는 자리도 관계의 인수로 보존한다. 입력 힌트는 Lean 명제의 인수 개수를 바꾸지 않는다.
- 지원 범위 밖의 식은 소스 위치를 포함한 오류로 처리한다. `IfPr`, `IfNotHoldPr`, `LetPr`, `IterPr`, `DebugPr` 전제는 요청한 대로 빈 분기로 처리한다.
- 기존 `TypD` 번역을 유지하고 변경 범위를 Lean skeleton에 한정한다.
- 저장소에 예제 입력이나 Lean `example` 선언을 추가하지 않는다. 변경 사항은 커밋하지 않는다.

## 구현 단계

1. `ast.ml`에서 자료형 선언과 관계 선언을 구분한다. 관계 선언에는 이름, 인수 타입 목록, 규칙 목록을 둔다. 규칙에는 이름, 타입이 붙은 변수 바인더, 전제 적용, 결론 적용을 둔다. 적용에는 관계 이름과 순서가 있는 항 목록을 둔다.
2. `translator.ml`의 타입 번역에서 `BoolT`, `NumT`의 `nat`·`int`, `TextT`, 인수가 없는 `VarT`를 처리한다. 지원하지 않는 타입 형태는 명시적으로 실패한다.
3. `RelD (id, nottyp, _, rulegroups, None, _)`의 `Mixfix.args nottyp.it`에서 인수 타입을 순서대로 얻고, 각 규칙 결론의 `Mixfix.args`에서 항을 얻는다. `VarE`의 타입 주석을 사용해 변수마다 바인더를 하나씩 만들고 처음 나타난 순서를 유지한다. 같은 변수의 반복 사용은 같은 바인더를 참조하며, 타입 주석이 충돌하면 오류를 낸다.
4. `VarE`와 접두형 `CaseE`를 번역한다. 생성자 이름은 소속 자료형으로 한정해 출력한다. 형변환을 포함한 다른 식 형태는 그 의미를 표현할 때까지 오류로 처리한다.
5. 긍정 전제인 `IfHoldPr`와 `RulePr`의 모든 인수를 원래 순서대로 전제 적용에 담는다. `IfPr`, `IfNotHoldPr`, `LetPr`, `IterPr`, `DebugPr`는 각각 빈 전제 목록을 반환한다.
6. `Some elsegroup`이 있는 `RelD`를 일반 분기보다 먼저 검사하고 `elsegroup` 위치에서 `otherwise` 오류를 낸다.
7. `printer.ml`에서 인수 타입 `T₁ … Tₙ`을 가진 관계를 `inductive R : T₁ → … → Tₙ → Prop where`로 출력한다. 규칙 생성자는 타입이 붙은 바인더, 전제 적용, 결론 적용을 포함한다. 인수가 없는 기존 형태도 유지한다.
8. 규칙 이름을 Lean 식별자로 인용하고, 같은 관계 안에서 중복된 이름에는 순번을 붙인다.

## 검증 기준

- 규칙의 같은 변수가 여러 자리에 나오면 바인더는 하나이며 자리 사이의 동일성이 유지된다.
- 출력 자리를 포함한 모든 인수가 관계 선언, 전제 적용, 결론 적용에 남는다.
- 재귀 전제는 올바른 관계를 참조하고 인수 순서를 유지한다.
- 생성자 형태의 인수는 올바른 자료형 생성자를 참조한다.
- 하이픈이 든 규칙 이름과 여러 규칙 그룹에서 반복되는 이름도 Lean 생성자로 출력된다.
- `IfPr`, `IfNotHoldPr`, `LetPr`, `IterPr`, `DebugPr`는 Lean 규칙에 전제를 추가하지 않는다.
- `otherwise`와 지원하지 않는 인수 식은 조용히 누락되지 않고 소스 위치를 포함해 실패한다.

OCaml 5.1 환경에서 `dune build p4spec/lib/lean-skeleton/main.exe`와 `make test-speclang`을 실행한다. 필요하면 임시 SpecTec 입력을 CLI에 전달하고 생성된 결과를 Lean으로 검사한 뒤 임시 파일을 삭제한다. 현재 5.1.0 opam switch에는 `dune-project`가 요구하는 `uutf`, `uucp`, `uuseg`가 없으므로, 의존성 누락으로 인한 빌드 실패와 코드 오류를 구분한다.
