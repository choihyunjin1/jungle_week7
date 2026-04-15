# B+ Tree 인덱스 디테일 리포트 (베이스 모델 선택용)

이 문서는 `master` 브랜치와 `feature/bptree-c-implementation` 브랜치의 소스 코드를 심도 깊게 비교 분석하여, 이후 최종 발표와 개발 확장을 위한 "베이스 모델"로 무엇을 선택할지 판단하기 위한 핵심 요소들을 정리한 리포트입니다.

---

## 1. 기반 아키텍처 및 B+ Tree 스펙 비교

가장 큰 차이는 **B+ Tree 노드의 확장성 및 인덱스 활용 방식**에 있습니다.

| 항목 | `master` 브랜치 | `feature/bptree-c-implementation` 브랜치 |
|---|---|---|
| **키(Key) 타입 및 지원** | `int key` 단일 타입 전용 (고정) | `IndexKey` Union 구조 (INT 및 VARCHAR 제네릭 지원) |
| **중복 키 (Unique 여부)** | 고유(Unique) 키만 허용 (중복 시 에러 `duplicate id key`) | **Non-Unique 인덱스 지원** (`RecordRefList` 동적 배열을 통해 동일 키에 여러 Row 저장 가능) |
| **B+ Tree 순회 성능** | 단일 건 탐색(`bptree_search`), 순차 Scan 기능 부족 | `bplus_tree_leftmost_leaf`, `find_leaf` 등 최적화된 Range Scan 지원 (`BETWEEN`, `<`, `>`) |
| **레코드 참조 방식** | `long offset` 저장, 탐색 후 매번 디스크(파일) 오프셋 접근 | 엔진 기동 시점에 파싱된 `RecordDisk*` 목록을 메모리에 적재 후 참조 |
| **노드 구현 한계점** | Leaf와 Internal 필드를 `BPTreeNode` 하나로 통합하여 불필요한 메모리 소모 | `BPlusNode` 구조체 안에 Union을 구성하여 메모리 효용성 증대 |

> [!NOTE] 
> `feature/` 브랜치의 B+ Tree 구현체는 다중 컬럼 지원, 문자열 키 클론(`key_clone`), 다중 인덱스 등록 기능이 모두 준비되어 있어 실제 상용 DBMS에 훨씬 가깝게 발전되어 있습니다.

---

## 2. SQL 파서 엔진 및 Context 분석

입력된 SQL을 처리하는 방식에서도 설계 철학이 크게 갈립니다.

| 항목 | `master` 브랜치 | `feature/bptree-c-implementation` 브랜치 |
|---|---|---|
| **구문 분석 구조(Parser)** | **정통파 (LEXER + PARSER + AST)** | 스크립트 기반 **수동 문자열 파싱 (Ad-hoc Parser)** |
| **장점** | 트리 형태의 AST 노드를 구축하여 확장하기 좋고 학술적/교과서적으로 뛰어남 | 문자열 복사 및 토큰화(`split_list_items`) 방식이므로 빠르고 가볍게 동작함 |
| **단점 / 제약** | AST를 이용하면서 메모리 할당/해제 관리가 무겁고 상대적으로 복잡함 | Parser 구조가 엔진 코드(`query.c`, `executor.c`)와 얽혀있어 구문 추가 확장이 까다로움 |
| **질의 실행(Executor)** | 연산자 트리를 순회하는 재귀적 평가 방식 | `QueryCondition` (enum과 min/max range) 구조 기반의 선형 비교 |

> [!IMPORTANT]
> `master` 쪽은 Lexer를 통해 AST 노드를 구축하며(`sql_processor.h` 내부 `NodeType`, `ASTNode` 확인) 전통적인 컴파일러 파싱 기법을 모범적으로 사용하고 있습니다. 반면 `feature` 쪽은 AST 계층을 경량화하고 쿼리 실행기 내부에서 직접 잘라서 쓰는 방식을 채택했습니다.

---

## 3. 메모리, 스토리지 및 트랜잭션 문맥

- **다중 인덱스 및 스키마 관리**: 
  - `master` 브랜치는 단일 테이블 `TableMeta`에 ID 기준 1개의 BTree(`bptree`)만 고정 할당되는 구조입니다.
  - `feature` 브랜치는 `Database`, `Schema`, `Table`, 배열 형태의 `IndexMetaRuntime[MAX_INDEXES]`를 선언하여 다중 테이블 구조나 다중 컬럼 인덱스로 확장하기가 훨씬 유연합니다. (`engine_internal.h` 참고).

---

## 4. 최종 추천 및 의사결정 가이드

### 상황별 베이스 모델 추천

1. **Option A: "스토리지 & Parser의 학술적 구현과 AST 발표"에 비중을 둘 때**
   - **추천**: `master` 브랜치 유지
   - **이유**: `master` 브랜치는 디스크 상의 페이지나 파일 Offset을 직접 건드리며 I/O를 발생시키고, 정교한 Parsing AST Engine을 보여주는 "교과서적인 구현"입니다. 인덱스 알고리즘보다는 DB 시스템 전체 아키텍처나 모듈화, Lexer 구현 과정을 어필할 생각이라면 `master`가 낫습니다.
   - **보완점**: 다만 Range Scan, 다중 인덱스 추가, 문자열 인덱싱 같은 기능을 확장하려면 수정해야 할 코드가 매우 많습니다.

2. **Option B: "고도화된 인덱스 및 데이터 탐색 능력"에 성과를 보여줄 때 (강력 추천)**
   - **추천**: `feature/bptree-c-implementation` 브랜치 채택
   - **이유**: 최종 발표에서 **다양한 조건(Range, 문자열 등)에 대응하는 고도화된 B+ Tree 알고리즘**을 강조하고자 한다면 이 브랜치가 베스트입니다. 중복 키 및 다중 인덱스 구조가 이미 잡혀있습니다.
   - **보완점**: 파싱 로직이 자체 하드코딩된 부분이 있어, 복잡한 쿼리(예: `AND`/`OR` 중첩, `JOIN` 등)를 지원하도록 언어 스펙을 확장할 땐 파서 코드를 새로 짜거나 `master`의 AST 구문을 이 브랜치로 포팅하는 형태의 보강이 필요할 수 있습니다.

> [!TIP]
> 두 브랜치의 우수한 점을 융합하는 방법도 있습니다. 베이스를 `feature/bptree-c-implementation`의 **Storage & B+ Tree 매니저**로 잡고, 파싱 계층(Controller Layer)만 `master`의 AST 로직을 이식하는 혼합 구성이 가장 완성도 높은 최종 결과물을 만들어낼 수 있습니다.
