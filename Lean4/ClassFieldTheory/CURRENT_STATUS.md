# ClassFieldTheory live status

更新時刻: 2026-08-13 現在 (JST)

このファイルは CFT の唯一の実装台帳である。変動する green 状態、build 証跡、既知の
技術課題、一時停止した拡張、受入条件をここに集約する。公開向けの安定した概要は
[`README.md`](README.md) に置く。

## 現在のスナップショット

| 項目 | 状態 |
|---|---|
| 対象 | production root `ClassFieldTheory`。2026-08-13 release snapshot は **1349 modules / 396402 code lines** |
| 集約・architecture | 公開 layout 整理済み。全 owner directory の同名 aggregate、root reachability、未解決 import、cycle、冗長 facade を architecture contract で監査する |
| 最後のrelease基準点 | 2026-08-13 source の fresh-started coherent validation。production root が warning-as-error 条件で GREEN |
| 現sourceの全体 build | **GREEN**。fresh artifact setから `--rehash --no-cache --wfail` でproduction rootを検証し、error 0、warning 0。公開リポジトリのGitHub Actionsもproduction rootだけを独立fresh buildする |
| chosen-place performance | 新pipelineの個別runは Action 65s、Equiv 12s、Tensor 8.5s、Inclusion 14s、EquivApply 7.7s、Induced 5.2s、Core 3.3s、Integral 13s、Chosen 21s、aggregate 3.5s。全target green / warning 0 |
| A--F frontier | 追加実装は一時停止。未完成の B finite-place character / finite-support / product-formula と C2--C4 は production source の外へ退避済み。完成済みの B finite setup / local--global bridge / infinite real comparison と C1 tame local formula は active source に残す |
| static contracts | architecture、documentation、public API、choice、performance contracts は同一source snapshotで GREEN。公開宣言16480、必須doc欠落0、sorry 0、nolint 0、TODO 0 |
| checkpoint | 公開releaseの正本はこのstandalone repositoryの`main`とrelease tag。過去workspaceのcheckpoint hashは公開API契約に含めない |

2026-08-13 のfresh passは不足direct import 1件とKronecker--Weberの不要な `[simp]`
属性6件を検出した。owner importの追加と属性除去後、同じfresh artifact setに対する全
reverse closureを `--rehash --no-cache --wfail` で再検証し、production rootが完走した。

`SmallHilbertPrincipalization` は generic quotient rewrite の implicit instance 再推論を除き、
containment membership と完全型付き `calc` 境界へ置換した。正式targetは 4999 / 4999、
wall 148.03秒、最大 RSS 4,499,712 KiB、error 0、warning 0。

## 現sourceの完了条件

- architecture contract が算出した production inventory の全件がrootから到達可能である
- ordinary `lake build ClassFieldTheory` が error 0、warning 0
- 一時 heartbeat / recursion override なし
- source 内の `set_option`、`sorry`、`admit`、新規 `axiom`、`nolint`、警告抑制なし
- architecture、documentation、public API、choice、performance contracts 成功
- root から全 module へ到達し、未解決 import、cycle、欠けた directory aggregate がない
- `git diff --check` 成功
- scoped CFT commit 完了

## 集約・文書・公開 API の契約

`ClassFieldTheory` は単なる見出し定理の一覧ではなく、CFT の全 import closure である。
`scripts/ClassFieldTheory/check_architecture_contract.py` は次を検査する。

- production inventory と code-line count を現filesystemから一意に算出すること
- `ClassFieldTheory` から全 inventory へ到達すること
- local import がすべて解決すること
- self import と import cycle がないこと
- 全owner directoryに同名aggregateがあり、各immediate childを直接importすること
- cache外の空source directoryと、direct Lean fileが0本でchild directoryが1つだけの冗長なownerがないこと
- root・aggregate・Lake globの三者が同じmodule集合を表し、`X.+`が実在directoryだけを指すこと

`scripts/ClassFieldTheory/check_documentation_contract.py` は全 Lean module の先頭 module
docstring、公開文書、コメントを検査する。公開 API の必須 docstring は
`scripts/lean_public_api.py` で独立に監査する。履歴上の出典依存ラベル、章節番号、番号だけの
結果参照、旧出典ファイル名を現在の文書・コメントへ戻さない。

文書構造は次の二層だけにする。

- `README.md`: 公開範囲、入口、主要 API、build 方法、短い将来範囲
- `CURRENT_STATUS.md`: live状態、履歴、停止境界、問題点、受入条件

module数やcode-line数はsource変更で変動するため、この文書にrelease定数として固定しない。
release記録には同一source snapshotで実行したarchitecture contractのinventoryを添付する。

## 数学的実装範囲

### 完成している主鎖

- abstract class formation の degree、norm、Frobenius、transfer、finite reciprocity
- valuation、local field、ramification、cohomology、Kummer、Lubin--Tate の基盤
- finite / profinite local reciprocity
- local Hilbert-symbol character の exact norm kernel と norm quotient 上の単射
- maximal finite Kummer pairing の radical 変数に関する MonoidHom
- number-field idèle class formation と class-field axiom
- finite global reciprocity と finite abelian correspondence
- infinite global Artin map の principal-idèle消滅、連続 idèle-class 降下、dense range、
  positive archimedean補正、surjectivity
- ray class field、Hilbert class field、ideal Artin、decomposition、principal ideal theorem
- cyclic Hasse norm theorem
- Hasse--Arf
- local / global Kronecker--Weber

### 数学監査で解消済みの意味論的問題

| 旧問題 | 現在の実装 |
|---|---|
| conductor の不存在を `0` と同一視 | `ConductorialSubgroup` に定義域を制限済み |
| modulus が有限部分だけ | `RayClass.Modulus` は `finitePart` と選択された実場所の `infinitePart` を持つ |
| ray class fields が固定閉包内の literal tower でない | `rayClassFieldSubfield : IntermediateField K (SeparableClosure K)` と monotonicity を実装済み |
| relative index が包含を要求しない | containment-aware `relativeIndexCardinal` と全域的 `intersectionIndexCardinal` に分離済み |
| commutator normality の重複 proof | `Subgroup.Normal.of_commutator_le` を使用済み |
| quotient tower の重複実装 | `Subgroup.quotientTowerEquiv` に統一済み |
| fixed-field lattice lemma の配置 | `AlgebraicNumberTheory.Galois.FixedFieldLattice` へ移動済み |
| closed quotient の total disconnectedness の配置 | `Topology` へ統合済み |

この表は宣言の存在と API 設計の状態である。最終 build 状態は上の live snapshot だけで
判定する。

## 数学的実装範囲と一時停止した拡張

以下は現在の有限 number-field CFT が誤っているという意味ではない。実装済み主鎖と、
release整理のためproduction source外へ一時退避した独立拡張を区別する台帳である。
追加のA--F実装は現在停止しており、この節を「次に実装するもの」の指示として扱わない。
退避sourceはrelease source tree外の作業領域にあり、active rootやrelease buildの対象には
含めない。

完了済み milestone は、実装時点で次を満たしたものとして記録している。

1. 新しい数学を要する milestone は最小の source-producing lemma を数学的 owner に置き、
   結論と同値な仮定を追加しない。既存定理の specialization / ownership migration はその旨を明記する。
2. consumer は named map、membership iff、range equalityなどの型付き境界だけを使う。
3. leafとowner aggregateを通常設定でwarning 0にし、不要なimport-only facadeを作らない。
4. source-independent契約をproduction sourceへ直接適用する。
5. documentation、architecture、choice、performance契約と全体 buildを通す。

### A. 最大 abelian 拡大の無限次大域相互法則

任意の abelian Galois 拡大について、一般の principal idèle 上で
`infiniteGlobalArtinMonoidHom` が消えること、`IdeleClassGroup K` への連続降下、代表元での
評価、dense range、一般数体のpositive archimedean補正、norm-one compactnessによる
surjectivityまで実装済みである。体一般の absolute abelianization 実装は
`AlgebraicNumberTheory.Galois.AbsoluteAbelianization` へ移動済みで、旧局所APIは
definitionally compatible なwrapperとして残している。

| ID | 予定 owner | source-producing endpoint | 完了判定 |
|---|---|---|---|
| A3a [done] | `AlgebraicNumberTheory.Galois.AbsoluteAbelianization` | `absoluteCommutatorClosure`、`maximalAbelianExtension`、`absoluteTopologicalAbelianizationEquivMaximalAbelianGalois` | 体一般な実装をMathlib-only ownerへ移し、generic `...MulEquiv_mk` と旧local APIのdefinitional compatibility wrapperを保持。leaf・旧wrapper・主要consumer・両aggregateがwarning 0でgreen |
| A3b [done] | `GlobalClassFieldTheory.Reciprocity.MaximalAbelianGlobalArtin` | `maximalAbelianGlobalArtin`、`maximalAbelianGlobalArtin_finiteProjection`、`maximalAbelianGlobalArtin_surjective` | specialization・代表元評価・有限level射影・surjectivityを実装。targeted buildは4983 / 4983 jobs、warning 0でgreen |
| A3c [done] | `AlgebraicNumberTheory.Idele.IdentityComponent` | `ideleClassIdentityComponent`、`ideleClassComponentQuotient` | positive archimedean section、norm-one correction、continuity、identity-component membership、代表元分解を実装。`IdentityComponent` targeted buildは7.6s、warning 0でgreen |
| A3d [done] | `GlobalClassFieldTheory.Reciprocity.MaximalAbelianKernel` | `maximalAbelianGlobalArtin_ker`、`ideleClassComponentQuotientEquivMaximalAbelianGalois`、`..._mk` | kernelの両包含、商の位相群同型、forward/inverseの連続性、商代表で maximal Artin と一致する評価定理を実装。leafは19s、warning 0でgreen |
| A4 [done] | `GlobalClassFieldTheory.GlobalClassFields.InfiniteAbelianClassFieldCorrespondence` | `infiniteAbelianClassFieldCorrespondence`、`infiniteAbelianClassFieldCorrespondence_finite_iff_open` | `ClosedSubgroup (IdeleClassGroup K ⧸ C_K⁰)` と最大 Abelian Galois 中間体の型付き順序反転、両 inverse 式、finite/open対応を実装。leafは5.2s、warning 0でgreen |

A3d の逆包含は、component quotient 上の有限 index separator、有限 abelian layer の
norm-range transport、有限 level Artin のkernelを接続して解消した。generic topology lemma
`ContinuousMonoidHom.connectedComponentOfOne_le_ker` は `Topology` ownerに置き、A4は得られた
component quotient同型とinfinite Galois correspondenceを合成して構成している。

### B. Hilbert 記号と大域積公式

local Hilbert symbol、simple/maximal Kummer比較、bilinearity・skew・非退化性までのB2は
active sourceにある。大域側ではfinite-place setup、local--global bridge、negative/realを含む
infinite-place comparisonまでの完成済み部分をactive sourceに残した。finite-place character
comparison、有限support、全場所積公式の未完成部分はrelease対象外へ退避した。

| ID | 予定 owner | source-producing endpoint | 完了判定 |
|---|---|---|---|
| B2a0 [done] | `KummerTheory.Concrete` と既存 maximal-pairing provider | public `maximalLocalKummerExtension`、`maximalLocalKummerPairingRightHom_map_eq_rootQuotient_of_pow`、`simpleKummerExtension_le_maximalKummerExtension` | private carrier の下流 unfold をなくし、同じ n 乗を持つ任意 root での評価を root-choice-independent に公開 |
| B2a1 [done] | `LocalClassFieldTheory.Concrete.Kummer.LocalHilbertPairing` | `rootQuotient_map_intermediateFieldInclusion`、`maximalLocalArtin_restrict_simpleKummer`、`maximalLocalKummerPairingRightHom_eq_localHilbertSymbolHom` | simple root を maximal field へ写し、Artin restriction と root quotient transport だけで既存 symbol と比較。leaf / aggregateはwarning 0でgreen |
| B2b [done] | 同 ownerと field-generic norm provider | `localHilbertSymbol_mul_right`、`unit_mem_localNormSubgroup_simpleKummerExtension_one_sub`、`localHilbertSymbol_steinberg`、`localHilbertSymbol_neg_self`、`localHilbertSymbol_skew` | 明示 norm witness、Steinberg、neg-self、skewまでleafがwarning 0でgreen |
| B2c [done] | 同 owner | `localHilbertPairing`、`localHilbertPairing_apply`、`localHilbertPairing_injective_left`、`localHilbertPairing_injective_right`、`localHilbertPairing_nondegenerate` | 左右の n 乗商上のpairing、評価一致、左右単射、非退化性を実装。leafは6.9s warning 0でgreen |
| B3 infrastructure [done, active] | `GlobalClassFieldTheory.Reciprocity.GlobalHilbertSymbol` | `Core`、`FinitePlaceComparison`、`FinitePlaceLocalGlobal` と infinite-place comparison chain | finite setup / local--global bridge と complex/negative/real comparisonをactive owner aggregateから到達可能に保つ |
| B3 finite character [paused] | 退避先 `B/GlobalHilbertSymbol/FinitePlaceCharacterComparison*.lean` | finite-place root-character comparison群 | 未完成sourceはproduction rootから切り離し、release buildへ含めない |
| B3 finite support [paused] | 退避先 `B/GlobalHilbertSymbol/FinitePlaceFiniteSupport.lean` | `finitePlaceHilbertSymbol_hasFiniteMulSupport` | 未完成sourceはproduction rootから切り離し、release buildへ含めない |
| B4 [paused] | 退避先 `B/HilbertProductFormula.lean` | `globalHilbertProduct`、`globalHilbertProduct_principal`、`hilbertSymbol_allPlaces_product_eq_one` | 未完成の全場所積公式をactive CFTの完成範囲として公開しない |

既存 `localHilbertSymbol_eq_one_iff_mem_localNormSubgroup` は将来条件ではなくregression条件である。
B2b の skew symmetry は最大pairingとの比較とbilinearityだけではなく、明示norm witness、
Steinberg、neg-selfを通す算術的な比較で実装済みである。一般には
`X ^ n - b` が既約とは限らないため、`Norm (1 - β) = 1 - β ^ n` を無条件に使わず、
Galois character の像と roots-of-unity の剰余類を通じて norm witness を構成する。

### C. 一般の power-residue reciprocity

finite-field、prime ideal、ideal power-residue symbols、分子と分母の乗法性は実装済みである。
純代数のsymbolは `AlgebraicNumberTheory` に残す。CFT側ではC1のtame local formulaだけを
完成済みactive endpointとし、B4に依存するC2--C4は一つの退避sourceへまとめてrelease対象外にした。

| ID | 予定 owner | endpoint | 完了判定 |
|---|---|---|---|
| C1 [done, active] | `LocalClassFieldTheory.Concrete.Kummer.PowerResidueTameFormula` | `localHilbertSymbol_tame_formula` | uniformizer/unit分解、unramified Artin、Frobeniusのroot作用からtame local formulaを生成し、Kummer owner aggregateから公開 |
| C2 [paused] | 退避先 `C/PowerResidueReciprocity.lean` | `powerResidueBadFinitePlaces`、good-place triviality | 未完成sourceはproduction rootから切り離し、release buildへ含めない |
| C3 [paused] | 同退避source | bad-place correction付きideal power-residue reciprocity | B4未完成のためactive CFTの定理として公開しない |
| C4 [paused] | 同退避source | quadratic specialization / Gauss reciprocity comparison | C3とともにactive CFTの定理として公開しない |

退避sourceは設計資料として保存するが、再開を明示するまでimport・API化・build対象化しない。

### D. ノルム制限定理

有限拡大 `E/K` と、その中の最大 abelian Galois 部分拡大 `M/K` に対し、idèle class norm
subgroup が一致することを目標とする。finite reciprocity と transfer infrastructure は既にある。

正規閉包、塔のnorm transitivity、有限Galois norm-residueのkernelは実装済みである。ここで
idèle-class normに対応する主写像は部分群包含が誘導するabelianization mapであり、transfer
imageではない。transferは逆向きのclass inclusionとの整合性および派生版に使う。

| ID | 予定 owner | source-producing endpoint | 完了判定 |
|---|---|---|---|
| D1 [done] | `GroupTheory.Quotient` | `Subgroup.comap_map_abelianization_eq_sup_commutator`、`Subgroup.quotientSupCommutatorEquivMapAbelianization`、`..._mk` | 前者は既存 `Subgroup.comap_map_eq` と `Abelianization.ker_of` の薄い specialization。追加仮定なしのquotient equivalenceと代表元評価を実質成果とする |
| D2 [done] | `AlgebraicNumberTheory.Galois.MaximalAbelianSubextension` | `finiteNormalClosureOriginalFixingSubgroup`、`finiteNormalClosureOriginalFixingSubgroupEquiv`、`finiteNormalClosureMaximalAbelianSubfield`、`..._isAbelianGalois`、`..._greatest` | `Gal(N/M) ≃ H` を型付き公開し、`fixedField (H ⊔ commutator G)` が元の体内の最大 Abelian Galois 部分体 |
| D3 [done] | `GlobalClassFieldTheory.Reciprocity.IntermediateNormAbelianization` | `globalNormResidueAbelianization_comp_ideleClassNorm_intermediate`、`..._range_eq_fixingSubgroup_image` | 非正規な中間体に対するordinary `ideleClassNorm K M` の自然性をfinite-tower norm providerから生成し、restriction / fixing-subgroup / surjective-compositeまで追加仮定なしで実装。provider 27s、consumer 8.1s、warning 0でgreen |
| D4 [done] | 同 owner | `ideleClassNorm_range_eq_artin_preimage_abelianizedFixingSubgroup` | finite reciprocity kernelとD3からnorm subgroupのpreimage表示を生成。同じconsumer leafのtargeted buildがwarning 0でgreen |
| D5 [done] | `GlobalClassFieldTheory.GlobalClassFields.NormLimitation` | `ideleClassNorm_range_eq_maximalAbelianSubfield`、`normLimitation` | D4をnormal closureとその最大Abelian部分体へ適用し、`finiteNormalClosureOriginalFieldEquiv` とnorm-range AlgEquiv transportで元の拡大へ戻す。任意有限拡大・両包含・Abelian Galois specializationを実装し、leafは10s、warning 0でgreen |
| D6 [done] | `GlobalClassFieldTheory.IdealClassFieldTheory.NormLimitation` | `idealNormSubgroup_eq_maximalAbelianSubfield`、`rayNormSubgroup_eq_maximalAbelianSubfield` | assumption-free ideal Artin kernel bridgeとD5からideal/ray norm subgroupの一致を実装。Statement / Core / public facadeを分離し、3 targetともwarning 0でgreen |

D3/D4 は結論と同値なrange equalityを仮定として渡さず、`N/M`のfinite reciprocity
surjectivityと非正規有限塔のordinary norm bridgeから像 equalityを生成してgreenになった。

### E. archimedean part を含む full conductor

full modulus の型は実装済みである。現 `Conductor.lean` が構成するのは
`ConductorialSubgroup` 上の narrow finite conductor である。一つの実場所を modulus から
除けることと、その一場所 idèle-class image が対象 subgroup に含まれることの同値は
実装済みである。archimedean local normとramificationの比較、full ray fieldへの一般embedding
criterionも既にある。

| ID | 予定 owner | endpoint | 完了判定 |
|---|---|---|---|
| E2a [done] | `GlobalClassFieldTheory.GlobalClassFields.ConductorInfinitePart` | `ConductorialSubgroup.fullConductorInfinitePart`、`fullConductorInfinitePart_subset_of_isDefiningModulus` | one-place class imageがsubgroupに入らない実場所のcanonical filter。choiceなし |
| E2b [done] | `AlgebraicNumberTheory.RayClass.FullModulus` と conductor owner | `RayClass.Modulus.eraseRealPlaces`、`eraseRealPlaces_isDefiningModulus_of_ranges_le` | 既存one-place iffをFinset inductionで反復 |
| E2c [done] | `GlobalClassFieldTheory.GlobalClassFields.ConductorInfinitePart` | `ConductorialSubgroup.fullConductor`、`fullConductor_isDefiningModulus`、`isDefiningModulus_iff_fullConductor_le` | finite partはliteralに`narrowFiniteConductor`、infinite partはE2a、全defining modulus中最小 |
| E3 [done] | `GlobalClassFieldTheory.GlobalClassFields.AbelianConductorExactness` | `ideleClassNormFullConductor_infinitePart_eq_realRamificationLocus` | one-place idèle-class norm membership、archimedean tensor norm、unramifiednessを接続し、full conductorの実場所部分を実分岐集合として同定 |
| E4 [done] | `GlobalClassFieldTheory.GlobalClassFields.FullConductorRayClassField` | `nonempty_algHom_to_rayClassField_iff_fullConductor_le` | 既存embedding iffとE2cの普遍性から導出。実proofを予定ownerへ移し、owner / aggregate closureは4992 / 4992 jobs、warning 0でgreen |

function-fieldへの将来拡張ではinfinite partが空になるspecializationとして再利用する。

### F. 基盤 API の hardening

`zHatToIntegerProfiniteCompletion`、有限商diagram、整数上の整合性、prime-product側の同型は
実装済みである。

| ID | 予定 owner | endpoint | 完了判定 |
|---|---|---|---|
| F1 [done] | `AbstractClassFieldTheory.Degree.ProfiniteIntegerFiniteQuotient` | `integerProfiniteCompletionToZHat`、`zHatContinuousAddEquivIntegerProfiniteCompletion` | 有限商射影が点を分離することから単射、整数像の稠密性とcompact/Hausdorffから全射を生成し、位相加法同型と逆写像を構成。新しいinjectivity/surjectivity仮定なし |
| F2 [done] | `AbstractClassFieldTheory.Reciprocity.ProfiniteAPI` | `ClassFormation.Profinite.normSubgroupOrderIso`、`ClassFormation.Profinite.classField`、`ClassFormation.Profinite.normResidueSymbol` | `P : ProfiniteGrp` を受け、`Profinite.classField` が同facadeのorder isomorphismを直接利用することで topology/compact/T2 instance列挙を削減。target buildも成功 |
| F3 [done] | public-contract tooling | reviewed choice boundary matrix の復旧と gate 統合 | final manifestを現source snapshotへ固定し、architecture、documentation、public API、choice、performance contractsを同一snapshotで検証済み |

F2で大量aliasやproof-field packageを作らない。主要endpointに限定し、generic fixed-field/topology
lemmaはdomain-specific consumerではなく一般ownerに置く。

## 現在の停止境界

公開releaseが確定するまでA--Fの追加実装は行わない。production folder、全directory
aggregate、README、LCFT import surface、static contracts、fresh production build、
証跡記録は完了した。残作業はGitHub CIと公開ホームページへの登録だけである。

退避したB3 finite-character / finite-support、B4、C2--C4の再開は別タスクとする。
退避物をrelease sourceへ自動復帰させず、再開時には依存DAGとAPI境界を改めて監査する。

## elaboration と性能の既知課題

### 根本原因

主因は broad `simp` や単純な物理行数ではなく、次の組合せである。

1. 一つの target が数百 module の大きな import closure を読む。
2. 同じ `Algebra`、`FiniteDimensional`、`NumberField`、`IsScalarTower` を別経路で構成する。
3. dependent quotient、fixed field、Galois group の endpoint がその instance proof を型に含む。
4. reducible wrapper が宣言 finalization で反復展開される。
5. consumer の巨大な `change` / `convert` が provider の raw endpoint を再照合する。

### 採用する境界

- provider に canonical instance path を一つ置く。
- 明示型または opaque な bridge を公開する。
- consumer には named character、actual Galois element、membership iff など最小の事実を渡す。
- 複数 endpoint が同じ dependent witnesses を使う場合は shared middle data を一度だけ構成する。
- helper 分割で timeout位置だけが移動したら、proof lengthではなく宣言型の defeq architecture を直す。
- generic high-priority instance を global 化して探索範囲を広げない。

### 残す性能台帳

| 領域 | 実測された症状 | 次に見る点 |
|---|---|---|
| selected-place cohomology | 旧単体は407s / 約4.2GB。新pipelineの個別実測は Action 65s、Equiv 12s、Tensor 8.5s、Inclusion 14s、EquivApply 7.7s、Induced 5.2s、Core 3.3s、Integral 13s、Chosen 21s、aggregate 3.5s。すべてgreen / warning 0 | 個別runの単純合計は約153s（約150s）。同一clean buildのwallではないため、並列効果やclean-wallとして報告しない |
| intrinsic fixed-field transport | 250--350秒級 | 多段 instance tower と raw fixed-field endpoint |
| global norm-residue naturality | 100秒超の宣言が複数 | providerへ移した semantic sections と typed transport の再利用 |
| rational finite norm transfer | 約4.5 GiB級 | named quotient zero、finite representative、relative membership の Data 境界 |
| small Hilbert / principal transfer | 100--300秒級 | absolute/relative fixed-field instance spine と shared norm data |

最終全体 build の結果で、現在も重い target だけを更新する。過去に重かったという理由だけで
green provider を再編集しない。

## 検証手順

production build:

```bash
cd <repository-root>
LEAN_NUM_THREADS=1 lake build ClassFieldTheory
```

exact trace:

```bash
python3 -B scripts/ClassFieldTheory/green_status.py \
  --probe-timeout 240 --json --list-no-green --list-frontier
```

static / public contracts:

```bash
python3 -B scripts/ClassFieldTheory/check_public_contracts.py
python3 -B scripts/ClassFieldTheory/check_documentation_contract.py
python3 -B scripts/ClassFieldTheory/check_architecture_contract.py
git diff --check
```

成功を記録するときは command、source snapshot、wall time、最大 RSS、error / warning、log pathを
同じ行に残す。source 編集をまたいだ build は診断資料であり、current green には加えない。

## 圧縮した実装履歴

### 2026-08-10: default-heartbeat baseline

- 一時 heartbeat / recursion override を解除。
- fresh build directory は `lakefile.toml` の設定に固定。
- Lake glob を anchor を暗黙要求しない形へ修正し、raw / unique とも実在1258 modules、
  unmatched 0、synthetic 0、duplicate 0を確認。
- fresh ordinary build は1175 / 1258まで進み、唯一の source rootを rational cyclotomic
  principal-prime transportへ限定。残83は reverse closureだった。

### 2026-08-10--11: provider canonicalization

- rational cyclotomic local Artin、fixed-field norm residue、ray norm、local-global compatibility、
  Hilbert tower、ideal Artin の各境界を canonical provider + typed bridge へ整理。
- `GlobalNormResidueNaturality` の semantic sectionを既存 providerへ移し、1258 module inventoryと
  公開名を維持したまま3000行 gateを回復。
- `PrincipalIdealTransfer` の旧absolute/relative transport再構成を
  `RationalFiniteNormTransfer` の公開 membership APIへ置換。
- public contracts は1258 modules、公開宣言の必須 docs欠落0、architecture cycle 0で成功。

### 2026-08-11: checkpoint と最終ゲート

- checkpoint commit `e0997fb2` を作成。
- `RationalFiniteNormTransfer` と直下 facadeをordinary warning 0でgreen化。
- exact 1251 / 1258、frontier 1から最終 `lake build ClassFieldTheory` を開始。
- 6個に分散していた Markdownを本 README と status の二層へ統合。

### 2026-08-11: 最初の post-green 拡張

- `InfiniteGlobalArtinDescent` を追加し、一般の principal-idèle消滅、idèle class groupへの
  連続降下、代表元での評価、dense rangeを実装。
- `LocalHilbertSymbolLaws` を追加し、local Hilbert characterのkernel equality、symbolが
  `1`であることのnorm-membership同値、norm quotientからの誘導写像の単射性を実装。
- 当時のinventory拡張後、両leaf、owner aggregate、全rootをordinary warning 0でbuild。
- 同一source snapshotでno-green 0、frontier 0、architecture cycle 0を確認。

### 2026-08-11: 無限次全射・無限素点 conductor・物理 layout

- 一般数体のpositive archimedean idèleを構成し、norm-one compactnessとdense imageから
  infinite global idèle-class Artin mapのsurjectivityを証明。
- defining modulusから一つの実場所を除去できることの必要十分条件を実装。
- 空 directoryを除去し、直下にLean fileが1本だけの19系統を既存aggregateへの統合または
  平坦化で解消。循環を避ける `NormCore` / `PrincipalCore` 境界を追加。
- 物理 directory検査をarchitecture contractへ追加し、rootから当時のproduction inventoryすべてへ到達、
  unresolved import 0、cycle 0を確認。

## 更新規則

1. exact 数値は process / source が安定した coherent traceだけで更新する。
2. prefix successをmodule greenと書かない。
3. provider edit後はreverse import closureをstaleと扱う。
4. 同じtargetまたは編集中providerを複数writerでbuildしない。
5. 独立laneの並行buildはtransitive import/output closureまで非交差か確認する。
6. warningはordinary build outputから数え、抑制せず原因を修正する。
7. 変動値をREADMEや別のdated auditへ複製しない。
