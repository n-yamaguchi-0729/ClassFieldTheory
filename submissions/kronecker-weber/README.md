# Kronecker–Weber：Palomar 提出準備

**準備中・未送信。** この nested package の Lean / Comparator / NanoDa 検査と
Palomar への提出・登録はまだ行っていません。

対象は `KroneckerWeber.exists_cyclotomicEmbedding` です。
有理数体上アーベル Galois な数体が、正の次数パラメータを持つ円分体へ
有理数代数として埋め込めることを述べます。数学的な新定理の主張ではありません。

## ファイルと依存

- `Challenge.lean`：Mathlib の語彙だけで元の定理と同名・同型の主張を置きます。
  意図した `sorry` は声明用の穴です。
- `Solution.lean`：`ClassFieldTheory.KroneckerWeber.Core` を直接 import し、
  既存の証明を供給します。Challenge を import してはいけません。
- `comparator.json`：上記の定理だけを指定。許可公理は
  `propext`・`Quot.sound`・`Classical.choice`、`enable_nanoda: true` です。
- `lakefile.toml`：Challenge と Solution を別ライブラリとし、
  `ClassFieldTheory` を同じリポジトリの `../..` から参照します。
- `formalization.yaml`：v0.4 の著者・対象・出典状況・AI 利用・レビュー記録です。
- `verification-pins.json`：確認時の公式検査器・スキーマの固定版です。

Lean は **4.33.0**。Mathlib は CFT 本体の固定 manifest から
`6f1ef4e5dd604a435bddba4747b13970cd65d2a1` を使います。
親リポジトリがこの版へ更新済みであることを、実行前に確認してください。

このディレクトリ自身の manifest は意図的に未生成です。
単一の同一リポジトリ内 path 依存だけを持つ TOML project は、依存先が
固定 manifest を持ち、そこに別の path 依存がない等の条件を満たす場合、
公式 [§6.3–§6.4](https://github.com/PalomarRegistry/PalomarPolicy/blob/4ed67de4fd69df383badb7857dff97e2fb734ab0/CONTRIBUTING.md#63-a-toml-project-without-its-own-manifest)
の例外を利用できます。条件変更時は正しい nested manifest を生成・検証・commit してください。
同じリポジトリに実質的な CFT 証明があるため、外部証明への thin wrapper として
架空の自己参照 commit を記載していません。ライセンスは root の
[Apache-2.0 LICENSE](../../LICENSE) が適用されます。

## 提出前の確認

1. 親 CFT の固定版・ソースコピー・CI を確定し、次をこのディレクトリで実行します。

   ```console
   lake build Challenge Solution
   ```

   Challenge の意図した声明用の穴と、Solution の証明検査を区別します。
2. 現行 hosted pipeline と同じ固定ツールで metadata と Comparator を検査します。
   NanoDa の有効化は提出側の要件です。既存 workspace の検査結果を、この package の
   比較成功や Palomar の機械検査成功として流用しません。
3. 著者・責任者は **Naganori Yamaguchi（山口永悟）**、GitHub は
   **n-yamaguchi-0729** と記載しています。
   [公開プロフィール](https://n-yamaguchi-0729.github.io/homepage-en.html)と
   [ライブラリの著者記録](https://n-yamaguchi-0729.github.io/YamaLean4Lib_pages/libraries/ClassFieldTheory/)
   に基づきます。具体的な依拠文献・版・定理番号、過去の AI モデル履歴・費用・
   所要時間・追加の謝辞は未記録です。責任者が出典と履歴を確認・補完してください。
   未検証の proof-status 件数をゼロとして埋めていません。
4. 最終的な公開 **40 桁 commit** と、その commit の CI・比較結果へのリンクを記録します。
   現時点では未確定です。実際の提出権限もこの時点で確認します。

## ユーザーが提出するとき

[公式提出ページ](https://submit.palomar-registry.org/)で、次を指定します。

- Repository：`n-yamaguchi-0729/ClassFieldTheory`
- Commit：確認済みの最終 40 桁 SHA
- Selected project：`submissions/kronecker-weber`
- Comparator：`submissions/kronecker-weber/comparator.json`
- Metadata：`submissions/kronecker-weber/formalization.yaml`

機械検査後の editorial review を確認し、**登録は別の操作**として判断します。
この準備作業では intake の送信、外部メッセージ、登録操作を行っていません。

[公式提出案内](https://palomar-registry.org/how-to-submit) ·
[固定 template](https://github.com/PalomarRegistry/PalomarTemplate/tree/128a6c5ce5f48622e69927ccd639cbff401022e8) ·
[固定 hosted verifier](https://github.com/PalomarRegistry/PalomarSubmission/tree/c605f23466450a52999fcfb3c6d68ed8febc56bf)
