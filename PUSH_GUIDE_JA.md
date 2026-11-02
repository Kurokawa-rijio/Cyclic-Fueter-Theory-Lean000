# GitHub への push 手順

このフォルダーが Lean プロジェクトのルートです。`lakefile.lean` と
`lean-toolchain` がこの階層にあることを確認してください。

## 依存関係の固定（任意）

Lean 4 と Lake がすでに使える場合は、PowerShell からプロジェクトのルートへ
移動して次を実行すると、依存関係を固定する `lake-manifest.json` ができます。

```powershell
cd "C:\Users\ryoji\Documents\Codex\2026-10-25\t\work\CyclicFueterTheory_Lean"
lake update
```

生成したファイルも Git に追加すると、依存バージョンを固定できます。
Lean/Lake をまだ用意していない場合は、この手順を飛ばして先に push できます。
GitHub Actions が初回実行時に依存関係を解決します。ローカルでビルド確認を
する場合は、依存関係を固定した後に続けて次を実行します。

```powershell
lake exe cache get
lake build
```

## GitHub に push

GitHub 上で空のリポジトリを作成します。初回は GitHub 側で README や
`.gitignore` を追加せず、このフォルダーの内容をそのまま初期 commit にします。

GitHub Desktop を使う場合は、`File` → `Add Local Repository` からこの
フォルダーを選び、リポジトリとして作成して commit した後、`Publish repository`
を選びます。

Git をコマンドで使う場合は、プロジェクトルートで次を実行します。

```powershell
git init
git add .
git commit -m "Initial Lean formalization"
git branch -M main
git remote add origin https://github.com/<ユーザー名>/<リポジトリ名>.git
git push -u origin main
```

`.github/workflows/lean.yml` が push 時に Lean ツールチェーンを用意し、
依存関係の解決、Mathlib キャッシュ取得、`lake build` を順に実行します。

## 現在の検証状況

この作業環境には Lean/Lake がないため、Lean ファイルはまだコンパイルされて
いません。CI が失敗した場合は GitHub Actions の最初の Lean エラーから修正し、
再 push してください。現時点では、コンパイルが通った証明として引用・公開しないで
ください。

元資料の PDF はこのプロジェクトには含めていません。Lean ソースの依存先は
`lakefile.lean` に記載した Mathlib です。
