# GitHub への push 手順

このフォルダーが Lean プロジェクトのルートです。`lakefile.lean` と
`lean-toolchain` がこの階層にあることを確認してください。

## 依存関係とローカルビルド

Lean 4 と Lake がすでに使える場合は、PowerShell からプロジェクトのルートへ
移動し、必要なら次を実行して依存関係を再解決できます。現在のプロジェクトには
依存バージョンを固定する `lake-manifest.json` を含めています。

```powershell
cd "C:\Users\ryoji\Documents\Codex\2026-10-25\t\work\CyclicFueterTheory_Lean"
lake update
```

Mathlib キャッシュを取得してビルドするには、プロジェクトルートで次を実行します。

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

このプロジェクトは Lean 4.35.0 でローカルビルド済みです。2026-11-02 の確認で
ルートの `CyclicFueterTheory` を含む `lake build` が成功しました。GitHub に push
した後は Actions の結果も確認してください。失敗した場合はログの最初の Lean
エラーから修正します。

元資料の PDF はこのプロジェクトには含めていません。Lean ソースの依存先は
`lakefile.lean` に記載した Mathlib です。
