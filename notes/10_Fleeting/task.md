Oracleからスキーマ情報を抽出し、AIでの活用やローカルでのメタデータ管理を行うための最適な手順を解説します。

まず、SQLiteとDuckDBの選択についてですが、今回の用途（スキーマ管理・AIへのコンテキスト提供）であれば **DuckDB** をおすすめします。

---

## 1. SQLite vs DuckDB (Oracleスキーマ管理用)

| 比較項目 | SQLite | DuckDB (推奨) |
| :--- | :--- | :--- |
| **型システムの柔軟性** | 緩い（型を無視しやすい） | **厳密（型チェックが強い）** |
| **Oracleとの相性** | シンプルすぎて型変換が必要 | **標準SQLに近く、多様な型に対応** |
| **AIとの親和性** | 非常に高い（一般的） | 高い（構造化データの分析に強い） |
| **メタデータの扱い** | 普通 | **JSONやParquet連携が強力** |

**DuckDBを推す理由:**
DuckDBはPostgreSQLに近い挙動を示し、データ型が豊富です。Oracleの複雑な型（NUMBER, DATE, TIMESTAMP等）をローカルに再現してAIに食わせる際、DuckDBの方がセマンティクスを維持しやすいためです。

---

## 2. A5:SQL Mk-2でのDDL一括出力手順

AIに渡すための「種」となるDDL（CREATE TABLE文）を抽出します。

1.  **「データベース」メニュー** ＞ **「DDLの生成」** を選択。
2.  **対象オブジェクト:** 「テーブル」にチェックを入れ、出力したいテーブルをすべて選択します。
3.  **オプション設定 (重要):**
    * **「論理名をコメントとして出力する」** に必ずチェックを入れてください。AIは物理名（`USR_ID`）より論理名（`ユーザーID`）がある方が圧倒的に理解が深まります。
    * 「Drop文を出力する」は不要なので外します。
4.  **出力:** 「ファイルへ保存」または「クリップボードへコピー」を実行します。

---

## 3. AIに読み込ませる・ローカルDBへ入れる際のTips

### AI（LLM）への渡し方
出力されたDDLをそのまま渡すのも良いですが、以下の形式でMarkdownにまとめるとAIの理解度が向上します。

> **プロンプト例:**
> 「以下のOracle DDLを読み取ってください。各カラムのコメント（論理名）を重視して、ER図の構造を把握してください。今後、この構造に基づいてSQLを生成してもらいます。」
> ```sql
> -- ここにA5M2で出力したDDLを貼る
> ```

### DuckDBへの取り込み
OracleのDDLはそのままではDuckDBで動かない場合があります（`NUMBER` 型や `VARCHAR2` など）。
* **AIに変換させる:** 「このOracle用DDLをDuckDBで動くように変換して」と依頼するのが最も速いです。
* **DuckDBにテーブル定義だけ入れる:** 変換後のSQLをDuckDBで実行すれば、`information_schema` を通じてテーブル構造をSQLで検索できるようになります。

---

「サーチと修正」を極めるための、2026年最新のMCP（Model Context Protocol）ツール定義スキーマを構成しました。

独自設計の肝となる「確信度」「ソースコード断片」「トレースID」を、AIが扱いやすい形で構造化しています。

---

## 1. ツール定義スキーマ（リクエスト側）

AIがツールを呼び出す際に、**「誰が（トレースID）」「どこを（パス）」**調べるかを定義します。

```json
{
  "name": "rigorous_symbol_analysis",
  "description": "Tree-sitterを用いてコードを物理解析します。AIの推測よりもこのツールの結果を優先してください。",
  "inputSchema": {
    "type": "object",
    "properties": {
      "traceId": {
        "type": "string",
        "description": "一連の調査セッションを追跡するためのユニークID（例: UUID）"
      },
      "filePath": {
        "type": "string",
        "description": "解析対象のソースファイルパス"
      },
      "symbolName": {
        "type": "string",
        "description": "検証・抽出したいシンボル名（メソッド、クラス、変数名）"
      },
      "includeSource": {
        "type": "boolean",
        "description": "修正の材料としてソースコードの断片を取得するかどうか"
      }
    },
    "required": ["traceId", "filePath", "symbolName"]
  }
}
```

---

## 2. レスポンススキーマ（結果側）

Java 23側で解析した「真実」をAIに返します。ここでのポイントは、自然言語の `text` だけでなく、**`structuredContent`** に判断材料を凝縮させることです。

```json
{
  "content": [
    {
      "type": "text",
      "text": "[Trace: ${traceId}] シンボル '${symbolName}' の物理解析を完了しました。"
    }
  ],
  "structuredContent": {
    "verification": {
      "confidenceScore": 1.0,
      "reliabilityReason": "Tree-sitterによるAST完全一致。ハルシネーションの可能性なし。",
      "astPath": "source_file > class_body > method_declaration"
    },
    "codeArtifacts": {
      "snippet": "public void validate() {\n    // 実際のコード内容\n}",
      "startLine": 42,
      "endLine": 45,
      "language": "java"
    },
    "sessionContext": {
      "traceId": "uuid-1234-5678",
      "timestamp": "2026-03-17T12:00:00Z"
    }
  }
}
```



---

## 3. このスキーマが強固にするポイント

### ① 確信度スコア (`confidenceScore`)
* **1.0**: ASTで完全に実在を確認。
* **0.7**: 同名シンボルがあるが、引数型が異なる可能性。
* **0.0**: 物理的に存在しない（AIに「君の記憶は間違っている」と突きつける指標）。

### ② ソースコードの断片 (`snippet`)
AIにファイル全体を読ませるのではなく、Tree-sitterが特定した**「修正すべきノードの範囲だけ」**を切り出して返します。これによりAIの消費トークンを抑えつつ、修正の精度を劇的に向上させます。

### ③ トレースID (`traceId`)
マルチエージェント（複数のAIが同時に動く環境）で、どのエージェントがどの論理パスを調査しているかをJava側で紐付けます。ログ分析や、後で「なぜこの修正をしたか」の根拠を遡る際のキーになります。

---
