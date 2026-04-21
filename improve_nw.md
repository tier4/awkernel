# ネットワークスタック改善ロードマップ

## 1. 概要

awkernel の TCP/UDP ネットワークスタックは、多数のコネクションを同時処理する際に
グローバルな `RwLock` 書き込みロックがボトルネックとなる。

ソケット生成・ポート割り当て・ソケット破棄のたびに `NET_MANAGER` グローバルロックを
取得するため、並列度が上がるほどスループットが頭打ちになる。本文書では問題箇所を
優先度順に整理し、段階的な改善フェーズを定義する。

---

## 2. 現状のロック構造

### 2.1 グローバル静的変数

```
net.rs
├── NET_MANAGER: RwLock<NetManager>
│   ├── interfaces: BTreeMap<u64, Arc<IfNet>>
│   ├── interface_id: u64
│   ├── tcp_ports_ipv4: BTreeMap<u16, u64>   (port → 参照カウント)
│   ├── tcp_port_ipv4_ephemeral: u16
│   ├── udp_ports_ipv4: BTreeSet<u16>
│   ├── udp_port_ipv4_ephemeral: u16
│   └── ... (IPv6 も同様)
├── IRQ_WAKERS: Mutex<BTreeMap<u16, IRQWaker>>
└── POLL_WAKERS: Mutex<BTreeMap<u64, IRQWaker>>

tcp_stream_no_std.rs
└── CLOSED_CONNECTIONS: Mutex<BTreeMap<u64, VecDeque<(SocketHandle, TcpPort)>>>

udp_socket_no_std.rs
└── NUM_MULTICAST_JOIN_IPV4: Mutex<BTreeMap<(u64, Ipv4Addr), usize>>
```

### 2.2 インターフェースごとの変数 (if_net.rs)

```
IfNet
├── inner: Mutex<IfNetInner>           ← LOCK #3
│   ├── interface: Interface           (smoltcp 本体)
│   ├── default_gateway_ipv4
│   ├── multicast_addr_ipv4: BTreeSet
│   └── multicast_addr_mac: BTreeMap
├── socket_set: RwLock<SocketSet>
├── tx_only_ringq: Vec<Mutex<RingQ>>   ← LOCK #2
└── rx_irq_to_driver: BTreeMap<u16, NetDriver>
    └── NetDriver::rx_ringq: Mutex<RingQ>  ← LOCK #1
```

### 2.3 ドキュメント化されたロック順序

```
1. NetDriver::rx_ringq
2. IfNet::tx_ringq  (tx_only_ringq[i])
3. IfNet::inner
```

### 2.4 主要パスのロック取得チェーン

**TCP 接続確立 (connect)**
```
NET_MANAGER.write()       ← グローバル書き込みロック (ポート確保)
  IfNet::inner.lock()     ← interface.poll 用
    IfNet::socket_set.write()  ← ソケット追加
```

**TCP/UDP データ送受信**
```
NET_MANAGER.read()
  socket_set.read()
    socket.lock()  (MCS ロック)
```

**ポーリング (poll_rx_tx)**
```
rx_ringq.lock()    ← パケット受信バッファ
  tx_ringq.lock()  ← パケット送信バッファ
    inner.lock()   ← interface.poll() 実行
```

---

## 3. 特定されたボトルネック

### 優先度一覧

| 優先度 | 場所 | ロック種別 | 問題 |
|---|---|---|---|
| CRITICAL | `net.rs:NET_MANAGER` | `RwLock::write()` | 全 TCP/UDP 接続確立がグローバル書き込みロックを取得。エフェメラルポート探索は最悪 O(16384) 反復しながらロック保持 |
| CRITICAL | `net.rs:get_ephemeral_port_tcp_ipv4` | 同上 | `entry(i)` (ループインデックス) で検索するバグ。正しくは `entry(port)` |
| HIGH | `if_net.rs:IfNet::inner` | `Mutex::lock()` | `interface.poll()` 呼び出し全体でロック保持。複数コアが同一インターフェースをポーリングするとシリアライズ |
| HIGH | `if_net.rs:IfNet::socket_set` | `RwLock::write()` | ソケット追加・削除で書き込みロック。接続レートが高いと write lock 競合が多発 |
| MEDIUM | `tcp_stream_no_std.rs:CLOSED_CONNECTIONS` | `Mutex::lock()` | グローバル Mutex。Drop ハンドラで毎回取得 |
| MEDIUM | `tcp_stream_no_std.rs:connect()` | 二重ロック | `inner.lock()` 保持中に `socket_set.write()` を取得。ドキュメントのロック順序に反する |

### 3.1 NET_MANAGER グローバル書き込みロック (CRITICAL)

`TcpStream::connect`、`TcpListener::bind_on_interface`、`TcpListener::accept`（2 回）、
`UdpSocket::bind_on_interface`、`UdpSocket::drop`、`TcpPort::drop` がすべて
`NET_MANAGER.write()` を取得する。

多数のコネクションが並行して確立・破棄されると、全スレッドがこの単一ロックで
逐次化される。

### 3.2 エフェメラルポート探索バグ (CRITICAL)

`net.rs` 内の `get_ephemeral_port_tcp_ipv4`（および IPv6 版）は次のような実装になっている。

```rust
for i in 0..(u16::MAX >> 2) {
    let port = self.tcp_port_ipv4_ephemeral.wrapping_add(i);
    let entry = self.tcp_ports_ipv4.entry(i);  // ← バグ: entry(port) が正しい
    ...
}
```

ループインデックス `i` でキーを検索しているため、ポートの空き判定が正しく動作しない。
`NET_MANAGER.write()` を保持したまま最悪 16384 回反復するため、パフォーマンス上も問題。

### 3.3 IfNet::inner のポーリング中ロック保持 (HIGH)

`poll_rx_tx` / `poll_tx_only` はいずれも `inner.lock()` を保持したまま
`interface.poll()` を呼ぶ。smoltcp の `Interface::poll` はパケット処理・TCP 状態機械
更新など相当量の作業を行うため、同一インターフェースの別ポーリングスレッドが
ロック待ちとなる。

さらに `IfNetInner` はポーリングに不要なマルチキャスト状態
（`multicast_addr_ipv4`、`multicast_addr_mac`）も同一 Mutex に含めているため、
マルチキャスト操作がポーリングを遅延させる。

### 3.4 socket_set 書き込みロックの競合 (HIGH)

ソケット追加（connect/bind/accept）・削除（drop）は `socket_set.write()` を必要とする。
これは全既存ソケットの `socket_set.read()` を保持しているスレッドをブロックする。
高接続レートではデータ転送が接続確立によって阻害される。

### 3.5 CLOSED_CONNECTIONS グローバル Mutex (MEDIUM)

`TcpStream::Drop` が毎回 `CLOSED_CONNECTIONS.lock()` を取得する。
接続破棄が集中するとグローバル Mutex で逐次化される。

### 3.6 connect() の二重ロック (MEDIUM)

`TcpStream::connect` では `inner.lock()` を保持したまま `socket_set.write()` を取得する。
`socket.connect()` に `interface.context()` を渡す必要があるためだが、
これによりロック順序（inner → socket_set）がドキュメントと逆になっている。

---

## 4. ロードマップ

### Pre-Phase: バグ修正（即日対応）

**変更内容:** `entry(i)` → `entry(port)` の修正

**対象ファイル:**
- `awkernel_lib/src/net.rs`
  - `get_ephemeral_port_tcp_ipv4` 内の `self.tcp_ports_ipv4.entry(i)` → `entry(port)`
  - `get_ephemeral_port_tcp_ipv6` 内の同様の箇所

**効果:** 正確なポート空き判定が可能になる。ポート探索が O(1) に近づく（
既使用ポートが少ない通常ケース）。

**リスク:** 低。1 行修正。

---

### Phase 1: PortAllocator 分離 — NET_MANAGER 書き込みロック除去

**目的:** ポート割り当て・解放操作を `NET_MANAGER` から分離し、
グローバル書き込みロックをホットパスから除去する。

#### 1.1 PortAllocator 新設

`NetManager` からポート関連フィールドをすべて抽出し、独立した構造体に移動する。

```rust
// 新設: awkernel_lib/src/net/port_alloc.rs
pub struct PortAllocator {
    tcp_ipv4: Mutex<BTreeMap<u16, u64>>,
    tcp_ipv4_ephemeral: AtomicU16,
    tcp_ipv6: Mutex<BTreeMap<u16, u64>>,
    tcp_ipv6_ephemeral: AtomicU16,
    udp_ipv4: Mutex<BTreeSet<u16>>,
    udp_ipv4_ephemeral: AtomicU16,
    udp_ipv6: Mutex<BTreeSet<u16>>,
    udp_ipv6_ephemeral: AtomicU16,
}

static PORT_ALLOC: PortAllocator = PortAllocator::new();
```

エフェメラルカーソルは `AtomicU16::fetch_add` で前進させる（ロック不要）。
実際のポート占有確認・挿入は各プロトコルの個別 Mutex だけを取得する。

これにより 4 つのプロトコル名前空間が独立し、TCP IPv4 の割り当てが
TCP IPv6 や UDP をブロックしない。

**変更対象ファイル:**
- `awkernel_lib/src/net.rs` — `NetManager` からポートフィールドを削除
- `awkernel_lib/src/net/port_alloc.rs` — 新規作成
- `awkernel_lib/src/net/tcp_stream/tcp_stream_no_std.rs` — `NET_MANAGER.write()` → `PORT_ALLOC` 呼び出し
- `awkernel_lib/src/net/tcp_listener/tcp_listener_no_std.rs` — 同様（accept 内の 2 箇所含む）
- `awkernel_lib/src/net/udp_socket/udp_socket_no_std.rs` — 同様
- `awkernel_lib/src/net/tcp.rs` — `TcpPort::drop` 内の `NET_MANAGER.write()` → `PORT_ALLOC`

**期待効果:**
- N スレッドが並行して接続確立する際、グローバル書き込みロック待ちがなくなる
- `NET_MANAGER` はインターフェース参照取得の読み込みロックのみになる
- 接続確立スループットがコア数に対しほぼ線形スケール

**リスク:** 中。`TcpPort::drop` のポート参照解放先変更に注意。

#### 1.2 NET_MANAGER の読み取り専用化確認

Phase 1.1 完了後、`NET_MANAGER.write()` の残存箇所を監査し、
`add_interface`（初期化パス）以外に書き込みロックがないことを確認する。

**変更対象ファイル:** `net.rs`（コード変更なし、確認のみ）

---

### Phase 2: IfNetInner 分割 — ポーリングとマルチキャストの分離

**目的:** `IfNet::inner` ロックの保持時間を短縮し、マルチキャスト操作が
ポーリングを遅延させないようにする。

#### 2.1 IfNetInner を IfNetCore と IfNetMulticast に分割

```rust
// 変更後
pub(super) struct IfNet {
    inner: Mutex<IfNetCore>,          // smoltcp Interface + ゲートウェイ
    multicast: Mutex<IfNetMulticast>, // マルチキャスト管理（独立）
    socket_set: RwLock<SocketSet>,
    ...
}

struct IfNetCore {
    interface: Interface,
    default_gateway_ipv4: Option<Ipv4Address>,
}

struct IfNetMulticast {
    multicast_addr_ipv4: BTreeSet<Ipv4Addr>,
    multicast_addr_mac: BTreeMap<[u8; 6], u32>,
}
```

`poll_rx_tx` / `poll_tx_only` は `inner.lock()` のみ取得し、
`multicast` は触れない。`join_multicast_v4` / `leave_multicast_v4` は
`multicast.lock()` のみ取得する。

**ロック順序の更新（ドキュメント要更新）:**
```
1. NetDriver::rx_ringq
2. IfNet::tx_ringq
3. IfNet::inner  (IfNetCore)
   ※ multicast は inner と同時に保持しない
```

**変更対象ファイル:**
- `awkernel_lib/src/net/if_net.rs` — 構造体分割、各メソッドの lock 先変更
- `awkernel_lib/src/net.rs` — `if_net.inner` でマルチキャスト参照している箇所を `if_net.multicast` に変更

**期待効果:**
- マルチキャスト操作中にポーリングが止まらなくなる
- `join_multicast_v4` / `leave_multicast_v4` がポーリングパスを阻害しない

**リスク:** 低〜中。smoltcp の `Interface::join_multicast_group()` は
`IfNetCore` 内の `interface` にアクセスするため、マルチキャストの smoltcp 側操作は
`inner.lock()` で、awkernel 側のブックキーピングは `multicast.lock()` で行う必要がある。
両方を同時保持しないよう注意（ロック順序ドキュメントを更新すること）。

**前提条件:** Phase 1

---

### Phase 3: 二重ロック解消・Drop キュー導入

#### 3.1 connect() の二重ロック修正

**現状:**
```rust
inner.lock() {
    socket_set.write() {      // ← inner を保持したまま write
        socket.connect(interface.context(), ...)
    }
}
```

`socket.connect()` が `interface.context()` を必要とするため `inner` を保持するが、
`socket_set.write()` は進行中の送受信（`socket_set.read()`）をブロックする。

**変更方針:**
`inner.lock()` を短命な読み取りに変えて、接続に必要な情報（ローカル IP アドレス、
現在時刻）だけを取り出してロック解放後に `socket_set.write()` を取得する。

```rust
// inner を短時間だけロックして必要情報を取り出す
let ctx = { inner.lock().extract_connect_context() };
// inner 解放後に socket_set を書き込みロック
socket_set.write().add(...);
socket.connect(ctx, ...);
```

smoltcp のフォーク版に `Interface::extract_connect_context()` または同等の
軽量アクセサを追加する。

**変更対象ファイル:**
- `awkernel_lib/src/net/tcp_stream/tcp_stream_no_std.rs`
- `awkernel_lib/smoltcp/src/iface/interface/mod.rs` — コンテキスト取り出しアクセサ追加

**期待効果:**
- connect 中に進行中の送受信がブロックされなくなる
- ロック順序がドキュメントと一致する

**リスク:** 中。smoltcp フォークへの変更を伴う。

#### 3.2 Drop キューによる socket_set.write() 遅延解放

**現状:** `TcpStream::Drop` が `socket_set.write()` を取得してソケットを即座に削除。
接続破棄が集中すると write lock がデータ転送をブロックする。

**変更方針:** `IfNet` にインターフェースごとの非同期削除キューを追加する。

```rust
pub(super) struct IfNet {
    ...
    drop_queue: Mutex<VecDeque<SocketHandle>>,  // 新規追加
}
```

`TcpStream::Drop` では `socket_set.write()` の代わりに `drop_queue` に
ハンドルを積む（`Mutex<VecDeque>` のロック取得のみ）。
既存の `tcp_garbage_collector`（100ms 周期）がキューを消費して
`socket_set.write()` でソケットを削除する。

`CLOSED_CONNECTIONS` グローバル Mutex の代替にもなる。
インターフェースごとに独立したキューなので、複数インターフェース間の
競合が生じない。

**変更対象ファイル:**
- `awkernel_lib/src/net/if_net.rs` — `drop_queue` フィールド追加、drain 処理追加
- `awkernel_lib/src/net/tcp_stream/tcp_stream_no_std.rs` — Drop を drop_queue push に変更
- `awkernel_services/src/network_service.rs` — `tcp_garbage_collector` を更新

**期待効果:**
- 接続破棄が集中しても `socket_set.write()` 競合が発生しない（GC レートに平滑化）
- `CLOSED_CONNECTIONS` グローバル Mutex のボトルネック解消

**リスク:** 低〜中。遅延削除のため、Drop 後 100ms 以内にハンドルが
再利用されないことを保証する必要がある（smoltcp の SocketSet はスロット再利用を
GC 後にのみ行うため問題なし）。

**前提条件:** Phase 2

---

### Phase 4: インターフェースごとのスケールアウト

#### 4.1 PortAllocator のインターフェースごとへの移動

Phase 1 で作成したグローバル `PORT_ALLOC` を `IfNet` 内に移動する。
TCP/UDP ソケットはすでに単一インターフェースに紐付いているため、
ポート名前空間をインターフェースごとに独立させることができる。

```rust
pub(super) struct IfNet {
    ...
    port_alloc: PortAllocator,  // グローバル PORT_ALLOC を廃止
}
```

`TcpPort::drop` はポート返却先インターフェースへの参照（`Weak<IfNet>`）を持つ必要がある。

**変更対象ファイル:**
- `awkernel_lib/src/net/if_net.rs` — `port_alloc` フィールド追加
- `awkernel_lib/src/net/tcp.rs` — `TcpPort` に `Weak<IfNet>` を追加
- `awkernel_lib/src/net/port_alloc.rs` — グローバル静的変数を削除

**期待効果:**
- 異なるインターフェース間でポート割り当て競合がゼロになる
- 複数 NIC 構成でポート確保スループットが NIC 数に比例してスケール

**リスク:** 中。`TcpPort` に `Weak<IfNet>` を持たせる設計変更。
インターフェース削除前にポートが解放される通常ケースでは問題ない。

**前提条件:** Phase 1、Phase 2

#### 4.2 マルチキュー RX のフェーズ分離ポーリング

複数の独立した RX キューを持つ NIC では、パケット受信（RX ドレイン）を
コアごとに並列実行し、smoltcp の `interface.poll()` のみ逐次化する
2 フェーズポーリングを導入する。

```
Phase A (並列, per-queue): hardware → rx_ringq  (rx_ringq.lock() のみ)
Phase B (逐次, per-iface): rx_ringq → interface.poll()  (inner.lock() が必要)
```

現在の `will_poll` AtomicUsize による協調排他を拡張し、Phase A と Phase B を
明示的に分離する。

**変更対象ファイル:**
- `awkernel_lib/src/net/if_net.rs` — `poll_rx_tx` のフェーズ分離リファクタリング

**注意:** SPIN モデル（`specification/awkernel_lib/src/net/if_net/if_net.pml`）の
LTL プロパティ（全パケットが最終的に送信される）をこのフェーズ変更に対して
再検証すること。実装前にモデルを更新し、`spin -a` で再チェックすること。

**期待効果:**
- 4 キュー NIC を 4 コアでポーリングする場合、RX 受信スループットが 4 倍近く向上
- `interface.poll()` のシリアライズ区間のみに競合を限定

**リスク:** 高。SPIN モデルの再検証が必要。Phase A/B の境界で
パケットの可視性保証を維持する必要がある。

**前提条件:** Phase 2（`IfNetCore` が分離済み）、Phase 3.1（二重ロック解消済み）

---

## 5. フェーズ依存関係

```
Pre-Phase (エフェメラルポートバグ修正)
    │
    ▼
Phase 1.1 (PortAllocator 分離)
    │
    ▼
Phase 1.2 (NET_MANAGER 読み取り専用化確認)
    │
    ▼
Phase 2.1 (IfNetInner → IfNetCore + IfNetMulticast)
    │
    ├──────────────────────┐
    ▼                      ▼
Phase 3.1               Phase 3.2
(connect 二重ロック解消) (Drop キュー導入)
    │                      │
    └──────────┬───────────┘
               ▼
          Phase 4.1                Phase 4.2
          (per-iface PortAllocator) (2 フェーズポーリング)
               │                       │
               └───────────┬───────────┘
                           ▼
                      (完全実装)
```

---

## 6. 各フェーズの期待効果

| フェーズ | 解消するボトルネック | 機構 | 期待効果 |
|---|---|---|---|
| Pre | ポート探索バグ | 1 行修正 | 正確性回復、探索 O(1) 化 |
| 1.1 | NET_MANAGER.write() 全接続逐次化 | AtomicU16 + 4 独立 Mutex | 並行接続確立がほぼ線形スケール |
| 1.2 | 残存 write lock 確認 | 監査のみ | 安全性確認 |
| 2.1 | inner lock がマルチキャストとポーリングを混在 | 構造体分割 | マルチキャスト操作がポーリングを阻害しない |
| 3.1 | connect の二重ロック | コンテキスト事前取り出し | connect 中も送受信が継続 |
| 3.2 | Drop 時の socket_set.write() 競合と CLOSED_CONNECTIONS | per-iface 遅延削除キュー | 接続破棄集中時も送受信が継続 |
| 4.1 | 複数 iface 間のポート割り当て競合 | per-iface PortAllocator | 複数 NIC 構成でポート確保が完全独立 |
| 4.2 | マルチキュー RX がシリアライズ | 2 フェーズポーリング | N キュー NIC で受信スループット N 倍近く改善 |

---

## 7. 変更しない不変条件

- **ロック順序:** rx_ringq → tx_ringq → inner (IfNetCore) の順序を全フェーズで維持する。
  `multicast` および `drop_queue` は葉ロックとし、`inner` と同時保持しない。
  各フェーズでロック順序コメント（`if_net.rs` 冒頭）を更新すること。

- **公開 API:** `TcpStream`、`UdpSocket`、`TcpListener`、`SockTcpStream`、
  `SockTcpListener`、`SockUdp` トレイトの型シグネチャを変更しない。

- **smoltcp フォーク変更の最小化:** Phase 3.1 のアクセサ追加、Phase 4.2 の
  ポーリング構造リファクタリングに限定する。それ以外のフェーズは awkernel 側のみ変更。

- **SPIN モデル:** Phase 4.2 の実装前に
  `specification/awkernel_lib/src/net/if_net/if_net.pml` の LTL プロパティを
  2 フェーズポーリングモデルに合わせて更新し、`spin -a` で再検証すること。

- **no_std 制約:** 全フェーズで `std` API に依存しない。追加する構造体は
  `Mutex`、`AtomicU16`、`BTreeMap`、`VecDeque` など no_std 互換の型のみ使用する。
