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

---

## 8. テスト手法

### 8.1 テスト環境の構成

現状のプロジェクトは `make qemu-x86_64-net` で QEMU を直接起動し、
ホスト↔ゲスト間の通信のみをテストしている。ここでは **VM 間通信** と
**多数コネクション負荷テスト** を可能にするため、libvirt/KVM を用いた
2-VM 構成を追加する。

```
Host Machine (libvirt / KVM)
├── virbr-awk  (NAT bridge, 192.168.100.0/24)  ← virsh net-define
├── VM: awkernel   (awkernel カーネル, QEMU/KVM, OVMF)
│   ├── vnet0: e1000e,  192.168.100.10
│   └── vnet1: virtio,  192.168.100.11
└── VM: counterpart  (Fedora/Ubuntu, iperf3 / netperf サーバ)
    └── vnet0: 192.168.100.2
```

`awkernel` 側のネットワーク設定は既存の QEMU 引数と同じ
（e1000e + virtio-net-pci、MAC アドレスは Makefile の値を維持）。

---

### 8.2 環境セットアップ

#### 8.2.1 仮想ネットワーク定義

```xml
<!-- awkernel-net.xml -->
<network>
  <name>virbr-awk</name>
  <forward mode='nat'/>
  <bridge name='virbr-awk' stp='on' delay='0'/>
  <ip address='192.168.100.1' netmask='255.255.255.0'>
    <dhcp>
      <range start='192.168.100.2' end='192.168.100.254'/>
    </dhcp>
  </ip>
</network>
```

```bash
virsh net-define awkernel-net.xml
virsh net-start  virbr-awk
virsh net-autostart virbr-awk
virsh net-list --all          # 起動確認
```

#### 8.2.2 カウンタパート VM の作成

```bash
# Fedora/Ubuntu など標準 Linux を 1 台用意する
virt-install \
  --name counterpart \
  --memory 2048 --vcpus 2 \
  --os-variant fedora40 \
  --network network=virbr-awk,model=virtio \
  --disk path=/var/lib/libvirt/images/counterpart.qcow2,size=20,format=qcow2 \
  --location /path/to/fedora.iso \
  --extra-args 'console=ttyS0' \
  --nographics --noautoconsole

virsh start   counterpart
virsh console counterpart    # インストール後にログイン
# インストール完了後
sudo dnf install -y iperf3 netperf nc   # または apt install
```

#### 8.2.3 awkernel VM の定義

Makefile の QEMU 引数を virsh の `<domain>` XML に変換して登録する。
NIC を既存の QEMU usermode ネットワークから `virbr-awk` ブリッジに切り替える。

```xml
<!-- awkernel-vm.xml (x86_64 UEFI の場合の骨子) -->
<domain type='kvm'>
  <name>awkernel</name>
  <memory unit='GiB'>4</memory>
  <vcpu>16</vcpu>
  <os>
    <type arch='x86_64' machine='q35'>hvm</type>
    <loader readonly='yes' type='pflash'>/usr/share/OVMF/OVMF_CODE.fd</loader>
    <nvram>/var/lib/libvirt/qemu/nvram/awkernel_VARS.fd</nvram>
  </os>
  <cpu mode='host-passthrough'/>
  <devices>
    <!-- awkernel イメージ -->
    <disk type='file' device='disk'>
      <driver name='qemu' type='raw'/>
      <source file='/path/to/x86_64_uefi.img'/>
      <target dev='sda' bus='sata'/>
    </disk>
    <!-- NIC 1: e1000e (net0) -->
    <interface type='network'>
      <source network='virbr-awk'/>
      <model type='e1000e'/>
      <mac address='12:34:56:11:22:33'/>
    </interface>
    <!-- NIC 2: virtio (net1) -->
    <interface type='network'>
      <source network='virbr-awk'/>
      <model type='virtio'/>
      <mac address='12:34:56:11:22:34'/>
    </interface>
    <serial type='pty'><target port='0'/></serial>
    <console type='pty'><target type='serial' port='0'/></console>
  </devices>
</domain>
```

```bash
virsh define  awkernel-vm.xml
virsh start   awkernel
virsh console awkernel          # シリアルコンソールでカーネルログ確認
```

#### 8.2.4 VM の停止・削除

```bash
virsh destroy   awkernel        # 強制停止
virsh destroy   counterpart
virsh undefine  awkernel        # 定義削除
virsh undefine  counterpart
virsh net-destroy   virbr-awk
virsh net-undefine  virbr-awk
```

---

### 8.3 テスト項目

| # | テスト名 | 目的 | ツール | 計測値 |
|---|---|---|---|---|
| T1 | 基本疎通確認 | TCP/UDP が到達すること | nc, ping | 成功/失敗 |
| T2 | UDP スループット | NET_MANAGER 改善前後の比較 | iperf3 -u | Gbps |
| T3 | TCP スループット | socket_set 競合改善の確認 | iperf3 | Gbps |
| T4 | 並列 TCP 接続 | 多数コネクション時スケーリング | iperf3 -P N | Gbps, CPU% |
| T5 | 接続確立レート | Phase 1 前後の比較 | netperf TCP_CRR | conn/s |
| T6 | リクエスト/レスポンス RTT | Phase 3 前後の比較 | netperf TCP_RR | μs |
| T7 | パケットキャプチャ解析 | ロスト・再送の確認 | tcpdump, tshark | ロス率% |
| T8 | PCAP ベースの手動確認 | awkernel 側パケット検査 | 既存 filter-dump | - |

---

### 8.4 テストコマンド詳細

#### 基本疎通 (T1)

```bash
# counterpart VM 上
nc -l -p 9000                               # TCP リスナー
nc -u -l -p 9001                            # UDP リスナー

# ホストから awkernel を経由した疎通確認（awkernel がエコーを返す場合）
nc 192.168.100.10 26099
echo "hello" | nc -u 192.168.100.10 26099
```

#### UDP スループット (T2)

```bash
# counterpart VM でサーバ起動
iperf3 -s

# ホストまたは counterpart から awkernel 向けに送信
iperf3 -c 192.168.100.10 -u -b 0 -t 30 -l 1400   # 帯域無制限, 30 秒
iperf3 -c 192.168.100.10 -u -b 0 -t 30 -P 32     # 32 並列ストリーム
```

#### TCP スループット・並列接続 (T3, T4)

```bash
# counterpart VM でサーバ起動
iperf3 -s -p 5201

# N 並列 TCP ストリーム
for N in 1 4 8 16 32 64 128; do
  echo "=== -P $N ==="
  iperf3 -c 192.168.100.10 -p 5201 -P $N -t 30 -J \
    | tee result_tcp_P${N}.json
done
```

#### 接続確立レート (T5) — Phase 1 比較に重要

```bash
# counterpart VM で netperf サーバ起動
netserver -p 12865

# TCP 接続生成レートの計測（30 秒間）
netperf -H 192.168.100.10 -p 12865 -t TCP_CRR -l 30 -- -r 1,1
```

期待値: Phase 1 適用後は Phase 0 比 **2〜4 倍**の接続/秒を記録する。

#### RTT レイテンシ (T6) — Phase 3 比較に重要

```bash
netperf -H 192.168.100.10 -p 12865 -t TCP_RR -l 30 -- -r 64,64
```

#### パケットキャプチャ (T7, T8)

```bash
# awkernel VM は QEMU filter-dump で自動キャプチャ済み
# counterpart 側で補足する場合
virsh domifstat counterpart vnet0   # パケット統計
virsh qemu-monitor-command awkernel --hmp \
  'info network'                    # QEMU ネットワーク状態確認

# キャプチャ解析
tcpdump -vvv -XXnr packets_net0.pcap | head -100
tshark -r packets_net0.pcap -z io,stat,1 "tcp"   # 1 秒ごとの TCP 統計
```

---

### 8.5 ベースライン取得手順

各フェーズの実装前に必ずベースラインを記録する。

```bash
#!/bin/bash
# baseline.sh — 変更前に実行してベースライン保存
DATE=$(date +%Y%m%d_%H%M%S)
DIR="bench_baseline_${DATE}"
mkdir -p $DIR

# T3: TCP スループット
iperf3 -c 192.168.100.10 -p 5201 -t 30 -J > $DIR/tcp_single.json

# T4: 並列 TCP
for N in 4 16 64; do
  iperf3 -c 192.168.100.10 -p 5201 -P $N -t 30 -J > $DIR/tcp_P${N}.json
done

# T5: 接続確立レート
netperf -H 192.168.100.10 -p 12865 -t TCP_CRR -l 30 -- -r 1,1 \
  > $DIR/tcp_crr.txt

# T6: RTT
netperf -H 192.168.100.10 -p 12865 -t TCP_RR -l 30 -- -r 64,64 \
  > $DIR/tcp_rr.txt

echo "Baseline saved to $DIR"
```

フェーズ実装後に同スクリプトを `bench_after_phaseN_${DATE}` として再実行し、
数値を比較する。

---

### 8.6 フェーズ別テスト手順

#### Pre-Phase（バグ修正）後

```bash
# ポート割り当てが正しく動作することを確認
# 1. 64 並列 TCP 接続を確立し、全て成功することを確認
iperf3 -c 192.168.100.10 -p 5201 -P 64 -t 10
# 2. エフェメラルポート番号が想定範囲内かシリアルコンソールで確認
virsh console awkernel
```

#### Phase 1（PortAllocator 分離）後

```bash
# T5: 接続確立レートがベースライン比 2 倍以上であることを確認
netperf -H 192.168.100.10 -p 12865 -t TCP_CRR -l 30 -- -r 1,1
# T4: 64 並列接続でのスループットがベースライン比 1.5 倍以上
iperf3 -c 192.168.100.10 -p 5201 -P 64 -t 30 -J
```

#### Phase 2（IfNetInner 分割）後

```bash
# マルチキャスト join/leave 中にデータ転送が止まらないことを確認
# 別ターミナルで転送継続
iperf3 -c 192.168.100.10 -p 5201 -t 60 &
# awkernel コンソールでマルチキャスト join/leave を繰り返す
virsh console awkernel
# iperf3 のスループットが join/leave 中も維持されていることを確認
```

#### Phase 3（二重ロック解消・Drop キュー）後

```bash
# T6: RTT がベースライン比 改善していることを確認
netperf -H 192.168.100.10 -p 12865 -t TCP_RR -l 30 -- -r 64,64
# 接続破棄集中テスト: 短命コネクションを高レートで生成
for i in $(seq 1 1000); do
  nc -z 192.168.100.10 26099 &
done
wait
# iperf3 の転送が阻害されていないことを並行確認
```

#### Phase 4（per-iface スケールアウト）後

```bash
# 複数インターフェース経由の並列転送
iperf3 -c 192.168.100.10 -p 5201 -P 32 -t 30 -J &  # net0 経由
iperf3 -c 192.168.100.11 -p 5201 -P 32 -t 30 -J &  # net1 経由
wait
# 合算スループットが単独 NIC の 2 倍近いことを確認
```

---

### 8.7 既存テストとの併用

上記 VM テストは既存のテスト体系を置き換えるものではなく、補完する。

| テスト種別 | 用途 | 実行タイミング |
|---|---|---|
| `make test` | 単体テスト（ロック・データ構造） | 毎コミット (CI) |
| SPIN モデル検証 (`make run` in specification/) | ポーリングアルゴリズムの正しさ | Phase 4.2 実装前後 |
| `make qemu-x86_64-net` + `scripts/udp.py` | 基本 UDP/TCP 疎通 | 各フェーズの動作確認 |
| VM テスト (本セクション) | 多数コネクション負荷・スループット計測 | フェーズ前後のベースライン比較 |
