# Specification of Barrier implementation
## How to run

1. download tla2tools (https://github.com/tlaplus/tlaplus/releases)

2. Translate PlusCal to TLA+
```bash
java -cp tla2tools.jar pcal.trans barrier.tla
```

3. Run TLC
```bash
java -jar tla2tools.jar -config barrier.cfg barrier.tla
```