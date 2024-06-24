# Use Docker

Build and execute.

```text
(host)$ docker compose build
(host)$ docker compose up -d
```

Attach.

```text
(host)$ docker exec -it  docker-awkernel-image-1 /bin/zsh
```

Compile.

```text
(docker)$ make aarch64 BSP=aarch64_virt
```
