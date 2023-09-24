FROM racket/racket:8.10-full

RUN apt-get update
RUN apt-get install -y curl git libc6

ENV ELAN_HOME=/usr/local/elan \
    PATH=/usr/local/elan/bin:/app/build/bin:$PATH \
    LEAN_VERSION=leanprover/lean4:v4.0.0

RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --no-modify-path --default-toolchain $LEAN_VERSION; \
    chmod -R a+w $ELAN_HOME; \
    elan --version; \
    lean --version; \
    leanc --version; \
    lake --version;

COPY . /app/

WORKDIR /app

RUN lake build
CMD sleep 9999999
CMD rinhac /var/rinha/source.rinha.json -o source && ./source
