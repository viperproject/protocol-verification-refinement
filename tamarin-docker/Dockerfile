FROM debian:bookworm-slim@sha256:df52e55e3361a81ac1bead266f3373ee55d29aa50cf0975d440c2be3483d8ed3
# note that trixie does not have `libtinfo5` anymore (but `libtinfo6` which doesn't work with the current Maude version)

RUN apt-get update && \
    apt-get install -y \
        curl \
        # libtinfo5 is needed by maude
        libtinfo5 \
        locales \
        # we need python for our Tamarin oracle:
        python3 \
        # vim is only provided for convenience:
        vim \
        wget \
        zip \
        make \
        git    

# `/.local/bin` is the installation location of Tamarin and its dependencies
RUN mkdir -p /.local/bin
ENV PATH=/.local/bin:$PATH

# install Maude
ENV TAMARIN_RELEASE_VERSION_FOR_MAUDE="1.6.0"
ENV MAUDE_VERSION="2.7.1"
ENV MAUDE_URL="https://github.com/tamarin-prover/tamarin-prover/releases/download/$TAMARIN_RELEASE_VERSION_FOR_MAUDE/Maude-$MAUDE_VERSION-linux.zip"
RUN curl -q -s -S -L --create-dirs -o maude.zip $MAUDE_URL && \
    unzip maude.zip -d /.local/bin/ && \
    rm maude.zip && \
    mv /.local/bin/maude.linux64 /.local/bin/maude && \
    chmod a+x /.local/bin/maude

# install tamarin-prover
ENV TAMARIN_VERSION="1.10.0"
RUN curl -q -s -S -L --create-dirs -o tamarin.tar.gz https://github.com/tamarin-prover/tamarin-prover/releases/download/$TAMARIN_VERSION/tamarin-prover-$TAMARIN_VERSION-linux64-ubuntu.tar.gz && \
    tar -x -C /.local/bin/ -f tamarin.tar.gz && \
    rm tamarin.tar.gz && \
    chmod +x /.local/bin/tamarin-prover

# change locale to `en_US.UTF-8`:
USER root
RUN sed -i '/en_US.UTF-8/s/^# //g' /etc/locale.gen && \
    locale-gen
ENV LANG="en_US.UTF-8"
ENV LANGUAGE="en_US:en"
ENV LC_ALL="en_US.UTF-8"

WORKDIR /tamarin
COPY dh/model/dh.spthy .
COPY wireguard/model/wireguard.oracle .
COPY wireguard/model/wireguard.spthy .
COPY tamarin-docker/verify-dh.sh .
COPY tamarin-docker/verify-wireguard.sh .
