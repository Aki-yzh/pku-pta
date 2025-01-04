#!/bin/bash
docker run --rm -it \
    -v ./global:/mnt/global_space -v ./user:/mnt/user_space \
    --cpus 2 --pids-limit 256 --memory 6g --network none --memory-swap -1 \
    --hostname container --add-host="container:127.0.0.1" \
    -e TOKEN=1:submission_zip \
    lab1_submitter_local