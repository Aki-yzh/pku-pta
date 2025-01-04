#!/bin/bash
git clone https://github.com/pascal-lab/java-benchmarks lab1_submitter/java-benchmarks
docker pull eclipse-temurin:17-jdk
docker build -t lab1_submitter_local lab1_submitter
