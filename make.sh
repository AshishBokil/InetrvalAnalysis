#!/usr/bin/env bash

set -e

bash setup.sh
bash build-targets.sh
bash build-analysis.sh
bash run-analysis.sh

