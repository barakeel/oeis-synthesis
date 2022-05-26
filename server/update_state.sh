#!/bin/bash
cd /home/thibault/big/oeis-dev
git pull
Holmake cleanAll
Holmake
hol < server/update_state.sml
