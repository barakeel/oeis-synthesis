#!/bin/bash
cd /home/thibault/big/oeis-synthesis
git pull
Holmake cleanAll
Holmake
hol < server/update_state.sml
