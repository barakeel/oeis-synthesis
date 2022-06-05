#!/bin/bash
cd /home/thibault/big/oeis-web
git pull
Holmake cleanAll
Holmake
hol < server/update_state.sml
