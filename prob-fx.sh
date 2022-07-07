#! /bin/bash
pack run prob-fx.ipkg $1
python3 graph.py $1
