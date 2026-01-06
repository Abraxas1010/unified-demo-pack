#!/usr/bin/env python3
import sys, json
try:
    import jsonschema
except Exception as e:
    print("jsonschema module missing. Install via: pip install jsonschema", file=sys.stderr)
    sys.exit(2)

if len(sys.argv) < 3:
    print("Usage: validate_unified_json.py <schema.json> <payload.json or ->", file=sys.stderr)
    sys.exit(2)

schema_path = sys.argv[1]
payload_path = sys.argv[2]

with open(schema_path, 'r') as f:
    schema = json.load(f)

if payload_path == '-':
    payload = json.load(sys.stdin)
else:
    with open(payload_path, 'r') as f:
        payload = json.load(f)

jsonschema.validate(instance=payload, schema=schema)
print("OK: unified payload conforms to schema")
