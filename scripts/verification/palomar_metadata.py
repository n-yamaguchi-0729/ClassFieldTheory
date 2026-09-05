#!/usr/bin/env python3
"""Validate metadata with the pinned v0.4 schema and Palomar mechanical profile."""
import argparse
import json
from pathlib import Path
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pipeline", type=Path, required=True)
    parser.add_argument("--schema", type=Path, required=True)
    parser.add_argument("--metadata", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = {"passed": False, "schemaVersion": "v0.4", "hostedSubmission": False}
    code = 1
    try:
        import jsonschema
        sys.path.insert(0, str(args.pipeline))
        from scripts import submission_contract
        data = submission_contract.load_formalization_metadata(args.metadata)
        if data.get("version") != "v0.4":
            raise ValueError("Metadata must use v0.4")
        schema = json.loads(args.schema.read_text())
        validator = jsonschema.validators.validator_for(schema)
        validator.check_schema(schema)
        validator(schema, format_checker=jsonschema.FormatChecker()).validate(data)
        submission_contract.normalized_provenance(data)
        result.update(passed=True, schemaValid=True, palomarMechanicalMinimumValid=True)
        code = 0
    except Exception as error:
        result["error"] = str(error)
    result["exitCode"] = code
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result))
    return code


if __name__ == "__main__":
    raise SystemExit(main())
