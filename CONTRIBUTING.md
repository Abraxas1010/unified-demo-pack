# Contributing to HeytingLean Unified Demo Pack

Thank you for your interest in contributing! This document explains how to contribute and the requirements for doing so.

---

## Before You Contribute

### 1. Contributor License Agreement (CLA)

This project uses **dual licensing** (AGPL-3.0 + Commercial). By contributing, you agree to the [Contributor License Agreement](CLA.md).

**By submitting a pull request, you confirm:**
- You have read and agree to the CLA
- You have the right to submit the contribution
- Your contribution may be distributed under both AGPL-3.0 and Commercial licenses

### 2. Code of Conduct

Be respectful and constructive. We're building verified cryptography — precision and clarity matter.

---

## How to Contribute

### Reporting Issues

1. Search existing issues first
2. Use the issue template
3. Include:
   - Lean/Mathlib version (`lean --version`, check `lean-toolchain`)
   - Minimal reproduction case
   - Expected vs actual behavior

### Pull Requests

1. **Fork** the repository
2. **Create a branch** from `main`: `git checkout -b feature/your-feature`
3. **Make your changes**
4. **Run verification:**
   ```bash
   ./scripts/guard_no_sorry.sh   # No incomplete proofs
   make build                     # Must compile
   make run-quick                 # Must pass
   ```
5. **Commit** with clear messages
6. **Push** and open a PR

### Commit Message Format

```
[AREA] Short description (50 chars max)

Longer description if needed. Explain what and why,
not just how.

Refs: #issue-number (if applicable)

I have read and agree to the HeytingLean CLA (CLA.md).
```

Areas: `[Contextuality]`, `[FHE]`, `[ZK]`, `[PQC]`, `[Quantum]`, `[Docs]`, `[CI]`, `[Build]`

---

## Code Standards

### Lean Code

1. **No `sorry` or `admit`** — All proofs must be complete
2. **No `axiom`** without explicit justification and documentation
3. **Follow Mathlib style** where applicable
4. **Document non-obvious proofs** with comments
5. **Use meaningful names** — `h₁` is fine for local hypotheses, but theorems need descriptive names

### Documentation

1. Module docstrings explaining purpose
2. Theorem statements should be readable
3. References to papers/specs where applicable

### Testing

1. Add sanity checks for new modules
2. Update `UnifiedDemo.lean` if adding new top-level features
3. Ensure `guard_no_sorry.sh` passes

---

## What We're Looking For

### High Priority

- [ ] Additional contextuality scenarios (KCBS, GHZ, cluster states)
- [ ] POVM joint measurability formalization
- [ ] Stronger FHE instantiations (multiplication proofs)
- [ ] ML-DSA (FIPS 204) integration
- [ ] KAT (Known Answer Test) verification

### Medium Priority

- [ ] Performance improvements
- [ ] Better error messages in CLI tools
- [ ] Additional ZK protocol interfaces
- [ ] Visualization improvements

### Always Welcome

- Documentation improvements
- Typo fixes
- Code clarity improvements
- Test coverage

---

## Review Process

1. **Automated checks** must pass
2. **At least one maintainer review** required
3. **Discussion** may be needed for significant changes
4. **Squash merge** preferred for clean history

---

## Licensing Reminder

Your contributions will be available under:
- **AGPL-3.0** for open source use
- **Commercial license** for proprietary use

This dual licensing supports project sustainability while keeping the code open for research and verification.

If this is a concern for your employer, please discuss before contributing, or contact us about a Corporate CLA.

---

## Questions?

- **Technical:** Open a GitHub issue
- **CLA/Licensing:** rgoodman@apoth3osis.io
- **General:** See [LICENSE.md](LICENSE.md)

---

*Thank you for helping build verified cryptography!*
