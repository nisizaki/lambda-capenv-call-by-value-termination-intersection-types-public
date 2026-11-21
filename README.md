# Call-by-value termination of λcapenv and intersection types (Isabelle/HOL)

An Isabelle/HOL formalization of the characterization of call-by-value
termination of the `id`-free **λcapenv** (the λ-calculus with first-class
environments and capture environments) by an intersection type system.  The
reduction is full σ (environment rules) together with β_v, which fires only on
closures applied to fireballs.

## Main results

| Statement | Isabelle name | Theory |
|---|---|---|
| `Typ M ⟷ CFN M` (typable iff it reaches a clash-free normal form) | `main_characterization` | `Main_Results` |
| `Typ M ⟷ CFSN M`; typable terms are strongly normalizing | `main_characterization_SN`, `Typ_imp_SN` | `Main_Results` |
| stuck normal forms (non-fireballs) are untypable | `clash_not_Typ` | `Main_Results` |
| σ terminates and is confluent | `sig_SN`, `sig_confluent` | `Sigma`, `Sig_Confluence` |
| uniform normalization | `NF_unique`, `WN_imp_SN`, `CFN_iff_CFSN` | `Uniform` |
| completeness (subject expansion), soundness | `completeness`, `soundness` | `Completeness`, `Soundness` |
| capture environments: typing, locality, non-retention, lazy environments | `cap_typing`, `cap_local`, `cap_nonretain_1`, `cap_nonretain_2`, `cap_nonretain_3`, `cap_lazy_env` | `Capture` |
| agreement with open call-by-value λ-calculus | `pure_cap_characterization`, `pure_cap_main`, `fv_condition_necessary` | `Pure_Capture` |
| bridge: the reduction of λcapenv (capI) is σ or full β; call-by-value reduction is included in it | `bij_toI`, `red_iff_sig_or_beta`, `cbv_sub_red` | `CapI_Bridge` (session `LambdaCapEnvCBV_CapI`) |

## Files

- `isabelle/ROOT`, `isabelle/*.thy`: session `LambdaCapEnvCBV`, 14 theories
  (about 4,000 lines): `ARS`, `Cap_Syntax`, `Sigma`, `Sig_Confluence`,
  `Cap_Reduction`, `Uniform`, `Typing`, `Completeness`, `Soundness`,
  `Main_Results`, `Capture`, `Examples`, `Lambda`, `Pure_Capture`.
- `bridge/ROOT`, `bridge/CapI_Bridge.thy`: session `LambdaCapEnvCBV_CapI`
  (one theory, about 70 lines) relating this calculus to the base calculus
  (capI) of `lambda-capenv-public`.

No theory contains `sorry`, `oops`, `axiomatization` or `ML` code.

## Building

Requires [Isabelle2025-2](https://isabelle.in.tum.de/).  Both sessions are checked
with `quick_and_dirty = false`.

The main session needs only HOL:

    isabelle build -d isabelle LambdaCapEnvCBV

The bridge session `LambdaCapEnvCBV_CapI` (directory `bridge/`) imports the theory
`Reduction` of the session `LambdaCapEnv` from the repository
[lambda-capenv-public](https://github.com/nisizaki/lambda-capenv-public).
Check out that repository next to this one and pass its `isabelle` directory
with `-d`:

    git clone https://github.com/nisizaki/lambda-capenv-public.git ../lambda-capenv-public
    isabelle build -d isabelle -d bridge -d ../lambda-capenv-public/isabelle LambdaCapEnvCBV_CapI

(this also builds the session `LambdaCapEnv`, which takes a few minutes or more
depending on the machine).

## Related repositories

- λcapenv core (terms, reduction, simple types, subject reduction, confluence,
  strong normalization, type inference), needed for the bridge:
  https://github.com/nisizaki/lambda-capenv-public
- Call-by-name normalizability of λcapenv and intersection types: https://github.com/nisizaki/lambda-capenv-weak-head-normalizability-intersection-types-public
- PCF_env interpreter (call-by-value λcapenv with PCF constructs):
  https://github.com/nisizaki/pcf-env-interpreter-public
- The same questions for λenv (with `id`):
  https://github.com/nisizaki/lambda-env-weak-head-normalizability-intersection-types,
  https://github.com/nisizaki/lambda-env-call-by-value-termination-intersection-types

## Authors

Shin-ya Nishizaki and Shogo Murasaki

## How to cite

Shin-ya Nishizaki and Shogo Murasaki. *Call-by-Value Termination of the id-free λcapenv and its Characterization by Intersection Types, Formalized in Isabelle/HOL.*

## License

MIT License (see [LICENSE](LICENSE)).
