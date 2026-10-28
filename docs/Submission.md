# Submitting to Palomar

1. Run `bash scripts/verify.sh` on Linux. The script checks the source layout,
   metadata, build, axiom reports and the three principal statements with
   sandboxed Comparator. `bash scripts/verify.sh --components` checks the
   extended suite instead.
2. Publish this directory's contents as the root of a public GitHub repository.
   Include `lake-manifest.json`, the licence, source files and metadata; the
   supplied `.gitignore` excludes generated build files and local logs.
3. Select the published commit on GitHub and copy its full commit identifier.
4. Open the [submission form](https://submit.palomar-registry.org/), enter the
   repository and published revision, and use the standard root layout.

| Setting | Value |
| --- | --- |
| Project directory | Repository root; leave the optional project path blank. |
| Comparator configuration | `comparator.json` |
| Formalization metadata | `formalization.yaml` |
| Responsible maintainers | Matthew J. Colbrook and George Stepaniants |
| Repository licence | Apache-2.0 |

The default submission records the main theorem, entire-group proposition and
normalization corollary together. The optional `comparator-components.json`
selects all 68 principal and supporting statements as a separate configuration.

The maintainers can submit through their own GitHub accounts. Palomar performs
its mechanical verification and editorial review on the selected published
revision; local checking does not itself create a registry entry.

See the [current submission guide](https://palomar-registry.org/how-to-submit)
for the registry's submission and registration process.
