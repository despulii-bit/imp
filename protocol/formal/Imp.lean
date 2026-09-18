import Imp.Validation
import Imp.Canonical
import Imp.Text
import Imp.Base64

/-!
# Imp — formalization index

Machine-checked core of the IMP Message Protocol. See
`protocol/spec/v0.1.md` for the requirement ↔ theorem mapping.

Modules:

* `Imp.Signature`    — abstract signature primitive (REQ-2.3, REQ-4.10)
* `Imp.Envelope`     — message members, signed projection (REQ-4.2, REQ-4.7)
* `Imp.KeyRegistry`  — epochs, rotation, chain validity (REQ-2.7 … REQ-3.5)
* `Imp.Validation`   — receiver acceptance gate (REQ-6.1, SEC-1/3/6)
* `Imp.Canonical`    — canonical byte framing injectivity (REQ-4.9, SEC-2)
* `Imp.Text`         — decimal and JSON-string encoders (REQ-4.7, SEC-2)
* `Imp.Base64`       — base64 bit-packing bijection (REQ-4.9, SEC-2)

All declarations live in namespace `Imp` as `Imp.<name>` (for example
`Imp.body_injective`); module names such as `Imp.Canonical` are import paths,
not name prefixes.
-/

namespace Imp
end Imp
