# IMP Registry (normative)

Normative annex to [`v0.1.md`](v0.1.md), specified by REQ-7.4.

**Status of this document.** The *procedure* and *naming rules* below are part
of the frozen contract. The *contents* (§R.5) grow additively after the freeze
— that is the point of a registry.

Requirements here use the prefix `REQ-R.` and are normative in the same sense
as `REQ-x.y` in the contract.

## R.1 Purpose

The registry standardizes *names* at IMP's extension points so that
independent implementations can interoperate without collisions. It is
**additive**: the registry never gates the protocol. Unregistered names are
permitted — they are simply not standardized, and a receiver treats them by
the tolerance rules of REQ-4.12 and REQ-7.3.

## R.2 Extension points

- **REQ-R.1** Message `type` values (REQ-4.11).
- **REQ-R.2** Envelope member names (REQ-4.7, REQ-7.3).
- **REQ-R.3** Feature identifiers — *reserved*: no feature identifiers exist
  until capability negotiation is introduced (REQ-7.5). The kind is defined
  now so that names can be registered without changing this document's
  procedure later.

## R.3 Naming rules

- **REQ-R.4** An **unqualified name** matches `[a-z][a-z0-9]*` (lowercase,
  no dot) and is **reserved for this specification**: only the change process
  of §R.4 may attach a standardized meaning to it. An unqualified name that is
  not registered has no standard meaning.
- **REQ-R.5** A **qualified name** is a reverse-DNS name: one or more
  dot-separated lowercase labels, each matching `[a-z][a-z0-9]*`, whose label
  sequence begins with a domain the registrant controls or is authorized to
  use — for example `net.example.invoice`. Qualified names are
  **permissionless and collision-free by construction**: they need not be
  registered to be used.
- **REQ-R.6** Implementations SHOULD use qualified names for private or
  application-specific semantics, and unqualified names only for standardized
  semantics.
- **REQ-R.7** Registration is what makes a name *standardized*; it is not what
  makes a name *legal*. No name requires approval to be used.

## R.4 Registration procedure

- **REQ-R.8** A proposal contains: the name; its kind (REQ-R.1–R.3); a
  one-paragraph definition; for a member, its canonical byte form under
  REQ-4.7 and its value type; and a statement of whether it changes any
  observable behaviour.
- **REQ-R.9** A proposal **MUST be additive** (REQ-7.3). It MUST NOT change
  the verification semantics of core messages, MUST NOT require a receiver to
  understand it, and MUST NOT add a member that is required in order to
  process a message without a wire-version bump. A proposal that cannot
  satisfy REQ-R.9 is a candidate for a new wire version, not for the registry.
- **REQ-R.10** A proposal that changes observable behaviour MUST include
  conformance vectors in the form of Annex B, and if it touches verification
  it MUST include updated Lean proofs (REQ-7.8).
- **REQ-R.11** Entries are reviewed and merged by the project owner and added
  to §R.5. An entry's status is one of `registered`, `reserved`, or
  `deprecated`.
- **REQ-R.12** A name MUST NOT be reused for a different meaning. An entry may
  be marked `deprecated`; deprecation is permanent for that meaning, mirroring
  REQ-2.8 for key ids.

## R.5 Registered entries

| Name | Kind | Status | Definition |
|---|---|---|---|
| `notification` | type | registered | A human-readable notice; payload interpretation is application-defined. |
| `event` | type | registered | A machine-actionable structured event; payload interpretation is application-defined. |
| `app` | type | registered | An application-defined payload; the envelope carries no interpretation of it. |

No member names and no feature identifiers are registered yet.

## R.6 Behaviour of implementations

- **REQ-R.13** An unknown or unregistered value MUST NOT cause verification to
  fail (REQ-4.12 for `type`; REQ-7.3 for members).
- **REQ-R.14** An implementation MAY ignore the semantics of an unregistered
  value, and MAY apply local policy to it (for example displaying `notification`
  payloads but quarantining unknown types).
- **REQ-R.15** A sender that includes a member defined by a registered entry
  MUST serialize it exactly as the entry specifies, and the canonical
  serialization MUST cover it (REQ-4.7).
