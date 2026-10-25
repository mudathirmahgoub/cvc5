# Evidence for the rules of the relations calculus

Lost (bold): without the rule the pair is no longer solved; WRONG: wrong answer or
failed model check without it; · : the rule fires but the pair is solved without it.

| rule | def | FMF | noFMF | stop | FMF+R | noFMF+R | noFMF+H |
|---|---|---|---|---|---|---|---|
| Cycle-Def | · (fires, not needed) | · (fires, not needed) |  | · (fires, not needed) | **tso-1-th** | · (fires, not needed) |  |
| Inst-Cycle | WRONG plsc-1-th-no-ltts, WRONG sc-1-th-just-rf, WRONG sc-1-th-no-ltts, WRONG sc-2-th-just-rf, WRONG tso-1-th-no-ltts | WRONG sc-2-th-just-rf | **sc-2-th-just-rf** | WRONG plsc-1-th-no-ltts, WRONG sc-1-th-just-rf, WRONG sc-1-th-no-ltts | WRONG plsc-2-th-just-rf, WRONG sc-2-th, WRONG sc-2-th-just-rf | **plsc-2-th**, **plsc-2-th-just-rf**, **sc-2-th**, **sc-2-th-just-rf** | **sc-2-th**, **sc-2-th-just-rf** |
| Unroll | WRONG plsc-1-th-no-ltts, WRONG sc-1-th-just-rf, WRONG sc-1-th-no-ltts, WRONG sc-2-th-just-rf, WRONG tso-1-th-no-ltts | WRONG plsc-1-th-no-ltts, WRONG sc-2-th-just-rf | **sc-2-th-just-rf** | WRONG plsc-1-th-no-ltts, WRONG sc-1-th-just-rf, WRONG sc-1-th-no-ltts | WRONG plsc-1-th-no-ltts, WRONG plsc-2-th-just-rf, WRONG sc-2-th, WRONG sc-2-th-just-rf | **plsc-2-th**, **plsc-2-th-just-rf**, **sc-2-th**, **sc-2-th-just-rf** | **sc-2-th**, **sc-2-th-just-rf** |
| Split-Len | WRONG sc-2-th-just-rf | WRONG sc-2-th-just-rf | **sc-2-th-just-rf** | · (fires, not needed) | **tso-1-th**, WRONG plsc-2-th-just-rf, WRONG sc-2-th, WRONG sc-2-th-just-rf | **plsc-2-th**, **plsc-2-th-just-rf**, **sc-2-th**, **sc-2-th-just-rf** | **sc-2-th**, **sc-2-th-just-rf** |
| Alternate | · (fires, not needed) | · (fires, not needed) | · (fires, not needed) | · (fires, not needed) | **tso-1-th** | · (fires, not needed) | · (fires, not needed) |
| Alt-Close | · (fires, not needed) | · (fires, not needed) | · (fires, not needed) | · (fires, not needed) | · (fires, not needed) | · (fires, not needed) | · (fires, not needed) |
| Chord | · (fires, not needed) | **sc-2-th-just-rf** | **sc-2-th-just-rf** | · (fires, not needed) | **plsc-2-th-just-rf**, **sc-2-th**, **sc-2-th-just-rf**, **tso-1-th** | **plsc-2-th**, **plsc-2-th-just-rf**, **sc-2-th**, **sc-2-th-just-rf** | **sc-2-th**, **sc-2-th-just-rf** |
| Distinct | **sc-1-th-just-rf** | · (fires, not needed) | · (fires, not needed) | · (fires, not needed) | · (fires, not needed) | · (fires, not needed) | · (fires, not needed) |
| Backward |  | · (fires, not needed) | · (fires, not needed) |  | **sc-2-th** | · (fires, not needed) | · (fires, not needed) |
| LC completion | **sc-2-th-just-rf** | WRONG sc-2-th-just-rf | **sc-2-th-just-rf** | · (fires, not needed) | WRONG plsc-2-th-just-rf, WRONG sc-2-th, WRONG sc-2-th-just-rf | **plsc-2-th**, **plsc-2-th-just-rf**, **sc-2-th**, **sc-2-th-just-rf** | **sc-2-th**, **sc-2-th-just-rf** |
| Branch | · (fires, not needed) |  |  | **sc-1-th-just-rf** |  |  |  |
| Acyclic-Down | · (fires, not needed) | **sc-1-th**, **sc-1-th-just-rf**, WRONG plsc-1-th, WRONG sc-2-th-just-rf | **sc-2-th-just-rf** | **sc-1-th-just-rf** | **sc-1-th**, WRONG plsc-1-th, WRONG plsc-2-th-just-rf, WRONG sc-2-th, WRONG sc-2-th-just-rf | **plsc-1-th**, **plsc-2-th**, **plsc-2-th-just-rf**, **sc-1-th**, **sc-2-th**, **sc-2-th-just-rf** | **sc-2-th**, **sc-2-th-just-rf** |
| Register | · (fires, not needed) | · (fires, not needed) | · (fires, not needed) | · (fires, not needed) | · (fires, not needed) | · (fires, not needed) | · (fires, not needed) |
| Inclusion |  | **plsc-1-th**, **sc-1-th**, **tso-1-th-just-rf** | · (fires, not needed) |  | **tso-1-th**, **tso-1-th-just-rf** | **tso-1-th**, **tso-1-th-just-rf** | · (fires, not needed) |
| TC-Sub: in TC(X) |  |  |  |  | **tso-1-th** | · (fires, not needed) |  |
| TC-Sub: R trans. |  |  |  |  | **sc-2-th**, **tso-1-th** | **plsc-2-th**, **sc-2-th** | **sc-2-th** |
| TC-Sub: A×B |  |  |  |  | **sc-2-th**, **tso-1-th** | **plsc-2-th**, **sc-2-th** | **sc-2-th** |
| TC-Sub: ∩/∖ |  |  |  |  | **plsc-2-th-just-rf** | **plsc-2-th**, **plsc-2-th-just-rf** |  |
| TC-Sub: R⊆S |  |  |  |  | **sc-1-th-no-ltts**, **tso-1-th-no-ltts** | · (fires, not needed) | · (fires, not needed) |
| Fun-UF | · (fires, not needed) | · (fires, not needed) | · (fires, not needed) | · (fires, not needed) | **sc-2-th**, **tso-1-th**, WRONG plsc-2-th-just-rf | **plsc-2-th**, **plsc-2-th-just-rf**, **sc-2-th** | · (fires, not needed) |
| TC-Down (lazy) |  |  |  |  | WRONG plsc-1-th-no-ltts, WRONG tso-1-th-no-ltts |  |  |
| TC-Up | **sc-2-th-just-rf** | WRONG plsc-1-th | · (fires, not needed) | · (fires, not needed) | WRONG plsc-1-th, WRONG plsc-1-th-just-rf, WRONG plsc-2-th-just-rf, WRONG tso-1-th | **plsc-1-th**, **plsc-1-th-just-rf**, **plsc-2-th-just-rf**, **tso-1-th** | · (fires, not needed) |
| TC-Down | WRONG plsc-1-th-no-ltts, WRONG sc-1-th-no-ltts, WRONG tso-1-th-no-ltts | WRONG plsc-1-th-no-ltts | · (fires, not needed) | WRONG plsc-1-th-no-ltts, WRONG sc-1-th-no-ltts |  |  |  |
| Join-Compose | WRONG sc-1-th-just-rf, WRONG sc-2-th-just-rf | **tso-1-th-just-rf**, WRONG plsc-1-th, WRONG sc-1-th, WRONG sc-1-th-just-rf, WRONG sc-2-th-just-rf | **sc-1-th-just-rf**, **sc-2-th-just-rf** | WRONG sc-1-th-just-rf | WRONG plsc-1-th, WRONG plsc-1-th-just-rf, WRONG plsc-2-th-just-rf, WRONG sc-1-th, WRONG sc-1-th-just-rf, WRONG sc-2-th, WRONG sc-2-th-just-rf, WRONG tso-1-th | **plsc-1-th**, **plsc-1-th-just-rf**, **plsc-2-th**, **plsc-2-th-just-rf**, **sc-1-th**, **sc-1-th-just-rf**, **sc-2-th**, **sc-2-th-just-rf**, **tso-1-th** | **sc-1-th-just-rf**, **sc-2-th**, **sc-2-th-just-rf** |
| Join-Split | WRONG tso-1-th-no-ltts | **tso-1-th-just-rf**, WRONG plsc-1-th, WRONG sc-1-th | · (fires, not needed) | **sc-1-th-just-rf**, WRONG plsc-1-th-no-ltts | **tso-1-th**, WRONG plsc-1-th, WRONG plsc-1-th-just-rf, WRONG plsc-2-th-just-rf, WRONG sc-1-th, WRONG tso-1-th-just-rf, WRONG tso-1-th-no-ltts | **plsc-1-th**, **plsc-1-th-just-rf**, **plsc-2-th**, **plsc-2-th-just-rf**, **sc-1-th**, **sc-2-th**, **tso-1-th**, **tso-1-th-just-rf** |  |
| all TC-Subset |  |  |  |  | **plsc-2-th-just-rf**, **sc-1-th-no-ltts**, **sc-2-th**, **tso-1-th-no-ltts** | **plsc-2-th**, **plsc-2-th-just-rf**, **sc-2-th** | **sc-2-th** |
| all minimality | **plsc-1-th-no-ltts**, **sc-1-th-no-ltts**, **tso-1-th-no-ltts** | **plsc-1-th**, **plsc-1-th-no-ltts**, **sc-1-th-no-ltts**, **sc-2-th-just-rf** | **sc-2-th-just-rf** | · (fires, not needed) | **plsc-1-th-no-ltts**, **plsc-2-th-just-rf**, **sc-1-th-no-ltts**, **sc-2-th**, **sc-2-th-just-rf**, **tso-1-th**, **tso-1-th-no-ltts** | **plsc-2-th**, **plsc-2-th-just-rf**, **sc-2-th**, **sc-2-th-just-rf** | **sc-2-th**, **sc-2-th-just-rf** |

## Never fired on any solved pair

- Same-Operands
- Anchor conflict
- Fun-Pairs
- Not-Fun
- Ground-TC
- Ground-Join

## Examples

- **Cycle-Def** (tso-1-th|fmf-unsat-rules): `cyc(co) ⇒ (cyc117,cyc117) ∈ co+`
- **Inst-Cycle** (sc-1-th-no-ltts|default): `cyc((rf ∪ (po ∪ (co ∪ fr)))) ⇒ cyclen6 >= 2`
- **Unroll** (sc-1-th-no-ltts|default): `cyclen6 >= 2 ⇒ (cyc5,cyc9) ∈ rf+ ∨ (cyc5,cyc9) ∈ po+ ∨ (cyc5,cyc9) ∈ co+ ∨ (cyc5,cyc9) ∈ fr+`
- **Split-Len** (sc-2-th-just-rf|nofmf-unsat-hammer): `cyc((po ∪ rf)) ∧ cyclen10 >= 2 ⇒ cyclen10 >= 3 ∨ (cyclen10 = 2 ∧ cyc9 = cyc14)`
- **Alternate** (tso-1-th|fmf-unsat-rules): `cyc((co ∪ (fr ∪ (rf ∪ (loc ∩ po+))))) ∧ cyclen8 >= 3 ⇒ ¬((cyc7,cyc10) ∈ co+ ∧ (cyc10,cyc95) ∈ co+)`
- **Alt-Close** (sc-1-th-just-rf|nofmf-unsat-hammer): `cyc((po ∪ rf)) ∧ cyclen6 = 3 ⇒ ¬((cyc9,cyc28) ∈ po+ ∧ (cyc5,cyc9) ∈ po+)`
- **Chord** (sc-2-th-just-rf|nofmf-unsat-hammer): `cyc((po ∪ rf)) ∧ cyclen10 >= 3 ⇒ (cyc9,cyc32) ∉ po+`
- **Distinct** (sc-1-th-just-rf|default): `cyclen6 ≠ 2 ∧ cyc((po ∪ rf)) ∧ cyclen6 >= 2 ⇒ cyc5 ≠ cyc9`
- **Backward** (sc-2-th|fmf-unsat-rules): `cyc((rf ∪ (po ∪ (co ∪ fr)))) ∧ cyclen10 = 3 ⇒ (cyc68,cyc9) ∉ rf+`
- **LC completion** (sc-2-th-just-rf|nofmf-unsat-hammer): `cyc((po ∪ rf)) ∧ cyclen10 >= 5 ⇒ cyc14 ≠ cyc82`
- **Branch** (sc-1-th-just-rf|stoponly): `cyc((po ∪ rf)) ∧ ¬(cyc(po)) ∧ cyclen7 = 3 ⇒ (cyc6,cyc10) ∉ po+ ∨ (cyc10,cyc49) ∉ po+`
- **Acyclic-Down** (sc-1-th|nofmf-unsat-rules): `(cyc9,cyc5) ∈ po+ ∧ ¬(cyc(po)) ⇒ cyc5 ≠ cyc9`
- **Register** (sc-1-th-just-rf|nofmf-unsat-hammer): `¬(cyc(po)) ⇒ po+ = (po ∪ po+)`
- **Inclusion** (tso-1-th-just-rf|nofmf-unsat-rules): `cyc(rf) ∧ ¬(cyc(po)) ⇒ cycedge21 ∈ rf ∧ cycedge21 ∉ po+`
- **TC-Sub: in TC(X)** (tso-1-th|fmf-unsat-rules): `(cyc10,cyc95) ∈ ((loc ∩ po+))+ ⇒ (cyc10,cyc95) ∈ po+`
- **TC-Sub: R trans.** (sc-2-th|nofmf-unsat-hammer): `(cyc14,cyc9) ∈ co+ ∧ co = (co ∪ co;co) ⇒ (cyc14,cyc9) ∈ co`
- **TC-Sub: A×B** (sc-2-th|nofmf-unsat-hammer): `(cyc14,cyc9) ∈ fr+ ∧ Read×Write = (fr ∪ Read×Write) ∧ ∅ = (Read ∩ Write) ⇒ (cyc14,cyc9) ∈ fr`
- **TC-Sub: ∩/∖** (plsc-2-th-just-rf|nofmf-unsat-rules): `(cyc9,cyc14) ∈ ((loc ∩ po+))+ ∧ fun(address) ∧ loc = address;(address)^-1 ⇒ (cyc9,cyc14) ∈ loc`
- **TC-Sub: R⊆S** (sc-1-th-no-ltts|fmf-unsat-rules): `(cyc5,cyc9) ∈ po+ ∧ Event×Event = (po ∪ Event×Event) ⇒ (cyc5,cyc9) ∈ Event×Event`
- **Fun-UF** (plsc-2-th-just-rf|nofmf-unsat-rules): `fun(address) ∧ (cyc9,srj23) ∈ address ⇒ srj23 = (rfun_34 cyc9)`
- **TC-Down (lazy)** (plsc-1-th-no-ltts|fmf-unsat-rules): `(cycedge59.0,cycedge59.1) ∈ po+ ⇒ (cycedge59.0,cycedge59.1) ∈ po ∨ ((cycedge59.0,stc181) ∈ po ∧ (stc282,cycedge59.1) ∈ po ∧ (stc181 = stc282 ∨ (stc181,stc282) ∈ po+))`
- **TC-Up** (plsc-1-th-just-rf|nofmf-unsat-rules): `(cyc6,cyc10) ∈ (loc ∩ po+) ∧ (loc ∩ po+) = (loc ∩ po+) ⇒ (cyc6,cyc10) ∈ ((loc ∩ po+))+`
- **TC-Down** (sc-1-th-no-ltts|default): `(cyc5,cyc9) ∈ po+ ⇒ (cyc5,cyc9) ∈ po ∨ ((cyc5,stc123) ∈ po ∧ (stc224,cyc9) ∈ po ∧ (stc123 = stc224 ∨ (stc123,stc224) ∈ po+))`
- **Join-Compose** (sc-1-th-just-rf|nofmf-unsat-hammer): `(cyc9) ∈ Write ∧ (cyc9,cyc5) ∈ rf+ ∧ rf = rf+ ⇒ (cyc5) ∈ Write;rf`
- **Join-Split** (sc-1-th|nofmf-unsat-rules): `(cyc5,cyc9) ∈ (address;(address)^-1 ∪ (co ∪ (rf ∪ fr))) ∧ address;(address)^-1 = (address;(address)^-1 ∪ (co ∪ (rf ∪ fr))) ⇒ (cyc5,srj22) ∈ address`

## Summary per rule

- Cycle-Def: fires on 10 pairs (10 lemmas); needed on 1, wrong without it on 0
- Inst-Cycle: fires on 42 pairs (46 lemmas); needed on 7, wrong without it on 12
- Unroll: fires on 42 pairs (96 lemmas); needed on 7, wrong without it on 14
- Split-Len: fires on 42 pairs (96 lemmas); needed on 8, wrong without it on 5
- Alternate: fires on 37 pairs (170 lemmas); needed on 1, wrong without it on 0
- Alt-Close: fires on 37 pairs (170 lemmas); needed on 0, wrong without it on 0
- Chord: fires on 37 pairs (196 lemmas); needed on 12, wrong without it on 0
- Distinct: fires on 42 pairs (156 lemmas); needed on 1, wrong without it on 0
- Backward: fires on 34 pairs (602 lemmas); needed on 1, wrong without it on 0
- LC completion: fires on 14 pairs (661 lemmas); needed on 8, wrong without it on 4
- Branch: fires on 8 pairs (18 lemmas); needed on 1, wrong without it on 0
- Acyclic-Down: fires on 38 pairs (1928 lemmas); needed on 13, wrong without it on 6
- Register: fires on 42 pairs (76 lemmas); needed on 0, wrong without it on 0
- Inclusion: fires on 34 pairs (66 lemmas); needed on 7, wrong without it on 0
- TC-Sub: in TC(X): fires on 13 pairs (68 lemmas); needed on 1, wrong without it on 0
- TC-Sub: R trans.: fires on 12 pairs (58 lemmas); needed on 5, wrong without it on 0
- TC-Sub: A×B: fires on 11 pairs (47 lemmas); needed on 5, wrong without it on 0
- TC-Sub: ∩/∖: fires on 10 pairs (23 lemmas); needed on 3, wrong without it on 0
- TC-Sub: R⊆S: fires on 18 pairs (190 lemmas); needed on 2, wrong without it on 0
- Fun-UF: fires on 42 pairs (1322 lemmas); needed on 5, wrong without it on 1
- TC-Down (lazy): fires on 2 pairs (2 lemmas); needed on 0, wrong without it on 2
- TC-Up: fires on 42 pairs (45314 lemmas); needed on 5, wrong without it on 5
- TC-Down: fires on 17 pairs (167 lemmas); needed on 0, wrong without it on 6
- Join-Compose: fires on 42 pairs (19453 lemmas); needed on 15, wrong without it on 15
- Join-Split: fires on 39 pairs (1053 lemmas); needed on 11, wrong without it on 10
- all TC-Subset: fires on 18 pairs (0 lemmas); needed on 8, wrong without it on 0
- all minimality: fires on 38 pairs (0 lemmas); needed on 21, wrong without it on 0
