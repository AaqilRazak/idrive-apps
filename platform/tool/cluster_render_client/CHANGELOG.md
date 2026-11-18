# tool/cluster_render_client

A version is frozen once a newer one exists. A component moves to a new
one with `node platform/platform.js use tool/cluster_render_client <version>`.

## 1.1.0

- (what changed, and which components it affects)

## 1.0.0

`cluster_render_client.js` (MPL-2.0), the cluster-render client, as it
was on main at 68aa156: from vizualyse-cast and vizualyse-moonlight.

## 1.1.0

Layers take `guide_hold` and `yield` (cluster-render PROTOCOL.md "Layer
fields", as upstream's client sends them): `guide_hold: false` on a `map`
layer keeps cluster-render's guide hold released while the layer wants the
map, so the slot over the map shows the car's badge, or BMW's own turn box
during a route. Booleans go as 0 / 1.

A video layer takes `always_packed` (PROTOCOL.md: every write as packed 4x4
blocks, only the changed ones), and `alwaysPacked` says whether the
service's hello offered it. A service without it ignores the field and
writes the layer exact.
