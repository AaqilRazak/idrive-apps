# tool/touch_ui

A version is frozen once a newer one exists. A component moves to a new
one with `node platform/platform.js use tool/touch_ui <version>`.

## 1.0.0

New: the touch kit, every tool's touch screen on the central screen (Node 8,
no dependencies), grown from vizualyse-cluster's picker:

- `ui_kit.js`: the look (Green on graphite, Barlow Semi Condensed at 20, 24,
  32 and 44 px), the frame (tabs or a title top left, the List corner top
  right, the body, the status line), the widgets (button, seg, toggle,
  dropdown and its sheet, tabs, chip, panel, text, image, tile, info,
  progress, qr, icon) and `Surface`, which redraws only the rectangles that
  changed since the last frame, each clipped, with every widget touching
  it. `lint()` checks targets (64 px or more, inside the app area, none
  overlapping).
- `ui_canvas.js`: the RGBX canvas (from vizualyse-cluster's `ui_draw.js`),
  now clipped, with native fills for opaque spans and corner masks cached
  per radius; lines and triangles for the icons; glyphs drawn to their own
  advance (the next glyph's ink no longer shows under a letter).
- `ui_host.js`: `TouchScreen`: one mgu-render pixmap in the app area, frames
  at most every 33 ms from the tool's in-memory model, the press drawn
  before its action runs, taps, swipes, the List corner (`'list'`), tabs
  and dropdowns handled by the kit, an action's error in the status line,
  and the time from each touch to its pixels logged.
- `touch_reader.py` (from vizualyse-cluster, unchanged but its doc) and its
  test; `ui_png.js` (from vizualyse-cluster's `png.js`); the fonts
  `ui.fonts.json`, `ui.f*.font.gz` (built by vizualyse-cluster's
  `tools/ui_fonts.js`).
- `test/touch_ui_test.js`: a gallery of every kind, partial redraws equal to
  a full one, hits, the host end to end. A full frame 12.7 ms and a press
  0.7 ms in Node 8 on one desktop core.

Used by vizualyse-cluster 0.4.0.
