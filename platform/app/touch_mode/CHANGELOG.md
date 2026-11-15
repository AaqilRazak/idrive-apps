# app/touch_mode

A version is frozen once a newer one exists. A component moves to a new
one with `node platform/platform.js use app/touch_mode <version>`.

## 1.0.0

New: `touch_mode.js`, an iDrive app's touch screen and its list (the touch
kit's app side), grown from vizualyse_cluster's picker handling: entered,
the app opens its empty screen state and asks the tool for its touch
screen; the tool's List corner (`{"ev":"list"}`), BACK or the car starting
to move bring the page (the iDrive list) back with `closeState` (or by
opening the page); the picture hides when its state is left or covered by a
pop-up; without a screen state it goes over the page. Used by
vizualyse_cluster 0.3.0.
