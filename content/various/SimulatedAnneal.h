/**
 * Author: FHVirus
 * Date: 2023-10-20
 * License: CC0
 * Source: oi-wiki
 * Description: rnd() should return $r \in [0, 1]$.
 * Status: not tested
 */
#pragma once

void simulateAnneal() {
  double t = 100000, now = ans;
  while (t > 0.001) {
    double nxt = now + t * rnd();
    double delta = calc(nxt) - calc(now);
    if (exp(-delta / t) > rnd()) now = nxt;
    t *= 0.97;
  }
  rep (i, 0, 1000) calc(ans + t * rnd());
}
