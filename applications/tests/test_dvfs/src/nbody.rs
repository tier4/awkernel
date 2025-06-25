use alloc::{vec, vec::Vec};
use num_traits::float::Float;

#[derive(Clone, Copy, Debug)]
struct Body {
    x: f64,
    y: f64,
    vx: f64,
    vy: f64,
    mass: f64,
}

impl Body {
    fn update_velocity(&mut self, fx: f64, fy: f64, dt: f64) {
        self.vx += fx / self.mass * dt;
        self.vy += fy / self.mass * dt;
    }

    fn update_position(&mut self, dt: f64) {
        self.x += self.vx * dt;
        self.y += self.vy * dt;
    }
}

fn compute_force(a: &Body, b: &Body, g: f64, eps: f64) -> (f64, f64) {
    let dx = b.x - a.x;
    let dy = b.y - a.y;
    let dist_sq = dx * dx + dy * dy + eps * eps; // softening
    let dist = dist_sq.sqrt();
    let f = g * a.mass * b.mass / dist_sq;
    let fx = f * dx / dist;
    let fy = f * dy / dist;
    (fx, fy)
}

fn nbody_step(bodies: &mut [Body], g: f64, dt: f64, eps: f64) {
    let n = bodies.len();
    let mut forces = vec![(0.0, 0.0); n];

    for i in 0..n {
        for j in 0..n {
            if i != j {
                let (fx, fy) = compute_force(&bodies[i], &bodies[j], g, eps);
                forces[i].0 += fx;
                forces[i].1 += fy;
            }
        }
    }

    for i in 0..n {
        bodies[i].update_velocity(forces[i].0, forces[i].1, dt);
        bodies[i].update_position(dt);
    }
}

pub fn simulate() {
    const N: usize = 5000;
    const STEPS: usize = 2;
    const G: f64 = 6.67430e-11;
    const DT: f64 = 0.1;
    const EPS: f64 = 1e-3;

    let mut rnd = XorShift64::new(0x12345678); // 乱数生成器の初期化

    // 初期化：ランダムにばら撒く（実用では乱数を使ってもよい）
    let mut bodies = (0..N)
        .map(|_| Body {
            x: rnd.next_f64(),
            y: rnd.next_f64(),
            vx: 0.0,
            vy: 0.0,
            mass: rnd.next_f64(),
        })
        .collect::<Vec<_>>();

    for _ in 0..STEPS {
        nbody_step(&mut bodies, G, DT, EPS);
    }
}

pub struct XorShift64 {
    state: u64,
}

impl XorShift64 {
    pub fn new(seed: u64) -> Self {
        Self { state: seed }
    }

    pub fn next(&mut self) -> u64 {
        let mut x = self.state;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.state = x;
        x
    }

    pub fn next_f64(&mut self) -> f64 {
        (self.next() as f64) / (u64::MAX as f64)
    }
}
