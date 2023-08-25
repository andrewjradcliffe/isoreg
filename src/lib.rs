#[derive(Debug)]
pub enum Direction {
    Increasing,
    Decreasing,
}
use self::Direction::*;

#[derive(Debug)]
pub struct IsoReg {
    x: Vec<f64>,
    mu: Vec<f64>,
}
impl IsoReg {
    pub fn interpolate(&self, z: f64) -> f64 {
        match self.x.binary_search_by(|x_j| x_j.partial_cmp(&z).unwrap()) {
            Ok(j) => {
                // An exact match on a binary search is inherently safe.
                unsafe { self.mu.get_unchecked(j).clone() }
            }
            Err(j) => {
                // We must determine where to interpolate from.
                let k = self.x.len();
                if j == 0 {
                    self.mu[1]
                        + (self.mu[0] - self.mu[1]) / (self.x[0] - self.x[1]) * (z - self.x[1])
                    // self.mu[0]
                    //     + (self.mu[0] - self.mu[1]) / (self.x[0] - self.x[1]) * (z - self.x[0])
                } else if j == k {
                    self.mu[k - 2]
                        + (self.mu[k - 1] - self.mu[k - 2]) / (self.x[k - 1] - self.x[k - 2])
                            * (z - self.x[k - 2])
                } else {
                    // z < x[j] => z - x[j] < 0
                    self.mu[j - 1]
                        + (self.mu[j] - self.mu[j - 1]) / (self.x[j] - self.x[j - 1])
                            * (z - self.x[j - 1])
                    // self.mu[j]
                    //     + (self.mu[j - 1] - self.mu[j]) / (self.x[j - 1] - self.x[j])
                    //         * (z - self.x[j])
                }
            }
        }
    }
    pub fn x<'a>(&'a self) -> &'a Vec<f64> {
        &self.x
    }
    pub fn mu<'a>(&'a self) -> &'a Vec<f64> {
        &self.mu
    }
}

pub fn isoreg_rtol(x: Vec<f64>, y: Vec<f64>) -> IsoReg {
    // These two necessary conditions could be handled more delicately.
    let n = y.len();
    assert_eq!(x.len(), n);
    assert!(n > 1);

    // N.B. The possibility of duplicates are not dealt with.
    let mut z: Vec<_> = x.into_iter().zip(y.into_iter()).collect();
    z.sort_unstable_by(|(a, _), (b, _)| a.partial_cmp(b).unwrap());
    let (x, y): (Vec<_>, Vec<_>) = z.into_iter().unzip();

    let mut nu = y.clone();

    let mut w: Vec<usize> = Vec::with_capacity(n);
    w.resize(n, 1);
    let mut j = n - 1;
    loop {
        while j > 0 && nu[j - 1] <= nu[j] {
            j -= 1;
        }
        if j == 0 {
            let mut nu_out = y;
            let mut pos: usize = 0;
            // The maximum value of `pos` is 1 + ∑ⱼwⱼ = 1 + (n - 1) = n, but the
            // last offset accessed is n - 1. Hence, all uses of `pos` are safe.
            for (nu_i, w_i) in nu.into_iter().zip(w.into_iter()) {
                for _ in 0..w_i {
                    nu_out[pos] = nu_i;
                    pos += 1;
                }
            }
            return IsoReg { x, mu: nu_out };
        }
        let w_prime = w[j - 1] + w[j];
        let w_j_m1 = w[j - 1] as f64;
        let w_j = w[j] as f64;
        let nu_prime = (w_j_m1 * nu[j - 1] + w_j * nu[j]) / w_prime as f64;
        nu.remove(j);
        w.remove(j);
        nu[j - 1] = nu_prime;
        w[j - 1] = w_prime;
        // Adjacent violators were pooled, thus check the newly formed block
        // against the (new) preceding block. However, if we pooled the
        // penultimate and last blocks, then no (new) preceding block exists,
        // and we must move the index left.
        j = j.min(nu.len() - 1);
    }
}

pub fn isoreg_ltor(x: Vec<f64>, y: Vec<f64>) -> IsoReg {
    // These two necessary conditions could be handled more delicately.
    let n = y.len();
    assert_eq!(x.len(), n);
    assert!(n > 1);

    // N.B. The possibility of duplicates are not dealt with.
    // let mut z: Vec<_> = x.iter().cloned().zip(y.iter().cloned()).collect();
    let mut z: Vec<_> = x.into_iter().zip(y.into_iter()).collect();
    z.sort_unstable_by(|(a, _), (b, _)| a.partial_cmp(b).unwrap());
    let (x, y): (Vec<_>, Vec<_>) = z.into_iter().unzip();

    let mut nu: Vec<f64> = Vec::with_capacity(n);
    nu.push(y[0]);
    let mut w: Vec<usize> = Vec::with_capacity(n);
    w.push(1);
    let mut j: usize = 0;
    let mut i: usize = 1;
    while i < n {
        j += 1;
        nu.push(y[i]);
        w.push(1);
        i += 1;
        while j > 0 && nu[j - 1] > nu[j] {
            let w_prime = w[j - 1] + w[j];
            let nu_prime = (w[j - 1] as f64 * nu[j - 1] + w[j] as f64 * nu[j]) / w_prime as f64;
            nu[j - 1] = nu_prime;
            w[j - 1] = w_prime;
            nu.pop();
            w.pop();
            j -= 1;
        }
    }
    let mut nu_out = y;
    let mut pos: usize = 0;
    let m = j + 1;
    j = 0;
    while j < m {
        let mu = nu[j];
        for _ in 0..w[j] {
            nu_out[pos] = mu;
            pos += 1
        }
        j += 1;
    }
    IsoReg { x, mu: nu_out }
}

// This assumes that `x` is sorted and that the permutation which sorts `x`
// has also been applied to `y`.
fn weighted_dup(x: &[f64], y: &[f64]) -> (Vec<f64>, Vec<f64>, Vec<usize>) {
    let n = y.len();
    assert_eq!(x.len(), n);
    let mut z: Vec<f64> = Vec::with_capacity(n);
    let mut v: Vec<f64> = Vec::with_capacity(n);
    let mut w: Vec<usize> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n {
        let a = x[i];
        let mut b = y[i];
        let mut c: usize = 1;
        i += 1;
        while i < n && x[i] == a {
            b += y[i];
            c += 1;
            i += 1;
        }
        z.push(a);
        v.push(b / c as f64);
        w.push(c);
    }
    (z, v, w)
}

pub fn isoreg_with_dup(x: Vec<f64>, y: Vec<f64>) -> IsoReg {
    // These two necessary conditions could be handled more delicately.
    let n = y.len();
    assert_eq!(x.len(), n);
    assert!(n > 1);

    let mut z: Vec<_> = x.into_iter().zip(y.into_iter()).collect();
    z.sort_unstable_by(|(a, _), (b, _)| a.partial_cmp(b).unwrap());
    let (x, y): (Vec<_>, Vec<_>) = z.into_iter().unzip();

    let (z, v, omega) = weighted_dup(&x, &y);
    let n = z.len();

    let mut nu = y;
    nu.clear();
    nu.push(v[0]);
    let mut w: Vec<usize> = Vec::with_capacity(n);
    w.push(omega[0]);
    let mut u: Vec<usize> = Vec::with_capacity(n);
    u.push(1);
    let mut j: usize = 0;
    let mut i: usize = 1;
    while i < n {
        j += 1;
        nu.push(v[i]);
        w.push(omega[i]);
        u.push(1);
        i += 1;
        while j > 0 && nu[j - 1] > nu[j] {
            let w_prime = w[j - 1] + w[j];
            let nu_prime = (w[j - 1] as f64 * nu[j - 1] + w[j] as f64 * nu[j]) / w_prime as f64;
            nu[j - 1] = nu_prime;
            w[j - 1] = w_prime;
            u[j - 1] += u[j];
            nu.pop();
            w.pop();
            u.pop();
            j -= 1;
        }
    }
    let mut nu_out = v;
    nu_out.clear();
    let m = j + 1;
    j = 0;
    while j < m {
        let mu = nu[j];
        for _ in 0..u[j] {
            nu_out.push(mu);
        }
        j += 1;
    }
    IsoReg { x: z, mu: nu_out }
}

pub fn isoreg(x: &[f64], y: &[f64], direction: Direction) -> IsoReg {
    let x = x.iter().cloned().collect();
    match direction {
        Increasing => {
            let y = y.iter().cloned().collect();
            isoreg_ltor(x, y)
        }
        Decreasing => {
            let y: Vec<_> = y.iter().cloned().map(|y_i| -y_i).collect();
            let mut iso = isoreg_ltor(x, y);
            iso.mu.iter_mut().for_each(|mu_i| *mu_i = -*mu_i);
            iso
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn isoreg_rtol_works_1() {
        let x = [0.0_f64, 2.0_f64, 4.0_f64];
        let y = [0.0_f64, 4.0_f64, 16.0_f64];

        let iso = isoreg_rtol(x.to_vec(), y.to_vec());
        assert_eq!(iso.interpolate(3.0), 10.0);
    }

    #[test]
    fn isoreg_ltor_works_1() {
        let x = [0.0_f64, 2.0_f64, 4.0_f64];
        let y = [0.0_f64, 4.0_f64, 16.0_f64];

        let iso = isoreg_ltor(x.to_vec(), y.to_vec());
        assert_eq!(iso.interpolate(3.0), 10.0);
    }

    fn vikings_data() -> (Vec<f64>, Vec<f64>) {
        let x: Vec<f64> = vec![
            37.0, 39.0, 40.0, 28.0, 37.0, 45.0, 22.0, 52.0, 37.0, 48.0, 26.0, 42.0, 22.0, 43.0,
            39.0, 36.0, 36.0, 48.0, 56.0, 37.0, 48.0, 39.0, 47.0, 36.0, 34.0, 24.0, 29.0, 45.0,
        ];
        let y: Vec<f64> = vec![
            1.0, 1.0, 1.0, 0.0, 1.0, 0.0, 1.0, 1.0, 1.0, 1.0, 1.0, 0.0, 1.0, 1.0, 1.0, 1.0, 1.0,
            0.0, 0.0, 1.0, 0.0, 1.0, 0.0, 1.0, 1.0, 1.0, 1.0, 1.0,
        ];
        (x, y)
    }

    #[test]
    fn isoreg_works_1() {
        let (x, y) = vikings_data();

        let mu: Vec<f64> = vec![
            1.0,
            1.0,
            1.0,
            1.0,
            13.0 / 14.0,
            13.0 / 14.0,
            13.0 / 14.0,
            13.0 / 14.0,
            13.0 / 14.0,
            13.0 / 14.0,
            13.0 / 14.0,
            13.0 / 14.0,
            13.0 / 14.0,
            13.0 / 14.0,
            13.0 / 14.0,
            13.0 / 14.0,
            13.0 / 14.0,
            13.0 / 14.0,
            0.5,
            0.5,
            0.5,
            0.5,
            0.4,
            0.4,
            0.4,
            0.4,
            0.4,
            0.0,
        ];

        let iso = isoreg(&x, &y, Direction::Decreasing);
        assert_eq!(iso.mu(), &mu);
    }

    #[test]
    fn weighted_dup_works() {
        let x: Vec<f64> = vec![1.0, 2.0, 2.0, 3.0, 3.0, 3.0, 4.0];
        let y: Vec<f64> = x.iter().cloned().map(|y_i| 10.0 * y_i).collect();
        let (z, v, w) = weighted_dup(&x, &y);
        assert_eq!(z, vec![1.0, 2.0, 3.0, 4.0]);
        assert_eq!(v, vec![10.0, 20.0, 30.0, 40.0]);
        assert_eq!(w, vec![1, 2, 3, 1]);

        let y: Vec<f64> = vec![5.5, 3.5, 4.5, 1.0, 2.0, 3.0, 6.0];
        let (z, v, w) = weighted_dup(&x, &y);
        assert_eq!(z, vec![1.0, 2.0, 3.0, 4.0]);
        assert_eq!(v, vec![5.5, 4.0, 2.0, 6.0]);
        assert_eq!(w, vec![1, 2, 3, 1]);

        let x: Vec<f64> = vec![1.0, 2.0, 2.0, 3.0, 3.0, 3.0];
        let y: Vec<f64> = x.iter().cloned().map(|y_i| 10.0 * y_i).collect();
        let (z, v, w) = weighted_dup(&x, &y);
        assert_eq!(z, vec![1.0, 2.0, 3.0]);
        assert_eq!(v, vec![10.0, 20.0, 30.0]);
        assert_eq!(w, vec![1, 2, 3]);

        let x: Vec<f64> = vec![2.0, 2.0, 2.0, 2.0, 2.0];
        let y: Vec<f64> = x.iter().cloned().map(|y_i| 10.0 * y_i).collect();
        let (z, v, w) = weighted_dup(&x, &y);
        assert_eq!(z, vec![2.0]);
        assert_eq!(v, vec![20.0]);
        assert_eq!(w, vec![5]);

        let x: Vec<f64> = vec![1.0];
        let y: Vec<f64> = vec![55.0];
        let (z, v, w) = weighted_dup(&x, &y);
        assert_eq!(z, vec![1.0]);
        assert_eq!(v, vec![55.0]);
        assert_eq!(w, vec![1]);

        let x: Vec<f64> = vec![];
        let y: Vec<f64> = vec![];
        let (z, v, w) = weighted_dup(&x, &y);
        assert_eq!(z, vec![]);
        assert_eq!(v, vec![]);
        assert_eq!(w, vec![]);
    }

    #[test]
    fn isoreg_with_dup_works_vikings_1() {
        let (x, mut y) = vikings_data();
        let z: Vec<f64> = vec![
            22.0, 24.0, 26.0, 28.0, 29.0, 34.0, 36.0, 37.0, 39.0, 40.0, 42.0, 43.0, 45.0, 47.0,
            48.0, 52.0, 56.0,
        ];
        let mu: Vec<f64> = vec![
            1.0,
            1.0,
            1.0,
            13.0 / 14.0,
            13.0 / 14.0,
            13.0 / 14.0,
            13.0 / 14.0,
            13.0 / 14.0,
            13.0 / 14.0,
            13.0 / 14.0,
            0.5,
            0.5,
            0.5,
            0.4,
            0.4,
            0.4,
            0.0,
        ];

        y.iter_mut().for_each(|y_i| *y_i = -*y_i);
        let iso = isoreg_with_dup(x, y);

        assert_eq!(iso.mu(), &mu.iter().map(|mu_i| -*mu_i).collect::<Vec<_>>());
        for (z_i, mu_i) in z.iter().zip(mu.iter()) {
            assert_eq!(-iso.interpolate(*z_i), *mu_i);
        }
        assert_eq!(-iso.interpolate(28.5), 13.0 / 14.0);
        assert_eq!(-iso.interpolate(41.0), ((13.0 / 14.0) + 0.5) / 2.0);
        assert_eq!(-iso.interpolate(53.0), -(-0.4 + (0.4 / 4.0) * 1.0));

        let (mut x, _) = vikings_data();
        x.sort_unstable_by(|a, b| a.partial_cmp(b).unwrap());
        let mu: Vec<f64> = vec![
            -1.0,
            -1.0,
            -1.0,
            -1.0,
            -13.0 / 14.0,
            -13.0 / 14.0,
            -13.0 / 14.0,
            -13.0 / 14.0,
            -13.0 / 14.0,
            -13.0 / 14.0,
            -13.0 / 14.0,
            -13.0 / 14.0,
            -13.0 / 14.0,
            -13.0 / 14.0,
            -13.0 / 14.0,
            -13.0 / 14.0,
            -13.0 / 14.0,
            -13.0 / 14.0,
            -0.5,
            -0.5,
            -0.5,
            -0.5,
            -0.4,
            -0.4,
            -0.4,
            -0.4,
            -0.4,
            0.0,
        ];
        for (x_i, mu_i) in x.iter().zip(mu.iter()) {
            assert_eq!(iso.interpolate(*x_i), *mu_i);
        }
    }

    #[test]
    fn online_isoreg_with_dup_works_vikings_1() {
        let (x, mut y) = vikings_data();
        let z: Vec<f64> = vec![
            22.0, 24.0, 26.0, 28.0, 29.0, 34.0, 36.0, 37.0, 39.0, 40.0, 42.0, 43.0, 45.0, 47.0,
            48.0, 52.0, 56.0,
        ];
        let mu: Vec<f64> = vec![
            1.0,
            1.0,
            1.0,
            13.0 / 14.0,
            13.0 / 14.0,
            13.0 / 14.0,
            13.0 / 14.0,
            13.0 / 14.0,
            13.0 / 14.0,
            13.0 / 14.0,
            0.5,
            0.5,
            0.5,
            0.4,
            0.4,
            0.4,
            0.0,
        ];
        y.iter_mut().for_each(|y_i| *y_i = -*y_i);

        let iso = online_isoreg_with_dup(x, y);
        for (z_i, mu_i) in z.into_iter().zip(mu.into_iter()) {
            assert_eq!(-iso.interpolate(z_i), mu_i);
        }
        assert_eq!(-iso.interpolate(28.5), 13.0 / 14.0);
        assert_eq!(-iso.interpolate(41.0), ((13.0 / 14.0) + 0.5) / 2.0);
        assert_eq!(-iso.interpolate(53.0), -(-0.4 + (0.4 / 4.0) * 1.0));
    }

    #[test]
    fn online_isoreg_with_dup_works_vikings_2() {
        let (x, mut y) = vikings_data();
        let z: Vec<f64> = vec![
            22.0, 24.0, 26.0, 28.0, 29.0, 34.0, 36.0, 37.0, 39.0, 40.0, 42.0, 43.0, 45.0, 47.0,
            48.0, 52.0, 56.0,
        ];
        let mu: Vec<f64> = vec![
            1.0,
            1.0,
            1.0,
            13.0 / 14.0,
            13.0 / 14.0,
            13.0 / 14.0,
            13.0 / 14.0,
            13.0 / 14.0,
            13.0 / 14.0,
            13.0 / 14.0,
            0.5,
            0.5,
            0.5,
            0.4,
            0.4,
            0.4,
            0.0,
        ];
        y.iter_mut().for_each(|y_i| *y_i = -*y_i);

        let mut iso = online_isoreg_with_dup(x[0..2].to_vec(), y[0..2].to_vec());
        for i in 2..x.len() {
            iso.add_point(x[i], y[i]);
        }

        for (z_i, mu_i) in z.into_iter().zip(mu.into_iter()) {
            assert_eq!(-iso.interpolate(z_i), mu_i);
        }
        assert_eq!(-iso.interpolate(28.5), 13.0 / 14.0);
        assert_eq!(-iso.interpolate(41.0), ((13.0 / 14.0) + 0.5) / 2.0);
        assert_eq!(-iso.interpolate(53.0), -(-0.4 + (0.4 / 4.0) * 1.0));
    }
}

#[derive(Debug)]
pub struct OnlineIsoReg {
    // Essential information to store
    z: Vec<f64>,
    v: Vec<f64>,
    omega: Vec<usize>,
    // The regression line
    mu: Vec<f64>,
    // Re-used temporaries
    nu: Vec<f64>,
    w: Vec<usize>,
    u: Vec<usize>,
}
pub fn online_isoreg_with_dup(x: Vec<f64>, y: Vec<f64>) -> OnlineIsoReg {
    // These two necessary conditions could be handled more delicately.
    let n = y.len();
    assert_eq!(x.len(), n);
    assert!(n > 1);

    let mut xy: Vec<_> = x.into_iter().zip(y.into_iter()).collect();
    xy.sort_unstable_by(|(a, _), (b, _)| a.partial_cmp(b).unwrap());
    let (x, y): (Vec<_>, Vec<_>) = xy.into_iter().unzip();

    let (z, v, omega) = weighted_dup(&x, &y);
    let n = z.len();

    let mut nu: Vec<f64> = Vec::with_capacity(n);
    nu.push(v[0]);
    let mut w: Vec<usize> = Vec::with_capacity(n);
    w.push(omega[0]);
    let mut u: Vec<usize> = Vec::with_capacity(n);
    u.push(1);
    let mut j: usize = 0;
    let mut i: usize = 1;
    while i < n {
        j += 1;
        nu.push(v[i]);
        w.push(omega[i]);
        u.push(1);
        i += 1;
        while j > 0 && nu[j - 1] > nu[j] {
            let w_prime = w[j - 1] + w[j];
            let nu_prime = (w[j - 1] as f64 * nu[j - 1] + w[j] as f64 * nu[j]) / w_prime as f64;
            nu[j - 1] = nu_prime;
            w[j - 1] = w_prime;
            u[j - 1] += u[j];
            nu.pop();
            w.pop();
            u.pop();
            j -= 1;
        }
    }
    let mut mu_out: Vec<f64> = Vec::with_capacity(n);
    // let mut pos: usize = 0;
    let m = j + 1;
    j = 0;
    while j < m {
        let mu = nu[j];
        for _ in 0..u[j] {
            // nu_out[pos] = mu;
            // pos += 1
            mu_out.push(mu);
        }
        j += 1;
    }
    OnlineIsoReg {
        z,
        v,
        omega,
        mu: mu_out,
        nu,
        w,
        u,
    }
}

impl OnlineIsoReg {
    pub fn interpolate(&self, x: f64) -> f64 {
        match self.z.binary_search_by(|z_j| z_j.partial_cmp(&x).unwrap()) {
            Ok(j) => {
                // An exact match on a binary search is inherently safe.
                unsafe { self.mu.get_unchecked(j).clone() }
            }
            Err(j) => {
                // We must determine where to interpolate from.
                let k = self.z.len();
                if j == 0 {
                    self.mu[1]
                        + (self.mu[0] - self.mu[1]) / (self.z[0] - self.z[1]) * (x - self.z[1])
                } else if j == k {
                    self.mu[k - 2]
                        + (self.mu[k - 1] - self.mu[k - 2]) / (self.z[k - 1] - self.z[k - 2])
                            * (x - self.z[k - 2])
                } else {
                    // x < z[j] => x - z[j] < 0
                    self.mu[j - 1]
                        + (self.mu[j] - self.mu[j - 1]) / (self.z[j] - self.z[j - 1])
                            * (x - self.z[j - 1])
                }
            }
        }
    }
    // pub fn x<'a>(&'a self) -> &'a Vec<f64> {
    //     &self.x
    // }
    // pub fn mu<'a>(&'a self) -> &'a Vec<f64> {
    //     &self.mu
    // }
    pub fn new() -> Self {
        Self {
            z: vec![],
            v: vec![],
            omega: vec![],
            mu: vec![],
            nu: vec![],
            w: vec![],
            u: vec![],
        }
    }
    pub fn add_point(&mut self, x: f64, y: f64) {
        match self.z.binary_search_by(|z_j| z_j.partial_cmp(&x).unwrap()) {
            Ok(j) => {
                let omega_prime = self.omega[j] + 1;
                let v_prime = (self.omega[j] as f64 * self.v[j] + y) / omega_prime as f64;
                self.v[j] = v_prime;
                self.omega[j] = omega_prime;
            }
            Err(j) => {
                self.v.insert(j, y);
                self.omega.insert(j, 1);
                self.z.insert(j, x);
            }
        }
        self.isoreg_ordered_nodup();
    }
    fn isoreg_ordered_nodup(&mut self) {
        self.nu.clear();
        self.w.clear();
        self.u.clear();
        let n = self.z.len();

        self.nu.push(self.v[0]);
        self.w.push(self.omega[0]);
        self.u.push(1);
        let mut j: usize = 0;
        let mut i: usize = 1;
        while i < n {
            j += 1;
            self.nu.push(self.v[i]);
            self.w.push(self.omega[i]);
            self.u.push(1);
            i += 1;
            while j > 0 && self.nu[j - 1] > self.nu[j] {
                let w_prime = self.w[j - 1] + self.w[j];
                let nu_prime = (self.w[j - 1] as f64 * self.nu[j - 1]
                    + self.w[j] as f64 * self.nu[j])
                    / w_prime as f64;
                self.nu[j - 1] = nu_prime;
                self.w[j - 1] = w_prime;
                self.u[j - 1] += self.u[j];
                self.nu.pop();
                self.w.pop();
                self.u.pop();
                j -= 1;
            }
        }
        self.mu.clear();
        let m = j + 1;
        j = 0;
        while j < m {
            let mu = self.nu[j];
            for _ in 0..self.u[j] {
                self.mu.push(mu);
            }
            j += 1;
        }
    }
}
