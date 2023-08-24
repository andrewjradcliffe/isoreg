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
            nu.swap_remove(j);
            w.swap_remove(j);
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

        let iso = isoreg_rtol(&x, &y);
        assert_eq!(iso.interpolate(3.0), 10.0);
    }

    #[test]
    fn isoreg_ltor_works_1() {
        let x = [0.0_f64, 2.0_f64, 4.0_f64];
        let y = [0.0_f64, 4.0_f64, 16.0_f64];

        let iso = isoreg_rtol(&x, &y);
        assert_eq!(iso.interpolate(3.0), 10.0);
    }
}
