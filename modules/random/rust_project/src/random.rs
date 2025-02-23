use rand::Rng;

pub fn random_float(min: f64, max: f64) -> f64 {
    let mut rng = rand::rng();
    rng.random_range(min..max)
}

pub fn random_int(min: i64, max: i64) -> i64 {
    let mut rng = rand::rng();
    rng.random_range(min..max)
}
