use std::fs::File;
use std::io::{BufRead, BufReader};

use anyhow::{anyhow, bail, Result};

fn day1() -> Result<()> {
    let file = File::open("day1.txt")?;
    let reader = BufReader::new(file);
    let mut xs = Vec::new();
    for line in reader.lines() {
        xs.push(line?.parse()?);
    }
    xs.sort();

    fn sum2(xs: &[u32], t: u32) -> Option<(usize, usize)> {
        let mut i = 0;
        let mut j = xs.len() - 1;
        while i < j {
            if xs[i] + xs[j] > t {
                j -= 1;
            } else if xs[i] + xs[j] < t {
                i += 1;
            } else {
                return Some((i, j));
            }
        }
        None
    }

    let (i, j) = sum2(xs.as_slice(), 2020).ok_or_else(|| anyhow!("no solution"))?;
    println!("{}", xs[i] * xs[j]);

    for i in 0..xs.len() - 2 {
        if let Some((j, k)) = sum2(&xs[i + 1..], 2020 - xs[i]) {
            let (j, k) = (i + j + 1, i + k + 1);
            println!("{}", xs[i] * xs[j] * xs[k]);
            return Ok(());
        }
    }
    bail!("no solution")
}

fn main() -> Result<()> {
    day1()
}
