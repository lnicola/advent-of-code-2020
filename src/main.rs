use std::error::Error;
use std::fs::File;
use std::io::{BufRead, BufReader};

fn day1() -> Result<(), Box<dyn Error>> {
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

    let (i, j) = sum2(xs.as_slice(), 2020).expect("no solution");
    print!("{} ", xs[i] * xs[j]);

    for i in 0..xs.len() - 2 {
        if let Some((j, k)) = sum2(&xs[i + 1..], 2020 - xs[i]) {
            let (j, k) = (i + j + 1, i + k + 1);
            println!("{}", xs[i] * xs[j] * xs[k]);
            return Ok(());
        }
    }
    panic!("no solution")
}

fn day2() -> Result<(), Box<dyn Error>> {
    let file = File::open("day2.txt")?;
    let reader = BufReader::new(file);
    let mut valid1 = 0;
    let mut valid2 = 0;
    for line in reader.lines() {
        let line = line?;
        let mut it = line.split(|c| c == '-' || c == ' ' || c == ':');
        let pos1 = it.next().unwrap().parse()?;
        let pos2 = it.next().unwrap().parse()?;
        let ch = it.next().unwrap().as_bytes()[0];
        it.next();
        let password = it.next().unwrap().as_bytes();

        let count = password.iter().filter(|&&c| c == ch).count();
        if count >= pos1 && count <= pos2 {
            valid1 += 1;
        }
        if (password[pos1 - 1] == ch) != (password[pos2 - 1] == ch) {
            valid2 += 1;
        }
    }
    println!("{} {}", valid1, valid2);
    Ok(())
}

fn main() -> Result<(), Box<dyn Error>> {
    day1()?;
    day2()?;
    Ok(())
}
