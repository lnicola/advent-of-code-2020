use std::collections::{HashMap, HashSet, VecDeque};
use std::error::Error;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::{iter, mem};

use self::interner::Interner;

mod arith;
pub mod interner;

fn day1() -> Result<(u32, u32), Box<dyn Error>> {
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
    let p1 = xs[i] * xs[j];

    for i in 0..xs.len() - 2 {
        if let Some((j, k)) = sum2(&xs[i + 1..], 2020 - xs[i]) {
            let (j, k) = (i + j + 1, i + k + 1);
            let p2 = xs[i] * xs[j] * xs[k];
            return Ok((p1, p2));
        }
    }
    panic!("no solution")
}

fn day2() -> Result<(i32, i32), Box<dyn Error>> {
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
    Ok((valid1, valid2))
}

fn day3() -> Result<(i32, i32), Box<dyn Error>> {
    let file = File::open("day3.txt")?;
    let reader = BufReader::new(file);

    let mut map = Vec::new();
    let mut height = 0;
    for line in reader.lines() {
        map.extend_from_slice(line?.as_bytes());
        height += 1;
    }
    let width = map.len() / height;

    let run = |sx, sy| {
        let mut x = 0;
        let mut trees = 0;
        for y in (0..height).step_by(sy) {
            if map[y * width + x] == b'#' {
                trees += 1;
            }
            x += sx;
            if x >= width {
                x = x % width;
            }
        }
        trees
    };

    let trees_11 = run(1, 1);
    let trees_31 = run(3, 1);
    let trees_51 = run(5, 1);
    let trees_71 = run(7, 1);
    let trees_12 = run(1, 2);
    let p2 = trees_11 * trees_31 * trees_51 * trees_71 * trees_12;
    Ok((trees_31, p2))
}

fn day4() -> Result<(i32, i32), Box<dyn Error>> {
    let file = File::open("day4.txt")?;
    let reader = BufReader::new(file);

    const NUL: u8 = 0b0000_0000;
    const BYR: u8 = 0b0000_0001;
    const IYR: u8 = 0b0000_0010;
    const EYR: u8 = 0b0000_0100;
    const HGT: u8 = 0b0000_1000;
    const HCL: u8 = 0b0001_0000;
    const ECL: u8 = 0b0010_0000;
    const PID: u8 = 0b0100_0000;
    const ALL: u8 = 0b0111_1111;

    let mut valid1 = 0;
    let mut valid2 = 0;
    let mut has = NUL;
    let mut valid = NUL;
    for line in reader.lines().chain(iter::once(Ok(String::new()))) {
        let line = line?;
        if line.is_empty() {
            if has == ALL {
                valid1 += 1;
                if valid == ALL {
                    valid2 += 1;
                }
            }
            has = NUL;
            valid = NUL;
            continue;
        }
        for part in line.split(' ') {
            let val = &part[4..];
            match &part[..3] {
                "byr" => {
                    has |= BYR;
                    if matches!(val.parse(), Ok(1920..=2002)) {
                        valid |= BYR;
                    }
                }
                "iyr" => {
                    has |= IYR;
                    if matches!(val.parse(), Ok(2010..=2020)) {
                        valid |= IYR;
                    }
                }
                "eyr" => {
                    has |= EYR;
                    if matches!(val.parse(), Ok(2020..=2030)) {
                        valid |= EYR;
                    }
                }
                "hgt" => {
                    has |= HGT;
                    if val.len() > 2
                        && matches!(
                            (&val[val.len() - 2..], val[..val.len() - 2].parse()),
                            ("cm", Ok(150..=193)) | ("in", Ok(59..=76))
                        )
                    {
                        valid |= HGT;
                    }
                }
                "hcl" => {
                    has |= HCL;
                    if val.len() == 7
                        && val.starts_with('#')
                        && (&val[1..])
                            .chars()
                            .all(|c| c.is_ascii_digit() || c >= 'a' && c <= 'f')
                    {
                        valid |= HCL;
                    }
                }
                "ecl" => {
                    has |= ECL;
                    if matches!(val, "amb" | "blu" | "brn" | "gry" | "grn" | "hzl" | "oth") {
                        valid |= ECL;
                    }
                }
                "pid" => {
                    has |= PID;
                    if val.len() == 9 && val.chars().all(|c| c.is_ascii_digit()) {
                        valid |= PID;
                    }
                }
                _ => {}
            }
        }
    }
    Ok((valid1, valid2))
}

fn day5() -> Result<(u16, u16), Box<dyn Error>> {
    let file = File::open("day5.txt")?;
    let reader = BufReader::new(file);

    let mut max_seat_id = 0u16;
    let mut taken = [false; 1023];
    for line in reader.lines() {
        let line = line?;
        let line = line.as_bytes();
        let mut row = 0;
        let mut col = 0;
        for &ch in &line[..7] {
            row = row << 1 | (ch == b'B') as u16;
        }
        for &ch in &line[7..] {
            col = col << 1 | (ch == b'R') as u16;
        }
        let seat_id = row << 3 | col;
        max_seat_id = max_seat_id.max(seat_id);
        taken[seat_id as usize] = true;
    }
    for i in 1..=1022 {
        if !taken[i] && taken[i - 1] && taken[i + 1] {
            return Ok((max_seat_id, i as u16));
        }
    }
    panic!("no solution");
}

fn day6() -> Result<(u16, u16), Box<dyn Error>> {
    let file = File::open("day6.txt")?;
    let reader = BufReader::new(file);

    let mut count1 = 0;
    let mut count2 = 0;
    let mut answers1 = [false; 26];
    let mut answers2 = [true; 26];
    for line in reader.lines().chain(iter::once(Ok(String::new()))) {
        let line = line?;
        if line.is_empty() {
            count1 += answers1.iter().filter(|&&p| p).count() as u16;
            count2 += answers2.iter().filter(|&&p| p).count() as u16;
            answers1 = [false; 26];
            answers2 = [true; 26];
            continue;
        }
        let mut ans = [false; 26];
        for &ch in line.as_bytes() {
            answers1[(ch - b'a') as usize] = true;
            ans[(ch - b'a') as usize] = true;
        }
        for (p, &q) in answers2.iter_mut().zip(ans.iter()) {
            *p &= q;
        }
    }
    Ok((count1, count2))
}

fn day7() -> Result<(usize, usize), Box<dyn Error>> {
    let file = File::open("day7.txt")?;
    let reader = BufReader::new(file);

    let mut bag_types = Interner::new();
    let mut nestings = HashMap::new();
    let mut allowed_in = HashMap::new();
    for line in reader.lines() {
        let line = line?;
        let bag_type = line[..line.find(" bags").unwrap()].to_string();
        let contents = &line[line.find("contain ").unwrap() + 8..];
        let outer = bag_types.insert(bag_type);
        let mut bag_contents = Vec::new();
        if contents != "no other bags." {
            for inner_bag in contents.split(|c| c == ',' || c == '.') {
                if !inner_bag.is_empty() {
                    let inner_bag = inner_bag.trim();
                    let p = inner_bag.find(' ').unwrap();
                    let count = inner_bag[..p].parse::<usize>()?;
                    let p2 = inner_bag[p + 1..].find(" bag").unwrap() + p + 1;
                    let inner_type = inner_bag[p + 1..p2].to_string();
                    let inner = bag_types.insert(inner_type);
                    bag_contents.push((inner, count));
                    allowed_in.entry(inner).or_insert(Vec::new()).push(outer);
                }
            }
        }
        nestings.insert(outer, bag_contents);
    }

    let shiny_gold_bag = *bag_types.get("shiny gold").unwrap();

    let mut q = VecDeque::new();
    let mut visited = HashSet::new();
    q.push_back(shiny_gold_bag);
    let mut sol1 = HashSet::new();
    while let Some(bag) = q.pop_front() {
        visited.insert(bag);
        if let Some(bags) = allowed_in.get(&bag) {
            for &bag in bags {
                if !visited.contains(&bag) {
                    sol1.insert(bag);
                    q.push_back(bag);
                }
            }
        }
    }

    fn p2(
        bag: usize,
        nestings: &HashMap<usize, Vec<(usize, usize)>>,
        descendants: &mut [usize],
    ) -> usize {
        if descendants[bag] != usize::MAX {
            return descendants[bag];
        }

        let mut res = 1;
        if let Some(bags) = nestings.get(&bag) {
            for &(inner, count) in bags {
                res += count * p2(inner, nestings, descendants);
            }
        }
        descendants[bag] = res;
        res
    }
    let mut descendants = vec![usize::MAX; bag_types.len()];
    Ok((
        sol1.len(),
        p2(shiny_gold_bag, &nestings, &mut descendants) - 1,
    ))
}

fn day8() -> Result<(i32, i32), Box<dyn Error>> {
    #[derive(Copy, Clone)]
    enum Instruction {
        Nop(i32),
        Acc(i32),
        Jmp(i32),
    }

    let file = File::open("day8.txt")?;
    let reader = BufReader::new(file);

    let mut program = Vec::new();
    for line in reader.lines() {
        let line = line?;
        let mut it = line.split(' ');
        let opcode = it.next().unwrap();
        let param = it.next().unwrap().parse()?;
        let instruction = match opcode {
            "nop" => Instruction::Nop(param),
            "acc" => Instruction::Acc(param),
            "jmp" => Instruction::Jmp(param),
            _ => unreachable!(),
        };
        program.push(instruction);
    }

    enum ExecutionResult {
        Loop(i32),
        Finished(i32),
    }

    fn run(program: &[Instruction], executed: &mut [bool]) -> ExecutionResult {
        let mut pc = 0;
        let mut acc = 0;
        while !executed[pc as usize] {
            executed[pc as usize] = true;
            match program[pc as usize] {
                Instruction::Nop(_) => pc += 1,
                Instruction::Acc(p) => {
                    acc += p;
                    pc += 1
                }
                Instruction::Jmp(r) => pc = pc + r as isize,
            }
            if pc < 0 || pc >= program.len() as isize {
                return ExecutionResult::Finished(acc);
            }
        }
        ExecutionResult::Loop(acc)
    }

    let mut executed = vec![false; program.len()];
    let p1 = match run(&program, executed.as_mut_slice()) {
        ExecutionResult::Loop(acc) => acc,
        _ => unreachable!(),
    };

    for i in 0..program.len() {
        for p in &mut executed {
            *p = false;
        }

        let saved = program[i];
        match program[i] {
            Instruction::Nop(acc) => program[i] = Instruction::Jmp(acc),
            Instruction::Jmp(r) => program[i] = Instruction::Nop(r),
            _ => {}
        }
        if let ExecutionResult::Finished(acc) = run(&program, executed.as_mut_slice()) {
            return Ok((p1, acc));
        }
        program[i] = saved;
    }
    panic!("no solution");
}

fn day9() -> Result<(u64, u64), Box<dyn Error>> {
    let file = File::open("day9.txt")?;
    let reader = BufReader::new(file);
    let mut xs = Vec::new();
    for line in reader.lines() {
        xs.push(line?.parse::<u64>()?);
    }
    const WINDOW_SIZE: usize = 25;
    let mut p1 = 0;
    for i in WINDOW_SIZE..xs.len() {
        let mut ok = false;
        'outer: for j in i - WINDOW_SIZE..i - 1 {
            for k in j + 1..i {
                if xs[i] == xs[j] + xs[k] {
                    ok = true;
                    break 'outer;
                }
            }
        }
        if !ok {
            p1 = xs[i];
            break;
        }
    }
    let mut prefix_sums = vec![0; xs.len() + 1];
    for i in 1..xs.len() {
        prefix_sums[i] = prefix_sums[i - 1] + xs[i - 1];
    }
    for i in 0..xs.len() - 1 {
        for j in i..xs.len() {
            if prefix_sums[j] - prefix_sums[i] == p1 {
                let p2 = xs[i..j].iter().min().unwrap() + xs[i..j].iter().max().unwrap();
                return Ok((p1, p2));
            }
        }
    }
    panic!("no solution");
}

fn day10() -> Result<(usize, usize), Box<dyn Error>> {
    let file = File::open("day10.txt")?;
    let reader = BufReader::new(file);
    let mut xs = Vec::new();
    for line in reader.lines() {
        xs.push(line?.parse::<usize>()?);
    }
    xs.sort();
    let mut cd1 = (xs[0] == 1) as usize;
    let mut cd3 = 1 + (xs[0] == 3) as usize;
    for w in xs.windows(2) {
        match w[1] - w[0] {
            1 => cd1 += 1,
            3 => cd3 += 1,
            _ => {}
        }
    }
    let mut s = vec![0usize; xs.last().unwrap() + 1];
    s[0] = 1;
    for &x in &xs {
        for i in x.saturating_sub(3)..x {
            s[x] += s[i];
        }
    }
    Ok((cd1 * cd3, *s.last().unwrap()))
}

fn day11() -> Result<(usize, usize), Box<dyn Error>> {
    let file = File::open("day11.txt")?;
    let reader = BufReader::new(file);

    let mut map = Vec::new();
    let mut height = 0;
    for line in reader.lines() {
        map.extend_from_slice(line?.as_bytes());
        height += 1;
    }
    let width = map.len() / height;

    const D: [(isize, isize); 8] = [
        (-1, 0),
        (1, 0),
        (0, -1),
        (0, 1),
        (-1, -1),
        (1, 1),
        (1, -1),
        (-1, 1),
    ];

    fn transition(current: u8, neighbors: usize, max_neighbors: usize) -> u8 {
        match current {
            b'.' => b'.',
            b'L' if neighbors == 0 => b'#',
            b'L' => b'L',
            b'#' if neighbors < max_neighbors => b'#',
            b'#' => b'L',
            _ => unreachable!(),
        }
    }

    let orig = map.clone();
    let mut new = vec![0; map.len()];
    loop {
        for i in 0..height {
            for j in 0..width {
                let count = D
                    .iter()
                    .map(|&(dx, dy)| (j as isize + dx, i as isize + dy))
                    .filter(|(x, y)| {
                        (0..width as isize).contains(x) && (0..height as isize).contains(y)
                    })
                    .map(|(x, y)| (x as usize, y as usize))
                    .filter(|(x, y)| map[y * width + x] == b'#')
                    .count();
                new[i * width + j] = transition(map[i * width + j], count, 4);
            }
        }
        if new == map {
            break;
        }
        mem::swap(&mut map, &mut new);
    }
    let p1 = map.iter().filter(|&&c| c == b'#').count();

    map = orig;
    loop {
        fn first(
            map: &[u8],
            width: usize,
            height: usize,
            x: usize,
            y: usize,
            dx: isize,
            dy: isize,
        ) -> u8 {
            let mut x = x as isize;
            let mut y = y as isize;
            loop {
                x += dx;
                y += dy;
                if !(0..width as isize).contains(&x) || !(0..height as isize).contains(&y) {
                    return 0;
                }
                let x = x as usize;
                let y = y as usize;
                match map[y * width + x as usize] {
                    b'#' => {
                        return b'#';
                    }
                    b'L' => {
                        return b'L';
                    }
                    _ => {}
                }
            }
        }
        for i in 0..height {
            for j in 0..width {
                let count = D
                    .iter()
                    .map(|&(dx, dy)| first(&map, width, height, j, i, dx, dy))
                    .filter(|&s| s == b'#')
                    .count();

                new[i * width + j] = transition(map[i * width + j], count, 5);
            }
        }
        if new == map {
            break;
        }
        mem::swap(&mut map, &mut new);
    }
    let p2 = map.iter().filter(|&&c| c == b'#').count();
    Ok((p1, p2))
}

fn day12() -> Result<(i32, i32), Box<dyn Error>> {
    let file = File::open("day12.txt")?;
    let reader = BufReader::new(file);

    let mut x1 = 0;
    let mut y1 = 0;
    let mut a = 3;
    let mut x2 = 0;
    let mut y2 = 0;
    let mut xw = 10;
    let mut yw = 1;

    const D: [(i32, i32); 4] = [(0, 1), (-1, 0), (0, -1), (1, 0)];
    fn rot(x: i32, y: i32, a: usize) -> (i32, i32) {
        const SIN: [i32; 4] = [0, 1, 0, -1];
        const COS: [i32; 4] = [1, 0, -1, 0];
        (x * COS[a] - y * SIN[a], x * SIN[a] + y * COS[a])
    }

    for line in reader.lines() {
        let line = line?;
        let c = line.as_bytes()[0];
        let d = line[1..].parse::<i32>()?;
        match c {
            b'N' => {
                y1 += d;
                yw += d;
            }
            b'W' => {
                x1 -= d;
                xw -= d;
            }
            b'S' => {
                y1 -= d;
                yw -= d;
            }
            b'E' => {
                x1 += d;
                xw += d;
            }
            b'L' => {
                let d = (d / 90) as usize;
                a = (a + d) % 4;
                let r = rot(xw, yw, d as usize);
                xw = r.0;
                yw = r.1;
            }
            b'R' => {
                let d = (d / 90) as usize;
                a = (4 + a - d) % 4;
                let r = rot(xw, yw, 4 - d as usize);
                xw = r.0;
                yw = r.1;
            }
            b'F' => {
                x1 += d * D[a].0;
                y1 += d * D[a].1;
                x2 += d * xw;
                y2 += d * yw;
            }
            _ => unreachable!(),
        }
    }

    Ok((x1.abs() + y1.abs(), x2.abs() + y2.abs()))
}

fn day13() -> Result<(i64, i64), Box<dyn Error>> {
    let file = File::open("day13.txt")?;
    let mut reader = BufReader::new(file);
    let mut s = String::new();
    reader.read_line(&mut s)?;
    let earliest = s.trim_end().parse::<i64>()?;
    s.clear();
    reader.read_line(&mut s)?;
    let mut ids = Vec::new();
    for x in s.split(',') {
        let id = match x {
            "x" => 0,
            x => x.trim_end().parse()?,
        };
        ids.push(id);
    }
    let p1 = ids
        .iter()
        .filter(|&&id| id != 0)
        .map(|&id| (id, id - earliest % id))
        .min_by_key(|p| p.1)
        .map(|(id, wait)| id * wait)
        .unwrap();
    let mut residues = Vec::new();
    let mut modulii = Vec::new();
    for (p, &id) in ids.iter().enumerate() {
        if id != 0 {
            residues.push((id - p as i64 % id) as i64);
            modulii.push(id as i64);
        }
    }
    let p2 = arith::chinese_remainder(residues.as_slice(), modulii.as_slice()).unwrap();
    Ok((p1, p2))
}

fn day14() -> Result<(i64, i64), Box<dyn Error>> {
    let file = File::open("day14.txt")?;
    let mut reader = BufReader::new(file);
    let mut s = String::new();
    let mut and_mask = !0u64;
    let mut or_mask = 0;
    let mut mem = HashMap::new();
    while reader.read_line(&mut s)? > 0 {
        if s.starts_with("mask = ") {
            and_mask = u64::from_str_radix(
                &(s[7..]
                    .trim_end()
                    .chars()
                    .map(|c| if c == 'X' { '1' } else { c })
                    .collect::<String>()),
                2,
            )?;
            or_mask = u64::from_str_radix(
                &(s[7..]
                    .trim_end()
                    .chars()
                    .map(|c| if c == 'X' { '0' } else { c })
                    .collect::<String>()),
                2,
            )?;
        } else {
            let p1 = s.find(']').unwrap();
            let addr = (&s[4..])[..p1 - 4].parse::<u64>()?;
            let p2 = s.find('=').unwrap();
            let val = u64::from_str_radix(&s.trim_end()[p2 + 2..], 10)?;
            let val = val & and_mask | or_mask;
            mem.insert(addr, val);
        }
        s.clear();
    }
    dbg!(mem.values().sum::<u64>());

    let file = File::open("day14.txt")?;
    let mut reader = BufReader::new(file);
    let mut s = String::new();
    let mut or_mask = 0;
    let mut floating_mask = 0;
    let mut mem = HashMap::new();
    while reader.read_line(&mut s)? > 0 {
        if s.starts_with("mask = ") {
            or_mask = u64::from_str_radix(
                &(s[7..]
                    .trim_end()
                    .chars()
                    .map(|c| if c == '1' { '1' } else { '0' })
                    .collect::<String>()),
                2,
            )?;
            floating_mask = u64::from_str_radix(
                &(s[7..]
                    .trim_end()
                    .chars()
                    .map(|c| if c == 'X' { '1' } else { '0' })
                    .collect::<String>()),
                2,
            )?;
        } else {
            let p1 = s.find(']').unwrap();
            let mut addr = (&s[4..][..p1 - 4]).parse::<u64>()?;
            let p2 = s.find('=').unwrap();
            let val = u64::from_str_radix(&s.trim_end()[p2 + 2..], 10)?;
            addr = addr & !floating_mask | or_mask;
            let floating_bits = floating_mask.count_ones();
            for floating in 0..(1 << floating_bits) {
                let mut f = floating;
                let mut mask = floating_mask;
                let mut m = 0;
                let mut s = 0;
                while f > 0 {
                    if mask & 1 == 1 {
                        m |= (f & 1) << s;
                        f >>= 1;
                    } else {
                    }
                    mask >>= 1;
                    s += 1;
                }
                mem.insert(addr | m, val);
            }
        }
        s.clear();
    }
    dbg!(mem.values().sum::<u64>());
    Ok((0, 0))
}

fn main() -> Result<(), Box<dyn Error>> {
    assert_eq!(day1()?, (539851, 212481360));
    assert_eq!(day2()?, (556, 605));
    assert_eq!(day3()?, (257, 1744787392));
    assert_eq!(day4()?, (256, 198));
    assert_eq!(day5()?, (947, 636));
    assert_eq!(day6()?, (6565, 3137));
    assert_eq!(day7()?, (161, 30899));
    assert_eq!(day8()?, (1941, 2096));
    assert_eq!(day9()?, (1639024365, 219202240));
    assert_eq!(day10()?, (1625, 3100448333024));
    assert_eq!(day11()?, (2283, 2054));
    assert_eq!(day12()?, (904, 18747));
    assert_eq!(day13()?, (2545, 266204454441577));
    day14()?;
    Ok(())
}
