use rayon::prelude::*;
use std::collections::{BTreeMap, BTreeSet, HashSet, VecDeque};

const CHALLENGE: &[u8] = include_bytes!("../challenge.bin");
const MASK: u16 = 32767;

#[derive(Clone, Eq, PartialEq, Hash)]
struct Vm {
    memory: Memory,
    register: [u16; 8],
    stack: Vec<u16>,
    ip: usize,
    calls: BTreeMap<u16, BTreeSet<u16>>,
}

#[derive(Clone, Eq, PartialEq, Hash)]
struct Memory(Vec<u16>);

impl std::ops::Index<u16> for Memory {
    type Output = u16;
    fn index(&self, i: u16) -> &Self::Output {
        &self.0[i as usize]
    }
}

impl std::ops::IndexMut<u16> for Memory {
    fn index_mut(&mut self, i: u16) -> &mut Self::Output {
        let i = i as usize;
        if i >= self.0.len() {
            self.0.resize(i + 1, 0);
        }
        &mut self.0[i]
    }
}

impl Memory {
    /// Reads the value from the instruction pointer, incrementing it
    fn val(&self, ip: &mut usize) -> Value {
        let v = self.0[*ip].into();
        *ip += 1;
        v
    }

    /// Reads a register index at the instruction pointer, incrementing it
    fn reg(&self, ip: &mut usize) -> Register {
        let v = self.val(ip);
        let Value::Register(reg) = v else {
            panic!("not a register: {v:?}");
        };
        reg
    }
    /// Reads the next opcode from the machine, incrementing `ip`
    fn read(&self, ip: &mut usize) -> Op {
        let op = self.0[*ip];
        *ip += 1;
        match op {
            0 => Op::Halt,
            1 => {
                let a = self.reg(ip);
                let b = self.val(ip);
                Op::Set(a, b)
            }
            2 => {
                let a = self.val(ip);
                Op::Push(a)
            }
            3 => {
                let a = self.reg(ip);
                Op::Pop(a)
            }
            4 => {
                let a = self.reg(ip);
                let b = self.val(ip);
                let c = self.val(ip);
                Op::Eq(a, b, c)
            }
            5 => {
                let a = self.reg(ip);
                let b = self.val(ip);
                let c = self.val(ip);
                Op::Gt(a, b, c)
            }
            6 => {
                let a = self.val(ip);
                Op::Jmp(a)
            }
            7 => {
                let a = self.val(ip);
                let b = self.val(ip);
                Op::Jt(a, b)
            }
            8 => {
                let a = self.val(ip);
                let b = self.val(ip);
                Op::Jf(a, b)
            }
            9 => {
                let a = self.reg(ip);
                let b = self.val(ip);
                let c = self.val(ip);
                Op::Add(a, b, c)
            }
            10 => {
                let a = self.reg(ip);
                let b = self.val(ip);
                let c = self.val(ip);
                Op::Mult(a, b, c)
            }
            11 => {
                let a = self.reg(ip);
                let b = self.val(ip);
                let c = self.val(ip);
                Op::Mod(a, b, c)
            }
            12 => {
                let a = self.reg(ip);
                let b = self.val(ip);
                let c = self.val(ip);
                Op::And(a, b, c)
            }
            13 => {
                let a = self.reg(ip);
                let b = self.val(ip);
                let c = self.val(ip);
                Op::Or(a, b, c)
            }
            14 => {
                let a = self.reg(ip);
                let b = self.val(ip);
                Op::Not(a, b)
            }
            15 => {
                let a = self.reg(ip);
                let b = self.val(ip);
                Op::Rmem(a, b)
            }
            16 => {
                let a = self.val(ip);
                let b = self.val(ip);
                Op::Wmem(a, b)
            }
            17 => {
                let a = self.val(ip);
                Op::Call(a)
            }
            18 => Op::Ret,
            19 => {
                let a = self.val(ip);
                Op::Out(a)
            }
            20 => {
                let a = self.reg(ip);
                Op::In(a)
            }
            21 => Op::Noop,
            i => Op::Unknown(i),
        }
    }

    /// Disassemble a function beginning at the given instruction
    #[allow(unused)]
    fn disassemble(&self, ip: usize) {
        let mut seen = BTreeMap::new();
        let mut todo = vec![ip];
        while let Some(mut ip) = todo.pop() {
            let prev_ip = ip;
            let op = self.read(&mut ip);
            if seen.insert(prev_ip, op).is_none() {
                if !matches!(op, Op::Ret) {
                    todo.push(ip);
                }
                match op {
                    Op::Jmp(Value::Literal(a)) => todo.push(a as usize),
                    Op::Jt(_, Value::Literal(a)) => todo.push(a as usize),
                    Op::Jf(_, Value::Literal(a)) => todo.push(a as usize),
                    Op::Jmp(..) | Op::Jt(..) | Op::Jf(..) => print!("OH NO"),
                    _ => (),
                }
            }
        }
        for (ip, op) in seen {
            println!("{ip}: {op}");
        }
    }

    /// Disassemble all functions found in program
    #[allow(unused)]
    fn disassemble_all(&self, calls: &BTreeMap<u16, BTreeSet<u16>>) {
        let mut seen: BTreeMap<usize, BTreeMap<usize, Op>> = BTreeMap::new();
        let mut todo = BTreeSet::new();
        todo.insert((0, 0));
        todo.insert((2756, 2756));
        todo.extend(
            calls
                .values()
                .flat_map(|v| v.iter().map(|k| (*k as usize, *k as usize))),
        );
        while let Some((base, mut ip)) = todo.pop_first() {
            let prev_ip = ip;
            let op = self.read(&mut ip);
            if seen.entry(base).or_default().insert(prev_ip, op).is_none() {
                if !matches!(op, Op::Ret) {
                    todo.insert((base, ip));
                }
                match op {
                    Op::Jmp(Value::Literal(a)) => {
                        if a != 2756 {
                            todo.insert((base, a as usize));
                        }
                    }
                    Op::Jt(_, Value::Literal(a)) => {
                        todo.insert((base, a as usize));
                    }
                    Op::Jf(_, Value::Literal(a)) => {
                        todo.insert((base, a as usize));
                    }
                    Op::Jmp(..) | Op::Jt(..) | Op::Jf(..) => print!("OH NO"),
                    Op::Call(Value::Literal(a)) => {
                        todo.insert((a as usize, a as usize));
                    }
                    _ => (),
                }
            }
        }
        let mut already_printed: BTreeSet<usize> = BTreeSet::new();
        for (base, instructions) in &seen {
            if instructions.keys().any(|i| already_printed.contains(i)) {
                continue;
            }
            println!("--------------------------------------------------\n");
            println!("{base}:");
            let mut known_reg_values = BTreeMap::new();
            let mut prev_string = String::new();
            let mut prev = *instructions.first_key_value().unwrap().0;
            for (&ip, &op) in instructions {
                if ip != prev || (seen.contains_key(&ip) && ip != *base) {
                    break;
                }
                prev = ip + op.len();

                already_printed.insert(ip);
                print!("{ip}: {op}");
                if let Op::Call(Value::Register(..)) = op {
                    if let Some(t) = calls.get(&ip.try_into().unwrap()) {
                        println!(" {:?}", t);
                    } else {
                        println!(" [?]");
                    }
                } else if matches!(op, Op::Call(Value::Literal(1540)))
                    && known_reg_values.contains_key(&0)
                {
                    let r0 = known_reg_values[&0] as usize;
                    let len = self.0[r0] as usize;
                    print!(" \"");
                    let mut printed_newline = false;
                    if r0 + 1 + len <= self.0.len() {
                        for c in &self.0[r0 + 1..][..len] {
                            let c = char::from_u32(*c as u32).unwrap();
                            print!("{}", c.escape_default());
                        }
                    } else {
                        print!("??");
                    }
                    println!(" \"");
                } else if let Op::Out(Value::Literal(c)) = op {
                    let c = char::from_u32(c as u32).unwrap();
                    if c == '\n' {
                        if !prev_string.is_empty() {
                            println!(" {prev_string:?}");
                            prev_string.clear();
                        } else {
                            println!();
                        }
                    } else {
                        prev_string.push(c);
                        println!();
                    }
                } else if matches!(op, Op::Call(Value::Literal(1480)))
                    && known_reg_values.contains_key(&0)
                    && known_reg_values.get(&1) == Some(&1553) // xor print
                    && known_reg_values.contains_key(&2)
                {
                    let r0 = known_reg_values[&0] as usize;
                    let key = known_reg_values[&2];
                    let len = self.0[r0];
                    print!(" \"");
                    let mut printed_newline = false;
                    if r0 + 1 + len as usize <= self.0.len() {
                        for i in &self.0[r0 + 1..][..len as usize] {
                            let c = i ^ key;
                            let c = char::from_u32(c as u32).unwrap();
                            print!("{}", c.escape_default());
                        }
                    } else {
                        print!("??");
                    }
                    println!("\"");
                } else {
                    println!();
                }

                match op {
                    Op::Set(Register(i), Value::Literal(v)) => {
                        known_reg_values.insert(i, v);
                    }
                    Op::Add(
                        Register(i),
                        Value::Literal(a),
                        Value::Literal(b),
                    ) => {
                        known_reg_values.insert(i, a.wrapping_add(b) & 0x7FFF);
                    }
                    Op::Pop(r) => {
                        let _ = known_reg_values.remove(&r.0);
                    }
                    Op::Call(..) => {
                        known_reg_values.clear();
                    }
                    _ => (),
                }
            }
            println!();
        }
    }

    /// Disassemble all functions found in program
    #[allow(unused)]
    fn disassemble_all_html(&self, calls: &BTreeMap<u16, BTreeSet<u16>>) {
        let mut seen: BTreeMap<usize, BTreeMap<usize, Op>> = BTreeMap::new();
        let mut todo = BTreeSet::new();
        let mut html = std::fs::File::create("out.html").unwrap();
        use std::io::Write;
        write!(
            &mut html,
            r#"
<!DOCTYPE html>
<html lang="en">

<head>
<meta charset="utf-8">
<title>The Annotated Synacor Challenge</title>
<style>
body {{
  font-family: Inconsolata, "Courier New", monospace;
  background-color: #282b2e;
  color: #e0e2e4;
}}
.op {{
  color: #93c763;
}}
.unknown {{
  color: #818e96;
}}
.comment {{
  color: #818e96;
}}
.line {{
  color: #ffcd22;
}}
.lit {{
  color: #ffcd22;
}}
.char {{
  color: #ec7600;
}}
.text {{
  color: #8cbbad;
}}
.reg {{
  color: #a082bd;
}}
a {{
  text-decoration: none;
  border-bottom:1px solid #ffcd22;
}}
</style>
<link href="/fonts/inconsolata/v30/inconsolata.css" rel="stylesheet">
</head>

<body>
"#
        );

        let out = todo.insert((0, 0));
        todo.insert((2756, 2756));
        todo.extend(
            calls
                .values()
                .flat_map(|v| v.iter().map(|k| (*k as usize, *k as usize))),
        );
        while let Some((base, mut ip)) = todo.pop_first() {
            let prev_ip = ip;
            let op = self.read(&mut ip);
            if seen.entry(base).or_default().insert(prev_ip, op).is_none() {
                if !matches!(op, Op::Ret) {
                    todo.insert((base, ip));
                }
                match op {
                    Op::Jmp(Value::Literal(a)) => {
                        if a != 2756 {
                            todo.insert((base, a as usize));
                        }
                    }
                    Op::Jt(_, Value::Literal(a)) => {
                        todo.insert((base, a as usize));
                    }
                    Op::Jf(_, Value::Literal(a)) => {
                        todo.insert((base, a as usize));
                    }
                    Op::Jmp(..) | Op::Jt(..) | Op::Jf(..) => print!("OH NO"),
                    Op::Call(Value::Literal(a)) => {
                        todo.insert((a as usize, a as usize));
                    }
                    Op::Call(Value::Register(..)) => {
                        if let Some(t) = calls.get(&ip.try_into().unwrap()) {
                            for &t in t {
                                todo.insert((t as usize, t as usize));
                            }
                        }
                    }
                    _ => (),
                }
            }
        }
        let mut already_printed: BTreeSet<usize> = BTreeSet::new();
        for (base, instructions) in &seen {
            if instructions.keys().any(|i| already_printed.contains(i)) {
                continue;
            }
            writeln!(&mut html, "<br>");
            writeln!(&mut html, "<div>");
            if let Some(name) = addr_to_name(*base as u16) {
                writeln!(
                    &mut html,
                    "<span class=\"comment\">{name}:</span><br>"
                );
            }
            let mut known_reg_values = BTreeMap::new();
            let mut prev_string = String::new();
            let mut prev = *instructions.first_key_value().unwrap().0;
            for (&ip, &op) in instructions {
                if ip != prev || (seen.contains_key(&ip) && ip != *base) {
                    break;
                }
                prev = ip + op.len();

                already_printed.insert(ip);
                write!(
                    &mut html,
                    "<span class=\"line\" id=\"f{ip}\">{ip}</span>:",
                );
                for i in format!("{ip}").len()..5 {
                    write!(&mut html, "&nbsp;");
                }

                write!(&mut html, "{}", HtmlOp(op));
                if let Op::Call(Value::Register(..)) = op {
                    if let Some(t) = calls.get(&ip.try_into().unwrap()) {
                        for (i, t) in t.iter().enumerate() {
                            if i > 0 {
                                write!(&mut html, ", ");
                            }
                            write!(
                                &mut html,
                                " {}",
                                HtmlJump(Value::Literal(*t))
                            );
                        }
                    } else {
                        write!(&mut html, " [?]");
                    }
                } else if matches!(op, Op::Call(Value::Literal(1540)))
                    && known_reg_values.contains_key(&0)
                {
                    let r0 = known_reg_values[&0] as usize;
                    let len = self.0[r0] as usize;
                    write!(&mut html, " <span class=\"text\">\"");
                    let mut printed_newline = false;
                    if r0 + 1 + len <= self.0.len() {
                        for c in &self.0[r0 + 1..][..len] {
                            let c = char::from_u32(*c as u32).unwrap();
                            write!(&mut html, "{}", c.escape_default());
                        }
                    } else {
                        write!(&mut html, "??");
                    }
                    writeln!(&mut html, " \"</span>");
                } else if let Op::Out(Value::Literal(c)) = op {
                    let c = char::from_u32(c as u32).unwrap();
                    if c == '\n' {
                        if !prev_string.is_empty() {
                            write!(
                                &mut html,
                                " <span class=\"text\">{prev_string:?}</span>"
                            );
                            prev_string.clear();
                        }
                    } else {
                        prev_string.push(c);
                    }
                } else if matches!(op, Op::Call(Value::Literal(1480)))
                    && known_reg_values.contains_key(&0)
                    && known_reg_values.get(&1) == Some(&1553) // xor print
                    && known_reg_values.contains_key(&2)
                {
                    let r0 = known_reg_values[&0] as usize;
                    let key = known_reg_values[&2];
                    let len = self.0[r0];
                    write!(&mut html, " <span class=\"text\">\"");
                    let mut printed_newline = false;
                    if r0 + 1 + len as usize <= self.0.len() {
                        for i in &self.0[r0 + 1..][..len as usize] {
                            let c = i ^ key;
                            let c = char::from_u32(c as u32).unwrap();
                            write!(&mut html, "{}", c.escape_default());
                        }
                    } else {
                        write!(&mut html, "??");
                    }
                    write!(&mut html, "\"</span>");
                }

                match op {
                    Op::Set(Register(i), Value::Literal(v)) => {
                        known_reg_values.insert(i, v);
                    }
                    Op::Add(
                        Register(i),
                        Value::Literal(a),
                        Value::Literal(b),
                    ) => {
                        known_reg_values.insert(i, a.wrapping_add(b) & 0x7FFF);
                    }
                    Op::Pop(r) => {
                        let _ = known_reg_values.remove(&r.0);
                    }
                    Op::Call(..) => {
                        known_reg_values.clear();
                    }
                    _ => (),
                }

                if !matches!(op, Op::Out(Value::Literal(..))) {
                    prev_string.clear();
                }
                writeln!(&mut html, "<br>");
            }
            writeln!(&mut html, "</div>");
        }
        write!(&mut html, "</body></html>");
    }
}

#[derive(Copy, Clone, Debug)]
enum Op {
    Halt,
    Set(Register, Value),
    Push(Value),
    Pop(Register),
    Eq(Register, Value, Value),
    Gt(Register, Value, Value),
    Jmp(Value),
    Jt(Value, Value),
    Jf(Value, Value),
    Add(Register, Value, Value),
    Mult(Register, Value, Value),
    Mod(Register, Value, Value),
    And(Register, Value, Value),
    Or(Register, Value, Value),
    Not(Register, Value),
    Rmem(Register, Value),
    Wmem(Value, Value),
    Call(Value),
    Ret,
    Out(Value),
    In(Register),
    Noop,
    Unknown(u16),
}

impl Op {
    fn len(&self) -> usize {
        match self {
            Op::Halt => 1,
            Op::Set(..) => 3,
            Op::Push(..) => 2,
            Op::Pop(..) => 2,
            Op::Eq(..) => 4,
            Op::Gt(..) => 4,
            Op::Jmp(..) => 2,
            Op::Jt(..) => 3,
            Op::Jf(..) => 3,
            Op::Add(..) => 4,
            Op::Mult(..) => 4,
            Op::Mod(..) => 4,
            Op::And(..) => 4,
            Op::Or(..) => 4,
            Op::Not(..) => 3,
            Op::Rmem(..) => 3,
            Op::Wmem(..) => 3,
            Op::Call(..) => 2,
            Op::Ret => 1,
            Op::Out(..) => 2,
            Op::In(..) => 2,
            Op::Noop => 1,
            Op::Unknown(..) => 1,
        }
    }
}

impl std::fmt::Display for Op {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Op::Halt => write!(f, "halt"),
            Op::Set(a, b) => write!(f, "{a} = {b}"),
            Op::Push(a) => write!(f, "push {a}"),
            Op::Pop(a) => write!(f, "pop  {a}"),
            Op::Eq(a, b, c) => write!(f, "{a}  = {b} == {c}"),
            Op::Gt(a, b, c) => write!(f, "{a} = {b} > {c}"),
            Op::Jmp(a) => write!(f, "jmp  {a}"),
            Op::Jt(a, b) => write!(f, "jt   {a} {b}"),
            Op::Jf(a, b) => write!(f, "jf   {a} {b}"),
            Op::Add(a, b, c) => write!(f, "{a} = {b} + {c}"),
            Op::Mult(a, b, c) => write!(f, "{a} = {b} * {c}"),
            Op::Mod(a, b, c) => write!(f, "{a} = {b} % {c}"),
            Op::And(a, b, c) => write!(f, "{a} = {b} & {c}"),
            Op::Or(a, b, c) => write!(f, "{a} = {b} | {c}"),
            Op::Not(a, b) => write!(f, "{a} = !{b}"),
            Op::Rmem(a, b) => write!(f, "rmem {a} {b}"),
            Op::Wmem(a, b) => write!(f, "wmem {a} {b}"),
            Op::Call(a) => write!(f, "call {a}"),
            Op::Ret => write!(f, "ret"),
            Op::Out(a) => match a {
                Value::Literal(c) => {
                    write!(f, "out  {:?}", char::from_u32(*c as u32).unwrap())
                }
                Value::Register(r) => write!(f, "out  {r}"),
            },
            Op::In(a) => write!(f, "in   {a}"),
            Op::Noop => write!(f, "noop"),
            Op::Unknown(a) => write!(f, "[{a}]"),
        }
    }
}

struct HtmlOp(Op);
struct HtmlReg(Register);
struct HtmlValue(Value);
struct HtmlJump(Value);

impl std::fmt::Display for HtmlReg {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "<span class=\"reg\">{}</span>", self.0)
    }
}

impl std::fmt::Display for HtmlValue {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self.0 {
            Value::Register(r) => write!(f, "{}", HtmlReg(r)),
            Value::Literal(i) => write!(f, "<span class=\"lit\">{i}</span>"),
        }
    }
}

fn addr_to_name(addr: u16) -> Option<&'static str> {
    let out = match addr {
        0 => "self-test",
        1480 => "map",
        1540 => "print",
        1550 => "putc",
        1553 => "xor-putc",
        1689 => "strcmp",
        1745 => "decrypt-data",
        2147 => "xor",
        2756 => "game-loop",
        2986 => "look",
        1789 => "read-user-input",
        1863 => "print-code",
        5836 => "print-list-item",
        3422 => "take-item",
        3590 => "use-item",
        4555 => "vault-door",
        4742 => "use-tablet",
        4821 => "use-can",
        4907 => "use-lantern",
        4999 => "use-coin",
        5467 => "use-teleporter",
        5743 => "use-mirror",
        2023 => "print-number",
        5382 => "use-red-coin",
        5399 => "use-corroded-coin",
        5416 => "use-shiny-coin",
        5433 => "use-concave-coin",
        5450 => "use-blue-coin",
        4682 => "reset-orb",
        2171 => "add-with-overflow-check",
        2180 => "sub-with-overflow-check",
        2200 => "mul-with-overflow-check",
        4301 => "orb-enter-number-room",
        4240 => "orb-enter-symbol-room",
        _ => return None,
    };
    Some(out)
}

impl std::fmt::Display for HtmlJump {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self.0 {
            Value::Literal(i) => {
                if let Some(name) = addr_to_name(i) {
                    write!(
                        f,
                        "<a href=\"#f{i}\"><span class=\"lit\">{i}({name})</span></a>"
                    )
                } else {
                    write!(
                        f,
                        "<a href=\"#f{i}\"><span class=\"lit\">{i}</span></a>"
                    )
                }
            }
            Value::Register(r) => write!(f, "{}", HtmlReg(r)),
        }
    }
}

impl std::fmt::Display for HtmlOp {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self.0 {
            Op::Halt => write!(f, "<span class=\"op\">halt<span>"),
            Op::Set(a, b) => write!(f, "{} = {}", HtmlReg(a), HtmlValue(b)),
            Op::Push(a) => {
                write!(f, "<span class=\"op\">push</span> {}", HtmlValue(a))
            }
            Op::Pop(a) => {
                write!(f, "<span class=\"op\">pop</span>  {}", HtmlReg(a))
            }
            Op::Eq(a, b, c) => write!(
                f,
                "{}  = {} == {}",
                HtmlReg(a),
                HtmlValue(b),
                HtmlValue(c)
            ),
            Op::Gt(a, b, c) => write!(
                f,
                "{} = {} > {}",
                HtmlReg(a),
                HtmlValue(b),
                HtmlValue(c)
            ),
            Op::Jmp(a) => {
                write!(f, "<span class=\"op\">jmp</span>  {}", HtmlJump(a))
            }
            Op::Jt(a, b) => write!(
                f,
                "<span class=\"op\">jt</span>   {} {}",
                HtmlValue(a),
                HtmlJump(b)
            ),
            Op::Jf(a, b) => write!(
                f,
                "<span class=\"op\">jf</span>   {} {}",
                HtmlValue(a),
                HtmlJump(b)
            ),
            Op::Add(a, b, c) => write!(
                f,
                "{} = {} + {}",
                HtmlReg(a),
                HtmlValue(b),
                HtmlValue(c)
            ),
            Op::Mult(a, b, c) => write!(
                f,
                "{} = {} * {}",
                HtmlReg(a),
                HtmlValue(b),
                HtmlValue(c)
            ),
            Op::Mod(a, b, c) => write!(
                f,
                "{} = {} % {}",
                HtmlReg(a),
                HtmlValue(b),
                HtmlValue(c)
            ),
            Op::And(a, b, c) => write!(
                f,
                "{} = {} & {}",
                HtmlReg(a),
                HtmlValue(b),
                HtmlValue(c)
            ),
            Op::Or(a, b, c) => write!(
                f,
                "{} = {} | {}",
                HtmlReg(a),
                HtmlValue(b),
                HtmlValue(c)
            ),
            Op::Not(a, b) => write!(f, "{} = !{}", HtmlReg(a), HtmlValue(b)),
            Op::Rmem(a, b) => {
                write!(
                    f,
                    "<span class=\"op\">rmem</span> {} {}",
                    HtmlReg(a),
                    HtmlValue(b)
                )
            }
            Op::Wmem(a, b) => {
                write!(
                    f,
                    "<span class=\"op\">wmem</span> {} {}",
                    HtmlValue(a),
                    HtmlValue(b)
                )
            }
            Op::Call(a) => {
                write!(f, "<span class=\"op\">call</span> {}", HtmlJump(a))
            }
            Op::Ret => write!(f, "<span class=\"op\">ret</span>"),
            Op::Out(a) => match a {
                Value::Literal(c) => {
                    write!(
                        f,
                        "<span class=\"op\">out</span>  <span class=\"char\">{:?}</span>",
                        char::from_u32(c as u32).unwrap()
                    )
                }
                Value::Register(r) => {
                    write!(f, "<span class=\"op\">out</span>  {}", HtmlReg(r))
                }
            },
            Op::In(a) => {
                write!(f, "<span class=\"op\">in</span>   {}", HtmlReg(a))
            }
            Op::Noop => write!(f, "<span class=\"op\">noop</span>"),
            Op::Unknown(a) => write!(f, "<span class=\"unknown\">[{a}]</span>"),
        }
    }
}

#[derive(Copy, Clone, Debug)]
struct Register(u8);

impl std::fmt::Display for Register {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "r{}", self.0)
    }
}

#[derive(Copy, Clone, Debug)]
enum Value {
    Literal(u16),
    Register(Register),
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Value::Literal(i) => write!(f, "{i}"),
            Value::Register(r) => write!(f, "{r}"),
        }
    }
}

impl From<u16> for Value {
    fn from(t: u16) -> Value {
        match t {
            0..=32767 => Value::Literal(t),
            32768..=32775 => Value::Register(Register((t - 32768) as u8)),
            _ => panic!("invalid value {t}"),
        }
    }
}

impl std::ops::Index<Register> for Vm {
    type Output = u16;
    fn index(&self, r: Register) -> &Self::Output {
        &self.register[r.0 as usize]
    }
}

impl std::ops::IndexMut<Register> for Vm {
    fn index_mut(&mut self, r: Register) -> &mut Self::Output {
        &mut self.register[r.0 as usize]
    }
}

#[derive(Debug)]
enum Status {
    /// Continue with normal operation
    ///
    /// The flag is true if the input byte was consumed
    Continue(bool),

    /// Stop immediately
    Halt,

    /// Print the given output byte
    Out(u8),

    /// The VM requires input and no input byte is available
    NeedsInput,
}

impl Vm {
    fn new(bin: &[u8]) -> Self {
        assert_eq!(bin.len() % 2, 0);
        let memory: Vec<u16> = bin
            .chunks_exact(2)
            .map(|b| u16::from_le_bytes([b[0], b[1]]))
            .collect();
        Self {
            memory: Memory(memory),
            register: [0; 8],
            stack: vec![],
            ip: 0,
            calls: BTreeMap::new(),
        }
    }

    /// Gets a value from a register or literal
    fn get(&self, v: Value) -> u16 {
        match v {
            Value::Literal(i) => i,
            Value::Register(r) => self.register[r.0 as usize],
        }
    }

    fn step(&mut self, input: Option<u8>) -> Status {
        let op = self.memory.read(&mut self.ip);
        match op {
            Op::Halt => return Status::Halt,
            Op::Set(a, b) => {
                self[a] = self.get(b);
            }
            Op::Push(a) => {
                self.stack.push(self.get(a));
            }
            Op::Pop(a) => {
                let v = self.stack.pop().unwrap();
                self[a] = v;
            }
            Op::Eq(a, b, c) => {
                self[a] = (self.get(b) == self.get(c)) as u16;
            }
            Op::Gt(a, b, c) => {
                self[a] = (self.get(b) > self.get(c)) as u16;
            }
            Op::Jmp(a) => {
                self.ip = self.get(a) as usize;
            }
            Op::Jt(a, b) => {
                if self.get(a) != 0 {
                    self.ip = self.get(b) as usize;
                }
            }
            Op::Jf(a, b) => {
                if self.get(a) == 0 {
                    self.ip = self.get(b) as usize;
                }
            }
            Op::Add(a, b, c) => {
                self[a] = self.get(b).wrapping_add(self.get(c)) & MASK;
            }
            Op::Mult(a, b, c) => {
                self[a] = self.get(b).wrapping_mul(self.get(c)) & MASK;
            }
            Op::Mod(a, b, c) => {
                self[a] = (self.get(b) % self.get(c)) & MASK;
            }
            Op::And(a, b, c) => {
                self[a] = (self.get(b) & self.get(c)) & MASK;
            }
            Op::Or(a, b, c) => {
                self[a] = (self.get(b) | self.get(c)) & MASK;
            }
            Op::Not(a, b) => {
                self[a] = !self.get(b) & MASK;
            }
            Op::Rmem(a, b) => {
                self[a] = self.memory[self.get(b)];
                if self.get(b) == 6147 {
                    println!("read 6147: {} at {}", self[a], self.ip);
                }
            }
            Op::Wmem(a, b) => {
                let a = self.get(a);
                self.memory[a] = self.get(b);
                if a == 6151 {
                    println!("mutated at {}", self.ip);
                }
                if a == 6147 {
                    println!("wrote 6147: {} at {}", self.memory[a], self.ip);
                }
            }
            Op::Call(a) => {
                self.stack.push(self.ip.try_into().unwrap());
                let target = self.get(a);
                self.calls
                    .entry((self.ip - 2).try_into().unwrap())
                    .or_default()
                    .insert(target);
                self.ip = target as usize;
            }
            Op::Ret => {
                let Some(r) = self.stack.pop() else {
                    return Status::Halt;
                };
                self.ip = r as usize;
            }
            Op::Out(a) => {
                return Status::Out(
                    self.get(a).try_into().expect("invalid char"),
                );
            }
            Op::In(a) => {
                let Some(i) = input else {
                    self.ip -= 2;
                    return Status::NeedsInput;
                };
                self[a] = i as u16;
                return Status::Continue(true);
            }
            Op::Noop => (),
            Op::Unknown(..) => panic!("unknown opcode during execution"),
        }
        Status::Continue(false)
    }
}

#[derive(Clone)]
struct Game {
    vm: Vm,
}

impl Game {
    fn step(&mut self, command: &str) -> (String, bool) {
        let mut iter = command.bytes().chain(std::iter::once(b'\n'));
        let mut i = iter.next();
        let mut out = vec![];
        let mut n = 0;
        let halt = loop {
            n += 1;
            if n > 5000000 {
                panic!("timeout");
            }
            let r = self.vm.step(i);
            if self.vm.ip == 6072 {
                println!("{} {}", self.vm.register[0], self.vm.register[1]);
            }
            match r {
                Status::Continue(true) => i = iter.next(),
                Status::Continue(false) => (),
                Status::Halt => break true,
                Status::Out(c) => {
                    print!("{}", char::from_u32(c as u32).unwrap());
                    out.push(c);
                }
                Status::NeedsInput => break false,
            }
        };

        let desc = String::from_utf8(out).unwrap();
        (desc, halt)
    }

    fn play(&mut self, input: &str) {
        for line in input.lines() {
            let line = line.trim();
            if line.is_empty() {
                continue;
            }
            print!("{line}");
            let (_desc, halt) = self.step(line);
            assert!(!halt);
        }
    }
}

#[derive(Clone, Debug, Hash, Eq, PartialEq)]
struct Room {
    name: String,
    description: String,
    items: Vec<String>,
    exits: Vec<String>,
    interactive: bool,
}

fn find_room_with_item(
    mut game: Game,
    seen: &mut HashSet<Room>,
) -> Option<Game> {
    let (desc, halt) = game.step("look");
    assert!(!halt);
    let Some((room, header)) = Room::parse(&desc) else {
        panic!("could not parse description:\n{desc}");
    };
    if !room.items.is_empty() {
        return Some(game);
    } else if !seen.insert(room.clone()) {
        return None;
    }
    assert!(header.is_empty());
    for e in room.exits {
        let mut game = game.clone();
        let (_desc, halt) = game.step(&e);
        if halt {
            return None;
        }
        if let Some(r) = find_room_with_item(game, seen) {
            return Some(r);
        }
    }
    None
}

impl Room {
    fn parse(s: &str) -> Option<(Self, String)> {
        #[derive(Copy, Clone)]
        enum Mode {
            Inventory,
            Exits,
        }
        let mut header = String::new();
        let mut description = String::new();
        let mut name = None;
        let mut mode = None;
        let mut interactive = false;
        let mut items = vec![];
        let mut exits = vec![];
        for line in s.lines() {
            if line == "I don't understand; try 'help' for instructions."
                || line == "Taken."
            {
                return None;
            } else if let Some(line) = line.strip_prefix("== ") {
                assert!(name.is_none());
                let Some(line) = line.strip_suffix(" ==") else {
                    panic!("invalid room name");
                };
                name = Some(line.to_owned());
            } else if name.is_none() {
                header += line;
                header += "\n";
            } else if line == "Things of interest here:" {
                mode = Some(Mode::Inventory);
            } else if line == "There is 1 exit:"
                || (line.starts_with("There are ") && line.ends_with(" exits:"))
            {
                mode = Some(Mode::Exits);
            } else if line == "What do you do?" {
                interactive = true;
            } else if line.starts_with("- ") && mode.is_some() {
                let line = line.strip_prefix("- ").unwrap();
                match mode.unwrap() {
                    Mode::Inventory => items.push(line.to_owned()),
                    Mode::Exits => exits.push(line.to_owned()),
                }
            } else {
                description += line;
                description += "\n";
            }
        }

        // Remove trailing newlines
        description.pop();
        let Some(name) = name else {
            println!("missing name in {s:?}");
            return None;
        };
        Some((
            Self {
                exits,
                items,
                name,
                interactive,
                description,
            },
            header.trim().to_owned(),
        ))
    }
}

fn main() {
    let vm = Vm::new(CHALLENGE);

    let mut game = Game { vm };

    // Hard-coded sequence to enter the maze of twisty little passages
    game.play(
        "
            take tablet
            use tablet
            doorway
            north
            north
            bridge
            continue
            down
            east
            take empty lantern
            west
            west
            passage
            ladder
        ",
    );

    // Explore the maze until we find a room with an item, then switch to manual
    // mode again
    game = find_room_with_item(game, &mut HashSet::new()).unwrap();

    // The item is a can, which lets us travel through the darkness
    game.play(
        "
            take can
            use can
            west
            ladder
            darkness
            use lantern
            continue
            west
            west
            west
            west
            north
            take red coin
            north
            east
            take concave coin
            down
            take corroded coin
            up
            west
            west
            take blue coin
            up
            take shiny coin
            down
            east
        ",
    );

    // At this point, the monument reads
    //
    // _ + _ * _^2 + _^3 - _ = 399
    //
    // And we have the following items:
    // - red coin = 2
    // - corroded coin = 3
    // - shiny coin = 5
    // - concave coin = 7
    // - blue coin = 9
    //
    // blue + red * shiny**2 + concave**3 - corroded = 399
    game.play(
        "
            use blue coin
            use red coin
            use shiny coin
            use concave coin
            use corroded coin
            north
            take teleporter
            use teleporter
            take business card
            look business card
            take strange book
            look strange book
        ",
    );

    // Finding the checksum is a bit slow, but not egregious
    let start = std::time::Instant::now();
    game.vm.register[7] = 25734; //find_checksum();
    println!(
        "solved in {:?}, got {}",
        start.elapsed(),
        game.vm.register[7]
    );

    game.vm.memory[5507] = 6; // Preload r0 with the correct answer
    game.vm.memory[5511] = 21; // replace calibration call with noop
    game.vm.memory[5512] = 21; // replace calibration jump with noop

    game.play("use teleporter");

    // We're now on the beach!
    game.play(
        "
            west
            north
            east
            north
            north
            north
            north
            north
            north
            east
            take journal
            look journal
            west
            north
            north
        ",
    );

    // WELCOME TO THE ORB ZONE
    //
    // The number 22 is carved into the orb's pedastal
    //
    //    *  8  - 1V
    //    4  * 11  *
    //    +  4  - 18
    //    O  -  9  *
    //
    //  The orb starts at weight 22 and we want to hit 30 at the vault (upper
    //  right corner)
    game.play("take orb");

    let path = solve_orb_grid();
    for p in path.chars() {
        let m = match p {
            'N' => "north",
            'S' => "south",
            'E' => "east",
            'W' => "west",
            c => panic!("invalid direction {c:?}"),
        };
        game.play(m);
    }

    game.play(
        "
            vault
            take mirror
            use mirror
        ",
    );

    let mut orig = Vm::new(CHALLENGE);
    while orig.ip != 2756 {
        orig.step(None);
    }
    orig.memory.disassemble_all(&game.vm.calls);
    orig.memory.disassemble_all_html(&game.vm.calls);
    use std::io::Write;
    let mut f = std::fs::File::create("decrypted.bin").unwrap();
    for b in &orig.memory.0 {
        f.write_all(&b.to_le_bytes()).unwrap();
    }

    let mut i = 0;
    while i < orig.memory.0.len() as u16 {
        let n = orig.memory[i];
        let mut all_ascii = true;
        let mut out = String::new();
        for j in 0..n {
            match orig.memory.0.get((i + 1 + j) as usize) {
                Some(c) => {
                    let c = char::from_u32(*c as u32).unwrap();
                    all_ascii &= c.is_ascii_alphanumeric()
                        || c.is_ascii_punctuation()
                        || c.is_ascii_whitespace();
                    if !all_ascii {
                        break;
                    }
                    out.push(c);
                }
                None => {
                    all_ascii = false;
                    break;
                }
            }
        }
        if all_ascii && !out.is_empty() {
            println!("{i}: {out:?}");
        } else {
            out.clear();
        }
        i += 1 + out.len() as u16;
    }

    println!("{:?}", &game.vm.memory.0[6147..6200]);

    /*
    use std::io::BufRead;
    for line in std::io::stdin().lock().lines() {
        let (_desc, halt) = game.step(&line.unwrap());
        if halt {
            break;
        }
    }
    */
}

#[derive(Clone, Debug)]
struct OrbState {
    x: i32,
    y: i32,
    prev: i32,
    pending: Option<i32>,
    path: String,
}

impl OrbState {
    fn set_pending(&mut self, v: i32) {
        let prev = self.pending.replace(v);
        assert!(prev.is_none());
    }
}

/// Solve for a path through the grid
///
/// The map is shown below:
/// ```
///     3 | *  8  - 1V
///     2 | 4  * 11  *
///     1 | +  4  - 18       N
///     0 | O  -  9  *     W   E
///     ----------------     S
///       | 0  1  2  3
/// ```
///
///  The orb starts at weight 22 (at the lower-right, `O`) and we want to hit 30
///  at the vault (upper right corner, `1V`).
fn solve_orb_grid() -> String {
    let mut todo = VecDeque::new();
    todo.push_back(OrbState {
        x: 3,
        y: 3,
        prev: 30,
        pending: Some(i32::MAX), // marker for the start
        path: String::new(),
    });
    while let Some(mut s) = todo.pop_front() {
        match (s.x, s.y) {
            // Numerical values
            (3, 3) => {
                if s.pending.take() == Some(i32::MAX) {
                    s.set_pending(1);
                } else {
                    // Can't re-enter the vault room
                    continue;
                }
            }
            (1, 3) => s.set_pending(8),
            (0, 2) => s.set_pending(4),
            (2, 2) => s.set_pending(11),
            (1, 1) => s.set_pending(4),
            (3, 1) => s.set_pending(18),
            (0, 0) => {
                if s.prev == 22 {
                    let mut flipped = String::new();
                    while let Some(c) = s.path.pop() {
                        flipped.push(c);
                    }
                    return flipped;
                } else {
                    // The orb evaporates if you re-enter its room
                    continue;
                }
            }
            (2, 0) => s.set_pending(9),

            // Multiplication nodes (which become division)
            (0, 3) | (1, 2) | (3, 2) | (3, 0) => {
                // Easy exit if we can't do the division
                let p = s.pending.take().unwrap();
                if s.prev % p == 0 {
                    s.prev /= p;
                } else {
                    continue;
                }
            }

            // Addition nodes (which become subtraction)
            (0, 1) => {
                let p = s.pending.take().unwrap();
                s.prev -= p;
                if s.prev < 0 {
                    continue;
                }
            }
            // Subtraction nodes (which become addition)
            (1, 0) | (2, 1) | (2, 3) => {
                let p = s.pending.take().unwrap();
                s.prev += p;
            }
            // Off-grid values
            (4..=i32::MAX, _)
            | (_, 4..=i32::MAX)
            | (i32::MIN..=-1, _)
            | (_, i32::MIN..=-1) => continue,
        }
        for (dx, dy, c) in
            [(1, 0, 'W'), (-1, 0, 'E'), (0, 1, 'S'), (0, -1, 'N')]
        {
            let mut s = s.clone();
            s.x += dx;
            s.y += dy;
            s.path.push(c);
            todo.push_back(s);
        }
    }
    panic!("could not find valid path");
}

/// Rust implementation of the teleportation checksum procedure
///
/// The procedure is defined by the function beginning at 6049, taking `r0` and
/// `r1` as inputs and returning a value in `r0`.
///
/// ```
/// 6049: jt   r0 6057
/// 6052: r0 = r1 + 1
/// 6056: ret
/// 6057: jt   r1 6070
/// 6060: r0 = r0 + 32767
/// 6064: r1 = r7
/// 6067: call 6049
/// 6069: ret
/// 6070: push r0
/// 6072: r1 = r1 + 32767
/// 6076: call 6049
/// 6078: r1 = r0
/// 6081: pop  r0
/// 6083: r0 = r0 + 32767
/// 6087: call 6049
/// 6089: ret
/// ```
///
/// This translates to roughly
/// ```
/// def f(r0, r1):
///     if r0 == 0:
///         return r1 + 1
///     elif r1 == 0:
///         return f(r0 - 1, r7)
///     else:
///         r1 = f(r0, r1 - 1)
///         return f(r0 - 1, r1)
/// ```
///
/// The Rust implementation memoizes the (r0, r1) -> r0
fn checksum(r0: u16, r1: u16, r7: u16, seen: &mut [u16]) -> u16 {
    // 3 bits for r0, 15 for r1
    assert!(r0 <= 4);
    let key = (r0 as usize) | (r1 as usize) << 3;
    if seen[key] == u16::MAX {
        seen[key] = if r0 == 0 {
            r1.wrapping_add(1) & MASK
        } else if r1 == 0 {
            checksum(r0 - 1, r7, r7, seen)
        } else {
            let r1 = checksum(r0, r1 - 1, r7, seen);
            checksum(r0 - 1, r1, r7, seen)
        };
    }
    seen[key]
}

/// Finds a value for r7 such that `checksum(4, 1) == 6`
#[allow(unused)]
fn find_checksum() -> u16 {
    rayon::ThreadPoolBuilder::new()
        .stack_size(8 * 1024 * 1024)
        .build_global()
        .unwrap();
    (1..32767)
        .into_par_iter()
        .find_any(|i| {
            let mut seen = vec![u16::MAX; 1 << 18];
            checksum(4, 1, *i, &mut seen) == 6
        })
        .unwrap()
}

const INLINE_NOTES: &[(usize, &str)] = &[
    (
        1703,
        indoc::indoc! {"
            if len(s1) != len(s2)
              return 0
            v = len(s1) | len(s2)
            if v == 0
              return 1
            prepare to call map with per-character comparison

            per-character comparison failed, return false
    "},
    ),
    (
        1789,
        indoc::indoc! {"
            end = address + length
            current address in r0
            total length?
            address++
            if address > end
                 break
            read a character into r4
            if 'c' == '\n'
                 break
            *address = c
            length++
            loop
            *start = length
            if last char == '\n'
              break
            read char
            loop
    "},
    ),
];

const FUNCTION_NAMES: &[(usize, &'static str)] = &[
    (1480, "map"),
    (1540, "print"),
    (1550, "putc"),
    (1553, "xor-putc"),
    (1689, "strcmp"),
    (1745, "decrypt-data"),
    (2147, "xor"),
    (1789, "read-user-input"),
    (5836, "print-list-item"),
];
