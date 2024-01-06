use std::{
    collections::{BTreeMap, HashMap, HashSet},
    io::BufRead,
};

const CHALLENGE: &[u8] = include_bytes!("../challenge.bin");
const MASK: u16 = 32767;

#[derive(Clone, Eq, PartialEq, Hash)]
struct Vm {
    memory: Memory,
    register: [u16; 8],
    stack: Vec<u16>,
    ip: usize,
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
            i => panic!("unimplemented instruction {i}"),
        }
    }

    /// Disassemble a function beginning at the given instruction
    #[allow(unused)]
    fn disassemble(&self, ip: usize) {
        let mut seen = BTreeMap::new();
        let mut todo = vec![ip];
        while let Some(mut ip) = todo.pop() {
            let op = self.read(&mut ip);
            if seen.insert(ip, op).is_none() {
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
            Op::Not(a, b) => write!(f, "not  {a} = !{b}"),
            Op::Rmem(a, b) => write!(f, "rmem {a} {b}"),
            Op::Wmem(a, b) => write!(f, "wmem {a} {b}"),
            Op::Call(a) => write!(f, "call {a}"),
            Op::Ret => write!(f, "ret"),
            Op::Out(a) => write!(f, "out  {a}"),
            Op::In(a) => write!(f, "in   {a}"),
            Op::Noop => write!(f, "noop"),
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
            }
            Op::Wmem(a, b) => {
                let a = self.get(a);
                self.memory[a] = self.get(b)
            }
            Op::Call(a) => {
                self.stack.push(self.ip.try_into().unwrap());
                self.ip = self.get(a) as usize;
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

    fn autoplay(&mut self, input: &str) {
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
    game.autoplay(
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
    game.autoplay(
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
    game.autoplay(
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

    // Found using `find_checksum` below, which is very slow
    game.vm.register[7] = 25734;

    game.vm.memory[5507] = 6; // Preload r0 with the correct answer
    game.vm.memory[5511] = 21; // replace calibration call with noop
    game.vm.memory[5512] = 21; // replace calibration jump with noop

    game.autoplay("use teleporter");

    // We're now on the beach!
    game.autoplay(
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
    game.autoplay(
        "
            take orb
        ",
    );

    for line in std::io::stdin().lock().lines() {
        let (_desc, halt) = game.step(&line.unwrap());
        if halt {
            break;
        }
    }

    /*
    // NNN -> back
    // SSS -> back
    vm.input.extend(input);

    let mut input = std::io::stdin();
    let mut output = std::io::stdout();
    while vm.step(&mut input, &mut output) {
        // keep going
    }
    */
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

/// Finds a value for r7 such that f(4, 1) == 6
///
/// This is very slow, so I only ran it once to find the magic number.
#[allow(unused)]
fn find_checksum() -> u16 {
    for i in 1..32767 {
        let mut seen = vec![u16::MAX; 1 << 18];
        if i % 1000 == 0 {
            println!("{i}");
        }
        let e = checksum(4, 1, i, &mut seen);
        if e == 6 {
            return i;
        }
    }
    panic!("no value found");
}
