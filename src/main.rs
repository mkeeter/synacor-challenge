use std::{collections::HashSet, io::BufRead};

const CHALLENGE: &[u8] = include_bytes!("../challenge.bin");
const MASK: u16 = 32767;

#[derive(Clone, Eq, PartialEq, Hash)]
struct Vm {
    memory: Vec<u16>,
    register: [u16; 8],
    stack: Vec<u16>,
    ip: usize,
}

const OP_HALT: u16 = 0;
const OP_SET: u16 = 1;
const OP_PUSH: u16 = 2;
const OP_POP: u16 = 3;
const OP_EQ: u16 = 4;
const OP_GT: u16 = 5;
const OP_JMP: u16 = 6;
const OP_JT: u16 = 7;
const OP_JF: u16 = 8;
const OP_ADD: u16 = 9;
const OP_MULT: u16 = 10;
const OP_MOD: u16 = 11;
const OP_AND: u16 = 12;
const OP_OR: u16 = 13;
const OP_NOT: u16 = 14;
const OP_RMEM: u16 = 15;
const OP_WMEM: u16 = 16;
const OP_CALL: u16 = 17;
const OP_RET: u16 = 18;
const OP_OUT: u16 = 19;
const OP_IN: u16 = 20;
const OP_NOOP: u16 = 21;

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
            memory,
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

    /// Reads the value from the instruction pointer, incrementing it
    fn val(&mut self) -> Value {
        let v = self.memory[self.ip].into();
        self.ip += 1;
        v
    }

    /// Reads a register index at the instruction pointer, incrementing it
    fn reg(&mut self) -> Register {
        let v = self.val();
        let Value::Register(reg) = v else {
            panic!("not a register: {v:?}");
        };
        reg
    }

    /// Reads the next opcode from the machine, incrementing `self.ip`
    fn next(&mut self) -> Op {
        let op = self.memory[self.ip];
        self.ip += 1;
        match op {
            OP_HALT => Op::Halt,
            OP_SET => {
                let a = self.reg();
                let b = self.val();
                Op::Set(a, b)
            }
            OP_PUSH => {
                let a = self.val();
                Op::Push(a)
            }
            OP_POP => {
                let a = self.reg();
                Op::Pop(a)
            }
            OP_EQ => {
                let a = self.reg();
                let b = self.val();
                let c = self.val();
                Op::Eq(a, b, c)
            }
            OP_GT => {
                let a = self.reg();
                let b = self.val();
                let c = self.val();
                Op::Gt(a, b, c)
            }
            OP_JMP => {
                let a = self.val();
                Op::Jmp(a)
            }
            OP_JT => {
                let a = self.val();
                let b = self.val();
                Op::Jt(a, b)
            }
            OP_JF => {
                let a = self.val();
                let b = self.val();
                Op::Jf(a, b)
            }
            OP_ADD => {
                let a = self.reg();
                let b = self.val();
                let c = self.val();
                Op::Add(a, b, c)
            }
            OP_MULT => {
                let a = self.reg();
                let b = self.val();
                let c = self.val();
                Op::Mult(a, b, c)
            }
            OP_MOD => {
                let a = self.reg();
                let b = self.val();
                let c = self.val();
                Op::Mod(a, b, c)
            }
            OP_AND => {
                let a = self.reg();
                let b = self.val();
                let c = self.val();
                Op::And(a, b, c)
            }
            OP_OR => {
                let a = self.reg();
                let b = self.val();
                let c = self.val();
                Op::Or(a, b, c)
            }
            OP_NOT => {
                let a = self.reg();
                let b = self.val();
                Op::Not(a, b)
            }
            OP_RMEM => {
                let a = self.reg();
                let b = self.val();
                Op::Rmem(a, b)
            }
            OP_WMEM => {
                let a = self.val();
                let b = self.val();
                Op::Wmem(a, b)
            }
            OP_CALL => {
                let a = self.val();
                Op::Call(a)
            }
            OP_RET => Op::Ret,
            OP_OUT => {
                let a = self.val();
                Op::Out(a)
            }
            OP_IN => {
                let a = self.reg();
                Op::In(a)
            }
            OP_NOOP => Op::Noop,
            i => panic!("unimplemented instruction {i}"),
        }
    }

    fn step(&mut self, input: Option<u8>) -> Status {
        match self.next() {
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
                self[a] = self.memory[self.get(b) as usize];
            }
            Op::Wmem(a, b) => {
                let a = self.get(a) as usize;
                if a >= self.memory.len() {
                    self.memory.resize(a + 1, 0);
                }
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
        let halt = loop {
            let r = self.vm.step(i);
            match r {
                Status::Continue(true) => i = iter.next(),
                Status::Continue(false) => (),
                Status::Halt => break true,
                Status::Out(c) => out.push(c),
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
            let (desc, halt) = self.step(line);
            assert!(!halt);
            print!("{desc}");
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
        let (desc, halt) = game.step(&e);
        if halt {
            println!("{desc}");
            return None;
        }
        if desc.split_whitespace().any(|w| w.len() == 12) {
            print!("{desc}");
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

    for i in 1..u16::MAX {
        println!("{i}");
        let mut game = game.clone();
        game.vm.register[7] = i;
        let o = game.step("use teleporter");
        println!("{o:?}");
    }
    //game.autoplay("use teleporter");

    for line in std::io::stdin().lock().lines() {
        let (desc, halt) = game.step(&line.unwrap());
        print!("{desc}");
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
