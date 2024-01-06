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

#[derive(Debug)]
enum Value {
    Literal(u16),
    Register(u8),
}

impl From<u16> for Value {
    fn from(t: u16) -> Value {
        match t {
            0..=32767 => Value::Literal(t),
            32768..=32775 => Value::Register((t - 32768) as u8),
            _ => panic!("invalid value {t}"),
        }
    }
}

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
    fn get(&self, v: Value) -> u16 {
        match v {
            Value::Literal(i) => i,
            Value::Register(r) => self.register[r as usize],
        }
    }

    fn val(&mut self) -> Value {
        let v = self.memory[self.ip].into();
        self.ip += 1;
        v
    }

    fn reg(&mut self) -> usize {
        let v = self.val();
        let Value::Register(reg) = v else {
            panic!("not a register: {v:?}");
        };
        reg.into()
    }

    fn arg(&mut self) -> u16 {
        let a = self.memory[self.ip].into();
        self.ip += 1;
        self.get(a)
    }

    fn op<V: Into<u16>, F: Fn(u16, u16) -> V>(&mut self, f: F) {
        let a = self.reg();
        let b = self.arg();
        let c = self.arg();
        self.register[a] = f(b, c).into() & MASK;
    }

    fn step(&mut self, input: Option<u8>) -> Status {
        let op = self.memory[self.ip];
        self.ip += 1;
        match op {
            OP_HALT => return Status::Halt,
            OP_SET => {
                let a = self.reg();
                let b = self.arg();
                self.register[a] = b;
            }
            OP_PUSH => {
                let a = self.arg();
                self.stack.push(a);
            }
            OP_POP => {
                let a = self.reg();
                let v = self.stack.pop().unwrap();
                self.register[a] = v;
            }
            OP_EQ => self.op(|b, c| b == c),
            OP_GT => self.op(|b, c| b > c),
            OP_JMP => {
                let a = self.arg();
                self.ip = a as usize;
            }
            OP_JT => {
                let a = self.arg();
                let b = self.arg();
                if a != 0 {
                    self.ip = b as usize;
                }
            }
            OP_JF => {
                let a = self.arg();
                let b = self.arg();
                if a == 0 {
                    self.ip = b as usize;
                }
            }
            OP_ADD => self.op(|b, c| b.wrapping_add(c)),
            OP_MULT => self.op(|b, c| b.wrapping_mul(c)),
            OP_MOD => self.op(|b, c| b % c),
            OP_AND => self.op(|b, c| b & c),
            OP_OR => self.op(|b, c| b | c),
            OP_NOT => {
                let a = self.reg();
                let b = self.arg();
                self.register[a] = (!b) & MASK;
            }
            OP_RMEM => {
                let a = self.reg();
                let b = self.arg();
                self.register[a] = self.memory[b as usize];
            }
            OP_WMEM => {
                let a = self.arg() as usize;
                let b = self.arg();
                if a >= self.memory.len() {
                    self.memory.resize(a + 1, 0);
                }
                self.memory[a] = b;
            }
            OP_CALL => {
                let a = self.arg();
                self.stack.push(self.ip.try_into().unwrap());
                self.ip = a as usize;
            }
            OP_RET => {
                let Some(r) = self.stack.pop() else {
                    return Status::Halt;
                };
                self.ip = r as usize;
            }
            OP_OUT => {
                let a = self.arg();
                return Status::Out(a.try_into().expect("invalid char"));
            }
            OP_IN => {
                let Some(i) = input else {
                    self.ip -= 1;
                    return Status::NeedsInput;
                };
                let a = self.reg();
                self.register[a] = i as u16;
                return Status::Continue(true);
            }
            OP_NOOP => (),
            i => panic!("unimplemented instruction {i}"),
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
            match self.vm.step(i) {
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
        ",
    );

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
