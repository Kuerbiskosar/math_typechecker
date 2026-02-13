use std::{collections::HashMap, fmt::Display, hash::Hash, ops::{Add, Div, Mul, Sub}, str::FromStr};

// Because Lanter ranted about using floating point numbers, I might implement fixed point arithmetic
// every number (and every value) has some unit attached to it ([-] being "no" unit or unitless.)
// new units will be generated at runtime, so I am not quite shure what the best way to implement them is.
// for now, the unit will be represented by a string! (The fisrst solution that comes to mind, which ~might~ be quite good)
// how will I mix and match between natural numbers and floats and etc???
#[derive(Clone, PartialEq, Debug)]
pub struct Number {
    pub value: f64,
    // imaginary_value: f64 // This may be added in the future (or there will be another number type?)
    pub unit: Unit,
}
impl Add for Number {
    type Output = Result<Self, String>;
    fn add(self, other: Self) -> Result<Self, String> {
        if self.unit.quantity != other.unit.quantity {
            return Err(format!("Quantities must be the same but where {} for {} and {} for {}", self.unit.quantity, self.unit, other.unit.quantity, other.unit))
        }
        // convert the unit of the smaller number to the unit of the bigger
        // when adding 1 kg + 1 g, the result 1.001 kg is (arguably) better than 1'001 g
        if self.unit.modifier > other.unit.modifier {
            // convert unit of other to unit of self
            let new_other_value = other.value * (other.unit.modifier / self.unit.modifier);
            Ok(Number { value: new_other_value+self.value, unit: self.unit })
        }
        else {
            let new_self_value = self.value * (self.unit.modifier / other.unit.modifier);
            Ok(Number { value: new_self_value + other.value, unit: other.unit })
        }
    }
}
impl Sub for Number {
    type Output = Result<Self, String>;

    fn sub(self, other: Self) -> Self::Output {
        if self.unit.quantity != other.unit.quantity {
            return Err(format!("Quantities must be the same but where {} for {} and {} for {}", self.unit.quantity, self.unit, other.unit.quantity, other.unit))
        }
        // convert the unit of the smaller number to the unit of the bigger
        // when subtracting 1 kg - 1 g, the result 0.999 kg is (arguably) better than 999 g
        // maybe at some point I make this dynamic to choose the value closer to zero? (as in 999 is further than 0.999)
        if self.unit.modifier > other.unit.modifier {
            // convert unit of other to unit of self
            let new_other_value = other.value * (other.unit.modifier / self.unit.modifier);
            Ok(Number { value: new_other_value-self.value, unit: self.unit })
        }
        else {
            let new_self_value = self.value * (self.unit.modifier / other.unit.modifier);
            Ok(Number { value: new_self_value - other.value, unit: other.unit })
        }
    }
}

impl Mul for Number {
    type Output = Number;

    fn mul(self, other: Self) -> Self::Output {
        // if the quantitys are the same, convert the bigger unit to the smaller
        // (1 km * 1 m will be something smaller than one km. having the result as 100 m^2 is (arguably) better than 0.001 km^2)
        if self.unit.quantity == other.unit.quantity {
            if self.unit.modifier < other.unit.modifier {
                // convert unit of other to unit of self^2
                let new_other_value = other.value * (other.unit.modifier / self.unit.modifier);
                Number { value: new_other_value*self.value, unit: self.unit.clone()*self.unit }
            }
            else { // convert unit of self to other and return other^2
                let new_self_value = self.value * (self.unit.modifier / other.unit.modifier);
                Number { value: new_self_value * other.value, unit: other.unit.clone()*other.unit }
            }
        } else {
            Number {
                value: self.value * other.value,
                unit: self.unit * other.unit,
            }
        }

    }
}
impl Div for Number {
    type Output = Result<Self, String>;

    fn div(self, other: Self) -> Self::Output {
        if other.value == 0.0 {
            return Err("Division by Zero".to_owned())
        }
        // if the quantitys are the same, convert the bigger unit to the smaller
        // This way we generally loose less precision (with the tradeoff, that overflow errors during conversion are more likely)
        // (1 km / 1 m will be 1000 [-] no matter what)
        if self.unit.quantity == other.unit.quantity {
            if self.unit.modifier < other.unit.modifier {
                // convert unit of other to unit of self^2
                let new_other_value = other.value * (other.unit.modifier / self.unit.modifier);
                Ok(Number { value: new_other_value/self.value, unit: self.unit.clone()/self.unit })
            }
            else { // convert unit of self to other
                let new_self_value = self.value * (self.unit.modifier / other.unit.modifier);
                Ok(Number { value: new_self_value / other.value, unit: other.unit.clone()*other.unit })
            }
        } else {
            Ok(Number {
                value: self.value / other.value,
                unit: self.unit / other.unit,
            })
        }
    }
}

impl Display for Number {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} [{}]", {self.value}, {&self.unit})
    }
}

#[derive(Clone, PartialEq, Debug)]
pub struct Unit
{
    // example Newton
    pub name: Option<String>,
    // example N
    pub symbol: Option<String>,
    // a unit like Newton is kg * m/s^2 aka. kg^1 * m^1 * s^-2. it will be stored as vec![("kg", 1), ("m", 1), ("s", -2)]
    // I considered using EITHER for the option, but instead, the alternative value is in the symbol field.
    // -> If there is no Unit, the String (key of HashMap) is the value (unit symbol) instead (no need to use either, otherwise the string would be stored twice)
    // meaning, if Option<Unit> is None, the key is a base unit.
    pub base_unit: HashMap<String, (Option<Unit>, i32)>,
    // example Force. if this unit got build during a computation, the quantity won't have a name, but 
    // a "base_name" like {mass: 1, length: 1, time: -2}
    pub quantity: Quantity,
    // used to convert between different units of the same Quantity
    pub modifier: f64,
}
impl Display for Unit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.symbol.to_owned().unwrap_or_else(|| show_unit_pretty(&self.base_unit, self.symbol.clone())))
    }
}
/// unwraps the base_unit field to only contain real base units (no Newton)
fn to_base_units(composed_units: &HashMap<String, (Option<Unit>, i32)>) -> HashMap<String, (Option<Unit>, i32)> {
    let mut out: HashMap<String, (Option<Unit>, i32)> = HashMap::default();
    for (key, (unit, exponent)) in composed_units {    
        match unit {
            Some(non_base_unit) => {
                // Go to the real base unit
                let recursive_base = to_base_units(&non_base_unit.base_unit);
                merge_units(&mut out, &recursive_base)
            },
            None => {out.entry(key.to_owned()).and_modify(|(_, counter)| *counter += exponent)
                .or_insert((None, *exponent));}
        };
    }
    // remove any entrys, with an exponent of 0
    out.retain(|_, (_,exponent )| *exponent != 0);
    out
}
// merges unit2 into unit1
/// merges two HasMaps of units together, by adding the exponents together
/// also works for quantitys.
fn merge_units<T: Clone>(units1: &mut HashMap<String, (Option<T>, i32)>, units2: &HashMap<String, (Option<T>, i32)>) {
    for (key, (unit, exponent)) in units2 {
        units1.entry(key.to_owned()).and_modify(|(_, counter)| *counter += exponent)
                .or_insert((unit.clone(), *exponent));
    }
    // remove any entrys, with an exponent of 0
    units1.retain(|_, (_,exponent )| *exponent != 0);
}
/// modifies units1 to be the resulting unit of units1/units2 (flips the sign of the exponents of units2)
fn merge_units_dividing<T: Clone>(units1: &mut HashMap<String, (Option<T>, i32)>, units2: &HashMap<String, (Option<T>, i32)>) {
    for (key, (unit, exponent)) in units2 {
        units1.entry(key.to_owned()).and_modify(|(_, counter)| *counter += -exponent)
                .or_insert((unit.clone(), *exponent * -1));
    }
    // remove any entrys, with an exponent of 0
    units1.retain(|_, (_,exponent )| *exponent != 0);
}

// converts a unit coposed of other units into a string with the highest available symbols
// (directly converts the HashMap into a string with key*exponent, completely ignoring the Unit entry (that's used to further evaluate it to base units))
fn show_unit_with_exponent<T>(base_unit: &HashMap<String, (Option<T>, i32)>) -> String {
    // TODO: First collect all keys, to return them sortet
    let mut out = String::new();
    for (base_symbol, (_, exponent)) in base_unit {
        out.push_str(&format!("{}^{}", base_symbol, exponent));
    }
    out
}
fn show_unit_pretty<T>(base_unit: &HashMap<String, (Option<T>, i32)>, symbol: Option<String>) -> String {
    // TODO: First collect all keys, to return them sortet
    let mut nominator = String::new();
    let mut denominator = String::new();
    let mut nr_denominators = 0;
    for (base_symbol, (_, exponent)) in base_unit {
        match exponent.cmp(&0) {
            std::cmp::Ordering::Less => {
                denominator.push_str(&format!("{}^{} ", base_symbol, -exponent));
                nr_denominators += 1;
            },
            std::cmp::Ordering::Equal => (),
            std::cmp::Ordering::Greater => {
                // TODO: exponent gets representet as a float, for which == comparision may fail (floating point errors)
                // maybe choose another method to represent the exponent
                if exponent == &1 {
                    nominator.push_str(&format!("{} ", base_symbol))
                } else {
                    nominator.push_str(&format!("{}^{} ", base_symbol, exponent))
                }
            },
        }
    };
    denominator = denominator.trim().to_owned();
    nominator = nominator.trim().to_owned();
    if denominator == "" && nominator == "" {
        match symbol {
            Some(sym) => sym.to_string(),
            None => "-".to_string(), // default symbol for unitless
        }
    } else if denominator == "" {
        nominator
    } else if nominator == "" {
        format!("1/{}", denominator)
    } else if nr_denominators > 1 {
        format!("{}/({})", nominator,denominator)
    } else {
        format!("{}/{}", nominator,denominator)
    }
}
impl Mul for Unit {
    type Output = Unit;

    fn mul(self, rhs: Self) -> Self::Output {
        // if the units have a symbol, we store the symbol and a reference to the base unit in the base_unit HashMap, if not, we merge together the existing units
        let mut new_unit: HashMap<String, (Option<Unit>, i32)>;
        if let Some(ref symbol) = self.symbol {
            new_unit = HashMap::from([(symbol.clone(), (Some(self.clone()), 1))]);
        } else {
            new_unit = self.base_unit.clone();
        }
        // same check as above for rhs
        if let Some(ref symbol) = rhs.symbol {
            merge_units(&mut new_unit, &HashMap::from([(symbol.clone(), (Some(rhs.clone()), 1))]));
        } else {
            merge_units(&mut new_unit, &rhs.base_unit);
        }
        // check if the resulting unit is a base unit
        let new_base_unit = to_base_units(&new_unit);
        // if the result would be unitless or a base unit
        if new_base_unit.len() <= 1 {
           new_unit = new_base_unit;
        }
        let quantity = self.quantity*rhs.quantity;
        Unit {
            name: None,
            symbol: None,
            base_unit: new_unit,
            quantity: quantity,
            modifier: self.modifier * rhs.modifier,
        }
    }
}
impl Div for Unit {
    type Output = Unit;

    fn div(self, rhs: Self) -> Self::Output {
        // if the units have a symbol, we store the symbol and a reference to the base unit in the base_unit HashMap, if not, we merge together the existing units
        let mut new_unit: HashMap<String, (Option<Unit>, i32)>;
        if let Some(ref symbol) = self.symbol {
            new_unit = HashMap::from([(symbol.clone(), (Some(self.clone()), 1))]);
        } else {
            new_unit = self.base_unit.clone();
        }
        // same check as above for rhs
        if let Some(ref symbol) = rhs.symbol {
            merge_units_dividing(&mut new_unit, &HashMap::from([(symbol.clone(), (Some(rhs.clone()), 1))]));
        } else {
            merge_units_dividing(&mut new_unit, &rhs.base_unit);
        }
        // check if the resulting unit is a base unit
        let new_base_unit = to_base_units(&new_unit);
        // if the result would be unitless or a base unit
        if new_base_unit.len() <= 1 {
           new_unit = new_base_unit;
        }
        let quantity = self.quantity/rhs.quantity;
        Unit {
            name: None,
            symbol: None,
            base_unit: new_unit,
            quantity: quantity,
            modifier: self.modifier * rhs.modifier,
        }
    }
}

impl Unit {
    /// a new unit based on a base quantity
    pub fn new_base(name: Option<String>, symbol: String, quantity: &Quantity, modifier: f64) -> Unit {
        // The base unit has its symbol stored in the key of quantity... maybe symbol is fully redundand?
        Unit {
            //name: Some(Name::from_str(name).unwrap()),
            name: name,
            symbol: None,
            base_unit: HashMap::from([(symbol, (None, 1))]),
            quantity: quantity.clone(),
            modifier: modifier }
    }
    /// creates a new base with low boilerplate inputs (string references instead of optional strings).
    /// This method is meant to create units for testing.
    pub fn new_test_base(name: &str, symbol: &str, quantity: &Quantity, modifier: f64) -> Unit {
        // The base unit has its symbol stored in the key of quantity... maybe symbol is fully redundand?
        Unit {
            //name: Some(Name::from_str(name).unwrap()),
            name: Some(name.to_string()),
            symbol: None,
            base_unit: HashMap::from([(symbol.to_string(), (None, 1))]),
            quantity: quantity.clone(),
            modifier: modifier }
    }

    /// creates a new derived unit. if base_units is empty, it will create a unitless, unnamed, base_unit with modifier = 1
    pub fn new_derived(name: &str, symbol: &str, base_units: Vec<(Unit, i32)>) -> Unit {
        
        let mut new_unit: HashMap<String, (Option<Unit>, i32)> = HashMap::default();
        let mut base_quantitys: Vec<(Quantity, i32)> = Vec::new();
        let mut modifier = 1.0;

        if base_units == Vec::default() {
            new_unit.insert(symbol.to_string(), (None, 1));
        } else {
            for (unit, exponent) in base_units {
                base_quantitys.push((unit.quantity, exponent));
                modifier = modifier * unit.modifier * (exponent as f64);
                if exponent > 0 {
                    for _i in 0..exponent {
                        merge_units(&mut new_unit, &unit.base_unit);
                    }
                } else if exponent < 0 {
                    for _i in 0..-exponent {
                        merge_units_dividing(&mut new_unit, &unit.base_unit);
                    }
                } // else if exponent = 0 doesn't need any processing (that unit doesn't really exist)
            }
        }
        
        let new_quantity = Quantity::new_nameless(base_quantitys);
        Unit {
            //name: Some(Name::from_str(&name.to_string()).unwrap()),
            name: Some(name.to_string()),
            symbol: Some(symbol.to_string()),
            base_unit: new_unit,
            quantity: new_quantity,
            modifier: modifier,
        }
    }
    pub fn new_coded(name: Option<String>, symbol: String, base_unit: HashMap<String, (Option<Unit>, i32)>, modifier: f64, quantity: Quantity) -> Unit {
        Unit {
            name: name,
            symbol: Some(symbol),
            base_unit,
            quantity,
            modifier,
        }
    }
    /// creates a new unit with the given name and symbol, by splitting the given string into unit symbols -> probably already not doing it trough strings anymore.
    /// The unit symbols must be contained inside the quantity_tracker (to get the quantity), otherwise Err() will be returned.
    /// Note that there is nothing stopping you from creating two units with different names but the same quantity (like Ws and J for the string kg*m^2/s^2)
    /// NOTE: currently not handling brackets just using / to switch between nominator and denominator, and using * as a separator between
    fn funky_derived(name: &str, symbol: &str, base_units: String, quantity_tracker: &mut HashMap<String, HashMap<String, (Option<Quantity>, i32)>>) -> Result<Unit, String> {
        
        // convert a string like km/h into a HashMap {km: 1, h: -1}
        let symbol = {
            // TODO: first the name must be separatet into its subnames
            // The nominators and denominators are sortet separately
            let symbol = symbol.to_string();
            let mut iterator = symbol.split("/");
            let mut nominators: Vec<&str> = Default::default();
            let mut denominators: Vec<&str> = Default::default();
            loop {
                match iterator.next() {
                    Some(a) => {
                        for base_unit in a.split("*") {
                            nominators.push(base_unit);
                        }
                    },
                    None => break,
                }

                match iterator.next() {
                    Some(a) => {
                        for base_unit in a.split("*") {
                            denominators.push(base_unit);
                        }
                    },
                    None => break,
                }
            }
            nominators.sort();
            denominators.sort();
            let mut symbol: HashMap<String, i32> = Default::default();
            for base_unit in nominators {
                symbol.entry(base_unit.to_string()).and_modify(|counter| *counter += 1).or_insert(1);
            }
            for base_unit in denominators {
                symbol.entry(base_unit.to_string()).and_modify(|counter| *counter -= 1).or_insert(-1);
            }
            symbol
        };
        todo!()
    }

    pub fn unitless() -> Unit {
        Unit { name: None,
            symbol: None,
            base_unit: HashMap::new(),
            quantity: Quantity::new_nameless(Vec::new()),
            modifier: 1.0
        }
    }
}

// TODO: derive PartialEq, to make Two quantitys with different symbol order the same.
#[derive(Clone, Debug)]
pub struct Quantity
{
    // actual name of the quantity ex. Mass, velocity etc.
    pub name: Option<String>,
    // Symbol like m, v etc.
    pub symbol: Option<String>, // this field allows renaming kg*m/s^2 to N
    pub base_quantity: HashMap<String, (Option<Quantity>, i32)>, // base units have their symbol as the key and (None, 1) as the value. By giving a base unit a symbol, there can be multiple different symbols for the same quantity (l and h for distance (h is height))
}

impl Quantity {
    pub fn new(name: &str, symbol: &str, base_quantitys: Vec<(Quantity, i32)>, /*quantity_tracker: &mut HashMap<String, HashMap<String, (Option<Quantity>, i32)>>*/) -> Self {
        //let name = Name::from_str(name).expect("too long names should have been handled on the pharser level");
        
        // // get id, which is not yet used (the loop will only have to run more than once, if we start to remove keys)
        // let mut test_id = quantity_tracker.len();
        // let id = loop {
        //     match quantity_tracker.get(&test_id) {
        //         Some(_) => test_id += 1,
        //         None => break test_id,
        //     }
        // };
        let mut new_quantity: HashMap<String, (Option<Quantity>, i32)> = HashMap::default();
        if base_quantitys == Vec::default() {
            new_quantity.insert(symbol.to_string(), (None, 1));
        } else {
            for (quantity, exponent) in base_quantitys {
                if exponent > 0 {
                    for _i in 0..exponent {
                        merge_units(&mut new_quantity, &quantity.base_quantity);
                    }
                } else if exponent < 0 {
                    for _i in 0..-exponent {
                        merge_units_dividing(&mut new_quantity, &quantity.base_quantity);
                    }
                } // else if exponent = 0 doesn't need any processing (that unit doesn't really exist)
            }
        }
        //quantity_tracker.insert(name.to_string(), new_quantity.clone());
        Quantity {
            name: Some(name.to_string()),
            symbol: Some(symbol.to_string()),
            base_quantity: to_base_quantitys(&new_quantity),
        }
    }
    /// The function executed, to create a new unit with the Quantity <Name>: <Symbol> = <expression> syntax
    /// The Quantity is derived by evaluating the given expression
    pub fn new_coded(name: Option<String>, symbol: String, base_quantity: HashMap<String, (Option<Quantity>, i32)>) -> Quantity {
        Quantity { name, symbol: Some(symbol), base_quantity: base_quantity }
    }
    pub fn new_nameless(base_quantitys: Vec<(Quantity, i32)>) -> Self {
        // // get id, which is not yet used (the loop will only have to run more than once, if we start to remove keys)
        // let mut test_id = quantity_tracker.len();
        // let id = loop {
        //     match quantity_tracker.get(&test_id) {
        //         Some(_) => test_id += 1,
        //         None => break test_id,
        //     }
        // };
        let mut new_quantity: HashMap<String, (Option<Quantity>, i32)> = HashMap::default();
        if base_quantitys == Vec::default() {
            // congratulations, you just implemented the unitless quantity, without giving it a name (or symbol)
        } else {
            for (quantity, exponent) in base_quantitys {
                if exponent > 0 {
                    for _i in 0..exponent {
                        merge_units(&mut new_quantity, &quantity.base_quantity);
                    }
                } else if exponent < 0 {
                    for _i in 0..-exponent {
                        merge_units_dividing(&mut new_quantity, &quantity.base_quantity);
                    }
                } // else if exponent = 0 doesn't need any processing (that unit doesn't really exist)
            }
        }
        Quantity {
            name: None,
            symbol: None,
            base_quantity: to_base_quantitys(&new_quantity),
        }
    }
    pub fn get_symbol(&self) -> String {
        // note: this is the display function
        format!("{}", self.symbol.to_owned().unwrap_or_else(|| show_unit_pretty(&self.base_quantity, self.symbol.clone())))
    }
    
}
impl Display for Quantity {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.symbol.to_owned().unwrap_or_else(|| show_unit_pretty(&self.base_quantity, self.symbol.clone())))
    }
}
impl PartialEq for Quantity {
    fn eq(&self, other: &Self) -> bool {
        let a = to_base_quantitys(&self.base_quantity);
        let b = to_base_quantitys(&other.base_quantity);
        let mut collector = Vec::new();
        if a.len() != b.len() {return false}
        for (base_symbol1, (_, exponent1)) in a {
            match b.get_key_value(&base_symbol1) {
                Some((base_symbol2, (_, exponent2))) => collector.push(&base_symbol1 == base_symbol2 && exponent1 == *exponent2),
                None => return false,
            }
        }
        // this code gives non-deterministic output, because the HaschMaps can be sortet differently!
        // for ((base_symbol1, (_, exponent1)), (base_symbol2, (_, exponent2))) in zip(a, b) {
        //     collector.push(base_symbol1 == base_symbol2 && exponent1 == exponent2);
        // }
        collector.iter().all(|x| *x) // check if all are true
    }
}
impl Mul for Quantity {
    type Output = Quantity;
    /// Returns the quantity of two multiplied Quantityes. Must depend on a global Quantity map, to check if quantity exists?
    fn mul(self, rhs: Self) -> Self::Output {
        // The "name" are the base units in alphabetical order
        let mut new_quantity = self.base_quantity.clone();
        merge_units(&mut new_quantity, &rhs.base_quantity);
        Quantity {
            name: None,
            symbol: None,
            base_quantity: new_quantity,
        }
    }
}
impl Div for Quantity {
    type Output = Quantity;

    fn div(self, rhs: Self) -> Self::Output {
        let mut new_quantity = self.base_quantity.clone();
        merge_units_dividing(&mut new_quantity, &rhs.base_quantity);
        Quantity {
            name: None,
            symbol: None,
            base_quantity: new_quantity,
        }
    }
}

fn to_base_quantitys(composed_units: &HashMap<String, (Option<Quantity>, i32)>) -> HashMap<String, (Option<Quantity>, i32)> {
    let mut out: HashMap<String, (Option<Quantity>, i32)> = HashMap::default();
    for (key, (unit, exponent)) in composed_units {    
        match unit {
            Some(non_base_unit) => {
                // Go to the real base unit
                let recursive_base = to_base_quantitys(&non_base_unit.base_quantity);
                merge_units(&mut out, &recursive_base)
            },
            None => {out.entry(key.to_owned()).and_modify(|(_, counter)| *counter += exponent)
                .or_insert((None, *exponent));}
        };
    }
    out
}

const MAX_UNIT_NAME_LENGHT: usize = 64;
/// Copy-able string type to identify values.
/// All names can maximum be 64 characters long. That's this long:
/// 1234567891023456789202345678930234567894023456789502345678960234
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Name{
    Name([char; MAX_UNIT_NAME_LENGHT])
}
impl FromStr for Name {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.len() > MAX_UNIT_NAME_LENGHT {
            return Err(format!("Failed to convert from string with length {} to name, because it was longer than {}.", s.len(), MAX_UNIT_NAME_LENGHT));
        }
        let mut buffer = ['\n';64];
        for (i, char) in s.chars().enumerate() {
            buffer[i] = char;
        }
        Ok(Name::Name(buffer))
    }
}
impl Display for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Name::Name(arr) => {
                // check how much space to allocate
                let mut capacity = 0;
                for char in arr {
                    if *char == '\n' {
                        break
                    }
                    capacity += 1;
                }
                let mut out = String::with_capacity(capacity);
                for i in 0..capacity {
                    if i >= MAX_UNIT_NAME_LENGHT {
                        break;
                    }
                    out.push(arr[i]);
                }
                write!(f, "{}", out)
            }
        }
    }
}

fn concat_name(left: Name, separator: &str, right: Name) -> Result<Name, String> {
        Name::from_str(&format!("{}{}{}", left.to_string(), separator, right.to_string()))
}
// a value, which can't be Nan, as float can.
// also trying to avoid floating point errors, by sacrificing memory
// The guys at IEEE are probably pretty smart, so it is probably stupid to try to make my own float-like-type... but whatever
// what happens on an overflow? the same thing as with an integer overflow: the program will panic.
// floating point values can't represent rationals exaclty. This type should be able to represent rationals with floating points.
struct SafeValue {
    negative: bool,
    base_numerator: usize,
    exponent_numerator: usize,
    base_denominator: usize,
    exponent_denumerator: usize,
    // imaginary_size: usize,
    // imaginary_base: usize,
    // imaginary_exponent: usize,
}

// This is the Unit of a value as in Millimeters and Kilograms. Not to be confused with the rust unit type.
// Also: Differnt Units can be converted within the same Quantity.
// I ~Think~ Units need to be their own type, because we create them at runtime and want to operate them together
// to compare different units they need some normal form.
// I could take the "easy" route and define seven base units, from which we can derive everything else, but 
// that's probably not very practical (Just take hardness for example. The Unit HV isn't based on the seven SI units right? -> I just checked, it is kgf/mm^2)
// maybe we want to measure ~LOVE~ in a non-physical way? that would need a special Quantity
// -> Currency is an obvious counterexample on why we need "Dynamic" Quantitys

// Modifier must be some number. There probably needs to be some trait which Modifier must fulfill.
/// String is the name, and f64 the multiplication from the base unit
/// example: Km is of Quantity "Mass" with Modifier 1000
/// The base unit m is of Quantity "Mass" with Modifier 1


#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test(){

    }
    #[test]
    fn type_testing() {
        // let mass = create_quantity("Mass").expect("name should be short enough");
        // let length = create_quantity("Length").expect("name should be short enough");
        // let meter = Unit::Unit("m", length, 1.0); // this works, because name implements from_string :D
        // let kilometer = Unit::Unit("mm", length, 1000.0); // TODO: i32 as a scalar doesn't cut it. we need fractions.
        // let a: Rc<String> = Rc::new("value".to_string());
        // let a = 0.1;
        //let mut quantity_tracker = HashMap::new();
        let mass = Quantity::new("mass", "m", Vec::default()); // typechecking the exact type of Quantity is impossible, because the available types will only be known at runtime.
        let kilogram = Unit{ name: Some("kilogram".to_string()), quantity: mass.clone(), modifier: 1.0, symbol: None, base_unit: HashMap::from([("kg".to_string(), (None, 1))])};
        let gram = Unit::new_test_base("gram", "g", &mass, 0.001);
        //let gram = Unit {name: Name::from_str("g").unwrap(), quantity: mass, modifier: 0.001};
        let a = Number{ value: 1.0, unit: kilogram };
        let b = Number {value:1.0,unit:gram};

        let length = Quantity::new("length", "l", Vec::default());
        println!("{}", (a.clone()+b.clone()).unwrap());
        println!("{}", (a.clone()*b.clone()));
        println!("{}", (a.unit.quantity));

        //panic!() // panic to see the output
    }
    #[test]
    fn test_addition() {
        let length = Quantity::new("length", "l", Vec::default());
        let mm = Unit::new_test_base("millimeter", "mm", &length, 1e-3);
        let m = Unit::new_test_base("meter", "m", &length, 1.0);
        let a = Number{ value: 1.0, unit: m};
        let b = Number{ value: 2.0, unit: mm};
        let c = a + b;
        let c = c.expect("+ operation on two equal quantitys (of different units) returned an error");
        assert_eq!(c.value, 1.002);
        assert_eq!(c.unit.base_unit, HashMap::from([("m".to_string(), (None, 1))]));
    }
    #[test]
    fn test_multiplication_square() {
        let length = Quantity::new("length", "l", Vec::default());
        let mm = Unit::new_test_base("millimeter", "mm", &length, 1e-3);
        let m = Unit::new_test_base("meter", "m", &length, 1.0);
        let a = Number{ value: 1.0, unit: m};
        let b = Number{ value: 2.0, unit: mm};
        let c = a * b;
        assert_eq!(c.value, 2000.0);
        assert_eq!(c.unit.base_unit, HashMap::from([("mm".to_string(), (None, 2))]));
    }
    #[test]
    fn test_multiplication_derived_units_cancellation() {
        let length = Quantity::new("length", "l", Vec::default());
        let time = Quantity::new("time", "t", Vec::default());
        let velocity = Quantity::new("velocity", "v", vec![(length.clone(), 1), (time.clone(), -1)]);
        
        let m = Unit::new_test_base("meter", "m", &length, 1.0);
        let s = Unit::new_test_base("seconds", "s", &time, 1.0);
        let vel = Unit::new_derived("si_velocity", "ↇ", vec![(m, 1), (s.clone(), -1)]);

        let a = Number{value: 1.0, unit: s};
        
        //let b1 = Number{value: 5.0, unit: m};
        //let b2 = Number{value: 5.0, unit: s};
        // unit that results in dividing b1 by b2, but division is not yet implementet
        let b_unit = Unit{
            name: None,
            symbol: None,
            base_unit: HashMap::from([("m".to_string(), (None, 1)), ("s".to_string(), (None, -1))]),
            quantity: velocity,
            modifier: 1.0};

        let b = Number{value: 1.0, unit: vel};
        let c = a.clone()*b.clone();
        //println!("unit of a: {:?}, unit of b: {:?}", a.unit.base_unit, b.unit.base_unit);
        //println!("resulting unit: {}", c.unit);
        assert_eq!(c.value, 1.0);
        assert_eq!(c.unit.base_unit, HashMap::from([("m".to_string(), (None, 1))]));

        // for the derived case
        //assert_eq!(c.unit.base_unit, HashMap::from([("ↇ".to_string(), (Some(vel.clone()), 1)), ("s".to_string(), (None, 2))]));
    }
    #[test]
    fn test_multiplication_unit_derivation() {
        let test = Quantity::new("test", "?", Vec::default());
        let length = Quantity::new("length", "l", Vec::default());
        let time = Quantity::new("time", "t", Vec::default());
        let velocity = Quantity::new("velocity", "v", vec![(length.clone(), 1), (time.clone(), -1)]);
        
        let u = Unit::new_derived("unitless", "-", Vec::default());
        let t = Unit::new_test_base("test", "~", &test, 1.0);
        let m = Unit::new_test_base("meter", "m", &length, 1.0);
        let s = Unit::new_test_base("seconds", "s", &time, 1.0);
        let vel = Unit::new_derived("si_velocity", "ↇ", vec![(m.clone(), 1), (s.clone(), -1)]);
        //println!("quantity of velocity: {:?}", vel.quantity);
        let a = Number{value: 1.0, unit: m};
        let b = Number{value: 1.0, unit: vel.clone()};
        let c = a.clone()*b.clone();
        //println!("unit of a: {:?}, unit of b: {:?}", a.unit, b.unit);
        //println!("resulting unit: {:?}", c.unit.base_unit);
        //println!("are the quantitys the same? {}", a.unit.quantity == b.unit.quantity);

        assert_eq!(c.unit.base_unit, HashMap::from([("ↇ".to_string(), (Some(vel.clone()), 1)), ("m".to_string(), (None, 1))]));
    }
    // TODO: add unit tests for division
    #[test]
    fn is_comparision_deterministic() {
        let test = Quantity::new("test", "?", Vec::default());
        let length = Quantity::new("length", "l", Vec::default());
        let time = Quantity::new("time", "t", Vec::default());
        let velocity = Quantity::new("velocity", "v", vec![(length.clone(), 1), (time.clone(), -1)]);
        
        let u = Unit::new_derived("unitless", "-", Vec::default());
        let t = Unit::new_test_base("test", "~", &test, 1.0);
        let m = Unit::new_test_base("meter", "m", &length, 1.0);
        let s = Unit::new_test_base("seconds", "s", &time, 1.0);
        let vel = Unit::new_derived("si_velocity", "ↇ", vec![(m.clone(), 1), (s.clone(), -1)]);


        let left = HashMap::from([("ↇ".to_string(), (Some(vel.clone()), 1)), ("m".to_string(), (None, 1))]);
        let right = HashMap::from([("ↇ".to_string(), (Some(vel.clone()), 1)), ("m".to_string(), (None, 1))]);
        //println!("left == right?: {}", left == right);
        assert_eq!(left, right);
    }
}