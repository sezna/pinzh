//! A library for converting Pinyin to Zhuyin (Bopomofo)
//!
//! This library provides functions to convert Pinyin romanization to Zhuyin symbols,
//! handling both the syllables and tones.

use std::collections::HashMap;

/// Represents the different tones in Chinese phonetics
///
/// The five tones can be displayed as either Zhuyin tone marks or numeric values (1-5).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Tone {
    /// First tone (high level) - usually unmarked in Zhuyin
    Tone1,
    /// Second tone (rising) - ˊ
    Tone2,
    /// Third tone (dipping) - ˇ
    Tone3,
    /// Fourth tone (falling) - ˋ
    Tone4,
    /// Fifth tone (neutral/light) - ˙ (placed before syllable)
    Tone5,
}

/// Backwards-compatible type alias
#[deprecated(since = "0.2.0", note = "Use `Tone` instead")]
pub type ZhuyinTone = Tone;

impl Tone {
    /// Convert a numeric tone (1-5) to a Tone enum
    ///
    /// # Example
    /// ```
    /// use pinzh::Tone;
    /// assert_eq!(Tone::from_number(3), Some(Tone::Tone3));
    /// assert_eq!(Tone::from_number(6), None);
    /// ```
    pub fn from_number(n: u8) -> Option<Self> {
        match n {
            1 => Some(Tone::Tone1),
            2 => Some(Tone::Tone2),
            3 => Some(Tone::Tone3),
            4 => Some(Tone::Tone4),
            5 => Some(Tone::Tone5),
            _ => None,
        }
    }

    /// Convert a Zhuyin tone mark to a Tone enum
    ///
    /// # Example
    /// ```
    /// use pinzh::Tone;
    /// assert_eq!(Tone::from_mark("ˇ"), Some(Tone::Tone3));
    /// assert_eq!(Tone::from_mark("x"), None);
    /// ```
    pub fn from_mark(s: &str) -> Option<Self> {
        match s {
            "ˊ" => Some(Tone::Tone2),
            "ˇ" => Some(Tone::Tone3),
            "ˋ" => Some(Tone::Tone4),
            "˙" => Some(Tone::Tone5),
            "" => Some(Tone::Tone1),
            _ => None,
        }
    }

    /// Get the Zhuyin tone mark as a string
    ///
    /// Note: Tone1 returns an empty string as it is typically unmarked in Zhuyin.
    ///
    /// # Example
    /// ```
    /// use pinzh::Tone;
    /// assert_eq!(Tone::Tone3.to_mark(), "ˇ");
    /// assert_eq!(Tone::Tone1.to_mark(), "");
    /// ```
    pub fn to_mark(&self) -> &str {
        match self {
            Tone::Tone1 => "", // First tone is usually unmarked
            Tone::Tone2 => "ˊ",
            Tone::Tone3 => "ˇ",
            Tone::Tone4 => "ˋ",
            Tone::Tone5 => "˙", // Light tone (placed before the syllable)
        }
    }

    /// Get the numeric representation of this tone (1-5)
    ///
    /// # Example
    /// ```
    /// use pinzh::Tone;
    /// assert_eq!(Tone::Tone3.to_number(), 3);
    /// ```
    pub fn to_number(&self) -> u8 {
        match self {
            Tone::Tone1 => 1,
            Tone::Tone2 => 2,
            Tone::Tone3 => 3,
            Tone::Tone4 => 4,
            Tone::Tone5 => 5,
        }
    }
}

impl std::fmt::Display for Tone {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_mark())
    }
}

/// Build the lookup table for Pinyin initials to Zhuyin
fn build_initials_table() -> HashMap<&'static str, &'static str> {
    let mut table = HashMap::new();

    // Labials
    table.insert("b", "ㄅ");
    table.insert("p", "ㄆ");
    table.insert("m", "ㄇ");
    table.insert("f", "ㄈ");

    // Alveolars
    table.insert("d", "ㄉ");
    table.insert("t", "ㄊ");
    table.insert("n", "ㄋ");
    table.insert("l", "ㄌ");

    // Gutturals
    table.insert("g", "ㄍ");
    table.insert("k", "ㄎ");
    table.insert("h", "ㄏ");

    // Palatals
    table.insert("j", "ㄐ");
    table.insert("q", "ㄑ");
    table.insert("x", "ㄒ");

    // Retroflexes
    table.insert("zh", "ㄓ");
    table.insert("ch", "ㄔ");
    table.insert("sh", "ㄕ");
    table.insert("r", "ㄖ");

    // Dental sibilants
    table.insert("z", "ㄗ");
    table.insert("c", "ㄘ");
    table.insert("s", "ㄙ");

    table
}

/// Build the lookup table for Pinyin finals to Zhuyin
fn build_finals_table() -> HashMap<&'static str, &'static str> {
    let mut table = HashMap::new();

    // Simple vowels
    table.insert("a", "ㄚ");
    table.insert("o", "ㄛ");
    table.insert("e", "ㄜ");
    table.insert("er", "ㄦ");

    // i-group
    table.insert("i", "ㄧ");
    table.insert("ia", "ㄧㄚ");
    table.insert("iao", "ㄧㄠ");
    table.insert("ie", "ㄧㄝ");
    table.insert("iu", "ㄧㄡ");
    table.insert("ian", "ㄧㄢ");
    table.insert("in", "ㄧㄣ");
    table.insert("iang", "ㄧㄤ");
    table.insert("ing", "ㄧㄥ");

    // u-group
    table.insert("u", "ㄨ");
    table.insert("ua", "ㄨㄚ");
    table.insert("uo", "ㄨㄛ");
    table.insert("uai", "ㄨㄞ");
    table.insert("ui", "ㄨㄟ");
    table.insert("uan", "ㄨㄢ");
    table.insert("un", "ㄨㄣ");
    table.insert("uang", "ㄨㄤ");
    table.insert("ong", "ㄨㄥ");
    table.insert("ueng", "ㄨㄥ");

    // ü-group
    table.insert("ü", "ㄩ");
    table.insert("üe", "ㄩㄝ");
    table.insert("üan", "ㄩㄢ");
    table.insert("ün", "ㄩㄣ");

    // Also handle 'v' as 'ü' for convenience
    table.insert("v", "ㄩ");
    table.insert("ve", "ㄩㄝ");

    // Compound finals
    table.insert("ai", "ㄞ");
    table.insert("ei", "ㄟ");
    table.insert("ao", "ㄠ");
    table.insert("ou", "ㄡ");
    table.insert("an", "ㄢ");
    table.insert("en", "ㄣ");
    table.insert("ang", "ㄤ");
    table.insert("eng", "ㄥ");

    table
}

/// Parse a Pinyin syllable to extract the initial, final, and tone
fn parse_pinyin_syllable(syllable: &str) -> (Option<String>, Option<String>, Option<u8>) {
    let syllable = syllable.to_lowercase();
    let mut chars: Vec<char> = syllable.chars().collect();

    // Extract tone number if present at the end
    let tone = if !chars.is_empty() && chars.last().unwrap().is_ascii_digit() {
        let tone_char = chars.pop().unwrap();
        tone_char.to_digit(10).map(|d| d as u8)
    } else {
        None
    };

    let syllable_without_tone: String = chars.into_iter().collect();

    // Try to match initials (longest match first)
    let initials_table = build_initials_table();
    let mut initial = None;
    let mut remaining = syllable_without_tone.as_str();

    // Check for two-character initials first (zh, ch, sh)
    if syllable_without_tone.len() >= 2 {
        let two_char = &syllable_without_tone[..2];
        if initials_table.contains_key(two_char) {
            initial = Some(two_char.to_string());
            remaining = &syllable_without_tone[2..];
        }
    }

    // If no two-character initial found, check for single-character initial
    if initial.is_none() && !syllable_without_tone.is_empty() {
        let one_char = &syllable_without_tone[..1];
        if initials_table.contains_key(one_char) {
            initial = Some(one_char.to_string());
            remaining = &syllable_without_tone[1..];
        }
    }

    // The remaining part is the final
    let final_part = if !remaining.is_empty() {
        // Special case: zh, ch, sh, r, z, c, s + i
        // The "i" here is not a real final, it's just part of the Pinyin spelling
        if remaining == "i" {
            if let Some(ref init) = initial {
                if matches!(init.as_str(), "zh" | "ch" | "sh" | "r" | "z" | "c" | "s") {
                    None // No final for these cases
                } else {
                    Some(remaining.to_string())
                }
            } else {
                Some(remaining.to_string())
            }
        } else {
            Some(remaining.to_string())
        }
    } else if initial.is_none() && !syllable_without_tone.is_empty() {
        // If no initial was found, the whole syllable might be a final
        Some(syllable_without_tone)
    } else {
        None
    };

    (initial, final_part, tone)
}

/// Convert a single Pinyin syllable to Zhuyin
///
/// # Arguments
/// * `pinyin` - A Pinyin syllable, optionally with a tone number (1-5) at the end
///
/// # Returns
/// A tuple containing the Zhuyin representation and optional tone
///
/// # Example
/// ```
/// use pinzh::convert_syllable;
///
/// let (zhuyin, tone) = convert_syllable("ma3");
/// assert_eq!(zhuyin, "ㄇㄚ");
/// assert_eq!(tone, Some(pinzh::Tone::Tone3));
/// ```
pub fn convert_syllable(pinyin: &str) -> (String, Option<Tone>) {
    let initials_table = build_initials_table();
    let finals_table = build_finals_table();

    let (initial, final_part, tone_num) = parse_pinyin_syllable(pinyin);

    let mut result = String::new();

    // Convert initial
    if let Some(ref init) = initial {
        if let Some(zhuyin_initial) = initials_table.get(init.as_str()) {
            result.push_str(zhuyin_initial);
        }
    }

    // Convert final
    if let Some(ref fin) = final_part {
        // Special handling for standalone syllables that are also initials
        if initial.is_none() {
            // Handle special cases like "yi", "wu", "yu"
            match fin.as_str() {
                "yi" => result.push_str("ㄧ"),
                "ya" => result.push_str("ㄧㄚ"),
                "yao" => result.push_str("ㄧㄠ"),
                "ye" => result.push_str("ㄧㄝ"),
                "you" => result.push_str("ㄧㄡ"),
                "yan" => result.push_str("ㄧㄢ"),
                "yin" => result.push_str("ㄧㄣ"),
                "yang" => result.push_str("ㄧㄤ"),
                "ying" => result.push_str("ㄧㄥ"),
                "yong" => result.push_str("ㄩㄥ"),

                "wu" => result.push_str("ㄨ"),
                "wa" => result.push_str("ㄨㄚ"),
                "wo" => result.push_str("ㄨㄛ"),
                "wai" => result.push_str("ㄨㄞ"),
                "wei" => result.push_str("ㄨㄟ"),
                "wan" => result.push_str("ㄨㄢ"),
                "wen" => result.push_str("ㄨㄣ"),
                "wang" => result.push_str("ㄨㄤ"),
                "weng" => result.push_str("ㄨㄥ"),

                "yu" => result.push_str("ㄩ"),
                "yue" => result.push_str("ㄩㄝ"),
                "yuan" => result.push_str("ㄩㄢ"),
                "yun" => result.push_str("ㄩㄣ"),

                _ => {
                    // Try direct lookup
                    if let Some(zhuyin_final) = finals_table.get(fin.as_str()) {
                        result.push_str(zhuyin_final);
                    } else {
                        // Return original if not found
                        result.push_str(fin);
                    }
                }
            }
        } else {
            // Check if we need to convert 'u' to 'ü' for j, q, x initials
            let lookup_fin = if let Some(ref init) = initial {
                if matches!(init.as_str(), "j" | "q" | "x") && fin.contains('u') {
                    // Replace 'u' with 'ü' for j, q, x initials
                    fin.replace('u', "ü")
                } else {
                    fin.clone()
                }
            } else {
                fin.clone()
            };

            // Try to find the final in the table
            if let Some(zhuyin_final) = finals_table.get(lookup_fin.as_str()) {
                result.push_str(zhuyin_final);
            } else {
                // If not found, use original
                result.push_str(fin);
            }
        }
    }

    // Convert tone
    let tone = tone_num.and_then(Tone::from_number);

    (result, tone)
}

/// Convert a Pinyin syllable to Zhuyin with tone mark
///
/// # Arguments
/// * `pinyin` - A Pinyin syllable, optionally with a tone number (1-5) at the end
///
/// # Returns
/// The complete Zhuyin representation with tone mark
///
/// # Example
/// ```
/// use pinzh::to_zhuyin;
///
/// let zhuyin = to_zhuyin("ni3");
/// assert_eq!(zhuyin, "ㄋㄧˇ");
/// ```
pub fn to_zhuyin(pinyin: &str) -> String {
    let (zhuyin, tone) = convert_syllable(pinyin);

    match tone {
        Some(Tone::Tone5) => {
            // Light tone mark goes before the syllable
            format!("{}{}", Tone::Tone5.to_mark(), zhuyin)
        }
        Some(t) => {
            // Other tone marks go after the syllable
            format!("{}{}", zhuyin, t.to_mark())
        }
        None => zhuyin,
    }
}

/// Extract the tone from a Pinyin syllable without converting to Zhuyin
///
/// # Arguments
/// * `pinyin` - A Pinyin syllable, optionally with a tone number (1-5) at the end
///
/// # Returns
/// The tone if present, or `None` if no tone number is found
///
/// # Example
/// ```
/// use pinzh::{extract_tone, Tone};
///
/// assert_eq!(extract_tone("ma3"), Some(Tone::Tone3));
/// assert_eq!(extract_tone("ni"), None);
/// ```
pub fn extract_tone(pinyin: &str) -> Option<Tone> {
    let chars: Vec<char> = pinyin.chars().collect();
    if chars.is_empty() {
        return None;
    }

    let last = *chars.last().unwrap();
    if last.is_ascii_digit() {
        last.to_digit(10).and_then(|d| Tone::from_number(d as u8))
    } else {
        None
    }
}

/// Extract the tone from a Zhuyin string with tone marks
///
/// Detects tone marks at the beginning (˙ for Tone5) or end (ˊˇˋ for Tones 2-4).
/// If no tone mark is found, assumes Tone1 (unmarked).
///
/// # Arguments
/// * `zhuyin` - A Zhuyin string, optionally with tone marks
///
/// # Returns
/// The detected tone, or `Tone::Tone1` if no mark is present
///
/// # Example
/// ```
/// use pinzh::{extract_tone_from_zhuyin, Tone};
///
/// assert_eq!(extract_tone_from_zhuyin("ㄇㄚˇ"), Some(Tone::Tone3));
/// assert_eq!(extract_tone_from_zhuyin("˙ㄇㄚ"), Some(Tone::Tone5));
/// assert_eq!(extract_tone_from_zhuyin("ㄇㄚ"), Some(Tone::Tone1));
/// ```
pub fn extract_tone_from_zhuyin(zhuyin: &str) -> Option<Tone> {
    if zhuyin.is_empty() {
        return None;
    }

    // Check for leading light tone mark (Tone5)
    if zhuyin.starts_with('˙') {
        return Some(Tone::Tone5);
    }

    // Check for trailing tone marks
    let last_char = zhuyin.chars().last()?;
    match last_char {
        'ˊ' => Some(Tone::Tone2),
        'ˇ' => Some(Tone::Tone3),
        'ˋ' => Some(Tone::Tone4),
        _ => Some(Tone::Tone1), // No mark = first tone
    }
}

/// Remove the tone number from a Pinyin syllable
///
/// # Arguments
/// * `pinyin` - A Pinyin syllable, optionally with a tone number (1-5) at the end
///
/// # Returns
/// The Pinyin syllable without the tone number
///
/// # Example
/// ```
/// use pinzh::strip_tone;
///
/// assert_eq!(strip_tone("ma3"), "ma");
/// assert_eq!(strip_tone("ni"), "ni");
/// ```
pub fn strip_tone(pinyin: &str) -> String {
    let mut chars: Vec<char> = pinyin.chars().collect();
    if !chars.is_empty() {
        let last = *chars.last().unwrap();
        if last.is_ascii_digit() && ('1'..='5').contains(&last) {
            chars.pop();
        }
    }
    chars.into_iter().collect()
}

/// Remove the tone mark from a Zhuyin string
///
/// # Arguments
/// * `zhuyin` - A Zhuyin string, optionally with tone marks
///
/// # Returns
/// The Zhuyin string without tone marks
///
/// # Example
/// ```
/// use pinzh::strip_tone_from_zhuyin;
///
/// assert_eq!(strip_tone_from_zhuyin("ㄇㄚˇ"), "ㄇㄚ");
/// assert_eq!(strip_tone_from_zhuyin("˙ㄇㄚ"), "ㄇㄚ");
/// ```
pub fn strip_tone_from_zhuyin(zhuyin: &str) -> String {
    let mut result = zhuyin.to_string();

    // Remove leading light tone mark
    if result.starts_with('˙') {
        result = result.chars().skip(1).collect();
    }

    // Remove trailing tone marks
    if let Some(last) = result.chars().last() {
        if matches!(last, 'ˊ' | 'ˇ' | 'ˋ') {
            result.pop();
        }
    }

    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_syllables() {
        assert_eq!(to_zhuyin("ma"), "ㄇㄚ");
        assert_eq!(to_zhuyin("ni"), "ㄋㄧ");
        assert_eq!(to_zhuyin("hao"), "ㄏㄠ");
    }

    #[test]
    fn test_with_tones() {
        assert_eq!(to_zhuyin("ma1"), "ㄇㄚ");  // First tone usually unmarked
        assert_eq!(to_zhuyin("ma2"), "ㄇㄚˊ");
        assert_eq!(to_zhuyin("ma3"), "ㄇㄚˇ");
        assert_eq!(to_zhuyin("ma4"), "ㄇㄚˋ");
        assert_eq!(to_zhuyin("ma5"), "˙ㄇㄚ");  // Light tone before syllable
    }

    #[test]
    fn test_complex_initials() {
        assert_eq!(to_zhuyin("zhi"), "ㄓ");
        assert_eq!(to_zhuyin("chi"), "ㄔ");
        assert_eq!(to_zhuyin("shi"), "ㄕ");
        assert_eq!(to_zhuyin("ri"), "ㄖ");
        assert_eq!(to_zhuyin("zi"), "ㄗ");
        assert_eq!(to_zhuyin("ci"), "ㄘ");
        assert_eq!(to_zhuyin("si"), "ㄙ");
        assert_eq!(to_zhuyin("zhong"), "ㄓㄨㄥ");
        assert_eq!(to_zhuyin("chang"), "ㄔㄤ");
    }

    #[test]
    fn test_standalone_vowels() {
        assert_eq!(to_zhuyin("yi"), "ㄧ");
        assert_eq!(to_zhuyin("wu"), "ㄨ");
        assert_eq!(to_zhuyin("yu"), "ㄩ");
        assert_eq!(to_zhuyin("er"), "ㄦ");
    }

    #[test]
    fn test_j_q_x_with_u() {
        assert_eq!(to_zhuyin("ju"), "ㄐㄩ");
        assert_eq!(to_zhuyin("qu"), "ㄑㄩ");
        assert_eq!(to_zhuyin("xu"), "ㄒㄩ");
        assert_eq!(to_zhuyin("juan"), "ㄐㄩㄢ");
    }

    #[test]
    fn test_w_y_syllables() {
        assert_eq!(to_zhuyin("wang"), "ㄨㄤ");
        assert_eq!(to_zhuyin("yang"), "ㄧㄤ");
        assert_eq!(to_zhuyin("yue"), "ㄩㄝ");
        assert_eq!(to_zhuyin("wei"), "ㄨㄟ");
    }

    #[test]
    fn test_tone_from_number() {
        assert_eq!(Tone::from_number(1), Some(Tone::Tone1));
        assert_eq!(Tone::from_number(2), Some(Tone::Tone2));
        assert_eq!(Tone::from_number(3), Some(Tone::Tone3));
        assert_eq!(Tone::from_number(4), Some(Tone::Tone4));
        assert_eq!(Tone::from_number(5), Some(Tone::Tone5));
        assert_eq!(Tone::from_number(0), None);
        assert_eq!(Tone::from_number(6), None);
    }

    #[test]
    fn test_tone_to_number() {
        assert_eq!(Tone::Tone1.to_number(), 1);
        assert_eq!(Tone::Tone2.to_number(), 2);
        assert_eq!(Tone::Tone3.to_number(), 3);
        assert_eq!(Tone::Tone4.to_number(), 4);
        assert_eq!(Tone::Tone5.to_number(), 5);
    }

    #[test]
    fn test_tone_from_mark() {
        assert_eq!(Tone::from_mark(""), Some(Tone::Tone1));
        assert_eq!(Tone::from_mark("ˊ"), Some(Tone::Tone2));
        assert_eq!(Tone::from_mark("ˇ"), Some(Tone::Tone3));
        assert_eq!(Tone::from_mark("ˋ"), Some(Tone::Tone4));
        assert_eq!(Tone::from_mark("˙"), Some(Tone::Tone5));
        assert_eq!(Tone::from_mark("x"), None);
    }

    #[test]
    fn test_tone_to_mark() {
        assert_eq!(Tone::Tone1.to_mark(), "");
        assert_eq!(Tone::Tone2.to_mark(), "ˊ");
        assert_eq!(Tone::Tone3.to_mark(), "ˇ");
        assert_eq!(Tone::Tone4.to_mark(), "ˋ");
        assert_eq!(Tone::Tone5.to_mark(), "˙");
    }

    #[test]
    fn test_tone_display() {
        assert_eq!(format!("{}", Tone::Tone1), "");
        assert_eq!(format!("{}", Tone::Tone2), "ˊ");
        assert_eq!(format!("{}", Tone::Tone3), "ˇ");
        assert_eq!(format!("{}", Tone::Tone4), "ˋ");
        assert_eq!(format!("{}", Tone::Tone5), "˙");
    }

    #[test]
    fn test_tone_roundtrip() {
        for n in 1..=5 {
            let tone = Tone::from_number(n).unwrap();
            assert_eq!(tone.to_number(), n);
        }
        for tone in [Tone::Tone1, Tone::Tone2, Tone::Tone3, Tone::Tone4, Tone::Tone5] {
            let mark = tone.to_mark();
            assert_eq!(Tone::from_mark(mark), Some(tone));
        }
    }

    #[test]
    fn test_extract_tone() {
        assert_eq!(extract_tone("ma1"), Some(Tone::Tone1));
        assert_eq!(extract_tone("ma2"), Some(Tone::Tone2));
        assert_eq!(extract_tone("ma3"), Some(Tone::Tone3));
        assert_eq!(extract_tone("ma4"), Some(Tone::Tone4));
        assert_eq!(extract_tone("ma5"), Some(Tone::Tone5));
        assert_eq!(extract_tone("ma"), None);
        assert_eq!(extract_tone("ni3hao3"), Some(Tone::Tone3)); // Gets last tone
        assert_eq!(extract_tone(""), None);
    }

    #[test]
    fn test_extract_tone_from_zhuyin() {
        assert_eq!(extract_tone_from_zhuyin("ㄇㄚ"), Some(Tone::Tone1));
        assert_eq!(extract_tone_from_zhuyin("ㄇㄚˊ"), Some(Tone::Tone2));
        assert_eq!(extract_tone_from_zhuyin("ㄇㄚˇ"), Some(Tone::Tone3));
        assert_eq!(extract_tone_from_zhuyin("ㄇㄚˋ"), Some(Tone::Tone4));
        assert_eq!(extract_tone_from_zhuyin("˙ㄇㄚ"), Some(Tone::Tone5));
        assert_eq!(extract_tone_from_zhuyin(""), None);
    }

    #[test]
    fn test_strip_tone() {
        assert_eq!(strip_tone("ma1"), "ma");
        assert_eq!(strip_tone("ma2"), "ma");
        assert_eq!(strip_tone("ma3"), "ma");
        assert_eq!(strip_tone("ma4"), "ma");
        assert_eq!(strip_tone("ma5"), "ma");
        assert_eq!(strip_tone("ma"), "ma");
        assert_eq!(strip_tone("ma6"), "ma6"); // 6 is not a valid tone
        assert_eq!(strip_tone(""), "");
    }

    #[test]
    fn test_strip_tone_from_zhuyin() {
        assert_eq!(strip_tone_from_zhuyin("ㄇㄚ"), "ㄇㄚ");
        assert_eq!(strip_tone_from_zhuyin("ㄇㄚˊ"), "ㄇㄚ");
        assert_eq!(strip_tone_from_zhuyin("ㄇㄚˇ"), "ㄇㄚ");
        assert_eq!(strip_tone_from_zhuyin("ㄇㄚˋ"), "ㄇㄚ");
        assert_eq!(strip_tone_from_zhuyin("˙ㄇㄚ"), "ㄇㄚ");
        assert_eq!(strip_tone_from_zhuyin(""), "");
    }
}