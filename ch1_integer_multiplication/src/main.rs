use std::cmp;
use std::convert::Infallible;
use std::fmt;
use std::io;
use std::io::Write;
use std::str::FromStr;

#[derive(Debug, PartialEq)]
struct BigInteger {
    digits: Vec<u8>,
}

impl BigInteger {
    const RADIX: u8 = 10;

    fn length(&self) -> usize {
        self.digits.len()
    }

    fn get_digit(&self, position: usize) -> Option<u8> {
        if position < self.length() {
            Some(self.digits[position])
        } else {
            None
        }
    }

    fn add(&self, another: &Self) -> Self {
        let length = cmp::max(self.length(), another.length());
        let mut digits = Vec::with_capacity(length);
        let mut carry = 0;
        for i in 0..length {
            let first = self.get_digit(i).unwrap_or(0);
            let second = another.get_digit(i).unwrap_or(0);
            let sum = first + second + carry;
            digits.push(sum % Self::RADIX);
            carry = sum / Self::RADIX;
        }

        if carry > 0 {
            digits.push(carry);
        }

        Self { digits }
    }

    fn complement(&self) -> Self {
        let mut digits = Vec::with_capacity(self.length());
        for digit in &self.digits {
            digits.push(Self::RADIX - digit - 1);
        }

        Self { digits }
    }

    fn subtract(&self, another: &Self) -> Self {
        let length = cmp::max(self.length(), another.length());
        let complement = self.pad_left(length).complement();
        let sum = complement.add(another);
        sum.complement()
    }

    fn shift_left(&self, places: usize) -> Self {
        if places == 0 {
            return Self {
                digits: self.digits.clone(),
            };
        }

        let mut digits = Vec::with_capacity(self.length() + places);
        for _ in 0..places {
            digits.push(0);
        }

        for digit in &self.digits {
            digits.push(*digit);
        }

        Self { digits }
    }

    fn pad_left(&self, length: usize) -> Self {
        if length <= self.length() {
            return Self {
                digits: self.digits.clone(),
            };
        }

        let mut digits = Vec::with_capacity(length);
        for digit in &self.digits {
            digits.push(*digit);
        }

        let padding = length - self.length();
        for _ in 0..padding {
            digits.push(0);
        }

        Self { digits }
    }

    fn trim_left(&self) -> Self {
        if self.length() == 1 || self.digits[self.length() - 1] != 0 {
            return Self {
                digits: self.digits.clone(),
            };
        }

        let mut digits: Vec<u8> = Vec::with_capacity(self.length());
        let mut non_zero_found = false;
        for digit in self.digits.iter().rev() {
            if non_zero_found {
                digits.push(*digit);
            } else if *digit != 0 {
                digits.push(*digit);
                non_zero_found = true;
            }
        }

        if digits.len() == 0 {
            return Self { digits: vec![0] };
        }

        Self {
            digits: digits.into_iter().rev().collect(),
        }
    }

    fn high(&self) -> Self {
        let length = self.length();
        let length_over_2 = length / 2;
        let digits: Vec<u8> = self.digits[length_over_2..].into();
        Self { digits }
    }

    fn low(&self) -> Self {
        let length = self.length();
        let length_over_2 = length / 2;
        let digits: Vec<u8> = self.digits[..length_over_2].into();
        Self { digits }
    }

    fn multiply_by_scalar(&self, scalar: u8) -> Self {
        if scalar == 0 {
            return Self { digits: vec![0] };
        } else if scalar == 1 {
            return Self {
                digits: self.digits.clone(),
            };
        }

        let mut digits = Vec::with_capacity(self.length());
        let mut carry = 0;
        for digit in &self.digits {
            let product = digit * scalar + carry;
            digits.push(product % Self::RADIX);
            carry = product / Self::RADIX;
        }

        if carry > 0 {
            digits.push(carry);
        }

        Self { digits }
    }

    fn multiply(&self, another: &Self) -> Self {
        let mut partial_products: Vec<Self> = Vec::with_capacity(another.length());
        for (index, digit) in another.digits.iter().enumerate() {
            let partial_product = self.multiply_by_scalar(*digit);
            partial_products.push(partial_product.shift_left(index));
        }

        let mut result: Self = Self { digits: vec![0] };
        for partial_product in partial_products.into_iter() {
            result = result.add(&partial_product);
        }

        result
    }

    fn multiply_recursive(&self, another: &Self) -> Self {
        if self.length() == 1 && another.length() == 1 {
            let product = self.digits[0] * another.digits[0];
            return product.into();
        }

        let length = cmp::max(self.length(), another.length()).next_power_of_two();
        let first = self.pad_left(length);
        let second = another.pad_left(length);

        let a = first.high();
        let b = first.low();
        let c = second.high();
        let d = second.low();

        let ac = a.multiply_recursive(&c);
        let ad = a.multiply_recursive(&d);
        let bc = b.multiply_recursive(&c);
        let bd = b.multiply_recursive(&d);

        let adbc = ad.add(&bc);
        let length_over_2 = length / 2;
        ac.shift_left(length)
            .add(&adbc.shift_left(length_over_2))
            .add(&bd)
            .trim_left()
    }

    fn multiply_karatsuba(&self, another: &Self) -> Self {
        if self.length() == 1 && another.length() == 1 {
            let product = self.digits[0] * another.digits[0];
            return product.into();
        }

        let length = cmp::max(self.length(), another.length()).next_power_of_two();
        let first = self.pad_left(length);
        let second = another.pad_left(length);

        let a = first.high();
        let b = first.low();
        let c = second.high();
        let d = second.low();

        let p = a.add(&b);
        let q = c.add(&d);

        let ac = a.multiply_karatsuba(&c);
        let bd = b.multiply_karatsuba(&d);
        let pq = p.multiply_karatsuba(&q);

        let adbc = pq.subtract(&ac).subtract(&bd);
        let length_over_2 = length / 2;
        ac.shift_left(length)
            .add(&adbc.shift_left(length_over_2))
            .add(&bd)
            .trim_left()
    }
}

impl From<u8> for BigInteger {
    fn from(value: u8) -> Self {
        const MAX_DIGITS_IN_U8: usize = 3;

        if value < 10 {
            return Self {
                digits: vec![value],
            };
        } else if value < 100 {
            return Self {
                digits: vec![value % Self::RADIX, value / Self::RADIX],
            };
        }

        let mut digits = Vec::with_capacity(MAX_DIGITS_IN_U8);
        let mut value = value;
        while value > 0 {
            digits.push(value % Self::RADIX);
            value /= Self::RADIX;
        }

        Self { digits }
    }
}

impl From<u16> for BigInteger {
    fn from(value: u16) -> Self {
        const MAX_DIGITS_IN_U16: usize = 5;

        if value <= u8::MAX.into() {
            return (value as u8).into();
        }

        let mut digits = Vec::with_capacity(MAX_DIGITS_IN_U16);
        let mut value = value;
        while value > 0 {
            digits.push((value % Self::RADIX as u16) as u8);
            value /= Self::RADIX as u16;
        }

        Self { digits }
    }
}

impl From<u32> for BigInteger {
    fn from(value: u32) -> Self {
        const MAX_DIGITS_IN_U32: usize = 10;

        if value <= u8::MAX.into() {
            return (value as u8).into();
        }

        let mut digits = Vec::with_capacity(MAX_DIGITS_IN_U32);
        let mut value = value;
        while value > 0 {
            digits.push((value % Self::RADIX as u32) as u8);
            value /= Self::RADIX as u32;
        }

        Self { digits }
    }
}

impl From<u64> for BigInteger {
    fn from(value: u64) -> Self {
        const MAX_DIGITS_IN_U64: usize = 20;

        if value <= u8::MAX.into() {
            return (value as u8).into();
        }

        let mut digits = Vec::with_capacity(MAX_DIGITS_IN_U64);
        let mut value = value;
        while value > 0 {
            digits.push((value % Self::RADIX as u64) as u8);
            value /= Self::RADIX as u64;
        }

        Self { digits }
    }
}

impl From<u128> for BigInteger {
    fn from(value: u128) -> Self {
        const MAX_DIGITS_IN_U128: usize = 40;

        if value <= u8::MAX.into() {
            return (value as u8).into();
        }

        let mut digits = Vec::with_capacity(MAX_DIGITS_IN_U128);
        let mut value = value;
        while value > 0 {
            digits.push((value % Self::RADIX as u128) as u8);
            value /= Self::RADIX as u128;
        }

        Self { digits }
    }
}

impl FromStr for BigInteger {
    type Err = Infallible;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut digits = Vec::with_capacity(s.len());
        for ch in s.chars().rev() {
            if let Some(digit) = ch.to_digit(Self::RADIX.into()) {
                let digit: u8 = digit.try_into().unwrap();
                digits.push(digit);
            }
        }

        Ok(Self { digits })
    }
}

impl fmt::Display for BigInteger {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut str = String::with_capacity(self.length());
        for digit in self.digits.iter().rev() {
            let digit: char = (digit + '0' as u8).into();
            str.push(digit);
        }

        write!(f, "{}", str)
    }
}

fn main() {
    let mut first = String::new();
    print!("Input first number: ");
    io::stdout().flush().unwrap();
    io::stdin().read_line(&mut first).unwrap();

    let mut second = String::new();
    print!("Input second number: ");
    io::stdout().flush().unwrap();
    io::stdin().read_line(&mut second).unwrap();

    let first: BigInteger = first.trim().parse().unwrap();
    let second: BigInteger = second.trim().parse().unwrap();

    let product = first.multiply(&second);
    println!("{} * {} = {} (simple)", first, second, product);

    let product = first.multiply_recursive(&second);
    println!("{} * {} = {} (recursive)", first, second, product);

    let product = first.multiply_karatsuba(&second);
    println!("{} * {} = {} (karatsuba)", first, second, product);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_from_u8() {
        // Arrange
        let input = 123u8;

        // Act
        let result: BigInteger = input.into();

        // Assert
        let expected = BigInteger {
            digits: vec![3, 2, 1],
        };

        assert_eq!(result, expected);
    }

    #[test]
    fn test_from_u16() {
        // Arrange
        let input = 12345u16;

        // Act
        let result: BigInteger = input.into();

        // Assert
        let expected = BigInteger {
            digits: vec![5, 4, 3, 2, 1],
        };

        assert_eq!(result, expected);
    }

    #[test]
    fn test_from_u32() {
        // Arrange
        let input = 1234567u32;

        // Act
        let result: BigInteger = input.into();

        // Assert
        let expected = BigInteger {
            digits: vec![7, 6, 5, 4, 3, 2, 1],
        };

        assert_eq!(result, expected);
    }

    #[test]
    fn test_from_u64() {
        // Arrange
        let input = 123456789012u64;

        // Act
        let result: BigInteger = input.into();

        // Assert
        let expected = BigInteger {
            digits: vec![2, 1, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1],
        };

        assert_eq!(result, expected);
    }

    #[test]
    fn test_from_u128() {
        // Arrange
        let input = 1234567890123456789012u128;

        // Act
        let result: BigInteger = input.into();

        // Assert
        let expected = BigInteger {
            digits: vec![
                2, 1, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1,
            ],
        };

        assert_eq!(result, expected);
    }

    #[test]
    fn test_parse() {
        // Arrange
        let input = "5678";

        // Act
        let result: BigInteger = input.parse().unwrap();

        // Assert
        let expected = BigInteger {
            digits: vec![8, 7, 6, 5],
        };

        assert_eq!(result, expected);
    }

    #[test]
    fn test_length() {
        // Arrange
        let value: BigInteger = "5678".parse().unwrap();

        // Act
        let length = value.length();

        // Assert
        assert_eq!(length, 4);
    }

    #[test]
    fn test_get_digit() {
        // Arrange
        let value: BigInteger = "5678".parse().unwrap();

        // Act
        let digit = value.get_digit(0);

        // Assert
        assert_eq!(digit, Some(8));
    }

    #[test]
    fn test_get_digit_out_of_range() {
        // Arrange
        let value: BigInteger = "5678".parse().unwrap();

        // Act
        let digit = value.get_digit(6);

        // Assert
        assert_eq!(digit, None);
    }

    #[test]
    fn test_add() {
        // Arrange
        let value: BigInteger = "5678".parse().unwrap();
        let another: BigInteger = "1234".parse().unwrap();

        // Act
        let sum = value.add(&another);

        // Assert
        let expected: BigInteger = "6912".parse().unwrap();
        assert_eq!(sum, expected);
    }

    #[test]
    fn test_complement() {
        // Arrange
        let value: BigInteger = "5678".parse().unwrap();

        // Act
        let complement = value.complement();

        // Assert
        let expected: BigInteger = "4321".parse().unwrap();
        assert_eq!(complement, expected);
    }

    #[test]
    fn test_subtract() {
        // Arrange
        let value: BigInteger = "5678".parse().unwrap();
        let another: BigInteger = "1234".parse().unwrap();

        // Act
        let sum = value.subtract(&another);

        // Assert
        let expected: BigInteger = "4444".parse().unwrap();
        assert_eq!(sum, expected);
    }

    #[test]
    fn test_shift_left() {
        // Arrange
        let value: BigInteger = "5678".parse().unwrap();

        // Act
        let result = value.shift_left(2);

        // Assert
        let expected: BigInteger = "567800".parse().unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn test_shift_left_by_zero() {
        // Arrange
        let value: BigInteger = "5678".parse().unwrap();

        // Act
        let result = value.shift_left(0);

        // Assert
        let expected: BigInteger = "5678".parse().unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn test_pad_left() {
        // Arrange
        let value: BigInteger = "5678".parse().unwrap();

        // Act
        let result = value.pad_left(6);

        // Assert
        let expected: BigInteger = "005678".parse().unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn test_pad_left_by_zero() {
        // Arrange
        let value: BigInteger = "5678".parse().unwrap();

        // Act
        let result = value.pad_left(0);

        // Assert
        let expected: BigInteger = "5678".parse().unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn test_trim_left() {
        // Arrange
        let value: BigInteger = "005678".parse().unwrap();

        // Act
        let result = value.trim_left();

        // Assert
        let expected: BigInteger = "5678".parse().unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn test_high() {
        // Arrange
        let value: BigInteger = "5678".parse().unwrap();

        // Act
        let result = value.high();

        // Assert
        let expected: BigInteger = "56".parse().unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn test_low() {
        // Arrange
        let value: BigInteger = "5678".parse().unwrap();

        // Act
        let result = value.low();

        // Assert
        let expected: BigInteger = "78".parse().unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn test_multiply_by_scalar() {
        // Arrange
        let value: BigInteger = "5678".parse().unwrap();

        // Act
        let result = value.multiply_by_scalar(2);

        // Assert
        let expected: BigInteger = "11356".parse().unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn test_multiply_by_scalar_zero() {
        // Arrange
        let value: BigInteger = "5678".parse().unwrap();

        // Act
        let result = value.multiply_by_scalar(0);

        // Assert
        let expected: BigInteger = "0".parse().unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn test_multiply_by_scalar_one() {
        // Arrange
        let value: BigInteger = "5678".parse().unwrap();

        // Act
        let result = value.multiply_by_scalar(1);

        // Assert
        let expected: BigInteger = "5678".parse().unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn test_multiply() {
        // Arrange
        let value: BigInteger = "5678".parse().unwrap();
        let another: BigInteger = "1234".parse().unwrap();

        // Act
        let result = value.multiply(&another);

        // Assert
        let expected: BigInteger = "7006652".parse().unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn test_multiply_by_zero() {
        // Arrange
        let value: BigInteger = "5678".parse().unwrap();
        let another: BigInteger = "0".parse().unwrap();

        // Act
        let result = value.multiply(&another);

        // Assert
        let expected: BigInteger = "0".parse().unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn test_multiply_by_one() {
        // Arrange
        let value: BigInteger = "5678".parse().unwrap();
        let another: BigInteger = "1".parse().unwrap();

        // Act
        let result = value.multiply(&another);

        // Assert
        let expected: BigInteger = "5678".parse().unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn test_multiply_recursive() {
        // Arrange
        let value: BigInteger = "5678".parse().unwrap();
        let another: BigInteger = "1234".parse().unwrap();

        // Act
        let result = value.multiply_recursive(&another);

        // Assert
        let expected: BigInteger = "7006652".parse().unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn test_multiply_recursive_by_zero() {
        // Arrange
        let value: BigInteger = "5678".parse().unwrap();
        let another: BigInteger = "0".parse().unwrap();

        // Act
        let result = value.multiply_recursive(&another);

        // Assert
        let expected: BigInteger = "0".parse().unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn test_multiply_recursive_by_one() {
        // Arrange
        let value: BigInteger = "5678".parse().unwrap();
        let another: BigInteger = "1".parse().unwrap();

        // Act
        let result = value.multiply_recursive(&another);

        // Assert
        let expected: BigInteger = "5678".parse().unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn test_multiply_karatsuba() {
        // Arrange
        let value: BigInteger = "5678".parse().unwrap();
        let another: BigInteger = "1234".parse().unwrap();

        // Act
        let result = value.multiply_karatsuba(&another);

        // Assert
        let expected: BigInteger = "7006652".parse().unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn test_multiply_karatsuba_by_zero() {
        // Arrange
        let value: BigInteger = "5678".parse().unwrap();
        let another: BigInteger = "0".parse().unwrap();

        // Act
        let result = value.multiply_karatsuba(&another);

        // Assert
        let expected: BigInteger = "0".parse().unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn test_multiply_karatsuba_by_one() {
        // Arrange
        let value: BigInteger = "5678".parse().unwrap();
        let another: BigInteger = "1".parse().unwrap();

        // Act
        let result = value.multiply_karatsuba(&another);

        // Assert
        let expected: BigInteger = "5678".parse().unwrap();
        assert_eq!(result, expected);
    }
}
