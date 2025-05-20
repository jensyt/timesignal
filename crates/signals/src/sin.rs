//! Calculate 32-bit sine.
//!
//! This module is adapted from [`libm`] and exports a single function, [`sin32`].
//!
//! [`libm`]: https://github.com/rust-lang/libm

/*
 * ====================================================
 * Copyright (C) 1993 by Sun Microsystems, Inc. All rights reserved.
 *
 * Developed at SunPro, a Sun Microsystems, Inc. business.
 * Permission to use, copy, modify, and distribute this
 * software is freely granted, provided that this notice
 * is preserved.
 * ====================================================
 */

const TOINT: f64 = 1.5 / f64::EPSILON;
/// 53 bits of 2/pi
const INV_PIO2: f64 = 6.36619772367581382433e-01; /* 0x3FE45F30, 0x6DC9C883 */
/// first 25 bits of pi/2
const PIO2_1: f64 = 1.57079631090164184570e+00; /* 0x3FF921FB, 0x50000000 */
/// pi/2 - pio2_1
const PIO2_1T: f64 = 1.58932547735281966916e-08; /* 0x3E5110b4, 0x611A6263 */

const C0: f64 = -0.499999997251031003120; /* -0x1ffffffd0c5e81.0p-54 */
const C1: f64 = 0.0416666233237390631894; /*  0x155553e1053a42.0p-57 */
const C2: f64 = -0.00138867637746099294692; /* -0x16c087e80f1e27.0p-62 */
const C3: f64 = 0.0000243904487962774090654; /*  0x199342e0ee5069.0p-68 */

const S1: f64 = -0.166666666416265235595; /* -0x15555554cbac77.0p-55 */
const S2: f64 = 0.0083333293858894631756; /*  0x111110896efbb2.0p-59 */
const S3: f64 = -0.000198393348360966317347; /* -0x1a00f9e2cae774.0p-65 */
const S4: f64 = 0.0000027183114939898219064; /*  0x16cd878c3b46a7.0p-71 */

/// Calculate `x % (pi / 2)`.
///
/// Adapted from `libm::rem_pio2f` assuming `|x| ~< 2^28*(pi/2)`.
#[inline(always)]
fn rem_pio2f(x: f32) -> (i32, f64) {
	let x64 = x as f64;

	/* |x| ~< 2^28*(pi/2), medium size */
	/* Use a specialized rint() to get fn.  Assume round-to-nearest. */
	let tmp = x64 * INV_PIO2 + TOINT;
	// force rounding of tmp to it's storage format on x87 to avoid
	// excess precision issues.
	#[cfg(all(target_arch = "x86", not(target_feature = "sse2")))]
	let tmp = force_eval!(tmp);
	let f_n = tmp - TOINT;
	(f_n as i32, x64 - f_n * PIO2_1 - f_n * PIO2_1T)
}

/// Calculate `cos(x)` where `|x| <= pi/2`.
///
/// Copied from `libm::k_cosf`.
#[inline(always)]
fn k_cosf(x: f64) -> f32 {
	let z = x * x;
	let w = z * z;
	let r = C2 + z * C3;
	(((1.0 + z * C0) + w * C1) + (w * z) * r) as f32
}

/// Calculate `sin(x)` where `|x| <= pi/2`.
///
/// Copied from `libm::k_sinf`.
#[inline(always)]
fn k_sinf(x: f64) -> f32 {
	let z = x * x;
	let w = z * z;
	let r = S3 + z * S4;
	let s = z * x;
	((x + s * (S1 + z * S2)) + s * w * r) as f32
}

/// Calculate `sin(x)` where `|x| ~< 2^28*(pi/2)`.
///
/// Adapted from `libm::sinf`.
pub fn sin32(x: f32) -> f32 {
	let (n, y) = rem_pio2f(x);

	match n & 3 {
		0 => k_sinf(y),
		1 => k_cosf(y),
		2 => k_sinf(-y),
		_ => -k_cosf(y),
	}
}
