
use std::collections::{HashMap, HashSet};
use std::hash::Hash;

/// Describes how an algebraic operation produced an element.
///
/// Operations that may produce no element in the represented carrier, such as
/// meet and subtract, return `Option<AlgebraicResult<_>>`. `None` represents
/// that absence; every `AlgebraicResult` describes a retained element that
/// actually exists.
///
/// NOTE 2: The following conditions for the Identity bitmask must be respected or the implementation may panic or
/// produce logically invalid results.
/// - The bit mask must be non-zero
/// - Bits beyond the number of operation arguments must not be set.  e.g. an arity-2 operation may only set bit 0
///     and bit 1, but never any additional bits.
/// - Setting two or more bits simultaneously asserts the arguments are identities of each other, so this must be
///     true in fact.
/// - The inverse of the above does not hold.  E.g. if multiple bits are not set, it may **not** be assumed that 
///     the arguments are not identities of each other.
/// - Non-commutative operations, such as [DistributiveLattice::psubtract], must never set bits beyond bit 0 ([SELF_IDENT])
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AlgebraicResult<V> {
    /// A result indicating the output element is identical to the input element(s) identified by the bit mask
    ///
    /// NOTE: The constants [SELF_IDENT] and [COUNTER_IDENT] can be used as conveniences when specifying the bitmask.
    Identity(u64),
    /// A new result element
    Element(V),
}

/// A bitmask value to `or` into the [AlgebraicResult::Identity] argument to specify the result is the identity of `self`
pub const SELF_IDENT: u64 = 0x1;

/// A bitmask value to `or` into the [AlgebraicResult::Identity] argument to specify the result is the identity of `other`
pub const COUNTER_IDENT: u64 = 0x2;

impl<V> AlgebraicResult<V> {
    /// Returns `true` is `self` is [AlgebraicResult::Identity], otherwise returns `false`
    #[inline]
    pub fn is_identity(&self) -> bool {
        matches!(self, AlgebraicResult::Identity(_))
    }
    /// Returns `true` is `self` is [AlgebraicResult::Element], otherwise returns `false`
    #[inline]
    pub fn is_element(&self) -> bool {
        matches!(self, AlgebraicResult::Element(_))
    }
    /// Returns the identity mask from a [AlgebraicResult::Identity], otherwise returns `None`
    #[inline]
    pub fn identity_mask(&self) -> Option<u64> {
        match self {
            Self::Identity(mask) => Some(*mask),
            Self::Element(_) => None,
        }
    }
    /// Swaps the mask bits in an [AlgebraicResult::Identity] result, for an arity-2 operation, such that
    /// the [SELF_IDENT] bit becomes the [COUNTER_IDENT] bit, and vise-versa
    ///
    /// Removes identity mask bits higher than 2
    #[inline]
    pub fn invert_identity(self) -> Self {
        match self {
            Self::Identity(mask) => {
                let new_mask = ((mask & SELF_IDENT) << 1) | ((mask & COUNTER_IDENT) >> 1);
                AlgebraicResult::Identity(new_mask)
            },
            Self::Element(v) => AlgebraicResult::Element(v),
        }
    }
    /// Maps a `AlgebraicResult<V>` to `AlgebraicResult<U>` by applying a function to a contained value, if
    /// self is `AlgebraicResult::Element(V)`.  Otherwise returns the value of `self`
    #[inline]
    pub fn map<U, F>(self, f: F) -> AlgebraicResult<U>
        where F: FnOnce(V) -> U,
    {
        match self {
            Self::Identity(mask) => AlgebraicResult::Identity(mask),
            Self::Element(v) => AlgebraicResult::Element(f(v)),
        }
    }
    /// Converts from `&AlgebraicResult<V>` to `AlgebraicResult<&V>`
    #[inline]
    pub fn as_ref(&self) -> AlgebraicResult<&V> {
        match *self {
            Self::Element(ref v) => AlgebraicResult::Element(v),
            Self::Identity(mask) => AlgebraicResult::Identity(mask),
        }
    }
    /// Returns an option containing the `Element` value, substituting the result of the `ident_f` closure
    /// if `self` is [Identity](AlgebraicResult::Identity)
    ///
    /// The index of the first identity argument is passed to the closure.  E.g. `0` for self, etc.
    #[inline]
    pub fn map_into_option<IdentF>(self, ident_f: IdentF) -> Option<V>
        where IdentF: FnOnce(usize) -> Option<V>
    {
        match self {
            Self::Element(v) => Some(v),
            Self::Identity(mask) => ident_f(mask.trailing_zeros() as usize),
        }
    }
    /// Returns an option containing the `Element` value, substituting the result from the corresponding
    /// index in the `idents` table if `self` is [Identity](AlgebraicResult::Identity)
    #[inline]
    pub fn into_option<I: AsRef<[VRef]>, VRef: std::borrow::Borrow<V>>(self, idents: I) -> Option<V>
        where V: Clone
    {
        match self {
            Self::Element(v) => Some(v),
            Self::Identity(mask) => {
                let idents = idents.as_ref();
                Some(idents[mask.trailing_zeros() as usize].borrow().clone())
            },
        }
    }

    /// Returns the contained `Element` value or an identity value from the `idents` table.
    #[inline]
    pub fn unwrap<I: AsRef<[VRef]>, VRef: std::borrow::Borrow<V>>(self, idents: I) -> V
        where V: Clone
    {
        match self {
            Self::Element(v) => v,
            Self::Identity(mask) => {
                let idents = idents.as_ref();
                idents[mask.trailing_zeros() as usize].borrow().clone()
            },
        }
    }
    /// Returns the contained `Element` value or obtains the identified argument from `ident_f`.
    #[inline]
    pub fn unwrap_or_else<IdentF>(self, ident_f: IdentF) -> V
        where
        IdentF: FnOnce(usize) -> V,
    {
        match self {
            Self::Element(v) => v,
            Self::Identity(mask) => ident_f(mask.trailing_zeros() as usize),
        }
    }
    /// Returns the contained `Element` value or one of the provided identity values.
    #[inline]
    pub fn unwrap_or<I: AsRef<[VRef]>, VRef: std::borrow::Borrow<V>>(self, idents: I) -> V
        where V: Clone
    {
        match self {
            Self::Element(v) => v,
            Self::Identity(mask) => {
                let idents = idents.as_ref();
                idents[mask.trailing_zeros() as usize].borrow().clone()
            },
        }
    }
    /// Merges two `AlgebraicResult`s into a combined `AlgebraicResult<U>`.  This method is useful to compose a
    /// result for an operation on whole type arguments, from the results of separate operations on each field
    /// of the arguments.
    ///
    /// NOTE: Take care when implementing the `meet` operation across heterogeneous items (e.g. abstracted sets),
    /// because one set may be a superset of the other.  simply merging the `AlgebraicResult`s from individual
    /// `meet` operations on the overlapping elements will lead to a false `Identity` result for one of the sets.
    ///
    /// ```
    /// use pathmap::ring::{Lattice, AlgebraicResult};
    /// 
    /// struct Composed {
    ///     field0: bool,
    ///     field1: bool,
    /// }
    ///
    /// fn pjoin(a: &Composed, b: &Composed) -> AlgebraicResult<Composed> {
    ///     let result0 = a.field0.pjoin(&b.field0);
    ///     let result1 = a.field1.pjoin(&b.field1);
    ///     result0.merge(result1, |which_arg| {
    ///         match which_arg {
    ///             0 => Some(a.field0),
    ///             1 => Some(b.field0),
    ///             _ => unreachable!()
    ///         }
    ///     }, |which_arg| {
    ///         match which_arg {
    ///             0 => Some(a.field1),
    ///             1 => Some(b.field1),
    ///             _ => unreachable!()
    ///         }
    ///     }, |field0, field1| {
    ///         AlgebraicResult::Element(Composed{
    ///             field0: field0.unwrap(),
    ///             field1: field1.unwrap()
    ///         })
    ///     })
    /// }
    /// ```
    #[inline]
    pub fn merge<BV, U, MergeF, AIdent, BIdent>(self, b: AlgebraicResult<BV>, self_idents: AIdent, b_idents: BIdent, merge_f: MergeF) -> AlgebraicResult<U>
        where
        MergeF: FnOnce(Option<V>, Option<BV>) -> AlgebraicResult<U>,
        AIdent: FnOnce(usize) -> Option<V>,
        BIdent: FnOnce(usize) -> Option<BV>,
    {
        match self {
            Self::Identity(self_mask) => {
                match b {
                    AlgebraicResult::Element(b_v) => {
                        let self_v = self_idents(self_mask.trailing_zeros() as usize);
                        merge_f(self_v, Some(b_v))
                    },
                    AlgebraicResult::Identity(b_mask) => {
                        let combined_mask = self_mask & b_mask;
                        if combined_mask > 0 {
                            AlgebraicResult::Identity(combined_mask)
                        } else {
                            let self_v = self_idents(self_mask.trailing_zeros() as usize);
                            let b_v = b_idents(b_mask.trailing_zeros() as usize);
                            merge_f(self_v, b_v)
                        }
                    }
                }
            },
            Self::Element(self_v) => {
                match b {
                    AlgebraicResult::Element(b_v) => merge_f(Some(self_v), Some(b_v)),
                    AlgebraicResult::Identity(b_mask) => {
                        let b_v = b_idents(b_mask.trailing_zeros() as usize);
                        merge_f(Some(self_v), b_v)
                    }
                }
            }
        }
    }
    /// Creates a new `AlgebraicResult` from an [AlgebraicStatus], and a method to create the element value
    #[inline]
    pub fn from_status<F>(status: AlgebraicStatus, element_f: F) -> Self
        where F: FnOnce() -> V
    {
        match status {
            AlgebraicStatus::Identity => Self::Identity(SELF_IDENT),
            AlgebraicStatus::Element => Self::Element(element_f())
        }
    }
    /// Returns an [AlgebraicStatus] associated with the `AlgebraicResult`
    #[inline]
    pub fn status(&self) -> AlgebraicStatus {
        match self {
            AlgebraicResult::Element(_) => AlgebraicStatus::Element,
            AlgebraicResult::Identity(mask) => {
                if mask & SELF_IDENT > 0 {
                    AlgebraicStatus::Identity
                } else {
                    AlgebraicStatus::Element
                }
            }
        }
    }
}

/// Merges results from two independently optional parts of a compound value.
///
/// This is the partial-operation counterpart to [`AlgebraicResult::merge`] and
/// is useful when implementing `pmeet` or `psubtract` for a struct with
/// multiple independently-computed fields. The identity callbacks materialize
/// a field from the indicated whole-operation argument when that field's result
/// is an identity.
#[inline]
pub fn merge_optional_results<AV, BV, U, MergeF, AIdent, BIdent>(
    a: Option<AlgebraicResult<AV>>,
    b: Option<AlgebraicResult<BV>>,
    a_idents: AIdent,
    b_idents: BIdent,
    merge_f: MergeF,
) -> Option<AlgebraicResult<U>>
where
    MergeF: FnOnce(Option<AV>, Option<BV>) -> AlgebraicResult<U>,
    AIdent: FnOnce(usize) -> Option<AV>,
    BIdent: FnOnce(usize) -> Option<BV>,
{
    match a {
        None => match b {
            None => None,
            Some(AlgebraicResult::Element(b_v)) => Some(merge_f(None, Some(b_v))),
            Some(AlgebraicResult::Identity(b_mask)) => {
                if a_idents(0).is_none() {
                    Some(AlgebraicResult::Identity(b_mask))
                } else {
                    Some(merge_f(None, b_idents(b_mask.trailing_zeros() as usize)))
                }
            }
        },
        Some(AlgebraicResult::Identity(a_mask)) => match b {
            None => {
                if b_idents(0).is_none() {
                    Some(AlgebraicResult::Identity(a_mask))
                } else {
                    Some(merge_f(a_idents(a_mask.trailing_zeros() as usize), None))
                }
            }
            Some(AlgebraicResult::Element(b_v)) => {
                Some(merge_f(a_idents(a_mask.trailing_zeros() as usize), Some(b_v)))
            }
            Some(AlgebraicResult::Identity(b_mask)) => {
                let combined_mask = a_mask & b_mask;
                if combined_mask > 0 {
                    Some(AlgebraicResult::Identity(combined_mask))
                } else {
                    Some(merge_f(
                        a_idents(a_mask.trailing_zeros() as usize),
                        b_idents(b_mask.trailing_zeros() as usize),
                    ))
                }
            }
        },
        Some(AlgebraicResult::Element(a_v)) => match b {
            None => Some(merge_f(Some(a_v), None)),
            Some(AlgebraicResult::Element(b_v)) => Some(merge_f(Some(a_v), Some(b_v))),
            Some(AlgebraicResult::Identity(b_mask)) => {
                Some(merge_f(Some(a_v), b_idents(b_mask.trailing_zeros() as usize)))
            }
        },
    }
}

impl<V> AlgebraicResult<Option<V>> {
    /// Moves optionality outside the algebraic result. `Element(None)` becomes
    /// `None`; identity results remain present because their value must be
    /// obtained from the identified argument.
    #[inline]
    pub fn flatten(self) -> Option<AlgebraicResult<V>> {
        match self {
            Self::Element(v) => {
                match v {
                    Some(v) => Some(AlgebraicResult::Element(v)),
                    None => None
                }
            },
            Self::Identity(mask) => Some(AlgebraicResult::Identity(mask)),
        }
    }
}

/// Status result that is returned from an in-place algebraic operation (a method that takes `&mut self`)
///
/// NOTE: `AlgebraicStatus` values are ordered, with `Element` lower than `Identity`.
/// Higher values make stronger guarantees about the results of the operation, but lower values
/// are still correct and your code must behave appropriately.
///
/// In general, `AlgebraicStatus` return values are a valid signal for loop termination, but should not be
/// strictly relied upon for other kinds of branching.  For example, `Element` might be returned by
/// [ZipperWriting::join](crate::zipper::ZipperWriting::join) instead of `Identity` if the internal representation was changed by the method,
/// however the next call to `join` ought to return `Identity` if nothing new is added.
///
/// Operations that may remove the result entirely return
/// `Option<AlgebraicStatus>`; absence is not an `AlgebraicStatus`.
#[derive(Clone, Copy, Default, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum AlgebraicStatus {
    /// A result indicating `self` contains the operation's output
    #[default]
    Element,
    /// A result indicating `self` was unmodified by the operation
    Identity,
}

impl AlgebraicStatus {
    /// Returns `true` if the status is [AlgebraicStatus::Identity], otherwise returns `false`
    #[inline]
    pub fn is_identity(&self) -> bool {
        matches!(self, Self::Identity)
    }
    /// Returns `true` if the status is [AlgebraicStatus::Element], otherwise returns `false`
    #[inline]
    pub fn is_element(&self) -> bool {
        matches!(self, Self::Element)
    }
    /// Merges two `AlgebraicStatus` values into one.  Useful when composing the status from operations on individual fields
    ///
    /// See [AlgebraicResult::merge].
    #[inline]
    pub fn merge(self, b: Self) -> AlgebraicStatus {
        match self {
            Self::Identity => match b {
                Self::Element => Self::Element,
                Self::Identity => Self::Identity,
            },
            Self::Element => Self::Element
        }
    }
}

/// Combines statuses from two independently optional parts of a compound value.
#[inline]
pub(crate) fn merge_optional_statuses(
    a: Option<AlgebraicStatus>,
    b: Option<AlgebraicStatus>,
    a_was_none: bool,
    b_was_none: bool,
) -> Option<AlgebraicStatus> {
    match a {
        None => match b {
            None => None,
            Some(AlgebraicStatus::Element) => Some(AlgebraicStatus::Element),
            Some(AlgebraicStatus::Identity) => Some(if a_was_none {
                AlgebraicStatus::Identity
            } else {
                AlgebraicStatus::Element
            }),
        },
        Some(AlgebraicStatus::Identity) => match b {
            Some(AlgebraicStatus::Element) => Some(AlgebraicStatus::Element),
            Some(AlgebraicStatus::Identity) => Some(AlgebraicStatus::Identity),
            None => Some(if b_was_none {
                AlgebraicStatus::Identity
            } else {
                AlgebraicStatus::Element
            }),
        },
        Some(AlgebraicStatus::Element) => Some(AlgebraicStatus::Element),
    }
}

impl<V> From<FatAlgebraicResult<V>> for Option<AlgebraicResult<V>> {
    #[inline]
    fn from(src: FatAlgebraicResult<V>) -> Self {
        if src.identity_mask > 0 {
            Some(AlgebraicResult::Identity(src.identity_mask))
        } else {
            match src.element {
                Some(element) => Some(AlgebraicResult::Element(element)),
                None => None
            }
        }
    }
}

/// Internal result type that can be down-converted to an
/// `Option<AlgebraicResult<_>>`, but carries additional information.
#[derive(Clone, Copy, Default, Debug, PartialEq, Eq)]
pub(crate) struct FatAlgebraicResult<V> {
    /// An identity mask that maps to the [AlgebraicResult::Identity] value, or 0 if the result is not an identity
    pub identity_mask: u64,
    /// Carries the element value, irrespective of the identity information.  It is the discretion of the code using
    /// this struct as to whether or not to populate this field in the case of an identity result
    pub element: Option<V>,
}

impl<V> FatAlgebraicResult<V> {
    #[inline(always)]
    pub(crate) const fn new(identity_mask: u64, element: Option<V>) -> Self {
        Self {identity_mask, element}
    }
    /// Converts an [AlgebraicResult] into a `FatAlgebraicResult`, assuming the source `result` was the
    /// output of a binary operation (two arguments).
    #[inline]
    pub(crate) fn from_binary_op_result(result: Option<AlgebraicResult<V>>, a: &V, b: &V) -> Self
        where V: Clone
    {
        match result {
            None => FatAlgebraicResult::none(),
            Some(AlgebraicResult::Element(v)) => FatAlgebraicResult::element(v),
            Some(AlgebraicResult::Identity(mask)) => {
                debug_assert!(mask <= (SELF_IDENT | COUNTER_IDENT));
                if mask & SELF_IDENT > 0 {
                    FatAlgebraicResult::new(mask, Some(a.clone()))
                } else {
                    debug_assert_eq!(mask, COUNTER_IDENT);
                    FatAlgebraicResult::new(mask, Some(b.clone()))
                }
            }
        }
    }
    /// Maps a `FatAlgebraicResult<V>` to `FatAlgebraicResult<U>` by applying a function to a contained value
    #[inline]
    pub fn map<U, F>(self, f: F) -> FatAlgebraicResult<U>
        where F: FnOnce(V) -> U,
    {
        FatAlgebraicResult::<U> {
            identity_mask: self.identity_mask,
            element: self.element.map(f)
        }
    }
    /// The result of an operation between non-none arguments that results in None
    #[inline(always)]
    pub(crate) const fn none() -> Self {
        Self {identity_mask: 0, element: None}
    }
    /// The result of an operation that generated a brand new result
    #[inline(always)]
    pub(crate) fn element(e: V) -> Self {
        Self {identity_mask: 0, element: Some(e)}
    }
    //GOAT, currently unused although implemented and working
    // /// Merges two `FatAlgebraicResult<V>`s into an `AlgebraicResult<U>`.  See [AlgebraicResult::merge]
    // #[inline]
    // pub fn merge_and_convert<U, F>(self, other: Self, merge_f: F) -> AlgebraicResult<U>
    //     where F: FnOnce(Option<V>, Option<V>) -> AlgebraicResult<U>,
    // {
    //     if self.element.is_none() && other.element.is_none() {
    //         return None
    //     }
    //     let combined_mask = self.identity_mask & other.identity_mask;
    //     if combined_mask > 0 {
    //         return AlgebraicResult::Identity(combined_mask)
    //     }
    //     merge_f(self.element, other.element)
    // }
    //GOAT, currently unused, but fully implemented and working
    // /// Intersects arg with the contents of self, and sets the arg_idx bit in the case of an identity result
    // pub fn meet(self, arg: &V, arg_idx: usize) -> Self where V: Lattice + Clone {
    //     match self.element {
    //         None => {
    //             debug_assert_eq!(self.identity_mask, 0);
    //             Self::new(self.identity_mask, None)
    //         },
    //         Some(self_element) => match self_element.pmeet(arg) {
    //             None => Self::none(),
    //             AlgebraicResult::Element(e) => Self::element(e),
    //             AlgebraicResult::Identity(mask) => {
    //                 if mask & SELF_IDENT > 0 {
    //                     let new_mask = self.identity_mask | ((mask & COUNTER_IDENT) << (arg_idx-1));
    //                     Self::new(new_mask, Some(self_element))
    //                 } else {
    //                     debug_assert!(mask & COUNTER_IDENT > 0);
    //                     let new_mask = (mask & COUNTER_IDENT) << (arg_idx-1);
    //                     Self::new(new_mask, Some(arg.clone()))
    //                 }
    //             }
    //         }
    //     }
    // }
    /// Unions arg with the contents of self, and sets the arg_idx bit in the case of an identity result
    pub fn join(self, arg: &V, arg_idx: usize) -> Self where V: Lattice + Clone {
        match self.element {
            None => {
                Self::new(self.identity_mask | 1 << arg_idx, Some(arg.clone()))
            },
            Some(self_element) => match self_element.pjoin(&arg) {
                AlgebraicResult::Element(e) => Self::element(e),
                AlgebraicResult::Identity(mask) => {
                    if mask & SELF_IDENT > 0 {
                        let new_mask = self.identity_mask | ((mask & COUNTER_IDENT) << (arg_idx-1));
                        Self::new(new_mask, Some(self_element))
                    } else {
                        debug_assert!(mask & COUNTER_IDENT > 0);
                        let new_mask = (mask & COUNTER_IDENT) << (arg_idx-1);
                        Self::new(new_mask, Some(arg.clone()))
                    }
                }
            }
        }
    }
}

/// Implements basic algebraic behavior (union & intersection) for a type
pub trait Lattice {
    /// Indicates whether the lattice operations are idempotent for the purpose of
    /// evaluating algebraic operations on shared subtries.
    ///
    /// If `IDEMPOTENT = true` the implementor is asserting that:
    /// `pjoin(self) -> AlgebraicResult::Identity(SELF_IDENT | COUNTER_IDENT)`,
    /// `join_into(self) -> AlgebraicStatus::Identity`,
    /// `pmeet(self) -> Some(AlgebraicResult::Identity(SELF_IDENT | COUNTER_IDENT))`,
    ///
    /// WARNING! This constant is currently informational only.  The node-level and zipper
    /// algebra implementations do not yet consult it, so changing it has no effect
    /// on their behavior.  It is planned for gating implementation shortcuts in the future
    const IDEMPOTENT: bool = true;

    /// Computes the join (least upper bound) of two elements.
    ///
    /// This operation is total. An implementation whose join can fall outside
    /// its represented carrier must instead lift that carrier into a type that
    /// can represent the result (for example, `Option<T>`).
    fn pjoin(&self, other: &Self) -> AlgebraicResult<Self> where Self: Sized;

    /// Implements the union operation between two instances of a type, consuming the `other` input operand,
    /// and modifying `self` to become the joined type
    ///
    fn join_into(&mut self, other: Self) -> AlgebraicStatus where Self: Sized {
        let result = self.pjoin(&other);
        in_place_default_impl(result, self, other, |e| e)
    }

    /// Computes the meet (greatest lower bound) of two elements.
    ///
    /// Returns `None` when the operands annihilate and no element remains.
    /// Otherwise, the inner result describes whether the output is identical
    /// to an operand or newly constructed. Thus optionality describes whether
    /// a result exists, while `AlgebraicResult` describes how an existing result
    /// relates to its inputs.
    fn pmeet(&self, other: &Self) -> Option<AlgebraicResult<Self>> where Self: Sized;

    //GOAT, we want a meet_into, that has the same semantics as join_into, e.g. mutating in-place.  I
    // don't think there is any benefit to consuming `other`, however, so we can still take `other: &Self`

    /// Joins every element in `xs`.
    ///
    /// The outer `None` means that `xs` itself was empty; individual joins are
    /// total and always produce an `AlgebraicResult`.
    //GOAT, this should be temporarily deprecated until we work out the correct function prototype
    fn join_all<S: AsRef<Self>, Args: AsRef<[S]>>(xs: Args) -> Option<AlgebraicResult<Self>> where Self: Sized + Clone {
        let mut iter = xs.as_ref().into_iter().enumerate();
        let mut result = match iter.next() {
            None => return None,
            Some((_, first)) => FatAlgebraicResult::new(SELF_IDENT, Some(first.as_ref().clone())),
        };
        for (i, next) in iter {
            result = result.join(next.as_ref(), i);
        }
        result.into()
    }
}

/// Internal function to implement the default behavior of `join_into`, `meet_into`, etc. in terms of `pjoin`, `pmeet`, etc.
fn in_place_default_impl<SelfT, OtherT, ConvertF>(result: AlgebraicResult<SelfT>, self_ref: &mut SelfT, other: OtherT, convert_f: ConvertF) -> AlgebraicStatus
    where
    ConvertF: Fn(OtherT) -> SelfT
{
    match result {
        AlgebraicResult::Element(v) => {
            *self_ref = v;
            AlgebraicStatus::Element
        },
        AlgebraicResult::Identity(mask) => {
            if mask & SELF_IDENT > 0 {
                AlgebraicStatus::Identity
            } else {
                *self_ref = convert_f(other);
                AlgebraicStatus::Element
            }
        },
    }
}

/// Implements algebraic behavior on a reference to a [Lattice] type, such as a smart pointer that can't
/// hold ownership
pub trait LatticeRef {
    type T;
    fn pjoin(&self, other: &Self) -> AlgebraicResult<Self::T>;
    /// Computes the meet of the referenced values, returning `None` when no
    /// result element remains.
    fn pmeet(&self, other: &Self) -> Option<AlgebraicResult<Self::T>>;
}

/// Implements subtract behavior for a type
pub trait DistributiveLattice {
    /// Indicates whether the subtraction operation is idempotent for the purpose of
    /// evaluating algebraic operations on shared subtries.
    ///
    /// If `IDEMPOTENT = true` the implementor is asserting that:
    /// `psubtract(self) -> None`,
    ///
    /// WARNING! This constant is currently informational only.  The node-level and zipper
    /// algebra implementations do not yet consult it, so changing it has no effect
    /// on their behavior.  It is planned for gating implementation shortcuts in the future
    const IDEMPOTENT: bool = true;

    /// Subtracts `other` from `self`.
    ///
    /// Returns `None` when subtraction completely annihilates `self`.
    /// Otherwise, the inner result describes the remaining element and how it
    /// relates to the input. This keeps absence orthogonal to the
    /// identity-versus-new-element distinction.
    fn psubtract(&self, other: &Self) -> Option<AlgebraicResult<Self>> where Self: Sized;

    //GOAT, We want a psubtract_from (subtract_into??) that operates on a `&mut self`
}

/// Implements subtract behavior on a reference to a [DistributiveLattice] type
pub trait DistributiveLatticeRef {
    /// The type that is referenced
    type T;

    /// Subtracts the referenced `other` value from `self`, returning `None`
    /// when no result element remains.
    fn psubtract(&self, other: &Self) -> Option<AlgebraicResult<Self::T>>;
}

// =-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-=
// Private traits
// =-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-=

/// Used to implement restrict operation.  TODO, come up with a better math-explanation about how this
/// is a quantale
///
/// Currently this trait isn't exposed because it's unclear what we degrees of felxibility really want
/// from restrict, and what performance we are willing to trade to get them
pub(crate) trait Quantale {
    /// TODO: Document this (currently internal-only)
    fn prestrict(&self, other: &Self) -> Option<AlgebraicResult<Self>> where Self: Sized;
}

/// An internal mirror of the [Lattice] trait, where the `self` and `other` types don't need to be
/// exactly the same type, in order to permit blanket implementations
pub(crate) trait HeteroLattice<OtherT> {
    fn pjoin(&self, other: &OtherT) -> AlgebraicResult<Self> where Self: Sized;
    fn join_into(&mut self, other: OtherT) -> AlgebraicStatus where Self: Sized {
        let result = self.pjoin(&other);
        in_place_default_impl(result, self, other, |e| Self::convert(e))
    }
    fn pmeet(&self, other: &OtherT) -> Option<AlgebraicResult<Self>> where Self: Sized;
    // fn join_all(xs: &[&Self]) -> Self where Self: Sized; //HeteroLattice will entirely disappear with the policy refactor, so it's not worth worying about this anymore
    fn convert(other: OtherT) -> Self;
}

/// An internal mirror of the [DistributiveLattice] trait, where the `self` and `other` types
/// don't need to be exactly the same type, to facilitate blanket impls
pub(crate) trait HeteroDistributiveLattice<OtherT> {
    fn psubtract(&self, other: &OtherT) -> Option<AlgebraicResult<Self>> where Self: Sized;
}

/// Internal mirror for [Quantale] See discussion on [HeteroLattice].
pub(crate) trait HeteroQuantale<OtherT> {
    fn prestrict(&self, other: &OtherT) -> Option<AlgebraicResult<Self>> where Self: Sized;
}

// =-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-=
// impls on primitive & std types
// =-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-=

// =-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-=
// =-*   `Option<V>`                                                                                  *-=

impl<V: Lattice + Clone> Lattice for Option<V> {
    fn pjoin(&self, other: &Option<V>) -> AlgebraicResult<Self> {
        match self {
            None => match other {
                None => { AlgebraicResult::Identity(SELF_IDENT | COUNTER_IDENT) }
                Some(_) => { AlgebraicResult::Identity(COUNTER_IDENT) }
            },
            Some(l) => match other {
                None => { AlgebraicResult::Identity(SELF_IDENT) }
                Some(r) => l.pjoin(r).map(Some)
            }
        }
    }
    fn join_into(&mut self, other: Self) -> AlgebraicStatus {
        match self {
            None => { match other {
                None => AlgebraicStatus::Identity,
                Some(r) => {
                    *self = Some(r);
                    AlgebraicStatus::Element
                }
            } }
            Some(l) => match other {
                None => AlgebraicStatus::Identity,
                Some(r) => l.join_into(r)
            }
        }
    }
    fn pmeet(&self, other: &Option<V>) -> Option<AlgebraicResult<Option<V>>> {
        match self {
            None => None,
            Some(l) => {
                match other {
                    None => None,
                    Some(r) => l.pmeet(r).map(|result| result.map(Some))
                }
            }
        }
    }
}

impl<V: DistributiveLattice + Clone> DistributiveLattice for Option<V> {
    fn psubtract(&self, other: &Self) -> Option<AlgebraicResult<Self>> {
        match self {
            None => None,
            Some(s) => {
                match other {
                    None => Some(AlgebraicResult::Identity(SELF_IDENT)),
                    Some(o) => s.psubtract(o).map(|result| result.map(Some))
                }
            }
        }
    }
}

#[test]
fn option_join_test() {
    assert_eq!(None::<()>.pjoin(&None), AlgebraicResult::Identity(SELF_IDENT | COUNTER_IDENT));

    let mut value = None::<()>;
    assert_eq!(value.join_into(None), AlgebraicStatus::Identity);
    assert_eq!(value, None);
}

#[test]
fn option_subtract_test() {
    assert_eq!(Some(()).psubtract(&Some(())), None);
    assert_eq!(Some(()).psubtract(&None), Some(AlgebraicResult::Identity(SELF_IDENT)));
    assert_eq!(Some(Some(())).psubtract(&Some(Some(()))), None);
    assert_eq!(Some(Some(())).psubtract(&None), Some(AlgebraicResult::Identity(SELF_IDENT)));
    assert_eq!(Some(Some(())).psubtract(&Some(None)), Some(AlgebraicResult::Identity(SELF_IDENT)));
    assert_eq!(Some(Some(Some(()))).psubtract(&Some(Some(None))), Some(AlgebraicResult::Identity(SELF_IDENT)));
    assert_eq!(Some(Some(Some(()))).psubtract(&Some(Some(Some(())))), None);
}

// =-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-=
// =-*   `Option<&V>`                                                                                 *-=

impl<V: Lattice + Clone> LatticeRef for Option<&V> {
    type T = Option<V>;
    fn pjoin(&self, other: &Self) -> AlgebraicResult<Self::T> {
        match self {
            None => { match other {
                None => { AlgebraicResult::Identity(SELF_IDENT | COUNTER_IDENT) }
                Some(_) => { AlgebraicResult::Identity(COUNTER_IDENT) }
            } }
            Some(l) => match other {
                None => { AlgebraicResult::Identity(SELF_IDENT) }
                Some(r) => { l.pjoin(r).map(|result| Some(result)) }
            }
        }
    }
    fn pmeet(&self, other: &Option<&V>) -> Option<AlgebraicResult<Option<V>>> {
        match self {
            None => None,
            Some(l) => {
                match other {
                    None => None,
                    Some(r) => l.pmeet(r).map(|result| result.map(Some))
                }
            }
        }
    }
}

impl<V: DistributiveLattice + Clone> DistributiveLatticeRef for Option<&V> {
    type T = Option<V>;
    fn psubtract(&self, other: &Self) -> Option<AlgebraicResult<Self::T>> {
        match self {
            None => None,
            Some(s) => {
                match other {
                    None => Some(AlgebraicResult::Identity(SELF_IDENT)),
                    Some(o) => s.psubtract(o).map(|result| result.map(Some))
                }
            }
        }
    }
}

// =-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-=
// =-*   `Box<V>`                                                                                     *-=

impl <V: Lattice> Lattice for Box<V> {
    fn pjoin(&self, other: &Self) -> AlgebraicResult<Self> {
        self.as_ref().pjoin(other.as_ref()).map(|result| Box::new(result))
    }
    fn pmeet(&self, other: &Self) -> Option<AlgebraicResult<Self>> {
        self.as_ref().pmeet(other.as_ref()).map(|result| result.map(Box::new))
    }
}

impl<V: DistributiveLattice> DistributiveLattice for Box<V> {
    fn psubtract(&self, other: &Self) -> Option<AlgebraicResult<Self>> {
        self.as_ref().psubtract(other.as_ref()).map(|result| result.map(Box::new))
    }
}

// =-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-=
// =-*   `&V`                                                                                         *-=

impl <V: Lattice> LatticeRef for &V {
    type T = V;
    fn pjoin(&self, other: &Self) -> AlgebraicResult<Self::T> {
        (**self).pjoin(other)
    }
    fn pmeet(&self, other: &Self) -> Option<AlgebraicResult<Self::T>> {
        (**self).pmeet(other)
    }
}

impl<V: DistributiveLattice> DistributiveLatticeRef for &V {
    type T = V;
    fn psubtract(&self, other: &Self) -> Option<AlgebraicResult<Self::T>> {
        (**self).psubtract(other)
    }
}

// =-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-=
// =-*  `()`, aka unit                                                                                *-=

impl DistributiveLattice for () {
    fn psubtract(&self, _other: &Self) -> Option<AlgebraicResult<Self>> where Self: Sized {
        None
    }
}

impl Lattice for () {
    fn pjoin(&self, _other: &Self) -> AlgebraicResult<Self> { AlgebraicResult::Identity(SELF_IDENT | COUNTER_IDENT) }
    fn pmeet(&self, _other: &Self) -> Option<AlgebraicResult<Self>> { Some(AlgebraicResult::Identity(SELF_IDENT | COUNTER_IDENT)) }
}

//GOAT trash
impl Lattice for usize {
    fn pjoin(&self, _other: &usize) -> AlgebraicResult<usize> { AlgebraicResult::Identity(SELF_IDENT) }
    fn pmeet(&self, _other: &usize) -> Option<AlgebraicResult<usize>> { Some(AlgebraicResult::Identity(SELF_IDENT)) }
}

//GOAT trash
impl Lattice for u64 {
    fn pjoin(&self, _other: &u64) -> AlgebraicResult<u64> { AlgebraicResult::Identity(SELF_IDENT) }
    fn pmeet(&self, _other: &u64) -> Option<AlgebraicResult<u64>> { Some(AlgebraicResult::Identity(SELF_IDENT)) }
}

//GOAT trash
impl DistributiveLattice for u64 {
    fn psubtract(&self, other: &Self) -> Option<AlgebraicResult<Self>> where Self: Sized {
        if self == other { None }
        else { Some(AlgebraicResult::Element(*self)) }
    }
}

//GOAT trash
impl Lattice for u32 {
    fn pjoin(&self, _other: &u32) -> AlgebraicResult<u32> { AlgebraicResult::Identity(SELF_IDENT) }
    fn pmeet(&self, _other: &u32) -> Option<AlgebraicResult<u32>> { Some(AlgebraicResult::Identity(SELF_IDENT)) }
}

//GOAT trash
impl Lattice for u16 {
    fn pjoin(&self, _other: &u16) -> AlgebraicResult<u16> { AlgebraicResult::Identity(SELF_IDENT) }
    fn pmeet(&self, _other: &u16) -> Option<AlgebraicResult<u16>> { Some(AlgebraicResult::Identity(SELF_IDENT)) }
}

//GOAT trash
impl DistributiveLattice for u16 {
    fn psubtract(&self, other: &Self) -> Option<AlgebraicResult<Self>> {
        if self == other { None }
        else { Some(AlgebraicResult::Element(*self)) }
    }
}

//GOAT trash
impl Lattice for u8 {
    fn pjoin(&self, _other: &u8) -> AlgebraicResult<u8> { AlgebraicResult::Identity(SELF_IDENT) }
    fn pmeet(&self, _other: &u8) -> Option<AlgebraicResult<u8>> { Some(AlgebraicResult::Identity(SELF_IDENT)) }
}

// =-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-=
// =-*   `bool`                                                                                       *-=
// NOTE: There is a default impl for `bool` and not for other primitives because there are fewer states,
// and therefore fewer meanings for a `bool`.

impl DistributiveLattice for bool {
    fn psubtract(&self, other: &bool) -> Option<AlgebraicResult<Self>> {
        if *self == *other {
            None
        } else {
            Some(AlgebraicResult::Identity(SELF_IDENT))
        }
    }
}

impl Lattice for bool {
    fn pjoin(&self, other: &bool) -> AlgebraicResult<bool> {
        if !*self && *other {
            AlgebraicResult::Identity(COUNTER_IDENT) //result is true
        } else {
            AlgebraicResult::Identity(SELF_IDENT)
        }
    }
    fn pmeet(&self, other: &bool) -> Option<AlgebraicResult<bool>> {
        if *self && !*other {
            Some(AlgebraicResult::Identity(COUNTER_IDENT)) //result is false
        } else {
            Some(AlgebraicResult::Identity(SELF_IDENT))
        }
    }
}

// =-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-=
// =-*   `SetLattice<K>`, including `HashMap<K, V>`, `HashSet<K>`, etc.                               *-=

/// Implemented on an unordered set type, (e.g. [HashMap], [HashSet], etc.) to get automatic implementations
/// of the [Lattice] and [DistributiveLattice] traits on the set type with the [set_lattice](crate::set_lattice) and
/// [set_dist_lattice](crate::set_dist_lattice) macros
///
/// BEWARE: The `Lattice` and `DistributiveLattice` impls that are derived from the `SetLattice` impl treat
/// an empty set as equivalent to a nonexistent set.  Therefore, if your arguments contain empty sets, those
/// sets may or may not be collapsed.  Your code must be aware of this.
pub trait SetLattice {
    /// A key type that uniquely identifies an element within the set
    type K: Clone + Eq;

    /// A payload value type that can be associated with a key in the set
    type V: Clone;

    /// An [Iterator] type over the contents of the set
    type Iter<'a>: Iterator<Item=(&'a Self::K, &'a Self::V)> where Self: 'a, Self::V: 'a, Self::K: 'a;

    /// Returns a new empty set with the specified capacity preallocated
    fn with_capacity(capacity: usize) -> Self;

    /// Returns the number of items in the set
    fn len(&self) -> usize;

    /// Returns `true` is the set is empty (`len() == 0`), otherwise returns `false`
    fn is_empty(&self) -> bool;

    /// Returns `true` if the set contains the key, otherwise `false`
    fn contains_key(&self, key: &Self::K) -> bool;

    /// Inserts a new (key, value) pair, replacing the item at `key` if it already existed
    fn insert(&mut self, key: Self::K, val: Self::V);

    /// Removes the element at `key` from the set
    fn remove(&mut self, key: &Self::K);

    /// Returns a reference to the element in the set, or None if the element is not contained within the set
    fn get(&self, key: &Self::K) -> Option<&Self::V>;

    /// Replaces the element at `key` with the new value `val`.  Will never be called for a non-existent key
    fn replace(&mut self, key: &Self::K, val: Self::V);

    /// Return a `Self::Iter` in order to iterate the set
    fn iter<'a>(&'a self) -> Self::Iter<'a>;

    /// An opportunity to free unused space in the set container, if appropriate
    fn shrink_to_fit(&mut self);
}

/// A macro to emit the [Lattice] implementation for a type that implements [SetLattice]
#[macro_export]
macro_rules! set_lattice {
    ( $type_ident:ident $(< $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ >)? ) => {
        impl $(< $( $lt $( : $clt $(+ $dlt )* )? ),+ >)? $crate::ring::Lattice for $type_ident $(< $( $lt ),+ >)? where Self: $crate::ring::SetLattice, <Self as $crate::ring::SetLattice>::V: $crate::ring::Lattice {
            fn pjoin(&self, other: &Self) -> $crate::ring::AlgebraicResult<Self> {
                let self_len = $crate::ring::SetLattice::len(self);
                let other_len = $crate::ring::SetLattice::len(other);
                let mut result = <Self as $crate::ring::SetLattice>::with_capacity(self_len.max(other_len));
                let mut is_ident = self_len >= other_len;
                let mut is_counter_ident = self_len <= other_len;
                for (key, self_val) in $crate::ring::SetLattice::iter(self) {
                    if let Some(other_val) = $crate::ring::SetLattice::get(other, key) {
                        // A key in both sets
                        let inner_result = self_val.pjoin(other_val);
                        $crate::ring::set_lattice_update_ident_flags_with_result(
                            &mut result, inner_result, key, self_val, other_val, &mut is_ident, &mut is_counter_ident
                        );
                    } else {
                        // A key in self, but not in other
                        $crate::ring::SetLattice::insert(&mut result, key.clone(), self_val.clone());
                        is_counter_ident = false;
                    }
                }
                for (key, value) in SetLattice::iter(other) {
                    if !$crate::ring::SetLattice::contains_key(self, key) {
                        // A key in other, but not in self
                        $crate::ring::SetLattice::insert(&mut result, key.clone(), value.clone());
                        is_ident = false;
                    }
                }
                $crate::ring::set_lattice_integrate_into_result(result, is_ident, is_counter_ident, self_len, other_len)
            }
            fn pmeet(&self, other: &Self) -> Option<$crate::ring::AlgebraicResult<Self>> {
                let mut result = <Self as $crate::ring::SetLattice>::with_capacity(0);
                let mut is_ident = true;
                let mut is_counter_ident = true;
                let (smaller, larger, switch) = if $crate::ring::SetLattice::len(self) < $crate::ring::SetLattice::len(other) {
                    (self, other, false)
                } else {
                    (other, self, true)
                };
                for (key, self_val) in $crate::ring::SetLattice::iter(smaller) {
                    if let Some(other_val) = $crate::ring::SetLattice::get(larger, key) {
                        let inner_result = self_val.pmeet(other_val);
                        $crate::ring::set_lattice_update_ident_flags_with_result(
                            &mut result, inner_result, key, self_val, other_val, &mut is_ident, &mut is_counter_ident
                        );
                    } else {
                        is_ident = false;
                    }
                }
                if switch {
                    core::mem::swap(&mut is_ident, &mut is_counter_ident);
                }
                if $crate::ring::SetLattice::is_empty(&result) {
                    None
                } else {
                    Some($crate::ring::set_lattice_integrate_into_result(result, is_ident, is_counter_ident, self.len(), other.len()))
                }
            }
        }
    }
}

/// Internal function to integrate an `AlgebraicResult` from an element in a set into the set's own overall result
#[inline]
#[doc(hidden)]
pub fn set_lattice_update_ident_flags_with_result<S: SetLattice, R: Into<Option<AlgebraicResult<S::V>>>>(
    result_set: &mut S,
    result: R,
    key: &S::K,
    self_val: &S::V,
    other_val: &S::V,
    is_ident: &mut bool,
    is_counter_ident: &mut bool
) {
    match result.into() {
        None => {
            *is_ident = false;
            *is_counter_ident = false;
        },
        Some(AlgebraicResult::Element(new_val)) => {
            *is_ident = false;
            *is_counter_ident = false;
            result_set.insert(key.clone(), new_val);
        },
        Some(AlgebraicResult::Identity(mask)) => {
            if mask & SELF_IDENT > 0 {
                result_set.insert(key.clone(), self_val.clone());
            } else {
                *is_ident = false;
            }
            if mask & COUNTER_IDENT > 0 {
                if mask & SELF_IDENT == 0 {
                    result_set.insert(key.clone(), other_val.clone());
                }
            } else {
                *is_counter_ident = false;
            }
        }
    }
}

/// Internal function to make an `AlgebraicResult` from a new result set and flags
#[inline]
#[doc(hidden)]
pub fn set_lattice_integrate_into_result<S: SetLattice>(
    result_set: S,
    is_ident: bool,
    is_counter_ident: bool,
    self_set_len: usize,
    other_set_len: usize,
) -> AlgebraicResult<S> {
    let result_len = result_set.len();
    let mut ident_mask = 0;
    if is_ident && self_set_len == result_len {
        ident_mask |= SELF_IDENT;
    }
    if is_counter_ident && other_set_len == result_len {
        ident_mask |= COUNTER_IDENT;
    }
    if ident_mask > 0 {
        AlgebraicResult::Identity(ident_mask)
    } else {
        AlgebraicResult::Element(result_set)
    }
}

/// A macro to emit the [DistributiveLattice] implementation for a type that implements [SetLattice]
#[macro_export]
macro_rules! set_dist_lattice {
    ( $type_ident:ident $(< $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ >)? ) => {
        impl $(< $( $lt $( : $clt $(+ $dlt )* )? ),+ >)? $crate::ring::DistributiveLattice for $type_ident $(< $( $lt ),+ >)? where Self: $crate::ring::SetLattice + Clone, <Self as $crate::ring::SetLattice>::V: $crate::ring::DistributiveLattice {
            fn psubtract(&self, other: &Self) -> Option<$crate::ring::AlgebraicResult<Self>> {
                let mut is_ident = true;
                let mut result = self.clone();
                //Two code paths, so that we only iterate over the smaller set
                if $crate::ring::SetLattice::len(self) > $crate::ring::SetLattice::len(other) {
                    for (key, other_val) in $crate::ring::SetLattice::iter(other) {
                        if let Some(self_val) = $crate::ring::SetLattice::get(self, key) {
                            set_lattice_subtract_element(&mut result, key, self_val, other_val, &mut is_ident)
                        }
                    }
                } else {
                    for (key, self_val) in $crate::ring::SetLattice::iter(self) {
                        if let Some(other_val) = $crate::ring::SetLattice::get(other, key) {
                            set_lattice_subtract_element(&mut result, key, self_val, other_val, &mut is_ident)
                        }
                    }
                }
                if $crate::ring::SetLattice::is_empty(&result) {
                    None
                } else if is_ident {
                    Some($crate::ring::AlgebraicResult::Identity(SELF_IDENT))
                } else {
                    $crate::ring::SetLattice::shrink_to_fit(&mut result);
                    Some($crate::ring::AlgebraicResult::Element(result))
                }
            }
        }
    }
}

/// Internal function to subtract set elements and integrate the results
#[inline]
fn set_lattice_subtract_element<S: SetLattice>(
    result_set: &mut S,
    key: &S::K,
    self_val: &S::V,
    other_val: &S::V,
    is_ident: &mut bool,
) where S::V: DistributiveLattice {
    match self_val.psubtract(other_val) {
        Some(AlgebraicResult::Element(new_val)) => {
            SetLattice::replace(result_set, key, new_val);
            *is_ident = false;
        },
        Some(AlgebraicResult::Identity(mask)) => {
            debug_assert_eq!(mask, SELF_IDENT);
        },
        None => {
            SetLattice::remove(result_set, key);
            *is_ident = false;
        }
    }
}

impl<K: Clone + Eq + Hash, V: Clone + Lattice> SetLattice for HashMap<K, V> {
    type K = K;
    type V = V;
    type Iter<'a> = std::collections::hash_map::Iter<'a, K, V> where K: 'a, V: 'a;
    fn with_capacity(capacity: usize) -> Self { Self::with_capacity(capacity) }
    fn len(&self) -> usize { self.len() }
    fn is_empty(&self) -> bool { self.is_empty() }
    fn contains_key(&self, key: &Self::K) -> bool { self.contains_key(key) }
    fn insert(&mut self, key: Self::K, val: Self::V) { self.insert(key, val); }
    fn get(&self, key: &Self::K) -> Option<&Self::V> { self.get(key) }
    fn replace(&mut self, key: &Self::K, val: Self::V) { *self.get_mut(key).unwrap() = val }
    fn remove(&mut self, key: &Self::K) { self.remove(key); }
    fn iter<'a>(&'a self) -> Self::Iter<'a> { self.iter() }
    fn shrink_to_fit(&mut self) { self.shrink_to_fit(); }
}

set_lattice!(HashMap<K, V>);
set_dist_lattice!(HashMap<K, V>);

impl<K: Clone + Eq + Hash> SetLattice for HashSet<K> {
    type K = K;
    type V = ();
    type Iter<'a> = HashSetIterWrapper<'a, K> where K: 'a;
    fn with_capacity(capacity: usize) -> Self { Self::with_capacity(capacity) }
    fn len(&self) -> usize { self.len() }
    fn is_empty(&self) -> bool { self.is_empty() }
    fn contains_key(&self, key: &Self::K) -> bool { self.contains(key) }
    fn insert(&mut self, key: Self::K, _val: Self::V) { self.insert(key); }
    fn get(&self, key: &Self::K) -> Option<&Self::V> { self.get(key).map(|_| &()) }
    fn replace(&mut self, key: &Self::K, _val: Self::V) { debug_assert!(self.contains(key)); /* a noop since we can assume the key already exists */ }
    fn remove(&mut self, key: &Self::K) { self.remove(key); }
    fn iter<'a>(&'a self) -> Self::Iter<'a> { HashSetIterWrapper(self.iter()) }
    fn shrink_to_fit(&mut self) { self.shrink_to_fit(); }
}

pub struct HashSetIterWrapper<'a, K> (std::collections::hash_set::Iter<'a, K>);

impl<'a, K> Iterator for HashSetIterWrapper<'a, K> {
    type Item = (&'a K, &'a());
    fn next(&mut self) -> Option<(&'a K, &'a())> {
        self.0.next().map(|key| (key, &()))
    }
}

set_lattice!(HashSet<K>);
set_dist_lattice!(HashSet<K>);

#[cfg(test)]
mod tests {
    use super::{AlgebraicResult, SetLattice, COUNTER_IDENT, SELF_IDENT};
    use crate::ring::{DistributiveLattice, Lattice};
    use std::collections::{HashMap, HashSet};
    use std::fmt::Debug;

    type NestedSetMap = HashMap<u8, HashSet<u16>>;

    fn assert_binary_result<T, R>(
        result: R,
        self_value: &T,
        counter_value: &T,
        expected: &T,
        allow_counter_identity: bool,
        context: &str,
    ) where
        T: Clone + Default + Eq + Debug,
        R: Into<Option<AlgebraicResult<T>>>,
    {
        let result = result.into();
        match &result {
            None => {
                assert_eq!(expected, &T::default(), "{context}: None result");
            }
            Some(AlgebraicResult::Identity(mask)) => {
                assert_ne!(*mask, 0, "{context}: zero identity mask");
                assert_eq!(
                    *mask & !(SELF_IDENT | COUNTER_IDENT),
                    0,
                    "{context}: identity mask sets an out-of-arity bit"
                );
                if !allow_counter_identity {
                    assert_eq!(
                        *mask & COUNTER_IDENT,
                        0,
                        "{context}: non-commutative operation returned counter identity"
                    );
                }
                if *mask & SELF_IDENT != 0 {
                    assert_eq!(self_value, expected, "{context}: self identity mismatch");
                }
                if *mask & COUNTER_IDENT != 0 {
                    assert_eq!(
                        counter_value, expected,
                        "{context}: counter identity mismatch"
                    );
                }
            }
            Some(AlgebraicResult::Element(_)) => {}
        }

        let actual = result
            .map(|result| result.unwrap([self_value, counter_value]))
            .unwrap_or_default();
        assert_eq!(actual, *expected, "{context}: materialized result");
    }

    fn normalize_nested_map(map: &NestedSetMap) -> NestedSetMap {
        map.iter()
            .filter(|(_, values)| !values.is_empty())
            .map(|(key, values)| (*key, values.clone()))
            .collect()
    }

    fn assert_nested_result<R>(
        result: R,
        self_value: &NestedSetMap,
        counter_value: &NestedSetMap,
        expected: &NestedSetMap,
        allow_counter_identity: bool,
        context: &str,
    ) where R: Into<Option<AlgebraicResult<NestedSetMap>>> {
        let result = result.into();
        match &result {
            None => {
                assert!(expected.is_empty(), "{context}: None result");
            }
            Some(AlgebraicResult::Identity(mask)) => {
                assert_ne!(*mask, 0, "{context}: zero identity mask");
                assert_eq!(
                    *mask & !(SELF_IDENT | COUNTER_IDENT),
                    0,
                    "{context}: identity mask sets an out-of-arity bit"
                );
                if !allow_counter_identity {
                    assert_eq!(
                        *mask & COUNTER_IDENT,
                        0,
                        "{context}: non-commutative operation returned counter identity"
                    );
                }
                if *mask & SELF_IDENT != 0 {
                    assert_eq!(
                        normalize_nested_map(self_value),
                        *expected,
                        "{context}: self identity mismatch"
                    );
                }
                if *mask & COUNTER_IDENT != 0 {
                    assert_eq!(
                        normalize_nested_map(counter_value),
                        *expected,
                        "{context}: counter identity mismatch"
                    );
                }
            }
            Some(AlgebraicResult::Element(_)) => {}
        }

        let actual = result
            .map(|result| result.unwrap([self_value, counter_value]))
            .unwrap_or_default();
        assert_eq!(
            normalize_nested_map(&actual),
            *expected,
            "{context}: materialized result"
        );
    }

    fn mixed(seed: u64) -> u64 {
        let mut x = seed.wrapping_add(0x9e37_79b9_7f4a_7c15);
        x = (x ^ (x >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        x = (x ^ (x >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        x ^ (x >> 31)
    }

    fn generated_set(seed: u64, salt: u64) -> HashSet<u16> {
        let mut set = HashSet::new();
        for value in 0..48 {
            if mixed(seed ^ salt ^ ((value as u64) << 32)) % 5 < 2 {
                set.insert(value);
            }
        }
        set
    }

    fn generated_nested_map(seed: u64, salt: u64) -> NestedSetMap {
        let mut map = NestedSetMap::new();
        for key in 0..8 {
            let key_seed = mixed(seed ^ salt ^ ((key as u64) << 24));
            if key_seed % 4 == 0 {
                continue;
            }

            let mut values = HashSet::new();
            for value in 0..16 {
                if mixed(key_seed ^ ((value as u64) << 32)) % 5 < 2 {
                    values.insert(value);
                }
            }
            if key_seed % 31 == 0 {
                values.clear();
            }
            map.insert(key, values);
        }
        map
    }

    fn nested_join(a: &NestedSetMap, b: &NestedSetMap) -> NestedSetMap {
        let mut result = normalize_nested_map(a);
        for (key, values) in b {
            if values.is_empty() {
                continue;
            }
            result
                .entry(*key)
                .or_default()
                .extend(values.iter().copied());
        }
        result
    }

    fn nested_meet(a: &NestedSetMap, b: &NestedSetMap) -> NestedSetMap {
        let mut result = NestedSetMap::new();
        for (key, a_values) in a {
            let Some(b_values) = b.get(key) else {
                continue;
            };
            let values = a_values
                .intersection(b_values)
                .copied()
                .collect::<HashSet<_>>();
            if !values.is_empty() {
                result.insert(*key, values);
            }
        }
        result
    }

    fn nested_subtract(a: &NestedSetMap, b: &NestedSetMap) -> NestedSetMap {
        let mut result = NestedSetMap::new();
        for (key, a_values) in a {
            let values = if let Some(b_values) = b.get(key) {
                a_values.difference(b_values).copied().collect()
            } else {
                a_values.clone()
            };
            if !values.is_empty() {
                result.insert(*key, values);
            }
        }
        result
    }

    #[test]
    fn set_lattice_join_test1() {
        let mut a = HashSet::new();
        let mut b = HashSet::new();

        // Joining two empty sets still produces an element: both inputs are identities.
        let joined_result = a.pjoin(&b);
        assert_eq!(joined_result, AlgebraicResult::Identity(SELF_IDENT | COUNTER_IDENT));

        //Straightforward join
        a.insert("A");
        b.insert("B");
        let joined_result = a.pjoin(&b);
        assert!(joined_result.is_element());
        let joined = joined_result.unwrap([&a, &b]);
        assert_eq!(joined.len(), 2);
        assert!(joined.get("A").is_some());
        assert!(joined.get("B").is_some());

        //Make "self" contain more entries
        a.insert("C");
        let joined_result = a.pjoin(&b);
        assert!(joined_result.is_element());
        let joined = joined_result.unwrap([&a, &b]);
        assert_eq!(joined.len(), 3);

        //Make "other" contain more entries
        b.insert("D");
        b.insert("F");
        b.insert("H");
        let joined_result = a.pjoin(&b);
        assert!(joined_result.is_element());
        let joined = joined_result.unwrap([&a, &b]);
        assert_eq!(joined.len(), 6);

        //Test identity with self arg
        let joined_result = joined.pjoin(&b);
        assert_eq!(joined_result, AlgebraicResult::Identity(SELF_IDENT));

        //Test identity with other arg
        let joined_result = b.pjoin(&joined);
        assert_eq!(joined_result, AlgebraicResult::Identity(COUNTER_IDENT));

        //Test mutual identity
        let joined_result = joined.pjoin(&joined);
        assert_eq!(joined_result, AlgebraicResult::Identity(SELF_IDENT | COUNTER_IDENT));
    }

    #[test]
    fn set_lattice_meet_test1() {
        let mut a = HashSet::new();
        let mut b = HashSet::new();

        //Test disjoint result
        a.insert("A");
        b.insert("B");
        let meet_result = a.pmeet(&b);
        assert_eq!(meet_result, None);

        //Straightforward meet
        a.insert("A");
        a.insert("C");
        b.insert("B");
        b.insert("C");
        let meet_result = a.pmeet(&b).unwrap();
        assert!(meet_result.is_element());
        let meet = meet_result.unwrap([&a, &b]);
        assert_eq!(meet.len(), 1);
        assert!(meet.get("A").is_none());
        assert!(meet.get("B").is_none());
        assert!(meet.get("C").is_some());

        //Make "self" contain more entries
        a.insert("D");
        let meet_result = a.pmeet(&b).unwrap();
        assert!(meet_result.is_element());
        let meet = meet_result.unwrap([&a, &b]);
        assert_eq!(meet.len(), 1);

        //Make "other" contain more entries
        b.insert("D");
        b.insert("E");
        b.insert("F");
        let meet_result = a.pmeet(&b).unwrap();
        assert!(meet_result.is_element());
        let meet = meet_result.unwrap([&a, &b]);
        assert_eq!(meet.len(), 2);

        //Test identity with self arg
        let meet_result = meet.pmeet(&b);
        assert_eq!(meet_result, Some(AlgebraicResult::Identity(SELF_IDENT)));

        //Test identity with other arg
        let meet_result = b.pmeet(&meet);
        assert_eq!(meet_result, Some(AlgebraicResult::Identity(COUNTER_IDENT)));

        //Test mutual identity
        let meet_result = meet.pmeet(&meet);
        assert_eq!(meet_result, Some(AlgebraicResult::Identity(SELF_IDENT | COUNTER_IDENT)));
    }

    #[test]
    fn seeded_hash_set_operations_match_set_oracle() {
        #[cfg(miri)]
        const SEEDS: u64 = 1;
        #[cfg(not(miri))]
        const SEEDS: u64 = 256;

        for seed in 0..SEEDS {
            let a = generated_set(seed, 0x243f_6a88_85a3_08d3);
            let b = generated_set(seed, 0x1319_8a2e_0370_7344);

            let expected_join = a.union(&b).copied().collect::<HashSet<_>>();
            assert_binary_result(
                a.pjoin(&b),
                &a,
                &b,
                &expected_join,
                true,
                &format!("HashSet join seed {seed}"),
            );
            let mut join_in_place = a.clone();
            join_in_place.join_into(b.clone());
            assert_eq!(
                join_in_place, expected_join,
                "HashSet join_into seed {seed}"
            );

            let expected_meet = a.intersection(&b).copied().collect::<HashSet<_>>();
            assert_binary_result(
                a.pmeet(&b),
                &a,
                &b,
                &expected_meet,
                true,
                &format!("HashSet meet seed {seed}"),
            );
            let expected_subtract = a.difference(&b).copied().collect::<HashSet<_>>();
            assert_binary_result(
                a.psubtract(&b),
                &a,
                &b,
                &expected_subtract,
                false,
                &format!("HashSet subtract seed {seed}"),
            );
        }
    }

    #[test]
    fn seeded_hash_map_operations_match_nested_set_oracle() {
        #[cfg(miri)]
        const SEEDS: u64 = 1;
        #[cfg(not(miri))]
        const SEEDS: u64 = 256;

        for seed in 0..SEEDS {
            let a = generated_nested_map(seed, 0x243f_6a88_85a3_08d3);
            let b = generated_nested_map(seed, 0x1319_8a2e_0370_7344);
            let c = generated_nested_map(seed, 0xa409_3822_299f_31d0);

            let expected_join = nested_join(&a, &b);
            assert_nested_result(
                a.pjoin(&b),
                &a,
                &b,
                &expected_join,
                true,
                &format!("HashMap join seed {seed}"),
            );
            let mut join_in_place = a.clone();
            join_in_place.join_into(b.clone());
            assert_eq!(
                normalize_nested_map(&join_in_place),
                expected_join,
                "HashMap join_into seed {seed}"
            );

            let expected_meet = nested_meet(&a, &b);
            assert_nested_result(
                a.pmeet(&b),
                &a,
                &b,
                &expected_meet,
                true,
                &format!("HashMap meet seed {seed}"),
            );
            let expected_subtract = nested_subtract(&a, &b);
            assert_nested_result(
                a.psubtract(&b),
                &a,
                &b,
                &expected_subtract,
                false,
                &format!("HashMap subtract seed {seed}"),
            );

            let ab_join = a.pjoin(&b).unwrap_or([&a, &b]);
            let expected_chain = nested_subtract(&nested_join(&a, &b), &c);
            assert_nested_result(
                ab_join.psubtract(&c),
                &ab_join,
                &c,
                &expected_chain,
                false,
                &format!("HashMap chained join/subtract seed {seed}"),
            );
        }
    }

    /// Used in [set_lattice_join_test2] and [set_lattice_meet_test2]
    #[derive(Clone, Debug)]
    struct Map<'a>(HashMap::<&'a str, HashMap<&'a str, ()>>);// TODO, should be struct Map<'a>(HashMap::<&'a str, Map<'a>>); see comment above about chalk
    impl<'a> SetLattice for Map<'a> {
        type K = &'a str;
        type V = HashMap<&'a str, ()>; //Option<Box<Map<'a>>>; TODO, see comment above about chalk
        type Iter<'it> = std::collections::hash_map::Iter<'it, Self::K, Self::V> where Self: 'it, Self::K: 'it, Self::V: 'it;
        fn with_capacity(capacity: usize) -> Self { Map(HashMap::with_capacity(capacity)) }
        fn len(&self) -> usize { self.0.len() }
        fn is_empty(&self) -> bool { self.0.is_empty() }
        fn contains_key(&self, key: &Self::K) -> bool { self.0.contains_key(key) }
        fn insert(&mut self, key: Self::K, val: Self::V) { self.0.insert(key, val); }
        fn get(&self, key: &Self::K) -> Option<&Self::V> { self.0.get(key) }
        fn replace(&mut self, key: &Self::K, val: Self::V) { self.0.replace(key, val) }
        fn remove(&mut self, key: &Self::K) { self.0.remove(key); }
        fn iter<'it>(&'it self) -> Self::Iter<'it> { self.0.iter() }
        fn shrink_to_fit(&mut self) { self.0.shrink_to_fit(); }
    }
    set_lattice!(Map<'a>);

    #[test]
    /// Tests a HashMap containing more HashMaps
    //TODO: When the [chalk trait solver](https://github.com/rust-lang/chalk) lands in stable rust, it would be nice
    // to promote this test to sample code and implement an arbitrarily deep recursive structure.  But currently
    // that's not worth the complexity due to limits in the stable rust trait sovler.
    fn set_lattice_join_test2() {
        let mut a = Map::with_capacity(1);
        let mut b = Map::with_capacity(1);

        // Top level join
        let mut inner_map_1 = HashMap::with_capacity(1);
        inner_map_1.insert("1", ());
        a.0.insert("A", inner_map_1.clone());
        b.0.insert("B", inner_map_1);
        a.0.insert("C", HashMap::new());
        b.0.insert("C", HashMap::new());
        let joined_result = a.pjoin(&b);
        assert!(joined_result.is_element());
        let joined = joined_result.unwrap([&a, &b]);
        assert_eq!(joined.len(), 3);
        assert!(joined.get(&"A").is_some());
        assert!(joined.get(&"B").is_some());
        assert!(joined.get(&"C").unwrap().is_empty());
        a.0.remove("C");
        b.0.remove("C");

        // Two level join, results should be Element even though the key existed in both args, because the values joined
        let mut inner_map_2 = HashMap::with_capacity(1);
        inner_map_2.insert("2", ());
        b.0.remove("B");
        b.0.insert("A", inner_map_2);
        let joined_result = a.pjoin(&b);
        assert!(joined_result.is_element());
        let joined = joined_result.unwrap([&a, &b]);
        assert_eq!(joined.len(), 1);
        let joined_inner = joined.get(&"A").unwrap();
        assert_eq!(joined_inner.len(), 2);
        assert!(joined_inner.get(&"1").is_some());
        assert!(joined_inner.get(&"2").is_some());

        // Redoing the join should yield Identity
        let joined_result = joined.pjoin(&a);
        assert_eq!(joined_result.identity_mask().unwrap(), SELF_IDENT);
        let joined_result = b.pjoin(&joined);
        assert_eq!(joined_result.identity_mask().unwrap(), COUNTER_IDENT);
    }

    #[test]
    /// Tests a HashMap containing more HashMaps.  See comments on [set_lattice_join_test2]
    fn set_lattice_meet_test2() {
        let mut a = Map::with_capacity(1);
        let mut b = Map::with_capacity(1);

        let mut inner_map_a = HashMap::new();
        inner_map_a.insert("a", ());
        let mut inner_map_b = HashMap::new();
        inner_map_b.insert("b", ());
        let mut inner_map_c = HashMap::new();
        inner_map_c.insert("c", ());

        // One level meet
        a.0.insert("A", inner_map_a.clone());
        a.0.insert("C", inner_map_c.clone());
        b.0.insert("B", inner_map_b.clone());
        b.0.insert("C", inner_map_c.clone());
        let meet_result = a.pmeet(&b).unwrap();
        assert!(meet_result.is_element());
        let meet = meet_result.unwrap([&a, &b]);
        assert_eq!(meet.len(), 1);
        assert!(meet.get(&"A").is_none());
        assert!(meet.get(&"B").is_none());
        assert!(meet.get(&"C").is_some());

        // The inner values do not overlap, so no outer entry remains.
        let mut inner_map_1 = HashMap::with_capacity(1);
        inner_map_1.insert("1", ());
        a.0.insert("A", inner_map_1);
        let mut inner_map_2 = HashMap::with_capacity(1);
        inner_map_2.insert("2", ());
        b.0.remove("B");
        b.0.remove("C");
        b.0.insert("A", inner_map_2.clone());
        let meet_result = a.pmeet(&b);
        assert!(meet_result.is_none());

        // Two level meet, now should return Element, because the values have some overlap
        inner_map_2.insert("1", ());
        b.0.insert("A", inner_map_2);
        let meet_result = a.pmeet(&b).unwrap();
        assert!(meet_result.is_element());
        let meet = meet_result.unwrap([&a, &b]);
        assert_eq!(meet.len(), 1);
        let meet_inner = meet.get(&"A").unwrap();
        assert_eq!(meet_inner.len(), 1);
        assert!(meet_inner.get(&"1").is_some());
        assert!(meet_inner.get(&"2").is_none());

        // Redoing the meet should yield Identity
        let meet_result = meet.pmeet(&a).unwrap();
        assert_eq!(meet_result.identity_mask().unwrap(), SELF_IDENT);
        let meet_result = b.pmeet(&meet).unwrap();
        assert_eq!(meet_result.identity_mask().unwrap(), COUNTER_IDENT);
    }
}
//GOAT, do an impl of SetLattice for Vec as an indexed set


//GOAT, LatticeCounter and LatticeBitfield should be traits.
// BitfieldLattice should be implemented on bool
// Make monad types that can implement these traits on all prim types
// Make a "convertable_to" trait across all prim types

// GOAT, TEST TODO:  A fuzz test for some of the algebraic operations (join, meet, subtract) across all
// different path configurations and operation orderings.

// Envisioned Implementation:
// 1. Create `set_a` of N values (e.g. integers 0..100) and assign a pseudorandom path to each element
// 2. Create `set_b` of M values and assign a different pseudorandom path to each element
// 3. Compose pseudorandom subsets of `set_a` and `set_b` and put them into HashSets
// 4. Put corresponding concatenated paths (Cartesian product) into PathMaps.
// 5. Select an operation to perform, and do the same operation to both the HashSets contining simple
// indices and to the PathMaps.  And validate the results match
// 6. Loop back to 3, continuing to choose additional operations to perform.

// The reason behind the cartesian product (concatenated paths) is because the chances of getting overlap
// beyond the first couple bytes of a random path are very slim.  The Cartesian product appraoch
// means we are likely to get large common prefixes followed by splits deep in the trie, which will
// exercise the code more thoroughly.
