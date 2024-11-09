#![forbid(unsafe_code)]
#![no_std]
#![no_builtins]
#![deny(missing_docs)]
#![doc = include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/README.md"))]

extern crate core;
use core::{fmt, mem, iter::Iterator};

#[repr(transparent)]
struct Padding<T> { 
    pad: mem::MaybeUninit<T>,
}

impl<T> Padding<T> {
    #[inline(always)]
    const fn new() -> Self { Self { pad: mem::MaybeUninit::uninit() } }
}

enum Peeked<T> {
    Empty,
    // we must track if the result of the peek 
    // is None as the underlying iterator may not 
    // be fused. Peeking must not impact standard
    // iteration.
    // 
    // Padding to keep s elem is same location for 
    // perf improvement in draining of peeked operations.
    // 
    // Prior to this padding, core::iter::Peekable was 
    // performing 33% better than this implementation 
    // (which granted this supports peeking twice), 
    // after padding this implementation performed very 
    // slightly better than core::iter::Peekable.
    Once((Padding<Option<T>>, Option<T>)),
    // Support for the second peek. 
    //      once v     peek 2 v
    Twice((Option<T>, Option<T>))
    // By padding Once, draining the peeked operations
    // became significantly more straight forward. 
    // 
    // Once value returned first, and peek 2 value 
    // transitioned to Once value. With padding peek 2
    // going to Once can be a simple updating of the 
    // descriminator.
}

macro_rules! matched {
    (
        $peeked:expr => {
            empty => $empty:expr,
            once $ov:ident => $once:expr,
            twice $fv:ident $sv:ident => $twice:expr $(,)?
        }
    ) => {
        match $peeked {
            Peeked::Empty => $empty,
            Peeked::Once((_, $ov)) => $once,
            Peeked::Twice(($fv, $sv)) => $twice
        }
    }
}

macro_rules! on_left {
    ($peeked:expr => { $elem:ident => $do:expr, else => $else:expr $(,)? }) => {
        match $peeked {
            Peeked::Once((_, $elem)) | Peeked::Twice(($elem, _)) => $do,
            _ => $else
        }
    }
}

macro_rules! is_some_and {
    ($opt:ident, $and:ident) => {
        match &$opt {
            Some(__inner) => $and(__inner),
            None => false
        }
    }
}

enum MaybeTerm {
    Size(usize),
    Add(usize)
}

impl<T> Peeked<T> {
    #[inline(always)]
    #[must_use]
    const fn once(elem: Option<T>) -> Self {
        Self::Once((Padding::new(), elem))
    }

    #[inline(always)]
    #[must_use]
    const fn twice(first: Option<T>, second: Option<T>) -> Self {
        Self::Twice((first, second))
    }

    #[inline]
    #[must_use]
    const fn num_peeked(&self) -> u8 {
        match self {
            Self::Empty    => 0,
            Self::Once(_)  => 1,
            Self::Twice(_) => 2
        }
    }

    #[inline]
    #[must_use]
    const fn maybe_term(&self) -> MaybeTerm {
        match self {
            // terminal, known size
            Self::Once((_, None)) | Self::Twice((None, _)) => MaybeTerm::Size(0),
            Self::Twice((Some(_), None))    => MaybeTerm::Size(1),
            // non terminal, add
            Self::Twice((Some(_), Some(_))) => MaybeTerm::Add(2),
            Self::Once((_, Some(_)))        => MaybeTerm::Add(1),
            Self::Empty                     => MaybeTerm::Add(0)
        }
    }

    #[inline]
    #[must_use]
    fn take(&mut self) -> Option<Option<T>> {
        // empty -> once -> twice (once, new)
        //      peek    peek 
        // 
        // to reverse we go
        // 
        //        ret                 ret     None
        // twice (once, new) -> once (new) -> empty
        //                  take          take
        matched! { mem::replace(self, Self::Empty) => {
            empty     => None,
            once p    => Some(p),
            twice f s => { *self = Self::once(s); Some(f) }
        } }
    }

    #[inline(always)]
    #[must_use]
    fn drain(&mut self) -> Peeked<T> {
        mem::replace(self, Self::Empty)
    }

    // whenever a new caller peeks, it should not reference
    // double peek, and simply be the following state of the
    // iterator. This will return Once's element or Twice's first
    // element.
    #[inline]
    #[must_use]
    const fn init_peek(&self) -> Option<&T> {
        matched! { self => {
            empty              => None,
            once elem          => elem.as_ref(),
            twice elem _ignore => elem.as_ref()
        } }
    }

    #[inline]
    #[must_use]
    fn init_peek_mut(&mut self) -> Option<&mut T> {
        matched! { self => {
            empty              => None,
            once elem          => elem.as_mut(),
            twice elem _ignore => elem.as_mut()
        } }
    }

    #[inline]
    #[must_use]
    fn has_first_and<P>(&self, and: P) -> bool where P: FnOnce(&Option<T>) -> bool {
        on_left!(self => { elem => and(elem), else => false })
    }

    /// Returns `true` if the `Peekable` is two steps ahead of the underlying iterator (the 
    /// maximum lookahead). 
    /// 
    /// This returning true does not imply runtime errors will take place, but that 
    /// peeks and the next two `next` invocations will not touch the underlying iterator.
    #[inline]
    #[must_use]   
    const fn is_full(&self) -> bool {
        matches!(self, Self::Twice(_))
    }

    /// Returns `true` if the `Peekable` is at least one step ahead of the underlying iterator.
    #[inline]
    #[must_use]
    const fn non_empty(&self) -> bool {
        !self.is_empty()
    }

    /// Returns `true` if the `Peekable` is only one step ahead of the underlying iterator.
    #[inline]
    #[must_use]
    const fn only_one(&self) -> bool {
        matches!(self, Self::Once(_))
    }

    /// Returns `true` if the `Peekable` is not ahead of the underlying iterator.
    #[inline]
    #[must_use]
    const fn is_empty(&self) -> bool {
        matches!(self, Self::Empty)
    }

    /// Precondition:  The Peeked state must be Empty.
    /// Postcondition: The Peeked state will be Once.
    #[inline]
    #[cfg_attr(debug_assertions, track_caller)]
    fn add_first_peek(&mut self, elem: Option<T>) {
        debug_assert!(
            self.is_empty(), 
            "Precondition violated: `add_first_peek` was called when state was not Empty."
        );

        *self = Self::once(elem);
    }
}

/// The result of [`Peek::drain_if`], providing either the `Drained` elements if 
/// `predicate` returned `true`, otherwise returning the original [`Peek`] instance.
/// 
/// `drain_if` must take ownership, as `Peek` cannot exist if there are not currently
/// peeked elements, and if the `predicate` evaluated to `true` this would be the case.
#[must_use = "You must not ignore `drain_if` operation's result"]
pub enum DrainIf<'r, T: Iterator> {
    /// The successful result of the `drain_if` operation.
    Drained((Option<T::Item>, T::Item)),
    /// The original [`Peek`] instance from the unsatisfied `drain_if` operation.
    Peek(Peek<'r, T>)
}

impl<'r, T: Iterator> DrainIf<'r, T> {
    /// Extract the successful result of the `drain_if` operation.
    #[inline]
    pub fn drained(self) -> Option<(Option<T::Item>, T::Item)> {
        match self {
            Self::Drained(res) => Some(res),
            Self::Peek(_)      => None
        }
    }

    /// Extract the original [`Peek`] instance from the unsatisfied `drain_if` operation.
    #[inline]
    pub fn peek(self) -> Option<Peek<'r, T>> {
        match self {
            Self::Peek(peek) => Some(peek),
            Self::Drained(_) => None
        }
    }

    /// Maps the failure (which returns the [`Peek`] instance) and success (the drained elements)
    /// to `R`.
    /// 
    /// # Arguments
    /// 
    /// * `e` - A function which takes the original [`Peek`] instance, to potentially recover
    ///   from the predicate not being met.
    /// * `map` - A function which takes the drained elements if the predicate was met.
    #[inline]
    pub fn map_or_else<E, F, R>(self, e: E, map: F) -> R 
        where
            E: FnOnce(Peek<'r, T>) -> R,
            F: FnOnce((Option<T::Item>, T::Item)) -> R
    {
        match self {
            Self::Drained(res) => map(res),
            Self::Peek(peek)   => e(peek)
        }
    }
}

/// A view into a peeked element of a [`Peekable`] iterator.
///
/// When using [`peek`] on a [`Peekable`] iterator, it returns this struct 
/// rather than a direct reference to the next element. This wrapper provides 
/// additional operations that would not be possible with a simple reference, 
/// such as peeking further ahead or consuming elements conditionally.
///
/// # Lifetime
///
/// A `Peek` instance borrows the [`Peekable`] iterator mutably, ensuring that 
/// no other operations can be performed on the iterator while the peek is active. 
/// This maintains iterator safety while allowing complex peek operations.
///
/// # Example
///
/// ```
/// # use peek_again::Peekable;
/// let mut iter = Peekable::new([1, 2, 3].into_iter());
///
/// // Get a Peek instance
/// let mut peek = iter.peek();
///
/// // Compare the peeked value
/// assert_eq!(peek, Some(&1));
///
/// // Look at the next element through the Peek instance
/// assert_eq!(peek.peek(), Some(&2));
///
/// // We can also modify the peeked value
/// if let Some(val) = peek.get_mut() {
///     *val *= 10;
/// }
///
/// // The modification is reflected when we consume the value
/// assert_eq!(iter.next(), Some(10));
/// 
/// // We also can move the iterator forward, consuming the currently peeked element
/// let peek = iter.peek();
/// 
/// let elem = if peek == Some(&2) {
///     peek.consume()
/// } else {
///     None
/// };
/// 
/// assert_eq!(elem, Some(2));
/// assert_eq!(iter.next(), Some(3));
/// ```
///
/// # Advanced Usage
///
/// The `Peek` type supports conditional consumption of elements based on looking 
/// ahead:
///
/// ```
/// # use peek_again::Peekable;
/// let mut iter = Peekable::new([1, 2, 3].into_iter());
/// let peek = iter.peek();
///
/// // We can consume elements based on what comes next
/// peek.drain_if(|&next| next == 2)
///     .map_or_else(
///         |_peek| unreachable!("Next value was 2"),
///         |(curr, next)| {
///             assert_eq!(curr, Some(1));
///             assert_eq!(next, 2);
///         }
///     );
/// ```
///
/// [`peek`]: Peekable::peek
#[repr(transparent)]
pub struct Peek<'r, T: Iterator> {
    src: &'r mut Peekable<T>
}

impl<'r, T> PartialEq<Option<&T::Item>> for Peek<'r, T> 
    where
        T: Iterator,
        <T as Iterator>::Item: PartialEq
{
    #[inline]
    fn eq(&self, other: &Option<&T::Item>) -> bool { self.src.peeked.has_first_and(|data| data.as_ref().eq(other)) }
}

impl<'r, T> fmt::Debug for Peek<'r, T> 
    where 
        T: Iterator,
        <T as Iterator>::Item: fmt::Debug
{
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Peek").field(&self.get()).finish()
    }
}

impl<'r, T: Iterator> Peek<'r, T> {
    #[inline]
    #[must_use]
    #[cfg_attr(debug_assertions, track_caller)]
    fn new(src: &'r mut Peekable<T>) -> Self {
        debug_assert!(
            !src.peeked.is_empty(),
            "Invariant violated on construction of Peek. Peeked state must not be Empty."
        );
        Self { src }
    }

    /// Get a reference to the underlying peeked element.
    #[inline]
    pub const fn get(&self) -> Option<&T::Item> {
        self.src.peeked.init_peek()
    }

    /// Get a mutable reference to the underlying peeked element.
    #[inline]
    pub fn get_mut(&mut self) -> Option<&mut T::Item> {
        self.src.peeked.init_peek_mut()
    }

    /// Get a reference to the element following what is currently peeked.
    /// 
    /// This is equivalent to calling [`peek_2`] on the [`Peekable`] iterator 
    /// directly. 
    /// 
    /// If you just want a reference to what is currently peeked, see [`get`].
    /// 
    /// # Example
    /// 
    /// ```
    /// # use peek_again::Peekable;
    /// # let mut iter = Peekable::new([1, 2, 3, 4].into_iter());
    /// let mut peek = iter.peek();
    /// let value = peek.peek().copied();
    /// let peek_2_val = iter.peek_2().copied();
    /// 
    /// assert_eq!(value, peek_2_val);
    /// ```
    /// 
    /// [`peek_2`]: Peekable::peek_2
    /// [`get`]: Peek::get
    #[must_use]
    pub fn peek(&mut self) -> Option<&T::Item> {
        self.src.transition_forward();
        match &self.src.peeked {
            Peeked::Twice((_, elem)) => elem.as_ref(),
            // postcondition of transition_forward
            _ => unreachable!()
        }
    }

    /// Get a mutable reference to the element following what is currently peeked.
    /// 
    /// This is equivalent to calling [`peek_2_mut`] on the [`Peekable`] iterator 
    /// directly. 
    /// 
    /// If you just want a mutable reference to what is currently peeked, see [`get_mut`].
    /// 
    /// # Example
    /// 
    /// ```
    /// # use peek_again::Peekable;
    /// let mut iter = Peekable::new([1, 2, 3, 4].into_iter());
    /// let mut peek = iter.peek();
    /// peek.peek_mut().map(|val| *val *= 2);
    /// 
    /// assert_eq!(iter.peek_2(), Some(&4));
    /// ```
    /// 
    /// [`peek_2_mut`]: Peekable::peek_2_mut
    /// [`get_mut`]: Peek::get_mut
    #[must_use]
    pub fn peek_mut(&mut self) -> Option<&mut T::Item> {
        self.src.transition_forward();
        match &mut self.src.peeked {
            Peeked::Twice((_, elem)) => elem.as_mut(),
            // postcondition of transition_forward
            _ => unreachable!()
        }
    }

    /// Advance the iterator, taking ownership of the underlying peeked element.
    /// 
    /// This should be used similarly to [`next_if`], otherwise it is simply
    /// a less efficient mode of calling [`next`].
    /// 
    /// # Example
    /// 
    /// ```
    /// # use peek_again::Peekable;
    /// let mut iter = Peekable::new([1, 2, 3, 4].into_iter());
    /// let peeked = iter.peek();
    /// 
    /// // in this scenario, it'd be best to use `next_if_eq`
    /// let value = if peeked == Some(&1) {
    ///     peeked.consume()
    /// } else {
    ///     None
    /// };
    /// 
    /// assert_eq!(value, Some(1));
    /// ```
    /// 
    /// [`next_if`]: Peekable::next_if
    /// [`next`]: Peekable::next
    #[inline]
    pub fn consume(self) -> Option<T::Item> {
        self.src.peeked
            .take()
            .unwrap(/* Peek cannot exist unless there is at least one peeked element */)
    }

    /// Drain the peeked elements if `predicate` returns `true`.
    /// 
    /// This is akin to `next_if` but over `peek_2` rather than `peek`. 
    /// 
    /// # Returns
    /// 
    /// If the second peek was `Some` and the `predicate` returned `true` this will return 
    /// both peeked elements in order.
    /// 
    /// The first element returned is an option, despite it being atypical for `Some`
    /// to follow `None` in an iterator, it is not impossible as the underlying iterator may 
    /// not be fused.
    /// 
    /// For more information on fused iterators see the [`FusedIterator`] marker trait.
    /// 
    /// # Example
    /// 
    /// ```
    /// # use peek_again::Peekable;
    /// # 
    /// let mut iter = Peekable::new([1, 2, 3, 4].into_iter());
    /// let mut peeked = iter.peek();
    /// 
    /// // since we are peeked, drain_if is referencing the second element.
    /// peeked.drain_if(|next| next == &2).map_or_else(
    ///     |mut _peeked| unreachable!("The second element was two"),
    ///     |(first, second)| {
    ///         assert_eq!(first, Some(1));
    ///         assert_eq!(second, 2);
    ///     }
    /// );
    /// ```
    /// 
    /// [`FusedIterator`]: core::iter::FusedIterator
    // drain_if must take ownership of self, as if the draining took place 
    // it would violate `Peek`'s invariant.
    pub fn drain_if<F>(self, predicate: F) -> DrainIf<'r, T> 
        where F: FnOnce(&T::Item) -> bool
    {
        self.src.transition_forward();
        match mem::replace(&mut self.src.peeked, Peeked::Empty) {
            Peeked::Twice((first, second)) => match second {
                Some(second) if predicate(&second) => DrainIf::Drained((first, second)),
                _ => {
                    self.src.peeked = Peeked::twice(first, second);
                    DrainIf::Peek(self)
                }
            },
            // Due to transition_forward we are guaranteed to be full.
            _ => unreachable!()
        }
    }
}

/// Interface for the current state of the [`Peekable`] iterator.
/// 
/// For a more detailed description, see [`Peekable::peek_state`].
#[repr(transparent)]
#[must_use]
#[derive(Copy, Clone)]
pub struct PeekState<'r, T> {
    peeked: &'r Peeked<T>
}

impl<'r, T> PeekState<'r, T> {
    #[inline]
    const fn new(peeked: &'r Peeked<T>) -> Self {
        Self { peeked }
    }

    /// Returns `true` if the `Peekable` is two steps behind the underlying iterator (the 
    /// maximum lookahead). 
    /// 
    /// This returning true does not imply runtime errors will take place, but that 
    /// subsequent peeks and the next two `next` invocations will not touch the underlying 
    /// iterator.
    #[inline]
    #[must_use]   
    pub const fn is_full(&self) -> bool {
        self.peeked.is_full()
    }

    /// Returns `true` if the `Peekable` is at least one step behind the underlying iterator.
    #[inline]
    #[must_use]
    pub const fn non_empty(&self) -> bool {
        self.peeked.non_empty()
    }

    /// Returns `true` if the `Peekable` is only one step behind the underlying iterator.
    #[inline]
    #[must_use]
    pub const fn only_one(&self) -> bool {
        self.peeked.only_one()
    }

    /// Returns `true` if the `Peekable` is not behind the underlying iterator. 
    /// 
    /// **This does not imply the underlying iterator has been exhausted**
    #[inline]
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.peeked.is_empty()
    }

    /// Returns the offset from the `Peekable` iterator and the underlying iterator.
    /// 
    /// The offset is simply how far the `Peekable` iterator has peeked; so if you
    /// called `peek_2` without advancing the `Peekable` iterator this will return `2`.
    /// 
    /// # Example
    /// 
    /// ```
    /// # use peek_again::Peekable;
    /// # let mut iter = Peekable::new([1, 2, 3, 4].into_iter());
    /// assert_eq!(iter.peek_state().num_peeked(), 0);
    /// iter.peek();
    /// assert_eq!(iter.peek_state().num_peeked(), 1);
    /// iter.next(); // decrements num_peeked as we move forward
    /// assert_eq!(iter.peek_state().num_peeked(), 0);
    /// iter.peek_2();
    /// assert_eq!(iter.peek_state().num_peeked(), 2);
    /// iter.peek();
    /// // the peek is simply going to use what we've peeked previously,
    /// // no mutation of state.
    /// assert_eq!(iter.peek_state().num_peeked(), 2);
    /// iter.next();
    /// assert_eq!(iter.peek_state().num_peeked(), 1);
    /// iter.next();
    /// assert_eq!(iter.peek_state().num_peeked(), 0);
    /// ```
    #[inline]
    #[must_use]
    pub const fn num_peeked(&self) -> u8 {
        self.peeked.num_peeked()
    }
}

/// An iterator which can peek the next two elements.
/// 
/// Similar to core library's [`Peekable`][1] iterator, offering equivalent performance
/// for common operations, and a slight performance regression if peeking two elements in 
/// the future.
/// 
/// # Example
/// 
/// ```
/// use peek_again::Peekable;
/// 
/// let src: [u8; 4] = [1, 2, 3, 4];
/// let mut iter = Peekable::new(src.into_iter());
/// 
/// assert_eq!(iter.peek_2(), Some(&2));
///
/// let mut peek = iter.peek(); 
/// assert_eq!(peek, Some(&1));
/// 
/// // we can also call peek.peek() for the same effect as peek_2
/// // (reason peek is mut)
/// assert_eq!(peek.peek(), Some(&2));
/// 
/// assert_eq!(iter.next(), Some(1));
/// assert_eq!(iter.next(), Some(2));
/// 
/// let three = iter.next_if_eq(&3);
/// assert_eq!(three, Some(3));
/// 
/// assert!(iter.next_if_eq(&7).is_none());
/// assert_eq!(iter.peek(), Some(&4));
/// ```
/// 
/// [1]: core::iter::Peekable
pub struct Peekable<T: Iterator> {
    iter: T,
    peeked: Peeked<T::Item>
}

impl<T: Iterator> Peekable<T> {
    /// Wrap an iterator providing the ability to peek up to the next two elements.
    pub const fn new(iter: T) -> Self {
        Self { iter, peeked: Peeked::Empty }
    }

    /// Get the current state of the [`Peekable`] iterator.
    /// 
    /// Offering the capacity to look at future elements is not black magic,
    /// the [`Peekable`] iterator must call the underlying iterator's `next` method
    /// to look at the next element.
    /// 
    /// Peekable iterators store the result of calling next under peek operations;
    /// when calling the `Peekable` iterator's own `next` method, it drains the 
    /// stored elements from `peek` and `peek_2` operations before invoking the
    /// underlying iterator's `next` method.
    ///
    /// This returns the state of the [`Peekable`] iterator, allowing to check 
    /// whether the [`Peekable`] iterator is behind the underlying iterator and
    /// by how much.
    /// 
    /// In general you will not need to use this, however it is here.
    /// 
    /// # Example
    /// 
    /// ```
    /// # use peek_again::Peekable;
    /// # let src = [0u8; 3];
    /// # let mut peekable = Peekable::new(src.into_iter());
    /// assert!(peekable.peek_state().is_empty());
    /// 
    /// let _ = peekable.peek();
    /// assert!(peekable.peek_state().non_empty());
    /// assert!(peekable.peek_state().only_one());
    /// 
    /// let _ = peekable.peek_2();
    /// assert!(peekable.peek_state().non_empty());
    /// // is_full does not imply subsequent peeks will 
    /// // fail, it only implies that the underlying 
    /// // iterator is two positions ahead of the Peekable
    /// // iterator.
    /// assert!(peekable.peek_state().is_full());
    /// // is_full and only_one are mutually exclusive
    /// assert!(!peekable.peek_state().only_one());
    ///
    /// peekable.next();
    /// peekable.next();
    /// assert!(peekable.peek_state().is_empty());
    /// ```
    #[inline]
    pub const fn peek_state(&self) -> PeekState<'_, T::Item> {
        PeekState::new(&self.peeked)
    }

    /// Precondition:  Peeked state must not be `Empty`.
    /// Postcondition: Peeked state will always be `Twice`.
    #[inline]
    fn transition_forward(&mut self) {
        // since we are only to be used in a peek, the state of peeked must not be empty. 
        // We are either transitioning to twice, or returning the final twice element. 
        self.peeked = match mem::replace(&mut self.peeked, Peeked::Empty) {
            twice @ Peeked::Twice(_) => twice,
            Peeked::Once((_, elem))  => Peeked::Twice((elem, self.iter.next())),
            // precondition
            Peeked::Empty            => unreachable!()
        }; 
    }

    /// Postcondition: Peeked state will always be `Twice`.
    fn fill(&mut self) {
        self.peeked = match mem::replace(&mut self.peeked, Peeked::Empty) {
            twice @ Peeked::Twice(_) => twice,
            Peeked::Once((_, elem))  => Peeked::twice(elem, self.iter.next()),
            Peeked::Empty            => {
                let first  = self.iter.next();
                let second = self.iter.next();
                Peeked::twice(first, second)
            }
        }; 
    }

    /// Returns a reference to the `next()` value without advancing the iterator.
    /// 
    /// # Returns
    /// 
    /// Unlike the core library's [`Peekable::peek`][1], this returns a custom 
    /// [`Peek`] type rather than the `Option<&next val>` directly. This allows
    /// for extra flexibility. 
    /// 
    /// # Example
    /// 
    /// ```
    /// # use peek_again::Peekable;
    /// # let mut lexer = Peekable::new(["undecidable!", "figured-out"].into_iter());
    /// let mut peeked = lexer.peek();
    /// 
    /// if peeked == Some(&"undecidable!") {
    ///     // take the peeked elements if the next token is "figured-out"
    ///     let (undecidable, next) = peeked
    ///         .drain_if(|next| next == &"figured-out")
    ///         .drained()
    ///         .unwrap();
    ///     
    ///     // undecidable is an option as the iterator may not
    ///     // be fused!
    ///     assert_eq!(undecidable, Some("undecidable!"));
    ///     // the result of `drain_if` was `Drained`, so next is 
    ///     // not an option
    ///     assert_eq!(next, "figured-out");
    /// }
    /// ```
    /// 
    /// [`next`]: Iterator::next
    /// [1]: core::iter::Peekable::peek
    #[inline]
    #[must_use]
    pub fn peek(&mut self) -> Peek<'_, T> {
        if self.peeked.is_empty() {
            self.peeked.add_first_peek(self.iter.next());
        }
        Peek::new(self)
    }

    /// Returns a reference to the element two steps ahead of the iterator's 
    /// current position without advancing it.
    ///
    /// This method allows looking ahead by two elements, in contrast to [`peek`] 
    /// which only looks ahead by one. If you need to peek both elements, 
    /// you can use [`peek`] and then call [`peek`][`Peek::peek`] on
    /// the returned [`Peek`] instance.
    ///
    /// # Example
    ///
    /// ```
    /// # use peek_again::Peekable;
    /// let mut iter = Peekable::new([1, 2, 3, 4].into_iter());
    ///
    /// assert_eq!(iter.peek_2(), Some(&2));
    /// // The iterator has not advanced
    /// assert_eq!(iter.next(), Some(1));
    ///
    /// // After advancing, peek_2 now looks at the element after next
    /// assert_eq!(iter.peek_2(), Some(&3));
    /// assert_eq!(iter.next(), Some(2));
    /// ```
    ///
    /// [`peek`]: Peekable::peek
    /// [`Peek::peek`]: Peek::peek
    #[inline]
    #[must_use]
    pub fn peek_2(&mut self) -> Option<&T::Item> {
        self.fill();
        match &self.peeked {
            Peeked::Twice((_, second)) => second.as_ref(),
            // fill postcondition
            _ => unreachable!()
        }
    }

    /// Returns a mutable reference to the element two steps ahead of the iterator's 
    /// current position without advancing it.
    /// 
    /// Similar to [`peek_2`], but provides mutable access to the peeked element. 
    /// This can be useful when you need to modify an element before actually consuming it.
    /// 
    /// # Example
    /// 
    /// ```
    /// # use peek_again::Peekable;
    /// let mut iter = Peekable::new([1, 2, 3, 4].into_iter());
    /// 
    /// // Modify the second element before consuming it
    /// if let Some(second) = iter.peek_2_mut() {
    ///     *second *= 2;
    /// }
    /// 
    /// assert_eq!(iter.next(), Some(1));
    /// assert_eq!(iter.next(), Some(4)); // Modified from 2 to 4
    /// assert_eq!(iter.next(), Some(3));
    /// ```
    /// 
    /// [`peek_2`]: Peekable::peek_2
    #[inline]
    #[must_use]
    pub fn peek_2_mut(&mut self) -> Option<&mut T::Item> {
        self.fill();
        match &mut self.peeked {
            Peeked::Twice((_, second)) => second.as_mut(),
            // fill postcondition
            _ => unreachable!()
        } 
    }

    /// Advances the iterator and returns the next value if the provided 
    /// predicate returns `true`.
    ///
    /// This method will peek at the next element and evaluate it with the 
    /// given predicate. If the predicate returns `true`, the iterator advances 
    /// and returns `Some(next)`. If the predicate returns `false`, the iterator 
    /// does not advance and returns `None`.
    ///
    /// This operation is similar to [`peek`] followed by [`next`] or [`consume`], but 
    /// is slightly more efficient as it is optimized for this exact purpose.
    ///
    /// # Example
    ///
    /// ```
    /// # use peek_again::Peekable;
    /// let mut iter = Peekable::new([1, 2, 3, 4].into_iter());
    ///
    /// // Consume values while they're less than 3
    /// assert_eq!(iter.next_if(|&x| x < 3), Some(1));
    /// assert_eq!(iter.next_if(|&x| x < 3), Some(2));
    /// assert_eq!(iter.next_if(|&x| x < 3), None);    
    /// 
    /// // The iterator hasn't advanced since the predicate returned false
    /// assert_eq!(iter.next(), Some(3));
    /// ```
    ///
    /// [`peek`]: Peekable::peek
    /// [`consume`]: Peek::consume
    /// [`next`]: Iterator::next
    pub fn next_if(&mut self, func: impl FnOnce(&T::Item) -> bool) -> Option<T::Item> {
        match mem::replace(&mut self.peeked, Peeked::Empty) {
            //             true
            //      +-----------------+
            //      v                 |
            //    +-------+         +------+  false   +------+
            //    | Empty | ------> | func | -------> | Once |
            //    +-------+         +------+          +------+
            Peeked::Empty => {
                let next = self.iter.next();

                if is_some_and!(next, func) {
                    next
                } else {
                    self.peeked = Peeked::once(next);
                    None
                }
            },
            //             false
            //      +-----------------+
            //      v                 |
            //    +------+          +------+  true   +-------+
            //    | Once | -------> | func | ------> | Empty |
            //    +------+          +------+         +-------+
            Peeked::Once((_, elem)) => if is_some_and!(elem, func) {
                elem
            } else {
                self.peeked = Peeked::once(elem);
                None
            },
            //              false
            //       +------------------+
            //       v                  |
            //     +-------+          +------+  true   +------+
            //     | Twice | -------> | func | ------> | Once |
            //     +-------+          +------+         +------+
            Peeked::Twice((elem, later)) => if is_some_and!(elem, func) {
                self.peeked = Peeked::once(later);
                elem
            } else {
                self.peeked = Peeked::twice(elem, later);
                None
            }
        }
    }

    /// Advances the iterator and returns the next value if it is equal to 
    /// the provided value.
    /// 
    /// This method is a specialized version of [`next_if`] that compares the 
    /// next value with the provided value for equality. If they are equal, the 
    /// iterator advances and returns `Some(next)`. If they are not equal, the 
    /// iterator does not advance and returns `None`.
    /// 
    /// # Example
    /// 
    /// ```
    /// # use peek_again::Peekable;
    /// let mut iter = Peekable::new(["a", "b", "c"].into_iter());
    /// 
    /// assert_eq!(iter.next_if_eq(&"a"), Some("a"));
    /// assert_eq!(iter.next_if_eq(&"z"), None);  // "b" != "z", so no advancement
    /// assert_eq!(iter.next(), Some("b"));       // iterator is still at "b"
    /// ```
    /// 
    /// # Comparison with [`next_if`]
    /// 
    /// This method is equivalent to calling:
    /// ```
    /// # use peek_again::Peekable;
    /// # let mut iter = Peekable::new(["a"].into_iter());
    /// # let expected = "a";
    /// iter.next_if(|x| x == &expected);
    /// ```
    /// 
    /// However, it may be more readable when checking for equality directly.
    /// 
    /// [`next_if`]: Peekable::next_if
    #[inline]
    pub fn next_if_eq<E>(&mut self, expected: &E) -> Option<T::Item> 
        where
            E: ?Sized,
            <T as Iterator>::Item: PartialEq<E>,
    {
        self.next_if(|next| next.eq(expected))
    }
}

impl<T: Iterator> Iterator for Peekable<T> {
    type Item = T::Item;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        match self.peeked.take() {
            Some(v) => v,
            None => self.iter.next(),
        }
    }

    #[inline]
    fn count(self) -> usize {
        let amount = match self.peeked {
            Peeked::Empty                  => 0,
            Peeked::Once ((_, Some(_)))    => 1,
            Peeked::Twice((Some(_), next)) => match next {
                Some(_) => 2,
                None    => 1
            },
            _ => return 0
        };

        amount + self.iter.count()
    }

    #[inline]
    fn nth(&mut self, n: usize) -> Option<T::Item> {
        if n == 0 {
            self.peeked.take().unwrap_or_else(|| self.iter.next())
        } else {
            match self.peeked.drain() {
                Peeked::Twice((_, elem)) => if n == 1 {
                    elem
                } else {
                    self.iter.nth(n - 2)
                },
                Peeked::Once(_) => self.iter.nth(n - 1),
                Peeked::Empty => self.iter.nth(n)
            }
        }
    }

    #[inline]
    fn last(mut self) -> Option<T::Item> {
        match self.peeked.drain() {
            Peeked::Empty => self.iter.last(),
            // first element none -> none 
            Peeked::Once((_, None)) | Peeked::Twice((None, _)) => None,
            // known single element
            Peeked::Twice((elem @ Some(_), None)) => elem,
            // all some implies final peeked elem may be 
            // last if underlying iterator last is none
            Peeked::Once((_, elem @ Some(_))) 
            | Peeked::Twice((Some(_), elem @ Some(_))) => self.iter.last().or(elem)
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let peek_len = match self.peeked.maybe_term() {
            MaybeTerm::Size(known_size) => return (known_size, Some(known_size)),
            MaybeTerm::Add(amnt) => amnt
        };

        let (lo, hi) = self.iter.size_hint();
        let lo = lo.saturating_add(peek_len);
        let hi = hi.and_then(|l| l.checked_add(peek_len));

        (lo, hi)
    }

    #[inline]
    fn fold<Acc, Fold>(mut self, init: Acc, mut fold: Fold) -> Acc
        where
            Self: Sized,
            Fold: FnMut(Acc, Self::Item) -> Acc,
    {
        let acc = match self.peeked.drain() {
            // known terminal states
            Peeked::Once((_, None)) | Peeked::Twice((None, _)) => return init,
            Peeked::Twice((Some(first), None))                 => return fold(init, first),

            // delegate to underlying iterator
            Peeked::Twice((Some(first), Some(second))) => {
                let acc = fold(init, first);
                fold(acc, second)
            },
            Peeked::Once((_, Some(first)))             => fold(init, first),
            Peeked::Empty                              => init
        };

        self.iter.fold(acc, fold)
    }

    // since we cannot implement try_fold in stable rust, we'll want to implement the 
    // dependents of try_fold
    #[inline]
    fn all<F>(&mut self, mut f: F) -> bool 
        where
            Self: Sized,
            F: FnMut(Self::Item) -> bool,
    {
        let peek_res = match self.peeked.drain() {
            // non-known terminals
            Peeked::Once((_, Some(elem)))              => f(elem),
            Peeked::Twice((Some(first), Some(second))) => f(first) && f(second),
            Peeked::Empty                              => true,
            
            // terminal
            Peeked::Once((_, None)) | Peeked::Twice((None, _)) => return true,    // empty -> true
            Peeked::Twice((Some(elem), None))                  => return f(elem), // known len 1 
        };

        peek_res && self.iter.all(f)
    }

    #[inline]
    fn any<F>(&mut self, mut f: F) -> bool
        where
            Self: Sized,
            F: FnMut(Self::Item) -> bool,
    {
        let peek_res = match self.peeked.drain() {
            // non-known terminals
            Peeked::Once((_, Some(elem)))              => f(elem),
            Peeked::Twice((Some(first), Some(second))) => f(first) || f(second),
            Peeked::Empty                              => false,
            
            // terminal
            Peeked::Once((_, None)) | Peeked::Twice((None, _)) => return false,   // empty -> false
            Peeked::Twice((Some(elem), None))                  => return f(elem), // known len 1 
        };

        peek_res || self.iter.any(f)
    }

    #[inline]
    fn find<P>(&mut self, mut predicate: P) -> Option<Self::Item> 
        where
            Self: Sized,
            P: FnMut(&Self::Item) -> bool,
    {
        match self.peeked.drain() {
            // cover potential peeked find
            Peeked::Once((_, Some(elem))) => if predicate(&elem) { return Some(elem) } else {/* continue */}, 
            
            Peeked::Twice((Some(elem), Some(n_elem))) => if predicate(&elem) {
                return Some(elem)
            } else if predicate(&n_elem) {
                return Some(n_elem)
            } else {
                /* continue */
            },

            // cover peeked indication of termination
            Peeked::Once((_, None)) | Peeked::Twice((None, _)) => return None,
            // cover known termination with single entry
            Peeked::Twice((Some(elem), None)) => return predicate(&elem).then_some(elem),

            // peeked is empty, continue to underlying iterator
            Peeked::Empty => {}
        }

        self.iter.find(predicate)
    }

    #[inline]
    fn find_map<B, F>(&mut self, mut f: F) -> Option<B> 
        where
            Self: Sized,
            F: FnMut(Self::Item) -> Option<B>
    {
        match self.peeked.drain() {
            // cover potential peeked find
            Peeked::Once((_, Some(elem))) => if let Some(out) = f(elem) { return Some(out) } else {/* continue */}, 
            
            Peeked::Twice((Some(elem), Some(n_elem))) => if let Some(out) = f(elem) {
                return Some(out)
            } else if let Some(n_out) = f(n_elem) {
                return Some(n_out)
            } else {
                /* continue */
            },

            // cover peeked indication of termination
            Peeked::Once((_, None)) | Peeked::Twice((None, _)) => return None,
            // cover known termination with single entry
            Peeked::Twice((Some(elem), None)) => return f(elem),

            // peeked is empty, continue to underlying iterator
            Peeked::Empty => {}
        }

        self.iter.find_map(f) 
    }

    #[inline]
    fn position<P>(&mut self, mut predicate: P) -> Option<usize>
        where
            Self: Sized,
            P: FnMut(Self::Item) -> bool,
    {
        let offset = match self.peeked.drain() {
            // cover potential peeked find
            Peeked::Once((_, Some(elem))) => if predicate(elem) { return Some(0) } else {/* continue */ 1}, 

            Peeked::Twice((Some(elem), Some(n_elem))) => if predicate(elem) {
                return Some(0)
            } else if predicate(n_elem) {
                return Some(1)
            } else {
                /* continue */
                2
            },
            
            // cover peeked indication of termination
            Peeked::Once((_, None)) | Peeked::Twice((None, _)) => return None,
            // cover known termination with single entry
            Peeked::Twice((Some(elem), None)) => return predicate(elem).then_some(0),

            // peeked is empty, continue to underlying iterator
            Peeked::Empty => 0
        };

        self.iter.position(predicate).map(|out| out + offset) 
    }
}

// I have some reservations when it comes to implementing DoubleEndedIterator etc. May be implemented.
// ExactSize, Fused, etc can also be implemented, I will do this later.

#[cfg(test)]
mod tests {
    extern crate alloc;
    use super::*;
    use alloc::{format, vec::Vec};
    use proptest::prelude::*;

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(50_000))]

        #[test]
        fn iter_find(collection in any::<Vec<u8>>(), to_find in any::<u8>()) {
            match Peekable::new(collection.iter()).find(|elem| *elem == &to_find) {
                Some(elem) => prop_assert_eq!(*elem, to_find),
                None => prop_assert!(collection.into_iter().find(|elem| elem == &to_find).is_none())
            }
        }

        #[test]
        fn iter_find_with_peeked(collection in any::<Vec<u8>>(), to_find in any::<u8>()) {
            let mut iter = Peekable::new(collection.iter());
            let _ = iter.peek();

            match iter.find(|elem| *elem == &to_find) {
                Some(elem) => prop_assert_eq!(*elem, to_find),
                None => prop_assert!(collection.into_iter().find(|elem| elem == &to_find).is_none())
            }
        }

        #[test]
        fn iter_find_with_peeked_2(collection in any::<Vec<u8>>(), to_find in any::<u8>()) {
            let mut iter = Peekable::new(collection.iter());
            let _ = iter.peek_2();

            match iter.find(|elem| *elem == &to_find) {
                Some(elem) => prop_assert_eq!(*elem, to_find),
                None => prop_assert!(collection.into_iter().find(|elem| elem == &to_find).is_none())
            }
        }

        #[test]
        fn iter_position(collection in any::<Vec<u8>>(), to_find in any::<u8>()) {
            match Peekable::new(collection.iter()).position(|elem| elem == &to_find) {
                Some(pos) => prop_assert_eq!(pos, collection.into_iter().position(|elem| elem == to_find).unwrap()),
                None => prop_assert!(collection.into_iter().position(|elem| elem == to_find).is_none())
            }
        }

        #[test]
        fn iter_position_peeked(collection in any::<Vec<u8>>(), to_find in any::<u8>()) {
            let mut iter = Peekable::new(collection.iter());
            let _ = iter.peek();

            match iter.position(|elem| elem == &to_find) {
                Some(pos) => prop_assert_eq!(pos, collection.into_iter().position(|elem| elem == to_find).unwrap()),
                None => prop_assert!(collection.into_iter().position(|elem| elem == to_find).is_none())
            }
        }

        #[test]
        fn iter_position_peeked_2(collection in any::<Vec<u8>>(), to_find in any::<u8>()) {
            let mut iter = Peekable::new(collection.iter());
            let _ = iter.peek_2();

            match iter.position(|elem| elem == &to_find) {
                Some(pos) => prop_assert_eq!(pos, collection.into_iter().position(|elem| elem == to_find).unwrap()),
                None => prop_assert!(collection.into_iter().position(|elem| elem == to_find).is_none())
            }
        }

        #[test]
        fn iter_any(collection in any::<Vec<u8>>(), to_find in any::<u8>()) {
            if Peekable::new(collection.iter()).any(|elem| elem == &to_find) {
                prop_assert!(collection.into_iter().any(|elem| elem == to_find))
            } else { 
                prop_assert!(!collection.into_iter().any(|elem| elem == to_find))
            }
        }

        #[test]
        fn iter_any_peeked(collection in any::<Vec<u8>>(), to_find in any::<u8>()) {
            let mut iter = Peekable::new(collection.iter());
            let _ = iter.peek();

            if iter.any(|elem| elem == &to_find) {
                prop_assert!(collection.into_iter().any(|elem| elem == to_find))
            } else { 
                prop_assert!(!collection.into_iter().any(|elem| elem == to_find))
            }
        }

        #[test]
        fn iter_any_peeked_2(collection in any::<Vec<u8>>(), to_find in any::<u8>()) {
            let mut iter = Peekable::new(collection.iter());
            let _ = iter.peek_2();

            if iter.any(|elem| elem == &to_find) {
                prop_assert!(collection.into_iter().any(|elem| elem == to_find))
            } else { 
                prop_assert!(!collection.into_iter().any(|elem| elem == to_find))
            }
        }

        #[test]
        fn iter_all(collection in any::<Vec<u8>>(), to_find in any::<u8>()) {
            if Peekable::new(collection.iter()).all(|elem| elem == &to_find) {
                prop_assert!(collection.into_iter().all(|elem| elem == to_find))
            } else { 
                prop_assert!(!collection.into_iter().all(|elem| elem == to_find))
            }
        }

        #[test]
        fn iter_all_peeked(collection in any::<Vec<u8>>(), to_find in any::<u8>()) {
            let mut iter = Peekable::new(collection.iter());
            let _ = iter.peek();

            if iter.all(|elem| elem == &to_find) {
                prop_assert!(collection.into_iter().all(|elem| elem == to_find))
            } else { 
                prop_assert!(!collection.into_iter().all(|elem| elem == to_find))
            }
        }

        #[test]
        fn iter_all_peeked_2(collection in any::<Vec<u8>>(), to_find in any::<u8>()) {
            let mut iter = Peekable::new(collection.iter());
            let _ = iter.peek_2();

            if iter.all(|elem| elem == &to_find) {
                prop_assert!(collection.into_iter().all(|elem| elem == to_find))
            } else { 
                prop_assert!(!collection.into_iter().all(|elem| elem == to_find))
            }
        }

        #[test]
        fn iter_nth(amnt in 0..16usize) {
            let mut collection = 0..=16;

            let res = Peekable::new(collection.clone()).nth(amnt);
            prop_assert_eq!(res, collection.nth(amnt));
        }

        #[test]
        fn iter_nth_peeked(amnt in 0..16usize) {
            let mut collection = 0..=16;

            let mut iter = Peekable::new(collection.clone());
            let _ = iter.peek();
            let res = iter.nth(amnt);

            prop_assert_eq!(res, collection.nth(amnt));
        }

        #[test]
        fn iter_nth_peeked_2(amnt in 0..16usize) {
            let mut collection = 0..=16;

            let mut iter = Peekable::new(collection.clone());
            let _ = iter.peek_2();
            let res = iter.nth(amnt);

            prop_assert_eq!(res, collection.nth(amnt));
        }

        #[test]
        fn iter_find_map(collection in any::<Vec<usize>>()) {
            match Peekable::new(collection.iter()).find_map(|elem| u8::try_from(*elem).ok()) {
                Some(m) => prop_assert_eq!(m, collection.into_iter().find_map(|elem| u8::try_from(elem).ok()).unwrap()),
                None    => prop_assert!(collection.into_iter().find_map(|elem| u8::try_from(elem).ok()).is_none())
            }
        }

        #[test]
        fn iter_find_map_peeked(collection in any::<Vec<usize>>()) {
            let mut iter = Peekable::new(collection.iter());
            let _ = iter.peek();

            match iter.find_map(|elem| u8::try_from(*elem).ok()) {
                Some(m) => prop_assert_eq!(m, collection.into_iter().find_map(|elem| u8::try_from(elem).ok()).unwrap()),
                None    => prop_assert!(collection.into_iter().find_map(|elem| u8::try_from(elem).ok()).is_none())
            }
        }

        #[test]
        fn iter_find_map_peeked_2(collection in any::<Vec<usize>>()) {
            let mut iter = Peekable::new(collection.iter());
            let _ = iter.peek_2();

            match iter.find_map(|elem| u8::try_from(*elem).ok()) {
                Some(m) => prop_assert_eq!(m, collection.into_iter().find_map(|elem| u8::try_from(elem).ok()).unwrap()),
                None    => prop_assert!(collection.into_iter().find_map(|elem| u8::try_from(elem).ok()).is_none())
            }
        }

        #[test]
        fn iter_last(collection in any::<Vec<usize>>()) {
            match Peekable::new(collection.iter()).last() {
                Some(m) => prop_assert_eq!(m, collection.iter().last().unwrap()),
                None    => prop_assert!(collection.last().is_none())
            }
        }

        #[test]
        fn iter_last_peeked(collection in any::<Vec<usize>>()) {
            let mut iter = Peekable::new(collection.iter());
            let _ = iter.peek();

            match iter.last() {
                Some(m) => prop_assert_eq!(m, collection.iter().last().unwrap()),
                None    => prop_assert!(collection.last().is_none())
            }
        }

        #[test]
        fn iter_last_peeked_2(collection in any::<Vec<usize>>()) {
            let mut iter = Peekable::new(collection.iter());
            let _ = iter.peek_2();

            match iter.last() {
                Some(m) => prop_assert_eq!(m, collection.iter().last().unwrap()),
                None    => prop_assert!(collection.last().is_none())
            }
        } 
    }
}
