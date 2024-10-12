//! Helper types for a holder of data.

use core::any::TypeId;
use core::fmt;
use core::mem::ManuallyDrop;
use core::ptr;

use crate::alloc::alloc::Global;
use crate::alloc::{self, Box};
use crate::any::Any;
use crate::compile::meta;
use crate::hash::Hash;
use crate::runtime::{AnyTypeInfo, MaybeTypeOf, RawStr, TypeInfo};

/// Errors raised during casting operations.
#[derive(Debug, PartialEq)]
#[allow(missing_docs)]
#[non_exhaustive]
pub(crate) enum AnyObjError {
    RefAsMut { name: RawStr },
    Cast,
}

impl fmt::Display for AnyObjError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            AnyObjError::RefAsMut { name } => write!(
                f,
                "Cannot borrow a shared reference `&{name}` mutably as `&mut {name}`",
            ),
            AnyObjError::Cast {} => write!(f, "Cast failed"),
        }
    }
}

impl core::error::Error for AnyObjError {}

/// Our own private dynamic Any implementation.
///
/// In contrast to `Box<dyn std::any::Any>`, this allows for storing a raw
/// pointer directly in the object to avoid one level of indirection. Otherwise
/// it's equivalent.
#[repr(C)]
pub struct AnyObj {
    vtable: &'static Vtable,
    data: ptr::NonNull<()>,
}

impl fmt::Debug for AnyObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.debug(f)
    }
}

impl AnyObj {
    /// Construct a new any from the original any.
    pub(crate) fn new<T>(data: T) -> alloc::Result<Self>
    where
        T: Any,
    {
        let data = unsafe {
            let (ptr, Global) = Box::into_raw_with_allocator(Box::try_new_in(data, Global)?);
            ptr::NonNull::new_unchecked(ptr.cast())
        };

        Ok(Self {
            vtable: &Vtable {
                drop: drop_impl::<T>,
                as_ptr: as_ptr_impl::<T>,
                debug: debug_impl::<T>,
                type_name: type_name_impl::<T>,
                type_hash: type_hash_impl::<T>,
            },
            data,
        })
    }

    /// Returns stored value if it is of type `T`, or `None` if it isn't.
    ///
    /// # Examples
    ///
    /// ```
    /// use rune::Any;
    /// use rune::runtime::AnyObj;
    ///
    /// #[derive(Debug, PartialEq, Eq, Any)]
    /// struct Thing(u32);
    ///
    /// let any = AnyObj::new(Thing(1u32))?;
    ///
    /// let Ok(thing) = any.downcast::<Thing>() else {
    ///     panic!("Conversion failed");
    /// };
    ///
    /// assert_eq!(thing, Thing(1));
    /// # Ok::<_, rune::support::Error>(())
    /// ```
    #[inline]
    pub(crate) fn downcast<T>(self) -> Result<T, (AnyObjError, Self)>
    where
        T: Any,
    {
        let this = ManuallyDrop::new(self);

        unsafe {
            let Some(ptr) = (this.vtable.as_ptr)(this.data.as_ptr(), TypeId::of::<T>()) else {
                let this = ManuallyDrop::into_inner(this);
                return Err((AnyObjError::Cast, this));
            };

            Ok(Box::into_inner(Box::from_raw_in(
                ptr.cast_mut().cast(),
                rune_alloc::alloc::Global,
            )))
        }
    }

    /// Returns some reference to the boxed value if it is of type `T`, or
    /// `None` if it isn't.
    ///
    /// # Examples
    ///
    /// ```
    /// use rune::Any;
    /// use rune::runtime::{AnyObj, AnyObjError};
    ///
    /// #[derive(Debug, PartialEq, Eq, Any)]
    /// struct Thing(u32);
    ///
    /// #[derive(Debug, PartialEq, Eq, Any)]
    /// struct Other;
    ///
    /// let any = AnyObj::new(Thing(1u32))?;
    /// assert_eq!(Ok(&Thing(1u32)), any.downcast_borrow_ref::<Thing>());
    /// assert_eq!(Err(AnyObjError::Cast), any.downcast_borrow_ref::<Other>());
    /// # Ok::<_, rune::support::Error>(())
    /// ```
    #[inline]
    pub(crate) fn downcast_borrow_ref<T>(&self) -> Result<&T, AnyObjError>
    where
        T: Any,
    {
        unsafe {
            let Some(ptr) = (self.vtable.as_ptr)(self.data.as_ptr(), TypeId::of::<T>()) else {
                return Err(AnyObjError::Cast);
            };

            Ok(&*ptr.cast())
        }
    }

    /// Returns some mutable reference to the boxed value if it is of type `T`, or
    /// `None` if it isn't.
    ///
    /// # Examples
    ///
    /// ```
    /// use rune::Any;
    /// use rune::runtime::AnyObj;
    ///
    /// #[derive(Debug, PartialEq, Eq, Any)]
    /// struct Thing(u32);
    ///
    /// let mut any = AnyObj::new(Thing(1u32))?;
    /// any.downcast_borrow_mut::<Thing>().unwrap().0 = 2;
    /// assert_eq!(Ok(&Thing(2u32)), any.downcast_borrow_ref::<Thing>());
    /// # Ok::<_, rune::support::Error>(())
    /// ```
    #[inline]
    pub(crate) fn downcast_borrow_mut<T>(&mut self) -> Result<&mut T, AnyObjError>
    where
        T: Any,
    {
        unsafe {
            let Some(ptr) = (self.vtable.as_ptr)(self.data.as_ptr(), TypeId::of::<T>()) else {
                return Err(AnyObjError::Cast);
            };

            Ok(&mut *ptr.cast_mut().cast())
        }
    }

    /// Debug format the current any type.
    pub(crate) fn debug(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (self.vtable.debug)(f)
    }

    /// Access the underlying type name for the data.
    pub(crate) fn type_name(&self) -> RawStr {
        (self.vtable.type_name)()
    }

    /// Access the underlying type id for the data.
    pub(crate) fn type_hash(&self) -> Hash {
        (self.vtable.type_hash)()
    }

    /// Access full type info for type.
    pub(crate) fn type_info(&self) -> TypeInfo {
        TypeInfo::Any(AnyTypeInfo::__private_new(
            (self.vtable.type_name)(),
            (self.vtable.type_hash)(),
        ))
    }
}

impl MaybeTypeOf for AnyObj {
    #[inline]
    fn maybe_type_of() -> alloc::Result<meta::DocType> {
        Ok(meta::DocType::empty())
    }
}

impl Drop for AnyObj {
    fn drop(&mut self) {
        // Safety: The safety of the called implementation is guaranteed at
        // compile time.
        unsafe {
            (self.vtable.drop)(self.data.as_ptr());
        }
    }
}

/// The signature of a drop function.
type DropFn = unsafe fn(*mut ());

/// The signature of a pointer coercion function.
type AsPtrFn = unsafe fn(this: *const (), expected: TypeId) -> Option<*const ()>;

/// The signature of a descriptive type name function.
type DebugFn = fn(&mut fmt::Formatter<'_>) -> fmt::Result;

/// Get the type name.
type TypeNameFn = fn() -> RawStr;

/// The signature of a type hash function.
type TypeHashFn = fn() -> Hash;

/// The vtable for any type stored in the virtual machine.
///
/// This can be implemented manually assuming it obeys the constraints of the
/// type. Otherwise we rely _heavily_ on the invariants provided by
/// `std::any::Any` which are checked at construction-time for this type.
struct Vtable {
    /// The underlying drop implementation for the stored type.
    drop: DropFn,
    /// Punt the inner pointer to the type corresponding to the type hash.
    as_ptr: AsPtrFn,
    /// Type information for diagnostics.
    debug: DebugFn,
    /// Type name accessor.
    type_name: TypeNameFn,
    /// Get the type hash of the stored type.
    type_hash: TypeHashFn,
}

unsafe fn drop_impl<T>(this: *mut ()) {
    drop(Box::from_raw_in(this as *mut T, Global));
}

fn as_ptr_impl<T>(this: *const (), expected: TypeId) -> Option<*const ()>
where
    T: Any,
{
    if expected == TypeId::of::<T>() {
        Some(this)
    } else {
        None
    }
}

fn debug_impl<T>(f: &mut fmt::Formatter<'_>) -> fmt::Result
where
    T: Any,
{
    write!(f, "{}", T::BASE_NAME)
}

fn type_name_impl<T>() -> RawStr
where
    T: ?Sized + Any,
{
    T::BASE_NAME
}

fn type_hash_impl<T>() -> Hash
where
    T: ?Sized + Any,
{
    T::type_hash()
}
