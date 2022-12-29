// SPDX-License-Identifier: GPL-2.0

//! TTYs and TTY line disciplines
//!
//! C headers: [`include/linux/tty.h`](../../../../include/linux/tty.h) and
//! [`include/linux/tty_ldisc.h`](../../../../include/linux/tty_ldisc.h)

use crate::{
    bindings,
    error::{code::*, from_kernel_result, Result},
    str::{CStr, CString},
    to_result,
    types::{AlwaysRefCounted, PointerWrapper},
};
use alloc::boxed::Box;
use core::{cell::UnsafeCell, fmt, marker::PhantomData, mem, pin::Pin, ptr};
use macros::vtable;

/// Wraps the kernel's `struct tty_struct`.
///
/// # Invariants
///
/// Instances of this type are always ref-counted, that is, a call to `tty_kref_get` ensures
/// that the allocation remains valid at least until the matching call to `tty_kref_put`.
// TODO: Split this, with the related tty_struct bindings, to a separate file.
// TODO: Expand binding support for `tty_struct`
#[repr(transparent)]
pub struct Tty(pub(crate) UnsafeCell<bindings::tty_struct>);

// TODO: Accessing fields of `struct tty_struct` through the pointer is UB because other threads may be
// writing to them. However, this is how the C code currently operates: naked reads and writes to
// fields. Even if we used relaxed atomics on the Rust side, we can't force this on the C side.
impl Tty {
    /// Creates a reference to a [`Tty`] from a valid pointer.
    ///
    /// # Safety
    ///
    /// The caller must ensure that `ptr` is valid and remains valid for the lifetime of the
    /// returned [`Tty`] instance.
    pub(crate) unsafe fn from_ptr<'a>(ptr: *const bindings::tty_struct) -> &'a Self {
        // SAFETY: The safety requirements guarantee the validity of the dereference, while the
        // `Tty` type being transparent makes the cast ok.
        unsafe { &*ptr.cast() }
    }

    /// Creates a mutable reference to a [`Tty`] from a valid pointer.
    ///
    /// # Safety
    ///
    /// The caller must ensure that `ptr` is valid and remains valid for the lifetime of the
    /// returned [`Tty`] instance. The caller must also ensure the `tty_struct` is locked and can
    /// be safely written to.
    pub(crate) unsafe fn from_ptr_locked<'a>(ptr: *mut bindings::tty_struct) -> &'a mut Self {
        // SAFETY: The safety requirements guarantee the validity of the dereference, while the
        // `Tty` type being transparent makes the cast ok. Holding the lock ensures the mutability
        // safety.
        unsafe { &mut *ptr.cast() }
    }

    /// Gets the value of the the tty_struct->name field.
    pub fn get_name(&self) -> Result<&CStr> {
        // SAFETY: By the type invariants, it's ok to dereference `self.0`.
        let tty = unsafe { &*self.0.get() };
        // SAFETY: Convert `[i8; 64]` to `&[u8]`.
        let name = unsafe { &*(&tty.name as *const [i8] as *const [u8]) };
        if let Some(idx) = name.iter().position(|&c| c == b'\0') {
            Ok(CStr::from_bytes_with_nul_unwrap(&name[..=idx]))
        } else {
            Err(EINVAL)
        }
    }

    /// Sets the value of the the tty_struct->receive_room field.
    pub fn set_receive_room(&mut self, bytes: u32) {
        // SAFETY: By the type invariants for `Tty` and `LockedTty, it's ok to dereference `self.0`
        // as mut.
        let tty = unsafe { &mut *self.0.get() };
        tty.receive_room = bytes
    }
}

// SAFETY: The type invariants guarantee that `Tty` is always ref-counted.
unsafe impl AlwaysRefCounted for Tty {
    fn inc_ref(&self) {
        // SAFETY: The existence of a shared reference means that the refcount is nonzero.
        // `tty_kref_get` is inlined, so manually inc tty_struct->kref.
        unsafe {
            let tty = &mut *self.0.get();
            bindings::refcount_inc(&mut tty.kref.refcount);
        }
    }

    unsafe fn dec_ref(obj: ptr::NonNull<Self>) {
        // SAFETY: The safety requirements guarantee that the refcount is nonzero.
        unsafe { bindings::tty_kref_put(obj.cast().as_ptr()) }
    }
}

/// Registration structure for a line discipline
pub struct Registration<T: Operations> {
    ldisc: UnsafeCell<bindings::tty_ldisc_ops>,
    registered: bool,
    _p: PhantomData<T>,
}

impl<T: Operations> Registration<T> {
    /// Creates new instance of registration.
    ///
    /// The data must be registered.
    pub fn new() -> Self {
        Self {
            ldisc: UnsafeCell::new(bindings::tty_ldisc_ops::default()),
            registered: false,
            _p: PhantomData,
        }
    }

    /// Returns a registered and pinned, heap-allocated representation of the registration.
    pub fn new_pinned(
        module: &'static crate::ThisModule,
        name: fmt::Arguments<'_>,
        num: i32,
    ) -> Result<Pin<Box<Self>>> {
        let mut reg = Pin::from(Box::try_new(Self::new())?);
        reg.as_mut().register(module, name, num)?;
        Ok(reg)
    }

    /// Registers a line discipline within the rest of the kernel.
    ///
    /// It must be pinned because the memory block that represents
    /// the registration may be self-referential.
    pub fn register(
        self: Pin<&mut Self>,
        module: &'static crate::ThisModule,
        name: fmt::Arguments<'_>,
        num: i32,
    ) -> Result {
        // SAFETY: We never move out of `this`.
        let this = unsafe { self.get_unchecked_mut() };

        if this.registered {
            return Err(EINVAL);
        }

        let name = CString::try_from_fmt(name)?;

        // SAFETY: Registration is pinned and contains allocated and set to zero
        // `bindings:tty_ldisc_ops` structure.
        Self::init_ldisc_ops(unsafe { &mut *this.ldisc.get() }, module, &name, num);

        // SAFETY: `bindings::tty_ldisc_ops` is initialized above which guarantees safety.
        to_result(unsafe { bindings::tty_register_ldisc(&mut *this.ldisc.get()) })?;

        this.registered = true;
        Ok(())
    }

    fn init_ldisc_ops(
        ldisc: &mut bindings::tty_ldisc_ops,
        module: &'static crate::ThisModule,
        name: &CString,
        num: i32,
    ) {
        ldisc.name = name.as_char_ptr() as *mut _;
        ldisc.owner = module.0;
        ldisc.num = num;

        ldisc.open = Some(Self::open_callback);
        ldisc.close = Some(Self::close_callback);
        ldisc.receive_buf = if T::HAS_RECEIVE_BUF {
            Some(Self::receive_buf_callback)
        } else {
            None
        }

        // SAFETY: All fields are properly initialized as remaining fields are already zeroed by
        // `bindings::tty_ldisc_ops::default()` call.
    }

    unsafe extern "C" fn open_callback(tty: *mut bindings::tty_struct) -> core::ffi::c_int {
        from_kernel_result! {
            // SAFETY: The C contract guarantees that `tty` is valid. Additionally, the created
            // reference never outlives this function, so it is guaranteed to be valid.
            // Additionally, the tty should be locked by the caller (which it is in the
            // default kernel C path that leads here).
            let ptr = T::open(unsafe { Tty::from_ptr_locked(tty) })?.into_pointer();
            // SAFETY: The C contract guarantees that `disc_data` is available
            // for the line discipline associated with the tty, so we know that there are no
            // concurrent threads/CPUs accessing it (it's not visible to any other Rust code).
            unsafe { (*tty).disc_data = ptr as *mut core::ffi::c_void };
            Ok(0)
        }
    }

    unsafe extern "C" fn close_callback(tty: *mut bindings::tty_struct) {
        // SAFETY: `disc_data` was initialised by `open_callback` with a value returned by
        // `T::LdiscData::into_pointer`.
        let ptr = mem::replace(unsafe { &mut (*tty).disc_data }, ptr::null_mut());
        // SAFETY: The C contract guarantees that `tty` is valid. Additionally, created reference
        // never outlives this function, so it is guaranteed to be valid.
        T::close(unsafe { T::LdiscData::from_pointer(ptr as _) }, unsafe {
            Tty::from_ptr(tty)
        });
    }

    unsafe extern "C" fn receive_buf_callback(
        tty: *mut bindings::tty_struct,
        cp: *const core::ffi::c_uchar,
        fp: *const core::ffi::c_char,
        count: core::ffi::c_int,
    ) {
        // SAFETY: Call to unsafe from_raw_parts(). Safety based on C API guarantees, that `cp` and
        // `fp` are non-null and at least count bytes in size.
        let cp = unsafe { &*ptr::slice_from_raw_parts(cp, count as usize) };
        let fp = unsafe { &*ptr::slice_from_raw_parts(fp, count as usize) };
        // SAFETY: `disc_data` was initialised by `open_callback` with a value returned by
        // `T::LdiscData::into_pointer`. `T::LdiscData::from_pointer` is only called by the
        // `close` callback, which can't be called while this function is running.
        let data = unsafe { T::LdiscData::borrow((*tty).disc_data) };
        // SAFETY: The C contract guarantees that `tty` is valid. Additionally, created reference
        // never outlives this function, so it is guaranteed to be valid.
        T::receive_buf(data, unsafe { Tty::from_ptr(tty) as _ }, cp, fp)
    }
}

impl<T: Operations> Default for Registration<T> {
    fn default() -> Self {
        Self::new()
    }
}

// SAFETY: The only method is `register()`, which requires a (pinned) mutable `Registration`, so it
// is safe to pass `&Registration` to multiple threads because it offers no interior mutability.
unsafe impl<T: Operations> Sync for Registration<T> {}

// SAFETY: All functions work from any thread.
#[allow(clippy::non_send_fields_in_send_ty)]
unsafe impl<T: Operations> Send for Registration<T> {}

impl<T: Operations> Drop for Registration<T> {
    /// Removes the registration from the kernel if it has completed successfully before.
    fn drop(&mut self) {
        // SAFETY: The instance of Registration<T> is unregistered only
        // after being initialized and registered before.
        if self.registered {
            unsafe { bindings::tty_unregister_ldisc(self.ldisc.get()) };
        }
    }
}

/// Corresponds to the kernel's `struct tty_ldisc_ops`.
///
/// You implement this trait whenever you would create a `struct tty_ldisc_ops`.
///
/// ldiscs may be used from multiple threads/processes concurrently, so your type must be
/// [`Sync`]. It must also be [`Send`] because [`Operations::close`] will be called from the
/// thread that closes or changes the line discipline.
#[vtable]
pub trait Operations {
    /// The type of the context data set by [`Operations::open`] and made
    /// available to other methods.
    type LdiscData: PointerWrapper + Send + Sync = ();

    /// Corresponds to the `open` function pointer in `struct tty_ldisc_ops`.
    fn open(_tty: &mut Tty) -> Result<Self::LdiscData> {
        Err(EINVAL)
    }

    /// Corresponds to the `close` function pointer in `struct tty_ldisc_ops`.
    fn close(_data: Self::LdiscData, _tty: &Tty) {}

    /// Corresponds to the `receive_buf` function pointer in `struct tty_ldisc_ops`.
    fn receive_buf(
        _data: <Self::LdiscData as PointerWrapper>::Borrowed<'_>,
        _tty: &Tty,
        _cp: &[u8],
        _fp: &[i8],
    ) {
    }
}
