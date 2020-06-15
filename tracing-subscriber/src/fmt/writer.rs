//! Abstractions for creating [`io::Write`] instances.
//!
//! [`io::Write`]: https://doc.rust-lang.org/std/io/trait.Write.html
use std::{
    io,
    sync::{Mutex, MutexGuard},
};

/// A type that can create [`io::Write`] instances.
///
/// `MakeWriter` is used by [`fmt::Subscriber`] or [`fmt::Layer`] to print
/// formatted text representations of [`Event`]s.
///
/// This trait is already implemented for function pointers and
/// immutably-borrowing closures that return an instance of [`io::Write`], such
/// as [`io::stdout`] and [`io::stderr`]. Additionally, it is implemented for
/// [`std::sync::Mutex`][mutex] when the tyoe inside the mutex implements
/// [`io::Write`].
///
/// # Examples
///
/// The simplest usage is to pass in a named function that returns a writer. For
/// example, to log all events to stderr, we could write:
/// ```
/// let subscriber = tracing_subscriber::fmt()
///     .with_writer(std::io::stderr)
///     .finish();
/// # drop(subscriber);
/// ```
///
/// Any function that returns a writer can be used:
///
/// ```
/// fn make_my_great_writer() -> impl std::io::Write {
///     // ...
///     # std::io::stdout()
/// }
///
/// let subscriber = tracing_subscriber::fmt()
///     .with_writer(make_my_great_writer)
///     .finish();
/// # drop(subscriber);
/// ```
///
/// A closure can be used to introduce arbitrary logic into how the writer is
/// created. For example, this will send every 5th event to stderr, and all
/// other events to stdout (why you would actually want to do this, I have no
/// idea, but you _can_):
///
/// ```
/// use std::io;
/// use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};
///
/// let n = AtomicUsize::new(0);
/// let subscriber = tracing_subscriber::fmt()
///     .with_writer(move || -> Box<dyn io::Write> {
///         if n.fetch_add(1, Relaxed) % 5 == 0 {
///             Box::new(io::stderr())
///         } else {
///             Box::new(io::stdout())
///        }
///     })
///     .finish();
/// # drop(subscriber);
/// ```
///
/// A single instance of a type implementing [`io::Write`] may be used as a
/// `MakeWriter` by wrapping it in a [`Mutex`][mutex]. For example, we could
/// write to a file like so:
///
/// ```
/// use std::{fs::File, sync::Mutex};
///
/// # fn docs() -> Result<(), Box<dyn std::error::Error>> {
/// let log_file = File::create("my_cool_trace.log")?;
/// let subscriber = tracing_subscriber::fmt()
///     .with_writer(Mutex::new(log_file))
///     .finish();
/// # drop(subscriber);
/// # Ok(())
/// # }
/// ```
///
/// [`io::Write`]: https://doc.rust-lang.org/std/io/trait.Write.html
/// [`fmt::Subscriber`]: ../../fmt/struct.Subscriber.html
/// [`fmt::Layer`]: ../../fmt/struct.Layer.html
/// [`Event`]: https://docs.rs/tracing-core/0.1.5/tracing_core/event/struct.Event.html
/// [`io::stdout`]: https://doc.rust-lang.org/std/io/fn.stdout.html
/// [`io::stderr`]: https://doc.rust-lang.org/std/io/fn.stderr.html
/// [mutex]: https://doc.rust-lang.org/std/sync/struct.Mutex.html
pub trait MakeWriter<'a> {
    /// The concrete [`io::Write`] implementation returned by [`make_writer`].
    ///
    /// [`io::Write`]: https://doc.rust-lang.org/std/io/trait.Write.html
    /// [`make_writer`]: #tymethod.make_writer
    type Writer: io::Write;

    /// Returns an instance of [`Writer`].
    ///
    /// # Implementer notes
    ///
    /// [`fmt::Layer`] or [`fmt::Subscriber`] will call this method each time an event is recorded. Ensure any state
    /// that must be saved across writes is not lost when the [`Writer`] instance is dropped. If
    /// creating a [`io::Write`] instance is expensive, be sure to cache it when implementing
    /// [`MakeWriter`] to improve performance.
    ///
    /// [`Writer`]: #associatedtype.Writer
    /// [`fmt::Layer`]: ../../fmt/struct.Layer.html
    /// [`fmt::Subscriber`]: ../../fmt/struct.Subscriber.html
    /// [`io::Write`]: https://doc.rust-lang.org/std/io/trait.Write.html
    /// [`MakeWriter`]: trait.MakeWriter.html
    fn make_writer(&'a self) -> Self::Writer;
}

/// A type implementing [`io::Write`] for a [`MutexGuard`] where tyhe type
/// inside the [`Mutex`] implements [`io::Write`].
///
/// This is used by the [`MakeWriter`] implementation for [`Mutex`], because
/// [`MutexGuard`] itself will not implement [`io::Write`] — instead, it
/// _dereferences_ to a type implementing [`io::Write`]. Because [`MakeWriter`]
/// requires the `Writer` type to implement [`io::Write`], it's necessary to add
/// a newtype that forwards the trait implementation.
///
/// [`io::Write`]: https://doc.rust-lang.org/std/io/trait.Write.html
/// [`MutexGuard`]: https://doc.rust-lang.org/std/sync/struct.MutexGuard.html
/// [`Mutex`]: https://doc.rust-lang.org/std/sync/struct.Mutex.html
/// [`MakeWriter`]: trait.MakeWriter.html
#[derive(Debug)]
pub struct MutexGuardWriter<'a, W>(MutexGuard<'a, W>);

impl<'a, F, W> MakeWriter<'a> for F
where
    F: Fn() -> W,
    W: io::Write,
{
    type Writer = W;

    fn make_writer(&'a self) -> Self::Writer {
        (self)()
    }
}

impl<'a, W> MakeWriter<'a> for Mutex<W>
where
    W: io::Write + 'a,
{
    type Writer = MutexGuardWriter<'a, W>;

    fn make_writer(&'a self) -> Self::Writer {
        MutexGuardWriter(self.lock().expect("lock poisoned"))
    }
}

impl<'a, W> io::Write for MutexGuardWriter<'a, W>
where
    W: io::Write,
{
    #[inline]
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.0.write(buf)
    }

    #[inline]
    fn flush(&mut self) -> io::Result<()> {
        self.0.flush()
    }

    #[inline]
    fn write_vectored(&mut self, bufs: &[io::IoSlice<'_>]) -> io::Result<usize> {
        self.0.write_vectored(bufs)
    }

    #[inline]
    fn write_all(&mut self, buf: &[u8]) -> io::Result<()> {
        self.0.write_all(buf)
    }

    #[inline]
    fn write_fmt(&mut self, fmt: std::fmt::Arguments<'_>) -> io::Result<()> {
        self.0.write_fmt(fmt)
    }
}

#[cfg(test)]
mod test {
    use super::MakeWriter;
    use crate::fmt::format::Format;
    use crate::fmt::test::{MockMakeWriter, MockWriter};
    use crate::fmt::Subscriber;
    use std::sync::{Arc, Mutex};
    use tracing::error;
    use tracing_core::dispatcher::{self, Dispatch};

    fn test_writer<T>(make_writer: T, msg: &str, buf: &Mutex<Vec<u8>>)
    where
        T: for<'writer> MakeWriter<'writer> + Send + Sync + 'static,
    {
        let subscriber = {
            #[cfg(feature = "ansi")]
            {
                let f = Format::default().without_time().with_ansi(false);
                Subscriber::builder()
                    .event_format(f)
                    .with_writer(make_writer)
                    .finish()
            }
            #[cfg(not(feature = "ansi"))]
            {
                let f = Format::default().without_time();
                Subscriber::builder()
                    .event_format(f)
                    .with_writer(make_writer)
                    .finish()
            }
        };
        let dispatch = Dispatch::from(subscriber);

        dispatcher::with_default(&dispatch, || {
            error!("{}", msg);
        });

        let expected = format!("ERROR {}: {}\n", module_path!(), msg);
        let actual = String::from_utf8(buf.try_lock().unwrap().to_vec()).unwrap();
        assert!(actual.contains(expected.as_str()));
    }

    #[test]
    fn custom_writer_closure() {
        let buf = Arc::new(Mutex::new(Vec::new()));
        let buf2 = buf.clone();
        let make_writer = move || MockWriter::new(buf2.clone());
        let msg = "my custom writer closure error";
        test_writer(make_writer, msg, &buf);
    }

    #[test]
    fn custom_writer_struct() {
        let buf = Arc::new(Mutex::new(Vec::new()));
        let make_writer = MockMakeWriter::new(buf.clone());
        let msg = "my custom writer struct error";
        test_writer(make_writer, msg, &buf);
    }

    #[test]
    fn custom_writer_mutex() {
        let buf = Arc::new(Mutex::new(Vec::new()));
        let writer = MockWriter::new(buf.clone());
        let make_writer = Mutex::new(writer);
        let msg = "my mutex writer error";
        test_writer(make_writer, msg, &buf);
    }
}
