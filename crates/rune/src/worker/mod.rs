//! Worker used by compiler.

mod import;
mod task;
mod wildcard_import;

use std::rc::Rc;

use crate::alloc::prelude::*;
use crate::alloc::{self, HashMap, Vec, VecDeque};
use crate::ast::{self, Span};
use crate::compile::{self, ModId};
use crate::indexing::items::Items;
use crate::indexing::{index, index2};
use crate::indexing::{IndexItem, Indexer, Scopes};
use crate::query::{GenericsParameters, Query, Used};
use crate::SourceId;

pub(crate) use self::import::Import;
pub(crate) use self::task::{LoadFileKind, Task};
pub(crate) use self::wildcard_import::WildcardImport;

pub(crate) struct Worker<'a, 'arena> {
    /// Query engine.
    pub(crate) q: Query<'a, 'arena>,
    /// Files that have been loaded.
    pub(crate) loaded: HashMap<ModId, (SourceId, Span)>,
    /// Worker queue.
    pub(crate) queue: VecDeque<Task>,
}

impl<'a, 'arena> Worker<'a, 'arena> {
    /// Construct a new worker.
    pub(crate) fn new(q: Query<'a, 'arena>) -> Self {
        Self {
            q,
            loaded: HashMap::new(),
            queue: VecDeque::new(),
        }
    }

    /// Perform indexing in the worker.
    pub(crate) fn index(&mut self) -> alloc::Result<()> {
        // NB: defer wildcard expansion until all other imports have been
        // indexed.
        let mut wildcard_imports = Vec::new();

        while !self.queue.is_empty() {
            // Prioritise processing the indexing queue. This ensures that files
            // and imports are loaded which might be used by subsequent steps.
            // We only advance wildcard imports and impl items once this is
            // empty.
            //
            // Language semantics also ensures that once this queue is drained,
            // every item which might affect the behavior of imports has been
            // indexed.
            while let Some(task) = self.queue.pop_front() {
                match task {
                    Task::LoadFile {
                        kind,
                        source_id,
                        mod_item,
                        mod_item_id,
                    } => {
                        let result = (|| {
                            let Some(source) = self.q.sources.get(source_id) else {
                                self.q
                                    .diagnostics
                                    .internal(source_id, "Missing queued source by id")?;
                                return Ok(());
                            };

                            let item = self.q.pool.module_item(mod_item);
                            tracing::trace!("Load file: {}", item);

                            let (root, is_module) = match kind {
                                LoadFileKind::Root => {
                                    (source.path().map(|p| p.try_to_owned()).transpose()?, false)
                                }
                                LoadFileKind::Module { root } => (root, true),
                            };

                            let items = Items::new(item)?;

                            macro_rules! indexer {
                                ($tree:expr) => {
                                    Indexer {
                                        q: self.q.borrow(),
                                        root,
                                        source_id,
                                        items,
                                        scopes: Scopes::new()?,
                                        item: IndexItem::new(mod_item, mod_item_id),
                                        nested_item: None,
                                        macro_depth: 0,
                                        loaded: Some(&mut self.loaded),
                                        queue: Some(&mut self.queue),
                                        tree: $tree,
                                    }
                                };
                            }

                            if self.q.options.function_body && !is_module {
                                let ast = crate::parse::parse_all::<ast::EmptyBlock>(
                                    source.as_str(),
                                    source_id,
                                    true,
                                )?;

                                let span = Span::new(0, source.len());
                                let mut idx = indexer!(Rc::default());

                                index::empty_block_fn(&mut idx, ast, &span)?;
                            } else {
                                if self.q.options.v2 {
                                    let tree = crate::grammar::prepare_text(source.as_str())
                                        .with_source_id(source_id)
                                        .parse()?;

                                    let tree = Rc::new(tree);

                                    if self.q.options.print_tree {
                                        let o = std::io::stdout();
                                        let mut o = o.lock();
                                        tree.print_with_source(&mut o, source.as_str())?;
                                    }

                                    let mut idx = indexer!(tree.clone());
                                    tree.parse_all(|p| index2::file(&mut idx, p))?;
                                } else {
                                    let mut ast = crate::parse::parse_all::<ast::File>(
                                        source.as_str(),
                                        source_id,
                                        true,
                                    )?;

                                    let mut idx = indexer!(Rc::default());
                                    index::file(&mut idx, &mut ast)?;
                                }
                            }

                            Ok::<_, compile::Error>(())
                        })();

                        if let Err(error) = result {
                            self.q.diagnostics.error(source_id, error)?;
                        }
                    }
                    Task::ExpandImport(import) => {
                        tracing::trace!("expand import");

                        let source_id = import.source_id;
                        let queue = &mut self.queue;

                        let result = import.process(&mut self.q, &mut |task| {
                            queue.try_push_back(task)?;
                            Ok(())
                        });

                        if let Err(error) = result {
                            self.q.diagnostics.error(source_id, error)?;
                        }
                    }
                    Task::ExpandWildcardImport(wildcard_import) => {
                        tracing::trace!("expand wildcard import");

                        let source_id = wildcard_import.location.source_id;

                        if let Err(error) = wildcard_imports.try_push(wildcard_import) {
                            self.q
                                .diagnostics
                                .error(source_id, compile::Error::from(error))?;
                        }
                    }
                }
            }

            // Process discovered wildcard imports, since they might be used
            // during impl items below.
            for mut wildcard_import in wildcard_imports.drain(..) {
                if let Err(error) = wildcard_import.process_local(&mut self.q) {
                    self.q
                        .diagnostics
                        .error(wildcard_import.location.source_id, error)?;
                }
            }

            // Expand impl items since they might be non-local. We need to look up the metadata associated with the item.
            while let Some(entry) = self.q.next_impl_item_entry() {
                tracing::trace!(item = ?self.q.pool.item(entry.path.id), "next impl item entry");

                let process = || {
                    // We conservatively deny `Self` impl since that is what
                    // Rust does, and at some point in the future we might
                    // introduce bounds which would not be communicated through
                    // `Self`.
                    let named =
                        self.q
                            .convert_path_with(&entry.path, true, Used::Used, Used::Unused)?;

                    if let Some((spanned, _)) = named.parameters.into_iter().flatten().next() {
                        return Err(compile::Error::new(
                            spanned.span(),
                            compile::ErrorKind::UnsupportedGenerics,
                        ));
                    }

                    let meta = self.q.lookup_meta(
                        &entry.location,
                        named.item,
                        GenericsParameters::default(),
                    )?;

                    // TODO: this should not be necessary, since the item being
                    // referenced should already have been inserted at this
                    // point.
                    self.q
                        .inner
                        .items
                        .try_insert(meta.item_meta.item, meta.item_meta)?;

                    let item = self.q.pool.item(meta.item_meta.item);
                    let items = Items::new(item)?;

                    let mut idx = Indexer {
                        q: self.q.borrow(),
                        root: entry.root,
                        source_id: entry.location.source_id,
                        items,
                        scopes: Scopes::new()?,
                        item: IndexItem::with_impl_item(
                            named.module,
                            named.item,
                            meta.item_meta.item,
                        ),
                        nested_item: entry.nested_item,
                        macro_depth: entry.macro_depth,
                        loaded: Some(&mut self.loaded),
                        queue: Some(&mut self.queue),
                        tree: Rc::default(),
                    };

                    for f in entry.functions {
                        index::item_fn(&mut idx, f)?;
                    }

                    Ok::<_, compile::Error>(())
                };

                if let Err(error) = process() {
                    self.q.diagnostics.error(entry.location.source_id, error)?;
                }
            }
        }

        Ok(())
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum ImportKind {
    /// The import is in-place.
    Local,
    /// The import is deferred.
    Global,
}
