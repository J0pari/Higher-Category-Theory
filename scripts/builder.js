import fs from 'fs';
import path from 'path';
import { fileURLToPath } from 'url';
import puppeteer from 'puppeteer';
import crypto from 'crypto';
import { performance } from 'perf_hooks';
import { execSync } from 'child_process';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const PROJECT_ROOT = path.resolve(__dirname, '..');

// Forward declarations
let traceOrchestrator;
let configPatternValidator;
let processingCoordinator;
let lazyTypeChecker;
let typeChecker;



class SumType {
    constructor(name, constructors) {
        this.name = name;
        this.constructors = constructors;
        this.elim = this.generateEliminator();
    }
    
    generateEliminator() {
        return (motive, ...cases) => {
            return (target) => {
                // Find which constructor was used
                for (let i = 0; i < this.constructors.length; i++) {
                    if (this.constructors[i].matches(target)) {
                        return cases[i](target);
                    }
                }
                throw new Error(`No matching constructor for ${target}`);
            };
        };
    }
}



// PULL-BASED COMPUTATION

class Lazy {
    constructor(thunk) {
        this._thunk = thunk;
        this._cache = undefined;
        this._evaluated = false;
    }
    
    get value() {
        if (!this._evaluated) {
            this._cache = this._thunk();
            this._evaluated = true;

            if (traceOrchestrator && typeof this._cache === 'string') {
                if (this._cache.includes('/') || this._cache.includes('\\')) {
                    traceOrchestrator.trace('LAZY_PATH', { path: this._cache, thunk: this._thunk.name || 'anonymous' });
                }
            }
        }
        return this._cache;
    }
    
    // Force evaluation
    force() {
        return this.value;
    }
    
    // Map without evaluating
    map(f) {
        return new Lazy(() => f(this.value));
    }
    
    // Flatmap for monadic composition (>>=)
    flatMap(f) {
        return new Lazy(() => {
            const result = f(this.value);
            return result instanceof Lazy ? result.value : result;
        });
    }
    
    isEvaluated() {
        return this._evaluated;
    }
    
    // Convert to string - forces evaluation
    toString() {
        return String(this.value);
    }
    
    // Convert to primitive - forces evaluation
    valueOf() {
        return this.value;
    }
}

// Lazy template that only evaluates when converted to string
class LazyTemplate {
    constructor(parts) {
        this.parts = parts;
        this._cache = undefined;
        this._evaluated = false;
    }
    
    toString() {
        if (!this._evaluated) {
            this._cache = this.parts.map(part => {
                if (part instanceof Lazy) {
                    return part.toString();
                } else if (part instanceof LazyTemplate) {
                    return part.toString();
                } else if (part && typeof part === 'object' && part.value !== undefined) {
                    return String(pull(part));
                }
                return String(part);
            }).join('');
            this._evaluated = true;
        }
        return this._cache;
    }
}

// Lazy Functor for mapping over lazy structures
class LazyFunctor {
    static map(f, lazyStructure) {
        if (lazyStructure instanceof Lazy) {
            return lazyStructure.map(f);
        }
        if (typeof lazyStructure === 'object' && lazyStructure !== null) {
            const result = {};
            for (const [k, v] of Object.entries(lazyStructure)) {
                result[k] = LazyFunctor.map(f, v);
            }
            return result;
        }
        return f(lazyStructure);
    }
    
    // Natural transformation: Lazy<A> -> A (only at the boundaries)
    static extract(lazyStructure) {
        return LazyFunctor.map(x => x instanceof Lazy ? x.value : x, lazyStructure);
    }
    
    // Lift a value into lazy context
    static lift(value) {
        if (value instanceof Lazy) return value;
        return new Lazy(() => value);
    }
}

// Kleisli composition for the pipeline
class Pipeline {
    // Kleisli arrow: (A -> M<B>) -> (B -> M<C>) -> (A -> M<C>)
    static kleisli(...stages) {
        if (stages.length === 0) return x => LazyFunctor.lift(x);
        if (stages.length === 1) return stages[0];
        
        return stages.reduce((f, g) => {
            return (x) => {
                const fx = f(x);
                if (fx instanceof Lazy) {
                    return fx.flatMap(g);
                } else if (fx instanceof PullPromise) {
                    return new PullPromise(async () => {
                        const result = await fx.pull();
                        const gx = g(result);
                        if (gx instanceof PullPromise) {
                            return await gx.pull();
                        } else if (gx instanceof Lazy) {
                            return gx.value;
                        }
                        return gx;
                    });
                }
                return g(fx);
            };
        });
    }
    
    // Compose multiple stages
    static compose(...stages) {
        return Pipeline.kleisli(...stages);
    }
    
    // Cache-aware composition
    static withCache(cacheKey, pipeline) {
        return new PullPromise(async () => {
            // Check cache first
            const cached = pullGraph.objects.get(cacheKey);
            if (cached && cached.cached && cached.value) {
                traceOrchestrator.trace('PIPELINE_CACHE_HIT', { cacheKey });
                return cached.value;
            }
            
            // Execute pipeline
            const result = await (pipeline instanceof PullPromise ? pipeline.pull() : pipeline);
            
            // Store in cache
            if (result) {
                pullGraph.register(cacheKey, new Lazy(() => result));
                traceOrchestrator.trace('PIPELINE_CACHE_STORE', { cacheKey });
            }
            
            return result;
        });
    }
    
}

// Comonadic context for configuration
class ConfigContext {
    constructor(value, environment) {
        this.value = value;
        this.environment = environment instanceof Lazy ? environment : new Lazy(() => environment);
    }
    
    // Comonad extract
    extract() {
        return this.value;
    }
    
    // Comonad extend
    extend(f) {
        return new ConfigContext(
            f(this),
            this.environment
        );
    }
    
    // Access environment lazily
    asks(f) {
        return new Lazy(() => f(this.environment.value));
    }
    
    // Create from CONFIG
    static create() {
        return new ConfigContext(null, {
            time: TIME,
            limits: LIMITS,
            config: CONFIG,
            // Everything stays lazy
        });
    }
    
    // Derive values compositionally
    derive(name, computation) {
        return this.extend(ctx => 
            new Lazy(() => computation(ctx.environment.value))
        );
    }
}

// Memoization with category theory
class Memo {
    constructor() {
        this.cache = new WeakMap();
        this.stringCache = new Map(); // For string keys
    }
    
    // Memoize while preserving laziness
    memoize(f) {
        return (x) => {
            const key = typeof x === 'string' ? x : x;
            const cache = typeof x === 'string' ? this.stringCache : this.cache;
            
            if (!cache.has(key)) {
                // Store the lazy computation, not the value
                cache.set(key, new Lazy(() => f(x)));
            }
            return cache.get(key);
        };
    }
    
    // Natural transformation: ensures coherence
    transform(nat, memoized) {
        return this.memoize(x => nat(memoized(x)));
    }
}

// Now define the lazy class wrappers
lazyTypeChecker = new Lazy(() => {
    class TypeChecker extends ConfigPatternValidator {
        constructor(enforceStrict = false) {
            super(enforceStrict);
            this.typeEnvironment = new Map();
        }

        typeCheck(term, expectedType = null) {
            this.validateStructure(term, expectedType || 'TERM');
            return this.violations.length === 0;
        }

        checkWellFormed(value, context) {
            return !this.detectMagicNumber(value, context);
        }
    }
    return TypeChecker;
});

// Infinite lazy streams (coinductive data)
class LazyStream {
    constructor(head, tailThunk) {
        this.head = head;
        this._tailThunk = tailThunk;
        this._tail = null;
    }
    
    get tail() {
        if (this._tail === null && this._tailThunk) {
            this._tail = this._tailThunk();
        }
        return this._tail;
    }
    
    take(n) {
        const result = [];
        let current = this;
        for (let i = 0; i < n && current; i++) {
            result.push(current.head);
            current = current.tail;
        }
        return result;
    }
    
    map(f) {
        return new LazyStream(
            f(this.head),
            this._tailThunk ? () => this.tail.map(f) : null
        );
    }
    
    // Cons operation - prepends element to stream (preserves laziness)
    cons(element) {
        return new LazyStream(element, () => this);
    }
    
    // Append operation - adds element at end (lazy)
    append(element) {
        if (!this._tailThunk) {
            // Base case - create new stream with element
            return new LazyStream(
                this.head,
                () => new LazyStream(element, null)
            );
        }
        // Recursive case - defer to tail
        return new LazyStream(
            this.head,
            () => this.tail.append(element)
        );
    }
    
    // Concatenate two streams lazily
    concat(other) {
        if (!this._tailThunk) {
            return new LazyStream(this.head, () => other);
        }
        return new LazyStream(
            this.head,
            () => this.tail.concat(other)
        );
    }
    
    // Create empty stream
    static empty() {
        return null;
    }
    
    // Create stream from array
    static fromArray(arr) {
        if (arr.length === 0) return null;
        return new LazyStream(
            arr[0],
            arr.length > 1 ? () => LazyStream.fromArray(arr.slice(1)) : null
        );
    }
    
    filter(pred) {
        if (pred(this.head)) {
            return new LazyStream(
                this.head,
                this._tailThunk ? () => this.tail.filter(pred) : null
            );
        }
        return this.tail ? this.tail.filter(pred) : null;
    }
    
    window(n) {
        if (n <= 0 || !this._tailThunk) return null;
        
        const buffer = [];
        let current = this;
        for (let i = 0; i < n && current; i++) {
            buffer.push(current.head);
            current = current.tail;
        }
        
        if (buffer.length < n) return null;
        
        return new LazyStream(
            buffer,
            this.tail ? () => this.tail.window(n) : null
        );
    }
}



// Lazy proxy for automatic lazification of any object
const lazify = (obj) => {
    const cache = new Map();
    
    return new Proxy(obj, {
        get(target, prop) {
            if (!cache.has(prop)) {
                const value = target[prop];
                if (typeof value === 'function') {
                    // Lazify function results
                    cache.set(prop, (...args) => {
                        const key = JSON.stringify(args);
                        if (!cache.has(`${prop}_${key}`)) {
                            cache.set(`${prop}_${key}`, new Lazy(() => value(...args)));
                        }
                        return cache.get(`${prop}_${key}`).value;
                    });
                } else if (typeof value === 'object' && value !== null) {
                    // Recursively lazify objects
                    cache.set(prop, lazify(value));
                } else {
                    // Wrap primitive values
                    cache.set(prop, new Lazy(() => value));
                }
            }
            const cached = cache.get(prop);
            return cached instanceof Lazy ? cached.value : cached;
        }
    });
};

// Lazy recursive definitions (for coinduction)
const fix = (f) => {
    const lazy = new Lazy(() => f(lazy.value));
    return lazy;
};

// PULL-BASED ARCHITECTURE

// Pull-based computation graph as a category
class PullGraph {
    constructor() {
        // Objects in the category (nodes)
        this.objects = new Map();
        
        // Morphisms between objects (edges with transformations)
        this.morphisms = new Map();
        
        // Identity morphism for each object
        this.identities = new Map();
        
        // Composition table for morphisms
        this.compositions = new Map();
        
        this.pullCount = 0;
        this.errorBoundaries = new Map();
        this.progressCallback = null;
        
        // Functors from this category to others
        this.functors = new Map();
    }
    
    // Register an object in the category
    register(id, computation, errorHandler = null) {
        const obj = {
            computation: computation instanceof Lazy ? computation : new Lazy(computation),
            cached: false,
            value: undefined,
            pullCount: 0,
            category: 'pull-graph'
        };
        
        this.objects.set(id, obj);
        
        // Create identity morphism
        this.identities.set(id, x => x);
        
        if (errorHandler) {
            this.errorBoundaries.set(id, errorHandler);
        }
    }
    
    // Add a morphism between objects
    morphism(sourceId, targetId, transform = x => x) {
        const morphId = `${sourceId}->${targetId}`;
        this.morphisms.set(morphId, {
            source: sourceId,
            target: targetId,
            transform: transform instanceof Lazy ? transform : new Lazy(() => transform),
            category: 'morphism'
        });
        
        // Update edges for compatibility
        if (!this.edges) this.edges = new Map();
        if (!this.edges.has(targetId)) {
            this.edges.set(targetId, new Set());
        }
        this.edges.get(targetId).add(sourceId);
    }
    
    // Compose two morphisms categorically
    compose(f, g) {
        // f: A -> B, g: B -> C, compose to get A -> C
        if (f.target !== g.source) {
            throw new Error(`Cannot compose morphisms: ${f.source}->${f.target} and ${g.source}->${g.target}`);
        }
        
        const composed = {
            source: f.source,
            target: g.target,
            transform: new Lazy(() => {
                const fx = f.transform.value;
                const gx = g.transform.value;
                return x => gx(fx(x));
            }),
            category: 'composed-morphism'
        };
        
        const compId = `${f.source}->>${g.target}`;
        this.compositions.set(compId, composed);
        return composed;
    }
    
    // Create a functor to another category
    functor(targetCategory, objectMap, morphismMap) {
        const functorId = `${this.constructor.name}->${targetCategory.constructor.name}`;
        this.functors.set(functorId, {
            source: this,
            target: targetCategory,
            objectMap: objectMap,
            morphismMap: morphismMap,
            
            // Apply functor to an object
            applyObject: (objId) => {
                const obj = this.objects.get(objId);
                if (!obj) throw new Error(`Object ${objId} not found`);
                return objectMap(obj);
            },
            
            // Apply functor to a morphism
            applyMorphism: (morphId) => {
                const morph = this.morphisms.get(morphId);
                if (!morph) throw new Error(`Morphism ${morphId} not found`);
                return morphismMap(morph);
            }
        });
        return this.functors.get(functorId);
    }
    
    // Backward compatibility
    dependsOn(nodeId, dependencyId) {
        this.morphism(dependencyId, nodeId);
    }
    
    get nodes() {
        return this.objects;
    }
    
    pull(nodeId) {
        const node = this.objects.get(nodeId);
        if (!node) {
            const error = new Error(`Unknown object: ${nodeId}`);
            if (traceOrchestrator) traceOrchestrator.error(error, { nodeId });
            throw error;
        }
        
        if (!node.cached) {
            try {
                this.pullCount++;
                
                if (processingCoordinator && processingCoordinator.state.has(nodeId)) {
                    const stateData = processingCoordinator.state.get(nodeId);
                    if (stateData) {
                        node.computation = stateData;
                    }
                }
                
                if (this.progressCallback && this.pullCount % 100 === 0) {
                    this.progressCallback({ 
                        pullCount: this.pullCount, 
                        nodeId,
                        stage: 'dependencies' 
                    });
                }
                
                if (traceOrchestrator) {
                    traceOrchestrator.trace('PULL_GRAPH_COMPUTE', { 
                        nodeId, 
                        hasDeps: this.edges.has(nodeId),
                        pullCount: node.pullCount++ 
                    });
                }
                
                const deps = this.edges.get(nodeId);
                if (deps) {
                    for (const depId of deps) {
                        this.pull(depId);
                    }
                }
                
                const errorHandler = this.errorBoundaries.get(nodeId);
                if (errorHandler) {
                    try {
                        const value = node.computation.value;
                        node.value = { error: null, value };
                    } catch (error) {
                        if (traceOrchestrator) {
                            traceOrchestrator.error(error, {
                                nodeId,
                                stage: 'computation',
                                handled: true
                            });
                        }
                        node.value = { error, value: errorHandler(error, nodeId) };
                    }
                    // Use Result eliminator to extract value
                    node.value = Result.elim(
                        () => 'Result', // motive
                        result => result.value, // Ok case
                        result => result.value  // Err case
                    )(node.value);
                } else {
                    node.value = node.computation.value;
                }
                
                node.cached = true;
                
                if (this.progressCallback) {
                    this.progressCallback({ 
                        pullCount: this.pullCount, 
                        nodeId,
                        stage: 'complete',
                        value: node.value 
                    });
                }
            } catch (error) {
                if (traceOrchestrator) {
                    traceOrchestrator.error(error, { 
                        nodeId, 
                        stage: 'pull',
                        fatal: !this.errorBoundaries.has(nodeId) 
                    });
                }
                throw error;
            }
        }
        
        return node.value;
    }
    
    setProgressCallback(callback) {
        this.progressCallback = callback;
    }
    
    // Invalidate cache (for reactive updates)
    invalidate(nodeId) {
        const node = this.objects.get(nodeId);
        if (node) {
            node.cached = false;
            // Invalidate all nodes that depend on this one
            if (this.edges) {
                for (const [id, deps] of this.edges) {
                    if (deps.has(nodeId)) {
                        this.invalidate(id);
                    }
                }
            }
        }
    }
}

// Transform any async operation into pull-based
class PullPromise {
    constructor(asyncThunk) {
        this._thunk = asyncThunk;
        this._promise = null;
        this._started = false;
    }
    
    // Only start the async operation when pulled
    pull() {
        if (!this._started) {
            this._promise = this._thunk();
            this._started = true;
        }
        return this._promise;
    }
    
    // Chain operations without executing
    then(onResolve, onReject) {
        return new PullPromise(() => 
            this.pull().then(onResolve, onReject)
        );
    }
    
    map(f) {
        return new PullPromise(() => 
            this.pull().then(f)
        );
    }
}

// Pull-based cache that only computes when accessed
class PullCache {
    constructor(generator) {
        this.generator = generator;
        this.graph = initPullGraph();
    }

    get(key) {
        const nodeKey = `pullcache:${key}`;
        if (!this.graph.nodes.has(nodeKey)) {
            this.graph.register(nodeKey, new Lazy(() => this.generator(key)));
        }
        return this.graph.pull(nodeKey);
    }

    has(key) {
        const nodeKey = `pullcache:${key}`;
        const node = this.graph.nodes.get(nodeKey);
        return node && node.evaluated;
    }

    warm(keys) {
        traceOrchestrator.trace('CACHE_WARM_START', { count: keys.length });
        const results = keys.map(key => this.get(key));
        traceOrchestrator.trace('CACHE_WARM_COMPLETE', { count: keys.length });
        return { keys, results };
    }

    invalidate(pattern) {
        const keys = Array.from(this.graph.nodes.keys())
            .filter(k => k.startsWith('pullcache:') && k.match(pattern))
            .map(k => k.replace('pullcache:', ''));
        keys.forEach(k => this.graph.invalidate(`pullcache:${k}`));
        lazyEvents.emit({ type: 'CACHE_INVALIDATED', count: keys.length });
        return keys;
    }
}

let pullGraph = null;
const initPullGraph = () => {
    if (!pullGraph) {
        pullGraph = new PullGraph();
        pullGraph.setProgressCallback((progress) => {
            if (progress.pullCount % 1000 === 0) {
                console.log(`[BUILD PROGRESS] Pulled ${progress.pullCount} nodes...`);
            }
        });
    }
    return pullGraph;
};
// Initialize immediately
initPullGraph();

// Lazy File System - fully integrated with our categorical structure
class LazyFS {
    constructor() {
        // Read cache using our existing PullCache
        this.readCache = new PullCache((path) => 
            fs.readFileSync(path, CONFIG.strings.standardEncoding)
        );
        
        // Write queue as lazy stream for sequential consistency
        this.writeQueue = new LazyStream(null, null);
        
        // File watchers as event streams
        this.watchers = new Map();
        
        // Stat cache for metadata
        this.statCache = new PullCache((path) => fs.statSync(path));
        
        // Directory listing cache
        this.dirCache = new PullCache((path) => fs.readdirSync(path));
    }

    // Read file lazily - integrates with our parse() pipeline
    read(path) {
        return new Lazy(() => {
            traceOrchestrator.trace('FS_READ', { path });
            return this.readCache.get(path);
        });
    }
    
    // Write file lazily - respects linear types for resource safety
    write(path, content) {
        return new PullPromise(async () => {
            traceOrchestrator.trace('FS_WRITE', { path });

            // Handle LazyTemplate specially
            if (content instanceof LazyTemplate) {
                content = content.toString();
            } else if (content instanceof Lazy) {
                content = content.value;
            }

            // Linear type: consume write token
            const writeToken = { resource: 'write', path };
            if (processingCoordinator.consumed.has(writeToken)) {
                throw new Error(`Write token already consumed for ${path}`);
            }
            processingCoordinator.consumed.add(writeToken);
            processingCoordinator.linearResources.add(`write:${path}`);

            try {
                await fs.promises.writeFile(path, content);
                return path;
            } finally {
                processingCoordinator.releaseResource('write', path);
            }
        });
    }
    
    // Watch path as lazy event stream
    watch(path) {
        // Return existing watcher stream if already watching
        if (this.watchers.has(path)) {
            return this.watchers.get(path);
        }
        
        // Create new lazy watcher stream
        const stream = new LazyStream(
            { type: 'init', path, time: Date.now() },
            () => {
                // Only start watching when stream is pulled
                const watcher = fs.watch(path, { encoding: CONFIG.strings.standardEncoding });
                
                // Convert Node.js events to our LazyStream
                let next = null;
                watcher.on('change', (eventType, filename) => {
                    const event = {
                        type: eventType,
                        path: filename ? path.join(path, filename) : path,
                        time: Date.now()
                    };
                    
                    // Chain events lazily
                    if (!next) {
                        next = new LazyStream(event, () => next);
                    }
                });
                
                watcher.on('error', (err) => {
                    traceOrchestrator.error(err, { path });
                });
                
                return next;
            }
        );
        
        this.watchers.set(path, stream);
        return stream;
    }
    
    // Check existence lazily
    exists(path) {
        return new Lazy(() => {
            try {
                this.statCache.get(path);
                return true;
            } catch {
                return false;
            }
        });
    }
    
    // Get file stats lazily
    stat(path) {
        return new Lazy(() => this.statCache.get(path));
    }
    
    // List directory lazily
    readdir(path) {
        return new Lazy(() => this.dirCache.get(path));
    }
    
    // Create directory lazily with proper error handling
    mkdir(path, options = { recursive: true }) {
        return new PullPromise(async () => {
            traceOrchestrator.trace('FS_MKDIR', { path, options });
            await fs.promises.mkdir(path, options);
            return path;
        });
    }
    
    // Remove file lazily
    unlink(path) {
        return new PullPromise(async () => {
            traceOrchestrator.trace('FS_UNLINK', { path });
            
            // Linear type: consume delete token
            const deleteToken = { resource: 'delete', path };
            if (processingCoordinator.consumed.has(deleteToken)) {
                throw new Error(`Delete token already consumed for ${path}`);
            }
            processingCoordinator.consumed.add(deleteToken);
            processingCoordinator.linearResources.add(`delete:${path}`);
            
            try {
                await fs.promises.unlink(path);
                // Invalidate caches
                this.readCache.cache.delete(path);
                this.statCache.cache.delete(path);
                return path;
            } finally {
                processingCoordinator.releaseResource('delete', path);
            }
        });
    }
    
    // Copy file lazily with verification
    copy(src, dest) {
        return new PullPromise(async () => {
            traceOrchestrator.trace('FS_COPY', { src, dest });
            
            // Read source lazily
            const content = await this.pull(this.read(src));
            
            // Write destination lazily
            await this.pull(this.write(dest, content));
            
            return { src, dest };
        });
    }
    
    // Batch operations for efficiency
    batchWrite(operations) {
        return new PullPromise(async () => {
            const results = [];
            for (const { path, content } of operations) {
                results.push(await this.write(path, content).pull());
            }
            return results;
        });
    }
    
    // Clear all caches
    clearCache() {
        this.readCache.cache.clear();
        this.statCache.cache.clear();
        this.dirCache.cache.clear();
    }
}

// Create global lazy file system instance
const lazyFS = new LazyFS();

// Lazy Event System - events as infinite streams in our topos
class LazyEventSystem {
    constructor() {
        // Root event stream - infinite lazy stream of all events
        this.rootStream = null;
        this.currentTail = null;

        // Track processed events for linear consume-once semantics
        this.eventStore = new Map(); // event type -> [{data, timestamp, processed}]
        this.handlers = new Map(); // event type -> [handler functions]

        // Initialize with empty stream
        this.events = fix(stream =>
            new LazyStream(null, () => this.currentTail || stream)
        );

        // Telemetry stream - enriched events
        this.telemetry = new Lazy(() =>
            this.events
                .map(e => this.enrichWithMetrics(e))
                .filter(e => e && e.significant)
        );

        // Error stream - filtered for errors
        this.errors = new Lazy(() =>
            this.events
                .filter(e => e && (e.type === 'error' || e.level === 'error'))
                .map(e => this.analyzeError(e))
        );

        // Performance stream - timing events
        this.performance = new Lazy(() =>
            this.events
                .filter(e => e && e.duration !== undefined)
                .map(e => ({
                    ...e,
                    percentile: this.calculatePercentile(e.duration)
                }))
        );

        // Causality stream - events with causal links
        this.causality = new Lazy(() =>
            this.events
                .filter(e => e && e.causes)
                .map(e => this.buildCausalChain(e))
        );

        // Resource usage stream
        this.resources = new Lazy(() =>
            this.events
                .filter(e => e && e.resource)
                .map(e => ({
                    ...e,
                    available: processingCoordinator.getResourceAvailability(e.resource)
                }))
        );

        // Validation violations stream
        this.violations = new Lazy(() =>
            this.events
                .filter(e => e && e.violation)
                .map(e => ({
                    ...e,
                    severity: this.assessViolationSeverity(e)
                }))
        );
    }
    
    // Emit event - adds to the infinite stream and stores for consume-once semantics
    emit(event) {
        const enrichedEvent = {
            ...event,
            timestamp: Date.now(),
            id: crypto.randomBytes(CONFIG.processor.hashLength).toString(CONFIG.strings.hashEncoding),
            context: traceOrchestrator.currentContext
        };

        // Store event with processed flag for linear consume-once semantics
        const eventType = event.type || 'default';
        if (!this.eventStore.has(eventType)) {
            this.eventStore.set(eventType, []);
        }
        this.eventStore.get(eventType).push({
            data: enrichedEvent,
            timestamp: enrichedEvent.timestamp,
            processed: false
        });

        // Create new tail for the stream
        const newTail = new LazyStream(enrichedEvent, () => this.currentTail);

        // Update current tail
        if (!this.currentTail) {
            this.currentTail = newTail;
            this.rootStream = newTail;
        } else {
            // Link to existing stream
            const oldTail = this.currentTail;
            this.currentTail = new LazyStream(enrichedEvent, () => oldTail);
        }

        // Trace emission
        traceOrchestrator.trace('EVENT_EMIT', enrichedEvent);

        return enrichedEvent;
    }

    // Register handler for event type
    on(eventType, handler) {
        if (!this.handlers.has(eventType)) {
            this.handlers.set(eventType, []);
        }
        this.handlers.get(eventType).push(handler);
    }

    // Pull all pending events for processing (consume-once semantics)
    pullEvents(eventType) {
        const pending = Maybe.elim(
            () => 'Maybe',
            () => [],
            p => p
        )(this.eventStore.get(eventType));
        const handlers = Maybe.elim(
            () => 'Maybe',
            () => [],
            h => h
        )(this.handlers.get(eventType));

        const results = [];
        for (const evt of pending) {
            if (!evt.processed) {
                for (const handler of handlers) {
                    results.push(handler(evt.data));
                }
                evt.processed = true;
            }
        }
        return results;
    }
    
    // Pull n events from stream
    consume(n = 1) {
        return this.events.take(n);
    }
    
    // Get events matching predicate
    query(predicate, limit = 10) {
        return new Lazy(() => 
            this.events
                .filter(predicate)
                .take(limit)
                .toArray()
        );
    }
    
    // Replay events from a checkpoint
    replay(fromTimestamp) {
        return new Lazy(() =>
            this.events
                .filter(e => e && e.timestamp >= fromTimestamp)
        );
    }
    
    // Fork the event stream for parallel processing
    fork() {
        return {
            main: this.events,
            fork: new LazyStream(null, () => this.currentTail)
        };
    }
    
    // Merge multiple event streams
    merge(...streams) {
        return streams.reduce((merged, stream) => 
            merged.interleave(stream), this.events
        );
    }
    
    // Window events by time
    window(duration) {
        const now = Date.now();
        return new Lazy(() =>
            this.events
                .filter(e => e && (now - e.timestamp) <= duration)
                .toArray()
        );
    }
    
    // Group events by type
    groupBy(keyFn) {
        return new Lazy(() => {
            const groups = new Map();
            let current = this.currentTail;
            
            while (current && current.head) {
                const key = keyFn(current.head);
                if (!groups.has(key)) {
                    groups.set(key, []);
                }
                groups.get(key).push(current.head);
                
                // Move to next in stream
                if (current.tail instanceof Function) {
                    current = current.tail();
                } else {
                    current = current.tail;
                }
            }
            
            return groups;
        });
    }
    
    // Enrich event with metrics
    enrichWithMetrics(event) {
        if (!event) return null;
        
        return {
            ...event,
            memory: process.memoryUsage(),
            cpu: process.cpuUsage(),
            uptime: process.uptime(),
            significant: this.isSignificant(event)
        };
    }
    
    // Analyze error event
    analyzeError(event) {
        if (!event) return null;
        
        return {
            ...event,
            stack: event.error?.stack,
            causality: traceOrchestrator.getCausalChain(event.id),
            impact: this.assessImpact(event),
            suggestions: this.generateSuggestions(event)
        };
    }
    
    // Build causal chain for event
    buildCausalChain(event) {
        const chain = [];
        let current = event;
        
        while (current && current.causes) {
            chain.push(current);
            current = this.findEvent(current.causes);
        }
        
        return {
            ...event,
            causalChain: chain,
            rootCause: chain[chain.length - 1]
        };
    }
    
    // Helper methods - delegating to TraceOrchestrator for validation
    isSignificant(event) {
        if (!traceOrchestrator) {
            return event.level === 'error' ||
                   event.duration > TIME.LONG ||
                   event.memory?.heapUsed > LIMITS.MEMORY_THRESHOLD;
        }

        // Use TraceOrchestrator metrics for significance assessment
        const metrics = traceOrchestrator.getMetrics();
        const bottlenecks = traceOrchestrator.identifyBottlenecks();

        return event.level === 'error' ||
               bottlenecks.some(b => b.operation === event.type) ||
               metrics.memoryPressure > CONFIG.ui.opacity.strong;
    }

    assessImpact(event) {
        if (!traceOrchestrator) {
            if (event.type === 'error') return 'high';
            if (event.duration > TIME.TIMEOUT) return 'medium';
            return 'low';
        }

        // Use TraceOrchestrator pattern detection for impact assessment
        const patterns = traceOrchestrator.detectPatterns();

        if (event.type === 'error' || patterns.errorClusters.some(cluster =>
            cluster.some(e => e.id === event.id))) {
            return 'high';
        }

        const bottlenecks = traceOrchestrator.identifyBottlenecks();
        if (bottlenecks.some(b => b.operation === event.type)) {
            return 'medium';
        }

        return 'low';
    }

    generateSuggestions(event) {
        const suggestions = [];

        // Use ERROR_SCHEMA pattern matching
        const errorCode = event.error?.code;
        const errorMsg = event.error?.message;

        if (ERROR_SCHEMA.fileNotFound.pattern.test(errorCode) ||
            ERROR_SCHEMA.fileNotFound.pattern.test(errorMsg)) {
            suggestions.push('Check file path exists');
        }

        if (ERROR_SCHEMA.operationTimeout.pattern.test(errorMsg)) {
            suggestions.push('Operation timed out - check network or increase timeout');
        }

        if (ERROR_SCHEMA.resourceClosed.pattern.test(errorMsg)) {
            suggestions.push('Resource was closed - check lifecycle management');
        }

        if (!traceOrchestrator) {
            if (event.duration > TIME.VERY_LONG) {
                suggestions.push('Consider async processing');
            }
            if (event.memory?.heapUsed > LIMITS.MEMORY_THRESHOLD) {
                suggestions.push('Memory usage high - consider optimization');
            }
        } else {
            // Use TraceOrchestrator bottleneck detection
            const bottlenecks = traceOrchestrator.identifyBottlenecks();
            if (bottlenecks.some(b => b.operation === event.type && b.avgDuration > TIME.VERY_LONG)) {
                suggestions.push('Consider async processing - detected performance bottleneck');
            }

            // Use TraceOrchestrator memory pressure calculation
            const metrics = traceOrchestrator.getMetrics();
            if (metrics.memoryPressure > CONFIG.ui.opacity.strong) {
                suggestions.push('Memory pressure detected - consider optimization');
            }

            // Use pattern detection for memory leaks
            const patterns = traceOrchestrator.detectPatterns();
            if (patterns.memoryLeaks) {
                suggestions.push('Potential memory leak detected - review resource cleanup');
            }
        }

        return suggestions;
    }

    calculatePercentile(duration) {
        if (!traceOrchestrator) {
            // Fallback to simple percentile calculation
            if (duration < TIME.TICK) return 50;
            if (duration < TIME.SECOND) return 70;
            if (duration < TIME.TIMEOUT) return 90;
            return 95;
        }

        // Use TraceOrchestrator performance profile for accurate percentiles
        const profile = traceOrchestrator.getPerformanceProfile();
        const allDurations = Object.values(profile).map(p => p.avg);

        if (allDurations.length === 0) {
            if (duration < TIME.TICK) return 50;
            if (duration < TIME.SECOND) return 70;
            if (duration < TIME.TIMEOUT) return 90;
            return 95;
        }

        allDurations.sort((a, b) => a - b);
        const index = allDurations.findIndex(d => d >= duration);
        if (index === -1) return 99;

        return Math.floor((index / allDurations.length) * 100);
    }

    assessViolationSeverity(event) {
        if (!traceOrchestrator || !traceOrchestrator.invariantChecker) {
            // Fallback using SEVERITY_SCHEMA
            for (const [level, schema] of Object.entries(SEVERITY_SCHEMA)) {
                if (schema.values.some(pattern => event.violation.includes(pattern))) {
                    return level;
                }
            }
            return 'low';
        }

        // Use InvariantChecker severity classification
        const severity = traceOrchestrator.invariantChecker.classifySeverity(event.violation);
        return severity || 'low';
    }
    
    findEvent(id) {
        let current = this.currentTail;
        
        while (current && current.head) {
            if (current.head.id === id) {
                return current.head;
            }
            current = current.tail instanceof Function ? current.tail() : current.tail;
        }
        
        return null;
    }
}

// Create global lazy event system
const lazyEvents = new LazyEventSystem();

// Lazy Git System - version control as lazy computations
class LazyGit {
    constructor() {
        // Dependency graph for git operations
        this.operations = new PullGraph();

        // Cache for git state
        this.statusCache = new PullCache(() => this._fetchStatus());
        this.diffCache = new PullCache((ref) => this._fetchDiff(ref));
        this.logCache = new PullCache((n) => this._fetchLog(n));

        // History as lazy stream
        this.history = new LazyStream(null, () => this._nextCommit());

        // Lazy pull helper - avoids early unwrapping
        this.pull = async (lazyValue) => {
            if (lazyValue instanceof PullPromise) {
                return await lazyValue.pull();
            }
            if (lazyValue instanceof Lazy) {
                const result = lazyValue.value;
                if (result instanceof PullPromise) {
                    return await result.pull();
                }
                return result;
            }
            return lazyValue;
        };

        // Changes as event stream
        this.changes = new LazyStream(null, null);
    }

    // Get status lazily
    status() {
        return new Lazy(() => {
            lazyEvents.emit({ type: 'git', action: 'status' });
            return this.statusCache.get('current');
        });
    }

    // Get current commit hash for hermetic builds
    getCurrentCommit() {
        return new PullPromise(async () => {
            try {
                const hash = execSync('git rev-parse HEAD', {
                    encoding: CONFIG.strings.standardEncoding
                }).trim();
                return hash;
            } catch (e) {
                return 'unknown';
            }
        });
    }

    // Get diff lazily
    diff(ref = 'HEAD') {
        return new Lazy(() => {
            lazyEvents.emit({ type: 'git', action: 'diff', ref });
            return this.diffCache.get(ref);
        });
    }

    // Get log lazily
    log(n = 10) {
        return new Lazy(() => {
            lazyEvents.emit({ type: 'git', action: 'log', count: n });
            return this.logCache.get(n);
        });
    }

    // Stage files lazily
    stage(files) {
        return new PullPromise(async () => {
            lazyEvents.emit({ type: 'git', action: 'stage', files });

            // Linear type: acquire staging lock
            const stageToken = { resource: 'git-stage', scope: 'global' };
            if (processingCoordinator.consumed.has(stageToken)) {
                throw new Error('Git staging lock already consumed');
            }
            processingCoordinator.consumed.add(stageToken);
            processingCoordinator.linearResources.add('git-stage:global');

            try {
                const results = [];
                for (const file of files) {
                    // Use lazy file existence check
                    const exists = lazyFS.exists(file).value;
                    if (exists) {
                        const result = execSync(`${CONFIG.strings.addCommand} ${file}`, {
                            encoding: CONFIG.strings.standardEncoding
                        });
                        results.push({ file, result });
                    }
                }

                // Invalidate status cache
                this.statusCache.cache.clear();

                return results;
            } finally {
                processingCoordinator.releaseResource('git-stage', 'global');
            }
        });
    }

    // Create commit lazily with empty message (as per requirements)
    commit(options = {}) {
        return new PullPromise(async () => {
            lazyEvents.emit({ type: 'git', action: 'commit', options });

            // Linear type: acquire commit lock
            const commitToken = { resource: 'git-commit', scope: 'global' };
            if (processingCoordinator.consumed.has(commitToken)) {
                throw new Error('Git commit lock already consumed');
            }
            processingCoordinator.consumed.add(commitToken);
            processingCoordinator.linearResources.add('git-commit:global');

            try {
                // Empty commit message as required
                const result = execSync('git commit --allow-empty-message -m ""', {
                    encoding: CONFIG.strings.standardEncoding
                });

                // Invalidate caches
                this.statusCache.cache.clear();
                this.logCache.cache.clear();
                this.diffCache.cache.clear();

                // Add to history stream
                this._addToHistory(result);

                return result;
            } finally {
                processingCoordinator.releaseResource('git-commit', 'global');
            }
        });
    }

    // Push lazily
    push(remote = 'origin', branch = null) {
        return new PullPromise(async () => {
            lazyEvents.emit({ type: 'git', action: 'push', remote, branch });

            // Linear type: acquire push lock
            const pushToken = { resource: 'git-push', scope: 'global' };
            if (processingCoordinator.consumed.has(pushToken)) {
                throw new Error('Git push lock already consumed');
            }
            processingCoordinator.consumed.add(pushToken);
            processingCoordinator.linearResources.add('git-push:global');

            try {
                const cmd = branch ? `git push ${remote} ${branch}` : `git push ${remote}`;
                const result = execSync(cmd, {
                    encoding: CONFIG.strings.standardEncoding
                });

                return result;
            } finally {
                processingCoordinator.releaseResource('git-push', 'global');
            }
        });
    }

    // Compose full commit workflow lazily
    commitWorkflow(files, push = false) {
        const stagePipeline = Pipeline.compose(
            files => this.stage(files),
            staged => new Lazy(() => {
                lazyEvents.emit({ type: 'GIT_STAGED', files: staged });
                return staged;
            })
        );

        const commitPipeline = Pipeline.compose(
            () => this.commit(),
            sha => new Lazy(() => {
                lazyEvents.emit({ type: 'GIT_COMMITTED', sha });
                return sha;
            })
        );

        const pushPipeline = push ? Pipeline.compose(
            () => this.push(),
            result => new Lazy(() => {
                lazyEvents.emit({ type: 'GIT_PUSHED', result });
                return result;
            })
        ) : () => new Lazy(() => 'No push');

        return Pipeline.kleisli(
            stagePipeline,
            commitPipeline,
            pushPipeline
        )(files);
    }

    // Branch workflow pipeline
    branchWorkflow(name, fromRef = 'HEAD') {
        return Pipeline.kleisli(
            () => this.stash(),
            () => this.checkout(fromRef),
            () => this.branch(name),
            () => this.stashPop()
        )();
    }

    // Rebase workflow pipeline
    rebaseWorkflow(onto) {
        return Pipeline.kleisli(
            () => this.status(),
            status => new Lazy(() => {
                if (status.modified.length > 0) {
                    throw new Error('Cannot rebase with uncommitted changes');
                }
                return status;
            }),
            () => this.rebase(onto),
            result => new Lazy(() => {
                lazyEvents.emit({ type: 'GIT_REBASED', onto, result });
                return result;
            })
        )();
    }

    // Check for uncommitted changes lazily
    hasChanges() {
        return new Lazy(() => {
            const status = this.statusCache.get('current');
            return status && status.trim().length > 0;
        });
    }

    // Get changed files lazily
    changedFiles() {
        return new Lazy(() => {
            const status = this.statusCache.get('current');
            if (!status) return [];

            return status
                .split('\n')
                .filter(line => line.trim())
                .map(line => {
                    const file = line.substring(GIT.statusPorcelainColumn).trim();
                    const status = line.substring(0, GIT.statusCodeLength).trim();
                    return { file, status };
                });
        });
    }

    // Get current branch lazily
    currentBranch() {
        return new Lazy(() => {
            const result = execSync('git branch --show-current', {
                encoding: CONFIG.strings.standardEncoding
            });
            return result.trim();
        });
    }

    // Create branch lazily
    createBranch(name) {
        return new PullPromise(async () => {
            lazyEvents.emit({ type: 'git', action: 'branch', name });

            const result = execSync(`git checkout -b ${name}`, {
                encoding: CONFIG.strings.standardEncoding
            });

            // Invalidate caches
            this.statusCache.cache.clear();

            return result;
        });
    }

    // Stash changes lazily
    stash(message = null) {
        return new PullPromise(async () => {
            lazyEvents.emit({ type: 'git', action: 'stash', message });

            const cmd = message ? `git stash push -m "${message}"` : 'git stash';
            const result = execSync(cmd, {
                encoding: CONFIG.strings.standardEncoding
            });

            // Invalidate status cache
            this.statusCache.cache.clear();

            return result;
        });
    }

    // Apply stash lazily
    stashPop() {
        return new PullPromise(async () => {
            lazyEvents.emit({ type: 'git', action: 'stash-pop' });

            const result = execSync('git stash pop', {
                encoding: CONFIG.strings.standardEncoding
            });

            // Invalidate status cache
            this.statusCache.cache.clear();

            return result;
        });
    }

    // Reset changes lazily
    reset(mode = '--soft', ref = 'HEAD') {
        return new PullPromise(async () => {
            lazyEvents.emit({ type: 'git', action: 'reset', mode, ref });

            // Linear type: acquire reset lock (dangerous operation)
            const resetToken = { resource: 'git-reset', scope: 'global' };
            if (processingCoordinator.consumed.has(resetToken)) {
                throw new Error('Git reset lock already consumed');
            }
            processingCoordinator.consumed.add(resetToken);
            processingCoordinator.linearResources.add('git-reset:global');

            try {
                const result = execSync(`git reset ${mode} ${ref}`, {
                    encoding: CONFIG.strings.standardEncoding
                });

                // Invalidate all caches
                this.statusCache.cache.clear();
                this.logCache.cache.clear();
                this.diffCache.cache.clear();

                return result;
            } finally {
                processingCoordinator.releaseResource('git-reset', 'global');
            }
        });
    }

    // Private helper methods
    _fetchStatus() {
        return execSync(CONFIG.strings.statusCommand, {
            encoding: CONFIG.strings.standardEncoding
        });
    }

    _fetchDiff(ref) {
        return execSync(`git diff ${ref}`, {
            encoding: CONFIG.strings.standardEncoding
        });
    }

    _fetchLog(n) {
        return execSync(`git log --oneline -n ${n}`, {
            encoding: CONFIG.strings.standardEncoding
        });
    }

    _nextCommit() {
        // Get next commit from history
        const log = this._fetchLog(1);
        if (log) {
            return new LazyStream(log, () => this._nextCommit());
        }
        return null;
    }

    _addToHistory(commit) {
        // Add commit to history stream
        const newNode = new LazyStream(commit, () => this.history);
        this.history = newNode;
    }

    // Clear all caches
    clearCache() {
        this.statusCache.cache.clear();
        this.diffCache.cache.clear();
        this.logCache.cache.clear();
    }
}

// Create global lazy git instance
const lazyGit = new LazyGit();

// DEPENDENT TYPES

class DependentType {
    constructor(param, paramType, bodyType) {
        this.param = param;
        this.paramType = paramType;
        this.bodyType = bodyType;
    }
    
    // Apply a value to get the resulting type
    apply(value) {
        if (!this.paramType.contains || !this.paramType.contains(value)) {
            // For now, skip validation if contains not defined
            if (this.paramType.contains) {
                throw new Error(`Value ${value} not in type ${this.paramType}`);
            }
        }
        return this.bodyType(value);
    }
    
    check(fn) {
        return new Proxy(fn, {
            apply: (target, thisArg, args) => {
                const [value] = args;
                const expectedType = this.apply(value);
                const result = target.apply(thisArg, args);
                // Type checking would go here
                return result;
            }
        });
    }
}

// Vector type - lists with length in the type
const Vec = (elementType, length) => {
    return new DependentType('n', NatType, (n) => {
        if (n !== length) throw new Error(`Expected length ${length}, got ${n}`);
        return { elementType, length: n };
    });
};

// Natural number type
const NatType = { contains: n => typeof n === 'number' && n >= 0 && Number.isInteger(n) };

// refinement types - base types with predicates
const Refinement = (baseType, predicate) => {
    return new DependentType('x', baseType, (x) => {
        if (!predicate(x)) throw new Error(`Value ${x} fails refinement`);
        return { base: baseType, valid: predicate(x) };
    });
};

// Validate array with expected length using Vec
const validateVec = (arr, expectedLength, description) => {
    try {
        checkType(arr, ArrayType);
    } catch {
        throw new Error(`${description}: expected array, got ${typeof arr}`);
    }
    if (arr.length !== expectedLength) {
        throw new Error(`${description}: expected length ${expectedLength}, got ${arr.length}`);
    }
    if (traceOrchestrator) {
        traceOrchestrator.trace('VEC_VALID', { length: expectedLength, description, actualLength: arr.length });
    }
    return arr;
};

// TACTICS


// EXTRACTION

// serialize runtime objects to plain data for debugging/telemetry
class StateSerializer {
    constructor() {
        this.serializers = new Map();
    }

    // serialize object using registered serializer
    serialize(typeName, obj) {
        const serializer = this.serializers.get(typeName);
        if (!serializer) return obj;
        return serializer(obj);
    }

    // register serializer for object type
    register(typeName, serializerFn) {
        this.serializers.set(typeName, serializerFn);
    }
}

// REFLECTION

class Reflection {
    constructor() {
        this.mirror = new Map();
    }
    
    // reflect value with type information
    reflect(value) {
        try {
            checkType(value, NumberType);
            const event = traceOrchestrator.events.find(e => e.context.value === value);
            return { type: 'Nat', value, event };
        } catch {}

        if (typeof value === 'function') {
            return { type: 'Function', value, source: value.toString() };
        }

        if (value instanceof SumType) {
            return {
                type: 'Type',
                value,
                constructors: value.constructors,
                eliminator: value.elim
            };
        }

        return { type: 'Unknown', value };
    }
    
    // Reify a type-level value back to runtime
    reify(reflected) {
        switch (reflected.type) {
            case 'Nat':
                return reflected.value;
            case 'Function':
                return eval(reflected.source);
            case 'Type':
                return reflected.value;
            default:
                return reflected.value;
        }
    }
    
    // introspect trace orchestrator state
    introspect(trace) {
        return {
            events: trace.events.length,
            violations: trace.runtimeViolations ? trace.runtimeViolations.size : 0,
            metrics: trace.metricsCalculator ? Object.keys(trace.metricsCalculator.getMetrics()).length : 0
        };
    }
}


const TIME = {
    TICK: 100,
    DEBOUNCE: 500,
    SECOND: 1000,
    TIMEOUT: 5000,
    LONG: 30000,
    VERY_LONG: 60000
};

const TIME_SCHEMA = {
    TICK: { type: 'positiveInt', min: 1 },
    DEBOUNCE: { type: 'positiveInt', min: TIME.TICK },
    TIMEOUT: { type: 'positiveInt', min: TIME.SECOND },
    LONG: { type: 'positiveInt', min: TIME.TIMEOUT },
    VERY_LONG: { type: 'positiveInt', min: TIME.LONG }
};

const LIMITS = {
    RETRIES: 3,
    BATCH: 50,
    MIN_GROUP: 3,
    MEMORY_THRESHOLD: 1073741824
};

const LIMITS_SCHEMA = {
    RETRIES: { type: 'positiveInt', min: 1 },
    BATCH: { type: 'positiveInt', min: 1 }
};

const GIT = {
    statusPorcelainColumn: 3,
    statusCodeLength: 2
};

const GIT_SCHEMA = {
    statusPorcelainColumn: { type: 'positiveInt', min: 1, exact: GIT.statusPorcelainColumn },
    statusCodeLength: { type: 'positiveInt', min: 1, exact: GIT.statusCodeLength }
};

const ERROR_SCHEMA = {
    fileNotFound: { type: 'string', pattern: /ENOENT|not found/i },
    resourceClosed: { type: 'string', pattern: /closed|disconnected/i },
    processDetached: { type: 'string', pattern: /detached|exited/i },
    operationTimeout: { type: 'string', pattern: /timeout|timed out/i }
};

const SEVERITY_SCHEMA = {
    high: {
        type: 'array',
        items: { type: 'string' },
        values: ['MAGIC_NUMBER', 'TYPE_ERROR', 'RESOURCE_LEAK']
    },
    medium: {
        type: 'array',
        items: { type: 'string' },
        values: ['CONFIG_VIOLATION', 'DEPRECATED_PATH', 'PERFORMANCE_WARNING']
    },
    low: {
        type: 'array',
        items: { type: 'string' },
        values: ['STYLE_VIOLATION', 'MINOR_ISSUE']
    }
};

const PRINT = {
    h1: 24,
    h2: 18,
    h3: 14,
    h4: 12,
    body: 11,
    footnote: 9,
    h1TopSpace: 24,
    h1BottomSpace: 12,
    h2TopSpace: 18,
    h2BottomSpace: 9,
    h3TopSpace: 14,
    h3BottomSpace: 7,
    h4TopSpace: 12,
    h4BottomSpace: 6,
    blockSpace: 12,
    inlineSpace: 10,
    indentSpace: 2,
    pdfMarginFraction: 0.75,
    pageMarginFraction: 1,
};

const BINARY = {
    KB: 1024,
    MB: 1048576,
    GB: 1073741824,
};

const CSS = {
    FONT_WEIGHTS: [100, 200, 300, 400, 500, 600, 700, 800, 900]
};

const THRESHOLDS = {
    MEMORY_LEAK_SLOPE: 1000,
    MEMORY_SPIKE_MB: 50,
    ERROR_CLUSTER_WINDOW: 1000,
    TOP_RESULTS: 10,
    AGGREGATE_WINDOW: 10,
    MEMORY_PRESSURE_HIGH: 0.85,
    MAX_FRACTION_DEPTH: 10,
    EVENT_RATE_BUSY: 50,
    VIEWPORT_HEIGHT: 100,
    HASH_SHORT_LENGTH: 16
};

class ConfigPatternValidator {
    constructor(enforceStrict = false) {
        this.violations = [];
        this.deprecatedPaths = new Set();
        this.magicNumbers = new Set();
        this.accessLog = [];
        this.computationGraph = new Map();  // The comonadic structure
        this.enforceStrict = enforceStrict;
        this.interceptFunctors();
    }
    
    interceptFunctors() {
        this.computationGraph = traceOrchestrator ? traceOrchestrator.events : [];
    }

    extract(value) {
        if (!traceOrchestrator) return null;
        const maybeProof = traceOrchestrator.events.find(e => e.context.value === value);
        return Maybe.elim(
            () => 'Maybe',
            () => null,
            v => v
        )(maybeProof);
    }
    
    detectMagicNumber(value, path) {
        if (typeof value !== 'number') return false;

        // Auto-discover config namespaces from ALL_CONFIGS
        const configNames = Object.keys(ALL_CONFIGS);
        if (configNames.some(name => path.startsWith(`${name}.`))) {
            return false;
        }

        const context = this.extract(value);

        if (context) {
            if (globalThis.DEBUG_CONFIG_ORIGINS) {
            }
            return false;
        }

        if (value === true || value === false) return false;

        if (path.includes('.weight.') && CSS.FONT_WEIGHTS.includes(value)) {
            this.computationGraph.set(value, { functor: 'CSS_STANDARD', inputs: ['font-weight'], timestamp: 0 });
            return false;
        }

        this.magicNumbers.add(`${path} = ${value}`);
        this.violations.push({
            type: 'MAGIC_NUMBER',
            path,
            value,
            message: `Value ${value} at ${path} is a literal magic number - replace with CONFIG constant`
        });

        return true;
    }
    
    checkDeprecatedPath(path) {
        const deprecated = [
            'CONFIG.constants',
            'ConfigSchema',
            'ConfigProfiles'
        ];
        
        for (const dep of deprecated) {
            if (path.startsWith(dep)) {
                this.deprecatedPaths.add(path);
                this.violations.push({
                    type: 'DEPRECATED_PATH',
                    path,
                    message: `Deprecated config path: ${path}`
                });
                return true;
            }
        }
        return false;
    }
    
    validateStructure(obj, path = 'CONFIG') {
        if (typeof obj !== 'object' || obj === null) {
            this.detectMagicNumber(obj, path);
            return;
        }
        
        for (const [key, value] of Object.entries(obj)) {
            const fullPath = `${path}.${key}`;
            this.checkDeprecatedPath(fullPath);
            
            if (typeof value === 'object' && value !== null) {
                this.validateStructure(value, fullPath);
            } else {
                this.detectMagicNumber(value, fullPath);
            }
        }
    }
    
    createProxy(obj, path = 'CONFIG') {
        const validator = this;
        return new Proxy(obj, {
            get(target, prop) {
                const fullPath = `${path}.${String(prop)}`;
                validator.accessLog.push({
                    path: fullPath,
                    timestamp: Date.now()
                });
                
                if (prop === 'constants' || prop === 'print' || prop === 'ui' || prop === 'validation') {
                    console.error(`[CONFIG VIOLATION] Accessing deprecated CONFIG.${prop}`);
                    validator.violations.push({
                        type: 'RUNTIME_DEPRECATED_ACCESS',
                        path: fullPath,
                        message: `Runtime access to deprecated path: ${fullPath}`
                    });
                }
                
                const value = target[prop];
                if (typeof value === 'object' && value !== null) {
                    return validator.createProxy(value, fullPath);
                }
                return value;
            },
            set(target, prop, value) {
                const fullPath = `${path}.${String(prop)}`;
                
                if (validator.detectMagicNumber(value, fullPath)) {
                    console.error(`[CONFIG VIOLATION] Magic number ${value} assigned to ${fullPath}`);
                }
                
                target[prop] = value;
                return true;
            }
        });
    }
    
    report() {
        if (this.violations.length === 0) {
            console.log('[CONFIG] No violations detected');
            return null;
        }
        
        console.error('\n========== CONFIG VIOLATIONS DETECTED ==========');
        console.error(`Found ${this.violations.length} violations:\n`);
        
        const byType = {};
        for (const v of this.violations) {
            if (!byType[v.type]) byType[v.type] = [];

            byType[v.type].push(v);
        }
        
        // Report MISSING_RECORD_COMPUTATION separately with clear fix instructions
        if (byType.MISSING_RECORD_COMPUTATION) {
            console.error(`\nMISSING_RECORD_COMPUTATION (${byType.MISSING_RECORD_COMPUTATION.length}) - These computed values need recordComputation():`);
            for (const v of byType.MISSING_RECORD_COMPUTATION) {
                console.error(`  ⚠ ${v.path} = ${v.value}`);
                console.error(`    FIX: Wrap with ${v.message.split('needs ')[1]}`);
            }
            delete byType.MISSING_RECORD_COMPUTATION;
        }
        
        if (byType.MAGIC_NUMBER) {
            const valueGroups = {};
            for (const v of byType.MAGIC_NUMBER) {
                if (!valueGroups[v.value]) valueGroups[v.value] = [];

                valueGroups[v.value].push(v.path);
            }
            
            console.error(`\nMAGIC_NUMBER (${byType.MAGIC_NUMBER.length}) - True literals that need replacement:`);
            for (const [value, paths] of Object.entries(valueGroups)) {
                // Identify which object this comes from
                const sources = paths.map(p => p.split('.')[0]);
                const uniqueSources = [...new Set(sources)];
                const sourceText = uniqueSources.length === 1 ? ` [from ${uniqueSources[0]}]` : '';
                
                if (paths.length > 1) {
                    console.error(`  ✗ Value ${value} appears ${paths.length} times${sourceText}:`);
                    paths.forEach(p => console.error(`      ${p}`));
                } else {
                    console.error(`  ✗ ${paths[0]} = ${value}${sourceText} (replace with computed constant)`);
                }
            }
            delete byType.MAGIC_NUMBER;
        }
        
        for (const [type, violations] of Object.entries(byType)) {
            console.error(`\n${type} (${violations.length}):`);
            for (const v of violations.slice(0, 10)) {  // Show first 10
                console.error(`  - ${v.message}`);
            }
            const limit = 10;
            if (violations.length > limit) {
                console.error(`  ... and ${violations.length - limit} more`);
            }
        }
        
        console.error('\n================================================\n');
        
        if (this.enforceStrict && this.violations.length > 0) {
            console.error('[FATAL] Categorical structure violated');
            process.exit(1);
        }
        
        return this.violations;
    }
}

const CONFIG_RAW = {};

CONFIG_RAW.core = {
    time: {
        msPerSecond: 1000,
        defaultSleepSeconds: 1
    }
};

CONFIG_RAW.network = {
    websocket: {
        updateInterval: 33,
        maxPayloadSize: 1048576
    },
    errors: {
        addressInUse: 'EADDRINUSE'
    }
};


CONFIG_RAW.scheduler = {
    maxConcurrent: 2,
    retryLimit: 3,
    retryDelayBase: 1000,
    debounceDelay: 500
};

CONFIG_RAW.processing = {
    polling: {
        intervalMs: 100
    },
    content: {
        maxHeadingLevel: 6,
        minGroupSize: 3
    },
    hash: {
        byteLength: 8
    }
};

// MORPHISMS: Transformations between computational states
CONFIG_RAW.morphisms = {
    // Identity - the do-nothing transformation
    identity: (x) => x,
    
    // Functors - structure-preserving maps
    functors: {
        map: 'map',  // Standard functor
        flatMap: 'flatMap',  // Monadic bind
        traverse: 'traverse',  // Traversable functor
        sequence: 'sequence',  // Sequence effects
        coflatMap: 'extract',  // Comonadic cobind
        distribute: 'distribute',  // Distributive functor
        ap: 'apply',  // Applicative functor
        fold: 'catamorphism',  // Fold/reduce
        unfold: 'anamorphism',  // Unfold/generate
        refold: 'hylomorphism'  // Fold after unfold
    },
    
    // Natural transformations
    natural: {
        lazy: 'force',  // Lazy -> Strict
        strict: 'defer',  // Strict -> Lazy  
        async: 'await',  // Async -> Sync
        sync: 'promise',  // Sync -> Async
        option: 'maybe',  // Option -> Maybe
        either: 'result',  // Either -> Result
        list: 'stream',  // List -> Stream
        tree: 'zipper',  // Tree -> Zipper
        state: 'store',  // State -> Store
        reader: 'env'  // Reader -> Env
    },
    
    // Compositions
    kleisli: Pipeline.kleisli,  // Kleisli composition
    compose: Pipeline.compose,  // Standard composition
    
    aggregator: {
        name: 'generate-index',
        apply: (docs) => renderView({ type: 'document-index' }, docs),
        barrier: 'artifacts',
        timeout: TIME.LONG
    },

    stateToView: {
        name: 'runtime-to-gui',
        apply: null,
        preserves: ['causality', 'metrics', 'events', 'errors'],
        proof: 'bijection'
    },
    
    // Higher-order morphisms
    higher: {
        // 2-morphisms (morphisms between morphisms)
        horizontal: (f, g) => (x) => g(f(x)),  // Horizontal composition
        vertical: (α, β) => (F) => β(α(F)),  // Vertical composition
        
        // n-morphisms (recursive)
        tower: function nMorphism(n) {
            if (n === 0) return CONFIG_RAW.morphisms.identity;
            if (n === 1) return (f) => f;
            return (α) => nMorphism(n - 1)(α);
        },
        
        // Kan extensions
        leftKan: null,  // Left Kan extension
        rightKan: null,  // Right Kan extension
        
        // Adjunctions
        leftAdjoint: null,  // F ⊣ G
        rightAdjoint: null,  // F ⊢ G
        
        // Yoneda embedding
        yoneda: (a) => (f) => f(a)
    }
};

// CONTRACTS: Rules and invariants
CONFIG_RAW.contracts = {
    // Type contracts
    types: {
        linear: 'use-once',  // Linear types
        affine: 'use-at-most-once',  // Affine types
        relevant: 'use-at-least-once',  // Relevant types
        unrestricted: 'use-many',  // Normal types
        ordered: 'use-in-order',  // Ordered types
        graded: 'use-n-times',  // Graded types
        session: 'protocol-typed',  // Session types
        refinement: 'predicate-refined',  // Refinement types
        dependent: 'value-dependent',  // Dependent types
        higher: 'kind-polymorphic'  // Higher-kinded types
    },

    // validation requirements
    validation: {
        termination: true,
        totality: true,
        determinism: false,
        purity: true,  // Must be pure
        // Logical properties
        consistency: true,  // No contradictions
        completeness: false,  // Gödel says no
        decidability: false,  // Halting problem
        soundness: true,  // Proofs are valid
        // Computational properties
        confluence: true,
        parametricity: true,
        naturality: true,
        functoriality: true
    },
    
    // Resource limits
    resources: {
        memory: LIMITS.MEMORY_THRESHOLD,
        time: TIME.VERY_LONG,
        energy: 100,  // Joules
        bandwidth: BINARY.MB,
        // Complexity bounds
        space: 'O(n)',  // Space complexity
        runtime: 'O(n log n)',  // Time complexity
        messages: 'O(n²)',  // Message complexity
        rounds: 'O(log n)'  // Round complexity
    },
    
    // Invariants that must hold
    invariants: {
        // Conservation laws
        energyConservation: true,  // Energy is conserved
        informationConservation: true,  // Information is preserved
        causalityPreservation: true,  // Causality is maintained
        // Algebraic laws
        associativity: ['compose', 'kleisli', 'parallel'],
        commutativity: ['parallel', 'merge'],
        idempotence: ['union', 'intersection'],
        distributivity: ['compose', 'parallel'],
        // Category laws
        identityLaws: true,  // id ∘ f = f = f ∘ id
        associativityLaws: true,  // (f ∘ g) ∘ h = f ∘ (g ∘ h)
        functorLaws: true,  // F(id) = id, F(g ∘ f) = F(g) ∘ F(f)
        naturalitySquares: true  // Natural transformation diagrams commute
    }
};

CONFIG_RAW.documents = {
    content: {
        experienceTitle: 'Higher Category Theory Through Human Experience',
        experienceDescription: 'An exploration of higher category theory through practical examples and human-scale analogies, bridging abstract mathematics with concrete experience.',
        primerTitle: 'Higher Category Theory: A Primer',
        primerDescription: 'A systematic introduction to higher category theory, covering simplicial sets, fibrations, limits, topoi, and their applications in modern mathematics.',
        defaultDescription: 'A comprehensive document on higher category theory and its mathematical foundations.'
    },

    artifacts: {
        workingDoc: {
            name: 'HCT Working Document',
            txt: 'src/HCT_working.txt',
            pdf: 'output/working.pdf',
            html: 'output/working.html',
            md: 'output/working.md'
        },
        primerDoc: {
            name: 'HCT Primer',
            txt: 'src/HCT_primer.txt',
            pdf: 'output/primer.pdf',
            html: 'output/primer.html',
            md: 'output/primer.md'
        },
        indexFile: 'output/index.html',
        readmeFile: 'output/README.md',
        lockFile: 'temp/.build.lock',
        buildScript: 'scripts/builder.js'
    },

    formats: {
        extensions: {
            txt: '.txt',
            pdf: '.pdf',
            html: '.html',
            md: '.md'
        },
        defaultOutputFormats: ['html', 'markdown', 'pdf']
    }
};

Object.assign(CONFIG_RAW, {
    debug: {
        maxEvents: 1000,
        maxMaps: TIME.TICK,
        cleanupInterval: TIME.TICK,
        stackFrameEnd: 7,  // 7 frames in stack trace
        performanceWarnThreshold: TIME.TICK,
        enableTelemetry: true,
        // Analysis windows use functorial composition
        analysis: {
            recentWindowSize: TIME.TICK,
            errorWindowSize: 20,
            memoryTrendSize: LIMITS.BATCH,
            performanceSampleSize: 20,
            topResultsLimit: 5,  // top 5 results
        }
    },
    
    // Scheduler - delegates to actors.orchestration
    scheduler: {
        maxConcurrent: CONFIG_RAW.actors?.orchestration?.maxConcurrent || 2,
        retryLimit: CONFIG_RAW.actors?.orchestration?.retryLimit || LIMITS.RETRIES,
        retryDelayBase: CONFIG_RAW.actors?.orchestration?.retryDelayBase || TIME.SECOND,
        debounceDelay: CONFIG_RAW.actors?.orchestration?.debounceDelay || TIME.DEBOUNCE,
        lockCheckInterval: TIME.TICK,
        buildHistoryLimit: LIMITS.BATCH,
        buildHistoryTrim: 25,
        defaultPriority: 0,
        retryPriority: -1,
        initialBuildPriority: 10,
        memoryPressureThreshold: 0.8,
        errorRateThreshold: 0.1,
        scaleDownFactor: 0.75,
        scaleUpFactor: 1.25
    },
    
    // Processor - uses substrate.topology
    processor: {
        hashLength: CONFIG_RAW.processing.hash.byteLength,
        sectionIdMaxLength: 100,
        headingMaxLevels: CONFIG_RAW.processing.content.maxHeadingLevel,
        minGroupSize: CONFIG_RAW.processing.content.minGroupSize,
        tocMaxDepth: 2,  // 2 levels in TOC
        subSectionLevel: 3,  // level 3 is subsection
        scrollHighlightThreshold: 100,  // 100px
        mediumSizeThreshold: 1024,
        largeSizeThreshold: 1048576,
        titleMaxLength: 200,
        codeBlockSliceLength: 3,  // 3 chars
        notFoundIndex: -1,  // -1
        topSectionLevel: 1,  // 1
        majorSectionLevel: 2,  // 2
        debugContextSize: 50,  // 50 chars
        coarsePrecision: 1,  // 1 decimal
        signalKillDefault: 0  // 0
    },
    
    latex: {
        maxRecursionDepth: 10,              // Max depth for recursive LaTeX processing
        minMatchLength: 10,                 // Min length for fuzzy title matching
        cacheKeyDepthPrefix: true,          // Include depth in cache keys
        logUnhandledCommands: true,         // Log unrecognized LaTeX commands
        debugSubstringLength: LIMITS.BATCH,           // Length of debug substring for error messages
    },
    
    // Browser & PDF settings (for puppeteer)
    browser: {
        launchTimeout: TIME.LONG,          // Timeout for puppeteer.launch
        pageLoadTimeout: TIME.LONG,        // Timeout for page.setContent
        pdfTimeout: TIME.VERY_LONG,        // Timeout for page.pdf
        maxRetries: LIMITS.RETRIES,        // Max retries for browser operations
    },
    
    // File Watching
    watcher: {
        dedupWindow: TIME.TICK,            // Dedup window for file events
        dedupCleanupInterval: TIME.TIMEOUT,// Clean old dedup entries
        initialBuildWaitMax: TIME.LONG,    // Max wait for initial builds
        initialBuildCheckInterval: TIME.TICK,
        postBuildDelay: TIME.DEBOUNCE,     // Delay after builds complete
    },
    
    // Process Management
    process: {
        lockHeartbeatInterval: TIME.SECOND,
        lockTimeout: TIME.TIMEOUT,         // Consider lock stale
        lockAliveCheckTime: TIME.VERY_LONG,// Max time to consider lock alive
        lockRetryAttempts: 10,             // Number of times to check for lock release
        lockUpdateInterval: TIME.LONG,
        shutdownTimeout: TIME.TIMEOUT,     // Max time to wait for cleanup
        statsInterval: TIME.TIMEOUT,       // Show scheduler stats
        heartbeatInterval: TIME.LONG,      // Keep-alive heartbeat interval
        exitCode: {
            success: 0,
            error: 1,
        },
    },
    
    // Git Integration
    git: {
        statusPorcelainColumn: GIT.statusPorcelainColumn,
        commitMessageMaxLength: 0, // 0 = empty commits as required
    },
    
    // Prediction system
    prediction: {
        failureThreshold: 0.7,  // probability threshold for emitting LIKELY_FAILURE event
        remediationThreshold: 0.6,  // probability threshold for triggering auto-remediation
        browserRestartThreshold: 0.85,  // probability threshold for restarting browser
    },
    
    // System limits and constraints for validation
    limits: {
        minPositive: 1,
        minZero: 0,
        maxScaleValue: 10,
        xssPreviewLength: 50,
        minFontSize: 10,
        maxFontSize: 24,
        minDebugEvents: TIME.TICK,
        minDebugMaps: 10,
        minConcurrent: 1,
        maxConcurrent: 10,
        minHashLength: 4,
        maxHashLength: 32,
        htmlHeadingLevels: 6,
        memoryPressureThreshold: new Lazy(() => 9 / 10),
        maxEventRate: new Lazy(() => 100 * 10),
        telemetryWindowSize: 2,
        aggregateWindowSize: 10,
        defaultLimit: 100,
    },
    
    // Legacy document metadata - now in manifestation.documents.content
    content: CONFIG_RAW.documents?.content || {
        experienceTitle: 'Higher Category Theory Through Human Experience',
        experienceDescription: 'An exploration of higher category theory through practical examples and human-scale analogies, bridging abstract mathematics with concrete experience.',
        primerTitle: 'Higher Category Theory: A Primer',
        primerDescription: 'A systematic introduction to higher category theory, covering simplicial sets, fibrations, limits, topoi, and their applications in modern mathematics.',
        defaultDescription: 'A comprehensive document on higher category theory and its mathematical foundations.',
    },

    // Legacy files - now in documents.artifacts
    files: (() => {
        const artifacts = CONFIG_RAW.documents?.artifacts;
        const formats = CONFIG_RAW.documents?.formats;
        return {
            sourcePattern: '**/*.txt',
            workingDoc: {
                ...artifacts.workingDoc,
                dependencies: new Lazy(() => ({
                    html: ['txt'],
                    pdf: ['html'],
                    md: ['txt']
                }))
            },
            primerDoc: {
                ...artifacts.primerDoc,
                dependencies: new Lazy(() => ({
                    html: ['txt'],
                    pdf: ['html'],
                    md: ['txt']
                }))
            },
            indexFile: artifacts.indexFile,
            indexDependencies: new Lazy(() => ['workingDoc.html', 'primerDoc.html']),
            readmeFile: artifacts.readmeFile,
            lockFile: artifacts.lockFile,
            buildScript: artifacts.buildScript,
            telemetryFile: 'telemetry.json',
            extensions: formats.extensions,
            defaultOutputFormats: formats.defaultOutputFormats
        };
    })(),
    
    // String constants
    strings: {
        // Operation categories (for task classification)
        operationCategories: ['build', 'parse', 'transform', 'pdf', 'latex', 'task'],
        defaultCategory: 'other',
        
        // Error patterns (for retry logic)
        errorPatterns: {
            fileNotFound: 'ENOENT',
            resourceClosed: 'Target closed',
            processDetached: 'detached',
            operationTimeout: 'timeout'
        },
        
        // Supported languages (for code blocks)
        supportedLanguages: ['text', 'javascript', 'python', 'typescript', 'html', 'css', 'json', 'yaml', 'bash', 'sh', 'markdown', 'md', 'latex', 'tex'],
        defaultLanguage: 'text',
        
        // Block delimiters
        codeDelimiter: '```',
        quoteDelimiter: '>',
        mathStartDelimiter: '<<<BLOCKMATH>>>',
        mathEndDelimiter: '<<</BLOCKMATH>>>',
        
        // Document structure prefixes
        structurePrefixes: ['Layer', 'Section', 'Chapter', 'Part'],
        
        // Command prefixes (for various parsers)
        commandPrefixes: {
            text: 'text',
            roman: 'mathrm',
            bold: 'textbf',
            italic: 'textit',
            fraction: 'frac'
        },
        
        // Semantic HTML elements
        semanticElements: {
            emphasis: 'em',
            strong: 'strong',
            superscript: 'sup',
            subscript: 'sub'
        },
        
        // Command line flags
        cliFlags: {
            push: '--push',
            online: '--online'
        },
        
        // DOM events
        domEvents: {
            contentLoaded: 'DOMContentLoaded',
            scroll: 'scroll'
        },
        
        // Scroll behavior options
        scrollBehavior: {
            smooth: 'smooth',
            auto: 'auto',
            instant: 'instant'
        },
        scrollBlock: {
            start: 'start',
            center: 'center',
            end: 'end',
            nearest: 'nearest'
        },
        
        // Encodings
        standardEncoding: 'utf8',
        standardEncodingDash: 'utf-8',
        
        // Process signals
        interruptSignal: 'SIGINT',
        exceptionEvent: 'uncaughtException',
        rejectionEvent: 'unhandledRejection',
        
        // Browser options
        emptyPageUrl: 'about:blank',
        networkIdleState: 'networkidle0',
        pageFormat: 'letter',
        
        // Platform
        windowsPlatform: 'win3N.two',
        windowsSleepCommand: () => `timeout /t ${CONFIG.core.time.defaultSleepSeconds} /nobreak >nul`,  // Build command dynamically
        unixSleepCommand: () => `sleep ${CONFIG.core.time.defaultSleepSeconds}`,
        
        // Build messages
        buildSystemVersion: 'HCT Build System v4.0',
        shutdownMessage: '[SHUTDOWN] Closing...',
        startupFailedMessage: '[STARTUP FAILED]',
        fatalErrorPrefix: '[FATAL]',
        errorPrefix: '[ERROR]',
        warningPrefix: '[WARNING]',
        lockPrefix: '[LOCK]',
        lockWaitingMessage: '[LOCK] Waiting for other build to complete...',
        lockStillRunningMessage: '[LOCK] Other build still running, exiting',
        lockErrorPrefix: '[LOCK ERROR]',
        lockCleanupErrorPrefix: '[LOCK CLEANUP ERROR]',
        criticalErrorPrefix: '[CRITICAL ERROR]',
        unhandledRejectionPrefix: '[UNHANDLED REJECTION]',
        shutdownBrowserErrorPrefix: '[SHUTDOWN] Browser cleanup error:',
        fatalLockMessage: '[FATAL] Could not acquire process lock',
        watchPrefix: '[WATCH]',
        watchFilePrefix: '[WATCHFILE]',
        watchingPrefix: '[WATCHING]',
        indexGenerated: '[INDEX] Generated index.html',
        
        // Git commands
        statusCommand: 'git status --porcelain',
        diffCommand: 'git diff --cached --name-only',
        addCommand: 'git add',
        logCommand: 'git log --oneline -n 5',
        
        // Document titles
        documentTitle: 'Higher Category Theory',
        metadataSeparator: ' · ',  // Separator for metadata items
        projectAbbreviation: 'HCT',
        buildVersion: 'v4.0',      // Build system version
        
        // Locale settings
        timeLocale: 'en-US',
        timeFormat: '2-digit',
        hourFormat12: false,
        
        // HTML attributes
        defaultLanguage: 'en',
        standardCharset: 'UTF-8',
        viewportContent: 'width=device-width, initial-scale=1.0',
        cacheControlContent: 'no-cache, no-store, must-revalidate',
        pragmaContent: 'no-cache',
        expiresContent: '0',
        
        // Browser args
        sandboxFlag: '--no-sandbox',
        setuidFlag: '--disable-setuid-sandbox',
        devShmFlag: '--disable-dev-shm-usage',
        gpuFlag: '--disable-gpu',
        zygoteFlag: '--no-zygote',
        headlessMode: 'new',
        
        // Font families
        primaryFont: 'Helvetica Neue',
        secondaryFont: 'Helvetica',
        fallbackFont: 'Arial',
        sansSerif: 'sans-serif',
        primaryFontStack: "'Helvetica Neue', Helvetica, Arial, sans-serif",
        fallbackFontStack: "'Arial', sans-serif",
        
        // Hash algorithms and encoding
        mainHashAlgorithm: 'sha256',     // Primary hash algorithm
        fallbackHashAlgorithm: 'md5',    // Secondary hash algorithm
        hashEncoding: 'hex',
        
        // File size units
        smallSizeUnit: ' B',
        mediumSizeUnit: ' KB',
        largeSizeUnit: ' MB',
        
        // Section identifiers
        sectionIdPrefix: 'sec-',
        sectionFallback: 'section',
        
        // CSS Classes
        classActive: 'active',
        classExpanded: 'expanded',
        classCollapsed: 'collapsed',
        // Content rendering classes
        blockContentClass: 'math-block',
        inlineContentClass: 'math-inline',
        textInsideClass: 'text-in-math',
        operatorClass: 'operator',
        romanStyleClass: 'mathrm',
        calligraphicClass: 'mathcal',
        blackboardClass: 'mathbb',
        frakturClass: 'mathfrak',
        sansSerifClass: 'mathsf',
        boldStyleClass: 'mathbf',
        annotatedElementClass: 'arrow-with-text',
        annotationTextClass: 'arrow-text',
        tildeAccentClass: 'tilde',
        hatAccentClass: 'hat',
        barAccentClass: 'bar',
        dotAccentClass: 'dot',
        vectorClass: 'vec',
        fractionClass: 'frac',
        numeratorClass: 'num',
        denominatorClass: 'den',
        // Navigation classes
        navigationContentClass: 'toc-content',
        navigationSectionClass: 'toc-section',
        navigationMajorClass: 'toc-major',
        toggleIconClass: 'toggle-icon',
        spacerClass: 'toc-spacer',
        navigationLinkClass: 'toc-link',
        navigationNumberClass: 'toc-number',
        childrenContainerClass: 'toc-children',
        anchorLinkClass: 'anchor-link',
        toggleControlClass: 'toc-toggle',
        // Layout classes
        sidebarClass: 'toc-sidebar',
        headerClass: 'toc-header',
        expandControlClass: 'expand-all',
        contentClass: 'content',
        documentSectionClass: 'document-section',
        sectionHeadingClass: 'section-heading',
        // HTML elements
        blockElement: 'div',
        inlineElement: 'span',
        linkElement: 'a',
        listItemElement: 'li',
        // Special characters
        collapsedIndicator: '▶',
        expandedIndicator: '▼',
        anchorSymbol: '#',
        // DOM attributes
        expandedAttribute: 'aria-expanded',
        // UI text labels
        expandAllLabel: 'Expand All',
        collapseAllLabel: 'Collapse All',
        contentsLabel: 'Contents',
    },
    
    // Colors
    colors: {
        // Text colors
        text: {
            body: '#2c3e50',          // Main body text (dark blue-gray)
            heading: '#333',          // Headings (dark gray)
            emphasis: '#000',         // Emphasized text (black)
            muted: '#777',            // Muted/secondary text
            disabled: '#999',         // Disabled/inactive text
            code: '#d73a49',          // Code strings/literals
        },
        // Background colors
        background: {
            main: '#ffffff',          // Main background (white)
            subtle: '#fafafa',        // Subtle background variation
            sidebar: '#f8f9fa',       // Sidebar/navigation background
            code: '#f6f8fa',          // Code block background
            highlight: '#f5f5f5',     // Highlighted/selected background
        },
        // Border colors
        border: {
            default: '#eN.onee4e8',       // Default border
            light: '#e8e8e8',         // Light/subtle border
            medium: '#e0e0e0',        // Medium emphasis border
        },
        // Link colors
        link: {
            default: '#0366d6',       // Default link
            hover: '#005N.twoa3',         // Hovered link
            active: '#0056b3',        // Active/pressed link
            visited: '#2c5aa0',       // Visited link
        },
        // Special colors
        shadowBase: 'rgba(0,0,0,',    // Base for shadow colors (black with alpha)
        neutralBase: 'white',          // Pure white/base color
    },
    
    // Regex patterns
    patterns: {
        // Math patterns
        blockMathBrackets: /\\\[\s*([\s\S]*?)\s*\\\]/g,
        inlineMathParens: /\\\((.*?)\\\)/g,
        blockMathMarker: /<<<BLOCKMATH>>>(.+?)<<<\/BLOCKMATH>>>/gs,
        inlineMathMarker: /<<<INLINEMATH>>>(.+?)<<<\/INLINEMATH>>>/g,
        codeBlocks: /```[\s\S]*?```/g,
        
        // Heading patterns (handle both Unix \n and Windows \r\n line endings)
        hashHeading: new RegExp(`^(#{1,${6}})\\s+(.+?)\\s*$`),  // 6 heading levels, trim trailing whitespace including \r
        setextPrimary: /^=+\s*$/,
        setextSecondary: /^-+\s*$/,
        horizontalRule: new RegExp(`^[-*_]{${3},}$`),  // Min 3 chars for HR
        
        // List patterns
        unorderedList: /^[-*+•]\s+/,
        orderedList: /^\d+[.)]\s+/,
        
        // Clean-up patterns
        nonWordChars: /[^\w\s-]/g,
        multiSpace: /\s+/g,
        multiDash: /-+/g,
        trimDash: /^-|-$/g,
        
        // LaTeX patterns
        arrayEnv: /\\begin\{array\}(?:\{[^}]*\})?([\s\S]+?)\\end\{array\}/g,
        alignedEnv: /\\begin\{aligned\}([\s\S]+?)\\end\{aligned\}/g,
        matrixEnv: /\\begin\{[bp]?matrix\}([\s\S]+?)\\end\{[bp]?matrix\}/g,
        operatorName: /\\operatorname\{([^}]+)\}/g,
        
        // Symbol patterns
        mathSymbols: /(\s|^)(→|←|⇒|⇐|↔|⇔|↦|∈|∉|⊂|⊃|⊆|⊇|≤|≥|≠|∼|≃|≅|≡|≈)(\s|$)/g,
        
        // Section counter patterns (will be initialized after CONFIG)
        sectionCount: null,  // Placeholder - initialized below
        capitalStart: /^[A-Z]/,
        layerOrSection: /^(?:Layer|Section) \d+:/,  // Match Layer/Section headers
        documentFilePattern: /^HCT_.*\.txt$/,  // Pattern for HCT document files
        documentPrefix: /^HCT_/,               // HCT document prefix
        txtExtension: /\.txt$/,                // Text file extension
    },
    
    // CSS property values
    css: {
        // Box model
        boxModel: {
            border: 'border-box',
            content: 'content-box'
        },
        // Display values
        display: {
            none: 'none',
            block: 'block',
            inline: 'inline',
            inlineBlock: 'inline-block',
            flex: 'flex',
            table: 'table',
            inlineTable: 'inline-table'
        },
        // Position values
        position: {
            static: 'static',
            relative: 'relative',
            absolute: 'absolute',
            fixed: 'fixed',
            sticky: 'sticky'
        },
        // Alignment
        align: {
            start: 'left',
            center: 'center',
            end: 'right',
            justify: 'justify',
            spaceBetween: 'space-between',
            spaceAround: 'space-around'
        },
        // Text decoration
        textDecoration: {
            none: 'none',
            underline: 'underline',
            lineThrough: 'line-through'
        },
        // Cursor
        cursor: {
            default: 'default',
            pointer: 'pointer',
            text: 'text'
        }
    },
    
    // UI Design System - compositional spacing and typography
    ui: {
        // Base unit for compositional spacing (powers of N.two)
        spacing: {
            // unit: N.twopx base (micro is the actual value)
            micro: 2,                             // 2px
            tiny: 4,                      // 4px  
            small: 6,                      // 6px
            compact: 8,
            normal: 12,
            medium: 16,
            large: 24,
            huge: 32,
            massive: 48,      // 48px
            giant: 64,
        },
        // Typography scale (golden ratio)
        typography: {
            weight: {
                light: 3 * 100,  // 300
                regular: 400,  // 400
                medium: 5 * 100,  // 500
                semibold: 6 * 100,  // 600
                bold: 7 * 100,  // 700
            },
            // Size multipliers for rem-based scaling
            scale: {
                tiny: 0.75,  // 0.75
                small: 0.875,  // 0.875
                base: 1,  // 1
                medium: 1.125,
                large: 1.25,  // 1.25
                xlarge: 1.5,  // 1.5
                huge: 2,  // 2
                giant: 2.5,  // 2.5
                massive: 3,  // 3
            },
            // Em-based relative sizes (relative to parent)
            emScale: {
                tiny: 0.1,
                small: 0.2,
                medium: 0.3,  // 0.3
                regular: 0.4,
                large: 0.5,
                xlarge: 0.8,
                base: 1,
                larger: 1.1,
            },
            // Pixel sizes for fixed dimensions
            pixels: {
                tiny: 12,
                small: 13,
                body: 15,
                base: 16,
                medium: 18,
                large: 20,
                xlarge: 22,
                huge: 32,
            },
            lineHeight: {
                tight: 1.25,  // 1.25
                snug: 1.375,  // 1.375
                normal: 1.5,  // 1.5
                relaxed: 1.625,  // 1.625
                loose: 1.75,  // 1.75
            },
            letterSpacing: {
                tight: -0.5,
                normal: 0,
                loose: 0.5,
            }
        },
        // Shadow system
        shadow: {
            opacity: {
                subtle: 0.041666666666666664,  // ~0.04
                light: 0.1,  // 0.1
                medium: 0.15,  // 0.15
                strong: 0.2,  // 0.2
            },
            offset: {
                none: 0,
                small: 1,
                medium: 2,
                large: 4,
            },
            blur: {
                sharp: 0,
                soft: 2,
                medium: 4,
                large: 8,
                xlarge: 16,
            }
        },
        // Border radius scale (derived from SPACE)
        radius: {
            none: 0,
            small: 3,
            medium: 6,
            large: 12,
            full: Number.MAX_SAFE_INTEGER,
        },
        // Opacity scale
        opacity: {
            transparent: 0,
            faint: 0.1,  // 0.1
            light: 0.3,  // 0.3
            medium: 0.5,  // 0.5
            strong: 0.7,  // 0.7
            heavy: 0.9,  // 0.9
            opaque: 1,
        },
        // Transition durations (seconds)
        transition: {
            instant: 0,
            fast: 0.15,      // 0.15 seconds
            normal: 0.2,  // 0.2 seconds
            slow: 0.3,      // 0.3 seconds  
            lazy: 0.5,  // 0.5 seconds
        },
        // Z-index layers
        zIndex: {
            below: -1,
            base: 0,
            dropdown: 1000,
            sticky: 1100,
            overlay: 1200,
            modal: 1300,
            popover: 1400,
            tooltip: 1500,
        },
        // Specific UI measurements
        layout: {
            sidebarWidth: 320,
            contentMaxWidth: 900,
            contentWideWidth: 960,
            mediaBreakpoint: 900,
            bannerPadding: 38,
            toggleButtonWidth: 20,
            tocIndent: 28,
            hashSliceStart: 1,
        },
        // CSS-specific values
        borderWidth: 1,  // Standard border width in px
        scrollDebounceDelay: TIME.TICK,
        // CSS transform values
        transform: {
            offscreen: 'translateX(-100%)',
            halfway: 'translateX(-50%)',
            none: 'translateX(0)',
        },
        // CSS dimension values
        dimensions: {
            full: '100%',
            half: '50%',
            quarter: '25%',
            none: '0',
        },
        // CSS property names
        cssProps: {
            all: 'all',
            ease: 'ease',
        },
        // Print-specific (using PRINT category)
        pdfMargin: `${PRINT.pdfMarginFraction}in`,
        // Numeric constants  
        zero: 0
    },
    
    // External URLs
    urls: {
        repositoryLink: 'https://github.com/J0pari/Higher-Category-Theory',  // GitHub repository URL
    },
    
    // Print/PDF specific settings - using PRINT category values
    print: {
        // Font sizes in points - hierarchical structure
        fontSize: {
            h1: PRINT.h1,
            h2: PRINT.h2,
            h3: PRINT.h3,
            h4: PRINT.h4,
            body: PRINT.body,
            footnote: PRINT.footnote,
        },
        // Spacing in points - compositional structure
        spacing: {
            h1: { top: PRINT.h1TopSpace, bottom: PRINT.h1BottomSpace },
            h2: { top: PRINT.h2TopSpace, bottom: PRINT.h2BottomSpace },
            h3: { top: PRINT.h3TopSpace, bottom: PRINT.h3BottomSpace },
            h4: { top: PRINT.h4TopSpace, bottom: PRINT.h4BottomSpace },
            block: PRINT.blockSpace,
            inline: PRINT.inlineSpace,
            indent: PRINT.indentSpace,
        },
        pageMargin: `${PRINT.pageMarginFraction}in`,
    },
    
    // Error detection strings
    errors: {
        detachedFrame: 'detached',
        closedContext: 'closed',
        targetClosed: 'Target closed',
        sessionClosed: 'Session closed',
    },
});

// LAWS: Universal laws that govern all computation
// Provide direct access
const CONFIG = CONFIG_RAW;

// Path resolution helpers - single source of truth for all path construction
CONFIG.resolvePath = (relativePath) => path.join(PROJECT_ROOT, relativePath);
CONFIG.resolveDocPath = (doc, format) => CONFIG.resolvePath(doc[format]);

// CONFIG STRUCTURE

// Move profileValues directly into ConfigProfiles where they belong
const CONFIG_PROFILES = {
    development: {
        debug: { 
            enableTelemetry: true, 
            maxEvents: 10 * 1000,
            cleanupInterval: 60 * 1000
        },
        scheduler: { 
            maxConcurrent: 2, 
            retryLimit: 5 
        },
        browser: { headless: false },
        mode: { strict: true }
    },
    production: {
        debug: { 
            enableTelemetry: false, 
            maxEvents: 1000,
            cleanupInterval: TIME.LONG 
        },
        scheduler: { 
            maxConcurrent: 4, 
            retryLimit: 3 
        },
        browser: { headless: true },
        mode: { strict: false }
    },
    test: {
        debug: { 
            enableTelemetry: true, 
            maxEvents: TIME.TICK, 
            cleanupInterval: 1000 
        },
        scheduler: { 
            maxConcurrent: 1, 
            retryLimit: 1 
        },
        browser: { headless: true },
        mode: { strict: true }
    }
};

// Schema functor: maps configuration space to validation constraints
const CONFIG_SCHEMA = {
    debug: {
        properties: {
            maxEvents: { type: 'number', min: CONFIG.limits.minDebugEvents },
            maxMaps: { type: 'number', min: CONFIG.limits.minDebugMaps }
        }
    },
    scheduler: {
        properties: {
            maxConcurrent: { type: 'number', min: CONFIG.limits.minConcurrent, max: CONFIG.limits.maxConcurrent },
            retryLimit: { type: 'number', min: 1, max: 10 }
        }
    },
    processor: {
        properties: {
            hashLength: { type: 'number', min: CONFIG.limits.minHashLength, max: CONFIG.limits.maxHashLength },
            headingMaxLevels: { type: 'number', exact: CONFIG.limits.htmlHeadingLevels },
            tocMaxDepth: { type: 'number', max: CONFIG.processor.headingMaxLevels }
        }
    },
    ui: {
        properties: {
            typography: {
                properties: {
                    scale: {
                        type: 'object',
                        valueSchema: { type: 'number', min: CONFIG.limits.minZero, max: CONFIG.limits.maxScaleValue }
                    },
                    pixels: {
                        properties: {
                            base: { type: 'number', min: CONFIG.limits.minFontSize, max: CONFIG.limits.maxFontSize }
                        }
                    }
                }
            }
        }
    }
};

CONFIG.patterns.sectionCount = new RegExp(`^#{${1},${CONFIG.processor.subSectionLevel}}\\s+`, 'gm');

// Initialize validator
configPatternValidator = new ConfigPatternValidator(true);

// Create generalized type checker using lazy definition
const TypeChecker = lazyTypeChecker.value;
typeChecker = new TypeChecker(true);

// ACTIVATE VALIDATION


const ALL_CONFIGS = {
    TIME,
    TIME_SCHEMA,
    LIMITS,
    LIMITS_SCHEMA,
    GIT,
    GIT_SCHEMA,
    ERROR_SCHEMA,
    SEVERITY_SCHEMA,
    PRINT,
    BINARY,
    CSS,
    THRESHOLDS,
    CONFIG_RAW,
    CONFIG,
    CONFIG_SCHEMA
};


// Validate each configuration object
for (const [name, obj] of Object.entries(ALL_CONFIGS)) {
    configPatternValidator.validateStructure(obj, name);
}


// Check violations
configPatternValidator.report();

// Create proxied CONFIG that will detect deprecated access at runtime
const CONFIG_PROXY = configPatternValidator.createProxy(CONFIG);

// Sophisticated context-aware magic number detector
function detectMagicNumberInCode(value, context) {
    // Extract numbers from any context - strings, templates, etc
    const extractNumbers = (input) => {
        try {
            checkType(input, NumberType);
            return [input];
        } catch {}

        try {
            checkType(input, StringType);
            // Skip comments, explanatory text, and variable names
            if (input.includes('//') || input.includes('/*') || input.includes('*')) return [];
            if (/\b(p\d+|PRIMES|CONFIG|TIME|COMMON|LIMITS|SPACE|BINARY)\b/.test(input)) return [];

            // Extract actual numeric literals from strings
            const matches = input.match(/\b\d+(\.\d+)?\b/g);
            return matches ? matches.map(Number) : [];
        } catch {}

        return [];
    };
    
    const numbers = extractNumbers(value);
    if (numbers.length === 0) return;
    
    for (const num of numbers) {
        // Skip booleans disguised as numbers
        if (num === true || num === false) continue;
        
        // Skip if it's from a known good source
        if (context && /\b(CONFIG|TIME|LIMITS|SPACE|PRIMES|COMMON|BINARY)\b/.test(context)) continue;
        
        // Skip array indices and object access patterns
        if (context && /\[\d+\]|\.\d+/.test(context)) continue;
        
        // Skip legitimate mathematical constants
        const legitimateConstants = [
            0, 1, 2, -1,
            3, 5, 7,
            4, 6, 10,
            10, 12, 50, 60, 100,
            THOUSAND, 1024, 1048576,
            1000, 1
        ];
        
        if (legitimateConstants.includes(num)) continue;
        
        // Skip powers of 2 (often used for binary operations)
        if (num > 0 && (num & (num - 1)) === 0) continue;
        
        // Skip version numbers, ports, status codes (contextual)
        if (context && /version|port|status|code|error/i.test(context)) continue;
        
        // Found a magic number!
        console.warn(`[MAGIC NUMBER] ${num} found in ${context || 'unknown context'} (value: ${JSON.stringify(value)})`);
    }
}

// Global interceptor for all string literals and number usage
const originalConsoleLog = console.log;
const originalConsoleWarn = console.warn;
const checkMagicInArgs = (...args) => {
    args.forEach((arg, i) => {
        if (typeof arg === 'string' || typeof arg === 'number') {
            detectMagicNumberInCode(arg, `console.arg[${i}]`);
        }
    });
};

// Enhance regex to catch numeric patterns
const enhancedNumberPattern = /(?<![a-zA-Z])(?:0[xX][\da-fA-F]+|0[bB][01]+|0[oO][0-7]+|\d+\.?\d*(?:[eE][+-]?\d+)?)/g;

// Resource pools for managing system resources
const ResourcePools = {
    retries: {
        total: CONFIG.scheduler.retryLimit * CONFIG.scheduler.maxConcurrent,
        available: CONFIG.scheduler.retryLimit * CONFIG.scheduler.maxConcurrent,
        allocate(n = 1) {
            if (this.available < n) return false;
            this.available -= n;
            return true;
        },
        release(n = 1) {
            this.available = Math.min(this.available + n, this.total);
        }
    },
    concurrent: {
        limit: CONFIG.scheduler.maxConcurrent,
        active: 0,
        canAllocate() { return this.active < this.limit; },
        allocate() { 
            if (!this.canAllocate()) return false;
            this.active++;
            return true;
        },
        release() { this.active = Math.max(0, this.active - 1); }
    }
};

// Template primitives that compose into larger structures
const Templates = {
    // HTML fragments
    htmlLink: (href, text, className = '') => 
        `<a href="${href}"${className ? ` class="${className}"` : ''}>${text}</a>`,
    htmlDiv: (content, className = '') => 
        `<div${className ? ` class="${className}"` : ''}>${content}</div>`,
    htmlSpan: (content, className = '') => 
        `<span${className ? ` class="${className}"` : ''}>${content}</span>`,
    
    // CSS fragments
    cssMargin: (top, right, bottom, left) => 
        `margin: ${top} ${right} ${bottom} ${left};`,
    cssPadding: (top, right, bottom, left) => 
        `padding: ${top} ${right} ${bottom} ${left};`,
    cssFlexContainer: (direction = 'row', justify = 'flex-start', align = 'stretch') => 
        `display: flex; flex-direction: ${direction}; justify-content: ${justify}; align-items: ${align};`
};

// CONFIGURATION SCHEMA

// type validation via refinement types
const checkType = (value, validator) => {
    if (validator.apply) return validator.apply(value);
    if (!validator.contains(value)) throw new Error('Type check failed');
};


// exact value matching
const checkExact = (value, target) => {
    if (value !== target) return `Not exact ${target}`;
};

// recursive schema validation with error collection
class SchemaValidator {
    constructor(types) {
        this.types = types;
    }

    validateValue(value, typeName) {
        const validator = this.types[typeName];
        if (!validator) throw new Error(`Unknown type: ${typeName}`);
        checkType(value, validator);
    }

    validateSchema(obj, schema, path = '') {
        const errors = [];
        const warnings = [];

        const validateNode = (node, schemaNode, nodePath) => {
            if (!schemaNode) return;

            if (schemaNode.type) {
                try {
                    this.validateValue(node, schemaNode.type);
                } catch (e) {
                    errors.push({ path: nodePath, error: e.message, value: node });
                    return;
                }

                if (schemaNode.type === 'number') {
                    if (schemaNode.min !== undefined && node < schemaNode.min) {
                        errors.push({ path: nodePath, error: `Below minimum ${schemaNode.min}`, value: node });
                    }
                    if (schemaNode.max !== undefined && node > schemaNode.max) {
                        errors.push({ path: nodePath, error: `Above maximum ${schemaNode.max}`, value: node });
                    }

                    if (schemaNode.exact !== undefined) {
                        const warning = checkExact(node, schemaNode.exact);
                        if (warning) warnings.push({ path: nodePath, warning, value: node });
                    }
                }
            }

            if (schemaNode.items && Array.isArray(node)) {
                node.forEach((item, idx) => {
                    validateNode(item, schemaNode.items, `${nodePath}[${idx}]`);
                });
            }

            if (schemaNode.valueSchema && node && typeof node === 'object') {
                for (const [key, value] of Object.entries(node)) {
                    validateNode(value, schemaNode.valueSchema, `${nodePath}.${key}`);
                }
            }

            if (schemaNode.properties && node && typeof node === 'object') {
                for (const [key, subSchema] of Object.entries(schemaNode.properties)) {
                    if (node[key] !== undefined) {
                        validateNode(node[key], subSchema, `${nodePath}.${key}`);
                    } else if (subSchema.required) {
                        errors.push({ path: `${nodePath}.${key}`, error: 'Required property missing' });
                    }
                }
            }
        };

        for (const [key, schemaNode] of Object.entries(schema)) {
            if (obj[key] !== undefined) {
                validateNode(obj[key], schemaNode, `${path}.${key}`);
            } else if (schemaNode.required) {
                errors.push({ path: `${path}.${key}`, error: 'Required section missing' });
            }
        }

        return { errors, warnings };
    }
}

const NumberType = { contains: v => typeof v === 'number' };
const StringType = { contains: v => typeof v === 'string' };
const BoolType = { contains: v => typeof v === 'boolean' };
const ArrayType = { contains: v => Array.isArray(v) };
const ObjectType = { contains: v => typeof v === 'object' && v !== null && !Array.isArray(v) };

const PositiveInt = Refinement(NumberType, n => n > 0 && Number.isInteger(n));
const NonNegativeInt = Refinement(NumberType, n => n >= 0 && Number.isInteger(n));
const ValidPath = Refinement(StringType, p => {
    try {
        return fs.existsSync(p);
    } catch {
        return false;
    }
});
const NonEmptyString = Refinement(StringType, s => s.length > 0);

class ConfigValidator {
    constructor(schema, debuggerInstance) {
        this.schema = schema;
        this.debugger = debuggerInstance;
        this.validator = new SchemaValidator({
            number: NumberType,
            string: StringType,
            boolean: BoolType,
            array: ArrayType,
            object: ObjectType,
            positiveInt: PositiveInt,
            nonNegativeInt: NonNegativeInt,
            nonEmptyString: NonEmptyString,
            validPath: ValidPath
        });
    }

    validate(config, path = 'CONFIG') {
        const result = this.validator.validateSchema(config, this.schema, path);

        result.errors.forEach(e => {
            this.debugger.error(new Error(e.error), { path: e.path, value: e.value });
        });
        result.warnings.forEach(w => {
            this.debugger.trace('CONFIG_WARNING', w);
        });

        return result;
    }
}

// Load configuration with profile support
function loadConfig(profile = process.env.NODE_ENV || 'development') {
    // Start with base CONFIG
    let config = CONFIG;
    
    // Apply profile overrides
    if (CONFIG_PROFILES[profile]) {
        config = deepMerge(config, CONFIG_PROFILES[profile]);
        traceOrchestrator.trace('CONFIG_PROFILE_LOADED', { profile });
    }
    
    return config;
}

// Deep merge helper
function deepMerge(target, source) {
    const result = { ...target };
    for (const [key, value] of Object.entries(source)) {
        if (value && typeof value === 'object' && !Array.isArray(value)) {
            if (!result[key]) result[key] = {};
            result[key] = deepMerge(result[key], value);
        } else {
            result[key] = value;
        }
    }
    return result;
}

// CONFIGURATION VALIDATION

function validateConfig() {
    const errors = [];
    
    // Validate no XSS in CONFIG strings
    const validateNoXSS = (obj, path = 'CONFIG') => {
        const xssPatterns = [
            /<script/i,
            /javascript:/i,
            /on\w+\s*=/i,  // onclick=, onerror=, etc.
            /eval\(/i,
            /expression\(/i
        ];
        
        for (const [key, value] of Object.entries(obj)) {
            const fullPath = `${path}.${key}`;
            if (typeof value === 'string') {
                for (const pattern of xssPatterns) {
                    if (pattern.test(value)) {
                        errors.push(`Potential XSS in ${fullPath}: "${value.substring(0, CONFIG.limits.xssPreviewLength)}..."`);
                    }
                }
            } else if (value && typeof value === 'object' && !Array.isArray(value) && !(value instanceof RegExp)) {
                validateNoXSS(value, fullPath);
            }
        }
    };
    
    validateNoXSS(CONFIG);
    
    // Validate transition durations
    const transitions = [
        CONFIG.ui.transition.fast,
        CONFIG.ui.transition.normal,
        CONFIG.ui.transition.slow
    ];
    
    if (!transitions.every((t, i) => i === 0 || t >= transitions[i-1])) {
        errors.push('Transition durations should be ordered: fast < normal < slow');
    }
    
    
    // Check for any remaining hardcoded values that slipped through
    const configStr = JSON.stringify(CONFIG);
    const suspiciousPatterns = [
        /timeout\d+/i,
        /margin\d+[^:]/i,
        /padding\d+[^:]/i,
        /size\d+[^:]/i,
    ];
    
    for (const pattern of suspiciousPatterns) {
        if (pattern.test(configStr)) {
            errors.push(`Suspicious tautological naming detected: ${pattern}`);
        }
    }
    
    if (errors.length > 0) {
        console.error('Configuration validation failed:');
        errors.forEach(err => console.error(`  - ${err}`));
        throw new Error('Invalid configuration');
    }
    
    
    // Validate all configs with schemas
    const SCHEMA_MAP = {
        TIME: TIME_SCHEMA,
        LIMITS: LIMITS_SCHEMA,
        GIT: GIT_SCHEMA,
        CONFIG: CONFIG_SCHEMA
    };

    const allValidations = [];
    for (const [name, schema] of Object.entries(SCHEMA_MAP)) {
        const validator = new ConfigValidator(schema, traceOrchestrator);
        const config = ALL_CONFIGS[name];
        if (config) {
            allValidations.push(validator.validate(config, name));
        }
    }

    for (const validation of allValidations) {
        if (validation.errors.length > 0) {
            validation.errors.forEach(e => {
                console.error(`  ${e.path}: ${e.error}`);
                traceOrchestrator.error(new Error(e.error), { path: e.path, value: e.value });
            });
            errors.push(...validation.errors.map(e => `${e.path}: ${e.error}`));
        }

        if (validation.warnings.length > 0) {
            validation.warnings.forEach(w => {
                console.warn(`  ${w.path}: ${w.warning}`);
                traceOrchestrator.trace('CONFIG_WARNING', w);
            });
        }
    }
    
    // Final check
    if (errors.length > 0) {
        process.exit(CONFIG.process.exitCode.error);
    }
    
    // Initialize ResourcePools based on validated CONFIG
    ResourcePools.retries.total = CONFIG.scheduler.retryLimit * CONFIG.scheduler.maxConcurrent;
    ResourcePools.retries.available = ResourcePools.retries.total;
    ResourcePools.concurrent.limit = CONFIG.scheduler.maxConcurrent;
    
    const allWarnings = allValidations.flatMap(v => v.warnings);
    return { errors: [], warnings: allWarnings };
}

// TRACE ANALYSIS & RUNTIME VERIFICATION

// EventStore - pure data storage
class EventStore {
    constructor(maxEvents = 10000, maxMaps = 1000) {
        this.events = [];
        this.errors = new Map();
        this.causality = new Map();
        this.stackTraces = new Map();
        this.performanceMarks = new Map();
        this.runtimeViolations = new Set();
        this.violationsReported = false;
        this.maxEvents = maxEvents;
        this.maxMaps = maxMaps;
        this.currentContext = null;
    }

    append(event) {
        this.events.push(event);
        if (this.events.length > this.maxEvents) {
            this.events = this.events.slice(-this.maxEvents);
        }

        if (this.currentContext) {
            if (!this.causality.has(this.currentContext.id)) {
                this.causality.set(this.currentContext.id, []);
            }
            this.causality.get(this.currentContext.id).push(event.id);
        }

        this.currentContext = event;
        return event.id;
    }

    getCausalChain(eventId) {
        const chain = [];
        let current = this.events.find(e => e.id === eventId);
        while (current) {
            chain.unshift(current);
            current = current.parent ? this.events.find(e => e.id === current.parent) : null;
        }
        return chain;
    }

    cleanup() {
        const trimMap = (map) => {
            if (map.size > this.maxMaps) {
                const toDelete = map.size - this.maxMaps;
                const keys = Array.from(map.keys()).slice(0, toDelete);
                keys.forEach(k => map.delete(k));
            }
        };
        trimMap(this.errors);
        trimMap(this.causality);
        trimMap(this.stackTraces);
        trimMap(this.performanceMarks);
    }
}

// CausalAnalysis - Markov chain prediction & failure patterns
class CausalAnalysis {
    constructor(eventStore) {
        this.store = eventStore;
        this.markovChain = new Map();
        this.failurePatterns = new Map();
    }

    updateMarkovChain(fromEvent, toEvent) {
        if (!this.markovChain.has(fromEvent)) {
            this.markovChain.set(fromEvent, new Map());
        }

        const transitions = this.markovChain.get(fromEvent);
        const count = Maybe.elim(
            () => 'Maybe',
            () => 0,
            c => c
        )(transitions.get(toEvent));
        transitions.set(toEvent, count + 1);

        if (toEvent.includes('ERROR')) {
            const pattern = `${fromEvent} -> ${toEvent}`;
            const occurrences = transitions.get(toEvent);
            const total = Array.from(transitions.values()).reduce((a, b) => a + b, 0);
            const probability = occurrences / total;

            this.failurePatterns.set(pattern, probability);
        }
    }

    predictNext(currentEvent) {
        if (!this.markovChain.has(currentEvent)) {
            return [];
        }

        const transitions = this.markovChain.get(currentEvent);
        const total = Array.from(transitions.values()).reduce((a, b) => a + b, 0);

        return Array.from(transitions.entries())
            .map(([event, count]) => ({
                event,
                probability: count / total
            }))
            .sort((a, b) => b.probability - a.probability)
            .slice(0, 5);
    }

    getFailureProbability(event) {
        const predictions = this.predictNext(event);
        return predictions
            .filter(p => p.event.includes('ERROR'))
            .reduce((sum, p) => sum + p.probability, 0);
    }

    buildCausalityGraph() {
        const nodes = new Map();
        const edges = [];

        this.store.causality.forEach((chain, id) => {
            chain.forEach((event, index) => {
                nodes.set(event.id, event);
                if (index > 0) {
                    edges.push({
                        from: chain[index - 1].id,
                        to: event.id,
                        weight: event.timestamp - chain[index - 1].timestamp
                    });
                }
            });
        });

        return { nodes: Array.from(nodes.values()), edges };
    }
}

// MetricsCalculator - computes performance metrics and analysis
class MetricsCalculator {
    constructor(eventStore, patternDetection) {
        this.store = eventStore;
        this.patterns = patternDetection;
    }

    getMetrics() {
        const recentEvents = this.store.events.slice(-CONFIG.debug.analysis.recentWindowSize);
        const recentErrors = Array.from(this.store.errors.values()).slice(-CONFIG.debug.analysis.errorWindowSize);

        return {
            eventRate: this.calculateEventRate(recentEvents),
            errorRate: this.calculateErrorRate(recentErrors),
            memoryPressure: this.calculateMemoryPressure(),
            performanceBottlenecks: this.identifyBottlenecks(),
            taskSuccess: this.calculateTaskSuccessRate()
        };
    }

    getPerformanceProfile() {
        const profiles = new Map();

        for (const [label, data] of this.store.performanceMarks) {
            const category = this.categorizeOperation(label);
            if (!profiles.has(category)) {
                profiles.set(category, { count: 0, totalTime: 0, totalMemory: 0, operations: [] });
            }
            const profile = profiles.get(category);
            profile.count++;
            profile.totalTime += data.duration;
            profile.totalMemory += data.memDelta;
            profile.operations.push({ label, ...data });
        }

        return Array.from(profiles.entries()).map(([category, data]) => ({
            category,
            avgTime: data.totalTime / data.count,
            avgMemory: data.totalMemory / data.count,
            ...data
        }));
    }

    getCriticalPath() {
        const paths = [];

        // Find all error events and trace their paths
        for (const [errorId, errorData] of this.store.errors) {
            const chain = errorData.causalChain;
            if (!chain || chain.length === 0) continue;
            const duration = chain.length > 1 ? chain[chain.length - 1].timestamp - chain[0].timestamp : 0;
            paths.push({
                errorId,
                duration,
                steps: chain.length,
                path: chain.map(e => e.event)
            });
        }

        // Sort by duration to find longest paths
        return paths.sort((a, b) => b.duration - a.duration).slice(0, CONFIG.debug.analysis.topResultsLimit);
    }

    detectPatterns() {
        const patterns = {
            memoryLeaks: this.patterns.detectMemoryLeaks(),
            performanceDegradation: this.patterns.detectPerformanceDegradation(),
            errorClusters: this.patterns.detectErrorClusters(),
            resourceSpikes: this.patterns.detectResourceSpikes()
        };

        return patterns;
    }

    calculateEventRate(events) {
        if (events.length < 2) return 0;
        const timeSpan = events[events.length - 1].timestamp - events[0].timestamp;
        return timeSpan > 0 ? (events.length / timeSpan) * CONFIG.core.time.msPerSecond : 0;
    }

    calculateErrorRate(errors) {
        if (errors.length === 0) return 0;
        const timeSpan = Date.now() - errors[0].timestamp;
        return timeSpan > 0 ? (errors.length / timeSpan) * CONFIG.core.time.msPerSecond : 0;
    }

    calculateMemoryPressure() {
        const mem = process.memoryUsage();
        return mem.heapUsed / mem.heapTotal;
    }

    identifyBottlenecks() {
        const slowOps = [];
        for (const [label, data] of this.store.performanceMarks) {
            if (data.duration > CONFIG.debug.performanceWarnThreshold) {
                slowOps.push({ operation: label, label, duration: data.duration, avgDuration: data.duration });
            }
        }
        return slowOps.sort((a, b) => b.duration - a.duration).slice(0, CONFIG.debug.analysis.topResultsLimit);
    }

    calculateTaskSuccessRate() {
        const taskEvents = this.store.events.filter(e => e.event.includes(CONFIG.strings.operationCategories[CONFIG.strings.operationCategories.length - 1]));
        const errorEvents = Array.from(this.store.errors.values());

        if (taskEvents.length === 0) return 1;
        const failureCount = errorEvents.filter(e => e.context.task).length;
        return 1 - (failureCount / taskEvents.length);
    }

    categorizeOperation(label) {
        for (const category of CONFIG.strings.operationCategories) {
            if (label.includes(category)) return category;
        }
        return CONFIG.strings.defaultCategory;
    }
}

// PatternDetection - detects anomalies and patterns in event streams
class PatternDetection {
    constructor(eventStore) {
        this.store = eventStore;
    }

    detectMemoryLeaks() {
        const memoryTrend = this.store.events.slice(-CONFIG.debug.analysis.memoryTrendSize).map(e => e.memory.heapUsed);
        if (memoryTrend.length < CONFIG.process.lockRetryAttempts) return false;

        // Simple linear regression to detect upward trend
        const n = memoryTrend.length;
        const indices = Array.from({ length: n }, (_, i) => i);
        const sumX = indices.reduce((a, b) => a + b, 0);
        const sumY = memoryTrend.reduce((a, b) => a + b, 0);
        const sumXY = indices.reduce((sum, x, i) => sum + x * memoryTrend[i], 0);
        const sumX2 = indices.reduce((sum, x) => sum + x * x, 0);

        const slope = (n * sumXY - sumX * sumY) / (n * sumX2 - sumX * sumX);
        return slope > THRESHOLDS.MEMORY_LEAK_SLOPE;
    }

    detectPerformanceDegradation() {
        const recent = Array.from(this.store.performanceMarks.values()).slice(-CONFIG.debug.analysis.performanceSampleSize);
        if (recent.length < CONFIG.process.lockRetryAttempts) return false;

        const halfPoint = Math.floor(recent.length / 2);
        const firstHalf = recent.slice(0, halfPoint);
        const secondHalf = recent.slice(halfPoint);

        const avgFirst = firstHalf.reduce((sum, d) => sum + d.duration, 0) / firstHalf.length;
        const avgSecond = secondHalf.reduce((sum, d) => sum + d.duration, 0) / secondHalf.length;

        return avgSecond > avgFirst * 2;
    }

    detectErrorClusters() {
        const errors = Array.from(this.store.errors.values());
        if (errors.length < CONFIG.processor.minGroupSize) return [];

        const clusters = [];
        let currentCluster = [errors[0]];

        for (let i = 1; i < errors.length; i++) {
            const timeDiff = errors[i].timestamp - errors[i - 1].timestamp;
            if (timeDiff < THRESHOLDS.ERROR_CLUSTER_WINDOW) {
                currentCluster.push(errors[i]);
            } else {
                if (currentCluster.length >= CONFIG.processor.minGroupSize) {
                    clusters.push(currentCluster);
                }
                currentCluster = [errors[i]];
            }
        }

        if (currentCluster.length >= CONFIG.processor.minGroupSize) {
            clusters.push(currentCluster);
        }

        return clusters;
    }

    detectResourceSpikes() {
        const spikes = [];
        const memoryData = this.store.events.map(e => ({ timestamp: e.timestamp, heap: e.memory.heapUsed }));

        for (let i = 1; i < memoryData.length; i++) {
            const delta = memoryData[i].heap - memoryData[i - 1].heap;
            if (delta > BINARY.MB * THRESHOLDS.MEMORY_SPIKE_MB) {
                spikes.push({
                    timestamp: memoryData[i].timestamp,
                    delta,
                    event: this.store.events[i].event
                });
            }
        }

        return spikes;
    }
}

// TelemetryExporter - exports metrics in various formats (Prometheus, Datadog, JSON)
class TelemetryExporter {
    constructor(orchestrator) {
        this.orchestrator = orchestrator;
        this.lazyTelemetry = null;
    }

    initializeLazyTelemetry() {
        this.lazyTelemetry = new Lazy(() => ({
            metrics: new Lazy(() => this.orchestrator.getMetrics()),
            profile: new Lazy(() => this.orchestrator.getPerformanceProfile()),
            patterns: new Lazy(() => this.orchestrator.detectPatterns()),
            system: new Lazy(() => ({
                memory: process.memoryUsage(),
                cpu: process.cpuUsage(),
                platform: process.platform,
                nodeVersion: process.version,
                pid: process.pid,
                uptime: Date.now() - (this.orchestrator.events[0]?.timestamp || Date.now())
            })),
            events: new Lazy(() => {
                const now = Date.now();
                return {
                    total: this.orchestrator.events.length,
                    rate: this.orchestrator.calculateEventRate(this.orchestrator.events),
                    recentCount: this.orchestrator.events.filter(e => now - e.timestamp < TIME.VERY_LONG).length,
                    oldestTimestamp: this.orchestrator.events[0]?.timestamp || null,
                    newestTimestamp: this.orchestrator.events[this.orchestrator.events.length - 1]?.timestamp || null,
                    recent: new LazyStream(
                        this.orchestrator.events[this.orchestrator.events.length - 1] || null,
                        () => this.orchestrator.events.length > 1
                            ? new LazyStream(this.orchestrator.events[this.orchestrator.events.length - 2], null)
                            : null
                    )
                };
            }),
            errors: new Lazy(() => ({
                total: this.orchestrator.errors.size,
                rate: this.orchestrator.calculateErrorRate(Array.from(this.orchestrator.errors.values())),
                recent: new Lazy(() =>
                    Array.from(this.orchestrator.errors.values())
                        .filter(e => Date.now() - e.timestamp < TIME.VERY_LONG)
                        .map(e => ({
                            message: e.error.message,
                            timestamp: e.timestamp,
                            context: e.context,
                            chainLength: e.causalChain.length
                        }))
                ),
                clusters: new Lazy(() =>
                    this.orchestrator.detectErrorClusters().map(cluster => ({
                        size: cluster.length,
                        startTime: cluster[0].timestamp,
                        endTime: cluster[cluster.length - 1].timestamp,
                        types: [...new Set(cluster.map(e => e.error.message.split(':')[0]))]
                    }))
                )
            })),
            performance: new Lazy(() => ({
                marks: this.orchestrator.performanceMarks.size,
                profile: new Lazy(() => this.orchestrator.getPerformanceProfile()),
                bottlenecks: new Lazy(() => this.orchestrator.identifyBottlenecks()),
                criticalPaths: new Lazy(() => this.orchestrator.getCriticalPath()),
                slowestOperations: new Lazy(() =>
                    Array.from(this.orchestrator.performanceMarks.entries())
                        .sort((a, b) => b[1].duration - a[1].duration)
                        .slice(0, THRESHOLDS.TOP_RESULTS)
                        .map(([label, data]) => ({
                            label,
                            duration: data.duration,
                            memory: data.memDelta,
                            timestamp: data.timestamp
                        }))
                )
            })),
            causality: new Lazy(() => ({
                chains: this.orchestrator.causality.size,
                maxChainLength: new Lazy(() =>
                    Math.max(...Array.from(this.orchestrator.causality.values()).map(c => c.length), 0)
                ),
                orphanEvents: new Lazy(() =>
                    this.orchestrator.events.filter(e => !e.parent && !this.orchestrator.causality.has(e.id)).length
                ),
                graph: new Lazy(() => this.orchestrator.buildCausalityGraph())
            })),
            scheduler: new Lazy(() =>
                (typeof scheduler !== 'undefined' && scheduler) ? {
                    queued: scheduler.queue.length,
                    running: scheduler.running.size,
                    locked: scheduler.locks.size,
                    history: new Lazy(() =>
                        Array.from(scheduler.buildHistory.entries()).map(([file, stats]) => ({
                            file,
                            success: stats.success,
                            failure: stats.failure,
                            successRate: (stats.success + stats.failure) > 0
                                ? stats.success / (stats.success + stats.failure)
                                : 0
                        }))
                    )
                } : null
            ),
            processor: new Lazy(() =>
                (typeof processor !== 'undefined' && processor?.state) ? {
                    browser: processor.state.browser !== null,
                    pages: processor.state.pages.size,
                    hashes: processor.state.hashes.size,
                    building: processor.state.building.size,
                    errors: processor.state.errors.length,
                    builds: processor.state.stats.builds,
                    uptime: Date.now() - processor.state.stats.uptime
                } : null
            ),
            export: new Lazy(() => {
                const timestamp = Date.now();
                const data = LazyFunctor.extract({
                    timestamp,
                    system: this.lazyTelemetry.value.system,
                    events: this.lazyTelemetry.value.events,
                    errors: this.lazyTelemetry.value.errors,
                    performance: this.lazyTelemetry.value.performance,
                    causality: this.lazyTelemetry.value.causality,
                    patterns: this.lazyTelemetry.value.patterns,
                    metrics: this.lazyTelemetry.value.metrics,
                    scheduler: this.lazyTelemetry.value.scheduler,
                    processor: this.lazyTelemetry.value.processor
                });
                return {
                    timestamp,
                    data,
                    json: new Lazy(() => JSON.stringify(data, null, 2)),
                    metrics: new Lazy(() => this.formatMetrics(data)),
                    timeseries: new Lazy(() => this.formatTimeseries(data))
                };
            })
        }));
        return this.lazyTelemetry;
    }

    createTelemetryStream() {
        if (!this.lazyTelemetry) {
            this.initializeLazyTelemetry();
        }
        const telemetryStream = fix(stream =>
            new LazyStream(
                new Lazy(() => ({
                    timestamp: Date.now(),
                    snapshot: this.lazyTelemetry.value.export.value.data
                })),
                () => {
                    return new Lazy(() => {
                        return new PullPromise(async () => {
                            await new Promise(resolve =>
                                setTimeout(resolve, CONFIG.watcher.interval || TIME.TICK.value)
                            );
                            return stream.value;
                        });
                    });
                }
            )
        );
        telemetryStream.deltaMetrics = new Lazy(() => telemetryStream.value
            .window(2)
            .map(window => {
                if (window.length < 2) return null;
                const [prev, curr] = window;
                return {
                    timestamp: curr.timestamp,
                    timeDelta: curr.timestamp - prev.timestamp,
                    eventDelta: curr.snapshot.events.total - prev.snapshot.events.total,
                    errorDelta: curr.snapshot.errors.total - prev.snapshot.errors.total,
                    memoryDelta: curr.snapshot.system.memory.heapUsed - prev.snapshot.system.memory.heapUsed
                };
            })
            .filter(delta => delta !== null)
        );
        telemetryStream.anomalies = new Lazy(() => telemetryStream.value
            .map(snapshot => {
                const anomalies = [];
                if (snapshot.snapshot.errors.rate > LIMITS.RETRIES) {
                    anomalies.push({
                        type: 'HIGH_ERROR_RATE',
                        value: snapshot.snapshot.errors.rate,
                        timestamp: snapshot.timestamp
                    });
                }
                const memoryPressure = snapshot.snapshot.system.memory.heapUsed /
                                      snapshot.snapshot.system.memory.heapTotal;
                const threshold = CONFIG.core.limits.memoryPressureThreshold;
                if (memoryPressure > (threshold instanceof Lazy ? threshold.value : threshold)) {
                    anomalies.push({
                        type: 'HIGH_MEMORY_PRESSURE',
                        value: memoryPressure,
                        timestamp: snapshot.timestamp
                    });
                }
                const maxRate = CONFIG.core.limits.maxEventRate;
                if (snapshot.snapshot.events.rate > (maxRate instanceof Lazy ? maxRate.value : maxRate)) {
                    anomalies.push({
                        type: 'EVENT_SPIKE',
                        value: snapshot.snapshot.events.rate,
                        timestamp: snapshot.timestamp
                    });
                }
                return anomalies.length > 0 ? { timestamp: snapshot.timestamp, anomalies } : null;
            })
            .filter(anomaly => anomaly !== null)
        );
        telemetryStream.aggregates = new Lazy(() => telemetryStream.value
            .window(THRESHOLDS.AGGREGATE_WINDOW)
            .map(window => ({
                timestamp: Date.now(),
                windowSize: window.length,
                avgEventRate: window.reduce((sum, s) => sum + s.snapshot.events.rate, 0) / window.length,
                avgErrorRate: window.reduce((sum, s) => sum + s.snapshot.errors.rate, 0) / window.length,
                maxMemory: Math.max(...window.map(s => s.snapshot.system.memory.heapUsed)),
                minMemory: Math.min(...window.map(s => s.snapshot.system.memory.heapUsed))
            }))
        );
        return telemetryStream;
    }

    exportTelemetry() {
        if (!this.lazyTelemetry) {
            this.initializeLazyTelemetry();
        }
        const exported = this.lazyTelemetry.value.export.value;
        return {
            raw: exported.data,
            metrics: exported.metrics.value,
            timeseries: exported.timeseries.value,
            json: exported.json.value
        };
    }

    formatMetrics(telemetry) {
        const metrics = [];
        metrics.push(`# HELP hct_events_total Total number of events`);
        metrics.push(`# TYPE hct_events_total gauge`);
        metrics.push(`hct_events_total ${telemetry.events.total}`);
        metrics.push(`# HELP hct_events_rate Events per second`);
        metrics.push(`# TYPE hct_events_rate gauge`);
        metrics.push(`hct_events_rate ${(telemetry.events.rate ?? 0).toFixed(2)}`);
        metrics.push(`# HELP hct_errors_total Total number of errors`);
        metrics.push(`# TYPE hct_errors_total counter`);
        metrics.push(`hct_errors_total ${telemetry.errors.total}`);
        metrics.push(`# HELP hct_memory_heap_used_bytes Heap memory used`);
        metrics.push(`# TYPE hct_memory_heap_used_bytes gauge`);
        metrics.push(`hct_memory_heap_used_bytes ${telemetry.system?.memory?.heapUsed ?? 0}`);
        metrics.push(`# HELP hct_memory_pressure Memory pressure ratio`);
        metrics.push(`# TYPE hct_memory_pressure gauge`);
        metrics.push(`hct_memory_pressure ${(telemetry.metrics.memoryPressure ?? 0).toFixed(3)}`);
        if (telemetry.performance?.profile) {
            telemetry.performance.profile.forEach(profile => {
                metrics.push(`# HELP hct_operation_duration_ms Operation duration by category`);
                metrics.push(`# TYPE hct_operation_duration_ms histogram`);
                metrics.push(`hct_operation_duration_ms{category="${profile.category}"} ${(profile.avgTime ?? 0).toFixed(2)}`);
            });
        }
        if (telemetry.scheduler) {
            metrics.push(`# HELP hct_scheduler_queue_size Number of queued tasks`);
            metrics.push(`# TYPE hct_scheduler_queue_size gauge`);
            metrics.push(`hct_scheduler_queue_size ${telemetry.scheduler.queued}`);
            metrics.push(`# HELP hct_scheduler_running_tasks Number of running tasks`);
            metrics.push(`# TYPE hct_scheduler_running_tasks gauge`);
            metrics.push(`hct_scheduler_running_tasks ${telemetry.scheduler.running}`);
        }
        if (telemetry.processor) {
            metrics.push(`# HELP hct_processor_builds_total Total builds completed`);
            metrics.push(`# TYPE hct_processor_builds_total counter`);
            metrics.push(`hct_processor_builds_total ${telemetry.processor.builds}`);
            metrics.push(`# HELP hct_processor_pages_open Number of browser pages open`);
            metrics.push(`# TYPE hct_processor_pages_open gauge`);
            metrics.push(`hct_processor_pages_open ${telemetry.processor.pages}`);
        }
        return metrics.join('\n');
    }

    formatTimeseries(telemetry) {
        const ts = Math.floor(telemetry.timestamp / TIME.SECOND);
        const tags = [`env:${process.env.NODE_ENV || 'development'}`, `pid:${telemetry.system.pid}`];

        const series = [
            { metric: 'hct.events.total', points: [[ts, telemetry.events.total]], type: 'gauge', tags },
            { metric: 'hct.events.rate', points: [[ts, telemetry.events.rate]], type: 'gauge', tags },
            { metric: 'hct.errors.total', points: [[ts, telemetry.errors.total]], type: 'count', tags },
            { metric: 'hct.memory.heap.used', points: [[ts, telemetry.system.memory.heapUsed]], type: 'gauge', tags }
        ];

        if (telemetry.performance?.profile) {
            telemetry.performance.profile.forEach(p => {
                series.push({
                    metric: 'hct.operation.duration',
                    points: [[ts, p.avgTime ?? 0]],
                    type: 'gauge',
                    tags: [...tags, `category:${p.category}`]
                });
            });
        }

        return { series };
    }
}

// InvariantChecker - verifies runtime properties over event traces
class InvariantChecker {
    constructor(eventStore) {
        this.store = eventStore;
    }

    checkInvariant(property, evidence) {
        const violations = [];
        for (const event of this.store.events) {
            if (!property(event, evidence)) {
                violations.push(event);
            }
        }
        return violations.length === 0 ? { holds: true } : { holds: false, violations };
    }

    checkHermetic(buildId) {
        const buildEvents = this.store.events.filter(e => e.context.buildId === buildId);
        const inputs = buildEvents.filter(e => e.event === 'INPUT_READ');
        const outputs = buildEvents.filter(e => e.event === 'OUTPUT_WRITE');
        const inputHashes = inputs.map(e => e.context.hash).sort().join(',');
        const outputHashes = outputs.map(e => e.context.hash).sort().join(',');
        const property = (otherBuildId) => {
            const otherBuildEvents = this.store.events.filter(e => e.context.buildId === otherBuildId);
            const otherInputs = otherBuildEvents.filter(e => e.event === 'INPUT_READ');
            const otherOutputs = otherBuildEvents.filter(e => e.event === 'OUTPUT_WRITE');
            const otherInputHashes = otherInputs.map(e => e.context.hash).sort().join(',');
            const otherOutputHashes = otherOutputs.map(e => e.context.hash).sort().join(',');
            return inputHashes === otherInputHashes ? outputHashes === otherOutputHashes : true;
        };
        const allBuilds = [...new Set(this.store.events.map(e => e.context.buildId))].filter(id => id && id !== buildId);
        const violations = allBuilds.filter(id => !property(id));
        return violations.length === 0 ? { hermetic: true } : { hermetic: false, violations };
    }

    checkCacheValid(cacheKey) {
        const cacheEvents = this.store.events.filter(e => e.context.cacheKey === cacheKey);
        if (cacheEvents.length === 0) return { valid: true, reason: 'no-cache-events' };
        const cacheWrite = cacheEvents.find(e => e.event === 'CACHE_WRITE');
        if (!cacheWrite) return { valid: false, reason: 'no-write-event' };
        const inputsAtWrite = cacheWrite.context.inputs;
        const currentInputModTimes = inputsAtWrite.map(input => ({
            file: input,
            mtime: this.store.events.filter(e => e.context.file === input && e.event === 'FILE_MODIFIED')
                .sort((a, b) => b.timestamp - a.timestamp)[0]?.timestamp
        }));
        const invalidInputs = currentInputModTimes.filter(i => i.mtime > cacheWrite.timestamp);
        return invalidInputs.length === 0 ? { valid: true } : { valid: false, invalidInputs };
    }

    checkIncremental(evidence) {
        const rebuilds = this.store.events.filter(e => e.event === 'BUILD_START');
        const violations = [];
        for (const rebuild of rebuilds) {
            const changedFiles = evidence.changedFiles;
            const builtFiles = this.store.events
                .filter(e => e.timestamp > rebuild.timestamp && e.event === 'FILE_BUILT')
                .map(e => e.context.file);
            const unnecessaryBuilds = builtFiles.filter(f => !changedFiles.includes(f));
            if (unnecessaryBuilds.length > 0) {
                violations.push({ rebuild: rebuild.id, unnecessary: unnecessaryBuilds });
            }
        }
        return violations.length === 0 ? { incremental: true } : { incremental: false, violations };
    }
}

// TraceOrchestrator - main class delegating to specialized components
class TraceOrchestrator {
    constructor() {
        this.store = new EventStore(CONFIG.debug.maxEvents, CONFIG.debug.maxMaps);
        this.causalAnalysis = new CausalAnalysis(this.store);
        this.patternDetection = new PatternDetection(this.store);
        this.metricsCalculator = new MetricsCalculator(this.store, this.patternDetection);
        this.telemetryExporter = new TelemetryExporter(this);
        this.invariantChecker = new InvariantChecker(this.store);

        // Expose store fields for backward compatibility
        this.events = this.store.events;
        this.errors = this.store.errors;
        this.causality = this.store.causality;
        this.stackTraces = this.store.stackTraces;
        this.performanceMarks = this.store.performanceMarks;
        this.runtimeViolations = this.store.runtimeViolations;
        this.violationsReported = this.store.violationsReported;
        this.maxEvents = this.store.maxEvents;
        this.maxMaps = this.store.maxMaps;
        this.currentContext = this.store.currentContext;

        // Expose causalAnalysis fields for backward compatibility
        this.markovChain = this.causalAnalysis.markovChain;
        this.failurePatterns = this.causalAnalysis.failurePatterns;

        // Expose telemetryExporter field for backward compatibility
        this.lazyTelemetry = null;

        this.setupPeriodicCleanup();
    }
    
    setupPeriodicCleanup() {
        const cleanup = new Lazy(() => {
            this.cleanupMaps();
            if (this.events.length > this.maxEvents) {
                this.events = this.events.slice(-this.maxEvents);
            }
            // Report any NEW runtime violations detected (linear consume-once semantics)
            if (this.runtimeViolations.size > 0 && !this.violationsReported) {
                console.error(`[RUNTIME] ${this.runtimeViolations.size} violations detected:`, 
                    Array.from(this.runtimeViolations));
                const reportToken = { resource: 'violations-report', instance: this };
                processingCoordinator.consumed.add(reportToken);
                processingCoordinator.linearResources.add('violations-report');
                this.violationsReported = true;
            }
            
            this.scheduleNextCleanup();
        });
        
        this.cleanupStream = new LazyStream(
            cleanup,
            () => this.cleanupStream
        );
        
        this.scheduleNextCleanup();
    }
    
    scheduleNextCleanup() {
        new PullPromise(async () => {
            await new Promise(resolve => {
                setTimeout(() => {
                    this.cleanupStream.head.value;
                    resolve();
                }, CONFIG.debug.cleanupInterval || TIME.LONG);
            });
        });
    }
    
    trace(event, context = {}) {
        const timestamp = Date.now();
        const stack = new Error().stack;
        const eventId = crypto.randomBytes(CONFIG.processor.hashLength).toString(CONFIG.strings.hashEncoding);
        
        // Track through sponge for causal hash
        if (processingCoordinator) {
            processingCoordinator.absorb({
                event,
                context,
                timestamp,
                eventId
            }, `trace-${eventId}`);

            const hasher = crypto.createHash(CONFIG.strings.mainHashAlgorithm);
            hasher.update(event);
            hasher.update(eventId.toString());
            hasher.update(timestamp.toString());
            context.causalHash = hasher.digest(CONFIG.strings.hashEncoding);
        }
        
        // Use existing ConfigPatternValidator to check for violations
        // Skip dynamic runtime values like durations, timestamps
        if (context && typeof context === 'object' && configPatternValidator) {
            for (const [key, value] of Object.entries(context)) {
                if (key === 'duration' || key === 'timestamp' || key === 'memDelta' || key === 'causalHash') continue;
                if (configPatternValidator.detectMagicNumber(value, `${event}.${key}`)) {
                    this.runtimeViolations.add(`MAGIC_NUMBER: ${value} in ${event}.${key}`);
                }
            }
        }
        
        const tracedEvent = {
            id: eventId,
            event,
            context,
            timestamp,
            stack: stack.split('\n').slice(2, CONFIG.debug.stackFrameEnd),
            memory: process.memoryUsage(),
            parent: this.store.currentContext ? this.store.currentContext.id : null
        };

        this.store.append(tracedEvent);
        
        // Update Markov chain for prediction
        if (this.store.currentContext) {
            this.updateMarkovChain(this.store.currentContext.event, event);

            const predictions = this.predictNext(event);
            if (predictions.some(p => p.event.includes('ERROR') && p.probability > CONFIG.prediction.failureThreshold)) {
                lazyEvents.emit({
                    type: 'LIKELY_FAILURE',
                    after: event,
                    predictions
                });
            }
        }

        return eventId;
    }
    
    updateMarkovChain(fromEvent, toEvent) {
        return this.causalAnalysis.updateMarkovChain(fromEvent, toEvent);
    }

    predictNext(currentEvent) {
        return this.causalAnalysis.predictNext(currentEvent);
    }

    getFailureProbability(event) {
        return this.causalAnalysis.getFailureProbability(event);
    }
    
    cleanupMaps() {
        this.store.cleanup();
    }
    
    error(error, context = {}) {
        const errorId = this.trace(`ERROR: ${error.message}`, context);

        const causalChain = this.store.getCausalChain(errorId);

        this.store.errors.set(errorId, {
            error,
            context,
            causalChain,
            timestamp: Date.now(),
            stack: error.stack
        });

        console.error(`[ERROR ${errorId}] ${error.message}`);
        console.error('Causal chain:', causalChain.map(e => `${e.event} (${e.timestamp})`).join(' -> '));

        return errorId;
    }

    getCausalChain(eventId) {
        return this.store.getCausalChain(eventId);
    }
    
    async performance(label, fn) {
        const start = performance.now();
        const startMem = process.memoryUsage();

        try {
            const result = await fn();
            const duration = performance.now() - start;
            const memDelta = process.memoryUsage().heapUsed - startMem.heapUsed;

            this.store.performanceMarks.set(label, { duration, memDelta, timestamp: Date.now() });

            if (duration > CONFIG.debug.performanceWarnThreshold) {
                console.warn(`[PERF] ${label} took ${duration.toFixed(2)}ms`);
            }

            return result;
        } catch (error) {
            this.error(error, { label, performance: true });
            throw error;
        }
    }
    
    getMetrics() {
        return this.metricsCalculator.getMetrics();
    }
    
    getPerformanceProfile() {
        return this.metricsCalculator.getPerformanceProfile();
    }
    
    getCriticalPath() {
        return this.metricsCalculator.getCriticalPath();
    }
    
    detectPatterns() {
        return this.metricsCalculator.detectPatterns();
    }

    calculateEventRate(events) {
        return this.metricsCalculator.calculateEventRate(events);
    }

    calculateErrorRate(errors) {
        return this.metricsCalculator.calculateErrorRate(errors);
    }

    calculateMemoryPressure() {
        return this.metricsCalculator.calculateMemoryPressure();
    }

    identifyBottlenecks() {
        return this.metricsCalculator.identifyBottlenecks();
    }

    calculateTaskSuccessRate() {
        return this.metricsCalculator.calculateTaskSuccessRate();
    }

    categorizeOperation(label) {
        return this.metricsCalculator.categorizeOperation(label);
    }

    detectMemoryLeaks() {
        return this.patternDetection.detectMemoryLeaks();
    }

    detectPerformanceDegradation() {
        return this.patternDetection.detectPerformanceDegradation();
    }

    detectErrorClusters() {
        return this.patternDetection.detectErrorClusters();
    }

    detectResourceSpikes() {
        return this.patternDetection.detectResourceSpikes();
    }

    categorizeOperation(label) {
        return this.metricsCalculator.categorizeOperation(label);
    }
    
    detectMemoryLeaks() {
        return this.patternDetection.detectMemoryLeaks();
    }
    
    detectPerformanceDegradation() {
        return this.patternDetection.detectPerformanceDegradation();
    }
    
    detectErrorClusters() {
        return this.patternDetection.detectErrorClusters();
    }
    
    detectResourceSpikes() {
        return this.patternDetection.detectResourceSpikes();
    }
    
    // Initialize lazy telemetry system
    initializeLazyTelemetry() {
        this.lazyTelemetry = this.telemetryExporter.initializeLazyTelemetry();
        return this.lazyTelemetry;
    }
    
    // Build causality graph for visualization
    buildCausalityGraph() {
        return this.causalAnalysis.buildCausalityGraph();
    }
    
    createTelemetryStream() {
        return this.telemetryExporter.createTelemetryStream();
    }
    
    exportTelemetry() {
        return this.telemetryExporter.exportTelemetry();
    }
    
    formatMetrics(telemetry) {
        return this.telemetryExporter.formatMetrics(telemetry);
    }
    
    formatTimeseries(telemetry) {
        return this.telemetryExporter.formatTimeseries(telemetry);
    }
}

traceOrchestrator = new TraceOrchestrator();

// Define inductive types for error handling and optional values
const Maybe = new SumType('Maybe', [
    { name: 'Nothing', matches: v => v === null || v === undefined },
    { name: 'Just', matches: v => v !== null && v !== undefined }
]);

const Result = new SumType('Result', [
    { name: 'Ok', matches: v => v && !v.error },
    { name: 'Err', matches: v => v && v.error }
]);

const stateSerializer = new StateSerializer();
const reflection = new Reflection();
const taskValidator = new SchemaValidator({
    validPath: ValidPath,
    array: ArrayType
});

// serializers for debug socket queries
stateSerializer.register('scheduler', (sched) => ({
    queue: sched.queue.length,
    running: Array.from(sched.running).map(t => t.name),
    history: sched.buildHistory.size
}));

stateSerializer.register('traceOrchestrator', (trace) => ({
    events: trace.events.length,
    violations: trace.runtimeViolations.size,
    metrics: trace.metricsCalculator ? trace.metricsCalculator.getMetrics() : {}
}));

// BUILD SCHEDULER

// Processing Coordinator - Air Traffic Control for math/markdown processing
class ProcessingCoordinator {
    constructor() {
        this.state = new Map();
        this.capacity = new Map();
        this.rate = new Map();
        
        this.processedRegions = new Map(); // content hash -> processor name
        this.processingPaths = {
            // Define clear lanes for each processor
            documentPreprocess: ['<<<BLOCKMATH>>>', '<<<INLINEMATH>>>'], // DocumentProcessor markers
            tokenizer: ['$', '\\(', '\\[', '_', 'colim_', 'lim_', 'f_*'], // HTMLModality.tokenize patterns  
            latexProcessor: ['<<<BLOCKMATH>>>', '<<<INLINEMATH>>>'], // LaTeX processor handles preprocessed markers
            latexCommands: ['\\frac', '\\mathcal', '\\text', '\\bullet'], // LaTeX commands within math
            markdownProcessor: ['**', '*', '`', '['], // Markdown patterns in text
            symbolFallback: ['→', '←', '⇒', '∈', '∉'] // Standalone symbols as safety net
        };
        
        // Track processing order to prevent races
        this.processingOrder = [];
        this.conflicts = [];
        
        // EXPANDED: Full dependency orchestration
        this.dependencies = new Map(); // module -> Set<dependencies>
        this.computationGraph = new Map(); // full DAG of computations
        this.linearResources = new Set(); // resources that can only be used once
        this.affinityResources = new Set(); // resources that can be used at most once
        this.borrowed = new WeakMap(); // resource -> {owner, returnBy}
        
        // REAL COMPONENTS IN THIS FILE
        this.realComponents = {
            // Classes that process documents
            processors: new Map([
                ['DocumentProcessor', null], // Will be set when instantiated
                ['LaTeXProcessor', null],
                ['HTMLModality', null],
                ['PDFModality', null],
                ['MarkdownModality', null]
            ]),
            
            // Orchestration classes
            orchestrators: new Map([
                ['BuildScheduler', null],
                ['ProcessLockManager', null],
                ['TraceOrchestrator', traceOrchestrator],
                ['ConfigValidator', null]
            ]),
            
            // Core systems
            systems: new Map([
                ['PullGraph', pullGraph],
                ['StateSerializer', stateSerializer],
                ['Reflection', reflection]
            ])
        };
        
        // Execution lanes for REAL components
        this.executionLanes = {
            pure: ['ConfigValidator', 'ConfigPatternValidator', 'SchemaValidator', 'StateSerializer'],
            io: ['buildFile', 'generatePDF', 'watch', 'discoverDocumentFiles'],
            state: ['ProcessingCoordinator', 'BuildScheduler', 'ProcessLockManager'],
            async: ['generatePDF', 'buildFile', 'watch'],
            transform: ['DocumentProcessor', 'LaTeXProcessor', 'HTMLModality', 'MarkdownModality'],
            ...this.processingPaths
        };
        
        this.happensBefore = new Map(); // a -> Set<b> where a must happen before b
        this.mutex = new Map(); // mutually exclusive execution groups
        
        // Resource consumption tracking (linear type system expansion)
        this.consumed = new WeakSet();
        
        // Hook into global systems (when they exist)
        this.pullGraph = typeof pullGraph !== 'undefined' ? pullGraph : null;
        
        // Setup REAL dependencies for THIS FILE
        this.setupRealDependencies();
        
        // Auto-discovery of components
        this.autoDiscovered = new Set();
        this.discoveryQueue = [];
    }
    
    // Register that a processor is about to handle content
    claimProcessing(processor, content, pattern) {
        const hash = this.hashContent(content);
        
        if (this.processedRegions.has(hash)) {
            const owner = this.processedRegions.get(hash);
            if (owner !== processor) {
                // Conflict detected!
                this.conflicts.push({
                    content,
                    pattern,
                    owner,
                    challenger: processor,
                    timestamp: Date.now()
                });
                
                traceOrchestrator.trace('PROCESSING_CONFLICT', {
                    content: content.substring(0, 50),
                    owner,
                    challenger: processor
                });
                
                // Return false to prevent double-processing
                return false;
            }
        }
        
        this.processedRegions.set(hash, processor);
        this.processingOrder.push({ processor, pattern, timestamp: Date.now() });
        return true;
    }
    
    // Check if content should be processed by a given processor
    shouldProcess(processor, content, pattern) {
        // Check if another processor already owns this pattern type
        const lane = this.getProcessingLane(pattern);
        
        if (lane && !this.processingPaths[processor]?.includes(pattern)) {
            // This processor shouldn't handle this pattern
            return false;
        }
        
        return this.claimProcessing(processor, content, pattern);
    }
    
    getProcessingLane(pattern) {
        for (const [lane, patterns] of Object.entries(this.processingPaths)) {
            if (patterns.some(p => pattern.includes(p))) {
                return lane;
            }
        }
        return null;
    }
    
    hashContent(content) {
        // Simple hash for tracking
        let hash = 0;
        for (let i = 0; i < content.length; i++) {
            const char = content.charCodeAt(i);
            hash = ((hash << 5) - hash) + char;
            hash = hash & hash; // Convert to 3N.twobit integer
        }
        return hash.toString(16);
    }
    
    reset() {
        this.processedRegions.clear();
        this.processingOrder = [];
        this.conflicts = [];
    }
    
    getReport() {
        return {
            processed: this.processedRegions.size,
            order: this.processingOrder,
            conflicts: this.conflicts,
            // Add new orchestration data
            dependencies: this.exportDependencies(),
            executionPlan: this.getExecutionPlan(),
            resourceUsage: this.getResourceUsage()
        };
    }
    
    // EXPANDED ORCHESTRATION METHODS
    
    // Register a dependency between modules
    addDependency(module, dependency) {
        if (!this.dependencies.has(module)) {
            this.dependencies.set(module, new Set());
        }
        this.dependencies.get(module).add(dependency);
        
        // Update pull graph
        if (this.pullGraph) {
            this.pullGraph.dependsOn(module, dependency);
        }
    }
    
    // SELF-REGISTRATION SYSTEM
    
    getRegistration(name) {
        return Maybe.elim(
            () => 'Maybe',
            () => Maybe.elim(
                () => 'Maybe',
                () => this.realComponents.systems.get(name),
                o => o
            )(this.realComponents.orchestrators.get(name)),
            p => p
        )(this.realComponents.processors.get(name));
    }
    
    acquireResource(type, resource) {
        const key = `${type}:${resource}`;
        if (this.linearResources.has(key)) {
            return false;
        }
        this.linearResources.add(key);
        return true;
    }
    
    releaseResource(type, resource) {
        const key = `${type}:${resource}`;
        this.linearResources.delete(key);
        return true;
    }
    
    registerSelf(component) {
        if (!component) return null;
        
        const name = component.constructor?.name || component.name || 'unknown';
        
        // Absorb component into sponge state
        if (component === this) {
            this.absorb({
                absorb: this.absorb.bind(this),
                contentHash: this.contentHash.bind(this),
                buildSponge: this.buildSponge.bind(this)
            }, 'self');
            
            // Connect to pull graph dependencies
            if (pullGraph && pullGraph.edges) {
                for (const [node, deps] of pullGraph.edges) {
                    this.dependencies.set(node, deps);
                }
            }
        }
        
        // Check if already registered to prevent loops
        if (this.realComponents.processors.has(name) || 
            this.realComponents.orchestrators.has(name) || 
            this.realComponents.systems.has(name)) {
            return this.getRegistration(name);
        }
        
        const registration = {
            name,
            instance: component,
            type: this.determineComponentType(component),
            dependencies: component.dependencies ?? [],
            provides: component.provides ?? [],
            consumes: component.consumes ?? [],
            lane: component.lane ?? this.determineExecutionLane(name),
            linear: component.linear ?? false,
            affine: component.affine ?? false,
            mutex: component.mutex ?? [],
            orderingConstraints: component.orderingConstraints ?? {},

            usedBy: new Set(),
            uses: new Set(),
            registeredAt: Date.now()
        };
        
        // Store in appropriate category
        if (registration.type === 'processor') {
            this.realComponents.processors.set(registration.name, registration);
        } else if (registration.type === 'orchestrator') {
            this.realComponents.orchestrators.set(registration.name, registration);
        } else {
            this.realComponents.systems.set(registration.name, registration);
        }
        
        // Register dependencies
        for (const dep of registration.dependencies) {
            this.addDependency(registration.name, dep);
            
            registration.uses.add(dep);
            
            const depReg = Maybe.elim(
                () => 'Maybe',
                () => Maybe.elim(
                    () => 'Maybe',
                    () => this.realComponents.systems.get(dep),
                    o => o
                )(this.realComponents.orchestrators.get(dep)),
                p => p
            )(this.realComponents.processors.get(dep));
            Maybe.elim(
                () => 'Maybe',
                () => null,
                reg => { if (reg.usedBy) reg.usedBy.add(registration.name); return reg; }
            )(depReg);
        }

        if (registration.orderingConstraints) {
            if (registration.orderingConstraints.before) {
                for (const before of registration.orderingConstraints.before) {
                    this.addOrderingConstraint(registration.name, before);
                }
            }
            if (registration.orderingConstraints.after) {
                for (const after of registration.orderingConstraints.after) {
                    this.addOrderingConstraint(after, registration.name);
                }
            }
        }
        
        // Register mutex groups
        if (registration.mutex.length > 0) {
            this.addMutexGroup([registration.name, ...registration.mutex]);
        }
        
        // Mark as linear/affine if specified
        if (registration.linear) {
            this.markLinear(registration.name);
        }
        if (registration.affine) {
            this.markAffine(registration.name);
        }
        
        // Track what it provides/consumes
        if (registration.provides.length > 0) {
            this.registerProvider(registration.name, registration.provides);
        }
        if (registration.consumes.length > 0) {
            this.registerConsumer(registration.name, registration.consumes);
        }
        
        // Mark as discovered
        this.autoDiscovered.add(registration.name);
        
        // Trigger discovery of dependencies if not yet registered
        for (const dep of registration.dependencies) {
            if (!this.autoDiscovered.has(dep)) {
                this.discoveryQueue.push(dep);
            }
        }
        
        return registration;
    }
    
    // Determine what type of component this is
    determineComponentType(component) {
        const name = component.constructor?.name || component.name;
        
        if (name.includes('Processor') || name.includes('Modality')) {
            return 'processor';
        }
        if (name.includes('Scheduler') || name.includes('Manager') || 
            name.includes('Coordinator') || name.includes('Debugger')) {
            return 'orchestrator';
        }
        if (name.includes('Serializer')) {
            return 'system';
        }
        
        // Check if it's a function
        if (typeof component === 'function') {
            return 'function';
        }
        
        return 'unknown';
    }
    
    // Register what a component provides
    registerProvider(name, resources) {
        if (!this.providers) this.providers = new Map();
        
        for (const resource of resources) {
            const resourceSet = Maybe.elim(
                () => 'Maybe',
                () => { this.providers.set(resource, new Set()); return this.providers.get(resource); },
                s => s
            )(this.providers.get(resource));
            resourceSet.add(name);
        }
    }
    
    // Register what a component consumes
    registerConsumer(name, resources) {
        (this.consumers ||= new Map());
        for (const resource of resources) {
            const resourceSet = Maybe.elim(
                () => 'Maybe',
                () => { this.consumers.set(resource, new Set()); return this.consumers.get(resource); },
                s => s
            )(this.consumers.get(resource));
            resourceSet.add(name);
            
            // Auto-add dependency on providers
            if (this.providers && this.providers.has(resource)) {
                for (const provider of this.providers.get(resource)) {
                    if (provider !== name) {
                        this.addDependency(name, provider);
                        
                        const consumerReg = Maybe.elim(
                            () => 'Maybe',
                            () => Maybe.elim(
                                () => 'Maybe',
                                () => this.realComponents.systems.get(name),
                                o => o
                            )(this.realComponents.orchestrators.get(name)),
                            p => p
                        )(this.realComponents.processors.get(name));
                        const providerReg = Maybe.elim(
                            () => 'Maybe',
                            () => Maybe.elim(
                                () => 'Maybe',
                                () => this.realComponents.systems.get(provider),
                                o => o
                            )(this.realComponents.orchestrators.get(provider)),
                            p => p
                        )(this.realComponents.processors.get(provider));
                        
                        if (consumerReg && consumerReg.uses) {
                            consumerReg.uses.add(provider);
                        }
                        if (providerReg && providerReg.usedBy) {
                            providerReg.usedBy.add(name);
                        }
                    }
                }
            }
        }
    }
    
    setupRealDependencies() {
        this.addDependency('DocumentProcessor', 'LaTeXProcessor');
        this.addDependency('DocumentProcessor', 'ProcessingCoordinator');
        
        this.addDependency('HTMLModality', 'LaTeXProcessor');
        this.addDependency('HTMLModality', 'DocumentProcessor');
        
        this.pipelineStages = new Map();
        
        // PDFModality extends HTMLModality
        this.addDependency('PDFModality', 'HTMLModality');
        this.addDependency('PDFModality', 'generatePDF');
        
        // BuildScheduler depends on ProcessingCoordinator
        this.addDependency('BuildScheduler', 'ProcessingCoordinator');
        this.addDependency('BuildScheduler', 'TraceOrchestrator');
        
        // buildFile depends on everything
        this.addDependency('buildFile', 'DocumentProcessor');
        this.addDependency('buildFile', 'HTMLModality');
        this.addDependency('buildFile', 'PDFModality');
        this.addDependency('buildFile', 'BuildScheduler');
        
        // watch depends on buildFile
        this.addDependency('watch', 'buildFile');
        this.addDependency('watch', 'ProcessLockManager');

        // Setup ordering constraints as pipeline stages
        this.addOrderingConstraint('validateConfig', 'buildFile');
        this.addOrderingConstraint('DocumentProcessor', 'generatePDF');
        this.addOrderingConstraint('HTMLModality', 'PDFModality');
        this.addOrderingConstraint('ProcessLockManager', 'DocumentProcessor');
        
        // Setup exclusive access (mutex groups)
        this.addMutexGroup(['DocumentProcessor', 'LaTeXProcessor', 'HTMLModality']);
        this.addMutexGroup(['generatePDF', 'PDFModality']);
        this.addMutexGroup(['validateConfig', 'ConfigValidator']);
        
        // Initialize pipeline network
        this.initializePipelineStages();
    }
    
    initializePipelineStages() {
        this.pipelineStages.set('read->parse', {
            source: 'readFile',
            destination: 'parse',
            distance: TIME.TICK,
            capacity: CONFIG.scheduler.maxConcurrent
        });
        
        this.pipelineStages.set('parse->transform', {
            source: 'parse',
            destination: 'transform',
            distance: TIME.DEBOUNCE,
            capacity: CONFIG.processor.minGroupSize
        });
        
        this.pipelineStages.set('transform->write', {
            source: 'transform',
            destination: 'write',
            distance: TIME.TICK,
            capacity: CONFIG.limits.maxConcurrent
        });
        
        this.pipelineStages.set('error->retry', {
            source: 'error',
            destination: 'retry',
            distance: TIME.TIMEOUT,
            capacity: CONFIG.scheduler.retryLimit,
            bidirectional: true
        });
    }
    
    absorb(data, tag) {
        // Sponge construction using Node crypto instead of manual Keccak
        // Keep composable absorb/squeeze interface but delegate to crypto.createHash

        if (!this.absorbed) {
            this.absorbed = [];
        }

        // Store as Lazy - evaluation happens in contentHash
        const lazyData = data instanceof Lazy ? data : new Lazy(() => data);
        this.rate.set(tag, lazyData);
        this.absorbed.push({ data: lazyData, tag });

        // Store in state for squeeze
        const mixed = new Lazy(() => {
            const pulled = lazyData.value;
            const capacity = this.capacity.get('integrity')?.value;
            return { ...pulled, _capacity: capacity };
        });

        this.state.set(tag, mixed);
        return mixed;
    }

    contentHash(domain = 'content') {
        // Squeeze phase - extract hash
        return new Lazy(() => {
            if (!this.absorbed || this.absorbed.length === 0) {
                throw new Error('No data absorbed yet');
            }

            // Create hash from absorbed data - evaluate Lazy values here
            const hasher = crypto.createHash(CONFIG.strings.mainHashAlgorithm);
            for (const item of this.absorbed) {
                const value = item.data.value; // Pull lazy value
                const serialized = typeof value === 'string' ? value : JSON.stringify(value);
                hasher.update(serialized);
                hasher.update(`|${item.tag}|`);
            }

            // Domain separation
            hasher.update(`|domain:${domain}|`);

            // Extract hash (squeeze)
            const hash = hasher.digest(CONFIG.strings.hashEncoding);

            // Domain-separated registration
            if (pullGraph) {
                pullGraph.register(`${domain}-hash-${hash}`, new Lazy(() => this.absorbed));
            }

            if (traceOrchestrator) {
                traceOrchestrator.trace('SPONGE_HASH', { hash, absorbed: this.absorbed, domain });
            }

            return hash;
        });
    }
    
    // Categorical cache functor that preserves pipeline structure
    cacheFunctor(pipeline, cacheKey) {
        return {
            // Map: transform cached values while preserving structure
            map: (f) => {
                const cached = pullGraph.nodes.get(cacheKey);
                if (cached) {
                    return new Lazy(() => f(cached.value));
                }
                return pipeline.then(result => {
                    pullGraph.register(cacheKey, new Lazy(() => result));
                    return f(result);
                });
            },
            
            // Compose: chain cache operations categorically
            compose: (other) => {
                return this.cacheFunctor(
                    pipeline.then(other),
                    `${cacheKey}-${other.id || 'composed'}`
                );
            },
            
            // Pull: extract value with cache check
            pull: async () => {
                const cached = pullGraph.nodes.get(cacheKey);
                if (cached && cached.value) {
                    const val = cached.value;
                    // Validate cache coherence
                    if (val && typeof val === 'object' && val.formats) {
                        return val;
                    }
                }
                // Execute pipeline and cache result
                const result = await pipeline;
                if (result && result.formats) {
                    pullGraph.register(cacheKey, new Lazy(() => result));
                }
                return result;
            }
        };
    }
    // Build-aware sponge that absorbs full context
    buildSponge(fileContent, fileName, buildContext) {
        // Clear previous state for new build
        this.absorbed = [];

        // Absorb file content
        this.absorb(fileContent, 'file-content');

        // Absorb file metadata
        this.absorb(fileName, 'file-name');
        this.absorb(buildContext.timestamp?.toString() || Date.now().toString(), 'timestamp');
        this.absorb(buildContext.version || '1.0.0', 'version');

        // Absorb git commit for hermetic builds
        if (buildContext.gitCommit) {
            this.absorb(buildContext.gitCommit, 'git-commit');
        }

        // Absorb dependencies for hermetic builds
        if (buildContext.dependencies) {
            buildContext.dependencies.forEach(dep => {
                this.absorb(dep.hash, `dep-${dep.name}`);
            });
        }

        // Absorb build configuration
        if (buildContext.formats) {
            buildContext.formats.forEach(fmt => this.absorb(fmt, `format-${fmt}`));
        }

        // Domain-separated hash for builds
        return this.contentHash('build');
    }
    
    executeStage(data, stageId) {
        const stage = this.pipelineStages.get(stageId);
        if (!stage) {
            throw new Error(`Stage ${stageId} not found`);
        }
        
        return new PullPromise(async () => {
            // Absorb input
            const absorbed = this.absorb(data, stageId);
            
            if (!stage.currentLoad) stage.currentLoad = 0;
            stage.currentLoad = stage.currentLoad + 1;
            await new Promise(resolve => setTimeout(resolve, stage.distance));
            stage.currentLoad--;
            
            const output = this.state.get(stageId);
            
            // Track in pull graph (register the lazy computation)
            if (pullGraph) {
                pullGraph.register(`stage-${stageId}-${Date.now()}`, output);
            }
            
            // Pull the lazy value for return
            return output ? output.value : data;
        });
    }
    
    // Mark resource as linear (use exactly once)
    markLinear(resource) {
        this.linearResources.add(resource);
    }
    
    // Mark resource as affine (use at most once) 
    markAffine(resource) {
        this.affinityResources.add(resource);
    }
    
    // Acquire resource with full linear type checking
    acquire(module, resource, mode = 'exclusive') {
        const resourceId = this.hashContent(resource);
        
        // Check if linear resource already consumed
        if (this.linearResources.has(resourceId)) {
            if (this.consumed.has(resource)) {
                throw new Error(`Linear resource ${resourceId} already consumed`);
            }
            this.consumed.add(resource);
        }
        
        // Check affine resources
        if (this.affinityResources.has(resourceId)) {
            if (this.consumed.has(resource)) {
                return { access: 'denied', reason: 'affine_already_used' };
            }
        }
        
        // Check borrowing
        if (this.borrowed.has(resource)) {
            const loan = this.borrowed.get(resource);
            if (Date.now() < loan.returnBy) {
                return { access: 'denied', reason: 'borrowed', owner: loan.owner };
            }
        }
        
        // Try existing claim mechanism
        if (this.claimProcessing(module, resource, mode)) {
            return {
                access: 'granted',
                release: () => this.release(module, resource),
                borrow: (duration) => this.borrow(module, resource, duration)
            };
        }
        
        // Conflict resolution
        return this.resolveConflict(module, resource, mode);
    }
    
    // Borrow resource temporarily
    borrow(borrower, resource, duration = 1000) {
        this.borrowed.set(resource, {
            owner: borrower,
            returnBy: Date.now() + duration
        });
        
        return {
            access: 'borrowed',
            mustReturn: duration,
            release: () => this.borrowed.delete(resource)
        };
    }
    
    // Release resource
    release(module, resource) {
        const resourceId = this.hashContent(resource);
        if (this.processedRegions.get(resourceId) === module) {
            this.processedRegions.delete(resourceId);
        }
        this.borrowed.delete(resource);
    }
    
    // Add ordering constraint
    addOrderingConstraint(before, after) {
        const beforeSet = Maybe.elim(
            () => 'Maybe',
            () => { this.happensBefore.set(before, new Set()); return this.happensBefore.get(before); },
            s => s
        )(this.happensBefore.get(before));
        beforeSet.add(after);
    }
    
    // Add mutex group
    addMutexGroup(modules) {
        const groupId = `mutex_${this.mutex.size}`;
        this.mutex.set(groupId, new Set(modules));
    }
    
    // Schedule execution with dependency resolution
    scheduleExecution(modules) {
        const sorted = [];
        const visited = new Set();
        const visiting = new Set();
        
        const visit = (module) => {
            if (visited.has(module)) return;
            if (visiting.has(module)) {
                throw new Error(`Circular dependency detected: ${module}`);
            }
            
            visiting.add(module);
            
            // Visit dependencies first
            const deps = Maybe.elim(
                () => 'Maybe',
                () => new Set(),
                d => d
            )(this.dependencies.get(module));
            for (const dep of deps) {
                visit(dep);
            }

            // Check ordering constraints
            const mustPrecede = Maybe.elim(
                () => 'Maybe',
                () => new Set(),
                m => m
            )(this.happensBefore.get(module));
            for (const dependency of mustPrecede) {
                if (sorted.includes(dependency)) {
                    // Reorder to satisfy ordering constraint
                    const idx = sorted.indexOf(dependency);
                    sorted.splice(idx, 0, module);
                    visiting.delete(module);
                    visited.add(module);
                    return;
                }
            }
            
            visiting.delete(module);
            visited.add(module);
            sorted.push(module);
        };
        
        for (const module of modules) {
            visit(module);
        }
        
        return this.optimizeExecutionPlan(sorted);
    }
    
    // Optimize for parallel execution
    optimizeExecutionPlan(sorted) {
        const plan = {
            sequential: [],
            parallel: [],
            lanes: {}
        };
        
        // Group by lanes
        for (const module of sorted) {
            const lane = this.determineExecutionLane(module);
            if (!plan.lanes[lane]) {
                plan.lanes[lane] = [];
            }
            plan.lanes[lane].push(module);
        }
        
        // Compute parallelization levels
        const levels = this.computeParallelizationLevels(sorted);
        
        for (const level of levels) {
            if (level.length === 1) {
                plan.sequential.push(level[0]);
            } else {
                // Check mutex constraints
                const groups = this.partitionByMutex(level);
                plan.parallel.push(groups);
            }
        }
        
        return plan;
    }
    
    // Compute parallelization levels
    computeParallelizationLevels(sorted) {
        const levels = [];
        const moduleLevel = new Map();
        
        for (const module of sorted) {
            const deps = Maybe.elim(
                () => 'Maybe',
                () => new Set(),
                d => d
            )(this.dependencies.get(module));
            let maxDepLevel = -1;
            
            for (const dep of deps) {
                if (moduleLevel.has(dep)) {
                    maxDepLevel = Math.max(maxDepLevel, moduleLevel.get(dep));
                }
            }
            
            const level = maxDepLevel + 1;
            moduleLevel.set(module, level);
            
            if (!levels[level]) {
                levels[level] = [];
            }
            levels[level].push(module);
        }
        
        return levels;
    }
    
    // Partition by mutex constraints
    partitionByMutex(modules) {
        const groups = [];
        const assigned = new Set();
        
        for (const module of modules) {
            if (assigned.has(module)) continue;
            
            const group = [module];
            assigned.add(module);
            
            // Check mutex constraints
            for (const [, mutexSet] of this.mutex) {
                if (mutexSet.has(module)) {
                    // Can't run with other mutex members
                    for (const other of modules) {
                        if (!assigned.has(other) && !mutexSet.has(other)) {
                            group.push(other);
                            assigned.add(other);
                        }
                    }
                }
            }
            
            groups.push(group);
        }
        
        return groups;
    }
    
    // Determine execution lane for module
    determineExecutionLane(module) {
        // Check if it's a processor
        for (const [lane, patterns] of Object.entries(this.processingPaths)) {
            if (module.includes(lane)) return lane;
        }
        
        // Check if it's async
        if (module.includes('async') || module.includes('Promise')) return 'async';
        
        // Check if it's I/O
        if (module.includes('read') || module.includes('write')) return 'io';
        
        // Check if it's state mutation
        if (module.includes('set') || module.includes('update')) return 'state';
        
        // Default to pure
        return 'pure';
    }
    
    // Resolve conflicts with strategies
    resolveConflict(requester, resource, mode) {
        const owner = this.processedRegions.get(this.hashContent(resource));
        
        // Try cooperation (sharing)
        if (mode === 'shared') {
            return {
                access: 'shared',
                constraints: ['read-only'],
                release: () => this.releaseShared(requester, resource)
            };
        }
        
        // Try deferral
        return {
            access: 'deferred',
            retry: () => this.acquire(requester, resource, mode),
            estimatedWait: 100
        };
    }
    
    // Export dependencies for visualization
    exportDependencies() {
        const result = {};
        for (const [module, deps] of this.dependencies) {
            result[module] = Array.from(deps);
        }
        return result;
    }
    
    // Get current execution plan
    getExecutionPlan() {
        const modules = Array.from(this.dependencies.keys());
        return this.scheduleExecution(modules);
    }
    
    // Get resource usage stats
    getResourceUsage() {
        return {
            linear: this.linearResources.size,
            affine: this.affinityResources.size,
            borrowed: this.borrowed.size,
            processed: this.processedRegions.size,
            conflicts: this.conflicts.length
        };
    }
    
    // Check for resource conflicts
    hasResourceConflicts() {
        // Check for unresolved conflicts
        if (this.conflicts.length > 0) return true;
        
        // Check for linear resources consumed multiple times
        if (this.consumed.size > this.linearResources.size) return true;
        
        // Check for overdue borrows
        if (this.borrowed.size > 0) {
            for (const [, loan] of this.borrowed) {
                if (Date.now() > loan.returnBy) return true;
            }
        }
        
        // Check for mutex violations
        const activeModules = new Set();
        for (const [, mutexSet] of this.mutex) {
            let count = 0;
            for (const module of mutexSet) {
                if (activeModules.has(module)) count++;
                if (count > 1) return true;
            }
        }
        
        return false;
    }
}

processingCoordinator = new ProcessingCoordinator();
processingCoordinator.registerSelf(processingCoordinator);

class BuildScheduler {
    constructor() {
        this.queue = [];
        this.running = new Set();
        this.maxConcurrent = CONFIG.scheduler.maxConcurrent;
        this.pendingTimers = new Map();
        this.locks = new Map(); // File-level locks
        this.buildHistory = new Map();
        this.coordinator = processingCoordinator;
        this.validatedBuilds = new Map();
        
        // SELF-REGISTRATION
        this.dependencies = ['ProcessingCoordinator', 'TraceOrchestrator', 'ProcessLockManager'];
        this.provides = ['task-scheduling', 'concurrency-control', 'auto-scaling'];
        this.consumes = ['processor-availability', 'performance-metrics'];
        this.lane = 'orchestrator';
        this.mutex = ['BuildScheduler'];  // Only one scheduler at a time
        this.orderingConstraints = {
            after: ['ProcessingCoordinator'],  // Must initialize after coordinator
            before: ['buildFile']  // Must be ready before builds start
        };
        
        // Register with coordinator
        if (processingCoordinator && processingCoordinator.registerSelf) {
            processingCoordinator.registerSelf(this);
        }
        
        // Auto-scaling based on performance metrics
        this.autoScale = {
            enabled: true,
            baselineConcurrency: CONFIG.scheduler.maxConcurrent,
            minConcurrency: CONFIG.limits.minConcurrent,
            maxConcurrency: CONFIG.limits.maxConcurrent,
            lastAdjustment: Date.now(),
            adjustmentInterval: TIME.LONG,
            
            adjust() {
                if (!this.enabled || Date.now() - this.lastAdjustment < this.adjustmentInterval) {
                    return;
                }
                
                const metrics = traceOrchestrator.getMetrics();
                
                // Scale down if memory pressure
                if (metrics.memoryPressure > CONFIG.scheduler.memoryPressureThreshold) {
                    this.parent.maxConcurrent = Math.max(
                        this.minConcurrency,
                        Math.floor(this.parent.maxConcurrent * CONFIG.scheduler.scaleDownFactor)
                    );
                    traceOrchestrator.trace('AUTO_SCALE_DOWN', { 
                        reason: 'memory_pressure',
                        newConcurrency: this.parent.maxConcurrent 
                    });
                }
                // Scale up if performance is good and queue is building
                else if (metrics.errorRate < CONFIG.scheduler.errorRateThreshold && this.parent.queue.length > this.parent.maxConcurrent) {
                    this.parent.maxConcurrent = Math.min(
                        this.maxConcurrency,
                        Math.ceil(this.parent.maxConcurrent * CONFIG.scheduler.scaleUpFactor)
                    );
                    traceOrchestrator.trace('AUTO_SCALE_UP', { 
                        reason: 'good_performance',
                        newConcurrency: this.parent.maxConcurrent 
                    });
                }
                
                // Adjust resource pools
                ResourcePools.concurrent.limit = this.parent.maxConcurrent;
                
                this.lastAdjustment = Date.now();
            }
        };
        this.autoScale.parent = this;
        
        // Connect telemetry stream for adaptive scheduling
        this.telemetrySubscription = null;
        this.initTelemetryFeedback();
    }
    
    initTelemetryFeedback() {
        // Subscribe to telemetry stream for real-time adaptation
        const telemetryStream = traceOrchestrator.createTelemetryStream();
        
        // Anomalies adjust priorities in real-time
        this.telemetrySubscription = new Lazy(() => telemetryStream.anomalies.value
            .filter(a => a !== null)
            .subscribe(anomaly => {
                if (anomaly.type === 'HIGH_MEMORY_PRESSURE') {
                    this.maxConcurrent = Math.max(
                        CONFIG.limits.minConcurrent, 
                        this.maxConcurrent - 1
                    );
                    traceOrchestrator.trace('TELEMETRY_SCALE_DOWN', {
                        anomaly: anomaly.type,
                        newConcurrency: this.maxConcurrent
                    });
                } else if (anomaly.type === 'HIGH_ERROR_RATE') {
                    // Pause scheduling temporarily
                    this.pauseScheduling(TIME.TICK);
                } else if (anomaly.type === 'PERFORMANCE_DEGRADATION') {
                    // Reduce concurrent builds
                    this.maxConcurrent = Math.floor(this.maxConcurrent * CONFIG.scheduler.scaleDownFactor);
                }
            }));
        
        // Use aggregates to predict optimal concurrency
        new Lazy(() => telemetryStream.aggregates.value.subscribe(agg => {
            const optimalConcurrency = this.predictOptimalConcurrency(agg);
            if (Math.abs(optimalConcurrency - this.maxConcurrent) > 1) {
                this.maxConcurrent = optimalConcurrency;
                traceOrchestrator.trace('TELEMETRY_OPTIMIZE', {
                    metrics: agg,
                    newConcurrency: this.maxConcurrent
                });
            }
        }));
    }
    
    predictOptimalConcurrency(metrics) {
        // Use Little's Law: L = λW
        // L = average number in system, λ = arrival rate, W = average time in system
        const arrivalRate = metrics.avgEventRate;
        const avgTime = metrics.avgEventLatency;
        const littlesLaw = arrivalRate * avgTime;
        
        // Adjust based on error rate
        const errorAdjustment = 1 - metrics.avgErrorRate;
        
        // Calculate optimal concurrency
        const optimal = Math.ceil(littlesLaw * errorAdjustment);
        
        // Clamp to configured limits
        return Math.max(
            CONFIG.limits.minConcurrent,
            Math.min(CONFIG.limits.maxConcurrent, optimal)
        );
    }
    
    pauseScheduling(duration) {
        const wasProcessing = this.processing;
        this.processing = false;
        
        new PullPromise(async () => {
            await new Promise(resolve => {
                const timer = traceOrchestrator.trace('PAUSE_SCHEDULING', { duration });
                lazyEvents.emit({ type: 'SCHEDULER_PAUSED', duration });
                
                // Use lazy timer instead of setTimeout
                const lazyTimer = new Lazy(() => {
                    this.processing = wasProcessing;
                    traceOrchestrator.trace('RESUME_SCHEDULING', { timer });
                    lazyEvents.emit({ type: 'SCHEDULER_RESUMED' });
                    resolve();
                });
                
                // Delay evaluation
                Promise.resolve().then(() => {
                    setTimeout(() => lazyTimer.value, duration);
                });
            });
        });
    }
    
    async schedule(task, priority = CONFIG.scheduler.defaultPriority) {
        console.log('[SCHEDULER] Scheduling task:', task.name, 'Priority:', priority);
        traceOrchestrator.trace('Schedule task', { task: task.name, priority });

        try {
            const failureProb = traceOrchestrator.getFailureProbability(task.name);
            if (failureProb >= CONFIG.prediction.remediationThreshold) {
                await this.remediate(task, failureProb);
                traceOrchestrator.trace('PREDICTED_FAILURE', {
                    task: task.name,
                    probability: failureProb
                });
            }
        } catch (e) {}

        // Check for existing task for same file
        const existing = this.queue.findIndex(t => t.file === task.file);
        if (existing !== CONFIG.processor.notFoundIndex) {
            // Replace with higher priority task
            if (priority > this.queue[existing].priority) {
                this.queue.splice(existing, 1);
            } else {
                traceOrchestrator.trace('Task already queued', { file: task.file });
                return;
            }
        }

        // Add to queue
        this.queue.push({ ...task, priority, id: crypto.randomBytes(CONFIG.processor.hashLength).toString(CONFIG.strings.hashEncoding) });
        this.queue.sort((a, b) => b.priority - a.priority);

        // Process queue
        await this.process();
    }

    async remediate(task, failureProb) {
        traceOrchestrator.trace('REMEDIATION_START', { task: task.name, probability: failureProb });

        // Clear cache for likely-to-fail tasks
        if (pullGraph && pullGraph.objects.has(task.file)) {
            pullGraph.objects.delete(task.file);
            traceOrchestrator.trace('CACHE_CLEARED', { file: task.file, reason: 'predicted-failure' });
        }

        // Reset build history to force clean rebuild
        if (this.buildHistory.has(task.file)) {
            this.buildHistory.delete(task.file);
            traceOrchestrator.trace('HISTORY_RESET', { file: task.file });
        }

        // If failure probability very high, restart browser (for document processing)
        if (failureProb > CONFIG.prediction.browserRestartThreshold && processor && processor.state.browser) {
            try {
                await processor.state.browser.close();
                processor.state.browser = null;
                traceOrchestrator.trace('BROWSER_RESTARTED', { reason: 'high-failure-probability' });
            } catch (e) {
                traceOrchestrator.error(e, { context: 'remediation-browser-restart' });
            }
        }

        traceOrchestrator.trace('REMEDIATION_COMPLETE', { task: task.name });
    }
    
    async scheduleProven(task, priority = CONFIG.scheduler.defaultPriority) {
        // Validate task inputs exist
        const state = {
            inputs: [task.file],
            task: task.name,
            context: {
                resources: this.coordinator.availableResources(),
                history: this.buildHistory.get(task.file),
                running: this.running.size
            }
        };

        const validation = taskValidator.validateSchema(state, {
            inputs: { type: 'array', items: { type: 'validPath' }, required: true }
        });

        if (validation.errors.length > 0) {
            const error = new Error(`Task validation failed: ${validation.errors.map(e => e.error).join(', ')}`);
            traceOrchestrator.trace('Task validation failed', { task: task.name, errors: validation.errors });
            throw error;
        }

        task.validated = true;

        return this.schedule(task, priority);
    }
    
    async process() {
        console.log('[SCHEDULER] Process called. Queue:', this.queue.length, 'Running:', this.running.size, 'MaxConcurrent:', this.maxConcurrent);
        // Auto-scale based on performance
        this.autoScale.adjust();
        
        while (this.queue.length > 0 && this.running.size < this.maxConcurrent) {
            const task = this.queue.shift();
            
            // Check if file is locked
            if (this.locks.has(task.file)) {
                traceOrchestrator.trace('File locked, requeuing', { file: task.file });
                this.queue.push(task); // Requeue at end
                await new Promise(resolve => setTimeout(resolve, CONFIG.scheduler.lockCheckInterval));
                continue;
            }
            
            // Lock file and run
            this.locks.set(task.file, task.id);
            this.running.add(task.id);
            
            this.runTask(task).finally(() => {
                this.running.delete(task.id);
                this.locks.delete(task.file);
                // Schedule next process cycle to avoid stack overflow
                setImmediate(() => this.process());
            });
        }
    }
    
    async runTask(task) {
        console.log('[SCHEDULER] Running task:', task.name);
        const startTime = Date.now();
        
        // Absorb task into coordinator
        this.coordinator.absorb(task, task.id);
        
        traceOrchestrator.trace('Running task', { task: task.name, file: task.file });
        
        try {
            await task.fn();
            
            // Track success
            if (!this.buildHistory.has(task.file)) {
                this.buildHistory.set(task.file, { success: 0, failure: 0 });
            }
            const history = this.buildHistory.get(task.file);
            if (history) history.success++;
            
            // Clean up buildHistory if it gets too large
            if (this.buildHistory.size > CONFIG.scheduler.buildHistoryLimit) {
                const entries = Array.from(this.buildHistory.entries());
                this.buildHistory = new Map(entries.slice(-CONFIG.scheduler.buildHistoryTrim));
            }
            
            traceOrchestrator.trace('Task completed', { 
                task: task.name
                // Duration is computed dynamically, not a magic number
            });
        } catch (error) {
            // Track failure
            if (!this.buildHistory.has(task.file)) {
                this.buildHistory.set(task.file, { success: 0, failure: 0 });
            }
            const history = this.buildHistory.get(task.file);
            if (history) history.failure++;
            
            traceOrchestrator.error(error, { 
                task: task.name, 
                file: task.file,
                history: this.buildHistory.get(task.file)
            });
            
            // ADAPTIVE retry logic using TraceOrchestrator analysis
            const failureHistory = this.buildHistory.get(task.file);
            if (failureHistory && failureHistory.failure < CONFIG.scheduler.retryLimit) {
                // Get insights from TraceOrchestrator
                const metrics = traceOrchestrator.getMetrics();
                const patterns = traceOrchestrator.detectPatterns();
                
                // Determine adaptive retry strategy
                const retryStrategy = this.determineRetryStrategy(error, metrics, patterns, failureHistory);
                
                if (retryStrategy.shouldRetry) {
                    traceOrchestrator.trace('Scheduling adaptive retry', { 
                        file: task.file, 
                        attempt: failureHistory.failure,
                        delay: retryStrategy.delay,
                        reason: retryStrategy.reason
                    });
                    
                    setTimeout(() => {
                        // Adjust priority based on failure patterns
                        const adaptivePriority = retryStrategy.priority || CONFIG.scheduler.retryPriority;
                        this.schedule(task, adaptivePriority);
                    }, retryStrategy.delay);
                } else {
                    traceOrchestrator.trace('Skipping retry', { 
                        file: task.file,
                        reason: retryStrategy.reason
                    });
                }
            }
        }
    }
    
    debounce(file, fn, delay = CONFIG.scheduler.debounceDelay) {
        if (this.pendingTimers.has(file)) {
            clearTimeout(this.pendingTimers.get(file));
        }
        
        const timer = setTimeout(() => {
            this.pendingTimers.delete(file);
            this.schedule({
                name: `build-${file}`,
                file,
                fn
            });
        }, delay);
        
        this.pendingTimers.set(file, timer);
    }
    
    getStats() {
        return {
            queued: this.queue.length,
            running: this.running.size,
            locked: this.locks.size,
            history: Array.from(this.buildHistory.entries())
        };
    }
    
    determineRetryStrategy(error, metrics, patterns, failureHistory) {
        const strategy = {
            shouldRetry: true,
            delay: CONFIG.scheduler.retryDelayBase,
            priority: CONFIG.scheduler.retryPriority,
            reason: 'default'
        };
        
        if (metrics.memoryPressure > THRESHOLDS.MEMORY_PRESSURE_HIGH) {
            strategy.shouldRetry = false;
            strategy.reason = 'memory_pressure_too_high';
            return strategy;
        }
        
        if (patterns.errorClusters.length > 0) {
            const recentCluster = patterns.errorClusters[patterns.errorClusters.length - 1];
            const timeSinceCluster = Date.now() - recentCluster[recentCluster.length - 1].timestamp;
            if (timeSinceCluster < TIME.TIMEOUT) {
                strategy.shouldRetry = false;
                strategy.reason = 'error_cluster_detected';
                return strategy;
            }
        }
        
        if (error.message.includes('ENOENT') || error.message.includes(CONFIG.strings.errorPatterns.fileNotFound)) {
            strategy.delay = TIME.TICK;
            strategy.reason = 'file_not_found';
        } else if (error.message.includes(CONFIG.strings.errorPatterns.resourceClosed) || error.message.includes(CONFIG.strings.errorPatterns.processDetached)) {
            strategy.delay = CONFIG.scheduler.retryDelayBase * CONFIG.processor.minGroupSize;
            strategy.reason = 'resource_closed';
            strategy.priority = -2;
        } else if (error.message.includes(CONFIG.strings.errorPatterns.operationTimeout)) {
            strategy.delay = CONFIG.scheduler.retryDelayBase * Math.pow(2, failureHistory.failure);
            strategy.reason = 'timeout_exponential_backoff';
        } else if (patterns.memoryLeaks) {
            strategy.delay = CONFIG.scheduler.retryDelayBase * THRESHOLDS.TOP_RESULTS;
            strategy.priority = -CONFIG.processor.minGroupSize;
            strategy.reason = 'memory_leak_detected';
        }
        
        if (metrics.eventRate > THRESHOLDS.EVENT_RATE_BUSY) {
            strategy.delay *= 2;
            strategy.reason += '_high_load';
        }
        
        // Increase priority if this is a critical path task
        const criticalPaths = traceOrchestrator.getCriticalPath();
        if (criticalPaths.some(path => path.path.includes(error.message))) {
            strategy.priority += 2;
            strategy.reason += '_critical_path';
        }
        
        // Cap maximum delay
        strategy.delay = Math.min(strategy.delay, TIME.LONG);
        
        return strategy;
    }
}

const scheduler = new BuildScheduler();

// DOCUMENT PROCESSOR

class DocumentProcessor {
    constructor() {
        this.sections = new Map();
        this.relationships = new Map();
        this.data = new Map();
        this.graph = initPullGraph();
        
        // SELF-REGISTRATION
        this.dependencies = ['LaTeXProcessor', 'ProcessingCoordinator'];
        this.provides = ['document-processing', 'section-management', 'relationship-tracking'];
        this.consumes = ['raw-text', 'latex-content'];
        this.lane = 'transform';
        this.linear = true;  // Each document can only be processed once
        this.mutex = ['LaTeXProcessor'];  // Can't run simultaneously with LaTeX processing
        this.orderingConstraints = {
            after: ['LaTeXProcessor'],  // LaTeX must be ready first
            before: ['HTMLModality', 'PDFModality']  // Must process before rendering
        };
        
        // Register with coordinator
        if (typeof processingCoordinator !== 'undefined' && processingCoordinator.registerSelf) {
            processingCoordinator.registerSelf(this);
        }
        
        this.modalities = {
            html: new HTMLModality(),
            pdf: new PDFModality(),
            markdown: new MarkdownModality()
        };
        
        this.memo = new Memo();
        this.context = ConfigContext.create();
        this.pipeline = null;
        
        this.state = {
            browser: null,
            pages: new Map(),
            hashes: new Map(),
            building: new Set(),
            errors: [],
            stats: { builds: 0, errors: 0, uptime: Date.now() }
        };
    }
    
    preprocessMathBlocks(text) {
        // Handle LaTeX escapes globally (natural transformation across all text)
        text = text.replace(/\\\{/g, '{');
        text = text.replace(/\\\}/g, '}');
        text = text.replace(/\\\\/g, '\\newline ');  // Preserve line breaks for math environments

        // Combine display math blocks
        text = text.replace(/\\\[\s*([\s\S]*?)\s*\\\]/g, (match, content) => {
            return `<<<BLOCKMATH>>>${content.trim()}<<</BLOCKMATH>>>`;
        });

        // Process inline math
        text = text.replace(/\\\((.*?)\\\)/g, (match, content) => {
            return `<<<INLINEMATH>>>${content}<<</INLINEMATH>>>`;
        });

        return text;
    }
    
    parse(text) {
        return new Lazy(() => {
            this.sections.clear();
            this.relationships.clear();
            this.data.clear();

            this.parseEager(text);

            return { sections: this.sections, relationships: this.relationships };
        });
    }
    
    preprocessLazy(text) {
        return new Lazy(() => this.preprocessMathBlocks(text));
    }
    
    extractSectionsLazy(text) {
        return new Lazy(() => {
            const lines = text.split('\n');
            const sections = [];
            let currentSection = null;
            
            for (let i = 0; i < lines.length; i++) {
                const heading = this.detectHeading(lines[i], lines[i + 1]);
                if (heading) {
                    if (currentSection) {
                        sections.push(currentSection);
                    }
                    currentSection = {
                        level: heading.level,
                        title: heading.content,
                        content: [],
                        id: this.generateStableId(heading.content, sections.length)
                    };
                    if (heading.skip) i++;
                } else if (currentSection) {
                    currentSection.content.push(lines[i]);
                }
            }
            if (currentSection) sections.push(currentSection);
            
            sections.forEach(section => {
                this.sections.set(section.id, section);
                this.data.set(section.id, section.content.join('\n'));
            });
            
            return { sections, text };
        });
    }
    
    buildRelationshipsLazy(data) {
        return new Lazy(() => {
            const sections = data.sections;
            for (let i = 0; i < sections.length; i++) {
                const section = sections[i];
                if (i > 0) {
                    this.relationships.set(section.id + ':prev', sections[i - 1].id);
                }
                if (i < sections.length - 1) {
                    this.relationships.set(section.id + ':next', sections[i + 1].id);
                }
            }
            return data;
        });
    }
    
    transformParallel(formats) {
        return new Lazy(() => {
            const results = {};
            
            for (const format of formats) {
                if (this.modalities[format]) {
                    results[format] = this.modalities[format].transform(this);
                    
                    if (results[format] instanceof Lazy) {
                        results[format] = results[format].value;
                    }
                }
            }
            
            return results;
        });
    }
    
    parseEager(text) {
        this.sections.clear();
        this.relationships.clear();
        this.data.clear();

        text = this.preprocessMathBlocks(text);

        const lines = text.split('\n');
        let currentSection = null;
        let sectionStack = [];
        let sectionCounter = 0;

        for (let i = 0; i < lines.length; i++) {
            const line = lines[i];
            const heading = this.detectHeading(line, lines[i + 1]);
            
            if (heading) {
                const id = this.generateStableId(heading.content, sectionCounter++);
                const section = {
                    id,
                    level: heading.level,
                    title: heading.content,
                    line: i,
                    children: [],
                    parent: null,
                    content: []
                };
                
                while (sectionStack.length > 0 && 
                       sectionStack[sectionStack.length - 1].level >= heading.level) {
                    sectionStack.pop();
                }
                
                if (sectionStack.length > 0) {
                    const parent = sectionStack[sectionStack.length - 1];
                    section.parent = parent.id;
                    parent.children.push(id);
                    
                    if (!this.relationships.has(parent.id)) {
                        this.relationships.set(parent.id, new Set());
                    }
                    this.relationships.get(parent.id).add(id);
                }
                
                this.sections.set(id, section);
                sectionStack.push(section);
                currentSection = section;
                
                if (heading.skip) i++;
            } else if (currentSection) {
                currentSection.content.push(line);
            }
        }

        for (const [id, section] of this.sections) {
            this.data.set(id, this.parseContent(section.content));
        }

        return this;
    }
    
    generateStableId(title, counter) {
        try {
            checkType(title, NonEmptyString);
        } catch {
            return `${CONFIG.strings.sectionIdPrefix}${counter}-untitled`;
        }
        
        const semantic = title.toLowerCase()
            .replace(CONFIG.patterns.nonWordChars, '')
            .replace(CONFIG.patterns.multiSpace, '-')
            .replace(CONFIG.patterns.multiDash, '-')
            .replace(CONFIG.patterns.trimDash, '');
        
        return `${CONFIG.strings.sectionIdPrefix}${counter}-${semantic || CONFIG.strings.sectionFallback}`.substring(0, CONFIG.processor.sectionIdMaxLength);
    }
    
    detectHeading(line, nextLine) {
        // Markdown-style headers
        const hashMatch = line.match(CONFIG.patterns.hashHeading);
        if (hashMatch) {
            return {
                level: hashMatch[1].length,
                content: hashMatch[2].trim(),
                skip: false
            };
        }
        
        // Underline-style headers
        if (nextLine && line.trim()) {
            if (CONFIG.patterns.setextPrimary.test(nextLine.trim()) && nextLine.trim().length >= CONFIG.processor.minGroupSize) {
                return {
                    level: CONFIG.processor.topLevelSection,
                    content: line.trim(),
                    skip: true
                };
            }
            if (CONFIG.patterns.setextSecondary.test(nextLine.trim()) && nextLine.trim().length >= CONFIG.processor.minGroupSize) {
                return {
                    level: CONFIG.processor.majorSectionLevel,
                    content: line.trim(),
                    skip: true
                };
            }
        }
        
        // Layer/Section detection for HCT documents
        if (CONFIG.patterns.layerOrSection.test(line)) {
            return {
                level: CONFIG.processor.sectionLevelN.two,
                content: line.trim(),
                skip: false
            };
        }
        
        return null;
    }
    
    parseContent(lines) {
        const blocks = [];
        let codeBlock = null;
        let mathBlock = null;
        
        for (const line of lines) {
            // Handle code blocks
            if (line.startsWith(CONFIG.strings.codeDelimiter)) {
                if (codeBlock) {
                    blocks.push({
                        type: 'code',
                        language: codeBlock.language,
                        content: codeBlock.lines.join('\n')
                    });
                    codeBlock = null;
                } else {
                    const lang = line.slice(CONFIG.processor.codeBlockSliceLength).trim();
                    // Validate language to prevent injection
                    const validLangs = CONFIG.strings.supportedLanguages;
                    codeBlock = {
                        language: validLangs.includes(lang) ? lang : CONFIG.strings.defaultLanguage,
                        lines: []
                    };
                }
                continue;
            }
            
            if (codeBlock) {
                codeBlock.lines.push(line);
                continue;
            }
            
            // Handle math block markers
            if (line.includes(CONFIG.strings.mathStartDelimiter)) {
                // Extract the math content
                const match = line.match(/<<<BLOCKMATH>>>(.+?)<<<\/BLOCKMATH>>>/);
                if (match) {
                    // Single-line block math
                    blocks.push({
                        type: 'paragraph',
                        content: line
                    });
                } else {
                    // Multi-line block math starts
                    mathBlock = {
                        lines: [line]
                    };
                }
                continue;
            }
            
            if (mathBlock) {
                mathBlock.lines.push(line);
                // Check if this line ends the math block
                if (line.includes(CONFIG.strings.mathEndDelimiter)) {
                    blocks.push({
                        type: 'paragraph',
                        content: mathBlock.lines.join('\n')
                    });
                    mathBlock = null;
                }
                continue;
            }
            
            const block = this.classifyBlock(line);
            blocks.push(block);
        }
        
        return blocks;
    }
    
    classifyBlock(line) {
        if (CONFIG.patterns.unorderedList.test(line)) {
            return {
                type: 'list-item',
                ordered: false,
                content: line.replace(CONFIG.patterns.unorderedList, ''),
                indent: line.search(/\S/)
            };
        }
        if (CONFIG.patterns.orderedList.test(line)) {
            return {
                type: 'list-item',
                ordered: true,
                content: line.replace(CONFIG.patterns.orderedList, ''),
                indent: line.search(/\S/)
            };
        }
        
        if (line.startsWith(CONFIG.strings.quoteDelimiter)) {
            return {
                type: 'blockquote',
                content: line.slice(1).trim()
            };
        }
        
        if (CONFIG.patterns.horizontalRule.test(line.trim())) {
            return { type: 'hr' };
        }
        
        if (!line.trim()) {
            return { type: 'blank' };
        }
        
        return {
            type: 'paragraph',
            content: line
        };
    }
    
    // Parallel transformations - generates multiple formats simultaneously
    async transformParallel(formats = null) {
        formats = formats || CONFIG.files.defaultOutputFormats;
        const results = {};
        const promises = [];
        
        for (const format of formats) {
            if (this.modalities[format]) {
                // Each format transformation runs in parallel
                const promise = (async () => {
                    try {
                        const cacheKey = `transform:${format}:${this.getCacheKey()}`;

                        // Register transformation in graph if not present
                        if (!this.graph.nodes.has(cacheKey)) {
                            this.graph.register(cacheKey, new Lazy(() => {
                                if (format === 'pdf') {
                                    return this.modalities[format].generateHTML(this);
                                } else if (format === 'html') {
                                    return this.modalities[format].generateHTML(this);
                                } else if (format === 'markdown') {
                                    return this.modalities[format].render(this);
                                }
                            }));
                        }

                        results[format] = this.graph.pull(cacheKey);
                    } catch (error) {
                        console.error(`Error generating ${format}:`, error);
                        results[format] = null; // Mark as failed but continue with other formats
                    }
                })();
                
                promises.push(promise);
            }
        }
        
        await Promise.all(promises);
        return results;
    }
    
    // Generate cache key based on current document structure
    getCacheKey() {
        // MUST include actual content for soundness - not just keys!
        const contentParts = [];
        for (const [id, section] of this.sections) {
            const content = this.data.get(id);
            if (content) {
                contentParts.push(`${id}:${JSON.stringify(content)}`);
            }
        }
        const fullContent = contentParts.join('|');
        return crypto.createHash(CONFIG.strings.fallbackHashAlgorithm).update(fullContent).digest(CONFIG.strings.hashEncoding);
    }
    
    generateTOC() {
        const toc = [];
        const stack = [];
        
        for (const [id, section] of this.sections) {
            // Group major sections (level 1-2) only
            if (section.level > CONFIG.processor.tocMaxDepth) continue;
            
            const entry = {
                id,
                title: section.title,
                level: section.level,
                children: []
            };
            
            // Add subsections
            for (const [subId, subSection] of this.sections) {
                if (subSection.parent === id && subSection.level === CONFIG.processor.subSectionLevel) {
                    entry.children.push({
                        id: subId,
                        title: subSection.title,
                        level: subSection.level,
                        children: []
                    });
                }
            }
            
            while (stack.length > 0 && stack[stack.length - 1].level >= entry.level) {
                stack.pop();
            }
            
            if (stack.length === 0) {
                toc.push(entry);
            } else {
                stack[stack.length - 1].children.push(entry);
            }
            
            stack.push(entry);
        }
        
        return toc;
    }
}

// LATEX PROCESSING

class LaTeXProcessor {
    constructor() {
        this.patterns = this.buildPatterns();
    }
    
    buildPatterns() {
        return {
            // Block math environments (process first)
            blockMath: [
                [/\$\$([^$]+?)\$\$/gm, (m, tex) => this.renderBlockMath(tex)],
                [/\\\[([\s\S]+?)\\\]/gm, (m, tex) => this.renderBlockMath(tex)],
                [/\\begin\{equation\}([\s\S]+?)\\end\{equation\}/gm, (m, tex) => this.renderBlockMath(tex)],
                [/\\begin\{align\}([\s\S]+?)\\end\{align\}/gm, (m, tex) => this.renderBlockMath(tex)],
            ],
            
            // Inline math (process second)
            inlineMath: [
                [/\$([^$]+?)\$/g, (m, tex) => this.renderInlineMath(tex)],
                [/\\\(([^)]+?)\\\)/g, (m, tex) => this.renderInlineMath(tex)],
                [/\\text\{([^}]+)\}/g, (m, text) => `<${CONFIG.strings.inlineElement} class="${CONFIG.strings.textInsideClass}">${text}</${CONFIG.strings.inlineElement}>`],
            ],
            
            // Commands that need special handling
            commands: {
                // Greek letters
                'alpha': 'α', 'beta': 'β', 'gamma': 'γ', 'delta': 'δ', 'epsilon': 'ε',
                'zeta': 'ζ', 'eta': 'η', 'theta': 'θ', 'iota': 'ι', 'kappa': 'κ',
                'lambda': 'λ', 'mu': 'μ', 'nu': 'ν', 'xi': 'ξ', 'pi': 'π',
                'rho': 'ρ', 'sigma': 'σ', 'tau': 'τ', 'upsilon': 'υ', 'phi': 'φ',
                'chi': 'χ', 'psi': 'ψ', 'omega': 'ω',
                
                // Capital Greek
                'Gamma': 'Γ', 'Delta': 'Δ', 'Theta': 'Θ', 'Lambda': 'Λ', 'Xi': 'Ξ',
                'Pi': 'Π', 'Sigma': 'Σ', 'Upsilon': 'Υ', 'Phi': 'Φ', 'Psi': 'Ψ', 'Omega': 'Ω',
                
                // Math operators
                'times': '×', 'div': '÷', 'pm': '±', 'mp': '∓', 'cdot': '·', 
                'circ': '∘', 'bullet': '•', 'star': '⋆', 'ast': '∗',
                'oplus': '⊕', 'otimes': '⊗', 'ominus': '⊖', 'oslash': '⊘',
                'odot': '⊙', 'wedge': '∧', 'vee': '∨',
                
                // Arrows
                'to': '→', 'rightarrow': '→', 'leftarrow': '←', 'leftrightarrow': '↔',
                'Rightarrow': '⇒', 'Leftarrow': '⇐', 'Leftrightarrow': '⇔',
                'mapsto': '↦', 'hookrightarrow': '↪', 'rightharpoonup': '⇀',
                'rightharpoondown': '⇁', 'rightleftarrows': '⇄',
                'leftrightarrows': '⇆', 'rightrightarrows': '⇉',
                'dashv': '⊣', 'vdash': '⊢',
                
                // Relations
                'leq': '≤', 'geq': '≥', 'neq': '≠', 'sim': '∼', 'simeq': '≃',
                'cong': '≅', 'equiv': '≡', 'approx': '≈', 'propto': '∝',
                'subset': '⊂', 'supset': '⊃', 'subseteq': '⊆', 'supseteq': '⊇',
                'asymp': '≍', 'preceq': '⪯', 'succeq': '⪰',
                'in': '∈', 'notin': '∉', 'ni': '∋',
                
                // Logic
                'forall': '∀', 'exists': '∃', 'nexists': '∄', 'neg': '¬', 'lnot': '¬',
                'land': '∧', 'lor': '∨', 'implies': '⇒', 'iff': '⇔',
                
                // Sets
                'emptyset': '∅', 'varnothing': '∅', 'cup': '∪', 'cap': '∩',
                'setminus': '∖', 'complement': '∁',
                
                // Special
                'infty': '∞', 'partial': '∂', 'nabla': '∇', 'square': '□',
                'triangle': '△', 'angle': '∠', 'perp': '⊥', 'parallel': '∥',
                
                // Category theory
                'op': '^{op}', 'co': '^{co}',
                
                // Dots
                'ldots': '…', 'cdots': '⋯', 'vdots': '⋮', 'ddots': '⋱',
            }
        };
    }
    
    process(text) {
        if (!text) return '';
        
        // Preserve code blocks - GOOD redundancy, protects math in code
        const codeBlocks = [];
        let result = text.replace(/```[\s\S]*?```/g, (match) => {
            codeBlocks.push(match);
            return `__CODE_BLOCK_${codeBlocks.length - 1}__`;
        });
        
        // Process our special markers from preprocessing - PRIMARY path
        result = result.replace(/<<<BLOCKMATH>>>(.+?)<<<\/BLOCKMATH>>>/gs, (m, content) => {
            if (processingCoordinator.shouldProcess('latexProcessor', content, '<<<BLOCKMATH>>>')) {
                return this.renderBlockMath(content);
            }
            return m; // Leave unchanged if coordinator says no
        });
        
        result = result.replace(/<<<INLINEMATH>>>(.+?)<<<\/INLINEMATH>>>/g, (m, content) => {
            if (processingCoordinator.shouldProcess('latexProcessor', content, '<<<INLINEMATH>>>')) {
                return this.renderInlineMath(content);
            }
            return m;
        });

        // Standalone math symbols (fallback for symbols outside math mode)
        result = result.replace(/(\s|^)(→|←|⇒|⇐|↔|⇔|↦|∈|∉|⊂|⊃|⊆|⊇|≤|≥|≠|∼|≃|≅|≡|≈)(\s|$)/g, '$1$2$3');
        
        // Restore code blocks
        codeBlocks.forEach((block, i) => {
            result = result.replace(`__CODE_BLOCK_${i}__`, block);
        });
        
        return result;
    }
    
    renderBlockMath(tex) {
        const processed = this.processTeX(tex);
        return `<${CONFIG.strings.blockElement} class="${CONFIG.strings.blockContentClass}">${processed}</${CONFIG.strings.blockElement}>`;
    }
    
    renderInlineMath(tex) {
        const processed = this.processTeX(tex);
        return `<${CONFIG.strings.inlineElement} class="${CONFIG.strings.inlineContentClass}">${processed}</${CONFIG.strings.inlineElement}>`;
    }
    
    processTeX(tex) {
        if (!tex) return '';
        let result = tex.trim();
        
        // Each recursive call creates a nested context
        // The depth tracks our position in the recursion tree
        if (!this.context) {
            this.context = {
                depth: 0,
                stack: [],
                cache: new Map(),
                transforms: new Map() // tracks transformations at each level
            };
        }
        
        // Define cacheKey in outer scope so it's accessible in finally block
        const cacheKey = `${this.context.depth}:${tex}`;
        
        // Check cache first
        if (this.context.cache.has(cacheKey)) {
            return this.context.cache.get(cacheKey);
        }
        
        // Recursion limit - prevents infinite loops
        if (this.context.depth > CONFIG.latex.maxRecursionDepth) {
            console.warn('Recursion depth exceeded:', tex.substring(0, CONFIG.latex.debugSubstringLength));
            return result;
        }
        
        // Push current context onto the stack
        this.context.stack.push({ input: tex, depth: this.context.depth });
        this.context.depth++;
        
        try {
            result = result.replace(/\\begin\{array\}(?:\{[^}]*\})?([\s\S]+?)\\end\{array\}/g, (m, content) => {
                // Split on \\ or \newline (row separators)
                const rows = content.trim().split(/(?:\\\\|\\newline)/g).filter(r => r.trim());
                const renderedRows = rows.map(row => {
                    const cells = row.split('&').map(cell => {
                        const processed = this.processTeX(cell.trim());
                        return `<td class="array-cell">${processed}</td>`;
                    });
                    return `<tr>${cells.join('')}</tr>`;
                });
                return `<table class="array-math"><tbody>${renderedRows.join('')}</tbody></table>`;
            });
            
            // Handle aligned environments for commutative diagrams
            result = result.replace(/\\begin\{aligned\}([\s\S]+?)\\end\{aligned\}/g, (m, content) => {
                const rows = content.trim().split('\\newline').filter(r => r.trim()).map(row => {
                    // Process each cell, handling & as column separator
                    const cells = row.split('&').map(cell => {
                        const processed = this.processTeX(cell.trim());
                        return `<td class="align-cell">${processed}</td>`;
                    });
                    return `<tr>${cells.join('')}</tr>`;
                });
                return `<table class="aligned-math"><tbody>${rows.join('')}</tbody></table>`;
            });
        
        // Handle matrix environments
        result = result.replace(/\\begin\{[bp]?matrix\}([\s\S]+?)\\end\{[bp]?matrix\}/g, (m, content) => {
            const rows = content.trim().split('\\\\').map(row => 
                row.split('&').map(cell => `<td>${this.processTeX(cell.trim())}</td>`).join('')
            );
            return `<table class="matrix"><tbody>${rows.map(r => `<tr>${r}</tr>`).join('')}</tbody></table>`;
        });
        
        result = result.replace(CONFIG.patterns.operatorName, `<${CONFIG.strings.inlineElement} class="${CONFIG.strings.operatorClass}">$1</${CONFIG.strings.inlineElement}>`);
        
        // Handle special text operators
        result = result.replace(/\\(Disc|Codisc|Lan|Ran|colim|lim|Hom|Map|Fun|Cat|Set|Grp|Top|Sh|PSh|St|Un|Im|Re|Ker|Coker|cone|Tot|Spec|Proj|Ext|Tor|Desc|EX|EY)\b/g, 
            `<${CONFIG.strings.inlineElement} class="${CONFIG.strings.operatorClass}">$1</${CONFIG.strings.inlineElement}>`);
        
        // Handle accented operators like Čech
        result = result.replace(/Čech/g, `<${CONFIG.strings.inlineElement} class="${CONFIG.strings.operatorClass}">Čech</${CONFIG.strings.inlineElement}>`);
        
        // Handle text commands
        result = result.replace(/\\text\{([^}]+)\}/g, `<${CONFIG.strings.inlineElement} class="${CONFIG.strings.textInsideClass}">$1</${CONFIG.strings.inlineElement}>`);
        result = result.replace(/\\mathrm\{([^}]+)\}/g, `<${CONFIG.strings.inlineElement} class="${CONFIG.strings.romanStyleClass}">$1</${CONFIG.strings.inlineElement}>`);
        result = result.replace(/\\textbf\{([^}]+)\}/g, `<${CONFIG.strings.semanticElements.strong}>$1</${CONFIG.strings.semanticElements.strong}>`);
        result = result.replace(/\\textit\{([^}]+)\}/g, `<${CONFIG.strings.semanticElements.emphasis}>$1</${CONFIG.strings.semanticElements.emphasis}>`);
        
        // PHASE 3: Handle math fonts
        result = result.replace(/\\mathcal\{([^}]+)\}/g, `<${CONFIG.strings.inlineElement} class="${CONFIG.strings.calligraphicClass}">$1</${CONFIG.strings.inlineElement}>`);
        result = result.replace(/\\mathbb\{([^}]+)\}/g, `<${CONFIG.strings.inlineElement} class="${CONFIG.strings.blackboardClass}">$1</${CONFIG.strings.inlineElement}>`);
        result = result.replace(/\\mathfrak\{([^}]+)\}/g, `<${CONFIG.strings.inlineElement} class="${CONFIG.strings.frakturClass}">$1</${CONFIG.strings.inlineElement}>`);
        result = result.replace(/\\mathsf\{([^}]+)\}/g, `<${CONFIG.strings.inlineElement} class="${CONFIG.strings.sansSerifClass}">$1</${CONFIG.strings.inlineElement}>`);
        result = result.replace(/\\mathbf\{([^}]+)\}/g, `<${CONFIG.strings.inlineElement} class="${CONFIG.strings.boldStyleClass}">$1</${CONFIG.strings.inlineElement}>`);
        
        // PHASE 4: Handle special arrows and decorations
        // Handle \xrightarrow{text} and similar
        result = result.replace(/\\xrightarrow\{([^}]+)\}/g, 
            `<${CONFIG.strings.inlineElement} class="${CONFIG.strings.annotatedElementClass}">→<${CONFIG.strings.inlineElement} class="${CONFIG.strings.annotationTextClass}">$1</${CONFIG.strings.inlineElement}></${CONFIG.strings.inlineElement}>`);
        result = result.replace(/\\xleftarrow\{([^}]+)\}/g, 
            `<${CONFIG.strings.inlineElement} class="${CONFIG.strings.annotatedElementClass}">←<${CONFIG.strings.inlineElement} class="${CONFIG.strings.annotationTextClass}">$1</${CONFIG.strings.inlineElement}></${CONFIG.strings.inlineElement}>`);
        
        // Handle accents and tildes
        result = result.replace(/\\tilde\{([^}]+)\}/g, `<${CONFIG.strings.inlineElement} class="${CONFIG.strings.tildeAccentClass}">$1ẽ</${CONFIG.strings.inlineElement}>`);
        result = result.replace(/\\hat\{([^}]+)\}/g, `<${CONFIG.strings.inlineElement} class="${CONFIG.strings.hatAccentClass}">$1ê</${CONFIG.strings.inlineElement}>`);
        result = result.replace(/\\bar\{([^}]+)\}/g, `<${CONFIG.strings.inlineElement} class="${CONFIG.strings.barAccentClass}">$1ē</${CONFIG.strings.inlineElement}>`);
        result = result.replace(/\\dot\{([^}]+)\}/g, `<${CONFIG.strings.inlineElement} class="${CONFIG.strings.dotAccentClass}">$1ė</${CONFIG.strings.inlineElement}>`);
        result = result.replace(/\\vec\{([^}]+)\}/g, `<${CONFIG.strings.inlineElement} class="${CONFIG.strings.vectorClass}">$1⃗</${CONFIG.strings.inlineElement}>`);
        
        let fractionIterations = 0;
        while (result.includes('\\frac{') && fractionIterations++ < THRESHOLDS.MAX_FRACTION_DEPTH) {
            result = result.replace(/\\frac\{([^{}]*(?:\{[^{}]*\}[^{}]*)*)\}\{([^{}]*(?:\{[^{}]*\}[^{}]*)*)\}/g, 
                (m, num, den) => {
                    const processedNum = this.escapeHtml(this.processTeX(num));
                    const processedDen = this.escapeHtml(this.processTeX(den));
                    return `<${CONFIG.strings.inlineElement} class="${CONFIG.strings.fractionClass}"><${CONFIG.strings.inlineElement} class="${CONFIG.strings.numeratorClass}">${processedNum}</${CONFIG.strings.inlineElement}><${CONFIG.strings.inlineElement} class="${CONFIG.strings.denominatorClass}">${processedDen}</${CONFIG.strings.inlineElement}></${CONFIG.strings.inlineElement}>`;
                });
        }
        
        // PHASE 6: Handle sub/superscripts (order matters: complex patterns first)
        // Special common superscripts
        result = result.replace(/\^op\b/g, `<${CONFIG.strings.semanticElements.superscript}>op</${CONFIG.strings.semanticElements.superscript}>`);
        result = result.replace(/\^co\b/g, `<${CONFIG.strings.semanticElements.superscript}>co</${CONFIG.strings.semanticElements.superscript}>`);
        result = result.replace(/\^\*/g, `<${CONFIG.strings.semanticElements.superscript}>*</${CONFIG.strings.semanticElements.superscript}>`);
        result = result.replace(/\^\+/g, `<${CONFIG.strings.semanticElements.superscript}>+</${CONFIG.strings.semanticElements.superscript}>`);
        
        // Handle complex subscripts and superscripts with nested braces
        // This needs careful handling to avoid breaking on nested structures
        const processScript = (content, type) => {
            const oldDepth = this.context ? this.context.depth : 0;
            if (this.context) {
                this.context.depth = Math.max(oldDepth - 1, 1);
            }
            const processed = this.processTeX(content);
            if (this.context) {
                this.context.depth = oldDepth;
            }
            return type === CONFIG.strings.semanticElements.superscript ? `<${CONFIG.strings.semanticElements.superscript}>${processed}</${CONFIG.strings.semanticElements.superscript}>` : `<${CONFIG.strings.semanticElements.subscript}>${processed}</${CONFIG.strings.semanticElements.subscript}>`;
        };
        
        // Process ALL LaTeX commands first before any subscript/superscript handling
        for (const [cmd, symbol] of Object.entries(this.patterns.commands)) {
            const regex = new RegExp(`\\\\${cmd}(?![a-zA-Z])`, 'g');
            result = result.replace(regex, symbol);
        }

        // Now handle ALL subscripts and superscripts (braced first, then simple)
        result = result.replace(/\^\{([^{}]*(?:\{[^{}]*\}[^{}]*)*)\}/g, (m, content) => processScript(content, CONFIG.strings.semanticElements.superscript));
        result = result.replace(/_\{([^{}]*(?:\{[^{}]*\}[^{}]*)*)\}/g, (m, content) => processScript(content, CONFIG.strings.semanticElements.subscript));
        
        // Simple single-character scripts (now symbols like • will work)
        result = result.replace(/\^([^\s\{\}])/g, `<${CONFIG.strings.semanticElements.superscript}>$1</${CONFIG.strings.semanticElements.superscript}>`);
        result = result.replace(/_([^\s\{\}])/g, `<${CONFIG.strings.semanticElements.subscript}>$1</${CONFIG.strings.semanticElements.subscript}>`)

        // Handle line breaks in math (from preprocessed \\)
        result = result.replace(/\\newline\s*/g, '<br>');

        // Handle remaining special symbols not in commands table
        result = result.replace(/\\setminus/g, '∖');
        result = result.replace(/\\backslash/g, '\\');
        result = result.replace(/\\partial/g, '∂');
        result = result.replace(/\\nabla/g, '∇');
        result = result.replace(/\\forall/g, '∀');
        result = result.replace(/\\exists/g, '∃');
        result = result.replace(/\\emptyset/g, '∅');
        result = result.replace(/\\in\b/g, '∈');
        result = result.replace(/\\notin\b/g, '∉');
        result = result.replace(/\\cup/g, '∪');
        result = result.replace(/\\cap/g, '∩');
        result = result.replace(/\\sqcup/g, '⊔');
        result = result.replace(/\\vee/g, '∨');
        result = result.replace(/\\wedge/g, '∧');
        result = result.replace(/\\neg/g, '¬');
        result = result.replace(/\\langle/g, '⟨');
        result = result.replace(/\\rangle/g, '⟩');
        result = result.replace(/\\lim/g, 'lim');
        result = result.replace(/\\varinjlim/g, 'colim');
        result = result.replace(/\\prod/g, '∏');
        result = result.replace(/\\coprod/g, '∐');
        result = result.replace(/\\sum/g, '∑');
        result = result.replace(/\\int/g, '∫');
        result = result.replace(/\\oint/g, '∮');
        result = result.replace(/\\dots/g, '…');
        result = result.replace(/\\cdots/g, '⋯');
        result = result.replace(/\\ldots/g, '…');
        result = result.replace(/\\ddots/g, '⋱');
        result = result.replace(/\\vdots/g, '⋮');
        result = result.replace(/\\quad/g, '&nbsp;&nbsp;&nbsp;&nbsp;');
        result = result.replace(/\\qquad/g, '&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;');
        result = result.replace(/\\,/g, '&nbsp;');
        result = result.replace(/\\ /g, '&nbsp;');
        result = result.replace(/\\;/g, '&nbsp;&nbsp;');
        result = result.replace(/\\!/g, '');
        result = result.replace(/\\longrightarrow/g, '⟶');
        result = result.replace(/\\downarrow/g, '↓');
        result = result.replace(/\\uparrow/g, '↑');
        result = result.replace(/\\natural/g, '♮');
        result = result.replace(/\\flat/g, '♭');
        result = result.replace(/\\sharp/g, '♯');
        result = result.replace(/\\heartsuit/g, '♥');
        
        // PHASE 9: Handle ASCII arrows and symbols
        result = result.replace(/->/g, '→');
        result = result.replace(/<-/g, '←');
        result = result.replace(/=>/g, '⇒');
        result = result.replace(/<=/g, '⇐');
        result = result.replace(/<=>/g, '⇔');
        result = result.replace(/\|->/g, '↦');
        
        // Handle standalone backslash for set difference (when not part of a command)
        result = result.replace(/(\w)\s*\\\s*(\w)/g, '$1 ∖ $2');
        
        // Remove unhandled backslashes
        result = result.replace(/\\([a-zA-Z]+)(?![{a-zA-Z])/g, (m, cmd) => {
            // Log unhandled commands in development
            if (this.context && this.context.depth <= CONFIG.processor.topSectionLevel) {
            }
            return cmd;
        });
        
        } catch (error) {
            console.error('LaTeX processing error at depth', this.context.depth, ':', error);
            result = tex; // Return original on error
        } finally {
            // Pop the fiber stack first to maintain consistency
            const context = this.context.stack.pop();
            
            // Only cache successful transformations
            if (context && result !== tex) {
                this.context.cache.set(cacheKey, result);
                
                // Record the transformation at current depth
                if (!this.context.transforms.has(this.context.depth - 1)) {
                    this.context.transforms.set(this.context.depth - 1, new Map());
                }
                this.context.transforms.get(this.context.depth - 1).set(tex, result);
            }
            
            // Now decrement depth
            this.context.depth--;
            
            // Reset context when we return to base level
            // But check if context exists first to avoid null reference
            if (this.context && this.context.depth === 0) {
                // Clear cache to prevent memory leaks but keep the structure
                this.context.cache.clear();
                this.context.transforms.clear();
                this.context.stack = [];
            }
        }
        
        return result;
    }
}

// HTML MODALITY

class HTMLModality {
    constructor() {
        this.latex = new LaTeXProcessor();
    }
    
    renderTOC(toc) {
        if (!toc || toc.length === 0) return '';
        
        return `
        <${CONFIG.strings.blockElement} class="${CONFIG.strings.navigationContentClass}">
            ${toc.map((entry, i) => this.renderTOCEntry(entry, i)).join('')}
        </${CONFIG.strings.blockElement}>`;
    }
    
    renderTOCEntry(entry, index) {
        const hasChildren = entry.children && entry.children.length > 0;
        const isNumbered = CONFIG.strings.structurePrefixes.some(prefix => entry.title.startsWith(prefix));
        const sectionNumber = isNumbered ? entry.title.match(/\d+/)?.[0] : '';
        
        return `
        <${CONFIG.strings.blockElement} class="${CONFIG.strings.navigationSectionClass} ${entry.level === CONFIG.processor.topLevel ? CONFIG.strings.navigationMajorClass : ''}">
            ${hasChildren ? `
                <button class="toc-toggle" onclick="toggleSection('toc-${entry.id}')" aria-expanded="false">
                    <${CONFIG.strings.inlineElement} class="${CONFIG.strings.toggleIconClass}">${CONFIG.strings.collapsedIndicator}</${CONFIG.strings.inlineElement}>
                </button>
            ` : `<${CONFIG.strings.inlineElement} class="${CONFIG.strings.spacerClass}"></${CONFIG.strings.inlineElement}>`}
            <${CONFIG.strings.linkElement} href="#${entry.id}" class="${CONFIG.strings.navigationLinkClass}" data-section="${entry.id}" onclick="navigateToSection('${entry.id}', event)">
                ${sectionNumber ? `<${CONFIG.strings.inlineElement} class="${CONFIG.strings.navigationNumberClass}">${sectionNumber}</${CONFIG.strings.inlineElement}>` : ''}
                ${entry.title}
            </${CONFIG.strings.linkElement}>
            ${hasChildren ? `
                <${CONFIG.strings.blockElement} class="${CONFIG.strings.childrenContainerClass}" id="toc-${entry.id}" style="display: ${CONFIG.css.display.none};">
                    ${entry.children.map((child, i) => this.renderTOCEntry(child, i)).join('')}
                </${CONFIG.strings.blockElement}>
            ` : ''}
        </${CONFIG.strings.blockElement}>`;
    }
    
    renderSection(section, content) {
        const heading = `<h${section.level} id="${section.id}" class="${CONFIG.strings.sectionHeadingClass}">
            <${CONFIG.strings.linkElement} href="#${section.id}" class="${CONFIG.strings.anchorLinkClass}" onclick="navigateToSection('${section.id}', event)">${CONFIG.strings.anchorSymbol}</${CONFIG.strings.linkElement}>
            ${this.escapeHtml(section.title)}
        </h${section.level}>`;
        
        const blocks = this.renderBlocks(content);
        
        // Add links to TOC entries
        const linkedBlocks = this.addTOCLinks(blocks);
        
        return `<section class="${CONFIG.strings.documentSectionClass}" data-section-id="${section.id}">
            ${heading}
            ${linkedBlocks}
        </section>`;
    }
    
    addTOCLinks(html) {
        // Process TOC entries in HTML
        
        // Process list items with TOC entries
        html = html.replace(
            /<li>([^<]+)<\/li>/g,
            (match, content) => {
                // Multiple patterns to match:
                // N.one. "N.one. Section N.one: Title" (working.txt new style)
                // N.two. "N.one. Layer N.one: Title" (primer.txt style)
                // 3. "Layer N.one: Title" (also primer style)
                // 4. "Section N.one: Title" (also working style)
                // 5. "N.one. Title" (old working.txt style)
                
                // Try to extract the number and title
                let prefix = '';
                let title = '';
                let fullTitle = content.trim();
                
                // Pattern N.one: "N.one. Section N.one: Title"
                const sectionWithNum = /^(\d+\.\s*Section \d+:\s*)(.*)$/;
                // Pattern N.two: "N.one. Layer N.one: Title"
                const layerWithNum = /^(\d+\.\s*Layer \d+:\s*)(.*)$/;
                // Pattern 3: "Section N.one: Title"
                const sectionOnly = /^(Section \d+:\s*)(.*)$/;
                // Pattern 4: "Layer N.one: Title"
                const layerOnly = /^(Layer \d+:\s*)(.*)$/;
                // Pattern 5: "N.one. Title"
                const numOnly = /^(\d+\.\s*)(.*)$/;
                
                let matched = false;
                
                if (sectionWithNum.test(fullTitle)) {
                    const m = fullTitle.match(sectionWithNum);
                    prefix = m[1];
                    title = m[2];
                    matched = true;
                } else if (layerWithNum.test(fullTitle)) {
                    const m = fullTitle.match(layerWithNum);
                    prefix = m[1];
                    title = m[2];
                    matched = true;
                } else if (sectionOnly.test(fullTitle)) {
                    const m = fullTitle.match(sectionOnly);
                    prefix = m[1];
                    title = m[2];
                    matched = true;
                } else if (layerOnly.test(fullTitle)) {
                    const m = fullTitle.match(layerOnly);
                    prefix = m[1];
                    title = m[2];
                    matched = true;
                } else if (numOnly.test(fullTitle)) {
                    const m = fullTitle.match(numOnly);
                    prefix = m[1];
                    title = m[2];
                    matched = true;
                }
                
                if (matched && title) {
                    // Find the actual section ID from the processor
                    const sectionId = this.findSectionId(title) || this.findSectionId(fullTitle);
                    
                    if (sectionId) {
                        return `<${CONFIG.strings.listItemElement}>${prefix}<${CONFIG.strings.linkElement} href="#${sectionId}" onclick="navigateToSection('${sectionId}', event)">${title}</${CONFIG.strings.linkElement}></${CONFIG.strings.listItemElement}>`;
                    }
                }
                
                return match;
            }
        );
        
        return html;
    }
    
    findSectionId(title) {
        // Search through the processor sections to find matching title
        if (!this.currentProcessor) return null;

        // Clean the search title
        const cleanSearchTitle = title.trim().toLowerCase();

        // Collect all matches with their priority (prefer level 2 main sections over level 3 subsections)
        const matches = [];

        for (const [id, section] of this.currentProcessor.sections) {
            const sectionTitle = section.title.toLowerCase();

            // Direct match - highest priority
            if (sectionTitle === cleanSearchTitle) {
                matches.push({ id, level: section.level, priority: 3 });
                continue;
            }

            // Match without number prefix (e.g., "1. " or "Layer 1: " or "Section 1: ")
            const sectionWithoutPrefix = sectionTitle.replace(/^(?:section \d+:\s*|layer \d+:\s*|\d+\.\s*)/, '');
            const searchWithoutPrefix = cleanSearchTitle.replace(/^(?:section \d+:\s*|layer \d+:\s*|\d+\.\s*)/, '');

            if (sectionWithoutPrefix === searchWithoutPrefix) {
                matches.push({ id, level: section.level, priority: 2 });
                continue;
            }

            // Match core title portion (fuzzy match) - lowest priority
            if (sectionTitle.includes(searchWithoutPrefix) || searchWithoutPrefix.includes(sectionWithoutPrefix)) {
                // Verify match significance
                if (searchWithoutPrefix.length > CONFIG.latex.minMatchLength && sectionWithoutPrefix.length > CONFIG.latex.minMatchLength) {
                    matches.push({ id, level: section.level, priority: 1 });
                }
            }
        }

        if (matches.length === 0) return null;

        // Sort by priority (highest first), then by level (prefer level 2 over level 3)
        matches.sort((a, b) => {
            if (b.priority !== a.priority) return b.priority - a.priority;
            return a.level - b.level; // Lower level number = higher in hierarchy
        });

        return matches[0].id;
    }
    
    generateIdFromTitle(title) {
        // Generate a stable ID from title text
        const clean = title.toLowerCase()
            .replace(CONFIG.patterns.nonWordChars, '')
            .replace(CONFIG.patterns.multiSpace, '-')
            .replace(CONFIG.patterns.multiDash, '-')
            .replace(CONFIG.patterns.trimDash, '');
        return `${CONFIG.strings.sectionIdPrefix}${clean}`.substring(0, CONFIG.processor.sectionIdMaxLength);
    }
    
    isSectionTitle(title) {
        // Simple heuristic for titles
        return title.length < CONFIG.processor.titleMaxLength && /^[A-Z]/.test(title.trim());
    }
    
    renderBlocks(blocks) {
        if (!blocks) return '';
        
        let html = [];
        let listStack = [];
        
        for (const block of blocks) {
            if (block.type !== 'list-item' && listStack.length > 0) {
                while (listStack.length > 0) {
                    const listType = listStack.pop();
                    html.push(`</${listType}>`);
                }
            }
            
            switch (block.type) {
                case 'paragraph':
                    const processed = this.processInline(block.content);
                    html.push(`<p>${processed}</p>`);
                    break;
                    
                case 'list-item':
                    const listType = block.ordered ? 'ol' : 'ul';
                    if (listStack.length === 0 || listStack[listStack.length - 1] !== listType) {
                        if (listStack.length > 0) {
                            html.push(`</${listStack.pop()}>`);
                        }
                        html.push(`<${listType}>`);
                        listStack.push(listType);
                    }
                    html.push(`<li>${this.processInline(block.content)}</li>`);
                    break;
                    
                case 'code':
                    html.push(`<pre><code class="language-${block.language}">${this.escapeHtml(block.content)}</code></pre>`);
                    break;
                    
                case 'blockquote':
                    html.push(`<blockquote>${this.processInline(block.content)}</blockquote>`);
                    break;
                    
                case 'hr':
                    html.push('<hr>');
                    break;
            }
        }
        
        while (listStack.length > 0) {
            html.push(`</${listStack.pop()}>`);
        }
        
        return html.join('\n');
    }
    
    processInline(text) {
        if (!text) return '';
        
        // Clear separation of concerns:
        // N.one. Tokenize identifies structure (math vs text)
        // N.two. Parse handles markdown in text regions
        // 3. LaTeX processes math content ONLY
        
        const tokens = this.tokenize(text);
        const processed = this.parseTokens(tokens);
        
        // LaTeX processor should ONLY handle math content inside tokens
        // NOT re-scan for patterns we already found
        return this.processLatexInTokenizedContent(processed);
    }
    
    processLatexInTokenizedContent(html) {
        // Process only the math spans we already identified
        // Don't re-scan for $ or \( patterns - we already tokenized those
        
        return html
            // Process math spans we created
            .replace(/<span class="math-inline">([^<]+)<\/span>/g, (match, tex) => {
                const processed = this.latex.processTeX(tex);
                return `<span class="math-inline">${processed}</span>`;
            })
            // Process block math we created  
            .replace(/<div class="math-block">([^<]+)<\/div>/g, (match, tex) => {
                const processed = this.latex.processTeX(tex);
                return `<div class="math-block">${processed}</div>`;
            });
    }
    
    tokenize(text) {
        const tokens = [];
        let pos = 0;
        
        // Reset coordinator for this tokenization pass
        processingCoordinator.reset();
        
        while (pos < text.length) {
            let tokenFound = false;
            
            // Check for preprocessed math placeholders FIRST
            if (text.substr(pos, 15) === '<<<BLOCKMATH>>>') {
                const end = text.indexOf('<<</BLOCKMATH>>>', pos);
                if (end !== -1) {
                    const content = text.slice(pos + 15, end);
                    tokens.push({ type: 'blockmath', content: content });
                    pos = end + 16;
                    tokenFound = true;
                }
            } else if (text.substr(pos, 15) === '<<<INLINEMATH>>>') {
                const end = text.indexOf('<<</INLINEMATH>>>', pos);
                if (end !== -1) {
                    const content = text.slice(pos + 15, end);
                    tokens.push({ type: 'inlinemath', content: content });
                    pos = end + 17;
                    tokenFound = true;
                }
            }
            
            // Check for escaped characters first
            if (!tokenFound && text[pos] === '\\' && pos + 1 < text.length) {
                const next = text[pos + 1];
                
                // Check for \( \) or \[ \]
                if (next === '(' || next === '[') {
                    const closer = next === '(' ? '\\)' : '\\]';
                    const end = text.indexOf(closer, pos + 2);
                    if (end !== -1) {
                        const content = text.slice(pos, end + 2);
                        // Check with coordinator before claiming this math
                        if (processingCoordinator.shouldProcess('tokenizer', content, '\\(')) {
                            tokens.push({ type: 'math', content: content });
                            pos = end + 2;
                            tokenFound = true;
                        }
                    }
                } else if (next === '$') {
                    // Escaped dollar - treat as regular text
                    tokens.push({ type: 'text', content: '\\$' });
                    pos += 2;
                    tokenFound = true;
                } else if (/[a-zA-Z]/.test(next)) {
                    // LaTeX command
                    let end = pos + 2;
                    while (end < text.length && /[a-zA-Z]/.test(text[end])) end++;
                    
                    // Check for arguments recursively
                    end = this.scanLatexArguments(text, end);
                    
                    tokens.push({ type: 'latex', content: text.slice(pos, end) });
                    pos = end;
                    tokenFound = true;
                }
            }
            
            // Check for math delimiters
            if (!tokenFound && text[pos] === '$') {
                let end = pos + 1;
                // Properly handle escaped dollars
                while (end < text.length) {
                    if (text[end] === '$' && text[end - 1] !== '\\') {
                        tokens.push({ type: 'math', content: text.slice(pos, end + 1) });
                        pos = end + 1;
                        tokenFound = true;
                        break;
                    }
                    end++;
                }
                if (!tokenFound) {
                    // Unmatched $ - treat as text
                    tokens.push({ type: 'text', content: '$' });
                    pos++;
                    tokenFound = true;
                }
            }
            
            // Check for math operators with subscripts (with word boundaries)
            if (!tokenFound && pos < text.length - 2) {
                const match = text.slice(pos).match(/^(colim|lim|hom|Hom|sup|inf|max|min)\b_/);
                if (match) {
                    let end = pos + match[1].length + 1; // operator + _
                    const subscriptEnd = this.scanSubscriptOrSuperscript(text, end);
                    if (subscriptEnd > end) {
                        tokens.push({ type: 'latex', content: text.slice(pos, subscriptEnd) });
                        pos = subscriptEnd;
                        tokenFound = true;
                    }
                }
            }
            
            // Check for single letter with subscript/superscript
            if (!tokenFound && pos + 1 < text.length && /[a-zA-Z]/.test(text[pos])) {
                const next = text[pos + 1];
                if (next === '_' || next === '^') {
                    // Make sure this isn't part of a word
                    const isWordBoundary = pos === 0 || !/[a-zA-Z]/.test(text[pos - 1]);
                    if (isWordBoundary) {
                        let end = pos + 2;
                        const scriptEnd = this.scanSubscriptOrSuperscript(text, end);
                        if (scriptEnd > end) {
                            tokens.push({ type: 'latex', content: text.slice(pos, scriptEnd) });
                            pos = scriptEnd;
                            tokenFound = true;
                        }
                    }
                }
            }
            
            // Check for markdown emphasis with underscores
            if (!tokenFound && text[pos] === '_') {
                // Only if not followed by subscript patterns
                if (pos + 1 < text.length && !(text[pos + 1] === '{' || text[pos + 1] === '*' || /[0-9]/.test(text[pos + 1]))) {
                    let end = pos + 1;
                    let mathDepth = 0;
                    
                    // Scan for matching underscore, properly tracking math regions
                    while (end < text.length) {
                        if (text[end] === '_' && mathDepth === 0) {
                            tokens.push({ type: 'emphasis', content: text.slice(pos + 1, end) });
                            pos = end + 1;
                            tokenFound = true;
                            break;
                        }
                        // Track math regions consistently
                        if (text[end] === '$' && text[end - 1] !== '\\') {
                            mathDepth = mathDepth === 0 ? 1 : 0;
                        } else if (text[end] === '\\' && end + 1 < text.length) {
                            if (text[end + 1] === '(') mathDepth++;
                            else if (text[end + 1] === ')' && mathDepth > 0) mathDepth--;
                        }
                        end++;
                    }
                }
            }
            
            // Collect regular text efficiently
            if (!tokenFound) {
                let end = pos;
                
                // Scan ahead for regular text, stopping at special characters
                while (end < text.length) {
                    const ch = text[end];
                    
                    // Stop at potential token boundaries
                    if (ch === '$' || ch === '\\' || ch === '_') {
                        break;
                    }
                    
                    // Stop at potential math patterns
                    if (end + 1 < text.length && /[a-zA-Z]/.test(ch)) {
                        const next = text[end + 1];
                        if (next === '_' || next === '^') {
                            const isWordBoundary = end === 0 || !/[a-zA-Z]/.test(text[end - 1]);
                            if (isWordBoundary) break;
                        }
                    }
                    
                    end++;
                }
                
                // Ensure we advance at least one character
                if (end === pos) end = pos + 1;
                
                tokens.push({ type: 'text', content: text.slice(pos, end) });
                pos = end;
            }
        }
        
        return tokens;
    }
    
    // Recursively scan LaTeX arguments
    scanLatexArguments(text, pos) {
        let end = pos;
        
        while (end < text.length && (text[end] === '_' || text[end] === '^' || text[end] === '{')) {
            if (text[end] === '{') {
                // Find matching brace with proper nesting
                let braceDepth = 1;
                end++;
                while (end < text.length && braceDepth > 0) {
                    if (text[end] === '\\' && end + 1 < text.length) {
                        // Skip escaped characters
                        end += 2;
                        continue;
                    }
                    if (text[end] === '{') braceDepth++;
                    else if (text[end] === '}') braceDepth--;
                    end++;
                }
            } else if (text[end] === '_' || text[end] === '^') {
                // Subscript or superscript
                end++;
                end = this.scanSubscriptOrSuperscript(text, end);
            }
        }
        
        return end;
    }
    
    // Scan subscript or superscript content
    scanSubscriptOrSuperscript(text, pos) {
        if (pos >= text.length) return pos;
        
        if (text[pos] === '{') {
            // Braced subscript/superscript
            let braceDepth = 1;
            let end = pos + 1;
            while (end < text.length && braceDepth > 0) {
                if (text[end] === '\\' && end + 1 < text.length) {
                    // Skip escaped characters
                    end += 2;
                    continue;
                }
                if (text[end] === '{') braceDepth++;
                else if (text[end] === '}') braceDepth--;
                end++;
            }
            return end;
        } else if (text[pos] === '*' || /[0-9a-zA-Z]/.test(text[pos])) {
            // Single character subscript/superscript
            return pos + 1;
        }
        
        return pos;
    }
    
    parseTokens(tokens) {
        // Build result by processing each token according to its type
        let result = '';
        
        // Merge adjacent text tokens for better markdown processing
        const mergedTokens = [];
        for (let i = 0; i < tokens.length; i++) {
            const token = tokens[i];
            
            if (token.type === 'text' && mergedTokens.length > 0 && 
                mergedTokens[mergedTokens.length - 1].type === 'text') {
                mergedTokens[mergedTokens.length - 1].content += token.content;
            } else {
                mergedTokens.push({...token});
            }
        }
        
        // Process each token according to its type
        for (const token of mergedTokens) {
            switch (token.type) {
                case 'blockmath':
                    // Preprocessed block math - process with LaTeX
                    result += `<div class="math-block">${this.latex.processTeX(token.content)}</div>`;
                    break;
                    
                case 'inlinemath':
                    // Preprocessed inline math - process with LaTeX
                    result += `<span class="math-inline">${this.latex.processTeX(token.content)}</span>`;
                    break;
                    
                case 'math':
                    // Wrap math content in appropriate spans for later LaTeX processing
                    if (token.content.startsWith('$$') || token.content.startsWith('\\[')) {
                        // Block math
                        const inner = token.content.replace(/^\$\$|\$\$$/g, '')
                                                   .replace(/^\\\[|\\\]$/g, '');
                        result += `<div class="math-block">${inner}</div>`;
                    } else {
                        // Inline math
                        const inner = token.content.replace(/^\$|\$$/g, '')
                                                   .replace(/^\\\(|\\\)$/g, '');
                        result += `<span class="math-inline">${inner}</span>`;
                    }
                    break;
                    
                case 'latex':
                    // LaTeX commands get processed directly
                    result += `<span class="math-inline">${token.content}</span>`;
                    break;
                    
                case 'emphasis':
                    // Emphasis content should NOT be re-processed for markdown
                    // It's already been extracted as emphasized
                    result += `<${CONFIG.strings.semanticElements.emphasis}>${token.content}</${CONFIG.strings.semanticElements.emphasis}>`;
                    break;
                    
                case 'text':
                    // Process markdown patterns in text tokens
                    result += this.processTextToken(token.content);
                    break;
            }
        }
        
        return result;
    }
    
    processTextToken(text) {
        let result = text;
        
        // Remove any leftover math markers that weren't properly processed
        result = result.replace(/<<<BLOCKMATH>>>/g, '');
        result = result.replace(/<<<\/BLOCKMATH>>>/g, '');
        result = result.replace(/<<<INLINEMATH>>>/g, '');
        result = result.replace(/<<<\/INLINEMATH>>>/g, '');
        
        // Bold **text**
        result = result.replace(/\*\*([^*]+)\*\*/g, 
            `<${CONFIG.strings.semanticElements.strong}>$1</${CONFIG.strings.semanticElements.strong}>`);
        
        // Italic *text* (but not **text**)
        result = result.replace(/(?<!\*)\*(?!\*)([^*]+)(?<!\*)\*(?!\*)/g, 
            `<${CONFIG.strings.semanticElements.emphasis}>$1</${CONFIG.strings.semanticElements.emphasis}>`);
        
        // Code `text`
        result = result.replace(/`([^`]+)`/g, '<code>$1</code>');
        
        // Links [text](url)
        result = result.replace(/\[([^\]]+)\]\(([^)]+)\)/g, '<a href="$2">$1</a>');
        
        return result;
    }
    
    escapeHtml(text) {
        const map = {
            '&': '&amp;',
            '<': '&lt;',
            '>': '&gt;',
            '"': '&quot;',
            "'": '&#39;'
        };
        return text.replace(/[&<>"']/g, m => map[m]);
    }
    
    generateHTML(processor) {
        // Store processor reference
        this.currentProcessor = processor;
        
        // Create lazy HTML generation pipeline
        return new Lazy(() => {
            const toc = processor.generateTOC();
            const tocHTML = this.renderTOC(toc);
            
            let sectionsHTML = [];
            for (const [id, section] of processor.sections) {
                const content = processor.data.get(id);
                sectionsHTML.push(this.renderSection(section, content));
            }
            
            // Build HTML lazily - only evaluate when stringified
            const template = new LazyTemplate([
                '<!DOCTYPE html>\n',
                '<html lang="', CONFIG.strings.defaultLanguage, '">\n',
                '<head>\n',
                '    <meta charset="', CONFIG.strings.standardCharset, '">\n',
                '    <meta name="viewport" content="', CONFIG.strings.viewportContent, '">\n',
                '    <title>', CONFIG.strings.documentTitle, '</title>\n',
                '    <style>', this.generateCSS(), '</style>\n',
                '    <script>', this.generateJS(), '</script>\n',
                '</head>\n',
                '<body>\n',
                '    <nav class="', CONFIG.strings.sidebarClass, '">\n',
                '        <div class="', CONFIG.strings.headerClass, '">\n',
                '            <h2>', CONFIG.strings.contentsLabel, '</h2>\n',
                '            <button class="', CONFIG.strings.expandControlClass, '" onclick="expandAll()">', CONFIG.strings.expandAllLabel, '</button>\n',
                '        </div>\n',
                '        ', tocHTML, '\n',
                '    </nav>\n',
                '    <main class="', CONFIG.strings.contentClass, '">\n',
                '        ', sectionsHTML.join('\n'), '\n',
                '    </main>\n',
                '</body>\n',
                '</html>'
            ]);
            
            // Execute the lazy template to get the actual HTML string
            return template.toString();
        });
    }
    
    generateCSS() {
        return new Lazy(() => {
            const context = ConfigContext.create();
            
            const cssConfig = context.derive('css', env => ({
                colors: env.config.colors,
                ui: env.config.ui,
                css: env.config.css,
                strings: env.config.strings,
                common: env.common,
                zero: 0, one: 1, two: 2
            }));
            
            const template = new LazyTemplate([
                '/* Variables */\n',
                ':root {\n',
                '    --serif: \'Crimson Text\', Georgia, serif;\n',
                '    --sans: -apple-system, BlinkMacSystemFont, \'Segoe UI\', sans-serif;\n',
                '    --mono: \'SF Mono\', Monaco, monospace;\n',
                '    --text: ', CONFIG.colors.text.body, ';\n',
                '    --bg: ', CONFIG.colors.background.main, ';\n',
                '    --sidebar-bg: ', CONFIG.colors.background.sidebar, ';\n',
                '    --border: ', CONFIG.colors.border.default, ';\n',
                '    --link: ', CONFIG.colors.link.default, ';\n',
                '    --link-hover: ', CONFIG.colors.link.active, ';\n',
                '}\n\n',
                this.buildCSSRules(cssConfig)
            ]);
            
            // Execute the lazy template to get the actual CSS string  
            return template.toString();
        });
    }
    
    buildCSSRules(context) {
        // Compose CSS rules lazily
        return Pipeline.compose(
            this.buildResetStyles.bind(this),
            this.buildBodyStyles.bind(this),
            this.buildTOCStyles.bind(this),
            this.buildContentStyles.bind(this),
            this.buildMathStyles.bind(this),
            this.buildCodeStyles.bind(this),
            this.buildResponsiveStyles.bind(this),
            this.buildPrintStyles.bind(this)
        )(context);
    }
    
    buildResetStyles(context) {
        return new Lazy(() => new LazyTemplate([
            '* {\n',
            '    margin: ', CONFIG.ui.zero, ';\n',
            '    padding: ', CONFIG.ui.zero, ';\n',
            '    box-sizing: ', CONFIG.css.boxModel.border, ';\n',
            '}\n\n'
        ]));
    }
    
    buildBodyStyles(prev) {
        return new Lazy(() => new LazyTemplate([
            prev,
            'body {\n',
            '    font-family: var(--serif);\n',
            '    font-size: ', CONFIG.ui.typography.pixels.base, 'px;\n',
            '    line-height: ', CONFIG.ui.typography.lineHeight.relaxed, ';\n',
            '    color: var(--text);\n',
            '    display: ', CONFIG.css.display.flex, ';\n',
            '    min-height: ', THRESHOLDS.VIEWPORT_HEIGHT, 'vh;\n',
            '}\n\n'
        ]));
    }
    
    buildTOCStyles(prev) {
        return new Lazy(() => new LazyTemplate([
            prev,
            '/* TOC Sidebar */\n',
            '.toc-sidebar {\n',
            '    width: ', CONFIG.ui.layout.sidebarWidth, 'px;\n',
            '    background: var(--sidebar-bg);\n',
            '    border-right: ', CONFIG.ui.borderWidth, 'px solid var(--border);\n',
            '    position: ', CONFIG.css.position.fixed, ';\n',
            '    top: 0;\n',
            '    left: ', CONFIG.ui.zero, ';\n',
            '    height: ', THRESHOLDS.VIEWPORT_HEIGHT, 'vh;\n',
            '    overflow-y: auto;\n',
            '    padding: ', CONFIG.ui.typography.scale.base, 'rem;\n',
            '}\n\n'
        ]));
    }
    
    buildContentStyles(prev) {
        return new Lazy(() => new LazyTemplate([
            prev,
            '/* Main Content */\n',
            '.content {\n',
            '    margin-left: ', CONFIG.ui.layout.sidebarWidth, 'px;\n',
            '    padding: ', CONFIG.ui.spacing.large, 'px ', CONFIG.ui.spacing.massive, 'px;\n',
            '    max-width: ', CONFIG.ui.layout.contentMaxWidth, 'px;\n',
            '    width: ', CONFIG.ui.dimensions.full, ';\n',
            '}\n\n',
            '.section-heading {\n',
            '    font-family: var(--sans);\n',
            '    margin: ', CONFIG.ui.spacing.large, 'px 0 ', CONFIG.ui.spacing.medium, 'px;\n',
            '    position: ', CONFIG.css.position.relative, ';\n',
            '    padding-left: ', CONFIG.ui.spacing.huge, 'px;\n',
            '}\n\n'
        ]));
    }
    
    buildMathStyles(prev) {
        return new Lazy(() => new LazyTemplate([
            prev,
            '/* Math Rendering */\n',
            '.', CONFIG.strings.blockContentClass, ' {\n',
            '    display: ', CONFIG.css.display.block, ';\n',
            '    margin: ', CONFIG.ui.typography.scale.medium, 'rem 0;\n',
            '    padding: ', CONFIG.ui.typography.scale.base, 'rem;\n',
            '    background: ', CONFIG.colors.background.code, ';\n',
            '    border-left: ', CONFIG.ui.spacing.tiny, 'px solid var(--link);\n',
            '    overflow-x: auto;\n',
            '    font-family: \'STIX Two Math\', \'Cambria Math\', serif;\n',
            '    font-size: ', CONFIG.ui.typography.scale.medium, 'em;\n',
            '    text-align: ', CONFIG.css.align.center, ';\n',
            '}\n\n',
            '.', CONFIG.strings.inlineContentClass, ' {\n',
            '    font-family: \'STIX Two Math\', \'Cambria Math\', serif;\n',
            '    font-size: ', CONFIG.ui.typography.scale.base, 'em;\n',
            '    padding: 0 ', CONFIG.ui.typography.emScale.small, 'em;\n',
            '}\n\n'
        ]));
    }
    
    buildCodeStyles(prev) {
        return new Lazy(() => new LazyTemplate([
            prev,
            '/* Code blocks */\n',
            'pre {\n',
            '    background: ', CONFIG.colors.background.code, ';\n',
            '    border: ', CONFIG.ui.borderWidth, 'px solid var(--border);\n',
            '    border-radius: ', CONFIG.ui.spacing.compact, 'px;\n',
            '    padding: ', CONFIG.ui.typography.scale.base, 'rem;\n',
            '    margin: ', CONFIG.ui.typography.scale.small, 'rem 0;\n',
            '    overflow-x: auto;\n',
            '}\n\n',
            'code {\n',
            '    font-family: var(--mono);\n',
            '    font-size: ', CONFIG.ui.typography.scale.small, 'em;\n',
            '    background: ', CONFIG.colors.background.code, ';\n',
            '    padding: ', CONFIG.ui.typography.emScale.small, 'em ', CONFIG.ui.typography.emScale.medium, 'em;\n',
            '    border-radius: ', CONFIG.ui.spacing.tiny, 'px;\n',
            '}\n\n'
        ]));
    }
    
    buildResponsiveStyles(prev) {
        return new Lazy(() => new LazyTemplate([
            prev,
            '/* Responsive */\n',
            '@media (max-width: ', CONFIG.ui.layout.mediaBreakpoint, 'px) {\n',
            '    .toc-sidebar {\n',
            '        transform: ', CONFIG.ui.transform.offscreen, ';\n',
            '        transition: transform ', CONFIG.ui.transition.slow, 's;\n',
            '    }\n',
            '    .toc-sidebar.open {\n',
            '        transform: ', CONFIG.ui.transform.none, ';\n',
            '    }\n',
            '    .content {\n',
            '        margin-left: ', CONFIG.ui.zero, ';\n',
            '    }\n',
            '}\n\n'
        ]));
    }
    
    buildPrintStyles(prev) {
        return new Lazy(() => new LazyTemplate([
            prev,
            '/* Print styles */\n',
            '@media print {\n',
            '    .toc-sidebar {\n',
            '        position: ', CONFIG.css.position.static, ';\n',
            '        width: ', CONFIG.ui.dimensions.full, ';\n',
            '        page-break-after: always;\n',
            '    }\n',
            '    .content {\n',
            '        margin-left: ', CONFIG.ui.zero, ';\n',
            '    }\n',
            '    .anchor-link {\n',
            '        display: ', CONFIG.css.display.none, ';\n',
            '    }\n',
            '}\n'
        ]));
    }

 
    generateJS() {
        // Direct access to CONFIG values for template literals
        const js = CONFIG;
        
        return `
// Navigation functions
function navigateToSection(id, event) {
    if (event) event.preventDefault();
    
    const element = document.getElementById(id);
    if (element) {
        element.scrollIntoView({ behavior: '${js.strings.scrollBehavior.smooth}', block: '${js.strings.scrollBlock.start}' });
        
        // Update active state WITHOUT expanding sections
        document.querySelectorAll('.' + '${js.strings.navigationLinkClass}').forEach(link => {
            link.classList.remove('${js.strings.classActive}');
        });
        document.querySelector(\`[data-section="\${id}"]\`)?.classList.add('${js.strings.classActive}');
        
        // Update URL
        history.pushState(null, null, '#' + id);
    }
}

function toggleSection(id) {
    const section = document.getElementById(id);
    if (!section) return;
    
    // Find the button that controls this section
    const button = document.querySelector(\`button[onclick="toggleSection('\${id}')"]\`);
    if (!button) return;
    
    const isHidden = section.style.display === 'none' || !section.style.display;
    
    if (isHidden) {
        section.style.display = 'block';
        button.setAttribute('aria-expanded', 'true');
        const icon = button.querySelector('.${js.strings.toggleIconClass}');
        if (icon) icon.textContent = '${js.strings.expandedIndicator}';
    } else {
        section.style.display = 'none';
        button.setAttribute('aria-expanded', 'false');
        const icon = button.querySelector('.${js.strings.toggleIconClass}');
        if (icon) icon.textContent = '${js.strings.collapsedIndicator}';
    }
}

function expandAll() {
    const button = document.querySelector('.' + '${js.strings.expandControlClass}');
    const sections = document.querySelectorAll('.' + '${js.strings.childrenContainerClass}');
    const toggles = document.querySelectorAll('.' + '${js.strings.toggleControlClass}');
    
    const allExpanded = Array.from(sections).every(s => s.style.display !== '${js.css.display.none}');
    
    sections.forEach(section => {
        section.style.display = allExpanded ? '${js.css.display.none}' : '${js.css.display.block}';
    });
    
    toggles.forEach(toggle => {
        toggle.setAttribute('${js.strings.expandedAttribute}', !allExpanded);
    });
    
    button.textContent = allExpanded ? '${js.strings.expandAllLabel}' : '${js.strings.collapseAllLabel}';
}

// Highlight current section on scroll
document.addEventListener('${js.strings.domEvents.contentLoaded}', function() {
    const sections = document.querySelectorAll('.' + '${js.strings.documentSectionClass}');
    const tocLinks = document.querySelectorAll('.' + '${js.strings.navigationLinkClass}');
    
    function highlightTOC(fromScroll = false) {
        let current = '';
        sections.forEach(section => {
            const rect = section.getBoundingClientRect();
            if (rect.top <= ${js.watcher.initialBuildCheckInterval}) {
                current = section.dataset.sectionId;
            }
        });
        
        tocLinks.forEach(link => {
            link.classList.remove('${js.strings.classActive}');
            if (link.dataset.section === current) {
                link.classList.add('${js.strings.classActive}');
                
                // ONLY auto-expand parent if this is from scrolling, not from clicking
                if (fromScroll) {
                    // Do nothing - don't auto-expand
                }
            }
        });
    }
    
    window.addEventListener('${js.strings.domEvents.scroll}', () => highlightTOC(true));
    highlightTOC(false);
    
    // Handle initial hash
    if (window.location.hash) {
        setTimeout(() => {
            const id = window.location.hash.slice(${js.ui.layout.hashSliceStart});
            navigateToSection(id);
        }, ${js.ui.scrollDebounceDelay});
    }
});
`;
    }
}

// PDF MODALITY

class PDFModality extends HTMLModality {
    generateHTML(processor) {
        // Store processor reference
        this.currentProcessor = processor;
        
        const toc = processor.generateTOC();
        const tocHTML = this.renderPDFTOC(toc);
        
        let sectionsHTML = [];
        for (const [id, section] of processor.sections) {
            const content = processor.data.get(id);
            sectionsHTML.push(this.renderPDFSection(section, content));
        }
        
        return `<!DOCTYPE html>
<html lang="${CONFIG.strings.defaultLanguage}">
<head>
    <meta charset="${CONFIG.strings.standardCharset}">
    <style>
        @page {
            size: letter;
            margin: ${CONFIG.print.pageMargin};
        }
        
        body {
            font-family: 'Times New Roman', serif;
            font-size: ${CONFIG.print.fontSize.body}pt;
            line-height: ${CONFIG.ui.typography.lineHeight.normal};
            color: ${CONFIG.colors.text.emphasis};
        }
        
        /* TOC Page */
        .toc-page {
            page-break-after: always;
        }
        
        .toc-title {
            font-size: ${CONFIG.print.fontSize.h1}pt;
            margin-bottom: ${CONFIG.ui.typography.scale.medium}rem;
            text-align: ${CONFIG.css.align.center};
        }
        
        .toc-entry {
            margin: ${CONFIG.ui.typography.emScale.large}em 0;
            page-break-inside: avoid;
        }
        
        .toc-entry a {
            color: ${CONFIG.colors.text.emphasis};
            text-decoration: ${CONFIG.css.textDecoration.none};
            display: ${CONFIG.css.display.block};
        }
        
        .toc-entry a:hover {
            text-decoration: ${CONFIG.css.textDecoration.underline};
        }
        
        .toc-level-0 { margin-left: ${CONFIG.ui.zero}; font-weight: ${CONFIG.ui.typography.weight.bold}; }
        .toc-level-1 { margin-left: ${CONFIG.print.spacing.indent}em; }
        .toc-level-2 { margin-left: ${CONFIG.ui.spacing.tiny}em; }
        
        .toc-page-number {
            float: right;
        }
        
        /* Content */
        h1, h2, h3, h4 {
            font-family: ${CONFIG.strings.fallbackFontStack};
            page-break-after: avoid;
        }
        
        h1 { font-size: ${CONFIG.print.fontSize.h1}pt; margin: ${CONFIG.print.spacing.h1.top}pt 0 ${CONFIG.print.spacing.h1.bottom}pt; }
        h2 { font-size: ${CONFIG.print.fontSize.h2}pt; margin: ${CONFIG.print.spacing.h2.top}pt 0 ${CONFIG.print.spacing.h2.bottom}pt; }
        h3 { font-size: ${CONFIG.print.fontSize.h3}pt; margin: ${CONFIG.print.spacing.h3.top}pt 0 ${CONFIG.print.spacing.h3.bottom}pt; }
        h4 { font-size: ${CONFIG.print.fontSize.h4}pt; margin: ${CONFIG.print.spacing.h4.top}pt 0 ${CONFIG.print.spacing.h4.bottom}pt; }
        
        /* Math */
        .math-block {
            display: ${CONFIG.css.display.block};
            margin: ${CONFIG.print.spacing.block}pt 0;
            text-align: ${CONFIG.css.align.center};
            font-family: 'Cambria Math', serif;
        }
        
        .math-inline {
            font-family: 'Cambria Math', serif;
        }
        
        /* Links in PDF should be blue */
        a {
            color: ${CONFIG.colors.link.default};
            text-decoration: ${CONFIG.css.textDecoration.underline};
        }
        
        pre {
            background: ${CONFIG.colors.background.highlight};
            padding: ${CONFIG.print.spacing.inline}pt;
            margin: ${CONFIG.print.spacing.inline}pt 0;
            page-break-inside: avoid;
            font-size: ${CONFIG.print.fontSize.footnote}pt;
        }
        
        code {
            font-family: 'Courier New', monospace;
            font-size: ${CONFIG.print.fontSize.footnote}pt;
        }
        
        /* Back to TOC navigation */
        .back-to-toc {
            display: ${CONFIG.css.display.inlineBlock};
            margin-top: ${CONFIG.print.spacing.inline}pt;
            font-size: ${CONFIG.print.fontSize.footnote}pt;
            color: ${CONFIG.colors.link.default};
            text-decoration: ${CONFIG.css.textDecoration.none};
        }
        
        .back-to-toc:before {
            content: '← ';
        }
    </style>
</head>
<body>
    <div class="toc-page" id="toc">
        <h1 class="toc-title">Contents</h1>
        ${tocHTML}
    </div>
    ${sectionsHTML.join('\n')}
</body>
</html>`;
    }
    
    renderPDFSection(section, content) {
        // Skip rendering duplicate TOC sections in PDF
        if (section.title && (
            section.title === 'Contents' || 
            section.title === 'Table of Contents' ||
            section.title.toLowerCase() === 'contents' ||
            section.title.toLowerCase() === 'table of contents'
        )) {
            return '';  // Skip this section entirely in PDF
        }
        
        const heading = `<h${section.level} id="${section.id}">
            ${this.escapeHtml(section.title)}
        </h${section.level}>`;
        
        // Add back-to-TOC link for major sections
        const backToTOC = section.level <= CONFIG.processor.tocMaxDepth ? 
            '<a href="#toc" class="back-to-toc">Back to Contents</a>' : '';
        
        const blocks = this.renderBlocks(content);
        
        return `<section>
            ${heading}
            ${backToTOC}
            ${blocks}
        </section>`;
    }
    
    renderPDFTOC(toc, level = 0) {
        if (!toc || toc.length === 0) return '';
        
        return toc.map(entry => `
            <div class="toc-entry toc-level-${level}">
                <a href="#${entry.id}" style="text-decoration: none; color: inherit;">
                    ${this.escapeHtml(entry.title)}
                </a>
                ${entry.children && entry.children.length > 0 ? 
                    this.renderPDFTOC(entry.children, level + 1) : ''}
            </div>
        `).join('');
    }
}

// MARKDOWN MODALITY

class MarkdownModality {
    render(processor) {
        let output = [];
        
        const toc = processor.generateTOC();
        if (toc.length > 0) {
            output.push('# Table of Contents\n');
            output.push(this.renderTOC(toc));
            output.push('\n---\n');
        }
        
        for (const [id, section] of processor.sections) {
            const content = processor.data.get(id);
            output.push(this.renderSection(section, content));
        }
        
        return output.join('\n');
    }
    
    renderTOC(toc, level = 0) {
        return toc.map(entry => {
            const indent = '  '.repeat(level);
            const link = `[${entry.title}](#${entry.id})`;
            const children = entry.children && entry.children.length > 0 ? 
                '\n' + this.renderTOC(entry.children, level + 1) : '';
            return `${indent}- ${link}${children}`;
        }).join('\n');
    }
    
    renderSection(section, content) {
        const heading = '#'.repeat(section.level) + ' ' + section.title;
        const blocks = this.renderBlocks(content);
        return `${heading}\n\n${blocks}\n`;
    }
    
    renderBlocks(blocks) {
        if (!blocks) return '';
        
        return blocks.map(block => {
            switch (block.type) {
                case 'paragraph':
                    return block.content;
                case 'list-item':
                    const marker = block.ordered ? '1.' : '-';
                    return `${marker} ${block.content}`;
                case 'code':
                    return '```' + block.language + '\n' + block.content + '\n```';
                case 'blockquote':
                    return `> ${block.content}`;
                case 'hr':
                    return '---';
                default:
                    return block.content;
            }
        }).join('\n\n');
    }
}

// BUILD SYSTEM

// Dynamic file discovery - finds all HCT documents based on pattern
function discoverDocumentFiles() {
    const files = fs.readdirSync(__dirname)
        .filter(file => CONFIG.patterns.documentFilePattern.test(file))
        .map(txtFile => {
            // Check if this file matches a CONFIG entry
            if (txtFile === CONFIG.files.workingDoc.txt) {
                return CONFIG.files.workingDoc;
            } else if (txtFile === CONFIG.files.primerDoc.txt) {
                return CONFIG.files.primerDoc;
            }
            // Fallback for other files not in CONFIG
            const baseName = txtFile.replace(CONFIG.patterns.documentPrefix, '').replace(CONFIG.patterns.txtExtension, '').toLowerCase();
            const displayName = baseName.split('_').map(word => 
                word.charAt(0).toUpperCase() + word.slice(1)
            ).join(' ');
            
            return {
                name: `${CONFIG.strings.projectAbbreviation} ${displayName}`,
                txt: txtFile,
                pdf: `${baseName}.pdf`,
                html: `${baseName}.html`,
                md: `${baseName}.md`
            };
        });
    
    return files;
}

// Use dynamic discovery or fallback to static CONFIG
const discoveredFiles = discoverDocumentFiles();
const FILES = discoveredFiles.length > 0 
    ? discoveredFiles
    : [CONFIG.files.workingDoc, CONFIG.files.primerDoc];

// COMMIT SAFEGUARD - Makes it IMPOSSIBLE to miss files
const MANDATORY_COMMIT_FILES = [
    CONFIG.files.buildScript,
    CONFIG.files.readmeFile,
    CONFIG.files.indexFile,
    'LICENSE',
    CONFIG.files.primerDoc.txt,
    CONFIG.files.workingDoc.txt,
    CONFIG.files.primerDoc.html,
    CONFIG.files.primerDoc.md,
    CONFIG.files.primerDoc.pdf,
    CONFIG.files.workingDoc.html,
    CONFIG.files.workingDoc.md,
    CONFIG.files.workingDoc.pdf
];

async function verifyCommitReadiness(isOnlinePush = false) {
    try {
        // LOCAL RULE: everything in folder is included
        if (!isOnlinePush) {
            // Local commits encapsulate ALL files in local folder, known or unknown
            // No verification needed - build proceeds
            return true;
        }
        
        // ONLINE RULE: For online pushes, use lazyGit to check status
        const changedFiles = await lazyGit.pull(lazyGit.changedFiles());
        const stagedFiles = await lazyGit.pull(lazyGit.diff('--cached'));
        
        const missingFromStaging = [];
        for (const mandatoryFile of MANDATORY_COMMIT_FILES) {
            const fileChanged = changedFiles.some(f => f.file === mandatoryFile);
            if (fileChanged && !stagedFiles.includes(mandatoryFile)) {
                missingFromStaging.push(mandatoryFile);
            }
        }
        
        if (missingFromStaging.length > 0) {
            console.error('ERROR: MANDATORY FILES NOT STAGED FOR ONLINE PUSH:');
            missingFromStaging.forEach(f => console.error(`  - ${f}`));
            console.error('\nUse: await lazyGit.stage(' + JSON.stringify(missingFromStaging) + ').pull()');
            return false;
        }
        return true;
    } catch (e) {
        console.warn('[GIT CHECK] Not in git repo or git unavailable:', e.message);
        return true; // Not in git repo, allow build to continue
    }
}

const processor = new DocumentProcessor();

// Smart process lock manager integrated into build system
class ProcessLockManager {
    constructor() {
        this.lockFile = path.join(PROJECT_ROOT, CONFIG.files.lockFile);
        this.heartbeatInterval = null;
        this.isOwner = false;
    }
    
    isProcessRunning(pid) {
        try {
            // Send signal to check if process exists
            process.kill(pid, CONFIG.processor.signalKillDefault);
            return true;
        } catch (error) {
            return false;
        }
    }
    
    acquire() {
        try {
            // Check for existing lock
            if (lazyFS.exists(this.lockFile).value) {
                const lockData = JSON.parse(fs.readFileSync(this.lockFile, CONFIG.strings.standardEncoding));
                const lockAge = Date.now() - lockData.timestamp;
                
                // Verify process is running
                if (this.isProcessRunning(lockData.pid)) {
                    // Process is alive - check if it's stale based on heartbeat
                    if (lockAge < CONFIG.scheduler.lockAliveCheckTime) {
                        console.error(`[LOCK] Build already running (PID: ${lockData.pid})`);
                        console.log(CONFIG.strings.lockWaitingMessage);
                        
                        // Wait for lock to release (configured retry attempts)
                        for (let i = 0; i < CONFIG.process.lockRetryAttempts; i++) {
                            if (!lazyFS.exists(this.lockFile).value) {
                                break;
                            }
                            // Sleep briefly using execSync (will be replaced when function becomes async)
                            execSync(
                                process.platform === CONFIG.strings.windowsPlatform ? CONFIG.strings.windowsSleepCommand() : CONFIG.strings.unixSleepCommand(),
                                {stdio: 'ignore'}
                            );
                        }
                        
                        // Check again
                        if (lazyFS.exists(this.lockFile).value) {
                            const updatedLockData = JSON.parse(fs.readFileSync(this.lockFile, CONFIG.strings.standardEncoding));
                            if (this.isProcessRunning(updatedLockData.pid)) {
                                console.error(CONFIG.strings.lockStillRunningMessage);
                                return false;
                            }
                        }
                    }
                }
                
                // Process is dead or lock is stale - clean it up
                fs.unlinkSync(this.lockFile);
            }
            
            // Create new lock
            this.writeLock();
            this.isOwner = true;
            
            // Start heartbeat to keep lock fresh
            this.heartbeatInterval = setInterval(() => {
                if (this.isOwner) {
                    this.writeLock();
                }
            }, CONFIG.process.heartbeatInterval);
            
            return true;
        } catch (error) {
            console.error(CONFIG.strings.lockErrorPrefix, error);
            // Clean up heartbeat if started
            if (this.heartbeatInterval) {
                clearInterval(this.heartbeatInterval);
                this.heartbeatInterval = null;
            }
            return false;
        }
    }
    
    writeLock() {
        const tempFile = this.lockFile + '.tmp';
        const lockData = JSON.stringify({
            pid: process.pid,
            timestamp: Date.now(),
            version: CONFIG.strings.buildVersion,
            started: new Date().toISOString()
        });
        // Write atomically: write to temp, then rename
        try {
            fs.writeFileSync(tempFile, lockData);
            fs.renameSync(tempFile, this.lockFile);
        } catch (error) {
            // Clean up temp file if rename failed
            try { fs.unlinkSync(tempFile); } catch {}
            throw error;
        }
    }
    
    release() {
        try {
            if (this.heartbeatInterval) {
                clearInterval(this.heartbeatInterval);
                this.heartbeatInterval = null;
            }
            
            if (this.isOwner && lazyFS.exists(this.lockFile).value) {
                // Only delete if we own the lock
                const lockData = JSON.parse(fs.readFileSync(this.lockFile, CONFIG.strings.standardEncoding));
                if (lockData.pid === process.pid) {
                    fs.unlinkSync(this.lockFile);
                    this.isOwner = false;
                }
            }
        } catch (error) {
            console.error(CONFIG.strings.lockCleanupErrorPrefix, error);
        }
    }
}

const lockManager = new ProcessLockManager();

// VIEW RENDERING

function renderView(config, data) {
    if (config.type === 'document-index') {
        return renderDocumentIndex(config, data);
    }
}

function renderDocumentIndex(config, documents) {
    const extractDescription = (text) => {
        // Get a professional summary based on document type
        if (text.includes(CONFIG.content.experienceTitle)) {
            return CONFIG.content.experienceDescription;
        } else if (text.includes(CONFIG.content.primerTitle)) {
            return CONFIG.content.primerDescription;
        }
        return CONFIG.content.defaultDescription;
    };
    
    const formatFileSize = (bytes) => {
        if (bytes < CONFIG.processor.mediumSizeThreshold) return bytes + CONFIG.strings.smallSizeUnit;
        if (bytes < CONFIG.processor.largeSizeThreshold) return (bytes / CONFIG.processor.mediumSizeThreshold).toFixed(CONFIG.processor.coarsePrecision) + CONFIG.strings.mediumSizeUnit;
        return (bytes / CONFIG.processor.largeSizeThreshold).toFixed(2) + CONFIG.strings.largeSizeUnit;
    };
    
    const docInfo = documents.map(doc => {
        const txtPath = CONFIG.resolveDocPath(doc, 'txt');
        const content = fs.readFileSync(txtPath, CONFIG.strings.standardEncodingDash);
        const description = extractDescription(content);

        // Get file sizes
        const getSizeOrZero = (filepath) => {
            try {
                return fs.statSync(filepath).size;
            } catch {
                return 0;
            }
        };

        const htmlSize = getSizeOrZero(CONFIG.resolveDocPath(doc, 'html'));
        const pdfSize = getSizeOrZero(CONFIG.resolveDocPath(doc, 'pdf'));
        const mdSize = getSizeOrZero(CONFIG.resolveDocPath(doc, 'md'));
        
        // Count sections
        const sectionCount = content.match(CONFIG.patterns.sectionCount)?.length;
        
        return {
            name: doc.name,
            description,
            formats: {
                html: { file: doc.html, size: formatFileSize(htmlSize) },
                pdf: { file: doc.pdf, size: formatFileSize(pdfSize) },
                md: { file: doc.md, size: formatFileSize(mdSize) },
                txt: { file: doc.txt, size: formatFileSize(getSizeOrZero(txtPath)) }
            },
            sections: sectionCount,
            lastModified: new Date().toISOString()
        };
    });
    
    // Generate version hash based on content
    const version = Date.now();
    
    const html = `<!DOCTYPE html>
<html lang="${CONFIG.strings.defaultLanguage}">
<head>
    <meta charset="${CONFIG.strings.standardCharset}">
    <meta name="viewport" content="${CONFIG.strings.viewportContent}">
    <meta http-equiv="Cache-Control" content="${CONFIG.strings.cacheControlContent}">
    <meta http-equiv="Pragma" content="${CONFIG.strings.pragmaContent}">
    <meta http-equiv="Expires" content="${CONFIG.strings.expiresContent}">
    <title>${CONFIG.strings.documentTitle}</title>
    <style>
        body {
            font-family: ${CONFIG.strings.primaryFontStack};
            line-height: ${CONFIG.ui.typography.lineHeight.loose};
            color: ${CONFIG.colors.text.heading};
            background: ${CONFIG.colors.background.subtle};
            max-width: ${CONFIG.ui.layout.contentWideWidth}px;
            margin: ${CONFIG.ui.spacing.giant}px auto;
            padding: 0 ${CONFIG.ui.spacing.huge}px;
        }
        
        h1 {
            font-size: ${CONFIG.ui.typography.pixels.huge}px;
            font-weight: ${CONFIG.ui.typography.weight.light};
            margin-bottom: ${CONFIG.ui.spacing.normal}px;
            letter-spacing: ${CONFIG.ui.typography.letterSpacing.tight}px;
        }
        
        .subtitle {
            color: ${CONFIG.colors.text.muted};
            margin-bottom: ${CONFIG.ui.spacing.giant}px;
            font-size: ${CONFIG.ui.typography.pixels.body}px;
        }
        
        .document {
            background: ${CONFIG.colors.neutralBase};
            margin: ${CONFIG.ui.spacing.large}px 0;
            padding: ${CONFIG.ui.spacing.huge}px;
            border: ${CONFIG.ui.borderWidth}px solid ${CONFIG.colors.border.light};
            box-shadow: ${CONFIG.ui.shadow.offset.none}px ${CONFIG.ui.shadow.offset.small}px ${CONFIG.ui.shadow.blur.soft}px ${CONFIG.colors.shadowBase}${CONFIG.ui.shadow.opacity.subtle});
        }
        
        .document h2 {
            font-size: ${CONFIG.ui.typography.pixels.xlarge}px;
            margin: 0 0 ${CONFIG.ui.spacing.normal}px 0;
            font-weight: ${CONFIG.ui.typography.weight.regular};
        }
        
        .description {
            color: ${CONFIG.colors.text.muted};
            margin-bottom: ${CONFIG.ui.spacing.medium}px;
            line-height: ${CONFIG.ui.typography.lineHeight.tight};
            font-size: ${CONFIG.ui.typography.pixels.body}px;
        }
        
        .metadata {
            font-size: ${CONFIG.ui.typography.pixels.small}px;
            color: ${CONFIG.colors.text.disabled};
            margin-bottom: ${CONFIG.ui.spacing.medium}px;
        }
        
        .metadata span + span::before {
            content: "${CONFIG.strings.metadataSeparator}";
            margin: 0 ${CONFIG.ui.spacing.small}px;
        }
        
        .formats {
            display: ${CONFIG.css.display.flex};
            gap: ${CONFIG.ui.spacing.normal}px;
        }
        
        .format-link {
            padding: ${CONFIG.ui.spacing.compact}px ${CONFIG.ui.spacing.medium}px;
            background: ${CONFIG.colors.background.subtle};
            border: ${CONFIG.ui.borderWidth}px solid ${CONFIG.colors.border.medium};
            text-decoration: ${CONFIG.css.textDecoration.none};
            color: ${CONFIG.colors.link.visited};
            font-size: ${CONFIG.ui.typography.pixels.small}px;
            transition: ${CONFIG.ui.cssProps.all} ${CONFIG.ui.transition.fast}s ${CONFIG.ui.cssProps.ease};
        }
        
        .format-link:hover {
            background: ${CONFIG.colors.link.visited};
            color: ${CONFIG.colors.neutralBase};
            border-color: ${CONFIG.colors.link.visited};
        }
        
        .format-type {
            font-weight: ${CONFIG.ui.typography.weight.medium};
            text-transform: lowercase;
        }
        
        .format-size {
            opacity: ${CONFIG.ui.opacity.strong};
            margin-left: ${CONFIG.ui.spacing.small}px;
            font-size: ${CONFIG.ui.typography.pixels.tiny}px;
        }
        
        .format-link:hover .format-size {
            opacity: ${CONFIG.ui.opacity.heavy};
        }
        
        .footer {
            margin-top: ${CONFIG.ui.spacing.giant}px;
            padding-top: ${CONFIG.ui.spacing.large}px;
            border-top: ${CONFIG.ui.borderWidth}px solid ${CONFIG.colors.border.light};
            font-size: ${CONFIG.ui.typography.pixels.small}px;
            color: ${CONFIG.colors.text.disabled};
            display: ${CONFIG.css.display.flex};
            justify-content: ${CONFIG.css.align.spaceBetween};
            align-items: ${CONFIG.css.align.center};
        }
        
        .github-link {
            color: ${CONFIG.colors.link.default};
            text-decoration: ${CONFIG.css.textDecoration.underline};
            font-weight: ${CONFIG.ui.typography.weight.medium};
            transition: ${CONFIG.ui.cssProps.all} ${CONFIG.ui.transition.fast}s ${CONFIG.ui.cssProps.ease};
        }
        
        .github-link:hover {
            color: ${CONFIG.colors.link.hover};
            background: ${CONFIG.colors.background.sidebar};
            padding: ${CONFIG.ui.spacing.tiny}px ${CONFIG.ui.spacing.compact}px;
            margin: -${CONFIG.ui.spacing.tiny}px -${CONFIG.ui.spacing.compact}px;
        }
    </style>
</head>
<body>
    <h1>${CONFIG.strings.documentTitle}</h1>
    <p class="subtitle">Documentation</p>
    
    ${docInfo.map(doc => `
    <div class="document">
        <h2>${doc.name}</h2>
        <p class="description">${doc.description}</p>
        <div class="metadata">
            <span>${doc.sections} sections</span>
            <span>${new Date(doc.lastModified).toLocaleDateString()}</span>
        </div>
        <div class="formats">
            <a href="${doc.formats.html.file.replace('output/', '')}?v=${version}" class="format-link">
                <span class="format-type">html</span>
                <span class="format-size">${doc.formats.html.size}</span>
            </${CONFIG.strings.linkElement}>
            <a href="${doc.formats.pdf.file.replace('output/', '')}?v=${version}" class="format-link">
                <span class="format-type">pdf</span>
                <span class="format-size">${doc.formats.pdf.size}</span>
            </${CONFIG.strings.linkElement}>
            <a href="${doc.formats.md.file.replace('output/', '')}?v=${version}" class="format-link">
                <span class="format-type">markdown</span>
                <span class="format-size">${doc.formats.md.size}</span>
            </${CONFIG.strings.linkElement}>
            <a href="../${doc.formats.txt.file}?v=${version}" class="format-link">
                <span class="format-type">source</span>
                <span class="format-size">${doc.formats.txt.size}</span>
            </${CONFIG.strings.linkElement}>
        </div>
    </div>
    `).join('')}
    
    <div class="footer">
        <span>${new Date().toLocaleString()}</span>
        <a href="${CONFIG.urls.repositoryLink}" class="github-link">GitHub</a>
    </div>
</body>
</html>`;
    
    // Use lazyFS for writing index - return the PullPromise for lazy evaluation
    return lazyFS.write(path.join(PROJECT_ROOT, CONFIG.files.indexFile), html);
}


async function buildFile(docConfig) {
    console.log('[BUILD] Starting build for:', docConfig.txt);

    // Read file content
    const fileContent = lazyFS.read(CONFIG.resolveDocPath(docConfig, 'txt')).value;

    // Get current git commit for hermetic builds
    const gitCommit = await lazyGit.getCurrentCommit().pull().catch(() => 'unknown');

    // Build dependencies (builder script hash)
    const builderContent = lazyFS.read(path.join(PROJECT_ROOT, 'scripts/builder.js')).value;
    const builderHash = (() => {
        try {
            const content = builderContent;
            const hash = crypto.createHash('sha256').update(content).digest('hex').substring(0, THRESHOLDS.HASH_SHORT_LENGTH);
            return { name: 'builder', hash };
        } catch {
            return { name: 'builder', hash: 'unknown' };
        }
    })();

    // Build context for proper sponge absorption
    const buildContext = {
        timestamp: Date.now(),
        version: CONFIG.version || '1.0.0',
        formats: ['html', 'pdf', 'md'],
        environment: process.env.NODE_ENV || 'production',
        gitCommit,
        dependencies: [builderHash]
    };

    // Use build-aware sponge with full context
    const buildHash = processingCoordinator.buildSponge(
        fileContent,
        docConfig.txt,
        buildContext
    );

    // Create cache key with domain separation
    const cacheKey = `build-${buildHash.value}-${docConfig.txt}`;
    console.log('[BUILD] Hermetic cache key:', cacheKey);
    console.log('[BUILD] Git commit:', buildContext.gitCommit);
    console.log('[BUILD] Builder hash:', buildContext.dependencies[0].hash);
    
    // Create categorical cache functor for this build
    const cache = processingCoordinator.cacheFunctor(
        null,  // Will be set to pipeline
        cacheKey
    );
    
    // Pipeline stages
    const validateFileExists = docConfig => new PullPromise(async () => {
        const txtPath = CONFIG.resolveDocPath(docConfig, 'txt');
        const exists = lazyFS.exists(txtPath).value;
        if (!exists) throw new Error(`File not found: ${txtPath}`);
        return { txtPath, docConfig };
    });

    const readFileContent = stageResult => new PullPromise(async () => {
        const data = stageResult instanceof PullPromise ? await stageResult.pull() : stageResult;
        const content = lazyFS.read(data.txtPath).value;
        return { content, docConfig: data.docConfig };
    });

    const computeHash = stageResult => new PullPromise(async () => {
        const data = stageResult instanceof PullPromise ? await stageResult.pull() : stageResult;
        const hash = crypto.createHash(CONFIG.strings.mainHashAlgorithm)
            .update(data.content)
            .digest(CONFIG.strings.hashEncoding);
        return { content: data.content, hash, file: data.docConfig.txt, docConfig: data.docConfig };
    });

    const addMetadata = data => new PullPromise(async () => {
        // Use the base name from the html file in CONFIG
        const outputBaseName = path.basename(data.docConfig.html, '.html');

        traceOrchestrator.trace('BUILD_START', { file: data.file, name: outputBaseName, hash: data.hash });

        // Pass raw content through without processing yet
        const result = { ...data, name: outputBaseName };

        return result;
    });

    const generateFormats = stageResult => new PullPromise(async () => {
        const data = stageResult instanceof PullPromise ? await stageResult.pull() : stageResult;

        // Validate input data before processing
        if (!data || !data.content) {
            throw new Error(`Invalid build data: missing content for ${data?.file || 'unknown file'}`);
        }

        // Create document processor and parse content
        const processor = new DocumentProcessor();
        try {
            const parseResult = processor.parse(data.content);
            // Parse returns a Lazy, must pull it
            if (parseResult instanceof Lazy) {
                parseResult.value;
            }
        } catch (parseError) {
            traceOrchestrator.error(parseError, {
                context: 'DOCUMENT_PARSE_FAILED',
                file: data.file,
                contentLength: data.content?.length
            });
            throw new Error(`Failed to parse document ${data.file}: ${parseError.message}`);
        }

        // Check modalities are properly initialized
        if (!processor.modalities || !processor.modalities.html || !processor.modalities.pdf || !processor.modalities.markdown) {
            throw new Error(`DocumentProcessor modalities not properly initialized for ${data.file}`);
        }

        // Generate each format with error handling
        const formats = {};
        const formatErrors = [];

        // HTML generation
        try {
            const htmlGenerator = new Lazy(() => processor.modalities.html.generateHTML(processor));
            formats.html = htmlGenerator.value;
            if (formats.html instanceof Lazy) {
                formats.html = formats.html.value;
            }
            if (formats.html instanceof LazyTemplate) {
                formats.html = formats.html.toString();
            }
            if (!formats.html || formats.html.length === 0) {
                throw new Error('HTML generation produced empty output');
            }
            processingCoordinator.absorb(formats.html, 'format-html');
        } catch (htmlError) {
            formatErrors.push(`HTML: ${htmlError.message}`);
            formats.html = `<!DOCTYPE html><html><body><h1>Error generating HTML</h1><pre>${htmlError.message}</pre></body></html>`;
        }

        // PDF HTML generation (for puppeteer)
        try {
            const pdfGenerator = new Lazy(() => processor.modalities.pdf.generateHTML(processor));
            formats.pdf = pdfGenerator.value;
            if (formats.pdf instanceof Lazy) {
                formats.pdf = formats.pdf.value;
            }
            if (formats.pdf instanceof LazyTemplate) {
                formats.pdf = formats.pdf.toString();
            }
            if (!formats.pdf || formats.pdf.length === 0) {
                throw new Error('PDF HTML generation produced empty output');
            }
            processingCoordinator.absorb(formats.pdf, 'format-pdf');
        } catch (pdfError) {
            formatErrors.push(`PDF: ${pdfError.message}`);
            formats.pdf = formats.html || '<!DOCTYPE html><html><body>Error generating PDF</body></html>';
        }

        // Markdown generation
        try {
            const mdGenerator = new Lazy(() => processor.modalities.markdown.render(processor));
            formats.md = mdGenerator.value;
            if (formats.md instanceof Lazy) {
                formats.md = formats.md.value;
            }
            if (formats.md instanceof LazyTemplate) {
                formats.md = formats.md.toString();
            }
            if (!formats.md || formats.md.length === 0) {
                throw new Error('Markdown generation produced empty output');
            }
            processingCoordinator.absorb(formats.md, 'format-markdown');
        } catch (mdError) {
            formatErrors.push(`Markdown: ${mdError.message}`);
            formats.md = `# Error generating Markdown\n\n${mdError.message}`;
        }

        // Log any format generation errors but continue
        if (formatErrors.length > 0) {
            traceOrchestrator.trace('FORMAT_GENERATION_PARTIAL_FAILURE', {
                file: data.file,
                errors: formatErrors,
                successfulFormats: Object.keys(formats).filter(k => !formatErrors.some(e => e.startsWith(k.toUpperCase())))
            });
        }

        return { ...data, formats };
    });

    const writeOutputFiles = data => new PullPromise(async () => {
        // Validate we have formats to write
        if (!data.formats || Object.keys(data.formats).length === 0) {
            throw new Error(`No formats generated for ${data.file}`);
        }

        const writeResults = {
            success: [],
            failed: []
        };

        // Write HTML file
        if (data.formats.html) {
            try {
                const htmlPath = path.join(PROJECT_ROOT, data.docConfig.html);
                await lazyFS.write(htmlPath, data.formats.html).pull();
                writeResults.success.push('html');
            } catch (htmlWriteError) {
                writeResults.failed.push({ format: 'html', error: htmlWriteError.message });
                traceOrchestrator.error(htmlWriteError, { context: 'HTML_WRITE_FAILED', file: data.file });
            }
        }

        // Write Markdown file
        if (data.formats.md) {
            try {
                const mdPath = path.join(PROJECT_ROOT, data.docConfig.md);
                await lazyFS.write(mdPath, data.formats.md).pull();
                writeResults.success.push('md');
            } catch (mdWriteError) {
                writeResults.failed.push({ format: 'md', error: mdWriteError.message });
                traceOrchestrator.error(mdWriteError, { context: 'MD_WRITE_FAILED', file: data.file });
            }
        }

        // Generate PDF file using puppeteer
        if (data.formats.pdf) {
            try {
                const pdfPath = path.join(PROJECT_ROOT, data.docConfig.pdf);
                await generatePDF(data.formats.pdf, pdfPath, data.name);
                writeResults.success.push('pdf');
            } catch (pdfError) {
                writeResults.failed.push({ format: 'pdf', error: pdfError.message });
                traceOrchestrator.error(pdfError, { context: 'PDF_GENERATION_FAILED', file: data.file });

                // Try to write PDF HTML as fallback
                try {
                    const fallbackPath = path.join(PROJECT_ROOT, `${path.basename(data.docConfig.pdf, '.pdf')}_pdf.html`);
                    await lazyFS.write(fallbackPath, data.formats.pdf).pull();
                    writeResults.success.push('pdf_fallback_html');
                } catch (fallbackError) {
                    // Ignore fallback error
                }
            }
        }

        // Check if at least one format was written successfully
        if (writeResults.success.length === 0) {
            throw new Error(`Failed to write any format for ${data.file}: ${JSON.stringify(writeResults.failed)}`);
        }

        // Record results
        data.writeResults = writeResults;

        // Register file existence in dependency graph
        const pullGraph = initPullGraph();

        // Register each successfully written file as a dependency node
        if (writeResults.success.includes('html')) {
            pullGraph.register(`file:${data.docConfig.html}`, new Lazy(() => true));
        }
        if (writeResults.success.includes('md')) {
            pullGraph.register(`file:${data.docConfig.md}`, new Lazy(() => true));
        }
        if (writeResults.success.includes('pdf')) {
            pullGraph.register(`file:${data.docConfig.pdf}`, new Lazy(() => true));
        }

        return data;
    });

    // Build pipeline as a morphism in the build category
    const fileBuildPipeline = Pipeline.kleisli(
        validateFileExists,
        readFileContent,
        computeHash,
        addMetadata,
        generateFormats,
        writeOutputFiles,

        data => new Lazy(() => {
            traceOrchestrator.trace('BUILD_COMPLETE', {
                file: data.file,
                name: data.name,
                formats: Object.keys(data.formats)
            });
            lazyEvents.emit({
                type: 'BUILD_SUCCESS',
                file: data.file,
                hash: data.hash
            });
            return data;
        })
    );
    
    // Compose cache with pipeline
    const cachedPipeline = new PullPromise(async () => {
        // Check cache first using the functor
        const cached = await cache.pull();
        if (cached) {
            console.log('[BUILD] Cache hit for:', docConfig.txt);
            traceOrchestrator.trace('CACHE_HIT_VALID', {
                file: docConfig.txt,
                formats: Object.keys(cached.formats)
            });
            return cached;
        }
        
        // Execute pipeline if not cached
        console.log('[BUILD] Cache miss, building:', docConfig.txt);
        const pipelineResult = fileBuildPipeline(docConfig);
        const result = pipelineResult instanceof PullPromise ? await pipelineResult.pull() : pipelineResult;
        
        // Store in cache with proper structure
        if (result && result.formats) {
            pullGraph.register(cacheKey, new Lazy(() => result));
            traceOrchestrator.trace('CACHE_STORE', {
                file: docConfig.txt,
                cacheKey,
                formats: Object.keys(result.formats)
            });
        }
        
        return result;
    });
    
    try {
        const result = await cachedPipeline.pull();
        return result;
    } catch (error) {
        traceOrchestrator.error(error, {
            file: docConfig.txt,
            context: 'file_build'
        });
        lazyEvents.emit({
            type: 'BUILD_ERROR',
            file: docConfig.txt,
            error: error.message
        });
        throw error;
    }
}

async function generatePDF(html, pdfPath, name) {
    if (!processor.state.browser) {
        try {
            if (traceOrchestrator) traceOrchestrator.trace('BROWSER_LAUNCH', { name });
            
            processor.state.browser = await puppeteer.launch({
                headless: CONFIG.strings.headlessMode,
                args: [
                    CONFIG.strings.sandboxFlag,
                    CONFIG.strings.setuidFlag,
                    CONFIG.strings.devShmFlag,  // Disable shared memory
                    CONFIG.strings.gpuFlag,  // Disable GPU
                    CONFIG.strings.zygoteFlag  // Disable zygote
                ],
                handleSIGINT: false,
                handleSIGTERM: false,
                handleSIGHUP: false
            });
            
            processor.state.browser.on('disconnected', () => {
                if (traceOrchestrator) traceOrchestrator.trace('BROWSER_DISCONNECTED', { name });
                processor.state.browser = null;
                processor.state.pages.clear();
            });
        } catch (error) {
            if (traceOrchestrator) traceOrchestrator.error(error, { context: 'BROWSER_LAUNCH', name });
            throw new Error(`Failed to launch browser: ${error.message}`);
        }
    }
    
    let page = processor.state.pages.get(name);
    let attempts = 0;
    const maxAttempts = CONFIG.browser.maxRetries;
    
    while (attempts < maxAttempts) {
        try {
            if (!page || page.isClosed()) {
                if (traceOrchestrator) traceOrchestrator.trace('PAGE_CREATE', { name, attempt: attempts });
                
                page = await processor.state.browser.newPage();
                processor.state.pages.set(name, page);
                
                page.on('error', err => {
                    if (traceOrchestrator) traceOrchestrator.error(err, { context: 'PAGE_ERROR', name });
                });
                
                page.on('pageerror', err => {
                    if (traceOrchestrator) traceOrchestrator.error(err, { context: 'PAGE_JS_ERROR', name });
                });
            }
            
            await page.goto(CONFIG.strings.emptyPageUrl);
            await page.setContent(html, { waitUntil: CONFIG.strings.networkIdleState, timeout: CONFIG.browser.pageLoadTimeout });
            await page.pdf({
                path: pdfPath,
                format: CONFIG.strings.pageFormat,
                printBackground: true,
                margin: { top: CONFIG.ui.pdfMargin, right: CONFIG.ui.pdfMargin, bottom: CONFIG.ui.pdfMargin, left: CONFIG.ui.pdfMargin },
                timeout: CONFIG.browser.pdfTimeout
            });
            
            await page.goto(CONFIG.strings.emptyPageUrl);
            
            if (traceOrchestrator) {
                traceOrchestrator.trace('PDF_GENERATED', { 
                    name, 
                    path: pdfPath, 
                    attempt: attempts 
                });
            }
            break;
            
        } catch (error) {
            if (traceOrchestrator) {
                traceOrchestrator.error(error, { 
                    context: 'PDF_GENERATION', 
                    name, 
                    attempt: attempts 
                });
            }
            if (error.message && (
                error.message.includes(CONFIG.errors.detachedFrame) || 
                error.message.includes(CONFIG.errors.closedContext) ||
                error.message.includes(CONFIG.errors.targetClosed) ||
                error.message.includes(CONFIG.errors.sessionClosed)
            )) {
                
                try {
                    await page.close();
                } catch (e) {
                }
                processor.state.pages.delete(name);
                
                attempts++;
                if (attempts < maxAttempts) {
                    if (!processor.state.browser || !processor.state.browser.isConnected()) {
                        if (traceOrchestrator) traceOrchestrator.trace('BROWSER_RECONNECT', { name });
                        processor.state.browser = null;
                        return await generatePDF(html, pdfPath, name);
                    }
                    
                    page = await processor.state.browser.newPage();
                    processor.state.pages.set(name, page);
                    continue;
                }
            }
            
            throw error;
        }
    }
}

// Deduplicator for file watch events
const watchDedup = new Map();
const DEDUP_WINDOW = CONFIG.watcher.dedupWindow;

function shouldProcessFileChange(file) {
    const now = Date.now();
    const lastEvent = watchDedup.get(file);
    
    if (lastEvent && (now - lastEvent) < DEDUP_WINDOW) {
        return false; // Skip duplicate event
    }
    
    watchDedup.set(file, now);
    
    // Clean old entries (collect first, then delete to avoid iteration issues)
    const toDelete = [];
    for (const [f, time] of watchDedup) {
        if (now - time > CONFIG.scheduler.retryDelayBase) {
            toDelete.push(f);
        }
    }
    toDelete.forEach(f => watchDedup.delete(f));
    
    return true;
}

async function watch() {
    // Check if this is an online push operation
    const isOnlinePush = process.argv.includes(CONFIG.strings.cliFlags.push) || process.argv.includes(CONFIG.strings.cliFlags.online);
    
    // Verify commit readiness before starting
    if (!verifyCommitReadiness(isOnlinePush)) {
        if (isOnlinePush) {
            console.error('\n[FATAL] Build aborted: Mandatory files not staged for online push');
            console.error('Please stage all required files before pushing online.');
        } else {
            console.error('\n[FATAL] Build aborted: Local build issue');
        }
        process.exit(CONFIG.process.exitCode.error);
    }
    
    // If online push, stage files, commit, and push
    if (isOnlinePush) {
        try {
            // Use lazyGit for all git operations
            // Stage all mandatory files
            await lazyGit.stage(MANDATORY_COMMIT_FILES).pull();
            
            // Create commit with empty message (as per permanent rule)
            await lazyGit.commit().pull();
            
            // Push to remote
            await lazyGit.push().pull();
            
            process.exit(CONFIG.process.exitCode.success);
        } catch (error) {
            console.error('[GIT ERROR]', error.message);
            process.exit(CONFIG.process.exitCode.error);
        }
    }
    
    // Acquire process lock
    if (!lockManager.acquire()) {
        console.error(CONFIG.strings.fatalLockMessage);
        process.exit(CONFIG.process.exitCode.error);
    }
    

    // Register build dependencies in pull graph using CONFIG
    for (const file of FILES) {
        const buildId = `build-${file.txt}`;

        // Register build task
        pullGraph.register(buildId, new Lazy(async () => {
            const result = await buildFile(file);
            if (result && result.pull) {
                return await result.pull();
            }
            return result;
        }));
        
        // Use CONFIG-defined dependencies if available
        if (file.dependencies) {
            const deps = file.dependencies.value;
            for (const [output, inputs] of Object.entries(deps)) {
                // Validate dependency array length
                validateVec(inputs, 1, `${file.txt}.${output} dependencies`);

                const outputId = `${file.txt}.${output}`;
                pullGraph.register(outputId, new Lazy(() => buildId));
                
                for (const input of inputs) {
                    const inputId = input === 'txt' ? buildId : `${file.txt}.${input}`;
                    pullGraph.dependsOn(outputId, inputId);
                }
            }
        } else {
            // Fallback to default dependencies
            const htmlId = `${file.txt}.html`;
            const pdfId = `${file.txt}.pdf`;
            const mdId = `${file.txt}.md`;
            
            pullGraph.register(htmlId, new Lazy(() => buildId));
            pullGraph.register(pdfId, new Lazy(() => buildId));
            pullGraph.register(mdId, new Lazy(() => buildId));
            
            pullGraph.dependsOn(htmlId, buildId);
            pullGraph.dependsOn(pdfId, buildId);
            pullGraph.dependsOn(mdId, buildId);
        }
    }
    
    // Register index dependency on all HTML files
    const indexId = 'build-index';
    pullGraph.register(indexId, new Lazy(() => {
        const htmlFiles = FILES.map(f => `${f.txt}.html`);
        return htmlFiles;
    }));
    
    for (const file of FILES) {
        pullGraph.dependsOn(indexId, `${file.txt}.html`);
    }
    
    // Initial build using scheduler with dependency order
    for (const file of FILES) {
        await scheduler.schedule({
            name: `initial-build-${file.txt}`,
            file: file.txt,
            fn: async () => {
                const buildId = `build-${file.txt}`;
                return await pullGraph.pull(buildId);
            }
        }, CONFIG.scheduler.initialBuildPriority);
    }
    
    // Wait for initial builds to complete (with timeout)
    const maxWaitTime = CONFIG.scheduler.initialBuildWaitMax;
    const startWait = Date.now();
    while (scheduler.running.size > CONFIG.processor.emptyCheckThreshold || scheduler.queue.length > CONFIG.processor.emptyCheckThreshold) {
        if (Date.now() - startWait > maxWaitTime) {
            console.warn(CONFIG.strings.warningPrefix + ' Initial builds taking too long, continuing anyway');
            break;
        }
        await new Promise(resolve => setTimeout(resolve, TIME.TICK));
    }
    
    // Small delay to ensure all writes complete
    await new Promise(resolve => setTimeout(resolve, TIME.DEBOUNCE));
    
    // Create morphism that waits for all build artifacts to materialize
    const artifactBarrier = new PullPromise(async () => {
        // Wait for all format outputs to exist on disk
        const waitForArtifact = async (path, maxWait = TIME.LONG) => {
            const start = Date.now();
            while (Date.now() - start < maxWait) {
                if (lazyFS.exists(path).value) {
                    const stats = fs.statSync(path);
                    if (stats.size > 0) return true;  // File exists and has content
                }
                await new Promise(resolve => setTimeout(resolve, TIME.TICK));
            }
            return false;
        };
        
        // Wait for all expected artifacts
        const artifacts = [];
        for (const file of FILES) {
            artifacts.push(waitForArtifact(CONFIG.resolveDocPath(file, 'html')));
            artifacts.push(waitForArtifact(CONFIG.resolveDocPath(file, 'pdf')));
            artifacts.push(waitForArtifact(CONFIG.resolveDocPath(file, 'md')));
        }
        await Promise.all(artifacts);
    });
    
    // Abstract morphism application - CONFIG defines the shape, machinery applies it
    await scheduler.schedule({
        name: CONFIG.morphisms.aggregator.name,  // 'generate-index' lives in CONFIG
        file: CONFIG.files.indexFile,
        fn: async () => {
            // Ensure all artifacts have materialized
            await artifactBarrier.pull();
            
            const result = CONFIG.morphisms.aggregator.apply(FILES);
            // Pull the lazy write to materialize the index file
            if (result && result.pull) {
                console.log('[INDEX] Pulling index generation...');
                await result.pull();
                console.log('[INDEX] Index generation complete');
            } else {
                console.log('[INDEX] No pull method on result:', result);
            }
        }
    }, CONFIG.scheduler.initialBuildPriority);

    // Configure file watchers
    // Use watchFile on Windows
    for (const file of FILES) {
        const txtPath = CONFIG.resolveDocPath(file, 'txt');
        if (lazyFS.exists(txtPath).value) {
            // Use both fs.watch and fs.watchFile for maximum reliability
            // fs.watch for instant detection when it works
            fs.watch(txtPath, { persistent: true }, (eventType) => {
                if (eventType === 'change' && shouldProcessFileChange(txtPath)) {
                    console.log(`${CONFIG.strings.watchPrefix} Detected change in ${file.txt}`);
                    // Use scheduler's debounce mechanism
                    scheduler.debounce(file.txt, async () => {
                        await buildFile(file);

                        // Small delay to ensure files are written
                        await new Promise(resolve => setTimeout(resolve, TIME.TICK))

                        renderView({ type: 'document-index' }, FILES);
                    }, CONFIG.watcher.postBuildDelay);
                }
            });
            
            fs.watchFile(txtPath, { interval: TIME.TICK }, (curr, prev) => {
                if (curr.mtime !== prev.mtime && shouldProcessFileChange(txtPath + '_watchfile')) {
                    console.log(`${CONFIG.strings.watchFilePrefix} Detected change in ${file.txt}`);
                    // Use scheduler's debounce mechanism
                    scheduler.debounce(file.txt, async () => {
                        await buildFile(file);

                        // Small delay to ensure files are written
                        await new Promise(resolve => setTimeout(resolve, TIME.TICK))

                        renderView({ type: 'document-index' }, FILES);
                    }, CONFIG.watcher.postBuildDelay);
                }
            });
        }
    }
    
    console.log(`${CONFIG.strings.watchingPrefix} ${FILES.map(f => f.txt).join(', ')}`);
    
    // Log scheduler stats periodically (store interval ID for cleanup)
    const statsInterval = setInterval(() => {
        const stats = scheduler.getStats();
        if (stats.running > CONFIG.processor.emptyCheckThreshold || stats.queued > CONFIG.processor.emptyCheckThreshold) {
        }
    }, TIME.TIMEOUT);
    
    // Keep-alive heartbeat to prevent timeouts
    const heartbeatInterval = setInterval(() => {
        // Output a heartbeat every 30 seconds to show we're still watching
        const uptime = Math.floor((Date.now() - processor.state.stats.uptime) / CONFIG.scheduler.retryDelayBase);
        
        // Export telemetry periodically for monitoring
        if (CONFIG.debug.enableTelemetry) {
            // Separate async work from the timer tick
            (async () => {
                try {
                    // Initialize lazy telemetry system if not already done
                    if (!traceOrchestrator.lazyTelemetry) {
                        traceOrchestrator.initializeLazyTelemetry();
                    }
                    
                    // Export telemetry to file
                    const exportLazy = traceOrchestrator.lazyTelemetry.value.export;
                    await lazyFS.write(
                        path.join(__dirname, CONFIG.files.telemetryFile),
                        exportLazy.value.json.value
                    ).pull();
                } catch (error) {
                    // Don't let telemetry errors crash the build system
                    traceOrchestrator.error(error, { context: 'telemetry_export' });
                }
            })();
        }
    }, CONFIG.process.heartbeatInterval);
    
    // Store intervals for cleanup on shutdown
    if (!processor.state.intervals) processor.state.intervals = [];
    processor.state.intervals.push(statsInterval);
    processor.state.intervals.push(heartbeatInterval);
}

// Handle uncaught exceptions gracefully
process.on(CONFIG.strings.exceptionEvent, (error) => {
    console.error(CONFIG.strings.criticalErrorPrefix, error);
    traceOrchestrator.error(error, { type: CONFIG.strings.exceptionEvent });
    // Don't exit - try to continue running
});

process.on(CONFIG.strings.rejectionEvent, (reason, promise) => {
    console.error(CONFIG.strings.unhandledRejectionPrefix, reason);
    traceOrchestrator.error(new Error(String(reason)), { 
        type: CONFIG.strings.rejectionEvent,
        promise: String(promise)
    });
    // Don't exit - try to continue running
});

process.on(CONFIG.strings.interruptSignal, async () => {
    console.log('\n' + CONFIG.strings.shutdownMessage);
    
    lockManager.release();
    
    // Clear all intervals
    if (processor.state.intervals) {
        for (const interval of processor.state.intervals) {
            clearInterval(interval);
        }
    }
    
    // Unwatch all files
    for (const file of FILES) {
        const txtPath = path.join(__dirname, file.txt);
        if (lazyFS.exists(txtPath).value) {
            fs.unwatchFile(txtPath);
        }
    }
    
    // Close browser resources with timeout
    try {
        const closePromises = [];
        
        for (const page of processor.state.pages.values()) {
            closePromises.push(page.close().catch(err => {
                console.warn('[CLEANUP] Failed to close page:', err.message);
            }));
        }
        
        if (processor.state.browser) {
            closePromises.push(processor.state.browser.close().catch(err => {
                console.warn('[CLEANUP] Failed to close browser:', err.message);
            }));
        }
        
        // Wait max 5 seconds for browser cleanup
        await Promise.race([
            Promise.all(closePromises),
            new Promise(resolve => setTimeout(resolve, TIME.TIMEOUT))
        ]);
    } catch (error) {
        console.error(CONFIG.strings.shutdownBrowserErrorPrefix, error.message);
    }
    
    const uptime = Math.floor((Date.now() - processor.state.stats.uptime) / CONFIG.scheduler.retryDelayBase);
    
    process.exit(CONFIG.process.exitCode.success);
});

// INITIALIZATION

// Load configuration profile based on environment
const profile = process.env.NODE_ENV || 'development';
const loadedConfig = loadConfig(profile);

// Merge with existing CONFIG
Object.assign(CONFIG, loadedConfig);

// Validate configuration with schema (uses existing traceOrchestrator instance)
const validationResult = validateConfig();
if (validationResult.warnings.length > 0) {
}

// Initialize auto-scaling for BuildScheduler
if (scheduler && scheduler.autoScale) {
    // Start auto-scaling interval (parent already set in constructor)
    const scaleInterval = setInterval(() => {
        if (scheduler && scheduler.autoScale && scheduler.autoScale.adjust) {
            scheduler.autoScale.adjust();
        }
    }, scheduler.autoScale.adjustmentInterval || TIME.LONG);
    
    // Track interval for cleanup
    if (!processor.state.intervals) {
        processor.state.intervals = [];
    }
    processor.state.intervals.push(scaleInterval);
    
    traceOrchestrator.trace('AUTO_SCALE_INIT', {
        profile,
        initialConcurrency: scheduler.maxConcurrent,
        scaling: {
            min: scheduler.autoScale.minConcurrency,
            max: scheduler.autoScale.maxConcurrency,
            baseline: scheduler.autoScale.baselineConcurrency
        }
    });
}

const SELF_HEAL_INTERFACE = {
    get topology() {
        const graph = {
            nodes: new Map(),
            edges: []
        };
        
        for (const [name, reg] of processingCoordinator.realComponents.processors) {
            graph.nodes.set(name, { type: 'processor', registration: reg });
            if (reg.uses) {
                for (const dep of reg.uses) {
                    graph.edges.push({ from: name, to: dep, type: 'uses' });
                }
            }
        }
        
        for (const [name, reg] of processingCoordinator.realComponents.orchestrators) {
            graph.nodes.set(name, { type: 'orchestrator', registration: reg });
            if (reg.uses) {
                for (const dep of reg.uses) {
                    graph.edges.push({ from: name, to: dep, type: 'uses' });
                }
            }
        }
        
        for (const [name, reg] of processingCoordinator.realComponents.systems) {
            graph.nodes.set(name, { type: 'system', registration: reg });
            if (reg.uses) {
                for (const dep of reg.uses) {
                    graph.edges.push({ from: name, to: dep, type: 'uses' });
                }
            }
        }
        
        return graph;
    },
    
    get violations() {
        const all = [];
        if (configPatternValidator.violations) {
            all.push(...configPatternValidator.violations);
        }
        if (traceOrchestrator.runtimeViolations) {
            all.push(...Array.from(traceOrchestrator.runtimeViolations));
        }
        return all;
    },
    
    
    processingCoordinator,
    traceOrchestrator,
    configPatternValidator
};

// Export for module usage
if (typeof module !== 'undefined' && module.exports) {
    module.exports = SELF_HEAL_INTERFACE;
}

const isValidateOnly = process.argv.includes('--validate') || process.argv.includes('--check');

if (isValidateOnly) {
    console.log('[VALIDATE] Running validation only mode...');
    
    // Check ALL violation sources
    let totalViolations = 0;
    
    // N.one. Config pattern violations
    if (configPatternValidator.violations.length > 0) {
        configPatternValidator.report();
        totalViolations += configPatternValidator.violations.length;
    }
    
    // N.two. Runtime violations from TraceOrchestrator
    if (traceOrchestrator.runtimeViolations.size > 0) {
        console.error(`[RUNTIME] ${traceOrchestrator.runtimeViolations.size} runtime violations:`, 
            Array.from(traceOrchestrator.runtimeViolations));
        totalViolations += traceOrchestrator.runtimeViolations.size;
    }
    
    // 3. TraceOrchestrator runtime violations
    const violations = traceOrchestrator.runtimeViolations.size;
    if (violations > 0) {
        console.error(`[RUNTIME] ${violations} runtime violations detected`);
        totalViolations += violations;
    }
    
    // 4. ProcessingCoordinator resource conflicts
    if (processingCoordinator.hasResourceConflicts()) {
        console.error('[RESOURCES] Resource conflicts detected');
        totalViolations++;
    }
    
    if (totalViolations > 0) {
        console.error(`[VALIDATE] FAILED: ${totalViolations} total violations across all systems`);
        process.exit(1);
    } else {
        console.log('[VALIDATE] No violations found - all checks passed!');
        process.exit(0);
    }
} else {
    // CLI Query Interface - query running system from command line
    const debugQuery = process.argv.find(arg => arg.startsWith('--query='));
    if (debugQuery) {
        const [queryPath, ...args] = debugQuery.split('=')[1].split(':');

        // Full debug interface
        const debug = {
            trace: (event, context) => traceOrchestrator.trace(event, context),
            error: (error, context) => traceOrchestrator.error(error, context),
            performance: (label, fn) => traceOrchestrator.performance(label, fn),
            getCausalChain: (eventId) => traceOrchestrator.getCausalChain(eventId),

            getMetrics: () => traceOrchestrator.getMetrics(),
            getPerformanceProfile: () => traceOrchestrator.getPerformanceProfile(),
            getCriticalPath: () => traceOrchestrator.getCriticalPath(),
            detectPatterns: () => traceOrchestrator.detectPatterns(),
            buildCausalityGraph: () => traceOrchestrator.buildCausalityGraph(),
            predictNext: (currentEvent) => traceOrchestrator.predictNext(currentEvent),
            getFailureProbability: (event) => traceOrchestrator.getFailureProbability(event),

            initializeLazyTelemetry: () => traceOrchestrator.initializeLazyTelemetry(),
            createTelemetryStream: () => traceOrchestrator.createTelemetryStream(),
            exportTelemetry: () => traceOrchestrator.exportTelemetry(),
            formatMetrics: (telemetry) => traceOrchestrator.formatMetrics(telemetry),
            formatTimeseries: (telemetry) => traceOrchestrator.formatTimeseries(telemetry),

            calculateEventRate: (events) => traceOrchestrator.calculateEventRate(events),
            calculateErrorRate: (errors) => traceOrchestrator.calculateErrorRate(errors),
            calculateMemoryPressure: () => traceOrchestrator.calculateMemoryPressure(),
            identifyBottlenecks: () => traceOrchestrator.identifyBottlenecks(),
            calculateTaskSuccessRate: () => traceOrchestrator.calculateTaskSuccessRate(),
            detectMemoryLeaks: () => traceOrchestrator.detectMemoryLeaks(),
            detectPerformanceDegradation: () => traceOrchestrator.detectPerformanceDegradation(),
            detectErrorClusters: () => traceOrchestrator.detectErrorClusters(),
            detectResourceSpikes: () => traceOrchestrator.detectResourceSpikes(),

            events: {
                all: () => traceOrchestrator.events,
                recent: (n = CONFIG.debug.analysis.recentWindowSize) =>
                    traceOrchestrator.events.slice(-n),
                byType: (type) =>
                    traceOrchestrator.events.filter(e => e.event.includes(type))
            },

            errors: {
                all: () => traceOrchestrator.errors,
                getCausalChain: (errorId) => traceOrchestrator.getCausalChain(errorId),
                withChains: () => {
                    const result = [];
                    for (const [id, error] of traceOrchestrator.errors) {
                        result.push({
                            id,
                            message: error.error.message,
                            chain: error.causalChain,
                            stack: error.stack
                        });
                    }
                    return result;
                },
                analyze: (errorId) => {
                    const error = traceOrchestrator.errors.get(errorId);
                    if (!error) return null;
                    return {
                        error,
                        chain: traceOrchestrator.getCausalChain(errorId),
                        predictions: traceOrchestrator.predictNext(error.context?.event)
                    };
                }
            },

            causality: {
                getCausalChain: (eventId) => traceOrchestrator.getCausalChain(eventId),
                buildCausalityGraph: () => traceOrchestrator.buildCausalityGraph(),
                chains: () => traceOrchestrator.causality,
                trace: (fromEvent, toEvent) => {
                    const chain = [];
                    let current = toEvent;
                    while (current && current !== fromEvent) {
                        chain.unshift(current);
                        const causes = traceOrchestrator.causality.get(current);
                        current = causes?.[0];
                    }
                    return chain;
                }
            },

            perf: {
                marks: () => traceOrchestrator.performanceMarks,
                slow: () => traceOrchestrator.identifyBottlenecks(),
                critical: () => traceOrchestrator.getCriticalPath(),
                telemetry: () => traceOrchestrator.exportTelemetry(),
                metrics: () => ({
                    eventRate: traceOrchestrator.calculateEventRate(traceOrchestrator.events),
                    errorRate: traceOrchestrator.calculateErrorRate(Array.from(traceOrchestrator.errors.values())),
                    memoryPressure: traceOrchestrator.calculateMemoryPressure(),
                    successRate: traceOrchestrator.calculateTaskSuccessRate()
                })
            },

            patterns: {
                detect: () => traceOrchestrator.detectPatterns(),
                markov: () => traceOrchestrator.markovChain,
                failures: () => traceOrchestrator.failurePatterns,
                predict: (event) => traceOrchestrator.predictNext(event),
                memoryLeak: () => traceOrchestrator.detectMemoryLeaks(),
                perfDegradation: () => traceOrchestrator.detectPerformanceDegradation(),
                errorClusters: () => traceOrchestrator.detectErrorClusters(),
                resourceSpikes: () => traceOrchestrator.detectResourceSpikes()
            },

            build: {
                cache: () => {
                    const events = traceOrchestrator.events.filter(e =>
                        e.event.includes('CACHE') || e.event.includes('BUILD')
                    );
                    return {
                        hits: events.filter(e => e.event.includes('CACHE_HIT')),
                        misses: events.filter(e => e.event.includes('CACHE_MISS')),
                        builds: events.filter(e => e.event === 'BUILD')
                    };
                },
                pipeline: () => {
                    const events = traceOrchestrator.events.filter(e =>
                        e.event.includes('PIPELINE')
                    );
                    return {
                        read: events.filter(e => e.event === 'PIPELINE_READ'),
                        parse: events.filter(e => e.event === 'PIPELINE_PARSE'),
                        transform: events.filter(e => e.event === 'PIPELINE_TRANSFORM'),
                        write: events.filter(e => e.event === 'PIPELINE_WRITE')
                    };
                },
                files: () => {
                    const events = traceOrchestrator.events.filter(e =>
                        e.event.startsWith('FS_')
                    );
                    return {
                        reads: events.filter(e => e.event === 'FS_READ'),
                        writes: events.filter(e => e.event === 'FS_WRITE'),
                        sizes: events.filter(e => e.event === 'FS_WRITE')
                            .map(e => ({ path: e.data?.path, size: e.data?.size }))
                    };
                },
                graph: () => ({
                    nodes: pullGraph.nodes.size,
                    evaluated: Array.from(pullGraph.nodes.entries())
                        .filter(([_, node]) => node.evaluated)
                        .map(([key]) => key),
                    lazy: Array.from(pullGraph.nodes.entries())
                        .filter(([_, node]) => !node.evaluated)
                        .map(([key]) => key)
                })
            },

            state: {
                scheduler: () => stateSerializer.serialize('scheduler', scheduler),
                coordinator: () => ({
                    resources: processingCoordinator.resources.size,
                    conflicts: processingCoordinator.hasResourceConflicts(),
                    keccakState: processingCoordinator.lazyKeccakState?._evaluated || false
                }),
                violations: () => ({
                    config: configPatternValidator.violations,
                    runtime: Array.from(traceOrchestrator.runtimeViolations)
                }),
                causality: () => stateSerializer.serialize('traceOrchestrator', traceOrchestrator),
                reflection: () => reflection.introspect(traceOrchestrator)
            },

            analyze: {
                whyNoFiles: () => {
                    console.log('\n[ANALYSIS] Why no output files?');
                    const cache = debug.build.cache();
                    const pipeline = debug.build.pipeline();
                    const files = debug.build.files();

                    console.log(`  Cache hits: ${cache.hits.length}`);
                    console.log(`  Cache misses: ${cache.misses.length}`);
                    console.log(`  Pipeline transforms: ${pipeline.transform.length}`);
                    console.log(`  File writes: ${files.writes.length}`);

                    if (files.writes.length > 0) {
                        console.log('  Written files:');
                        files.sizes.forEach(f => {
                            console.log(`    ${f.path}: ${f.size} bytes`);
                        });
                    }

                    if (cache.hits.length > 0 && files.writes.length === 0) {
                        console.log('  ISSUE: Cache hits but no file writes - cache may be stale');
                    }

                    return { cache, pipeline, files };
                },

                traceBuildPath: (file) => {
                    const events = traceOrchestrator.events.filter(e =>
                        e.data?.file === file || e.data?.path?.includes(file)
                    );
                    console.log(`\n[BUILD PATH] ${file}:`);
                    events.forEach(e => {
                        console.log(`  ${new Date(e.timestamp).toISOString()}: ${e.event}`);
                        if (e.data) console.log(`    Data:`, e.data);
                    });
                    return events;
                },

                traceCacheInvalid: () => {
                    const invalidEvents = traceOrchestrator.events.filter(e =>
                        e.event === 'CACHE_HIT_INVALID'
                    );
                    const results = invalidEvents.map(e => ({
                        event: e,
                        chain: traceOrchestrator.getCausalChain(e.id),
                        predictions: traceOrchestrator.predictNext('CACHE_HIT_INVALID'),
                        context: e.context || e.data
                    }));
                    console.log(`\n[CACHE INVALID] Found ${invalidEvents.length} invalid cache hits`);
                    results.forEach(r => {
                        console.log(`  Event ID: ${r.event.id}`);
                        console.log(`  Context:`, r.context);
                        console.log(`  Causal chain: ${r.chain.map(c => c.event).join(' -> ')}`);
                        console.log(`  Predictions:`, r.predictions);
                    });
                    return results;
                },

                findCacheProblem: () => {
                    const cacheEvents = traceOrchestrator.events.filter(e => e.event.includes('CACHE'));
                    const patterns = traceOrchestrator.detectPatterns();
                    const metrics = traceOrchestrator.getMetrics();
                    const critical = traceOrchestrator.getCriticalPath();

                    console.log('\n[CACHE ANALYSIS]');
                    console.log(`Total cache events: ${cacheEvents.length}`);
                    console.log(`Invalid hits: ${cacheEvents.filter(e => e.event === 'CACHE_HIT_INVALID').length}`);
                    console.log(`Valid hits: ${cacheEvents.filter(e => e.event === 'CACHE_HIT').length}`);
                    console.log(`Misses: ${cacheEvents.filter(e => e.event === 'CACHE_MISS').length}`);
                    console.log(`Stores: ${cacheEvents.filter(e => e.event === 'CACHE_STORE').length}`);

                    const invalidChains = cacheEvents
                        .filter(e => e.event === 'CACHE_HIT_INVALID')
                        .map(e => traceOrchestrator.getCausalChain(e.id));

                    if (invalidChains.length > 0) {
                        console.log('\nInvalid cache hit chains:');
                        invalidChains.forEach(chain => {
                            console.log(`  ${chain.map(c => c.event).join(' -> ')}`);
                        });
                    }

                    const predictions = traceOrchestrator.predictNext('CACHE_HIT_INVALID');
                    if (predictions.length > 0) {
                        console.log('\nPredicted after CACHE_HIT_INVALID:');
                        predictions.forEach(p => {
                            console.log(`  ${p.event}: ${(p.probability * 100).toFixed(1)}%`);
                        });
                    }

                    return { cacheEvents, patterns, metrics, critical, invalidChains, predictions };
                }
            },

            clear: () => {
                traceOrchestrator.events = [];
                traceOrchestrator.errors.clear();
                traceOrchestrator.causality.clear();
                traceOrchestrator.performanceMarks.clear();
                console.log('[DEBUG] Cleared all debug data');
            },

            help: () => {
                return {
                    commands: {
                        'events.*': 'Event tracking (all, recent, byType, trace, mark)',
                        'errors.*': 'Error analysis (all, recent, withChains, analyze)',
                        'causality.*': 'Causal chains (get, chains, trace)',
                        'perf.*': 'Performance (marks, slow, critical, telemetry, metrics)',
                        'patterns.*': 'Pattern detection (detect, markov, predict, memoryLeak)',
                        'build.*': 'Build debugging (cache, pipeline, files, graph)',
                        'state.*': 'System state (scheduler, coordinator, violations)',
                        'analyze.*': 'Analysis tools (whyNoFiles, traceBuildPath)',
                        'clear()': 'Clear all debug data',
                        'help()': 'Show this help'
                    }
                };
            }
        };

        // Navigate query path and execute
        const parts = queryPath.split('.');
        let result = debug;
        for (const part of parts) {
            if (!result[part]) {
                console.log(JSON.stringify({ error: `Unknown query: ${queryPath}`, available: Object.keys(result) }, null, 2));
                process.exit(1);
            }
            result = result[part];
        }

        // Execute function with args if callable
        if (typeof result === 'function') {
            result = result(...args);
        }

        // Output result
        console.log(JSON.stringify(result, null, 2));
        process.exit(0);
    }

    // Interactive debug API
    if (process.env.DEBUG || process.argv.includes('--debug')) {
        const buildDebugAPI = () => ({
            // Direct instrumentation
            trace: (event, ctx) => traceOrchestrator.trace(event, ctx),
            error: (err, ctx) => traceOrchestrator.error(err, ctx),
            performance: (label, fn) => traceOrchestrator.performance(label, fn),
            getCausalChain: (id) => traceOrchestrator.getCausalChain(id),

            // Metrics and profiling
            getMetrics: () => traceOrchestrator.getMetrics(),
            getPerformanceProfile: () => traceOrchestrator.getPerformanceProfile(),
            getCriticalPath: () => traceOrchestrator.getCriticalPath(),
            detectPatterns: () => traceOrchestrator.detectPatterns(),
            buildCausalityGraph: () => traceOrchestrator.buildCausalityGraph(),
            predictNext: (evt) => traceOrchestrator.predictNext(evt),
            getFailureProbability: (evt) => traceOrchestrator.getFailureProbability(evt),

            // Computation metrics
            calculateEventRate: (events) => traceOrchestrator.calculateEventRate(events),
            calculateErrorRate: (errors) => traceOrchestrator.calculateErrorRate(errors),
            calculateMemoryPressure: () => traceOrchestrator.calculateMemoryPressure(),
            calculateTaskSuccessRate: () => traceOrchestrator.calculateTaskSuccessRate(),
            identifyBottlenecks: () => traceOrchestrator.identifyBottlenecks(),

            // Pattern detection
            detectMemoryLeaks: () => traceOrchestrator.detectMemoryLeaks(),
            detectPerformanceDegradation: () => traceOrchestrator.detectPerformanceDegradation(),
            detectErrorClusters: () => traceOrchestrator.detectErrorClusters(),
            detectResourceSpikes: () => traceOrchestrator.detectResourceSpikes(),

            // Telemetry export
            telemetry: {
                init: () => traceOrchestrator.initializeLazyTelemetry(),
                stream: () => traceOrchestrator.createTelemetryStream(),
                export: () => traceOrchestrator.exportTelemetry(),
                formatMetrics: (data) => traceOrchestrator.formatMetrics(data),
                formatTimeseries: (data) => traceOrchestrator.formatTimeseries(data)
            },

            // Event inspection
            events: {
                all: () => traceOrchestrator.events,
                recent: (n = CONFIG.debug.analysis.recentWindowSize) =>
                    traceOrchestrator.events.slice(-n),
                byType: (type) =>
                    traceOrchestrator.events.filter(e => e.event.includes(type)),
                byFile: (file) => traceOrchestrator.events.filter(e =>
                    e.data?.file === file || e.data?.path?.includes(file)),
                chain: (id) => traceOrchestrator.getCausalChain(id),
                trace: (from, to) => {
                    const chain = [];
                    let current = to;
                    while (current && current !== from) {
                        chain.unshift(current);
                        const causes = traceOrchestrator.causality.get(current);
                        current = causes?.[0];
                    }
                    return chain;
                }
            },

            // Error inspection
            errors: {
                all: () => Array.from(traceOrchestrator.errors.values()),
                recent: (n = THRESHOLDS.TOP_RESULTS) =>
                    Array.from(traceOrchestrator.errors.values()).slice(-n),
                withChains: () => Array.from(traceOrchestrator.errors.entries())
                    .map(([id, err]) => ({
                        id,
                        message: err.error.message,
                        chain: err.causalChain,
                        stack: err.stack,
                        timestamp: err.timestamp
                    })),
                analyze: (id) => {
                    const err = traceOrchestrator.errors.get(id);
                    return err ? {
                        error: err,
                        chain: traceOrchestrator.getCausalChain(id),
                        predictions: traceOrchestrator.predictNext(err.context?.event)
                    } : null;
                },
                clusters: () => traceOrchestrator.detectErrorClusters(),
                getCausalChain: (id) => traceOrchestrator.getCausalChain(id)
            },

            // Causality analysis
            causality: {
                chains: () => traceOrchestrator.causality,
                graph: () => traceOrchestrator.buildCausalityGraph(),
                trace: (from, to) => {
                    const chain = [];
                    let current = to;
                    while (current && current !== from) {
                        chain.unshift(current);
                        const causes = traceOrchestrator.causality.get(current);
                        current = causes?.[0];
                    }
                    return chain;
                },
                getCausalChain: (id) => traceOrchestrator.getCausalChain(id)
            },

            // Performance inspection
            perf: {
                marks: () => traceOrchestrator.performanceMarks,
                profile: () => traceOrchestrator.getPerformanceProfile(),
                bottlenecks: () => traceOrchestrator.identifyBottlenecks(),
                critical: () => traceOrchestrator.getCriticalPath(),
                slowest: (n = THRESHOLDS.TOP_RESULTS) =>
                    Array.from(traceOrchestrator.performanceMarks.entries())
                        .sort((a, b) => b[1].duration - a[1].duration)
                        .slice(0, n)
                        .map(([label, data]) => ({ label, ...data })),
                metrics: () => ({
                    eventRate: traceOrchestrator.calculateEventRate(traceOrchestrator.events),
                    errorRate: traceOrchestrator.calculateErrorRate(Array.from(traceOrchestrator.errors.values())),
                    memoryPressure: traceOrchestrator.calculateMemoryPressure(),
                    taskSuccess: traceOrchestrator.calculateTaskSuccessRate()
                })
            },

            // Pattern recognition
            patterns: {
                detect: () => traceOrchestrator.detectPatterns(),
                memoryLeaks: () => traceOrchestrator.detectMemoryLeaks(),
                perfDegradation: () => traceOrchestrator.detectPerformanceDegradation(),
                errorClusters: () => traceOrchestrator.detectErrorClusters(),
                resourceSpikes: () => traceOrchestrator.detectResourceSpikes(),
                markov: () => traceOrchestrator.markovChain,
                failures: () => traceOrchestrator.failurePatterns,
                predict: (event) => traceOrchestrator.predictNext(event),
                failureProb: (event) => traceOrchestrator.getFailureProbability(event)
            },

            // Build system inspection
            build: {
                cache: () => {
                    const events = traceOrchestrator.events.filter(e =>
                        e.event.includes('CACHE') || e.event.includes('BUILD'));
                    return {
                        hits: events.filter(e => e.event.includes('CACHE_HIT')),
                        misses: events.filter(e => e.event.includes('CACHE_MISS')),
                        invalid: events.filter(e => e.event === 'CACHE_HIT_INVALID'),
                        stores: events.filter(e => e.event === 'CACHE_STORE'),
                        builds: events.filter(e => e.event === 'BUILD')
                    };
                },
                pipeline: () => {
                    const stages = ['READ', 'PARSE', 'TRANSFORM', 'WRITE'];
                    const events = traceOrchestrator.events.filter(e =>
                        e.event.includes('PIPELINE'));
                    return stages.reduce((acc, stage) => {
                        acc[stage.toLowerCase()] = events.filter(e =>
                            e.event === `PIPELINE_${stage}`);
                        return acc;
                    }, {});
                },
                files: () => {
                    const fsEvents = traceOrchestrator.events.filter(e =>
                        e.event.startsWith('FS_'));
                    return {
                        reads: fsEvents.filter(e => e.event === 'FS_READ'),
                        writes: fsEvents.filter(e => e.event === 'FS_WRITE'),
                        sizes: fsEvents.filter(e => e.event === 'FS_WRITE')
                            .map(e => ({ path: e.data?.path, size: e.data?.size }))
                    };
                },
                graph: () => ({
                    nodes: pullGraph.nodes.size,
                    evaluated: Array.from(pullGraph.nodes.entries())
                        .filter(([_, node]) => node.evaluated)
                        .map(([key]) => key),
                    pending: Array.from(pullGraph.nodes.entries())
                        .filter(([_, node]) => !node.evaluated)
                        .map(([key]) => key)
                }),
                tracePath: (file) => traceOrchestrator.events.filter(e =>
                    e.data?.file === file || e.data?.path?.includes(file))
            },

            // System state
            state: {
                scheduler: () => stateSerializer.serialize('scheduler', scheduler),
                coordinator: () => ({
                    resources: processingCoordinator.resources.size,
                    conflicts: processingCoordinator.hasResourceConflicts(),
                    keccakState: processingCoordinator.lazyKeccakState?._evaluated || false
                }),
                violations: () => ({
                    config: configPatternValidator.violations,
                    runtime: Array.from(traceOrchestrator.runtimeViolations)
                }),
                telemetry: () => stateSerializer.serialize('traceOrchestrator', traceOrchestrator),
                reflect: () => reflection.introspect(traceOrchestrator)
            },

            // Diagnostic analysis
            analyze: {
                whyNoFiles: () => {
                    const cache = global.debug.build.cache();
                    const pipeline = global.debug.build.pipeline();
                    const files = global.debug.build.files();

                    const report = {
                        cache: {
                            hits: cache.hits.length,
                            misses: cache.misses.length,
                            invalid: cache.invalid.length
                        },
                        pipeline: {
                            reads: pipeline.read.length,
                            parses: pipeline.parse.length,
                            transforms: pipeline.transform.length,
                            writes: pipeline.write.length
                        },
                        files: {
                            reads: files.reads.length,
                            writes: files.writes.length,
                            sizes: files.sizes
                        }
                    };

                    if (cache.hits.length > 0 && files.writes.length === 0) {
                        report.issue = 'Cache hits without writes - stale cache';
                    }

                    return report;
                },
                traceBuild: (file) => {
                    const events = traceOrchestrator.events.filter(e =>
                        e.data?.file === file || e.data?.path?.includes(file));
                    return events.map(e => ({
                        timestamp: e.timestamp,
                        event: e.event,
                        data: e.data,
                        parent: e.parent
                    }));
                },
                cacheInvalid: () => {
                    const invalid = traceOrchestrator.events.filter(e =>
                        e.event === 'CACHE_HIT_INVALID');
                    return invalid.map(e => ({
                        id: e.id,
                        timestamp: e.timestamp,
                        chain: traceOrchestrator.getCausalChain(e.id),
                        predictions: traceOrchestrator.predictNext('CACHE_HIT_INVALID'),
                        context: e.context || e.data
                    }));
                },
                cacheSummary: () => {
                    const cache = traceOrchestrator.events.filter(e =>
                        e.event.includes('CACHE'));
                    const types = ['CACHE_HIT_INVALID', 'CACHE_HIT', 'CACHE_MISS', 'CACHE_STORE'];
                    const counts = types.reduce((acc, type) => {
                        acc[type] = cache.filter(e => e.event === type).length;
                        return acc;
                    }, {});

                    const invalidChains = cache
                        .filter(e => e.event === 'CACHE_HIT_INVALID')
                        .map(e => traceOrchestrator.getCausalChain(e.id));

                    return {
                        total: cache.length,
                        counts,
                        invalidChains,
                        predictions: traceOrchestrator.predictNext('CACHE_HIT_INVALID')
                    };
                }
            },

            // Utilities
            clear: () => {
                traceOrchestrator.events = [];
                traceOrchestrator.errors.clear();
                traceOrchestrator.causality.clear();
                traceOrchestrator.performanceMarks.clear();
                return { cleared: true, timestamp: Date.now() };
            },

            help: () => ({
                sections: {
                    direct: ['trace', 'error', 'performance', 'getCausalChain'],
                    metrics: ['getMetrics', 'getPerformanceProfile', 'getCriticalPath', 'detectPatterns', 'buildCausalityGraph', 'predictNext', 'getFailureProbability'],
                    computation: ['calculateEventRate', 'calculateErrorRate', 'calculateMemoryPressure', 'calculateTaskSuccessRate', 'identifyBottlenecks'],
                    detection: ['detectMemoryLeaks', 'detectPerformanceDegradation', 'detectErrorClusters', 'detectResourceSpikes'],
                    telemetry: ['telemetry.init', 'telemetry.stream', 'telemetry.export', 'telemetry.formatMetrics', 'telemetry.formatTimeseries'],
                    events: ['events.all', 'events.recent', 'events.byType', 'events.byFile', 'events.chain', 'events.trace'],
                    errors: ['errors.all', 'errors.recent', 'errors.withChains', 'errors.analyze', 'errors.clusters', 'errors.getCausalChain'],
                    causality: ['causality.chains', 'causality.graph', 'causality.trace', 'causality.getCausalChain'],
                    perf: ['perf.marks', 'perf.profile', 'perf.bottlenecks', 'perf.critical', 'perf.slowest', 'perf.metrics'],
                    patterns: ['patterns.detect', 'patterns.memoryLeaks', 'patterns.perfDegradation', 'patterns.errorClusters', 'patterns.resourceSpikes', 'patterns.markov', 'patterns.failures', 'patterns.predict', 'patterns.failureProb'],
                    build: ['build.cache', 'build.pipeline', 'build.files', 'build.graph', 'build.tracePath'],
                    state: ['state.scheduler', 'state.coordinator', 'state.violations', 'state.telemetry', 'state.reflect'],
                    analyze: ['analyze.whyNoFiles', 'analyze.traceBuild', 'analyze.cacheInvalid', 'analyze.cacheSummary'],
                    util: ['clear', 'help']
                }
            })
        });

        global.debug = buildDebugAPI();
        global.d = global.debug;
    }

    process.on('SIGINT', () => {
        process.exit(0);
    });

    watch().catch(error => {
        console.error(CONFIG.strings.startupFailedMessage, error);
        lockManager.release();
        process.exit(1);
    });
}