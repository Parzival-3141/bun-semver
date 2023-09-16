const std = @import("std");
const mem = std.mem;

const debub = false;
const dbprint = if (debub) std.debug.print else nop;

fn nop(fmt: []const u8, args: anytype) void {
    _ = args;
    _ = fmt;
}

// const version_str = ">=1.2.9 <2.0.0 ^v1.x * || ~0.2.3 1.2.3-alpha.3||>=v1.0.0-beta.1.4+b9 1.2.3 - v2.3";
// const version_str = ">=1.2.9 <2.0.0 v1.x * || ~0.2.3 1.2.3 >=v1.0.0||1.2.3 - v2.3 || ~0.0.1 ~1.2 ~3.*.1 ~*";
const version_str = "~5.0.0";
// const version_str = "1 || 2 || pre-3 || 3";
// const version_str = "";

pub fn main() !void {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();

    for (0..10) |_| {
        var timer = try std.time.Timer.start();
        const now = timer.read();

        const range = try parse(arena.allocator(), version_str);
        defer range.deinit();

        std.log.debug("time: {d:.5}ms", .{@as(f32, @floatFromInt(timer.read() - now)) / @as(f32, @floatFromInt(std.time.ns_per_ms))});
    }

    // dbprint("\nRange (set#: Comparators)\n", .{});
    // for (range.sets, 0..) |set, i| {
    //     dbprint("{d}:", .{i});
    //     for (set) |cmp| {
    //         dbprint(" {} ", .{cmp});
    //     }
    //     dbprint("\n", .{});
    // }
}

// TODO: Reduce size of tokens
const Token = struct {
    tag: Tag,
    loc: Loc,

    pub const Loc = struct {
        start: usize,
        end: usize,
    };

    pub fn getValue(t: Token, src: []const u8) []const u8 {
        return src[t.loc.start..t.loc.end];
    }

    pub const Tag = enum(u8) {
        invalid,
        eof,

        // Operators
        equal,
        greater_than,
        greater_than_equal,
        less_than,
        less_than_equal,

        // Range Macros
        tilde,
        caret,
        hyphen_range,

        semver,
        partial_semver,
        pre_release,

        // these are logical operations, which evaluate operands lazily
        comparator_and,
        comparator_or,
    };
};

const Tokenizer = struct {
    src: [:0]const u8,
    idx: usize,

    pub fn init(input: [:0]const u8) Tokenizer {
        return .{ .src = input, .idx = 0 };
    }

    const State = enum {
        start,
        semver_num_start,
        semver_num,
        semver_num_end,

        angle_bracket_left,
        angle_bracket_right,

        whitespace,
        hyphen_range,
        hyphen_range_end,
        comparator_or,
        comparator_or_end,

        pre_release_start,
        pre_release,
    };

    pub fn next(t: *Tokenizer) Token {
        var state = State.start;
        var result = Token{
            .tag = .eof,
            .loc = .{
                .start = t.idx,
                .end = undefined,
            },
        };

        var semver_position: u3 = 1; // track which "major.minor.patch" we're in. (1-3)
        var increment = true;
        while (true) : ({
            if (increment) t.idx += 1;
        }) {
            increment = true;
            const c = t.src[t.idx];
            switch (state) {
                .start => switch (c) {
                    // End
                    0 => {
                        if (t.idx != t.src.len) {
                            result.tag = .invalid;
                            result.loc.start = t.idx;
                            t.idx += 1;
                            result.loc.end = t.idx;
                            return result;
                        } else break;
                    },
                    // Comparator AND, ComparatorSet OR, or beginning of HyphenRange
                    ' ' => {
                        result.tag = .comparator_and;
                        state = .whitespace;
                    },
                    '|' => {
                        result.tag = .comparator_or;
                        state = .comparator_or;
                    },

                    // SemVer
                    'v' => {
                        state = .semver_num_start;
                        result.tag = .semver;
                        result.loc.start += 1;
                    },
                    'x', 'X', '*' => {
                        state = .semver_num_end;
                        result.tag = .partial_semver;
                    },
                    '0'...'9' => {
                        state = .semver_num_start;
                        result.tag = .semver;
                        increment = false; // switch state without incrementing idx
                    },

                    // Operators
                    '>' => state = .angle_bracket_right,
                    '<' => state = .angle_bracket_left,
                    '=' => {
                        result.tag = .equal;
                        t.idx += 1;
                        break;
                    },
                    '^' => {
                        result.tag = .caret;
                        t.idx += 1;
                        break;
                    },
                    '~' => {
                        result.tag = .tilde;
                        t.idx += 1;
                        break;
                    },

                    // PreRelease
                    '-', '+' => {
                        state = .pre_release_start;
                    },

                    else => {
                        result.tag = .invalid;
                        t.idx += 1;
                        result.loc.end = t.idx;
                        return result;
                    },
                },
                .semver_num_start => switch (c) {
                    'x', 'X', '*' => {
                        state = .semver_num_end;
                        result.tag = .partial_semver;
                    },

                    '0' => state = .semver_num_end,
                    '1'...'9' => state = .semver_num,

                    else => {
                        result.tag = .invalid;
                        result.loc.end = t.idx;
                        t.idx += 1;
                        return result;
                    },
                },
                .semver_num => switch (c) {
                    '0'...'9' => {},
                    else => {
                        state = .semver_num_end;
                        increment = false; // switch state without incrementing idx
                    },
                },
                .semver_num_end => {
                    if (semver_position == 3) break;

                    semver_position += 1;

                    if (c == '.') {
                        state = .semver_num_start;
                    } else {
                        result.tag = .partial_semver;
                        break;
                    }
                },

                .angle_bracket_left => {
                    if (c == '=') {
                        result.tag = .less_than_equal;
                        t.idx += 1;
                    } else result.tag = .less_than;
                    break;
                },
                .angle_bracket_right => {
                    if (c == '=') {
                        result.tag = .greater_than_equal;
                        t.idx += 1;
                    } else result.tag = .greater_than;
                    break;
                },
                .whitespace => switch (c) {
                    ' ' => {},
                    '-' => {
                        state = .hyphen_range;
                    },
                    '|' => {
                        state = .comparator_or;
                        result.tag = .comparator_or;
                    },
                    else => break,
                },
                .hyphen_range => switch (c) {
                    ' ' => {
                        state = .hyphen_range_end;
                        result.tag = .hyphen_range;
                    },
                    else => {
                        result.tag = .invalid;
                        t.idx += 1;
                        result.loc.end = t.idx;
                        return result;
                    },
                },
                .hyphen_range_end => switch (c) {
                    ' ' => {},
                    else => break,
                },
                .comparator_or => switch (c) {
                    '|' => state = .comparator_or_end,
                    else => {
                        result.tag = .invalid;
                        t.idx += 1;
                        result.loc.end = t.idx;
                        return result;
                    },
                },
                .comparator_or_end => switch (c) {
                    ' ' => {},
                    else => break,
                },
                .pre_release_start => switch (c) {
                    '0'...'9',
                    'A'...'Z',
                    'a'...'z',
                    => {
                        state = .pre_release;
                        result.tag = .pre_release;
                    },
                    else => {
                        result.tag = .invalid;
                        t.idx += 1;
                        result.loc.end = t.idx;
                        return result;
                    },
                },
                .pre_release => switch (c) {
                    // The grammar is to complex to parse here, so just tokenize
                    // all valid characters.
                    '-',
                    '+',
                    '0'...'9',
                    'A'...'Z',
                    'a'...'z',
                    '.',
                    => {},
                    else => break,
                },
            }
        }

        if (result.tag == .eof) result.loc.start = t.idx;
        result.loc.end = t.idx;
        return result;
    }
};

/// Caller owns the returned `Range`.
fn parse(allocator: mem.Allocator, input: [:0]const u8) error{ OutOfMemory, ParseError }!Range {
    // Source bytes to Tokens ratio: 3.240000009536743 for version_str
    // However most dependencies don't make extensive use of ranges, and are usually just one Semver and Operation.
    // Round this down to 3 or even 2.
    // Could pre-allocate a list of tokens for reuse throughout the entire file, instead of per parse.
    const estimated_token_count = input.len / 3;
    var tokens = try std.ArrayList(Token).initCapacity(allocator, estimated_token_count);
    defer tokens.deinit();

    var tokenizer = Tokenizer.init(input);
    dbprint("Tokens:\n", .{});
    while (true) {
        const token = tokenizer.next();
        try tokens.append(token);
        dbprint(
            "{s: ^20}: '{s}'\n",
            .{ @tagName(token.tag), token.getValue(input) },
        );
        if (token.tag == .eof) break;
    }
    dbprint(
        "\nSource bytes to Tokens ratio: {d}\n",
        .{@as(f32, @floatFromInt(input.len)) / @as(f32, @floatFromInt(tokens.items.len - 1))},
    );

    var parser = Parser{
        .allocator = allocator,
        .src = input,
        .tokens = tokens.items,
        .set_lens = try std.ArrayList(usize).initCapacity(allocator, 1),
        .comparators = try std.ArrayList(Comparator).initCapacity(allocator, 2),
    };
    defer parser.set_lens.deinit();
    defer parser.comparators.deinit();

    try parser.parseRange();

    return Range.init(
        allocator,
        try parser.set_lens.toOwnedSlice(),
        try parser.comparators.toOwnedSlice(),
    );
}

pub const Range = struct {
    allocator: mem.Allocator,
    /// Contains each ComparatorSet
    sets: [][]const Comparator,
    /// Tracks the length of the underlying Comparator buffer. Shouldn't be changed after init.
    total_cmps: usize,

    pub fn init(
        /// Must be the allocator used to allocate `set_lens` and `cmp_buf`
        allocator: mem.Allocator,
        set_lens: []usize,
        cmp_buf: []const Comparator,
    ) mem.Allocator.Error!Range {
        var setlist: [][]const Comparator = try allocator.alloc([]const Comparator, set_lens.len);

        var cursor: usize = 0;
        for (setlist, 0..) |*set, i| {
            const len = set_lens[i];
            set.* = cmp_buf[cursor..][0..len];
            cursor += len;
        }

        allocator.free(set_lens);

        return Range{ .allocator = allocator, .sets = setlist, .total_cmps = cmp_buf.len };
    }

    pub fn deinit(r: Range) void {
        // Free underlying Comparator buffer
        const cmp_buf: [*]const Comparator = @ptrCast(&r.sets[0][0]);
        r.allocator.free(cmp_buf[0..r.total_cmps]);

        r.allocator.free(r.sets);
    }
};

const Parser = struct {
    allocator: mem.Allocator,
    src: []const u8,
    tokens: []const Token,
    tok_idx: usize = 0,
    /// Each element represents a set, and it's value is the amount of Comparators
    /// the set contains.
    set_lens: std.ArrayList(usize),
    comparators: std.ArrayList(Comparator),

    /// Range <- ComparatorSet (OR ComparatorSet)*
    /// OR <- (' ')* '||' (' ')*
    pub fn parseRange(p: *Parser) !void {
        // skip leading whitespace
        while (p.matchToken(.comparator_and)) |_| {}

        p.set_lens.appendAssumeCapacity(0);
        try p.parseComparatorSet();

        while (true) {
            if (p.matchToken(.comparator_or)) |_| {
                try p.nextComparatorSet();
                try p.parseComparatorSet();
            } else break;
        }

        // skip trailing whitespace
        while (p.matchToken(.comparator_and)) |_| {}
        _ = try p.expectToken(.eof);
    }

    /// ComparatorSet <- (SemVer ' - ' SemVer) / Comparator (' ' Comparator)*
    fn parseComparatorSet(p: *Parser) !void {
        const peek = p.peekToken().tag;
        if (peek == .semver or peek == .partial_semver) {
            const ahead = p.peekTokenAhead(1);
            if (ahead != null and ahead.?.tag == .hyphen_range) {
                return try p.expectHyphenRange();
            }
        }

        try p.parseComparator();
        while (true) {
            if (p.matchToken(.comparator_and)) |_| {
                try p.parseComparator();
            } else break;
        }
    }

    /// Comparator <- (Operator / `~` / '^')? SemVer
    /// Operator <- '>=' / '>' / '<=' / '<' / '='
    fn parseComparator(p: *Parser) !void {
        if (p.matchOperatorToken()) |op| {
            return try p.expectEitherVersion(Comparator.Operator.fromToken(op));
        }
        if (p.matchToken(.tilde)) |_| {
            return p.parseTildeMacro();
        }
        if (p.matchToken(.caret)) |_| {
            return p.parseCaretMacro();
        }

        try p.expectEitherVersion(null);
    }

    fn expectHyphenRange(p: *Parser) !void {
        // A HyphenRange is an inclusive set of two versions.
        // If the first version is a PartialVersion, then the missing pieces are replaced with zeroes.
        // (e.g. 1.2 - 2.3.4 := >=1.2.0 <=2.3.4)
        // If the second version is a PartialVersion, and the leftmost values aren't Wildcards, then
        // the generated Comparator must exclude everything greater than the leftmost non-Wildcard values.
        // Otherwise we match anything >= the first version (TODO: error instead?).
        // E.g.
        // 1.2.3 - 2.3 := >=1.2.3 <2.4.0-0
        // 1.2.3 - 2 := >=1.2.3 <3.0.0-0
        // 1.2.3 - *.2 := >=1.2.3
        // HyphenRange <- version ' - ' version

        // a.b.c - x.y.z := >=a.b.c <=x.y.z

        // a.b.* - x.y.z := >=a.b.0 <=x.y.z
        // a.*.* - x.y.z := >=a.0.0 <=x.y.z
        // *.*.* - x.y.z := <=x.y.z

        // a.b.c - x.y.* := >=a.b.c <x.(y+1).0
        // a.b.c - x.*.* := >=a.b.c <(x+1).0.0
        // a.b.c - *.*.* := >=a.b.c

        // *.*.* - *.*.* := >=0.0.0

        const lhs: ?SemanticVersion = blk: {
            if (p.peekToken().tag == .semver)
                break :blk try p.expectSemanticVersion();

            const partial = try p.expectPartialVersion();
            break :blk if (partial.major == null) null else partial.toSemVer();
        };

        _ = try p.expectToken(.hyphen_range);

        var rhs_has_wildcard = false;
        const rhs: ?SemanticVersion = blk: {
            if (p.peekToken().tag == .semver)
                break :blk try p.expectSemanticVersion();

            const partial = try p.expectPartialVersion();
            if (partial.major == null) break :blk null;

            var semver = partial.toSemVer();
            if (partial.minor == null) {
                semver.major += 1;
                rhs_has_wildcard = true;
            } else if (partial.patch == null) {
                semver.minor += 1;
                rhs_has_wildcard = true;
            }

            break :blk semver;
        };

        if (lhs == null and rhs == null) {
            // match anything
            return try p.addComparator(.{ .op = .gte, .semver = .{ .major = 0, .minor = 0, .patch = 0 } });
        }

        if (lhs) |l| {
            try p.addComparator(.{ .op = .gte, .semver = l });
        }

        if (rhs) |r| {
            try p.addComparator(.{ .op = if (rhs_has_wildcard) .lt else .lte, .semver = r });
        }
    }

    fn parseTildeMacro(p: *Parser) !void {
        // Tilde Ranges ~1.2.3 ~1.2 ~1
        // Allows patch-level changes if a minor version is specified on the comparator.
        // Allows minor-level changes if not.

        // ~a.b.c        := >=a.b.c <a.(b+1).0
        // ~a.b.*        := >=a.b.0 <a.(b+1).0 // same as a.b.*
        // ~a.*.*        := >=a.0.0 <(a+1).0.0 // same as a.*.*
        // ~a.b.c-beta-2 := >=a.b.c-beta-2 <a.(b+1).0

        // Note that prereleases in the 1.2.3 version will be allowed, if they are greater than
        // or equal to beta.2. So, 1.2.3-beta.4 would be allowed, but 1.2.4-beta.2 would not,
        // because it is a prerelease of a different [major, minor, patch] tuple.

        var has_minor = false;

        const lh_semver = if (p.peekToken().tag == .semver) blk: {
            has_minor = true;
            break :blk try p.expectSemanticVersion();
        } else blk: {
            const partial = try p.expectPartialVersion();
            if (partial.major == null) {
                // all Wildcards, accept any version
                return try p.addComparator(.{ .op = .gte, .semver = partial.toSemVer() });
            }
            has_minor = partial.minor != null;
            break :blk partial.toSemVer();
        };

        var rh_semver = lh_semver;

        if (!has_minor)
            rh_semver.major += 1
        else
            rh_semver.minor += 1;

        rh_semver.patch = 0;

        // TODO: handle prereleases
        // if (partial.patch != null and partial.pre_release != null) {
        //     try p.addComparator(.{ .op = .gte, .semver = lh_semver });
        //     rh_semver.pre_release.pre = null;
        //     rh_semver.pre_release.build = null;
        //     try p.addComparator(.{ .op = .lt, .semver = rh_semver });
        //     return;
        // }

        try p.addComparator(.{ .op = .gte, .semver = lh_semver });
        try p.addComparator(.{ .op = .lt, .semver = rh_semver });
    }

    fn parseCaretMacro(p: *Parser) !void {
        // Caret Ranges ^1.2.3 ^0.2.5 ^0.0.4
        // Allows changes that do not modify the left-most non-zero element in the
        // [major, minor, patch] tuple. In other words, this allows patch and minor updates for
        // versions 1.0.0 and above, patch updates for versions 0.X >=0.1.0, and no updates for versions 0.0.X.

        // Many authors treat a 0.x version as if the x were the major "breaking-change" indicator.

        // Caret ranges are ideal when an author may make breaking changes between 0.2.4 and 0.3.0
        // releases, which is a common practice. However, it presumes that there will not be
        // breaking changes between 0.2.4 and 0.2.5. It allows for changes that are presumed to be
        // additive (but non-breaking), according to commonly observed practices.

        // ^1.2.3 := >=1.2.3 <2.0.0-0
        // ^0.2.3 := >=0.2.3 <0.3.0-0
        // ^0.0.3 := >=0.0.3 <0.0.4-0
        // ^1.2.3-beta.2 := >=1.2.3-beta.2 <2.0.0-0 Note that prereleases in the 1.2.3 version will be allowed, if they are greater than or equal to beta.2. So, 1.2.3-beta.4 would be allowed, but 1.2.4-beta.2 would not, because it is a prerelease of a different [major, minor, patch] tuple.
        // ^0.0.3-beta := >=0.0.3-beta <0.0.4-0 Note that prereleases in the 0.0.3 version only will be allowed, if they are greater than or equal to beta. So, 0.0.3-pr.2 would be allowed.

        // When parsing caret ranges, a missing patch value desugars to the number 0, but will allow flexibility within that value, even if the major and minor versions are both 0.
        // ^1.2.x := >=1.2.0 <2.0.0-0
        // ^0.0.x := >=0.0.0 <0.1.0-0
        // ^0.0 := >=0.0.0 <0.1.0-0

        // A missing minor and patch values will desugar to zero, but also allow flexibility within those values, even if the major version is zero.
        // ^1.x := >=1.0.0 <2.0.0-0
        // ^0.x := >=0.0.0 <1.0.0-0

        // --------------------------------------------
        // ^a.b.c := >=a.b.c <(a+1).0.0
        // ^0.b.c := >=0.b.c <0.(b+1).0
        // ^0.0.c := >=0.0.c <0.0.(c+1)

        // ^a.b.c-beta.2 := >=a.b.c-beta.2 <(a+1).0.0
        // ^0.0.c-beta   := >=0.0.c-beta <0.0.(c+1)

        // ^a.b.* := >=a.b.0 <(a+1).0.0
        // ^a.*.* := >=a.0.0 <(a+1).0.0
        // ^0.0.* := >=0.0.0 <0.1.0
        // ^0.*.* := >=0.0.0 <0.1.0

        // ^a.*.* := >=a.0.0 <(a+1).0.0
        // ^a.0.* := >=a.0.0 <(a+1).0.0
        // ^a.b.* := >=a.b.0 <(a+1).b.0
        // ^a.b.c := >=a.b.0 <(a+1).b.c
        // ^0.0.c := >=0.0.c <0.0.(c+1)
        // ^0.b.0 := >=0.b.0 <0.(b+1).0

        // leftmost non-zero
        // wildcards resolve to 0
        // if a wildcard is the leftmost non-zero, treat the zero to it's left as the upper bound

        // Allows changes that do not modify the left-most non-zero element in the [major, minor, patch] tuple
        if (p.peekToken().tag == .semver) {
            // p.expectSemanticVersion();
        }

        @panic("TODO");
    }

    pub fn parseRange1(p: *Parser) !void {
        p.set_lens.appendAssumeCapacity(0);
        // p.expectComparatorSet();
        // while (p.tokens[p.tok_idx].tag == .comparator_or) {
        //     p.expectComparatorSet();
        // }

        while (true) {
            switch (p.peekToken().tag) {
                .semver => {
                    var semver = try p.expectSemanticVersion();
                    if (p.peekToken().tag == .pre_release) {
                        const pr = p.nextToken();
                        semver.pre_release.pre = pr.getValue(p.src); // TODO: actually parse this
                    }
                    try p.addComparator(.{ .op = .eql, .semver = semver });
                },
                .partial_semver => try p.parsePartialVersion(null), // TODO: pass in op

                // .greater_than,
                // .greater_than_equal,
                // .less_than,
                // .less_than_equal,
                // .equal,
                // => {
                //     _ = p.nextToken();
                // },
                .comparator_and => _ = p.nextToken(), // expect Comparator
                .eof => break,
                else => |t| std.debug.panic("TODO: parse token {s}\n", .{@tagName(t)}),
            }
        }
    }

    /// Will parse either a SemanticVersion or PartialVersion,
    /// adding Comparators immediately.
    fn expectEitherVersion(p: *Parser, op: ?Comparator.Operator) !void {
        return switch (p.peekToken().tag) {
            .semver => try p.addComparator(.{
                .op = op orelse .eql,
                .semver = try p.expectSemanticVersion(),
            }),
            .partial_semver => try p.parsePartialVersion(
                try p.expectPartialVersion(),
                op,
            ),
            else => error.ParseError,
        };
    }

    fn expectSemanticVersion(p: *Parser) !SemanticVersion {
        const tok = try p.expectToken(.semver);

        const str = tok.getValue(p.src);
        var iter = std.mem.splitScalar(u8, str, '.');

        return SemanticVersion{
            .major = std.fmt.parseInt(u32, iter.first(), 10) catch return error.ParseError,
            // we know these aren't null because semver tokens are fully formed.
            .minor = std.fmt.parseInt(u32, iter.next().?, 10) catch return error.ParseError,
            .patch = std.fmt.parseInt(u32, iter.next().?, 10) catch return error.ParseError,
            .pre_release = .{},
        };
    }

    fn expectPartialVersion(p: *Parser) !PartialVersion {
        const tok = try p.expectToken(.partial_semver);
        var partial = PartialVersion{};

        var iter = std.mem.splitScalar(u8, tok.getValue(p.src), '.');
        var i: usize = 1;
        while (iter.next()) |value| : (i += 1) {
            if (std.mem.eql(u8, value, "*") or
                std.mem.eql(u8, value, "x") or
                std.mem.eql(u8, value, "X"))
                // TODO: Causes the remaining values to be Wildcards. I'm pretty sure this is
                // the intended behaviour, but it needs more testing. This fn requires a rewrite if not...
                break;
            // continue;

            const slot: *?u32 = switch (i) {
                1 => &partial.major,
                2 => &partial.minor,
                3 => &partial.patch,
                else => unreachable,
            };

            slot.* = std.fmt.parseInt(u32, value, 10) catch return error.ParseError;
        }

        return partial;
    }

    /// Parse partial with op, generating new Comparators
    fn parsePartialVersion(p: *Parser, partial: PartialVersion, operation: ?Comparator.Operator) !void {
        if (partial.major == null) {
            // all wildcards
            // removing the ": type" here causes a funky compile error.
            const pop: Comparator.Operator = if (operation) |op|
                switch (op) {
                    .lt, .gt => .lt,
                    else => .gte,
                }
            else
                .gte;
            try p.addComparator(.{ .op = pop, .semver = .{ .major = 0, .minor = 0, .patch = 0 } });
            return;
        }

        // TODO: See if these cases can be collapsed
        if (partial.minor == null) {
            // a.*.*
            // >  : >=(a+1).0.0
            // >= : >=a.0.0
            // <  : <a.0.0
            // <= : <(a+1).0.0
            // =  : >=a.0.0 <(a+1).0.0

            switch (operation orelse .eql) {
                .gt => try p.addComparator(.{ .op = .gte, .semver = .{ .major = partial.major.? + 1, .minor = 0, .patch = 0 } }),
                .gte => try p.addComparator(.{ .op = .gte, .semver = .{ .major = partial.major.?, .minor = 0, .patch = 0 } }),
                .lt => try p.addComparator(.{ .op = .lt, .semver = .{ .major = partial.major.?, .minor = 0, .patch = 0 } }),
                .lte => try p.addComparator(.{ .op = .lt, .semver = .{ .major = partial.major.? + 1, .minor = 0, .patch = 0 } }),
                .eql => {
                    try p.addComparator(.{ .op = .gte, .semver = .{ .major = partial.major.?, .minor = 0, .patch = 0 } });
                    try p.addComparator(.{ .op = .lt, .semver = .{ .major = partial.major.? + 1, .minor = 0, .patch = 0 } });
                },
            }

            return;
        }

        if (partial.patch == null) {
            // a.b.*
            // >  : >=a.(b+1).0
            // >= : >=a.b.0
            // <  : <a.b.0
            // <= : <a.(b+1).0
            // =  : >=a.b.0 <a.(b+1).0

            switch (operation orelse .eql) {
                .gt => try p.addComparator(.{ .op = .gte, .semver = .{ .major = partial.major.?, .minor = partial.minor.? + 1, .patch = 0 } }),
                .gte => try p.addComparator(.{ .op = .gte, .semver = .{ .major = partial.major.?, .minor = partial.minor.?, .patch = 0 } }),
                .lt => try p.addComparator(.{ .op = .lt, .semver = .{ .major = partial.major.?, .minor = partial.minor.?, .patch = 0 } }),
                .lte => try p.addComparator(.{ .op = .lt, .semver = .{ .major = partial.major.?, .minor = partial.minor.? + 1, .patch = 0 } }),
                .eql => {
                    try p.addComparator(.{ .op = .gte, .semver = .{ .major = partial.major.?, .minor = partial.minor.?, .patch = 0 } });
                    try p.addComparator(.{ .op = .lt, .semver = .{ .major = partial.major.?, .minor = partial.minor.? + 1, .patch = 0 } });
                },
            }

            return;
        }

        // If none of partial's fields are null, then it couldn't have been a partial in the first place!
        unreachable;
    }

    fn nextToken(p: *Parser) Token {
        const t = p.tokens[p.tok_idx];
        p.tok_idx += 1;
        return t;
    }

    fn peekToken(p: Parser) Token {
        return p.tokens[p.tok_idx];
    }

    fn peekTokenAhead(p: Parser, offset: usize) ?Token {
        return if (p.tok_idx + offset < p.tokens.len) p.tokens[p.tok_idx + offset] else null;
    }

    fn matchToken(p: *Parser, tag: Token.Tag) ?Token {
        return if (p.peekToken().tag == tag) p.nextToken() else null;
    }

    fn matchOperatorToken(p: *Parser) ?Token {
        return switch (p.peekToken().tag) {
            .equal,
            .less_than,
            .less_than_equal,
            .greater_than,
            .greater_than_equal,
            => p.nextToken(),
            else => null,
        };
    }

    fn expectToken(p: *Parser, tag: Token.Tag) !Token {
        return if (p.peekToken().tag == tag) p.nextToken() else error.ParseError;
    }

    fn addComparator(p: *Parser, cmp: Comparator) !void {
        p.set_lens.items[p.set_lens.items.len - 1] += 1;
        try p.comparators.append(cmp);
    }

    fn nextComparatorSet(p: *Parser) !void {
        try p.set_lens.append(0);
    }
};

// A Range is a set of one or more ComparatorSets, each seperated by an Or.
// Ranges specify the full set of valid versions. A given version must satisfy
// at least one ComparatorSet in the Range to satisfy the Range.
// Range <- ComparatorSet (Or ComparatorSet)*

// An Or is a logical OR, lazily evaluating it's operands.
// Or <- (' ')* '||' (' ')*

// A ComparatorSet is one or more Comparators, each seperated by an And.
// A given version must satisfy every Comparator in the set to satisfy the ComparatorSet.
// ComparatorSet <- Comparator (And Comparator)*

// An And is a logical AND, lazily evaluating it's operands.
// And <- ' '

// A Comparator in an Operator and a SemanticVersion. Operator defaults to '=' if one isn't defined.
// Comparator <- Operator SemanticVersion

// An Operator is a basic inequality operator (>, >=, <, <=). This includes `=`, although it's
// superfluous.
// Operator <- '>=' / '>' / '<=' / '<' / '='

// A SemanticVersion is a full Semantic Version according to the spec (https://semver.org).
// SemanticVersions can have a PreRelease.

// NPM defines Range Macros, which resolve to a ComparatorSet.
// They are HyphenRanges, TildeRanges, CaretRanges, and PartialVersions.
// See https://github.com/npm/node-semver/tree/main#advanced-range-syntax for definitions.
// Notes:
// PartialVersion is equivalent to NPM's X-Range.
// HyphenRanges will drop the upper bound if the second version starts with a Wildcard (TODO: error instead?).

// A HyphenRange is an inclusive set of two versions.
// If the first version is a PartialVersion, then the missing pieces are replaced with zeroes.
// (e.g. 1.2 - 2.3.4 := >=1.2.0 <=2.3.4)
// If the second version is a PartialVersion, and the leftmost values aren't Wildcards, then
// the generated Comparator must exclude everything greater than the leftmost non-Wildcard values.
// Otherwise we match anything >= the first version (TODO: error instead?).
// E.g.
// 1.2.3 - 2.3 := >=1.2.3 <2.4.0-0
// 1.2.3 - 2 := >=1.2.3 <3.0.0-0
// 1.2.3 - *.2 := >=1.2.3
// HyphenRange <- version ' - ' version

// A PartialVersion is a SemanticVersion that's incomplete or contains Wildcards.
// A Wildcard is a stand-in for a major/minor/patch value. It represents all
// possible values for the given major/minor/patch "slot".
// Wildcards cause all remaining slots to become Wildcards as well. E.g. 1.*.2 == 1.*.*
//
// An incomplete version is equivalent to one with Wildcards for the missing slots.
// E.g. 1.0 == 1.0.*

// const Range = []ComparatorSet;
// const ComparatorSet = []Comparator;

const Comparator = struct {
    op: Operator,
    semver: SemanticVersion,

    pub const Operator = enum {
        /// `=`
        eql,
        /// `<`
        lt,
        /// `<=`
        lte,
        /// `>=`
        gt,
        /// `>=`
        gte,

        pub fn fromToken(tok: Token) Operator {
            return switch (tok.tag) {
                .equal => .eql,
                .greater_than => .gt,
                .greater_than_equal => .gte,
                .less_than => .lt,
                .less_than_equal => .lte,
                else => unreachable,
            };
        }
    };

    pub fn format(value: Comparator, comptime fmt: []const u8, options: std.fmt.FormatOptions, writer: anytype) !void {
        _ = fmt;
        _ = options;

        const op_str = switch (value.op) {
            .eql => "",
            .lt => "<",
            .lte => "<=",
            .gt => ">",
            .gte => ">=",
        };

        try writer.print("{s}{}", .{ op_str, value.semver });
    }
};

const SemanticVersion = struct {
    major: u32,
    minor: u32,
    patch: u32,
    pre_release: PreRelease = .{},

    pub const PreRelease = struct {
        pre: ?[]const u8 = null,
        build: ?[]const u8 = null,
    };

    pub fn format(value: SemanticVersion, comptime fmt: []const u8, options: std.fmt.FormatOptions, writer: anytype) !void {
        _ = options;
        _ = fmt;

        try writer.print("{d}.{d}.{d}{s}{s}", .{
            value.major,
            value.minor,
            value.patch,
            value.pre_release.pre orelse "",
            value.pre_release.build orelse "",
        });
    }
};

const PartialVersion = struct {
    major: ?u32 = null,
    minor: ?u32 = null,
    patch: ?u32 = null,
    // pre_release: ?PreRelease,

    /// Check which fields are `null` against a pattern
    ///
    /// Example:
    /// ```zig
    /// const p = PartialVersion{.major = 1, .patch = 2};
    /// assert(p.match(true, false, true) == true);
    /// ```
    pub fn match(p: PartialVersion, major: bool, minor: bool, patch: bool) bool {
        return (major == (p.major != null)) and (minor == (p.minor != null)) and (patch == (p.patch != null));
    }

    /// `null` fields are converted to `0`
    pub fn toSemVer(p: PartialVersion) SemanticVersion {
        return SemanticVersion{
            .major = p.major orelse 0,
            .minor = p.minor orelse 0,
            .patch = p.patch orelse 0,
            .pre_release = .{},
        };
    }
};
