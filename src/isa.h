
#ifndef UBERSPEC_ISA_H
#define UBERSPEC_ISA_H

inline bool is_gpr_key(int k) { return (unsigned)k < (unsigned)RZ; }

struct Field { int off, base, w; char kind; };

struct TnShape {
    int form = 0;
    int ch = 0;
    int n = 0;
    int reg[4] = {RZ, RZ, RZ, RZ};
};

static const int FIELD_SLOTS = 8;

enum { RN_SPLIT = 1, RN_ALIGN = 2, RN_OVERLAP = 4, RN_ORDERS = 8, RN_REGS = 16, RN_CHECK = 32,
       RN_DEFS = 64 };

template <class I> struct ProgramT {
    typedef I Isa;
    typedef typename I::Word Word;
    typedef typename I::RSet RSet;

    std::vector<u8> bc, ct;
    u32 co = 0;
    const u8 *blob = nullptr;
    size_t blobsz = 0;

    int n = 0;
    std::vector<int> rel;
    std::vector<Word> q;
    std::vector<int16_t> op;
    std::vector<uint16_t> props;
    std::unordered_map<int, int> idx_of;

    std::vector<RSet> defs, maydefs, uses;

    void load_paths(const std::string &bcp, const std::string &ctp);
    void load_bytes(std::vector<u8> b, std::vector<u8> c);
    void build();

    const char *name(int i) const { return I::op_name(op[i]); }
    int snap(int addr) const;
    bool guarded(int i) const;
    bool never(int i) const;
    int target(int i) const;
    bool blob_u32(int byte_off, u32 *out) const;
    void du(int i, RSet &d, RSet &md, RSet &u) const;
    static void du_word(Word qq, int nm, unsigned pr, RSet &d, RSet &md, RSet &u) {
        I::du(qq, nm, pr, d, md, u);
    }
};

struct CFGraph {
    int n = 0;
    std::vector<int8_t> cat;
    std::vector<int> tgt;
    std::vector<char> grd, nev;
    std::vector<std::vector<int>> succ;
    std::vector<std::vector<int>> pred;
    std::vector<char> unknown;
    bool overflow = false;

    template <class P> void build(const P &p, bool seed_orphans) {
        P::Isa::build_cfg(p, seed_orphans, *this);
    }
    std::vector<char> reachable_from_entry() const;
};

#endif
