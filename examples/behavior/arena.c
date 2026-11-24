#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

enum { N = 4096, O = 16384, D = 64, RULES = 64 };
enum { MULTI = 1, BRIDGE = 2, ONE = 4 };
typedef uint32_t Id;
typedef struct { uint16_t rule, depth; Id primary, secondary; uint32_t flags; } Node;
_Static_assert(sizeof(Node) == 16, "provenance layout");
typedef struct {
    Node nodes[N];
    Id overflow[O];
    uint32_t used, words;
} Arena;
typedef struct {
    uint64_t mass[N], reward[RULES];
    uint32_t seen[N], depth_seen[D+1], generation;
    Id next[N], bucket[D+1];
    uint32_t unique, bridges;
} Scratch;

static void reset(Arena *a) {
    a->used = 1;
    a->words = 0;
}
static uint16_t depth(const Arena *a, Id x) {
    return x ? a->nodes[x].depth : 0;
}
/* Returns zero on refusal; existing descendants keep safe topological ranks. */
static Id derive(Arena *a, Id existing, uint16_t rule, const Id *parents,
                 uint32_t count, uint32_t is_bridge) {
    if (!count || count > O || rule == 0 || rule >= RULES ||
        existing >= a->used || (!existing && a->used == N))
        return 0;
    uint16_t d = 0;
    for (uint32_t i = 0; i < count; ++i) {
        if (parents[i] >= a->used) return 0;
        uint16_t p = depth(a, parents[i]);
        if (d < p) d = p;
    }
    if (d >= D || (existing && d + 1 >= depth(a, existing))) return 0;
    if (count > 2 && count > O - a->words) return 0;
    Id chosen = existing ? existing : a->used++;
    Node n = {rule, (uint16_t)(d + 1), parents[0], count == 2 ? parents[1] : 0,
              (is_bridge ? BRIDGE : 0) | (count == 1 ? ONE : 0)};
    if (count > 2) {
        n.flags |= MULTI;
        n.secondary = a->words;
        a->overflow[a->words++] = count-1;
        for (uint32_t i=1; i<count; ++i) a->overflow[a->words++] = parents[i];
    }
    a->nodes[chosen] = n;
    return chosen;
}
static void queue(Scratch *s, const Arena *a, Id id, uint64_t mass) {
    if (!id || !mass) return;
    assert(id < a->used);
    if (s->seen[id] == s->generation) {
        s->mass[id] += mass;
        return;
    }
    uint16_t d = depth(a,id);
    if (s->depth_seen[d] != s->generation) {
        s->bucket[d]=0;
        s->depth_seen[d]=s->generation;
    }
    s->seen[id]=s->generation;
    s->mass[id]=mass;
    s->next[id]=s->bucket[d];
    s->bucket[d]=id;
}
static void distribute(Scratch *s, const Arena *a, Id left, Id right, uint32_t reward) {
    if (++s->generation == 0) {
        memset(s->seen,0,sizeof s->seen);
        memset(s->depth_seen,0,sizeof s->depth_seen);
        s->generation=1;
    }
    s->unique = 0;
    s->bridges = 0;
    queue(s,a,left,reward/2);
    queue(s,a,right,reward-reward/2);
    for (uint16_t d=D; d; --d) if (s->depth_seen[d]==s->generation) {
        for (Id i=s->bucket[d]; i; i=s->next[i]) {
            const Node n=a->nodes[i];
            uint64_t m=s->mass[i];
            ++s->unique;
            if (n.flags & BRIDGE) ++s->bridges;
            uint64_t adjusted = (n.flags & BRIDGE) ? m + m/2 : m;
            assert(UINT64_MAX - s->reward[n.rule] >= adjusted);
            s->reward[n.rule] += adjusted;
            uint64_t sent=(m*85)/100;
            int multi=n.flags & MULTI;
            uint32_t npar=multi ? 1 + a->overflow[n.secondary] : (n.flags & ONE ? 1 : 2);
            queue(s,a,n.primary,sent/npar);
            if (multi) for (uint32_t j=1;j<npar;++j)
                queue(s,a,a->overflow[n.secondary+j],sent/npar);
            else if (npar==2) queue(s,a,n.secondary,sent/npar);
        }
    }
}
static uint32_t random_state = 1552659;
static uint32_t draw(void) {
    random_state = random_state * 1664525u + 1013904223u;
    return random_state;
}
static void differential(Arena *a, Scratch *s) {
    for (unsigned trial=0; trial<128; ++trial) {
        reset(a);
        memset(s->reward,0,sizeof s->reward);
        /* Independent ordered input lists (not read from packed arena). */
        Id deps[49][4]={{0}};
        uint32_t arity[49]={0}, rules[49]={0}, bridge[49]={0};
        uint64_t mass[49]={0}, expected[RULES]={0};
        for (Id id=1;id<49;++id) {
            arity[id]=1+draw()%4;
            rules[id]=1+draw()%23;
            bridge[id]=(draw()>>4)&1;
            for (uint32_t k=0;k<arity[id];++k) deps[id][k]=draw()%id;
            assert(derive(a,0,(uint16_t)rules[id],deps[id],arity[id],bridge[id])==id);
        }
        Id x=1+draw()%48, y=1+draw()%48;
        mass[x]+=8192; mass[y]+=8193;
        for (Id id=48;id;--id) {
            uint64_t n=mass[id];
            expected[rules[id]] += n + (bridge[id] ? n/2 : 0);
            for (uint32_t k=0;k<arity[id];++k)
                mass[deps[id][k]] += (n*85/100)/arity[id];
        }
        distribute(s,a,x,y,16385);
        assert(!memcmp(s->reward,expected,sizeof expected));
    }
}
int main(void) {
    static Arena a;
    static Scratch s;
    reset(&a);
    const Id zero[]={0};
    Id root=derive(&a,0,1,zero,1,1);
    Id one=derive(&a,0,2,&root,1,0), two=derive(&a,0,3,&root,1,0);
    Id parents[]={one,two,root};
    Id merge=derive(&a,0,4,parents,3,0);
    assert(root && one && two && merge && a.words==3 && depth(&a,merge)==3);
    distribute(&s,&a,merge,merge,12000);
    assert(s.unique==4 && s.bridges==1 && s.reward[4]==12000);
    /* 3,400 direct plus two decayed 2,890 shares; attributed once. */
    assert(s.reward[1]==13770);
    assert(!derive(&a,root,1,&merge,1,1));
    assert(!derive(&a,one,2,&one,1,0));
    assert(derive(&a,merge,4,zero,1,0)==merge && depth(&a,merge)==1);
    assert(!derive(&a,merge,4,zero,1,0));
    s.generation=UINT32_MAX;
    distribute(&s,&a,merge,merge,100);
    assert(s.generation==1 && s.unique==1);
    reset(&a);
    assert(!derive(&a,0,1,&merge,1,0) && a.words==0);
    for (uint32_t i=1;i<N;++i) assert(derive(&a,0,1,zero,1,0)==i);
    assert(!derive(&a,0,1,zero,1,0));
    reset(&a);
    static Id many[O];
    assert(derive(&a,0,1,many,O,0));
    assert(a.words==O && !derive(&a,0,1,many,3,0));
    differential(&a,&s);
    printf("{\"node_bytes\":%zu,\"arena_bytes\":%zu,\"scratch_bytes\":%zu,"
           "\"diamond_unique\":4,\"shared_bridge_credit\":13770,"
           "\"node_capacity\":%d,\"overflow_word_capacity\":%d,"
           "\"cycles_refused\":true,\"tag_wrap_tested\":true,\"oracle_dags\":128}\n",
           sizeof(Node),sizeof(Arena),sizeof(Scratch),N,O);
}
