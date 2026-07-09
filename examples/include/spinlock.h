#ifndef SPINLOCK_H
#define SPINLOCK_H

#include <stddef.h>
#include <stdatomic.h>

//@rc::require refinedc.examples.spinlock
//@rc::import spinlock_def from refinedc.examples.spinlock
//@rc::context `{!lockG Σ}

struct spinlock {
    atomic_bool lock;
};

[[rc::parameters("p : loc")]]
[[rc::args("p @ &own<uninit<struct_spinlock>>")]]
[[rc::exists("gamma : lock_id")]]
[[rc::ensures("own p : spinlock<gamma>")]]
void sl_init(struct spinlock* lock);


[[rc::parameters("p : loc", "gamma : lock_id", "beta : own_state")]]
[[rc::args("p @ &frac<beta, spinlock<gamma>>")]]
[[rc::ensures("frac beta p : spinlock<gamma>", "[lock_token gamma []]")]]
void sl_lock(struct spinlock* lock);


[[rc::parameters("p : loc", "gamma : lock_id", "beta : own_state")]]
[[rc::args("p @ &frac<beta, spinlock<gamma>>")]]
[[rc::requires("[lock_token gamma []]")]]
[[rc::ensures("frac beta p : spinlock<gamma>")]]
void sl_unlock(struct spinlock* lock);

// Locks both a and b in a determinitic order (used to avoid deadlocks).
[[rc::parameters("p1 : loc", "gamma1 : lock_id", "beta1 : own_state")]]
[[rc::parameters("p2 : loc", "gamma2 : lock_id", "beta2 : own_state")]]
[[rc::args("p1 @ &frac<beta1, spinlock<gamma1>>")]]
[[rc::args("p2 @ &frac<beta2, spinlock<gamma2>>")]]
[[rc::ensures("frac beta1 p1 : spinlock<gamma1>", "[lock_token gamma1 []]")]]
[[rc::ensures("frac beta2 p2 : spinlock<gamma2>", "[lock_token gamma2 []]")]]
void sl_lock_both(struct spinlock* a, struct spinlock* b);

// Same but with implementation assuming locks to be in the same allocaiton.
[[rc::parameters("p1 : loc", "gamma1 : lock_id", "beta1 : own_state")]]
[[rc::parameters("p2 : loc", "gamma2 : lock_id", "beta2 : own_state")]]
[[rc::args("p1 @ &frac<beta1, spinlock<gamma1>>")]]
[[rc::args("p2 @ &frac<beta2, spinlock<gamma2>>")]]
[[rc::requires("{p1.1 = p2.1}")]]
[[rc::ensures("frac beta1 p1 : spinlock<gamma1>", "[lock_token gamma1 []]")]]
[[rc::ensures("frac beta2 p2 : spinlock<gamma2>", "[lock_token gamma2 []]")]]
void sl_lock_both_same_prov(struct spinlock* a, struct spinlock* b);
#endif
