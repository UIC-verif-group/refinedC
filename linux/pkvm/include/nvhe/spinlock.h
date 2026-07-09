/* SPDX-License-Identifier: GPL-2.0-only */

#ifndef __ARM64_KVM_NVHE_SPINLOCK_H__
#define __ARM64_KVM_NVHE_SPINLOCK_H__

#include <nvhe/types.h>

//@rc::require refinedc.linux.pkvm.spinlock
//@rc::import spinlock_def from refinedc.linux.pkvm.spinlock
//@rc::context `{!lockG Σ} `{!spinlockG Σ}

typedef struct hyp_spinlock {
#ifdef __AARCH64EB__
  _Atomic u16 next, owner;
#else
  _Atomic u16 owner, next;
#endif
} hyp_spinlock_t;

[[rc::parameters("p : loc")]]
[[rc::args("p @ &own<uninit<struct_hyp_spinlock>>")]]
[[rc::exists("id : lock_id")]]
[[rc::ensures("own p : hyp_spinlock_t<id>")]]
static inline void hyp_spin_lock_init(hyp_spinlock_t *lock);

[[rc::parameters("p : loc", "id : lock_id", "s : own_state")]]
[[rc::args("p @ &frac<s, hyp_spinlock_t<id>>")]]
[[rc::ensures("frac s p : hyp_spinlock_t<id>", "[spinlock_token id []]")]]
static inline void hyp_spin_lock(hyp_spinlock_t *lock);

[[rc::parameters("p : loc", "id : lock_id", "s : own_state")]]
[[rc::args("p @ &frac<s, hyp_spinlock_t<id>>")]]
[[rc::requires("[spinlock_token id []]")]]
[[rc::ensures("frac s p : hyp_spinlock_t<id>")]]
static inline void hyp_spin_unlock(hyp_spinlock_t *lock);

#endif /* __ARM64_KVM_NVHE_SPINLOCK_H__ */
