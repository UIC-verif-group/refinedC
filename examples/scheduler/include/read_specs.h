#pragma once

//@rc::import fdsched_extra from refinedc.examples.scheduler.src.fdsched

//@rc::context `{!PacketArrivals}

// This specification assumes that `__builtin_errno` returns a newly allocated pointer on each call (due to the &own in the returns). This is not very realistic, but it does not influence the verification much.
// TODO: make this specification more realistic
[[rc::parameters("n : Z")]]
[[rc::requires("[is_errno n]")]]
[[rc::returns("&own<n @ int<i32>>")]]
[[rc::ensures("[is_errno n]")]]
extern int *__builtin_errno(void);

[[rc::parameters("data : {list Z}", "fd : Z", "l : loc", "t1 : nat", "errno : Z")]]
[[rc::args("fd @ int<i32>", "l @ &own<{uninit (mk_array_layout u8 (Z.to_nat max_msg_len))}>", "max_msg_len @ int<size_t>")]]
[[rc::requires("[is_errno errno]")]]
[[rc::requires("[curr_read_index t1]")]]
[[rc::ensures("[curr_read_index (t1 + 1%nat)]")]]
[[rc::exists("n : Z", "pckt : packet_ID")]]
[[rc::returns("{if (bool_decide $ is_Some $ (packet_arrivals fd t1)) then length (get_packet_data pckt) else -1} @ int<i64>")]]
[[rc::ensures("own l : array_p<u8, {get_packet_data pckt `at_type` int(u8)}, {Z.to_nat max_msg_len}>")]]
[[rc::ensures("[is_errno n]")]]
[[rc::ensures("{if  (bool_decide $ is_Some $ (packet_arrivals fd t1)) then True else n = EWOULDBLOCK}")]]
[[rc::ensures("{pckt = {|fd := fd; read_index := t1|}}")]]
ssize_t read(int fd, void* data, size_t msg_len);
