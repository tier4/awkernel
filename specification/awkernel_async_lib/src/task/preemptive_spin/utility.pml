inline min(a,b,ret) {
	d_step {
		if
		:: a < b -> ret = a
		:: else -> ret = b
		fi
	}
}

inline remove_from_channel(ch,msg) {
	d_step {
		byte msg_i;byte tmp_msg;byte original_len = len(ch);

        for (msg_i : 0 .. original_len - 1) {
			ch?tmp_msg;
			if
			:: (tmp_msg != msg) -> ch!tmp_msg
			:: else
			fi
		}
	}
}

inline move_channel(src_ch,dst_ch) {
	d_step {
		assert(empty(dst_ch));assert(nempty(src_ch));

		byte msg_i;byte tmp_msg;byte src_len = len(src_ch);
		for (msg_i : 0 .. src_len - 1) {
			src_ch?tmp_msg;
			dst_ch!tmp_msg;
		}
	}
}
