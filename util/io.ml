let read_all_chan ch = really_input_string ch (in_channel_length ch)
let read_all string = In_channel.with_open_bin string read_all_chan

let file_to_bools file =
  let content = read_all file in
  StringUtil.from_hex_string content
