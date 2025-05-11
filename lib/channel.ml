type channel = {
  state: string;
  proof: string list;
}

let send channel msg =
  let proof = (String.concat ":" ["send";msg])::channel.proof in
  let state = Sha256.to_hex (Sha256.string (String.concat "" [channel.state;msg])) in
  {state;proof}

let receive_random_int channel min max = 
  let n = Z.(+) min (Z.(mod) (Z.of_string_base 16 channel.state) (Z.(+) (Z.(-) max min) Z.one)) in
  let proof = (String.concat ":" ["receive_random_int";Z.to_string n])::channel.proof in
  let state = Sha256.to_hex (Sha256.string channel.state) in
  (n,{state;proof})

let receive_random_field_element channel =
  let n,{state;_} = receive_random_int channel Z.zero (Z.(-) Field.order Z.one) in
  let proof = (String.concat ":" ["receive_random_field_element";Z.to_string n])::channel.proof in 
  (n,{state;proof})