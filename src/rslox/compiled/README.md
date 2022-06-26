I've opted to implement this using safe rust, since I cared more about learning the language proper than about raw performance (and also, this is a hobby project; I wouldn't write C if you paid me).

Other performance hurting changes include:
1. Code isn't a raw sequence of bytes, it's an ADT vector.

